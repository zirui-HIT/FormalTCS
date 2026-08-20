#!/usr/bin/env python3
"""Run Codex with an ephemeral ModelRouter provider configuration.

Codex speaks the Responses API natively and the ModelRouter OpenAI-compatible
endpoint accepts that dialect verbatim, including the Codex-private
``additional_tools`` input item, ``namespace`` tools and ``client_metadata``.
Those models are therefore relayed byte-for-byte so ``prompt_cache_key`` and the
stable request prefix reach the provider untouched, which is what makes input
caching work.  Claude models have no Responses endpoint here and keep the
Responses-to-Chat translation leg.
"""

from __future__ import annotations

import argparse
from contextlib import AbstractContextManager
import hashlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import itertools
import json
import os
from pathlib import Path
import re
import shutil
import socket
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.request
from urllib.parse import urlsplit, urlunsplit
import uuid


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
if str(REPOSITORY_ROOT) not in sys.path:
    sys.path.insert(0, str(REPOSITORY_ROOT))

from utils.claude_runtime import (  # noqa: E402
    load_api_credentials,
    redact_secret,
    sanitized_environment,
)


PROVIDER_ID = "modelrouter"
MODEL_ID = os.environ.get("LEANMARATHON_MODEL") or "gpt-5.6-sol"
PROXY_ENV_KEY = "LEANMARATHON_CODEX_PROXY_TOKEN"
# Agent reasoning/tool turns are intentionally not time-limited.  Only the
# connection, response headers, and first SSE line have a deadline; after the
# stream starts, the socket is restored to blocking mode so a slow model turn
# can run for as long as the stage permits.
MODELROUTER_TIMEOUT_SECONDS = None
# Upstream traffic can remain queued for several minutes before response headers
# arrive.  A shorter deadline repeatedly discards that queue position and can
# starve every newly submitted pipeline.
MODELROUTER_FIRST_SSE_TIMEOUT_SECONDS = 600
MODELROUTER_RETRIES = 2
MODELROUTER_TRANSIENT_HTTP_CODES = frozenset({408, 429, 500, 502, 503, 504})
# Claude leg only: Chat Completions has no provider-side prompt cache, so the
# shared system and tool prefix carries an explicit ephemeral cache breakpoint.
PROMPT_CACHE_TTL = "1h"
TOOL_OUTPUT_DEDUP_MIN_BYTES = 512


class ModelRouterProtocolError(RuntimeError):
    """Raised when ModelRouter terminates a response without a valid choice."""


class UpstreamHTTPError(RuntimeError):
    """Carries an upstream HTTP failure so it can be forwarded to Codex."""

    def __init__(self, code, body, content_type, exhausted=False):
        super().__init__(f"MODELROUTER_HTTP_{code}")
        self.code = code
        self.body = body
        self.content_type = content_type or "application/json"
        self.exhausted = exhausted


def uses_chat_leg(model):
    """Return whether one model must be relayed through Chat Completions."""
    return str(model).startswith("claude-")


def openai_base_url(value):
    """Normalize one configured API_URL value to an OpenAI-compatible v1 base."""
    parsed = urlsplit(value)
    if parsed.scheme not in {"http", "https"} or not parsed.netloc:
        raise ValueError("API_URL must contain an absolute HTTP(S) endpoint")
    path = parsed.path.rstrip("/")
    if "/protocol/anthropic" in path:
        path = path.split("/protocol/anthropic", 1)[0] + "/protocol/openai/v1"
    elif "/protocol/openai" in path:
        path = path.split("/protocol/openai", 1)[0] + "/protocol/openai/v1"
    else:
        for suffix in ("/chat/completions", "/responses"):
            if path.endswith(suffix):
                path = path[: -len(suffix)]
                break
        if not path.endswith("/v1"):
            path += "/v1"
    return urlunsplit((parsed.scheme, parsed.netloc, path, parsed.query, ""))


def _credentials(endpoint_index=0):
    key, urls = load_api_credentials()
    if not 0 <= endpoint_index < len(urls):
        raise ValueError(
            f"ModelRouter endpoint index {endpoint_index} is outside the configured API_URL list"
        )
    return key, urls, openai_base_url(urls[endpoint_index])


def _reject_user_codex_home(path):
    resolved = Path(path).expanduser().resolve()
    protected = (Path.home() / ".codex").resolve()
    if resolved == protected or protected in resolved.parents:
        raise ValueError("LeanMarathon refuses to use or modify the user's ~/.codex directory")
    return resolved


def _redact(text, secrets):
    for secret in secrets:
        if secret:
            text = redact_secret(text, secret)
    return text


def _isolated_codex_environment():
    """Build a child environment with no inherited user Codex state or paths."""
    environment = sanitized_environment(os.environ)
    allowed_sensitive = {
        "GITEA_TOKEN",
        "LEANMARATHON_GIT_TOKEN",
        "LEANMARATHON_CODEX_PROXY_TOKEN",
    }
    for name in tuple(environment):
        if name.startswith("CODEX_"):
            environment.pop(name, None)
            continue
        upper = name.upper()
        if name not in allowed_sensitive and any(
            marker in upper
            for marker in ("SECRET", "PASSWORD", "PASSWD", "PRIVATE_KEY", "CREDENTIAL")
        ):
            environment.pop(name, None)
    protected = (Path.home() / ".codex").resolve()
    path_entries = []
    for entry in environment.get("PATH", "").split(os.pathsep):
        if not entry:
            continue
        resolved = Path(entry).expanduser().resolve()
        if resolved == protected or protected in resolved.parents:
            continue
        path_entries.append(entry)
    environment["PATH"] = os.pathsep.join(path_entries)
    return environment


def _restore_unlimited_stream_timeout(response):
    """Remove the first-line socket deadline without depending on one urllib layout."""
    candidates = [response]
    for _depth in range(4):
        next_candidates = []
        for candidate in candidates:
            for attribute in ("fp", "raw", "_sock", "sock"):
                child = getattr(candidate, attribute, None)
                if child is None:
                    continue
                if hasattr(child, "settimeout"):
                    child.settimeout(MODELROUTER_TIMEOUT_SECONDS)
                    return
                next_candidates.append(child)
        candidates = next_candidates


def billing_usage(usage):
    """Extract disjoint billing fields from one Responses-shaped usage object.

    Codex records ``cached_tokens`` but ignores the ``cache_write_tokens`` that
    ModelRouter reports, so cache creation would otherwise be billed at the
    cheaper uncached input rate.  The field names match ``utils.codex_usage``.
    """
    usage = usage if isinstance(usage, dict) else {}
    input_details = usage.get("input_tokens_details")
    output_details = usage.get("output_tokens_details")
    input_details = input_details if isinstance(input_details, dict) else {}
    output_details = output_details if isinstance(output_details, dict) else {}
    total_input = int(usage.get("input_tokens", 0) or 0)
    cached = int(input_details.get("cached_tokens", 0) or 0)
    cache_write = int(input_details.get("cache_write_tokens", 0) or 0)
    return {
        "input_tokens": max(0, total_input - cached - cache_write),
        "cached_input_tokens": cached,
        "cache_write_input_tokens": cache_write,
        "output_tokens": int(usage.get("output_tokens", 0) or 0),
        "reasoning_output_tokens": int(output_details.get("reasoning_tokens", 0) or 0),
    }


# --------------------------------------------------------------------------- #
# Claude leg: Responses to Chat Completions translation
# --------------------------------------------------------------------------- #


def _content_text(value):
    """Flatten Responses or Chat text content without retaining media payloads."""
    if isinstance(value, str):
        return value
    if not isinstance(value, list):
        return ""
    pieces = []
    for part in value:
        if isinstance(part, str):
            pieces.append(part)
        elif isinstance(part, dict):
            text = part.get("text")
            if isinstance(text, str):
                pieces.append(text)
    return "".join(pieces)


def _chat_namespace_tool_name(namespace, name):
    """Return a stable Chat function name for one Responses namespace tool."""
    candidate = f"{namespace}__{name}"
    if len(candidate) <= 64:
        return candidate
    digest = hashlib.sha256(f"{namespace}\0{name}".encode("utf-8")).hexdigest()[:10]
    prefix = f"ns_{digest}_"
    return prefix + name[: 64 - len(prefix)]


def _prompt_cache_key(model, system_text, tools):
    """Route equal stable prompt prefixes to the same ModelRouter cache shard."""
    value = json.dumps(
        {"model": model, "system": system_text, "tools": tools},
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    )
    digest = hashlib.sha256(value.encode("utf-8")).hexdigest()[:32]
    return f"leanmarathon-{digest}"


def _responses_to_chat(payload, *, tool_output_dedup_stats=None):
    """Translate the Codex Responses request subset to Chat Completions."""
    system_parts = []
    additional_tools = []
    seen_tool_outputs = {}
    dedup_stats = {
        "tool_outputs_seen": 0,
        "eligible_outputs": 0,
        "deduplicated_outputs": 0,
        "original_utf8_bytes": 0,
        "forwarded_utf8_bytes": 0,
        "saved_utf8_bytes": 0,
    }
    instructions = payload.get("instructions")
    if isinstance(instructions, str) and instructions:
        system_parts.append(instructions)
    messages = []

    for item in payload.get("input") or []:
        if not isinstance(item, dict):
            continue
        kind = item.get("type")
        if kind == "message":
            role = item.get("role", "user")
            content = _content_text(item.get("content"))
            if role in {"system", "developer"}:
                if content:
                    system_parts.append(content)
            else:
                messages.append({"role": role, "content": content})
        elif kind in {"function_call", "custom_tool_call"}:
            arguments = item.get("arguments", item.get("input", ""))
            if not isinstance(arguments, str):
                arguments = json.dumps(arguments, ensure_ascii=False)
            name = item.get("name", "tool")
            namespace = item.get("namespace")
            if isinstance(namespace, str) and namespace:
                name = _chat_namespace_tool_name(namespace, name)
            call = {
                "id": item.get("call_id") or item.get("id") or f"call_{uuid.uuid4().hex}",
                "type": "function",
                "function": {"name": name, "arguments": arguments},
            }
            if messages and messages[-1].get("role") == "assistant":
                messages[-1].setdefault("tool_calls", []).append(call)
            else:
                messages.append({"role": "assistant", "content": None, "tool_calls": [call]})
        elif kind in {"function_call_output", "custom_tool_call_output"}:
            content = _content_text(item.get("output"))
            content_bytes = len(content.encode("utf-8"))
            dedup_stats["tool_outputs_seen"] += 1
            dedup_stats["original_utf8_bytes"] += content_bytes
            forwarded = content
            if content_bytes >= TOOL_OUTPUT_DEDUP_MIN_BYTES:
                dedup_stats["eligible_outputs"] += 1
                digest = hashlib.sha256(content.encode("utf-8")).hexdigest()
                previous = seen_tool_outputs.get(digest)
                if previous is None or previous[0] != content:
                    seen_tool_outputs[digest] = (content, str(item.get("call_id") or ""))
                else:
                    previous_call_id = previous[1] or "an earlier tool call"
                    reference = (
                        "[LeanMarathon exact tool-output reference: this output is byte-for-byte "
                        f"identical to call_id={previous_call_id}; sha256={digest}; "
                        f"utf8_bytes={content_bytes}. The complete content appears earlier in "
                        "this request.]"
                    )
                    if len(reference.encode("utf-8")) < content_bytes:
                        forwarded = reference
                        dedup_stats["deduplicated_outputs"] += 1
            forwarded_bytes = len(forwarded.encode("utf-8"))
            dedup_stats["forwarded_utf8_bytes"] += forwarded_bytes
            dedup_stats["saved_utf8_bytes"] += content_bytes - forwarded_bytes
            messages.append(
                {
                    "role": "tool",
                    "tool_call_id": item.get("call_id", ""),
                    "content": forwarded,
                }
            )
        elif kind == "reasoning":
            continue
        elif kind == "additional_tools":
            additional_tools.extend(
                tool for tool in item.get("tools", []) if isinstance(tool, dict)
            )
        else:
            raise ValueError(f"unsupported Responses input item type: {kind!r}")

    tools = []
    tool_routes = {}
    for tool in [*(payload.get("tools") or []), *additional_tools]:
        if not isinstance(tool, dict):
            continue
        kind = tool.get("type", "function")
        name = tool.get("name") or kind
        if kind == "function":
            function = {
                key: tool[key]
                for key in ("name", "description", "parameters", "strict")
                if key in tool
            }
            tool_routes[name] = {"kind": kind, "name": name, "namespace": None}
            tools.append({"type": "function", "function": function})
            continue
        if kind == "namespace":
            for child in tool.get("tools") or []:
                if not isinstance(child, dict) or child.get("type", "function") not in {
                    "custom",
                    "function",
                }:
                    continue
                child_name = child.get("name")
                if not isinstance(child_name, str) or not child_name:
                    continue
                chat_name = _chat_namespace_tool_name(name, child_name)
                if chat_name in tool_routes:
                    raise ValueError(
                        f"duplicate Chat tool name after namespace expansion: {chat_name}"
                    )
                child_kind = child.get("type", "function")
                function = {"description": child.get("description", "")}
                if child_kind == "function":
                    function.update(
                        {key: child[key] for key in ("parameters", "strict") if key in child}
                    )
                else:
                    function["parameters"] = {
                        "type": "object",
                        "properties": {"input": {"type": "string"}},
                        "required": ["input"],
                        "additionalProperties": False,
                    }
                function["name"] = chat_name
                function.setdefault("description", f"Invoke {name}.{child_name}.")
                tool_routes[chat_name] = {
                    "kind": "namespace_custom" if child_kind == "custom" else kind,
                    "name": child_name,
                    "namespace": name,
                }
                tools.append({"type": "function", "function": function})
            continue
        tool_routes[name] = {"kind": kind, "name": name, "namespace": None}
        tools.append(
            {
                "type": "function",
                "function": {
                    "name": name,
                    "description": tool.get("description", f"Invoke the {name} tool."),
                    "parameters": {
                        "type": "object",
                        "properties": {"input": {"type": "string"}},
                        "required": ["input"],
                        "additionalProperties": False,
                    },
                },
            }
        )

    request = {
        "model": payload.get("model", MODEL_ID),
        "messages": messages,
        "stream": False,
    }
    if tools:
        request["tools"] = tools
        choice = payload.get("tool_choice", "auto")
        if isinstance(choice, str):
            request["tool_choice"] = choice
        elif isinstance(choice, dict) and choice.get("name"):
            choice_name = choice["name"]
            choice_namespace = choice.get("namespace")
            if isinstance(choice_namespace, str) and choice_namespace:
                choice_name = _chat_namespace_tool_name(choice_namespace, choice_name)
            request["tool_choice"] = {"type": "function", "function": {"name": choice_name}}
    reasoning = payload.get("reasoning")
    if isinstance(reasoning, dict) and reasoning.get("effort"):
        request["reasoning_effort"] = reasoning["effort"]
    if system_parts:
        system_text = "\n\n".join(system_parts)
        request["system"] = [
            {
                "type": "text",
                "text": system_text,
                "cache_control": {"type": "ephemeral", "ttl": PROMPT_CACHE_TTL},
            }
        ]
        request["prompt_cache_key"] = _prompt_cache_key(request["model"], system_text, tools)
    if tool_output_dedup_stats is not None:
        tool_output_dedup_stats.update(dedup_stats)
    return request, tool_routes


def _unwrap_chat_response(value):
    """Unwrap common gateway envelopes until a Chat response is reached."""
    seen = set()
    current = value
    while isinstance(current, dict) and id(current) not in seen:
        seen.add(id(current))
        if current.get("error"):
            raise RuntimeError(str(current["error"]))
        if current.get("success") is False:
            raise RuntimeError(str(current.get("message") or current))
        if isinstance(current.get("choices"), list):
            return current
        advanced = False
        for key in ("data", "result", "response", "content"):
            child = current.get(key)
            if isinstance(child, str):
                try:
                    child = json.loads(child)
                except json.JSONDecodeError:
                    continue
            if isinstance(child, dict):
                current = child
                advanced = True
                break
        if not advanced:
            break
    raise RuntimeError("ModelRouter response does not contain Chat choices")


def _read_chat_stream(response, model, first_line=None):
    """Accumulate one OpenAI-compatible Chat SSE stream into a Chat response."""
    content_parts = []
    tool_calls = {}
    usage = {}
    response_id = None
    response_model = model
    created = time.time()
    finish_reason = None
    announced = False
    lines = response if first_line is None else itertools.chain((first_line,), response)
    for raw_line in lines:
        line = raw_line.decode("utf-8", errors="replace").strip()
        if not line.startswith("data:"):
            continue
        data = line[5:].strip()
        if data == "[DONE]":
            break
        if not data:
            continue
        try:
            chunk = _unwrap_chat_response(json.loads(data))
        except json.JSONDecodeError as exc:
            raise RuntimeError("ModelRouter Chat stream returned invalid JSON") from exc
        if not announced:
            print(f"MODELROUTER_STREAM_ACTIVE model={model} leg=chat", flush=True)
            announced = True
        response_id = chunk.get("id") or response_id
        response_model = chunk.get("model") or response_model
        created = chunk.get("created") or created
        if isinstance(chunk.get("usage"), dict):
            usage = chunk["usage"]
        choices = chunk.get("choices") or []
        if not choices:
            continue
        choice = choices[0]
        finish_reason = choice.get("finish_reason") or finish_reason
        delta = choice.get("delta") or choice.get("message") or {}
        content = delta.get("content")
        if isinstance(content, str):
            content_parts.append(content)
        elif isinstance(content, list):
            for block in content:
                if not isinstance(block, dict):
                    continue
                if isinstance(block.get("text"), str):
                    content_parts.append(block["text"])
                if block.get("type") == "tool_use":
                    index = len(tool_calls)
                    tool_calls[index] = {
                        "id": block.get("id"),
                        "type": "function",
                        "function": {
                            "name": block.get("name", ""),
                            "arguments": json.dumps(block.get("input", {}), ensure_ascii=False),
                        },
                    }
        for call in delta.get("tool_calls") or []:
            index = int(call.get("index", len(tool_calls)))
            current = tool_calls.setdefault(
                index,
                {"id": None, "type": "function", "function": {"name": "", "arguments": ""}},
            )
            if call.get("id"):
                current["id"] = call["id"]
            function = call.get("function") or {}
            if function.get("name"):
                current["function"]["name"] += function["name"]
            if function.get("arguments"):
                current["function"]["arguments"] += function["arguments"]
    if not announced:
        raise ModelRouterProtocolError("ModelRouter Chat stream contained no data events")
    content_text = "".join(content_parts)
    ordered_tool_calls = [tool_calls[index] for index in sorted(tool_calls)]
    if finish_reason is None and not content_text and not ordered_tool_calls:
        raise ModelRouterProtocolError(
            "ModelRouter Chat stream ended with an empty assistant response and no finish_reason"
        )
    return {
        "id": response_id or f"chat_{uuid.uuid4().hex}",
        "model": response_model,
        "created": created,
        "choices": [
            {
                "message": {
                    "role": "assistant",
                    "content": content_text or None,
                    "tool_calls": ordered_tool_calls,
                },
                "finish_reason": finish_reason,
            }
        ],
        "usage": usage,
    }


def _chat_response_usage(chat):
    """Map an Anthropic-flavoured Chat usage object onto Responses usage."""
    usage = chat.get("usage") if isinstance(chat.get("usage"), dict) else {}
    prompt_details = usage.get("prompt_tokens_details")
    completion_details = usage.get("completion_tokens_details")
    prompt_cached = (
        prompt_details.get("cached_tokens", 0) if isinstance(prompt_details, dict) else 0
    )
    cached = int(usage.get("cache_read_input_tokens", prompt_cached) or 0)
    cache_write = int(usage.get("cache_creation_input_tokens", 0) or 0)
    reasoning = (
        completion_details.get("reasoning_tokens", 0)
        if isinstance(completion_details, dict)
        else 0
    )
    uncached_input = int(usage.get("prompt_tokens", usage.get("input_tokens", 0)) or 0)
    input_tokens = uncached_input
    if "cache_read_input_tokens" in usage or "cache_creation_input_tokens" in usage:
        input_tokens += cached + cache_write
    output_tokens = int(usage.get("completion_tokens", usage.get("output_tokens", 0)) or 0)
    return {
        "input_tokens": input_tokens,
        "input_tokens_details": {
            "cached_tokens": cached,
            "cache_write_tokens": cache_write,
        },
        "output_tokens": output_tokens,
        "output_tokens_details": {"reasoning_tokens": int(reasoning or 0)},
        "total_tokens": input_tokens + output_tokens,
    }


def _tool_call_output_item(name, arguments, call_id, tool_routes):
    """Map one upstream tool call back to its Codex Responses output item."""
    if not isinstance(arguments, str):
        arguments = json.dumps(arguments, ensure_ascii=False)
    elif not arguments.strip():
        # Claude may omit the argument object for a parameterless tool, while
        # Codex Responses and MCP require syntactically valid JSON.
        arguments = "{}"
    route = tool_routes.get(name, {"kind": "function", "name": name, "namespace": None})
    item_id = f"fc_{uuid.uuid4().hex}"
    if route["kind"] in {"custom", "namespace_custom"}:
        try:
            decoded = json.loads(arguments)
        except json.JSONDecodeError:
            decoded = None
        custom_input = decoded.get("input") if isinstance(decoded, dict) else arguments
        if not isinstance(custom_input, str):
            custom_input = json.dumps(custom_input, ensure_ascii=False)
        item = {
            "id": item_id,
            "type": "custom_tool_call",
            "call_id": call_id,
            "name": route["name"],
            "input": custom_input,
        }
        if route["namespace"]:
            item["namespace"] = route["namespace"]
        return item
    item = {
        "id": item_id,
        "type": "function_call",
        "status": "completed",
        "call_id": call_id,
        "name": route["name"],
        "arguments": arguments,
    }
    if route["kind"] == "namespace":
        item["namespace"] = route["namespace"]
    return item


def _chat_to_response(chat_value, request_payload, tool_routes):
    """Translate one complete Chat response into a complete Responses object."""
    chat = _unwrap_chat_response(chat_value)
    try:
        choice = chat["choices"][0]
        message = choice["message"]
    except (IndexError, KeyError, TypeError) as exc:
        raise RuntimeError("ModelRouter response has no assistant choice") from exc
    output = []
    content = _content_text(message.get("content"))
    if content:
        output.append(
            {
                "id": f"msg_{uuid.uuid4().hex}",
                "type": "message",
                "status": "completed",
                "role": "assistant",
                "content": [{"type": "output_text", "text": content, "annotations": []}],
            }
        )
    chat_tool_calls = list(message.get("tool_calls") or [])
    if isinstance(message.get("content"), list):
        for block in message["content"]:
            if not isinstance(block, dict) or block.get("type") != "tool_use":
                continue
            chat_tool_calls.append(
                {
                    "id": block.get("id"),
                    "function": {
                        "name": block.get("name"),
                        "arguments": json.dumps(block.get("input", {}), ensure_ascii=False),
                    },
                }
            )
    for call in chat_tool_calls:
        function = call.get("function") if isinstance(call, dict) else None
        if not isinstance(function, dict):
            continue
        output.append(
            _tool_call_output_item(
                function.get("name", "tool"),
                function.get("arguments", ""),
                call.get("id") or f"call_{uuid.uuid4().hex}",
                tool_routes,
            )
        )
    if not output:
        raise ModelRouterProtocolError(
            "ModelRouter Chat turn produced no assistant message or tool call"
        )
    return {
        "id": chat.get("id") or f"resp_{uuid.uuid4().hex}",
        "object": "response",
        "created_at": float(chat.get("created", time.time())),
        "completed_at": time.time(),
        "status": "completed",
        "error": None,
        "incomplete_details": None,
        "instructions": request_payload.get("instructions"),
        "model": chat.get("model", request_payload.get("model", MODEL_ID)),
        "output": output,
        "parallel_tool_calls": bool(request_payload.get("parallel_tool_calls", True)),
        "tool_choice": request_payload.get("tool_choice", "auto"),
        "tools": request_payload.get("tools") or [],
        "usage": _chat_response_usage(chat),
    }


# --------------------------------------------------------------------------- #
# Proxy
# --------------------------------------------------------------------------- #


class _TerminalObserver:
    """Read usage out of a forwarded Responses SSE stream without altering it."""

    def __init__(self):
        self.terminal = None

    def feed(self, line):
        if not line.startswith(b"data:") or b'"response.completed"' not in line:
            return
        try:
            event = json.loads(line[5:].strip())
        except json.JSONDecodeError:
            return
        if isinstance(event, dict) and event.get("type") == "response.completed":
            response = event.get("response")
            if isinstance(response, dict):
                self.terminal = response

    def assistant_items(self):
        items = (self.terminal or {}).get("output") or []
        return [
            item
            for item in items
            if isinstance(item, dict)
            and (
                item.get("type") in {"function_call", "custom_tool_call"}
                or (item.get("type") == "message" and _content_text(item.get("content")))
            )
        ]


class ModelRouterProxy(AbstractContextManager):
    """Serve a private loopback Responses endpoint backed by ModelRouter.

    Non-Claude models are relayed byte-for-byte to the upstream Responses
    endpoint, which keeps ``prompt_cache_key`` and the request prefix intact so
    provider-side input caching applies.  Claude models are translated to Chat
    Completions and their reply is re-emitted as a Responses SSE stream.
    """

    def __init__(self, base_url, key, usage_path):
        self.responses_url = base_url.rstrip("/") + "/responses"
        self.chat_url = base_url.rstrip("/") + "/chat/completions"
        self.key = key
        self.usage_path = Path(usage_path)
        self.server = None
        self.thread = None
        self._lock = threading.Lock()

    def _open_upstream(self, url, body, *, retry_http):
        """Open one upstream response, retrying only before any byte is served."""
        for attempt in range(MODELROUTER_RETRIES + 1):
            request = urllib.request.Request(
                url,
                data=body,
                method="POST",
                headers={
                    "Authorization": f"Bearer {self.key}",
                    "Content-Type": "application/json",
                    "Accept": "text/event-stream",
                },
            )
            try:
                response = urllib.request.urlopen(
                    request, timeout=MODELROUTER_FIRST_SSE_TIMEOUT_SECONDS
                )
            except urllib.error.HTTPError as exc:
                detail = exc.read()
                text = detail.decode("utf-8", errors="replace")
                transient_route_404 = exc.code == 404 and "does not exist" in text
                retryable = transient_route_404 or (
                    retry_http and exc.code in MODELROUTER_TRANSIENT_HTTP_CODES
                )
                if retryable and attempt < MODELROUTER_RETRIES:
                    time.sleep(2**attempt)
                    continue
                if transient_route_404:
                    raise RuntimeError(
                        "MODELROUTER_TRANSIENT_MODEL_ROUTE_404 after "
                        f"{attempt + 1} attempts: {text[:2000]}"
                    ) from exc
                raise UpstreamHTTPError(
                    exc.code,
                    detail,
                    exc.headers.get("Content-Type"),
                    exhausted=retryable,
                ) from exc
            except (socket.timeout, TimeoutError, OSError) as exc:
                if attempt < MODELROUTER_RETRIES:
                    time.sleep(2**attempt)
                    continue
                raise RuntimeError(
                    "MODELROUTER_CONNECTION_FAILURE after "
                    f"{attempt + 1} attempts for {len(body)} request bytes: {exc}"
                ) from exc
            content_type = response.headers.get("Content-Type", "")
            if "text/event-stream" not in content_type:
                _restore_unlimited_stream_timeout(response)
                return response, None
            try:
                first_line = response.readline()
            except (socket.timeout, TimeoutError):
                first_line = b""
            if not first_line:
                response.close()
                if attempt < MODELROUTER_RETRIES:
                    time.sleep(2**attempt)
                    continue
                raise RuntimeError(
                    "MODELROUTER_FIRST_SSE_TIMEOUT after "
                    f"{attempt + 1} attempts for {len(body)} request bytes"
                )
            _restore_unlimited_stream_timeout(response)
            return response, first_line

    def _record(self, *, leg, model, usage, raw_usage, extra=None):
        record = {
            "timestamp": time.time(),
            "leg": leg,
            "model": model,
            "usage": usage,
            "raw_usage": raw_usage,
        }
        if extra:
            record.update(extra)
        with self._lock:
            self.usage_path.parent.mkdir(parents=True, exist_ok=True)
            with self.usage_path.open("a", encoding="utf-8") as handle:
                handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")

    def serve_passthrough(self, handler, body, payload):
        """Relay one Responses request and its SSE reply without modification."""
        response, first_line = self._open_upstream(
            self.responses_url, body, retry_http=False
        )
        if first_line is None:
            # The upstream answered a streaming request with a plain body; hand it
            # to Codex unchanged instead of inventing a stream around it.
            with response:
                content_type = response.headers.get("Content-Type", "application/json")
                raw = response.read()
            print(
                "MODELROUTER_NON_STREAMING_RESPONSE forwarded to Codex "
                f"content_type={content_type}",
                flush=True,
            )
            handler._send_bytes(200, content_type, raw)
            return
        observer = _TerminalObserver()
        with response:
            handler.send_response(200)
            handler.send_header(
                "Content-Type", response.headers.get("Content-Type", "text/event-stream")
            )
            handler.send_header("Cache-Control", "no-cache")
            handler.send_header("Transfer-Encoding", "chunked")
            handler.end_headers()
            print(
                f"MODELROUTER_STREAM_ACTIVE model={payload.get('model')} leg=responses",
                flush=True,
            )
            for line in itertools.chain((first_line,), response):
                handler.wfile.write(b"%x\r\n" % len(line) + line + b"\r\n")
                handler.wfile.flush()
                observer.feed(line)
            handler.wfile.write(b"0\r\n\r\n")
            handler.wfile.flush()
        terminal = observer.terminal or {}
        if not observer.assistant_items():
            print(
                "MODELROUTER_EMPTY_TERMINAL_RESPONSE the upstream turn produced no "
                "assistant message or tool call",
                flush=True,
            )
        raw_usage = terminal.get("usage") if isinstance(terminal.get("usage"), dict) else {}
        self._record(
            leg="responses",
            model=payload.get("model") or MODEL_ID,
            usage=billing_usage(raw_usage),
            raw_usage=raw_usage,
            extra={
                "upstream_model": terminal.get("model"),
                "prompt_cache_key": payload.get("prompt_cache_key"),
                "request_bytes": len(body),
                "status": terminal.get("status"),
            },
        )

    def serve_chat_leg(self, handler, payload):
        """Translate one Responses request to Chat and re-emit a Responses stream."""
        dedup_stats = {}
        request_payload, tool_routes = _responses_to_chat(
            payload, tool_output_dedup_stats=dedup_stats
        )
        request_payload["stream"] = True
        request_payload["stream_options"] = {"include_usage": True}
        body = json.dumps(request_payload, ensure_ascii=False).encode("utf-8")
        document = None
        for attempt in range(MODELROUTER_RETRIES + 1):
            upstream, first_line = self._open_upstream(self.chat_url, body, retry_http=True)
            try:
                with upstream:
                    if first_line is None:
                        document = json.loads(upstream.read().decode("utf-8", errors="replace"))
                    else:
                        document = _read_chat_stream(
                            upstream, request_payload["model"], first_line=first_line
                        )
                break
            except ModelRouterProtocolError as error:
                if attempt >= MODELROUTER_RETRIES:
                    raise ModelRouterProtocolError(
                        f"MODELROUTER_EMPTY_TERMINAL_RESPONSE after {attempt + 1} attempts: {error}"
                    ) from error
                time.sleep(2**attempt)
        response = _chat_to_response(document, payload, tool_routes)
        _write_synthetic_stream(handler, response)
        chat = _unwrap_chat_response(document)
        self._record(
            leg="chat",
            model=payload.get("model") or MODEL_ID,
            usage=billing_usage(response["usage"]),
            raw_usage=chat.get("usage", {}),
            extra={
                "upstream_model": response["model"],
                "tool_output_dedup": dedup_stats,
                "request_tools": [
                    {
                        "chat_name": chat_name,
                        "name": route["name"],
                        "kind": route["kind"],
                        "namespace": route["namespace"],
                    }
                    for chat_name, route in sorted(tool_routes.items())
                ],
            },
        )

    def __enter__(self):
        proxy = self

        class Handler(BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.1"

            def do_POST(self):  # noqa: N802
                try:
                    if not self.path.rstrip("/").endswith("/responses"):
                        raise ValueError("only the Responses endpoint is supported")
                    size = int(self.headers.get("Content-Length", "0"))
                    if size <= 0 or size > 256 * 1024 * 1024:
                        raise ValueError("invalid Responses request size")
                    body = self.rfile.read(size)
                    payload = json.loads(body)
                    if uses_chat_leg(payload.get("model") or MODEL_ID):
                        proxy.serve_chat_leg(self, payload)
                    else:
                        proxy.serve_passthrough(self, body, payload)
                except UpstreamHTTPError as error:
                    # Forwarded verbatim so Codex applies its own retry policy.
                    if error.exhausted:
                        print(
                            f"MODELROUTER_TRANSIENT_HTTP_{error.code} exhausted "
                            f"after {MODELROUTER_RETRIES + 1} attempts",
                            flush=True,
                        )
                    else:
                        print(
                            f"MODELROUTER_UPSTREAM_HTTP_{error.code} forwarded to Codex",
                            flush=True,
                        )
                    self._send_bytes(error.code, error.content_type, error.body)
                except Exception as exc:  # noqa: BLE001
                    print(f"MODELROUTER_BRIDGE_ERROR {exc}", flush=True)
                    self._send_bytes(
                        502,
                        "application/json",
                        json.dumps(
                            {"error": {"message": str(exc), "type": "bridge_error"}}
                        ).encode("utf-8"),
                    )

            def _send_bytes(self, code, content_type, body):
                try:
                    self.send_response(code)
                    self.send_header("Content-Type", content_type)
                    self.send_header("Content-Length", str(len(body)))
                    self.end_headers()
                    self.wfile.write(body)
                except (BrokenPipeError, ConnectionResetError):
                    return

            def log_message(self, _format, *_args):
                return

        self.server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self.server.daemon_threads = True
        self.thread = threading.Thread(target=self.server.serve_forever, daemon=True)
        self.thread.start()
        return self

    @property
    def base_url(self):
        return f"http://127.0.0.1:{self.server.server_port}/v1"

    def __exit__(self, _exc_type, _exc, _traceback):
        if self.server is not None:
            self.server.shutdown()
            self.server.server_close()
        if self.thread is not None:
            self.thread.join(timeout=5)
        return False


def _write_synthetic_stream(handler, response):
    """Emit one complete Responses object as the SSE stream Codex expects."""
    created = dict(response)
    created.update({"status": "in_progress", "completed_at": None, "output": [], "usage": None})
    events = [{"type": "response.created", "sequence_number": 0, "response": created}]
    sequence = 1
    for output_index, item in enumerate(response["output"]):
        for kind in ("response.output_item.added", "response.output_item.done"):
            events.append(
                {
                    "type": kind,
                    "sequence_number": sequence,
                    "output_index": output_index,
                    "item": item,
                }
            )
            sequence += 1
    events.append(
        {"type": "response.completed", "sequence_number": sequence, "response": response}
    )
    body = (
        "".join(
            f"event: {event['type']}\ndata: {json.dumps(event, ensure_ascii=False)}\n\n"
            for event in events
        )
        + "data: [DONE]\n\n"
    ).encode("utf-8")
    handler.send_response(200)
    handler.send_header("Content-Type", "text/event-stream")
    handler.send_header("Cache-Control", "no-cache")
    handler.send_header("Content-Length", str(len(body)))
    handler.end_headers()
    handler.wfile.write(body)


# --------------------------------------------------------------------------- #
# Runtime
# --------------------------------------------------------------------------- #


def connectivity_smoke(endpoint_index=0):
    """Verify the configured key, URL, and model on the leg the model will use.

    The Responses leg sends a function tool together with a reasoning effort so
    a provider that rejects that combination is detected here.
    """
    key, urls, base_url = _credentials(endpoint_index)
    secrets = [key, *urls, base_url]
    expected = "LEANMARATHON_OK"
    chat_leg = uses_chat_leg(MODEL_ID)
    if chat_leg:
        url = base_url.rstrip("/") + "/chat/completions"
        payload = {
            "model": MODEL_ID,
            "messages": [{"role": "user", "content": f"Reply with exactly {expected}"}],
            "max_tokens": 32,
        }
    else:
        url = base_url.rstrip("/") + "/responses"
        payload = {
            "model": MODEL_ID,
            "instructions": "You are a smoke test.",
            "input": [
                {
                    "type": "message",
                    "role": "user",
                    "content": [
                        {"type": "input_text", "text": f"Reply with exactly {expected}"}
                    ],
                }
            ],
            "tools": [
                {
                    "type": "function",
                    "name": "noop",
                    "description": "Never call this tool.",
                    "parameters": {
                        "type": "object",
                        "properties": {},
                        "additionalProperties": False,
                    },
                }
            ],
            "tool_choice": "auto",
            "reasoning": {"effort": "high"},
            "include": ["reasoning.encrypted_content"],
            "store": False,
            "prompt_cache_key": "leanmarathon-smoke",
        }
    request = urllib.request.Request(
        url,
        data=json.dumps(payload, ensure_ascii=False).encode("utf-8"),
        method="POST",
        headers={
            "Authorization": f"Bearer {key}",
            "Content-Type": "application/json",
            "Accept": "application/json",
        },
    )
    try:
        with urllib.request.urlopen(request, timeout=180) as response:
            raw = response.read().decode("utf-8", errors="replace")
        document = json.loads(raw)
        if chat_leg:
            chat = _unwrap_chat_response(document)
            output = _content_text(chat.get("choices", [{}])[0].get("message", {}).get("content"))
        else:
            output = "".join(
                _content_text(item.get("content"))
                for item in document.get("output") or []
                if isinstance(item, dict) and item.get("type") == "message"
            )
    except urllib.error.HTTPError as error:
        detail = _redact(error.read().decode("utf-8", errors="replace")[:2000], secrets)
        raise RuntimeError(f"ModelRouter connectivity smoke failed: HTTP {error.code} {detail}")
    except (OSError, ValueError, KeyError, IndexError, json.JSONDecodeError) as error:
        detail = _redact(str(error), secrets)
        raise RuntimeError(f"ModelRouter connectivity smoke failed: {detail}") from error
    if expected not in output:
        raise RuntimeError("ModelRouter connectivity smoke returned an unexpected response")
    leg = "chat" if chat_leg else "responses"
    print(f"MODELROUTER_SMOKE_OK model={MODEL_ID} leg={leg} endpoint_index={endpoint_index}")


def prepare_codex_home(codex_home, endpoint_index=0):
    """Create a private job-level Codex config without persisting API_KEY or API_URL."""
    codex_home = _reject_user_codex_home(codex_home)
    _credentials(endpoint_index)
    codex_home.mkdir(parents=True, exist_ok=True)
    config = codex_home / "config.toml"
    config.write_text(
        "\n".join(
            [
                f'model = "{MODEL_ID}"',
                f'model_provider = "{PROVIDER_ID}"',
                'model_reasoning_effort = "high"',
                "model_context_window = 272000",
                # Upstream 4xx and 5xx replies are forwarded unchanged, so Codex
                # owns retry and stream-recovery for the passthrough leg.
                "request_max_retries = 4",
                "stream_max_retries = 5",
                "stream_idle_timeout_ms = 600000",
                "",
                f"[model_providers.{PROVIDER_ID}]",
                'name = "ModelRouter"',
                'base_url = "http://127.0.0.1:1/v1"',
                f'env_key = "{PROXY_ENV_KEY}"',
                'wire_api = "responses"',
                "requires_openai_auth = false",
                "",
            ]
        ),
        encoding="utf-8",
    )
    config.chmod(0o600)
    return config


def run_codex(command, codex_home, endpoint_index=0):
    """Run Codex through a private loopback proxy in front of ModelRouter."""
    codex_home = _reject_user_codex_home(codex_home)
    key, urls, base_url = _credentials(endpoint_index)
    config = codex_home / "config.toml"
    if not config.is_file():
        raise ValueError("temporary Codex config has not been prepared")
    config_text = config.read_text(encoding="utf-8", errors="replace")
    if key in config_text or any(secret in config_text for secret in [*urls, base_url]):
        raise ValueError("temporary Codex provider config failed its credential isolation check")
    environment = _isolated_codex_environment()
    environment.pop("API_KEY", None)
    environment.pop("API_URL", None)
    environment["CODEX_HOME"] = str(codex_home)
    environment[PROXY_ENV_KEY] = "local-loopback-only"
    with ModelRouterProxy(
        base_url, key, usage_path=codex_home / "sessions" / "modelrouter-usage.jsonl"
    ) as proxy:
        active_config, substitutions = re.subn(
            r'base_url = "http://127\.0\.0\.1:\d+/v1"',
            lambda _: f"base_url = {json.dumps(proxy.base_url)}",
            config_text,
        )
        if not substitutions:
            raise ValueError("temporary Codex provider config has no loopback placeholder")
        config.write_text(active_config, encoding="utf-8")
        try:
            process = subprocess.Popen(
                command,
                env=environment,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                bufsize=1,
            )
            assert process.stdout is not None
            for line in process.stdout:
                print(_redact(line, [key, *urls, base_url]), end="", flush=True)
            returncode = process.wait()
        finally:
            config.write_text(
                re.sub(
                    r'base_url = "http://127\.0\.0\.1:\d+/v1"',
                    'base_url = "http://127.0.0.1:1/v1"',
                    config_text,
                ),
                encoding="utf-8",
            )
    _scrub_rollout_credentials(codex_home, [key, *urls, base_url])
    return returncode


def _scrub_rollout_credentials(codex_home, secrets):
    """Redact credentials echoed by upstream errors without destroying resume state."""
    replacements = tuple(secret for secret in secrets if secret)
    if not replacements:
        return
    for path in codex_home.rglob("*.jsonl"):
        text = path.read_text(encoding="utf-8", errors="replace")
        scrubbed = text
        for secret in replacements:
            scrubbed = scrubbed.replace(secret, "<REDACTED>")
        if scrubbed != text:
            path.write_text(scrubbed, encoding="utf-8")


def _clean_codex_home_files(codex_home, secrets):
    """Retain only credential-free rollout JSONL files needed for resume."""
    sessions = codex_home / "sessions"
    if sessions.is_dir():
        _scrub_rollout_credentials(codex_home, secrets)
        for item in sessions.rglob("*"):
            if item.is_symlink():
                item.unlink(missing_ok=True)
            elif item.is_file() and item.suffix != ".jsonl":
                item.unlink(missing_ok=True)
    if codex_home.exists():
        for child in list(codex_home.iterdir()):
            if child == sessions:
                continue
            if child.is_symlink() or child.is_file():
                child.unlink(missing_ok=True)
            elif child.is_dir():
                shutil.rmtree(child, ignore_errors=True)
    if sessions.is_dir():
        directories = (path for path in sessions.rglob("*") if path.is_dir())
        for path in sorted(directories, key=lambda value: len(value.parts), reverse=True):
            try:
                path.rmdir()
            except OSError:
                pass


def clean_codex_home(codex_home, endpoint_index=0):
    """Retain only credential-free rollout JSONL files needed for session resume."""
    codex_home = _reject_user_codex_home(codex_home)
    key, urls, base_url = _credentials(endpoint_index)
    _clean_codex_home_files(codex_home, [key, *urls, base_url])


def main():
    """Expose prepare, exec, and cleanup operations for the harness adapters."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--codex-home", required=True, type=Path)
    parser.add_argument("--endpoint-index", type=int, default=0)
    parser.add_argument("operation", choices=("smoke", "prepare", "exec", "cleanup"))
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if args.operation == "smoke":
        connectivity_smoke(args.endpoint_index)
        return 0
    if args.operation == "prepare":
        prepare_codex_home(args.codex_home, args.endpoint_index)
        return 0
    if args.operation == "cleanup":
        clean_codex_home(args.codex_home, args.endpoint_index)
        return 0
    command = list(args.command)
    if command and command[0] == "--":
        command.pop(0)
    if not command:
        parser.error("exec requires a command after --")
    return run_codex(command, args.codex_home, args.endpoint_index)


if __name__ == "__main__":
    raise SystemExit(main())

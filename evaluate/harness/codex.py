"""Codex harness adapter.

Codex runs through the ModelRouter proxy runtime (`utils/codex_modelrouter.py`),
which keeps credentials out of the Codex configuration and records authoritative proxy token
usage. Codex owns its session identifiers, so the first turn discovers the id from the retained
rollout and later turns continue with `codex exec resume`.
"""

import sys
import time
from pathlib import Path

from utils.claude_runtime import sanitized_environment
from utils.codex_usage import (
    find_session_rollout,
    session_ids_from_rollouts,
    usage_from_proxy_records,
    usage_from_rollout,
)

from harness.base import empty_usage, endpoint_error, invocation_id, run_process, write_transcript

TASK_PREFIX = (
    "You are evaluated on one benchmark task inside this workspace. Read the task brief and the "
    "files under input/, then write the requested deliverable under output/ using your tools. "
    "Never modify anything under input/.\n\n"
)


def _shared_usage(usage):
    """Map Codex usage fields onto the shared four-field usage shape."""
    return {
        "input_tokens": int(usage.get("input_tokens", 0)),
        "cache_creation_input_tokens": int(usage.get("cache_write_input_tokens", 0)),
        "cache_read_input_tokens": int(usage.get("cached_input_tokens", 0)),
        "output_tokens": int(usage.get("output_tokens", 0)),
    }


def _prepare(runtime, codex_home, environment):
    """Create the isolated Codex configuration once per session."""
    if (Path(codex_home) / "config.toml").is_file():
        return
    Path(codex_home).mkdir(parents=True, exist_ok=True)
    run_process(
        [
            sys.executable,
            str(runtime),
            "--codex-home",
            str(codex_home),
            "prepare",
        ],
        cwd=Path(codex_home),
        env=environment,
        timeout=300,
    )


def run_turn(
    *,
    runtime,
    binary,
    model,
    prompt,
    workspace,
    codex_home,
    session_id,
    resume,
    timeout,
    transcript_dir,
    sandbox=(),
    task_prefix=TASK_PREFIX,
):
    """Run one Codex turn in the workspace and return its status, text, and usage."""
    codex_home = Path(codex_home)
    workspace = Path(workspace)
    environment = sanitized_environment()
    environment["LEANMARATHON_MODEL"] = model
    _prepare(runtime, codex_home, environment)
    name = invocation_id()
    last_message = codex_home / f"last-message-{name}.txt"
    codex_command = [binary, "exec"]
    if resume and session_id:
        codex_command += ["resume", session_id]
    codex_command += [
        "--model",
        model,
        "--sandbox",
        "workspace-write",
        "--skip-git-repo-check",
        "--cd",
        str(workspace),
        "--output-last-message",
        str(last_message),
        task_prefix + prompt,
    ]
    command = [
        sys.executable,
        str(runtime),
        "--codex-home",
        str(codex_home),
        "exec",
        "--",
        *codex_command,
    ]
    started = time.time()
    result = run_process([*sandbox, *command], cwd=workspace, env=environment, timeout=timeout)
    write_transcript(transcript_dir, name, result["stdout"], result["stderr"])
    active = session_id
    if not resume or not active:
        discovered = session_ids_from_rollouts(codex_home, started - 10)
        if discovered:
            active = discovered[-1]
    usage = empty_usage()
    proxy = usage_from_proxy_records(codex_home / "sessions" / "modelrouter-usage.jsonl", started - 10)
    if any(proxy.values()):
        usage = _shared_usage(proxy)
    elif active:
        rollout = find_session_rollout(codex_home, active)
        if rollout is not None:
            usage = _shared_usage(usage_from_rollout(rollout, started - 10))
    text = last_message.read_text(encoding="utf-8", errors="replace").strip() if last_message.is_file() else ""
    if last_message.is_file():
        last_message.unlink()
    status = "timed_out" if result["timed_out"] else ("completed" if result["exit_code"] == 0 else "failed")
    return {
        "status": status,
        "text": text,
        "session_id": active,
        "usage": usage,
        "exit_code": result["exit_code"],
        "invocation_id": name,
        "endpoint_error": None if status == "completed" else endpoint_error(result["stdout"], result["stderr"]),
    }

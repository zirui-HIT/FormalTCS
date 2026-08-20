"""Credential and environment helpers for Claude Code runtimes."""

import os
from urllib.parse import urlsplit, urlunsplit


def load_api_credentials(key_env="API_KEY", url_env="API_URL", error_type=ValueError):
    """Load a nonempty API key and one or more comma-separated endpoints from the environment."""
    key = os.environ.get(key_env)
    urls = os.environ.get(url_env)
    if not isinstance(key, str) or not key.strip() or "\n" in key or "\r" in key:
        raise error_type(f"Environment variable {key_env} must contain a nonempty API key")
    if not isinstance(urls, str) or not urls.strip():
        raise error_type(f"Environment variable {url_env} must contain at least one endpoint URL")
    endpoints = [value.strip() for value in urls.split(",") if value.strip()]
    if not endpoints:
        raise error_type(f"Environment variable {url_env} must contain at least one endpoint URL")
    return key.strip(), endpoints


def claude_code_base_urls(urls):
    """Convert gateway protocol URLs to bases compatible with Claude Code's appended /v1/messages path."""
    output = []
    for value in urls:
        parsed = urlsplit(value)
        path = parsed.path.rstrip("/")
        if "/protocol/openai" in path:
            path = path.split("/protocol/openai", 1)[0] + "/protocol/anthropic"
        elif path.endswith("/protocol/anthropic/v1"):
            path = path[:-3]
        output.append(urlunsplit((parsed.scheme, parsed.netloc, path, parsed.query, parsed.fragment)))
    return output


def sanitized_environment(source=None):
    """Copy an environment while removing inherited API credentials."""
    environment = dict(source if source is not None else os.environ)
    for name in tuple(environment):
        if name.endswith("_API_KEY") or name.endswith("_API_TOKEN"):
            environment.pop(name, None)
    return environment


def redact_secret(value, secret):
    """Replace an exact secret value in text with a stable marker."""
    return value.replace(secret, "<REDACTED>")

"""Shared plumbing for harness adapters: transcripts, timeouts, and usage shape.

Every adapter exposes `run_turn(...) -> dict` with the keys `status` (`completed`, `failed`,
or `timed_out`), `text`, `session_id`, `usage`, `exit_code`, and `endpoint_error` (`quota`,
`auth`, or `None`). Usage always uses the four-field Anthropic-style shape so one pricing
routine covers every harness.
"""

import os
import re
import signal
import subprocess
import uuid
from pathlib import Path

from utils.claude_runtime import redact_secret

USAGE_FIELDS = (
    "input_tokens",
    "cache_creation_input_tokens",
    "cache_read_input_tokens",
    "output_tokens",
)

# Endpoint-side refusals: the shared account is out of quota for this minute, or its key was
# disabled. Neither says anything about the model, so they must not spend a cell's attempts.
QUOTA_RE = re.compile(
    r"insufficient_quota|Allocated quota exceeded|rate.?limit|too many requests|"
    r"Request rejected \(429\)|\b429\b",
    re.I,
)
AUTH_RE = re.compile(r"\bFailed to authenticate\b|invalid_api_key|\bunauthorized\b|API密钥状态异常", re.I)


def endpoint_error(*streams):
    """Classify raw harness output as an endpoint refusal: `quota`, `auth`, or `None`."""
    text = "\n".join(stream for stream in streams if stream)
    if QUOTA_RE.search(text):
        return "quota"
    if AUTH_RE.search(text):
        return "auth"
    return None


def empty_usage():
    """Return a zero-valued usage record in the shared four-field shape."""
    return {field: 0 for field in USAGE_FIELDS}


def invocation_id():
    """Return an opaque identifier for one harness invocation."""
    return str(uuid.uuid4())


def write_transcript(transcript_dir, name, stdout, stderr):
    """Persist one invocation's raw streams for post-mortem debugging."""
    directory = Path(transcript_dir)
    directory.mkdir(parents=True, exist_ok=True)
    (directory / f"{name}.stdout.txt").write_text(stdout, encoding="utf-8")
    (directory / f"{name}.stderr.txt").write_text(stderr, encoding="utf-8")


def sandbox_command(command, *, mask=(), read_only=(), writable=()):
    """Wrap a harness command in a bwrap sandbox that hides everything but its own workspace."""
    prefix = ["bwrap", "--bind", "/", "/", "--proc", "/proc", "--dev", "/dev", "--die-with-parent"]
    for path in mask:
        prefix += ["--tmpfs", str(path)]
    for path in read_only:
        prefix += ["--ro-bind", str(path), str(path)]
    for path in writable:
        prefix += ["--bind", str(path), str(path)]
    return [*prefix, *command]


def run_process(command, *, cwd, env, timeout, secrets=(), stdin=None):
    """Run one harness process in its own process group and always return redacted output."""
    process = subprocess.Popen(
        command,
        cwd=str(cwd),
        env=env,
        stdin=subprocess.PIPE if stdin is not None else subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=True,
    )
    timed_out = False
    try:
        stdout, stderr = process.communicate(input=stdin, timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        stdout, stderr = process.communicate()
    for secret in secrets:
        if not secret:
            continue
        stdout = redact_secret(stdout or "", secret)
        stderr = redact_secret(stderr or "", secret)
    return {
        "stdout": stdout or "",
        "stderr": stderr or "",
        "exit_code": None if timed_out else process.returncode,
        "timed_out": timed_out,
    }

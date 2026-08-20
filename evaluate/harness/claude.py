"""Claude Code harness adapter.

Claude Code runs headless in the task workspace with its normal file and shell tools, so the
model reads `input/` and writes `output/` itself. The caller owns the session identifier, so a
turn either opens that session (`--session-id`) or continues it (`--resume`).
"""

import json
from pathlib import Path

from utils.claude_runtime import claude_code_base_urls, sanitized_environment
from utils.claude_usage import normalize_usage

from harness.base import empty_usage, endpoint_error, invocation_id, run_process, write_transcript

SYSTEM_PROMPT = (
    "You are evaluated on one benchmark task inside this workspace. Read the task brief and the "
    "files under input/, then write the requested deliverable under output/ using your tools. "
    "Never modify anything under input/."
)


def run_turn(
    *,
    binary,
    model,
    prompt,
    workspace,
    session_id,
    resume,
    timeout,
    base_url,
    api_key,
    transcript_dir,
    sandbox=(),
    allow_tools=True,
):
    """Run one Claude Code turn in the workspace and return its status, text, and usage."""
    environment = sanitized_environment()
    environment["ANTHROPIC_BASE_URL"] = claude_code_base_urls([base_url])[0]
    environment["ANTHROPIC_AUTH_TOKEN"] = api_key
    environment["CLAUDE_CODE_DISABLE_EXPERIMENTAL_BETAS"] = "1"
    command = [
        binary,
        "--print",
        "--output-format",
        "json",
        "--disable-slash-commands",
        "--permission-mode",
        "bypassPermissions",
        "--system-prompt",
        SYSTEM_PROMPT,
        "--model",
        model,
    ]
    if not allow_tools:
        command += ["--tools", ""]
    command += ["--resume" if resume else "--session-id", session_id]
    name = invocation_id()
    result = run_process(
        [*sandbox, *command],
        cwd=Path(workspace),
        env=environment,
        timeout=timeout,
        secrets=[api_key],
        stdin=prompt,
    )
    write_transcript(transcript_dir, name, result["stdout"], result["stderr"])
    usage = empty_usage()
    text = ""
    status = "timed_out" if result["timed_out"] else "failed"
    try:
        payload = json.loads(result["stdout"])
    except json.JSONDecodeError:
        payload = None
    if isinstance(payload, dict):
        usage = normalize_usage(payload.get("usage", {}))
        value = payload.get("result")
        text = value if isinstance(value, str) else json.dumps(value, ensure_ascii=False)
        if result["exit_code"] == 0 and not payload.get("is_error"):
            status = "completed"
    return {
        "status": status,
        "text": text,
        "session_id": session_id,
        "usage": usage,
        "exit_code": result["exit_code"],
        "invocation_id": name,
        "endpoint_error": None if status == "completed" else endpoint_error(result["stdout"], result["stderr"]),
    }

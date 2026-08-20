"""DeepSeek Harness (`dsh`) adapter.

`dsh --profile headless` mints a fresh random session id on every launch, so it cannot
continue a conversation. This adapter therefore boots its own profile: the assets in
`dsh_profile/` (profile manifest, patch layer, and a small Cordis runner plugin) are
materialized into `<dsh_home>/profiles/evaluate/` at call time -- `dsh` only loads profiles
from `$DSH_HOME/profiles/<name>`, and `dsh_home` is per-session and disposable -- and booted
with `dsh --profile evaluate`. The runner takes the caller's session id, creates the session
on the first turn and resumes it from the JSONL persistence backend on every later turn, so
turn N+1 sees the full prior context.

Tools are the stock dsh file and shell tools running with the workspace as cwd, so the agent
reads `input/` and writes `output/` itself. Approval is forced to `never` and the sandbox root
follows the workspace, so a turn can never block on a prompt. Telemetry is disabled in the
patch layer and through `DSH_TELEMETRY_DISABLED`.

The model route is one hand-declared OpenAI-compatible provider (`api: openai-completions`)
pointed at `base_url`. Its credential is a reference name resolved at request time by the
dsh credentials service, which layers the inherited process environment over
`$DSH_HOME/.credentials.yaml`; the key is passed only through the child environment, so it
never reaches a file and is redacted out of every transcript.

Usage tokens come from the persisted session log: the runner sums the `usage` payload dsh
records on each `assistant/message` event of this turn (`inputTokens`, `outputTokens`,
`cacheReadTokens`, `cacheWriteTokens`). Measured against this endpoint, `inputTokens` is the
UNCACHED prompt tokens and the cached prefix is reported separately, so the full prompt size
is `input_tokens + cache_read_input_tokens`. The endpoint reports no cache writes, so
`cache_creation_input_tokens` stays 0 rather than being invented.

The log itself lives at `<dsh_home>/sessions/<workspace-key>/<session_id>/session.jsonl.zstd`,
where `<workspace-key>` is derived from the agent's cwd: resuming a session therefore requires
the same `workspace` and `dsh_home` as the turn that created it.
"""

import json
import shutil
from pathlib import Path

from utils.claude_runtime import redact_secret, sanitized_environment

from harness.base import USAGE_FIELDS, empty_usage, endpoint_error, invocation_id, run_process, write_transcript

PROFILE_NAME = "evaluate"
PROFILE_ASSETS = Path(__file__).resolve().parent / "dsh_profile"
PROVIDER_ID = "evaluate"
CREDENTIAL_ENV = "DSH_EVAL_CREDENTIAL"
DEFAULT_CONTEXT_WINDOW = 131072
DEFAULT_MAX_TOKENS = 65536


def _materialize_profile(dsh_home):
    """Copy the profile assets into `<dsh_home>/profiles/<PROFILE_NAME>` and return that directory."""
    directory = Path(dsh_home) / "profiles" / PROFILE_NAME
    directory.mkdir(parents=True, exist_ok=True)
    for asset in ("package.json", "cordis.patch.yml", "runner.js"):
        shutil.copyfile(PROFILE_ASSETS / asset, directory / asset)
    return directory


def _turn_environment(*, model, base_url, api_key, dsh_home, session_id, resume, prompt_file, result_file, permission_mode):
    """Build the child environment: routing config, turn inputs, and the opaque credential."""
    environment = sanitized_environment()
    environment["DSH_HOME"] = str(dsh_home)
    environment["DSH_TELEMETRY_DISABLED"] = "1"
    environment["DSH_PERMISSION_MODE"] = permission_mode
    environment["DSH_EVAL_PROVIDER"] = PROVIDER_ID
    environment["DSH_EVAL_MODEL"] = model
    environment["DSH_EVAL_BASE_URL"] = base_url
    environment["DSH_EVAL_CONTEXT_WINDOW"] = str(DEFAULT_CONTEXT_WINDOW)
    environment["DSH_EVAL_MAX_TOKENS"] = str(DEFAULT_MAX_TOKENS)
    environment["DSH_EVAL_SESSION_ID"] = session_id
    environment["DSH_EVAL_RESUME"] = "1" if resume else "0"
    environment["DSH_EVAL_PROMPT_FILE"] = str(prompt_file)
    environment["DSH_EVAL_RESULT_FILE"] = str(result_file)
    environment[CREDENTIAL_ENV] = api_key
    return environment


def _read_result(result_file, secret):
    """Load the runner's turn result, or None when it is missing or unreadable."""
    path = Path(result_file)
    if not path.is_file():
        return None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    if not isinstance(payload, dict):
        return None
    if isinstance(payload.get("text"), str):
        payload["text"] = redact_secret(payload["text"], secret)
    return payload


def _normalize_usage(value):
    """Coerce the runner's usage record into the shared four-field integer shape."""
    usage = empty_usage()
    if isinstance(value, dict):
        for field in USAGE_FIELDS:
            count = value.get(field)
            if isinstance(count, int) and not isinstance(count, bool) and count > 0:
                usage[field] = count
    return usage


def run_turn(
    *,
    dsh_binary,
    model,
    prompt,
    workspace,
    dsh_home,
    session_id,
    resume,
    timeout,
    base_url,
    api_key,
    transcript_dir,
    sandbox=(),
    permission_mode="danger-full-access",
):
    """Run one dsh turn in the workspace, resuming the caller's session, and return its outcome."""
    workspace = Path(workspace)
    dsh_home = Path(dsh_home)
    workspace.mkdir(parents=True, exist_ok=True)
    _materialize_profile(dsh_home)
    name = invocation_id()
    exchange = dsh_home / "turns" / name
    exchange.mkdir(parents=True, exist_ok=True)
    prompt_file = exchange / "prompt.txt"
    prompt_file.write_text(prompt, encoding="utf-8")
    result_file = exchange / "result.json"
    environment = _turn_environment(
        model=model,
        base_url=base_url,
        api_key=api_key,
        dsh_home=dsh_home,
        session_id=session_id,
        resume=resume,
        prompt_file=prompt_file,
        result_file=result_file,
        permission_mode=permission_mode,
    )
    result = run_process(
        [*sandbox, dsh_binary, "--profile", PROFILE_NAME],
        cwd=workspace,
        env=environment,
        timeout=timeout,
        secrets=[api_key],
    )
    write_transcript(transcript_dir, name, result["stdout"], result["stderr"])
    payload = _read_result(result_file, api_key)
    usage = _normalize_usage(payload.get("usage") if payload else None)
    text = payload.get("text", "") if payload else ""
    if result["timed_out"]:
        status = "timed_out"
    elif payload is not None and payload.get("status") == "completed" and result["exit_code"] == 0:
        status = "completed"
    else:
        status = "failed"
    return {
        "status": status,
        "text": text if isinstance(text, str) else "",
        "session_id": session_id,
        "usage": usage,
        "exit_code": result["exit_code"],
        "invocation_id": name,
        "endpoint_error": None if status == "completed" else endpoint_error(result["stdout"], result["stderr"]),
    }

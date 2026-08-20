"""Shared runtime plumbing for AutoResearch: config, Codex turns, usage accounting.

Codex turns run through the ModelRouter proxy runtime (via the evaluate harness
adapter), one persistent session per agent, with the same endpoint-refusal and zero-token
retry policy as the evaluate sweep. Every turn appends one immutable usage record with its
CNY cost.
"""

import datetime
import json
import os
import re
import sys
import threading
import time
from contextlib import contextmanager
from pathlib import Path

BASE = Path(__file__).resolve().parent
REPOSITORY_ROOT = BASE.parent
EVALUATE_ROOT = REPOSITORY_ROOT / "evaluate"
for _path in (str(REPOSITORY_ROOT), str(EVALUATE_ROOT), str(BASE)):
    if _path not in sys.path:
        sys.path.insert(0, _path)

from harness import base as harness_base  # noqa: E402  (evaluate)
from harness import codex as codex_harness  # noqa: E402  (evaluate)

from utils.claude_usage import (  # noqa: E402
    append_usage_record,
    read_usage_records,
    usage_cost_cny,
    usage_summary,
)
from utils.filesystem import append_jsonl, write_json  # noqa: E402

PATH_KEYS = ("dataset_root", "state_root", "temp_root", "results_root", "codex_runtime")
ENV_KEYS = {
    "lean_root": "LEAN_ROOT",
    "mathlib_root": "MATHLIB_ROOT",
    "codex": "CODEX_BIN",
}
AGENT_PREFIX = (
    "You are one agent of an autonomous theoretical-computer-science research loop working "
    "inside this workspace. Follow the instructions in the prompt, read and write files with "
    "your own tools, and stop when your deliverable is written.\n\n"
)

_SEMAPHORES = {}
_SEMAPHORES_LOCK = threading.Lock()


class TurnError(RuntimeError):
    """Raised when an agent turn cannot produce a usable result."""


def load_config(path=None):
    """Load the AutoResearch configuration and resolve its paths against the config file."""
    path = Path(path) if path else BASE / "config.json"
    config = json.loads(path.read_text(encoding="utf-8"))
    for key in PATH_KEYS:
        config[key] = str((path.parent / config[key]).resolve())
    for key, env in ENV_KEYS.items():
        if os.environ.get(env):
            config[key] = os.environ[env]
    if not config.get("lean_root"):
        raise TurnError("export LEAN_ROOT to the Lean toolchain prefix containing bin/lean and bin/lake")
    if not config.get("mathlib_root"):
        config["mathlib_root"] = str(Path(config["lean_root"]) / "mathlib4")
    return config


def now():
    """Return the current UTC timestamp in second resolution."""
    return datetime.datetime.now(datetime.timezone.utc).replace(microsecond=0).isoformat()


def safe_name(value):
    """Reduce an identifier to a filesystem-safe path component."""
    return re.sub(r"[^A-Za-z0-9._-]+", "-", str(value)).strip("-") or "unnamed"


@contextmanager
def endpoint_slot(config, endpoint="codex"):
    """Bound the number of concurrent harness turns per endpoint."""
    limit = max(1, int(config.get("endpoint_limits", {}).get(endpoint, 8)))
    with _SEMAPHORES_LOCK:
        semaphore = _SEMAPHORES.setdefault(endpoint, threading.Semaphore(limit))
    semaphore.acquire()
    try:
        yield
    finally:
        semaphore.release()


def brief(name):
    """Return one immutable agent brief from the prompts directory."""
    return (BASE / "prompts" / f"{name}.md").read_text(encoding="utf-8")


def turn_sandbox(config, workspace, state_dir):
    """Return the bwrap prefix that hides the repository and other runs from a turn."""
    return harness_base.sandbox_command(
        [],
        mask=[REPOSITORY_ROOT, Path(config["temp_root"])],
        read_only=[REPOSITORY_ROOT / "utils"],
        writable=[Path(workspace), Path(state_dir)],
    )


def record_usage(usage_path, *, phase, model, result, pricing, started):
    """Append one immutable usage record for a finished turn."""
    usage = result["usage"]
    append_usage_record(
        usage_path,
        {
            "phase": phase,
            "model": model,
            "session_id": result.get("session_id"),
            "invocation_id": result.get("invocation_id"),
            "status": result["status"],
            "exit_code": result.get("exit_code"),
            "usage": usage,
            "cost_cny": usage_cost_cny(usage, pricing) if pricing else None,
            "duration_seconds": round(time.monotonic() - started, 3),
            "finished_at": now(),
        },
    )


def run_agent_turn(
    config,
    *,
    phase,
    prompt,
    workspace,
    codex_home,
    session,
    state_dir,
    timeout,
    task_prefix=AGENT_PREFIX,
    settings=None,
    sandbox_root=None,
):
    """Run one Codex turn, retrying endpoint refusals, and update the session record.

    ``session`` is a mutable dict with ``session_id`` and ``started`` keys owned by the caller;
    it is updated in place so an interrupted loop resumes the same conversation. The turn's
    working directory is ``workspace``; ``sandbox_root`` widens the writable sandbox to a
    parent (the shared run workspace) when the agent must read or write outside its own
    working directory.
    """
    settings = settings or config.get("generation", {})
    backoff = int(settings.get("retry_backoff_seconds", 90))
    max_retries = int(settings.get("max_endpoint_retries", 5))
    usage_path = Path(state_dir) / "usage.jsonl"
    transcript_dir = Path(state_dir) / "transcripts"
    sandbox = turn_sandbox(config, sandbox_root or workspace, state_dir)
    endpoint_retries = 0
    rotations = 0
    while True:
        started = time.monotonic()
        with endpoint_slot(config):
            result = codex_harness.run_turn(
                runtime=config["codex_runtime"],
                binary=config["codex"],
                model=config["model"],
                prompt=prompt,
                workspace=workspace,
                codex_home=codex_home,
                session_id=session.get("session_id"),
                resume=bool(session.get("started")),
                timeout=int(timeout),
                transcript_dir=transcript_dir,
                sandbox=sandbox,
                task_prefix=task_prefix,
            )
        record_usage(
            usage_path,
            phase=phase,
            model=config["model"],
            result=result,
            pricing=config.get("pricing"),
            started=started,
        )
        if result.get("session_id"):
            session["session_id"] = result["session_id"]
            session["started"] = True
        if result["status"] == "completed":
            return result
        error = result.get("endpoint_error")
        if error:
            endpoint_retries += 1
            if endpoint_retries >= max_retries:
                raise TurnError(f"{phase}: endpoint refused the turn {endpoint_retries} times ({error})")
            time.sleep(backoff * (5 if error == "auth" else 3))
            continue
        if not any(result["usage"].values()) and rotations < 1:
            rotations += 1
            session["session_id"] = None
            session["started"] = False
            time.sleep(backoff)
            continue
        raise TurnError(f"{phase}: turn ended with status {result['status']}")


def run_check_script(config, script, timeout=None):
    """Run one check.sh authoritatively and return its exit code and combined output."""
    timeout = int(timeout or config["compile_timeout_seconds"])
    started = time.monotonic()
    result = harness_base.run_process(
        ["bash", str(Path(script).resolve())],
        cwd=Path(script).resolve().parent,
        env=os.environ.copy(),
        timeout=timeout,
    )
    output = (result["stdout"] + result["stderr"]).strip()
    if result["timed_out"]:
        output = (output + f"\n[compile timed out after {timeout}s]").strip()
    return {
        "ok": (not result["timed_out"]) and result["exit_code"] == 0,
        "exit_code": result["exit_code"],
        "output": output,
        "duration_seconds": round(time.monotonic() - started, 3),
    }


def usage_totals(paths):
    """Aggregate token totals, priced cost, and calls over usage files."""
    records = []
    for path in sorted(Path(p) for p in paths):
        for record in read_usage_records(path):
            usage = dict(record.get("usage") or {})
            usage["cost_cny"] = record.get("cost_cny") or 0.0
            records.append(usage)
    return usage_summary(records)


def save_state(state_dir, state):
    """Persist one state dict atomically enough for a crash between turns."""
    write_json(Path(state_dir) / "state.json", state)


def load_state(state_dir):
    """Load one state dict, or None when it does not exist yet."""
    path = Path(state_dir) / "state.json"
    if not path.is_file():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def append_claim(config, record):
    """Append one accepted claim to the published candidate pool."""
    append_jsonl(Path(config["results_root"]) / "claims.jsonl", record)

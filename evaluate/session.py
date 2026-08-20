"""Resumable session state and immutable token accounting for one benchmark cell.

A benchmark cell is one (configuration, dataset item, task) triple. Each cell owns exactly one
harness session: `state.json` records the session identity and progress so an interrupted run
resumes the same conversation instead of restarting it, and `usage.jsonl` keeps one immutable
record per model invocation with its token counts and CNY cost.
"""

import json
import re
from datetime import datetime, timezone
from pathlib import Path

from utils.claude_usage import (
    add_usage,
    append_usage_record,
    empty_usage,
    normalize_usage,
    read_usage_records,
    usage_cost_cny,
)

STATE_VERSION = "1.0"
SAFE_NAME_RE = re.compile(r"[^A-Za-z0-9._-]+")


def now():
    """Return the current UTC timestamp in second resolution."""
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def safe_name(value):
    """Reduce an identifier to a filesystem-safe path component."""
    return SAFE_NAME_RE.sub("-", str(value)).strip("-") or "unnamed"


def cell_dirs(config, config_name, item_id, task):
    """Return the persistent state directory and the disposable workspace of one cell."""
    parts = (safe_name(config_name), safe_name(item_id), safe_name(task))
    return (
        Path(config["state_root"]).joinpath(*parts),
        Path(config["temp_root"]).joinpath(*parts),
    )


def ensure_state(state_dir, *, config_name, item_id, task, input_fingerprint):
    """Load the cell state, or create it, refusing to reuse a session across changed inputs."""
    path = Path(state_dir) / "state.json"
    if path.is_file():
        state = json.loads(path.read_text(encoding="utf-8"))
        if state.get("input_fingerprint") != input_fingerprint:
            state["input_fingerprint"] = input_fingerprint
            state["session_id"] = None
            state["session_started"] = False
            state["turns"] = 0
            state["invocations"] = 0
            state["rotated"] = False
            state["grade"] = None
            state["stage"] = "prepared"
            state["history"] = [*state.get("history", []), {"reset_at": now(), "reason": "inputs changed"}]
            save_state(state_dir, state)
        return state
    state = {
        "schema_version": STATE_VERSION,
        "config": config_name,
        "item": item_id,
        "task": task,
        "input_fingerprint": input_fingerprint,
        "session_id": None,
        "session_started": False,
        "turns": 0,
        "stage": "prepared",
        "grade": None,
        "last_error": None,
        "created_at": now(),
        "updated_at": now(),
    }
    save_state(state_dir, state)
    return state


def save_state(state_dir, state):
    """Persist the cell state atomically enough for a crash between turns."""
    path = Path(state_dir) / "state.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    state["updated_at"] = now()
    temporary = path.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(state, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def rotate_session(state_dir, state, reason):
    """Archive an unusable session and let the next turn open a fresh one."""
    state.setdefault("history", []).append(
        {
            "archived_at": now(),
            "reason": reason,
            "session_id": state.get("session_id"),
            "turns": state.get("turns", 0),
        }
    )
    state["session_id"] = None
    state["session_started"] = False
    state["turns"] = 0
    save_state(state_dir, state)


def cost_of(usage, pricing):
    """Return the CNY cost of one usage record, or None when the model has no published price."""
    if not pricing:
        return None
    return usage_cost_cny(usage, pricing)


def record_usage(state_dir, record):
    """Append one immutable usage record for this cell."""
    append_usage_record(Path(state_dir) / "usage.jsonl", record)


def summarize_usage(paths):
    """Aggregate token totals, priced cost, and unpriced calls over usage files."""
    total = empty_usage()
    cost = 0.0
    calls = 0
    unpriced = 0
    for path in paths:
        for record in read_usage_records(path):
            usage = normalize_usage(record.get("usage", {}))
            total = add_usage(total, usage)
            calls += 1
            value = record.get("cost_cny")
            if isinstance(value, (int, float)):
                cost += float(value)
            else:
                unpriced += 1
    total["calls"] = calls
    total["total_input_tokens"] = (
        total["input_tokens"] + total["cache_creation_input_tokens"] + total["cache_read_input_tokens"]
    )
    total["cost_cny"] = round(cost, 6)
    total["unpriced_calls"] = unpriced
    return total


def usage_files(state_root):
    """Find every usage file below a state root."""
    root = Path(state_root)
    if not root.is_dir():
        return []
    return sorted(root.glob("*/*/*/usage.jsonl"))

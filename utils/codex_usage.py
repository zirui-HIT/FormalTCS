"""Codex rollout token accounting and CNY pricing helpers."""

import datetime
import json
from pathlib import Path


USAGE_FIELDS = (
    "input_tokens",
    "cached_input_tokens",
    "cache_write_input_tokens",
    "output_tokens",
    "reasoning_output_tokens",
)

MODEL_PRICING_CNY = {
    "gpt-5.6-sol": {
        "input_per_million": 1.75,
        "output_per_million": 10.5,
        "cached_input_per_million": 0.175,
        "cache_write_input_per_million": 2.1875,
    },
    "claude-opus-4-8": {
        "input_per_million": 2.25,
        "output_per_million": 11.25,
        "cached_input_per_million": 0.225,
        "cache_write_input_per_million": 2.813,
    },
    "claude-opus-5": {
        "input_per_million": 2.25,
        "output_per_million": 11.25,
        "cached_input_per_million": 0.225,
        "cache_write_input_per_million": 2.813,
    },
}
PRICED_MODELS = frozenset(MODEL_PRICING_CNY)


def empty_usage():
    """Return a zero-valued Codex token usage record."""
    return {field: 0 for field in USAGE_FIELDS}


def _nonnegative(value):
    return int(value) if isinstance(value, (int, float)) and value >= 0 else 0


def normalize_cumulative_usage(value):
    """Convert one Codex cumulative counter into disjoint billing fields."""
    if not isinstance(value, dict):
        return empty_usage()
    total_input = _nonnegative(value.get("input_tokens", 0))
    cached = _nonnegative(value.get("cached_input_tokens", 0))
    cache_write = _nonnegative(value.get("cache_write_input_tokens", 0))
    return {
        "input_tokens": max(0, total_input - cached - cache_write),
        "cached_input_tokens": cached,
        "cache_write_input_tokens": cache_write,
        "output_tokens": _nonnegative(value.get("output_tokens", 0)),
        "reasoning_output_tokens": _nonnegative(value.get("reasoning_output_tokens", 0)),
    }


def subtract_usage(current, previous):
    """Subtract two cumulative usage records without allowing negative deltas."""
    current = normalize_cumulative_usage(current)
    previous = normalize_cumulative_usage(previous)
    return {field: max(0, current[field] - previous[field]) for field in USAGE_FIELDS}


def usage_cost_cny(usage, pricing=None, model=None):
    """Calculate CNY cost without double-counting reasoning output tokens."""
    if pricing is None:
        pricing = MODEL_PRICING_CNY.get(model)
        if pricing is None:
            raise ValueError(f"pricing unavailable for billing model: {model}")
    usage = {field: _nonnegative(usage.get(field, 0)) for field in USAGE_FIELDS}
    return round(
        usage["input_tokens"] * float(pricing["input_per_million"]) / 1_000_000
        + usage["cached_input_tokens"]
        * float(pricing["cached_input_per_million"])
        / 1_000_000
        + usage["cache_write_input_tokens"]
        * float(pricing["cache_write_input_per_million"])
        / 1_000_000
        + usage["output_tokens"] * float(pricing["output_per_million"]) / 1_000_000,
        9,
    )


def _timestamp_seconds(value):
    if not isinstance(value, str):
        return 0.0
    try:
        return datetime.datetime.fromisoformat(value.replace("Z", "+00:00")).timestamp()
    except ValueError:
        return 0.0


def usage_from_rollout(path, start_timestamp=0):
    """Return the cumulative token delta emitted after an invocation start time."""
    before = {}
    after = None
    path = Path(path)
    if not path.is_file():
        return empty_usage()
    with path.open(encoding="utf-8", errors="replace") as handle:
        for line in handle:
            try:
                event = json.loads(line)
            except json.JSONDecodeError:
                continue
            payload = event.get("payload")
            if not isinstance(payload, dict) or payload.get("type") != "token_count":
                continue
            info = payload.get("info")
            total = info.get("total_token_usage") if isinstance(info, dict) else None
            if not isinstance(total, dict):
                continue
            if _timestamp_seconds(event.get("timestamp")) < float(start_timestamp):
                before = total
            else:
                after = total
    return subtract_usage(after or {}, before)


def usage_from_proxy_records(path, start_timestamp=0):
    """Sum the ModelRouter proxy usage records emitted after an invocation start.

    Codex rollout counters report cached input but not the cache-write tokens the
    provider bills at the higher cache-creation rate, so the proxy records are
    authoritative when they exist.
    """
    path = Path(path)
    total = empty_usage()
    if not path.is_file():
        return total
    seen = False
    with path.open(encoding="utf-8", errors="replace") as handle:
        for line in handle:
            try:
                record = json.loads(line)
            except json.JSONDecodeError:
                continue
            if not isinstance(record, dict):
                continue
            try:
                timestamp = float(record.get("timestamp", 0) or 0)
            except (TypeError, ValueError):
                continue
            if timestamp < float(start_timestamp):
                continue
            usage = record.get("usage")
            if not isinstance(usage, dict):
                continue
            seen = True
            for field in USAGE_FIELDS:
                total[field] += _nonnegative(usage.get(field, 0))
    return total if seen else empty_usage()


def terminal_turn_from_rollout(path, start_timestamp=0):
    """Return terminal metadata for the last Codex turn started by an invocation."""
    path = Path(path)
    terminal = {
        "task_complete_seen": False,
        "last_agent_message_present": False,
        "output_tokens": None,
    }
    if not path.is_file():
        return terminal
    active = False
    with path.open(encoding="utf-8", errors="replace") as handle:
        for line in handle:
            try:
                event = json.loads(line)
            except json.JSONDecodeError:
                continue
            timestamp = _timestamp_seconds(event.get("timestamp"))
            if timestamp < float(start_timestamp):
                continue
            payload = event.get("payload")
            if not isinstance(payload, dict):
                continue
            if event.get("type") == "event_msg" and payload.get("type") == "task_started":
                active = True
                terminal = {
                    "task_complete_seen": False,
                    "last_agent_message_present": False,
                    "output_tokens": None,
                }
                continue
            if not active:
                continue
            if event.get("type") == "event_msg" and payload.get("type") == "token_count":
                info = payload.get("info")
                last = info.get("last_token_usage") if isinstance(info, dict) else None
                if isinstance(last, dict):
                    terminal["output_tokens"] = _nonnegative(last.get("output_tokens", 0))
            elif event.get("type") == "event_msg" and payload.get("type") == "task_complete":
                terminal["task_complete_seen"] = True
                message = payload.get("last_agent_message")
                terminal["last_agent_message_present"] = isinstance(message, str) and bool(
                    message.strip()
                )
    return terminal


def latest_completed_turn_from_rollout(path):
    """Return the newest completed turn even when a later turn was interrupted."""
    path = Path(path)
    latest = None
    active = None
    if not path.is_file():
        return None
    with path.open(encoding="utf-8", errors="replace") as handle:
        for line in handle:
            try:
                event = json.loads(line)
            except json.JSONDecodeError:
                continue
            payload = event.get("payload")
            if not isinstance(payload, dict):
                continue
            if event.get("type") == "event_msg" and payload.get("type") == "task_started":
                active = {
                    "task_complete_seen": False,
                    "last_agent_message_present": False,
                    "output_tokens": None,
                }
            elif active is not None and event.get("type") == "event_msg" and payload.get(
                "type"
            ) == "token_count":
                info = payload.get("info")
                last = info.get("last_token_usage") if isinstance(info, dict) else None
                if isinstance(last, dict):
                    active["output_tokens"] = _nonnegative(last.get("output_tokens", 0))
            elif active is not None and event.get("type") == "event_msg" and payload.get(
                "type"
            ) == "task_complete":
                active["task_complete_seen"] = True
                message = payload.get("last_agent_message")
                active["last_agent_message_present"] = isinstance(message, str) and bool(
                    message.strip()
                )
                latest = active
                active = None
    return latest


def find_session_rollout(codex_home, session_id):
    """Find a retained rollout JSONL for one exact Codex session id."""
    sessions = Path(codex_home) / "sessions"
    if not sessions.is_dir() or not session_id:
        return None
    for path in sessions.rglob("*.jsonl"):
        if session_id in path.name:
            return path
    return None


def session_ids_from_rollouts(codex_home, start_timestamp=0):
    """Discover retained Codex session ids when ``history.jsonl`` is absent.

    Some non-interactive ``codex exec`` versions write the authoritative
    ``session_meta`` event to the rollout but do not append a history entry.
    Results are ordered by session start time so callers can safely select the
    most recent invocation.
    """
    sessions = Path(codex_home) / "sessions"
    if not sessions.is_dir():
        return []
    discovered = []
    for path in sessions.rglob("*.jsonl"):
        try:
            with path.open(encoding="utf-8", errors="replace") as handle:
                first = json.loads(handle.readline())
        except (OSError, json.JSONDecodeError):
            continue
        payload = first.get("payload")
        if first.get("type") != "session_meta" or not isinstance(payload, dict):
            continue
        session_id = payload.get("session_id") or payload.get("id")
        timestamp = _timestamp_seconds(first.get("timestamp") or payload.get("timestamp"))
        if not session_id or timestamp < float(start_timestamp):
            continue
        discovered.append((timestamp, str(session_id)))
    return [session_id for _timestamp, session_id in sorted(discovered)]


def append_usage_record(path, record):
    """Append one deterministic usage record to a JSON Lines file."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")

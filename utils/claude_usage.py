"""Claude Code token accounting, persistence, and pricing helpers."""

import json
from pathlib import Path


USAGE_FIELDS = (
    "input_tokens",
    "cache_creation_input_tokens",
    "cache_read_input_tokens",
    "output_tokens",
)


def empty_usage():
    """Return a zero-valued Claude token usage record."""
    return {field: 0 for field in USAGE_FIELDS}


def normalize_usage(value):
    """Normalize nonnegative numeric token fields into integers."""
    usage = empty_usage()
    if not isinstance(value, dict):
        return usage
    for field in USAGE_FIELDS:
        candidate = value.get(field, 0)
        if isinstance(candidate, (int, float)) and candidate >= 0:
            usage[field] = int(candidate)
    return usage


def add_usage(left, right):
    """Add two Claude token usage records field by field."""
    left = normalize_usage(left)
    right = normalize_usage(right)
    return {field: left[field] + right[field] for field in USAGE_FIELDS}


def usage_cost_cny(usage, pricing):
    """Calculate the configured CNY cost of a token usage record."""
    usage = normalize_usage(usage)
    cache_read_rate = float(pricing.get("cache_read_per_million", pricing.get("cache_input_per_million", 0.0)))
    cache_creation_rate = float(pricing.get("cache_creation_per_million", cache_read_rate))
    return round(
        usage["input_tokens"] * float(pricing["input_per_million"]) / 1_000_000
        + usage["output_tokens"] * float(pricing["output_per_million"]) / 1_000_000
        + usage["cache_read_input_tokens"] * cache_read_rate / 1_000_000
        + usage["cache_creation_input_tokens"] * cache_creation_rate / 1_000_000,
        9,
    )


def usage_from_events(events):
    """Extract usage from the final result or unique assistant messages."""
    results = [event for event in events if event.get("type") == "result"]
    if results and isinstance(results[-1].get("usage"), dict):
        return normalize_usage(results[-1]["usage"])
    messages = {}
    anonymous = []
    for event in events:
        message = event.get("message")
        if not isinstance(message, dict) or not isinstance(message.get("usage"), dict):
            continue
        identifier = message.get("id")
        if isinstance(identifier, str) and identifier:
            messages[identifier] = normalize_usage(message["usage"])
        else:
            anonymous.append(normalize_usage(message["usage"]))
    total = empty_usage()
    for usage in [*messages.values(), *anonymous]:
        total = add_usage(total, usage)
    return total


def read_usage_records(path):
    """Read dictionary records from a JSON Lines usage file."""
    path = Path(path)
    if not path.is_file():
        return []
    records = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        value = json.loads(line)
        if isinstance(value, dict):
            records.append(value)
    return records


def usage_summary(records):
    """Summarize calls, token fields, total input, and recorded cost."""
    total = empty_usage()
    cost = 0.0
    for record in records:
        total = add_usage(total, record)
        cost += float(record.get("cost_cny", 0.0))
    total["cost_cny"] = round(cost, 9)
    total["calls"] = len(records)
    total["total_input_tokens"] = (
        total["input_tokens"]
        + total["cache_creation_input_tokens"]
        + total["cache_read_input_tokens"]
    )
    return total


def append_usage_record(path, record):
    """Append one usage record to a JSON Lines file."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")


def project_usage_summary(work, pattern="usage.jsonl"):
    """Summarize usage files below a project work directory."""
    work = Path(work)
    records = []
    for path in sorted(work.glob(pattern)):
        records.extend(read_usage_records(path))
    return usage_summary(records)

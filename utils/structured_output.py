"""Helpers for decoding structured data from Claude Code output."""

import json


def nested_objects(value):
    """Yield every dictionary nested in dictionaries and lists."""
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from nested_objects(child)
    elif isinstance(value, list):
        for child in value:
            yield from nested_objects(child)


def strings(value):
    """Yield every string nested in dictionaries and lists."""
    if isinstance(value, str):
        yield value
    elif isinstance(value, dict):
        for child in value.values():
            yield from strings(child)
    elif isinstance(value, list):
        for child in value:
            yield from strings(child)


def json_fragments(text):
    """Yield JSON objects embedded in arbitrary text."""
    decoder = json.JSONDecoder()
    for index, character in enumerate(text):
        if character != "{":
            continue
        try:
            value, _ = decoder.raw_decode(text[index:])
        except json.JSONDecodeError:
            continue
        if isinstance(value, dict):
            yield value


def extract_response(raw, required, error_type=ValueError):
    """Extract the first JSON object containing all required keys."""
    try:
        parsed = json.loads(raw)
    except json.JSONDecodeError:
        parsed = None
    candidates = list(strings(parsed)) if parsed is not None else []
    if parsed is not None:
        candidates.extend(json.dumps(value, ensure_ascii=False) for value in nested_objects(parsed))
    candidates.append(raw)
    for text in sorted(candidates, key=len, reverse=True):
        for value in json_fragments(text):
            if required <= value.keys():
                return value
    raise error_type(f"Claude Code response does not contain keys: {', '.join(sorted(required))}")


def extract_text_response(raw, error_type=ValueError):
    """Return a nonempty text response or raise the requested error type."""
    value = raw.strip()
    if not value:
        raise error_type("Claude Code did not return a nonempty response")
    return value


def parse_claude_events(raw):
    """Decode all JSON object events from Claude Code stream output."""
    events = []
    for line in raw.splitlines():
        try:
            value = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(value, dict):
            events.append(value)
    return events


def claude_result(events, required, error_type=ValueError):
    """Validate the final Claude Code result event and decode its payload."""
    results = [event for event in events if event.get("type") == "result"]
    if not results:
        raise error_type("Claude Code did not emit a result event")
    result = results[-1]
    if result.get("is_error") is True or result.get("subtype") not in {None, "success"}:
        message = result.get("result") or result.get("error") or "unknown error"
        raise error_type(f"Claude Code result failed: {message}")
    value = result.get("structured_output")
    if value is None:
        value = result.get("result")
    if required:
        if isinstance(value, dict) and required <= value.keys():
            return value
        raw_value = value if isinstance(value, str) else json.dumps(value, ensure_ascii=False)
        return extract_response(raw_value, required, error_type)
    raw_value = value if isinstance(value, str) else json.dumps(value, ensure_ascii=False)
    return extract_text_response(raw_value, error_type)


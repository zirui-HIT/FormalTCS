"""Filesystem, serialization, hashing, and path-safety helpers."""

import datetime
import hashlib
import json
import uuid
from pathlib import Path


def now():
    """Return the current UTC time as an ISO 8601 string."""
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def read_json(path):
    """Read and decode a UTF-8 JSON file."""
    with Path(path).open(encoding="utf-8") as handle:
        return json.load(handle)


def write_text(path, value):
    """Atomically write UTF-8 text, creating parent directories as needed."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + f".tmp.{uuid.uuid4().hex}")
    temporary.write_text(value, encoding="utf-8")
    temporary.replace(path)


def write_json(path, value):
    """Atomically write a deterministic, human-readable UTF-8 JSON file."""
    write_text(path, json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n")


def append_jsonl(path, value):
    """Append one deterministic JSON object to a JSON Lines file."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(value, ensure_ascii=False, sort_keys=True) + "\n")


def resolve_path(value, base):
    """Resolve a path relative to the supplied base directory."""
    path = Path(value)
    return path.resolve() if path.is_absolute() else (Path(base) / path).resolve()


def require_inside(path, parent, label, error_type=ValueError):
    """Resolve a path and require it to remain inside a parent directory."""
    path = Path(path).resolve()
    parent = Path(parent).resolve()
    if path != parent and parent not in path.parents:
        raise error_type(f"{label} must be inside {parent}")
    return path


def sha256_bytes(value):
    """Return the hexadecimal SHA-256 digest of a byte string."""
    return hashlib.sha256(value).hexdigest()


def sha256_file(path):
    """Return the hexadecimal SHA-256 digest of a file."""
    return sha256_bytes(Path(path).read_bytes())


def sha256_files(root, paths):
    """Hash files deterministically using their relative paths and contents."""
    root = Path(root)
    digest = hashlib.sha256()
    for path in sorted((Path(path) for path in paths), key=lambda item: item.as_posix()):
        digest.update(path.relative_to(root).as_posix().encode())
        digest.update(path.read_bytes())
    return digest.hexdigest()


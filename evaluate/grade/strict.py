"""Pass@1 grading for the theorem-proving task.

A candidate file counts only when it proves the unmodified reference statement: the statement is
compared with the published one, the sources are rejected for proof-bypassing tokens outside
comments and string literals, and the proof is then verified with `utils.leanmarathon.strict_final`,
which runs a strict compilation (`warn.sorry` as an error), an environment-level axiom audit, and a
fresh kernel replay. A verifier that cannot be run at all is reported as an error, never as a
rejected proof.
"""

import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

from dataset import attach_shared_packages, normalize_statement

REPOSITORY_ROOT = Path(__file__).resolve().parents[2]
if str(REPOSITORY_ROOT) not in sys.path:
    sys.path.insert(0, str(REPOSITORY_ROOT))

from utils.leanmarathon.verify_blueprint import mask_comments_and_strings  # noqa: E402

FORBIDDEN_TOKENS = ("sorry", "sorryAx", "sorry_using", "admit", "stop", "axiom", "native_decide", "Lean.trustCompiler")
DOTTED_NAME_TOKENS = frozenset({"sorry", "admit", "stop"})
RELAXED_OPTION_RE = re.compile(r"\bset_option\s+(warn\.sorry|warningAsError)\s+(?::=\s*)?false\b")
DECLARATION_RE = re.compile(r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(theorem|lemma)\s")
LIBRARY_MODULE = "Theorem"


def _lean_environment(config):
    """Build the shared Lean environment used by every verification step."""
    lean_root = Path(config["lean_root"])
    mathlib_root = Path(config["mathlib_root"])
    paths = [mathlib_root / ".lake" / "build" / "lib" / "lean"]
    packages = mathlib_root / ".lake" / "packages"
    if packages.is_dir():
        paths.extend(sorted(path / ".lake" / "build" / "lib" / "lean" for path in packages.iterdir()))
    environment = dict(os.environ)
    environment["LEAN_ROOT"] = str(lean_root)
    environment["MATHLIB_ROOT"] = str(mathlib_root)
    environment["PATH"] = f"{lean_root / 'bin'}:{environment.get('PATH', '')}"
    environment["LEAN_PATH"] = ":".join(str(path) for path in paths if path.is_dir())
    environment["PYTHONPATH"] = str(REPOSITORY_ROOT)
    return environment


def _lakefile(item, lean_jobs):
    """Return a Lake configuration that builds the candidate file as one library module."""
    source = (item["theorem_dir"] / "lakefile.toml").read_text(encoding="utf-8")
    lines = source.splitlines()
    first_table = next((index for index, line in enumerate(lines) if line.lstrip().startswith("[")), len(lines))
    package_keys = [line for line in lines[:first_table] if not line.startswith("moreLeanArgs")]
    tables = lines[first_table:]
    return "\n".join(
        [
            *package_keys,
            f'moreLeanArgs = ["-j", "{lean_jobs}"]',
            f'defaultTargets = ["{LIBRARY_MODULE}"]',
            "",
            *tables,
            "",
            "[[lean_lib]]",
            f'name = "{LIBRARY_MODULE}"',
            "",
        ]
    )


def _collapse(text):
    return re.sub(r"\s+", " ", text).strip()


def source_issues(candidate, item):
    """Return the reasons a candidate file cannot be accepted before any compilation."""
    masked = mask_comments_and_strings(candidate)
    if not DECLARATION_RE.search(masked):
        return ["candidate contains no top-level theorem"]
    issues = []
    for token in FORBIDDEN_TOKENS:
        boundary = r"(?<![\w'.])" if token in DOTTED_NAME_TOKENS else r"(?<![\w'])"
        if re.search(boundary + re.escape(token) + r"(?![\w'])", masked):
            issues.append(f"forbidden token in candidate source: {token}")
    for match in RELAXED_OPTION_RE.finditer(masked):
        issues.append(f"candidate source relaxes `{match.group(1)}`")
    if normalize_statement(mask_comments_and_strings(item["statement"])) not in _collapse(masked):
        issues.append("candidate does not contain the reference statement verbatim")
    return issues


def _failure_reason(failed):
    if not failed:
        return "strict verification failed"
    return "; ".join(
        f"{step.get('name')}: {_collapse(' '.join(step.get('details') or []))[:240]}".rstrip(": ")
        for step in failed
    )


def verify(config, item, candidate, verify_dir):
    """Verify one candidate proof strictly and return the Pass@1 outcome."""
    verify_dir = Path(verify_dir)
    if verify_dir.exists():
        shutil.rmtree(verify_dir)
    project = verify_dir / "project"
    project.mkdir(parents=True)
    issues = source_issues(candidate, item)
    if issues:
        return {"status": "verified", "passed": False, "reason": "; ".join(issues[:4]), "steps": []}
    for name in ("lean-toolchain", "lake-manifest.json"):
        shutil.copyfile(item["theorem_dir"] / name, project / name)
    (project / "lakefile.toml").write_text(_lakefile(item, config["lean_jobs"]), encoding="utf-8")
    (project / f"{LIBRARY_MODULE}.lean").write_text(candidate.rstrip() + "\n", encoding="utf-8")
    attach_shared_packages(project, config["mathlib_root"])
    report = verify_dir / "strict.json"
    command = [
        sys.executable,
        "-m",
        "utils.leanmarathon.strict_final",
        "--project-root",
        str(project),
        "--lean-file",
        f"{LIBRARY_MODULE}.lean",
        "--declaration",
        item["core_label"],
        "--report",
        str(report),
        "--lean-root",
        str(config["lean_root"]),
        "--timeout",
        str(config["strict_timeout_seconds"]),
    ]
    try:
        completed = subprocess.run(
            command,
            cwd=REPOSITORY_ROOT,
            env=_lean_environment(config),
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=int(config["strict_timeout_seconds"]) * 2,
            check=False,
        )
    except subprocess.TimeoutExpired:
        return {"status": "verified", "passed": False, "reason": "strict verification timed out", "steps": []}
    except OSError as error:
        return {"status": "error", "passed": False, "reason": f"strict verifier could not run: {error}", "steps": []}
    (verify_dir / "strict.log").write_text(completed.stdout or "", encoding="utf-8")
    try:
        payload = json.loads(report.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {
            "status": "error",
            "passed": False,
            "reason": f"strict verifier produced no report (exit {completed.returncode}); see {verify_dir / 'strict.log'}",
            "steps": [],
        }
    steps = payload.get("steps", [])
    failed = [step for step in steps if not step.get("passed")]
    passed = payload.get("status") == "passed" and completed.returncode == 0
    return {
        "status": "verified",
        "passed": bool(passed),
        "reason": "" if passed else _failure_reason(failed),
        "steps": [{"name": step.get("name"), "passed": step.get("passed")} for step in steps],
    }

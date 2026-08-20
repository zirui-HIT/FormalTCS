#!/usr/bin/env python3
"""Production strict verifier for completed LeanMarathon blueprint modules.

The verifier is intentionally separate from intermediate blueprint checks:
workers may still use canonical placeholders, while a completed module must
pass source scanning, a full Lake build, an environment-level axiom audit, and
fresh kernel replay.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from utils.leanmarathon import verify_blueprint


ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
FORBIDDEN_SOURCE_TOKENS = (
    "sorry_using",
    "sorryAx",
    "Lean.trustCompiler",
    "sorry",
    "admit",
    "stop",
    "axiom",
)

# `stop` and `admit` are tactics, so unlike `sorry` they are also legal identifiers.
# A file that binds one of these names is audited for tactic-position uses only:
# flagging every occurrence rejected a proof whose binder was named `stop` and cost
# one node two hours of repair rounds against a diagnostic it could not act on.
TACTIC_ONLY_TOKENS = frozenset({"stop", "admit"})

# These three also end legitimate dotted names, as in `set_option warn.sorry true` or a
# projection, so an occurrence that follows a dot is not a bypass. `sorryAx` is not in the
# set, because a qualified `Lean.sorryAx` must still be reported.
DOTTED_NAME_TOKENS = frozenset({"sorry", "admit", "stop"})

# Text that can precede a tactic, ignoring whitespace: a tactic follows `by`, a
# separator, or begins its own line inside a tactic block.
TACTIC_PREFIX = re.compile(r"(?:\bby|;|<;>|·|=>|\{|\n)[ \t]*$")

# What follows an identifier use rather than a bare tactic: an ascription, a
# projection, or an operator.  Occurrences like these are not reported for
# tactic-only tokens, because the environment axiom audit and the leanchecker
# replay are what actually guarantee no proof was bypassed; this source scan is
# defence in depth, and a false positive here costs whole pipeline hours.
IDENTIFIER_FOLLOWER = re.compile(r"[ \t]*(?::|\.|[+\-*/<>=≠≤≥^%∈∪∩])")


@dataclass
class StepResult:
    name: str
    passed: bool
    details: list[str] = field(default_factory=list)


def load_blueprint_verifier() -> Any:
    return verify_blueprint


def module_from_path(path: Path) -> str:
    without_suffix = path.with_suffix("")
    if without_suffix.is_absolute() or ".." in without_suffix.parts:
        raise ValueError(f"Lean file must be a project-relative path: {path}")
    return ".".join(part for part in without_suffix.parts if part not in ("", "."))


def lean_string(value: str) -> str:
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def tail(text: str, max_lines: int = 80) -> str:
    lines = text.splitlines()
    if len(lines) <= max_lines:
        return text.strip()
    return "\n".join(["... (truncated)", *lines[-max_lines:]]).strip()


def run_step(
    name: str,
    command: list[str],
    *,
    cwd: Path,
    env: dict[str, str],
    timeout: int,
) -> StepResult:
    try:
        proc = subprocess.run(
            command,
            cwd=str(cwd),
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return StepResult(name, False, [str(exc)])
    details = [
        value
        for value in (tail(proc.stdout), tail(proc.stderr))
        if value
    ]
    return StepResult(name, proc.returncode == 0, details)


def bound_as_identifier(masked: str, token: str) -> bool:
    """Whether the file binds ``token`` as a name, for example ``(stop : Fin n)``."""
    binder = re.compile(
        rf"[(\{{\[⟨]\s*(?:[\w']+\s+)*{re.escape(token)}(?![\w'])[^)\}}\]⟩\n]*:"
    )
    return bool(binder.search(masked))


def source_checks(
    lean_file: Path,
    verifier: Any,
    *,
    require_blueprint: bool,
) -> tuple[StepResult, list[Any]]:
    source = lean_file.read_text(encoding="utf-8")
    masked = verifier.mask_comments_and_strings(source)
    failures: list[str] = []
    for token in FORBIDDEN_SOURCE_TOKENS:
        pattern = re.compile(rf"(?<![\w']){re.escape(token)}(?![\w'])")
        tactic_position_only = token in TACTIC_ONLY_TOKENS and bound_as_identifier(
            masked, token
        )
        for match in pattern.finditer(masked):
            if token in DOTTED_NAME_TOKENS and masked[: match.start()].endswith("."):
                continue
            if token in TACTIC_ONLY_TOKENS:
                if tactic_position_only and (
                    not TACTIC_PREFIX.search(masked[: match.start()])
                    or IDENTIFIER_FOLLOWER.match(masked[match.end() :])
                ):
                    continue
            line = masked.count("\n", 0, match.start()) + 1
            failures.append(f"{lean_file}:{line}: forbidden token `{token}`")
    disabled_option = re.compile(
        r"\bset_option\s+(warn\.sorry|warningAsError)\s+(?::=\s*)?false\b"
    )
    for match in disabled_option.finditer(masked):
        line = masked.count("\n", 0, match.start()) + 1
        failures.append(
            f"{lean_file}:{line}: final source may not disable `{match.group(1)}`"
        )

    nodes, anomalies = verifier.parse_file(lean_file)
    if require_blueprint:
        failures.extend(anomalies)
        if not nodes:
            failures.append(f"{lean_file}: no blueprint declarations found")
        for node in nodes:
            if node.keyword in verifier.PROOF_KEYWORDS and node.body_kind != "complete":
                failures.append(
                    f"{lean_file}:{node.line_decl}: proof `{node.lean_name}` is not complete"
                )
    return StepResult("source audit", not failures, failures), nodes


def audit_source(module: str, declarations: list[str]) -> str:
    decls = ", ".join(lean_string(name) for name in declarations)
    allowed = ", ".join(lean_string(name) for name in sorted(ALLOWED_AXIOMS))
    return f"""import Lean
import {module}

open Lean

private def strictAudit : CoreM Unit := do
  let declarations : Array String := #[{decls}]
  let allowed : NameSet := NameSet.ofArray (#[{allowed}].map String.toName)
  let env ← getEnv
  for declaration in declarations do
    let name := declaration.toName
    match env.find? name with
    | none => throwError s!"strict audit could not find declaration '{{name}}'"
    | some (.axiomInfo _) =>
        throwError s!"strict audit rejects project axiom declaration '{{name}}'"
    | some _ => pure ()
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError s!"strict audit rejects axiom '{{axiomName}}' used by '{{name}}'"

#eval strictAudit
"""


def write_report(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project-root", required=True, type=Path)
    parser.add_argument("--lean-file", required=True, type=Path)
    parser.add_argument("--module")
    parser.add_argument("--declaration", action="append", default=[])
    parser.add_argument("--report", required=True, type=Path)
    parser.add_argument("--lean-root", type=Path)
    parser.add_argument("--timeout", type=int, default=3600)
    parser.add_argument(
        "--allow-incomplete-skip",
        action="store_true",
        help="return success without final checks when canonical placeholders remain",
    )
    args = parser.parse_args()

    project_root = args.project_root.expanduser().resolve()
    relative_lean_file = args.lean_file
    if relative_lean_file.is_absolute():
        try:
            relative_lean_file = relative_lean_file.resolve().relative_to(project_root)
        except ValueError:
            print("Lean file is outside the project root", file=sys.stderr)
            return 2
    lean_file = project_root / relative_lean_file
    module = args.module or module_from_path(relative_lean_file)
    report_path = args.report.expanduser().resolve()
    payload: dict[str, Any] = {
        "schema_version": "1.0",
        "project_root": str(project_root),
        "lean_file": str(relative_lean_file),
        "module": module,
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "status": "failed",
        "steps": [],
    }

    if not project_root.is_dir() or not lean_file.is_file():
        payload["steps"] = [
            {
                "name": "inputs",
                "passed": False,
                "details": [f"missing project root or Lean file: {lean_file}"],
            }
        ]
        write_report(report_path, payload)
        return 2

    verifier = load_blueprint_verifier()
    nodes, anomalies = verifier.parse_file(lean_file)
    incomplete = [
        node.lean_name
        for node in nodes
        if node.keyword in verifier.PROOF_KEYWORDS
        and node.body_kind in {"by_sorry", "by_sorry_using"}
    ]
    if args.allow_incomplete_skip and incomplete and not anomalies:
        payload["status"] = "skipped_incomplete"
        payload["incomplete_declarations"] = incomplete
        write_report(report_path, payload)
        print(f"SKIP strict final verification: {len(incomplete)} placeholder proof(s) remain")
        return 0

    source_result, nodes = source_checks(
        lean_file,
        verifier,
        require_blueprint=not bool(args.declaration),
    )
    results = [source_result]
    declarations = list(args.declaration) or [
        node.lean_name
        for node in nodes
        if node.keyword in verifier.PROOF_KEYWORDS and node.lean_name
    ]
    if not declarations:
        source_result.passed = False
        source_result.details.append("no theorem or lemma declarations selected for axiom audit")

    env = os.environ.copy()
    lean_root = args.lean_root or (
        Path(env["LEAN_ROOT"]).expanduser() if env.get("LEAN_ROOT") else None
    )
    if lean_root is not None:
        env["LEAN_ROOT"] = str(lean_root.resolve())
        env["PATH"] = str(lean_root.resolve() / "bin") + os.pathsep + env.get("PATH", "")

    if source_result.passed:
        results.append(
            run_step("lake build", ["lake", "build"], cwd=project_root, env=env, timeout=args.timeout)
        )
    if all(result.passed for result in results):
        results.append(
            run_step(
                "strict target compilation",
                [
                    "lake",
                    "env",
                    "lean",
                    "-Dwarn.sorry=true",
                    "-DwarningAsError=true",
                    "--",
                    str(relative_lean_file),
                ],
                cwd=project_root,
                env=env,
                timeout=args.timeout,
            )
        )
    if all(result.passed for result in results):
        with tempfile.TemporaryDirectory(prefix="leanmarathon-strict-audit-") as temp_dir:
            audit_file = Path(temp_dir) / "Audit.lean"
            audit_file.write_text(audit_source(module, declarations), encoding="utf-8")
            results.append(
                run_step(
                    "environment axiom audit",
                    ["lake", "env", "lean", "--", str(audit_file)],
                    cwd=project_root,
                    env=env,
                    timeout=args.timeout,
                )
            )
    if all(result.passed for result in results):
        checker = shutil.which("leanchecker", path=env.get("PATH")) or shutil.which(
            "lean4checker", path=env.get("PATH")
        )
        if checker is None:
            results.append(StepResult("fresh kernel replay", False, ["leanchecker was not found"]))
        else:
            results.append(
                run_step(
                    "fresh kernel replay",
                    ["lake", "env", checker, "--fresh", module],
                    cwd=project_root,
                    env=env,
                    timeout=args.timeout,
                )
            )

    passed = bool(results) and all(result.passed for result in results)
    payload["status"] = "passed" if passed else "failed"
    payload["declarations"] = declarations
    payload["steps"] = [
        {"name": result.name, "passed": result.passed, "details": result.details}
        for result in results
    ]
    write_report(report_path, payload)
    for result in results:
        print(f"{'PASS' if result.passed else 'FAIL'}  {result.name}")
        for detail in result.details:
            for line in detail.splitlines():
                print(f"      {line}")
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())

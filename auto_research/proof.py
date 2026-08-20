"""Theorem Proof (FT2FP): prove each accepted claim's statement, verified strictly.

Each accepted claim owns one resumable proof cell: a ready-to-build Lake workspace the Codex
session iterates in, then the evaluate strict verifier (strict compilation, environment-level
axiom audit, fresh kernel replay) decides Pass@1. The deliverable and verdict are published
under ``results/proofs/<claim_id>/``.
"""

import hashlib
import json
import re
import shutil
from pathlib import Path

import runtime
import workspace as ws
from grade import strict  # noqa: E402  (evaluate, imported after the runtime bootstrap)
import dataset as evaluate_dataset  # noqa: E402  (evaluate)
from utils.filesystem import write_text

STATE_VERSION = "1.0"


def _lakefile(source, lean_jobs):
    """Rewrite the published Lake configuration to compile with the requested concurrency."""
    replaced, count = re.subn(
        r"(?m)^moreLeanArgs\s*=.*$", f'moreLeanArgs = ["-j", "{lean_jobs}"]', source
    )
    if count:
        return replaced
    return source.rstrip() + f'\n\nmoreLeanArgs = ["-j", "{lean_jobs}"]\n'


def _read_output(workspace_dir):
    path = Path(workspace_dir) / "output" / "proof.lean"
    if not path.is_file():
        return None
    content = path.read_text(encoding="utf-8", errors="replace").strip()
    return content or None


def _item(claim):
    """Build the synthetic dataset item the strict verifier grades against."""
    theorem_dir = Path(claim["theorem_dir"])
    source = (theorem_dir / "theorem.lean").read_text(encoding="utf-8")
    parts, issues = ws.validate_theorem(source)
    if issues:
        raise RuntimeError(f"published theorem is invalid: {'; '.join(issues)}")
    return {
        "theorem_dir": theorem_dir,
        "theorem_source": source,
        "statement": parts["statement"],
        "core_label": ws.qualified_declaration(parts),
    }


def _prepare(config, claim, workspace_dir):
    """Materialize the immutable inputs, the Lake project, and the strict check script."""
    theorem_dir = Path(claim["theorem_dir"])
    source = (theorem_dir / "theorem.lean").read_text(encoding="utf-8")
    workspace_dir = Path(workspace_dir)
    inputs = workspace_dir / "input"
    if inputs.is_dir():
        shutil.rmtree(inputs)
    inputs.mkdir(parents=True)
    (workspace_dir / "output").mkdir(parents=True, exist_ok=True)
    write_text(inputs / "theorem.lean", source)
    project = workspace_dir / "project"
    project.mkdir(parents=True, exist_ok=True)
    for name in ws.SUPPORT_FILES:
        text = (theorem_dir / name).read_text(encoding="utf-8")
        if name == "lakefile.toml":
            text = _lakefile(text, config["lean_jobs"])
        write_text(project / name, text)
    write_text(project / "theorem.lean", source)
    evaluate_dataset.attach_shared_packages(project, config["mathlib_root"])
    script = workspace_dir / "check.sh"
    write_text(script, ws.check_script(config, "theorem.lean", True))
    script.chmod(0o755)
    write_text(workspace_dir / "TASK.md", runtime.brief("ft2fp"))
    digest = hashlib.sha256()
    digest.update(source.encode("utf-8"))
    return digest.hexdigest()


def _turn_prompt(workspace_dir, attempt):
    brief = runtime.brief("ft2fp")
    if attempt == 0:
        return (
            f"The workspace is {workspace_dir}. Its brief is also stored as TASK.md.\n\n"
            f"{brief}\n"
            "Work now: read the inputs with your tools and write the deliverable."
        )
    return (
        f"The deliverable output/proof.lean is still missing or empty in {workspace_dir}. "
        "Continue the same task, finish the remaining work, and write that file now.\n\n"
        f"{brief}"
    )


def _publish(config, claim_id, workspace_dir, outcome):
    """Mirror the proof deliverable and its verdict into the results directory."""
    target = Path(config["results_root"]) / "proofs" / claim_id
    target.mkdir(parents=True, exist_ok=True)
    source = Path(workspace_dir) / "output" / "proof.lean"
    if source.is_file():
        shutil.copyfile(source, target / "proof.lean")
    (target / "verdict.json").write_text(
        json.dumps(outcome, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    return target


def run_proof(config, claim, retry=False, regrade=False):
    """Drive one claim's proof cell to a graded verdict and return its state."""
    claim_id = runtime.safe_name(claim["claim_id"])
    state_dir = Path(config["state_root"]) / "proofs" / claim_id
    cell_dir = Path(config["temp_root"]) / "proofs" / claim_id
    workspace_dir = cell_dir / "workspace"
    verify_dir = cell_dir / "verify"
    state = runtime.load_state(state_dir)
    fingerprint = _prepare(config, claim, workspace_dir)
    if state is None or state.get("input_fingerprint") != fingerprint:
        if state is not None:
            state.update(
                input_fingerprint=fingerprint,
                session={"session_id": None, "started": False},
                invocations=0,
                grade=None,
                stage="prepared",
            )
        else:
            state = {
                "schema_version": STATE_VERSION,
                "claim_id": claim["claim_id"],
                "stage": "prepared",
                "session": {"session_id": None, "started": False},
                "invocations": 0,
                "grade": None,
                "input_fingerprint": fingerprint,
                "created_at": runtime.now(),
            }
        runtime.save_state(state_dir, state)
    if state.get("stage") == "graded" and not regrade:
        return state
    if state.get("stage") == "failed" and not retry:
        return state
    if retry:
        state["invocations"] = 0
        state["session"] = {"session_id": None, "started": False}
        runtime.save_state(state_dir, state)
    settings = config["proof"]
    item = _item(claim)
    produced = _read_output(workspace_dir) is not None
    attempt = int(state.get("invocations", 0))
    while not produced and attempt < int(settings["max_turns"]):
        state["stage"] = "running"
        runtime.save_state(state_dir, state)
        try:
            runtime.run_agent_turn(
                config,
                phase=f"{claim_id}/proof/turn-{attempt}",
                prompt=_turn_prompt(workspace_dir, attempt),
                workspace=workspace_dir,
                codex_home=state_dir / "codex-home",
                session=state["session"],
                state_dir=state_dir,
                timeout=settings["timeout_seconds"],
                task_prefix=runtime.codex_harness.TASK_PREFIX,
                settings=settings,
            )
        except runtime.TurnError as error:
            state["stage"] = "failed"
            state["last_error"] = str(error)
            runtime.save_state(state_dir, state)
            return state
        attempt += 1
        state["invocations"] = attempt
        runtime.save_state(state_dir, state)
        produced = _read_output(workspace_dir) is not None
    state["stage"] = "produced" if produced else "failed"
    runtime.save_state(state_dir, state)
    if produced:
        outcome = strict.verify(config, item, _read_output(workspace_dir), verify_dir)
        state["grade"] = outcome
        state["stage"] = "graded" if outcome.get("status") == "verified" else "produced"
        runtime.save_state(state_dir, state)
        _publish(config, claim_id, workspace_dir, outcome)
    return state

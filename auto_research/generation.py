"""Agent-loop generation: planner, formalizer, and judger iterate in one shared workspace.

One run owns one resumable state file, one shared workspace, and one Codex home. Each claim
advances planning → formalizing (at most three compiler-feedback rounds) → judging, and ends
either accepted (published under ``results/``) or discarded (with feedback the next planner
attempt reads).
"""

import json
import shutil
from pathlib import Path

import runtime
import workspace as ws
from utils.filesystem import write_text
from utils.structured_output import extract_response

COMPILER_FEEDBACK_LIMIT = 3000
STATE_VERSION = "1.0"


def new_run_state(run_id, seed, sampled_ids):
    """Return the initial state of one generation run."""
    return {
        "schema_version": STATE_VERSION,
        "run_id": run_id,
        "seed": seed,
        "sampled": sampled_ids,
        "stage": "generating",
        "claims": [],
        "created_at": runtime.now(),
        "updated_at": runtime.now(),
    }


def run_generation(config, run_id, seed):
    """Drive one generation run to completion and return (state, accepted claims)."""
    state_dir = Path(config["state_root"]) / "runs" / runtime.safe_name(run_id)
    workspace_dir = Path(config["temp_root"]) / "runs" / runtime.safe_name(run_id) / "workspace"
    items = {item["id"]: item for item in ws.load_benchmark(config)}
    state = runtime.load_state(state_dir)
    if state is None:
        sampled = ws.sample_benchmark(
            list(items.values()), config["generation"]["sample_size"], seed
        )
        state = new_run_state(run_id, seed, [item["id"] for item in sampled])
        runtime.save_state(state_dir, state)
    ws.init_run_workspace(config, [items[identifier] for identifier in state["sampled"]], workspace_dir)
    accepted = []
    while state["stage"] == "generating":
        claim = _next_claim(config, state)
        if claim is None:
            break
        runtime.save_state(state_dir, state)
        _drive_claim(config, state, claim, state_dir, workspace_dir)
        runtime.save_state(state_dir, state)
        if claim["stage"] == "accepted":
            accepted.append(claim)
            if config["generation"].get("stop_on_accept", True):
                break
    state["stage"] = "done"
    runtime.save_state(state_dir, state)
    return state, accepted


def _next_claim(config, state):
    """Return the first unfinished claim, or append a fresh one within the run budget."""
    for claim in state["claims"]:
        if claim["stage"] not in {"accepted", "discarded"}:
            return claim
    if len(state["claims"]) >= int(config["generation"]["max_claims"]):
        return None
    index = len(state["claims"]) + 1
    claim = {
        "claim_id": f"{state['run_id']}-{index}",
        "index": index,
        "stage": "planning",
        "rounds": 0,
        "sessions": {name: {"session_id": None, "started": False} for name in ("planner", "formalizer", "judger")},
        "failure": None,
        "verdict": None,
        "theorem": None,
    }
    state["claims"].append(claim)
    return claim


def _drive_claim(config, state, claim, state_dir, workspace_dir):
    """Advance one claim through its stages until it reaches a terminal stage."""
    handlers = {"planning": _plan, "formalizing": _formalize, "judging": _judge}
    while claim["stage"] in handlers:
        handlers[claim["stage"]](config, state, claim, state_dir, workspace_dir)
        runtime.save_state(state_dir, state)


def _objective_path(workspace_dir, index):
    return Path(workspace_dir) / "objectives" / f"claim-{index}.md"


def _feedback_excerpt(claim, compiler_output=""):
    parts = [claim.get("failure") or ""]
    if compiler_output:
        parts.append(f"Last compiler output:\n\n```\n{compiler_output[-COMPILER_FEEDBACK_LIMIT:]}\n```")
    return "\n\n".join(part for part in parts if part.strip())


def _write_feedback(workspace_dir, claim, compiler_output=""):
    write_text(
        Path(workspace_dir) / "feedback" / f"claim-{claim['index']}.md",
        f"# Discarded claim: {claim['claim_id']}\n\n{_feedback_excerpt(claim, compiler_output)}\n",
    )


def _discard(claim, failure):
    claim["stage"] = "discarded"
    claim["failure"] = failure


def _plan(config, state, claim, state_dir, workspace_dir):
    """Run one planner turn and check that it produced a research objective."""
    index = claim["index"]
    prompt = (
        f"The workspace is {workspace_dir}.\n\n{runtime.brief('planner')}\n\n"
        f"Instructions for this turn:\n"
        f"- Write your new research objective to objectives/claim-{index}.md now.\n"
        f"- This is attempt {index} of at most {config['generation']['max_claims']} in this run."
        + (
            " Earlier attempts in this run were discarded; read every feedback/claim-*.md before proposing."
            if index > 1
            else ""
        )
        + "\n- If the objective file already exists from an interrupted attempt, review it, finalize it, and stop.\n"
    )
    try:
        runtime.run_agent_turn(
            config,
            phase=f"{claim['claim_id']}/planner",
            prompt=prompt,
            workspace=workspace_dir,
            codex_home=Path(state_dir) / "codex-home",
            session=claim["sessions"]["planner"],
            state_dir=state_dir,
            timeout=config["generation"]["planner_timeout_seconds"],
        )
    except runtime.TurnError as error:
        _discard(claim, f"planner turn failed: {error}")
        return
    objective = _objective_path(workspace_dir, index)
    if not objective.is_file() or not objective.read_text(encoding="utf-8").strip():
        _discard(claim, "planner produced no objective file")
        return
    claim["stage"] = "formalizing"


def _template_item(config, state):
    items = {item["id"]: item for item in ws.load_benchmark(config)}
    return items[state["sampled"][0]]


def _formalizer_prompt(claim_workspace, rounds, feedback=""):
    prompt = (
        f"Your working directory is {claim_workspace}.\n\n{runtime.brief('formalizer')}\n\n"
        "Instructions for this turn:\n"
        "- Formalize the objective in objective.md into project/theorem.lean, compiling with ./check.sh until it reports no errors.\n"
    )
    if rounds > 1:
        prompt += (
            f"\nRound {rounds} of at most 3. The previous round did not yet produce an acceptable statement.\n"
            f"Compiler and validation feedback:\n\n```\n{feedback[-COMPILER_FEEDBACK_LIMIT:]}\n```\n\n"
            "Fix project/theorem.lean and compile again. If the objective cannot be formalized within this round, write failure.md in your working directory and stop.\n"
        )
    return prompt


def _formalize(config, state, claim, state_dir, workspace_dir):
    """Run up to three formalizer rounds, each followed by an authoritative compile."""
    claim_workspace = Path(workspace_dir) / "claims" / claim["claim_id"]
    objective = _objective_path(workspace_dir, claim["index"])
    if not (claim_workspace / "project" / "theorem.lean").is_file():
        if not objective.is_file():
            _discard(claim, "objective file lost from the workspace")
            return
        ws.scaffold_claim(config, claim_workspace, _template_item(config, state))
        shutil.copyfile(objective, claim_workspace / "objective.md")
    rounds = int(claim.get("rounds", 0))
    feedback = claim.get("last_feedback", "")
    if rounds >= 3:
        # Crash-resume after the last round: re-check authoritatively before discarding.
        check = runtime.run_check_script(config, claim_workspace / "check.sh")
        source = (claim_workspace / "project" / "theorem.lean").read_text(encoding="utf-8")
        _parts, issues = ws.validate_theorem(source)
        if check["ok"] and not issues:
            claim["stage"] = "judging"
            return
        _discard(
            claim,
            "statement did not compile within 3 rounds: "
            + _feedback_excerpt(claim, feedback)[:COMPILER_FEEDBACK_LIMIT],
        )
        _write_feedback(workspace_dir, claim, feedback)
        return
    while rounds < 3:
        current = rounds + 1
        try:
            runtime.run_agent_turn(
                config,
                phase=f"{claim['claim_id']}/formalizer/round-{current}",
                prompt=_formalizer_prompt(claim_workspace, current, feedback),
                workspace=claim_workspace,
                codex_home=Path(state_dir) / "codex-home",
                session=claim["sessions"]["formalizer"],
                state_dir=state_dir,
                timeout=config["generation"]["formalizer_timeout_seconds"],
                sandbox_root=workspace_dir,
            )
        except runtime.TurnError as error:
            claim["rounds"] = current
            _discard(claim, f"formalizer turn failed: {error}")
            _write_feedback(workspace_dir, claim)
            return
        rounds = current
        claim["rounds"] = rounds
        failure_note = claim_workspace / "failure.md"
        if failure_note.is_file() and failure_note.read_text(encoding="utf-8").strip():
            _discard(
                claim,
                "formalizer gave up: " + failure_note.read_text(encoding="utf-8").strip()[:COMPILER_FEEDBACK_LIMIT],
            )
            _write_feedback(workspace_dir, claim)
            return
        check = runtime.run_check_script(config, claim_workspace / "check.sh")
        source = (claim_workspace / "project" / "theorem.lean").read_text(encoding="utf-8")
        _parts, issues = ws.validate_theorem(source)
        claim["compile_ok"] = bool(check["ok"] and not issues)
        if claim["compile_ok"]:
            claim["stage"] = "judging"
            return
        feedback = "\n".join(
            [f"check.sh exited with code {check['exit_code']}.", *issues, check["output"]]
        ).strip()
        claim["last_feedback"] = feedback
        runtime.save_state(state_dir, state)
    _discard(claim, "statement did not compile within 3 rounds: " + _feedback_excerpt(claim, feedback)[:COMPILER_FEEDBACK_LIMIT])
    _write_feedback(workspace_dir, claim, feedback)


def _parse_verdict(text, judgement_file):
    """Decode the judger's verdict from its final message, falling back to its file."""
    for loader in (
        lambda: extract_response(text, {"nl_claim", "novel", "rationale"}),
        lambda: json.loads(Path(judgement_file).read_text(encoding="utf-8")),
    ):
        try:
            value = loader()
        except (ValueError, OSError, json.JSONDecodeError):
            continue
        if isinstance(value, dict) and {"nl_claim", "novel", "rationale"} <= value.keys():
            return value
    return None


def _coerce_novel(value):
    if isinstance(value, str):
        return value.strip().lower() in {"true", "yes", "1"}
    return bool(value)


def _judge(config, state, claim, state_dir, workspace_dir):
    """Run one judger turn and either accept or discard the compiled statement."""
    claim_workspace = Path(workspace_dir) / "claims" / claim["claim_id"]
    if not (claim_workspace / "project" / "theorem.lean").is_file():
        _discard(claim, "claim workspace lost before judging")
        return
    prompt = (
        f"Your working directory is {claim_workspace}.\n\n{runtime.brief('judger')}\n\n"
        "Instructions for this turn:\n"
        "- Judge the candidate now: write judgement.json in your working directory and make your final message exactly the JSON object.\n"
    )
    try:
        result = runtime.run_agent_turn(
            config,
            phase=f"{claim['claim_id']}/judger",
            prompt=prompt,
            workspace=claim_workspace,
            codex_home=Path(state_dir) / "codex-home",
            session=claim["sessions"]["judger"],
            state_dir=state_dir,
            timeout=config["generation"]["judger_timeout_seconds"],
            sandbox_root=workspace_dir,
        )
    except runtime.TurnError as error:
        _discard(claim, f"judger turn failed: {error}")
        return
    verdict = _parse_verdict(result.get("text", ""), claim_workspace / "judgement.json")
    if verdict is None:
        _discard(claim, "judger produced no parsable verdict")
        _write_feedback(workspace_dir, claim)
        return
    claim["verdict"] = {
        "nl_claim": verdict.get("nl_claim"),
        "significance": verdict.get("significance"),
        "rationale": verdict.get("rationale"),
        "novel": _coerce_novel(verdict.get("novel")),
    }
    if not claim["verdict"]["novel"]:
        _discard(claim, "judger rejected the claim: " + str(verdict.get("rationale", ""))[:COMPILER_FEEDBACK_LIMIT])
        _write_feedback(workspace_dir, claim)
        return
    published, issues = ws.publish_theorem(config, claim_workspace, claim["claim_id"])
    if issues:
        _discard(claim, "accepted statement failed validation: " + "; ".join(issues))
        _write_feedback(workspace_dir, claim)
        return
    claim["theorem"] = published
    claim["stage"] = "accepted"
    ws.accepted_summary(
        Path(workspace_dir) / "accepted" / claim["claim_id"],
        claim["claim_id"],
        claim["verdict"],
        published,
    )
    runtime.append_claim(
        config,
        {
            "claim_id": claim["claim_id"],
            "run_id": state["run_id"],
            "nl_claim": claim["verdict"]["nl_claim"],
            "significance": claim["verdict"]["significance"],
            "rationale": claim["verdict"]["rationale"],
            "objective_file": f"objectives/claim-{claim['index']}.md",
            "theorem_dir": published["theorem_dir"],
            "core_label": published["core_label"],
            "created_at": runtime.now(),
        },
    )

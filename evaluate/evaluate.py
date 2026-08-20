"""Benchmark the model and harness matrix on the four annotated Lean-4 dataset tasks.

Usage:
    python3 evaluate/evaluate.py run --config claude-opus-5 --task cc2nc --limit 4
    python3 evaluate/evaluate.py grade --task nc2ft
    python3 evaluate/evaluate.py status
    python3 evaluate/evaluate.py usage
    python3 evaluate/evaluate.py report

One (configuration, item, task) cell owns one resumable harness session: the workspace under
`temp_root` carries the inputs the model reads and the deliverable it writes, while the state and
immutable token accounting live under `state_root`.
"""

import argparse
import json
import os
import shutil
import subprocess
import sys
import threading
import time
import uuid
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

BASE = Path(__file__).resolve().parent
REPOSITORY_ROOT = BASE.parent
for path in (str(REPOSITORY_ROOT), str(BASE)):
    if path not in sys.path:
        sys.path.insert(0, path)

from utils.claude_runtime import load_api_credentials  # noqa: E402

import dataset  # noqa: E402
import session  # noqa: E402
from harness import base as harness_base  # noqa: E402
from grade import rubric, strict  # noqa: E402

PATH_KEYS = ("dataset_root", "state_root", "temp_root", "results_root", "codex_runtime")
ENV_KEYS = {
    "lean_root": "LEAN_ROOT",
    "mathlib_root": "MATHLIB_ROOT",
    "claude": "CLAUDE_BIN",
    "codex": "CODEX_BIN",
    "dsh": "DSH_BIN",
}
RUBRIC_TASKS = ("cc2nc", "c2np")


class EvaluateError(RuntimeError):
    """Raised for configuration, harness, or grading failures the operator must see."""


def load_config(path=None):
    """Load the benchmark configuration and resolve its paths against the config file."""
    path = Path(path) if path else BASE / "config" / "default.json"
    config = json.loads(path.read_text(encoding="utf-8"))
    for key in PATH_KEYS:
        config[key] = str((path.parent / config[key]).resolve())
    for key, env in ENV_KEYS.items():
        if os.environ.get(env):
            config[key] = os.environ[env]
    if not config.get("lean_root"):
        raise EvaluateError("export LEAN_ROOT to the Lean toolchain prefix containing bin/lean and bin/lake")
    if not config.get("mathlib_root"):
        config["mathlib_root"] = str(Path(config["lean_root"]) / "mathlib4")
    config["beq"] = dict(config["beq"])
    if os.environ.get("BEQ_PYTHON"):
        config["beq"]["python"] = os.environ["BEQ_PYTHON"]
    elif config["beq"].get("python"):
        config["beq"]["python"] = os.path.abspath(path.parent / config["beq"]["python"])
    else:
        config["beq"]["python"] = sys.executable
    config["beq"]["script"] = str((BASE / config["beq"]["script"]).resolve())
    config["dsh"] = str(Path(config["dsh"]).expanduser())
    config["configs"] = {entry["name"]: entry for entry in config["configs"]}
    return config


def credentials(config):
    """Load the single API credential from the environment."""
    api_key, api_urls = load_api_credentials(error_type=EvaluateError)
    host = api_urls[0]
    api_base = host if host.startswith("http") else f"https://{host}"
    return {
        "api_key": api_key,
        "api_url": api_urls[0],
        "api_base": api_base,
    }


def task_brief(task):
    """Return the immutable task brief handed to the model."""
    return (BASE / "prompts" / f"{task}.md").read_text(encoding="utf-8")


def turn_prompt(task, workspace, attempt):
    """Compose the prompt of one turn: the brief first, then a nudge for later attempts."""
    brief = task_brief(task)
    if attempt == 0:
        return (
            f"The workspace is {workspace}. Its brief is also stored as TASK.md.\n\n"
            f"{brief}\n"
            "Work now: read the inputs with your tools and write the deliverable."
        )
    missing = dataset.OUTPUT_FILES[task]
    return (
        f"The deliverable {missing} is still missing or empty in {workspace}. "
        "Continue the same task, finish the remaining work, and write that file now.\n\n"
        f"{brief}"
    )


def turn_sandbox(config, workspace, state_dir):
    """Return the bwrap prefix that hides the dataset and every other cell from a harness turn."""
    return harness_base.sandbox_command(
        [],
        mask=[REPOSITORY_ROOT, config["temp_root"]],
        read_only=[REPOSITORY_ROOT / "utils"],
        writable=[workspace, state_dir],
    )


def run_harness_turn(config, entry, secrets, *, item, task, workspace, state_dir, state, attempt):
    """Run one harness turn for a cell and return the harness result."""
    harness = entry["harness"]
    limits = config["tasks"][task]
    transcript_dir = Path(state_dir) / "transcripts"
    prompt = turn_prompt(task, workspace, attempt)
    timeout = int(limits["timeout_seconds"])
    sandbox = turn_sandbox(config, workspace, state_dir)
    if harness == "claude":
        from harness import claude

        identifier = state.get("session_id") or str(uuid.uuid4())
        return claude.run_turn(
            binary=config["claude"],
            model=entry["model"],
            prompt=prompt,
            workspace=workspace,
            session_id=identifier,
            resume=bool(state.get("session_started")),
            timeout=timeout,
            base_url=secrets["api_url"],
            api_key=secrets["api_key"],
            transcript_dir=transcript_dir,
            sandbox=sandbox,
        )
    if harness == "codex":
        from harness import codex

        return codex.run_turn(
            runtime=config["codex_runtime"],
            binary=config["codex"],
            model=entry["model"],
            prompt=prompt,
            workspace=workspace,
            codex_home=Path(state_dir) / "codex-home",
            session_id=state.get("session_id"),
            resume=bool(state.get("session_started")),
            timeout=timeout,
            transcript_dir=transcript_dir,
            sandbox=sandbox,
        )
    if harness == "dsh":
        from harness import dsh

        identifier = state.get("session_id") or f"session-{uuid.uuid4()}"
        return dsh.run_turn(
            dsh_binary=config["dsh"],
            model=entry["model"],
            prompt=prompt,
            workspace=Path(workspace),
            dsh_home=Path(state_dir) / "dsh-home",
            session_id=identifier,
            resume=bool(state.get("session_started")),
            timeout=timeout,
            base_url=f"{secrets['api_base']}/compatible-mode/v1",
            api_key=secrets["api_key"],
            transcript_dir=transcript_dir,
            sandbox=sandbox,
        )
    raise EvaluateError(f"unknown harness: {harness}")


def grade_cell(config, secrets, item, task, workspace, state_dir):
    """Grade one produced deliverable, except for the batched BEq+ metric."""
    response = dataset.read_output(workspace, task)
    if response is None:
        return {"status": "missing"}
    if task in RUBRIC_TASKS:
        started = time.monotonic()
        result = rubric.score(
            judge=config["judge"],
            base_url=secrets["api_base"],
            api_key=secrets["api_key"],
            task=task,
            item=item,
            response=response,
            weights=config["weights"],
        )
        usage = result.pop("usage")
        session.record_usage(
            state_dir,
            {
                "phase": "judge",
                "model": config["judge"]["model"],
                "usage": usage,
                "cost_cny": session.cost_of(usage, config["judge"].get("pricing")),
                "duration_seconds": round(time.monotonic() - started, 3),
                "finished_at": session.now(),
                "status": "completed" if result["status"] == "scored" else result["status"],
            },
        )
        return result
    if task == "ft2fp":
        return strict.verify(config, item, response, Path(workspace).parent / "verify")
    return {"status": "pending_batch"}


def export_cell_result(config, state, state_dir, workspace=None):
    """Mirror one produced cell under results/<config>/<paper_id>/<task>/ for external use."""
    workspace = Path(workspace) if workspace is not None else session.cell_dirs(
        config, state["config"], state["item"], state["task"]
    )[1]
    source = dataset.output_path(workspace, state["task"])
    if not source.is_file():
        return False
    overall = config.get("overall_name", "default")
    target_dir = Path(config["results_root"]) / overall / state["config"] / state["item"] / state["task"]
    target = target_dir / dataset.OUTPUT_FILES[state["task"]]
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, target)
    (target_dir / "state.json").write_text(json.dumps(state, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    usage = Path(state_dir) / "usage.jsonl"
    if usage.is_file():
        shutil.copyfile(usage, target_dir / "usage.jsonl")
    grade = state.get("grade")
    if grade:
        (target_dir / "grade.json").write_text(json.dumps(grade, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return True


def run_cell(config, entry, secrets, item, task, *, grade=True, retry=False):
    """Drive one cell to a deliverable, resuming its session, and grade it when possible."""
    state_dir, workspace = session.cell_dirs(config, entry["name"], item["id"], task)
    workspace.mkdir(parents=True, exist_ok=True)
    fingerprint = dataset.prepare_workspace(
        config, item, task, workspace, instructions=task_brief(task)
    )
    state = session.ensure_state(
        state_dir,
        config_name=entry["name"],
        item_id=item["id"],
        task=task,
        input_fingerprint=fingerprint,
    )
    if state.get("stage") == "graded":
        export_cell_result(config, state, state_dir, workspace)
        return {"cell": state_dir.name, "status": "cached", "state": state}
    if retry and state.get("stage") == "failed":
        state["invocations"] = 0
        state["rotated"] = False
        session.save_state(state_dir, state)
    if not state.get("session_started"):
        dataset.clear_output(workspace)
    produced = dataset.read_output(workspace, task) is not None
    attempts = int(config["tasks"][task]["max_turns"])
    backoff = int(config.get("retry_backoff_seconds", 60))
    endpoint_retries = 0
    max_endpoint_retries = int(config.get("max_endpoint_retries", 5))
    while not produced and int(state.get("invocations", 0)) < attempts:
        attempt = int(state.get("turns", 0))
        state["stage"] = "running"
        session.save_state(state_dir, state)
        started = time.monotonic()
        result = run_harness_turn(
            config,
            entry,
            secrets,
            item=item,
            task=task,
            workspace=workspace,
            state_dir=state_dir,
            state=state,
            attempt=attempt,
        )
        usage = result["usage"]
        session.record_usage(
            state_dir,
            {
                "phase": f"{task}-turn-{attempt}",
                "harness": entry["harness"],
                "model": entry["model"],
                "session_id": result.get("session_id"),
                "invocation_id": result.get("invocation_id"),
                "status": result["status"],
                "exit_code": result.get("exit_code"),
                "usage": usage,
                "cost_cny": session.cost_of(usage, entry.get("pricing")),
                "duration_seconds": round(time.monotonic() - started, 3),
                "finished_at": session.now(),
            },
        )
        state["invocations"] = int(state.get("invocations", 0)) + 1
        state["turns"] = attempt + 1
        if result.get("session_id"):
            state["session_id"] = result["session_id"]
            state["session_started"] = True
        state["last_error"] = None if result["status"] == "completed" else result["status"]
        session.save_state(state_dir, state)
        produced = dataset.read_output(workspace, task) is not None
        if produced:
            break
        ep_err = result.get("endpoint_error")
        if ep_err:
            state["invocations"] = int(state.get("invocations", 0)) - 1
            session.save_state(state_dir, state)
            endpoint_retries += 1
            if endpoint_retries >= max_endpoint_retries:
                break
            time.sleep(backoff * (5 if ep_err == "auth" else 3))
        elif result["status"] != "completed" and not any(usage.values()):
            if not state.get("rotated"):
                state["rotated"] = True
                session.rotate_session(state_dir, state, "zero-token harness failure")
            if int(state.get("invocations", 0)) < attempts:
                time.sleep(backoff)
    state["stage"] = "produced" if produced else "failed"
    session.save_state(state_dir, state)
    if produced:
        export_cell_result(config, state, state_dir, workspace)
    if produced and grade:
        outcome = grade_cell(config, secrets, item, task, workspace, state_dir)
        state["grade"] = outcome
        state["stage"] = "graded" if outcome.get("status") in {"scored", "verified"} else "produced"
        session.save_state(state_dir, state)
        export_cell_result(config, state, state_dir, workspace)
    return {"cell": state_dir.name, "status": state["stage"], "state": state}


def select_items(config, names=None, limit=None):
    """Select dataset items by identifier, or the first `limit` items in published order."""
    items = dataset.load_items(config["dataset_root"])
    if names:
        wanted = set(names)
        items = [item for item in items if item["id"] in wanted]
        missing = wanted - {item["id"] for item in items}
        if missing:
            raise EvaluateError(f"unknown dataset items: {', '.join(sorted(missing))}")
    if limit:
        items = items[: int(limit)]
    return items


def command_run(config, args):
    """Run every requested cell, in parallel across cells but sequentially inside a session."""
    secrets = credentials(config)
    entries = [config["configs"][name] for name in (args.config or sorted(config["configs"]))]
    items = select_items(config, args.items, args.limit)
    tasks = args.task or list(dataset.TASKS)
    per_endpoint = {}
    for entry in entries:
        endpoint = entry.get("endpoint", entry["harness"])
        per_endpoint.setdefault(endpoint, []).append(
            [(entry, item, task) for item in items for task in tasks]
        )
    for endpoint, groups in per_endpoint.items():
        interleaved = []
        queues = [list(reversed(g)) for g in groups]
        while any(queues):
            for queue in queues:
                if queue:
                    interleaved.append(queue.pop())
        per_endpoint[endpoint] = interleaved
    total = sum(len(cs) for cs in per_endpoint.values())
    limits = config.get("endpoint_limits", {})
    pool_sizes = {
        endpoint: max(1, int(limits.get(endpoint, args.workers)))
        for endpoint in per_endpoint
    }
    plan = ", ".join(f"{ep}:{pool_sizes[ep]}x{len(per_endpoint[ep])}" for ep in per_endpoint)
    print(
        f"cells: {total} (configs={len(entries)} items={len(items)} tasks={len(tasks)}) "
        f"workers={sum(pool_sizes.values())} [{plan}]",
        flush=True,
    )
    results = []
    results_lock = threading.Lock()

    def work(cell):
        entry, item, task = cell
        try:
            outcome = run_cell(config, entry, secrets, item, task, grade=not args.no_grade, retry=args.retry)
        except Exception as error:  # one failing cell must not abort the sweep
            outcome = {"cell": f"{entry['name']}/{item['id']}/{task}", "status": "error", "error": f"{type(error).__name__}: {error}"}
        label = f"{entry['name']}/{item['id']}/{task}"
        detail = outcome.get("error") or json.dumps(
            (outcome.get("state") or {}).get("grade") or {}, ensure_ascii=False
        )
        with results_lock:
            print(f"{outcome['status']:>9}  {label}  {detail[:160]}", flush=True)
            results.append(outcome)

    pools = {ep: ThreadPoolExecutor(max_workers=pool_sizes[ep]) for ep in per_endpoint}
    futures = []
    try:
        for endpoint, cells in per_endpoint.items():
            for cell in cells:
                futures.append(pools[endpoint].submit(work, cell))
        for future in futures:
            future.result()
    finally:
        for pool in pools.values():
            pool.shutdown(wait=True)
    failures = [outcome for outcome in results if outcome["status"] in {"error", "failed"}]
    print(f"done: {len(results) - len(failures)}/{len(results)} cells produced", flush=True)
    return 0 if not failures else 1


def _cells(config, config_names=None, tasks=None, item_ids=None):
    """Iterate persisted cells as (config entry name, item id, task, state directory)."""
    root = Path(config["state_root"])
    if not root.is_dir():
        return []
    found = []
    for state_path in sorted(root.glob("*/*/*/state.json")):
        state = json.loads(state_path.read_text(encoding="utf-8"))
        if config_names and state["config"] not in config_names:
            continue
        if tasks and state["task"] not in tasks:
            continue
        if item_ids is not None and state["item"] not in item_ids:
            continue
        found.append((state, state_path.parent))
    return found


def command_grade(config, args):
    """Grade produced deliverables, including the batched BEq+ metric for autoformalization."""
    secrets = credentials(config)
    items = {item["id"]: item for item in dataset.load_items(config["dataset_root"])}
    selected = None
    if args.items or args.limit:
        selected = {item["id"] for item in select_items(config, args.items, args.limit)}
    pending_beq = []
    pending_cells = []
    for state, state_dir in _cells(config, args.config, args.task, selected):
        item = items.get(state["item"])
        if item is None:
            continue
        _, workspace = session.cell_dirs(config, state["config"], state["item"], state["task"])
        if dataset.read_output(workspace, state["task"]) is None:
            continue
        if state.get("stage") == "graded" and not args.regrade:
            continue
        if state["task"] == "nc2ft":
            pending_beq.append((state, state_dir, item, workspace))
            continue
        pending_cells.append((state, state_dir, item, workspace))

    def grade_one(cell):
        state, state_dir, item, workspace = cell
        try:
            outcome = grade_cell(config, secrets, item, state["task"], workspace, state_dir)
        except Exception as error:  # one failing cell must not abort the batch
            outcome = {"status": "error", "reason": f"{type(error).__name__}: {error}"}
        state["grade"] = outcome
        state["stage"] = "graded" if outcome.get("status") in {"scored", "verified"} else "produced"
        session.save_state(state_dir, state)
        export_cell_result(config, state, state_dir, workspace)
        print(
            f"{state['stage']:>7}  {state['config']}/{state['item']}/{state['task']}  "
            f"{json.dumps(outcome, ensure_ascii=False)[:160]}",
            flush=True,
        )
        return state["stage"] == "graded"

    graded = 0
    if pending_cells:
        with ThreadPoolExecutor(max_workers=max(1, int(args.jobs))) as pool:
            graded += sum(1 for done in pool.map(grade_one, pending_cells) if done)
    if pending_beq:
        graded += grade_beq(config, pending_beq, args.workers)
    print(f"graded {graded} cells", flush=True)
    return 0


def grade_beq(config, pending, workers):
    """Grade autoformalization cells in one batched BEq+ run against the reference statements."""
    settings = config["beq"]
    script = Path(settings["script"])
    interpreter = Path(settings["python"])
    if not script.is_file() or not interpreter.is_file():
        raise EvaluateError(f"BEq+ grader is unavailable: {interpreter} {script}")
    work_dir = Path(config["temp_root"]) / "beq"
    work_dir.mkdir(parents=True, exist_ok=True)
    jobs = []
    batched = []
    for entry in pending:
        state, state_dir, item, workspace = entry
        candidate = dataset.read_output(workspace, "nc2ft")
        try:
            parts = dataset.split_candidate(candidate)
        except dataset.DatasetError as error:
            state["grade"] = {
                "status": "verified",
                "verdict": "ill_typed",
                "passed": False,
                "details": str(error),
                "duration_seconds": 0.0,
            }
            state["stage"] = "graded"
            session.save_state(state_dir, state)
            export_cell_result(config, state, state_dir, workspace)
            continue
        batched.append(entry)
        jobs.append(
            {
                "id": f"{state['config']}|{state['item']}",
                "reference_header": item["header"],
                "reference": item["statement"],
                "candidate_header": parts["header"],
                "candidate": parts["statement"],
            }
        )
    graded = len(pending) - len(batched)
    if not jobs:
        return graded
    jobs_path = work_dir / "jobs.json"
    report_path = work_dir / "report.json"
    jobs_path.write_text(json.dumps({"jobs": jobs}, ensure_ascii=False), encoding="utf-8")
    completed = subprocess.run(
        [
            str(interpreter),
            str(script),
            "--jobs",
            str(jobs_path),
            "--report",
            str(report_path),
            "--workers",
            str(workers or settings["workers"]),
            "--timeout-per-proof",
            str(settings["timeout_per_proof"]),
        ],
        cwd=REPOSITORY_ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=int(settings["timeout_seconds"]),
        check=False,
    )
    (work_dir / "beq.log").write_text(completed.stdout or "", encoding="utf-8")
    if not report_path.is_file():
        raise EvaluateError(f"BEq+ grader produced no report (exit {completed.returncode}); see {work_dir / 'beq.log'}")
    report = json.loads(report_path.read_text(encoding="utf-8"))
    verdicts = {result["id"]: result for result in report.get("results", [])}
    for state, state_dir, _item, _workspace in batched:
        result = verdicts.get(f"{state['config']}|{state['item']}")
        if result is None:
            continue
        state["grade"] = {
            "status": "verified",
            "verdict": result["verdict"],
            "passed": result["verdict"] == "equivalent",
            "details": result.get("details", ""),
            "duration_seconds": result.get("duration_seconds"),
        }
        state["stage"] = "graded"
        session.save_state(state_dir, state)
        export_cell_result(config, state, state_dir, _workspace)
        graded += 1
        print(f"graded  {state['config']}/{state['item']}/nc2ft  {result['verdict']}", flush=True)
    return graded


def _selected_items(config, args):
    """Return the item ids the caller scoped to with `--items`/`--limit`, or None for every item."""
    if not args.items and not args.limit:
        return None
    return {item["id"] for item in select_items(config, args.items, args.limit)}


def command_export_results(config, args):
    """Mirror existing produced deliverables into the published results directory."""
    exported = 0
    selected = _selected_items(config, args)
    for state, state_dir in _cells(config, args.config, args.task, selected):
        if state.get("stage") not in {"produced", "graded"}:
            continue
        _, workspace = session.cell_dirs(config, state["config"], state["item"], state["task"])
        if export_cell_result(config, state, state_dir, workspace):
            exported += 1
    print(f"exported {exported} cells to {Path(config['results_root']) / config.get('overall_name', 'default')}", flush=True)
    return 0


def command_status(config, args):
    """Summarize cell progress per configuration and task."""
    rows = {}
    for state, _state_dir in _cells(config, args.config, args.task, _selected_items(config, args)):
        key = (state["config"], state["task"])
        row = rows.setdefault(key, {"cells": 0, "graded": 0, "produced": 0, "failed": 0})
        row["cells"] += 1
        stage = state.get("stage")
        if stage == "graded":
            row["graded"] += 1
        elif stage == "produced":
            row["produced"] += 1
        elif stage in {"failed", "running"}:
            row["failed"] += 1
    for (name, task), row in sorted(rows.items()):
        print(f"{name:24} {task:6} cells={row['cells']:4} graded={row['graded']:4} produced={row['produced']:4} unfinished={row['failed']:4}")
    return 0


def command_usage(config, args):
    """Report token usage and CNY cost per configuration, plus the unpriced remainder."""
    per_config = {}
    for state, state_dir in _cells(config, args.config, args.task, _selected_items(config, args)):
        per_config.setdefault(state["config"], []).append(Path(state_dir) / "usage.jsonl")
    total = None
    for name, paths in sorted(per_config.items()):
        summary = session.summarize_usage(paths)
        total = summary if total is None else {
            key: (summary[key] + total[key]) if isinstance(summary[key], (int, float)) else summary[key]
            for key in summary
        }
        print(
            f"{name:24} calls={summary['calls']:5} in={summary['total_input_tokens']:9} "
            f"out={summary['output_tokens']:8} cost={summary['cost_cny']:.4f} CNY unpriced_calls={summary['unpriced_calls']}"
        )
    if total:
        print(
            f"{'TOTAL':24} calls={total['calls']:5} in={total['total_input_tokens']:9} "
            f"out={total['output_tokens']:8} cost={round(total['cost_cny'], 4):.4f} CNY unpriced_calls={total['unpriced_calls']}"
        )
    return 0


def command_report(config, args):
    """Aggregate graded cells into the published score table."""
    metrics = {"cc2nc": "LLM-Rubric", "nc2ft": "BEq+", "c2np": "LLM-Rubric", "ft2fp": "Pass@1"}
    rows = {}
    details = []
    for state, _state_dir in _cells(config, args.config, args.task, _selected_items(config, args)):
        grade = state.get("grade") or {}
        key = (state["config"], state["task"])
        row = rows.setdefault(key, {"n": 0, "scored": 0, "score_sum": 0.0, "passed": 0})
        row["n"] += 1
        if grade.get("status") == "scored":
            row["scored"] += 1
            row["score_sum"] += float(grade["score"])
        elif grade.get("status") == "verified":
            row["scored"] += 1
            row["passed"] += 1 if grade.get("passed") else 0
        details.append(
            {
                "config": state["config"],
                "item": state["item"],
                "task": state["task"],
                "stage": state.get("stage"),
                "grade": grade,
            }
        )
    summary = []
    for (name, task), row in sorted(rows.items()):
        value = None
        if row["scored"]:
            value = round(row["score_sum"] / row["scored"], 4) if task in RUBRIC_TASKS else round(row["passed"] / row["scored"], 4)
        summary.append(
            {
                "config": name,
                "task": task,
                "metric": metrics[task],
                "cells": row["n"],
                "graded": row["scored"],
                "score": value,
            }
        )
        print(f"{name:24} {task:6} {metrics[task]:11} graded={row['scored']:4}/{row['n']:<4} score={value}")
    results_root = Path(config["results_root"]) / config.get("overall_name", "default")
    results_root.mkdir(parents=True, exist_ok=True)
    payload = {"schema_version": "1.0", "generated_at": session.now(), "summary": summary, "cells": details}
    (results_root / "scores.json").write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {results_root / 'scores.json'}")
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--config-file", type=Path)
    subparsers = parser.add_subparsers(dest="command", required=True)

    def add_selection(target):
        target.add_argument("--config", action="append", help="configuration name (repeatable)")
        target.add_argument("--task", action="append", choices=list(dataset.TASKS), help="task (repeatable)")
        target.add_argument("--items", action="append", help="dataset item id (repeatable)")
        target.add_argument("--limit", type=int, help="use only the first N items")

    run_parser = subparsers.add_parser("run", help="run harness sessions and grade what can be graded")
    add_selection(run_parser)
    run_parser.add_argument("--workers", type=int, default=8)
    run_parser.add_argument("--no-grade", action="store_true", help="produce deliverables without grading")
    run_parser.add_argument("--retry", action="store_true", help="give failed cells a fresh attempt budget")
    run_parser.set_defaults(handler=command_run)

    grade_parser = subparsers.add_parser("grade", help="grade produced deliverables")
    add_selection(grade_parser)
    grade_parser.add_argument("--workers", type=int, default=0, help="BEq+ workers (0 uses the config default)")
    grade_parser.add_argument("--jobs", type=int, default=8, help="rubric and strict cells graded in parallel")
    grade_parser.add_argument("--regrade", action="store_true")
    grade_parser.set_defaults(handler=command_grade)

    export_parser = subparsers.add_parser("export-results", help=command_export_results.__doc__.splitlines()[0].lower())
    add_selection(export_parser)
    export_parser.set_defaults(handler=command_export_results)

    for name, handler in (("status", command_status), ("usage", command_usage), ("report", command_report)):
        target = subparsers.add_parser(name, help=handler.__doc__.splitlines()[0].lower())
        add_selection(target)
        target.set_defaults(handler=handler)

    args = parser.parse_args()
    try:
        config = load_config(args.config_file)
    except EvaluateError as error:
        parser.error(str(error))
    if getattr(args, "config", None):
        unknown = [name for name in args.config if name not in config["configs"]]
        if unknown:
            parser.error(f"unknown configuration(s): {', '.join(unknown)}")
    try:
        return args.handler(config, args)
    except EvaluateError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())

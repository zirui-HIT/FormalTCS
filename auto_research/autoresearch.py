"""Drive the AutoResearch pipeline: agent-loop generation, then theorem proving.

Usage:
    python3 auto_research/autoresearch.py run --runs 1 [--stage all|generation|proof]
    python3 auto_research/autoresearch.py run --resume R0001
    python3 auto_research/autoresearch.py status
    python3 auto_research/autoresearch.py usage
    python3 auto_research/autoresearch.py report

Runs execute in parallel (bounded by the codex endpoint limit), each run driving its three
agents sequentially; proof cells then run in parallel the same way.
"""

import argparse
import json
import random
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

BASE = Path(__file__).resolve().parent
if str(BASE) not in sys.path:
    sys.path.insert(0, str(BASE))

import generation  # noqa: E402
import proof  # noqa: E402
import runtime  # noqa: E402
import workspace as ws  # noqa: E402


def _run_states(config):
    root = Path(config["state_root"]) / "runs"
    if not root.is_dir():
        return []
    states = []
    for path in sorted(root.glob("*/state.json")):
        states.append(json.loads(path.read_text(encoding="utf-8")))
    return states


def _proof_states(config):
    root = Path(config["state_root"]) / "proofs"
    if not root.is_dir():
        return []
    states = []
    for path in sorted(root.glob("*/state.json")):
        states.append(json.loads(path.read_text(encoding="utf-8")))
    return states


def _next_run_id(config, taken=()):
    """Return the next free run id, also honoring ids assigned but not yet on disk."""
    root = Path(config["state_root"]) / "runs"
    existing = {path.name for path in root.glob("R*")} if root.is_dir() else set()
    existing |= set(taken)
    number = 1
    while f"R{number:04d}" in existing:
        number += 1
    return f"R{number:04d}"


def _pending_proof_claims(config, only=None, retry=False, regrade=False):
    claims = ws.read_claims(config)
    if only:
        wanted = set(only)
        claims = [claim for claim in claims if claim["claim_id"] in wanted]
    pending = []
    for claim in claims:
        state = runtime.load_state(
            Path(config["state_root"]) / "proofs" / runtime.safe_name(claim["claim_id"])
        )
        if state and state.get("stage") == "graded" and not regrade:
            continue
        if state and state.get("stage") == "failed" and not retry:
            continue
        pending.append(claim)
    return pending


def command_run(config, args):
    """Run generation runs and then the proof cells of accepted claims."""
    accepted = []
    if args.stage in {"generation", "all"}:
        pairs = [(run_id, None) for run_id in (args.resume or [])]
        taken = set()
        for offset in range(max(0, args.runs)):
            run_id = _next_run_id(config, taken)
            taken.add(run_id)
            seed = args.seed + offset if args.seed is not None else random.randrange(2**31)
            pairs.append((run_id, seed))
        print(f"generation runs: {len(pairs)} workers={args.workers}", flush=True)

        def generate(pair):
            run_id, seed = pair
            if seed is None and runtime.load_state(
                Path(config["state_root"]) / "runs" / runtime.safe_name(run_id)
            ) is None:
                return run_id, None, f"run {run_id} has no state to resume"
            try:
                state, accepted_claims = generation.run_generation(config, run_id, seed)
            except Exception as error:  # one failing run must not abort the sweep
                return run_id, None, f"{type(error).__name__}: {error}"
            return run_id, accepted_claims, None

        with ThreadPoolExecutor(max_workers=max(1, args.workers)) as pool:
            for run_id, accepted_claims, error in pool.map(generate, pairs):
                if error:
                    print(f"  failed  {run_id}  {error[:200]}", flush=True)
                    continue
                accepted.extend(accepted_claims)
                stage = "accepted" if accepted_claims else "exhausted"
                print(f"  {stage:>9}  {run_id}  claims={[c['claim_id'] for c in accepted_claims]}", flush=True)
    if args.stage in {"proof", "all"}:
        claims = _pending_proof_claims(config, args.claim, args.retry, args.regrade)
        print(f"proof cells: {len(claims)} workers={args.workers}", flush=True)

        def prove(claim):
            try:
                state = proof.run_proof(config, claim, retry=args.retry, regrade=args.regrade)
            except Exception as error:  # one failing cell must not abort the sweep
                return claim["claim_id"], f"{type(error).__name__}: {error}"
            grade = state.get("grade") or {}
            detail = (
                f"passed={grade.get('passed')}"
                if grade
                else f"stage={state.get('stage')} {state.get('last_error') or ''}"
            )
            return claim["claim_id"], detail

        with ThreadPoolExecutor(max_workers=max(1, args.workers)) as pool:
            for claim_id, detail in pool.map(prove, claims):
                print(f"  proof  {claim_id}  {detail[:200]}", flush=True)
    return 0


def command_status(config, args):
    """Summarize run and proof-cell progress."""
    for state in _run_states(config):
        claims = state.get("claims", [])
        accepted = [claim["claim_id"] for claim in claims if claim.get("stage") == "accepted"]
        discarded = sum(1 for claim in claims if claim.get("stage") == "discarded")
        print(
            f"{state['run_id']:>8}  {state.get('stage', '?'):>11}  claims={len(claims)} "
            f"accepted={len(accepted)} discarded={discarded}  {','.join(accepted)}"
        )
    for state in _proof_states(config):
        grade = state.get("grade") or {}
        detail = f"passed={grade.get('passed')}" if grade else ""
        print(
            f"{state['claim_id']:>16}  {state.get('stage', '?'):>9}  {detail}  "
            f"{(grade.get('reason') or '')[:100]}"
        )
    return 0


def command_usage(config, args):
    """Report token usage and CNY cost per run and proof cell, plus the total."""
    groups = []
    for state in _run_states(config):
        groups.append(
            (
                f"run {state['run_id']}",
                [Path(config["state_root"]) / "runs" / runtime.safe_name(state["run_id"]) / "usage.jsonl"],
            )
        )
    for state in _proof_states(config):
        groups.append(
            (
                f"proof {state['claim_id']}",
                [Path(config["state_root"]) / "proofs" / runtime.safe_name(state["claim_id"]) / "usage.jsonl"],
            )
        )
    total = None
    for name, paths in groups:
        summary = runtime.usage_totals(paths)
        if not summary["calls"]:
            continue
        total = summary if total is None else {key: summary[key] + total[key] for key in summary}
        print(
            f"{name:>28}  calls={summary['calls']:3} in={summary['total_input_tokens']:9} "
            f"out={summary['output_tokens']:8} cost={summary['cost_cny']:.4f} CNY"
        )
    if total:
        print(
            f"{'TOTAL':>28}  calls={total['calls']:3} in={total['total_input_tokens']:9} "
            f"out={total['output_tokens']:8} cost={round(total['cost_cny'], 4):.4f} CNY"
        )
    return 0


def command_report(config, args):
    """Aggregate runs, claims, proofs, and usage into results/report.json."""
    results_root = Path(config["results_root"])
    results_root.mkdir(parents=True, exist_ok=True)
    claims = ws.read_claims(config)
    proof_states = _proof_states(config)
    payload = {
        "schema_version": "1.0",
        "generated_at": runtime.now(),
        "runs": [
            {
                "run_id": state["run_id"],
                "seed": state.get("seed"),
                "stage": state.get("stage"),
                "sampled": state.get("sampled", []),
                "claims": [
                    {
                        "claim_id": claim["claim_id"],
                        "stage": claim.get("stage"),
                        "rounds": claim.get("rounds"),
                        "failure": claim.get("failure"),
                        "verdict": claim.get("verdict"),
                    }
                    for claim in state.get("claims", [])
                ],
            }
            for state in _run_states(config)
        ],
        "claims": claims,
        "proofs": [
            {
                "claim_id": state["claim_id"],
                "stage": state.get("stage"),
                "passed": (state.get("grade") or {}).get("passed"),
                "reason": (state.get("grade") or {}).get("reason"),
            }
            for state in proof_states
        ],
        "usage": runtime.usage_totals(
            [
                path
                for path in [
                    *[
                        Path(config["state_root"]) / "runs" / runtime.safe_name(state["run_id"]) / "usage.jsonl"
                        for state in _run_states(config)
                    ],
                    *[
                        Path(config["state_root"]) / "proofs" / runtime.safe_name(state["claim_id"]) / "usage.jsonl"
                        for state in proof_states
                    ],
                ]
                if path.is_file()
            ]
        ),
    }
    report = results_root / "report.json"
    report.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    passed = sum(1 for entry in payload["proofs"] if entry["passed"])
    print(
        f"runs={len(payload['runs'])} accepted_claims={len(claims)} "
        f"proofs={len(payload['proofs'])} passed={passed}"
    )
    print(f"cost={payload['usage']['cost_cny']:.4f} CNY calls={payload['usage']['calls']}")
    print(f"wrote {report}")
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--config-file", type=Path)
    subparsers = parser.add_subparsers(dest="command", required=True)

    run_parser = subparsers.add_parser("run", help="run generation runs and proof cells")
    run_parser.add_argument("--runs", type=int, default=1, help="number of new generation runs")
    run_parser.add_argument("--resume", action="append", help="run id to resume (repeatable)")
    run_parser.add_argument("--seed", type=int, help="benchmark sampling seed for new runs")
    run_parser.add_argument(
        "--stage", choices=("generation", "proof", "all"), default="all", help="pipeline stages to run"
    )
    run_parser.add_argument("--workers", type=int, default=4, help="parallel runs or proof cells")
    run_parser.add_argument("--claim", action="append", help="claim id to prove (repeatable)")
    run_parser.add_argument("--retry", action="store_true", help="retry failed proof cells")
    run_parser.add_argument(
        "--regrade", action="store_true", help="re-verify the existing proof deliverable of graded cells"
    )
    run_parser.set_defaults(handler=command_run)

    for name, handler in (
        ("status", command_status),
        ("usage", command_usage),
        ("report", command_report),
    ):
        target = subparsers.add_parser(name, help=handler.__doc__.splitlines()[0].lower())
        target.set_defaults(handler=handler)

    args = parser.parse_args()
    try:
        config = runtime.load_config(args.config_file)
    except runtime.TurnError as error:
        parser.error(str(error))
    return args.handler(config, args)


if __name__ == "__main__":
    raise SystemExit(main())

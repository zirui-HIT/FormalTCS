# Benchmark

A Lean 4 benchmark of 175 core theorems from theoretical computer science papers, together with
the harness that evaluates frontier models on it and the agent loop that lets a model explore
new theorems on top of it. Every item pairs a natural-language claim and proof with a verified
Lean 4 formalization built against Mathlib.

## Layout

```text
benchmark/                     # the published dataset
├── collection.json            # 100 proof items (reference Lean proof available)
├── statements.json            # 75 statement items (formal statement, no reference proof)
├── theorems/<paper_id>/       # one standalone Lake project per item: theorem.lean (the
│                              # statement proved `by sorry`) + lakefile/manifest/toolchain
└── proofs/<paper_id>/         # one completed reference Lean project per proof item
evaluate/                      # evaluation harness for the four benchmark tasks
auto_research/                 # planner → formalizer → judger agent loop + theorem proving
utils/                         # shared runtime: credentials, usage accounting, Codex proxy,
                               # and the strict Lean verifier (utils/leanmarathon/)
```

## Tasks

| Task                        | Input                | Output     | Metric     |
| --------------------------- | -------------------- | ---------- | ---------- |
| Theorem Elicitation (CC2NC) | Core Claim           | NL Claim   | LLM-Rubric |
| Autoformalization (NC2FT)   | NL Claim             | FL Theorem | BEq+       |
| Proof Elicitation (C2NP)    | NL Claim, FL Theorem | NL Proof   | LLM-Rubric |
| Theorem Proving (FT2FP)     | FL Theorem           | FL Proof   | Pass@1     |

Models and harnesses are paired in `evaluate/config/default.json` (`configs`): Codex, Claude
Code, and `dsh` each drive the models they can serve. Inputs and deliverables are exchanged as
files inside a per-cell workspace (`input/`, `output/`, and for Lean tasks a ready-to-build Lake
project plus `check.sh`), so the model reads and writes with its own tools.

## Requirements

* Python ≥ 3.10 (stdlib only, except `lean-interact` for the BEq+ grader: `pip install lean-interact`)
* [elan](https://github.com/leanprover/elan) with toolchain `leanprover/lean4:v4.32.2`
* `bwrap` (bubblewrap) for harness sandboxing, `git` for the one-time REPL clone
* The CLI of every harness you run: `codex`, `claude`, or `dsh`

### Lean environment

Every project shares one prebuilt Mathlib, pinned in all 175 `lake-manifest.json` files:

```bash
elan default leanprover/lean4:v4.32.2
export LEAN_ROOT="$(dirname "$(elan which lean)")/.."   # prefix containing bin/lean, bin/lake
git clone https://github.com/leanprover-community/mathlib4 "$LEAN_ROOT/mathlib4"
cd "$LEAN_ROOT/mathlib4" && git checkout 905b95818eb32af7874a58b427f50c1711a5e96c
lake exe cache get                                     # downloads the prebuilt artifacts
```

No project ever downloads or rebuilds Mathlib: workspaces symlink `$MATHLIB_ROOT` in, and the
BEq+ grader reuses it through a generated facade package.

## Environment variables

| Variable       | Required for            | Meaning                                                              |
| -------------- | ----------------------- | -------------------------------------------------------------------- |
| `LEAN_ROOT`    | all Lean tasks/grading  | Lean toolchain prefix (`bin/lean`, `bin/lake`), with `mathlib4/`     |
| `MATHLIB_ROOT` | no (default `$LEAN_ROOT/mathlib4`) | prebuilt Mathlib checkout                     |
| `API_KEY`      | every run/grade command | API key of the OpenAI-compatible endpoint                            |
| `API_URL`      | every run/grade command | endpoint URL (multiple endpoints: comma-separated)                   |
| `CLAUDE_BIN`   | no (default `claude`)   | Claude Code CLI executable                                           |
| `CODEX_BIN`    | no (default `codex`)    | Codex CLI executable                                                 |
| `DSH_BIN`      | no (default `dsh`)      | dsh CLI executable                                                   |
| `BEQ_PYTHON`   | no (default `sys.executable`) | interpreter with `lean-interact` installed for BEq+ grading   |

## evaluate/

```bash
python3 evaluate/evaluate.py run --config claude-opus-5 --task cc2nc --limit 4
python3 evaluate/evaluate.py run --workers 16        # every configuration and task
python3 evaluate/evaluate.py grade --task nc2ft      # batched BEq+ grading
python3 evaluate/evaluate.py status                  # cell progress per config/task
python3 evaluate/evaluate.py usage                   # token usage and CNY cost
python3 evaluate/evaluate.py report                  # writes evaluate/results/collection/scores.json
python3 evaluate/evaluate.py export-results          # mirror deliverables into results/
```

Parameters: `--config-file` (alternative JSON config), `--config`, `--task`, `--items`, `--limit`
(all repeatable and combinable), `run --workers/--no-grade/--retry`, `grade --workers/--jobs/
--regrade`. One (configuration, item, task) cell owns one resumable harness session; state lives
in `evaluate/.cache/work/`, workspaces under `/tmp/evaluate/`, published results in
`evaluate/results/`. An interrupted sweep resumes where it stopped; `--retry` gives failed cells
a fresh attempt budget.

Operational knobs in `evaluate/config/default.json`: `lean_jobs` (parallel Lean workers per
compile), per-task `timeout_seconds`/`max_turns`, `endpoint_limits` (concurrent turns per
endpoint), `judge` (rubric model, retries, pricing), `beq` (workers, per-proof and batch
timeouts), and the `configs` matrix (harness, model, pricing per evaluated system).

Grading: LLM-Rubric scores each response once on logic/complete/correct/clear weighted
0.4/0.3/0.2/0.1; BEq+ proves the candidate statement equivalent to the reference inside one Lean
command (first use clones and builds the REPL into `evaluate/.env/`, then reuses it); FT2FP
rejects any file that alters the reference statement or contains a proof bypass, then runs a
strict compilation, an environment-level axiom audit, and a fresh kernel replay.

## auto_research/

Agent-Loop Generation runs three agents — planner (proposes a research objective), formalizer
(compiles the Lean statement against the benchmark's Lake setup, at most three compiler-feedback
rounds), judger (translates back to a natural-language claim and filters for novelty) — in a
shared workspace seeded with 16 sampled benchmark instances. Accepted claims are published to
`auto_research/results/` and then proved like FT2FP. All agents use the Codex harness.

```bash
python3 auto_research/autoresearch.py run --runs 4 --workers 4   # generation, then proofs
python3 auto_research/autoresearch.py run --resume R0001         # resume one run
python3 auto_research/autoresearch.py run --stage proof --retry  # only failed proof cells
python3 auto_research/autoresearch.py status | usage | report
```

Parameters: `--config-file`, `--runs`, `--resume`, `--seed` (benchmark sampling), `--stage
all|generation|proof`, `--workers`, `--claim` (prove specific claims), `--retry`, `--regrade`.
Knobs in `auto_research/config.json`: `model`, `generation` (`sample_size`, `max_claims`,
`stop_on_accept`, per-agent timeouts), `proof` (`timeout_seconds`, `max_turns`),
`endpoint_limits`. State lives in `auto_research/.cache/`, workspaces under
`/tmp/auto_research/`, published claims/theorems/proofs in `auto_research/results/`.

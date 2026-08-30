# FormalTCS: Benchmarking End-to-End Frontier Formal Theoretical Computer Science Research of Large Language Models

This repository contains a Lean 4 benchmark built from **143 core theorems from theoretical computer science papers**. Each benchmark item includes a natural-language statement and proof together with a verified Lean 4 formalization against Mathlib.

The repository also contains:

* the evaluation harness used for the four benchmark tasks;
* reference Lean projects for checking and grading model outputs; and
* an `auto_research` pipeline for proposing, formalizing, and proving new claims starting from examples in the benchmark.

## Repository structure

```text
benchmark/
├── collection.json            # all 143 benchmark items
├── theorems/<paper_id>/       # theorem statement, with the proof replaced by `sorry`
└── proofs/<paper_id>/         # completed reference Lean project

evaluate/                      # benchmark evaluation harness
auto_research/                 # theorem generation + proving pipeline
utils/                         # shared runtime and Lean verification utilities
```

Each directory under `benchmark/theorems/` is a standalone Lake project. The corresponding directory under `benchmark/proofs/` contains the verified reference proof.

## Benchmark tasks

We evaluate four directions between informal and formal mathematics:

| Task                | ID      | Given                                 | Predict                | Metric     |
| ------------------- | ------- | ------------------------------------- | ---------------------- | ---------- |
| Theorem Elicitation | `cc2nc` | core claim                            | natural-language claim | LLM rubric |
| Autoformalization   | `nc2ft` | natural-language claim                | Lean theorem statement | BEq+       |
| Proof Elicitation   | `c2np`  | natural-language claim + Lean theorem | natural-language proof | LLM rubric |
| Theorem Proving     | `ft2fp` | Lean theorem                          | Lean proof             | Pass@1     |

The evaluation harness currently supports Codex, Claude Code, and `dsh`. Model/harness combinations are defined in [`evaluate/config/default.json`](evaluate/config/default.json).

For every evaluation cell, the model works in an isolated file-based workspace. Inputs are written to `input/`, answers are expected in `output/`, and Lean tasks additionally receive a ready-to-build Lake project and a `check.sh` script.

## Setup

### Requirements

The evaluation code expects:

* Python 3.10 or newer;
* [`elan`](https://github.com/leanprover/elan);
* Lean `v4.32.2`;
* `bwrap` (bubblewrap);
* `git`;
* the CLI for each harness you intend to run: `codex`, `claude`, and/or `dsh`.

Most of the Python code uses only the standard library. Autoformalization grading additionally requires [`lean-interact`](https://pypi.org/project/lean-interact/):

```bash
pip install lean-interact
```

### Lean and Mathlib

All 143 projects use the same Lean toolchain and Mathlib revision. Set them up once:

```bash
elan default leanprover/lean4:v4.32.2

export LEAN_ROOT="$(dirname "$(elan which lean)")/.."

git clone https://github.com/leanprover-community/mathlib4 "$LEAN_ROOT/mathlib4"
cd "$LEAN_ROOT/mathlib4"
git checkout 905b95818eb32af7874a58b427f50c1711a5e96c
lake exe cache get

export MATHLIB_ROOT="$LEAN_ROOT/mathlib4"
```

`MATHLIB_ROOT` is optional; if unset, it defaults to `$LEAN_ROOT/mathlib4`.

The benchmark projects do not fetch or rebuild Mathlib during evaluation. Their manifests are pinned to the revision above, and evaluation workspaces reuse the prebuilt checkout.

### API endpoints

The harnesses use an OpenAI-compatible endpoint:

```bash
export API_KEY=...
export API_URL=...
```

`API_URL` may contain multiple comma-separated endpoints. The evaluator distributes requests according to the concurrency limits in the configuration file.

The harness executable names can also be overridden:

```bash
export CODEX_BIN=codex
export CLAUDE_BIN=claude
export DSH_BIN=dsh
```

For BEq+ grading, `BEQ_PYTHON` can be used to select a Python interpreter with `lean-interact` installed.

## Running the benchmark

A small run is usually the easiest way to check that the environment is working:

```bash
python3 evaluate/evaluate.py run \
    --config claude-opus-5 \
    --task cc2nc \
    --limit 4
```

To run the full configuration matrix:

```bash
python3 evaluate/evaluate.py run --workers 16
```

Runs are resumable. Progress is stored under `evaluate/.cache/work/`, so re-running the same command continues unfinished cells rather than starting from scratch.

Useful commands:

```bash
# Show progress by model/task
python3 evaluate/evaluate.py status

# Grade autoformalization outputs
python3 evaluate/evaluate.py grade --task nc2ft

# Show token usage and estimated CNY cost
python3 evaluate/evaluate.py usage

# Aggregate scores
python3 evaluate/evaluate.py report

# Copy model deliverables into results/
python3 evaluate/evaluate.py export-results
```

Published evaluation outputs live under `evaluate/results/`. Temporary model workspaces are created under `/tmp/evaluate/`.

### Selecting runs

`--config`, `--task`, `--items`, and `--limit` may be combined and repeated to select a subset of the benchmark. An alternative configuration file can be supplied with `--config-file`.

For execution, the main additional options are:

```text
run:
  --workers
  --no-grade
  --retry

grade:
  --workers
  --jobs
  --regrade
```

`--retry` gives previously failed cells a fresh attempt budget while leaving completed cells untouched.

Most runtime settings are kept in `evaluate/config/default.json`, including:

* per-task timeouts and turn limits;
* parallel Lean jobs;
* per-endpoint concurrency limits;
* rubric-judge model and pricing;
* BEq+ worker and timeout settings; and
* the model/harness configuration matrix.

## Grading

The four tasks use three different grading paths.

### Natural-language tasks

`cc2nc` and `c2np` are graded by an LLM rubric. Each answer is scored once for:

```text
logic         0.4
completeness  0.3
correctness   0.2
clarity       0.1
```

The judge model and retry settings are configured under `judge` in `evaluate/config/default.json`.

### Autoformalization

`nc2ft` uses **BEq+** rather than string matching.

The grader asks Lean to establish equivalence between the candidate theorem and the reference theorem inside a generated facade project. On first use it clones and builds the Lean REPL under `evaluate/.env/`; subsequent grading runs reuse the same environment and Mathlib checkout.

### Theorem proving

`ft2fp` is accepted only if the submitted proof passes the strict Lean verifier.

Before compilation, the verifier checks that the reference theorem statement has not been modified and rejects known proof bypasses. Successful candidates then go through:

1. strict compilation;
2. an environment-level axiom audit; and
3. a fresh kernel replay.

The reported metric is Pass@1.

## `auto_research`

`auto_research` uses the benchmark as context for generating new formal research claims.

A generation run has three agents:

1. **planner** — proposes a research objective;
2. **formalizer** — turns it into a Lean statement and fixes compiler errors, for up to three feedback rounds;
3. **judger** — translates the formal statement back to natural language and filters candidates for novelty.

By default, the shared workspace is seeded with 16 sampled benchmark examples. Accepted claims are written to `auto_research/results/` and then sent through a theorem-proving stage using the same style of strict Lean verification as `ft2fp`.

All three agents currently use the Codex harness.

Run generation and proving together with:

```bash
python3 auto_research/autoresearch.py run --runs 4 --workers 4
```

Other common workflows:

```bash
# Resume a particular research run
python3 auto_research/autoresearch.py run --resume R0001

# Retry only failed theorem-proving cells
python3 auto_research/autoresearch.py run --stage proof --retry

# Inspect progress and usage
python3 auto_research/autoresearch.py status
python3 auto_research/autoresearch.py usage
python3 auto_research/autoresearch.py report
```

The run command also supports `--config-file`, `--seed`, `--stage`, `--claim`, and `--regrade`.

Generation and proof settings are in `auto_research/config.json`. The main knobs are the model, benchmark sample size, maximum number of generated claims, agent timeouts, proof timeout/turn limits, and endpoint concurrency.

Persistent state is stored in `auto_research/.cache/`; temporary workspaces are created under `/tmp/auto_research/`.

## Reproducibility

The benchmark is intentionally pinned at the Lean and Mathlib level:

```text
Lean     leanprover/lean4:v4.32.2
Mathlib  905b95818eb32af7874a58b427f50c1711a5e96c
```

Each benchmark theorem has its own Lake project and manifest, while the evaluator reuses a single prebuilt Mathlib checkout. This keeps individual evaluation cells lightweight and avoids dependency changes between runs.

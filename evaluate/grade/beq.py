#!/usr/bin/env python3
"""BEq+ grader for the Autoformalization (NC2FT) task of the benchmark.

The metric is a port of `BEq+` (with the `BEqL` fast path it uses internally) from

```bibtex
@inproceedings{poiroux-etal-2025-reliable,
    title = "Reliable Evaluation and Benchmarks for Statement Autoformalization",
    author = "Poiroux, Auguste and Weiss, Gail and Kun{\v{c}}ak, Viktor and Bosselut, Antoine",
    booktitle = "Proceedings of the 2025 Conference on Empirical Methods in Natural Language Processing",
    year = "2025", url = "https://aclanthology.org/2025.emnlp-main.907/",
}
```

The reference BEq+ implementation is followed step by step:
both proof directions, the `sorry` well-typedness precheck, the `exact?` (BEqL) fast path,
the `assumption` false-positive guard, `apply` + solver tactics, the `have`-conclusion
strategy with its provable-without-`have` sanity check, and the `convert ... using k`
ladder for `k = 0..4`. Two further strategies (5 and 6, see "Definitional relaxations"
below) are appended, because NC2FT hands the model only the reference `import` lines: the
model has to invent its own `def`s, and two extensionally equal but not definitionally equal
encodings of the same recursion would otherwise fail every strategy of the ladder.

Usage:
    python3 evaluate/grade/beq.py \
        --jobs /tmp/x/jobs.json --report /tmp/x/report.json [--workers 4] [--timeout-per-proof 60]

`jobs.json`: `{"jobs": [{"id", "reference_header", "reference", "candidate_header",
"candidate"}, ...]}`. NC2FT hands the model only the reference `import` lines, so each side
is a self-contained Lean file: its own preamble (imports, `open`/`set_option`/`variable`
lines and bespoke `def`/`abbrev`/`structure` declarations) plus exactly one bare theorem
ending in `:=`. The two preambles are independent and routinely declare colliding names.
`report.json`: `{"schema_version": "1.0", "results": [{"id", "verdict", "details",
"duration_seconds"}, ...]}` with one result per job, in input order. Verdicts are
`equivalent`, `not_proven`, `ill_typed` (candidate unparsable or not well typed) and
`error` (infrastructure failure, broken reference side, or job-budget timeout). The script
never raises for a single bad job and exits 0 whenever the report was written.

Assembly of the two preambles into one Lean command:
* Every `import` line of both preambles is hoisted to the top of the command, deduplicated by
  the module it names, and followed by the `TACTIC_IMPORTS` the metric needs. Lean requires
  imports first, so a preamble whose imports are not at the top is repaired by the hoisting. The
  Lean module system is supported: `public import ...` lines count as imports and a leading lone
  `module` line is hoisted in front of them.
* The rest of each preamble plus its theorem is wrapped in `namespace BEqRef ... end BEqRef`
  respectively `namespace BEqCand ... end BEqCand`, so colliding declaration names cannot
  clash and each statement elaborates against its own definitions. `open`, `set_option` and
  `variable` lines stay scoped to their side. A preamble may itself open namespaces (balanced
  `namespace X ... end X` blocks simply nest; scopes left open by the preamble, as produced by
  the dataset splitter, are closed again right before `end BEqRef`/`end BEqCand`, and they
  extend the prefix of the theorem name).
* The longest verbatim common prefix of the two preambles is hoisted in front of both wrapper
  namespaces and elaborated once. `structure`, `inductive` and `class` declarations are
  generative: declaring the same one in both namespaces yields two distinct, non-convertible
  types, so without this sharing even a verbatim copy of the reference could not be proven
  equivalent. A candidate that re-implements such a type under its own name (or with any textual
  difference before it) therefore stays `not_proven`, whatever it means; only `def`/`abbrev`
  declarations survive being duplicated, because `apply` and `convert` unfold them.
* The base theorem is declared with a `sorry` body on its own side and is used from the other
  side under its fully qualified name (`_root_.BEqRef.base_theorem`, plus the namespaces the
  preamble left open). The reformulated theorem is always the last declaration of the command,
  and its side's namespaces are deliberately left open so the proof can be appended.
* Messages are attributed by line: `formal_2_start_line` is the line of the reformulated
  theorem, hence errors and `declaration uses 'sorry'` warnings of the injected side, of the
  hoisted imports and of both preambles are ignored, exactly as before.

Definitional relaxations (strategies 5 and 6, added on top of the reference ladder):
* Declaration harvesting: `declaration_names` walks each preamble, tracks the `namespace`
  stack and collects every `def`/`abbrev` it introduces (any combination of `noncomputable`,
  `unsafe`, `partial`, `protected`, ... is accepted, `private` ones are skipped) as a
  `_root_.`-qualified name. Two name sets are kept per side: `names`, valid inside the
  assembled two-sided command (`_root_.BEqRef.foo`, including the shared hoisted prefix), and
  `solo_names`, valid when that side is elaborated alone. Only `def`/`abbrev` are harvested;
  `structure`/`inductive`/`class` are generative and handled by the shared-prefix hoisting.
* Strategy 5 (definitional solver): `apply <base_theorem>` followed by the solver tactic set
  in which `simp_all! +arith +decide` is given the harvested names as a simp set
  (`simp_all! +arith +decide [_root_.BEqRef.foo, _root_.BEqCand.foo, ...]`). This closes gaps
  that are pure unfolding, e.g. an `abbrev` on one side and a `def` on the other, or a
  helper that is inlined by the other encoding.
* Strategy 6 (definitional bridge), only tried when strategies 1-5 all failed: the conclusion
  of the base theorem is proved as a named `have beqBaseFact : <conclusion> := by
  apply_rules [<base_theorem>]; <definitional solver>`, and the goal is then reduced to it by
  `convert <CONVERT_CONFIG> beqBaseFact using k` for `k = 1..4`. Each `convert` leaf is
  attacked by a bridge tactic that (a) normalises both sides with
  `simp only [<harvested names>, Function.iterate_succ_apply', Function.iterate_zero_apply]`,
  (b) runs a bounded congruence descent `iterate 16 (all_goals (try (first | rfl | apply
  beqAuxIterateEq ... | funext _ | congr 1)))`, and (c) if that alone does not close the goal,
  retries under `clear * - ; induction <n> with | zero => ... | succ beqStep beqIh => ...` for
  up to `MAX_INDUCTION_VARS` = 3 of the statement's `ℕ`-typed binders (innermost first),
  rewriting with the induction hypothesis after unfolding it. `clear * -` makes the induction
  hypothesis unconditional, which is what lets it apply to the whole trajectory.
* `BRIDGE_PRELUDE` emits two auxiliary theorems at the root of every two-sided command,
  `beqAuxIterateEq : (T 0 = a) -> (forall n, T (n+1) = F (T n)) -> forall n, F^[n] a = T n`
  and its `.symm` variant. Both are fully proved (`induction` + `Function.iterate_succ_apply'`),
  contain no `sorry` and no axiom, and their `F`, `a`, `T` are inferred by unification, so
  `apply beqAuxIterateEq` bridges a structural recursion against a `Function.iterate` encoding
  at any index expression, including compound ones such as `N (k + 1)`.
* Soundness: both new strategies go through the same `checker.check` path as the reference
  ones, i.e. `lean_code_is_valid(..., allow_sorry=False)` on the appended proof, so `sorry`,
  `admit`, `native_decide`, `axiom` or a `Lean.trustCompiler` shortcut in a generated proof can
  never make a job `equivalent`; the injected base theorem stays the only `sorry` in the file.
  The `assumption` false-positive guard is evaluated before them, and strategy 6 additionally
  reuses (and strengthens) the provable-without-`have` check: the check now runs with the
  reformulated side's own `solo_names` as a simp set, so it rejects a wider class of statements
  that are provable on their own than the reference check does.
* Known limits of the bridge: it only closes gaps reachable by unfolding, `Function.iterate`
  normalisation, congruence and induction on a `ℕ` binder of the statement. Rewrites that need
  a side condition are out of reach - e.g. real subtraction `((N : ℝ) - i)` against a cast
  truncated subtraction `((N - i : ℕ) : ℝ)` inside a `Finset.sum` are equal only under
  `i < N`, which requires `Finset.sum_congr` with the range-membership hypothesis. Such a
  candidate stays `not_proven`. An encoding that is off by one iterate step also stays
  `not_proven`, as it must.

Environment (no Mathlib is ever downloaded, copied or rebuilt):
* Lean toolchain `leanprover/lean4:v4.32.2` and the prebuilt Mathlib are reused from
  `$LEAN_ROOT` (required).
* `evaluate/.env/lean-facade` is a Lake package whose `.lake/build/lib/lean` only holds
  symlinks to the shared compiled artifacts; `lean-interact` runs its REPL there through
  `LocalProject(auto_build=False)`, so `lake` never builds or fetches anything.
* `evaluate/.env/repl` holds the cached `augustepoiroux/repl` sources (tag
  `v1.3.18_lean-toolchain-v4.32.0`, `lean-toolchain` pinned to the local toolchain) and its
  compiled `repl` binary. It is cloned and built once on first use and reused afterwards.

Operational notes:
* Recommended `--workers 8` on this 23-core host: one Lean server per worker, peaking around
  3.5 GB RSS each, jobs are pulled from a shared queue so servers stay warm and reuse the
  REPL header cache.
* Observed latency: median ~11 s per job, ~15 s at the 90th percentile, ~29 s when the whole
  reference ladder has to run; the 71 dataset items graded against themselves take ~112 s wall
  clock with `--workers 8`, and all 71 come out `equivalent`. Jobs that reach the two new
  strategies are the expensive ones: ~50-80 s for the recursion-vs-`Function.iterate` controls,
  which is the observed worst case (~79 s).
* Per-job worst case after the relaxation: at most 13 proof searches per direction (precheck,
  `exact?`, `assumption` guard, `apply` + 2 solvers, provable-without-`have` check,
  `have`-conclusion, `convert ... using 0..4`, definitional solver, definitional bridge), i.e.
  <= 26 REPL calls per job. Each is capped by `--timeout-per-proof` (default 60 s) and the job
  as a whole by `--timeout-per-job` (default 12x that = 720 s), so the wall-clock bound per job
  is unchanged; only the average cost of jobs that are *not* `equivalent` early grows.
* `--memory-per-server-mb` defaults to 0 (disabled): `lean-interact` applies it as `RLIMIT_AS`,
  and Lean reserves far more address space than it uses, so small limits make the servers die
  with `std::bad_alloc` while importing Mathlib. Use >= 65536 if a limit is really needed.
* `--timeout-per-job` defaults to 12x `--timeout-per-proof`; exceeding it yields `error`, while
  an individual proof search that times out is just a failed strategy.
* Known BEq+ limitation (inherited on purpose): a statement that `intros; symm_saturate;
  assumption` closes on its own is never certified `equivalent`, because the reference treats
  such proofs as false positives. No dataset statement currently behaves this way.

Deviations from the reference implementation, forced by our dataset / toolchain:
* `simp_all_arith!` only throws "deprecated" in Lean >= 4.20, so the solver tactic set uses
  its documented expansion `simp_all! +arith +decide` instead.
* `tauto` / `noncomm_ring` are Mathlib tactics, and the preambles use narrow imports, so
  `import Mathlib.Tactic.Tauto` and `import Mathlib.Tactic.NoncommRing` are appended to the
  hoisted import block of every two-sided command. The definitional bridge adds
  `import Mathlib.Tactic.ClearExcept` (for `clear * -`) and `import Mathlib.Logic.Function.Iterate`
  (for `Function.iterate_succ_apply'` / `Function.iterate_zero_apply`, also needed by
  `BRIDGE_PRELUDE`). Nothing else is added; `exact?`, `apply_rules`, `symm_saturate`, `intros`,
  `iterate`, `funext`, `congr` and `convert` are Lean core in 4.32.2.
* Both well-typedness prechecks elaborate one side alone (its own imports, its own preamble,
  its statement with a `sorry` body, no tactic imports added), and require the whole command to
  be error free. A candidate is therefore `ill_typed` exactly when its own file does not
  elaborate - never because of a name collision with the reference preamble - and a candidate
  that forgets an import it needs is `ill_typed` even though the reference preamble would have
  provided it, which is the point of the self-contained NC2FT contract. A reference side that
  fails this precheck is reported as `error`.
* The `have`-conclusion strategy extracts the conclusion from the base theorem alone (the
  reference scans header + theorem, which only works when the header carries no `def`), and
  wraps it in `open <base namespaces> in (...)` so that the definitions of the base preamble
  resolve while the `have` is elaborated inside the other side's namespace. Colliding names
  still resolve to the enclosing (reformulated) side, because Lean's namespace chain takes
  precedence over `open`, so for colliding preambles this strategy degenerates to proving the
  candidate's own conclusion; the other strategies are unaffected.
* The provable-without-`have` sanity check elaborates the reformulated side alone (its own
  preamble is required by its statement, unlike in the reference where headers are import-only),
  and its solver is armed with that side's harvested `def`/`abbrev` names as a simp set. The
  guard is therefore strictly stronger than the reference one, and it gates both the
  `have`-conclusion strategy and the new definitional bridge.
* A file-level `set_option maxHeartbeats 400000` is emitted after the imports, because the
  per-side `set_option` lines of a preamble are now scoped to that side's namespace and would
  no longer cover the appended proof search. Each side can still raise it for itself.
* `convert (config := .unfoldSameFun)` no longer elaborates: `convert` expects a
  `Convert.CheapConfig` while `.unfoldSameFun` is a `Congr!.Config` preset, so the same fields
  are now set explicitly (see `CONVERT_CONFIG`).
"""

from __future__ import annotations

import argparse
import dataclasses
import json
import os
import re
import subprocess
import sys
import threading
import time
from pathlib import Path
from queue import Empty, Queue
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from utils.lean_environment import ensure_lean_facade, reusable_lean_paths  # noqa: E402

DEFAULT_LEAN_ROOT = Path(os.environ["LEAN_ROOT"]) if os.environ.get("LEAN_ROOT") else None
ENV_DIR = Path(__file__).resolve().parents[1] / ".env"
REPL_TAG = "v1.3.18_lean-toolchain-v4.32.0"
REPL_GIT_URL = "https://github.com/augustepoiroux/repl"
TACTIC_IMPORTS = (
    "Mathlib.Tactic.Tauto",
    "Mathlib.Tactic.NoncommRing",
    # `clear * -` (auxiliary induction) and the `Function.iterate` rewrite lemmas.
    "Mathlib.Tactic.ClearExcept",
    "Mathlib.Logic.Function.Iterate",
)
# Rewrites turning `f^[n + 1] x` into `f (f^[n] x)`, i.e. into the shape a structural recursion
# unfolds to, so that both encodings of a trajectory expose the same one-step structure.
ITERATE_LEMMAS = ("Function.iterate_succ_apply'", "Function.iterate_zero_apply")
# Rounds of the bounded congruence descent of the bridge strategy: every round applies at most one
# step (`rfl`, an auxiliary-induction leaf, `funext` or `congr 1`) to every open goal.
DESCENT_ROUNDS = 16
# At most this many `ℕ`-typed binders of the reformulated statement are tried as induction targets.
MAX_INDUCTION_VARS = 3
# Auxiliary theorems bridging `Function.iterate` and structural recursion: a sequence that starts
# at `a` and steps with `F` is the iterate of `F`. Both are fully proved (`induction` plus
# `Function.iterate_succ_apply'`), so no `sorry`/axiom enters any proof through them, and `apply`
# infers `F`, `a` and `T` from the goal, which is what makes the strategy representation agnostic.
BRIDGE_PRELUDE = """theorem beqAuxIterateEq {α : Type _} {F : α → α} {a : α} {T : ℕ → α}
    (h0 : T 0 = a) (hs : ∀ n, T (n + 1) = F (T n)) : ∀ n, F^[n] a = T n := by
  intro n
  induction n with
  | zero => simpa using h0.symm
  | succ m ih => rw [Function.iterate_succ_apply', ih, hs]

theorem beqAuxIterateEq' {α : Type _} {F : α → α} {a : α} {T : ℕ → α}
    (h0 : T 0 = a) (hs : ∀ n, T (n + 1) = F (T n)) : ∀ n, T n = F^[n] a :=
  fun n => (beqAuxIterateEq h0 hs n).symm
"""
# Options applying to the whole command: the `set_option` lines of a preamble are scoped to the
# namespace of their own side and would not cover the appended proof search anymore.
FILE_OPTIONS = ("set_option maxHeartbeats 400000",)
REFERENCE_NAMESPACE = "BEqRef"
CANDIDATE_NAMESPACE = "BEqCand"
IMPORT_RE = re.compile(r"^(?:(?:public|private|meta|protected)\s+)*import\s+\S+")
MODULE_RE = re.compile(r"^module\s*$")
SCOPE_OPEN_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:public|private|protected|meta|noncomputable|scoped|local)\s+)*"
    r"(namespace|section|mutual)\b\s*(\S*)"
)
SCOPE_END_RE = re.compile(r"^end\b\s*(\S*)")
OPEN_RE = re.compile(r"^open\s+(\S.*)$")
# Definitions a preamble introduces: only `def`/`abbrev` bodies can be unfolded by `simp only`.
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?((?:(?:private|protected|public|meta|noncomputable|unsafe|partial|scoped|local)\s+)*)"
    r"(def|abbrev)\s+([^\s({\[:⦃⟨]+)"
)
# Binder groups whose type is exactly `ℕ`, e.g. `(K : ℕ)` or `{m n : ℕ}`: the induction targets of
# the auxiliary-induction strategy. `(N : ℕ → ℕ)` deliberately does not match.
NAT_BINDER_RE = re.compile(r"[({⦃]\s*([A-Za-z_][^:()\[\]{}⦃⦄]*?)\s*:\s*ℕ\s*[)}⦄]")
# `convert (config := .unfoldSameFun)` of the reference no longer elaborates: `convert` now
# expects a `Convert.CheapConfig`, while `.unfoldSameFun` is a `Congr!.Config` preset. We spell
# out exactly the fields set by `Congr!.Config.unfoldSameFun`.
CONVERT_CONFIG = (
    "(config := { partialApp := false, sameFun := true, transparency := .default,"
    " preTransparency := .default, postTransparency := .default })"
)
BASE_THM_NAME = "base_theorem"
REFORMULATED_THM_NAME = "reformulated_theorem"
SCHEMA_VERSION = "1.0"
MAX_DETAILS = 300


class JobBudgetExceeded(RuntimeError):
    """Raised when a single job exhausted its wall-clock budget."""


class InfraFailure(RuntimeError):
    """Raised when the Lean server repeatedly failed for reasons unrelated to the proofs."""


class Budget:
    """Wall-clock budget shared by every REPL call of one job."""

    def __init__(self, timeout_per_proof: float, timeout_per_job: float):
        self.timeout_per_proof = timeout_per_proof
        self._deadline = time.monotonic() + timeout_per_job

    def remaining(self) -> float:
        return self._deadline - time.monotonic()

    def next_timeout(self) -> float:
        remaining = self.remaining()
        if remaining <= 0:
            raise JobBudgetExceeded("job budget exhausted")
        return min(self.timeout_per_proof, remaining)


def log(message: str, verbose: bool) -> None:
    if verbose:
        print(message, file=sys.stderr, flush=True)


# --------------------------------------------------------------------------------------
# Lean environment provisioning
# --------------------------------------------------------------------------------------


def write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def lean_paths(lean_root: Path, mathlib_root: Path) -> list[Path]:
    """Compiled Lean library directories shared by every project of the repository."""
    paths = reusable_lean_paths(mathlib_root)
    known = {path.resolve() for path in paths}
    for extra in (lean_root / "cslib", lean_root / "slt"):
        build = extra / ".lake" / "build" / "lib" / "lean"
        if build.is_dir() and build.resolve() not in known:
            paths.append(build.resolve())
            known.add(build.resolve())
    return paths


def ensure_facade(lean_root: Path, mathlib_root: Path, facade_dir: Path) -> Path:
    """Create/refresh the Lake facade project pointing at the shared Mathlib artifacts."""
    sources = lean_paths(lean_root, mathlib_root)
    if not sources:
        raise RuntimeError(f"no compiled Lean artifacts found under {mathlib_root}")
    facade_dir.mkdir(parents=True, exist_ok=True)
    ensure_lean_facade(facade_dir, sources, "evaluate_beq", write_text)
    toolchain = (mathlib_root / "lean-toolchain").read_text(encoding="utf-8").strip()
    write_text(facade_dir / "lean-toolchain", toolchain + "\n")
    manifest = facade_dir / "lake-manifest.json"
    if not manifest.is_file():
        write_text(
            manifest,
            json.dumps(
                {
                    "version": "1.2.0",
                    "packagesDir": ".lake/packages",
                    "packages": [],
                    "name": "evaluate_beq",
                    "lakeDir": ".lake",
                },
                indent=1,
            )
            + "\n",
        )
    return facade_dir


def ensure_repl_sources(repl_dir: Path, verbose: bool) -> Path:
    """Make sure the REPL sources are cached locally, cloning them once if necessary."""
    if (repl_dir / "REPL.lean").is_file():
        return repl_dir
    if repl_dir.exists():
        raise RuntimeError(f"incomplete REPL cache at {repl_dir}: remove the directory and run again")
    log(f"[beq] cloning the Lean REPL ({REPL_TAG}) into {repl_dir}", verbose)
    repl_dir.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(
        ["git", "clone", "--quiet", "--depth", "1", "--branch", REPL_TAG, REPL_GIT_URL, str(repl_dir)],
        check=True,
        timeout=1800,
    )
    return repl_dir


def build_repl(repl_dir: Path, lake_path: Path, toolchain: str, verbose: bool) -> None:
    """Compile the REPL binary against the local toolchain (once, then cached)."""
    binary = repl_dir / ".lake" / "build" / "bin" / "repl"
    if binary.is_file():
        return
    write_text(repl_dir / "lean-toolchain", toolchain + "\n")
    log(f"[beq] building the Lean REPL in {repl_dir}", verbose)
    subprocess.run(
        [str(lake_path), "build"],
        cwd=repl_dir,
        check=True,
        timeout=1800,
        stdout=None if verbose else subprocess.DEVNULL,
        stderr=None if verbose else subprocess.DEVNULL,
    )


def prepare_environment(
    lean_root: Path,
    mathlib_root: Path,
    env_dir: Path,
    memory_per_server_mb: int | None,
    verbose: bool,
):
    """Return a ready-to-share `LeanREPLConfig` bound to the local toolchain and Mathlib."""
    lake_path = lean_root / "bin" / "lake"
    if not lake_path.is_file():
        raise RuntimeError(f"lake executable not found: {lake_path}")
    os.environ["PATH"] = f"{lean_root / 'bin'}{os.pathsep}{os.environ.get('PATH', '')}"
    os.environ["LEAN_PATH"] = os.pathsep.join(str(path) for path in lean_paths(lean_root, mathlib_root))
    os.environ.setdefault("LEAN_NUM_THREADS", "2")

    facade = ensure_facade(lean_root, mathlib_root, env_dir / "lean-facade")
    toolchain = (mathlib_root / "lean-toolchain").read_text(encoding="utf-8").strip()
    repl_dir = ensure_repl_sources(env_dir / "repl", verbose)
    build_repl(repl_dir, lake_path, toolchain, verbose)

    from lean_interact import LeanREPLConfig
    from lean_interact.project import LocalProject

    return LeanREPLConfig(
        project=LocalProject(directory=str(facade), lake_path=str(lake_path), auto_build=False),
        local_repl_path=str(repl_dir),
        build_repl=False,
        lake_path=str(lake_path),
        memory_hard_limit_mb=memory_per_server_mb,
        verbose=verbose,
    )


# --------------------------------------------------------------------------------------
# BEq+ metric
# --------------------------------------------------------------------------------------


def solver_proofs() -> tuple[str, str]:
    """Return the `apply`-style and `have`-style solver tactic blocks of BEq+."""

    def prove_all(tactics: list[str]) -> str:
        prove_independent = " ; ".join([f"(all_goals try {t})" for t in tactics])
        prove_combined = "all_goals (" + " ; ".join([f"(try {t})" for t in tactics]) + ")"
        return "all_goals intros\nfirst | (" + prove_independent + ") | (" + prove_combined + ")"

    simp_all_arith = "simp_all! +arith +decide"
    apply_tactics = ["tauto", simp_all_arith, "noncomm_ring", "exact?"]
    have_tactics = ["tauto", simp_all_arith, "exact? using this"]
    return prove_all(apply_tactics), prove_all(have_tactics)


def definitional_solvers(defs: str) -> tuple[str, str]:
    """`solver_proofs`, but every `simp_all` also unfolds the definitions of both preambles.

    This is the cheap half of the relaxation: two preambles that encode the same notion with
    different `def`s (or bundle the same hypotheses differently) become comparable as soon as the
    solver may unfold them, which the plain BEq+ tactic set never does.
    """

    def prove_all(tactics: list[str]) -> str:
        prove_independent = " ; ".join([f"(all_goals try {t})" for t in tactics])
        prove_combined = "all_goals (" + " ; ".join([f"(try {t})" for t in tactics]) + ")"
        return "all_goals intros\nfirst | (" + prove_independent + ") | (" + prove_combined + ")"

    simp_all_defs = f"simp_all! +arith +decide [{defs}]"
    apply_tactics = ["tauto", simp_all_defs, "noncomm_ring", "exact?"]
    have_tactics = ["tauto", simp_all_defs, "exact? using this"]
    return prove_all(apply_tactics), prove_all(have_tactics)


def induction_targets(statement: str) -> list[str]:
    """`ℕ`-typed binder names of a statement, innermost first, as auxiliary-induction targets.

    The binders of the reformulated theorem are still named in the goal (they are binders of the
    theorem, not `intro`duced by the proof), so they can be used verbatim by `induction`. Later
    binders come first because an iteration count is usually introduced after the data it counts.
    """
    names: list[str] = []
    for group in NAT_BINDER_RE.findall(statement):
        names.extend(group.split())
    unique = list(dict.fromkeys(reversed(names)))
    return unique[:MAX_INDUCTION_VARS]


def bridge_proof(defs: str, targets: list[str]) -> str:
    """Tactic closing purely definitional equality goals, e.g. recursion vs `Function.iterate`.

    `convert` reduces the two statements to equalities between the corresponding subterms of both
    encodings; this tactic is what closes them. It is a bounded fixpoint: every round applies at
    most one step to every open goal, and the steps are `rfl`, the two auxiliary iterate/recursion
    theorems (whose `F`, `a` and `T` are inferred from the goal by `apply`), `funext` and
    `congr 1`. When the two encodings recurse on a `ℕ` argument of the statement, a bounded
    induction on that argument is tried as well: the induction hypothesis is rewritten into the
    goal and the descent closes the step. Nothing here can prove an equality that does not hold,
    and `done` makes an incomplete attempt fail instead of silently leaving goals open.
    """
    unfold = f"simp only [{defs}]"
    unfold_iterate = f"simp only [{defs}, {', '.join(ITERATE_LEMMAS)}]"
    leaf = f"(first | rfl | ({unfold}; try rfl))"
    descent = (
        f"iterate {DESCENT_ROUNDS} (all_goals (try (first"
        " | rfl"
        f" | (apply beqAuxIterateEq <;> intros <;> {leaf})"
        f" | (apply beqAuxIterateEq' <;> intros <;> {leaf})"
        " | funext _"
        " | congr 1)))"
    )
    close = f"((try {unfold_iterate}); {descent})"
    step = (
        f"((try {unfold_iterate} at beqIh); (try {unfold_iterate}); (try simp only [beqIh]);"
        f" (try rw [beqIh]); (try {unfold_iterate}); {descent})"
    )
    inductions = [
        f"((clear * - ; induction {target} with | zero => {close} | succ beqStep beqIh => {step}); done)"
        for target in targets
    ]
    return "first | " + " | ".join([f"({close}; done)", *inductions])


def hoist_imports(header: str) -> tuple[list[str], str]:
    """Split a preamble into its `import` lines and the body that has to stay in a namespace.

    A lone `module` line is hoisted as well: the Lean module system requires it to be the very
    first command of the file, before any import.
    """
    imports: list[str] = []
    body: list[str] = []
    for line in header.splitlines():
        if IMPORT_RE.match(line) or MODULE_RE.match(line):
            imports.append(line.strip())
        else:
            body.append(line)
    while body and not body[0].strip():
        body.pop(0)
    return imports, "\n".join(body).rstrip()


def scan_scopes(body: str) -> tuple[list[str], list[str], list[str], bool]:
    """Inspect a preamble body for scopes it leaves open and for the namespaces it opens.

    Returns the namespaces still open at the end of the body (they prefix the theorem name),
    the `end` lines closing every scope still open (innermost first), the payloads of its
    `open` commands (needed to re-expose the side's scope from inside the other namespace),
    and whether the body closes more scopes than it opens.
    """
    from lean_interact.utils import remove_lean_comments

    text = remove_lean_comments(body) or body
    stack: list[tuple[str, str]] = []
    opens: list[str] = []
    balanced = True
    for raw in text.splitlines():
        line = raw.strip()
        opened = SCOPE_OPEN_RE.match(line)
        ended = SCOPE_END_RE.match(line)
        declared = OPEN_RE.match(line)
        if opened:
            stack.append((opened.group(1), opened.group(2)))
        elif ended:
            if stack:
                stack.pop()
            else:
                balanced = False
        elif declared and " in " not in f" {line} ":
            opens.append(declared.group(1).strip())
    namespaces = [name for kind, name in stack if kind == "namespace" and name]
    closers = [f"end {name}".strip() for _, name in reversed(stack)]
    return namespaces, closers, opens, balanced


def declaration_names(body: str, prefix: tuple[str, ...]) -> list[str]:
    """Fully qualified names of the `def`/`abbrev` declarations a preamble body introduces.

    `prefix` is the namespace the body is elaborated in (shared scopes plus wrapper namespace).
    Nested `namespace` blocks of the body extend that prefix, so the returned names are usable
    from the other side as well. `private` declarations are skipped: they are not accessible from
    another namespace. Only `def`/`abbrev` are collected, since only their bodies (or their
    equation lemmas, for structural recursion) can be unfolded by `simp only`/`unfold`.
    """
    from lean_interact.utils import remove_lean_comments

    text = remove_lean_comments(body) or body
    stack: list[str] = []
    names: list[str] = []
    for raw in text.splitlines():
        line = raw.strip()
        opened = SCOPE_OPEN_RE.match(line)
        ended = SCOPE_END_RE.match(line)
        declared = DECL_RE.match(line)
        if opened:
            stack.append(opened.group(2) if opened.group(1) == "namespace" else "")
        elif ended:
            if stack:
                stack.pop()
        elif declared and "private" not in declared.group(1):
            parts = [*prefix, *(scope for scope in stack if scope), declared.group(3)]
            names.append("_root_." + ".".join(parts) if parts else declared.group(3))
    return names


def starts_declaration(lines: list[str], index: int) -> bool:
    """True when `lines[index]` cannot be the continuation of the declaration before it."""
    if index >= len(lines):
        return True
    return not lines[index].strip() or not lines[index][:1].isspace()


def split_shared(first: str, second: str) -> tuple[str, str, str]:
    """Hoist the longest common prefix of two preambles, returning (shared, rest, rest).

    A Lean preamble is linear - a declaration only depends on earlier ones - so a common prefix
    is self-contained and can be elaborated once, outside both namespaces. This is what makes
    identical (or partially identical) preambles comparable at all: a `structure`, `inductive`
    or `class` declared once per namespace yields two distinct, non-convertible types, so
    duplicating it would make even a verbatim copy of the reference unprovable. The cut is moved
    back to a declaration boundary, and it is dropped entirely when it would leave a stray `end`
    in one of the remainders.
    """
    left, right = first.splitlines(), second.splitlines()
    limit = 0
    while limit < min(len(left), len(right)) and left[limit] == right[limit]:
        limit += 1
    while limit > 0 and not (starts_declaration(left, limit) and starts_declaration(right, limit)):
        limit -= 1
    shared = "\n".join(left[:limit]).rstrip()
    rests = ["\n".join(side[limit:]).strip("\n") for side in (left, right)]
    if any(not scan_scopes(rest)[3] for rest in rests):
        return "", first, second
    return shared, rests[0], rests[1]


@dataclasses.dataclass(frozen=True)
class Side:
    """One statement with its own preamble, isolated inside a wrapper namespace."""

    wrapper: str
    imports: tuple[str, ...]
    preamble: str
    body: str
    closers: tuple[str, ...]
    scopes: tuple[str, ...]
    opens: tuple[str, ...]
    statement: str
    names: tuple[str, ...] = ()
    solo_names: tuple[str, ...] = ()

    @property
    def namespace(self) -> str:
        """Namespace the theorem of this side ends up in, wrapper and shared scopes included."""
        return ".".join(self.scopes)

    def theorem(self, name: str, add_sorry: bool) -> str:
        """Rename the statement's theorem and optionally give it a `sorry` body."""
        from lean_interact.utils import clean_last_theorem_string

        return clean_last_theorem_string(self.statement, name, add_sorry=add_sorry)

    def qualified(self, name: str) -> str:
        """Name under which a declaration of this side is visible from the other one."""
        return f"_root_.{self.namespace}.{name}"

    def opening(self) -> str:
        """Wrapper namespace plus the unshared preamble, ready to be followed by a declaration."""
        parts = [f"namespace {self.wrapper}"]
        if self.body:
            parts.append(self.body)
        return "\n".join(parts) + "\n\n"

    def closing(self) -> str:
        """Close the scopes the unshared preamble left open, then the wrapper namespace itself."""
        return "\n".join([*self.closers, f"end {self.wrapper}"]) + "\n"

    def open_decls(self) -> list[str]:
        """`open` payloads exposing this side's declarations to code elaborated elsewhere."""
        namespaces = [self.scopes[0]]
        for scope in self.scopes[1:]:
            namespaces.append(f"{namespaces[-1]}.{scope}")
        return [" ".join(namespaces), *self.opens]


def make_pair(job: dict[str, Any]) -> tuple[str, Side, Side]:
    """Build both isolated sides of a job plus the preamble prefix they share verbatim."""
    headers = [
        hoist_imports(job.get("reference_header", "")),
        hoist_imports(job.get("candidate_header", "")),
    ]
    shared, *bodies = split_shared(headers[0][1], headers[1][1])
    shared_scopes, _, _, _ = scan_scopes(shared)
    shared_names = declaration_names(shared, ())
    sides = []
    for wrapper, (imports, preamble), body, statement in zip(
        (REFERENCE_NAMESPACE, CANDIDATE_NAMESPACE),
        headers,
        bodies,
        (job.get("reference", ""), job.get("candidate", "")),
    ):
        namespaces, closers, opens, _ = scan_scopes(body)
        sides.append(
            Side(
                wrapper=wrapper,
                imports=tuple(imports),
                preamble=preamble,
                body=body,
                closers=tuple(closers),
                scopes=(*shared_scopes, wrapper, *namespaces),
                opens=tuple(opens),
                statement=statement.strip(),
                names=tuple(shared_names + declaration_names(body, (*shared_scopes, wrapper))),
                solo_names=tuple(declaration_names(preamble, ())),
            )
        )
    return shared, sides[0], sides[1]


def import_block(*groups: tuple[str, ...]) -> str:
    """Deduplicated `module`/`import` lines of every side, followed by the command-level options."""
    lines: list[str] = []
    seen: set[str] = set()
    module = False
    for group in groups:
        for entry in group:
            text = entry.strip()
            if MODULE_RE.match(text):
                module = True
                continue
            line = text if IMPORT_RE.match(text) else f"import {text}"
            name = line.split()[-1]
            if name not in seen:
                seen.add(name)
                lines.append(line)
    prelude = ["module"] if module else []
    return "\n".join([*prelude, *lines, *FILE_OPTIONS]) + "\n\n"


def pair_code(shared: str, base: Side, reform: Side, base_name: str, reform_name: str) -> tuple[str, int]:
    """Assemble both sides, the base one `sorry`ed and closed, the reformulated one left open.

    The auxiliary iterate/recursion theorems of `BRIDGE_PRELUDE` are declared at root level right
    after the imports, so both sides and the appended proof can use them.

    Returns the code up to and including `:= by`, and the line of the reformulated theorem.
    """
    prefix = (
        import_block(base.imports, reform.imports, TACTIC_IMPORTS)
        + BRIDGE_PRELUDE
        + "\n"
        + (shared + "\n\n" if shared else "")
        + base.opening()
        + base.theorem(base_name, add_sorry=True)
        + "\n\n"
        + base.closing()
        + "\n"
        + reform.opening()
    )
    return prefix + reform.theorem(reform_name, add_sorry=False) + " := by", prefix.count("\n") + 1


def solo_code(side: Side, name: str, proof: str | None, tactic_imports: bool) -> tuple[str, int]:
    """Assemble one side alone, as its author wrote it: no wrapper namespace, own preamble only.

    `proof` is `None` for the `sorry` well-typedness precheck, which needs no tactic import.
    """
    extra = TACTIC_IMPORTS if tactic_imports else ()
    prefix = import_block(side.imports, extra) + (side.preamble + "\n\n" if side.preamble else "")
    if proof is None:
        return prefix + side.theorem(name, add_sorry=True), prefix.count("\n") + 1
    return prefix + side.theorem(name, add_sorry=False) + " := by" + proof, prefix.count("\n") + 1


def open_in(text: str, decls: list[str]) -> str:
    """Wrap a type coming from another side in the `open ... in` layers it needs to elaborate."""
    wrapped = f"({text})"
    for decl in reversed(decls):
        if decl:
            wrapped = f"(open {decl} in {wrapped})"
    return wrapped


def extract_exact_proof(lean_output, proof_start_line: int | None = None) -> str | None:
    """Port of the reference helper: read the `Try this:` suggestion of `exact?`."""
    from lean_interact.interface import Pos, message_intersects_code

    start = Pos(line=proof_start_line, column=0) if proof_start_line else None
    for message in lean_output.messages:
        if message_intersects_code(message, start, None):
            if message.severity == "error":
                return None
            if message.severity == "info" and message.data.startswith("Try this:"):
                return message.data.split("Try this:")[1].strip()
    return None


class ProofChecker:
    """Runs Lean code with a candidate proof appended, mirroring `check_proof_sub`."""

    def __init__(self, server, budget: Budget, verbose: bool = False):
        self.server = server
        self.budget = budget
        self.verbose = verbose
        self.infra_failures = 0

    def note_infra_failure(self, error: BaseException, context: str) -> None:
        """Record a REPL-level failure, escalating to `InfraFailure` if they keep coming."""
        self.infra_failures += 1
        log(f"[beq] REPL error during {context}: {type(error).__name__}: {error}", self.verbose)
        if self.infra_failures >= 3:
            raise InfraFailure(f"{self.infra_failures} REPL failures, last one: {type(error).__name__}: {error}")

    def run(self, code: str, timeout: float):
        from lean_interact import Command

        return self.server.run(Command(cmd=code), timeout=timeout)

    def check(self, formal_code: str, formal_2_start_line: int, proof: str, indent_level: int = 2) -> str | None:
        from lean_interact.interface import CommandResponse, LeanError, Pos
        from lean_interact.utils import indent_code

        prepended = "\nintros\nsymm_saturate\n"
        timeout = self.budget.next_timeout()
        try:
            lean_output = self.run(formal_code + indent_code(prepended + proof, indent_level), timeout)
            if isinstance(lean_output, LeanError):
                return None
            if not isinstance(lean_output, CommandResponse):
                return None
            start = Pos(line=formal_2_start_line, column=0)
            if proof == "sorry":
                return proof if lean_output.lean_code_is_valid(start_pos=start) else None
            if lean_output.lean_code_is_valid(start_pos=start, allow_sorry=False):
                if proof == "exact?":
                    return extract_exact_proof(lean_output, proof_start_line=formal_2_start_line)
                return proof
        except TimeoutError:
            log(f"[beq] timeout on proof `{proof.splitlines()[0][:40]}`", self.verbose)
        except (ConnectionAbortedError, ChildProcessError, MemoryError, json.JSONDecodeError) as error:
            self.note_infra_failure(error, "proof checking")
        return None

    def side_is_well_typed(self, side: Side) -> tuple[bool, str]:
        """`sorry` well-typedness precheck of one side alone: its imports, preamble, statement."""
        from lean_interact.interface import CommandResponse

        code, _ = solo_code(side, REFORMULATED_THM_NAME, None, tactic_imports=False)
        try:
            lean_output = self.run(code, self.budget.next_timeout())
        except TimeoutError:
            log("[beq] timeout on the well-typedness precheck", self.verbose)
            return False, "timed out"
        except (ConnectionAbortedError, ChildProcessError, MemoryError, json.JSONDecodeError) as error:
            self.note_infra_failure(error, "the well-typedness precheck")
            return False, f"lean server failure: {error}"
        if not isinstance(lean_output, CommandResponse):
            return False, "lean rejected the file before elaboration"
        if lean_output.lean_code_is_valid():
            return True, ""
        errors = [message.data for message in lean_output.messages if message.severity == "error"]
        return False, errors[0].strip().replace("\n", " ")[:400] if errors else "unknown elaboration error"


def beq_plus(
    shared: str,
    reference: Side,
    candidate: Side,
    checker: ProofChecker,
    labels: tuple[str, str] = ("1 -> 2", "2 -> 1"),
) -> tuple[bool, list[str]]:
    """Port of `beq_plus` for per-side preambles: (equivalence proven, per-direction details)."""
    from lean_interact.interface import CommandResponse, Pos
    from lean_interact.utils import indent_code, split_conclusion

    proof_all_apply, proof_all_have = solver_proofs()
    res = [False, False]
    details: list[str] = []

    for i, (base, reform) in enumerate([(reference, candidate), (candidate, reference)]):
        try:
            formal_code, formal_2_start_line = pair_code(
                shared, base, reform, BASE_THM_NAME, REFORMULATED_THM_NAME
            )
            base_declaration = base.theorem(BASE_THM_NAME, add_sorry=True)
        except ValueError:
            details.append(f"{labels[i]}: invalid theorem string")
            break
        base_thm = base.qualified(BASE_THM_NAME)
        # Definitions both preambles introduce: the rewrite set of the relaxed strategies. `defs`
        # is qualified for the assembled pair, `solo_defs` for the reformulated side alone.
        defs = ", ".join(dict.fromkeys([*base.names, *reform.names]))
        solo_defs = ", ".join(dict.fromkeys(reform.solo_names))
        defs_apply = definitional_solvers(defs)[0] if defs else proof_all_apply

        # Preliminary check to ensure the pair elaborates together.
        if checker.check(formal_code, formal_2_start_line, "sorry") is None:
            details.append(f"{labels[i]}: ill-typed pair")
            break

        # 1. BEqL fast path.
        proof_exact = checker.check(formal_code, formal_2_start_line, "exact?")
        if proof_exact and BASE_THM_NAME in proof_exact:
            res[i] = True
            details.append(f"{labels[i]}: exact? ({proof_exact})")
            continue

        # If trivially provable by `assumption`, we skip: it would be a false positive.
        if checker.check(formal_code, formal_2_start_line, "assumption"):
            details.append(f"{labels[i]}: skipped, provable by assumption")
            continue

        # 2. Apply the base theorem directly.
        if checker.check(formal_code, formal_2_start_line, f"apply {base_thm}\n" + proof_all_apply):
            res[i] = True
            details.append(f"{labels[i]}: apply {base_thm}")
            continue

        # Sanity check shared by every strategy that assumes the conclusion of the base theorem:
        # a statement its own side's solver proves alone can never count as equivalent. The solver
        # used here may unfold the reformulated side's own definitions, which is a superset of the
        # plain one, so the guard also covers the relaxed strategies below.
        provable_without_have = False
        try:
            solo_have = definitional_solvers(solo_defs)[1] if solo_defs else proof_all_have
            code, start_line = solo_code(
                reform, REFORMULATED_THM_NAME, indent_code(solo_have, 2), tactic_imports=True
            )
            response = checker.run(code, checker.budget.next_timeout())
            if isinstance(response, CommandResponse):
                provable_without_have = response.lean_code_is_valid(
                    start_pos=Pos(line=start_line, column=0), allow_sorry=False
                )
        except TimeoutError:
            pass
        except (ConnectionAbortedError, ChildProcessError, MemoryError, json.JSONDecodeError) as error:
            checker.note_infra_failure(error, "the provable-without-have check")

        idx_conclusion = split_conclusion(base_declaration)
        conclusion = ""
        if idx_conclusion:
            idx_end_conclusion = base_declaration.rfind(":=")
            conclusion = base_declaration[idx_conclusion + 1 : idx_end_conclusion].strip()

        # 3. Add the conclusion of the base theorem as a hypothesis.
        if not provable_without_have and conclusion:
            have_stmt_proof = (
                f"have : {open_in(conclusion, base.open_decls())} := by\n"
                + indent_code(f"apply_rules [{base_thm}]\n" + proof_all_apply, 2)
                + "\n"
            )
            if checker.check(formal_code, formal_2_start_line, have_stmt_proof + proof_all_have):
                res[i] = True
                details.append(f"{labels[i]}: have-conclusion")
                continue

        # 4. Apply the base theorem with some tolerance on the conclusion.
        for max_step in range(0, 5):
            if checker.check(
                formal_code,
                formal_2_start_line,
                f"convert {CONVERT_CONFIG} {base_thm} using {max_step}\n" + proof_all_apply,
            ):
                res[i] = True
                details.append(f"{labels[i]}: convert using {max_step}")
                break
        if res[i]:
            continue

        # 5. Apply the base theorem, letting the solver unfold the definitions of both preambles.
        if defs and checker.check(formal_code, formal_2_start_line, f"apply {base_thm}\n" + defs_apply):
            res[i] = True
            details.append(f"{labels[i]}: apply {base_thm} + definitional solver")
            continue

        # 6. Definitional bridge: assume the conclusion of the base theorem, let `convert` reduce
        # the two encodings to equalities between corresponding subterms, and close those with the
        # definitional descent plus a bounded auxiliary induction. Same guard as strategy 3.
        if defs and conclusion and not provable_without_have:
            bridge = bridge_proof(defs, induction_targets(reform.statement))
            alternatives = " | ".join(
                f"(convert {CONVERT_CONFIG} beqBaseFact using {step} <;> ({bridge}))" for step in range(1, 5)
            )
            bridge_stmt_proof = (
                f"have beqBaseFact : {open_in(conclusion, base.open_decls())} := by\n"
                + indent_code(f"apply_rules [{base_thm}]\n" + defs_apply, 2)
                + "\n"
                + f"first | {alternatives}"
            )
            if checker.check(formal_code, formal_2_start_line, bridge_stmt_proof):
                res[i] = True
                details.append(f"{labels[i]}: definitional bridge")
                continue

        if not res[i]:
            details.append(f"{labels[i]}: not proven")
            break

    return res[0] and res[1], details


# --------------------------------------------------------------------------------------
# Job grading
# --------------------------------------------------------------------------------------


def grade_job(job: dict[str, Any], server, timeout_per_proof: float, timeout_per_job: float, verbose: bool):
    """Grade one job and return (verdict, details)."""
    checker = ProofChecker(server, Budget(timeout_per_proof, timeout_per_job), verbose)
    shared, reference, candidate = make_pair(job)

    try:
        reference.theorem(BASE_THM_NAME, add_sorry=True)
    except ValueError:
        return "error", "reference statement could not be parsed as a single theorem"
    try:
        candidate.theorem(BASE_THM_NAME, add_sorry=True)
    except ValueError:
        return "ill_typed", "candidate statement could not be parsed as a single theorem"

    ok, reason = checker.side_is_well_typed(reference)
    if not ok:
        return "error", f"reference header + statement failed the `sorry` well-typedness precheck: {reason}"
    ok, reason = checker.side_is_well_typed(candidate)
    if not ok:
        return "ill_typed", f"candidate header + statement failed the `sorry` well-typedness precheck: {reason}"

    equivalent, details = beq_plus(
        shared, reference, candidate, checker, labels=("reference -> candidate", "candidate -> reference")
    )
    reason = "; ".join(details) if details else "no direction proven"
    return ("equivalent" if equivalent else "not_proven"), reason


def worker_loop(config, tasks: Queue, results: list, args, worker_id: int) -> None:
    """Own one Lean server and grade jobs until the queue is empty."""
    from lean_interact import AutoLeanServer

    server = None
    try:
        while True:
            try:
                index, job = tasks.get_nowait()
            except Empty:
                return
            started = time.monotonic()
            try:
                if server is None:
                    log(f"[beq] worker {worker_id}: starting Lean server", args.verbose)
                    server = AutoLeanServer(config=config)
                verdict, details = grade_job(
                    job, server, args.timeout_per_proof, args.timeout_per_job, args.verbose
                )
            except JobBudgetExceeded:
                verdict, details = "error", f"job exceeded its {args.timeout_per_job:g}s wall-clock budget"
            except Exception as error:  # noqa: BLE001 - never fail the whole run for one job
                verdict = "error"
                details = f"{type(error).__name__}: {error}"
                if server is not None:
                    try:
                        server.kill()
                    except Exception:  # noqa: BLE001
                        pass
                    server = None
            duration = time.monotonic() - started
            results[index] = {
                "id": job.get("id"),
                "verdict": verdict,
                "details": details[:MAX_DETAILS],
                "duration_seconds": round(duration, 3),
            }
            log(f"[beq] worker {worker_id}: {job.get('id')} -> {verdict} ({duration:.1f}s)", args.verbose)
            tasks.task_done()
    finally:
        if server is not None:
            try:
                server.kill()
            except Exception:  # noqa: BLE001
                pass


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="BEq+ grader for Lean statement autoformalization")
    parser.add_argument("--jobs", required=True, type=Path, help="input jobs JSON file")
    parser.add_argument("--report", required=True, type=Path, help="output report JSON file")
    parser.add_argument(
        "--workers",
        type=int,
        default=4,
        help="number of concurrent Lean servers, one per worker (default 4, recommended 8)",
    )
    parser.add_argument("--timeout-per-proof", type=float, default=60.0, help="timeout per REPL command in seconds")
    parser.add_argument(
        "--timeout-per-job",
        type=float,
        default=0.0,
        help="wall-clock budget per job in seconds (default: 12x --timeout-per-proof)",
    )
    parser.add_argument("--lean-root", type=Path, default=DEFAULT_LEAN_ROOT, help="local Lean toolchain root")
    parser.add_argument("--mathlib-root", type=Path, default=None, help="prebuilt Mathlib root")
    parser.add_argument("--env-dir", type=Path, default=ENV_DIR, help="directory holding the REPL and facade caches")
    parser.add_argument(
        "--memory-per-server-mb",
        type=int,
        default=0,
        help=(
            "hard memory limit per Lean server, 0 (default) disables it. lean-interact enforces it as"
            " RLIMIT_AS, i.e. on reserved address space, which Lean largely overshoots: values below"
            " ~65536 make servers die with std::bad_alloc while importing Mathlib"
        ),
    )
    parser.add_argument("--verbose", action="store_true", help="log progress to stderr")
    args = parser.parse_args(argv)
    if args.timeout_per_job <= 0:
        args.timeout_per_job = 12 * args.timeout_per_proof
    if args.lean_root is None:
        parser.error("no Lean root given: export LEAN_ROOT or pass --lean-root")
    if args.mathlib_root is None:
        args.mathlib_root = args.lean_root / "mathlib4"
    args.workers = max(1, args.workers)
    return args


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    payload = json.loads(args.jobs.read_text(encoding="utf-8"))
    jobs = payload.get("jobs", [])
    results: list[dict[str, Any] | None] = [None] * len(jobs)

    try:
        if jobs:
            config = prepare_environment(
                args.lean_root,
                args.mathlib_root,
                args.env_dir,
                args.memory_per_server_mb or None,
                args.verbose,
            )
            tasks: Queue = Queue()
            for index, job in enumerate(jobs):
                tasks.put((index, job))
            threads = [
                threading.Thread(
                    target=worker_loop, args=(config, tasks, results, args, worker_id), daemon=True
                )
                for worker_id in range(min(args.workers, len(jobs)))
            ]
            for thread in threads:
                thread.start()
            for thread in threads:
                thread.join()
    except Exception as error:  # noqa: BLE001 - report the failure instead of crashing
        print(f"[beq] fatal: {type(error).__name__}: {error}", file=sys.stderr, flush=True)
        for index, job in enumerate(jobs):
            if results[index] is None:
                results[index] = {
                    "id": job.get("id"),
                    "verdict": "error",
                    "details": f"environment failure: {type(error).__name__}: {error}"[:MAX_DETAILS],
                    "duration_seconds": 0.0,
                }

    for index, job in enumerate(jobs):
        if results[index] is None:
            results[index] = {
                "id": job.get("id"),
                "verdict": "error",
                "details": "job was not processed",
                "duration_seconds": 0.0,
            }

    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(
        json.dumps({"schema_version": SCHEMA_VERSION, "results": results}, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

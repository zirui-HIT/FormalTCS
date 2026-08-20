# Task: Autoformalization

`input/nl_claim.md` contains a natural-language theorem statement. `input/imports.lean`
contains the Mathlib import lines the reference formalization uses. No definitions are given:
choosing the Lean representation of every notion in the claim is part of the task.

Deliverable: write one self-contained Lean 4 file to `output/statement.lean`.

Requirements:

- Read the inputs with your own tools. Never modify anything under `input/`.
- `output/statement.lean` must hold, in this order: the import lines, then every auxiliary
  `def`, `abbrev`, `notation`, or `instance` your formalization needs, then exactly one
  top-level `theorem` that formalizes the claim and ends with `:=`, with no proof. Keep imports
  narrow; add further Mathlib imports only when you actually need them.
- Formalize the claim faithfully: every hypothesis and the exact conclusion of the informal
  statement must appear, with no extra assumptions that weaken it and no definition that makes
  it vacuous.
- `project/candidate.lean` is a scratch file seeded with the same imports. Develop there,
  append `:= by sorry` to your theorem, and run `./check.sh` to type-check against the shared
  Mathlib build. The script compiles concurrently, so run it as often as you need. A
  `declaration uses 'sorry'` warning is expected; any error is not.
- Equivalence with the reference formalization is checked mechanically in both directions, so a
  file that merely type-checks but weakens, strengthens, or trivializes the claim scores zero.
- Finish only after `output/statement.lean` type-checks (with `:= by sorry` appended) and holds
  the statement without its proof.

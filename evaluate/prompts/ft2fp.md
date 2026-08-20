# Task: Theorem Proving

`project/` is a ready-to-build Lake project. `project/theorem.lean` holds narrow Mathlib
imports, the auxiliary definitions of this problem, and exactly one theorem whose proof is
`by sorry`. The shared prebuilt Mathlib is already linked into `project/.lake/packages`, so
never download, copy, or rebuild Mathlib or any dependency.

Deliverable: write the complete proved file to `output/proof.lean`.

Requirements:

- Prove the theorem by replacing `sorry` with a real proof. Work in `project/theorem.lean`.
- Do not change the theorem statement, its name, its binders, or the existing definitions. You
  may add auxiliary lemmas above the theorem and may add narrow Mathlib imports.
- Forbidden anywhere in the file: `sorry`, `admit`, `stop`, `sorryAx`, `axiom`, `native_decide`,
  and any `set_option` that relaxes `warn.sorry` or `warningAsError`. Verification recompiles
  the file strictly, audits the environment axioms of the target declaration, and replays the
  proof in a fresh kernel, so none of these can pass.
- `./check.sh` compiles `project/theorem.lean` with `-Dwarn.sorry=true -DwarningAsError=true`
  and with parallel workers. Iterate with it until it reports no errors and no warnings.
- Then copy the final file verbatim to `output/proof.lean`.
- Partial credit does not exist: only a fully verified proof counts. If time runs out, still
  copy your best complete-file attempt to `output/proof.lean`.

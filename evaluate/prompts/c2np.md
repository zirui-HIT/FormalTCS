# Task: Proof Elicitation

`input/nl_claim.md` contains a natural-language theorem statement and `input/theorem.lean`
contains its Lean 4 formalization, including the auxiliary definitions it depends on. The Lean
proof itself is withheld (`by sorry`).

Deliverable: write a complete natural-language proof to `output/nl_proof.md`.

Requirements:

- Read the inputs with your own tools. Never modify anything under `input/`.
- Prove the stated theorem, using the Lean definitions as the authoritative meaning of every
  notion that appears in it.
- Justify every step. State which hypothesis, standard theorem, or computation licenses each
  inference, and make the overall structure (induction, contradiction, case analysis) explicit.
- Cover every case: the proof must be complete, not a sketch, and must not assume the result.
- Lean code is neither required nor forbidden; mathematical rigour is what is graded.
- English only. Finish only after `output/nl_proof.md` contains the final proof.

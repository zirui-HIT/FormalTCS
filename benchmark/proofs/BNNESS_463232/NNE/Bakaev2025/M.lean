/-
Copyright (c) 2026 Anthony Chang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Chang
-/
import Mathlib
import NNE.Max

/-!
# The M function

`M = ½(P₁ + P₂ + P₃ + P₄ + Q − R₁₃ − R₁₄ − R₂₃ − R₂₄)`;
-/

namespace NNE
/-- `P₁ = max(2x₅, x₁+x₂, 2x₁, x₁+x₃, x₁+x₄, x₃+x₄)`. -/
def P₁ (x : Fin 5 → ℝ) : ℝ :=
  MAXf ![2 * x 4, x 0 + x 1, 2 * x 0, x 0 + x 2, x 0 + x 3, x 2 + x 3]

/-- `P₂ = max(2x₅, x₁+x₂, 2x₂, x₂+x₃, x₂+x₄, x₃+x₄)`. -/
def P₂ (x : Fin 5 → ℝ) : ℝ :=
  MAXf ![2 * x 4, x 0 + x 1, 2 * x 1, x 1 + x 2, x 1 + x 3, x 2 + x 3]

/-- `P₃ = max(2x₅, x₃+x₄, 2x₃, x₃+x₁, x₃+x₂, x₁+x₂)`. -/
def P₃ (x : Fin 5 → ℝ) : ℝ :=
  MAXf ![2 * x 4, x 2 + x 3, 2 * x 2, x 2 + x 0, x 2 + x 1, x 0 + x 1]

/-- `P₄ = max(2x₅, x₃+x₄, 2x₄, x₄+x₁, x₄+x₂, x₁+x₂)`. -/
def P₄ (x : Fin 5 → ℝ) : ℝ :=
  MAXf ![2 * x 4, x 2 + x 3, 2 * x 3, x 3 + x 0, x 3 + x 1, x 0 + x 1]

/-- `Q = max(2x₅, x₁+x₂, x₃+x₄)`. -/
def Q (x : Fin 5 → ℝ) : ℝ :=
  MAXf ![2 * x 4, x 0 + x 1, x 2 + x 3]

/-- `R₁₃ = max(2x₅, x₁+x₃, x₁+x₂, x₃+x₄)`. -/
def R₁₃ (x : Fin 5 → ℝ) : ℝ :=
  MAXf ![2 * x 4, x 0 + x 2, x 0 + x 1, x 2 + x 3]

/-- `R₁₄ = max(2x₅, x₁+x₄, x₁+x₂, x₃+x₄)`. -/
def R₁₄ (x : Fin 5 → ℝ) : ℝ :=
  MAXf ![2 * x 4, x 0 + x 3, x 0 + x 1, x 2 + x 3]

/-- `R₂₃ = max(2x₅, x₂+x₃, x₁+x₂, x₃+x₄)`. -/
def R₂₃ (x : Fin 5 → ℝ) : ℝ :=
  MAXf ![2 * x 4, x 1 + x 2, x 0 + x 1, x 2 + x 3]

/-- `R₂₄ = max(2x₅, x₂+x₄, x₁+x₂, x₃+x₄)`. -/
def R₂₄ (x : Fin 5 → ℝ) : ℝ :=
  MAXf ![2 * x 4, x 1 + x 3, x 0 + x 1, x 2 + x 3]

/-- `M = ½(P₁ + P₂ + P₃ + P₄ + Q − R₁₃ − R₁₄ − R₂₃ − R₂₄)`; -/
noncomputable def M (x : Fin 5 → ℝ) : ℝ :=
  (P₁ x + P₂ x + P₃ x + P₄ x + Q x - R₁₃ x - R₁₄ x - R₂₃ x - R₂₄ x) / 2

/-! ### The core identity behind Claim 4

Twice the maximum of five reals `y₀, y₁, y₂, y₃, w` is an alternating sum of
nine maxima, each of the "block" shape `(2w ⊔ e) ⊔ ((s ⊔ t) + (u ⊔ v))`
matching a generator `T_{a+1,b+1} ∘ L` in Claim 5.  In the notation of the
paper (with `x₅ = w`), the nine terms are `P₁, P₂, P₃, P₄, Q, R₁₃, R₁₄, R₂₃,
R₂₄`. -/

set_option maxHeartbeats 1600000 in
-- the case analysis over the orderings of five reals makes `grind` exceed the default limit
/-- The nine-term decomposition of twice the maximum of five reals (Claim 4). -/
lemma max5_core_identity (w y₀ y₁ y₂ y₃ : ℝ) :
    2 * (y₀ ⊔ (y₁ ⊔ (y₂ ⊔ (y₃ ⊔ w))))
      = ((2 * w ⊔ (y₀ + y₁)) ⊔ ((y₀ ⊔ y₂) + (y₀ ⊔ y₃)))
      + ((2 * w ⊔ (y₀ + y₁)) ⊔ ((y₁ ⊔ y₂) + (y₁ ⊔ y₃)))
      + ((2 * w ⊔ (y₂ + y₃)) ⊔ ((y₂ ⊔ y₀) + (y₂ ⊔ y₁)))
      + ((2 * w ⊔ (y₂ + y₃)) ⊔ ((y₃ ⊔ y₀) + (y₃ ⊔ y₁)))
      + ((2 * w ⊔ (y₂ + y₃)) ⊔ ((y₀ ⊔ y₀) + (y₁ ⊔ y₁)))
      - ((2 * w ⊔ (y₂ + y₃)) ⊔ ((y₁ ⊔ y₂) + (y₀ ⊔ y₀)))
      - ((2 * w ⊔ (y₂ + y₃)) ⊔ ((y₁ ⊔ y₃) + (y₀ ⊔ y₀)))
      - ((2 * w ⊔ (y₂ + y₃)) ⊔ ((y₀ ⊔ y₂) + (y₁ ⊔ y₁)))
      - ((2 * w ⊔ (y₂ + y₃)) ⊔ ((y₀ ⊔ y₃) + (y₁ ⊔ y₁))) := by
  grind (splits := 200)

/-! ### Block forms of the nine functions -/

/-- `P₁` in block form. -/
lemma P₁_eq (x : Fin 5 → ℝ) :
    P₁ x = (2 * x 4 ⊔ (x 0 + x 1)) ⊔ ((x 0 ⊔ x 2) + (x 0 ⊔ x 3)) := by
  simp only [P₁, MAXf_vecCons, MAXf_single]
  grind

/-- `P₂` in block form. -/
lemma P₂_eq (x : Fin 5 → ℝ) :
    P₂ x = (2 * x 4 ⊔ (x 0 + x 1)) ⊔ ((x 1 ⊔ x 2) + (x 1 ⊔ x 3)) := by
  simp only [P₂, MAXf_vecCons, MAXf_single]
  grind

/-- `P₃` in block form. -/
lemma P₃_eq (x : Fin 5 → ℝ) :
    P₃ x = (2 * x 4 ⊔ (x 2 + x 3)) ⊔ ((x 2 ⊔ x 0) + (x 2 ⊔ x 1)) := by
  simp only [P₃, MAXf_vecCons, MAXf_single]
  grind

/-- `P₄` in block form. -/
lemma P₄_eq (x : Fin 5 → ℝ) :
    P₄ x = (2 * x 4 ⊔ (x 2 + x 3)) ⊔ ((x 3 ⊔ x 0) + (x 3 ⊔ x 1)) := by
  simp only [P₄, MAXf_vecCons, MAXf_single]
  grind

/-- `Q` in block form. -/
lemma Q_eq (x : Fin 5 → ℝ) :
    Q x = (2 * x 4 ⊔ (x 2 + x 3)) ⊔ ((x 0 ⊔ x 0) + (x 1 ⊔ x 1)) := by
  simp only [Q, MAXf_vecCons, MAXf_single]
  grind

/-- `R₁₃` in block form. -/
lemma R₁₃_eq (x : Fin 5 → ℝ) :
    R₁₃ x = (2 * x 4 ⊔ (x 2 + x 3)) ⊔ ((x 1 ⊔ x 2) + (x 0 ⊔ x 0)) := by
  simp only [R₁₃, MAXf_vecCons, MAXf_single]
  grind

/-- `R₁₄` in block form. -/
lemma R₁₄_eq (x : Fin 5 → ℝ) :
    R₁₄ x = (2 * x 4 ⊔ (x 2 + x 3)) ⊔ ((x 1 ⊔ x 3) + (x 0 ⊔ x 0)) := by
  simp only [R₁₄, MAXf_vecCons, MAXf_single]
  grind

/-- `R₂₃` in block form. -/
lemma R₂₃_eq (x : Fin 5 → ℝ) :
    R₂₃ x = (2 * x 4 ⊔ (x 2 + x 3)) ⊔ ((x 0 ⊔ x 2) + (x 1 ⊔ x 1)) := by
  simp only [R₂₃, MAXf_vecCons, MAXf_single]
  grind

/-- `R₂₄` in block form. -/
lemma R₂₄_eq (x : Fin 5 → ℝ) :
    R₂₄ x = (2 * x 4 ⊔ (x 2 + x 3)) ⊔ ((x 0 ⊔ x 3) + (x 1 ⊔ x 1)) := by
  simp only [R₂₄, MAXf_vecCons, MAXf_single]
  grind

end NNE

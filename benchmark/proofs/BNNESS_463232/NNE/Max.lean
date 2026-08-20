/-
Copyright (c) 2026 Anthony Chang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Chang
-/

import Mathlib

/-!
# The MAX function

This file defines the Max function.

The `MAXₙ(x) = max{x₁,…,xₙ}` function is the "hard" CPWL function whose
depth requirements drive every bound in the paper.
-/

namespace NNE

/-- The maximum of a nonempty vector `x : Fin (n+1) → ℝ`. -/
def MAXf {n : ℕ} (x : Fin (n + 1) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty x

/-- Unfolding lemma: `MAXf` is the `Finset.sup'` over all coordinates. -/
lemma MAXf_def {n : ℕ} (x : Fin (n + 1) → ℝ) :
    MAXf x = Finset.univ.sup' Finset.univ_nonempty x := rfl

/-- Every coordinate is bounded by the maximum. -/
lemma le_MAXf {n : ℕ} (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : x i ≤ MAXf x :=
  Finset.le_sup' x (Finset.mem_univ i)

/-- The maximum is the least upper bound of the coordinates. -/
lemma MAXf_le {n : ℕ} {x : Fin (n + 1) → ℝ} {c : ℝ} (h : ∀ i, x i ≤ c) :
    MAXf x ≤ c :=
  Finset.sup'_le _ x fun i _ => h i

/-- The maximum is attained at some coordinate. -/
lemma exists_MAXf_eq {n : ℕ} (x : Fin (n + 1) → ℝ) : ∃ i, MAXf x = x i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty x
  exact ⟨i, hi⟩

/-- `MAXf` is monotone in the pointwise order on vectors. -/
lemma MAXf_mono {n : ℕ} : Monotone (MAXf (n := n)) := fun _ y h =>
  MAXf_le fun i => (h i).trans (le_MAXf y i)

/-- The maximum of a single coordinate is that coordinate. -/
@[simp] lemma MAXf_zero (x : Fin 1 → ℝ) : MAXf x = x 0 :=
  le_antisymm (MAXf_le fun i => by fin_cases i; exact le_rfl) (le_MAXf x 0)

/-- The maximum over `Fin (n+2)` peels off the first coordinate.
This matches the recursion the paper uses to build large `MAX`s from small ones. -/
lemma MAXf_succ {n : ℕ} (x : Fin (n + 2) → ℝ) :
    MAXf x = x 0 ⊔ MAXf (fun i : Fin (n + 1) => x i.succ) := by
  apply le_antisymm
  · apply MAXf_le
    intro i
    refine Fin.cases ?_ ?_ i
    · exact le_sup_left
    · intro j
      exact le_sup_of_le_right (le_MAXf (fun i : Fin (n + 1) => x i.succ) j)
  · apply sup_le
    · exact le_MAXf x 0
    · exact MAXf_le fun j => le_MAXf x j.succ

/-- `MAXf` is continuous. -/
@[fun_prop]
lemma continuous_MAXf {n : ℕ} : Continuous (MAXf (n := n)) := by
  induction n with
  | zero =>
      have : MAXf (n := 0) = fun x : Fin 1 → ℝ => x 0 := funext MAXf_zero
      rw [this]; exact continuous_apply 0
  | succ n ih =>
      have : MAXf (n := n + 1)
          = fun x => max (x 0) (MAXf (fun i : Fin (n + 1) => x i.succ)) := by
        funext x; exact MAXf_succ x
      rw [this]
      exact (continuous_apply 0).max
        (ih.comp (continuous_pi fun i => continuous_apply i.succ))

/-! ### Evaluating `MAXf` on explicit vectors -/

/-- If `x i` dominates every coordinate then it is the maximum. -/
lemma MAXf_eq_of_le {n : ℕ} (x : Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (h : ∀ j, x j ≤ x i) : MAXf x = x i :=
  le_antisymm (MAXf_le h) (le_MAXf x i)

/-- Peeling the head off a `MAXf` of a `vecCons`. -/
lemma MAXf_vecCons {n : ℕ} (a : ℝ) (x : Fin (n + 1) → ℝ) :
    MAXf (Matrix.vecCons a x) = a ⊔ MAXf x := by
  rw [MAXf_succ]
  simp

/-- `MAXf` of a singleton vector. -/
lemma MAXf_single (a : ℝ) : MAXf ![a] = a := by
  simp

/-- `MAXf` on `Fin 5`, written as an iterated pointwise maximum. -/
lemma MAXf_five (x : Fin 5 → ℝ) :
    MAXf x = x 0 ⊔ (x 1 ⊔ (x 2 ⊔ (x 3 ⊔ x 4))) := by
  have hx : x = ![x 0, x 1, x 2, x 3, x 4] := by
    funext i; fin_cases i <;> rfl
  conv_lhs => rw [hx]
  simp only [MAXf_vecCons, MAXf_single]

/-- Explicit five-entry evaluation of `MAXf`. -/
lemma MAXf_five_explicit (a b c d e : ℝ) :
    MAXf ![a, b, c, d, e] = a ⊔ (b ⊔ (c ⊔ (d ⊔ e))) := by
  simp only [MAXf_vecCons, MAXf_single]

/-- `MAXf` of a five-entry vector whose first entry dominates. -/
lemma MAXf_dominant₀ {a b c d e : ℝ} (h1 : b ≤ a) (h2 : c ≤ a) (h3 : d ≤ a) (h4 : e ≤ a) :
    MAXf ![a, b, c, d, e] = a := by
  refine MAXf_eq_of_le _ 0 fun j => ?_
  fin_cases j <;> simp_all

/-- `MAXf` of a five-entry vector whose second entry dominates. -/
lemma MAXf_dominant₁ {a b c d e : ℝ} (h1 : a ≤ b) (h2 : c ≤ b) (h3 : d ≤ b) (h4 : e ≤ b) :
    MAXf ![a, b, c, d, e] = b := by
  refine MAXf_eq_of_le _ 1 fun j => ?_
  fin_cases j <;> simp_all

/-- `MAXf` of a five-entry vector whose third entry dominates. -/
lemma MAXf_dominant₂ {a b c d e : ℝ} (h1 : a ≤ c) (h2 : b ≤ c) (h3 : d ≤ c) (h4 : e ≤ c) :
    MAXf ![a, b, c, d, e] = c := by
  refine MAXf_eq_of_le _ 2 fun j => ?_
  fin_cases j <;> simp_all

end NNE

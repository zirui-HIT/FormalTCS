/-
Copyright (c) 2026 Anthony Chang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Chang
-/
import Mathlib
import NNE.T

/-!
# Auxiliary lemmas for the main results

Proof-specific scaffolding for `NNE.lean`:

* the `W`-decomposition and the nine generator maps behind Claim 5;
* the descent step behind Claim 6;
* the block-sum network behind Claim 7;
* the slope-jump machinery behind the one-hidden-layer lower bound.

The reusable API extracted alongside these proofs lives in `NNE.ReLU`,
`NNE.ReLUk`, `NNE.ReLUClass`, `NNE.Max`, `NNE.M` and `NNE.T`.
-/

open Topology

namespace NNE

/-! ### Evaluation lemmas for `Tval`/`T` and the `W`-decomposition (Claim 5) -/

/-- The distinguished coordinate `y_j` (for `j ≤ 3`) in the setting of Claim 5. -/
def yc (a b : ℕ) (x : Fin (4 * a + (b + 4) + 1) → ℝ) (j : ℕ) : ℝ :=
  x ⟨4 * a + b + min j 3, by omega⟩

/-- The minimum of the four distinguished coordinates. -/
noncomputable def ymin (a b : ℕ) (x : Fin (4 * a + (b + 4) + 1) → ℝ) : ℝ :=
  (yc a b x 0 ⊓ yc a b x 1) ⊓ (yc a b x 2 ⊓ yc a b x 3)

lemma ymin_le_yc (a b : ℕ) (x : Fin (4 * a + (b + 4) + 1) → ℝ) {j : ℕ} (hj : j < 4) :
    ymin a b x ≤ yc a b x j := by
  interval_cases j
  · exact inf_le_left.trans inf_le_left
  · exact inf_le_left.trans inf_le_right
  · exact inf_le_right.trans inf_le_left
  · exact inf_le_right.trans inf_le_right

/-- Restriction of `x` to the first `4a + (b+4)` coordinates. -/
def xrest (a b : ℕ) (x : Fin (4 * a + (b + 4) + 1) → ℝ) : Fin (4 * a + (b + 4)) → ℝ :=
  fun i => x (Fin.castAdd 1 i)

lemma xrest_mk (a b : ℕ) (x : Fin (4 * a + (b + 4) + 1) → ℝ) {j : ℕ}
    (hj : j < 4 * a + (b + 4)) : xrest a b x ⟨j, hj⟩ = x ⟨j, by omega⟩ := rfl

/-- `x` restricted, with the four distinguished coordinates lowered to their minimum. -/
noncomputable def xlow (a b : ℕ) (x : Fin (4 * a + (b + 4) + 1) → ℝ) :
    Fin (4 * a + (b + 4)) → ℝ :=
  fun i => if (i : ℕ) < 4 * a + b then xrest a b x i else ymin a b x

lemma xlow_low (a b : ℕ) (x : Fin (4 * a + (b + 4) + 1) → ℝ) {j : ℕ}
    (hj : j < 4 * a + b) :
    xlow a b x ⟨j, by omega⟩ = x ⟨j, by omega⟩ := by
  simp only [xlow]
  rw [if_pos hj]
  rfl

lemma xlow_y (a b : ℕ) (x : Fin (4 * a + (b + 4) + 1) → ℝ) {j : ℕ}
    (hj1 : 4 * a + b ≤ j) (hj2 : j < 4 * a + (b + 4)) :
    xlow a b x ⟨j, by omega⟩ = ymin a b x := by
  simp only [xlow]
  rw [if_neg (by omega)]

/-- The value `W`: the `T`-maximum over the blocks, the untouched extras, and
the minimum of the four distinguished coordinates. -/
noncomputable def Wval (a b : ℕ) (x : Fin (4 * a + (b + 4) + 1) → ℝ) : ℝ :=
  T a (b + 4) (xlow a b x)

/-- Splitting off the four distinguished coordinates from `T_{a,b+4}` (the
decomposition `T = y₀ ⊔ y₁ ⊔ y₂ ⊔ y₃ ⊔ W` behind Claim 5). -/
lemma T_xrest_eq (a b : ℕ) (x : Fin (4 * a + (b + 4) + 1) → ℝ) :
    T a (b + 4) (xrest a b x)
      = yc a b x 0 ⊔ (yc a b x 1 ⊔ (yc a b x 2 ⊔ (yc a b x 3 ⊔ Wval a b x))) := by
  apply le_antisymm
  · apply T_le
    intro i
    induction i using Fin.addCases with
    | left blk =>
        obtain ⟨iv, hiv⟩ := blk
        have hW : Tval a (b + 4) (xlow a b x) (Fin.castAdd (b + 4) ⟨iv, hiv⟩) ≤ Wval a b x :=
          Tval_le_T _ _ _ _
        rw [Tval_castAdd a (b + 4) (xlow a b x) hiv] at hW
        rw [Tval_castAdd a (b + 4) (xrest a b x) hiv]
        rw [xrest_mk, xrest_mk, xrest_mk, xrest_mk]
        rw [xlow_low a b x (by omega), xlow_low a b x (by omega),
          xlow_low a b x (by omega), xlow_low a b x (by omega)] at hW
        exact le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_right
          (le_sup_of_le_right hW)))
    | right ex =>
        obtain ⟨ev, hev⟩ := ex
        rw [Tval_natAdd a (b + 4) (xrest a b x) hev, xrest_mk]
        by_cases hex : ev < b
        · have hW : Tval a (b + 4) (xlow a b x) (Fin.natAdd a ⟨ev, hev⟩) ≤ Wval a b x :=
            Tval_le_T _ _ _ _
          rw [Tval_natAdd a (b + 4) (xlow a b x) hev, xlow_low a b x (by omega)] at hW
          exact le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_right
            (le_sup_of_le_right hW)))
        · -- one of the four distinguished coordinates
          have h4 : ev = b ∨ ev = b + 1 ∨ ev = b + 2 ∨ ev = b + 3 := by omega
          rcases h4 with h | h | h | h
          · exact le_sup_of_le_left (le_of_eq (congrArg x (Fin.mk_eq_mk.mpr (by omega))))
          · exact le_sup_of_le_right (le_sup_of_le_left
              (le_of_eq (congrArg x (Fin.mk_eq_mk.mpr (by omega)))))
          · exact le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_left
              (le_of_eq (congrArg x (Fin.mk_eq_mk.mpr (by omega))))))
          · exact le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_right
              (le_sup_of_le_left (le_of_eq (congrArg x (Fin.mk_eq_mk.mpr (by omega)))))))
  · -- each of the five pieces is at most the left-hand side
    have hy : ∀ j : ℕ, j < 4 → yc a b x j ≤ T a (b + 4) (xrest a b x) := by
      intro j hj
      have hle := Tval_le_T a (b + 4) (xrest a b x) (Fin.natAdd a ⟨b + j, by omega⟩)
      rw [Tval_natAdd a (b + 4) (xrest a b x) (by omega), xrest_mk] at hle
      exact le_trans (le_of_eq (congrArg x (Fin.mk_eq_mk.mpr (by omega)))) hle
    refine sup_le (hy 0 (by omega)) (sup_le (hy 1 (by omega)) (sup_le (hy 2 (by omega))
      (sup_le (hy 3 (by omega)) ?_)))
    -- W ≤ T (xrest x)
    apply T_le
    intro i
    induction i using Fin.addCases with
    | left blk =>
        obtain ⟨iv, hiv⟩ := blk
        have hle : Tval a (b + 4) (xrest a b x) (Fin.castAdd (b + 4) ⟨iv, hiv⟩)
            ≤ T a (b + 4) (xrest a b x) := Tval_le_T _ _ _ _
        rw [Tval_castAdd a (b + 4) (xrest a b x) hiv] at hle
        rw [Tval_castAdd a (b + 4) (xlow a b x) hiv]
        rw [xrest_mk, xrest_mk, xrest_mk, xrest_mk] at hle
        rw [xlow_low a b x (by omega), xlow_low a b x (by omega),
          xlow_low a b x (by omega), xlow_low a b x (by omega)]
        exact hle
    | right ex =>
        obtain ⟨ev, hev⟩ := ex
        rw [Tval_natAdd a (b + 4) (xlow a b x) hev]
        by_cases hex : ev < b
        · have hle : Tval a (b + 4) (xrest a b x) (Fin.natAdd a ⟨ev, hev⟩)
              ≤ T a (b + 4) (xrest a b x) := Tval_le_T _ _ _ _
          rw [Tval_natAdd a (b + 4) (xrest a b x) hev, xrest_mk] at hle
          rw [xlow_low a b x (by omega)]
          exact hle
        · rw [xlow_y a b x (by omega) (by omega)]
          refine le_trans (ymin_le_yc a b x (by omega : (0 : ℕ) < 4)) ?_
          exact hy 0 (by omega)

/-! ### The Claim-5 generators -/

/-- The linear map defining a Claim-5 generator: original blocks and extras
doubled, one new block `(s, t, u, v)`, one new extra `e`. -/
noncomputable def Lgen (a b : ℕ) (s t u v e : (Fin (4 * a + (b + 4) + 1) → ℝ) →ₗ[ℝ] ℝ) :
    (Fin (4 * a + (b + 4) + 1) → ℝ) →ₗ[ℝ] (Fin (4 * (a + 1) + (b + 1)) → ℝ) :=
  LinearMap.pi fun j =>
    if h1 : (j : ℕ) < 4 * a then (2 : ℝ) • projₗ ⟨(j : ℕ), by omega⟩
    else if h2 : (j : ℕ) = 4 * a then s
    else if h3 : (j : ℕ) = 4 * a + 1 then t
    else if h4 : (j : ℕ) = 4 * a + 2 then u
    else if h5 : (j : ℕ) = 4 * a + 3 then v
    else if h6 : (j : ℕ) < 4 * (a + 1) + b then (2 : ℝ) • projₗ ⟨(j : ℕ) - 4, by omega⟩
    else e

section LgenEval

variable (a b : ℕ) (s t u v e : (Fin (4 * a + (b + 4) + 1) → ℝ) →ₗ[ℝ] ℝ)
  (x : Fin (4 * a + (b + 4) + 1) → ℝ)

lemma Lgen_low {J : ℕ} (hJ : J < 4 * a) :
    Lgen a b s t u v e x ⟨J, by omega⟩ = 2 * x ⟨J, by omega⟩ := by
  simp only [Lgen, LinearMap.pi_apply]
  rw [dif_pos hJ]
  rfl

lemma Lgen_s : Lgen a b s t u v e x ⟨4 * a, by omega⟩ = s x := by
  simp only [Lgen, LinearMap.pi_apply]
  rw [dif_neg (show ¬(4 * a < 4 * a) by omega)]
  rfl

lemma Lgen_t : Lgen a b s t u v e x ⟨4 * a + 1, by omega⟩ = t x := by
  simp only [Lgen, LinearMap.pi_apply]
  rw [dif_neg (show ¬(4 * a + 1 < 4 * a) by omega),
    dif_neg (show ¬(4 * a + 1 = 4 * a) by omega)]
  rfl

lemma Lgen_u : Lgen a b s t u v e x ⟨4 * a + 2, by omega⟩ = u x := by
  simp only [Lgen, LinearMap.pi_apply]
  rw [dif_neg (show ¬(4 * a + 2 < 4 * a) by omega),
    dif_neg (show ¬(4 * a + 2 = 4 * a) by omega),
    dif_neg (show ¬(4 * a + 2 = 4 * a + 1) by omega)]
  rfl

lemma Lgen_v : Lgen a b s t u v e x ⟨4 * a + 3, by omega⟩ = v x := by
  simp only [Lgen, LinearMap.pi_apply]
  rw [dif_neg (show ¬(4 * a + 3 < 4 * a) by omega),
    dif_neg (show ¬(4 * a + 3 = 4 * a) by omega),
    dif_neg (show ¬(4 * a + 3 = 4 * a + 1) by omega),
    dif_neg (show ¬(4 * a + 3 = 4 * a + 2) by omega)]
  rfl

lemma Lgen_z {J : ℕ} (hJ : J < b) :
    Lgen a b s t u v e x ⟨4 * (a + 1) + J, by omega⟩ = 2 * x ⟨4 * a + J, by omega⟩ := by
  simp only [Lgen, LinearMap.pi_apply]
  rw [dif_neg (show ¬(4 * (a + 1) + J < 4 * a) by omega),
    dif_neg (show ¬(4 * (a + 1) + J = 4 * a) by omega),
    dif_neg (show ¬(4 * (a + 1) + J = 4 * a + 1) by omega),
    dif_neg (show ¬(4 * (a + 1) + J = 4 * a + 2) by omega),
    dif_neg (show ¬(4 * (a + 1) + J = 4 * a + 3) by omega),
    dif_pos (show 4 * (a + 1) + J < 4 * (a + 1) + b by omega)]
  change (2 : ℝ) * x _ = 2 * x _
  exact congrArg (fun r => 2 * r) (congrArg x (Fin.mk_eq_mk.mpr (by omega)))

lemma Lgen_e : Lgen a b s t u v e x ⟨4 * (a + 1) + b, by omega⟩ = e x := by
  simp only [Lgen, LinearMap.pi_apply]
  rw [dif_neg (show ¬(4 * (a + 1) + b < 4 * a) by omega),
    dif_neg (show ¬(4 * (a + 1) + b = 4 * a) by omega),
    dif_neg (show ¬(4 * (a + 1) + b = 4 * a + 1) by omega),
    dif_neg (show ¬(4 * (a + 1) + b = 4 * a + 2) by omega),
    dif_neg (show ¬(4 * (a + 1) + b = 4 * a + 3) by omega),
    dif_neg (show ¬(4 * (a + 1) + b < 4 * (a + 1) + b) by omega)]

end LgenEval

/-- Evaluation of a Claim-5 generator: `T_{a+1,b+1} ∘ Lgen` is the maximum of
`2W`, the new extra `e`, and the new block `(s ⊔ t) + (u ⊔ v)`. -/
lemma gen_eval (a b : ℕ) (x : Fin (4 * a + (b + 4) + 1) → ℝ)
    (s t u v e : (Fin (4 * a + (b + 4) + 1) → ℝ) →ₗ[ℝ] ℝ)
    (he : 2 * ymin a b x ≤ e x) :
    T (a + 1) (b + 1) (Lgen a b s t u v e x)
      = (2 * Wval a b x ⊔ e x) ⊔ ((s x ⊔ t x) + (u x ⊔ v x)) := by
  apply le_antisymm
  · apply T_le
    intro i
    induction i using Fin.addCases with
    | left blk =>
        obtain ⟨iv, hiv⟩ := blk
        rw [Tval_castAdd (a + 1) (b + 1) _ hiv]
        by_cases hia : iv < a
        · rw [Lgen_low a b s t u v e x (show 4 * iv < 4 * a by omega),
            Lgen_low a b s t u v e x (show 4 * iv + 1 < 4 * a by omega),
            Lgen_low a b s t u v e x (show 4 * iv + 2 < 4 * a by omega),
            Lgen_low a b s t u v e x (show 4 * iv + 3 < 4 * a by omega)]
          have hW := le_two_mul_T a (b + 4) (xlow a b x) (Fin.castAdd (b + 4) ⟨iv, hia⟩)
          rw [Tval_castAdd a (b + 4) (xlow a b x) hia] at hW
          rw [xlow_low a b x (by omega), xlow_low a b x (by omega),
            xlow_low a b x (by omega), xlow_low a b x (by omega)] at hW
          rw [mul_add, mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
            mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)] at hW
          exact le_sup_of_le_left (le_sup_of_le_left hW)
        · have hia' : iv = a := by omega
          subst hia'
          rw [Lgen_s, Lgen_t, Lgen_u, Lgen_v]
          exact le_sup_right
    | right ex =>
        obtain ⟨ev, hev⟩ := ex
        rw [Tval_natAdd (a + 1) (b + 1) _ hev]
        by_cases heb : ev < b
        · rw [Lgen_z a b s t u v e x heb]
          have hW := le_two_mul_T a (b + 4) (xlow a b x) (Fin.natAdd a ⟨ev, by omega⟩)
          rw [Tval_natAdd a (b + 4) (xlow a b x) (by omega),
            xlow_low a b x (by omega)] at hW
          exact le_sup_of_le_left (le_sup_of_le_left hW)
        · have heb' : ev = b := by omega
          subst heb'
          rw [Lgen_e]
          exact le_sup_of_le_left le_sup_right
  · refine sup_le (sup_le ?_ ?_) ?_
    · -- `2W` is at most the generator value
      apply two_mul_T_le
      intro i
      induction i using Fin.addCases with
      | left blk =>
          obtain ⟨iv, hiv⟩ := blk
          rw [Tval_castAdd a (b + 4) _ hiv]
          rw [xlow_low a b x (by omega), xlow_low a b x (by omega),
            xlow_low a b x (by omega), xlow_low a b x (by omega)]
          have hle := Tval_le_T (a + 1) (b + 1) (Lgen a b s t u v e x)
            (Fin.castAdd (b + 1) ⟨iv, by omega⟩)
          rw [Tval_castAdd (a + 1) (b + 1) _ (show iv < a + 1 by omega)] at hle
          rw [Lgen_low a b s t u v e x (show 4 * iv < 4 * a by omega),
            Lgen_low a b s t u v e x (show 4 * iv + 1 < 4 * a by omega),
            Lgen_low a b s t u v e x (show 4 * iv + 2 < 4 * a by omega),
            Lgen_low a b s t u v e x (show 4 * iv + 3 < 4 * a by omega)] at hle
          rw [mul_add, mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
            mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
          exact hle
      | right ex =>
          obtain ⟨ev, hev⟩ := ex
          rw [Tval_natAdd a (b + 4) _ hev]
          by_cases heb : ev < b
          · rw [xlow_low a b x (by omega)]
            have hle := Tval_le_T (a + 1) (b + 1) (Lgen a b s t u v e x)
              (Fin.natAdd (a + 1) ⟨ev, by omega⟩)
            rw [Tval_natAdd (a + 1) (b + 1) _ (show ev < b + 1 by omega),
              Lgen_z a b s t u v e x heb] at hle
            exact hle
          · rw [xlow_y a b x (by omega) (by omega)]
            refine le_trans he ?_
            have hle := Tval_le_T (a + 1) (b + 1) (Lgen a b s t u v e x)
              (Fin.natAdd (a + 1) ⟨b, by omega⟩)
            rw [Tval_natAdd (a + 1) (b + 1) _ (show b < b + 1 by omega), Lgen_e] at hle
            exact hle
    · -- the new extra is at most the generator value
      have hle := Tval_le_T (a + 1) (b + 1) (Lgen a b s t u v e x)
        (Fin.natAdd (a + 1) ⟨b, by omega⟩)
      rw [Tval_natAdd (a + 1) (b + 1) _ (show b < b + 1 by omega), Lgen_e] at hle
      exact hle
    · -- the new block is at most the generator value
      have hle := Tval_le_T (a + 1) (b + 1) (Lgen a b s t u v e x)
        (Fin.castAdd (b + 1) ⟨a, by omega⟩)
      rw [Tval_castAdd (a + 1) (b + 1) _ (show a < a + 1 by omega)] at hle
      rw [Lgen_s, Lgen_t, Lgen_u, Lgen_v] at hle
      exact hle

/-! ### Functionals for the Claim-5 generators -/

/-- The linear functional extracting the distinguished coordinate `y_j`. -/
def yproj (a b : ℕ) (j : ℕ) : (Fin (4 * a + (b + 4) + 1) → ℝ) →ₗ[ℝ] ℝ :=
  projₗ ⟨4 * a + b + min j 3, by omega⟩

lemma yproj_apply (a b : ℕ) (x : Fin (4 * a + (b + 4) + 1) → ℝ) (j : ℕ) :
    yproj a b j x = yc a b x j := rfl

lemma yproj_add_apply (a b : ℕ) (x : Fin (4 * a + (b + 4) + 1) → ℝ) (i j : ℕ) :
    (yproj a b i + yproj a b j) x = yc a b x i + yc a b x j := rfl

lemma two_ymin_le_add (a b : ℕ) (x : Fin (4 * a + (b + 4) + 1) → ℝ) {i j : ℕ}
    (hi : i < 4) (hj : j < 4) :
    2 * ymin a b x ≤ (yproj a b i + yproj a b j) x := by
  have h1 := ymin_le_yc a b x hi
  have h2 := ymin_le_yc a b x hj
  change 2 * ymin a b x ≤ yc a b x i + yc a b x j
  linarith

/-! ### From `Tspace` membership to `ReLUClass` membership (Claim 6) -/

/-- The class-level step behind Claim 6: computability of `T_{a+1,b+1}` gives
computability of `T_{a,b+4}` at the same depth, given Claim 5. -/
lemma step_class_of {a b k : ℕ}
    (hc5 : (fun x : Fin (4 * a + (b + 4) + 1) → ℝ =>
        T a (b + 4) (fun i => x (Fin.castAdd 1 i)))
      ∈ Tspace (a + 1) (b + 1) (4 * a + (b + 4) + 1))
    (h : T (a + 1) (b + 1) ∈ ReLUClass (4 * (a + 1) + (b + 1)) k) :
    T a (b + 4) ∈ ReLUClass (4 * a + (b + 4)) k := by
  have hres : (fun x : Fin (4 * a + (b + 4) + 1) → ℝ =>
      T a (b + 4) (fun i => x (Fin.castAdd 1 i))) ∈ ReLUClass (4 * a + (b + 4) + 1) k :=
    Tspace_subset_ReLUClass h hc5
  have hcomp := (mem_ReLUClass.mp hres).comp_affine_right
    ((extZero (4 * a + (b + 4))).toAffineMap)
  refine mem_ReLUClass.mpr ?_
  have e : (fun x' => (fun x (_ : Fin 1) => T a (b + 4) (fun i => x (Fin.castAdd 1 i)))
        ((extZero (4 * a + (b + 4))).toAffineMap x'))
      = fun x' (_ : Fin 1) => T a (b + 4) x' := by
    funext x' j
    change T a (b + 4) (fun i => extZero (4 * a + (b + 4)) x' (Fin.castAdd 1 i)) = T a (b + 4) x'
    congr 1
    funext i
    exact extZero_castAdd _ x' i
  rwa [e] at hcomp

/-- `step_class_of`, with the numerology generalized so that it can be applied
inside inductions without dependent rewriting. -/
lemma step_class_of' {a b a' b' B k : ℕ} [NeZero (a' + b')] [NeZero (a + B)]
    (ha : a' = a + 1) (hb : b' = b + 1) (hB : B = b + 4)
    (hc5 : (fun x : Fin (4 * a + (b + 4) + 1) → ℝ =>
        T a (b + 4) (fun i => x (Fin.castAdd 1 i)))
      ∈ Tspace (a + 1) (b + 1) (4 * a + (b + 4) + 1))
    (h : T a' b' ∈ ReLUClass (4 * a' + b') k) :
    T a B ∈ ReLUClass (4 * a + B) k := by
  subst ha
  subst hb
  subst hB
  exact step_class_of hc5 h

/-! ### The block-sum network (Claim 7) and the `MAXf` bridges -/

/-- First layer of the block-sum network: per block the differences `u - v` and
`w - s`, then all coordinates positively and negatively. -/
noncomputable def bmA₁ (a : ℕ) : (Fin (4 * a + 2) → ℝ) →ₗ[ℝ] (Fin (10 * a + 4) → ℝ) :=
  LinearMap.pi fun j =>
    if h1 : (j : ℕ) < a then
      projₗ ⟨4 * (j : ℕ), by omega⟩ - projₗ ⟨4 * (j : ℕ) + 1, by omega⟩
    else if h2 : (j : ℕ) < 2 * a then
      projₗ ⟨4 * ((j : ℕ) - a) + 2, by omega⟩ - projₗ ⟨4 * ((j : ℕ) - a) + 3, by omega⟩
    else if h3 : (j : ℕ) < 2 * a + (4 * a + 2) then projₗ ⟨(j : ℕ) - 2 * a, by omega⟩
    else -projₗ ⟨(j : ℕ) - (6 * a + 2), by omega⟩

lemma bmA₁_diff1 (a : ℕ) (x : Fin (4 * a + 2) → ℝ) {j : ℕ} (hj : j < a) :
    bmA₁ a x ⟨j, by omega⟩ = x ⟨4 * j, by omega⟩ - x ⟨4 * j + 1, by omega⟩ := by
  simp only [bmA₁, LinearMap.pi_apply]
  rw [dif_pos hj]
  rfl

lemma bmA₁_diff2 (a : ℕ) (x : Fin (4 * a + 2) → ℝ) {j : ℕ} (hj : j < a) :
    bmA₁ a x ⟨a + j, by omega⟩ = x ⟨4 * j + 2, by omega⟩ - x ⟨4 * j + 3, by omega⟩ := by
  simp only [bmA₁, LinearMap.pi_apply]
  rw [dif_neg (show ¬(a + j < a) by omega), dif_pos (show a + j < 2 * a by omega)]
  change x _ - x _ = _
  rw [congrArg x (Fin.mk_eq_mk.mpr (show 4 * ((a + j) - a) + 2 = 4 * j + 2 by omega)),
    congrArg x (Fin.mk_eq_mk.mpr (show 4 * ((a + j) - a) + 3 = 4 * j + 3 by omega))]

lemma bmA₁_pos (a : ℕ) (x : Fin (4 * a + 2) → ℝ) {j : ℕ} (hj : j < 4 * a + 2) :
    bmA₁ a x ⟨2 * a + j, by omega⟩ = x ⟨j, by omega⟩ := by
  simp only [bmA₁, LinearMap.pi_apply]
  rw [dif_neg (show ¬(2 * a + j < a) by omega), dif_neg (show ¬(2 * a + j < 2 * a) by omega),
    dif_pos (show 2 * a + j < 2 * a + (4 * a + 2) by omega)]
  change x _ = _
  rw [congrArg x (Fin.mk_eq_mk.mpr (show (2 * a + j) - 2 * a = j by omega))]

lemma bmA₁_neg (a : ℕ) (x : Fin (4 * a + 2) → ℝ) {j : ℕ} (hj : j < 4 * a + 2) :
    bmA₁ a x ⟨6 * a + 2 + j, by omega⟩ = -x ⟨j, by omega⟩ := by
  simp only [bmA₁, LinearMap.pi_apply]
  rw [dif_neg (show ¬(6 * a + 2 + j < a) by omega),
    dif_neg (show ¬(6 * a + 2 + j < 2 * a) by omega),
    dif_neg (show ¬(6 * a + 2 + j < 2 * a + (4 * a + 2)) by omega)]
  change -(x _) = _
  rw [congrArg x (Fin.mk_eq_mk.mpr (show (6 * a + 2 + j) - (6 * a + 2) = j by omega))]

/-- Second layer of the block-sum network. -/
noncomputable def bmA₂ (a : ℕ) :
    (Fin (10 * a + 4) → ℝ) →ₗ[ℝ] (Fin (4 * 0 + (a + 2)) → ℝ) :=
  LinearMap.pi fun io =>
    if h : (io : ℕ) < a then
      projₗ ⟨(io : ℕ), by omega⟩ + projₗ ⟨a + (io : ℕ), by omega⟩
        + (projₗ ⟨2 * a + (4 * (io : ℕ) + 1), by omega⟩
            - projₗ ⟨6 * a + 2 + (4 * (io : ℕ) + 1), by omega⟩)
        + (projₗ ⟨2 * a + (4 * (io : ℕ) + 3), by omega⟩
            - projₗ ⟨6 * a + 2 + (4 * (io : ℕ) + 3), by omega⟩)
    else
      projₗ ⟨2 * a + (4 * a + ((io : ℕ) - a)), by omega⟩
        - projₗ ⟨6 * a + 2 + (4 * a + ((io : ℕ) - a)), by omega⟩

/-- Block coordinates of the block-sum network compute the `Tval` block values. -/
lemma bm_block (a : ℕ) (x : Fin (4 * a + 2) → ℝ) {J : ℕ} (hJ : J < a)
    (hJ' : J < 4 * 0 + (a + 2)) :
    bmA₂ a (reluV (bmA₁ a x)) ⟨J, hJ'⟩ = Tval a 2 x (Fin.castAdd 2 ⟨J, hJ⟩) := by
  rw [Tval_castAdd a 2 x hJ]
  simp only [bmA₂, LinearMap.pi_apply]
  rw [dif_pos (show J < a from hJ)]
  change reluV (bmA₁ a x) _ + reluV (bmA₁ a x) _
      + (reluV (bmA₁ a x) _ - reluV (bmA₁ a x) _)
      + (reluV (bmA₁ a x) _ - reluV (bmA₁ a x) _) = _
  simp only [reluV_apply]
  rw [bmA₁_diff1 a x hJ, bmA₁_diff2 a x hJ,
    bmA₁_pos a x (j := 4 * J + 1) (by omega), bmA₁_neg a x (j := 4 * J + 1) (by omega),
    bmA₁_pos a x (j := 4 * J + 3) (by omega), bmA₁_neg a x (j := 4 * J + 3) (by omega)]
  have g1 := relu_max_gadget (x ⟨4 * J, by omega⟩) (x ⟨4 * J + 1, by omega⟩)
  have g2 := relu_max_gadget (x ⟨4 * J + 2, by omega⟩) (x ⟨4 * J + 3, by omega⟩)
  linarith

/-- Extra coordinates of the block-sum network pass the extras through. -/
lemma bm_extra (a : ℕ) (x : Fin (4 * a + 2) → ℝ) {J : ℕ} (h1 : a ≤ J) (h2 : J < a + 2)
    (hJ' : J < 4 * 0 + (a + 2)) :
    bmA₂ a (reluV (bmA₁ a x)) ⟨J, hJ'⟩ = Tval a 2 x (Fin.natAdd a ⟨J - a, by omega⟩) := by
  rw [Tval_natAdd a 2 x (show J - a < 2 by omega)]
  simp only [bmA₂, LinearMap.pi_apply]
  rw [dif_neg (show ¬(J < a) by omega)]
  change reluV (bmA₁ a x) _ - reluV (bmA₁ a x) _ = _
  simp only [reluV_apply]
  rw [bmA₁_pos a x (j := 4 * a + (J - a)) (by omega),
    bmA₁_neg a x (j := 4 * a + (J - a)) (by omega)]
  exact relu_sub_relu_neg _

/-- The block-sum network turns `T_{0,a+2}` into `T_{a,2}`. -/
lemma T_bm_eq (a : ℕ) [NeZero (0 + (a + 2))] [NeZero (a + 2)] (x : Fin (4 * a + 2) → ℝ) :
    T 0 (a + 2) (bmA₂ a (reluV (bmA₁ a x))) = T a 2 x := by
  apply le_antisymm
  · apply T_le
    intro i
    induction i using Fin.addCases with
    | left blk => exact blk.elim0
    | right ex =>
        obtain ⟨ev, hev⟩ := ex
        rw [Tval_natAdd 0 (a + 2) _ hev]
        by_cases heb : ev < a
        · rw [bm_block a x (show 4 * 0 + ev < a by omega) _]
          exact Tval_le_T _ _ _ _
        · rw [bm_extra a x (show a ≤ 4 * 0 + ev by omega) (show 4 * 0 + ev < a + 2 by omega) _]
          exact Tval_le_T _ _ _ _
  · apply T_le
    intro i
    induction i using Fin.addCases with
    | left blk =>
        obtain ⟨iv, hiv⟩ := blk
        have hle := Tval_le_T 0 (a + 2) (bmA₂ a (reluV (bmA₁ a x)))
          (Fin.natAdd 0 ⟨iv, by omega⟩)
        rw [Tval_natAdd 0 (a + 2) _ (show iv < a + 2 by omega)] at hle
        rw [bm_block a x (show 4 * 0 + iv < a by omega) _] at hle
        refine le_trans (le_of_eq ?_) hle
        exact congrArg (Tval a 2 x) (congrArg (Fin.castAdd 2) (Fin.mk_eq_mk.mpr (by omega))).symm
    | right ex =>
        obtain ⟨ev, hev⟩ := ex
        have hle := Tval_le_T 0 (a + 2) (bmA₂ a (reluV (bmA₁ a x)))
          (Fin.natAdd 0 ⟨a + ev, by omega⟩)
        rw [Tval_natAdd 0 (a + 2) _ (show a + ev < a + 2 by omega)] at hle
        rw [bm_extra a x (show a ≤ 4 * 0 + (a + ev) by omega)
          (show 4 * 0 + (a + ev) < a + 2 by omega) _] at hle
        refine le_trans (le_of_eq ?_) hle
        exact congrArg (Tval a 2 x) (congrArg (Fin.natAdd a) (Fin.mk_eq_mk.mpr (by omega))).symm

/-- General form of Claim 7: one extra layer converts `T_{0,a+2}` into `T_{a,2}`. -/
lemma claim7_general (a k : ℕ) [NeZero (0 + (a + 2))] [NeZero (a + 2)]
    (h : Tcomputable 0 (a + 2) k) : Tcomputable a 2 (k + 1) := by
  have hBM : ReLUk 1 (fun x : Fin (4 * a + 2) → ℝ => bmA₂ a (reluV (bmA₁ a x))) := by
    have key := ReLUk.layer (ReLUk.affine (bmA₁ a).toAffineMap) (bmA₂ a).toAffineMap
    exact key
  have hcomp := ReLUk.comp (mem_ReLUClass.mp h) hBM
  rw [Nat.add_comm 1 k] at hcomp
  refine mem_ReLUClass.mpr ?_
  have e : (fun x : Fin (4 * a + 2) → ℝ =>
        (fun y (_ : Fin 1) => T 0 (a + 2) y) (bmA₂ a (reluV (bmA₁ a x))))
      = fun x (_ : Fin 1) => T a 2 x := by
    funext x j
    exact T_bm_eq a x
  rwa [e] at hcomp

/-! ### The one-hidden-layer lower bound (Proposition 3) -/

/-- The slope-jump functional of a one-hidden-layer network at `z` along `v`. -/
noncomputable def slopeJump {n p : ℕ} (A : (Fin n → ℝ) →ᵃ[ℝ] (Fin p → ℝ))
    (B : (Fin p → ℝ) →ᵃ[ℝ] (Fin 1 → ℝ)) (z v : Fin n → ℝ) : ℝ :=
  B.linear (fun i => if A z i = 0 then |A.linear v i| else 0) 0

/-- Second differences of an affine map are linear-map values. -/
lemma affine_second {p : ℕ} (B : (Fin p → ℝ) →ᵃ[ℝ] (Fin 1 → ℝ)) (y₁ y₂ y₃ : Fin p → ℝ) :
    B y₁ 0 + B y₂ 0 - 2 * B y₃ 0 = B.linear (y₁ + y₂ - (2 : ℝ) • y₃) 0 := by
  have h1 : B.linear (y₁ - y₃) = B y₁ - B y₃ := B.linearMap_vsub y₁ y₃
  have h2 : B.linear (y₂ - y₃) = B y₂ - B y₃ := B.linearMap_vsub y₂ y₃
  have e : y₁ + y₂ - (2 : ℝ) • y₃ = (y₁ - y₃) + (y₂ - y₃) := by
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, map_add, h1, h2]
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- The second-difference formula for one-hidden-layer networks: for small
`ε > 0`, the symmetric second difference along `v` is exactly `ε` times the
slope jump. -/
lemma net_second_diff {n p : ℕ} (A : (Fin n → ℝ) →ᵃ[ℝ] (Fin p → ℝ))
    (B : (Fin p → ℝ) →ᵃ[ℝ] (Fin 1 → ℝ)) (z v : Fin n → ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      B (reluV (A (z + ε • v))) 0 + B (reluV (A (z - ε • v))) 0
        - 2 * B (reluV (A z)) 0 = ε * slopeJump A B z v := by
  have hcomp : ∀ i : Fin p, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      relu (A z i + ε * A.linear v i) + relu (A z i - ε * A.linear v i)
        - 2 * relu (A z i) = ε * (if A z i = 0 then |A.linear v i| else 0) := by
    intro i
    by_cases hz : A z i = 0
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : ε ∈ Set.Ioi (0 : ℝ))
      rw [if_pos hz, hz]
      rw [show (0 : ℝ) + ε * A.linear v i = ε * A.linear v i by ring,
        show (0 : ℝ) - ε * A.linear v i = -(ε * A.linear v i) by ring]
      rw [relu_add_relu_neg, relu_zero, abs_mul, abs_of_pos hε]
      ring
    · filter_upwards [Ioo_mem_nhdsGT
        (show (0 : ℝ) < |A z i| / (|A.linear v i| + 1) from by positivity)] with ε hε
      obtain ⟨hε0, hεlt⟩ := hε
      rw [if_neg hz, mul_zero]
      apply relu_second_diff_of_abs_le
      rw [abs_mul, abs_of_pos hε0]
      have hpos : (0 : ℝ) < |A.linear v i| + 1 := by positivity
      have h2 : ε * (|A.linear v i| + 1) < |A z i| := (lt_div_iff₀ hpos).mp hεlt
      nlinarith [abs_nonneg (A.linear v i)]
  filter_upwards [Filter.eventually_all.mpr hcomp] with ε hall
  have hvec : reluV (A (z + ε • v)) + reluV (A (z - ε • v)) - (2 : ℝ) • reluV (A z)
      = ε • fun i => if A z i = 0 then |A.linear v i| else 0 := by
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, reluV_apply, smul_eq_mul,
      affine_apply_add_smul, affine_apply_sub_smul]
    exact hall i
  rw [affine_second, hvec, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul, slopeJump]

end NNE

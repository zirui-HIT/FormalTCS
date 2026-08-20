/-
Copyright (c) 2026 Anthony Chang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Chang
-/
import Mathlib
import NNE.Max
import NNE.ReLUClass

/-!
# The `T_{a,b}` function.

`T_{a,b} : ℝ^{4a+b} → ℝ` is the maximum of `a` "block" terms
`max(x_{4i-3},x_{4i-2}) + max(x_{4i-1},x_{4i})` and `b` extra coordinates.
`𝒯_{a,b}` (`Tspace`) is the span of the functions `T_{a,b} ∘ L`, `L` linear.
-/

namespace NNE

/-- Value vector: the `a` block terms `max(x_{4i},x_{4i+1}) + max(x_{4i+2},x_{4i+3})`
(0-indexed) followed by the `b` extra coordinates `x_{4a+j}`. -/
def Tval (a b : ℕ) (x : Fin (4 * a + b) → ℝ) : Fin (a + b) → ℝ :=
  Fin.addCases
    (fun i : Fin a =>
      max (x ⟨4 * i, by omega⟩) (x ⟨4 * i + 1, by omega⟩)
        + max (x ⟨4 * i + 2, by omega⟩) (x ⟨4 * i + 3, by omega⟩))
    (fun j : Fin b => x ⟨4 * a + j, by omega⟩)

/-- `T_{a,b} : ℝ^{4a+b} → ℝ`, the maximum of the `a` block terms and `b` extra args. -/
noncomputable def T (a b : ℕ) [NeZero (a + b)] (x : Fin (4 * a + b) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (Tval a b x)

/-- `𝒯_{a,b}` on ambient dimension `N`: the span of the functions `T_{a,b} ∘ L`
for linear `L : ℝ^N → ℝ^{4a+b}`. -/
noncomputable def Tspace (a b N : ℕ) [NeZero (a + b)] :
    Submodule ℝ ((Fin N → ℝ) → ℝ) :=
  Submodule.span ℝ
    {g | ∃ L : (Fin N → ℝ) →ₗ[ℝ] (Fin (4 * a + b) → ℝ), g = fun x => T a b (L x)}

/-- `T_{a,b}` is computable with `k` hidden layers (note `T_{0,m} = MAX_m`). -/
def Tcomputable (a b k : ℕ) [NeZero (a + b)] : Prop :=
  T a b ∈ ReLUClass (4 * a + b) k

/-! ### Evaluation and bounds -/

lemma Tval_castAdd (a b : ℕ) (x : Fin (4 * a + b) → ℝ) {i : ℕ} (hi : i < a) :
    Tval a b x (Fin.castAdd b ⟨i, hi⟩)
      = max (x ⟨4 * i, by omega⟩) (x ⟨4 * i + 1, by omega⟩)
        + max (x ⟨4 * i + 2, by omega⟩) (x ⟨4 * i + 3, by omega⟩) :=
  Fin.addCases_left _

lemma Tval_natAdd (a b : ℕ) (x : Fin (4 * a + b) → ℝ) {j : ℕ} (hj : j < b) :
    Tval a b x (Fin.natAdd a ⟨j, hj⟩) = x ⟨4 * a + j, by omega⟩ :=
  Fin.addCases_right _

lemma Tval_le_T (a b : ℕ) [NeZero (a + b)] (x : Fin (4 * a + b) → ℝ) (i : Fin (a + b)) :
    Tval a b x i ≤ T a b x :=
  Finset.le_sup' _ (Finset.mem_univ i)

lemma T_le {a b : ℕ} [NeZero (a + b)] {x : Fin (4 * a + b) → ℝ} {c : ℝ}
    (h : ∀ i, Tval a b x i ≤ c) : T a b x ≤ c :=
  Finset.sup'_le _ _ fun i _ => h i

lemma two_mul_T (a b : ℕ) [NeZero (a + b)] (x : Fin (4 * a + b) → ℝ) :
    2 * T a b x = Finset.univ.sup' Finset.univ_nonempty (fun i => 2 * Tval a b x i) :=
  Finset.apply_sup'_eq_sup'_comp _ (fun t => 2 * t) fun p q =>
    mul_max_of_nonneg p q (by norm_num : (0 : ℝ) ≤ 2)

lemma two_mul_T_le {a b : ℕ} [NeZero (a + b)] {x : Fin (4 * a + b) → ℝ} {c : ℝ}
    (h : ∀ i, 2 * Tval a b x i ≤ c) : 2 * T a b x ≤ c := by
  rw [two_mul_T]
  exact Finset.sup'_le _ _ fun i _ => h i

lemma le_two_mul_T (a b : ℕ) [NeZero (a + b)] (x : Fin (4 * a + b) → ℝ) (i : Fin (a + b)) :
    2 * Tval a b x i ≤ 2 * T a b x :=
  mul_le_mul_of_nonneg_left (Tval_le_T a b x i) (by norm_num)

/-- Transport of `T`-computability along equalities of the parameters. -/
lemma T_mem_congr {a a' B B' k : ℕ} (ha : a = a') (hB : B = B')
    [NeZero (a + B)] [NeZero (a' + B')]
    (h : T a B ∈ ReLUClass (4 * a + B) k) : T a' B' ∈ ReLUClass (4 * a' + B') k := by
  subst ha
  subst hB
  exact h

/-! ### `𝒯` and `ReLUClass` -/

/-- If `T_{a,b}` is computable with `k` hidden layers, then so is every element
of the span `𝒯_{a,b}` (on any ambient dimension). -/
lemma Tspace_subset_ReLUClass {a b : ℕ} [NeZero (a + b)] {N k : ℕ}
    (hT : T a b ∈ ReLUClass (4 * a + b) k) {f : (Fin N → ℝ) → ℝ}
    (hf : f ∈ Tspace a b N) : f ∈ ReLUClass N k := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨L, rfl⟩ := hg
      exact mem_ReLUClass.mpr ((mem_ReLUClass.mp hT).comp_affine_right L.toAffineMap)
  | zero => exact const_mem_ReLUClass 0 k
  | add u v hu hv ihu ihv => exact ReLUClass.add ihu ihv
  | smul c u hu ihu => exact ReLUClass.smul c ihu

/-! ### `T₀,ₘ` is the maximum of the coordinates -/

/-- `T_{0,m+1}` is the maximum of the coordinates. -/
lemma T_zero_eq_MAXf (m : ℕ) [NeZero (0 + (m + 1))] (x : Fin (4 * 0 + (m + 1)) → ℝ) :
    T 0 (m + 1) x = MAXf (n := 4 * 0 + m) x := by
  have he : Tval 0 (m + 1) x = x := by
    funext i
    induction i using Fin.addCases with
    | left blk => exact blk.elim0
    | right j =>
        obtain ⟨jv, hjv⟩ := j
        rw [Tval_natAdd 0 (m + 1) x hjv]
        exact congrArg x (Fin.ext (show 4 * 0 + jv = 0 + jv by omega))
  exact congrArg (Finset.univ.sup' Finset.univ_nonempty) he

/-- Reindexing `MAXf` along the defeq-breaking cast `m + 1 = 4*0 + (m+1)`. -/
lemma MAXf_comp_cast (m : ℕ) (x : Fin (4 * 0 + (m + 1)) → ℝ) :
    MAXf (n := m) (fun i => x (Fin.cast (show m + 1 = 4 * 0 + (m + 1) by omega) i))
      = MAXf (n := 4 * 0 + m) x := by
  apply le_antisymm
  · exact MAXf_le fun i => le_MAXf x _
  · refine MAXf_le fun i => ?_
    exact le_MAXf (fun i => x (Fin.cast (show m + 1 = 4 * 0 + (m + 1) by omega) i))
      (Fin.cast (show 4 * 0 + (m + 1) = m + 1 by omega) i)

/-- Reindexing `MAXf` along the opposite cast. -/
lemma MAXf_comp_cast' (m : ℕ) (x : Fin (m + 1) → ℝ) :
    MAXf (n := 4 * 0 + m) (fun i => x (Fin.cast (show 4 * 0 + (m + 1) = m + 1 by omega) i))
      = MAXf (n := m) x := by
  apply le_antisymm
  · exact MAXf_le fun i => le_MAXf x _
  · refine MAXf_le fun i => ?_
    exact le_MAXf (fun i => x (Fin.cast (show 4 * 0 + (m + 1) = m + 1 by omega) i))
      (Fin.cast (show m + 1 = 4 * 0 + (m + 1) by omega) i)

/-- Transfer `MAXf` computability to `T_{0,m+1}` computability. -/
lemma Tcomputable_of_MAXf_mem {m k : ℕ} [NeZero (0 + (m + 1))]
    (h : (MAXf : (Fin (m + 1) → ℝ) → ℝ) ∈ ReLUClass (m + 1) k) :
    Tcomputable 0 (m + 1) k := by
  have hcomp := (mem_ReLUClass.mp h).comp_affine_right
    ((LinearMap.funLeft ℝ ℝ (Fin.cast (show m + 1 = 4 * 0 + (m + 1) by omega))).toAffineMap)
  refine mem_ReLUClass.mpr ?_
  have e : (fun x : Fin (4 * 0 + (m + 1)) → ℝ =>
        (fun y (_ : Fin 1) => MAXf y)
          ((LinearMap.funLeft ℝ ℝ
            (Fin.cast (show m + 1 = 4 * 0 + (m + 1) by omega))).toAffineMap x))
      = fun x (_ : Fin 1) => T 0 (m + 1) x := by
    funext x j
    change MAXf (n := m)
        (fun i => x (Fin.cast (show m + 1 = 4 * 0 + (m + 1) by omega) i)) = T 0 (m + 1) x
    rw [MAXf_comp_cast m x]
    exact (T_zero_eq_MAXf m x).symm
  rwa [e] at hcomp

/-- Transfer `T_{0,m+1}` computability to `MAXf` computability. -/
lemma MAXf_mem_of_Tcomputable {m k : ℕ} [NeZero (0 + (m + 1))]
    (h : Tcomputable 0 (m + 1) k) :
    (MAXf : (Fin (m + 1) → ℝ) → ℝ) ∈ ReLUClass (m + 1) k := by
  have hcomp := (mem_ReLUClass.mp h).comp_affine_right
    ((LinearMap.funLeft ℝ ℝ (Fin.cast (show 4 * 0 + (m + 1) = m + 1 by omega))).toAffineMap)
  refine mem_ReLUClass.mpr ?_
  have e : (fun x : Fin (m + 1) → ℝ =>
        (fun y (_ : Fin 1) => T 0 (m + 1) y)
          ((LinearMap.funLeft ℝ ℝ
            (Fin.cast (show 4 * 0 + (m + 1) = m + 1 by omega))).toAffineMap x))
      = fun x (_ : Fin 1) => MAXf x := by
    funext x j
    change T 0 (m + 1)
        (fun i => x (Fin.cast (show 4 * 0 + (m + 1) = m + 1 by omega) i)) = MAXf x
    rw [T_zero_eq_MAXf m]
    exact MAXf_comp_cast' m x
  rwa [e] at hcomp

end NNE

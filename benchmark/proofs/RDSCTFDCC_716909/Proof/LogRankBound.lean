import Mathlib
import Proof.Types.BoolMat
import Proof.Types.Protocol
import Proof.Types.CommComplexity
import Proof.Types.MatComplexity
import Proof.UpperBound

namespace Proof.LogRankBound

open Proof.Types.BoolMat
open Proof.Types.Protocol
open Proof.Types.CommComplexity
open Proof.Types.MatComplexity
open Matrix

/-! ### The real matrix of a Boolean function / matrix and its rank -/

/-- The real matrix obtained from a Boolean function by the entrywise coercion
`true ↦ 1`, `false ↦ 0`. -/
noncomputable def matRf {m n : ℕ} (f : Fin m → Fin n → Bool) :
    Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of (fun i j => if f i j then (1 : ℝ) else 0)

/-- The real matrix of a Boolean matrix `M`. -/
noncomputable def boolMatR (M : BoolMat) : Matrix (Fin M.m) (Fin M.n) ℝ :=
  matRf M.e

/-- The (real) rank of a Boolean matrix. -/
noncomputable def boolRank (M : BoolMat) : ℕ := (boolMatR M).rank

/-! ### Matrix rank subadditivity (not in Mathlib) -/

/-- **Rank subadditivity.** `(A + B).rank ≤ A.rank + B.rank`. -/
lemma rank_add_le {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) :
    (A + B).rank ≤ A.rank + B.rank := by
  -- `rank X = finrank ℝ (range X.mulVecLin)` by definition.
  have hsub : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rw [Matrix.mulVecLin_add]
    intro v hv
    obtain ⟨w, hw⟩ := hv
    rw [← hw]
    simp only [LinearMap.add_apply]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left ⟨w, rfl⟩) (Submodule.mem_sup_right ⟨w, rfl⟩)
  calc (A + B).rank
      = Module.finrank ℝ ↥(LinearMap.range (A + B).mulVecLin) := rfl
    _ ≤ Module.finrank ℝ
          ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) :=
        Submodule.finrank_mono hsub
    _ ≤ Module.finrank ℝ ↥(LinearMap.range A.mulVecLin) +
          Module.finrank ℝ ↥(LinearMap.range B.mulVecLin) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ = A.rank + B.rank := rfl

/-! ### Constant-matrix rank -/

/-- The real matrix of the constant-`true` function is the all-ones outer
product, hence has rank ≤ 1. -/
lemma rank_const_le_one {m n : ℕ} (z : Bool) :
    (matRf (fun (_ : Fin m) (_ : Fin n) => z)).rank ≤ 1 := by
  cases z with
  | false =>
      have h0 : matRf (fun (_ : Fin m) (_ : Fin n) => false) = 0 := by
        ext i j
        simp [matRf]
      rw [h0, Matrix.rank_zero]
      exact Nat.zero_le 1
  | true =>
      have h1 : matRf (fun (_ : Fin m) (_ : Fin n) => true)
          = Matrix.vecMulVec (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) := by
        ext i j
        simp [matRf, Matrix.vecMulVec]
      rw [h1]
      exact Matrix.rank_vecMulVec_le _ _

/-! ### The core protocol-rank bound -/

/-- **Protocol rank bound.** The real matrix of the function computed by a
protocol `P` has rank at most `2 ^ P.cost`. -/
lemma protocol_rank_bound {m n : ℕ} (P : Protocol (Fin m) (Fin n) Bool) :
    (matRf (Protocol.eval P)).rank ≤ 2 ^ P.cost := by
  induction P with
  | leaf z =>
      have hconst : Protocol.eval (Protocol.leaf z : Protocol (Fin m) (Fin n) Bool)
          = fun (_ : Fin m) (_ : Fin n) => z := rfl
      rw [hconst]
      have : (2 : ℕ) ^ (Protocol.leaf z : Protocol (Fin m) (Fin n) Bool).cost = 1 := by
        simp [Protocol.cost]
      rw [this]
      exact rank_const_le_one z
  | aNode a l r ihl ihr =>
      -- Row decomposition by Alice's predicate.
      set Ml := matRf (Protocol.eval l) with hMl
      set Mr := matRf (Protocol.eval r) with hMr
      set M := matRf (Protocol.eval (Protocol.aNode a l r)) with hM
      set D0 : Matrix (Fin m) (Fin m) ℝ :=
        Matrix.diagonal (fun i => if a i then (0 : ℝ) else 1) with hD0
      set D1 : Matrix (Fin m) (Fin m) ℝ :=
        Matrix.diagonal (fun i => if a i then (1 : ℝ) else 0) with hD1
      have hdecomp : M = D0 * Ml + D1 * Mr := by
        rw [hM, hMl, hMr, hD0, hD1]
        ext i j
        simp only [matRf, Matrix.of_apply, Matrix.add_apply,
          Matrix.diagonal_mul]
        by_cases hai : a i
        · simp [Protocol.eval, hai]
        · simp [Protocol.eval, hai]
      have hstep : M.rank ≤ Ml.rank + Mr.rank := by
        rw [hdecomp]
        calc (D0 * Ml + D1 * Mr).rank
            ≤ (D0 * Ml).rank + (D1 * Mr).rank := rank_add_le _ _
          _ ≤ Ml.rank + Mr.rank :=
              Nat.add_le_add (Matrix.rank_mul_le_right _ _)
                (Matrix.rank_mul_le_right _ _)
      have harith : Ml.rank + Mr.rank ≤ 2 ^ (Protocol.aNode a l r).cost := by
        have hl : Ml.rank ≤ 2 ^ l.cost := ihl
        have hr : Mr.rank ≤ 2 ^ r.cost := ihr
        have hbl : (2 : ℕ) ^ l.cost ≤ 2 ^ (max l.cost r.cost) :=
          Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
        have hbr : (2 : ℕ) ^ r.cost ≤ 2 ^ (max l.cost r.cost) :=
          Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
        have hcost : (Protocol.aNode a l r).cost = 1 + max l.cost r.cost := rfl
        calc Ml.rank + Mr.rank
            ≤ 2 ^ (max l.cost r.cost) + 2 ^ (max l.cost r.cost) :=
              Nat.add_le_add (le_trans hl hbl) (le_trans hr hbr)
          _ = 2 ^ (1 + max l.cost r.cost) := by ring
          _ = 2 ^ (Protocol.aNode a l r).cost := by rw [hcost]
      exact le_trans hstep harith
  | bNode b l r ihl ihr =>
      -- Column decomposition by Bob's predicate.
      set Ml := matRf (Protocol.eval l) with hMl
      set Mr := matRf (Protocol.eval r) with hMr
      set M := matRf (Protocol.eval (Protocol.bNode b l r)) with hM
      set E0 : Matrix (Fin n) (Fin n) ℝ :=
        Matrix.diagonal (fun j => if b j then (0 : ℝ) else 1) with hE0
      set E1 : Matrix (Fin n) (Fin n) ℝ :=
        Matrix.diagonal (fun j => if b j then (1 : ℝ) else 0) with hE1
      have hdecomp : M = Ml * E0 + Mr * E1 := by
        rw [hM, hMl, hMr, hE0, hE1]
        ext i j
        simp only [matRf, Matrix.of_apply, Matrix.add_apply,
          Matrix.mul_diagonal]
        by_cases hbj : b j
        · simp [Protocol.eval, hbj]
        · simp [Protocol.eval, hbj]
      have hstep : M.rank ≤ Ml.rank + Mr.rank := by
        rw [hdecomp]
        calc (Ml * E0 + Mr * E1).rank
            ≤ (Ml * E0).rank + (Mr * E1).rank := rank_add_le _ _
          _ ≤ Ml.rank + Mr.rank :=
              Nat.add_le_add (Matrix.rank_mul_le_left _ _)
                (Matrix.rank_mul_le_left _ _)
      have harith : Ml.rank + Mr.rank ≤ 2 ^ (Protocol.bNode b l r).cost := by
        have hl : Ml.rank ≤ 2 ^ l.cost := ihl
        have hr : Mr.rank ≤ 2 ^ r.cost := ihr
        have hbl : (2 : ℕ) ^ l.cost ≤ 2 ^ (max l.cost r.cost) :=
          Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
        have hbr : (2 : ℕ) ^ r.cost ≤ 2 ^ (max l.cost r.cost) :=
          Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
        have hcost : (Protocol.bNode b l r).cost = 1 + max l.cost r.cost := rfl
        calc Ml.rank + Mr.rank
            ≤ 2 ^ (max l.cost r.cost) + 2 ^ (max l.cost r.cost) :=
              Nat.add_le_add (le_trans hl hbl) (le_trans hr hbr)
          _ = 2 ^ (1 + max l.cost r.cost) := by ring
          _ = 2 ^ (Protocol.bNode b l r).cost := by rw [hcost]
      exact le_trans hstep harith

/-! ### Nonemptiness of achievable costs -/

/-- The achievable cost set of any Boolean matrix is nonempty (reuse the full
announce protocol from `Proof.UpperBound`). -/
lemma achievableCosts_nonempty (M : BoolMat) : (AchievableCosts M.e).Nonempty :=
  Proof.UpperBound.AchievableCosts_nonempty M.e

/-! ### The log-rank lower bound (now a theorem, no axiom) -/

/-- **Log-rank lower bound.** `D(M) ≥ log₂ rank_ℝ(M)`. -/
theorem logRank_lowerBound (M : BoolMat) :
    (Dmat M : ℝ) ≥ Real.logb 2 (boolRank M) := by
  -- An optimal protocol realizing `Dmat M` exists.
  have hne : (AchievableCosts M.e).Nonempty := achievableCosts_nonempty M
  have hmem : Dmat M ∈ AchievableCosts M.e := by
    have : sInf (AchievableCosts M.e) ∈ AchievableCosts M.e := Nat.sInf_mem hne
    simpa [Dmat, D] using this
  obtain ⟨P, hcost, hcomp⟩ := hmem
  -- `eval P = M.e`.
  have hPeval : Protocol.eval P = M.e := by
    funext x y; exact hcomp x y
  -- `boolRank M ≤ 2 ^ Dmat M`.
  have hrankN : boolRank M ≤ 2 ^ Dmat M := by
    have h1 : (boolMatR M).rank = (matRf (Protocol.eval P)).rank := by
      rw [hPeval]; rfl
    have h2 : (matRf (Protocol.eval P)).rank ≤ 2 ^ P.cost :=
      protocol_rank_bound P
    rw [boolRank, h1, ← hcost]
    exact h2
  -- Cast and take logb.
  by_cases hzero : boolRank M = 0
  · rw [hzero]
    simp only [Nat.cast_zero, Real.logb_zero]
    positivity
  · have hpos : (0 : ℝ) < boolRank M := by
      have : 0 < boolRank M := Nat.pos_of_ne_zero hzero
      exact_mod_cast this
    have hle : (boolRank M : ℝ) ≤ (2 : ℝ) ^ Dmat M := by
      have := hrankN
      calc (boolRank M : ℝ) ≤ ((2 ^ Dmat M : ℕ) : ℝ) := by exact_mod_cast this
        _ = (2 : ℝ) ^ Dmat M := by push_cast; ring
    calc Real.logb 2 (boolRank M)
        ≤ Real.logb 2 ((2 : ℝ) ^ Dmat M) :=
          Real.logb_le_logb_of_le (by norm_num) hpos hle
      _ = Dmat M := by rw [Real.logb_pow]; simp [Real.logb_self_eq_one]

/-! ### Part (A): the {0,1}-column / fooling bound -/

/-- The if-encoding `Bool → ℝ` (`true ↦ 1`, `false ↦ 0`) is injective. -/
private lemma bool_if_inj :
    Function.Injective (fun b : Bool => if b then (1 : ℝ) else 0) := by
  intro a b hab
  cases a <;> cases b <;> simp_all

/-- **Column-counting / fooling bound.** If the columns of `M` are pairwise
distinct, then `M.n ≤ 2 ^ boolRank M`. -/
theorem distinctCols_card_le_two_pow_rank (M : BoolMat)
    (hM : Function.Injective
      (fun (j : Fin M.n) => (fun i : Fin M.m => M.e i j))) :
    M.n ≤ 2 ^ boolRank M := by
  classical
  set A := boolMatR M with hA
  -- Column map of the real matrix is injective.
  have hcolinj : Function.Injective (fun j : Fin M.n => A.col j) := by
    intro j1 j2 h
    simp only at h
    apply hM
    funext i
    have hcc : A.col j1 i = A.col j2 i := congrFun h i
    have hentry : ∀ j, A.col j i = (if M.e i j then (1 : ℝ) else 0) := by
      intro j; simp [hA, boolMatR, matRf, Matrix.col]
    rw [hentry, hentry] at hcc
    exact bool_if_inj hcc
  -- Select `finrank`-many rows spanning the row space.
  obtain ⟨g, hgmem, hgspan, _hgli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range A.row)
  -- `proj j i` = value of the `i`-th chosen row at column `j`.
  set proj : Fin M.n →
      (Fin (Module.finrank ℝ ↥(Submodule.span ℝ (Set.range A.row))) → ℝ) :=
    fun j i => g i j with hproj
  -- `proj` is injective: columns agreeing on the spanning rows agree everywhere.
  have hprojinj : Function.Injective proj := by
    intro j1 j2 hpj
    have hrowsval : ∀ i, g i j1 = g i j2 := fun i => congrFun hpj i
    -- The coordinate-difference functional `v ↦ v j1 - v j2`.
    let φ : (Fin M.n → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun v => v j1 - v j2
        map_add' := by intro x y; simp; ring
        map_smul' := by intro c x; simp; ring }
    have hφspan : Set.EqOn (⇑φ) (⇑(0 : (Fin M.n → ℝ) →ₗ[ℝ] ℝ)) (Set.range g) := by
      rintro v ⟨i, rfl⟩
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply]
      rw [hrowsval i]; ring
    -- `φ` vanishes on the span of the chosen rows = span of all rows.
    have hφrow : ∀ i : Fin M.m, φ (A.row i) = 0 := by
      intro i
      have hmem : A.row i ∈ Submodule.span ℝ (Set.range g) := by
        rw [hgspan]
        exact Submodule.subset_span ⟨i, rfl⟩
      have := LinearMap.eqOn_span hφspan hmem
      simpa using this
    apply hcolinj
    funext i
    have hri : A.row i j1 = A.row i j2 := by
      have := hφrow i
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk] at this
      linarith
    simpa [Matrix.col, Matrix.row] using hri
  -- Each chosen row is a row `A.row (ρ i)`; its entries are `{0,1}`.
  have hgrow : ∀ i, ∃ ι : Fin M.m, g i = A.row ι := by
    intro i
    obtain ⟨ι, hι⟩ := hgmem i
    exact ⟨ι, hι.symm⟩
  choose ρ hρ using hgrow
  have hprojval : ∀ j i, proj j i = (if M.e (ρ i) j then (1 : ℝ) else 0) := by
    intro j i
    show g i j = _
    rw [hρ i]
    simp [hA, boolMatR, matRf, Matrix.row]
  -- The Bool-valued projection, injective since `proj` factors through it.
  set proj' : Fin M.n →
      (Fin (Module.finrank ℝ ↥(Submodule.span ℝ (Set.range A.row))) → Bool) :=
    fun j i => M.e (ρ i) j with hproj'
  have hproj'inj : Function.Injective proj' := by
    intro j1 j2 h
    apply hprojinj
    funext i
    rw [hprojval, hprojval]
    have : M.e (ρ i) j1 = M.e (ρ i) j2 := congrFun h i
    rw [this]
  -- Count: `M.n ≤ card (Fin r → Bool) = 2 ^ r`.
  have hcard := Fintype.card_le_of_injective proj' hproj'inj
  rw [Fintype.card_fin, Fintype.card_pi_const, Fintype.card_bool] at hcard
  have hfin : Module.finrank ℝ ↥(Submodule.span ℝ (Set.range A.row)) = boolRank M := by
    rw [boolRank, ← hA, Matrix.rank_eq_finrank_span_row]
  rw [hfin] at hcard
  exact hcard

end Proof.LogRankBound

import Colorexpanders.Base

open Matrix BigOperators
open scoped Matrix.Norms.L2Operator

namespace ThresholdRank

variable {n : Type*} [Fintype n] [DecidableEq n]

/-!
### Lemma 4.3 / Lemma A.1

This is the “PSD witness ⇒ large top threshold rank” lemma.
We assume the eigenvalues are already known to lie in `[-1,1]`, and later
we will derive that from `‖A‖ ≤ 1` for the operator norm.
-/

section Lemma4_3

variable (A M : Matrix n n ℝ)
variable (hA : A.IsHermitian)

/-- **Lemma 4.3 / Lemma A.1.**

Let `A` be Hermitian with eigenvalues in `[-1,1]`. Suppose there exists a
positive semidefinite matrix `M` such that

* `frobeniusInner A M ≥ 1 - ε`,
* `frobeniusSq M ≤ 1 / r`,
* `Matrix.trace M = 1`,

for some `ε ≥ 0`, `r > 0`. Then, for any `C > 1`, the top threshold rank
of `A` at `1 - C⋅ε` is at least `(1 - 1/C)^2 r` (as a real inequality via coercion).
-/
theorem lemma4_3
    (hSpec : eigenvaluesBounded A hA)
    (hMpsd : Matrix.PosSemidef M)
    (hTr : Matrix.trace M = 1)
    {ε r : ℝ} (hr : 0 < r)
    (hInner : frobeniusInner A M ≥ 1 - ε)
    (hFrob : frobeniusSq M ≤ 1 / r)
    {C : ℝ} (hC : 1 < C) :
    ((topThresholdRank A hA (1 - C * ε)) : ℝ) ≥ (1 - 1 / C)^2 * r := by
  classical
  let Uunit := hA.eigenvectorUnitary
  let U : Matrix n n ℝ := Uunit
  have hU : U ∈ Matrix.unitaryGroup n ℝ := Uunit.property
  let d : n → ℝ := hA.eigenvalues
  have hA_decomp : A = U * Matrix.diagonal (fun i => d i) * Uᴴ := by
    have hspec := hA.spectral_theorem
    change A = (Uunit : Matrix n n ℝ) * _ * _ at hspec
    simpa [U, d, Matrix.star_eq_conjTranspose, conjTranspose, Matrix.ext_iff,
      RCLike.ofReal_real_eq_id, CompTriple.comp_eq,
      ConjAct.ofConjAct_toConjAct, Unitary.val_inv_toUnits_apply, UnitaryGroup.inv_val] using hspec

  let M' : Matrix n n ℝ := Uᴴ * M * U
  have hMpsd' : Matrix.PosSemidef M' :=
    hMpsd.conjTranspose_mul_mul_same (B := U)

  have hTr' : Matrix.trace M' = 1 := by
    have := trace_conjUnitary (n := n) (U := U) (hU := hU) (A := M)
    simpa [M', conjTranspose_eq_transpose_of_trivial] using this.trans hTr
  have hFrob' : frobeniusSq M' = frobeniusSq M :=
    frobeniusSq_conjUnitary (n := n) (U := U) (hU := hU) (M := M)

  have hInner_diag :
      frobeniusInner A M = ∑ i, d i * M' i i :=
    frobeniusInner_diagonalization (n := n)
      (U := U) (hU := hU) (d := d) (A := A) (M := M) hA_decomp hA

  have hdiag_nonneg : ∀ i, 0 ≤ M' i i := fun i => posSemidef_diag_nonneg hMpsd' i
  have hdiag_sum : ∑ i, M' i i = 1 := by simpa only [trace, diag_apply] using hTr'

  have hlam_le_one : ∀ i, d i ≤ 1 := fun i => (abs_le.mp (hSpec i)).2

  have hInner_lower : 1 - ε ≤ ∑ i, d i * M' i i := by
    linarith [hInner_diag, hInner]

  have hsum_le_one : ∑ i, d i * M' i i ≤ 1 := by
    calc
      ∑ i, d i * M' i i ≤ ∑ i, (1 : ℝ) * M' i i := by
        exact Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hlam_le_one i) (hdiag_nonneg i)
      _ = 1 := by simp [hdiag_sum]
  have hε_nonneg : 0 ≤ ε := by nlinarith [hInner_lower, hsum_le_one]

  set τ : ℝ := 1 - C * ε
  let S : Finset n := Finset.univ.filter (fun i => τ ≤ d i)
  let p : ℝ := ∑ i ∈ S, M' i i

  have hcomp_diag_sum :
      ∑ i ∈ Finset.univ.filter (fun i => ¬ τ ≤ d i), M' i i = 1 - p := by
    classical
    have hsplit :=
      Finset.sum_filter_add_sum_filter_not
        (s := Finset.univ) (p := fun i => τ ≤ d i) (f := fun i => M' i i)
    have hsplit' :
        p + ∑ i ∈ Finset.univ.filter (fun i => ¬ τ ≤ d i), M' i i = 1 := by
      simpa only [p, S, not_le, hdiag_sum] using hsplit
    linarith

  have hsum_split_le :
      ∑ i, d i * M' i i ≤ p + τ * (1 - p) := by
    classical
    let Sc : Finset n := Finset.univ.filter (fun i => ¬ τ ≤ d i)
    have hsplit :=
      Finset.sum_filter_add_sum_filter_not
        (s := Finset.univ) (p := fun i => τ ≤ d i) (f := fun i => d i * M' i i)
    have hsplit' :
        ∑ i, d i * M' i i =
          ∑ i ∈ S, d i * M' i i + ∑ i ∈ Sc, d i * M' i i := by
      simpa only [S, Sc] using hsplit.symm
    have hS_le : ∑ i ∈ S, d i * M' i i ≤ p := by
      calc
        ∑ i ∈ S, d i * M' i i ≤ ∑ i ∈ S, (1 : ℝ) * M' i i := by
          exact Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (hlam_le_one i) (hdiag_nonneg i)
        _ = p := by simp only [one_mul, p]
    have hSc_le :
        ∑ i ∈ Sc, d i * M' i i ≤ τ * (1 - p) := by
      calc
        ∑ i ∈ Sc, d i * M' i i ≤ ∑ i ∈ Sc, τ * M' i i := by
          exact Finset.sum_le_sum fun i hi =>
            mul_le_mul_of_nonneg_right
              (le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hi).2)) (hdiag_nonneg i)
        _ = τ * ∑ i ∈ Sc, M' i i := by
          simpa only using (Finset.mul_sum (a := τ) (s := Sc) (f := fun i => M' i i)).symm
        _ = τ * (1 - p) := by simpa only [Sc] using congrArg (fun x => τ * x) hcomp_diag_sum
    calc
      ∑ i, d i * M' i i
          = ∑ i ∈ S, d i * M' i i + ∑ i ∈ Sc, d i * M' i i := hsplit'
      _ ≤ p + τ * (1 - p) := add_le_add hS_le hSc_le

  have hineq : C * ε * (1 - p) ≤ ε := by
    have h := le_trans hInner_lower hsum_split_le
    have hrewrite : p + τ * (1 - p) = 1 - C * ε * (1 - p) := by
      unfold τ
      ring
    linarith [h, hrewrite]

  have hCpos : 0 < C := lt_trans (show (0 : ℝ) < 1 by norm_num) hC

  have hp_lower : 1 - 1 / C ≤ p := by
    by_cases hε0 : ε = 0
    · subst hε0
      have hsum_eq : ∑ i, d i * M' i i = 1 := by
        have hlow : (1 : ℝ) ≤ ∑ i, d i * M' i i := by simpa only [sub_zero] using hInner_lower
        exact le_antisymm hsum_le_one hlow
      have hdiff_sum : ∑ i, (1 - d i) * M' i i = 0 := by
        have hrewrite :
            ∑ i, (1 - d i) * M' i i = (∑ i, M' i i) - ∑ i, d i * M' i i := by
          calc
            ∑ i, (1 - d i) * M' i i = ∑ i, (M' i i - d i * M' i i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
            _ = (∑ i, M' i i) - ∑ i, d i * M' i i := by simp only [Finset.sum_sub_distrib]
        linarith [hrewrite, hdiag_sum, hsum_eq]
      have hnonneg' :
          ∀ i ∈ (Finset.univ : Finset n), 0 ≤ (1 - d i) * M' i i := by
        intro i hi
        exact mul_nonneg (by linarith [hlam_le_one i]) (hdiag_nonneg i)
      have hzero :
          ∀ i ∈ (Finset.univ : Finset n), (1 - d i) * M' i i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg hnonneg').1 hdiff_sum
      have hτ1 : τ = 1 := by simp only [mul_zero, sub_zero, τ]
      have hcomp_sum_zero :
          ∑ i ∈ Finset.univ.filter (fun i => ¬ τ ≤ d i), M' i i = 0 := by
        refine (Finset.sum_eq_zero_iff_of_nonneg ?_).2 ?_
        · intro i hi
          exact hdiag_nonneg i
        · intro i hi
          have hnot : ¬ τ ≤ d i := (Finset.mem_filter.mp hi).2
          have hne : (1 - d i) ≠ 0 := by linarith [hτ1, hnot]
          exact (mul_eq_zero.mp (hzero i (Finset.mem_univ i))).resolve_left hne
      have hp_one : p = 1 := by linarith [hcomp_diag_sum, hcomp_sum_zero]
      have hCinv_pos : 0 < (1 / C : ℝ) := one_div_pos.mpr hCpos
      linarith [hp_one, hCinv_pos]
    · have hεpos : 0 < ε := lt_of_le_of_ne hε_nonneg (by simpa only [ne_eq, eq_comm] using hε0)
      have hstep1 : C * (1 - p) ≤ 1 := by
        have hdiv : C * (1 - p) ≤ ε / ε := by
          refine (le_div_iff₀ hεpos).2 ?_
          have hmul : C * (1 - p) * ε = C * ε * (1 - p) := by ring
          linarith [hineq, hmul]
        simpa only [div_self (ne_of_gt hεpos)] using hdiv
      have hdiv : 1 - p ≤ 1 / C := by
        refine (le_div_iff₀ hCpos).2 ?_
        simpa only [mul_assoc, mul_comm, mul_left_comm] using hstep1
      linarith

  have hp_nonneg : 0 ≤ p := by
    simpa only [p] using Finset.sum_nonneg (fun i _ => hdiag_nonneg i)

  have hCS :
      p ≤ Real.sqrt (S.card) * Real.sqrt (∑ i ∈ S, (M' i i)^2) := by
    classical
    have h :=
      Real.sum_mul_le_sqrt_mul_sqrt (s := S) (f := fun _ => (1 : ℝ)) (g := fun i => M' i i)
    simpa only [pow_two, ge_iff_le, one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
      h
  have hCS_sq :
      p^2 ≤ (S.card : ℝ) * ∑ i ∈ S, (M' i i)^2 := by
    have hsum_nonneg : 0 ≤ ∑ i ∈ S, (M' i i)^2 := by positivity
    have hcard_nonneg : 0 ≤ (S.card : ℝ) := by exact_mod_cast Nat.zero_le _
    nlinarith [hCS, hp_nonneg, Real.sq_sqrt hcard_nonneg, Real.sq_sqrt hsum_nonneg]

  have hdiag_sq_le :
      ∑ i ∈ S, (M' i i)^2 ≤ frobeniusSq M' := by
    classical
    have hrow : ∀ i, (M' i i)^2 ≤ ∑ j, (M' i j)^2 := by
      intro i
      exact Finset.single_le_sum (f := fun j => (M' i j)^2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have hrows :
        ∑ i ∈ S, (M' i i)^2 ≤ ∑ i ∈ S, ∑ j, (M' i j)^2 := by
      exact Finset.sum_le_sum (fun i _ => hrow i)
    have htotal :
        ∑ i ∈ S, ∑ j, (M' i j)^2 ≤ ∑ i, ∑ j, (M' i j)^2 := by
      exact Finset.sum_le_univ_sum_of_nonneg (s := S) (f := fun i => ∑ j, (M' i j)^2)
        (by intro i; positivity)
    exact le_trans hrows (by simpa only [frobeniusSq] using htotal)

  have hCS_sq' :
      p^2 ≤ (S.card : ℝ) * frobeniusSq M' := by
    have hcard_nonneg : 0 ≤ (S.card : ℝ) := by exact_mod_cast Nat.zero_le _
    have hbound :=
      mul_le_mul_of_nonneg_left hdiag_sq_le hcard_nonneg
    exact le_trans hCS_sq hbound

  have hFrob'' : frobeniusSq M' ≤ 1 / r := by
    simpa only [hFrob', one_div] using hFrob
  have hcard_bound :
      p^2 * r ≤ (S.card : ℝ) := by
    have hr_nonneg : 0 ≤ r := le_of_lt hr
    have hmul :
        p^2 * r ≤ ((S.card : ℝ) * frobeniusSq M') * r := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_right hCS_sq' hr_nonneg)
    have hFrob_mul : frobeniusSq M' * r ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right hFrob'' hr_nonneg
      have hr_ne : r ≠ 0 := ne_of_gt hr
      have hright : (1 / r) * r = (1 : ℝ) := by field_simp [hr_ne]
      linarith
    have hcard_nonneg : 0 ≤ (S.card : ℝ) := by exact_mod_cast Nat.zero_le _
    have hmul' :
        ((S.card : ℝ) * frobeniusSq M') * r ≤ (S.card : ℝ) := by
      nlinarith [hFrob_mul, hcard_nonneg]
    exact le_trans hmul hmul'

  have hp_sq : (1 - 1 / C)^2 ≤ p^2 := by
    have hpos : 0 ≤ 1 - 1 / C := by
      have hCge : (1 : ℝ) ≤ C := le_of_lt hC
      have hinv_le_one : 1 / C ≤ (1 : ℝ) := by
        simpa only [one_div, inv_one] using
          (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hCge)
      linarith
    simpa only [pow_two] using
      (mul_le_mul hp_lower hp_lower hpos hp_nonneg)

  have hfinal :
      (1 - 1 / C)^2 * r ≤ (S.card : ℝ) := by
    have hr_nonneg : 0 ≤ r := le_of_lt hr
    have hp_sq' := mul_le_mul_of_nonneg_right hp_sq hr_nonneg
    exact le_trans hp_sq' hcard_bound

  have hS_card_nat :
      topThresholdRank A hA τ = S.card := by
    have hcard : Fintype.card { i | τ ≤ hA.eigenvalues i } = S.card :=
      Fintype.card_of_finset' (s := S) (p := { i | τ ≤ hA.eigenvalues i }) (by
        intro i
        simp only [S, d, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq])
    change Fintype.card { i // τ ≤ hA.eigenvalues i } = S.card
    rw [Fintype.card_subtype]

  simpa only [ge_iff_le, hS_card_nat] using hfinal

end Lemma4_3

end ThresholdRank

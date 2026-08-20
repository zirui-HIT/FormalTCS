import Colorexpanders.Base
import Colorexpanders.Lemma4_3
import Colorexpanders.Lemma4_4

open Matrix BigOperators
open scoped Matrix.Norms.L2Operator

namespace ThresholdRank

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Theorem 4.1 (Large bottom rank implies large top rank).**

Includes the trivial `t = 0` case. -/
theorem large_bottom_rank_implies_large_top_rank
    [Nonempty n] (A : Matrix n n ℝ)
    (hHerm : A.IsHermitian)
    (hNonneg : ∀ i j, 0 ≤ A i j)
    (hOp : ‖A‖ ≤ (1 : ℝ))
    {μ : ℝ} (hμ : 0 ≤ μ)
    {t : ℕ} (hBottom : bottomThresholdRank A hHerm μ ≥ t)
    {σ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) :
    (topThresholdRank A hHerm ((μ^(2 : ℕ) - σ) / (1 - σ)) : ℝ)
      ≥ σ^2 * (t : ℝ) := by
  classical
  by_cases ht0 : t = 0
  · subst ht0
    have hnonneg :
        0 ≤ (topThresholdRank A hHerm ((μ^(2:ℕ) - σ) / (1 - σ)) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    nlinarith
  · have ht : 0 < t := Nat.pos_of_ne_zero ht0
    obtain ⟨M, hMpsd, hTr, hFrob, hInner⟩ :=
      lemma4_4 (A := A) (n := n) (hHerm := hHerm) (hNonneg := hNonneg)
        (hOp := hOp) (hμ := hμ) (ht := ht) (hBottom := hBottom)

    let ε : ℝ := 1 - μ^(2:ℕ)
    have hInner' : frobeniusInner A M ≥ 1 - ε := by
      unfold ε
      nlinarith [hInner]
    have hC : 1 < (1 - σ)⁻¹ := by
      refine (one_lt_inv₀ (sub_pos.mpr hσ₁)).2 ?_
      linarith

    have hTop :
        (topThresholdRank A hHerm (1 - (1 - σ)⁻¹ * ε) : ℝ) ≥
          (1 - 1 / ((1 - σ)⁻¹))^2 * (t : ℝ) :=
      lemma4_3 (A := A) (M := M) (n := n) (hA := hHerm)
        (eigenvaluesBounded_of_opNorm_le_one (A := A) hHerm hOp)
        hMpsd hTr (ε := ε) (r := (t : ℝ))
        (by exact_mod_cast ht) hInner' hFrob (C := (1 - σ)⁻¹) hC

    have hτ :
        1 - (1 - σ)⁻¹ * ε = (μ^(2:ℕ) - σ) / (1 - σ) := by
      have hden : (1 - σ) ≠ 0 := by linarith
      unfold ε
      field_simp [hden]
      ring
    have hτ' :
        1 - ε * (1 - σ)⁻¹ = (μ^(2:ℕ) - σ) / (1 - σ) := by
      simpa only [mul_comm] using hτ

    have hσsq :
        (1 - 1 / ((1 - σ)⁻¹))^2 = σ^2 := by
      have hden : (1 - σ) ≠ 0 := by linarith
      field_simp [hden]
      ring
    simpa only [hτ', hσsq, mul_comm] using hTop

/-- **Corollary 4.2 (Small top rank implies small bottom rank).** -/
theorem small_top_rank_implies_small_bottom_rank
    [Nonempty n] (A : Matrix n n ℝ)
    (hHerm : A.IsHermitian)
    (hNonneg : ∀ i j, 0 ≤ A i j)
    (hOp : ‖A‖ ≤ (1 : ℝ))
    {τ : ℝ} (hτ : 0 ≤ τ) {s : ℕ}
    (htop : topThresholdRank A hHerm τ ≤ s)
    {σ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) :
    (bottomThresholdRank A hHerm (Real.sqrt (σ + τ * (1 - σ))) : ℝ)
      ≤ s / (σ^2) := by
  classical
  set μ : ℝ := Real.sqrt (σ + τ * (1 - σ)) with hμdef
  have hμ_nonneg : 0 ≤ μ := by simp only [hμdef, Real.sqrt_nonneg]
  have hμ_sq : μ^(2:ℕ) = σ + τ * (1 - σ) := by
    have hpos : 0 ≤ σ + τ * (1 - σ) := by
      have hσnonneg : 0 ≤ σ := le_of_lt hσ₀
      have h1σ : 0 ≤ 1 - σ := sub_nonneg.mpr (le_of_lt hσ₁)
      nlinarith
    have h := Real.sq_sqrt hpos
    simpa only [hμdef] using h
  have hτ_from_μ :
      (μ^(2:ℕ) - σ) / (1 - σ) = τ := by
    have hden : 1 - σ ≠ 0 := by linarith
    calc
      (μ^(2:ℕ) - σ) / (1 - σ) = ((σ + τ * (1 - σ)) - σ) / (1 - σ) := by
        simp only [hμ_sq]
      _ = τ := by
        field_simp [hden]
        ring
  have htop_real : (topThresholdRank A hHerm τ : ℝ) ≤ s := by
    exact_mod_cast htop
  have hσ2_pos : 0 < σ^2 := by nlinarith
  have htop_lower :
      (topThresholdRank A hHerm τ : ℝ) ≥
        σ^2 * (bottomThresholdRank A hHerm μ : ℝ) := by
    simpa only [hτ_from_μ] using
      (large_bottom_rank_implies_large_top_rank (A := A) (n := n) (hHerm := hHerm)
        (hNonneg := hNonneg) (hOp := hOp) (hμ := hμ_nonneg) (hBottom := le_rfl) (σ := σ) hσ₀ hσ₁)
  have hmul_le_s : σ^2 * (bottomThresholdRank A hHerm μ : ℝ) ≤ s := by
    linarith [htop_real, htop_lower]
  exact (le_div_iff₀ hσ2_pos).2 (by simpa only [mul_comm] using hmul_le_s)

#print axioms large_bottom_rank_implies_large_top_rank
#print axioms small_top_rank_implies_small_bottom_rank

end ThresholdRank

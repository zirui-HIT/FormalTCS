import GenLimit.Paper39_DenseGeneration.Abstract.PartialEnumeration
import GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity

/-!
# The partial-enumeration density endgame

This module formalizes the liminf calculation in Theorem 3.17 directly in
ambient prefixes.  It avoids the paper's informal order-preserving
normalization of the target to the positive integers.
-/

open Filter
open scoped Topology

namespace GenLimit
namespace PatientScope

/-- The generator's target-relative lower density in a partial-enumeration
certificate. -/
noncomputable def PartialEnumerationCertificate.lowerDensity
    (P : PartialEnumerationCertificate) : ℝ :=
  relativeLowerDensity (P.defender ∩ P.target) P.target

/-- Analytic counting core of Theorem 3.17. -/
theorem partialDensity_of_counting
    (N E D : ℕ → ℕ) (r : ℕ)
    (hN : Tendsto N atTop atTop)
    (hE_le_N : ∀ n, E n ≤ N n)
    (hD_le_N : ∀ n, D n ≤ N n)
    (hcount : ∀ n, E n ≤ 2 * D n + r + Nat.log2 (N n)) :
    (1 / 2 : ℝ) *
        liminf (fun n => (E n : ℝ) / (N n : ℝ)) atTop ≤
      liminf (fun n => (D n : ℝ) / (N n : ℝ)) atTop := by
  let eRatio : ℕ → ℝ := fun n => (E n : ℝ) / (N n : ℝ)
  let dRatio : ℕ → ℝ := fun n => (D n : ℝ) / (N n : ℝ)
  let err : ℕ → ℝ := fun n =>
    ((r + Nat.log2 (N n) : ℕ) : ℝ) / (N n : ℝ)
  have herr : Tendsto err atTop (𝓝 0) := by
    have h := (tendsto_countingError_div r).comp hN
    change Tendsto ((fun n : ℕ => ((r + n.log2 : ℕ) : ℝ) / (n : ℝ)) ∘ N)
      atTop (𝓝 0)
    exact h
  have heNonneg : ∀ n, 0 ≤ eRatio n := fun n =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hdNonneg : ∀ n, 0 ≤ dRatio n := fun n =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have heLeOne : ∀ n, eRatio n ≤ 1 := by
    intro n
    by_cases hn : N n = 0
    · simp [eRatio, hn]
    · dsimp [eRatio]
      rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast hE_le_N n
  have hdLeOne : ∀ n, dRatio n ≤ 1 := by
    intro n
    by_cases hn : N n = 0
    · simp [dRatio, hn]
    · dsimp [dRatio]
      rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast hD_le_N n
  have heBound : atTop.IsBoundedUnder (· ≥ ·) eRatio :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall heNonneg)
  have hdBound : atTop.IsBoundedUnder (· ≥ ·) dRatio :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall hdNonneg)
  have hdCobound : atTop.IsCoboundedUnder (· ≥ ·) dRatio :=
    isCoboundedUnder_ge_of_le atTop hdLeOne
  rw [show (fun n => (E n : ℝ) / (N n : ℝ)) = eRatio from rfl,
    show (fun n => (D n : ℝ) / (N n : ℝ)) = dRatio from rfl]
  apply (le_liminf_iff' hdCobound hdBound).2
  intro y hy
  have htwo : 2 * y < liminf eRatio atTop := by nlinarith
  obtain ⟨c, hyc, hc⟩ := exists_between htwo
  have heEvent : ∀ᶠ n in atTop, c < eRatio n :=
    eventually_lt_of_lt_liminf hc heBound
  have herrEvent : ∀ᶠ n in atTop, err n < c - 2 * y := by
    have hpos : 0 < c - 2 * y := sub_pos.mpr hyc
    exact (tendsto_order.1 herr).2 _ hpos
  have hNpos : ∀ᶠ n in atTop, 0 < N n :=
    hN.eventually (eventually_gt_atTop 0)
  filter_upwards [heEvent, herrEvent, hNpos] with n hen herrn hn
  have hnR : (0 : ℝ) < N n := by exact_mod_cast hn
  have hcountR :
      (E n : ℝ) ≤ 2 * (D n : ℝ) + (r : ℝ) +
        (Nat.log2 (N n) : ℝ) := by
    exact_mod_cast hcount n
  have hcompare : eRatio n - err n ≤ 2 * dRatio n := by
    dsimp [eRatio, dRatio, err]
    rw [show ((r + Nat.log2 (N n) : ℕ) : ℝ) =
      (r : ℝ) + (Nat.log2 (N n) : ℝ) by norm_num]
    rw [sub_le_iff_le_add, div_le_iff₀ hnR]
    field_simp [hnR.ne']
    nlinarith
  nlinarith

namespace PartialEnumerationCertificate

/-- Theorem 3.17 at certificate level: the generator obtains at least half
the enumerated set's lower density inside the true target. -/
theorem theorem_3_17
    (P : PartialEnumerationCertificate)
    (hInfinite : P.target.Infinite)
    (hlog : ∀ n, prefixCount P.switchLoss n ≤
      Nat.log2 (P.targetCount n)) :
    (1 / 2 : ℝ) * relativeLowerDensity P.enumerated P.target ≤
      P.lowerDensity := by
  apply partialDensity_of_counting
    P.targetCount P.enumeratedCount P.defenderCount P.earlyAttacker.card
  · change Tendsto (prefixCount P.target) atTop atTop
    exact tendsto_prefixCount_atTop hInfinite
  · intro n
    exact prefixCount_mono P.enumerated_subset_target n
  · intro n
    exact prefixCount_mono (Set.inter_subset_right) n
  · intro n
    simpa only [targetCount] using
      P.enumeratedCount_le_two_mul_defender hlog n

end PartialEnumerationCertificate
end PatientScope
end GenLimit

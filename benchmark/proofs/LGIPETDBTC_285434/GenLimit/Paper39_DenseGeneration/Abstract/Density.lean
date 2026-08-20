import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# The asymptotic counting argument for lower density

This module isolates the final analytic calculation in the proof of Theorem 3.14.
After the order-preserving reduction of the target language to `ℕ`, let `D n`
and `A n` count the first `n` target elements first announced by the generator
and adversary.  If these counts partition each prefix, and the charging
argument bounds `A n` by `D n + r + log₂ n`, then the generator has lower
density at least `1/2`.
-/

open Filter
open scoped Topology

namespace GenLimit

/-- The discrete base-two logarithm is negligible compared with `n`. -/
theorem tendsto_natLog2_div :
    Tendsto (fun n : ℕ => (Nat.log2 n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have hlogb :
      Tendsto (fun n : ℕ => Real.logb 2 (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [id_eq] using
      (Real.isLittleO_logb_id_atTop (b := (2 : ℝ))).natCast_atTop.tendsto_div_nhds_zero
  exact squeeze_zero
    (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (fun n => div_le_div_of_nonneg_right (Real.log2_le_logb n) (Nat.cast_nonneg _))
    hlogb

/-- A fixed constant plus `log₂ n` is negligible compared with `n`. -/
theorem tendsto_countingError_div (r : ℕ) :
    Tendsto (fun n : ℕ => ((r + Nat.log2 n : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have hr : Tendsto (fun n : ℕ => (r : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa only [Nat.cast_add, add_div, zero_add] using hr.add tendsto_natLog2_div

/-- The lower comparison sequence used in Theorem 3.14 tends to `1/2`. -/
theorem tendsto_half_sub_countingError (r : ℕ) :
    Tendsto
      (fun n : ℕ => (1 / 2 : ℝ) - ((r + Nat.log2 n : ℕ) : ℝ) / (2 * (n : ℝ)))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have h := (tendsto_countingError_div r).div_const (2 : ℝ)
  simpa [div_div, mul_comm] using tendsto_const_nhds.sub h

/-- The asymptotic counting core of Theorem 3.14.

`D n` and `A n` are the numbers among the first `n` target elements first
announced by the generator and adversary, respectively. The first assumption
says these two classes partition every prefix. The second is the charging
bound obtained from Fact 3.12 and Lemma 3.13.
-/
theorem lowerDensity_half_of_counting
    (D A : ℕ → ℕ) (r : ℕ)
    (hpartition : ∀ n, D n + A n = n)
    (hcharge : ∀ n, A n ≤ D n + r + Nat.log2 n) :
    (1 / 2 : ℝ) ≤ liminf (fun n : ℕ => (D n : ℝ) / (n : ℝ)) atTop := by
  let g : ℕ → ℝ := fun n =>
    (1 / 2 : ℝ) - ((r + Nat.log2 n : ℕ) : ℝ) / (2 * (n : ℝ))
  have hg : Tendsto g atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [g] using tendsto_half_sub_countingError r
  have hcompare : ∀ᶠ n : ℕ in atTop, g n ≤ (D n : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hcountNat : n ≤ 2 * D n + r + Nat.log2 n := by
      calc
        n = D n + A n := (hpartition n).symm
        _ ≤ D n + (D n + r + Nat.log2 n) := Nat.add_le_add_left (hcharge n) _
        _ = 2 * D n + r + Nat.log2 n := by omega
    have hcountR :
        (n : ℝ) ≤ 2 * (D n : ℝ) + (r : ℝ) + (Nat.log2 n : ℝ) := by
      exact_mod_cast hcountNat
    rw [show g n =
      (1 / 2 : ℝ) - ((r : ℝ) + (Nat.log2 n : ℝ)) / (2 * (n : ℝ)) by
        simp [g]]
    rw [le_div_iff₀ hnR]
    field_simp [hnR.ne']
    nlinarith
  have hD_le_n : ∀ n, D n ≤ n := fun n => by
    calc
      D n ≤ D n + A n := Nat.le_add_right _ _
      _ = n := hpartition n
  have hratio_le_one : ∀ n, (D n : ℝ) / (n : ℝ) ≤ 1 := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      rw [div_le_one hnR]
      exact_mod_cast hD_le_n n
  calc
    (1 / 2 : ℝ) = liminf g atTop := hg.liminf_eq.symm
    _ ≤ liminf (fun n : ℕ => (D n : ℝ) / (n : ℝ)) atTop :=
      liminf_le_liminf hcompare hg.isBoundedUnder_ge
        (isCoboundedUnder_ge_of_le atTop hratio_le_one)

end GenLimit

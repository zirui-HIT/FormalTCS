import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat

set_option linter.all false
set_option maxHeartbeats 500000

noncomputable def approx_ratio (M : ℕ) (r : ℕ → ℝ) : ℝ :=
  ((M : ℝ) - 1) / ((M : ℝ) + 1) *
    (((M : ℝ) - 5) / ((M : ℝ) - 1)
      - (5 / 6) * (r 5 / ((M : ℝ) - 1))
      - (5 / ((M : ℝ) - 1)) * ∑ j ∈ Finset.Icc 6 M, r j / ((j : ℝ) - 1))

structure utility_config_instance where
  M : ℕ
  hM : 6 ≤ M
  r : ℕ → ℝ
  principalOpt : ℝ
  hPrincipalOpt : 0 ≤ principalOpt
  principalAlg : ℝ
  principalReturned : ℝ
  hReturned : principalAlg ≤ principalReturned
  objOpt : ℝ
  objAlg : ℝ
  estBoundsHold : Prop
  hEst : estBoundsHold
  trueBoundsHold : Prop
  hEstToTrue : estBoundsHold → trueBoundsHold
  hAlgLB : trueBoundsHold → objAlg ≤ principalAlg
  hOptFeasible : objOpt ≤ objAlg
  hOptub : approx_ratio M r * principalOpt ≤ objOpt

theorem main (I : utility_config_instance) :
    approx_ratio I.M I.r * I.principalOpt ≤ I.principalReturned := by sorry

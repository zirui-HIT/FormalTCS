import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Union
import Mathlib.Topology.MetricSpace.Pseudo.Basic

open scoped RealInnerProductSpace

def mse {H : Type*} [NormedAddCommGroup H] (y f : H) : ℝ :=
  ‖f - y‖ ^ 2

def path_orthogonality {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (y : H) (xfeat : ι → H) (S : ℕ → Finset ι) (yhat : ℕ → H) : Prop :=
  (∀ t : ℕ, ⟪yhat t, yhat t - y⟫ = 0) ∧
    (∀ t : ℕ, ∀ l ∈ S t, ⟪xfeat l, yhat t - y⟫ = 0) ∧
      (∀ t : ℕ, ⟪yhat t, yhat (t + 1) - y⟫ = 0)

theorem small_improvement_path {ι H : Type*} [DecidableEq ι] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (y : H) (xfeat : ι → H) (S : ℕ → Finset ι) (yhat : ℕ → H)
    (horth : path_orthogonality y xfeat S yhat) (α : ι → ℝ) {a b : ℕ} (hab : a < b)
    {ε : ℝ} (hεnonneg : 0 ≤ ε) (hε : mse y (yhat a) - mse y (yhat b) = ε) {Ag MX : ℝ}
    (hAg : ∑ l ∈ (Finset.Ioc a b).biUnion S, |α l| ≤ Ag) (hMX : 0 ≤ MX)
    (hmom : ∀ l ∈ (Finset.Ioc a b).biUnion S, ⟪xfeat l, xfeat l⟫ ≤ MX ^ 2) :
    mse y (yhat b) ≤ mse y (∑ l ∈ (Finset.Ioc a b).biUnion S, α l • xfeat l)
      + 2 * Ag * MX * Real.sqrt ((b - a : ℕ) : ℝ) * Real.sqrt ε := by sorry

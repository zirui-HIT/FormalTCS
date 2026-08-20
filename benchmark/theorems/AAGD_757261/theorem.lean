import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Order.Filter.Extr
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option linter.all false
set_option maxHeartbeats 500000

noncomputable def gd_iterate {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] (f : F → ℝ) (α : ℕ → ℝ) (x₀ : F) : ℕ → F
  | 0 => x₀
  | (t + 1) => gd_iterate f α x₀ t - α t • gradient f (gd_iterate f α x₀ t)

noncomputable def silver_rate : ℝ :=
  2 * Real.logb 2 (1 + Real.sqrt 2) / (1 + Real.logb 2 (1 + Real.sqrt 2))

theorem main {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] :
    ∃ (α : ℕ → ℝ) (C : ℝ), (∀ t, 0 < α t) ∧ 0 < C ∧
      ∀ (f : F → ℝ) (x₀ xStar : F),
        Differentiable ℝ f → ConvexOn ℝ Set.univ f → LipschitzWith 1 (gradient f) →
          IsMinOn f Set.univ xStar →
          ∀ T : ℕ, 1 ≤ T →
            f (gd_iterate f α x₀ T) - f xStar ≤
              C * ‖x₀ - xStar‖ ^ 2 / (T : ℝ) ^ silver_rate := by sorry

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open MeasureTheory

noncomputable def mse {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y g : Ω → ℝ) : ℝ :=
  ∫ ω, (Y ω - g ω) ^ 2 ∂P

noncomputable def disagreement {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (g₁ g₂ : Ω → ℝ) : ℝ :=
  ∫ ω, (g₁ ω - g₂ ω) ^ 2 ∂P

noncomputable def average_predictor {Ω : Type*} (g₁ g₂ : Ω → ℝ) : Ω → ℝ :=
  fun ω => (g₁ ω + g₂ ω) / 2

noncomputable def population_risk {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℝ)
    (H : Set (Ω → ℝ)) : ℝ :=
  sInf ((fun g => mse P Y g) '' H)

theorem midpoint_anchor {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y f₁ f₂ : Ω → ℝ) (H : Set (Ω → ℝ))
    (hY : MemLp Y 2 P) (h₁ : MemLp f₁ 2 P) (h₂ : MemLp f₂ 2 P)
    (hmem : average_predictor f₁ f₂ ∈ H) :
    disagreement P f₁ f₂ ≤
      2 * (mse P Y f₁ - population_risk P Y H) +
      2 * (mse P Y f₂ - population_risk P Y H) := by sorry

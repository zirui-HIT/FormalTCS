import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open MeasureTheory

noncomputable def correlation {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : MeasureTheory.Measure Ω) (y : Ω → ℝ) (x : Ω → X) (h : X → ℝ) : ℝ :=
  ∫ ω, (2 * y ω - 1) * h (x ω) ∂μ

noncomputable def residual_correlation {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : MeasureTheory.Measure Ω) (y : Ω → ℝ) (x : Ω → X)
    (p c : X → ℝ) : ℝ :=
  ∫ ω, c (x ω) * (y ω - p (x ω)) ∂μ

noncomputable def threshold_predictor {Ω : Type*} (p : Ω → ℝ) : Ω → ℝ :=
  fun ω => Real.sign (2 * p ω - 1)

def multiaccurate {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : MeasureTheory.Measure Ω) (C : Set (X → ℝ)) (τ : ℝ)
    (y : Ω → ℝ) (x : Ω → X) (p : X → ℝ) : Prop :=
  ∀ c ∈ C, |residual_correlation μ y x p c| ≤ τ

noncomputable def calibration_error {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : MeasureTheory.Measure Ω) (y : Ω → ℝ) (x : Ω → X)
    (p : X → ℝ) : ℝ :=
  ∫ ω, |(μ[y | MeasurableSpace.comap (fun ω => p (x ω)) (borel ℝ)]) ω -
    p (x ω)| ∂μ

def calibrated {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : MeasureTheory.Measure Ω) (τ : ℝ) (y : Ω → ℝ)
    (x : Ω → X) (p : X → ℝ) : Prop :=
  calibration_error μ y x p ≤ τ

noncomputable def best_correlation {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : MeasureTheory.Measure Ω) (y : Ω → ℝ) (x : Ω → X)
    (C : Set (X → ℝ)) : ℝ :=
  sSup ((fun c => correlation μ y x c) '' C)

theorem calma_to_sal
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (C : Set (X → ℝ)) (y : Ω → ℝ) (x : Ω → X) (p : X → ℝ)
    (τ : ℝ) (hτ : 0 < τ)
    (hy : Measurable y) (hx : Measurable x) (hp : Measurable p)
    (hy_range : ∀ᵐ ω ∂μ, y ω = 0 ∨ y ω = 1)
    (hp_range : ∀ ξ, p ξ ∈ Set.Icc (0 : ℝ) 1)
    (hC : ∀ c ∈ C, Measurable c ∧ ∀ ξ, |c ξ| ≤ 1)
    (hma : multiaccurate μ C τ y x p) (hcal : calibrated μ τ y x p) :
    correlation μ y x (threshold_predictor p) ≥
      best_correlation μ y x C - 4 * τ := by sorry

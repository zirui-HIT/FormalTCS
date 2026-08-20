import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Topology.UnitInterval

set_option linter.all false
set_option maxHeartbeats 500000

def truthful_outcome_value (x : Bool) : ℝ :=
  if x then 1 else 0

structure c_smoothed_setting (T : ℕ) (c : ℝ) where
  nature : List Bool → MeasureTheory.Measure unitInterval
  density : List Bool → unitInterval → ENNReal
  nature_probability :
    ∀ h, h.length < T → MeasureTheory.IsProbabilityMeasure (nature h)
  nature_eq_density :
    ∀ h, h.length < T →
      nature h =
        (MeasureTheory.volume : MeasureTheory.Measure unitInterval).withDensity (density h)
  density_bound :
    ∀ h, h.length < T →
      ∀ᵐ p ∂(MeasureTheory.volume : MeasureTheory.Measure unitInterval),
        density h p ≤ ENNReal.ofReal (1 / c)

noncomputable def masked_threshold_residual_sum
    (z : List (unitInterval × Bool))
    (mask : Fin z.length → Bool)
    (α : unitInterval) : ℝ :=
  ∑ t : Fin z.length,
    if mask t = true ∧ (z.get t).1 ≤ α then
      truthful_outcome_value (z.get t).2 - ((z.get t).1 : ℝ)
    else 0

noncomputable def subsampled_step_calibration_error
    (z : List (unitInterval × Bool)) : ℝ :=
  (∑ mask : Fin z.length → Bool,
      sSup (Set.range fun α : unitInterval =>
        |masked_threshold_residual_sum z mask α|)) /
    (Fintype.card (Fin z.length → Bool) : ℝ)

def realized_variance (z : List (unitInterval × Bool)) : ℝ :=
  ∑ t : Fin z.length, ((z.get t).1 : ℝ) * (1 - ((z.get t).1 : ℝ))

noncomputable def sequential_expectation
    (nature : List Bool → MeasureTheory.Measure unitInterval)
    (payoff : List (unitInterval × Bool) → ℝ) :
    ℕ → List (unitInterval × Bool) → ℝ
  | 0, z => payoff z
  | n + 1, z =>
      ∫ p,
        (p : ℝ) * sequential_expectation nature payoff n (z ++ [(p, true)]) +
          (1 - (p : ℝ)) *
            sequential_expectation nature payoff n (z ++ [(p, false)])
        ∂(nature (z.map Prod.snd))

noncomputable def truthful_expected_subsampled_error
    {T : ℕ} {c : ℝ} (P : c_smoothed_setting T c) : ℝ :=
  sequential_expectation P.nature subsampled_step_calibration_error T []

noncomputable def expected_sqrt_realized_variance
    {T : ℕ} {c : ℝ} (P : c_smoothed_setting T c) : ℝ :=
  sequential_expectation P.nature (fun z => Real.sqrt (realized_variance z)) T []

theorem strongupperbound_asymptotic :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ {T : ℕ} {c : ℝ} (P : c_smoothed_setting T c),
        2 ≤ T → 0 < c → c ≤ Real.exp (-1) →
          truthful_expected_subsampled_error P ≤
            C₁ * Real.sqrt (Real.log (1 / c)) *
                expected_sqrt_realized_variance P +
              C₂ * (Real.log (T : ℝ)) ^ 2 * Real.log ((T : ℝ) / c) := by sorry

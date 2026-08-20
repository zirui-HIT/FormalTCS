import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Interval.Set.OrdConnected

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

def binary_decision_loss (τ y yhat : ℝ) : ℝ :=
  τ * (1 - y) * yhat + (1 - τ) * y * (1 - yhat)

noncomputable def risk_bd (μ : Measure Ω) (Y g : Ω → ℝ) (τ : ℝ) : ℝ :=
  ∫ ω, binary_decision_loss τ (Y ω)
      (Set.indicator {x : ℝ | τ ≤ x} (fun _ => (1 : ℝ)) (g ω)) ∂μ

noncomputable def cutoff_cal_error (μ : Measure Ω) (Y V : Ω → ℝ) : ℝ :=
  ⨆ I : {s : Set ℝ // s.OrdConnected},
    |∫ ω, (Y ω - V ω) * Set.indicator I.1 (fun _ => (1 : ℝ)) (V ω) ∂μ|

noncomputable def monotone_wrapper_risk (μ : Measure Ω) (Y V : Ω → ℝ) (τ : ℝ) : ℝ :=
  ⨅ h : {h : ℝ → ℝ // Monotone h ∧ Set.MapsTo h (Set.Icc 0 1) (Set.Icc 0 1)},
    risk_bd μ Y (fun ω => h.1 (V ω)) τ

theorem monotone_risk_gap_le_two_cal_error (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y V : Ω → ℝ) (hYmeas : Measurable Y) (hVmeas : Measurable V)
    (hYbin : ∀ ω, Y ω = 0 ∨ Y ω = 1) (hVmem : ∀ ω, V ω ∈ Set.Icc (0 : ℝ) 1)
    (hbdd : BddAbove (Set.range (fun J : {s : Set ℝ // s.OrdConnected} =>
      |∫ ω, (Y ω - V ω) * Set.indicator J.1 (fun _ => (1 : ℝ)) (V ω) ∂μ|)))
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    risk_bd μ Y V τ - monotone_wrapper_risk μ Y V τ
      ≤ 2 * cutoff_cal_error μ Y V := by sorry

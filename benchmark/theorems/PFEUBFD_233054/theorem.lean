import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory
open scoped ENNReal

def admissible_f_generator (f : ℝ → ℝ) : Prop :=
  ConvexOn ℝ (Set.Ici (0 : ℝ)) f ∧
    (∀ t ∈ Set.Ici (0 : ℝ), 0 ≤ f t) ∧
      f 1 = 0 ∧ HasDerivAt f 0 1

noncomputable def f_slope_at_infinity (f : ℝ → ℝ) : ℝ≥0∞ :=
  ⨆ t : {t : ℝ // 1 ≤ t}, ENNReal.ofReal (f t / t)

noncomputable def f_divergence {α : Type*} [MeasurableSpace α]
    (f : ℝ → ℝ) (μ ν : Measure α) : ℝ≥0∞ :=
  (∫⁻ x, ENNReal.ofReal (f ((ν.rnDeriv μ x).toReal)) ∂μ) +
    ν.singularPart μ Set.univ * f_slope_at_infinity f

noncomputable def gamma_f (f : ℝ → ℝ) (M : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ t : {t : ℝ // 1 ≤ t ∧ M ≤ ENNReal.ofReal (f t / t)},
    ENNReal.ofReal (t : ℝ)

noncomputable def iid_sample_measure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (n : ℕ) : Measure (Fin n → α) :=
  Measure.pi fun _ : Fin n => μ

def relative_accuracy_event {α : Type*} [MeasurableSpace α] {n : ℕ}
    (Zhat : (Fin n → α) → (Fin n → ℝ≥0∞) → ℝ≥0∞)
    (r : α → ℝ≥0∞) (Z : ℝ≥0∞) (ε : ℝ) : Set (Fin n → α) :=
  {x |
    ENNReal.ofReal (1 - ε) * Z ≤ Zhat x (fun i => Z * r (x i)) ∧
      Zhat x (fun i => Z * r (x i)) ≤ ENNReal.ofReal (1 + ε) * Z}

noncomputable def sample_complexity_scale {α : Type*} [MeasurableSpace α]
    (f : ℝ → ℝ) (μ ν : Measure α) (c ε δ : ℝ) : ℝ≥0∞ :=
  (gamma_f f (6 * f_divergence f μ ν / ENNReal.ofReal ε) *
      ENNReal.ofReal (Real.log (1 / δ)) / ENNReal.ofReal ε) ⊔
    ENNReal.ofReal (c ^ 2 / ε ^ 2)

def bounded_f_divergence_estimation : Prop :=
  ∃ C : ℝ≥0∞, 0 < C ∧ C ≠ ∞ ∧
    ∀ {α : Type*} [MeasurableSpace α]
      (f : ℝ → ℝ) (c ε δ : ℝ) (n : ℕ)
      (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ν ≪ μ →
      admissible_f_generator f →
      1 ≤ c →
      AntitoneOn (fun t => f t / t ^ 2) (Set.Ici c) →
      0 < ε → ε < 1 → 0 < δ → δ < 1 →
      C * sample_complexity_scale f μ ν c ε δ ≤ (n : ℝ≥0∞) →
      ∃ Zhat : (Fin n → α) → (Fin n → ℝ≥0∞) → ℝ≥0∞,
        Measurable (Function.uncurry Zhat) ∧
          ∀ Z : ℝ≥0∞, 0 < Z → Z ≠ ∞ →
            ENNReal.ofReal (1 - δ) ≤
              iid_sample_measure μ n
                (relative_accuracy_event Zhat (ν.rnDeriv μ) Z ε)

theorem ub_fdiv : bounded_f_divergence_estimation := by sorry

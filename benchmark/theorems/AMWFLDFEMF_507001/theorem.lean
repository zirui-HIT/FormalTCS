import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open scoped ENNReal BigOperators
open MeasureTheory

noncomputable def population_model_class_risk
    {Z F : Type*} [MeasurableSpace Z]
    (loss : F → Z → ℝ≥0∞) (P : Measure Z) : ℝ≥0∞ :=
  ⨅ f : F, ∫⁻ z, loss f z ∂P

noncomputable def empirical_model_class_risk
    {Z F : Type*} (loss : F → Z → ℝ≥0∞)
    {N : ℕ} (sample : Fin N → Z) : ℝ≥0∞ :=
  ⨅ f : F, (∑ i : Fin N, loss f (sample i)) / (N : ℝ≥0∞)

noncomputable def iid_sample_law
    {Z : Type*} [MeasurableSpace Z] (P : Measure Z) (N : ℕ) :
    Measure (Fin N → Z) :=
  Measure.pi (fun _ : Fin N ↦ P)

def valid_distribution_free_lower_bound
    {Z F Ξ : Type*} [MeasurableSpace Z] [MeasurableSpace Ξ]
    (loss : F → Z → ℝ≥0∞) (α : ℝ) (n : ℕ)
    (seedLaw : Measure Ξ) (_hseed : IsProbabilityMeasure seedLaw)
    (lowerBound : (Fin n → Z) → Ξ → ℝ≥0∞) : Prop :=
  ∀ (P : Measure Z), IsProbabilityMeasure P →
    MeasurableSet
        {outcome : (Fin n → Z) × Ξ |
          population_model_class_risk loss P ≥ lowerBound outcome.1 outcome.2} ∧
      (iid_sample_law P n).prod seedLaw
          {outcome |
            population_model_class_risk loss P ≥ lowerBound outcome.1 outcome.2} ≥
        ENNReal.ofReal (1 - α)

theorem high_complexity
    {Z F Ξ : Type*} [MeasurableSpace Z] [MeasurableSpace Ξ]
    (loss : F → Z → ℝ≥0∞) (hloss_finite : ∀ f z, loss f z ≠ ⊤)
    (α : ℝ) (n N : ℕ)
    (hα_lower : 0 < α) (hα_upper : α < 1)
    (hn : 1 ≤ n) (hnN : n ≤ N)
    (seedLaw : Measure Ξ) (hseed : IsProbabilityMeasure seedLaw)
    (lowerBound : (Fin n → Z) → Ξ → ℝ≥0∞)
    (hvalid : valid_distribution_free_lower_bound loss α n seedLaw hseed lowerBound)
    (hcomparison_measurable : MeasurableSet
      {outcome : (Fin N → Z) × Ξ |
        lowerBound (fun i ↦ outcome.1 (Fin.castLE hnN i)) outcome.2 >
          empirical_model_class_risk loss outcome.1})
    (P : Measure Z) (hP : IsProbabilityMeasure P) :
    (iid_sample_law P N).prod seedLaw
        {outcome |
          lowerBound (fun i ↦ outcome.1 (Fin.castLE hnN i)) outcome.2 >
            empirical_model_class_risk loss outcome.1} ≤
      ENNReal.ofReal α +
        (n : ℝ≥0∞) ^ 2 / (2 * (N : ℝ≥0∞)) := by
  sorry

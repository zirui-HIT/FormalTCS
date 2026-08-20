import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.Support

open MeasureTheory
open scoped BigOperators

abbrev feature_vector (d : ℕ) := Fin d → ℝ

noncomputable def extended_distribution {d : ℕ}
    (μ : ProbabilityMeasure (feature_vector d)) : ProbabilityMeasure (feature_vector d) :=
  ProbabilityMeasure.pi fun j => μ.map (measurable_pi_apply j).aemeasurable

def mix_features {d : ℕ} (S : Finset (Fin d))
    (x y : feature_vector d) : feature_vector d :=
  fun j => if j ∈ S then x j else y j

noncomputable def interventional_value {d : ℕ}
    (ν : ProbabilityMeasure (feature_vector d)) (f : feature_vector d → ℝ)
    (S : Finset (Fin d)) (x : feature_vector d) : ℝ :=
  ∫ y, f (mix_features S x y) ∂(ν : Measure (feature_vector d))

noncomputable def shap_value {d : ℕ}
    (ν : ProbabilityMeasure (feature_vector d)) (f : feature_vector d → ℝ)
    (i : Fin d) (x : feature_vector d) : ℝ :=
  (d : ℝ)⁻¹ * ∑ S ∈ (Finset.univ.erase i).powerset,
    (Nat.choose (d - 1) S.card : ℝ)⁻¹ *
      (interventional_value ν f (insert i S) x - interventional_value ν f S x)

noncomputable def aggregate_shap_value {d : ℕ}
    (ν : ProbabilityMeasure (feature_vector d)) (f : feature_vector d → ℝ)
    (i : Fin d) : ℝ :=
  ∫ x, |shap_value ν f i x| ∂(ν : Measure (feature_vector d))

def is_determined_except_on {d : ℕ}
    (ν : ProbabilityMeasure (feature_vector d)) (i : Fin d)
    (g : feature_vector d → ℝ) : Prop :=
  Measurable g ∧
    ∀ x, x ∈ (ν : Measure (feature_vector d)).support →
      ∀ y, y ∈ (ν : Measure (feature_vector d)).support →
        (∀ j, j ≠ i → x j = y j) → g x = g y

theorem small_mu_star_shap_allows_discard_feature {d : ℕ}
    (μ : ProbabilityMeasure (feature_vector d)) (f : feature_vector d → ℝ)
    (i : Fin d) (ε : ℝ) (hε : 0 < ε) (hf : Measurable f)
    (hf_range : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (haggregate : aggregate_shap_value (extended_distribution μ) f i ≤ ε) :
    ∃ g : feature_vector d → ℝ,
      is_determined_except_on (extended_distribution μ) i g ∧
      (∫ x, (f x - g x) ^ 2
        ∂(extended_distribution μ : Measure (feature_vector d))) < (d : ℝ) ^ 2 * ε := by sorry

import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open scoped BigOperators Interval
open MeasureTheory Set

def coordinate_laws_supported {n : ℕ}
    (D : Fin n → ProbabilityMeasure ℝ) : Prop :=
  ∀ i, ∀ᵐ y ∂(D i : Measure ℝ), y ∈ Icc (0 : ℝ) 1

noncomputable def distribution_means {n : ℕ}
    (D : Fin n → ProbabilityMeasure ℝ) : Fin n → ℝ :=
  fun i ↦ ∫ y, y ∂(D i : Measure ℝ)

noncomputable def vector_mean {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (∑ i, x i) / (n : ℝ)

noncomputable def vector_variance {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (∑ i, (x i) ^ 2) / (n : ℝ) - (vector_mean x) ^ 2

noncomputable def bernoulli_weight {n : ℕ}
    (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  x i * (∫ t in (0 : ℝ)..1,
    ∏ k ∈ Finset.univ.filter (fun k : Fin n ↦ k ≠ i), (1 - t * x k))
    + (n : ℝ)⁻¹ * ∏ k, (1 - x k)

noncomputable def strategy_value {n : ℕ}
    (D : Fin n → ProbabilityMeasure ℝ)
    (S : (Fin n → ℝ) → Fin n → ℝ) : ℝ :=
  ∫ y, ∑ i, distribution_means D i * S y i
    ∂(ProbabilityMeasure.pi D : Measure (Fin n → ℝ))

theorem adaptive_weighted_averaging_lower_bounds {n : ℕ} (hn : 2 ≤ n)
    (D : Fin n → ProbabilityMeasure ℝ)
    (hD : coordinate_laws_supported D) :
    (vector_mean (distribution_means D) +
        (n : ℝ) / ((n : ℝ) - 1) * vector_variance (distribution_means D) ≤
      strategy_value D bernoulli_weight) ∧
    (vector_mean (distribution_means D) +
        (1 - ∏ k, (1 - distribution_means D k)) *
          (vector_variance (distribution_means D) /
            vector_mean (distribution_means D)) ≤
      strategy_value D bernoulli_weight) := by
  sorry

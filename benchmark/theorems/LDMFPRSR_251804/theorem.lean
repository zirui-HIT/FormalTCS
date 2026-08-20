import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory
open Asymptotics

noncomputable def standard_gaussian_measure : Measure ℝ :=
  gaussianReal 0 1

noncomputable def isotropic_gaussian_measure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n ↦ standard_gaussian_measure)

noncomputable def gaussian_scale_mixture (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.map
    (fun z : ℝ × (Fin n → ℝ) ↦ fun i ↦ z.1 * z.2 i)
    (standard_gaussian_measure.prod (isotropic_gaussian_measure n))

noncomputable def origin_contamination {Ω : Type*} [MeasurableSpace Ω] [Zero Ω]
    (α : NNReal) (Q : Measure Ω) : Measure Ω :=
  ((↑(1 - α) : ENNReal) • Q) + ((↑α : ENNReal) • Measure.dirac 0)

noncomputable def iid_product_measure {Ω : Type*} [MeasurableSpace Ω]
    (m : ℕ) (μ : Measure Ω) : Measure (Fin m → Ω) :=
  Measure.pi (fun _ : Fin m ↦ μ)

noncomputable def sample_polynomial_observable {n m : ℕ}
    (p : MvPolynomial (Fin m × Fin n) ℝ) (x : Fin m → Fin n → ℝ) : ℝ :=
  p.eval (fun ij ↦ x ij.1 ij.2)

noncomputable def sample_polynomial_expectation {n m : ℕ}
    (μ : Measure (Fin n → ℝ)) (p : MvPolynomial (Fin m × Fin n) ℝ) : ℝ :=
  ∫ x, sample_polynomial_observable p x ∂iid_product_measure m μ

noncomputable def sample_polynomial_variance {n m : ℕ}
    (μ : Measure (Fin n → ℝ)) (p : MvPolynomial (Fin m × Fin n) ℝ) : ℝ :=
  variance (sample_polynomial_observable p) (iid_product_measure m μ)

noncomputable def low_degree_advantage (n m k : ℕ)
    (P Q : Measure (Fin n → ℝ)) : ℝ :=
  sSup {r : ℝ | ∃ p : MvPolynomial (Fin m × Fin n) ℝ,
    p.totalDegree ≤ k ∧
    0 < sample_polynomial_variance Q p ∧
    r = |sample_polynomial_expectation P p - sample_polynomial_expectation Q p| /
      Real.sqrt (sample_polynomial_variance Q p)}

def gaussian_mean_variance_constant (C : ℝ) : Prop :=
  ∀ (d : ℕ) (q : Polynomial ℝ),
    q.natDegree ≤ d → q.coeff 0 = 0 →
      |∫ x, q.eval x ∂standard_gaussian_measure| ≤
        C * Real.sqrt ((d : ℝ) * variance (fun x ↦ q.eval x) standard_gaussian_measure)

theorem lda_bound_is_big_o (C : ℝ) (hCpos : 0 < C)
    (hC : gaussian_mean_variance_constant C)
    (α : ℕ → NNReal) (m k : ℕ → ℕ) (hα : ∀ n, α n ≤ 1)
    (hdegree : (fun n ↦ (k n : ℝ)) =O[Filter.atTop]
      (fun n ↦ 1 / ((α n : ℝ) ^ 2 * (m n : ℝ)))) :
    (fun n ↦ low_degree_advantage n (m n) (k n)
      (origin_contamination (α n) (gaussian_scale_mixture n))
      (gaussian_scale_mixture n)) =O[Filter.atTop]
      (fun _ : ℕ ↦ (1 : ℝ)) := by sorry

import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.Basic

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory Metric ProbabilityTheory
open scoped ENNReal NNReal

abbrev ngca_sample_space (n d : ℕ) := Fin n → EuclideanSpace ℝ (Fin d)

abbrev ngca_unit_sphere (d : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1

noncomputable def ngca_uniform_sphere_measure (d : ℕ) : Measure (ngca_unit_sphere d) :=
  let σ := Measure.toSphere (volume : Measure (EuclideanSpace ℝ (Fin d)))
  (σ Set.univ)⁻¹ • σ

abbrev ngca_polynomial (n d : ℕ) := MvPolynomial (Fin n × Fin d) ℝ

noncomputable def ngca_polynomial_eval {n d : ℕ} (p : ngca_polynomial n d)
    (x : ngca_sample_space n d) : ℝ :=
  MvPolynomial.eval (fun ij => x ij.1 ij.2) p

noncomputable def ngca_sign (t : ℝ) : ℝ :=
  if 0 ≤ t then 1 else 0

noncomputable def ngca_polynomial_test {n d : ℕ} (p : ngca_polynomial n d)
    (x : ngca_sample_space n d) : ℝ :=
  ngca_sign (ngca_polynomial_eval p x)

noncomputable def ngca_standard_vector_measure (d : ℕ) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  Measure.map
    ((EuclideanSpace.equiv (Fin d) ℝ :
      EuclideanSpace ℝ (Fin d) ≃L[ℝ] (Fin d → ℝ)).symm)
    (Measure.pi (fun _ : Fin d => gaussianReal 0 1))

noncomputable def ngca_hidden_sample_measure {d : ℕ} (A : Measure ℝ)
    (v : ngca_unit_sphere d) : Measure (EuclideanSpace ℝ (Fin d)) :=
  Measure.map
    (fun (zξ : EuclideanSpace ℝ (Fin d) × ℝ) =>
      zξ.1 - inner ℝ zξ.1 (v : EuclideanSpace ℝ (Fin d)) •
          (v : EuclideanSpace ℝ (Fin d)) +
        zξ.2 • (v : EuclideanSpace ℝ (Fin d)))
    ((ngca_standard_vector_measure d).prod A)

noncomputable def ngca_iid_samples {d : ℕ} (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) :
    Measure (ngca_sample_space n d) :=
  Measure.pi (fun _ : Fin n => μ)

noncomputable def ngca_standard_samples (n d : ℕ) : Measure (ngca_sample_space n d) :=
  ngca_iid_samples n (ngca_standard_vector_measure d)

noncomputable def ngca_hidden_samples {d : ℕ} (n : ℕ) (A : Measure ℝ)
    (v : ngca_unit_sphere d) : Measure (ngca_sample_space n d) :=
  ngca_iid_samples n (ngca_hidden_sample_measure A v)

def ngca_matches_moments (A : Measure ℝ) (m : ℕ) : Prop :=
  ∀ j : ℕ, j ≤ m →
    moment id j A = moment id j (gaussianReal 0 1)

noncomputable def ngca_acceptance {n d : ℕ} (μ : Measure (ngca_sample_space n d))
    (p : ngca_polynomial n d) : ℝ :=
  ∫ x, ngca_polynomial_test p x ∂μ

noncomputable def ngca_averaged_gap {n d : ℕ} (A : Measure ℝ)
    (p : ngca_polynomial n d) : ℝ :=
  |(∫ v, ngca_acceptance (ngca_hidden_samples n A v) p
        ∂ngca_uniform_sphere_measure d) -
    ngca_acceptance (ngca_standard_samples n d) p|

theorem ngca_main_result :
    ∃ Cstar : ℝ, 8 < Cstar ∧
      ∀ (cstar : ℝ) (d k n m : ℕ) (p : ngca_polynomial n d) (A : Measure ℝ),
        0 < cstar → cstar < 1 / 4 →
        0 < d → 0 < k → 0 < n → 0 < m → Even m →
        ((max k m : ℕ) : ℝ) < (d : ℝ) ^ (cstar / Cstar) →
        (n : ℝ) < (d : ℝ) ^ ((1 / 4 - cstar) * (m : ℝ)) →
        p.totalDegree ≤ k → IsProbabilityMeasure A → ngca_matches_moments A m →
        ngca_averaged_gap A p ≤ 0.11 := by sorry

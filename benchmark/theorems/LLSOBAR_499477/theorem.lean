import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Gaussian.Multivariate

set_option linter.all false
set_option maxHeartbeats 500000

abbrev real_vector (n : ℕ) := Fin n → ℝ

abbrev integer_vector (n : ℕ) := Fin n → ℤ

def cast_integer_vector {n : ℕ} (z : integer_vector n) : real_vector n :=
  fun i ↦ (z i : ℝ)

noncomputable def vector_euclidean_norm {n : ℕ} (x : real_vector n) : ℝ :=
  Real.sqrt (∑ i, (x i) ^ 2)

noncomputable def matrix_singular_values {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) : ℕ →₀ ℝ :=
  (Matrix.toEuclideanLin S).singularValues

def apply_sketch {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (x : real_vector n) : real_vector r :=
  Matrix.mulVec A x

def row_span {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ) :
    Submodule ℝ (real_vector n) :=
  Submodule.span ℝ (Set.range A.row)

def orthonormal_rows {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ) : Prop :=
  ∀ i j, ∑ k, A i k * A j k = if i = j then 1 else 0

def rational_entries {n r : ℕ} (M : Matrix (Fin r) (Fin n) ℝ) : Prop :=
  ∀ i j, ∃ q : ℚ, M i j = (q : ℝ)

def orthogonal_integer_lattice {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ) :
    Set (integer_vector n) :=
  {z | ∀ i, ∑ j, A i j * (z j : ℝ) = 0}

def embedded_orthogonal_lattice {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ) :
    Set (real_vector n) :=
  cast_integer_vector '' orthogonal_integer_lattice A

noncomputable def largest_successive_minimum {n r : ℕ}
    (A : Matrix (Fin r) (Fin n) ℝ) : ℝ :=
  sInf {R : ℝ |
    0 ≤ R ∧
      Submodule.span ℝ
          {x : real_vector n |
            x ∈ embedded_orthogonal_lattice A ∧ vector_euclidean_norm x ≤ R} =
        Submodule.span ℝ (embedded_orthogonal_lattice A)}

noncomputable def centered_discrete_gaussian {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ)
    (D : MeasureTheory.ProbabilityMeasure (integer_vector n)) : Prop :=
  ∃ Z : ℝ, 0 < Z ∧ ∀ z : integer_vector n,
    (D : MeasureTheory.Measure (integer_vector n)).real {z} =
      Real.exp
          (-(dotProduct (cast_integer_vector z)
              (Matrix.mulVec (S.transpose * S)⁻¹ (cast_integer_vector z))) / 2) /
        Z

noncomputable def integer_noisy_law {n : ℕ}
    (D I : MeasureTheory.ProbabilityMeasure (integer_vector n)) :
    MeasureTheory.Measure (real_vector n) :=
  ((D : MeasureTheory.Measure (integer_vector n)).prod
      (I : MeasureTheory.Measure (integer_vector n))).map
    (fun p ↦ cast_integer_vector (p.1 + p.2))

noncomputable def continuous_gaussian_law {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) : MeasureTheory.Measure (real_vector n) :=
  (ProbabilityTheory.multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin n)) (S.transpose * S)).map
    (fun x : EuclideanSpace ℝ (Fin n) ↦ fun i ↦ x i)

noncomputable def continuous_noisy_law {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ)
    (I : MeasureTheory.ProbabilityMeasure (integer_vector n)) :
    MeasureTheory.Measure (real_vector n) :=
  ((continuous_gaussian_law S).prod
      (I : MeasureTheory.Measure (integer_vector n))).map
    (fun p ↦ p.1 + cast_integer_vector p.2)

def sketch_success_probability {n r : ℕ}
    (μ : MeasureTheory.Measure (real_vector n))
    (f : real_vector n → ℤ) (A : Matrix (Fin r) (Fin n) ℝ)
    (g : real_vector r → ℤ) : ℝ :=
  μ.real {x | g (apply_sketch A x) = f x}

def smooth_between {n : ℕ} (δ : ℝ) (f : real_vector n → ℤ)
    (μ ν : MeasureTheory.Measure (real_vector n)) : Prop :=
  (μ.prod ν).real {p | f p.1 ≠ f p.2} ≤ δ

theorem lifting
    {n r : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin r) (Fin n) ℝ)
    (D I : MeasureTheory.ProbabilityMeasure (integer_vector n))
    (f : real_vector n → ℤ) (g : real_vector r → ℤ)
    (C δ : ℝ)
    (hn : 1 < n) (hrn : r ≤ n)
    (hC : 0 < C) (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (hrate : 1 / Real.rpow (n : ℝ) C ≤ δ / 3)
    (hD : centered_discrete_gaussian S D)
    (hcov : (S.transpose * S).det ≠ 0)
    (hfinite : (Set.range f).Finite)
    (horth : orthonormal_rows A)
    (hrat : ∃ M : Matrix (Fin r) (Fin n) ℝ,
      rational_entries M ∧ row_span M = row_span A)
    (hdisc : sketch_success_probability (integer_noisy_law D I) f A g ≥
      1 - δ / 3)
    (hlattice : largest_successive_minimum A ≤
      matrix_singular_values S (n - 1) / (10 * C * Real.log (n : ℝ)))
    (hscale :
      Real.rpow (n : ℝ) (6 * C) ≥ matrix_singular_values S 0 ∧
      matrix_singular_values S 0 ≥ matrix_singular_values S (n - 1) ∧
      matrix_singular_values S (n - 1) ≥ Real.rpow (n : ℝ) (5 * C + 3))
    (hsmooth : smooth_between (δ / 3) f
      (integer_noisy_law D I) (continuous_noisy_law S I)) :
    ∃ A' : Matrix (Fin (4 * r)) (Fin n) ℝ,
      ∃ h : real_vector (4 * r) → ℤ,
        sketch_success_probability (continuous_noisy_law S I) f A' h ≥
          1 - δ := by sorry

import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory ProbabilityTheory

noncomputable section

abbrev decoupled_variables (q m : ℕ) (Ω : Type*) :=
  Fin q → Fin m → Ω → ℝ

abbrev matrix_chaos_coefficients (q m d₁ d₂ : ℕ) :=
  (Fin q → Fin m) → Matrix (Fin d₁) (Fin d₂) ℝ

noncomputable def matrix_spectral_norm {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ]
    (M : Matrix ι κ ℝ) : ℝ :=
  ‖(Matrix.toEuclideanLin M).toContinuousLinearMap‖

noncomputable def matrix_chaos_value {q m d₁ d₂ : ℕ} {Ω : Type*}
    (h : decoupled_variables q m Ω)
    (A : matrix_chaos_coefficients q m d₁ d₂) (ω : Ω) :
    Matrix (Fin d₁) (Fin d₂) ℝ :=
  ∑ i : Fin q → Fin m, (∏ k : Fin q, h k (i k) ω) • A i

noncomputable def sigma_flattening {q m d₁ d₂ : ℕ}
    (A : matrix_chaos_coefficients q m d₁ d₂) (R : Finset (Fin q)) :
    Matrix (Fin d₁ × (↥R → Fin m))
      (Fin d₂ × (↥((Finset.univ : Finset (Fin q)) \ R) → Fin m)) ℝ :=
  fun r c =>
    A (fun k =>
      if hk : k ∈ R then r.2 ⟨k, hk⟩
      else c.2 ⟨k, by simp [hk]⟩) r.1 c.1

noncomputable def sigma_parameter {q m d₁ d₂ : ℕ}
    (A : matrix_chaos_coefficients q m d₁ d₂) : ℝ :=
  ((Finset.univ : Finset (Fin q)).powerset).sup'
    (by exact ⟨∅, by simp⟩)
    (fun R => matrix_spectral_norm (sigma_flattening A R))

noncomputable def random_l1_norm {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  ∫ ω, |X ω| ∂μ

noncomputable def random_lp_norm {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (p : ℝ) (μ : Measure Ω) : ℝ :=
  ENNReal.toReal (eLpNorm X (ENNReal.ofReal (max 1 p)) μ)

def has_subgaussian_psi2_bound {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop :=
  0 < K ∧ HasSubgaussianMGF X ⟨K ^ 2, sq_nonneg K⟩ μ

noncomputable def subgaussian_psi2_norm {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  sInf {K : ℝ | has_subgaussian_psi2_bound X μ K}

def has_finite_subgaussian_psi2_norm {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∃ K : ℝ, has_subgaussian_psi2_bound X μ K

noncomputable def log_dimension_factor (q d m : ℕ) : ℝ :=
  Real.rpow (Real.log ((d + m : ℕ) : ℝ)) ((q : ℝ) / 2)

noncomputable def expected_matrix_chaos_norm {q m d₁ d₂ : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (h : decoupled_variables q m Ω)
    (A : matrix_chaos_coefficients q m d₁ d₂) : ℝ :=
  ∫ ω, matrix_spectral_norm (matrix_chaos_value h A ω) ∂μ

def admissible_decoupled_matrix_chaos {Ω : Type*} [MeasurableSpace Ω]
    (q m d₁ d₂ : ℕ) (μ : Measure Ω) (X : Ω → ℝ)
    (h : decoupled_variables q m Ω)
    (A : matrix_chaos_coefficients q m d₁ d₂) : Prop :=
  0 < q ∧ 0 < m ∧ 0 < d₁ ∧ 0 < d₂ ∧
  IsProbabilityMeasure μ ∧
  iIndepFun (fun p : Fin q × Fin m => h p.1 p.2) μ ∧
  (∀ k i, IdentDistrib (h k i) X μ μ) ∧
  Integrable X μ ∧
  (∫ ω, X ω ∂μ) = 0 ∧
  Integrable (fun ω => matrix_spectral_norm (matrix_chaos_value h A ω)) μ

def iterated_nck_bounds {q m d₁ d₂ : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (C : ℝ) (μ : Measure Ω) (X : Ω → ℝ)
    (h : decoupled_variables q m Ω)
    (A : matrix_chaos_coefficients q m d₁ d₂) : Prop :=
  random_l1_norm X μ ^ q * sigma_parameter A ≤
      C * expected_matrix_chaos_norm μ h A ∧
  (has_finite_subgaussian_psi2_norm X μ →
    expected_matrix_chaos_norm μ h A ≤
        C * subgaussian_psi2_norm X μ ^ q *
          log_dimension_factor q (max d₁ d₂) m * sigma_parameter A) ∧
  (eLpNorm X (ENNReal.ofReal (max 1 (Real.log (m : ℝ)))) μ ≠ ⊤ →
    expected_matrix_chaos_norm μ h A ≤
        C * random_lp_norm X (Real.log (m : ℝ)) μ ^ q *
          log_dimension_factor q (max d₁ d₂) m * sigma_parameter A)

def iterated_nck_at_order (q : ℕ) (C : ℝ) : Prop :=
  ∀ (m d₁ d₂ : ℕ) (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (h : decoupled_variables q m Ω)
    (A : matrix_chaos_coefficients q m d₁ d₂),
    admissible_decoupled_matrix_chaos q m d₁ d₂ μ X h A →
      iterated_nck_bounds C μ X h A

theorem iterated_nck :
    ∀ q : ℕ, 0 < q → ∃ C : ℝ, 0 < C ∧ iterated_nck_at_order q C := by sorry

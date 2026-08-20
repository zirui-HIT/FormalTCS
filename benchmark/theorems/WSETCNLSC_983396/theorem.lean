import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Basic

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory

abbrev real_tensor (n k : ℕ) : Type := (Fin k → Fin n) → ℝ

def tensor_mode_unfold {n k : ℕ} (T : real_tensor n k) (s : Fin k) :
    Matrix (Fin n) ({j : Fin k // j ≠ s} → Fin n) ℝ :=
  fun i js => T fun j => if h : j = s then i else js ⟨j, h⟩

def first_mode_unfold {n d : ℕ} (T : real_tensor n (d + 1)) :
    Matrix (Fin n) ({j : Fin (d + 1) // j ≠ 0} → Fin n) ℝ :=
  tensor_mode_unfold T 0

noncomputable def tensor_frobenius_norm {n k : ℕ} (T : real_tensor n k) : ℝ :=
  Real.sqrt (∑ i, (T i) ^ 2)

def tensor_symmetric {n k : ℕ} (T : real_tensor n k) : Prop :=
  ∀ (σ : Equiv.Perm (Fin k)) (i : Fin k → Fin n), T (fun j => i (σ j)) = T i

noncomputable def matrix_singular_values {m n : Type*}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : ℕ →₀ ℝ :=
  A.toEuclideanLin.singularValues

noncomputable def matrix_right_singular_vector_basis {m n : Type*}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) :
    OrthonormalBasis (Fin (Fintype.card n)) ℝ (EuclideanSpace ℝ n) :=
  A.toEuclideanLin.isSymmetric_adjoint_comp_self.eigenvectorBasis finrank_euclideanSpace

noncomputable def matrix_left_singular_vector {m n : Type*}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (i : Fin (Fintype.card n)) : EuclideanSpace ℝ m :=
  (matrix_singular_values A i)⁻¹ • A.toEuclideanLin (matrix_right_singular_vector_basis A i)

noncomputable def matrix_left_leverage_score {m n : Type*}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (i : m) : ℝ :=
  ∑ j : Fin (Fintype.card n),
    if 0 < matrix_singular_values A j then (matrix_left_singular_vector A j i) ^ 2 else 0

noncomputable def matrix_right_leverage_score {m n : Type*}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (j : n) : ℝ :=
  ∑ i : Fin (Fintype.card n),
    if 0 < matrix_singular_values A i then (matrix_right_singular_vector_basis A i j) ^ 2 else 0

noncomputable def matrix_incoherent {m n : Type*}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (μ₁ μ₂ : ℝ) : Prop :=
  (∀ i, matrix_left_leverage_score A i ≤ μ₁ * (A.rank : ℝ) / (Fintype.card m : ℝ)) ∧
    ∀ j, matrix_right_leverage_score A j ≤ μ₂ * (A.rank : ℝ) / (Fintype.card n : ℝ)

noncomputable def tensor_incoherent {n k : ℕ} (T : real_tensor n k) (μ₁ μ₂ : ℝ) : Prop :=
  ∀ s : Fin k, matrix_incoherent (tensor_mode_unfold T s) μ₁ μ₂

noncomputable def matrix_condition_number {m n : Type*}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (r : ℕ) : ℝ :=
  matrix_singular_values A 0 / matrix_singular_values A (r - 1)

noncomputable def tensor_project {n k : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (T : real_tensor n k) : real_tensor n k := by
  classical
  exact fun i => ∑ j : Fin k → Fin n, (∏ s : Fin k, Q (i s) (j s)) * T j

structure wedge_sample_index (n d : ℕ) where
  row₁ : Fin n
  column : {s : Fin (d + 1) // s ≠ 0} → Fin n
  row₂ : Fin n
  ordered : row₁.val ≤ row₂.val

noncomputable def wedge_sampled_gram {n d : ℕ} (T : real_tensor n (d + 1)) (p : ℝ)
    (W : wedge_sample_index n d → Bool) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∑ ell,
    if h : i.val ≤ j.val then
      if W ⟨i, ell, j, h⟩ then
        p⁻¹ * first_mode_unfold T i ell * first_mode_unfold T j ell
      else 0
    else
      if W ⟨j, ell, i, Nat.le_of_lt (Nat.lt_of_not_ge h)⟩ then
        p⁻¹ * first_mode_unfold T i ell * first_mode_unfold T j ell
      else 0

def leading_spectral_projector {n : ℕ} (Z Q : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) : Prop :=
  Z.transpose = Z ∧ Q.transpose = Q ∧ Q * Q = Q ∧ Q.rank = r ∧ Q * Z = Z * Q ∧
    ∀ x y : Fin n → ℝ,
      Matrix.mulVec Q x = x → Matrix.mulVec Q y = 0 →
        dotProduct x x = 1 → dotProduct y y = 1 →
          dotProduct x (Matrix.mulVec Z x) ≥ dotProduct y (Matrix.mulVec Z y)

noncomputable def uniform_sampled_observation {n d : ℕ} (T : real_tensor n (d + 1)) (q : ℝ)
    (S : (Fin (d + 1) → Fin n) → Bool) : real_tensor n (d + 1) :=
  fun i => if S i then q⁻¹ * T i else 0

def algorithm2_joint_sampling_law {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n d : ℕ} (p q : ℝ) (W : Ω → wedge_sample_index n d → Bool)
    (S : Ω → (Fin (d + 1) → Fin n) → Bool) : Prop :=
  (∀ w s, MeasurableSet {ω | W ω = w ∧ S ω = s}) ∧
    ∀ w s, μ.real {ω | W ω = w ∧ S ω = s} =
      (∏ i : Fin n, ∏ ell : {u : Fin (d + 1) // u ≠ 0} → Fin n,
        ∏ j : {j : Fin n // i.val ≤ j.val},
          if w ⟨i, ell, j.1, j.2⟩ then p else 1 - p) *
      ∏ u : Fin (d + 1) → Fin n, if s u then q else 1 - q

structure wedge_spectral_estimator (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    (n d r : ℕ) (T : real_tensor n (d + 1)) (p q : ℝ) where
  wedgeSample : Ω → wedge_sample_index n d → Bool
  uniformSample : Ω → (Fin (d + 1) → Fin n) → Bool
  joint_sampling_law : algorithm2_joint_sampling_law μ p q wedgeSample uniformSample
  projection : Ω → Matrix (Fin n) (Fin n) ℝ
  projection_factorization :
    ∃ F : (wedge_sample_index n d → Bool) → Matrix (Fin n) (Fin n) ℝ,
      projection = fun ω => F (wedgeSample ω)
  projection_measurable : ∀ i j, Measurable (fun ω => projection ω i j)
  projection_is_leading : ∀ ω,
    leading_spectral_projector (wedge_sampled_gram T p (wedgeSample ω)) (projection ω) r
  uniformObservation : Ω → real_tensor n (d + 1)
  uniformObservation_eq : ∀ ω,
    uniformObservation ω = uniform_sampled_observation T q (uniformSample ω)

noncomputable def wedge_spectral_output {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {n d r : ℕ}
    {T : real_tensor n (d + 1)} {p q : ℝ}
    (E : wedge_spectral_estimator Ω μ n d r T p q) (ω : Ω) : real_tensor n (d + 1) :=
  tensor_project (E.projection ω) (E.uniformObservation ω)

noncomputable def wedge_sampling_threshold (C₀ κ a μ₁ μ₂ : ℝ) (n d r : ℕ) : ℝ :=
  C₀ * κ ^ 4 * a * μ₁ * μ₂ * (r : ℝ) ^ 2 * Real.log (n : ℝ) /
    (n : ℝ) ^ (d + 1)

noncomputable def uniform_sampling_threshold (a : ℝ) (n d : ℕ) : ℝ :=
  a * (d : ℝ) * Real.log (n : ℝ) / (n : ℝ) ^ (d + 1)

noncomputable def wedge_residual_scale (κ a μ₁ μ₂ p : ℝ) (n d r : ℕ) : ℝ :=
  κ ^ 2 * Real.sqrt
    (a * μ₁ * μ₂ * (r : ℝ) ^ 2 * Real.log (n : ℝ) /
      (p * (n : ℝ) ^ (d + 1)))

noncomputable def wedge_bias_scale (κ a μ₁ μ₂ p : ℝ) (n d r : ℕ) : ℝ :=
  ((d + 1 : ℕ) : ℝ) * Real.sqrt (r : ℝ) * wedge_residual_scale κ a μ₁ μ₂ p n d r

noncomputable def uniform_noise_scale (κ a μ₁ μ₂ q : ℝ) (n d r : ℕ) : ℝ :=
  (2 : ℝ) ^ (d + 1) *
    Real.rpow (r : ℝ) ((3 : ℝ) / 2 + ((d + 1 : ℕ) : ℝ) / 2) *
    κ ^ (2 * (d + 1)) *
    Real.sqrt
      (a * (d : ℝ) * μ₁ ^ (d + 2) * μ₂ * Real.log (n : ℝ) /
        (q * (n : ℝ) ^ (d + 1)))

noncomputable def spectral_error_scale (κ a μ₁ μ₂ p q : ℝ) (n d r : ℕ) : ℝ :=
  wedge_bias_scale κ a μ₁ μ₂ p n d r + uniform_noise_scale κ a μ₁ μ₂ q n d r

noncomputable def polynomial_failure_scale (K : ℝ) (n : ℕ) (a : ℝ) : ℝ :=
  K * Real.rpow (n : ℝ) (-a)

theorem spectral_method_frobenius_bound :
    ∃ C₀ C K : ℝ, 0 < C₀ ∧ 0 < C ∧ 0 ≤ K ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (n d r : ℕ) (μ₁ μ₂ κ a p q : ℝ) (T : real_tensor n (d + 1))
        (E : wedge_spectral_estimator Ω μ n d r T p q),
        2 ≤ n → 1 ≤ d → 0 < r → 0 < μ₁ → 0 < μ₂ → 1 ≤ κ → 2 ≤ a →
        0 < p → p ≤ 1 → 0 < q → q ≤ 1 →
        tensor_symmetric T → tensor_incoherent T μ₁ μ₂ →
        (first_mode_unfold T).rank = r →
        matrix_condition_number (first_mode_unfold T) r = κ →
        p ≥ wedge_sampling_threshold C₀ κ a μ₁ μ₂ n d r →
        q ≥ uniform_sampling_threshold a n d →
        μ.real
            {ω | tensor_frobenius_norm (T - wedge_spectral_output E ω) ≤
              C * spectral_error_scale κ a μ₁ μ₂ p q n d r * tensor_frobenius_norm T} ≥
          1 - polynomial_failure_scale K n a := by sorry

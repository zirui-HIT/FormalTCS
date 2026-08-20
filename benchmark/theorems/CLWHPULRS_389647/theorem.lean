import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option linter.all false
set_option maxHeartbeats 500000

def nondegenerate_real_matrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  Function.Injective (Matrix.mulVec A) ∧ ∀ i, A i ≠ 0

noncomputable def leverage_scores {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) : Fin m → ℝ :=
  fun i => dotProduct (A i)
    (Matrix.mulVec ((Matrix.transpose A * A)⁻¹) (A i))

noncomputable def alpha_p (p : ℝ) : ℝ :=
  2 / (p - 2)

def is_lewis_weight_vector {m n : ℕ} (p : ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (w : Fin m → ℝ) : Prop :=
  (∀ i, 0 < w i) ∧
    w = leverage_scores
      (Matrix.diagonal (fun i => (w i) ^ (1 / 2 - 1 / p)) * A)

def is_epsilon_estimate {m : ℕ} (ε : ℝ)
    (σ w : Fin m → ℝ) : Prop :=
  (∀ i, 0 < w i) ∧
    ∀ i, (1 - ε) * σ i ≤ w i ∧ w i ≤ (1 + ε) * σ i

structure dual_relative_smoothness_run (m : ℕ) where
  iterations : ℕ
  iterates : ℕ → Fin m → ℝ
  output : Fin m → ℝ
  diagonalScalings : ℕ → Fin m → ℝ
  computedLeverageScores : ℕ → Fin m → ℝ

def each_iteration_computes_leverage_scores {m n : ℕ} (p : ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (run : dual_relative_smoothness_run m) : Prop :=
  ∀ t, t < run.iterations →
    (∀ i, run.diagonalScalings t i =
      (run.iterates t i) ^ (1 / 2 : ℝ)) ∧
    run.computedLeverageScores t =
      leverage_scores
        (Matrix.diagonal (run.diagonalScalings t) * A)

noncomputable def dual_relative_smoothness_execution {m n : ℕ} (p ε : ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (w : Fin m → ℝ)
    (run : dual_relative_smoothness_run m) : Prop :=
  0 < run.iterations ∧
    (∀ i, run.iterates 0 i =
      (leverage_scores A i) ^ (1 / (1 + alpha_p p))) ∧
    (∀ t, t < run.iterations → ∀ i, 0 < run.iterates t i) ∧
    each_iteration_computes_leverage_scores p A run ∧
    (∀ t, t + 1 < run.iterations → ∀ i,
      run.iterates (t + 1) i =
        (1 + (((run.computedLeverageScores t i /
          (run.iterates t i) ^ (1 + alpha_p p)) ^
            (1 / alpha_p p)) - 1) / p ^ 2) * run.iterates t i) ∧
    run.output = (fun i =>
      (run.iterates (run.iterations - 1) i) ^ (1 + alpha_p p)) ∧
    is_epsilon_estimate ε w run.output

noncomputable def dual_iteration_scale (m : ℕ) (p ε : ℝ) : ℝ :=
  p ^ 2 * max 1 (Real.log (((m : ℝ) * p * alpha_p p) / ε))

theorem relative_smoothness_dual_main :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m n : ℕ) (p ε : ℝ) (A : Matrix (Fin m) (Fin n) ℝ),
        2 < p → 0 < ε → nondegenerate_real_matrix A →
          ∃ σ : Fin m → ℝ,
            is_lewis_weight_vector p A σ ∧
            (∀ τ : Fin m → ℝ, is_lewis_weight_vector p A τ → τ = σ) ∧
            ∃ run : dual_relative_smoothness_run m,
              dual_relative_smoothness_execution p ε A σ run ∧
              is_epsilon_estimate ε σ run.output ∧
              (run.iterations : ℝ) ≤ C * dual_iteration_scale m p ε ∧
              each_iteration_computes_leverage_scores p A run := by sorry

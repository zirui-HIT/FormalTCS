import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option linter.all false
set_option maxHeartbeats 500000

abbrev osgm_point (n : ℕ) := EuclideanSpace ℝ (Fin n)

abbrev osgm_matrix (n : ℕ) := EuclideanSpace ℝ (Fin n × Fin n)

def osgm_matrix_view {n : ℕ} (P : osgm_matrix n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => P (i, j)

noncomputable def ratio_surrogate {n : ℕ} (f : osgm_point n → ℝ)
    (xStar x : osgm_point n) (P : osgm_matrix n) : ℝ :=
  (f (x - Matrix.toEuclideanLin (osgm_matrix_view P) (gradient f x)) - f xStar) /
    (f x - f xStar)

def metric_projection_map {n : ℕ} (Pset : Set (osgm_matrix n))
    (project : osgm_matrix n → osgm_matrix n) : Prop :=
  ∀ A, project A ∈ Pset ∧ ∀ Q ∈ Pset, ‖project A - A‖ ≤ ‖Q - A‖

def osgm_objective_assumptions {n : ℕ} (f : osgm_point n → ℝ)
    (xStar : osgm_point n) (L μ : ℝ) : Prop :=
  0 < L ∧ 0 < μ ∧ Differentiable ℝ f ∧
    (∀ x, DifferentiableAt ℝ (gradient f) x) ∧
    (∀ x, f xStar ≤ f x) ∧
    (∀ x y,
      abs (f x - f y - inner ℝ (gradient f y) (x - y)) ≤
        L / 2 * ‖x - y‖ ^ 2) ∧
    (∀ x y,
      μ / 2 * ‖x - y‖ ^ 2 ≤
        f x - f y - inner ℝ (gradient f y) (x - y))

def positive_objective_gaps {n : ℕ} (f : osgm_point n → ℝ)
    (xStar : osgm_point n) (x : ℕ → osgm_point n) (K : ℕ) : Prop :=
  ∀ k, 1 ≤ k → k ≤ K → 0 < f (x k) - f xStar

noncomputable def osgm_rx_run {n : ℕ} (f : osgm_point n → ℝ)
    (xStar : osgm_point n) (x : ℕ → osgm_point n)
    (P : ℕ → osgm_matrix n) (project : osgm_matrix n → osgm_matrix n)
    (η : ℝ) (K : ℕ) : Prop :=
  (∀ k, 1 ≤ k → k ≤ K →
    x (k + 1) = x k -
      Matrix.toEuclideanLin (osgm_matrix_view (P k)) (gradient f (x k))) ∧
  (∀ k, 1 ≤ k → k ≤ K →
    P (k + 1) = project
      (P k - η • gradient (ratio_surrogate f xStar (x k)) (P k)))

noncomputable def preconditioner_feasible {n : ℕ} (f : osgm_point n → ℝ)
    (κ : ℝ) (P : osgm_matrix n) : Prop :=
  0 < κ ∧ Matrix.PosSemidef (osgm_matrix_view P) ∧
    ∃ R : osgm_matrix n, Matrix.PosSemidef (osgm_matrix_view R) ∧
      osgm_matrix_view R * osgm_matrix_view R = osgm_matrix_view P ∧
      ∀ x v,
        κ⁻¹ * ‖v‖ ^ 2 ≤
            inner ℝ (Matrix.toEuclideanLin (osgm_matrix_view R) v)
              ((fderiv ℝ (gradient f) x)
                (Matrix.toEuclideanLin (osgm_matrix_view R) v)) ∧
          inner ℝ (Matrix.toEuclideanLin (osgm_matrix_view R) v)
              ((fderiv ℝ (gradient f) x)
                (Matrix.toEuclideanLin (osgm_matrix_view R) v)) ≤
            ‖v‖ ^ 2

noncomputable def universal_optimal_preconditioner {n : ℕ}
    (f : osgm_point n → ℝ) (Pset : Set (osgm_matrix n))
    (κStar : ℝ) (PStar : osgm_matrix n) : Prop :=
  PStar ∈ Pset ∧ preconditioner_feasible f κStar PStar ∧
    ∀ κ P, P ∈ Pset → preconditioner_feasible f κ P → κStar ≤ κ

theorem rx_globalconv {n K : ℕ} (f : osgm_point n → ℝ)
    (xStar : osgm_point n) (x : ℕ → osgm_point n)
    (P : ℕ → osgm_matrix n) (Pset : Set (osgm_matrix n))
    (project : osgm_matrix n → osgm_matrix n) (PStar : osgm_matrix n)
    (L μ η κStar : ℝ) (hK : 0 < K)
    (hobjective : osgm_objective_assumptions f xStar L μ)
    (hclosed : IsClosed Pset) (hconvex : Convex ℝ Pset)
    (hprojection : metric_projection_map Pset project)
    (hPone : P 1 ∈ Pset)
    (hrun : osgm_rx_run f xStar x P project η K)
    (hpositive : positive_objective_gaps f xStar x K)
    (huniversal : universal_optimal_preconditioner f Pset κStar PStar)
    (heta : η = min (1 / (4 * L ^ 2))
      (‖PStar - P 1‖ / (2 * L * Real.sqrt (K : ℝ)))) :
    f (x (K + 1)) - f xStar ≤
      (f (x 1) - f xStar) *
        (1 - κStar⁻¹ +
          max (4 * L * ‖PStar - P 1‖ / Real.sqrt (K : ℝ))
            (8 * L ^ 2 * ‖PStar - P 1‖ ^ 2 / (K : ℝ))) ^ K := by sorry

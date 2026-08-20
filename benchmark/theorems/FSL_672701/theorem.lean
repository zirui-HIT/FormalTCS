import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Probability.Moments.Variance

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory ProbabilityTheory

abbrev euclidean_state (d : ℕ) := Fin d → ℝ

noncomputable def log_laplace_transform {d : ℕ}
    (φ : euclidean_state d → ℝ) (x : euclidean_state d) : ℝ :=
  Real.log (∫ y, Real.exp (∑ i, x i * y i - φ y))

noncomputable def chi_squared_divergence {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (((μ.rnDeriv ν x).toReal - 1) ^ 2) ∂ν

noncomputable def coordinate_gradient {d : ℕ}
    (f : euclidean_state d → ℝ) (x : euclidean_state d) : euclidean_state d :=
  fun i => (fderiv ℝ f x) (fun j => if j = i then 1 else 0)

noncomputable def coordinate_hessian {d : ℕ}
    (f : euclidean_state d → ℝ) (x : euclidean_state d) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j =>
    (fderiv ℝ (fun z => coordinate_gradient f z j) x)
      (fun k => if k = i then 1 else 0)

noncomputable def mirror_dirichlet_form {d : ℕ}
    (π : Measure (euclidean_state d)) (ψ f : euclidean_state d → ℝ) : ℝ :=
  ∫ x, ∑ i, coordinate_gradient f x i *
    ∑ j, (coordinate_hessian ψ x)⁻¹ i j * coordinate_gradient f x j ∂π

def functional_poincare {d : ℕ} (π : Measure (euclidean_state d))
    (ψ : euclidean_state d → ℝ) (α : ℝ) : Prop :=
  ∀ f : euclidean_state d → ℝ,
    ContDiff ℝ 1 f → MeasureTheory.MemLp f 2 π →
      ProbabilityTheory.variance f π ≤ α⁻¹ * mirror_dirichlet_form π ψ f

noncomputable def normalized_measure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) : Measure Ω :=
  (μ Set.univ)⁻¹ • μ

noncomputable def gibbs_base_measure {d : ℕ}
    (φ : euclidean_state d → ℝ) : Measure (euclidean_state d) :=
  (volume : Measure (euclidean_state d)).withDensity
    (fun x => ENNReal.ofReal (Real.exp (-φ x)))

noncomputable def measure_convolution_power {d : ℕ}
    (ρ : Measure (euclidean_state d)) :
    ℕ → Measure (euclidean_state d)
  | 0 => Measure.dirac 0
  | n + 1 => (measure_convolution_power ρ n).conv ρ

noncomputable def dual_conditional {d : ℕ}
    (φ : euclidean_state d → ℝ) (τ : ℕ) (x : euclidean_state d) :
    Measure (euclidean_state d) :=
  normalized_measure
    ((measure_convolution_power (gibbs_base_measure φ) τ).withDensity
      (fun y => ENNReal.ofReal (Real.exp (∑ i, x i * y i))))

noncomputable def primal_conditional {d : ℕ}
    (ψ : euclidean_state d → ℝ) (π : Measure (euclidean_state d))
    (τ : ℕ) (y : euclidean_state d) : Measure (euclidean_state d) :=
  normalized_measure
    (π.withDensity
      (fun x => ENNReal.ofReal
        (Real.exp (∑ i, x i * y i - (τ : ℝ) * ψ x))))

noncomputable def dual_marginal {d : ℕ}
    (φ ψ : euclidean_state d → ℝ) (π : Measure (euclidean_state d))
    (τ : ℕ) : Measure (euclidean_state d) :=
  (measure_convolution_power (gibbs_base_measure φ) τ).withDensity
    (fun y => ∫⁻ x, ENNReal.ofReal
      (Real.exp (∑ i, x i * y i - (τ : ℝ) * ψ x)) ∂π)

noncomputable def forward_conditional_expectation {d : ℕ}
    (φ : euclidean_state d → ℝ) (τ : ℕ)
    (g : euclidean_state d → ℝ) (x : euclidean_state d) : ℝ :=
  ∫ y, g y ∂(dual_conditional φ τ x)

noncomputable def backward_conditional_expectation {d : ℕ}
    (ψ : euclidean_state d → ℝ) (π : Measure (euclidean_state d))
    (τ : ℕ) (f : euclidean_state d → ℝ) (y : euclidean_state d) : ℝ :=
  ∫ x, f x ∂(primal_conditional ψ π τ y)

def llt_prox_step {d : ℕ}
    (φ ψ : euclidean_state d → ℝ) (π : Measure (euclidean_state d))
    (τ : ℕ) (μ ν : Measure (euclidean_state d)) : Prop :=
  ∀ A : Set (euclidean_state d), MeasurableSet A →
    ν A = ∫⁻ x, ∫⁻ y, primal_conditional ψ π τ y A
      ∂(dual_conditional φ τ x) ∂μ

def llt_prox_trajectory {d : ℕ}
    (φ ψ : euclidean_state d → ℝ) (π : Measure (euclidean_state d))
    (τ : ℕ) (μ : ℕ → Measure (euclidean_state d)) : Prop :=
  (∀ k, IsProbabilityMeasure (μ k)) ∧
    ∀ k, llt_prox_step φ ψ π τ (μ k) (μ (k + 1))

theorem mixing {d τ k : ℕ} {α : ℝ}
    {φ ψ : euclidean_state d → ℝ}
    {π : Measure (euclidean_state d)}
    {μ : ℕ → Measure (euclidean_state d)}
    (hconv : ConvexOn ℝ Set.univ φ)
    (hψ : ψ = log_laplace_transform φ)
    (hτ : 0 < τ) (hα : 0 < α)
    (hπ : IsProbabilityMeasure π)
    (hPI : functional_poincare π ψ α)
    (hcond_prob : ∀ x, IsProbabilityMeasure (dual_conditional φ τ x))
    (hcond_meas : AEMeasurable (fun x => dual_conditional φ τ x) π)
    (hmarginal : dual_marginal φ ψ π τ =
      Measure.bind π (fun x => dual_conditional φ τ x))
    (hadjoint :
      (∀ u, MeasureTheory.MemLp u 2 (dual_marginal φ ψ π τ) →
        MeasureTheory.MemLp
          (forward_conditional_expectation φ τ u) 2 π) ∧
      (∀ v, MeasureTheory.MemLp v 2 π →
        MeasureTheory.MemLp
          (backward_conditional_expectation ψ π τ v) 2
            (dual_marginal φ ψ π τ)) ∧
      ∀ u v,
        MeasureTheory.MemLp u 2 (dual_marginal φ ψ π τ) →
        MeasureTheory.MemLp v 2 π →
        ∫ x, forward_conditional_expectation φ τ u x * v x ∂π =
          ∫ y, u y * backward_conditional_expectation ψ π τ v y
            ∂(dual_marginal φ ψ π τ))
    (hforward_range :
      ∀ v, MeasureTheory.MemLp v 2 π →
        ContDiff ℝ 1 (backward_conditional_expectation ψ π τ v) ∧
        ContDiff ℝ 1 (forward_conditional_expectation φ τ
          (backward_conditional_expectation ψ π τ v)) ∧
        mirror_dirichlet_form π ψ
            (forward_conditional_expectation φ τ
              (backward_conditional_expectation ψ π τ v)) ≤
          (τ : ℝ) * ∫ x, ProbabilityTheory.variance
            (backward_conditional_expectation ψ π τ v)
            (dual_conditional φ τ x) ∂π)
    (hμ0 : μ 0 ≪ π)
    (htrajectory : llt_prox_trajectory φ ψ π τ μ) :
    chi_squared_divergence (μ k) π ≤
      ENNReal.ofReal (1 / (1 + α / (τ : ℝ)) ^ (2 * k)) *
        chi_squared_divergence (μ 0) π := by sorry

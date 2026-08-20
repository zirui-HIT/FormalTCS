import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Order.LiminfLimsup
import Mathlib.Probability.Process.Filtration

set_option linter.all false

open MeasureTheory

noncomputable def clipped_vector {d : ℕ} (γ : ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  min 1 (γ / ‖v‖) • v

noncomputable def clipped_step_size (p : ℝ) (t : ℕ) : ℝ :=
  Real.rpow (((t + 2 : ℕ) : ℝ)) (-p / (3 * p - 2))

noncomputable def clipping_radius (G p : ℝ) (t : ℕ) : ℝ :=
  if p = 2 then
    2 * G * Real.sqrt (Real.log (((t + 2 : ℕ) : ℝ)))
  else
    2 * G * Real.rpow (((t + 2 : ℕ) : ℝ)) ((2 - p) / (6 * p - 4))

def nonconvex_cost_assumptions {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (G : ℝ) (L : NNReal) : Prop :=
  0 < G ∧
    BddBelow (Set.range f) ∧
    Differentiable ℝ f ∧
    (∀ y, ‖gradient f y‖ ≤ G) ∧
    LipschitzWith L (gradient f)

noncomputable def heavy_tail_noise_assumptions
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    {d : ℕ} (filtration : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x g : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (p σ : ℝ) : Prop :=
  1 < p ∧ p ≤ 2 ∧ 0 ≤ σ ∧
    (∀ t, MeasureTheory.Integrable (g t) μ) ∧
    (∀ t, MeasureTheory.Integrable
      (fun ω => Real.rpow ‖g t ω - gradient f (x t ω)‖ p) μ) ∧
    (∀ t, μ[g t | filtration t] =ᵐ[μ] fun ω => gradient f (x t ω)) ∧
    (∀ t, μ[(fun ω => Real.rpow ‖g t ω - gradient f (x t ω)‖ p) | filtration t]
      ≤ᵐ[μ] fun _ => Real.rpow σ p)

noncomputable def clipped_sgd_run
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    {d : ℕ} (filtration : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (x g : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (G p : ℝ) : Prop :=
  (∃ x₀ : EuclideanSpace ℝ (Fin d), ∀ᵐ ω ∂μ, x 0 ω = x₀) ∧
    (∀ t, Measurable[filtration t, borel (EuclideanSpace ℝ (Fin d))] (x t)) ∧
    (∀ t, ∀ᵐ ω ∂μ,
      x (t + 1) ω = x t ω -
        clipped_step_size p t • clipped_vector (clipping_radius G p t) (g t ω))

noncomputable def best_iterate_gradient_squared
    {Ω : Type*} {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (t : ℕ) (ω : Ω) : ℝ :=
  if h : (Finset.range t).Nonempty then
    (Finset.range t).inf' h (fun k => ‖gradient f (x k ω)‖ ^ 2)
  else
    0

noncomputable def ldp_upper_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (F : ℕ → Ω → ℝ) (speed : ℕ → ℝ) (rate : ℝ → EReal) : Prop :=
  (∀ᶠ t in Filter.atTop, 0 < speed t) ∧
    Filter.Tendsto speed Filter.atTop Filter.atTop ∧
    ∀ B : Set ℝ, MeasurableSet B →
      Filter.limsup
          (fun t => ENNReal.log (μ ((F t) ⁻¹' B)) / (speed t : EReal))
          Filter.atTop
        ≤ -sInf (rate '' closure B)

noncomputable def heavy_tail_ldp_speed (p : ℝ) (t : ℕ) : ℝ :=
  Real.rpow (t : ℝ) (4 * (p - 1) / (3 * p - 2)) / Real.log (t : ℝ)

noncomputable def critical_ldp_speed (t : ℕ) : ℝ :=
  (t : ℝ) / (Real.log (t : ℝ)) ^ 2

noncomputable def heavy_tail_rate_function (G y : ℝ) : EReal :=
  if 0 ≤ y then (↑((y ^ 2 / (768 * G ^ 4) : ℝ)) : EReal) else ⊤

noncomputable def critical_rate_function (G y : ℝ) : EReal :=
  if 0 ≤ y then (↑((y ^ 2 / (384 * G ^ 4) : ℝ)) : EReal) else ⊤

theorem main_non_conv_clip
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    {d : ℕ} (filtration : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x g : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (G : ℝ) (L : NNReal) (p σ : ℝ)
    (hcost : nonconvex_cost_assumptions f G L)
    (hnoise : heavy_tail_noise_assumptions μ filtration f x g p σ)
    (hrun : clipped_sgd_run μ filtration x g G p) :
    (p < 2 →
      ldp_upper_bound μ (best_iterate_gradient_squared f x)
        (heavy_tail_ldp_speed p) (heavy_tail_rate_function G)) ∧
    (p = 2 →
      ldp_upper_bound μ (best_iterate_gradient_squared f x)
        critical_ldp_speed (critical_rate_function G)) := by sorry

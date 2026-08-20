import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Data.Finset.Max
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.Order.LocalExtr

set_option maxHeartbeats 500000

open scoped BigOperators
open MeasureTheory

structure denoising_problem (k m : ℕ) where
  sample : Fin (k + 2) → ℝ
  signal : ℝ
  weightBound : ℝ
  innerWeight : Fin m → ℝ

def valid_denoising_problem {k m : ℕ} (p : denoising_problem k m) : Prop :=
  0 < m ∧
    0 < p.signal ∧ p.signal < 1 ∧
    1 ≤ p.weightBound ∧
    StrictMono p.sample ∧
    ∀ l : Fin m, p.innerWeight l = 1 ∨ p.innerWeight l = -1

abbrev score_parameters (m : ℕ) :=
  (Fin m → ℝ) × (Fin m → ℝ)

noncomputable def parameter_distance {m : ℕ}
    (θ θ' : score_parameters m) : ℝ :=
  Real.sqrt
    ((∑ l : Fin m, (θ.1 l - θ'.1 l) ^ 2) +
      ∑ l : Fin m, (θ.2 l - θ'.2 l) ^ 2)

noncomputable def parameter_gradient {m : ℕ}
    (F : score_parameters m → ℝ) (θ : score_parameters m) :
    score_parameters m :=
  (fun l =>
      (fderiv ℝ F θ)
        ((fun r => if r = l then 1 else 0), 0),
    fun l =>
      (fderiv ℝ F θ)
        (0, (fun r => if r = l then 1 else 0)))

def relu (z : ℝ) : ℝ :=
  max z 0

noncomputable def network_score {k m : ℕ} (p : denoising_problem k m)
    (θ : score_parameters m) (y : ℝ) : ℝ :=
  (m : ℝ)⁻¹ * ∑ l : Fin m,
    θ.1 l * relu (p.innerWeight l * y + θ.2 l)

noncomputable def minimum_spacing {k : ℕ} (x : Fin (k + 2) → ℝ) : ℝ :=
  let gaps : Finset ℝ :=
    Finset.univ.image (fun i : Fin (k + 1) => x i.succ - x i.castSucc)
  gaps.min' (by
    simp [gaps])

def gaussian_variance (σ : ℝ) : NNReal :=
  ⟨σ ^ 2, sq_nonneg σ⟩

noncomputable def score_matching_risk {k m : ℕ} (p : denoising_problem k m)
    (σ : ℝ) (s : ℝ → ℝ) : ℝ :=
  ((k + 2 : ℕ) : ℝ)⁻¹ * ∑ i : Fin (k + 2),
    ∫ y : ℝ,
      (s y + (σ ^ 2)⁻¹ * (y - p.signal * p.sample i)) ^ 2
      ∂ProbabilityTheory.gaussianReal
        (p.signal * p.sample i) (gaussian_variance σ)

noncomputable def network_risk {k m : ℕ} (p : denoising_problem k m)
    (σ : ℝ) (θ : score_parameters m) : ℝ :=
  score_matching_risk p σ (network_score p θ)

noncomputable def sample_network_risk {k m : ℕ}
    (p : denoising_problem k m) (σ : ℝ) (i : Fin (k + 2))
    (θ : score_parameters m) : ℝ :=
  ∫ y : ℝ,
    (network_score p θ y +
      (σ ^ 2)⁻¹ * (y - p.signal * p.sample i)) ^ 2
    ∂ProbabilityTheory.gaussianReal
      (p.signal * p.sample i) (gaussian_variance σ)

noncomputable def empirical_optimal_score {k m : ℕ}
    (p : denoising_problem k m) (σ y : ℝ) : ℝ :=
  (∑ i : Fin (k + 2),
      (p.signal * p.sample i - y) *
        Real.exp (-((y - p.signal * p.sample i) ^ 2) / (2 * σ ^ 2))) /
    (σ ^ 2 * ∑ i : Fin (k + 2),
      Real.exp (-((y - p.signal * p.sample i) ^ 2) / (2 * σ ^ 2)))

noncomputable def excess_risk {k m : ℕ} (p : denoising_problem k m)
    (σ : ℝ) (θ : score_parameters m) : ℝ :=
  network_risk p σ θ -
    score_matching_risk p σ (empirical_optimal_score p σ)

def interior_parameters {k m : ℕ} (p : denoising_problem k m)
    (θ : score_parameters m) : Prop :=
  ∀ l : Fin m, -p.weightBound < θ.1 l ∧ θ.1 l < p.weightBound

noncomputable def linearized_sgd_trajectory {k m : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (p : denoising_problem k m)
    (σ η : ℝ) (θstar : score_parameters m)
    (sampleIndex : ℕ → Ω → Fin (k + 2))
    (trajectory : ℕ → Ω → score_parameters m) : Prop :=
  (∀ j : ℕ, Measurable (sampleIndex j)) ∧
    (∀ j : ℕ, Measurable (trajectory j)) ∧
    (∀ j : ℕ,
      Measure.map (sampleIndex j) P =
        (PMF.uniformOfFintype (Fin (k + 2))).toMeasure) ∧
    ProbabilityTheory.iIndepFun sampleIndex P ∧
    ∀ (j : ℕ) (ω : Ω),
      trajectory (j + 1) ω =
        trajectory j ω -
          ((m : ℝ) * η) •
            (parameter_gradient
                (sample_network_risk p σ (sampleIndex j ω)) θstar +
              (fderiv ℝ
                (parameter_gradient
                  (sample_network_risk p σ (sampleIndex j ω))) θstar)
                (trajectory j ω - θstar))

noncomputable def linearly_stable_local_minimum {k m : ℕ}
    (p : denoising_problem k m) (σ η : ℝ)
    (θstar : score_parameters m) : Prop :=
  IsLocalMin (network_risk p σ) θstar ∧
    ∃ ε : ℝ, 0 < ε ∧
      ∃ δ : ℝ, 0 < δ ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
          [IsProbabilityMeasure P]
          (sampleIndex : ℕ → Ω → Fin (k + 2))
          (trajectory : ℕ → Ω → score_parameters m),
          linearized_sgd_trajectory P p σ η θstar sampleIndex trajectory →
            (∀ ω : Ω,
              parameter_distance (trajectory 0 ω) θstar < δ) →
              (∀ j : ℕ,
                Integrable
                  (fun ω : Ω =>
                    parameter_distance (trajectory j ω) θstar) P) ∧
              BddAbove
                (Set.range
                  (fun j : ℕ => ∫ ω : Ω,
                    parameter_distance (trajectory j ω) θstar ∂P)) ∧
              Filter.limsup
                (fun j : ℕ => ∫ ω : Ω,
                  parameter_distance (trajectory j ω) θstar ∂P)
                Filter.atTop ≤ ε

noncomputable def sample_weight_scale {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (1 + (n : ℝ) + ∑ i : Fin n, |x i|) ^ 6

def scale_compatible_weight_bound {k m : ℕ}
    (p : denoising_problem k m) (σ : ℝ) : Prop :=
  sample_weight_scale p.sample / σ ^ 6 ≤ p.weightBound

theorem main_without_d2 {k : ℕ}
    (x : Fin (k + 2) → ℝ) (μ : ℝ) :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧
      ∀ {m : ℕ} (p : denoising_problem k m),
        p.sample = x → p.signal = μ → valid_denoising_problem p →
          ∀ (σ η : ℝ), 0 < σ → σ < 1 → σ ≤ σ₀ →
            scale_compatible_weight_bound p σ →
              η > 2 ^ 12 * σ ^ 2 /
              (p.signal * (((k + 2 : ℕ) : ℝ) ^ 2) *
                minimum_spacing p.sample) →
            ∀ (θstar : score_parameters m),
              linearly_stable_local_minimum p σ η θstar →
                interior_parameters p θstar →
                excess_risk p σ θstar >
                  Real.pi * (((k + 2 : ℕ) : ℝ) ^ 5) *
                      p.signal ^ 3 * minimum_spacing p.sample ^ 3 /
                    (2 ^ 36 * Real.exp (1 / 2) *
                      p.weightBound ^ 4 * σ ^ 4) := by sorry

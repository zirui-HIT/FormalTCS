import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.Probability.Distributions.Gaussian.Real

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators ENNReal

abbrev sampling_point (d : ℕ) := EuclideanSpace ℝ (Fin d)

structure sampling_problem (d : ℕ) where
  target : ProbabilityTheory.Kernel (sampling_point d) (sampling_point d)
  negLogDensity : sampling_point d → sampling_point d → ℝ

def is_probability_potential {d : ℕ} (problem : sampling_problem d) : Prop :=
  (∀ y, MeasureTheory.IsProbabilityMeasure (problem.target y)) ∧
    ∀ y, problem.target y = MeasureTheory.volume.withDensity
      (fun x => ENNReal.ofReal (Real.exp (-problem.negLogDensity y x)))

def is_strongly_log_concave_with_condition_number_at_most {d : ℕ}
    (problem : sampling_problem d) (κ : ℝ) : Prop :=
  is_probability_potential problem ∧
    ∃ m L : ℝ, 0 < m ∧ 0 ≤ L ∧ L ≤ κ * m ∧
      ∀ y, StrongConvexOn Set.univ m (problem.negLogDensity y) ∧
        LipschitzWith L.toNNReal (fderiv ℝ (problem.negLogDensity y))

inductive sampling_distance where
  | totalVariation
  | kullbackLeibler

noncomputable def probability_total_variation_distance {α : Type*} [MeasurableSpace α]
    (μ ν : MeasureTheory.Measure α) : ℝ≥0∞ :=
  ⨆ (s : Set α) (_hs : MeasurableSet s),
    ENNReal.ofReal |(μ s).toReal - (ν s).toReal|

noncomputable def measure_sampling_distance {α : Type*} [MeasurableSpace α]
    (D : sampling_distance) (μ ν : MeasureTheory.Measure α) : ℝ≥0∞ :=
  match D with
  | .totalVariation => probability_total_variation_distance μ ν
  | .kullbackLeibler => InformationTheory.klDiv μ ν

structure slc_black_box_sampler (d : ℕ) where
  sample : sampling_problem d → ℝ →
    ProbabilityTheory.Kernel (sampling_point d) (sampling_point d)
  sample_isMarkovKernel : ∀ problem δ,
    ProbabilityTheory.IsMarkovKernel (sample problem δ)
  queries : ℝ → ℕ

noncomputable def is_accurate_on_problem {d : ℕ} (D : sampling_distance)
    (sampler : slc_black_box_sampler d) (problem : sampling_problem d) (δ : ℝ) : Prop :=
  ∀ y, measure_sampling_distance D (sampler.sample problem δ y) (problem.target y) ≤
    ENNReal.ofReal δ

noncomputable def is_slc_sampler_with_query_complexity {d : ℕ}
    (D : sampling_distance) (sampler : slc_black_box_sampler d)
    (Nslc : ℝ → ℕ) : Prop :=
  sampler.queries = Nslc ∧
    ∀ (problem : sampling_problem d) (δ : ℝ),
      0 < δ → is_strongly_log_concave_with_condition_number_at_most problem 4 →
        is_accurate_on_problem D sampler problem δ

structure reverse_sampling_path (K d : ℕ) where
  terminal : sampling_problem d
  backward : Fin K → sampling_problem d

noncomputable def compose_reverse_kernels {d : ℕ}
    (terminal : MeasureTheory.Measure (sampling_point d))
    (kernels : List (ProbabilityTheory.Kernel (sampling_point d) (sampling_point d))) :
    MeasureTheory.Measure (sampling_point d) :=
  kernels.foldl (fun μ kernel => μ.bind kernel) terminal

noncomputable def sampled_reverse_output {K d : ℕ} (path : reverse_sampling_path K d)
    (sampler : slc_black_box_sampler d) (ε : ℝ) :
    MeasureTheory.Measure (sampling_point d) :=
  let localAccuracy := ε / (K + 1 : ℝ)
  compose_reverse_kernels (sampler.sample path.terminal localAccuracy 0)
    (List.ofFn fun i : Fin K => sampler.sample (path.backward (Fin.rev i)) localAccuracy)

noncomputable def unscale_early_stopped_law {d : ℕ} (sigmaTarget : ℝ)
    (μ : MeasureTheory.Measure (sampling_point d)) :
    MeasureTheory.Measure (sampling_point d) :=
  MeasureTheory.Measure.map
    (fun y : sampling_point d => WithLp.toLp 2 fun i =>
      Real.sqrt 2 * sigmaTarget * y i) μ

noncomputable def rescaled_reverse_output {K d : ℕ} (path : reverse_sampling_path K d)
    (sampler : slc_black_box_sampler d) (sigmaTarget ε : ℝ) :
    MeasureTheory.Measure (sampling_point d) :=
  unscale_early_stopped_law sigmaTarget (sampled_reverse_output path sampler ε)

noncomputable def total_reduction_query_count (K : ℕ) (Nslc : ℝ → ℕ) (ε : ℝ) : ℕ :=
  ∑ k ∈ Finset.range (K + 1), Nslc (ε / (K + 1 : ℝ))

def iterated_covariance_parameter (a B : ℕ → ℝ) (k : ℕ) : ℝ :=
  4 * B k * ∏ ℓ ∈ Finset.range k, (a ℓ) ^ 2

def uses_adaptive_stepsizes (K : ℕ) (a B : ℕ → ℝ) : Prop :=
  0 < K ∧
    (∀ k, k ≤ K → 0 < B k) ∧
    (∀ k, k < K → 0 < a k ∧ a k < 1) ∧
    a 0 = 1 / Real.sqrt 2 ∧
    (∀ k, 1 ≤ k → k < K →
      (a k) ^ 2 =
        (2 * iterated_covariance_parameter a B k + 2) /
          (2 * iterated_covariance_parameter a B k + 3)) ∧
    B 0 ≤ 1 / 2

def trajectory_length_condition (K : ℕ) (a B : ℕ → ℝ) : Prop :=
  (∏ ℓ ∈ Finset.range K, (a ℓ) ^ 2) ≤ 1 / (8 * B K)

structure multimodal_forward_trajectory {K d : ℕ} (a B : ℕ → ℝ)
    (path : reverse_sampling_path K d)
    (sourceTarget : MeasureTheory.Measure (sampling_point d)) where
  sigmaTarget : ℝ
  sigmaTarget_pos : 0 < sigmaTarget
  dataLaw : MeasureTheory.Measure (sampling_point d)
  dataLaw_probability : MeasureTheory.IsProbabilityMeasure dataLaw
  earlyStoppingKernel :
    ProbabilityTheory.Kernel (sampling_point d) (sampling_point d)
  forwardLaw : Fin (K + 1) → MeasureTheory.Measure (sampling_point d)
  forwardTransition :
    Fin K → ProbabilityTheory.Kernel (sampling_point d) (sampling_point d)
  forwardGivenData :
    Fin (K + 1) → ProbabilityTheory.Kernel (sampling_point d) (sampling_point d)
  forwardTransitionDensity :
    Fin K → sampling_point d → sampling_point d → ℝ
  forwardGivenDataDensity :
    Fin (K + 1) → sampling_point d → sampling_point d → ℝ
  forwardDensity : Fin (K + 1) → sampling_point d → ℝ
  dataGivenForward :
    Fin (K + 1) → ProbabilityTheory.Kernel (sampling_point d) (sampling_point d)
  conditionalMean : Fin (K + 1) → sampling_point d → sampling_point d
  conditionalCovariance :
    Fin (K + 1) → sampling_point d → Fin d → Fin d → ℝ
  source_target_eq : sourceTarget = dataLaw.bind earlyStoppingKernel
  early_stopping_gaussian : ∀ x, earlyStoppingKernel x =
    MeasureTheory.Measure.map
      (fun w : Fin d → ℝ => WithLp.toLp 2 fun i => x i + sigmaTarget * w i)
      (MeasureTheory.Measure.pi fun _ : Fin d =>
        ProbabilityTheory.gaussianReal 0 1)
  initial_forward_law : ∀ x,
    forwardGivenData ⟨0, Nat.zero_lt_succ K⟩ x =
      MeasureTheory.Measure.map
        (fun z : sampling_point d => WithLp.toLp 2 fun i =>
          z i / (Real.sqrt 2 * sigmaTarget)) (earlyStoppingKernel x)
  affine_gaussian_transition : ∀ (k : Fin K) (y : sampling_point d),
    forwardTransition k y = MeasureTheory.Measure.map
      (fun w : Fin d → ℝ => WithLp.toLp 2 fun i =>
        a k * y i + Real.sqrt (1 - (a k) ^ 2) * w i)
      (MeasureTheory.Measure.pi fun _ : Fin d =>
        ProbabilityTheory.gaussianReal 0 1)
  initial_forward_density : ∀ (x y : sampling_point d),
    forwardGivenDataDensity ⟨0, Nat.zero_lt_succ K⟩ x y =
      Real.exp (-(∑ i, (y i -
        x i / (Real.sqrt 2 * sigmaTarget)) ^ 2)) /
        (Real.sqrt Real.pi) ^ d
  transition_density_formula : ∀ (k : Fin K) (x y : sampling_point d),
    forwardTransitionDensity k x y =
      Real.exp (-(∑ i, (y i - a k * x i) ^ 2) /
        (2 * (1 - (a k) ^ 2))) /
        (Real.sqrt (2 * Real.pi * (1 - (a k) ^ 2))) ^ d
  forward_density_recursion : ∀ (k : Fin K) (x y : sampling_point d),
    forwardGivenDataDensity (Fin.succ k) x y =
      ∫ z, forwardGivenDataDensity (Fin.castSucc k) x z *
        forwardTransitionDensity k z y
  forward_mixture_density : ∀ (k : Fin (K + 1)) (y : sampling_point d),
    forwardDensity k y = ∫ x, forwardGivenDataDensity k x y ∂dataLaw
  forward_transition_density_representation :
    ∀ (k : Fin K) (x : sampling_point d),
      forwardTransition k x = MeasureTheory.volume.withDensity
        (fun y => ENNReal.ofReal (forwardTransitionDensity k x y))
  forward_given_data_density_representation :
    ∀ (k : Fin (K + 1)) (x : sampling_point d),
      forwardGivenData k x = MeasureTheory.volume.withDensity
        (fun y => ENNReal.ofReal (forwardGivenDataDensity k x y))
  forward_marginal_density_representation : ∀ k,
    forwardLaw k = MeasureTheory.volume.withDensity
      (fun y => ENNReal.ofReal (forwardDensity k y))
  forward_density_pos : ∀ (k : Fin (K + 1)) (y : sampling_point d),
    0 < forwardDensity k y
  transition_density_pos : ∀ (k : Fin K) (x y : sampling_point d),
    0 < forwardTransitionDensity k x y
  forward_recursion : ∀ (k : Fin K) (x : sampling_point d),
    forwardGivenData (Fin.succ k) x =
      (forwardGivenData (Fin.castSucc k) x).bind (forwardTransition k)
  forward_marginal : ∀ k,
    forwardLaw k = dataLaw.bind (forwardGivenData k)
  data_given_forward_bayes : ∀ (k : Fin (K + 1))
      (y : sampling_point d),
    dataGivenForward k y = dataLaw.withDensity
      (fun x => ENNReal.ofReal
        (forwardGivenDataDensity k x y / forwardDensity k y))
  data_disintegration : ∀ (k : Fin (K + 1))
      (s t : Set (sampling_point d)),
    MeasurableSet s → MeasurableSet t →
      (∫⁻ y in s, dataGivenForward k y t ∂forwardLaw k) =
        ∫⁻ x in t, forwardGivenData k x s ∂dataLaw
  conditional_mean_identity : ∀ (k : Fin (K + 1))
      (y : sampling_point d) (i : Fin d),
    conditionalMean k y i =
      ∫ x, x i / (Real.sqrt 2 * sigmaTarget) ∂dataGivenForward k y
  conditional_covariance_identity : ∀ (k : Fin (K + 1))
      (y : sampling_point d) (i j : Fin d),
    conditionalCovariance k y i j =
      ∫ x, (x i / (Real.sqrt 2 * sigmaTarget) - conditionalMean k y i) *
        (x j / (Real.sqrt 2 * sigmaTarget) - conditionalMean k y j)
          ∂dataGivenForward k y
  covariance_bound : ∀ k : Fin (K + 1),
    B k = sSup (Set.range fun y : sampling_point d =>
      sSup {r : ℝ | ∃ u : sampling_point d,
        (∑ i, (u i) ^ 2) = 1 ∧
          r = ∑ i, ∑ j, u i * conditionalCovariance k y i j * u j})
  conditional_covariance_quadratic_bounds :
    ∀ (k : Fin (K + 1)) (y u : sampling_point d),
      0 ≤ ∑ i, ∑ j, u i * conditionalCovariance k y i j * u j ∧
        (∑ i, ∑ j, u i * conditionalCovariance k y i j * u j) ≤
          B k * ∑ i, (u i) ^ 2
  forward_potential_twice_continuously_differentiable :
    ∀ k : Fin (K + 1),
      ContDiff ℝ 2
        (fun z : sampling_point d => -Real.log (forwardDensity k z))
  forward_hessian_quadratic_form :
    ∀ (k : Fin (K + 1)) (y u : sampling_point d),
      (fderiv ℝ (fderiv ℝ
        (fun z : sampling_point d => -Real.log (forwardDensity k z))) y) u u =
        (∑ i, (u i) ^ 2) /
            (1 - (1 / 2 : ℝ) *
              ∏ ℓ ∈ Finset.range (k : ℕ), (a ℓ) ^ 2) -
          ((∏ ℓ ∈ Finset.range (k : ℕ), (a ℓ) ^ 2) /
              (1 - (1 / 2 : ℝ) *
                ∏ ℓ ∈ Finset.range (k : ℕ), (a ℓ) ^ 2) ^ 2) *
            ∑ i, ∑ j, u i * conditionalCovariance k y i j * u j
  terminal_marginal : ∀ y,
    path.terminal.target y = forwardLaw ⟨K, Nat.lt_succ_self K⟩
  terminal_potential : ∀ y x,
    path.terminal.negLogDensity y x =
      -Real.log (forwardDensity ⟨K, Nat.lt_succ_self K⟩ x)
  backward_pointwise_bayes : ∀ (k : Fin K) (y : sampling_point d),
    (path.backward k).target y = MeasureTheory.volume.withDensity
      (fun x => ENNReal.ofReal
        (forwardDensity (Fin.castSucc k) x *
          forwardTransitionDensity k x y /
            forwardDensity (Fin.succ k) y))
  backward_potential : ∀ (k : Fin K) (y x : sampling_point d),
    (path.backward k).negLogDensity y x =
      -Real.log (forwardDensity (Fin.castSucc k) x *
        forwardTransitionDensity k x y /
          forwardDensity (Fin.succ k) y)
  backward_potential_twice_continuously_differentiable :
    ∀ (k : Fin K) (y : sampling_point d),
      ContDiff ℝ 2 ((path.backward k).negLogDensity y)
  backward_hessian_quadratic_form :
    ∀ (k : Fin K) (y x u : sampling_point d),
      (fderiv ℝ (fderiv ℝ
        ((path.backward k).negLogDensity y)) x) u u =
        (fderiv ℝ (fderiv ℝ
          (fun z : sampling_point d =>
            -Real.log (forwardDensity (Fin.castSucc k) z))) x) u u +
          ((a k) ^ 2 / (1 - (a k) ^ 2)) * ∑ i, (u i) ^ 2
  backward_disintegration : ∀ (k : Fin K) (s t : Set (sampling_point d)),
    MeasurableSet s → MeasurableSet t →
      (∫⁻ y in s, (path.backward k).target y t ∂forwardLaw (Fin.succ k)) =
        ∫⁻ x in t, forwardTransition k x s ∂forwardLaw (Fin.castSucc k)
  normalized_potentials :
    is_probability_potential path.terminal ∧
      ∀ k : Fin K, is_probability_potential (path.backward k)

theorem slc_reduction_for_multimodal_case {K d : ℕ} (a B : ℕ → ℝ)
    (path : reverse_sampling_path K d)
    (sourceTarget : MeasureTheory.Measure (sampling_point d))
    (sampler : slc_black_box_sampler d)
    (Nslc : ℝ → ℕ) (D : sampling_distance) (ε : ℝ)
    (hAdaptive : uses_adaptive_stepsizes K a B)
    (hTrajectory : multimodal_forward_trajectory a B path sourceTarget)
    (hLength : trajectory_length_condition K a B)
    (hε : 0 < ε)
    (hSampler : is_slc_sampler_with_query_complexity D sampler Nslc) :
    (is_strongly_log_concave_with_condition_number_at_most path.terminal 4 ∧
      ∀ k : Fin K,
        is_strongly_log_concave_with_condition_number_at_most (path.backward k) 4) ∧
      measure_sampling_distance D
        (rescaled_reverse_output path sampler hTrajectory.sigmaTarget ε)
        sourceTarget ≤ ENNReal.ofReal ε ∧
      total_reduction_query_count K Nslc ε =
        ∑ k ∈ Finset.range (K + 1), Nslc (ε / (K + 1 : ℝ)) := by sorry

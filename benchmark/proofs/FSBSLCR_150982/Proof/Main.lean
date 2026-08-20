import Architect
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

@[blueprint "def:sampling-point"
  (statement := /-- For an ambient dimension $d$, the state space is the Euclidean vector space $\mathbb{R}^d$, represented as functions from $\operatorname{Fin}(d)$ to $\mathbb{R}$. -/)
  (title := /-- Sampling state space -/)
  (latexEnv := "definition")]
abbrev sampling_point (d : ℕ) := EuclideanSpace ℝ (Fin d)

@[blueprint "def:sampling-problem"
  (statement := /-- A sampling problem in dimension $d$ consists of a probability kernel $y \mapsto p(\,\cdot\mid y)$ and a candidate negative log-density $V(y,\cdot)$.  The parameter $y$ permits the same object to represent every backward conditional; a terminal marginal is represented by a kernel constant in $y$. -/)
  (title := /-- Parameterized sampling problem -/)
  (latexEnv := "definition")]
structure sampling_problem (d : ℕ) where
  target : ProbabilityTheory.Kernel (sampling_point d) (sampling_point d)
  negLogDensity : sampling_point d → sampling_point d → ℝ

@[blueprint "def:is-probability-potential"
  (statement := /-- A sampling problem has a normalized probability potential if, for every parameter $y$, its target is a probability measure with Lebesgue density $x \mapsto \exp(-V(y,x))$. -/)
  (title := /-- Normalized probability potential -/)
  (latexEnv := "definition")]
def is_probability_potential {d : ℕ} (problem : sampling_problem d) : Prop :=
  (∀ y, MeasureTheory.IsProbabilityMeasure (problem.target y)) ∧
    ∀ y, problem.target y = MeasureTheory.volume.withDensity
      (fun x => ENNReal.ofReal (Real.exp (-problem.negLogDensity y x)))

@[blueprint "def:is-strongly-log-concave-with-condition-number-at-most"
  (statement := /-- Let $\kappa>0$.  A sampling problem is strongly log-concave with condition number at most $\kappa$ if its targets have normalized potentials and there exist $m>0$ and $L\geq 0$ with $L\leq \kappa m$ such that every potential is $m$-strongly convex and has $L$-Lipschitz gradient. -/)
  (title := /-- Strong log-concavity with bounded condition number -/)
  (latexEnv := "definition")]
def is_strongly_log_concave_with_condition_number_at_most {d : ℕ}
    (problem : sampling_problem d) (κ : ℝ) : Prop :=
  is_probability_potential problem ∧
    ∃ m L : ℝ, 0 < m ∧ 0 ≤ L ∧ L ≤ κ * m ∧
      ∀ y, StrongConvexOn Set.univ m (problem.negLogDensity y) ∧
        LipschitzWith L.toNNReal (fderiv ℝ (problem.negLogDensity y))

@[blueprint "def:sampling-distance"
  (statement := /-- The reduction is asserted for exactly two discrepancies between probability laws: total variation distance and Kullback--Leibler divergence. -/)
  (title := /-- Admissible sampling distances -/)
  (latexEnv := "definition")]
inductive sampling_distance where
  | totalVariation
  | kullbackLeibler

@[blueprint "def:probability-total-variation-distance"
  (statement := /-- For probability measures $\mu$ and $\nu$, their total variation distance is $\sup_A |\mu(A)-\nu(A)|$, where the supremum ranges over measurable sets $A$. -/)
  (title := /-- Total variation distance -/)
  (latexEnv := "definition")]
noncomputable def probability_total_variation_distance {α : Type*} [MeasurableSpace α]
    (μ ν : MeasureTheory.Measure α) : ℝ≥0∞ :=
  ⨆ (s : Set α) (_hs : MeasurableSet s),
    ENNReal.ofReal |(μ s).toReal - (ν s).toReal|

@[blueprint "def:measure-sampling-distance"
  (statement := /-- The discrepancy $D(\mu,\nu)$ is interpreted as total variation when $D=\mathrm{TV}$ and as $\mathrm{KL}(\mu\|\nu)$ when $D=\mathrm{KL}$. -/)
  (title := /-- Distance between sampling laws -/)
  (latexEnv := "definition")]
noncomputable def measure_sampling_distance {α : Type*} [MeasurableSpace α]
    (D : sampling_distance) (μ ν : MeasureTheory.Measure α) : ℝ≥0∞ :=
  match D with
  | .totalVariation => probability_total_variation_distance μ ν
  | .kullbackLeibler => InformationTheory.klDiv μ ν

@[blueprint "def:slc-black-box-sampler"
  (statement := /-- A black-box SLC sampler assigns to every sampling problem and tolerance a Markov kernel giving its probability-valued output law, together with the number of score-oracle queries used at that tolerance. -/)
  (title := /-- Black-box strongly log-concave sampler -/)
  (latexEnv := "definition")]
structure slc_black_box_sampler (d : ℕ) where
  sample : sampling_problem d → ℝ →
    ProbabilityTheory.Kernel (sampling_point d) (sampling_point d)
  sample_isMarkovKernel : ∀ problem δ,
    ProbabilityTheory.IsMarkovKernel (sample problem δ)
  queries : ℝ → ℕ

@[blueprint "def:is-accurate-on-problem"
  (statement := /-- A sampler is $\delta$-accurate on a parameterized problem in discrepancy $D$ if, uniformly for every conditioning value $y$, the output law lies within $\delta$ of the target law. -/)
  (title := /-- Per-problem sampling accuracy -/)
  (latexEnv := "definition")]
noncomputable def is_accurate_on_problem {d : ℕ} (D : sampling_distance)
    (sampler : slc_black_box_sampler d) (problem : sampling_problem d) (δ : ℝ) : Prop :=
  ∀ y, measure_sampling_distance D (sampler.sample problem δ y) (problem.target y) ≤
    ENNReal.ofReal δ

@[blueprint "def:is-slc-sampler-with-query-complexity"
  (statement := /-- Fix an admissible discrepancy $D$.  A black box has query complexity $N_{\mathrm{SLC}}$ for $D$ if its query-count function is $N_{\mathrm{SLC}}$ and it returns a $\delta$-accurate law in discrepancy $D$ for every problem whose SLC condition number is at most $4$, whenever $\delta>0$. -/)
  (title := /-- SLC sampler guarantee and query complexity -/)
  (latexEnv := "definition")]
noncomputable def is_slc_sampler_with_query_complexity {d : ℕ}
    (D : sampling_distance) (sampler : slc_black_box_sampler d)
    (Nslc : ℝ → ℕ) : Prop :=
  sampler.queries = Nslc ∧
    ∀ (problem : sampling_problem d) (δ : ℝ),
      0 < δ → is_strongly_log_concave_with_condition_number_at_most problem 4 →
        is_accurate_on_problem D sampler problem δ

@[blueprint "def:reverse-sampling-path"
  (statement := /-- A reverse sampling path of length $K$ consists of the terminal marginal problem $p_K$ and the $K$ backward conditional problems $p_{k\mid k+1}$, indexed chronologically by $k\in\operatorname{Fin}(K)$. -/)
  (title := /-- Terminal and backward sampling sub-problems -/)
  (latexEnv := "definition")]
structure reverse_sampling_path (K d : ℕ) where
  terminal : sampling_problem d
  backward : Fin K → sampling_problem d

@[blueprint "def:compose-reverse-kernels"
  (statement := /-- Starting from a terminal law, compose a list of backward kernels in the order in which they occur in the list. -/)
  (title := /-- Reverse-kernel composition -/)
  (latexEnv := "definition")]
noncomputable def compose_reverse_kernels {d : ℕ}
    (terminal : MeasureTheory.Measure (sampling_point d))
    (kernels : List (ProbabilityTheory.Kernel (sampling_point d) (sampling_point d))) :
    MeasureTheory.Measure (sampling_point d) :=
  kernels.foldl (fun μ kernel => μ.bind kernel) terminal

@[blueprint "def:exact-reverse-target"
  (statement := /-- The exact target of a reverse path is obtained from $p_K$ by successively applying $p_{K-1\mid K},\ldots,p_{0\mid1}$.  The terminal problem is evaluated at the zero parameter because a terminal marginal is constant in that parameter. -/)
  (title := /-- Exact target law of the reverse path -/)
  (latexEnv := "definition")]
noncomputable def exact_reverse_target {K d : ℕ} (path : reverse_sampling_path K d) :
    MeasureTheory.Measure (sampling_point d) :=
  compose_reverse_kernels (path.terminal.target 0)
    (List.ofFn fun i : Fin K => (path.backward (Fin.rev i)).target)

@[blueprint "def:sampled-reverse-output"
  (statement := /-- For a requested global accuracy $\varepsilon$, run the black-box sampler on the terminal problem and on each backward conditional at local accuracy $\varepsilon/(K+1)$, and compose the resulting kernels in reverse chronological order.  The resulting law is expressed in the coordinate system of the initial law of the reverse path. -/)
  (title := /-- Output law of the sampled reverse path -/)
  (latexEnv := "definition")]
noncomputable def sampled_reverse_output {K d : ℕ} (path : reverse_sampling_path K d)
    (sampler : slc_black_box_sampler d) (ε : ℝ) :
    MeasureTheory.Measure (sampling_point d) :=
  let localAccuracy := ε / (K + 1 : ℝ)
  compose_reverse_kernels (sampler.sample path.terminal localAccuracy 0)
    (List.ofFn fun i : Fin K => sampler.sample (path.backward (Fin.rev i)) localAccuracy)

@[blueprint "def:unscale-early-stopped-law"
  (statement := /-- If a law is expressed in the coordinates $y=z/(\sqrt{2}\sigma)$, its pushforward under $y\mapsto\sqrt{2}\sigma y$ is the corresponding law in the original $z$-coordinates. -/)
  (title := /-- Inverse scaling of the early-stopped law -/)
  (latexEnv := "definition")]
noncomputable def unscale_early_stopped_law {d : ℕ} (sigmaTarget : ℝ)
    (μ : MeasureTheory.Measure (sampling_point d)) :
    MeasureTheory.Measure (sampling_point d) :=
  MeasureTheory.Measure.map
    (fun y : sampling_point d => WithLp.toLp 2 fun i =>
      Real.sqrt 2 * sigmaTarget * y i) μ

@[blueprint "def:rescaled-reverse-output"
  (statement := /-- The final output of the reduction is obtained by applying the deterministic inverse scaling $y\mapsto\sqrt{2}\sigma_{\mathrm{tar}}y$ to the reverse sampler's output law. -/)
  (title := /-- Reverse output in the source coordinates -/)
  (latexEnv := "definition")]
noncomputable def rescaled_reverse_output {K d : ℕ} (path : reverse_sampling_path K d)
    (sampler : slc_black_box_sampler d) (sigmaTarget ε : ℝ) :
    MeasureTheory.Measure (sampling_point d) :=
  unscale_early_stopped_law sigmaTarget (sampled_reverse_output path sampler ε)

@[blueprint "def:total-reduction-query-count"
  (statement := /-- The total query count is the sum of the black-box query complexities for the $K+1$ terminal and backward sub-problems, each requested at accuracy $\varepsilon/(K+1)$. -/)
  (title := /-- Query count of the reduction -/)
  (latexEnv := "definition")]
noncomputable def total_reduction_query_count (K : ℕ) (Nslc : ℝ → ℕ) (ε : ℝ) : ℕ :=
  ∑ k ∈ Finset.range (K + 1), Nslc (ε / (K + 1 : ℝ))

@[blueprint "def:iterated-covariance-parameter"
  (statement := /-- For stepsizes $(a_k)$ and conditional covariance bounds $(B_k)$, set $\lambda_k=4B_k\prod_{\ell=0}^{k-1}a_\ell^2$. -/)
  (title := /-- Adaptive covariance parameter -/)
  (latexEnv := "definition")]
def iterated_covariance_parameter (a B : ℕ → ℝ) (k : ℕ) : ℝ :=
  4 * B k * ∏ ℓ ∈ Finset.range k, (a ℓ) ^ 2

@[blueprint "def:uses-adaptive-stepsizes"
  (statement := /-- A length-$K$ trajectory uses the adaptive schedule when $K>0$, all relevant covariance bounds are positive, $0<a_k<1$ for $k<K$, $a_0=1/\sqrt{2}$, for $1\leq k<K$ one has $a_k^2=(2\lambda_k+2)/(2\lambda_k+3)$, and the initial normalized posterior-covariance bound satisfies $B_0\leq 1/2$. -/)
  (title := /-- Adaptive stepsize schedule -/)
  (latexEnv := "definition")]
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

@[blueprint "def:trajectory-length-condition"
  (statement := /-- The terminal length condition is $\prod_{\ell=0}^{K-1}a_\ell^2\leq (8B_K)^{-1}$. -/)
  (title := /-- Terminal product bound -/)
  (latexEnv := "definition")]
def trajectory_length_condition (K : ℕ) (a B : ℕ → ℝ) : Prop :=
  (∏ ℓ ∈ Finset.range K, (a ℓ) ^ 2) ≤ 1 / (8 * B K)

@[blueprint "def:has-multimodal-hessian-control"
  (statement := /-- The corrected trajectory-control conclusion distinguishes the special initial backward step from the steps governed by the adaptive recurrence.  The terminal potential is $(1-\lambda_K)$-strongly convex with $2$-Lipschitz gradient.  The potential of $p_{0\mid1}$ is $1$-strongly convex with $4$-Lipschitz gradient.  For every $k$ with $1\leq k<K$, the potential of $p_{k\mid k+1}$ is $(\lambda_k+2)$-strongly convex with gradient Lipschitz constant $2(\lambda_k+2)$.  Every potential is normalized against its probability kernel. -/)
  (title := /-- Hessian control along the multimodal trajectory -/)
  (latexEnv := "definition")]
def has_multimodal_hessian_control {K d : ℕ} (a B : ℕ → ℝ)
    (path : reverse_sampling_path K d) : Prop :=
  is_probability_potential path.terminal ∧
    (∀ y, StrongConvexOn Set.univ (1 - iterated_covariance_parameter a B K)
      (path.terminal.negLogDensity y) ∧
      LipschitzWith (2 : ℝ).toNNReal
        (fderiv ℝ (path.terminal.negLogDensity y))) ∧
    ∀ k : Fin K,
      is_probability_potential (path.backward k) ∧
        ∀ y, StrongConvexOn Set.univ
          (if (k : ℕ) = 0 then (1 : ℝ)
            else iterated_covariance_parameter a B k + 2)
          ((path.backward k).negLogDensity y) ∧
          LipschitzWith
            (if (k : ℕ) = 0 then (4 : ℝ)
              else 2 * (iterated_covariance_parameter a B k + 2)).toNNReal
            (fderiv ℝ ((path.backward k).negLogDensity y))

@[blueprint "def:multimodal-forward-trajectory"
  (statement := /-- Fix a probability law $\mu_X$ on $\mathbb{R}^d$, an early-stopping scale $\sigma_{\mathrm{tar}}>0$, the law $\mu_Z$ of $Z=X+\sigma_{\mathrm{tar}}W_0$, stepsizes $(a_k)$, and conditional-covariance bounds $(B_k)$.  A source-faithful multimodal trajectory is expressed in the scaled initial coordinates $Y_1=Z/(\sqrt{2}\sigma_{\mathrm{tar}})$ and consists of the Gaussian early-stopping kernel, the subsequent affine Gaussian forward kernels, all forward marginal laws, the conditional laws of $X$ given each forward state, and the reverse conditional problems.  The special initialization producing $Y_1$ is represented by the initial forward kernel and is not an assertion that its law equals the unscaled law $\mu_Z$.  The structure specifies everywhere-defined densities: the initial and transition densities are the pointwise Gaussian formulas, the later forward densities are obtained by pointwise convolution, and each marginal density is the mixture over $\mu_X$.  The data-given-forward kernels and backward kernels are the corresponding pointwise Bayes versions, whose strictly positive denominators fix them at every conditioning value, including values in null sets.  The terminal sampling problem is constant in its dummy parameter and its potential is the negative logarithm of the terminal marginal density; each backward potential is likewise the negative logarithm of its canonical Bayes density.  The conditional mean and covariance fields are those of the normalized signal $X/(\sqrt{2}\sigma_{\mathrm{tar}})$ under the canonical data-given-forward kernels, and $B_k$ is exactly the supremum over conditioning values of the operator norms of these normalized conditional covariances; in particular, every covariance quadratic form is nonnegative and bounded above by $B_k\lVert u\rVert^2$.  Finally, put $q_k^2=\prod_{\ell<k}a_\ell^2$ and $v_k=1-q_k^2/2$.  Every forward negative log-density is $C^2$, and its Fréchet Hessian satisfies
  \[
  D^2(-\log p_k)(y)[u,u]
  =\frac{\lVert u\rVert^2}{v_k}
   -\frac{q_k^2}{v_k^2}\,u^\top\operatorname{Cov}\!\left(
     \frac{X}{\sqrt{2}\sigma_{\mathrm{tar}}}\,\middle|\,Y_k=y\right)u
  \]
  for every $k$, $y$, and $u$.  Every backward potential is also $C^2$, and its Hessian quadratic form is the corresponding forward quadratic form plus $a_k^2(1-a_k^2)^{-1}\lVert u\rVert^2$. -/)
  (title := /-- Source-faithful Gaussian forward and reverse trajectory -/)
  (latexEnv := "definition")]
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

@[blueprint "lem:euclidean-hessian-bounds-give-strong-convexity-and-smoothness"
  (statement := /-- Let $f:\mathbb{R}^d\to\mathbb{R}$ be twice continuously Fréchet differentiable, and let $0\leq m$ and $0<L$.  If
  \[
  m\lVert u\rVert^2\leq D^2f(x)[u,u]\leq L\lVert u\rVert^2
  \]
  for every $x,u\in\mathbb{R}^d$, then $f$ is $m$-strongly convex on $\mathbb{R}^d$ and $Df$ is $L$-Lipschitz. -/)
  (proof := /-- Restrict $f$ to every affine line $t\mapsto x+t(y-x)$.  The chain rule identifies its second derivative with $D^2f(x+t(y-x))[y-x,y-x]$.  After subtracting $m\lVert y-x\rVert^2t^2/2$, the resulting scalar function has nonnegative second derivative and is therefore convex.  Its convexity inequality at $0$ and $1$ is precisely the strong-convexity inequality for $f$.  The same scalar argument applied to $f$ and to $L\lVert v\rVert^2t^2/2-f(x+tv)$ gives, for every $x,v$,
  \[
  f(x)+Df(x)[v]\leq f(x+v)\leq
  f(x)+Df(x)[v]+\frac{L}{2}\lVert v\rVert^2.
  \]
  Let $p=\nabla f(x)-\nabla f(y)$ and apply the upper inequality at $x$ with increment $-p/L$, while applying the lower inequality from $y$ to the same point.  The Riesz identity $\bigl(Df(x)-Df(y)\bigr)[p]=\lVert p\rVert^2$ yields
  \[
  \lVert p\rVert^2\leq
  2L\bigl(f(x)-f(y)-Df(y)[x-y]\bigr).
  \]
  Adding this estimate to its version with $x$ and $y$ interchanged, and then applying Cauchy--Schwarz, gives $\lVert\nabla f(x)-\nabla f(y)\rVert\leq L\lVert x-y\rVert$.  The Fréchet--Riesz isometry transfers this estimate to $Df$. -/)
  (title := /-- Euclidean Hessian bounds imply strong convexity and smoothness -/)
  (latexEnv := "lemma")]
lemma euclidean_hessian_bounds_give_strong_convexity_and_smoothness {d : ℕ}
    {f : sampling_point d → ℝ} {m L : ℝ}
    (hm : 0 ≤ m) (hL : 0 < L) (hf : ContDiff ℝ 2 f)
    (hquad : ∀ x u, m * ‖u‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ f) x) u u ∧
      (fderiv ℝ (fderiv ℝ f) x) u u ≤ L * ‖u‖ ^ 2) :
    StrongConvexOn Set.univ m f ∧
      LipschitzWith L.toNNReal (fderiv ℝ f) := by
  have hline_first (x v : sampling_point d) (t : ℝ) :
      deriv (fun s : ℝ => f (x + s • v)) t =
        fderiv ℝ f (x + t • v) v := by
    have hz : HasDerivAt (fun s : ℝ => x + s • v) v t := by
      simpa using (hasDerivAt_id t).smul_const v |>.const_add x
    change deriv (f ∘ fun s : ℝ => x + s • v) t = _
    simpa using
      ((hf.differentiable (by norm_num) (x + t • v)).hasFDerivAt.comp
        t hz.hasFDerivAt).hasDerivAt.deriv
  have hline_second (x v : sampling_point d) (t : ℝ) :
      (deriv^[2] fun s : ℝ => f (x + s • v)) t =
        (fderiv ℝ (fderiv ℝ f) (x + t • v)) v v := by
    rw [show (deriv^[2] fun s : ℝ => f (x + s • v)) t =
      deriv (deriv fun s : ℝ => f (x + s • v)) t by rfl]
    rw [show deriv (fun s : ℝ => f (x + s • v)) =
      fun s => fderiv ℝ f (x + s • v) v from funext (hline_first x v)]
    have hz : HasDerivAt (fun s : ℝ => x + s • v) v t := by
      simpa using (hasDerivAt_id t).smul_const v |>.const_add x
    have hc : HasDerivAt (fun s : ℝ => fderiv ℝ f (x + s • v))
        (fderiv ℝ (fderiv ℝ f) (x + t • v) v) t := by
      change HasDerivAt (fderiv ℝ f ∘ fun s : ℝ => x + s • v) _ t
      simpa using
        (((hf.fderiv_right (by norm_num)).differentiable_one
          (x + t • v)).hasFDerivAt.comp t hz.hasFDerivAt).hasDerivAt
    simpa using (hc.clm_apply (hasDerivAt_const t v)).deriv
  have huniform (x y : sampling_point d) (a b : ℝ)
      (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
      f (a • x + b • y) ≤ a • f x + b • f y -
        a * b * (m / 2 * ‖x - y‖ ^ 2) := by
    let v := y - x
    let F := fun t : ℝ => f (x + t • v)
    let c := m / 2 * ‖v‖ ^ 2
    let P := fun t : ℝ => c * t ^ 2
    let ψ := F - P
    have hFcont : ContDiff ℝ 2 F := by
      dsimp [F, v]
      fun_prop
    have hPcont : ContDiff ℝ 2 P := by
      dsimp [P]
      fun_prop
    have hψcont : ContDiff ℝ 2 ψ := hFcont.sub hPcont
    have hFdiff : Differentiable ℝ F := hFcont.differentiable (by norm_num)
    have hFderivdiff : Differentiable ℝ (deriv F) := by
      simpa only [iteratedDeriv_one] using hFcont.differentiable_iteratedDeriv' 1
    have hψdiff : Differentiable ℝ ψ := hψcont.differentiable (by norm_num)
    have hψderivdiff : Differentiable ℝ (deriv ψ) := by
      simpa only [iteratedDeriv_one] using hψcont.differentiable_iteratedDeriv' 1
    have hP_deriv (t : ℝ) : deriv P t = 2 * c * t := by
      dsimp [P]
      change deriv (fun y : ℝ => c * (id ^ 2) y) t = _
      rw [(((hasDerivAt_id t).pow 2).const_mul c).deriv]
      simp [pow_two]
      ring
    have hψ_deriv_at (t : ℝ) : deriv ψ t = deriv F t - (2 * c) * t := by
      dsimp [ψ]
      rw [deriv_sub (hFdiff t) (hPcont.differentiable (by norm_num) t), hP_deriv]
    have hψ_second (t : ℝ) :
        (deriv^[2] ψ) t =
          (fderiv ℝ (fderiv ℝ f) (x + t • v)) v v - 2 * c := by
      rw [show (deriv^[2] ψ) t = deriv (deriv ψ) t by rfl]
      rw [show deriv ψ = fun s => deriv F s - (2 * c) * s
        from funext hψ_deriv_at]
      have hFsecond : HasDerivAt (deriv F) ((deriv^[2] F) t) t := by
        simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
          (hFderivdiff t).hasDerivAt
      have hlin : HasDerivAt (fun s : ℝ => (2 * c) * s) (2 * c) t := by
        simpa using (hasDerivAt_id t).const_mul (2 * c)
      change deriv ((deriv F) - fun s : ℝ => (2 * c) * s) t = _
      rw [(hFsecond.sub hlin).deriv]
      have hFformula :
          (deriv^[2] F) t =
            (fderiv ℝ (fderiv ℝ f) (x + t • v)) v v :=
        hline_second x v t
      rw [hFformula]
    have hnonneg (t : ℝ) : 0 ≤ (deriv^[2] ψ) t := by
      rw [hψ_second]
      dsimp [c]
      nlinarith [(hquad (x + t • v) v).1]
    have hconv : ConvexOn ℝ Set.univ ψ :=
      convexOn_univ_of_deriv2_nonneg hψdiff hψderivdiff hnonneg
    have hs := hconv.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
      ha hb hab
    dsimp [ψ, P, F, c, v] at hs
    norm_num [smul_eq_mul] at hs
    have haeq : a = 1 - b := by linarith
    have hpoint : a • x + b • y = x + b • (y - x) := by
      rw [haeq]
      module
    calc
      f (a • x + b • y) = f (x + b • (y - x)) := congrArg f hpoint
      _ ≤ a * f x + b * (f y - m / 2 * ‖y - x‖ ^ 2) +
          m / 2 * ‖y - x‖ ^ 2 * b ^ 2 := hs
      _ = a • f x + b • f y - a * b * (m / 2 * ‖x - y‖ ^ 2) := by
        rw [norm_sub_rev, haeq]
        simp only [smul_eq_mul]
        ring
  have hstrong : StrongConvexOn Set.univ m f := by
    change UniformConvexOn Set.univ (fun r => m / 2 * r ^ 2) f
    exact ⟨convex_univ, fun x _ y _ a b ha hb hab =>
      huniform x y a b ha hb hab⟩
  have hsupport (x v : sampling_point d) :
      f x + fderiv ℝ f x v ≤ f (x + v) := by
    let F := fun t : ℝ => f (x + t • v)
    have hFcont : ContDiff ℝ 2 F := by
      dsimp [F]
      fun_prop
    have hFdiff : Differentiable ℝ F := hFcont.differentiable (by norm_num)
    have hFderivdiff : Differentiable ℝ (deriv F) := by
      simpa only [iteratedDeriv_one] using hFcont.differentiable_iteratedDeriv' 1
    have hFconv : ConvexOn ℝ Set.univ F :=
      convexOn_univ_of_deriv2_nonneg hFdiff hFderivdiff (fun t => by
        change 0 ≤ (deriv^[2] fun s : ℝ => f (x + s • v)) t
        rw [hline_second]
        nlinarith [(hquad (x + t • v) v).1])
    have hslope := hFconv.deriv_le_slope (Set.mem_univ (0 : ℝ))
      (Set.mem_univ (1 : ℝ)) zero_lt_one (hFdiff 0)
    dsimp [F] at hslope
    rw [hline_first] at hslope
    norm_num [slope_def_field] at hslope
    linarith
  have hdescent (x v : sampling_point d) :
      f (x + v) ≤ f x + fderiv ℝ f x v + L / 2 * ‖v‖ ^ 2 := by
    let F := fun t : ℝ => f (x + t • v)
    let c := L / 2 * ‖v‖ ^ 2
    let P := fun t : ℝ => c * t ^ 2
    let χ := P - F
    have hFcont : ContDiff ℝ 2 F := by
      dsimp [F]
      fun_prop
    have hPcont : ContDiff ℝ 2 P := by
      dsimp [P]
      fun_prop
    have hχcont : ContDiff ℝ 2 χ := hPcont.sub hFcont
    have hFdiff : Differentiable ℝ F := hFcont.differentiable (by norm_num)
    have hχdiff : Differentiable ℝ χ := hχcont.differentiable (by norm_num)
    have hχderivdiff : Differentiable ℝ (deriv χ) := by
      simpa only [iteratedDeriv_one] using hχcont.differentiable_iteratedDeriv' 1
    have hP_deriv (t : ℝ) : deriv P t = 2 * c * t := by
      dsimp [P]
      change deriv (fun y : ℝ => c * (id ^ 2) y) t = _
      rw [(((hasDerivAt_id t).pow 2).const_mul c).deriv]
      simp [pow_two]
      ring
    have hχ_deriv_at (t : ℝ) : deriv χ t = 2 * c * t - deriv F t := by
      dsimp [χ]
      rw [deriv_sub (hPcont.differentiable (by norm_num) t) (hFdiff t), hP_deriv]
    have hχ_second (t : ℝ) :
        (deriv^[2] χ) t =
          2 * c - (fderiv ℝ (fderiv ℝ f) (x + t • v)) v v := by
      rw [show (deriv^[2] χ) t = deriv (deriv χ) t by rfl]
      rw [show deriv χ = fun s => 2 * c * s - deriv F s
        from funext hχ_deriv_at]
      have hlin : HasDerivAt (fun s : ℝ => (2 * c) * s) (2 * c) t := by
        simpa using (hasDerivAt_id t).const_mul (2 * c)
      have hFderivdiff : Differentiable ℝ (deriv F) := by
        simpa only [iteratedDeriv_one] using hFcont.differentiable_iteratedDeriv' 1
      have hFsecond : HasDerivAt (deriv F) ((deriv^[2] F) t) t := by
        simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
          (hFderivdiff t).hasDerivAt
      change deriv ((fun s : ℝ => (2 * c) * s) - deriv F) t = _
      rw [(hlin.sub hFsecond).deriv]
      have hFformula :
          (deriv^[2] F) t =
            (fderiv ℝ (fderiv ℝ f) (x + t • v)) v v :=
        hline_second x v t
      rw [hFformula]
    have hχconv : ConvexOn ℝ Set.univ χ :=
      convexOn_univ_of_deriv2_nonneg hχdiff hχderivdiff (fun t => by
        rw [hχ_second]
        dsimp [c]
        nlinarith [(hquad (x + t • v) v).2])
    have hslope := hχconv.deriv_le_slope (Set.mem_univ (0 : ℝ))
      (Set.mem_univ (1 : ℝ)) zero_lt_one (hχdiff 0)
    dsimp [χ, P, F, c] at hslope
    rw [hχ_deriv_at] at hslope
    have hfirst0 : deriv F 0 = fderiv ℝ f x v := by
      simpa using hline_first x v 0
    rw [hfirst0] at hslope
    norm_num [slope_def_field] at hslope
    linarith
  have hgap (x y : sampling_point d) :
      ‖gradient f x - gradient f y‖ ^ 2 ≤
        2 * L * (f x - f y - fderiv ℝ f y (x - y)) := by
    let p := gradient f x - gradient f y
    let α := 1 / L
    let z := x - α • p
    have hs := hsupport y (z - y)
    have hd := hdescent x (-α • p)
    have hz1 : y + (z - y) = z := by module
    have hz2 : x + -α • p = z := by
      dsimp [z]
      module
    rw [hz1] at hs
    rw [hz2] at hd
    have hp_eval : fderiv ℝ f x p - fderiv ℝ f y p = ‖p‖ ^ 2 := by
      dsimp [p]
      rw [← inner_gradient_left, ← inner_gradient_left, ← inner_sub_left,
        real_inner_self_eq_norm_sq]
    have hαpos : 0 < α := by
      dsimp [α]
      positivity
    have hnorm : ‖-α • p‖ ^ 2 = α ^ 2 * ‖p‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hαpos.le]
      ring
    have hfy : fderiv ℝ f y (z - y) =
        fderiv ℝ f y (x - y) - α * fderiv ℝ f y p := by
      dsimp [z]
      simp only [map_sub, map_smul, smul_eq_mul]
      ring
    have hfx : fderiv ℝ f x (-α • p) = -α * fderiv ℝ f x p := by
      rw [map_smul]
      simp only [smul_eq_mul]
    rw [hfy] at hs
    rw [hfx, hnorm] at hd
    have hα : α * L = 1 := by
      dsimp [α]
      field_simp
    have hα2 : L * α ^ 2 = α := by
      dsimp [α]
      field_simp
    have hcancel : L * α ^ 2 * ‖p‖ ^ 2 = α * ‖p‖ ^ 2 :=
      congrArg (fun r : ℝ => r * ‖p‖ ^ 2) hα2
    have hmid :
        α * ‖p‖ ^ 2 ≤
          2 * (f x - f y - fderiv ℝ f y (x - y)) := by
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hmid hL.le
    have hn : ‖p‖ ^ 2 = L * (α * ‖p‖ ^ 2) := by
      calc
        ‖p‖ ^ 2 = (α * L) * ‖p‖ ^ 2 := by rw [hα, one_mul]
        _ = L * (α * ‖p‖ ^ 2) := by ring
    change ‖p‖ ^ 2 ≤ 2 * L * (f x - f y - fderiv ℝ f y (x - y))
    calc
      ‖p‖ ^ 2 = L * (α * ‖p‖ ^ 2) := hn
      _ ≤ L * (2 * (f x - f y - fderiv ℝ f y (x - y))) := hmul
      _ = 2 * L * (f x - f y - fderiv ℝ f y (x - y)) := by ring
  have hgrad_lip (x y : sampling_point d) :
      ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖ := by
    let p := gradient f x - gradient f y
    let v := x - y
    change ‖p‖ ≤ L * ‖v‖
    have hxy := hgap x y
    have hyx := hgap y x
    rw [norm_sub_rev] at hyx
    have hrev : fderiv ℝ f x (y - x) = -fderiv ℝ f x (x - y) := by
      rw [show y - x = -(x - y) by module, map_neg]
    rw [hrev] at hyx
    have hpv : fderiv ℝ f x v - fderiv ℝ f y v = @inner ℝ _ _ p v := by
      dsimp [p, v]
      rw [← inner_gradient_left, ← inner_gradient_left, ← inner_sub_left]
    have hsq : ‖p‖ ^ 2 ≤ L * @inner ℝ _ _ p v := by
      nlinarith [hxy, hyx, hpv]
    have hcs : @inner ℝ _ _ p v ≤ ‖p‖ * ‖v‖ := real_inner_le_norm p v
    by_cases hp0 : ‖p‖ = 0
    · rw [hp0]
      exact mul_nonneg hL.le (norm_nonneg v)
    · have hp_pos : 0 < ‖p‖ :=
        lt_of_le_of_ne (norm_nonneg p) (Ne.symm hp0)
      by_contra hnot
      have hlt : L * ‖v‖ < ‖p‖ := lt_of_not_ge hnot
      have hmul := mul_lt_mul_of_pos_left hlt hp_pos
      nlinarith
  have hgradnorm (x y : sampling_point d) :
      ‖fderiv ℝ f x - fderiv ℝ f y‖ =
        ‖gradient f x - gradient f y‖ := by
    rw [show fderiv ℝ f x - fderiv ℝ f y =
      InnerProductSpace.toDual ℝ _ (gradient f x - gradient f y) by
        ext v
        simp [gradient]]
    simpa using (InnerProductSpace.toDual ℝ (sampling_point d)).norm_map
      (gradient f x - gradient f y)
  refine ⟨hstrong, ?_⟩
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simp only [dist_eq_norm, NNReal.smul_def]
  rw [Real.coe_toNNReal L hL.le, hgradnorm]
  exact hgrad_lip x y

@[blueprint "lem:multimodal-trajectory-hessian-control"
  (statement := /-- Let $K,d\in\mathbb{N}$, let $a,B:\mathbb{N}\to\mathbb{R}$, let a reverse sampling path of length $K$ in dimension $d$ be given, and let $\mu$ be a measure on $\mathbb{R}^d$.  Suppose that $K>0$, that $B_k>0$ for every $k\leq K$, that $0<a_k<1$ for every $k<K$, that $a_0=1/\sqrt{2}$, that
  \[
  a_k^2=\frac{2\lambda_k+2}{2\lambda_k+3}
  \qquad (1\leq k<K),
  \]
  and that $B_0\leq 1/2$, where $\lambda_k=4B_k\prod_{\ell<k}a_\ell^2$.  Assume that these data form a source-faithful multimodal Gaussian forward and reverse trajectory with source target $\mu$, and that $\prod_{\ell<K}a_\ell^2\leq(8B_K)^{-1}$.  Then the terminal problem has a normalized probability potential, and, for every value of its parameter, this potential is $(1-\lambda_K)$-strongly convex and has $2$-Lipschitz Fréchet derivative.  Every backward problem also has a normalized probability potential.  For every conditioning value, the backward potential at $k=0$ is $1$-strongly convex and has $4$-Lipschitz Fréchet derivative, while for every $k$ with $1\leq k<K$ it is $(\lambda_k+2)$-strongly convex and has $2(\lambda_k+2)$-Lipschitz Fréchet derivative. -/)
  (proof := /-- Fix $k\leq K$ and $y\in\mathbb{R}^d$, and write $q_k^2=\prod_{\ell<k}a_\ell^2$ and $v_k=1-q_k^2/2$.  Since every stepsize before $K$ lies in $(0,1)$ by \cref{def:uses-adaptive-stepsizes}, one has $0<q_k^2\leq1$ and hence $1/2\leq v_k\leq1$.  The $C^2$ regularity and the second-order Tweedie identity supplied by \cref{def:multimodal-forward-trajectory} give, for every $u\in\mathbb{R}^d$,
  \[
  D^2(-\log p_k)(y)[u,u]
  =v_k^{-1}\lVert u\rVert^2
   -q_k^2v_k^{-2}\,u^\top\Sigma_k(y)u,
  \]
  where $\Sigma_k(y)$ is the conditional covariance of $X/(\sqrt{2}\sigma_{\mathrm{tar}})$ given $Y_k=y$.  The integral formula for $\Sigma_k(y)$ in \cref{def:multimodal-forward-trajectory} makes this quadratic form nonnegative, while the definition of $B_k$ in the same contract bounds it above by $B_k\lVert u\rVert^2$.  Since $v_k^{-1}\geq1$, $v_k^{-1}\leq2$, and $v_k^{-2}\leq4$, the Hessian quadratic form lies between $(1-4B_kq_k^2)\lVert u\rVert^2$ and $2\lVert u\rVert^2$.  Thus the forward Hessian lies between $(1-\lambda_k)I$ and $2I$, where $\lambda_k=4B_kq_k^2$; in particular this holds for the terminal potential when $k=K$.  The adaptive-schedule hypothesis in \cref{def:uses-adaptive-stepsizes} gives $B_K>0$, and the terminal product bound in \cref{def:trajectory-length-condition} therefore yields
  \[
  \lambda_K=4B_K\prod_{\ell<K}a_\ell^2\leq\frac12.
  \]
  Thus the terminal Hessian lies between $(1-\lambda_K)I$ and $2I$, with $1-\lambda_K\geq1/2$.  Applying \cref{lem:euclidean-hessian-bounds-give-strong-convexity-and-smoothness} to the trajectory's $C^2$ regularity and these directional Hessian bounds gives $(1-\lambda_K)$-strong convexity and a $2$-Lipschitz Fréchet derivative.

  For the initial backward conditional, the backward Hessian identity and $C^2$ regularity in \cref{def:multimodal-forward-trajectory}, together with $a_0=1/\sqrt{2}$, add the precision $a_0^2(1-a_0^2)^{-1}I=I$ to the initial forward Hessian.  At $k=0$ the forward identity reads $2I-4\Sigma_0(y)$, and $B_0\leq1/2$ from \cref{def:uses-adaptive-stepsizes} bounds this matrix between $0$ and $2I$.  Hence $I\preceq\BackHess_0(y)\preceq3I\preceq4I$.  Now fix $k$ with $1\leq k<K$.  The backward Hessian identity in \cref{def:multimodal-forward-trajectory} adds $a_k^2(1-a_k^2)^{-1}I$ to the forward Hessian.  On this positive index range the adaptive rule in \cref{def:uses-adaptive-stepsizes} gives $a_k^2(1-a_k^2)^{-1}=2\lambda_k+2$.  Adding this scalar matrix to the preceding forward bounds yields the lower bound $(\lambda_k+3)I$, hence $(\lambda_k+2)I$, and the upper bound $2(\lambda_k+2)I$.  A second application of \cref{lem:euclidean-hessian-bounds-give-strong-convexity-and-smoothness}, now to each backward potential, gives the asserted strong-convexity and Fréchet-derivative Lipschitz constants.  Finally, the terminal and backward density representations are normalized probability potentials by \cref{def:multimodal-forward-trajectory}; because their potentials are fixed pointwise by the same formulas, the bounds apply to the chosen sampling problems at every parameter, including null conditioning values. -/)
  (title := /-- Hessian control derived from the Gaussian trajectory -/)
  (latexEnv := "lemma")]
lemma multimodal_trajectory_hessian_control {K d : ℕ} (a B : ℕ → ℝ)
    (path : reverse_sampling_path K d)
    (sourceTarget : MeasureTheory.Measure (sampling_point d))
    (hAdaptive : uses_adaptive_stepsizes K a B)
    (hTrajectory : multimodal_forward_trajectory a B path sourceTarget)
    (hLength : trajectory_length_condition K a B) :
    has_multimodal_hessian_control a B path := by
  rcases hAdaptive with ⟨hK, hB, ha, ha0, hrec, hB0⟩
  have hprod_bounds (k : ℕ) (hk : k ≤ K) :
      0 < ∏ ℓ ∈ Finset.range k, (a ℓ) ^ 2 ∧
        (∏ ℓ ∈ Finset.range k, (a ℓ) ^ 2) ≤ 1 := by
    constructor
    · apply Finset.prod_pos
      intro i hi
      exact sq_pos_of_pos (ha i (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)).1
    · apply Finset.prod_le_one
      · intro i hi
        positivity
      · intro i hi
        have hai := ha i (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)
        nlinarith [sq_nonneg (a i)]
  have hforward_bounds (k : Fin (K + 1)) (x u : sampling_point d) :
      (1 - iterated_covariance_parameter a B k) * ‖u‖ ^ 2 ≤
          (fderiv ℝ (fderiv ℝ
            (fun z : sampling_point d =>
              -Real.log (hTrajectory.forwardDensity k z))) x) u u ∧
        (fderiv ℝ (fderiv ℝ
            (fun z : sampling_point d =>
              -Real.log (hTrajectory.forwardDensity k z))) x) u u ≤
          2 * ‖u‖ ^ 2 := by
    let q : ℝ := ∏ ℓ ∈ Finset.range (k : ℕ), (a ℓ) ^ 2
    let v : ℝ := 1 - (1 / 2 : ℝ) * q
    let s : ℝ := ‖u‖ ^ 2
    let c : ℝ :=
      ∑ i, ∑ j, u i * hTrajectory.conditionalCovariance k x i j * u j
    have hk : (k : ℕ) ≤ K := Nat.le_of_lt_succ k.isLt
    have hq := hprod_bounds k hk
    have hs : 0 ≤ s := by
      dsimp [s]
      positivity
    have hBk : 0 < B k := hB k hk
    have hc : 0 ≤ c ∧ c ≤ B k * s := by
      simpa only [c, s, EuclideanSpace.real_norm_sq_eq] using
        hTrajectory.conditional_covariance_quadratic_bounds k x u
    have hv_lower : (1 / 2 : ℝ) ≤ v := by
      dsimp [v]
      nlinarith
    have hv_upper : v ≤ 1 := by
      dsimp [v]
      nlinarith
    have hv_pos : 0 < v := lt_of_lt_of_le (by norm_num) hv_lower
    have hfirst_lower : s ≤ s / v := by
      apply (le_div_iff₀ hv_pos).2
      exact mul_le_of_le_one_right hs hv_upper
    have hfirst_upper : s / v ≤ 2 * s := by
      apply (div_le_iff₀ hv_pos).2
      have hmul := mul_le_mul_of_nonneg_left hv_lower hs
      nlinarith
    have hv_sq : (1 / 4 : ℝ) ≤ v ^ 2 := by
      nlinarith [sq_nonneg (v - 1 / 2)]
    have hqv := mul_le_mul_of_nonneg_left hv_sq hq.1.le
    have hcoeff :
        q / v ^ 2 ≤ 4 * q := by
      apply (div_le_iff₀ (sq_pos_of_pos hv_pos)).2
      nlinarith
    have hcoeff_nonneg : 0 ≤ q / v ^ 2 := by positivity
    have hterm_nonneg : 0 ≤ (q / v ^ 2) * c :=
      mul_nonneg hcoeff_nonneg hc.1
    have hterm_upper : (q / v ^ 2) * c ≤ 4 * B k * q * s := by
      calc
        (q / v ^ 2) * c ≤ (4 * q) * c :=
          mul_le_mul_of_nonneg_right hcoeff hc.1
        _ ≤ (4 * q) * (B k * s) :=
          mul_le_mul_of_nonneg_left hc.2 (by positivity)
        _ = 4 * B k * q * s := by ring
    rw [hTrajectory.forward_hessian_quadratic_form]
    rw [iterated_covariance_parameter, ← EuclideanSpace.real_norm_sq_eq]
    change (1 - 4 * B k * q) * s ≤ s / v - (q / v ^ 2) * c ∧
      s / v - (q / v ^ 2) * c ≤ 2 * s
    constructor <;> nlinarith
  have hforward_zero_bounds (x u : sampling_point d) :
      0 ≤
          (fderiv ℝ (fderiv ℝ
            (fun z : sampling_point d =>
              -Real.log (hTrajectory.forwardDensity
                ⟨0, Nat.zero_lt_succ K⟩ z))) x) u u ∧
        (fderiv ℝ (fderiv ℝ
            (fun z : sampling_point d =>
              -Real.log (hTrajectory.forwardDensity
                ⟨0, Nat.zero_lt_succ K⟩ z))) x) u u ≤
          2 * ‖u‖ ^ 2 := by
    let s : ℝ := ‖u‖ ^ 2
    let c : ℝ :=
      ∑ i, ∑ j, u i *
        hTrajectory.conditionalCovariance ⟨0, Nat.zero_lt_succ K⟩ x i j * u j
    have hs : 0 ≤ s := by
      dsimp [s]
      positivity
    have hc : 0 ≤ c ∧ c ≤ B 0 * s := by
      simpa only [c, s, EuclideanSpace.real_norm_sq_eq] using
        hTrajectory.conditional_covariance_quadratic_bounds
          ⟨0, Nat.zero_lt_succ K⟩ x u
    have hc_half : c ≤ (1 / 2 : ℝ) * s := by
      exact hc.2.trans (mul_le_mul_of_nonneg_right hB0 hs)
    rw [hTrajectory.forward_hessian_quadratic_form]
    simp only [Fin.val_zero, Finset.range_zero, Finset.prod_empty]
    norm_num [EuclideanSpace.real_norm_sq_eq]
    have hc_nonneg := hc.1
    dsimp [c] at hc_nonneg
    dsimp [c, s] at hc_half
    rw [EuclideanSpace.real_norm_sq_eq] at hc_half
    constructor <;> nlinarith
  have ha0sq : (a 0) ^ 2 = (1 / 2 : ℝ) := by
    rw [ha0, div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have ha0precision : (a 0) ^ 2 / (1 - (a 0) ^ 2) = (1 : ℝ) := by
    rw [ha0sq]
    norm_num
  have hBK : 0 < B K := hB K le_rfl
  have hterminal_parameter :
      iterated_covariance_parameter a B K ≤ (1 / 2 : ℝ) := by
    have h8B : 0 < 8 * B K := mul_pos (by norm_num) hBK
    have hmul : (∏ ℓ ∈ Finset.range K, (a ℓ) ^ 2) * (8 * B K) ≤ 1 := by
      exact (le_div_iff₀ h8B).mp hLength
    rw [iterated_covariance_parameter]
    nlinarith
  refine ⟨hTrajectory.normalized_potentials.1, ?_, ?_⟩
  · intro y
    have hpotential :
        path.terminal.negLogDensity y =
          fun z : sampling_point d =>
            -Real.log
              (hTrajectory.forwardDensity ⟨K, Nat.lt_succ_self K⟩ z) :=
      funext (hTrajectory.terminal_potential y)
    rw [hpotential]
    apply euclidean_hessian_bounds_give_strong_convexity_and_smoothness
    · nlinarith
    · norm_num
    · exact hTrajectory.forward_potential_twice_continuously_differentiable
        ⟨K, Nat.lt_succ_self K⟩
    · exact hforward_bounds ⟨K, Nat.lt_succ_self K⟩
  · intro k
    refine ⟨hTrajectory.normalized_potentials.2 k, ?_⟩
    intro y
    by_cases hk0 : (k : ℕ) = 0
    · have hkeq : k = ⟨0, hK⟩ := Fin.ext hk0
      subst k
      have hindex :
          Fin.castSucc (⟨0, hK⟩ : Fin K) =
            (⟨0, Nat.zero_lt_succ K⟩ : Fin (K + 1)) := Fin.ext rfl
      have hresult :
          StrongConvexOn Set.univ 1
              ((path.backward (⟨0, hK⟩ : Fin K)).negLogDensity y) ∧
            LipschitzWith (4 : ℝ).toNNReal
              (fderiv ℝ
                ((path.backward (⟨0, hK⟩ : Fin K)).negLogDensity y)) := by
        apply euclidean_hessian_bounds_give_strong_convexity_and_smoothness
        · norm_num
        · norm_num
        · exact hTrajectory.backward_potential_twice_continuously_differentiable
            ⟨0, hK⟩ y
        · intro x u
          rw [hTrajectory.backward_hessian_quadratic_form, ha0precision, hindex]
          rw [← EuclideanSpace.real_norm_sq_eq]
          have hf := hforward_zero_bounds x u
          constructor <;> nlinarith [sq_nonneg ‖u‖]
      simpa using hresult
    · simp only [if_neg hk0]
      have hk_one : 1 ≤ (k : ℕ) := Nat.one_le_iff_ne_zero.mpr hk0
      have hk_le : (k : ℕ) ≤ K := Nat.le_of_lt k.isLt
      have hq := hprod_bounds k hk_le
      have hlambda_pos : 0 < iterated_covariance_parameter a B k := by
        rw [iterated_covariance_parameter]
        exact mul_pos (mul_pos (by norm_num) (hB k hk_le)) hq.1
      have hprecision :
          (a k) ^ 2 / (1 - (a k) ^ 2) =
            2 * iterated_covariance_parameter a B k + 2 := by
        have hschedule := hrec k hk_one k.isLt
        have hden :
            0 < 2 * iterated_covariance_parameter a B k + 3 := by
          nlinarith
        rw [hschedule]
        field_simp [ne_of_gt hden]
        ring
      apply euclidean_hessian_bounds_give_strong_convexity_and_smoothness
      · nlinarith
      · nlinarith
      · exact hTrajectory.backward_potential_twice_continuously_differentiable k y
      · intro x u
        rw [hTrajectory.backward_hessian_quadratic_form, hprecision]
        rw [← EuclideanSpace.real_norm_sq_eq]
        have hf := hforward_bounds (Fin.castSucc k) x u
        have hf' :
            (1 - iterated_covariance_parameter a B k) * ‖u‖ ^ 2 ≤
                (fderiv ℝ (fderiv ℝ
                  (fun z : sampling_point d =>
                    -Real.log
                      (hTrajectory.forwardDensity (Fin.castSucc k) z))) x) u u ∧
              (fderiv ℝ (fderiv ℝ
                  (fun z : sampling_point d =>
                    -Real.log
                      (hTrajectory.forwardDensity (Fin.castSucc k) z))) x) u u ≤
                2 * ‖u‖ ^ 2 := by
          simpa using hf
        constructor <;> nlinarith [sq_nonneg ‖u‖]

@[blueprint "lem:exact-reverse-backward-step"
  (statement := /-- Let a reverse sampling path and a source measure form a source-faithful multimodal trajectory.  For every $k<K$, binding the forward marginal at index $k+1$ with the trajectory's $k$th reverse conditional kernel gives the forward marginal at index $k$. -/)
  (proof := /-- Fix $k<K$ and a measurable set $T$.  Evaluate the bound measure on $T$ and apply the backward disintegration identity from \cref{def:multimodal-forward-trajectory} with the other measurable set equal to the whole state space.  The left-hand side is the defining integral for the bind, while the right-hand side reduces to the index-$k$ forward marginal of $T$ because every forward transition kernel has total mass one.  Equality on every measurable $T$ proves equality of the measures. -/)
  (title := /-- One exact backward step recovers the preceding marginal -/)
  (latexEnv := "lemma")]
lemma exact_reverse_backward_step {K d : ℕ} (a B : ℕ → ℝ)
    (path : reverse_sampling_path K d)
    (sourceTarget : MeasureTheory.Measure (sampling_point d))
    (hTrajectory : multimodal_forward_trajectory a B path sourceTarget)
    (k : Fin K) :
    (hTrajectory.forwardLaw (Fin.succ k)).bind ((path.backward k).target) =
      hTrajectory.forwardLaw (Fin.castSucc k) := by
  ext t ht
  rw [MeasureTheory.Measure.bind_apply ht (path.backward k).target.aemeasurable]
  have htransition_univ (x : sampling_point d) :
      hTrajectory.forwardTransition k x Set.univ = 1 := by
    rw [hTrajectory.affine_gaussian_transition]
    rw [MeasureTheory.Measure.map_apply (by fun_prop) MeasurableSet.univ]
    simp
  simpa [htransition_univ] using
    hTrajectory.backward_disintegration k Set.univ t MeasurableSet.univ ht

@[blueprint "lem:reverse-fin-fold-telescope"
  (statement := /-- Let $x_0,\ldots,x_K$ be elements of a type, let $b_k$ be elements of a second type, and let $A$ be an action satisfying $A(x_{k+1},b_k)=x_k$ for every $k<K$.  Starting at $x_K$ and folding $A$ against $b_{K-1},\ldots,b_0$ in that order yields $x_0$. -/)
  (proof := /-- Proceed by induction on $K$.  The assertion is immediate for $K=0$.  For $K+1$, the first map in the reverse enumeration is $s_K$, which sends $x_{K+1}$ to $x_K$ by hypothesis.  The remaining reverse enumeration consists of $s_{K-1},\ldots,s_0$, so the induction hypothesis applied to the initial segment $x_0,\ldots,x_K$ gives $x_0$. -/)
  (title := /-- Telescoping a reverse finite fold -/)
  (latexEnv := "lemma")]
lemma reverse_fin_fold_telescope {α β : Type*} {K : ℕ}
    (x : Fin (K + 1) → α) (item : Fin K → β) (act : α → β → α)
    (hstep : ∀ k, act (x (Fin.succ k)) (item k) = x (Fin.castSucc k)) :
    (List.ofFn fun i : Fin K => item (Fin.rev i)).foldl act
        (x (Fin.last K)) = x 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [List.ofFn_succ]
      simp only [List.foldl_cons]
      rw [show act (x (Fin.last (K + 1)))
          (item (Fin.rev (0 : Fin (K + 1)))) =
          x (Fin.castSucc (Fin.last K)) by
        simpa using hstep (Fin.last K)]
      simpa [Fin.rev_succ] using
        ih (x := fun i => x i.castSucc) (item := fun i => item i.castSucc)
          (fun k => by simpa using hstep k.castSucc)

@[blueprint "lem:exact-reverse-target-eq-source-target"
  (statement := /-- Let $K,d\in\mathbb{N}$, let $a,B:\mathbb{N}\to\mathbb{R}$, let a reverse sampling path of length $K$ in $\mathbb{R}^d$ and a measure $\mu_Z$ form a source-faithful multimodal forward trajectory, and denote its positive early-stopping scale by $\sigma_{\mathrm{tar}}$.  Then exact composition of the terminal marginal with the reverse conditional kernels in reverse chronological order equals the trajectory's index-zero forward marginal.  Moreover, the pushforward of this exact reverse target under $y\mapsto\sqrt{2}\sigma_{\mathrm{tar}}y$ equals $\mu_Z$. -/)
  (proof := /-- The terminal-marginal identity in \cref{def:multimodal-forward-trajectory} identifies the initial measure in \cref{def:exact-reverse-target,def:compose-reverse-kernels} with the index-$K$ forward marginal.  By \cref{lem:exact-reverse-backward-step}, binding the index-$(k+1)$ marginal with the $k$th reverse kernel gives the index-$k$ marginal.  Applying \cref{lem:reverse-fin-fold-telescope} to the reverse enumeration of these kernels proves that the exact reverse target is the index-zero forward marginal.

  For the second equality, put $c=\sqrt{2}\sigma_{\mathrm{tar}}$.  Positivity of the trajectory scale in \cref{def:multimodal-forward-trajectory} gives $c>0$, so the coordinatewise maps $z\mapsto z/c$ and $y\mapsto cy$ are measurable inverses.  Fix a measurable set $S$.  Expand the pushforward in \cref{def:unscale-early-stopped-law} and the index-zero marginal as a bind over the data law.  The initial-forward-law identity in \cref{def:multimodal-forward-trajectory} replaces each conditional law by the pushforward of the early-stopping kernel under $z\mapsto z/c$.  Since the two scaling maps are inverse, its value on the preimage of $S$ is the early-stopping kernel's value on $S$.  The two bind integrals are therefore equal, and the source-target identity in \cref{def:multimodal-forward-trajectory} identifies the latter integral with $\mu_Z(S)$.  Extensionality over measurable $S$ proves the claimed pushforward equality. -/)
  (title := /-- Exact reversal followed by inverse scaling recovers the source target -/)
  (latexEnv := "lemma")]
lemma exact_reverse_target_eq_source_target {K d : ℕ} (a B : ℕ → ℝ)
    (path : reverse_sampling_path K d)
    (sourceTarget : MeasureTheory.Measure (sampling_point d))
    (hTrajectory : multimodal_forward_trajectory a B path sourceTarget) :
    exact_reverse_target path =
        hTrajectory.forwardLaw ⟨0, Nat.zero_lt_succ K⟩ ∧
      unscale_early_stopped_law hTrajectory.sigmaTarget
        (exact_reverse_target path) = sourceTarget := by
  have hExact : exact_reverse_target path =
      hTrajectory.forwardLaw ⟨0, Nat.zero_lt_succ K⟩ := by
    unfold exact_reverse_target compose_reverse_kernels
    rw [hTrajectory.terminal_marginal]
    have hkernel_list :
        (do
          let kernel ← List.ofFn fun i : Fin K =>
            (path.backward (Fin.rev i)).target
          pure (kernel : sampling_point d →
            MeasureTheory.Measure (sampling_point d))) =
          List.ofFn fun i : Fin K =>
            ((path.backward (Fin.rev i)).target :
              sampling_point d →
                MeasureTheory.Measure (sampling_point d)) := by
      simpa only [List.bind_eq_flatMap, Function.comp_def,
        List.map_ofFn] using
        List.flatMap_pure_eq_map
          (fun kernel : ProbabilityTheory.Kernel
              (sampling_point d) (sampling_point d) =>
            (kernel : sampling_point d →
              MeasureTheory.Measure (sampling_point d)))
          (List.ofFn fun i : Fin K =>
            (path.backward (Fin.rev i)).target)
    rw [hkernel_list]
    exact reverse_fin_fold_telescope hTrajectory.forwardLaw
      (fun k => ((path.backward k).target :
        sampling_point d → MeasureTheory.Measure (sampling_point d)))
      (fun μ kernel => μ.bind kernel)
      (exact_reverse_backward_step a B path sourceTarget hTrajectory)
  constructor
  · exact hExact
  · rw [hExact]
    have hscale_ne :
        Real.sqrt 2 * hTrajectory.sigmaTarget ≠ 0 := by
      exact mul_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num))
        (ne_of_gt hTrajectory.sigmaTarget_pos)
    have hscale_normalize :
        (fun z : sampling_point d => WithLp.toLp 2 fun i =>
          Real.sqrt 2 * hTrajectory.sigmaTarget *
            (z i / (Real.sqrt 2 * hTrajectory.sigmaTarget))) = id := by
      funext z
      ext i
      field_simp [ne_of_gt hTrajectory.sigmaTarget_pos] <;> rfl
    have hscale_measurable : Measurable
        (fun y : sampling_point d => WithLp.toLp 2 fun i =>
          Real.sqrt 2 * hTrajectory.sigmaTarget * y i) := by
      fun_prop
    have hnormalize_measurable : Measurable
        (fun z : sampling_point d => WithLp.toLp 2 fun i =>
          z i / (Real.sqrt 2 * hTrajectory.sigmaTarget)) := by
      fun_prop
    unfold unscale_early_stopped_law
    rw [hTrajectory.forward_marginal]
    refine Eq.trans ?_ hTrajectory.source_target_eq.symm
    ext s hs
    rw [MeasureTheory.Measure.map_apply hscale_measurable hs]
    rw [MeasureTheory.Measure.bind_apply (hscale_measurable hs)
      (hTrajectory.forwardGivenData
        ⟨0, Nat.zero_lt_succ K⟩).aemeasurable]
    rw [MeasureTheory.Measure.bind_apply hs
      hTrajectory.earlyStoppingKernel.aemeasurable]
    apply MeasureTheory.lintegral_congr
    intro x
    rw [hTrajectory.initial_forward_law]
    rw [← MeasureTheory.Measure.map_apply hscale_measurable hs]
    rw [MeasureTheory.Measure.map_map hscale_measurable
      hnormalize_measurable]
    rw [show
      (fun y : sampling_point d => WithLp.toLp 2 fun i =>
        Real.sqrt 2 * hTrajectory.sigmaTarget * y i) ∘
        (fun z : sampling_point d => WithLp.toLp 2 fun i =>
          z i / (Real.sqrt 2 * hTrajectory.sigmaTarget)) = id by
      simpa [Function.comp_def] using hscale_normalize]
    simp

@[blueprint "lem:sampling-distance-map-contraction"
  (statement := /-- Let $D$ be either total variation or Kullback--Leibler divergence.  For measurable spaces $\alpha$ and $\beta$, probability measures $\mu,\nu$ on $\alpha$, and a measurable map $f:\alpha\to\beta$, the discrepancy between the pushforward laws satisfies $D(f_\#\mu,f_\#\nu)\leq D(\mu,\nu)$. -/)
  (proof := /-- Unfold \cref{def:measure-sampling-distance} and split into the two cases of \cref{def:sampling-distance}.  In the total-variation case, \cref{def:probability-total-variation-distance} expresses the discrepancy as a supremum over measurable sets.  For every measurable $S\subseteq\beta$, measurability of $f$ makes $f^{-1}(S)$ measurable, and the two pushforward masses of $S$ equal the original masses of $f^{-1}(S)$; hence the corresponding term is bounded by the source supremum.  In the Kullback--Leibler case, the result is immediate if $\operatorname{KL}(\mu\mathbin\|\nu)=\infty$.  Otherwise, $\mu$ is absolutely continuous with respect to $\nu$ and its log-likelihood ratio is integrable.  The Radon--Nikodym derivative of the two pushforwards, evaluated after $f$, is almost everywhere the conditional expectation of $d\mu/d\nu$ with respect to the sigma-algebra pulled back by $f$.  Conditional Jensen's inequality for the convex Kullback--Leibler generator therefore bounds its value by the conditional expectation of the generator applied to $d\mu/d\nu$.  Integrating this almost-everywhere inequality, using preservation of integrals by conditional expectation and the integral representation of Kullback--Leibler divergence, gives the required contraction. -/)
  (title := /-- Sampling discrepancies contract under measurable pushforward -/)
  (latexEnv := "lemma")]
lemma sampling_distance_map_contraction {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (D : sampling_distance)
    (f : α → β) (hf : Measurable f)
    (μ ν : MeasureTheory.Measure α)
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν] :
    measure_sampling_distance D (MeasureTheory.Measure.map f μ)
      (MeasureTheory.Measure.map f ν) ≤ measure_sampling_distance D μ ν := by
  cases D with
  | totalVariation =>
      unfold measure_sampling_distance probability_total_variation_distance
      refine iSup_le fun s => iSup_le fun hs => ?_
      rw [MeasureTheory.Measure.map_apply hf hs, MeasureTheory.Measure.map_apply hf hs]
      exact le_iSup_of_le (f ⁻¹' s) (le_iSup_of_le (hf hs) le_rfl)
  | kullbackLeibler =>
      simp only [measure_sampling_distance]
      by_cases htop : InformationTheory.klDiv μ ν = ∞
      · rw [htop]
        exact le_top
      have hdata := InformationTheory.klDiv_ne_top_iff.mp htop
      have hac : MeasureTheory.Measure.AbsolutelyContinuous μ ν := hdata.1
      have hint : MeasureTheory.Integrable (MeasureTheory.llr μ ν) μ := hdata.2
      have hac_map : MeasureTheory.Measure.AbsolutelyContinuous
          (MeasureTheory.Measure.map f μ) (MeasureTheory.Measure.map f ν) := hac.map hf
      rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac hac_map,
        InformationTheory.klDiv_eq_lintegral_klFun_of_ac hac,
        MeasureTheory.lintegral_map (by fun_prop) hf]
      have hrn := MeasureTheory.toReal_rnDeriv_map hac hf
      have hgen_int :
          MeasureTheory.Integrable
            (fun x => InformationTheory.klFun (μ.rnDeriv ν x).toReal) ν :=
        (InformationTheory.integrable_klFun_rnDeriv_iff hac).2 hint
      have hgen_nonneg :
          0 ≤ᵐ[ν] (fun x => InformationTheory.klFun (μ.rnDeriv ν x).toReal) :=
        Filter.Eventually.of_forall fun x =>
          InformationTheory.klFun_nonneg ENNReal.toReal_nonneg
      have hjensen :=
        InformationTheory.convexOn_klFun.map_condExp_le
          hf.comap_le
          (InformationTheory.continuous_klFun.lowerSemicontinuous.lowerSemicontinuousOn
            (Set.Ici 0))
          (Filter.Eventually.of_forall fun x => ENNReal.toReal_nonneg)
          isClosed_Ici MeasureTheory.Measure.integrable_toReal_rnDeriv hgen_int
      have hpoint :
          (fun x => InformationTheory.klFun
            ((MeasureTheory.Measure.map f μ).rnDeriv
              (MeasureTheory.Measure.map f ν) (f x)).toReal) ≤ᵐ[ν]
            MeasureTheory.condExp (m := ‹MeasurableSpace β›.comap f) ν
              (InformationTheory.klFun ∘ fun x => (μ.rnDeriv ν x).toReal) := by
        filter_upwards [hrn, hjensen] with x hx hle
        simpa [Function.comp_apply, hx] using hle
      have hgen_int_comp :
          MeasureTheory.Integrable
            (InformationTheory.klFun ∘ fun x => (μ.rnDeriv ν x).toReal) ν := by
        simpa [Function.comp_def] using hgen_int
      have hgen_nonneg_comp :
          0 ≤ᵐ[ν] (InformationTheory.klFun ∘ fun x => (μ.rnDeriv ν x).toReal) := by
        simpa [Function.comp_def] using hgen_nonneg
      have hcond_int :
          MeasureTheory.Integrable
            (MeasureTheory.condExp (m := ‹MeasurableSpace β›.comap f) ν
              (InformationTheory.klFun ∘ fun x => (μ.rnDeriv ν x).toReal)) ν :=
        MeasureTheory.integrable_condExp
      have hcond_nonneg :
          0 ≤ᵐ[ν] MeasureTheory.condExp (m := ‹MeasurableSpace β›.comap f) ν
            (InformationTheory.klFun ∘ fun x => (μ.rnDeriv ν x).toReal) :=
        MeasureTheory.condExp_nonneg hgen_nonneg_comp
      refine (MeasureTheory.lintegral_mono_ae
        (hpoint.mono fun x hx => ENNReal.ofReal_mono hx)).trans_eq ?_
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
          hcond_int hcond_nonneg,
        MeasureTheory.integral_condExp hf.comap_le,
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgen_int_comp hgen_nonneg_comp]
      rfl

@[blueprint "lem:terminal-problem-condition-number"
  (statement := /-- Let $K,d\in\mathbb{N}$, let $a,B:\mathbb{N}\to\mathbb{R}$, and let a reverse sampling path of length $K$ in dimension $d$ be given.  Assume $K>0$, $B_k>0$ for every $k\leq K$, $0<a_k<1$ for every $k<K$, $a_0=1/\sqrt{2}$, and, for $1\leq k<K$, $a_k^2=(2\lambda_k+2)/(2\lambda_k+3)$, where $\lambda_k=4B_k\prod_{\ell<k}a_\ell^2$.  Assume also the stated multimodal Hessian control: the terminal potential is normalized, $(1-\lambda_K)$-strongly convex, and has $2$-Lipschitz gradient, while every backward potential at $k<K$ is normalized, $(\lambda_k+2)$-strongly convex, and has $2(\lambda_k+2)$-Lipschitz gradient.  If $\prod_{\ell<K}a_\ell^2\leq (8B_K)^{-1}$, then the terminal sampling problem is strongly log-concave with condition number at most $4$. -/)
  (proof := /-- By \cref{def:uses-adaptive-stepsizes}, $B_K>0$.  Multiplying the inequality in \cref{def:trajectory-length-condition} by the positive number $8B_K$ and using \cref{def:iterated-covariance-parameter} gives $\lambda_K\leq 1/2$.  Consequently, $m:=1-\lambda_K$ is positive and $L:=2$ satisfies $0\leq L\leq4m$.  By \cref{def:has-multimodal-hessian-control}, the terminal potential is normalized, is $m$-strongly convex, and has $L$-Lipschitz gradient for every parameter.  These witnesses establish the condition-number bound in \cref{def:is-strongly-log-concave-with-condition-number-at-most}. -/)
  (title := /-- Conditioning of the terminal marginal -/)
  (latexEnv := "lemma")]
lemma terminal_problem_condition_number {K d : ℕ} (a B : ℕ → ℝ)
    (path : reverse_sampling_path K d)
    (hAdaptive : uses_adaptive_stepsizes K a B)
    (hControl : has_multimodal_hessian_control a B path)
    (hLength : trajectory_length_condition K a B) :
    is_strongly_log_concave_with_condition_number_at_most path.terminal 4 := by
  rcases hAdaptive with ⟨_, hB, _, _, _⟩
  rcases hControl with ⟨hProb, hTerminal, _⟩
  have hBK : 0 < B K := hB K le_rfl
  have hden : 0 < 8 * B K := by positivity
  have hscaled : (∏ ℓ ∈ Finset.range K, (a ℓ) ^ 2) * (8 * B K) ≤ 1 :=
    (le_div_iff₀ hden).mp hLength
  have hLambda : iterated_covariance_parameter a B K ≤ (1 : ℝ) / 2 := by
    unfold iterated_covariance_parameter
    nlinarith
  refine ⟨hProb, 1 - iterated_covariance_parameter a B K, 2, ?_, by norm_num, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · exact hTerminal

@[blueprint "lem:backward-problems-condition-number"
  (statement := /-- Let $K,d\in\mathbb{N}$, let $a,B:\mathbb{N}\to\mathbb{R}$, and let a reverse sampling path of length $K$ in dimension $d$ be given.  If $a$ and $B$ satisfy the adaptive stepsize schedule and the path satisfies the corrected multimodal Hessian-control condition, then, for every $k\in\operatorname{Fin}(K)$, the backward conditional problem $p_{k\mid k+1}$ is strongly log-concave with condition number at most $4$. -/)
  (proof := /-- Fix $k\in\operatorname{Fin}(K)$.  By \cref{def:has-multimodal-hessian-control}, the backward conditional problem is a probability potential.  If $k=0$, its potential is $1$-strongly convex and has $4$-Lipschitz gradient, so the witnesses $m=1$ and $L=4$ give condition number at most $4$.  Suppose instead that $1\leq k$.  The same Hessian-control condition gives $(\lambda_k+2)$-strong convexity and a $2(\lambda_k+2)$-Lipschitz gradient.  By \cref{def:uses-adaptive-stepsizes}, one has $B_k>0$.  Since every squared stepsize is nonnegative, \cref{def:iterated-covariance-parameter} gives $\lambda_k\geq0$.  Thus $m:=\lambda_k+2$ is positive, $L:=2m$ is nonnegative, and $L\leq4m$.  In either case these witnesses satisfy \cref{def:is-strongly-log-concave-with-condition-number-at-most}.  Since $k$ was arbitrary, the assertion follows for every $k\in\operatorname{Fin}(K)$. -/)
  (title := /-- Conditioning of all backward conditionals -/)
  (latexEnv := "lemma")]
lemma backward_problems_condition_number {K d : ℕ} (a B : ℕ → ℝ)
    (path : reverse_sampling_path K d)
    (hAdaptive : uses_adaptive_stepsizes K a B)
    (hControl : has_multimodal_hessian_control a B path) :
    ∀ k : Fin K,
      is_strongly_log_concave_with_condition_number_at_most (path.backward k) 4 := by
  intro k
  rcases hControl.2.2 k with ⟨hProb, hBounds⟩
  refine ⟨hProb, ?_⟩
  by_cases hk : (k : ℕ) = 0
  · refine ⟨1, 4, by norm_num, by norm_num, by norm_num, ?_⟩
    intro y
    simpa [hk] using hBounds y
  · have hB : 0 < B k := hAdaptive.2.1 k (Nat.le_of_lt k.isLt)
    have hnonneg : 0 ≤ iterated_covariance_parameter a B k := by
      unfold iterated_covariance_parameter
      positivity
    refine ⟨iterated_covariance_parameter a B k + 2,
      2 * (iterated_covariance_parameter a B k + 2),
      by nlinarith, by nlinarith, by nlinarith, ?_⟩
    intro y
    simpa [hk] using hBounds y

@[blueprint "lem:all-subproblems-condition-number"
  (statement := /-- Let $K,d\in\mathbb{N}$, let $a,B:\mathbb{N}\to\mathbb{R}$, let $\lambda_j=4B_j\prod_{\ell<j}a_\ell^2$, and let a reverse sampling path of length $K$ in dimension $d$ be given.  Assume $K>0$, $B_j>0$ for every $j\leq K$, $0<a_j<1$ for every $j<K$, $a_0=1/\sqrt{2}$, $a_j^2=(2\lambda_j+2)/(2\lambda_j+3)$ for every $1\leq j<K$, and $B_0\leq1/2$.  Assume that the terminal and every backward problem have normalized probability potentials; for every parameter, the terminal potential is $(1-\lambda_K)$-strongly convex with $2$-Lipschitz gradient, the backward potential at $j=0$ is $1$-strongly convex with $4$-Lipschitz gradient, and every backward potential at $1\leq j<K$ is $(\lambda_j+2)$-strongly convex with $2(\lambda_j+2)$-Lipschitz gradient.  If $\prod_{\ell<K}a_\ell^2\leq(8B_K)^{-1}$, then the terminal problem and every backward problem indexed by $j\in\operatorname{Fin}(K)$ are strongly log-concave with condition number at most $4$. -/)
  (proof := /-- Applying \cref{lem:terminal-problem-condition-number} to the adaptive-schedule, Hessian-control, and trajectory-length hypotheses proves the assertion for the terminal problem.  Applying \cref{lem:backward-problems-condition-number} to the adaptive-schedule and Hessian-control hypotheses proves the assertion for every backward problem indexed by $\operatorname{Fin}(K)$.  These two assertions form the required conjunction. -/)
  (title := /-- Conditioning of the complete sub-problem collection -/)
  (latexEnv := "lemma")]
lemma all_subproblems_condition_number {K d : ℕ} (a B : ℕ → ℝ)
    (path : reverse_sampling_path K d)
    (hAdaptive : uses_adaptive_stepsizes K a B)
    (hControl : has_multimodal_hessian_control a B path)
    (hLength : trajectory_length_condition K a B) :
    is_strongly_log_concave_with_condition_number_at_most path.terminal 4 ∧
      ∀ k : Fin K,
        is_strongly_log_concave_with_condition_number_at_most (path.backward k) 4 := by
  exact ⟨terminal_problem_condition_number a B path hAdaptive hControl hLength,
    backward_problems_condition_number a B path hAdaptive hControl⟩

@[blueprint "lem:probability-total-variation-integral-bound"
  (statement := /-- Let $\mu$ and $\nu$ be probability measures on a measurable space, and let $f$ be a measurable function with values in $[0,1]$.  Then the absolute difference between the expectations of $f$ under $\mu$ and $\nu$, embedded in $\mathbb{R}_{\geq0}^{\infty}$, is at most the total-variation distance between $\mu$ and $\nu$. -/)
  (proof := /-- By the layer-cake formula, each expectation is the integral over $0<t\leq1$ of the probability of the measurable superlevel set $\{f>t\}$.  For every such $t$, \cref{def:probability-total-variation-distance} bounds the absolute difference of these two probabilities by the total-variation distance.  The norm inequality for integrals and the fact that the interval $(0,1]$ has length one give the claim. -/)
  (title := /-- Total variation controls bounded expectations -/)
  (latexEnv := "lemma")]
lemma probability_total_variation_integral_bound {α : Type*} [MeasurableSpace α]
    (μ ν : MeasureTheory.Measure α)
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν]
    (f : α → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    ENNReal.ofReal |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤
      probability_total_variation_distance μ ν := by
  let V := probability_total_variation_distance μ ν
  have hV_le : V ≤ 1 := by
    unfold V probability_total_variation_distance
    refine iSup_le fun s => iSup_le fun _ => ?_
    rw [ENNReal.ofReal_le_one]
    have hμs : (μ s).toReal ≤ 1 := by
      apply ENNReal.toReal_mono ENNReal.one_ne_top
      simpa using MeasureTheory.measure_mono (μ := μ) (Set.subset_univ s)
    have hνs : (ν s).toReal ≤ 1 := by
      apply ENNReal.toReal_mono ENNReal.one_ne_top
      simpa using MeasureTheory.measure_mono (μ := ν) (Set.subset_univ s)
    have hμs0 : 0 ≤ (μ s).toReal := ENNReal.toReal_nonneg
    have hνs0 : 0 ≤ (ν s).toReal := ENNReal.toReal_nonneg
    rw [abs_le]
    constructor <;> linarith
  have hV_top : V ≠ ∞ := ne_of_lt (lt_of_le_of_lt hV_le ENNReal.one_lt_top)
  have hf_int_μ : MeasureTheory.Integrable f μ :=
    MeasureTheory.Integrable.of_bound hf.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [hf0 x], hf1 x⟩)
  have hf_int_ν : MeasureTheory.Integrable f ν :=
    MeasureTheory.Integrable.of_bound hf.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [hf0 x], hf1 x⟩)
  have hμ_layer := hf_int_μ.integral_eq_integral_meas_lt
    (Filter.Eventually.of_forall hf0)
  have hν_layer := hf_int_ν.integral_eq_integral_meas_lt
    (Filter.Eventually.of_forall hf0)
  have hμ_restrict :
      ∫ t in Set.Ioi (0 : ℝ), μ.real {x | t < f x} =
        ∫ t in Set.Ioc (0 : ℝ) 1, μ.real {x | t < f x} := by
    apply MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
      measurableSet_Ioi.nullMeasurableSet
      (fun _ ht => ht.1)
    refine Filter.Eventually.of_forall fun t ht => ?_
    have ht1 : 1 < t := by
      rcases ht with ⟨ht0, ht_not⟩
      simp only [Set.mem_Ioi] at ht0
      simp only [Set.mem_Ioc, not_and] at ht_not
      exact lt_of_not_ge (ht_not ht0)
    have hempty : {x | t < f x} = ∅ := by
      exact Set.eq_empty_iff_forall_notMem.mpr fun x hx =>
        (not_lt_of_ge (hf1 x)) (lt_trans ht1 hx)
    simp [hempty]
  have hν_restrict :
      ∫ t in Set.Ioi (0 : ℝ), ν.real {x | t < f x} =
        ∫ t in Set.Ioc (0 : ℝ) 1, ν.real {x | t < f x} := by
    apply MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
      measurableSet_Ioi.nullMeasurableSet
      (fun _ ht => ht.1)
    refine Filter.Eventually.of_forall fun t ht => ?_
    have ht1 : 1 < t := by
      rcases ht with ⟨ht0, ht_not⟩
      simp only [Set.mem_Ioi] at ht0
      simp only [Set.mem_Ioc, not_and] at ht_not
      exact lt_of_not_ge (ht_not ht0)
    have hempty : {x | t < f x} = ∅ := by
      exact Set.eq_empty_iff_forall_notMem.mpr fun x hx =>
        (not_lt_of_ge (hf1 x)) (lt_trans ht1 hx)
    simp [hempty]
  have hμ_meas : Measurable (fun t : ℝ => μ.real {x | t < f x}) := by
    apply Measurable.ennreal_toReal
    exact Antitone.measurable fun _ _ htu =>
      MeasureTheory.measure_mono fun _ hx => lt_of_le_of_lt htu hx
  have hν_meas : Measurable (fun t : ℝ => ν.real {x | t < f x}) := by
    apply Measurable.ennreal_toReal
    exact Antitone.measurable fun _ _ htu =>
      MeasureTheory.measure_mono fun _ hx => lt_of_le_of_lt htu hx
  have hμ_int : MeasureTheory.IntegrableOn (fun t : ℝ => μ.real {x | t < f x})
      (Set.Ioc 0 1) := by
    apply MeasureTheory.IntegrableOn.of_bound (by simp) hμ_meas.aestronglyMeasurable.restrict 1
    refine Filter.Eventually.of_forall fun t => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg MeasureTheory.measureReal_nonneg]
    calc
      μ.real {x | t < f x} ≤ μ.real Set.univ :=
        MeasureTheory.measureReal_mono (Set.subset_univ {x | t < f x})
      _ = 1 := by simp
  have hν_int : MeasureTheory.IntegrableOn (fun t : ℝ => ν.real {x | t < f x})
      (Set.Ioc 0 1) := by
    apply MeasureTheory.IntegrableOn.of_bound (by simp) hν_meas.aestronglyMeasurable.restrict 1
    refine Filter.Eventually.of_forall fun t => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg MeasureTheory.measureReal_nonneg]
    calc
      ν.real {x | t < f x} ≤ ν.real Set.univ :=
        MeasureTheory.measureReal_mono (Set.subset_univ {x | t < f x})
      _ = 1 := by simp
  rw [hμ_layer, hν_layer, hμ_restrict, hν_restrict,
    ← MeasureTheory.integral_sub hμ_int hν_int]
  apply (ENNReal.ofReal_le_iff_le_toReal hV_top).2
  calc
    |∫ t in Set.Ioc (0 : ℝ) 1, μ.real {x | t < f x} - ν.real {x | t < f x}| =
        ‖∫ t in Set.Ioc (0 : ℝ) 1, μ.real {x | t < f x} - ν.real {x | t < f x}‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ ∫ _t in Set.Ioc (0 : ℝ) 1, V.toReal := by
      apply MeasureTheory.norm_integral_le_of_norm_le (by simp)
      refine Filter.Eventually.of_forall fun t => ?_
      rw [Real.norm_eq_abs]
      apply (ENNReal.ofReal_le_iff_le_toReal hV_top).1
      unfold V probability_total_variation_distance
      exact le_iSup_of_le {x | t < f x}
        (le_iSup_of_le (hf measurableSet_Ioi) le_rfl)
    _ = V.toReal := by simp

@[blueprint "lem:probability-total-variation-bind-le"
  (statement := /-- Let $\mu$ and $\nu$ be probability measures, let $\kappa$ and $\eta$ be Markov kernels, and let $\delta<\infty$.  If the total-variation distance between $\kappa(x)$ and $\eta(x)$ is at most $\delta$ for every $x$, then the total-variation distance between $\mu\mathbin{\mathrm{bind}}\kappa$ and $\nu\mathbin{\mathrm{bind}}\eta$ is at most the distance between $\mu$ and $\nu$ plus $\delta$. -/)
  (proof := /-- Fix a measurable output event.  Expand both bound measures as integrals and insert the integral of the exact-kernel probability against $\mu$.  The first resulting difference is at most $\delta$ by the pointwise kernel hypothesis and the norm inequality for integrals.  The second is at most the total-variation distance between $\mu$ and $\nu$ by \cref{lem:probability-total-variation-integral-bound}, since an event probability under a Markov kernel is a measurable $[0,1]$-valued function.  The triangle inequality and \cref{def:probability-total-variation-distance} give the result after taking the supremum over events. -/)
  (title := /-- One-step total-variation propagation through kernels -/)
  (latexEnv := "lemma")]
lemma probability_total_variation_bind_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : MeasureTheory.Measure α)
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν]
    (κ η : ProbabilityTheory.Kernel α β)
    [ProbabilityTheory.IsMarkovKernel κ] [ProbabilityTheory.IsMarkovKernel η]
    (δ : ℝ≥0∞) (hδ : δ ≠ ∞)
    (hlocal : ∀ x, probability_total_variation_distance (κ x) (η x) ≤ δ) :
    probability_total_variation_distance (μ.bind κ) (ν.bind η) ≤
      probability_total_variation_distance μ ν + δ := by
  let V := probability_total_variation_distance μ ν
  have hV_le : V ≤ 1 := by
    unfold V probability_total_variation_distance
    refine iSup_le fun s => iSup_le fun _ => ?_
    rw [ENNReal.ofReal_le_one]
    have hμs : (μ s).toReal ≤ 1 := by
      apply ENNReal.toReal_mono ENNReal.one_ne_top
      simpa using MeasureTheory.measure_mono (μ := μ) (Set.subset_univ s)
    have hνs : (ν s).toReal ≤ 1 := by
      apply ENNReal.toReal_mono ENNReal.one_ne_top
      simpa using MeasureTheory.measure_mono (μ := ν) (Set.subset_univ s)
    have hμs0 : 0 ≤ (μ s).toReal := ENNReal.toReal_nonneg
    have hνs0 : 0 ≤ (ν s).toReal := ENNReal.toReal_nonneg
    rw [abs_le]
    constructor <;> linarith
  have hV_top : V ≠ ∞ := ne_of_lt (lt_of_le_of_lt hV_le ENNReal.one_lt_top)
  unfold probability_total_variation_distance
  refine iSup_le fun s => iSup_le fun hs => ?_
  have hκ_meas : Measurable (fun x => (κ x s).toReal) :=
    Measurable.ennreal_toReal (κ.measurable_coe hs)
  have hη_meas : Measurable (fun x => (η x s).toReal) :=
    Measurable.ennreal_toReal (η.measurable_coe hs)
  have hκ_one : ∀ x, (κ x s).toReal ≤ 1 := fun x => by
    apply ENNReal.toReal_mono ENNReal.one_ne_top
    simpa using MeasureTheory.measure_mono (μ := κ x) (Set.subset_univ s)
  have hη_one : ∀ x, (η x s).toReal ≤ 1 := fun x => by
    apply ENNReal.toReal_mono ENNReal.one_ne_top
    simpa using MeasureTheory.measure_mono (μ := η x) (Set.subset_univ s)
  have hκ_int : MeasureTheory.Integrable (fun x => (κ x s).toReal) μ :=
    MeasureTheory.Integrable.of_bound hκ_meas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        exact hκ_one x)
  have hη_int_μ : MeasureTheory.Integrable (fun x => (η x s).toReal) μ :=
    MeasureTheory.Integrable.of_bound hη_meas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        exact hη_one x)
  have hη_int_ν : MeasureTheory.Integrable (fun x => (η x s).toReal) ν :=
    MeasureTheory.Integrable.of_bound hη_meas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        exact hη_one x)
  have hκ_finite : ∀ᵐ x ∂μ, κ x s < ∞ :=
    Filter.Eventually.of_forall fun x => lt_of_le_of_lt
      (by simpa using MeasureTheory.measure_mono (μ := κ x) (Set.subset_univ s))
      ENNReal.one_lt_top
  have hη_finite_μ : ∀ᵐ x ∂μ, η x s < ∞ :=
    Filter.Eventually.of_forall fun x => lt_of_le_of_lt
      (by simpa using MeasureTheory.measure_mono (μ := η x) (Set.subset_univ s))
      ENNReal.one_lt_top
  have hη_finite_ν : ∀ᵐ x ∂ν, η x s < ∞ :=
    Filter.Eventually.of_forall fun x => lt_of_le_of_lt
      (by simpa using MeasureTheory.measure_mono (μ := η x) (Set.subset_univ s))
      ENNReal.one_lt_top
  have hbindκ : (μ.bind κ s).toReal = ∫ x, (κ x s).toReal ∂μ := by
    rw [MeasureTheory.Measure.bind_apply hs κ.aemeasurable,
      ← MeasureTheory.integral_toReal (κ.measurable_coe hs).aemeasurable hκ_finite]
  have hbindη : (ν.bind η s).toReal = ∫ x, (η x s).toReal ∂ν := by
    rw [MeasureTheory.Measure.bind_apply hs η.aemeasurable,
      ← MeasureTheory.integral_toReal (η.measurable_coe hs).aemeasurable hη_finite_ν]
  have hlocal_real : ∀ x, |(κ x s).toReal - (η x s).toReal| ≤ δ.toReal := by
    intro x
    apply (ENNReal.ofReal_le_iff_le_toReal hδ).1
    exact (hlocal x).trans' (by
      unfold probability_total_variation_distance
      exact le_iSup_of_le s (le_iSup_of_le hs le_rfl))
  have hfirst :
      |∫ x, (κ x s).toReal ∂μ - ∫ x, (η x s).toReal ∂μ| ≤ δ.toReal := by
    rw [← MeasureTheory.integral_sub hκ_int hη_int_μ]
    calc
      |∫ x, (κ x s).toReal - (η x s).toReal ∂μ| =
          ‖∫ x, (κ x s).toReal - (η x s).toReal ∂μ‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∫ _x, δ.toReal ∂μ := by
        apply MeasureTheory.norm_integral_le_of_norm_le (by simp)
        exact Filter.Eventually.of_forall fun x => by
          simpa [Real.norm_eq_abs] using hlocal_real x
      _ = δ.toReal := by simp
  have hsecond_enn := probability_total_variation_integral_bound μ ν
    (fun x => (η x s).toReal) hη_meas
    (fun _ => ENNReal.toReal_nonneg) hη_one
  have hsecond :
      |∫ x, (η x s).toReal ∂μ - ∫ x, (η x s).toReal ∂ν| ≤ V.toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hV_top).1 hsecond_enn
  apply (ENNReal.ofReal_le_iff_le_toReal (ENNReal.add_ne_top.2 ⟨hV_top, hδ⟩)).2
  rw [ENNReal.toReal_add hV_top hδ]
  rw [hbindκ, hbindη]
  calc
    |∫ x, (κ x s).toReal ∂μ - ∫ x, (η x s).toReal ∂ν| ≤
        |∫ x, (κ x s).toReal ∂μ - ∫ x, (η x s).toReal ∂μ| +
          |∫ x, (η x s).toReal ∂μ - ∫ x, (η x s).toReal ∂ν| :=
      abs_sub_le _ _ _
    _ ≤ V.toReal + δ.toReal := by linarith

@[blueprint "lem:kullback-leibler-comp-prod-right-le"
  (statement := /-- Let $\mu$ be a probability measure, let $\kappa$ and $\eta$ be Markov kernels, and let $\delta<\infty$.  If $\operatorname{KL}(\kappa(x)\mathbin\|\eta(x))\leq\delta$ for every $x$, then $\operatorname{KL}(\mu\otimes\kappa\mathbin\|\mu\otimes\eta)\leq\delta$. -/)
  (proof := /-- Finiteness of each pointwise KL divergence gives $\kappa(x)\ll\eta(x)$ and hence removes the singular part in the kernel Radon--Nikodym decomposition.  Thus $\mu\otimes\kappa$ has density $(x,y)\mapsto d\kappa(x)/d\eta(x)(y)$ with respect to $\mu\otimes\eta$.  The integral formula for KL and Tonelli's theorem identify the joint divergence with the $\mu$-integral of the pointwise divergences.  The assumed uniform bound and the fact that $\mu$ has mass one yield the result. -/)
  (title := /-- Uniform conditional KL bounds the composition-product KL -/)
  (latexEnv := "lemma")]
lemma kullback_leibler_comp_prod_right_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (κ η : ProbabilityTheory.Kernel α β)
    [ProbabilityTheory.IsMarkovKernel κ] [ProbabilityTheory.IsMarkovKernel η]
    (δ : ℝ≥0∞) (hδ : δ ≠ ∞)
    (hlocal : ∀ x, InformationTheory.klDiv (κ x) (η x) ≤ δ) :
    InformationTheory.klDiv (MeasureTheory.Measure.compProd μ κ)
      (MeasureTheory.Measure.compProd μ η) ≤ δ := by
  have hlocal_top : ∀ x, InformationTheory.klDiv (κ x) (η x) ≠ ∞ := fun x =>
    ne_top_of_le_ne_top hδ (hlocal x)
  have hlocal_ac : ∀ x, MeasureTheory.Measure.AbsolutelyContinuous (κ x) (η x) := fun x =>
    (InformationTheory.klDiv_ne_top_iff.mp (hlocal_top x)).1
  have hsing : ProbabilityTheory.Kernel.singularPart κ η = 0 := by
    ext x s hs
    rw [ProbabilityTheory.Kernel.singularPart_eq_singularPart_measure,
      (MeasureTheory.Measure.singularPart_eq_zero (κ x) (η x)).2 (hlocal_ac x)]
    simp
  have hκ_density :
      κ = η.withDensity (ProbabilityTheory.Kernel.rnDeriv κ η) := by
    have hdecomp := ProbabilityTheory.Kernel.rnDeriv_add_singularPart κ η
    rw [hsing, add_zero] at hdecomp
    exact hdecomp.symm
  let F : α × β → ℝ≥0∞ := fun p => ProbabilityTheory.Kernel.rnDeriv κ η p.1 p.2
  have hF_meas : Measurable F := by
    exact ProbabilityTheory.Kernel.measurable_rnDeriv κ η
  have hjoint_density :
      MeasureTheory.Measure.compProd μ κ =
        (MeasureTheory.Measure.compProd μ η).withDensity F := by
    rw [hκ_density, MeasureTheory.Measure.compProd_withDensity
      (ProbabilityTheory.Kernel.measurable_rnDeriv κ η)]
  have hlocal_eq : ∀ x,
      InformationTheory.klDiv (κ x) (η x) =
        ∫⁻ y, ENNReal.ofReal
          (InformationTheory.klFun (ProbabilityTheory.Kernel.rnDeriv κ η x y).toReal) ∂η x := by
    intro x
    rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac (hlocal_ac x)]
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards [ProbabilityTheory.Kernel.rnDeriv_eq_rnDeriv_measure
      (κ := κ) (η := η) (a := x)] with y hy
    rw [hy]
  have hjoint_eq :
      InformationTheory.klDiv (MeasureTheory.Measure.compProd μ κ)
          (MeasureTheory.Measure.compProd μ η) =
        ∫⁻ p, ENNReal.ofReal (InformationTheory.klFun (F p).toReal)
          ∂(MeasureTheory.Measure.compProd μ η) := by
    have hjoint_ac : MeasureTheory.Measure.AbsolutelyContinuous
        (MeasureTheory.Measure.compProd μ κ)
        (MeasureTheory.Measure.compProd μ η) := by
      rw [hjoint_density]
      exact MeasureTheory.withDensity_absolutelyContinuous _ _
    have hrn_joint := MeasureTheory.Measure.rnDeriv_withDensity
      (MeasureTheory.Measure.compProd μ η) hF_meas
    rw [← hjoint_density] at hrn_joint
    rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac hjoint_ac]
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards [hrn_joint] with p hp
    rw [hp]
  rw [hjoint_eq, MeasureTheory.Measure.lintegral_compProd (by fun_prop)]
  calc
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (InformationTheory.klFun (F (x, y)).toReal) ∂η x ∂μ) =
        ∫⁻ x, InformationTheory.klDiv (κ x) (η x) ∂μ := by
      apply MeasureTheory.lintegral_congr
      intro x
      exact (hlocal_eq x).symm
    _ ≤ ∫⁻ _x, δ ∂μ := MeasureTheory.lintegral_mono hlocal
    _ = δ := by simp

@[blueprint "lem:measure-sampling-distance-bind-le"
  (statement := /-- Let $D$ be total variation or Kullback--Leibler divergence, let $\mu$ and $\nu$ be probability measures, and let $\kappa$ and $\eta$ be Markov kernels.  If $D(\kappa(x),\eta(x))\leq\delta<\infty$ for every $x$, then $D(\mu\mathbin{\mathrm{bind}}\kappa,\nu\mathbin{\mathrm{bind}}\eta)\leq D(\mu,\nu)+\delta$. -/)
  (proof := /-- For total variation, apply \cref{lem:probability-total-variation-bind-le}.  For KL, first apply \cref{lem:sampling-distance-map-contraction} to the second projection of the two composition-product measures.  The KL chain rule splits the resulting joint divergence into the marginal divergence and the common-first-marginal conditional divergence, which \cref{lem:kullback-leibler-comp-prod-right-le} bounds by $\delta$. -/)
  (title := /-- One-step propagation for the admissible sampling distances -/)
  (latexEnv := "lemma")]
lemma measure_sampling_distance_bind_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (D : sampling_distance)
    (μ ν : MeasureTheory.Measure α)
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν]
    (κ η : ProbabilityTheory.Kernel α β)
    [ProbabilityTheory.IsMarkovKernel κ] [ProbabilityTheory.IsMarkovKernel η]
    (δ : ℝ≥0∞) (hδ : δ ≠ ∞)
    (hlocal : ∀ x, measure_sampling_distance D (κ x) (η x) ≤ δ) :
    measure_sampling_distance D (μ.bind κ) (ν.bind η) ≤
      measure_sampling_distance D μ ν + δ := by
  cases D with
  | totalVariation =>
      simpa [measure_sampling_distance] using
        probability_total_variation_bind_le μ ν κ η δ hδ hlocal
  | kullbackLeibler =>
      simp only [measure_sampling_distance] at hlocal ⊢
      have hconditional := kullback_leibler_comp_prod_right_le μ κ η δ hδ hlocal
      have hcontract := sampling_distance_map_contraction
        sampling_distance.kullbackLeibler Prod.snd measurable_snd
        (MeasureTheory.Measure.compProd μ κ) (MeasureTheory.Measure.compProd ν η)
      have hmapκ : MeasureTheory.Measure.map Prod.snd
          (MeasureTheory.Measure.compProd μ κ) = μ.bind κ := by
        ext s hs
        rw [MeasureTheory.Measure.map_apply measurable_snd hs,
          MeasureTheory.Measure.bind_apply hs κ.aemeasurable,
          MeasureTheory.Measure.compProd_apply (measurable_snd hs)]
        rfl
      have hmapη : MeasureTheory.Measure.map Prod.snd
          (MeasureTheory.Measure.compProd ν η) = ν.bind η := by
        ext s hs
        rw [MeasureTheory.Measure.map_apply measurable_snd hs,
          MeasureTheory.Measure.bind_apply hs η.aemeasurable,
          MeasureTheory.Measure.compProd_apply (measurable_snd hs)]
        rfl
      have hbind_contract :
          InformationTheory.klDiv (μ.bind κ) (ν.bind η) ≤
            InformationTheory.klDiv (MeasureTheory.Measure.compProd μ κ)
              (MeasureTheory.Measure.compProd ν η) := by
        simpa [measure_sampling_distance, hmapκ, hmapη] using hcontract
      calc
        InformationTheory.klDiv (μ.bind κ) (ν.bind η) ≤
            InformationTheory.klDiv (MeasureTheory.Measure.compProd μ κ)
              (MeasureTheory.Measure.compProd ν η) := hbind_contract
        _ = InformationTheory.klDiv μ ν +
            InformationTheory.klDiv (MeasureTheory.Measure.compProd μ κ)
              (MeasureTheory.Measure.compProd μ η) :=
          InformationTheory.klDiv_compProd_eq_add μ ν κ η
        _ ≤ InformationTheory.klDiv μ ν + δ := add_le_add le_rfl hconditional

@[blueprint "lem:measure-sampling-distance-foldl-bind-le"
  (statement := /-- Let two equally long lists of Markov kernels be paired stage by stage, with every paired kernel value at sampling distance at most $\delta<\infty$.  Binding the first list from a probability law $\mu$ and the second from a probability law $\nu$ increases their sampling distance by at most the list length times $\delta$. -/)
  (proof := /-- Induct on the stagewise pairing of the two kernel lists.  The empty lists contribute no error.  At a nonempty stage, \cref{lem:measure-sampling-distance-bind-le} increases the current discrepancy by at most $\delta$; both resulting bound measures remain probability measures because the kernels are Markov.  Apply the induction hypothesis to the tails and combine the two bounds, obtaining one copy of $\delta$ for every list element. -/)
  (title := /-- Iterated propagation through paired kernel lists -/)
  (latexEnv := "lemma")]
lemma measure_sampling_distance_foldl_bind_le {α : Type*} [MeasurableSpace α]
    [MeasurableSpace.CountableOrCountablyGenerated α α]
    (D : sampling_distance)
    (μ ν : MeasureTheory.Measure α)
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν]
    (κs ηs : List (ProbabilityTheory.Kernel α α))
    (δ : ℝ≥0∞) (hδ : δ ≠ ∞)
    (hmarkovκ : ∀ κ ∈ κs, ProbabilityTheory.IsMarkovKernel κ)
    (hmarkovη : ∀ η ∈ ηs, ProbabilityTheory.IsMarkovKernel η)
    (hpair : List.Forall₂
      (fun κ η => ∀ x, measure_sampling_distance D (κ x) (η x) ≤ δ) κs ηs) :
    measure_sampling_distance D
        (κs.foldl (fun ρ κ => ρ.bind κ) μ)
        (ηs.foldl (fun ρ η => ρ.bind η) ν) ≤
      measure_sampling_distance D μ ν + (κs.length : ℝ≥0∞) * δ := by
  induction hpair generalizing μ ν with
  | nil => simp
  | cons hhead htail ih =>
      rename_i κ η κs ηs hprobμ hprobν
      letI : ProbabilityTheory.IsMarkovKernel κ := hmarkovκ κ (by simp)
      letI : ProbabilityTheory.IsMarkovKernel η := hmarkovη η (by simp)
      have hmarkovκ_tail : ∀ ξ ∈ κs, ProbabilityTheory.IsMarkovKernel ξ := by
        intro ξ hξ
        exact hmarkovκ ξ (by simp [hξ])
      have hmarkovη_tail : ∀ ξ ∈ ηs, ProbabilityTheory.IsMarkovKernel ξ := by
        intro ξ hξ
        exact hmarkovη ξ (by simp [hξ])
      have hstep := measure_sampling_distance_bind_le D μ ν κ η δ hδ hhead
      have hrest := ih (μ := μ.bind κ) (ν := ν.bind η)
        hmarkovκ_tail hmarkovη_tail
      calc
        measure_sampling_distance D
            ((κ :: κs).foldl (fun ρ ξ => ρ.bind ξ) μ)
            ((η :: ηs).foldl (fun ρ ξ => ρ.bind ξ) ν) ≤
          measure_sampling_distance D (μ.bind κ) (ν.bind η) +
            (κs.length : ℝ≥0∞) * δ := by simpa using hrest
        _ ≤ (measure_sampling_distance D μ ν + δ) +
            (κs.length : ℝ≥0∞) * δ := add_le_add hstep le_rfl
        _ = measure_sampling_distance D μ ν +
            ((κ :: κs).length : ℝ≥0∞) * δ := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

@[blueprint "lem:backward-sampling-error-propagation"
  (statement := /-- Let $K,d\in\mathbb{N}$, let a reverse sampling path in dimension $d$ consist of one terminal problem and $K$ backward problems, and fix either total variation or Kullback--Leibler divergence $D$ and a number $\varepsilon>0$.  Let a probability-valued black-box SLC sampler have query-complexity function $N_{\mathrm{SLC}}$ and, for every $\delta>0$, return a law within $\delta$ in $D$ of every SLC target with condition number at most $4$.  If the terminal problem and every backward problem of the path are SLC with condition number at most $4$, then composing the sampler outputs obtained at local accuracy $\varepsilon/(K+1)$ gives a law whose $D$-distance from the exact reverse target is at most $\varepsilon$. -/)
  (proof := /-- Put $\delta=\varepsilon/(K+1)$, which is positive because $\varepsilon>0$.  By \cref{def:is-slc-sampler-with-query-complexity}, the sampled terminal law is within $\delta$ of the exact terminal law, and every sampled backward kernel value is within $\delta$ of the corresponding exact kernel value.  By \cref{def:slc-black-box-sampler}, all sampled kernels are Markov; the SLC hypotheses state in particular that all exact target kernels are probability-valued.  Apply \cref{lem:measure-sampling-distance-foldl-bind-le} to the reverse-ordered lists of the $K$ sampled and exact backward kernels.  Starting from the terminal discrepancy, it gives a final bound $\delta+K\delta=(K+1)\delta=\varepsilon$, which is exactly the claimed comparison of the composed sampled and exact reverse laws. -/)
  (title := /-- Accumulation of reverse sampling errors -/)
  (latexEnv := "lemma")]
lemma backward_sampling_error_propagation {K d : ℕ}
    (path : reverse_sampling_path K d) (sampler : slc_black_box_sampler d)
    (Nslc : ℝ → ℕ) (D : sampling_distance) (ε : ℝ)
    (hε : 0 < ε)
    (hSampler : is_slc_sampler_with_query_complexity D sampler Nslc)
    (hSLC : is_strongly_log_concave_with_condition_number_at_most path.terminal 4 ∧
      ∀ k : Fin K,
        is_strongly_log_concave_with_condition_number_at_most (path.backward k) 4) :
    measure_sampling_distance D (sampled_reverse_output path sampler ε)
      (exact_reverse_target path) ≤ ENNReal.ofReal ε := by
  let δr : ℝ := ε / (K + 1 : ℝ)
  let δ : ℝ≥0∞ := ENNReal.ofReal δr
  let κs : List (ProbabilityTheory.Kernel (sampling_point d) (sampling_point d)) :=
    List.ofFn fun i : Fin K => sampler.sample (path.backward (Fin.rev i)) δr
  let ηs : List (ProbabilityTheory.Kernel (sampling_point d) (sampling_point d)) :=
    List.ofFn fun i : Fin K => (path.backward (Fin.rev i)).target
  have hden : 0 < (K + 1 : ℝ) := by positivity
  have hδr : 0 < δr := div_pos hε hden
  have hδtop : δ ≠ ∞ := by
    exact ENNReal.ofReal_ne_top
  unfold is_slc_sampler_with_query_complexity at hSampler
  rcases hSampler with ⟨_, haccurate⟩
  have hterminal : measure_sampling_distance D
      (sampler.sample path.terminal δr 0) (path.terminal.target 0) ≤ δ := by
    exact haccurate path.terminal δr hδr hSLC.1 0
  letI : MeasureTheory.IsProbabilityMeasure (sampler.sample path.terminal δr 0) :=
    (sampler.sample_isMarkovKernel path.terminal δr).isProbabilityMeasure 0
  letI : MeasureTheory.IsProbabilityMeasure (path.terminal.target 0) :=
    hSLC.1.1.1 0
  have hmarkovκ : ∀ κ ∈ κs, ProbabilityTheory.IsMarkovKernel κ := by
    change ∀ κ ∈ List.ofFn (fun i : Fin K =>
      sampler.sample (path.backward (Fin.rev i)) δr), ProbabilityTheory.IsMarkovKernel κ
    rw [List.forall_mem_ofFn_iff]
    intro i
    exact sampler.sample_isMarkovKernel (path.backward (Fin.rev i)) δr
  have hmarkovη : ∀ η ∈ ηs, ProbabilityTheory.IsMarkovKernel η := by
    change ∀ η ∈ List.ofFn (fun i : Fin K =>
      (path.backward (Fin.rev i)).target), ProbabilityTheory.IsMarkovKernel η
    rw [List.forall_mem_ofFn_iff]
    intro i
    exact ⟨(hSLC.2 (Fin.rev i)).1.1⟩
  have hpair : List.Forall₂
      (fun κ η => ∀ x, measure_sampling_distance D (κ x) (η x) ≤ δ) κs ηs := by
    apply List.forall₂_iff_get.2
    constructor
    · simp [κs, ηs]
    · intro n hnκ hnη
      let i : Fin K := ⟨n, by simpa [κs] using hnκ⟩
      have hi := haccurate (path.backward (Fin.rev i)) δr hδr
        (hSLC.2 (Fin.rev i))
      unfold is_accurate_on_problem at hi
      simpa [κs, ηs, i] using hi
  have hfold := measure_sampling_distance_foldl_bind_le D
    (sampler.sample path.terminal δr 0) (path.terminal.target 0)
    κs ηs δ hδtop hmarkovκ hmarkovη hpair
  have herror : measure_sampling_distance D
      (κs.foldl (fun ρ κ => ρ.bind κ) (sampler.sample path.terminal δr 0))
      (ηs.foldl (fun ρ η => ρ.bind η) (path.terminal.target 0)) ≤
      δ + (K : ℝ≥0∞) * δ := by
    calc
      measure_sampling_distance D
          (κs.foldl (fun ρ κ => ρ.bind κ) (sampler.sample path.terminal δr 0))
          (ηs.foldl (fun ρ η => ρ.bind η) (path.terminal.target 0)) ≤
        measure_sampling_distance D (sampler.sample path.terminal δr 0)
            (path.terminal.target 0) + (κs.length : ℝ≥0∞) * δ := hfold
      _ ≤ δ + (K : ℝ≥0∞) * δ := by
        have hlen : κs.length = K := by simp [κs]
        rw [hlen]
        exact add_le_add hterminal le_rfl
  have htotal : δ + (K : ℝ≥0∞) * δ = ENNReal.ofReal ε := by
    calc
      δ + (K : ℝ≥0∞) * δ = (K + 1 : ℝ≥0∞) * δ := by ring
      _ = ENNReal.ofReal (K + 1 : ℝ) * ENNReal.ofReal δr := by
        dsimp [δ]
        congr 1
        norm_cast
      _ = ENNReal.ofReal ((K + 1 : ℝ) * δr) := by
        rw [ENNReal.ofReal_mul hden.le]
      _ = ENNReal.ofReal ε := by
        congr 1
        dsimp [δr]
        field_simp
  simpa [sampled_reverse_output, exact_reverse_target, compose_reverse_kernels,
    κs, ηs, δr, htotal] using herror.trans_eq htotal

@[blueprint "thm:slc-reduction-for-multimodal-case"
  (statement := /-- Let $K,d\in\mathbb{N}$, let $a,B:\mathbb{N}\to\mathbb{R}$, let $\mathcal P$ be a reverse sampling path of length $K$ in dimension $d$, and let $\mu$ be a measure on $\mathbb{R}^d$.  Suppose that $a$ and $B$ satisfy the adaptive stepsize condition, that $\mathcal P$ and $\mu$ form a source-faithful multimodal forward trajectory, and that $\prod_{\ell=0}^{K-1}a_\ell^2\leq(8B_K)^{-1}$.  Fix $D\in\{\mathrm{TV},\mathrm{KL}\}$ and $\varepsilon>0$, and let a probability-valued black-box SLC sampler have query-complexity function $N_{\mathrm{SLC}}:\mathbb{R}\to\mathbb{N}$ and satisfy its accuracy guarantee for $D$.  Then the terminal problem of $\mathcal P$ and every backward problem indexed by $k\in\operatorname{Fin}(K)$ are strongly log-concave with condition number at most $4$.  Moreover, the $D$-distance from $\mu$ of the composed reverse output, after applying the inverse scaling determined by the trajectory's positive early-stopping scale, is at most $\operatorname{ofReal}(\varepsilon)$, and
  \[
  \operatorname{total\_reduction\_query\_count}(K,N_{\mathrm{SLC}},\varepsilon)
  =\sum_{k\in\operatorname{range}(K+1)}
    N_{\mathrm{SLC}}\!\left(\frac{\varepsilon}{K+1}\right).
  \] -/)
  (proof := /-- Apply \cref{lem:multimodal-trajectory-hessian-control} to the adaptive-schedule, trajectory, and terminal-length hypotheses.  Applying \cref{lem:all-subproblems-condition-number} to the resulting Hessian control proves that the terminal problem and every backward problem have SLC condition number at most $4$.  With these bounds, \cref{lem:backward-sampling-error-propagation} shows that the $D$-distance between the composed sampled reverse law and the exact reverse target is at most $\operatorname{ofReal}(\varepsilon)$.

  It remains to justify data processing under the inverse scaling.  By \cref{def:slc-black-box-sampler}, every sampled kernel is Markov.  The probability-potential component of \cref{def:is-strongly-log-concave-with-condition-number-at-most} implies that the exact terminal law and every exact backward kernel are probability-valued.  Induction over the reverse-ordered kernel lists in \cref{def:sampled-reverse-output,def:exact-reverse-target,def:compose-reverse-kernels}, using at each successor step that binding a probability measure with a Markov kernel again gives a probability measure, therefore proves that both composed laws are probability measures.  The inverse-scaling map in \cref{def:unscale-early-stopped-law} is measurable, so \cref{lem:sampling-distance-map-contraction} bounds the discrepancy of the two rescaled laws by their discrepancy before scaling.  The second equality in \cref{lem:exact-reverse-target-eq-source-target} identifies the rescaled exact law with the source target; combining this equality with the contraction bound and the propagated-error bound proves the asserted accuracy of \cref{def:rescaled-reverse-output}.  Finally, \cref{def:total-reduction-query-count} unfolds to the displayed finite sum, so the query-count equality is reflexive. -/)
  (title := /-- SLC reduction for the multimodal case -/)
  (latexEnv := "theorem")]
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
        ∑ k ∈ Finset.range (K + 1), Nslc (ε / (K + 1 : ℝ)) := by
  have hControl := multimodal_trajectory_hessian_control a B path sourceTarget
    hAdaptive hTrajectory hLength
  have hSLC := all_subproblems_condition_number a B path hAdaptive hControl hLength
  refine ⟨hSLC, ?_, by rfl⟩
  have hError := backward_sampling_error_propagation path sampler Nslc D ε hε
    hSampler hSLC
  have hExact := exact_reverse_target_eq_source_target a B path sourceTarget hTrajectory
  have foldl_bind_probability
      (μ : MeasureTheory.Measure (sampling_point d))
      [MeasureTheory.IsProbabilityMeasure μ]
      (kernels : List (ProbabilityTheory.Kernel (sampling_point d) (sampling_point d)))
      (hKernels : ∀ kernel ∈ kernels, ProbabilityTheory.IsMarkovKernel kernel) :
      MeasureTheory.IsProbabilityMeasure
        (kernels.foldl (fun ρ kernel => ρ.bind kernel) μ) := by
    induction kernels generalizing μ with
    | nil => simpa
    | cons kernel kernels ih =>
        letI : ProbabilityTheory.IsMarkovKernel kernel :=
          hKernels kernel (by simp)
        letI : MeasureTheory.IsProbabilityMeasure (μ.bind kernel) := inferInstance
        simpa using
          ih (μ := μ.bind kernel) (fun η hη => hKernels η (by simp [hη]))
  have hSampledProbability : MeasureTheory.IsProbabilityMeasure
      (sampled_reverse_output path sampler ε) := by
    unfold sampled_reverse_output compose_reverse_kernels
    letI : MeasureTheory.IsProbabilityMeasure
        (sampler.sample path.terminal (ε / (K + 1 : ℝ)) 0) :=
      (sampler.sample_isMarkovKernel path.terminal
        (ε / (K + 1 : ℝ))).isProbabilityMeasure 0
    apply foldl_bind_probability
    rw [List.forall_mem_ofFn_iff]
    intro i
    exact sampler.sample_isMarkovKernel (path.backward (Fin.rev i))
      (ε / (K + 1 : ℝ))
  have hExactProbability : MeasureTheory.IsProbabilityMeasure
      (exact_reverse_target path) := by
    unfold exact_reverse_target compose_reverse_kernels
    letI : MeasureTheory.IsProbabilityMeasure (path.terminal.target 0) :=
      hSLC.1.1.1 0
    apply foldl_bind_probability
    rw [List.forall_mem_ofFn_iff]
    intro i
    exact ⟨(hSLC.2 (Fin.rev i)).1.1⟩
  letI := hSampledProbability
  letI := hExactProbability
  change measure_sampling_distance D
    (unscale_early_stopped_law hTrajectory.sigmaTarget
      (sampled_reverse_output path sampler ε)) sourceTarget ≤ ENNReal.ofReal ε
  calc
    _ = measure_sampling_distance D
        (unscale_early_stopped_law hTrajectory.sigmaTarget
          (sampled_reverse_output path sampler ε))
        (unscale_early_stopped_law hTrajectory.sigmaTarget
          (exact_reverse_target path)) :=
      congrArg (fun ν => measure_sampling_distance D
        (unscale_early_stopped_law hTrajectory.sigmaTarget
          (sampled_reverse_output path sampler ε)) ν) hExact.2.symm
    _ ≤ measure_sampling_distance D (sampled_reverse_output path sampler ε)
        (exact_reverse_target path) :=
      sampling_distance_map_contraction D _ (by fun_prop) _ _
    _ ≤ ENNReal.ofReal ε := hError

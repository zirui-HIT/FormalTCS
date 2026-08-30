import Architect
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Probability.Distributions.Poisson.Basic

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory
open scoped ENNReal NNReal Topology

@[blueprint "def:qtd-total-variation"
  (statement := /-- For probability measures $\mu$ and $\nu$ on a common measurable space, define their total variation distance by
  \[
    \operatorname{TV}(\mu,\nu)
      = \sup_{A\ \mathrm{measurable}} |\mu(A)-\nu(A)|.
  \]
  This normalization agrees with one half of the $L^1$ distance when both measures admit densities. -/)
  (title := /-- Total variation distance -/)
  (latexEnv := "definition")]
noncomputable def qtd_total_variation {α : Type*} [MeasurableSpace α]
    (μ ν : ProbabilityMeasure α) : ℝ :=
  sSup {r : ℝ | ∃ s : Set α, MeasurableSet s ∧
    r = |(μ : Measure α).real s - (ν : Measure α).real s|}

@[blueprint "def:qtd-discrete-total-variation"
  (statement := /-- For two summable real mass functions $p,q\colon\mathbb N\to\mathbb R$, define
  \[
    \operatorname{TV}_{\mathrm d}(p,q)=\frac12\sum_{x\in\mathbb N}|p(x)-q(x)|.
  \]
  The finite encoded laws used below are regarded as mass functions on $\mathbb N$ with finite support. -/)
  (title := /-- Discrete total variation distance -/)
  (latexEnv := "definition")]
noncomputable def qtd_discrete_total_variation (p q : ℕ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑' x : ℕ, |p x - q x|

@[blueprint "def:qtd-discrete-kl"
  (statement := /-- For real mass functions $p,q\colon\mathbb N\to\mathbb R$, define the discrete Kullback--Leibler expression
  \[
    D_{\mathrm{KL}}(p\Vert q)
      =\sum_{x:p(x)\ne0}p(x)\log\!\left(\frac{p(x)}{q(x)}\right).
  \]
  All later uses impose the probability and support conditions supplied by the algorithmic-law predicate. -/)
  (title := /-- Discrete Kullback--Leibler divergence -/)
  (latexEnv := "definition")]
noncomputable def qtd_discrete_kl (p q : ℕ → ℝ) : ℝ :=
  ∑' x : ℕ, if p x = 0 then 0 else p x * Real.log (p x / q x)

@[blueprint "def:qtd-probability-mass"
  (statement := /-- A function $p\colon\mathbb N\to\mathbb R$ is an encoded probability mass if it is nonnegative, summable with total mass one, and has finite support. -/)
  (title := /-- Encoded finite probability mass -/)
  (latexEnv := "definition")]
def qtd_probability_mass (p : ℕ → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ Summable p ∧ (∑' x, p x) = 1 ∧ ∃ N, ∀ x, N ≤ x → p x = 0

@[blueprint "def:qtd-admissible-error"
  (statement := /-- An error tolerance is admissible when $0<\epsilon<1$. This is the regime in which all logarithms, reciprocal error scales, and the early-stopping estimate in the source argument are intended to be used. -/)
  (title := /-- Admissible error tolerance -/)
  (latexEnv := "definition")]
def qtd_admissible_error (ε : ℝ) : Prop := 0 < ε ∧ ε < 1

@[blueprint "def:qtd-complexity-scale"
  (statement := /-- For fixed dimension $d$, the claimed accuracy-dependent complexity scale is
  \[
    \epsilon\longmapsto d\,\log^2(d/\epsilon).
  \] -/)
  (title := /-- Target complexity scale -/)
  (latexEnv := "definition")]
noncomputable def qtd_complexity_scale (d : ℕ) (ε : ℝ) : ℝ :=
  (d : ℝ) * (Real.log ((d : ℝ) / ε)) ^ 2

@[blueprint "def:quantized-transition-diffusion-family"
  (statement := /-- Fix $d\in\mathbb N$. A quantized transition diffusion family records a target law $p_*$ on $\mathbb R^d$, its potential, and, for every tolerance $\epsilon$, a finite codebook, the lower corner of each quantization cell, an encoder, and a decoder. It also records the decoded histogram and generated laws, the scalar parameters of quantization and reverse simulation, the time grid and uniformization rates, the encoded endpoint laws, the exact forward and reverse law trajectories, the learned reverse law trajectory, and the exact and learned transition-rate and score data. No analytic or probabilistic assertion is included in this data structure. -/)
  (title := /-- Data of a quantized transition diffusion family -/)
  (latexEnv := "definition")]
structure quantized_transition_diffusion_family (d : ℕ) where
  pStar : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))
  pBar : ℝ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d))
  pHat : ℝ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d))
  encode : ℝ → EuclideanSpace ℝ (Fin d) → ℕ
  decode : ℝ → (ℕ → ℝ) → ProbabilityMeasure (EuclideanSpace ℝ (Fin d))
  quantizationCodebook : ℝ → Finset ℕ
  quantizationCellLower : ℝ → ℕ → EuclideanSpace ℝ (Fin d)
  fStar : EuclideanSpace ℝ (Fin d) → ℝ
  sigma : ℝ
  hessianBound : ℝ
  secondMomentBound : ℝ
  cubeRadius : ℝ → ℝ
  cellWidth : ℝ → ℝ
  binCount : ℝ → ℝ
  horizon : ℝ → ℝ
  earlyStop : ℝ → ℝ
  scoreError : ℝ → ℝ
  scoreEntropyLoss : ℝ → ℝ
  terminalIndex : ℝ → ℕ
  timestamp : ℝ → ℕ → ℝ
  rate : ℝ → ℕ → ℝ
  qStar : ℝ → ℕ → ℝ
  qForwardAtDelta : ℝ → ℕ → ℝ
  qReverseInitial : ℝ → ℕ → ℝ
  qApproxInitial : ℝ → ℕ → ℝ
  qReverseAtStop : ℝ → ℕ → ℝ
  qApproxAtStop : ℝ → ℕ → ℝ
  qForward : ℝ → ℝ → ℕ → ℝ
  qReverse : ℝ → ℝ → ℕ → ℝ
  qApproxReverse : ℝ → ℝ → ℕ → ℝ
  forwardRate : ℝ → ℕ → ℕ → ℝ
  reverseRate : ℝ → ℝ → ℕ → ℕ → ℝ
  learnedScore : ℝ → ℝ → ℕ → ℕ → ℝ
  learnedReverseRate : ℝ → ℝ → ℕ → ℕ → ℝ

@[blueprint "def:qtd-aggregate-rate"
  (statement := /-- For a quantized transition diffusion family $F$ and a tolerance $\epsilon$, define the aggregate uniformization rate by
  \[
    \overline\beta_\epsilon
      =\sum_{w=0}^{W_\epsilon-1}
        \beta_{\epsilon,w}
        \bigl(t_{\epsilon,w+1}-t_{\epsilon,w}\bigr).
  \]
  Thus every summand is the Poisson rate prescribed on one time segment multiplied by the length of that segment. -/)
  (title := /-- Aggregate scheduled uniformization rate -/)
  (latexEnv := "definition")]
noncomputable def qtd_aggregate_rate {d : ℕ}
    (F : quantized_transition_diffusion_family d) (ε : ℝ) : ℝ :=
  ∑ w ∈ Finset.range (F.terminalIndex ε),
    F.rate ε w * (F.timestamp ε (w + 1) - F.timestamp ε w)

@[blueprint "def:qtd-expected-iterations"
  (statement := /-- For a quantized transition diffusion family $F$ and a tolerance $\epsilon$, let $\overline N_\epsilon$ have the Poisson law with parameter equal to the nonnegative part of the scheduled aggregate rate $\overline\beta_\epsilon$. Define the expected iteration and score-estimation complexity of truncated uniformization to be
  \[
    \mathbb E[\overline N_\epsilon]
      =\int_{\mathbb N} n\,
        d\operatorname{Poisson}
          \bigl((\overline\beta_\epsilon)_+\bigr)(n).
  \]
  Under the parameter schedule below, each segment rate and segment length is nonnegative, so $\overline\beta_\epsilon\ge0$ and the positive-part operation does not change the Poisson parameter. -/)
  (title := /-- Expected uniformization-event complexity -/)
  (latexEnv := "definition")]
noncomputable def qtd_expected_iterations {d : ℕ}
    (F : quantized_transition_diffusion_family d) (ε : ℝ) : ℝ :=
  ∫ n : ℕ, (n : ℝ) ∂
    ProbabilityTheory.poissonMeasure (Real.toNNReal (qtd_aggregate_rate F ε))

@[blueprint "def:qtd-quantization-cube"
  (statement := /-- For a quantized transition diffusion family $F$ and a tolerance $\epsilon$, define the truncation cube
  \[
    C_\epsilon=\{x\in\mathbb R^d: |x_i|\le L_\epsilon
      \text{ for every }i\}.
  \]
  Here $L_\epsilon$ is the recorded cube radius. -/)
  (title := /-- Quantization cube -/)
  (latexEnv := "definition")]
def qtd_quantization_cube {d : ℕ} (F : quantized_transition_diffusion_family d)
    (ε : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, |x i| ≤ F.cubeRadius ε}

@[blueprint "def:qtd-quantization-cell"
  (statement := /-- For a code $n$, let $a_{\epsilon,n}\in\mathbb R^d$ be its recorded lower corner. Its quantization cell is the intersection of the truncation cube with the half-open axis-aligned box
  \[
    \prod_{i=1}^d[a_{\epsilon,n,i},a_{\epsilon,n,i}+l_\epsilon).
  \]
  Thus every coordinate width is the scheduled cell width $l_\epsilon$. -/)
  (title := /-- Axis-aligned quantization cell -/)
  (latexEnv := "definition")]
def qtd_quantization_cell {d : ℕ} (F : quantized_transition_diffusion_family d)
    (ε : ℝ) (n : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  qtd_quantization_cube F ε ∩
    {x | ∀ i,
      F.quantizationCellLower ε n i ≤ x i ∧
      x i < F.quantizationCellLower ε n i + F.cellWidth ε}

@[blueprint "def:qtd-analytic-assumptions"
  (statement := /-- Let $\mathcal F$ be a quantized transition diffusion family in dimension $d$. The analytic assumptions are: $p_*$ has density proportional to $e^{-f_*}$; the second-moment integrand is integrable and its expectation is at most $m_0$; the potential $f_*$ is twice continuously Fréchet differentiable and the operator norm of its Hessian is at most $H$ everywhere; and, for every $t\in\mathbb R$ and $u\in\mathbb R^d$, the moment-generating-function integrand is integrable and its expectation is at most $\exp(\sigma^2t^2\lVert u\rVert^2/2)$.

  We also record the two analytic estimates needed by the quantization argument. First, the score is square-integrable and the whole-space integration-by-parts estimate gives
  \[
    \int \lVert\nabla f_*(x)\rVert^2\,dp_*(x)\le dH.
  \]
  Second, for every admissible $\epsilon$, the cellwise $L^1$ Poincaré estimate, summed over the quantization cells, gives
  \[
    \operatorname{TV}(p_*,\overline p_{*,\epsilon})
      \le p_*(C_\epsilon^{\mathsf c})+2\epsilon.
  \]
  These two displayed bounds are explicit interface hypotheses because the fixed import surface contains neither the required whole-space integration-by-parts theorem nor the required multivariate cubical $L^1$ Poincaré theorem. -/)
  (title := /-- Analytic assumptions and quantization estimates -/)
  (latexEnv := "definition")]
noncomputable def qtd_analytic_assumptions {d : ℕ}
    (F : quantized_transition_diffusion_family d) : Prop :=
  (∃ Z : ℝ, 0 < Z ∧
    (F.pStar : Measure (EuclideanSpace ℝ (Fin d))) =
      volume.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-F.fStar x) / Z))) ∧
  MeasureTheory.Integrable (fun x ↦ ‖x‖ ^ 2)
    (F.pStar : Measure (EuclideanSpace ℝ (Fin d))) ∧
  (∫ x, ‖x‖ ^ 2 ∂(F.pStar : Measure (EuclideanSpace ℝ (Fin d)))) ≤
    F.secondMomentBound ∧
  ContDiff ℝ 2 F.fStar ∧
  (∀ x, ‖fderiv ℝ (gradient F.fStar) x‖ ≤ F.hessianBound) ∧
  (∀ (t : ℝ) (u : EuclideanSpace ℝ (Fin d)),
    MeasureTheory.Integrable (fun x ↦ Real.exp (t * inner ℝ x u))
      (F.pStar : Measure (EuclideanSpace ℝ (Fin d))) ∧
    (∫ x, Real.exp (t * inner ℝ x u)
        ∂(F.pStar : Measure (EuclideanSpace ℝ (Fin d)))) ≤
      Real.exp (F.sigma ^ 2 * t ^ 2 * ‖u‖ ^ 2 / 2)) ∧
  MeasureTheory.Integrable (fun x ↦ ‖gradient F.fStar x‖ ^ 2)
    (F.pStar : Measure (EuclideanSpace ℝ (Fin d))) ∧
  (∫ x, ‖gradient F.fStar x‖ ^ 2
      ∂(F.pStar : Measure (EuclideanSpace ℝ (Fin d)))) ≤
    (d : ℝ) * F.hessianBound ∧
  (∀ ε, qtd_admissible_error ε →
    qtd_total_variation F.pStar (F.pBar ε) ≤
      ((F.pStar : Measure (EuclideanSpace ℝ (Fin d)))
        ((qtd_quantization_cube F ε)ᶜ)).toReal + 2 * ε)

@[blueprint "def:qtd-training-assumption"
  (statement := /-- Assumption A4 requires the score error $\epsilon_{\mathrm{score}}$ to be nonnegative and the score-entropy loss at every admissible tolerance $\epsilon$ to be at most $\epsilon_{\mathrm{score}}^2$. -/)
  (title := /-- Score-estimation assumption A4 -/)
  (latexEnv := "definition")]
def qtd_training_assumption {d : ℕ}
    (F : quantized_transition_diffusion_family d) : Prop :=
  ∀ ε, qtd_admissible_error ε →
    0 ≤ F.scoreError ε ∧
    F.scoreEntropyLoss ε ≤ (F.scoreError ε) ^ 2

@[blueprint "def:qtd-parameter-schedule"
  (statement := /-- The parameter schedule is the collection of identities and inequalities stipulated in the main theorem: the formulas for the real parameters $L$, $l$, $K$, $T$, $\delta$, and $\epsilon_{\mathrm{score}}$; the recurrence and terminal condition for the time grid; and the prescribed segment rates $\beta_{t_w}$. In particular, no integrality condition is imposed on the real quantity $d\log_2K$. -/)
  (title := /-- Quantization and reverse-process parameter schedule -/)
  (latexEnv := "definition")]
noncomputable def qtd_parameter_schedule {d : ℕ}
    (F : quantized_transition_diffusion_family d) : Prop :=
  ∀ ε, qtd_admissible_error ε →
    0 < F.sigma ∧ 0 < F.hessianBound ∧ 0 < F.secondMomentBound ∧
    F.cubeRadius ε = F.sigma * Real.sqrt (2 * Real.log (2 * (d : ℝ) / ε)) ∧
    F.cellWidth ε = ε /
      (2 * F.hessianBound *
        (F.sigma * Real.sqrt (2 * (d : ℝ) * Real.log (2 * (d : ℝ) / ε)) +
          (d : ℝ) + Real.sqrt ((d : ℝ) * F.secondMomentBound))) ∧
    F.binCount ε = 2 * F.cubeRadius ε / F.cellWidth ε ∧
    F.scoreError ε ≤ ε /
      (Real.log ((d : ℝ) / ε) + Real.log (Real.logb 2 (F.binCount ε))) ∧
    F.horizon ε =
      Real.log ((d : ℝ) / ε) + Real.log (Real.logb 2 (F.binCount ε)) ∧
    0 < F.earlyStop ε ∧
    F.earlyStop ε ≤ ε / ((d : ℝ) * Real.logb 2 (F.binCount ε)) ∧
    F.timestamp ε 0 = 0 ∧
    (∀ w < F.terminalIndex ε,
      F.timestamp ε (w + 1) - F.timestamp ε w =
        (1 / 2 : ℝ) * (F.horizon ε - F.timestamp ε (w + 1))) ∧
    F.timestamp ε (F.terminalIndex ε) = F.horizon ε - F.earlyStop ε ∧
    (∀ w ≤ F.terminalIndex ε,
      F.rate ε w =
        2 * (d : ℝ) * Real.logb 2 (F.binCount ε) /
          min 1 (F.horizon ε - F.timestamp ε w))

@[blueprint "def:qtd-validated-parameter-schedule"
  (statement := /-- Let $d\in\mathbb N$, and let $F$ be a quantized transition diffusion family in dimension $d$. A validated parameter schedule consists of the identities and inequalities in \cref{def:qtd-parameter-schedule}, together with the following three conditions for every $\epsilon\in(0,1)$. Writing
  \[
    B_\epsilon=d\log_2K_\epsilon,
  \]
  one has $B_\epsilon\ge1$, the trained score satisfies
  \[
    \epsilon_{\mathrm{score},\epsilon}
      \le \frac{\epsilon}{\max\{1,T_\epsilon\}},
  \]
  and the terminal grid index is the first index for which the prescribed upper bound on the early-stopping offset holds, in the quantitative form
  \[
    \frac{2\epsilon}{3B_\epsilon}<\delta_\epsilon
      \le\frac{\epsilon}{B_\epsilon}.
  \]
  The lower bound is the consequence of the recurrence
  $T_\epsilon-t_{w+1}=\frac23(T_\epsilon-t_w)$ at the preceding grid point. -/)
  (title := /-- Validated parameter schedule -/)
  (latexEnv := "definition")]
noncomputable def qtd_validated_parameter_schedule {d : ℕ}
    (F : quantized_transition_diffusion_family d) : Prop :=
  qtd_parameter_schedule F ∧
  ∀ ε, qtd_admissible_error ε →
    1 ≤ (d : ℝ) * Real.logb 2 (F.binCount ε) ∧
    F.scoreError ε ≤ ε / max 1 (F.horizon ε) ∧
    (2 / 3 : ℝ) *
        (ε / ((d : ℝ) * Real.logb 2 (F.binCount ε))) <
      F.earlyStop ε

@[blueprint "def:qtd-hamming-neighbor"
  (statement := /-- For an admissible tolerance $\epsilon$, two encoded states $x,y\in\mathcal I_\epsilon$ are Hamming neighbors if their binary encodings differ in exactly one coordinate. Equivalently, there is an index
  \[
    i<d\left\lfloor\log_2K_\epsilon\right\rfloor
  \]
  such that $y$ is obtained from $x$ by toggling bit $i$. -/)
  (title := /-- Hamming adjacency of encoded states -/)
  (latexEnv := "definition")]
def qtd_hamming_neighbor {d : ℕ} (F : quantized_transition_diffusion_family d)
    (ε : ℝ) (x y : ℕ) : Prop :=
  x ∈ F.quantizationCodebook ε ∧
  y ∈ F.quantizationCodebook ε ∧
  ∃ i < d * ⌊Real.logb 2 (F.binCount ε)⌋₊,
    y = Nat.xor x (2 ^ i)

@[blueprint "def:qtd-algorithmic-laws"
  (statement := /-- For every admissible tolerance $\epsilon$, let $C_\epsilon$ be the scheduled truncation cube and let $\mathcal I_\epsilon$ be the finite codebook. The algorithmic laws require the following.

  First, all encoded laws are probability masses supported on $\mathcal I_\epsilon$. The measurable encoder identifies each code fiber inside $C_\epsilon$ with its axis-aligned cell from \cref{def:qtd-quantization-cell}; these cells are measurable, have positive finite Lebesgue measure, are pairwise disjoint, and cover $C_\epsilon$. The exact encoded mass is the cell mass of the conditional target law:
  \[
    q_{*,\epsilon}(n)
      =\frac{p_*(C_{\epsilon,n})}{p_*(C_\epsilon)}
      \quad(n\in\mathcal I_\epsilon),
  \]
  and it vanishes off the codebook.

  Second, if $p$ is any encoded probability mass supported on $\mathcal I_\epsilon$, then its decoding is the piecewise-uniform histogram
  \[
    \operatorname{decode}_\epsilon(p)(A)
      =\sum_{n\in\mathcal I_\epsilon}p(n)
        \frac{\operatorname{vol}(A\cap C_{\epsilon,n})}
             {\operatorname{vol}(C_{\epsilon,n})}
  \]
  for every measurable set $A$. In particular, decoding $q_{*,\epsilon}$ gives $\overline p_{*,\epsilon}$, while decoding the terminal approximate mass gives $\widehat p_\epsilon$. Decoding preserves total variation between encoded probability masses.

  Finally, time reversal identifies the exact reverse law at time $T-\delta$ with the forward law at time $\delta$. The real number $\log_2K_\epsilon$ is the natural number of binary coordinates, the codebook is exactly the set of natural numbers below $2^{d\log_2K_\epsilon}$, the off-diagonal forward generator has rate one precisely between Hamming neighbors from \cref{def:qtd-hamming-neighbor} and rate zero otherwise, and the standard no-jump coupling gives the valid early-time estimate
  \[
    \operatorname{TV}_{\mathrm d}(q_{*,\epsilon},q^\to_{\delta,\epsilon})
      \le 1-\exp(-\delta_\epsilon d\log_2K_\epsilon).
  \] -/)
  (title := /-- Probability and time-reversal laws of the algorithms -/)
  (latexEnv := "definition")]
def qtd_algorithmic_laws {d : ℕ}
    (F : quantized_transition_diffusion_family d) : Prop :=
  (∀ ε, qtd_admissible_error ε →
    qtd_probability_mass (F.qStar ε) ∧
    qtd_probability_mass (F.qForwardAtDelta ε) ∧
    qtd_probability_mass (F.qReverseInitial ε) ∧
    qtd_probability_mass (F.qApproxInitial ε) ∧
    qtd_probability_mass (F.qReverseAtStop ε) ∧
    qtd_probability_mass (F.qApproxAtStop ε)) ∧
  (∀ ε, qtd_admissible_error ε →
    ∀ x, x ∉ F.quantizationCodebook ε →
      F.qStar ε x = 0 ∧
      F.qForwardAtDelta ε x = 0 ∧
      F.qReverseInitial ε x = 0 ∧
      F.qApproxInitial ε x = 0 ∧
      F.qReverseAtStop ε x = 0 ∧
      F.qApproxAtStop ε x = 0) ∧
  (∀ ε, qtd_admissible_error ε →
    Measurable (F.encode ε) ∧
    0 < (F.pStar : Measure (EuclideanSpace ℝ (Fin d)))
      (qtd_quantization_cube F ε) ∧
    (∀ x ∈ F.quantizationCodebook ε,
      MeasurableSet (qtd_quantization_cell F ε x) ∧
      0 < volume (qtd_quantization_cell F ε x) ∧
      volume (qtd_quantization_cell F ε x) < ∞) ∧
    qtd_quantization_cube F ε =
      ⋃ x ∈ F.quantizationCodebook ε, qtd_quantization_cell F ε x ∧
    (∀ x ∈ F.quantizationCodebook ε,
      ∀ y ∈ F.quantizationCodebook ε, x ≠ y →
        Disjoint (qtd_quantization_cell F ε x)
          (qtd_quantization_cell F ε y)) ∧
    (∀ x ∈ F.quantizationCodebook ε,
      qtd_quantization_cube F ε ∩ (F.encode ε) ⁻¹' ({x} : Set ℕ) =
        qtd_quantization_cell F ε x) ∧
    (∀ x, ENNReal.ofReal (F.qStar ε x) =
      if x ∈ F.quantizationCodebook ε then
        (F.pStar : Measure (EuclideanSpace ℝ (Fin d)))
            (qtd_quantization_cell F ε x) /
          (F.pStar : Measure (EuclideanSpace ℝ (Fin d)))
            (qtd_quantization_cube F ε)
      else 0) ∧
    F.pBar ε = F.decode ε (F.qStar ε) ∧
    F.pHat ε = F.decode ε (F.qApproxAtStop ε)) ∧
  (∀ ε p, qtd_admissible_error ε →
    qtd_probability_mass p →
    (∀ x, x ∉ F.quantizationCodebook ε → p x = 0) →
    ∀ s, MeasurableSet s →
      (F.decode ε p : Measure (EuclideanSpace ℝ (Fin d))) s =
        ∑ x ∈ F.quantizationCodebook ε,
          ENNReal.ofReal (p x) *
            (volume (s ∩ qtd_quantization_cell F ε x) /
              volume (qtd_quantization_cell F ε x))) ∧
  (∀ ε p q, qtd_admissible_error ε →
    qtd_probability_mass p → qtd_probability_mass q →
    qtd_total_variation (F.decode ε p) (F.decode ε q) =
      qtd_discrete_total_variation p q) ∧
  ((∀ ε x, qtd_admissible_error ε →
      F.qReverseAtStop ε x = F.qForwardAtDelta ε x) ∧
    (∀ ε, qtd_admissible_error ε →
      Real.logb 2 (F.binCount ε) =
        (⌊Real.logb 2 (F.binCount ε)⌋₊ : ℝ) ∧
      (∀ x, x ∈ F.quantizationCodebook ε ↔
        x < 2 ^ (d * ⌊Real.logb 2 (F.binCount ε)⌋₊)) ∧
      (∀ x y, x ≠ y →
        (qtd_hamming_neighbor F ε x y → F.forwardRate ε x y = 1) ∧
        (¬qtd_hamming_neighbor F ε x y → F.forwardRate ε x y = 0)) ∧
      qtd_discrete_total_variation (F.qStar ε) (F.qForwardAtDelta ε) ≤
        1 - Real.exp
          (-F.earlyStop ε * (d : ℝ) * Real.logb 2 (F.binCount ε))))

@[blueprint "def:qtd-reverse-process-laws"
  (statement := /-- For every admissible tolerance $\epsilon$, let $T$ and $\delta$ be the scheduled horizon and early-stopping offset. The exact forward laws $q_t^{\to}$ on $[0,T]$ and the exact and learned reverse laws $q_t^{\leftarrow}$ and $\widehat q_t$ on $[0,T-\delta]$ are finite probability masses. Their recorded initial and terminal masses are their actual endpoints, and $q_t^{\leftarrow}=q_{T-t}^{\to}$. The three paths satisfy the Kolmogorov forward equations for conservative rate matrices. Off the diagonal, the exact reverse rate is
  \[
    R_t^{\leftarrow}(x,y)
      =R^{\to}(y,x)\frac{q_t^{\leftarrow}(x)}
                            {q_t^{\leftarrow}(y)},
  \]
  whereas the learned rate replaces this exact likelihood ratio by the trained score. On each time segment its exit rate is bounded by the prescribed uniformization rate, so truncated uniformization has $\widehat q_t$ as its marginal law. The instantaneous reverse KL derivative is bounded by the score-entropy loss, which in turn dominates the corresponding rate-level Bregman divergence. Finally, the forward KL derivative satisfies the source's entropy-dissipation inequality and its initial value has the standard finite-state entropy bound. -/)
  (title := /-- Exact and learned reverse-process semantics -/)
  (latexEnv := "definition")]
noncomputable def qtd_reverse_process_laws {d : ℕ}
    (F : quantized_transition_diffusion_family d) : Prop :=
  ∀ ε, qtd_admissible_error ε →
    (∀ t, 0 ≤ t → t ≤ F.horizon ε →
      qtd_probability_mass (F.qForward ε t)) ∧
    (∀ t, 0 ≤ t → t ≤ F.horizon ε - F.earlyStop ε →
      qtd_probability_mass (F.qReverse ε t) ∧
      qtd_probability_mass (F.qApproxReverse ε t)) ∧
    (∀ x, F.qForward ε 0 x = F.qStar ε x) ∧
    (∀ x, F.qForward ε (F.earlyStop ε) x = F.qForwardAtDelta ε x) ∧
    (∀ t x, 0 ≤ t → t ≤ F.horizon ε - F.earlyStop ε →
      F.qReverse ε t x = F.qForward ε (F.horizon ε - t) x) ∧
    (∀ x, F.qReverse ε 0 x = F.qReverseInitial ε x) ∧
    (∀ x,
      F.qReverse ε (F.horizon ε - F.earlyStop ε) x =
        F.qReverseAtStop ε x) ∧
    (∀ x, F.qApproxReverse ε 0 x = F.qApproxInitial ε x) ∧
    (∀ x,
      F.qApproxReverse ε (F.horizon ε - F.earlyStop ε) x =
        F.qApproxAtStop ε x) ∧
    (∀ x y, x ≠ y → 0 ≤ F.forwardRate ε x y) ∧
    (∀ y,
      F.forwardRate ε y y =
        -∑' x, if x = y then 0 else F.forwardRate ε x y) ∧
    (∀ t x y, 0 ≤ t → t ≤ F.horizon ε - F.earlyStop ε → x ≠ y →
      F.reverseRate ε t x y =
        F.forwardRate ε y x * F.qReverse ε t x / F.qReverse ε t y) ∧
    (∀ t x y, 0 ≤ t → t ≤ F.horizon ε - F.earlyStop ε → x ≠ y →
      F.learnedReverseRate ε t x y =
        F.forwardRate ε y x * F.learnedScore ε t x y) ∧
    (∀ t x y, 0 ≤ t → t ≤ F.horizon ε - F.earlyStop ε → x ≠ y →
      0 ≤ F.reverseRate ε t x y ∧
      0 ≤ F.learnedReverseRate ε t x y ∧
      (0 < F.reverseRate ε t x y → 0 < F.learnedReverseRate ε t x y)) ∧
    (∀ t y, 0 ≤ t → t ≤ F.horizon ε - F.earlyStop ε →
      F.reverseRate ε t y y =
        -∑' x, if x = y then 0 else F.reverseRate ε t x y) ∧
    (∀ t y, 0 ≤ t → t ≤ F.horizon ε - F.earlyStop ε →
      F.learnedReverseRate ε t y y =
        -∑' x, if x = y then 0 else F.learnedReverseRate ε t x y) ∧
    (∀ t y, 0 ≤ t → t ≤ F.horizon ε →
      HasDerivAt (fun s ↦ F.qForward ε s y)
        (∑' x, F.forwardRate ε y x * F.qForward ε t x) t) ∧
    (∀ t y, 0 ≤ t → t ≤ F.horizon ε - F.earlyStop ε →
      HasDerivAt (fun s ↦ F.qReverse ε s y)
        (∑' x, F.reverseRate ε t y x * F.qReverse ε t x) t) ∧
    (∀ t y, 0 ≤ t → t ≤ F.horizon ε - F.earlyStop ε →
      HasDerivAt (fun s ↦ F.qApproxReverse ε s y)
        (∑' x, F.learnedReverseRate ε t y x *
          F.qApproxReverse ε t x) t) ∧
    (∀ w < F.terminalIndex ε, ∀ t y,
      F.timestamp ε w ≤ t → t ≤ F.timestamp ε (w + 1) →
      (∑' x, if x = y then 0 else F.learnedReverseRate ε t x y) ≤
        F.rate ε w) ∧
    (∀ t, 0 ≤ t → t ≤ F.horizon ε - F.earlyStop ε →
      (∑' y, F.qReverse ε t y *
        ∑' x, if x = y then 0 else
          if F.reverseRate ε t x y = 0 then
            F.learnedReverseRate ε t x y
          else
            F.reverseRate ε t x y *
                Real.log (F.reverseRate ε t x y /
                  F.learnedReverseRate ε t x y) +
              F.learnedReverseRate ε t x y -
                F.reverseRate ε t x y) ≤ F.scoreEntropyLoss ε) ∧
    (∀ t, 0 ≤ t → t ≤ F.horizon ε - F.earlyStop ε →
      ∃ r,
        HasDerivAt
          (fun s ↦ qtd_discrete_kl (F.qReverse ε s)
            (F.qApproxReverse ε s)) r t ∧
        r ≤ F.scoreEntropyLoss ε) ∧
    (∀ t, 0 ≤ t → t ≤ F.horizon ε →
      ∃ r,
        HasDerivAt
          (fun s ↦ qtd_discrete_kl (F.qForward ε s)
            (F.qApproxInitial ε)) r t ∧
        r ≤ -qtd_discrete_kl (F.qForward ε t) (F.qApproxInitial ε)) ∧
    qtd_discrete_kl (F.qForward ε 0) (F.qApproxInitial ε) ≤
      (d : ℝ) * Real.logb 2 (F.binCount ε)

@[blueprint "def:qtd-validated-reverse-process-laws"
  (statement := /-- Let $d\in\mathbb N$, and let $F$ satisfy the exact and learned reverse-process semantics in \cref{def:qtd-reverse-process-laws}. The semantics are validated when the unit-rate Hamming-neighbor forward chain also records its sharp entropy dissipation: for every $\epsilon\in(0,1)$ and every $t\in[0,T_\epsilon]$, the function
  \[
    G_\epsilon(s)
      =D_{\mathrm{KL}}(q^{\to}_{s,\epsilon}\Vert
        \widehat q_{0,\epsilon})
  \]
  is differentiable at $t$ and
  \[
    G_\epsilon'(t)\le-2G_\epsilon(t).
  \]
  This is the tensorized two-state modified log-Sobolev inequality for the hypercube generator whose off-diagonal bit-flip rates are one. -/)
  (title := /-- Validated reverse-process semantics -/)
  (latexEnv := "definition")]
noncomputable def qtd_validated_reverse_process_laws {d : ℕ}
    (F : quantized_transition_diffusion_family d) : Prop :=
  qtd_reverse_process_laws F ∧
  ∀ ε, qtd_admissible_error ε →
    ∀ t, 0 ≤ t → t ≤ F.horizon ε →
      ∃ r,
        HasDerivAt
          (fun s ↦ qtd_discrete_kl (F.qForward ε s)
            (F.qApproxInitial ε)) r t ∧
        r ≤ -2 *
          qtd_discrete_kl (F.qForward ε t) (F.qApproxInitial ε)

@[blueprint "lem:qtd-subgaussian-one-sided-tail"
  (statement := /-- Let $d\in\mathbb N$, let $F$ be a quantized transition diffusion family in dimension $d$ satisfying the analytic assumptions of \cref{def:qtd-analytic-assumptions}, and suppose that $\sigma>0$. If $u\in\mathbb R^d$ is a unit vector and $a>0$, then
  \[
    p_*\{x:a\le\langle x,u\rangle\}
      \le \exp\!\left(-\frac{a^2}{2\sigma^2}\right).
  \] -/)
  (proof := /-- Set $t=a/\sigma^2>0$ and apply Markov's inequality to the nonnegative integrable function $x\mapsto\exp(t\langle x,u\rangle)$. The moment-generating-function clause of \cref{def:qtd-analytic-assumptions} and the identity $\lVert u\rVert=1$ give
  \[
    e^{ta}p_*\{x:a\le\langle x,u\rangle\}
      \le \exp(\sigma^2t^2/2)
      =e^{ta}\exp\!\left(-\frac{a^2}{2\sigma^2}\right).
  \]
  Cancelling the strictly positive factor $e^{ta}$ proves the claim. -/)
  (title := /-- One-sided sub-Gaussian tail bound -/)
  (latexEnv := "lemma")]
lemma qtd_subgaussian_one_sided_tail {d : ℕ}
    (F : quantized_transition_diffusion_family d)
    (ha : qtd_analytic_assumptions F) (hσ : 0 < F.sigma)
    (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1)
    (a : ℝ) (ha_pos : 0 < a) :
    (F.pStar : Measure (EuclideanSpace ℝ (Fin d))).real
        {x | a ≤ inner ℝ x u} ≤
      Real.exp (-a ^ 2 / (2 * F.sigma ^ 2)) := by
  rcases ha with
    ⟨hden, hmom, hmom_le, hsmooth, hhess, hmgf, hscore_int, hscore_le, hquant⟩
  let t := a / F.sigma ^ 2
  have ht : 0 < t := div_pos ha_pos (sq_pos_of_pos hσ)
  have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
    (μ := (F.pStar : Measure (EuclideanSpace ℝ (Fin d))))
    (f := fun x => Real.exp (t * inner ℝ x u))
    (Filter.Eventually.of_forall (fun x => Real.exp_nonneg _))
    (hmgf t u).1 (Real.exp (t * a))
  have hset :
      {x | Real.exp (t * a) ≤ Real.exp (t * inner ℝ x u)} =
        {x | a ≤ inner ℝ x u} := by
    ext x
    simp only [Set.mem_setOf_eq, Real.exp_le_exp]
    constructor <;> intro hx <;> nlinarith
  rw [hset] at hmarkov
  have hbound := hmarkov.trans (hmgf t u).2
  rw [hu, one_pow, mul_one] at hbound
  have hexp : Real.exp (F.sigma ^ 2 * t ^ 2 / 2) =
      Real.exp (t * a) * Real.exp (-a ^ 2 / (2 * F.sigma ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [t]
    field_simp [ne_of_gt hσ]
    ring
  rw [hexp] at hbound
  nlinarith [Real.exp_pos (t * a)]

@[blueprint "lem:qtd-subgaussian-cube-tail"
  (statement := /-- Let $d\in\mathbb N$, and let $F$ be a quantized transition diffusion family satisfying the analytic assumptions of \cref{def:qtd-analytic-assumptions} and the parameter schedule of \cref{def:qtd-parameter-schedule}. For every $\epsilon\in\mathbb R$ with $0<\epsilon<1$, the target mass outside the quantization cube of \cref{def:qtd-quantization-cube} satisfies
  \[
    p_*(C_\epsilon^{\mathsf c})\le\epsilon.
  \] -/)
  (proof := /-- Fix $\epsilon\in(0,1)$. The early-stopping inequalities in \cref{def:qtd-parameter-schedule} first imply $d>0$, since for $d=0$ they would bound a positive number by zero. Consequently $2d/\epsilon>1$ and the scheduled radius $L_\epsilon$ is positive. Apply \cref{lem:qtd-subgaussian-one-sided-tail} with the two unit vectors $e_i$ and $-e_i$, and take their union, to obtain
  \[
    p_*\{x:L_\epsilon<|x_i|\}
      \le 2\exp\!\left(-\frac{L_\epsilon^2}{2\sigma^2}\right)
  \]
  for every coordinate $i$. By \cref{def:qtd-quantization-cube}, the complement of $C_\epsilon$ is the union of these coordinate-tail events. The finite union bound and the scheduled identity
  $L_\epsilon=\sigma\sqrt{2\log(2d/\epsilon)}$ yield
  \[
    p_*(C_\epsilon^{\mathsf c})
      \le 2d\exp\!\left(-\frac{L_\epsilon^2}{2\sigma^2}\right)
      =2d\exp(-\log(2d/\epsilon))
      =\epsilon.
  \] -/)
  (title := /-- Sub-Gaussian mass outside the quantization cube -/)
  (latexEnv := "lemma")]
lemma qtd_subgaussian_cube_tail {d : ℕ}
    (F : quantized_transition_diffusion_family d)
    (ha : qtd_analytic_assumptions F) (hp : qtd_parameter_schedule F) :
    ∀ ε, qtd_admissible_error ε →
      ((F.pStar : Measure (EuclideanSpace ℝ (Fin d)))
        ((qtd_quantization_cube F ε)ᶜ)).toReal ≤ ε := by
  intro ε hε
  rcases hp ε hε with
    ⟨hσ, hH, hm0, hL, hlwidth, hK, hscore, hT, hδ, hδle, ht0, hgrid, htW, hrate⟩
  have hdNat : 0 < d := Nat.pos_of_ne_zero (by
    intro hd
    subst d
    norm_num at hδle
    linarith)
  have hd : 0 < (d : ℝ) := by exact_mod_cast hdNat
  have hdone : (1 : ℝ) ≤ d := by exact_mod_cast hdNat
  have harg : 1 < 2 * (d : ℝ) / ε :=
    (lt_div_iff₀ hε.1).2 (by nlinarith [hε.2, hdone])
  have hlog : 0 < Real.log (2 * (d : ℝ) / ε) := Real.log_pos harg
  have hLpos : 0 < F.cubeRadius ε := by
    rw [hL]
    positivity
  have hcoord (i : Fin d) :
      (F.pStar : Measure (EuclideanSpace ℝ (Fin d))).real
          {x | F.cubeRadius ε < |x i|} ≤
        2 * Real.exp (-(F.cubeRadius ε) ^ 2 / (2 * F.sigma ^ 2)) := by
    let ep : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i 1
    let en : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i (-1)
    have hep : ‖ep‖ = 1 := by simp [ep, PiLp.norm_single]
    have hen : ‖en‖ = 1 := by simp [en, PiLp.norm_single]
    have hp' :=
      qtd_subgaussian_one_sided_tail F ha hσ ep hep (F.cubeRadius ε) hLpos
    have hn' :=
      qtd_subgaussian_one_sided_tail F ha hσ en hen (F.cubeRadius ε) hLpos
    have hsubset : {x | F.cubeRadius ε < |x i|} ⊆
        {x | F.cubeRadius ε ≤ inner ℝ x ep} ∪
          {x | F.cubeRadius ε ≤ inner ℝ x en} := by
      intro x hx
      change F.cubeRadius ε < |x i| at hx
      simp only [Set.mem_union, Set.mem_setOf_eq]
      have hepi : inner ℝ x ep = x i := by
        simp [ep, EuclideanSpace.inner_single_right]
      have heni : inner ℝ x en = -(x i) := by
        simp [en, EuclideanSpace.inner_single_right]
      rw [hepi, heni]
      by_cases hxi : 0 ≤ x i
      · left
        exact le_of_lt (by simpa [abs_of_nonneg hxi] using hx)
      · right
        exact le_of_lt (by simpa [abs_of_neg (lt_of_not_ge hxi)] using hx)
    calc
      (F.pStar : Measure (EuclideanSpace ℝ (Fin d))).real
          {x | F.cubeRadius ε < |x i|}
          ≤ (F.pStar : Measure (EuclideanSpace ℝ (Fin d))).real
              ({x | F.cubeRadius ε ≤ inner ℝ x ep} ∪
                {x | F.cubeRadius ε ≤ inner ℝ x en}) :=
            MeasureTheory.measureReal_mono hsubset
      _ ≤ (F.pStar : Measure (EuclideanSpace ℝ (Fin d))).real
              {x | F.cubeRadius ε ≤ inner ℝ x ep} +
            (F.pStar : Measure (EuclideanSpace ℝ (Fin d))).real
              {x | F.cubeRadius ε ≤ inner ℝ x en} :=
            MeasureTheory.measureReal_union_le _ _
      _ ≤ Real.exp (-(F.cubeRadius ε) ^ 2 / (2 * F.sigma ^ 2)) +
            Real.exp (-(F.cubeRadius ε) ^ 2 / (2 * F.sigma ^ 2)) :=
            add_le_add hp' hn'
      _ = 2 * Real.exp (-(F.cubeRadius ε) ^ 2 /
            (2 * F.sigma ^ 2)) := by ring
  have hcube : (qtd_quantization_cube F ε)ᶜ =
      ⋃ i : Fin d, {x | F.cubeRadius ε < |x i|} := by
    ext x
    simp [qtd_quantization_cube]
  have htail_raw :
      ((F.pStar : Measure (EuclideanSpace ℝ (Fin d)))
          ((qtd_quantization_cube F ε)ᶜ)).toReal ≤
        (d : ℝ) * (2 * Real.exp (-(F.cubeRadius ε) ^ 2 /
          (2 * F.sigma ^ 2))) := by
    rw [hcube]
    calc
      (F.pStar : Measure (EuclideanSpace ℝ (Fin d))).real
          (⋃ i : Fin d, {x | F.cubeRadius ε < |x i|})
          ≤ ∑ i : Fin d,
              (F.pStar : Measure (EuclideanSpace ℝ (Fin d))).real
                {x | F.cubeRadius ε < |x i|} :=
            MeasureTheory.measureReal_iUnion_fintype_le _
      _ ≤ ∑ _i : Fin d, 2 * Real.exp (-(F.cubeRadius ε) ^ 2 /
            (2 * F.sigma ^ 2)) := Finset.sum_le_sum (fun i _hi => hcoord i)
      _ = (d : ℝ) * (2 * Real.exp (-(F.cubeRadius ε) ^ 2 /
            (2 * F.sigma ^ 2))) := by simp
  have hsqrt :
      (Real.sqrt (2 * Real.log (2 * (d : ℝ) / ε))) ^ 2 =
        2 * Real.log (2 * (d : ℝ) / ε) :=
    Real.sq_sqrt (le_of_lt (by positivity))
  have hexponent :
      -(F.cubeRadius ε) ^ 2 / (2 * F.sigma ^ 2) =
        -Real.log (2 * (d : ℝ) / ε) := by
    rw [hL, mul_pow, hsqrt]
    field_simp [ne_of_gt hσ]
  have htail_value :
      (d : ℝ) * (2 * Real.exp (-(F.cubeRadius ε) ^ 2 /
        (2 * F.sigma ^ 2))) = ε := by
    rw [hexponent, Real.exp_neg, Real.exp_log (lt_trans (by norm_num) harg)]
    field_simp [ne_of_gt hd, ne_of_gt hε.1]
  exact htail_raw.trans_eq htail_value

@[blueprint "lem:qtd-quantization-gap"
  (statement := /-- Let $d\in\mathbb N$, and let $F$ be a quantized transition diffusion family in dimension $d$ satisfying the analytic assumptions of \cref{def:qtd-analytic-assumptions}, the prescribed parameter schedule of \cref{def:qtd-parameter-schedule}, and the algorithmic laws of \cref{def:qtd-algorithmic-laws}. Then, for every $\epsilon\in\mathbb R$ with $0<\epsilon<1$, the target law $p_*$ and the decoded histogram law $\overline p_{*,\epsilon}$ satisfy
  \[
    \operatorname{TV}(p_*,\overline p_{*,\epsilon})\le 3\epsilon.
  \]
  -/)
  (proof := /-- Fix an admissible $\epsilon$. By \cref{lem:qtd-subgaussian-cube-tail}, the target mass outside the scheduled quantization cube satisfies
  \[
    p_*(C_\epsilon^{\mathsf c})\le\epsilon.
  \]
  The explicit cellwise quantization estimate in \cref{def:qtd-analytic-assumptions} gives
  \[
    \operatorname{TV}(p_*,\overline p_{*,\epsilon})
      \le p_*(C_\epsilon^{\mathsf c})+2\epsilon.
  \]
  Combining these inequalities yields
  \[
    \operatorname{TV}(p_*,\overline p_{*,\epsilon})
      \le\epsilon+2\epsilon=3\epsilon.
  \] -/)
  (title := /-- Quantization error of the target law -/)
  (latexEnv := "lemma")]
lemma qtd_quantization_gap {d : ℕ} (F : quantized_transition_diffusion_family d)
    (ha : qtd_analytic_assumptions F) (hp : qtd_parameter_schedule F)
    (hl : qtd_algorithmic_laws F) :
    ∀ ε, qtd_admissible_error ε →
      qtd_total_variation F.pStar (F.pBar ε) ≤ 3 * ε := by
  intro ε hε
  have htail := qtd_subgaussian_cube_tail F ha hp ε hε
  exact (ha.2.2.2.2.2.2.2.2 ε hε).trans (by linarith)

@[blueprint "lem:qtd-poisson-mean-identity"
  (statement := /-- Let $d\in\mathbb N$, and let $F$ be a quantized transition diffusion family in dimension $d$ satisfying the prescribed parameter schedule. For every tolerance $\epsilon$ with $0<\epsilon<1$, the expected number of uniformization events equals the aggregate rate determined by the scheduled segment rates and segment lengths:
  \[
    \mathbb E[\overline N_\epsilon]=\overline\beta_\epsilon.
  \] -/)
  (proof := /-- Fix an admissible $\epsilon$, so that $0<\epsilon<1$ by \cref{def:qtd-admissible-error}. By \cref{def:qtd-parameter-schedule}, positivity of the early-stopping offset and its prescribed upper bound imply
  \[
    d\log_2 K_\epsilon>0.
  \]
  For each segment, put $A_w=T_\epsilon-t_{\epsilon,w}$ and $B_w=t_{\epsilon,w+1}-t_{\epsilon,w}$. The grid recurrence gives $A_w=3B_w$. If $A_w\ge0$, then both $\min\{1,A_w\}$ and $B_w$ are nonnegative; if $A_w<0$, then both are nonpositive. Since the numerator $2d\log_2K_\epsilon$ is nonnegative, the scheduled product
  \[
    \frac{2d\log_2K_\epsilon}{\min\{1,A_w\}}B_w
  \]
  is nonnegative in either case. Thus every summand in \cref{def:qtd-aggregate-rate} is nonnegative, so $\overline\beta_\epsilon\ge0$.

  It remains to compute the first moment in \cref{def:qtd-expected-iterations}. For a nonnegative parameter $r$, shift the exponential series $e^r=\sum_{n\ge0}r^n/n!$ by one index and use $e^{-r}e^r=1$ to obtain
  \[
    \sum_{n\ge0}e^{-r}\frac{r^n}{n!}n=r.
  \]
  Applying this identity to $r=(\overline\beta_\epsilon)_+$ and using $\overline\beta_\epsilon\ge0$ removes the nonnegative-part operation and yields the claimed equality. -/)
  (title := /-- Expected number of uniformization events -/)
  (latexEnv := "lemma")]
lemma qtd_poisson_mean_identity {d : ℕ} (F : quantized_transition_diffusion_family d)
    (hp : qtd_parameter_schedule F) :
    ∀ ε, qtd_admissible_error ε →
      qtd_expected_iterations F ε = qtd_aggregate_rate F ε := by
  intro ε hε
  have hPoissonMean (r : ℝ≥0) :
      ∫ n : ℕ, (n : ℝ) ∂ ProbabilityTheory.poissonMeasure r = (r : ℝ) := by
    rw [ProbabilityTheory.integral_poissonMeasure]
    simp only [smul_eq_mul]
    let x : ℝ := r
    have hexp : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
      simpa only [← Real.exp_eq_exp_ℝ] using
        (NormedSpace.expSeries_div_hasSum_exp x)
    have hshift :
        HasSum
          (fun n : ℕ =>
            Real.exp (-x) * x ^ (n + 1) / ((n + 1).factorial : ℝ) * (n + 1 : ℝ))
          x := by
      have hs := hexp.mul_left (Real.exp (-x) * x)
      have hsum : Real.exp (-x) * x * Real.exp x = x := by
        calc
          Real.exp (-x) * x * Real.exp x =
              x * (Real.exp (-x) * Real.exp x) := by ring
          _ = x := by rw [← Real.exp_add]; simp
      rw [hsum] at hs
      refine hs.congr_fun ?_
      intro n
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ]
      field_simp
    let f : ℕ → ℝ :=
      fun n => Real.exp (-x) * x ^ n / (n.factorial : ℝ) * (n : ℝ)
    have hshift' : HasSum (fun n : ℕ => f (n + 1)) x := by
      simpa [f] using hshift
    have hfull : HasSum f x := by
      have h := (hasSum_nat_add_iff 1).mp hshift'
      simpa [f] using h
    simpa [f, x] using hfull.tsum_eq
  rcases hp ε hε with
    ⟨_, _, _, _, _, _, _, _, hδpos, hδbound, _, hrec, _, hrate⟩
  have hquot :
      0 < ε / ((d : ℝ) * Real.logb 2 (F.binCount ε)) :=
    lt_of_lt_of_le hδpos hδbound
  have hden : 0 < (d : ℝ) * Real.logb 2 (F.binCount ε) := by
    rcases (div_pos_iff.mp hquot) with hpos | hneg
    · exact hpos.2
    · exact (not_lt_of_ge (le_of_lt hε.1) hneg.1).elim
  have hscale : 0 ≤ 2 * (d : ℝ) * Real.logb 2 (F.binCount ε) := by
    nlinarith [hden]
  have hagg : 0 ≤ qtd_aggregate_rate F ε := by
    rw [qtd_aggregate_rate]
    apply Finset.sum_nonneg
    intro w hw
    rw [hrate w (Nat.le_of_lt (Finset.mem_range.mp hw))]
    have hgrid := hrec w (Finset.mem_range.mp hw)
    let A := F.horizon ε - F.timestamp ε w
    let B := F.timestamp ε (w + 1) - F.timestamp ε w
    have hAB : A = 3 * B := by
      dsimp [A, B]
      linarith
    change 0 ≤
      (2 * (d : ℝ) * Real.logb 2 (F.binCount ε) / min 1 A) * B
    by_cases hA : 0 ≤ A
    · have hB : 0 ≤ B := by nlinarith [hAB]
      exact mul_nonneg (div_nonneg hscale (le_min zero_le_one hA)) hB
    · have hA' : A ≤ 0 := le_of_not_ge hA
      have hB : B ≤ 0 := by nlinarith [hAB]
      have hmin : min 1 A ≤ 0 := le_trans (min_le_right 1 A) hA'
      exact mul_nonneg_of_nonpos_of_nonpos
        (div_nonpos_of_nonneg_of_nonpos hscale hmin) hB
  unfold qtd_expected_iterations
  rw [hPoissonMean, Real.coe_toNNReal _ hagg]

@[blueprint "lem:qtd-normalized-rate-sum-bound"
  (statement := /-- Let $W\in\mathbb N$, let $s_0,\ldots,s_W$ be positive real
  numbers with $s_{w+1}<s_w$ for every $w<W$, and suppose that $s_0=T$ and
  $s_W=\delta$. Then
  \[
    \sum_{w=0}^{W-1}\frac{s_w-s_{w+1}}{\min\{1,s_w\}}
      \le T+\log(1/\delta).
  \] -/)
  (proof := /-- Define $\Phi(x)=1+\log x$ for $0<x<1$ and $\Phi(x)=x$ for
  $x\ge1$. If two consecutive values lie below $1$, the inequality
  $\log y\le y-1$, applied to $y=s_{w+1}/s_w$, bounds the normalized segment
  cost by $\Phi(s_w)-\Phi(s_{w+1})$. If both lie above $1$, this is an equality;
  if they straddle $1$, the same logarithmic inequality at $s_{w+1}$ gives the
  bound. Summing telescopes. Finally $\Phi(T)\le T$ and
  $\log\delta\le\Phi(\delta)$, again by $\log x\le x-1$, which yields the
  displayed estimate. -/)
  (title := /-- Telescoping bound for normalized scheduled rates -/)
  (latexEnv := "lemma")]
lemma qtd_normalized_rate_sum_bound (s : ℕ → ℝ) (W : ℕ) (T δ : ℝ)
    (hpos : ∀ w ≤ W, 0 < s w)
    (hdec : ∀ w < W, s (w + 1) < s w)
    (hzero : s 0 = T) (hterminal : s W = δ) :
    ∑ w ∈ Finset.range W, (s w - s (w + 1)) / min 1 (s w) ≤
      T + Real.log (1 / δ) := by
  let φ : ℝ → ℝ := fun x => if x < 1 then 1 + Real.log x else x
  have hstep : ∀ w < W,
      (s w - s (w + 1)) / min 1 (s w) ≤ φ (s w) - φ (s (w + 1)) := by
    intro w hw
    have hsw : 0 < s w := hpos w (Nat.le_of_lt hw)
    have hsn : 0 < s (w + 1) := hpos (w + 1) (Nat.succ_le_of_lt hw)
    have hlt : s (w + 1) < s w := hdec w hw
    by_cases hsmall : s w < 1
    · have hnsmall : s (w + 1) < 1 := lt_trans hlt hsmall
      have hlog := Real.log_le_sub_one_of_pos (div_pos hsn hsw)
      rw [Real.log_div (ne_of_gt hsn) (ne_of_gt hsw)] at hlog
      have hfrac :
          (s w - s (w + 1)) / s w = 1 - s (w + 1) / s w := by
        field_simp
      rw [min_eq_right (le_of_lt hsmall), hfrac]
      simp only [φ, if_pos hsmall, if_pos hnsmall]
      linarith
    · have hsone : 1 ≤ s w := le_of_not_gt hsmall
      rw [min_eq_left hsone]
      by_cases hnsmall : s (w + 1) < 1
      · have hlog := Real.log_le_sub_one_of_pos hsn
        simp only [φ, if_neg hsmall, if_pos hnsmall]
        linarith
      · simp [φ, hsmall, hnsmall]
  have hsum :
      (∑ w ∈ Finset.range W, (s w - s (w + 1)) / min 1 (s w)) ≤
        ∑ w ∈ Finset.range W, (φ (s w) - φ (s (w + 1))) := by
    exact Finset.sum_le_sum fun w hw => hstep w (Finset.mem_range.mp hw)
  rw [Finset.sum_range_sub'] at hsum
  have hφzero : φ (s 0) ≤ s 0 := by
    by_cases hsmall : s 0 < 1
    · have hlog := Real.log_le_sub_one_of_pos (hpos 0 (Nat.zero_le W))
      simp only [φ, if_pos hsmall]
      linarith
    · simp [φ, hsmall]
  have hφterminal : Real.log (s W) ≤ φ (s W) := by
    by_cases hsmall : s W < 1
    · simp [φ, hsmall]
    · have hlog := Real.log_le_sub_one_of_pos (hpos W le_rfl)
      simp only [φ, if_neg hsmall]
      linarith
  have hδpos : 0 < δ := by simpa [hterminal] using hpos W le_rfl
  have hlog_inv : Real.log (1 / δ) = -Real.log δ := by
    rw [Real.log_div one_ne_zero (ne_of_gt hδpos), Real.log_one, zero_sub]
  calc
    (∑ w ∈ Finset.range W, (s w - s (w + 1)) / min 1 (s w)) ≤
        φ (s 0) - φ (s W) := hsum
    _ ≤ s 0 - Real.log (s W) := sub_le_sub hφzero hφterminal
    _ = T + Real.log (1 / δ) := by rw [hzero, hterminal, hlog_inv]; ring

@[blueprint "lem:qtd-aggregate-rate-bound"
  (statement := /-- Let $d\in\mathbb N$, and let $F$ be a quantized transition
  diffusion family satisfying the parameter schedule in
  \cref{def:qtd-parameter-schedule}. Then, for every $\epsilon\in\mathbb R$ with
  $0<\epsilon<1$, its aggregate scheduled rate satisfies
  \[
    \overline\beta_\epsilon\le
    2d\log_2(K_\epsilon)\bigl(T_\epsilon+\log(1/\delta_\epsilon)\bigr),
  \]
  where $K_\epsilon$, $T_\epsilon$, and $\delta_\epsilon$ are respectively the
  bin count, time horizon, and early-stopping offset recorded by $F$. -/)
  (proof := /-- Fix an admissible $\epsilon$ and put
  $s_w=T_\epsilon-t_{\epsilon,w}$. The terminal identity in
  \cref{def:qtd-parameter-schedule} gives $s_W=\delta_\epsilon>0$, and backward
  induction through the grid recurrence shows that every $s_w$ is positive.
  The same recurrence gives $s_w-s_{w+1}=s_{w+1}/2>0$, so the sequence is
  strictly decreasing. Hence \cref{lem:qtd-normalized-rate-sum-bound} yields
  \[
    \sum_{w=0}^{W-1}\frac{s_w-s_{w+1}}{\min\{1,s_w\}}
      \le T_\epsilon+\log(1/\delta_\epsilon).
  \]
  The positive early-stop bound in \cref{def:qtd-parameter-schedule} forces
  $d\log_2(K_\epsilon)>0$. Substituting the scheduled rate formula into
  \cref{def:qtd-aggregate-rate} and multiplying the normalized estimate by
  $2d\log_2(K_\epsilon)$ proves the claim. -/)
  (title := /-- Integrated uniformization-rate estimate -/)
  (latexEnv := "lemma")]
lemma qtd_aggregate_rate_bound {d : ℕ} (F : quantized_transition_diffusion_family d)
    (hp : qtd_parameter_schedule F) :
    ∀ ε, qtd_admissible_error ε →
      qtd_aggregate_rate F ε ≤
        2 * (d : ℝ) * Real.logb 2 (F.binCount ε) *
          (F.horizon ε + Real.log (1 / F.earlyStop ε)) := by
  intro ε hε
  have hεpos : 0 < ε := hε.1
  rcases hp ε hε with
    ⟨_, _, _, _, _, _, _, _, hδpos, hδupper, htzero, hrec, hterminal, hrate⟩
  let s : ℕ → ℝ := fun w => F.horizon ε - F.timestamp ε w
  have hszero : s 0 = F.horizon ε := by simp [s, htzero]
  have hsterminal : s (F.terminalIndex ε) = F.earlyStop ε := by
    dsimp [s]
    rw [hterminal]
    ring
  have hsrec : ∀ w < F.terminalIndex ε,
      s w - s (w + 1) = (1 / 2 : ℝ) * s (w + 1) := by
    intro w hw
    dsimp [s]
    have hr := hrec w hw
    linarith
  have hspos : ∀ w ≤ F.terminalIndex ε, 0 < s w := by
    intro w hw
    exact Nat.decreasingInduction
      (fun k hk ih => by
        have hr := hsrec k hk
        nlinarith)
      (by simpa [hsterminal] using hδpos) hw
  have hsdec : ∀ w < F.terminalIndex ε, s (w + 1) < s w := by
    intro w hw
    have hr := hsrec w hw
    have hn := hspos (w + 1) (Nat.succ_le_of_lt hw)
    nlinarith
  have hnorm := qtd_normalized_rate_sum_bound s (F.terminalIndex ε)
    (F.horizon ε) (F.earlyStop ε) hspos hsdec hszero hsterminal
  let B : ℝ := (d : ℝ) * Real.logb 2 (F.binCount ε)
  have hquotpos : 0 < ε / B := by
    exact lt_of_lt_of_le hδpos hδupper
  have hBpos : 0 < B := by
    rcases (div_pos_iff.mp hquotpos) with h | h
    · exact h.2
    · linarith
  rw [qtd_aggregate_rate]
  calc
    (∑ w ∈ Finset.range (F.terminalIndex ε),
        F.rate ε w * (F.timestamp ε (w + 1) - F.timestamp ε w)) =
        2 * B * ∑ w ∈ Finset.range (F.terminalIndex ε),
          (s w - s (w + 1)) / min 1 (s w) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      rw [hrate w (Nat.le_of_lt (Finset.mem_range.mp hw))]
      dsimp [B, s]
      ring
    _ ≤ 2 * B * (F.horizon ε + Real.log (1 / F.earlyStop ε)) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = 2 * (d : ℝ) * Real.logb 2 (F.binCount ε) *
        (F.horizon ε + Real.log (1 / F.earlyStop ε)) := by dsimp [B]; ring

@[blueprint "lem:qtd-complexity-order"
  (statement := /-- Let $d\in\mathbb N$, and let $F$ be a quantized transition diffusion family satisfying the validated parameter schedule in \cref{def:qtd-validated-parameter-schedule}. Then the expected iteration and score-estimation complexity satisfies
  \[
    O\!\left(d\log^2(d/\epsilon)\right)
  \]
  as $\epsilon\downarrow0$. -/)
  (proof := /-- Fix $d$ and $F$, and put
  $B_\epsilon=d\log_2K_\epsilon$. By
  \cref{lem:qtd-poisson-mean-identity}, the expected number of iterations is
  $\overline\beta_\epsilon$. The estimate in
  \cref{lem:qtd-aggregate-rate-bound} gives
  \[
    \overline\beta_\epsilon
      \le 2B_\epsilon
        \bigl(T_\epsilon+\log(1/\delta_\epsilon)\bigr).
  \]
  The validated schedule in \cref{def:qtd-validated-parameter-schedule}
  supplies
  $\delta_\epsilon>2\epsilon/(3B_\epsilon)$; hence
  \[
    \log(1/\delta_\epsilon)
      <\log\!\left(\frac{3B_\epsilon}{2\epsilon}\right).
  \]
  Substitution of the scheduled formulas for $L_\epsilon$, $l_\epsilon$,
  and $K_\epsilon=2L_\epsilon/l_\epsilon$ shows, with constants depending
  only on the fixed parameters $d$, $H$, $\sigma$, and $m_0$, that
  \[
    \log_2K_\epsilon=O(\log(d/\epsilon)).
  \]
  The identity
  $T_\epsilon=\log(d/\epsilon)+\log\log_2K_\epsilon$ and the preceding
  upper bound for $\log(1/\delta_\epsilon)$ then show that both
  $T_\epsilon$ and $\log(1/\delta_\epsilon)$ are
  $O(\log(d/\epsilon))$. Multiplying these estimates proves
  $\overline\beta_\epsilon=O(d\log^2(d/\epsilon))$. -/)
  (title := /-- Almost-linear expected complexity -/)
  (latexEnv := "lemma")]
lemma qtd_complexity_order {d : ℕ} (F : quantized_transition_diffusion_family d)
    (hp : qtd_validated_parameter_schedule F) :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0))
      (qtd_expected_iterations F) (qtd_complexity_scale d) := by
  obtain ⟨hbase, hvalid⟩ := hp
  have hhalf : qtd_admissible_error (1 / 2 : ℝ) := ⟨by norm_num, by norm_num⟩
  obtain ⟨hσ, hH, hm0, _⟩ := hbase (1 / 2) hhalf
  obtain ⟨hB1half, _, _⟩ := hvalid (1 / 2) hhalf
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    rcases eq_or_lt_of_le (Nat.cast_nonneg (α := ℝ) d) with h | h
    · rw [← h, zero_mul] at hB1half
      linarith
    · exact h
  have hdnat : 0 < d := Nat.cast_pos.mp hdpos
  have hdnat1 : 1 ≤ d := hdnat
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdnat1
  have hlogd : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hd1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨M0, hM0pos, hM0⟩ : ∃ M0 : ℝ, 0 < M0 ∧
      M0 = F.sigma * Real.sqrt (2 * (d : ℝ)) + (d : ℝ) +
        Real.sqrt ((d : ℝ) * F.secondMomentBound) := by
    refine ⟨_, ?_, rfl⟩
    have h1 : 0 ≤ F.sigma * Real.sqrt (2 * (d : ℝ)) :=
      mul_nonneg hσ.le (Real.sqrt_nonneg _)
    have h2 : 0 ≤ Real.sqrt ((d : ℝ) * F.secondMomentBound) := Real.sqrt_nonneg _
    linarith
  obtain ⟨A, hApos, hA⟩ : ∃ A : ℝ, 0 < A ∧
      A = 4 * F.sigma * F.hessianBound * Real.sqrt 2 * M0 := by
    refine ⟨_, ?_, rfl⟩
    have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h4 : (0 : ℝ) < 4 * F.sigma := by linarith
    exact mul_pos (mul_pos (mul_pos h4 hH) h2) hM0pos
  obtain ⟨c3, hc3pos, hc3⟩ : ∃ c3 : ℝ, 0 < c3 ∧ c3 = 4 / Real.log 2 :=
    ⟨_, div_pos (by norm_num) hlog2, rfl⟩
  have ha1 := abs_nonneg (Real.log A)
  have ha2 := abs_nonneg (Real.log c3)
  have ha3 := abs_nonneg (Real.log 2)
  have ha4 := abs_nonneg (Real.log 3)
  have ha5 := abs_nonneg (Real.log (d : ℝ))
  have hk1 := le_abs_self (Real.log A)
  have hk2 := le_abs_self (Real.log c3)
  have hk3 := le_abs_self (Real.log 2)
  have hk4 := le_abs_self (Real.log 3)
  have hk5 := le_abs_self (Real.log (d : ℝ))
  obtain ⟨Lam, hLam1, hLamA, hLamc3, hLam2, hLam3, hLamd⟩ :
      ∃ L : ℝ, 1 ≤ L ∧ Real.log A ≤ L ∧ Real.log c3 ≤ L ∧ Real.log 2 ≤ L ∧
        Real.log 3 ≤ L ∧ Real.log (d : ℝ) ≤ L :=
    ⟨1 + |Real.log A| + |Real.log c3| + |Real.log 2| + |Real.log 3| +
        |Real.log (d : ℝ)|,
      by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  refine Asymptotics.isBigO_iff.mpr ⟨16 * c3, ?_⟩
  rw [nhdsWithin, Filter.eventually_inf_principal]
  have hmem : Set.Iio (min (1 / 3 : ℝ) (Real.exp (-Lam))) ∈ nhds (0 : ℝ) :=
    Iio_mem_nhds (lt_min (by norm_num) (Real.exp_pos _))
  filter_upwards [hmem] with ε hεlt hεmem
  have hεpos : 0 < ε := hεmem
  have hεlt' : ε < min (1 / 3 : ℝ) (Real.exp (-Lam)) := hεlt
  have hε3 : ε < 1 / 3 := lt_of_lt_of_le hεlt' (min_le_left _ _)
  have hεexp : ε < Real.exp (-Lam) := lt_of_lt_of_le hεlt' (min_le_right _ _)
  have hεadm : qtd_admissible_error ε := ⟨hεpos, by linarith⟩
  obtain ⟨lam, hlam⟩ : ∃ l : ℝ, l = Real.log ((d : ℝ) / ε) := ⟨_, rfl⟩
  have hlamsplit : lam = Real.log (d : ℝ) - Real.log ε := by
    rw [hlam, Real.log_div (ne_of_gt hdpos) (ne_of_gt hεpos)]
  have hlogεneg : Real.log ε < -Lam := by
    have h := Real.log_lt_log hεpos hεexp
    rwa [Real.log_exp] at h
  have hlamLam : Lam ≤ lam := by rw [hlamsplit]; linarith
  have hlam1 : 1 ≤ lam := le_trans hLam1 hlamLam
  have hlampos : 0 < lam := lt_of_lt_of_le zero_lt_one hlam1
  have hnlogε : -Real.log ε ≤ lam := by rw [hlamsplit]; linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = Real.log (2 * (d : ℝ) / ε) := ⟨_, rfl⟩
  have husplit : u = Real.log 2 + lam := by
    rw [hu, hlam, show (2 * (d : ℝ) / ε) = 2 * ((d : ℝ) / ε) by ring,
      Real.log_mul (by norm_num) (ne_of_gt (div_pos hdpos hεpos))]
  have hu1 : 1 ≤ u := by rw [husplit]; linarith
  have hupos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  have hu2 : u ≤ 2 * lam := by
    have h : Real.log 2 ≤ lam := le_trans hLam2 hlamLam
    rw [husplit]; linarith
  obtain ⟨_, _, _, hL, hlw, hKdef, _, hTdef, hδpos, _, _, _, _, _⟩ := hbase ε hεadm
  obtain ⟨hB1, _, hδlow⟩ := hvalid ε hεadm
  rw [← hu] at hL hlw
  obtain ⟨Mu, hMupos, hMu⟩ : ∃ Mu : ℝ, 0 < Mu ∧
      Mu = F.sigma * Real.sqrt (2 * (d : ℝ) * u) + (d : ℝ) +
        Real.sqrt ((d : ℝ) * F.secondMomentBound) := by
    refine ⟨_, ?_, rfl⟩
    have h1 : 0 ≤ F.sigma * Real.sqrt (2 * (d : ℝ) * u) :=
      mul_nonneg hσ.le (Real.sqrt_nonneg _)
    have h2 : 0 ≤ Real.sqrt ((d : ℝ) * F.secondMomentBound) := Real.sqrt_nonneg _
    linarith
  rw [← hMu] at hlw
  have hden : (0 : ℝ) < 2 * F.hessianBound * Mu :=
    mul_pos (mul_pos (by norm_num) hH) hMupos
  have hcellpos : 0 < F.cellWidth ε := by
    rw [hlw]; exact div_pos hεpos hden
  have hsq2upos : (0 : ℝ) < Real.sqrt (2 * u) := Real.sqrt_pos.mpr (by linarith)
  have hbinpos : 0 < F.binCount ε := by
    rw [hKdef, hL]
    exact div_pos (mul_pos (by norm_num) (mul_pos hσ hsq2upos)) hcellpos
  have hbinmul : F.binCount ε * ε =
      4 * F.sigma * F.hessianBound * Mu * Real.sqrt (2 * u) := by
    rw [hKdef, hL, hlw, div_div_eq_mul_div,
      div_mul_cancel₀ _ (ne_of_gt hεpos)]
    ring
  have hsqrt2 : Real.sqrt (2 * u) = Real.sqrt 2 * Real.sqrt u :=
    Real.sqrt_mul (by norm_num) u
  have hsu : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hupos.le
  have hsq1 : 1 ≤ Real.sqrt u := Real.one_le_sqrt.mpr hu1
  have hMule : Mu ≤ M0 * Real.sqrt u := by
    rw [hMu, hM0, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * (d : ℝ)) u]
    have hnn : 0 ≤ (d : ℝ) + Real.sqrt ((d : ℝ) * F.secondMomentBound) := by positivity
    have hstep : (d : ℝ) + Real.sqrt ((d : ℝ) * F.secondMomentBound) ≤
        ((d : ℝ) + Real.sqrt ((d : ℝ) * F.secondMomentBound)) * Real.sqrt u :=
      le_mul_of_one_le_right hnn hsq1
    have hexp : (F.sigma * Real.sqrt (2 * (d : ℝ)) + (d : ℝ) +
          Real.sqrt ((d : ℝ) * F.secondMomentBound)) * Real.sqrt u =
        F.sigma * (Real.sqrt (2 * (d : ℝ)) * Real.sqrt u) +
          ((d : ℝ) + Real.sqrt ((d : ℝ) * F.secondMomentBound)) * Real.sqrt u := by
      ring
    rw [hexp]
    linarith [hstep]
  have hsHnn : (0 : ℝ) ≤ 4 * F.sigma * F.hessianBound :=
    mul_nonneg (mul_nonneg (by norm_num) hσ.le) hH.le
  have hbin_le : F.binCount ε * ε ≤ A * u := by
    rw [hbinmul, hA, hsqrt2]
    have h1 : Mu * (Real.sqrt 2 * Real.sqrt u) ≤
        M0 * Real.sqrt u * (Real.sqrt 2 * Real.sqrt u) :=
      mul_le_mul_of_nonneg_right hMule (by positivity)
    have h2 : M0 * Real.sqrt u * (Real.sqrt 2 * Real.sqrt u) =
        Real.sqrt 2 * M0 * u := by
      rw [show M0 * Real.sqrt u * (Real.sqrt 2 * Real.sqrt u) =
        Real.sqrt 2 * M0 * (Real.sqrt u * Real.sqrt u) by ring, hsu]
    have h3 : Mu * (Real.sqrt 2 * Real.sqrt u) ≤ Real.sqrt 2 * M0 * u := by
      rw [← h2]; exact h1
    calc 4 * F.sigma * F.hessianBound * Mu * (Real.sqrt 2 * Real.sqrt u)
        = 4 * F.sigma * F.hessianBound * (Mu * (Real.sqrt 2 * Real.sqrt u)) := by ring
      _ ≤ 4 * F.sigma * F.hessianBound * (Real.sqrt 2 * M0 * u) :=
          mul_le_mul_of_nonneg_left h3 hsHnn
      _ = 4 * F.sigma * F.hessianBound * Real.sqrt 2 * M0 * u := by ring
  have hlogbin : Real.log (F.binCount ε) ≤ 4 * lam := by
    have h1 : Real.log (F.binCount ε * ε) ≤ Real.log (A * u) :=
      Real.log_le_log (mul_pos hbinpos hεpos) hbin_le
    rw [Real.log_mul (ne_of_gt hbinpos) (ne_of_gt hεpos),
      Real.log_mul (ne_of_gt hApos) (ne_of_gt hupos)] at h1
    have h2 : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hupos
    have h3 : Real.log A ≤ lam := le_trans hLamA hlamLam
    linarith
  have hB2le : Real.logb 2 (F.binCount ε) ≤ c3 * lam := by
    rw [← Real.log_div_log, div_le_iff₀ hlog2, hc3]
    have h : 4 / Real.log 2 * lam * Real.log 2 = 4 * lam := by
      field_simp
    rw [h]
    linarith
  have hB2pos : 0 < Real.logb 2 (F.binCount ε) := by
    rcases le_or_gt (Real.logb 2 (F.binCount ε)) 0 with h | h
    · exfalso
      have h2 : (d : ℝ) * Real.logb 2 (F.binCount ε) ≤ (d : ℝ) * 0 :=
        mul_le_mul_of_nonneg_left h hdpos.le
      rw [mul_zero] at h2
      linarith
    · exact h
  have hlogB2 : Real.log (Real.logb 2 (F.binCount ε)) ≤ 2 * lam - 1 := by
    have h1 : Real.log (Real.logb 2 (F.binCount ε)) ≤ Real.log (c3 * lam) :=
      Real.log_le_log hB2pos hB2le
    rw [Real.log_mul (ne_of_gt hc3pos) (ne_of_gt hlampos)] at h1
    have h2 : Real.log lam ≤ lam - 1 := Real.log_le_sub_one_of_pos hlampos
    have h3 : Real.log c3 ≤ lam := le_trans hLamc3 hlamLam
    linarith
  have hTle : F.horizon ε ≤ 3 * lam := by
    rw [hTdef, ← hlam]
    linarith
  have hBpos : (0 : ℝ) < (d : ℝ) * Real.logb 2 (F.binCount ε) := mul_pos hdpos hB2pos
  have hlog1δ : Real.log (1 / F.earlyStop ε) ≤ 5 * lam := by
    have hapos : (0 : ℝ) < 2 / 3 * (ε / ((d : ℝ) * Real.logb 2 (F.binCount ε))) :=
      mul_pos (by norm_num) (div_pos hεpos hBpos)
    have h1 : 1 / F.earlyStop ε ≤
        1 / (2 / 3 * (ε / ((d : ℝ) * Real.logb 2 (F.binCount ε)))) :=
      one_div_le_one_div_of_le hapos hδlow.le
    have h2 : 1 / (2 / 3 * (ε / ((d : ℝ) * Real.logb 2 (F.binCount ε)))) =
        3 * ((d : ℝ) * Real.logb 2 (F.binCount ε)) / (2 * ε) := by
      rw [eq_div_iff (by positivity)]
      field_simp
    rw [h2] at h1
    have h3 : Real.log (1 / F.earlyStop ε) ≤
        Real.log (3 * ((d : ℝ) * Real.logb 2 (F.binCount ε)) / (2 * ε)) :=
      Real.log_le_log (one_div_pos.mpr hδpos) h1
    have h4 : Real.log (3 * ((d : ℝ) * Real.logb 2 (F.binCount ε)) / (2 * ε)) =
        Real.log 3 + (Real.log (d : ℝ) + Real.log (Real.logb 2 (F.binCount ε))) -
          (Real.log 2 + Real.log ε) := by
      rw [Real.log_div (ne_of_gt (mul_pos (by norm_num) hBpos))
          (ne_of_gt (mul_pos (by norm_num) hεpos)),
        Real.log_mul (by norm_num) (ne_of_gt hBpos),
        Real.log_mul (ne_of_gt hdpos) (ne_of_gt hB2pos),
        Real.log_mul (by norm_num) (ne_of_gt hεpos)]
    rw [h4] at h3
    have h5 : Real.log 3 ≤ lam := le_trans hLam3 hlamLam
    have h6 : Real.log (d : ℝ) ≤ lam := le_trans hLamd hlamLam
    linarith
  have hYle : F.horizon ε + Real.log (1 / F.earlyStop ε) ≤ 8 * lam := by linarith
  have hprodle : Real.logb 2 (F.binCount ε) *
      (F.horizon ε + Real.log (1 / F.earlyStop ε)) ≤ c3 * lam * (8 * lam) := by
    rcases le_or_gt 0 (F.horizon ε + Real.log (1 / F.earlyStop ε)) with hY0 | hY0
    · refine mul_le_mul hB2le hYle hY0 ?_
      exact le_of_lt (mul_pos hc3pos hlampos)
    · exact le_trans (le_of_lt (mul_neg_of_pos_of_neg hB2pos hY0))
        (le_of_lt (mul_pos (mul_pos hc3pos hlampos) (by linarith)))
  have hfinal : qtd_expected_iterations F ε ≤ 16 * c3 * ((d : ℝ) * lam ^ 2) := by
    rw [qtd_poisson_mean_identity F hbase ε hεadm]
    refine (qtd_aggregate_rate_bound F hbase ε hεadm).trans ?_
    have h1 : 2 * (d : ℝ) * (Real.logb 2 (F.binCount ε) *
        (F.horizon ε + Real.log (1 / F.earlyStop ε))) ≤
        2 * (d : ℝ) * (c3 * lam * (8 * lam)) :=
      mul_le_mul_of_nonneg_left hprodle (by positivity)
    calc 2 * (d : ℝ) * Real.logb 2 (F.binCount ε) *
          (F.horizon ε + Real.log (1 / F.earlyStop ε))
        = 2 * (d : ℝ) * (Real.logb 2 (F.binCount ε) *
            (F.horizon ε + Real.log (1 / F.earlyStop ε))) := by ring
      _ ≤ 2 * (d : ℝ) * (c3 * lam * (8 * lam)) := h1
      _ = 16 * c3 * ((d : ℝ) * lam ^ 2) := by ring
  have hEnn : 0 ≤ qtd_expected_iterations F ε := by
    rw [qtd_expected_iterations]
    exact integral_nonneg fun n => Nat.cast_nonneg n
  have hgval : qtd_complexity_scale d ε = (d : ℝ) * lam ^ 2 := by
    rw [qtd_complexity_scale, hlam]
  have hgnn : 0 ≤ qtd_complexity_scale d ε := by rw [hgval]; positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hEnn, abs_of_nonneg hgnn,
    hgval]
  exact hfinal

@[blueprint "lem:qtd-reverse-kl-accumulation"
  (statement := /-- Let $d\in\mathbb N$, and let $F$ be a quantized transition diffusion family in dimension $d$ satisfying the score-estimation assumption A4 from \cref{def:qtd-training-assumption}, the parameter schedule in \cref{def:qtd-parameter-schedule}, and the exact and learned reverse-process laws in \cref{def:qtd-reverse-process-laws}. Then, for every $\epsilon\in\mathbb R$ with $0<\epsilon<1$, the terminal reverse-process divergence satisfies
  \[
    D_{\mathrm{KL}}(q^{\leftarrow}_{T_\epsilon-\delta_\epsilon}\Vert
      \widehat q_{T_\epsilon-\delta_\epsilon})
    \le D_{\mathrm{KL}}(q^{\leftarrow}_0\Vert\widehat q_0)
       +(T_\epsilon-\delta_\epsilon)\epsilon_{\mathrm{score},\epsilon}^2.
  \] -/)
  (proof := /-- Fix an admissible tolerance $\epsilon$, write $W$ for its terminal index, and abbreviate $T=T_\epsilon$ and $\delta=\delta_\epsilon$. The recurrence in \cref{def:qtd-parameter-schedule} gives, by induction,
  \[
    t_w=T\bigl(1-(2/3)^w\bigr)\qquad(0\le w\le W).
  \]
  At $w=W$, the terminal identity $t_W=T-\delta$ and the strict positivity of $\delta$ imply $T>0$. Since $(2/3)^W\le1$, it follows that $T-\delta=t_W\ge0$.

  Define
  \[
    G(t)=D_{\mathrm{KL}}(q_t^{\leftarrow}\Vert\widehat q_t).
  \]
  By \cref{def:qtd-reverse-process-laws}, at every $t\in[0,T-\delta]$ the function $G$ has a derivative bounded above by the score-entropy loss. Assumption A4 in \cref{def:qtd-training-assumption} therefore gives
  \[
    G'(t)\le L_{\mathrm{SE}}(\widehat v)
      \le \epsilon_{\mathrm{score},\epsilon}^2.
  \]
  If $T-\delta=0$, the desired inequality is immediate. Otherwise, the mean value theorem supplies $c\in(0,T-\delta)$ such that
  \[
    \frac{G(T-\delta)-G(0)}{T-\delta}=G'(c)
      \le\epsilon_{\mathrm{score},\epsilon}^2.
  \]
  Multiplication by the positive duration yields
  $G(T-\delta)\le G(0)+(T-\delta)\epsilon_{\mathrm{score},\epsilon}^2$.
  Finally, the four endpoint identities in \cref{def:qtd-reverse-process-laws} identify these two values of $G$ with the terminal and initial divergences in the statement. -/)
  (title := /-- Accumulation of reverse-process score error -/)
  (latexEnv := "lemma")]
lemma qtd_reverse_kl_accumulation {d : ℕ} (F : quantized_transition_diffusion_family d)
    (ht : qtd_training_assumption F) (hp : qtd_parameter_schedule F)
    (hr : qtd_reverse_process_laws F) :
    ∀ ε, qtd_admissible_error ε →
      qtd_discrete_kl (F.qReverseAtStop ε) (F.qApproxAtStop ε) ≤
        qtd_discrete_kl (F.qReverseInitial ε) (F.qApproxInitial ε) +
          (F.horizon ε - F.earlyStop ε) * (F.scoreError ε) ^ 2 := by
  intro ε hε
  obtain ⟨_, hscore⟩ := ht ε hε
  obtain ⟨_, _, _, _, _, _, _, _, hδ, _, ht0, hstep, hlast, _⟩ := hp ε hε
  obtain ⟨_, _, _, _, _, hrev0, hrevlast, happ0, happlast, _, _, _, _, _, _,
    _, _, _, _, _, _, hkl, _, _⟩ := hr ε hε
  have htime : ∀ w ≤ F.terminalIndex ε,
      F.timestamp ε w =
        F.horizon ε * (1 - (2 / 3 : ℝ) ^ w) := by
    intro w hw
    induction w with
    | zero =>
        simp [ht0]
    | succ w ih =>
        have hwlt : w < F.terminalIndex ε := Nat.lt_of_succ_le hw
        have hwle : w ≤ F.terminalIndex ε := Nat.le_of_lt hwlt
        have hrec := hstep w hwlt
        rw [ih hwle] at hrec
        rw [pow_succ]
        norm_num at hrec ⊢
        ring_nf at hrec ⊢
        linarith
  have htime_last := htime (F.terminalIndex ε) le_rfl
  rw [hlast] at htime_last
  have hpow_pos : 0 < (2 / 3 : ℝ) ^ F.terminalIndex ε :=
    pow_pos (by norm_num) _
  have hhorizon : 0 < F.horizon ε := by
    nlinarith
  have hpow_le : (2 / 3 : ℝ) ^ F.terminalIndex ε ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have hduration : 0 ≤ F.horizon ε - F.earlyStop ε := by
    rw [htime_last]
    positivity
  have hrev0' : F.qReverse ε 0 = F.qReverseInitial ε := funext hrev0
  have hrevlast' :
      F.qReverse ε (F.horizon ε - F.earlyStop ε) =
        F.qReverseAtStop ε := funext hrevlast
  have happ0' : F.qApproxReverse ε 0 = F.qApproxInitial ε := funext happ0
  have happlast' :
      F.qApproxReverse ε (F.horizon ε - F.earlyStop ε) =
        F.qApproxAtStop ε := funext happlast
  rw [← hrevlast', ← happlast', ← hrev0', ← happ0']
  let g : ℝ → ℝ := fun t ↦
    qtd_discrete_kl (F.qReverse ε t) (F.qApproxReverse ε t)
  change g (F.horizon ε - F.earlyStop ε) ≤
    g 0 + (F.horizon ε - F.earlyStop ε) * F.scoreError ε ^ 2
  by_cases hzero : F.horizon ε - F.earlyStop ε = 0
  · simp [hzero]
  · have hduration_pos : 0 < F.horizon ε - F.earlyStop ε :=
      lt_of_le_of_ne hduration (Ne.symm hzero)
    have hcontinuous : ContinuousOn g
        (Set.Icc 0 (F.horizon ε - F.earlyStop ε)) := by
      intro t htin
      obtain ⟨r, hderiv, _⟩ := hkl t htin.1 htin.2
      exact hderiv.continuousAt.continuousWithinAt
    have hderiv : ∀ t ∈ Set.Ioo 0 (F.horizon ε - F.earlyStop ε),
        HasDerivAt g (deriv g t) t := by
      intro t htin
      obtain ⟨r, hgr, _⟩ := hkl t (le_of_lt htin.1) (le_of_lt htin.2)
      exact hgr.differentiableAt.hasDerivAt
    obtain ⟨c, hc, hslope⟩ :=
      exists_hasDerivAt_eq_slope g (deriv g) hduration_pos hcontinuous hderiv
    obtain ⟨r, hgr, hrle⟩ :=
      hkl c (le_of_lt hc.1) (le_of_lt hc.2)
    have hc_bound : deriv g c ≤ F.scoreError ε ^ 2 := by
      rw [hgr.deriv]
      exact hrle.trans hscore
    rw [hslope, sub_zero] at hc_bound
    have hdifference :
        g (F.horizon ε - F.earlyStop ε) - g 0 ≤
          F.scoreError ε ^ 2 * (F.horizon ε - F.earlyStop ε) :=
      (div_le_iff₀ hduration_pos).mp hc_bound
    linarith

@[blueprint "lem:qtd-schedule-horizon-nonnegative"
  (statement := /-- Let $d\in\mathbb N$ and let $F$ satisfy the prescribed parameter schedule. For every $\epsilon$ with $0<\epsilon<1$, both the scheduled horizon $T_\epsilon$ and the terminal time $T_\epsilon-\delta_\epsilon$ are nonnegative. -/)
  (proof := /-- By \cref{def:qtd-parameter-schedule}, the remaining time at the terminal grid point is $\delta_\epsilon>0$. The grid recurrence shows by descending induction that the remaining time is positive at every preceding grid point; at the initial grid point this is $T_\epsilon>0$. Starting instead from the zero initial timestamp, the same recurrence and positivity of the remaining times show by forward induction that every timestamp is nonnegative. The terminal timestamp identity then gives $T_\epsilon-\delta_\epsilon\ge0$. -/)
  (title := /-- Nonnegativity of the scheduled time interval -/)
  (latexEnv := "lemma")]
lemma qtd_schedule_horizon_nonnegative {d : ℕ}
    (F : quantized_transition_diffusion_family d) (hp : qtd_parameter_schedule F) :
    ∀ ε, qtd_admissible_error ε →
      0 ≤ F.horizon ε - F.earlyStop ε ∧ 0 ≤ F.horizon ε := by
  intro ε hε
  rcases hp ε hε with
    ⟨_, _, _, _, _, _, _, _, hδ, _, ht0, hstep, hterminal, _⟩
  have hremaining : ∀ w, w ≤ F.terminalIndex ε →
      0 < F.horizon ε - F.timestamp ε w := by
    intro w hw
    induction hw using Nat.decreasingInduction with
    | self =>
        rw [hterminal]
        linarith
    | of_succ k hk ih =>
        have hkstep := hstep k hk
        linarith
  have htime : ∀ w, w ≤ F.terminalIndex ε → 0 ≤ F.timestamp ε w := by
    intro w
    induction w with
    | zero =>
        intro _
        rw [ht0]
    | succ w ih =>
        intro hw
        have hwlt : w < F.terminalIndex ε := Nat.lt_of_succ_le hw
        have hprev : 0 ≤ F.timestamp ε w :=
          ih (Nat.le_trans (Nat.le_succ w) hw)
        have hrem := hremaining (w + 1) hw
        have hwstep := hstep w hwlt
        linarith
  constructor
  · rw [← hterminal]
    exact htime (F.terminalIndex ε) le_rfl
  · have hzero := hremaining 0 (Nat.zero_le _)
    rw [ht0] at hzero
    simpa only [sub_zero] using hzero.le

@[blueprint "lem:qtd-exponential-decay"
  (statement := /-- Let $f\colon\mathbb R\to\mathbb R$ and $T\ge0$. If, for every $t\in[0,T]$, the function $f$ has a derivative $r_t$ satisfying $r_t\le-f(t)$, then
  \[
    f(T)\le e^{-T}f(0).
  \] -/)
  (proof := /-- Set $g(t)=e^t f(t)$. The product rule gives $g'(t)=e^t(f(t)+r_t)\le0$ at every point of $[0,T]$. Hence $g$ is antitone there, so $e^T f(T)\le f(0)$. Multiplication by the positive factor $e^{-T}$ yields the asserted estimate. -/)
  (title := /-- Exponential decay from a differential inequality -/)
  (latexEnv := "lemma")]
lemma qtd_exponential_decay (f : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hderiv : ∀ t, 0 ≤ t → t ≤ T →
      ∃ r, HasDerivAt f r t ∧ r ≤ -f t) :
    f T ≤ Real.exp (-T) * f 0 := by
  let g : ℝ → ℝ := fun t ↦ Real.exp t * f t
  have hg : ∀ t, 0 ≤ t → t ≤ T →
      ∃ r, HasDerivAt g r t ∧ r ≤ 0 := by
    intro t ht0 htT
    obtain ⟨r, hr, hrle⟩ := hderiv t ht0 htT
    refine ⟨Real.exp t * f t + Real.exp t * r, ?_, ?_⟩
    · exact (Real.hasDerivAt_exp t).mul hr
    · rw [← mul_add]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg t) (by linarith)
  have hgcont : ContinuousOn g (Set.Icc 0 T) := by
    intro t ht
    obtain ⟨r, hr, _⟩ := hg t ht.1 ht.2
    exact hr.continuousAt.continuousWithinAt
  have hgdiff : DifferentiableOn ℝ g (interior (Set.Icc 0 T)) := by
    intro t ht
    have ht' : t ∈ Set.Icc 0 T := interior_subset ht
    exact ((hg t ht'.1 ht'.2).choose_spec.1).differentiableAt.differentiableWithinAt
  have hgderiv : ∀ t ∈ interior (Set.Icc 0 T), deriv g t ≤ 0 := by
    intro t ht
    have ht' : t ∈ Set.Icc 0 T := interior_subset ht
    obtain ⟨r, hr, hrle⟩ := hg t ht'.1 ht'.2
    rw [hr.deriv]
    exact hrle
  have hganti : AntitoneOn g (Set.Icc 0 T) :=
    antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hgcont hgdiff hgderiv
  have hgend : g T ≤ g 0 :=
    hganti ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT
  calc
    f T = Real.exp (-T) * g T := by
      dsimp [g]
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp (-T) * g 0 :=
      mul_le_mul_of_nonneg_left hgend (Real.exp_nonneg _)
    _ = Real.exp (-T) * f 0 := by simp [g]

@[blueprint "lem:qtd-forward-kl-contraction"
  (statement := /-- Let $d\in\mathbb N$, and let $F$ be a quantized transition diffusion family satisfying the parameter schedule, the algorithmic laws, and the validated reverse-process laws. Then, for every $\epsilon\in(0,1)$,
  \[
    D_{\mathrm{KL}}(q^{\leftarrow}_0\Vert\widehat q_0)
      \le e^{-2T_\epsilon}d\log_2K_\epsilon,
  \]
  where $T_\epsilon$ and $K_\epsilon$ are respectively the horizon and bin count recorded by $F$. -/)
  (proof := /-- Fix an admissible $\epsilon$. By
  \cref{lem:qtd-schedule-horizon-nonnegative}, both $T_\epsilon$ and
  $T_\epsilon-\delta_\epsilon$ are nonnegative. The endpoint and
  time-reversal clauses of \cref{def:qtd-reverse-process-laws} identify
  $q^{\leftarrow}_0$ with the exact forward law at time $T_\epsilon$.
  Put
  \[
    G(t)=D_{\mathrm{KL}}(q^{\to}_t\Vert\widehat q_0).
  \]
  By \cref{def:qtd-validated-reverse-process-laws}, $G'(t)\le-2G(t)$
  throughout $[0,T_\epsilon]$. Apply
  \cref{lem:qtd-exponential-decay} to
  $s\mapsto G(s/2)$ on $[0,2T_\epsilon]$. Its derivative is at most the
  negative of its value, and therefore
  $G(T_\epsilon)\le e^{-2T_\epsilon}G(0)$. Finally, the initial-entropy
  clause of \cref{def:qtd-reverse-process-laws} gives
  $G(0)\le d\log_2K_\epsilon$. Multiplication by the nonnegative factor
  $e^{-2T_\epsilon}$ proves the asserted estimate. -/)
  (title := /-- Exponential KL contraction of the forward chain -/)
  (latexEnv := "lemma")]
lemma qtd_forward_kl_contraction {d : ℕ} (F : quantized_transition_diffusion_family d)
    (hp : qtd_parameter_schedule F) (hl : qtd_algorithmic_laws F)
    (hr : qtd_validated_reverse_process_laws F) :
    ∀ ε, qtd_admissible_error ε →
      qtd_discrete_kl (F.qReverseInitial ε) (F.qApproxInitial ε) ≤
        Real.exp (-2 * F.horizon ε) * (d : ℝ) *
          Real.logb 2 (F.binCount ε) := by
  intro ε hε
  obtain ⟨hrlaws, hmlsi⟩ := hr
  obtain ⟨hTδ, hT⟩ := qtd_schedule_horizon_nonnegative F hp ε hε
  obtain ⟨_, _, _, _, hrevfwd, hrev0, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, hinit⟩ := hrlaws ε hε
  have hid : F.qReverseInitial ε = F.qForward ε (F.horizon ε) := by
    funext x
    rw [← hrev0 x, hrevfwd 0 x le_rfl hTδ, sub_zero]
  rw [hid]
  have hdecay : ∀ u : ℝ, 0 ≤ u → u ≤ 2 * F.horizon ε →
      ∃ r, HasDerivAt
        (fun v : ℝ ↦ qtd_discrete_kl (F.qForward ε (v / 2)) (F.qApproxInitial ε)) r u ∧
        r ≤ -qtd_discrete_kl (F.qForward ε (u / 2)) (F.qApproxInitial ε) := by
    intro u hu0 huT
    have hhalf0 : 0 ≤ u / 2 := by linarith
    have hhalfT : u / 2 ≤ F.horizon ε := by linarith
    obtain ⟨r, hr, hrle⟩ := hmlsi ε hε (u / 2) hhalf0 hhalfT
    have hderiv : HasDerivAt (fun v : ℝ ↦ v / 2) (1 / 2 : ℝ) u := by
      simpa using (hasDerivAt_id u).div_const 2
    refine ⟨r * (1 / 2), ?_, ?_⟩
    · exact HasDerivAt.comp u hr hderiv
    · nlinarith [hrle]
  have hkey := qtd_exponential_decay
    (fun v : ℝ ↦ qtd_discrete_kl (F.qForward ε (v / 2)) (F.qApproxInitial ε))
    (2 * F.horizon ε) (by linarith) hdecay
  simp only [zero_div] at hkey
  have hhalf : 2 * F.horizon ε / 2 = F.horizon ε := by ring
  rw [hhalf] at hkey
  have hstep :
      Real.exp (-(2 * F.horizon ε)) *
          qtd_discrete_kl (F.qForward ε 0) (F.qApproxInitial ε) ≤
        Real.exp (-(2 * F.horizon ε)) *
          ((d : ℝ) * Real.logb 2 (F.binCount ε)) :=
    mul_le_mul_of_nonneg_left hinit (Real.exp_nonneg _)
  have hfinal :
      Real.exp (-(2 * F.horizon ε)) * ((d : ℝ) * Real.logb 2 (F.binCount ε)) =
        Real.exp (-2 * F.horizon ε) * (d : ℝ) * Real.logb 2 (F.binCount ε) := by
    rw [neg_mul]
    ring
  linarith [hkey.trans hstep, hfinal.le, hfinal.ge]

@[blueprint "lem:qtd-terminal-kl-bound"
  (statement := /-- Let $d\in\mathbb N$, and let $F$ satisfy the validated parameter schedule and validated reverse-process laws. For every $\epsilon\in(0,1)$, the terminal exact and learned reverse laws satisfy
  \[
    D_{\mathrm{KL}}(q^{\leftarrow}_{T-\delta}\Vert\widehat q_{T-\delta})
      \le 2\epsilon^2.
  \] -/)
  (proof := /-- Fix an admissible $\epsilon$, and abbreviate
  $B=d\log_2K_\epsilon$ and $T=T_\epsilon$. The validated schedule in
  \cref{def:qtd-validated-parameter-schedule} gives $B\ge1$,
  $T=\log(B/\epsilon)$, and
  $\epsilon_{\mathrm{score}}\le\epsilon/\max\{1,T\}$.
  By \cref{lem:qtd-forward-kl-contraction},
  \[
    D_{\mathrm{KL}}(q^{\leftarrow}_0\Vert\widehat q_0)
      \le e^{-2T}B
      =\frac{\epsilon^2}{B}
      \le\epsilon^2.
  \]
  The scheduled time grid has $0\le T-\delta\le T$. If $0\le T\le1$,
  then
  \[
    (T-\delta)\epsilon_{\mathrm{score}}^2
      \le T\epsilon^2\le\epsilon^2.
  \]
  If $T\ge1$, then
  \[
    (T-\delta)\epsilon_{\mathrm{score}}^2
      \le T(\epsilon/T)^2
      =\epsilon^2/T\le\epsilon^2.
  \]
  Substitution of these two estimates into
  \cref{lem:qtd-reverse-kl-accumulation} yields the claimed upper bound
  $2\epsilon^2$. -/)
  (title := /-- Terminal KL estimate -/)
  (latexEnv := "lemma")]
lemma qtd_terminal_kl_bound {d : ℕ} (F : quantized_transition_diffusion_family d)
    (ht : qtd_training_assumption F) (hp : qtd_validated_parameter_schedule F)
    (hl : qtd_algorithmic_laws F) (hr : qtd_validated_reverse_process_laws F) :
    ∀ ε, qtd_admissible_error ε →
      qtd_discrete_kl (F.qReverseAtStop ε) (F.qApproxAtStop ε) ≤ 2 * ε ^ 2 := by
  intro ε hε
  have hacc := qtd_reverse_kl_accumulation F ht hp.1 hr.1 ε hε
  have hcon := qtd_forward_kl_contraction F hp.1 hl hr ε hε
  obtain ⟨hse0, _⟩ := ht ε hε
  obtain ⟨hTδ, hT0⟩ := qtd_schedule_horizon_nonnegative F hp.1 ε hε
  obtain ⟨_, _, _, _, _, _, _, hTdef, hδpos, _, _, _, _, _⟩ := hp.1 ε hε
  obtain ⟨hB1, hsc, _⟩ := hp.2 ε hε
  set B2 : ℝ := Real.logb 2 (F.binCount ε) with hB2def
  have hεpos : 0 < ε := hε.1
  have hB2pos : 0 < B2 := by
    rcases le_or_gt B2 0 with h | h
    · nlinarith [Nat.cast_nonneg (α := ℝ) d]
    · exact h
  have hdpos : 0 < (d : ℝ) := by
    rcases le_or_gt (d : ℝ) 0 with h | h
    · nlinarith
    · exact h
  have hBpos : 0 < (d : ℝ) * B2 := mul_pos hdpos hB2pos
  have hyt : 0 < (d : ℝ) * B2 / ε := div_pos hBpos hεpos
  have hTeq : F.horizon ε = Real.log ((d : ℝ) * B2 / ε) := by
    rw [hTdef, ← Real.log_mul (by positivity) (ne_of_gt hB2pos)]
    congr 1
    ring
  have hexp : Real.exp (-2 * F.horizon ε) = (ε / ((d : ℝ) * B2)) ^ 2 := by
    rw [hTeq]
    have hsplit : (-2 : ℝ) * Real.log ((d : ℝ) * B2 / ε) =
        -Real.log ((d : ℝ) * B2 / ε) + -Real.log ((d : ℝ) * B2 / ε) := by ring
    rw [hsplit, Real.exp_add, Real.exp_neg, Real.exp_log hyt]
    field_simp
  have hbound1 : Real.exp (-2 * F.horizon ε) * (d : ℝ) * B2 ≤ ε ^ 2 := by
    have hrw : Real.exp (-2 * F.horizon ε) * (d : ℝ) * B2 =
        ε ^ 2 / ((d : ℝ) * B2) := by
      rw [hexp]
      field_simp
    rw [hrw, div_le_iff₀ hBpos]
    nlinarith [sq_nonneg ε]
  have hm1 : (1 : ℝ) ≤ max 1 (F.horizon ε) := le_max_left _ _
  have hmT : F.horizon ε ≤ max 1 (F.horizon ε) := le_max_right _ _
  have hmpos : 0 < max 1 (F.horizon ε) := lt_of_lt_of_le zero_lt_one hm1
  have hse2 : F.scoreError ε ^ 2 ≤ (ε / max 1 (F.horizon ε)) ^ 2 := by
    have h0 : 0 ≤ ε / max 1 (F.horizon ε) := by positivity
    nlinarith [hse0, hsc]
  have hbound2 : (F.horizon ε - F.earlyStop ε) * F.scoreError ε ^ 2 ≤ ε ^ 2 := by
    have hdur : F.horizon ε - F.earlyStop ε ≤ max 1 (F.horizon ε) := by
      linarith
    have hstep : (F.horizon ε - F.earlyStop ε) * F.scoreError ε ^ 2 ≤
        max 1 (F.horizon ε) * (ε / max 1 (F.horizon ε)) ^ 2 :=
      mul_le_mul hdur hse2 (sq_nonneg _) hmpos.le
    have hval : max 1 (F.horizon ε) * (ε / max 1 (F.horizon ε)) ^ 2 =
        ε ^ 2 / max 1 (F.horizon ε) := by
      field_simp
    rw [hval] at hstep
    have hle : ε ^ 2 / max 1 (F.horizon ε) ≤ ε ^ 2 := by
      rw [div_le_iff₀ hmpos]
      nlinarith [sq_nonneg ε]
    linarith
  linarith

@[blueprint "lem:qtd-pinsker-conversion"
  (statement := /-- Let $d\in\mathbb N$, and let $F$ satisfy the training assumption, the validated parameter schedule, the algorithmic laws, and the validated reverse-process laws. Then, for every $\epsilon\in(0,1)$,
  \[
    \operatorname{TV}_{\mathrm d}
      (q^{\leftarrow}_{T-\delta},\widehat q_{T-\delta})\le\epsilon.
  \] -/)
  (proof := /-- Apply Pinsker's inequality $\operatorname{TV}_{\mathrm d}(p,q)\le\sqrt{D_{\mathrm{KL}}(p\Vert q)/2}$ to the probability masses supplied by \cref{def:qtd-algorithmic-laws}. The bound of \cref{lem:qtd-terminal-kl-bound} then gives the result. A general measure-theoretic Pinsker theorem was not found in the installed libraries, so this conversion remains a separate interface node. -/)
  (title := /-- Pinsker conversion at the terminal time -/)
  (latexEnv := "lemma")]
lemma qtd_pinsker_conversion {d : ℕ} (F : quantized_transition_diffusion_family d)
    (ht : qtd_training_assumption F) (hp : qtd_validated_parameter_schedule F)
    (hl : qtd_algorithmic_laws F) (hr : qtd_validated_reverse_process_laws F) :
    ∀ ε, qtd_admissible_error ε →
      qtd_discrete_total_variation (F.qReverseAtStop ε) (F.qApproxAtStop ε) ≤ ε := by
  intro ε hε
  classical
  have hεpos : 0 < ε := hε.1
  have hε1 : ε < 1 := hε.2
  have fixd : ∀ (f : ℝ → ℝ) (a b x : ℝ), HasDerivAt f a x → a = b → HasDerivAt f b x :=
    fun f a b x h hab => hab ▸ h
  have endpt : ∀ (f : ℝ → ℝ) (r c : ℝ), 0 < c → HasDerivAt f r c → f c = 0 →
      (∀ u, 0 ≤ u → u ≤ c → 0 ≤ f u) → r ≤ 0 := by
    intro f r c hc hd h0 hnn
    rw [hasDerivAt_iff_tendsto_slope] at hd
    have hle : nhdsWithin c (Set.Iio c) ≤ nhdsWithin c ({c}ᶜ) :=
      nhdsWithin_mono _ (fun x hx => ne_of_lt hx)
    have hmem : Set.Ioi (0 : ℝ) ∈ nhdsWithin c (Set.Iio c) :=
      nhdsWithin_le_nhds (Ioi_mem_nhds hc)
    refine le_of_tendsto (hd.mono_left hle) ?_
    filter_upwards [hmem, self_mem_nhdsWithin] with u hu0 huc
    have hu0' : 0 < u := hu0
    have huc' : u < c := huc
    have h2 : 0 ≤ f u := hnn u (le_of_lt hu0') (le_of_lt huc')
    rw [slope_def_field, h0]
    exact div_nonpos_iff.mpr (Or.inl ⟨by linarith, by linarith⟩)
  have conn : ∀ (m : ℕ) (P : ℕ → Prop),
      (∀ y, y < 2 ^ m → P y → ∀ i, i < m → P (y ^^^ 2 ^ i)) →
      ∀ y y', y < 2 ^ m → y' < 2 ^ m → P y → P y' := by
    intro m P hstep
    have key : ∀ k y y', y < 2 ^ m → y' < 2 ^ m →
        (∀ j, k ≤ j → y.testBit j = y'.testBit j) → P y → P y' := by
      intro k
      induction k with
      | zero =>
        intro y y' _ _ hbits hP
        have h : y = y' := Nat.eq_of_testBit_eq (fun j => hbits j (Nat.zero_le j))
        exact h ▸ hP
      | succ k ih =>
        intro y y' hy hy' hbits hP
        by_cases hsame : y.testBit k = y'.testBit k
        · refine ih y y' hy hy' (fun j hj => ?_) hP
          rcases Nat.eq_or_lt_of_le hj with h | h
          · rw [← h]; exact hsame
          · exact hbits j h
        · by_cases hkm : k < m
          · have hzlt : y ^^^ 2 ^ k < 2 ^ m :=
              Nat.xor_lt_two_pow hy (Nat.pow_lt_pow_right (by norm_num) hkm)
            have hPz : P (y ^^^ 2 ^ k) := hstep y hy hP k hkm
            refine ih (y ^^^ 2 ^ k) y' hzlt hy' (fun j hj => ?_) hPz
            rcases Nat.eq_or_lt_of_le hj with h | h
            · rw [← h, Nat.testBit_xor, Nat.testBit_two_pow_self, Bool.xor_true]
              exact (Bool.eq_not_of_ne (Ne.symm hsame)).symm
            · rw [Nat.testBit_xor, Nat.testBit_two_pow_of_ne (by omega), Bool.xor_false]
              exact hbits j h
          · exfalso
            refine hsame ?_
            have h1 : y.testBit k = false :=
              Nat.testBit_lt_two_pow
                (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) (by omega)))
            have h2 : y'.testBit k = false :=
              Nat.testBit_lt_two_pow
                (lt_of_lt_of_le hy' (Nat.pow_le_pow_right (by norm_num) (by omega)))
            rw [h1, h2]
    intro y y' hy hy' hP
    refine key m y y' hy hy' (fun j hj => ?_) hP
    have h1 : y.testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) hj))
    have h2 : y'.testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hy' (Nat.pow_le_pow_right (by norm_num) hj))
    rw [h1, h2]
  have core : ∀ t : ℝ, 0 ≤ t → 3 / 2 * (t - 1) ^ 2 ≤ (t + 2) * (t * Real.log t - t + 1) := by
    have hF : ∀ t : ℝ, 0 < t →
        HasDerivAt (fun x : ℝ => (x + 2) * (x * Real.log x - x + 1)
            - (3 / 2 * (x * x) - 3 * x + 3 / 2))
          ((t * Real.log t - t + 1) + (t + 2) * Real.log t - (3 * t - 3)) t := by
      intro t ht
      have hid : HasDerivAt (fun y : ℝ => y) 1 t := hasDerivAt_id' t
      have h1 : HasDerivAt (fun x : ℝ => x * Real.log x) (Real.log t + 1) t :=
        fixd _ _ _ _ (hid.mul (Real.hasDerivAt_log (ne_of_gt ht))) (by field_simp)
      have h2 : HasDerivAt (fun x : ℝ => x * Real.log x - x + 1) (Real.log t) t :=
        fixd _ _ _ _ ((h1.sub hid).add_const 1) (by ring)
      have hpoly : HasDerivAt (fun x : ℝ => 3 / 2 * (x * x) - 3 * x + 3 / 2) (3 * t - 3) t :=
        fixd _ _ _ _ ((((hid.mul hid).const_mul (3 / 2 : ℝ)).sub
          (hid.const_mul (3 : ℝ))).add_const (3 / 2)) (by ring)
      exact fixd _ _ _ _ (((hid.add_const 2).mul h2).sub hpoly) (by ring)
    have hF1 : ∀ t : ℝ, 0 < t →
        HasDerivAt (fun x : ℝ => (x * Real.log x - x + 1) + (x + 2) * Real.log x - (3 * x - 3))
          (2 * Real.log t + 2 / t - 2) t := by
      intro t ht
      have hid : HasDerivAt (fun y : ℝ => y) 1 t := hasDerivAt_id' t
      have h1 : HasDerivAt (fun x : ℝ => x * Real.log x) (Real.log t + 1) t :=
        fixd _ _ _ _ (hid.mul (Real.hasDerivAt_log (ne_of_gt ht))) (by field_simp)
      have h2 : HasDerivAt (fun x : ℝ => x * Real.log x - x + 1) (Real.log t) t :=
        fixd _ _ _ _ ((h1.sub hid).add_const 1) (by ring)
      have hlogd : HasDerivAt (fun x : ℝ => (x + 2) * Real.log x) (Real.log t + (t + 2) / t) t :=
        fixd _ _ _ _ ((hid.add_const 2).mul (Real.hasDerivAt_log (ne_of_gt ht))) (by field_simp)
      exact fixd _ _ _ _ ((h2.add hlogd).sub
        (fixd _ _ _ _ ((hid.const_mul (3 : ℝ)).sub_const 3) rfl)) (by field_simp; ring)
    have hF2 : ∀ t : ℝ, 0 < t → 0 ≤ 2 * Real.log t + 2 / t - 2 := by
      intro t ht
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / t by positivity)
      rw [Real.log_div one_ne_zero (ne_of_gt ht), Real.log_one] at h
      have h2 : 2 / t = 2 * (1 / t) := by ring
      linarith
    have hsign : ∀ t : ℝ, 0 < t →
        (1 ≤ t → 0 ≤ (t * Real.log t - t + 1) + (t + 2) * Real.log t - (3 * t - 3)) ∧
        (t ≤ 1 → (t * Real.log t - t + 1) + (t + 2) * Real.log t - (3 * t - 3) ≤ 0) := by
      have hcont1 : ∀ a b : ℝ, 0 < a →
          ContinuousOn (fun x : ℝ => (x * Real.log x - x + 1) + (x + 2) * Real.log x - (3 * x - 3))
            (Set.Icc a b) := by
        intro a b ha x hx
        exact ((hF1 x (lt_of_lt_of_le ha hx.1)).continuousAt).continuousWithinAt
      intro t ht
      constructor
      · intro h1
        rcases eq_or_lt_of_le h1 with h | h
        · rw [← h]; norm_num
        · obtain ⟨c, hc, hcv⟩ := exists_hasDerivAt_eq_slope
            (fun x : ℝ => (x * Real.log x - x + 1) + (x + 2) * Real.log x - (3 * x - 3))
            (fun x : ℝ => 2 * Real.log x + 2 / x - 2) h (hcont1 1 t one_pos)
            (fun x hx => hF1 x (lt_trans one_pos hx.1))
          have hnn := hF2 c (lt_trans one_pos hc.1)
          rw [hcv] at hnn
          norm_num at hnn
          have hd : 0 < t - 1 := by linarith
          rcases div_nonneg_iff.mp hnn with ⟨hnum, _⟩ | ⟨_, hden⟩
          · linarith
          · linarith
      · intro h1
        rcases eq_or_lt_of_le h1 with h | h
        · rw [h]; norm_num
        · obtain ⟨c, hc, hcv⟩ := exists_hasDerivAt_eq_slope
            (fun x : ℝ => (x * Real.log x - x + 1) + (x + 2) * Real.log x - (3 * x - 3))
            (fun x : ℝ => 2 * Real.log x + 2 / x - 2) h (hcont1 t 1 ht)
            (fun x hx => hF1 x (lt_trans ht hx.1))
          have hnn := hF2 c (lt_trans ht hc.1)
          rw [hcv] at hnn
          norm_num at hnn
          have hd : 0 < 1 - t := by linarith
          rcases div_nonneg_iff.mp hnn with ⟨hnum, _⟩ | ⟨_, hden⟩
          · linarith
          · linarith
    have hcont : ∀ a b : ℝ, 0 < a →
        ContinuousOn (fun x : ℝ => (x + 2) * (x * Real.log x - x + 1)
            - (3 / 2 * (x * x) - 3 * x + 3 / 2)) (Set.Icc a b) := by
      intro a b ha x hx
      exact ((hF x (lt_of_lt_of_le ha hx.1)).continuousAt).continuousWithinAt
    intro t ht
    have hexp : 3 / 2 * (t - 1) ^ 2 = 3 / 2 * (t * t) - 3 * t + 3 / 2 := by ring
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h]; norm_num
    · have hgoal : 0 ≤ (t + 2) * (t * Real.log t - t + 1) - (3 / 2 * (t * t) - 3 * t + 3 / 2) := by
        rcases lt_trichotomy t 1 with hlt | heq | hgt
        · obtain ⟨c, hc, hcv⟩ := exists_hasDerivAt_eq_slope
            (fun x : ℝ => (x + 2) * (x * Real.log x - x + 1)
              - (3 / 2 * (x * x) - 3 * x + 3 / 2))
            (fun x : ℝ => (x * Real.log x - x + 1) + (x + 2) * Real.log x - (3 * x - 3))
            hlt (hcont t 1 h) (fun x hx => hF x (lt_trans h hx.1))
          have hs := (hsign c (lt_trans h hc.1)).2 (le_of_lt hc.2)
          rw [hcv] at hs
          norm_num at hs
          have hd : 0 < 1 - t := by linarith
          rcases div_nonpos_iff.mp hs with ⟨_, hden⟩ | ⟨hnum, _⟩
          · linarith
          · linarith
        · rw [heq]; norm_num
        · obtain ⟨c, hc, hcv⟩ := exists_hasDerivAt_eq_slope
            (fun x : ℝ => (x + 2) * (x * Real.log x - x + 1)
              - (3 / 2 * (x * x) - 3 * x + 3 / 2))
            (fun x : ℝ => (x * Real.log x - x + 1) + (x + 2) * Real.log x - (3 * x - 3))
            hgt (hcont 1 t one_pos) (fun x hx => hF x (lt_trans one_pos hx.1))
          have hs := (hsign c (lt_trans one_pos hc.1)).1 (le_of_lt hc.1)
          rw [hcv] at hs
          norm_num at hs
          have hd : 0 < t - 1 := by linarith
          rcases div_nonneg_iff.mp hs with ⟨hnum, _⟩ | ⟨_, hden⟩
          · linarith
          · linarith
      linarith
  have hptw : ∀ a b : ℝ, 0 ≤ a → 0 < b →
      3 / 2 * (a - b) ^ 2 / (a + 2 * b) ≤ a * Real.log (a / b) - a + b := by
    intro a b ha hb
    have hc := core (a / b) (div_nonneg ha hb.le)
    have hab : 0 < a + 2 * b := by linarith
    have hbne : b ≠ 0 := ne_of_gt hb
    have e1 : b ^ 2 * (3 / 2 * (a / b - 1) ^ 2) = 3 / 2 * (a - b) ^ 2 := by field_simp
    have e2 : b ^ 2 * ((a / b + 2) * ((a / b) * Real.log (a / b) - a / b + 1))
        = (a + 2 * b) * (a * Real.log (a / b) - a + b) := by field_simp
    have hb2 : (0 : ℝ) < b ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hc hb2.le
    rw [e1, e2] at hmul
    rw [div_le_iff₀ hab]
    linarith
  have pinskerFin : ∀ (S : Finset ℕ) (u v : ℕ → ℝ), (∀ x ∈ S, 0 ≤ u x) → (∀ x ∈ S, 0 < v x) →
      ∑ x ∈ S, u x = 1 → ∑ x ∈ S, v x = 1 →
      (∑ x ∈ S, |u x - v x|) ^ 2 / 2 ≤ ∑ x ∈ S, u x * Real.log (u x / v x) := by
    intro S u v hu hv hus hvs
    have hgpos : ∀ x ∈ S, 0 < u x + 2 * v x := by
      intro x hx
      have h1 := hu x hx
      have h2 := hv x hx
      linarith
    have hsum3 : ∑ x ∈ S, (u x + 2 * v x) = 3 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hus, hvs]
      ring
    have hced := Finset.sq_sum_div_le_sum_sq_div S (fun x => |u x - v x|) hgpos
    rw [hsum3] at hced
    have hterm : ∀ x ∈ S, 3 / 2 * (|u x - v x| ^ 2 / (u x + 2 * v x))
        ≤ u x * Real.log (u x / v x) - u x + v x := by
      intro x hx
      have h := hptw (u x) (v x) (hu x hx) (hv x hx)
      rw [sq_abs]
      calc 3 / 2 * ((u x - v x) ^ 2 / (u x + 2 * v x))
          = 3 / 2 * (u x - v x) ^ 2 / (u x + 2 * v x) := by ring
        _ ≤ _ := h
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum] at hsum
    have hrhs : ∑ x ∈ S, (u x * Real.log (u x / v x) - u x + v x)
        = ∑ x ∈ S, u x * Real.log (u x / v x) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hus, hvs]
      ring
    rw [hrhs] at hsum
    have hced' : (∑ x ∈ S, |u x - v x|) ^ 2 / 3
        ≤ ∑ x ∈ S, |u x - v x| ^ 2 / (u x + 2 * v x) := hced
    linarith
  have hkl := qtd_terminal_kl_bound F ht hp hl hr ε hε
  obtain ⟨hmass, hoff, hgeom, hdecode, htvpres, hRAS, hcode⟩ := hl
  obtain ⟨hrl, hmlsi⟩ := hr
  obtain ⟨hTδ0, hT0⟩ := qtd_schedule_horizon_nonnegative F hp.1 ε hε
  obtain ⟨hσ, hH, hm0, hLdef, hldef, hKdef, _, hTdef, hδpos, hδup, _, _, _, _⟩ := hp.1 ε hε
  obtain ⟨hB1, _, _⟩ := hp.2 ε hε
  obtain ⟨hint, hcb, hfrate, _⟩ := hcode ε hε
  obtain ⟨R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12, R13, R14, R15, R16, R17,
    R18, R19, R20, R21, R22, R23, R24⟩ := hrl ε hε
  obtain ⟨_, _, _, _, hpmass, hqmass⟩ := hmass ε hε
  obtain ⟨hpnn, hpsummable, hptsum, Np, hpNp⟩ := hpmass
  obtain ⟨hqnn, hqsummable, hqtsum, Nq, hqNq⟩ := hqmass
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hB2pos : 0 < Real.logb 2 (F.binCount ε) := by
    rcases le_or_gt (Real.logb 2 (F.binCount ε)) 0 with h | h
    · exfalso
      have := mul_nonpos_of_nonneg_of_nonpos hdnn h
      linarith
    · exact h
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    rcases eq_or_lt_of_le hdnn with h | h
    · exfalso
      rw [← h, zero_mul] at hB1
      linarith
    · exact h
  have hd0 : 0 < d := by exact_mod_cast hdpos
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    have : 1 ≤ d := hd0
    exact_mod_cast this
  have hfl1 : 1 ≤ ⌊Real.logb 2 (F.binCount ε)⌋₊ := by
    rcases Nat.eq_zero_or_pos ⌊Real.logb 2 (F.binCount ε)⌋₊ with h | h
    · exfalso
      rw [hint, h] at hB2pos
      norm_num at hB2pos
    · exact h
  have hB2ge1 : (1 : ℝ) ≤ Real.logb 2 (F.binCount ε) := by
    rw [hint]
    exact_mod_cast hfl1
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [one_div, Real.log_inv] at h
    linarith
  have hLpos : 0 < F.cubeRadius ε := by
    rw [hLdef]
    have h1 : 0 < Real.log (2 * (d : ℝ) / ε) := by
      refine Real.log_pos ?_
      rw [lt_div_iff₀ hεpos]
      nlinarith
    exact mul_pos hσ (Real.sqrt_pos.mpr (by positivity))
  have hlpos : 0 < F.cellWidth ε := by
    rw [hldef]
    refine div_pos hεpos ?_
    refine mul_pos (by linarith : (0 : ℝ) < 2 * F.hessianBound) ?_
    have h1 : 0 ≤ F.sigma * Real.sqrt (2 * (d : ℝ) * Real.log (2 * (d : ℝ) / ε)) :=
      mul_nonneg hσ.le (Real.sqrt_nonneg _)
    have h2 : 0 ≤ Real.sqrt ((d : ℝ) * F.secondMomentBound) := Real.sqrt_nonneg _
    linarith
  have hKpos : 0 < F.binCount ε := by
    rw [hKdef]
    exact div_pos (by linarith) hlpos
  have hTδpos : 0 < F.horizon ε - F.earlyStop ε := by
    rcases eq_or_lt_of_le hTδ0 with hz | h
    · exfalso
      have hTlog : F.horizon ε
          = Real.log ((d : ℝ) * Real.logb 2 (F.binCount ε) / ε) := by
        rw [hTdef, ← Real.log_mul (by positivity) (ne_of_gt hB2pos)]
        congr 1
        field_simp
      have hBlt : (d : ℝ) * Real.logb 2 (F.binCount ε) < 2 := by
        by_contra hcon0
        have hcon : (2 : ℝ) ≤ (d : ℝ) * Real.logb 2 (F.binCount ε) := not_lt.mp hcon0
        have h2 : (2 : ℝ) ≤ (d : ℝ) * Real.logb 2 (F.binCount ε) / ε := by
          rw [le_div_iff₀ hεpos]
          nlinarith
        have h3 : Real.log 2 ≤ Real.log ((d : ℝ) * Real.logb 2 (F.binCount ε) / ε) :=
          Real.log_le_log (by norm_num) h2
        have h5 : ε / ((d : ℝ) * Real.logb 2 (F.binCount ε)) ≤ ε / 2 :=
          div_le_div_of_nonneg_left hεpos.le (by norm_num) hcon
        rw [hTlog] at hz
        linarith
      have hdeq : d = 1 := by
        by_contra hdne
        have h2 : 2 ≤ d := by omega
        have h2' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast h2
        nlinarith
      have hfleq : ⌊Real.logb 2 (F.binCount ε)⌋₊ = 1 := by
        by_contra hne
        have h2 : 2 ≤ ⌊Real.logb 2 (F.binCount ε)⌋₊ := by omega
        have h2' : (2 : ℝ) ≤ Real.logb 2 (F.binCount ε) := by
          rw [hint]
          exact_mod_cast h2
        nlinarith
      have hB2one : Real.logb 2 (F.binCount ε) = 1 := by
        rw [hint, hfleq]
        norm_num
      have hKtwo : F.binCount ε = 2 := by
        rw [← Real.log_div_log, div_eq_one_iff_eq (by linarith)] at hB2one
        have h := Real.exp_log hKpos
        rw [hB2one, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
        exact h.symm
      have hlL : F.cellWidth ε = F.cubeRadius ε := by
        rw [hKtwo, eq_div_iff (ne_of_gt hlpos)] at hKdef
        linarith
      have hnone : d * ⌊Real.logb 2 (F.binCount ε)⌋₊ = 1 := by
        rw [hfleq, mul_one]
        exact hdeq
      obtain ⟨_, _, _, hcov, _, _, _, _, _⟩ := hgeom ε hε
      have hpt3 : ∀ c : ℝ, |c| ≤ F.cubeRadius ε →
          ∃ x ∈ F.quantizationCodebook ε,
            F.quantizationCellLower ε x ⟨0, hd0⟩ ≤ c ∧
              c < F.quantizationCellLower ε x ⟨0, hd0⟩ + F.cellWidth ε := by
        intro c hc
        have hmemcube : (WithLp.toLp 2 (fun _ : Fin d => c) : EuclideanSpace ℝ (Fin d))
            ∈ qtd_quantization_cube F ε := by
          simp only [qtd_quantization_cube, Set.mem_setOf_eq]
          intro i
          exact hc
        rw [hcov] at hmemcube
        obtain ⟨x, hxS, hxcell⟩ := Set.mem_iUnion₂.mp hmemcube
        exact ⟨x, hxS, hxcell.2 ⟨0, hd0⟩⟩
      obtain ⟨x1, hx1S, hx1a, hx1b⟩ := hpt3 (-F.cubeRadius ε) (by
        rw [abs_neg, abs_of_pos hLpos])
      obtain ⟨x2, hx2S, hx2a, hx2b⟩ := hpt3 0 (by
        rw [abs_zero]; exact hLpos.le)
      obtain ⟨x3, hx3S, hx3a, hx3b⟩ := hpt3 (F.cubeRadius ε) (by rw [abs_of_pos hLpos])
      rw [hlL] at hx1b hx2b hx3b
      have h12 : x1 ≠ x2 := by
        intro h
        rw [h] at hx1a
        linarith
      have h23 : x2 ≠ x3 := by
        intro h
        rw [h] at hx2a
        linarith
      have h13 : x1 ≠ x3 := by
        intro h
        rw [h] at hx1a
        linarith
      have hb1 := (hcb x1).mp hx1S
      have hb2 := (hcb x2).mp hx2S
      have hb3 := (hcb x3).mp hx3S
      rw [hnone, pow_one] at hb1 hb2 hb3
      omega
    · exact h
  have hδT : F.earlyStop ε ≤ F.horizon ε := by linarith
  have hpδ : ∀ x, F.qForward ε (F.earlyStop ε) x = F.qReverseAtStop ε x := by
    intro x
    rw [R4 x, hRAS ε x hε]
  have hprop : ∀ y, F.qReverseAtStop ε y = 0 →
      ∀ x, x ≠ y → F.forwardRate ε y x = 1 → F.qReverseAtStop ε x = 0 := by
    intro y hy x hxy hrate
    have hD : HasDerivAt (fun s => F.qForward ε s y)
        (∑' z, F.forwardRate ε y z * F.qForward ε (F.earlyStop ε) z) (F.earlyStop ε) :=
      R17 (F.earlyStop ε) y hδpos.le hδT
    have hzero : F.qForward ε (F.earlyStop ε) y = 0 := by
      rw [hpδ y]; exact hy
    have hnn : ∀ u, 0 ≤ u → u ≤ F.earlyStop ε → 0 ≤ F.qForward ε u y := fun u h1 h2 =>
      (R1 u h1 (le_trans h2 hδT)).1 y
    have hle := endpt _ _ _ hδpos hD hzero hnn
    have hterms : ∀ z, 0 ≤ F.forwardRate ε y z * F.qForward ε (F.earlyStop ε) z := by
      intro z
      by_cases hzy : z = y
      · rw [hzy, hzero, mul_zero]
      · exact mul_nonneg (R10 y z (fun h => hzy h.symm)) ((R1 _ hδpos.le hδT).1 z)
    have hsum0 : ∑' z, F.forwardRate ε y z * F.qForward ε (F.earlyStop ε) z = 0 :=
      le_antisymm hle (tsum_nonneg hterms)
    obtain ⟨N, hN⟩ := (R1 (F.earlyStop ε) hδpos.le hδT).2.2.2
    have hvanish : ∀ z ∉ Finset.range N,
        F.forwardRate ε y z * F.qForward ε (F.earlyStop ε) z = 0 := by
      intro z hz
      simp only [Finset.mem_range, not_lt] at hz
      rw [hN z hz, mul_zero]
    rw [tsum_eq_sum hvanish] at hsum0
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => hterms z)).mp hsum0
    by_cases hxN : x ∈ Finset.range N
    · have h := hall x hxN
      rw [hrate, one_mul, hpδ x] at h
      exact h
    · simp only [Finset.mem_range, not_lt] at hxN
      rw [← hpδ x]
      exact hN x hxN
  have hxorne : ∀ (y i : ℕ), y ^^^ 2 ^ i ≠ y := by
    intro y i h
    have h2 := congrArg (fun m => Nat.testBit m i) h
    simp only [Nat.testBit_xor, Nat.testBit_two_pow_self, Bool.xor_true] at h2
    exact (Bool.not_ne_self _) h2
  have hnbr : ∀ y i, y < 2 ^ (d * ⌊Real.logb 2 (F.binCount ε)⌋₊) →
      i < d * ⌊Real.logb 2 (F.binCount ε)⌋₊ →
      F.forwardRate ε y (y ^^^ 2 ^ i) = 1 ∧ F.forwardRate ε (y ^^^ 2 ^ i) y = 1 ∧
        y ^^^ 2 ^ i < 2 ^ (d * ⌊Real.logb 2 (F.binCount ε)⌋₊) := by
    intro y i hy hi
    have hxlt : y ^^^ 2 ^ i < 2 ^ (d * ⌊Real.logb 2 (F.binCount ε)⌋₊) :=
      Nat.xor_lt_two_pow hy (Nat.pow_lt_pow_right (by norm_num) hi)
    have hback : y = (y ^^^ 2 ^ i) ^^^ 2 ^ i := by
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    refine ⟨?_, ?_, hxlt⟩
    · exact (hfrate y (y ^^^ 2 ^ i) (Ne.symm (hxorne y i))).1
        ⟨(hcb y).mpr hy, (hcb _).mpr hxlt, ⟨i, hi, rfl⟩⟩
    · exact (hfrate (y ^^^ 2 ^ i) y (hxorne y i)).1
        ⟨(hcb _).mpr hxlt, (hcb y).mpr hy, ⟨i, hi, hback⟩⟩
  have hppos : ∀ y, y < 2 ^ (d * ⌊Real.logb 2 (F.binCount ε)⌋₊) →
      0 < F.qReverseAtStop ε y := by
    intro y hy
    rcases eq_or_lt_of_le (hpnn y) with h | h
    · exfalso
      have hzero : ∀ z, F.qReverseAtStop ε z = 0 := by
        intro z
        by_cases hz : z < 2 ^ (d * ⌊Real.logb 2 (F.binCount ε)⌋₊)
        · refine conn (d * ⌊Real.logb 2 (F.binCount ε)⌋₊)
            (fun w => F.qReverseAtStop ε w = 0) ?_ y z hy hz h.symm
          intro w hw hw0 i hi
          obtain ⟨hr1, _, hxlt⟩ := hnbr w i hw hi
          exact hprop w hw0 (w ^^^ 2 ^ i) (hxorne w i) hr1
        · exact (hoff ε hε z (fun hmem => hz ((hcb z).mp hmem))).2.2.2.2.1
      rw [tsum_congr hzero, tsum_zero] at hptsum
      norm_num at hptsum
    · exact h
  have hqpos : ∀ y, y < 2 ^ (d * ⌊Real.logb 2 (F.binCount ε)⌋₊) →
      0 < F.qApproxAtStop ε y := by
    have hqprop : ∀ y, y < 2 ^ (d * ⌊Real.logb 2 (F.binCount ε)⌋₊) →
        F.qApproxAtStop ε y = 0 → ∀ i, i < d * ⌊Real.logb 2 (F.binCount ε)⌋₊ →
        F.qApproxAtStop ε (y ^^^ 2 ^ i) = 0 := by
      intro y hy hy0 i hi
      obtain ⟨_, hr2, hxlt⟩ := hnbr y i hy hi
      have hxy : y ^^^ 2 ^ i ≠ y := hxorne y i
      have hD : HasDerivAt (fun s => F.qApproxReverse ε s y)
          (∑' z, F.learnedReverseRate ε (F.horizon ε - F.earlyStop ε) y z *
            F.qApproxReverse ε (F.horizon ε - F.earlyStop ε) z)
          (F.horizon ε - F.earlyStop ε) :=
        R19 (F.horizon ε - F.earlyStop ε) y hTδ0 le_rfl
      have hzero : F.qApproxReverse ε (F.horizon ε - F.earlyStop ε) y = 0 := by
        rw [R9 y]; exact hy0
      have hnn : ∀ u, 0 ≤ u → u ≤ F.horizon ε - F.earlyStop ε →
          0 ≤ F.qApproxReverse ε u y := fun u h1 h2 => (R2 u h1 h2).2.1 y
      have hle := endpt _ _ _ hTδpos hD hzero hnn
      have hterms : ∀ z, 0 ≤ F.learnedReverseRate ε (F.horizon ε - F.earlyStop ε) y z *
          F.qApproxReverse ε (F.horizon ε - F.earlyStop ε) z := by
        intro z
        by_cases hzy : z = y
        · rw [hzy, hzero, mul_zero]
        · exact mul_nonneg
            (R14 (F.horizon ε - F.earlyStop ε) y z hTδ0 le_rfl (fun h => hzy h.symm)).2.1
            ((R2 _ hTδ0 le_rfl).2.1 z)
      have hsum0 : ∑' z, F.learnedReverseRate ε (F.horizon ε - F.earlyStop ε) y z *
          F.qApproxReverse ε (F.horizon ε - F.earlyStop ε) z = 0 :=
        le_antisymm hle (tsum_nonneg hterms)
      obtain ⟨N, hN⟩ := (R2 (F.horizon ε - F.earlyStop ε) hTδ0 le_rfl).2.2.2.2
      have hvanish : ∀ z ∉ Finset.range N,
          F.learnedReverseRate ε (F.horizon ε - F.earlyStop ε) y z *
            F.qApproxReverse ε (F.horizon ε - F.earlyStop ε) z = 0 := by
        intro z hz
        simp only [Finset.mem_range, not_lt] at hz
        rw [hN z hz, mul_zero]
      rw [tsum_eq_sum hvanish] at hsum0
      have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => hterms z)).mp hsum0
      have hrpos : 0 < F.reverseRate ε (F.horizon ε - F.earlyStop ε) y (y ^^^ 2 ^ i) := by
        rw [R12 (F.horizon ε - F.earlyStop ε) y (y ^^^ 2 ^ i) hTδ0 le_rfl (Ne.symm hxy),
          hr2, R7 y, R7 (y ^^^ 2 ^ i), one_mul]
        exact div_pos (hppos y hy) (hppos _ hxlt)
      have hlpos' : 0 < F.learnedReverseRate ε (F.horizon ε - F.earlyStop ε) y (y ^^^ 2 ^ i) :=
        (R14 (F.horizon ε - F.earlyStop ε) y (y ^^^ 2 ^ i) hTδ0 le_rfl (Ne.symm hxy)).2.2 hrpos
      by_cases hxN : y ^^^ 2 ^ i ∈ Finset.range N
      · have h := hall (y ^^^ 2 ^ i) hxN
        rcases mul_eq_zero.mp h with h1 | h2
        · exact absurd h1 (ne_of_gt hlpos')
        · rw [← R9 (y ^^^ 2 ^ i)]; exact h2
      · simp only [Finset.mem_range, not_lt] at hxN
        rw [← R9 (y ^^^ 2 ^ i)]
        exact hN _ hxN
    intro y hy
    rcases eq_or_lt_of_le (hqnn y) with h | h
    · exfalso
      have hzero : ∀ z, F.qApproxAtStop ε z = 0 := by
        intro z
        by_cases hz : z < 2 ^ (d * ⌊Real.logb 2 (F.binCount ε)⌋₊)
        · refine conn (d * ⌊Real.logb 2 (F.binCount ε)⌋₊)
            (fun w => F.qApproxAtStop ε w = 0) ?_ y z hy hz h.symm
          intro w hw hw0 i hi
          exact hqprop w hw hw0 i hi
        · exact (hoff ε hε z (fun hmem => hz ((hcb z).mp hmem))).2.2.2.2.2
      rw [tsum_congr hzero, tsum_zero] at hqtsum
      norm_num at hqtsum
    · exact h
  have hSp : ∀ z ∉ F.quantizationCodebook ε, F.qReverseAtStop ε z = 0 := fun z hz =>
    (hoff ε hε z hz).2.2.2.2.1
  have hSq : ∀ z ∉ F.quantizationCodebook ε, F.qApproxAtStop ε z = 0 := fun z hz =>
    (hoff ε hε z hz).2.2.2.2.2
  have hpsum : ∑ z ∈ F.quantizationCodebook ε, F.qReverseAtStop ε z = 1 := by
    have h : ∑' z, F.qReverseAtStop ε z
        = ∑ z ∈ F.quantizationCodebook ε, F.qReverseAtStop ε z := tsum_eq_sum hSp
    rw [← h]
    exact hptsum
  have hqsum : ∑ z ∈ F.quantizationCodebook ε, F.qApproxAtStop ε z = 1 := by
    have h : ∑' z, F.qApproxAtStop ε z
        = ∑ z ∈ F.quantizationCodebook ε, F.qApproxAtStop ε z := tsum_eq_sum hSq
    rw [← h]
    exact hqtsum
  have hTVeq : qtd_discrete_total_variation (F.qReverseAtStop ε) (F.qApproxAtStop ε)
      = 1 / 2 * ∑ z ∈ F.quantizationCodebook ε,
        |F.qReverseAtStop ε z - F.qApproxAtStop ε z| := by
    rw [qtd_discrete_total_variation,
      tsum_eq_sum (fun z hz => by rw [hSp z hz, hSq z hz]; norm_num)]
  have hKLeq : qtd_discrete_kl (F.qReverseAtStop ε) (F.qApproxAtStop ε)
      = ∑ z ∈ F.quantizationCodebook ε,
        F.qReverseAtStop ε z * Real.log (F.qReverseAtStop ε z / F.qApproxAtStop ε z) := by
    rw [qtd_discrete_kl, tsum_eq_sum (fun z hz => by rw [hSp z hz]; norm_num)]
    refine Finset.sum_congr rfl (fun z hz => ?_)
    rw [if_neg (ne_of_gt (hppos z ((hcb z).mp hz)))]
  have hpin := pinskerFin (F.quantizationCodebook ε) (F.qReverseAtStop ε) (F.qApproxAtStop ε)
    (fun z _ => hpnn z) (fun z hz => hqpos z ((hcb z).mp hz)) hpsum hqsum
  rw [← hKLeq] at hpin
  have hSnn : 0 ≤ ∑ z ∈ F.quantizationCodebook ε,
      |F.qReverseAtStop ε z - F.qApproxAtStop ε z| :=
    Finset.sum_nonneg (fun z _ => abs_nonneg _)
  rw [hTVeq]
  nlinarith [hpin, hkl, hSnn, hεpos]

@[blueprint "lem:qtd-early-stopping-gap"
  (statement := /-- Let $d\in\mathbb N$, and let $F$ be a quantized transition diffusion family satisfying the parameter schedule of \cref{def:qtd-parameter-schedule} and the algorithmic laws of \cref{def:qtd-algorithmic-laws}. Then, for every $\epsilon\in\mathbb R$ with $0<\epsilon<1$, the encoded target law and the exact forward law at the scheduled early-stopping time satisfy
  \[
    \operatorname{TV}_{\mathrm d}
      (q_{*,\epsilon},q^{\to}_{\delta_\epsilon,\epsilon})\le\epsilon.
  \] -/)
  (proof := /-- Fix $\epsilon\in\mathbb R$ with $0<\epsilon<1$, and set $b=d\log_2K_\epsilon$. By \cref{def:qtd-parameter-schedule}, $0<\delta_\epsilon$ and $\delta_\epsilon\le\epsilon/b$. These inequalities and $\epsilon>0$ force $b>0$, so multiplication by $b$ gives $\delta_\epsilon b\le\epsilon$. By the coupling estimate in \cref{def:qtd-algorithmic-laws},
  \[
    \operatorname{TV}_{\mathrm d}(q_{*,\epsilon},q^{\to}_{\delta_\epsilon,\epsilon})
      \le 1-e^{-\delta_\epsilon b}.
  \]
  The exponential tangent inequality $1-x\le e^{-x}$ at $x=\delta_\epsilon b$ yields $1-e^{-\delta_\epsilon b}\le\delta_\epsilon b$. Combining the three inequalities proves the claim. -/)
  (title := /-- Error introduced by early stopping -/)
  (latexEnv := "lemma")]
lemma qtd_early_stopping_gap {d : ℕ} (F : quantized_transition_diffusion_family d)
    (hp : qtd_parameter_schedule F) (hl : qtd_algorithmic_laws F) :
    ∀ ε, qtd_admissible_error ε →
      qtd_discrete_total_variation (F.qStar ε) (F.qForwardAtDelta ε) ≤ ε := by
  intro ε hε
  rcases hp ε hε with ⟨_, _, _, _, _, _, _, _, hδpos, hδle, _⟩
  rcases hl with ⟨_, _, _, _, _, ⟨_, hchain⟩⟩
  rcases hchain ε hε with ⟨_, _, _, htv⟩
  have hdenom_pos : 0 < (d : ℝ) * Real.logb 2 (F.binCount ε) := by
    by_contra hn
    have hdenom_nonpos : (d : ℝ) * Real.logb 2 (F.binCount ε) ≤ 0 :=
      le_of_not_gt hn
    have hquot_nonpos :
        ε / ((d : ℝ) * Real.logb 2 (F.binCount ε)) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos hε.1.le hdenom_nonpos
    exact (not_lt_of_ge hquot_nonpos) (lt_of_lt_of_le hδpos hδle)
  have hprod_le :
      F.earlyStop ε * (d : ℝ) * Real.logb 2 (F.binCount ε) ≤ ε := by
    simpa [mul_assoc] using (le_div_iff₀ hdenom_pos).mp hδle
  have hexp :=
    Real.add_one_le_exp
      (-F.earlyStop ε * (d : ℝ) * Real.logb 2 (F.binCount ε))
  calc
    qtd_discrete_total_variation (F.qStar ε) (F.qForwardAtDelta ε) ≤
        1 - Real.exp
          (-F.earlyStop ε * (d : ℝ) * Real.logb 2 (F.binCount ε)) := htv
    _ ≤ F.earlyStop ε * (d : ℝ) * Real.logb 2 (F.binCount ε) := by
      linarith
    _ ≤ ε := hprod_le

@[blueprint "lem:qtd-discrete-generated-gap"
  (statement := /-- Let $d\in\mathbb N$, and let $F$ satisfy the training assumption, the validated parameter schedule, the algorithmic laws, and the validated reverse-process laws. For every $\epsilon\in(0,1)$, the encoded generated law is within $2\epsilon$ in total variation of the encoded target law. -/)
  (proof := /-- The validated schedule in \cref{def:qtd-validated-parameter-schedule} contains the base schedule required by \cref{lem:qtd-early-stopping-gap}. By time reversal in \cref{def:qtd-algorithmic-laws}, $q^{\leftarrow}_{T-\delta}=q^{\to}_\delta$. Apply the triangle inequality for discrete total variation, using \cref{lem:qtd-early-stopping-gap} for the target-to-forward term and \cref{lem:qtd-pinsker-conversion} for the forward-to-generated term. Their sum is $2\epsilon$. -/)
  (title := /-- Total variation error on the encoded state space -/)
  (latexEnv := "lemma")]
lemma qtd_discrete_generated_gap {d : ℕ} (F : quantized_transition_diffusion_family d)
    (ht : qtd_training_assumption F) (hp : qtd_validated_parameter_schedule F)
    (hl : qtd_algorithmic_laws F) (hr : qtd_validated_reverse_process_laws F) :
    ∀ ε, qtd_admissible_error ε →
      qtd_discrete_total_variation (F.qStar ε) (F.qApproxAtStop ε) ≤ 2 * ε := by
  intro ε hε
  have h1 := qtd_early_stopping_gap F hp.1 hl ε hε
  have h2 := qtd_pinsker_conversion F ht hp hl hr ε hε
  have hrev : ∀ x, F.qReverseAtStop ε x = F.qForwardAtDelta ε x :=
    fun x => hl.2.2.2.2.2.1 ε x hε
  have h2' :
      qtd_discrete_total_variation (F.qForwardAtDelta ε) (F.qApproxAtStop ε) ≤ ε := by
    have hfun : F.qReverseAtStop ε = F.qForwardAtDelta ε := funext hrev
    rwa [hfun] at h2
  obtain ⟨hm1, hm2, _, _, _, hm6⟩ := hl.1 ε hε
  obtain ⟨_, _, _, N1, hN1⟩ := hm1
  obtain ⟨_, _, _, N2, hN2⟩ := hm2
  obtain ⟨_, _, _, N3, hN3⟩ := hm6
  set N : ℕ := max N1 (max N2 N3) with hNdef
  have hz1 : ∀ x, N ≤ x → F.qStar ε x = 0 := by
    intro x hx
    exact hN1 x (le_trans (le_max_left _ _) hx)
  have hz2 : ∀ x, N ≤ x → F.qForwardAtDelta ε x = 0 := by
    intro x hx
    exact hN2 x (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx)
  have hz3 : ∀ x, N ≤ x → F.qApproxAtStop ε x = 0 := by
    intro x hx
    exact hN3 x (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx)
  have hnot : ∀ b : ℕ, b ∉ Finset.range N → N ≤ b := by
    intro b hb
    exact Nat.le_of_not_lt (fun hlt => hb (Finset.mem_range.mpr hlt))
  have e1 : ∑' x : ℕ, |F.qStar ε x - F.qApproxAtStop ε x| =
      ∑ x ∈ Finset.range N, |F.qStar ε x - F.qApproxAtStop ε x| := by
    refine tsum_eq_sum ?_
    intro b hb
    rw [hz1 b (hnot b hb), hz3 b (hnot b hb)]
    simp
  have e2 : ∑' x : ℕ, |F.qStar ε x - F.qForwardAtDelta ε x| =
      ∑ x ∈ Finset.range N, |F.qStar ε x - F.qForwardAtDelta ε x| := by
    refine tsum_eq_sum ?_
    intro b hb
    rw [hz1 b (hnot b hb), hz2 b (hnot b hb)]
    simp
  have e3 : ∑' x : ℕ, |F.qForwardAtDelta ε x - F.qApproxAtStop ε x| =
      ∑ x ∈ Finset.range N, |F.qForwardAtDelta ε x - F.qApproxAtStop ε x| := by
    refine tsum_eq_sum ?_
    intro b hb
    rw [hz2 b (hnot b hb), hz3 b (hnot b hb)]
    simp
  have hsum :
      ∑ x ∈ Finset.range N, |F.qStar ε x - F.qApproxAtStop ε x| ≤
        (∑ x ∈ Finset.range N, |F.qStar ε x - F.qForwardAtDelta ε x|) +
          ∑ x ∈ Finset.range N, |F.qForwardAtDelta ε x - F.qApproxAtStop ε x| := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum ?_
    intro x _
    exact abs_sub_le _ _ _
  rw [qtd_discrete_total_variation] at h1 h2' ⊢
  rw [e1]
  rw [e2] at h1
  rw [e3] at h2'
  linarith

@[blueprint "lem:qtd-encoding-preserves-tv"
  (statement := /-- Let $d\in\mathbb N$, and let $F$ be a quantized transition diffusion family satisfying the algorithmic laws of \cref{def:qtd-algorithmic-laws}. For every $\epsilon\in\mathbb R$ with $0<\epsilon<1$, decoding the exact and approximate encoded laws into their piecewise-uniform continuous laws preserves total variation:
  \[
    \operatorname{TV}(\overline p_{*,\epsilon},\widehat p_\epsilon)
      =\operatorname{TV}_{\mathrm d}(q_{*,\epsilon},\widehat q_{T-\delta,\epsilon}).
  \] -/)
  (proof := /-- Fix $\epsilon\in\mathbb R$ with $0<\epsilon<1$. By \cref{def:qtd-algorithmic-laws}, $q_{*,\epsilon}$ and $\widehat q_{T-\delta,\epsilon}$ are probability masses, while $\overline p_{*,\epsilon}$ and $\widehat p_\epsilon$ are their respective decodings. Applying the total-variation preservation clause of the same definition to these two masses and substituting the decoding identities yields the asserted equality. -/)
  (title := /-- Preservation of total variation under decoding -/)
  (latexEnv := "lemma")]
lemma qtd_encoding_preserves_tv {d : ℕ} (F : quantized_transition_diffusion_family d)
    (hl : qtd_algorithmic_laws F) :
    ∀ ε, qtd_admissible_error ε →
      qtd_total_variation (F.pBar ε) (F.pHat ε) =
        qtd_discrete_total_variation (F.qStar ε) (F.qApproxAtStop ε) := by
  intro ε hε
  rcases hl with ⟨hmass, _, hdecode, _, htv, _⟩
  rcases hmass ε hε with ⟨hqs, _, _, _, _, hqa⟩
  rcases hdecode ε hε with ⟨_, _, _, _, _, _, _, hpBar, hpHat⟩
  rw [hpBar, hpHat]
  exact htv ε (F.qStar ε) (F.qApproxAtStop ε) hε hqs hqa

@[blueprint "lem:qtd-quantized-generated-gap"
  (statement := /-- Let $d\in\mathbb N$, and let $F$ satisfy the training assumption, the validated parameter schedule, the algorithmic laws, and the validated reverse-process laws. For every $\epsilon\in(0,1)$, the histogram law and the generated continuous law are within $2\epsilon$ in total variation. -/)
  (proof := /-- The encoded estimate of \cref{lem:qtd-discrete-generated-gap} is transferred to the decoded continuous laws by \cref{lem:qtd-encoding-preserves-tv}. -/)
  (title := /-- Error between histogram and generated laws -/)
  (latexEnv := "lemma")]
lemma qtd_quantized_generated_gap {d : ℕ} (F : quantized_transition_diffusion_family d)
    (ht : qtd_training_assumption F) (hp : qtd_validated_parameter_schedule F)
    (hl : qtd_algorithmic_laws F) (hr : qtd_validated_reverse_process_laws F) :
    ∀ ε, qtd_admissible_error ε →
      qtd_total_variation (F.pBar ε) (F.pHat ε) ≤ 2 * ε := by
  intro ε hε
  rw [qtd_encoding_preserves_tv F hl ε hε]
  exact qtd_discrete_generated_gap F ht hp hl hr ε hε

@[blueprint "lem:qtd-final-total-variation"
  (statement := /-- Let $d\in\mathbb N$, and let $F$ satisfy assumptions A1--A4, the validated parameter schedule, the algorithmic laws, and the validated reverse-process laws. For every $\epsilon\in(0,1)$, the generated law satisfies
  \[
    \operatorname{TV}(p_*,\widehat p)\le5\epsilon.
  \] -/)
  (proof := /-- The validated schedule in \cref{def:qtd-validated-parameter-schedule} contains the base schedule required by \cref{lem:qtd-quantization-gap}. Apply the triangle inequality for total variation through the histogram law. The first term is at most $3\epsilon$ by \cref{lem:qtd-quantization-gap}, and the second is at most $2\epsilon$ by \cref{lem:qtd-quantized-generated-gap}. Adding the bounds gives $5\epsilon$. -/)
  (title := /-- Final total variation guarantee -/)
  (latexEnv := "lemma")]
lemma qtd_final_total_variation {d : ℕ} (F : quantized_transition_diffusion_family d)
    (ha : qtd_analytic_assumptions F) (ht : qtd_training_assumption F)
    (hp : qtd_validated_parameter_schedule F) (hl : qtd_algorithmic_laws F)
    (hr : qtd_validated_reverse_process_laws F) :
    ∀ ε, qtd_admissible_error ε →
      qtd_total_variation F.pStar (F.pHat ε) ≤ 5 * ε := by
  intro ε hε
  have hbdd : ∀ μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      BddAbove {r : ℝ | ∃ s : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet s ∧
        r = |(μ : Measure (EuclideanSpace ℝ (Fin d))).real s -
          (ν : Measure (EuclideanSpace ℝ (Fin d))).real s|} := by
    intro μ ν
    refine ⟨1, ?_⟩
    rintro r ⟨s, _, rfl⟩
    have h1 : (μ : Measure (EuclideanSpace ℝ (Fin d))).real s ≤ 1 :=
      measureReal_le_one
    have h2 : (ν : Measure (EuclideanSpace ℝ (Fin d))).real s ≤ 1 :=
      measureReal_le_one
    have h3 : 0 ≤ (μ : Measure (EuclideanSpace ℝ (Fin d))).real s :=
      measureReal_nonneg
    have h4 : 0 ≤ (ν : Measure (EuclideanSpace ℝ (Fin d))).real s :=
      measureReal_nonneg
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hle : ∀ (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
      (s : Set (EuclideanSpace ℝ (Fin d))), MeasurableSet s →
      |(μ : Measure (EuclideanSpace ℝ (Fin d))).real s -
        (ν : Measure (EuclideanSpace ℝ (Fin d))).real s| ≤
        qtd_total_variation μ ν := by
    intro μ ν s hs
    exact le_csSup (hbdd μ ν) ⟨s, hs, rfl⟩
  have h1 := qtd_quantization_gap F ha hp.1 hl ε hε
  have h2 := qtd_quantized_generated_gap F ht hp hl hr ε hε
  refine csSup_le ⟨0, ∅, MeasurableSet.empty, by simp⟩ ?_
  rintro r ⟨s, hs, rfl⟩
  have hA := hle F.pStar (F.pBar ε) s hs
  have hB := hle (F.pBar ε) (F.pHat ε) s hs
  have hC :
      |(F.pStar : Measure (EuclideanSpace ℝ (Fin d))).real s -
        (F.pHat ε : Measure (EuclideanSpace ℝ (Fin d))).real s| ≤
      |(F.pStar : Measure (EuclideanSpace ℝ (Fin d))).real s -
        (F.pBar ε : Measure (EuclideanSpace ℝ (Fin d))).real s| +
      |(F.pBar ε : Measure (EuclideanSpace ℝ (Fin d))).real s -
        (F.pHat ε : Measure (EuclideanSpace ℝ (Fin d))).real s| :=
    abs_sub_le _ _ _
  linarith

@[blueprint "thm:main-thm"
  (statement := /-- Let $d$ be a positive natural number, and let $p_*\propto e^{-f_*}$ be a target law on $\mathbb R^d$ satisfying assumptions A1--A3 together with the stated whole-space score integration-by-parts and cellwise $L^1$ Poincaré estimates. Suppose that the trained discrete score satisfies A4. For every $\epsilon\in(0,1)$, require the data-quantization algorithm to partition the radius-$L$ cube into pairwise disjoint axis-aligned cells of width $l$, assign to each code the corresponding conditional $p_*$-mass, and decode every encoded law by distributing its code masses uniformly with respect to Lebesgue measure on those same cells. Thus $\overline p_{*,\epsilon}$ is the piecewise-uniform histogram determined by $p_*$, rather than an arbitrary decoding of its encoded mass. Let the exact forward and reverse laws be the marginals of the unit-rate Hamming-neighbor hypercube CTMC, let the learned reverse law be generated from that trained score and simulated by truncated uniformization, and let $\widehat p_\epsilon$ be the same cellwise-uniform decoding of its terminal law. Choose
  \[
  L=\sigma\sqrt{2\log(2d/\epsilon)},\qquad
  l=\frac{\epsilon}{2H\bigl(\sigma\sqrt{2d\log(2d/\epsilon)}+d+\sqrt{dm_0}\bigr)},
  \qquad K=\frac{2L}{l},
  \]
  put $B=d\log_2K$, require $B\ge1$ and
  $\epsilon_{\mathrm{score}}\le\epsilon/\max\{1,T\}$, and use the stated reverse-time partition and rates, where
  \[
    T=\log(d/\epsilon)+\log\log_2K,
    \qquad
    \frac{2\epsilon}{3d\log_2K}<\delta
      \le\frac{\epsilon}{d\log_2K}.
  \]
  The lower bound on $\delta$ requires the terminal grid index to be the first index satisfying the displayed upper bound. Assume, moreover, the tensorized two-state entropy-dissipation inequality
  \[
    \frac{\mathrm d}{\mathrm dt}
      D_{\mathrm{KL}}(q_t^{\to}\Vert\widehat q_0)
      \le-2D_{\mathrm{KL}}(q_t^{\to}\Vert\widehat q_0)
  \]
  for the unit-rate Hamming chain.
  Then the expected iteration and score-estimation complexity is $O(d\log^2(d/\epsilon))$ as $\epsilon\downarrow0$, and the generated law $\widehat p_\epsilon$ satisfies $\operatorname{TV}(p_*,\widehat p_\epsilon)\le5\epsilon$ for every admissible $\epsilon$. -/)
  (proof := /-- The asymptotic complexity assertion is \cref{lem:qtd-complexity-order}. The accuracy assertion is \cref{lem:qtd-final-total-variation}. Taking these two conclusions together proves the theorem. -/)
  (title := /-- Main convergence and complexity theorem for quantized transition diffusion -/)
  (latexEnv := "theorem")]
theorem main_thm {d : ℕ} (F : quantized_transition_diffusion_family d)
    (hd : 0 < d)
    (ha : qtd_analytic_assumptions F) (ht : qtd_training_assumption F)
    (hp : qtd_validated_parameter_schedule F) (hl : qtd_algorithmic_laws F)
    (hr : qtd_validated_reverse_process_laws F) :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0))
        (qtd_expected_iterations F) (qtd_complexity_scale d) ∧
      ∀ ε, qtd_admissible_error ε →
        qtd_total_variation F.pStar (F.pHat ε) ≤ 5 * ε := by
  exact ⟨qtd_complexity_order F hp, qtd_final_total_variation F ha ht hp hl hr⟩

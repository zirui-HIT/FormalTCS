import Architect
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.Basic

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:hellinger-density"
  (statement := /-- Let $(\Omega,\mathcal A,\mu)$ be a measure space. A Hellinger density consists of a measurable nonnegative function $p:\Omega\to\mathbb R$, together with the probability measure having Radon--Nikodym density $p$ with respect to $\mu$. -/)
  (title := /-- Densities on a common measure space -/)
  (latexEnv := "definition")]
structure hellinger_density (Ω : Type*) [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) where
  toProbabilityMeasure : MeasureTheory.ProbabilityMeasure Ω
  val : Ω → ℝ
  nonnegative : ∀ x, 0 ≤ val x
  measurable_val : Measurable val
  measure_eq_withDensity :
    (toProbabilityMeasure : MeasureTheory.Measure Ω) =
      μ.withDensity (fun x => ENNReal.ofReal (val x))

@[blueprint "def:squared-hellinger"
  (statement := /-- For two densities $p$ and $q$ relative to the same measure $\mu$, define their squared Hellinger distance by
  \[
    H^2(p,q)=\frac12\int_\Omega(\sqrt{p}-\sqrt{q})^2\,d\mu.
  \] -/)
  (title := /-- Squared Hellinger distance -/)
  (latexEnv := "definition")]
noncomputable def squared_hellinger {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} (p q : hellinger_density Ω μ) : ℝ :=
  (2 : ℝ)⁻¹ *
    MeasureTheory.integral μ
      (fun x => (Real.sqrt (p.val x) - Real.sqrt (q.val x)) ^ (2 : ℕ))

@[blueprint "def:concept-class"
  (statement := /-- A Boolean concept class on a type $\Omega$ is a set of functions from $\Omega$ to $\mathrm{Bool}$. -/)
  (title := /-- Boolean concept classes -/)
  (latexEnv := "definition")]
abbrev concept_class (Ω : Type*) :=
  Set (Ω → Bool)

@[blueprint "def:set-shatters"
  (statement := /-- A Boolean concept class $\mathcal H$ shatters a set $W\subseteq\Omega$ if every subset $W'\subseteq W$ is the trace on $W$ of the true set of some concept in $\mathcal H$. -/)
  (title := /-- Shattering of a set -/)
  (latexEnv := "definition")]
def set_shatters {Ω : Type*} (H : concept_class Ω) (W : Set Ω) : Prop :=
  ∀ W' ⊆ W, ∃ h ∈ H, h ⁻¹' {true} ∩ W = W'

@[blueprint "def:concept-event"
  (statement := /-- The event represented by a Boolean concept $h:\Omega\to\mathrm{Bool}$ is the set of points on which $h$ takes the value $\mathrm{true}$. -/)
  (title := /-- Event associated with a Boolean concept -/)
  (latexEnv := "definition")]
def concept_event {Ω : Type*} (h : Ω → Bool) : Set Ω :=
  {x | h x = true}

@[blueprint "def:ratio-concept-class"
  (statement := /-- For a family $\mathcal F$ of densities, its ratio class consists of all Boolean concepts of the form
  \[
    x\longmapsto \mathbf 1\{p(x)\geq \tau q(x)\},
    \qquad p,q\in\mathcal F,\quad \tau\in\mathbb R.
  \]
  This cross-multiplied formulation also specifies the concept when $q(x)=0$. -/)
  (title := /-- Ratio class of a density family -/)
  (latexEnv := "definition")]
def ratio_concept_class {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} (F : Set (hellinger_density Ω μ)) :
    concept_class Ω :=
  {h | ∃ p ∈ F, ∃ q ∈ F, ∃ τ : ℝ,
    h = fun x => decide (τ * q.val x ≤ p.val x)}

@[blueprint "def:modified-hellinger-distance"
  (statement := /-- Given a Boolean concept class $\mathcal H$ and finite measures $P,Q$, define
  \[
    d_{\mathcal H}(P,Q)
      =\sup_{h\in\mathcal H}\frac12
        \bigl(\sqrt{P[h]}-\sqrt{Q[h]}\bigr)^2.
  \] -/)
  (title := /-- Modified Hellinger distance over a concept class -/)
  (latexEnv := "definition")]
noncomputable def modified_hellinger_distance {Ω : Type*} [MeasurableSpace Ω]
    (H : concept_class Ω)
    (P Q : MeasureTheory.Measure Ω) : ℝ :=
  sSup {r : ℝ | ∃ h ∈ H,
    r = (2 : ℝ)⁻¹ *
      (Real.sqrt (P.real (concept_event h)) -
        Real.sqrt (Q.real (concept_event h))) ^ (2 : ℕ)}

@[blueprint "def:empirical-measure"
  (statement := /-- For a sample $x=(x_1,\ldots,x_n)$, its empirical measure is
  \[
    P_x=\frac1n\sum_{i=1}^n\delta_{x_i}.
  \] -/)
  (title := /-- Empirical measure -/)
  (latexEnv := "definition")]
noncomputable def empirical_measure {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (x : Fin n → Ω) : MeasureTheory.Measure Ω :=
  (n : ENNReal)⁻¹ • (∑ i : Fin n, MeasureTheory.Measure.dirac (x i))

@[blueprint "def:is-approximate-minimum-distance-estimator"
  (statement := /-- Let $\mathcal F$ be a density family, let $\mathcal H$ be a concept class, and let $\varepsilon\geq0$. A map $\widehat f$ from samples of size $n$ to densities is an $\varepsilon$-approximate minimum-distance estimator if $\widehat f(x)\in\mathcal F$ and
  \[
    d_{\mathcal H}(P_x,\widehat f(x))
      \leq d_{\mathcal H}(P_x,g)+\varepsilon
  \]
  for every $g\in\mathcal F$ and every sample $x$. -/)
  (title := /-- Approximate minimum-distance estimator -/)
  (latexEnv := "definition")]
def is_approximate_minimum_distance_estimator {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} (n : ℕ)
    (H : concept_class Ω)
    (F : Set (hellinger_density Ω μ))
    (ε : ℝ) (hat : (Fin n → Ω) → hellinger_density Ω μ) : Prop :=
  0 ≤ ε ∧ ∀ x, hat x ∈ F ∧ ∀ g ∈ F,
    modified_hellinger_distance H (empirical_measure n x)
        (hat x).toProbabilityMeasure ≤
      modified_hellinger_distance H (empirical_measure n x)
        g.toProbabilityMeasure + ε

@[blueprint "def:is-minimum-distance-estimator"
  (statement := /-- Let $\mathcal F$ be a density family and $\mathcal H$ a concept class. An exact minimum-distance estimator is a $0$-approximate minimum-distance estimator in the sense of \cref{def:is-approximate-minimum-distance-estimator}. Thus its empirical objective is no larger than that of any $g\in\mathcal F$ on every sample. -/)
  (title := /-- Exact minimum-distance estimator -/)
  (latexEnv := "definition")]
def is_minimum_distance_estimator {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} (n : ℕ)
    (H : concept_class Ω)
    (F : Set (hellinger_density Ω μ))
    (hat : (Fin n → Ω) → hellinger_density Ω μ) : Prop :=
  is_approximate_minimum_distance_estimator n H F 0 hat

@[blueprint "def:shattered-cardinalities"
  (statement := /-- For a Boolean concept class $\mathcal H$, let $S(\mathcal H)$ be the set of cardinalities of finite subsets of $\Omega$ shattered by $\mathcal H$. -/)
  (title := /-- Cardinalities shattered by a concept class -/)
  (latexEnv := "definition")]
def shattered_cardinalities {Ω : Type*}
    (H : concept_class Ω) : Set ℕ :=
  {m | ∃ W : Finset Ω, W.card = m ∧
    set_shatters H (W : Set Ω)}

@[blueprint "def:has-vc-dimension"
  (statement := /-- A Boolean concept class $\mathcal H$ has VC dimension $d$ if its shattered cardinalities are bounded above and their supremum is $d$. -/)
  (title := /-- Exact VC dimension -/)
  (latexEnv := "definition")]
def has_vc_dimension {Ω : Type*}
    (H : concept_class Ω) (d : ℕ) : Prop :=
  BddAbove (shattered_cardinalities H) ∧
    sSup (shattered_cardinalities H) = d

@[blueprint "def:binary-logarithm"
  (statement := /-- Define the base-two logarithm by $\log_2 x=\log x/\log 2$, using the total real logarithm supplied by Lean. -/)
  (title := /-- Binary logarithm -/)
  (latexEnv := "definition")]
noncomputable def binary_logarithm (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

@[blueprint "def:entropy-envelope"
  (statement := /-- Define
  \[
    z(x)=x-x\log x=x+\operatorname{negMulLog}(x).
  \]
  Thus $z(x)=x\log(e/x)$ for $x>0$, while $z(0)=0$ is the continuous-extension convention. -/)
  (title := /-- Entropy envelope -/)
  (latexEnv := "definition")]
noncomputable def entropy_envelope (x : ℝ) : ℝ :=
  x + Real.negMulLog x

@[blueprint "def:hellinger-log-penalty"
  (statement := /-- Define the target approximation penalty
  \[
    \Phi(x)=x\log_2(2/x).
  \]
  Lean's total division and logarithm give $\Phi(0)=0$. -/)
  (title := /-- Logarithmically weighted Hellinger loss -/)
  (latexEnv := "definition")]
noncomputable def hellinger_log_penalty (x : ℝ) : ℝ :=
  x * binary_logarithm (2 / x)

@[blueprint "def:best-approximation-penalty"
  (statement := /-- For a target density $f$ and model $\mathcal F$, define the logarithmically weighted best approximation error by
  \[
    \inf_{g\in\mathcal F}\Phi\bigl(H^2(f,g)\bigr).
  \] -/)
  (title := /-- Best logarithmically weighted model approximation -/)
  (latexEnv := "definition")]
noncomputable def best_approximation_penalty {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} (f : hellinger_density Ω μ)
    (F : Set (hellinger_density Ω μ)) : ℝ :=
  sInf {r : ℝ | ∃ g ∈ F,
    r = hellinger_log_penalty (squared_hellinger f g)}

@[blueprint "def:uniform-convergence-radius"
  (statement := /-- For $n\geq2$, VC dimension $d$, and failure probability $\delta$, define the radius
  \[
    R(n,d,\delta)=
      \frac{32\bigl(d\log(2n+1)+\log(8/\delta)\bigr)}{n}
  \]
  appearing in the source's second-order uniform-convergence estimate. -/)
  (title := /-- Second-order uniform-convergence radius -/)
  (latexEnv := "definition")]
noncomputable def uniform_convergence_radius (n d : ℕ) (δ : ℝ) : ℝ :=
  32 * ((d : ℝ) * Real.log (2 * (n : ℝ) + 1) + Real.log (8 / δ)) /
    (n : ℝ)

@[blueprint "def:source-complexity-term"
  (statement := /-- Define the natural-logarithm complexity expression used in the last displayed calculation of the source proof:
  \[
    \frac{\bigl(d\log(2n+1)+\log(8/\delta)\bigr)\log n}{n}.
  \] -/)
  (title := /-- Source-form complexity term -/)
  (latexEnv := "definition")]
noncomputable def source_complexity_term (n d : ℕ) (δ : ℝ) : ℝ :=
  (((d : ℝ) * Real.log (2 * (n : ℝ) + 1) + Real.log (8 / δ)) *
    Real.log n) / (n : ℝ)

@[blueprint "def:vc-complexity-term"
  (statement := /-- Define the complexity term in the target theorem:
  \[
    \frac{\bigl(d\log_2 n+\log_2(2/\delta)\bigr)\log_2 n}{n}.
  \] -/)
  (title := /-- VC complexity term in the target scale -/)
  (latexEnv := "definition")]
noncomputable def vc_complexity_term (n d : ℕ) (δ : ℝ) : ℝ :=
  (((d : ℝ) * binary_logarithm n + binary_logarithm (2 / δ)) *
    binary_logarithm n) / (n : ℝ)

@[blueprint "def:iid-sample-law"
  (statement := /-- The law of $n$ independent observations from a density $f$ is the finite product of the probability measure represented by $f$. -/)
  (title := /-- Law of an i.i.d. sample -/)
  (latexEnv := "definition")]
noncomputable def iid_sample_law {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {n : ℕ} (f : hellinger_density Ω μ) :
    MeasureTheory.Measure (Fin n → Ω) :=
  (MeasureTheory.ProbabilityMeasure.pi
    (fun _ : Fin n => f.toProbabilityMeasure)).toMeasure

@[blueprint "def:is-atomless-measure"
  (statement := /-- A measure $\nu$ on $(\Omega,\mathcal A)$ is atomless if every measurable set of positive $\nu$-measure contains a measurable subset whose measure is strictly positive and strictly smaller. Equivalently, no measurable set of positive measure is a measure-theoretic atom. -/)
  (title := /-- Atomless measures -/)
  (latexEnv := "definition")]
def is_atomless_measure {Ω : Type*} [MeasurableSpace Ω]
    (ν : MeasureTheory.Measure Ω) : Prop :=
  ∀ s : Set Ω, MeasurableSet s → 0 < ν s →
    ∃ t : Set Ω, t ⊆ s ∧ MeasurableSet t ∧ 0 < ν t ∧ ν t < ν s

@[blueprint "lem:density-measure-univ"
  (statement := /-- Let $(\Omega,\mathcal A)$ be a measurable space, let $\mu$ be a measure on it, and let $p$ be a Hellinger density relative to $\mu$. Then the probability measure represented by $p$ assigns mass one to $\Omega$. -/)
  (proof := /-- By \cref{def:hellinger-density}, $p$ carries a probability measure $p.\mathrm{toProbabilityMeasure}$. The defining normalization property of a probability measure states that its mass on $\Omega$ is one. -/)
  (title := /-- A density represents a probability measure -/)
  (latexEnv := "lemma")]
lemma density_measure_univ {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} (p : hellinger_density Ω μ) :
    (p.toProbabilityMeasure : MeasureTheory.Measure Ω) Set.univ = 1 := by
  exact p.toProbabilityMeasure.prop.measure_univ

@[blueprint "lem:empirical-measure-univ"
  (statement := /-- Let $\Omega$ be a measurable space, let $n\in\mathbb N$ satisfy $n>0$, and let $x\colon\operatorname{Fin}(n)\to\Omega$. Then the empirical measure of $x$ assigns mass one to $\Omega$. -/)
  (proof := /-- Expand \cref{def:empirical-measure}. Each Dirac measure has mass one on the full space, the finite sum has mass $n$, and multiplication by $n^{-1}$ gives one because $n>0$. -/)
  (title := /-- The empirical measure is a probability measure -/)
  (latexEnv := "lemma")]
lemma empirical_measure_univ {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (x : Fin n → Ω) :
    empirical_measure n x Set.univ = 1 := by
  simp [empirical_measure, ENNReal.inv_mul_cancel, hn.ne']

@[blueprint "lem:squared-hellinger-range"
  (statement := /-- Let $(\Omega,\mathcal A)$ be a measurable space, let $\mu$ be a
  measure on $\Omega$, and let $p,q$ be Hellinger densities relative to $\mu$. Then
  \[
    0\leq H^2(p,q)\leq1.
  \] -/)
  (proof := /-- The measure identity in \cref{def:hellinger-density} and the
  unit-mass identity in \cref{lem:density-measure-univ} show that each density
  has lower integral one. Thus both densities are integrable and have ordinary
  integral one. The integrand in \cref{def:squared-hellinger} is nonnegative.
  Moreover, nonnegativity of the square roots and the identities
  $(\sqrt{p})^2=p$ and $(\sqrt{q})^2=q$ give the pointwise bound
  $(\sqrt p-\sqrt q)^2\leq p+q$. Monotonicity and additivity of the integral
  therefore yield
  \[
    0\leq H^2(p,q)\leq\frac12\int_\Omega(p+q)\,d\mu=1.
  \] -/)
  (title := /-- Range of squared Hellinger distance -/)
  (latexEnv := "lemma")]
lemma squared_hellinger_range {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} (p q : hellinger_density Ω μ) :
    0 ≤ squared_hellinger p q ∧ squared_hellinger p q ≤ 1 := by
  have density_lintegral_eq_one (r : hellinger_density Ω μ) :
      ∫⁻ x, ENNReal.ofReal (r.val x) ∂μ = 1 := by
    have hmass :
        μ.withDensity (fun x => ENNReal.ofReal (r.val x)) Set.univ = 1 := by
      rw [← r.measure_eq_withDensity]
      exact density_measure_univ r
    rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ] at hmass
    simpa only [MeasureTheory.Measure.restrict_univ] using hmass
  have density_integrable (r : hellinger_density Ω μ) :
      MeasureTheory.Integrable r.val μ := by
    exact
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
        r.measurable_val.aestronglyMeasurable
        (Filter.Eventually.of_forall r.nonnegative)).mp (by
          rw [density_lintegral_eq_one r]
          norm_num)
  have density_integral_eq_one (r : hellinger_density Ω μ) :
      ∫ x, r.val x ∂μ = 1 := by
    rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall r.nonnegative)
      r.measurable_val.aestronglyMeasurable,
      density_lintegral_eq_one r]
    norm_num
  unfold squared_hellinger
  constructor
  · exact mul_nonneg (by norm_num)
      (MeasureTheory.integral_nonneg fun x => sq_nonneg
        (Real.sqrt (p.val x) - Real.sqrt (q.val x)))
  · have hpoint :
        ∀ x, (Real.sqrt (p.val x) - Real.sqrt (q.val x)) ^ (2 : ℕ) ≤
          p.val x + q.val x := by
      intro x
      nlinarith [Real.sq_sqrt (p.nonnegative x),
        Real.sq_sqrt (q.nonnegative x),
        mul_nonneg (Real.sqrt_nonneg (p.val x)) (Real.sqrt_nonneg (q.val x))]
    have hint :
        ∫ x, (Real.sqrt (p.val x) - Real.sqrt (q.val x)) ^ (2 : ℕ) ∂μ ≤
          ∫ x, (p.val x + q.val x) ∂μ := by
      exact MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun x => sq_nonneg
          (Real.sqrt (p.val x) - Real.sqrt (q.val x)))
        ((density_integrable p).add (density_integrable q))
        (Filter.Eventually.of_forall hpoint)
    calc
      (2 : ℝ)⁻¹ *
            ∫ x, (Real.sqrt (p.val x) - Real.sqrt (q.val x)) ^ (2 : ℕ) ∂μ ≤
          (2 : ℝ)⁻¹ * ∫ x, (p.val x + q.val x) ∂μ :=
        mul_le_mul_of_nonneg_left hint (by norm_num)
      _ = 1 := by
        rw [MeasureTheory.integral_add (density_integrable p) (density_integrable q),
          density_integral_eq_one p, density_integral_eq_one q]
        norm_num

@[blueprint "lem:hellinger-density-integrable"
  (statement := /-- Let $(\Omega,\mathcal A)$ be a measurable space, let $\mu$ be a measure on $\Omega$, and let $p$ be a probability density relative to $\mu$. Then the real-valued density function $p$ is integrable with respect to $\mu$. -/)
  (proof := /-- By \cref{lem:density-measure-univ}, the probability measure represented by $p$ has total mass one. The measure identity in \cref{def:hellinger-density}, together with the formula for a measure defined by a density, therefore identifies the lower integral of $\operatorname{ofReal}(p)$ with one. This lower integral is finite, and the measurability and nonnegativity fields in \cref{def:hellinger-density} yield the asserted integrability. -/)
  (title := /-- Integrability of a Hellinger density -/)
  (latexEnv := "lemma")]
lemma hellinger_density_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} (p : hellinger_density Ω μ) :
    MeasureTheory.Integrable p.val μ := by
  have hmass :
      μ.withDensity (fun x => ENNReal.ofReal (p.val x)) Set.univ = 1 := by
    rw [← p.measure_eq_withDensity]
    exact density_measure_univ p
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ] at hmass
  simp only [MeasureTheory.Measure.restrict_univ] at hmass
  exact
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      p.measurable_val.aestronglyMeasurable
      (Filter.Eventually.of_forall p.nonnegative)).mp (by
        rw [hmass]
        norm_num)

@[blueprint "lem:hellinger-sqrt-sqdiff-integrable"
  (statement := /-- Let $(\Omega,\mathcal A)$ be a measurable space, let $\mu$ be a measure on $\Omega$, and let $p,q$ be probability densities relative to $\mu$. Then the function
  \[
    x\longmapsto\bigl(\sqrt{p(x)}-\sqrt{q(x)}\bigr)^2
  \]
  is integrable with respect to $\mu$. -/)
  (proof := /-- By \cref{lem:hellinger-density-integrable}, both $p$ and $q$ are integrable. The displayed function is measurable and nonnegative. Moreover, the identities $(\sqrt p)^2=p$ and $(\sqrt q)^2=q$, together with the nonnegativity of $(\sqrt p+\sqrt q)^2$, give the pointwise bound
  \[
    \left|\bigl(\sqrt p-\sqrt q\bigr)^2\right|\leq 2(p+q).
  \]
  The right-hand side is integrable, so domination proves the claim. -/)
  (title := /-- Integrability of squared square-root differences -/)
  (latexEnv := "lemma")]
lemma hellinger_sqrt_sqdiff_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} (p q : hellinger_density Ω μ) :
    MeasureTheory.Integrable
      (fun x => (Real.sqrt (p.val x) - Real.sqrt (q.val x)) ^ (2 : ℕ)) μ := by
  refine
    (((hellinger_density_integrable p).add
      (hellinger_density_integrable q)).const_mul 2).mono' ?_ ?_
  · exact
      ((p.measurable_val.sqrt.sub q.measurable_val.sqrt).pow_const 2).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (Real.sqrt (p.val x) - Real.sqrt (q.val x)) ^ 2 ≤
      2 * (p.val x + q.val x)
    nlinarith [Real.sq_sqrt (p.nonnegative x),
      Real.sq_sqrt (q.nonnegative x),
      sq_nonneg (Real.sqrt (p.val x) + Real.sqrt (q.val x))]

@[blueprint "lem:squared-hellinger-approx-triangle"
  (statement := /-- Let $(\Omega,\mathcal A)$ be a measurable space, let $\mu$ be a measure on $\Omega$, and let $p,q,r$ be probability densities relative to $\mu$. Then
  \[
    H^2(p,r)\leq2\bigl(H^2(p,q)+H^2(q,r)\bigr).
  \] -/)
  (proof := /-- By \cref{lem:hellinger-sqrt-sqdiff-integrable}, all three squared square-root differences below are integrable. Pointwise, write $\sqrt p-\sqrt r=(\sqrt p-\sqrt q)+(\sqrt q-\sqrt r)$ and apply $(a+b)^2\leq2(a^2+b^2)$. Integrating this inequality, using additivity and homogeneity of the integral, and then applying \cref{def:squared-hellinger} proves the claim. -/)
  (title := /-- Approximate triangle inequality for squared Hellinger distance -/)
  (latexEnv := "lemma")]
lemma squared_hellinger_approx_triangle {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} (p q r : hellinger_density Ω μ) :
    squared_hellinger p r ≤
      2 * (squared_hellinger p q + squared_hellinger q r) := by
  have hpq := hellinger_sqrt_sqdiff_integrable p q
  have hqr := hellinger_sqrt_sqdiff_integrable q r
  have hpr := hellinger_sqrt_sqdiff_integrable p r
  have hpoint : ∀ x,
      (Real.sqrt (p.val x) - Real.sqrt (r.val x)) ^ (2 : ℕ) ≤
        2 * ((Real.sqrt (p.val x) - Real.sqrt (q.val x)) ^ (2 : ℕ) +
          (Real.sqrt (q.val x) - Real.sqrt (r.val x)) ^ (2 : ℕ)) := by
    intro x
    nlinarith [sq_nonneg
      ((Real.sqrt (p.val x) - Real.sqrt (q.val x)) -
        (Real.sqrt (q.val x) - Real.sqrt (r.val x)))]
  have hi :=
    MeasureTheory.integral_mono hpr ((hpq.add hqr).const_mul 2) hpoint
  change
    (∫ x, (Real.sqrt (p.val x) - Real.sqrt (r.val x)) ^ (2 : ℕ) ∂μ) ≤
      ∫ x, 2 * ((Real.sqrt (p.val x) - Real.sqrt (q.val x)) ^ (2 : ℕ) +
        (Real.sqrt (q.val x) - Real.sqrt (r.val x)) ^ (2 : ℕ)) ∂μ at hi
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add hpq hqr] at hi
  unfold squared_hellinger
  nlinarith

@[blueprint "lem:modified-hellinger-symm"
  (statement := /-- For every measurable space $\Omega$, every Boolean concept class
  $\mathcal H$ on $\Omega$, and all measures $P,Q$ on $\Omega$,
  \[
    d_{\mathcal H}(P,Q)=d_{\mathcal H}(Q,P).
  \] -/)
  (proof := /-- Unfold \cref{def:modified-hellinger-distance}. For every
  $h\in\mathcal H$, interchanging $P$ and $Q$ negates the difference of square
  roots, and $(a-b)^2=(b-a)^2$. Thus a real number belongs to the set whose
  supremum defines $d_{\mathcal H}(P,Q)$ if and only if it belongs to the
  corresponding set for $d_{\mathcal H}(Q,P)$. The sets, and hence their
  suprema, are equal. -/)
  (title := /-- Symmetry of the modified distance -/)
  (latexEnv := "lemma")]
lemma modified_hellinger_symm {Ω : Type*} [MeasurableSpace Ω]
    (H : concept_class Ω)
    (P Q : MeasureTheory.Measure Ω) :
    modified_hellinger_distance H P Q =
      modified_hellinger_distance H Q P := by
  unfold modified_hellinger_distance
  congr 1
  ext r
  constructor <;> rintro ⟨h, hh, rfl⟩ <;>
    refine ⟨h, hh, ?_⟩ <;> ring

@[blueprint "lem:modified-hellinger-range"
  (statement := /-- Let $\Omega$ be a measurable space, let $\mathcal H$ be a Boolean concept class on $\Omega$, and let $P$ and $Q$ be measures on $\Omega$ satisfying $P(\Omega)=Q(\Omega)=1$. Then
  \[
    0\leq d_{\mathcal H}(P,Q)\leq1
  \]. -/)
  (proof := /-- If $\mathcal H$ is empty, then the set in \cref{def:modified-hellinger-distance} is empty and its real supremum is zero. Suppose that $\mathcal H$ is nonempty. For every $h\in\mathcal H$, monotonicity of $P$ and $Q$, together with $P(\Omega)=Q(\Omega)=1$, gives $0\leq P[h],Q[h]\leq1$. Thus both square roots belong to $[0,1]$, so their difference has absolute value at most one. Consequently
  \[
    0\leq \frac12\bigl(\sqrt{P[h]}-\sqrt{Q[h]}\bigr)^2\leq\frac12.
  \]
  The set of these terms is nonempty and bounded above. Its supremum is therefore nonnegative and at most $1/2$, and hence at most one. -/)
  (title := /-- Range of the modified distance -/)
  (latexEnv := "lemma")]
lemma modified_hellinger_range {Ω : Type*} [MeasurableSpace Ω]
    (H : concept_class Ω)
    (P Q : MeasureTheory.Measure Ω)
    (hP : P Set.univ = 1) (hQ : Q Set.univ = 1) :
    0 ≤ modified_hellinger_distance H P Q ∧
      modified_hellinger_distance H P Q ≤ 1 := by
  by_cases hH : H.Nonempty
  · rw [modified_hellinger_distance]
    have hterm (h : Ω → Bool) :
        0 ≤ (2 : ℝ)⁻¹ *
            (Real.sqrt (P.real (concept_event h)) -
              Real.sqrt (Q.real (concept_event h))) ^ (2 : ℕ) ∧
          (2 : ℝ)⁻¹ *
            (Real.sqrt (P.real (concept_event h)) -
              Real.sqrt (Q.real (concept_event h))) ^ (2 : ℕ) ≤ (2 : ℝ)⁻¹ := by
      have hP_event : P.real (concept_event h) ≤ 1 := by
        have hm := MeasureTheory.measureReal_mono (μ := P)
          (Set.subset_univ (concept_event h)) (by simp [hP])
        simpa [MeasureTheory.Measure.real, hP] using hm
      have hQ_event : Q.real (concept_event h) ≤ 1 := by
        have hm := MeasureTheory.measureReal_mono (μ := Q)
          (Set.subset_univ (concept_event h)) (by simp [hQ])
        simpa [MeasureTheory.Measure.real, hQ] using hm
      have hP_sqrt_nonneg := Real.sqrt_nonneg (P.real (concept_event h))
      have hQ_sqrt_nonneg := Real.sqrt_nonneg (Q.real (concept_event h))
      have hP_sqrt_le : Real.sqrt (P.real (concept_event h)) ≤ 1 := by
        nlinarith [Real.sq_sqrt
          (MeasureTheory.measureReal_nonneg (μ := P) (s := concept_event h))]
      have hQ_sqrt_le : Real.sqrt (Q.real (concept_event h)) ≤ 1 := by
        nlinarith [Real.sq_sqrt
          (MeasureTheory.measureReal_nonneg (μ := Q) (s := concept_event h))]
      have hdiff_sq :
          (Real.sqrt (P.real (concept_event h)) -
            Real.sqrt (Q.real (concept_event h))) ^ (2 : ℕ) ≤ 1 := by
        nlinarith [mul_nonneg
          (show 0 ≤ 1 - (Real.sqrt (P.real (concept_event h)) -
            Real.sqrt (Q.real (concept_event h))) by linarith)
          (show 0 ≤ 1 + (Real.sqrt (P.real (concept_event h)) -
            Real.sqrt (Q.real (concept_event h))) by linarith)]
      constructor
      · positivity
      · calc
          (2 : ℝ)⁻¹ *
              (Real.sqrt (P.real (concept_event h)) -
                Real.sqrt (Q.real (concept_event h))) ^ (2 : ℕ)
              ≤ (2 : ℝ)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left hdiff_sq (by norm_num)
          _ = (2 : ℝ)⁻¹ := by ring
    have hset_nonempty :
        {r : ℝ | ∃ h ∈ H,
          r = (2 : ℝ)⁻¹ *
            (Real.sqrt (P.real (concept_event h)) -
              Real.sqrt (Q.real (concept_event h))) ^ (2 : ℕ)}.Nonempty := by
      obtain ⟨h, hh⟩ := hH
      exact ⟨_, h, hh, rfl⟩
    have hset_bdd :
        BddAbove {r : ℝ | ∃ h ∈ H,
          r = (2 : ℝ)⁻¹ *
            (Real.sqrt (P.real (concept_event h)) -
              Real.sqrt (Q.real (concept_event h))) ^ (2 : ℕ)} := by
      refine ⟨(2 : ℝ)⁻¹, ?_⟩
      rintro r ⟨h, hh, rfl⟩
      exact (hterm h).2
    constructor
    · obtain ⟨h, hh⟩ := hH
      have hr :
          (2 : ℝ)⁻¹ *
            (Real.sqrt (P.real (concept_event h)) -
              Real.sqrt (Q.real (concept_event h))) ^ (2 : ℕ) ∈
            {r : ℝ | ∃ h ∈ H,
              r = (2 : ℝ)⁻¹ *
                (Real.sqrt (P.real (concept_event h)) -
                  Real.sqrt (Q.real (concept_event h))) ^ (2 : ℕ)} :=
        ⟨h, hh, rfl⟩
      exact (hterm h).1.trans (le_csSup hset_bdd hr)
    · calc
        sSup {r : ℝ | ∃ h ∈ H,
            r = (2 : ℝ)⁻¹ *
              (Real.sqrt (P.real (concept_event h)) -
                Real.sqrt (Q.real (concept_event h))) ^ (2 : ℕ)}
            ≤ (2 : ℝ)⁻¹ := csSup_le hset_nonempty (by
              rintro r ⟨h, hh, rfl⟩
              exact (hterm h).2)
        _ ≤ 1 := by norm_num
  · have hHempty : H = ∅ := Set.not_nonempty_iff_eq_empty.mp hH
    subst H
    simp [modified_hellinger_distance]

@[blueprint "lem:modified-hellinger-approx-triangle"
  (statement := /-- Let $\Omega$ be a measurable space, let $\mathcal H$ be a Boolean concept class on $\Omega$, and let $P,Q,R$ be measures on $\Omega$ satisfying $P(\Omega)=Q(\Omega)=R(\Omega)=1$. Then
  \[
    d_{\mathcal H}(P,R)
      \leq2\bigl(d_{\mathcal H}(P,Q)+d_{\mathcal H}(Q,R)\bigr).
  \] -/)
  (proof := /-- If $\mathcal H$ is empty, all three suprema in \cref{def:modified-hellinger-distance} vanish. Otherwise, the total-mass hypotheses imply that every event has real measure at most one under $P$, $Q$, and $R$; hence the sets whose suprema define the three distances are nonempty and bounded above. For each $h\in\mathcal H$, insert $\sqrt{Q[h]}$ between $\sqrt{P[h]}$ and $\sqrt{R[h]}$ and apply $(a+b)^2\leq2(a^2+b^2)$. Each resulting summand is at most its corresponding supremum in \cref{def:modified-hellinger-distance}. Taking the supremum over $h$ gives the stated inequality. -/)
  (title := /-- Approximate triangle inequality for the modified distance -/)
  (latexEnv := "lemma")]
lemma modified_hellinger_approx_triangle {Ω : Type*} [MeasurableSpace Ω]
    (H : concept_class Ω)
    (P Q R : MeasureTheory.Measure Ω)
    (hP : P Set.univ = 1) (hQ : Q Set.univ = 1)
    (hR : R Set.univ = 1) :
    modified_hellinger_distance H P R ≤
      2 * (modified_hellinger_distance H P Q +
        modified_hellinger_distance H Q R) := by
  by_cases hH : H.Nonempty
  · have hbdd (A B : MeasureTheory.Measure Ω)
        (hA : A Set.univ = 1) (hB : B Set.univ = 1) :
        BddAbove {r : ℝ | ∃ h ∈ H,
          r = (2 : ℝ)⁻¹ *
            (Real.sqrt (A.real (concept_event h)) -
              Real.sqrt (B.real (concept_event h))) ^ (2 : ℕ)} := by
      refine ⟨1, ?_⟩
      rintro r ⟨h, hh, rfl⟩
      have hA_event : A.real (concept_event h) ≤ 1 := by
        calc
          A.real (concept_event h) ≤ A.real Set.univ :=
            MeasureTheory.measureReal_mono
              (Set.subset_univ (concept_event h)) (by simp [hA])
          _ = 1 := by simp [MeasureTheory.Measure.real, hA]
      have hB_event : B.real (concept_event h) ≤ 1 := by
        calc
          B.real (concept_event h) ≤ B.real Set.univ :=
            MeasureTheory.measureReal_mono
              (Set.subset_univ (concept_event h)) (by simp [hB])
          _ = 1 := by simp [MeasureTheory.Measure.real, hB]
      have hA_sqrt : Real.sqrt (A.real (concept_event h)) ≤ 1 :=
        Real.sqrt_le_one.mpr hA_event
      have hB_sqrt : Real.sqrt (B.real (concept_event h)) ≤ 1 :=
        Real.sqrt_le_one.mpr hB_event
      have hleft : 0 ≤
          1 - (Real.sqrt (A.real (concept_event h)) -
            Real.sqrt (B.real (concept_event h))) := by
        linarith [Real.sqrt_nonneg (B.real (concept_event h))]
      have hright : 0 ≤
          1 + (Real.sqrt (A.real (concept_event h)) -
            Real.sqrt (B.real (concept_event h))) := by
        linarith [Real.sqrt_nonneg (A.real (concept_event h))]
      nlinarith [mul_nonneg hleft hright]
    unfold modified_hellinger_distance
    apply csSup_le
    · rcases hH with ⟨h, hh⟩
      exact ⟨(2 : ℝ)⁻¹ *
        (Real.sqrt (P.real (concept_event h)) -
          Real.sqrt (R.real (concept_event h))) ^ (2 : ℕ),
        ⟨h, hh, rfl⟩⟩
    · intro r hr
      rcases hr with ⟨h, hh, rfl⟩
      have hPQ := le_csSup (hbdd P Q hP hQ)
        (show (2 : ℝ)⁻¹ *
          (Real.sqrt (P.real (concept_event h)) -
            Real.sqrt (Q.real (concept_event h))) ^ (2 : ℕ) ∈
          {r : ℝ | ∃ h ∈ H,
            r = (2 : ℝ)⁻¹ *
              (Real.sqrt (P.real (concept_event h)) -
                Real.sqrt (Q.real (concept_event h))) ^ (2 : ℕ)}
          from ⟨h, hh, rfl⟩)
      have hQR := le_csSup (hbdd Q R hQ hR)
        (show (2 : ℝ)⁻¹ *
          (Real.sqrt (Q.real (concept_event h)) -
            Real.sqrt (R.real (concept_event h))) ^ (2 : ℕ) ∈
          {r : ℝ | ∃ h ∈ H,
            r = (2 : ℝ)⁻¹ *
              (Real.sqrt (Q.real (concept_event h)) -
                Real.sqrt (R.real (concept_event h))) ^ (2 : ℕ)}
          from ⟨h, hh, rfl⟩)
      nlinarith [sq_nonneg
        ((Real.sqrt (P.real (concept_event h)) -
            Real.sqrt (Q.real (concept_event h))) -
          (Real.sqrt (Q.real (concept_event h)) -
            Real.sqrt (R.real (concept_event h))))]
  · rw [Set.not_nonempty_iff_eq_empty.mp hH]
    simp [modified_hellinger_distance]

@[blueprint "lem:modified-distance-le-squared-hellinger"
  (statement := /-- Let $(\Omega,\mathcal A)$ be a measurable space, let $\mu$ be a
  measure on $\Omega$, and let $\mathcal F$ be a family of Hellinger densities
  relative to $\mu$. For every pair of Hellinger densities $p,q$ relative to $\mu$,
  \[
    d_{\mathcal H}(p,q)\leq H^2(p,q),
    \qquad \mathcal H=\operatorname{Ratio}(\mathcal F).
  \] -/)
  (proof := /-- The unit-mass identity in \cref{def:hellinger-density} first
  implies that both density functions are integrable. Every concept in
  \cref{def:ratio-concept-class} represents a measurable event $A$. Put
  $u=\sqrt p$ and $v=\sqrt q$ on $A$, and write
  $a=\int_Ap$, $b=\int_Aq$, and $c=\int_Auv$. The nonnegativity of
  $\int_A(tu-v)^2$ for every $t\in\mathbb R$ gives $c^2\leq ab$ and hence
  $c\leq\sqrt{ab}$. Expanding the square therefore yields
  \[
    (\sqrt a-\sqrt b)^2\leq\int_A(u-v)^2
      \leq\int_\Omega(u-v)^2.
  \]
  After multiplication by $1/2$, this bounds every summand in
  \cref{def:modified-hellinger-distance} by \cref{def:squared-hellinger}.
  Taking the supremum proves the result when the ratio class is nonempty. If
  the density family is empty, that supremum is zero, while
  \cref{lem:squared-hellinger-range} gives the required nonnegativity. -/)
  (title := /-- The modified distance is dominated by Hellinger distance -/)
  (latexEnv := "lemma")]
lemma modified_distance_le_squared_hellinger {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} (F : Set (hellinger_density Ω μ))
    (p q : hellinger_density Ω μ) :
    modified_hellinger_distance (ratio_concept_class F)
        p.toProbabilityMeasure q.toProbabilityMeasure ≤
      squared_hellinger p q := by
  have hp_mass : ∫⁻ x, ENNReal.ofReal (p.val x) ∂μ = 1 := by
    have h := congrArg (fun ν : MeasureTheory.Measure Ω => ν Set.univ)
      p.measure_eq_withDensity
    simpa [MeasureTheory.withDensity_apply] using h.symm
  have hp_int : MeasureTheory.Integrable p.val μ := by
    apply (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      p.measurable_val.aestronglyMeasurable
      (Filter.Eventually.of_forall p.nonnegative)).mp
    rw [hp_mass]
    norm_num
  have hq_mass : ∫⁻ x, ENNReal.ofReal (q.val x) ∂μ = 1 := by
    have h := congrArg (fun ν : MeasureTheory.Measure Ω => ν Set.univ)
      q.measure_eq_withDensity
    simpa [MeasureTheory.withDensity_apply] using h.symm
  have hq_int : MeasureTheory.Integrable q.val μ := by
    apply (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      q.measurable_val.aestronglyMeasurable
      (Filter.Eventually.of_forall q.nonnegative)).mp
    rw [hq_mass]
    norm_num
  have hdiff_int : MeasureTheory.Integrable
      (fun x => (Real.sqrt (p.val x) - Real.sqrt (q.val x)) ^ 2) μ := by
    refine ((hp_int.add hq_int).const_mul 2).mono_nonneg ?_ ?_ ?_
    · exact (p.measurable_val.sqrt.sub q.measurable_val.sqrt).pow_const
        2 |>.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => sq_nonneg _
    · exact Filter.Eventually.of_forall fun x => by
        change (Real.sqrt (p.val x) - Real.sqrt (q.val x)) ^ 2 ≤
          2 * (p.val x + q.val x)
        nlinarith [Real.sq_sqrt (p.nonnegative x),
          Real.sq_sqrt (q.nonnegative x),
          sq_nonneg (Real.sqrt (p.val x) + Real.sqrt (q.val x))]
  by_cases hF : F.Nonempty
  · obtain ⟨f₀, hf₀⟩ := hF
    rw [modified_hellinger_distance]
    refine csSup_le ?_ ?_
    · let h : Ω → Bool :=
        fun x => decide ((0 : ℝ) * f₀.val x ≤ f₀.val x)
      refine ⟨_, h, ?_, rfl⟩
      exact ⟨f₀, hf₀, f₀, hf₀, 0, rfl⟩
    · intro b hb
      rcases hb with ⟨h, hh, rfl⟩
      rcases hh with ⟨f, hf, g, hg, τ, rfl⟩
      let s : Set Ω :=
        concept_event (fun x => decide (τ * g.val x ≤ f.val x))
      have hs : MeasurableSet s := by
        dsimp [s]
        simpa [concept_event] using
          measurableSet_le (measurable_const.mul g.measurable_val)
            f.measurable_val
      have hp_set :
          (p.toProbabilityMeasure : MeasureTheory.Measure Ω).real s =
            ∫ x in s, p.val x ∂μ := by
        rw [MeasureTheory.Measure.real, p.measure_eq_withDensity,
          MeasureTheory.withDensity_apply _ hs]
        symm
        exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall p.nonnegative)
          p.measurable_val.aestronglyMeasurable
      have hq_set :
          (q.toProbabilityMeasure : MeasureTheory.Measure Ω).real s =
            ∫ x in s, q.val x ∂μ := by
        rw [MeasureTheory.Measure.real, q.measure_eq_withDensity,
          MeasureTheory.withDensity_apply _ hs]
        symm
        exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall q.nonnegative)
          q.measurable_val.aestronglyMeasurable
      let u : Ω → ℝ := fun x => Real.sqrt (p.val x)
      let v : Ω → ℝ := fun x => Real.sqrt (q.val x)
      let A : ℝ := ∫ x in s, p.val x ∂μ
      let B : ℝ := ∫ x in s, q.val x ∂μ
      let C : ℝ := ∫ x in s, u x * v x ∂μ
      have hp_res : MeasureTheory.Integrable p.val (μ.restrict s) :=
        hp_int.mono_measure MeasureTheory.Measure.restrict_le_self
      have hq_res : MeasureTheory.Integrable q.val (μ.restrict s) :=
        hq_int.mono_measure MeasureTheory.Measure.restrict_le_self
      have huv_int : MeasureTheory.Integrable
          (fun x => u x * v x) (μ.restrict s) := by
        refine (hp_res.add hq_res).mono' ?_ ?_
        · exact
            (p.measurable_val.sqrt.mul q.measurable_val.sqrt).aestronglyMeasurable
              |>.mono_measure MeasureTheory.Measure.restrict_le_self
        · exact Filter.Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs, abs_of_nonneg
              (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
            dsimp [u, v]
            nlinarith [Real.sq_sqrt (p.nonnegative x),
              Real.sq_sqrt (q.nonnegative x),
              sq_nonneg (Real.sqrt (p.val x) - Real.sqrt (q.val x))]
      have hA : 0 ≤ A := by
        dsimp [A]
        exact MeasureTheory.integral_nonneg
          (fun x => p.nonnegative x)
      have hB : 0 ≤ B := by
        dsimp [B]
        exact MeasureTheory.integral_nonneg
          (fun x => q.nonnegative x)
      have hC : 0 ≤ C := by
        dsimp [C]
        exact MeasureTheory.integral_nonneg
          (fun x => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      have hquad (t : ℝ) :
          0 ≤ t ^ 2 * A - (2 * t) * C + B := by
        dsimp [A, B, C]
        calc
          0 ≤ ∫ x in s, (t * u x - v x) ^ 2 ∂μ :=
            MeasureTheory.integral_nonneg
              (fun x => sq_nonneg (t * u x - v x))
          _ = ∫ x in s,
                (t ^ 2 * p.val x - (2 * t) * (u x * v x)) +
                  q.val x ∂μ := by
            congr 1
            funext x
            dsimp [u, v]
            nlinarith [Real.sq_sqrt (p.nonnegative x),
              Real.sq_sqrt (q.nonnegative x)]
          _ = (∫ x in s,
                t ^ 2 * p.val x - (2 * t) * (u x * v x) ∂μ) +
              (∫ x in s, q.val x ∂μ) :=
            MeasureTheory.integral_add
              ((hp_res.const_mul (t ^ 2)).sub
                (huv_int.const_mul (2 * t))) hq_res
          _ = ((∫ x in s, t ^ 2 * p.val x ∂μ) -
                (∫ x in s, (2 * t) * (u x * v x) ∂μ)) +
              (∫ x in s, q.val x ∂μ) := by
            rw [MeasureTheory.integral_sub
              (hp_res.const_mul (t ^ 2))
              (huv_int.const_mul (2 * t))]
          _ = _ := by
            simp only [MeasureTheory.integral_const_mul]
      have hC_sq : C ^ 2 ≤ A * B := by
        by_cases hA0 : A = 0
        · have hp_zero : p.val =ᵐ[μ.restrict s] 0 := by
            apply (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
              (Filter.Eventually.of_forall p.nonnegative) hp_res).mp
            simpa [A] using hA0
          have huv_zero : (fun x => u x * v x) =ᵐ[μ.restrict s] 0 :=
            hp_zero.mono fun x hx => by
              change p.val x = 0 at hx
              dsimp [u]
              rw [hx]
              simp
          have hC0 : C = 0 := by
            dsimp [C]
            rw [MeasureTheory.integral_congr_ae huv_zero]
            simp
          simpa [hC0] using mul_nonneg hA hB
        · have hdisc := hquad (C / A)
          field_simp [hA0] at hdisc
          nlinarith [sq_nonneg A]
      have hcs : C ≤ Real.sqrt A * Real.sqrt B := by
        have hAB : 0 ≤ Real.sqrt A * Real.sqrt B :=
          mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB,
          sq_nonneg (C + Real.sqrt A * Real.sqrt B)]
      have hset_eq :
          ∫ x in s, (u x - v x) ^ 2 ∂μ =
            A + B - 2 * C := by
        dsimp [A, B, C]
        calc
          ∫ x in s, (u x - v x) ^ 2 ∂μ =
              ∫ x in s,
                (p.val x + q.val x) - 2 * (u x * v x) ∂μ := by
            congr 1
            funext x
            dsimp [u, v]
            nlinarith [Real.sq_sqrt (p.nonnegative x),
              Real.sq_sqrt (q.nonnegative x)]
          _ = (∫ x in s, p.val x + q.val x ∂μ) -
              (∫ x in s, 2 * (u x * v x) ∂μ) :=
            MeasureTheory.integral_sub
              (hp_res.add hq_res) (huv_int.const_mul 2)
          _ = ((∫ x in s, p.val x ∂μ) +
                (∫ x in s, q.val x ∂μ)) -
              (∫ x in s, 2 * (u x * v x) ∂μ) := by
            rw [MeasureTheory.integral_add hp_res hq_res]
          _ = _ := by
            simp only [MeasureTheory.integral_const_mul]
      have hlocal :
          (Real.sqrt A - Real.sqrt B) ^ 2 ≤
            ∫ x in s, (u x - v x) ^ 2 ∂μ := by
        rw [hset_eq]
        nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB]
      have hrestrict :
          ∫ x in s, (u x - v x) ^ 2 ∂μ ≤
            ∫ x, (Real.sqrt (p.val x) - Real.sqrt (q.val x)) ^ 2 ∂μ := by
        dsimp [u, v]
        exact MeasureTheory.setIntegral_le_integral hdiff_int
          (Filter.Eventually.of_forall fun x => sq_nonneg _)
      have hmain :
          (Real.sqrt A - Real.sqrt B) ^ 2 ≤
            ∫ x, (Real.sqrt (p.val x) - Real.sqrt (q.val x)) ^ 2 ∂μ :=
        hlocal.trans hrestrict
      have hhalf := mul_le_mul_of_nonneg_left hmain
        (by positivity : 0 ≤ (2 : ℝ)⁻¹)
      simpa [s, A, B, hp_set, hq_set, squared_hellinger] using hhalf
  · have hratio : ratio_concept_class F = ∅ := by
      simp [Set.not_nonempty_iff_eq_empty.mp hF, ratio_concept_class]
    simp [modified_hellinger_distance, hratio,
      (squared_hellinger_range p q).1]

@[blueprint "lem:entropy-envelope-monotone"
  (statement := /-- For all real numbers $x$ and $y$ satisfying $0\leq x\leq y\leq1$, the entropy envelope satisfies $z(x)\leq z(y)$. -/)
  (proof := /-- By \cref{def:entropy-envelope}, $z$ is the sum of the identity function and the total negative-entropy function, and is therefore continuous on $[0,1]$. For every $x\in(0,1)$, the derivative of this sum is $1+(-\log x-1)=-\log x$. Since $0<x<1$, one has $\log x\leq0$, so this derivative is nonnegative. The interval $[0,1]$ is convex; hence the derivative criterion for monotonicity shows that $z$ is nondecreasing there. -/)
  (title := /-- Monotonicity of the entropy envelope -/)
  (latexEnv := "lemma")]
lemma entropy_envelope_monotone :
    MonotoneOn entropy_envelope (Set.Icc (0 : ℝ) 1) := by
  have hmono : MonotoneOn (id + Real.negMulLog) (Set.Icc (0 : ℝ) 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (f' := fun x => -Real.log x) ?_ ?_ ?_
    · exact (continuous_id.add Real.continuous_negMulLog).continuousOn
    · intro x hx
      have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := by
        simpa only [interior_Icc] using hx
      have hxne : x ≠ 0 := ne_of_gt hxIoo.1
      have hderiv := (hasDerivAt_id x).add (Real.hasDerivAt_negMulLog hxne)
      rw [show (1 + (-Real.log x - 1) : ℝ) = -Real.log x by ring] at hderiv
      exact hderiv.hasDerivWithinAt
    · intro x hx
      have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := interior_subset hx
      exact neg_nonneg.mpr (Real.log_nonpos hxIcc.1 hxIcc.2)
  intro x hx y hy hxy
  unfold entropy_envelope
  exact hmono hx hy hxy

@[blueprint "lem:entropy-envelope-dominates"
  (statement := /-- For every $x\in[0,1]$, one has $x\leq z(x)$. -/)
  (proof := /-- On $[0,1]$ one has $\log x\leq0$. Hence $-x\log x\geq0$, and \cref{def:entropy-envelope} gives $z(x)=x-x\log x\geq x$. -/)
  (title := /-- The entropy envelope dominates its argument -/)
  (latexEnv := "lemma")]
lemma entropy_envelope_dominates {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x ≤ entropy_envelope x := by
  rw [entropy_envelope, Real.negMulLog_def]
  linarith [Real.mul_log_nonpos hx0 hx1]

@[blueprint "lem:entropy-envelope-subadd"
  (statement := /-- If $x,a,b\in[0,1]$ and $x\leq a+b$, then
  \[
    z(x)\leq z(a)+z(b).
  \] -/)
  (proof := /-- Suppose first that $a+b\leq1$. By \cref{lem:entropy-envelope-monotone}, it suffices to prove $z(a+b)\leq z(a)+z(b)$. This is immediate from \cref{def:entropy-envelope} if $a=0$ or $b=0$. Otherwise $a,b>0$, and monotonicity of the logarithm gives $\log a\leq\log(a+b)$ and $\log b\leq\log(a+b)$. Multiplication by the nonnegative numbers $a$ and $b$, followed by addition, yields
  \[
    a\log a+b\log b\leq(a+b)\log(a+b),
  \]
  which is equivalent to the required subadditivity inequality by \cref{def:entropy-envelope}. If $1<a+b$, then \cref{lem:entropy-envelope-monotone} gives $z(x)\leq z(1)=1$, while two applications of \cref{lem:entropy-envelope-dominates} give $1<a+b\leq z(a)+z(b)$. -/)
  (title := /-- Subadditivity of the entropy envelope -/)
  (latexEnv := "lemma")]
lemma entropy_envelope_subadd {x a b : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hxab : x ≤ a + b) :
    entropy_envelope x ≤ entropy_envelope a + entropy_envelope b := by
  by_cases hs : a + b ≤ 1
  · have hsum0 : 0 ≤ a + b := by linarith
    have hmono : entropy_envelope x ≤ entropy_envelope (a + b) :=
      entropy_envelope_monotone ⟨hx0, hx1⟩ ⟨hsum0, hs⟩ hxab
    apply hmono.trans
    by_cases ha : a = 0
    · subst a
      simp [entropy_envelope]
    by_cases hb : b = 0
    · subst b
      simp [entropy_envelope]
    have ha_pos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha)
    have hb_pos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb)
    have hsum_pos : 0 < a + b := by linarith
    have ha_sum : a ≤ a + b := by linarith
    have hb_sum : b ≤ a + b := by linarith
    have hloga : Real.log a ≤ Real.log (a + b) :=
      Real.strictMonoOn_log.monotoneOn ha_pos hsum_pos ha_sum
    have hlogb : Real.log b ≤ Real.log (a + b) :=
      Real.strictMonoOn_log.monotoneOn hb_pos hsum_pos hb_sum
    simp only [entropy_envelope, Real.negMulLog_def]
    nlinarith [mul_le_mul_of_nonneg_left hloga ha0,
      mul_le_mul_of_nonneg_left hlogb hb0]
  · have hsum1 : 1 ≤ a + b := le_of_not_ge hs
    have hmono : entropy_envelope x ≤ entropy_envelope 1 :=
      entropy_envelope_monotone ⟨hx0, hx1⟩ ⟨by norm_num, by norm_num⟩ hx1
    have ha := entropy_envelope_dominates ha0 ha1
    have hb := entropy_envelope_dominates hb0 hb1
    have hone : entropy_envelope 1 = 1 := by simp [entropy_envelope]
    rw [hone] at hmono
    linarith

@[blueprint "lem:entropy-envelope-approx-subadd"
  (statement := /-- For all real numbers $x,a,b$ satisfying
  $0\leq x\leq1$, $0\leq a\leq1$, and $0\leq b\leq1$, if
  $x\leq2(a+b)$, then
  \[
    z(x)\leq2\bigl(z(a)+z(b)\bigr).
  \] -/)
  (proof := /-- Set $s=a+b$. If $s\leq1$, apply
  \cref{lem:entropy-envelope-subadd} first to $x\leq s+s$ and then to
  $s=a+b$; this gives $z(x)\leq2z(s)\leq2(z(a)+z(b))$. If $1<s$,
  then $x\leq1<s=a+b$, so another application of
  \cref{lem:entropy-envelope-subadd} gives $z(x)\leq z(a)+z(b)$.
  By \cref{lem:entropy-envelope-dominates}, both $z(a)$ and $z(b)$ are
  nonnegative, and hence $z(a)+z(b)\leq2(z(a)+z(b))$. -/)
  (title := /-- Entropy estimate for an approximate triangle inequality -/)
  (latexEnv := "lemma")]
lemma entropy_envelope_approx_subadd {x a b : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hxab : x ≤ 2 * (a + b)) :
    entropy_envelope x ≤
      2 * (entropy_envelope a + entropy_envelope b) := by
  by_cases hs1 : a + b ≤ 1
  · have hs0 : 0 ≤ a + b := add_nonneg ha0 hb0
    have houter := entropy_envelope_subadd hx0 hx1 hs0 hs1 hs0 hs1
      (by nlinarith [hxab])
    have hinner := entropy_envelope_subadd hs0 hs1 ha0 ha1 hb0 hb1
      (le_refl (a + b))
    nlinarith
  · have hs : 1 ≤ a + b := le_of_not_ge hs1
    have hxs : x ≤ a + b := hx1.trans hs
    have hsub := entropy_envelope_subadd hx0 hx1 ha0 ha1 hb0 hb1 hxs
    have hza : 0 ≤ entropy_envelope a :=
      ha0.trans (entropy_envelope_dominates ha0 ha1)
    have hzb : 0 ≤ entropy_envelope b :=
      hb0.trans (entropy_envelope_dominates hb0 hb1)
    nlinarith

@[blueprint "lem:move-log-across-reverse-bound"
  (statement := /-- Let $x,y\in[0,1]$. If
  \[
    x\geq\frac{y}{50\log_2(4/y)},
  \]
  then $y\leq100z(x)$, where $z(x)=x+\operatorname{negMulLog}(x)$; equivalently,
  $z(x)=x\log(e/x)$ for $x>0$, with the continuous-extension convention
  $z(0)=0$, and this logarithm is natural. -/)
  (proof := /-- If $y=0$, then \cref{lem:entropy-envelope-dominates} gives
  $0\leq x\leq z(x)$, so the conclusion follows. Suppose that $y>0$, and
  set $L=\log_2(4/y)$ and $u=y/(50L)$. The standard bound
  $1-2^{-1}\leq\log 2$ gives $\log 2\geq1/2$. Since $y\leq1$,
  monotonicity of the natural logarithm gives
  $2\log 2=\log 4\leq\log(4/y)$; hence \cref{def:binary-logarithm}
  yields $L\geq2$. Thus $u>0$, and the hypothesis gives $u\leq x\leq1$.
  By \cref{lem:entropy-envelope-monotone}, one has $z(u)\leq z(x)$.
  Moreover, $L\geq2$ implies $u\leq y/4$, and therefore
  $4/y\leq1/u$. Taking logarithms and using $u\leq1$ yields
  \[
    \log(4/y)\leq-\log u,
    \qquad
    L\leq2(-\log u)\leq2(1-\log u).
  \]
  Since $y=50Lu$, multiplication by $50u\geq0$ and
  \cref{def:entropy-envelope} give
  \[
    y\leq100u(1-\log u)=100z(u)\leq100z(x),
  \]
  as required. -/)
  (title := /-- Moving the logarithm across the reverse bound -/)
  (latexEnv := "lemma")]
lemma move_log_across_reverse_bound {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hxy : y / (50 * binary_logarithm (4 / y)) ≤ x) :
    y ≤ 100 * entropy_envelope x := by
  by_cases hy : y = 0
  · subst y
    have hxz : 0 ≤ entropy_envelope x :=
      hx0.trans (entropy_envelope_dominates hx0 hx1)
    nlinarith
  have hypos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hy)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hlog2pos : 0 < Real.log 2 := by linarith
  have hfour_div : (4 : ℝ) ≤ 4 / y := by
    apply (le_div_iff₀ hypos).2
    nlinarith
  have hlog_four : Real.log 4 ≤ Real.log (4 / y) :=
    Real.log_le_log (by norm_num) hfour_div
  have hlog_lower : 2 * Real.log 2 ≤ Real.log (4 / y) := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)] at hlog_four
    linarith
  set L : ℝ := binary_logarithm (4 / y) with hL
  have hL2 : 2 ≤ L := by
    rw [hL, binary_logarithm]
    exact (le_div_iff₀ hlog2pos).2 hlog_lower
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL2
  have hdenpos : 0 < 50 * L := mul_pos (by norm_num) hLpos
  set u : ℝ := y / (50 * L) with hu
  have hupos : 0 < u := by
    rw [hu]
    exact div_pos hypos hdenpos
  have hu0 : 0 ≤ u := le_of_lt hupos
  have hux : u ≤ x := by
    simpa [hu, hL] using hxy
  have hu1 : u ≤ 1 := hux.trans hx1
  have hzu_le : entropy_envelope u ≤ entropy_envelope x :=
    entropy_envelope_monotone ⟨hu0, hu1⟩ ⟨hx0, hx1⟩ hux
  have huy4 : u ≤ y / 4 := by
    rw [hu, div_le_div_iff₀ hdenpos (by norm_num)]
    nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hL2)]
  have hfrac : 4 / y ≤ 1 / u := by
    rw [div_le_div_iff₀ hypos hupos]
    nlinarith
  have hlogcomp : Real.log (4 / y) ≤ -Real.log u := by
    have h := Real.log_le_log (div_pos (by norm_num) hypos) hfrac
    simpa [one_div] using h
  have hlogu : Real.log u ≤ 0 := Real.log_nonpos hu0 hu1
  have hscale : -Real.log u ≤ 2 * (-Real.log u) * Real.log 2 := by
    have hnonneg : 0 ≤ (-Real.log u) * (2 * Real.log 2 - 1) :=
      mul_nonneg (neg_nonneg.mpr hlogu) (by linarith)
    nlinarith
  have hLlog : L ≤ 2 * (-Real.log u) := by
    rw [hL, binary_logarithm]
    apply (div_le_iff₀ hlog2pos).2
    exact hlogcomp.trans hscale
  have hLenv : L ≤ 2 * (1 - Real.log u) := by linarith
  have hy_eq : y = 50 * L * u := by
    rw [hu]
    field_simp
  have hmul := mul_le_mul_of_nonneg_right hLenv
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 50) hu0)
  have hy_zu : y ≤ 100 * entropy_envelope u := by
    rw [entropy_envelope, Real.negMulLog_def]
    nlinarith
  exact hy_zu.trans (mul_le_mul_of_nonneg_left hzu_le (by norm_num))

@[blueprint "lem:reverse-data-processing-ratio-class"
  (statement := /-- Let $(\Omega,\mathcal A)$ be a measurable space, let $\mu$ be a measure on $\Omega$, and let $\mathcal F$ be a family of probability densities with respect to $\mu$. For every $p,q\in\mathcal F$, the probability measures $P_p$ and $P_q$ induced by these densities satisfy
  \[
    \frac{H^2(p,q)}{50\log_2\bigl(4/H^2(p,q)\bigr)}
      \leq d_{\operatorname{Ratio}(\mathcal F)}(P_p,P_q).
  \] -/)
  (proof := /-- By \cref{lem:squared-hellinger-range}, the squared Hellinger distance lies in $[0,1]$. If it vanishes, the conclusion follows from the nonnegativity supplied by \cref{lem:modified-hellinger-range}, whose unit-mass hypotheses are given by \cref{lem:density-measure-univ}. Assume henceforth that $y=H^2(p,q)>0$, and put $L=\log_2(4/y)$, so that $L\geq2$.

  We first prove a one-sided estimate for arbitrary $a,b\in\mathcal F$ under the hypothesis that the part of the Hellinger integral on $\{b\leq a\}$ is at least $H^2(a,b)$. Every threshold $\{t b\leq a\}$ belongs to \cref{def:ratio-concept-class}. Expanding \cref{def:modified-hellinger-distance} and comparing the masses of this event under the measures induced by $a$ and $b$ shows that, for every $c\geq0$,
  \[
    c^2 P_b\bigl((1+c)^2b\leq a\bigr)\leq2D,
  \]
  where $D$ is the modified distance. Set $s=\sqrt y/2$. On the near-equality region
  \[
    N=\{b\leq a<(1+s)^2b\},
  \]
  the pointwise squared root difference is at most $s^2b$, and hence its integral is at most $y/4$. For each $k=0,\ldots,\lceil L\rceil$, apply the preceding threshold estimate with $c=2^ks$; the Hellinger integral over
  \[
    \{(1+2^ks)^2b\leq a<(1+2^{k+1}s)^2b,\ a<4b\}
  \]
  is at most $8D$. The terminal region $\{4b\leq a\}$ also contributes at most $8D$. These regions are pairwise disjoint and cover $\{b\leq a\}$: for the intermediate region this follows by choosing the least dyadic interval containing $\sqrt{a/b}-1$, with the zero-denominator case excluded by $a<4b$. Since $\lceil L\rceil<L+1$ and $L\geq2$, summing gives
  \[
    y\leq \frac y4+8(\lceil L\rceil+2)D
      \leq \frac y4+20LD,
  \]
  which implies the weaker estimate $y\leq50LD$ and therefore the claimed one-sided bound.

  Finally, decompose the integral in \cref{def:squared-hellinger} over $\{q\leq p\}$ and its complement. One of the two pieces is at least $H^2(p,q)$. In the first case apply the one-sided estimate directly. In the second, enlarge $\{p<q\}$ to $\{p\leq q\}$ and interchange $p$ and $q$; the squared Hellinger integrand is unchanged after squaring, while \cref{lem:modified-hellinger-symm} restores the original order of the two induced measures. -/)
  (title := /-- Reverse data processing for a ratio class -/)
  (latexEnv := "lemma")]
lemma reverse_data_processing_ratio_class {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {F : Set (hellinger_density Ω μ)}
    {p q : hellinger_density Ω μ} (hp : p ∈ F) (hq : q ∈ F) :
    squared_hellinger p q /
        (50 * binary_logarithm (4 / squared_hellinger p q)) ≤
      modified_hellinger_distance (ratio_concept_class F)
        p.toProbabilityMeasure q.toProbabilityMeasure := by
  classical
  rcases squared_hellinger_range p q with ⟨hy0, hy1⟩
  rcases modified_hellinger_range (ratio_concept_class F)
      p.toProbabilityMeasure q.toProbabilityMeasure
      (density_measure_univ p) (density_measure_univ q) with ⟨hd0, hd1⟩
  by_cases hy : squared_hellinger p q = 0
  · simpa [hy] using hd0
  · have hypos : 0 < squared_hellinger p q := lt_of_le_of_ne hy0 (Ne.symm hy)
    let P : MeasureTheory.Measure Ω := p.toProbabilityMeasure
    let Q : MeasureTheory.Measure Ω := q.toProbabilityMeasure
    let D : ℝ := modified_hellinger_distance (ratio_concept_class F) P Q
    let S : Set ℝ :=
      {r : ℝ | ∃ h ∈ ratio_concept_class F,
        r = (2 : ℝ)⁻¹ *
          (Real.sqrt (P.real (concept_event h)) -
            Real.sqrt (Q.real (concept_event h))) ^ (2 : ℕ)}
    have hBdd : BddAbove S := by
      refine ⟨1, ?_⟩
      rintro r ⟨h, hh, rfl⟩
      have hP0 : 0 ≤ P.real (concept_event h) :=
        MeasureTheory.measureReal_nonneg
      have hQ0 : 0 ≤ Q.real (concept_event h) :=
        MeasureTheory.measureReal_nonneg
      have hP1 : P.real (concept_event h) ≤ 1 :=
        MeasureTheory.measureReal_le_one
      have hQ1 : Q.real (concept_event h) ≤ 1 :=
        MeasureTheory.measureReal_le_one
      have hsP0 := Real.sqrt_nonneg (P.real (concept_event h))
      have hsQ0 := Real.sqrt_nonneg (Q.real (concept_event h))
      have hsP1 : Real.sqrt (P.real (concept_event h)) ≤ 1 := by
        nlinarith [Real.sq_sqrt hP0]
      have hsQ1 : Real.sqrt (Q.real (concept_event h)) ≤ 1 := by
        nlinarith [Real.sq_sqrt hQ0]
      norm_num
      nlinarith [sq_nonneg
        (Real.sqrt (P.real (concept_event h)) -
          Real.sqrt (Q.real (concept_event h)))]
    have hthreshold (a b : hellinger_density Ω μ)
        (ha : a ∈ F) (hb : b ∈ F) (t : ℝ) :
        (2 : ℝ)⁻¹ *
            (Real.sqrt (P.real (concept_event
              (fun x => decide (t * b.val x ≤ a.val x)))) -
              Real.sqrt (Q.real (concept_event
                (fun x => decide (t * b.val x ≤ a.val x))))) ^ (2 : ℕ) ≤
          D := by
      dsimp [D, modified_hellinger_distance]
      exact le_csSup hBdd
        ⟨fun x => decide (t * b.val x ≤ a.val x),
          ⟨a, ha, b, hb, t, rfl⟩, rfl⟩
    have hdensity_integrable (a : hellinger_density Ω μ) :
        MeasureTheory.Integrable a.val μ := by
      refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
        a.measurable_val.aestronglyMeasurable
        (Filter.Eventually.of_forall a.nonnegative)).mp ?_
      have heq : (∫⁻ x, ENNReal.ofReal (a.val x) ∂μ) =
          μ.withDensity (fun x => ENNReal.ofReal (a.val x)) Set.univ := by
        rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ]
        simp
      rw [heq, ← a.measure_eq_withDensity]
      finiteness
    have hdensity_set_integral (a : hellinger_density Ω μ)
        (E : Set Ω) (hE : MeasurableSet E) :
        ∫ x in E, a.val x ∂μ =
          (a.toProbabilityMeasure : MeasureTheory.Measure Ω).real E := by
      rw [MeasureTheory.measureReal_def, a.measure_eq_withDensity,
        MeasureTheory.withDensity_apply _ hE]
      rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall a.nonnegative)
        a.measurable_val.aestronglyMeasurable.restrict]
    have hhellinger_integrable (a b : hellinger_density Ω μ) :
        MeasureTheory.Integrable
          (fun x => (Real.sqrt (a.val x) - Real.sqrt (b.val x)) ^ (2 : ℕ)) μ := by
      refine (((hdensity_integrable a).add
        (hdensity_integrable b)).const_mul 2).mono_nonneg ?_ ?_ ?_
      · exact ((a.measurable_val.sqrt.sub
          b.measurable_val.sqrt).pow_const 2).aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun x => sq_nonneg _)
      · filter_upwards with x
        change (Real.sqrt (a.val x) - Real.sqrt (b.val x)) ^ 2 ≤
          2 * (a.val x + b.val x)
        nlinarith [Real.sq_sqrt (a.nonnegative x),
          Real.sq_sqrt (b.nonnegative x),
          sq_nonneg (Real.sqrt (a.val x) + Real.sqrt (b.val x))]
    have hordered (a b : hellinger_density Ω μ) (ha : a ∈ F) (hb : b ∈ F)
        (hside_ab : squared_hellinger a b ≤
          ∫ x in {x | b.val x ≤ a.val x},
            (Real.sqrt (a.val x) - Real.sqrt (b.val x)) ^ (2 : ℕ) ∂μ) :
        squared_hellinger a b /
            (50 * binary_logarithm (4 / squared_hellinger a b)) ≤
          modified_hellinger_distance (ratio_concept_class F)
            a.toProbabilityMeasure b.toProbabilityMeasure := by
      rcases squared_hellinger_range a b with ⟨hyab0, hyab1⟩
      rcases modified_hellinger_range (ratio_concept_class F)
          a.toProbabilityMeasure b.toProbabilityMeasure
          (density_measure_univ a) (density_measure_univ b) with ⟨hDab0, hDab1⟩
      by_cases hyab : squared_hellinger a b = 0
      · simpa [hyab] using hDab0
      · have hyabpos : 0 < squared_hellinger a b :=
          lt_of_le_of_ne hyab0 (Ne.symm hyab)
        let Pa : MeasureTheory.Measure Ω := a.toProbabilityMeasure
        let Pb : MeasureTheory.Measure Ω := b.toProbabilityMeasure
        let Dab : ℝ :=
          modified_hellinger_distance (ratio_concept_class F) Pa Pb
        let Sab : Set ℝ :=
          {r : ℝ | ∃ h ∈ ratio_concept_class F,
            r = (2 : ℝ)⁻¹ *
              (Real.sqrt (Pa.real (concept_event h)) -
                Real.sqrt (Pb.real (concept_event h))) ^ (2 : ℕ)}
        have hBddab : BddAbove Sab := by
          refine ⟨1, ?_⟩
          rintro r ⟨h, hh, rfl⟩
          have hPa0 : 0 ≤ Pa.real (concept_event h) :=
            MeasureTheory.measureReal_nonneg
          have hPb0 : 0 ≤ Pb.real (concept_event h) :=
            MeasureTheory.measureReal_nonneg
          have hPa1 : Pa.real (concept_event h) ≤ 1 :=
            MeasureTheory.measureReal_le_one
          have hPb1 : Pb.real (concept_event h) ≤ 1 :=
            MeasureTheory.measureReal_le_one
          have hsPa0 := Real.sqrt_nonneg (Pa.real (concept_event h))
          have hsPb0 := Real.sqrt_nonneg (Pb.real (concept_event h))
          have hsPa1 : Real.sqrt (Pa.real (concept_event h)) ≤ 1 := by
            nlinarith [Real.sq_sqrt hPa0]
          have hsPb1 : Real.sqrt (Pb.real (concept_event h)) ≤ 1 := by
            nlinarith [Real.sq_sqrt hPb0]
          norm_num
          nlinarith [sq_nonneg
            (Real.sqrt (Pa.real (concept_event h)) -
              Real.sqrt (Pb.real (concept_event h)))]
        have hthreshold_ab (t : ℝ) :
            (2 : ℝ)⁻¹ *
                (Real.sqrt (Pa.real (concept_event
                  (fun x => decide (t * b.val x ≤ a.val x)))) -
                  Real.sqrt (Pb.real (concept_event
                    (fun x => decide (t * b.val x ≤ a.val x))))) ^ (2 : ℕ) ≤
              Dab := by
          dsimp [Dab, modified_hellinger_distance]
          exact le_csSup hBddab
            ⟨fun x => decide (t * b.val x ≤ a.val x),
              ⟨a, ha, b, hb, t, rfl⟩, rfl⟩
        have hthreshold_mass (t : ℝ) (ht0 : 0 ≤ t) :
            t * Pb.real {x | t * b.val x ≤ a.val x} ≤
              Pa.real {x | t * b.val x ≤ a.val x} := by
          let T : Set Ω := {x | t * b.val x ≤ a.val x}
          have hT : MeasurableSet T :=
            measurableSet_le (b.measurable_val.const_mul t) a.measurable_val
          rw [← hdensity_set_integral a T hT,
            ← hdensity_set_integral b T hT,
            ← MeasureTheory.integral_const_mul]
          exact MeasureTheory.setIntegral_mono_on
            ((hdensity_integrable b).const_mul t).integrableOn
            (hdensity_integrable a).integrableOn hT
            (fun x hx => hx)
        let yab : ℝ := squared_hellinger a b
        let Lab : ℝ := binary_logarithm (4 / yab)
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have h4y : (4 : ℝ) ≤ 4 / yab := by
          rw [le_div_iff₀ (show 0 < yab by exact hyabpos)]
          nlinarith [hyab1]
        have hlog4 : Real.log 4 ≤ Real.log (4 / yab) :=
          Real.log_le_log (by norm_num) h4y
        have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
          norm_num
        have hLab : 2 ≤ Lab := by
          dsimp [Lab, binary_logarithm]
          rw [le_div_iff₀ hlog2]
          nlinarith
        have hthreshold_quantitative (c : ℝ) (hc0 : 0 ≤ c) :
            c ^ 2 * Pb.real {x | (1 + c) ^ 2 * b.val x ≤ a.val x} ≤
              2 * Dab := by
          let T : Set Ω := {x | (1 + c) ^ 2 * b.val x ≤ a.val x}
          have hmass := hthreshold_mass ((1 + c) ^ 2) (sq_nonneg _)
          have hP0 : 0 ≤ Pa.real T := MeasureTheory.measureReal_nonneg
          have hQ0 : 0 ≤ Pb.real T := MeasureTheory.measureReal_nonneg
          have hsP0 := Real.sqrt_nonneg (Pa.real T)
          have hsQ0 := Real.sqrt_nonneg (Pb.real T)
          have hroot :
              (1 + c) * Real.sqrt (Pb.real T) ≤ Real.sqrt (Pa.real T) := by
            have hc1 : 0 ≤ 1 + c := by linarith
            have hleft0 : 0 ≤ (1 + c) * Real.sqrt (Pb.real T) :=
              mul_nonneg hc1 hsQ0
            apply (sq_le_sq₀ hleft0 hsP0).mp
            rw [mul_pow, Real.sq_sqrt hQ0, Real.sq_sqrt hP0]
            exact hmass
          have hdiff : c * Real.sqrt (Pb.real T) ≤
              Real.sqrt (Pa.real T) - Real.sqrt (Pb.real T) := by
            linarith
          have hcd0 : 0 ≤ c * Real.sqrt (Pb.real T) :=
            mul_nonneg hc0 hsQ0
          have hdiff0 :
              0 ≤ Real.sqrt (Pa.real T) - Real.sqrt (Pb.real T) := by
            linarith
          have hsquare :
              (c * Real.sqrt (Pb.real T)) ^ 2 = c ^ 2 * Pb.real T := by
            rw [mul_pow, Real.sq_sqrt hQ0]
          have hconcept : concept_event
              (fun x => decide ((1 + c) ^ 2 * b.val x ≤ a.val x)) = T := by
            ext x
            simp [concept_event, T]
          have hsup := hthreshold_ab ((1 + c) ^ 2)
          rw [hconcept] at hsup
          have hsqle := (sq_le_sq₀ hcd0 hdiff0).2 hdiff
          rw [hsquare] at hsqle
          norm_num at hsup
          nlinarith
        let sab : ℝ := Real.sqrt yab / 2
        have hsab0 : 0 ≤ sab := by positivity
        have hsabpos : 0 < sab := by
          dsimp [sab]
          positivity
        let N : Set Ω :=
          {x | b.val x ≤ a.val x ∧
            a.val x < (1 + sab) ^ 2 * b.val x}
        have hN : MeasurableSet N :=
          (measurableSet_le b.measurable_val a.measurable_val).inter
            (measurableSet_lt a.measurable_val
              (b.measurable_val.const_mul ((1 + sab) ^ 2)))
        have hnear_point : ∀ x ∈ N,
            (Real.sqrt (a.val x) - Real.sqrt (b.val x)) ^ 2 ≤
              sab ^ 2 * b.val x := by
          intro x hx
          rcases hx with ⟨hba, hab⟩
          have hua := Real.sq_sqrt (a.nonnegative x)
          have hvb := Real.sq_sqrt (b.nonnegative x)
          have hu0 := Real.sqrt_nonneg (a.val x)
          have hv0 := Real.sqrt_nonneg (b.val x)
          have huv : Real.sqrt (b.val x) ≤ Real.sqrt (a.val x) :=
            Real.sqrt_le_sqrt hba
          have hs1 : 0 ≤ 1 + sab := by linarith
          have hprod0 : 0 ≤ (1 + sab) * Real.sqrt (b.val x) :=
            mul_nonneg hs1 hv0
          have hsqrtlt :
              Real.sqrt (a.val x) < (1 + sab) * Real.sqrt (b.val x) := by
            by_contra h
            push Not at h
            have hsquares := (sq_le_sq₀ hprod0 hu0).2 h
            have hsqprod :
                ((1 + sab) * Real.sqrt (b.val x)) ^ 2 =
                  (1 + sab) ^ 2 * b.val x := by
              rw [mul_pow, hvb]
            rw [hsqprod, hua] at hsquares
            linarith
          have hdiff :
              Real.sqrt (a.val x) - Real.sqrt (b.val x) ≤
                sab * Real.sqrt (b.val x) := by
            linarith
          have hdiff0 :
              0 ≤ Real.sqrt (a.val x) - Real.sqrt (b.val x) := by
            linarith
          have hsv0 : 0 ≤ sab * Real.sqrt (b.val x) :=
            mul_nonneg hsab0 hv0
          calc
            (Real.sqrt (a.val x) - Real.sqrt (b.val x)) ^ 2 ≤
                (sab * Real.sqrt (b.val x)) ^ 2 :=
              (sq_le_sq₀ hdiff0 hsv0).2 hdiff
            _ = sab ^ 2 * b.val x := by rw [mul_pow, hvb]
        have hnear_integral :
            ∫ x in N,
                (Real.sqrt (a.val x) - Real.sqrt (b.val x)) ^ 2 ∂μ ≤
              yab / 4 := by
          calc
            _ ≤ ∫ x in N, sab ^ 2 * b.val x ∂μ :=
              MeasureTheory.setIntegral_mono_on
                (hhellinger_integrable a b).integrableOn
                ((hdensity_integrable b).const_mul (sab ^ 2)).integrableOn
                hN hnear_point
            _ = sab ^ 2 * Pb.real N := by
              rw [MeasureTheory.integral_const_mul,
                hdensity_set_integral b N hN]
            _ ≤ yab / 4 := by
              have hPb1 : Pb.real N ≤ 1 := MeasureTheory.measureReal_le_one
              have hPb0 : 0 ≤ Pb.real N := MeasureTheory.measureReal_nonneg
              have hsqy := Real.sq_sqrt hyab0
              dsimp [sab]
              nlinarith
        have hband_integral (c : ℝ) (hc0 : 0 ≤ c) :
            let E : Set Ω :=
              {x | (1 + c) ^ 2 * b.val x ≤ a.val x ∧
                a.val x < (1 + 2 * c) ^ 2 * b.val x ∧
                a.val x < 4 * b.val x}
            ∫ x in E,
                (Real.sqrt (a.val x) - Real.sqrt (b.val x)) ^ 2 ∂μ ≤
              8 * Dab := by
          dsimp only
          let E : Set Ω :=
            {x | (1 + c) ^ 2 * b.val x ≤ a.val x ∧
              a.val x < (1 + 2 * c) ^ 2 * b.val x ∧
              a.val x < 4 * b.val x}
          let T : Set Ω := {x | (1 + c) ^ 2 * b.val x ≤ a.val x}
          have hE : MeasurableSet E :=
            (measurableSet_le
              (b.measurable_val.const_mul ((1 + c) ^ 2))
              a.measurable_val).inter
              ((measurableSet_lt a.measurable_val
                (b.measurable_val.const_mul ((1 + 2 * c) ^ 2))).inter
                (measurableSet_lt a.measurable_val
                  (b.measurable_val.const_mul 4)))
          have hT : MeasurableSet T :=
            measurableSet_le
              (b.measurable_val.const_mul ((1 + c) ^ 2))
              a.measurable_val
          have hET : E ⊆ T := fun x hx => hx.1
          have hpoint : ∀ x ∈ E,
              (Real.sqrt (a.val x) - Real.sqrt (b.val x)) ^ 2 ≤
                4 * c ^ 2 * b.val x := by
            intro x hx
            have hab := hx.2.1
            have hba : b.val x ≤ a.val x := by
              have ht := hx.1
              nlinarith [sq_nonneg c, b.nonnegative x]
            have hua := Real.sq_sqrt (a.nonnegative x)
            have hvb := Real.sq_sqrt (b.nonnegative x)
            have hu0 := Real.sqrt_nonneg (a.val x)
            have hv0 := Real.sqrt_nonneg (b.val x)
            have huv : Real.sqrt (b.val x) ≤ Real.sqrt (a.val x) :=
              Real.sqrt_le_sqrt hba
            have hc1 : 0 ≤ 1 + 2 * c := by linarith
            have hprod0 : 0 ≤ (1 + 2 * c) * Real.sqrt (b.val x) :=
              mul_nonneg hc1 hv0
            have hsqrtlt :
                Real.sqrt (a.val x) <
                  (1 + 2 * c) * Real.sqrt (b.val x) := by
              by_contra h
              push Not at h
              have hsquares := (sq_le_sq₀ hprod0 hu0).2 h
              have hsqprod :
                  ((1 + 2 * c) * Real.sqrt (b.val x)) ^ 2 =
                    (1 + 2 * c) ^ 2 * b.val x := by
                rw [mul_pow, hvb]
              rw [hsqprod, hua] at hsquares
              linarith
            have hdiff :
                Real.sqrt (a.val x) - Real.sqrt (b.val x) ≤
                  2 * c * Real.sqrt (b.val x) := by
              linarith
            have hdiff0 :
                0 ≤ Real.sqrt (a.val x) - Real.sqrt (b.val x) := by
              linarith
            have hcv0 : 0 ≤ 2 * c * Real.sqrt (b.val x) := by positivity
            calc
              _ ≤ (2 * c * Real.sqrt (b.val x)) ^ 2 :=
                (sq_le_sq₀ hdiff0 hcv0).2 hdiff
              _ = 4 * c ^ 2 * b.val x := by
                rw [mul_pow, mul_pow, hvb]
                ring
          calc
            _ ≤ ∫ x in E, (4 * c ^ 2) * b.val x ∂μ :=
              MeasureTheory.setIntegral_mono_on
                (hhellinger_integrable a b).integrableOn
                ((hdensity_integrable b).const_mul
                  (4 * c ^ 2)).integrableOn hE hpoint
            _ = (4 * c ^ 2) * Pb.real E := by
              rw [MeasureTheory.integral_const_mul,
                hdensity_set_integral b E hE]
            _ ≤ (4 * c ^ 2) * Pb.real T := by
              apply mul_le_mul_of_nonneg_left
              · exact MeasureTheory.measureReal_mono hET
                  (by dsimp [Pb]; finiteness)
              · positivity
            _ ≤ 8 * Dab := by
              have hq := hthreshold_quantitative c hc0
              change c ^ 2 * Pb.real T ≤ 2 * Dab at hq
              nlinarith [mul_nonneg (sq_nonneg c)
                (MeasureTheory.measureReal_nonneg : 0 ≤ Pb.real T)]
        have hfinal_integral :
            ∫ x in {x | 4 * b.val x ≤ a.val x},
                (Real.sqrt (a.val x) - Real.sqrt (b.val x)) ^ 2 ∂μ ≤
              8 * Dab := by
          let Z : Set Ω := {x | 4 * b.val x ≤ a.val x}
          have hZ : MeasurableSet Z :=
            measurableSet_le (b.measurable_val.const_mul 4) a.measurable_val
          have hmass := hthreshold_mass 4 (by norm_num)
          have hP0 : 0 ≤ Pa.real Z := MeasureTheory.measureReal_nonneg
          have hQ0 : 0 ≤ Pb.real Z := MeasureTheory.measureReal_nonneg
          have hsP0 := Real.sqrt_nonneg (Pa.real Z)
          have hsQ0 := Real.sqrt_nonneg (Pb.real Z)
          have hroot :
              2 * Real.sqrt (Pb.real Z) ≤ Real.sqrt (Pa.real Z) := by
            have hleft0 : 0 ≤ 2 * Real.sqrt (Pb.real Z) := by positivity
            rw [← (sq_le_sq₀ hleft0 hsP0)]
            rw [mul_pow, Real.sq_sqrt hQ0, Real.sq_sqrt hP0]
            norm_num
            exact hmass
          have hdiff : Real.sqrt (Pa.real Z) / 2 ≤
              Real.sqrt (Pa.real Z) - Real.sqrt (Pb.real Z) := by
            linarith
          have hhalf0 : 0 ≤ Real.sqrt (Pa.real Z) / 2 := by positivity
          have hdiff0 :
              0 ≤ Real.sqrt (Pa.real Z) - Real.sqrt (Pb.real Z) := by
            linarith
          have hconcept :
              concept_event (fun x => decide (4 * b.val x ≤ a.val x)) = Z := by
            ext x
            simp [concept_event, Z]
          have hsup := hthreshold_ab 4
          rw [hconcept] at hsup
          have hsquares := (sq_le_sq₀ hhalf0 hdiff0).2 hdiff
          have hPaD : Pa.real Z ≤ 8 * Dab := by
            rw [div_pow, Real.sq_sqrt hP0] at hsquares
            norm_num at hsquares hsup
            nlinarith
          calc
            _ ≤ ∫ x in Z, a.val x ∂μ := by
              apply MeasureTheory.setIntegral_mono_on
                (hhellinger_integrable a b).integrableOn
                (hdensity_integrable a).integrableOn hZ
              intro x hx
              change 4 * b.val x ≤ a.val x at hx
              have hba : b.val x ≤ a.val x := by
                nlinarith [b.nonnegative x]
              have huv := Real.sqrt_le_sqrt hba
              nlinarith [Real.sq_sqrt (a.nonnegative x),
                Real.sq_sqrt (b.nonnegative x),
                mul_nonneg (Real.sqrt_nonneg (a.val x))
                  (Real.sqrt_nonneg (b.val x))]
            _ = Pa.real Z := hdensity_set_integral a Z hZ
            _ ≤ 8 * Dab := hPaD
        have hdyadic_cover (z s : ℝ) (n : ℕ) (hs : 0 < s)
            (hsz : s ≤ z) (hz1 : z < 1) (htop : 1 / s ≤ 2 ^ n) :
            ∃ k ∈ Finset.range (n + 1),
              (2 : ℝ) ^ k * s ≤ z ∧ z < (2 : ℝ) ^ (k + 1) * s := by
          have hex : ∃ k : ℕ, z < (2 : ℝ) ^ (k + 1) * s := by
            refine ⟨n, ?_⟩
            have hspos : 0 < (2 : ℝ) ^ n * s :=
              mul_pos (by positivity) hs
            have hone : 1 ≤ (2 : ℝ) ^ n * s := by
              rw [div_le_iff₀ hs] at htop
              nlinarith
            have hmono :
                (2 : ℝ) ^ n * s ≤ (2 : ℝ) ^ (n + 1) * s := by
              rw [pow_succ]
              nlinarith [hspos]
            linarith
          let k := Nat.find hex
          have hkprop : z < (2 : ℝ) ^ (k + 1) * s := Nat.find_spec hex
          have hkn : k ≤ n := Nat.find_min' hex (by
            have hspos : 0 < (2 : ℝ) ^ n * s :=
              mul_pos (by positivity) hs
            have hone : 1 ≤ (2 : ℝ) ^ n * s := by
              rw [div_le_iff₀ hs] at htop
              nlinarith
            have hmono :
                (2 : ℝ) ^ n * s ≤ (2 : ℝ) ^ (n + 1) * s := by
              rw [pow_succ]
              nlinarith [hspos]
            linarith)
          refine ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hkn), ?_,
            hkprop⟩
          dsimp [k]
          by_cases hk0 : Nat.find hex = 0
          · rw [hk0]
            norm_num
            exact hsz
          · obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
            have hnot := Nat.find_min hex (show l < Nat.find hex by omega)
            push Not at hnot
            rw [hl]
            exact hnot
        let nab : ℕ := Nat.ceil Lab
        have hLabn : Lab ≤ (nab : ℝ) := by
          dsimp [nab]
          exact Nat.le_ceil Lab
        have hpowy : 4 / yab ≤ (2 : ℝ) ^ nab := by
          apply Real.le_pow_of_log_le (by norm_num)
          have hlogeq : Real.log (4 / yab) = Lab * Real.log 2 := by
            dsimp [Lab, binary_logarithm]
            field_simp
          rw [hlogeq]
          nlinarith
        have hone_s : 1 / sab ≤ 4 / yab := by
          have hsqrty : 0 < Real.sqrt yab := Real.sqrt_pos.2 hyabpos
          have hfrac :
              2 / Real.sqrt yab ≤ 4 / yab := by
            rw [div_le_div_iff₀ hsqrty hyabpos]
            nlinarith [Real.sq_sqrt hyab0, Real.sqrt_nonneg yab]
          convert hfrac using 1 <;> dsimp [sab] <;> field_simp
        have htop : 1 / sab ≤ (2 : ℝ) ^ nab := hone_s.trans hpowy
        have hncast : (nab : ℝ) < Lab + 1 := by
          dsimp [nab]
          exact Nat.ceil_lt_add_one (by linarith : 0 ≤ Lab)
        let Band : ℕ → Set Ω := fun k =>
          {x | (1 + (2 : ℝ) ^ k * sab) ^ 2 * b.val x ≤ a.val x ∧
            a.val x < (1 + 2 * ((2 : ℝ) ^ k * sab)) ^ 2 * b.val x ∧
            a.val x < 4 * b.val x}
        have hBand_measurable (k : ℕ) : MeasurableSet (Band k) := by
          dsimp [Band]
          exact (measurableSet_le
            (b.measurable_val.const_mul
              ((1 + (2 : ℝ) ^ k * sab) ^ 2))
            a.measurable_val).inter
              ((measurableSet_lt a.measurable_val
                (b.measurable_val.const_mul
                  ((1 + 2 * ((2 : ℝ) ^ k * sab)) ^ 2))).inter
                (measurableSet_lt a.measurable_val
                  (b.measurable_val.const_mul 4)))
        have hBand_integral (k : ℕ) :
            ∫ x in Band k,
                (Real.sqrt (a.val x) - Real.sqrt (b.val x)) ^ 2 ∂μ ≤
              8 * Dab := by
          simpa [Band] using
            hband_integral ((2 : ℝ) ^ k * sab) (by positivity)
        have hBand_disjoint_ordered (i j : ℕ) (hijlt : i < j) :
            Disjoint (Band i) (Band j) := by
          apply Set.disjoint_left.2
          intro x hxi hxj
          have hpowers :
              (2 : ℝ) ^ (i + 1) ≤ (2 : ℝ) ^ j := by
            exact pow_le_pow_right₀ (by norm_num)
              (Nat.succ_le_iff.2 hijlt)
          rw [pow_succ] at hpowers
          have hc :
              2 * ((2 : ℝ) ^ i * sab) ≤ (2 : ℝ) ^ j * sab := by
            have hmul := mul_le_mul_of_nonneg_right hpowers hsab0
            simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
          have hsqi :
              (1 + 2 * ((2 : ℝ) ^ i * sab)) ^ 2 ≤
                (1 + (2 : ℝ) ^ j * sab) ^ 2 := by
            have hci0 : 0 ≤ 2 * ((2 : ℝ) ^ i * sab) := by positivity
            nlinarith [sq_nonneg
              ((1 + (2 : ℝ) ^ j * sab) -
                (1 + 2 * ((2 : ℝ) ^ i * sab)))]
          have hmul := mul_le_mul_of_nonneg_right hsqi (b.nonnegative x)
          exact (not_lt_of_ge (hmul.trans hxj.1)) hxi.2.1
        have hBand_pairwise :
            Set.Pairwise (↑(Finset.range (nab + 1)))
              (fun i j => Disjoint (Band i) (Band j)) := by
          intro i hi j hj hij
          by_cases hijlt : i < j
          · exact hBand_disjoint_ordered i j hijlt
          · have hji : j < i := lt_of_le_of_ne
              (Nat.le_of_not_gt hijlt) (Ne.symm hij)
            exact (hBand_disjoint_ordered j i hji).symm
        let BU : Set Ω := ⋃ k ∈ Finset.range (nab + 1), Band k
        have hBU_measurable : MeasurableSet BU := by
          dsimp [BU]
          exact Finset.measurableSet_biUnion _ (fun k hk => hBand_measurable k)
        have hBU_integral :
            ∫ x in BU,
                (Real.sqrt (a.val x) - Real.sqrt (b.val x)) ^ 2 ∂μ ≤
              8 * ((nab : ℝ) + 1) * Dab := by
          calc
            _ = ∑ k ∈ Finset.range (nab + 1),
                ∫ x in Band k,
                  (Real.sqrt (a.val x) - Real.sqrt (b.val x)) ^ 2 ∂μ := by
              dsimp [BU]
              exact MeasureTheory.integral_biUnion_finset
                (Finset.range (nab + 1))
                (fun k hk => hBand_measurable k) hBand_pairwise
                (fun k hk => (hhellinger_integrable a b).integrableOn)
            _ ≤ ∑ k ∈ Finset.range (nab + 1), 8 * Dab :=
              Finset.sum_le_sum (fun k hk => hBand_integral k)
            _ = 8 * ((nab : ℝ) + 1) * Dab := by
              simp
              ring
        have hsable : sab ≤ (1 : ℝ) / 2 := by
          have hsqrt_le : Real.sqrt yab ≤ 1 := by
            nlinarith [Real.sq_sqrt hyab0, Real.sqrt_nonneg yab]
          dsimp [sab]
          linarith
        let Z : Set Ω := {x | 4 * b.val x ≤ a.val x}
        have hZ : MeasurableSet Z :=
          measurableSet_le (b.measurable_val.const_mul 4) a.measurable_val
        have hNBU : Disjoint N BU := by
          apply Set.disjoint_left.2
          intro x hxN hxBU
          rcases Set.mem_iUnion.1 hxBU with ⟨k, hxBU⟩
          rcases Set.mem_iUnion.1 hxBU with ⟨hk, hxBand⟩
          have hc : sab ≤ (2 : ℝ) ^ k * sab := by
            have hp : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
            nlinarith [mul_nonneg (sub_nonneg.2 hp) hsab0]
          have hsq :
              (1 + sab) ^ 2 ≤ (1 + (2 : ℝ) ^ k * sab) ^ 2 := by
            nlinarith [sq_nonneg
              ((1 + (2 : ℝ) ^ k * sab) - (1 + sab))]
          have hmul := mul_le_mul_of_nonneg_right hsq (b.nonnegative x)
          exact (not_lt_of_ge (hmul.trans hxBand.1)) hxN.2
        have hNZ : Disjoint N Z := by
          apply Set.disjoint_left.2
          intro x hxN hxZ
          have hsq : (1 + sab) ^ 2 ≤ (4 : ℝ) := by nlinarith
          have hmul := mul_le_mul_of_nonneg_right hsq (b.nonnegative x)
          exact (not_lt_of_ge hxZ) (hxN.2.trans_le hmul)
        have hBUZ : Disjoint BU Z := by
          apply Set.disjoint_left.2
          intro x hxBU hxZ
          rcases Set.mem_iUnion.1 hxBU with ⟨k, hxBU⟩
          rcases Set.mem_iUnion.1 hxBU with ⟨hk, hxBand⟩
          exact (not_lt_of_ge hxZ) hxBand.2.2
        have hcover :
            {x | b.val x ≤ a.val x} ⊆ N ∪ BU ∪ Z := by
          intro x hxba
          by_cases hxN : a.val x < (1 + sab) ^ 2 * b.val x
          · exact Or.inl (Or.inl ⟨hxba, hxN⟩)
          by_cases hxZ : 4 * b.val x ≤ a.val x
          · exact Or.inr hxZ
          · apply Or.inl
            apply Or.inr
            have hab4 : a.val x < 4 * b.val x := lt_of_not_ge hxZ
            have hbpos : 0 < b.val x := by
              by_contra hb
              push Not at hb
              nlinarith [a.nonnegative x]
            have hvpos : 0 < Real.sqrt (b.val x) :=
              Real.sqrt_pos.2 hbpos
            have hu0 := Real.sqrt_nonneg (a.val x)
            have hv0 := Real.sqrt_nonneg (b.val x)
            have hua := Real.sq_sqrt (a.nonnegative x)
            have hvb := Real.sq_sqrt (b.nonnegative x)
            have hlower :
                (1 + sab) * Real.sqrt (b.val x) ≤
                  Real.sqrt (a.val x) := by
              have hleft0 :
                  0 ≤ (1 + sab) * Real.sqrt (b.val x) := by positivity
              apply (sq_le_sq₀ hleft0 hu0).mp
              rw [mul_pow, hvb, hua]
              exact le_of_not_gt hxN
            have hupper :
                Real.sqrt (a.val x) < 2 * Real.sqrt (b.val x) := by
              by_contra h
              push Not at h
              have hsquares :=
                (sq_le_sq₀ (by positivity : 0 ≤ 2 * Real.sqrt (b.val x))
                  hu0).2 h
              rw [mul_pow, hvb, hua] at hsquares
              norm_num at hsquares
              linarith
            let z : ℝ :=
              Real.sqrt (a.val x) / Real.sqrt (b.val x) - 1
            have hsz : sab ≤ z := by
              dsimp [z]
              rw [le_sub_iff_add_le, le_div_iff₀ hvpos]
              simpa [add_comm] using hlower
            have hz1 : z < 1 := by
              dsimp [z]
              rw [sub_lt_iff_lt_add, div_lt_iff₀ hvpos]
              norm_num
              exact hupper
            rcases hdyadic_cover z sab nab hsabpos hsz hz1 htop with
              ⟨k, hk, hck, hkc⟩
            dsimp [BU]
            simp only [Set.mem_iUnion]
            refine ⟨k, hk, ?_⟩
            have hcroot :
                (1 + (2 : ℝ) ^ k * sab) * Real.sqrt (b.val x) ≤
                  Real.sqrt (a.val x) := by
              dsimp [z] at hck
              rw [le_sub_iff_add_le, le_div_iff₀ hvpos] at hck
              simpa [add_comm] using hck
            have hcroot_upper :
                Real.sqrt (a.val x) <
                  (1 + 2 * ((2 : ℝ) ^ k * sab)) *
                    Real.sqrt (b.val x) := by
              dsimp [z] at hkc
              rw [sub_lt_iff_lt_add, div_lt_iff₀ hvpos] at hkc
              rw [pow_succ] at hkc
              simpa [mul_assoc, mul_left_comm, mul_comm, add_comm] using hkc
            have hc0 : 0 ≤ (2 : ℝ) ^ k * sab := by positivity
            have hcr0 :
                0 ≤ (1 + (2 : ℝ) ^ k * sab) *
                  Real.sqrt (b.val x) := by positivity
            have hcru0 :
                0 ≤ (1 + 2 * ((2 : ℝ) ^ k * sab)) *
                  Real.sqrt (b.val x) := by positivity
            refine ⟨?_, ?_, hab4⟩
            · have hsquares := (sq_le_sq₀ hcr0 hu0).2 hcroot
              rw [mul_pow, hvb, hua] at hsquares
              exact hsquares
            · have hsquares :=
                (sq_lt_sq₀ hu0 hcru0).2 hcroot_upper
              rw [mul_pow, hvb, hua] at hsquares
              exact hsquares
        have hU_integral :
            ∫ x in N ∪ BU ∪ Z,
                (Real.sqrt (a.val x) - Real.sqrt (b.val x)) ^ 2 ∂μ =
              (∫ x in N,
                  (Real.sqrt (a.val x) - Real.sqrt (b.val x)) ^ 2 ∂μ) +
                (∫ x in BU,
                  (Real.sqrt (a.val x) - Real.sqrt (b.val x)) ^ 2 ∂μ) +
                ∫ x in Z,
                  (Real.sqrt (a.val x) - Real.sqrt (b.val x)) ^ 2 ∂μ := by
          rw [MeasureTheory.setIntegral_union
            (hNZ.union_left hBUZ) hZ
            (hhellinger_integrable a b).integrableOn
            (hhellinger_integrable a b).integrableOn]
          rw [MeasureTheory.setIntegral_union hNBU hBU_measurable
            (hhellinger_integrable a b).integrableOn
            (hhellinger_integrable a b).integrableOn]
        have hordered_integral :
            ∫ x in {x | b.val x ≤ a.val x},
                (Real.sqrt (a.val x) - Real.sqrt (b.val x)) ^ 2 ∂μ ≤
              ∫ x in N ∪ BU ∪ Z,
                (Real.sqrt (a.val x) - Real.sqrt (b.val x)) ^ 2 ∂μ := by
          exact MeasureTheory.setIntegral_mono_set
            (hhellinger_integrable a b).integrableOn
            (Filter.Eventually.of_forall (fun x => sq_nonneg _))
            (Filter.Eventually.of_forall hcover)
        have hyab_bound :
            yab ≤ yab / 4 + 8 * ((nab : ℝ) + 2) * Dab := by
          have hfinal :
              ∫ x in Z,
                  (Real.sqrt (a.val x) - Real.sqrt (b.val x)) ^ 2 ∂μ ≤
                8 * Dab := by
            simpa [Z] using hfinal_integral
          change yab ≤
            ∫ x in {x | b.val x ≤ a.val x},
              (Real.sqrt (a.val x) - Real.sqrt (b.val x)) ^ 2 ∂μ at hside_ab
          calc
            yab ≤ ∫ x in {x | b.val x ≤ a.val x},
                (Real.sqrt (a.val x) - Real.sqrt (b.val x)) ^ 2 ∂μ :=
              hside_ab
            _ ≤ ∫ x in N ∪ BU ∪ Z,
                (Real.sqrt (a.val x) - Real.sqrt (b.val x)) ^ 2 ∂μ :=
              hordered_integral
            _ = (∫ x in N,
                    (Real.sqrt (a.val x) - Real.sqrt (b.val x)) ^ 2 ∂μ) +
                  (∫ x in BU,
                    (Real.sqrt (a.val x) - Real.sqrt (b.val x)) ^ 2 ∂μ) +
                  ∫ x in Z,
                    (Real.sqrt (a.val x) - Real.sqrt (b.val x)) ^ 2 ∂μ :=
              hU_integral
            _ ≤ yab / 4 + 8 * ((nab : ℝ) + 1) * Dab + 8 * Dab := by
              gcongr
            _ = yab / 4 + 8 * ((nab : ℝ) + 2) * Dab := by ring
        have hDab_nonneg : 0 ≤ Dab := by
          dsimp [Dab, Pa, Pb]
          exact hDab0
        have hnLab : (nab : ℝ) + 2 ≤ (5 : ℝ) / 2 * Lab := by
          have hfirst : (nab : ℝ) + 2 < Lab + 3 := by
            linarith only [hncast]
          have hsecond : Lab + 3 ≤ (5 : ℝ) / 2 * Lab := by
            linarith only [hLab]
          exact (le_of_lt hfirst).trans hsecond
        have hcoefficient :
            8 * ((nab : ℝ) + 2) * Dab ≤ 20 * Lab * Dab := by
          calc
            8 * ((nab : ℝ) + 2) * Dab ≤
                8 * ((5 : ℝ) / 2 * Lab) * Dab := by gcongr
            _ = 20 * Lab * Dab := by ring
        have hyab_final : yab ≤ 50 * Lab * Dab := by
          have hrough :
              yab ≤ yab / 4 + 20 * Lab * Dab :=
            hyab_bound.trans (add_le_add (le_refl (yab / 4)) hcoefficient)
          have hLD : 0 ≤ Lab * Dab :=
            mul_nonneg (le_trans (by norm_num) hLab) hDab_nonneg
          linarith only [hrough, hLD]
        change yab / (50 * Lab) ≤ Dab
        apply (div_le_iff₀ (by positivity : 0 < 50 * Lab)).2
        simpa [mul_assoc, mul_left_comm, mul_comm] using hyab_final
    let A : Set Ω := {x | q.val x ≤ p.val x}
    have hA : MeasurableSet A :=
      measurableSet_le q.measurable_val p.measurable_val
    have hsplit :
        (∫ x in A,
            (Real.sqrt (p.val x) - Real.sqrt (q.val x)) ^ (2 : ℕ) ∂μ) +
          (∫ x in Aᶜ,
            (Real.sqrt (p.val x) - Real.sqrt (q.val x)) ^ (2 : ℕ) ∂μ) =
          2 * squared_hellinger p q := by
      rw [MeasureTheory.integral_add_compl hA (hhellinger_integrable p q)]
      rw [squared_hellinger]
      ring
    have hleft0 : 0 ≤
        ∫ x in A,
          (Real.sqrt (p.val x) - Real.sqrt (q.val x)) ^ (2 : ℕ) ∂μ :=
      MeasureTheory.setIntegral_nonneg_of_ae
        (Filter.Eventually.of_forall (fun x => sq_nonneg _))
    have hright0 : 0 ≤
        ∫ x in Aᶜ,
          (Real.sqrt (p.val x) - Real.sqrt (q.val x)) ^ (2 : ℕ) ∂μ :=
      MeasureTheory.setIntegral_nonneg_of_ae
        (Filter.Eventually.of_forall (fun x => sq_nonneg _))
    have hside :
        squared_hellinger p q ≤
            ∫ x in A,
              (Real.sqrt (p.val x) - Real.sqrt (q.val x)) ^ (2 : ℕ) ∂μ ∨
          squared_hellinger p q ≤
            ∫ x in Aᶜ,
              (Real.sqrt (p.val x) - Real.sqrt (q.val x)) ^ (2 : ℕ) ∂μ := by
      by_contra h
      push Not at h
      nlinarith
    rcases hside with hleft | hright
    · exact hordered p q hp hq (by simpa [A] using hleft)
    · have hsq_symm :
          squared_hellinger q p = squared_hellinger p q := by
        unfold squared_hellinger
        congr 1
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        ring
      let B : Set Ω := {x | p.val x ≤ q.val x}
      have hB : MeasurableSet B :=
        measurableSet_le p.measurable_val q.measurable_val
      have hAcB : Aᶜ ⊆ B := by
        intro x hx
        change ¬q.val x ≤ p.val x at hx
        change p.val x ≤ q.val x
        exact le_of_lt (lt_of_not_ge hx)
      have hcomp_swap :
          (∫ x in Aᶜ,
              (Real.sqrt (p.val x) - Real.sqrt (q.val x)) ^ 2 ∂μ) =
            ∫ x in Aᶜ,
              (Real.sqrt (q.val x) - Real.sqrt (p.val x)) ^ 2 ∂μ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        ring
      have hcomp_mono :
          (∫ x in Aᶜ,
              (Real.sqrt (q.val x) - Real.sqrt (p.val x)) ^ 2 ∂μ) ≤
            ∫ x in B,
              (Real.sqrt (q.val x) - Real.sqrt (p.val x)) ^ 2 ∂μ := by
        exact MeasureTheory.setIntegral_mono_set
          (hhellinger_integrable q p).integrableOn
          (Filter.Eventually.of_forall (fun x => sq_nonneg _))
          (Filter.Eventually.of_forall hAcB)
      have hside_qp :
          squared_hellinger q p ≤
            ∫ x in {x | p.val x ≤ q.val x},
              (Real.sqrt (q.val x) - Real.sqrt (p.val x)) ^ 2 ∂μ := by
        calc
          squared_hellinger q p = squared_hellinger p q := hsq_symm
          _ ≤ ∫ x in Aᶜ,
              (Real.sqrt (p.val x) - Real.sqrt (q.val x)) ^ 2 ∂μ := hright
          _ = ∫ x in Aᶜ,
              (Real.sqrt (q.val x) - Real.sqrt (p.val x)) ^ 2 ∂μ := hcomp_swap
          _ ≤ ∫ x in B,
              (Real.sqrt (q.val x) - Real.sqrt (p.val x)) ^ 2 ∂μ := hcomp_mono
          _ = ∫ x in {x | p.val x ≤ q.val x},
              (Real.sqrt (q.val x) - Real.sqrt (p.val x)) ^ 2 ∂μ := by
            rfl
      have hreverse := hordered q p hq hp hside_qp
      calc
        squared_hellinger p q /
              (50 * binary_logarithm (4 / squared_hellinger p q)) =
            squared_hellinger q p /
              (50 * binary_logarithm (4 / squared_hellinger q p)) := by
                rw [hsq_symm]
        _ ≤ modified_hellinger_distance (ratio_concept_class F)
              q.toProbabilityMeasure p.toProbabilityMeasure := hreverse
        _ = modified_hellinger_distance (ratio_concept_class F)
              p.toProbabilityMeasure q.toProbabilityMeasure :=
            (modified_hellinger_symm (ratio_concept_class F)
              p.toProbabilityMeasure q.toProbabilityMeasure).symm

@[blueprint "lem:model-pair-hellinger-bound"
  (statement := /-- Let $(\Omega,\mathcal A)$ be a measurable space, let $\mu$ be a measure on $\Omega$, and let $\mathcal F$ be a family of Hellinger densities relative to $\mu$. For every $p,q\in\mathcal F$, let $P_p$ and $P_q$ denote their induced probability measures. Then
  \[
    H^2(p,q)\leq
      100z\bigl(d_{\operatorname{Ratio}(\mathcal F)}(P_p,P_q)\bigr).
  \] -/)
  (proof := /-- The reverse inequality in \cref{lem:reverse-data-processing-ratio-class} supplies the hypothesis of \cref{lem:move-log-across-reverse-bound}. The range assumptions required there follow from \cref{lem:squared-hellinger-range}, \cref{lem:modified-hellinger-range}, and the unit-mass identity \cref{lem:density-measure-univ}. Applying the scalar lemma gives the result. -/)
  (title := /-- Upper-bounding model-pair Hellinger loss by modified distance -/)
  (latexEnv := "lemma")]
lemma model_pair_hellinger_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {F : Set (hellinger_density Ω μ)}
    {p q : hellinger_density Ω μ} (hp : p ∈ F) (hq : q ∈ F) :
    squared_hellinger p q ≤
      100 * entropy_envelope
        (modified_hellinger_distance (ratio_concept_class F)
          p.toProbabilityMeasure q.toProbabilityMeasure) := by
  rcases squared_hellinger_range p q with ⟨hy0, hy1⟩
  rcases modified_hellinger_range (ratio_concept_class F)
      p.toProbabilityMeasure q.toProbabilityMeasure
      (density_measure_univ p) (density_measure_univ q) with ⟨hx0, hx1⟩
  exact move_log_across_reverse_bound hx0 hx1 hy0 hy1
    (reverse_data_processing_ratio_class hp hq)

@[blueprint "lem:hellinger-loss-reduction"
  (statement := /-- Let $(\Omega,\mathcal A)$ be a measurable space, let $\mu$ be a measure on $\Omega$, and let $\mathcal F$ be a family of Hellinger densities relative to $\mu$. For every Hellinger density $f$ relative to $\mu$ and every $g,\widehat f\in\mathcal F$, let $P_g$ and $P_{\widehat f}$ be the probability measures induced by $g$ and $\widehat f$, respectively. Then
  \[
    H^2(f,\widehat f)
      \leq2H^2(f,g)+
        200z\bigl(d_{\operatorname{Ratio}(\mathcal F)}(P_g,P_{\widehat f})\bigr).
  \] -/)
  (proof := /-- Apply \cref{lem:squared-hellinger-approx-triangle} through the intermediate density $g$. Since both $g$ and $\widehat f$ lie in the model, \cref{lem:model-pair-hellinger-bound} bounds the second squared Hellinger term. Multiplying that estimate by the factor two from the approximate triangle inequality gives the coefficient $200$. -/)
  (title := /-- Reduction of estimator loss to a model-pair modified distance -/)
  (latexEnv := "lemma")]
lemma hellinger_loss_reduction {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {F : Set (hellinger_density Ω μ)}
    (f g hatf : hellinger_density Ω μ) (hg : g ∈ F) (hhat : hatf ∈ F) :
    squared_hellinger f hatf ≤
      2 * squared_hellinger f g +
        200 * entropy_envelope
          (modified_hellinger_distance (ratio_concept_class F)
            g.toProbabilityMeasure hatf.toProbabilityMeasure) := by
  linarith [squared_hellinger_approx_triangle f g hatf,
    model_pair_hellinger_bound hg hhat]

@[blueprint "lem:minimum-distance-entropy-bound"
  (statement := /-- Let $(\Omega,\mathcal A)$ be a measurable space, let $\mu$ be a measure on $\Omega$, and let $\mathcal F$ be a family of Hellinger densities relative to $\mu$. Let $n\geq2$ and $0\leq\varepsilon\leq1$, and let $\widehat f$ be an $\varepsilon$-approximate minimum-distance estimator for the ratio class of $\mathcal F$. For every Hellinger density $f$ relative to $\mu$, every sample $x\colon\operatorname{Fin}(n)\to\Omega$, and every $g\in\mathcal F$,
  \[
  z\bigl(d_{\mathcal H}(g,\widehat f(x))\bigr)
    \leq10z\bigl(d_{\mathcal H}(f,g)\bigr)
      +12z\bigl(d_{\mathcal H}(f,P_x)\bigr)
      +4z(\varepsilon),
  \quad \mathcal H=\operatorname{Ratio}(\mathcal F).
  \] -/)
  (proof := /-- Apply \cref{lem:modified-hellinger-approx-triangle} first through $f$ and then through the empirical measure $P_x$. Each approximate triangle inequality is converted to an entropy inequality by \cref{lem:entropy-envelope-approx-subadd}; the range hypotheses follow from \cref{lem:modified-hellinger-range}, using \cref{lem:density-measure-univ} and \cref{lem:empirical-measure-univ}. The approximate minimum-distance property gives $d_{\mathcal H}(P_x,\widehat f(x))\leq d_{\mathcal H}(P_x,g)+\varepsilon$. Apply \cref{lem:entropy-envelope-subadd} to this additional sum, using $0\leq\varepsilon\leq1$, and apply the approximate triangle inequality to $d_{\mathcal H}(P_x,g)$ through $f$, using symmetry from \cref{lem:modified-hellinger-symm}. Collecting the resulting terms yields the coefficients $10$, $12$, and $4$. -/)
  (title := /-- Deterministic entropy estimate for an approximate minimum-distance estimator -/)
  (latexEnv := "lemma")]
lemma minimum_distance_entropy_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {n : ℕ} (hn : 2 ≤ n)
    {F : Set (hellinger_density Ω μ)} {ε : ℝ} (hε1 : ε ≤ 1)
    {hat : (Fin n → Ω) → hellinger_density Ω μ}
    (hhat : is_approximate_minimum_distance_estimator n
      (ratio_concept_class F) F ε hat)
    (f : hellinger_density Ω μ) (x : Fin n → Ω)
    (g : hellinger_density Ω μ) (hg : g ∈ F) :
    entropy_envelope
        (modified_hellinger_distance (ratio_concept_class F)
          g.toProbabilityMeasure (hat x).toProbabilityMeasure) ≤
      10 * entropy_envelope
        (modified_hellinger_distance (ratio_concept_class F)
          f.toProbabilityMeasure g.toProbabilityMeasure) +
      12 * entropy_envelope
        (modified_hellinger_distance (ratio_concept_class F)
          f.toProbabilityMeasure (empirical_measure n x)) +
      4 * entropy_envelope ε := by
  have hn0 : 0 < n := by omega
  have hε0 : 0 ≤ ε := hhat.1
  have hf_mass := density_measure_univ f
  have hg_mass := density_measure_univ g
  have hhat_mass := density_measure_univ (hat x)
  have hx_mass := empirical_measure_univ hn0 x
  have h_g_hat_range := modified_hellinger_range (ratio_concept_class F)
    g.toProbabilityMeasure (hat x).toProbabilityMeasure hg_mass hhat_mass
  have h_g_f_range := modified_hellinger_range (ratio_concept_class F)
    g.toProbabilityMeasure f.toProbabilityMeasure hg_mass hf_mass
  have h_f_g_range := modified_hellinger_range (ratio_concept_class F)
    f.toProbabilityMeasure g.toProbabilityMeasure hf_mass hg_mass
  have h_f_hat_range := modified_hellinger_range (ratio_concept_class F)
    f.toProbabilityMeasure (hat x).toProbabilityMeasure hf_mass hhat_mass
  have h_f_x_range := modified_hellinger_range (ratio_concept_class F)
    f.toProbabilityMeasure (empirical_measure n x) hf_mass hx_mass
  have h_x_f_range := modified_hellinger_range (ratio_concept_class F)
    (empirical_measure n x) f.toProbabilityMeasure hx_mass hf_mass
  have h_x_g_range := modified_hellinger_range (ratio_concept_class F)
    (empirical_measure n x) g.toProbabilityMeasure hx_mass hg_mass
  have h_x_hat_range := modified_hellinger_range (ratio_concept_class F)
    (empirical_measure n x) (hat x).toProbabilityMeasure hx_mass hhat_mass
  have htri_g_hat := modified_hellinger_approx_triangle
    (ratio_concept_class F) g.toProbabilityMeasure f.toProbabilityMeasure
    (hat x).toProbabilityMeasure hg_mass hf_mass hhat_mass
  have htri_f_hat := modified_hellinger_approx_triangle
    (ratio_concept_class F) f.toProbabilityMeasure (empirical_measure n x)
    (hat x).toProbabilityMeasure hf_mass hx_mass hhat_mass
  have htri_x_g := modified_hellinger_approx_triangle
    (ratio_concept_class F) (empirical_measure n x) f.toProbabilityMeasure
    g.toProbabilityMeasure hx_mass hf_mass hg_mass
  have houter := entropy_envelope_approx_subadd
    h_g_hat_range.1 h_g_hat_range.2 h_g_f_range.1 h_g_f_range.2
    h_f_hat_range.1 h_f_hat_range.2 htri_g_hat
  have hsecond := entropy_envelope_approx_subadd
    h_f_hat_range.1 h_f_hat_range.2 h_f_x_range.1 h_f_x_range.2
    h_x_hat_range.1 h_x_hat_range.2 htri_f_hat
  have hmin := (hhat.2 x).2 g hg
  have hmin_entropy := entropy_envelope_subadd
    h_x_hat_range.1 h_x_hat_range.2 h_x_g_range.1 h_x_g_range.2
    hε0 hε1 hmin
  have hxg_entropy := entropy_envelope_approx_subadd
    h_x_g_range.1 h_x_g_range.2 h_x_f_range.1 h_x_f_range.2
    h_f_g_range.1 h_f_g_range.2 htri_x_g
  rw [modified_hellinger_symm (ratio_concept_class F)
    g.toProbabilityMeasure f.toProbabilityMeasure] at houter
  rw [modified_hellinger_symm (ratio_concept_class F)
    (empirical_measure n x) f.toProbabilityMeasure] at hxg_entropy
  linarith

@[blueprint "lem:deterministic-estimator-oracle-bound"
  (statement := /-- Let $(\Omega,\mathcal A,\mu)$ be a measure space, let
  $n\geq2$, let $\mathcal F$ be a family of Hellinger densities relative to
  $\mu$, and let $0\leq\varepsilon\leq1$. Suppose that $\widehat f$ maps
  samples $x\colon\operatorname{Fin}(n)\to\Omega$ to Hellinger densities
  relative to $\mu$ and is an $\varepsilon$-approximate minimum-distance
  estimator over $\mathcal F$ with respect to
  $\mathcal H=\operatorname{Ratio}(\mathcal F)$. Then every
  Hellinger density $f$ relative to $\mu$, every sample
  $x\colon\operatorname{Fin}(n)\to\Omega$, and every $g\in\mathcal F$ satisfy
  \[
    H^2(f,\widehat f(x))
      \leq2002z\bigl(H^2(f,g)\bigr)
        +2400z\bigl(d_{\mathcal H}(f,P_x)\bigr)
        +800z(\varepsilon).
  \] -/)
  (proof := /-- Start with \cref{lem:hellinger-loss-reduction} and substitute \cref{lem:minimum-distance-entropy-bound}. By \cref{lem:modified-distance-le-squared-hellinger}, monotonicity from \cref{lem:entropy-envelope-monotone}, and the ranges in \cref{lem:squared-hellinger-range} and \cref{lem:modified-hellinger-range}, the model modified-distance term is at most $z(H^2(f,g))$. Finally, \cref{lem:entropy-envelope-dominates} absorbs the remaining $2H^2(f,g)$ into $2z(H^2(f,g))$, giving the coefficient $2002$; multiplying the empirical and slack coefficients $12$ and $4$ in \cref{lem:minimum-distance-entropy-bound} by $200$ gives $2400$ and $800$, respectively. -/)
  (title := /-- Deterministic oracle inequality -/)
  (latexEnv := "lemma")]
lemma deterministic_estimator_oracle_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {n : ℕ} (hn : 2 ≤ n)
    {F : Set (hellinger_density Ω μ)} {ε : ℝ} (hε1 : ε ≤ 1)
    {hat : (Fin n → Ω) → hellinger_density Ω μ}
    (hhat : is_approximate_minimum_distance_estimator n
      (ratio_concept_class F) F ε hat)
    (f : hellinger_density Ω μ) (x : Fin n → Ω)
    (g : hellinger_density Ω μ) (hg : g ∈ F) :
    squared_hellinger f (hat x) ≤
      2002 * entropy_envelope (squared_hellinger f g) +
      2400 * entropy_envelope
        (modified_hellinger_distance (ratio_concept_class F)
          f.toProbabilityMeasure (empirical_measure n x)) +
      800 * entropy_envelope ε := by
  have h_loss := hellinger_loss_reduction f g (hat x) hg (hhat.2 x).1
  have h_min := minimum_distance_entropy_bound hn hε1 hhat f x g hg
  have h_sq_range := squared_hellinger_range f g
  have h_mod_range := modified_hellinger_range (ratio_concept_class F)
    f.toProbabilityMeasure g.toProbabilityMeasure
    f.toProbabilityMeasure.prop.measure_univ
    g.toProbabilityMeasure.prop.measure_univ
  have h_mod_le_sq := modified_distance_le_squared_hellinger F f g
  have h_entropy_le := entropy_envelope_monotone
    h_mod_range h_sq_range h_mod_le_sq
  have h_sq_le_entropy := entropy_envelope_dominates
    h_sq_range.1 h_sq_range.2
  linarith

@[blueprint "lem:ratio-concept-event-measurable"
  (statement := /-- Let $(\Omega,\mathcal A,\mu)$ be a measure space and let $\mathcal F$ be a family of Hellinger densities relative to $\mu$. For every $h\in\operatorname{Ratio}(\mathcal F)$, the event
  \[
    \{x\in\Omega:h(x)=\mathrm{true}\}
  \]
  is measurable. -/)
  (proof := /-- Unfolding \cref{def:ratio-concept-class, def:concept-event}, there exist $p,q\in\mathcal F$ and $\tau\in\mathbb R$ such that
  \[
    \{x:h(x)=\mathrm{true}\}=\{x:\tau q(x)\leq p(x)\}.
  \]
  The functions $p$ and $q$ are measurable by \cref{def:hellinger-density}; hence $x\mapsto\tau q(x)$ is measurable, and the displayed sublevel set is measurable. -/)
  (title := /-- Measurability of ratio-concept events -/)
  (latexEnv := "lemma")]
lemma ratio_concept_event_measurable {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} (F : Set (hellinger_density Ω μ))
    (h : Ω → Bool) (hh : h ∈ ratio_concept_class F) :
    MeasurableSet (concept_event h) := by
  rcases hh with ⟨p, hp, q, hq, τ, rfl⟩
  unfold concept_event
  simpa using measurableSet_le (q.measurable_val.const_mul τ) p.measurable_val

@[blueprint "lem:normalized-vc-partial-binomial-sum-bound"
  (statement := /-- For all natural numbers $m$ and $d$,
  \[
    \sum_{k=0}^{d}\binom{m}{k}\leq(m+1)^d.
  \] -/)
  (proof := /-- Induct on $d$. The case $d=0$ is immediate. For the induction step, split off $\binom{m}{d+1}$, bound it by $m^{d+1}$, and use $m^d\leq(m+1)^d$. Adding this estimate to the induction hypothesis gives
  \[
    (m+1)^d+m(m+1)^d=(m+1)^{d+1}.
  \] -/)
  (title := /-- A polynomial bound for partial binomial sums -/)
  (latexEnv := "lemma")]
lemma normalized_vc_partial_binomial_sum_bound (m d : ℕ) :
    (∑ k ∈ Finset.range (d + 1), m.choose k) ≤ (m + 1) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [show d.succ + 1 = (d + 1) + 1 by omega,
        Finset.sum_range_succ]
      have hchoose : m.choose (d + 1) ≤ m ^ (d + 1) :=
        Nat.choose_le_pow m (d + 1)
      have hpow : m ^ (d + 1) ≤ m * (m + 1) ^ d := by
        rw [pow_succ, mul_comm (m ^ d) m]
        gcongr
        omega
      calc
        (∑ k ∈ Finset.range (d + 1), m.choose k) + m.choose (d + 1)
            ≤ (m + 1) ^ d + m ^ (d + 1) := Nat.add_le_add ih hchoose
        _ ≤ (m + 1) ^ d + m * (m + 1) ^ d := Nat.add_le_add_left hpow _
        _ = (m + 1) ^ d.succ := by rw [pow_succ]; ring

@[blueprint "lem:normalized-vc-trace-cardinality-bound"
  (statement := /-- Let $\mathcal H$ be a Boolean concept class of VC dimension $d$. On every finite set $W$, the number of distinct traces induced by $\mathcal H$ is at most $(|W|+1)^d$. -/)
  (proof := /-- Form the finite family of all traces on $W$. Every set shattered by this trace family is also shattered by $\mathcal H$, so its cardinality is at most $d$ by \cref{def:has-vc-dimension}. The Sauer--Shelah lemma bounds the number of traces by the partial binomial sum, and \cref{lem:normalized-vc-partial-binomial-sum-bound} bounds that sum by $(|W|+1)^d$. -/)
  (title := /-- Polynomial growth of VC traces -/)
  (latexEnv := "lemma")]
lemma normalized_vc_trace_cardinality_bound {Ω : Type*}
    (H : concept_class Ω) {d : ℕ} (hvc : has_vc_dimension H d)
    (W : Finset Ω) :
    (@Finset.filter (Finset ↥W)
      (fun s => ∃ h ∈ H, ∀ x : ↥W, x ∈ s ↔ h x = true)
      (Classical.decPred _) Finset.univ).card ≤
      (W.card + 1) ^ d := by
  classical
  let A : Finset (Finset ↥W) := Finset.univ.filter fun s =>
    ∃ h ∈ H, ∀ x : ↥W, x ∈ s ↔ h x = true
  change A.card ≤ (W.card + 1) ^ d
  have hdim : A.vcDim ≤ d := by
    rw [Finset.vcDim]
    apply Finset.sup_le
    intro s hs
    have hsh : A.Shatters s := Finset.mem_shatterer.mp hs
    let U : Finset Ω := s.image fun x : ↥W => (x : Ω)
    have hUcard : U.card = s.card :=
      Finset.card_image_of_injective s Subtype.val_injective
    have hU : set_shatters H (U : Set Ω) := by
      intro U' hU'
      let t : Finset ↥W := s.filter fun x => (x : Ω) ∈ U'
      have hts : t ⊆ s := Finset.filter_subset _ _
      obtain ⟨u, huA, hsu⟩ := hsh hts
      obtain ⟨h, hh, hu⟩ : ∃ h ∈ H, ∀ x : ↥W, x ∈ u ↔ h x = true := by
        simpa [A] using huA
      refine ⟨h, hh, ?_⟩
      ext x
      change (h x = true ∧ x ∈ U) ↔ x ∈ U'
      constructor
      · rintro ⟨hxtrue, hxU⟩
        rcases Finset.mem_image.mp hxU with ⟨y, hys, rfl⟩
        have hyu : y ∈ u := (hu y).2 hxtrue
        have hyinter : y ∈ s ∩ u := Finset.mem_inter.mpr ⟨hys, hyu⟩
        rw [hsu] at hyinter
        exact (Finset.mem_filter.mp hyinter).2
      · intro hxU'
        have hxU : x ∈ U := hU' hxU'
        rcases Finset.mem_image.mp hxU with ⟨y, hys, rfl⟩
        have hyt : y ∈ t := Finset.mem_filter.mpr ⟨hys, hxU'⟩
        have hyinter : y ∈ s ∩ u := by simpa [hsu] using hyt
        exact ⟨(hu y).1 (Finset.mem_inter.mp hyinter).2,
          Finset.mem_image.mpr ⟨y, hys, rfl⟩⟩
    have hmem : U.card ∈ shattered_cardinalities H := ⟨U, rfl, hU⟩
    have hle : U.card ≤ sSup (shattered_cardinalities H) :=
      le_csSup hvc.1 hmem
    rw [hvc.2] at hle
    simpa [hUcard] using hle
  have hsubset : Finset.Iic A.vcDim ⊆ Finset.range (d + 1) := by
    intro k hk
    simp only [Finset.mem_Iic] at hk
    simp only [Finset.mem_range]
    omega
  calc
    A.card ≤ A.shatterer.card := Finset.card_le_card_shatterer A
    _ ≤ ∑ k ∈ Finset.Iic A.vcDim, (Fintype.card ↥W).choose k :=
      A.card_shatterer_le_sum_vcDim
    _ ≤ ∑ k ∈ Finset.range (d + 1), W.card.choose k := by
      simpa using Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ => Nat.zero_le _)
    _ ≤ (W.card + 1) ^ d :=
      normalized_vc_partial_binomial_sum_bound W.card d

@[blueprint "lem:normalized-vc-exponential-budget"
  (statement := /-- If $n\geq2$, $d\geq1$, and $0<\delta<1$, and
  \[
    A=d\log(2n+1)+\log(8/\delta),
  \]
  then
  \[
    8(2n+1)^d\exp\!\left(-\frac{(4\sqrt A)^2}{16}\right)=\delta.
  \] -/)
  (proof := /-- Both $2n+1$ and $8/\delta$ are greater than one, so $A$ is nonnegative and the square of $\sqrt A$ is $A$. The exponential addition, natural-logarithm, and natural-power identities give
  \[
    e^A=(2n+1)^d(8/\delta).
  \]
  Substitution and cancellation yield the asserted identity. -/)
  (title := /-- Evaluation of the VC exponential budget -/)
  (latexEnv := "lemma")]
lemma normalized_vc_exponential_budget {n d : ℕ} {δ : ℝ}
    (hn : 2 ≤ n) (hd : 1 ≤ d) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    8 * (2 * (n : ℝ) + 1) ^ d *
        Real.exp (-(4 * Real.sqrt
          ((d : ℝ) * Real.log (2 * (n : ℝ) + 1) +
            Real.log (8 / δ))) ^ 2 / 16) = δ := by
  let B : ℝ := 2 * (n : ℝ) + 1
  let C : ℝ := 8 / δ
  let A : ℝ := (d : ℝ) * Real.log B + Real.log C
  have hB : 0 < B := by simp [B]; positivity
  have hBone : 1 < B := by simp [B]; positivity
  have hC : 0 < C := div_pos (by norm_num) hδ0
  have hCone : 1 < C := by
    change 1 < 8 / δ
    rw [one_lt_div hδ0]
    linarith
  have hA : 0 ≤ A := by
    change 0 ≤ (d : ℝ) * Real.log B + Real.log C
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg d) (Real.log_nonneg hBone.le))
      (Real.log_nonneg hCone.le)
  have hsquare : (4 * Real.sqrt A) ^ 2 / 16 = A := by
    rw [mul_pow, Real.sq_sqrt hA]
    ring
  have hneg : -(4 * Real.sqrt A) ^ 2 / 16 = -A := by
    rw [neg_div, hsquare]
  have hexpA : Real.exp A = B ^ d * C := by
    change Real.exp ((d : ℝ) * Real.log B + Real.log C) = B ^ d * C
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hB,
      Real.exp_log hC]
  change 8 * B ^ d * Real.exp (-(4 * Real.sqrt A) ^ 2 / 16) = δ
  rw [hneg, Real.exp_neg, hexpA]
  field_simp [ne_of_gt hB, ne_of_gt hC]
  change 8 = (8 / δ) * δ
  field_simp [ne_of_gt hδ0]

@[blueprint "lem:normalized-vc-weighted-sign-mgf"
  (statement := /-- For every finite real vector $(a_i)_{i=1}^n$ and every $t\in\mathbb R$, the uniform sign average satisfies
  \[
    2^{-n}\sum_{\sigma\in\{-1,1\}^n}
      \exp\!\left(t\sum_i\sigma_i a_i\right)
      \leq \exp\!\left(\frac{t^2}{2}\sum_i a_i^2\right).
  \] -/)
  (proof := /-- Rewrite the exponential of the signed sum as a product and exchange the sum over sign vectors with the product over coordinates. For each coordinate, the elementary inequality $e^u+e^{-u}\leq2e^{u^2/2}$ bounds its two-point exponential average. Multiplying these bounds, cancelling the factor $2^n$, and combining the product of exponentials proves the claim. -/)
  (title := /-- MGF bound for a weighted Rademacher sum -/)
  (latexEnv := "lemma")]
lemma normalized_vc_weighted_sign_mgf {n : ℕ} (a : Fin n → ℝ) (t : ℝ) :
    ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
        Real.exp (t * ∑ i : Fin n,
          (if σ i = true then (1 : ℝ) else -1) * a i) ≤
      Real.exp (t ^ 2 * (∑ i : Fin n, a i ^ 2) / 2) := by
  have hexp : ∀ σ : Fin n → Bool,
      Real.exp (t * ∑ i : Fin n,
        (if σ i = true then (1 : ℝ) else -1) * a i) =
        ∏ i : Fin n, Real.exp
          (t * (if σ i = true then (1 : ℝ) else -1) * a i) := by
    intro σ
    rw [show t * ∑ i : Fin n,
        (if σ i = true then (1 : ℝ) else -1) * a i =
      ∑ i : Fin n, t * (if σ i = true then (1 : ℝ) else -1) * a i by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring,
      Real.exp_sum]
  simp_rw [hexp]
  rw [show ∑ σ : Fin n → Bool, ∏ i : Fin n,
      Real.exp (t * (if σ i = true then (1 : ℝ) else -1) * a i) =
      ∏ i : Fin n, ∑ b : Bool,
        Real.exp (t * (if b = true then (1 : ℝ) else -1) * a i) by
    rw [← Fintype.prod_sum (fun i (b : Bool) =>
      Real.exp (t * (if b = true then (1 : ℝ) else -1) * a i))]]
  have hcoord : ∀ i : Fin n,
      ∑ b : Bool, Real.exp
          (t * (if b = true then (1 : ℝ) else -1) * a i) ≤
        2 * Real.exp (t ^ 2 * a i ^ 2 / 2) := by
    intro i
    have hcosh := Real.cosh_le_exp_half_sq (t * a i)
    have hsum : ∑ b : Bool, Real.exp
        (t * (if b = true then (1 : ℝ) else -1) * a i) =
        Real.exp (t * a i) + Real.exp (-(t * a i)) := by
      simp only [Fintype.sum_bool, if_pos, Bool.false_eq_true, if_false]
      ring_nf
    rw [hsum]
    rw [Real.cosh_eq] at hcosh
    calc
      Real.exp (t * a i) + Real.exp (-(t * a i)) =
          2 * ((Real.exp (t * a i) + Real.exp (-(t * a i))) / 2) := by ring
      _ ≤ 2 * Real.exp ((t * a i) ^ 2 / 2) := by gcongr
      _ = 2 * Real.exp (t ^ 2 * a i ^ 2 / 2) := by ring_nf
  have hprod :
      ∏ i : Fin n, ∑ b : Bool,
          Real.exp (t * (if b = true then (1 : ℝ) else -1) * a i) ≤
        ∏ i : Fin n, 2 * Real.exp (t ^ 2 * a i ^ 2 / 2) :=
    Finset.prod_le_prod
      (fun i _ => Finset.sum_nonneg fun b _ => (Real.exp_pos _).le)
      (fun i _ => hcoord i)
  calc
    ((2 : ℝ) ^ n)⁻¹ * ∏ i : Fin n, ∑ b : Bool,
        Real.exp (t * (if b = true then (1 : ℝ) else -1) * a i)
        ≤ ((2 : ℝ) ^ n)⁻¹ * ∏ i : Fin n,
          2 * Real.exp (t ^ 2 * a i ^ 2 / 2) := by gcongr
    _ = ∏ i : Fin n, Real.exp (t ^ 2 * a i ^ 2 / 2) := by
      rw [Finset.prod_mul_distrib]
      simp [Finset.prod_const]
    _ = Real.exp (∑ i : Fin n, t ^ 2 * a i ^ 2 / 2) :=
      (Real.exp_sum Finset.univ _).symm
    _ = Real.exp (t ^ 2 * (∑ i : Fin n, a i ^ 2) / 2) := by
      congr 1
      calc
        (∑ i : Fin n, t ^ 2 * a i ^ 2 / 2) =
            ∑ i : Fin n, (t ^ 2 / 2) * a i ^ 2 := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = (t ^ 2 / 2) * ∑ i : Fin n, a i ^ 2 := by
          rw [Finset.mul_sum]
        _ = t ^ 2 * (∑ i : Fin n, a i ^ 2) / 2 := by ring

@[blueprint "lem:normalized-vc-weighted-sign-tail"
  (statement := /-- Let $(a_i)_{i=1}^n$ be real numbers, put $M=\sum_i a_i^2$, and suppose $M>0$ and $u>0$. Then the uniform proportion of sign vectors satisfying $u<\sum_i\sigma_i a_i$ is at most $\exp(-u^2/(2M))$. -/)
  (proof := /-- Apply exponential Markov at $t=u/M>0$: on the exceptional set, $e^{tu}<e^{t\sum_i\sigma_i a_i}$. Sum this inequality over signs, enlarge to all sign vectors, and apply \cref{lem:normalized-vc-weighted-sign-mgf}. Division by $e^{tu}$ and substitution of $t=u/M$ give the exponent $-u^2/(2M)$. -/)
  (title := /-- Tail bound for a weighted Rademacher sum -/)
  (latexEnv := "lemma")]
lemma normalized_vc_weighted_sign_tail {n : ℕ} (a : Fin n → ℝ)
    {u : ℝ} (hu : 0 < u) (hM : 0 < ∑ i : Fin n, a i ^ 2) :
    ((Finset.univ.filter fun σ : Fin n → Bool =>
      u < ∑ i : Fin n, (if σ i = true then (1 : ℝ) else -1) * a i).card : ℝ) /
        (2 : ℝ) ^ n ≤
      Real.exp (-u ^ 2 / (2 * ∑ i : Fin n, a i ^ 2)) := by
  let M : ℝ := ∑ i : Fin n, a i ^ 2
  let t : ℝ := u / M
  let B : Finset (Fin n → Bool) := Finset.univ.filter fun σ =>
    u < ∑ i : Fin n, (if σ i = true then (1 : ℝ) else -1) * a i
  have ht : 0 < t := div_pos hu hM
  have hexppos : 0 < Real.exp (t * u) := Real.exp_pos _
  have hmarkov : (B.card : ℝ) * Real.exp (t * u) ≤
      ∑ σ : Fin n → Bool, Real.exp
        (t * ∑ i : Fin n, (if σ i = true then (1 : ℝ) else -1) * a i) := by
    calc
      (B.card : ℝ) * Real.exp (t * u) =
          ∑ σ ∈ B, Real.exp (t * u) := by simp [nsmul_eq_mul]
      _ ≤ ∑ σ ∈ B, Real.exp
          (t * ∑ i : Fin n,
            (if σ i = true then (1 : ℝ) else -1) * a i) := by
        apply Finset.sum_le_sum
        intro σ hσ
        apply Real.exp_le_exp.mpr
        have hbad : u < ∑ i : Fin n,
            (if σ i = true then (1 : ℝ) else -1) * a i :=
          (Finset.mem_filter.mp hσ).2
        exact mul_le_mul_of_nonneg_left hbad.le ht.le
      _ ≤ ∑ σ : Fin n → Bool, Real.exp
          (t * ∑ i : Fin n,
            (if σ i = true then (1 : ℝ) else -1) * a i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro σ hσ hnot
        exact (Real.exp_pos _).le
  have hcard : (B.card : ℝ) ≤
      (∑ σ : Fin n → Bool, Real.exp
        (t * ∑ i : Fin n,
          (if σ i = true then (1 : ℝ) else -1) * a i)) /
        Real.exp (t * u) := (le_div_iff₀ hexppos).2 hmarkov
  have hmgf := normalized_vc_weighted_sign_mgf a t
  have htwo : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  calc
    (B.card : ℝ) / (2 : ℝ) ^ n = ((2 : ℝ) ^ n)⁻¹ * B.card := by ring
    _ ≤ ((2 : ℝ) ^ n)⁻¹ *
        ((∑ σ : Fin n → Bool, Real.exp
          (t * ∑ i : Fin n,
            (if σ i = true then (1 : ℝ) else -1) * a i)) /
          Real.exp (t * u)) := by gcongr
    _ = Real.exp (-(t * u)) *
        (((2 : ℝ) ^ n)⁻¹ *
          ∑ σ : Fin n → Bool, Real.exp
            (t * ∑ i : Fin n,
              (if σ i = true then (1 : ℝ) else -1) * a i)) := by
      rw [Real.exp_neg]
      field_simp
    _ ≤ Real.exp (-(t * u)) * Real.exp (t ^ 2 * M / 2) := by
      apply mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (-u ^ 2 / (2 * M)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [t]
      field_simp [ne_of_gt hM]
      ring

@[blueprint "lem:normalized-vc-self-normalized-sign-tail"
  (statement := /-- For every finite real vector $(a_i)_{i=1}^n$ and every $t>0$, the uniform proportion of sign vectors satisfying
  \[
    \frac{t}{2\sqrt2}\sqrt{\sum_i a_i^2}
      <\sum_i\sigma_i a_i
  \]
  is at most $e^{-t^2/16}$. -/)
  (proof := /-- If $\sum_i a_i^2=0$, every coefficient vanishes and the exceptional set is empty. Otherwise apply \cref{lem:normalized-vc-weighted-sign-tail} with $u=(t/(2\sqrt2))\sqrt{\sum_i a_i^2}$. The identities $(\sqrt2)^2=2$ and $(\sqrt{\sum_i a_i^2})^2=\sum_i a_i^2$ reduce the resulting exponent to $-t^2/16$. -/)
  (title := /-- Self-normalized Rademacher tail bound -/)
  (latexEnv := "lemma")]
lemma normalized_vc_self_normalized_sign_tail {n : ℕ} (a : Fin n → ℝ)
    {t : ℝ} (ht : 0 < t) :
    ((Finset.univ.filter fun σ : Fin n → Bool =>
      t / (2 * Real.sqrt 2) * Real.sqrt (∑ i : Fin n, a i ^ 2) <
        ∑ i : Fin n, (if σ i = true then (1 : ℝ) else -1) * a i).card : ℝ) /
        (2 : ℝ) ^ n ≤ Real.exp (-t ^ 2 / 16) := by
  let M : ℝ := ∑ i : Fin n, a i ^ 2
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i hi => sq_nonneg (a i)
  rcases hM0.eq_or_lt with hMzero | hMpos
  · have ha : ∀ i, a i = 0 := by
      intro i
      have hai : a i ^ 2 ≤ M := by
        dsimp [M]
        exact Finset.single_le_sum (fun j hj => sq_nonneg (a j))
          (Finset.mem_univ i)
      rw [← hMzero] at hai
      nlinarith [sq_nonneg (a i)]
    have hsqrtM : Real.sqrt M = 0 := by rw [← hMzero, Real.sqrt_zero]
    have hsum : ∀ σ : Fin n → Bool,
        (∑ i : Fin n, (if σ i = true then (1 : ℝ) else -1) * a i) = 0 := by
      intro σ
      apply Finset.sum_eq_zero
      intro i hi
      rw [ha i, mul_zero]
    have hfilter : (Finset.univ.filter fun σ : Fin n → Bool =>
        t / (2 * Real.sqrt 2) * Real.sqrt M <
          ∑ i : Fin n, (if σ i = true then (1 : ℝ) else -1) * a i) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro σ hσ
      rw [hsqrtM, mul_zero, hsum]
      exact lt_irrefl 0
    rw [show (∑ i : Fin n, a i ^ 2) = M from rfl, hfilter]
    simpa using (Real.exp_pos (-t ^ 2 / 16)).le
  · have hsqrtM : 0 < Real.sqrt M := Real.sqrt_pos.2 hMpos
    have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hu : 0 < t / (2 * Real.sqrt 2) * Real.sqrt M := by positivity
    have htail := normalized_vc_weighted_sign_tail a hu hMpos
    have hexponent :
        -(t / (2 * Real.sqrt 2) * Real.sqrt M) ^ 2 / (2 * M) =
          -t ^ 2 / 16 := by
      have hsq2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hsqM : (Real.sqrt M) ^ 2 = M := Real.sq_sqrt hM0
      rw [mul_pow, div_pow, mul_pow, hsq2, hsqM]
      field_simp [ne_of_gt hMpos, ne_of_gt hsqrt2]
      ring
    simpa [M, hexponent] using htail

@[blueprint "lem:normalized-vc-indicator-count-moments"
  (statement := /-- Let $P$ be a probability measure and let $h$ be a measurable Boolean concept. For an i.i.d. sample of size $n$, the count
  \[
    S_h(x)=\sum_{i=1}^n\mathbf 1_{\{h(x_i)=\mathrm{true}\}}
  \]
  belongs to $L^2$, has mean $nP\{h=\mathrm{true}\}$, and has variance at most that mean. -/)
  (proof := /-- Write the count as the sum of the coordinate indicator variables. Coordinate projections under the finite product measure are independent and measure preserving. Each indicator has expectation and second moment $P\{h=\mathrm{true}\}$, so its variance is at most this number. Linearity of the integral and additivity of variance for independent variables give the asserted mean and variance bounds; boundedness gives the $L^2$ assertion. -/)
  (title := /-- Moments of an i.i.d. Boolean count -/)
  (latexEnv := "lemma")]
lemma normalized_vc_indicator_count_moments {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.ProbabilityMeasure Ω) {n : ℕ} (h : Ω → Bool)
    (hh : MeasurableSet (concept_event h)) :
    let S : (Fin n → Ω) → ℝ := fun x =>
      ∑ i : Fin n, if h (x i) = true then (1 : ℝ) else 0
    MeasureTheory.MemLp S 2
        (MeasureTheory.Measure.pi fun _ : Fin n =>
          (P : MeasureTheory.Measure Ω)) ∧
      (∫ x, S x ∂MeasureTheory.Measure.pi fun _ : Fin n =>
          (P : MeasureTheory.Measure Ω)) =
        (n : ℝ) * (P : MeasureTheory.Measure Ω).real (concept_event h) ∧
      ProbabilityTheory.variance S
          (MeasureTheory.Measure.pi fun _ : Fin n =>
            (P : MeasureTheory.Measure Ω)) ≤
        (n : ℝ) * (P : MeasureTheory.Measure Ω).real (concept_event h) := by
  classical
  let ν : MeasureTheory.Measure Ω := P
  let g : Ω → ℝ := fun x => if h x = true then 1 else 0
  let Xi : Fin n → (Fin n → Ω) → ℝ := fun i x => g (x i)
  let S : (Fin n → Ω) → ℝ := fun x => ∑ i : Fin n, Xi i x
  have hg : Measurable g := by
    rw [show g = (concept_event h).indicator (fun _ => (1 : ℝ)) by
      funext x
      by_cases hx : h x = true <;> simp [g, concept_event, hx]]
    exact measurable_const.indicator hh
  have hXi : ∀ i : Fin n, MeasureTheory.MemLp (Xi i) 2
      (MeasureTheory.Measure.pi fun _ : Fin n => ν) := by
    intro i
    apply MeasureTheory.MemLp.of_bound
      ((hg.comp (measurable_pi_apply i)).aestronglyMeasurable) 1
    filter_upwards with x
    by_cases hx : h (x i) = true <;> simp [Xi, g, hx]
  have hS : MeasureTheory.MemLp S 2
      (MeasureTheory.Measure.pi fun _ : Fin n => ν) := by
    simpa [S] using MeasureTheory.memLp_finsetSum Finset.univ
      (fun i hi => hXi i)
  have hg_integral :
      (∫ x, g x ∂ν) = ν.real (concept_event h) := by
    rw [show g = (concept_event h).indicator (fun _ => (1 : ℝ)) by
      funext x
      by_cases hx : h x = true <;> simp [g, concept_event, hx]]
    simpa using
      (MeasureTheory.integral_indicator_const (μ := ν) (1 : ℝ) hh)
  have hXi_integral : ∀ i : Fin n,
      (∫ x, Xi i x ∂MeasureTheory.Measure.pi fun _ : Fin n => ν) =
        ν.real (concept_event h) := by
    intro i
    rw [show Xi i = fun x => g (x i) from rfl,
      MeasureTheory.integral_comp_eval hg.aestronglyMeasurable,
      hg_integral]
  have hmean :
      (∫ x, S x ∂MeasureTheory.Measure.pi fun _ : Fin n => ν) =
        (n : ℝ) * ν.real (concept_event h) := by
    rw [show S = fun x => ∑ i ∈ Finset.univ, Xi i x by
      funext x
      simp [S]]
    rw [MeasureTheory.integral_finsetSum Finset.univ
      (fun i hi => (hXi i).integrable (by norm_num))]
    simp_rw [hXi_integral]
    simp
  have hind : ProbabilityTheory.iIndepFun Xi
      (MeasureTheory.Measure.pi fun _ : Fin n => ν) := by
    exact ProbabilityTheory.iIndepFun_pi
      (fun i => hg.aemeasurable)
  have hpair : Set.Pairwise (↑(Finset.univ : Finset (Fin n)) : Set (Fin n))
      (fun i j => ProbabilityTheory.IndepFun (Xi i) (Xi j)
        (MeasureTheory.Measure.pi fun _ : Fin n => ν)) := by
    intro i hi j hj hij
    exact hind.indepFun hij
  have hvarsum :
      ProbabilityTheory.variance S
          (MeasureTheory.Measure.pi fun _ : Fin n => ν) =
        ∑ i : Fin n, ProbabilityTheory.variance (Xi i)
          (MeasureTheory.Measure.pi fun _ : Fin n => ν) := by
    have hSfun : S = ∑ i : Fin n, Xi i := by
      funext x
      simp [S]
    rw [hSfun]
    exact ProbabilityTheory.IndepFun.variance_sum
      (s := (Finset.univ : Finset (Fin n)))
      (fun i hi => hXi i) hpair
  have hXi_sq_integral : ∀ i : Fin n,
      (∫ x, (Xi i x) ^ 2
        ∂MeasureTheory.Measure.pi fun _ : Fin n => ν) =
        ν.real (concept_event h) := by
    intro i
    have hi :
        (∫ x : Fin n → Ω, (g (x i)) ^ 2
          ∂MeasureTheory.Measure.pi fun _ : Fin n => ν) =
          ∫ x, g x ^ 2 ∂ν :=
      MeasureTheory.integral_comp_eval
        (X := fun _ : Fin n => Ω) (μ := fun _ : Fin n => ν)
        (i := i) (f := fun x => g x ^ 2)
        ((hg.pow_const 2).aestronglyMeasurable)
    rw [show (fun x => (Xi i x) ^ 2) = fun x => (g (x i)) ^ 2 from rfl,
      hi]
    calc
      (∫ x, g x ^ 2 ∂ν) = ∫ x, g x ∂ν := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        simp [g]
      _ = ν.real (concept_event h) := hg_integral
  have hvar :
      ProbabilityTheory.variance S
          (MeasureTheory.Measure.pi fun _ : Fin n => ν) ≤
        (n : ℝ) * ν.real (concept_event h) := by
    rw [hvarsum]
    calc
      (∑ i : Fin n, ProbabilityTheory.variance (Xi i)
          (MeasureTheory.Measure.pi fun _ : Fin n => ν))
          ≤ ∑ i : Fin n, ν.real (concept_event h) := by
            apply Finset.sum_le_sum
            intro i hi
            calc
              ProbabilityTheory.variance (Xi i)
                  (MeasureTheory.Measure.pi fun _ : Fin n => ν)
                  ≤ ∫ x, (Xi i x) ^ 2
                    ∂MeasureTheory.Measure.pi fun _ : Fin n => ν :=
                ProbabilityTheory.variance_le_expectation_sq
                  ((hg.comp (measurable_pi_apply i)).aestronglyMeasurable)
              _ = ν.real (concept_event h) := hXi_sq_integral i
      _ = (n : ℝ) * ν.real (concept_event h) := by simp
  dsimp [S, Xi, g, ν] at hS hmean hvar ⊢
  exact ⟨hS, hmean, hvar⟩

@[blueprint "lem:normalized-vc-ghost-comparison"
  (statement := /-- Let $S$ be a nonnegative real random variable on a probability space, with mean $a$, variance at most $a$, and $S\in L^2$. If $t\geq4$ and a fixed $s\geq0$ satisfies
  \[
    t<\frac{a-s}{\sqrt a}
    \quad\text{or}\quad
    t<\frac{s-a}{\sqrt s},
  \]
  then, with probability at least $1/2$, an independent value $S'$ satisfies the corresponding self-normalized comparison
  \[
    \frac{t}{2\sqrt2}\sqrt{S'+s}<S'-s
    \quad\text{or}\quad
    \frac{t}{2\sqrt2}\sqrt{S'+s}<s-S'.
  \] -/)
  (proof := /-- In either case put $c=|a-s|/2$. Chebyshev's inequality and the variance bound show that
  \[
    \Pr\{|S'-a|\geq c\}\leq a/c^2\leq1/4,
  \]
  because the assumed deviation and $t\geq4$ imply $(a-s)^2>16a$ or $(s-a)^2>16s\geq16a$. Thus the complementary event has probability at least $3/4$. On this event $S'$ lies within $c$ of $a$; elementary algebra gives the appropriate numerator larger than $|a-s|/2$ and $S'+s<2a$ in the first case or $S'+s<2s$ in the second. Monotonicity of the square root then gives the displayed self-normalized comparison. -/)
  (title := /-- Ghost-sample comparison from a variance bound -/)
  (latexEnv := "lemma")]
lemma normalized_vc_ghost_comparison {α : Type*} [MeasurableSpace α]
    (ν : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure ν]
    (S : α → ℝ) (hSmeas : Measurable S) (hSnonneg : ∀ x, 0 ≤ S x)
    (hS2 : MeasureTheory.MemLp S 2 ν) {a s t : ℝ}
    (ha0 : 0 ≤ a) (hs0 : 0 ≤ s)
    (hmean : (∫ x, S x ∂ν) = a)
    (hvar : ProbabilityTheory.variance S ν ≤ a)
    (ht : 4 ≤ t)
    (hbad : t < (a - s) / Real.sqrt a ∨
      t < (s - a) / Real.sqrt s) :
    (1 / 2 : ENNReal) ≤ ν {y |
      t / (2 * Real.sqrt 2) * Real.sqrt (S y + s) < S y - s ∨
      t / (2 * Real.sqrt 2) * Real.sqrt (S y + s) < s - S y} := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rcases hbad with hlower | hupper
  · have ha : 0 < a := by
      by_contra h
      have : a = 0 := le_antisymm (le_of_not_gt h) ha0
      simp [this] at hlower
      linarith
    have hsqrta : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
    have hgap : t * Real.sqrt a < a - s :=
      (lt_div_iff₀ hsqrta).mp hlower
    have hsa : s < a := by nlinarith
    let c : ℝ := (a - s) / 2
    have hc : 0 < c := by dsimp [c]; linarith
    have htsq : 16 ≤ t ^ 2 := by nlinarith
    have hsqrta_sq : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha.le
    have hgap_sq : t ^ 2 * a < (a - s) ^ 2 := by
      have hsq := (sq_lt_sq₀ (mul_pos ht0 hsqrta).le
        (by linarith : 0 ≤ a - s)).2 hgap
      rw [mul_pow, hsqrta_sq] at hsq
      exact hsq
    have hratio : a / c ^ 2 ≤ (1 : ℝ) / 4 := by
      apply (div_le_iff₀ (sq_pos_of_pos hc)).2
      dsimp [c]
      nlinarith
    let D : Set α := {y | c ≤ |S y - a|}
    have hDmeas : MeasurableSet D :=
      measurableSet_le measurable_const ((hSmeas.sub_const _).abs)
    have hD : ν D ≤ (1 / 4 : ENNReal) := by
      calc
        ν D ≤ ENNReal.ofReal (ProbabilityTheory.variance S ν / c ^ 2) := by
          simpa [D, hmean] using
            ProbabilityTheory.meas_ge_le_variance_div_sq hS2 hc
        _ ≤ ENNReal.ofReal (a / c ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          gcongr
        _ ≤ ENNReal.ofReal ((1 : ℝ) / 4) :=
          ENNReal.ofReal_le_ofReal hratio
        _ = (1 / 4 : ENNReal) := by
          norm_num [ENNReal.ofReal_div_of_pos]
    have hDtop : ν D ≠ ⊤ :=
      ne_top_of_le_ne_top (by norm_num : (1 / 4 : ENNReal) ≠ ⊤) hD
    have hDc : (1 / 2 : ENNReal) ≤ ν Dᶜ := by
      rw [MeasureTheory.measure_compl hDmeas hDtop,
        MeasureTheory.measure_univ]
      have hDle1 : ν D ≤ ν Set.univ :=
        MeasureTheory.measure_mono (Set.subset_univ D)
      apply (ENNReal.le_sub_iff_add_le_left hDtop (by simpa using hDle1)).2
      calc
        ν D + (1 / 2 : ENNReal) ≤ 1 / 4 + 1 / 2 := by gcongr
        _ ≤ 1 / 2 + 1 / 2 := by
          gcongr
          norm_num
        _ = 1 := by simpa using ENNReal.add_halves (1 : ENNReal)
    apply hDc.trans (MeasureTheory.measure_mono ?_)
    intro y hy
    have hyabs : |S y - a| < c := by
      simpa [D] using hy
    have hybounds := abs_lt.mp hyabs
    have hylower : (a + s) / 2 < S y := by
      dsimp [c] at hybounds
      linarith
    have hyupper : S y < (3 * a - s) / 2 := by
      dsimp [c] at hybounds
      linarith
    have hsum : S y + s < 2 * a := by linarith
    have hsumsqrt : Real.sqrt (S y + s) ≤ Real.sqrt (2 * a) :=
      Real.sqrt_le_sqrt hsum.le
    have hsqrtmul : Real.sqrt (2 * a) = Real.sqrt 2 * Real.sqrt a := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    left
    have hcoef : 0 ≤ t / (2 * Real.sqrt 2) := by positivity
    calc
      t / (2 * Real.sqrt 2) * Real.sqrt (S y + s)
          ≤ t / (2 * Real.sqrt 2) * Real.sqrt (2 * a) := by gcongr
      _ = t * Real.sqrt a / 2 := by rw [hsqrtmul]; field_simp
      _ < (a - s) / 2 := by linarith
      _ < S y - s := by linarith
  · have hs : 0 < s := by
      by_contra h
      have : s = 0 := le_antisymm (le_of_not_gt h) hs0
      simp [this] at hupper
      linarith
    have hsqrts : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
    have hgap : t * Real.sqrt s < s - a :=
      (lt_div_iff₀ hsqrts).mp hupper
    have has : a < s := by nlinarith
    let c : ℝ := (s - a) / 2
    have hc : 0 < c := by dsimp [c]; linarith
    have htsq : 16 ≤ t ^ 2 := by nlinarith
    have hsqrts_sq : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs.le
    have hgap_sq : t ^ 2 * s < (s - a) ^ 2 := by
      have hsq := (sq_lt_sq₀ (mul_pos ht0 hsqrts).le
        (by linarith : 0 ≤ s - a)).2 hgap
      rw [mul_pow, hsqrts_sq] at hsq
      exact hsq
    have hratio : a / c ^ 2 ≤ (1 : ℝ) / 4 := by
      apply (div_le_iff₀ (sq_pos_of_pos hc)).2
      dsimp [c]
      nlinarith
    let D : Set α := {y | c ≤ |S y - a|}
    have hDmeas : MeasurableSet D :=
      measurableSet_le measurable_const ((hSmeas.sub_const _).abs)
    have hD : ν D ≤ (1 / 4 : ENNReal) := by
      calc
        ν D ≤ ENNReal.ofReal (ProbabilityTheory.variance S ν / c ^ 2) := by
          simpa [D, hmean] using
            ProbabilityTheory.meas_ge_le_variance_div_sq hS2 hc
        _ ≤ ENNReal.ofReal (a / c ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          gcongr
        _ ≤ ENNReal.ofReal ((1 : ℝ) / 4) :=
          ENNReal.ofReal_le_ofReal hratio
        _ = (1 / 4 : ENNReal) := by
          norm_num [ENNReal.ofReal_div_of_pos]
    have hDtop : ν D ≠ ⊤ :=
      ne_top_of_le_ne_top (by norm_num : (1 / 4 : ENNReal) ≠ ⊤) hD
    have hDc : (1 / 2 : ENNReal) ≤ ν Dᶜ := by
      rw [MeasureTheory.measure_compl hDmeas hDtop,
        MeasureTheory.measure_univ]
      have hDle1 : ν D ≤ ν Set.univ :=
        MeasureTheory.measure_mono (Set.subset_univ D)
      apply (ENNReal.le_sub_iff_add_le_left hDtop (by simpa using hDle1)).2
      calc
        ν D + (1 / 2 : ENNReal) ≤ 1 / 4 + 1 / 2 := by gcongr
        _ ≤ 1 / 2 + 1 / 2 := by
          gcongr
          norm_num
        _ = 1 := by simpa using ENNReal.add_halves (1 : ENNReal)
    apply hDc.trans (MeasureTheory.measure_mono ?_)
    intro y hy
    have hyabs : |S y - a| < c := by
      simpa [D] using hy
    have hybounds := abs_lt.mp hyabs
    have hylower : (3 * a - s) / 2 < S y := by
      dsimp [c] at hybounds
      linarith
    have hyupper : S y < (a + s) / 2 := by
      dsimp [c] at hybounds
      linarith
    have hsum : S y + s < 2 * s := by linarith
    have hsumsqrt : Real.sqrt (S y + s) ≤ Real.sqrt (2 * s) :=
      Real.sqrt_le_sqrt hsum.le
    have hsqrtmul : Real.sqrt (2 * s) = Real.sqrt 2 * Real.sqrt s := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    right
    have hcoef : 0 ≤ t / (2 * Real.sqrt 2) := by positivity
    calc
      t / (2 * Real.sqrt 2) * Real.sqrt (S y + s)
          ≤ t / (2 * Real.sqrt 2) * Real.sqrt (2 * s) := by gcongr
      _ = t * Real.sqrt s / 2 := by rw [hsqrtmul]; field_simp
      _ < (s - a) / 2 := by linarith
      _ < s - S y := by linarith

@[blueprint "lem:normalized-vc-ghost-symmetrization"
  (statement := /-- Let $(S_i)_{i\in I}$ be a finite family of nonnegative, measurable, square-integrable random variables on a probability space. Suppose that $S_i$ has mean $a_i\geq0$ and variance at most $a_i$. For $t\geq4$, the probability that some $S_i$ has either normalized deviation
  \[
    t<\frac{a_i-S_i}{\sqrt{a_i}}
    \quad\text{or}\quad
    t<\frac{S_i-a_i}{\sqrt{S_i}}
  \]
  is at most twice the product-space probability that two independent copies satisfy one of the corresponding self-normalized comparison inequalities. -/)
  (proof := /-- For every exceptional first sample, choose an offending index. By \cref{lem:normalized-vc-ghost-comparison}, the section of the comparison event over the second sample has measure at least $1/2$. Thus the indicator of the original exceptional event is pointwise bounded by twice the measure of that section. Integrate this inequality and use the product-measure section formula. -/)
  (title := /-- Finite-family ghost-sample symmetrization -/)
  (latexEnv := "lemma")]
lemma normalized_vc_ghost_symmetrization {α ι : Type*}
    [MeasurableSpace α] [Fintype ι]
    (ν : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure ν]
    (S : ι → α → ℝ) (a : ι → ℝ)
    (hSmeas : ∀ i, Measurable (S i))
    (hSnonneg : ∀ i x, 0 ≤ S i x)
    (hmom : ∀ i, MeasureTheory.MemLp (S i) 2 ν ∧
      (∫ x, S i x ∂ν) = a i ∧
      ProbabilityTheory.variance (S i) ν ≤ a i)
    {t : ℝ} (ht : 4 ≤ t) :
    ν {x | ∃ i,
      t < (a i - S i x) / Real.sqrt (a i) ∨
      t < (S i x - a i) / Real.sqrt (S i x)} ≤
      2 * (ν.prod ν) {z | ∃ i,
        t / (2 * Real.sqrt 2) * Real.sqrt (S i z.2 + S i z.1) <
          S i z.2 - S i z.1 ∨
        t / (2 * Real.sqrt 2) * Real.sqrt (S i z.2 + S i z.1) <
          S i z.1 - S i z.2} := by
  let B : Set α := {x | ∃ i,
    t < (a i - S i x) / Real.sqrt (a i) ∨
    t < (S i x - a i) / Real.sqrt (S i x)}
  let C : Set (α × α) := {z | ∃ i,
    t / (2 * Real.sqrt 2) * Real.sqrt (S i z.2 + S i z.1) <
      S i z.2 - S i z.1 ∨
    t / (2 * Real.sqrt 2) * Real.sqrt (S i z.2 + S i z.1) <
      S i z.1 - S i z.2}
  have hBmeas : MeasurableSet B := by
    dsimp [B]
    measurability
  have hCmeas : MeasurableSet C := by
    dsimp [C]
    measurability
  have hsection : ∀ x ∈ B, (1 / 2 : ENNReal) ≤
      ν (Prod.mk x ⁻¹' C) := by
    intro x hx
    rcases hx with ⟨i, hi⟩
    have hai : 0 ≤ a i := by
      rw [← (hmom i).2.1]
      exact MeasureTheory.integral_nonneg (hSnonneg i)
    have hghost := normalized_vc_ghost_comparison ν (S i)
      (hSmeas i) (hSnonneg i) (hmom i).1 hai (hSnonneg i x)
      (hmom i).2.1 (hmom i).2.2 ht hi
    apply hghost.trans (MeasureTheory.measure_mono ?_)
    intro y hy
    rcases hy with hy | hy
    · exact ⟨i, Or.inl (by simpa [C, add_comm] using hy)⟩
    · exact ⟨i, Or.inr (by simpa [C, add_comm] using hy)⟩
  rw [show {x | ∃ i,
      t < (a i - S i x) / Real.sqrt (a i) ∨
      t < (S i x - a i) / Real.sqrt (S i x)} = B from rfl,
    show {z | ∃ i,
      t / (2 * Real.sqrt 2) * Real.sqrt (S i z.2 + S i z.1) <
        S i z.2 - S i z.1 ∨
      t / (2 * Real.sqrt 2) * Real.sqrt (S i z.2 + S i z.1) <
        S i z.1 - S i z.2} = C from rfl,
    MeasureTheory.Measure.prod_apply hCmeas]
  calc
    ν B = ∫⁻ x, B.indicator (fun _ => (1 : ENNReal)) x ∂ν := by
      exact (MeasureTheory.lintegral_indicator_one hBmeas).symm
    _ ≤ ∫⁻ x, 2 * ν (Prod.mk x ⁻¹' C) ∂ν := by
      apply MeasureTheory.lintegral_mono
      intro x
      by_cases hx : x ∈ B
      · rw [Set.indicator_of_mem hx]
        have hxhalf := hsection x hx
        calc
          (1 : ENNReal) = 2 * (1 / 2 : ENNReal) := by
            simpa [one_div] using
              (ENNReal.mul_inv_cancel (by norm_num : (2 : ENNReal) ≠ 0)
                (by norm_num : (2 : ENNReal) ≠ ⊤)).symm
          _ ≤ 2 * ν (Prod.mk x ⁻¹' C) := by gcongr
      · simp [Set.indicator, hx]
    _ = 2 * ∫⁻ x, ν (Prod.mk x ⁻¹' C) ∂ν := by
      rw [MeasureTheory.lintegral_const_mul 2
        (measurable_measure_prodMk_left_finite hCmeas)]

@[blueprint "lem:normalized-vc-swap-measure-preserving"
  (statement := /-- Let $P$ be a probability measure and let $X,Y$ be independent $P$-samples of length $n$. For every sign vector $\sigma\in\{-1,1\}^n$, independently exchanging $X_i$ and $Y_i$ in precisely the coordinates selected by $\sigma$ preserves the joint law of $(X,Y)$. -/)
  (proof := /-- Identify a pair of samples with a sample of ordered pairs by the measurable equivalence between functions into a product and pairs of functions. On each coordinate use either the identity or the coordinate swap; both preserve $P\otimes P$. The product of these coordinate maps preserves the finite product measure. Conjugating by the measurable equivalence proves the assertion. -/)
  (title := /-- Coordinate swaps preserve the double-sample law -/)
  (latexEnv := "lemma")]
lemma normalized_vc_swap_measure_preserving {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    {n : ℕ} (σ : Fin n → Bool) :
    MeasureTheory.MeasurePreserving
      (fun z : (Fin n → Ω) × (Fin n → Ω) =>
        (fun i => if σ i = true then z.1 i else z.2 i,
          fun i => if σ i = true then z.2 i else z.1 i))
      ((MeasureTheory.Measure.pi fun _ : Fin n => P).prod
        (MeasureTheory.Measure.pi fun _ : Fin n => P))
      ((MeasureTheory.Measure.pi fun _ : Fin n => P).prod
        (MeasureTheory.Measure.pi fun _ : Fin n => P)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow Ω Ω (Fin n)
  let swapPair : Fin n → Ω × Ω → Ω × Ω := fun i z =>
    if σ i = true then z else z.swap
  have he : MeasureTheory.MeasurePreserving e
      (MeasureTheory.Measure.pi fun _ : Fin n => P.prod P)
      ((MeasureTheory.Measure.pi fun _ : Fin n => P).prod
        (MeasureTheory.Measure.pi fun _ : Fin n => P)) := by
    exact MeasureTheory.measurePreserving_arrowProdEquivProdArrow Ω Ω (Fin n)
      (fun _ => P) (fun _ => P)
  have heinv : MeasureTheory.MeasurePreserving e.symm
      ((MeasureTheory.Measure.pi fun _ : Fin n => P).prod
        (MeasureTheory.Measure.pi fun _ : Fin n => P))
      (MeasureTheory.Measure.pi fun _ : Fin n => P.prod P) :=
    he.symm (e := e)
  have hcoord : ∀ i : Fin n, MeasureTheory.MeasurePreserving (swapPair i)
      (P.prod P) (P.prod P) := by
    intro i
    by_cases hi : σ i = true
    · convert (MeasureTheory.MeasurePreserving.id (μ := P.prod P)) using 1
      funext z
      simp [swapPair, hi]
    · simpa [swapPair, hi] using P.measurePreserving_swap
  have hpi : MeasureTheory.MeasurePreserving
      (fun z i => swapPair i (z i))
      (MeasureTheory.Measure.pi fun _ : Fin n => P.prod P)
      (MeasureTheory.Measure.pi fun _ : Fin n => P.prod P) :=
    MeasureTheory.measurePreserving_pi
      (fun _ : Fin n => P.prod P) (fun _ : Fin n => P.prod P) hcoord
  have hcomp := he.comp (hpi.comp heinv)
  convert hcomp using 1
  funext z
  ext i <;>
    by_cases hi : σ i = true <;>
      simp [e, swapPair, Function.comp_def,
        MeasurableEquiv.arrowProdEquivProdArrow,
        Equiv.arrowProdEquivProdArrow, hi]

@[blueprint "lem:normalized-vc-swap-count-bound"
  (statement := /-- Let $\mathcal H$ have VC dimension $d$, let $\mathcal J\subseteq\mathcal H$ be finite, and fix two samples $x,y$ of length $n$. For $t>0$, the uniform proportion of coordinate swaps for which some $h\in\mathcal J$ satisfies either self-normalized count comparison is at most
  \[
    2(2n+1)^d e^{-t^2/16}.
  \] -/)
  (proof := /-- Let $W$ be the set of observations occurring in the two samples. Concepts with the same trace on $W$ give identical count comparisons after every coordinate swap. The number of traces is at most $(|W|+1)^d\leq(2n+1)^d$ by \cref{lem:normalized-vc-trace-cardinality-bound}. For a fixed trace, write the count difference as a signed sum of coefficients in $\{-1,0,1\}$. Their squared sum is at most the sum of the two counts. Apply \cref{lem:normalized-vc-self-normalized-sign-tail} to these coefficients and to their negatives, then take the finite union over traces and the two directions. -/)
  (title := /-- VC bound for bad coordinate swaps -/)
  (latexEnv := "lemma")]
lemma normalized_vc_swap_count_bound {Ω : Type*}
    (H : concept_class Ω) {d n : ℕ} (hvc : has_vc_dimension H d)
    (J : Finset (Ω → Bool)) (hJ : (J : Set (Ω → Bool)) ⊆ H)
    (x y : Fin n → Ω) {t : ℝ} (ht : 0 < t) :
    ((Finset.univ.filter fun σ : Fin n → Bool => ∃ h ∈ J,
      t / (2 * Real.sqrt 2) *
          Real.sqrt
            ((∑ i : Fin n, if h (y i) = true then (1 : ℝ) else 0) +
              ∑ i : Fin n, if h (x i) = true then (1 : ℝ) else 0) <
        ∑ i : Fin n, (if σ i = true then (1 : ℝ) else -1) *
          ((if h (y i) = true then (1 : ℝ) else 0) -
            if h (x i) = true then (1 : ℝ) else 0) ∨
      t / (2 * Real.sqrt 2) *
          Real.sqrt
            ((∑ i : Fin n, if h (y i) = true then (1 : ℝ) else 0) +
              ∑ i : Fin n, if h (x i) = true then (1 : ℝ) else 0) <
        ∑ i : Fin n, (if σ i = true then (1 : ℝ) else -1) *
          (-((if h (y i) = true then (1 : ℝ) else 0) -
            if h (x i) = true then (1 : ℝ) else 0))).card : ℝ) /
        (2 : ℝ) ^ n ≤
      2 * (2 * (n : ℝ) + 1) ^ d * Real.exp (-t ^ 2 / 16) := by
  classical
  let W : Finset Ω :=
    (Finset.univ.image x) ∪ (Finset.univ.image y)
  let xW : Fin n → ↥W := fun i =>
    ⟨x i, show x i ∈ W by simp [W]⟩
  let yW : Fin n → ↥W := fun i =>
    ⟨y i, show y i ∈ W by simp [W]⟩
  let A : Finset (Finset ↥W) := Finset.univ.filter fun s =>
    ∃ h ∈ H, ∀ z : ↥W, z ∈ s ↔ h z = true
  have hAcard : A.card ≤ (2 * n + 1) ^ d := by
    have htrace := normalized_vc_trace_cardinality_bound H hvc W
    have hWcard : W.card ≤ 2 * n := by
      have hxcard : (Finset.univ.image x).card ≤ n := by
        simpa using (Finset.card_image_le :
          (Finset.univ.image x).card ≤ Finset.univ.card)
      have hycard : (Finset.univ.image y).card ≤ n := by
        simpa using (Finset.card_image_le :
          (Finset.univ.image y).card ≤ Finset.univ.card)
      calc
        W.card ≤ (Finset.univ.image x).card +
            (Finset.univ.image y).card := Finset.card_union_le _ _
        _ ≤ n + n := Nat.add_le_add hxcard hycard
        _ = 2 * n := by omega
    calc
      A.card ≤ (W.card + 1) ^ d := by simpa [A] using htrace
      _ ≤ (2 * n + 1) ^ d := by gcongr
  let coeff : Finset ↥W → Fin n → ℝ := fun s i =>
    (if yW i ∈ s then 1 else 0) - if xW i ∈ s then 1 else 0
  let pairCount : Finset ↥W → ℝ := fun s =>
    (∑ i : Fin n, if yW i ∈ s then (1 : ℝ) else 0) +
      ∑ i : Fin n, if xW i ∈ s then (1 : ℝ) else 0
  let E : Finset ↥W → Finset (Fin n → Bool) := fun s =>
    Finset.univ.filter fun σ =>
      t / (2 * Real.sqrt 2) * Real.sqrt (pairCount s) <
          ∑ i : Fin n,
            (if σ i = true then (1 : ℝ) else -1) * coeff s i ∨
      t / (2 * Real.sqrt 2) * Real.sqrt (pairCount s) <
          ∑ i : Fin n,
            (if σ i = true then (1 : ℝ) else -1) * (-coeff s i)
  have hcoeffsq : ∀ s : Finset ↥W,
      (∑ i : Fin n, (coeff s i) ^ 2) ≤ pairCount s := by
    intro s
    dsimp [coeff, pairCount]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    by_cases hy : yW i ∈ s <;> by_cases hx : xW i ∈ s <;>
      simp [hy, hx]
  have hE : ∀ s : Finset ↥W,
      ((E s).card : ℝ) / (2 : ℝ) ^ n ≤
        2 * Real.exp (-t ^ 2 / 16) := by
    intro s
    let Epos : Finset (Fin n → Bool) := Finset.univ.filter fun σ =>
      t / (2 * Real.sqrt 2) * Real.sqrt (pairCount s) <
        ∑ i : Fin n,
          (if σ i = true then (1 : ℝ) else -1) * coeff s i
    let Eneg : Finset (Fin n → Bool) := Finset.univ.filter fun σ =>
      t / (2 * Real.sqrt 2) * Real.sqrt (pairCount s) <
        ∑ i : Fin n,
          (if σ i = true then (1 : ℝ) else -1) * (-coeff s i)
    have hcoefnonneg : 0 ≤ t / (2 * Real.sqrt 2) := by positivity
    have hsqrtle : Real.sqrt (∑ i : Fin n, (coeff s i) ^ 2) ≤
        Real.sqrt (pairCount s) := Real.sqrt_le_sqrt (hcoeffsq s)
    have hpos_sub : Epos ⊆ Finset.univ.filter fun σ : Fin n → Bool =>
        t / (2 * Real.sqrt 2) *
            Real.sqrt (∑ i : Fin n, (coeff s i) ^ 2) <
          ∑ i : Fin n,
            (if σ i = true then (1 : ℝ) else -1) * coeff s i := by
      intro σ hσ
      rw [Finset.mem_filter] at hσ ⊢
      exact ⟨Finset.mem_univ _, lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left hsqrtle hcoefnonneg) hσ.2⟩
    have hneg_sq : (∑ i : Fin n, (-coeff s i) ^ 2) =
        ∑ i : Fin n, (coeff s i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hneg_sub : Eneg ⊆ Finset.univ.filter fun σ : Fin n → Bool =>
        t / (2 * Real.sqrt 2) *
            Real.sqrt (∑ i : Fin n, (-coeff s i) ^ 2) <
          ∑ i : Fin n,
            (if σ i = true then (1 : ℝ) else -1) * (-coeff s i) := by
      intro σ hσ
      rw [Finset.mem_filter] at hσ ⊢
      rw [hneg_sq]
      exact ⟨Finset.mem_univ _, lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left hsqrtle hcoefnonneg) hσ.2⟩
    have hpos := normalized_vc_self_normalized_sign_tail (coeff s) ht
    have hneg := normalized_vc_self_normalized_sign_tail
      (fun i => -coeff s i) ht
    have hposcard : ((Epos.card : ℝ) / (2 : ℝ) ^ n) ≤
        Real.exp (-t ^ 2 / 16) := by
      calc
        (Epos.card : ℝ) / (2 : ℝ) ^ n ≤
            ((Finset.univ.filter fun σ : Fin n → Bool =>
              t / (2 * Real.sqrt 2) *
                  Real.sqrt (∑ i : Fin n, (coeff s i) ^ 2) <
                ∑ i : Fin n,
                  (if σ i = true then (1 : ℝ) else -1) *
                    coeff s i).card : ℝ) / (2 : ℝ) ^ n := by
              gcongr
        _ ≤ Real.exp (-t ^ 2 / 16) := hpos
    have hnegcard : ((Eneg.card : ℝ) / (2 : ℝ) ^ n) ≤
        Real.exp (-t ^ 2 / 16) := by
      calc
        (Eneg.card : ℝ) / (2 : ℝ) ^ n ≤
            ((Finset.univ.filter fun σ : Fin n → Bool =>
              t / (2 * Real.sqrt 2) *
                  Real.sqrt (∑ i : Fin n, (-coeff s i) ^ 2) <
                ∑ i : Fin n,
                  (if σ i = true then (1 : ℝ) else -1) *
                    (-coeff s i)).card : ℝ) / (2 : ℝ) ^ n := by
              gcongr
        _ ≤ Real.exp (-t ^ 2 / 16) := hneg
    have hEsub : E s ⊆ Epos ∪ Eneg := by
      intro σ hσ
      simp only [E, Epos, Eneg, Finset.mem_filter, Finset.mem_union] at hσ ⊢
      rcases hσ.2 with hp | hn
      · exact Or.inl ⟨Finset.mem_univ _, hp⟩
      · exact Or.inr ⟨Finset.mem_univ _, hn⟩
    have hcard : (E s).card ≤ Epos.card + Eneg.card :=
      (Finset.card_le_card hEsub).trans (Finset.card_union_le _ _)
    calc
      ((E s).card : ℝ) / (2 : ℝ) ^ n
          ≤ ((Epos.card + Eneg.card : ℕ) : ℝ) / (2 : ℝ) ^ n := by
            gcongr
      _ = (Epos.card : ℝ) / (2 : ℝ) ^ n +
          (Eneg.card : ℝ) / (2 : ℝ) ^ n := by
            push_cast
            ring
      _ ≤ Real.exp (-t ^ 2 / 16) + Real.exp (-t ^ 2 / 16) :=
        add_le_add hposcard hnegcard
      _ = 2 * Real.exp (-t ^ 2 / 16) := by ring
  let Bad : Finset (Fin n → Bool) := Finset.univ.filter fun σ =>
    ∃ h ∈ J,
      t / (2 * Real.sqrt 2) *
          Real.sqrt
            ((∑ i : Fin n, if h (y i) = true then (1 : ℝ) else 0) +
              ∑ i : Fin n, if h (x i) = true then (1 : ℝ) else 0) <
        ∑ i : Fin n, (if σ i = true then (1 : ℝ) else -1) *
          ((if h (y i) = true then (1 : ℝ) else 0) -
            if h (x i) = true then (1 : ℝ) else 0) ∨
      t / (2 * Real.sqrt 2) *
          Real.sqrt
            ((∑ i : Fin n, if h (y i) = true then (1 : ℝ) else 0) +
              ∑ i : Fin n, if h (x i) = true then (1 : ℝ) else 0) <
        ∑ i : Fin n, (if σ i = true then (1 : ℝ) else -1) *
          (-((if h (y i) = true then (1 : ℝ) else 0) -
            if h (x i) = true then (1 : ℝ) else 0))
  have hBadsub : Bad ⊆ A.biUnion E := by
    intro σ hσ
    rcases (Finset.mem_filter.mp hσ).2 with ⟨h, hhJ, hbad⟩
    let s : Finset ↥W := Finset.univ.filter fun z => h z = true
    have hsA : s ∈ A := by
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨h, hJ (by simpa using hhJ), fun z => by simp [s]⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨s, hsA, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hxmem : ∀ i : Fin n, xW i ∈ s ↔ h (x i) = true := by
      intro i
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
    have hymem : ∀ i : Fin n, yW i ∈ s ↔ h (y i) = true := by
      intro i
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
    simpa [E, pairCount, coeff, hxmem, hymem] using hbad
  have hcardBad : Bad.card ≤ ∑ s ∈ A, (E s).card :=
    (Finset.card_le_card hBadsub).trans Finset.card_biUnion_le
  have htwo : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  calc
    (Bad.card : ℝ) / (2 : ℝ) ^ n
        ≤ (∑ s ∈ A, (E s).card : ℕ) / (2 : ℝ) ^ n := by
          gcongr
    _ = ∑ s ∈ A, ((E s).card : ℝ) / (2 : ℝ) ^ n := by
      push_cast
      rw [Finset.sum_div]
    _ ≤ ∑ s ∈ A, 2 * Real.exp (-t ^ 2 / 16) := by
      exact Finset.sum_le_sum fun s hs => hE s
    _ = (A.card : ℝ) * (2 * Real.exp (-t ^ 2 / 16)) := by simp
    _ ≤ (((2 * n + 1) ^ d : ℕ) : ℝ) *
        (2 * Real.exp (-t ^ 2 / 16)) := by
      gcongr
    _ = 2 * (2 * (n : ℝ) + 1) ^ d *
        Real.exp (-t ^ 2 / 16) := by
      push_cast
      ring

@[blueprint "lem:normalized-vc-double-sample-bound"
  (statement := /-- Let $P$ be a probability measure, let $\mathcal H$ have VC dimension $d$, and let $\mathcal J\subseteq\mathcal H$ be finite. For two independent samples of length $n$ and $t>0$, the probability that some $h\in\mathcal J$ satisfies either self-normalized comparison is at most
  \[
    2(2n+1)^d e^{-t^2/16}.
  \] -/)
  (proof := /-- Average the comparison event over all coordinate swaps. Every swap preserves the double-sample law by \cref{lem:normalized-vc-swap-measure-preserving}. For each fixed pair of samples, \cref{lem:normalized-vc-swap-count-bound} bounds the proportion of swaps in the event by $2(2n+1)^d e^{-t^2/16}$. Exchange the finite sum over swaps with the lower integral and cancel the positive finite factor $2^n$. -/)
  (title := /-- Double-sample VC comparison bound -/)
  (latexEnv := "lemma")]
lemma normalized_vc_double_sample_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (H : concept_class Ω) {d n : ℕ} (hvc : has_vc_dimension H d)
    (J : Finset (Ω → Bool)) (hJ : (J : Set (Ω → Bool)) ⊆ H)
    (hmeas : ∀ h ∈ J, MeasurableSet (concept_event h))
    {t : ℝ} (ht : 0 < t) :
    let ν := MeasureTheory.Measure.pi fun _ : Fin n => P
    let S : (Ω → Bool) → (Fin n → Ω) → ℝ := fun h x =>
      ∑ i : Fin n, if h (x i) = true then 1 else 0
    (ν.prod ν) {z | ∃ h ∈ J,
      t / (2 * Real.sqrt 2) * Real.sqrt (S h z.2 + S h z.1) <
          S h z.2 - S h z.1 ∨
      t / (2 * Real.sqrt 2) * Real.sqrt (S h z.2 + S h z.1) <
          S h z.1 - S h z.2} ≤
      ENNReal.ofReal
        (2 * (2 * (n : ℝ) + 1) ^ d * Real.exp (-t ^ 2 / 16)) := by
  classical
  let ν : MeasureTheory.Measure (Fin n → Ω) :=
    MeasureTheory.Measure.pi fun _ : Fin n => P
  let S : (Ω → Bool) → (Fin n → Ω) → ℝ := fun h x =>
    ∑ i : Fin n, if h (x i) = true then 1 else 0
  let C : Set ((Fin n → Ω) × (Fin n → Ω)) := {z | ∃ h ∈ J,
    t / (2 * Real.sqrt 2) * Real.sqrt (S h z.2 + S h z.1) <
        S h z.2 - S h z.1 ∨
    t / (2 * Real.sqrt 2) * Real.sqrt (S h z.2 + S h z.1) <
        S h z.1 - S h z.2}
  let τ : (Fin n → Bool) →
      ((Fin n → Ω) × (Fin n → Ω)) →
      ((Fin n → Ω) × (Fin n → Ω)) := fun σ z =>
    (fun i => if σ i = true then z.1 i else z.2 i,
      fun i => if σ i = true then z.2 i else z.1 i)
  have hSmeas : ∀ h ∈ J, Measurable (S h) := by
    intro h hh
    have hevent := hmeas h hh
    have hg : Measurable (fun z : Ω =>
        if h z = true then (1 : ℝ) else 0) := by
      rw [show (fun z : Ω => if h z = true then (1 : ℝ) else 0) =
          (concept_event h).indicator (fun _ => (1 : ℝ)) by
        funext z
        by_cases hz : h z = true <;> simp [concept_event, hz]]
      exact measurable_const.indicator hevent
    dsimp [S]
    exact Finset.measurable_sum Finset.univ
      (fun i hi => hg.comp (measurable_pi_apply i))
  have hCmeas : MeasurableSet C := by
    rw [show C = ⋃ h : ↥J, {z |
        t / (2 * Real.sqrt 2) * Real.sqrt (S h z.2 + S h z.1) <
            S h z.2 - S h z.1 ∨
        t / (2 * Real.sqrt 2) * Real.sqrt (S h z.2 + S h z.1) <
            S h z.1 - S h z.2} by
      ext z
      simp [C]]
    apply MeasurableSet.iUnion
    intro h
    have hm := hSmeas h h.property
    have hm1 : Measurable (fun z :
        (Fin n → Ω) × (Fin n → Ω) => S h z.1) :=
      hm.comp measurable_fst
    have hm2 : Measurable (fun z :
        (Fin n → Ω) × (Fin n → Ω) => S h z.2) :=
      hm.comp measurable_snd
    exact (measurableSet_lt
      (measurable_const.mul ((hm2.add hm1).sqrt))
      (hm2.sub hm1)).union
      (measurableSet_lt
        (measurable_const.mul ((hm2.add hm1).sqrt))
        (hm1.sub hm2))
  have hpre : ∀ σ : Fin n → Bool, (ν.prod ν) (τ σ ⁻¹' C) =
      (ν.prod ν) C := by
    intro σ
    have hp := normalized_vc_swap_measure_preserving P σ
    exact hp.measure_preimage hCmeas.nullMeasurableSet
  let K : ℝ :=
    2 * (2 * (n : ℝ) + 1) ^ d * Real.exp (-t ^ 2 / 16)
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hpoint : ∀ z : (Fin n → Ω) × (Fin n → Ω),
      ((Finset.univ.filter fun σ : Fin n → Bool => τ σ z ∈ C).card :
          ENNReal) ≤
        ((2 : ENNReal) ^ n) * ENNReal.ofReal K := by
    intro z
    have hcount := normalized_vc_swap_count_bound H hvc J hJ
      z.1 z.2 ht
    have hiff : ∀ σ : Fin n → Bool, τ σ z ∈ C ↔
        ∃ h ∈ J,
          t / (2 * Real.sqrt 2) *
              Real.sqrt (S h z.2 + S h z.1) <
            ∑ i : Fin n, (if σ i = true then (1 : ℝ) else -1) *
              ((if h (z.2 i) = true then (1 : ℝ) else 0) -
                if h (z.1 i) = true then (1 : ℝ) else 0) ∨
          t / (2 * Real.sqrt 2) *
              Real.sqrt (S h z.2 + S h z.1) <
            ∑ i : Fin n, (if σ i = true then (1 : ℝ) else -1) *
              (-((if h (z.2 i) = true then (1 : ℝ) else 0) -
                if h (z.1 i) = true then (1 : ℝ) else 0)) := by
      intro σ
      have hsum : ∀ h : Ω → Bool,
          S h (τ σ z).2 + S h (τ σ z).1 =
            S h z.2 + S h z.1 := by
        intro h
        dsimp [S, τ]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hσ : σ i = true <;> simp [hσ] <;> ring
      have hdiff : ∀ h : Ω → Bool,
          S h (τ σ z).2 - S h (τ σ z).1 =
            ∑ i : Fin n, (if σ i = true then (1 : ℝ) else -1) *
              ((if h (z.2 i) = true then (1 : ℝ) else 0) -
                if h (z.1 i) = true then (1 : ℝ) else 0) := by
        intro h
        dsimp [S, τ]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hσ : σ i = true <;> simp [hσ] <;> ring
      have hdiff' : ∀ h : Ω → Bool,
          S h (τ σ z).1 - S h (τ σ z).2 =
            ∑ i : Fin n, (if σ i = true then (1 : ℝ) else -1) *
              (-((if h (z.2 i) = true then (1 : ℝ) else 0) -
                if h (z.1 i) = true then (1 : ℝ) else 0)) := by
        intro h
        rw [show S h (τ σ z).1 - S h (τ σ z).2 =
          -(S h (τ σ z).2 - S h (τ σ z).1) by ring, hdiff h,
          ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      simp only [C]
      constructor
      · rintro ⟨h, hh, hbad⟩
        refine ⟨h, hh, ?_⟩
        rw [hsum h, hdiff h, hdiff' h] at hbad
        exact hbad
      · rintro ⟨h, hh, hbad⟩
        refine ⟨h, hh, ?_⟩
        rw [hsum h, hdiff h, hdiff' h]
        exact hbad
    have hfilter :
        (Finset.univ.filter fun σ : Fin n → Bool => τ σ z ∈ C) =
          Finset.univ.filter fun σ : Fin n → Bool =>
            ∃ h ∈ J,
              t / (2 * Real.sqrt 2) *
                  Real.sqrt (S h z.2 + S h z.1) <
                ∑ i : Fin n, (if σ i = true then (1 : ℝ) else -1) *
                  ((if h (z.2 i) = true then (1 : ℝ) else 0) -
                    if h (z.1 i) = true then (1 : ℝ) else 0) ∨
              t / (2 * Real.sqrt 2) *
                  Real.sqrt (S h z.2 + S h z.1) <
                ∑ i : Fin n, (if σ i = true then (1 : ℝ) else -1) *
                  (-((if h (z.2 i) = true then (1 : ℝ) else 0) -
                    if h (z.1 i) = true then (1 : ℝ) else 0)) := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hiff σ
    have hreal0 := (div_le_iff₀
      (pow_pos (by norm_num : (0 : ℝ) < 2) n)).mp hcount
    have hof := ENNReal.ofReal_le_ofReal hreal0
    rw [hfilter]
    simpa only [S, K, ENNReal.ofReal_mul hK0,
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_natCast, Nat.cast_ofNat] using (by
        simpa [mul_comm] using hof)
  have hsum :
      ((2 : ENNReal) ^ n) * (ν.prod ν) C =
        ∑ σ : Fin n → Bool, (ν.prod ν) (τ σ ⁻¹' C) := by
    simp_rw [hpre]
    simp [Fintype.card_fun]
  have hsumle :
      (∑ σ : Fin n → Bool, (ν.prod ν) (τ σ ⁻¹' C)) ≤
        ((2 : ENNReal) ^ n) * ENNReal.ofReal K := by
    calc
      (∑ σ : Fin n → Bool, (ν.prod ν) (τ σ ⁻¹' C)) =
          ∑ σ : Fin n → Bool,
            ∫⁻ z, (τ σ ⁻¹' C).indicator
              (fun _ => (1 : ENNReal)) z ∂ν.prod ν := by
            apply Finset.sum_congr rfl
            intro σ hσ
            exact congrArg id
              (MeasureTheory.lintegral_indicator_one
                (hCmeas.preimage
                  (normalized_vc_swap_measure_preserving P σ).measurable)).symm
      _ = ∫⁻ z, ∑ σ : Fin n → Bool,
          (τ σ ⁻¹' C).indicator (fun _ => (1 : ENNReal)) z ∂ν.prod ν := by
            rw [MeasureTheory.lintegral_finsetSum Finset.univ]
            intro σ hσ
            exact ((measurable_const.indicator
              (hCmeas.preimage
                (normalized_vc_swap_measure_preserving P σ).measurable)))
      _ = ∫⁻ z, ((Finset.univ.filter fun σ : Fin n → Bool =>
          τ σ z ∈ C).card : ENNReal) ∂ν.prod ν := by
            congr 1
            funext z
            simp [Set.indicator, Finset.card_filter]
      _ ≤ ∫⁻ _z, ((2 : ENNReal) ^ n) * ENNReal.ofReal K ∂ν.prod ν :=
        MeasureTheory.lintegral_mono hpoint
      _ = ((2 : ENNReal) ^ n) * ENNReal.ofReal K := by simp
  rw [← hsum] at hsumle
  have hfinal : (ν.prod ν) C ≤ ENNReal.ofReal K :=
    (ENNReal.mul_le_mul_iff_left
    (by positivity : (2 : ENNReal) ^ n ≠ 0)
    (by norm_num : (2 : ENNReal) ^ n ≠ ⊤)).mp (by
      simpa [mul_comm] using hsumle)
  simpa [ν, S, C, K] using hfinal

@[blueprint "lem:normalized-vc-uniform-convergence"
  (statement := /-- Let $(\Omega,\mathcal A)$ be a measurable space, let $\mu$ be a measure on it, let $f$ be a Hellinger density relative to $\mu$, and let $\mathcal H$ be a countable class of Boolean concepts of VC dimension $d\geq1$. Assume that the event represented by every $h\in\mathcal H$ is measurable. Fix $n\geq2$ and $0<\delta<1$, and write
  \[
    A=d\log(2n+1)+\log(8/\delta),\qquad
    N_h(x)=\sum_{i=1}^n\mathbf 1_{\{h(x_i)=\mathrm{true}\}}.
  \]
  Then the probability, under the law of $n$ independent observations from $f$, of the measurable set of samples $x$ for which there exists $h\in\mathcal H$ satisfying either
  \[
    4\sqrt A<
      \frac{n\,\mathbb P_f[h]-N_h(x)}
           {\sqrt{n\,\mathbb P_f[h]}}
    \quad\text{or}\quad
    4\sqrt A<
      \frac{N_h(x)-n\,\mathbb P_f[h]}
           {\sqrt{N_h(x)}}
  \]
  is at most $\delta$. Here $\mathbb P_f[h]$ is the probability of the measurable event represented by $h$. -/)
  (proof := /-- Write $P$ for the probability measure represented by $f$, let $\nu=P^{\otimes n}$ be the product law in \cref{def:iid-sample-law}, and set
  \[
    S_h(x)=\sum_{i=1}^n\mathbf 1_{\{h(x_i)=\mathrm{true}\}},
    \qquad a_h=nP(\{h=\mathrm{true}\}),
    \qquad A=d\log(2n+1)+\log(8/\delta),
  \]
  with $T=4\sqrt A$. The inequalities $n\geq2$ and $0<\delta<1$ imply that
  $\log(2n+1)\geq0$ and $8\leq8/\delta$. Since $e<3\leq8$, monotonicity of
  the exponential and logarithm gives $1\leq\log(8/\delta)$; consequently
  $A\geq1$ and $T\geq4$.

  Fix a finite subfamily $\mathcal J\subseteq\mathcal H$. The measurability
  of the events in \cref{def:concept-event} implies directly that each
  coordinate indicator, and hence each finite sum $S_h$, is measurable;
  every $S_h$ is also nonnegative. By
  \cref{lem:normalized-vc-indicator-count-moments}, $S_h$ belongs to
  $L^2(\nu)$, has mean $a_h$, and has variance at most $a_h$. Thus
  \cref{lem:normalized-vc-ghost-symmetrization}, followed by
  \cref{lem:normalized-vc-double-sample-bound}, yields
  \[
    \nu(B_{\mathcal J})\leq4(2n+1)^d e^{-T^2/16}.
  \]
  The factor on the right is nonnegative, while
  \cref{lem:normalized-vc-exponential-budget} identifies twice this factor
  with $\delta$; hence $\nu(B_{\mathcal J})\leq\delta$ for every such
  $\mathcal J$.

  Regard the countable class $\mathcal H$ as a countable subtype and index
  its finite subfamilies by their finite subsets. The corresponding sets
  $B_{\mathcal J}$ form a monotone family under inclusion, and their union is
  exactly the exceptional event obtained by quantifying over all
  $h\in\mathcal H$. Continuity from below identifies the measure of this
  union with the supremum of the measures $\nu(B_{\mathcal J})$. The uniform
  finite-subfamily bound therefore makes this supremum at most $\delta$.
  Unfolding $S_h$, $a_h$, $T$, \cref{def:concept-event}, and
  \cref{def:iid-sample-law} gives the displayed event in the statement. -/)
  (title := /-- Normalized VC uniform convergence for a countable class -/)
  (latexEnv := "lemma")]
lemma normalized_vc_uniform_convergence {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {n d : ℕ} {δ : ℝ}
    (hn : 2 ≤ n) (hd : 1 ≤ d) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (f : hellinger_density Ω μ) (H : concept_class Ω)
    (hcount : H.Countable)
    (hvc : has_vc_dimension H d)
    (hmeas : ∀ h ∈ H, MeasurableSet (concept_event h)) :
    iid_sample_law (n := n) f
        {x | ∃ h ∈ H,
          4 * Real.sqrt
              ((d : ℝ) * Real.log (2 * (n : ℝ) + 1) +
                Real.log (8 / δ)) <
            (((n : ℝ) *
                f.toProbabilityMeasure.toMeasure.real (concept_event h)) -
              ∑ i : Fin n, if h (x i) = true then (1 : ℝ) else 0) /
              Real.sqrt ((n : ℝ) *
                f.toProbabilityMeasure.toMeasure.real (concept_event h)) ∨
          4 * Real.sqrt
              ((d : ℝ) * Real.log (2 * (n : ℝ) + 1) +
                Real.log (8 / δ)) <
            ((∑ i : Fin n, if h (x i) = true then (1 : ℝ) else 0) -
                (n : ℝ) *
                  f.toProbabilityMeasure.toMeasure.real (concept_event h)) /
              Real.sqrt
                (∑ i : Fin n, if h (x i) = true then (1 : ℝ) else 0)} ≤
      ENNReal.ofReal δ := by
  classical
  let P : MeasureTheory.ProbabilityMeasure Ω := f.toProbabilityMeasure
  let ν : MeasureTheory.Measure (Fin n → Ω) :=
    MeasureTheory.Measure.pi fun _ : Fin n => (P : MeasureTheory.Measure Ω)
  let S : (Ω → Bool) → (Fin n → Ω) → ℝ := fun h x =>
    ∑ i : Fin n, if h (x i) = true then 1 else 0
  let a : (Ω → Bool) → ℝ := fun h =>
    (n : ℝ) * (P : MeasureTheory.Measure Ω).real (concept_event h)
  let A : ℝ := (d : ℝ) * Real.log (2 * (n : ℝ) + 1) +
    Real.log (8 / δ)
  let t : ℝ := 4 * Real.sqrt A
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hbase : 1 < 2 * (n : ℝ) + 1 := by nlinarith
  have hlogbase : 0 ≤ Real.log (2 * (n : ℝ) + 1) :=
    Real.log_nonneg hbase.le
  have hC : 0 < 8 / δ := div_pos (by norm_num) hδ0
  have h8C : (8 : ℝ) ≤ 8 / δ := by
    rw [le_div_iff₀ hδ0]
    nlinarith
  have hexpC : Real.exp 1 ≤ 8 / δ :=
    (Real.exp_one_lt_three.le.trans (by norm_num)).trans h8C
  have hlogC : 1 ≤ Real.log (8 / δ) := by
    rw [← Real.exp_le_exp, Real.exp_log hC]
    exact hexpC
  have hA1 : 1 ≤ A := by
    dsimp [A]
    have hdlog : 0 ≤ (d : ℝ) * Real.log (2 * (n : ℝ) + 1) :=
      mul_nonneg (Nat.cast_nonneg d) hlogbase
    linarith
  have hsqrtA : 1 ≤ Real.sqrt A := by
    simpa using Real.sqrt_le_sqrt hA1
  have ht : 4 ≤ t := by
    dsimp [t]
    nlinarith
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hfinite : ∀ J : Finset (Ω → Bool),
      (J : Set (Ω → Bool)) ⊆ H →
      ν {x | ∃ h ∈ J,
        t < (a h - S h x) / Real.sqrt (a h) ∨
        t < (S h x - a h) / Real.sqrt (S h x)} ≤
        ENNReal.ofReal δ := by
    intro J hJ
    have hSmeas : ∀ i : ↥J, Measurable (S i.1) := by
      intro i
      have hevent : MeasurableSet (concept_event i.1) :=
        hmeas i.1 (hJ i.2)
      have hg : Measurable (fun z : Ω =>
          if i.1 z = true then (1 : ℝ) else 0) := by
        rw [show (fun z : Ω => if i.1 z = true then (1 : ℝ) else 0) =
            (concept_event i.1).indicator (fun _ => (1 : ℝ)) by
          funext z
          by_cases hz : i.1 z = true <;> simp [concept_event, hz]]
        exact measurable_const.indicator hevent
      dsimp [S]
      exact Finset.measurable_sum Finset.univ
        (fun i hi => hg.comp (measurable_pi_apply i))
    have hSnonneg : ∀ i : ↥J, ∀ x, 0 ≤ S i.1 x := by
      intro i x
      dsimp [S]
      exact Finset.sum_nonneg fun k hk => by
        split <;> positivity
    have hmom : ∀ i : ↥J,
        MeasureTheory.MemLp (S i.1) 2 ν ∧
        (∫ x, S i.1 x ∂ν) = a i.1 ∧
        ProbabilityTheory.variance (S i.1) ν ≤ a i.1 := by
      intro i
      simpa [S, a, ν, P] using
        (normalized_vc_indicator_count_moments P i.1
          (hmeas i.1 (hJ i.2)))
    have hghost := normalized_vc_ghost_symmetrization ν
      (fun i : ↥J => S i.1) (fun i : ↥J => a i.1)
      hSmeas hSnonneg hmom ht
    have hdouble := normalized_vc_double_sample_bound
      (P : MeasureTheory.Measure Ω) H (n := n) hvc J hJ
      (fun h hh => hmeas h (hJ hh)) (t := t) ht0
    let K : ℝ := (2 * (n : ℝ) + 1) ^ d * Real.exp (-t ^ 2 / 16)
    have hghost' :
        ν {x | ∃ h ∈ J,
          t < (a h - S h x) / Real.sqrt (a h) ∨
          t < (S h x - a h) / Real.sqrt (S h x)} ≤
          2 * (ν.prod ν) {z | ∃ h ∈ J,
            t / (2 * Real.sqrt 2) * Real.sqrt (S h z.2 + S h z.1) <
              S h z.2 - S h z.1 ∨
            t / (2 * Real.sqrt 2) * Real.sqrt (S h z.2 + S h z.1) <
              S h z.1 - S h z.2} := by
      simpa using hghost
    have hdouble' :
        (ν.prod ν) {z | ∃ h ∈ J,
          t / (2 * Real.sqrt 2) * Real.sqrt (S h z.2 + S h z.1) <
            S h z.2 - S h z.1 ∨
          t / (2 * Real.sqrt 2) * Real.sqrt (S h z.2 + S h z.1) <
            S h z.1 - S h z.2} ≤
          ENNReal.ofReal (2 * K) := by
      have hKr : 2 * (2 * (n : ℝ) + 1) ^ d * Real.exp (-t ^ 2 / 16) =
          2 * K := by
        dsimp [K]
        ring
      simpa only [ν, S, hKr] using hdouble
    have hbudget := normalized_vc_exponential_budget hn hd hδ0 hδ1
    have hK0 : 0 ≤ K := by
      dsimp [K]
      positivity
    have hreal : 4 * K ≤ δ := by
      dsimp [K, t, A] at hK0 ⊢
      nlinarith [hbudget]
    calc
      ν {x | ∃ h ∈ J,
          t < (a h - S h x) / Real.sqrt (a h) ∨
          t < (S h x - a h) / Real.sqrt (S h x)}
          ≤ 2 * (ν.prod ν) {z | ∃ h ∈ J,
            t / (2 * Real.sqrt 2) * Real.sqrt (S h z.2 + S h z.1) <
              S h z.2 - S h z.1 ∨
            t / (2 * Real.sqrt 2) * Real.sqrt (S h z.2 + S h z.1) <
              S h z.1 - S h z.2} := hghost'
      _ ≤ 2 * ENNReal.ofReal (2 * K) := by gcongr
      _ = ENNReal.ofReal (4 * K) := by
        rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hreal
  letI : Countable H := hcount.to_subtype
  let B : Finset H → Set (Fin n → Ω) := fun J =>
    {x | ∃ h : H, h ∈ J ∧
      (t < (a h.1 - S h.1 x) / Real.sqrt (a h.1) ∨
       t < (S h.1 x - a h.1) / Real.sqrt (S h.1 x))}
  have hBmono : Monotone B := by
    intro J K hJK x hx
    rcases hx with ⟨h, hh, hdev⟩
    exact ⟨h, hJK hh, hdev⟩
  have hBbound : ∀ J : Finset H, ν (B J) ≤ ENNReal.ofReal δ := by
    intro J
    let J' : Finset (Ω → Bool) :=
      J.map ⟨Subtype.val, Subtype.val_injective⟩
    have hJ' : (J' : Set (Ω → Bool)) ⊆ H := by
      intro h hh
      simp only [J', Finset.mem_coe, Finset.mem_map] at hh
      rcases hh with ⟨k, hk, rfl⟩
      exact k.2
    have hbound := hfinite J' hJ'
    simpa [B, J'] using hbound
  have hUnion : (⋃ J : Finset H, B J) =
      {x | ∃ h ∈ H,
        t < (a h - S h x) / Real.sqrt (a h) ∨
        t < (S h x - a h) / Real.sqrt (S h x)} := by
    ext x
    simp only [Set.mem_iUnion, B, Set.mem_setOf_eq]
    constructor
    · rintro ⟨J, h, hh, hdev⟩
      exact ⟨h.1, h.2, hdev⟩
    · rintro ⟨h, hh, hdev⟩
      let hs : H := ⟨h, hh⟩
      exact ⟨{hs}, hs, by simp, hdev⟩
  change ν {x | ∃ h ∈ H,
      t < (a h - S h x) / Real.sqrt (a h) ∨
      t < (S h x - a h) / Real.sqrt (S h x)} ≤ ENNReal.ofReal δ
  rw [← hUnion, hBmono.measure_iUnion]
  exact iSup_le hBbound

@[blueprint "lem:second-order-vc-root-deviation-bound"
  (statement := /-- Let $A,a,b\in\mathbb R$ be nonnegative. If
  \[
    \frac{b-a}{\sqrt b}\leq4\sqrt A
    \qquad\text{and}\qquad
    \frac{a-b}{\sqrt a}\leq4\sqrt A,
  \]
  then
  \[
    \frac12\bigl(\sqrt b-\sqrt a\bigr)^2\leq8A.
  \] -/)
  (proof := /-- If $a\leq b$ and $b>0$, multiply the first hypothesis by
  $\sqrt b$. Since
  $(\sqrt b-\sqrt a)\sqrt b\leq b-a$, cancellation of the positive
  factor $\sqrt b$ gives
  $\sqrt b-\sqrt a\leq4\sqrt A$. If $b=0$, nonnegativity and
  $a\leq b$ force $a=0$. The case $b\leq a$ follows symmetrically from
  the second hypothesis. Squaring the resulting absolute bound and using
  $(\sqrt A)^2=A$ gives the claim. -/)
  (title := /-- From self-normalized deviations to a square-root bound -/)
  (latexEnv := "lemma")]
lemma second_order_vc_root_deviation_bound {A a b : ℝ}
    (hA : 0 ≤ A) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hba : (b - a) / Real.sqrt b ≤ 4 * Real.sqrt A)
    (hab : (a - b) / Real.sqrt a ≤ 4 * Real.sqrt A) :
    (2 : ℝ)⁻¹ * (Real.sqrt b - Real.sqrt a) ^ (2 : ℕ) ≤ 8 * A := by
  by_cases hle : a ≤ b
  · by_cases hbzero : b = 0
    · have hazero : a = 0 := by linarith
      simp [hbzero, hazero, hA]
    · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hbzero)
      have hspos : 0 < Real.sqrt b := Real.sqrt_pos.2 hbpos
      have hsle : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt hle
      have hcross := (div_le_iff₀ hspos).mp hba
      have hprod :
          (Real.sqrt b - Real.sqrt a) * Real.sqrt b ≤
            4 * Real.sqrt A * Real.sqrt b := by
        nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
          mul_nonneg (Real.sqrt_nonneg a) (sub_nonneg.mpr hsle)]
      have hdiff : Real.sqrt b - Real.sqrt a ≤ 4 * Real.sqrt A :=
        le_of_mul_le_mul_right hprod hspos
      have hsq : (Real.sqrt b - Real.sqrt a) ^ (2 : ℕ) ≤
          (4 * Real.sqrt A) ^ (2 : ℕ) := by
        nlinarith [mul_nonneg
          (sub_nonneg.mpr hdiff)
          (add_nonneg
            (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num)
              (Real.sqrt_nonneg A))
            (sub_nonneg.mpr hsle))]
      nlinarith [Real.sq_sqrt hA]
  · have hle' : b ≤ a := le_of_not_ge hle
    by_cases hazero : a = 0
    · have hbzero : b = 0 := by linarith
      simp [hbzero, hazero, hA]
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hazero)
      have hspos : 0 < Real.sqrt a := Real.sqrt_pos.2 hap
      have hsle : Real.sqrt b ≤ Real.sqrt a := Real.sqrt_le_sqrt hle'
      have hcross := (div_le_iff₀ hspos).mp hab
      have hprod :
          (Real.sqrt a - Real.sqrt b) * Real.sqrt a ≤
            4 * Real.sqrt A * Real.sqrt a := by
        nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
          mul_nonneg (Real.sqrt_nonneg b) (sub_nonneg.mpr hsle)]
      have hdiff : Real.sqrt a - Real.sqrt b ≤ 4 * Real.sqrt A :=
        le_of_mul_le_mul_right hprod hspos
      have hsq : (Real.sqrt b - Real.sqrt a) ^ (2 : ℕ) ≤
          (4 * Real.sqrt A) ^ (2 : ℕ) := by
        nlinarith [mul_nonneg
          (sub_nonneg.mpr hdiff)
          (add_nonneg
            (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num)
              (Real.sqrt_nonneg A))
            (sub_nonneg.mpr hsle))]
      nlinarith [Real.sq_sqrt hA]

@[blueprint "lem:second-order-vc-empirical-event-mass"
  (statement := /-- Let $(\Omega,\mathcal A)$ be a measurable space, let
  $n\geq1$, let $x\colon\operatorname{Fin}(n)\to\Omega$, and let
  $h\colon\Omega\to\operatorname{Bool}$ represent a measurable event.
  Then
  \[
    P_x[\{h=\mathrm{true}\}]
      =\frac1n\sum_{i\in\operatorname{Fin}(n)}
        \mathbf 1_{\{h(x_i)=\mathrm{true}\}}.
  \] -/)
  (proof := /-- Unfold \cref{def:empirical-measure} and
  \cref{def:concept-event}. On the measurable concept event, each Dirac
  measure contributes one exactly when $h(x_i)=\mathrm{true}$. The finite
  sum of these contributions is then multiplied by $n^{-1}$, and conversion
  from extended nonnegative reals to real numbers yields the displayed
  identity because $n>0$. -/)
  (title := /-- Empirical mass of a measurable concept event -/)
  (latexEnv := "lemma")]
lemma second_order_vc_empirical_event_mass {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (x : Fin n → Ω) (h : Ω → Bool)
    (hmeas : MeasurableSet (concept_event h)) :
    (empirical_measure n x).real (concept_event h) =
      (∑ i : Fin n, if h (x i) = true then (1 : ℝ) else 0) / (n : ℝ) := by
  simp [MeasureTheory.Measure.real, empirical_measure, hmeas, hn.ne',
    concept_event, div_eq_mul_inv]
  rw [ENNReal.toReal_sum]
  · have hmeas' : MeasurableSet {x | h x = true} := by
      simpa [concept_event] using hmeas
    simp [MeasureTheory.Measure.dirac_apply' _ hmeas', Set.indicator, hn.ne',
      mul_comm]
    simp_rw [apply_ite ENNReal.toReal]
    simp
  · intro i hi
    simp [MeasureTheory.Measure.dirac_apply' _ hmeas, Set.indicator]

@[blueprint "lem:second-order-vc-uniform-convergence"
  (statement := /-- Let $(\Omega,\mathcal A)$ be a measurable space, let $\mu$ be a measure on it, let $n,d\in\mathbb N$ satisfy $n\geq2$ and $d\geq1$, and let $0<\delta<1$. Let $f$ be a Hellinger density relative to $\mu$, and let $\mathcal F$ be a family of Hellinger densities relative to $\mu$. Assume that the probability measure represented by $f$ is atomless in the sense of \cref{def:is-atomless-measure}, and that the ratio class of $\mathcal F$ is countable and has VC dimension exactly $d$. Then the probability, under $f^{\otimes n}$, of the event
  \[
    d_{\operatorname{Ratio}(\mathcal F)}(f,P_x)
      >R(n,d,\delta)
  \]
  is at most $\delta$. -/)
  (proof := /-- Every event in $\operatorname{Ratio}(\mathcal F)$ is measurable by \cref{lem:ratio-concept-event-measurable}. Apply \cref{lem:normalized-vc-uniform-convergence} to the countable class $\mathcal H=\operatorname{Ratio}(\mathcal F)$, as defined in \cref{def:ratio-concept-class}, and put
  \[
    A=d\log(2n+1)+\log(8/\delta),\quad
    a=N_h(x),\quad b=n\,\mathbb P_f[h].
  \]
  The numerical hypotheses imply $A\geq0$. Outside the exceptional set of \cref{lem:normalized-vc-uniform-convergence}, the two inequalities
  \[
    \frac{b-a}{\sqrt b}\leq4\sqrt A,
    \qquad
    \frac{a-b}{\sqrt a}\leq4\sqrt A
  \]
  hold for every $h\in\mathcal H$. By \cref{lem:second-order-vc-root-deviation-bound},
  \[
    \frac12\bigl(\sqrt b-\sqrt a\bigr)^2\leq8A.
  \]
  The identity in \cref{lem:second-order-vc-empirical-event-mass}, together with \cref{def:empirical-measure}, identifies the empirical event mass with $a/n$. Dividing the preceding inequality by $n$ therefore bounds the corresponding summand in \cref{def:modified-hellinger-distance} by $8A/n$, and hence by $32A/n=R(n,d,\delta)$ from \cref{def:uniform-convergence-radius}. If the ratio class is empty, the defining supremum is zero; otherwise, taking the supremum over $h\in\mathcal H$ gives the same radius bound. Thus the failure event is contained in the measurable exceptional set of \cref{lem:normalized-vc-uniform-convergence}. Monotonicity of the measure \cref{def:iid-sample-law} now yields the asserted probability bound. -/)
  (title := /-- Second-order VC uniform convergence -/)
  (latexEnv := "lemma")]
lemma second_order_vc_uniform_convergence {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {n d : ℕ} {δ : ℝ}
    (hn : 2 ≤ n) (hd : 1 ≤ d) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (f : hellinger_density Ω μ) (F : Set (hellinger_density Ω μ))
    (hatom : is_atomless_measure
      (f.toProbabilityMeasure : MeasureTheory.Measure Ω))
    (hratio_countable : (ratio_concept_class F).Countable)
    (hvc : has_vc_dimension (ratio_concept_class F) d) :
    iid_sample_law (n := n) f
        {x | uniform_convergence_radius n d δ <
          modified_hellinger_distance (ratio_concept_class F)
            f.toProbabilityMeasure (empirical_measure n x)} ≤
      ENNReal.ofReal δ := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hnpos : 0 < n := by omega
  have hlogbase : 0 ≤ Real.log (2 * (n : ℝ) + 1) :=
    Real.log_nonneg (by linarith)
  have hlogC : 0 ≤ Real.log (8 / δ) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hδ0]
    nlinarith
  have hA0 : 0 ≤ (d : ℝ) * Real.log (2 * (n : ℝ) + 1) + Real.log (8 / δ) := by
    have hdlog : 0 ≤ (d : ℝ) * Real.log (2 * (n : ℝ) + 1) :=
      mul_nonneg (Nat.cast_nonneg d) hlogbase
    linarith
  have hRdef : uniform_convergence_radius n d δ =
      32 * ((d : ℝ) * Real.log (2 * (n : ℝ) + 1) + Real.log (8 / δ)) /
        (n : ℝ) := by
    rw [uniform_convergence_radius]
  have hR0 : 0 ≤ uniform_convergence_radius n d δ := by
    rw [hRdef]
    positivity
  have hgen : ∀ A a b : ℝ, 0 ≤ A →
      2⁻¹ * (Real.sqrt b - Real.sqrt a) ^ (2 : ℕ) ≤ 8 * A →
      2⁻¹ * (Real.sqrt (b / (n : ℝ)) - Real.sqrt (a / (n : ℝ))) ^ (2 : ℕ) ≤
        32 * A / (n : ℝ) := by
    intro A a b hA hab
    have hsq : Real.sqrt (n : ℝ) ^ (2 : ℕ) = (n : ℝ) := Real.sq_sqrt hn0.le
    have hid : 2⁻¹ * (Real.sqrt (b / (n : ℝ)) -
          Real.sqrt (a / (n : ℝ))) ^ (2 : ℕ) =
        (2⁻¹ * (Real.sqrt b - Real.sqrt a) ^ (2 : ℕ)) / (n : ℝ) := by
      rw [Real.sqrt_div' _ hn0.le, Real.sqrt_div' _ hn0.le,
        div_sub_div_same, div_pow, hsq]
      ring
    rw [hid]
    exact div_le_div_of_nonneg_right (by linarith) hn0.le
  refine le_trans (MeasureTheory.measure_mono ?_)
    (normalized_vc_uniform_convergence hn hd hδ0 hδ1 f (ratio_concept_class F)
      hratio_countable hvc (ratio_concept_event_measurable F))
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  by_contra hcon
  simp only [Set.mem_setOf_eq, not_exists, not_and, not_or, not_lt] at hcon
  have hD : modified_hellinger_distance (ratio_concept_class F)
      (f.toProbabilityMeasure : MeasureTheory.Measure Ω)
      (empirical_measure n x) ≤ uniform_convergence_radius n d δ := by
    rw [modified_hellinger_distance]
    refine Real.sSup_le ?_ hR0
    rintro r ⟨h, hh, rfl⟩
    obtain ⟨h1, h2⟩ := hcon h hh
    have hmeasev := ratio_concept_event_measurable F h hh
    have hemp := second_order_vc_empirical_event_mass hnpos x h hmeasev
    have hb0 : 0 ≤ (n : ℝ) *
        (f.toProbabilityMeasure : MeasureTheory.Measure Ω).real
          (concept_event h) :=
      mul_nonneg hn0.le MeasureTheory.measureReal_nonneg
    have ha0 : 0 ≤ ∑ i : Fin n, if h (x i) = true then (1 : ℝ) else 0 :=
      Finset.sum_nonneg (fun i _ => by positivity)
    have hkey := second_order_vc_root_deviation_bound hA0 ha0 hb0 h1 h2
    have hbn : (f.toProbabilityMeasure : MeasureTheory.Measure Ω).real
          (concept_event h) =
        ((n : ℝ) * (f.toProbabilityMeasure : MeasureTheory.Measure Ω).real
          (concept_event h)) / (n : ℝ) := by
      field_simp
    rw [hemp, hbn, hRdef]
    exact hgen _ _ _ hA0 hkey
  linarith

@[blueprint "lem:uniform-convergence-entropy-bound"
  (statement := /-- Let $(\Omega,\mathcal A)$ be a measurable space, let $\mu$ be a measure on it, let $n,d\in\mathbb N$ satisfy $n\geq2$ and $d\geq1$, and let $\delta\in\mathbb R$ satisfy $0<\delta<1$. Let $f$ be a Hellinger density relative to $\mu$, and let $\mathcal F$ be a family of Hellinger densities relative to $\mu$. Suppose that the probability measure represented by $f$ is atomless and that the ratio class of $\mathcal F$ is countable and has VC dimension exactly $d$. Then the probability under $f^{\otimes n}$ of the event
  \[
    z\bigl(d_{\operatorname{Ratio}(\mathcal F)}(f,P_x)\bigr)
      >32\,
        \frac{\bigl(d\log(2n+1)+\log(8/\delta)\bigr)\log n}{n}.
  \]
  is at most $\delta$. -/)
  (proof := /-- Put
  \[
    A=d\log(2n+1)+\log(8/\delta),
    \qquad R=32A/n.
  \]
  The assumptions imply $A\geq\log 8\geq1$, and hence
  $R\geq e/n>0$. Therefore
  $\log R\geq1-\log n$, so, whenever $R\leq1$,
  \[
    z(R)=R(1-\log R)\leq R\log n
      =32\operatorname{SourceComp}(n,d,\delta),
  \]
  where the definitions are those of \cref{def:entropy-envelope,def:uniform-convergence-radius,def:source-complexity-term}.
  For a sample $x$, \cref{lem:density-measure-univ} and
  \cref{lem:empirical-measure-univ} allow
  \cref{lem:modified-hellinger-range} to be applied to
  $D=d_{\operatorname{Ratio}(\mathcal F)}(f,P_x)$, giving
  $0\leq D\leq1$. If $D\leq R\leq1$, then
  \cref{lem:entropy-envelope-monotone} gives
  $z(D)\leq z(R)$, and the preceding estimate applies. If $D\leq R$
  but $R>1$, the same monotonicity gives $z(D)\leq z(1)=1$.
  In this second case the target threshold is at least one: for $n=2$,
  the bound $A\geq1$ gives $R\geq16$ and
  $R\log2>1$, whereas for $n\geq3$ one has
  $R\log n>\log3>1$.
  Thus every sample in the entropy failure event satisfies $D>R$.
  The entropy failure event is therefore contained in the event controlled
  by \cref{lem:second-order-vc-uniform-convergence}; the countability
  hypothesis of that lemma is precisely the assumed countability of
  $\operatorname{Ratio}(\mathcal F)$. Monotonicity of the measure yields the
  stated bound. -/)
  (title := /-- Entropy form of the VC uniform-convergence estimate -/)
  (latexEnv := "lemma")]
lemma uniform_convergence_entropy_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {n d : ℕ} {δ : ℝ}
    (hn : 2 ≤ n) (hd : 1 ≤ d) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (f : hellinger_density Ω μ) (F : Set (hellinger_density Ω μ))
    (hatom : is_atomless_measure
      (f.toProbabilityMeasure : MeasureTheory.Measure Ω))
    (hratio_countable : (ratio_concept_class F).Countable)
    (hvc : has_vc_dimension (ratio_concept_class F) d) :
    iid_sample_law (n := n) f
        {x | 32 * source_complexity_term n d δ <
          entropy_envelope
            (modified_hellinger_distance (ratio_concept_class F)
              f.toProbabilityMeasure (empirical_measure n x))} ≤
      ENNReal.ofReal δ := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogbase : 0 ≤ Real.log (2 * (n : ℝ) + 1) :=
    Real.log_nonneg (by linarith)
  have hlogn0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hexp1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  obtain ⟨A, hA1, hR, hS⟩ : ∃ A : ℝ, 1 ≤ A ∧
      uniform_convergence_radius n d δ = 32 * A / (n : ℝ) ∧
      source_complexity_term n d δ = A * Real.log (n : ℝ) / (n : ℝ) := by
    refine ⟨(d : ℝ) * Real.log (2 * (n : ℝ) + 1) + Real.log (8 / δ), ?_, ?_, ?_⟩
    · have hdlog : 0 ≤ (d : ℝ) * Real.log (2 * (n : ℝ) + 1) :=
        mul_nonneg (Nat.cast_nonneg d) hlogbase
      have h8C : (8 : ℝ) ≤ 8 / δ := by
        rw [le_div_iff₀ hδ0]
        nlinarith
      have hlogC : (1 : ℝ) ≤ Real.log (8 / δ) := by
        rw [show (1 : ℝ) = Real.log (Real.exp 1) by simp]
        exact Real.log_le_log (Real.exp_pos 1) (by nlinarith)
      linarith
    · rw [uniform_convergence_radius]
    · rw [source_complexity_term]
  have hRpos : 0 < uniform_convergence_radius n d δ := by
    rw [hR]
    exact div_pos (by linarith) hn0
  have hRA : 0 < 32 * A / (n : ℝ) := by rw [← hR]; exact hRpos
  have h32S : 32 * source_complexity_term n d δ =
      (32 * A / (n : ℝ)) * Real.log (n : ℝ) := by
    rw [hS]
    field_simp
  have main : ∀ D : ℝ, 0 ≤ D → D ≤ 1 →
      D ≤ uniform_convergence_radius n d δ →
      entropy_envelope D ≤ 32 * source_complexity_term n d δ := by
    intro D hD0 hD1 hDR
    rcases le_or_gt (uniform_convergence_radius n d δ) 1 with hR1 | hR1
    · have hmono := entropy_envelope_monotone ⟨hD0, hD1⟩ ⟨hRpos.le, hR1⟩ hDR
      have hRlow : 32 / (n : ℝ) ≤ 32 * A / (n : ℝ) := by
        apply div_le_div_of_nonneg_right (by linarith) hn0.le
      have hlogR : Real.log (32 / (n : ℝ)) ≤ Real.log (32 * A / (n : ℝ)) :=
        Real.log_le_log (by positivity) hRlow
      have hsplit : Real.log (32 / (n : ℝ)) = Real.log 32 - Real.log (n : ℝ) :=
        Real.log_div (by norm_num) (ne_of_gt hn0)
      have hlog32 : (1 : ℝ) ≤ Real.log 32 := by
        rw [show (1 : ℝ) = Real.log (Real.exp 1) by simp]
        exact Real.log_le_log (Real.exp_pos 1) (by nlinarith)
      have h1 : 1 - Real.log (32 * A / (n : ℝ)) ≤ Real.log (n : ℝ) := by
        linarith
      have hzR : entropy_envelope (uniform_convergence_radius n d δ) ≤
          32 * source_complexity_term n d δ := by
        rw [entropy_envelope, Real.negMulLog_def, hR, h32S]
        linarith [mul_le_mul_of_nonneg_left h1 hRA.le]
      linarith
    · have hone : entropy_envelope (1 : ℝ) = 1 := by
        simp [entropy_envelope, Real.negMulLog_def]
      have hmono := entropy_envelope_monotone ⟨hD0, hD1⟩
        ⟨zero_le_one, le_rfl⟩ hD1
      rw [hone] at hmono
      have hthresh : (1 : ℝ) ≤ 32 * source_complexity_term n d δ := by
        rw [h32S]
        rcases eq_or_lt_of_le hn with h2 | h3
        · have hn2 : (n : ℝ) = 2 := by exact_mod_cast h2.symm
          rw [hn2]
          nlinarith [Real.log_two_gt_d9]
        · have hn3 : (3 : ℝ) ≤ (n : ℝ) := by
            have : (3 : ℕ) ≤ n := h3
            exact_mod_cast this
          have hlogn1 : 1 < Real.log (n : ℝ) := by
            rw [show (1 : ℝ) = Real.log (Real.exp 1) by simp]
            exact Real.log_lt_log (Real.exp_pos 1) (by nlinarith)
          have hRgt : (1 : ℝ) < 32 * A / (n : ℝ) := by rw [← hR]; exact hR1
          nlinarith [mul_pos (sub_pos.2 hRgt) (sub_pos.2 hlogn1)]
      linarith
  refine le_trans (MeasureTheory.measure_mono ?_)
    (second_order_vc_uniform_convergence hn hd hδ0 hδ1 f F hatom
      hratio_countable hvc)
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  simp only [Set.mem_setOf_eq]
  by_contra hcon
  rw [not_lt] at hcon
  have hrange := modified_hellinger_range (ratio_concept_class F)
    (f.toProbabilityMeasure : MeasureTheory.Measure Ω) (empirical_measure n x)
    (density_measure_univ f) (empirical_measure_univ (by omega) x)
  linarith [main _ hrange.1 hrange.2 hcon]

@[blueprint "lem:entropy-envelope-le-target-penalty"
  (statement := /-- There is a fixed numerical comparison between the source entropy envelope and the target base-two penalty: for every $x\in[0,1]$,
  \[
    z(x)\leq2\Phi(x).
  \] -/)
  (proof := /-- Since $x\geq0$, either $x=0$ or $x>0$. In the first case, expanding \cref{def:entropy-envelope}, \cref{def:hellinger-log-penalty}, and \cref{def:binary-logarithm} shows that both sides vanish. Suppose that $0<x\leq1$. Then $\log x\leq0$, while $0<\log2\leq1$, where the upper bound follows from $\log t\leq t-1$ at $t=2$. Hence both $\log x$ and $\log2-2$ are nonpositive, so
  \[
    0\leq \log x\,(\log2-2).
  \]
  Expanding the same three definitions and using $\log(2/x)=\log2-\log x$, factor out the nonnegative number $x$. After multiplying by the positive number $\log2$, the remaining inequality is
  \[
    (1-\log x)\log2\leq2(\log2-\log x).
  \]
  The right-hand side minus the left-hand side equals $\log2+\log x\,(\log2-2)$, which is nonnegative by the two preceding sign inequalities. -/)
  (title := /-- Comparison of logarithmic Hellinger penalties -/)
  (latexEnv := "lemma")]
lemma entropy_envelope_le_target_penalty {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    entropy_envelope x ≤ 2 * hellinger_log_penalty x := by
  rcases eq_or_lt_of_le hx0 with rfl | hx
  · norm_num [entropy_envelope, hellinger_log_penalty, binary_logarithm,
      Real.negMulLog]
  · have hxne : x ≠ 0 := ne_of_gt hx
    have hlogx : Real.log x ≤ 0 := Real.log_nonpos hx0 hx1
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2le : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      norm_num at h
      exact h
    have hprod : 0 ≤ Real.log x * (Real.log 2 - 2) :=
      mul_nonneg_of_nonpos_of_nonpos hlogx (by linarith)
    rw [entropy_envelope, hellinger_log_penalty, binary_logarithm,
      Real.negMulLog, Real.log_div (by norm_num) hxne]
    calc
      x + -x * Real.log x = x * (1 - Real.log x) := by ring
      _ ≤ x * (2 * (Real.log 2 - Real.log x) / Real.log 2) := by
        apply mul_le_mul_of_nonneg_left _ hx0
        rw [le_div_iff₀ hlog2pos]
        nlinarith
      _ = 2 * (x * ((Real.log 2 - Real.log x) / Real.log 2)) := by ring

@[blueprint "lem:source-complexity-le-target-complexity"
  (statement := /-- Let $n,d\in\mathbb N$ and $\delta\in\mathbb R$ satisfy $n\geq2$, $d\geq1$, and $0<\delta<1$. Then the source natural-logarithm complexity term is at most four times the target base-two complexity term:
  \[
    \operatorname{SourceComp}(n,d,\delta)
      \leq4\operatorname{VCComp}(n,d,\delta).
  \] -/)
  (proof := /-- Expand \cref{def:source-complexity-term}, \cref{def:vc-complexity-term}, and \cref{def:binary-logarithm}. Since $n\geq2$, the nonnegativity of $(n-2)(n^2+2n+2)$ gives $2n+1\leq n^3$; monotonicity of the logarithm and the power identity therefore give $\log(2n+1)\leq3\log n$. Since $0<\delta<1$, one has $\delta^3\leq\delta$ and hence $8/\delta\leq(2/\delta)^3$, so likewise $\log(8/\delta)\leq3\log(2/\delta)$. Multiplication by the nonnegative quantities $d$ and $\log n$ shows that the source numerator is at most three times the corresponding natural-logarithm target numerator. Finally, $0<\log2<1$, while $\log n$ and $\log(2/\delta)$ are nonnegative; thus division of either logarithm by $\log2$ can only increase it. The base-two target numerator consequently dominates the natural-logarithm target numerator. Division by the positive number $n$ preserves the inequality, and replacing the factor three by four proves the claim. -/)
  (title := /-- Comparison of source and target complexity scales -/)
  (latexEnv := "lemma")]
lemma source_complexity_le_target_complexity {n d : ℕ} {δ : ℝ}
    (hn : 2 ≤ n) (hd : 1 ≤ d) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    source_complexity_term n d δ ≤
      4 * vc_complexity_term n d δ := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by
    linarith
  have hn1 : 1 < (n : ℝ) := by
    linarith
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast hd
  have hd0 : 0 ≤ (d : ℝ) := by
    linarith
  have hlogn0 : 0 ≤ Real.log (n : ℝ) :=
    (Real.log_pos hn1).le
  have hn_cube : 2 * (n : ℝ) + 1 ≤ (n : ℝ) ^ 3 := by
    have hfactor :
        0 ≤ ((n : ℝ) - 2) * ((n : ℝ) ^ 2 + 2 * (n : ℝ) + 2) := by
      positivity
    nlinarith
  have hlog_n :
      Real.log (2 * (n : ℝ) + 1) ≤ 3 * Real.log (n : ℝ) := by
    have h := (Real.log_le_log_iff (by positivity) (pow_pos hn0 3)).2 hn_cube
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hδsq : δ * δ ≤ (1 : ℝ) * 1 :=
    mul_self_le_mul_self hδ0.le hδ1.le
  have hδcube : δ ^ 3 ≤ δ := by
    calc
      δ ^ 3 = δ * (δ * δ) := by ring
      _ ≤ δ * (1 * 1) := mul_le_mul_of_nonneg_left hδsq hδ0.le
      _ = δ := by ring
  have hconf_arg : 8 / δ ≤ (2 / δ) ^ 3 := by
    rw [div_pow]
    norm_num
    exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hδ0 3) hδcube
  have hlog_conf : Real.log (8 / δ) ≤ 3 * Real.log (2 / δ) := by
    have h := (Real.log_le_log_iff (div_pos (by norm_num) hδ0)
      (pow_pos (div_pos (by norm_num) hδ0) 3)).2 hconf_arg
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have htwoδ : 1 < 2 / δ := by
    apply (lt_div_iff₀ hδ0).2
    linarith
  have hlogconf0 : 0 ≤ Real.log (2 / δ) :=
    (Real.log_pos htwoδ).le
  have hsource_bracket :
      (d : ℝ) * Real.log (2 * (n : ℝ) + 1) + Real.log (8 / δ) ≤
        3 * ((d : ℝ) * Real.log (n : ℝ) + Real.log (2 / δ)) := by
    have hdlog := mul_le_mul_of_nonneg_left hlog_n hd0
    nlinarith
  have hlog2pos : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hlog2le : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h
    exact h.le
  have hlogn_div :
      Real.log (n : ℝ) ≤ Real.log (n : ℝ) / Real.log (2 : ℝ) := by
    apply (le_div_iff₀ hlog2pos).2
    nlinarith [mul_nonneg hlogn0 (sub_nonneg.mpr hlog2le)]
  have hlogconf_div :
      Real.log (2 / δ) ≤ Real.log (2 / δ) / Real.log (2 : ℝ) := by
    apply (le_div_iff₀ hlog2pos).2
    nlinarith [mul_nonneg hlogconf0 (sub_nonneg.mpr hlog2le)]
  have htarget_bracket :
      (d : ℝ) * Real.log (n : ℝ) + Real.log (2 / δ) ≤
        (d : ℝ) * (Real.log (n : ℝ) / Real.log (2 : ℝ)) +
          Real.log (2 / δ) / Real.log (2 : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hlogn_div hd0]
  have htarget_bracket_nonneg :
      0 ≤ (d : ℝ) * (Real.log (n : ℝ) / Real.log (2 : ℝ)) +
        Real.log (2 / δ) / Real.log (2 : ℝ) := by
    positivity
  have hproduct :
      ((d : ℝ) * Real.log (n : ℝ) + Real.log (2 / δ)) * Real.log (n : ℝ) ≤
        ((d : ℝ) * (Real.log (n : ℝ) / Real.log (2 : ℝ)) +
          Real.log (2 / δ) / Real.log (2 : ℝ)) *
            (Real.log (n : ℝ) / Real.log (2 : ℝ)) := by
    exact mul_le_mul htarget_bracket hlogn_div hlogn0 htarget_bracket_nonneg
  have hsource_product :
      ((d : ℝ) * Real.log (2 * (n : ℝ) + 1) + Real.log (8 / δ)) *
          Real.log (n : ℝ) ≤
        4 * (((d : ℝ) * (Real.log (n : ℝ) / Real.log (2 : ℝ)) +
          Real.log (2 / δ) / Real.log (2 : ℝ)) *
            (Real.log (n : ℝ) / Real.log (2 : ℝ))) := by
    have hmul := mul_le_mul_of_nonneg_right hsource_bracket hlogn0
    have hbase_nonneg :
        0 ≤ ((d : ℝ) * Real.log (n : ℝ) + Real.log (2 / δ)) *
          Real.log (n : ℝ) := by
      positivity
    nlinarith
  unfold source_complexity_term vc_complexity_term binary_logarithm
  calc
    (((d : ℝ) * Real.log (2 * (n : ℝ) + 1) + Real.log (8 / δ)) *
        Real.log (n : ℝ)) / (n : ℝ) ≤
      (4 * (((d : ℝ) * (Real.log (n : ℝ) / Real.log (2 : ℝ)) +
        Real.log (2 / δ) / Real.log (2 : ℝ)) *
          (Real.log (n : ℝ) / Real.log (2 : ℝ)))) / (n : ℝ) :=
            div_le_div_of_nonneg_right hsource_product hn0.le
    _ = 4 * (((d : ℝ) * (Real.log (n : ℝ) / Real.log (2 : ℝ)) +
        Real.log (2 / δ) / Real.log (2 : ℝ)) *
          (Real.log (n : ℝ) / Real.log (2 : ℝ)) / (n : ℝ)) := by ring

@[blueprint "lem:approximation-slack-entropy-bound"
  (statement := /-- Let $n,d\in\mathbb N$ and $\delta,\varepsilon\in\mathbb R$ satisfy
  $n\geq2$, $d\geq1$, $0<\delta<1$, and
  \[
    0\leq\varepsilon\leq\frac1n,
  \]
  Then the entropy contribution of $\varepsilon$ is absorbed by the target complexity scale:
  \[
    z(\varepsilon)\leq
      2\operatorname{VCComp}(n,d,\delta).
  \] -/)
  (proof := /-- Since $n\geq2$, the numbers $\varepsilon$ and $1/n$ lie in
  $[0,1]$. Thus \cref{lem:entropy-envelope-monotone} gives
  $z(\varepsilon)\leq z(1/n)$. Expanding \cref{def:entropy-envelope} and using
  $\log(1/n)=-\log n$ yields
  \[
    z(1/n)=\frac{1+\log n}{n}.
  \]
  Put $L=\log_2 n$ and $C=\log_2(2/\delta)$. Monotonicity of the logarithm,
  together with $n\geq2$ and $0<\delta<1$, gives $L\geq1$ and $C\geq1$.
  Moreover, $0<\log2\leq1$ implies $\log n\leq L$. Since $d\geq1$, it follows
  that
  \[
    1+\log n\leq L+1\leq(dL+C)L
      \leq2(dL+C)L.
  \]
  Divide by the positive number $n$ and expand
  \cref{def:vc-complexity-term} and \cref{def:binary-logarithm} to obtain the
  claimed inequality. -/)
  (title := /-- Entropy cost of an approximate optimization slack -/)
  (latexEnv := "lemma")]
lemma approximation_slack_entropy_bound {n d : ℕ} {δ ε : ℝ}
    (hn : 2 ≤ n) (hd : 1 ≤ d) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hε0 : 0 ≤ ε) (hεn : ε ≤ (n : ℝ)⁻¹) :
    entropy_envelope ε ≤ 2 * vc_complexity_term n d δ := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by
    linarith
  have hn1 : 1 < (n : ℝ) := by
    linarith
  have hinv0 : 0 ≤ (n : ℝ)⁻¹ := (inv_pos.mpr hn0).le
  have hinv1 : (n : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hn0).2 hn1.le
  have hmono :
      entropy_envelope ε ≤ entropy_envelope (n : ℝ)⁻¹ :=
    entropy_envelope_monotone ⟨hε0, hεn.trans hinv1⟩
      ⟨hinv0, hinv1⟩ hεn
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast hd
  have hlogn0 : 0 ≤ Real.log (n : ℝ) := (Real.log_pos hn1).le
  have hlog2pos : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hlog2le : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    exact h
  have hlogn_div :
      Real.log (n : ℝ) ≤ Real.log (n : ℝ) / Real.log (2 : ℝ) := by
    apply (le_div_iff₀ hlog2pos).2
    nlinarith [mul_nonneg hlogn0 (sub_nonneg.mpr hlog2le)]
  have hlog2n :
      1 ≤ Real.log (n : ℝ) / Real.log (2 : ℝ) := by
    rw [le_div_iff₀ hlog2pos]
    simpa only [one_mul] using Real.log_le_log (by norm_num) hnR
  have htwoδ : (2 : ℝ) ≤ 2 / δ := by
    apply (le_div_iff₀ hδ0).2
    nlinarith
  have hlog2δ :
      1 ≤ Real.log (2 / δ) / Real.log (2 : ℝ) := by
    rw [le_div_iff₀ hlog2pos]
    simpa only [one_mul] using Real.log_le_log (by norm_num) htwoδ
  let L := Real.log (n : ℝ) / Real.log (2 : ℝ)
  let C := Real.log (2 / δ) / Real.log (2 : ℝ)
  have hL0 : 0 ≤ L := by
    dsimp [L]
    positivity
  have hL1 : 1 ≤ L := by
    simpa [L] using hlog2n
  have hC1 : 1 ≤ C := by
    simpa [C] using hlog2δ
  have hdL : L ≤ (d : ℝ) * L := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hdR hL0
  have hbracket : L + 1 ≤ (d : ℝ) * L + C := by
    linarith
  have hsum0 : 0 ≤ L + 1 := by
    linarith
  have hsum_mul : L + 1 ≤ (L + 1) * L := by
    nlinarith [mul_nonneg hsum0 (sub_nonneg.mpr hL1)]
  have hproduct :
      L + 1 ≤ ((d : ℝ) * L + C) * L :=
    hsum_mul.trans (mul_le_mul_of_nonneg_right hbracket hL0)
  have hproduct0 : 0 ≤ ((d : ℝ) * L + C) * L := by
    linarith
  have hnum :
      1 + Real.log (n : ℝ) ≤
        2 * (((d : ℝ) * L + C) * L) := by
    have : 1 + Real.log (n : ℝ) ≤ L + 1 := by
      linarith
    nlinarith
  calc
    entropy_envelope ε ≤ entropy_envelope (n : ℝ)⁻¹ := hmono
    _ = (1 + Real.log (n : ℝ)) / (n : ℝ) := by
      simp only [entropy_envelope, Real.negMulLog_def, Real.log_inv]
      ring
    _ ≤ (2 * (((d : ℝ) * L + C) * L)) / (n : ℝ) :=
      div_le_div_of_nonneg_right hnum hn0.le
    _ = 2 * vc_complexity_term n d δ := by
      unfold vc_complexity_term binary_logarithm
      dsimp [L, C]
      ring

@[blueprint "lem:simultaneous-target-oracle-bound"
  (statement := /-- Let $(\Omega,\mathcal A)$ be a measurable space, let
  $\mu$ be a measure on $\Omega$, and let $n,d\in\mathbb N$ and
  $\delta,\varepsilon\in\mathbb R$ satisfy $n\geq2$, $d\geq1$,
  $0<\delta<1$, and $0\leq\varepsilon\leq1/n$. Let $f$ be a Hellinger
  density relative to $\mu$, let $\mathcal F$ be a family of Hellinger
  densities relative to $\mu$, and let $\widehat f$ map each sample
  $x:\operatorname{Fin}(n)\to\Omega$ to a Hellinger density relative to
  $\mu$. Suppose that $\widehat f$ is an $\varepsilon$-approximate
  minimum-distance estimator over $\mathcal F$ with respect to
  $\operatorname{Ratio}(\mathcal F)$, that the
  probability measure represented by $f$ is atomless in the sense of
  \cref{def:is-atomless-measure}, and that
  $\operatorname{Ratio}(\mathcal F)$ is countable and has VC dimension
  exactly $d$. Then, under the i.i.d. sample law $f^{\otimes n}$, the
  probability of the event on which the following inequality fails for at
  least one $g\in\mathcal F$ is at most $\delta$:
  \[
    H^2(f,\widehat f(x))
      \leq400000\left(
        \Phi(H^2(f,g))+
        \operatorname{VCComp}(n,d,\delta)\right).
  \] -/)
  (proof := /-- Since $n\geq2$, one has $1/n\leq1$, and hence
  $\varepsilon\leq1$. The assumed countability of
  $\operatorname{Ratio}(\mathcal F)$ supplies the countability hypothesis of
  \cref{lem:uniform-convergence-entropy-bound}. Outside the failure event in
  that lemma, apply
  \cref{lem:deterministic-estimator-oracle-bound} for each
  $g\in\mathcal F$. By \cref{lem:squared-hellinger-range},
  $H^2(f,g)\in[0,1]$, so
  \cref{lem:entropy-envelope-le-target-penalty} gives
  $z(H^2(f,g))\leq2\Phi(H^2(f,g))$. Moreover,
  \cref{lem:entropy-envelope-dominates} and the same comparison show that
  $\Phi(H^2(f,g))\geq0$. The definitions
  \cref{def:binary-logarithm,def:vc-complexity-term}, together with
  $n\geq2$ and $0<\delta<1$, show that
  $\operatorname{VCComp}(n,d,\delta)\geq0$.
  The bound defining the complement of the uniform-convergence failure event
  and \cref{lem:source-complexity-le-target-complexity} bound the empirical
  contribution by
  $307200\operatorname{VCComp}(n,d,\delta)$. The nonnegativity of
  $\varepsilon$ follows from the approximate-estimator predicate, so
  \cref{lem:approximation-slack-entropy-bound} bounds the remaining
  $800z(\varepsilon)$ by
  $1600\operatorname{VCComp}(n,d,\delta)$. Consequently the deterministic
  bound is at most
  $4004\Phi(H^2(f,g))+308800\operatorname{VCComp}(n,d,\delta)$, which is
  at most $400000(\Phi(H^2(f,g))+
  \operatorname{VCComp}(n,d,\delta))$. Thus failure of the simultaneous
  inequality implies the uniform-convergence failure event. Monotonicity of
  probability and \cref{lem:uniform-convergence-entropy-bound} prove
  the claim. -/)
  (title := /-- Simultaneous high-probability oracle inequality -/)
  (latexEnv := "lemma")]
lemma simultaneous_target_oracle_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {n d : ℕ} {δ ε : ℝ}
    (hn : 2 ≤ n) (hd : 1 ≤ d) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (f : hellinger_density Ω μ) (F : Set (hellinger_density Ω μ))
    (hat : (Fin n → Ω) → hellinger_density Ω μ)
    (hatom : is_atomless_measure
      (f.toProbabilityMeasure : MeasureTheory.Measure Ω))
    (hratio_countable : (ratio_concept_class F).Countable)
    (hvc : has_vc_dimension (ratio_concept_class F) d)
    (hεn : ε ≤ (n : ℝ)⁻¹)
    (hhat : is_approximate_minimum_distance_estimator n
      (ratio_concept_class F) F ε hat) :
    iid_sample_law (n := n) f
        {x | ¬ ∀ g ∈ F, squared_hellinger f (hat x) ≤
          400000 * (hellinger_log_penalty (squared_hellinger f g) +
            vc_complexity_term n d δ)} ≤
      ENNReal.ofReal δ := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hε0 : 0 ≤ ε := hhat.1
  have hinv1 : (n : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hn0).2 (by linarith)
  have hε1 : ε ≤ 1 := le_trans hεn hinv1
  have hvc0 : 0 ≤ vc_complexity_term n d δ := by
    have h := approximation_slack_entropy_bound (n := n) (d := d) (δ := δ)
      (ε := 0) hn hd hδ0 hδ1 le_rfl (by positivity)
    simpa [entropy_envelope, Real.negMulLog] using h
  have hsrc := source_complexity_le_target_complexity hn hd hδ0 hδ1
  have hslack := approximation_slack_entropy_bound hn hd hδ0 hδ1 hε0 hεn
  refine le_trans (MeasureTheory.measure_mono ?_)
    (uniform_convergence_entropy_bound hn hd hδ0 hδ1 f F hatom
      hratio_countable hvc)
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  simp only [Set.mem_setOf_eq]
  by_contra hcon
  rw [not_lt] at hcon
  apply hx
  intro g hg
  have hdet := deterministic_estimator_oracle_bound hn hε1 hhat f x g hg
  have hsq := squared_hellinger_range f g
  have hpen := entropy_envelope_le_target_penalty hsq.1 hsq.2
  have hdom := entropy_envelope_dominates hsq.1 hsq.2
  have hphi0 : 0 ≤ hellinger_log_penalty (squared_hellinger f g) := by
    linarith
  linarith

@[blueprint "lem:infimum-oracle-bound"
  (statement := /-- Let $(\Omega,\mathcal A)$ be a measurable space, let $\mu$ be a
  measure on $\Omega$, let $n,d\in\mathbb N$ and
  $\delta,\varepsilon\in\mathbb R$ satisfy $n\geq2$, $d\geq1$, and
  $0<\delta<1$, and let $f$ be a Hellinger density relative to $\mu$.
  Let $\mathcal F$ be a nonempty family of Hellinger densities relative to
  $\mu$, and let $\widehat f$ map samples
  $x:\operatorname{Fin}(n)\to\Omega$ to Hellinger densities relative to
  $\mu$. Suppose that the probability measure represented by $f$ is atomless
  in the sense of \cref{def:is-atomless-measure}, that the ratio class of
  $\mathcal F$ is countable and has VC dimension exactly $d$, and that
  $0\leq\varepsilon\leq1/n$. Suppose also that $\widehat f$ is an
  $\varepsilon$-approximate ratio-class minimum-distance estimator and that
  the sample-to-loss map $x\mapsto H^2(f,\widehat f(x))$ is measurable. Then,
  under the i.i.d. sample law represented by $f$, the following measurable
  event has probability at least $1-\delta$:
  \[
    H^2(f,\widehat f(x))
      \leq400000\left(
        \inf_{g\in\mathcal F}\Phi(H^2(f,g))+
        \operatorname{VCComp}(n,d,\delta)\right).
  \] -/)
  (proof := /-- Let $S$ denote the displayed success event. Its measurability
  follows from the assumed measurability of
  $x\mapsto H^2(f,\widehat f(x))$. The assumed countability of the ratio
  class supplies the corresponding hypothesis of
  \cref{lem:simultaneous-target-oracle-bound}. Fix a sample $x$ for which the
  simultaneous inequalities of that lemma hold. The set
  whose infimum defines \cref{def:best-approximation-penalty} is nonempty
  because $\mathcal F$ is nonempty. Moreover,

  \[
    \frac{H^2(f,\widehat f(x))}{400000}
      -\operatorname{VCComp}(n,d,\delta)
  \]

  is a lower bound for this set, by the simultaneous inequality for each
  $g\in\mathcal F$. The greatest-lower-bound property therefore yields the
  defining inequality of $S$. Hence $S^{\complement}$ is contained in the
  simultaneous failure event, and
  \cref{lem:simultaneous-target-oracle-bound} bounds its probability by
  $\operatorname{ofReal}(\delta)$. Finally, the measure
  \cref{def:iid-sample-law} has total mass one. Applying the measure-complement
  identity to the measurable set $S^{\complement}$ and using
  $\operatorname{ofReal}(1-\delta)=1-\operatorname{ofReal}(\delta)$ gives the
  asserted lower bound for the probability of $S$. -/)
  (title := /-- High-probability oracle inequality at the best approximation -/)
  (latexEnv := "lemma")]
lemma infimum_oracle_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {n d : ℕ} {δ ε : ℝ}
    (hn : 2 ≤ n) (hd : 1 ≤ d) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (f : hellinger_density Ω μ) (F : Set (hellinger_density Ω μ))
    (hF : F.Nonempty)
    (hat : (Fin n → Ω) → hellinger_density Ω μ)
    (hatom : is_atomless_measure
      (f.toProbabilityMeasure : MeasureTheory.Measure Ω))
    (hratio_countable : (ratio_concept_class F).Countable)
    (hvc : has_vc_dimension (ratio_concept_class F) d)
    (hεn : ε ≤ (n : ℝ)⁻¹)
    (hhat : is_approximate_minimum_distance_estimator n
      (ratio_concept_class F) F ε hat)
    (hmeas : Measurable (fun x => squared_hellinger f (hat x))) :
    iid_sample_law (n := n) f
        {x | squared_hellinger f (hat x) ≤
          400000 * (best_approximation_penalty f F +
            vc_complexity_term n d δ)} ≥
      ENNReal.ofReal (1 - δ) := by
  have hsimul := simultaneous_target_oracle_bound hn hd hδ0 hδ1 f F hat hatom
    hratio_countable hvc hεn hhat
  set S : Set (Fin n → Ω) :=
    {x | squared_hellinger f (hat x) ≤
      400000 * (best_approximation_penalty f F +
        vc_complexity_term n d δ)} with hS
  have hsub : Sᶜ ⊆
      {x | ¬ ∀ g ∈ F, squared_hellinger f (hat x) ≤
        400000 * (hellinger_log_penalty (squared_hellinger f g) +
          vc_complexity_term n d δ)} := by
    intro x hx
    simp only [Set.mem_setOf_eq]
    intro hall
    apply hx
    simp only [hS, Set.mem_setOf_eq]
    have hlb : squared_hellinger f (hat x) / 400000 -
        vc_complexity_term n d δ ≤ best_approximation_penalty f F := by
      rw [best_approximation_penalty]
      refine le_csInf ?_ ?_
      · obtain ⟨g, hg⟩ := hF
        exact ⟨_, g, hg, rfl⟩
      · rintro r ⟨g, hg, rfl⟩
        have hg' := hall g hg
        linarith
    linarith
  have hcompl : iid_sample_law (n := n) f Sᶜ ≤ ENNReal.ofReal δ :=
    le_trans (MeasureTheory.measure_mono hsub) hsimul
  have huniv : iid_sample_law (n := n) f Set.univ = 1 := by
    simp [iid_sample_law]
  have hadd : (1 : ENNReal) ≤
      iid_sample_law (n := n) f S + iid_sample_law (n := n) f Sᶜ := by
    have hle := MeasureTheory.measure_union_le
      (μ := iid_sample_law (n := n) f) S Sᶜ
    rw [Set.union_compl_self, huniv] at hle
    exact hle
  have hofReal : ENNReal.ofReal (1 - δ) = 1 - ENNReal.ofReal δ := by
    rw [ENNReal.ofReal_sub _ hδ0.le]
    simp
  rw [ge_iff_le, hofReal]
  calc (1 : ENNReal) - ENNReal.ofReal δ
      ≤ 1 - iid_sample_law (n := n) f Sᶜ := tsub_le_tsub_left hcompl 1
    _ ≤ iid_sample_law (n := n) f S := by
        rw [tsub_le_iff_right]
        exact hadd

@[blueprint "thm:hellinger-minimum-distance-estimator"
  (statement := /-- There exists an absolute constant $C>0$ with the following property. For every common measure space, every target density $f$ whose probability measure is atomless in the measure-theoretic sense of \cref{def:is-atomless-measure}, every nonempty density family $\mathcal F$, every $n\geq2$, every $0<\delta<1$, and every countable ratio class of VC dimension $d\geq1$, let $0\leq\varepsilon\leq1/n$. Every $\varepsilon$-approximate ratio-class minimum-distance estimator $\widehat f_n$ for which $x\mapsto H^2(f,\widehat f_n(x))$ is measurable satisfies, on a measurable event of probability at least $1-\delta$,
  \[
    H^2(f,\widehat f_n)
      \leq C\left[
        \inf_{g\in\mathcal F}
          H^2(f,g)\log_2\!\frac{2}{H^2(f,g)}
        +\frac{(d\log_2 n+\log_2(2/\delta))\log_2 n}{n}
      \right].
  \]
  No assumption requires $f\in\mathcal F$. The choice $\varepsilon=0$ recovers an exact estimator, while every positive tolerance at most $1/n$ permits a nonattained empirical infimum to be approximated without changing the stated rate. -/)
  (proof := /-- Take the absolute constant $C=400000$. The measurability hypothesis makes the displayed success set measurable. The assumed countability of the ratio class supplies the countability hypothesis of \cref{lem:infimum-oracle-bound}; for arbitrary admissible parameters, that lemma gives exactly this event with probability at least $1-\delta$, with the contribution of the optimization tolerance already absorbed into the VC term. The definitions of the best-approximation and VC terms identify its right-hand side with the two expressions displayed in the statement. -/)
  (title := /-- Hellinger risk of the ratio-class minimum-distance estimator -/)
  (latexEnv := "theorem")]
theorem hellinger_minimum_distance_estimator :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
        (n d : ℕ) (δ : ℝ) (f : hellinger_density Ω μ)
        (F : Set (hellinger_density Ω μ)),
        2 ≤ n → 1 ≤ d → 0 < δ → δ < 1 → F.Nonempty →
        ∀ (ε : ℝ), ε ≤ (n : ℝ)⁻¹ →
        ∀ (hat : (Fin n → Ω) → hellinger_density Ω μ),
          is_atomless_measure
            (f.toProbabilityMeasure : MeasureTheory.Measure Ω) →
          (ratio_concept_class F).Countable →
          has_vc_dimension (ratio_concept_class F) d →
          is_approximate_minimum_distance_estimator n
            (ratio_concept_class F) F ε hat →
          Measurable (fun x => squared_hellinger f (hat x)) →
          iid_sample_law (n := n) f
              {x | squared_hellinger f (hat x) ≤
                C * (best_approximation_penalty f F +
                  vc_complexity_term n d δ)} ≥
            ENNReal.ofReal (1 - δ) := by
  refine ⟨400000, by norm_num, ?_⟩
  intro Ω _ μ n d δ f F hn hd hδ0 hδ1 hF ε hεn hat hatom hcount hvc hhat hmeas
  exact infimum_oracle_bound hn hd hδ0 hδ1 f F hF hat hatom hcount hvc hεn hhat
    hmeas

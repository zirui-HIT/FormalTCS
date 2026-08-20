import Architect
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Compactness.Compact

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory

variable {IStep Step : Type*}
  [MeasurableSpace IStep]
  [Inhabited Step] [TopologicalSpace Step] [MeasurableSpace Step]
  [BorelSpace Step] [SecondCountableTopology Step] [CompactSpace Step]
  [TopologicalSpace.MetrizableSpace Step]

@[blueprint "def:input-prefix-eq"
  (statement := /-- For a horizon $T \in \mathbb{N}$, a time $t \in \mathbb{N}$, and two inputs
    $x, x' : \{0, \dots, T-1\} \to \mathcal{X}_{\mathrm{step}}$, we write $x_{\le t} = x'_{\le t}$
    to mean that $x_i = x'_i$ for every index $i$ with $i < t$. -/)
  (title := /-- Agreement of Input Prefixes -/)
  (latexEnv := "definition")]
def input_prefix_eq (T t : ℕ) (x x' : Fin T → IStep) : Prop :=
  ∀ i : Fin T, (i : ℕ) < t → x i = x' i

@[blueprint "def:action-prefix"
  (statement := /-- For a horizon $T$ and a time $t$, the projection onto the first $t$ actions
    sends an action sequence $y : \{0, \dots, T-1\} \to \mathcal{Y}_{\mathrm{step}}$ to the sequence
    that agrees with $y$ on every index $i < t$ and equals a fixed base point on every index
    $i \ge t$. -/)
  (title := /-- Projection onto the First $t$ Actions -/)
  (latexEnv := "definition")]
def action_prefix (T t : ℕ) (y : Fin T → Step) : Fin T → Step :=
  fun i => if (i : ℕ) < t then y i else default

@[blueprint "def:is-online-algorithm"
  (statement := /-- Fix a horizon $T$ and, for each input $x$, a set $\mathcal{Y}(x)$ of feasible
    action sequences. A family $\nu = (\nu_x)_x$ of Borel probability measures on
    $\mathcal{Y}_{\mathrm{step}}^{T}$, indexed by inputs $x$, is a randomized online algorithm if it
    is feasible and causal: (i) for every input $x$ the measure $\nu_x$ assigns mass $1$ to
    $\mathcal{Y}(x)$; and (ii) for all $t \in \mathbb{N}$ and all inputs $x, x'$ with
    $x_{\le t} = x'_{\le t}$, the pushforwards of $\nu_x$ and $\nu_{x'}$ under the projection onto
    the first $t$ actions coincide. -/)
  (title := /-- Randomized Online Algorithm -/)
  (latexEnv := "definition")]
def is_online_algorithm (T : ℕ) (feasible : (Fin T → IStep) → Set (Fin T → Step))
    (ν : (Fin T → IStep) → ProbabilityMeasure (Fin T → Step)) : Prop :=
  (∀ x, (ν x : Measure (Fin T → Step)) (feasible x) = 1) ∧
    (∀ (t : ℕ) (x x' : Fin T → IStep), input_prefix_eq T t x x' →
      Measure.map (action_prefix T t) (ν x : Measure (Fin T → Step)) =
        Measure.map (action_prefix T t) (ν x' : Measure (Fin T → Step)))

@[blueprint "def:expected-cost"
  (statement := /-- Given a Borel probability measure $\mu$ on a measurable space $\alpha$ and a
    real-valued cost function $c : \alpha \to \mathbb{R}$, the expected cost
    $\mathbb{E}_{Y \sim \mu}[c(Y)]$ is the Bochner integral $\int_{\alpha} c \, d\mu$. -/)
  (title := /-- Expected Cost -/)
  (latexEnv := "definition")]
noncomputable def expected_cost {α : Type*} [MeasurableSpace α] (μ : ProbabilityMeasure α)
    (c : α → ℝ) : ℝ :=
  ∫ a, c a ∂(μ : Measure α)

@[blueprint "def:is-finitely-supported"
  (statement := /-- A Borel probability measure $\mathcal{D}$ on a measurable space $\iota$ is
    finitely supported if there exists a finite set $s \subseteq \iota$ whose complement is
    $\mathcal{D}$-null. -/)
  (title := /-- Finitely Supported Distribution -/)
  (latexEnv := "definition")]
def is_finitely_supported {ι : Type*} [MeasurableSpace ι] (D : ProbabilityMeasure ι) : Prop :=
  ∃ s : Finset ι, (D : Measure ι) ((↑s : Set ι)ᶜ) = 0

@[blueprint "def:online-algorithm-set"
  (statement := /-- Fix a horizon $T$ and feasible-action sets $\mathcal{Y}(\cdot)$. The space
    $\mathfrak{A}$ of causal randomized online algorithms is the set of all families
    $\nu : x \mapsto \nu_x$ of Borel probability measures on $\mathcal{Y}_{\mathrm{step}}^{T}$ that
    are randomized online algorithms in the sense of \cref{def:is-online-algorithm}, regarded inside
    the product space $\prod_{x} \mathcal{P}(\mathcal{Y}_{\mathrm{step}}^{T})$ with the product of
    the topologies of weak convergence. -/)
  (title := /-- The Space of Online Algorithms -/)
  (latexEnv := "definition")]
def online_algorithm_set (T : ℕ) (feasible : (Fin T → IStep) → Set (Fin T → Step)) :
    Set ((Fin T → IStep) → ProbabilityMeasure (Fin T → Step)) :=
  {ν | is_online_algorithm T feasible ν}

@[blueprint "lem:action-prefix-continuous"
  (statement := /-- Fix a horizon $T$ and a time $t$. The projection onto the first $t$ actions of
    \cref{def:action-prefix}, viewed as a map $\mathcal{Y}_{\mathrm{step}}^{T} \to
    \mathcal{Y}_{\mathrm{step}}^{T}$, is continuous. -/)
  (proof := /-- By \cref{def:action-prefix} the projection acts coordinatewise: its value at index
    $i$ equals the evaluation $y \mapsto y_i$ when $i < t$ and the constant base point otherwise.
    Each coordinate map is continuous, being either a coordinate projection or a constant map, so
    the projection is continuous by the universal property of the product topology. -/)
  (title := /-- Continuity of the Projection onto the First $t$ Actions -/)
  (latexEnv := "lemma")]
lemma action_prefix_continuous (T t : ℕ) :
    Continuous (action_prefix (Step := Step) T t) := by
  apply continuous_pi
  intro i
  simp only [action_prefix]
  split_ifs with h
  · exact continuous_apply i
  · exact continuous_const

@[blueprint "lem:prob-measure-closed-eq-one-isClosed"
  (statement := /-- Let $\Omega$ be a topological space carrying its Borel $\sigma$-algebra on
    which closed sets admit outer approximation by continuous functions, and let $F \subseteq \Omega$
    be closed. Then the set of Borel probability measures $\mu$ on $\Omega$ with $\mu(F) = 1$ is
    closed for the topology of weak convergence. -/)
  (proof := /-- By the portmanteau theorem, for every probability measure $\mu$ the limit superior
    of $\nu \mapsto \nu(F)$ as $\nu \to \mu$ is at most $\mu(F)$; hence $\mu \mapsto \mu(F)$ is upper
    semicontinuous. Since every probability measure satisfies $\mu(F) \le 1$, the set
    $\{\mu : \mu(F) = 1\}$ coincides with the preimage $\{\mu : 1 \le \mu(F)\}$ of the closed ray
    $[1, \infty)$ under this upper semicontinuous map, and is therefore closed. -/)
  (title := /-- Closedness of the Full-Mass Constraint on a Closed Set -/)
  (latexEnv := "lemma")]
lemma prob_measure_closed_eq_one_isClosed {Ω : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {F : Set Ω} (hF : IsClosed F) :
    IsClosed {μ : ProbabilityMeasure Ω | (μ : Measure Ω) F = 1} := by
  have usc : UpperSemicontinuous (fun μ : ProbabilityMeasure Ω => (μ : Measure Ω) F) := by
    rw [upperSemicontinuous_iff_limsup_le]
    intro μ
    exact ProbabilityMeasure.limsup_measure_closed_le_of_tendsto Filter.tendsto_id hF
  have hset : {μ : ProbabilityMeasure Ω | (μ : Measure Ω) F = 1}
      = (fun μ : ProbabilityMeasure Ω => (μ : Measure Ω) F) ⁻¹' Set.Ici 1 := by
    ext μ
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ici]
    constructor
    · intro h; rw [h]
    · intro h; exact le_antisymm prob_le_one h
  rw [hset]
  exact usc.isClosed_preimage 1

@[blueprint "lem:online-feasibility-closed"
  (statement := /-- Fix a horizon $T$ and, for every input $x$, a closed set $\mathcal{Y}(x)$ of
    feasible action sequences. Then the set of families $\nu$ of Borel probability measures on
    $\mathcal{Y}_{\mathrm{step}}^{T}$, indexed by inputs, that satisfy the feasibility constraint
    $\nu_x(\mathcal{Y}(x)) = 1$ for every input $x$ is closed for the product of the topologies of
    weak convergence. -/)
  (proof := /-- The set is the intersection over all inputs $x$ of the sets
    $\{\nu : \nu_x(\mathcal{Y}(x)) = 1\}$. Each such set is the preimage of
    $\{\mu : \mu(\mathcal{Y}(x)) = 1\}$ under the continuous coordinate evaluation
    $\nu \mapsto \nu_x$, and that target set is closed by
    \cref{lem:prob-measure-closed-eq-one-isClosed} because $\mathcal{Y}(x)$ is closed. An
    intersection of closed sets is closed. -/)
  (title := /-- Closedness of the Feasibility Constraint -/)
  (latexEnv := "lemma")]
lemma online_feasibility_closed (T : ℕ) (feasible : (Fin T → IStep) → Set (Fin T → Step))
    (hfeasible : ∀ x, IsClosed (feasible x)) :
    IsClosed {ν : (Fin T → IStep) → ProbabilityMeasure (Fin T → Step) |
      ∀ x, (ν x : Measure (Fin T → Step)) (feasible x) = 1} := by
  rw [Set.setOf_forall]
  refine isClosed_iInter (fun x => ?_)
  have hpre : {ν : (Fin T → IStep) → ProbabilityMeasure (Fin T → Step) |
      (ν x : Measure (Fin T → Step)) (feasible x) = 1}
      = (fun ν => ν x) ⁻¹'
          {μ : ProbabilityMeasure (Fin T → Step) | (μ : Measure (Fin T → Step)) (feasible x) = 1} :=
    by ext ν; simp only [Set.mem_setOf_eq, Set.mem_preimage]
  rw [hpre]
  exact (prob_measure_closed_eq_one_isClosed (hfeasible x)).preimage (continuous_apply x)

@[blueprint "lem:online-causality-closed"
  (statement := /-- Fix a horizon $T$. The set of families $\nu$ of Borel probability measures on
    $\mathcal{Y}_{\mathrm{step}}^{T}$, indexed by inputs, that satisfy the causality constraint —
    for all times $t$ and inputs $x, x'$ with $x_{\le t} = x'_{\le t}$ the pushforwards of $\nu_x$
    and $\nu_{x'}$ under the projection onto the first $t$ actions coincide — is closed for the
    product of the topologies of weak convergence. -/)
  (proof := /-- The set is the intersection, over all times $t$ and all inputs $x, x'$ with
    $x_{\le t} = x'_{\le t}$, of the sets on which the two pushforwards agree. For fixed data the
    map $\nu \mapsto (\pi_t)_{\#}\nu_x$ is continuous, being the composition of the continuous
    coordinate evaluation $\nu \mapsto \nu_x$ with the continuous pushforward map associated to the
    continuous projection of \cref{lem:action-prefix-continuous}. Hence each set is closed as the
    equalizer of two continuous maps, and an intersection of closed sets is closed. -/)
  (title := /-- Closedness of the Causality Constraint -/)
  (latexEnv := "lemma")]
lemma online_causality_closed (T : ℕ) :
    IsClosed {ν : (Fin T → IStep) → ProbabilityMeasure (Fin T → Step) |
      ∀ (t : ℕ) (x x' : Fin T → IStep), input_prefix_eq T t x x' →
        Measure.map (action_prefix T t) (ν x : Measure (Fin T → Step)) =
          Measure.map (action_prefix T t) (ν x' : Measure (Fin T → Step))} := by
  rw [Set.setOf_forall]
  refine isClosed_iInter (fun t => ?_)
  rw [Set.setOf_forall]
  refine isClosed_iInter (fun x => ?_)
  rw [Set.setOf_forall]
  refine isClosed_iInter (fun x' => ?_)
  rw [Set.setOf_forall]
  refine isClosed_iInter (fun _ => ?_)
  have hcont : Continuous (action_prefix (Step := Step) T t) := action_prefix_continuous T t
  have key : {ν : (Fin T → IStep) → ProbabilityMeasure (Fin T → Step) |
      Measure.map (action_prefix T t) (ν x : Measure (Fin T → Step)) =
        Measure.map (action_prefix T t) (ν x' : Measure (Fin T → Step))}
      = {ν | (fun ν => (ν x).map hcont.measurable.aemeasurable) ν
          = (fun ν => (ν x').map hcont.measurable.aemeasurable) ν} := by
    ext ν
    simp only [Set.mem_setOf_eq]
    rw [← ProbabilityMeasure.toMeasure_injective.eq_iff,
      ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map]
  rw [key]
  exact isClosed_eq ((ProbabilityMeasure.continuous_map hcont).comp (continuous_apply x))
    ((ProbabilityMeasure.continuous_map hcont).comp (continuous_apply x'))

@[blueprint "lem:algorithm-set-compact"
  (statement := /-- Fix a horizon $T$ and, for every input $x$, a compact set $\mathcal{Y}(x)$ of
    feasible action sequences in the compact metric space $\mathcal{Y}_{\mathrm{step}}^{T}$. Then
    the space $\mathfrak{A}$ of causal randomized online algorithms of
    \cref{def:online-algorithm-set} is compact for the product of the topologies of weak
    convergence. -/)
  (proof := /-- The ambient space $\prod_{x} \mathcal{P}(\mathcal{Y}_{\mathrm{step}}^{T})$ is
    compact: since $\mathcal{Y}_{\mathrm{step}}^{T}$ is a compact metric space, each factor
    $\mathcal{P}(\mathcal{Y}_{\mathrm{step}}^{T})$ is compact by Prokhorov's theorem, and the product
    over all inputs is compact by Tychonoff's theorem. Inside this space, $\mathfrak{A}$ is the
    intersection of the feasibility constraints $\{\nu : \nu_x(\mathcal{Y}(x)) = 1\}$, which are
    closed by \cref{lem:online-feasibility-closed} because each $\mathcal{Y}(x)$ is
    compact and hence closed, together with the causality
    constraints $\{\nu : (\pi_t)_{\#}\nu_x = (\pi_t)_{\#}\nu_{x'}\}$ ranging over all $t$ and all
    inputs $x, x'$ with $x_{\le t} = x'_{\le t}$, which are closed because the projection pushforward
    maps are continuous for the topologies of weak convergence, by
    \cref{lem:online-causality-closed}. Therefore $\mathfrak{A}$ is a closed
    subset of a compact space, and is compact. -/)
  (title := /-- Compactness of the Space of Online Algorithms -/)
  (latexEnv := "lemma")]
lemma algorithm_set_compact (T : ℕ) (feasible : (Fin T → IStep) → Set (Fin T → Step))
    (hfeasible : ∀ x, IsCompact (feasible x)) :
    IsCompact (online_algorithm_set T feasible) := by
  have hclosed : IsClosed (online_algorithm_set T feasible) := by
    have hset : online_algorithm_set T feasible =
        {ν | ∀ x, (ν x : Measure (Fin T → Step)) (feasible x) = 1} ∩
          {ν | ∀ (t : ℕ) (x x' : Fin T → IStep), input_prefix_eq T t x x' →
              Measure.map (action_prefix T t) (ν x : Measure (Fin T → Step)) =
                Measure.map (action_prefix T t) (ν x' : Measure (Fin T → Step))} := by
      ext ν
      simp only [online_algorithm_set, is_online_algorithm, Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [hset]
    exact (online_feasibility_closed T feasible (fun x => (hfeasible x).isClosed)).inter
      (online_causality_closed T)
  haveI hStepPi : CompactSpace (Fin T → Step) := Pi.compactSpace
  haveI hProb : CompactSpace (ProbabilityMeasure (Fin T → Step)) := inferInstance
  haveI hcompact : CompactSpace ((Fin T → IStep) → ProbabilityMeasure (Fin T → Step)) :=
    Pi.compactSpace
  exact hclosed.isCompact

@[blueprint "lem:online-algorithm-mixture"
  (statement := /-- Fix a horizon $T$ and feasible-action sets $\mathcal{Y}(\cdot)$. Let
    $\nu^{(1)}$ and $\nu^{(2)}$ be randomized online algorithms in the sense of
    \cref{def:is-online-algorithm}, and let $a, b \ge 0$ satisfy $a + b = 1$. If a family
    $\nu^{\mathrm{m}}$ of Borel probability measures on $\mathcal{Y}_{\mathrm{step}}^{T}$ satisfies
    $\nu^{\mathrm{m}}_x = a\,\nu^{(1)}_x + b\,\nu^{(2)}_x$ for every input $x$, then
    $\nu^{\mathrm{m}}$ is a randomized online algorithm. -/)
  (proof := /-- We verify the two defining conditions of \cref{def:is-online-algorithm}. For
    feasibility, fix an input $x$. Since $\nu^{\mathrm{m}}_x = a\,\nu^{(1)}_x + b\,\nu^{(2)}_x$ and
    both $\nu^{(1)}_x$ and $\nu^{(2)}_x$ assign mass $1$ to $\mathcal{Y}(x)$, we obtain
    $\nu^{\mathrm{m}}_x(\mathcal{Y}(x)) = a \cdot 1 + b \cdot 1 = a + b = 1$. For causality, fix a
    time $t$ and inputs $x, x'$ with $x_{\le t} = x'_{\le t}$. The projection onto the first $t$
    actions is measurable by \cref{lem:action-prefix-continuous}, and pushforward under a measurable
    map is additive and commutes with scalar multiplication, so
    $(\pi_t)_\#\nu^{\mathrm{m}}_x = a\,(\pi_t)_\#\nu^{(1)}_x + b\,(\pi_t)_\#\nu^{(2)}_x$ and likewise
    for $x'$. Because $\nu^{(1)}$ and $\nu^{(2)}$ are causal,
    $(\pi_t)_\#\nu^{(1)}_x = (\pi_t)_\#\nu^{(1)}_{x'}$ and
    $(\pi_t)_\#\nu^{(2)}_x = (\pi_t)_\#\nu^{(2)}_{x'}$, whence the two pushforwards of
    $\nu^{\mathrm{m}}$ agree. -/)
  (title := /-- Mixtures of Online Algorithms are Online Algorithms -/)
  (latexEnv := "lemma")]
lemma online_algorithm_mixture (T : ℕ) (feasible : (Fin T → IStep) → Set (Fin T → Step))
    (ν₁ ν₂ : (Fin T → IStep) → ProbabilityMeasure (Fin T → Step))
    (h₁ : is_online_algorithm T feasible ν₁) (h₂ : is_online_algorithm T feasible ν₂)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (νm : (Fin T → IStep) → ProbabilityMeasure (Fin T → Step))
    (hmix : ∀ x, (νm x : Measure (Fin T → Step))
      = ENNReal.ofReal a • (ν₁ x : Measure (Fin T → Step))
        + ENNReal.ofReal b • (ν₂ x : Measure (Fin T → Step))) :
    is_online_algorithm T feasible νm := by
  constructor
  · intro x
    rw [hmix x]
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, h₁.1 x, h₂.1 x, mul_one]
    rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one]
  · intro t x x' hpre
    have hmeas : Measurable (action_prefix (Step := Step) T t) :=
      (action_prefix_continuous T t).measurable
    rw [hmix x, hmix x', Measure.map_add _ _ hmeas, Measure.map_add _ _ hmeas,
      Measure.map_smul, Measure.map_smul, Measure.map_smul, Measure.map_smul,
      h₁.2 t x x' hpre, h₂.2 t x x' hpre]

@[blueprint "lem:expected-cost-continuous"
  (statement := /-- Fix a horizon $T$ and a continuous cost function
    $c : \mathcal{Y}_{\mathrm{step}}^{T} \to \mathbb{R}$ on the compact metric space
    $\mathcal{Y}_{\mathrm{step}}^{T}$. Then the expected-cost functional
    $\mu \mapsto \mathbb{E}_{Y \sim \mu}[c(Y)]$ of \cref{def:expected-cost} is continuous on the space
    of Borel probability measures on $\mathcal{Y}_{\mathrm{step}}^{T}$ endowed with the topology of
    weak convergence. -/)
  (proof := /-- Since $\mathcal{Y}_{\mathrm{step}}^{T}$ is compact, the continuous function $c$ is
    bounded, so it defines a bounded continuous function whose associated integral functional
    $\mu \mapsto \int c \, d\mu$ is continuous for the topology of weak convergence. By
    \cref{def:expected-cost} the expected-cost functional equals this integral functional, hence it
    is continuous. -/)
  (title := /-- Continuity of the Expected-Cost Functional -/)
  (latexEnv := "lemma")]
lemma expected_cost_continuous (c : (Fin T → Step) → ℝ) (hc : Continuous c) :
    Continuous (fun μ : ProbabilityMeasure (Fin T → Step) => expected_cost μ c) := by
  have h := MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (BoundedContinuousFunction.mkOfCompact ⟨c, hc⟩)
  simpa [expected_cost] using h

@[blueprint "lem:expected-cost-mixture"
  (statement := /-- Fix a horizon $T$ and a continuous cost function
    $c : \mathcal{Y}_{\mathrm{step}}^{T} \to \mathbb{R}$. Let $\mu_1, \mu_2$ be Borel probability
    measures on $\mathcal{Y}_{\mathrm{step}}^{T}$, let $a, b \ge 0$, and let $\mu_{\mathrm{m}}$ be a
    Borel probability measure with $\mu_{\mathrm{m}} = a\,\mu_1 + b\,\mu_2$. Then the expected cost
    of \cref{def:expected-cost} is affine in the mixture:
    $\mathbb{E}_{Y \sim \mu_{\mathrm{m}}}[c(Y)] = a\,\mathbb{E}_{Y \sim \mu_1}[c(Y)]
      + b\,\mathbb{E}_{Y \sim \mu_2}[c(Y)]$. -/)
  (proof := /-- Because $\mathcal{Y}_{\mathrm{step}}^{T}$ is compact and $c$ is continuous, $c$ is
    bounded, hence integrable with respect to every finite measure, in particular with respect to
    $\mu_1$ and $\mu_2$. Using $\mu_{\mathrm{m}} = a\,\mu_1 + b\,\mu_2$ and the additivity of the
    Bochner integral over a sum of measures together with its homogeneity under scaling of the
    measure, we compute $\int c \, d\mu_{\mathrm{m}} = a \int c \, d\mu_1 + b \int c \, d\mu_2$.
    By \cref{def:expected-cost} this is the claimed identity for the expected cost. -/)
  (title := /-- Affinity of Expected Cost in Mixtures -/)
  (latexEnv := "lemma")]
lemma expected_cost_mixture (c : (Fin T → Step) → ℝ) (hc : Continuous c)
    (μ₁ μ₂ : ProbabilityMeasure (Fin T → Step)) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (μm : ProbabilityMeasure (Fin T → Step))
    (hm : (μm : Measure (Fin T → Step))
      = ENNReal.ofReal a • (μ₁ : Measure (Fin T → Step))
        + ENNReal.ofReal b • (μ₂ : Measure (Fin T → Step))) :
    expected_cost μm c = a * expected_cost μ₁ c + b * expected_cost μ₂ c := by
  have hbdd : Integrable c (μ₁ : Measure (Fin T → Step)) :=
    (BoundedContinuousFunction.mkOfCompact ⟨c, hc⟩).integrable _
  have hbdd₂ : Integrable c (μ₂ : Measure (Fin T → Step)) :=
    (BoundedContinuousFunction.mkOfCompact ⟨c, hc⟩).integrable _
  simp only [expected_cost, hm]
  rw [integral_add_measure (hbdd.smul_measure (by simp)) (hbdd₂.smul_measure (by simp)),
    integral_smul_measure, integral_smul_measure, smul_eq_mul, smul_eq_mul,
    ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]

@[blueprint "lem:online-minimax-finite"
  (statement := /-- Fix a horizon $T \in \mathbb{N}$ and constants $\alpha, \beta$. Let
    $\mathcal{Y}(\cdot)$ assign to each input a compact set of feasible action sequences, let
    $\cost(x, \cdot)$ be continuous for every input $x$, and let $\OPT$ denote the offline optimum.
    Assume that singletons of the input space are measurable. Suppose that for every finitely
    supported Borel probability distribution $\mathcal{D}$ over inputs there exists a randomized
    online algorithm $\nu^{\mathcal{D}}$ with
    $\mathbb{E}_{X \sim \mathcal{D}} \mathbb{E}_{Y \sim \nu^{\mathcal{D}}_X}[\cost(X, Y)]
      \le \alpha\, \mathbb{E}_{X \sim \mathcal{D}}[\OPT(X)] + \beta$. Then for every finite set $S$
    of inputs there exists a randomized online algorithm $\nu$ such that
    $\mathbb{E}_{Y \sim \nu_x}[\cost(x, Y)] \le \alpha\, \OPT(x) + \beta$ for every $x \in S$. -/)
  (proof := /-- Argue by contradiction and assume no algorithm meets the bound on all of $S$. Let
    $\mathfrak{A}$ be the compact space of causal randomized online algorithms of
    \cref{lem:algorithm-set-compact}, and consider the affine evaluation map
    $\Phi(\nu) = (x \mapsto \mathbb{E}_{Y \sim \nu_x}[\cost(x, Y)] - \alpha\, \OPT(x))_{x \in S}$
    into $\mathbb{R}^{S}$. Its image $K = \Phi(\mathfrak{A})$ is compact, since $\Phi$ is continuous
    by \cref{lem:expected-cost-continuous}, and convex, since mixtures of algorithms are algorithms
    by \cref{lem:online-algorithm-mixture} and expected cost is affine in mixtures by
    \cref{lem:expected-cost-mixture}. The contradiction hypothesis says $K$ is disjoint from the
    closed convex box $Q = \{w : \forall x,\ w_x \le \beta\}$. By the geometric Hahn–Banach theorem
    there is a continuous linear functional $f(w) = \sum_x w_x\, d_x$ and reals $u < v$ with $f < u$
    on $K$ and $f > v$ on $Q$. Testing $f$ on rays of $Q$ that decrease a single coordinate forces
    $d_x \le 0$ for all $x$, and $f$ is nonzero because it separates a point of the nonempty $K$
    from $Q$, so $d \ne 0$. Writing $M = -\sum_x d_x > 0$ and $p_x = -d_x / M$ defines a probability
    vector; the associated finitely supported prior $\mathcal{D} = \sum_{x \in S} p_x\, \delta_x$
    satisfies, for any integrand, $\int g \, d\mathcal{D} = \sum_x p_x\, g(x)$ by
    \cref{def:expected-cost} and the Dirac evaluation. Applying the hypothesis to $\mathcal{D}$
    yields an algorithm $\nu'$ with $\sum_x p_x(\mathbb{E}_{\nu'_x}[\cost] - \alpha \OPT(x)) \le
    \beta$. But $\nu' \in \mathfrak{A}$ so $\Phi(\nu') \in K$, and evaluating the separating
    inequality $f(\Phi(\nu')) < v < f(\beta\mathbf{1})$ with $d_x = -M p_x$ gives
    $\sum_x p_x(\mathbb{E}_{\nu'_x}[\cost] - \alpha \OPT(x)) > \beta$, a contradiction. -/)
  (title := /-- Worst-Case Guarantee on Every Finite Set of Inputs -/)
  (latexEnv := "lemma")]
lemma online_minimax_finite [MeasurableSingletonClass IStep] (T : ℕ) (α β : ℝ)
    (feasible : (Fin T → IStep) → Set (Fin T → Step))
    (cost : (Fin T → IStep) → (Fin T → Step) → ℝ) (opt : (Fin T → IStep) → ℝ)
    (hcost : ∀ x, Continuous (cost x)) (hfeasible : ∀ x, IsCompact (feasible x))
    (hbayes : ∀ D : ProbabilityMeasure (Fin T → IStep), is_finitely_supported D →
      ∃ ν, is_online_algorithm T feasible ν ∧
        (∫ x, expected_cost (ν x) (cost x) ∂(D : Measure (Fin T → IStep)))
          ≤ α * (∫ x, opt x ∂(D : Measure (Fin T → IStep))) + β)
    (S : Finset (Fin T → IStep)) :
    ∃ ν, is_online_algorithm T feasible ν ∧
      ∀ x ∈ S, expected_cost (ν x) (cost x) ≤ α * opt x + β := by
  classical
  rcases isEmpty_or_nonempty (Fin T → IStep) with hEmpty | hNe
  · haveI := hEmpty
    exact ⟨fun x => isEmptyElim x,
      ⟨fun x => isEmptyElim x, fun _ x _ _ => isEmptyElim x⟩, fun x _ => isEmptyElim x⟩
  obtain ⟨x₀⟩ := hNe
  by_contra hcon
  simp only [not_exists, not_and, not_forall, not_le, exists_prop] at hcon
  set A := online_algorithm_set T feasible with hA
  set Φ : ((Fin T → IStep) → ProbabilityMeasure (Fin T → Step)) → (↥S → ℝ) :=
    fun ν x => expected_cost (ν ↑x) (cost ↑x) - α * opt ↑x with hΦ
  have hΦcont : Continuous Φ := by
    apply continuous_pi
    intro x
    exact ((expected_cost_continuous (cost ↑x) (hcost ↑x)).comp
      (continuous_apply (↑x : Fin T → IStep))).sub continuous_const
  set K : Set (↥S → ℝ) := Φ '' A with hK
  have hKcomp : IsCompact K := (algorithm_set_compact T feasible hfeasible).image hΦcont
  have hKconv : Convex ℝ K := by
    rintro _ ⟨ν₁, hν₁, rfl⟩ _ ⟨ν₂, hν₂, rfl⟩ a b ha hb hab
    refine ⟨fun z => ⟨ENNReal.ofReal a • (ν₁ z : Measure (Fin T → Step))
        + ENNReal.ofReal b • (ν₂ z : Measure (Fin T → Step)), ?_⟩, ?_, ?_⟩
    · constructor
      simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one]
    · exact online_algorithm_mixture T feasible ν₁ ν₂ hν₁ hν₂ a b ha hb hab _ (fun z => rfl)
    · funext x'
      have hmc := expected_cost_mixture (cost ↑x') (hcost ↑x') (ν₁ ↑x') (ν₂ ↑x') a b ha hb
        ⟨ENNReal.ofReal a • (ν₁ ↑x' : Measure (Fin T → Step))
          + ENNReal.ofReal b • (ν₂ ↑x' : Measure (Fin T → Step)), by
            constructor
            simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
            rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one]⟩ rfl
      simp only [hΦ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hmc]
      linear_combination (α * opt (x' : Fin T → IStep)) * hab
  set Q : Set (↥S → ℝ) := {w | ∀ x, w x ≤ β} with hQ
  have hQconv : Convex ℝ Q := by
    intro w hw w' hw' a b ha hb hab x
    simp only [hQ, Set.mem_setOf_eq] at hw hw'
    have : a * w x + b * w' x ≤ a * β + b * β :=
      add_le_add (mul_le_mul_of_nonneg_left (hw x) ha) (mul_le_mul_of_nonneg_left (hw' x) hb)
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← add_mul, hab] using this
  have hQclosed : IsClosed Q := by
    have : Q = ⋂ x : ↥S, {w : ↥S → ℝ | w x ≤ β} := by
      ext w; simp [Q, Set.mem_iInter]
    rw [this]
    exact isClosed_iInter (fun x => isClosed_le (continuous_apply x) continuous_const)
  have hq0 : (fun _ : ↥S => β) ∈ Q := fun x => le_refl β
  have hdisj : Disjoint K Q := by
    rw [Set.disjoint_left]
    rintro _ ⟨ν, hνA, rfl⟩ hΦQ
    simp only [hQ, Set.mem_setOf_eq, hΦ] at hΦQ
    obtain ⟨x, hx, hlt⟩ := hcon ν hνA
    have hbx := hΦQ ⟨x, hx⟩
    simp only at hbx
    linarith [hbx, hlt]
  obtain ⟨f, u, v, hfK, huv, hfQ⟩ :=
    geometric_hahn_banach_compact_closed hKconv hKcomp hQconv hQclosed hdisj
  set d : ↥S → ℝ := fun x => f (Pi.single x 1) with hd
  have frepr : ∀ w : ↥S → ℝ, f w = ∑ x : ↥S, w x * d x := by
    intro w
    conv_lhs => rw [show w = ∑ x : ↥S, w x • Pi.single x (1 : ℝ) by
      ext j; simp [Finset.sum_apply, Pi.single_apply]]
    rw [map_sum]
    simp [map_smul, smul_eq_mul, mul_comm, hd]
  set c₀ : ℝ := ∑ x : ↥S, β * d x with hc₀
  have hfq0 : f (fun _ : ↥S => β) = c₀ := by rw [frepr]
  have hd_le : ∀ x₀, d x₀ ≤ 0 := by
    intro x₀
    have hval : ∀ s : ℝ, f (fun z => if z = x₀ then β - s else β) = c₀ - s * d x₀ := by
      intro s
      rw [frepr, hc₀]
      rw [show (∑ x : ↥S, (if x = x₀ then β - s else β) * d x)
          = ∑ x : ↥S, (β * d x - (if x = x₀ then s * d x₀ else 0)) from
        Finset.sum_congr rfl (fun x _ => by
          split_ifs with h
          · subst h; ring
          · ring)]
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']
      simp
    by_contra hpos
    rw [not_le] at hpos
    have hc0v : 0 < c₀ - v := by
      have := hfQ (fun _ : ↥S => β) hq0
      rw [hfq0] at this
      linarith
    set s := (c₀ - v + 1) / d x₀ with hs
    have hsnn : (fun z => if z = x₀ then β - s else β) ∈ Q := by
      intro z; simp only [Set.mem_setOf_eq]; split_ifs with h
      · have : 0 ≤ s := div_nonneg (by linarith) (le_of_lt hpos)
        linarith
      · exact le_refl β
    have h1 := hfQ _ hsnn
    rw [hval] at h1
    have : s * d x₀ = c₀ - v + 1 := by
      rw [hs]; field_simp
    linarith [h1, this]
  set Dw : ↥S → ℝ := fun x => - d x with hDw
  have hDwnn : ∀ x, 0 ≤ Dw x := fun x => by rw [hDw]; simpa using hd_le x
  obtain ⟨ν₀, hν₀, -⟩ := hbayes ⟨Measure.dirac x₀, inferInstance⟩ ⟨{x₀}, by simp⟩
  have hk₀K : Φ ν₀ ∈ K := Set.mem_image_of_mem Φ hν₀
  have hfne : ∃ x, d x ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have heq : f (Φ ν₀) = f (fun _ : ↥S => β) := by rw [frepr, frepr]; simp [h]
    have := hfK (Φ ν₀) hk₀K
    have := hfQ (fun _ : ↥S => β) hq0
    linarith
  have hDwpos : ∃ x, 0 < Dw x := by
    obtain ⟨x, hx⟩ := hfne
    exact ⟨x, lt_of_le_of_ne (hDwnn x) (by rw [hDw]; simpa [eq_comm] using hx)⟩
  set M : ℝ := ∑ x : ↥S, Dw x with hM
  have hMpos : 0 < M := by
    obtain ⟨x, hx⟩ := hDwpos
    exact Finset.sum_pos' (fun i _ => hDwnn i) ⟨x, Finset.mem_univ x, hx⟩
  set p : ↥S → ℝ := fun x => Dw x / M with hp
  have hp_nn : ∀ x, 0 ≤ p x := fun x => div_nonneg (hDwnn x) (le_of_lt hMpos)
  have hp_sum : ∑ x : ↥S, p x = 1 := by
    rw [hp]
    simp only [← Finset.sum_div]
    rw [div_self (ne_of_gt hMpos)]
  have hdp : ∀ x, d x = -(M * p x) := by
    intro x
    have hMp : M * p x = Dw x := by rw [hp]; field_simp
    rw [hMp, hDw]; ring
  set 𝒟 : Measure (Fin T → IStep) :=
    ∑ x : ↥S, ENNReal.ofReal (p x) • Measure.dirac (↑x : Fin T → IStep) with h𝒟
  have hmass : ∑ x : ↥S, ENNReal.ofReal (p x) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hp_nn x), hp_sum, ENNReal.ofReal_one]
  have hprob : IsProbabilityMeasure 𝒟 := by
    constructor
    rw [h𝒟, Measure.finset_sum_apply]
    simp only [Measure.smul_apply, Measure.dirac_apply, Set.mem_univ, Set.indicator_of_mem,
      Pi.one_apply, smul_eq_mul, mul_one]
    exact hmass
  set D_pm : ProbabilityMeasure (Fin T → IStep) := ⟨𝒟, hprob⟩ with hD_pm
  have hcoe : (D_pm : Measure (Fin T → IStep)) = 𝒟 := rfl
  have hfs : is_finitely_supported D_pm := by
    refine ⟨S, ?_⟩
    rw [hcoe, h𝒟, Measure.finset_sum_apply]
    apply Finset.sum_eq_zero
    intro x _
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [Measure.dirac_apply' _ (S.measurableSet.compl)]
    simp [x.2]
  have hInt : ∀ g : (Fin T → IStep) → ℝ, (∫ y, g y ∂𝒟) = ∑ x : ↥S, p x * g ↑x := by
    intro g
    rw [h𝒟, integral_finsetSum_measure]
    · refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [integral_smul_measure, integral_dirac, smul_eq_mul, ENNReal.toReal_ofReal (hp_nn x)]
    · intro i _
      exact (integrable_dirac (f := g) (a := (↑i : Fin T → IStep))
        (by simp [enorm_lt_top])).smul_measure (by simp [ENNReal.ofReal_ne_top])
  obtain ⟨ν', hν', hle'⟩ := hbayes D_pm hfs
  rw [hcoe, hInt, hInt] at hle'
  have hν'K : Φ ν' ∈ K := Set.mem_image_of_mem Φ hν'
  have hsep : f (Φ ν') < f (fun _ : ↥S => β) := by
    have h1 := hfK (Φ ν') hν'K
    have h2 := hfQ (fun _ : ↥S => β) hq0
    linarith
  set EO : ℝ := ∑ x : ↥S, p x * (expected_cost (ν' ↑x) (cost ↑x) - α * opt ↑x) with hEO
  have hfphi : f (Φ ν') = -M * EO := by
    rw [frepr, hEO, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [hdp x]
    show (expected_cost (ν' ↑x) (cost ↑x) - α * opt ↑x) * (-(M * p x))
      = -M * (p x * (expected_cost (ν' ↑x) (cost ↑x) - α * opt ↑x))
    ring
  have hfq0' : f (fun _ : ↥S => β) = -M * β := by
    rw [hfq0, hc₀]
    rw [show (∑ x : ↥S, β * d x) = ∑ x : ↥S, -M * (β * p x) from
      Finset.sum_congr rfl (fun x _ => by rw [hdp x]; ring)]
    rw [← Finset.mul_sum, ← Finset.mul_sum, hp_sum, mul_one]
  have hbetaEO : β < EO := by
    rw [hfphi, hfq0'] at hsep
    have hMEO : M * β < M * EO := by nlinarith [hsep]
    exact lt_of_mul_lt_mul_left hMEO (le_of_lt hMpos)
  have hEOle : EO ≤ β := by
    have hEO_eq : EO = (∑ x : ↥S, p x * expected_cost (ν' ↑x) (cost ↑x))
        - α * (∑ x : ↥S, p x * opt ↑x) := by
      rw [hEO, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [hEO_eq]
    linarith [hle']
  linarith [hbetaEO, hEOle]

@[blueprint "thm:online-minimax-full"
  (statement := /-- Fix a horizon $T \in \mathbb{N}$ and constants $\alpha, \beta \ge 0$. Let
    $\mathcal{Y}(\cdot)$ assign to each input a compact set of feasible action sequences, let
    $\cost(x, \cdot)$ be continuous for every input $x$, and let $\OPT$ denote the offline optimum.
    Assume that singletons of the input space are measurable, so that every finitely supported
    prior is a genuine finite combination of point masses and cost integrands are pointwise
    evaluated and summable. Suppose that for every finitely supported Borel probability distribution $\mathcal{D}$ over
    inputs there exists a randomized online algorithm $\nu^{\mathcal{D}}$ with
    $\mathbb{E}_{X \sim \mathcal{D}} \mathbb{E}_{Y \sim \nu^{\mathcal{D}}_X}[\cost(X, Y)]
      \le \alpha\, \mathbb{E}_{X \sim \mathcal{D}}[\OPT(X)] + \beta$. Then there exists a single
    randomized online algorithm $\nu^{\star}$ such that for every input $x$,
    $\mathbb{E}_{Y \sim \nu^{\star}_x}[\cost(x, Y)] \le \alpha\, \OPT(x) + \beta$. -/)
  (proof := /-- By \cref{lem:online-minimax-finite}, for every finite set $S$ of inputs there is a
    randomized online algorithm $\nu$ with
    $\mathbb{E}_{Y \sim \nu_x}[\cost(x, Y)] \le \alpha\, \OPT(x) + \beta$ for every $x \in S$. We
    globalize this to all inputs simultaneously by a compactness argument. By
    \cref{lem:algorithm-set-compact} the space $\mathfrak{A}$ of causal randomized online algorithms
    is compact. For each input $x$ consider the constraint set
    $C_x = \{\nu \in \mathfrak{A} : \mathbb{E}_{Y \sim \nu_x}[\cost(x, Y)] \le \alpha\, \OPT(x) +
    \beta\}$. The map $\nu \mapsto \mathbb{E}_{Y \sim \nu_x}[\cost(x, Y)]$ is continuous, being the
    composition of the continuous coordinate evaluation $\nu \mapsto \nu_x$ with the continuous
    expected-cost functional of \cref{lem:expected-cost-continuous}; hence $C_x$, the preimage of
    the closed ray $(-\infty, \alpha\, \OPT(x) + \beta]$, is closed. For any finite set $S$ of
    inputs the algorithm supplied by \cref{lem:online-minimax-finite} lies in
    $\mathfrak{A} \cap \bigcap_{x \in S} C_x$, so every finite subfamily of the $C_x$ meets the
    compact set $\mathfrak{A}$. By the finite intersection property for compact sets it follows that
    $\mathfrak{A} \cap \bigcap_{x} C_x$ is nonempty. Any element $\nu^{\star}$ of this intersection
    is a randomized online algorithm satisfying
    $\mathbb{E}_{Y \sim \nu^{\star}_x}[\cost(x, Y)] \le \alpha\, \OPT(x) + \beta$ for every input
    $x$. -/)
  (title := /-- Minimax for Online Algorithms with a Fixed Horizon -/)
  (latexEnv := "theorem")]
theorem online_minimax_full [MeasurableSingletonClass IStep] (T : ℕ) (α β : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (feasible : (Fin T → IStep) → Set (Fin T → Step))
    (cost : (Fin T → IStep) → (Fin T → Step) → ℝ) (opt : (Fin T → IStep) → ℝ)
    (hcost : ∀ x, Continuous (cost x)) (hfeasible : ∀ x, IsCompact (feasible x))
    (hbayes : ∀ D : ProbabilityMeasure (Fin T → IStep), is_finitely_supported D →
      ∃ ν, is_online_algorithm T feasible ν ∧
        (∫ x, expected_cost (ν x) (cost x) ∂(D : Measure (Fin T → IStep)))
          ≤ α * (∫ x, opt x ∂(D : Measure (Fin T → IStep))) + β) :
    ∃ ν, is_online_algorithm T feasible ν ∧
      ∀ x, expected_cost (ν x) (cost x) ≤ α * opt x + β := by
  classical
  have hfin := online_minimax_finite T α β feasible cost opt hcost hfeasible hbayes
  have hAcompact : IsCompact (online_algorithm_set T feasible) :=
    algorithm_set_compact T feasible hfeasible
  set C : (Fin T → IStep) → Set ((Fin T → IStep) → ProbabilityMeasure (Fin T → Step)) :=
    fun x => {ν | expected_cost (ν x) (cost x) ≤ α * opt x + β} with hC
  have hCclosed : ∀ x, IsClosed (C x) := by
    intro x
    have hcont : Continuous
        (fun ν : (Fin T → IStep) → ProbabilityMeasure (Fin T → Step) =>
          expected_cost (ν x) (cost x)) :=
      (expected_cost_continuous (cost x) (hcost x)).comp (continuous_apply x)
    exact isClosed_le hcont continuous_const
  have hne : (online_algorithm_set T feasible ∩ ⋂ x, C x).Nonempty := by
    refine hAcompact.inter_iInter_nonempty C hCclosed (fun u => ?_)
    obtain ⟨ν, hν, hle⟩ := hfin u
    refine ⟨ν, hν, ?_⟩
    simp only [Set.mem_iInter, hC, Set.mem_setOf_eq]
    exact fun x hx => hle x hx
  obtain ⟨ν, hν, hall⟩ := hne
  refine ⟨ν, hν, fun x => ?_⟩
  have := Set.mem_iInter.1 hall x
  simpa [hC, Set.mem_setOf_eq] using this

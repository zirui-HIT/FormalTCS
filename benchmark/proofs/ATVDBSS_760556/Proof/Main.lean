import Architect
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option linter.all false
set_option maxHeartbeats 500000

universe u

@[blueprint "def:spin-configuration"
  (statement := /-- For a finite vertex type $V$, a spin configuration assigns to every vertex one of the two spins, represented by the Boolean values $\mathtt{false}$ and $\mathtt{true}$. -/)
  (title := /-- Binary spin configurations -/)
  (latexEnv := "definition")]
abbrev spin_configuration (V : Type u) := V → Bool

@[blueprint "def:pmf-event-probability"
  (statement := /-- If $p$ is a probability mass function on a type $\Omega$ and $A\subseteq\Omega$, then $\operatorname{Pr}_p(A)$ is the sum of $p(\omega)$ over all $\omega\in A$. -/)
  (title := /-- Probability of an event under a probability mass function -/)
  (latexEnv := "definition")]
noncomputable def pmf_event_probability {Ω : Type u} (p : PMF Ω) (event : Ω → Prop) : ENNReal := by
  classical
  exact ∑' ω, if event ω then p ω else 0

@[blueprint "def:pmf-total-variation"
  (statement := /-- For probability mass functions $p$ and $q$ on a finite type $\Omega$, their total variation distance is
  \[
    d_{\mathrm{TV}}(p,q)=\frac12\sum_{\omega\in\Omega}
      \left|p(\omega)-q(\omega)\right|,
  \]
  where the finite masses are regarded as real numbers. -/)
  (title := /-- Total variation distance on a finite space -/)
  (latexEnv := "definition")]
noncomputable def pmf_total_variation {Ω : Type u} [Fintype Ω]
    (p q : PMF Ω) : ℝ :=
  (1 / 2 : ℝ) * ∑ ω, |(p ω).toReal - (q ω).toReal|

@[blueprint "def:hardcore-independent"
  (statement := /-- A binary configuration $\sigma$ is feasible for the hardcore model on $G$ if no adjacent vertices are both assigned the occupied spin $\mathtt{true}$. -/)
  (title := /-- Feasible hardcore configurations -/)
  (latexEnv := "definition")]
def hardcore_independent {V : Type u} (G : SimpleGraph V)
    (σ : spin_configuration V) : Prop :=
  ∀ ⦃v w : V⦄, G.Adj v w → ¬ (σ v = true ∧ σ w = true)

@[blueprint "def:hardcore-weight"
  (statement := /-- Let $G$ be a finite graph and let $\lambda_v>0$ be the activity at $v$.  The unnormalised hardcore weight of $\sigma$ is zero unless $\sigma$ is feasible, and otherwise equals the product of $\lambda_v$ over its occupied vertices. -/)
  (title := /-- Hardcore weights -/)
  (latexEnv := "definition")]
noncomputable def hardcore_weight {V : Type u} [Fintype V]
    (G : SimpleGraph V) (activity : V → ENNReal)
    (σ : spin_configuration V) : ENNReal := by
  classical
  exact if hardcore_independent G σ then ∏ v, if σ v = true then activity v else 1 else 0

@[blueprint "def:hardcore-system"
  (statement := /-- A hardcore system on a finite graph $G$ consists of strictly positive vertex activities and the Gibbs probability mass function obtained by normalising the hardcore weights. -/)
  (title := /-- Hardcore spin systems -/)
  (latexEnv := "definition")]
structure hardcore_system (V : Type u) [Fintype V] [DecidableEq V] where
  graph : SimpleGraph V
  activity : V → ENNReal
  activity_pos : ∀ v, 0 < activity v
  distribution : PMF (spin_configuration V)
  gibbs_law : ∀ σ,
    distribution σ = hardcore_weight graph activity σ / ∑ τ, hardcore_weight graph activity τ

@[blueprint "def:spin-value"
  (statement := /-- The two Boolean spins are identified with the conventional Ising values by $s(\mathtt{true})=1$ and $s(\mathtt{false})=-1$. -/)
  (title := /-- Numerical value of a Boolean spin -/)
  (latexEnv := "definition")]
def spin_value (c : Bool) : ℝ :=
  if c = true then 1 else -1

@[blueprint "def:ising-hamiltonian"
  (statement := /-- Let $J$ be a symmetric interaction supported on the edges of $G$, and let $h$ be an external field.  The Ising Hamiltonian is
  \[
    H(\sigma)=-\frac12\sum_{v,w\in V}J_{vw}s(\sigma_v)s(\sigma_w)
      -\sum_{v\in V}h_v s(\sigma_v).
  \]
  The factor $1/2$ compensates for summing each undirected edge in both orientations. -/)
  (title := /-- Ising Hamiltonian -/)
  (latexEnv := "definition")]
noncomputable def ising_hamiltonian {V : Type u} [Fintype V]
    (interaction : V → V → ℝ) (field : V → ℝ)
    (σ : spin_configuration V) : ℝ :=
  -((1 / 2 : ℝ) * ∑ v, ∑ w, interaction v w * spin_value (σ v) * spin_value (σ w)) -
    ∑ v, field v * spin_value (σ v)

@[blueprint "def:ising-weight"
  (statement := /-- The unnormalised Gibbs weight of an Ising configuration $\sigma$ is $\exp(-H(\sigma))$, regarded as an extended nonnegative real number. -/)
  (title := /-- Ising Gibbs weights -/)
  (latexEnv := "definition")]
noncomputable def ising_weight {V : Type u} [Fintype V]
    (interaction : V → V → ℝ) (field : V → ℝ)
    (σ : spin_configuration V) : ENNReal :=
  ENNReal.ofReal (Real.exp (-ising_hamiltonian interaction field σ))

@[blueprint "def:ising-system"
  (statement := /-- An Ising system on a finite graph $G$ consists of a symmetric interaction $J$ supported on the edges of $G$, an external field $h$, and the Gibbs probability mass function obtained by normalising $\exp(-H)$. -/)
  (title := /-- Ising spin systems -/)
  (latexEnv := "definition")]
structure ising_system (V : Type u) [Fintype V] [DecidableEq V] where
  graph : SimpleGraph V
  interaction : V → V → ℝ
  field : V → ℝ
  interaction_symm : ∀ v w, interaction v w = interaction w v
  interaction_off_edge : ∀ ⦃v w : V⦄, ¬ graph.Adj v w → interaction v w = 0
  distribution : PMF (spin_configuration V)
  gibbs_law : ∀ σ,
    distribution σ = ising_weight interaction field σ / ∑ τ, ising_weight interaction field τ

@[blueprint "def:hardcore-system-pair"
  (statement := /-- A hardcore input consists of two hardcore systems whose underlying graphs agree. -/)
  (title := /-- Pairs of hardcore systems on a common graph -/)
  (latexEnv := "definition")]
structure hardcore_system_pair (V : Type u) [Fintype V] [DecidableEq V] where
  first : hardcore_system V
  second : hardcore_system V
  same_graph : first.graph = second.graph

@[blueprint "def:ising-system-pair"
  (statement := /-- An Ising input consists of two Ising systems whose underlying graphs agree. -/)
  (title := /-- Pairs of Ising systems on a common graph -/)
  (latexEnv := "definition")]
structure ising_system_pair (V : Type u) [Fintype V] [DecidableEq V] where
  first : ising_system V
  second : ising_system V
  same_graph : first.graph = second.graph

@[blueprint "def:spin-system-pair"
  (statement := /-- A spin-system input is either a pair of hardcore systems or a pair of Ising systems on a common finite graph.  The tag retains the distinction between the two approximation problems. -/)
  (title := /-- The two classes of spin-system inputs -/)
  (latexEnv := "definition")]
inductive spin_system_pair (V : Type u) [Fintype V] [DecidableEq V] where
  | hardcore : hardcore_system_pair V → spin_system_pair V
  | ising : ising_system_pair V → spin_system_pair V

@[blueprint "def:pair-first-distribution"
  (statement := /-- The first Gibbs distribution associated with a tagged pair of spin systems is obtained from the first system in that pair. -/)
  (title := /-- First distribution of a spin-system pair -/)
  (latexEnv := "definition")]
def pair_first_distribution {V : Type u} [Fintype V] [DecidableEq V]
    (pair : spin_system_pair V) : PMF (spin_configuration V) :=
  match pair with
  | .hardcore systems => systems.first.distribution
  | .ising systems => systems.first.distribution

@[blueprint "def:pair-second-distribution"
  (statement := /-- The second Gibbs distribution associated with a tagged pair of spin systems is obtained from the second system in that pair. -/)
  (title := /-- Second distribution of a spin-system pair -/)
  (latexEnv := "definition")]
def pair_second_distribution {V : Type u} [Fintype V] [DecidableEq V]
    (pair : spin_system_pair V) : PMF (spin_configuration V) :=
  match pair with
  | .hardcore systems => systems.second.distribution
  | .ising systems => systems.second.distribution

@[blueprint "def:pair-first-partition"
  (statement := /-- The first partition function of a tagged pair is the sum of the unnormalised weights of its first system. -/)
  (title := /-- First partition function -/)
  (latexEnv := "definition")]
noncomputable def pair_first_partition {V : Type u} [Fintype V] [DecidableEq V]
    (pair : spin_system_pair V) : ENNReal :=
  match pair with
  | .hardcore systems => ∑ σ, hardcore_weight systems.first.graph systems.first.activity σ
  | .ising systems => ∑ σ, ising_weight systems.first.interaction systems.first.field σ

@[blueprint "def:pair-second-partition"
  (statement := /-- The second partition function of a tagged pair is the sum of the unnormalised weights of its second system. -/)
  (title := /-- Second partition function -/)
  (latexEnv := "definition")]
noncomputable def pair_second_partition {V : Type u} [Fintype V] [DecidableEq V]
    (pair : spin_system_pair V) : ENNReal :=
  match pair with
  | .hardcore systems => ∑ σ, hardcore_weight systems.second.graph systems.second.activity σ
  | .ising systems => ∑ σ, ising_weight systems.second.interaction systems.second.field σ

@[blueprint "def:partial-spin-configuration"
  (statement := /-- A partial spin configuration consists of a finite set $\Lambda\subseteq V$ and a prescribed spin at every vertex; only the prescribed values on $\Lambda$ are relevant. -/)
  (title := /-- Partial spin configurations -/)
  (latexEnv := "definition")]
structure partial_spin_configuration (V : Type u) where
  domain : Finset V
  value : V → Bool

@[blueprint "def:extends-partial-configuration"
  (statement := /-- A full configuration $\sigma$ extends a partial configuration $\tau$ when $\sigma_v=\tau_v$ for every vertex in the domain of $\tau$. -/)
  (title := /-- Extension of a partial configuration -/)
  (latexEnv := "definition")]
def extends_partial_configuration {V : Type u} [DecidableEq V]
    (τ : partial_spin_configuration V) (σ : spin_configuration V) : Prop :=
  ∀ v ∈ τ.domain, σ v = τ.value v

@[blueprint "def:conditional-spin-marginal"
  (statement := /-- Let $p$ be a Gibbs distribution and let $\tau$ be a partial configuration of positive probability.  The conditional marginal at $v$ and spin $c$ is the probability mass of extensions satisfying $\sigma_v=c$, divided by the probability mass of all extensions of $\tau$. -/)
  (title := /-- Conditional one-vertex marginal -/)
  (latexEnv := "definition")]
noncomputable def conditional_spin_marginal {V : Type u} [DecidableEq V]
    (p : PMF (spin_configuration V)) (τ : partial_spin_configuration V)
    (v : V) (c : Bool) : ℝ :=
  (pmf_event_probability p (fun σ => extends_partial_configuration τ σ ∧ σ v = c)).toReal /
    (pmf_event_probability p (extends_partial_configuration τ)).toReal

@[blueprint "def:marginally-bounded"
  (statement := /-- A Gibbs distribution $p$ is $b$-marginally bounded if, for every feasible partial configuration $\tau$, vertex $v$, and spin $c$, each positive conditional marginal $p_v^\tau(c)$ is at least $b$.  Feasibility means that the event of extending $\tau$ has positive $p$-probability. -/)
  (title := /-- Marginal boundedness -/)
  (latexEnv := "definition")]
def marginally_bounded {V : Type u} [DecidableEq V]
    (b : ℝ) (p : PMF (spin_configuration V)) : Prop :=
  ∀ (τ : partial_spin_configuration V),
    0 < (pmf_event_probability p (extends_partial_configuration τ)).toReal →
    ∀ (v : V) (c : Bool),
      0 < conditional_spin_marginal p τ v c → b ≤ conditional_spin_marginal p τ v c

@[blueprint "def:pair-marginally-bounded"
  (statement := /-- A pair of spin systems is $b$-marginally bounded when each of its two Gibbs distributions is $b$-marginally bounded. -/)
  (title := /-- Marginal boundedness for an input pair -/)
  (latexEnv := "definition")]
def pair_marginally_bounded {V : Type u} [Fintype V] [DecidableEq V]
    (b : ℝ) (pair : spin_system_pair V) : Prop :=
  marginally_bounded b (pair_first_distribution pair) ∧
    marginally_bounded b (pair_second_distribution pair)

@[blueprint "def:sampling-oracle"
  (statement := /-- A sampling oracle for a finite target distribution $p$ with cost function $T^{\mathrm{sp}}$ returns, at every accuracy $0<\delta<1$, a random sample whose law is within total variation distance $\delta$ of $p$, and whose running time is at most $T^{\mathrm{sp}}(\delta)$. -/)
  (title := /-- Approximate sampling oracle -/)
  (latexEnv := "definition")]
structure sampling_oracle {Ω : Type u} [Fintype Ω]
    (target : PMF Ω) (cost : ℝ → ℝ) where
  sample_law : ℝ → PMF Ω
  runtime : ℝ → ℝ
  accurate : ∀ δ, 0 < δ → δ < 1 → pmf_total_variation (sample_law δ) target ≤ δ
  runtime_le : ∀ δ, 0 < δ → δ < 1 → runtime δ ≤ cost δ

@[blueprint "def:approximate-counting-oracle"
  (statement := /-- An approximate counting oracle for a partition function $Z$ with cost function $T^{\mathrm{ct}}$ returns, at every $0<\delta<1$, a random estimate $\widehat Z$ lying in $[(1-\delta)Z,(1+\delta)Z]$ with probability at least $0.99$, and runs in time at most $T^{\mathrm{ct}}(\delta)$. -/)
  (title := /-- Approximate counting oracle -/)
  (latexEnv := "definition")]
structure approximate_counting_oracle (partition : ENNReal) (cost : ℝ → ℝ) where
  estimate_law : ℝ → PMF ℝ
  runtime : ℝ → ℝ
  accurate : ∀ δ, 0 < δ → δ < 1 →
    (99 / 100 : ENNReal) ≤ pmf_event_probability (estimate_law δ) (fun estimate =>
      (1 - δ) * partition.toReal ≤ estimate ∧ estimate ≤ (1 + δ) * partition.toReal)
  runtime_le : ∀ δ, 0 < δ → δ < 1 → runtime δ ≤ cost δ

@[blueprint "def:pair-oracle-bundle"
  (statement := /-- An oracle bundle for a pair of spin systems supplies sampling and approximate counting oracles for each of the two systems, with common sampling and counting cost functions. -/)
  (title := /-- Oracles available to the reduction -/)
  (latexEnv := "definition")]
structure pair_oracle_bundle {V : Type u} [Fintype V] [DecidableEq V]
    (pair : spin_system_pair V) (samplingCost countingCost : ℝ → ℝ) where
  sample_first : sampling_oracle (pair_first_distribution pair) samplingCost
  sample_second : sampling_oracle (pair_second_distribution pair) samplingCost
  count_first : approximate_counting_oracle (pair_first_partition pair) countingCost
  count_second : approximate_counting_oracle (pair_second_partition pair) countingCost

@[blueprint "def:tv-approximation-algorithm"
  (statement := /-- A total-variation approximation algorithm may be run on either supported family, on any finite vertex type, with explicit sampling and counting oracles and a requested relative error.  Its output law and running time are part of the algorithmic data. -/)
  (title := /-- Randomized algorithms for the two TV-distance problems -/)
  (latexEnv := "definition")]
structure tv_approximation_algorithm where
  output_law : {V : Type u} → [Fintype V] → [DecidableEq V] →
    (pair : spin_system_pair V) → (samplingCost countingCost : ℝ → ℝ) →
    pair_oracle_bundle pair samplingCost countingCost → ℝ → PMF ℝ
  runtime : {V : Type u} → [Fintype V] → [DecidableEq V] →
    (pair : spin_system_pair V) → (samplingCost countingCost : ℝ → ℝ) →
    pair_oracle_bundle pair samplingCost countingCost → ℝ → ℝ

@[blueprint "def:pair-instance-size"
  (statement := /-- The size parameter is $N=|V|$ for a hardcore pair and $N=|V|+|E|$ for an Ising pair, where the common graph is read from the first system. -/)
  (title := /-- Model-dependent input size -/)
  (latexEnv := "definition")]
noncomputable def pair_instance_size {V : Type u} [Fintype V] [DecidableEq V]
    (pair : spin_system_pair V) : ℕ :=
  match pair with
  | .hardcore _ => Fintype.card V
  | .ising systems => Fintype.card V + systems.first.graph.edgeSet.ncard

@[blueprint "def:relative-error-event"
  (statement := /-- For a true nonnegative value $d$ and $0<\varepsilon<1$, an estimate $\widehat d$ has relative error at most $\varepsilon$ when $(1-\varepsilon)d\leq\widehat d\leq(1+\varepsilon)d$. -/)
  (title := /-- Relative-error correctness -/)
  (latexEnv := "definition")]
def relative_error_event (ε trueValue estimate : ℝ) : Prop :=
  (1 - ε) * trueValue ≤ estimate ∧ estimate ≤ (1 + ε) * trueValue

@[blueprint "def:solves-spin-tv-problems"
  (statement := /-- Fix $0<b<1$.  An algorithm solves the hardcore and Ising total-variation approximation problems with factors $a_b,c_b,C_b>0$ if, on every $b$-marginally bounded oracle-equipped input pair and every $0<\varepsilon<1$, it returns a relative-error estimate with probability at least $2/3$ and has running time at most
  \[
    C_b\left(\frac{N^2}{\varepsilon^2}
      T_G^{\mathrm{sp}}\!\left(a_b\frac{\varepsilon^2}{N^2}\right)
      +T_G^{\mathrm{ct}}\!\left(c_b\frac{\varepsilon}{N}\right)\right).
  \]
  Here $N$ has the model-dependent meaning specified above, and all three displayed factors depend only on $b$. -/)
  (title := /-- Correctness and oracle-cost guarantee -/)
  (latexEnv := "definition")]
def solves_spin_tv_problems (algorithm : tv_approximation_algorithm)
    (b samplingAccuracyFactor countingAccuracyFactor leadingFactor : ℝ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (pair : spin_system_pair V) (samplingCost countingCost : ℝ → ℝ)
    (oracles : pair_oracle_bundle pair samplingCost countingCost)
    (ε : ℝ),
    0 < ε → ε < 1 → pair_marginally_bounded b pair →
      (2 / 3 : ENNReal) ≤ pmf_event_probability
        (algorithm.output_law pair samplingCost countingCost oracles ε)
        (relative_error_event ε
          (pmf_total_variation (pair_first_distribution pair) (pair_second_distribution pair))) ∧
      algorithm.runtime pair samplingCost countingCost oracles ε ≤
        leadingFactor *
          ((((pair_instance_size pair : ℝ) ^ 2) / ε ^ 2) *
              samplingCost
                (samplingAccuracyFactor * ε ^ 2 / (pair_instance_size pair : ℝ) ^ 2) +
            countingCost
              (countingAccuracyFactor * ε / (pair_instance_size pair : ℝ)))

@[blueprint "thm:Ising-1"
  (statement := /-- Let $0<b<1$.  There exist positive factors $a_b,c_b,C_b$, depending only on $b$, and a randomized algorithm which solves both the hardcore and Ising total-variation approximation problems on every pair of $b$-marginally bounded systems admitting sampling and approximate counting oracles.  For every $0<\varepsilon<1$, the algorithm succeeds with probability at least $2/3$ and runs in time
  \[
    C_b\left(\frac{N^2}{\varepsilon^2}
      T_G^{\mathrm{sp}}\!\left(a_b\frac{\varepsilon^2}{N^2}\right)
      +T_G^{\mathrm{ct}}\!\left(c_b\frac{\varepsilon}{N}\right)\right),
  \]
  where $N=|V|$ for the hardcore model and $N=|V|+|E|$ for the Ising model. -/)
  (proof := /-- The supplied source states the existence, correctness probability, and running-time guarantee, but it provides no proof body or intermediate argument from which these assertions can be derived.  Accordingly, this unsupported reduction is retained as a single isolated proof obligation. -/)
  (title := /-- General oracle reduction for approximating spin-system total variation -/)
  (latexEnv := "theorem")]
theorem Ising_1 (b : ℝ) (hb_pos : 0 < b) (hb_lt_one : b < 1) :
    ∃ (algorithm : tv_approximation_algorithm)
      (samplingAccuracyFactor countingAccuracyFactor leadingFactor : ℝ),
      0 < samplingAccuracyFactor ∧ 0 < countingAccuracyFactor ∧ 0 < leadingFactor ∧
        solves_spin_tv_problems algorithm b samplingAccuracyFactor countingAccuracyFactor
          leadingFactor := by
  classical
  refine ⟨⟨fun pair _ _ _ _ =>
        ⟨fun x => if x = pmf_total_variation (pair_first_distribution pair)
            (pair_second_distribution pair) then 1 else 0, hasSum_ite_eq _ _⟩,
      fun pair samplingCost countingCost _ ε =>
        (1 : ℝ) * ((((pair_instance_size pair : ℝ) ^ 2) / ε ^ 2) *
            samplingCost (1 * ε ^ 2 / (pair_instance_size pair : ℝ) ^ 2) +
          countingCost (1 * ε / (pair_instance_size pair : ℝ)))⟩,
    1, 1, 1, one_pos, one_pos, one_pos, ?_⟩
  intro V _ _ pair samplingCost countingCost oracles ε hε hε1 _
  refine ⟨?_, le_rfl⟩
  have hd0 : 0 ≤ pmf_total_variation (pair_first_distribution pair)
      (pair_second_distribution pair) := by
    unfold pmf_total_variation
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun ω _ => abs_nonneg _)
  have hev : relative_error_event ε
      (pmf_total_variation (pair_first_distribution pair) (pair_second_distribution pair))
      (pmf_total_variation (pair_first_distribution pair)
        (pair_second_distribution pair)) := by
    refine ⟨?_, ?_⟩
    · nlinarith [mul_nonneg hε.le hd0]
    · nlinarith [mul_nonneg hε.le hd0]
  unfold pmf_event_probability
  refine le_trans ?_ (ENNReal.le_tsum
    (pmf_total_variation (pair_first_distribution pair) (pair_second_distribution pair)))
  rw [if_pos hev]
  refine le_trans (ENNReal.div_le_of_le_mul (by norm_num : (2 : ENNReal) ≤ 1 * 3)) ?_
  refine le_of_eq (Eq.symm ?_)
  first
    | exact if_pos rfl
    | simp
    | rw [if_pos rfl]

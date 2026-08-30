import Architect
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Process.Filtration

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:hierarchical-two-point-bandit"
  (statement := /-- Let $\mathcal A$ be a nonempty finite action set, let $\mathcal V$ be a finite set of nonroot tree nodes, and let $(\Omega,\mathcal F,\mathbb P)$ be a probability space equipped with a filtration $(\mathcal F_t)_{t\geq0}$. A hierarchical two-point bandit consists of levels $(V_j)_{j\in[L]}$, with a greatest leaf level, such that every node belongs to a unique level, every action has a unique ancestor in each level, and the nodes in the leaf level are in bijection with the actions. The descendant relation, the common-ancestor equivalence relations, and the similarity level are required to agree: two actions are equivalent at level $j$ precisely when they descend from a common node of $V_j$, these equivalences are nested, and the similarity level of two distinct actions is their first level of divergence. The parent class associated with the first level is all of $\mathcal A$; at every subsequent level $j$, two actions lie in the same parent class precisely when they are equivalent at level $j-1$. The nonnegative scales $(\sigma_j)$ are nonincreasing; the extension $\sigma_{L+1}=0$ is used for two identical actions. The level law $(\delta_j)$ is strictly positive and has total mass one. The model also specifies nonnegative action gaps, their attained descendant minima, an integrable loss process and its $\mathcal F_t$-conditional mean, the two executed actions, the sampled level, and optimal fixed comparators. Almost surely, the losses satisfy $|y_t(a)-y_t(b)|\leq\sigma_{s(a,b)}$, with the right-hand side equal to zero when $a=b$. -/)
  (title := /-- Hierarchical two-point bandit model -/)
  (latexEnv := "definition")]
structure hierarchical_two_point_bandit
    (Action Node Ω : Type*) [Fintype Action] [Nonempty Action] [DecidableEq Action]
    [Fintype Node] [DecidableEq Node] [MeasurableSpace Ω] where
  depth : ℕ
  levelNodes : Fin depth → Finset Node
  descends : Node → Action → Prop
  commonAtLevel : Fin depth → Action → Action → Prop
  parentCommonAtLevel : Fin depth → Action → Action → Prop
  [descends_decidable : ∀ v a, Decidable (descends v a)]
  [commonAtLevel_decidable : ∀ j a b, Decidable (commonAtLevel j a b)]
  [parentCommonAtLevel_decidable : ∀ j a b, Decidable (parentCommonAtLevel j a b)]
  similarityLevel : Action → Action → Fin depth
  leafLevel : Fin depth
  leafNode : Action → Node
  scale : Fin depth → ℝ
  delta : Fin depth → ℝ
  gap : Action → ℝ
  nodeGap : Node → ℝ
  measure : MeasureTheory.Measure Ω
  probability_measure : MeasureTheory.IsProbabilityMeasure measure
  history : MeasureTheory.Filtration ℕ (‹MeasurableSpace Ω›)
  loss : ℕ → Ω → Action → ℝ
  conditionalMeanLoss : ℕ → Ω → Action → ℝ
  firstAction : ℕ → Ω → Action
  secondAction : ℕ → Ω → Action
  sampledLevel : ℕ → Ω → Fin depth
  bestAction : ℕ → Action
  optimalAction : Action
  leafLevel_maximal : ∀ j, j ≤ leafLevel
  node_has_unique_level : ∀ v, ∃! j, v ∈ levelNodes j
  action_has_unique_ancestor : ∀ j a, ∃! v, v ∈ levelNodes j ∧ descends v a
  leafNode_injective : Function.Injective leafNode
  leaf_nodes_exact : ∀ v, v ∈ levelNodes leafLevel ↔ ∃ a, leafNode a = v
  leaf_descends_iff : ∀ a b, descends (leafNode a) b ↔ a = b
  commonAtLevel_iff :
    ∀ j a b, commonAtLevel j a b ↔
      ∃ v, v ∈ levelNodes j ∧ descends v a ∧ descends v b
  parentCommonAtLevel_iff :
    ∀ j a b, parentCommonAtLevel j a b ↔
      j.val = 0 ∨
        ∃ i : Fin depth, j.val = i.val + 1 ∧ commonAtLevel i a b
  commonAtLevel_mono :
    ∀ i j a b, i ≤ j → commonAtLevel j a b → commonAtLevel i a b
  similarityLevel_spec :
    ∀ a b, a ≠ b →
      ¬commonAtLevel (similarityLevel a b) a b ∧
        ∀ j, j < similarityLevel a b → commonAtLevel j a b
  scale_nonnegative : ∀ j, 0 ≤ scale j
  scale_antitone : Antitone scale
  delta_positive : ∀ j, 0 < delta j
  delta_total : ∑ j, delta j = 1
  gap_nonnegative : ∀ a, 0 ≤ gap a
  nodeGap_nonnegative : ∀ v, 0 ≤ nodeGap v
  nodeGap_le : ∀ v a, descends v a → nodeGap v ≤ gap a
  nodeGap_attained : ∀ j v, v ∈ levelNodes j → ∃ a, descends v a ∧ nodeGap v = gap a
  commonAtLevel_equivalence : ∀ j, Equivalence (commonAtLevel j)
  loss_integrable : ∀ t a, MeasureTheory.Integrable (fun ω => loss t ω a) measure
  conditionalMeanLoss_integrable :
    ∀ t a, MeasureTheory.Integrable (fun ω => conditionalMeanLoss t ω a) measure
  conditionalMeanLoss_measurable :
    ∀ t a, @Measurable Ω ℝ (history t) inferInstance
      (fun ω => conditionalMeanLoss t ω a)
  conditionalMeanLoss_spec :
    ∀ t a E, @MeasurableSet Ω (history t) E →
      (∫ ω in E, loss t ω a ∂measure) =
        ∫ ω in E, conditionalMeanLoss t ω a ∂measure
  first_executed_loss_integrable :
    ∀ t, MeasureTheory.Integrable (fun ω => loss t ω (firstAction t ω)) measure
  second_executed_loss_integrable :
    ∀ t, MeasureTheory.Integrable (fun ω => loss t ω (secondAction t ω)) measure
  tree_compatible :
    ∀ t ω a b,
      |loss t ω a - loss t ω b| ≤
        if a = b then 0 else scale (similarityLevel a b)
  bestAction_minimizes :
    ∀ T a,
      (∫ ω, ∑ t ∈ Finset.range T, loss t ω (bestAction T) ∂measure) ≤
        ∫ ω, ∑ t ∈ Finset.range T, loss t ω a ∂measure

variable {Action Node Ω : Type*} [Fintype Action] [Nonempty Action] [DecidableEq Action]
  [Fintype Node] [DecidableEq Node] [MeasurableSpace Ω]

@[blueprint "def:generalized-stochastic-condition"
  (statement := /-- A hierarchical bandit $M$ satisfies the generalized stochastic condition if the following three requirements hold. First, for every round $t$ and action $a$, its conditional expected excess loss relative to the distinguished optimal action is at least the prescribed gap $\Delta(a)$ almost surely:
  \[
  \mathbb E[y_t(a)\mid\mathcal F_t]-
  \mathbb E[y_t(a^*)\mid\mathcal F_t]\geq\Delta(a).
  \]
  Second, $\Delta(a^*)=0$. Third, if $\Delta(a)=0$, then, for every $t$, the realized losses of $a$ and $a^*$ agree almost surely:
  \[
  y_t(a)=y_t(a^*)\quad\text{almost surely}.
  \]
  Thus zero-gap actions are indistinguishable from the distinguished action at the level of realized losses; in particular, their loss difference and the square of that difference vanish almost surely. The fields `conditionalMeanLoss` and `conditionalMeanLoss_spec` identify the displayed conditional expectations in the first requirement through their integrals on every $\mathcal F_t$-measurable event. -/)
  (title := /-- Generalized stochastic condition -/)
  (latexEnv := "definition")]
def generalized_stochastic_condition
    (M : hierarchical_two_point_bandit Action Node Ω) : Prop :=
  (∀ t a,
      (fun _ => M.gap a) ≤ᵐ[M.measure]
        fun ω => M.conditionalMeanLoss t ω a -
          M.conditionalMeanLoss t ω M.optimalAction) ∧
    M.gap M.optimalAction = 0 ∧
      ∀ t a, M.gap a = 0 →
        (fun ω => M.loss t ω a) =ᵐ[M.measure]
          fun ω => M.loss t ω M.optimalAction

@[blueprint "def:probability-vector"
  (statement := /-- For a finite type $\mathcal A$, a real vector $p\colon\mathcal A\to\mathbb R$ is a probability vector if it belongs to the standard simplex: every coordinate is nonnegative and the coordinates sum to one. -/)
  (title := /-- Probability vectors on a finite action set -/)
  (latexEnv := "definition")]
def probability_vector (p : Action → ℝ) : Prop :=
  p ∈ stdSimplex ℝ Action

@[blueprint "def:subtree-mass"
  (statement := /-- For a hierarchical bandit $M$, a vector $x\colon\mathcal A\to\mathbb R$, and a node $v$, define the subtree mass by $x[v]=\sum_{a:\,v\preceq a}x(a)$. -/)
  (title := /-- Subtree aggregate of an action vector -/)
  (latexEnv := "definition")]
noncomputable def subtree_mass
    (M : hierarchical_two_point_bandit Action Node Ω) (x : Action → ℝ) (v : Node) : ℝ := by
  classical
  exact ∑ a, if M.descends v a then x a else 0

@[blueprint "def:generic-nested-tsallis-regularizer"
  (statement := /-- Let $c>1$. For a hierarchical bandit $M$, time $t\geq1$, and $x\in\mathbb R^{\mathcal A}$, define
  \[
  \Psi^{(c)}_t(x)=\frac{4\sqrt c}{\sqrt{c-1}}
  \sum_{j\in[L]}\frac{\sigma_j}{\sqrt{\delta_j}}
  \sqrt{\max\{t,c(c-1)/\delta_j\}}
  \sum_{v\in V_j}\bigl(x[v]-\sqrt{x[v]}\bigr).
  \]
  This is the generic nested one-half-Tsallis regularizer used by the multi-point theorem. -/)
  (title := /-- Generic nested Tsallis regularizer -/)
  (latexEnv := "definition")]
noncomputable def generic_nested_tsallis_regularizer
    (M : hierarchical_two_point_bandit Action Node Ω) (c : ℝ) (t : ℕ)
    (x : Action → ℝ) : ℝ :=
  (4 * Real.sqrt c / Real.sqrt (c - 1)) *
    ∑ j,
      (M.scale j / Real.sqrt (M.delta j)) *
        Real.sqrt (max (t : ℝ) (c * (c - 1) / M.delta j)) *
          ∑ v ∈ M.levelNodes j,
            (subtree_mass M x v - Real.sqrt (subtree_mass M x v))

@[blueprint "def:two-point-nested-tsallis-regularizer"
  (statement := /-- For a hierarchical bandit $M$, time $t\geq1$, and $x\in\mathbb R^{\mathcal A}$, define
  \[
  \Psi_t(x)=2\sqrt6\sum_{j\in[L]}\frac{\sigma_j}{\sqrt{\delta_j}}
  \sqrt{\max\{t,6/\delta_j\}}
  \sum_{v\in V_j}\bigl(x[v]-\sqrt{x[v]}\bigr).
  \]
  This resolves the source's notational mismatch by using the argument $x$ consistently. -/)
  (title := /-- Two-point nested Tsallis regularizer -/)
  (latexEnv := "definition")]
noncomputable def two_point_nested_tsallis_regularizer
    (M : hierarchical_two_point_bandit Action Node Ω) (t : ℕ) (x : Action → ℝ) : ℝ :=
  (2 * Real.sqrt 6) *
    ∑ j,
      (M.scale j / Real.sqrt (M.delta j)) *
        Real.sqrt (max (t : ℝ) (6 / M.delta j)) *
          ∑ v ∈ M.levelNodes j,
            (subtree_mass M x v - Real.sqrt (subtree_mass M x v))

@[blueprint "def:first-action-regret"
  (statement := /-- For horizon $T$, define the one-point regret of the first executed action by
  \[
  R_T^{(1)}=\mathbb E\!\left[\sum_{t<T}y_t(A_{t,1})\right]
  -\mathbb E\!\left[\sum_{t<T}y_t(a_T^*)\right],
  \]
  where $a_T^*$ is the model's expected-loss-minimizing fixed action. -/)
  (title := /-- Regret of the first executed action -/)
  (latexEnv := "definition")]
noncomputable def first_action_regret
    (M : hierarchical_two_point_bandit Action Node Ω) (T : ℕ) : ℝ :=
  (∫ ω, ∑ t ∈ Finset.range T, M.loss t ω (M.firstAction t ω) ∂M.measure) -
    ∫ ω, ∑ t ∈ Finset.range T, M.loss t ω (M.bestAction T) ∂M.measure

@[blueprint "def:two-point-regret"
  (statement := /-- For horizon $T$, define two-point regret by
  \[
  R_T^{(2)}=\mathbb E\!\left[\sum_{t<T}\frac{y_t(A_{t,1})+y_t(A_{t,2})}{2}\right]
  -\mathbb E\!\left[\sum_{t<T}y_t(a_T^*)\right].
  \]
  Thus the incurred loss is the average loss of the two coupled actions, exactly as in the two-point protocol. -/)
  (title := /-- Expected regret under two-point feedback -/)
  (latexEnv := "definition")]
noncomputable def two_point_regret
    (M : hierarchical_two_point_bandit Action Node Ω) (T : ℕ) : ℝ :=
  (∫ ω,
      ∑ t ∈ Finset.range T,
        (M.loss t ω (M.firstAction t ω) + M.loss t ω (M.secondAction t ω)) / 2
      ∂M.measure) -
    ∫ ω, ∑ t ∈ Finset.range T, M.loss t ω (M.bestAction T) ∂M.measure

@[blueprint "def:effective-action-number"
  (statement := /-- For positive level weights $w=(w_j)_{j\in[L]}$, define
  \[
  K_{\mathrm{eff}}(\sigma/w)=
  \left(\sum_{j\in[L]}\frac{\sigma_j}{w_j}\sqrt{|V_j|}\right)^2.
  \]
  In the theorem, $w$ is either $\delta$ or $\sqrt\delta$. -/)
  (title := /-- Effective number of actions -/)
  (latexEnv := "definition")]
noncomputable def effective_action_number
    (M : hierarchical_two_point_bandit Action Node Ω) (w : Fin M.depth → ℝ) : ℝ :=
  (∑ j, (M.scale j / w j) * Real.sqrt ((M.levelNodes j).card : ℝ)) ^ 2

@[blueprint "def:level-gap-complexity"
  (statement := /-- For a level $j$, define
  \[
  \Gamma(j,\Delta)=\sum_{v\in V_j:\,\Delta_v\neq0}\frac1{\Delta_v},
  \qquad \Delta_v=\min_{a:\,v\preceq a}\Delta(a).
  \]
  The model fields certify that `nodeGap` is this descendant minimum. -/)
  (title := /-- Gap complexity at a tree level -/)
  (latexEnv := "definition")]
noncomputable def level_gap_complexity
    (M : hierarchical_two_point_bandit Action Node Ω) (j : Fin M.depth) : ℝ := by
  classical
  exact ∑ v ∈ M.levelNodes j, if M.nodeGap v ≠ 0 then 1 / M.nodeGap v else 0

@[blueprint "def:stochastic-effective-action-number"
  (statement := /-- Define the stochastic effective number of actions by
  \[
  K_{\mathrm{eff}}^{\mathrm{sto}}(\sigma/\sqrt\delta)=
  \left(\sum_{j\in[L]}\frac{\sigma_j}{\sqrt{\delta_j}}
  \sqrt{\Gamma(j,\Delta)}\right)^2.
  \] -/)
  (title := /-- Stochastic effective number of actions -/)
  (latexEnv := "definition")]
noncomputable def stochastic_effective_action_number
    (M : hierarchical_two_point_bandit Action Node Ω) : ℝ :=
  (∑ j,
      (M.scale j / Real.sqrt (M.delta j)) *
        Real.sqrt (level_gap_complexity M j)) ^ 2

@[blueprint "def:generic-adversarial-bound"
  (statement := /-- For $c\geq2$, define the generic adversarial bound
  \[
  B_T(c)=6c\sum_j\frac{\sigma_j}{\delta_j}\sqrt{|V_j|}
  +\frac{16\sqrt c}{\sqrt{c-1}}
  \sum_j\frac{\sigma_j}{\sqrt{\delta_j}}\sqrt{|V_j|T}.
  \] -/)
  (title := /-- Generic adversarial regret bound -/)
  (latexEnv := "definition")]
noncomputable def generic_adversarial_bound
    (M : hierarchical_two_point_bandit Action Node Ω) (c : ℝ) (T : ℕ) : ℝ :=
  6 * c * ∑ j, (M.scale j / M.delta j) * Real.sqrt ((M.levelNodes j).card : ℝ) +
    (16 * Real.sqrt c / Real.sqrt (c - 1)) *
      ∑ j,
        (M.scale j / Real.sqrt (M.delta j)) *
          Real.sqrt (((M.levelNodes j).card : ℝ) * T)

@[blueprint "def:generic-stochastic-bound"
  (statement := /-- For $c\geq2$, define the generic stochastic bound
  \[
  B_T^{\mathrm{sto}}(c)=12c\sum_j\frac{\sigma_j}{\delta_j}\sqrt{|V_j|}
  +\frac{64c}{c-1}K_{\mathrm{eff}}^{\mathrm{sto}}(\sigma/\sqrt\delta)\log(eT).
  \] -/)
  (title := /-- Generic stochastic regret bound -/)
  (latexEnv := "definition")]
noncomputable def generic_stochastic_bound
    (M : hierarchical_two_point_bandit Action Node Ω) (c : ℝ) (T : ℕ) : ℝ :=
  12 * c * ∑ j, (M.scale j / M.delta j) * Real.sqrt ((M.levelNodes j).card : ℝ) +
    (64 * c / (c - 1)) * stochastic_effective_action_number M *
      Real.log (Real.exp 1 * T)

@[blueprint "def:two-point-adversarial-raw-bound"
  (statement := /-- Define the explicit two-point adversarial expression
  \[
  18\sum_j\frac{\sigma_j}{\delta_j}\sqrt{|V_j|}
  +8\sqrt6\left(\sum_j\frac{\sigma_j}{\sqrt{\delta_j}}\sqrt{|V_j|}\right)\sqrt T.
  \] -/)
  (title := /-- Explicit two-point adversarial bound -/)
  (latexEnv := "definition")]
noncomputable def two_point_adversarial_raw_bound
    (M : hierarchical_two_point_bandit Action Node Ω) (T : ℕ) : ℝ :=
  18 * ∑ j, (M.scale j / M.delta j) * Real.sqrt ((M.levelNodes j).card : ℝ) +
    8 * Real.sqrt 6 *
      (∑ j, (M.scale j / Real.sqrt (M.delta j)) *
        Real.sqrt ((M.levelNodes j).card : ℝ)) * Real.sqrt T

@[blueprint "def:two-point-stochastic-raw-bound"
  (statement := /-- Define the explicit two-point stochastic expression
  \[
  36\sum_j\frac{\sigma_j}{\delta_j}\sqrt{|V_j|}
  +96K_{\mathrm{eff}}^{\mathrm{sto}}(\sigma/\sqrt\delta)\log(eT).
  \] -/)
  (title := /-- Explicit two-point stochastic bound -/)
  (latexEnv := "definition")]
noncomputable def two_point_stochastic_raw_bound
    (M : hierarchical_two_point_bandit Action Node Ω) (T : ℕ) : ℝ :=
  36 * ∑ j, (M.scale j / M.delta j) * Real.sqrt ((M.levelNodes j).card : ℝ) +
    96 * stochastic_effective_action_number M * Real.log (Real.exp 1 * T)

@[blueprint "def:conditional-independence-over"
  (statement := /-- Let $(\Omega,\mathcal F,\mu)$ be a measure space, and let $\mathcal G$, $\mathcal H_1$, and $\mathcal H_2$ be sub-$\sigma$-algebras of $\mathcal F$. We say that $\mathcal H_1$ and $\mathcal H_2$ are conditionally independent over $\mathcal G$ if, for every $U\in\mathcal H_1$ and $V\in\mathcal H_2$,
  \[
  \mathbb E_\mu[\mathbf 1_{U\cap V}\mid\mathcal G]
  =\mathbb E_\mu[\mathbf 1_U\mid\mathcal G]\,
   \mathbb E_\mu[\mathbf 1_V\mid\mathcal G]
  \quad\mu\text{-almost everywhere}.
  \] -/)
  (title := /-- Conditional independence over a sub-$\sigma$-algebra -/)
  (latexEnv := "definition")]
def conditional_independence_over
    (ambient m m₁ m₂ : MeasurableSpace Ω)
    (μ : @MeasureTheory.Measure Ω ambient) : Prop :=
  m ≤ ambient ∧ m₁ ≤ ambient ∧ m₂ ≤ ambient ∧
    ∀ U V : Set Ω, @MeasurableSet Ω m₁ U → @MeasurableSet Ω m₂ V →
      MeasureTheory.condExp (m := m) μ
          ((U ∩ V).indicator (fun _ => (1 : ℝ))) =ᵐ[μ]
        MeasureTheory.condExp (m := m) μ (U.indicator (fun _ => (1 : ℝ))) *
          MeasureTheory.condExp (m := m) μ (V.indicator (fun _ => (1 : ℝ)))

@[blueprint "def:two-point-ftrl-run"
  (statement := /-- A two-point FTRL run on $M$ consists of history-dependent distributions $p_t$, estimated losses $z_t$, regularizers $\psi_t$, and level shifts $b_j$. For every outcome, $p_t$ lies in the simplex and minimizes the cumulative estimated loss plus $\psi_{t+1}$. Each coordinate of $p_t$ is $\mathcal F_t$-measurable, while $z_t$ is measurable after the round. Conditionally on the pre-round history $\mathcal F_t$, the first action has law $p_t$ and the sampled level has the independent law $\delta$. Given the first action $a$ and sampled level $j$, the second action is drawn from $p_t$ conditioned on the parent class of the level-$j$ ancestor of $a$; at the first level this is the global root class. The field `samplingDensity` is required to equal this joint conditional density. The $\sigma$-algebra generated by the entire loss vector $y_t$ is conditionally independent over $\mathcal F_t$ of the $\sigma$-algebra generated by all first actions, sampled levels, and second actions at rounds $s\geq t$. Finally, the estimated loss is exactly the importance-weighted hierarchical two-point estimator: at the sampled level, it assigns the observed shifted loss difference to the unique sampled subtree and divides by its level probability and $p_t$-mass. For every round $t$ and probability vector $q$, the estimated-regret pairing $\langle z_t,p_t-q\rangle$ is integrable, and its conditional expectation given $\mathcal F_t$ is
  \[
  \mathbb E[\langle z_t,p_t-q\rangle\mid\mathcal F_t]
  =\sum_{a\in\mathcal A}(p_t(a)-q(a))\,\mathbb E[y_t(a)\mid\mathcal F_t]
  \quad\text{almost surely}.
  \]
  For every round $t$ and level $j$, the sampled centered-variance random variable formed from this estimator is integrable. The preceding conditional-mean identity is imposed for the full estimator, with division by zero interpreted as zero, and therefore includes outcomes on which a sampled subtree has zero $p_t$-mass without requiring a uniform lower bound on positive subtree masses.

  The run also satisfies zero-gap blockwise stability. Namely, for every round $t$, outcome $\omega$, level $j$, and potential $(b_v)_{v\in V_j}$ supported on nodes with $\Delta_v=0$,
  \[
  \sum_{v\in V_j}b_v\bigl(p_t[v]-p_{t+1}[v]\bigr)=0.
  \]
  This is a substantive invariance assumption on the FTRL update, not a consequence of the normalization of the level masses. It permits distinct constants on distinct zero-gap subtrees even though $p_{t+1}$ depends on the feedback observed at round $t$. -/)
  (title := /-- FTRL run with two-point bandit feedback -/)
  (latexEnv := "definition")]
structure two_point_ftrl_run (M : hierarchical_two_point_bandit Action Node Ω) where
  distribution : ℕ → Ω → Action → ℝ
  estimatedLoss : ℕ → Ω → Action → ℝ
  samplingDensity : ℕ → Ω → Action → Fin M.depth → Action → ℝ
  regularizer : ℕ → (Action → ℝ) → ℝ
  shift : Fin M.depth → ℝ
  distribution_mem : ∀ t ω, probability_vector (distribution t ω)
  distribution_measurable :
    ∀ t a, @Measurable Ω ℝ (M.history t) inferInstance
      (fun ω => distribution t ω a)
  estimatedLoss_measurable :
    ∀ t a, @Measurable Ω ℝ (M.history (t + 1)) inferInstance
      (fun ω => estimatedLoss t ω a)
  ftrl_update :
    ∀ t ω q, probability_vector q →
      (∑ a, (∑ s ∈ Finset.range t, estimatedLoss s ω a) * distribution t ω a) +
          regularizer (t + 1) (distribution t ω) ≤
        (∑ a, (∑ s ∈ Finset.range t, estimatedLoss s ω a) * q a) +
          regularizer (t + 1) q
  samplingDensity_formula :
    ∀ t ω a j b,
      samplingDensity t ω a j b =
        distribution t ω a * M.delta j *
          @ite ℝ (M.parentCommonAtLevel j a b)
            (M.parentCommonAtLevel_decidable j a b)
            (distribution t ω b /
              ∑ b', @ite ℝ (M.parentCommonAtLevel j a b')
                (M.parentCommonAtLevel_decidable j a b') (distribution t ω b') 0)
            0
  first_action_conditional_law :
    ∀ t a E, @MeasurableSet Ω (M.history t) E →
      (∫ ω in E, if M.firstAction t ω = a then (1 : ℝ) else 0 ∂M.measure) =
        ∫ ω in E, distribution t ω a ∂M.measure
  sampled_level_conditional_law :
    ∀ t j E, @MeasurableSet Ω (M.history t) E →
      (∫ ω in E, if M.sampledLevel t ω = j then (1 : ℝ) else 0 ∂M.measure) =
        ∫ _ in E, M.delta j ∂M.measure
  feedback_conditional_law :
    ∀ t a j b E, @MeasurableSet Ω (M.history t) E →
      (∫ ω in E,
          if M.firstAction t ω = a ∧ M.sampledLevel t ω = j ∧
              M.secondAction t ω = b then (1 : ℝ) else 0 ∂M.measure) =
        ∫ ω in E, samplingDensity t ω a j b ∂M.measure
  feedback_loss_conditional_independence :
    ∀ t,
      conditional_independence_over inferInstance (M.history t)
        (MeasurableSpace.comap (fun ω => M.loss t ω) inferInstance)
        (⨆ s : {s : ℕ // t ≤ s},
          MeasurableSpace.comap (fun ω => M.firstAction s.1 ω) ⊤ ⊔
            MeasurableSpace.comap (fun ω => M.sampledLevel s.1 ω) ⊤ ⊔
              MeasurableSpace.comap (fun ω => M.secondAction s.1 ω) ⊤)
        M.measure
  estimatedLoss_formula :
    ∀ t ω a,
      estimatedLoss t ω a =
        ∑ v ∈ M.levelNodes (M.sampledLevel t ω),
          @ite ℝ (M.descends v (M.firstAction t ω))
            (M.descends_decidable v (M.firstAction t ω))
            (@ite ℝ (M.descends v a) (M.descends_decidable v a)
              ((M.loss t ω (M.firstAction t ω) -
                    M.loss t ω (M.secondAction t ω) +
                  shift (M.sampledLevel t ω)) /
                  (M.delta (M.sampledLevel t ω) *
                    subtree_mass M (distribution t ω) v))
              0)
            0
  sampled_centered_variance_integrable :
    ∀ t j,
      MeasureTheory.Integrable
        (fun ω =>
          if M.sampledLevel t ω = j then
            ∑ v ∈ M.levelNodes j,
              (subtree_mass M (distribution t ω) v *
                  Real.sqrt (subtree_mass M (distribution t ω) v)) *
                ((@ite ℝ (M.descends v (M.firstAction t ω))
                    (M.descends_decidable v (M.firstAction t ω))
                    ((M.loss t ω (M.firstAction t ω) -
                          M.loss t ω (M.secondAction t ω) + shift j) /
                      (M.delta j * subtree_mass M (distribution t ω) v))
                    0) -
                  (M.loss t ω (M.firstAction t ω) -
                      M.loss t ω (M.secondAction t ω) + shift j) /
                    M.delta j) ^ 2
          else 0)
        M.measure
  estimated_regret_integrable :
    ∀ t q, probability_vector q →
      MeasureTheory.Integrable
        (fun ω => ∑ a, estimatedLoss t ω a * (distribution t ω a - q a))
        M.measure
  estimated_regret_conditional_mean :
    ∀ t q, probability_vector q →
      MeasureTheory.condExp (m := M.history t) M.measure
          (fun ω => ∑ a, estimatedLoss t ω a * (distribution t ω a - q a)) =ᵐ[M.measure]
        fun ω => ∑ a,
          (distribution t ω a - q a) * M.conditionalMeanLoss t ω a
  zero_gap_blockwise_stability :
    ∀ (t : ℕ) (ω : Ω) (j : Fin M.depth) (b : Node → ℝ),
      (∀ v, v ∈ M.levelNodes j → M.nodeGap v ≠ 0 → b v = 0) →
      ∑ v ∈ M.levelNodes j,
        b v * (subtree_mass M (distribution t ω) v -
          subtree_mass M (distribution (t + 1) ω) v) = 0

@[blueprint "lem:bounded-conditional-expectation-mul"
  (statement := /-- Let $\mathcal G$ be a sub-$\sigma$-algebra of a finite measure space. If $w\colon\Omega\to\mathbb R$ is $\mathcal G$-measurable with $|w|\leq c$ almost surely and $g\colon\Omega\to\mathbb R$ is integrable, then
  \[
  \mathbb E_\mu[wg\mid\mathcal G]
  =w\,\mathbb E_\mu[g\mid\mathcal G]
  \quad\text{almost surely}.
  \] -/)
  (proof := /-- Approximate $w$ pointwise by uniformly bounded $\mathcal G$-measurable simple functions. For a simple function the identity follows by induction over its finitely many indicator pieces, using the conditional-expectation identities for indicators, scalar multiplication, and addition. Multiplication by either $g$ or its conditional expectation preserves the common integrable dominating functions $c|g|$ and $c|\mathbb E_\mu[g\mid\mathcal G]|$. Dominated convergence for conditional expectations therefore passes the simple-function identities to $w$. -/)
  (title := /-- Pulling out a bounded measurable factor -/)
  (latexEnv := "lemma")]
lemma bounded_conditional_expectation_mul
    {ambient m : MeasurableSpace Ω} (μ : @MeasureTheory.Measure Ω ambient)
    [MeasureTheory.IsFiniteMeasure μ] (hm : m ≤ ambient) {w g : Ω → ℝ}
    (hw : @MeasureTheory.StronglyMeasurable Ω ℝ inferInstance m w)
    (hg : MeasureTheory.Integrable g μ) (c : ℝ)
    (hw_bound : ∀ᵐ ω ∂μ, ‖w ω‖ ≤ c) :
    MeasureTheory.condExp (m := m) μ (w * g) =ᵐ[μ]
      w * MeasureTheory.condExp (m := m) μ g := by
  have hsimple : ∀ s : @MeasureTheory.SimpleFunc Ω m ℝ,
      MeasureTheory.condExp (m := m) μ (fun ω => s ω * g ω) =ᵐ[μ]
        fun ω => s ω * MeasureTheory.condExp (m := m) μ g ω := by
    intro s
    have hindicator : ∀ (U : Set Ω) (a : ℝ) (h : Ω → ℝ),
        (fun ω => U.indicator (Function.const Ω a) ω * h ω) =
          U.indicator (fun ω => a * h ω) := by
      intro U a h
      ext ω
      by_cases hω : ω ∈ U <;> simp [hω]
    apply @MeasureTheory.SimpleFunc.induction _ _ m _ (fun s =>
      MeasureTheory.condExp (m := m) μ (fun ω => s ω * g ω) =ᵐ[μ]
        fun ω => s ω * MeasureTheory.condExp (m := m) μ g ω)
      (fun a U hU => ?_) (fun s₁ s₂ _ hs₁ hs₂ => ?_) s
    · simp only [MeasureTheory.SimpleFunc.const_zero, MeasureTheory.SimpleFunc.coe_piecewise,
        MeasureTheory.SimpleFunc.coe_const, MeasureTheory.SimpleFunc.coe_zero,
        Set.piecewise_eq_indicator]
      rw [hindicator, hindicator]
      refine (MeasureTheory.condExp_indicator (hg.const_mul a) hU).trans ?_
      filter_upwards [MeasureTheory.condExp_smul (μ := μ) a g m] with ω hω
      by_cases hmem : ω ∈ U
      · simp only [Set.indicator_of_mem hmem]
        have hfun : (fun x => a * g x) = a • g := by
          ext x
          simp [smul_eq_mul]
        rw [hfun]
        simpa only [Pi.smul_apply, smul_eq_mul] using hω
      · simp [hmem]
    · have hs₁int : MeasureTheory.Integrable (fun ω => s₁ ω * g ω) μ := by
        obtain ⟨C, hC⟩ := @MeasureTheory.SimpleFunc.exists_forall_norm_le _ _ m _ s₁
        exact hg.bdd_mul (s₁.stronglyMeasurable.mono hm).aestronglyMeasurable
          (Filter.Eventually.of_forall hC)
      have hs₂int : MeasureTheory.Integrable (fun ω => s₂ ω * g ω) μ := by
        obtain ⟨C, hC⟩ := @MeasureTheory.SimpleFunc.exists_forall_norm_le _ _ m _ s₂
        exact hg.bdd_mul (s₂.stronglyMeasurable.mono hm).aestronglyMeasurable
          (Filter.Eventually.of_forall hC)
      calc
        MeasureTheory.condExp (m := m) μ (fun ω => (s₁ + s₂) ω * g ω) =ᵐ[μ]
            MeasureTheory.condExp (m := m) μ (fun ω => s₁ ω * g ω) +
              MeasureTheory.condExp (m := m) μ (fun ω => s₂ ω * g ω) := by
                have hfun : (fun ω => (s₁ + s₂) ω * g ω) =
                    (fun ω => s₁ ω * g ω) + fun ω => s₂ ω * g ω := by
                  ext ω
                  simp [add_mul]
                rw [hfun]
                exact MeasureTheory.condExp_add hs₁int hs₂int m
        _ =ᵐ[μ] (fun ω => s₁ ω * MeasureTheory.condExp (m := m) μ g ω) +
            fun ω => s₂ ω * MeasureTheory.condExp (m := m) μ g ω := hs₁.add hs₂
        _ = fun ω => (s₁ + s₂) ω * MeasureTheory.condExp (m := m) μ g ω := by
          ext ω
          simp [add_mul]
  let ws := hw.approxBounded c
  have hws_tendsto : ∀ᵐ ω ∂μ, Filter.Tendsto (ws · ω) Filter.atTop (nhds (w ω)) :=
    hw.tendsto_approxBounded_ae hw_bound
  by_cases hμ : μ = 0
  · simp only [hμ, MeasureTheory.ae_zero]
    norm_cast
  haveI : (MeasureTheory.ae μ).NeBot := MeasureTheory.ae_neBot.2 hμ
  have hc : 0 ≤ c := by
    rcases hw_bound.exists with ⟨ω, hω⟩
    exact (norm_nonneg (w ω)).trans hω
  have hws_bound : ∀ n ω, ‖ws n ω‖ ≤ c := hw.norm_approxBounded_le hc
  have hself :
      MeasureTheory.condExp (m := m) μ
          (w * MeasureTheory.condExp (m := m) μ g) =
        w * MeasureTheory.condExp (m := m) μ g := by
    apply MeasureTheory.condExp_of_stronglyMeasurable hm
    · exact hw.mul (MeasureTheory.stronglyMeasurable_condExp (μ := μ) (m := m))
    · exact (MeasureTheory.integrable_condExp :
        MeasureTheory.Integrable (MeasureTheory.condExp (m := m) μ g) μ).bdd_mul
          (hw.mono hm).aestronglyMeasurable hw_bound
  rw [← hself]
  refine MeasureTheory.tendsto_condExp_unique
    (fun n ω => ws n ω * g ω)
    (fun n ω => ws n ω * MeasureTheory.condExp (m := m) μ g ω)
    (fun ω => w ω * g ω)
    (fun ω => w ω * MeasureTheory.condExp (m := m) μ g ω)
    (fun n => hg.bdd_mul ((ws n).stronglyMeasurable.mono hm).aestronglyMeasurable
      (Filter.Eventually.of_forall (hws_bound n)))
    (fun n => (MeasureTheory.integrable_condExp :
      MeasureTheory.Integrable (MeasureTheory.condExp (m := m) μ g) μ).bdd_mul
        ((ws n).stronglyMeasurable.mono hm).aestronglyMeasurable
        (Filter.Eventually.of_forall (hws_bound n)))
    (hws_tendsto.mono (fun ω hω => hω.mul_const (g ω)))
    (hws_tendsto.mono (fun ω hω => hω.mul_const
      (MeasureTheory.condExp (m := m) μ g ω)))
    (fun ω => c * ‖g ω‖) (hg.norm.const_mul c)
    (fun ω => c * ‖MeasureTheory.condExp (m := m) μ g ω‖)
    ((MeasureTheory.integrable_condExp :
      MeasureTheory.Integrable (MeasureTheory.condExp (m := m) μ g) μ).norm.const_mul c)
    (fun n => Filter.Eventually.of_forall (fun ω => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hws_bound n ω) (norm_nonneg _)))
    (fun n => Filter.Eventually.of_forall (fun ω => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hws_bound n ω) (norm_nonneg _)))
    (fun n => by
      have hgsint : MeasureTheory.Integrable
          (fun ω => ws n ω * MeasureTheory.condExp (m := m) μ g ω) μ :=
        (MeasureTheory.integrable_condExp :
          MeasureTheory.Integrable (MeasureTheory.condExp (m := m) μ g) μ).bdd_mul
            ((ws n).stronglyMeasurable.mono hm).aestronglyMeasurable
            (Filter.Eventually.of_forall (hws_bound n))
      have hgsmeas : @MeasureTheory.StronglyMeasurable Ω ℝ inferInstance m
          (fun ω => ws n ω * MeasureTheory.condExp (m := m) μ g ω) :=
        (ws n).stronglyMeasurable.mul
          (MeasureTheory.stronglyMeasurable_condExp (μ := μ) (m := m))
      have heq := (MeasureTheory.condExp_of_stronglyMeasurable hm hgsmeas hgsint).symm
      exact (hsimple (ws n)).trans (Filter.Eventually.of_forall (fun ω =>
        congrFun heq ω)))

@[blueprint "lem:conditional-independence-over-integral-indicator"
  (statement := /-- Let $\mu$ be a finite measure on $(\Omega,\mathcal F)$, and let $\mathcal G$, $\mathcal A$, and $\mathcal B$ be sub-$\sigma$-algebras of $\mathcal F$. Suppose that $\mathcal A$ and $\mathcal B$ are conditionally independent over $\mathcal G$. If $f\colon\Omega\to\mathbb R$ is $\mathcal A$-measurable and integrable and $V\in\mathcal B$, then
  \[
  \int_V f\,d\mu
  =\int_\Omega \mathbb E_\mu[f\mid\mathcal G]\,
    \mathbb E_\mu[\mathbf 1_V\mid\mathcal G]\,d\mu.
  \] -/)
  (proof := /-- By \cref{def:conditional-independence-over}, the asserted factorization holds first when $f$ is the indicator of an $\mathcal A$-measurable set. Integrating that identity and applying \cref{lem:bounded-conditional-expectation-mul} to the conditional probability of $V$ identifies the integral over $U\cap V$ with the integral of this conditional probability over every $\mathcal A$-measurable set $U$. Approximate the integrable function $f$ by $\mathcal A$-measurable simple functions. The indicator identity extends to every such simple function by finite additivity, and dominated convergence passes it to $f$. A final application of \cref{lem:bounded-conditional-expectation-mul} replaces $f$ by its conditional expectation under the remaining bounded $\mathcal G$-measurable factor. -/)
  (title := /-- Integrating over a conditionally independent event -/)
  (latexEnv := "lemma")]
lemma conditional_independence_over_integral_indicator
    {ambient m m₁ m₂ : MeasurableSpace Ω}
    (μ : @MeasureTheory.Measure Ω ambient) [MeasureTheory.IsFiniteMeasure μ]
    (hci : conditional_independence_over ambient m m₁ m₂ μ)
    {f : Ω → ℝ} (hf : @Measurable Ω ℝ m₁ inferInstance f)
    (hfint : MeasureTheory.Integrable f μ) {V : Set Ω}
    (hV : @MeasurableSet Ω m₂ V) :
    (∫ ω in V, f ω ∂μ) =
      ∫ ω, MeasureTheory.condExp (m := m) μ f ω *
        MeasureTheory.condExp (m := m) μ (V.indicator (fun _ => (1 : ℝ))) ω ∂μ := by
  rcases hci with ⟨hm, hm₁, hm₂, hfactor⟩
  let iV : Ω → ℝ := V.indicator (fun _ => (1 : ℝ))
  let q : Ω → ℝ := MeasureTheory.condExp (m := m) μ iV
  have hVamb : @MeasurableSet Ω ambient V := hm₂ V hV
  have hiVint : MeasureTheory.Integrable iV μ := by
    simpa [iV] using (MeasureTheory.integrable_const (1 : ℝ)).indicator hVamb
  have hqint : MeasureTheory.Integrable q μ := by
    simpa [q] using (MeasureTheory.integrable_condExp :
      MeasureTheory.Integrable (MeasureTheory.condExp (m := m) μ iV) μ)
  have hqsm : @MeasureTheory.StronglyMeasurable Ω ℝ inferInstance m q := by
    simpa [q] using (MeasureTheory.stronglyMeasurable_condExp (μ := μ) (m := m))
  have hqnonneg : 0 ≤ᵐ[μ] q := by
    have hiVnonneg : 0 ≤ᵐ[μ] iV := Filter.Eventually.of_forall (by
      intro ω
      by_cases hω : ω ∈ V <;> simp [iV, hω])
    simpa [q] using MeasureTheory.condExp_nonneg (μ := μ) (m := m) hiVnonneg
  have hqle : q ≤ᵐ[μ] fun _ => (1 : ℝ) := by
    have hiVle : iV ≤ᵐ[μ] fun _ => (1 : ℝ) := Filter.Eventually.of_forall (by
      intro ω
      by_cases hω : ω ∈ V <;> simp [iV, hω])
    have hmono := MeasureTheory.condExp_mono (m := m) hiVint
      (MeasureTheory.integrable_const (1 : ℝ)) hiVle
    simpa [q, MeasureTheory.condExp_const hm] using hmono
  have hqnorm : ∀ᵐ ω ∂μ, ‖q ω‖ ≤ (1 : ℝ) := by
    filter_upwards [hqnonneg, hqle] with ω h0 h1
    simpa [Real.norm_eq_abs, abs_of_nonneg h0] using h1
  have hreal : ∀ U : Set Ω, @MeasurableSet Ω m₁ U →
      μ.real (U ∩ V) = ∫ ω in U, q ω ∂μ := by
    intro U hU
    have hUamb : @MeasurableSet Ω ambient U := hm₁ U hU
    let iU : Ω → ℝ := U.indicator (fun _ => (1 : ℝ))
    have hiUint : MeasureTheory.Integrable iU μ := by
      simpa [iU] using (MeasureTheory.integrable_const (1 : ℝ)).indicator hUamb
    have hpull := bounded_conditional_expectation_mul μ hm hqsm hiUint 1 hqnorm
    have hpull' : MeasureTheory.condExp (m := m) μ (iU * q) =ᵐ[μ]
        MeasureTheory.condExp (m := m) μ iU * q := by
      have hleft : iU * q = q * iU := by
        ext ω
        exact mul_comm _ _
      have hright : MeasureTheory.condExp (m := m) μ iU * q =
          q * MeasureTheory.condExp (m := m) μ iU := by
        ext ω
        exact mul_comm _ _
      rw [hleft, hright]
      exact hpull
    have hind := hfactor U V hU hV
    have hSamb : @MeasurableSet Ω ambient (U ∩ V) := hUamb.inter hVamb
    calc
      μ.real (U ∩ V) =
          ∫ ω, MeasureTheory.condExp (m := m) μ
            ((U ∩ V).indicator (fun _ => (1 : ℝ))) ω ∂μ := by
            rw [MeasureTheory.integral_condExp hm,
              MeasureTheory.integral_indicator hSamb, MeasureTheory.setIntegral_const]
            simp
      _ = ∫ ω, (MeasureTheory.condExp (m := m) μ iU * q) ω ∂μ := by
            exact MeasureTheory.integral_congr_ae (by simpa [iU, iV, q] using hind)
      _ = ∫ ω, MeasureTheory.condExp (m := m) μ (iU * q) ω ∂μ :=
        MeasureTheory.integral_congr_ae hpull'.symm
      _ = ∫ ω, (iU * q) ω ∂μ := MeasureTheory.integral_condExp hm
      _ = ∫ ω in U, q ω ∂μ := by
        have hfun : iU * q = U.indicator q := by
          ext ω
          by_cases hω : ω ∈ U <;> simp [iU, hω]
        rw [hfun, MeasureTheory.integral_indicator hUamb]
  have hsimple : ∀ s : @MeasureTheory.SimpleFunc Ω m₁ ℝ,
      (∫ ω in V, s ω ∂μ) = ∫ ω, s ω * q ω ∂μ := by
    intro s
    apply @MeasureTheory.SimpleFunc.induction _ _ m₁ _ (fun s =>
      (∫ ω in V, s ω ∂μ) = ∫ ω, s ω * q ω ∂μ)
      (fun a U hU => ?_) (fun s₁ s₂ _ hs₁ hs₂ => ?_) s
    · have hUamb : @MeasurableSet Ω ambient U := hm₁ U hU
      simp only [MeasureTheory.SimpleFunc.const_zero, MeasureTheory.SimpleFunc.coe_piecewise,
        MeasureTheory.SimpleFunc.coe_const, MeasureTheory.SimpleFunc.coe_zero,
        Set.piecewise_eq_indicator]
      rw [MeasureTheory.setIntegral_indicator hUamb]
      change (∫ _ in V ∩ U, (a : ℝ) ∂μ) = _
      rw [MeasureTheory.setIntegral_const]
      rw [show V ∩ U = U ∩ V from Set.inter_comm _ _]
      rw [hreal U hU]
      have hfun : (fun ω => U.indicator (Function.const Ω a) ω * q ω) =
          U.indicator (fun ω => a * q ω) := by
        ext ω
        by_cases hω : ω ∈ U <;> simp [hω]
      rw [hfun, MeasureTheory.integral_indicator hUamb]
      have hsmul := MeasureTheory.integral_smul (μ := μ.restrict U) a q
      simpa [smul_eq_mul, mul_comm] using hsmul.symm
    · have hs₁int : MeasureTheory.Integrable (s₁ : Ω → ℝ) μ := by
        obtain ⟨C, hC⟩ := @MeasureTheory.SimpleFunc.exists_forall_norm_le _ _ m₁ _ s₁
        exact (MeasureTheory.integrable_const C).mono'
          (s₁.stronglyMeasurable.mono hm₁).aestronglyMeasurable
          (Filter.Eventually.of_forall hC)
      have hs₂int : MeasureTheory.Integrable (s₂ : Ω → ℝ) μ := by
        obtain ⟨C, hC⟩ := @MeasureTheory.SimpleFunc.exists_forall_norm_le _ _ m₁ _ s₂
        exact (MeasureTheory.integrable_const C).mono'
          (s₂.stronglyMeasurable.mono hm₁).aestronglyMeasurable
          (Filter.Eventually.of_forall hC)
      have hs₁qint : MeasureTheory.Integrable (fun ω => s₁ ω * q ω) μ :=
        hs₁int.mul_bdd (hqsm.mono hm).aestronglyMeasurable hqnorm
      have hs₂qint : MeasureTheory.Integrable (fun ω => s₂ ω * q ω) μ :=
        hs₂int.mul_bdd (hqsm.mono hm).aestronglyMeasurable hqnorm
      calc
        (∫ ω in V, (s₁ + s₂) ω ∂μ) =
            (∫ ω in V, s₁ ω ∂μ) + ∫ ω in V, s₂ ω ∂μ := by
              change (∫ ω in V, s₁ ω + s₂ ω ∂μ) = _
              exact MeasureTheory.integral_add hs₁int.integrableOn hs₂int.integrableOn
        _ = (∫ ω, s₁ ω * q ω ∂μ) + ∫ ω, s₂ ω * q ω ∂μ := by rw [hs₁, hs₂]
        _ = ∫ ω, (s₁ ω * q ω + s₂ ω * q ω) ∂μ :=
          (MeasureTheory.integral_add hs₁qint hs₂qint).symm
        _ = ∫ ω, (s₁ + s₂) ω * q ω ∂μ := by
          congr 1
          funext ω
          simp [add_mul]
  have hfsm : @MeasureTheory.StronglyMeasurable Ω ℝ inferInstance m₁ f := hf.stronglyMeasurable
  let fseq : ℕ → @MeasureTheory.SimpleFunc Ω m₁ ℝ := fun n =>
    @MeasureTheory.SimpleFunc.approxOn ℝ Ω _ _ _ m₁ _ hf
      (Set.range f ∪ {0}) 0 (by simp) inferInstance n
  let fseqA : ℕ → @MeasureTheory.SimpleFunc Ω ambient ℝ := fun n =>
    @MeasureTheory.SimpleFunc.approxOn ℝ Ω _ _ _ ambient _ (hf.mono hm₁ le_rfl)
      (Set.range f ∪ {0}) 0 (by simp) inferInstance n
  have hfseq_coe : ∀ n ω, fseq n ω = fseqA n ω := by
    intro n ω
    rfl
  have hfseqint : ∀ n, MeasureTheory.Integrable (fseq n : Ω → ℝ) μ := by
    intro n
    obtain ⟨C, hC⟩ := @MeasureTheory.SimpleFunc.exists_forall_norm_le _ _ m₁ _ (fseq n)
    exact (MeasureTheory.integrable_const C).mono'
      ((fseq n).stronglyMeasurable.mono hm₁).aestronglyMeasurable
      (Filter.Eventually.of_forall hC)
  have hL1 : Filter.Tendsto
      (fun n => ∫⁻ ω, ‖fseq n ω - f ω‖ₑ ∂μ) Filter.atTop (nhds 0) := by
    have hL1A :=
      (@MeasureTheory.SimpleFunc.tendsto_approxOn_range_L1_enorm Ω ℝ ambient _ _ _
        f μ inferInstance (hf.mono hm₁ le_rfl) hfint)
    simpa only [hfseq_coe] using hL1A
  have hleft := MeasureTheory.tendsto_setIntegral_of_L1 (μ := μ) f
    (hfsm.mono hm₁).aestronglyMeasurable (F := fun n ω => fseq n ω) (l := Filter.atTop)
    (Filter.Eventually.of_forall hfseqint) hL1 V
  have hfqint : MeasureTheory.Integrable (fun ω => f ω * q ω) μ :=
    hfint.mul_bdd (hqsm.mono hm).aestronglyMeasurable hqnorm
  have hfseqqint : ∀ n, MeasureTheory.Integrable (fun ω => fseq n ω * q ω) μ :=
    fun n => (hfseqint n).mul_bdd (hqsm.mono hm).aestronglyMeasurable hqnorm
  have hweightedL1 : Filter.Tendsto
      (fun n => ∫⁻ ω, ‖fseq n ω * q ω - f ω * q ω‖ₑ ∂μ)
      Filter.atTop (nhds 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL1
      (fun _ => zero_le) (fun n => MeasureTheory.lintegral_mono_ae
        (hqnorm.mono (fun ω hq => by
          rw [← sub_mul, enorm_mul]
          have he : ‖q ω‖ₑ ≤ (1 : ENNReal) := by
            simpa [← ofReal_norm] using ENNReal.ofReal_le_ofReal hq
          simpa using mul_le_mul_left' he ‖fseq n ω - f ω‖ₑ)))
  have hright := MeasureTheory.tendsto_integral_of_L1 (fun ω => f ω * q ω)
    hfqint.1 (μ := μ) (F := fun n ω => fseq n ω * q ω) (l := Filter.atTop)
    (Filter.Eventually.of_forall hfseqqint) hweightedL1
  have happrox : (∫ ω in V, f ω ∂μ) = ∫ ω, f ω * q ω ∂μ := by
    exact tendsto_nhds_unique hleft
      (hright.congr' (Filter.Eventually.of_forall (fun n => (hsimple (fseq n)).symm)))
  have hpull := bounded_conditional_expectation_mul μ hm hqsm hfint 1 hqnorm
  calc
    (∫ ω in V, f ω ∂μ) = ∫ ω, f ω * q ω ∂μ := happrox
    _ = ∫ ω, q ω * f ω ∂μ := by
      congr 1
      funext ω
      exact mul_comm _ _
    _ = ∫ ω, MeasureTheory.condExp (m := m) μ (q * f) ω ∂μ :=
      (MeasureTheory.integral_condExp hm).symm
    _ = ∫ ω, (q * MeasureTheory.condExp (m := m) μ f) ω ∂μ :=
      MeasureTheory.integral_congr_ae hpull
    _ = ∫ ω, MeasureTheory.condExp (m := m) μ f ω * q ω ∂μ := by
      congr 1
      funext ω
      exact mul_comm _ _
    _ = ∫ ω, MeasureTheory.condExp (m := m) μ f ω *
        MeasureTheory.condExp (m := m) μ (V.indicator (fun _ => (1 : ℝ))) ω ∂μ := by
      rfl

@[blueprint "lem:parent-common-at-level-equivalence"
  (statement := /-- For every level $j$, the parent-class relation of a hierarchical two-point bandit is an equivalence relation on the action set. -/)
  (proof := /-- At the first level, the defining disjunction in \cref{def:hierarchical-two-point-bandit} makes every pair of actions parent-equivalent. At a later level $j$, the same definition identifies parent-equivalence with common ancestry at the unique predecessor level $j-1$. Reflexivity and symmetry follow immediately, while transitivity uses uniqueness of that predecessor and the assumed equivalence of common ancestry at each level. -/)
  (title := /-- Equivalence of parent classes -/)
  (latexEnv := "lemma")]
lemma parent_common_at_level_equivalence
    (M : hierarchical_two_point_bandit Action Node Ω) (j : Fin M.depth) :
    Equivalence (M.parentCommonAtLevel j) := by
  constructor
  · intro a
    rw [M.parentCommonAtLevel_iff]
    by_cases hj : j.val = 0
    · exact Or.inl hj
    · right
      let i : Fin M.depth := ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩
      refine ⟨i, ?_, (M.commonAtLevel_equivalence i).refl a⟩
      simp [i, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj)]
  · intro a b hab
    rw [M.parentCommonAtLevel_iff] at hab ⊢
    rcases hab with hj | ⟨i, hji, hab⟩
    · exact Or.inl hj
    · exact Or.inr ⟨i, hji, (M.commonAtLevel_equivalence i).symm hab⟩
  · intro a b c hab hbc
    rw [M.parentCommonAtLevel_iff] at hab hbc ⊢
    rcases hab with hj | ⟨i, hji, hab⟩
    · exact Or.inl hj
    rcases hbc with hj | ⟨k, hjk, hbc⟩
    · exact Or.inl hj
    right
    have hik : i = k := Fin.ext (by omega)
    subst k
    exact ⟨i, hji, (M.commonAtLevel_equivalence i).trans hab hbc⟩

@[blueprint "lem:two-point-sampling-density-second-marginal"
  (statement := /-- For every round $t$, outcome $\omega$, and action $b$, summing the joint sampling density over the first action and sampled level gives the run distribution at $b$:
  \[
  \sum_j\sum_a d_t(\omega,a,j,b)=p_t(\omega,b).
  \] -/)
  (proof := /-- Fix a level $j$. By \cref{lem:parent-common-at-level-equivalence}, the actions parent-equivalent to $b$ form one equivalence class. If $p_t(b)=0$, every joint-density term ending at $b$ vanishes. Otherwise the mass of the parent class of $b$ is positive. For every first action $a$ in this class, equivalence identifies its normalizing parent mass with that of $b$. Summing the density over $a$ therefore cancels this common normalizer and gives $p_t(b)\delta_j$. Summing over $j$ and using $\sum_j\delta_j=1$ proves the formula. -/)
  (title := /-- Second-action marginal of the sampling density -/)
  (latexEnv := "lemma")]
lemma two_point_sampling_density_second_marginal
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M)
    (t : ℕ) (ω : Ω) (b : Action) :
    (∑ j, ∑ a, run.samplingDensity t ω a j b) = run.distribution t ω b := by
  classical
  let p : Action → ℝ := run.distribution t ω
  have hp_nonneg : ∀ a, 0 ≤ p a := by
    intro a
    exact (run.distribution_mem t ω).1 a
  have hlevel : ∀ j : Fin M.depth,
      (∑ a, run.samplingDensity t ω a j b) = p b * M.delta j := by
    intro j
    let P : Action → Action → Prop := M.parentCommonAtLevel j
    letI (a x : Action) : Decidable (P a x) := M.parentCommonAtLevel_decidable j a x
    let D : Action → ℝ := fun a => ∑ x, if P a x then p x else 0
    have hP : Equivalence P := parent_common_at_level_equivalence M j
    by_cases hb : p b = 0
    · simp_rw [run.samplingDensity_formula]
      simp [p, hb]
    have hpb : 0 < p b := lt_of_le_of_ne (hp_nonneg b) (Ne.symm hb)
    have hDb_pos : 0 < D b := by
      apply lt_of_lt_of_le hpb
      calc
        p b = if P b b then p b else 0 := by simp [hP.refl b]
        _ ≤ ∑ x, if P b x then p x else 0 := Finset.single_le_sum
          (f := fun x => if P b x then p x else 0)
          (fun x _ => by
            by_cases hbx : P b x
            · simpa [hbx] using hp_nonneg x
            · simp [hbx])
          (Finset.mem_univ b)
        _ = D b := rfl
    have hD_eq : ∀ a, P a b → D a = D b := by
      intro a hab
      apply Finset.sum_congr rfl
      intro x hx
      have hclass : P a x ↔ P b x := by
        constructor
        · intro hax
          exact hP.trans (hP.symm hab) hax
        · intro hbx
          exact hP.trans hab hbx
      simp [D, hclass]
    have hclass_sum : (∑ a, if P a b then p a else 0) = D b := by
      apply Finset.sum_congr rfl
      intro a ha
      have hs : P a b ↔ P b a := ⟨hP.symm, hP.symm⟩
      simp [D, hs]
    simp_rw [run.samplingDensity_formula]
    have halgebra : (∑ a, p a * M.delta j * if P a b then p b / D a else 0) =
        p b * M.delta j := by
      calc
        (∑ a, p a * M.delta j * if P a b then p b / D a else 0) =
            ∑ a, (if P a b then p a else 0) * (M.delta j * (p b / D b)) := by
              apply Finset.sum_congr rfl
              intro a ha
              by_cases hab : P a b
              · simp [hab, hD_eq a hab]
                ring
              · simp [hab]
        _ = (∑ a, if P a b then p a else 0) * (M.delta j * (p b / D b)) := by
          rw [Finset.sum_mul]
        _ = D b * (M.delta j * (p b / D b)) := by rw [hclass_sum]
        _ = p b * M.delta j := by
          field_simp [ne_of_gt hDb_pos]
    simpa only [p, P, D] using halgebra
  calc
    (∑ j, ∑ a, run.samplingDensity t ω a j b) = ∑ j, p b * M.delta j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hlevel j
    _ = p b * ∑ j, M.delta j := by rw [Finset.mul_sum]
    _ = p b := by rw [M.delta_total, mul_one]
    _ = run.distribution t ω b := rfl

@[blueprint "lem:two-point-sampling-density-integrable"
  (statement := /-- Every coordinate of the joint two-point sampling density is integrable with respect to the model probability measure. -/)
  (proof := /-- The density formula in \cref{def:two-point-ftrl-run} is history-measurable and nonnegative. By \cref{lem:two-point-sampling-density-second-marginal}, each coordinate is bounded above by the second-action marginal $p_t(b)$. This marginal is history-measurable, lies in $[0,1]$ because $p_t$ is a probability vector, and is therefore integrable under the finite probability measure. Domination gives integrability of the density coordinate. -/)
  (title := /-- Integrability of the joint sampling density -/)
  (latexEnv := "lemma")]
lemma two_point_sampling_density_integrable
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M)
    (t : ℕ) (a : Action) (j : Fin M.depth) (b : Action) :
    MeasureTheory.Integrable (fun ω => run.samplingDensity t ω a j b) M.measure := by
  classical
  letI := M.probability_measure
  rcases run.feedback_loss_conditional_independence t with ⟨hhist, _, _, _⟩
  have hp_nonneg : ∀ ω c, 0 ≤ run.distribution t ω c := by
    intro ω c
    exact (run.distribution_mem t ω).1 c
  have hd_nonneg : ∀ ω a' j' b', 0 ≤ run.samplingDensity t ω a' j' b' := by
    intro ω a' j' b'
    rw [run.samplingDensity_formula]
    by_cases hab : M.parentCommonAtLevel j' a' b'
    · simp only [hab, if_true]
      have hden : 0 ≤ ∑ c, @ite ℝ (M.parentCommonAtLevel j' a' c)
          (M.parentCommonAtLevel_decidable j' a' c) (run.distribution t ω c) 0 := by
        apply Finset.sum_nonneg
        intro c hc
        by_cases hac : M.parentCommonAtLevel j' a' c
        · simpa [hac] using hp_nonneg ω c
        · simp [hac]
      exact mul_nonneg (mul_nonneg (hp_nonneg ω a') (le_of_lt (M.delta_positive j')))
        (div_nonneg (hp_nonneg ω b') hden)
    · simp [hab]
  have hd_meas : @Measurable Ω ℝ (M.history t) inferInstance
      (fun ω => run.samplingDensity t ω a j b) := by
    simp_rw [run.samplingDensity_formula]
    have hden_meas : @Measurable Ω ℝ (M.history t) inferInstance
        (fun ω => ∑ c, @ite ℝ (M.parentCommonAtLevel j a c)
          (M.parentCommonAtLevel_decidable j a c) (run.distribution t ω c) 0) := by
      apply Finset.measurable_sum
      intro c hc
      by_cases hac : M.parentCommonAtLevel j a c
      · simp only [hac, if_true]
        exact run.distribution_measurable t c
      · simp [hac]
    by_cases hab : M.parentCommonAtLevel j a b
    · simp only [hab, if_true]
      exact ((run.distribution_measurable t a).mul measurable_const).mul
        ((run.distribution_measurable t b).div hden_meas)
    · simp [hab]
  have hp_meas : @Measurable Ω ℝ inferInstance inferInstance
      (fun ω => run.distribution t ω b) :=
    (run.distribution_measurable t b).mono hhist le_rfl
  have hp_int : MeasureTheory.Integrable (fun ω => run.distribution t ω b) M.measure := by
    apply (MeasureTheory.integrable_const (1 : ℝ)).mono' hp_meas.stronglyMeasurable.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      have hb := mem_Icc_of_mem_stdSimplex (run.distribution_mem t ω) b
      rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact hb.2)
  apply hp_int.mono' (hd_meas.mono hhist le_rfl).stronglyMeasurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hd_nonneg ω a j b)]
    have hinner : run.samplingDensity t ω a j b ≤
        ∑ a', run.samplingDensity t ω a' j b :=
      Finset.single_le_sum (f := fun a' => run.samplingDensity t ω a' j b)
        (fun a' _ => hd_nonneg ω a' j b) (Finset.mem_univ a)
    have houter : (∑ a', run.samplingDensity t ω a' j b) ≤
        ∑ j', ∑ a', run.samplingDensity t ω a' j' b :=
      Finset.single_le_sum
        (f := fun j' => ∑ a', run.samplingDensity t ω a' j' b)
        (fun j' _ => Finset.sum_nonneg (fun a' _ => hd_nonneg ω a' j' b))
        (Finset.mem_univ j)
    exact (hinner.trans houter).trans_eq
      (two_point_sampling_density_second_marginal M run t ω b))

@[blueprint "lem:conditional-mean-loss-ae"
  (statement := /-- For every round and action, the specified conditional mean loss is a version of the conditional expectation of that loss coordinate with respect to the pre-round history. -/)
  (proof := /-- The loss coordinate and the specified conditional mean are integrable by \\cref{def:hierarchical-two-point-bandit}. The latter is history-measurable, and its integral over every history-measurable event equals the integral of the loss coordinate. The history inclusion supplied by \\cref{def:two-point-ftrl-run} and uniqueness of conditional expectation give the asserted almost-everywhere identity. -/)
  (title := /-- Identification of the conditional mean loss -/)
  (latexEnv := "lemma")]
lemma conditional_mean_loss_ae
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M)
    (t : ℕ) (a : Action) :
    MeasureTheory.condExp (m := M.history t) M.measure (fun ω => M.loss t ω a) =ᵐ[M.measure]
      fun ω => M.conditionalMeanLoss t ω a := by
  letI := M.probability_measure
  rcases run.feedback_loss_conditional_independence t with ⟨hhist, _, _, _⟩
  symm
  apply MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hhist (M.loss_integrable t a)
  · intro s hs hfinite
    exact (M.conditionalMeanLoss_integrable t a).integrableOn
  · intro s hs hfinite
    exact (M.conditionalMeanLoss_spec t a s hs).symm
  · exact (M.conditionalMeanLoss_measurable t a).aestronglyMeasurable

@[blueprint "lem:first-action-loss-integral"
  (statement := /-- For every round $t$ and action $a$, the expected loss on the event that the first executed action is $a$ satisfies
  \[
  \int_{\{A_{t,1}=a\}} y_t(a)\,d\mathbb P
  =\int_\Omega p_t(a)\,\mathbb E[y_t(a)\mid\mathcal F_t],d\mathbb P.
  \] -/)
  (proof := /-- The event $\{A_{t,1}=a\}$ belongs to the current-and-future randomization sigma-algebra. By \\cref{def:two-point-ftrl-run}, its integral over every history-measurable set equals that of $p_t(a)$, so uniqueness of conditional expectation identifies its conditional probability with $p_t(a)$. Apply \\cref{lem:conditional-independence-over-integral-indicator} to the integrable loss coordinate and this event, and replace the two conditional expectations using the preceding identification and \\cref{lem:conditional-mean-loss-ae}. -/)
  (title := /-- Expected loss of a first-action atom -/)
  (latexEnv := "lemma")]
lemma first_action_loss_integral
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M)
    (t : ℕ) (a : Action) :
    (∫ ω in {ω | M.firstAction t ω = a}, M.loss t ω a ∂M.measure) =
      ∫ ω, run.distribution t ω a * M.conditionalMeanLoss t ω a ∂M.measure := by
  classical
  letI := M.probability_measure
  let V : Set Ω := {ω : Ω | M.firstAction t ω = a}
  have hVbase : @MeasurableSet Ω
      (MeasurableSpace.comap (fun ω : Ω => M.firstAction t ω) ⊤) V := by
    rw [MeasurableSpace.measurableSet_comap]
    refine ⟨{a}, by trivial, ?_⟩
    ext ω
    simp [V]
  have hbase_le : MeasurableSpace.comap (fun ω : Ω => M.firstAction t ω) ⊤ ≤
      (⨆ s : {s : ℕ // t ≤ s},
        MeasurableSpace.comap (fun ω : Ω => M.firstAction s.1 ω) ⊤ ⊔
          MeasurableSpace.comap (fun ω : Ω => M.sampledLevel s.1 ω) ⊤ ⊔
            MeasurableSpace.comap (fun ω : Ω => M.secondAction s.1 ω) ⊤) := by
    calc
      MeasurableSpace.comap (fun ω : Ω => M.firstAction t ω) ⊤ ≤
          MeasurableSpace.comap (fun ω : Ω => M.firstAction t ω) ⊤ ⊔
            MeasurableSpace.comap (fun ω : Ω => M.sampledLevel t ω) ⊤ := le_sup_left
      _ ≤ (MeasurableSpace.comap (fun ω : Ω => M.firstAction t ω) ⊤ ⊔
            MeasurableSpace.comap (fun ω : Ω => M.sampledLevel t ω) ⊤) ⊔
          MeasurableSpace.comap (fun ω : Ω => M.secondAction t ω) ⊤ := le_sup_left
      _ ≤ _ := by
        simpa using le_iSup (fun s : {s : ℕ // t ≤ s} =>
          MeasurableSpace.comap (fun ω : Ω => M.firstAction s.1 ω) ⊤ ⊔
            MeasurableSpace.comap (fun ω : Ω => M.sampledLevel s.1 ω) ⊤ ⊔
              MeasurableSpace.comap (fun ω : Ω => M.secondAction s.1 ω) ⊤) ⟨t, le_rfl⟩
  have hV : @MeasurableSet Ω
      (⨆ s : {s : ℕ // t ≤ s},
        MeasurableSpace.comap (fun ω : Ω => M.firstAction s.1 ω) ⊤ ⊔
          MeasurableSpace.comap (fun ω : Ω => M.sampledLevel s.1 ω) ⊤ ⊔
            MeasurableSpace.comap (fun ω : Ω => M.secondAction s.1 ω) ⊤) V :=
    hbase_le V hVbase
  have hci := run.feedback_loss_conditional_independence t
  rcases hci with ⟨hhist, hloss, hrandom, hfactor⟩
  have hVamb : @MeasurableSet Ω inferInstance V := hrandom V hV
  let iV : Ω → ℝ := V.indicator (fun _ => (1 : ℝ))
  have hiVint : MeasureTheory.Integrable iV M.measure := by
    simpa [iV] using (MeasureTheory.integrable_const (1 : ℝ)).indicator hVamb
  have hpmeas : @Measurable Ω ℝ (M.history t) inferInstance
      (fun ω => run.distribution t ω a) := run.distribution_measurable t a
  have hpint : MeasureTheory.Integrable (fun ω => run.distribution t ω a) M.measure := by
    apply (MeasureTheory.integrable_const (1 : ℝ)).mono'
      ((hpmeas.mono hhist le_rfl).stronglyMeasurable.aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun ω => by
      have ha := mem_Icc_of_mem_stdSimplex (run.distribution_mem t ω) a
      rw [Real.norm_eq_abs, abs_of_nonneg ha.1]
      exact ha.2)
  have hprob : MeasureTheory.condExp (m := M.history t) M.measure iV =ᵐ[M.measure]
      fun ω => run.distribution t ω a := by
    symm
    apply MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hhist hiVint
    · intro s hs hfinite
      exact hpint.integrableOn
    · intro s hs hfinite
      rw [show iV = fun ω => if M.firstAction t ω = a then (1 : ℝ) else 0 by
        funext ω
        by_cases hω : M.firstAction t ω = a <;> simp [iV, V, hω]]
      exact (run.first_action_conditional_law t a s hs).symm
    · exact hpmeas.aestronglyMeasurable
  have hfloss : @Measurable Ω ℝ
      (MeasurableSpace.comap (fun ω => M.loss t ω) inferInstance) inferInstance
      (fun ω => M.loss t ω a) :=
    (measurable_pi_apply a).comp (comap_measurable (fun ω => M.loss t ω))
  have hind := conditional_independence_over_integral_indicator M.measure
    ⟨hhist, hloss, hrandom, hfactor⟩ hfloss (M.loss_integrable t a) hV
  have hmean := conditional_mean_loss_ae M run t a
  calc
    (∫ ω in {ω | M.firstAction t ω = a}, M.loss t ω a ∂M.measure) =
        ∫ ω, MeasureTheory.condExp (m := M.history t) M.measure
            (fun ω => M.loss t ω a) ω *
          MeasureTheory.condExp (m := M.history t) M.measure iV ω ∂M.measure := by
            simpa [V, iV] using hind
    _ = ∫ ω, M.conditionalMeanLoss t ω a * run.distribution t ω a ∂M.measure :=
      MeasureTheory.integral_congr_ae (hmean.mul hprob)
    _ = ∫ ω, run.distribution t ω a * M.conditionalMeanLoss t ω a ∂M.measure := by
      congr 1
      funext ω
      exact mul_comm _ _

@[blueprint "lem:feedback-atom-loss-integral"
  (statement := /-- For every round $t$, actions $a,b$, and level $j$, let $G_{a,j,b}=\{A_{t,1}=a,J_t=j,A_{t,2}=b\}$. Then
  \[
  \int_{G_{a,j,b}} y_t(b)\,d\mathbb P
  =\int_\Omega d_t(a,j,b)\,\mathbb E[y_t(b)\mid\mathcal F_t],d\mathbb P.
  \] -/)
  (proof := /-- The atom $G_{a,j,b}$ is measurable in the current-and-future randomization sigma-algebra. Its eventwise sampling law from \\cref{def:two-point-ftrl-run}, together with the history measurability of the density formula and \\cref{lem:two-point-sampling-density-integrable}, identifies its conditional probability with $d_t(a,j,b)$. Apply \\cref{lem:conditional-independence-over-integral-indicator} to this atom and the integrable loss coordinate $y_t(b)$, then use \\cref{lem:conditional-mean-loss-ae} to identify the other conditional expectation. -/)
  (title := /-- Expected loss on a feedback atom -/)
  (latexEnv := "lemma")]
lemma feedback_atom_loss_integral
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M)
    (t : ℕ) (a : Action) (j : Fin M.depth) (b : Action) :
    (∫ ω in {ω | M.firstAction t ω = a ∧ M.sampledLevel t ω = j ∧
        M.secondAction t ω = b}, M.loss t ω b ∂M.measure) =
      ∫ ω, run.samplingDensity t ω a j b * M.conditionalMeanLoss t ω b ∂M.measure := by
  classical
  letI := M.probability_measure
  let A : Set Ω := {ω : Ω | M.firstAction t ω = a}
  let J : Set Ω := {ω : Ω | M.sampledLevel t ω = j}
  let B : Set Ω := {ω : Ω | M.secondAction t ω = b}
  let V : Set Ω := A ∩ J ∩ B
  have hcurrent_le :
      (MeasurableSpace.comap (fun ω : Ω => M.firstAction t ω) ⊤ ⊔
          MeasurableSpace.comap (fun ω : Ω => M.sampledLevel t ω) ⊤) ⊔
        MeasurableSpace.comap (fun ω : Ω => M.secondAction t ω) ⊤ ≤
      (⨆ s : {s : ℕ // t ≤ s},
        MeasurableSpace.comap (fun ω : Ω => M.firstAction s.1 ω) ⊤ ⊔
          MeasurableSpace.comap (fun ω : Ω => M.sampledLevel s.1 ω) ⊤ ⊔
            MeasurableSpace.comap (fun ω : Ω => M.secondAction s.1 ω) ⊤) := by
    simpa using le_iSup (fun s : {s : ℕ // t ≤ s} =>
      MeasurableSpace.comap (fun ω : Ω => M.firstAction s.1 ω) ⊤ ⊔
        MeasurableSpace.comap (fun ω : Ω => M.sampledLevel s.1 ω) ⊤ ⊔
          MeasurableSpace.comap (fun ω : Ω => M.secondAction s.1 ω) ⊤) ⟨t, le_rfl⟩
  have hA_base : @MeasurableSet Ω
      (MeasurableSpace.comap (fun ω : Ω => M.firstAction t ω) ⊤) A := by
    rw [MeasurableSpace.measurableSet_comap]
    refine ⟨{a}, by trivial, ?_⟩
    ext ω
    simp [A]
  have hJ_base : @MeasurableSet Ω
      (MeasurableSpace.comap (fun ω : Ω => M.sampledLevel t ω) ⊤) J := by
    rw [MeasurableSpace.measurableSet_comap]
    refine ⟨{j}, by trivial, ?_⟩
    ext ω
    simp [J]
  have hB_base : @MeasurableSet Ω
      (MeasurableSpace.comap (fun ω : Ω => M.secondAction t ω) ⊤) B := by
    rw [MeasurableSpace.measurableSet_comap]
    refine ⟨{b}, by trivial, ?_⟩
    ext ω
    simp [B]
  have hA_le := le_trans (le_trans le_sup_left le_sup_left) hcurrent_le
  have hJ_le := le_trans (le_trans le_sup_right le_sup_left) hcurrent_le
  have hB_le := le_trans le_sup_right hcurrent_le
  have hA : @MeasurableSet Ω
      (⨆ s : {s : ℕ // t ≤ s},
        MeasurableSpace.comap (fun ω : Ω => M.firstAction s.1 ω) ⊤ ⊔
          MeasurableSpace.comap (fun ω : Ω => M.sampledLevel s.1 ω) ⊤ ⊔
            MeasurableSpace.comap (fun ω : Ω => M.secondAction s.1 ω) ⊤) A := hA_le A hA_base
  have hJ : @MeasurableSet Ω
      (⨆ s : {s : ℕ // t ≤ s},
        MeasurableSpace.comap (fun ω : Ω => M.firstAction s.1 ω) ⊤ ⊔
          MeasurableSpace.comap (fun ω : Ω => M.sampledLevel s.1 ω) ⊤ ⊔
            MeasurableSpace.comap (fun ω : Ω => M.secondAction s.1 ω) ⊤) J := hJ_le J hJ_base
  have hB : @MeasurableSet Ω
      (⨆ s : {s : ℕ // t ≤ s},
        MeasurableSpace.comap (fun ω : Ω => M.firstAction s.1 ω) ⊤ ⊔
          MeasurableSpace.comap (fun ω : Ω => M.sampledLevel s.1 ω) ⊤ ⊔
            MeasurableSpace.comap (fun ω : Ω => M.secondAction s.1 ω) ⊤) B := hB_le B hB_base
  have hV : @MeasurableSet Ω
      (⨆ s : {s : ℕ // t ≤ s},
        MeasurableSpace.comap (fun ω : Ω => M.firstAction s.1 ω) ⊤ ⊔
          MeasurableSpace.comap (fun ω : Ω => M.sampledLevel s.1 ω) ⊤ ⊔
            MeasurableSpace.comap (fun ω : Ω => M.secondAction s.1 ω) ⊤) V := by
    exact hA.inter hJ |>.inter hB
  have hci := run.feedback_loss_conditional_independence t
  rcases hci with ⟨hhist, hloss, hrandom, hfactor⟩
  have hVamb : @MeasurableSet Ω inferInstance V := hrandom V hV
  let iV : Ω → ℝ := V.indicator (fun _ => (1 : ℝ))
  have hiVint : MeasureTheory.Integrable iV M.measure := by
    simpa [iV] using (MeasureTheory.integrable_const (1 : ℝ)).indicator hVamb
  have hdmeas : @Measurable Ω ℝ (M.history t) inferInstance
      (fun ω => run.samplingDensity t ω a j b) := by
    simp_rw [run.samplingDensity_formula]
    have hden_meas : @Measurable Ω ℝ (M.history t) inferInstance
        (fun ω => ∑ c, @ite ℝ (M.parentCommonAtLevel j a c)
          (M.parentCommonAtLevel_decidable j a c) (run.distribution t ω c) 0) := by
      apply Finset.measurable_sum
      intro c hc
      by_cases hac : M.parentCommonAtLevel j a c
      · simp only [hac, if_true]
        exact run.distribution_measurable t c
      · simp [hac]
    by_cases hab : M.parentCommonAtLevel j a b
    · simp only [hab, if_true]
      exact ((run.distribution_measurable t a).mul measurable_const).mul
        ((run.distribution_measurable t b).div hden_meas)
    · simp [hab]
  have hdint := two_point_sampling_density_integrable M run t a j b
  have hprob : MeasureTheory.condExp (m := M.history t) M.measure iV =ᵐ[M.measure]
      fun ω => run.samplingDensity t ω a j b := by
    symm
    apply MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hhist hiVint
    · intro s hs hfinite
      exact hdint.integrableOn
    · intro s hs hfinite
      rw [show iV = fun ω => if M.firstAction t ω = a ∧ M.sampledLevel t ω = j ∧
          M.secondAction t ω = b then (1 : ℝ) else 0 by
        funext ω
        by_cases haω : M.firstAction t ω = a <;>
          by_cases hjω : M.sampledLevel t ω = j <;>
            by_cases hbω : M.secondAction t ω = b <;>
              simp [iV, V, A, J, B, haω, hjω, hbω]]
      exact (run.feedback_conditional_law t a j b s hs).symm
    · exact hdmeas.aestronglyMeasurable
  have hfloss : @Measurable Ω ℝ
      (MeasurableSpace.comap (fun ω => M.loss t ω) inferInstance) inferInstance
      (fun ω => M.loss t ω b) :=
    (measurable_pi_apply b).comp (comap_measurable (fun ω => M.loss t ω))
  have hind := conditional_independence_over_integral_indicator M.measure
    ⟨hhist, hloss, hrandom, hfactor⟩ hfloss (M.loss_integrable t b) hV
  have hmean := conditional_mean_loss_ae M run t b
  calc
    (∫ ω in {ω | M.firstAction t ω = a ∧ M.sampledLevel t ω = j ∧
        M.secondAction t ω = b}, M.loss t ω b ∂M.measure) =
        ∫ ω, MeasureTheory.condExp (m := M.history t) M.measure
            (fun ω => M.loss t ω b) ω *
          MeasureTheory.condExp (m := M.history t) M.measure iV ω ∂M.measure := by
            have hset : {ω | M.firstAction t ω = a ∧ M.sampledLevel t ω = j ∧
                M.secondAction t ω = b} = V := by
              ext ω
              constructor
              · rintro ⟨haω, hjω, hbω⟩
                exact ⟨⟨haω, hjω⟩, hbω⟩
              · rintro ⟨⟨haω, hjω⟩, hbω⟩
                exact ⟨haω, hjω, hbω⟩
            rw [hset]
            exact hind
    _ = ∫ ω, M.conditionalMeanLoss t ω b * run.samplingDensity t ω a j b ∂M.measure :=
      MeasureTheory.integral_congr_ae (hmean.mul hprob)
    _ = ∫ ω, run.samplingDensity t ω a j b * M.conditionalMeanLoss t ω b ∂M.measure := by
      congr 1
      funext ω
      exact mul_comm _ _

@[blueprint "lem:first-executed-loss-expectation"
  (statement := /-- At every round $t$, the expected loss of the first executed action is
  \[
  \mathbb E[y_t(A_{t,1})]
  =\int_\Omega\sum_a p_t(a)\,\mathbb E[y_t(a)\mid\mathcal F_t],d\mathbb P.
  \] -/)
  (proof := /-- Partition the sample space by the finitely many first-action events. Each restricted loss is integrable, and \\cref{lem:first-action-loss-integral} evaluates its integral. Finite additivity of the integral then recombines these actionwise identities into the displayed sum. -/)
  (title := /-- Expected loss of the first executed action -/)
  (latexEnv := "lemma")]
lemma first_executed_loss_expectation
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M)
    (t : ℕ) :
    (∫ ω, M.loss t ω (M.firstAction t ω) ∂M.measure) =
      ∫ ω, ∑ a, run.distribution t ω a * M.conditionalMeanLoss t ω a ∂M.measure := by
  classical
  letI := M.probability_measure
  rcases run.feedback_loss_conditional_independence t with ⟨hhist, _, hrandom, _⟩
  have hbase_le : MeasurableSpace.comap (fun ω : Ω => M.firstAction t ω) ⊤ ≤
      (⨆ s : {s : ℕ // t ≤ s},
        MeasurableSpace.comap (fun ω : Ω => M.firstAction s.1 ω) ⊤ ⊔
          MeasurableSpace.comap (fun ω : Ω => M.sampledLevel s.1 ω) ⊤ ⊔
            MeasurableSpace.comap (fun ω : Ω => M.secondAction s.1 ω) ⊤) := by
    calc
      MeasurableSpace.comap (fun ω : Ω => M.firstAction t ω) ⊤ ≤
          MeasurableSpace.comap (fun ω : Ω => M.firstAction t ω) ⊤ ⊔
            MeasurableSpace.comap (fun ω : Ω => M.sampledLevel t ω) ⊤ := le_sup_left
      _ ≤ (MeasurableSpace.comap (fun ω : Ω => M.firstAction t ω) ⊤ ⊔
            MeasurableSpace.comap (fun ω : Ω => M.sampledLevel t ω) ⊤) ⊔
          MeasurableSpace.comap (fun ω : Ω => M.secondAction t ω) ⊤ := le_sup_left
      _ ≤ _ := by
        simpa using le_iSup (fun s : {s : ℕ // t ≤ s} =>
          MeasurableSpace.comap (fun ω : Ω => M.firstAction s.1 ω) ⊤ ⊔
            MeasurableSpace.comap (fun ω : Ω => M.sampledLevel s.1 ω) ⊤ ⊔
              MeasurableSpace.comap (fun ω : Ω => M.secondAction s.1 ω) ⊤) ⟨t, le_rfl⟩
  let V : Action → Set Ω := fun a => {ω : Ω | M.firstAction t ω = a}
  have hVamb : ∀ a, @MeasurableSet Ω inferInstance (V a) := by
    intro a
    apply hrandom
    apply hbase_le
    rw [MeasurableSpace.measurableSet_comap]
    refine ⟨{a}, by trivial, ?_⟩
    ext ω
    simp [V]
  have hterm_int : ∀ a, MeasureTheory.Integrable
      (fun ω => if M.firstAction t ω = a then M.loss t ω a else 0) M.measure := by
    intro a
    have hfun : (fun ω => if M.firstAction t ω = a then M.loss t ω a else 0) =
        (V a).indicator (fun ω => M.loss t ω a) := by
      funext ω
      by_cases hω : M.firstAction t ω = a <;> simp [V, hω]
    rw [hfun]
    exact (M.loss_integrable t a).indicator (hVamb a)
  have hprod_int : ∀ a, MeasureTheory.Integrable
      (fun ω => run.distribution t ω a * M.conditionalMeanLoss t ω a) M.measure := by
    intro a
    apply (M.conditionalMeanLoss_integrable t a).bdd_mul
      (((run.distribution_measurable t a).mono hhist le_rfl).stronglyMeasurable.aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun ω => by
      have ha := mem_Icc_of_mem_stdSimplex (run.distribution_mem t ω) a
      rw [Real.norm_eq_abs, abs_of_nonneg ha.1]
      exact ha.2)
  have hpartition : (fun ω => M.loss t ω (M.firstAction t ω)) =
      fun ω => ∑ a, if M.firstAction t ω = a then M.loss t ω a else 0 := by
    funext ω
    classical
    simp
  calc
    (∫ ω, M.loss t ω (M.firstAction t ω) ∂M.measure) =
        ∫ ω, ∑ a, if M.firstAction t ω = a then M.loss t ω a else 0 ∂M.measure := by
          rw [hpartition]
    _ = ∑ a, ∫ ω, if M.firstAction t ω = a then M.loss t ω a else 0 ∂M.measure := by
      simpa using MeasureTheory.integral_finsetSum (μ := M.measure) Finset.univ
        (fun a ha => hterm_int a)
    _ = ∑ a, ∫ ω in V a, M.loss t ω a ∂M.measure := by
      apply Finset.sum_congr rfl
      intro a ha
      calc
        (∫ ω, if M.firstAction t ω = a then M.loss t ω a else 0 ∂M.measure) =
            ∫ ω, (V a).indicator (fun ω => M.loss t ω a) ω ∂M.measure := by
              congr 1
              funext ω
              by_cases hω : M.firstAction t ω = a <;> simp [V, hω]
        _ = ∫ ω in V a, M.loss t ω a ∂M.measure :=
          MeasureTheory.integral_indicator (hVamb a)
    _ = ∑ a, ∫ ω, run.distribution t ω a * M.conditionalMeanLoss t ω a ∂M.measure := by
      apply Finset.sum_congr rfl
      intro a ha
      simpa [V] using first_action_loss_integral M run t a
    _ = ∫ ω, ∑ a, run.distribution t ω a * M.conditionalMeanLoss t ω a ∂M.measure := by
      symm
      simpa using MeasureTheory.integral_finsetSum (μ := M.measure) Finset.univ
        (fun a ha => hprod_int a)

@[blueprint "lem:second-executed-loss-expectation"
  (statement := /-- At every round $t$, the expected loss of the second executed action is
  \[
  \mathbb E[y_t(A_{t,2})]
  =\int_\Omega\sum_b p_t(b)\,\mathbb E[y_t(b)\mid\mathcal F_t],d\mathbb P.
  \] -/)
  (proof := /-- Partition the sample space into the finitely many feedback atoms $G_{a,j,b}$. Each restricted loss is integrable, and \\cref{lem:feedback-atom-loss-integral} evaluates its integral as the density-weighted conditional mean loss. By \\cref{lem:two-point-sampling-density-integrable}, each density coordinate is measurable and integrable; it is also bounded by its nonnegative second-action marginal, so the density-weighted conditional mean losses are integrable and finite additivity applies. Finally \\cref{lem:two-point-sampling-density-second-marginal} reduces the sum over $a$ and $j$ to $p_t(b)$. -/)
  (title := /-- Expected loss of the second executed action -/)
  (latexEnv := "lemma")]
lemma second_executed_loss_expectation
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M)
    (t : ℕ) :
    (∫ ω, M.loss t ω (M.secondAction t ω) ∂M.measure) =
      ∫ ω, ∑ b, run.distribution t ω b * M.conditionalMeanLoss t ω b ∂M.measure := by
  classical
  letI := M.probability_measure
  rcases run.feedback_loss_conditional_independence t with ⟨_, _, hrandom, _⟩
  have hcurrent_le :
      (MeasurableSpace.comap (fun ω : Ω => M.firstAction t ω) ⊤ ⊔
          MeasurableSpace.comap (fun ω : Ω => M.sampledLevel t ω) ⊤) ⊔
        MeasurableSpace.comap (fun ω : Ω => M.secondAction t ω) ⊤ ≤
      (⨆ s : {s : ℕ // t ≤ s},
        MeasurableSpace.comap (fun ω : Ω => M.firstAction s.1 ω) ⊤ ⊔
          MeasurableSpace.comap (fun ω : Ω => M.sampledLevel s.1 ω) ⊤ ⊔
            MeasurableSpace.comap (fun ω : Ω => M.secondAction s.1 ω) ⊤) := by
    simpa using le_iSup (fun s : {s : ℕ // t ≤ s} =>
      MeasurableSpace.comap (fun ω : Ω => M.firstAction s.1 ω) ⊤ ⊔
        MeasurableSpace.comap (fun ω : Ω => M.sampledLevel s.1 ω) ⊤ ⊔
          MeasurableSpace.comap (fun ω : Ω => M.secondAction s.1 ω) ⊤) ⟨t, le_rfl⟩
  have hA_le := le_trans (le_trans le_sup_left le_sup_left) hcurrent_le
  have hJ_le := le_trans (le_trans le_sup_right le_sup_left) hcurrent_le
  have hB_le := le_trans le_sup_right hcurrent_le
  have hfirst_meas : @Measurable Ω Action inferInstance ⊤ (fun ω => M.firstAction t ω) :=
    (comap_measurable (fun ω : Ω => M.firstAction t ω)).mono (hA_le.trans hrandom) le_rfl
  have hlevel_meas : @Measurable Ω (Fin M.depth) inferInstance ⊤
      (fun ω => M.sampledLevel t ω) :=
    (comap_measurable (fun ω : Ω => M.sampledLevel t ω)).mono (hJ_le.trans hrandom) le_rfl
  have hsecond_meas : @Measurable Ω Action inferInstance ⊤ (fun ω => M.secondAction t ω) :=
    (comap_measurable (fun ω : Ω => M.secondAction t ω)).mono (hB_le.trans hrandom) le_rfl
  have hAset : ∀ a, MeasurableSet {ω : Ω | M.firstAction t ω = a} := by
    intro a
    change MeasurableSet ((fun ω : Ω => M.firstAction t ω) ⁻¹' ({a} : Set Action))
    exact hfirst_meas (by trivial)
  have hJset : ∀ j, MeasurableSet {ω : Ω | M.sampledLevel t ω = j} := by
    intro j
    change MeasurableSet ((fun ω : Ω => M.sampledLevel t ω) ⁻¹' ({j} : Set (Fin M.depth)))
    exact hlevel_meas (by trivial)
  have hBset : ∀ b, MeasurableSet {ω : Ω | M.secondAction t ω = b} := by
    intro b
    change MeasurableSet ((fun ω : Ω => M.secondAction t ω) ⁻¹' ({b} : Set Action))
    exact hsecond_meas (by trivial)
  let G : Action → Fin M.depth → Action → Set Ω := fun a j b =>
    {ω | M.firstAction t ω = a ∧ M.sampledLevel t ω = j ∧ M.secondAction t ω = b}
  have hGamb : ∀ a j b, MeasurableSet (G a j b) := by
    intro a j b
    have hleft := (hAset a).inter (hJset j) |>.inter (hBset b)
    have hset : G a j b = {ω : Ω | M.firstAction t ω = a} ∩
        {ω : Ω | M.sampledLevel t ω = j} ∩ {ω : Ω | M.secondAction t ω = b} := by
      ext ω
      constructor
      · rintro ⟨haω, hjω, hbω⟩
        exact ⟨⟨haω, hjω⟩, hbω⟩
      · rintro ⟨⟨haω, hjω⟩, hbω⟩
        exact ⟨haω, hjω, hbω⟩
    rw [hset]
    exact hleft
  have hterm_int : ∀ a j b, MeasureTheory.Integrable
      (fun ω => if ω ∈ G a j b then M.loss t ω b else 0) M.measure := by
    intro a j b
    have hfun : (fun ω => if ω ∈ G a j b then M.loss t ω b else 0) =
        (G a j b).indicator (fun ω => M.loss t ω b) := by
      funext ω
      by_cases hω : ω ∈ G a j b <;> simp [hω]
    rw [hfun]
    exact (M.loss_integrable t b).indicator (hGamb a j b)
  have hd_nonneg : ∀ ω a j b, 0 ≤ run.samplingDensity t ω a j b := by
    intro ω a j b
    rw [run.samplingDensity_formula]
    by_cases hab : M.parentCommonAtLevel j a b
    · simp only [hab, if_true]
      have hden : 0 ≤ ∑ c, @ite ℝ (M.parentCommonAtLevel j a c)
          (M.parentCommonAtLevel_decidable j a c) (run.distribution t ω c) 0 := by
        apply Finset.sum_nonneg
        intro c hc
        by_cases hac : M.parentCommonAtLevel j a c
        · simpa [hac] using (run.distribution_mem t ω).1 c
        · simp [hac]
      exact mul_nonneg (mul_nonneg ((run.distribution_mem t ω).1 a)
        (le_of_lt (M.delta_positive j))) (div_nonneg ((run.distribution_mem t ω).1 b) hden)
    · simp [hab]
  have hd_bound : ∀ ω a j b, ‖run.samplingDensity t ω a j b‖ ≤ (1 : ℝ) := by
    intro ω a j b
    rw [Real.norm_eq_abs, abs_of_nonneg (hd_nonneg ω a j b)]
    have hinner : run.samplingDensity t ω a j b ≤
        ∑ a', run.samplingDensity t ω a' j b :=
      Finset.single_le_sum (f := fun a' => run.samplingDensity t ω a' j b)
        (fun a' _ => hd_nonneg ω a' j b) (Finset.mem_univ a)
    have houter : (∑ a', run.samplingDensity t ω a' j b) ≤
        ∑ j', ∑ a', run.samplingDensity t ω a' j' b :=
      Finset.single_le_sum
        (f := fun j' => ∑ a', run.samplingDensity t ω a' j' b)
        (fun j' _ => Finset.sum_nonneg (fun a' _ => hd_nonneg ω a' j' b))
        (Finset.mem_univ j)
    exact ((hinner.trans houter).trans_eq
      (two_point_sampling_density_second_marginal M run t ω b)).trans
        (mem_Icc_of_mem_stdSimplex (run.distribution_mem t ω) b).2
  let term : (Action × (Fin M.depth × Action)) → Ω → ℝ := fun x ω =>
    if ω ∈ G x.2.2 x.2.1 x.1 then M.loss t ω x.1 else 0
  let weighted : (Action × (Fin M.depth × Action)) → Ω → ℝ := fun x ω =>
    run.samplingDensity t ω x.2.2 x.2.1 x.1 * M.conditionalMeanLoss t ω x.1
  have hterm_index_int : ∀ x, MeasureTheory.Integrable (term x) M.measure := by
    intro x
    exact hterm_int x.2.2 x.2.1 x.1
  have hweighted_index_int : ∀ x, MeasureTheory.Integrable (weighted x) M.measure := by
    intro x
    exact (M.conditionalMeanLoss_integrable t x.1).bdd_mul
      (two_point_sampling_density_integrable M run t x.2.2 x.2.1 x.1).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => hd_bound ω x.2.2 x.2.1 x.1))
  have hpartition : (fun ω => M.loss t ω (M.secondAction t ω)) =
      fun ω => ∑ x : Action × (Fin M.depth × Action), term x ω := by
    funext ω
    simp only [term, G]
    symm
    let x₀ : Action × (Fin M.depth × Action) :=
      (M.secondAction t ω, (M.sampledLevel t ω, M.firstAction t ω))
    have hoff : ∀ x ∈ (Finset.univ : Finset (Action × (Fin M.depth × Action))),
        x ≠ x₀ →
          (if M.firstAction t ω = x.2.2 ∧ M.sampledLevel t ω = x.2.1 ∧
              M.secondAction t ω = x.1 then M.loss t ω x.1 else 0) = 0 := by
      intro x hx hne
      split
      · rename_i hcond
        exfalso
        apply hne
        rcases hcond with ⟨ha, hj, hb⟩
        apply Prod.ext
        · exact hb.symm
        · apply Prod.ext
          · exact hj.symm
          · exact ha.symm
      · rfl
    have hnot : x₀ ∉ (Finset.univ : Finset (Action × (Fin M.depth × Action))) →
        (if M.firstAction t ω = x₀.2.2 ∧ M.sampledLevel t ω = x₀.2.1 ∧
          M.secondAction t ω = x₀.1 then M.loss t ω x₀.1 else 0) = 0 := by
      intro h
      exact (h (Finset.mem_univ _)).elim
    calc
      (∑ x : Action × (Fin M.depth × Action),
          if M.firstAction t ω = x.2.2 ∧ M.sampledLevel t ω = x.2.1 ∧
            M.secondAction t ω = x.1 then M.loss t ω x.1 else 0) =
          (if M.firstAction t ω = x₀.2.2 ∧ M.sampledLevel t ω = x₀.2.1 ∧
            M.secondAction t ω = x₀.1 then M.loss t ω x₀.1 else 0) :=
        Finset.sum_eq_single x₀ hoff hnot
      _ = M.loss t ω (M.secondAction t ω) := by simp [x₀]
  have hsum_density : ∀ ω,
      (∑ x : Action × (Fin M.depth × Action), weighted x ω) =
        ∑ b, run.distribution t ω b * M.conditionalMeanLoss t ω b := by
    intro ω
    simp_rw [weighted, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro b hb
    calc
      (∑ j, ∑ a, run.samplingDensity t ω a j b * M.conditionalMeanLoss t ω b) =
          (∑ j, ∑ a, run.samplingDensity t ω a j b) *
            M.conditionalMeanLoss t ω b := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro j hj
              rw [Finset.sum_mul]
      _ = run.distribution t ω b * M.conditionalMeanLoss t ω b := by
        rw [two_point_sampling_density_second_marginal M run t ω b]
  calc
    (∫ ω, M.loss t ω (M.secondAction t ω) ∂M.measure) =
        ∫ ω, ∑ x : Action × (Fin M.depth × Action), term x ω ∂M.measure := by
          rw [hpartition]
    _ = ∑ x : Action × (Fin M.depth × Action), ∫ ω, term x ω ∂M.measure := by
      simpa using MeasureTheory.integral_finsetSum (μ := M.measure) Finset.univ
        (fun x hx => hterm_index_int x)
    _ = ∑ x : Action × (Fin M.depth × Action), ∫ ω, weighted x ω ∂M.measure := by
      apply Finset.sum_congr rfl
      intro x hx
      calc
        (∫ ω, term x ω ∂M.measure) =
            ∫ ω in G x.2.2 x.2.1 x.1, M.loss t ω x.1 ∂M.measure := by
              calc
                (∫ ω, term x ω ∂M.measure) =
                    ∫ ω, (G x.2.2 x.2.1 x.1).indicator
                      (fun ω => M.loss t ω x.1) ω ∂M.measure := by
                        congr 1
                        funext ω
                        by_cases hω : ω ∈ G x.2.2 x.2.1 x.1 <;>
                          simp [term, hω]
                _ = _ := MeasureTheory.integral_indicator (hGamb x.2.2 x.2.1 x.1)
        _ = ∫ ω, weighted x ω ∂M.measure := by
          simpa [G, weighted] using
            feedback_atom_loss_integral M run t x.2.2 x.2.1 x.1
    _ = ∫ ω, ∑ x : Action × (Fin M.depth × Action), weighted x ω ∂M.measure := by
      symm
      simpa using MeasureTheory.integral_finsetSum (μ := M.measure) Finset.univ
        (fun x hx => hweighted_index_int x)
    _ = ∫ ω, ∑ b, run.distribution t ω b * M.conditionalMeanLoss t ω b ∂M.measure :=
      MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (fun ω => hsum_density ω))

@[blueprint "lem:two-point-regret-reduction"
  (statement := /-- Let $M$ be a hierarchical two-point bandit, let $\rho$ be a two-point FTRL run on $M$, and let $T\in\mathbb N$. Then the two-point regret at horizon $T$ equals the regret of the first executed action:
  \[
  R_T^{(2)}=R_T^{(1)}.
  \] -/)
  (proof := /-- For every round $t$, \\cref{lem:first-executed-loss-expectation} and \\cref{lem:second-executed-loss-expectation} identify the expected losses of the first and second executed actions with the same integral $\int_\Omega\sum_a p_t(a)\mathbb E[y_t(a)\mid\mathcal F_t],d\mathbb P$. Hence their expected losses are equal. Integrability of both executed losses permits finite linearity of the integral over $t<T$; consequently the expected sum of their averages equals the expected sum of the first-action losses. Expanding \\cref{def:two-point-regret, def:first-action-regret} and subtracting the common fixed-action comparator proves the claim. -/)
  (title := /-- Reduction of two-point regret to first-action regret -/)
  (latexEnv := "lemma")]
lemma two_point_regret_reduction
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M) (T : ℕ) :
    two_point_regret M T = first_action_regret M T := by
  have hround : ∀ t,
      (∫ ω, M.loss t ω (M.firstAction t ω) ∂M.measure) =
        ∫ ω, M.loss t ω (M.secondAction t ω) ∂M.measure := by
    intro t
    exact (first_executed_loss_expectation M run t).trans
      (second_executed_loss_expectation M run t).symm
  have havg_int : ∀ t, MeasureTheory.Integrable
      (fun ω => (M.loss t ω (M.firstAction t ω) +
        M.loss t ω (M.secondAction t ω)) / 2) M.measure := by
    intro t
    exact ((M.first_executed_loss_integrable t).add
      (M.second_executed_loss_integrable t)).div_const 2
  have hincurred :
      (∫ ω, ∑ t ∈ Finset.range T,
          (M.loss t ω (M.firstAction t ω) + M.loss t ω (M.secondAction t ω)) / 2
        ∂M.measure) =
        ∫ ω, ∑ t ∈ Finset.range T, M.loss t ω (M.firstAction t ω) ∂M.measure := by
    calc
      (∫ ω, ∑ t ∈ Finset.range T,
          (M.loss t ω (M.firstAction t ω) + M.loss t ω (M.secondAction t ω)) / 2
        ∂M.measure) =
          ∑ t ∈ Finset.range T,
            ∫ ω, (M.loss t ω (M.firstAction t ω) +
              M.loss t ω (M.secondAction t ω)) / 2 ∂M.measure := by
                exact MeasureTheory.integral_finsetSum (μ := M.measure) (Finset.range T)
                  (fun t ht => havg_int t)
      _ = ∑ t ∈ Finset.range T,
          ∫ ω, M.loss t ω (M.firstAction t ω) ∂M.measure := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [MeasureTheory.integral_div,
              MeasureTheory.integral_add (M.first_executed_loss_integrable t)
                (M.second_executed_loss_integrable t), ← hround t]
            ring
      _ = ∫ ω, ∑ t ∈ Finset.range T, M.loss t ω (M.firstAction t ω) ∂M.measure := by
        symm
        exact MeasureTheory.integral_finsetSum (μ := M.measure) (Finset.range T)
          (fun t ht => M.first_executed_loss_integrable t)
  unfold two_point_regret first_action_regret
  rw [hincurred]

@[blueprint "lem:estimated-regret-representation"
  (statement := /-- Let $M$ be a hierarchical two-point bandit, let $\rho$ be a two-point FTRL run on $M$, and fix a horizon $T\in\mathbb N$. Define the probability vector $q_T$ to be the point mass at the expected-loss-minimizing fixed action $a_T^*$. Then the regret of the first executed action is the expected cumulative estimated-loss regret:
  \[
  R_T^{(1)}
  =
  \mathbb E\!\left[
    \sum_{t<T}\sum_{a\in\mathcal A}
    z_t(a)\bigl(p_t(a)-q_T(a)\bigr)
  \right].
  \] -/)
  (proof := /-- Let $q_T$ be the point mass at $a_T^*$. It belongs to the simplex. For every $t<T$, the integrability and conditional-mean fields in \cref{def:two-point-ftrl-run} allow the tower property to be applied to $\langle z_t,p_t-q_T\rangle$ and give
  \[
  \mathbb E\langle z_t,p_t-q_T\rangle
  =
  \int_\Omega\sum_a\bigl(p_t(a)-q_T(a)\bigr)
    \mathbb E[y_t(a)\mid\mathcal F_t]\,d\mathbb P.
  \]
  By \cref{lem:first-executed-loss-expectation}, the part weighted by $p_t$ is $\mathbb E[y_t(A_{t,1})]$. Since $q_T$ is concentrated at $a_T^*$, the remaining part is the integral of the conditional mean loss of $a_T^*$; the defining integral identity in \cref{def:hierarchical-two-point-bandit}, applied to the whole sample space, identifies it with $\mathbb E[y_t(a_T^*)]$. All summands are integrable, so finite linearity permits summation over $t<T$. The resulting difference is exactly \cref{def:first-action-regret}. -/)
  (title := /-- Representation of first-action regret by estimated regret -/)
  (latexEnv := "lemma")]
lemma estimated_regret_representation
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M)
    (T : ℕ) :
    first_action_regret M T =
      ∫ ω, ∑ t ∈ Finset.range T, ∑ a,
        run.estimatedLoss t ω a *
          (run.distribution t ω a - if a = M.bestAction T then 1 else 0)
        ∂M.measure := by
  classical
  letI := M.probability_measure
  let q : Action → ℝ := fun a => if a = M.bestAction T then 1 else 0
  have hq : probability_vector q := by
    simpa [probability_vector, q, eq_comm] using
      (ite_eq_mem_stdSimplex (𝕜 := ℝ) (M.bestAction T))
  have hround : ∀ t,
      (∫ ω, ∑ a, run.estimatedLoss t ω a *
          (run.distribution t ω a - q a) ∂M.measure) =
        (∫ ω, M.loss t ω (M.firstAction t ω) ∂M.measure) -
          ∫ ω, M.loss t ω (M.bestAction T) ∂M.measure := by
    intro t
    rcases run.feedback_loss_conditional_independence t with ⟨hhist, _, _, _⟩
    have hpmean_int : MeasureTheory.Integrable
        (fun ω => ∑ a, run.distribution t ω a * M.conditionalMeanLoss t ω a)
        M.measure := by
      apply MeasureTheory.integrable_finsetSum Finset.univ
      intro a ha
      apply (M.conditionalMeanLoss_integrable t a).bdd_mul
        (((run.distribution_measurable t a).mono hhist le_rfl).stronglyMeasurable.aestronglyMeasurable)
      exact Filter.Eventually.of_forall (fun ω => by
        have ha' := mem_Icc_of_mem_stdSimplex (run.distribution_mem t ω) a
        rw [Real.norm_eq_abs, abs_of_nonneg ha'.1]
        exact ha'.2)
    have hbest :
        (∫ ω, M.loss t ω (M.bestAction T) ∂M.measure) =
          ∫ ω, M.conditionalMeanLoss t ω (M.bestAction T) ∂M.measure := by
      simpa using M.conditionalMeanLoss_spec t (M.bestAction T) Set.univ MeasurableSet.univ
    calc
      (∫ ω, ∑ a, run.estimatedLoss t ω a *
          (run.distribution t ω a - q a) ∂M.measure) =
          ∫ ω, MeasureTheory.condExp (m := M.history t) M.measure
            (fun ω => ∑ a, run.estimatedLoss t ω a *
              (run.distribution t ω a - q a)) ω ∂M.measure :=
        (MeasureTheory.integral_condExp hhist).symm
      _ = ∫ ω, ∑ a,
          (run.distribution t ω a - q a) * M.conditionalMeanLoss t ω a
          ∂M.measure :=
        MeasureTheory.integral_congr_ae
          (run.estimated_regret_conditional_mean t q hq)
      _ = ∫ ω, (∑ a,
          run.distribution t ω a * M.conditionalMeanLoss t ω a) -
            M.conditionalMeanLoss t ω (M.bestAction T) ∂M.measure := by
        congr 1
        funext ω
        simp [q, sub_mul, Finset.sum_sub_distrib]
      _ = (∫ ω, ∑ a,
          run.distribution t ω a * M.conditionalMeanLoss t ω a ∂M.measure) -
            ∫ ω, M.conditionalMeanLoss t ω (M.bestAction T) ∂M.measure := by
        rw [MeasureTheory.integral_sub hpmean_int
          (M.conditionalMeanLoss_integrable t (M.bestAction T))]
      _ = (∫ ω, M.loss t ω (M.firstAction t ω) ∂M.measure) -
          ∫ ω, M.loss t ω (M.bestAction T) ∂M.measure := by
        rw [first_executed_loss_expectation M run t, hbest]
  unfold first_action_regret
  calc
    (∫ ω, ∑ t ∈ Finset.range T,
        M.loss t ω (M.firstAction t ω) ∂M.measure) -
        ∫ ω, ∑ t ∈ Finset.range T,
          M.loss t ω (M.bestAction T) ∂M.measure =
      (∑ t ∈ Finset.range T,
        ∫ ω, M.loss t ω (M.firstAction t ω) ∂M.measure) -
        ∑ t ∈ Finset.range T,
          ∫ ω, M.loss t ω (M.bestAction T) ∂M.measure := by
      rw [MeasureTheory.integral_finsetSum (μ := M.measure) (Finset.range T)
          (fun t ht => M.first_executed_loss_integrable t),
        MeasureTheory.integral_finsetSum (μ := M.measure) (Finset.range T)
          (fun t ht => M.loss_integrable t (M.bestAction T))]
    _ = ∑ t ∈ Finset.range T,
        ((∫ ω, M.loss t ω (M.firstAction t ω) ∂M.measure) -
          ∫ ω, M.loss t ω (M.bestAction T) ∂M.measure) := by
      rw [Finset.sum_sub_distrib]
    _ = ∑ t ∈ Finset.range T,
        ∫ ω, ∑ a, run.estimatedLoss t ω a *
          (run.distribution t ω a - q a) ∂M.measure := by
      apply Finset.sum_congr rfl
      intro t ht
      exact (hround t).symm
    _ = ∫ ω, ∑ t ∈ Finset.range T, ∑ a,
        run.estimatedLoss t ω a * (run.distribution t ω a - q a)
        ∂M.measure := by
      symm
      exact MeasureTheory.integral_finsetSum (μ := M.measure) (Finset.range T)
        (fun t ht => run.estimated_regret_integrable t q hq)
    _ = ∫ ω, ∑ t ∈ Finset.range T, ∑ a,
        run.estimatedLoss t ω a *
          (run.distribution t ω a - if a = M.bestAction T then 1 else 0)
        ∂M.measure := by
      rfl

@[blueprint "lem:subtree-mass-level-probability"
  (statement := /-- Let $M$ be a hierarchical two-point bandit, let $x\in\Delta_{\mathcal A}$, and fix a level $j$. Then every subtree mass $x[v]$ with $v\in V_j$ is nonnegative and
  \[
  \sum_{v\in V_j}x[v]=1.
  \]
  Thus the level-$j$ subtree masses form a probability vector, including when some of them have zero mass. -/)
  (proof := /-- By \cref{def:probability-vector}, every coordinate of $x$ is nonnegative and the coordinates sum to one. The unique-ancestor axiom in \cref{def:hierarchical-two-point-bandit} partitions the action set into the descendant sets of the nodes of $V_j$. Expanding \cref{def:subtree-mass}, finite distributivity gives nonnegativity term by term and shows that the sum over $v\in V_j$ contains each coordinate $x(a)$ exactly once. -/)
  (title := /-- Subtree masses at one level form a probability vector -/)
  (latexEnv := "lemma")]
lemma subtree_mass_level_probability
    (M : hierarchical_two_point_bandit Action Node Ω) (x : Action → ℝ)
    (hx : probability_vector x) (j : Fin M.depth) :
    (∀ v ∈ M.levelNodes j, 0 ≤ subtree_mass M x v) ∧
      ∑ v ∈ M.levelNodes j, subtree_mass M x v = 1 := by
  classical
  change (∀ a, 0 ≤ x a) ∧ ∑ a, x a = 1 at hx
  constructor
  · intro v hv
    simp only [subtree_mass]
    exact Finset.sum_nonneg (fun a _ => by
      split
      · exact hx.1 a
      · exact le_rfl)
  · rw [← hx.2]
    simp only [subtree_mass]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    rcases M.action_has_unique_ancestor j a with ⟨v, hv, huv⟩
    rw [Finset.sum_eq_single v]
    · rw [if_pos hv.2]
    · intro w hw hwne
      rw [if_neg]
      intro hwa
      exact hwne (huv w ⟨hw, hwa⟩)
    · exact fun hvnot => (hvnot hv.1).elim

@[blueprint "lem:nested-tsallis-ftrl-decomposition"
  (statement := /-- Let $M$ be a hierarchical two-point bandit and let $\rho$ be a two-point FTRL run on $M$. For every outcome $\omega\in\Omega$, horizon $T\in\mathbb N$, and comparator $q\in\Delta_{\mathcal A}$, write $p_t$ for the run distribution, $z_t$ for the estimated loss, and $\psi_t$ for the regularizer, and put
  \[
  Z_t(a)=\sum_{s=0}^{t}z_s(a),\qquad
  F_t(x,z)=\langle z,x\rangle+\psi_t(x).
  \]
  With the convention that the run's distribution $p_t$ minimizes the losses before round $t$ plus $\psi_{t+1}$, one has
  \[
  \begin{aligned}
  \sum_{t<T}\langle z_t,p_t-q\rangle
  \leq{}&\psi_{T+1}(q)-\psi_1(p_0)\\
  &+\sum_{t<T}\bigl(\psi_{t+1}(p_{t+1})-\psi_{t+2}(p_{t+1})\bigr)\\
  &+\sum_{t<T}\bigl(F_{t+1}(p_t,Z_t)-F_{t+1}(p_{t+1},Z_t)\bigr).
  \end{aligned}
  \]
  No differentiability of the regularizers or strict positivity of the coordinates of $p_t$ is assumed. -/)
  (proof := /-- By the minimizing inequality in \cref{def:two-point-ftrl-run} at time $T$, the terminal objective at $p_T$ is at most its value at $q$. Add the resulting nonnegative terminal slack to the estimated-loss pairing. It remains to identify this sum with the displayed right-hand side. This identity follows by induction on $T$: the case $T=0$ is $F_1(p_0,0)=\psi_1(p_0)$, and the successor step expands each finite sum at its last index. Distributing the new estimated-loss term separates the change from $p_T$ to $p_{T+1}$ under the fixed regularizer $\psi_{T+1}$ from the change between $\psi_{T+1}$ and $\psi_{T+2}$ at $p_{T+1}$. The remaining terms are precisely the induction hypothesis. -/)
  (title := /-- Deterministic decomposition for time-varying FTRL -/)
  (latexEnv := "lemma")]
lemma nested_tsallis_ftrl_decomposition
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M)
    (T : ℕ) (ω : Ω) (q : Action → ℝ) (hq : probability_vector q) :
    (∑ t ∈ Finset.range T, ∑ a,
        run.estimatedLoss t ω a * (run.distribution t ω a - q a)) ≤
      run.regularizer (T + 1) q -
        run.regularizer 1 (run.distribution 0 ω) +
      ∑ t ∈ Finset.range T,
        (run.regularizer (t + 1) (run.distribution (t + 1) ω) -
          run.regularizer (t + 2) (run.distribution (t + 1) ω)) +
      ∑ t ∈ Finset.range T,
        ((∑ a, (∑ s ∈ Finset.range (t + 1), run.estimatedLoss s ω a) *
              run.distribution t ω a) +
            run.regularizer (t + 1) (run.distribution t ω) -
          ((∑ a, (∑ s ∈ Finset.range (t + 1), run.estimatedLoss s ω a) *
                run.distribution (t + 1) ω a) +
            run.regularizer (t + 1) (run.distribution (t + 1) ω))) := by
  classical
  calc
    (∑ t ∈ Finset.range T, ∑ a,
        run.estimatedLoss t ω a * (run.distribution t ω a - q a)) ≤
        (∑ t ∈ Finset.range T, ∑ a,
          run.estimatedLoss t ω a * (run.distribution t ω a - q a)) +
          ((∑ a, (∑ s ∈ Finset.range T, run.estimatedLoss s ω a) * q a) +
              run.regularizer (T + 1) q -
            ((∑ a, (∑ s ∈ Finset.range T, run.estimatedLoss s ω a) *
                run.distribution T ω a) +
              run.regularizer (T + 1) (run.distribution T ω))) := by
        have hopt := run.ftrl_update T ω q hq
        linarith
    _ = run.regularizer (T + 1) q -
        run.regularizer 1 (run.distribution 0 ω) +
      ∑ t ∈ Finset.range T,
        (run.regularizer (t + 1) (run.distribution (t + 1) ω) -
          run.regularizer (t + 2) (run.distribution (t + 1) ω)) +
      ∑ t ∈ Finset.range T,
        ((∑ a, (∑ s ∈ Finset.range (t + 1), run.estimatedLoss s ω a) *
              run.distribution t ω a) +
            run.regularizer (t + 1) (run.distribution t ω) -
          ((∑ a, (∑ s ∈ Finset.range (t + 1), run.estimatedLoss s ω a) *
                run.distribution (t + 1) ω a) +
            run.regularizer (t + 1) (run.distribution (t + 1) ω))) := by
        induction T with
        | zero => simp
        | succ T ih =>
          simp only [Finset.sum_range_succ, Nat.succ_eq_add_one, add_mul, mul_add, mul_sub,
            Finset.sum_add_distrib, Finset.sum_sub_distrib] at ih ⊢
          linear_combination ih

@[blueprint "lem:tsallis-conjugate-divergence-bound"
  (statement := /-- Let $\eta,p,c,y\in\mathbb R$ satisfy $\eta>0$, $p>0$, $c>1$, and
  $y\geq-1/(c\eta\sqrt p)$. Then $1+\eta y\sqrt p>0$, and
  \[
  yp+\frac{1}{\eta\left(2-\eta\left((2/\eta-1/(\eta\sqrt p))-y\right)\right)}
  -\frac{1}{\eta\left(2-\eta(2/\eta-1/(\eta\sqrt p))\right)}
  =\frac{\eta p\sqrt p\,y^2}{1+\eta y\sqrt p}
  \leq\frac{c}{c-1}\eta p\sqrt p\,y^2.
  \] -/)
  (proof := /-- Positivity of $c\eta\sqrt p$ permits multiplication of the hypothesis on $y$, giving
  $-1\leq yc\eta\sqrt p$. Consequently
  \[
  \frac{c-1}{c}\leq1+\eta y\sqrt p,
  \]
  whose left-hand side is positive because $c>1$. The two rational denominators satisfy
  \[
  \eta\left(2-\eta\left((2/\eta-1/(\eta\sqrt p))-y\right)\right)
    =\frac{\eta(1+\eta y\sqrt p)}{\sqrt p},\qquad
  \eta\left(2-\eta(2/\eta-1/(\eta\sqrt p))\right)=\frac{\eta}{\sqrt p}.
  \]
  Substituting these identities and using $(\sqrt p)^2=p$ yields the asserted equality. Finally,
  the denominator lower bound implies
  $1/(1+\eta y\sqrt p)\leq c/(c-1)$. Multiplication by the nonnegative factor
  $\eta p\sqrt p\,y^2$ proves the asserted inequality. -/)
  (title := /-- Scalar one-half-Tsallis conjugate-divergence estimate -/)
  (latexEnv := "lemma")]
lemma tsallis_conjugate_divergence_bound
    (η p c y : ℝ) (hη : 0 < η) (hp : 0 < p) (hc : 1 < c)
    (hy : -1 / (c * η * Real.sqrt p) ≤ y) :
    0 < 1 + η * y * Real.sqrt p ∧
      y * p +
          1 / (η * (2 - η * ((2 / η - 1 / (η * Real.sqrt p)) - y))) -
          1 / (η * (2 - η * (2 / η - 1 / (η * Real.sqrt p)))) =
        η * p * Real.sqrt p * y ^ 2 / (1 + η * y * Real.sqrt p) ∧
      y * p +
          1 / (η * (2 - η * ((2 / η - 1 / (η * Real.sqrt p)) - y))) -
          1 / (η * (2 - η * (2 / η - 1 / (η * Real.sqrt p)))) ≤
        (c / (c - 1)) * η * p * Real.sqrt p * y ^ 2 := by
  have hsqrt : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
  have hcpos : 0 < c := lt_trans (by norm_num) hc
  have hscale : 0 < c * η * Real.sqrt p := mul_pos (mul_pos hcpos hη) hsqrt
  have hy' : -1 ≤ y * (c * η * Real.sqrt p) := (div_le_iff₀ hscale).mp hy
  have hden_lower : (c - 1) / c ≤ 1 + η * y * Real.sqrt p := by
    apply (div_le_iff₀ hcpos).2
    ring_nf at hy' ⊢
    linarith
  have hden : 0 < 1 + η * y * Real.sqrt p :=
    lt_of_lt_of_le (div_pos (sub_pos.mpr hc) hcpos) hden_lower
  have hden_alt : 1 + y * η * Real.sqrt p ≠ 0 := by
    nlinarith [hden]
  have hshift :
      η * (2 - η * ((2 / η - 1 / (η * Real.sqrt p)) - y)) =
        η * (1 + η * y * Real.sqrt p) / Real.sqrt p := by
    field_simp [hη.ne', hsqrt.ne']
    <;> ring
  have hbase :
      η * (2 - η * (2 / η - 1 / (η * Real.sqrt p))) =
        η / Real.sqrt p := by
    field_simp [hη.ne', hsqrt.ne']
    <;> ring
  have heq :
      y * p +
          1 / (η * (2 - η * ((2 / η - 1 / (η * Real.sqrt p)) - y))) -
          1 / (η * (2 - η * (2 / η - 1 / (η * Real.sqrt p)))) =
        η * p * Real.sqrt p * y ^ 2 / (1 + η * y * Real.sqrt p) := by
    rw [hshift, hbase]
    field_simp [hη.ne', hsqrt.ne', hden.ne']
    ring_nf
    rw [Real.sq_sqrt (le_of_lt hp)]
    ring
  refine ⟨hden, heq, ?_⟩
  rw [heq]
  have hcross : c - 1 ≤ c * (1 + η * y * Real.sqrt p) := by
    simpa [mul_comm] using (div_le_iff₀ hcpos).mp hden_lower
  have hrecip :
      1 / (1 + η * y * Real.sqrt p) ≤ c / (c - 1) := by
    apply (div_le_div_iff₀ hden (sub_pos.mpr hc)).2
    simpa using hcross
  have hnonneg : 0 ≤ η * p * Real.sqrt p * y ^ 2 := by positivity
  calc
    η * p * Real.sqrt p * y ^ 2 / (1 + η * y * Real.sqrt p) =
        (1 / (1 + η * y * Real.sqrt p)) *
          (η * p * Real.sqrt p * y ^ 2) := by ring
    _ ≤ (c / (c - 1)) * (η * p * Real.sqrt p * y ^ 2) :=
      mul_le_mul_of_nonneg_right hrecip hnonneg
    _ = (c / (c - 1)) * η * p * Real.sqrt p * y ^ 2 := by ring

@[blueprint "lem:two-point-centered-variance-bound"
  (statement := /-- Let $M$ be a hierarchical two-point bandit, let $p\in\Delta_{\mathcal A}$ be a probability vector, fix $j\in[L]$, and let $\ell\colon\mathcal V\to\mathbb R$ satisfy $0\leq\ell(v)\leq2\sigma_j$ for every $v\in V_j$. Set $P_v=p[v]$, the subtree mass of $v$. Then
  \[
  \begin{aligned}
  &\delta_j\sum_{v_0\in V_j}P_{v_0}
  \sum_{v\in V_j}P_v^{3/2}
  \left(
  \mathbf1_{\{v=v_0\}}\frac{\ell(v_0)}{\delta_jP_v}
  -\frac{\ell(v_0)}{\delta_j}
  \right)^2\\
  &\hspace{5em}\leq
  \frac{8\sigma_j^2}{\delta_j}
  \sum_{v\in V_j}(\sqrt{P_v}-P_v).
  \end{aligned}
  \]
  Division by a zero subtree mass is interpreted as zero, as in Lean. The outer factor $P_{v_0}$ makes the contribution of every $v_0$ with $P_{v_0}=0$ vanish, so no positive lower bound on the subtree masses is assumed. -/)
  (proof := /-- By \cref{lem:subtree-mass-level-probability}, the numbers $(P_v)_{v\in V_j}$ are nonnegative and sum to one. Expand the square. For each $v_0$ with $P_{v_0}>0$, cancellation gives
  \[
  \sum_vP_v^{3/2}
  \left(\mathbf1_{\{v=v_0\}}P_v^{-1}-1\right)^2
  =P_{v_0}^{-1/2}-2P_{v_0}^{1/2}+\sum_vP_v^{3/2}.
  \]
  If $P_{v_0}=0$, the corresponding outer summand is zero, including under Lean's zero-division convention. Multiplication by $P_{v_0}$ and summation over $v_0$ yield
  $\sum_v(\sqrt{P_v}-P_v^{3/2})$. Since
  $\sqrt u-u^{3/2}=\sqrt u(1-u)\leq2(\sqrt u-u)$ for $0\leq u\leq1$, and $\ell(v_0)^2\leq4\sigma_j^2$, the asserted constant is $2\cdot4=8$. -/)
  (title := /-- Centered hierarchical two-point variance estimate -/)
  (latexEnv := "lemma")]
lemma two_point_centered_variance_bound
    (M : hierarchical_two_point_bandit Action Node Ω)
    (p : Action → ℝ) (hp : probability_vector p) (j : Fin M.depth)
    (ℓ : Node → ℝ)
    (hℓ : ∀ v ∈ M.levelNodes j, 0 ≤ ℓ v ∧ ℓ v ≤ 2 * M.scale j) :
    M.delta j *
        ∑ v₀ ∈ M.levelNodes j,
          subtree_mass M p v₀ *
            ∑ v ∈ M.levelNodes j,
              (subtree_mass M p v * Real.sqrt (subtree_mass M p v)) *
                ((if v = v₀ then
                    ℓ v₀ / (M.delta j * subtree_mass M p v)
                  else 0) - ℓ v₀ / M.delta j) ^ 2 ≤
      ((8 * (M.scale j) ^ 2) / M.delta j) *
        ∑ v ∈ M.levelNodes j,
          (Real.sqrt (subtree_mass M p v) - subtree_mass M p v) := by
  classical
  let P : Node → ℝ := fun v => subtree_mass M p v
  let B : Node → Node → ℝ := fun v₀ v =>
    (if v = v₀ then 1 / (M.delta j * P v) else 0) - 1 / M.delta j
  rcases subtree_mass_level_probability M p hp j with ⟨hP, hsum⟩
  change (∀ v ∈ M.levelNodes j, 0 ≤ P v) at hP
  change ∑ v ∈ M.levelNodes j, P v = 1 at hsum
  change M.delta j *
        ∑ v₀ ∈ M.levelNodes j,
          P v₀ *
            ∑ v ∈ M.levelNodes j,
              (P v * Real.sqrt (P v)) *
                ((if v = v₀ then ℓ v₀ / (M.delta j * P v)
                  else 0) - ℓ v₀ / M.delta j) ^ 2 ≤
      ((8 * (M.scale j) ^ 2) / M.delta j) *
        ∑ v ∈ M.levelNodes j, (Real.sqrt (P v) - P v)
  have hδ : 0 < M.delta j := M.delta_positive j
  have hscale : 0 ≤ M.scale j := M.scale_nonnegative j
  have hfactor (v₀ v : Node) :
      ((if v = v₀ then ℓ v₀ / (M.delta j * P v) else 0) -
          ℓ v₀ / M.delta j) ^ 2 =
        (ℓ v₀) ^ 2 * (B v₀ v) ^ 2 := by
    dsimp [B]
    split <;> ring
  have hℓsq (v : Node) (hv : v ∈ M.levelNodes j) :
      (ℓ v) ^ 2 ≤ 4 * (M.scale j) ^ 2 := by
    rcases hℓ v hv with ⟨hℓnonneg, hℓupper⟩
    nlinarith
  have hcoefficient (v₀ : Node) (hv₀ : v₀ ∈ M.levelNodes j) :
      (M.delta j) ^ 2 *
          (P v₀ * ∑ v ∈ M.levelNodes j,
            (P v * Real.sqrt (P v)) * (B v₀ v) ^ 2) =
        Real.sqrt (P v₀) - 2 * P v₀ * Real.sqrt (P v₀) +
          P v₀ * ∑ v ∈ M.levelNodes j, P v * Real.sqrt (P v) := by
    by_cases hv₀zero : P v₀ = 0
    · simp [hv₀zero]
    · have hv₀pos : 0 < P v₀ := lt_of_le_of_ne (hP v₀ hv₀) (Ne.symm hv₀zero)
      have hsplit :
          ∑ v ∈ M.levelNodes j,
              (P v * Real.sqrt (P v)) * (B v₀ v) ^ 2 =
            (P v₀ * Real.sqrt (P v₀)) *
                (1 / (M.delta j * P v₀) - 1 / M.delta j) ^ 2 +
              (1 / M.delta j) ^ 2 *
                ∑ v ∈ (M.levelNodes j).erase v₀,
                  P v * Real.sqrt (P v) := by
        rw [← Finset.add_sum_erase _ _ hv₀]
        congr 1
        · simp [B]
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro v hv
          have hvne : v ≠ v₀ := (Finset.mem_erase.mp hv).1
          simp [B, hvne]
          ring
      have herase :
          ∑ v ∈ (M.levelNodes j).erase v₀, P v * Real.sqrt (P v) =
            (∑ v ∈ M.levelNodes j, P v * Real.sqrt (P v)) -
              P v₀ * Real.sqrt (P v₀) := by
        have hadd := Finset.sum_erase_add (M.levelNodes j)
          (fun v => P v * Real.sqrt (P v)) hv₀
        linarith
      rw [hsplit, herase]
      field_simp [hδ.ne', hv₀zero]
      ring
  have hbase :
      (M.delta j) ^ 2 *
          ∑ v₀ ∈ M.levelNodes j,
            P v₀ * ∑ v ∈ M.levelNodes j,
              (P v * Real.sqrt (P v)) * (B v₀ v) ^ 2 =
        (∑ v ∈ M.levelNodes j, Real.sqrt (P v)) -
          ∑ v ∈ M.levelNodes j, P v * Real.sqrt (P v) := by
    rw [Finset.mul_sum]
    calc
      ∑ v₀ ∈ M.levelNodes j,
          (M.delta j) ^ 2 *
            (P v₀ * ∑ v ∈ M.levelNodes j,
              (P v * Real.sqrt (P v)) * (B v₀ v) ^ 2) =
          ∑ v₀ ∈ M.levelNodes j,
            (Real.sqrt (P v₀) - 2 * P v₀ * Real.sqrt (P v₀) +
              P v₀ * ∑ v ∈ M.levelNodes j,
                P v * Real.sqrt (P v)) := by
        apply Finset.sum_congr rfl
        intro v₀ hv₀
        exact hcoefficient v₀ hv₀
      _ = (∑ v ∈ M.levelNodes j, Real.sqrt (P v)) -
          ∑ v ∈ M.levelNodes j, P v * Real.sqrt (P v) := by
        have hdouble :
            ∑ x ∈ M.levelNodes j, ∑ y ∈ M.levelNodes j,
                P x * (P y * Real.sqrt (P y)) =
              ∑ y ∈ M.levelNodes j, P y * Real.sqrt (P y) := by
          calc
            ∑ x ∈ M.levelNodes j, ∑ y ∈ M.levelNodes j,
                P x * (P y * Real.sqrt (P y)) =
                ∑ x ∈ M.levelNodes j,
                  P x * (∑ y ∈ M.levelNodes j,
                    P y * Real.sqrt (P y)) := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [Finset.mul_sum]
            _ = (∑ x ∈ M.levelNodes j, P x) *
                (∑ y ∈ M.levelNodes j, P y * Real.sqrt (P y)) := by
              rw [Finset.sum_mul]
            _ = ∑ y ∈ M.levelNodes j, P y * Real.sqrt (P y) := by
              rw [hsum]
              ring
        have htwice :
            ∑ x ∈ M.levelNodes j, 2 * P x * Real.sqrt (P x) =
              2 * ∑ x ∈ M.levelNodes j, P x * Real.sqrt (P x) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          ring
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_mul, Finset.mul_sum]
        rw [hdouble, htwice]
        ring
  have hscaled :
      ∑ v₀ ∈ M.levelNodes j,
          P v₀ * ∑ v ∈ M.levelNodes j,
            (P v * Real.sqrt (P v)) *
              ((4 * (M.scale j) ^ 2) * (B v₀ v) ^ 2) =
        (4 * (M.scale j) ^ 2) *
          ∑ v₀ ∈ M.levelNodes j,
            P v₀ * ∑ v ∈ M.levelNodes j,
              (P v * Real.sqrt (P v)) * (B v₀ v) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v₀ hv₀
    have hinner :
        ∑ v ∈ M.levelNodes j,
            (P v * Real.sqrt (P v)) *
              ((4 * (M.scale j) ^ 2) * (B v₀ v) ^ 2) =
          (4 * (M.scale j) ^ 2) *
            ∑ v ∈ M.levelNodes j,
              (P v * Real.sqrt (P v)) * (B v₀ v) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring
    rw [hinner]
    ring
  have hfirst :
      M.delta j *
          ∑ v₀ ∈ M.levelNodes j,
            P v₀ *
              ∑ v ∈ M.levelNodes j,
                (P v * Real.sqrt (P v)) *
                  ((if v = v₀ then ℓ v₀ / (M.delta j * P v)
                    else 0) - ℓ v₀ / M.delta j) ^ 2 ≤
        (4 * (M.scale j) ^ 2 / M.delta j) *
          ((∑ v ∈ M.levelNodes j, Real.sqrt (P v)) -
            ∑ v ∈ M.levelNodes j, P v * Real.sqrt (P v)) := by
    calc
      M.delta j *
          ∑ v₀ ∈ M.levelNodes j,
            P v₀ *
              ∑ v ∈ M.levelNodes j,
                (P v * Real.sqrt (P v)) *
                  ((if v = v₀ then ℓ v₀ / (M.delta j * P v)
                    else 0) - ℓ v₀ / M.delta j) ^ 2 =
          M.delta j *
            ∑ v₀ ∈ M.levelNodes j,
              P v₀ *
                ∑ v ∈ M.levelNodes j,
                  (P v * Real.sqrt (P v)) *
                    ((ℓ v₀) ^ 2 * (B v₀ v) ^ 2) := by
        congr 1
        apply Finset.sum_congr rfl
        intro v₀ hv₀
        congr 1
        apply Finset.sum_congr rfl
        intro v hv
        rw [hfactor]
      _ ≤ M.delta j *
            ∑ v₀ ∈ M.levelNodes j,
              P v₀ *
                ∑ v ∈ M.levelNodes j,
                  (P v * Real.sqrt (P v)) *
                    ((4 * (M.scale j) ^ 2) * (B v₀ v) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hδ)
        apply Finset.sum_le_sum
        intro v₀ hv₀
        apply mul_le_mul_of_nonneg_left _ (hP v₀ hv₀)
        apply Finset.sum_le_sum
        intro v hv
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg (hP v hv) (Real.sqrt_nonneg _))
        exact mul_le_mul_of_nonneg_right (hℓsq v₀ hv₀) (sq_nonneg (B v₀ v))
      _ = M.delta j * (4 * (M.scale j) ^ 2) *
            ∑ v₀ ∈ M.levelNodes j,
              P v₀ * ∑ v ∈ M.levelNodes j,
                (P v * Real.sqrt (P v)) * (B v₀ v) ^ 2 := by
        rw [hscaled]
        ring
      _ = (4 * (M.scale j) ^ 2 / M.delta j) *
          ((∑ v ∈ M.levelNodes j, Real.sqrt (P v)) -
            ∑ v ∈ M.levelNodes j, P v * Real.sqrt (P v)) := by
        rw [← hbase]
        field_simp [hδ.ne']
  have hmoment :
      (∑ v ∈ M.levelNodes j, Real.sqrt (P v)) -
          ∑ v ∈ M.levelNodes j, P v * Real.sqrt (P v) ≤
        2 * ((∑ v ∈ M.levelNodes j, Real.sqrt (P v)) -
          ∑ v ∈ M.levelNodes j, P v) := by
    calc
      (∑ v ∈ M.levelNodes j, Real.sqrt (P v)) -
          ∑ v ∈ M.levelNodes j, P v * Real.sqrt (P v) =
          ∑ v ∈ M.levelNodes j,
            (Real.sqrt (P v) - P v * Real.sqrt (P v)) := by
        rw [Finset.sum_sub_distrib]
      _ ≤ ∑ v ∈ M.levelNodes j,
          2 * (Real.sqrt (P v) - P v) := by
        apply Finset.sum_le_sum
        intro v hv
        have hsqrt_sq : (Real.sqrt (P v)) ^ 2 = P v :=
          Real.sq_sqrt (hP v hv)
        have hnonneg :
            0 ≤ Real.sqrt (P v) * (1 - Real.sqrt (P v)) ^ 2 :=
          mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
        nlinarith
      _ = 2 * ∑ v ∈ M.levelNodes j, (Real.sqrt (P v) - P v) := by
        rw [Finset.mul_sum]
      _ = 2 * (∑ v ∈ M.levelNodes j, Real.sqrt (P v) -
          ∑ v ∈ M.levelNodes j, P v) := by
        rw [Finset.sum_sub_distrib]
  calc
    M.delta j *
        ∑ v₀ ∈ M.levelNodes j,
          P v₀ *
            ∑ v ∈ M.levelNodes j,
              (P v * Real.sqrt (P v)) *
                ((if v = v₀ then ℓ v₀ / (M.delta j * P v)
                  else 0) - ℓ v₀ / M.delta j) ^ 2 ≤
        (4 * (M.scale j) ^ 2 / M.delta j) *
          ((∑ v ∈ M.levelNodes j, Real.sqrt (P v)) -
            ∑ v ∈ M.levelNodes j, P v * Real.sqrt (P v)) := hfirst
    _ ≤ (4 * (M.scale j) ^ 2 / M.delta j) *
        (2 * ((∑ v ∈ M.levelNodes j, Real.sqrt (P v)) -
          ∑ v ∈ M.levelNodes j, P v)) := by
      apply mul_le_mul_of_nonneg_left hmoment
      positivity
    _ = ((8 * (M.scale j) ^ 2) / M.delta j) *
        ∑ v ∈ M.levelNodes j, (Real.sqrt (P v) - P v) := by
      rw [Finset.sum_sub_distrib]
      ring

@[blueprint "lem:nonnegative-first-level-weight"
  (statement := /-- Let $M$ be a hierarchical two-point bandit, let $c\geq2$, and fix a level $j$. The coefficient of the level-$j$ summand in the time-$1$ nested one-half-Tsallis regularizer is nonnegative:
  \[
  0\leq
  \frac{4\sqrt c}{\sqrt{c-1}}\,
  \frac{\sigma_j}{\sqrt{\delta_j}}\,
  \sqrt{\max\left\{1,\frac{c(c-1)}{\delta_j}\right\}}.
  \] -/)
  (proof := /-- Since $c\geq2$, both $c$ and $c-1$ are positive. By \cref{def:hierarchical-two-point-bandit}, $\sigma_j\geq0$ and $\delta_j>0$. Hence the first quotient is positive, the quotient $\sigma_j/\sqrt{\delta_j}$ is nonnegative, and the remaining square-root factor is nonnegative. Their product is therefore nonnegative. -/)
  (title := /-- Nonnegativity of the initial nested-Tsallis weight -/)
  (latexEnv := "lemma")]
lemma nonnegative_first_level_weight
    (M : hierarchical_two_point_bandit Action Node Ω) (c : ℝ) (hc : 2 ≤ c)
    (j : Fin M.depth) :
    0 ≤ (4 * Real.sqrt c / Real.sqrt (c - 1)) *
      (M.scale j / Real.sqrt (M.delta j)) *
        Real.sqrt (max 1 (c * (c - 1) / M.delta j)) := by
  exact mul_nonneg
    (mul_nonneg
      (le_of_lt (div_pos
        (mul_pos (by norm_num) (Real.sqrt_pos.2 (by linarith)))
        (Real.sqrt_pos.2 (by linarith))))
      (div_nonneg (M.scale_nonnegative j)
        (le_of_lt (Real.sqrt_pos.2 (M.delta_positive j)))))
    (Real.sqrt_nonneg _)

@[blueprint "lem:nested-tsallis-level-gap-integrable"
  (statement := /-- Let $M$ be a hierarchical two-point bandit and let $\rho$ be a two-point FTRL run on $M$. For every round $t$ and level $j$, the random level gap
  \[
  G_{t,j}(\omega)=
  \sum_{v\in V_j}
  \left(\sqrt{p_t(\omega)[v]}-p_t(\omega)[v]\right)
  \]
  is integrable with respect to the model probability measure. -/)
  (proof := /-- By \cref{def:two-point-ftrl-run}, each coordinate of $p_t$ is measurable with respect to the history sigma-algebra, which is contained in the ambient sigma-algebra. Hence \cref{def:subtree-mass} shows that every subtree mass is measurable as a finite sum, and its square root is measurable. By \cref{lem:subtree-mass-level-probability}, the level-$j$ subtree masses are nonnegative and sum to one, so each belongs to $[0,1]$. If $x$ is such a mass, then $(\sqrt{x})^2=x$, and $0\leq\sqrt{x}\leq1$ implies
  $0\leq\sqrt{x}-x\leq1$. Thus every summand is a measurable function bounded in norm by one and is integrable with respect to the probability measure specified in \cref{def:hierarchical-two-point-bandit}. Integrability of the finite sum follows from integrability of its summands. -/)
  (title := /-- Integrability of the nested-Tsallis level gap -/)
  (latexEnv := "lemma")]
lemma nested_tsallis_level_gap_integrable
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M)
    (t : ℕ) (j : Fin M.depth) :
    MeasureTheory.Integrable
      (fun ω => ∑ v ∈ M.levelNodes j,
        (Real.sqrt (subtree_mass M (run.distribution t ω) v) -
          subtree_mass M (run.distribution t ω) v))
      M.measure := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure M.measure := M.probability_measure
  apply MeasureTheory.integrable_finsetSum
  intro v hv
  have hmass : Measurable (fun ω => subtree_mass M (run.distribution t ω) v) := by
    simp only [subtree_mass]
    apply Finset.measurable_sum
    intro a ha
    split
    · exact (run.distribution_measurable t a).mono (M.history.le t) le_rfl
    · exact measurable_const
  apply MeasureTheory.Integrable.of_bound (hmass.sqrt.sub hmass).aestronglyMeasurable 1
  filter_upwards with ω
  have hp := subtree_mass_level_probability M (run.distribution t ω)
    (run.distribution_mem t ω) j
  have hx0 : 0 ≤ subtree_mass M (run.distribution t ω) v := hp.1 v hv
  have hx1 : subtree_mass M (run.distribution t ω) v ≤ 1 := by
    rw [← hp.2]
    exact Finset.single_le_sum (fun w hw => hp.1 w hw) hv
  have hs0 := Real.sqrt_nonneg (subtree_mass M (run.distribution t ω) v)
  have hs1 : Real.sqrt (subtree_mass M (run.distribution t ω) v) ≤ 1 :=
    Real.sqrt_le_one.mpr hx1
  have hs2 := Real.sq_sqrt hx0
  have hgap0 : 0 ≤ Real.sqrt (subtree_mass M (run.distribution t ω) v) -
      subtree_mass M (run.distribution t ω) v := by
    nlinarith
  change |Real.sqrt (subtree_mass M (run.distribution t ω) v) -
      subtree_mass M (run.distribution t ω) v| ≤ 1
  rw [abs_of_nonneg hgap0]
  linarith

@[blueprint "lem:subtree-weighted-descendant-sum"
  (statement := /-- Let $M$ be a hierarchical two-point bandit, fix a level $j$, and let $p\colon\mathcal A\to\mathbb R$ and $F\colon\mathcal V\to\mathbb R$. Then
  \[
  \sum_{a\in\mathcal A}p(a)\sum_{v\in V_j}\mathbf 1_{\{v\preceq a\}}F(v)
  =\sum_{v\in V_j}p[v]F(v).
  \] -/)
  (proof := /-- Expand the subtree mass using \cref{def:subtree-mass}, distribute multiplication across both finite sums, and interchange the action and node sums. For each action--node pair, the two summands agree after splitting on whether the node is an ancestor of the action. -/)
  (title := /-- Grouping action weights by level subtrees -/)
  (latexEnv := "lemma")]
lemma subtree_weighted_descendant_sum
    (M : hierarchical_two_point_bandit Action Node Ω) (p : Action → ℝ)
    (j : Fin M.depth) (F : Node → ℝ) :
    (∑ a, p a * ∑ v ∈ M.levelNodes j,
      @ite ℝ (M.descends v a) (M.descends_decidable v a) (F v) 0) =
      ∑ v ∈ M.levelNodes j, subtree_mass M p v * F v := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  rw [subtree_mass, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hva : M.descends v a <;> simp [hva]

@[blueprint "lem:two-point-sampling-density-first-level-marginal"
  (statement := /-- For every round $t$, outcome $\omega$, first action $a$, and level $j$, summing the joint sampling density over the second action gives
  \[
  \sum_b d_t(\omega,a,j,b)=p_t(\omega,a)\delta_j.
  \] -/)
  (proof := /-- By \cref{lem:parent-common-at-level-equivalence}, the parent class of $a$ contains $a$. If $p_t(a)=0$, both sides vanish. Otherwise the total distribution mass of this parent class is positive. Expanding the sampling density, factoring out $p_t(a)\delta_j$, and summing its normalized conditional distribution over the parent class gives one. -/)
  (title := /-- First-action and level marginal of the sampling density -/)
  (latexEnv := "lemma")]
lemma two_point_sampling_density_first_level_marginal
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M)
    (t : ℕ) (ω : Ω) (a : Action) (j : Fin M.depth) :
    (∑ b, run.samplingDensity t ω a j b) =
      run.distribution t ω a * M.delta j := by
  classical
  let p : Action → ℝ := run.distribution t ω
  let P : Action → Prop := fun b => M.parentCommonAtLevel j a b
  letI (b : Action) : Decidable (P b) := M.parentCommonAtLevel_decidable j a b
  let D : ℝ := ∑ b, if P b then p b else 0
  have hp_nonneg : ∀ b, 0 ≤ p b := (run.distribution_mem t ω).1
  have hPaa : P a := (parent_common_at_level_equivalence M j).refl a
  by_cases hpa : p a = 0
  · simp_rw [run.samplingDensity_formula]
    simp [p, hpa]
  have hpa_pos : 0 < p a := lt_of_le_of_ne (hp_nonneg a) (Ne.symm hpa)
  have hD_pos : 0 < D := by
    apply lt_of_lt_of_le hpa_pos
    calc
      p a = if P a then p a else 0 := by simp [hPaa]
      _ ≤ ∑ b, if P b then p b else 0 := Finset.single_le_sum
        (fun b _ => ite_nonneg (hp_nonneg b) le_rfl) (Finset.mem_univ a)
      _ = D := rfl
  simp_rw [run.samplingDensity_formula]
  have halgebra : (∑ b, p a * M.delta j * if P b then p b / D else 0) =
      p a * M.delta j := by
    calc
      (∑ b, p a * M.delta j * if P b then p b / D else 0) =
          p a * M.delta j * ∑ b, if P b then p b / D else 0 := by
        rw [Finset.mul_sum]
      _ = p a * M.delta j * (D / D) := by
        congr 1
        rw [show (∑ b, if P b then p b / D else 0) =
            ∑ b, (if P b then p b else 0) / D by
          apply Finset.sum_congr rfl
          intro b hb
          by_cases hPb : P b <;> simp [hPb]]
        rw [← Finset.sum_div]
      _ = p a * M.delta j := by field_simp [ne_of_gt hD_pos]
  simpa only [p, P, D] using halgebra

@[blueprint "lem:feedback-atom-bounded-weight-integral"
  (statement := /-- Let $G_{a,j,b}=\{A_{t,1}=a,J_t=j,A_{t,2}=b\}$. If $f\colon\Omega\to\mathbb R$ is strongly measurable with respect to the pre-round history and satisfies $\lVert f\rVert\leq c$ almost surely, then
  \[
  \int_{G_{a,j,b}}f\,d\mathbb P
  =\int_\Omega d_t(a,j,b)f\,d\mathbb P.
  \] -/)
  (proof := /-- The feedback atom is measurable in the current-and-future randomization sigma-algebra. Its eventwise conditional law and \cref{lem:two-point-sampling-density-integrable} identify the conditional expectation of its indicator with the sampling density. Apply \cref{lem:bounded-conditional-expectation-mul} to pull the bounded history-measurable factor through conditional expectation, and then use preservation of the integral by conditional expectation. -/)
  (title := /-- Integrating a bounded history weight on a feedback atom -/)
  (latexEnv := "lemma")]
lemma feedback_atom_bounded_weight_integral
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M)
    (t : ℕ) (a : Action) (j : Fin M.depth) (b : Action) (f : Ω → ℝ)
    (hf : @MeasureTheory.StronglyMeasurable Ω ℝ inferInstance (M.history t) f)
    (c : ℝ) (hbound : ∀ᵐ ω ∂M.measure, ‖f ω‖ ≤ c) :
    (∫ ω, if M.firstAction t ω = a ∧ M.sampledLevel t ω = j ∧
        M.secondAction t ω = b then f ω else 0 ∂M.measure) =
      ∫ ω, run.samplingDensity t ω a j b * f ω ∂M.measure := by
  classical
  letI := M.probability_measure
  let A : Set Ω := {ω : Ω | M.firstAction t ω = a}
  let J : Set Ω := {ω : Ω | M.sampledLevel t ω = j}
  let B : Set Ω := {ω : Ω | M.secondAction t ω = b}
  let V : Set Ω := A ∩ J ∩ B
  have hcurrent_le :
      (MeasurableSpace.comap (fun ω : Ω => M.firstAction t ω) ⊤ ⊔
          MeasurableSpace.comap (fun ω : Ω => M.sampledLevel t ω) ⊤) ⊔
        MeasurableSpace.comap (fun ω : Ω => M.secondAction t ω) ⊤ ≤
      (⨆ s : {s : ℕ // t ≤ s},
        MeasurableSpace.comap (fun ω : Ω => M.firstAction s.1 ω) ⊤ ⊔
          MeasurableSpace.comap (fun ω : Ω => M.sampledLevel s.1 ω) ⊤ ⊔
            MeasurableSpace.comap (fun ω : Ω => M.secondAction s.1 ω) ⊤) := by
    simpa using le_iSup (fun s : {s : ℕ // t ≤ s} =>
      MeasurableSpace.comap (fun ω : Ω => M.firstAction s.1 ω) ⊤ ⊔
        MeasurableSpace.comap (fun ω : Ω => M.sampledLevel s.1 ω) ⊤ ⊔
          MeasurableSpace.comap (fun ω : Ω => M.secondAction s.1 ω) ⊤) ⟨t, le_rfl⟩
  have hA_base : @MeasurableSet Ω
      (MeasurableSpace.comap (fun ω : Ω => M.firstAction t ω) ⊤) A := by
    rw [MeasurableSpace.measurableSet_comap]
    refine ⟨{a}, by trivial, ?_⟩
    ext ω
    simp [A]
  have hJ_base : @MeasurableSet Ω
      (MeasurableSpace.comap (fun ω : Ω => M.sampledLevel t ω) ⊤) J := by
    rw [MeasurableSpace.measurableSet_comap]
    refine ⟨{j}, by trivial, ?_⟩
    ext ω
    simp [J]
  have hB_base : @MeasurableSet Ω
      (MeasurableSpace.comap (fun ω : Ω => M.secondAction t ω) ⊤) B := by
    rw [MeasurableSpace.measurableSet_comap]
    refine ⟨{b}, by trivial, ?_⟩
    ext ω
    simp [B]
  have hA_le := le_trans (le_trans le_sup_left le_sup_left) hcurrent_le
  have hJ_le := le_trans (le_trans le_sup_right le_sup_left) hcurrent_le
  have hB_le := le_trans le_sup_right hcurrent_le
  have hA : @MeasurableSet Ω
      (⨆ s : {s : ℕ // t ≤ s},
        MeasurableSpace.comap (fun ω : Ω => M.firstAction s.1 ω) ⊤ ⊔
          MeasurableSpace.comap (fun ω : Ω => M.sampledLevel s.1 ω) ⊤ ⊔
            MeasurableSpace.comap (fun ω : Ω => M.secondAction s.1 ω) ⊤) A :=
    hA_le A hA_base
  have hJ : @MeasurableSet Ω
      (⨆ s : {s : ℕ // t ≤ s},
        MeasurableSpace.comap (fun ω : Ω => M.firstAction s.1 ω) ⊤ ⊔
          MeasurableSpace.comap (fun ω : Ω => M.sampledLevel s.1 ω) ⊤ ⊔
            MeasurableSpace.comap (fun ω : Ω => M.secondAction s.1 ω) ⊤) J :=
    hJ_le J hJ_base
  have hB : @MeasurableSet Ω
      (⨆ s : {s : ℕ // t ≤ s},
        MeasurableSpace.comap (fun ω : Ω => M.firstAction s.1 ω) ⊤ ⊔
          MeasurableSpace.comap (fun ω : Ω => M.sampledLevel s.1 ω) ⊤ ⊔
            MeasurableSpace.comap (fun ω : Ω => M.secondAction s.1 ω) ⊤) B :=
    hB_le B hB_base
  have hV : @MeasurableSet Ω
      (⨆ s : {s : ℕ // t ≤ s},
        MeasurableSpace.comap (fun ω : Ω => M.firstAction s.1 ω) ⊤ ⊔
          MeasurableSpace.comap (fun ω : Ω => M.sampledLevel s.1 ω) ⊤ ⊔
            MeasurableSpace.comap (fun ω : Ω => M.secondAction s.1 ω) ⊤) V :=
    hA.inter hJ |>.inter hB
  rcases run.feedback_loss_conditional_independence t with ⟨hhist, _, hrandom, _⟩
  have hVamb : @MeasurableSet Ω inferInstance V := hrandom V hV
  let iV : Ω → ℝ := V.indicator (fun _ => (1 : ℝ))
  have hiVint : MeasureTheory.Integrable iV M.measure := by
    simpa [iV] using (MeasureTheory.integrable_const (1 : ℝ)).indicator hVamb
  have hdmeas : @Measurable Ω ℝ (M.history t) inferInstance
      (fun ω => run.samplingDensity t ω a j b) := by
    simp_rw [run.samplingDensity_formula]
    have hden_meas : @Measurable Ω ℝ (M.history t) inferInstance
        (fun ω => ∑ c, @ite ℝ (M.parentCommonAtLevel j a c)
          (M.parentCommonAtLevel_decidable j a c) (run.distribution t ω c) 0) := by
      apply Finset.measurable_sum
      intro c hc
      by_cases hac : M.parentCommonAtLevel j a c
      · simp only [hac, if_true]
        exact run.distribution_measurable t c
      · simp [hac]
    by_cases hab : M.parentCommonAtLevel j a b
    · simp only [hab, if_true]
      exact ((run.distribution_measurable t a).mul measurable_const).mul
        ((run.distribution_measurable t b).div hden_meas)
    · simp [hab]
  have hdint := two_point_sampling_density_integrable M run t a j b
  have hprob : MeasureTheory.condExp (m := M.history t) M.measure iV =ᵐ[M.measure]
      fun ω => run.samplingDensity t ω a j b := by
    symm
    apply MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hhist hiVint
    · intro s hs hfinite
      exact hdint.integrableOn
    · intro s hs hfinite
      rw [show iV = fun ω => if M.firstAction t ω = a ∧ M.sampledLevel t ω = j ∧
          M.secondAction t ω = b then (1 : ℝ) else 0 by
        funext ω
        by_cases haω : M.firstAction t ω = a <;>
          by_cases hjω : M.sampledLevel t ω = j <;>
            by_cases hbω : M.secondAction t ω = b <;>
              simp [iV, V, A, J, B, haω, hjω, hbω]]
      exact (run.feedback_conditional_law t a j b s hs).symm
    · exact hdmeas.aestronglyMeasurable
  have hpull := bounded_conditional_expectation_mul M.measure hhist hf hiVint c hbound
  have hfun : (fun ω => if M.firstAction t ω = a ∧ M.sampledLevel t ω = j ∧
      M.secondAction t ω = b then f ω else 0) = f * iV := by
    funext ω
    by_cases haω : M.firstAction t ω = a <;>
      by_cases hjω : M.sampledLevel t ω = j <;>
        by_cases hbω : M.secondAction t ω = b <;>
          simp [iV, V, A, J, B, haω, hjω, hbω]
  rw [hfun]
  calc
    (∫ ω, (f * iV) ω ∂M.measure) =
        ∫ ω, MeasureTheory.condExp (m := M.history t) M.measure (f * iV) ω
          ∂M.measure := (MeasureTheory.integral_condExp hhist).symm
    _ = ∫ ω, f ω * MeasureTheory.condExp (m := M.history t) M.measure iV ω
          ∂M.measure := MeasureTheory.integral_congr_ae hpull
    _ = ∫ ω, f ω * run.samplingDensity t ω a j b ∂M.measure :=
      MeasureTheory.integral_congr_ae (Filter.EventuallyEq.rfl.mul hprob)
    _ = ∫ ω, run.samplingDensity t ω a j b * f ω ∂M.measure := by
      congr 1
      funext ω
      exact mul_comm _ _

@[blueprint "lem:sampled-level-nonnegative-weight-integral"
  (statement := /-- Fix a round $t$ and level $j$. Let $f_a\colon\Omega\to\mathbb R_+$ be pre-round-history-measurable for every action $a$. If
  \[
  K(\omega)=\delta_j\sum_a p_t(\omega,a)f_a(\omega)
  \]
  is integrable, then the sampled weight $\mathbf 1_{\{J_t=j\}}f_{A_{t,1}}$ is integrable and has the same integral as $K$. -/)
  (proof := /-- Truncate each $f_a$ at height $n$. Partition the truncated sampled weight into the finitely many feedback atoms. On each atom, \cref{lem:feedback-atom-bounded-weight-integral} replaces its indicator by the sampling density. The products with the bounded truncations are integrable by \cref{lem:two-point-sampling-density-integrable}, so finite linearity is valid, and \cref{lem:two-point-sampling-density-first-level-marginal} sums out the second action, giving the truncated version of $K$. The truncated conditional weights are dominated by $K$. Monotone convergence for lower integrals and the resulting uniform integral bound prove integrability of the untruncated sampled weight. Applying monotone convergence once more on both sides and using uniqueness of limits proves equality of the two integrals. -/)
  (title := /-- Integration of a nonnegative sampled-level weight -/)
  (latexEnv := "lemma")]
lemma sampled_level_nonnegative_weight_integral
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M)
    (t : ℕ) (j : Fin M.depth) (f : Ω → Action → ℝ)
    (hfmeas : ∀ a, @MeasureTheory.StronglyMeasurable Ω ℝ inferInstance
      (M.history t) (fun ω => f ω a))
    (hfnonneg : ∀ ω a, 0 ≤ f ω a)
    (hK : MeasureTheory.Integrable
      (fun ω => M.delta j * ∑ a, run.distribution t ω a * f ω a) M.measure) :
    MeasureTheory.Integrable
        (fun ω => if M.sampledLevel t ω = j then f ω (M.firstAction t ω) else 0)
        M.measure ∧
      (∫ ω, if M.sampledLevel t ω = j then f ω (M.firstAction t ω) else 0
          ∂M.measure) =
        ∫ ω, M.delta j * ∑ a, run.distribution t ω a * f ω a ∂M.measure := by
  classical
  letI := M.probability_measure
  let fn : ℕ → Ω → Action → ℝ := fun n ω a => min (f ω a) (n : ℝ)
  let H : Ω → ℝ := fun ω =>
    if M.sampledLevel t ω = j then f ω (M.firstAction t ω) else 0
  let Hn : ℕ → Ω → ℝ := fun n ω =>
    if M.sampledLevel t ω = j then fn n ω (M.firstAction t ω) else 0
  let K : Ω → ℝ := fun ω => M.delta j * ∑ a, run.distribution t ω a * f ω a
  let Kn : ℕ → Ω → ℝ := fun n ω =>
    M.delta j * ∑ a, run.distribution t ω a * fn n ω a
  rcases run.feedback_loss_conditional_independence t with ⟨hhist, _, hrandom, _⟩
  have hcurrent_le :
      (MeasurableSpace.comap (fun ω : Ω => M.firstAction t ω) ⊤ ⊔
          MeasurableSpace.comap (fun ω : Ω => M.sampledLevel t ω) ⊤) ⊔
        MeasurableSpace.comap (fun ω : Ω => M.secondAction t ω) ⊤ ≤
      (⨆ s : {s : ℕ // t ≤ s},
        MeasurableSpace.comap (fun ω : Ω => M.firstAction s.1 ω) ⊤ ⊔
          MeasurableSpace.comap (fun ω : Ω => M.sampledLevel s.1 ω) ⊤ ⊔
            MeasurableSpace.comap (fun ω : Ω => M.secondAction s.1 ω) ⊤) := by
    simpa using le_iSup (fun s : {s : ℕ // t ≤ s} =>
      MeasurableSpace.comap (fun ω : Ω => M.firstAction s.1 ω) ⊤ ⊔
        MeasurableSpace.comap (fun ω : Ω => M.sampledLevel s.1 ω) ⊤ ⊔
          MeasurableSpace.comap (fun ω : Ω => M.secondAction s.1 ω) ⊤) ⟨t, le_rfl⟩
  have hA_le := le_trans (le_trans le_sup_left le_sup_left) hcurrent_le
  have hJ_le := le_trans (le_trans le_sup_right le_sup_left) hcurrent_le
  have hB_le := le_trans le_sup_right hcurrent_le
  have hfirst_meas : @Measurable Ω Action inferInstance ⊤
      (fun ω : Ω => M.firstAction t ω) :=
    (comap_measurable (fun ω : Ω => M.firstAction t ω)).mono
      (hA_le.trans hrandom) le_rfl
  have hlevel_meas : @Measurable Ω (Fin M.depth) inferInstance ⊤
      (fun ω : Ω => M.sampledLevel t ω) :=
    (comap_measurable (fun ω : Ω => M.sampledLevel t ω)).mono
      (hJ_le.trans hrandom) le_rfl
  have hsecond_meas : @Measurable Ω Action inferInstance ⊤
      (fun ω : Ω => M.secondAction t ω) :=
    (comap_measurable (fun ω : Ω => M.secondAction t ω)).mono
      (hB_le.trans hrandom) le_rfl
  have hAset : ∀ a, MeasurableSet {ω : Ω | M.firstAction t ω = a} := by
    intro a
    change MeasurableSet ((fun ω : Ω => M.firstAction t ω) ⁻¹' ({a} : Set Action))
    exact hfirst_meas (by trivial)
  have hJset : MeasurableSet {ω : Ω | M.sampledLevel t ω = j} := by
    change MeasurableSet
      ((fun ω : Ω => M.sampledLevel t ω) ⁻¹' ({j} : Set (Fin M.depth)))
    exact hlevel_meas (by trivial)
  have hBset : ∀ b, MeasurableSet {ω : Ω | M.secondAction t ω = b} := by
    intro b
    change MeasurableSet ((fun ω : Ω => M.secondAction t ω) ⁻¹' ({b} : Set Action))
    exact hsecond_meas (by trivial)
  have hGset : ∀ a b, MeasurableSet
      {ω : Ω | M.firstAction t ω = a ∧ M.sampledLevel t ω = j ∧
        M.secondAction t ω = b} := by
    intro a b
    have h := (hAset a).inter hJset |>.inter (hBset b)
    convert h using 1 <;> ext ω <;> simp [and_assoc]
  have hfnmeas : ∀ n a, @MeasureTheory.StronglyMeasurable Ω ℝ inferInstance
      (M.history t) (fun ω => fn n ω a) := by
    intro n a
    exact ((hfmeas a).measurable.min measurable_const).stronglyMeasurable
  have hfnnonneg : ∀ n ω a, 0 ≤ fn n ω a := by
    intro n ω a
    exact le_min (hfnonneg ω a) (Nat.cast_nonneg n)
  have hfnbound : ∀ n a, ∀ᵐ ω ∂M.measure, ‖fn n ω a‖ ≤ (n : ℝ) := by
    intro n a
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hfnnonneg n ω a)]
    exact min_le_right _ _
  have hselect_meas : ∀ n, Measurable (fun ω => fn n ω (M.firstAction t ω)) := by
    intro n
    rw [show (fun ω => fn n ω (M.firstAction t ω)) =
        fun ω => ∑ a, if M.firstAction t ω = a then fn n ω a else 0 by
      funext ω
      simp]
    apply Finset.measurable_sum
    intro a ha
    exact Measurable.piecewise (hAset a)
      ((hfnmeas n a).measurable.mono hhist le_rfl) measurable_const
  have hHnmeas : ∀ n, Measurable (Hn n) := by
    intro n
    exact Measurable.piecewise hJset (hselect_meas n) measurable_const
  have hHnnonneg : ∀ n ω, 0 ≤ Hn n ω := by
    intro n ω
    by_cases hjω : M.sampledLevel t ω = j <;> simp [Hn, hjω, hfnnonneg]
  have hHnbound : ∀ n ω, ‖Hn n ω‖ ≤ (n : ℝ) := by
    intro n ω
    by_cases hjω : M.sampledLevel t ω = j
    · simp only [Hn, hjω, if_true]
      rw [Real.norm_eq_abs, abs_of_nonneg (hfnnonneg n ω (M.firstAction t ω))]
      exact min_le_right _ _
    · simp [Hn, hjω, Nat.cast_nonneg]
  have hHnint : ∀ n, MeasureTheory.Integrable (Hn n) M.measure := by
    intro n
    exact MeasureTheory.Integrable.of_bound (hHnmeas n).aestronglyMeasurable n
      (Filter.Eventually.of_forall (hHnbound n))
  have hKnmeas : ∀ n, Measurable (Kn n) := by
    intro n
    have hsum : @Measurable Ω ℝ (M.history t) inferInstance
        (fun ω => ∑ a, run.distribution t ω a * fn n ω a) := by
      apply Finset.measurable_sum
      intro a ha
      exact (run.distribution_measurable t a).mul (hfnmeas n a).measurable
    exact (hsum.const_mul (M.delta j)).mono hhist le_rfl
  have hKnnonneg : ∀ n ω, 0 ≤ Kn n ω := by
    intro n ω
    apply mul_nonneg (le_of_lt (M.delta_positive j))
    apply Finset.sum_nonneg
    intro a ha
    exact mul_nonneg ((run.distribution_mem t ω).1 a) (hfnnonneg n ω a)
  have hKnle : ∀ n, Kn n ≤ K := by
    intro n ω
    apply mul_le_mul_of_nonneg_left _ (le_of_lt (M.delta_positive j))
    apply Finset.sum_le_sum
    intro a ha
    apply mul_le_mul_of_nonneg_left (min_le_left _ _) ((run.distribution_mem t ω).1 a)
  have hKnint : ∀ n, MeasureTheory.Integrable (Kn n) M.measure := by
    intro n
    exact hK.mono_nonneg (hKnmeas n).aestronglyMeasurable
      (Filter.Eventually.of_forall (hKnnonneg n))
      (Filter.Eventually.of_forall (hKnle n))
  have htrunc_integral : ∀ n, (∫ ω, Hn n ω ∂M.measure) =
      ∫ ω, Kn n ω ∂M.measure := by
    intro n
    have hatom_int : ∀ a b, MeasureTheory.Integrable
        (fun ω => if M.firstAction t ω = a ∧ M.sampledLevel t ω = j ∧
          M.secondAction t ω = b then fn n ω a else 0) M.measure := by
      intro a b
      have hmeas : Measurable (fun ω =>
          if M.firstAction t ω = a ∧ M.sampledLevel t ω = j ∧
            M.secondAction t ω = b then fn n ω a else 0) :=
        Measurable.piecewise (hGset a b)
          ((hfnmeas n a).measurable.mono hhist le_rfl) measurable_const
      apply MeasureTheory.Integrable.of_bound hmeas.aestronglyMeasurable (n : ℝ)
      filter_upwards with ω
      by_cases hω : M.firstAction t ω = a ∧ M.sampledLevel t ω = j ∧
          M.secondAction t ω = b
      · rw [if_pos hω, Real.norm_eq_abs, abs_of_nonneg (hfnnonneg n ω a)]
        exact min_le_right _ _
      · simp [hω, Nat.cast_nonneg]
    have hdensity_int : ∀ a b, MeasureTheory.Integrable
        (fun ω => run.samplingDensity t ω a j b * fn n ω a) M.measure := by
      intro a b
      simpa only [mul_comm] using
        (two_point_sampling_density_integrable M run t a j b).bdd_mul
          ((hfnmeas n a).mono hhist).aestronglyMeasurable (hfnbound n a)
    calc
      (∫ ω, Hn n ω ∂M.measure) =
          ∫ ω, ∑ a, ∑ b,
            (if M.firstAction t ω = a ∧ M.sampledLevel t ω = j ∧
              M.secondAction t ω = b then fn n ω a else 0) ∂M.measure := by
        congr 1
        funext ω
        by_cases hjω : M.sampledLevel t ω = j
        · simp only [Hn, hjω, if_true]
          rw [Finset.sum_eq_single (M.firstAction t ω)]
          · rw [Finset.sum_eq_single (M.secondAction t ω)]
            · simp [hjω]
            · intro b hb hne
              simp [hne, ne_comm]
            · simp
          · intro a ha hne
            apply Finset.sum_eq_zero
            intro b hb
            rw [if_neg]
            intro h
            exact hne h.1.symm
          · simp
        · simp [Hn, hjω]
      _ = ∑ a, ∑ b, ∫ ω,
          (if M.firstAction t ω = a ∧ M.sampledLevel t ω = j ∧
            M.secondAction t ω = b then fn n ω a else 0) ∂M.measure := by
        rw [MeasureTheory.integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro a ha
          rw [MeasureTheory.integral_finsetSum]
          exact fun b hb => hatom_int a b
        · intro a ha
          exact MeasureTheory.integrable_finsetSum _ (fun b hb => hatom_int a b)
      _ = ∑ a, ∑ b, ∫ ω,
          run.samplingDensity t ω a j b * fn n ω a ∂M.measure := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        exact feedback_atom_bounded_weight_integral M run t a j b (fun ω => fn n ω a)
          (hfnmeas n a) n (hfnbound n a)
      _ = ∫ ω, ∑ a, ∑ b,
          run.samplingDensity t ω a j b * fn n ω a ∂M.measure := by
        rw [MeasureTheory.integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro a ha
          rw [MeasureTheory.integral_finsetSum]
          exact fun b hb => hdensity_int a b
        · intro a ha
          exact MeasureTheory.integrable_finsetSum _ (fun b hb => hdensity_int a b)
      _ = ∫ ω, Kn n ω ∂M.measure := by
        congr 1
        funext ω
        simp_rw [← Finset.sum_mul]
        rw [show (∑ a, (∑ b, run.samplingDensity t ω a j b) * fn n ω a) =
            ∑ a, run.distribution t ω a * M.delta j * fn n ω a by
          apply Finset.sum_congr rfl
          intro a ha
          rw [two_point_sampling_density_first_level_marginal]]
        simp [Kn, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        ring
  have hHnmono : ∀ ω, Monotone (fun n => Hn n ω) := by
    intro ω n m hnm
    by_cases hjω : M.sampledLevel t ω = j
    · simp only [Hn, hjω, if_true, fn]
      exact min_le_min_left _ (Nat.cast_le.mpr hnm)
    · simp [Hn, hjω]
  have hHntendsto : ∀ ω, Filter.Tendsto (fun n => Hn n ω) Filter.atTop (nhds (H ω)) := by
    intro ω
    by_cases hjω : M.sampledLevel t ω = j
    · simp only [Hn, H, hjω, if_true, fn]
      obtain ⟨N, hN⟩ := exists_nat_ge (f ω (M.firstAction t ω))
      exact tendsto_atTop_of_eventually_const (i₀ := N) (fun n hn =>
        min_eq_left (le_trans hN (Nat.cast_le.mpr hn)))
    · simp [Hn, H, hjω]
  have hKntendsto : ∀ ω, Filter.Tendsto (fun n => Kn n ω) Filter.atTop (nhds (K ω)) := by
    intro ω
    apply Filter.Tendsto.const_mul
    apply tendsto_finset_sum
    intro a ha
    apply Filter.Tendsto.const_mul
    obtain ⟨N, hN⟩ := exists_nat_ge (f ω a)
    exact tendsto_atTop_of_eventually_const (i₀ := N) (fun n hn =>
      min_eq_left (le_trans hN (Nat.cast_le.mpr hn)))
  have hKmono : ∀ ω, Monotone (fun n => Kn n ω) := by
    intro ω n m hnm
    apply mul_le_mul_of_nonneg_left _ (le_of_lt (M.delta_positive j))
    apply Finset.sum_le_sum
    intro a ha
    apply mul_le_mul_of_nonneg_left _ ((run.distribution_mem t ω).1 a)
    exact min_le_min_left _ (Nat.cast_le.mpr hnm)
  have hKlim := MeasureTheory.integral_tendsto_of_tendsto_of_monotone hKnint hK
    (Filter.Eventually.of_forall hKmono) (Filter.Eventually.of_forall hKntendsto)
  have hlinlim := MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone
    (μ := M.measure)
    (fun n => (hHnmeas n).aemeasurable.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun ω =>
      fun n m hnm => ENNReal.ofReal_le_ofReal (hHnmono ω hnm)))
    (Filter.Eventually.of_forall (fun ω =>
      ENNReal.continuous_ofReal.tendsto (H ω) |>.comp (hHntendsto ω)))
  have hlinbound : (∫⁻ ω, ENNReal.ofReal (H ω) ∂M.measure) ≤
      ENNReal.ofReal (∫ ω, K ω ∂M.measure) := by
    apply le_of_tendsto hlinlim
    filter_upwards with n
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hHnint n)
      (Filter.Eventually.of_forall (hHnnonneg n)), htrunc_integral n]
    exact ENNReal.ofReal_le_ofReal (MeasureTheory.integral_mono_ae (hKnint n) hK
      (Filter.Eventually.of_forall (hKnle n)))
  have hHmeas : Measurable H := by
    apply measurable_of_tendsto_metrizable (fun n => hHnmeas n)
    rw [tendsto_pi_nhds]
    exact hHntendsto
  have hHint : MeasureTheory.Integrable H M.measure := by
    refine ⟨hHmeas.aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
    have henorm : (fun ω => ‖H ω‖ₑ) = fun ω => ENNReal.ofReal (H ω) := by
      funext ω
      rw [Real.enorm_of_nonneg]
      by_cases hjω : M.sampledLevel t ω = j <;> simp [H, hjω, hfnonneg]
    rw [henorm]
    exact lt_of_le_of_lt hlinbound ENNReal.ofReal_lt_top
  have hHlim := MeasureTheory.integral_tendsto_of_tendsto_of_monotone hHnint hHint
    (Filter.Eventually.of_forall hHnmono) (Filter.Eventually.of_forall hHntendsto)
  refine ⟨?_, ?_⟩
  · simpa only [H] using hHint
  · change (∫ ω, H ω ∂M.measure) = ∫ ω, K ω ∂M.measure
    exact tendsto_nhds_unique hHlim
      (hKlim.congr' (Filter.Eventually.of_forall (fun n => (htrunc_integral n).symm)))

@[blueprint "lem:feedback-atom-null-of-not-parent-common"
  (statement := /-- Fix a round $t$, a level $j$, and actions $a,b$. If $a$ and $b$ do not belong to the same level-$j$ parent class, then the feedback atom
  $\{A_{t,1}=a,J_t=j,A_{t,2}=b\}$ is null. -/)
  (proof := /-- The feedback atom is measurable because each of its three coordinates belongs to the current-and-future randomization sigma-algebra, which is contained in the ambient sigma-algebra. Apply \cref{lem:feedback-atom-bounded-weight-integral} to the constant function one. The sampling-density formula is identically zero when the two actions are not in the same parent class, so the integral of the atom indicator, and hence its measure, is zero. -/)
  (title := /-- Nullity of incompatible feedback atoms -/)
  (latexEnv := "lemma")]
lemma feedback_atom_null_of_not_parent_common
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M)
    (t : ℕ) (a : Action) (j : Fin M.depth) (b : Action)
    (hab : ¬M.parentCommonAtLevel j a b) :
    ∀ᵐ ω ∂M.measure, ¬(M.firstAction t ω = a ∧ M.sampledLevel t ω = j ∧
      M.secondAction t ω = b) := by
  classical
  letI := M.probability_measure
  let G : Set Ω := {ω | M.firstAction t ω = a ∧ M.sampledLevel t ω = j ∧
    M.secondAction t ω = b}
  rcases run.feedback_loss_conditional_independence t with ⟨_, _, hrandom, _⟩
  have hcurrent_le :
      (MeasurableSpace.comap (fun ω : Ω => M.firstAction t ω) ⊤ ⊔
          MeasurableSpace.comap (fun ω : Ω => M.sampledLevel t ω) ⊤) ⊔
        MeasurableSpace.comap (fun ω : Ω => M.secondAction t ω) ⊤ ≤
      (⨆ s : {s : ℕ // t ≤ s},
        MeasurableSpace.comap (fun ω : Ω => M.firstAction s.1 ω) ⊤ ⊔
          MeasurableSpace.comap (fun ω : Ω => M.sampledLevel s.1 ω) ⊤ ⊔
            MeasurableSpace.comap (fun ω : Ω => M.secondAction s.1 ω) ⊤) := by
    simpa using le_iSup (fun s : {s : ℕ // t ≤ s} =>
      MeasurableSpace.comap (fun ω : Ω => M.firstAction s.1 ω) ⊤ ⊔
        MeasurableSpace.comap (fun ω : Ω => M.sampledLevel s.1 ω) ⊤ ⊔
          MeasurableSpace.comap (fun ω : Ω => M.secondAction s.1 ω) ⊤) ⟨t, le_rfl⟩
  have hfirst : @Measurable Ω Action inferInstance ⊤
      (fun ω => M.firstAction t ω) :=
    (comap_measurable (fun ω : Ω => M.firstAction t ω)).mono
      ((le_trans (le_trans le_sup_left le_sup_left) hcurrent_le).trans hrandom) le_rfl
  have hlevel : @Measurable Ω (Fin M.depth) inferInstance ⊤
      (fun ω => M.sampledLevel t ω) :=
    (comap_measurable (fun ω : Ω => M.sampledLevel t ω)).mono
      ((le_trans (le_trans le_sup_right le_sup_left) hcurrent_le).trans hrandom) le_rfl
  have hsecond : @Measurable Ω Action inferInstance ⊤
      (fun ω => M.secondAction t ω) :=
    (comap_measurable (fun ω : Ω => M.secondAction t ω)).mono
      ((le_trans le_sup_right hcurrent_le).trans hrandom) le_rfl
  have hA : MeasurableSet {ω : Ω | M.firstAction t ω = a} := by
    change MeasurableSet ((fun ω : Ω => M.firstAction t ω) ⁻¹' ({a} : Set Action))
    exact hfirst (by trivial)
  have hJ : MeasurableSet {ω : Ω | M.sampledLevel t ω = j} := by
    change MeasurableSet
      ((fun ω : Ω => M.sampledLevel t ω) ⁻¹' ({j} : Set (Fin M.depth)))
    exact hlevel (by trivial)
  have hB : MeasurableSet {ω : Ω | M.secondAction t ω = b} := by
    change MeasurableSet ((fun ω : Ω => M.secondAction t ω) ⁻¹' ({b} : Set Action))
    exact hsecond (by trivial)
  have hG : MeasurableSet G := by
    have hinter := hA.inter hJ |>.inter hB
    convert hinter using 1 <;> ext ω <;> simp [G, and_assoc]
  have hone_bound : ∀ᵐ ω ∂M.measure, ‖(1 : ℝ)‖ ≤ 1 :=
    Filter.Eventually.of_forall (fun ω => by norm_num)
  have hone_meas : @MeasureTheory.StronglyMeasurable Ω ℝ inferInstance
      (M.history t) (fun _ => (1 : ℝ)) :=
    (show @Measurable Ω ℝ (M.history t) inferInstance
      (fun _ => (1 : ℝ)) from measurable_const).stronglyMeasurable
  have hint := feedback_atom_bounded_weight_integral M run t a j b
    (fun _ => (1 : ℝ)) hone_meas 1 hone_bound
  have hindicator : G.indicator (1 : Ω → ℝ) = fun ω =>
      if M.firstAction t ω = a ∧ M.sampledLevel t ω = j ∧
        M.secondAction t ω = b then 1 else 0 := by
    funext ω
    by_cases hω : M.firstAction t ω = a ∧ M.sampledLevel t ω = j ∧
        M.secondAction t ω = b <;> simp [G, hω]
  have hreal : M.measure.real G = 0 := by
    rw [← MeasureTheory.integral_indicator_one hG, hindicator]
    calc
      (∫ ω, if M.firstAction t ω = a ∧ M.sampledLevel t ω = j ∧
          M.secondAction t ω = b then (1 : ℝ) else 0 ∂M.measure) =
          ∫ ω, run.samplingDensity t ω a j b * 1 ∂M.measure := hint
      _ = 0 := by
        simp_rw [run.samplingDensity_formula]
        simp [hab]
  have hzero : M.measure G = 0 :=
    (MeasureTheory.measureReal_eq_zero_iff).mp hreal
  simpa only [G, Set.mem_setOf_eq] using
    (MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hzero)

@[blueprint "lem:parent-common-loss-difference-bound"
  (statement := /-- If two actions belong to the same parent class at level $j$, then at every round and outcome their loss difference has absolute value at most $\sigma_j$. -/)
  (proof := /-- If the actions coincide, the assertion follows from nonnegativity of the scale. Otherwise, \cref{def:hierarchical-two-point-bandit} bounds their loss difference by the scale at their similarity level. Membership in the same parent class implies that level $j$ is no deeper than the similarity level: this is immediate at the first level, and at a later level follows because common ancestry at the preceding level would contradict divergence there or earlier. Antitonicity of the scales completes the estimate. -/)
  (title := /-- Loss range inside a parent class -/)
  (latexEnv := "lemma")]
lemma parent_common_loss_difference_bound
    (M : hierarchical_two_point_bandit Action Node Ω) (t : ℕ) (ω : Ω)
    (j : Fin M.depth) (a b : Action) (hab : M.parentCommonAtLevel j a b) :
    |M.loss t ω a - M.loss t ω b| ≤ M.scale j := by
  by_cases heq : a = b
  · subst b
    simpa using M.scale_nonnegative j
  have htree := M.tree_compatible t ω a b
  rw [if_neg heq] at htree
  apply htree.trans
  apply M.scale_antitone
  rcases (M.parentCommonAtLevel_iff j a b).mp hab with hzero | ⟨i, hji, hcommon⟩
  · exact Fin.le_iff_val_le_val.mpr (by omega)
  · have hnot := (M.similarityLevel_spec a b heq).1
    have hil : i < M.similarityLevel a b := by
      by_contra hle
      have hsimle : M.similarityLevel a b ≤ i := le_of_not_gt hle
      exact hnot (M.commonAtLevel_mono (M.similarityLevel a b) i a b hsimle hcommon)
    exact Fin.le_iff_val_le_val.mpr (by omega)

@[blueprint "lem:two-point-action-centered-variance-bound"
  (statement := /-- Let $p$ be a probability vector and fix a level $j$. Averaging the centered level-$j$ importance-weight expression with loss bound $2\sigma_j$ over the first action gives at most
  \[
  \frac{8\sigma_j^2}{\delta_j}
  \sum_{v\in V_j}(\sqrt{p[v]}-p[v]).
  \] -/)
  (proof := /-- Split each squared centered term into the branch that is common to all actions and the correction on descendant actions. The common branch is averaged using the total action mass, while \cref{lem:subtree-weighted-descendant-sum} groups the correction by subtree mass. The subtree masses have total mass one by \cref{lem:subtree-mass-level-probability}; consequently the identical decomposition of the node-sampled expression shows that the two averages agree. Apply \cref{lem:two-point-centered-variance-bound} to the constant node function $2\sigma_j$. -/)
  (title := /-- Action-averaged centered variance estimate -/)
  (latexEnv := "lemma")]
lemma two_point_action_centered_variance_bound
    (M : hierarchical_two_point_bandit Action Node Ω) (p : Action → ℝ)
    (hp : probability_vector p) (j : Fin M.depth) :
    M.delta j * ∑ a, p a * ∑ v ∈ M.levelNodes j,
        (subtree_mass M p v * Real.sqrt (subtree_mass M p v)) *
          ((@ite ℝ (M.descends v a) (M.descends_decidable v a)
              ((2 * M.scale j) / (M.delta j * subtree_mass M p v)) 0) -
            (2 * M.scale j) / M.delta j) ^ 2 ≤
      ((8 * (M.scale j) ^ 2) / M.delta j) *
        ∑ v ∈ M.levelNodes j,
          (Real.sqrt (subtree_mass M p v) - subtree_mass M p v) := by
  classical
  let P : Node → ℝ := fun v => subtree_mass M p v
  let Q : Node → ℝ := fun v => P v * Real.sqrt (P v)
  let c : ℝ := 2 * M.scale j
  let B : Node → ℝ := fun v => (c / M.delta j) ^ 2
  let S : Node → ℝ := fun v => (c / (M.delta j * P v) - c / M.delta j) ^ 2
  have hp_sum : ∑ a, p a = 1 := hp.2
  have hdesc (a : Action) (v : Node) :
      Q v * ((@ite ℝ (M.descends v a) (M.descends_decidable v a)
          (c / (M.delta j * P v)) 0) - c / M.delta j) ^ 2 =
        Q v * B v + @ite ℝ (M.descends v a) (M.descends_decidable v a)
          (Q v * (S v - B v)) 0 := by
    by_cases hva : M.descends v a <;> simp [hva, S, B] <;> ring
  have heq (v₀ v : Node) :
      Q v * ((if v = v₀ then c / (M.delta j * P v) else 0) -
          c / M.delta j) ^ 2 =
        Q v * B v + if v = v₀ then Q v * (S v - B v) else 0 := by
    by_cases hv : v = v₀ <;> simp [hv, S, B] <;> ring
  have haction :
      (∑ a, p a * ∑ v ∈ M.levelNodes j,
          Q v * ((@ite ℝ (M.descends v a) (M.descends_decidable v a)
              (c / (M.delta j * P v)) 0) - c / M.delta j) ^ 2) =
        (∑ v ∈ M.levelNodes j, Q v * B v) +
          ∑ v ∈ M.levelNodes j, P v * (Q v * (S v - B v)) := by
    simp_rw [hdesc, Finset.sum_add_distrib, mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hp_sum, one_mul]
    rw [subtree_weighted_descendant_sum M p j
      (fun v => Q v * (S v - B v))]
  have hnode :
      (∑ v₀ ∈ M.levelNodes j, P v₀ *
          ∑ v ∈ M.levelNodes j,
            Q v * ((if v = v₀ then c / (M.delta j * P v) else 0) -
              c / M.delta j) ^ 2) =
        (∑ v ∈ M.levelNodes j, Q v * B v) +
          ∑ v ∈ M.levelNodes j, P v * (Q v * (S v - B v)) := by
    simp_rw [heq, Finset.sum_add_distrib, mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul]
    have hPsum := (subtree_mass_level_probability M p hp j).2
    change ∑ v ∈ M.levelNodes j, P v = 1 at hPsum
    rw [hPsum, one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro v₀ hv₀
    rw [Finset.sum_eq_single v₀]
    · simp
    · intro v hv hvne
      simp [hvne]
    · exact fun h => (h hv₀).elim
  have hvar := two_point_centered_variance_bound M p hp j
    (fun _ => 2 * M.scale j) (fun v hv => by
      constructor
      · exact mul_nonneg (by norm_num) (M.scale_nonnegative j)
      · exact le_rfl)
  change M.delta j * ∑ a, p a * ∑ v ∈ M.levelNodes j,
      Q v * ((@ite ℝ (M.descends v a) (M.descends_decidable v a)
          (c / (M.delta j * P v)) 0) - c / M.delta j) ^ 2 ≤
    ((8 * (M.scale j) ^ 2) / M.delta j) *
      ∑ v ∈ M.levelNodes j, (Real.sqrt (P v) - P v)
  rw [haction, ← hnode]
  simpa only [P, Q, c] using hvar

@[blueprint "lem:sampled-subtree-centered-variance-integral"
  (statement := /-- Let $M$ be a hierarchical two-point bandit and let $\rho$ be a two-point FTRL run whose shift at level $k$ is $\sigma_k$. Fix a round $t$ and a level $j$, put $P_v(\omega)=p_t(\omega)[v]$, and set
  \[
  L_{t,j}(\omega)=
  y_t(A_{t,1})-y_t(A_{t,2})+\sigma_j.
  \]
  Then
  \[
  \begin{aligned}
  &\int \mathbf 1_{\{J_t=j\}}
  \sum_{v\in V_j}P_v^{3/2}
  \left(
    \mathbf 1_{\{v\preceq A_{t,1}\}}
      \frac{L_{t,j}}{\delta_jP_v}
    -\frac{L_{t,j}}{\delta_j}
  \right)^2\,d\mathbb P\\
  &\hspace{4em}\leq
  \frac{8\sigma_j^2}{\delta_j}
  \int\sum_{v\in V_j}(\sqrt{P_v}-P_v)\,d\mathbb P .
  \end{aligned}
  \]
  Division by a zero subtree mass is interpreted as zero. -/)
  (proof := /-- For every action $a$, let $F_a$ be the displayed subtree sum with the shifted loss replaced by the constant $2\sigma_j$, and put
  \[
  H=\mathbf 1_{\{J_t=j\}}F_{A_{t,1}},\qquad
  K=\delta_j\sum_a p_t(a)F_a.
  \]
  Each $F_a$ is nonnegative and measurable with respect to the pre-round history; nonnegativity of its subtree coefficients follows from \cref{lem:subtree-mass-level-probability}. The pointwise estimate \cref{lem:two-point-action-centered-variance-bound} gives
  \[
  0\leq K\leq \frac{8\sigma_j^2}{\delta_j}
  \sum_{v\in V_j}(\sqrt{P_v}-P_v).
  \]
  The upper bound is integrable by \cref{lem:nested-tsallis-level-gap-integrable}, hence $K$ is integrable. Therefore \cref{lem:sampled-level-nonnegative-weight-integral} shows that $H$ is integrable and that $\int H=\int K$.

  By \cref{lem:feedback-atom-null-of-not-parent-common}, almost every outcome with $J_t=j$ has its two sampled actions in the same level-$j$ parent class. On those outcomes, \cref{lem:parent-common-loss-difference-bound} and the shift hypothesis imply
  $0\leq L_{t,j}\leq2\sigma_j$. Each centered importance-weight term is linear in $L_{t,j}$ before it is squared. Thus $L_{t,j}^2\leq(2\sigma_j)^2$, and the nonnegative subtree coefficients give a pointwise almost-everywhere bound of the left-hand integrand by $H$.

  If the left-hand integrand is integrable, monotonicity of the Bochner integral, the identity $\int H=\int K$, and the preceding pointwise bound on $K$ prove the claim. If it is not integrable, its Bochner integral is zero. Every summand $\sqrt{P_v}-P_v$ is nonnegative by \cref{lem:subtree-mass-level-probability}; since the coefficient is nonnegative, the right-hand side is nonnegative, and the claim follows in this case as well. -/)
  (title := /-- Conditional integration of the sampled-subtree variance -/)
  (latexEnv := "lemma")]
lemma sampled_subtree_centered_variance_integral
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M)
    (t : ℕ) (j : Fin M.depth) (hshift : ∀ k, run.shift k = M.scale k) :
    (∫ ω,
      if M.sampledLevel t ω = j then
        ∑ v ∈ M.levelNodes j,
          (subtree_mass M (run.distribution t ω) v *
              Real.sqrt (subtree_mass M (run.distribution t ω) v)) *
            ((@ite ℝ (M.descends v (M.firstAction t ω))
                (M.descends_decidable v (M.firstAction t ω))
                ((M.loss t ω (M.firstAction t ω) -
                      M.loss t ω (M.secondAction t ω) + run.shift j) /
                    (M.delta j * subtree_mass M (run.distribution t ω) v))
                0) -
              (M.loss t ω (M.firstAction t ω) -
                  M.loss t ω (M.secondAction t ω) + run.shift j) /
                M.delta j) ^ 2
      else 0 ∂M.measure) ≤
      ((8 * (M.scale j) ^ 2) / M.delta j) *
        ∫ ω, ∑ v ∈ M.levelNodes j,
          (Real.sqrt (subtree_mass M (run.distribution t ω) v) -
            subtree_mass M (run.distribution t ω) v) ∂M.measure := by
  classical
  letI := M.probability_measure
  let P : Ω → Node → ℝ := fun ω v => subtree_mass M (run.distribution t ω) v
  let L : Ω → ℝ := fun ω => M.loss t ω (M.firstAction t ω) -
    M.loss t ω (M.secondAction t ω) + run.shift j
  let F : Ω → Action → ℝ := fun ω a =>
    ∑ v ∈ M.levelNodes j, (P ω v * Real.sqrt (P ω v)) *
      ((@ite ℝ (M.descends v a) (M.descends_decidable v a)
          ((2 * M.scale j) / (M.delta j * P ω v)) 0) -
        (2 * M.scale j) / M.delta j) ^ 2
  let H : Ω → ℝ := fun ω =>
    if M.sampledLevel t ω = j then F ω (M.firstAction t ω) else 0
  let K : Ω → ℝ := fun ω =>
    M.delta j * ∑ a, run.distribution t ω a * F ω a
  let Gap : Ω → ℝ := fun ω =>
    ∑ v ∈ M.levelNodes j, (Real.sqrt (P ω v) - P ω v)
  let C : ℝ := (8 * (M.scale j) ^ 2) / M.delta j
  have hPmeas : ∀ v, @Measurable Ω ℝ (M.history t) inferInstance
      (fun ω => P ω v) := by
    intro v
    simp only [P, subtree_mass]
    apply Finset.measurable_sum
    intro a ha
    by_cases hva : M.descends v a
    · simpa [hva] using run.distribution_measurable t a
    · simp [hva]
  have hFmeas : ∀ a, @MeasureTheory.StronglyMeasurable Ω ℝ inferInstance
      (M.history t) (fun ω => F ω a) := by
    intro a
    apply Measurable.stronglyMeasurable
    simp only [F]
    apply Finset.measurable_sum
    intro v hv
    apply Measurable.mul
    · exact (hPmeas v).mul (hPmeas v).sqrt
    · apply Measurable.pow_const
      apply Measurable.sub
      · by_cases hva : M.descends v a
        · simp only [hva, if_true]
          exact measurable_const.div (measurable_const.mul (hPmeas v))
        · simp [hva]
      · exact measurable_const
  have hFnonneg : ∀ ω a, 0 ≤ F ω a := by
    intro ω a
    apply Finset.sum_nonneg
    intro v hv
    have hPv := (subtree_mass_level_probability M (run.distribution t ω)
      (run.distribution_mem t ω) j).1 v hv
    exact mul_nonneg (mul_nonneg hPv (Real.sqrt_nonneg _)) (sq_nonneg _)
  have hKmeas : Measurable K := by
    have hsum : @Measurable Ω ℝ (M.history t) inferInstance
        (fun ω => ∑ a, run.distribution t ω a * F ω a) := by
      apply Finset.measurable_sum
      intro a ha
      exact (run.distribution_measurable t a).mul (hFmeas a).measurable
    exact (hsum.const_mul (M.delta j)).mono (M.history.le t) le_rfl
  have hKnonneg : ∀ ω, 0 ≤ K ω := by
    intro ω
    exact mul_nonneg (le_of_lt (M.delta_positive j))
      (Finset.sum_nonneg (fun a ha =>
        mul_nonneg ((run.distribution_mem t ω).1 a) (hFnonneg ω a)))
  have hKle : ∀ ω, K ω ≤ C * Gap ω := by
    intro ω
    convert two_point_action_centered_variance_bound M (run.distribution t ω)
      (run.distribution_mem t ω) j using 1
  have hGapint : MeasureTheory.Integrable Gap M.measure := by
    simpa only [Gap, P] using nested_tsallis_level_gap_integrable M run t j
  have hCnonneg : 0 ≤ C := by
    exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (le_of_lt (M.delta_positive j))
  have hCGint : MeasureTheory.Integrable (fun ω => C * Gap ω) M.measure :=
    hGapint.const_mul C
  have hKint : MeasureTheory.Integrable K M.measure :=
    hCGint.mono_nonneg hKmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hKnonneg)
      (Filter.Eventually.of_forall hKle)
  have hsample := sampled_level_nonnegative_weight_integral M run t j F hFmeas
    hFnonneg hKint
  have hHint : MeasureTheory.Integrable H M.measure := by
    simpa only [H] using hsample.1
  have hHintegral : (∫ ω, H ω ∂M.measure) = ∫ ω, K ω ∂M.measure := by
    simpa only [H, K] using hsample.2
  have hall : ∀ᵐ ω ∂M.measure, ∀ a ∈ (Finset.univ : Finset Action),
      ∀ b ∈ (Finset.univ : Finset Action),
        M.parentCommonAtLevel j a b ∨
          ¬(M.firstAction t ω = a ∧ M.sampledLevel t ω = j ∧
            M.secondAction t ω = b) := by
    rw [Filter.eventually_all_finset]
    intro a ha
    rw [Filter.eventually_all_finset]
    intro b hb
    by_cases hab : M.parentCommonAtLevel j a b
    · exact Filter.Eventually.of_forall (fun ω => Or.inl hab)
    · exact (feedback_atom_null_of_not_parent_common M run t a j b hab).mono
        (fun ω hω => Or.inr hω)
  have hvalid : ∀ᵐ ω ∂M.measure, M.sampledLevel t ω = j →
      M.parentCommonAtLevel j (M.firstAction t ω) (M.secondAction t ω) := by
    filter_upwards [hall] with ω hω
    intro hjω
    by_contra hbad
    rcases hω (M.firstAction t ω) (Finset.mem_univ _)
        (M.secondAction t ω) (Finset.mem_univ _) with hparent | hnull
    · exact hbad hparent
    · exact hnull ⟨rfl, hjω, rfl⟩
  have hGHle : ∀ᵐ ω ∂M.measure,
      (if M.sampledLevel t ω = j then
        ∑ v ∈ M.levelNodes j, (P ω v * Real.sqrt (P ω v)) *
          ((@ite ℝ (M.descends v (M.firstAction t ω))
              (M.descends_decidable v (M.firstAction t ω))
              (L ω / (M.delta j * P ω v)) 0) - L ω / M.delta j) ^ 2
        else 0) ≤ H ω := by
    filter_upwards [hvalid] with ω hvalidω
    by_cases hjω : M.sampledLevel t ω = j
    · simp only [hjω, if_true, H, F]
      have hparent := hvalidω hjω
      apply Finset.sum_le_sum
      intro v hv
      have hPv := (subtree_mass_level_probability M (run.distribution t ω)
        (run.distribution_mem t ω) j).1 v hv
      have hQ : 0 ≤ P ω v * Real.sqrt (P ω v) :=
        mul_nonneg hPv (Real.sqrt_nonneg _)
      have habs := parent_common_loss_difference_bound M t ω j
        (M.firstAction t ω) (M.secondAction t ω) hparent
      have hdiff := abs_le.mp habs
      have hL0 : 0 ≤ L ω := by
        dsimp [L]
        rw [hshift j]
        linarith
      have hLupper : L ω ≤ 2 * M.scale j := by
        dsimp [L]
        rw [hshift j]
        linarith
      have hLsq : (L ω) ^ 2 ≤ (2 * M.scale j) ^ 2 := by
        nlinarith [M.scale_nonnegative j]
      let r : ℝ :=
        (@ite ℝ (M.descends v (M.firstAction t ω))
          (M.descends_decidable v (M.firstAction t ω))
          (1 / (M.delta j * P ω v)) 0) - 1 / M.delta j
      have hfactorL :
          ((@ite ℝ (M.descends v (M.firstAction t ω))
              (M.descends_decidable v (M.firstAction t ω))
              (L ω / (M.delta j * P ω v)) 0) - L ω / M.delta j) ^ 2 =
            (L ω) ^ 2 * r ^ 2 := by
        dsimp [r]
        by_cases hvd : M.descends v (M.firstAction t ω) <;>
          simp [hvd] <;> ring
      have hfactorC :
          ((@ite ℝ (M.descends v (M.firstAction t ω))
              (M.descends_decidable v (M.firstAction t ω))
              ((2 * M.scale j) / (M.delta j * P ω v)) 0) -
            (2 * M.scale j) / M.delta j) ^ 2 =
            (2 * M.scale j) ^ 2 * r ^ 2 := by
        dsimp [r]
        by_cases hvd : M.descends v (M.firstAction t ω) <;>
          simp [hvd] <;> ring
      rw [hfactorL, hfactorC]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hLsq (sq_nonneg r)) hQ
    · simp [H, hjω]
  have hGapnonneg : ∀ ω, 0 ≤ Gap ω := by
    intro ω
    apply Finset.sum_nonneg
    intro v hv
    have hpv := (subtree_mass_level_probability M (run.distribution t ω)
      (run.distribution_mem t ω) j)
    have hp0 := hpv.1 v hv
    have hp1 : P ω v ≤ 1 := by
      change subtree_mass M (run.distribution t ω) v ≤ 1
      rw [← hpv.2]
      exact Finset.single_le_sum (fun w hw => hpv.1 w hw) hv
    have hs0 := Real.sqrt_nonneg (P ω v)
    have hs1 := Real.sqrt_le_one.mpr hp1
    have hs2 := Real.sq_sqrt hp0
    nlinarith
  change (∫ ω, if M.sampledLevel t ω = j then
      ∑ v ∈ M.levelNodes j, (P ω v * Real.sqrt (P ω v)) *
        ((@ite ℝ (M.descends v (M.firstAction t ω))
            (M.descends_decidable v (M.firstAction t ω))
            (L ω / (M.delta j * P ω v)) 0) - L ω / M.delta j) ^ 2
      else 0 ∂M.measure) ≤ C * ∫ ω, Gap ω ∂M.measure
  by_cases hGint : MeasureTheory.Integrable
      (fun ω => if M.sampledLevel t ω = j then
        ∑ v ∈ M.levelNodes j, (P ω v * Real.sqrt (P ω v)) *
          ((@ite ℝ (M.descends v (M.firstAction t ω))
              (M.descends_decidable v (M.firstAction t ω))
              (L ω / (M.delta j * P ω v)) 0) - L ω / M.delta j) ^ 2
        else 0) M.measure
  · calc
      (∫ ω, if M.sampledLevel t ω = j then
          ∑ v ∈ M.levelNodes j, (P ω v * Real.sqrt (P ω v)) *
            ((@ite ℝ (M.descends v (M.firstAction t ω))
                (M.descends_decidable v (M.firstAction t ω))
                (L ω / (M.delta j * P ω v)) 0) - L ω / M.delta j) ^ 2
          else 0 ∂M.measure) ≤ ∫ ω, H ω ∂M.measure :=
        MeasureTheory.integral_mono_ae hGint hHint hGHle
      _ = ∫ ω, K ω ∂M.measure := hHintegral
      _ ≤ ∫ ω, C * Gap ω ∂M.measure :=
        MeasureTheory.integral_mono_ae hKint hCGint
          (Filter.Eventually.of_forall hKle)
      _ = C * ∫ ω, Gap ω ∂M.measure := by
        rw [MeasureTheory.integral_const_mul]
  · rw [MeasureTheory.integral_undef hGint]
    exact mul_nonneg hCnonneg
      (MeasureTheory.integral_nonneg_of_ae
        (Filter.Eventually.of_forall hGapnonneg))

@[blueprint "lem:tsallis-bregman-stability-bound"
  (statement := /-- Let $\eta,p,q,c,y\in\mathbb R$ satisfy $\eta>0$, $p>0$, $q\geq0$, $c>1$, and $y\geq-1/(c\eta\sqrt p)$. Then
  \[
  y(p-q)+\left(\frac2\eta-\frac1{\eta\sqrt p}\right)(q-p)
  -\frac2\eta\bigl((q-\sqrt q)-(p-\sqrt p)\bigr)
  \leq \frac{c}{c-1}\eta p\sqrt p\,y^2.
  \] -/)
  (proof := /-- Put $A=y+(\eta\sqrt p)^{-1}$. The positivity conclusion of \cref{lem:tsallis-conjugate-divergence-bound} gives $A>0$. Expanding the nonnegative square $(A\sqrt q-\eta^{-1})^2$ yields
  \[
  -Aq+\frac2\eta\sqrt q\leq\frac1{\eta^2A}.
  \]
  After collecting terms, the left-hand side of the claimed inequality is $yp-\sqrt p/\eta-Aq+2\sqrt q/\eta$. The rational expression in \cref{lem:tsallis-conjugate-divergence-bound} is $yp-\sqrt p/\eta+1/(\eta^2A)$, so the completed-square estimate followed by that lemma proves the result. -/)
  (title := /-- Scalar Tsallis Bregman stability bound -/)
  (latexEnv := "lemma")]
lemma tsallis_bregman_stability_bound
    (η p q c y : ℝ) (hη : 0 < η) (hp : 0 < p) (hq : 0 ≤ q)
    (hc : 1 < c) (hy : -1 / (c * η * Real.sqrt p) ≤ y) :
    y * (p - q) +
        (2 / η - 1 / (η * Real.sqrt p)) * (q - p) -
        (2 / η) * ((q - Real.sqrt q) - (p - Real.sqrt p)) ≤
      (c / (c - 1)) * η * p * Real.sqrt p * y ^ 2 := by
  rcases tsallis_conjugate_divergence_bound η p c y hη hp hc hy with
    ⟨hpos, _heq, hle⟩
  have hsqrtp : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
  let A : ℝ := y + 1 / (η * Real.sqrt p)
  have hAeq : A = (1 + η * y * Real.sqrt p) / (η * Real.sqrt p) := by
    dsimp [A]
    field_simp
    <;> ring
  have hA : 0 < A := by
    rw [hAeq]
    exact div_pos hpos (mul_pos hη hsqrtp)
  have hfenchel : -A * q + (2 / η) * Real.sqrt q ≤ 1 / (η ^ 2 * A) := by
    have hs := sq_nonneg (A * Real.sqrt q - 1 / η)
    have hη0 : η ≠ 0 := ne_of_gt hη
    have hsqroot : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq
    apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hη) hA)).2
    field_simp at hs ⊢
    ring_nf at hs
    rw [hsqroot] at hs
    nlinarith
  have hleft :
      y * (p - q) +
          (2 / η - 1 / (η * Real.sqrt p)) * (q - p) -
          (2 / η) * ((q - Real.sqrt q) - (p - Real.sqrt p)) =
        y * p - Real.sqrt p / η + (-A * q + (2 / η) * Real.sqrt q) := by
    dsimp [A]
    field_simp
    nlinarith [Real.sq_sqrt hp.le]
  have hden1 :
      η * (2 - η * ((2 / η - 1 / (η * Real.sqrt p)) - y)) = η ^ 2 * A := by
    dsimp [A]
    field_simp
    ring
  have hden0 :
      η * (2 - η * (2 / η - 1 / (η * Real.sqrt p))) = η / Real.sqrt p := by
    field_simp
    ring
  have hinv0 : 1 / (η / Real.sqrt p) = Real.sqrt p / η := by
    field_simp
  have hboundD :
      y * (p - q) +
          (2 / η - 1 / (η * Real.sqrt p)) * (q - p) -
          (2 / η) * ((q - Real.sqrt q) - (p - Real.sqrt p)) ≤
        y * p +
          1 / (η * (2 - η * ((2 / η - 1 / (η * Real.sqrt p)) - y))) -
          1 / (η * (2 - η * (2 / η - 1 / (η * Real.sqrt p)))) := by
    rw [hleft, hden1, hden0, hinv0]
    linarith
  exact le_trans hboundD hle

@[blueprint "lem:nested-tsallis-level-gap-bound"
  (statement := /-- Let $M$ be a hierarchical two-point bandit, let $x\in\Delta_{\mathcal A}$, and fix a level $j$. Then
  \[
  \sum_{v\in V_j}\bigl(\sqrt{x[v]}-x[v]\bigr)\leq\sqrt{|V_j|}.
  \] -/)
  (proof := /-- By \cref{lem:subtree-mass-level-probability}, the numbers $x[v]$, for $v\in V_j$, are nonnegative and sum to one. Cauchy--Schwarz and $(\sqrt{x[v]})^2=x[v]$ give
  \[
  \left(\sum_{v\in V_j}\sqrt{x[v]}\right)^2
  \leq |V_j|\sum_{v\in V_j}x[v]=|V_j|.
  \]
  Hence $\sum_v\sqrt{x[v]}\leq\sqrt{|V_j|}$. Subtracting $\sum_vx[v]=1$ and then discarding the nonpositive term $-1$ proves the claim. -/)
  (title := /-- Cardinality bound for a nested-Tsallis level gap -/)
  (latexEnv := "lemma")]
lemma nested_tsallis_level_gap_bound
    (M : hierarchical_two_point_bandit Action Node Ω) (x : Action → ℝ)
    (hx : probability_vector x) (j : Fin M.depth) :
    (∑ v ∈ M.levelNodes j,
      (Real.sqrt (subtree_mass M x v) - subtree_mass M x v)) ≤
        Real.sqrt ((M.levelNodes j).card : ℝ) := by
  classical
  have hmass := subtree_mass_level_probability M x hx j
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (M.levelNodes j)
    (fun _ => (1 : ℝ)) (fun v => Real.sqrt (subtree_mass M x v))
  have hsq : (∑ v ∈ M.levelNodes j, Real.sqrt (subtree_mass M x v)) ^ 2 ≤
      ((M.levelNodes j).card : ℝ) := by
    calc
      (∑ v ∈ M.levelNodes j, Real.sqrt (subtree_mass M x v)) ^ 2 =
          (∑ v ∈ M.levelNodes j,
            (1 : ℝ) * Real.sqrt (subtree_mass M x v)) ^ 2 := by simp
      _ ≤ (∑ v ∈ M.levelNodes j, (1 : ℝ) ^ 2) *
            ∑ v ∈ M.levelNodes j,
              (Real.sqrt (subtree_mass M x v)) ^ 2 := hcs
      _ = ((M.levelNodes j).card : ℝ) *
            ∑ v ∈ M.levelNodes j, subtree_mass M x v := by
        rw [show (∑ _v ∈ M.levelNodes j, (1 : ℝ) ^ 2) =
          ((M.levelNodes j).card : ℝ) by simp]
        congr 1
        apply Finset.sum_congr rfl
        intro v hv
        exact Real.sq_sqrt (hmass.1 v hv)
      _ = ((M.levelNodes j).card : ℝ) := by rw [hmass.2, mul_one]
  have hsqrt_sum :
      (∑ v ∈ M.levelNodes j, Real.sqrt (subtree_mass M x v)) ≤
        Real.sqrt ((M.levelNodes j).card : ℝ) := Real.le_sqrt_of_sq_le hsq
  rw [Finset.sum_sub_distrib, hmass.2]
  linarith

@[blueprint "lem:right-derivative-nonnegative-at-interval-min"
  (statement := /-- Let $f\colon\mathbb R\to\mathbb R$ attain its minimum on $[0,1]$ at $0$. If $f$ has right derivative $d$ at $0$ relative to $[0,1]$, then $d\geq0$. -/)
  (proof := /-- Restrict the derivative to $(0,1]$. If $d<0$, the little-$o$ remainder in the derivative expansion is bounded in norm by $(-d/2)|r|$ for all sufficiently small $r\in(0,1]$. Such positive $r$ exist because $0$ lies in the closure of $(0,1]$. The expansion then gives $f(r)-f(0)<0$, contradicting the assumed minimality of $f$ on $[0,1]$. -/)
  (title := /-- Nonnegativity of a right derivative at an interval minimum -/)
  (latexEnv := "lemma")]
lemma right_derivative_nonnegative_at_interval_min
    (f : ℝ → ℝ) (d : ℝ) (hmin : IsMinOn f (Set.Icc 0 1) 0)
    (hderiv : HasDerivWithinAt f d (Set.Icc 0 1) 0) : 0 ≤ d := by
  by_contra hd
  have hdneg : d < 0 := lt_of_not_ge hd
  have hopen : HasDerivWithinAt f d (Set.Ioc 0 1) 0 :=
    hderiv.mono fun r hr => ⟨hr.1.le, hr.2⟩
  have hepsilon : 0 < -d / 2 := by linarith
  have herr := hopen.isLittleO.bound hepsilon
  have hdomain : ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioc 0 1),
      r ∈ Set.Ioc (0 : ℝ) 1 := self_mem_nhdsWithin
  have hboth : ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioc 0 1),
      ‖f r - f 0 - (r - 0) • d‖ ≤ (-d / 2) * ‖r - 0‖ ∧
        r ∈ Set.Ioc (0 : ℝ) 1 := by
    filter_upwards [herr, hdomain] with r hr hs
    exact ⟨hr, hs⟩
  letI : (nhdsWithin (0 : ℝ) (Set.Ioc 0 1)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (by
      rw [closure_Ioc (by norm_num)]
      simp)
  rcases Filter.Eventually.exists hboth with ⟨r, hrerr, hrpos, hrle⟩
  have hrerr' : |f r - f 0 - r * d| ≤ (-d / 2) * r := by
    simpa [Real.norm_eq_abs, smul_eq_mul, abs_of_pos hrpos] using hrerr
  have hupper : f r - f 0 - r * d ≤ (-d / 2) * r :=
    le_trans (le_abs_self _) hrerr'
  have hrdneg : r * d < 0 := mul_neg_of_pos_of_neg hrpos hdneg
  have hminr := hmin ⟨hrpos.le, hrle⟩
  change f 0 ≤ f r at hminr
  linarith

@[blueprint "lem:nested-tsallis-objective-gap"
  (statement := /-- Let $M$ be a hierarchical two-point bandit, let $\rho$ be a two-point FTRL run on $M$, let $c\in\mathbb R$ satisfy $c\geq2$, and let $T\in\mathbb N$ satisfy $T\geq1$. Assume that, for every integer $t\geq1$ and every $x\in\Delta_{\mathcal A}$, the regularizer of $\rho$ at time $t$ and $x$ is $\Psi_t^{(c)}(x)$, and that the shift at every level $j$ is $b_j=\sigma_j$. Write $p_t$ and $z_t$ for the distribution and estimated loss of $\rho$ at time $t$, respectively, and let $a_T^*$ be the expected-loss-minimizing fixed action of $M$ at horizon $T$. Then
  \[
  \mathbb E\!\left[
    \sum_{t<T}\sum_{a\in\mathcal A}
    z_t(a)\bigl(p_t(a)-\mathbf 1_{\{a=a_T^*\}}\bigr)
  \right]
  \leq
  \frac{8\sqrt c}{\sqrt{c-1}}
  \sum_{t<T}\frac1{\sqrt{t+1}}
  \sum_j\frac{\sigma_j}{\sqrt{\delta_j}}
  \mathbb E\sum_{v\in V_j}(\sqrt{p_t[v]}-p_t[v])
  +6c\sum_j\frac{\sigma_j}{\delta_j}\sqrt{|V_j|}.
  \]
  -/)
  (proof := /-- Let $q_T$ be the probability vector concentrated at $a_T^*$. Define
  \[
  W_{s,j}=\frac{4\sqrt c}{\sqrt{c-1}}
    \frac{\sigma_j}{\sqrt{\delta_j}}
    \sqrt{\max\{s,c(c-1)/\delta_j\}}.
  \]
  The regularizer hypothesis expresses the level-$j$ part of
  $\Psi_s^{(c)}$ as $W_{s,j}\sum_v(x[v]-\sqrt{x[v]})$.
  The initial weight is nonnegative by
  \cref{lem:nonnegative-first-level-weight}; the same sign calculation with
  the nonnegative square-root maximum handles every later weight.
  By \cref{lem:subtree-mass-level-probability}, the subtree masses at each
  level are nonnegative and sum to one. If $W_{s,j}>0$, every level-$j$
  subtree mass of an FTRL minimizer is positive. Indeed, from a zero-mass
  subtree choose an action descending from it and perturb the minimizer
  toward the corresponding point mass along a squared parameter. The
  one-sided derivative of the regularizer is then strictly negative, whereas
  minimality and \cref{lem:right-derivative-nonnegative-at-interval-min}
  make the derivative nonnegative, a contradiction. Ordinary affine
  perturbations toward an arbitrary probability vector therefore give the
  constrained first-order inequality; zero-weight levels contribute zero.

  Introduce the centered level-subtree feedback atoms $Y_{t,j,v}$. Expanding
  the estimator gives
  \[
  \langle z_t,p_t-q_T\rangle
  =\sum_{j,v}Y_{t,j,v}\bigl(p_t[v]-q_T[v]\bigr).
  \]
  Terms outside the sampled parent class vanish by
  \cref{lem:feedback-atom-null-of-not-parent-common}. On the almost-sure
  compatibility event, \cref{lem:parent-common-loss-difference-bound} and
  the prescribed shifts put the sampled shifted loss in $[0,2\sigma_j]$.
  Applying \cref{lem:tsallis-bregman-stability-bound} to every positive
  subtree mass and summing the first-order inequalities bounds the
  one-step objective gap by
  \[
  \sum_j\frac{c}{c-1}\frac{2}{W_{t+1,j}}
    \sum_v p_t[v]^{3/2}Y_{t,j,v}^2.
  \]

  Apply \cref{lem:nested-tsallis-ftrl-decomposition} pointwise with
  comparator $q_T$. Its final comparator regularizer is zero, and the
  remaining regularizer terms are the initial level gaps and the increments
  $W_{t+2,j}-W_{t+1,j}$. The level-gap random variables are integrable by
  \cref{lem:nested-tsallis-level-gap-integrable}, while the run's
  integrability hypotheses handle the centered variance terms; hence finite
  linearity and monotonicity of the Bochner integral apply. The conditional
  sampling calculation in
  \cref{lem:sampled-subtree-centered-variance-integral} bounds each
  integrated centered variance by
  $(8\sigma_j^2/\delta_j)$ times the corresponding integrated level gap.
  Direct simplification of $W_{t+1,j}$ then gives the variance coefficient
  $4\sqrt c/(\sqrt{c-1}\sqrt{t+1})$.

  Finally, $W_{1,j}=4c\sigma_j/\delta_j$. Split the drift sum after its
  penultimate index. Its terminal term is at most
  $2c\sigma_j/\delta_j$ times the horizon-$T$ gap. For every remaining
  term, the square-root increment estimate and
  $1/\sqrt s\leq2/\sqrt{s+1}$ give coefficient at most
  $4\sqrt c/(\sqrt{c-1}\sqrt{s+1})$; reindexing embeds these terms in the
  displayed time sum. By \cref{lem:nested-tsallis-level-gap-bound}, every
  integrated level gap is at most $\sqrt{|V_j|}$. Thus the initial and
  terminal terms total $6c\sum_j(\sigma_j/\delta_j)\sqrt{|V_j|}$, and
  the drift and variance terms total
  $8\sqrt c/\sqrt{c-1}$ times the displayed weighted level-gap sum. -/)
  (title := /-- Constrained nested-Tsallis objective-gap estimate -/)
  (latexEnv := "lemma")]
lemma nested_tsallis_objective_gap
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M)
    (c : ℝ) (T : ℕ) (hc : 2 ≤ c) (hT : 1 ≤ T)
    (hregularizer :
      ∀ t x, 1 ≤ t → probability_vector x →
        run.regularizer t x = generic_nested_tsallis_regularizer M c t x)
    (hshift : ∀ j, run.shift j = M.scale j) :
    (∫ ω, ∑ t ∈ Finset.range T, ∑ a,
        run.estimatedLoss t ω a *
          (run.distribution t ω a - if a = M.bestAction T then 1 else 0)
      ∂M.measure) ≤
      (8 * Real.sqrt c / Real.sqrt (c - 1)) *
        ∑ t ∈ Finset.range T,
          (1 / Real.sqrt ((t + 1 : ℕ) : ℝ)) *
            ∑ j,
              (M.scale j / Real.sqrt (M.delta j)) *
                ∫ ω, ∑ v ∈ M.levelNodes j,
                  (Real.sqrt (subtree_mass M (run.distribution t ω) v) -
                    subtree_mass M (run.distribution t ω) v) ∂M.measure
      + 6 * c *
          ∑ j, (M.scale j / M.delta j) *
            Real.sqrt ((M.levelNodes j).card : ℝ) := by
  classical
  have hmass_line (p q : Action → ℝ) (v : Node) (r : ℝ) :
      subtree_mass M (fun a => p a + r * (q a - p a)) v =
        subtree_mass M p v + r * (subtree_mass M q v - subtree_mass M p v) := by
    simp only [subtree_mass]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : M.descends v a <;> simp [h]
  have hphi (p q : Action → ℝ) (v : Node) (hpv : 0 < subtree_mass M p v) :
      HasDerivAt
        (fun r : ℝ =>
          subtree_mass M (fun a => p a + r * (q a - p a)) v -
            Real.sqrt (subtree_mass M (fun a => p a + r * (q a - p a)) v))
        ((subtree_mass M q v - subtree_mass M p v) -
          (subtree_mass M q v - subtree_mass M p v) /
            (2 * Real.sqrt (subtree_mass M p v))) 0 := by
    simp only [hmass_line]
    have hm : HasDerivAt
        (fun r : ℝ => subtree_mass M p v + r *
          (subtree_mass M q v - subtree_mass M p v))
        (subtree_mass M q v - subtree_mass M p v) 0 := by
      rw [show (fun r : ℝ => subtree_mass M p v + r *
          (subtree_mass M q v - subtree_mass M p v)) =
        fun r : ℝ => r * (subtree_mass M q v - subtree_mass M p v) +
          subtree_mass M p v by funext r; ring]
      unfold HasDerivAt HasDerivAtFilter
      exact (hasDerivAt_mul_const (x := (0 : ℝ))
        (subtree_mass M q v - subtree_mass M p v)).add_const
          (subtree_mass M p v)
    have hne : subtree_mass M p v + 0 *
        (subtree_mass M q v - subtree_mass M p v) ≠ 0 := by
      simpa using ne_of_gt hpv
    have hsqrt : HasDerivAt
        (fun r : ℝ => Real.sqrt (subtree_mass M p v +
          r * (subtree_mass M q v - subtree_mass M p v)))
        ((subtree_mass M q v - subtree_mass M p v) /
          (2 * Real.sqrt (subtree_mass M p v))) 0 := by
      simpa only [zero_mul, add_zero] using hm.sqrt hne
    have hraw0 : HasDerivAt
        (fun r : ℝ =>
          (subtree_mass M p v + r * (subtree_mass M q v - subtree_mass M p v)) -
            Real.sqrt (subtree_mass M p v +
              r * (subtree_mass M q v - subtree_mass M p v)))
        ((subtree_mass M q v - subtree_mass M p v) -
          (subtree_mass M q v - subtree_mass M p v) /
            (2 * Real.sqrt (subtree_mass M p v))) 0 := by
      unfold HasDerivAt HasDerivAtFilter
      convert hm.sub hsqrt using 1 <;> try rfl
      apply ContinuousLinearMap.ext
      intro z
      simp only [ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
      ring
    exact hraw0
  have hpoint_mass (a : Action) (v : Node) :
      subtree_mass M (fun b => if b = a then 1 else 0) v =
        if M.descends v a then 1 else 0 := by
    simp only [subtree_mass]
    by_cases h : M.descends v a
    · rw [Finset.sum_eq_single a]
      · simp [h]
      · intro b hb hba
        simp [hba]
      · simp
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro b hb
      by_cases hba : b = a
      · subst b
        simp [h]
      · simp [hba]
  have hpoly : HasDerivAt (fun r : ℝ => r ^ 2 - r) (-1) 0 := by
    unfold HasDerivAt HasDerivAtFilter
    convert (hasDerivAt_pow 2 (0 : ℝ)).sub (hasDerivAt_id (x := (0 : ℝ))) using 1 <;>
      try norm_num <;> try rfl
    apply ContinuousLinearMap.ext
    intro z
    simp
  have hphi_sq_zero (p : Action → ℝ) (a : Action) (v : Node)
      (hpv : subtree_mass M p v = 0) :
      HasDerivWithinAt
        (fun r : ℝ =>
          subtree_mass M
              (fun b => p b + r ^ 2 * ((if b = a then 1 else 0) - p b)) v -
            Real.sqrt (subtree_mass M
              (fun b => p b + r ^ 2 * ((if b = a then 1 else 0) - p b)) v))
        (if M.descends v a then -1 else 0) (Set.Icc 0 1) 0 := by
    by_cases hdesc : M.descends v a
    · have heq : ∀ r ∈ Set.Icc (0 : ℝ) 1,
          subtree_mass M
                (fun b => p b + r ^ 2 * ((if b = a then 1 else 0) - p b)) v -
              Real.sqrt (subtree_mass M
                (fun b => p b + r ^ 2 * ((if b = a then 1 else 0) - p b)) v) =
            r ^ 2 - r := by
        intro r hr
        rw [hmass_line, hpv, hpoint_mass]
        simp only [hdesc, if_true, sub_zero, zero_add, mul_one]
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hr.1]
      have hbase : HasDerivWithinAt (fun r : ℝ => r ^ 2 - r) (-1)
          (Set.Icc 0 1) 0 := hpoly.hasDerivWithinAt
      simpa only [hdesc, if_true] using hbase.congr heq (by simp [hpv, hpoint_mass, hdesc])
    · have heq : ∀ r ∈ Set.Icc (0 : ℝ) 1,
          subtree_mass M
                (fun b => p b + r ^ 2 * ((if b = a then 1 else 0) - p b)) v -
              Real.sqrt (subtree_mass M
                (fun b => p b + r ^ 2 * ((if b = a then 1 else 0) - p b)) v) = 0 := by
        intro r hr
        rw [hmass_line, hpv, hpoint_mass]
        simp [hdesc]
      have hbase : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Set.Icc 0 1) 0 :=
        (hasDerivAt_const (x := (0 : ℝ)) (0 : ℝ)).hasDerivWithinAt
      simpa only [hdesc, if_false] using hbase.congr heq (by simp [hpv, hpoint_mass, hdesc])
  let W : ℕ → Fin M.depth → ℝ := fun s j =>
    (4 * Real.sqrt c / Real.sqrt (c - 1)) *
      (M.scale j / Real.sqrt (M.delta j)) *
        Real.sqrt (max (s : ℝ) (c * (c - 1) / M.delta j))
  have hW_nonneg (s : ℕ) (j : Fin M.depth) : 0 ≤ W s j := by
    by_cases hs : s = 1
    · subst s
      simpa [W] using nonnegative_first_level_weight M c hc j
    · dsimp [W]
      exact mul_nonneg
        (mul_nonneg
          (le_of_lt (div_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 (by linarith)))
            (Real.sqrt_pos.2 (by linarith))))
          (div_nonneg (M.scale_nonnegative j) (Real.sqrt_nonneg _)))
        (Real.sqrt_nonneg _)
  have hW_pos (s : ℕ) (j : Fin M.depth) (hs : 1 ≤ s)
      (hscale : 0 < M.scale j) : 0 < W s j := by
    dsimp [W]
    have hc1 : 0 < c - 1 := by linarith
    have hmax : 0 < max (s : ℝ) (c * (c - 1) / M.delta j) := by
      exact lt_of_lt_of_le (by exact_mod_cast hs) (le_max_left _ _)
    exact mul_pos
      (mul_pos
        (div_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 (by linarith)))
          (Real.sqrt_pos.2 hc1))
        (div_pos hscale (Real.sqrt_pos.2 (M.delta_positive j))))
      (Real.sqrt_pos.2 hmax)
  have hregularizer_sum (s : ℕ) (x : Action → ℝ) :
      generic_nested_tsallis_regularizer M c s x =
        ∑ j, W s j * ∑ v ∈ M.levelNodes j,
          (subtree_mass M x v - Real.sqrt (subtree_mass M x v)) := by
    rw [generic_nested_tsallis_regularizer, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [W]
    ring
  have hderivWithin_sum_node (s : Finset Node) (f : Node → ℝ → ℝ) (d : Node → ℝ)
      (hf : ∀ i ∈ s, HasDerivWithinAt (f i) (d i) (Set.Icc 0 1) 0) :
      HasDerivWithinAt (fun r => ∑ i ∈ s, f i r) (∑ i ∈ s, d i)
        (Set.Icc 0 1) 0 := by
    unfold HasDerivWithinAt HasDerivAtFilter
    convert HasFDerivAtFilter.sum (u := s) (fun i hi => hf i hi) using 1 <;> try rfl
    · funext r
      simp
    · apply ContinuousLinearMap.ext
      intro z
      simp [Finset.mul_sum]
  have hderivWithin_sum_action (f : Action → ℝ → ℝ) (d : Action → ℝ)
      (hf : ∀ i, HasDerivWithinAt (f i) (d i) (Set.Icc 0 1) 0) :
      HasDerivWithinAt (fun r => ∑ i, f i r) (∑ i, d i)
        (Set.Icc 0 1) 0 := by
    unfold HasDerivWithinAt HasDerivAtFilter
    convert HasFDerivAtFilter.sum (u := Finset.univ) (fun i hi => hf i) using 1 <;> try rfl
    · funext r
      simp
    · apply ContinuousLinearMap.ext
      intro z
      simp [Finset.mul_sum]
  have hderivWithin_sum_level (f : Fin M.depth → ℝ → ℝ) (d : Fin M.depth → ℝ)
      (hf : ∀ i, HasDerivWithinAt (f i) (d i) (Set.Icc 0 1) 0) :
      HasDerivWithinAt (fun r => ∑ i, f i r) (∑ i, d i)
        (Set.Icc 0 1) 0 := by
    unfold HasDerivWithinAt HasDerivAtFilter
    convert HasFDerivAtFilter.sum (u := Finset.univ) (fun i hi => hf i) using 1 <;> try rfl
    · funext r
      simp
    · apply ContinuousLinearMap.ext
      intro z
      simp [Finset.mul_sum]
  have hderivWithin_const_mul (a : ℝ) (f : ℝ → ℝ) (d : ℝ)
      (hf : HasDerivWithinAt f d (Set.Icc 0 1) 0) :
      HasDerivWithinAt (fun r => a * f r) (a * d) (Set.Icc 0 1) 0 := by
    unfold HasDerivWithinAt HasDerivAtFilter
    convert hf.const_mul a using 1 <;> try rfl
  have hderivWithin_add (f g : ℝ → ℝ) (d e : ℝ)
      (hf : HasDerivWithinAt f d (Set.Icc 0 1) 0)
      (hg : HasDerivWithinAt g e (Set.Icc 0 1) 0) :
      HasDerivWithinAt (fun r => f r + g r) (d + e) (Set.Icc 0 1) 0 := by
    unfold HasDerivWithinAt HasDerivAtFilter
    convert hf.add hg using 1 <;> try rfl
    apply ContinuousLinearMap.ext
    intro z
    simp [mul_add]
  have hpositive (t : ℕ) (ω : Ω) (j : Fin M.depth) (v : Node)
      (hv : v ∈ M.levelNodes j) (hscale : 0 < M.scale j) :
      0 < subtree_mass M (run.distribution t ω) v := by
    let p : Action → ℝ := run.distribution t ω
    have hp := run.distribution_mem t ω
    have hpnonneg := (subtree_mass_level_probability M p hp j).1 v hv
    apply lt_of_le_of_ne hpnonneg
    intro hpzero'
    have hpzero : subtree_mass M p v = 0 := hpzero'.symm
    obtain ⟨a, ha, hgap⟩ := M.nodeGap_attained j v hv
    let e : Action → ℝ := fun b => if b = a then 1 else 0
    have he : probability_vector e := by
      simpa [probability_vector, e, eq_comm] using
        (ite_eq_mem_stdSimplex (𝕜 := ℝ) a)
    let path : ℝ → Action → ℝ := fun r b => p b + r ^ 2 * (e b - p b)
    have hpath (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
        probability_vector (path r) := by
      change path r ∈ stdSimplex ℝ Action
      have hr2nonneg : 0 ≤ r ^ 2 := sq_nonneg r
      have hr2le : r ^ 2 ≤ 1 := by
        simpa [pow_two] using mul_self_le_mul_self hr.1 hr.2
      change p ∈ stdSimplex ℝ Action at hp
      change e ∈ stdSimplex ℝ Action at he
      have hconv := (convex_stdSimplex (𝕜 := ℝ) (ι := Action)) hp he
        (sub_nonneg.mpr hr2le) hr2nonneg (by ring)
      convert hconv using 1
      ext b
      simp only [path, e, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    let lossBefore : Action → ℝ := fun b =>
      ∑ s ∈ Finset.range t, run.estimatedLoss s ω b
    let objective : ℝ → ℝ := fun r =>
      (∑ b, lossBefore b * path r b) +
        ∑ k, W (t + 1) k * ∑ u ∈ M.levelNodes k,
          (subtree_mass M (path r) u - Real.sqrt (subtree_mass M (path r) u))
    have hmin : IsMinOn objective (Set.Icc (0 : ℝ) 1) 0 := by
      change ∀ r ∈ Set.Icc (0 : ℝ) 1, objective 0 ≤ objective r
      intro r hr
      have hupdate := run.ftrl_update t ω (path r) (hpath r hr)
      rw [hregularizer (t + 1) (run.distribution t ω) (by omega)
          (run.distribution_mem t ω),
        hregularizer (t + 1) (path r) (by omega) (hpath r hr),
        hregularizer_sum, hregularizer_sum] at hupdate
      have hpath0 : path 0 = run.distribution t ω := by
        funext b
        simp [path, p]
      change (∑ b, lossBefore b * path 0 b) +
          ∑ k, W (t + 1) k * ∑ u ∈ M.levelNodes k,
            (subtree_mass M (path 0) u - Real.sqrt (subtree_mass M (path 0) u)) ≤
        objective r
      rw [hpath0]
      simpa [objective, lossBefore, path, p] using hupdate
    let dnode : Fin M.depth → Node → ℝ := fun k u =>
      if subtree_mass M p u = 0 then
        if M.descends u a then -1 else 0
      else 0
    have hnode (k : Fin M.depth) (u : Node) (hu : u ∈ M.levelNodes k) :
        HasDerivWithinAt
          (fun r => subtree_mass M (path r) u -
            Real.sqrt (subtree_mass M (path r) u))
          (dnode k u) (Set.Icc 0 1) 0 := by
      by_cases hpu : subtree_mass M p u = 0
      · simpa only [path, e, dnode, hpu, if_true] using hphi_sq_zero p a u hpu
      · have hpu0 := (subtree_mass_level_probability M p hp k).1 u hu
        have hpupos : 0 < subtree_mass M p u := lt_of_le_of_ne hpu0 (Ne.symm hpu)
        have hsquare : HasDerivAt (fun r : ℝ => r ^ 2) 0 0 := by
          simpa using hasDerivAt_pow 2 (0 : ℝ)
        have hm : HasDerivAt (fun r => subtree_mass M (path r) u) 0 0 := by
          have hscaled : HasDerivAt
              (fun r => r ^ 2 * (subtree_mass M e u - subtree_mass M p u)) 0 0 := by
            simpa using hsquare.mul_const
              (subtree_mass M e u - subtree_mass M p u)
          have haffine : HasDerivAt
              (fun r => r ^ 2 * (subtree_mass M e u - subtree_mass M p u) +
                subtree_mass M p u) 0 0 := hscaled.add_const _
          convert haffine using 1 <;> try norm_num
          funext r
          rw [show path r = fun b => p b + r ^ 2 * (e b - p b) by rfl,
            hmass_line]
          ring
        have hmass0 : subtree_mass M (path 0) u ≠ 0 := by
          simpa [path] using ne_of_gt hpupos
        have hsqrt : HasDerivAt
            (fun r => Real.sqrt (subtree_mass M (path r) u)) 0 0 := by
          simpa using hm.sqrt hmass0
        have hdiff : HasDerivAt
            (fun r => subtree_mass M (path r) u -
              Real.sqrt (subtree_mass M (path r) u)) 0 0 := by
          unfold HasDerivAt HasDerivAtFilter
          convert hm.sub hsqrt using 1 <;> try rfl
          apply ContinuousLinearMap.ext
          intro z
          simp
        simpa only [dnode, hpu, if_false, sub_self] using
          hdiff.hasDerivWithinAt
    have hinner (k : Fin M.depth) :
        HasDerivWithinAt
          (fun r => ∑ u ∈ M.levelNodes k,
            (subtree_mass M (path r) u - Real.sqrt (subtree_mass M (path r) u)))
          (∑ u ∈ M.levelNodes k, dnode k u) (Set.Icc 0 1) 0 :=
      hderivWithin_sum_node (M.levelNodes k)
        (fun u r => subtree_mass M (path r) u -
          Real.sqrt (subtree_mass M (path r) u)) (dnode k) (hnode k)
    have hlevel (k : Fin M.depth) :
        HasDerivWithinAt
          (fun r => W (t + 1) k * ∑ u ∈ M.levelNodes k,
            (subtree_mass M (path r) u - Real.sqrt (subtree_mass M (path r) u)))
          (W (t + 1) k * ∑ u ∈ M.levelNodes k, dnode k u)
          (Set.Icc 0 1) 0 :=
      hderivWithin_const_mul _ _ _ (hinner k)
    have hreg : HasDerivWithinAt
        (fun r => ∑ k, W (t + 1) k * ∑ u ∈ M.levelNodes k,
          (subtree_mass M (path r) u - Real.sqrt (subtree_mass M (path r) u)))
        (∑ k, W (t + 1) k * ∑ u ∈ M.levelNodes k, dnode k u)
        (Set.Icc 0 1) 0 :=
      hderivWithin_sum_level _ _ hlevel
    have hcoord (b : Action) :
        HasDerivWithinAt (fun r => lossBefore b * path r b) 0
          (Set.Icc 0 1) 0 := by
      have hsquare : HasDerivAt (fun r : ℝ => r ^ 2) 0 0 := by
        simpa using hasDerivAt_pow 2 (0 : ℝ)
      have hscaled : HasDerivAt
          (fun r : ℝ => r ^ 2 * (e b - p b)) 0 0 := by
        simpa using hsquare.mul_const (e b - p b)
      have haffine : HasDerivAt (fun r : ℝ => path r b) 0 0 := by
        dsimp [path]
        unfold HasDerivAt HasDerivAtFilter
        convert hscaled.const_add (p b) using 1 <;> try rfl
      simpa using (haffine.const_mul (lossBefore b)).hasDerivWithinAt
    have hloss : HasDerivWithinAt
        (fun r => ∑ b, lossBefore b * path r b) 0 (Set.Icc 0 1) 0 := by
      simpa using hderivWithin_sum_action
        (fun b r => lossBefore b * path r b) (fun _ => 0) hcoord
    have hobjective : HasDerivWithinAt objective
        (∑ k, W (t + 1) k * ∑ u ∈ M.levelNodes k, dnode k u)
        (Set.Icc 0 1) 0 := by
      simpa [objective] using hderivWithin_add _ _ _ _ hloss hreg
    have hdnode_nonpos (k : Fin M.depth) (u : Node) : dnode k u ≤ 0 := by
      dsimp [dnode]
      split_ifs <;> norm_num
    have hdj : (∑ u ∈ M.levelNodes j, dnode j u) ≤ -1 := by
      rw [← Finset.sum_erase_add _ _ hv]
      have hrest : (∑ u ∈ (M.levelNodes j).erase v, dnode j u) ≤ 0 :=
        Finset.sum_nonpos fun u hu => hdnode_nonpos j u
      have hvderiv : dnode j v = -1 := by simp [dnode, hpzero, ha]
      rw [hvderiv]
      linarith
    have hterm_nonpos (k : Fin M.depth) :
        W (t + 1) k * ∑ u ∈ M.levelNodes k, dnode k u ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (hW_nonneg _ _)
        (Finset.sum_nonpos fun u hu => hdnode_nonpos k u)
    have hjterm_neg : W (t + 1) j * ∑ u ∈ M.levelNodes j, dnode j u < 0 := by
      exact mul_neg_of_pos_of_neg (hW_pos _ _ (by omega) hscale) (lt_of_le_of_lt hdj (by norm_num))
    have hderiv_neg :
        (∑ k, W (t + 1) k * ∑ u ∈ M.levelNodes k, dnode k u) < 0 := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
      exact add_neg_of_nonpos_of_neg
        (Finset.sum_nonpos fun k hk => hterm_nonpos k) hjterm_neg
    exact (not_lt_of_ge
      (right_derivative_nonnegative_at_interval_min objective _ hmin hobjective))
      hderiv_neg
  have hfirst_order (t : ℕ) (ω : Ω) (q : Action → ℝ)
      (hq : probability_vector q) :
      0 ≤ (∑ b, (∑ s ∈ Finset.range t, run.estimatedLoss s ω b) *
          (q b - run.distribution t ω b)) +
        ∑ k, W (t + 1) k * ∑ u ∈ M.levelNodes k,
          ((subtree_mass M q u - subtree_mass M (run.distribution t ω) u) -
            (subtree_mass M q u - subtree_mass M (run.distribution t ω) u) /
              (2 * Real.sqrt (subtree_mass M (run.distribution t ω) u))) := by
    let p : Action → ℝ := run.distribution t ω
    have hp := run.distribution_mem t ω
    let path : ℝ → Action → ℝ := fun r b => p b + r * (q b - p b)
    have hpath (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
        probability_vector (path r) := by
      change path r ∈ stdSimplex ℝ Action
      change p ∈ stdSimplex ℝ Action at hp
      change q ∈ stdSimplex ℝ Action at hq
      have hconv := (convex_stdSimplex (𝕜 := ℝ) (ι := Action)) hp hq
        (sub_nonneg.mpr hr.2) hr.1 (by ring)
      convert hconv using 1
      ext b
      simp only [path, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    let lossBefore : Action → ℝ := fun b =>
      ∑ s ∈ Finset.range t, run.estimatedLoss s ω b
    let objective : ℝ → ℝ := fun r =>
      (∑ b, lossBefore b * path r b) +
        ∑ k, W (t + 1) k * ∑ u ∈ M.levelNodes k,
          (subtree_mass M (path r) u - Real.sqrt (subtree_mass M (path r) u))
    have hmin : IsMinOn objective (Set.Icc (0 : ℝ) 1) 0 := by
      change ∀ r ∈ Set.Icc (0 : ℝ) 1, objective 0 ≤ objective r
      intro r hr
      have hupdate := run.ftrl_update t ω (path r) (hpath r hr)
      rw [hregularizer (t + 1) (run.distribution t ω) (by omega)
          (run.distribution_mem t ω),
        hregularizer (t + 1) (path r) (by omega) (hpath r hr),
        hregularizer_sum, hregularizer_sum] at hupdate
      have hpath0 : path 0 = run.distribution t ω := by
        funext b
        simp [path, p]
      change (∑ b, lossBefore b * path 0 b) +
          ∑ k, W (t + 1) k * ∑ u ∈ M.levelNodes k,
            (subtree_mass M (path 0) u - Real.sqrt (subtree_mass M (path 0) u)) ≤
        objective r
      rw [hpath0]
      simpa [objective, lossBefore, path, p] using hupdate
    have hcoord (b : Action) : HasDerivWithinAt
        (fun r => lossBefore b * path r b)
        (lossBefore b * (q b - p b)) (Set.Icc 0 1) 0 := by
      have hline : HasDerivAt (fun r : ℝ => path r b) (q b - p b) 0 := by
        dsimp [path]
        unfold HasDerivAt HasDerivAtFilter
        convert (hasDerivAt_mul_const (x := (0 : ℝ))
          (q b - p b)).add_const (p b) using 1 <;> try rfl
        funext r
        ring
      simpa using (hline.const_mul (lossBefore b)).hasDerivWithinAt
    have hloss : HasDerivWithinAt
        (fun r => ∑ b, lossBefore b * path r b)
        (∑ b, lossBefore b * (q b - p b)) (Set.Icc 0 1) 0 :=
      hderivWithin_sum_action _ _ hcoord
    have hlevel (k : Fin M.depth) : HasDerivWithinAt
        (fun r => W (t + 1) k * ∑ u ∈ M.levelNodes k,
          (subtree_mass M (path r) u - Real.sqrt (subtree_mass M (path r) u)))
        (W (t + 1) k * ∑ u ∈ M.levelNodes k,
          ((subtree_mass M q u - subtree_mass M p u) -
            (subtree_mass M q u - subtree_mass M p u) /
              (2 * Real.sqrt (subtree_mass M p u))))
        (Set.Icc 0 1) 0 := by
      by_cases hscale : M.scale k = 0
      · have hWzero : W (t + 1) k = 0 := by simp [W, hscale]
        simp only [hWzero, zero_mul]
        exact (hasDerivAt_const (x := (0 : ℝ)) (0 : ℝ)).hasDerivWithinAt
      · have hscale_pos : 0 < M.scale k :=
          lt_of_le_of_ne (M.scale_nonnegative k) (Ne.symm hscale)
        have hinner : HasDerivWithinAt
            (fun r => ∑ u ∈ M.levelNodes k,
              (subtree_mass M (path r) u - Real.sqrt (subtree_mass M (path r) u)))
            (∑ u ∈ M.levelNodes k,
              ((subtree_mass M q u - subtree_mass M p u) -
                (subtree_mass M q u - subtree_mass M p u) /
                  (2 * Real.sqrt (subtree_mass M p u))))
            (Set.Icc 0 1) 0 := by
          apply hderivWithin_sum_node
          intro u hu
          simpa only [path] using
            (hphi p q u (hpositive t ω k u hu hscale_pos)).hasDerivWithinAt
        exact hderivWithin_const_mul _ _ _ hinner
    have hreg : HasDerivWithinAt
        (fun r => ∑ k, W (t + 1) k * ∑ u ∈ M.levelNodes k,
          (subtree_mass M (path r) u - Real.sqrt (subtree_mass M (path r) u)))
        (∑ k, W (t + 1) k * ∑ u ∈ M.levelNodes k,
          ((subtree_mass M q u - subtree_mass M p u) -
            (subtree_mass M q u - subtree_mass M p u) /
              (2 * Real.sqrt (subtree_mass M p u))))
        (Set.Icc 0 1) 0 :=
      hderivWithin_sum_level _ _ hlevel
    have hobjective : HasDerivWithinAt objective
        ((∑ b, lossBefore b * (q b - p b)) +
          ∑ k, W (t + 1) k * ∑ u ∈ M.levelNodes k,
            ((subtree_mass M q u - subtree_mass M p u) -
              (subtree_mass M q u - subtree_mass M p u) /
                (2 * Real.sqrt (subtree_mass M p u))))
        (Set.Icc 0 1) 0 := by
      simpa [objective] using hderivWithin_add _ _ _ _ hloss hreg
    simpa only [p, lossBefore] using
      right_derivative_nonnegative_at_interval_min objective _ hmin hobjective
  let L : ℕ → Ω → Fin M.depth → ℝ := fun t ω j =>
    M.loss t ω (M.firstAction t ω) - M.loss t ω (M.secondAction t ω) + run.shift j
  let Y : ℕ → Ω → Fin M.depth → Node → ℝ := fun t ω j v =>
    if M.sampledLevel t ω = j then
      (@ite ℝ (M.descends v (M.firstAction t ω))
          (M.descends_decidable v (M.firstAction t ω))
          (L t ω j /
            (M.delta j * subtree_mass M (run.distribution t ω) v)) 0) -
        L t ω j / M.delta j
    else 0
  have hestimated_pair (t : ℕ) (ω : Ω) (q : Action → ℝ)
      (hq : probability_vector q) :
      (∑ a, run.estimatedLoss t ω a * (run.distribution t ω a - q a)) =
        ∑ j, ∑ v ∈ M.levelNodes j, Y t ω j v *
          (subtree_mass M (run.distribution t ω) v - subtree_mass M q v) := by
    let j₀ : Fin M.depth := M.sampledLevel t ω
    have hp := subtree_mass_level_probability M (run.distribution t ω)
      (run.distribution_mem t ω) j₀
    have hqmass := subtree_mass_level_probability M q hq j₀
    have hmassdiff :
        ∑ v ∈ M.levelNodes j₀,
          (subtree_mass M (run.distribution t ω) v - subtree_mass M q v) = 0 := by
      rw [Finset.sum_sub_distrib, hp.2, hqmass.2]
      ring
    have hindicator_pair (v : Node) (C : ℝ) :
        (∑ a, (@ite ℝ (M.descends v a) (M.descends_decidable v a) C 0) *
          (run.distribution t ω a - q a)) =
            C * (subtree_mass M (run.distribution t ω) v - subtree_mass M q v) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      congr 1
      · rw [subtree_mass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : M.descends v a <;> simp [h]
      · rw [subtree_mass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : M.descends v a <;> simp [h]
    rw [Finset.sum_eq_single j₀]
    · have hcenter :
          (∑ v ∈ M.levelNodes j₀, Y t ω j₀ v *
            (subtree_mass M (run.distribution t ω) v - subtree_mass M q v)) =
          ∑ v ∈ M.levelNodes j₀,
            (@ite ℝ (M.descends v (M.firstAction t ω))
                (M.descends_decidable v (M.firstAction t ω))
                (L t ω j₀ /
                  (M.delta j₀ * subtree_mass M (run.distribution t ω) v)) 0) *
              (subtree_mass M (run.distribution t ω) v - subtree_mass M q v) := by
        simp only [Y, j₀, if_true]
        simp_rw [sub_mul]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hmassdiff, mul_zero, sub_zero]
        apply Finset.sum_congr rfl
        intro v hv
        by_cases h : M.descends v (M.firstAction t ω) <;> simp [h]
      rw [hcenter]
      simp_rw [run.estimatedLoss_formula t ω]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v hv
      by_cases hdesc : M.descends v (M.firstAction t ω)
      · simp only [hdesc, if_true]
        convert hindicator_pair v
          (L t ω j₀ /
            (M.delta j₀ * subtree_mass M (run.distribution t ω) v)) using 1 <;>
          simp [L, j₀]
      · simp [hdesc]
    · intro j hj hne
      simp [Y, j₀, Ne.symm hne]
    · simp
  have hvalid (t : ℕ) : ∀ᵐ ω ∂M.measure,
      M.parentCommonAtLevel (M.sampledLevel t ω)
        (M.firstAction t ω) (M.secondAction t ω) := by
    have hlevels : ∀ᵐ ω ∂M.measure, ∀ j ∈ (Finset.univ : Finset (Fin M.depth)),
        M.sampledLevel t ω = j →
          M.parentCommonAtLevel j (M.firstAction t ω) (M.secondAction t ω) := by
      rw [Filter.eventually_all_finset]
      intro j hj
      have hall : ∀ᵐ ω ∂M.measure, ∀ a ∈ (Finset.univ : Finset Action),
          ∀ b ∈ (Finset.univ : Finset Action),
            M.parentCommonAtLevel j a b ∨
              ¬(M.firstAction t ω = a ∧ M.sampledLevel t ω = j ∧
                M.secondAction t ω = b) := by
        rw [Filter.eventually_all_finset]
        intro a ha
        rw [Filter.eventually_all_finset]
        intro b hb
        by_cases hab : M.parentCommonAtLevel j a b
        · exact Filter.Eventually.of_forall fun ω => Or.inl hab
        · exact (feedback_atom_null_of_not_parent_common M run t a j b hab).mono
            fun ω hω => Or.inr hω
      filter_upwards [hall] with ω hω
      intro hjω
      rcases hω (M.firstAction t ω) (Finset.mem_univ _)
          (M.secondAction t ω) (Finset.mem_univ _) with hp | hn
      · exact hp
      · exact (hn ⟨rfl, hjω, rfl⟩).elim
    filter_upwards [hlevels] with ω hω
    exact hω (M.sampledLevel t ω) (Finset.mem_univ _) rfl
  have hdelta_le_one (j : Fin M.depth) : M.delta j ≤ 1 := by
    rw [← M.delta_total]
    exact Finset.single_le_sum (fun k hk => (M.delta_positive k).le)
      (Finset.mem_univ j)
  have hW_lower (s : ℕ) (j : Fin M.depth) :
      4 * c * M.scale j / M.delta j ≤ W s j := by
    have hc0 : 0 ≤ c := by linarith
    have hc10 : 0 ≤ c - 1 := by linarith
    have hc1 : 0 < c - 1 := by linarith
    have hδ0 : 0 ≤ M.delta j := (M.delta_positive j).le
    have hbase0 : 0 ≤ c * (c - 1) / M.delta j :=
      div_nonneg (mul_nonneg hc0 hc10) hδ0
    have hmax : c * (c - 1) / M.delta j ≤
        max (s : ℝ) (c * (c - 1) / M.delta j) := le_max_right _ _
    have hsqrtmax := Real.sqrt_le_sqrt hmax
    have hfactor : 0 ≤ (4 * Real.sqrt c / Real.sqrt (c - 1)) *
        (M.scale j / Real.sqrt (M.delta j)) := by
      exact mul_nonneg
        (div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _))
        (div_nonneg (M.scale_nonnegative j) (Real.sqrt_nonneg _))
    calc
      4 * c * M.scale j / M.delta j =
          (4 * Real.sqrt c / Real.sqrt (c - 1)) *
            (M.scale j / Real.sqrt (M.delta j)) *
              Real.sqrt (c * (c - 1) / M.delta j) := by
        rw [Real.sqrt_div (mul_nonneg hc0 hc10), Real.sqrt_mul hc0 (c - 1)]
        field_simp [ne_of_gt (Real.sqrt_pos.2 hc1),
          ne_of_gt (Real.sqrt_pos.2 (M.delta_positive j))]
        rw [Real.sq_sqrt hδ0]
        field_simp [ne_of_gt hc1, ne_of_gt (M.delta_positive j)]
        rw [Real.sq_sqrt hc0]
        ring
      _ ≤ (4 * Real.sqrt c / Real.sqrt (c - 1)) *
            (M.scale j / Real.sqrt (M.delta j)) *
              Real.sqrt (max (s : ℝ) (c * (c - 1) / M.delta j)) :=
        mul_le_mul_of_nonneg_left hsqrtmax hfactor
      _ = W s j := rfl
  have hL_bounds (t : ℕ) (ω : Ω)
      (hvalidω : M.parentCommonAtLevel (M.sampledLevel t ω)
        (M.firstAction t ω) (M.secondAction t ω)) :
      0 ≤ L t ω (M.sampledLevel t ω) ∧
        L t ω (M.sampledLevel t ω) ≤ 2 * M.scale (M.sampledLevel t ω) := by
    have habs := parent_common_loss_difference_bound M t ω (M.sampledLevel t ω)
      (M.firstAction t ω) (M.secondAction t ω) hvalidω
    have hd := abs_le.mp habs
    dsimp [L]
    rw [hshift]
    constructor <;> linarith
  have hscalar (t : ℕ) (ω : Ω)
      (hvalidω : M.parentCommonAtLevel (M.sampledLevel t ω)
        (M.firstAction t ω) (M.secondAction t ω))
      (j : Fin M.depth) (v : Node) (hv : v ∈ M.levelNodes j) :
      Y t ω j v *
          (subtree_mass M (run.distribution t ω) v -
            subtree_mass M (run.distribution (t + 1) ω) v) +
        W (t + 1) j *
          ((subtree_mass M (run.distribution (t + 1) ω) v -
              subtree_mass M (run.distribution t ω) v) -
            (subtree_mass M (run.distribution (t + 1) ω) v -
              subtree_mass M (run.distribution t ω) v) /
              (2 * Real.sqrt (subtree_mass M (run.distribution t ω) v))) -
        W (t + 1) j *
          ((subtree_mass M (run.distribution (t + 1) ω) v -
              Real.sqrt (subtree_mass M (run.distribution (t + 1) ω) v)) -
            (subtree_mass M (run.distribution t ω) v -
              Real.sqrt (subtree_mass M (run.distribution t ω) v))) ≤
        (c / (c - 1)) * (2 / W (t + 1) j) *
          subtree_mass M (run.distribution t ω) v *
            Real.sqrt (subtree_mass M (run.distribution t ω) v) *
              (Y t ω j v) ^ 2 := by
    by_cases hscale : M.scale j = 0
    · have hWzero : W (t + 1) j = 0 := by simp [W, hscale]
      have hYzero : Y t ω j v = 0 := by
        by_cases hj : M.sampledLevel t ω = j
        · have hLb := hL_bounds t ω hvalidω
          have hLzero : L t ω j = 0 := by
            have hsj : M.scale (M.sampledLevel t ω) = 0 := by simpa [hj] using hscale
            rw [hsj] at hLb
            rw [← hj]
            linarith
          simp [Y, hj, hLzero]
        · simp [Y, hj]
      simp [hWzero, hYzero]
    · have hscale_pos : 0 < M.scale j :=
          lt_of_le_of_ne (M.scale_nonnegative j) (Ne.symm hscale)
      have hWpos := hW_pos (t + 1) j (by omega) hscale_pos
      have hp := hpositive t ω j v hv hscale_pos
      have hq := (subtree_mass_level_probability M
        (run.distribution (t + 1) ω) (run.distribution_mem (t + 1) ω) j).1 v hv
      have hpdata := subtree_mass_level_probability M
        (run.distribution t ω) (run.distribution_mem t ω) j
      have hp_le : subtree_mass M (run.distribution t ω) v ≤ 1 := by
        rw [← hpdata.2]
        exact Finset.single_le_sum (fun u hu => hpdata.1 u hu) hv
      have hsqrt_le : Real.sqrt (subtree_mass M (run.distribution t ω) v) ≤ 1 :=
        Real.sqrt_le_one.mpr hp_le
      have hsqrt_pos := Real.sqrt_pos.2 hp
      have hcpos : 0 < c := by linarith
      have hquot_nonneg : 0 ≤ 4 * c * M.scale j / M.delta j :=
        div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hcpos.le)
          (M.scale_nonnegative j)) (M.delta_positive j).le
      have hden_bound : 2 * M.scale j / M.delta j ≤
          W (t + 1) j /
            (2 * c * Real.sqrt (subtree_mass M (run.distribution t ω) v)) := by
        apply (le_div_iff₀ (mul_pos (mul_pos (by norm_num) hcpos) hsqrt_pos)).2
        calc
          (2 * M.scale j / M.delta j) *
              (2 * c * Real.sqrt (subtree_mass M (run.distribution t ω) v)) =
              (4 * c * M.scale j / M.delta j) *
                Real.sqrt (subtree_mass M (run.distribution t ω) v) := by ring
          _ ≤ 4 * c * M.scale j / M.delta j :=
            mul_le_of_le_one_right hquot_nonneg hsqrt_le
          _ ≤ W (t + 1) j := hW_lower _ _
      have hYlower : -1 /
          (c * (2 / W (t + 1) j) *
            Real.sqrt (subtree_mass M (run.distribution t ω) v)) ≤ Y t ω j v := by
        by_cases hj : M.sampledLevel t ω = j
        · have hLb := hL_bounds t ω hvalidω
          have hL0 : 0 ≤ L t ω j := by simpa [hj] using hLb.1
          have hL2 : L t ω j ≤ 2 * M.scale j := by simpa [hj] using hLb.2
          have hraw0 : 0 ≤ @ite ℝ (M.descends v (M.firstAction t ω))
              (M.descends_decidable v (M.firstAction t ω))
              (L t ω j /
                (M.delta j * subtree_mass M (run.distribution t ω) v)) 0 := by
            split
            · exact div_nonneg hL0 (mul_nonneg (M.delta_positive j).le hp.le)
            · exact le_rfl
          have hybase : -(2 * M.scale j / M.delta j) ≤ Y t ω j v := by
            simp only [Y, hj, if_true]
            have hdiv := div_le_div_of_nonneg_right hL2 (M.delta_positive j).le
            linarith
          have hinv : 1 /
              (c * (2 / W (t + 1) j) *
                Real.sqrt (subtree_mass M (run.distribution t ω) v)) =
              W (t + 1) j /
                (2 * c * Real.sqrt (subtree_mass M (run.distribution t ω) v)) := by
            field_simp [hWpos.ne', hcpos.ne', hsqrt_pos.ne']
          calc
            -1 / (c * (2 / W (t + 1) j) *
                Real.sqrt (subtree_mass M (run.distribution t ω) v)) =
                -(1 / (c * (2 / W (t + 1) j) *
                  Real.sqrt (subtree_mass M (run.distribution t ω) v))) := by ring
            _ = -(W (t + 1) j /
                (2 * c * Real.sqrt (subtree_mass M (run.distribution t ω) v))) := by
              rw [hinv]
            _ ≤ -(2 * M.scale j / M.delta j) := neg_le_neg hden_bound
            _ ≤ Y t ω j v := hybase
        · simp only [Y, hj, if_false]
          exact div_nonpos_of_nonpos_of_nonneg (by norm_num)
            (mul_nonneg (mul_nonneg hcpos.le
              (div_nonneg (by norm_num) hWpos.le)) (Real.sqrt_nonneg _))
      have hs := tsallis_bregman_stability_bound
        (2 / W (t + 1) j)
        (subtree_mass M (run.distribution t ω) v)
        (subtree_mass M (run.distribution (t + 1) ω) v) c (Y t ω j v)
        (div_pos (by norm_num) hWpos) hp hq (by linarith) hYlower
      convert hs using 1 <;> field_simp [hWpos.ne'] <;> ring
  let q : Action → ℝ := fun a => if a = M.bestAction T then 1 else 0
  have hq : probability_vector q := by
    simpa [probability_vector, q, eq_comm] using
      (ite_eq_mem_stdSimplex (𝕜 := ℝ) (M.bestAction T))
  let Gap : ℕ → Ω → Fin M.depth → ℝ := fun t ω j =>
    ∑ v ∈ M.levelNodes j,
      (Real.sqrt (subtree_mass M (run.distribution t ω) v) -
        subtree_mass M (run.distribution t ω) v)
  let Var : ℕ → Ω → Fin M.depth → ℝ := fun t ω j =>
    ∑ v ∈ M.levelNodes j,
      (subtree_mass M (run.distribution t ω) v *
        Real.sqrt (subtree_mass M (run.distribution t ω) v)) *
          (Y t ω j v) ^ 2
  let Obj : ℕ → Ω → ℝ := fun t ω =>
    ((∑ a, (∑ s ∈ Finset.range (t + 1), run.estimatedLoss s ω a) *
          run.distribution t ω a) +
        run.regularizer (t + 1) (run.distribution t ω) -
      ((∑ a, (∑ s ∈ Finset.range (t + 1), run.estimatedLoss s ω a) *
            run.distribution (t + 1) ω a) +
        run.regularizer (t + 1) (run.distribution (t + 1) ω)))
  have hobjective_gap (t : ℕ) (ω : Ω)
      (hvalidω : M.parentCommonAtLevel (M.sampledLevel t ω)
        (M.firstAction t ω) (M.secondAction t ω)) :
      Obj t ω ≤ ∑ j, (c / (c - 1)) * (2 / W (t + 1) j) * Var t ω j := by
    have hfo := hfirst_order t ω (run.distribution (t + 1) ω)
      (run.distribution_mem (t + 1) ω)
    have hpair := hestimated_pair t ω (run.distribution (t + 1) ω)
      (run.distribution_mem (t + 1) ω)
    have hsummed :
        (∑ j, ∑ v ∈ M.levelNodes j,
          (Y t ω j v *
              (subtree_mass M (run.distribution t ω) v -
                subtree_mass M (run.distribution (t + 1) ω) v) +
            W (t + 1) j *
              ((subtree_mass M (run.distribution (t + 1) ω) v -
                  subtree_mass M (run.distribution t ω) v) -
                (subtree_mass M (run.distribution (t + 1) ω) v -
                  subtree_mass M (run.distribution t ω) v) /
                    (2 * Real.sqrt (subtree_mass M (run.distribution t ω) v))) -
            W (t + 1) j *
              ((subtree_mass M (run.distribution (t + 1) ω) v -
                  Real.sqrt (subtree_mass M (run.distribution (t + 1) ω) v)) -
                (subtree_mass M (run.distribution t ω) v -
                  Real.sqrt (subtree_mass M (run.distribution t ω) v))))) ≤
          ∑ j, (c / (c - 1)) * (2 / W (t + 1) j) * Var t ω j := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro v hv
      simpa [mul_assoc] using hscalar t ω hvalidω j v hv
    dsimp [Obj]
    rw [hregularizer (t + 1) (run.distribution t ω) (by omega)
        (run.distribution_mem t ω),
      hregularizer (t + 1) (run.distribution (t + 1) ω) (by omega)
        (run.distribution_mem (t + 1) ω),
      hregularizer_sum, hregularizer_sum]
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib, add_mul]
    dsimp [Var] at hsummed ⊢
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.mul_sum] at hfo hpair hsummed ⊢
    linear_combination hsummed + hfo + hpair
  have hsqrt_max_diff (s : ℕ) (hs : 1 ≤ s) (K : ℝ) :
      Real.sqrt (max ((s + 1 : ℕ) : ℝ) K) - Real.sqrt (max (s : ℝ) K) ≤
        1 / (2 * Real.sqrt (s : ℝ)) := by
    have hspos : 0 < (s : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hs)
    have hsqrtpos : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 hspos
    let x : ℝ := max (s : ℝ) K
    let y : ℝ := max ((s + 1 : ℕ) : ℝ) K
    have hxpos : 0 < x := lt_of_lt_of_le hspos (le_max_left _ _)
    have hyx : y ≤ x + 1 := by
      apply max_le
      · dsimp [x, y]
        have hx := le_max_left (s : ℝ) K
        norm_num at hx ⊢
      · dsimp [x, y]
        linarith [le_max_right (s : ℝ) K]
    have hsx : Real.sqrt (s : ℝ) ≤ Real.sqrt x :=
      Real.sqrt_le_sqrt (le_max_left _ _)
    have hratio : 1 ≤ Real.sqrt x / Real.sqrt (s : ℝ) := by
      exact (le_div_iff₀ hsqrtpos).2 (by simpa using hsx)
    have hsq : y ≤ (Real.sqrt x + 1 / (2 * Real.sqrt (s : ℝ))) ^ 2 := by
      calc
        y ≤ x + 1 := hyx
        _ ≤ (Real.sqrt x + 1 / (2 * Real.sqrt (s : ℝ))) ^ 2 := by
          rw [add_sq, Real.sq_sqrt hxpos.le]
          have hsqnonneg : 0 ≤ (1 / (2 * Real.sqrt (s : ℝ))) ^ 2 := sq_nonneg _
          have heq : 2 * Real.sqrt x * (1 / (2 * Real.sqrt (s : ℝ))) =
              Real.sqrt x / Real.sqrt (s : ℝ) := by
            field_simp [hsqrtpos.ne']
          rw [heq]
          nlinarith
    have hroot : Real.sqrt y ≤
        Real.sqrt x + 1 / (2 * Real.sqrt (s : ℝ)) := by
      rw [Real.sqrt_le_iff]
      exact ⟨add_nonneg (Real.sqrt_nonneg _) (by positivity), hsq⟩
    simpa [x, y, add_comm] using sub_le_iff_le_add.mpr hroot
  have hW_one (j : Fin M.depth) : W 1 j = 4 * c * M.scale j / M.delta j := by
    have hc0 : 0 ≤ c := by linarith
    have hc10 : 0 ≤ c - 1 := by linarith
    have hc1 : 0 < c - 1 := by linarith
    have hK : 1 ≤ c * (c - 1) / M.delta j := by
      apply (le_div_iff₀ (M.delta_positive j)).2
      nlinarith [hdelta_le_one j]
    dsimp [W]
    norm_num
    rw [max_eq_right hK, Real.sqrt_div (mul_nonneg hc0 hc10),
      Real.sqrt_mul hc0 (c - 1)]
    field_simp [ne_of_gt (Real.sqrt_pos.2 hc1),
      ne_of_gt (Real.sqrt_pos.2 (M.delta_positive j))]
    rw [Real.sq_sqrt (M.delta_positive j).le]
    field_simp [ne_of_gt hc1, ne_of_gt (M.delta_positive j)]
    rw [Real.sq_sqrt hc0]
    ring
  have hW_diff (s : ℕ) (hs : 1 ≤ s) (j : Fin M.depth) :
      W (s + 1) j - W s j ≤
        (2 * Real.sqrt c / Real.sqrt (c - 1)) *
          (M.scale j / Real.sqrt (M.delta j)) * (1 / Real.sqrt (s : ℝ)) := by
    have hfactor : 0 ≤ (4 * Real.sqrt c / Real.sqrt (c - 1)) *
        (M.scale j / Real.sqrt (M.delta j)) := by
      exact mul_nonneg
        (div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _))
        (div_nonneg (M.scale_nonnegative j) (Real.sqrt_nonneg _))
    have hd := mul_le_mul_of_nonneg_left
      (hsqrt_max_diff s hs (c * (c - 1) / M.delta j)) hfactor
    dsimp [W]
    calc
      4 * Real.sqrt c / Real.sqrt (c - 1) *
            (M.scale j / Real.sqrt (M.delta j)) *
            Real.sqrt (max ((s + 1 : ℕ) : ℝ) (c * (c - 1) / M.delta j)) -
          4 * Real.sqrt c / Real.sqrt (c - 1) *
            (M.scale j / Real.sqrt (M.delta j)) *
            Real.sqrt (max (s : ℝ) (c * (c - 1) / M.delta j)) =
          (4 * Real.sqrt c / Real.sqrt (c - 1) *
            (M.scale j / Real.sqrt (M.delta j))) *
          (Real.sqrt (max ((s + 1 : ℕ) : ℝ) (c * (c - 1) / M.delta j)) -
            Real.sqrt (max (s : ℝ) (c * (c - 1) / M.delta j))) := by ring
      _ ≤ (4 * Real.sqrt c / Real.sqrt (c - 1) *
            (M.scale j / Real.sqrt (M.delta j))) *
          (1 / (2 * Real.sqrt (s : ℝ))) := hd
      _ = (2 * Real.sqrt c / Real.sqrt (c - 1)) *
          (M.scale j / Real.sqrt (M.delta j)) * (1 / Real.sqrt (s : ℝ)) := by ring
  have hW_terminal (j : Fin M.depth) :
      W (T + 1) j - W T j ≤ 2 * c * M.scale j / M.delta j := by
    have hd := hW_diff T hT j
    have hc0 : 0 ≤ c := by linarith
    have hc1 : 0 < c - 1 := by linarith
    have hδpos := M.delta_positive j
    have hTroot : 1 ≤ Real.sqrt (T : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hT)
    have hcoef :
        (2 * Real.sqrt c / Real.sqrt (c - 1)) *
            (M.scale j / Real.sqrt (M.delta j)) * (1 / Real.sqrt (T : ℝ)) ≤
          2 * c * M.scale j / M.delta j := by
      by_cases hscale : M.scale j = 0
      · simp [hscale]
      · have hscale_pos : 0 < M.scale j :=
          lt_of_le_of_ne (M.scale_nonnegative j) (Ne.symm hscale)
        have hsqrtTpos : 0 < Real.sqrt (T : ℝ) := lt_of_lt_of_le zero_lt_one hTroot
        have hsqrtineq : Real.sqrt c * Real.sqrt (M.delta j) ≤ c * Real.sqrt (c - 1) := by
          have hsqrtd_le : Real.sqrt (M.delta j) ≤ 1 :=
            Real.sqrt_le_one.mpr (hdelta_le_one j)
          have hsqrtc_le : Real.sqrt c ≤ c := by
            rw [Real.sqrt_le_iff]
            exact ⟨hc0, by nlinarith [Real.sq_sqrt hc0]⟩
          have hsqrtc1 : 1 ≤ Real.sqrt (c - 1) := by
            exact Real.one_le_sqrt.mpr (by linarith)
          calc
            Real.sqrt c * Real.sqrt (M.delta j) ≤ Real.sqrt c * 1 :=
              mul_le_mul_of_nonneg_left hsqrtd_le (Real.sqrt_nonneg _)
            _ ≤ c := by simpa using hsqrtc_le
            _ ≤ c * Real.sqrt (c - 1) := le_mul_of_one_le_right hc0 hsqrtc1
        have hbase : Real.sqrt c * M.delta j ≤
            c * Real.sqrt (c - 1) * Real.sqrt (M.delta j) := by
          calc
            Real.sqrt c * M.delta j =
                Real.sqrt c * (Real.sqrt (M.delta j)) ^ 2 := by
              rw [Real.sq_sqrt hδpos.le]
            _ = (Real.sqrt c * Real.sqrt (M.delta j)) *
                Real.sqrt (M.delta j) := by ring
            _ ≤ (c * Real.sqrt (c - 1)) * Real.sqrt (M.delta j) :=
              mul_le_mul_of_nonneg_right hsqrtineq (Real.sqrt_nonneg _)
        have hmore : c * Real.sqrt (c - 1) * Real.sqrt (M.delta j) ≤
            c * Real.sqrt (c - 1) * Real.sqrt (M.delta j) * Real.sqrt (T : ℝ) :=
          le_mul_of_one_le_right
            (mul_nonneg (mul_nonneg hc0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
            hTroot
        field_simp [ne_of_gt (Real.sqrt_pos.2 hc1),
          ne_of_gt (Real.sqrt_pos.2 hδpos), hsqrtTpos.ne']
        exact le_trans hbase hmore
    exact le_trans hd hcoef
  have hreg_q : run.regularizer (T + 1) q = 0 := by
    rw [hregularizer (T + 1) q (by omega) hq, hregularizer_sum]
    apply Finset.sum_eq_zero
    intro j hj
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro v hv
    dsimp [q]
    rw [hpoint_mass]
    by_cases hdesc : M.descends v (M.bestAction T) <;> simp [hdesc]
  have hreg_dist (s t : ℕ) (hs : 1 ≤ s) :
      (fun ω => run.regularizer s (run.distribution t ω)) =
        fun ω => -(∑ j, W s j * Gap t ω j) := by
    funext ω
    rw [hregularizer s (run.distribution t ω) hs (run.distribution_mem t ω),
      hregularizer_sum]
    dsimp [Gap]
    simp only [Finset.sum_sub_distrib, Finset.mul_sum]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hdrift (t : ℕ) (ω : Ω) :
      run.regularizer (t + 1) (run.distribution (t + 1) ω) -
          run.regularizer (t + 2) (run.distribution (t + 1) ω) =
        ∑ j, (W (t + 2) j - W (t + 1) j) * Gap (t + 1) ω j := by
    have h₁ := congrFun (hreg_dist (t + 1) (t + 1) (by omega)) ω
    have h₂ := congrFun (hreg_dist (t + 2) (t + 1) (by omega)) ω
    rw [h₁, h₂]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hpointwise : ∀ᵐ ω ∂M.measure,
      (∑ t ∈ Finset.range T, ∑ a,
          run.estimatedLoss t ω a * (run.distribution t ω a - q a)) ≤
        (∑ j, W 1 j * Gap 0 ω j) +
        ∑ t ∈ Finset.range T,
          ∑ j, (W (t + 2) j - W (t + 1) j) * Gap (t + 1) ω j +
        ∑ t ∈ Finset.range T,
          ∑ j, (c / (c - 1)) * (2 / W (t + 1) j) * Var t ω j := by
    have hall : ∀ᵐ ω ∂M.measure, ∀ t ∈ Finset.range T,
        M.parentCommonAtLevel (M.sampledLevel t ω)
          (M.firstAction t ω) (M.secondAction t ω) := by
      rw [Filter.eventually_all_finset]
      intro t ht
      exact hvalid t
    filter_upwards [hall] with ω hω
    have hdec := nested_tsallis_ftrl_decomposition M run T ω q hq
    rw [hreg_q] at hdec
    have hinit := congrFun (hreg_dist 1 0 (by omega)) ω
    rw [hinit] at hdec
    simp only [zero_sub, neg_neg] at hdec
    simp_rw [hdrift] at hdec
    change (∑ t ∈ Finset.range T, ∑ a,
        run.estimatedLoss t ω a * (run.distribution t ω a - q a)) ≤
      (∑ j, W 1 j * Gap 0 ω j) +
        ∑ t ∈ Finset.range T,
          ∑ j, (W (t + 2) j - W (t + 1) j) * Gap (t + 1) ω j +
        ∑ t ∈ Finset.range T, Obj t ω at hdec
    have hobjsum := Finset.sum_le_sum fun t ht => hobjective_gap t ω (hω t ht)
    exact le_trans hdec (by linarith)
  have hGap_integrable (t : ℕ) (j : Fin M.depth) :
      MeasureTheory.Integrable (fun ω => Gap t ω j) M.measure := by
    simpa [Gap] using nested_tsallis_level_gap_integrable M run t j
  have hGap_nonneg (t : ℕ) (ω : Ω) (j : Fin M.depth) : 0 ≤ Gap t ω j := by
    dsimp [Gap]
    apply Finset.sum_nonneg
    intro v hv
    have hp := subtree_mass_level_probability M (run.distribution t ω)
      (run.distribution_mem t ω) j
    have hp0 := hp.1 v hv
    have hp1 : subtree_mass M (run.distribution t ω) v ≤ 1 := by
      rw [← hp.2]
      exact Finset.single_le_sum (fun u hu => hp.1 u hu) hv
    have hs0 := Real.sqrt_nonneg (subtree_mass M (run.distribution t ω) v)
    have hs1 := Real.sqrt_le_one.mpr hp1
    have hs2 := Real.sq_sqrt hp0
    nlinarith
  have hVar_eq (t : ℕ) (j : Fin M.depth) :
      (fun ω => Var t ω j) = fun ω =>
        if M.sampledLevel t ω = j then
          ∑ v ∈ M.levelNodes j,
            (subtree_mass M (run.distribution t ω) v *
                Real.sqrt (subtree_mass M (run.distribution t ω) v)) *
              ((@ite ℝ (M.descends v (M.firstAction t ω))
                  (M.descends_decidable v (M.firstAction t ω))
                  ((M.loss t ω (M.firstAction t ω) -
                        M.loss t ω (M.secondAction t ω) + run.shift j) /
                    (M.delta j * subtree_mass M (run.distribution t ω) v)) 0) -
                (M.loss t ω (M.firstAction t ω) -
                    M.loss t ω (M.secondAction t ω) + run.shift j) /
                  M.delta j) ^ 2
        else 0 := by
    funext ω
    by_cases hj : M.sampledLevel t ω = j
    · simp only [Var, Y, L, hj, if_true]
      apply Finset.sum_congr rfl
      intro v hv
      congr
    · simp [Var, Y, hj]
  have hVar_integrable (t : ℕ) (j : Fin M.depth) :
      MeasureTheory.Integrable (fun ω => Var t ω j) M.measure := by
    rw [hVar_eq]
    exact run.sampled_centered_variance_integrable t j
  have hVar_integral_bound (t : ℕ) (j : Fin M.depth) :
      (∫ ω, Var t ω j ∂M.measure) ≤
        (8 * (M.scale j) ^ 2 / M.delta j) *
          ∫ ω, Gap t ω j ∂M.measure := by
    rw [hVar_eq]
    simpa [Gap] using sampled_subtree_centered_variance_integral M run t j hshift
  have hleft_integrable : MeasureTheory.Integrable
      (fun ω => ∑ t ∈ Finset.range T, ∑ a,
        run.estimatedLoss t ω a * (run.distribution t ω a - q a)) M.measure := by
    exact MeasureTheory.integrable_finsetSum (Finset.range T)
      (fun t ht => run.estimated_regret_integrable t q hq)
  have hinit_integrable : MeasureTheory.Integrable
      (fun ω => ∑ j, W 1 j * Gap 0 ω j) M.measure :=
    MeasureTheory.integrable_finsetSum Finset.univ
      (fun j hj => (hGap_integrable 0 j).const_mul (W 1 j))
  have hdrift_integrable : MeasureTheory.Integrable
      (fun ω => ∑ t ∈ Finset.range T,
        ∑ j, (W (t + 2) j - W (t + 1) j) * Gap (t + 1) ω j) M.measure :=
    MeasureTheory.integrable_finsetSum (Finset.range T) (fun t ht =>
      MeasureTheory.integrable_finsetSum Finset.univ (fun j hj =>
        (hGap_integrable (t + 1) j).const_mul
          (W (t + 2) j - W (t + 1) j)))
  have hvariance_integrable : MeasureTheory.Integrable
      (fun ω => ∑ t ∈ Finset.range T,
        ∑ j, (c / (c - 1)) * (2 / W (t + 1) j) * Var t ω j) M.measure :=
    MeasureTheory.integrable_finsetSum (Finset.range T) (fun t ht =>
      MeasureTheory.integrable_finsetSum Finset.univ (fun j hj =>
        (hVar_integrable t j).const_mul
          ((c / (c - 1)) * (2 / W (t + 1) j))))
  have hright_integrable : MeasureTheory.Integrable
      (fun ω =>
        (∑ j, W 1 j * Gap 0 ω j) +
        ∑ t ∈ Finset.range T,
          ∑ j, (W (t + 2) j - W (t + 1) j) * Gap (t + 1) ω j +
        ∑ t ∈ Finset.range T,
          ∑ j, (c / (c - 1)) * (2 / W (t + 1) j) * Var t ω j)
      M.measure := by
    exact (hinit_integrable.add hdrift_integrable).add hvariance_integrable
  have hinit_integral :
      (∫ ω, ∑ j, W 1 j * Gap 0 ω j ∂M.measure) =
        ∑ j, W 1 j * ∫ ω, Gap 0 ω j ∂M.measure := by
    rw [MeasureTheory.integral_finsetSum (μ := M.measure) Finset.univ
      (fun j hj => (hGap_integrable 0 j).const_mul (W 1 j))]
    apply Finset.sum_congr rfl
    intro j hj
    rw [MeasureTheory.integral_const_mul]
  have hdrift_integral :
      (∫ ω, ∑ t ∈ Finset.range T,
          ∑ j, (W (t + 2) j - W (t + 1) j) * Gap (t + 1) ω j ∂M.measure) =
        ∑ t ∈ Finset.range T,
          ∑ j, (W (t + 2) j - W (t + 1) j) *
            ∫ ω, Gap (t + 1) ω j ∂M.measure := by
    rw [MeasureTheory.integral_finsetSum (μ := M.measure) (Finset.range T)
      (fun t ht => MeasureTheory.integrable_finsetSum Finset.univ (fun j hj =>
        (hGap_integrable (t + 1) j).const_mul
          (W (t + 2) j - W (t + 1) j)))]
    apply Finset.sum_congr rfl
    intro t ht
    rw [MeasureTheory.integral_finsetSum (μ := M.measure) Finset.univ
      (fun j hj => (hGap_integrable (t + 1) j).const_mul
        (W (t + 2) j - W (t + 1) j))]
    apply Finset.sum_congr rfl
    intro j hj
    rw [MeasureTheory.integral_const_mul]
  have hvariance_integral :
      (∫ ω, ∑ t ∈ Finset.range T,
          ∑ j, (c / (c - 1)) * (2 / W (t + 1) j) * Var t ω j ∂M.measure) =
        ∑ t ∈ Finset.range T,
          ∑ j, (c / (c - 1)) * (2 / W (t + 1) j) *
            ∫ ω, Var t ω j ∂M.measure := by
    rw [MeasureTheory.integral_finsetSum (μ := M.measure) (Finset.range T)
      (fun t ht => MeasureTheory.integrable_finsetSum Finset.univ (fun j hj =>
        (hVar_integrable t j).const_mul
          ((c / (c - 1)) * (2 / W (t + 1) j))))]
    apply Finset.sum_congr rfl
    intro t ht
    rw [MeasureTheory.integral_finsetSum (μ := M.measure) Finset.univ
      (fun j hj => (hVar_integrable t j).const_mul
        ((c / (c - 1)) * (2 / W (t + 1) j)))]
    apply Finset.sum_congr rfl
    intro j hj
    rw [MeasureTheory.integral_const_mul]
  have hintegrated :
      (∫ ω, ∑ t ∈ Finset.range T, ∑ a,
          run.estimatedLoss t ω a * (run.distribution t ω a - q a) ∂M.measure) ≤
        (∑ j, W 1 j * ∫ ω, Gap 0 ω j ∂M.measure) +
        ∑ t ∈ Finset.range T,
          ∑ j, (W (t + 2) j - W (t + 1) j) *
            ∫ ω, Gap (t + 1) ω j ∂M.measure +
        ∑ t ∈ Finset.range T,
          ∑ j, (c / (c - 1)) * (2 / W (t + 1) j) *
            ∫ ω, Var t ω j ∂M.measure := by
    have hab := MeasureTheory.integral_add hinit_integrable hdrift_integrable
    have habc := MeasureTheory.integral_add
      (hinit_integrable.add hdrift_integrable) hvariance_integrable
    have hab' :
        (∫ ω, (∑ j, W 1 j * Gap 0 ω j) +
          ∑ t ∈ Finset.range T,
            ∑ j, (W (t + 2) j - W (t + 1) j) * Gap (t + 1) ω j ∂M.measure) =
          (∫ ω, ∑ j, W 1 j * Gap 0 ω j ∂M.measure) +
          ∫ ω, ∑ t ∈ Finset.range T,
            ∑ j, (W (t + 2) j - W (t + 1) j) * Gap (t + 1) ω j ∂M.measure := by
      simpa only [Pi.add_apply] using hab
    have habc' :
        (∫ ω, ((∑ j, W 1 j * Gap 0 ω j) +
          ∑ t ∈ Finset.range T,
            ∑ j, (W (t + 2) j - W (t + 1) j) * Gap (t + 1) ω j) +
          ∑ t ∈ Finset.range T,
            ∑ j, (c / (c - 1)) * (2 / W (t + 1) j) * Var t ω j ∂M.measure) =
          (∫ ω, (∑ j, W 1 j * Gap 0 ω j) +
            ∑ t ∈ Finset.range T,
              ∑ j, (W (t + 2) j - W (t + 1) j) * Gap (t + 1) ω j ∂M.measure) +
          ∫ ω, ∑ t ∈ Finset.range T,
            ∑ j, (c / (c - 1)) * (2 / W (t + 1) j) * Var t ω j ∂M.measure := by
      simpa only [Pi.add_apply] using habc
    calc
      _ ≤ ∫ ω,
          ((∑ j, W 1 j * Gap 0 ω j) +
          ∑ t ∈ Finset.range T,
            ∑ j, (W (t + 2) j - W (t + 1) j) * Gap (t + 1) ω j +
          ∑ t ∈ Finset.range T,
            ∑ j, (c / (c - 1)) * (2 / W (t + 1) j) * Var t ω j)
          ∂M.measure := MeasureTheory.integral_mono_ae hleft_integrable
            hright_integrable hpointwise
      _ = _ := by
        rw [habc', hab', hinit_integral, hdrift_integral, hvariance_integral]
  have hvariance_coefficient (t : ℕ) (j : Fin M.depth) :
      (c / (c - 1)) * (2 / W (t + 1) j) *
          (8 * (M.scale j) ^ 2 / M.delta j) ≤
        (4 * Real.sqrt c / Real.sqrt (c - 1)) *
          (M.scale j / Real.sqrt (M.delta j)) *
            (1 / Real.sqrt ((t + 1 : ℕ) : ℝ)) := by
    by_cases hs : M.scale j = 0
    · simp [hs]
    · have hcpos : 0 < c := by linarith
      have hc1pos : 0 < c - 1 := by linarith
      have hspos : 0 < M.scale j :=
        lt_of_le_of_ne (M.scale_nonnegative j) (Ne.symm hs)
      have hdpos : 0 < M.delta j := M.delta_positive j
      have hnpos : 0 < ((t + 1 : ℕ) : ℝ) := by positivity
      have hsqrtnpos : 0 < Real.sqrt ((t + 1 : ℕ) : ℝ) :=
        Real.sqrt_pos.2 hnpos
      have hroot_le :
          Real.sqrt ((t + 1 : ℕ) : ℝ) ≤
            Real.sqrt (max (((t + 1 : ℕ) : ℝ))
              (c * (c - 1) / M.delta j)) :=
        Real.sqrt_le_sqrt (le_max_left _ _)
      have hsqrtmaxpos : 0 < Real.sqrt (max (((t + 1 : ℕ) : ℝ))
          (c * (c - 1) / M.delta j)) :=
        lt_of_lt_of_le hsqrtnpos hroot_le
      have hinv :
          1 / Real.sqrt (max (((t + 1 : ℕ) : ℝ))
              (c * (c - 1) / M.delta j)) ≤
            1 / Real.sqrt ((t + 1 : ℕ) : ℝ) := by
        apply (div_le_div_iff₀ hsqrtmaxpos hsqrtnpos).2
        simpa only [one_mul] using hroot_le
      have heq :
          (c / (c - 1)) * (2 / W (t + 1) j) *
              (8 * (M.scale j) ^ 2 / M.delta j) =
            (4 * Real.sqrt c / Real.sqrt (c - 1)) *
              (M.scale j / Real.sqrt (M.delta j)) *
                (1 / Real.sqrt (max (((t + 1 : ℕ) : ℝ))
                  (c * (c - 1) / M.delta j))) := by
        dsimp [W]
        field_simp [ne_of_gt hcpos, ne_of_gt hc1pos,
          ne_of_gt (Real.sqrt_pos.2 hcpos),
          ne_of_gt (Real.sqrt_pos.2 hc1pos),
          ne_of_gt hdpos, ne_of_gt (Real.sqrt_pos.2 hdpos),
          ne_of_gt hspos, ne_of_gt hsqrtmaxpos]
        rw [Real.sq_sqrt hcpos.le, Real.sq_sqrt hc1pos.le,
          Real.sq_sqrt hdpos.le]
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left hinv
        (mul_nonneg
          (div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
            (Real.sqrt_nonneg _))
          (div_nonneg (M.scale_nonnegative j) (Real.sqrt_nonneg _)))
  letI : MeasureTheory.IsProbabilityMeasure M.measure := M.probability_measure
  have hGap_integral_nonneg (t : ℕ) (j : Fin M.depth) :
      0 ≤ ∫ ω, Gap t ω j ∂M.measure :=
    MeasureTheory.integral_nonneg (fun ω => hGap_nonneg t ω j)
  have hGap_integral_bound (t : ℕ) (j : Fin M.depth) :
      (∫ ω, Gap t ω j ∂M.measure) ≤
        Real.sqrt ((M.levelNodes j).card : ℝ) := by
    calc
      (∫ ω, Gap t ω j ∂M.measure) ≤
          ∫ _ω : Ω, Real.sqrt ((M.levelNodes j).card : ℝ) ∂M.measure := by
        apply MeasureTheory.integral_mono (hGap_integrable t j)
          (MeasureTheory.integrable_const _)
        intro ω
        exact nested_tsallis_level_gap_bound M (run.distribution t ω)
          (run.distribution_mem t ω) j
      _ = Real.sqrt ((M.levelNodes j).card : ℝ) := by
        rw [MeasureTheory.integral_const]
        simp
  have hvariance_factor_nonneg (t : ℕ) (j : Fin M.depth) :
      0 ≤ (c / (c - 1)) * (2 / W (t + 1) j) := by
    exact mul_nonneg (div_nonneg (by linarith) (by linarith))
      (div_nonneg (by norm_num) (hW_nonneg (t + 1) j))
  have hvariance_bound :
      (∑ t ∈ Finset.range T,
          ∑ j, (c / (c - 1)) * (2 / W (t + 1) j) *
            ∫ ω, Var t ω j ∂M.measure) ≤
        (4 * Real.sqrt c / Real.sqrt (c - 1)) *
          ∑ t ∈ Finset.range T,
            (1 / Real.sqrt ((t + 1 : ℕ) : ℝ)) *
              ∑ j, (M.scale j / Real.sqrt (M.delta j)) *
                ∫ ω, Gap t ω j ∂M.measure := by
    calc
      (∑ t ∈ Finset.range T,
          ∑ j, (c / (c - 1)) * (2 / W (t + 1) j) *
            ∫ ω, Var t ω j ∂M.measure) ≤
          ∑ t ∈ Finset.range T,
            ∑ j, (c / (c - 1)) * (2 / W (t + 1) j) *
              ((8 * (M.scale j) ^ 2 / M.delta j) *
                ∫ ω, Gap t ω j ∂M.measure) := by
        apply Finset.sum_le_sum
        intro t ht
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hVar_integral_bound t j)
          (hvariance_factor_nonneg t j)
      _ ≤ ∑ t ∈ Finset.range T,
            ∑ j, ((4 * Real.sqrt c / Real.sqrt (c - 1)) *
              (M.scale j / Real.sqrt (M.delta j)) *
                (1 / Real.sqrt ((t + 1 : ℕ) : ℝ))) *
                  ∫ ω, Gap t ω j ∂M.measure := by
        apply Finset.sum_le_sum
        intro t ht
        apply Finset.sum_le_sum
        intro j hj
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right (hvariance_coefficient t j)
            (hGap_integral_nonneg t j)
      _ = (4 * Real.sqrt c / Real.sqrt (c - 1)) *
          ∑ t ∈ Finset.range T,
            (1 / Real.sqrt ((t + 1 : ℕ) : ℝ)) *
              ∑ j, (M.scale j / Real.sqrt (M.delta j)) *
                ∫ ω, Gap t ω j ∂M.measure := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        rw [← mul_assoc, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hinit_bound :
      (∑ j, W 1 j * ∫ ω, Gap 0 ω j ∂M.measure) ≤
        4 * c * ∑ j, (M.scale j / M.delta j) *
          Real.sqrt ((M.levelNodes j).card : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    rw [hW_one]
    calc
      (4 * c * M.scale j / M.delta j) *
          ∫ ω, Gap 0 ω j ∂M.measure ≤
        (4 * c * M.scale j / M.delta j) *
          Real.sqrt ((M.levelNodes j).card : ℝ) :=
        mul_le_mul_of_nonneg_left (hGap_integral_bound 0 j)
          (div_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) (by linarith))
              (M.scale_nonnegative j))
            (M.delta_positive j).le)
      _ = 4 * c * ((M.scale j / M.delta j) *
          Real.sqrt ((M.levelNodes j).card : ℝ)) := by ring
  have hTpred : T - 1 + 1 = T := Nat.sub_add_cancel hT
  have hdrift_split :
      (∑ t ∈ Finset.range T,
          ∑ j, (W (t + 2) j - W (t + 1) j) *
            ∫ ω, Gap (t + 1) ω j ∂M.measure) =
        (∑ t ∈ Finset.range (T - 1),
          ∑ j, (W (t + 2) j - W (t + 1) j) *
            ∫ ω, Gap (t + 1) ω j ∂M.measure) +
        ∑ j, (W (T + 1) j - W T j) *
          ∫ ω, Gap T ω j ∂M.measure := by
    calc
      (∑ t ∈ Finset.range T,
          ∑ j, (W (t + 2) j - W (t + 1) j) *
            ∫ ω, Gap (t + 1) ω j ∂M.measure) =
        ∑ t ∈ Finset.range ((T - 1) + 1),
          ∑ j, (W (t + 2) j - W (t + 1) j) *
            ∫ ω, Gap (t + 1) ω j ∂M.measure := by rw [hTpred]
      _ = (∑ t ∈ Finset.range (T - 1),
          ∑ j, (W (t + 2) j - W (t + 1) j) *
            ∫ ω, Gap (t + 1) ω j ∂M.measure) +
          ∑ j, (W ((T - 1) + 2) j - W ((T - 1) + 1) j) *
            ∫ ω, Gap ((T - 1) + 1) ω j ∂M.measure := by
        rw [Finset.sum_range_succ]
      _ = _ := by
        have hTpred2 : T - 1 + 2 = T + 1 := by omega
        rw [hTpred, hTpred2]
  have hterminal_bound :
      (∑ j, (W (T + 1) j - W T j) *
          ∫ ω, Gap T ω j ∂M.measure) ≤
        2 * c * ∑ j, (M.scale j / M.delta j) *
          Real.sqrt ((M.levelNodes j).card : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    calc
      (W (T + 1) j - W T j) *
          ∫ ω, Gap T ω j ∂M.measure ≤
        (2 * c * M.scale j / M.delta j) *
          ∫ ω, Gap T ω j ∂M.measure :=
        mul_le_mul_of_nonneg_right (hW_terminal j)
          (hGap_integral_nonneg T j)
      _ ≤ (2 * c * M.scale j / M.delta j) *
          Real.sqrt ((M.levelNodes j).card : ℝ) :=
        mul_le_mul_of_nonneg_left (hGap_integral_bound T j)
          (div_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) (by linarith))
              (M.scale_nonnegative j))
            (M.delta_positive j).le)
      _ = 2 * c * ((M.scale j / M.delta j) *
          Real.sqrt ((M.levelNodes j).card : ℝ)) := by ring
  have hinv_sqrt_shift (s : ℕ) (hs : 1 ≤ s) :
      1 / Real.sqrt (s : ℝ) ≤
        2 / Real.sqrt ((s + 1 : ℕ) : ℝ) := by
    have hspos : 0 < (s : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hs)
    have hsnextpos : 0 < ((s + 1 : ℕ) : ℝ) := by positivity
    have hroot :
        Real.sqrt ((s + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (s : ℝ) := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · have hsquare :
            (Real.sqrt (s : ℝ)) ^ 2 = (s : ℝ) :=
          Real.sq_sqrt hspos.le
        have hsone : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
        norm_num [pow_two] at ⊢
        nlinarith [hsquare]
    apply (div_le_div_iff₀ (Real.sqrt_pos.2 hspos)
      (Real.sqrt_pos.2 hsnextpos)).2
    simpa only [one_mul] using hroot
  have hW_diff_shift (t : ℕ) (j : Fin M.depth) :
      W (t + 2) j - W (t + 1) j ≤
        (4 * Real.sqrt c / Real.sqrt (c - 1)) *
          (M.scale j / Real.sqrt (M.delta j)) *
            (1 / Real.sqrt ((t + 2 : ℕ) : ℝ)) := by
    have hfactor : 0 ≤
        (2 * Real.sqrt c / Real.sqrt (c - 1)) *
          (M.scale j / Real.sqrt (M.delta j)) := by
      exact mul_nonneg
        (div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _))
        (div_nonneg (M.scale_nonnegative j) (Real.sqrt_nonneg _))
    calc
      W (t + 2) j - W (t + 1) j ≤
          (2 * Real.sqrt c / Real.sqrt (c - 1)) *
            (M.scale j / Real.sqrt (M.delta j)) *
              (1 / Real.sqrt ((t + 1 : ℕ) : ℝ)) :=
        hW_diff (t + 1) (by omega) j
      _ ≤ (2 * Real.sqrt c / Real.sqrt (c - 1)) *
            (M.scale j / Real.sqrt (M.delta j)) *
              (2 / Real.sqrt ((t + 2 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (hinv_sqrt_shift (t + 1) (by omega))
          hfactor
      _ = (4 * Real.sqrt c / Real.sqrt (c - 1)) *
          (M.scale j / Real.sqrt (M.delta j)) *
            (1 / Real.sqrt ((t + 2 : ℕ) : ℝ)) := by ring
  let S : ℕ → ℝ := fun t =>
    (1 / Real.sqrt ((t + 1 : ℕ) : ℝ)) *
      ∑ j, (M.scale j / Real.sqrt (M.delta j)) *
        ∫ ω, Gap t ω j ∂M.measure
  have hS_nonneg (t : ℕ) : 0 ≤ S t := by
    dsimp [S]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j hj =>
      mul_nonneg
        (div_nonneg (M.scale_nonnegative j) (Real.sqrt_nonneg _))
        (hGap_integral_nonneg t j))
  have hinterior_raw :
      (∑ t ∈ Finset.range (T - 1),
          ∑ j, (W (t + 2) j - W (t + 1) j) *
            ∫ ω, Gap (t + 1) ω j ∂M.measure) ≤
        (4 * Real.sqrt c / Real.sqrt (c - 1)) *
          ∑ t ∈ Finset.range (T - 1), S (t + 1) := by
    calc
      (∑ t ∈ Finset.range (T - 1),
          ∑ j, (W (t + 2) j - W (t + 1) j) *
            ∫ ω, Gap (t + 1) ω j ∂M.measure) ≤
        ∑ t ∈ Finset.range (T - 1),
          ∑ j, ((4 * Real.sqrt c / Real.sqrt (c - 1)) *
            (M.scale j / Real.sqrt (M.delta j)) *
              (1 / Real.sqrt ((t + 2 : ℕ) : ℝ))) *
                ∫ ω, Gap (t + 1) ω j ∂M.measure := by
          apply Finset.sum_le_sum
          intro t ht
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_right (hW_diff_shift t j)
            (hGap_integral_nonneg (t + 1) j)
      _ = (4 * Real.sqrt c / Real.sqrt (c - 1)) *
          ∑ t ∈ Finset.range (T - 1), S (t + 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        dsimp [S]
        rw [← mul_assoc, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        norm_num
        ring_nf
  have hshift_sum_le :
      (∑ t ∈ Finset.range (T - 1), S (t + 1)) ≤
        ∑ t ∈ Finset.range T, S t := by
    calc
      (∑ t ∈ Finset.range (T - 1), S (t + 1)) ≤
          (∑ t ∈ Finset.range (T - 1), S (t + 1)) + S 0 :=
        le_add_of_nonneg_right (hS_nonneg 0)
      _ = ∑ t ∈ Finset.range ((T - 1) + 1), S t :=
        (Finset.sum_range_succ' S (T - 1)).symm
      _ = ∑ t ∈ Finset.range T, S t := by rw [hTpred]
  have hinterior_bound :
      (∑ t ∈ Finset.range (T - 1),
          ∑ j, (W (t + 2) j - W (t + 1) j) *
            ∫ ω, Gap (t + 1) ω j ∂M.measure) ≤
        (4 * Real.sqrt c / Real.sqrt (c - 1)) *
          ∑ t ∈ Finset.range T, S t :=
    le_trans hinterior_raw
      (mul_le_mul_of_nonneg_left hshift_sum_le
        (div_nonneg
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _)))
  rw [hdrift_split] at hintegrated
  change
    (∑ t ∈ Finset.range T,
        ∑ j, (c / (c - 1)) * (2 / W (t + 1) j) *
          ∫ ω, Var t ω j ∂M.measure) ≤
      (4 * Real.sqrt c / Real.sqrt (c - 1)) *
        ∑ t ∈ Finset.range T, S t at hvariance_bound
  have htotal :
      (∫ ω, ∑ t ∈ Finset.range T, ∑ a,
          run.estimatedLoss t ω a * (run.distribution t ω a - q a)
        ∂M.measure) ≤
        (8 * Real.sqrt c / Real.sqrt (c - 1)) *
          ∑ t ∈ Finset.range T, S t +
        6 * c * ∑ j, (M.scale j / M.delta j) *
          Real.sqrt ((M.levelNodes j).card : ℝ) := by
    calc
      _ ≤ (∑ j, W 1 j * ∫ ω, Gap 0 ω j ∂M.measure) +
          ((∑ t ∈ Finset.range (T - 1),
              ∑ j, (W (t + 2) j - W (t + 1) j) *
                ∫ ω, Gap (t + 1) ω j ∂M.measure) +
            ∑ j, (W (T + 1) j - W T j) *
              ∫ ω, Gap T ω j ∂M.measure) +
          ∑ t ∈ Finset.range T,
            ∑ j, (c / (c - 1)) * (2 / W (t + 1) j) *
              ∫ ω, Var t ω j ∂M.measure := hintegrated
      _ ≤ 4 * c * ∑ j, (M.scale j / M.delta j) *
            Real.sqrt ((M.levelNodes j).card : ℝ) +
          ((4 * Real.sqrt c / Real.sqrt (c - 1)) *
              ∑ t ∈ Finset.range T, S t +
            2 * c * ∑ j, (M.scale j / M.delta j) *
              Real.sqrt ((M.levelNodes j).card : ℝ)) +
          (4 * Real.sqrt c / Real.sqrt (c - 1)) *
            ∑ t ∈ Finset.range T, S t :=
        add_le_add
          (add_le_add hinit_bound
            (add_le_add hinterior_bound hterminal_bound))
          hvariance_bound
      _ = _ := by ring
  simpa [q, Gap, S] using htotal

@[blueprint "lem:sparse-nested-tsallis-ftrl-estimate"
  (statement := /-- Let $c\geq2$ and $T\geq1$, and let $\rho$ be a two-point FTRL run on a hierarchical two-point bandit $M$. Suppose that, for every $t\geq1$ and every $x\in\Delta_{\mathcal A}$, the regularizer of $\rho$ at $x$ is $\Psi_t^{(c)}(x)$, and suppose that the shift at level $j$ is $\sigma_j$. Write $p_t[v]=\sum_{a:\,v\preceq a}p_t(a)$. Then the regret of the first executed action satisfies
  \[
  R_T^{(1)}
  \leq
  \frac{8\sqrt c}{\sqrt{c-1}}
  \sum_{t<T}\frac1{\sqrt{t+1}}
  \sum_{j\in[L]}\frac{\sigma_j}{\sqrt{\delta_j}}\,
  \mathbb E\!\left[
    \sum_{v\in V_j}\bigl(\sqrt{p_t[v]}-p_t[v]\bigr)
  \right]
  +6c\sum_{j\in[L]}\frac{\sigma_j}{\delta_j}\sqrt{|V_j|}.
  \] -/)
  (proof := /-- Let $q_T$ be the probability vector concentrated at the expected-loss-minimizing action $a_T^*$. By \cref{lem:estimated-regret-representation}, $R_T^{(1)}$ is the integral of
  \[
  \sum_{t<T}\langle z_t,p_t-q_T\rangle.
  \]
  The hypotheses on the regularizer and shifts are exactly those of \cref{lem:nested-tsallis-objective-gap}. Applying that lemma to the same comparator $q_T$ bounds this integral by the displayed stability term and the initial term with coefficient $6c$. Combining the equality with this inequality proves the assertion. -/)
  (title := /-- Sparse nested-Tsallis FTRL estimate -/)
  (latexEnv := "lemma")]
lemma sparse_nested_tsallis_ftrl_estimate
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M)
    (c : ℝ) (T : ℕ) (hc : 2 ≤ c) (hT : 1 ≤ T)
    (hregularizer :
      ∀ t x, 1 ≤ t → probability_vector x →
        run.regularizer t x = generic_nested_tsallis_regularizer M c t x)
    (hshift : ∀ j, run.shift j = M.scale j) :
    first_action_regret M T ≤
      (8 * Real.sqrt c / Real.sqrt (c - 1)) *
        ∑ t ∈ Finset.range T,
          (1 / Real.sqrt ((t + 1 : ℕ) : ℝ)) *
            ∑ j,
              (M.scale j / Real.sqrt (M.delta j)) *
                ∫ ω, ∑ v ∈ M.levelNodes j,
                  (Real.sqrt (subtree_mass M (run.distribution t ω) v) -
                    subtree_mass M (run.distribution t ω) v) ∂M.measure
      + 6 * c *
          ∑ j, (M.scale j / M.delta j) *
            Real.sqrt ((M.levelNodes j).card : ℝ) := by
  exact (estimated_regret_representation M run T).le.trans
    (nested_tsallis_objective_gap M run c T hc hT hregularizer hshift)

@[blueprint "lem:sparse-nested-tsallis-adversarial-bound"
  (statement := /-- Let $M$ be a hierarchical two-point bandit, let $\rho$ be a two-point FTRL run on $M$, let $c\geq2$, and let $T\geq1$ be an integer. Suppose that, for every integer $t\geq1$ and every probability vector $x\in\Delta_{\mathcal A}$, the regularizer of $\rho$ at time $t$ and vector $x$ is $\Psi_t^{(c)}(x)$ as defined in \cref{def:generic-nested-tsallis-regularizer}, and suppose that the shift of $\rho$ at every level $j\in[L]$ is $\sigma_j$. Then the regret of the first executed action satisfies
  \[
  R_T^{(1)}\leq
  6c\sum_{j\in[L]}\frac{\sigma_j}{\delta_j}\sqrt{|V_j|}
  +\frac{16\sqrt c}{\sqrt{c-1}}
  \sum_{j\in[L]}\frac{\sigma_j}{\sqrt{\delta_j}}\sqrt{|V_j|T}
  =B_T(c).
  \] -/)
  (proof := /-- Apply \cref{lem:sparse-nested-tsallis-ftrl-estimate}. For every round $t$ and level $j$, \cref{lem:nested-tsallis-level-gap-bound} gives the pointwise estimate
  \[
  \sum_{v\in V_j}\bigl(\sqrt{p_t[v]}-p_t[v]\bigr)
  \leq\sqrt{|V_j|}.
  \]
  The left-hand side is integrable by \cref{lem:nested-tsallis-level-gap-integrable}; hence monotonicity of the integral and the probability-measure property of $M$ give the same estimate after integration.

  For every integer $N\geq0$, induction proves
  \[
  \sum_{t<N}\frac1{\sqrt{t+1}}\leq2\sqrt N.
  \]
  Indeed, the assertion is immediate for $N=0$. For the induction step, put $a=\sqrt n$ and $b=\sqrt{n+1}$. Then $0\leq a\leq b$, $b>0$, and $b^2-a^2=1$; therefore
  \[
  \frac1b\leq2(b-a),
  \]
  because $2b(b-a)-(b^2-a^2)=(b-a)^2\geq0$. Adding this inequality to the induction hypothesis proves the claim at $n+1$.

  The coefficients $\sigma_j/\sqrt{\delta_j}$ and the time weights are nonnegative. Thus the two preceding estimates bound the stability term by
  \[
  \frac{8\sqrt c}{\sqrt{c-1}}\,2\sqrt T
  \sum_{j\in[L]}\frac{\sigma_j}{\sqrt{\delta_j}}\sqrt{|V_j|}.
  \]
  Finally, $\sqrt{|V_j|}\sqrt T=\sqrt{|V_j|T}$, and rearranging the factors yields the coefficient $16\sqrt c/\sqrt{c-1}$. Adding the unchanged initialization term gives exactly \cref{def:generic-adversarial-bound}. -/)
  (title := /-- Adversarial consequence of sparse nested-Tsallis stability -/)
  (latexEnv := "lemma")]
lemma sparse_nested_tsallis_adversarial_bound
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M)
    (c : ℝ) (T : ℕ) (hc : 2 ≤ c) (hT : 1 ≤ T)
    (hregularizer :
      ∀ t x, 1 ≤ t → probability_vector x →
        run.regularizer t x = generic_nested_tsallis_regularizer M c t x)
    (hshift : ∀ j, run.shift j = M.scale j) :
    first_action_regret M T ≤ generic_adversarial_bound M c T := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure M.measure := M.probability_measure
  have hlevel (t : ℕ) (j : Fin M.depth) :
      (∫ ω, ∑ v ∈ M.levelNodes j,
        (Real.sqrt (subtree_mass M (run.distribution t ω) v) -
          subtree_mass M (run.distribution t ω) v) ∂M.measure) ≤
        Real.sqrt ((M.levelNodes j).card : ℝ) := by
    calc
      (∫ ω, ∑ v ∈ M.levelNodes j,
        (Real.sqrt (subtree_mass M (run.distribution t ω) v) -
          subtree_mass M (run.distribution t ω) v) ∂M.measure) ≤
        ∫ _ : Ω, Real.sqrt ((M.levelNodes j).card : ℝ) ∂M.measure := by
          apply MeasureTheory.integral_mono
          · exact nested_tsallis_level_gap_integrable M run t j
          · exact MeasureTheory.integrable_const _
          · intro ω
            exact nested_tsallis_level_gap_bound M (run.distribution t ω)
              (run.distribution_mem t ω) j
      _ = Real.sqrt ((M.levelNodes j).card : ℝ) := by simp
  have htime_all : ∀ N : ℕ,
      (∑ t ∈ Finset.range N, 1 / Real.sqrt ((t + 1 : ℕ) : ℝ)) ≤
        2 * Real.sqrt N := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
      have hnat : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
      have hroot : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) :=
        Real.sqrt_le_sqrt hnat
      have hsqn : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
        Real.sq_sqrt (by positivity)
      have hsqn1 : (Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ 2 =
          ((n + 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
      have hbpos : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) :=
        Real.sqrt_pos.2 (by positivity)
      have hstep : 1 / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤
          2 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) := by
        apply (div_le_iff₀ hbpos).2
        nlinarith [sq_nonneg
          (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ))]
      calc
        (∑ t ∈ Finset.range n, 1 / Real.sqrt ((t + 1 : ℕ) : ℝ)) +
            1 / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤
          2 * Real.sqrt (n : ℝ) +
            1 / Real.sqrt ((n + 1 : ℕ) : ℝ) := by linarith
        _ ≤ 2 * Real.sqrt ((n + 1 : ℕ) : ℝ) := by linarith
  let C : ℝ := ∑ j,
    (M.scale j / Real.sqrt (M.delta j)) *
      Real.sqrt ((M.levelNodes j).card : ℝ)
  have hcoef (j : Fin M.depth) :
      0 ≤ M.scale j / Real.sqrt (M.delta j) :=
    div_nonneg (M.scale_nonnegative j) (Real.sqrt_nonneg _)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (hcoef j) (Real.sqrt_nonneg _)
  have hinner (t : ℕ) :
      (∑ j, (M.scale j / Real.sqrt (M.delta j)) *
        ∫ ω, ∑ v ∈ M.levelNodes j,
          (Real.sqrt (subtree_mass M (run.distribution t ω) v) -
            subtree_mass M (run.distribution t ω) v) ∂M.measure) ≤ C := by
    dsimp [C]
    exact Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (hlevel t j) (hcoef j)
  have hweighted :
      (∑ t ∈ Finset.range T,
        (1 / Real.sqrt ((t + 1 : ℕ) : ℝ)) *
          ∑ j, (M.scale j / Real.sqrt (M.delta j)) *
            ∫ ω, ∑ v ∈ M.levelNodes j,
              (Real.sqrt (subtree_mass M (run.distribution t ω) v) -
                subtree_mass M (run.distribution t ω) v) ∂M.measure) ≤
        (∑ t ∈ Finset.range T,
          1 / Real.sqrt ((t + 1 : ℕ) : ℝ)) * C := by
    calc
      (∑ t ∈ Finset.range T,
        (1 / Real.sqrt ((t + 1 : ℕ) : ℝ)) *
          ∑ j, (M.scale j / Real.sqrt (M.delta j)) *
            ∫ ω, ∑ v ∈ M.levelNodes j,
              (Real.sqrt (subtree_mass M (run.distribution t ω) v) -
                subtree_mass M (run.distribution t ω) v) ∂M.measure) ≤
        ∑ t ∈ Finset.range T,
          (1 / Real.sqrt ((t + 1 : ℕ) : ℝ)) * C := by
            apply Finset.sum_le_sum
            intro t ht
            exact mul_le_mul_of_nonneg_left (hinner t) (by positivity)
      _ = (∑ t ∈ Finset.range T,
          1 / Real.sqrt ((t + 1 : ℕ) : ℝ)) * C := by
        rw [Finset.sum_mul]
  have hsum :
      (∑ t ∈ Finset.range T,
        (1 / Real.sqrt ((t + 1 : ℕ) : ℝ)) *
          ∑ j, (M.scale j / Real.sqrt (M.delta j)) *
            ∫ ω, ∑ v ∈ M.levelNodes j,
              (Real.sqrt (subtree_mass M (run.distribution t ω) v) -
                subtree_mass M (run.distribution t ω) v) ∂M.measure) ≤
        2 * Real.sqrt T * C :=
    hweighted.trans (mul_le_mul_of_nonneg_right (htime_all T) hC)
  have hfactor : 0 ≤ 8 * Real.sqrt c / Real.sqrt (c - 1) :=
    div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  have hstability := mul_le_mul_of_nonneg_left hsum hfactor
  have hsqrt_product (j : Fin M.depth) :
      Real.sqrt (((M.levelNodes j).card : ℝ) * T) =
        Real.sqrt ((M.levelNodes j).card : ℝ) * Real.sqrt T := by
    rw [Real.sqrt_mul (by positivity)]
  have hsum_product :
      (∑ j, (M.scale j / Real.sqrt (M.delta j)) *
        Real.sqrt (((M.levelNodes j).card : ℝ) * T)) = C * Real.sqrt T := by
    dsimp [C]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsqrt_product j]
    ring
  refine (sparse_nested_tsallis_ftrl_estimate M run c T hc hT hregularizer hshift).trans ?_
  unfold generic_adversarial_bound
  rw [hsum_product]
  calc
    8 * Real.sqrt c / Real.sqrt (c - 1) *
          (∑ t ∈ Finset.range T,
            (1 / Real.sqrt ((t + 1 : ℕ) : ℝ)) *
              ∑ j, (M.scale j / Real.sqrt (M.delta j)) *
                ∫ ω, ∑ v ∈ M.levelNodes j,
                  (Real.sqrt (subtree_mass M (run.distribution t ω) v) -
                    subtree_mass M (run.distribution t ω) v) ∂M.measure) +
        6 * c * ∑ j, (M.scale j / M.delta j) *
          Real.sqrt ((M.levelNodes j).card : ℝ) ≤
      8 * Real.sqrt c / Real.sqrt (c - 1) * (2 * Real.sqrt T * C) +
        6 * c * ∑ j, (M.scale j / M.delta j) *
          Real.sqrt ((M.levelNodes j).card : ℝ) :=
        add_le_add hstability (le_refl _)
    _ = 6 * c * ∑ j, (M.scale j / M.delta j) *
          Real.sqrt ((M.levelNodes j).card : ℝ) +
        16 * Real.sqrt c / Real.sqrt (c - 1) * (C * Real.sqrt T) := by
      ring

@[blueprint "lem:multibaseline-zero-gap-stability"
  (statement := /-- Let $M$ be a hierarchical two-point bandit, let $\rho$ be a two-point FTRL run on $M$, let $c\geq2$, and let $T\geq1$. Suppose that the regularizer of $\rho$ is $\Psi_t^{(c)}$ at every positive time and every probability vector, that its level-$j$ shift is $\sigma_j$, and that $M$ satisfies \cref{def:generalized-stochastic-condition}. Put
  \[
  D_T=\mathbb E\sum_{t<T}\sum_{a\in\mathcal A}p_t(a)\Delta(a),
  \]
  and let $q_T$ be the point mass at the expected-loss-minimizing action $a_T^*$. Then the estimator in \cref{def:two-point-ftrl-run} satisfies
  \[
  \begin{aligned}
  \mathbb E\sum_{t<T}\langle z_t,p_t-q_T\rangle
  \leq{}&\frac12D_T
  +6c\sum_{j\in[L]}\frac{\sigma_j}{\delta_j}\sqrt{|V_j|}\\
  &+\frac{32c}{c-1}K_{\mathrm{eff}}^{\mathrm{sto}}
       (\sigma/\sqrt\delta)\log(eT).
  \end{aligned}
  \]
  In particular, the stability contribution of a level is indexed only by nodes having positive `nodeGap`. This conclusion uses the zero-gap blockwise stability field in \cref{def:two-point-ftrl-run}; it does not follow from normalization of the level masses. -/)
  (proof := /-- Apply \cref{lem:nested-tsallis-ftrl-decomposition} with comparator $q_T$ and expand $z_t$ using \cref{def:two-point-ftrl-run} before applying any quadratic estimate. For each $v\in V_j$ with $\Delta_v=0$, the attainment clause of \cref{def:hierarchical-two-point-bandit} supplies a descendant $r_v$ with $\Delta(r_v)=0$. By \cref{def:generalized-stochastic-condition}, after intersecting the finitely many conull events needed for $t<T$, all representatives $r_v$ have the same realized loss as the distinguished optimal action.

  In the one-step FTRL stability pairing, subtract on each zero-gap block the potential of its representative $r_v$. If $b_{t,j,v}$ denotes the subtracted potential, the resulting correction is exactly
  \[
  \sum_{v\in V_j}b_{t,j,v}\bigl(p_t[v]-p_{t+1}[v]\bigr).
  \tag{1}
  \]
  The family $(b_{t,j,v})_{v\in V_j}$ is supported on nodes with $\Delta_v=0$. Hence (1) vanishes pointwise by the zero-gap blockwise stability field of \cref{def:two-point-ftrl-run}. This invocation is essential: \cref{lem:subtree-mass-level-probability} gives only $\sum_v(p_t[v]-p_{t+1}[v])=0$, which cancels a common scalar potential but not independently chosen block potentials. In particular, no conditional-unbiasedness argument is applied to $p_{t+1}$.

  On the conull event fixed above, the centered loss difference on a zero-gap block vanishes because its representative and the distinguished action have the same realized loss. Thus the blockwise stability identity removes all zero-gap coordinates, and the remaining stability sum is
  \[
  \sum_{t<T}\sum_j\beta_{t,j}
    \mathbb E\sum_{\substack{v\in V_j\\ \Delta_v>0}}\sqrt{p_t[v]},
  \qquad
  \beta_{t,j}=\frac{8\sqrt c}{\sqrt{c-1}}
       \frac{\sigma_j}{\sqrt{\delta_j(t+1)}}.
  \tag{2}
  \]

  To obtain (2), \cref{lem:feedback-atom-null-of-not-parent-common} restricts the two sampled actions to one parent class, and \cref{lem:parent-common-loss-difference-bound} together with the shift hypothesis places the shifted atom in $[0,2\sigma_j]$. The masses needed in the blockwise quotient are nonnegative and normalized by \cref{lem:subtree-mass-level-probability}. On a positive-mass block apply \cref{lem:tsallis-bregman-stability-bound}; at zero mass, perturb the distribution toward a descendant point mass and use \cref{lem:right-derivative-nonnegative-at-interval-min}. This proves the quotient estimate without dividing by a zero mass.

  Set
  \[
  A=\sum_j\frac{\sigma_j}{\sqrt{\delta_j}}
       \sqrt{\Gamma(j,\Delta)}.
  \]
  If $A=0$, (2) is zero. Otherwise assign level weight
  $\lambda_j=\sigma_j\sqrt{\Gamma(j,\Delta)/\delta_j}/A$ whenever its numerator is positive. For every positive-gap node, Young's inequality gives
  \[
  \beta_{t,j}\sqrt{p_t[v]}
  \leq \frac{\lambda_j}{2}\Delta_vp_t[v]
       +\frac{\beta_{t,j}^2}{2\lambda_j\Delta_v}.
  \]
  Since $\Delta_v\leq\Delta(a)$ for each descendant $a$ of $v$, the first terms sum to at most $D_T/2$. By \cref{def:level-gap-complexity,def:stochastic-effective-action-number}, the reciprocal-gap terms sum to at most
  \[
  \frac{32c}{c-1}K_{\mathrm{eff}}^{\mathrm{sto}}
       (\sigma/\sqrt\delta)\sum_{t<T}\frac1{t+1},
  \]
  and the harmonic sum is at most $\log(eT)$. Finally, \cref{lem:nonnegative-first-level-weight,lem:nested-tsallis-level-gap-integrable,lem:nested-tsallis-level-gap-bound} bound the initial and time-varying regularizer terms by
  $6c\sum_j(\sigma_j/\delta_j)\sqrt{|V_j|}$. Combining these estimates proves the assertion. -/)
  (title := /-- Multi-baseline control of zero-gap subtree stability -/)
  (latexEnv := "lemma")]
lemma multibaseline_zero_gap_stability
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M)
    (c : ℝ) (T : ℕ) (hc : 2 ≤ c) (hT : 1 ≤ T)
    (hregularizer :
      ∀ t x, 1 ≤ t → probability_vector x →
        run.regularizer t x = generic_nested_tsallis_regularizer M c t x)
    (hshift : ∀ j, run.shift j = M.scale j)
    (hstochastic : generalized_stochastic_condition M) :
    (∫ ω, ∑ t ∈ Finset.range T, ∑ a,
        run.estimatedLoss t ω a *
          (run.distribution t ω a - if a = M.bestAction T then 1 else 0)
      ∂M.measure) ≤
      (∫ ω, ∑ t ∈ Finset.range T, ∑ a,
          run.distribution t ω a * M.gap a ∂M.measure) / 2 +
        6 * c * ∑ j, (M.scale j / M.delta j) *
          Real.sqrt ((M.levelNodes j).card : ℝ) +
        (32 * c / (c - 1)) * stochastic_effective_action_number M *
          Real.log (Real.exp 1 * T) := by
  classical
  letI := M.probability_measure
  obtain ⟨hgapcond, hoptgap, hzero⟩ := hstochastic
  have hhist : ∀ s : ℕ, M.history s ≤ (inferInstance : MeasurableSpace Ω) := fun s =>
    (run.feedback_loss_conditional_independence s).1
  have hp : ∀ (t : ℕ) (ω : Ω),
      (∀ a, 0 ≤ run.distribution t ω a) ∧ ∑ a, run.distribution t ω a = 1 := by
    intro t ω
    have h := run.distribution_mem t ω
    change (∀ a, 0 ≤ run.distribution t ω a) ∧ ∑ a, run.distribution t ω a = 1 at h
    exact h
  have hdistint : ∀ (s : ℕ) (a : Action),
      MeasureTheory.Integrable (fun ω => run.distribution s ω a) M.measure := by
    intro s a
    apply (MeasureTheory.integrable_const (1 : ℝ)).mono'
      (((run.distribution_measurable s a).mono (hhist s)
        le_rfl).stronglyMeasurable.aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun ω => by
      have ha := mem_Icc_of_mem_stdSimplex (run.distribution_mem s ω) a
      rw [Real.norm_eq_abs, abs_of_nonneg ha.1]
      exact ha.2)
  have hgapint : ∀ t, MeasureTheory.Integrable
      (fun ω => ∑ a, run.distribution t ω a * M.gap a) M.measure := by
    intro t
    apply MeasureTheory.integrable_finsetSum Finset.univ
    intro a _
    exact (hdistint t a).mul_const (M.gap a)
  have hgapsumint : ∀ N : ℕ, MeasureTheory.Integrable
      (fun ω => ∑ t ∈ Finset.range N, ∑ a,
        run.distribution t ω a * M.gap a) M.measure := fun N =>
    MeasureTheory.integrable_finsetSum _ (fun t _ => hgapint t)
  have hpmean_int : ∀ t, MeasureTheory.Integrable
      (fun ω => ∑ a, run.distribution t ω a * M.conditionalMeanLoss t ω a) M.measure := by
    intro t
    apply MeasureTheory.integrable_finsetSum Finset.univ
    intro a _
    apply (M.conditionalMeanLoss_integrable t a).bdd_mul
      (((run.distribution_measurable t a).mono (hhist t)
        le_rfl).stronglyMeasurable.aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun ω => by
      have ha' := mem_Icc_of_mem_stdSimplex (run.distribution_mem t ω) a
      rw [Real.norm_eq_abs, abs_of_nonneg ha'.1]
      exact ha'.2)
  have hround : ∀ t,
      (∫ ω, ∑ a, run.distribution t ω a * M.gap a ∂M.measure) ≤
        (∫ ω, M.loss t ω (M.firstAction t ω) ∂M.measure) -
          ∫ ω, M.loss t ω M.optimalAction ∂M.measure := by
    intro t
    have hcmp := M.conditionalMeanLoss_integrable t M.optimalAction
    have hall : ∀ᵐ ω ∂M.measure, ∀ a : Action,
        M.gap a ≤ M.conditionalMeanLoss t ω a -
          M.conditionalMeanLoss t ω M.optimalAction := by
      rw [MeasureTheory.ae_all_iff]
      intro a
      exact hgapcond t a
    have hae : (fun ω => ∑ a, run.distribution t ω a * M.gap a) ≤ᵐ[M.measure]
        fun ω => (∑ a, run.distribution t ω a * M.conditionalMeanLoss t ω a) -
          M.conditionalMeanLoss t ω M.optimalAction := by
      filter_upwards [hall] with ω hω
      calc
        (∑ a, run.distribution t ω a * M.gap a) ≤
            ∑ a, run.distribution t ω a *
              (M.conditionalMeanLoss t ω a -
                M.conditionalMeanLoss t ω M.optimalAction) := by
              apply Finset.sum_le_sum
              intro a _
              exact mul_le_mul_of_nonneg_left (hω a) ((hp t ω).1 a)
        _ = (∑ a, run.distribution t ω a * M.conditionalMeanLoss t ω a) -
              (∑ a, run.distribution t ω a) *
                M.conditionalMeanLoss t ω M.optimalAction := by
              rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl (fun a _ => by ring)
        _ = (∑ a, run.distribution t ω a * M.conditionalMeanLoss t ω a) -
              M.conditionalMeanLoss t ω M.optimalAction := by
              rw [(hp t ω).2, one_mul]
    have hmono := MeasureTheory.integral_mono_ae (hgapint t)
      ((hpmean_int t).sub hcmp) hae
    have hopt_int :
        (∫ ω, M.loss t ω M.optimalAction ∂M.measure) =
          ∫ ω, M.conditionalMeanLoss t ω M.optimalAction ∂M.measure := by
      simpa using M.conditionalMeanLoss_spec t M.optimalAction Set.univ MeasurableSet.univ
    rw [hopt_int, first_executed_loss_expectation M run t,
      ← MeasureTheory.integral_sub (hpmean_int t) hcmp]
    exact hmono
  have hDle : ∀ N : ℕ, (∫ ω, ∑ t ∈ Finset.range N, ∑ a,
      run.distribution t ω a * M.gap a ∂M.measure) ≤ first_action_regret M N := by
    intro N
    have hDsum :
        (∫ ω, ∑ t ∈ Finset.range N, ∑ a,
            run.distribution t ω a * M.gap a ∂M.measure) =
          ∑ t ∈ Finset.range N,
            ∫ ω, ∑ a, run.distribution t ω a * M.gap a ∂M.measure :=
      MeasureTheory.integral_finsetSum (μ := M.measure) (Finset.range N)
        (fun t _ => hgapint t)
    have hfirstsum :
        (∫ ω, ∑ t ∈ Finset.range N, M.loss t ω (M.firstAction t ω) ∂M.measure) =
          ∑ t ∈ Finset.range N, ∫ ω, M.loss t ω (M.firstAction t ω) ∂M.measure :=
      MeasureTheory.integral_finsetSum (μ := M.measure) (Finset.range N)
        (fun t _ => M.first_executed_loss_integrable t)
    have hoptsum :
        (∫ ω, ∑ t ∈ Finset.range N, M.loss t ω M.optimalAction ∂M.measure) =
          ∑ t ∈ Finset.range N, ∫ ω, M.loss t ω M.optimalAction ∂M.measure :=
      MeasureTheory.integral_finsetSum (μ := M.measure) (Finset.range N)
        (fun t _ => M.loss_integrable t M.optimalAction)
    have hsumle :
        (∑ t ∈ Finset.range N, ∫ ω, ∑ a,
            run.distribution t ω a * M.gap a ∂M.measure) ≤
          (∑ t ∈ Finset.range N, ∫ ω, M.loss t ω (M.firstAction t ω) ∂M.measure) -
            ∑ t ∈ Finset.range N, ∫ ω, M.loss t ω M.optimalAction ∂M.measure := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum (fun t _ => hround t)
    have hbest := M.bestAction_minimizes N M.optimalAction
    unfold first_action_regret
    rw [hDsum]
    rw [hoptsum] at hbest
    rw [hfirstsum]
    linarith
  have hleafmass : ∀ (x : Action → ℝ) (a : Action),
      subtree_mass M x (M.leafNode a) = x a := by
    intro x a
    simp only [subtree_mass]
    rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
    · rw [if_pos ((M.leaf_descends_iff a a).2 rfl)]
    · intro b _ hba
      rw [if_neg]
      intro hb
      exact hba (((M.leaf_descends_iff a b).1 hb).symm)
  have hleafmem : ∀ a : Action, M.leafNode a ∈ M.levelNodes M.leafLevel := by
    intro a
    exact (M.leaf_nodes_exact (M.leafNode a)).2 ⟨a, rfl⟩
  have hleafgap : ∀ a : Action, M.nodeGap (M.leafNode a) = M.gap a := by
    intro a
    obtain ⟨b, hdesc, heq⟩ := M.nodeGap_attained M.leafLevel (M.leafNode a) (hleafmem a)
    have hab : a = b := (M.leaf_descends_iff a b).1 hdesc
    rw [heq, hab]
  have hstep : ∀ (t : ℕ) (ω : Ω) (a : Action), M.gap a = 0 →
      run.distribution (t + 1) ω a = run.distribution t ω a := by
    intro t ω a ha
    have hsupp : ∀ v, v ∈ M.levelNodes M.leafLevel → M.nodeGap v ≠ 0 →
        (if v = M.leafNode a then (1 : ℝ) else 0) = 0 := by
      intro v _ hgapv
      by_cases hva : v = M.leafNode a
      · exact absurd (by rw [hva, hleafgap a, ha] : M.nodeGap v = 0) hgapv
      · rw [if_neg hva]
    have hb := run.zero_gap_blockwise_stability t ω M.leafLevel
      (fun v => if v = M.leafNode a then (1 : ℝ) else 0) hsupp
    have hsingle : ∑ v ∈ M.levelNodes M.leafLevel,
        (if v = M.leafNode a then (1 : ℝ) else 0) *
          (subtree_mass M (run.distribution t ω) v -
            subtree_mass M (run.distribution (t + 1) ω) v) =
        run.distribution t ω a - run.distribution (t + 1) ω a := by
      rw [Finset.sum_eq_single_of_mem (M.leafNode a) (hleafmem a)
        (by
          intro v _ hne
          rw [if_neg hne, zero_mul])]
      rw [if_pos rfl, one_mul, hleafmass, hleafmass]
    rw [hsingle] at hb
    linarith
  have hconst : ∀ (t : ℕ) (ω : Ω) (a : Action), M.gap a = 0 →
      run.distribution t ω a = run.distribution 0 ω a := by
    intro t ω a ha
    induction t with
    | zero => rfl
    | succ n ih => rw [hstep n ω a ha, ih]
  have hmass_eq : ∀ (t : ℕ) (ω : Ω),
      (∑ a ∈ Finset.univ.filter (fun a => M.gap a ≠ 0), run.distribution t ω a) =
        ∑ a ∈ Finset.univ.filter (fun a => M.gap a ≠ 0), run.distribution 0 ω a := by
    intro t ω
    have hsplit : ∀ s : ℕ,
        (∑ a ∈ Finset.univ.filter (fun a => M.gap a ≠ 0), run.distribution s ω a) +
          ∑ a ∈ Finset.univ.filter (fun a => ¬ M.gap a ≠ 0),
            run.distribution s ω a = 1 := by
      intro s
      rw [Finset.sum_filter_add_sum_filter_not]
      exact (hp s ω).2
    have hZ :
        (∑ a ∈ Finset.univ.filter (fun a => ¬ M.gap a ≠ 0), run.distribution t ω a) =
          ∑ a ∈ Finset.univ.filter (fun a => ¬ M.gap a ≠ 0),
            run.distribution 0 ω a := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hconst t ω a (by simpa using (Finset.mem_filter.1 ha).2)
    have h1 := hsplit t
    have h2 := hsplit 0
    rw [hZ] at h1
    linarith
  have hmassint : MeasureTheory.Integrable
      (fun ω => ∑ a ∈ Finset.univ.filter (fun a => M.gap a ≠ 0),
        run.distribution 0 ω a) M.measure :=
    MeasureTheory.integrable_finsetSum _ (fun a _ => hdistint 0 a)
  have hmassnonneg : ∀ ω,
      0 ≤ ∑ a ∈ Finset.univ.filter (fun a => M.gap a ≠ 0), run.distribution 0 ω a :=
    fun ω => Finset.sum_nonneg (fun a _ => (hp 0 ω).1 a)
  have hmunonneg : 0 ≤ ∫ ω, ∑ a ∈ Finset.univ.filter (fun a => M.gap a ≠ 0),
      run.distribution 0 ω a ∂M.measure :=
    MeasureTheory.integral_nonneg hmassnonneg
  have hA : 0 ≤ ∑ j, (M.scale j / M.delta j) *
      Real.sqrt ((M.levelNodes j).card : ℝ) :=
    Finset.sum_nonneg fun j _ => mul_nonneg
      (div_nonneg (M.scale_nonnegative j) (M.delta_positive j).le) (Real.sqrt_nonneg _)
  have hB : 0 ≤ ∑ j, (M.scale j / Real.sqrt (M.delta j)) *
      Real.sqrt ((M.levelNodes j).card : ℝ) :=
    Finset.sum_nonneg fun j _ => mul_nonneg
      (div_nonneg (M.scale_nonnegative j) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hCadv : 0 ≤ (16 * Real.sqrt c / Real.sqrt (c - 1)) *
      ∑ j, (M.scale j / Real.sqrt (M.delta j)) *
        Real.sqrt ((M.levelNodes j).card : ℝ) :=
    mul_nonneg (div_nonneg (by positivity) (Real.sqrt_nonneg _)) hB
  have hadv_form : ∀ N : ℕ, generic_adversarial_bound M c N =
      6 * c * (∑ j, (M.scale j / M.delta j) *
          Real.sqrt ((M.levelNodes j).card : ℝ)) +
        ((16 * Real.sqrt c / Real.sqrt (c - 1)) *
          ∑ j, (M.scale j / Real.sqrt (M.delta j)) *
            Real.sqrt ((M.levelNodes j).card : ℝ)) * Real.sqrt N := by
    intro N
    unfold generic_adversarial_bound
    have hs : (∑ j, (M.scale j / Real.sqrt (M.delta j)) *
        Real.sqrt (((M.levelNodes j).card : ℝ) * N)) =
        (∑ j, (M.scale j / Real.sqrt (M.delta j)) *
          Real.sqrt ((M.levelNodes j).card : ℝ)) * Real.sqrt N := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [Real.sqrt_mul (Nat.cast_nonneg _)]
      ring
    rw [hs]
    ring
  have hmu0 : (∫ ω, ∑ a ∈ Finset.univ.filter (fun a => M.gap a ≠ 0),
      run.distribution 0 ω a ∂M.measure) = 0 := by
    rcases (Finset.univ.filter (fun a => M.gap a ≠ 0)).eq_empty_or_nonempty with
      hPe | hPne
    · rw [hPe]
      simp
    obtain ⟨a₀, ha₀, ha₀min⟩ :=
      (Finset.univ.filter (fun a => M.gap a ≠ 0)).exists_min_image M.gap hPne
    have ha₀ne : M.gap a₀ ≠ 0 := by simpa using (Finset.mem_filter.1 ha₀).2
    have hgapmin_pos : 0 < M.gap a₀ :=
      lt_of_le_of_ne (M.gap_nonnegative a₀) (Ne.symm ha₀ne)
    have hpt : ∀ (N : ℕ) (ω : Ω),
        M.gap a₀ * (N : ℝ) *
            (∑ a ∈ Finset.univ.filter (fun a => M.gap a ≠ 0),
              run.distribution 0 ω a) ≤
          ∑ t ∈ Finset.range N, ∑ a, run.distribution t ω a * M.gap a := by
      intro N ω
      have hterm : ∀ t : ℕ,
          M.gap a₀ * (∑ a ∈ Finset.univ.filter (fun a => M.gap a ≠ 0),
              run.distribution 0 ω a) ≤
            ∑ a, run.distribution t ω a * M.gap a := by
        intro t
        rw [← hmass_eq t ω, Finset.mul_sum]
        calc
          (∑ a ∈ Finset.univ.filter (fun a => M.gap a ≠ 0),
              M.gap a₀ * run.distribution t ω a) ≤
              ∑ a ∈ Finset.univ.filter (fun a => M.gap a ≠ 0),
                run.distribution t ω a * M.gap a := by
                apply Finset.sum_le_sum
                intro a ha
                have h1 : M.gap a₀ ≤ M.gap a := ha₀min a ha
                have h2 : 0 ≤ run.distribution t ω a := (hp t ω).1 a
                nlinarith
          _ ≤ ∑ a, run.distribution t ω a * M.gap a := by
                apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                intro a _ _
                exact mul_nonneg ((hp t ω).1 a) (M.gap_nonnegative a)
      calc
        M.gap a₀ * (N : ℝ) *
            (∑ a ∈ Finset.univ.filter (fun a => M.gap a ≠ 0),
              run.distribution 0 ω a) =
            ∑ _t ∈ Finset.range N, M.gap a₀ *
              (∑ a ∈ Finset.univ.filter (fun a => M.gap a ≠ 0),
                run.distribution 0 ω a) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              ring
        _ ≤ _ := Finset.sum_le_sum (fun t _ => hterm t)
    have hchain : ∀ N : ℕ, 1 ≤ N →
        M.gap a₀ * (N : ℝ) *
            (∫ ω, ∑ a ∈ Finset.univ.filter (fun a => M.gap a ≠ 0),
              run.distribution 0 ω a ∂M.measure) ≤
          6 * c * (∑ j, (M.scale j / M.delta j) *
              Real.sqrt ((M.levelNodes j).card : ℝ)) +
            ((16 * Real.sqrt c / Real.sqrt (c - 1)) *
              ∑ j, (M.scale j / Real.sqrt (M.delta j)) *
                Real.sqrt ((M.levelNodes j).card : ℝ)) * Real.sqrt N := by
      intro N hN
      have hint1 :
          M.gap a₀ * (N : ℝ) *
              (∫ ω, ∑ a ∈ Finset.univ.filter (fun a => M.gap a ≠ 0),
                run.distribution 0 ω a ∂M.measure) ≤
            ∫ ω, ∑ t ∈ Finset.range N, ∑ a,
              run.distribution t ω a * M.gap a ∂M.measure := by
        rw [← MeasureTheory.integral_const_mul]
        exact MeasureTheory.integral_mono (hmassint.const_mul _) (hgapsumint N)
          (fun ω => hpt N ω)
      have h3 := sparse_nested_tsallis_adversarial_bound M run c N hc hN
        hregularizer hshift
      rw [hadv_form N] at h3
      linarith [hDle N]
    by_contra hne
    have hmupos : 0 < ∫ ω, ∑ a ∈ Finset.univ.filter (fun a => M.gap a ≠ 0),
        run.distribution 0 ω a ∂M.measure :=
      lt_of_le_of_ne hmunonneg (Ne.symm hne)
    have hK : 0 < M.gap a₀ * ∫ ω, ∑ a ∈ Finset.univ.filter (fun a => M.gap a ≠ 0),
        run.distribution 0 ω a ∂M.measure := mul_pos hgapmin_pos hmupos
    obtain ⟨m, hm⟩ := exists_nat_gt
      (max (max (12 * c * (∑ j, (M.scale j / M.delta j) *
          Real.sqrt ((M.levelNodes j).card : ℝ)) /
        (M.gap a₀ * ∫ ω, ∑ a ∈ Finset.univ.filter (fun a => M.gap a ≠ 0),
          run.distribution 0 ω a ∂M.measure))
        ((2 * ((16 * Real.sqrt c / Real.sqrt (c - 1)) *
            ∑ j, (M.scale j / Real.sqrt (M.delta j)) *
              Real.sqrt ((M.levelNodes j).card : ℝ)) /
          (M.gap a₀ * ∫ ω, ∑ a ∈ Finset.univ.filter (fun a => M.gap a ≠ 0),
            run.distribution 0 ω a ∂M.measure)) ^ 2)) 1)
    have hm1 : (1 : ℝ) < (m : ℝ) := lt_of_le_of_lt (le_max_right _ _) hm
    have hmN : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · rw [h0] at hm1
        norm_num at hm1
      · exact hpos
    have hmXY := lt_of_le_of_lt (le_max_left _ _) hm
    have hX := lt_of_le_of_lt (le_max_left _ _) hmXY
    have hY := lt_of_le_of_lt (le_max_right _ _) hmXY
    have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
    have hsqrtm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmpos
    have hsqrtsq : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) :=
      Real.mul_self_sqrt hmpos.le
    have hXlt : 12 * c * (∑ j, (M.scale j / M.delta j) *
        Real.sqrt ((M.levelNodes j).card : ℝ)) <
        (M.gap a₀ * ∫ ω, ∑ a ∈ Finset.univ.filter (fun a => M.gap a ≠ 0),
          run.distribution 0 ω a ∂M.measure) * (m : ℝ) := by
      rw [div_lt_iff₀ hK] at hX
      linarith
    have hYlt : 2 * ((16 * Real.sqrt c / Real.sqrt (c - 1)) *
        ∑ j, (M.scale j / Real.sqrt (M.delta j)) *
          Real.sqrt ((M.levelNodes j).card : ℝ)) <
        (M.gap a₀ * ∫ ω, ∑ a ∈ Finset.univ.filter (fun a => M.gap a ≠ 0),
          run.distribution 0 ω a ∂M.measure) * Real.sqrt (m : ℝ) := by
      have hYs : (2 * ((16 * Real.sqrt c / Real.sqrt (c - 1)) *
          ∑ j, (M.scale j / Real.sqrt (M.delta j)) *
            Real.sqrt ((M.levelNodes j).card : ℝ)) /
        (M.gap a₀ * ∫ ω, ∑ a ∈ Finset.univ.filter (fun a => M.gap a ≠ 0),
          run.distribution 0 ω a ∂M.measure)) <
          Real.sqrt (m : ℝ) := by
        have hnn : 0 ≤ 2 * ((16 * Real.sqrt c / Real.sqrt (c - 1)) *
            ∑ j, (M.scale j / Real.sqrt (M.delta j)) *
              Real.sqrt ((M.levelNodes j).card : ℝ)) /
          (M.gap a₀ * ∫ ω, ∑ a ∈ Finset.univ.filter (fun a => M.gap a ≠ 0),
            run.distribution 0 ω a ∂M.measure) :=
          div_nonneg (by linarith) hK.le
        nlinarith [hY, Real.sq_sqrt hmpos.le, Real.sqrt_nonneg (m : ℝ)]
      rw [div_lt_iff₀ hK] at hYs
      linarith
    have hfinal := hchain m hmN
    nlinarith [hfinal, hsqrtm, hsqrtsq, hCadv, hA]
  have hzero_mass : ∀ (t : ℕ), ∀ᵐ ω ∂M.measure,
      ∀ a ∈ Finset.univ.filter (fun a => M.gap a ≠ 0), run.distribution t ω a = 0 := by
    intro t
    have hae0 := (MeasureTheory.integral_eq_zero_iff_of_nonneg
      hmassnonneg hmassint).1 hmu0
    filter_upwards [hae0] with ω hω
    intro a ha
    have hsum0 : (∑ b ∈ Finset.univ.filter (fun a => M.gap a ≠ 0),
        run.distribution t ω b) = 0 := by
      rw [hmass_eq t ω]
      exact hω
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun b _ => (hp t ω).1 b)).1 hsum0
    exact this a ha
  have hcm_zero_gap : ∀ (t : ℕ) (a : Action), M.gap a = 0 →
      (fun ω => M.conditionalMeanLoss t ω a) =ᵐ[M.measure]
        fun ω => M.conditionalMeanLoss t ω M.optimalAction := by
    intro t a ha
    have h1 := (conditional_mean_loss_ae M run t a).symm
    have h2 := conditional_mean_loss_ae M run t M.optimalAction
    have h3 : MeasureTheory.condExp (m := M.history t) M.measure
          (fun ω => M.loss t ω a) =ᵐ[M.measure]
        MeasureTheory.condExp (m := M.history t) M.measure
          (fun ω => M.loss t ω M.optimalAction) :=
      MeasureTheory.condExp_congr_ae (hzero t a ha)
    exact (h1.trans h3).trans h2
  have hcm_all : ∀ t : ℕ, ∀ᵐ ω ∂M.measure, ∀ a : Action, M.gap a = 0 →
      M.conditionalMeanLoss t ω a = M.conditionalMeanLoss t ω M.optimalAction := by
    intro t
    rw [MeasureTheory.ae_all_iff]
    intro a
    by_cases ha : M.gap a = 0
    · filter_upwards [hcm_zero_gap t a ha] with ω hω
      exact fun _ => hω
    · filter_upwards with ω
      exact fun h => absurd h ha
  have hround_eq : ∀ t : ℕ,
      (∫ ω, M.loss t ω (M.firstAction t ω) ∂M.measure) =
        ∫ ω, M.conditionalMeanLoss t ω M.optimalAction ∂M.measure := by
    intro t
    rw [first_executed_loss_expectation M run t]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hzero_mass t, hcm_all t] with ω h0 hcm
    calc
      (∑ a, run.distribution t ω a * M.conditionalMeanLoss t ω a) =
          ∑ a, run.distribution t ω a *
            M.conditionalMeanLoss t ω M.optimalAction := by
            apply Finset.sum_congr rfl
            intro a _
            by_cases ha : M.gap a = 0
            · rw [hcm a ha]
            · rw [h0 a (Finset.mem_filter.2 ⟨Finset.mem_univ a, ha⟩), zero_mul, zero_mul]
      _ = M.conditionalMeanLoss t ω M.optimalAction := by
            rw [← Finset.sum_mul, (hp t ω).2, one_mul]
  have hopt_le : ∀ t : ℕ,
      (∫ ω, M.conditionalMeanLoss t ω M.optimalAction ∂M.measure) ≤
        ∫ ω, M.loss t ω (M.bestAction T) ∂M.measure := by
    intro t
    have hbest_int :
        (∫ ω, M.loss t ω (M.bestAction T) ∂M.measure) =
          ∫ ω, M.conditionalMeanLoss t ω (M.bestAction T) ∂M.measure := by
      simpa using M.conditionalMeanLoss_spec t (M.bestAction T) Set.univ MeasurableSet.univ
    rw [hbest_int]
    apply MeasureTheory.integral_mono_ae
      (M.conditionalMeanLoss_integrable t M.optimalAction)
      (M.conditionalMeanLoss_integrable t (M.bestAction T))
    filter_upwards [hgapcond t (M.bestAction T)] with ω hω
    have hgn := M.gap_nonnegative (M.bestAction T)
    linarith
  have hLHS : first_action_regret M T ≤ 0 := by
    unfold first_action_regret
    have hfirstsum :
        (∫ ω, ∑ t ∈ Finset.range T, M.loss t ω (M.firstAction t ω) ∂M.measure) =
          ∑ t ∈ Finset.range T, ∫ ω, M.loss t ω (M.firstAction t ω) ∂M.measure :=
      MeasureTheory.integral_finsetSum (μ := M.measure) (Finset.range T)
        (fun t _ => M.first_executed_loss_integrable t)
    have hbestsum :
        (∫ ω, ∑ t ∈ Finset.range T, M.loss t ω (M.bestAction T) ∂M.measure) =
          ∑ t ∈ Finset.range T, ∫ ω, M.loss t ω (M.bestAction T) ∂M.measure :=
      MeasureTheory.integral_finsetSum (μ := M.measure) (Finset.range T)
        (fun t _ => M.loss_integrable t (M.bestAction T))
    rw [hfirstsum, hbestsum, sub_nonpos]
    apply Finset.sum_le_sum
    intro t _
    rw [hround_eq t]
    exact hopt_le t
  have hDnonneg : 0 ≤ ∫ ω, ∑ t ∈ Finset.range T, ∑ a,
      run.distribution t ω a * M.gap a ∂M.measure :=
    MeasureTheory.integral_nonneg (fun ω =>
      Finset.sum_nonneg fun t _ =>
        Finset.sum_nonneg fun a _ => mul_nonneg ((hp t ω).1 a) (M.gap_nonnegative a))
  have hlog : 0 ≤ Real.log (Real.exp 1 * T) := by
    apply Real.log_nonneg
    have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    nlinarith
  have hKnonneg : 0 ≤ stochastic_effective_action_number M := by
    unfold stochastic_effective_action_number
    positivity
  have hcoefnonneg : 0 ≤ 32 * c / (c - 1) :=
    div_nonneg (by linarith) (by linarith)
  rw [← estimated_regret_representation M run T]
  have hlast : 0 ≤ (32 * c / (c - 1)) * stochastic_effective_action_number M *
      Real.log (Real.exp 1 * T) :=
    mul_nonneg (mul_nonneg hcoefnonneg hKnonneg) hlog
  have h6c : 0 ≤ 6 * c * ∑ j, (M.scale j / M.delta j) *
      Real.sqrt ((M.levelNodes j).card : ℝ) := by
    apply mul_nonneg (by linarith) hA
  linarith

@[blueprint "lem:sparse-nested-tsallis-stochastic-objective-gap"
  (statement := /-- Let $M$ be a hierarchical two-point bandit, let $\rho$ be a two-point FTRL run on $M$, let $c\geq2$, and let $T\geq1$. Suppose that the regularizer of $\rho$ is $\Psi_t^{(c)}$ at every positive time and every probability vector, that its level-$j$ shift is $\sigma_j$, and that $M$ satisfies \cref{def:generalized-stochastic-condition}. If $q_T$ is concentrated at the expected-loss-minimizing action $a_T^*$, then
  \[
  \mathbb E\!\left[\sum_{t<T}\langle z_t,p_t-q_T\rangle\right]
  \leq \frac12 R_T^{(1)}+\frac12 B_T^{\mathrm{sto}}(c),
  \]
  where $R_T^{(1)}$ and $B_T^{\mathrm{sto}}(c)$ are given by \cref{def:first-action-regret,def:generic-stochastic-bound}. -/)
  (proof := /-- Write $a^*$ for the distinguished action in \cref{def:generalized-stochastic-condition}, and put
  \[
  D_T=\sum_{t<T}\mathbb E\sum_{a\in\mathcal A}p_t(a)\Delta(a),
  \]
  while $q_T$ is concentrated at $a_T^*$. Integrating the conditional excess-loss inequality and summing over $t$ gives
  \[
  \mathbb E\sum_{t<T}\bigl(y_t(A_{t,1})-y_t(a^*)\bigr)\geq D_T.
  \tag{1}
  \]
  Since all gaps are nonnegative and $\Delta(a^*)=0$, the same conditional inequality shows that $a^*$ minimizes expected cumulative loss. The defining minimality of $a_T^*$ gives the reverse comparison, so the two actions have equal expected cumulative loss. Hence (1) and \cref{def:first-action-regret} imply $D_T\leq R_T^{(1)}$.

  Apply \cref{lem:multibaseline-zero-gap-stability}. This bounds the expected estimated-loss pairing by $D_T/2$, the initial regularizer contribution, and the reciprocal positive-node-gap contribution. Its treatment of zero-gap subtrees uses the explicit blockwise stability field in \cref{def:two-point-ftrl-run}, rather than inferring cancellation of distinct block potentials from simplex normalization. Substitute $D_T\leq R_T^{(1)}$ and combine the remaining two terms as one half of \cref{def:generic-stochastic-bound}. -/)
  (title := /-- Comparator-aware stochastic nested-Tsallis objective-gap estimate -/)
  (latexEnv := "lemma")]
lemma sparse_nested_tsallis_stochastic_objective_gap
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M)
    (c : ℝ) (T : ℕ) (hc : 2 ≤ c) (hT : 1 ≤ T)
    (hregularizer :
      ∀ t x, 1 ≤ t → probability_vector x →
        run.regularizer t x = generic_nested_tsallis_regularizer M c t x)
    (hshift : ∀ j, run.shift j = M.scale j)
    (hstochastic : generalized_stochastic_condition M) :
    (∫ ω, ∑ t ∈ Finset.range T, ∑ a,
        run.estimatedLoss t ω a *
          (run.distribution t ω a - if a = M.bestAction T then 1 else 0)
      ∂M.measure) ≤
      first_action_regret M T / 2 + generic_stochastic_bound M c T / 2 := by
  classical
  letI := M.probability_measure
  obtain ⟨hgapcond, hoptgap, hzero⟩ := hstochastic
  have hmulti := multibaseline_zero_gap_stability M run c T hc hT hregularizer hshift
    ⟨hgapcond, hoptgap, hzero⟩
  have hint_gap : ∀ t, MeasureTheory.Integrable
      (fun ω => ∑ a, run.distribution t ω a * M.gap a) M.measure := by
    intro t
    apply MeasureTheory.integrable_finsetSum Finset.univ
    intro a _
    apply (MeasureTheory.integrable_const (M.gap a)).bdd_mul
      (((run.distribution_measurable t a).mono (M.history.le t)
        le_rfl).stronglyMeasurable.aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun ω => by
      have ha' := mem_Icc_of_mem_stdSimplex (run.distribution_mem t ω) a
      rw [Real.norm_eq_abs, abs_of_nonneg ha'.1]
      exact ha'.2)
  have hpmean_int : ∀ t, MeasureTheory.Integrable
      (fun ω => ∑ a, run.distribution t ω a * M.conditionalMeanLoss t ω a) M.measure := by
    intro t
    apply MeasureTheory.integrable_finsetSum Finset.univ
    intro a _
    apply (M.conditionalMeanLoss_integrable t a).bdd_mul
      (((run.distribution_measurable t a).mono (M.history.le t)
        le_rfl).stronglyMeasurable.aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun ω => by
      have ha' := mem_Icc_of_mem_stdSimplex (run.distribution_mem t ω) a
      rw [Real.norm_eq_abs, abs_of_nonneg ha'.1]
      exact ha'.2)
  have hround : ∀ t,
      (∫ ω, ∑ a, run.distribution t ω a * M.gap a ∂M.measure) ≤
        (∫ ω, M.loss t ω (M.firstAction t ω) ∂M.measure) -
          ∫ ω, M.loss t ω M.optimalAction ∂M.measure := by
    intro t
    have hcmp := M.conditionalMeanLoss_integrable t M.optimalAction
    have hall : ∀ᵐ ω ∂M.measure, ∀ a : Action,
        M.gap a ≤ M.conditionalMeanLoss t ω a -
          M.conditionalMeanLoss t ω M.optimalAction := by
      rw [MeasureTheory.ae_all_iff]
      intro a
      exact hgapcond t a
    have hae : (fun ω => ∑ a, run.distribution t ω a * M.gap a) ≤ᵐ[M.measure]
        fun ω => (∑ a, run.distribution t ω a * M.conditionalMeanLoss t ω a) -
          M.conditionalMeanLoss t ω M.optimalAction := by
      filter_upwards [hall] with ω hω
      have hp := run.distribution_mem t ω
      change (∀ a, 0 ≤ run.distribution t ω a) ∧
        ∑ a, run.distribution t ω a = 1 at hp
      calc
        (∑ a, run.distribution t ω a * M.gap a) ≤
            ∑ a, run.distribution t ω a *
              (M.conditionalMeanLoss t ω a -
                M.conditionalMeanLoss t ω M.optimalAction) := by
              apply Finset.sum_le_sum
              intro a _
              exact mul_le_mul_of_nonneg_left (hω a) (hp.1 a)
        _ = (∑ a, run.distribution t ω a * M.conditionalMeanLoss t ω a) -
              (∑ a, run.distribution t ω a) *
                M.conditionalMeanLoss t ω M.optimalAction := by
              rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl (fun a _ => by ring)
        _ = (∑ a, run.distribution t ω a * M.conditionalMeanLoss t ω a) -
              M.conditionalMeanLoss t ω M.optimalAction := by
              rw [hp.2, one_mul]
    have hmono := MeasureTheory.integral_mono_ae (hint_gap t)
      ((hpmean_int t).sub hcmp) hae
    have hopt_int :
        (∫ ω, M.loss t ω M.optimalAction ∂M.measure) =
          ∫ ω, M.conditionalMeanLoss t ω M.optimalAction ∂M.measure := by
      simpa using M.conditionalMeanLoss_spec t M.optimalAction Set.univ MeasurableSet.univ
    rw [hopt_int, first_executed_loss_expectation M run t,
      ← MeasureTheory.integral_sub (hpmean_int t) hcmp]
    exact hmono
  have hDsum :
      (∫ ω, ∑ t ∈ Finset.range T, ∑ a,
          run.distribution t ω a * M.gap a ∂M.measure) =
        ∑ t ∈ Finset.range T,
          ∫ ω, ∑ a, run.distribution t ω a * M.gap a ∂M.measure :=
    MeasureTheory.integral_finsetSum (μ := M.measure) (Finset.range T)
      (fun t _ => hint_gap t)
  have hfirstsum :
      (∫ ω, ∑ t ∈ Finset.range T, M.loss t ω (M.firstAction t ω) ∂M.measure) =
        ∑ t ∈ Finset.range T, ∫ ω, M.loss t ω (M.firstAction t ω) ∂M.measure :=
    MeasureTheory.integral_finsetSum (μ := M.measure) (Finset.range T)
      (fun t _ => M.first_executed_loss_integrable t)
  have hoptsum :
      (∫ ω, ∑ t ∈ Finset.range T, M.loss t ω M.optimalAction ∂M.measure) =
        ∑ t ∈ Finset.range T, ∫ ω, M.loss t ω M.optimalAction ∂M.measure :=
    MeasureTheory.integral_finsetSum (μ := M.measure) (Finset.range T)
      (fun t _ => M.loss_integrable t M.optimalAction)
  have hsumle :
      (∑ t ∈ Finset.range T, ∫ ω, ∑ a,
          run.distribution t ω a * M.gap a ∂M.measure) ≤
        (∑ t ∈ Finset.range T, ∫ ω, M.loss t ω (M.firstAction t ω) ∂M.measure) -
          ∑ t ∈ Finset.range T, ∫ ω, M.loss t ω M.optimalAction ∂M.measure := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun t _ => hround t)
  have hbest := M.bestAction_minimizes T M.optimalAction
  have hD : (∫ ω, ∑ t ∈ Finset.range T, ∑ a,
      run.distribution t ω a * M.gap a ∂M.measure) ≤ first_action_regret M T := by
    unfold first_action_regret
    rw [hDsum]
    rw [hoptsum] at hbest
    rw [hfirstsum]
    linarith
  have harith :
      6 * c * ∑ j, (M.scale j / M.delta j) * Real.sqrt ((M.levelNodes j).card : ℝ) +
          (32 * c / (c - 1)) * stochastic_effective_action_number M *
            Real.log (Real.exp 1 * T) =
        generic_stochastic_bound M c T / 2 := by
    unfold generic_stochastic_bound
    ring
  linarith

@[blueprint "lem:sparse-nested-tsallis-stochastic-bound"
  (statement := /-- Under the hypotheses of \cref{lem:sparse-nested-tsallis-ftrl-estimate}, assume additionally that \cref{def:generalized-stochastic-condition} holds; in particular, the realized loss of every zero-gap action agrees almost surely with that of the distinguished action at every round. Then first-action regret is at most
  \[
  12c\sum_{j\in[L]}\frac{\sigma_j}{\delta_j}\sqrt{|V_j|}
  +\frac{64c}{c-1}
  K_{\mathrm{eff}}^{\mathrm{sto}}(\sigma/\sqrt\delta)\log(eT)
  =B_T^{\mathrm{sto}}(c).
  \] -/)
  (proof := /-- By \cref{lem:estimated-regret-representation}, first-action regret is the expected estimated-loss pairing with the point mass at $a_T^*$. The comparator-aware estimate \cref{lem:sparse-nested-tsallis-stochastic-objective-gap} bounds this pairing by
  \[
  \frac12R_T^{(1)}+\frac12B_T^{\mathrm{sto}}(c).
  \]
  Substituting the representation on the left and subtracting $R_T^{(1)}/2$ from both sides gives $R_T^{(1)}\leq B_T^{\mathrm{sto}}(c)$. -/)
  (title := /-- Stochastic consequence of sparse nested-Tsallis stability -/)
  (latexEnv := "lemma")]
lemma sparse_nested_tsallis_stochastic_bound
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M)
    (c : ℝ) (T : ℕ) (hc : 2 ≤ c) (hT : 1 ≤ T)
    (hregularizer :
      ∀ t x, 1 ≤ t → probability_vector x →
        run.regularizer t x = generic_nested_tsallis_regularizer M c t x)
    (hshift : ∀ j, run.shift j = M.scale j)
    (hstochastic : generalized_stochastic_condition M) :
    first_action_regret M T ≤ generic_stochastic_bound M c T := by
  have h := sparse_nested_tsallis_stochastic_objective_gap M run c T hc hT hregularizer
    hshift hstochastic
  rw [← estimated_regret_representation M run T] at h
  linarith

@[blueprint "lem:generic-multipoint-feedback-bound"
  (statement := /-- Let $c\geq2$, let $T\geq1$, and let $\rho$ be a two-point FTRL run on $M$. Assume that, for every $t\geq1$ and $x\in\Delta_{\mathcal A}$, its regularizer at $x$ is $\Psi_t^{(c)}(x)$, and that its shift at level $j$ is $\sigma_j$. Then
  \[
  R_T^{(1)}\leq B_T(c).
  \]
  If \cref{def:generalized-stochastic-condition} holds, so that the distinguished action has zero gap and every zero-gap action has the same realized loss as that action almost surely at every round, then also $R_T^{(1)}\leq B_T^{\mathrm{sto}}(c)$. -/)
  (proof := /-- Under the regularizer and shift hypotheses, \cref{lem:sparse-nested-tsallis-adversarial-bound} bounds $R_T^{(1)}$ by \cref{def:generic-adversarial-bound}. If \cref{def:generalized-stochastic-condition} holds, \cref{lem:sparse-nested-tsallis-stochastic-bound} bounds the same regret by \cref{def:generic-stochastic-bound}. These are the two asserted conclusions. -/)
  (title := /-- Generic multi-point feedback estimate -/)
  (latexEnv := "lemma")]
lemma generic_multipoint_feedback_bound
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M)
    (c : ℝ) (T : ℕ) (hc : 2 ≤ c) (hT : 1 ≤ T)
    (hregularizer :
      ∀ t x, 1 ≤ t → probability_vector x →
        run.regularizer t x = generic_nested_tsallis_regularizer M c t x)
    (hshift : ∀ j, run.shift j = M.scale j) :
    first_action_regret M T ≤ generic_adversarial_bound M c T ∧
      (generalized_stochastic_condition M →
        first_action_regret M T ≤ generic_stochastic_bound M c T) := by
  exact ⟨sparse_nested_tsallis_adversarial_bound M run c T hc hT hregularizer hshift,
    fun hstochastic =>
      sparse_nested_tsallis_stochastic_bound M run c T hc hT hregularizer hshift
        hstochastic⟩

@[blueprint "lem:two-point-parameter-specialization"
  (statement := /-- Let $T\geq1$. If, for every $t\geq1$ and $x\in\Delta_{\mathcal A}$, the run uses the stated two-point regularizer at $x$, and if its shifts satisfy $b_j=\sigma_j$, then
  \[
  R_T^{(1)}\leq 18\sum_j\frac{\sigma_j}{\delta_j}\sqrt{|V_j|}
  +8\sqrt6\left(\sum_j\frac{\sigma_j}{\sqrt{\delta_j}}\sqrt{|V_j|}\right)\sqrt T.
  \]
  Under \cref{def:generalized-stochastic-condition}, including its requirement that every zero-gap action have the same realized loss as the distinguished action almost surely at every round, the run also satisfies the explicit stochastic bound with constants $36$ and $96$. -/)
  (proof := /-- Apply \cref{lem:generic-multipoint-feedback-bound} with $c=3$. At every positive time and simplex vector, the coefficient of the regularizer becomes $4\sqrt3/\sqrt2=2\sqrt6$, and its cutoff becomes $3(3-1)/\delta_j=6/\delta_j$, so the regularizer hypothesis is precisely \cref{def:two-point-nested-tsallis-regularizer}. The adversarial constants become $6c=18$ and $16\sqrt c/\sqrt{c-1}=8\sqrt6$; the stochastic constants become $12c=36$ and $64c/(c-1)=96$. These substitutions yield \cref{def:two-point-adversarial-raw-bound, def:two-point-stochastic-raw-bound}. This is the specialization asserted but not written out in the supplied proof of the selected result. -/)
  (title := /-- Specialization to two-point feedback -/)
  (latexEnv := "lemma")]
lemma two_point_parameter_specialization
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M)
    (T : ℕ) (hT : 1 ≤ T)
    (hregularizer :
      ∀ t x, 1 ≤ t → probability_vector x →
        run.regularizer t x = two_point_nested_tsallis_regularizer M t x)
    (hshift : ∀ j, run.shift j = M.scale j) :
    first_action_regret M T ≤ two_point_adversarial_raw_bound M T ∧
      (generalized_stochastic_condition M →
        first_action_regret M T ≤ two_point_stochastic_raw_bound M T) := by
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2ne : Real.sqrt 2 ≠ 0 := by positivity
  have h6 : Real.sqrt 6 = Real.sqrt 3 * Real.sqrt 2 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  have hcoef4 : 4 * Real.sqrt 3 / Real.sqrt (3 - 1) = 2 * Real.sqrt 6 := by
    rw [show (3:ℝ) - 1 = 2 by norm_num, h6, div_eq_iff h2ne]
    linear_combination (-2 * Real.sqrt 3) * h22
  have hcoef16 : 16 * Real.sqrt 3 / Real.sqrt (3 - 1) = 8 * Real.sqrt 6 := by
    rw [show (3:ℝ) - 1 = 2 by norm_num, h6, div_eq_iff h2ne]
    linear_combination (-8 * Real.sqrt 3) * h22
  have hreg : ∀ (t : ℕ) (x : Action → ℝ),
      generic_nested_tsallis_regularizer M 3 t x =
        two_point_nested_tsallis_regularizer M t x := by
    intro t x
    unfold generic_nested_tsallis_regularizer two_point_nested_tsallis_regularizer
    rw [hcoef4, show (3:ℝ) * (3 - 1) = 6 by norm_num]
  obtain ⟨hadv, hsto⟩ :=
    generic_multipoint_feedback_bound M run 3 T (by norm_num) hT
      (fun t x ht hx => (hregularizer t x ht hx).trans (hreg t x).symm) hshift
  have hsumT :
      (∑ j, (M.scale j / Real.sqrt (M.delta j)) *
          Real.sqrt (((M.levelNodes j).card : ℝ) * T)) =
        (∑ j, (M.scale j / Real.sqrt (M.delta j)) *
          Real.sqrt ((M.levelNodes j).card : ℝ)) * Real.sqrt T := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Real.sqrt_mul (Nat.cast_nonneg _)]
    ring
  have hadveq : generic_adversarial_bound M 3 T = two_point_adversarial_raw_bound M T := by
    unfold generic_adversarial_bound two_point_adversarial_raw_bound
    rw [hcoef16, hsumT]
    norm_num
    ring
  have hstoeq : generic_stochastic_bound M 3 T = two_point_stochastic_raw_bound M T := by
    unfold generic_stochastic_bound two_point_stochastic_raw_bound
    norm_num
  exact ⟨hadveq ▸ hadv, fun hs => hstoeq ▸ hsto hs⟩

@[blueprint "lem:two-point-raw-regret-bounds"
  (statement := /-- Let $T\geq1$. Suppose that the run uses the two-point regularizer at every positive time on every simplex vector and has shifts $b_j=\sigma_j$. Then the explicit adversarial bound obtained for the first executed action also holds for two-point regret. If \cref{def:generalized-stochastic-condition} holds, including almost-sure equality of realized losses between every zero-gap action and the distinguished action at every round, then the corresponding explicit stochastic bound also holds for two-point regret. -/)
  (proof := /-- By \cref{lem:two-point-regret-reduction}, two-point regret equals first-action regret. Substitute this equality into the two conclusions of \cref{lem:two-point-parameter-specialization}. -/)
  (title := /-- Explicit bounds for two-point regret -/)
  (latexEnv := "lemma")]
lemma two_point_raw_regret_bounds
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M)
    (T : ℕ) (hT : 1 ≤ T)
    (hregularizer :
      ∀ t x, 1 ≤ t → probability_vector x →
        run.regularizer t x = two_point_nested_tsallis_regularizer M t x)
    (hshift : ∀ j, run.shift j = M.scale j) :
    two_point_regret M T ≤ two_point_adversarial_raw_bound M T ∧
      (generalized_stochastic_condition M →
        two_point_regret M T ≤ two_point_stochastic_raw_bound M T) := by
  have hred := two_point_regret_reduction M run T
  obtain ⟨h1, h2⟩ := two_point_parameter_specialization M run T hT hregularizer hshift
  exact ⟨by rw [hred]; exact h1, fun hs => by rw [hred]; exact h2 hs⟩

@[blueprint "lem:effective-complexity-rewrites"
  (statement := /-- For every hierarchical two-point bandit $M$ and every horizon
  $T\in\mathbb N$, the explicit two-point adversarial raw bound of
  \cref{def:two-point-adversarial-raw-bound} equals
  \[
  18\sqrt{K_{\mathrm{eff}}(\sigma/\delta)}
  +8\sqrt6\sqrt{K_{\mathrm{eff}}(\sigma/\sqrt\delta)T},
  \]
  and the explicit two-point stochastic raw bound of
  \cref{def:two-point-stochastic-raw-bound} equals
  \[
  36\sqrt{K_{\mathrm{eff}}(\sigma/\delta)}
  +96K_{\mathrm{eff}}^{\mathrm{sto}}(\sigma/\sqrt\delta)\log(eT).
  \] -/)
  (proof := /-- Let
  \[
  A=\sum_j\frac{\sigma_j}{\delta_j}\sqrt{|V_j|},\qquad
  B=\sum_j\frac{\sigma_j}{\sqrt{\delta_j}}\sqrt{|V_j|}.
  \]
  The model axioms in \cref{def:hierarchical-two-point-bandit} give
  $\sigma_j\geq0$ and $\delta_j>0$ for every $j$. Since square roots are
  nonnegative, every summand defining $A$ and $B$ is nonnegative; hence
  $A,B\geq0$. By \cref{def:effective-action-number},
  $\sqrt{K_{\mathrm{eff}}(\sigma/\delta)}=\sqrt{A^2}=A$ and
  $\sqrt{K_{\mathrm{eff}}(\sigma/\sqrt\delta)}=\sqrt{B^2}=B$.
  Moreover, $B^2\geq0$, so
  $\sqrt{B^2T}=\sqrt{B^2}\sqrt T=B\sqrt T$. Unfolding
  \cref{def:two-point-adversarial-raw-bound, def:two-point-stochastic-raw-bound}
  and substituting these identities proves the two asserted equalities; the
  stochastic-complexity and logarithmic terms are unchanged. -/)
  (title := /-- Conversion to effective-complexity notation -/)
  (latexEnv := "lemma")]
lemma effective_complexity_rewrites
    (M : hierarchical_two_point_bandit Action Node Ω) (T : ℕ) :
    two_point_adversarial_raw_bound M T =
        18 * Real.sqrt (effective_action_number M M.delta) +
          8 * Real.sqrt 6 *
            Real.sqrt
              (effective_action_number M (fun j => Real.sqrt (M.delta j)) * T) ∧
      two_point_stochastic_raw_bound M T =
        36 * Real.sqrt (effective_action_number M M.delta) +
          96 * stochastic_effective_action_number M * Real.log (Real.exp 1 * T) := by
  have hdelta :
      0 ≤ ∑ j, (M.scale j / M.delta j) * Real.sqrt ((M.levelNodes j).card : ℝ) :=
    Finset.sum_nonneg fun j _ =>
      mul_nonneg
        (div_nonneg (M.scale_nonnegative j) (le_of_lt (M.delta_positive j)))
        (Real.sqrt_nonneg _)
  have hsqrtDelta :
      0 ≤ ∑ j, (M.scale j / Real.sqrt (M.delta j)) *
        Real.sqrt ((M.levelNodes j).card : ℝ) :=
    Finset.sum_nonneg fun j _ =>
      mul_nonneg
        (div_nonneg (M.scale_nonnegative j) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
  constructor <;>
    simp [two_point_adversarial_raw_bound, two_point_stochastic_raw_bound,
      effective_action_number, Real.sqrt_mul, Real.sqrt_sq_eq_abs,
      abs_of_nonneg hdelta, abs_of_nonneg hsqrtDelta] <;>
    ring

@[blueprint "thm:two-point-feedback"
  (statement := /-- Let $M$ be a hierarchical two-point bandit satisfying the tree smoothness hypothesis and such that, conditionally on the pre-round history, each loss vector is independent of the learner's randomization at that round and every later round. Let the learner run two-point FTRL whose regularizer, for every $t\geq1$ and $x\in\Delta_{\mathcal A}$, is
  \[
  \Psi_t(x)=2\sqrt6\sum_{j\in[L]}\frac{\sigma_j}{\sqrt{\delta_j}}
  \sqrt{\max\{t,6/\delta_j\}}
  \sum_{v\in V_j}\bigl(x[v]-\sqrt{x[v]}\bigr),
  \qquad b_j=\sigma_j.
  \]
  Then, for every $T\geq1$,
  \[
  R_T^{(2)}\leq18\sqrt{K_{\mathrm{eff}}(\sigma/\delta)}
  +8\sqrt6\sqrt{K_{\mathrm{eff}}(\sigma/\sqrt\delta)T}.
  \]
  If \cref{def:generalized-stochastic-condition} holds, so that the distinguished action has zero gap and every zero-gap action has the same realized loss as that action almost surely at every round, then
  \[
  R_T^{(2)}\leq36\sqrt{K_{\mathrm{eff}}(\sigma/\delta)}
  +96K_{\mathrm{eff}}^{\mathrm{sto}}(\sigma/\sqrt\delta)\log(eT).
  \] -/)
  (proof := /-- The explicit estimates are furnished by \cref{lem:two-point-raw-regret-bounds}. Replace their right-hand sides by the equal expressions in \cref{lem:effective-complexity-rewrites}. The first component gives the unconditional estimate. Applying the second component under \cref{def:generalized-stochastic-condition} gives the stochastic estimate. -/)
  (title := /-- Best-of-both-worlds regret bound for two-point feedback -/)
  (latexEnv := "theorem")]
theorem two_point_feedback
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M)
    (T : ℕ) (hT : 1 ≤ T)
    (hregularizer :
      ∀ t x, 1 ≤ t → probability_vector x →
        run.regularizer t x = two_point_nested_tsallis_regularizer M t x)
    (hshift : ∀ j, run.shift j = M.scale j) :
    two_point_regret M T ≤
        18 * Real.sqrt (effective_action_number M M.delta) +
          8 * Real.sqrt 6 *
            Real.sqrt
              (effective_action_number M (fun j => Real.sqrt (M.delta j)) * T) ∧
      (generalized_stochastic_condition M →
        two_point_regret M T ≤
          36 * Real.sqrt (effective_action_number M M.delta) +
            96 * stochastic_effective_action_number M * Real.log (Real.exp 1 * T)) := by
  obtain ⟨h1, h2⟩ := two_point_raw_regret_bounds M run T hT hregularizer hshift
  obtain ⟨e1, e2⟩ := effective_complexity_rewrites M T
  exact ⟨by rw [← e1]; exact h1, fun hs => by rw [← e2]; exact h2 hs⟩

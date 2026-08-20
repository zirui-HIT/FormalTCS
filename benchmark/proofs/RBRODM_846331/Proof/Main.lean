import Architect
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.NNReal.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Defs

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:imprecise-belief"
  (statement := /-- Let $\mathcal O$ be an observation space.  An imprecise belief on
  $\mathcal O$ is a nonempty, closed, convex set $B$ of functions
  $p : \mathcal O \to \mathbb R$ such that every $p\in B$ is nonnegative,
  summable, and has total mass one. -/)
  (title := /-- Imprecise beliefs -/)
  (latexEnv := "definition")]
structure imprecise_belief (Observation : Type*) where
  carrier : Set (Observation → ℝ)
  nonempty : carrier.Nonempty
  mass_nonnegative : ∀ p ∈ carrier, ∀ o, 0 ≤ p o
  mass_summable : ∀ p ∈ carrier, Summable p
  total_mass_one : ∀ p ∈ carrier, ∑' o, p o = 1
  isClosed : IsClosed carrier
  convex : Convex ℝ carrier

@[blueprint "def:robust-model"
  (statement := /-- For an action space $\mathcal A$ and an observation space
  $\mathcal O$, a robust model assigns to every action $a\in\mathcal A$ an
  imprecise belief on $\mathcal O$. -/)
  (title := /-- Robust models -/)
  (latexEnv := "definition")]
abbrev robust_model (Action Observation : Type*) :=
  Action → imprecise_belief Observation

@[blueprint "def:online-history"
  (statement := /-- A finite online history over $\mathcal A$ and $\mathcal O$ is
  a finite ordered list of action--observation pairs. -/)
  (title := /-- Online histories -/)
  (latexEnv := "definition")]
abbrev online_history (Action Observation : Type*) :=
  List (Action × Observation)

@[blueprint "def:online-estimation-oracle"
  (statement := /-- An online estimation oracle returns, for every round index and
  every finite action--observation history, an estimated robust model. -/)
  (title := /-- Online estimation oracles -/)
  (latexEnv := "definition")]
structure online_estimation_oracle (Action Observation : Type*) where
  estimate : ℕ → online_history Action Observation → robust_model Action Observation

@[blueprint "def:robust-loss"
  (statement := /-- A robust loss $\mathcal L$ assigns a nonnegative real number
  $\mathcal L(\widehat M,M,a)$ to an estimated model $\widehat M$, a comparison
  model $M$, and an action $a$. -/)
  (title := /-- Losses between robust models -/)
  (latexEnv := "definition")]
abbrev robust_loss (Action Observation : Type*) :=
  robust_model Action Observation → robust_model Action Observation → Action → NNReal

@[blueprint "def:probability-mass"
  (statement := /-- A probability mass on a type $X$ is a nonnegative summable
  function $p:X\to\mathbb R$ whose total mass is one. -/)
  (title := /-- Probability masses -/)
  (latexEnv := "definition")]
structure probability_mass (X : Type*) where
  mass : X → ℝ
  nonnegative : ∀ x, 0 ≤ mass x
  summable : Summable mass
  total_mass_one : ∑' x, mass x = 1

@[blueprint "def:subprobability-mass"
  (statement := /-- A subprobability mass on a type $X$ is a nonnegative
  summable function $\mu:X\to\mathbb R$ whose total mass is at most one. -/)
  (title := /-- Subprobability masses -/)
  (latexEnv := "definition")]
structure subprobability_mass (X : Type*) where
  mass : X → ℝ
  nonnegative : ∀ x, 0 ≤ mass x
  summable : Summable mass
  total_mass_le_one : ∑' x, mass x ≤ 1

@[blueprint "def:robust-online-decision-framework"
  (statement := /-- A robust online decision framework consists of a reward
  $r : \mathcal A\times\mathcal O\to[0,1]$ and a hypothesis class
  $\mathcal M\subseteq\mathcal A\to\Box\mathcal O$.  The action space is
  required to support at least one probability mass.  Regret, the fuzzy
  decision--estimation coefficient, E2D, and the estimator-bound predicates
  are derived from these data below rather than supplied as unconstrained
  fields. -/)
  (title := /-- Robust online decision frameworks -/)
  (latexEnv := "definition")]
structure robust_online_decision_framework (Action Observation : Type*) where
  reward : Action → Observation → ℝ
  reward_mem_unit : ∀ a o, reward a o ∈ Set.Icc (0 : ℝ) 1
  hypothesisClass : Set (robust_model Action Observation)
  action_distribution_nonempty : Nonempty (probability_mass Action)

@[blueprint "def:online-policy"
  (statement := /-- An online policy assigns an action probability mass to
  every finite action--observation history. -/)
  (title := /-- Online policies -/)
  (latexEnv := "definition")]
abbrev online_policy (Action Observation : Type*) :=
  online_history Action Observation → probability_mass Action

@[blueprint "def:online-environment"
  (statement := /-- An online environment assigns an observation probability
  mass to every finite history and proposed action. -/)
  (title := /-- Online environments -/)
  (latexEnv := "definition")]
abbrev online_environment (Action Observation : Type*) :=
  online_history Action Observation → Action → probability_mass Observation

@[blueprint "def:environment-consistent"
  (statement := /-- An online environment $\theta$ is consistent with a robust
  model $M$ if, after every history and for every action, the observation law
  selected by $\theta$ belongs to the imprecise belief $M(a)$. -/)
  (title := /-- Consistency of environments and robust models -/)
  (latexEnv := "definition")]
def environment_consistent
    {Action Observation : Type*}
    (environment : online_environment Action Observation)
    (model : robust_model Action Observation) : Prop :=
  ∀ history action, (environment history action).mass ∈ (model action).carrier

@[blueprint "def:robust-action-value"
  (statement := /-- For a robust model $M$ and action $a$, define
  $f^M(a)$ as the infimum, over all observation laws $p\in M(a)$, of the
  expected reward $\sum_o p(o)r(a,o)$. -/)
  (title := /-- Worst-case action values -/)
  (latexEnv := "definition")]
noncomputable def robust_action_value
    {Action Observation : Type*}
    (framework : robust_online_decision_framework Action Observation)
    (model : robust_model Action Observation) (action : Action) : ℝ :=
  sInf (Set.range fun p : {p // p ∈ (model action).carrier} =>
    ∑' observation, p.1 observation * framework.reward action observation)

@[blueprint "def:robust-optimal-value"
  (statement := /-- The robust optimal value $\max(f^M)$ is the supremum of
  the worst-case action values $f^M(a)$ over all actions $a$. -/)
  (title := /-- Robust optimal values -/)
  (latexEnv := "definition")]
noncomputable def robust_optimal_value
    {Action Observation : Type*}
    (framework : robust_online_decision_framework Action Observation)
    (model : robust_model Action Observation) : ℝ :=
  sSup (Set.range fun action => robust_action_value framework model action)

@[blueprint "def:fuzzy-decision-objective"
  (statement := /-- Fix a reference model $\overline M$, a loss
  $\mathcal L$, a radius $\varepsilon$, a hypothesis class $\mathcal M$, and
  an action law $p$.  The fuzzy decision objective is the supremum, over
  subprobability masses $\mu$ supported on $\mathcal M$ whose mean loss
  $\mathbb E_{M\sim\mu,a\sim p}\mathcal L(\overline M,M,a)$ is at most
  $\varepsilon^2$, of
  $\mathbb E_{M\sim\mu,a\sim p}[\max(f^M)-f^{\overline M}(a)]$. -/)
  (title := /-- The loss-constrained fuzzy decision objective -/)
  (latexEnv := "definition")]
noncomputable def fuzzy_decision_objective
    {Action Observation : Type*}
    (framework : robust_online_decision_framework Action Observation)
    (loss : robust_loss Action Observation) (epsilon : ℝ)
    (reference : robust_model Action Observation)
    (actions : probability_mass Action) : ℝ :=
  sSup {value | ∃ mu : subprobability_mass (robust_model Action Observation),
    (∀ model, 0 < mu.mass model → model ∈ framework.hypothesisClass) ∧
    (∑' model, mu.mass model *
      (∑' action, actions.mass action * (loss reference model action : ℝ))) ≤
        epsilon ^ 2 ∧
    value = ∑' model, mu.mass model *
      (∑' action, actions.mass action *
        (robust_optimal_value framework model -
          robust_action_value framework reference action))}

@[blueprint "def:fuzzy-decision-estimation-coefficient-at"
  (statement := /-- The fuzzy decision--estimation coefficient at a reference
  model $\overline M$ is the infimum of the fuzzy decision objective over all
  action probability masses. -/)
  (title := /-- Fuzzy DEC at a reference model -/)
  (latexEnv := "definition")]
noncomputable def fuzzy_decision_estimation_coefficient_at
    {Action Observation : Type*}
    (framework : robust_online_decision_framework Action Observation)
    (loss : robust_loss Action Observation) (epsilon : ℝ)
    (reference : robust_model Action Observation) : ℝ :=
  sInf (Set.range fun actions =>
    fuzzy_decision_objective framework loss epsilon reference actions)

@[blueprint "def:fuzzy-decision-minimizer"
  (statement := /-- A fuzzy decision minimizer for a framework and loss
  function assigns, to every radius $\varepsilon\in\mathbb R$ and every
  reference model $\overline M$, an action probability mass at which the
  infimum defining
  $\operatorname{dec}^{f,\mathcal L}_{\varepsilon}
    (\mathcal M,\overline M)$ is attained. -/)
  (title := /-- Certified fuzzy decision minimizers -/)
  (latexEnv := "definition")]
structure fuzzy_decision_minimizer
    {Action Observation : Type*}
    (framework : robust_online_decision_framework Action Observation)
    (loss : robust_loss Action Observation) where
  actions : ℝ → robust_model Action Observation → probability_mass Action
  attains : ∀ epsilon reference,
    fuzzy_decision_objective framework loss epsilon reference
        (actions epsilon reference) =
      fuzzy_decision_estimation_coefficient_at framework loss epsilon reference

@[blueprint "def:fuzzy-decision-estimation-coefficient"
  (statement := /-- The worst-case fuzzy decision--estimation coefficient
  $\operatorname{dec}^{f,\mathcal L}_{\varepsilon}(\mathcal M)$ is the
  supremum, over all reference robust models $\overline M$, of the fuzzy
  coefficient at $\overline M$. -/)
  (title := /-- Worst-case fuzzy decision--estimation coefficients -/)
  (latexEnv := "definition")]
noncomputable def fuzzy_decision_estimation_coefficient
    {Action Observation : Type*}
    (framework : robust_online_decision_framework Action Observation)
    (loss : robust_loss Action Observation) (epsilon : ℝ) : ℝ :=
  sSup (Set.range fun reference =>
    fuzzy_decision_estimation_coefficient_at framework loss epsilon reference)

@[blueprint "def:e2d-action-distribution"
  (statement := /-- Fix a framework, a loss $\mathcal L$, and a certified
  fuzzy decision minimizer.  At radius $\varepsilon$ and reference model
  $\overline M$, the E2D action distribution is the action probability mass
  supplied by the certificate; in particular, it attains
  $\operatorname{dec}^{f,\mathcal L}_{\varepsilon}
    (\mathcal M,\overline M)$. -/)
  (title := /-- E2D action distributions -/)
  (latexEnv := "definition")]
noncomputable def e2d_action_distribution
    {Action Observation : Type*}
    (framework : robust_online_decision_framework Action Observation)
    (loss : robust_loss Action Observation)
    (minimizer : fuzzy_decision_minimizer framework loss) (epsilon : ℝ)
    (reference : robust_model Action Observation) :
    probability_mass Action :=
  minimizer.actions epsilon reference

@[blueprint "def:e2d-policy"
  (statement := /-- For a positive horizon $T$, confidence level
  $\delta\in[0,1]$, estimator
  $\widehat M$, loss $\mathcal L$, certified fuzzy decision minimizer, and
  inaccuracy bound $\beta$, the E2D policy uses at every history $h$ the
  certified minimizing action law at $\widehat M_{|h|}(h)$ with the fixed radius
  $\sqrt{\beta(T,\delta)/T}$. -/)
  (title := /-- Estimations-to-decisions policies -/)
  (latexEnv := "definition")]
noncomputable def e2d_policy
    {Action Observation : Type*}
    (framework : robust_online_decision_framework Action Observation)
    (estimator : online_estimation_oracle Action Observation)
    (loss : robust_loss Action Observation)
    (minimizer : fuzzy_decision_minimizer framework loss)
    (beta : ℕ → ℝ → ℝ)
    (T : ℕ) (delta : ℝ) : online_policy Action Observation :=
  fun history =>
    e2d_action_distribution framework loss minimizer
      (Real.sqrt (beta T delta / (T : ℝ)))
      (estimator.estimate history.length history)

@[blueprint "def:trajectory-probability"
  (statement := /-- The probability of a reverse-chronological finite history
  under a policy $\pi$ and environment $\theta$ is the product of the
  successive conditional action and observation probabilities. -/)
  (title := /-- Probabilities of finite online histories -/)
  (latexEnv := "definition")]
def trajectory_probability
    {Action Observation : Type*}
    (policy : online_policy Action Observation)
    (environment : online_environment Action Observation) :
    online_history Action Observation → ℝ
  | [] => 1
  | (action, observation) :: history =>
      trajectory_probability policy environment history *
        (policy history).mass action *
        (environment history action).mass observation

@[blueprint "def:event-probability"
  (statement := /-- The probability of an event $E$ on histories of length
  $T$ is the sum of the trajectory probabilities of precisely those
  length-$T$ histories for which $E$ holds. -/)
  (title := /-- Probabilities of finite-horizon events -/)
  (latexEnv := "definition")]
noncomputable def event_probability
    {Action Observation : Type*}
    (policy : online_policy Action Observation)
    (environment : online_environment Action Observation)
    (T : ℕ) (event : online_history Action Observation → Prop) : ℝ := by
  classical
  exact ∑' history, if history.length = T ∧ event history then
    trajectory_probability policy environment history else 0

@[blueprint "def:expected-cumulative-reward"
  (statement := /-- The expected cumulative reward through round $T$ under a
  policy and environment is the sum, over all length-$T$ histories, of the
  trajectory probability times the sum of the rewards along that history. -/)
  (title := /-- Expected cumulative rewards -/)
  (latexEnv := "definition")]
noncomputable def expected_cumulative_reward
    {Action Observation : Type*}
    (framework : robust_online_decision_framework Action Observation)
    (policy : online_policy Action Observation)
    (environment : online_environment Action Observation) (T : ℕ) : ℝ :=
  ∑' history, if history.length = T then
    trajectory_probability policy environment history *
      (history.map (fun pair => framework.reward pair.1 pair.2)).sum else 0

@[blueprint "def:e2d-regret"
  (statement := /-- Fix a certified fuzzy decision minimizer.  The regret of
  the resulting E2D policy against a robust model $M$ at a positive horizon
  $T$ and confidence level $\delta\in[0,1]$ is the supremum over all
  environments $\theta$ consistent with $M$ of $T\max(f^M)$ minus the
  expected cumulative reward of that policy. -/)
  (title := /-- Regret of estimations to decisions -/)
  (latexEnv := "definition")]
noncomputable def e2d_regret
    {Action Observation : Type*}
    (framework : robust_online_decision_framework Action Observation)
    (estimator : online_estimation_oracle Action Observation)
    (loss : robust_loss Action Observation)
    (minimizer : fuzzy_decision_minimizer framework loss)
    (beta : ℕ → ℝ → ℝ)
    (model : robust_model Action Observation) (T : ℕ) (delta : ℝ) : ℝ :=
  sSup {value | ∃ environment : online_environment Action Observation,
    environment_consistent environment model ∧
    value = (T : ℝ) * robust_optimal_value framework model -
      expected_cumulative_reward framework
        (e2d_policy framework estimator loss minimizer beta T delta)
        environment T}

@[blueprint "def:cumulative-inaccuracy"
  (statement := /-- Along a finite history, the cumulative inaccuracy is the
  sum over preceding histories of the policy expectation of
  $\mathcal L(\widehat M_t,M,a)$. -/)
  (title := /-- Cumulative estimator inaccuracy -/)
  (latexEnv := "definition")]
noncomputable def cumulative_inaccuracy
    {Action Observation : Type*}
    (estimator : online_estimation_oracle Action Observation)
    (loss : robust_loss Action Observation)
    (model : robust_model Action Observation)
    (policy : online_policy Action Observation) :
    online_history Action Observation → ℝ
  | [] => 0
  | _ :: history =>
      cumulative_inaccuracy estimator loss model policy history +
        ∑' action, (policy history).mass action *
          (loss (estimator.estimate history.length history) model action : ℝ)

@[blueprint "def:cumulative-optimism"
  (statement := /-- Along a finite history, the cumulative optimism is the sum
  over preceding histories of the policy expectation of the difference
  between the robust value under the estimated model and the expected reward
  under the environment's current observation law. -/)
  (title := /-- Cumulative estimator optimism -/)
  (latexEnv := "definition")]
noncomputable def cumulative_optimism
    {Action Observation : Type*}
    (framework : robust_online_decision_framework Action Observation)
    (estimator : online_estimation_oracle Action Observation)
    (policy : online_policy Action Observation)
    (environment : online_environment Action Observation) :
    online_history Action Observation → ℝ
  | [] => 0
  | _ :: history =>
      cumulative_optimism framework estimator policy environment history +
        ∑' action, (policy history).mass action *
          (robust_action_value framework
              (estimator.estimate history.length history) action -
            ∑' observation, (environment history action).mass observation *
              framework.reward action observation)

@[blueprint "def:is-inaccuracy-bound"
  (statement := /-- A function $\beta$ is an inaccuracy bound for an estimator
  relative to $\mathcal L$ and $\mathcal M$ if, for every positive horizon
  $T$, every $\delta\in[0,1]$, every
  $M\in\mathcal M$, and every environment consistent with $M$, the resulting
  E2D trajectory determined by a certified fuzzy decision minimizer has
  cumulative inaccuracy at most $\beta(T,\delta)$ with probability at least
  $1-\delta$. -/)
  (title := /-- Inaccuracy bounds -/)
  (latexEnv := "definition")]
noncomputable def is_inaccuracy_bound
    {Action Observation : Type*}
    (framework : robust_online_decision_framework Action Observation)
    (estimator : online_estimation_oracle Action Observation)
    (loss : robust_loss Action Observation)
    (minimizer : fuzzy_decision_minimizer framework loss)
    (beta : ℕ → ℝ → ℝ) : Prop :=
  ∀ (T : ℕ) (hT : 0 < T) (delta : ℝ)
      (hdelta : delta ∈ Set.Icc (0 : ℝ) 1),
      ∀ model, model ∈ framework.hypothesisClass →
        ∀ environment, environment_consistent environment model →
          1 - delta ≤ event_probability
            (e2d_policy framework estimator loss minimizer beta T delta)
            environment T
            (fun history =>
              cumulative_inaccuracy estimator loss model
                (e2d_policy framework estimator loss minimizer beta T delta)
                history ≤ beta T delta)

@[blueprint "def:is-optimism-bound"
  (statement := /-- A function $\alpha$ is an optimism bound for an estimator
  relative to $\mathcal L$, $\mathcal M$, and its E2D inaccuracy parameter
  $\beta$ if, for every positive horizon $T$ and every confidence level
  $\delta\in[0,1]$, the value $\alpha(T,\delta)$ is nonnegative and, for every
  model and every consistent environment, the E2D trajectory determined by a
  certified fuzzy decision minimizer has cumulative optimism at most
  $\alpha(T,\delta)$ with probability at least $1-\delta$. -/)
  (title := /-- Optimism bounds -/)
  (latexEnv := "definition")]
noncomputable def is_optimism_bound
    {Action Observation : Type*}
    (framework : robust_online_decision_framework Action Observation)
    (estimator : online_estimation_oracle Action Observation)
    (loss : robust_loss Action Observation)
    (minimizer : fuzzy_decision_minimizer framework loss)
    (beta alpha : ℕ → ℝ → ℝ) : Prop :=
  ∀ (T : ℕ) (hT : 0 < T) (delta : ℝ)
      (hdelta : delta ∈ Set.Icc (0 : ℝ) 1),
      0 ≤ alpha T delta ∧
        ∀ model, model ∈ framework.hypothesisClass →
          ∀ environment, environment_consistent environment model →
            1 - delta ≤ event_probability
              (e2d_policy framework estimator loss minimizer beta T delta)
              environment T
              (fun history =>
                cumulative_optimism framework estimator
                  (e2d_policy framework estimator loss minimizer beta T delta)
                  environment history ≤ alpha T delta)

@[blueprint "lem:summable-of-nonnegative-sum-le-local"
  (statement := /-- A nonnegative real-valued family whose finite partial sums
  have a common upper bound is summable. -/)
  (proof := /-- The finite partial sums form a monotone net.  Their common upper
  bound makes their supremum finite, and the net converges to this supremum,
  which is therefore the infinite sum of the family. -/)
  (title := /-- Bounded partial sums imply summability -/)
  (latexEnv := "lemma")]
lemma summable_of_nonnegative_sum_le_local
    {ι : Type*} {f : ι → ℝ} {C : ℝ} (hf : ∀ i, 0 ≤ f i)
    (hC : ∀ u : Finset ι, ∑ i ∈ u, f i ≤ C) :
    Summable f := by
  exact ⟨⨆ u : Finset ι, ∑ i ∈ u, f i,
    tendsto_atTop_ciSup (Finset.sum_mono_set_of_nonneg hf)
      ⟨C, fun _ ⟨u, hu⟩ => hu ▸ hC u⟩⟩

@[blueprint "lem:summable-prod-of-nonnegative-local"
  (statement := /-- A nonnegative real-valued family on a product is summable
  exactly when every second-coordinate fiber is summable and the family of
  fiber sums is summable. -/)
  (proof := /-- For a finite set of pairs, group the sum by first coordinate.
  Each fiber sum is bounded by the corresponding infinite fiber sum, and the
  resulting finite outer sum is bounded by the outer infinite sum.  Apply
  \cref{lem:summable-of-nonnegative-sum-le-local} to these uniform bounds.  The
  converse follows by restricting a summable family to each fiber and taking
  its iterated sum. -/)
  (title := /-- Tonelli criterion for nonnegative real product families -/)
  (latexEnv := "lemma")]
lemma summable_prod_of_nonnegative_local
    {ι κ : Type*} {f : ι × κ → ℝ} (hf : ∀ x, 0 ≤ f x) :
    Summable f ↔
      (∀ i, Summable (fun j => f (i, j))) ∧
        Summable (fun i => ∑' j, f (i, j)) := by
  classical
  constructor
  · intro h
    constructor
    · intro i
      exact h.comp_injective (fun x y hxy => congrArg Prod.snd hxy)
    · exact h.prod
  · rintro ⟨hinner, houter⟩
    apply summable_of_nonnegative_sum_le_local hf
    intro u
    calc
      (∑ z ∈ u, f z) =
          ∑ i ∈ u.image Prod.fst,
            ∑ z ∈ u with z.1 = i, f z := by
        symm
        calc
          (∑ i ∈ u.image Prod.fst,
              ∑ z ∈ u with z.1 = i, f z) =
              ∑ z ∈ u with z.1 ∈ u.image Prod.fst, f z :=
            Finset.sum_fiberwise_eq_sum_filter u
              (u.image Prod.fst) Prod.fst f
          _ = ∑ z ∈ u, f z := by
            have hfilter :
                u.filter (fun z => z.1 ∈ u.image Prod.fst) = u := by
              ext z
              constructor
              · intro hz
                exact (Finset.mem_filter.mp hz).1
              · intro hz
                apply Finset.mem_filter.mpr
                exact ⟨hz, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
            rw [hfilter]
      _ ≤ ∑ i ∈ u.image Prod.fst, ∑' j, f (i, j) := by
        apply Finset.sum_le_sum
        intro i hi
        let v := u.filter (fun z : ι × κ => z.1 = i)
        have hvfst (z : ι × κ) (hz : z ∈ v) : z.1 = i := by
          exact (Finset.mem_filter.mp hz).2
        have hinj : Set.InjOn Prod.snd (v : Set (ι × κ)) := by
          intro x hx y hy hxy
          apply Prod.ext
          · rw [hvfst x hx, hvfst y hy]
          · exact hxy
        calc
          (∑ z ∈ u with z.1 = i, f z) =
              ∑ z ∈ v, f (i, z.2) := by
            apply Finset.sum_congr rfl
            intro z hz
            have hzpair : z = (i, z.2) := by
              exact Prod.ext (hvfst z hz) rfl
            rw [hzpair]
          _ = ∑ j ∈ v.image Prod.snd, f (i, j) := by
            symm
            exact Finset.sum_image hinj
          _ ≤ ∑' j, f (i, j) :=
            (hinner i).sum_le_tsum _ (fun j _ => hf (i, j))
      _ ≤ ∑' i, ∑' j, f (i, j) :=
        houter.sum_le_tsum _ (fun i _ =>
          tsum_nonneg (fun j => hf (i, j)))

@[blueprint "lem:trajectory-probability-nonnegative"
  (statement := /-- Every finite trajectory has nonnegative probability under
  every online policy and online environment. -/)
  (proof := /-- Induction on the history and the recursion in
  \cref{def:trajectory-probability} reduce the claim to nonnegativity of the
  action and observation probability masses. -/)
  (title := /-- Nonnegativity of trajectory probabilities -/)
  (latexEnv := "lemma")]
lemma trajectory_probability_nonnegative
    {Action Observation : Type*}
    (policy : online_policy Action Observation)
    (environment : online_environment Action Observation) :
    ∀ history, 0 ≤ trajectory_probability policy environment history := by
  intro history
  induction history with
  | nil => simp [trajectory_probability]
  | cons pair history ih =>
      simp only [trajectory_probability]
      exact mul_nonneg (mul_nonneg ih
        ((policy history).nonnegative pair.1))
        ((environment history pair.1).nonnegative pair.2)

@[blueprint "lem:trajectory-probability-tuple-summable"
  (statement := /-- For every horizon $T$, trajectory probability is summable
  over the tuples representing histories of length $T$, and its sum is one. -/)
  (proof := /-- Induct on $T$.  Separate a tuple into its preceding tuple and
  newest action--observation pair.  Nonnegativity follows from
  \cref{lem:trajectory-probability-nonnegative}; the product summability
  criterion \cref{lem:summable-prod-of-nonnegative-local} applies because the
  action and observation masses are summable, and their total masses are one.
  The remaining outer sum is the induction hypothesis. -/)
  (title := /-- Summability and normalization for trajectory tuples -/)
  (latexEnv := "lemma")]
lemma trajectory_probability_tuple_summable
    {Action Observation : Type*}
    (policy : online_policy Action Observation)
    (environment : online_environment Action Observation) (T : ℕ) :
    Summable (fun x : Fin T → Action × Observation =>
      trajectory_probability policy environment (List.ofFn x)) ∧
    (∑' x : Fin T → Action × Observation,
      trajectory_probability policy environment (List.ofFn x)) = 1 := by
  induction T with
  | zero =>
      constructor
      · exact Summable.of_finite
      · simp [trajectory_probability]
  | succ T ih =>
      let e := (Equiv.prodComm (Fin T → Action × Observation)
        (Action × Observation)).trans
          (Fin.consEquiv (fun _ : Fin (T + 1) => Action × Observation))
      have hhead : ∀ tail : Fin T → Action × Observation,
          Summable (fun pair : Action × Observation =>
            trajectory_probability policy environment (List.ofFn tail) *
              (policy (List.ofFn tail)).mass pair.1 *
              (environment (List.ofFn tail) pair.1).mass pair.2) := by
        intro tail
        apply (summable_prod_of_nonnegative_local (fun pair =>
          mul_nonneg
            (mul_nonneg (trajectory_probability_nonnegative _ _ _)
              ((policy (List.ofFn tail)).nonnegative pair.1))
            ((environment (List.ofFn tail) pair.1).nonnegative pair.2))).2
        constructor
        · intro action
          simpa [mul_assoc] using
            (environment (List.ofFn tail) action).summable.mul_left
              (trajectory_probability policy environment (List.ofFn tail) *
                (policy (List.ofFn tail)).mass action)
        · have heq : (fun action => ∑' observation,
              trajectory_probability policy environment (List.ofFn tail) *
                (policy (List.ofFn tail)).mass action *
                (environment (List.ofFn tail) action).mass observation) =
              (fun action =>
                trajectory_probability policy environment (List.ofFn tail) *
                  (policy (List.ofFn tail)).mass action) := by
            funext action
            rw [(environment (List.ofFn tail) action).summable.tsum_mul_left]
            rw [(environment (List.ofFn tail) action).total_mass_one]
            ring
          rw [heq]
          exact (policy (List.ofFn tail)).summable.mul_left
            (trajectory_probability policy environment (List.ofFn tail))
      have hhead_sum : (fun tail : Fin T → Action × Observation =>
          ∑' pair : Action × Observation,
            trajectory_probability policy environment (List.ofFn tail) *
              (policy (List.ofFn tail)).mass pair.1 *
              (environment (List.ofFn tail) pair.1).mass pair.2) =
          (fun tail =>
            trajectory_probability policy environment (List.ofFn tail)) := by
        funext tail
        rw [(hhead tail).tsum_prod]
        have heq : (fun action => ∑' observation,
            trajectory_probability policy environment (List.ofFn tail) *
              (policy (List.ofFn tail)).mass action *
              (environment (List.ofFn tail) action).mass observation) =
            (fun action =>
              trajectory_probability policy environment (List.ofFn tail) *
                (policy (List.ofFn tail)).mass action) := by
          funext action
          rw [(environment (List.ofFn tail) action).summable.tsum_mul_left]
          rw [(environment (List.ofFn tail) action).total_mass_one]
          ring
        rw [heq]
        rw [(policy (List.ofFn tail)).summable.tsum_mul_left]
        rw [(policy (List.ofFn tail)).total_mass_one]
        ring
      have hs : Summable (fun z :
          (Fin T → Action × Observation) × (Action × Observation) =>
            trajectory_probability policy environment (List.ofFn z.1) *
              (policy (List.ofFn z.1)).mass z.2.1 *
              (environment (List.ofFn z.1) z.2.1).mass z.2.2) := by
        apply (summable_prod_of_nonnegative_local
          (f := fun z : (Fin T → Action × Observation) ×
              (Action × Observation) =>
            trajectory_probability policy environment (List.ofFn z.1) *
              (policy (List.ofFn z.1)).mass z.2.1 *
              (environment (List.ofFn z.1) z.2.1).mass z.2.2)
          (fun z : (Fin T → Action × Observation) ×
              (Action × Observation) => mul_nonneg
            (mul_nonneg (trajectory_probability_nonnegative _ _ _)
              ((policy (List.ofFn z.1)).nonnegative z.2.1))
            ((environment (List.ofFn z.1) z.2.1).nonnegative z.2.2))).2
        constructor
        · exact hhead
        · rw [hhead_sum]
          exact ih.1
      constructor
      · apply e.summable_iff.mp
        convert hs using 1
        funext z
        rcases z with ⟨tail, pair⟩
        simp [e, List.ofFn_cons, trajectory_probability]
      · rw [← e.tsum_eq]
        simp [e, List.ofFn_cons, trajectory_probability]
        rw [hs.tsum_prod]
        rw [hhead_sum]
        exact ih.2

@[blueprint "lem:event-probability-tuple-tsum-local"
  (statement := /-- For every horizon $T$ and event on online histories, its
  probability is the sum of trajectory probabilities over the $T$-tuples
  whose associated histories satisfy the event. -/)
  (proof := /-- Reindex histories by the canonical dependent sum of fixed-length
  tuples.  The length condition restricts the dependent sum to its $T$-fiber;
  extend the event-weighted function on that fiber by zero and use injectivity
  of the fiber embedding to identify its infinite sum. -/)
  (title := /-- Tuple representation of event probabilities -/)
  (latexEnv := "lemma")]
lemma event_probability_tuple_tsum_local
    {Action Observation : Type*}
    (policy : online_policy Action Observation)
    (environment : online_environment Action Observation)
    (T : ℕ) (event : online_history Action Observation → Prop)
    [DecidablePred event] :
    event_probability policy environment T event =
      ∑' x : Fin T → Action × Observation,
        if event (List.ofFn x) then
          trajectory_probability policy environment (List.ofFn x)
        else 0 := by
  classical
  let f : (Fin T → Action × Observation) → ℝ := fun x =>
    if event (List.ofFn x) then
      trajectory_probability policy environment (List.ofFn x)
    else 0
  let embed : (Fin T → Action × Observation) →
      (Σ n, Fin n → Action × Observation) := fun x => ⟨T, x⟩
  have hi : Function.Injective embed := by
    intro x y hxy
    exact eq_of_heq (Sigma.mk.inj_iff.mp hxy).2
  unfold event_probability
  rw [← (List.equivSigmaTuple
    (α := Action × Observation)).symm.tsum_eq]
  simp only [List.equivSigmaTuple_symm_apply, List.length_ofFn]
  have heq : (fun c : Σ n, Fin n → Action × Observation =>
      if c.1 = T ∧ event (List.ofFn c.2) then
        trajectory_probability policy environment (List.ofFn c.2)
      else 0) = Function.extend embed f 0 := by
    funext c
    rcases c with ⟨n, x⟩
    by_cases hn : n = T
    · subst n
      simp [embed, f, hi]
    · simp only [hn, false_and, if_false]
      symm
      apply Function.extend_apply'
      rintro ⟨y, hy⟩
      exact hn (congrArg Sigma.fst hy).symm
  rw [heq, tsum_extend_zero hi]

@[blueprint "lem:trajectory-probability-tuple-event-summable-local"
  (statement := /-- For every fixed horizon, the trajectory probabilities
  restricted to an arbitrary event on trajectory tuples form a summable
  family. -/)
  (proof := /-- Restrict the summable trajectory family supplied by
  \cref{lem:trajectory-probability-tuple-summable} to the subtype defined by
  the event, then identify subtype summability with summability of the
  corresponding indicator function. -/)
  (title := /-- Summability of fixed-horizon event probabilities -/)
  (latexEnv := "lemma")]
lemma trajectory_probability_tuple_event_summable_local
    {Action Observation : Type*}
    (policy : online_policy Action Observation)
    (environment : online_environment Action Observation) (T : ℕ)
    (event : (Fin T → Action × Observation) → Prop)
    [DecidablePred event] :
    Summable (fun x : Fin T → Action × Observation =>
      if event x then
        trajectory_probability policy environment (List.ofFn x)
      else 0) := by
  classical
  let s : Set (Fin T → Action × Observation) := {x | event x}
  have hs : Summable (fun x : s =>
      trajectory_probability policy environment (List.ofFn x.1)) :=
    (trajectory_probability_tuple_summable policy environment T).1.subtype s
  have hi : Summable (s.indicator (fun x =>
      trajectory_probability policy environment (List.ofFn x))) :=
    summable_subtype_iff_indicator.mp hs
  refine hi.congr ?_
  intro x
  by_cases hx : event x <;> simp [s, hx]

@[blueprint "lem:e2d-total-expectation-bound-local"
  (statement := /-- Fix the E2D policy at horizon $T$ and confidence level
  $\delta$.  Suppose a cumulative decision term is at most $2T d$ whenever
  the inaccuracy event holds, and its sum with cumulative optimism defines a
  trajectory total bounded above by the history length and summable at
  horizon $T$.  If $d\geq0$, then under every environment consistent with the
  comparison model, the expected total is at most
  $2Td+\alpha(T,\delta)+2T\delta$. -/)
  (proof := /-- Reindex both certified high-probability events by
  \cref{lem:event-probability-tuple-tsum-local}.  Their tuple indicators are
  summable by \cref{lem:trajectory-probability-tuple-event-summable-local}.
  The union bound, together with normalization from
  \cref{lem:trajectory-probability-tuple-summable}, gives failure probability
  at most $2\delta$.  On the intersection, add the decision and optimism
  bounds; on its complement, use the length bound.  Multiply pointwise by the
  nonnegative trajectory weights from
  \cref{lem:trajectory-probability-nonnegative}, sum, and use normalization. -/)
  (title := /-- Expected E2D trajectory-total bound -/)
  (latexEnv := "lemma")]
lemma e2d_total_expectation_bound_local
    {Action Observation : Type*}
    (framework : robust_online_decision_framework Action Observation)
    (T : ℕ) (hT : 0 < T) (delta : ℝ)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) 1)
    (loss : robust_loss Action Observation)
    (minimizer : fuzzy_decision_minimizer framework loss)
    (estimator : online_estimation_oracle Action Observation)
    (beta alpha : ℕ → ℝ → ℝ)
    (hbeta : is_inaccuracy_bound framework estimator loss minimizer beta)
    (halpha : is_optimism_bound framework estimator loss minimizer beta alpha)
    (model : robust_model Action Observation)
    (hmodel : model ∈ framework.hypothesisClass)
    (dec : ℝ)
    (decision : online_history Action Observation → ℝ)
    (total : online_environment Action Observation →
      online_history Action Observation → ℝ)
    (hdecision_good : ∀ history, history.length = T →
      cumulative_inaccuracy estimator loss model
          (e2d_policy framework estimator loss minimizer beta T delta)
          history ≤ beta T delta →
        decision history ≤ 2 * (T : ℝ) * dec)
    (htotal_eq : ∀ environment history,
      total environment history =
        decision history +
          cumulative_optimism framework estimator
            (e2d_policy framework estimator loss minimizer beta T delta)
            environment history)
    (htotal_le : ∀ environment history,
      total environment history ≤ (history.length : ℝ))
    (htotal_summable : ∀ environment,
      Summable (fun x : Fin T → Action × Observation =>
        trajectory_probability
            (e2d_policy framework estimator loss minimizer beta T delta)
            environment (List.ofFn x) *
          total environment (List.ofFn x)))
    (hdec_nonneg : 0 ≤ dec)
    (environment : online_environment Action Observation)
    (hconsistent : environment_consistent environment model) :
    (∑' x : Fin T → Action × Observation,
      trajectory_probability
          (e2d_policy framework estimator loss minimizer beta T delta)
          environment (List.ofFn x) *
        total environment (List.ofFn x)) ≤
      2 * (T : ℝ) * dec + alpha T delta +
        2 * (T : ℝ) * delta := by
  classical
  let policy :=
    e2d_policy framework estimator loss minimizer beta T delta
  let A : (Fin T → Action × Observation) → Prop := fun x =>
    cumulative_inaccuracy estimator loss model policy (List.ofFn x) ≤
      beta T delta
  let B : (Fin T → Action × Observation) → Prop := fun x =>
    cumulative_optimism framework estimator policy environment
      (List.ofFn x) ≤ alpha T delta
  let G : (Fin T → Action × Observation) → Prop := fun x =>
    A x ∧ B x
  let Bad : (Fin T → Action × Observation) → Prop := fun x =>
    ¬ G x
  let p : (Fin T → Action × Observation) → ℝ := fun x =>
    trajectory_probability policy environment (List.ofFn x)
  have hp := trajectory_probability_tuple_summable
    policy environment T
  have hA : 1 - delta ≤ ∑' x, if A x then p x else 0 := by
    have hb := hbeta T hT delta hdelta model hmodel
      environment hconsistent
    rw [event_probability_tuple_tsum_local] at hb
    simpa [A, p, policy] using hb
  have hop := halpha T hT delta hdelta
  have halpha_nonneg : 0 ≤ alpha T delta := hop.1
  have hB : 1 - delta ≤ ∑' x, if B x then p x else 0 := by
    have hb := hop.2 model hmodel environment hconsistent
    rw [event_probability_tuple_tsum_local] at hb
    simpa [B, p, policy] using hb
  have hsA : Summable (fun x => if A x then p x else 0) := by
    simpa [p] using trajectory_probability_tuple_event_summable_local
      policy environment T A
  have hsB : Summable (fun x => if B x then p x else 0) := by
    simpa [p] using trajectory_probability_tuple_event_summable_local
      policy environment T B
  have hsG : Summable (fun x => if G x then p x else 0) := by
    simpa [p] using trajectory_probability_tuple_event_summable_local
      policy environment T G
  have hsBad : Summable (fun x => if Bad x then p x else 0) := by
    simpa [p] using trajectory_probability_tuple_event_summable_local
      policy environment T Bad
  have hunion :
      (∑' x, if A x then p x else 0) +
          (∑' x, if B x then p x else 0) ≤
        (∑' x, if G x then p x else 0) + 1 := by
    calc
      (∑' x, if A x then p x else 0) +
            (∑' x, if B x then p x else 0) =
          ∑' x, ((if A x then p x else 0) +
            (if B x then p x else 0)) :=
        (hsA.tsum_add hsB).symm
      _ ≤ ∑' x, ((if G x then p x else 0) + p x) := by
        apply (hsA.add hsB).tsum_le_tsum
        · intro x
          have hp_nonneg : 0 ≤ p x :=
            trajectory_probability_nonnegative policy environment
              (List.ofFn x)
          by_cases hAx : A x <;> by_cases hBx : B x <;>
            simp [G, hAx, hBx, hp_nonneg]
        · exact hsG.add hp.1
      _ = (∑' x, if G x then p x else 0) + ∑' x, p x :=
        hsG.tsum_add hp.1
      _ = (∑' x, if G x then p x else 0) + 1 := by
        rw [hp.2]
  have hG_lower : 1 - 2 * delta ≤
      ∑' x, if G x then p x else 0 := by
    linarith [hA, hB, hunion]
  have hpartition :
      (∑' x, if G x then p x else 0) +
          (∑' x, if Bad x then p x else 0) = 1 := by
    rw [← hsG.tsum_add hsBad]
    calc
      (∑' x, ((if G x then p x else 0) +
          (if Bad x then p x else 0))) =
          ∑' x, p x := by
        apply tsum_congr
        intro x
        by_cases hGx : G x <;> simp [Bad, hGx]
      _ = 1 := hp.2
  have hBad_upper :
      (∑' x, if Bad x then p x else 0) ≤ 2 * delta := by
    linarith [hG_lower, hpartition]
  let C := 2 * (T : ℝ) * dec + alpha T delta
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have htotal_point (x : Fin T → Action × Observation) :
      total environment (List.ofFn x) ≤
        C + (T : ℝ) * (if Bad x then 1 else 0) := by
    by_cases hGx : G x
    · have hnotBad : ¬ Bad x := by
        intro hBad
        exact hBad hGx
      rw [if_neg hnotBad, mul_zero, add_zero]
      rw [htotal_eq]
      exact add_le_add
        (hdecision_good (List.ofFn x) (by simp)
          (by simpa [A, policy] using hGx.1))
        (by simpa [B, policy] using hGx.2)
    · have hBad : Bad x := hGx
      rw [if_pos hBad, mul_one]
      have ht := htotal_le environment (List.ofFn x)
      simp only [List.length_ofFn] at ht
      linarith
  have hweighted_point (x : Fin T → Action × Observation) :
      p x * total environment (List.ofFn x) ≤
        p x * C + (if Bad x then p x else 0) * (T : ℝ) := by
    have hp_nonneg : 0 ≤ p x :=
      trajectory_probability_nonnegative policy environment (List.ofFn x)
    have hm := mul_le_mul_of_nonneg_left (htotal_point x) hp_nonneg
    by_cases hBad : Bad x <;> simp [hBad] at hm ⊢ <;> linarith
  have hsC : Summable (fun x => p x * C) := hp.1.mul_right C
  have hsBadT :
      Summable (fun x => (if Bad x then p x else 0) * (T : ℝ)) :=
    hsBad.mul_right (T : ℝ)
  have hsTotal :
      Summable (fun x => p x * total environment (List.ofFn x)) := by
    simpa [p, policy] using htotal_summable environment
  calc
    (∑' x, p x * total environment (List.ofFn x)) ≤
        ∑' x, (p x * C +
          (if Bad x then p x else 0) * (T : ℝ)) :=
      hsTotal.tsum_le_tsum hweighted_point (hsC.add hsBadT)
    _ = C + (∑' x, if Bad x then p x else 0) * (T : ℝ) := by
      rw [hsC.tsum_add hsBadT, hp.1.tsum_mul_right, hp.2,
        hsBad.tsum_mul_right]
      ring
    _ ≤ C + 2 * (T : ℝ) * delta := by
      have hT_nonneg : 0 ≤ (T : ℝ) := Nat.cast_nonneg T
      have hm := mul_le_mul_of_nonneg_right hBad_upper hT_nonneg
      nlinarith
    _ = 2 * (T : ℝ) * dec + alpha T delta +
        2 * (T : ℝ) * delta := by
      rfl

@[blueprint "thm:e2d-regret-bound"
  (statement := /-- Let $\mathcal A$ and $\mathcal O$ be types, let a robust
  online decision framework on these types be fixed, let $T\geq 1$, and let
  $\delta\in[0,1]$.  Fix a nonnegative robust loss $\mathcal L$, a certified
  fuzzy decision minimizer for this framework and loss, an online estimation
  oracle $\widehat M$, and functions $\beta,\alpha:\mathbb N\times\mathbb R
  \to\mathbb R$.  Suppose that $\beta$ is an inaccuracy bound and $\alpha$ is
  an optimism bound for this oracle, loss, minimizer, and framework.  Then, for
  every $M$ in the framework's hypothesis class and every $\varepsilon\in
  \mathbb R$ satisfying $\varepsilon=\sqrt{\beta(T,\delta)/T}$, the E2D policy
  determined by these data satisfies
  \[
    \operatorname{REG}(\mathrm{E2D},M,T)
    \leq 2T\,\operatorname{dec}^{f,\mathcal L}_{\varepsilon}(\mathcal M)
      +\alpha(T,\delta)+2T\delta.
  \] -/)
  (proof := /-- First, the definitions of robust action value and robust
  optimal value, together with the unit reward bound, show that both values
  lie in $[0,1]$.  Averaging bounded action gaps and model gaps then bounds the
  fuzzy decision objective, its value at a reference model, and its worst-case
  value.  The summability needed for these averages follows from
  \cref{lem:summable-prod-of-nonnegative-local}.  Since the certified minimizer
  attains the coefficient at each reference model, its one-step decision gap
  is at most the worst-case coefficient plus the corresponding loss divided
  by the squared radius.  Treating positive and zero squared radius separately
  and summing over a history shows that, on the certified inaccuracy event,
  the cumulative decision term is at most twice the horizon times the
  coefficient.

  For a consistent environment, add cumulative optimism to this decision
  term.  The unit reward bounds and consistency show that each one-step total
  lies in $[-1,1]$.  Induction over tuple trajectories, using nonnegative
  trajectory weights from \cref{lem:trajectory-probability-nonnegative}, their
  summability and normalization from
  \cref{lem:trajectory-probability-tuple-summable}, and the product criterion
  above, proves that the expected trajectory total equals the horizon times
  the robust optimal value minus expected cumulative reward.  Applying
  \cref{lem:e2d-total-expectation-bound-local} to the inaccuracy and optimism
  certificates bounds this expectation by the claimed right-hand side for
  every consistent environment.  Finally, choose at each action a probability
  law from the nonempty carrier of the comparison model; this gives a
  consistent environment and hence makes the defining supremum nonempty.
  Taking the supremum over all consistent environments yields the stated
  regret bound. -/)
  (title := /-- Regret bound for estimations to decisions -/)
  (latexEnv := "theorem")]
theorem e2d_regret_bound
    {Action Observation : Type*}
    (framework : robust_online_decision_framework Action Observation)
    (T : ℕ) (hT : 0 < T) (delta : ℝ) (hdelta : delta ∈ Set.Icc (0 : ℝ) 1)
    (loss : robust_loss Action Observation)
    (minimizer : fuzzy_decision_minimizer framework loss)
    (estimator : online_estimation_oracle Action Observation)
    (beta alpha : ℕ → ℝ → ℝ)
    (hbeta : is_inaccuracy_bound framework estimator loss minimizer beta)
    (halpha : is_optimism_bound framework estimator loss minimizer beta alpha)
    (model : robust_model Action Observation)
    (hmodel : model ∈ framework.hypothesisClass)
    (epsilon : ℝ) (hepsilon : epsilon = Real.sqrt (beta T delta / (T : ℝ))) :
    e2d_regret framework estimator loss minimizer beta model T delta ≤
      2 * (T : ℝ) *
          fuzzy_decision_estimation_coefficient framework loss epsilon +
        alpha T delta + 2 * (T : ℝ) * delta := by
  classical
  subst epsilon
  have havg (m : robust_model Action Observation) (a : Action)
      (p : {p // p ∈ (m a).carrier}) :
      (∑' o, p.1 o * framework.reward a o) ∈ Set.Icc (0 : ℝ) 1 := by
    have hn (o) : 0 ≤ p.1 o * framework.reward a o :=
      mul_nonneg ((m a).mass_nonnegative p.1 p.2 o)
        (framework.reward_mem_unit a o).1
    have hle (o) : p.1 o * framework.reward a o ≤ p.1 o :=
      mul_le_of_le_one_right ((m a).mass_nonnegative p.1 p.2 o)
        (framework.reward_mem_unit a o).2
    have hs : Summable (fun o => p.1 o * framework.reward a o) := by
      let f : Observation × Bool → ℝ := fun z =>
        if z.2 then p.1 z.1 * framework.reward a z.1
        else p.1 z.1 * (1 - framework.reward a z.1)
      have hf : Summable f := by
        apply (summable_prod_of_nonnegative_local (fun z => by
          dsimp [f]
          split
          · exact hn z.1
          · exact mul_nonneg ((m a).mass_nonnegative p.1 p.2 z.1)
              (sub_nonneg.mpr (framework.reward_mem_unit a z.1).2))).2
        constructor
        · intro o
          exact Summable.of_finite
        · simpa [f, mul_sub] using (m a).mass_summable p.1 p.2
      have hi : Function.Injective (fun o : Observation => (o, true)) := by
        intro x y h
        exact congrArg Prod.fst h
      exact hf.comp_injective hi
    constructor
    · exact tsum_nonneg hn
    · rw [← (m a).total_mass_one p.1 p.2]
      exact hs.tsum_le_tsum hle ((m a).mass_summable p.1 p.2)
  have hAction : Nonempty Action := by
    by_contra hn
    haveI : IsEmpty Action := not_nonempty_iff.mp hn
    let q := Classical.choice framework.action_distribution_nonempty
    have hq := q.total_mass_one
    simpa using hq
  have haction (m : robust_model Action Observation) (a : Action) :
      robust_action_value framework m a ∈ Set.Icc (0 : ℝ) 1 := by
    unfold robust_action_value
    obtain ⟨p, hp⟩ := (m a).nonempty
    let pp : {p // p ∈ (m a).carrier} := ⟨p, hp⟩
    have hne : (Set.range fun q : {q // q ∈ (m a).carrier} =>
        ∑' o, q.1 o * framework.reward a o).Nonempty :=
      ⟨∑' o, pp.1 o * framework.reward a o, Set.mem_range_self pp⟩
    have hb : BddBelow (Set.range fun q : {q // q ∈ (m a).carrier} =>
        ∑' o, q.1 o * framework.reward a o) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨q, rfl⟩
      exact (havg m a q).1
    constructor
    · apply le_csInf hne
      rintro _ ⟨q, rfl⟩
      exact (havg m a q).1
    · calc
        sInf (Set.range fun q : {q // q ∈ (m a).carrier} =>
          ∑' o, q.1 o * framework.reward a o) ≤
            ∑' o, pp.1 o * framework.reward a o :=
          csInf_le hb (Set.mem_range_self pp)
        _ ≤ 1 := (havg m a pp).2
  have hoptimal (m : robust_model Action Observation) :
      robust_optimal_value framework m ∈ Set.Icc (0 : ℝ) 1 := by
    unfold robust_optimal_value
    let a := Classical.choice hAction
    have hb : BddAbove
        (Set.range fun a => robust_action_value framework m a) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨b, rfl⟩
      exact (haction m b).2
    constructor
    · calc
        0 ≤ robust_action_value framework m a := (haction m a).1
        _ ≤ sSup (Set.range fun b =>
            robust_action_value framework m b) :=
          le_csSup hb (Set.mem_range_self a)
    · apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨a, rfl⟩
      exact (haction m a).2
  have havg_action (q : probability_mass Action) (f : Action → ℝ)
      (hf : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) :
      (∑' x, q.mass x * f x) ∈ Set.Icc (-1 : ℝ) 1 := by
    have hs : Summable (fun x => q.mass x * f x) := by
      let u : Action → ℝ := fun x => (f x + 1) / 2
      have hu (x) : u x ∈ Set.Icc (0 : ℝ) 1 := by
        dsimp [u]
        constructor <;> linarith [(hf x).1, (hf x).2]
      have hsu : Summable (fun x => q.mass x * u x) := by
        let g : Action × Bool → ℝ := fun z =>
          if z.2 then q.mass z.1 * u z.1
          else q.mass z.1 * (1 - u z.1)
        have hg : Summable g := by
          apply (summable_prod_of_nonnegative_local (fun z => by
            dsimp [g]
            split
            · exact mul_nonneg (q.nonnegative z.1) (hu z.1).1
            · exact mul_nonneg (q.nonnegative z.1)
                (sub_nonneg.mpr (hu z.1).2))).2
          constructor
          · intro x
            exact Summable.of_finite
          · simpa [g, mul_sub] using q.summable
        have hi : Function.Injective (fun x : Action => (x, true)) := by
          intro x y h
          exact congrArg Prod.fst h
        exact hg.comp_injective hi
      rw [show (fun x => q.mass x * f x) =
          (fun x => 2 * (q.mass x * u x) - q.mass x) by
        funext x
        dsimp [u]
        ring]
      exact (hsu.mul_left 2).sub q.summable
    constructor
    · calc
        -1 = -(∑' x, q.mass x) := by rw [q.total_mass_one]
        _ = ∑' x, -(q.mass x) := tsum_neg.symm
        _ ≤ ∑' x, q.mass x * f x := q.summable.neg.tsum_le_tsum
          (fun x => by
            have hx := (hf x).1
            nlinarith [q.nonnegative x]) hs
    · calc
        (∑' x, q.mass x * f x) ≤ ∑' x, q.mass x :=
          hs.tsum_le_tsum
            (fun x => by
              have hx := (hf x).2
              nlinarith [q.nonnegative x]) q.summable
        _ = 1 := q.total_mass_one
  have havg_models
      (q : subprobability_mass (robust_model Action Observation))
      (f : robust_model Action Observation → ℝ)
      (hf : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) :
      (∑' x, q.mass x * f x) ∈ Set.Icc (-1 : ℝ) 1 := by
    have hs : Summable (fun x => q.mass x * f x) := by
      let u : robust_model Action Observation → ℝ :=
        fun x => (f x + 1) / 2
      have hu (x) : u x ∈ Set.Icc (0 : ℝ) 1 := by
        dsimp [u]
        constructor <;> linarith [(hf x).1, (hf x).2]
      have hsu : Summable (fun x => q.mass x * u x) := by
        let g : robust_model Action Observation × Bool → ℝ := fun z =>
          if z.2 then q.mass z.1 * u z.1
          else q.mass z.1 * (1 - u z.1)
        have hg : Summable g := by
          apply (summable_prod_of_nonnegative_local (fun z => by
            dsimp [g]
            split
            · exact mul_nonneg (q.nonnegative z.1) (hu z.1).1
            · exact mul_nonneg (q.nonnegative z.1)
                (sub_nonneg.mpr (hu z.1).2))).2
          constructor
          · intro x
            exact Summable.of_finite
          · simpa [g, mul_sub] using q.summable
        let embed : robust_model Action Observation →
            robust_model Action Observation × Bool := fun x => (x, true)
        have hi : Function.Injective embed := by
          intro x y h
          exact congrArg Prod.fst h
        have hc : Summable (g ∘ embed) := hg.comp_injective hi
        have heq : (g ∘ embed) = fun x => q.mass x * u x := by
          funext x
          rfl
        rw [← heq]
        exact hc
      rw [show (fun x => q.mass x * f x) =
          (fun x => 2 * (q.mass x * u x) - q.mass x) by
        funext x
        dsimp [u]
        ring]
      exact (hsu.mul_left 2).sub q.summable
    constructor
    · calc
        -1 ≤ -(∑' x, q.mass x) := by linarith [q.total_mass_le_one]
        _ = ∑' x, -(q.mass x) := tsum_neg.symm
        _ ≤ ∑' x, q.mass x * f x := q.summable.neg.tsum_le_tsum
          (fun x => by
            have hx := (hf x).1
            nlinarith [q.nonnegative x]) hs
    · calc
        (∑' x, q.mass x * f x) ≤ ∑' x, q.mass x :=
          hs.tsum_le_tsum
            (fun x => by
              have hx := (hf x).2
              nlinarith [q.nonnegative x]) q.summable
        _ ≤ 1 := q.total_mass_le_one
  have hgap (reference m : robust_model Action Observation)
      (actions : probability_mass Action) :
      (∑' a, actions.mass a *
        (robust_optimal_value framework m -
          robust_action_value framework reference a)) ∈
        Set.Icc (-1 : ℝ) 1 := by
    apply havg_action
    intro a
    constructor <;> linarith [(hoptimal m).1, (hoptimal m).2,
      (haction reference a).1, (haction reference a).2]
  have hobjective (e : ℝ) (reference : robust_model Action Observation)
      (actions : probability_mass Action) :
      fuzzy_decision_objective framework loss e reference actions ∈
        Set.Icc (0 : ℝ) 1 := by
    let S : Set ℝ := {value | ∃ mu :
        subprobability_mass (robust_model Action Observation),
      (∀ m, 0 < mu.mass m → m ∈ framework.hypothesisClass) ∧
      (∑' m, mu.mass m *
        (∑' a, actions.mass a * (loss reference m a : ℝ))) ≤ e ^ 2 ∧
      value = ∑' m, mu.mass m *
        (∑' a, actions.mass a *
          (robust_optimal_value framework m -
            robust_action_value framework reference a))}
    let zeroMu : subprobability_mass (robust_model Action Observation) :=
      { mass := fun _ => 0
        nonnegative := fun _ => le_rfl
        summable := summable_zero
        total_mass_le_one := by simp }
    have hzero : (0 : ℝ) ∈ S := by
      refine ⟨zeroMu, ?_, ?_, ?_⟩
      · intro m hm
        simp [zeroMu] at hm
      · simp [zeroMu, sq_nonneg]
      · simp [zeroMu]
    have hub : ∀ v ∈ S, v ≤ 1 := by
      intro v hv
      obtain ⟨mu, _, _, rfl⟩ := hv
      exact (havg_models mu
        (fun m => ∑' a, actions.mass a *
          (robust_optimal_value framework m -
            robust_action_value framework reference a))
        (fun m => hgap reference m actions)).2
    have hb : BddAbove S := ⟨1, hub⟩
    change sSup S ∈ Set.Icc (0 : ℝ) 1
    exact ⟨le_csSup hb hzero, csSup_le ⟨0, hzero⟩ hub⟩
  have hcoeff_at (e : ℝ) (reference : robust_model Action Observation) :
      fuzzy_decision_estimation_coefficient_at framework loss e reference ∈
        Set.Icc (0 : ℝ) 1 := by
    unfold fuzzy_decision_estimation_coefficient_at
    have hb : BddBelow (Set.range fun actions =>
        fuzzy_decision_objective framework loss e reference actions) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨actions, rfl⟩
      exact (hobjective e reference actions).1
    let actions := Classical.choice framework.action_distribution_nonempty
    have hne : (Set.range fun q =>
        fuzzy_decision_objective framework loss e reference q).Nonempty :=
      ⟨fuzzy_decision_objective framework loss e reference actions,
        Set.mem_range_self actions⟩
    constructor
    · apply le_csInf hne
      rintro _ ⟨q, rfl⟩
      exact (hobjective e reference q).1
    · calc
        sInf (Set.range fun q =>
          fuzzy_decision_objective framework loss e reference q) ≤
            fuzzy_decision_objective framework loss e reference actions :=
          csInf_le hb (Set.mem_range_self actions)
        _ ≤ 1 := (hobjective e reference actions).2
  have hcoeff (e : ℝ) :
      fuzzy_decision_estimation_coefficient framework loss e ∈
        Set.Icc (0 : ℝ) 1 := by
    unfold fuzzy_decision_estimation_coefficient
    have hb : BddAbove (Set.range fun reference =>
        fuzzy_decision_estimation_coefficient_at framework loss e reference) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨reference, rfl⟩
      exact (hcoeff_at e reference).2
    have hne : (Set.range fun reference =>
        fuzzy_decision_estimation_coefficient_at framework loss e reference).Nonempty :=
      ⟨fuzzy_decision_estimation_coefficient_at framework loss e model,
        Set.mem_range_self model⟩
    constructor
    · calc
        0 ≤ fuzzy_decision_estimation_coefficient_at framework loss e model :=
          (hcoeff_at e model).1
        _ ≤ sSup (Set.range fun reference =>
            fuzzy_decision_estimation_coefficient_at framework loss e reference) :=
          le_csSup hb (Set.mem_range_self model)
    · apply csSup_le hne
      rintro _ ⟨reference, rfl⟩
      exact (hcoeff_at e reference).2
  have hdecision (reference : robust_model Action Observation)
      (hr : 0 < (Real.sqrt (beta T delta / (T : ℝ))) ^ 2) :
      let actions := minimizer.actions
        (Real.sqrt (beta T delta / (T : ℝ))) reference
      let x := ∑' a, actions.mass a * (loss reference model a : ℝ)
      ∑' a, actions.mass a *
          (robust_optimal_value framework model -
            robust_action_value framework reference a) ≤
        fuzzy_decision_estimation_coefficient framework loss
            (Real.sqrt (beta T delta / (T : ℝ))) *
          (1 + x / (Real.sqrt (beta T delta / (T : ℝ))) ^ 2) := by
    dsimp
    let r := Real.sqrt (beta T delta / (T : ℝ))
    let actions := minimizer.actions r reference
    let x := ∑' a, actions.mass a * (loss reference model a : ℝ)
    let gap := ∑' a, actions.mass a *
      (robust_optimal_value framework model -
        robust_action_value framework reference a)
    have hx : 0 ≤ x := tsum_nonneg fun a =>
      mul_nonneg (actions.nonnegative a) (NNReal.coe_nonneg _)
    let w := r ^ 2 / (r ^ 2 + x)
    have hr' : 0 < r ^ 2 := hr
    have hr0 : r ≠ 0 := by nlinarith [sq_nonneg r]
    have hden : 0 < r ^ 2 + x := by nlinarith
    have hw0 : 0 ≤ w := by dsimp [w]; positivity
    have hw1 : w ≤ 1 := by
      dsimp [w]
      apply (div_le_one hden).2
      linarith
    let pointMu :
        subprobability_mass (robust_model Action Observation) :=
      { mass := fun m => if m = model then w else 0
        nonnegative := fun m => by split <;> positivity
        summable := by
          apply summable_of_finite_support
          apply (Set.finite_singleton model).subset
          intro m hm
          simp only [Function.mem_support] at hm
          by_cases hme : m = model
          · simpa [hme]
          · simp [hme] at hm
        total_mass_le_one := by simpa using hw1 }
    let S : Set ℝ := {value | ∃ mu :
        subprobability_mass (robust_model Action Observation),
      (∀ m, 0 < mu.mass m → m ∈ framework.hypothesisClass) ∧
      (∑' m, mu.mass m *
        (∑' a, actions.mass a * (loss reference m a : ℝ))) ≤ r ^ 2 ∧
      value = ∑' m, mu.mass m *
        (∑' a, actions.mass a *
          (robust_optimal_value framework m -
            robust_action_value framework reference a))}
    have hpoint : w * gap ∈ S := by
      refine ⟨pointMu, ?_, ?_, ?_⟩
      · intro m hm
        by_cases hm' : m = model
        · simpa [hm'] using hmodel
        · simp [pointMu, hm'] at hm
      · simp [pointMu, x]
        dsimp [w]
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hden).2
        nlinarith [sq_nonneg (r ^ 2)]
      · simp [pointMu, gap]
    have hub : ∀ v ∈ S, v ≤ 1 := by
      rintro v ⟨mu, _, _, rfl⟩
      exact (havg_models mu
        (fun m => ∑' a, actions.mass a *
          (robust_optimal_value framework m -
            robust_action_value framework reference a))
        (fun m => hgap reference m actions)).2
    have hwgap :
        w * gap ≤ fuzzy_decision_objective
          framework loss r reference actions := by
      unfold fuzzy_decision_objective
      exact le_csSup ⟨1, hub⟩ hpoint
    have hwd :
        w * gap ≤ fuzzy_decision_estimation_coefficient framework loss r := by
      calc
        w * gap ≤ fuzzy_decision_objective framework loss r reference actions :=
          hwgap
        _ = fuzzy_decision_estimation_coefficient_at framework loss r reference :=
          minimizer.attains r reference
        _ ≤ fuzzy_decision_estimation_coefficient framework loss r := by
          unfold fuzzy_decision_estimation_coefficient
          apply le_csSup
          · exact ⟨1, by
              rintro _ ⟨m, rfl⟩
              exact (hcoeff_at r m).2⟩
          · exact Set.mem_range_self reference
    have hwd' :
        (r ^ 2 * gap) / (r ^ 2 + x) ≤
          fuzzy_decision_estimation_coefficient framework loss r := by
      calc
        (r ^ 2 * gap) / (r ^ 2 + x) = w * gap := by
          dsimp [w]
          ring
        _ ≤ fuzzy_decision_estimation_coefficient framework loss r := hwd
    have hmul :
        r ^ 2 * gap ≤
          fuzzy_decision_estimation_coefficient framework loss r *
            (r ^ 2 + x) :=
      (div_le_iff₀ hden).1 hwd'
    change gap ≤
      fuzzy_decision_estimation_coefficient framework loss r *
        (1 + x / r ^ 2)
    rw [show fuzzy_decision_estimation_coefficient framework loss r *
        (1 + x / r ^ 2) =
        (fuzzy_decision_estimation_coefficient framework loss r *
          (r ^ 2 + x)) / r ^ 2 by
      field_simp [hr0]]
    apply (le_div_iff₀ hr').2
    nlinarith
  have hdecision_feasible (reference : robust_model Action Observation)
      (hx : (∑' a,
        (minimizer.actions (Real.sqrt (beta T delta / (T : ℝ)))
          reference).mass a * (loss reference model a : ℝ)) ≤
          (Real.sqrt (beta T delta / (T : ℝ))) ^ 2) :
      (∑' a,
        (minimizer.actions (Real.sqrt (beta T delta / (T : ℝ)))
          reference).mass a *
          (robust_optimal_value framework model -
            robust_action_value framework reference a)) ≤
        fuzzy_decision_estimation_coefficient framework loss
          (Real.sqrt (beta T delta / (T : ℝ))) := by
    let r := Real.sqrt (beta T delta / (T : ℝ))
    let actions := minimizer.actions r reference
    let gap := ∑' a, actions.mass a *
      (robust_optimal_value framework model -
        robust_action_value framework reference a)
    let pointMu :
        subprobability_mass (robust_model Action Observation) :=
      { mass := fun m => if m = model then 1 else 0
        nonnegative := fun m => by split <;> positivity
        summable := by
          apply summable_of_finite_support
          apply (Set.finite_singleton model).subset
          intro m hm
          simp only [Function.mem_support] at hm
          by_cases hme : m = model
          · simpa [hme]
          · simp [hme] at hm
        total_mass_le_one := by simp }
    let S : Set ℝ := {value | ∃ mu :
        subprobability_mass (robust_model Action Observation),
      (∀ m, 0 < mu.mass m → m ∈ framework.hypothesisClass) ∧
      (∑' m, mu.mass m *
        (∑' a, actions.mass a * (loss reference m a : ℝ))) ≤ r ^ 2 ∧
      value = ∑' m, mu.mass m *
        (∑' a, actions.mass a *
          (robust_optimal_value framework m -
            robust_action_value framework reference a))}
    have hpoint : gap ∈ S := by
      refine ⟨pointMu, ?_, ?_, ?_⟩
      · intro m hm
        by_cases hme : m = model
        · simpa [hme] using hmodel
        · simp [pointMu, hme] at hm
      · simpa [pointMu, actions, r] using hx
      · simp [pointMu, gap]
    have hub : ∀ v ∈ S, v ≤ 1 := by
      rintro v ⟨mu, _, _, rfl⟩
      exact (havg_models mu
        (fun m => ∑' a, actions.mass a *
          (robust_optimal_value framework m -
            robust_action_value framework reference a))
        (fun m => hgap reference m actions)).2
    calc
      (∑' a, (minimizer.actions
          (Real.sqrt (beta T delta / (T : ℝ))) reference).mass a *
        (robust_optimal_value framework model -
          robust_action_value framework reference a)) =
          gap := rfl
      _ ≤ fuzzy_decision_objective framework loss r reference actions := by
        unfold fuzzy_decision_objective
        exact le_csSup ⟨1, hub⟩ hpoint
      _ = fuzzy_decision_estimation_coefficient_at framework loss r reference :=
        minimizer.attains r reference
      _ ≤ fuzzy_decision_estimation_coefficient framework loss r := by
        unfold fuzzy_decision_estimation_coefficient
        apply le_csSup
        · exact ⟨1, by
            rintro _ ⟨m, rfl⟩
            exact (hcoeff_at r m).2⟩
        · exact Set.mem_range_self reference
  let radius := Real.sqrt (beta T delta / (T : ℝ))
  let policy :=
    e2d_policy framework estimator loss minimizer beta T delta
  let dec := fuzzy_decision_estimation_coefficient framework loss radius
  let stepLoss : online_history Action Observation → ℝ := fun history =>
    ∑' a, (policy history).mass a *
      (loss (estimator.estimate history.length history) model a : ℝ)
  let stepGap : online_history Action Observation → ℝ := fun history =>
    ∑' a, (policy history).mass a *
      (robust_optimal_value framework model -
        robust_action_value framework
          (estimator.estimate history.length history) a)
  let decision : online_history Action Observation → ℝ := fun history =>
    List.rec 0 (fun _ tail total => total + stepGap tail) history
  have hpolicy (history : online_history Action Observation) :
      policy history =
        minimizer.actions radius
          (estimator.estimate history.length history) := by
    rfl
  have hstepLoss_nonneg (history : online_history Action Observation) :
      0 ≤ stepLoss history := by
    apply tsum_nonneg
    intro a
    exact mul_nonneg ((policy history).nonnegative a) (NNReal.coe_nonneg _)
  have hinaccuracy_nonneg (history : online_history Action Observation) :
      0 ≤ cumulative_inaccuracy estimator loss model policy history := by
    induction history with
    | nil => simp [cumulative_inaccuracy]
    | cons pair tail ih =>
        simp only [cumulative_inaccuracy]
        exact add_nonneg ih (hstepLoss_nonneg tail)
  have hdecision_pos (history : online_history Action Observation)
      (hr : 0 < radius ^ 2) :
      decision history ≤ dec *
        ((history.length : ℝ) +
          cumulative_inaccuracy estimator loss model policy history /
            radius ^ 2) := by
    induction history with
    | nil =>
        simp [decision, cumulative_inaccuracy]
    | cons pair tail ih =>
        have hs := hdecision
          (estimator.estimate tail.length tail) (by simpa [radius] using hr)
        have hs' : stepGap tail ≤ dec * (1 + stepLoss tail / radius ^ 2) := by
          simpa [stepGap, stepLoss, dec, radius, hpolicy] using hs
        calc
          decision (pair :: tail) = decision tail + stepGap tail := by
            rfl
          _ ≤ dec *
                ((tail.length : ℝ) +
                  cumulative_inaccuracy estimator loss model policy tail /
                    radius ^ 2) +
              dec * (1 + stepLoss tail / radius ^ 2) :=
            add_le_add ih hs'
          _ = dec *
              (((pair :: tail).length : ℝ) +
                cumulative_inaccuracy estimator loss model policy
                    (pair :: tail) / radius ^ 2) := by
            simp only [List.length_cons, Nat.cast_add, Nat.cast_one,
              cumulative_inaccuracy]
            ring
  have hdecision_zero (history : online_history Action Observation)
      (hr : radius ^ 2 = 0)
      (hz : cumulative_inaccuracy estimator loss model policy history = 0) :
      decision history ≤ dec * (history.length : ℝ) := by
    induction history with
    | nil =>
        simp [decision]
    | cons pair tail ih =>
        have htail_nonneg := hinaccuracy_nonneg tail
        have hstep_nonneg := hstepLoss_nonneg tail
        have hsum :
            cumulative_inaccuracy estimator loss model policy tail +
              stepLoss tail = 0 := by
          simpa only [cumulative_inaccuracy] using hz
        have htail_zero :
            cumulative_inaccuracy estimator loss model policy tail = 0 := by
          nlinarith
        have hstep_zero : stepLoss tail = 0 := by nlinarith
        have hstep_le : stepLoss tail ≤ radius ^ 2 := by
          rw [hr]
          exact le_of_eq hstep_zero
        have hs := hdecision_feasible
          (estimator.estimate tail.length tail)
          (by simpa [stepLoss, radius, hpolicy] using hstep_le)
        have hs' : stepGap tail ≤ dec := by
          simpa [stepGap, dec, radius, hpolicy] using hs
        calc
          decision (pair :: tail) = decision tail + stepGap tail := by rfl
          _ ≤ dec * (tail.length : ℝ) + dec :=
            add_le_add (ih htail_zero) hs'
          _ = dec * ((pair :: tail).length : ℝ) := by
            simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
            ring
  have hdecision_good (history : online_history Action Observation)
      (hlen : history.length = T)
      (hgood :
        cumulative_inaccuracy estimator loss model policy history ≤
          beta T delta) :
      decision history ≤ 2 * (T : ℝ) * dec := by
    have hbeta0 : 0 ≤ beta T delta :=
      (hinaccuracy_nonneg history).trans hgood
    have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
    have hratio : 0 ≤ beta T delta / (T : ℝ) :=
      div_nonneg hbeta0 (le_of_lt hTreal)
    have hr_sq : radius ^ 2 = beta T delta / (T : ℝ) := by
      simpa [radius] using Real.sq_sqrt hratio
    have hbeta_eq : beta T delta = (T : ℝ) * radius ^ 2 := by
      apply (div_left_inj' (ne_of_gt hTreal)).1
      rw [← hr_sq]
      field_simp
    by_cases hr0 : radius ^ 2 = 0
    · have hbeta_zero : beta T delta = 0 := by rw [hbeta_eq, hr0, mul_zero]
      have hinacc_zero :
          cumulative_inaccuracy estimator loss model policy history = 0 := by
        nlinarith [hinaccuracy_nonneg history]
      have hd := hdecision_zero history hr0 hinacc_zero
      rw [hlen] at hd
      have hdec0 : 0 ≤ dec := by simpa [dec, radius] using
        (hcoeff radius).1
      nlinarith [show (0 : ℝ) ≤ T by positivity]
    · have hrpos : 0 < radius ^ 2 := lt_of_le_of_ne (sq_nonneg radius)
        (Ne.symm hr0)
      have hd := hdecision_pos history hrpos
      have hquot :
          cumulative_inaccuracy estimator loss model policy history /
              radius ^ 2 ≤ (T : ℝ) := by
        apply (div_le_iff₀ hrpos).2
        rw [← hbeta_eq]
        exact hgood
      rw [hlen] at hd
      have hdec0 : 0 ≤ dec := by simpa [dec, radius] using
        (hcoeff radius).1
      nlinarith
  have hsummable_action (q : probability_mass Action) (f : Action → ℝ)
      (hf : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) :
      Summable (fun x => q.mass x * f x) := by
    let u : Action → ℝ := fun x => (f x + 1) / 2
    have hu (x) : u x ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp [u]
      constructor <;> linarith [(hf x).1, (hf x).2]
    have hsu : Summable (fun x => q.mass x * u x) := by
      let g : Action × Bool → ℝ := fun z =>
        if z.2 then q.mass z.1 * u z.1
        else q.mass z.1 * (1 - u z.1)
      have hg : Summable g := by
        apply (summable_prod_of_nonnegative_local (fun z => by
          dsimp [g]
          split
          · exact mul_nonneg (q.nonnegative z.1) (hu z.1).1
          · exact mul_nonneg (q.nonnegative z.1)
              (sub_nonneg.mpr (hu z.1).2))).2
        constructor
        · intro x
          exact Summable.of_finite
        · simpa [g, mul_sub] using q.summable
      have hi : Function.Injective (fun x : Action => (x, true)) := by
        intro x y hxy
        exact congrArg Prod.fst hxy
      exact hg.comp_injective hi
    rw [show (fun x => q.mass x * f x) =
        (fun x => 2 * (q.mass x * u x) - q.mass x) by
      funext x
      dsimp [u]
      ring]
    exact (hsu.mul_left 2).sub q.summable
  have henvavg (environment : online_environment Action Observation)
      (history : online_history Action Observation) (a : Action) :
      (∑' o, (environment history a).mass o *
        framework.reward a o) ∈ Set.Icc (0 : ℝ) 1 := by
    let q := environment history a
    have hn (o) : 0 ≤ q.mass o * framework.reward a o :=
      mul_nonneg (q.nonnegative o) (framework.reward_mem_unit a o).1
    have hle (o) : q.mass o * framework.reward a o ≤ q.mass o :=
      mul_le_of_le_one_right (q.nonnegative o)
        (framework.reward_mem_unit a o).2
    have hs : Summable (fun o => q.mass o * framework.reward a o) := by
      let f : Observation × Bool → ℝ := fun z =>
        if z.2 then q.mass z.1 * framework.reward a z.1
        else q.mass z.1 * (1 - framework.reward a z.1)
      have hf : Summable f := by
        apply (summable_prod_of_nonnegative_local (fun z => by
          dsimp [f]
          split
          · exact hn z.1
          · exact mul_nonneg (q.nonnegative z.1)
              (sub_nonneg.mpr (framework.reward_mem_unit a z.1).2))).2
        constructor
        · intro o
          exact Summable.of_finite
        · simpa [f, mul_sub] using q.summable
      let embed : Observation → Observation × Bool := fun o => (o, true)
      have hi : Function.Injective embed := by
        intro x y hxy
        exact congrArg Prod.fst hxy
      have hc : Summable (f ∘ embed) := hf.comp_injective hi
      have heq :
          (f ∘ embed) = fun o => q.mass o * framework.reward a o := by
        funext o
        rfl
      rw [← heq]
      exact hc
    constructor
    · exact tsum_nonneg hn
    · rw [← q.total_mass_one]
      exact hs.tsum_le_tsum hle q.summable
  let total (environment : online_environment Action Observation)
      (history : online_history Action Observation) :=
    decision history +
      cumulative_optimism framework estimator policy environment history
  have hstep_total (environment : online_environment Action Observation)
      (history : online_history Action Observation) :
      stepGap history +
          (∑' a, (policy history).mass a *
            (robust_action_value framework
                (estimator.estimate history.length history) a -
              ∑' o, (environment history a).mass o *
                framework.reward a o)) ∈ Set.Icc (-1 : ℝ) 1 := by
    let f : Action → ℝ := fun a =>
      robust_optimal_value framework model -
        robust_action_value framework
          (estimator.estimate history.length history) a
    let g : Action → ℝ := fun a =>
      robust_action_value framework
          (estimator.estimate history.length history) a -
        ∑' o, (environment history a).mass o * framework.reward a o
    have hf (a) : f a ∈ Set.Icc (-1 : ℝ) 1 := by
      dsimp [f]
      constructor <;> linarith [(hoptimal model).1, (hoptimal model).2,
        (haction (estimator.estimate history.length history) a).1,
        (haction (estimator.estimate history.length history) a).2]
    have hg (a) : g a ∈ Set.Icc (-1 : ℝ) 1 := by
      dsimp [g]
      constructor <;> linarith [
        (haction (estimator.estimate history.length history) a).1,
        (haction (estimator.estimate history.length history) a).2,
        (henvavg environment history a).1,
        (henvavg environment history a).2]
    have hfg (a) : f a + g a ∈ Set.Icc (-1 : ℝ) 1 := by
      dsimp [f, g]
      constructor <;> linarith [(hoptimal model).1, (hoptimal model).2,
        (henvavg environment history a).1,
        (henvavg environment history a).2]
    rw [show stepGap history +
          (∑' a, (policy history).mass a *
            (robust_action_value framework
                (estimator.estimate history.length history) a -
              ∑' o, (environment history a).mass o *
                framework.reward a o)) =
        ∑' a, (policy history).mass a * (f a + g a) by
      rw [← (hsummable_action (policy history) f hf).tsum_add
        (hsummable_action (policy history) g hg)]
      apply tsum_congr
      intro a
      dsimp [stepGap, f, g]
      ring]
    exact havg_action (policy history) (fun a => f a + g a) hfg
  have htotal_le (environment : online_environment Action Observation)
      (history : online_history Action Observation) :
      total environment history ≤ (history.length : ℝ) := by
    induction history with
    | nil =>
        simp [total, decision, cumulative_optimism]
    | cons pair tail ih =>
        calc
          total environment (pair :: tail) =
              total environment tail + stepGap tail +
                (∑' a, (policy tail).mass a *
                  (robust_action_value framework
                      (estimator.estimate tail.length tail) a -
                    ∑' o, (environment tail a).mass o *
                      framework.reward a o)) := by
                simp only [total, decision, cumulative_optimism]
                ring
          _ = total environment tail +
                (stepGap tail +
                  (∑' a, (policy tail).mass a *
                    (robust_action_value framework
                        (estimator.estimate tail.length tail) a -
                      ∑' o, (environment tail a).mass o *
                        framework.reward a o))) := by ring
          _ ≤ (tail.length : ℝ) + 1 :=
            add_le_add ih (hstep_total environment tail).2
          _ = ((pair :: tail).length : ℝ) := by
            simp
  have htotal_mem (environment : online_environment Action Observation)
      (history : online_history Action Observation) :
      total environment history ∈
        Set.Icc (-(history.length : ℝ)) (history.length : ℝ) := by
    induction history with
    | nil => simp [total, decision, cumulative_optimism]
    | cons pair tail ih =>
        have hrec : total environment (pair :: tail) =
            total environment tail +
              (stepGap tail +
                (∑' a, (policy tail).mass a *
                  (robust_action_value framework
                      (estimator.estimate tail.length tail) a -
                    ∑' o, (environment tail a).mass o *
                      framework.reward a o))) := by
          simp only [total, decision, cumulative_optimism]
          ring
        rw [hrec]
        constructor
        · norm_num [List.length_cons]
          linarith [ih.1, (hstep_total environment tail).1]
        · norm_num [List.length_cons]
          linarith [ih.2, (hstep_total environment tail).2]
  have hreward_history (history : online_history Action Observation) :
      (history.map (fun pair => framework.reward pair.1 pair.2)).sum ∈
        Set.Icc 0 (history.length : ℝ) := by
    induction history with
    | nil => simp
    | cons pair tail ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons,
          Nat.cast_add, Nat.cast_one]
        constructor
        · exact add_nonneg (framework.reward_mem_unit pair.1 pair.2).1 ih.1
        · linarith [(framework.reward_mem_unit pair.1 pair.2).2, ih.2]
  have hstep_balance (environment : online_environment Action Observation)
      (history : online_history Action Observation) :
      stepGap history +
          (∑' a, (policy history).mass a *
            (robust_action_value framework
                (estimator.estimate history.length history) a -
              ∑' o, (environment history a).mass o *
                framework.reward a o)) +
          (∑' a, (policy history).mass a *
            (∑' o, (environment history a).mass o *
              framework.reward a o)) =
        robust_optimal_value framework model := by
    let f : Action → ℝ := fun a =>
      robust_optimal_value framework model -
        robust_action_value framework
          (estimator.estimate history.length history) a
    let g : Action → ℝ := fun a =>
      robust_action_value framework
          (estimator.estimate history.length history) a -
        ∑' o, (environment history a).mass o * framework.reward a o
    let rwd : Action → ℝ := fun a =>
      ∑' o, (environment history a).mass o * framework.reward a o
    have hf (a) : f a ∈ Set.Icc (-1 : ℝ) 1 := by
      dsimp [f]
      constructor <;> linarith [(hoptimal model).1, (hoptimal model).2,
        (haction (estimator.estimate history.length history) a).1,
        (haction (estimator.estimate history.length history) a).2]
    have hg (a) : g a ∈ Set.Icc (-1 : ℝ) 1 := by
      dsimp [g]
      constructor <;> linarith [
        (haction (estimator.estimate history.length history) a).1,
        (haction (estimator.estimate history.length history) a).2,
        (henvavg environment history a).1,
        (henvavg environment history a).2]
    have hrwd (a) : rwd a ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor
      · linarith [(henvavg environment history a).1]
      · exact (henvavg environment history a).2
    have hsf := hsummable_action (policy history) f hf
    have hsg := hsummable_action (policy history) g hg
    have hsr := hsummable_action (policy history) rwd hrwd
    have hsumfg :
        (∑' a, (policy history).mass a * f a) +
            (∑' a, (policy history).mass a * g a) =
          ∑' a, (policy history).mass a * (f a + g a) := by
      rw [← hsf.tsum_add hsg]
      apply tsum_congr
      intro a
      ring
    have hfg_mem (a) : f a + g a ∈ Set.Icc (-1 : ℝ) 1 := by
      dsimp [f, g]
      constructor <;> linarith [(hoptimal model).1,
        (hoptimal model).2, (henvavg environment history a).1,
        (henvavg environment history a).2]
    have hsfg := hsummable_action (policy history)
      (fun a => f a + g a) hfg_mem
    have hsumall :
        (∑' a, (policy history).mass a * (f a + g a)) +
            (∑' a, (policy history).mass a * rwd a) =
          ∑' a, (policy history).mass a * ((f a + g a) + rwd a) := by
      rw [← hsfg.tsum_add hsr]
      apply tsum_congr
      intro a
      ring
    change (∑' a, (policy history).mass a * f a) +
        (∑' a, (policy history).mass a * g a) +
        (∑' a, (policy history).mass a * rwd a) =
          robust_optimal_value framework model
    rw [hsumfg, hsumall]
    have hpoint :
        (fun a => (policy history).mass a * ((f a + g a) + rwd a)) =
          (fun a => (policy history).mass a *
            robust_optimal_value framework model) := by
      funext a
      dsimp [f, g, rwd]
      ring
    rw [hpoint]
    rw [(policy history).summable.tsum_mul_right
      (robust_optimal_value framework model)]
    rw [(policy history).total_mass_one]
    ring
  have henvsummable (environment : online_environment Action Observation)
      (history : online_history Action Observation) (a : Action) :
      Summable (fun o => (environment history a).mass o *
        framework.reward a o) := by
    let q := environment history a
    let f : Observation × Bool → ℝ := fun z =>
      if z.2 then q.mass z.1 * framework.reward a z.1
      else q.mass z.1 * (1 - framework.reward a z.1)
    have hf : Summable f := by
      apply (summable_prod_of_nonnegative_local (fun z => by
        dsimp [f]
        split
        · exact mul_nonneg (q.nonnegative z.1)
            (framework.reward_mem_unit a z.1).1
        · exact mul_nonneg (q.nonnegative z.1)
            (sub_nonneg.mpr (framework.reward_mem_unit a z.1).2))).2
      constructor
      · intro o
        exact Summable.of_finite
      · simpa [f, mul_sub] using q.summable
    let embed : Observation → Observation × Bool := fun o => (o, true)
    have hi : Function.Injective embed := by
      intro x y hxy
      exact congrArg Prod.fst hxy
    have hc : Summable (f ∘ embed) := hf.comp_injective hi
    have heq : (f ∘ embed) =
        (fun o => (environment history a).mass o *
          framework.reward a o) := by
      funext o
      rfl
    rw [← heq]
    exact hc
  have hpair_data (environment : online_environment Action Observation)
      (history : online_history Action Observation) (A : ℝ) :
      Summable (fun pair : Action × Observation =>
        trajectory_probability policy environment history *
          (policy history).mass pair.1 *
          (environment history pair.1).mass pair.2 *
          (A + stepGap history +
            (∑' a, (policy history).mass a *
              (robust_action_value framework
                  (estimator.estimate history.length history) a -
                ∑' o, (environment history a).mass o *
                  framework.reward a o)) +
            framework.reward pair.1 pair.2)) ∧
      (∑' pair : Action × Observation,
        trajectory_probability policy environment history *
          (policy history).mass pair.1 *
          (environment history pair.1).mass pair.2 *
          (A + stepGap history +
            (∑' a, (policy history).mass a *
              (robust_action_value framework
                  (estimator.estimate history.length history) a -
                ∑' o, (environment history a).mass o *
                  framework.reward a o)) +
            framework.reward pair.1 pair.2)) =
        trajectory_probability policy environment history *
          (A + robust_optimal_value framework model) := by
    let K := stepGap history +
      (∑' a, (policy history).mass a *
        (robust_action_value framework
            (estimator.estimate history.length history) a -
          ∑' o, (environment history a).mass o *
            framework.reward a o))
    let F : Action × Observation → ℝ := fun pair =>
        trajectory_probability policy environment history *
          (policy history).mass pair.1 *
          (environment history pair.1).mass pair.2 *
          (A + K + framework.reward pair.1 pair.2)
    have hbase : Summable (fun pair : Action × Observation =>
        trajectory_probability policy environment history *
          (policy history).mass pair.1 *
          (environment history pair.1).mass pair.2) := by
      apply (summable_prod_of_nonnegative_local (fun pair =>
        mul_nonneg
          (mul_nonneg (trajectory_probability_nonnegative _ _ _)
            ((policy history).nonnegative pair.1))
          ((environment history pair.1).nonnegative pair.2))).2
      constructor
      · intro a
        simpa [mul_assoc] using
          (environment history a).summable.mul_left
            (trajectory_probability policy environment history *
              (policy history).mass a)
      · have heq : (fun a => ∑' o,
            trajectory_probability policy environment history *
              (policy history).mass (a, o).1 *
              (environment history (a, o).1).mass (a, o).2) =
            (fun a => trajectory_probability policy environment history *
              (policy history).mass a) := by
          funext a
          rw [show (fun o =>
              trajectory_probability policy environment history *
                (policy history).mass a *
                (environment history a).mass o) =
              (fun o => (trajectory_probability policy environment history *
                (policy history).mass a) *
                (environment history a).mass o) by rfl]
          rw [(environment history a).summable.tsum_mul_left]
          rw [(environment history a).total_mass_one]
          ring
        rw [heq]
        exact (policy history).summable.mul_left
          (trajectory_probability policy environment history)
    have hreward : Summable (fun pair : Action × Observation =>
        trajectory_probability policy environment history *
          (policy history).mass pair.1 *
          (environment history pair.1).mass pair.2 *
          framework.reward pair.1 pair.2) := by
      apply (summable_prod_of_nonnegative_local (fun pair =>
        mul_nonneg
          (mul_nonneg
            (mul_nonneg (trajectory_probability_nonnegative _ _ _)
              ((policy history).nonnegative pair.1))
            ((environment history pair.1).nonnegative pair.2))
          (framework.reward_mem_unit pair.1 pair.2).1)).2
      constructor
      · intro a
        simpa [mul_assoc] using
          (henvsummable environment history a).mul_left
            (trajectory_probability policy environment history *
              (policy history).mass a)
      · have hR : ∀ a : Action,
            (∑' o, (environment history a).mass o *
              framework.reward a o) ∈ Set.Icc (-1 : ℝ) 1 := by
          intro a
          constructor
          · linarith [(henvavg environment history a).1]
          · exact (henvavg environment history a).2
        have heq : (fun a => ∑' o,
            trajectory_probability policy environment history *
              (policy history).mass (a, o).1 *
                (environment history (a, o).1).mass (a, o).2 *
              framework.reward (a, o).1 (a, o).2) =
            (fun a => trajectory_probability policy environment history *
              ((policy history).mass a *
                (∑' o, (environment history a).mass o *
                  framework.reward a o))) := by
          funext a
          rw [show (fun o =>
              trajectory_probability policy environment history *
                (policy history).mass a *
                  (environment history a).mass o *
                framework.reward a o) =
              (fun o =>
                (trajectory_probability policy environment history *
                  (policy history).mass a) *
                  ((environment history a).mass o *
                    framework.reward a o)) by
            funext o
            ring]
          rw [(henvsummable environment history a).tsum_mul_left]
          ring
        rw [heq]
        exact (hsummable_action (policy history)
          (fun a => ∑' o, (environment history a).mass o *
            framework.reward a o) hR).mul_left
          (trajectory_probability policy environment history)
    have hsF : Summable F := by
      have hc := hbase.mul_right (A + K)
      rw [show F = fun pair =>
          (trajectory_probability policy environment history *
            (policy history).mass pair.1 *
            (environment history pair.1).mass pair.2) * (A + K) +
          trajectory_probability policy environment history *
            (policy history).mass pair.1 *
            (environment history pair.1).mass pair.2 *
            framework.reward pair.1 pair.2 by
        funext pair
        dsimp [F]
        ring]
      exact hc.add hreward
    have hs : Summable (fun pair : Action × Observation =>
        trajectory_probability policy environment history *
          (policy history).mass pair.1 *
          (environment history pair.1).mass pair.2 *
          (A + K + framework.reward pair.1 pair.2)) := by
      exact hsF
    have hbase_sum :
        (∑' pair : Action × Observation,
          trajectory_probability policy environment history *
            (policy history).mass pair.1 *
            (environment history pair.1).mass pair.2) =
          trajectory_probability policy environment history := by
      rw [hbase.tsum_prod]
      have heq : (fun a => ∑' o,
          trajectory_probability policy environment history *
            (policy history).mass (a, o).1 *
            (environment history (a, o).1).mass (a, o).2) =
          (fun a => trajectory_probability policy environment history *
            (policy history).mass a) := by
        funext a
        rw [show (fun o =>
            trajectory_probability policy environment history *
              (policy history).mass a *
              (environment history a).mass o) =
            (fun o =>
              (trajectory_probability policy environment history *
                (policy history).mass a) *
                (environment history a).mass o) by rfl]
        rw [(environment history a).summable.tsum_mul_left]
        rw [(environment history a).total_mass_one]
        ring
      rw [heq]
      rw [(policy history).summable.tsum_mul_left]
      rw [(policy history).total_mass_one]
      ring
    have hreward_sum :
        (∑' pair : Action × Observation,
          trajectory_probability policy environment history *
            (policy history).mass pair.1 *
            (environment history pair.1).mass pair.2 *
            framework.reward pair.1 pair.2) =
          trajectory_probability policy environment history *
            (∑' a, (policy history).mass a *
              ∑' o, (environment history a).mass o *
                framework.reward a o) := by
      rw [hreward.tsum_prod]
      have heq : (fun a => ∑' o,
          trajectory_probability policy environment history *
            (policy history).mass (a, o).1 *
              (environment history (a, o).1).mass (a, o).2 *
            framework.reward (a, o).1 (a, o).2) =
          (fun a => trajectory_probability policy environment history *
            ((policy history).mass a *
              (∑' o, (environment history a).mass o *
                framework.reward a o))) := by
        funext a
        rw [show (fun o =>
            trajectory_probability policy environment history *
              (policy history).mass a *
                (environment history a).mass o *
              framework.reward a o) =
            (fun o =>
              (trajectory_probability policy environment history *
                (policy history).mass a) *
                ((environment history a).mass o *
                  framework.reward a o)) by
          funext o
          ring]
        rw [(henvsummable environment history a).tsum_mul_left]
        ring
      rw [heq]
      have hR : ∀ a : Action,
          (∑' o, (environment history a).mass o *
            framework.reward a o) ∈ Set.Icc (-1 : ℝ) 1 := by
        intro a
        constructor
        · linarith [(henvavg environment history a).1]
        · exact (henvavg environment history a).2
      have houter := hsummable_action (policy history)
        (fun a => ∑' o, (environment history a).mass o *
          framework.reward a o) hR
      rw [houter.tsum_mul_left]
    have hsplit : F = (fun pair : Action × Observation =>
        (trajectory_probability policy environment history *
          (policy history).mass pair.1 *
          (environment history pair.1).mass pair.2) * (A + K) +
        trajectory_probability policy environment history *
          (policy history).mass pair.1 *
          (environment history pair.1).mass pair.2 *
          framework.reward pair.1 pair.2) := by
      funext pair
      dsimp [F]
      ring
    constructor
    · rw [show (fun pair : Action × Observation =>
          trajectory_probability policy environment history *
            (policy history).mass pair.1 *
            (environment history pair.1).mass pair.2 *
            (A + stepGap history +
              (∑' a, (policy history).mass a *
                (robust_action_value framework
                    (estimator.estimate history.length history) a -
                  ∑' o, (environment history a).mass o *
                    framework.reward a o)) +
              framework.reward pair.1 pair.2)) =
          (fun pair =>
            trajectory_probability policy environment history *
              (policy history).mass pair.1 *
              (environment history pair.1).mass pair.2 *
              (A + K + framework.reward pair.1 pair.2)) by
        funext pair
        dsimp [K]
        ring]
      exact hs
    · rw [show (fun pair : Action × Observation =>
          trajectory_probability policy environment history *
            (policy history).mass pair.1 *
            (environment history pair.1).mass pair.2 *
            (A + stepGap history +
              (∑' a, (policy history).mass a *
                (robust_action_value framework
                    (estimator.estimate history.length history) a -
                  ∑' o, (environment history a).mass o *
                    framework.reward a o)) +
              framework.reward pair.1 pair.2)) = F by
        funext pair
        dsimp [F, K]
        ring]
      rw [hsplit]
      rw [(hbase.mul_right (A + K)).tsum_add hreward]
      rw [hbase.tsum_mul_right, hbase_sum, hreward_sum]
      dsimp [K]
      linear_combination trajectory_probability policy environment history *
        (hstep_balance environment history)
  have hpair_summable (environment : online_environment Action Observation)
      (history : online_history Action Observation) (A : ℝ) :
      Summable (fun pair : Action × Observation =>
        trajectory_probability policy environment history *
          (policy history).mass pair.1 *
          (environment history pair.1).mass pair.2 *
          (A + stepGap history +
            (∑' a, (policy history).mass a *
              (robust_action_value framework
                  (estimator.estimate history.length history) a -
                ∑' o, (environment history a).mass o *
                  framework.reward a o)) +
            framework.reward pair.1 pair.2)) :=
    (hpair_data environment history A).1
  have hpair_sum (environment : online_environment Action Observation)
      (history : online_history Action Observation) (A : ℝ) :
      (∑' pair : Action × Observation,
        trajectory_probability policy environment history *
          (policy history).mass pair.1 *
          (environment history pair.1).mass pair.2 *
          (A + stepGap history +
            (∑' a, (policy history).mass a *
              (robust_action_value framework
                  (estimator.estimate history.length history) a -
                ∑' o, (environment history a).mass o *
                  framework.reward a o)) +
            framework.reward pair.1 pair.2)) =
        trajectory_probability policy environment history *
          (A + robust_optimal_value framework model) :=
    (hpair_data environment history A).2
  have htuple_data (environment : online_environment Action Observation) :
      ∀ n : ℕ,
      Summable (fun x : Fin n → Action × Observation =>
        trajectory_probability policy environment (List.ofFn x) *
          (total environment (List.ofFn x) +
            ((List.ofFn x).map
              (fun pair => framework.reward pair.1 pair.2)).sum)) ∧
      (∑' x : Fin n → Action × Observation,
        trajectory_probability policy environment (List.ofFn x) *
          (total environment (List.ofFn x) +
            ((List.ofFn x).map
              (fun pair => framework.reward pair.1 pair.2)).sum)) =
        (n : ℝ) * robust_optimal_value framework model := by
    intro n
    induction n with
    | zero =>
        constructor
        · exact Summable.of_finite
        · simp [trajectory_probability, total, decision,
            cumulative_optimism]
    | succ n ih =>
        let e := (Equiv.prodComm (Fin n → Action × Observation)
          (Action × Observation)).trans
            (Fin.consEquiv (fun _ : Fin (n + 1) =>
              Action × Observation))
        let G : (Fin n → Action × Observation) ×
            (Action × Observation) → ℝ := fun z =>
          trajectory_probability policy environment (List.ofFn z.1) *
            (policy (List.ofFn z.1)).mass z.2.1 *
            (environment (List.ofFn z.1) z.2.1).mass z.2.2 *
            (total environment (List.ofFn z.1) +
              ((List.ofFn z.1).map
                (fun pair => framework.reward pair.1 pair.2)).sum +
              stepGap (List.ofFn z.1) +
              (∑' a, (policy (List.ofFn z.1)).mass a *
                (robust_action_value framework
                    (estimator.estimate (List.ofFn z.1).length
                      (List.ofFn z.1)) a -
                  ∑' o, (environment (List.ofFn z.1) a).mass o *
                    framework.reward a o)) +
              framework.reward z.2.1 z.2.2)
        have hinner (tail : Fin n → Action × Observation) :
            Summable (fun pair : Action × Observation => G (tail, pair)) := by
          simpa [G, add_assoc] using hpair_summable environment
            (List.ofFn tail)
            (total environment (List.ofFn tail) +
              ((List.ofFn tail).map
                (fun pair => framework.reward pair.1 pair.2)).sum)
        have hinner_sum : (fun tail : Fin n → Action × Observation =>
            ∑' pair : Action × Observation, G (tail, pair)) =
            (fun tail =>
              trajectory_probability policy environment (List.ofFn tail) *
                (total environment (List.ofFn tail) +
                  ((List.ofFn tail).map
                    (fun pair => framework.reward pair.1 pair.2)).sum +
                  robust_optimal_value framework model)) := by
          funext tail
          simpa [G, add_assoc] using hpair_sum environment
            (List.ofFn tail)
            (total environment (List.ofFn tail) +
              ((List.ofFn tail).map
                (fun pair => framework.reward pair.1 pair.2)).sum)
        have houter : Summable (fun tail : Fin n → Action × Observation =>
            ∑' pair : Action × Observation, G (tail, pair)) := by
          rw [hinner_sum]
          rw [show (fun tail : Fin n → Action × Observation =>
              trajectory_probability policy environment (List.ofFn tail) *
                (total environment (List.ofFn tail) +
                  ((List.ofFn tail).map
                    (fun pair => framework.reward pair.1 pair.2)).sum +
                  robust_optimal_value framework model)) =
              (fun tail =>
                trajectory_probability policy environment (List.ofFn tail) *
                  (total environment (List.ofFn tail) +
                    ((List.ofFn tail).map
                      (fun pair => framework.reward pair.1 pair.2)).sum) +
                trajectory_probability policy environment (List.ofFn tail) *
                  robust_optimal_value framework model) by
            funext tail
            ring]
          exact ih.1.add
            (((trajectory_probability_tuple_summable policy environment n).1
              ).mul_right (robust_optimal_value framework model))
        let M : (Fin n → Action × Observation) ×
            (Action × Observation) → ℝ := fun z =>
          trajectory_probability policy environment (List.ofFn z.1) *
            (policy (List.ofFn z.1)).mass z.2.1 *
            (environment (List.ofFn z.1) z.2.1).mass z.2.2
        have hM_nonneg (z) : 0 ≤ M z := by
          exact mul_nonneg
            (mul_nonneg (trajectory_probability_nonnegative _ _ _)
              ((policy (List.ofFn z.1)).nonnegative z.2.1))
            ((environment (List.ofFn z.1) z.2.1).nonnegative z.2.2)
        have hM_inner (tail : Fin n → Action × Observation) :
            Summable (fun pair : Action × Observation => M (tail, pair)) := by
          apply (summable_prod_of_nonnegative_local
            (fun pair => hM_nonneg (tail, pair))).2
          constructor
          · intro action
            simpa [M, mul_assoc] using
              (environment (List.ofFn tail) action).summable.mul_left
                (trajectory_probability policy environment (List.ofFn tail) *
                  (policy (List.ofFn tail)).mass action)
          · have heq : (fun action => ∑' observation,
                M (tail, (action, observation))) =
                (fun action =>
                  trajectory_probability policy environment (List.ofFn tail) *
                    (policy (List.ofFn tail)).mass action) := by
              funext action
              dsimp [M]
              rw [(environment (List.ofFn tail) action).summable.tsum_mul_left]
              rw [(environment (List.ofFn tail) action).total_mass_one]
              ring
            rw [heq]
            exact (policy (List.ofFn tail)).summable.mul_left
              (trajectory_probability policy environment (List.ofFn tail))
        have hM_inner_sum : (fun tail : Fin n → Action × Observation =>
            ∑' pair : Action × Observation, M (tail, pair)) =
            (fun tail => trajectory_probability policy environment
              (List.ofFn tail)) := by
          funext tail
          rw [(hM_inner tail).tsum_prod]
          have heq : (fun action => ∑' observation,
              M (tail, (action, observation))) =
              (fun action =>
                trajectory_probability policy environment (List.ofFn tail) *
                  (policy (List.ofFn tail)).mass action) := by
            funext action
            dsimp [M]
            rw [(environment (List.ofFn tail) action).summable.tsum_mul_left]
            rw [(environment (List.ofFn tail) action).total_mass_one]
            ring
          rw [heq]
          rw [(policy (List.ofFn tail)).summable.tsum_mul_left]
          rw [(policy (List.ofFn tail)).total_mass_one]
          ring
        have hM : Summable M := by
          apply (summable_prod_of_nonnegative_local hM_nonneg).2
          constructor
          · exact hM_inner
          · rw [hM_inner_sum]
            exact (trajectory_probability_tuple_summable
              policy environment n).1
        let GS : (Fin n → Action × Observation) ×
            (Action × Observation) → ℝ := fun z =>
          G z + M z * (2 * ((n + 1 : ℕ) : ℝ))
        have hGS_nonneg (z) : 0 ≤ GS z := by
          rw [show GS z =
              trajectory_probability policy environment
                  (z.2 :: List.ofFn z.1) *
                (total environment (z.2 :: List.ofFn z.1) +
                  ((z.2 :: List.ofFn z.1).map
                    (fun pair => framework.reward pair.1 pair.2)).sum +
                  2 * ((n + 1 : ℕ) : ℝ)) by
            dsimp [GS, G, M, total, decision, cumulative_optimism]
            simp only [trajectory_probability, List.map_cons, List.sum_cons]
            ring]
          apply mul_nonneg (trajectory_probability_nonnegative _ _ _)
          have ht := htotal_mem environment (z.2 :: List.ofFn z.1)
          have hr := hreward_history (z.2 :: List.ofFn z.1)
          simp only [List.length_cons, List.length_ofFn, Nat.cast_add,
            Nat.cast_one] at ht hr
          have hn : 0 ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
          calc
            0 ≤ ((n + 1 : ℕ) : ℝ) := hn
            _ = -((n + 1 : ℕ) : ℝ) + 0 +
                2 * ((n + 1 : ℕ) : ℝ) := by ring
            _ ≤ total environment (z.2 :: List.ofFn z.1) +
                ((z.2 :: List.ofFn z.1).map
                  (fun pair => framework.reward pair.1 pair.2)).sum +
                2 * ((n + 1 : ℕ) : ℝ) := by
              have hb := add_le_add_right (add_le_add ht.1 hr.1)
                (2 * ((n + 1 : ℕ) : ℝ))
              norm_num [Nat.cast_add, Nat.cast_one] at hb ⊢
              nlinarith [hb]
        have hGS_inner (tail : Fin n → Action × Observation) :
            Summable (fun pair : Action × Observation => GS (tail, pair)) := by
          exact (hinner tail).add
            ((hM_inner tail).mul_right (2 * ((n + 1 : ℕ) : ℝ)))
        have hGS_inner_sum :
            (fun tail : Fin n → Action × Observation =>
              ∑' pair : Action × Observation, GS (tail, pair)) =
            (fun tail =>
              (∑' pair : Action × Observation, G (tail, pair)) +
                trajectory_probability policy environment (List.ofFn tail) *
                  (2 * ((n + 1 : ℕ) : ℝ))) := by
          funext tail
          rw [(hinner tail).tsum_add
            ((hM_inner tail).mul_right (2 * ((n + 1 : ℕ) : ℝ)))]
          rw [(hM_inner tail).tsum_mul_right]
          rw [congrFun hM_inner_sum tail]
        have hGS_outer : Summable (fun tail : Fin n →
            Action × Observation =>
            ∑' pair : Action × Observation, GS (tail, pair)) := by
          rw [hGS_inner_sum]
          exact houter.add
            (((trajectory_probability_tuple_summable policy environment n).1
              ).mul_right (2 * ((n + 1 : ℕ) : ℝ)))
        have hGS : Summable GS := by
          apply (summable_prod_of_nonnegative_local hGS_nonneg).2
          exact ⟨hGS_inner, hGS_outer⟩
        have hG : Summable G := by
          rw [show G = (fun z =>
              GS z - M z * (2 * ((n + 1 : ℕ) : ℝ))) by
            funext z
            dsimp [GS]
            ring]
          exact hGS.sub
            (hM.mul_right (2 * ((n + 1 : ℕ) : ℝ)))
        let Q : (Fin (n + 1) → Action × Observation) → ℝ := fun x =>
            trajectory_probability policy environment (List.ofFn x) *
              (total environment (List.ofFn x) +
                ((List.ofFn x).map
                  (fun pair => framework.reward pair.1 pair.2)).sum)
        have he_list (z : (Fin n → Action × Observation) ×
            (Action × Observation)) :
            List.ofFn (e z) = z.2 :: List.ofFn z.1 := by
          simp [e, List.ofFn_cons]
        have hcompose : Q ∘ e = G := by
          funext z
          dsimp [Q, Function.comp_def]
          rw [he_list z]
          simp only [trajectory_probability, total,
            decision, cumulative_optimism, List.map_cons, List.sum_cons]
          dsimp [G]
          ring
        have hsucc : Summable Q := by
          apply e.summable_iff.mp
          rw [hcompose]
          exact hG
        constructor
        · exact hsucc
        · change (∑' x, Q x) = _
          rw [← e.tsum_eq]
          change (∑' z, (Q ∘ e) z) = _
          rw [hcompose]
          rw [hG.tsum_prod]
          rw [hinner_sum]
          rw [show (fun tail : Fin n → Action × Observation =>
              trajectory_probability policy environment (List.ofFn tail) *
                (total environment (List.ofFn tail) +
                  ((List.ofFn tail).map
                    (fun pair => framework.reward pair.1 pair.2)).sum +
                  robust_optimal_value framework model)) =
              (fun tail =>
                trajectory_probability policy environment (List.ofFn tail) *
                  (total environment (List.ofFn tail) +
                    ((List.ofFn tail).map
                      (fun pair => framework.reward pair.1 pair.2)).sum) +
                trajectory_probability policy environment (List.ofFn tail) *
                  robust_optimal_value framework model) by
            funext tail
            ring]
          rw [ih.1.tsum_add
            (((trajectory_probability_tuple_summable policy environment n).1
              ).mul_right (robust_optimal_value framework model))]
          rw [ih.2,
            ((trajectory_probability_tuple_summable policy environment n).1
              ).tsum_mul_right,
            (trajectory_probability_tuple_summable policy environment n).2]
          norm_num [Nat.cast_add, Nat.cast_one]
          ring
  have hsummable_weighted
      (q f : (Fin T → Action × Observation) → ℝ) (C : ℝ)
      (hq : Summable q) (hq_nonneg : ∀ x, 0 ≤ q x)
      (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) C) :
      Summable (fun x => q x * f x) := by
    let g : (Fin T → Action × Observation) × Bool → ℝ := fun z =>
      if z.2 then q z.1 * f z.1 else q z.1 * (C - f z.1)
    have hg : Summable g := by
      apply (summable_prod_of_nonnegative_local (fun z => by
        dsimp [g]
        split
        · exact mul_nonneg (hq_nonneg z.1) (hf z.1).1
        · exact mul_nonneg (hq_nonneg z.1)
            (sub_nonneg.mpr (hf z.1).2))).2
      constructor
      · intro x
        exact Summable.of_finite
      · simpa [g, mul_sub] using hq.mul_right C
    let embed : (Fin T → Action × Observation) →
        (Fin T → Action × Observation) × Bool := fun x => (x, true)
    have hi : Function.Injective embed := by
      intro x y hxy
      exact congrArg Prod.fst hxy
    have hc : Summable (g ∘ embed) := hg.comp_injective hi
    have heq : (g ∘ embed) = (fun x => q x * f x) := by
      funext x
      rfl
    rw [← heq]
    exact hc
  have hreward_tuple (environment : online_environment Action Observation) :
      Summable (fun x : Fin T → Action × Observation =>
        trajectory_probability policy environment (List.ofFn x) *
          ((List.ofFn x).map
            (fun pair => framework.reward pair.1 pair.2)).sum) := by
    apply hsummable_weighted
        (fun x : Fin T → Action × Observation =>
          trajectory_probability policy environment (List.ofFn x))
        (fun x =>
          ((List.ofFn x).map
            (fun pair : Action × Observation =>
              framework.reward pair.1 pair.2)).sum)
        (T : ℝ)
    · exact (trajectory_probability_tuple_summable policy environment T).1
    · intro x
      exact trajectory_probability_nonnegative policy environment (List.ofFn x)
    · intro x
      simpa using hreward_history (List.ofFn x)
  have htotal_tuple (environment : online_environment Action Observation) :
      Summable (fun x : Fin T → Action × Observation =>
        trajectory_probability policy environment (List.ofFn x) *
          total environment (List.ofFn x)) := by
    have hs := (htuple_data environment T).1.sub
      (hreward_tuple environment)
    simpa only [mul_add, add_sub_cancel_right] using hs
  have hreward_identity
      (environment : online_environment Action Observation) :
      expected_cumulative_reward framework policy environment T =
        ∑' x : Fin T → Action × Observation,
          trajectory_probability policy environment (List.ofFn x) *
            ((List.ofFn x).map
              (fun pair => framework.reward pair.1 pair.2)).sum := by
    let f : (Fin T → Action × Observation) → ℝ := fun x =>
      trajectory_probability policy environment (List.ofFn x) *
        ((List.ofFn x).map
          (fun pair => framework.reward pair.1 pair.2)).sum
    let embed : (Fin T → Action × Observation) →
        (Σ n, Fin n → Action × Observation) := fun x => ⟨T, x⟩
    have hi : Function.Injective embed := by
      intro x y hxy
      exact eq_of_heq (Sigma.mk.inj_iff.mp hxy).2
    unfold expected_cumulative_reward
    rw [← (List.equivSigmaTuple
      (α := Action × Observation)).symm.tsum_eq]
    simp only [List.equivSigmaTuple_symm_apply, List.length_ofFn]
    have heq : (fun c : Σ n, Fin n → Action × Observation =>
        if c.1 = T then
          trajectory_probability policy environment (List.ofFn c.2) *
            ((List.ofFn c.2).map
              (fun pair => framework.reward pair.1 pair.2)).sum
        else 0) = Function.extend embed f 0 := by
      funext c
      rcases c with ⟨n, x⟩
      by_cases hn : n = T
      · subst n
        simp [embed, f, hi]
      · rw [if_neg hn]
        symm
        apply Function.extend_apply'
        rintro ⟨y, hy⟩
        exact hn (congrArg Sigma.fst hy).symm
    rw [heq, tsum_extend_zero hi]
  have htotal_identity
      (environment : online_environment Action Observation) :
      (T : ℝ) * robust_optimal_value framework model -
          expected_cumulative_reward framework policy environment T =
        ∑' x : Fin T → Action × Observation,
          trajectory_probability policy environment (List.ofFn x) *
            total environment (List.ofFn x) := by
    have hsum := (htotal_tuple environment).tsum_add
      (hreward_tuple environment)
    have hsum' :
        (∑' x : Fin T → Action × Observation,
          trajectory_probability policy environment (List.ofFn x) *
            (total environment (List.ofFn x) +
              ((List.ofFn x).map
                (fun pair => framework.reward pair.1 pair.2)).sum)) =
        (∑' x : Fin T → Action × Observation,
          trajectory_probability policy environment (List.ofFn x) *
            total environment (List.ofFn x)) +
        ∑' x : Fin T → Action × Observation,
          trajectory_probability policy environment (List.ofFn x) *
            ((List.ofFn x).map
              (fun pair => framework.reward pair.1 pair.2)).sum := by
      simpa only [mul_add] using hsum
    rw [(htuple_data environment T).2] at hsum'
    rw [hreward_identity environment]
    exact (sub_eq_iff_eq_add).2 hsum'
  have henvironment_bound
      (environment : online_environment Action Observation)
      (hconsistent : environment_consistent environment model) :
      (∑' x : Fin T → Action × Observation,
        trajectory_probability policy environment (List.ofFn x) *
          total environment (List.ofFn x)) ≤
        2 * (T : ℝ) * dec + alpha T delta +
          2 * (T : ℝ) * delta := by
    have hdec_nonneg : 0 ≤ dec := by
      exact (hcoeff radius).1
    exact e2d_total_expectation_bound_local framework T hT delta hdelta
      loss minimizer estimator beta alpha hbeta halpha model hmodel dec
      decision total
      (fun history hlength hgood =>
        hdecision_good history hlength hgood)
      (fun _ _ => rfl) htotal_le htotal_tuple hdec_nonneg
      environment hconsistent
  unfold e2d_regret
  let S : Set ℝ := {value | ∃ environment :
      online_environment Action Observation,
    environment_consistent environment model ∧
    value = (T : ℝ) * robust_optimal_value framework model -
      expected_cumulative_reward framework policy environment T}
  change sSup S ≤ _
  let chosen : (action : Action) →
      {p // p ∈ (model action).carrier} := fun action =>
    ⟨Classical.choose (model action).nonempty,
      Classical.choose_spec (model action).nonempty⟩
  let environment : online_environment Action Observation :=
    fun _ action =>
      { mass := (chosen action).1
        nonnegative := (model action).mass_nonnegative
          (chosen action).1 (chosen action).2
        summable := (model action).mass_summable
          (chosen action).1 (chosen action).2
        total_mass_one := (model action).total_mass_one
          (chosen action).1 (chosen action).2 }
  have hconsistent : environment_consistent environment model := by
    intro history action
    exact (chosen action).2
  have hS : S.Nonempty := by
    refine ⟨(T : ℝ) * robust_optimal_value framework model -
      expected_cumulative_reward framework policy environment T, ?_⟩
    exact ⟨environment, hconsistent, rfl⟩
  apply csSup_le hS
  intro value hvalue
  rcases hvalue with ⟨environment, hconsistent, rfl⟩
  rw [htotal_identity environment]
  simpa only [dec, radius] using
    henvironment_bound environment hconsistent

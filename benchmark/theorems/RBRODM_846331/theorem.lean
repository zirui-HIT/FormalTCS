import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.NNReal.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Defs

set_option linter.all false
set_option maxHeartbeats 500000

structure imprecise_belief (Observation : Type*) where
  carrier : Set (Observation → ℝ)
  nonempty : carrier.Nonempty
  mass_nonnegative : ∀ p ∈ carrier, ∀ o, 0 ≤ p o
  mass_summable : ∀ p ∈ carrier, Summable p
  total_mass_one : ∀ p ∈ carrier, ∑' o, p o = 1
  isClosed : IsClosed carrier
  convex : Convex ℝ carrier

abbrev robust_model (Action Observation : Type*) :=
  Action → imprecise_belief Observation

abbrev online_history (Action Observation : Type*) :=
  List (Action × Observation)

structure online_estimation_oracle (Action Observation : Type*) where
  estimate : ℕ → online_history Action Observation → robust_model Action Observation

abbrev robust_loss (Action Observation : Type*) :=
  robust_model Action Observation → robust_model Action Observation → Action → NNReal

structure probability_mass (X : Type*) where
  mass : X → ℝ
  nonnegative : ∀ x, 0 ≤ mass x
  summable : Summable mass
  total_mass_one : ∑' x, mass x = 1

structure subprobability_mass (X : Type*) where
  mass : X → ℝ
  nonnegative : ∀ x, 0 ≤ mass x
  summable : Summable mass
  total_mass_le_one : ∑' x, mass x ≤ 1

structure robust_online_decision_framework (Action Observation : Type*) where
  reward : Action → Observation → ℝ
  reward_mem_unit : ∀ a o, reward a o ∈ Set.Icc (0 : ℝ) 1
  hypothesisClass : Set (robust_model Action Observation)
  action_distribution_nonempty : Nonempty (probability_mass Action)

abbrev online_policy (Action Observation : Type*) :=
  online_history Action Observation → probability_mass Action

abbrev online_environment (Action Observation : Type*) :=
  online_history Action Observation → Action → probability_mass Observation

def environment_consistent
    {Action Observation : Type*}
    (environment : online_environment Action Observation)
    (model : robust_model Action Observation) : Prop :=
  ∀ history action, (environment history action).mass ∈ (model action).carrier

noncomputable def robust_action_value
    {Action Observation : Type*}
    (framework : robust_online_decision_framework Action Observation)
    (model : robust_model Action Observation) (action : Action) : ℝ :=
  sInf (Set.range fun p : {p // p ∈ (model action).carrier} =>
    ∑' observation, p.1 observation * framework.reward action observation)

noncomputable def robust_optimal_value
    {Action Observation : Type*}
    (framework : robust_online_decision_framework Action Observation)
    (model : robust_model Action Observation) : ℝ :=
  sSup (Set.range fun action => robust_action_value framework model action)

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

noncomputable def fuzzy_decision_estimation_coefficient_at
    {Action Observation : Type*}
    (framework : robust_online_decision_framework Action Observation)
    (loss : robust_loss Action Observation) (epsilon : ℝ)
    (reference : robust_model Action Observation) : ℝ :=
  sInf (Set.range fun actions =>
    fuzzy_decision_objective framework loss epsilon reference actions)

structure fuzzy_decision_minimizer
    {Action Observation : Type*}
    (framework : robust_online_decision_framework Action Observation)
    (loss : robust_loss Action Observation) where
  actions : ℝ → robust_model Action Observation → probability_mass Action
  attains : ∀ epsilon reference,
    fuzzy_decision_objective framework loss epsilon reference
        (actions epsilon reference) =
      fuzzy_decision_estimation_coefficient_at framework loss epsilon reference

noncomputable def fuzzy_decision_estimation_coefficient
    {Action Observation : Type*}
    (framework : robust_online_decision_framework Action Observation)
    (loss : robust_loss Action Observation) (epsilon : ℝ) : ℝ :=
  sSup (Set.range fun reference =>
    fuzzy_decision_estimation_coefficient_at framework loss epsilon reference)

noncomputable def e2d_action_distribution
    {Action Observation : Type*}
    (framework : robust_online_decision_framework Action Observation)
    (loss : robust_loss Action Observation)
    (minimizer : fuzzy_decision_minimizer framework loss) (epsilon : ℝ)
    (reference : robust_model Action Observation) :
    probability_mass Action :=
  minimizer.actions epsilon reference

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

noncomputable def event_probability
    {Action Observation : Type*}
    (policy : online_policy Action Observation)
    (environment : online_environment Action Observation)
    (T : ℕ) (event : online_history Action Observation → Prop) : ℝ := by
  classical
  exact ∑' history, if history.length = T ∧ event history then
    trajectory_probability policy environment history else 0

noncomputable def expected_cumulative_reward
    {Action Observation : Type*}
    (framework : robust_online_decision_framework Action Observation)
    (policy : online_policy Action Observation)
    (environment : online_environment Action Observation) (T : ℕ) : ℝ :=
  ∑' history, if history.length = T then
    trajectory_probability policy environment history *
      (history.map (fun pair => framework.reward pair.1 pair.2)).sum else 0

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
        alpha T delta + 2 * (T : ℝ) * delta := by sorry

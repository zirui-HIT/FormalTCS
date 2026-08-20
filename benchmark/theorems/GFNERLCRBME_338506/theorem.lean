import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators

abbrev feature_vector (d : ℕ) := EuclideanSpace ℝ (Fin d)

def unit_parameter_ball (d : ℕ) : Set (feature_vector d) :=
  Metric.closedBall 0 1

structure finite_policy (X Y : Type) [Fintype Y] where
  probability : X → Y → ℝ
  probability_nonnegative : ∀ x y, 0 ≤ probability x y
  probability_sum_one : ∀ x, ∑ y, probability x y = 1

noncomputable def linear_softmax_probability
    {X Y : Type} [Fintype Y] {d : ℕ} (β : ℝ)
    (referencePolicy : finite_policy X Y)
    (feature : X → Y → feature_vector d) (θ : feature_vector d) (x : X) (y : Y) : ℝ :=
  referencePolicy.probability x y * Real.exp (β⁻¹ * inner ℝ θ (feature x y)) /
    ∑ z, referencePolicy.probability x z * Real.exp (β⁻¹ * inner ℝ θ (feature x z))

noncomputable def policy_kl_divergence
    {X Y : Type} [Fintype X] [Fintype Y]
    (promptProbability : X → ℝ) (policy referencePolicy : finite_policy X Y) : ℝ := by
  classical
  exact ∑ x, promptProbability x * ∑ y,
    if policy.probability x y = 0 then 0
    else policy.probability x y *
      Real.log (policy.probability x y / referencePolicy.probability x y)

noncomputable def regularized_objective
    {X Y : Type} [Fintype X] [Fintype Y]
    (promptProbability : X → ℝ) (reward : X → Y → ℝ)
    (referencePolicy : finite_policy X Y) (β : ℝ) (policy : finite_policy X Y) : ℝ :=
  (∑ x, promptProbability x * ∑ y, policy.probability x y * reward x y) -
    β * policy_kl_divergence promptProbability policy referencePolicy

structure alignment_instance (X Y : Type) [Fintype X] [Fintype Y] (d : ℕ) where
  beta : ℝ
  beta_positive : 0 < beta
  promptProbability : X → ℝ
  promptProbability_nonnegative : ∀ x, 0 ≤ promptProbability x
  promptProbability_sum_one : ∑ x, promptProbability x = 1
  referencePolicy : finite_policy X Y
  referencePolicy_positive : ∀ x y, 0 < referencePolicy.probability x y
  feature : X → Y → feature_vector d
  feature_norm_le_one : ∀ x y, ‖feature x y‖ ≤ 1
  softmaxPolicy : feature_vector d → finite_policy X Y
  softmaxPolicy_formula : ∀ θ x y,
    (softmaxPolicy θ).probability x y =
      linear_softmax_probability beta referencePolicy feature θ x y
  trueParameter : feature_vector d
  trueParameter_mem_unit_ball : trueParameter ∈ unit_parameter_ball d
  reward : X → Y → ℝ
  reward_realizable : ∀ x y y',
    reward x y - reward x y' = inner ℝ trueParameter (feature x y - feature x y')
  reward_difference_abs_le_one : ∀ x y y', |reward x y - reward x y'| ≤ 1
  optimalPolicy : finite_policy X Y
  optimalPolicy_eq_softmax : optimalPolicy = softmaxPolicy trueParameter
  optimalPolicy_is_maximizer : ∀ policy,
    regularized_objective promptProbability reward referencePolicy beta policy ≤
      regularized_objective promptProbability reward referencePolicy beta optimalPolicy

noncomputable def coverage_coefficient
    {X Y : Type} [Fintype X] [Fintype Y] {d : ℕ}
    (inst : alignment_instance X Y d) : ℝ :=
  sSup (Set.range fun p : X × Y =>
    inst.optimalPolicy.probability p.1 p.2 /
      inst.referencePolicy.probability p.1 p.2)

inductive alignment_oracle_program
    (X Y : Type) [Fintype Y] (d : ℕ) (Result : Type) where
  | returnResult (result : Result)
  | rewardQuery (x : X) (y : Y)
      (next : ℝ → alignment_oracle_program X Y d Result)
  | strongSamplingQuery (x : X) (θ : feature_vector d)
      (hθ : θ ∈ unit_parameter_ball d)
      (next : Y → feature_vector d → alignment_oracle_program X Y d Result)
  | randomChoice (n : ℕ) (weight : Fin n → ℝ)
      (weight_nonnegative : ∀ i, 0 ≤ weight i)
      (weight_sum_one : ∑ i, weight i = 1)
      (next : Fin n → alignment_oracle_program X Y d Result)

noncomputable def oracle_program_output_probability
    {X Y : Type} [Fintype X] [Fintype Y] {d : ℕ}
    (inst : alignment_instance X Y d)
    (program : alignment_oracle_program X Y d (finite_policy X Y))
    (event : Set (finite_policy X Y)) : ℝ := by
  classical
  induction program with
  | returnResult result =>
      exact if result ∈ event then 1 else 0
  | rewardQuery x y next ih =>
      exact ih (inst.reward x y)
  | strongSamplingQuery x θ hθ next ih =>
      exact ∑ y, (inst.softmaxPolicy θ).probability x y *
        ih y (inst.feature x y)
  | randomChoice n weight weight_nonnegative weight_sum_one next ih =>
      exact ∑ i, weight i * ih i

noncomputable def oracle_program_reward_queries
    {X Y Result : Type} [Fintype X] [Fintype Y] {d : ℕ}
    (inst : alignment_instance X Y d)
    (program : alignment_oracle_program X Y d Result) : ℕ := by
  classical
  induction program with
  | returnResult result =>
      exact 0
  | rewardQuery x y next ih =>
      exact 1 + ih (inst.reward x y)
  | strongSamplingQuery x θ hθ next ih =>
      exact Finset.univ.sup fun y =>
        if 0 < (inst.softmaxPolicy θ).probability x y
        then ih y (inst.feature x y)
        else 0
  | randomChoice n weight weight_nonnegative weight_sum_one next ih =>
      exact Finset.univ.sup fun i => if 0 < weight i then ih i else 0

noncomputable def oracle_program_strong_sampling_queries
    {X Y Result : Type} [Fintype X] [Fintype Y] {d : ℕ}
    (inst : alignment_instance X Y d)
    (program : alignment_oracle_program X Y d Result) : ℕ := by
  classical
  induction program with
  | returnResult result =>
      exact 0
  | rewardQuery x y next ih =>
      exact ih (inst.reward x y)
  | strongSamplingQuery x θ hθ next ih =>
      exact 1 + Finset.univ.sup fun y =>
        if 0 < (inst.softmaxPolicy θ).probability x y
        then ih y (inst.feature x y)
        else 0
  | randomChoice n weight weight_nonnegative weight_sum_one next ih =>
      exact Finset.univ.sup fun i => if 0 < weight i then ih i else 0

structure online_alignment_algorithm where
  program :
    {X Y : Type} → [Fintype X] → [Fintype Y] → {d : ℕ} →
      ℝ → ℝ → ℝ → alignment_oracle_program X Y d (finite_policy X Y)

def valid_for_coverage_class
    (algorithm : online_alignment_algorithm) (coverageBound : ℝ)
    (responseBound d : ℕ) (β : ℝ) (rewardBudget samplingBudget : ℕ) : Prop :=
  ∀ (X Y : Type) [Fintype X] [Fintype Y]
      (inst : alignment_instance X Y d),
    inst.beta = β →
    Fintype.card Y ≤ responseBound →
    coverage_coefficient inst ≤ coverageBound →
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
      let program := algorithm.program (X := X) (Y := Y) (d := d) β ε δ
      1 - δ ≤ oracle_program_output_probability inst program
        {policy |
          regularized_objective inst.promptProbability inst.reward
              inst.referencePolicy inst.beta inst.optimalPolicy -
            regularized_objective inst.promptProbability inst.reward
              inst.referencePolicy inst.beta policy ≤ ε} ∧
      oracle_program_reward_queries inst program ≤ rewardBudget ∧
      oracle_program_strong_sampling_queries inst program ≤ samplingBudget

noncomputable def coverage_complexity_scale (β : ℝ) (d : ℕ) (coverageBound : ℝ) : ℝ :=
  min (Real.exp (β ^ 2 * (d : ℝ) / 2))
    (min (Real.exp (β⁻¹ / 2)) coverageBound)

theorem necessity_of_coverage :
    ∃ c : ℝ, 0 < c ∧
      ∀ (coverageBound β : ℝ) (responseBound d rewardBudget samplingBudget : ℕ)
        (algorithm : online_alignment_algorithm),
        2 ≤ coverageBound →
        2 ≤ responseBound →
        0 < β →
        valid_for_coverage_class algorithm coverageBound responseBound d β
            rewardBudget samplingBudget →
          (responseBound : ℝ) / 8 ≤ (rewardBudget : ℝ) ∨
            c * coverage_complexity_scale β d coverageBound ≤ (samplingBudget : ℝ) := by sorry

import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option linter.all false

structure finite_random_variable where
  Outcome : Type
  outcome_finite : Fintype Outcome
  probability : Outcome → ℝ
  probability_nonnegative : ∀ ω, 0 ≤ probability ω
  probability_sum_one :
    letI := outcome_finite
    ∑ ω, probability ω = 1
  value : Outcome → ℝ
  value_nonnegative : ∀ ω, 0 ≤ value ω

noncomputable def finite_random_variable_truncated_expectation
    (W : finite_random_variable) (y : ℝ) : ℝ :=
  letI := W.outcome_finite
  ∑ ω, W.probability ω * min y (W.value ω)

structure costly_information_mdp where
  State : Type
  state_finite : Fintype State
  Action : State → Type
  action_finite : ∀ s, Fintype (Action s)
  initial : State
  terminal : Set State
  terminalValue : State → ℝ
  actionCost : (s : State) → Action s → ℝ
  actionCost_nonnegative : ∀ s a, 0 ≤ actionCost s a
  transition : (s : State) → Action s → PMF State
  horizon : State → ℕ
  transition_descends :
    ∀ s a t, t ∈ (transition s a).support → horizon t < horizon s
  waterFillingSurrogate : finite_random_variable
  committedWaterFillingSurrogate :
    (∀ s : {s : State // s ∉ terminal}, PMF (Action s.1)) →
      finite_random_variable

abbrev costly_information_commitment (M : costly_information_mdp) :=
  ∀ s : {s : M.State // s ∉ M.terminal}, PMF (M.Action s.1)

noncomputable def costly_information_optimality_curve
    (M : costly_information_mdp) (y : ℝ) : ℝ :=
  finite_random_variable_truncated_expectation M.waterFillingSurrogate y

noncomputable def costly_information_committed_optimality_curve
    (M : costly_information_mdp) (π : costly_information_commitment M)
    (y : ℝ) : ℝ :=
  finite_random_variable_truncated_expectation
    (M.committedWaterFillingSurrogate π) y

def local_approximation (M : costly_information_mdp) (α : ℝ)
    (π : costly_information_commitment M) : Prop :=
  ∀ y : ℝ, costly_information_committed_optimality_curve M π (α * y) ≤
    α * costly_information_optimality_curve M y

noncomputable def matroid_water_filling_cost {ι : Type*} [Fintype ι]
    (M : Matroid ι) (W : ι → finite_random_variable) : ℝ :=
  letI : DecidableEq ι := Classical.decEq ι
  letI : ∀ i, Fintype (W i).Outcome := fun i => (W i).outcome_finite
  ∑ ω : ∀ i, (W i).Outcome,
    (∏ i, (W i).probability (ω i)) *
      sInf {c : ℝ | ∃ B : Finset ι,
        M.IsBase (B : Set ι) ∧ c = ∑ i ∈ B, (W i).value (ω i)}

structure matroid_min_cics (ι : Type*) [Fintype ι] where
  groundMatroid : Matroid ι
  ground_eq_univ : groundMatroid.E = Set.univ
  constituent : ι → costly_information_mdp
  optimalCost : ℝ
  optimalCost_pos : 0 < optimalCost
  optimalCost_lower_bound :
    matroid_water_filling_cost groundMatroid
      (fun i => (constituent i).waterFillingSurrogate) ≤ optimalCost
  minimizingPolicy :
    ∀ i, costly_information_commitment (constituent i)
  minimizingPolicy_minimal :
    ∀ policy : ∀ i, costly_information_commitment (constituent i),
      matroid_water_filling_cost groundMatroid
        (fun i => (constituent i).committedWaterFillingSurrogate
          (minimizingPolicy i)) ≤
      matroid_water_filling_cost groundMatroid
        (fun i => (constituent i).committedWaterFillingSurrogate (policy i))

abbrev committing_policy {ι : Type*} [Fintype ι] (I : matroid_min_cics ι) :=
  ∀ i, costly_information_commitment (I.constituent i)

noncomputable def committed_optimal_cost {ι : Type*} [Fintype ι]
    (I : matroid_min_cics ι) (policy : committing_policy I) : ℝ :=
  matroid_water_filling_cost I.groundMatroid
    (fun i => (I.constituent i).committedWaterFillingSurrogate (policy i))

noncomputable def commitment_gap {ι : Type*} [Fintype ι]
    (I : matroid_min_cics ι) : ℝ :=
  committed_optimal_cost I I.minimizingPolicy / I.optimalCost

theorem la_comp {ι : Type*} [Fintype ι]
    (I : matroid_min_cics ι) (α : ℝ)
    (hα : 1 ≤ α)
    (hlocal : ∀ i, ∃ π : costly_information_commitment (I.constituent i),
      local_approximation (I.constituent i) α π) :
    commitment_gap I ≤ α := by sorry

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option linter.all false
set_option maxHeartbeats 500000

universe u

abbrev spin_configuration (V : Type u) := V → Bool

noncomputable def pmf_event_probability {Ω : Type u} (p : PMF Ω) (event : Ω → Prop) : ENNReal := by
  classical
  exact ∑' ω, if event ω then p ω else 0

noncomputable def pmf_total_variation {Ω : Type u} [Fintype Ω]
    (p q : PMF Ω) : ℝ :=
  (1 / 2 : ℝ) * ∑ ω, |(p ω).toReal - (q ω).toReal|

def hardcore_independent {V : Type u} (G : SimpleGraph V)
    (σ : spin_configuration V) : Prop :=
  ∀ ⦃v w : V⦄, G.Adj v w → ¬ (σ v = true ∧ σ w = true)

noncomputable def hardcore_weight {V : Type u} [Fintype V]
    (G : SimpleGraph V) (activity : V → ENNReal)
    (σ : spin_configuration V) : ENNReal := by
  classical
  exact if hardcore_independent G σ then ∏ v, if σ v = true then activity v else 1 else 0

structure hardcore_system (V : Type u) [Fintype V] [DecidableEq V] where
  graph : SimpleGraph V
  activity : V → ENNReal
  activity_pos : ∀ v, 0 < activity v
  distribution : PMF (spin_configuration V)
  gibbs_law : ∀ σ,
    distribution σ = hardcore_weight graph activity σ / ∑ τ, hardcore_weight graph activity τ

def spin_value (c : Bool) : ℝ :=
  if c = true then 1 else -1

noncomputable def ising_hamiltonian {V : Type u} [Fintype V]
    (interaction : V → V → ℝ) (field : V → ℝ)
    (σ : spin_configuration V) : ℝ :=
  -((1 / 2 : ℝ) * ∑ v, ∑ w, interaction v w * spin_value (σ v) * spin_value (σ w)) -
    ∑ v, field v * spin_value (σ v)

noncomputable def ising_weight {V : Type u} [Fintype V]
    (interaction : V → V → ℝ) (field : V → ℝ)
    (σ : spin_configuration V) : ENNReal :=
  ENNReal.ofReal (Real.exp (-ising_hamiltonian interaction field σ))

structure ising_system (V : Type u) [Fintype V] [DecidableEq V] where
  graph : SimpleGraph V
  interaction : V → V → ℝ
  field : V → ℝ
  interaction_symm : ∀ v w, interaction v w = interaction w v
  interaction_off_edge : ∀ ⦃v w : V⦄, ¬ graph.Adj v w → interaction v w = 0
  distribution : PMF (spin_configuration V)
  gibbs_law : ∀ σ,
    distribution σ = ising_weight interaction field σ / ∑ τ, ising_weight interaction field τ

structure hardcore_system_pair (V : Type u) [Fintype V] [DecidableEq V] where
  first : hardcore_system V
  second : hardcore_system V
  same_graph : first.graph = second.graph

structure ising_system_pair (V : Type u) [Fintype V] [DecidableEq V] where
  first : ising_system V
  second : ising_system V
  same_graph : first.graph = second.graph

inductive spin_system_pair (V : Type u) [Fintype V] [DecidableEq V] where
  | hardcore : hardcore_system_pair V → spin_system_pair V
  | ising : ising_system_pair V → spin_system_pair V

def pair_first_distribution {V : Type u} [Fintype V] [DecidableEq V]
    (pair : spin_system_pair V) : PMF (spin_configuration V) :=
  match pair with
  | .hardcore systems => systems.first.distribution
  | .ising systems => systems.first.distribution

def pair_second_distribution {V : Type u} [Fintype V] [DecidableEq V]
    (pair : spin_system_pair V) : PMF (spin_configuration V) :=
  match pair with
  | .hardcore systems => systems.second.distribution
  | .ising systems => systems.second.distribution

noncomputable def pair_first_partition {V : Type u} [Fintype V] [DecidableEq V]
    (pair : spin_system_pair V) : ENNReal :=
  match pair with
  | .hardcore systems => ∑ σ, hardcore_weight systems.first.graph systems.first.activity σ
  | .ising systems => ∑ σ, ising_weight systems.first.interaction systems.first.field σ

noncomputable def pair_second_partition {V : Type u} [Fintype V] [DecidableEq V]
    (pair : spin_system_pair V) : ENNReal :=
  match pair with
  | .hardcore systems => ∑ σ, hardcore_weight systems.second.graph systems.second.activity σ
  | .ising systems => ∑ σ, ising_weight systems.second.interaction systems.second.field σ

structure partial_spin_configuration (V : Type u) where
  domain : Finset V
  value : V → Bool

def extends_partial_configuration {V : Type u} [DecidableEq V]
    (τ : partial_spin_configuration V) (σ : spin_configuration V) : Prop :=
  ∀ v ∈ τ.domain, σ v = τ.value v

noncomputable def conditional_spin_marginal {V : Type u} [DecidableEq V]
    (p : PMF (spin_configuration V)) (τ : partial_spin_configuration V)
    (v : V) (c : Bool) : ℝ :=
  (pmf_event_probability p (fun σ => extends_partial_configuration τ σ ∧ σ v = c)).toReal /
    (pmf_event_probability p (extends_partial_configuration τ)).toReal

def marginally_bounded {V : Type u} [DecidableEq V]
    (b : ℝ) (p : PMF (spin_configuration V)) : Prop :=
  ∀ (τ : partial_spin_configuration V),
    0 < (pmf_event_probability p (extends_partial_configuration τ)).toReal →
    ∀ (v : V) (c : Bool),
      0 < conditional_spin_marginal p τ v c → b ≤ conditional_spin_marginal p τ v c

def pair_marginally_bounded {V : Type u} [Fintype V] [DecidableEq V]
    (b : ℝ) (pair : spin_system_pair V) : Prop :=
  marginally_bounded b (pair_first_distribution pair) ∧
    marginally_bounded b (pair_second_distribution pair)

structure sampling_oracle {Ω : Type u} [Fintype Ω]
    (target : PMF Ω) (cost : ℝ → ℝ) where
  sample_law : ℝ → PMF Ω
  runtime : ℝ → ℝ
  accurate : ∀ δ, 0 < δ → δ < 1 → pmf_total_variation (sample_law δ) target ≤ δ
  runtime_le : ∀ δ, 0 < δ → δ < 1 → runtime δ ≤ cost δ

structure approximate_counting_oracle (partition : ENNReal) (cost : ℝ → ℝ) where
  estimate_law : ℝ → PMF ℝ
  runtime : ℝ → ℝ
  accurate : ∀ δ, 0 < δ → δ < 1 →
    (99 / 100 : ENNReal) ≤ pmf_event_probability (estimate_law δ) (fun estimate =>
      (1 - δ) * partition.toReal ≤ estimate ∧ estimate ≤ (1 + δ) * partition.toReal)
  runtime_le : ∀ δ, 0 < δ → δ < 1 → runtime δ ≤ cost δ

structure pair_oracle_bundle {V : Type u} [Fintype V] [DecidableEq V]
    (pair : spin_system_pair V) (samplingCost countingCost : ℝ → ℝ) where
  sample_first : sampling_oracle (pair_first_distribution pair) samplingCost
  sample_second : sampling_oracle (pair_second_distribution pair) samplingCost
  count_first : approximate_counting_oracle (pair_first_partition pair) countingCost
  count_second : approximate_counting_oracle (pair_second_partition pair) countingCost

structure tv_approximation_algorithm where
  output_law : {V : Type u} → [Fintype V] → [DecidableEq V] →
    (pair : spin_system_pair V) → (samplingCost countingCost : ℝ → ℝ) →
    pair_oracle_bundle pair samplingCost countingCost → ℝ → PMF ℝ
  runtime : {V : Type u} → [Fintype V] → [DecidableEq V] →
    (pair : spin_system_pair V) → (samplingCost countingCost : ℝ → ℝ) →
    pair_oracle_bundle pair samplingCost countingCost → ℝ → ℝ

noncomputable def pair_instance_size {V : Type u} [Fintype V] [DecidableEq V]
    (pair : spin_system_pair V) : ℕ :=
  match pair with
  | .hardcore _ => Fintype.card V
  | .ising systems => Fintype.card V + systems.first.graph.edgeSet.ncard

def relative_error_event (ε trueValue estimate : ℝ) : Prop :=
  (1 - ε) * trueValue ≤ estimate ∧ estimate ≤ (1 + ε) * trueValue

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

theorem Ising_1 (b : ℝ) (hb_pos : 0 < b) (hb_lt_one : b < 1) :
    ∃ (algorithm : tv_approximation_algorithm)
      (samplingAccuracyFactor countingAccuracyFactor leadingFactor : ℝ),
      0 < samplingAccuracyFactor ∧ 0 < countingAccuracyFactor ∧ 0 < leadingFactor ∧
        solves_spin_tv_problems algorithm b samplingAccuracyFactor countingAccuracyFactor
          leadingFactor := by sorry

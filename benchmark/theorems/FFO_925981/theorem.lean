import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fintype.Card
import Mathlib.Probability.ProbabilityMassFunction.Monad

set_option linter.all false
set_option maxHeartbeats 500000

inductive filter_update (U : Type*)
  | insert (x : U)
  | delete (x : U)

def apply_filter_update {U : Type*} [DecidableEq U] (S : Finset U) :
    filter_update U → Finset U
  | filter_update.insert x => insert x S
  | filter_update.delete x => S.erase x

def stored_filter_keys {U : Type*} [DecidableEq U]
    (updates : List (filter_update U)) : Finset U :=
  updates.foldl apply_filter_update ∅

def legal_filter_update_trace {U : Type*} [DecidableEq U]
    (capacity : ℕ) (updates : List (filter_update U)) : Prop :=
  ∀ k ≤ updates.length, (stored_filter_keys (updates.take k)).card ≤ capacity

structure dynamic_filter_family (U : ℕ → Type*) where
  State : ℕ → Type*
  stateFintype : ∀ n, Fintype (State n)
  spaceBits : ℕ → ℕ
  updateBudget : ℕ → ℕ
  initialStateDistribution : (n : ℕ) → PMF (State n)
  updateTransition :
    (n : ℕ) → State n → filter_update (U n) → PMF (State n)
  queryDistribution : (n : ℕ) → State n → U n → PMF Bool
  stateCardinalityBound :
    ∀ n, @Fintype.card (State n) (stateFintype n) ≤ 2 ^ spaceBits n

noncomputable def dynamic_filter_state_distribution {U : ℕ → Type*}
    (A : dynamic_filter_family U) (n : ℕ)
    (updates : List (filter_update (U n))) : PMF (A.State n) :=
  updates.foldl
    (fun distribution update =>
      distribution.bind (fun state => A.updateTransition n state update))
    (A.initialStateDistribution n)

noncomputable def dynamic_filter_positive_answer_probability {U : ℕ → Type*}
    (A : dynamic_filter_family U) (n : ℕ)
    (updates : List (filter_update (U n))) (x : U n) : ℝ :=
  ENNReal.toReal
    (((dynamic_filter_state_distribution A n updates).bind
      (fun state => A.queryDistribution n state x)) true)

def implements_dynamic_filter {U : ℕ → Type*} [∀ n, DecidableEq (U n)]
    (A : dynamic_filter_family U) (capacity : ℕ → ℕ) (ε : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (updates : List (filter_update (U n))),
    updates.length ≤ A.updateBudget n →
    legal_filter_update_trace (capacity n) updates →
      (∀ x : U n,
        x ∈ stored_filter_keys updates →
          dynamic_filter_positive_answer_probability A n updates x = 1) ∧
      (∀ x : U n, x ∉ stored_filter_keys updates →
        dynamic_filter_positive_answer_probability A n updates x ≤ ε n)

def vanishing_false_positive_rate (ε : ℕ → ℝ) : Prop :=
  (∀ᶠ n in Filter.atTop, ε n ∈ Set.Ioo (0 : ℝ) 1) ∧
    Asymptotics.IsLittleO Filter.atTop ε (fun _ : ℕ => (1 : ℝ))

def universe_outgrows_filter_scale (U : ℕ → Type*) [∀ n, Fintype (U n)]
    (ε : ℕ → ℝ) : Prop :=
  Asymptotics.IsLittleO Filter.atTop
    (fun n : ℕ => (n : ℝ) * (ε n)⁻¹)
    (fun n : ℕ => (Fintype.card (U n) : ℝ))

def supports_superlinear_updates {U : ℕ → Type*}
    (A : dynamic_filter_family U) : Prop :=
  Asymptotics.IsLittleO Filter.atTop
    (fun n : ℕ => (n : ℝ))
    (fun n : ℕ => (A.updateBudget n : ℝ))

noncomputable def filter_space_leading_term (ε : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * Real.logb 2 (ε n)⁻¹ +
    (n : ℝ) * Real.logb 2 (Real.exp 1)

def filter_space_lower_bound {U : ℕ → Type*}
    (A : dynamic_filter_family U) (ε : ℕ → ℝ) : Prop :=
  ∃ r : ℕ → ℝ,
    Asymptotics.IsLittleO Filter.atTop r (fun n : ℕ => (n : ℝ)) ∧
      ∀ᶠ n in Filter.atTop,
        filter_space_leading_term ε n - r n ≤ (A.spaceBits n : ℝ)

theorem filter_lb
    (U : ℕ → Type*) [∀ n, Fintype (U n)] [∀ n, DecidableEq (U n)]
    (ε : ℕ → ℝ) (A : dynamic_filter_family U)
    (hε : vanishing_false_positive_rate ε)
    (hU : universe_outgrows_filter_scale U ε)
    (hfilter : implements_dynamic_filter A (fun n => n) ε)
    (hupdates : supports_superlinear_updates A) :
    filter_space_lower_bound A ε := by sorry

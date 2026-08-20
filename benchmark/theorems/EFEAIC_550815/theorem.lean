import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.NNReal.Defs

open scoped NNReal

abbrev chore_allocation (Agent Chore : Type) := Chore → Agent

noncomputable def chore_bundle {Agent Chore : Type} [Fintype Chore]
    (x : chore_allocation Agent Chore) (i : Agent) : Finset Chore := by
  classical
  exact Finset.univ.filter (fun j => x j = i)

def bundle_cost {Agent Chore : Type} (c : Agent → Chore → NNReal)
    (i : Agent) (S : Finset Chore) : NNReal :=
  ∑ j ∈ S, c i j

noncomputable def allocated_bundle_cost {Agent Chore : Type} [Fintype Chore]
    (c : Agent → Chore → NNReal) (x : chore_allocation Agent Chore)
    (i k : Agent) : NNReal :=
  bundle_cost c i (chore_bundle x k)

noncomputable def envy_free_up_to_one_chore {Agent Chore : Type} [Fintype Chore]
    (c : Agent → Chore → NNReal) (x : chore_allocation Agent Chore) : Prop := by
  classical
  exact ∀ i k : Agent,
    allocated_bundle_cost c x i k < allocated_bundle_cost c x i i →
      ∃ j ∈ chore_bundle x i,
        bundle_cost c i ((chore_bundle x i).erase j) ≤
          allocated_bundle_cost c x i k

noncomputable def pareto_dominates {Agent Chore : Type} [Fintype Chore]
    (c : Agent → Chore → NNReal)
    (y x : chore_allocation Agent Chore) : Prop :=
  (∀ i : Agent,
      allocated_bundle_cost c y i i ≤ allocated_bundle_cost c x i i) ∧
    ∃ h : Agent,
      allocated_bundle_cost c y h h < allocated_bundle_cost c x h h

noncomputable def pareto_optimal {Agent Chore : Type} [Fintype Chore]
    (c : Agent → Chore → NNReal)
    (x : chore_allocation Agent Chore) : Prop :=
  ∀ y : chore_allocation Agent Chore, ¬ pareto_dominates c y x

theorem main {Agent Chore : Type}
    [Fintype Agent] [Nonempty Agent] [Fintype Chore]
    (c : Agent → Chore → NNReal) :
    ∃ x : chore_allocation Agent Chore,
      envy_free_up_to_one_chore c x ∧ pareto_optimal c x := by sorry

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Order.Defs.Unbundled
import Mathlib.Topology.Order.Basic

set_option maxHeartbeats 500000

open scoped BigOperators

noncomputable def voter_preference_fraction
    {V C : Type} [Fintype V]
    (prefers : V → C → C → Prop) (a b : C) : ℝ := by
  classical
  exact
    ((Finset.univ.filter (fun v => prefers v a b)).card : ℝ) /
      (Fintype.card V : ℝ)

def finite_distribution_on
    {C : Type} [Fintype C] [DecidableEq C]
    (S : Finset C) (D : C → ℝ) : Prop :=
  (∀ b, 0 ≤ D b) ∧
    (∑ b, D b) = 1 ∧
      ∀ b, b ∉ S → D b = 0

noncomputable def alpha_dominating_committee
    {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [DecidableEq C]
    (prefers : V → C → C → Prop) (α : ℝ) (S : Finset C) : Prop :=
  ∀ a, a ∉ S →
    ∃ b, b ∈ S ∧ α ≤ voter_preference_fraction prefers b a

noncomputable def near_dominating_witness
    {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [DecidableEq C]
    (prefers : V → C → C → Prop) (remainder : ℝ → ℝ) (ε : ℝ)
    (S : Finset C) (D : C → ℝ) : Prop :=
  (S.card : ℝ) ≤
      (1 + remainder ε) * Real.pi / (8 * ε ^ 2) ∧
    finite_distribution_on S D ∧
      alpha_dominating_committee prefers ((1 : ℝ) / 2 - ε) S ∧
        ∀ a,
          (∑ b, D b * voter_preference_fraction prefers a b) ≤
            (1 : ℝ) / 2 + ε

theorem approximately_dominating_sets_in_elections :
    ∃ remainder : ℝ → ℝ,
      Filter.Tendsto remainder
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
        ∀ (ε : ℝ), 0 < ε →
          ∀ (V C : Type) [Fintype V] [Nonempty V]
            [Fintype C] [Nonempty C] [DecidableEq C],
            ∀ prefers : V → C → C → Prop,
              (∀ v, IsStrictTotalOrder C (prefers v)) →
                ∃ (S : Finset C) (D : C → ℝ),
                  near_dominating_witness prefers remainder ε S D := by sorry

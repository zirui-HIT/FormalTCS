import Mathlib

structure election (V C : Type*) where
  prefers : V → C → C → Prop
  preference_is_strict_total : ∀ v, IsStrictTotalOrder C (prefers v)

abbrev committee (C : Type*) := Finset C

def prefers_over_committee {V C : Type*} (E : election V C) (v : V) (a : C)
    (S : committee C) : Prop :=
  ∀ b ∈ S, E.prefers v a b

noncomputable def voter_fraction {V C : Type*} [Fintype V] (E : election V C) (a : C)
    (S : committee C) : ℝ := by
  classical
  exact
    ((Finset.univ.filter (fun v => prefers_over_committee E v a S)).card : ℝ) /
      (Fintype.card V : ℝ)

def alpha_undominated {V C : Type*} [Fintype V] (E : election V C) (α : ℝ) (k : ℕ)
    (S : committee C) : Prop :=
  S.card ≤ k ∧ ∀ a : C, voter_fraction E a S < α

theorem main {V C : Type*} [Fintype V] [Fintype C] [DecidableEq C]
    (E : election V C) (α : ℝ) (k : ℕ)
    (hαpos : 0 < α) (hαle : α ≤ 1) (hk : 0 < k)
    (hcond : 2 / ((k : ℝ) + 1) ≤ α / (1 - Real.log α)) :
    ∃ S : committee C, alpha_undominated E α k S := by sorry

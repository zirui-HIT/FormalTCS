import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option linter.all false
set_option maxHeartbeats 500000

open Asymptotics Filter

structure promise_template where
  relationCount : ℕ
  arity : Fin relationCount → ℕ
  arity_pos : ∀ r, 0 < arity r
  strong : (r : Fin relationCount) → Set (Fin (arity r) → Bool)
  weak : (r : Fin relationCount) → Set (Fin (arity r) → Bool)
  strong_le_weak : ∀ r, strong r ⊆ weak r
  maxArity : ℕ
  arity_le_max : ∀ r, arity r ≤ maxArity

def preserves_relation_pair {k m : ℕ}
    (P Q : Set (Fin k → Bool)) (F : (Fin m → Bool) → Bool) : Prop :=
  ∀ rows : Fin m → Fin k → Bool,
    (∀ row, rows row ∈ P) →
      (fun coordinate => F (fun row => rows row coordinate)) ∈ Q

def boolean_majority (m : ℕ) (x : Fin (2 * m + 1) → Bool) : Bool :=
  decide (m < (Finset.univ.filter fun i => x i = true).card)

def admits_majority (Γ : promise_template) : Prop :=
  ∀ (r : Fin Γ.relationCount) (m : ℕ),
    preserves_relation_pair (Γ.strong r) (Γ.weak r) (boolean_majority m)

structure pcsp_constraint (Γ : promise_template) (n : ℕ) where
  relation : Fin Γ.relationCount
  scope : Fin (Γ.arity relation) → Fin n

structure pcsp_instance (Γ : promise_template) where
  variableCount : ℕ
  constraintCount : ℕ
  constraint : Fin constraintCount → pcsp_constraint Γ variableCount

abbrev pcsp_assignment {Γ : promise_template} (I : pcsp_instance Γ) :=
  Fin I.variableCount → Bool

def constraint_output_tuple {Γ : promise_template} (I : pcsp_instance Γ)
    (assignment : pcsp_assignment I) (j : Fin I.constraintCount) :
    Fin (Γ.arity (I.constraint j).relation) → Bool :=
  fun coordinate => assignment ((I.constraint j).scope coordinate)

def strongly_satisfies_constraint {Γ : promise_template} (I : pcsp_instance Γ)
    (assignment : pcsp_assignment I) (j : Fin I.constraintCount) : Prop :=
  constraint_output_tuple I assignment j ∈ Γ.strong (I.constraint j).relation

def weakly_satisfies_constraint {Γ : promise_template} (I : pcsp_instance Γ)
    (assignment : pcsp_assignment I) (j : Fin I.constraintCount) : Prop :=
  constraint_output_tuple I assignment j ∈ Γ.weak (I.constraint j).relation

noncomputable def finite_average {ι : Type*} [Fintype ι] (f : ι → ℝ) : ℝ := by
  classical
  exact if h : Nonempty ι then (∑ i, f i) / Fintype.card ι else 0

noncomputable def satisfaction_fraction {ι : Type*} [Fintype ι]
    (p : ι → Prop) : ℝ := by
  classical
  exact if h : Nonempty ι then
    ((Finset.univ.filter p).card : ℝ) / Fintype.card ι
  else 1

noncomputable def strong_satisfaction_fraction {Γ : promise_template}
    (I : pcsp_instance Γ) (assignment : pcsp_assignment I) : ℝ :=
  satisfaction_fraction fun j => strongly_satisfies_constraint I assignment j

noncomputable def weak_satisfaction_fraction {Γ : promise_template}
    (I : pcsp_instance Γ) (assignment : pcsp_assignment I) : ℝ :=
  satisfaction_fraction fun j => weakly_satisfies_constraint I assignment j

def approximately_strongly_satisfiable {Γ : promise_template}
    (I : pcsp_instance Γ) (ε : ℝ) : Prop :=
  ∃ assignment : pcsp_assignment I,
    1 - ε ≤ strong_satisfaction_fraction I assignment

structure uniform_randomized_algorithm (Γ : promise_template) where
  run : (ε : ℝ) → (I : pcsp_instance Γ) → PMF (pcsp_assignment I)
  cost : (ε : ℝ) → pcsp_instance Γ → ℕ

noncomputable def expected_weak_satisfaction {Γ : promise_template}
    (A : uniform_randomized_algorithm Γ) (ε : ℝ) (I : pcsp_instance Γ) : ℝ := by
  classical
  exact ∑ assignment : pcsp_assignment I,
    (A.run ε I assignment).toReal * weak_satisfaction_fraction I assignment

def polynomial_time {Γ : promise_template}
    (A : uniform_randomized_algorithm Γ) : Prop :=
  ∀ ε : ℝ, ∃ c d : ℕ, ∀ I : pcsp_instance Γ,
    A.cost ε I ≤ c * (I.variableCount + I.constraintCount + 1) ^ d

def robust_with_loss {Γ : promise_template}
    (A : uniform_randomized_algorithm Γ) (loss : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ I : pcsp_instance Γ,
    approximately_strongly_satisfiable I ε →
      1 - loss ε ≤ expected_weak_satisfaction A ε I

theorem robust_MAJ (Γ : promise_template) (hMajority : admits_majority Γ) :
    ∃ (A : uniform_randomized_algorithm Γ) (loss : ℝ → ℝ),
      polynomial_time A ∧
      robust_with_loss A loss ∧
      loss =O[nhdsWithin 0 (Set.Ici 0)] fun ε : ℝ => Real.sqrt ε := by sorry

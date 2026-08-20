import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Countable.Defs
import Mathlib.Data.List.Basic

def enumerates {U : Type*} (L : Set U) (e : ℕ → U) : Prop :=
  (∀ n, e n ∈ L) ∧ ∀ x ∈ L, ∃ n, e n = x

def prefix_seq {U : Type*} (e : ℕ → U) (t : ℕ) : List U :=
  (List.range t).map e

def list_identifies {U : Type*} (C : ℕ → Set U) (L : Set U) {k : ℕ}
    (μ : Fin k → ℕ) : Prop :=
  ∃ j : Fin k, C (μ j) = L

def identifies_in_limit {U : Type*} {k : ℕ} (C : ℕ → Set U)
    (A : List U → Fin k → ℕ) : Prop :=
  ∀ z : ℕ, ∀ e : ℕ → U, enumerates (C z) e →
    ∃ tStar : ℕ, ∀ t : ℕ, tStar ≤ t → list_identifies C (C z) (A (prefix_seq e t))

def identifiable {U : Type*} (C : ℕ → Set U) (k : ℕ) : Prop :=
  ∃ A : List U → Fin k → ℕ, identifies_in_limit C A

def angluin_predicate {U : Type*} (C : ℕ → Set U) : ℕ → ℕ → Prop
  | _, 0 => False
  | i, (k + 1) =>
      ∃ T : Set U, T.Finite ∧ T ⊆ C i ∧
        ∀ j, C j ⊂ C i → (¬ (T ⊆ C j) ∨ angluin_predicate C j k)

def k_angluin_condition {U : Type*} (C : ℕ → Set U) (k : ℕ) : Prop :=
  ∀ i, angluin_predicate C i k

theorem k_list_identification_characterization {U : Type*} [Countable U]
    (C : ℕ → Set U) (hne : ∀ i, (C i).Nonempty) {k : ℕ} (hk : 1 ≤ k) :
    identifiable C k ↔ k_angluin_condition C k := by sorry

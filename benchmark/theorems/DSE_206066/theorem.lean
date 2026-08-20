import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option linter.all false
set_option maxHeartbeats 500000

abbrev binary_hypothesis (X : Type) := X → Bool

abbrev hypothesis_class (X : Type) := Set (binary_hypothesis X)

abbrev labeled_example (X : Type) := X × Bool

structure finite_dataset (X : Type) where
  examples : List (labeled_example X)
  nonempty : examples ≠ []

noncomputable def empirical_classification_loss {X : Type}
    (S : List (labeled_example X)) (h : binary_hypothesis X) : ℝ :=
  ((S.filter fun z => h z.1 != z.2).length : ℝ) / S.length

abbrev erm_rule (X : Type) := List (labeled_example X) → binary_hypothesis X

def is_erm {X : Type} (H : hypothesis_class X) (A : erm_rule X) : Prop :=
  ∀ S, A S ∈ H ∧
    ∀ h ∈ H, empirical_classification_loss S (A S) ≤ empirical_classification_loss S h

def is_selected_sample {X : Type} (D : finite_dataset X) (n : ℕ)
    (S : List (labeled_example X)) : Prop :=
  S.length = n ∧ ∀ z, z ∈ S → z ∈ D.examples

noncomputable def best_class_loss {X : Type} (H : hypothesis_class X)
    (D : finite_dataset X) : ℝ :=
  sInf {r : ℝ | ∃ h ∈ H, r = empirical_classification_loss D.examples h}

noncomputable def selection_regret {X : Type} (H : hypothesis_class X)
    (A : erm_rule X) (D : finite_dataset X) (n : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ S : List (labeled_example X),
    is_selected_sample D n S ∧
      r = empirical_classification_loss D.examples (A S) - best_class_loss H D}

noncomputable def worst_selection_regret {X : Type} (H : hypothesis_class X)
    (n : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ A : erm_rule X, is_erm H A ∧
    ∃ D : finite_dataset X, r = selection_regret H A D n}

def trivial_rate (R : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, R n = 1

def linear_rate (R : ℕ → ℝ) : Prop :=
  ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ n : ℕ, 2 ≤ n → C₁ / (n : ℝ) ≤ R n ∧
      R n ≤ C₂ * Real.log (n : ℝ) / (n : ℝ)

def zero_rate (R : ℕ → ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → R n = 0

def exactly_one_of_three (P Q R : Prop) : Prop :=
  (P ∧ ¬ Q ∧ ¬ R) ∨ (¬ P ∧ Q ∧ ¬ R) ∨ (¬ P ∧ ¬ Q ∧ R)

theorem binary_classification_regret_trichotomy (X : Type)
    (H : hypothesis_class X) :
    exactly_one_of_three
      (trivial_rate (worst_selection_regret H))
      (linear_rate (worst_selection_regret H))
      (zero_rate (worst_selection_regret H)) := by sorry

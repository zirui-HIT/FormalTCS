import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Card
import Mathlib.Probability.ProbabilityMassFunction.Basic

universe u v

abbrev eq_hypothesis_class (X : Type u) := Set (X → Bool)

abbrev eq_hypothesis {X : Type u} (H : eq_hypothesis_class X) := {h // h ∈ H}

def eq_mistake_tree (X : Type u) (d : ℕ) :=
  ∀ i : Fin d, (Fin i → Bool) → X

def eq_tree_path {X : Type u} {d : ℕ} (tree : eq_mistake_tree X d)
    (bits : Fin d → Bool) (i : Fin d) : X :=
  tree i (fun j => bits ⟨j.1, lt_trans j.2 i.2⟩)

def eq_shatters_tree {X : Type u} (H : eq_hypothesis_class X) {d : ℕ}
    (tree : eq_mistake_tree X d) : Prop :=
  ∀ bits : Fin d → Bool, ∃ h : eq_hypothesis H,
    ∀ i : Fin d, h.1 (eq_tree_path tree bits i) = bits i

def eq_shatters_depth {X : Type u} (H : eq_hypothesis_class X) (d : ℕ) : Prop :=
  ∃ tree : eq_mistake_tree X d, eq_shatters_tree H tree

noncomputable def littlestone_dim {X : Type u} (H : eq_hypothesis_class X) : ℕ := by
  classical
  exact (Finset.range (H.ncard + 1)).sup
    (fun d => if eq_shatters_depth H d then d else 0)

structure eq_feedback (X : Type u) (H : eq_hypothesis_class X) where
  hypothesis : eq_hypothesis H
  point : X
  label : Bool

abbrev eq_history (X : Type u) (H : eq_hypothesis_class X) :=
  List (eq_feedback X H)

structure eq_learning_rule (X : Type u) (H : eq_hypothesis_class X) where
  choose : eq_history X H → PMF (eq_hypothesis H)

structure eq_counterexample_generator (X : Type u) (H : eq_hypothesis_class X) where
  draw : ∀ (history : List (eq_hypothesis H))
    (target proposed : eq_hypothesis H), target ≠ proposed → PMF X
  valid : ∀ (history : List (eq_hypothesis H))
    (target proposed : eq_hypothesis H) (hne : target ≠ proposed),
    (draw history target proposed hne).support ⊆
      {x | proposed.1 x ≠ target.1 x}

def eq_is_symmetric {X : Type u} {H : eq_hypothesis_class X}
    (adversary : eq_counterexample_generator X H) : Prop :=
  ∀ (history : List (eq_hypothesis H)) (h c : eq_hypothesis H) (hne : h ≠ c),
    adversary.draw history h c hne =
      adversary.draw history c h (Ne.symm hne)

def eq_hypothesis_history {X : Type u} {H : eq_hypothesis_class X}
    (history : eq_history X H) : List (eq_hypothesis H) :=
  history.map eq_feedback.hypothesis

noncomputable def pmf_expectation {α : Type v} (p : PMF α)
    (f : α → ENNReal) : ENNReal :=
  ∑' a, p a * f a

noncomputable def eq_survival_probability {X : Type u} {H : eq_hypothesis_class X}
    (learner : eq_learning_rule X H) (adversary : eq_counterexample_generator X H)
    (target : eq_hypothesis H) : eq_history X H → ℕ → ENNReal := by
  classical
  intro history n
  induction n generalizing history with
  | zero =>
      exact 1
  | succ n ih =>
      exact pmf_expectation (learner.choose history) (fun proposed =>
        if heq : proposed = target then 0
        else
          pmf_expectation
            (adversary.draw (eq_hypothesis_history history) target proposed
              (Ne.symm heq))
            (fun x => ih (history ++
              [{ hypothesis := proposed, point := x, label := target.1 x }])))

noncomputable def eq_expected_queries {X : Type u} {H : eq_hypothesis_class X}
    (learner : eq_learning_rule X H) (adversary : eq_counterexample_generator X H)
    (target : eq_hypothesis H) : ENNReal :=
  ∑' n : ℕ, eq_survival_probability learner adversary target [] n

def full_information_upper_statement : Prop :=
  ∃ C : ENNReal, C ≠ ⊤ ∧
    ∀ (X : Type u) (H : eq_hypothesis_class X), H.Finite → H.Nonempty →
      ∀ adversary : eq_counterexample_generator X H,
        eq_is_symmetric adversary →
        ∃ learner : eq_learning_rule X H, ∀ target : eq_hypothesis H,
          eq_expected_queries learner adversary target ≤
            C * ((littlestone_dim H : ENNReal) + 1)

def full_information_lower_statement : Prop :=
  ∃ c : ENNReal, 0 < c ∧ c ≠ ⊤ ∧
    ∀ (X : Type u) (H : eq_hypothesis_class X), H.Finite → H.Nonempty →
      ∃ adversary : eq_counterexample_generator X H,
        eq_is_symmetric adversary ∧
        ∀ learner : eq_learning_rule X H, ∃ target : eq_hypothesis H,
          c * (littlestone_dim H : ENNReal) ≤
            eq_expected_queries learner adversary target

theorem full_information :
    full_information_upper_statement ∧ full_information_lower_statement := by sorry

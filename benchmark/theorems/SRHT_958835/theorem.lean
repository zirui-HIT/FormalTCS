import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Logic.Equiv.Defs

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory Finset BigOperators

noncomputable def seed_measure : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

def tester (n m : ℕ) : Type :=
  (Fin m → Fin n) → ℝ → Bool

def measurable_tester {n m : ℕ} (A : tester n m) : Prop :=
  ∀ X : Fin m → Fin n, MeasurableSet {r : ℝ | A X r = true}

noncomputable def seed_accept_prob {n m : ℕ} (A : tester n m) (X : Fin m → Fin n) : ℝ :=
  seed_measure.real {r : ℝ | A X r = true}

noncomputable def threshold_tester {n m : ℕ} (f : (Fin m → Fin n) → ℝ) : tester n m :=
  fun X r => decide (r ≤ f X)

def is_random_threshold {n m : ℕ} (A : tester n m) : Prop :=
  ∃ f : (Fin m → Fin n) → ℝ, (∀ X, f X ∈ Set.Icc (0 : ℝ) 1) ∧ A = threshold_tester f

noncomputable def sample_weight {n : ℕ} (p : PMF (Fin n)) {m : ℕ} (X : Fin m → Fin n) : ℝ :=
  ∏ i : Fin m, (p (X i)).toReal

noncomputable def accept_prob {n m : ℕ} (p : PMF (Fin n)) (A : tester n m) : ℝ :=
  ∑ X : Fin m → Fin n, sample_weight p X * seed_accept_prob A X

noncomputable def replicable {n m : ℕ} (ρ : ℝ) (A : tester n m) : Prop :=
  ∀ p : PMF (Fin n),
    1 - ρ ≤ ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
      sample_weight p X * sample_weight p X' *
        seed_measure.real {r : ℝ | A X r = A X' r}

noncomputable def perm_pmf {n : ℕ} (π : Equiv.Perm (Fin n)) (p : PMF (Fin n)) : PMF (Fin n) :=
  p.map π

noncomputable def tv_dist {n : ℕ} (p q : PMF (Fin n)) : ℝ :=
  (1 / 2) * ∑ j : Fin n, |(p j).toReal - (q j).toReal|

def symmetric_property {n : ℕ} (P : Set (PMF (Fin n))) : Prop :=
  ∀ p ∈ P, ∀ π : Equiv.Perm (Fin n), perm_pmf π p ∈ P

noncomputable def far_from {n : ℕ} (ε : ℝ) (P : Set (PMF (Fin n))) (p : PMF (Fin n)) : Prop :=
  ∀ q ∈ P, ε ≤ tv_dist p q

noncomputable def accurate_tester {n m : ℕ} (ε δ : ℝ) (P : Set (PMF (Fin n)))
    (A : tester n m) : Prop :=
  (∀ p ∈ P, 1 - δ ≤ accept_prob p A) ∧
    (∀ p : PMF (Fin n), far_from ε P p → accept_prob p A ≤ δ)

def order_invariant {n m : ℕ} (A : tester n m) : Prop :=
  ∀ (r : ℝ) (σ : Equiv.Perm (Fin m)) (X : Fin m → Fin n), A X r = A (X ∘ σ) r

def label_invariant {n m : ℕ} (A : tester n m) : Prop :=
  ∀ (r : ℝ) (π : Equiv.Perm (Fin n)) (X : Fin m → Fin n), A X r = A (π ∘ X) r

noncomputable def perm_robust_replicable {n m : ℕ} (ρ : ℝ) (A : tester n m) : Prop :=
  ∀ (p : PMF (Fin n)) (π : Equiv.Perm (Fin n)),
    ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
      sample_weight p X * sample_weight (perm_pmf π p) X' *
        seed_measure.real {r : ℝ | A X r ≠ A X' r} ≤ ρ

theorem main_canonical {n m : ℕ} (ρ ε δ : ℝ) (P : Set (PMF (Fin n)))
    (hP : symmetric_property P) (A : tester n m) (hA : measurable_tester A)
    (hrep : replicable ρ A) (hacc : accurate_tester ε δ P A) :
    ∃ A' : tester n m,
      accurate_tester ε δ P A' ∧
      is_random_threshold A' ∧
      order_invariant A' ∧
      label_invariant A' ∧
      replicable ρ A' ∧
      perm_robust_replicable ρ A' := by sorry

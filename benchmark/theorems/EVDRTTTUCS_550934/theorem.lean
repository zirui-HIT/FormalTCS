import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators

def is_union_of_convex (d s : ℕ) (C : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ K : Fin s → Set (EuclideanSpace ℝ (Fin d)),
    (∀ i, Convex ℝ (K i)) ∧ C = ⋃ i, K i

def has_radon_partition_property (d s t n : ℕ) : Prop :=
  ∀ P : Finset (EuclideanSpace ℝ (Fin d)), P.card = n →
    ∃ A B : Finset (EuclideanSpace ℝ (Fin d)),
      A ∪ B = P ∧ Disjoint A B ∧
      ∀ C D : Set (EuclideanSpace ℝ (Fin d)),
        is_union_of_convex d s C → is_union_of_convex d t D →
        (A : Set (EuclideanSpace ℝ (Fin d))) ⊆ C →
        (B : Set (EuclideanSpace ℝ (Fin d))) ⊆ D →
        (C ∩ D).Nonempty

noncomputable def radon_number (d s t : ℕ) : ℕ :=
  sInf {n : ℕ | has_radon_partition_property d s t n}

theorem main :
    ∃ C : ℝ, 0 < C ∧ ∀ d s t : ℕ, 1 ≤ d → 1 ≤ s → 1 ≤ t →
      (radon_number d s t : ℝ) ≤
        C * (d : ℝ) * (s : ℝ) * (t : ℝ) * Real.log ((s : ℝ) * (t : ℝ) + 1) := by sorry

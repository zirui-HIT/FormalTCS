import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Order.Lattice.Nat

set_option linter.all false
set_option maxHeartbeats 500000

def observed_set {α : Type*} (input : ℕ → α) (t : ℕ) : Set α :=
  input '' Set.Iio t

def language_family_intersection {α : Type*} (C : ℕ → Set α) (A : Set ℕ) : Set α :=
  ⋂ i, ⋂ (_ : i ∈ A), C i

noncomputable def nonuniform_complexity {α : Type*} (C : ℕ → Set α) (i : ℕ) : ℕ :=
  sSup {n : ℕ | ∃ A : Set ℕ,
    A.Finite ∧ A ⊆ Set.Icc 1 i ∧ i ∈ A ∧
      (language_family_intersection C A).Finite ∧
      n = (language_family_intersection C A).ncard}

noncomputable def greedy_selected_indices {α : Type*}
    (C : ℕ → Set α) (S : Set α) : ℕ → Set ℕ
  | 0 => ∅
  | n + 1 =>
      @ite (Set ℕ)
        (S ⊆ C (n + 1) ∧
          (language_family_intersection C (greedy_selected_indices C S n) ∩
            C (n + 1)).Infinite)
        (Classical.propDecidable _)
        (insert (n + 1) (greedy_selected_indices C S n))
        (greedy_selected_indices C S n)

def greedy_intersection {α : Type*}
    (C : ℕ → Set α) (S : Set α) (t : ℕ) : Set α :=
  language_family_intersection C (greedy_selected_indices C S t)

noncomputable def greedy_output {α : Type*} [Nonempty α]
    (C : ℕ → Set α) (input : ℕ → α) (t : ℕ) : α :=
  @dite α
    (greedy_intersection C (observed_set input t) t \
      observed_set input t).Nonempty
    (Classical.propDecidable _)
    (fun h => h.choose)
    (fun _ => Classical.choice (inferInstance : Nonempty α))

theorem nonuniform_generation_upper_bound {σ : Type*} [Fintype σ]
    (C : ℕ → Set (List σ)) (hLanguagesInfinite : ∀ i, 1 ≤ i → (C i).Infinite)
    (iStar : ℕ) (hPositive : 1 ≤ iStar)
    (input : ℕ → List σ) (hEnumeration : Set.range input = C iStar)
    (t : ℕ)
    (hThreshold : max iStar (nonuniform_complexity C iStar + 1) ≤
      (observed_set input t).ncard) :
    greedy_output C input t ∈ C iStar \ observed_set input t := by
  sorry

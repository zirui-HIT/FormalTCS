import Mathlib

set_option linter.all false

abbrev concept_class (X : Type*) : Type _ := Set (X → Bool)

def class_shatters {X : Type*} (C : Set (X → Bool)) (W : Set X) : Prop :=
  ∀ p : X → Bool, ∃ c ∈ C, ∀ x ∈ W, c x = p x

noncomputable def vc_dim {X : Type*} (C : Set (X → Bool)) : ℕ :=
  sSup {n : ℕ | ∃ W : Finset X, W.card = n ∧ class_shatters C (↑W)}

def restrict_class {X : Type*} (C : Set (X → Bool)) (T : Set X) (b : X → Bool) :
    Set (X → Bool) :=
  {c | c ∈ C ∧ ∀ x ∈ T, c x = b x}

noncomputable def tail_width (k i : ℕ) : ℝ :=
  (2 : ℝ) ^ (Real.logb 2 (8 * (k : ℝ)) * (2 : ℝ) ^ (2 * i))

inductive greedy_run {X : Type*} (k : ℕ) : Set (X → Bool) → Set X → Prop
  | terminate (C : Set (X → Bool)) (h : C.Subsingleton) : greedy_run k C ∅
  | step (C : Set (X → Bool)) (T : Finset X) (b : X → Bool) (S : Set X)
      (hlow : 1 ≤ T.card) (hhigh : T.card ≤ k)
      (hne : (restrict_class C (↑T) b).Nonempty)
      (hmin : ∀ (T' : Finset X) (b' : X → Bool), 1 ≤ T'.card → T'.card ≤ k →
        (restrict_class C (↑T') b').Nonempty →
        (restrict_class C (↑T) b).ncard ≤ (restrict_class C (↑T') b').ncard)
      (htie : ∀ (T' : Finset X) (b' : X → Bool), 1 ≤ T'.card → T'.card ≤ k →
        (restrict_class C (↑T') b').Nonempty →
        (restrict_class C (↑T') b').ncard = (restrict_class C (↑T) b).ncard →
        T.card ≤ T'.card)
      (hrec : greedy_run k (restrict_class C (↑T) b) S) :
      greedy_run k C ((↑T : Set X) ∪ S)

theorem general_k_lower_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ (X : ℕ → Type) (_ : ∀ N : ℕ, Finite (X N)) (F : ∀ N : ℕ, concept_class (X N)),
      ∀ N : ℕ, 1 ≤ N →
        (F N).Finite ∧
        vc_dim (F N) ≤ 4 * k + 1 ∧
        ((F N).ncard : ℝ) ≤ tail_width k N ^ (4 * k) ∧
        (Nat.card (X N) : ℝ) ≤ 6 * (k : ℝ) * tail_width k N ∧
        (∃ S : Set (X N), greedy_run k (F N) S) ∧
        (∀ S : Set (X N), greedy_run k (F N) S → k * N ≤ S.ncard) := by sorry

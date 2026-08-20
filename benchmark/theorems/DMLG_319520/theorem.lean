import Mathlib.Data.Finset.Image
import Mathlib.Data.Set.Basic

namespace GenLimit

abbrev Language := Set ℕ

abbrev LanguageFamily := ℕ → Language

def Presents (stream : ℕ → ℕ) (L : Language) : Prop :=
  Set.range stream = L

def sample (stream : ℕ → ℕ) (t : ℕ) : Finset ℕ :=
  (Finset.range t).image stream

def Consistent (C : LanguageFamily) (stream : ℕ → ℕ) (t i : ℕ) : Prop :=
  ↑(sample stream t) ⊆ C i

theorem eventually_not_consistent_of_not_subset
    {C : LanguageFamily} {stream : ℕ → ℕ} {z i : ℕ}
    (hP : Presents stream (C z)) (hbad : ¬ C z ⊆ C i) :
    ∃ T, ∀ t, T ≤ t → ¬ Consistent C stream t i := by
  sorry

end GenLimit

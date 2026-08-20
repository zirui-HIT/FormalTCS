import GenLimit.Core.GenericGeneration

/-!
# Positive version spaces and closure

Paper-independent definitions and elementary facts for a class of languages
conditioned on a finite positive sample.
-/

namespace GenLimit.Generic

/-- Languages in `H` that contain the positive sample `S`. -/
def versionSpace (H : LanguageClass α) (S : Finset α) : Set (Language α) :=
  {L | L ∈ H ∧ (↑S : Set α) ⊆ L}

/-- The intersection of all languages in a positive version space. -/
def commonCore (H : LanguageClass α) (S : Finset α) : Language α :=
  {x | ∀ L, L ∈ versionSpace H S → x ∈ L}

/-- Positive closure, with `none` representing an empty version space. -/
noncomputable def closure
    (H : LanguageClass α) (S : Finset α) : Option (Language α) := by
  classical
  exact if (versionSpace H S).Nonempty then some (commonCore H S) else none

theorem mem_versionSpace_iff
    {H : LanguageClass α} {S : Finset α} {L : Language α} :
    L ∈ versionSpace H S ↔ L ∈ H ∧ (↑S : Set α) ⊆ L :=
  Iff.rfl

theorem closure_eq_none_iff
    {H : LanguageClass α} {S : Finset α} :
    closure H S = none ↔ ¬(versionSpace H S).Nonempty := by
  classical
  constructor
  · intro hnone hVS
    have hsome : closure H S = some (commonCore H S) := by
      simp [closure, hVS]
    rw [hnone] at hsome
    cases hsome
  · intro hVS
    simp [closure, hVS]

theorem closure_eq_some_iff
    {H : LanguageClass α} {S : Finset α} {C : Language α} :
    closure H S = some C ↔
      (versionSpace H S).Nonempty ∧ C = commonCore H S := by
  classical
  constructor
  · intro hcl
    by_cases hVS : (versionSpace H S).Nonempty
    · refine ⟨hVS, ?_⟩
      have hc : commonCore H S = C := by
        simpa [closure, hVS] using hcl
      exact hc.symm
    · simp [closure, hVS] at hcl
  · rintro ⟨hVS, rfl⟩
    simp [closure, hVS]

theorem sample_subset_of_streamIn
    {stream : Stream α} {L : Language α} (hstream : StreamIn stream L)
    (t : ℕ) : (↑(sample stream t) : Set α) ⊆ L := by
  intro x hx
  obtain ⟨s, -, rfl⟩ := mem_sample_iff.mp hx
  exact hstream ⟨s, rfl⟩

theorem target_mem_versionSpace
    {H : LanguageClass α} {L : Language α} (hLH : L ∈ H)
    {stream : Stream α} (hstream : StreamIn stream L) (t : ℕ) :
    L ∈ versionSpace H (sample stream t) :=
  ⟨hLH, sample_subset_of_streamIn hstream t⟩

theorem sample_subset_commonCore
    {H : LanguageClass α} {S : Finset α} :
    (↑S : Set α) ⊆ commonCore H S := by
  intro x hx L hL
  exact hL.2 hx

theorem commonCore_subset_of_mem_versionSpace
    {H : LanguageClass α} {S : Finset α} {L : Language α}
    (hL : L ∈ versionSpace H S) :
    commonCore H S ⊆ L := by
  intro x hx
  exact hx L hL

end GenLimit.Generic

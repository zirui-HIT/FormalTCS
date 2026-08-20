import GenLimit.Paper02_LearningTheory.Definitions
import GenLimit.Core.ClosureDimension
import Mathlib.Data.Countable.Defs

/-!
# Closure dimension and the uniform-generation construction

This file formalizes Definition 3.1, Lemmas 3.1 and 3.2, and Theorem 3.3
in Li--Raman--Tewari, *Generation through the
Lens of Learning Theory*, arXiv:2410.13714v5 / COLT 2025.

The paper treats the closure dimension as an element of
`ℕ ∪ {∞}`.  We avoid encoding that extended-number type: `HasClosureDimension
H d` states directly that `d` is the largest finite witness size.  Its first
conjunct is exactly the part used by the sufficiency proof.
-/

namespace GenLimit.LiRamanTewari

abbrev IsClosureWitness {α : Type*}
    (H : GenLimit.Generic.LanguageClass α) (S : Finset α) : Prop :=
  GenLimit.Generic.IsClosureWitness H S
abbrev ClosureDimensionAtMost {α : Type*}
    (H : GenLimit.Generic.LanguageClass α) (d : ℕ) : Prop :=
  GenLimit.Generic.ClosureDimensionAtMost H d
abbrev HasClosureDimension {α : Type*}
    (H : GenLimit.Generic.LanguageClass α) (d : ℕ) : Prop :=
  GenLimit.Generic.HasClosureDimension H d
abbrev HasFiniteClosureDimension {α : Type*}
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  GenLimit.Generic.HasFiniteClosureDimension H
abbrev HasInfiniteClosureDimension {α : Type*}
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  GenLimit.Generic.HasInfiniteClosureDimension H

theorem closure_witness_mono
    {H : GenLimit.Generic.LanguageClass α} {S T : Finset α}
    (hST : S ⊆ T) (hT : IsClosureWitness H T) :
    IsClosureWitness H S :=
  GenLimit.Generic.closure_witness_mono hST hT

/-- The exact-cardinality form used in the proof of Lemma 3.1.  It is the
formal counterpart of restricting an arbitrarily large witness
`z₁, ..., z_d⋆` to its first `d` elements. -/
theorem exists_closure_witness_card_eq
    {H : GenLimit.Generic.LanguageClass α}
    (hC : HasInfiniteClosureDimension H) (d : ℕ) :
    ∃ S : Finset α, S.card = d ∧ IsClosureWitness H S :=
  GenLimit.Generic.exists_closure_witness_card_eq hC d

/-- Quantitative core of Lemma 3.1: a finite closure witness of cardinality
`d` defeats a proposed generator at uniform threshold `d`.

This is the generator-wise lower bound used both by the paper's infinite
closure-dimension obstruction and by its sample-complexity comparison. -/
theorem closure_witness_defeats_uniform_threshold [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    {S : Finset α} {d : ℕ} (hSd : S.card = d)
    (hS : IsClosureWitness H S) (gen : GenLimit.Generic.Generator α) :
    ¬ IsUniformGeneratorAt gen H d := by
  classical
  intro hgen
  rcases hS with ⟨hVS, hcoreFinite⟩
  let C : Finset α := hcoreFinite.toFinset
  have hSC : S ⊆ C := by
    intro x hx
    change x ∈ hcoreFinite.toFinset
    rw [Set.Finite.mem_toFinset]
    exact sample_subset_commonCore hx
  let historyList : List α := S.toList ++ (C \ S).toList
  have hhistoryFinset : historyList.toFinset = C := by
    simp only [historyList, List.toFinset_append, Finset.toList_toFinset]
    exact Finset.union_sdiff_of_subset hSC
  let xhat : α := gen historyList.length (fun i ↦ historyList.get i)
  obtain ⟨L, hLVS, hbad⟩ :
      ∃ L, L ∈ versionSpace H S ∧
        (xhat ∈ commonCore H S ∨ xhat ∉ L) := by
    by_cases hx : xhat ∈ commonCore H S
    · obtain ⟨L, hL⟩ := hVS
      exact ⟨L, hL, Or.inl hx⟩
    · change ¬ ∀ K, K ∈ versionSpace H S → xhat ∈ K at hx
      push Not at hx
      obtain ⟨L, hLVS, hxL⟩ := hx
      exact ⟨L, hLVS, Or.inr hxL⟩
  have hLInfinite : L.Infinite := hUUS L hLVS.1
  obtain ⟨fallback, hfallback⟩ := hLInfinite.nonempty
  let stream : GenLimit.Generic.Stream α :=
    GenLimit.Generic.historyThenFallback historyList fallback
  have hstream : GenLimit.Generic.StreamIn stream L := by
    rintro x ⟨n, rfl⟩
    by_cases hn : n < historyList.length
    · have hmemHistory : historyList.get ⟨n, hn⟩ ∈ historyList :=
        List.get_mem historyList ⟨n, hn⟩
      have hmemC : historyList.get ⟨n, hn⟩ ∈ C := by
        rw [← hhistoryFinset]
        simpa only [List.mem_toFinset] using hmemHistory
      have hmemCore : historyList.get ⟨n, hn⟩ ∈ commonCore H S := by
        change historyList.get ⟨n, hn⟩ ∈ (hcoreFinite.toFinset : Finset α) at hmemC
        rwa [Set.Finite.mem_toFinset] at hmemC
      have hmemL : historyList.get ⟨n, hn⟩ ∈ L :=
        commonCore_subset_of_mem_versionSpace hLVS hmemCore
      simpa [stream, GenLimit.Generic.historyThenFallback, hn] using hmemL
    · simpa [stream, GenLimit.Generic.historyThenFallback, hn] using hfallback
  have hfirstSample : GenLimit.Generic.sample stream S.card = S := by
    calc
      GenLimit.Generic.sample stream S.card =
          GenLimit.Generic.sample
            (GenLimit.Generic.historyThenFallback S.toList fallback) S.card := by
        apply GenLimit.Generic.sample_eq_of_eq_on_prefix
        intro n hn
        have hnS : n < S.toList.length := by simpa using hn
        have hnHistory : n < historyList.length := by
          simp only [historyList, List.length_append, Finset.length_toList]
          omega
        change GenLimit.Generic.historyThenFallback historyList fallback n =
          GenLimit.Generic.historyThenFallback S.toList fallback n
        simp only [GenLimit.Generic.historyThenFallback, dif_pos hnHistory,
          dif_pos hnS, historyList]
        exact List.getElem_append_left hnS
      _ = GenLimit.Generic.sample
          (GenLimit.Generic.historyThenFallback S.toList fallback) S.toList.length := by
        rw [Finset.length_toList]
      _ = S.toList.toFinset :=
        GenLimit.Generic.sample_historyThenFallback_length S.toList fallback
      _ = S := Finset.toList_toFinset S
  have hfullSample : GenLimit.Generic.sample stream historyList.length = C := by
    change GenLimit.Generic.sample
      (GenLimit.Generic.historyThenFallback historyList fallback) historyList.length = C
    rw [GenLimit.Generic.sample_historyThenFallback_length, hhistoryFinset]
  have htriggerCard : (GenLimit.Generic.sample stream S.card).card = d := by
    rw [hfirstSample, hSd]
  have htime : S.card ≤ historyList.length := by
    simp [historyList]
  have hcorrect := hgen L hLVS.1 stream hstream S.card htriggerCard historyList.length htime
  have houtput : GenLimit.Generic.output gen stream historyList.length = xhat := by
    unfold GenLimit.Generic.output
    simp only [stream, xhat]
    congr 1
    funext i
    simp [GenLimit.Generic.historyThenFallback, i.isLt]
  rcases hbad with hxCore | hxL
  · apply hcorrect.2
    rw [hfullSample, houtput]
    change xhat ∈ hcoreFinite.toFinset
    rwa [Set.Finite.mem_toFinset]
  · apply hxL
    simpa only [houtput] using hcorrect.1

/-- Lemma 3.1 (`lem:closnec`), with the paper's quantifier order inherited
literally from `UniformlyGeneratable`: infinite closure dimension defeats
every proposed generator and every proposed uniform threshold. -/
theorem closure_dimension_necessity [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    (hC : HasInfiniteClosureDimension H) :
    ¬ UniformlyGeneratable H := by
  rintro ⟨gen, d, hgen⟩
  obtain ⟨S, hSd, hS⟩ := exists_closure_witness_card_eq hC d
  exact (closure_witness_defeats_uniform_threshold hUUS hSd hS gen) hgen

/-- The two direct encodings of the paper's alternatives `C(H) < ∞` and
`C(H) = ∞` are complementary.  The reverse implication chooses the largest
finite witness size by well-ordering the first cardinality at which witnesses
are uniformly absent. -/
theorem finite_closure_dimension_iff_not_infinite
    {H : GenLimit.Generic.LanguageClass α} :
    HasFiniteClosureDimension H ↔ ¬ HasInfiniteClosureDimension H :=
  GenLimit.Generic.finite_closure_dimension_iff_not_infinite

theorem core_diff_sample_infinite
    {H : GenLimit.Generic.LanguageClass α} {d : ℕ}
    (hC : ClosureDimensionAtMost H d) (S : Finset α)
    (hd : d < S.card) (hVS : (versionSpace H S).Nonempty) :
    (commonCore H S \ (↑S : Set α)).Infinite :=
  GenLimit.Generic.core_diff_sample_infinite hC S hd hVS

/-- The generator used in the proof of closure-dimension sufficiency.  Before
the threshold, or on an inconsistent history, it returns an arbitrary point.
After a consistent history containing more than `d` distinct examples, it
chooses a fresh element from the infinite common core. -/
noncomputable def closureGenerator [Nonempty α]
    (H : GenLimit.Generic.LanguageClass α) (d : ℕ)
    (hC : ClosureDimensionAtMost H d) : GenLimit.Generic.Generator α :=
  by
  classical
  exact fun _ xs =>
    let S := GenLimit.Generic.sequenceSample xs
    if hd : d < S.card then
      if hVS : (versionSpace H S).Nonempty then
        Classical.choose (core_diff_sample_infinite hC S hd hVS).nonempty
      else Classical.choice inferInstance
    else Classical.choice inferInstance

theorem closureGenerator_spec [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α} {d t : ℕ}
    (hC : ClosureDimensionAtMost H d) (xs : Fin t → α)
    (hd : d < (GenLimit.Generic.sequenceSample xs).card)
    (hVS : (versionSpace H (GenLimit.Generic.sequenceSample xs)).Nonempty) :
    closureGenerator H d hC t xs ∈
      commonCore H (GenLimit.Generic.sequenceSample xs) \
        (↑(GenLimit.Generic.sequenceSample xs) : Set α) := by
  classical
  simpa only [closureGenerator, dif_pos hd, dif_pos hVS] using
    Classical.choose_spec
      (core_diff_sample_infinite hC (GenLimit.Generic.sequenceSample xs) hd hVS).nonempty

/-- The named closure generator works at the paper's threshold `d + 1`.

The `Nonempty α` hypothesis makes explicit the paper's implicit assumption
that the example space contains an arbitrary fallback output. -/
theorem closureGenerator_isUniformGeneratorAt [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (_hUUS : UUS H) {d : ℕ}
    (hC : HasClosureDimension H d) :
    IsUniformGeneratorAt (closureGenerator H d hC.1) H (d + 1) := by
  let gen := closureGenerator H d hC.1
  intro L hLH stream hstream t ht s hts
  have hmono : GenLimit.Generic.sample stream t ⊆ GenLimit.Generic.sample stream s :=
    GenLimit.Generic.sample_mono hts
  have hcard : d < (GenLimit.Generic.sample stream s).card := by
    have hle : d + 1 ≤ (GenLimit.Generic.sample stream s).card := by
      rw [← ht]
      exact Finset.card_le_card hmono
    exact Nat.lt_of_succ_le hle
  have htarget : L ∈ versionSpace H (GenLimit.Generic.sample stream s) :=
    target_mem_versionSpace hLH hstream s
  have hVS : (versionSpace H (GenLimit.Generic.sample stream s)).Nonempty :=
    ⟨L, htarget⟩
  have hspec := closureGenerator_spec hC.1 (fun i : Fin s => stream i)
    (by simpa [GenLimit.Generic.sequenceSample_prefix] using hcard)
    (by simpa [GenLimit.Generic.sequenceSample_prefix] using hVS)
  rw [GenLimit.Generic.sequenceSample_prefix] at hspec
  constructor
  · exact commonCore_subset_of_mem_versionSpace htarget hspec.1
  · exact hspec.2

/-- Sufficiency in the uniform-generatability characterization
(`lem:clossuff`, constructive direction of Theorem 3.3). -/
theorem closure_dimension_sufficiency [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) {d : ℕ}
    (hC : HasClosureDimension H d) :
    ∃ gen : GenLimit.Generic.Generator α, IsUniformGeneratorAt gen H (d + 1) :=
  ⟨closureGenerator H d hC.1,
    closureGenerator_isUniformGeneratorAt hUUS hC⟩

/-- The paper-level corollary stated with `C(H) < ∞`, rather than with a
chosen numerical value of the closure dimension. -/
theorem finite_closure_dimension_implies_uniform [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    (hfinite : HasFiniteClosureDimension H) :
    UniformlyGeneratable H := by
  obtain ⟨d, hd⟩ := hfinite
  obtain ⟨gen, hgen⟩ := closure_dimension_sufficiency hUUS hd
  exact ⟨gen, d + 1, hgen⟩

/-- Theorem 3.3 (Characterization of Uniform Generatability).

The `Nonempty α` hypothesis records the paper's implicit nonempty example
universe, needed to define a generator even before its threshold is reached. -/
theorem uniform_generatability_iff_finite_closure_dimension
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) :
    UniformlyGeneratable H ↔ HasFiniteClosureDimension H := by
  constructor
  · intro hUniform
    apply finite_closure_dimension_iff_not_infinite.mpr
    intro hInfinite
    exact closure_dimension_necessity hUUS hInfinite hUniform
  · exact finite_closure_dimension_implies_uniform hUUS

end GenLimit.LiRamanTewari

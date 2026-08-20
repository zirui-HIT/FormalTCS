import GenLimit.Core.ClassGeneration
import GenLimit.Core.VersionSpace
import GenLimit.Core.ClassCovers

/-!
# #02 Learning Theory: paper-facing definitions

Source: the paper authors, the paper authors, and the paper authors, *Generation through the
Lens of Learning Theory*, arXiv:2410.13714v5 / COLT 2025.

The underlying notions are shared by later developments, so their canonical
definitions live in `GenLimit.Generic`.  These transparent aliases preserve
the source-facing `GenLimit.LiRamanTewari` API.
-/

namespace GenLimit.LiRamanTewari

abbrev UUS {α : Type*} (H : GenLimit.Generic.LanguageClass α) : Prop :=
  GenLimit.Generic.UUS H
abbrev versionSpace {α : Type*} (H : GenLimit.Generic.LanguageClass α)
    (S : Finset α) : Set (GenLimit.Generic.Language α) :=
  GenLimit.Generic.versionSpace H S
abbrev commonCore {α : Type*} (H : GenLimit.Generic.LanguageClass α)
    (S : Finset α) : GenLimit.Generic.Language α :=
  GenLimit.Generic.commonCore H S
noncomputable abbrev closure {α : Type*}
    (H : GenLimit.Generic.LanguageClass α) (S : Finset α) :
    Option (GenLimit.Generic.Language α) :=
  GenLimit.Generic.closure H S

abbrev IsLimitGenerator {α : Type*} (gen : GenLimit.Generic.Generator α)
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  GenLimit.Generic.IsLimitGenerator gen H
abbrev GeneratableInLimit {α : Type*}
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  GenLimit.Generic.GeneratableInLimit H
abbrev IsUniformGeneratorAt {α : Type*}
    (gen : GenLimit.Generic.Generator α) (H : GenLimit.Generic.LanguageClass α)
    (d : ℕ) : Prop :=
  GenLimit.Generic.IsUniformGeneratorAt gen H d
abbrev UniformlyGeneratable {α : Type*}
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  GenLimit.Generic.UniformlyGeneratable H
abbrev IsNonuniformGenerator {α : Type*}
    (gen : GenLimit.Generic.Generator α) (H : GenLimit.Generic.LanguageClass α) : Prop :=
  GenLimit.Generic.IsNonuniformGenerator gen H
abbrev NonuniformlyGeneratable {α : Type*}
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  GenLimit.Generic.NonuniformlyGeneratable H

abbrev IsNondecreasingCover {α : Type*}
    (H : GenLimit.Generic.LanguageClass α)
    (classes : ℕ → GenLimit.Generic.LanguageClass α) : Prop :=
  GenLimit.Generic.IsNondecreasingCover H classes
abbrev IsFiniteCover {α : Type*}
    (H : GenLimit.Generic.LanguageClass α) {n : ℕ}
    (classes : Fin n → GenLimit.Generic.LanguageClass α) : Prop :=
  GenLimit.Generic.IsFiniteCover H classes

theorem mem_versionSpace_iff
    {H : GenLimit.Generic.LanguageClass α} {S : Finset α}
    {L : GenLimit.Generic.Language α} :
    L ∈ versionSpace H S ↔ L ∈ H ∧ (↑S : Set α) ⊆ L :=
  GenLimit.Generic.mem_versionSpace_iff

theorem closure_eq_none_iff
    {H : GenLimit.Generic.LanguageClass α} {S : Finset α} :
    closure H S = none ↔ ¬(versionSpace H S).Nonempty :=
  GenLimit.Generic.closure_eq_none_iff

theorem closure_eq_some_iff
    {H : GenLimit.Generic.LanguageClass α} {S : Finset α}
    {C : GenLimit.Generic.Language α} :
    closure H S = some C ↔
      (versionSpace H S).Nonempty ∧ C = commonCore H S :=
  GenLimit.Generic.closure_eq_some_iff

theorem sample_subset_of_streamIn
    {stream : GenLimit.Generic.Stream α} {L : GenLimit.Generic.Language α}
    (hstream : GenLimit.Generic.StreamIn stream L) (t : ℕ) :
    (↑(GenLimit.Generic.sample stream t) : Set α) ⊆ L :=
  GenLimit.Generic.sample_subset_of_streamIn hstream t

theorem target_mem_versionSpace
    {H : GenLimit.Generic.LanguageClass α} {L : GenLimit.Generic.Language α}
    (hLH : L ∈ H) {stream : GenLimit.Generic.Stream α}
    (hstream : GenLimit.Generic.StreamIn stream L) (t : ℕ) :
    L ∈ versionSpace H (GenLimit.Generic.sample stream t) :=
  GenLimit.Generic.target_mem_versionSpace hLH hstream t

theorem sample_subset_commonCore
    {H : GenLimit.Generic.LanguageClass α} {S : Finset α} :
    (↑S : Set α) ⊆ commonCore H S :=
  GenLimit.Generic.sample_subset_commonCore

theorem commonCore_subset_of_mem_versionSpace
    {H : GenLimit.Generic.LanguageClass α} {S : Finset α}
    {L : GenLimit.Generic.Language α} (hL : L ∈ versionSpace H S) :
    commonCore H S ⊆ L :=
  GenLimit.Generic.commonCore_subset_of_mem_versionSpace hL

end GenLimit.LiRamanTewari

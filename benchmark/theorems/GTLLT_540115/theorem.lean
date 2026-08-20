import Mathlib

namespace GenLimit.Generic

abbrev LanguageClass (α : Type*) := Set (Set α)

abbrev Generator (α : Type*) := (n : ℕ) → (Fin n → α) → α

abbrev Stream (α : Type*) := ℕ → α

noncomputable def sample {α : Type*} (stream : Stream α) (t : ℕ) : Finset α := by
  classical
  exact (Finset.range t).image stream

def StreamIn {α : Type*} (stream : Stream α) (L : Set α) : Prop :=
  ∀ n, stream n ∈ L

def output {α : Type*} (gen : Generator α) (stream : Stream α) (s : ℕ) : α :=
  gen s (fun i : Fin s => stream i)

def CorrectAt {α : Type*} (gen : Generator α) (L : Set α)
    (stream : Stream α) (s : ℕ) : Prop :=
  output gen stream s ∈ L ∧ output gen stream s ∉ sample stream s

def UUS {α : Type*} (H : LanguageClass α) : Prop :=
  ∀ L, L ∈ H → L.Infinite

def IsUniformGeneratorAt {α : Type*}
    (gen : Generator α) (H : LanguageClass α) (d : ℕ) : Prop :=
  ∀ L, L ∈ H → ∀ stream : Stream α, StreamIn stream L →
    ∀ t, (sample stream t).card = d →
      ∀ s, t ≤ s → CorrectAt gen L stream s

def UniformlyGeneratable {α : Type*} (H : LanguageClass α) : Prop :=
  ∃ gen : Generator α, ∃ d : ℕ, IsUniformGeneratorAt gen H d

def versionSpace {α : Type*} (H : LanguageClass α) (S : Finset α) : Set (Set α) :=
  {L | L ∈ H ∧ (↑S : Set α) ⊆ L}

def commonCore {α : Type*} (H : LanguageClass α) (S : Finset α) : Set α :=
  {x | ∀ L ∈ versionSpace H S, x ∈ L}

def IsClosureWitness {α : Type*} (H : LanguageClass α) (S : Finset α) : Prop :=
  (versionSpace H S).Nonempty ∧ (commonCore H S).Finite

def ClosureDimensionAtMost {α : Type*} (H : LanguageClass α) (d : ℕ) : Prop :=
  ∀ S : Finset α, IsClosureWitness H S → S.card ≤ d

def HasClosureDimension {α : Type*} (H : LanguageClass α) (d : ℕ) : Prop :=
  ClosureDimensionAtMost H d ∧ ∃ S : Finset α, S.card = d ∧ IsClosureWitness H S

def HasFiniteClosureDimension {α : Type*} (H : LanguageClass α) : Prop :=
  ∃ d : ℕ, HasClosureDimension H d

end GenLimit.Generic

namespace GenLimit.LiRamanTewari

open GenLimit.Generic

theorem uniform_generatability_iff_finite_closure_dimension
    {α : Type*} [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) :
    UniformlyGeneratable H ↔ HasFiniteClosureDimension H := by sorry

end GenLimit.LiRamanTewari

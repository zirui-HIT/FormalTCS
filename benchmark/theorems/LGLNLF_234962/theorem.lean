import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.List.OfFn

structure generation_language where
  carrier : Set Int
  infinite_carrier : carrier.Infinite

abbrev language_collection := Set generation_language

abbrev sample_free_generator := Nat → Int

def generated_before (z : sample_free_generator) (t : Nat) : Set Int :=
  {u | ∃ i < t, z i = u}

def sample_free_fresh_for
    (z : sample_free_generator) (K : generation_language) (t : Nat) : Prop :=
  z t ∈ K.carrier ∧ z t ∉ generated_before z t

def nonuniformly_generatable_without_samples (C : language_collection) : Prop :=
  ∃ z : sample_free_generator, ∀ K ∈ C, ∃ t₀ : Nat, ∀ t ≥ t₀,
    sample_free_fresh_for z K t

def uniformly_generatable_without_samples (C : language_collection) : Prop :=
  ∃ z : sample_free_generator, ∃ t₀ : Nat, ∀ K ∈ C, ∀ t ≥ t₀,
    sample_free_fresh_for z K t

abbrev sample_based_generator := List Int → Int

def enumerates_language (x : Nat → Int) (K : generation_language) : Prop :=
  Set.range x = K.carrier

def enumeration_prefix (x : Nat → Int) (t : Nat) : List Int :=
  List.ofFn (fun i : Fin (t + 1) => x i.val)

def seen_prefix (x : Nat → Int) (t : Nat) : Set Int :=
  {u | ∃ i ≤ t, x i = u}

def sample_based_fresh_for
    (G : sample_based_generator) (x : Nat → Int)
    (K : generation_language) (t : Nat) : Prop :=
  G (enumeration_prefix x t) ∈ K.carrier ∧
    G (enumeration_prefix x t) ∉ seen_prefix x t

def generates_in_limit (G : sample_based_generator) (C : language_collection) : Prop :=
  ∀ K ∈ C, ∀ x : Nat → Int, enumerates_language x K →
    ∃ t₀ : Nat, ∀ t ≥ t₀, sample_based_fresh_for G x K t

def generatable_in_limit (C : language_collection) : Prop :=
  ∃ G : sample_based_generator, generates_in_limit G C

theorem union_ungen :
    ∃ C₁ C₂ : language_collection,
      nonuniformly_generatable_without_samples C₁ ∧
      uniformly_generatable_without_samples C₂ ∧
      ¬ generatable_in_limit (C₁ ∪ C₂) := by sorry

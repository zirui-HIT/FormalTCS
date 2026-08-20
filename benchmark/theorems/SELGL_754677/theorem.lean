import Mathlib.Computability.DFA
import Mathlib.Data.Set.Card

structure finite_dfa (α : Type) where
  stateCount : ℕ
  automaton : DFA α (Fin stateCount)

def finite_dfa_language {α : Type} (A : finite_dfa α) : Language α :=
  A.automaton.accepts

structure bounded_dfa (α : Type) (s : ℕ) where
  stateCount : ℕ
  stateCount_le : stateCount ≤ s
  automaton : DFA α (Fin stateCount)

def bounded_dfa_language {α : Type} {s : ℕ} (A : bounded_dfa α s) : Language α :=
  A.automaton.accepts

abbrev language_enumeration {α : Type} (K : Language α) :=
  {w : ℕ → {x : List α // x ∈ K} // Function.Surjective w}

def stream_prefix {α : Type} {K : Language α} (w : language_enumeration K) (t : ℕ) :
    List (Option α) :=
  (List.ofFn fun i : Fin t => (w.1 i).1).flatMap
    fun x => x.map some ++ [none]

structure streaming_generator (α : Type) (s : ℕ) where
  memoryBits : ℕ
  initial : Fin memoryBits → Bool
  step : (Fin memoryBits → Bool) → Option α → (Fin memoryBits → Bool)
  output : (Fin memoryBits → Bool) → finite_dfa α

structure generator_family where
  generator : ∀ {α : Type} [Fintype α] (s : ℕ) (hs : 0 < s), streaming_generator α s

def streaming_generator_run {α : Type} {s : ℕ} (G : streaming_generator α s)
    (input : List (Option α)) : Fin G.memoryBits → Bool :=
  input.foldl G.step G.initial

def generated_language (F : generator_family) {α : Type} [Fintype α] (s : ℕ)
    (hs : 0 < s) (input : List (Option α)) : Language α :=
  finite_dfa_language
    ((F.generator s hs).output (streaming_generator_run (F.generator s hs) input))

def uses_polynomial_space (F : generator_family) : Prop :=
  ∃ C d : ℕ,
    ∀ {α : Type} [Fintype α] (s : ℕ) (hs : 0 < s),
      (F.generator (α := α) s hs).memoryBits ≤
        C * (s + Fintype.card α + 1) ^ d

def eventually_no_hallucination (F : generator_family) : Prop :=
  ∀ {α : Type} [Fintype α] (s : ℕ) (hs : 0 < s) (target : bounded_dfa α s)
    (w : language_enumeration (bounded_dfa_language target)),
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      generated_language F s hs (stream_prefix w t) ≤
        bounded_dfa_language target

def has_generation_gap_order (F : generator_family) : Prop :=
  ∀ (s : ℕ) (hs : 0 < s), ∃ C k₀ : ℕ,
    ∀ {α : Type} [Fintype α], k₀ ≤ Fintype.card α →
      ∀ (target : bounded_dfa α s)
        (w : language_enumeration (bounded_dfa_language target)),
        ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
          (bounded_dfa_language target \
            generated_language F s hs (stream_prefix w t)).Finite ∧
          (bounded_dfa_language target \
            generated_language F s hs (stream_prefix w t)).ncard ≤
              C * Fintype.card α ^ (2 * s - 2)

theorem space_efficient_language_generation :
    ∃ F : generator_family,
      uses_polynomial_space F ∧
      eventually_no_hallucination F ∧
      has_generation_gap_order F := by sorry

import Mathlib.Computability.Language
import Mathlib.Data.Set.Countable
import Mathlib.Data.Fintype.Card

abbrev palette (α : Type*) [Fintype α] := Fin (Fintype.card α + 1)

abbrev trace_coloring (α : Type*) [Fintype α] := List α → palette α

def color_trace {α : Type*} [Fintype α] (c : trace_coloring α) (x : List α) : List (palette α) :=
  (List.range (x.length + 1)).map (fun i => c (x.take i))

abbrev annotated_string (α : Type*) [Fintype α] := List α × List (palette α)

abbrev coloring_family (α : Type*) [Fintype α] := Language α → trace_coloring α

def is_text {α : Type*} (K : Language α) (t : ℕ → List α) : Prop :=
  ∀ x, x ∈ K ↔ ∃ n, t n = x

abbrev learner (α : Type*) [Fintype α] := List (annotated_string α) → Language α

def annotated_history {α : Type*} [Fintype α] (c : trace_coloring α) (t : ℕ → List α)
    (n : ℕ) : List (annotated_string α) :=
  (List.range n).map (fun i => (t i, color_trace c (t i)))

def identifies_in_limit {α : Type*} [Fintype α] (c : trace_coloring α) (t : ℕ → List α)
    (A : learner α) (K : Language α) : Prop :=
  ∃ tstar, ∀ n, tstar ≤ n → A (annotated_history c t n) = K

def identifiable_with_traces {α : Type*} [Fintype α] (C : Set (Language α)) : Prop :=
  ∃ (A : learner α) (cf : coloring_family α),
    ∀ K ∈ C, ∀ t : ℕ → List α, is_text K t → identifies_in_limit (cf K) t A K

theorem main_theorem {α : Type*} [Fintype α] (C : Set (Language α))
    (hCountable : C.Countable) (hNonempty : ∀ L ∈ C, L.Nonempty) :
    identifiable_with_traces C := by sorry

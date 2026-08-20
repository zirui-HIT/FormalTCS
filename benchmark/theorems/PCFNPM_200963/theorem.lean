import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.MetricSpace.Defs

set_option linter.all false
set_option maxHeartbeats 500000

def planar_open_segment (x y : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {z | ∃ t : ℝ, 0 < t ∧ t < 1 ∧ z = (1 - t) • x + t • y}

def straight_line_planar {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ position : V → ℝ × ℝ,
    Function.Injective position ∧
      (∀ ⦃a b v : V⦄, G.Adj a b → v ≠ a → v ≠ b →
        position v ∉ planar_open_segment (position a) (position b)) ∧
      (∀ ⦃a b c d : V⦄, G.Adj a b → G.Adj c d →
        ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
          Disjoint (planar_open_segment (position a) (position b))
            (planar_open_segment (position c) (position d)))

def walk_metric_length {V : Type*} [MetricSpace V] {G : SimpleGraph V} {u v : V}
    (walk : G.Walk u v) : ℝ :=
  (walk.darts.map fun dart => dist dart.fst dart.snd).sum

def is_planar_metric (V : Type*) [Fintype V] [MetricSpace V] : Prop :=
  ∃ G : SimpleGraph V,
    straight_line_planar G ∧ G.Connected ∧
      ∀ u v : V,
        (∀ walk : G.Walk u v, dist u v ≤ walk_metric_length walk) ∧
          ∃ walk : G.Walk u v, walk_metric_length walk = dist u v

def furthest_neighbor_radius {V : Type*} [MetricSpace V] (P : Finset V)
    (hP : P.Nonempty) (v : V) : ℝ :=
  P.sup' hP fun p => dist v p

def is_furthest_neighbor_coreset {V : Type*} [MetricSpace V] (P : Finset V)
    (hP : P.Nonempty) (ε : ℝ) (Q : Finset V) : Prop :=
  Q ⊆ P ∧ ∀ v : V, ∃ q ∈ Q,
    (1 - ε) * furthest_neighbor_radius P hP v ≤ dist v q

def polynomial_time_computable {A B : Type} (f : A → B) : Prop :=
  ∃ (inputAlphabet outputAlphabet : Type)
      (_ : Fintype inputAlphabet) (_ : Fintype outputAlphabet)
      (encodeInput : A → List inputAlphabet) (encodeOutput : B → List outputAlphabet),
    Nonempty (@Turing.TM2ComputableInPolyTime A B inputAlphabet outputAlphabet
      encodeInput encodeOutput f)

def is_polynomial_furthest_coreset_constructor {V : Type*} [MetricSpace V]
    (C k : ℕ) (construct : Finset V → ℝ → Finset V) : Prop :=
  ∀ (P : Finset V) (hP : P.Nonempty) (ε : ℝ), 0 < ε → ε < 1 →
    is_furthest_neighbor_coreset P hP ε (construct P ε) ∧
      (construct P ε).card ≤ C * (Nat.ceil ε⁻¹) ^ k

theorem polynomial_coreset_for_furthest_neighbor :
    ∃ C k : ℕ, ∀ (V : Type) [Fintype V] [MetricSpace V],
      is_planar_metric V →
        ∃ construct : Finset V → ℝ → Finset V,
          polynomial_time_computable
              (fun input : Finset V × ℝ => construct input.1 input.2) ∧
            is_polynomial_furthest_coreset_constructor C k construct := by sorry

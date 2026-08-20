import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.Convex.Segment
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Real.Basic

set_option linter.all false
set_option maxHeartbeats 500000

def points_in_convex_position {n : ℕ} (p : Fin n → ℝ × ℝ) : Prop :=
  ConvexIndependent ℝ p

def noncrossing_straight_line_graph {n : ℕ} (p : Fin n → ℝ × ℝ)
    (G : SimpleGraph (Fin n)) : Prop :=
  ∀ ⦃a b c d : Fin n⦄, G.Adj a b → G.Adj c d →
    a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    Disjoint (openSegment ℝ (p a) (p b)) (openSegment ℝ (p c) (p d))

def noncrossing_spanning_tree {n : ℕ} (p : Fin n → ℝ × ℝ) :=
  {G : SimpleGraph (Fin n) // G.IsTree ∧ noncrossing_straight_line_graph p G}

def tree_flip {n : ℕ} (G H : SimpleGraph (Fin n)) : Prop :=
  ∃ e e' : Sym2 (Fin n),
    e ∈ G.edgeSet ∧ e ∉ H.edgeSet ∧
    e' ∈ H.edgeSet ∧ e' ∉ G.edgeSet ∧
    G.edgeSet \ {e} = H.edgeSet \ {e'}

def noncrossing_tree_flip_graph {n : ℕ} (p : Fin n → ℝ × ℝ) :
    SimpleGraph (noncrossing_spanning_tree p) :=
  SimpleGraph.fromRel fun T T' => tree_flip T.1 T'.1

noncomputable def flip_distance {n : ℕ} {p : Fin n → ℝ × ℝ}
    (T T' : noncrossing_spanning_tree p) : ℕ :=
  (noncrossing_tree_flip_graph p).dist T T'

theorem main_lower_bound :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      ∃ p : Fin n → ℝ × ℝ,
        points_in_convex_position p ∧
        ∃ T T' : noncrossing_spanning_tree p,
          (14 / 9 : ℝ) * (n : ℝ) - C ≤ (flip_distance T T' : ℝ) := by sorry

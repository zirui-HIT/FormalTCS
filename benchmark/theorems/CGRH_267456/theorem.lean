import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.Digraph.Orientation
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Nat.Log

set_option linter.all false
set_option maxHeartbeats 500000

def directed_reachable {V : Type*} (G : Digraph V) (u v : V) : Prop :=
  Relation.ReflTransGen G.Adj u v

def reachability_embedding {V : Type*} (G : Digraph V) (d : ℕ)
    (a b : V → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ u v, 0 < inner ℝ (a u) (b v) ↔ directed_reachable G u v

def admits_reachability_embedding {V : Type*} (G : Digraph V) (d : ℕ) : Prop :=
  ∃ a b : V → EuclideanSpace ℝ (Fin d), reachability_embedding G d a b

structure directed_tree_decomposition {V : Type*} [DecidableEq V] (G : Digraph V) where
  BagIndex : Type
  [bagIndexFintype : Fintype BagIndex]
  [bagIndexDecidableEq : DecidableEq BagIndex]
  tree : SimpleGraph BagIndex
  treeIsTree : tree.IsTree
  bag : BagIndex → Finset V
  vertexCover : ∀ v, ∃ i, v ∈ bag i
  edgeCover : ∀ ⦃u v⦄, G.toSimpleGraphInclusive.Adj u v →
    ∃ i, u ∈ bag i ∧ v ∈ bag i
  runningIntersection : ∀ v, (tree.induce {i | v ∈ bag i}).Preconnected

def has_treewidth_at_most {V : Type*} [DecidableEq V] (G : Digraph V) (t : ℕ) : Prop :=
  ∃ D : directed_tree_decomposition G, ∀ i, (D.bag i).card ≤ t + 1

theorem dig :
    ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : Digraph V) (n t : ℕ),
      Fintype.card V = n →
      has_treewidth_at_most G t →
      ∃ d : ℕ,
        d ≤ C * (t + 1) * (Nat.clog 2 n + 1) ∧ admits_reachability_embedding G d := by sorry

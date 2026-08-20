import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option linter.all false
set_option maxHeartbeats 500000

structure edge_weighted_tree (V : Type*) where
  graph : SimpleGraph V
  isTree : graph.IsTree
  weight : Sym2 V → ℝ

noncomputable def tree_dist {V : Type*} (T : edge_weighted_tree V) (x y : V) : ℝ :=
  (((T.isTree.existsUnique_path x y).exists.choose).edges.map T.weight).sum

structure plane_tree where
  vertex : Type
  tree : edge_weighted_tree vertex
  place : EuclideanSpace ℝ (Fin 2) → vertex

def two_tree_cover (P : Set (EuclideanSpace ℝ (Fin 2)))
    (T₁ T₂ : plane_tree) : Prop :=
  ∀ x ∈ P, ∀ y ∈ P,
    (dist x y ≤ tree_dist T₁.tree (T₁.place x) (T₁.place y) ∧
        tree_dist T₁.tree (T₁.place x) (T₁.place y) ≤ Real.sqrt 26 * dist x y) ∨
      (dist x y ≤ tree_dist T₂.tree (T₂.place x) (T₂.place y) ∧
        tree_dist T₂.tree (T₂.place x) (T₂.place y) ≤ Real.sqrt 26 * dist x y)

theorem steiner (P : Set (EuclideanSpace ℝ (Fin 2))) (hP : P.Finite) :
    ∃ T₁ T₂ : plane_tree, two_tree_cover P T₁ T₂ := by sorry

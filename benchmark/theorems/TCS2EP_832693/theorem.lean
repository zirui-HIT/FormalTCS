import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option maxHeartbeats 500000

abbrev euclidean_plane := EuclideanSpace ℝ (Fin 2)

noncomputable def euclidean_polyline_length (vertices : List euclidean_plane) : ℝ :=
  ((vertices.zip vertices.tail).map (fun edge => dist edge.1 edge.2)).sum

structure euclidean_spanning_tree (P : Finset euclidean_plane) where
  graph : SimpleGraph ↥P
  preconnected : graph.Preconnected
  isAcyclic : graph.IsAcyclic

noncomputable def euclidean_walk_length {P : Finset euclidean_plane} {G : SimpleGraph ↥P}
    {x y : ↥P} (walk : G.Walk x y) : ℝ :=
  euclidean_polyline_length (walk.support.map (fun z => z.1))

noncomputable def euclidean_tree_distance {P : Finset euclidean_plane}
    (tree : euclidean_spanning_tree P) (x y : ↥P) : ℝ :=
  sInf (Set.range (fun walk : tree.graph.Walk x y => euclidean_walk_length walk))

structure euclidean_tree_cover (P : Finset euclidean_plane) where
  first : euclidean_spanning_tree P
  second : euclidean_spanning_tree P

noncomputable def euclidean_tree_cover_distance {P : Finset euclidean_plane}
    (cover : euclidean_tree_cover P) (x y : ↥P) : ℝ :=
  min (euclidean_tree_distance cover.first x y)
    (euclidean_tree_distance cover.second x y)

def euclidean_tree_cover_has_stretch {P : Finset euclidean_plane}
    (cover : euclidean_tree_cover P) (t : ℝ) : Prop :=
  ∀ x y : ↥P,
    euclidean_tree_cover_distance cover x y ≤ t * dist (x.1 : euclidean_plane) y.1

theorem tree_cover_size_two_for_euclidean_plane :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ P : Finset euclidean_plane,
        ∃ cover : euclidean_tree_cover P,
          euclidean_tree_cover_has_stretch cover C := by sorry

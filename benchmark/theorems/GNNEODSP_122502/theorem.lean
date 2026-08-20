import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Iterate

set_option linter.all false
set_option maxHeartbeats 500000

structure attributed_graph where
  vertexCount : ℕ
  adjacency : SimpleGraph (Fin vertexCount)
  edgeWeight : Sym2 (Fin vertexCount) → ℝ
  nodeFeature : Fin vertexCount → ℝ
  source : Fin vertexCount
  beta : ℝ

noncomputable def graph_edge_finset (G : attributed_graph) : Finset (Sym2 (Fin G.vertexCount)) := by
  classical
  exact Finset.univ.filter fun e => e ∈ G.adjacency.edgeSet

noncomputable def graph_neighbor_finset (G : attributed_graph) (v : Fin G.vertexCount) :
    Finset (Fin G.vertexCount) := by
  classical
  exact Finset.univ.filter fun u => G.adjacency.Adj v u

def graph_space (G : attributed_graph) : Prop :=
  (∀ e ∈ graph_edge_finset G, 0 ≤ G.edgeWeight e) ∧
    G.nodeFeature G.source = 0 ∧
      (∀ v, v ≠ G.source → G.nodeFeature v = G.beta) ∧
        (∑ e ∈ graph_edge_finset G, G.edgeWeight e) < G.beta

noncomputable def bellman_ford_step (G : attributed_graph)
    (x : Fin G.vertexCount → ℝ) (v : Fin G.vertexCount) : ℝ :=
  let candidates := insert v (graph_neighbor_finset G v)
  candidates.inf' (by simp [candidates]) fun u =>
    if u = v then x v else x u + G.edgeWeight s(u, v)

noncomputable def bellman_ford_iterate (G : attributed_graph) (K : ℕ) :
    Fin G.vertexCount → ℝ :=
  Nat.iterate (bellman_ford_step G) K G.nodeFeature

structure scalar_relu_layer (width : ℕ) where
  weight : Matrix (Fin width) (Fin width) ℝ
  bias : Fin width → ℝ

structure scalar_relu_mlp where
  depth : ℕ
  width : ℕ
  leftInput : Fin width
  rightInput : Fin width
  output : Fin width
  leftInput_ne_rightInput : leftInput ≠ rightInput
  layer : Fin depth → scalar_relu_layer width

noncomputable def scalar_relu_mlp_state (P : scalar_relu_mlp) (x y : ℝ) :
    ℕ → Fin P.width → ℝ
  | 0 => fun i => if i = P.leftInput then x else if i = P.rightInput then y else 0
  | k + 1 =>
      if hk : k < P.depth then
        fun i => max 0
          (((P.layer ⟨k, hk⟩).weight.mulVec (scalar_relu_mlp_state P x y k)) i +
            (P.layer ⟨k, hk⟩).bias i)
      else scalar_relu_mlp_state P x y k

noncomputable def scalar_relu_mlp_eval (P : scalar_relu_mlp) (x y : ℝ) : ℝ :=
  scalar_relu_mlp_state P x y P.depth P.output

noncomputable def scalar_relu_mlp_nonzero_parameters (P : scalar_relu_mlp) : ℕ := by
  classical
  exact ∑ ℓ : Fin P.depth,
    ((Finset.univ.filter fun ij : Fin P.width × Fin P.width =>
      (P.layer ℓ).weight ij.1 ij.2 ≠ 0).card +
    (Finset.univ.filter fun i : Fin P.width => (P.layer ℓ).bias i ≠ 0).card)

structure min_agg_gnn where
  layerCount : ℕ
  mlpDepth : ℕ
  messageMLP : Fin layerCount → scalar_relu_mlp
  updateMLP : Fin layerCount → scalar_relu_mlp
  messageDepth : ∀ ℓ, (messageMLP ℓ).depth = mlpDepth
  updateDepth : ∀ ℓ, (updateMLP ℓ).depth = mlpDepth
  hiddenFeature : (ℓ : ℕ) → (G : attributed_graph) → Fin G.vertexCount → ℝ
  hiddenFeature_zero : ∀ G v, hiddenFeature 0 G v = G.nodeFeature v
  hiddenFeature_succ : ∀ (ℓ : Fin layerCount) (G : attributed_graph)
      (v : Fin G.vertexCount),
    hiddenFeature (ℓ.1 + 1) G v =
      scalar_relu_mlp_eval (updateMLP ℓ)
        ((insert v (graph_neighbor_finset G v)).inf' (by simp)
          (fun u => scalar_relu_mlp_eval (messageMLP ℓ)
            (hiddenFeature ℓ.1 G u)
            (if u = v then 0 else G.edgeWeight s(u, v))))
        (hiddenFeature ℓ.1 G v)

noncomputable def min_agg_gnn_nonzero_parameters (A : min_agg_gnn) : ℕ :=
  ∑ ℓ : Fin A.layerCount,
    (scalar_relu_mlp_nonzero_parameters (A.messageMLP ℓ) +
      scalar_relu_mlp_nonzero_parameters (A.updateMLP ℓ))

def gnn_output (A : min_agg_gnn) (G : attributed_graph) (v : Fin G.vertexCount) : ℝ :=
  A.hiddenFeature A.layerCount G v

structure graph_training_set where
  size : ℕ
  graph : Fin size → attributed_graph

structure distinguished_training_set (K : ℕ) where
  scalingSize : ℕ
  scalingGraph : Fin scalingSize → attributed_graph
  pathZeroOneGraph : attributed_graph
  pathOneTwoGraph : attributed_graph
  hopGraph : attributed_graph

noncomputable def scaling_training_family (K : ℕ) (i : Fin (K + 1)) : attributed_graph :=
  { vertexCount := 2
    adjacency := SimpleGraph.pathGraph 2
    edgeWeight := fun e =>
      if e = s((0 : Fin 2), (1 : Fin 2)) then
        (((i : ℕ) : ℝ) + 1) / ((K : ℝ) + 1)
      else 0
    nodeFeature := fun v => if v = (0 : Fin 2) then 0 else 2
    source := 0
    beta := 2 }

noncomputable def path_zero_one_training_graph : attributed_graph :=
  { vertexCount := 2
    adjacency := SimpleGraph.pathGraph 2
    edgeWeight := fun e => if e = s((0 : Fin 2), (1 : Fin 2)) then 1 else 0
    nodeFeature := fun v => if v = (0 : Fin 2) then 0 else 2
    source := 0
    beta := 2 }

noncomputable def path_one_two_training_graph : attributed_graph :=
  { vertexCount := 3
    adjacency := SimpleGraph.pathGraph 3
    edgeWeight := fun e => if e = s((0 : Fin 3), (1 : Fin 3)) then 1 else 0
    nodeFeature := fun v => if v = (1 : Fin 3) then 0 else 2
    source := 1
    beta := 2 }

noncomputable def hop_training_graph (K : ℕ) : attributed_graph :=
  { vertexCount := K + 1
    adjacency := SimpleGraph.pathGraph (K + 1)
    edgeWeight := fun _ => 1
    nodeFeature := fun v => if v = (0 : Fin (K + 1)) then 0 else (K : ℝ) + 1
    source := ⟨0, Nat.zero_lt_succ K⟩
    beta := (K : ℝ) + 1 }

noncomputable def canonical_distinguished_training_set (K : ℕ) :
    distinguished_training_set K :=
  { scalingSize := K + 1
    scalingGraph := scaling_training_family K
    pathZeroOneGraph := path_zero_one_training_graph
    pathOneTwoGraph := path_one_two_training_graph
    hopGraph := hop_training_graph K }

def contains_distinguished_training_set (K : ℕ) (T : graph_training_set) : Prop :=
  let D := canonical_distinguished_training_set K
  (∀ i : Fin D.scalingSize, ∃ j : Fin T.size, D.scalingGraph i = T.graph j) ∧
    (∃ j : Fin T.size, D.pathZeroOneGraph = T.graph j) ∧
      (∃ j : Fin T.size, D.pathOneTwoGraph = T.graph j) ∧
        ∃ j : Fin T.size, D.hopGraph = T.graph j

noncomputable def reachable_vertex_count (G : attributed_graph) : ℕ := by
  classical
  exact (Finset.univ.filter fun v => G.adjacency.Reachable G.source v).card

noncomputable def total_reachable_nodes (T : graph_training_set) : ℕ :=
  ∑ i : Fin T.size, reachable_vertex_count (T.graph i)

noncomputable def training_mean_absolute_error (T : graph_training_set) (K : ℕ)
    (A : min_agg_gnn) : ℝ := by
  classical
  exact if total_reachable_nodes T = 0 then 0 else
    (∑ i : Fin T.size, ∑ v : Fin (T.graph i).vertexCount,
      if (T.graph i).adjacency.Reachable (T.graph i).source v then
        |gnn_output A (T.graph i) v - bellman_ford_iterate (T.graph i) K v|
      else 0) / (total_reachable_nodes T : ℝ)

noncomputable def regularized_loss (T : graph_training_set) (K : ℕ)
    (A : min_agg_gnn) (η : ℝ) : ℝ :=
  training_mean_absolute_error T K A + η * min_agg_gnn_nonzero_parameters A

noncomputable def global_regularized_minimum (T : graph_training_set) (K L m : ℕ)
    (η : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ A : min_agg_gnn,
    A.layerCount = L ∧ A.mlpDepth = m ∧ regularized_loss T K A η = r}

def loss_within (T : graph_training_set) (K L m : ℕ) (A : min_agg_gnn)
    (ε η : ℝ) : Prop :=
  regularized_loss T K A η ≤ global_regularized_minimum T K L m η + ε

def sparse_parameter_count (m L K : ℕ) : ℕ :=
  m * L + m * K + K

theorem main_deep
    (T : graph_training_set) (A : min_agg_gnn)
    (K L m M : ℕ) (ε η : ℝ)
    (hK : 0 < K) (hKL : K ≤ L) (hmpos : 0 < m)
    (hM : M = total_reachable_nodes T)
    (hcontains : contains_distinguished_training_set K T)
    (hspace : ∀ i : Fin T.size, graph_space (T.graph i))
    (hL : A.layerCount = L) (hm : A.mlpDepth = m)
    (hε : 0 < ε) (hεη : ε < η)
    (hη : η < 1 / (2 * (M : ℝ) * (sparse_parameter_count m L K : ℝ)))
    (hloss : loss_within T K L m A ε η) :
    ∀ (G : attributed_graph), graph_space G → ∀ v : Fin G.vertexCount,
      (1 - (M : ℝ) * ε) * bellman_ford_iterate G K v ≤ gnn_output A G v ∧
        gnn_output A G v ≤
          (1 + (M : ℝ) * ε) * bellman_ford_iterate G K v := by sorry

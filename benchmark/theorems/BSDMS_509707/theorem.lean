import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Nat.Choose.Basic

set_option linter.all false
set_option maxHeartbeats 500000

def weighted_walk_length {V : Type*} (G : SimpleGraph V) (weight : V → V → ℝ)
    {u v : V} (q : G.Walk u v) : ℝ :=
  (q.darts.map fun e => weight e.fst e.snd).sum

structure edge_weighted_graph (V : Type*) [MetricSpace V] where
  graph : SimpleGraph V
  weight : V → V → ℝ
  weight_symm : ∀ u v, weight u v = weight v u
  weight_pos : ∀ {u v}, graph.Adj u v → 0 < weight u v
  distance_realized :
    ∀ u v, ∃ q : graph.Walk u v, weighted_walk_length graph weight q = dist u v
  distance_minimal :
    ∀ {u v} (q : graph.Walk u v), dist u v ≤ weighted_walk_length graph weight q

def has_clique_minor {V : Type*} (G : SimpleGraph V) (h : ℕ) : Prop :=
  ∃ branch : Fin h → Set V,
    (∀ i, (G.induce (branch i)).Connected) ∧
    (∀ i j, i ≠ j → Disjoint (branch i) (branch j)) ∧
    (∀ i j, i ≠ j →
      ∃ u ∈ branch i, ∃ v ∈ branch j, G.Adj u v)

def clique_minor_free {V : Type*} (G : SimpleGraph V) (h : ℕ) : Prop :=
  ¬ has_clique_minor G h

def is_epsilon_ladder_at_width {V : Type*} [MetricSpace V] (ε r : ℝ)
    {ℓ : ℕ} (x p : Fin ℓ → V) : Prop :=
  0 < r ∧
    (∀ i, (1 + ε) * r < dist (p i) (x i)) ∧
    (∀ i j, i.val < j.val → dist (p i) (x j) ≤ r)

def is_epsilon_ladder {V : Type*} [MetricSpace V] (ε : ℝ) {ℓ : ℕ}
    (x p : Fin ℓ → V) : Prop :=
  ∃ r : ℝ, is_epsilon_ladder_at_width ε r x p

def epsilon_scatter_dimension_at_most (V : Type*) [MetricSpace V]
    (ε B : ℝ) : Prop :=
  ∀ (ℓ : ℕ) (x p : Fin ℓ → V),
    is_epsilon_ladder ε x p → (ℓ : ℝ) ≤ B

noncomputable def scatter_bound_constant (h : ℕ) (ε : ℝ) : ℝ :=
  (Nat.choose (h - 2 + 2 * ⌈36 * (h : ℝ) * ε⁻¹⌉₊) (h - 1) : ℝ) *
    (12 + 72 * ε⁻¹) * (h - 1)

noncomputable def scatter_bound (h : ℕ) (ε : ℝ) : ℝ :=
  let c := scatter_bound_constant h ε
  Real.rpow (6 * c * Real.rpow (9 * ε⁻¹ + 2) c) (c + 1)

theorem dim_bound :
    (∀ (h : ℕ) (ε : ℝ), 1 ≤ h → 0 < ε →
      ∀ (V : Type*) [MetricSpace V],
        ∀ (G : edge_weighted_graph V),
          clique_minor_free G.graph h →
          epsilon_scatter_dimension_at_most V ε (scatter_bound h ε)) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ (h : ℕ) (ε : ℝ), 1 ≤ h → 0 < ε →
        ∀ (V : Type*) [MetricSpace V],
          ∀ (G : edge_weighted_graph V),
            clique_minor_free G.graph h →
            epsilon_scatter_dimension_at_most V ε
              (Real.rpow 2
                (Real.rpow (max 2 ((h : ℝ) * ε⁻¹)) (C * (h : ℝ))))) := by sorry

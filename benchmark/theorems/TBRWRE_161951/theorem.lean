import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators

structure graph_edge_weights {V : Type*} (G : SimpleGraph V) where
  weight : V → V → ℝ
  symmetric : ∀ x y, weight x y = weight y x
  positive_of_adj : ∀ {x y}, G.Adj x y → 0 < weight x y
  zero_of_not_adj : ∀ {x y}, ¬ G.Adj x y → weight x y = 0

def weight_lipschitz {V : Type*} (G : SimpleGraph V) (β : ℝ)
    (w : graph_edge_weights G) : Prop :=
  ∀ ⦃x y z : V⦄, G.Adj x y → G.Adj x z →
    β⁻¹ ≤ w.weight x y / w.weight x z ∧ w.weight x y / w.weight x z ≤ β

noncomputable def weighted_degree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (w : graph_edge_weights G) (x : V) : ℝ := by
  classical
  exact ∑ y, w.weight x y

noncomputable def weighted_transition {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (w : graph_edge_weights G) : Matrix V V ℝ := by
  classical
  exact fun x y => if x = y then 0 else w.weight x y / weighted_degree G w x

noncomputable def stationary_distribution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (w : graph_edge_weights G) : V → ℝ := by
  classical
  exact fun x => weighted_degree G w x / ∑ z, weighted_degree G w z

noncomputable def external_vertex_boundary {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (S : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => v ∉ S ∧ ∃ u ∈ S, G.Adj u v

noncomputable def vertex_expansion {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℝ :=
  sInf {r : ℝ | ∃ S : Finset V, S.Nonempty ∧ 2 * S.card ≤ Fintype.card V ∧
    r = (external_vertex_boundary G S).card / (S.card : ℝ)}

noncomputable def robust_radius (ψ : ℝ) : ℕ :=
  ⌈2 / Real.log (1 + ψ)⌉₊

noncomputable def robust_lipschitz_bound (ψ : ℝ) : ℝ :=
  Real.exp (1 / (2 * (robust_radius ψ : ℝ)))

noncomputable def stationary_mass {V : Type*} (π : V → ℝ) (S : Finset V) : ℝ := by
  classical
  exact ∑ x ∈ S, π x

noncomputable def stationary_cut_flow {V : Type*} (π : V → ℝ) (P : Matrix V V ℝ)
    (S T : Finset V) : ℝ := by
  classical
  exact ∑ x ∈ S, ∑ y ∈ T, π x * P x y

noncomputable def markov_conductance {V : Type*} [Fintype V] [DecidableEq V] (π : V → ℝ)
    (P : Matrix V V ℝ) : ℝ :=
  sInf {r : ℝ | ∃ S : Finset V, S.Nonempty ∧ 0 < stationary_mass π S ∧
    stationary_mass π S ≤ 1 / 2 ∧
    r = stationary_cut_flow π P S (Finset.univ \ S) / stationary_mass π S}

noncomputable def weighted_mean {V : Type*} [Fintype V] [DecidableEq V]
    (π f : V → ℝ) : ℝ := by
  classical
  exact ∑ x, π x * f x

noncomputable def weighted_variance {V : Type*} [Fintype V] [DecidableEq V]
    (π f : V → ℝ) : ℝ := by
  classical
  exact ∑ x, π x * (f x - weighted_mean π f) ^ 2

noncomputable def dirichlet_form {V : Type*} [Fintype V] [DecidableEq V] (π : V → ℝ)
    (P : Matrix V V ℝ) (f : V → ℝ) : ℝ := by
  classical
  exact (1 / 2) * ∑ x, ∑ y, π x * P x y * (f x - f y) ^ 2

noncomputable def spectral_gap {V : Type*} [Fintype V] [DecidableEq V] (π : V → ℝ)
    (P : Matrix V V ℝ) : ℝ :=
  sInf {r : ℝ | ∃ f : V → ℝ, 0 < weighted_variance π f ∧
    r = dirichlet_form π P f / weighted_variance π f}

theorem robustness_of_expanders {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite]
    (d : ℕ) (ψ : ℝ) (w : graph_edge_weights G)
    (hConnected : G.Connected) (hRegular : G.IsRegularOfDegree d)
    (hExpansion : ψ ≤ vertex_expansion G) (hψ : 0 < ψ)
    (hTriangle : ∀ ⦃x y : V⦄, G.Adj x y →
      ∃ z : V, G.Adj x z ∧ G.Adj z y)
    (hLipschitz : weight_lipschitz G (robust_lipschitz_bound ψ) w) :
    ((1 / 4000) * (((d : ℝ) ^ (2 * robust_radius ψ))⁻¹) ≤
        markov_conductance (stationary_distribution G w)
          (weighted_transition G w ^ (2 * robust_radius ψ))) ∧
      ((1 / 100000000) * ((robust_radius ψ : ℝ)⁻¹) *
          (((d : ℝ) ^ (4 * robust_radius ψ))⁻¹) ≤
        spectral_gap (stationary_distribution G w) (weighted_transition G w)) := by sorry

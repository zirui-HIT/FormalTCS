import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Analysis.SpecialFunctions.Log.Base

open scoped Classical

noncomputable def directed_regular {V : Type*} [Fintype V]
    (G : Digraph V) (d : ℕ) : Prop :=
  (∀ v : V, (Finset.univ.filter fun w : V => G.Adj v w).card = d) ∧
    ∀ v : V, (Finset.univ.filter fun w : V => G.Adj w v).card = d

noncomputable def directed_cycle_factors {V : Type*} [Fintype V]
    (G : Digraph V) : Finset (Equiv.Perm V) :=
  Finset.univ.filter fun σ : Equiv.Perm V => ∀ v : V, G.Adj v (σ v)

noncomputable def permutation_cycle_count {V : Type*} [Fintype V]
    (σ : Equiv.Perm V) : ℕ :=
  Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid σ))

noncomputable def uniform_expected_cycle_count {V : Type*} [Fintype V]
    (G : Digraph V) : ℝ :=
  (∑ σ ∈ directed_cycle_factors G, (permutation_cycle_count σ : ℝ)) /
    ((directed_cycle_factors G).card : ℝ)

theorem small_cycle_factor_directed {n d : ℕ} (G : Digraph (Fin n))
    (hreg : directed_regular G d) (hd : 2 ≤ d) :
    uniform_expected_cycle_count G ≤
      4 * (n : ℝ) * Real.logb 2 (d : ℝ) / (d : ℝ) := by sorry

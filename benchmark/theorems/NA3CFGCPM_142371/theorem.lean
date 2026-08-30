import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Nat.Dist
import Mathlib.Logic.Equiv.Multiset

open scoped BigOperators

def valid_popular_sums_input (N : ℕ) (A : Multiset ℕ) : Prop :=
  A.card ≤ N ∧ ∀ a ∈ A, a < N

def multiset_convolution_coefficient (A B : Multiset ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (k + 1), A.count i * B.count (k - i)

def subpolynomial_overhead (g : ℕ → ℕ) : Prop :=
  ∀ d : ℕ, 0 < d → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (g N) ^ d ≤ N

structure deterministic_popular_sums_algorithm where
  output : ℕ → Multiset ℕ → Multiset ℕ → ℝ → (ℕ →₀ ℕ)
  runningTime : ℕ → Multiset ℕ → Multiset ℕ → ℝ → ℕ

def deterministic_popular_sums_specification
    (algorithm : deterministic_popular_sums_algorithm) : Prop :=
  ∃ g : ℕ → ℕ,
    subpolynomial_overhead g ∧
      ∃ Ctime Csparsity : ℝ,
        0 < Ctime ∧
          0 < Csparsity ∧
            ∀ (N : ℕ) (A B : Multiset ℕ) (ε : ℝ),
              0 < N →
                valid_popular_sums_input N A →
                    valid_popular_sums_input N B →
                    0 < ε →
                      (algorithm.runningTime N A B ε : ℝ) ≤
                          Ctime *
                            ((ε⁻¹ * (A.card : ℝ) + (B.card : ℝ)) *
                              (g N : ℝ)) ∧
                        ((algorithm.output N A B ε).support.card : ℝ) ≤
                            Csparsity * ε⁻¹ * (A.card : ℝ) *
                              (Real.log ((N : ℝ) + 2)) ^ 2 ∧
                          ∀ k : ℕ,
                            (Nat.dist (algorithm.output N A B ε k)
                                (multiset_convolution_coefficient A B k) : ℝ) ≤
                              ε * (B.card : ℝ)

theorem deterministic_popular_sums_approximation :
    ∃ algorithm : deterministic_popular_sums_algorithm,
      deterministic_popular_sums_specification algorithm := by sorry

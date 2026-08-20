import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Nat.Dist
import Mathlib.Logic.Equiv.Multiset

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators

def valid_popular_sums_input (N : ℕ) (A : Multiset ℕ) : Prop :=
  A.card ≤ N ∧ ∀ a ∈ A, a < N

def multiset_convolution_coefficient (A B : Multiset ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (k + 1), A.count i * B.count (k - i)

def subpolynomial_overhead (g : ℕ → ℕ) : Prop :=
  ∀ d : ℕ, 0 < d → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (g N) ^ d ≤ N

structure deterministic_popular_sums_algorithm where
  stateCount : ℕ
  machine : Turing.TM0.Machine Bool (Fin (stateCount + 1))

noncomputable def popular_sums_machine_input
    (N : ℕ) (A B : Multiset ℕ) (ε : ℝ) : List Bool :=
  Nat.bits (Encodable.encode (N, A, B, max 1 ⌈ε⁻¹⌉₊))

def binary_natural_code (n : ℕ) : List Bool :=
  List.replicate (Nat.bits n).length true ++ [false] ++ Nat.bits n

def sparse_vector_binary_encoding (f : ℕ →₀ ℕ) : List Bool :=
  binary_natural_code f.support.card ++
    f.support.sort.foldr
      (fun k code => binary_natural_code k ++ binary_natural_code (f k) ++ code) []

def popular_sums_machine_output
    (algorithm : deterministic_popular_sums_algorithm)
    (configuration : Turing.TM0.Cfg Bool (Fin (algorithm.stateCount + 1)))
    (f : ℕ →₀ ℕ) : Prop :=
  ∀ i : ℕ,
    configuration.Tape.right₀.nth i =
      (sparse_vector_binary_encoding f).getI i

def popular_sums_machine_execution
    (algorithm : deterministic_popular_sums_algorithm)
    (N : ℕ) (A B : Multiset ℕ) (ε : ℝ)
    (configuration : Turing.TM0.Cfg Bool (Fin (algorithm.stateCount + 1)))
    (time : ℕ) : Prop :=
  Nonempty (StateTransition.EvalsToInTime
      (Turing.TM0.step algorithm.machine)
      (Turing.TM0.init (popular_sums_machine_input N A B ε))
      (some configuration) time) ∧
    Turing.TM0.step algorithm.machine configuration = none

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
                      ∃ (f : ℕ →₀ ℕ)
                          (configuration :
                            Turing.TM0.Cfg Bool (Fin (algorithm.stateCount + 1)))
                          (time : ℕ),
                        popular_sums_machine_execution
                            algorithm N A B ε configuration time ∧
                          popular_sums_machine_output algorithm configuration f ∧
                            (time : ℝ) ≤
                                Ctime *
                                  (ε⁻¹ * (A.card : ℝ) + (B.card : ℝ)) *
                                  (g N : ℝ) ∧
                              (f.support.card : ℝ) ≤
                                  Csparsity * ε⁻¹ * (A.card : ℝ) *
                                    (Real.log ((N : ℝ) + 2)) ^ 2 ∧
                                ∀ k : ℕ,
                                  (Nat.dist (f k)
                                      (multiset_convolution_coefficient A B k) : ℝ) ≤
                                    ε * (B.card : ℝ)

theorem deterministic_popular_sums_approximation :
    ∃ algorithm : deterministic_popular_sums_algorithm,
      deterministic_popular_sums_specification algorithm := by sorry

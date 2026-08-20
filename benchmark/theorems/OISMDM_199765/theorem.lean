import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators

def node_seq (s : ℕ → ℕ) (a : ℕ) : ℕ :=
  1 + ∑ t ∈ Finset.Ico 1 a, s t

def step_approx (Z : ℕ → ℝ) (s : ℕ → ℕ) (k : ℕ) (j : ℕ) : ℝ :=
  Z (node_seq s (((Finset.Icc 1 k).filter (fun a => node_seq s a ≤ j)).card))

def l1_error (Z Z' : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, |Z j - Z' j|

def valid_schedule (s : ℕ → ℕ) (k n : ℕ) : Prop :=
  (∀ t ∈ Finset.Icc 1 k, 1 ≤ s t) ∧ ∑ t ∈ Finset.Icc 1 k, s t = n

structure mdm_problem where
  alphabet : Type
  alphabet_fintype : Fintype alphabet
  n : ℕ
  μ : PMF (Fin n → alphabet)
  Z : ℕ → ℝ
  expectedKL : (ℕ → ℕ) → ℝ
  Z_base : Z 1 = 0
  Z_mono : ∀ i ∈ Finset.Icc 1 n, ∀ j ∈ Finset.Icc 1 n, i ≤ j → Z i ≤ Z j
  expectedKL_eq : ∀ (k : ℕ), 1 ≤ k → k ≤ n → ∀ s, valid_schedule s k n →
    expectedKL s = l1_error Z (step_approx Z s k) n

theorem optimal_schedule (P : mdm_problem) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ P.n)
    (sStar : ℕ → ℕ) (hsStar : valid_schedule sStar k P.n)
    (hmin : ∀ s, valid_schedule s k P.n →
      l1_error P.Z (step_approx P.Z sStar k) P.n ≤ l1_error P.Z (step_approx P.Z s k) P.n) :
    ∀ s, valid_schedule s k P.n → P.expectedKL sStar ≤ P.expectedKL s := by sorry

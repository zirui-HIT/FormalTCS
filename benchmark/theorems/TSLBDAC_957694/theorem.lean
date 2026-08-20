import Mathlib.RingTheory.Binomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

structure ROBP (k n w : ℕ) where
  start : Fin w
  step : Fin n → Fin w → Fin k → Fin w
  out : Fin w → Fin k → ℝ

def ROBP_run {k n w : ℕ} (P : ROBP k n w) (x : Fin n → Fin k) : Fin w :=
  Fin.foldl n (fun v t => P.step t v (x t)) P.start

def symbol_count {k n : ℕ} (x : Fin n → Fin k) (j : Fin k) : ℕ :=
  (Finset.univ.filter fun i : Fin n => x i = j).card

def computes_approx_count {k n w : ℕ} (P : ROBP k n w) (Δ : ℝ) : Prop :=
  ∀ x : Fin n → Fin k, ∀ j : Fin k,
    |P.out (ROBP_run P x) j - (symbol_count x j : ℝ)| ≤ Δ

theorem k_counter_lb (k n w m : ℕ) (Δ : ℝ) (hk : 2 ≤ k) (hn : 1 ≤ n) (hw : 1 ≤ w)
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ (n : ℝ) / (2 * ((k : ℝ) - 1)))
    (hP : ∃ P : ROBP k n w, computes_approx_count P Δ)
    (hmn : m ≤ n - 1) (hmw : Nat.choose (m + k - 1) (k - 1) ≤ w)
    (hmax : ∀ m' : ℕ, m' ≤ n - 1 → Nat.choose (m' + k - 1) (k - 1) ≤ w → m' ≤ m) :
    (Nat.choose (m + k) k : ℝ) + ((n : ℝ) - m - 1) * w
      ≥ Ring.choose ((n : ℝ) - 2 * ((k : ℝ) - 1) * Δ + (k : ℝ) - 1) k := by sorry

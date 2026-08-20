import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Matrix.Basic
import Mathlib.Logic.Equiv.Fin.Basic

abbrev binary_matrix (r c : ℕ) := Matrix (Fin r) (Fin c) Bool

def matrix_weight {r c : ℕ} (A : binary_matrix r c) : ℕ :=
  (Finset.univ.filter (fun p : Fin r × Fin c => A p.1 p.2 = true)).card

def contains_pattern {r c n m : ℕ} (P : binary_matrix r c) (A : binary_matrix n m) : Prop :=
  ∃ ρ : Fin r → Fin n, StrictMono ρ ∧
    ∃ κ : Fin c → Fin m, StrictMono κ ∧
      ∀ i j, P i j = true → A (ρ i) (κ j) = true

def pattern_free {r c n m : ℕ} (P : binary_matrix r c) (A : binary_matrix n m) : Prop :=
  ¬contains_pattern P A

noncomputable def extremal_function {r c : ℕ} (P : binary_matrix r c) (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun A : binary_matrix n n => pattern_free P A)).sup matrix_weight

def pattern_s_zero : binary_matrix 3 4 := fun i j =>
  decide ((i.1 = 0 ∧ (j.1 = 0 ∨ j.1 = 2)) ∨
    (i.1 = 1 ∧ (j.1 = 0 ∨ j.1 = 3)) ∨
    (i.1 = 2 ∧ (j.1 = 1 ∨ j.1 = 3)))

def pattern_s_one : binary_matrix 3 4 := fun i j =>
  decide ((i.1 = 0 ∧ (j.1 = 0 ∨ j.1 = 3)) ∨
    (i.1 = 1 ∧ (j.1 = 0 ∨ j.1 = 2)) ∨
    (i.1 = 2 ∧ (j.1 = 1 ∨ j.1 = 3)))

def pach_tardos_lower_bound {r c : ℕ} (P : binary_matrix r c) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    (n : ℝ) * Real.rpow 2
        (Real.sqrt (Real.logb 2 (n : ℝ)) -
          C * Real.logb 2 (Real.logb 2 (n : ℝ))) ≤
      (extremal_function P n : ℝ)

theorem PT_refutation :
    pach_tardos_lower_bound pattern_s_zero ∧ pach_tardos_lower_bound pattern_s_one := by sorry

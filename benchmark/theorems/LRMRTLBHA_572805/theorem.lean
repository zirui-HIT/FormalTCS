import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Order.Lattice.Nat

open scoped BigOperators

def booleanize {p : ℕ} (x : ZMod p) : Bool :=
  decide (x = 1)

def boolean_disagreement_count {p : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M L : Matrix ι κ (ZMod p)) : ℕ :=
  ((Finset.univ : Finset (ι × κ)).filter fun ij ↦
    booleanize (M ij.1 ij.2) ≠ booleanize (L ij.1 ij.2)).card

noncomputable def boolean_rigidity {p : ℕ} [Fact p.Prime]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ (ZMod p)) (r : ℕ) : ℕ :=
  sInf {s : ℕ | ∃ L : Matrix ι κ (ZMod p),
    Matrix.rank L ≤ r ∧ boolean_disagreement_count M L = s}

def is_sign_matrix {p : ℕ} {ι κ : Type*} (A : Matrix ι κ (ZMod p)) : Prop :=
  ∀ i j, A i j = 1 ∨ A i j = -1

def kronecker_power {p q : ℕ} (A : Matrix (Fin q) (Fin q) (ZMod p)) (n : ℕ) :
    Matrix (Fin n → Fin q) (Fin n → Fin q) (ZMod p) :=
  Matrix.of fun x y ↦ ∏ t : Fin n, A (x t) (y t)

theorem kronecker_power_boolean_rigidity_lower_bound
    (p q : ℕ) [Fact p.Prime]
    (A : Matrix (Fin q) (Fin q) (ZMod p))
    (hA : is_sign_matrix A) (hrank : 1 < Matrix.rank A) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ c₂ < 1 ∧
      ∀ n : ℕ, 0 < n →
        (q : ℝ) ^ (2 * n) * ((1 / 2 : ℝ) - c₂ ^ n) ≤
          (boolean_rigidity (kronecker_power A n) ⌊c₁ * (n : ℝ)⌋₊ : ℝ) := by
  sorry

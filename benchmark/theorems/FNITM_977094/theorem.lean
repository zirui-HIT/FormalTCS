import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.NNReal.Defs

set_option linter.all false
set_option maxHeartbeats 500000

def boolean_matrix {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ i j, M i j = 0 ∨ M i j = 1

noncomputable def matrix_row_l2_max {m k : ℕ}
    (U : Matrix (Fin m) (Fin k) ℝ) : NNReal :=
  Finset.univ.sup fun i =>
    Real.toNNReal (Real.sqrt (∑ j, (U i j) ^ 2))

noncomputable def matrix_column_l2_max {k n : ℕ}
    (V : Matrix (Fin k) (Fin n) ℝ) : NNReal :=
  Finset.univ.sup fun j =>
    Real.toNNReal (Real.sqrt (∑ i, (V i j) ^ 2))

noncomputable def factorization_cost {m k n : ℕ}
    (U : Matrix (Fin m) (Fin k) ℝ) (V : Matrix (Fin k) (Fin n) ℝ) : ℝ :=
  (matrix_row_l2_max U : ℝ) * (matrix_column_l2_max V : ℝ)

noncomputable def gamma_two {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sInf {x : ℝ | ∃ (k : ℕ) (U : Matrix (Fin m) (Fin k) ℝ)
    (V : Matrix (Fin k) (Fin n) ℝ), M = U * V ∧ x = factorization_cost U V}

def is_monochromatic_rectangle {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (I : Finset (Fin m)) (J : Finset (Fin n)) : Prop :=
  (∀ i ∈ I, ∀ j ∈ J, M i j = 0) ∨
    (∀ i ∈ I, ∀ j ∈ J, M i j = 1)

def has_density_monochromatic_rectangle {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℝ) (δ₁ δ₂ : ℝ) : Prop :=
  ∃ (I : Finset (Fin m)) (J : Finset (Fin n)),
    is_monochromatic_rectangle M I J ∧
      δ₁ * (m : ℝ) ≤ (I.card : ℝ) ∧ δ₂ * (n : ℝ) ≤ (J.card : ℝ)

theorem mono_rectangle :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m n : ℕ) (γ : ℝ) (M : Matrix (Fin m) (Fin n) ℝ),
        boolean_matrix M → gamma_two M ≤ γ →
          has_density_monochromatic_rectangle M
            (Real.rpow 2 (-(C * γ ^ 3))) (Real.rpow 2 (-(C * γ ^ 3))) := by sorry

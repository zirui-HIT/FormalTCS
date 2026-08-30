import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Block

set_option linter.all false

open scoped BigOperators

def decaying_matrix (f : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if j.1 ≤ i.1 then f (i.1 - j.1) else 0

def decay_polynomial (f : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k : Fin n, (f k.1 : ℂ) * z ^ k.1

noncomputable def distinguished_root (n : ℕ) : ℂ :=
  Complex.exp (((Real.pi : ℂ) / (n : ℂ)) * Complex.I)

noncomputable def real_row_p_trace {m d : ℕ} (p : ℕ)
    (A : Matrix (Fin m) (Fin d) ℝ) : ℝ :=
  Real.rpow (∑ i : Fin m,
    Real.rpow (∑ j : Fin d, (A i j) ^ 2) ((p : ℝ) / 2)) (1 / (p : ℝ))

noncomputable def real_column_norm {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ) : ℝ :=
  sSup (Set.range fun j : Fin d => Real.sqrt (∑ i : Fin m, (A i j) ^ 2))

noncomputable def real_maximum_row_norm {m d : ℕ}
    (A : Matrix (Fin m) (Fin d) ℝ) : ℝ :=
  sSup (Set.range fun i : Fin m => Real.sqrt (∑ j : Fin d, (A i j) ^ 2))

noncomputable def finite_p_factorization_norm {n : ℕ} (p : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sInf {c : ℝ | ∃ (d : ℕ) (B : Matrix (Fin n) (Fin d) ℝ)
    (C : Matrix (Fin d) (Fin n) ℝ),
    M = B * C ∧ c = real_row_p_trace p B * real_column_norm C}

noncomputable def infinite_factorization_norm {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sInf {c : ℝ | ∃ (d : ℕ) (B : Matrix (Fin n) (Fin d) ℝ)
    (C : Matrix (Fin d) (Fin n) ℝ),
    M = B * C ∧ c = real_maximum_row_norm B * real_column_norm C}

noncomputable def operator_two_factorization_norm {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  infinite_factorization_norm M

noncomputable def frobenius_factorization_norm {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  finite_p_factorization_norm 2 M

def lower_triangular {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  L.BlockTriangular OrderDual.toDual

noncomputable def fourier_bound (f : ℕ → ℝ) (n p : ℕ) : ℝ :=
  (∑ k : Fin (2 * n), ‖decay_polynomial f n (distinguished_root n ^ k.1)‖) /
    (2 * Real.rpow (n : ℝ) (1 - 1 / (p : ℝ)))

noncomputable def operator_fourier_bound (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ k : Fin (2 * n), ‖decay_polynomial f n (distinguished_root n ^ k.1)‖) /
    (2 * (n : ℝ))

noncomputable def frobenius_fourier_bound (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ k : Fin (2 * n), ‖decay_polynomial f n (distinguished_root n ^ k.1)‖) /
    (2 * Real.sqrt (n : ℝ))

structure toeplitz_factorization_output (n : ℕ) where
  left : Matrix (Fin n) (Fin n) ℝ
  right : Matrix (Fin n) (Fin n) ℝ

inductive real_arithmetic_expression where
  | register : ℕ → real_arithmetic_expression
  | weight : ℕ → real_arithmetic_expression
  | integer : ℤ → real_arithmetic_expression
  | pi : real_arithmetic_expression
  | neg : real_arithmetic_expression → real_arithmetic_expression
  | add : real_arithmetic_expression → real_arithmetic_expression → real_arithmetic_expression
  | mul : real_arithmetic_expression → real_arithmetic_expression → real_arithmetic_expression
  | div : real_arithmetic_expression → real_arithmetic_expression → real_arithmetic_expression
  | sqrt : real_arithmetic_expression → real_arithmetic_expression
  | sin : real_arithmetic_expression → real_arithmetic_expression
  | cos : real_arithmetic_expression → real_arithmetic_expression
  | branchNonnegative : real_arithmetic_expression → real_arithmetic_expression →
      real_arithmetic_expression → real_arithmetic_expression

noncomputable def real_arithmetic_expression_evaluate (f : ℕ → ℝ) (registers : List ℝ) :
    real_arithmetic_expression → ℝ
  | .register k => registers.getD k 0
  | .weight k => f k
  | .integer z => (z : ℝ)
  | .pi => Real.pi
  | .neg x => -real_arithmetic_expression_evaluate f registers x
  | .add x y =>
      real_arithmetic_expression_evaluate f registers x +
        real_arithmetic_expression_evaluate f registers y
  | .mul x y =>
      real_arithmetic_expression_evaluate f registers x *
        real_arithmetic_expression_evaluate f registers y
  | .div x y =>
      real_arithmetic_expression_evaluate f registers x /
        real_arithmetic_expression_evaluate f registers y
  | .sqrt x => Real.sqrt (real_arithmetic_expression_evaluate f registers x)
  | .sin x => Real.sin (real_arithmetic_expression_evaluate f registers x)
  | .cos x => Real.cos (real_arithmetic_expression_evaluate f registers x)
  | .branchNonnegative c x y =>
      if 0 ≤ real_arithmetic_expression_evaluate f registers c then
        real_arithmetic_expression_evaluate f registers x
      else
        real_arithmetic_expression_evaluate f registers y

def real_arithmetic_expression_operation_count : real_arithmetic_expression → ℕ
  | .register _ => 0
  | .weight _ => 1
  | .integer _ => 0
  | .pi => 0
  | .neg x => 1 + real_arithmetic_expression_operation_count x
  | .add x y => 1 + real_arithmetic_expression_operation_count x +
      real_arithmetic_expression_operation_count y
  | .mul x y => 1 + real_arithmetic_expression_operation_count x +
      real_arithmetic_expression_operation_count y
  | .div x y => 1 + real_arithmetic_expression_operation_count x +
      real_arithmetic_expression_operation_count y
  | .sqrt x => 1 + real_arithmetic_expression_operation_count x
  | .sin x => 1 + real_arithmetic_expression_operation_count x
  | .cos x => 1 + real_arithmetic_expression_operation_count x
  | .branchNonnegative c x y => 1 + real_arithmetic_expression_operation_count c +
      max (real_arithmetic_expression_operation_count x)
        (real_arithmetic_expression_operation_count y)

structure factorization_arithmetic_program (n : ℕ) where
  instructions : List real_arithmetic_expression
  left : Matrix (Fin n) (Fin n) ℕ
  right : Matrix (Fin n) (Fin n) ℕ

noncomputable def factorization_arithmetic_program_evaluate {n : ℕ}
    (P : factorization_arithmetic_program n) (f : ℕ → ℝ) :
    toeplitz_factorization_output n :=
  let registers := P.instructions.foldl
    (fun values instruction =>
      values ++ [real_arithmetic_expression_evaluate f values instruction]) []
  { left := fun i j => registers.getD (P.left i j) 0
    right := fun i j => registers.getD (P.right i j) 0 }

def factorization_arithmetic_program_operation_count {n : ℕ}
    (P : factorization_arithmetic_program n) : ℕ :=
  (P.instructions.map real_arithmetic_expression_operation_count).sum

structure toeplitz_factorization_algorithm where
  program : (n : ℕ) → factorization_arithmetic_program n

noncomputable def toeplitz_factorization_algorithm_run
    (A : toeplitz_factorization_algorithm) (f : ℕ → ℝ) (n : ℕ) :
    toeplitz_factorization_output n :=
  factorization_arithmetic_program_evaluate (A.program n) f

def toeplitz_factorization_algorithm_operation_count
    (A : toeplitz_factorization_algorithm) (n : ℕ) : ℕ :=
  factorization_arithmetic_program_operation_count (A.program n)

def factorization_algorithm_efficient (A : toeplitz_factorization_algorithm) : Prop :=
  ∃ C q : ℕ, 0 < C ∧ ∀ n : ℕ,
    toeplitz_factorization_algorithm_operation_count A n ≤ C * (n + 1) ^ q

def factorization_output_valid (f : ℕ → ℝ) (n : ℕ)
    (out : toeplitz_factorization_output n) : Prop :=
  decaying_matrix f n = out.left * out.right ∧ lower_triangular out.left

theorem main_upper_bound_gamma (f : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    ∃ A : toeplitz_factorization_algorithm,
      factorization_algorithm_efficient A ∧
      factorization_output_valid f n (toeplitz_factorization_algorithm_run A f n) ∧
      (∀ p : ℕ, 2 ≤ p →
        finite_p_factorization_norm p (decaying_matrix f n) ≤
            real_row_p_trace p (toeplitz_factorization_algorithm_run A f n).left *
              real_column_norm (toeplitz_factorization_algorithm_run A f n).right ∧
          real_row_p_trace p (toeplitz_factorization_algorithm_run A f n).left *
              real_column_norm (toeplitz_factorization_algorithm_run A f n).right ≤
            fourier_bound f n p) ∧
      operator_two_factorization_norm (decaying_matrix f n) =
          infinite_factorization_norm (decaying_matrix f n) ∧
      operator_two_factorization_norm (decaying_matrix f n) ≤ operator_fourier_bound f n ∧
      frobenius_factorization_norm (decaying_matrix f n) ≤ frobenius_fourier_bound f n := by sorry

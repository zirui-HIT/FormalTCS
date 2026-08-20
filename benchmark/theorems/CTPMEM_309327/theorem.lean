import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Relation

universe u

def principal_minor_equivalent {𝔽 : Type u} [Field 𝔽] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) 𝔽) : Prop :=
  ∀ S : Finset (Fin n),
    Matrix.det
        (A.submatrix (fun i : S ↦ (i : Fin n)) (fun i : S ↦ (i : Fin n))) =
      Matrix.det
        (B.submatrix (fun i : S ↦ (i : Fin n)) (fun i : S ↦ (i : Fin n)))

def matrix_irreducible {𝔽 : Type u} [Field 𝔽] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝔽) : Prop :=
  Nonempty (Fin n) ∧
    ∀ i j : Fin n,
      Relation.ReflTransGen (fun x y : Fin n ↦ x ≠ y ∧ A x y ≠ 0) i j

noncomputable def matrix_cut {𝔽 : Type u} [Field 𝔽] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝔽) (X : Finset (Fin n)) : Prop :=
  2 ≤ X.card ∧ X.card ≤ n - 2 ∧
    Matrix.rank
        (A.submatrix
          (fun i : {i : Fin n // i ∈ X} ↦ (i : Fin n))
          (fun j : {j : Fin n // j ∉ X} ↦ (j : Fin n))) ≤ 1 ∧
      Matrix.rank
        (A.submatrix
          (fun i : {i : Fin n // i ∉ X} ↦ (i : Fin n))
          (fun j : {j : Fin n // j ∈ X} ↦ (j : Fin n))) ≤ 1

def first_nonzero_cut_row {𝔽 : Type u} [Field 𝔽] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝔽) (X : Finset (Fin n))
    (r : Fin n) (q : Fin n → 𝔽) : Prop :=
  r ∈ X ∧
    (∀ j : Fin n, j ∉ X → q j = A r j) ∧
      (∃ j : Fin n, j ∉ X ∧ A r j ≠ 0) ∧
        ∀ r' : Fin n, r' ∈ X → r' < r →
          ∀ j : Fin n, j ∉ X → A r' j = 0

def first_nonzero_cut_column {𝔽 : Type u} [Field 𝔽] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝔽) (X : Finset (Fin n))
    (c : Fin n) (u : Fin n → 𝔽) : Prop :=
  c ∈ X ∧
    (∀ i : Fin n, i ∉ X → u i = A i c) ∧
      (∃ i : Fin n, i ∉ X ∧ A i c ≠ 0) ∧
        ∀ c' : Fin n, c' ∈ X → c' < c →
          ∀ i : Fin n, i ∉ X → A i c' = 0

def cut_transpose_at {𝔽 : Type u} [Field 𝔽] {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) 𝔽) (X : Finset (Fin n)) : Prop :=
  matrix_irreducible A ∧ matrix_cut A X ∧
    ∃ r c : Fin n, ∃ p q u v : Fin n → 𝔽,
      first_nonzero_cut_row A X r q ∧
        first_nonzero_cut_column A X c u ∧
          (∀ i : Fin n, i ∈ X →
            ∀ j : Fin n, j ∉ X → A i j = p i * q j) ∧
            (∀ i : Fin n, i ∉ X →
              ∀ j : Fin n, j ∈ X → A i j = u i * v j) ∧
              ∀ i j : Fin n,
                C i j =
                  if i ∈ X then
                    if j ∈ X then A i j else p i * u j
                  else
                    if j ∈ X then q i * v j else A j i

def diagonally_similar {𝔽 : Type u} [Field 𝔽] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) 𝔽) : Prop :=
  ∃ d : Fin n → 𝔽,
    (∀ i : Fin n, d i ≠ 0) ∧
      ∀ i j : Fin n, B i j = d i * A i j * (d j)⁻¹

def diagonally_equivalent {𝔽 : Type u} [Field 𝔽] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) 𝔽) : Prop :=
  diagonally_similar A B ∨ diagonally_similar A B.transpose

def cut_transpose_step {𝔽 : Type u} [Field 𝔽] {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) 𝔽) : Prop :=
  ∃ X : Finset (Fin n), cut_transpose_at A C X

def short_cut_transpose_chain {𝔽 : Type u} [Field 𝔽] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) 𝔽) : Prop :=
  ∃ k : ℕ, k < 2 * n ∧
    ∃ Aseq : ℕ → Matrix (Fin n) (Fin n) 𝔽,
      Aseq 0 = A ∧
        (∀ i : ℕ, i < k → cut_transpose_step (Aseq i) (Aseq (i + 1))) ∧
          diagonally_equivalent (Aseq k) B

theorem main_one {𝔽 : Type u} [Field 𝔽] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) 𝔽)
    (hA : matrix_irreducible A) (hB : matrix_irreducible B) :
    principal_minor_equivalent A B ↔ short_cut_transpose_chain A B := by sorry

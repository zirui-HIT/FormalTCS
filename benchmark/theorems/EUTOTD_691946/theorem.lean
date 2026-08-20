import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Span.Defs

open scoped BigOperators

abbrev order_three_tensor (K : Type) (n p : ℕ) := Fin n → Fin n → Fin p → K

def rank_one_tensor {K : Type} [Mul K] {n p : ℕ}
    (u v : Fin n → K) (w : Fin p → K) : order_three_tensor K n p :=
  fun i j k => u i * v j * w k

def tensor_decomposition {K : Type} [Semiring K] {n p r : ℕ}
    (T : order_three_tensor K n p)
    (u v : Fin r → Fin n → K) (w : Fin r → Fin p → K) : Prop :=
  T = ∑ a, rank_one_tensor (u a) (v a) (w a)

def has_tensor_rank {K : Type} [Semiring K] {n p : ℕ}
    (T : order_three_tensor K n p) (r : ℕ) : Prop :=
  (∃ (u v : Fin r → Fin n → K) (w : Fin r → Fin p → K),
      tensor_decomposition T u v w) ∧
    ∀ (q : ℕ) (u v : Fin q → Fin n → K) (w : Fin q → Fin p → K),
      tensor_decomposition T u v w → r ≤ q

def essentially_unique_decomposition {K : Type} [Semiring K] {n p r : ℕ}
    (T : order_three_tensor K n p)
    (u v : Fin r → Fin n → K) (w : Fin r → Fin p → K) : Prop :=
  ∀ (u' v' : Fin r → Fin n → K) (w' : Fin r → Fin p → K),
    tensor_decomposition T u' v' w' →
      ∃ σ : Equiv.Perm (Fin r), ∀ a,
        rank_one_tensor (u' a) (v' a) (w' a) =
          rank_one_tensor (u (σ a)) (v (σ a)) (w (σ a))

def pairwise_linearly_independent {K : Type} [Field K] {r p : ℕ}
    (w : Fin r → Fin p → K) : Prop :=
  ∀ ⦃a b : Fin r⦄, a ≠ b →
    LinearIndependent K (fun t : Fin 2 => if t = 0 then w a else w b)

def tensor_slice {K : Type} {n p : ℕ} (T : order_three_tensor K n p) (k : Fin p) :
    Matrix (Fin n) (Fin n) K :=
  fun i j => T i j k

def tensor_slice_span {K : Type} [Field K] {n p : ℕ} (T : order_three_tensor K n p) :
    Submodule K (Matrix (Fin n) (Fin n) K) :=
  Submodule.span K (Set.range (tensor_slice T))

def slice_span_contains_invertible {K : Type} [Field K] {n p : ℕ}
    (T : order_three_tensor K n p) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) K, A ∈ tensor_slice_span T ∧ IsUnit A

noncomputable def normalized_nonfirst_slices {K : Type} [Field K] {n q : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (T : order_three_tensor K n (q + 2)) :
    Fin (q + 1) → Matrix (Fin n) (Fin n) K :=
  fun k => A⁻¹ * tensor_slice T k.succ

def matrix_commutator {K : Type} [Ring K] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  A * B - B * A

def matrix_column_span {K : Type} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) : Submodule K (Fin n → K) :=
  Submodule.span K (Set.range (fun j => fun i => A i j))

noncomputable def commuting_extension_dimension_hypothesis {K : Type} [Field K]
    {n s : ℕ} (r : ℕ) (B : Fin s → Matrix (Fin n) (Fin n) K) (k l m : Fin s) : Prop :=
  k ≠ l ∧ k ≠ m ∧ l ≠ m ∧
  Module.finrank K (matrix_column_span (matrix_commutator (B k) (B l))) = 2 * (r - n) ∧
  Module.finrank K (matrix_column_span (matrix_commutator (B k) (B m))) = 2 * (r - n) ∧
  Module.finrank K (matrix_column_span (matrix_commutator (B l) (B m))) = 2 * (r - n) ∧
  Module.finrank K
      ↥(matrix_column_span (matrix_commutator (B k) (B l)) ⊔
        matrix_column_span (matrix_commutator (B k) (B m))) = 3 * (r - n) ∧
  Module.finrank K
      ↥(matrix_column_span (matrix_commutator (B l) (B k)) ⊔
        matrix_column_span (matrix_commutator (B l) (B m))) = 3 * (r - n) ∧
  Module.finrank K
      ↥(matrix_column_span (matrix_commutator (B m) (B k)) ⊔
        matrix_column_span (matrix_commutator (B m) (B l))) = 3 * (r - n)

noncomputable def commuting_extension_uniqueness_hypothesis {K : Type} [Field K]
    {n q : ℕ} (r : ℕ) (B : Fin (q + 1) → Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ l : Fin (q + 1), l ≠ 0 → ∃ m : Fin (q + 1),
    m ≠ 0 ∧ m ≠ l ∧ commuting_extension_dimension_hypothesis r B 0 l m

noncomputable def tensor_uniqueness_hypotheses {K : Type} [Field K] {n q r : ℕ}
    (T : order_three_tensor K n (q + 2))
    (u v : Fin r → Fin n → K) (w : Fin r → Fin (q + 2) → K) : Prop :=
  4 ≤ q + 2 ∧
  tensor_decomposition T u v w ∧
  pairwise_linearly_independent w ∧
  slice_span_contains_invertible T ∧
  ∃ A : Matrix (Fin n) (Fin n) K,
    A ∈ tensor_slice_span T ∧ IsUnit A ∧
      commuting_extension_uniqueness_hypothesis r (normalized_nonfirst_slices A T)

def tensor_uniqueness_conclusion {K : Type} [Semiring K] {n p r : ℕ}
    (T : order_three_tensor K n p)
    (u v : Fin r → Fin n → K) (w : Fin r → Fin p → K) : Prop :=
  has_tensor_rank T r ∧ essentially_unique_decomposition T u v w

theorem efficient_overcomplete_tensor_uniqueness {K : Type} [Field K] [Infinite K]
    {n q r : ℕ}
    (T : order_three_tensor K n (q + 2))
    (u v : Fin r → Fin n → K) (w : Fin r → Fin (q + 2) → K)
    (hq : 2 ≤ q)
    (h : tensor_uniqueness_hypotheses T u v w) :
    tensor_uniqueness_conclusion T u v w := by sorry

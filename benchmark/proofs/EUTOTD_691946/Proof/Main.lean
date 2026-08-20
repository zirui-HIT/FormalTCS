import Architect
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Span.Defs

open scoped BigOperators

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:order-three-tensor"
  (statement := /-- For a field $K$ and natural numbers $n,p$, an order-three tensor of format
  $n\times n\times p$ is represented by its coordinate function
  $\operatorname{Fin}(n)\to\operatorname{Fin}(n)\to\operatorname{Fin}(p)\to K$. -/)
  (title := /-- Order-three tensors -/)
  (latexEnv := "definition")]
abbrev order_three_tensor (K : Type) (n p : ℕ) := Fin n → Fin n → Fin p → K

@[blueprint "def:rank-one-tensor"
  (statement := /-- Given $u,v\in K^n$ and $w\in K^p$, the rank-one tensor
  $u\otimes v\otimes w$ has coordinates $(u\otimes v\otimes w)_{ijk}=u_i v_j w_k$. -/)
  (title := /-- Rank-one tensors -/)
  (latexEnv := "definition")]
def rank_one_tensor {K : Type} [Mul K] {n p : ℕ}
    (u v : Fin n → K) (w : Fin p → K) : order_three_tensor K n p :=
  fun i j k => u i * v j * w k

@[blueprint "def:tensor-decomposition"
  (statement := /-- Let $T$ be a tensor of format $n\times n\times p$. Families
  $(u_a)_{a\in\operatorname{Fin}(r)}$, $(v_a)_{a\in\operatorname{Fin}(r)}$, and
  $(w_a)_{a\in\operatorname{Fin}(r)}$ form a decomposition of length $r$ if
  $T=\sum_a u_a\otimes v_a\otimes w_a$. -/)
  (title := /-- Finite tensor decompositions -/)
  (latexEnv := "definition")]
def tensor_decomposition {K : Type} [Semiring K] {n p r : ℕ}
    (T : order_three_tensor K n p)
    (u v : Fin r → Fin n → K) (w : Fin r → Fin p → K) : Prop :=
  T = ∑ a, rank_one_tensor (u a) (v a) (w a)

@[blueprint "def:has-tensor-rank"
  (statement := /-- A tensor $T$ has tensor rank $r$ if it admits a decomposition of length $r$
  and every finite rank-one decomposition of $T$ has length at least $r$. -/)
  (title := /-- Exact tensor rank -/)
  (latexEnv := "definition")]
def has_tensor_rank {K : Type} [Semiring K] {n p : ℕ}
    (T : order_three_tensor K n p) (r : ℕ) : Prop :=
  (∃ (u v : Fin r → Fin n → K) (w : Fin r → Fin p → K),
      tensor_decomposition T u v w) ∧
    ∀ (q : ℕ) (u v : Fin q → Fin n → K) (w : Fin q → Fin p → K),
      tensor_decomposition T u v w → r ≤ q

@[blueprint "def:essentially-unique-decomposition"
  (statement := /-- A fixed decomposition
  $T=\sum_{a=1}^r u_a\otimes v_a\otimes w_a$ is essentially unique if every other
  decomposition of $T$ into $r$ rank-one tensors has, after a permutation, exactly the same
  rank-one tensor terms. -/)
  (title := /-- Essential uniqueness -/)
  (latexEnv := "definition")]
def essentially_unique_decomposition {K : Type} [Semiring K] {n p r : ℕ}
    (T : order_three_tensor K n p)
    (u v : Fin r → Fin n → K) (w : Fin r → Fin p → K) : Prop :=
  ∀ (u' v' : Fin r → Fin n → K) (w' : Fin r → Fin p → K),
    tensor_decomposition T u' v' w' →
      ∃ σ : Equiv.Perm (Fin r), ∀ a,
        rank_one_tensor (u' a) (v' a) (w' a) =
          rank_one_tensor (u (σ a)) (v (σ a)) (w (σ a))

@[blueprint "def:pairwise-linearly-independent"
  (statement := /-- A family $(w_a)_{a\in\operatorname{Fin}(r)}$ is pairwise linearly
  independent if, for every two distinct indices $a$ and $b$, the two-vector family
  $(w_a,w_b)$ is linearly independent over $K$. -/)
  (title := /-- Pairwise linear independence -/)
  (latexEnv := "definition")]
def pairwise_linearly_independent {K : Type} [Field K] {r p : ℕ}
    (w : Fin r → Fin p → K) : Prop :=
  ∀ ⦃a b : Fin r⦄, a ≠ b →
    LinearIndependent K (fun t : Fin 2 => if t = 0 then w a else w b)

@[blueprint "def:tensor-slice"
  (statement := /-- For $k\in\operatorname{Fin}(p)$, the $k$-th slice of a tensor $T$ of
  format $n\times n\times p$ is the matrix whose $(i,j)$ entry is $T_{ijk}$. -/)
  (title := /-- Tensor slices -/)
  (latexEnv := "definition")]
def tensor_slice {K : Type} {n p : ℕ} (T : order_three_tensor K n p) (k : Fin p) :
    Matrix (Fin n) (Fin n) K :=
  fun i j => T i j k

@[blueprint "def:tensor-slice-span"
  (statement := /-- The slice span of $T$ is the $K$-linear span of all matrices obtained as
  slices of $T$. -/)
  (title := /-- The span of the slices -/)
  (latexEnv := "definition")]
def tensor_slice_span {K : Type} [Field K] {n p : ℕ} (T : order_three_tensor K n p) :
    Submodule K (Matrix (Fin n) (Fin n) K) :=
  Submodule.span K (Set.range (tensor_slice T))

@[blueprint "def:slice-span-contains-invertible"
  (statement := /-- The slice span of $T$ contains an invertible matrix if there exists a
  matrix $A$ in that span which is a unit of the matrix ring. -/)
  (title := /-- An invertible slice combination -/)
  (latexEnv := "definition")]
def slice_span_contains_invertible {K : Type} [Field K] {n p : ℕ}
    (T : order_three_tensor K n p) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) K, A ∈ tensor_slice_span T ∧ IsUnit A

@[blueprint "def:normalized-nonfirst-slices"
  (statement := /-- Let $T$ have $q+2$ slices and let $A$ be a square matrix. The normalized
  nonfirst slices are the $q+1$ matrices $A^{-1}T_2,\ldots,A^{-1}T_{q+2}$, with Lean index
  $k$ corresponding to the paper index $k+2$. -/)
  (title := /-- Normalized nonfirst slices -/)
  (latexEnv := "definition")]
noncomputable def normalized_nonfirst_slices {K : Type} [Field K] {n q : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (T : order_three_tensor K n (q + 2)) :
    Fin (q + 1) → Matrix (Fin n) (Fin n) K :=
  fun k => A⁻¹ * tensor_slice T k.succ

@[blueprint "def:matrix-commutator"
  (statement := /-- The commutator of square matrices $A$ and $B$ is
  $[A,B]=AB-BA$. -/)
  (title := /-- Matrix commutators -/)
  (latexEnv := "definition")]
def matrix_commutator {K : Type} [Ring K] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  A * B - B * A

@[blueprint "def:matrix-column-span"
  (statement := /-- The column space of an $n\times n$ matrix $A$ is the linear span in $K^n$
  of the functions $i\mapsto A_{ij}$ as $j$ ranges over the column indices. -/)
  (title := /-- Column spaces of matrices -/)
  (latexEnv := "definition")]
def matrix_column_span {K : Type} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) : Submodule K (Fin n → K) :=
  Submodule.span K (Set.range (fun j => fun i => A i j))

@[blueprint "def:commuting-extension-dimension-hypothesis"
  (statement := /-- Let $(B_a)_{a\in\operatorname{Fin}(s)}$ be square matrices and let
  $k,l,m$ be three indices. Hypothesis $(H_{klm})$ asserts that the indices are distinct; that
  the column spaces of $[B_k,B_l]$, $[B_k,B_m]$, and $[B_l,B_m]$ each have dimension
  $2(r-n)$; and that the three sums obtained by fixing in turn $k$, $l$, and $m$ each have
  dimension $3(r-n)$. -/)
  (title := /-- The dimension hypothesis $(H_{klm})$ -/)
  (latexEnv := "definition")]
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

@[blueprint "def:commuting-extension-uniqueness-hypothesis"
  (statement := /-- A tuple $(B_1,\ldots,B_{q+1})$ satisfies the hypothesis of the uniqueness
  theorem for commuting extensions if, for every $l\in\{2,\ldots,q+1\}$, there exists
  $m\notin\{1,l\}$ such that $(H_{1lm})$ holds. Lean index $0$ represents the paper index $1$.
  -/)
  (title := /-- Hypothesis for uniqueness of commuting extensions -/)
  (latexEnv := "definition")]
noncomputable def commuting_extension_uniqueness_hypothesis {K : Type} [Field K]
    {n q : ℕ} (r : ℕ) (B : Fin (q + 1) → Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ l : Fin (q + 1), l ≠ 0 → ∃ m : Fin (q + 1),
    m ≠ 0 ∧ m ≠ l ∧ commuting_extension_dimension_hypothesis r B 0 l m

@[blueprint "def:commuting-extension"
  (statement := /-- Let $(B_k)_{k\in\operatorname{Fin}(s)}$ be $n\times n$ matrices and let
  $\iota:\operatorname{Fin}(n)\hookrightarrow\operatorname{Fin}(r)$ identify the prescribed
  coordinates. A family $(Z_k)_{k\in\operatorname{Fin}(s)}$ of $r\times r$ matrices is a
  commuting extension of $B$ along $\iota$ if the $Z_k$ commute pairwise and the
  $(\iota(i),\iota(j))$ entry of $Z_k$ is $(B_k)_{ij}$ for every $k,i,j$. -/)
  (title := /-- Commuting matrix extensions -/)
  (latexEnv := "definition")]
def commuting_extension {K : Type} [Field K] {n s r : ℕ}
    (B : Fin s → Matrix (Fin n) (Fin n) K)
    (Z : Fin s → Matrix (Fin r) (Fin r) K) (ι : Fin n ↪ Fin r) : Prop :=
  (∀ k l, Commute (Z k) (Z l)) ∧
    ∀ k i j, Z k (ι i) (ι j) = B k i j

@[blueprint "def:coordinate-block-preserving"
  (statement := /-- Let $\iota:\operatorname{Fin}(n)\hookrightarrow\operatorname{Fin}(r)$
  specify a coordinate subspace. A matrix $P\in M_r(K)$ preserves the prescribed block if
  every row and every column indexed by $\iota(i)$ is the corresponding row or column of
  the identity matrix. Equivalently, relative to the prescribed coordinates and their
  coordinate complement, $P$ has the form $I_n\oplus S$. -/)
  (title := /-- Block-preserving changes of complementary coordinates -/)
  (latexEnv := "definition")]
def coordinate_block_preserving {K : Type} [Field K] {n r : ℕ}
    (ι : Fin n ↪ Fin r) (P : Matrix (Fin r) (Fin r) K) : Prop :=
  (∀ i j, P (ι i) j = if ι i = j then 1 else 0) ∧
    ∀ i j, P j (ι i) = if j = ι i then 1 else 0

@[blueprint "def:commuting-extension-equivalent"
  (statement := /-- Let $\iota:\operatorname{Fin}(n)\hookrightarrow\operatorname{Fin}(r)$
  specify the common prescribed coordinates of two size-$r$ matrix families $(Z_k)$ and
  $(Z'_k)$. The families are equivalent along $\iota$ if one invertible matrix $P$ which
  preserves the prescribed block simultaneously conjugates them, so that
  $Z'_k=P^{-1}Z_kP$ for every $k$. -/)
  (title := /-- Block-preserving equivalence of commuting extensions -/)
  (latexEnv := "definition")]
noncomputable def commuting_extension_equivalent {K : Type} [Field K] {n s r : ℕ}
    (ι : Fin n ↪ Fin r) (Z Z' : Fin s → Matrix (Fin r) (Fin r) K) : Prop :=
  ∃ P : Matrix (Fin r) (Fin r) K, IsUnit P ∧ coordinate_block_preserving ι P ∧
    ∀ k, Z' k = P⁻¹ * Z k * P

@[blueprint "def:essentially-unique-commuting-extension"
  (statement := /-- A family $B$ has an essentially unique commuting extension of size $r$
  if, for every coordinate embedding $\iota$, any two size-$r$ commuting extensions of $B$
  along $\iota$ are equivalent by one simultaneous conjugacy which is the identity on the
  prescribed coordinate block. -/)
  (title := /-- Essential uniqueness of a commuting extension -/)
  (latexEnv := "definition")]
def essentially_unique_commuting_extension {K : Type} [Field K] {n s : ℕ}
    (r : ℕ) (B : Fin s → Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ (ι : Fin n ↪ Fin r) (Z Z' : Fin s → Matrix (Fin r) (Fin r) K),
    commuting_extension B Z ι → commuting_extension B Z' ι →
      commuting_extension_equivalent ι Z Z'

@[blueprint "def:tensor-uniqueness-hypotheses"
  (statement := /-- Let $p=q+2$ and let
  $T=\sum_{a=1}^r u_a\otimes v_a\otimes w_a$ have format $n\times n\times p$.
  The uniqueness hypotheses are: $p\geq4$; the displayed equality is a tensor decomposition;
  the vectors $w_a$ are pairwise linearly independent; the span of all slices contains an
  invertible matrix; and there exists an invertible $A$ in that span for which
  $(A^{-1}T_2,\ldots,A^{-1}T_p)$ satisfies the quantified hypotheses $(H_{1lm})$ of the
  uniqueness theorem for commuting extensions. -/)
  (title := /-- Hypotheses of the tensor uniqueness theorem -/)
  (latexEnv := "definition")]
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

@[blueprint "def:tensor-uniqueness-conclusion"
  (statement := /-- The conclusion attached to a fixed length-$r$ decomposition of $T$ is the
  conjunction that $T$ has tensor rank $r$ and that the fixed decomposition is essentially
  unique. -/)
  (title := /-- Conclusion of the tensor uniqueness theorem -/)
  (latexEnv := "definition")]
def tensor_uniqueness_conclusion {K : Type} [Semiring K] {n p r : ℕ}
    (T : order_three_tensor K n p)
    (u v : Fin r → Fin n → K) (w : Fin r → Fin p → K) : Prop :=
  has_tensor_rank T r ∧ essentially_unique_decomposition T u v w

@[blueprint "lem:invertible-slice-forces-row-rank"
  (statement := /-- Let $K$ be a field, let $n,p,s$ be nonnegative integers, and let $T$ be
  an $n\times n\times p$ tensor. Suppose that families
  $(u_a)_{a\in\operatorname{Fin}(s)}$ and $(v_a)_{a\in\operatorname{Fin}(s)}$ in $K^n$, and
  a family $(w_a)_{a\in\operatorname{Fin}(s)}$ in $K^p$, satisfy
  $T=\sum_{a\in\operatorname{Fin}(s)}u_a\otimes v_a\otimes w_a$. If the linear span of the
  slices of $T$ contains an invertible matrix, then $n\leq s$. -/)
  (proof := /-- By \cref{def:slice-span-contains-invertible}, choose an invertible matrix $A$
  in the slice span. Let $U$ be the $n\times s$ matrix whose $a$th column is $u_a$. From
  \cref{def:tensor-decomposition,def:rank-one-tensor,def:tensor-slice}, for each
  $k\in\operatorname{Fin}(p)$ the $k$th slice factors as $T_k=UB_k$, where
  $(B_k)_{aj}=(v_a)_j(w_a)_k$. The matrices of the form $UB$ constitute a linear subspace:
  the zero matrix has factor $0$, sums have factor $B+C$, and scalar multiples have factor
  $cB$. Consequently, the definition of the slice span in \cref{def:tensor-slice-span}
  implies, by induction on span membership, that $A=UB$ for some $s\times n$ matrix $B$.
  Hence the rank inequalities for a matrix product give
  $\operatorname{rank}(A)\leq\operatorname{rank}(U)\leq s$. Since $A$ is invertible,
  $\operatorname{rank}(A)=n$, and therefore $n\leq s$. -/)
  (title := /-- An invertible slice combination bounds decomposition length -/)
  (latexEnv := "lemma")]
lemma invertible_slice_forces_row_rank {K : Type} [Field K] {n p s : ℕ}
    (T : order_three_tensor K n p)
    (u v : Fin s → Fin n → K) (w : Fin s → Fin p → K)
    (hdecomp : tensor_decomposition T u v w)
    (hinvertible : slice_span_contains_invertible T) : n ≤ s := by
  rcases hinvertible with ⟨A, hA, hAunit⟩
  let U : Matrix (Fin n) (Fin s) K := fun i a => u a i
  change T = ∑ a, rank_one_tensor (u a) (v a) (w a) at hdecomp
  have hslice (k : Fin p) :
      ∃ B : Matrix (Fin s) (Fin n) K, tensor_slice T k = U * B := by
    refine ⟨fun a j => v a j * w a k, ?_⟩
    ext i j
    simp [tensor_slice, hdecomp, rank_one_tensor, Matrix.mul_apply, U, mul_assoc]
  have hfactor (M : Matrix (Fin n) (Fin n) K) (hM : M ∈ tensor_slice_span T) :
      ∃ B : Matrix (Fin s) (Fin n) K, M = U * B := by
    change M ∈ Submodule.span K (Set.range (tensor_slice T)) at hM
    refine Submodule.span_induction (R := K) (s := Set.range (tensor_slice T))
      (p := fun M _ => ∃ B, M = U * B) ?_ ?_ ?_ ?_ hM
    · intro X hX
      rcases hX with ⟨k, rfl⟩
      exact hslice k
    · exact ⟨0, by simp⟩
    · intro X Y hX hY ihX ihY
      rcases ihX with ⟨BX, rfl⟩
      rcases ihY with ⟨BY, rfl⟩
      exact ⟨BX + BY, (Matrix.mul_add U BX BY).symm⟩
    · intro c X hX ihX
      rcases ihX with ⟨BX, rfl⟩
      exact ⟨c • BX, (Matrix.mul_smul U c BX).symm⟩
  rcases hfactor A hA with ⟨B, hAB⟩
  calc
    n = A.rank := by simpa using (Matrix.rank_of_isUnit A hAunit).symm
    _ = (U * B).rank := congrArg Matrix.rank hAB
    _ ≤ U.rank := Matrix.rank_mul_le_left U B
    _ ≤ Fintype.card (Fin s) := Matrix.rank_le_card_width U
    _ = s := by simp

@[blueprint "lem:slice-span-coefficient-representation"
  (statement := /-- Every matrix in the slice span of a tensor with finitely many slices is
  a linear combination of those slices, with one scalar coefficient for each slice. -/)
  (proof := /-- Induct on membership in the linear span from
  \cref{def:tensor-slice-span}. A generating slice is represented by its coordinate
  indicator function; the zero matrix, sums, and scalar multiples are represented
  respectively by the zero function, pointwise addition, and pointwise scalar
  multiplication. -/)
  (title := /-- Coefficients for a finite slice-span element -/)
  (latexEnv := "lemma")]
lemma slice_span_coefficient_representation {K : Type} [Field K] {n p : ℕ}
    (T : order_three_tensor K n p) (A : Matrix (Fin n) (Fin n) K)
    (hA : A ∈ tensor_slice_span T) :
    ∃ c : Fin p → K, A = ∑ k, c k • tensor_slice T k := by
  classical
  change A ∈ Submodule.span K (Set.range (tensor_slice T)) at hA
  refine Submodule.span_induction (R := K) (s := Set.range (tensor_slice T))
    (p := fun M _ => ∃ c : Fin p → K, M = ∑ k, c k • tensor_slice T k)
    ?_ ?_ ?_ ?_ hA
  · intro M hM
    rcases hM with ⟨k, rfl⟩
    refine ⟨fun j => if j = k then 1 else 0, ?_⟩
    simp
  · exact ⟨0, by simp⟩
  · intro X Y _ _ hX hY
    rcases hX with ⟨c, rfl⟩
    rcases hY with ⟨d, rfl⟩
    refine ⟨c + d, ?_⟩
    simp [Finset.sum_add_distrib, add_smul]
  · intro a X _ hX
    rcases hX with ⟨c, rfl⟩
    refine ⟨a • c, ?_⟩
    simp [Finset.smul_sum, smul_smul]

@[blueprint "def:three-scalar-skew"
  (statement := /-- For scalars $a,b,c$, the associated alternating three-by-three matrix
  has upper-triangular entries $a,b,c$ and the negatives of these entries below the
  diagonal. -/)
  (title := /-- A three-dimensional alternating matrix -/)
  (latexEnv := "definition")]
def three_scalar_skew {K : Type} [Ring K] (a b c : K) : Matrix (Fin 3) (Fin 3) K :=
  fun i j =>
    if i = 0 then
      if j = 1 then a else if j = 2 then b else 0
    else if i = 1 then
      if j = 0 then -a else if j = 2 then c else 0
    else
      if j = 0 then -b else if j = 1 then -c else 0

@[blueprint "def:three-slice-skew-block"
  (statement := /-- For square matrices $A,B,C$, the three-slice skew block matrix has
  block rows $(0,A,B)$, $(-A,0,C)$, and $(-B,-C,0)$. -/)
  (title := /-- The three-slice skew block matrix -/)
  (latexEnv := "definition")]
def three_slice_skew_block {K : Type} [Ring K] {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) K :=
  fun i j =>
    if i.1 = 0 then
      if j.1 = 1 then A i.2 j.2 else if j.1 = 2 then B i.2 j.2 else 0
    else if i.1 = 1 then
      if j.1 = 0 then -A i.2 j.2 else if j.1 = 2 then C i.2 j.2 else 0
    else
      if j.1 = 0 then -B i.2 j.2 else if j.1 = 1 then -C i.2 j.2 else 0

@[blueprint "def:three-block-canonical"
  (statement := /-- For a square matrix $D$, the canonical three-block matrix has block
  rows $(0,I,0)$, $(-I,0,0)$, and $(0,0,D)$. -/)
  (title := /-- A canonical three-block matrix -/)
  (latexEnv := "definition")]
def three_block_canonical {K : Type} [Ring K] {n : ℕ}
    (D : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) K :=
  fun i j =>
    if i.1 = 0 then
      if j.1 = 1 then if i.2 = j.2 then 1 else 0 else 0
    else if i.1 = 1 then
      if j.1 = 0 then if i.2 = j.2 then -1 else 0 else 0
    else
      if j.1 = 2 then D i.2 j.2 else 0

@[blueprint "def:three-block-index-equiv"
  (statement := /-- The product index $\operatorname{Fin}(3)\times\operatorname{Fin}(n)$
  is identified with three successive copies of $\operatorname{Fin}(n)$. -/)
  (title := /-- Reindexing three equal blocks -/)
  (latexEnv := "definition")]
def three_block_index_equiv (n : ℕ) :
    Fin 3 × Fin n ≃ (Fin n ⊕ Fin n) ⊕ Fin n :=
  { toFun := fun i =>
      if i.1 = 0 then Sum.inl (Sum.inl i.2)
      else if i.1 = 1 then Sum.inl (Sum.inr i.2)
      else Sum.inr i.2
    invFun := fun i =>
      match i with
      | Sum.inl (Sum.inl j) => (0, j)
      | Sum.inl (Sum.inr j) => (1, j)
      | Sum.inr j => (2, j)
    left_inv := by
      intro i
      rcases i with ⟨i, ii⟩
      fin_cases i <;> simp
    right_inv := by
      intro i
      rcases i with (i | i)
      · rcases i with (i | i) <;> simp
      · simp }

@[blueprint "lem:matrix-rank-add-le"
  (statement := /-- Over a field, the rank of the sum of two matrices is at most the sum of
  their ranks. -/)
  (proof := /-- Every column of $X+Y$ is the sum of a column of $X$ and the corresponding
  column of $Y$. Hence its column span is contained in the sum of the two column spans.
  Monotonicity of dimension and subadditivity of the dimension of a sum give the result. -/)
  (title := /-- Subadditivity of matrix rank -/)
  (latexEnv := "lemma")]
lemma matrix_rank_add_le {K : Type} [Field K] {m n : Type}
    [Fintype m] [Fintype n] (X Y : Matrix m n K) :
    (X + Y).rank ≤ X.rank + Y.rank := by
  classical
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols,
    Matrix.rank_eq_finrank_span_cols]
  refine le_trans (Submodule.finrank_mono ?_)
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
  refine Submodule.span_le.2 ?_
  rintro z ⟨j, rfl⟩
  change X.col j + Y.col j ∈
    Submodule.span K (Set.range X.col) ⊔ Submodule.span K (Set.range Y.col)
  apply (Submodule.span K (Set.range X.col) ⊔
    Submodule.span K (Set.range Y.col)).add_mem
  · exact (show Submodule.span K (Set.range X.col) ≤
        Submodule.span K (Set.range X.col) ⊔
          Submodule.span K (Set.range Y.col) from le_sup_left)
      (Submodule.subset_span ⟨j, rfl⟩)
  · exact (show Submodule.span K (Set.range Y.col) ≤
        Submodule.span K (Set.range X.col) ⊔
          Submodule.span K (Set.range Y.col) from le_sup_right)
      (Submodule.subset_span ⟨j, rfl⟩)

@[blueprint "lem:three-scalar-skew-rank-le-two"
  (statement := /-- The rank of a three-dimensional alternating matrix over a field is at
  most two. -/)
  (proof := /-- If all three parameters vanish, the matrix is zero. Otherwise the nonzero
  vector $(c,-b,a)$ lies in its kernel. Rank-nullity in dimension three then bounds the
  rank by two. -/)
  (title := /-- Rank of a three-dimensional alternating matrix -/)
  (latexEnv := "lemma")]
lemma three_scalar_skew_rank_le_two {K : Type} [Field K] (a b c : K) :
    (three_scalar_skew a b c).rank ≤ 2 := by
  classical
  by_cases hzero : a = 0 ∧ b = 0 ∧ c = 0
  · rcases hzero with ⟨rfl, rfl, rfl⟩
    have hz : three_scalar_skew (0 : K) 0 0 = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [three_scalar_skew]
    rw [hz]
    simpa using
      (Matrix.rank_zero (R := K) (m := Fin 3) (n := Fin 3))
  · let x : Fin 3 → K := fun i =>
      if i = 0 then c else if i = 1 then -b else a
    have hx : x ≠ 0 := by
      intro hx0
      have hc := congrFun hx0 (0 : Fin 3)
      have hb := congrFun hx0 (1 : Fin 3)
      have ha := congrFun hx0 (2 : Fin 3)
      simp [x] at ha hb hc
      exact hzero ⟨ha, hb, hc⟩
    have hxker : x ∈ (three_scalar_skew a b c).mulVecLin.ker := by
      rw [LinearMap.mem_ker]
      ext i
      fin_cases i <;>
        simp [Matrix.mulVecLin_apply, Matrix.mulVec, three_scalar_skew, x,
          dotProduct, Fin.sum_univ_three] <;> ring
    have hker : 1 ≤ Module.finrank K (three_scalar_skew a b c).mulVecLin.ker := by
      rw [Submodule.one_le_finrank_iff]
      intro hbot
      apply hx
      have hxmem : x ∈ (⊥ : Submodule K (Fin 3 → K)) := by
        rw [← hbot]
        exact hxker
      simpa using hxmem
    have hrn :=
      LinearMap.finrank_range_add_finrank_ker
        (three_scalar_skew a b c).mulVecLin
    change Module.finrank K
      (LinearMap.range (three_scalar_skew a b c).mulVecLin) ≤ 2
    have hdim : Module.finrank K (Fin 3 → K) = 3 := by simp
    omega

@[blueprint "lem:three-slice-skew-rank-one-le-two"
  (statement := /-- If the three blocks of a three-slice skew block matrix are scalar
  multiples of the same rank-one matrix, then the block matrix has rank at most two. -/)
  (proof := /-- Factor the block matrix through the three-dimensional alternating matrix
  from \cref{lem:three-scalar-skew-rank-le-two}: the left factor inserts the vector $u$ in
  each block and the right factor evaluates against $v$. The rank of a product does not
  exceed the rank of its middle factor. -/)
  (title := /-- Rank of one skew-block summand -/)
  (latexEnv := "lemma")]
lemma three_slice_skew_rank_one_le_two {K : Type} [Field K] {n : ℕ}
    (u v : Fin n → K) (a b c : K) :
    (three_slice_skew_block
      (a • Matrix.vecMulVec u v)
      (b • Matrix.vecMulVec u v)
      (c • Matrix.vecMulVec u v)).rank ≤ 2 := by
  classical
  let L : Matrix (Fin 3 × Fin n) (Fin 3) K :=
    fun i t => if i.1 = t then u i.2 else 0
  let R : Matrix (Fin 3) (Fin 3 × Fin n) K :=
    fun t j => if t = j.1 then v j.2 else 0
  have hfactor :
      three_slice_skew_block
          (a • Matrix.vecMulVec u v)
          (b • Matrix.vecMulVec u v)
          (c • Matrix.vecMulVec u v) =
        (L * three_scalar_skew a b c) * R := by
    ext i j
    rcases i with ⟨i, ii⟩
    rcases j with ⟨j, jj⟩
    fin_cases i <;> fin_cases j <;>
      simp [L, R, Matrix.mul_apply, three_slice_skew_block, three_scalar_skew,
        Fin.sum_univ_three, Matrix.vecMulVec, mul_assoc, mul_left_comm, mul_comm]
  rw [hfactor]
  calc
    ((L * three_scalar_skew a b c) * R).rank ≤
        (L * three_scalar_skew a b c).rank :=
      Matrix.rank_mul_le_left _ _
    _ ≤ (three_scalar_skew a b c).rank :=
      Matrix.rank_mul_le_right _ _
    _ ≤ 2 := three_scalar_skew_rank_le_two a b c

@[blueprint "lem:three-slice-skew-upper-bound"
  (statement := /-- If three square matrices admit simultaneous expansions as sums of $s$
  rank-one matrices, then their three-slice skew block matrix has rank at most $2s$. -/)
  (proof := /-- Expand the block matrix as the sum of the $s$ skew block matrices attached
  to the individual rank-one terms. Each summand has rank at most two by
  \cref{lem:three-slice-skew-rank-one-le-two}. Repeated use of
  \cref{lem:matrix-rank-add-le} gives the bound $2s$. -/)
  (title := /-- Upper rank bound for the three-slice skew matrix -/)
  (latexEnv := "lemma")]
lemma three_slice_skew_upper_bound {K : Type} [Field K] {n s : ℕ}
    (u v : Fin s → Fin n → K) (α β γ : Fin s → K)
    (A B C : Matrix (Fin n) (Fin n) K)
    (hA : A = ∑ a, α a • Matrix.vecMulVec (u a) (v a))
    (hB : B = ∑ a, β a • Matrix.vecMulVec (u a) (v a))
    (hC : C = ∑ a, γ a • Matrix.vecMulVec (u a) (v a)) :
    (three_slice_skew_block A B C).rank ≤ 2 * s := by
  classical
  let F : Fin s → Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) K :=
    fun a => three_slice_skew_block
      (α a • Matrix.vecMulVec (u a) (v a))
      (β a • Matrix.vecMulVec (u a) (v a))
      (γ a • Matrix.vecMulVec (u a) (v a))
  have hsum : three_slice_skew_block A B C = ∑ a, F a := by
    rw [hA, hB, hC]
    ext i j
    rcases i with ⟨i, ii⟩
    rcases j with ⟨j, jj⟩
    fin_cases i <;> fin_cases j <;>
      simp [F, three_slice_skew_block, Matrix.sum_apply, Matrix.smul_apply]
  have hfin (t : Finset (Fin s)) :
      (∑ a ∈ t, F a).rank ≤ 2 * t.card := by
    induction t using Finset.induction_on with
    | empty =>
        simp
    | @insert a t ha ih =>
        rw [Finset.sum_insert ha]
        calc
          (F a + ∑ x ∈ t, F x).rank ≤
              (F a).rank + (∑ x ∈ t, F x).rank :=
            matrix_rank_add_le _ _
          _ ≤ 2 + 2 * t.card := Nat.add_le_add
            (three_slice_skew_rank_one_le_two
              (u a) (v a) (α a) (β a) (γ a)) ih
          _ = 2 * (insert a t).card := by simp [ha]; omega
  rw [hsum]
  simpa using hfin Finset.univ

@[blueprint "lem:three-block-canonical-rank"
  (statement := /-- The rank of the canonical three-block matrix associated with an
  $n\times n$ matrix $D$ is $2n+\operatorname{rank}(D)$. -/)
  (proof := /-- Its kernel consists exactly of vectors whose first two blocks vanish and
  whose third block lies in the kernel of $D$. Restriction to the third block is therefore
  a linear equivalence of kernels. Apply rank-nullity to the canonical map, whose domain has
  dimension $3n$, and to $D$, whose domain has dimension $n$. -/)
  (title := /-- Rank of the canonical three-block matrix -/)
  (latexEnv := "lemma")]
lemma three_block_canonical_rank {K : Type} [Field K] {n : ℕ}
    (D : Matrix (Fin n) (Fin n) K) :
    (three_block_canonical D).rank = 2 * n + D.rank := by
  classical
  let Φ := (three_block_canonical D).mulVecLin
  let Ψ := D.mulVecLin
  let e : Φ.ker ≃ₗ[K] Ψ.ker :=
    { toFun := fun x => ⟨fun i => x.1 (2, i), by
        rw [LinearMap.mem_ker]
        funext i
        have h := congrFun x.2 (2, i)
        dsimp [Φ, Matrix.mulVecLin_apply] at h
        simpa [Ψ, three_block_canonical, Matrix.mulVecLin_apply,
          Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three] using h⟩
      invFun := fun z => ⟨fun i => if i.1 = 2 then z.1 i.2 else 0, by
        rw [LinearMap.mem_ker]
        ext i
        rcases i with ⟨i, ii⟩
        fin_cases i
        · simp [Φ, three_block_canonical, Matrix.mulVecLin_apply,
            Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three]
        · simp [Φ, three_block_canonical, Matrix.mulVecLin_apply,
            Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three]
        · have h := congrFun z.2 ii
          dsimp [Ψ, Matrix.mulVecLin_apply] at h
          simpa [Φ, three_block_canonical, Matrix.mulVecLin_apply,
            Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three] using h⟩
      left_inv := by
        intro x
        apply Subtype.ext
        funext i
        rcases i with ⟨i, ii⟩
        fin_cases i
        · have h := congrFun x.2 (1, ii)
          dsimp [Φ, Matrix.mulVecLin_apply] at h
          have hx0 : x.1 (0, ii) = 0 := by
            have hn : -x.1 (0, ii) = 0 := by
              simpa [three_block_canonical, Matrix.mulVec,
                dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three] using h
            simpa using neg_eq_zero.mp hn
          simp [hx0]
        · have h := congrFun x.2 (0, ii)
          dsimp [Φ, Matrix.mulVecLin_apply] at h
          have hx1 : x.1 (1, ii) = 0 := by
            simpa [three_block_canonical, Matrix.mulVec,
              dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three] using h
          simp [hx1]
        · simp
      right_inv := by
        intro z
        apply Subtype.ext
        funext i
        simp
      map_add' := by
        intro x y
        apply Subtype.ext
        rfl
      map_smul' := by
        intro a x
        apply Subtype.ext
        rfl }
  have hker : Module.finrank K Φ.ker = Module.finrank K Ψ.ker :=
    e.finrank_eq
  have hΦ := LinearMap.finrank_range_add_finrank_ker Φ
  have hΨ := LinearMap.finrank_range_add_finrank_ker Ψ
  have hdimΦ : Module.finrank K (Fin 3 × Fin n → K) = 3 * n := by
    simp
  have hdimΨ : Module.finrank K (Fin n → K) = n := by
    simp
  change Module.finrank K (LinearMap.range Φ) =
    2 * n + Module.finrank K (LinearMap.range Ψ)
  omega

@[blueprint "lem:three-slice-skew-lower-bound"
  (statement := /-- If $A$ is invertible, the rank of the three-slice skew block matrix
  associated with $A,B,C$ is at least
  \[
    2n+\operatorname{rank}[A^{-1}B,A^{-1}C].
  \] -/)
  (proof := /-- Reindex the matrix as a two-by-two block matrix whose leading block is
  $\left(\begin{smallmatrix}0&A\\-A&0\end{smallmatrix}\right)$. Its explicit inverse gives
  block Gaussian elimination to a block diagonal matrix. The trailing Schur complement,
  after left multiplication by $A^{-1}$, is the required commutator, so its rank is at least
  the commutator rank. A final block-row multiplication converts the leading invertible
  block to the canonical form of \cref{lem:three-block-canonical-rank}, whose rank is twice
  $n$ plus the rank of its trailing block. -/)
  (title := /-- Lower rank bound for the three-slice skew matrix -/)
  (latexEnv := "lemma")]
lemma three_slice_skew_lower_bound {K : Type} [Field K] {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) K) (hAunit : IsUnit A) :
    2 * n + (matrix_commutator (A⁻¹ * B) (A⁻¹ * C)).rank ≤
      (three_slice_skew_block A B C).rank := by
  classical
  let J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
    Matrix.fromBlocks 0 A (-A) 0
  let Jinv : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
    Matrix.fromBlocks 0 (-A⁻¹) A⁻¹ 0
  let U : Matrix (Fin n ⊕ Fin n) (Fin n) K :=
    fun i j => match i with
      | Sum.inl i => B i j
      | Sum.inr i => C i j
  let V : Matrix (Fin n) (Fin n ⊕ Fin n) K :=
    fun i j => match j with
      | Sum.inl j => -B i j
      | Sum.inr j => -C i j
  let M : Matrix ((Fin n ⊕ Fin n) ⊕ Fin n) ((Fin n ⊕ Fin n) ⊕ Fin n) K :=
    Matrix.fromBlocks J U V 0
  let S : Matrix (Fin n) (Fin n) K := -(V * Jinv * U)
  let P : Matrix ((Fin n ⊕ Fin n) ⊕ Fin n) ((Fin n ⊕ Fin n) ⊕ Fin n) K :=
    Matrix.fromBlocks 1 0 (-V * Jinv) 1
  let Q : Matrix ((Fin n ⊕ Fin n) ⊕ Fin n) ((Fin n ⊕ Fin n) ⊕ Fin n) K :=
    Matrix.fromBlocks 1 (-Jinv * U) 0 1
  let J₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
    Matrix.fromBlocks 0 1 (-1) 0
  let R : Matrix ((Fin n ⊕ Fin n) ⊕ Fin n) ((Fin n ⊕ Fin n) ⊕ Fin n) K :=
    Matrix.fromBlocks (J₀ * Jinv) 0 0 1
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hAunit
  have hJinvJ : Jinv * J = 1 := by
    simp [Jinv, J, Matrix.fromBlocks_multiply, Matrix.nonsing_inv_mul A hdet]
  have hJJinv : J * Jinv = 1 := by
    simp [Jinv, J, Matrix.fromBlocks_multiply, Matrix.mul_nonsing_inv A hdet]
  have hJU : J * (Jinv * U) = U := by
    calc
      J * (Jinv * U) = (J * Jinv) * U := (Matrix.mul_assoc _ _ _).symm
      _ = U := by rw [hJJinv, Matrix.one_mul]
  have hVJ : V * Jinv * J = V := by
    calc
      V * Jinv * J = V * (Jinv * J) := Matrix.mul_assoc _ _ _
      _ = V := by rw [hJinvJ, Matrix.mul_one]
  have hElim :
      (P * M) * Q = Matrix.fromBlocks J 0 0 S := by
    simp [P, M, Q, S, Matrix.fromBlocks_multiply, mul_assoc, hJU, hVJ]
  have hNormalize :
      R * Matrix.fromBlocks J 0 0 S =
        Matrix.fromBlocks J₀ 0 0 S := by
    simp [R, Matrix.fromBlocks_multiply, mul_assoc, hJinvJ]
  let e := three_block_index_equiv n
  have hSkewReindex :
      (three_slice_skew_block A B C).reindex e e = M := by
    ext i j
    rcases i with (i | i)
    · rcases i with (i | i)
      · rcases j with (j | j)
        · rcases j with (j | j) <;>
            simp [e, M, J, U, V, three_block_index_equiv,
              three_slice_skew_block, Matrix.reindex_apply]
        · simp [e, M, J, U, V, three_block_index_equiv,
            three_slice_skew_block, Matrix.reindex_apply]
      · rcases j with (j | j)
        · rcases j with (j | j) <;>
            simp [e, M, J, U, V, three_block_index_equiv,
              three_slice_skew_block, Matrix.reindex_apply]
        · simp [e, M, J, U, V, three_block_index_equiv,
            three_slice_skew_block, Matrix.reindex_apply]
    · rcases j with (j | j)
      · rcases j with (j | j) <;>
          simp [e, M, J, U, V, three_block_index_equiv,
            three_slice_skew_block, Matrix.reindex_apply]
      · simp [e, M, J, U, V, three_block_index_equiv,
          three_slice_skew_block, Matrix.reindex_apply]
  have hCanonicalReindex :
      (three_block_canonical S).reindex e e =
        Matrix.fromBlocks J₀ 0 0 S := by
    ext i j
    rcases i with (i | i)
    · rcases i with (i | i)
      · rcases j with (j | j)
        · rcases j with (j | j) <;>
            simp [e, J₀, three_block_index_equiv, three_block_canonical,
              Matrix.reindex_apply, Matrix.one_apply] <;>
            split_ifs <;> simp_all
        · simp [e, J₀, three_block_index_equiv, three_block_canonical,
            Matrix.reindex_apply, Matrix.one_apply]
      · rcases j with (j | j)
        · rcases j with (j | j) <;>
            simp [e, J₀, three_block_index_equiv, three_block_canonical,
              Matrix.reindex_apply, Matrix.one_apply] <;>
            split_ifs <;> simp_all
        · simp [e, J₀, three_block_index_equiv, three_block_canonical,
            Matrix.reindex_apply, Matrix.one_apply]
    · rcases j with (j | j)
      · rcases j with (j | j) <;>
          simp [e, J₀, three_block_index_equiv, three_block_canonical,
            Matrix.reindex_apply, Matrix.one_apply]
      · simp [e, J₀, three_block_index_equiv, three_block_canonical,
          Matrix.reindex_apply, Matrix.one_apply]
    all_goals split_ifs <;> simp_all
  have hProduct :
      R * ((P * M) * Q) = Matrix.fromBlocks J₀ 0 0 S := by
    rw [hElim]
    exact hNormalize
  have hCanonicalLe :
      (three_block_canonical S).rank ≤ (three_slice_skew_block A B C).rank := by
    calc
      (three_block_canonical S).rank =
          ((three_block_canonical S).reindex e e).rank :=
        (Matrix.rank_reindex e e _).symm
      _ = (R * ((P * M) * Q)).rank := by rw [hCanonicalReindex, hProduct]
      _ ≤ ((P * M) * Q).rank := Matrix.rank_mul_le_right _ _
      _ ≤ (P * M).rank := Matrix.rank_mul_le_left _ _
      _ ≤ M.rank := Matrix.rank_mul_le_right _ _
      _ = ((three_slice_skew_block A B C).reindex e e).rank := by
        rw [hSkewReindex]
      _ = (three_slice_skew_block A B C).rank :=
        Matrix.rank_reindex e e _
  let W : Matrix (Fin n ⊕ Fin n) (Fin n) K :=
    fun i j => match i with
      | Sum.inl i => -(A⁻¹ * C) i j
      | Sum.inr i => (A⁻¹ * B) i j
  have hJinvU : Jinv * U = W := by
    ext i j
    rcases i with (i | i)
    · simp [Jinv, U, W, Matrix.mul_apply, Matrix.fromBlocks,
        Fintype.sum_sum_type, Finset.sum_neg_distrib]
    · simp [Jinv, U, W, Matrix.mul_apply, Matrix.fromBlocks,
        Fintype.sum_sum_type]
  have hVW :
      V * W = B * (A⁻¹ * C) - C * (A⁻¹ * B) := by
    ext i j
    simp [V, W, Matrix.mul_apply, Fintype.sum_sum_type,
      Finset.sum_neg_distrib, sub_eq_add_neg]
  have hVJU :
      V * Jinv * U = B * (A⁻¹ * C) - C * (A⁻¹ * B) := by
    calc
      V * Jinv * U = V * (Jinv * U) := Matrix.mul_assoc _ _ _
      _ = V * W := by rw [hJinvU]
      _ = _ := hVW
  have hComm :
      matrix_commutator (A⁻¹ * B) (A⁻¹ * C) = A⁻¹ * (-S) := by
    rw [show -S = V * Jinv * U by simp [S]]
    rw [hVJU]
    simp [matrix_commutator, mul_sub, mul_assoc]
  have hCommLe :
      (matrix_commutator (A⁻¹ * B) (A⁻¹ * C)).rank ≤ S.rank := by
    rw [hComm]
    calc
      (A⁻¹ * -S).rank ≤ (-S).rank := Matrix.rank_mul_le_right _ _
      _ ≤ S.rank := by
        rw [show -S = (-1 : Matrix (Fin n) (Fin n) K) * S by simp]
        exact Matrix.rank_mul_le_right _ _
  have hCanonicalRank := three_block_canonical_rank S
  omega

@[blueprint "lem:strassen-skew-flattening-matrix-bound"
  (statement := /-- Let three $n\times n$ matrices $A,B,C$ be simultaneous sums of $s$
  rank-one matrices, with scalar coefficient families $\alpha,\beta,\gamma$. If $A$ is
  invertible and $n\leq s$, then
  \[
    \operatorname{rank}[A^{-1}B,A^{-1}C]\leq 2(s-n).
  \] -/)
  (proof := /-- By \cref{lem:three-slice-skew-upper-bound}, the simultaneous rank-one
  expansions bound the rank of the associated three-slice skew block matrix by $2s$.
  By \cref{lem:three-slice-skew-lower-bound}, invertibility of $A$ bounds the same rank
  below by $2n+\operatorname{rank}[A^{-1}B,A^{-1}C]$. Combining these inequalities and
  using $n\leq s$ gives
  $\operatorname{rank}[A^{-1}B,A^{-1}C]\leq 2(s-n)$. -/)
  (title := /-- The skew-flattening matrix inequality -/)
  (latexEnv := "lemma")]
lemma strassen_skew_flattening_matrix_bound {K : Type} [Field K] {n s : ℕ}
    (u v : Fin s → Fin n → K) (α β γ : Fin s → K)
    (A B C : Matrix (Fin n) (Fin n) K)
    (hA : A = ∑ a, α a • Matrix.vecMulVec (u a) (v a))
    (hB : B = ∑ a, β a • Matrix.vecMulVec (u a) (v a))
    (hC : C = ∑ a, γ a • Matrix.vecMulVec (u a) (v a))
    (hAunit : IsUnit A) (hns : n ≤ s) :
    (matrix_commutator (A⁻¹ * B) (A⁻¹ * C)).rank ≤ 2 * (s - n) := by
  have hupper := three_slice_skew_upper_bound u v α β γ A B C hA hB hC
  have hlower := three_slice_skew_lower_bound A B C hAunit
  omega

@[blueprint "lem:strassen-three-slice-commutator-bound"
  (statement := /-- Let $T$ be an $n\times n\times p$ tensor with a decomposition of
  length $s$, and let $A$ be an invertible matrix in the span of its slices. For any two
  slice indices $k$ and $l$, the column rank of the commutator
  $[A^{-1}T_k,A^{-1}T_l]$ is at most $2(s-n)$. -/)
  (proof := /-- By \cref{lem:invertible-slice-forces-row-rank}, one has $n\leq s$.
  Use \cref{lem:slice-span-coefficient-representation} to express $A$ with the same
  rank-one terms as the tensor slices. The simultaneous rank-one expansions of
  $A,T_k,T_l$ then satisfy \cref{lem:strassen-skew-flattening-matrix-bound}, which gives
  the asserted commutator-rank bound. -/)
  (title := /-- Strassen's three-slice commutator bound -/)
  (latexEnv := "lemma")]
lemma strassen_three_slice_commutator_bound {K : Type} [Field K] {n p s : ℕ}
    (T : order_three_tensor K n p)
    (u v : Fin s → Fin n → K) (w : Fin s → Fin p → K)
    (hdecomp : tensor_decomposition T u v w)
    (A : Matrix (Fin n) (Fin n) K)
    (hAspan : A ∈ tensor_slice_span T) (hAunit : IsUnit A)
    (k l : Fin p) :
    Module.finrank K
        (matrix_column_span
          (matrix_commutator (A⁻¹ * tensor_slice T k) (A⁻¹ * tensor_slice T l))) ≤
      2 * (s - n) := by
  classical
  have hns : n ≤ s :=
    invertible_slice_forces_row_rank T u v w hdecomp ⟨A, hAspan, hAunit⟩
  rcases slice_span_coefficient_representation T A hAspan with ⟨c, hAc⟩
  let α : Fin s → K := fun a => ∑ j, c j * w a j
  change T = ∑ a, rank_one_tensor (u a) (v a) (w a) at hdecomp
  have hslice (j : Fin p) :
      tensor_slice T j = ∑ a, w a j • Matrix.vecMulVec (u a) (v a) := by
    rw [hdecomp]
    ext i t
    simp [tensor_slice, rank_one_tensor, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.vecMulVec_apply, mul_assoc, mul_left_comm, mul_comm]
  have hslice_apply (j : Fin p) (i t : Fin n) :
      tensor_slice T j i t = ∑ a, w a j * (u a i * v a t) := by
    rw [hslice]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply]
    change (∑ a, w a j * (u a i * v a t)) =
      ∑ a, w a j * (u a i * v a t)
    rfl
  have hAform : A = ∑ a, α a • Matrix.vecMulVec (u a) (v a) := by
    rw [hAc]
    ext i t
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply]
    change (∑ j, c j * tensor_slice T j i t) =
      ∑ a, α a * (u a i * v a t)
    simp_rw [hslice_apply]
    simp only [α]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp [mul_assoc, mul_left_comm, mul_comm]
  have hrank :=
    strassen_skew_flattening_matrix_bound u v α (fun a => w a k) (fun a => w a l)
      A (tensor_slice T k) (tensor_slice T l) hAform (hslice k) (hslice l) hAunit hns
  change
    Module.finrank K
        (Submodule.span K
          (Set.range
            (matrix_commutator (A⁻¹ * tensor_slice T k) (A⁻¹ * tensor_slice T l)).col)) ≤
      2 * (s - n)
  rw [← Matrix.rank_eq_finrank_span_cols]
  exact hrank

@[blueprint "lem:strassen-rank-lower-bound"
  (statement := /-- Let $K$ be a field, let $p=q+2\geq4$, and suppose that the displayed
  length-$r$ decomposition of an $n\times n\times p$ tensor $T$ satisfies the tensor
  uniqueness hypotheses. Then every decomposition of $T$ of length $s$ satisfies $r\leq s$.
  -/)
  (proof := /-- Apply \cref{lem:invertible-slice-forces-row-rank} first to the displayed
  decomposition and then to the competing decomposition; this gives $n\leq r$ and $n\leq s$.
  Choose any nonzero normalized-slice index $l$. Such an index exists because $q+2\geq4$.
  By \cref{def:commuting-extension-uniqueness-hypothesis}, there is an index
  $m\notin\{0,l\}$ for which $H_{0lm}$ holds. Let $A$ be the invertible slice combination
  supplied by \cref{def:tensor-uniqueness-hypotheses}. Applying
  \cref{lem:strassen-three-slice-commutator-bound} to the competing decomposition and the
  two slices indexed by $l$ and $m$ gives
  \[
     s\geq n+\frac12\operatorname{rank}[A^{-1}T_{l+2},A^{-1}T_{m+2}].
  \]
  By \cref{def:commuting-extension-dimension-hypothesis}, the column space of this
  commutator has dimension $2(r-n)$. Thus $s\geq n+(r-n)=r$, where the last equality uses
  $n\leq r$. This proves the asserted lower bound for every competing decomposition. -/)
  (title := /-- Strassen's bound gives tensor-rank minimality -/)
  (latexEnv := "lemma")]
lemma strassen_rank_lower_bound {K : Type} [Field K] {n q r s : ℕ}
    (T : order_three_tensor K n (q + 2))
    (u v : Fin r → Fin n → K) (w : Fin r → Fin (q + 2) → K)
    (hq : 2 ≤ q)
    (h : tensor_uniqueness_hypotheses T u v w)
    (u' v' : Fin s → Fin n → K) (w' : Fin s → Fin (q + 2) → K)
    (hdecomp' : tensor_decomposition T u' v' w') : r ≤ s := by
  rcases h with ⟨_, hdecomp, _, hinvertible, A, hAspan, hAunit, hunique⟩
  have hnr : n ≤ r :=
    invertible_slice_forces_row_rank T u v w hdecomp hinvertible
  have hns : n ≤ s :=
    invertible_slice_forces_row_rank T u' v' w' hdecomp' hinvertible
  let l : Fin (q + 1) := ⟨1, by omega⟩
  have hl : l ≠ 0 := by
    simp [l]
  rcases hunique l hl with ⟨m, _, _, hdim⟩
  have hcomm :
      Module.finrank K
          (matrix_column_span
            (matrix_commutator
              (A⁻¹ * tensor_slice T l.succ)
              (A⁻¹ * tensor_slice T m.succ))) =
        2 * (r - n) := by
    exact hdim.2.2.2.2.2.1
  have hbound :
      Module.finrank K
          (matrix_column_span
            (matrix_commutator
              (A⁻¹ * tensor_slice T l.succ)
              (A⁻¹ * tensor_slice T m.succ))) ≤
        2 * (s - n) :=
    strassen_three_slice_commutator_bound
      T u' v' w' hdecomp' A hAspan hAunit l.succ m.succ
  omega

@[blueprint "lem:extremal-block-commutator-rank"
  (statement := /-- Let $K$ be a field, let $E$ and $C$ be finite index sets, and put
  $d=|C|$. Suppose that $A,B:E\leftarrow C$, $P,Q:C\leftarrow E$, and an endomorphism
  $M$ of $K^E$ satisfy $M=AP-BQ$ and $\dim\operatorname{im}M=2d$. Then $A$ and $B$
  are injective with $d$-dimensional disjoint images, these images sum to
  $\operatorname{im}M$, the products $AP$ and $BQ$ have the same images as $A$ and $B$,
  respectively, and $P$ and $Q$ are surjective. -/)
  (proof := /-- The image of $M$ is contained in the sum of the images of $A$ and $B$,
  while each of those images has dimension at most $d$. Equality
  $\dim\operatorname{im}M=2d$ forces equality at every stage of this dimension bound.
  Grassmann's identity then makes the two images disjoint, and rank--nullity makes $A$ and
  $B$ injective. Applying the same bound to the images of $AP$ and $BQ$ shows that they
  fill the images of $A$ and $B$; injectivity of the latter maps then makes $P$ and $Q$
  surjective. -/)
  (title := /-- Equality in the block-commutator rank bound -/)
  (latexEnv := "lemma")]
lemma extremal_block_commutator_rank {K : Type} [Field K] {E C : Type}
    [Fintype E] [DecidableEq E] [Fintype C] [DecidableEq C]
    (A B : Matrix E C K) (P Q : Matrix C E K) (M : Matrix E E K)
    (hM : M = A * P - B * Q)
    (hrank : Module.finrank K (LinearMap.range M.mulVecLin) = 2 * Fintype.card C) :
    Module.finrank K (LinearMap.range A.mulVecLin) = Fintype.card C ∧
    Module.finrank K (LinearMap.range B.mulVecLin) = Fintype.card C ∧
    LinearMap.range M.mulVecLin =
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin ∧
    LinearMap.range A.mulVecLin ⊓ LinearMap.range B.mulVecLin = ⊥ ∧
    LinearMap.range (A * P).mulVecLin = LinearMap.range A.mulVecLin ∧
    LinearMap.range (B * Q).mulVecLin = LinearMap.range B.mulVecLin ∧
    Function.Injective A.mulVecLin ∧ Function.Injective B.mulVecLin ∧
    Function.Surjective P.mulVecLin ∧ Function.Surjective Q.mulVecLin := by
  have hAP : LinearMap.range (A * P).mulVecLin ≤ LinearMap.range A.mulVecLin := by
    rw [Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  have hBQ : LinearMap.range (B * Q).mulVecLin ≤ LinearMap.range B.mulVecLin := by
    rw [Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  have hMle : LinearMap.range M.mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro x ⟨v, rfl⟩
    rw [hM]
    simp only [Matrix.mulVecLin_apply, Matrix.sub_mulVec]
    apply Submodule.sub_mem
    · exact hAP.trans le_sup_left ⟨v, rfl⟩
    · exact hBQ.trans le_sup_right ⟨v, rfl⟩
  have hMle' : LinearMap.range M.mulVecLin ≤
      LinearMap.range (A * P).mulVecLin ⊔ LinearMap.range (B * Q).mulVecLin := by
    rintro x ⟨v, rfl⟩
    rw [hM]
    simp only [Matrix.mulVecLin_apply, Matrix.sub_mulVec]
    apply Submodule.sub_mem
    · exact (le_sup_left : LinearMap.range (A * P).mulVecLin ≤ _) ⟨v, rfl⟩
    · exact (le_sup_right : LinearMap.range (B * Q).mulVecLin ≤ _) ⟨v, rfl⟩
  have hAle : Module.finrank K (LinearMap.range A.mulVecLin) ≤ Fintype.card C := by
    simpa only [Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_range_le A.mulVecLin
  have hBle : Module.finrank K (LinearMap.range B.mulVecLin) ≤ Fintype.card C := by
    simpa only [Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_range_le B.mulVecLin
  have hsumle := Submodule.finrank_add_le_finrank_add_finrank
    (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
  have hMsum := Submodule.finrank_mono hMle
  have hA : Module.finrank K (LinearMap.range A.mulVecLin) = Fintype.card C := by
    omega
  have hB : Module.finrank K (LinearMap.range B.mulVecLin) = Fintype.card C := by
    omega
  have hsum : Module.finrank K
      ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) =
      2 * Fintype.card C := by
    omega
  have hrange : LinearMap.range M.mulVecLin =
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hMle (by omega)
  have hinter : LinearMap.range A.mulVecLin ⊓ LinearMap.range B.mulVecLin = ⊥ := by
    apply (Submodule.finrank_eq_zero).mp
    have hgrass := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
    omega
  have hAPle : Module.finrank K (LinearMap.range (A * P).mulVecLin) ≤
      Fintype.card C := (Submodule.finrank_mono hAP).trans (by omega)
  have hBQle : Module.finrank K (LinearMap.range (B * Q).mulVecLin) ≤
      Fintype.card C := (Submodule.finrank_mono hBQ).trans (by omega)
  have hprodsumle := Submodule.finrank_add_le_finrank_add_finrank
    (LinearMap.range (A * P).mulVecLin) (LinearMap.range (B * Q).mulVecLin)
  have hMprodsum := Submodule.finrank_mono hMle'
  have hAPdim : Module.finrank K (LinearMap.range (A * P).mulVecLin) =
      Fintype.card C := by
    omega
  have hBQdim : Module.finrank K (LinearMap.range (B * Q).mulVecLin) =
      Fintype.card C := by
    omega
  have hAPrange : LinearMap.range (A * P).mulVecLin = LinearMap.range A.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hAP (by omega)
  have hBQrange : LinearMap.range (B * Q).mulVecLin = LinearMap.range B.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hBQ (by omega)
  have hAinj : Function.Injective A.mulVecLin := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.finrank_eq_zero).mp
    have hnull := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [hA, Module.finrank_fintype_fun_eq_card] at hnull
    omega
  have hBinj : Function.Injective B.mulVecLin := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.finrank_eq_zero).mp
    have hnull := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
    rw [hB, Module.finrank_fintype_fun_eq_card] at hnull
    omega
  have hPsurj : Function.Surjective P.mulVecLin := by
    intro c
    have hc : A.mulVecLin c ∈ LinearMap.range (A * P).mulVecLin := by
      rw [hAPrange]
      exact ⟨c, rfl⟩
    rcases hc with ⟨v, hv⟩
    refine ⟨v, hAinj ?_⟩
    rw [Matrix.mulVecLin_mul] at hv
    exact hv
  have hQsurj : Function.Surjective Q.mulVecLin := by
    intro c
    have hc : B.mulVecLin c ∈ LinearMap.range (B * Q).mulVecLin := by
      rw [hBQrange]
      exact ⟨c, rfl⟩
    rcases hc with ⟨v, hv⟩
    refine ⟨v, hBinj ?_⟩
    rw [Matrix.mulVecLin_mul] at hv
    exact hv
  exact ⟨hA, hB, hrange, hinter, hAPrange, hBQrange, hAinj, hBinj, hPsurj, hQsurj⟩

@[blueprint "lem:recover-subspace-from-three-sums"
  (statement := /-- Let $A,B,C$ be finite-dimensional subspaces of a vector space over a
  field, and let $d$ be a nonnegative integer. If $A$, $A+B$, and $A+C$ have dimensions
  $d$, $2d$, and $2d$, respectively, while $(A+B)+(A+C)$ has dimension $3d$, then
  $A=(A+B)\cap(A+C)$. -/)
  (proof := /-- The inclusion of $A$ in the intersection is immediate. Grassmann's identity
  applied to $A+B$ and $A+C$ shows that their intersection has dimension
  $2d+2d-3d=d$. Equality follows because the included subspace $A$ has the same finite
  dimension. -/)
  (title := /-- Recovering one summand from three direct sums -/)
  (latexEnv := "lemma")]
lemma recover_subspace_from_three_sums {K : Type} [Field K] {V : Type}
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    (A B C : Submodule K V) (d : ℕ)
    (hA : Module.finrank K A = d)
    (hAB : Module.finrank K ↥(A ⊔ B) = 2 * d)
    (hAC : Module.finrank K ↥(A ⊔ C) = 2 * d)
    (hABC : Module.finrank K ↥((A ⊔ B) ⊔ (A ⊔ C)) = 3 * d) :
    A = (A ⊔ B) ⊓ (A ⊔ C) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · exact le_inf le_sup_left le_sup_left
  · have hgrass := Submodule.finrank_sup_add_finrank_inf_eq (A ⊔ B) (A ⊔ C)
    omega

@[blueprint "lem:commuting-block-witness-triple"
  (statement := /-- Let $B_k,B_l,B_m$ satisfy the six dimension equalities
  $(H_{klm})$ with extension excess $d$, and suppose
  $[B_i,B_j]=X_jY_i-X_iY_j$ for the three indices. Then each $X_i$ is injective, each
  $Y_i$ is surjective, the three images of the $X_i$ are pairwise disjoint, and each image
  $\operatorname{im}X_i$ is the intersection of the two commutator images involving $i$.
  -/)
  (proof := /-- Apply \cref{lem:extremal-block-commutator-rank} to each of the three
  commutators. This gives full rank, injectivity, surjectivity, the pairwise direct-sum
  decompositions of the commutator images, and pairwise disjointness. Substitute those
  decompositions into the three $3d$ dimension equalities and apply
  \cref{lem:recover-subspace-from-three-sums} in turn to $X_k,X_l,X_m$. -/)
  (title := /-- Structure forced by one witness triple -/)
  (latexEnv := "lemma")]
lemma commuting_block_witness_triple {K : Type} [Field K] {n s : ℕ}
    {C : Type} [Fintype C] [DecidableEq C]
    (B : Fin s → Matrix (Fin n) (Fin n) K)
    (X : Fin s → Matrix (Fin n) C K) (Y : Fin s → Matrix C (Fin n) K)
    (k l m : Fin s)
    (hcomm : ∀ i j, matrix_commutator (B i) (B j) = X j * Y i - X i * Y j)
    (hdim : commuting_extension_dimension_hypothesis (n + Fintype.card C) B k l m) :
    LinearMap.range (X k).mulVecLin =
        LinearMap.range (matrix_commutator (B k) (B l)).mulVecLin ⊓
          LinearMap.range (matrix_commutator (B k) (B m)).mulVecLin ∧
    LinearMap.range (X l).mulVecLin =
        LinearMap.range (matrix_commutator (B l) (B k)).mulVecLin ⊓
          LinearMap.range (matrix_commutator (B l) (B m)).mulVecLin ∧
    LinearMap.range (X m).mulVecLin =
        LinearMap.range (matrix_commutator (B m) (B k)).mulVecLin ⊓
          LinearMap.range (matrix_commutator (B m) (B l)).mulVecLin ∧
    Function.Injective (X k).mulVecLin ∧ Function.Injective (X l).mulVecLin ∧
    Function.Injective (X m).mulVecLin ∧ Function.Surjective (Y k).mulVecLin ∧
    Function.Surjective (Y l).mulVecLin ∧ Function.Surjective (Y m).mulVecLin ∧
    LinearMap.range (X k).mulVecLin ⊓ LinearMap.range (X l).mulVecLin = ⊥ ∧
    LinearMap.range (X k).mulVecLin ⊓ LinearMap.range (X m).mulVecLin = ⊥ ∧
    LinearMap.range (X l).mulVecLin ⊓ LinearMap.range (X m).mulVecLin = ⊥ := by
  rcases hdim with ⟨hkl, hkm, hlm, hrkl, hrkm, hrlm, hsk, hsl, hsm⟩
  have hcol (M : Matrix (Fin n) (Fin n) K) :
      matrix_column_span M = LinearMap.range M.mulVecLin := by
    rw [Matrix.range_mulVecLin]
    rfl
  have hrkl' : Module.finrank K
      (LinearMap.range (matrix_commutator (B k) (B l)).mulVecLin) =
      2 * Fintype.card C := by
    rw [← hcol]
    simpa using hrkl
  have hrkm' : Module.finrank K
      (LinearMap.range (matrix_commutator (B k) (B m)).mulVecLin) =
      2 * Fintype.card C := by
    rw [← hcol]
    simpa using hrkm
  have hrlm' : Module.finrank K
      (LinearMap.range (matrix_commutator (B l) (B m)).mulVecLin) =
      2 * Fintype.card C := by
    rw [← hcol]
    simpa using hrlm
  have pkl := extremal_block_commutator_rank (X l) (X k) (Y k) (Y l)
    (matrix_commutator (B k) (B l)) (hcomm k l) hrkl'
  have pkm := extremal_block_commutator_rank (X m) (X k) (Y k) (Y m)
    (matrix_commutator (B k) (B m)) (hcomm k m) hrkm'
  have plm := extremal_block_commutator_rank (X m) (X l) (Y l) (Y m)
    (matrix_commutator (B l) (B m)) (hcomm l m) hrlm'
  have hrev (i j : Fin s) :
      LinearMap.range (matrix_commutator (B j) (B i)).mulVecLin =
        LinearMap.range (matrix_commutator (B i) (B j)).mulVecLin := by
    have hm : matrix_commutator (B j) (B i) = -matrix_commutator (B i) (B j) := by
      simp [matrix_commutator]
    rw [hm]
    have hlin : (-matrix_commutator (B i) (B j)).mulVecLin =
        -(matrix_commutator (B i) (B j)).mulVecLin := by
      ext v a
      simp
    rw [hlin, LinearMap.range_neg]
  have hsk' : Module.finrank K
      ↥(LinearMap.range (matrix_commutator (B k) (B l)).mulVecLin ⊔
        LinearMap.range (matrix_commutator (B k) (B m)).mulVecLin) =
      3 * Fintype.card C := by
    rw [← hcol, ← hcol]
    simpa using hsk
  have hsl' : Module.finrank K
      ↥(LinearMap.range (matrix_commutator (B l) (B k)).mulVecLin ⊔
        LinearMap.range (matrix_commutator (B l) (B m)).mulVecLin) =
      3 * Fintype.card C := by
    rw [← hcol, ← hcol]
    simpa using hsl
  have hsm' : Module.finrank K
      ↥(LinearMap.range (matrix_commutator (B m) (B k)).mulVecLin ⊔
        LinearMap.range (matrix_commutator (B m) (B l)).mulVecLin) =
      3 * Fintype.card C := by
    rw [← hcol, ← hcol]
    simpa using hsm
  have pkl' : LinearMap.range (matrix_commutator (B k) (B l)).mulVecLin =
      LinearMap.range (X k).mulVecLin ⊔ LinearMap.range (X l).mulVecLin := by
    simpa [sup_comm] using pkl.2.2.1
  have pkm' : LinearMap.range (matrix_commutator (B k) (B m)).mulVecLin =
      LinearMap.range (X k).mulVecLin ⊔ LinearMap.range (X m).mulVecLin := by
    simpa [sup_comm] using pkm.2.2.1
  have plm' : LinearMap.range (matrix_commutator (B l) (B m)).mulVecLin =
      LinearMap.range (X l).mulVecLin ⊔ LinearMap.range (X m).mulVecLin := by
    simpa [sup_comm] using plm.2.2.1
  have rk := recover_subspace_from_three_sums
    (LinearMap.range (X k).mulVecLin) (LinearMap.range (X l).mulVecLin)
    (LinearMap.range (X m).mulVecLin) (Fintype.card C) pkl.2.1
    (by rw [← pkl']; exact hrkl') (by rw [← pkm']; exact hrkm')
    (by rw [← pkl', ← pkm']; exact hsk')
  have rl := recover_subspace_from_three_sums
    (LinearMap.range (X l).mulVecLin) (LinearMap.range (X k).mulVecLin)
    (LinearMap.range (X m).mulVecLin) (Fintype.card C) pkl.1
    (by rw [← sup_comm, ← pkl']; exact hrkl') (by rw [← plm']; exact hrlm')
    (by
      rw [hrev k l, pkl', plm'] at hsl'
      rw [sup_comm (LinearMap.range (X l).mulVecLin)
        (LinearMap.range (X k).mulVecLin)]
      exact hsl')
  have rm := recover_subspace_from_three_sums
    (LinearMap.range (X m).mulVecLin) (LinearMap.range (X k).mulVecLin)
    (LinearMap.range (X l).mulVecLin) (Fintype.card C) pkm.1
    (by rw [← sup_comm, ← pkm']; exact hrkm')
    (by rw [← sup_comm, ← plm']; exact hrlm')
    (by
      rw [hrev k m, hrev l m, pkm', plm'] at hsm'
      rw [sup_comm (LinearMap.range (X m).mulVecLin)
        (LinearMap.range (X k).mulVecLin),
        sup_comm (LinearMap.range (X m).mulVecLin)
          (LinearMap.range (X l).mulVecLin)]
      exact hsm')
  have rk' : LinearMap.range (X k).mulVecLin =
      LinearMap.range (matrix_commutator (B k) (B l)).mulVecLin ⊓
        LinearMap.range (matrix_commutator (B k) (B m)).mulVecLin := by
    rw [pkl', pkm']
    exact rk
  have rl' : LinearMap.range (X l).mulVecLin =
      LinearMap.range (matrix_commutator (B l) (B k)).mulVecLin ⊓
        LinearMap.range (matrix_commutator (B l) (B m)).mulVecLin := by
    rw [hrev k l, pkl', plm']
    simpa [sup_comm] using rl
  have rm' : LinearMap.range (X m).mulVecLin =
      LinearMap.range (matrix_commutator (B m) (B k)).mulVecLin ⊓
        LinearMap.range (matrix_commutator (B m) (B l)).mulVecLin := by
    rw [hrev k m, hrev l m, pkm', plm']
    simpa [sup_comm] using rm
  exact ⟨rk', rl', rm', pkl.2.2.2.2.2.2.2.1, pkl.2.2.2.2.2.2.1,
    plm.2.2.2.2.2.2.1, pkl.2.2.2.2.2.2.2.2.1, pkl.2.2.2.2.2.2.2.2.2,
    plm.2.2.2.2.2.2.2.2.2, by simpa [inf_comm] using pkl.2.2.2.1,
    by simpa [inf_comm] using pkm.2.2.2.1, by simpa [inf_comm] using plm.2.2.2.1⟩

@[blueprint "lem:injective-matrices-with-equal-range"
  (statement := /-- Let $A,A':E\leftarrow C$ be matrices over a field. If their associated
  linear maps are injective and have the same image, then there is an invertible square
  matrix $S$ on $C$ such that $A'=AS$. -/)
  (proof := /-- Restrict $A'$ to the common image. Both this restriction and the range
  restriction of $A$ are linear equivalences because the two maps are injective and have
  the same range. Their composite gives an automorphism of $K^C$ carrying $A$ to $A'$.
  Taking its matrix yields the required invertible matrix $S$. -/)
  (title := /-- Change of basis between injective maps with common image -/)
  (latexEnv := "lemma")]
lemma injective_matrices_with_equal_range {K : Type} [Field K] {E C : Type}
    [Fintype E] [DecidableEq E] [Fintype C] [DecidableEq C]
    (A A' : Matrix E C K) (hA : Function.Injective A.mulVecLin)
    (hA' : Function.Injective A'.mulVecLin)
    (hrange : LinearMap.range A.mulVecLin = LinearMap.range A'.mulVecLin) :
    ∃ S : Matrix C C K, IsUnit S ∧ A' = A * S := by
  let g : (C → K) →ₗ[K] LinearMap.range A.mulVecLin :=
    A'.mulVecLin.codRestrict (LinearMap.range A.mulVecLin) fun c => by
      rw [hrange]
      exact ⟨c, rfl⟩
  have hg_inj : Function.Injective g := by
    intro x y hxy
    apply hA'
    exact congrArg Subtype.val hxy
  have hg_surj : Function.Surjective g := by
    rintro ⟨z, hz⟩
    rw [hrange] at hz
    rcases hz with ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  let eg : (C → K) ≃ₗ[K] LinearMap.range A.mulVecLin :=
    LinearEquiv.ofBijective g ⟨hg_inj, hg_surj⟩
  let ea : (C → K) ≃ₗ[K] LinearMap.range A.mulVecLin :=
    LinearEquiv.ofInjective A.mulVecLin hA
  let es : (C → K) ≃ₗ[K] C → K := eg.trans ea.symm
  let S : Matrix C C K := LinearMap.toMatrix' es.toLinearMap
  have hunitlin : IsUnit es.toLinearMap := by
    apply isUnit_iff_exists.mpr
    refine ⟨es.symm.toLinearMap, ?_, ?_⟩
    · ext c
      simp
    · ext c
      simp
  have hSunit : IsUnit S := by
    simpa [S] using hunitlin
  have hcomp : A.mulVecLin.comp es.toLinearMap = A'.mulVecLin := by
    apply LinearMap.ext
    intro c
    change A.mulVecLin (ea.symm (eg c)) = A'.mulVecLin c
    have hea : A.mulVecLin (ea.symm (eg c)) = (eg c).1 := by
      change (ea (ea.symm (eg c))).1 = (eg c).1
      rw [ea.apply_symm_apply]
    exact hea.trans rfl
  refine ⟨S, hSunit, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  exact hcomp.symm

@[blueprint "lem:sum-block-commutation-identities"
  (statement := /-- Suppose a family of pairwise commuting block matrices has blocks
  $\left(\begin{smallmatrix}B_i&X_i\\Y_i&D_i\end{smallmatrix}\right)$. Then
  $[B_i,B_j]=X_jY_i-X_iY_j$ and
  $B_iX_j+X_iD_j=B_jX_i+X_jD_i$ for every pair $i,j$. -/)
  (proof := /-- Expand the equality of the two block-matrix products. Equality of their
  upper-left blocks gives the commutator identity after rearrangement, and equality of
  their upper-right blocks gives the second displayed identity directly. -/)
  (title := /-- Upper block identities for commuting matrices -/)
  (latexEnv := "lemma")]
lemma sum_block_commutation_identities {K : Type} [Field K] {n : ℕ} {C I : Type}
    [Fintype C] [DecidableEq C]
    (B : I → Matrix (Fin n) (Fin n) K) (X : I → Matrix (Fin n) C K)
    (Y : I → Matrix C (Fin n) K) (D : I → Matrix C C K)
    (W : I → Matrix (Fin n ⊕ C) (Fin n ⊕ C) K)
    (hdecomp : ∀ i, W i = Matrix.fromBlocks (B i) (X i) (Y i) (D i))
    (hW : ∀ i j, Commute (W i) (W j)) :
    (∀ i j, matrix_commutator (B i) (B j) = X j * Y i - X i * Y j) ∧
      ∀ i j, B i * X j + X i * D j = B j * X i + X j * D i := by
  constructor
  · intro i j
    have hc : W i * W j = W j * W i := hW i j
    rw [hdecomp i, hdecomp j, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply] at hc
    ext a b
    have ht := congrArg (fun M => M (Sum.inl a) (Sum.inl b)) hc
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.add_apply] at ht
    simp only [matrix_commutator, Matrix.sub_apply]
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa [add_comm] using ht
  · intro i j
    have hc : W i * W j = W j * W i := hW i j
    rw [hdecomp i, hdecomp j, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply] at hc
    ext a b
    exact congrArg (fun M => M (Sum.inl a) (Sum.inr b)) hc

@[blueprint "lem:unique-difference-in-disjoint-ranges"
  (statement := /-- Let $A,B,A',B'$ be linear maps into a common vector space. Suppose
  $A-B=A'-B'$, the images of $A$ and $A'$ lie in a subspace $U$, the images of $B$ and
  $B'$ lie in a subspace $V$, and $U\cap V=0$. Then $A=A'$ and $B=B'$. -/)
  (proof := /-- Rearranging the displayed equality gives $A-A'=B-B'$. Applied to any
  vector, the left side lies in $U$ and the right side lies in $V$; disjointness therefore
  makes both sides zero. Thus $A=A'$, and substitution into the original equality gives
  $B=B'$. -/)
  (title := /-- Uniqueness of a difference across disjoint ranges -/)
  (latexEnv := "lemma")]
lemma unique_difference_in_disjoint_ranges {K : Type} [Field K] {E F : Type}
    [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]
    (A B A' B' : Matrix E F K) (U V : Submodule K (E → K))
    (h : A - B = A' - B')
    (hA : LinearMap.range A.mulVecLin ≤ U) (hA' : LinearMap.range A'.mulVecLin ≤ U)
    (hB : LinearMap.range B.mulVecLin ≤ V) (hB' : LinearMap.range B'.mulVecLin ≤ V)
    (hUV : U ⊓ V = ⊥) : A = A' ∧ B = B' := by
  have hdiff : A - A' = B - B' := by
    calc
      A - A' = (A - B) + (B - A') := by abel
      _ = (A' - B') + (B - A') := by rw [h]
      _ = B - B' := by abel
  have hAA : A = A' := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    change A.mulVecLin x = A'.mulVecLin x
    apply sub_eq_zero.mp
    have hu : (A - A').mulVecLin x ∈ U := by
      simp only [Matrix.mulVecLin_apply, Matrix.sub_mulVec]
      exact Submodule.sub_mem U (hA ⟨x, rfl⟩) (hA' ⟨x, rfl⟩)
    have hv : (A - A').mulVecLin x ∈ V := by
      rw [hdiff]
      simp only [Matrix.mulVecLin_apply, Matrix.sub_mulVec]
      exact Submodule.sub_mem V (hB ⟨x, rfl⟩) (hB' ⟨x, rfl⟩)
    have hz : (A - A').mulVecLin x ∈ (⊥ : Submodule K (E → K)) := by
      rw [← hUV]
      exact ⟨hu, hv⟩
    simpa only [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Submodule.mem_bot] using hz
  refine ⟨hAA, ?_⟩
  rw [hAA] at h
  exact sub_right_inj.mp h

@[blueprint "lem:commutator-components-determine-changes"
  (statement := /-- Let $X_i,X_j$ and $X'_i,X'_j$ be injective maps with matching images,
  with the two images disjoint. Suppose $X'_i=X_iS_i$, $X'_j=X_jS_j$, and
  $X_jY_i-X_iY_j=X'_jY'_i-X'_iY'_j$. Then
  $Y_i=S_jY'_i$ and $Y_j=S_iY'_j$. -/)
  (proof := /-- The four product images lie in the two disjoint image spaces of $X_j$ and
  $X_i$. Thus \cref{lem:unique-difference-in-disjoint-ranges} identifies the two product
  components separately. Substitute $X'_j=X_jS_j$ and cancel the injective map $X_j$ to
  obtain $Y_i=S_jY'_i$; the second equality follows identically from $X_i$. -/)
  (title := /-- Comparing the components of a commutator decomposition -/)
  (latexEnv := "lemma")]
lemma commutator_components_determine_changes {K : Type} [Field K] {E C : Type}
    [Fintype E] [DecidableEq E] [Fintype C] [DecidableEq C]
    (Xi Xj Xi' Xj' : Matrix E C K) (Yi Yj Yi' Yj' : Matrix C E K)
    (Si Sj : Matrix C C K)
    (hcomm : Xj * Yi - Xi * Yj = Xj' * Yi' - Xi' * Yj')
    (hri : LinearMap.range Xi.mulVecLin = LinearMap.range Xi'.mulVecLin)
    (hrj : LinearMap.range Xj.mulVecLin = LinearMap.range Xj'.mulVecLin)
    (hdisj : LinearMap.range Xi.mulVecLin ⊓ LinearMap.range Xj.mulVecLin = ⊥)
    (hinji : Function.Injective Xi.mulVecLin) (hinjj : Function.Injective Xj.mulVecLin)
    (hSi : Xi' = Xi * Si) (hSj : Xj' = Xj * Sj) :
    Yi = Sj * Yi' ∧ Yj = Si * Yj' := by
  have hprod (A : Matrix E C K) (P : Matrix C E K) :
      LinearMap.range (A * P).mulVecLin ≤ LinearMap.range A.mulVecLin := by
    rw [Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  have hc := unique_difference_in_disjoint_ranges
    (Xj * Yi) (Xi * Yj) (Xj' * Yi') (Xi' * Yj')
    (LinearMap.range Xj.mulVecLin) (LinearMap.range Xi.mulVecLin) hcomm
    (hprod Xj Yi) (by rw [hrj]; exact hprod Xj' Yi')
    (hprod Xi Yj) (by rw [hri]; exact hprod Xi' Yj')
    (by simpa [inf_comm] using hdisj)
  constructor
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    change Yi.mulVecLin v = (Sj * Yi').mulVecLin v
    apply hinjj
    have hp := congrArg (fun M => M.mulVecLin v) hc.1
    rw [hSj] at hp
    simpa only [Matrix.mulVecLin_mul, LinearMap.comp_apply] using hp
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    change Yj.mulVecLin v = (Si * Yj').mulVecLin v
    apply hinji
    have hp := congrArg (fun M => M.mulVecLin v) hc.2
    rw [hSi] at hp
    simpa only [Matrix.mulVecLin_mul, LinearMap.comp_apply] using hp

@[blueprint "lem:commuting-extension-sum-block-rigidity"
  (statement := /-- Let $K$ be a field, let $q\geq2$, let $C$ be a finite coordinate set,
  and let $B=(B_0,\ldots,B_q)$ be $n\times n$ matrices satisfying the commuting-extension
  dimension hypotheses with extension size $n+|C|$. If two pairwise commuting families of
  matrices on $K^n\oplus K^C$ have common upper-left blocks $B_i$, then they are
  simultaneously conjugate by a block diagonal matrix $I_n\oplus S$ with $S$ invertible. -/)
  (proof := /-- Use \cref{lem:sum-block-commutation-identities} to extract the upper-left
  and upper-right block equations. For each witness triple,
  \cref{lem:commuting-block-witness-triple} identifies the images of the $X$-blocks from
  the fixed commutators, proves that the $X$-blocks are injective, and proves that the
  $Y$-blocks are surjective. Hence \cref{lem:injective-matrices-with-equal-range} supplies
  invertible matrices $S_i$ satisfying $X'_i=X_iS_i$. Applying
  \cref{lem:commutator-components-determine-changes} to the three pairs in a witness
  triple and using surjectivity of the primed $Y$-blocks gives $S_0=S_l=S_m$; all witness
  triples therefore yield one matrix $S$ with $X'_i=X_iS$ and $Y_i=SY'_i$ for every $i$.
  Subtract the primed and unprimed upper-right block equations. The resulting two sides
  lie in disjoint $X$-images, so \cref{lem:unique-difference-in-disjoint-ranges} and
  injectivity give $SD'_i=D_iS$. Block multiplication then yields simultaneous conjugacy
  by $I_n\oplus S$. -/)
  (title := /-- Rigidity in prescribed sum coordinates -/)
  (latexEnv := "lemma")]
lemma commuting_extension_sum_block_rigidity {K : Type} [Field K] {n q : ℕ}
    {C : Type} [Fintype C] [DecidableEq C]
    (B : Fin (q + 1) → Matrix (Fin n) (Fin n) K)
    (hq : 2 ≤ q)
    (hB : commuting_extension_uniqueness_hypothesis (n + Fintype.card C) B)
    (W W' : Fin (q + 1) → Matrix (Fin n ⊕ C) (Fin n ⊕ C) K)
    (hW : ∀ k l, Commute (W k) (W l)) (hW' : ∀ k l, Commute (W' k) (W' l))
    (hblock : ∀ k i j, W k (Sum.inl i) (Sum.inl j) = B k i j)
    (hblock' : ∀ k i j, W' k (Sum.inl i) (Sum.inl j) = B k i j) :
    ∃ S : Matrix C C K, IsUnit S ∧ ∀ k,
      W' k = Matrix.fromBlocks 1 0 0 S⁻¹ * W k * Matrix.fromBlocks 1 0 0 S := by
  let X : Fin (q + 1) → Matrix (Fin n) C K :=
    fun k i c => W k (Sum.inl i) (Sum.inr c)
  let Y : Fin (q + 1) → Matrix C (Fin n) K :=
    fun k c i => W k (Sum.inr c) (Sum.inl i)
  let D : Fin (q + 1) → Matrix C C K :=
    fun k c d => W k (Sum.inr c) (Sum.inr d)
  let X' : Fin (q + 1) → Matrix (Fin n) C K :=
    fun k i c => W' k (Sum.inl i) (Sum.inr c)
  let Y' : Fin (q + 1) → Matrix C (Fin n) K :=
    fun k c i => W' k (Sum.inr c) (Sum.inl i)
  let D' : Fin (q + 1) → Matrix C C K :=
    fun k c d => W' k (Sum.inr c) (Sum.inr d)
  have hdecomp (k : Fin (q + 1)) :
      W k = Matrix.fromBlocks (B k) (X k) (Y k) (D k) := by
    ext a b
    rcases a with i | c <;> rcases b with j | d
    · exact hblock k i j
    · rfl
    · rfl
    · rfl
  have hdecomp' (k : Fin (q + 1)) :
      W' k = Matrix.fromBlocks (B k) (X' k) (Y' k) (D' k) := by
    ext a b
    rcases a with i | c <;> rcases b with j | d
    · exact hblock' k i j
    · rfl
    · rfl
    · rfl
  have hids := sum_block_commutation_identities B X Y D W hdecomp hW
  have hids' := sum_block_commutation_identities B X' Y' D' W' hdecomp' hW'
  have hcomm := hids.1
  have hcomm' := hids'.1
  have hupper := hids.2
  have hupper' := hids'.2
  have hglobal (i : Fin (q + 1)) :
      LinearMap.range (X i).mulVecLin = LinearMap.range (X' i).mulVecLin ∧
      Function.Injective (X i).mulVecLin ∧ Function.Injective (X' i).mulVecLin ∧
      Function.Surjective (Y i).mulVecLin ∧ Function.Surjective (Y' i).mulVecLin := by
    by_cases hi : i = 0
    · subst i
      let l : Fin (q + 1) := ⟨1, by omega⟩
      have hl : l ≠ 0 := by simp [l]
      rcases hB l hl with ⟨m, hm0, hml, hdim⟩
      rcases commuting_block_witness_triple B X Y 0 l m hcomm hdim with
        ⟨r0, rl, rm, ix0, ixl, ixm, sy0, syl, sym, d0l, d0m, dlm⟩
      rcases commuting_block_witness_triple B X' Y' 0 l m hcomm' hdim with
        ⟨r0', rl', rm', ix0', ixl', ixm', sy0', syl', sym', d0l', d0m', dlm'⟩
      exact ⟨r0.trans r0'.symm, ix0, ix0', sy0, sy0'⟩
    · rcases hB i hi with ⟨m, hm0, hmi, hdim⟩
      rcases commuting_block_witness_triple B X Y 0 i m hcomm hdim with
        ⟨r0, ri, rm, ix0, ixi, ixm, sy0, syi, sym, d0i, d0m, dim⟩
      rcases commuting_block_witness_triple B X' Y' 0 i m hcomm' hdim with
        ⟨r0', ri', rm', ix0', ixi', ixm', sy0', syi', sym', d0i', d0m', dim'⟩
      exact ⟨ri.trans ri'.symm, ixi, ixi', syi, syi'⟩
  let Sch (i : Fin (q + 1)) := injective_matrices_with_equal_range
    (X i) (X' i) (hglobal i).2.1 (hglobal i).2.2.1 (hglobal i).1
  let S (i : Fin (q + 1)) : Matrix C C K := Classical.choose (Sch i)
  have hSunit (i : Fin (q + 1)) : IsUnit (S i) :=
    (Classical.choose_spec (Sch i)).1
  have hSX (i : Fin (q + 1)) : X' i = X i * S i :=
    (Classical.choose_spec (Sch i)).2
  have cancel_right {A A' : Matrix C C K} {P : Matrix C (Fin n) K}
      (hP : Function.Surjective P.mulVecLin) (h : A * P = A' * P) : A = A' := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro c
    rcases hP c with ⟨v, rfl⟩
    change A.mulVecLin (P.mulVecLin v) = A'.mulVecLin (P.mulVecLin v)
    have hv := congrArg (fun M => M.mulVecLin v) h
    simpa only [Matrix.mulVecLin_mul, LinearMap.comp_apply] using hv
  have hSall (i : Fin (q + 1)) : S i = S 0 := by
    by_cases hi : i = 0
    · subst i
      rfl
    · rcases hB i hi with ⟨m, hm0, hmi, hdim⟩
      rcases commuting_block_witness_triple B X Y 0 i m hcomm hdim with
        ⟨r0, ri, rm, ix0, ixi, ixm, sy0, syi, sym, d0i, d0m, dim⟩
      rcases commuting_block_witness_triple B X' Y' 0 i m hcomm' hdim with
        ⟨r0', ri', rm', ix0', ixi', ixm', sy0', syi', sym', d0i', d0m', dim'⟩
      have c0i := commutator_components_determine_changes
        (X 0) (X i) (X' 0) (X' i) (Y 0) (Y i) (Y' 0) (Y' i)
        (S 0) (S i) ((hcomm 0 i).symm.trans (hcomm' 0 i))
        (hglobal 0).1 (hglobal i).1 d0i (hglobal 0).2.1 (hglobal i).2.1
        (hSX 0) (hSX i)
      have c0m := commutator_components_determine_changes
        (X 0) (X m) (X' 0) (X' m) (Y 0) (Y m) (Y' 0) (Y' m)
        (S 0) (S m) ((hcomm 0 m).symm.trans (hcomm' 0 m))
        (hglobal 0).1 (hglobal m).1 d0m (hglobal 0).2.1 (hglobal m).2.1
        (hSX 0) (hSX m)
      have cim := commutator_components_determine_changes
        (X i) (X m) (X' i) (X' m) (Y i) (Y m) (Y' i) (Y' m)
        (S i) (S m) ((hcomm i m).symm.trans (hcomm' i m))
        (hglobal i).1 (hglobal m).1 dim (hglobal i).2.1 (hglobal m).2.1
        (hSX i) (hSX m)
      have h0m : S 0 = S m := cancel_right syi' (c0i.2.symm.trans cim.1)
      have hmi : S m = S i := cancel_right sy0' (c0m.1.symm.trans c0i.1)
      exact hmi.symm.trans h0m.symm
  have hXall (i : Fin (q + 1)) : X' i = X i * S 0 := by
    rw [hSX i, hSall i]
  have hYall (i : Fin (q + 1)) : Y i = S 0 * Y' i := by
    by_cases hi : i = 0
    · subst i
      let l : Fin (q + 1) := ⟨1, by omega⟩
      have hl : l ≠ 0 := by simp [l]
      rcases hB l hl with ⟨m, hm0, hml, hdim⟩
      rcases commuting_block_witness_triple B X Y 0 l m hcomm hdim with
        ⟨r0, rl, rm, ix0, ixl, ixm, sy0, syl, sym, d0l, d0m, dlm⟩
      have c0l := commutator_components_determine_changes
        (X 0) (X l) (X' 0) (X' l) (Y 0) (Y l) (Y' 0) (Y' l)
        (S 0) (S l) ((hcomm 0 l).symm.trans (hcomm' 0 l))
        (hglobal 0).1 (hglobal l).1 d0l (hglobal 0).2.1 (hglobal l).2.1
        (hSX 0) (hSX l)
      rw [hSall l] at c0l
      exact c0l.1
    · rcases hB i hi with ⟨m, hm0, hmi, hdim⟩
      rcases commuting_block_witness_triple B X Y 0 i m hcomm hdim with
        ⟨r0, ri, rm, ix0, ixi, ixm, sy0, syi, sym, d0i, d0m, dim⟩
      have c0i := commutator_components_determine_changes
        (X 0) (X i) (X' 0) (X' i) (Y 0) (Y i) (Y' 0) (Y' i)
        (S 0) (S i) ((hcomm 0 i).symm.trans (hcomm' 0 i))
        (hglobal 0).1 (hglobal i).1 d0i (hglobal 0).2.1 (hglobal i).2.1
        (hSX 0) (hSX i)
      exact c0i.2
  have hDpair (i j : Fin (q + 1))
      (hdisj : LinearMap.range (X i).mulVecLin ⊓
        LinearMap.range (X j).mulVecLin = ⊥) :
      S 0 * D' i = D i * S 0 ∧ S 0 * D' j = D j * S 0 := by
    have hp := hupper' i j
    rw [hXall i, hXall j] at hp
    have hu := congrArg (fun M => M * S 0) (hupper i j)
    simp only [Matrix.add_mul] at hu
    have hp' : B i * (X j * S 0) + X i * (S 0 * D' j) =
        B j * (X i * S 0) + X j * (S 0 * D' i) := by
      simpa only [Matrix.mul_assoc] using hp
    have hu' : B i * (X j * S 0) + X i * (D j * S 0) =
        B j * (X i * S 0) + X j * (D i * S 0) := by
      simpa only [Matrix.mul_assoc] using hu
    have heq : X i * (S 0 * D' j - D j * S 0) =
        X j * (S 0 * D' i - D i * S 0) := by
      calc
        X i * (S 0 * D' j - D j * S 0) =
            (B i * (X j * S 0) + X i * (S 0 * D' j)) -
              (B i * (X j * S 0) + X i * (D j * S 0)) := by
                simp only [Matrix.mul_sub, Matrix.mul_assoc]
                abel
        _ = (B j * (X i * S 0) + X j * (S 0 * D' i)) -
              (B j * (X i * S 0) + X j * (D i * S 0)) := by rw [hp', hu']
        _ = X j * (S 0 * D' i - D i * S 0) := by
                simp only [Matrix.mul_sub, Matrix.mul_assoc]
                abel
    have hprod (A : Matrix (Fin n) C K) (P : Matrix C C K) :
        LinearMap.range (A * P).mulVecLin ≤ LinearMap.range A.mulVecLin := by
      rw [Matrix.mulVecLin_mul]
      exact LinearMap.range_comp_le_range _ _
    have hz := unique_difference_in_disjoint_ranges
      (X i * (S 0 * D' j - D j * S 0))
      (X j * (S 0 * D' i - D i * S 0)) 0 0
      (LinearMap.range (X i).mulVecLin) (LinearMap.range (X j).mulVecLin)
      (by rw [heq]; simp) (hprod _ _) (by simp) (hprod _ _) (by simp) hdisj
    have cancel_left_zero {A : Matrix (Fin n) C K} {P : Matrix C C K}
        (hA : Function.Injective A.mulVecLin) (h : A * P = 0) : P = 0 := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro c
      apply hA
      have hc := congrArg (fun M => M.mulVecLin c) h
      simpa only [Matrix.toLin'_apply', Matrix.mulVecLin_mul, LinearMap.comp_apply,
        Matrix.mulVecLin_zero, LinearMap.zero_apply, map_zero] using hc
    have hi : S 0 * D' i - D i * S 0 = 0 :=
      cancel_left_zero (hglobal j).2.1 hz.2
    have hj : S 0 * D' j - D j * S 0 = 0 :=
      cancel_left_zero (hglobal i).2.1 hz.1
    exact ⟨sub_eq_zero.mp hi, sub_eq_zero.mp hj⟩
  have hDall (i : Fin (q + 1)) : S 0 * D' i = D i * S 0 := by
    by_cases hi : i = 0
    · subst i
      let l : Fin (q + 1) := ⟨1, by omega⟩
      have hl : l ≠ 0 := by simp [l]
      rcases hB l hl with ⟨m, hm0, hml, hdim⟩
      rcases commuting_block_witness_triple B X Y 0 l m hcomm hdim with
        ⟨r0, rl, rm, ix0, ixl, ixm, sy0, syl, sym, d0l, d0m, dlm⟩
      exact (hDpair 0 l d0l).1
    · rcases hB i hi with ⟨m, hm0, hmi, hdim⟩
      rcases commuting_block_witness_triple B X Y 0 i m hcomm hdim with
        ⟨r0, ri, rm, ix0, ixi, ixm, sy0, syi, sym, d0i, d0m, dim⟩
      exact (hDpair 0 i d0i).2
  let P : Matrix (Fin n ⊕ C) (Fin n ⊕ C) K := Matrix.fromBlocks 1 0 0 (S 0)
  have hintertwine (k : Fin (q + 1)) : W k * P = P * W' k := by
    rw [hdecomp k, hdecomp' k]
    simp only [P, Matrix.fromBlocks_multiply]
    ext a b
    rcases a with i | c <;> rcases b with j | d
    · simp
    · simpa using congrArg (fun M => M i d) (hXall k).symm
    · simpa using congrArg (fun M => M c j) (hYall k)
    · simpa using congrArg (fun M => M c d) (hDall k).symm
  refine ⟨S 0, hSunit 0, ?_⟩
  intro k
  let Q : Matrix (Fin n ⊕ C) (Fin n ⊕ C) K :=
    Matrix.fromBlocks 1 0 0 (S 0)⁻¹
  have hSdet : IsUnit (S 0).det :=
    (Matrix.isUnit_iff_isUnit_det (S 0)).mp (hSunit 0)
  have hQP : Q * P = 1 := by
    simp [Q, P, Matrix.fromBlocks_multiply, Matrix.nonsing_inv_mul (S 0) hSdet]
  change W' k = Q * W k * P
  calc
    W' k = 1 * W' k := by simp
    _ = (Q * P) * W' k := by rw [hQP]
    _ = Q * (P * W' k) := by rw [Matrix.mul_assoc]
    _ = Q * (W k * P) := by rw [hintertwine k]
    _ = Q * W k * P := by rw [Matrix.mul_assoc]

@[blueprint "lem:commuting-extension-block-rigidity"
  (statement := /-- Let $K$ be a field, let $n,q,r$ be nonnegative integers with
  $q\geq2$, and let $B=(B_0,\ldots,B_q)$ be $n\times n$ matrices satisfying the
  quantified hypotheses $H_{0lm}$ with parameter $r$. Fix a coordinate embedding
  $\iota:\operatorname{Fin}(n)\hookrightarrow\operatorname{Fin}(r)$. Any two size-$r$
  commuting extensions of $B$ along $\iota$ are simultaneously conjugate by an invertible
  matrix of the form $I_n\oplus S$ relative to the prescribed coordinates and their
  coordinate complement. -/)
  (proof := /-- Let $C$ be the finite set of coordinates outside the range of $\iota$.
  The equivalence
  $\operatorname{Fin}(n)\sqcup C\simeq\operatorname{Fin}(r)$ induced by $\iota$ gives
  $n+|C|=r$. Reindex both commuting extensions along this equivalence. Their upper-left
  blocks remain $B_i$, so the dimension hypothesis has the form required by
  \cref{lem:commuting-extension-sum-block-rigidity}. That lemma supplies an invertible
  matrix $S$ on $K^C$ and simultaneous conjugacy by $I_n\oplus S$ in the reindexed
  coordinates. Reindex this block diagonal matrix back to $K^r$. Its rows and columns on
  the range of $\iota$ are those of the identity, so it satisfies
  \cref{def:coordinate-block-preserving}; transporting the conjugacy equation shows that
  it witnesses \cref{def:commuting-extension-equivalent}. -/)
  (title := /-- Rigidity of the prescribed block in commuting extensions -/)
  (latexEnv := "lemma")]
lemma commuting_extension_block_rigidity {K : Type} [Field K] {n q r : ℕ}
    (B : Fin (q + 1) → Matrix (Fin n) (Fin n) K)
    (hq : 2 ≤ q)
    (hB : commuting_extension_uniqueness_hypothesis r B)
    (ι : Fin n ↪ Fin r) (Z Z' : Fin (q + 1) → Matrix (Fin r) (Fin r) K)
    (hZ : commuting_extension B Z ι) (hZ' : commuting_extension B Z' ι) :
    commuting_extension_equivalent ι Z Z' := by
  classical
  let C := {j : Fin r // j ∉ Set.range ι}
  let er : Fin n ≃ Set.range ι := ι.toEquivRange
  let e : Fin n ⊕ C ≃ Fin r :=
    (Equiv.sumCongr er (Equiv.refl C)).trans
      (Equiv.sumCompl (fun j : Fin r => j ∈ Set.range ι))
  have heinl (i : Fin n) : e (Sum.inl i) = ι i := by
    rfl
  have heinr (c : C) : e (Sum.inr c) = c.1 := by
    rfl
  have hcard : n + Fintype.card C = r := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr e
  have hBc : commuting_extension_uniqueness_hypothesis (n + Fintype.card C) B := by
    rw [hcard]
    exact hB
  let W : Fin (q + 1) → Matrix (Fin n ⊕ C) (Fin n ⊕ C) K :=
    fun k => Matrix.reindexAlgEquiv K K e.symm (Z k)
  let W' : Fin (q + 1) → Matrix (Fin n ⊕ C) (Fin n ⊕ C) K :=
    fun k => Matrix.reindexAlgEquiv K K e.symm (Z' k)
  have hW (k l : Fin (q + 1)) : Commute (W k) (W l) := by
    simpa [W] using (hZ.1 k l).map (Matrix.reindexAlgEquiv K K e.symm)
  have hW' (k l : Fin (q + 1)) : Commute (W' k) (W' l) := by
    simpa [W'] using (hZ'.1 k l).map (Matrix.reindexAlgEquiv K K e.symm)
  have hblock (k : Fin (q + 1)) (i j : Fin n) :
      W k (Sum.inl i) (Sum.inl j) = B k i j := by
    simpa [W, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, heinl] using hZ.2 k i j
  have hblock' (k : Fin (q + 1)) (i j : Fin n) :
      W' k (Sum.inl i) (Sum.inl j) = B k i j := by
    simpa [W', Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, heinl] using hZ'.2 k i j
  rcases commuting_extension_sum_block_rigidity B hq hBc W W' hW hW' hblock hblock' with
    ⟨S, hSunit, hconj⟩
  let Ps : Matrix (Fin n ⊕ C) (Fin n ⊕ C) K := Matrix.fromBlocks 1 0 0 S
  let Qs : Matrix (Fin n ⊕ C) (Fin n ⊕ C) K := Matrix.fromBlocks 1 0 0 S⁻¹
  let P : Matrix (Fin r) (Fin r) K := Matrix.reindexAlgEquiv K K e Ps
  let Q : Matrix (Fin r) (Fin r) K := Matrix.reindexAlgEquiv K K e Qs
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSunit
  have hQsPs : Qs * Ps = 1 := by
    simp [Qs, Ps, Matrix.fromBlocks_multiply, Matrix.nonsing_inv_mul S hSdet]
  have hPsQs : Ps * Qs = 1 := by
    simp [Qs, Ps, Matrix.fromBlocks_multiply, Matrix.mul_nonsing_inv S hSdet]
  have hQP : Q * P = 1 := by
    simpa [Q, P] using congrArg (Matrix.reindexAlgEquiv K K e) hQsPs
  have hPQ : P * Q = 1 := by
    simpa [Q, P] using congrArg (Matrix.reindexAlgEquiv K K e) hPsQs
  have hPunit : IsUnit P := isUnit_iff_exists.mpr ⟨Q, hPQ, hQP⟩
  have hpreserve : coordinate_block_preserving ι P := by
    constructor
    · intro i j
      have hi : e.symm (ι i) = Sum.inl i := by
        apply e.injective
        simp [heinl]
      change Ps (e.symm (ι i)) (e.symm j) = if ι i = j then 1 else 0
      rw [hi]
      rcases hj : e.symm j with a | c
      · have hje : j = ι a := by
          calc
            j = e (e.symm j) := (e.apply_symm_apply j).symm
            _ = ι a := by rw [hj, heinl]
        simp [Ps, hj, hje, Matrix.one_apply]
      · have hje : j = c.1 := by
          calc
            j = e (e.symm j) := (e.apply_symm_apply j).symm
            _ = c.1 := by rw [hj, heinr]
        have hne : ι i ≠ j := by
          rw [hje]
          exact fun h => c.2 ⟨i, h⟩
        simp [Ps, hj, hne]
    · intro i j
      have hi : e.symm (ι i) = Sum.inl i := by
        apply e.injective
        simp [heinl]
      change Ps (e.symm j) (e.symm (ι i)) = if j = ι i then 1 else 0
      rw [hi]
      rcases hj : e.symm j with a | c
      · have hje : j = ι a := by
          calc
            j = e (e.symm j) := (e.apply_symm_apply j).symm
            _ = ι a := by rw [hj, heinl]
        simp [Ps, hj, hje, Matrix.one_apply]
      · have hje : j = c.1 := by
          calc
            j = e (e.symm j) := (e.apply_symm_apply j).symm
            _ = c.1 := by rw [hj, heinr]
        have hne : j ≠ ι i := by
          rw [hje]
          exact fun h => c.2 ⟨i, h.symm⟩
        simp [Ps, hj, hne]
  have hQinv : Q = P⁻¹ := by
    have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPunit
    calc
      Q = Q * 1 := by simp
      _ = Q * (P * P⁻¹) := by rw [Matrix.mul_nonsing_inv P hPdet]
      _ = (Q * P) * P⁻¹ := by rw [Matrix.mul_assoc]
      _ = P⁻¹ := by rw [hQP]; simp
  refine ⟨P, hPunit, hpreserve, ?_⟩
  intro k
  have hc := congrArg (Matrix.reindexAlgEquiv K K e) (hconj k)
  rw [map_mul, map_mul] at hc
  rw [← hQinv]
  simpa [W, W', P, Q, Ps, Qs] using hc

@[blueprint "lem:commuting-extension-uniqueness"
  (statement := /-- Let $K$ be a field, let $n,q,r$ be nonnegative integers with
  $q\geq2$, and let $B=(B_0,\ldots,B_q)$ be $n\times n$ matrices. Suppose that, for every
  nonzero $l\in\operatorname{Fin}(q+1)$, there is an
  $m\in\operatorname{Fin}(q+1)$ with $m\neq0$ and $m\neq l$ such that $H_{0lm}$ holds
  with parameter $r$. Then, for every coordinate embedding
  $\iota:\operatorname{Fin}(n)\hookrightarrow\operatorname{Fin}(r)$ and every two size-$r$
  commuting extensions $Z,Z'$ of $B$ along $\iota$, there is one invertible matrix $P$
  preserving the prescribed coordinate block such that
  $Z'_k=P^{-1}Z_kP$ for every $k\in\operatorname{Fin}(q+1)$. -/)
  (proof := /-- Fix a coordinate embedding $\iota$ and two commuting extensions $Z,Z'$ of
  $B$ along $\iota$. The hypotheses of
  \cref{lem:commuting-extension-block-rigidity} give their equivalence along $\iota$.
  Since $\iota,Z,Z'$ were arbitrary, this is precisely essential uniqueness in the sense
  of \cref{def:essentially-unique-commuting-extension}. -/)
  (title := /-- Uniqueness theorem for commuting extensions -/)
  (latexEnv := "lemma")]
lemma commuting_extension_uniqueness {K : Type} [Field K] {n q r : ℕ}
    (B : Fin (q + 1) → Matrix (Fin n) (Fin n) K)
    (hq : 2 ≤ q)
    (hB : commuting_extension_uniqueness_hypothesis r B) :
    essentially_unique_commuting_extension r B := by
  intro ι Z Z' hZ hZ'
  exact commuting_extension_block_rigidity B hq hB ι Z Z' hZ hZ'

@[blueprint "def:decomposition-attached-commuting-extension"
  (statement := /-- Let
  $T=\sum_{a=1}^r u_a\otimes v_a\otimes w_a$ be an
  $n\times n\times(q+2)$ tensor, let
  $A=\sum_k\lambda_kT_k$ be invertible, and suppose that every
  $\alpha_a=\sum_k\lambda_k(w_a)_k$ is nonzero. A commuting extension $Z$ of the
  normalized nonfirst slices is attached to this decomposition along
  $\iota:\operatorname{Fin}(n)\hookrightarrow\operatorname{Fin}(r)$ if there are
  invertible $r\times r$ matrices $X,Y$ with $X^{\mathsf T}Y=I_r$ such that the
  prescribed columns of $Y$ are the vectors $v_a$, the prescribed columns of $X$ are
  $\alpha_a u_aA^{-\mathsf T}$, and
  \[
    Z_j=X^{\mathsf T}\operatorname{diag}
      \left(\frac{(w_a)_{j+2}}{\alpha_a}\right)_{a=1}^rY
  \]
  for every normalized-slice index $j$. -/)
  (title := /-- Commuting extensions attached to tensor decompositions -/)
  (latexEnv := "definition")]
noncomputable def decomposition_attached_commuting_extension {K : Type} [Field K]
    {n q r : ℕ} (A : Matrix (Fin n) (Fin n) K) (c : Fin (q + 2) → K)
    (T : order_three_tensor K n (q + 2))
    (u v : Fin r → Fin n → K) (w : Fin r → Fin (q + 2) → K)
    (Z : Fin (q + 1) → Matrix (Fin r) (Fin r) K) (ι : Fin n ↪ Fin r) : Prop :=
  tensor_decomposition T u v w ∧
  A = ∑ k, c k • tensor_slice T k ∧
  IsUnit A ∧
  (∀ a, (∑ k, c k * w a k) ≠ 0) ∧
  commuting_extension (normalized_nonfirst_slices A T) Z ι ∧
  ∃ X Y : Matrix (Fin r) (Fin r) K,
    IsUnit X ∧ IsUnit Y ∧ X.transpose * Y = 1 ∧
    (∀ a i, Y a (ι i) = v a i) ∧
    (∀ a i,
      X a (ι i) =
        (∑ k, c k * w a k) * ∑ j, u a j * (A⁻¹) i j) ∧
    ∀ k,
      Z k =
        X.transpose *
          Matrix.diagonal (fun a => w a k.succ / ∑ t, c t * w a t) * Y

@[blueprint "lem:polynomial-matrix-rank-lower-bound-persists"
  (statement := /-- Let $K$ be a field and let $P(t)$ be a square matrix whose
  entries are polynomials over $K$. There is a polynomial $f$ with $f(0)\ne0$ such that,
  whenever $f(t)\ne0$, the rank of $P(t)$ is at least the rank of $P(0)$. -/)
  (proof := /-- Put $P(0)$ into rank normal form by invertible row and column operations.
  Apply the same constant operations to $P(t)$, and let $f(t)$ be the determinant of the
  square block which is the identity block at $t=0$. Thus $f(0)=1$. If $f(t)\ne0$, that
  block has full rank. The rank of a submatrix is at most that of the whole transformed
  matrix, and multiplication on either side cannot increase rank, so
  $\operatorname{rank}P(0)\leq\operatorname{rank}P(t)$. -/)
  (title := /-- Polynomial specialization preserves a rank lower bound generically -/)
  (latexEnv := "lemma")]
lemma polynomial_matrix_rank_lower_bound_persists
    {K : Type} [Field K] {n : ℕ}
    (P : Matrix (Fin n) (Fin n) (Polynomial K)) :
    ∃ f : Polynomial K, Polynomial.eval 0 f ≠ 0 ∧
      ∀ t : K, Polynomial.eval t f ≠ 0 →
        (P.map (Polynomial.evalRingHom 0 : Polynomial K →+* K)).rank ≤
          (P.map (Polynomial.evalRingHom t : Polynomial K →+* K)).rank := by
  classical
  let P0 : Matrix (Fin n) (Fin n) K :=
    P.map (Polynomial.evalRingHom 0 : Polynomial K →+* K)
  obtain ⟨V, U, e, hV, hU, hnormal⟩ := Matrix.exists_rank_normal_form P0
  let Q : Matrix (Fin n) (Fin n) (Polynomial K) :=
    V.map Polynomial.C * P * U.map Polynomial.C
  let emb : Fin P0.rank → Fin n := fun i => e.symm (Sum.inl i)
  let f : Polynomial K := (Q.submatrix emb emb).det
  refine ⟨f, ?_, ?_⟩
  · change (Polynomial.evalRingHom 0) (Q.submatrix emb emb).det ≠ 0
    rw [RingHom.map_det]
    change ((Q.map (Polynomial.evalRingHom 0 : Polynomial K →+* K)).submatrix emb emb).det ≠
      0
    have hQ0 :
        Q.map (Polynomial.evalRingHom 0 : Polynomial K →+* K) = V * P0 * U := by
      ext i j
      simp [Q, P0, Matrix.mul_apply, Polynomial.eval_finset_sum, Polynomial.eval_mul]
    rw [hQ0]
    rw [hnormal]
    have hcanon :
        ((Matrix.fromBlocks 1 0 0 0).submatrix e e).submatrix emb emb =
          (1 : Matrix (Fin P0.rank) (Fin P0.rank) K) := by
      ext i j
      simp [emb, Matrix.one_apply]
    rw [hcanon]
    simp
  · intro t hft
    have hdet :
        ((Q.map (Polynomial.evalRingHom t : Polynomial K →+* K)).submatrix emb emb).det ≠
          0 := by
      change (Polynomial.evalRingHom t) (Q.submatrix emb emb).det ≠ 0 at hft
      rw [RingHom.map_det] at hft
      exact hft
    have hblock :
        ((Q.map (Polynomial.evalRingHom t : Polynomial K →+* K)).submatrix emb emb).rank =
          P0.rank := by
      have hu :
          IsUnit
            ((Q.map (Polynomial.evalRingHom t : Polynomial K →+* K)).submatrix emb emb) :=
        (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.mpr hdet)
      simpa using Matrix.rank_of_isUnit _ hu
    calc
      P0.rank =
          ((Q.map (Polynomial.evalRingHom t : Polynomial K →+* K)).submatrix emb emb).rank :=
        hblock.symm
      _ ≤ (Q.map (Polynomial.evalRingHom t : Polynomial K →+* K)).rank :=
        Matrix.rank_submatrix_le _ _ _
      _ ≤ (P.map (Polynomial.evalRingHom t : Polynomial K →+* K)).rank := by
        have hQt :
            Q.map (Polynomial.evalRingHom t : Polynomial K →+* K) =
              V * P.map (Polynomial.evalRingHom t : Polynomial K →+* K) * U := by
          ext i j
          simp [Q, Matrix.mul_apply, Polynomial.eval_finset_sum, Polynomial.eval_mul]
        rw [hQt]
        exact le_trans
          (Matrix.rank_mul_le_left
            (V * P.map (Polynomial.evalRingHom t : Polynomial K →+* K)) U)
          (Matrix.rank_mul_le_right V
            (P.map (Polynomial.evalRingHom t : Polynomial K →+* K)))

@[blueprint "lem:polynomial-matrix-column-sum-dimension-persists"
  (statement := /-- Let $P(t)$ and $Q(t)$ be square polynomial matrices over a
  field. There is a polynomial $f$ with $f(0)\ne0$ such that, whenever $f(t)\ne0$, the
  dimension of the sum of the column spaces of $P(t)$ and $Q(t)$ is at least its dimension
  at $t=0$. -/)
  (proof := /-- Choose a projection of the ambient coordinate space onto the sum of the
  two column spaces at $t=0$. Express each column of its matrix as a sum of a linear
  combination of columns of $P(0)$ and one of columns of $Q(0)$. Keeping these coefficient
  matrices constant produces a square polynomial matrix $W(t)$ whose column space is the
  required sum at zero and is contained in the corresponding sum at every $t$. Apply
  \cref{lem:polynomial-matrix-rank-lower-bound-persists} to $W(t)$ and compare ranks with
  column-space dimensions. -/)
  (title := /-- Polynomial specialization preserves column-space sums generically -/)
  (latexEnv := "lemma")]
lemma polynomial_matrix_column_sum_dimension_persists
    {K : Type} [Field K] {n : ℕ}
    (P Q : Matrix (Fin n) (Fin n) (Polynomial K)) :
    ∃ f : Polynomial K, Polynomial.eval 0 f ≠ 0 ∧
      ∀ t : K, Polynomial.eval t f ≠ 0 →
        Module.finrank K
            ↥(matrix_column_span (P.map (Polynomial.evalRingHom 0 : Polynomial K →+* K)) ⊔
              matrix_column_span
                (Q.map (Polynomial.evalRingHom 0 : Polynomial K →+* K))) ≤
          Module.finrank K
            ↥(matrix_column_span (P.map (Polynomial.evalRingHom t : Polynomial K →+* K)) ⊔
              matrix_column_span
                (Q.map (Polynomial.evalRingHom t : Polynomial K →+* K))) := by
  classical
  let P0 : Matrix (Fin n) (Fin n) K :=
    P.map (Polynomial.evalRingHom 0 : Polynomial K →+* K)
  let Q0 : Matrix (Fin n) (Fin n) K :=
    Q.map (Polynomial.evalRingHom 0 : Polynomial K →+* K)
  let S0 := matrix_column_span P0 ⊔ matrix_column_span Q0
  obtain ⟨S0c, hcompl⟩ := Submodule.exists_isCompl S0
  let proj : (Fin n → K) →ₗ[K] (Fin n → K) := S0.projection S0c hcompl
  let delta : Fin n → Fin n → K := fun j i => if i = j then 1 else 0
  let W0 : Matrix (Fin n) (Fin n) K := fun i j => proj (delta j) i
  have hmulVec (x : Fin n → K) : W0.mulVec x = proj x := by
    have hx : (∑ j, x j • delta j) = x := by
      ext i
      simp [delta]
    calc
      W0.mulVec x = ∑ j, x j • proj (delta j) := by
        ext i
        simp [W0, Matrix.mulVec, dotProduct, mul_comm]
      _ = proj (∑ j, x j • delta j) := by simp
      _ = proj x := congrArg proj hx
  have hW0col (j : Fin n) : W0.col j ∈ S0 := by
    change proj (delta j) ∈ S0
    exact (Submodule.range_projection hcompl).symm ▸
      LinearMap.mem_range_self proj (delta j)
  have span_repr (M : Matrix (Fin n) (Fin n) K) (x : Fin n → K)
      (hx : x ∈ matrix_column_span M) : ∃ c : Fin n → K, M.mulVec c = x := by
    change x ∈ Submodule.span K (Set.range (fun j => fun i => M i j)) at hx
    refine Submodule.span_induction (R := K)
      (p := fun x _ => ∃ c : Fin n → K, M.mulVec c = x) ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with ⟨j, rfl⟩
      refine ⟨fun k => if k = j then 1 else 0, ?_⟩
      ext i
      simp [Matrix.mulVec, dotProduct]
    · exact ⟨0, by simp⟩
    · intro x y _ _ hx hy
      rcases hx with ⟨cx, rfl⟩
      rcases hy with ⟨cy, rfl⟩
      refine ⟨cx + cy, ?_⟩
      ext i
      simp only [Matrix.mulVec, dotProduct, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    · intro a x _ hx
      rcases hx with ⟨cx, rfl⟩
      refine ⟨a • cx, ?_⟩
      ext i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
  have hrepr (j : Fin n) :
      ∃ rp rq : Fin n → K,
        P0.mulVec rp + Q0.mulVec rq = W0.col j := by
    rcases (Submodule.mem_sup.mp (hW0col j)) with ⟨x, hx, y, hy, hxy⟩
    rcases span_repr P0 x hx with ⟨rp, hrp⟩
    rcases span_repr Q0 y hy with ⟨rq, hrq⟩
    refine ⟨rp, rq, ?_⟩
    rw [← hxy, ← hrp, ← hrq]
  choose rp rq hrpq using hrepr
  let R : Matrix (Fin n) (Fin n) K := fun i j => rp j i
  let S : Matrix (Fin n) (Fin n) K := fun i j => rq j i
  have hfactor : P0 * R + Q0 * S = W0 := by
    ext i j
    have h := congrFun (hrpq j) i
    simpa [R, S, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using h
  let W : Matrix (Fin n) (Fin n) (Polynomial K) :=
    P * R.map Polynomial.C + Q * S.map Polynomial.C
  have hWeval (t : K) :
      W.map (Polynomial.evalRingHom t : Polynomial K →+* K) =
        P.map (Polynomial.evalRingHom t : Polynomial K →+* K) * R +
          Q.map (Polynomial.evalRingHom t : Polynomial K →+* K) * S := by
    ext i j
    simp [W, Matrix.mul_apply, Polynomial.eval_finset_sum, Polynomial.eval_mul]
  have hWzero :
      W.map (Polynomial.evalRingHom 0 : Polynomial K →+* K) = W0 := by
    rw [hWeval]
    exact hfactor
  have column_span_eq_span_cols (M : Matrix (Fin n) (Fin n) K) :
      matrix_column_span M = Submodule.span K (Set.range M.col) := by
    apply congrArg (Submodule.span K)
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, rfl⟩
  have hspanW0 : matrix_column_span W0 = S0 := by
    rw [column_span_eq_span_cols, ← Matrix.range_mulVecLin]
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      rw [Matrix.mulVecLin_apply, hmulVec]
      exact (Submodule.range_projection hcompl).symm ▸ LinearMap.mem_range_self proj x
    · intro y hy
      refine ⟨y, ?_⟩
      rw [Matrix.mulVecLin_apply, hmulVec]
      exact S0.projection_apply_left hcompl ⟨y, hy⟩
  have hW0rank : W0.rank = Module.finrank K S0 := by
    rw [Matrix.rank_eq_finrank_span_cols]
    rw [← column_span_eq_span_cols, hspanW0]
  rcases polynomial_matrix_rank_lower_bound_persists W with ⟨f, hf0, hf⟩
  refine ⟨f, hf0, ?_⟩
  intro t hft
  have hrank := hf t hft
  rw [hWzero, hW0rank] at hrank
  let Pt : Matrix (Fin n) (Fin n) K :=
    P.map (Polynomial.evalRingHom t : Polynomial K →+* K)
  let Qt : Matrix (Fin n) (Fin n) K :=
    Q.map (Polynomial.evalRingHom t : Polynomial K →+* K)
  let St := matrix_column_span Pt ⊔ matrix_column_span Qt
  have mulVec_mem_column_span (M : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
      M.mulVec x ∈ matrix_column_span M := by
    change M.mulVec x ∈ Submodule.span K (Set.range (fun j => fun i => M i j))
    have heq : M.mulVec x = ∑ j, x j • (fun i => M i j) := by
      ext i
      simp [Matrix.mulVec, dotProduct, mul_comm]
    rw [heq]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hspan :
      matrix_column_span
          (W.map (Polynomial.evalRingHom t : Polynomial K →+* K)) ≤ St := by
    rw [hWeval]
    apply Submodule.span_le.mpr
    rintro z ⟨j, rfl⟩
    apply Submodule.add_mem
    · apply (le_sup_left : matrix_column_span Pt ≤ St)
      have hm := mulVec_mem_column_span Pt (fun k => R k j)
      change Pt.mulVec (fun k => R k j) ∈ matrix_column_span Pt
      exact hm
    · apply (le_sup_right : matrix_column_span Qt ≤ St)
      have hm := mulVec_mem_column_span Qt (fun k => S k j)
      change Qt.mulVec (fun k => S k j) ∈ matrix_column_span Qt
      exact hm
  change Module.finrank K S0 ≤ Module.finrank K St
  calc
    Module.finrank K S0 ≤
        (W.map (Polynomial.evalRingHom t : Polynomial K →+* K)).rank := hrank
    _ = Module.finrank K
          (matrix_column_span
            (W.map (Polynomial.evalRingHom t : Polynomial K →+* K))) := by
      rw [column_span_eq_span_cols]
      exact Matrix.rank_eq_finrank_span_cols
        (W.map (Polynomial.evalRingHom t : Polynomial K →+* K))
    _ ≤ Module.finrank K St := Submodule.finrank_mono hspan

@[blueprint "lem:minimal-tensor-decomposition-third-factors-nonzero"
  (statement := /-- If a tensor has rank $r$, then in every decomposition of length $r$
  each third factor is nonzero. -/)
  (proof := /-- If one third factor vanished, its rank-one summand would be zero. Removing
  that index with the order embedding which skips it would give a decomposition of length
  $r-1$, contradicting the defining lower bound for tensor rank. -/)
  (title := /-- Third factors in a minimal decomposition are nonzero -/)
  (latexEnv := "lemma")]
lemma minimal_tensor_decomposition_third_factors_nonzero
    {K : Type} [Field K] {n p r : ℕ}
    (T : order_three_tensor K n p)
    (u v : Fin r → Fin n → K) (w : Fin r → Fin p → K)
    (hdecomp : tensor_decomposition T u v w) (hrank : has_tensor_rank T r) :
    ∀ a, w a ≠ 0 := by
  intro a hwa
  cases r with
  | zero => exact Fin.elim0 a
  | succ r =>
      let u' : Fin r → Fin n → K := fun b => u (a.succAbove b)
      let v' : Fin r → Fin n → K := fun b => v (a.succAbove b)
      let w' : Fin r → Fin p → K := fun b => w (a.succAbove b)
      have hsmall : tensor_decomposition T u' v' w' := by
        change T = ∑ b, rank_one_tensor (u' b) (v' b) (w' b)
        rw [hdecomp, Fin.sum_univ_succAbove _ a]
        have hzero : rank_one_tensor (u a) (v a) (w a) = 0 := by
          ext i j k
          simp [rank_one_tensor, hwa]
        rw [hzero]
        simp [u', v', w']
      have hle := hrank.2 r u' v' w' hsmall
      omega

@[blueprint "lem:common-nonzero-pairing-direction"
  (statement := /-- Let $K$ be an infinite field. For two finite families of nonzero
  vectors in $K^p$, where $p>0$, there is one vector $d\in K^p$ with $d_0=1$ whose
  pairing with every vector in both families is nonzero. -/)
  (proof := /-- Encode a vector $z$ by
  $P_z(X)=\sum_k z_kX^k$. A nonzero vector gives a nonzero polynomial, because the
  coefficient of $X^k$ recovers $z_k$. The product of the finitely many polynomials from
  both families is therefore nonzero. A nonzero polynomial over an infinite field does
  not vanish everywhere, so choose $t$ where this product is nonzero and put $d_k=t^k$.
  Then $d_0=1$, and evaluation of each factor gives the required pairing. -/)
  (title := /-- A common direction avoiding finitely many pairing hyperplanes -/)
  (latexEnv := "lemma")]
lemma common_nonzero_pairing_direction
    {K : Type} [Field K] [Infinite K] {p r s : ℕ}
    (hp : 0 < p) (w : Fin r → Fin p → K) (w' : Fin s → Fin p → K)
    (hw : ∀ a, w a ≠ 0) (hw' : ∀ a, w' a ≠ 0) :
    ∃ d : Fin p → K, d ⟨0, hp⟩ = 1 ∧
      (∀ a, (∑ k, d k * w a k) ≠ 0) ∧
      ∀ a, (∑ k, d k * w' a k) ≠ 0 := by
  classical
  let poly : (Fin p → K) → Polynomial K :=
    fun z => ∑ k, Polynomial.C (z k) * Polynomial.X ^ (k : ℕ)
  have poly_ne_zero {z : Fin p → K} (hz : z ≠ 0) : poly z ≠ 0 := by
    obtain ⟨k, hk⟩ : ∃ k, z k ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hz
      funext j
      exact hall j
    intro hzero
    have hcoeff := congrArg (fun f : Polynomial K => f.coeff (k : ℕ)) hzero
    simp only [poly, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at hcoeff
    have hsum :
        (∑ x : Fin p, if (k : ℕ) = (x : ℕ) then z x else 0) = z k := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hj
        have hval : (k : ℕ) ≠ (j : ℕ) := fun h => hj (Fin.ext h.symm)
        simp [hval]
      · simp
    rw [hsum] at hcoeff
    exact hk hcoeff
  let g : Polynomial K := (∏ a, poly (w a)) * ∏ a, poly (w' a)
  have hg : g ≠ 0 := by
    apply mul_ne_zero
    · exact Finset.prod_ne_zero_iff.mpr fun a _ => poly_ne_zero (hw a)
    · exact Finset.prod_ne_zero_iff.mpr fun a _ => poly_ne_zero (hw' a)
  obtain ⟨t, ht⟩ : ∃ t : K, Polynomial.eval t g ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hg (Polynomial.zero_of_eval_zero g hall)
  let d : Fin p → K := fun k => t ^ (k : ℕ)
  have heval (z : Fin p → K) :
      Polynomial.eval t (poly z) = ∑ k : Fin p, t ^ (k : ℕ) * z k := by
    simp only [poly, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hprod :
      (∏ a, Polynomial.eval t (poly (w a))) ≠ 0 ∧
        (∏ a, Polynomial.eval t (poly (w' a))) ≠ 0 := by
    change Polynomial.eval t ((∏ a, poly (w a)) * ∏ a, poly (w' a)) ≠ 0 at ht
    simp only [Polynomial.eval_mul, Polynomial.eval_prod] at ht
    exact mul_ne_zero_iff.mp ht
  refine ⟨d, by simp [d], ?_, ?_⟩
  · intro a
    have ha := (Finset.prod_ne_zero_iff.mp hprod.1) a (Finset.mem_univ a)
    rw [heval] at ha
    simpa [d] using ha
  · intro a
    have ha := (Finset.prod_ne_zero_iff.mp hprod.2) a (Finset.mem_univ a)
    rw [heval] at ha
    simpa [d] using ha

@[blueprint "lem:normalized-commutator-column-sum-bound"
  (statement := /-- Let a tensor have a length-$r$ decomposition, let
  $A=\sum_k c_kT_k$ be invertible, and suppose every pairing
  $\sum_kc_k(w_a)_k$ is nonzero. For any three slices $T_i,T_j,T_l$, the dimension of
  the sum of the column spaces of
  $[A^{-1}T_i,A^{-1}T_j]$ and $[A^{-1}T_i,A^{-1}T_l]$ is at most $3(r-n)$. -/)
  (proof := /-- Write the normalized slices as $XE_kY$, where the $E_k$ are diagonal and
  $XY=I_n$. Put $H=I_r-YX$. Each commutator is
  $X(E_jHE_i-E_iHE_j)Y$. Hence the two commutator images lie in the sum of the three
  column spaces of $XE_iH$, $XE_jH$, and $XE_lH$. Since $XH=0$, the column space of
  $H$ lies in the kernel of $X$. The identity $XY=I_n$ gives
  $\operatorname{rank}X=n$, so rank-nullity gives
  $\dim\ker X=r-n$. Each of the three column spaces therefore has dimension at most
  $r-n$, and subadditivity gives the asserted bound. -/)
  (title := /-- A four-slice bound for two commutator images -/)
  (latexEnv := "lemma")]
lemma normalized_commutator_column_sum_bound
    {K : Type} [Field K] {n p r : ℕ}
    (T : order_three_tensor K n p)
    (u v : Fin r → Fin n → K) (w : Fin r → Fin p → K)
    (hdecomp : tensor_decomposition T u v w)
    (A : Matrix (Fin n) (Fin n) K) (c : Fin p → K)
    (hA : A = ∑ k, c k • tensor_slice T k) (hAunit : IsUnit A)
    (hnonzero : ∀ a, (∑ k, c k * w a k) ≠ 0)
    (i j l : Fin p) :
    Module.finrank K
        ↥(matrix_column_span
            (matrix_commutator (A⁻¹ * tensor_slice T i) (A⁻¹ * tensor_slice T j)) ⊔
          matrix_column_span
            (matrix_commutator (A⁻¹ * tensor_slice T i) (A⁻¹ * tensor_slice T l))) ≤
      3 * (r - n) := by
  classical
  let U : Matrix (Fin n) (Fin r) K := fun x a => u a x
  let V : Matrix (Fin r) (Fin n) K := fun a y => v a y
  let α : Fin r → K := fun a => ∑ k, c k * w a k
  let D : Fin p → Matrix (Fin r) (Fin r) K :=
    fun k => Matrix.diagonal (fun a => w a k)
  let Dα : Matrix (Fin r) (Fin r) K := Matrix.diagonal α
  let Dαi : Matrix (Fin r) (Fin r) K := Matrix.diagonal (fun a => (α a)⁻¹)
  have hslice (k : Fin p) : tensor_slice T k = U * D k * V := by
    have hUD : U * D k = fun x a => u a x * w a k := by
      ext x a
      change (U * Matrix.diagonal (fun b => w b k)) x a = u a x * w a k
      rw [Matrix.mul_diagonal]
    rw [hUD]
    ext x y
    change T x y k = _
    rw [hdecomp]
    simp [V, rank_one_tensor, Matrix.mul_apply, mul_assoc, mul_comm, mul_left_comm]
  have hAfac : A = U * Dα * V := by
    have hDsum : (∑ k, c k • D k) = Dα := by
      ext a b
      by_cases hab : a = b
      · subst b
        simp [D, Dα, α, Matrix.sum_apply, Matrix.smul_apply, mul_comm]
      · simp [D, Dα, Matrix.sum_apply, Matrix.smul_apply, hab]
    calc
      A = ∑ k, c k • tensor_slice T k := hA
      _ = ∑ k, U * (c k • D k) * V := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hslice]
        ext x y
        simp [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc,
          mul_comm, mul_left_comm]
      _ = U * (∑ k, c k • D k) * V := by
        symm
        rw [Matrix.mul_sum, Matrix.sum_mul]
      _ = U * Dα * V := by rw [hDsum]
  have hDinv : Dα * Dαi = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext a b
    by_cases hab : a = b
    · subst b
      simp [Dα, Dαi, α, hnonzero]
    · simp [Dα, Dαi, hab]
  let X : Matrix (Fin n) (Fin r) K := A⁻¹ * U * Dα
  let Y : Matrix (Fin r) (Fin n) K := V
  have hXY : X * Y = 1 := by
    calc
      X * Y = A⁻¹ * (U * Dα * V) := by simp [X, Y, Matrix.mul_assoc]
      _ = A⁻¹ * A := by rw [← hAfac]
      _ = 1 := Matrix.nonsing_inv_mul A
        ((Matrix.isUnit_iff_isUnit_det A).mp hAunit)
  let E : Fin p → Matrix (Fin r) (Fin r) K := fun k => Dαi * D k
  have hDE (k : Fin p) : Dα * E k = D k := by
    simp only [E, ← Matrix.mul_assoc, hDinv, one_mul]
  have hEcomm (k m : Fin p) : E k * E m = E m * E k := by
    simp [E, Dαi, D, Matrix.diagonal_mul_diagonal, mul_comm]
  have hB (k : Fin p) : A⁻¹ * tensor_slice T k = X * E k * Y := by
    rw [hslice]
    simp only [X, Y]
    calc
      A⁻¹ * (U * D k * V) = A⁻¹ * U * D k * V := by
        simp [Matrix.mul_assoc]
      _ = A⁻¹ * U * (Dα * E k) * V := by rw [hDE]
      _ = (A⁻¹ * U * Dα) * E k * V := by simp [Matrix.mul_assoc]
  let H : Matrix (Fin r) (Fin r) K := 1 - Y * X
  have hXH : X * H = 0 := by
    change X * (1 - Y * X) = 0
    have hassoc : X * (Y * X) = (X * Y) * X := (Matrix.mul_assoc X Y X).symm
    rw [Matrix.mul_sub, Matrix.mul_one, hassoc, hXY, Matrix.one_mul, sub_self]
  have hcomm (k m : Fin p) :
      matrix_commutator (A⁻¹ * tensor_slice T k) (A⁻¹ * tensor_slice T m) =
        X * (E m * H * E k - E k * H * E m) * Y := by
    rw [hB, hB]
    unfold matrix_commutator
    have hinside :
        E k * (Y * X) * E m - E m * (Y * X) * E k =
          E m * H * E k - E k * H * E m := by
      change E k * (Y * X) * E m - E m * (Y * X) * E k =
        E m * (1 - Y * X) * E k - E k * (1 - Y * X) * E m
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
      rw [hEcomm m k]
      abel
    calc
      (X * E k * Y) * (X * E m * Y) - (X * E m * Y) * (X * E k * Y) =
          X * (E k * (Y * X) * E m - E m * (Y * X) * E k) * Y := by
        simp only [Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]
      _ = X * (E m * H * E k - E k * H * E m) * Y := by rw [hinside]
  let cs {a b : Type} [Fintype a] [Fintype b]
      (M : Matrix a b K) : Submodule K (a → K) :=
    Submodule.span K (Set.range M.col)
  have cs_mul_le {a b d : Type} [Fintype a] [Fintype b] [Fintype d]
      (M : Matrix a b K) (N : Matrix b d K) : cs (M * N) ≤ cs M := by
    apply Submodule.span_le.mpr
    rintro z ⟨q, rfl⟩
    have heq : (M * N).col q = ∑ k, N k q • M.col k := by
      ext x
      simp [Matrix.mul_apply, mul_comm]
    rw [heq]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have cs_sub_le {a b : Type} [Fintype a] [Fintype b]
      (M N : Matrix a b K) : cs (M - N) ≤ cs M ⊔ cs N := by
    apply Submodule.span_le.mpr
    rintro z ⟨q, rfl⟩
    apply Submodule.sub_mem
    · exact (le_sup_left : cs M ≤ cs M ⊔ cs N) (Submodule.subset_span ⟨q, rfl⟩)
    · exact (le_sup_right : cs N ≤ cs M ⊔ cs N) (Submodule.subset_span ⟨q, rfl⟩)
  let F : Fin p → Matrix (Fin n) (Fin r) K := fun k => X * E k * H
  have hcomm_le (k m : Fin p) :
      matrix_column_span
          (matrix_commutator (A⁻¹ * tensor_slice T k) (A⁻¹ * tensor_slice T m)) ≤
        cs (F m) ⊔ cs (F k) := by
    rw [hcomm]
    change cs (X * (E m * H * E k - E k * H * E m) * Y) ≤ _
    calc
      cs (X * (E m * H * E k - E k * H * E m) * Y) ≤
          cs (X * (E m * H * E k - E k * H * E m)) := cs_mul_le _ _
      _ = cs (F m * E k - F k * E m) := by
        congr 1
        simp [F, Matrix.mul_assoc, Matrix.mul_sub]
      _ ≤ cs (F m * E k) ⊔ cs (F k * E m) := cs_sub_le _ _
      _ ≤ cs (F m) ⊔ cs (F k) :=
        sup_le_sup (cs_mul_le _ _) (cs_mul_le _ _)
  have hXrank : X.rank = n := by
    apply le_antisymm
    · simpa using Matrix.rank_le_card_height X
    · calc
        n = (1 : Matrix (Fin n) (Fin n) K).rank := by simp
        _ = (X * Y).rank := by rw [hXY]
        _ ≤ X.rank := Matrix.rank_mul_le_left X Y
  have hHker : cs H ≤ LinearMap.ker X.mulVecLin := by
    apply Submodule.span_le.mpr
    rintro z ⟨q, rfl⟩
    change X.mulVec (H.col q) = 0
    have h := congrArg (fun M : Matrix (Fin n) (Fin r) K => M.col q) hXH
    change (X * H).col q = 0
    have hz : (0 : Matrix (Fin n) (Fin r) K).col q = (0 : Fin n → K) := by
      ext x
      rfl
    rw [hz] at h
    exact h
  have hHdim : Module.finrank K (cs H) ≤ r - n := by
    calc
      Module.finrank K (cs H) ≤ Module.finrank K (LinearMap.ker X.mulVecLin) :=
        Submodule.finrank_mono hHker
      _ = r - X.rank := by
        have hnull := LinearMap.finrank_range_add_finrank_ker X.mulVecLin
        have hrange :
            Module.finrank K (LinearMap.range X.mulVecLin) = X.rank := rfl
        rw [hrange] at hnull
        simp only [Module.finrank_pi, Fintype.card_fin] at hnull
        omega
      _ = r - n := by rw [hXrank]
  have hFdim (k : Fin p) : Module.finrank K (cs (F k)) ≤ r - n := by
    calc
      Module.finrank K (cs (F k)) = (F k).rank :=
        (Matrix.rank_eq_finrank_span_cols (F k)).symm
      _ ≤ H.rank := by
        simp only [F]
        exact Matrix.rank_mul_le_right (X * E k) H
      _ = Module.finrank K (cs H) := Matrix.rank_eq_finrank_span_cols H
      _ ≤ r - n := hHdim
  have htotal :
      matrix_column_span
          (matrix_commutator (A⁻¹ * tensor_slice T i) (A⁻¹ * tensor_slice T j)) ⊔
        matrix_column_span
          (matrix_commutator (A⁻¹ * tensor_slice T i) (A⁻¹ * tensor_slice T l)) ≤
        (cs (F i) ⊔ cs (F j)) ⊔ cs (F l) := by
    apply sup_le
    · exact (hcomm_le i j).trans (sup_le
        (le_sup_right.trans le_sup_left)
        (le_sup_left.trans le_sup_left))
    · exact (hcomm_le i l).trans (sup_le
        le_sup_right
        (le_sup_left.trans le_sup_left))
  calc
    Module.finrank K
        ↥(matrix_column_span
            (matrix_commutator (A⁻¹ * tensor_slice T i) (A⁻¹ * tensor_slice T j)) ⊔
          matrix_column_span
            (matrix_commutator (A⁻¹ * tensor_slice T i) (A⁻¹ * tensor_slice T l))) ≤
        Module.finrank K ↥((cs (F i) ⊔ cs (F j)) ⊔ cs (F l)) :=
      Submodule.finrank_mono htotal
    _ ≤ (Module.finrank K (cs (F i)) + Module.finrank K (cs (F j))) +
          Module.finrank K (cs (F l)) := le_trans
      (Submodule.finrank_add_le_finrank_add_finrank _ _)
      (Nat.add_le_add_right (Submodule.finrank_add_le_finrank_add_finrank _ _) _)
    _ ≤ 3 * (r - n) := by
      have hi := hFdim i
      have hj := hFdim j
      have hl := hFdim l
      omega

@[blueprint "lem:affine-normalization-commutator-polynomial-model"
  (statement := /-- Let $A(t)=A_0+tD$. For a tensor with $q+2$ slices there are
  polynomial matrices $C_{kl}(t)$ such that, whenever $A(t)$ is invertible, the column
  space of $C_{kl}(t)$ equals that of
  $[A(t)^{-1}T_{k+2},A(t)^{-1}T_{l+2}]$ for every $k,l$. -/)
  (proof := /-- Regard $A(t)$ as a polynomial matrix and put
  $N_k(t)=\operatorname{adj}(A(t))T_{k+2}$ and
  $C_{kl}(t)=[N_k(t),N_l(t)]$. Evaluation commutes with adjugates and matrix
  operations. If $A(t)$ is invertible, then
  $A(t)^{-1}=\det(A(t))^{-1}\operatorname{adj}(A(t))$, so the normalized commutator
  is the nonzero scalar $\det(A(t))^{-2}$ times $C_{kl}(t)$. Nonzero scalar
  multiplication does not change a matrix column space. -/)
  (title := /-- Polynomial models for commutators along an affine normalization -/)
  (latexEnv := "lemma")]
lemma affine_normalization_commutator_polynomial_model
    {K : Type} [Field K] {n q : ℕ}
    (T : order_three_tensor K n (q + 2))
    (A0 D : Matrix (Fin n) (Fin n) K) :
    ∃ (Ap : Matrix (Fin n) (Fin n) (Polynomial K))
      (Cp : Fin (q + 1) → Fin (q + 1) →
        Matrix (Fin n) (Fin n) (Polynomial K)),
      (∀ t : K,
        Ap.map (Polynomial.evalRingHom t : Polynomial K →+* K) = A0 + t • D) ∧
      ∀ (t : K), IsUnit (A0 + t • D) → ∀ k l,
        matrix_column_span
            (matrix_commutator
              ((A0 + t • D)⁻¹ * tensor_slice T k.succ)
              ((A0 + t • D)⁻¹ * tensor_slice T l.succ)) =
          matrix_column_span
            ((Cp k l).map
              (Polynomial.evalRingHom t : Polynomial K →+* K)) := by
  classical
  let Ap : Matrix (Fin n) (Fin n) (Polynomial K) :=
    fun x y => Polynomial.C (A0 x y) + Polynomial.X * Polynomial.C (D x y)
  have hApeval (t : K) :
      Ap.map (Polynomial.evalRingHom t : Polynomial K →+* K) = A0 + t • D := by
    ext x y
    simp [Ap, Matrix.smul_apply]
    ring
  let Np : Fin (q + 1) → Matrix (Fin n) (Fin n) (Polynomial K) :=
    fun k => Ap.adjugate * (tensor_slice T k.succ).map Polynomial.C
  let Cp : Fin (q + 1) → Fin (q + 1) →
      Matrix (Fin n) (Fin n) (Polynomial K) :=
    fun k l => matrix_commutator (Np k) (Np l)
  have hNeval (t : K) (k : Fin (q + 1)) :
      (Np k).map (Polynomial.evalRingHom t : Polynomial K →+* K) =
        (A0 + t • D).adjugate * tensor_slice T k.succ := by
    have hadj :
        Ap.adjugate.map (Polynomial.evalRingHom t : Polynomial K →+* K) =
          (A0 + t • D).adjugate := by
      change (Polynomial.evalRingHom t).mapMatrix Ap.adjugate = _
      rw [RingHom.map_adjugate]
      change (Ap.map (Polynomial.evalRingHom t : Polynomial K →+* K)).adjugate = _
      rw [hApeval]
    change (Ap.adjugate * (tensor_slice T k.succ).map Polynomial.C).map
      (Polynomial.evalRingHom t : Polynomial K →+* K) = _
    rw [Matrix.map_mul, hadj]
    ext x y
    simp [Matrix.mul_apply]
  have hCeval (t : K) (k l : Fin (q + 1)) :
      (Cp k l).map (Polynomial.evalRingHom t : Polynomial K →+* K) =
        matrix_commutator ((A0 + t • D).adjugate * tensor_slice T k.succ)
          ((A0 + t • D).adjugate * tensor_slice T l.succ) := by
    calc
      (Cp k l).map (Polynomial.evalRingHom t : Polynomial K →+* K) =
          matrix_commutator
            ((Np k).map (Polynomial.evalRingHom t : Polynomial K →+* K))
            ((Np l).map (Polynomial.evalRingHom t : Polynomial K →+* K)) := by
        ext x y
        simp [Cp, matrix_commutator, Matrix.mul_apply, Polynomial.eval_finset_sum,
          Polynomial.eval_mul]
      _ = matrix_commutator ((A0 + t • D).adjugate * tensor_slice T k.succ)
          ((A0 + t • D).adjugate * tensor_slice T l.succ) :=
        congrArg₂ matrix_commutator (hNeval t k) (hNeval t l)
  have column_span_smul (a : K) (ha : a ≠ 0)
      (M : Matrix (Fin n) (Fin n) K) :
      matrix_column_span (a • M) = matrix_column_span M := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro z ⟨j, rfl⟩
      change (fun i => a * M i j) ∈ matrix_column_span M
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · apply Submodule.span_le.mpr
      rintro z ⟨j, rfl⟩
      have hmem :
          (a⁻¹ : K) • (fun i => a * M i j) ∈ matrix_column_span (a • M) :=
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      have heq :
          (a⁻¹ : K) • (fun i => a * M i j) = fun i => M i j := by
        ext i
        simp [Pi.smul_apply, ha]
      rw [heq] at hmem
      exact hmem
  refine ⟨Ap, Cp, hApeval, ?_⟩
  intro t hunit k l
  have hdetunit := (Matrix.isUnit_iff_isUnit_det (A0 + t • D)).mp hunit
  let z : K := ↑hdetunit.unit⁻¹
  have hz : z ≠ 0 := Units.ne_zero hdetunit.unit⁻¹
  have hinv : (A0 + t • D)⁻¹ = z • (A0 + t • D).adjugate := by
    simpa [z] using
      Matrix.nonsing_inv_apply (A := A0 + t • D) hdetunit
  have heq :
      matrix_commutator
          ((A0 + t • D)⁻¹ * tensor_slice T k.succ)
          ((A0 + t • D)⁻¹ * tensor_slice T l.succ) =
        (z * z) •
          ((Cp k l).map (Polynomial.evalRingHom t : Polynomial K →+* K)) := by
    rw [hinv, hCeval]
    simp only [Matrix.smul_mul]
    unfold matrix_commutator
    simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_sub, mul_assoc,
      mul_comm]
  rw [heq, column_span_smul (z * z) (mul_ne_zero hz hz)]

@[blueprint "lem:generic-normalization-preserves-commutator-dimensions"
  (statement := /-- Let $K$ be an infinite field. Suppose that a displayed length-$r$
  decomposition of an $n\times n\times(q+2)$ tensor $T$ satisfies the tensor uniqueness
  hypotheses and that $T$ has rank $r$. Given any second length-$r$ decomposition, there
  are coefficients $\lambda$, a matrix
  $A=\sum_k\lambda_kT_k$, and an embedding
  $\iota:\operatorname{Fin}(n)\hookrightarrow\operatorname{Fin}(r)$ such that $A$ is an
  invertible member of the slice span, $\lambda_0\ne0$, every pairing of $\lambda$ with
  a third factor in either decomposition is nonzero, and the normalized nonfirst slices
  $A^{-1}T_2,\ldots,A^{-1}T_{q+2}$ satisfy the quantified commuting-extension dimension
  hypotheses with parameter $r$. -/)
  (proof := /-- Let $A_0$ be the invertible slice combination and let $H_0$ be the
  dimension hypothesis supplied by the tensor uniqueness assumptions. By
  \cref{lem:slice-span-coefficient-representation}, write
  $A_0=\sum_k(c_0)_kT_k$. Since both displayed decompositions have the minimal length
  $r$, \cref{lem:minimal-tensor-decomposition-third-factors-nonzero} shows that every
  third factor in either decomposition is nonzero. Apply
  \cref{lem:common-nonzero-pairing-direction} to obtain a vector $d$ with $d_0=1$
  which pairs nontrivially with every such third factor.

  Put $D=\sum_kd_kT_k$, $A(t)=A_0+tD$, and
  $c_k(t)=(c_0)_k+td_k$. By
  \cref{lem:affine-normalization-commutator-polynomial-model}, there are a polynomial
  matrix $\mathcal A(t)$ evaluating to $A(t)$ and polynomial matrices
  $C_{ab}(t)$ whose evaluated column spaces are those of the normalized commutators
  whenever $A(t)$ is invertible. For every nonzero index $l$, choose from $H_0$ an
  index $m(l)$ and the corresponding three commutator dimensions and three dimensions
  of sums of two commutator column spaces. Applying
  \cref{lem:polynomial-matrix-rank-lower-bound-persists} to the three relevant
  matrices $C_{ab}(t)$ gives polynomials whose nonvanishing preserves the three rank
  lower bounds. Applying
  \cref{lem:polynomial-matrix-column-sum-dimension-persists} to the three relevant
  pairs gives polynomials whose nonvanishing preserves the three column-space-sum
  lower bounds.

  Form one polynomial as the product of $\det\mathcal A(t)$, the coordinate factor
  $(c_0)_0+t$, all pairing polynomials
  $\sum_k(c_0)_k(w_a)_k+t\sum_kd_k(w_a)_k$ and their counterparts for the competing
  decomposition, and all six families of persistence polynomials. The determinant
  factor is nonzero because its value at zero is $\det A_0$; the coordinate factor
  has coefficient one in degree one; every pairing polynomial has nonzero
  degree-one coefficient by the choice of $d$; and every persistence polynomial is
  nonzero because its value at zero is nonzero. Hence the product is nonzero.
  Infinitude of $K$ supplies a parameter $t$ at which it does not vanish.

  At this parameter, $A(t)$ is invertible, $c_0(t)\ne0$, and every required pairing
  is nonzero. The persistence factors give the six lower bounds transported from
  $A_0$. The individual commutator upper bounds from
  \cref{lem:strassen-three-slice-commutator-bound} and the column-space-sum upper
  bounds from \cref{lem:normalized-commutator-column-sum-bound} give the matching
  equalities, so the chosen witnesses $m(l)$ establish the full dimension
  hypothesis for $A(t)$. Finally,
  \cref{lem:invertible-slice-forces-row-rank} gives $n\leq r$, from which the
  coordinate embedding $\operatorname{Fin}(n)\hookrightarrow\operatorname{Fin}(r)$
  is obtained. -/)
  (title := /-- A common generic slice normalization -/)
  (latexEnv := "lemma")]
lemma generic_normalization_preserves_commutator_dimensions
    {K : Type} [Field K] [Infinite K] {n q r : ℕ}
    (T : order_three_tensor K n (q + 2))
    (u v : Fin r → Fin n → K) (w : Fin r → Fin (q + 2) → K)
    (h : tensor_uniqueness_hypotheses T u v w) (hrank : has_tensor_rank T r)
    (u' v' : Fin r → Fin n → K) (w' : Fin r → Fin (q + 2) → K)
    (hdecomp' : tensor_decomposition T u' v' w') :
    ∃ (A : Matrix (Fin n) (Fin n) K) (c : Fin (q + 2) → K)
      (ι : Fin n ↪ Fin r),
      A ∈ tensor_slice_span T ∧ IsUnit A ∧
      A = ∑ k, c k • tensor_slice T k ∧ c 0 ≠ 0 ∧
      commuting_extension_uniqueness_hypothesis r (normalized_nonfirst_slices A T) ∧
      (∀ a, (∑ k, c k * w a k) ≠ 0) ∧
      ∀ a, (∑ k, c k * w' a k) ≠ 0 := by
  classical
  rcases h with ⟨hq, hdecomp, hpair, hinvertible, A0, hA0span, hA0unit, hH0⟩
  rcases slice_span_coefficient_representation T A0 hA0span with ⟨c0, hA0c⟩
  have hw : ∀ a, w a ≠ 0 :=
    minimal_tensor_decomposition_third_factors_nonzero T u v w hdecomp hrank
  have hw' : ∀ a, w' a ≠ 0 :=
    minimal_tensor_decomposition_third_factors_nonzero T u' v' w' hdecomp' hrank
  have hp : 0 < q + 2 := by omega
  rcases common_nonzero_pairing_direction hp w w' hw hw' with
    ⟨d, hd0, hdw, hdw'⟩
  let D : Matrix (Fin n) (Fin n) K := ∑ k, d k • tensor_slice T k
  let At : K → Matrix (Fin n) (Fin n) K := fun t => A0 + t • D
  let ct : K → Fin (q + 2) → K := fun t k => c0 k + t * d k
  have hAtcoef (t : K) : At t = ∑ k, ct t k • tensor_slice T k := by
    change A0 + t • D = _
    rw [hA0c]
    simp only [ct, D, add_smul, Finset.sum_add_distrib, Finset.smul_sum,
      smul_smul]
  have hAtspan (t : K) : At t ∈ tensor_slice_span T := by
    rw [hAtcoef]
    change (∑ k, ct t k • tensor_slice T k) ∈
      Submodule.span K (Set.range (tensor_slice T))
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  rcases affine_normalization_commutator_polynomial_model T A0 D with
    ⟨Ap, Cp, hApeval0, hcommspan0⟩
  have hApeval (t : K) :
      Ap.map (Polynomial.evalRingHom t : Polynomial K →+* K) = At t := by
    simpa [At] using hApeval0 t
  have hcommspan (t : K) (hunit : IsUnit (At t)) (k l : Fin (q + 1)) :
      matrix_column_span
          (matrix_commutator
            ((At t)⁻¹ * tensor_slice T k.succ)
            ((At t)⁻¹ * tensor_slice T l.succ)) =
        matrix_column_span
          ((Cp k l).map (Polynomial.evalRingHom t : Polynomial K →+* K)) := by
    simpa [At] using hcommspan0 t (by simpa [At] using hunit) k l
  have hAtzero : At 0 = A0 := by simp [At]
  have hCp0 (k l : Fin (q + 1)) :
      matrix_column_span
          ((Cp k l).map (Polynomial.evalRingHom 0 : Polynomial K →+* K)) =
        matrix_column_span
          (matrix_commutator
            (A0⁻¹ * tensor_slice T k.succ)
            (A0⁻¹ * tensor_slice T l.succ)) := by
    rw [← hcommspan 0 (by simpa [hAtzero] using hA0unit) k l, hAtzero]
  let mw : Fin (q + 1) → Fin (q + 1) := fun l =>
    if hl : l ≠ 0 then Classical.choose (hH0 l hl) else 0
  have hmw (l : Fin (q + 1)) (hl : l ≠ 0) :
      mw l ≠ 0 ∧ mw l ≠ l ∧
        commuting_extension_dimension_hypothesis r
          (normalized_nonfirst_slices A0 T) 0 l (mw l) := by
    simp only [mw, dif_pos hl]
    exact Classical.choose_spec (hH0 l hl)
  let Rmat : Fin (q + 1) → Fin 3 →
      Matrix (Fin n) (Fin n) (Polynomial K) := fun l z =>
    if z = 0 then Cp 0 l else if z = 1 then Cp 0 (mw l) else Cp l (mw l)
  let SL : Fin (q + 1) → Fin 3 →
      Matrix (Fin n) (Fin n) (Polynomial K) := fun l z =>
    if z = 0 then Cp 0 l else if z = 1 then Cp l 0 else Cp (mw l) 0
  let SR : Fin (q + 1) → Fin 3 →
      Matrix (Fin n) (Fin n) (Polynomial K) := fun l z =>
    if z = 0 then Cp 0 (mw l) else if z = 1 then Cp l (mw l) else Cp (mw l) l
  let fr : Fin (q + 1) → Fin 3 → Polynomial K := fun l z =>
    Classical.choose (polynomial_matrix_rank_lower_bound_persists (Rmat l z))
  have hfr (l : Fin (q + 1)) (z : Fin 3) :
      Polynomial.eval 0 (fr l z) ≠ 0 ∧
        ∀ t : K, Polynomial.eval t (fr l z) ≠ 0 →
          ((Rmat l z).map
            (Polynomial.evalRingHom 0 : Polynomial K →+* K)).rank ≤
          ((Rmat l z).map
            (Polynomial.evalRingHom t : Polynomial K →+* K)).rank :=
    Classical.choose_spec
      (polynomial_matrix_rank_lower_bound_persists (Rmat l z))
  let fs : Fin (q + 1) → Fin 3 → Polynomial K := fun l z =>
    Classical.choose
      (polynomial_matrix_column_sum_dimension_persists (SL l z) (SR l z))
  have hfs (l : Fin (q + 1)) (z : Fin 3) :
      Polynomial.eval 0 (fs l z) ≠ 0 ∧
        ∀ t : K, Polynomial.eval t (fs l z) ≠ 0 →
          Module.finrank K
              ↥(matrix_column_span
                  ((SL l z).map
                    (Polynomial.evalRingHom 0 : Polynomial K →+* K)) ⊔
                matrix_column_span
                  ((SR l z).map
                    (Polynomial.evalRingHom 0 : Polynomial K →+* K))) ≤
            Module.finrank K
              ↥(matrix_column_span
                  ((SL l z).map
                    (Polynomial.evalRingHom t : Polynomial K →+* K)) ⊔
                matrix_column_span
                  ((SR l z).map
                    (Polynomial.evalRingHom t : Polynomial K →+* K))) :=
    Classical.choose_spec
      (polynomial_matrix_column_sum_dimension_persists (SL l z) (SR l z))
  let pairPoly (z : Fin r → Fin (q + 2) → K) (a : Fin r) : Polynomial K :=
    Polynomial.C (∑ k, c0 k * z a k) +
      Polynomial.X * Polynomial.C (∑ k, d k * z a k)
  let coordPoly : Polynomial K := Polynomial.C (c0 0) + Polynomial.X
  let g : Polynomial K :=
    Ap.det * coordPoly *
      (∏ a, pairPoly w a) * (∏ a, pairPoly w' a) *
      (∏ l, ∏ z, fr l z) * (∏ l, ∏ z, fs l z)
  have hdetpoly : Ap.det ≠ 0 := by
    intro heq
    have heval := congrArg (Polynomial.evalRingHom 0) heq
    rw [RingHom.map_det] at heval
    simp only [map_zero] at heval
    change (Ap.map (Polynomial.evalRingHom 0 : Polynomial K →+* K)).det = 0 at heval
    rw [hApeval 0, hAtzero] at heval
    have hdet0 := (Matrix.isUnit_iff_isUnit_det A0).mp hA0unit
    exact IsUnit.ne_zero hdet0 heval
  have hcoord : coordPoly ≠ 0 := by
    intro heq
    have hc := congrArg (fun f : Polynomial K => f.coeff 1) heq
    simpa [coordPoly] using hc
  have hpair (z : Fin r → Fin (q + 2) → K)
      (hz : ∀ a, (∑ k, d k * z a k) ≠ 0) (a : Fin r) :
      pairPoly z a ≠ 0 := by
    intro heq
    have hc := congrArg (fun f : Polynomial K => f.coeff 1) heq
    apply hz a
    simpa [pairPoly] using hc
  have hg : g ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · apply mul_ne_zero hdetpoly hcoord
          · exact Finset.prod_ne_zero_iff.mpr fun a _ => hpair w hdw a
        · exact Finset.prod_ne_zero_iff.mpr fun a _ => hpair w' hdw' a
      · exact Finset.prod_ne_zero_iff.mpr fun l _ =>
          Finset.prod_ne_zero_iff.mpr fun z _ =>
            fun heq => (hfr l z).1 (by rw [heq]; simp)
    · exact Finset.prod_ne_zero_iff.mpr fun l _ =>
        Finset.prod_ne_zero_iff.mpr fun z _ =>
          fun heq => (hfs l z).1 (by rw [heq]; simp)
  obtain ⟨t, ht⟩ : ∃ t : K, Polynomial.eval t g ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hg (Polynomial.zero_of_eval_zero g hall)
  have hparts :
      Polynomial.eval t Ap.det ≠ 0 ∧ Polynomial.eval t coordPoly ≠ 0 ∧
      (∀ a, Polynomial.eval t (pairPoly w a) ≠ 0) ∧
      (∀ a, Polynomial.eval t (pairPoly w' a) ≠ 0) ∧
      (∀ l z, Polynomial.eval t (fr l z) ≠ 0) ∧
      ∀ l z, Polynomial.eval t (fs l z) ≠ 0 := by
    change Polynomial.eval t
      (Ap.det * coordPoly * (∏ a, pairPoly w a) * (∏ a, pairPoly w' a) *
        (∏ l, ∏ z, fr l z) * (∏ l, ∏ z, fs l z)) ≠ 0 at ht
    simp only [Polynomial.eval_mul, Polynomial.eval_prod, mul_ne_zero_iff,
      Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const] at ht
    rcases ht with ⟨⟨⟨⟨⟨hdet, hcoord⟩, hw0⟩, hw0'⟩, hfr0⟩, hfs0⟩
    exact ⟨hdet, hcoord, hw0, hw0', hfr0, hfs0⟩
  have hAtunit : IsUnit (At t) := by
    apply (Matrix.isUnit_iff_isUnit_det (At t)).mpr
    apply isUnit_iff_ne_zero.mpr
    rw [← hApeval t]
    change ((Polynomial.evalRingHom t).mapMatrix Ap).det ≠ 0
    rw [← RingHom.map_det]
    exact hparts.1
  have hct0 : ct t 0 ≠ 0 := by
    have := hparts.2.1
    have hdzero : d 0 = 1 := hd0
    simpa [coordPoly, ct, hdzero] using this
  have hctw : ∀ a, (∑ k, ct t k * w a k) ≠ 0 := by
    intro a
    have := hparts.2.2.1 a
    simpa [pairPoly, ct, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc] using this
  have hctw' : ∀ a, (∑ k, ct t k * w' a k) ≠ 0 := by
    intro a
    have := hparts.2.2.2.1 a
    simpa [pairPoly, ct, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc] using this
  have hHt :
      commuting_extension_uniqueness_hypothesis r
        (normalized_nonfirst_slices (At t) T) := by
    intro l hl
    refine ⟨mw l, (hmw l hl).1, (hmw l hl).2.1, ?_⟩
    rcases (hmw l hl).2.2 with
      ⟨h0l, h0m, hlm, hr0l, hr0m, hrlm, hs0, hsl, hsm⟩
    let m := mw l
    have hrank_eq (a b : Fin (q + 1))
        (hbase : Module.finrank K
          (matrix_column_span
            (matrix_commutator
              (A0⁻¹ * tensor_slice T a.succ)
              (A0⁻¹ * tensor_slice T b.succ))) = 2 * (r - n))
        (z : Fin 3) (hR : Rmat l z = Cp a b) :
        Module.finrank K
          (matrix_column_span
            (matrix_commutator
              ((At t)⁻¹ * tensor_slice T a.succ)
              ((At t)⁻¹ * tensor_slice T b.succ))) = 2 * (r - n) := by
      have hlower := (hfr l z).2 t (hparts.2.2.2.2.1 l z)
      rw [hR] at hlower
      have hcpt := hcommspan t hAtunit a b
      have hlower' : 2 * (r - n) ≤
          Module.finrank K
            (matrix_column_span
              (matrix_commutator
                ((At t)⁻¹ * tensor_slice T a.succ)
                ((At t)⁻¹ * tensor_slice T b.succ))) := by
        rw [hcpt]
        calc
          2 * (r - n) = Module.finrank K
              (matrix_column_span
                ((Cp a b).map
                  (Polynomial.evalRingHom 0 : Polynomial K →+* K))) := by
            rw [hCp0 a b]
            exact hbase.symm
          _ = ((Cp a b).map
                (Polynomial.evalRingHom 0 : Polynomial K →+* K)).rank :=
            (Matrix.rank_eq_finrank_span_cols _).symm
          _ ≤ ((Cp a b).map
                (Polynomial.evalRingHom t : Polynomial K →+* K)).rank := hlower
          _ = Module.finrank K
              (matrix_column_span
                ((Cp a b).map
                  (Polynomial.evalRingHom t : Polynomial K →+* K))) :=
            Matrix.rank_eq_finrank_span_cols _
      have hupper := strassen_three_slice_commutator_bound
        T u v w hdecomp (At t) (hAtspan t) hAtunit a.succ b.succ
      omega
    have hsum_eq (a b c : Fin (q + 1))
        (hbase : Module.finrank K
          ↥(matrix_column_span
              (matrix_commutator
                (A0⁻¹ * tensor_slice T a.succ)
                (A0⁻¹ * tensor_slice T b.succ)) ⊔
            matrix_column_span
              (matrix_commutator
                (A0⁻¹ * tensor_slice T a.succ)
                (A0⁻¹ * tensor_slice T c.succ))) = 3 * (r - n))
        (z : Fin 3) (hL : SL l z = Cp a b) (hR : SR l z = Cp a c) :
        Module.finrank K
          ↥(matrix_column_span
              (matrix_commutator
                ((At t)⁻¹ * tensor_slice T a.succ)
                ((At t)⁻¹ * tensor_slice T b.succ)) ⊔
            matrix_column_span
              (matrix_commutator
                ((At t)⁻¹ * tensor_slice T a.succ)
                ((At t)⁻¹ * tensor_slice T c.succ))) = 3 * (r - n) := by
      have hlower := (hfs l z).2 t (hparts.2.2.2.2.2 l z)
      rw [hL, hR] at hlower
      rw [hCp0 a b, hCp0 a c] at hlower
      have hspab := hcommspan t hAtunit a b
      have hspac := hcommspan t hAtunit a c
      rw [← hspab, ← hspac] at hlower
      have hupper := normalized_commutator_column_sum_bound
        T u v w hdecomp (At t) (ct t) (hAtcoef t) hAtunit hctw
          a.succ b.succ c.succ
      omega
    refine ⟨h0l, h0m, hlm, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hrank_eq 0 l hr0l 0 (by simp [Rmat])
    · exact hrank_eq 0 (mw l) hr0m 1 (by simp [Rmat])
    · exact hrank_eq l (mw l) hrlm 2 (by
        simp [Rmat])
    · exact hsum_eq 0 l (mw l) hs0 0 (by simp [SL]) (by simp [SR])
    · exact hsum_eq l 0 (mw l) hsl 1 (by simp [SL]) (by simp [SR])
    · exact hsum_eq (mw l) 0 l hsm 2 (by
        simp [SL]) (by
        simp [SR])
  have hnr : n ≤ r :=
    invertible_slice_forces_row_rank T u v w hdecomp hinvertible
  let ι : Fin n ↪ Fin r :=
    ⟨fun a => ⟨a.val, lt_of_lt_of_le a.isLt hnr⟩,
      fun a b hab => Fin.ext (congrArg (fun x : Fin r => x.val) hab)⟩
  refine ⟨At t, ct t, ι, hAtspan t, hAtunit, hAtcoef t, hct0, hHt, hctw, hctw'⟩

@[blueprint "lem:dual-families-extend-to-inverse-matrices"
  (statement := /-- Let $K$ be a field and let $x_i,y_i\in K^r$, indexed by
  $i\in\operatorname{Fin}(n)$, satisfy $x_i^{\mathsf T}y_j=\delta_{ij}$. For every
  embedding $\iota:\operatorname{Fin}(n)\hookrightarrow\operatorname{Fin}(r)$, there are
  invertible matrices $X,Y\in M_r(K)$ with $X^{\mathsf T}Y=I_r$ whose columns indexed by
  $\iota(i)$ are respectively $x_i$ and $y_i$. -/)
  (proof := /-- Regard the transpose of the matrix with columns $x_i$ as a surjective map
  $L:K^r\to K^n$; the displayed duality says that the map with columns $y_i$ is a right
  inverse. Rank--nullity identifies $\ker L$ with a coordinate space indexed by the
  complement of the image of $\iota$. Mapping the prescribed coordinates by the $y_i$ and
  the complementary coordinates isomorphically onto $\ker L$ gives an automorphism of
  $K^r$. Its matrix is $Y$, and the transpose of the matrix of its inverse is $X$. The
  inverse identities give $X^{\mathsf T}Y=I_r$, while applying $L$ recovers the prescribed
  columns of $X$. -/)
  (title := /-- Completion of dual families to inverse matrices -/)
  (latexEnv := "lemma")]
lemma dual_families_extend_to_inverse_matrices
    {K : Type} [Field K] {n r : ℕ}
    (x y : Fin r → Fin n → K)
    (hdual : ∀ i j, ∑ a, x a i * y a j =
      (1 : Matrix (Fin n) (Fin n) K) i j)
    (ι : Fin n ↪ Fin r) :
    ∃ X Y : Matrix (Fin r) (Fin r) K,
      IsUnit X ∧ IsUnit Y ∧ X.transpose * Y = 1 ∧
      (∀ a i, Y a (ι i) = y a i) ∧
      ∀ a i, X a (ι i) = x a i := by
  classical
  let Xm : Matrix (Fin r) (Fin n) K := fun a i => x a i
  let Ym : Matrix (Fin r) (Fin n) K := fun a i => y a i
  have hXmYm : Xm.transpose * Ym = 1 := by
    ext i j
    simpa [Matrix.mul_apply, Xm, Ym] using hdual i j
  let L : (Fin r → K) →ₗ[K] Fin n → K := Xm.transpose.mulVecLin
  have hLY : L.comp Ym.mulVecLin = LinearMap.id := by
    rw [← Matrix.mulVecLin_mul, hXmYm]
    exact Matrix.mulVecLin_one
  have hLsurj : Function.Surjective L := by
    intro z
    refine ⟨Ym.mulVec z, ?_⟩
    exact LinearMap.congr_fun hLY z
  let C := {j : Fin r // j ∉ Set.range ι}
  let er : Fin n ≃ Set.range ι := ι.toEquivRange
  let e : Fin n ⊕ C ≃ Fin r :=
    (Equiv.sumCongr er (Equiv.refl C)).trans
      (Equiv.sumCompl (fun j : Fin r => j ∈ Set.range ι))
  have heinl (i : Fin n) : e (Sum.inl i) = ι i := by
    rfl
  have heinr (c : C) : e (Sum.inr c) = c.1 := by
    rfl
  have hcard : n + Fintype.card C = r := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr e
  have hkerCard : Module.finrank K (LinearMap.ker L) = Fintype.card C := by
    have hrankNull := LinearMap.finrank_range_add_finrank_ker L
    rw [LinearMap.range_eq_top.mpr hLsurj] at hrankNull
    have hrankNull' : n + Module.finrank K (LinearMap.ker L) = r := by
      simpa using hrankNull
    omega
  let ec : (C → K) ≃ₗ[K] LinearMap.ker L :=
    LinearEquiv.ofFinrankEq (C → K) (LinearMap.ker L) (by
      rw [Module.finrank_fintype_fun_eq_card]
      exact hkerCard.symm)
  let pn : (Fin n ⊕ C → K) →ₗ[K] Fin n → K :=
    { toFun := fun z i => z (Sum.inl i)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let pc : (Fin n ⊕ C → K) →ₗ[K] C → K :=
    { toFun := fun z c => z (Sum.inr c)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let g : (Fin n ⊕ C → K) →ₗ[K] Fin r → K :=
    Ym.mulVecLin.comp pn +
      (LinearMap.ker L).subtype.comp (ec.toLinearMap.comp pc)
  have hLg (z : Fin n ⊕ C → K) : L (g z) = pn z := by
    have hfirst : L (Ym.mulVec (pn z)) = pn z := by
      exact LinearMap.congr_fun hLY (pn z)
    change L (Ym.mulVec (pn z) + (ec (pc z)).1) = pn z
    rw [map_add, hfirst, (ec (pc z)).2, add_zero]
  have hginj : Function.Injective g := by
    intro z z' hzz'
    have hn : pn z = pn z' := by
      rw [← hLg z, ← hLg z', hzz']
    have hkval : (ec (pc z)).1 = (ec (pc z')).1 := by
      change Ym.mulVec (pn z) + (ec (pc z)).1 =
        Ym.mulVec (pn z') + (ec (pc z')).1 at hzz'
      rw [hn] at hzz'
      exact add_left_cancel hzz'
    have hc : pc z = pc z' := by
      apply ec.injective
      exact Subtype.ext hkval
    funext s
    rcases s with i | c
    · exact congrFun hn i
    · exact congrFun hc c
  have hgsurj : Function.Surjective g := by
    intro t
    let zker : LinearMap.ker L :=
      ⟨t - Ym.mulVec (L t), by
        have hfirst : L (Ym.mulVec (L t)) = L t := by
          exact LinearMap.congr_fun hLY (L t)
        change L (t - Ym.mulVec (L t)) = 0
        rw [map_sub, hfirst, sub_self]⟩
    refine ⟨fun s => Sum.elim (L t) (ec.symm zker) s, ?_⟩
    change Ym.mulVec (L t) + (ec (ec.symm zker)).1 = t
    rw [ec.apply_symm_apply]
    change Ym.mulVec (L t) + (t - Ym.mulVec (L t)) = t
    abel
  let eg : (Fin n ⊕ C → K) ≃ₗ[K] Fin r → K :=
    LinearEquiv.ofBijective g ⟨hginj, hgsurj⟩
  let re : (Fin r → K) ≃ₗ[K] Fin n ⊕ C → K :=
    { toFun := fun z s => z (e s)
      invFun := fun z j => z (e.symm j)
      left_inv := by intro z; funext j; simp
      right_inv := by intro z; funext s; simp
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let es : (Fin r → K) ≃ₗ[K] Fin r → K := re.trans eg
  let Y : Matrix (Fin r) (Fin r) K := LinearMap.toMatrix' es.toLinearMap
  let X : Matrix (Fin r) (Fin r) K :=
    (LinearMap.toMatrix' es.symm.toLinearMap).transpose
  have hYunit : IsUnit Y := by
    have hunitlin : IsUnit es.toLinearMap := by
      apply isUnit_iff_exists.mpr
      refine ⟨es.symm.toLinearMap, ?_, ?_⟩
      · ext z
        simp
      · ext z
        simp
    simpa [Y] using hunitlin
  have hEinvunit : IsUnit (LinearMap.toMatrix' es.symm.toLinearMap) := by
    have hunitlin : IsUnit es.symm.toLinearMap := by
      apply isUnit_iff_exists.mpr
      refine ⟨es.toLinearMap, ?_, ?_⟩
      · ext z
        simp
      · ext z
        simp
    simpa using hunitlin
  have hXunit : IsUnit X := by
    simpa [X] using hEinvunit
  have hXY : X.transpose * Y = 1 := by
    simp [X, Y, ← LinearMap.toMatrix'_comp]
  have hresingle (i : Fin n) :
      re (Pi.single (ι i) 1) = Pi.single (Sum.inl i) 1 := by
    funext s
    rcases s with j | c
    · simp [re, heinl, Pi.single_apply]
    · have hne : ι i ≠ c.1 := by
        intro hic
        exact c.2 ⟨i, hic⟩
      simp [re, heinr, Pi.single_apply, hne]
  have hYcols (a : Fin r) (i : Fin n) : Y a (ι i) = y a i := by
    simp only [Y, LinearMap.toMatrix'_apply]
    change g (re (Pi.single (ι i) 1)) a = y a i
    rw [hresingle]
    have hpni : pn (Pi.single (Sum.inl i) 1) = Pi.single i 1 := by
      funext j
      simp [pn, Pi.single_apply]
    have hpci : pc (Pi.single (Sum.inl i) 1) = 0 := by
      funext c
      simp [pc, Pi.single_apply]
    change (Ym.mulVec (pn (Pi.single (Sum.inl i) 1)) +
      (ec (pc (Pi.single (Sum.inl i) 1))).1) a = y a i
    rw [hpni, hpci, map_zero]
    simp [Ym, Matrix.mulVec_single_one]
  have hegLeft (t : Fin r → K) (i : Fin n) :
      eg.symm t (Sum.inl i) = L t i := by
    have hz := hLg (eg.symm t)
    change L (eg (eg.symm t)) = pn (eg.symm t) at hz
    rw [eg.apply_symm_apply] at hz
    exact (congrFun hz i).symm
  have hreinv (z : Fin n ⊕ C → K) (i : Fin n) :
      re.symm z (ι i) = z (Sum.inl i) := by
    change z (e.symm (ι i)) = z (Sum.inl i)
    congr 1
    apply e.injective
    simp [heinl]
  have hXcols (a : Fin r) (i : Fin n) : X a (ι i) = x a i := by
    simp only [X, Matrix.transpose_apply, LinearMap.toMatrix'_apply]
    change re.symm (eg.symm (Pi.single a 1)) (ι i) = x a i
    rw [hreinv, hegLeft]
    change (Xm.transpose.mulVec (Pi.single a 1)) i = x a i
    simp [Xm, Matrix.mulVec_single_one]
  exact ⟨X, Y, hXunit, hYunit, hXY, hYcols, hXcols⟩

@[blueprint "lem:rank-decomposition-yields-commuting-extension"
  (statement := /-- Let $K$ be a field, let $n,q,r$ be nonnegative integers, and let
  $T$ be an $n\times n\times(q+2)$ tensor over $K$ with a decomposition
  $T=\sum_{a\in\operatorname{Fin}(r)}u_a\otimes v_a\otimes w_a$. Let
  $c:\operatorname{Fin}(q+2)\to K$ and let $A\in M_n(K)$ be invertible, with
  $A=\sum_k c_kT_k$. Suppose that
  $\alpha_a=\sum_k c_k(w_a)_k$ is nonzero for every
  $a\in\operatorname{Fin}(r)$. Then, for every coordinate embedding
  $\iota:\operatorname{Fin}(n)\hookrightarrow\operatorname{Fin}(r)$, there exists a
  size-$r$ commuting extension of the normalized nonfirst slices of $T$ that is attached to
  the given decomposition, coefficients, and embedding. -/)
  (proof := /-- By
  \cref{def:tensor-decomposition,def:rank-one-tensor,def:tensor-slice}, write the slices as
  $T_k=U^{\mathsf T}D_kV$, where the $a$th diagonal entry of $D_k$ is $(w_a)_k$, and put
  $D_\lambda=\sum_k\lambda_kD_k$. The hypotheses give
  $A=U^{\mathsf T}D_\lambda V$ and make $D_\lambda$ invertible. Set
  $\widetilde U=D_\lambda UA^{-\mathsf T}$. Then
  $\widetilde U^{\mathsf T}V=I_n$. Apply
  \cref{lem:dual-families-extend-to-inverse-matrices} to the columns of $\widetilde U$ and
  $V$: it completes the columns of $V$, in the coordinates prescribed by $\iota$, by a
  basis of $\ker(\widetilde U^{\mathsf T})$, and the corresponding dual completion gives
  invertible $r\times r$ matrices $X,Y$ with $X^{\mathsf T}Y=I_r$ and with the required
  prescribed columns.

  For each normalized nonfirst-slice index $j$, define
  $Z_j=X^{\mathsf T}D_\lambda^{-1}D_{j+2}Y$. These matrices commute because they are
  simultaneously conjugate to diagonal matrices. Their prescribed block is
  $A^{-1}T_{j+2}$, as required by \cref{def:normalized-nonfirst-slices}, and their diagonal
  formula, together with the prescribed columns of $X$ and $Y$, verifies every clause of
  \cref{def:decomposition-attached-commuting-extension}. -/)
  (title := /-- A rank decomposition produces an attached commuting extension -/)
  (latexEnv := "lemma")]
lemma rank_decomposition_yields_commuting_extension
    {K : Type} [Field K] {n q r : ℕ}
    (T : order_three_tensor K n (q + 2))
    (u v : Fin r → Fin n → K) (w : Fin r → Fin (q + 2) → K)
    (hdecomp : tensor_decomposition T u v w)
    (A : Matrix (Fin n) (Fin n) K) (c : Fin (q + 2) → K)
    (hA : A = ∑ k, c k • tensor_slice T k) (hAunit : IsUnit A)
    (hnonzero : ∀ a, (∑ k, c k * w a k) ≠ 0) (ι : Fin n ↪ Fin r) :
    ∃ Z : Fin (q + 1) → Matrix (Fin r) (Fin r) K,
      decomposition_attached_commuting_extension A c T u v w Z ι := by
  classical
  let α : Fin r → K := fun a => ∑ k, c k * w a k
  change T = ∑ a, rank_one_tensor (u a) (v a) (w a) at hdecomp
  have hslice (k : Fin (q + 2)) (i j : Fin n) :
      tensor_slice T k i j = ∑ a, u a i * v a j * w a k := by
    change T i j k = ∑ a, u a i * v a j * w a k
    rw [hdecomp]
    simp [rank_one_tensor]
  have hAentry (i j : Fin n) :
      A i j = ∑ a, u a i * (α a * v a j) := by
    calc
      A i j = (∑ k, c k • tensor_slice T k) i j := by
        exact congrFun (congrFun hA i) j
      _ = ∑ k, c k * tensor_slice T k i j := by
        simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      _ = ∑ k, c k * ∑ a, u a i * v a j * w a k := by
        simp_rw [hslice]
      _ = ∑ a, u a i * (α a * v a j) := by
        simp only [α, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro k hk
        ring
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hAunit
  have hAinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hAdet
  let x : Fin r → Fin n → K :=
    fun a i => α a * ∑ j, u a j * (A⁻¹) i j
  have hdual (i j : Fin n) :
      ∑ a, x a i * v a j = (1 : Matrix (Fin n) (Fin n) K) i j := by
    calc
      ∑ a, x a i * v a j =
          ∑ l, (A⁻¹) i l * ∑ a, u a l * (α a * v a j) := by
        simp only [x, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro l hl
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = ∑ l, (A⁻¹) i l * A l j := by
        simp_rw [hAentry]
      _ = (A⁻¹ * A) i j := by
        rw [Matrix.mul_apply]
      _ = (1 : Matrix (Fin n) (Fin n) K) i j := by
        rw [hAinv]
  rcases dual_families_extend_to_inverse_matrices x v hdual ι with
    ⟨X, Y, hXunit, hYunit, hXY, hYcols, hXcols⟩
  let Z : Fin (q + 1) → Matrix (Fin r) (Fin r) K := fun k =>
    X.transpose * Matrix.diagonal (fun a => w a k.succ / α a) * Y
  have hYX : Y * X.transpose = 1 := mul_eq_one_comm.mp hXY
  refine ⟨Z, hdecomp, hA, hAunit, hnonzero, ?_, X, Y, hXunit, hYunit,
    hXY, hYcols, ?_, ?_⟩
  · constructor
    · intro k l
      change Z k * Z l = Z l * Z k
      have hdiag :
          Matrix.diagonal (fun a => w a k.succ / α a) *
              Matrix.diagonal (fun a => w a l.succ / α a) =
            Matrix.diagonal (fun a => w a l.succ / α a) *
              Matrix.diagonal (fun a => w a k.succ / α a) := by
        rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
        apply congrArg Matrix.diagonal
        funext a
        ring
      change (X.transpose * Matrix.diagonal (fun a => w a k.succ / α a) * Y) *
          (X.transpose * Matrix.diagonal (fun a => w a l.succ / α a) * Y) =
        (X.transpose * Matrix.diagonal (fun a => w a l.succ / α a) * Y) *
          (X.transpose * Matrix.diagonal (fun a => w a k.succ / α a) * Y)
      calc
        _ = (X.transpose * Matrix.diagonal (fun a => w a k.succ / α a)) *
              (Y * X.transpose) *
              (Matrix.diagonal (fun a => w a l.succ / α a) * Y) := by
            simp only [mul_assoc]
        _ = X.transpose *
              (Matrix.diagonal (fun a => w a k.succ / α a) *
                Matrix.diagonal (fun a => w a l.succ / α a)) * Y := by
            rw [hYX]
            simp only [mul_one, one_mul, mul_assoc]
        _ = X.transpose *
              (Matrix.diagonal (fun a => w a l.succ / α a) *
                Matrix.diagonal (fun a => w a k.succ / α a)) * Y := by
            rw [hdiag]
        _ = (X.transpose * Matrix.diagonal (fun a => w a l.succ / α a)) *
              (Y * X.transpose) *
              (Matrix.diagonal (fun a => w a k.succ / α a) * Y) := by
            rw [hYX]
            simp only [mul_one, one_mul, mul_assoc]
        _ = _ := by
            simp only [mul_assoc]
    · intro k i j
      change Z k (ι i) (ι j) =
        (A⁻¹ * tensor_slice T k.succ) i j
      calc
        Z k (ι i) (ι j) =
            ∑ a, X a (ι i) * (w a k.succ / α a) * Y a (ι j) := by
          change ((X.transpose * Matrix.diagonal (fun a => w a k.succ / α a)) * Y)
              (ι i) (ι j) = _
          rw [Matrix.mul_apply]
          apply Finset.sum_congr rfl
          intro a ha
          rw [Matrix.mul_diagonal]
          rfl
        _ = ∑ a, (∑ l, u a l * (A⁻¹) i l) * w a k.succ * v a j := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [hXcols, hYcols]
          have ha0 : α a ≠ 0 := by
            simpa [α] using hnonzero a
          change (α a * ∑ l, u a l * (A⁻¹) i l) *
              (w a k.succ / α a) * v a j =
            (∑ l, u a l * (A⁻¹) i l) * w a k.succ * v a j
          field_simp [ha0]
          <;> ring
        _ = ∑ l, (A⁻¹) i l * ∑ a, u a l * v a j * w a k.succ := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro l hl
          apply Finset.sum_congr rfl
          intro a ha
          ring
        _ = ∑ l, (A⁻¹) i l * tensor_slice T k.succ l j := by
          simp_rw [hslice]
        _ = (A⁻¹ * tensor_slice T k.succ) i j := by
          rw [Matrix.mul_apply]
  · intro a i
    exact hXcols a i
  · intro k
    simp [Z, α]

@[blueprint "lem:normalized-successor-coordinates-injective"
  (statement := /-- Let $K$ be a field, let $q,r$ be nonnegative integers, let
  $c\colon\operatorname{Fin}(q+2)\to K$, and let
  $(w_a)_{a\in\operatorname{Fin}(r)}$ be a family in $K^{q+2}$. Suppose that $c_0\ne0$,
  every scalar $\alpha_a=\sum_t c_t(w_a)_t$ is nonzero, and the vectors $w_a$ are
  pairwise linearly independent. Then the map
  $a\mapsto((w_a)_{k+1}/\alpha_a)_{k\in\operatorname{Fin}(q+1)}$ is injective. -/)
  (proof := /-- Suppose that the normalized successor-coordinate vectors belonging to
  $a$ and $b$ are equal. Since $\alpha_a$ and $\alpha_b$ are nonzero, cross-multiplication
  gives $\alpha_b(w_a)_{k+1}=\alpha_a(w_b)_{k+1}$ for every successor coordinate.
  Expanding the two normalization sums shows that the difference between
  $\alpha_b(w_a)_0$ and $\alpha_a(w_b)_0$, multiplied by $c_0$, is zero; hence the same
  equality holds in coordinate zero because $c_0\ne0$. Thus
  $\alpha_bw_a=\alpha_aw_b$. If $a\ne b$, the defining linear independence in
  \cref{def:pairwise-linearly-independent} forces both coefficients to vanish, contrary
  to the normalization hypotheses. Therefore $a=b$. -/)
  (title := /-- Normalized successor coordinates separate pairwise independent vectors -/)
  (latexEnv := "lemma")]
lemma normalized_successor_coordinates_injective
    {K : Type} [Field K] {q r : ℕ}
    (c : Fin (q + 2) → K) (w : Fin r → Fin (q + 2) → K)
    (hc : c 0 ≠ 0) (hnonzero : ∀ a, (∑ t, c t * w a t) ≠ 0)
    (hpair : pairwise_linearly_independent w) :
    Function.Injective (fun a => fun k : Fin (q + 1) =>
      w a k.succ / ∑ t, c t * w a t) := by
  intro a b habnorm
  have hsucc (k : Fin (q + 1)) :
      (∑ t, c t * w b t) * w a k.succ =
        (∑ t, c t * w a t) * w b k.succ := by
    have hk := congr_fun habnorm k
    field_simp [hnonzero a, hnonzero b] at hk
    simpa [mul_comm] using hk
  have hweighted :
      ∑ k : Fin (q + 1), c k.succ * ((∑ t, c t * w b t) * w a k.succ) =
        ∑ k : Fin (q + 1), c k.succ * ((∑ t, c t * w a t) * w b k.succ) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hsucc k]
  have hzero :
      (∑ t, c t * w b t) * w a 0 =
        (∑ t, c t * w a t) * w b 0 := by
    apply mul_left_cancel₀ hc
    calc
      c 0 * ((∑ t, c t * w b t) * w a 0) =
          (∑ t, c t * w b t) * (∑ t, c t * w a t) -
            ∑ k : Fin (q + 1),
              c k.succ * ((∑ t, c t * w b t) * w a k.succ) := by
                rw [show (∑ t, c t * w a t) =
                  c 0 * w a 0 + ∑ k : Fin (q + 1), c k.succ * w a k.succ from
                    Fin.sum_univ_succ _]
                rw [mul_add, Finset.mul_sum]
                ring_nf
      _ = (∑ t, c t * w a t) * (∑ t, c t * w b t) -
            ∑ k : Fin (q + 1),
              c k.succ * ((∑ t, c t * w a t) * w b k.succ) := by
                rw [hweighted]
                ring_nf
      _ = c 0 * ((∑ t, c t * w a t) * w b 0) := by
                rw [show (∑ t, c t * w b t) =
                  c 0 * w b 0 + ∑ k : Fin (q + 1), c k.succ * w b k.succ from
                    Fin.sum_univ_succ _]
                rw [mul_add, Finset.mul_sum]
                ring_nf
  have hall (k : Fin (q + 2)) :
      (∑ t, c t * w b t) * w a k =
        (∑ t, c t * w a t) * w b k := by
    refine Fin.cases hzero (fun k => ?_) k
    exact hsucc k
  by_contra hab
  have hfamily : (fun t : Fin 2 => if t = 0 then w a else w b) = ![w a, w b] := by
    funext t
    fin_cases t <;> simp
  have hlin := hpair hab
  rw [hfamily] at hlin
  have hrelation :
      (-(∑ t, c t * w b t)) • w a + (∑ t, c t * w a t) • w b = 0 := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    rw [neg_mul, hall k]
    ring
  have hcoeff := (LinearIndependent.pair_iff.mp hlin)
    (-(∑ t, c t * w b t)) (∑ t, c t * w a t) hrelation
  exact hnonzero b (neg_eq_zero.mp hcoeff.1)

@[blueprint "lem:normalized-successor-coordinates-determine-full-vector"
  (statement := /-- Let $K$ be a field, let $q$ be a nonnegative integer, let
  $c\colon\operatorname{Fin}(q+2)\to K$ satisfy $c_0\ne0$, and let $x,y\in K^{q+2}$.
  Put $\alpha_x=\sum_t c_tx_t$ and $\alpha_y=\sum_t c_ty_t$, and suppose that both
  scalars are nonzero. If $x_{k+1}/\alpha_x=y_{k+1}/\alpha_y$ for every
  $k\in\operatorname{Fin}(q+1)$, then
  $\alpha_xy_t=\alpha_yx_t$ for every $t\in\operatorname{Fin}(q+2)$. -/)
  (proof := /-- Cross-multiplication gives the claimed equality in every successor
  coordinate. Multiply these equalities by the corresponding coefficients $c_{k+1}$ and
  sum. After expanding the definitions of $\alpha_x$ and $\alpha_y$, all successor terms
  cancel and leave
  $c_0(\alpha_xy_0-\alpha_yx_0)=0$. Since $c_0\ne0$, the equality also holds at coordinate
  zero, and hence at every coordinate. -/)
  (title := /-- Normalized successor coordinates determine the full scaled vector -/)
  (latexEnv := "lemma")]
lemma normalized_successor_coordinates_determine_full_vector
    {K : Type} [Field K] {q : ℕ} (c : Fin (q + 2) → K)
    (x y : Fin (q + 2) → K) (hc : c 0 ≠ 0)
    (hx : (∑ t, c t * x t) ≠ 0) (hy : (∑ t, c t * y t) ≠ 0)
    (hnorm : ∀ k : Fin (q + 1),
      x k.succ / (∑ t, c t * x t) = y k.succ / (∑ t, c t * y t)) :
    ∀ t, (∑ s, c s * x s) * y t = (∑ s, c s * y s) * x t := by
  have hsucc (k : Fin (q + 1)) :
      (∑ t, c t * x t) * y k.succ = (∑ t, c t * y t) * x k.succ := by
    have hk := hnorm k
    field_simp [hx, hy] at hk
    symm
    simpa [mul_comm] using hk
  have hweighted :
      ∑ k : Fin (q + 1), c k.succ * ((∑ t, c t * x t) * y k.succ) =
        ∑ k : Fin (q + 1), c k.succ * ((∑ t, c t * y t) * x k.succ) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hsucc k]
  have hzero :
      (∑ t, c t * x t) * y 0 = (∑ t, c t * y t) * x 0 := by
    apply mul_left_cancel₀ hc
    calc
      c 0 * ((∑ t, c t * x t) * y 0) =
          (∑ t, c t * x t) * (∑ t, c t * y t) -
            ∑ k : Fin (q + 1), c k.succ * ((∑ t, c t * x t) * y k.succ) := by
                rw [show (∑ t, c t * y t) =
                  c 0 * y 0 + ∑ k : Fin (q + 1), c k.succ * y k.succ from
                    Fin.sum_univ_succ _]
                rw [mul_add, Finset.mul_sum]
                ring_nf
      _ = (∑ t, c t * y t) * (∑ t, c t * x t) -
            ∑ k : Fin (q + 1), c k.succ * ((∑ t, c t * y t) * x k.succ) := by
                rw [hweighted]
                ring
      _ = c 0 * ((∑ t, c t * y t) * x 0) := by
                rw [show (∑ t, c t * x t) =
                  c 0 * x 0 + ∑ k : Fin (q + 1), c k.succ * x k.succ from
                    Fin.sum_univ_succ _]
                rw [mul_add, Finset.mul_sum]
                ring_nf
  intro t
  refine Fin.cases hzero (fun k => ?_) t
  exact hsucc k

@[blueprint "lem:block-conjugacy-identifies-rank-one-terms"
  (statement := /-- Let $K$ be a field, let $n,q,r$ be nonnegative integers, and let $T$ be
  an $n\times n\times(q+2)$ tensor over $K$. Let
  $(u_a,v_a,w_a)_{a\in\operatorname{Fin}(r)}$ and
  $(u'_a,v'_a,w'_a)_{a\in\operatorname{Fin}(r)}$ be two length-$r$ decompositions of $T$.
  Fix a matrix $A\in M_n(K)$, coefficients
  $c\colon\operatorname{Fin}(q+2)\to K$, an embedding
  $\iota\colon\operatorname{Fin}(n)\hookrightarrow\operatorname{Fin}(r)$, and two
  families $Z,Z'$ of $r\times r$ matrices indexed by $\operatorname{Fin}(q+1)$. Suppose
  that $Z$ and $Z'$ are decomposition-attached commuting extensions of the respective
  decompositions relative to the same data $(A,c,T,\iota)$. If $c_0\ne0$, the family
  $(w_a)_a$ is pairwise linearly independent, and $Z$ and $Z'$ are equivalent along
  $\iota$ by a block-preserving simultaneous conjugacy, then there is a permutation
  $\sigma$ of $\operatorname{Fin}(r)$ such that
  \[
    u'_a\otimes v'_a\otimes w'_a
      =u_{\sigma(a)}\otimes v_{\sigma(a)}\otimes w_{\sigma(a)}
  \]
  for every $a\in\operatorname{Fin}(r)$. -/)
  (proof := /-- Put $\alpha_a=\sum_k c_k(w_a)_k$ and
  $\alpha'_a=\sum_k c_k(w'_a)_k$. By
  \cref{def:decomposition-attached-commuting-extension}, choose invertible matrices
  $X,Y,X',Y'$ satisfying $X^{\mathsf T}Y=X'^{\mathsf T}Y'=I_r$ and realizing $Z,Z'$ as
  the diagonal models with joint eigenvalues
  $((w_a)_{j+1}/\alpha_a)_j$ and $((w'_a)_{j+1}/\alpha'_a)_j$. Let $P$ be the invertible
  block-preserving conjugator supplied by
  \cref{def:commuting-extension-equivalent}, and set
  $Q=YPX'^{\mathsf T}$. The conjugacy relation implies
  \[
    \operatorname{diag}((w_a)_{j+1}/\alpha_a)_a\,Q
      =Q\,\operatorname{diag}((w'_a)_{j+1}/\alpha'_a)_a
  \]
  for every $j$. The matrix $Q$ is invertible, so each of its columns has a nonzero entry.
  Choose $\sigma(a)$ with $Q_{\sigma(a),a}\ne0$. The displayed intertwining identity
  shows that the normalized successor-coordinate vectors of $w_{\sigma(a)}$ and $w'_a$
  agree. By \cref{lem:normalized-successor-coordinates-injective}, any other nonzero entry
  in column $a$ must lie in row $\sigma(a)$. Applying $Q^{-1}Q=I_r$ to two columns shows
  that $\sigma$ is injective; since $\operatorname{Fin}(r)$ is finite, it is a permutation.

  The identities $PX'^{\mathsf T}=X^{\mathsf T}Q$ and $QY'=YP$, together with the row and
  column conditions in \cref{def:coordinate-block-preserving}, give, with
  $d_a=Q_{\sigma(a),a}$,
  \[
    X'_{a,\iota(i)}=d_aX_{\sigma(a),\iota(i)},\qquad
    d_aY'_{a,\iota(i)}=Y_{\sigma(a),\iota(i)}.
  \]
  Substituting the prescribed columns from
  \cref{def:decomposition-attached-commuting-extension} and cancelling the invertible
  matrix $A^{-1}$ yields
  $\alpha'_au'_a=d_a\alpha_{\sigma(a)}u_{\sigma(a)}$ and
  $d_av'_a=v_{\sigma(a)}$. The matched normalized successor coordinates and
  \cref{lem:normalized-successor-coordinates-determine-full-vector} give
  $\alpha_{\sigma(a)}w'_a=\alpha'_aw_{\sigma(a)}$. All three scalars
  $d_a,\alpha_{\sigma(a)},\alpha'_a$ are nonzero. Multiplying the three coordinatewise
  relations and cancelling them proves
  $u'_a\otimes v'_a\otimes w'_a
    =u_{\sigma(a)}\otimes v_{\sigma(a)}\otimes w_{\sigma(a)}$ for every $a$. -/)
  (title := /-- Block conjugacy recovers the tensor terms -/)
  (latexEnv := "lemma")]
lemma block_conjugacy_identifies_rank_one_terms
    {K : Type} [Field K] {n q r : ℕ}
    (T : order_three_tensor K n (q + 2))
    (u v u' v' : Fin r → Fin n → K)
    (w w' : Fin r → Fin (q + 2) → K)
    (A : Matrix (Fin n) (Fin n) K) (c : Fin (q + 2) → K)
    (ι : Fin n ↪ Fin r)
    (Z Z' : Fin (q + 1) → Matrix (Fin r) (Fin r) K)
    (hattach : decomposition_attached_commuting_extension A c T u v w Z ι)
    (hattach' : decomposition_attached_commuting_extension A c T u' v' w' Z' ι)
    (hc : c 0 ≠ 0) (hpair : pairwise_linearly_independent w)
    (hequiv : commuting_extension_equivalent ι Z Z') :
    ∃ σ : Equiv.Perm (Fin r), ∀ a,
      rank_one_tensor (u' a) (v' a) (w' a) =
        rank_one_tensor (u (σ a)) (v (σ a)) (w (σ a)) := by
  rcases hattach with
    ⟨hdec, hA, hAunit, hα, hcomm, X, Y, hXunit, hYunit, hXY, hYι, hXι, hZ⟩
  rcases hattach' with
    ⟨hdec', hA', hAunit', hα', hcomm', X', Y', hXunit', hYunit', hXY', hYι', hXι', hZ'⟩
  rcases hequiv with ⟨P, hPunit, hPblock, hconj⟩
  have hYX : Y * X.transpose = 1 := by
    apply hYunit.mul_right_cancel
    rw [Matrix.mul_assoc, hXY]
    simp
  have hYX' : Y' * X'.transpose = 1 := by
    apply hYunit'.mul_right_cancel
    rw [Matrix.mul_assoc, hXY']
    simp
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPunit
  have hPPinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPdet
  have hZP (k : Fin (q + 1)) : Z k * P = P * Z' k := by
    calc
      Z k * P = (P * P⁻¹) * (Z k * P) := by rw [hPPinv]; simp
      _ = P * (P⁻¹ * Z k * P) := by simp [Matrix.mul_assoc]
      _ = P * Z' k := by rw [hconj k]
  let D : Fin (q + 1) → Matrix (Fin r) (Fin r) K := fun k =>
    Matrix.diagonal (fun a => w a k.succ / ∑ t, c t * w a t)
  let D' : Fin (q + 1) → Matrix (Fin r) (Fin r) K := fun k =>
    Matrix.diagonal (fun a => w' a k.succ / ∑ t, c t * w' a t)
  let Q : Matrix (Fin r) (Fin r) K := Y * P * X'.transpose
  have hYZ (k : Fin (q + 1)) : Y * Z k = D k * Y := by
    rw [hZ k]
    simp [D, ← Matrix.mul_assoc, hYX]
  have hZX' (k : Fin (q + 1)) : Z' k * X'.transpose = X'.transpose * D' k := by
    rw [hZ' k]
    simp [D', Matrix.mul_assoc, hYX']
  have hinter (k : Fin (q + 1)) : D k * Q = Q * D' k := by
    calc
      D k * Q = (D k * Y) * P * X'.transpose := by simp [Q, Matrix.mul_assoc]
      _ = (Y * Z k) * P * X'.transpose := by rw [hYZ k]
      _ = Y * (Z k * P) * X'.transpose := by simp [Matrix.mul_assoc]
      _ = Y * (P * Z' k) * X'.transpose := by rw [hZP k]
      _ = (Y * P) * (Z' k * X'.transpose) := by simp [Matrix.mul_assoc]
      _ = (Y * P) * (X'.transpose * D' k) := by rw [hZX' k]
      _ = Q * D' k := by simp [Q, Matrix.mul_assoc]
  have hXtunit' : IsUnit X'.transpose := (Matrix.isUnit_transpose X').2 hXunit'
  have hQunit : IsUnit Q := (hYunit.mul hPunit).mul hXtunit'
  rcases isUnit_iff_exists.mp hQunit with ⟨R, hQR, hRQ⟩
  have hcol (a : Fin r) : ∃ b, Q b a ≠ 0 := by
    by_contra h
    push Not at h
    have haa := congr_fun (congr_fun hRQ a) a
    simp [Matrix.mul_apply, h] at haa
  choose σ hσ using hcol
  have hQmatch {b a : Fin r} (hba : Q b a ≠ 0) (k : Fin (q + 1)) :
      w b k.succ / (∑ t, c t * w b t) =
        w' a k.succ / (∑ t, c t * w' a t) := by
    have hi := congr_fun (congr_fun (hinter k) b) a
    have hi' :
        (w b k.succ / (∑ t, c t * w b t)) * Q b a =
          Q b a * (w' a k.succ / (∑ t, c t * w' a t)) := by
      simpa only [D, D', Matrix.diagonal_mul, Matrix.mul_diagonal] using hi
    exact mul_right_cancel₀ hba (by simpa [mul_comm] using hi')
  have hmatch (a : Fin r) (k : Fin (q + 1)) :
      w (σ a) k.succ / (∑ t, c t * w (σ a) t) =
        w' a k.succ / (∑ t, c t * w' a t) :=
    hQmatch (hσ a) k
  have hnormInjective := normalized_successor_coordinates_injective c w hc hα hpair
  have hQzero (b a : Fin r) (hneq : b ≠ σ a) : Q b a = 0 := by
    by_contra hba
    apply hneq
    apply hnormInjective
    funext k
    exact (hQmatch hba k).trans (hmatch a k).symm
  have hQsupport (b a : Fin r) :
      Q b a = if b = σ a then Q (σ a) a else 0 := by
    by_cases hba : b = σ a
    · subst b
      simp
    · rw [hQzero b a hba]
      simp [hba]
  have hRQentry (i a : Fin r) :
      R i (σ a) * Q (σ a) a = if i = a then 1 else 0 := by
    have hi := congr_fun (congr_fun hRQ i) a
    rw [Matrix.mul_apply] at hi
    have hsum :
        ∑ x, R i x * Q x a = R i (σ a) * Q (σ a) a := by
      apply Fintype.sum_eq_single (σ a)
      intro b hba
      rw [hQzero b a hba, mul_zero]
    rw [hsum] at hi
    simpa only [Matrix.one_apply] using hi
  have hσinjective : Function.Injective σ := by
    intro a b hab
    by_contra hne
    have hone := hRQentry a a
    have hzero := hRQentry a b
    have hone' : R a (σ a) * Q (σ a) a = 1 := by
      simpa only [if_pos rfl, if_true] using hone
    have hzero' : R a (σ b) * Q (σ b) b = 0 := by
      simpa only [if_neg hne] using hzero
    have hR : R a (σ a) ≠ 0 := by
      intro hRa
      rw [hRa, zero_mul] at hone'
      exact zero_ne_one hone'
    have hR' : R a (σ b) ≠ 0 := by simpa [hab] using hR
    exact (mul_ne_zero hR' (hσ b)) hzero'
  let σe : Equiv.Perm (Fin r) := Equiv.ofBijective σ
    ⟨hσinjective, Finite.surjective_of_injective hσinjective⟩
  have hPX : P * X'.transpose = X.transpose * Q := by
    simp [Q, ← Matrix.mul_assoc, hXY]
  have hQY : Q * Y' = Y * P := by
    simp [Q, Matrix.mul_assoc, hXY']
  have hXrel (a : Fin r) (i : Fin n) :
      X' a (ι i) = X (σ a) (ι i) * Q (σ a) a := by
    have hi := congr_fun (congr_fun hPX (ι i)) a
    rw [Matrix.mul_apply, Matrix.mul_apply] at hi
    have hleft :
        ∑ x, P (ι i) x * X'.transpose x a = X' a (ι i) := by
      calc
        ∑ x, P (ι i) x * X'.transpose x a =
            P (ι i) (ι i) * X'.transpose (ι i) a := by
          apply Fintype.sum_eq_single (ι i)
          intro b hbi
          rw [hPblock.1 i b]
          simp [hbi.symm]
        _ = X' a (ι i) := by simp [hPblock.1]
    have hright :
        ∑ x, X.transpose (ι i) x * Q x a = X (σ a) (ι i) * Q (σ a) a := by
      apply Fintype.sum_eq_single (σ a)
      intro b hba
      rw [hQzero b a hba, mul_zero]
    rw [hleft, hright] at hi
    exact hi
  have hQrowzero (a b : Fin r) (hba : b ≠ a) : Q (σ a) b = 0 := by
    apply hQzero
    exact hσinjective.ne hba.symm
  have hYrel (a : Fin r) (i : Fin n) :
      Q (σ a) a * Y' a (ι i) = Y (σ a) (ι i) := by
    have hi := congr_fun (congr_fun hQY (σ a)) (ι i)
    rw [Matrix.mul_apply, Matrix.mul_apply] at hi
    have hleft :
        ∑ x, Q (σ a) x * Y' x (ι i) = Q (σ a) a * Y' a (ι i) := by
      apply Fintype.sum_eq_single a
      intro b hba
      rw [hQrowzero a b hba, zero_mul]
    have hright :
        ∑ x, Y (σ a) x * P x (ι i) = Y (σ a) (ι i) := by
      calc
        ∑ x, Y (σ a) x * P x (ι i) =
            Y (σ a) (ι i) * P (ι i) (ι i) := by
          apply Fintype.sum_eq_single (ι i)
          intro b hbi
          rw [hPblock.2 i b]
          simp [hbi]
        _ = Y (σ a) (ι i) := by simp [hPblock.2]
    rw [hleft, hright] at hi
    exact hi
  have hAinvrel (a : Fin r) :
      Matrix.mulVec (A⁻¹) (fun j => (∑ t, c t * w' a t) * u' a j) =
        Matrix.mulVec (A⁻¹)
          (fun j => (Q (σ a) a * (∑ t, c t * w (σ a) t)) * u (σ a) j) := by
    funext i
    have hi := hXrel a i
    rw [hXι' a i, hXι (σ a) i] at hi
    rw [Matrix.mulVec, Matrix.mulVec]
    calc
      ∑ j, A⁻¹ i j * ((∑ t, c t * w' a t) * u' a j) =
          (∑ t, c t * w' a t) * ∑ j, u' a j * A⁻¹ i j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ((∑ t, c t * w (σ a) t) * ∑ j, u (σ a) j * A⁻¹ i j) *
          Q (σ a) a := hi
      _ = ∑ j, A⁻¹ i j *
          ((Q (σ a) a * (∑ t, c t * w (σ a) t)) * u (σ a) j) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hAunit
  have hAAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hAdet
  have hfactor (a : Fin r) :
      (fun j => (∑ t, c t * w' a t) * u' a j) =
        (fun j => (Q (σ a) a * (∑ t, c t * w (σ a) t)) * u (σ a) j) := by
    have hi := congrArg (fun z => Matrix.mulVec A z) (hAinvrel a)
    simpa [Matrix.mulVec_mulVec, hAAinv] using hi
  have hu (a : Fin r) (i : Fin n) :
      (∑ t, c t * w' a t) * u' a i =
        (Q (σ a) a * (∑ t, c t * w (σ a) t)) * u (σ a) i :=
    congr_fun (hfactor a) i
  have hv (a : Fin r) (i : Fin n) :
      Q (σ a) a * v' a i = v (σ a) i := by
    simpa [hYι', hYι] using hYrel a i
  have hw (a : Fin r) (k : Fin (q + 2)) :
      (∑ t, c t * w (σ a) t) * w' a k =
        (∑ t, c t * w' a t) * w (σ a) k :=
    normalized_successor_coordinates_determine_full_vector c (w (σ a)) (w' a)
      hc (hα (σ a)) (hα' a) (hmatch a) k
  refine ⟨σe, ?_⟩
  intro a
  funext i j k
  change u' a i * v' a j * w' a k =
    u (σ a) i * v (σ a) j * w (σ a) k
  have hui := hu a i
  have hvj := hv a j
  have hwk := hw a k
  have huexp :
      u' a i =
        ((Q (σ a) a * (∑ t, c t * w (σ a) t)) * u (σ a) i) /
          (∑ t, c t * w' a t) := by
    apply (eq_div_iff (hα' a)).2
    simpa [mul_comm] using hui
  have hvexp : v' a j = v (σ a) j / Q (σ a) a := by
    apply (eq_div_iff (hσ a)).2
    simpa [mul_comm] using hvj
  have hwexp :
      w' a k = ((∑ t, c t * w' a t) * w (σ a) k) /
        (∑ t, c t * w (σ a) t) := by
    apply (eq_div_iff (hα (σ a))).2
    simpa [mul_comm] using hwk
  rw [huexp, hvexp, hwexp]
  field_simp [hσ a, hα (σ a), hα' a]

@[blueprint "lem:rank-minimal-decomposition-commuting-extension"
  (statement := /-- Let $K$ be an infinite field. Suppose that an
  $n\times n\times(q+2)$ tensor $T$ has rank $r$ and that a displayed length-$r$
  decomposition satisfies the tensor uniqueness hypotheses. For every second length-$r$
  decomposition of $T$, there exist an invertible matrix $A$ in the slice span, an embedding
  $\iota\colon\operatorname{Fin}(n)\hookrightarrow\operatorname{Fin}(r)$, and two
  size-$r$ commuting extensions $Z,Z'$ of the normalized nonfirst slices along $\iota$.
  The normalized nonfirst slices satisfy the commuting-extension uniqueness hypothesis,
  and, if $Z$ and $Z'$ are equivalent along $\iota$ by a block-preserving simultaneous
  conjugacy, then a permutation of $\operatorname{Fin}(r)$ identifies the rank-one tensor
  terms of the second decomposition with those of the displayed decomposition. -/)
  (proof := /-- Fix the second decomposition. By
  \cref{lem:generic-normalization-preserves-commutator-dimensions}, choose a common
  invertible slice normalization $A=\sum_k\lambda_kT_k$, a coordinate embedding $\iota$,
  and coefficients $\lambda$ for which the quantified commutator-dimension hypotheses
  persist, $\lambda_0\ne0$, and every normalization scalar for both decompositions is
  nonzero. Apply \cref{lem:rank-decomposition-yields-commuting-extension} to the displayed
  decomposition and to the competing decomposition, using the same $A$, $\lambda$, and
  $\iota$. This gives two size-$r$ commuting extensions attached to the respective
  decompositions.

  Retain the invertible slice-span membership and the commuting-extension dimension
  hypotheses supplied by the generic-normalization lemma. If the two extensions are
  block-preservingly equivalent, then
  \cref{lem:block-conjugacy-identifies-rank-one-terms} applies to their attachment data,
  the nonzero coefficient $\lambda_0$, and the pairwise linear independence contained in
  the tensor uniqueness hypotheses. It yields a permutation identifying every competing
  rank-one term with the corresponding displayed term, which is the final asserted
  implication. -/)
  (title := /-- Minimal decompositions produce comparable commuting extensions -/)
  (latexEnv := "lemma")]
lemma rank_minimal_decomposition_commuting_extension {K : Type} [Field K] [Infinite K]
    {n q r : ℕ} (T : order_three_tensor K n (q + 2))
    (u v : Fin r → Fin n → K) (w : Fin r → Fin (q + 2) → K)
    (h : tensor_uniqueness_hypotheses T u v w) (hrank : has_tensor_rank T r) :
    ∀ (u' v' : Fin r → Fin n → K) (w' : Fin r → Fin (q + 2) → K),
      tensor_decomposition T u' v' w' →
        ∃ (A : Matrix (Fin n) (Fin n) K) (ι : Fin n ↪ Fin r)
          (Z Z' : Fin (q + 1) → Matrix (Fin r) (Fin r) K),
          A ∈ tensor_slice_span T ∧ IsUnit A ∧
          commuting_extension_uniqueness_hypothesis r (normalized_nonfirst_slices A T) ∧
          commuting_extension (normalized_nonfirst_slices A T) Z ι ∧
          commuting_extension (normalized_nonfirst_slices A T) Z' ι ∧
          (commuting_extension_equivalent ι Z Z' →
            ∃ σ : Equiv.Perm (Fin r), ∀ a,
              rank_one_tensor (u' a) (v' a) (w' a) =
              rank_one_tensor (u (σ a)) (v (σ a)) (w (σ a))) := by
  intro u' v' w' hdecomp'
  rcases generic_normalization_preserves_commutator_dimensions
      T u v w h hrank u' v' w' hdecomp' with
    ⟨A, c, ι, hAspan, hAunit, hAc, hc0, huniq, hnonzero, hnonzero'⟩
  rcases rank_decomposition_yields_commuting_extension
      T u v w h.2.1 A c hAc hAunit hnonzero ι with
    ⟨Z, hattach⟩
  rcases rank_decomposition_yields_commuting_extension
      T u' v' w' hdecomp' A c hAc hAunit hnonzero' ι with
    ⟨Z', hattach'⟩
  refine
    ⟨A, ι, Z, Z', hAspan, hAunit, huniq, hattach.2.2.2.2.1,
      hattach'.2.2.2.2.1, ?_⟩
  exact fun hequiv =>
    block_conjugacy_identifies_rank_one_terms
      T u v u' v' w w' A c ι Z Z' hattach hattach' hc0 h.2.2.1 hequiv

@[blueprint "lem:commuting-extension-determines-tensor-terms"
  (statement := /-- Let $K$ be an infinite field and let $p=q+2\geq4$. If a displayed
  length-$r$ decomposition of an $n\times n\times p$ tensor satisfies the tensor uniqueness
  hypotheses and the tensor has rank $r$, then every second length-$r$ decomposition has
  the same rank-one terms after a permutation. -/)
  (proof := /-- Fix a competing length-$r$ decomposition. By
  \cref{lem:rank-minimal-decomposition-commuting-extension}, choose a common normalization
  and the two associated size-$r$ commuting extensions along one coordinate embedding.
  Their normalized matrix family satisfies the quantified hypotheses $H_{0lm}$. Since
  $q\geq2$, \cref{lem:commuting-extension-uniqueness} makes the two extensions equivalent
  through a conjugator which preserves that prescribed block. The final clause of
  \cref{lem:rank-minimal-decomposition-commuting-extension} converts this block-preserving
  equivalence into a permutation identifying every competing rank-one term with the
  corresponding displayed term. Since the competing decomposition was arbitrary, this is
  precisely essential uniqueness. -/)
  (title := /-- Commuting-extension uniqueness identifies tensor terms -/)
  (latexEnv := "lemma")]
lemma commuting_extension_determines_tensor_terms {K : Type} [Field K] [Infinite K]
    {n q r : ℕ} (T : order_three_tensor K n (q + 2))
    (u v : Fin r → Fin n → K) (w : Fin r → Fin (q + 2) → K)
    (hq : 2 ≤ q)
    (h : tensor_uniqueness_hypotheses T u v w) (hrank : has_tensor_rank T r) :
    essentially_unique_decomposition T u v w := by
  intro u' v' w' hdecomp'
  rcases rank_minimal_decomposition_commuting_extension
      T u v w h hrank u' v' w' hdecomp' with
    ⟨A, ι, Z, Z', _, _, huniq, hZ, hZ', hterms⟩
  apply hterms
  apply commuting_extension_uniqueness (normalized_nonfirst_slices A T) hq huniq <;>
    assumption

@[blueprint "lem:tensor-rank-from-uniqueness-hypotheses"
  (statement := /-- Let $K$ be a field, let $n,q,r$ be nonnegative integers with $2\leq q$,
  and set $p=q+2$. Let
  $T=\sum_{a=1}^r u_a\otimes v_a\otimes w_a$ be a tensor of format $n\times n\times p$.
  Assume that the $w_a$ are pairwise linearly independent, that the span of the slices of
  $T$ contains an invertible matrix, and that there is an invertible matrix $A$ in this span
  such that, for every $2\leq l\leq p-1$, there is an $m\notin\{1,l\}$ for which
  $(H_{1lm})$ holds for $(A^{-1}T_2,\ldots,A^{-1}T_p)$. Then $T$ has tensor rank $r$.
  -/)
  (proof := /-- The displayed equality in \cref{def:tensor-uniqueness-hypotheses} supplies a
  decomposition of length $r$. Let a decomposition of $T$ of arbitrary length $s$ be given.
  By \cref{lem:strassen-rank-lower-bound}, its length satisfies $r\leq s$. Thus the displayed
  decomposition realizes the minimum among all finite rank-one decompositions, which is
  exactly the assertion that $T$ has rank $r$ in the sense of \cref{def:has-tensor-rank}. -/)
  (title := /-- Rank under the commuting-extension hypotheses -/)
  (latexEnv := "lemma")]
lemma tensor_rank_from_uniqueness_hypotheses {K : Type} [Field K] {n q r : ℕ}
    (T : order_three_tensor K n (q + 2))
    (u v : Fin r → Fin n → K) (w : Fin r → Fin (q + 2) → K)
    (hq : 2 ≤ q)
    (h : tensor_uniqueness_hypotheses T u v w) : has_tensor_rank T r := by
  exact ⟨⟨u, v, w, h.2.1⟩,
    fun s u' v' w' hdecomp' =>
      strassen_rank_lower_bound T u v w hq h u' v' w' hdecomp'⟩

@[blueprint "lem:essential-uniqueness-from-uniqueness-hypotheses"
  (statement := /-- Let $K$ be an infinite field, let $p=q+2\geq4$, and let
  $T=\sum_{a=1}^r u_a\otimes v_a\otimes w_a$ be a tensor of format $n\times n\times p$.
  Assume that the $w_a$ are pairwise linearly independent, that the slice span contains an
  invertible matrix, and that an invertible matrix $A$ in this span makes the normalized
  nonfirst slices satisfy the quantified hypotheses $(H_{1lm})$. Then the displayed
  decomposition is essentially unique up to permutation of its rank-one terms. -/)
  (proof := /-- By \cref{lem:tensor-rank-from-uniqueness-hypotheses}, $T$ has exact rank
  $r$. Apply \cref{lem:commuting-extension-determines-tensor-terms} to this rank statement
  and to the given uniqueness hypotheses. It follows that every competing length-$r$
  decomposition agrees with the displayed one term by term after a permutation, which is
  precisely the required essential uniqueness. -/)
  (title := /-- Essential uniqueness under the commuting-extension hypotheses -/)
  (latexEnv := "lemma")]
lemma essential_uniqueness_from_uniqueness_hypotheses {K : Type} [Field K] [Infinite K]
    {n q r : ℕ}
    (T : order_three_tensor K n (q + 2))
    (u v : Fin r → Fin n → K) (w : Fin r → Fin (q + 2) → K)
    (hq : 2 ≤ q)
    (h : tensor_uniqueness_hypotheses T u v w) :
    essentially_unique_decomposition T u v w := by
  apply commuting_extension_determines_tensor_terms T u v w hq h
  exact tensor_rank_from_uniqueness_hypotheses T u v w hq h

@[blueprint "thm:efficient-overcomplete-tensor-uniqueness"
  (statement := /-- Let $K$ be an infinite field, let $n,q,r$ be nonnegative integers with
  $2\leq q$, and set $p=q+2$. Let
  $T=\sum_{a=1}^r u_a\otimes v_a\otimes w_a$ be a tensor of format $n\times n\times p$.
  Suppose that the vectors $w_a$ are pairwise linearly independent and that the span of the
  slices of $T$ contains an invertible matrix. Assume moreover that there exists an invertible
  matrix $A$ in this span such that, for every $2\leq l\leq p-1$, there is an
  $m\notin\{1,l\}$ for which $(H_{1lm})$ holds for
  $(A^{-1}T_2,\ldots,A^{-1}T_p)$. Then $T$ has tensor rank $r$, and the displayed
  decomposition into $r$ rank-one tensors is essentially unique. -/)
  (proof := /-- By \cref{lem:tensor-rank-from-uniqueness-hypotheses}, the tensor has rank $r$.
  By \cref{lem:essential-uniqueness-from-uniqueness-hypotheses}, the displayed decomposition
  is essentially unique. These two conclusions give the required conjunction. -/)
  (title := /-- Efficient uniqueness theorem for overcomplete tensor decomposition -/)
  (latexEnv := "theorem")]
theorem efficient_overcomplete_tensor_uniqueness {K : Type} [Field K] [Infinite K]
    {n q r : ℕ}
    (T : order_three_tensor K n (q + 2))
    (u v : Fin r → Fin n → K) (w : Fin r → Fin (q + 2) → K)
    (hq : 2 ≤ q)
    (h : tensor_uniqueness_hypotheses T u v w) :
    tensor_uniqueness_conclusion T u v w := by
  constructor
  · exact tensor_rank_from_uniqueness_hypotheses T u v w hq h
  · exact essential_uniqueness_from_uniqueness_hypotheses T u v w hq h

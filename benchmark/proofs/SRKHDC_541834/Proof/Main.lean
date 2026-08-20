import Architect
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Data.Real.Sign
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Order.Lattice.Nat

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:binary-string"
  (statement := /-- For every natural number $n$, a binary string of length $n$ is a function from $\operatorname{Fin}(n)$ to the Boolean type. -/)
  (title := /-- Binary strings -/)
  (latexEnv := "definition")]
abbrev binary_string (n : ℕ) := Fin n → Bool

@[blueprint "def:exact-hamming-matrix"
  (statement := /-- For natural numbers $n$ and $k$, the exact $k$-Hamming-distance matrix is the Boolean matrix indexed by binary strings of length $n$ whose $(x,y)$-entry is true if and only if the Hamming distance between $x$ and $y$ equals $k$. -/)
  (title := /-- The exact Hamming-distance matrix -/)
  (latexEnv := "definition")]
def exact_hamming_matrix (n k : ℕ) :
    Matrix (binary_string n) (binary_string n) Bool :=
  fun x y => decide (hammingDist x y = k)

@[blueprint "def:boolean-sign"
  (statement := /-- The real sign attached to a Boolean value is $-1$ for false and $1$ for true. -/)
  (title := /-- Boolean signs -/)
  (latexEnv := "definition")]
def boolean_sign : Bool → ℝ
  | false => -1
  | true => 1

@[blueprint "def:sign-realizes"
  (statement := /-- Let $M$ be a Boolean matrix and let $A$ be a real matrix with the same row and column index types. The matrix $A$ sign-realizes $M$ if the sign of each entry of $A$ is the Boolean sign prescribed by \cref{def:boolean-sign} at the corresponding entry of $M$. -/)
  (title := /-- Sign realization of a Boolean matrix -/)
  (latexEnv := "definition")]
def sign_realizes {I J : Type*}
    (M : Matrix I J Bool) (A : Matrix I J ℝ) : Prop :=
  ∀ i j, Real.sign (A i j) = boolean_sign (M i j)

@[blueprint "def:sign-rank"
  (statement := /-- Let $M$ be a Boolean matrix with finite column index type. Its sign-rank is the least natural number that occurs as the rank of a real matrix sign-realizing $M$ in the sense of \cref{def:sign-realizes}. -/)
  (title := /-- Sign-rank -/)
  (latexEnv := "definition")]
noncomputable def sign_rank {I J : Type*} [Fintype J]
    (M : Matrix I J Bool) : ℕ :=
  sInf {r : ℕ | ∃ A : Matrix I J ℝ,
    sign_realizes M A ∧ Matrix.rank A = r}

@[blueprint "def:oracle-tree"
  (statement := /-- Let $I$ and $J$ be types. An oracle tree on $I\times J$ is either a leaf labelled by a Boolean output or an internal node labelled by a Boolean query matrix, with one subtree for each possible answer to that query. -/)
  (title := /-- Boolean oracle trees -/)
  (latexEnv := "definition")]
inductive oracle_tree (I J : Type*) where
  | leaf : Bool → oracle_tree I J
  | query :
      Matrix I J Bool →
      oracle_tree I J →
      oracle_tree I J →
      oracle_tree I J

@[blueprint "def:oracle-tree-evaluation"
  (statement := /-- The evaluation of the oracle tree from \cref{def:oracle-tree} at an input $(i,j)$ follows the false or true child at every internal node according to the value of its query at $(i,j)$ and returns the label of the resulting leaf. -/)
  (title := /-- Evaluation of an oracle tree -/)
  (latexEnv := "definition")]
def oracle_tree_evaluation {I J : Type*} :
    oracle_tree I J → I → J → Bool
  | oracle_tree.leaf value, _, _ => value
  | oracle_tree.query Q falseTree trueTree, i, j =>
      if Q i j then
        oracle_tree_evaluation trueTree i j
      else
        oracle_tree_evaluation falseTree i j

@[blueprint "def:oracle-tree-depth"
  (statement := /-- The depth of an oracle tree from \cref{def:oracle-tree} is zero at a leaf and is one plus the maximum of the depths of the two children at an internal node. -/)
  (title := /-- Depth of an oracle tree -/)
  (latexEnv := "definition")]
def oracle_tree_depth {I J : Type*} : oracle_tree I J → ℕ
  | oracle_tree.leaf _ => 0
  | oracle_tree.query _ falseTree trueTree =>
      max (oracle_tree_depth falseTree) (oracle_tree_depth trueTree) + 1

@[blueprint "def:query-support-rank-at-most"
  (statement := /-- A Boolean query matrix $Q$ has support-rank at most $r$ if there exists a real matrix $B$ of rank at most $r$ whose zero entries are precisely the false entries of $Q$. -/)
  (title := /-- Bounded support-rank of a query -/)
  (latexEnv := "definition")]
def query_support_rank_at_most {I J : Type*} [Fintype J]
    (Q : Matrix I J Bool) (r : ℕ) : Prop :=
  ∃ B : Matrix I J ℝ,
    (∀ i j, B i j = 0 ↔ Q i j = false) ∧ Matrix.rank B ≤ r

@[blueprint "def:oracle-tree-support-rank-at-most"
  (statement := /-- An oracle tree from \cref{def:oracle-tree} has support-rank at most $r$ if every query labelling an internal node has support-rank at most $r$ in the sense of \cref{def:query-support-rank-at-most}, recursively on both children. -/)
  (title := /-- Uniform support-rank along an oracle tree -/)
  (latexEnv := "definition")]
def oracle_tree_support_rank_at_most {I J : Type*} [Fintype J] :
    oracle_tree I J → ℕ → Prop
  | oracle_tree.leaf _, _ => True
  | oracle_tree.query Q falseTree trueTree, r =>
      query_support_rank_at_most Q r ∧
        oracle_tree_support_rank_at_most falseTree r ∧
        oracle_tree_support_rank_at_most trueTree r

@[blueprint "lem:matrix-rank-add-le"
  (statement := /-- Let $I$ and $J$ be finite types, and let $A$ and $B$ be real $I\times J$ matrices. Then
  \[
    \operatorname{rank}(A+B)
      \leq \operatorname{rank}(A)+\operatorname{rank}(B).
  \] -/)
  (proof := /-- The linear map associated with $A+B$ is the sum of the linear maps associated with $A$ and $B$, so its range is contained in the sum of their ranges. Monotonicity of finite dimension therefore bounds $operatorname{rank}(A+B)$ by the dimension of this sum. Grassmann's identity states that the dimension of the sum plus the dimension of the intersection equals $operatorname{rank}(A)+\operatorname{rank}(B)$; since the dimension of the intersection is nonnegative, the asserted inequality follows. -/)
  (title := /-- Subadditivity of matrix rank -/)
  (latexEnv := "lemma")]
lemma matrix_rank_add_le {I J : Type*} [Fintype I] [Fintype J]
    (A B : Matrix I J ℝ) :
    Matrix.rank (A + B) ≤ Matrix.rank A + Matrix.rank B := by
  unfold Matrix.rank
  apply le_trans (Submodule.finrank_mono (by
    simpa only [Matrix.mulVecLin_add] using
      LinearMap.range_add_le A.mulVecLin B.mulVecLin))
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
  omega

@[blueprint "lem:matrix-rank-hadamard-le"
  (statement := /-- Let $I$ and $J$ be finite types, and let $A$ and $B$ be real $I\times J$ matrices. Their entrywise product satisfies
  \[
    \operatorname{rank}(A\circ B)
      \leq \operatorname{rank}(A)\operatorname{rank}(B).
  \] -/)
  (proof := /-- Choose bases $(u_a)_a$ and $(v_b)_b$ of the column spaces of $A$ and $B$, indexed respectively by sets of cardinality $\operatorname{rank}(A)$ and $\operatorname{rank}(B)$. Write the $j$th columns as
  \[
    A_{\bullet j}=\sum_a \alpha_{aj}u_a,
    \qquad
    B_{\bullet j}=\sum_b \beta_{bj}v_b.
  \]
  Define matrices $C$ and $D$, with their common index set consisting of pairs $(a,b)$, by
  \[
    C_{i,(a,b)}=(u_a)_i(v_b)_i,
    \qquad
    D_{(a,b),j}=\alpha_{aj}\beta_{bj}.
  \]
  Distributivity of finite sums gives $(CD)_{ij}=A_{ij}B_{ij}$, so $A\circ B=CD$. The rank of a matrix product is at most the rank of its left factor, and the rank of $C$ is at most its number of columns, which is $\operatorname{rank}(A)\operatorname{rank}(B)$. -/)
  (title := /-- Rank of an entrywise product -/)
  (latexEnv := "lemma")]
lemma matrix_rank_hadamard_le {I J : Type*} [Fintype I] [Fintype J]
    (A B : Matrix I J ℝ) :
    Matrix.rank (fun i j => A i j * B i j) ≤
      Matrix.rank A * Matrix.rank B := by
  classical
  let bA := Module.finBasis ℝ (LinearMap.range A.mulVecLin)
  let aCol (j : J) : LinearMap.range A.mulVecLin :=
    ⟨A.col j, by
      rw [Matrix.range_mulVecLin]
      exact Submodule.subset_span (Set.mem_range_self j)⟩
  let C_A : Matrix I (Fin (Matrix.rank A)) ℝ :=
    fun i k => (bA k : I → ℝ) i
  let D_A : Matrix (Fin (Matrix.rank A)) J ℝ :=
    fun k j => bA.repr (aCol j) k
  have hA : A = C_A * D_A := by
    ext i j
    have h := bA.sum_repr (aCol j)
    have hi := congrFun
      (congrArg (fun x : LinearMap.range A.mulVecLin => (x : I → ℝ)) h) i
    change (aCol j : I → ℝ) i =
      ∑ k, (bA k : I → ℝ) i * bA.repr (aCol j) k
    rw [← hi]
    simp only [Submodule.coe_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k hk
    exact mul_comm _ _
  let bB := Module.finBasis ℝ (LinearMap.range B.mulVecLin)
  let bCol (j : J) : LinearMap.range B.mulVecLin :=
    ⟨B.col j, by
      rw [Matrix.range_mulVecLin]
      exact Submodule.subset_span (Set.mem_range_self j)⟩
  let C_B : Matrix I (Fin (Matrix.rank B)) ℝ :=
    fun i k => (bB k : I → ℝ) i
  let D_B : Matrix (Fin (Matrix.rank B)) J ℝ :=
    fun k j => bB.repr (bCol j) k
  have hB : B = C_B * D_B := by
    ext i j
    have h := bB.sum_repr (bCol j)
    have hi := congrFun
      (congrArg (fun x : LinearMap.range B.mulVecLin => (x : I → ℝ)) h) i
    change (bCol j : I → ℝ) i =
      ∑ k, (bB k : I → ℝ) i * bB.repr (bCol j) k
    rw [← hi]
    simp only [Submodule.coe_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k hk
    exact mul_comm _ _
  let C : Matrix I (Fin (Matrix.rank A) × Fin (Matrix.rank B)) ℝ :=
    fun i k => C_A i k.1 * C_B i k.2
  let D : Matrix (Fin (Matrix.rank A) × Fin (Matrix.rank B)) J ℝ :=
    fun k j => D_A k.1 j * D_B k.2 j
  have hH : (fun i j => A i j * B i j) = C * D := by
    ext i j
    have haij := congrFun (congrFun hA i) j
    have hbij := congrFun (congrFun hB i) j
    rw [haij, hbij]
    simp only [Matrix.mul_apply, C, D]
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    ac_rfl
  calc
    Matrix.rank (fun i j => A i j * B i j) =
        Matrix.rank (C * D) := congrArg Matrix.rank hH
    _ ≤ Matrix.rank C := Matrix.rank_mul_le_left C D
    _ ≤ Fintype.card (Fin (Matrix.rank A) × Fin (Matrix.rank B)) :=
      Matrix.rank_le_card_width C
    _ = Matrix.rank A * Matrix.rank B := by
      simpa only [Fintype.card_prod, Fintype.card_fin]

@[blueprint "lem:combine-sign-realizers-along-query"
  (statement := /-- Let $I$ and $J$ be finite types, let $Q,M_0,M_1$ be Boolean $I\times J$ matrices, and let $A_0,A_1,B$ be real $I\times J$ matrices. Suppose that $B(i,j)=0$ if and only if $Q(i,j)$ is false, and that $A_0$ and $A_1$ sign-realize $M_0$ and $M_1$, respectively. Define the Boolean matrix $M$ by $M(i,j)=M_1(i,j)$ when $Q(i,j)$ is true and $M(i,j)=M_0(i,j)$ when $Q(i,j)$ is false. Then there exists a real matrix $A$ that sign-realizes $M$ and satisfies
  \[
    \operatorname{rank}(A)
      \leq \operatorname{rank}(A_0)
       +\operatorname{rank}(B)^2\operatorname{rank}(A_1).
  \] -/)
  (proof := /-- Because $I\times J$ is finite and every entry of $A_1$ is nonzero by \cref{def:sign-realizes}, choose $\gamma>0$ so large that, at every entry where $B$ is nonzero, the term $\gamma B(i,j)^2A_1(i,j)$ strictly dominates $A_0(i,j)$ in absolute value. Set
  \[
    A=A_0+\gamma(B\circ B\circ A_1).
  \]
  If $Q(i,j)$ is false, then $B(i,j)=0$, so the sign of $A(i,j)$ is the sign prescribed by $M_0(i,j)$. If $Q(i,j)$ is true, then $B(i,j)^2>0$ and the dominating second term has the sign prescribed by $M_1(i,j)$. Hence $A$ sign-realizes the selected matrix. Apply \cref{lem:matrix-rank-add-le} to the displayed sum and apply \cref{lem:matrix-rank-hadamard-le} twice to its second summand; multiplication by the nonzero scalar $\gamma$ does not increase rank. This gives the stated rank estimate. -/)
  (title := /-- Combining realizers at an oracle query -/)
  (latexEnv := "lemma")]
lemma combine_sign_realizers_along_query
    {I J : Type*} [Fintype I] [Fintype J]
    (Q M₀ M₁ : Matrix I J Bool)
    (A₀ A₁ B : Matrix I J ℝ)
    (hB : ∀ i j, B i j = 0 ↔ Q i j = false)
    (hA₀ : sign_realizes M₀ A₀)
    (hA₁ : sign_realizes M₁ A₁) :
    ∃ A : Matrix I J ℝ,
      sign_realizes
        (fun i j => if Q i j then M₁ i j else M₀ i j) A ∧
      Matrix.rank A ≤
        Matrix.rank A₀ + Matrix.rank B ^ 2 * Matrix.rank A₁ := by
  classical
  obtain ⟨c, hc⟩ := Finite.exists_le (fun p : I × J =>
    |A₀ p.1 p.2| / ((B p.1 p.2) ^ 2 * |A₁ p.1 p.2|))
  let γ : ℝ := c + 1
  let C : Matrix I J ℝ := fun i j => B i j * B i j * A₁ i j
  let A : Matrix I J ℝ := A₀ + γ • C
  refine ⟨A, ?_, ?_⟩
  · intro i j
    cases hq : Q i j
    · have hz : B i j = 0 := (hB i j).2 hq
      simpa [A, C, hq, hz] using hA₀ i j
    · have hBn : B i j ≠ 0 := by
        intro hz
        have := (hB i j).1 hz
        simp [hq] at this
      have hA₁n : A₁ i j ≠ 0 := by
        intro hz
        have hs := hA₁ i j
        rw [hz, Real.sign_zero] at hs
        cases hm : M₁ i j <;> simp [hm, boolean_sign] at hs
      have hd : 0 < (B i j) ^ 2 * |A₁ i j| :=
        mul_pos (sq_pos_of_ne_zero hBn) (abs_pos.mpr hA₁n)
      have hle : |A₀ i j| ≤ c * ((B i j) ^ 2 * |A₁ i j|) :=
        (div_le_iff₀ hd).mp (hc (i, j))
      have hγc : c < γ := by simp [γ]
      have hdom : |A₀ i j| < γ * ((B i j) ^ 2 * |A₁ i j|) :=
        hle.trans_lt (mul_lt_mul_of_pos_right hγc hd)
      cases hm : M₁ i j
      · have hs := hA₁ i j
        rw [hm, boolean_sign] at hs
        have hn : A₁ i j < 0 := by
          rw [Real.sign] at hs
          split_ifs at hs with hneg hpos
          · exact hneg
          · norm_num at hs
          · norm_num at hs
        rw [abs_of_neg hn] at hdom
        have hneg : A₀ i j + γ * (B i j * B i j * A₁ i j) < 0 := by
          nlinarith [le_abs_self (A₀ i j)]
        simpa [A, C, hq, hm, boolean_sign] using Real.sign_of_neg hneg
      · have hs := hA₁ i j
        rw [hm, boolean_sign] at hs
        have hp : 0 < A₁ i j := by
          rw [Real.sign] at hs
          split_ifs at hs with hneg hpos
          · norm_num at hs
          · exact hpos
          · norm_num at hs
        rw [abs_of_pos hp] at hdom
        have hpos : 0 < A₀ i j + γ * (B i j * B i j * A₁ i j) := by
          nlinarith [neg_abs_le (A₀ i j)]
        simpa [A, C, hq, hm, boolean_sign] using Real.sign_of_pos hpos
  · have hscalar : Matrix.rank (γ • C) ≤ Matrix.rank C := by
      simpa only [Matrix.smul_mul, Matrix.one_mul] using
        (Matrix.rank_mul_le_right (γ • (1 : Matrix I I ℝ)) C)
    have hC : Matrix.rank C ≤
        Matrix.rank B * (Matrix.rank B * Matrix.rank A₁) := by
      calc
        Matrix.rank C =
            Matrix.rank (fun i j => B i j * (B i j * A₁ i j)) := by
              congr 1
              funext i j
              simp [C, mul_assoc]
        _ ≤ Matrix.rank B *
            Matrix.rank (fun i j => B i j * A₁ i j) :=
              matrix_rank_hadamard_le _ _
        _ ≤ Matrix.rank B * (Matrix.rank B * Matrix.rank A₁) :=
              Nat.mul_le_mul_left _ (matrix_rank_hadamard_le B A₁)
    calc
      Matrix.rank A = Matrix.rank (A₀ + γ • C) := rfl
      _ ≤ Matrix.rank A₀ + Matrix.rank (γ • C) :=
        matrix_rank_add_le _ _
      _ ≤ Matrix.rank A₀ + Matrix.rank C :=
        Nat.add_le_add_left hscalar _
      _ ≤ Matrix.rank A₀ +
          Matrix.rank B * (Matrix.rank B * Matrix.rank A₁) :=
        Nat.add_le_add_left hC _
      _ = Matrix.rank A₀ + Matrix.rank B ^ 2 * Matrix.rank A₁ := by
        simp [pow_two, Nat.mul_assoc]

@[blueprint "lem:constant-boolean-sign-rank-le-one"
  (statement := /-- Let $I$ and $J$ be finite types and let $b$ be a Boolean value. The constant $I\times J$ Boolean matrix with value $b$ has sign-rank at most one. -/)
  (proof := /-- The constant real matrix whose entries are the nonzero value prescribed by \cref{def:boolean-sign} sign-realizes the constant Boolean matrix by \cref{def:sign-realizes}. It is an outer-product matrix, so its rank is at most one. The definition of sign-rank in \cref{def:sign-rank} then gives the desired bound. -/)
  (title := /-- Sign-rank of a constant Boolean matrix -/)
  (latexEnv := "lemma")]
lemma constant_boolean_sign_rank_le_one
    {I J : Type*} [Fintype I] [Fintype J] (b : Bool) :
    sign_rank (fun _ : I => fun _ : J => b) ≤ 1 := by
  classical
  let A : Matrix I J ℝ :=
    Matrix.vecMulVec (fun _ : I => boolean_sign b) (fun _ : J => 1)
  calc
    sign_rank (fun _ : I => fun _ : J => b) ≤ Matrix.rank A := by
      apply Nat.sInf_le
      refine ⟨A, ?_, rfl⟩
      intro i j
      cases b
      · simpa [A, Matrix.vecMulVec, boolean_sign] using
          (Real.sign_of_neg (show (-1 : ℝ) < 0 by norm_num))
      · simp [A, Matrix.vecMulVec, boolean_sign]
    _ ≤ 1 := Matrix.rank_vecMulVec_le _ _

@[blueprint "lem:sign-rank-attained-for-finite-matrix"
  (statement := /-- Let $I$ be a type, let $J$ be a finite type, and let $M$ be a Boolean $I\times J$ matrix. There exists a real matrix $A$ that sign-realizes $M$ and satisfies
  \[
    \operatorname{rank}(A)=\operatorname{signrank}(M).
  \] -/)
  (proof := /-- Define $A(i,j)$ to be the real value prescribed by \cref{def:boolean-sign} for $M(i,j)$. Its entrywise signs agree with those values, so $A$ sign-realizes $M$ by \cref{def:sign-realizes}. Consequently, the set of ranks of real matrices sign-realizing $M$ is nonempty. The well-ordering principle for the natural numbers implies that the infimum of this set belongs to the set, and \cref{def:sign-rank} identifies that infimum with $\operatorname{signrank}(M)$. -/)
  (title := /-- Attainment of sign-rank -/)
  (latexEnv := "lemma")]
lemma sign_rank_attained_for_finite_matrix
    {I J : Type*} [Fintype J] (M : Matrix I J Bool) :
    ∃ A : Matrix I J ℝ,
      sign_realizes M A ∧ Matrix.rank A = sign_rank M := by
  classical
  let A : Matrix I J ℝ := fun i j => boolean_sign (M i j)
  have hA : sign_realizes M A := by
    intro i j
    cases h : M i j
    · simpa [A, h, boolean_sign] using
        (Real.sign_of_neg (show (-1 : ℝ) < 0 by norm_num))
    · simp [A, h, boolean_sign]
  have hne : {s : ℕ | ∃ A : Matrix I J ℝ,
      sign_realizes M A ∧ Matrix.rank A = s}.Nonempty :=
    ⟨Matrix.rank A, A, hA, rfl⟩
  simpa only [sign_rank, Set.mem_setOf_eq] using Nat.sInf_mem hne

@[blueprint "lem:oracle-tree-sign-rank-bound"
  (statement := /-- Let $I$ and $J$ be finite types, let $T$ be an oracle tree on $I\times J$, and let $r\in\mathbb{N}$. Suppose that every query in $T$ has support-rank at most $r$. Then
  \[
    \operatorname{signrank}(T)
      \leq (1+r^2)^{\operatorname{depth}(T)},
  \]
  where the Boolean matrix represented by $T$ is its evaluation from \cref{def:oracle-tree-evaluation} and its depth is defined in \cref{def:oracle-tree-depth}. -/)
  (proof := /-- Induct on the tree $T$. At a leaf, the evaluation from \cref{def:oracle-tree-evaluation} is constant and the depth from \cref{def:oracle-tree-depth} is zero, so \cref{lem:constant-boolean-sign-rank-le-one} gives the desired estimate. At an internal node, the hypothesis from \cref{def:oracle-tree-support-rank-at-most} supplies a real support matrix $B$ for the root query with rank at most $r$, together with the corresponding hypotheses for both subtrees. Apply the induction hypotheses to bound the two subtree sign-ranks. By \cref{lem:sign-rank-attained-for-finite-matrix}, choose sign-realizers $A_0$ and $A_1$ whose ranks equal those sign-ranks. Then \cref{lem:combine-sign-realizers-along-query} produces a sign-realizer for the evaluation at the internal node whose rank is at most
  \[
    \operatorname{rank}(A_0)+\operatorname{rank}(B)^2\operatorname{rank}(A_1).
  \]
  The definition in \cref{def:sign-rank} bounds the sign-rank of the node evaluation by the rank of this realizer. If $d$ is the maximum of the two subtree depths, monotonicity of powers, the induction hypotheses, and $\operatorname{rank}(B)\leq r$ bound the displayed quantity by
  \[
    (1+r^2)^d+r^2(1+r^2)^d
      =(1+r^2)^{d+1}.
  \]
  By \cref{def:oracle-tree-depth}, $d+1$ is the depth of the internal node, which completes the induction. -/)
  (title := /-- Oracle-tree upper bound for sign-rank -/)
  (latexEnv := "lemma")]
lemma oracle_tree_sign_rank_bound
    {I J : Type*} [Fintype I] [Fintype J]
    (T : oracle_tree I J) (r : ℕ)
    (hT : oracle_tree_support_rank_at_most T r) :
    sign_rank (fun i j => oracle_tree_evaluation T i j) ≤
      (1 + r ^ 2) ^ oracle_tree_depth T := by
  induction T with
  | leaf value =>
      simpa [oracle_tree_evaluation, oracle_tree_depth] using
        (constant_boolean_sign_rank_le_one (I := I) (J := J) value)
  | query Q falseTree trueTree ihFalse ihTrue =>
      rcases hT with ⟨⟨B, hB, hBr⟩, hFalse, hTrue⟩
      have hFalseRank := ihFalse hFalse
      have hTrueRank := ihTrue hTrue
      obtain ⟨A₀, hA₀, hrA₀⟩ :=
        sign_rank_attained_for_finite_matrix
          (fun i j => oracle_tree_evaluation falseTree i j)
      obtain ⟨A₁, hA₁, hrA₁⟩ :=
        sign_rank_attained_for_finite_matrix
          (fun i j => oracle_tree_evaluation trueTree i j)
      obtain ⟨A, hA, hArank⟩ :=
        combine_sign_realizers_along_query Q
          (fun i j => oracle_tree_evaluation falseTree i j)
          (fun i j => oracle_tree_evaluation trueTree i j)
          A₀ A₁ B hB hA₀ hA₁
      have hbase : 0 < 1 + r ^ 2 := by omega
      have hFalsePow :
          (1 + r ^ 2) ^ oracle_tree_depth falseTree ≤
            (1 + r ^ 2) ^
              max (oracle_tree_depth falseTree) (oracle_tree_depth trueTree) :=
        Nat.pow_le_pow_right hbase (Nat.le_max_left _ _)
      have hTruePow :
          (1 + r ^ 2) ^ oracle_tree_depth trueTree ≤
            (1 + r ^ 2) ^
              max (oracle_tree_depth falseTree) (oracle_tree_depth trueTree) :=
        Nat.pow_le_pow_right hbase (Nat.le_max_right _ _)
      calc
        sign_rank (fun i j =>
            oracle_tree_evaluation
              (oracle_tree.query Q falseTree trueTree) i j) ≤
            Matrix.rank A := by
          apply Nat.sInf_le
          refine ⟨A, ?_, rfl⟩
          simpa [oracle_tree_evaluation] using hA
        _ ≤ Matrix.rank A₀ + Matrix.rank B ^ 2 * Matrix.rank A₁ := hArank
        _ = sign_rank (fun i j => oracle_tree_evaluation falseTree i j) +
            Matrix.rank B ^ 2 *
              sign_rank (fun i j => oracle_tree_evaluation trueTree i j) := by
          rw [hrA₀, hrA₁]
        _ ≤ (1 + r ^ 2) ^ oracle_tree_depth falseTree +
            r ^ 2 * (1 + r ^ 2) ^ oracle_tree_depth trueTree := by
          exact Nat.add_le_add hFalseRank
            (Nat.mul_le_mul (Nat.pow_le_pow_left hBr 2) hTrueRank)
        _ ≤ (1 + r ^ 2) ^
              max (oracle_tree_depth falseTree) (oracle_tree_depth trueTree) +
            r ^ 2 * (1 + r ^ 2) ^
              max (oracle_tree_depth falseTree) (oracle_tree_depth trueTree) := by
          exact Nat.add_le_add hFalsePow (Nat.mul_le_mul_left _ hTruePow)
        _ = (1 + r ^ 2) ^
              (max (oracle_tree_depth falseTree)
                (oracle_tree_depth trueTree) + 1) := by
          rw [pow_succ]
          ring
        _ = (1 + r ^ 2) ^ oracle_tree_depth
              (oracle_tree.query Q falseTree trueTree) := rfl

@[blueprint "lem:sign-rank-congr"
  (statement := /-- Let $I$ be a type, let $J$ be a finite type, and let $M,N\colon I\times J\to\{0,1\}$ be Boolean matrices. If $M(i,j)=N(i,j)$ for every $i\in I$ and $j\in J$, then the sign-ranks of $M$ and $N$ are equal. -/)
  (proof := /-- Applying function extensionality first in the row variable and then in the column variable to the hypothesis gives $M=N$. Applying the sign-rank function from \cref{def:sign-rank} to this equality yields the claimed equality. -/)
  (title := /-- Sign-rank respects pointwise equality -/)
  (latexEnv := "lemma")]
lemma sign_rank_congr
    {I J : Type*} [Fintype J]
    (M N : Matrix I J Bool)
    (hMN : ∀ i j, M i j = N i j) :
    sign_rank M = sign_rank N := by
  apply congrArg sign_rank
  funext i j
  exact hMN i j

@[blueprint "lem:real-mv-polynomial-has-nonzero-evaluation"
  (statement := /-- Let $\sigma$ be a finite type and let $p\in\mathbb{R}[X_s:s\in\sigma]$ be a nonzero multivariate polynomial. Then there is a point $a\colon\sigma\to\mathbb{R}$ such that $p(a)\neq0$. -/)
  (proof := /-- Choose a monomial of maximal total degree in the nonempty support of $p$. Its coefficient is nonzero and its degree is the total degree of $p$. For each variable, take a finite set of real numbers having cardinality strictly greater than the corresponding exponent. The combinatorial Nullstellensatz then supplies an evaluation point at which $p$ is nonzero. -/)
  (title := /-- A nonzero real multivariate polynomial has a nonzero value -/)
  (latexEnv := "lemma")]
lemma real_mv_polynomial_has_nonzero_evaluation
    {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ) (hp : p ≠ 0) :
    ∃ a : σ → ℝ, MvPolynomial.eval a p ≠ 0 := by
  classical
  obtain ⟨t, ht, hdeg⟩ := p.support.exists_mem_eq_sup
    (MvPolynomial.support_nonempty.mpr hp)
    (fun m => Multiset.card (Finsupp.toMultiset m))
  have hcoeff : p.coeff t ≠ 0 := MvPolynomial.mem_support_iff.mp ht
  have htotal : p.totalDegree = t.degree := by
    rw [MvPolynomial.totalDegree_eq, hdeg, Finsupp.card_toMultiset]
    simp [Finsupp.degree_apply, Finsupp.sum]
  let S : σ → Finset ℝ := fun i =>
    (Finset.range (t i + 1)).map (Nat.castEmbedding : ℕ ↪ ℝ)
  have hcard : ∀ i, t i < (S i).card := by
    intro i
    simp [S]
  obtain ⟨a, _, ha⟩ :=
    MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero
      p t hcoeff htotal S hcard
  exact ⟨a, ha⟩

@[blueprint "lem:matrix-rank-le-finrank-of-linear-evaluation"
  (statement := /-- Let $I$ and $J$ be finite types, let $E$ be a finite-dimensional real vector space, let $u_i\in E$ for $i\in I$, and let $f_j\in E^*$ for $j\in J$. If a real matrix $B$ satisfies $B_{ij}=f_j(u_i)$ for every $i,j$, then $\operatorname{rank}(B)\leq\dim_{\mathbb{R}}E$. -/)
  (proof := /-- Choose a basis of $E$ indexed by $\operatorname{Fin}(\dim_{\mathbb{R}}E)$. The coordinate row of each $u_i$ and the values of each $f_j$ on the basis form matrices $U$ and $V$, respectively. Expanding $u_i$ in the chosen basis shows that $B=UV$. The rank of a product is at most the rank of its left factor, and the latter is at most its number of columns, namely $\dim_{\mathbb{R}}E$. -/)
  (title := /-- Rank bound for linear evaluation matrices -/)
  (latexEnv := "lemma")]
lemma matrix_rank_le_finrank_of_linear_evaluation
    {I J E : Type*} [Fintype I] [Fintype J]
    [AddCommGroup E] [Module ℝ E] [Module.Free ℝ E] [Module.Finite ℝ E]
    (u : I → E) (f : J → E →ₗ[ℝ] ℝ) (B : Matrix I J ℝ)
    (hB : ∀ i j, B i j = f j (u i)) :
    Matrix.rank B ≤ Module.finrank ℝ E := by
  classical
  let b := Module.finBasis ℝ E
  let U : Matrix I (Fin (Module.finrank ℝ E)) ℝ :=
    fun i a => b.repr (u i) a
  let V : Matrix (Fin (Module.finrank ℝ E)) J ℝ :=
    fun a j => f j (b a)
  have hmul : U * V = B := by
    ext i j
    rw [Matrix.mul_apply]
    calc
      ∑ a, U i a * V a j =
          f j (∑ a, (b.repr (u i) a) • b a) := by
            simp only [U, V, map_sum, map_smul, smul_eq_mul]
      _ = f j (u i) := by rw [b.sum_repr]
      _ = B i j := (hB i j).symm
  rw [← hmul]
  exact (Matrix.rank_mul_le_left U V).trans (by
    simpa using Matrix.rank_le_card_width U)

@[blueprint "lem:block-determinant-kernel-rank"
  (statement := /-- Let $X$ be a finite type. For each $x\in X$, let $u_x$ and $v_x$ be families of $j$ row vectors in $\mathbb{R}^{2j}$. The matrix whose $(x,y)$-entry is the determinant of the $2j$-by-$2j$ matrix with upper rows $u_x$ and lower rows $v_y$ has rank at most $4^j$. -/)
  (proof := /-- Fixing the lower $j$ rows turns the determinant into an alternating $j$-linear form in the upper rows. Such a form is determined by its values on the increasing enumerations of the $j$-element subsets of a basis of $\mathbb{R}^{2j}$: basis extensionality for alternating maps and permutation equivariance prove injectivity of this coordinate map. Hence the space of these forms has dimension at most the number of all subsets of a $2j$-element set, namely $2^{2j}=4^j$. The matrix is a linear-evaluation matrix on this space, so \cref{lem:matrix-rank-le-finrank-of-linear-evaluation} gives the claimed rank bound. -/)
  (title := /-- Rank of a block-determinant kernel -/)
  (latexEnv := "lemma")]
lemma block_determinant_kernel_rank
    {X : Type*} [Fintype X] (j : ℕ)
    (u v : X → Fin j → (Fin j ⊕ Fin j → ℝ)) :
    Matrix.rank (fun x y => Matrix.det (fun s => Sum.elim (u x) (v y) s)) ≤
      4 ^ j := by
  classical
  let K := Fin j ⊕ Fin j
  let E := AlternatingMap ℝ (K → ℝ) ℝ (Fin j)
  let S := {s : Finset K // s.card = j}
  let enum (s : S) : Fin j ≃ {a // a ∈ s.1} :=
    Fintype.equivOfCardEq (by simp [s.2])
  let coord : E →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun a s =>
        a (fun i => (Pi.basisFun ℝ K) ((enum s i).1))
      map_add' := by
        intro a b
        rfl
      map_smul' := by
        intro c a
        rfl }
  have hcoord : Function.Injective coord := by
    intro a b hab
    apply (Pi.basisFun ℝ K).ext_alternating
    intro w hw
    let s : S := ⟨Finset.univ.image w, by
      rw [Finset.card_image_iff.mpr]
      · simp
      · intro i _ k _ hik
        exact hw hik⟩
    let q : Fin j → Fin j := fun i =>
      (enum s).symm ⟨w i, by simp [s]⟩
    have hq : Function.Injective q := by
      intro i k hik
      apply hw
      have := congrArg (fun z => ((enum s) z).1) hik
      simpa [q] using this
    let e : Equiv.Perm (Fin j) := Equiv.ofBijective q
      ⟨hq, Finite.surjective_of_injective hq⟩
    have hw_eq : (fun i => (Pi.basisFun ℝ K) (w i)) =
        (fun i => (Pi.basisFun ℝ K) ((enum s i).1)) ∘ e := by
      funext i
      congr 2
      change w i = (enum s (q i)).1
      simp [q]
    have hs := congrFun (congrArg (fun z => z) hab) s
    change a (fun i => (Pi.basisFun ℝ K) ((enum s i).1)) =
      b (fun i => (Pi.basisFun ℝ K) ((enum s i).1)) at hs
    rw [hw_eq, a.map_perm, b.map_perm, hs]
  letI : Module.Finite ℝ E := Module.Finite.of_injective coord hcoord
  have hdim : Module.finrank ℝ E ≤ 4 ^ j := by
    calc
      Module.finrank ℝ E ≤ Module.finrank ℝ (S → ℝ) :=
        LinearMap.finrank_le_finrank_of_injective hcoord
      _ = Fintype.card S := by simp
      _ ≤ Fintype.card (Finset K) := Fintype.card_subtype_le _
      _ = 4 ^ j := by
        simp only [K, Fintype.card_finset, Fintype.card_sum, Fintype.card_fin]
        calc
          2 ^ (j + j) = 2 ^ (2 * j) := by rw [two_mul]
          _ = (2 ^ 2) ^ j := pow_mul 2 2 j
          _ = 4 ^ j := by norm_num
  let fullAlt : AlternatingMap ℝ (K → ℝ) ℝ K := Matrix.detRowAlternating
  let lowerAlt (y : X) : E :=
    { toMultilinearMap :=
        { toFun := fun rows =>
            fullAlt (Sum.elim rows (v y))
          map_update_add' := by
            intro _ rows i x₁ x₂
            have hu (z : K → ℝ) :
                Sum.elim (Function.update rows i z) (v y) =
                  Function.update (Sum.elim rows (v y)) (Sum.inl i) z := by
              funext s
              cases s with
              | inl a =>
                  by_cases h : a = i <;> simp [Function.update, h]
              | inr a => simp [Function.update]
            rw [hu (x₁ + x₂), hu x₁, hu x₂]
            exact fullAlt.toMultilinearMap.map_update_add
              (Sum.elim rows (v y)) (Sum.inl i) x₁ x₂
          map_update_smul' := by
            intro _ rows i c x
            have hu (z : K → ℝ) :
                Sum.elim (Function.update rows i z) (v y) =
                  Function.update (Sum.elim rows (v y)) (Sum.inl i) z := by
              funext s
              cases s with
              | inl a =>
                  by_cases h : a = i <;> simp [Function.update, h]
              | inr a => simp [Function.update]
            rw [hu (c • x), hu x]
            exact fullAlt.toMultilinearMap.map_update_smul
              (Sum.elim rows (v y)) (Sum.inl i) c x }
      map_eq_zero_of_eq' := by
        intro rows i k hik heq
        apply fullAlt.map_eq_zero_of_eq (Sum.elim rows (v y))
          (i := Sum.inl i) (j := Sum.inl k)
        · simpa using hik
        · intro h
          exact heq (Sum.inl.inj h) }
  let evalUpper (x : X) : E →ₗ[ℝ] ℝ :=
    { toFun := fun a => a (u x)
      map_add' := by intro a b; rfl
      map_smul' := by intro c a; rfl }
  have hrank : Matrix.rank
      (Matrix.transpose (fun x y =>
        Matrix.det (fun s => Sum.elim (u x) (v y) s))) ≤
      Module.finrank ℝ E := by
    apply matrix_rank_le_finrank_of_linear_evaluation lowerAlt evalUpper
    intro y x
    simp only [Matrix.transpose_apply]
    rfl
  rw [Matrix.rank_transpose] at hrank
  exact hrank.trans hdim

@[blueprint "lem:block-determinant-zero-iff"
  (statement := /-- For real $j$-by-$j$ matrices $A$ and $C$, the determinant of the block matrix $\left(\begin{smallmatrix}A&I\\ C&I\end{smallmatrix}\right)$ vanishes if and only if $\det(A-C)=0$. -/)
  (proof := /-- A vector $(p,q)$ lies in the kernel of the block matrix precisely when $Ap+q=0$ and $Cp+q=0$. A nonzero such vector must have $p\neq0$, and subtracting the two equations gives $(A-C)p=0$. Conversely, a nonzero vector $p$ in the kernel of $A-C$ yields the nonzero block-kernel vector $(p,-Ap)$. The characterization of a singular square matrix by the existence of a nonzero kernel vector proves the equivalence. -/)
  (title := /-- Singularity of a two-by-two block matrix -/)
  (latexEnv := "lemma")]
lemma block_determinant_zero_iff (j : ℕ)
    (A C : Matrix (Fin j) (Fin j) ℝ) :
    Matrix.det (Matrix.fromBlocks A 1 C 1) = 0 ↔
      Matrix.det (A - C) = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff,
    ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨w, hw, hMw⟩
    let p : Fin j → ℝ := fun i => w (Sum.inl i)
    let q : Fin j → ℝ := fun i => w (Sum.inr i)
    have hwdecomp : w = Sum.elim p q := by
      funext s
      cases s <;> rfl
    have htop : A.mulVec p + q = 0 := by
      funext i
      have hi := congrFun hMw (Sum.inl i)
      rw [hwdecomp] at hi
      simp [Matrix.fromBlocks, Matrix.mulVec,
        Fintype.sum_sum_type] at hi
      have hone : (1 : Matrix (Fin j) (Fin j) ℝ) i ⬝ᵥ q = q i :=
        congrFun (Matrix.one_mulVec q) i
      rw [hone] at hi
      exact hi
    have hbot : C.mulVec p + q = 0 := by
      funext i
      have hi := congrFun hMw (Sum.inr i)
      rw [hwdecomp] at hi
      simp [Matrix.fromBlocks, Matrix.mulVec,
        Fintype.sum_sum_type] at hi
      have hone : (1 : Matrix (Fin j) (Fin j) ℝ) i ⬝ᵥ q = q i :=
        congrFun (Matrix.one_mulVec q) i
      rw [hone] at hi
      exact hi
    have hp : p ≠ 0 := by
      intro hp0
      have hq0 : q = 0 := by simpa [hp0] using htop
      apply hw
      funext s
      cases s with
      | inl i => exact congrFun hp0 i
      | inr i => exact congrFun hq0 i
    refine ⟨p, hp, ?_⟩
    rw [Matrix.sub_mulVec]
    funext i
    have ht := congrFun htop i
    have hb := congrFun hbot i
    simp only [Pi.add_apply, Pi.zero_apply] at ht hb ⊢
    change A.mulVec p i - C.mulVec p i = 0
    linarith
  · rintro ⟨p, hp, hdiff⟩
    let q : Fin j → ℝ := -(A.mulVec p)
    let w : Fin j ⊕ Fin j → ℝ := Sum.elim p q
    refine ⟨w, ?_, ?_⟩
    · intro hw0
      apply hp
      funext i
      exact congrFun hw0 (Sum.inl i)
    · funext s
      cases s with
      | inl i =>
          have hone : (1 : Matrix (Fin j) (Fin j) ℝ) i ⬝ᵥ
              A.mulVec p = A.mulVec p i :=
            congrFun (Matrix.one_mulVec (A.mulVec p)) i
          simp [Matrix.fromBlocks, Matrix.mulVec, w, q,
            Fintype.sum_sum_type, hone]
      | inr i =>
          have hi := congrFun hdiff i
          simp only [Matrix.sub_mulVec, Pi.sub_apply, Pi.zero_apply] at hi
          have hone : (1 : Matrix (Fin j) (Fin j) ℝ) i ⬝ᵥ
              A.mulVec p = A.mulVec p i :=
            congrFun (Matrix.one_mulVec (A.mulVec p)) i
          simp [Matrix.fromBlocks, Matrix.mulVec, w, q,
            Fintype.sum_sum_type, hone, hi]
          change C.mulVec p i - A.mulVec p i = 0
          linarith

@[blueprint "lem:hamming-gram-determinant-polynomial-ne-zero"
  (statement := /-- Let $x,y$ be length-$n$ binary strings at Hamming distance at least $j$. Give every coordinate $i$ a formal vector $X_i\in\mathbb{R}^j$, let $H_x=\sum_{i:x_i=1}X_iX_i^{\mathsf T}$, and define $H_y$ similarly. Then the multivariate polynomial $\det(H_x-H_y)$ is nonzero. -/)
  (proof := /-- Choose $j$ coordinates on which $x$ and $y$ differ and specialize their formal vectors to the standard basis of $\mathbb{R}^j$, specializing every other vector to zero. The specialized difference $H_x-H_y$ is diagonal, and each diagonal entry is $1$ or $-1$ according to the orientation of the corresponding bit difference. Its determinant is therefore nonzero, so the original determinant polynomial is nonzero. -/)
  (title := /-- Nonvanishing of a generic Hamming Gram determinant -/)
  (latexEnv := "lemma")]
lemma hamming_gram_determinant_polynomial_ne_zero
    (n j : ℕ) (x y : binary_string n) (hxy : j ≤ hammingDist x y) :
    Matrix.det
      ((fun a b : Fin j => ∑ i : Fin n,
          MvPolynomial.C (if x i then (1 : ℝ) else 0) *
            MvPolynomial.X (i, a) * MvPolynomial.X (i, b)) -
       (fun a b : Fin j => ∑ i : Fin n,
          MvPolynomial.C (if y i then (1 : ℝ) else 0) *
            MvPolynomial.X (i, a) * MvPolynomial.X (i, b))) ≠ 0 := by
  classical
  let bitVal : Bool → ℝ := fun b => if b then 1 else 0
  let HP : binary_string n →
      Matrix (Fin j) (Fin j) (MvPolynomial (Fin n × Fin j) ℝ) :=
    fun q a b => ∑ i : Fin n,
      MvPolynomial.C (bitVal (q i)) *
        MvPolynomial.X (i, a) * MvPolynomial.X (i, b)
  let D := Finset.univ.filter (fun i : Fin n => x i ≠ y i)
  have hcard : j ≤ D.card := by
    simpa [D, hammingDist] using hxy
  have hcard' : j ≤ Fintype.card {i : Fin n // i ∈ D} := by
    simpa using hcard
  let e : Fin j → {i : Fin n // i ∈ D} := fun a =>
    (Fintype.equivFin {i : Fin n // i ∈ D}).symm
      ⟨a.1, a.2.trans_le hcard'⟩
  have he : Function.Injective e := by
    intro a b hab
    apply Fin.ext
    have h := congrArg (fun z =>
      (Fintype.equivFin {i : Fin n // i ∈ D}) z) hab
    simpa [e] using congrArg Fin.val h
  let z : Fin n × Fin j → ℝ := fun ia =>
    if ia.1 = (e ia.2).1 then 1 else 0
  let sgn : Fin j → ℝ := fun a => if x (e a).1 then 1 else -1
  have heval : (fun a b =>
      MvPolynomial.eval z ((HP x - HP y) a b)) =
      Matrix.diagonal sgn := by
    ext a b
    by_cases hab : a = b
    · subst b
      have hd := (Finset.mem_filter.mp (e a).2).2
      cases hx : x (e a).1 <;> cases hy : y (e a).1 <;>
        simp_all only [HP, bitVal, z, sgn, Matrix.diagonal,
          Matrix.sub_apply, map_sub, map_sum, map_mul,
          MvPolynomial.eval_C, MvPolynomial.eval_X, Bool.false_eq_true,
          ↓reduceIte, sub_zero, zero_sub] <;>
        rw [Finset.sum_eq_single (e a).1,
          Finset.sum_eq_single (e a).1] <;> simp_all
    · have hene : (e a).1 ≠ (e b).1 := by
        intro h
        apply hab
        exact he (Subtype.ext h)
      simp only [HP, bitVal, z, sgn, Matrix.diagonal,
        Matrix.sub_apply, map_sub, map_sum, map_mul,
        MvPolynomial.eval_C, MvPolynomial.eval_X]
      rw [Finset.sum_eq_single (e a).1,
        Finset.sum_eq_single (e a).1] <;> simp_all
  have hdiag : Matrix.det (Matrix.diagonal sgn) ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (by
      intro a _
      cases h : x (e a).1 <;> simp [sgn, h])
  change Matrix.det (HP x - HP y) ≠ 0
  intro hzero
  apply hdiag
  rw [← heval]
  have hmap : MvPolynomial.eval z (Matrix.det (HP x - HP y)) =
      Matrix.det (fun a b =>
        MvPolynomial.eval z ((HP x - HP y) a b)) := by
    exact RingHom.map_det (MvPolynomial.eval z) (HP x - HP y)
  rw [← hmap, hzero]
  simp

@[blueprint "lem:hamming-gram-rank-sum-le-card"
  (statement := /-- Let $s$ be a set of coordinates, let $c_i\in\mathbb{R}$, and let $w_i\in\mathbb{R}^j$. The rank of $\sum_{i\in s}(c_iw_i)w_i^{\mathsf T}$ is at most $|s|$. -/)
  (proof := /-- Induct on $s$. The empty sum has rank zero. When a new coordinate is inserted, \cref{lem:matrix-rank-add-le} bounds the rank of the enlarged sum by the rank of the old sum plus the rank of the new outer product; the latter is at most one. The induction hypothesis and the formula for the cardinality after insertion give the result. -/)
  (title := /-- Rank of a finite sum of outer products -/)
  (latexEnv := "lemma")]
lemma hamming_gram_rank_sum_le_card (n j : ℕ) (s : Finset (Fin n))
    (c : Fin n → ℝ) (w : Fin n → Fin j → ℝ) :
    Matrix.rank (∑ i ∈ s, Matrix.vecMulVec (c i • w i) (w i)) ≤
      s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
      calc
        Matrix.rank (Matrix.vecMulVec (c i • w i) (w i) +
            ∑ x ∈ s, Matrix.vecMulVec (c x • w x) (w x)) ≤
            Matrix.rank (Matrix.vecMulVec (c i • w i) (w i)) +
              Matrix.rank (∑ x ∈ s, Matrix.vecMulVec (c x • w x) (w x)) :=
          matrix_rank_add_le _ _
        _ ≤ 1 + s.card :=
          Nat.add_le_add (Matrix.rank_vecMulVec_le _ _) ih
        _ = s.card + 1 := Nat.add_comm _ _

@[blueprint "lem:generic-hamming-gram-matrices"
  (statement := /-- For all natural numbers $n$ and $j$, there are real symmetric $j$-by-$j$ matrices $H_x$, indexed by length-$n$ binary strings, such that $\det(H_x-H_y)=0$ exactly when the Hamming distance between $x$ and $y$ is less than $j$. -/)
  (proof := /-- Form the determinant polynomials from \cref{lem:hamming-gram-determinant-polynomial-ne-zero} for every pair at Hamming distance at least $j$. Their finite product is nonzero, so \cref{lem:real-mv-polynomial-has-nonzero-evaluation} supplies one simultaneous specialization at which every factor is nonzero. The resulting matrices therefore have nonzero difference determinant above the threshold. Below the threshold, their difference is a sum of fewer than $j$ rank-one matrices. Applying \cref{lem:hamming-gram-rank-sum-le-card} bounds its rank by the Hamming distance; a nonzero determinant would instead force rank $j$, a contradiction. -/)
  (title := /-- Generic Gram matrices detect a Hamming threshold -/)
  (latexEnv := "lemma")]
lemma generic_hamming_gram_matrices (n j : ℕ) :
    ∃ H : binary_string n → Matrix (Fin j) (Fin j) ℝ,
      ∀ x y, Matrix.det (H x - H y) = 0 ↔ hammingDist x y < j := by
  classical
  let bitVal : Bool → ℝ := fun b => if b then 1 else 0
  let HP : binary_string n →
      Matrix (Fin j) (Fin j) (MvPolynomial (Fin n × Fin j) ℝ) :=
    fun x a b => ∑ i : Fin n,
      MvPolynomial.C (bitVal (x i)) *
        MvPolynomial.X (i, a) * MvPolynomial.X (i, b)
  let DP : binary_string n → binary_string n →
      MvPolynomial (Fin n × Fin j) ℝ :=
    fun x y => Matrix.det (HP x - HP y)
  have hDP (x y : binary_string n) (hxy : j ≤ hammingDist x y) :
      DP x y ≠ 0 := by
    exact hamming_gram_determinant_polynomial_ne_zero n j x y hxy
  let good := Finset.univ.filter (fun p : binary_string n × binary_string n =>
    j ≤ hammingDist p.1 p.2)
  let P : MvPolynomial (Fin n × Fin j) ℝ :=
    ∏ p ∈ good, DP p.1 p.2
  have hP : P ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact hDP p.1 p.2 (Finset.mem_filter.mp hp).2
  obtain ⟨z, hz⟩ := real_mv_polynomial_has_nonzero_evaluation P hP
  have hevalDP (x y : binary_string n) (hxy : j ≤ hammingDist x y) :
      MvPolynomial.eval z (DP x y) ≠ 0 := by
    intro hzero
    apply hz
    simp only [P, map_prod]
    have hmem : (x, y) ∈ good := by simp [good, hxy]
    exact Finset.prod_eq_zero hmem hzero
  let H : binary_string n → Matrix (Fin j) (Fin j) ℝ := fun x =>
    (HP x).map (MvPolynomial.eval z)
  have hdet_of_le (x y : binary_string n) (hxy : j ≤ hammingDist x y) :
      Matrix.det (H x - H y) ≠ 0 := by
    have hm := RingHom.map_det (MvPolynomial.eval z) (HP x - HP y)
    have hn := hevalDP x y hxy
    rw [show DP x y = Matrix.det (HP x - HP y) by rfl] at hn
    rw [hm] at hn
    have heq : (MvPolynomial.eval z).mapMatrix (HP x - HP y) = H x - H y := by
      ext a b
      simp [H]
    rw [heq] at hn
    exact hn
  let D (x y : binary_string n) :=
    Finset.univ.filter (fun i : Fin n => x i ≠ y i)
  let coeff (x y : binary_string n) (i : Fin n) : ℝ :=
    bitVal (x i) - bitVal (y i)
  let w (i : Fin n) (a : Fin j) : ℝ := z (i, a)
  have hmatrix (x y : binary_string n) :
      H x - H y =
        ∑ i ∈ D x y, Matrix.vecMulVec (coeff x y i • w i) (w i) := by
    ext a b
    simp only [H, HP, Matrix.sub_apply, Matrix.map_apply, map_sub, map_sum,
      map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Matrix.vecMulVec_apply,
      Matrix.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_sub_distrib]
    change (∑ i : Fin n,
        (bitVal (x i) * z (i, a) * z (i, b) -
          bitVal (y i) * z (i, a) * z (i, b))) =
      ∑ i ∈ D x y, coeff x y i * w i a * w i b
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : x i = y i <;> simp [hi, coeff, w] <;> ring
  have hdet_of_lt (x y : binary_string n) (hxy : hammingDist x y < j) :
      Matrix.det (H x - H y) = 0 := by
    by_contra hne
    have hfull := (Matrix.linearIndependent_rows_of_det_ne_zero hne).rank_matrix
    have hr := hamming_gram_rank_sum_le_card n j (D x y) (coeff x y) w
    rw [← hmatrix x y] at hr
    have hcard : (D x y).card = hammingDist x y := by
      simp [D, hammingDist]
    rw [hfull, hcard] at hr
    simp at hr
    omega
  refine ⟨H, ?_⟩
  intro x y
  constructor
  · intro hz0
    by_contra hnot
    exact hdet_of_le x y (Nat.le_of_not_gt hnot) hz0
  · exact hdet_of_lt x y

@[blueprint "lem:hamming-threshold-query-support-rank"
  (statement := /-- For all natural numbers $n$ and $j$, the Boolean matrix on pairs of length-$n$ binary strings whose entry is true exactly when their Hamming distance is at least $j$ has support-rank at most $4^j$. -/)
  (proof := /-- Choose matrices $H_x$ as in \cref{lem:generic-hamming-gram-matrices}. For each $x$, append the $j$ rows of the identity matrix to the rows of $H_x$, and let $B_{x,y}$ be the determinant obtained by stacking the resulting rows for $x$ above those for $y$. By \cref{lem:block-determinant-zero-iff}, $B_{x,y}=0$ if and only if $\det(H_x-H_y)=0$; the defining property of the matrices $H_x$ says that this is equivalent to $d_H(x,y)<j$, hence to the threshold query being false. Thus $B$ has the required support in the sense of \cref{def:query-support-rank-at-most}. Finally, \cref{lem:block-determinant-kernel-rank} gives $\operatorname{rank}(B)\leq4^j$. -/)
  (title := /-- Support-rank of a Hamming-threshold query -/)
  (latexEnv := "lemma")]
lemma hamming_threshold_query_support_rank (n j : ℕ) :
    query_support_rank_at_most
      (fun x y : binary_string n => decide (j ≤ hammingDist x y)) (4 ^ j) := by
  classical
  obtain ⟨H, hH⟩ := generic_hamming_gram_matrices n j
  let rows : binary_string n → Fin j → (Fin j ⊕ Fin j → ℝ) :=
    fun x i => Sum.elim (H x i) ((1 : Matrix (Fin j) (Fin j) ℝ) i)
  let B : Matrix (binary_string n) (binary_string n) ℝ :=
    fun x y => Matrix.det (fun s => Sum.elim (rows x) (rows y) s)
  rw [query_support_rank_at_most]
  refine ⟨B, ?_, ?_⟩
  · intro x y
    change Matrix.det (Matrix.fromBlocks (H x) 1 (H y) 1) = 0 ↔
      decide (j ≤ hammingDist x y) = false
    rw [block_determinant_zero_iff, hH]
    simp
  · exact block_determinant_kernel_rank j rows rows

@[blueprint "lem:exact-hamming-threshold-oracle-tree"
  (statement := /-- There exists an absolute natural number $c$ such that, for every $n,k\in\mathbb{N}$, there is an oracle tree $T$ on pairs of length-$n$ binary strings with the following properties:
  \[
    T(x,y)=\mathsf{HD}_k^n(x,y)
      \quad\text{for every }x,y,
  \]
  the depth of $T$ is at most $2$, and every query in $T$ has support-rank at most $2^{c(k+1)}$. -/)
  (proof := /-- Take the absolute constant $c=2$. Fix $n,k\in\mathbb{N}$ and, for each $j$, let $Q_j(x,y)$ assert that $j\leq d_H(x,y)$. Construct the tree from \cref{def:oracle-tree} that first queries $Q_k$, returns false after a false answer, and after a true answer queries $Q_{k+1}$ and returns true exactly when that second answer is false. By \cref{def:oracle-tree-evaluation}, its value is true precisely when $k\leq d_H(x,y)<k+1$, equivalently when $d_H(x,y)=k$; this is \cref{def:exact-hamming-matrix}. Its depth is $2$ by \cref{def:oracle-tree-depth}.

  By \cref{lem:hamming-threshold-query-support-rank}, $Q_k$ and $Q_{k+1}$ have support-rank at most $4^k$ and $4^{k+1}$, respectively. Since $4^{k+1}=2^{2(k+1)}$ and $4^k\leq4^{k+1}$, unpacking \cref{def:query-support-rank-at-most} supplies witnesses for both queries with the common bound $2^{2(k+1)}$. Recursing through the two internal nodes gives \cref{def:oracle-tree-support-rank-at-most}, completing the construction. -/)
  (title := /-- A threshold oracle tree for exact Hamming distance -/)
  (latexEnv := "lemma")]
lemma exact_hamming_threshold_oracle_tree :
    ∃ c : ℕ, ∀ n k : ℕ,
      ∃ T : oracle_tree (binary_string n) (binary_string n),
        (∀ x y,
          oracle_tree_evaluation T x y = exact_hamming_matrix n k x y) ∧
        oracle_tree_depth T ≤ 2 ∧
        oracle_tree_support_rank_at_most T (2 ^ (c * (k + 1))) := by
  refine ⟨2, ?_⟩
  intro n k
  let Q : ℕ → Matrix (binary_string n) (binary_string n) Bool :=
    fun j x y => decide (j ≤ hammingDist x y)
  let T : oracle_tree (binary_string n) (binary_string n) :=
    oracle_tree.query (Q k) (oracle_tree.leaf false)
      (oracle_tree.query (Q (k + 1)) (oracle_tree.leaf true)
        (oracle_tree.leaf false))
  refine ⟨T, ?_, ?_, ?_⟩
  · intro x y
    simp only [T, Q, oracle_tree_evaluation, exact_hamming_matrix]
    by_cases h : hammingDist x y = k <;> simp [h] <;> omega
  · simp [T, oracle_tree_depth]
  · have hpow : 4 ^ (k + 1) = 2 ^ (2 * (k + 1)) := by
      rw [show 4 = 2 ^ 2 by norm_num, pow_mul]
    have hk := hamming_threshold_query_support_rank n k
    have hk1 := hamming_threshold_query_support_rank n (k + 1)
    rw [query_support_rank_at_most] at hk hk1
    rcases hk with ⟨Bk, hBk, hrk⟩
    rcases hk1 with ⟨Bk1, hBk1, hrk1⟩
    simp only [T, oracle_tree_support_rank_at_most, Q]
    constructor
    · exact ⟨Bk, hBk, hrk.trans (by
        rw [← hpow, pow_succ]
        omega)⟩
    · constructor
      · trivial
      · exact ⟨⟨Bk1, hBk1, by simpa [hpow] using hrk1⟩, trivial, trivial⟩

@[blueprint "thm:sign-rank-of-exact-hamming-distance"
  (statement := /-- There exists an absolute natural number $c$ such that, for all $n,k\in\mathbb{N}$, the sign-rank of the exact $k$-Hamming-distance matrix on length-$n$ binary strings satisfies
  \[
    \operatorname{signrank}(\mathsf{HD}_k^n)
      \leq 2^{c(k+1)}.
  \]
  This is a uniform $2^{O(k)}$ bound, independent of $n$; the additive constant in the exponent accounts for a uniform multiplicative constant, including at $k=0$. -/)
  (proof := /-- Let $c_0$ be the absolute constant supplied by \cref{lem:exact-hamming-threshold-oracle-tree}, and fix $n,k\in\mathbb{N}$. Choose the resulting oracle tree $T$, and set
  \[
    r=2^{c_0(k+1)}.
  \]
  The tree computes $\mathsf{HD}_k^n$ pointwise, has depth at most $2$, and has support-rank at most $r$. The pointwise equality and \cref{lem:sign-rank-congr} identify the sign-rank of $\mathsf{HD}_k^n$ with that of the evaluation of $T$. Applying \cref{lem:oracle-tree-sign-rank-bound}, and then using the depth bound, gives
  \[
    \operatorname{signrank}(\mathsf{HD}_k^n)
      \leq (1+r^2)^{\operatorname{depth}(T)}
      \leq (1+r^2)^2.
  \]
  Since $r\geq1$ and $k+1\geq1$, one has
  \[
    1+r^2
      \leq2r^2
      =2^{2c_0(k+1)+1}
      \leq2^{(2c_0+1)(k+1)}.
  \]
  Squaring this inequality yields
  \[
    \operatorname{signrank}(\mathsf{HD}_k^n)
      \leq2^{(4c_0+2)(k+1)}.
  \]
  Thus the absolute natural number $c=4c_0+2$, independent of $n$ and $k$, satisfies the asserted bound. -/)
  (title := /-- Sign-rank of exact Hamming distance -/)
  (latexEnv := "theorem")]
theorem sign_rank_of_exact_hamming_distance :
    ∃ c : ℕ, ∀ n k : ℕ,
      sign_rank (exact_hamming_matrix n k) ≤ 2 ^ (c * (k + 1)) := by
  obtain ⟨c₀, hc₀⟩ := exact_hamming_threshold_oracle_tree
  refine ⟨4 * c₀ + 2, ?_⟩
  intro n k
  obtain ⟨T, hEval, hDepth, hSupport⟩ := hc₀ n k
  let r := 2 ^ (c₀ * (k + 1))
  have hrpos : 0 < r := by
    positivity
  have hr_sq_pos : 0 < r ^ 2 := by
    positivity
  have hbase : 0 < 1 + r ^ 2 := by
    positivity
  have hdepth : (1 + r ^ 2) ^ oracle_tree_depth T ≤
      (1 + r ^ 2) ^ 2 :=
    Nat.pow_le_pow_right hbase hDepth
  have hexponent : 2 * (c₀ * (k + 1)) + 1 ≤
      (2 * c₀ + 1) * (k + 1) := by
    nlinarith
  have hr_sq : r ^ 2 = 2 ^ (2 * (c₀ * (k + 1))) := by
    simp only [r]
    rw [← pow_mul]
    congr 1
    ring
  have hinner : 1 + r ^ 2 ≤ 2 ^ ((2 * c₀ + 1) * (k + 1)) := by
    calc
      1 + r ^ 2 ≤ r ^ 2 + r ^ 2 := by omega
      _ = 2 * r ^ 2 := by ring
      _ = 2 ^ (2 * (c₀ * (k + 1)) + 1) := by
        rw [hr_sq, pow_succ]
        ring
      _ ≤ 2 ^ ((2 * c₀ + 1) * (k + 1)) :=
        Nat.pow_le_pow_right (by norm_num) hexponent
  calc
    sign_rank (exact_hamming_matrix n k) =
        sign_rank (fun x y => oracle_tree_evaluation T x y) := by
      apply sign_rank_congr
      intro x y
      exact (hEval x y).symm
    _ ≤ (1 + r ^ 2) ^ oracle_tree_depth T := by
      exact oracle_tree_sign_rank_bound T r hSupport
    _ ≤ (1 + r ^ 2) ^ 2 := hdepth
    _ ≤ (2 ^ ((2 * c₀ + 1) * (k + 1))) ^ 2 :=
      Nat.pow_le_pow_left hinner 2
    _ = 2 ^ ((4 * c₀ + 2) * (k + 1)) := by
      rw [← pow_mul]
      congr 1
      ring

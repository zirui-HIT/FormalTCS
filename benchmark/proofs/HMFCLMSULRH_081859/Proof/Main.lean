import Architect
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.TensorPower.Symmetric
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Lattice.Nat
import Mathlib.RingTheory.MvPolynomial.Basic

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:sparse-vector"
  (statement := /-- A vector $z\in\mathbb R^m$ is $k$-sparse if the set of coordinates on which it is nonzero has cardinality at most $k$. -/)
  (title := /-- Sparse vector -/)
  (latexEnv := "definition")]
def sparse_vector {m : ℕ} (k : ℕ) (z : Fin m → ℝ) : Prop :=
  Set.ncard (Function.support z) ≤ k

@[blueprint "def:unit-cube-vector"
  (statement := /-- A vector $z\in\mathbb R^m$ belongs to the unit cube if $-1\leq z_i\leq 1$ for every $i\in[m]$. -/)
  (title := /-- Unit-cube vector -/)
  (latexEnv := "definition")]
def unit_cube_vector {m : ℕ} (z : Fin m → ℝ) : Prop :=
  ∀ i, z i ∈ Set.Icc (-1 : ℝ) 1

@[blueprint "def:linearly-recovers"
  (statement := /-- For $m,k,d\in\mathbb N$ and $\epsilon\in\mathbb R$, the predicate $\operatorname{LinearlyRecovers}(m,k,d,\epsilon)$ holds if there are matrices $A,B\in\mathbb R^{d\times m}$ such that
  \[
    \left|(B^{\mathsf T}Az)_i-z_i\right|<\epsilon
  \]
  for every $k$-sparse $z\in[-1,1]^m$ and every $i\in[m]$. -/)
  (title := /-- Linear recovery in the sup norm -/)
  (latexEnv := "definition")]
def linearly_recovers (m k d : ℕ) (ε : ℝ) : Prop :=
  ∃ A B : Matrix (Fin d) (Fin m) ℝ,
    ∀ z : Fin m → ℝ,
      sparse_vector k z →
      unit_cube_vector z →
      ∀ i, |((B.transpose * A).mulVec z) i - z i| < ε

@[blueprint "def:embedding-dimension"
  (statement := /-- The quantity $d(m,k,\epsilon)$ is the least natural number $d$ for which $\operatorname{LinearlyRecovers}(m,k,d,\epsilon)$ holds. The infimum convention assigns the value $0$ if the set of admissible dimensions is empty. -/)
  (title := /-- Minimal embedding dimension -/)
  (latexEnv := "definition")]
noncomputable def embedding_dimension (m k : ℕ) (ε : ℝ) : ℕ :=
  sInf {d : ℕ | linearly_recovers m k d ε}

@[blueprint "def:epsilon-threshold"
  (statement := /-- For $m,k\in\mathbb N$, define
  \[
    \tau(m,k)=\frac{\sqrt{k^3}\sqrt5}{\sqrt m}.
  \]
  Since $k$ is nonnegative, this is the paper's quantity $k^{3/2}\sqrt5/\sqrt m$. -/)
  (title := /-- Admissible-error threshold -/)
  (latexEnv := "definition")]
noncomputable def epsilon_threshold (m k : ℕ) : ℝ :=
  Real.sqrt ((k : ℝ) ^ 3) * Real.sqrt 5 / Real.sqrt (m : ℝ)

@[blueprint "def:lower-bound-scale"
  (statement := /-- For $m,k\in\mathbb N$, define the real-valued lower-bound scale
  \[
    L(m,k)=\frac{k^2}{\log k}\log\frac{m}{k}.
  \] -/)
  (title := /-- Lower-bound scale -/)
  (latexEnv := "definition")]
noncomputable def lower_bound_scale (m k : ℕ) : ℝ :=
  ((k : ℝ) ^ 2 / Real.log (k : ℝ)) *
    Real.log ((m : ℝ) / (k : ℝ))

@[blueprint "def:lower-bound-filter"
  (statement := /-- For fixed $\epsilon\in\mathbb R$, let $\mathcal F_\epsilon$ be the joint at-top filter on pairs $(m,k)\in\mathbb N^2$, restricted to the admissible pairs satisfying $\tau(m,k)<\epsilon$. -/)
  (title := /-- Filter of admissible asymptotic parameters -/)
  (latexEnv := "definition")]
def lower_bound_filter (ε : ℝ) : Filter (ℕ × ℕ) :=
  Filter.atTop ⊓
    Filter.principal {p : ℕ × ℕ | epsilon_threshold p.1 p.2 < ε}

@[blueprint "def:binary-vector"
  (statement := /-- A vector $z\in\mathbb R^m$ is binary if $z_i\in\{0,1\}$ for every $i\in[m]$. -/)
  (title := /-- Binary vector -/)
  (latexEnv := "definition")]
def binary_vector {m : ℕ} (z : Fin m → ℝ) : Prop :=
  ∀ i, z i = 0 ∨ z i = 1

@[blueprint "def:threshold-classifies"
  (statement := /-- Matrices $A,B\in\mathbb R^{d\times m}$ and thresholds $t\in\mathbb R^m$ classify $k$-sparse binary vectors when, for every such vector $z$ and every $i\in[m]$,
  \[
    (B^{\mathsf T}Az)_i>t_i
    \quad\Longleftrightarrow\quad z_i=1.
  \] -/)
  (title := /-- Linear threshold classification -/)
  (latexEnv := "definition")]
def threshold_classifies (m k d : ℕ)
    (A B : Matrix (Fin d) (Fin m) ℝ) (t : Fin m → ℝ) : Prop :=
  ∀ (i : Fin m) (z : Fin m → ℝ),
    sparse_vector k z →
    binary_vector z →
    (((B.transpose * A).mulVec z) i > t i ↔ z i = 1)

@[blueprint "def:normalized-threshold-classifies"
  (statement := /-- A threshold classifier is normalized if it classifies all $k$-sparse binary vectors and its correlation matrix $B^{\mathsf T}A$ has every diagonal entry equal to $1$. -/)
  (title := /-- Normalized threshold classification -/)
  (latexEnv := "definition")]
def normalized_threshold_classifies (m k d : ℕ)
    (A B : Matrix (Fin d) (Fin m) ℝ) (t : Fin m → ℝ) : Prop :=
  threshold_classifies m k d A B t ∧
    ∀ i, (B.transpose * A) i i = 1

@[blueprint "def:large-correlation-star"
  (statement := /-- Let $m,k\in\mathbb N$. A matrix $C\in\mathbb R^{m\times m}$ has a large $k$-correlation star if there exist $i\in[m]$ and $T^*\subseteq[m]\setminus\{i\}$ with $|T^*|=2k$ such that
  \[
    |C_{ij}|\geq \frac{2}{k}
  \]
  for every $j\in T^*$. -/)
  (title := /-- Large correlation star -/)
  (latexEnv := "definition")]
def large_correlation_star {m : ℕ} (k : ℕ)
    (C : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  ∃ (i : Fin m) (T : Finset (Fin m)),
    T.card = 2 * k ∧
      i ∉ T ∧
      ∀ j ∈ T, (2 : ℝ) / (k : ℝ) ≤ |C i j|

@[blueprint "lem:normalize-threshold-classifier"
  (statement := /-- Let $m,k,d\in\mathbb N$ with $1\leq k$. If $A,B\in\mathbb R^{d\times m}$ and $t\in\mathbb R^m$ classify all $k$-sparse binary vectors, then there are $B'\in\mathbb R^{d\times m}$ and $t'\in\mathbb R^m$ for which $(A,B',t')$ is a normalized threshold classifier. -/)
  (proof := /-- For each $i$, apply the classification equivalence from \cref{def:threshold-classifies} first to the zero vector and then to the $i$th coordinate vector. These two tests give $0\leq t_i<(B^{\mathsf T}A)_{ii}$, so the diagonal entry is positive. Scale the $i$th column of $B$ and the threshold $t_i$ by the reciprocal of this diagonal entry. Positive scaling preserves both directions of every threshold equivalence and makes the $i$th diagonal entry equal to $1$. Performing this independently for all $i$ gives the data required by \cref{def:normalized-threshold-classifies}. -/)
  (title := /-- Normalize the threshold classifier -/)
  (latexEnv := "lemma")]
lemma normalize_threshold_classifier {m k d : ℕ}
    {A B : Matrix (Fin d) (Fin m) ℝ} {t : Fin m → ℝ}
    (hk : 1 ≤ k) (hclass : threshold_classifies m k d A B t) :
    ∃ (B' : Matrix (Fin d) (Fin m) ℝ) (t' : Fin m → ℝ),
      normalized_threshold_classifies m k d A B' t' := by
  classical
  let q : Fin m → ℝ := fun i => (B.transpose * A) i i
  have hq (i : Fin m) : 0 < q i := by
    have hz := hclass i 0 (by simp [sparse_vector]) (by simp [binary_vector])
    have hs : sparse_vector k (Pi.single i (1 : ℝ)) := by
      simp [sparse_vector, Pi.support_single, hk]
    have hb : binary_vector (Pi.single i (1 : ℝ)) := by
      intro j
      by_cases hji : j = i
      · right
        subst j
        simp
      · left
        simp [Pi.single, hji]
    have he := hclass i (Pi.single i 1) hs hb
    simp [Matrix.mulVec_single_one] at hz he
    change 0 < (B.transpose * A) i i
    exact lt_of_le_of_lt hz he
  let B' : Matrix (Fin d) (Fin m) ℝ := fun x i => (q i)⁻¹ * B x i
  let t' : Fin m → ℝ := fun i => (q i)⁻¹ * t i
  have hentry (i j : Fin m) :
      (B'.transpose * A) i j = (q i)⁻¹ * (B.transpose * A) i j := by
    simp [B', Matrix.mul_apply, ← Finset.mul_sum, mul_assoc]
  have hmul (i : Fin m) (z : Fin m → ℝ) :
      ((B'.transpose * A).mulVec z) i =
        (q i)⁻¹ * (((B.transpose * A).mulVec z) i) := by
    simp [Matrix.mulVec, dotProduct, hentry, ← Finset.mul_sum, mul_assoc]
  refine ⟨B', t', ?_, ?_⟩
  · intro i z hs hb
    rw [hmul]
    change ((q i)⁻¹ * t i < (q i)⁻¹ * ((B.transpose * A).mulVec z) i ↔ z i = 1)
    rw [mul_lt_mul_iff_right₀ (inv_pos.mpr (hq i))]
    exact hclass i z hs hb
  · intro i
    rw [hentry]
    change (q i)⁻¹ * q i = 1
    exact inv_mul_cancel₀ (hq i).ne'

@[blueprint "lem:alon-hermitian-sum-sq-eigenvalues"
  (statement := /-- For a real Hermitian matrix, the sum of the squares of its eigenvalues equals the sum of the squares of all its entries. -/)
  (proof := /-- Diagonalize the matrix by the Hermitian spectral theorem. The trace of its square is invariant under the resulting unitary conjugation and is therefore the sum of the squared eigenvalues. Expanding the same trace entrywise and using Hermitian symmetry gives the sum of the squared entries. -/)
  (title := /-- Frobenius identity for a Hermitian matrix -/)
  (latexEnv := "lemma")]
lemma alon_hermitian_sum_sq_eigenvalues {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    (∑ i, (hA.eigenvalues i) ^ 2) = ∑ i, ∑ j, (A i j) ^ 2 := by
  classical
  have hsymm (i j : Fin n) : A j i = A i j := by
    simpa using hA.apply i j
  let eig : Fin n → ℝ := hA.eigenvalues
  change (∑ i, (eig i) ^ 2) = ∑ i, ∑ j, (A i j) ^ 2
  calc
    (∑ i, (eig i) ^ 2) =
        (Matrix.diagonal eig * Matrix.diagonal eig).trace := by
          simp [Matrix.trace, Matrix.mul_apply, pow_two]
    _ = (A * A).trace := by
      have hspec : A =
          Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary (Matrix.diagonal eig) := by
        simpa [eig] using hA.spectral_theorem
      rw [hspec]
      rw [← map_mul]
      simp only [Unitary.conjStarAlgAut_apply]
      rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]
    _ = ∑ i, ∑ j, (A i j) ^ 2 := by
      rw [Matrix.trace]
      apply Finset.sum_congr rfl
      intro i _
      change (A * A) i i = _
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [hsymm]
      rw [pow_two]

@[blueprint "lem:alon-hermitian-rank-bound"
  (statement := /-- For a real Hermitian matrix $A$, the square of the sum of its diagonal entries is at most its rank times the sum of the squares of all its entries. -/)
  (proof := /-- By the Hermitian spectral theorem, the trace is the sum of the eigenvalues and the rank is the number of nonzero eigenvalues. Apply Cauchy--Schwarz on that support, enlarge the resulting sum of squares to all eigenvalues, and invoke \cref{lem:alon-hermitian-sum-sq-eigenvalues}. -/)
  (title := /-- Rank bound from trace and Frobenius mass -/)
  (latexEnv := "lemma")]
lemma alon_hermitian_rank_bound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    (∑ i, A i i) ^ 2 ≤
      (A.rank : ℝ) * (∑ i, ∑ j, (A i j) ^ 2) := by
  classical
  let support : Finset (Fin n) := Finset.univ.filter fun i => hA.eigenvalues i ≠ 0
  have hsum : (∑ i ∈ support, hA.eigenvalues i) = ∑ i, hA.eigenvalues i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, not_ne_iff] at hi
    exact hi
  have hrank : support.card = A.rank := by
    rw [hA.rank_eq_rank_diagonal, Matrix.rank_diagonal]
    rw [Fintype.card_subtype]
  have hsquares :
      (∑ i ∈ support, (hA.eigenvalues i) ^ 2) ≤
        ∑ i, (hA.eigenvalues i) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro i _ _
    positivity
  change A.trace ^ 2 ≤ _
  rw [Matrix.trace]
  have htrace : (∑ i, A.diag i) = ∑ i, hA.eigenvalues i := by
    simpa [Matrix.trace] using hA.trace_eq_sum_eigenvalues
  calc
    (∑ i, A.diag i) ^ 2 = (∑ i ∈ support, hA.eigenvalues i) ^ 2 := by
      rw [hsum, htrace]
    _ ≤ (support.card : ℝ) * ∑ i ∈ support, (hA.eigenvalues i) ^ 2 := by
      simpa using
        (Finset.sum_mul_sq_le_sq_mul_sq support (fun _ => (1 : ℝ))
          (fun i => hA.eigenvalues i))
    _ ≤ (A.rank : ℝ) * ∑ i, (hA.eigenvalues i) ^ 2 := by
      rw [hrank]
      exact mul_le_mul_of_nonneg_left hsquares (Nat.cast_nonneg _)
    _ = (A.rank : ℝ) * (∑ i, ∑ j, (A i j) ^ 2) := by
      rw [alon_hermitian_sum_sq_eigenvalues A hA]

@[blueprint "lem:alon-card-symmetric-power"
  (statement := /-- The number of multisets of cardinality $s$ drawn from an $r$-element type is the multichoose coefficient $\binom{r+s-1}{s}$. -/)
  (proof := /-- Induct first on the multiset cardinality and then on the size of the underlying finite type. For the successor step, partition the multisets according to whether they contain zero. Erasing one zero identifies the first part with multisets of cardinality one less, while decrementing every entry identifies the complementary part with multisets on the smaller finite type. The resulting cardinality recurrence is the multichoose recurrence. -/)
  (title := /-- Cardinality of a finite symmetric power -/)
  (latexEnv := "lemma")]
lemma alon_card_symmetric_power :
    ∀ r s : ℕ, Fintype.card (Sym (Fin r) s) = Nat.multichoose r s := by
  intro r s
  induction s generalizing r with
  | zero => simp
  | succ s ihs =>
    induction r with
    | zero => simp
    | succ r ihr =>
      cases r with
      | zero => simp
      | succ r =>
        let eraseZero : {x : Sym (Fin (r + 2)) (s + 1) // (0 : Fin (r + 2)) ∈ x} ≃
            Sym (Fin (r + 2)) s :=
          { toFun := fun x => x.1.erase 0 x.2
            invFun := fun x => ⟨Sym.cons 0 x, Sym.mem_cons_self 0 x⟩
            left_inv := by intro x; simp
            right_inv := by intro x; simp }
        let avoidZero : {x : Sym (Fin (r + 2)) (s + 1) // (0 : Fin (r + 2)) ∉ x} ≃
            Sym (Fin (r + 1)) (s + 1) :=
          { toFun := fun x => Sym.map (Fin.predAbove (0 : Fin (r + 1))) x.1
            invFun := fun x =>
              ⟨Sym.map (Fin.succAbove (0 : Fin (r + 2))) x,
                (mt Sym.mem_map.1) (not_exists.2 fun t =>
                  not_and.2 fun _ => Fin.succAbove_ne (0 : Fin (r + 2)) t)⟩
            left_inv := by
              intro x
              ext1
              simp only [Sym.map_map]
              refine (Sym.map_congr fun v hv => ?_).trans (Sym.map_id' _)
              exact Fin.succAbove_predAbove (ne_of_mem_of_not_mem hv x.2)
            right_inv := by
              intro x
              simp only [Sym.map_map, Function.comp_apply, ← Fin.castSucc_zero,
                Fin.predAbove_succAbove, Sym.map_id'] }
        rw [Nat.multichoose_succ_succ, ← ihr, ← ihs (r + 2),
          add_comm (Fintype.card _), ← Fintype.card_sum]
        refine Fintype.card_congr (Equiv.symm ?_)
        exact (eraseZero.symm.sumCongr avoidZero.symm).trans
          (Equiv.sumCompl fun x : Sym (Fin (r + 2)) (s + 1) => (0 : Fin (r + 2)) ∈ x)

@[blueprint "lem:alon-bounded-polynomial-finrank"
  (statement := /-- The real vector space of polynomials in $r$ variables of total degree at most $s$ has dimension at most the multichoose coefficient for $r+1$ variables and degree $s$. -/)
  (proof := /-- The canonical monomial basis is indexed by exponent vectors of total mass at most $s$. Add a slack coordinate equal to $s$ minus that mass; this injects the index type into the symmetric power of an $(r+1)$-element type. Apply \cref{lem:alon-card-symmetric-power} to count the latter. -/)
  (title := /-- Dimension of bounded-degree multivariate polynomials -/)
  (latexEnv := "lemma")]
lemma alon_bounded_polynomial_finrank (r s : ℕ) :
    Module.finrank ℝ (MvPolynomial.restrictTotalDegree (Fin r) ℝ s) ≤
      Nat.multichoose (r + 1) s := by
  classical
  let Index := {d : Fin r →₀ ℕ // d.sum (fun _ e => e) ≤ s}
  let mass : Index → Fin (r + 1) → ℕ := fun d =>
    Fin.cases (s - d.1.sum (fun _ e => e)) (fun i => d.1 i)
  have hmass (d : Index) : ∑ i, mass d i = s := by
    have hd := d.2
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hd
    rw [Fin.sum_univ_succ]
    simp only [mass, Fin.cases_zero, Fin.cases_succ]
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    omega
  let encode : Index → Sym (Fin (r + 1)) s := fun d =>
    (Sym.equivNatSumOfFintype (α := Fin (r + 1)) s).symm ⟨mass d, hmass d⟩
  have hencode : Function.Injective encode := by
    intro a b hab
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    have h := congrArg
      (fun z => ((Sym.equivNatSumOfFintype (α := Fin (r + 1)) s) z).1 i.succ) hab
    simpa [encode, mass] using h
  letI : Fintype Index := Fintype.ofInjective encode hencode
  have hdim :
      Module.finrank ℝ (MvPolynomial.restrictTotalDegree (Fin r) ℝ s) =
        Fintype.card Index := by
    exact Module.finrank_eq_card_basis
      (MvPolynomial.basisRestrictSupport ℝ
        {d : Fin r →₀ ℕ | d.sum (fun _ e => e) ≤ s})
  rw [hdim, ← alon_card_symmetric_power (r + 1) s]
  exact Fintype.card_le_of_injective encode hencode

@[blueprint "lem:alon-entrywise-power-rank"
  (statement := /-- If $C$ is a real square matrix and $C^{\circ s}$ is its entrywise $s$th power, then
  \[
    \operatorname{rank}(C^{\circ s})
      \leq \binom{\operatorname{rank}(C)+s}{s}.
  \] -/)
  (proof := /-- Choose a basis of the column space of $C$. Each matrix entry is the evaluation of a linear polynomial in the corresponding column coordinates, so each row of $C^{\circ s}$ is obtained by evaluating a polynomial of total degree at most $s$. Thus the row space is a linear image of the bounded-degree polynomial space. Apply \cref{lem:alon-bounded-polynomial-finrank} to bound its dimension. -/)
  (title := /-- Rank of an entrywise matrix power -/)
  (latexEnv := "lemma")]
lemma alon_entrywise_power_rank {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (s : ℕ) :
    Matrix.rank (fun i j => (C i j) ^ s : Matrix (Fin n) (Fin n) ℝ) ≤
      Nat.multichoose (C.rank + 1) s := by
  classical
  let V : Submodule ℝ (Fin n → ℝ) := LinearMap.range C.mulVecLin
  let basis : Module.Basis (Fin C.rank) ℝ V := Module.finBasis ℝ V
  let column (j : Fin n) : V :=
    ⟨fun i => C i j, ⟨Pi.single j 1, by ext i; simp [Matrix.mulVec_single_one]⟩⟩
  let coord (j : Fin n) (l : Fin C.rank) : ℝ := basis.repr (column j) l
  have hcolumn (i j : Fin n) :
      C i j = ∑ l, coord j l * (basis l : Fin n → ℝ) i := by
    have h := basis.sum_repr (column j)
    have hv := congrArg (fun v : V => V.subtype v) h
    rw [map_sum] at hv
    have hi := congrFun hv i
    simpa [coord, column, mul_comm] using hi.symm
  let linearPolynomial (i : Fin n) : MvPolynomial (Fin C.rank) ℝ :=
    ∑ l, ((basis l : Fin n → ℝ) i) • MvPolynomial.X l
  have hlinearPolynomial (i : Fin n) : (linearPolynomial i).totalDegree ≤ 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro l _
    exact (MvPolynomial.totalDegree_smul_le _ _).trans_eq
      (MvPolynomial.totalDegree_X l)
  let polynomial (i : Fin n) : MvPolynomial (Fin C.rank) ℝ :=
    (linearPolynomial i) ^ s
  have hpolynomial (i : Fin n) : (polynomial i).totalDegree ≤ s := by
    exact (MvPolynomial.totalDegree_pow _ _).trans (by
      simpa using Nat.mul_le_mul_left s (hlinearPolynomial i))
  let P := MvPolynomial.restrictTotalDegree (Fin C.rank) ℝ s
  let polynomialInP (i : Fin n) : P :=
    ⟨polynomial i,
      (MvPolynomial.mem_restrictTotalDegree (σ := Fin C.rank) (R := ℝ) s
        (polynomial i)).2 (hpolynomial i)⟩
  let evaluate : P →ₗ[ℝ] (Fin n → ℝ) :=
    LinearMap.pi fun j =>
      (MvPolynomial.eval₂AlgHom (R := ℝ) (S₁ := ℝ) (coord j)).toLinearMap.comp P.subtype
  have hevaluate (i : Fin n) :
      evaluate (polynomialInP i) = fun j => (C i j) ^ s := by
    funext j
    change MvPolynomial.eval₂AlgHom (R := ℝ) (S₁ := ℝ) (coord j)
        (linearPolynomial i ^ s) =
      (C i j) ^ s
    rw [map_pow]
    apply congrArg (fun x : ℝ => x ^ s)
    simp only [linearPolynomial, map_sum, map_smul, MvPolynomial.eval₂AlgHom_X]
    rw [hcolumn]
    simp [mul_comm]
  let D : Matrix (Fin n) (Fin n) ℝ := fun i j => (C i j) ^ s
  have hspan : Submodule.span ℝ (Set.range D.row) ≤ LinearMap.range evaluate := by
    apply Submodule.span_le.2
    intro v hv
    rcases hv with ⟨i, rfl⟩
    refine ⟨polynomialInP i, ?_⟩
    change evaluate (polynomialInP i) = fun j => D i j
    simpa [D] using hevaluate i
  rw [show (fun i j => (C i j) ^ s : Matrix (Fin n) (Fin n) ℝ) = D from rfl,
    Matrix.rank_eq_finrank_span_row]
  calc
    Module.finrank ℝ (Submodule.span ℝ (Set.range D.row)) ≤
        Module.finrank ℝ (LinearMap.range evaluate) :=
      Submodule.finrank_mono hspan
    _ ≤ Module.finrank ℝ P := LinearMap.finrank_range_le evaluate
    _ ≤ Nat.multichoose (C.rank + 1) s := alon_bounded_polynomial_finrank C.rank s

@[blueprint "lem:alon-general-rank-bound"
  (statement := /-- For every real square matrix $D$, the square of its trace is at most twice its rank times the sum of the squares of all its entries. -/)
  (proof := /-- Apply \cref{lem:alon-hermitian-rank-bound} to the Hermitian matrix $S=D+D^{\mathsf T}$. Its trace is twice that of $D$, its rank is at most twice the rank of $D$, and the inequality $(x+y)^2\leq2x^2+2y^2$ bounds its squared Frobenius mass by four times that of $D$. Dividing the resulting inequality by four gives the claim. -/)
  (title := /-- Trace--Frobenius bound for an arbitrary matrix -/)
  (latexEnv := "lemma")]
lemma alon_general_rank_bound {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, D i i) ^ 2 ≤
      2 * (D.rank : ℝ) * (∑ i, ∑ j, (D i j) ^ 2) := by
  classical
  let S : Matrix (Fin n) (Fin n) ℝ := D + D.transpose
  have hS : S.IsHermitian := by
    unfold Matrix.IsHermitian
    simp [S, Matrix.conjTranspose_apply, add_comm]
  have hspan :
      Submodule.span ℝ (Set.range S.col) ≤
        Submodule.span ℝ (Set.range D.col) ⊔
          Submodule.span ℝ (Set.range D.transpose.col) := by
    apply Submodule.span_le.2
    intro v hv
    rcases hv with ⟨j, rfl⟩
    change D.col j + D.transpose.col j ∈ _
    exact Submodule.add_mem _
      (show D.col j ∈ _ ⊔ _ from
        (show Submodule.span ℝ (Set.range D.col) ≤ _ from le_sup_left)
          (Submodule.subset_span (Set.mem_range_self j)))
      (show D.transpose.col j ∈ _ ⊔ _ from
        (show Submodule.span ℝ (Set.range D.transpose.col) ≤ _ from le_sup_right)
          (Submodule.subset_span (Set.mem_range_self j)))
  have hrank : S.rank ≤ 2 * D.rank := by
    rw [Matrix.rank_eq_finrank_span_cols, mul_comm]
    calc
      Module.finrank ℝ (Submodule.span ℝ (Set.range S.col)) ≤
          Module.finrank ℝ
            ((Submodule.span ℝ (Set.range D.col) ⊔
              Submodule.span ℝ (Set.range D.transpose.col)) :
                Submodule ℝ (Fin n → ℝ)) :=
        Submodule.finrank_mono hspan
      _ ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range D.col)) +
          Module.finrank ℝ (Submodule.span ℝ (Set.range D.transpose.col)) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
      _ = D.rank + D.transpose.rank := by
        rw [← Matrix.rank_eq_finrank_span_cols, ← Matrix.rank_eq_finrank_span_cols]
      _ = D.rank + D.rank := by rw [Matrix.rank_transpose]
      _ = D.rank * 2 := by omega
  have hdiag : (∑ i, S i i) = 2 * ∑ i, D i i := by
    simp only [S, add_apply, Matrix.transpose_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change D i i + D i i = 2 * D i i
    ring
  have hmass :
      (∑ i, ∑ j, (S i j) ^ 2) ≤ 4 * ∑ i, ∑ j, (D i j) ^ 2 := by
    calc
      (∑ i, ∑ j, (S i j) ^ 2) ≤
          ∑ i, ∑ j, (2 * (D i j) ^ 2 + 2 * (D j i) ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        dsimp [S]
        change (D i j + D j i) ^ 2 ≤ 2 * D i j ^ 2 + 2 * D j i ^ 2
        nlinarith [sq_nonneg (D i j - D j i)]
      _ = 4 * ∑ i, ∑ j, (D i j) ^ 2 := by
        have hswap : (∑ i, ∑ j, (D j i) ^ 2) = ∑ i, ∑ j, (D i j) ^ 2 := by
          rw [Finset.sum_comm]
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [hswap]
        ring
  have hrankR : (S.rank : ℝ) ≤ 2 * (D.rank : ℝ) := by
    exact_mod_cast hrank
  have hmass_nonneg : 0 ≤ ∑ i, ∑ j, (S i j) ^ 2 := by positivity
  have hDmass_nonneg : 0 ≤ ∑ i, ∑ j, (D i j) ^ 2 := by positivity
  have hproduct :
      (S.rank : ℝ) * (∑ i, ∑ j, (S i j) ^ 2) ≤
        (2 * (D.rank : ℝ)) * (4 * ∑ i, ∑ j, (D i j) ^ 2) := by
    exact mul_le_mul hrankR hmass hmass_nonneg (by positivity)
  have h := alon_hermitian_rank_bound S hS
  rw [hdiag] at h
  nlinarith

@[blueprint "lem:alon-power-factorial-bound"
  (statement := /-- For every natural number $s$, one has $s^s\leq 3^s s!$. -/)
  (proof := /-- The exponential-series estimate gives $s^s/s!\leq e^s$. The elementary exponential bound $e\leq3$ therefore gives $s^s/s!\leq3^s$; multiplication by the positive number $s!$ proves the claim. -/)
  (title := /-- A factorial lower bound with constant three -/)
  (latexEnv := "lemma")]
lemma alon_power_factorial_bound (s : ℕ) : s ^ s ≤ 3 ^ s * s.factorial := by
  have hseries :
      (s : ℝ) ^ s / (s.factorial : ℝ) ≤ Real.exp (s : ℝ) :=
    Real.pow_div_factorial_le_exp (x := (s : ℝ)) (by positivity) s
  have hexp : Real.exp (s : ℝ) = (Real.exp 1) ^ s := by
    rw [← Real.exp_nat_mul]
    simp
  have hone : Real.exp 1 ≤ 3 := by
    have h := Real.exp_le_two_add_div_two_sub (x := (1 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  have hreal : (s : ℝ) ^ s ≤ 3 ^ s * (s.factorial : ℝ) := by
    calc
      (s : ℝ) ^ s = ((s : ℝ) ^ s / (s.factorial : ℝ)) * (s.factorial : ℝ) := by
        field_simp
      _ ≤ (3 : ℝ) ^ s * (s.factorial : ℝ) := by
        gcongr
        exact hseries.trans (by
          rw [hexp]
          simpa using pow_le_pow_left₀ (Real.exp_pos 1).le hone s)
  exact_mod_cast hreal

@[blueprint "lem:alon-multichoose-upper-bound"
  (statement := /-- If $s>0$, then
  \[
    \binom{r+s}{s}\leq\left(\frac{3(r+s)}s\right)^s.
  \] -/)
  (proof := /-- Rewrite the multichoose coefficient as $\binom{r+s}{s}$ and apply the standard bound $\binom{r+s}{s}\leq(r+s)^s/s!$. The factorial estimate \cref{lem:alon-power-factorial-bound} gives $s^s\leq3^s s!$; multiplying this inequality by $(r+s)^s$ and dividing by the positive quantities $s!$ and $s^s$ yields the displayed estimate. -/)
  (title := /-- A uniform upper bound for multichoose coefficients -/)
  (latexEnv := "lemma")]
lemma alon_multichoose_upper_bound (r s : ℕ) (hs : 0 < s) :
    (Nat.multichoose (r + 1) s : ℝ) ≤
      (3 * ((r + s : ℕ) : ℝ) / (s : ℝ)) ^ s := by
  have hrewrite : r + 1 + s - 1 = r + s := by omega
  rw [Nat.multichoose_eq, hrewrite]
  have hfacNat := alon_power_factorial_bound s
  have hfac : (s : ℝ) ^ s ≤ 3 ^ s * (s.factorial : ℝ) := by exact_mod_cast hfacNat
  have hsfac : (0 : ℝ) < (s.factorial : ℕ) := by exact_mod_cast Nat.factorial_pos s
  have hspow : (0 : ℝ) < (s : ℝ) ^ s := by positivity
  calc
    ((r + s).choose s : ℝ) ≤ ((r + s : ℕ) : ℝ) ^ s / (s.factorial : ℕ) :=
      Nat.choose_le_pow_div s (r + s)
    _ ≤ (3 ^ s * ((r + s : ℕ) : ℝ) ^ s) / (s : ℝ) ^ s := by
      apply (div_le_div_iff₀ hsfac hspow).2
      have := mul_le_mul_of_nonneg_left hfac
        (pow_nonneg (show (0 : ℝ) ≤ ((r + s : ℕ) : ℝ) by positivity) s)
      nlinarith
    _ = (3 * ((r + s : ℕ) : ℝ) / (s : ℝ)) ^ s := by
      rw [div_pow, mul_pow]

@[blueprint "lem:alon-entrywise-power-rank-lower"
  (statement := /-- Let $C$ be a real $n\times n$ matrix with unit diagonal and off-diagonal entries of absolute value less than $\varepsilon$. If $n>0$ and $\varepsilon\geq0$, then the entrywise $s$th power $D$ satisfies
  \[
    n\leq2\operatorname{rank}(D)(1+n\varepsilon^{2s}).
  \] -/)
  (proof := /-- Put $D_{ij}=C_{ij}^s$. Its trace is $n$. Each diagonal contribution to its squared Frobenius mass is $1$, while every off-diagonal contribution is at most $\varepsilon^{2s}$; hence the total mass is at most $n(1+n\varepsilon^{2s})$. Apply \cref{lem:alon-general-rank-bound} to $D$ and cancel the positive factor $n$. -/)
  (title := /-- Rank lower bound for an entrywise power -/)
  (latexEnv := "lemma")]
lemma alon_entrywise_power_rank_lower {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (s : ℕ)
    (hn : 0 < n) (hε : 0 ≤ ε) (hdiag : ∀ i, C i i = 1)
    (hoff : ∀ i j, i ≠ j → |C i j| < ε) :
    (n : ℝ) ≤
      2 * (Matrix.rank (fun i j => (C i j) ^ s :
        Matrix (Fin n) (Fin n) ℝ) : ℝ) *
        (1 + (n : ℝ) * ε ^ (2 * s)) := by
  classical
  let D : Matrix (Fin n) (Fin n) ℝ := fun i j => (C i j) ^ s
  have htrace : (∑ i, D i i) = (n : ℝ) := by
    simp [D, hdiag]
  have hentry (i j : Fin n) :
      (D i j) ^ 2 ≤ ε ^ (2 * s) + if i = j then 1 else 0 := by
    by_cases hij : i = j
    · subst j
      simp [D, hdiag]
      positivity
    · simp only [hij, ↓reduceIte, add_zero]
      have habs : |C i j| ≤ ε := (hoff i j hij).le
      have hsq : (C i j) ^ 2 ≤ ε ^ 2 := by
        calc
          (C i j) ^ 2 = |C i j| ^ 2 := (sq_abs (C i j)).symm
          _ ≤ ε ^ 2 := (sq_le_sq₀ (abs_nonneg _) hε).2 habs
      calc
        (D i j) ^ 2 = ((C i j) ^ 2) ^ s := by
          simp only [D]
          rw [← pow_mul, ← pow_mul]
          congr 1
          omega
        _ ≤ (ε ^ 2) ^ s := pow_le_pow_left₀ (sq_nonneg _) hsq s
        _ = ε ^ (2 * s) := by rw [pow_mul]
  have hmass :
      (∑ i, ∑ j, (D i j) ^ 2) ≤
        (n : ℝ) * ((n : ℝ) * ε ^ (2 * s) + 1) := by
    calc
      (∑ i, ∑ j, (D i j) ^ 2) ≤
          ∑ i, ∑ j, (ε ^ (2 * s) + if i = j then 1 else 0) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact hentry i j
      _ = (n : ℝ) * ((n : ℝ) * ε ^ (2 * s) + 1) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        simp
        ring
  have hmass_nonneg : 0 ≤ ∑ i, ∑ j, (D i j) ^ 2 := by positivity
  have hrank_nonneg : (0 : ℝ) ≤ D.rank := by positivity
  have hproduct :
      2 * (D.rank : ℝ) * (∑ i, ∑ j, (D i j) ^ 2) ≤
        2 * (D.rank : ℝ) *
          ((n : ℝ) * ((n : ℝ) * ε ^ (2 * s) + 1)) := by
    exact mul_le_mul_of_nonneg_left hmass (by positivity)
  have hbound := alon_general_rank_bound D
  rw [htrace] at hbound
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  change (n : ℝ) ≤ 2 * (D.rank : ℝ) * (1 + (n : ℝ) * ε ^ (2 * s))
  nlinarith

@[blueprint "lem:alon-rank-obstruction"
  (statement := /-- There is an absolute constant $\alpha>0$ such that the following holds. Let $n,k\in\mathbb N$ satisfy
  \[
    \frac1{\sqrt n}<\frac2k<\frac12,
  \]
  and let $C\in\mathbb R^{n\times n}$ have $C_{ii}=1$ for every $i$. If
  \[
    \operatorname{rank}(C)
      <\alpha\frac{k^2}{\log k}\log n,
  \]
  then some distinct $i,j\in[n]$ satisfy $|C_{ij}|\geq 2/k$. -/)
  (proof := /-- Take $\alpha=1/10000$ and argue by contradiction. Put $q=k/2$, and suppose that every off-diagonal entry has absolute value less than $1/q$. The hypotheses imply $k\geq5$, $q>2$, and $q^2<n$; the strict rank hypothesis also forces $\log n>0$. Set
  \[
    x=\frac{\log n}{2\log q},\qquad s=\lfloor x\rfloor,
    \qquad D_{ij}=C_{ij}^s,qquad Q=q^{2s}.
  \]
  Then $s\geq1$ and $Q\leq n$. Applying \cref{lem:alon-entrywise-power-rank-lower} with $\varepsilon=1/q$ gives
  \[
    n\leq2\operatorname{rank}(D)\left(1+\frac nQ\right).
  \]
  Since $Q\leq n$, multiplication by $Q$ and cancellation of the positive factor $n$ yield $Q\leq4\operatorname{rank}(D)$. On the other hand, \cref{lem:alon-entrywise-power-rank} gives
  \[
    \operatorname{rank}(D)\leq
    \binom{\operatorname{rank}(C)+s}{s}.
  \]
  The inequalities $x<s+1$ and $\log q<\log k$ show that $\log n/\log k<4s$. Consequently the assumed rank bound implies
  \[
    \operatorname{rank}(C)<\frac{k^2s}{2500}.
  \]
  If $s=1$, then $D=C$ and the last inequality, together with $k\geq5$, gives $4\operatorname{rank}(D)<k^2/4=q^2=Q$, contradicting the preceding lower bound. If $s\geq2$, the estimate \cref{lem:alon-multichoose-upper-bound} and the same numerical bounds give
  \[
    \operatorname{rank}(D)leq
    \left(\frac{3(\operatorname{rank}(C)+s)}s\right)^s
    <\left(\frac{q^2}{2}\right)^s.
  \]
  Since $2^s\geq4$, this again gives $4\operatorname{rank}(D)<q^{2s}=Q$, a contradiction. Thus an off-diagonal entry has absolute value at least $2/k$. -/)
  (title := /-- Alon's rank obstruction -/)
  (latexEnv := "lemma")]
lemma alon_rank_obstruction :
    ∃ α : ℝ, 0 < α ∧
      ∀ (n k : ℕ) (C : Matrix (Fin n) (Fin n) ℝ),
        (1 : ℝ) / Real.sqrt (n : ℝ) < (2 : ℝ) / (k : ℝ) →
        (2 : ℝ) / (k : ℝ) < (1 : ℝ) / 2 →
        (∀ i, C i i = 1) →
        (C.rank : ℝ) <
          α * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) *
            Real.log (n : ℝ) →
        ∃ i j, i ≠ j ∧ (2 : ℝ) / (k : ℝ) ≤ |C i j| := by
  refine ⟨(1 : ℝ) / 10000, by norm_num, ?_⟩
  intro n k C hroot hhalf hdiag hrank
  by_contra hconclusion
  have hoff (i j : Fin n) (hij : i ≠ j) : |C i j| < (2 : ℝ) / (k : ℝ) := by
    exact lt_of_not_ge fun h => hconclusion ⟨i, j, hij, h⟩
  have heps_nonneg : 0 ≤ (2 : ℝ) / (k : ℝ) :=
    le_trans (by positivity : 0 ≤ (1 : ℝ) / Real.sqrt (n : ℝ)) hroot.le
  have heps_pos : 0 < (2 : ℝ) / (k : ℝ) :=
    lt_of_le_of_lt (by positivity : 0 ≤ (1 : ℝ) / Real.sqrt (n : ℝ)) hroot
  have hkR : 0 < (k : ℝ) := by
    rcases (div_pos_iff.mp heps_pos) with h | h
    · exact h.2
    · norm_num at h
  have hk4R : (4 : ℝ) < k := by
    have := (div_lt_iff₀ hkR).1 hhalf
    norm_num at this
    nlinarith
  have hk4 : 4 < k := by exact_mod_cast hk4R
  have hk5 : 5 ≤ k := by omega
  have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos (by nlinarith)
  have hrhs :
      0 < ((1 : ℝ) / 10000) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) *
        Real.log (n : ℝ) :=
    lt_of_le_of_lt (Nat.cast_nonneg C.rank) hrank
  have hcoefficient :
      0 < ((1 : ℝ) / 10000) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) := by
    positivity
  have hlogn : 0 < Real.log (n : ℝ) := by
    rcases (mul_pos_iff.mp hrhs) with h | h
    · exact h.2
    · exact False.elim ((not_lt_of_ge hcoefficient.le) h.1)
  have hnR : (1 : ℝ) < n := (Real.log_pos_iff (by positivity)).1 hlogn
  have hn : 0 < n := by exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1) hnR)
  let q : ℝ := (k : ℝ) / 2
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : 1 < q := by dsimp [q]; nlinarith
  have hqk : q < (k : ℝ) := by dsimp [q]; nlinarith
  have hlogq : 0 < Real.log q := Real.log_pos hq1
  have hlogqk : Real.log q < Real.log (k : ℝ) :=
    Real.strictMonoOn_log hq hkR hqk
  have heps : (2 : ℝ) / (k : ℝ) = 1 / q := by
    dsimp [q]
    field_simp
  rw [heps] at hroot hoff
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hqsqrt : q < Real.sqrt (n : ℝ) :=
    (one_div_lt_one_div hsqrt hq).1 hroot
  have hq2n : q ^ 2 < (n : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)]
  have hlogq2n : Real.log (q ^ 2) < Real.log (n : ℝ) :=
    Real.strictMonoOn_log (sq_pos_of_pos hq)
      (lt_trans (sq_pos_of_pos hq) hq2n) hq2n
  rw [Real.log_pow] at hlogq2n
  let x : ℝ := Real.log (n : ℝ) / (2 * Real.log q)
  have hx1 : 1 < x := by
    apply (lt_div_iff₀ (by positivity : 0 < 2 * Real.log q)).2
    norm_num at hlogq2n ⊢
    nlinarith
  let s : ℕ := ⌊x⌋₊
  have hs : 0 < s := by
    exact lt_of_lt_of_le Nat.zero_lt_one
      (Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ x by simpa using hx1.le))
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hs_le_x : (s : ℝ) ≤ x := by
    exact Nat.floor_le (by linarith [hx1])
  have hx_lt_succ : x < (s : ℝ) + 1 := by
    simpa [s] using (Nat.lt_floor_add_one x)
  have hlog_lower : ((2 * s : ℕ) : ℝ) * Real.log q ≤ Real.log (n : ℝ) := by
    have := (le_div_iff₀ (by positivity : 0 < 2 * Real.log q)).1 hs_le_x
    norm_num at this ⊢
    nlinarith
  have hqpow_le_n : q ^ (2 * s) ≤ (n : ℝ) :=
    (Real.pow_le_iff_le_log hq (by positivity)).2 hlog_lower
  have hlog_upper :
      Real.log (n : ℝ) < ((2 * (s + 1) : ℕ) : ℝ) * Real.log q := by
    have := (div_lt_iff₀ (by positivity : 0 < 2 * Real.log q)).1 hx_lt_succ
    norm_num at this ⊢
    nlinarith
  have hlog_ratio : Real.log (n : ℝ) / Real.log (k : ℝ) < 4 * (s : ℝ) := by
    have hsone : (s : ℝ) + 1 ≤ 2 * s := by
      have : (s : ℝ) ≥ 1 := by exact_mod_cast hs
      linarith
    have hmul := mul_lt_mul_of_pos_left hlogqk
      (by positivity : 0 < 2 * ((s : ℝ) + 1))
    apply (div_lt_iff₀ hlogk).2
    norm_num at hlog_upper hmul ⊢
    nlinarith [mul_le_mul_of_nonneg_right hsone hlogk.le]
  have hrscaled :
      (C.rank : ℝ) < (k : ℝ) ^ 2 * (s : ℝ) / 2500 := by
    have hm := mul_lt_mul_of_pos_left hlog_ratio
      (by positivity : 0 < ((1 : ℝ) / 10000) * (k : ℝ) ^ 2)
    calc
      (C.rank : ℝ) <
          ((1 : ℝ) / 10000) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) *
            Real.log (n : ℝ) := hrank
      _ = ((1 : ℝ) / 10000) * (k : ℝ) ^ 2 *
          (Real.log (n : ℝ) / Real.log (k : ℝ)) := by field_simp
      _ < (k : ℝ) ^ 2 * (s : ℝ) / 2500 := by
        norm_num at hm ⊢
        nlinarith
  let D : Matrix (Fin n) (Fin n) ℝ := fun i j => (C i j) ^ s
  have hlower := alon_entrywise_power_rank_lower C (1 / q) s hn
    (by positivity) hdiag hoff
  change (n : ℝ) ≤
      2 * (D.rank : ℝ) * (1 + (n : ℝ) * (1 / q) ^ (2 * s)) at hlower
  let Q : ℝ := q ^ (2 * s)
  have hQpos : 0 < Q := by dsimp [Q]; positivity
  have hQle : Q ≤ (n : ℝ) := by exact hqpow_le_n
  have hrecip_power : (1 / q) ^ (2 * s) = 1 / Q := by
    dsimp [Q]
    rw [div_pow]
    simp
  rw [hrecip_power] at hlower
  have hlowerQ : Q ≤ 4 * (D.rank : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hlower hQpos.le
    have hidentity : (1 + (n : ℝ) * (1 / Q)) * Q = Q + (n : ℝ) := by
      field_simp
    rw [mul_assoc, hidentity] at hmul
    have hnpos : (0 : ℝ) < n := by positivity
    nlinarith
  by_cases hsone : s = 1
  · simp [Q, D, hsone] at hlowerQ
    change q ^ 2 ≤ 4 * (C.rank : ℝ) at hlowerQ
    simp [hsone] at hrscaled
    have hk25 : (25 : ℝ) ≤ (k : ℝ) ^ 2 := by
      have hk5R : (5 : ℝ) ≤ k := by exact_mod_cast hk5
      nlinarith [sq_nonneg ((k : ℝ) - 5)]
    have : 4 * (C.rank : ℝ) < q ^ 2 := by
      dsimp [q]
      norm_num at hrscaled ⊢
      nlinarith only [hrscaled, hk25]
    linarith
  · have hs2 : 2 ≤ s := by omega
    let M : ℕ := Nat.multichoose (C.rank + 1) s
    have hDupper : D.rank ≤ M := by
      exact alon_entrywise_power_rank C s
    have hMlower : Q ≤ 4 * (M : ℝ) := by
      exact hlowerQ.trans (by exact_mod_cast Nat.mul_le_mul_left 4 hDupper)
    have hMupper :
        (M : ℝ) ≤
          (3 * (((C.rank + s : ℕ) : ℝ)) / (s : ℝ)) ^ s := by
      exact alon_multichoose_upper_bound C.rank s hs
    have hk25 : (25 : ℝ) ≤ (k : ℝ) ^ 2 := by
      have hk5R : (5 : ℝ) ≤ k := by exact_mod_cast hk5
      nlinarith [sq_nonneg ((k : ℝ) - 5)]
    have hbase :
        3 * (((C.rank + s : ℕ) : ℝ)) / (s : ℝ) < q ^ 2 / 2 := by
      apply (div_lt_iff₀ hsR).2
      dsimp [q]
      norm_num at hrscaled ⊢
      have hk25s := mul_le_mul_of_nonneg_right hk25 hsR.le
      nlinarith only [hrscaled, hk25s, hsR]
    have hpowbase :
        (3 * (((C.rank + s : ℕ) : ℝ)) / (s : ℝ)) ^ s <
          (q ^ 2 / 2) ^ s := by
      exact pow_lt_pow_left₀ hbase (by positivity) (ne_of_gt hs)
    have htwo : (4 : ℝ) ≤ 2 ^ s := by
      exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) hs2
    have hfinal : 4 * (M : ℝ) < Q := by
      calc
        4 * (M : ℝ) ≤ 4 *
            (3 * (((C.rank + s : ℕ) : ℝ)) / (s : ℝ)) ^ s := by gcongr
        _ < 4 * (q ^ 2 / 2) ^ s := by gcongr
        _ ≤ Q := by
          dsimp [Q]
          rw [div_pow, pow_mul]
          have hqpow : 0 ≤ q ^ (2 * s) := by positivity
          rw [← mul_div_assoc]
          apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ s)).2
          simpa [mul_comm] using
            (mul_le_mul_of_nonneg_right htwo (pow_nonneg (sq_nonneg q) s))
    linarith

@[blueprint "lem:turan-extracts-large-correlation-star"
  (statement := /-- There is an absolute constant $\alpha>0$ such that the following holds for every $m,k\in\mathbb N$. Set
  \[
    r=\left\lfloor\frac{m}{4k+1}\right\rfloor,
  \]
  and assume that
  \[
    r>0,
    \qquad \frac{1}{\sqrt r}<\frac{2}{k}<\frac12.
  \]
  If $C\in\mathbb R^{m\times m}$ satisfies $C_{ii}=1$ for every $i\in[m]$ and
  \[
    \operatorname{rank}(C)
      <\alpha\frac{k^2}{\log k}\log r,
  \]
  then there exist $i\in[m]$ and a set $T\subseteq[m]\setminus\{i\}$ of cardinality $2k$ such that
  \[
    |C_{ij}|\geq\frac{2}{k}
  \]
  for every $j\in T$. -/)
  (proof := /-- Set $r=\lfloor m/(4k+1)\rfloor$ and $\delta=2/k$. Suppose, contrary to \cref{def:large-correlation-star}, that no row has $2k$ distinct off-diagonal entries of absolute value at least $\delta$. For distinct indices $i,j$, write $i\to j$ when $|C_{ij}|\geq\delta$. Thus every vertex has fewer than $2k$ outgoing neighbors.

  Let $S\subseteq[m]$ be nonempty. The number of arrows with both endpoints in $S$ is less than $2k|S|$. Interchanging the two endpoints shows that the sum of the incoming degrees over $S$ equals the sum of the outgoing degrees. Consequently the sum, over $i\in S$, of the number of vertices $j\in S$ for which $i\to j$ or $j\to i$ is less than $4k|S|$. Some $i\in S$ therefore has fewer than $4k$ such neighbors.

  Inductively choose this vertex and delete it together with all its symmetric neighbors. Each step deletes at most $4k+1$ vertices, so the inequality $(4k+1)r\leq m$ yields a set $S$ of cardinality $r$ containing no arrow in either direction between distinct elements. Reindex the principal submatrix $D=C_S$ by $[r]$. Its diagonal is equal to $1$, and restriction to a principal submatrix gives $\operatorname{rank}(D)\leq\operatorname{rank}(C)$. Hence all hypotheses of \cref{lem:alon-rank-obstruction} hold for $D$, which produces distinct $i,j\in S$ with $|C_{ij}|\geq2/k$. This is an arrow inside $S$, contradicting its construction. Therefore a row with at least $2k$ qualifying off-diagonal entries exists; choosing any $2k$ of them gives the set required by \cref{def:large-correlation-star}. -/)
  (title := /-- Extract a large correlation star by a Turán argument -/)
  (latexEnv := "lemma")]
lemma turan_extracts_large_correlation_star :
    ∃ α : ℝ, 0 < α ∧
      ∀ (m k : ℕ) (C : Matrix (Fin m) (Fin m) ℝ),
        0 < m / (4 * k + 1) →
        (1 : ℝ) / Real.sqrt ((m / (4 * k + 1) : ℕ) : ℝ) <
          (2 : ℝ) / (k : ℝ) →
        (2 : ℝ) / (k : ℝ) < (1 : ℝ) / 2 →
        (∀ i, C i i = 1) →
        (C.rank : ℝ) <
          α * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) *
            Real.log ((m / (4 * k + 1) : ℕ) : ℝ) →
        large_correlation_star k C := by
  classical
  rcases alon_rank_obstruction with ⟨α, hα, hAlon⟩
  refine ⟨α, hα, ?_⟩
  intro m k C hr hroot hhalf hdiag hrank
  let r := m / (4 * k + 1)
  let δ : ℝ := (2 : ℝ) / (k : ℝ)
  change 0 < r at hr
  change (1 : ℝ) / Real.sqrt (r : ℝ) < δ at hroot
  change δ < (1 : ℝ) / 2 at hhalf
  change (C.rank : ℝ) <
    α * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) * Real.log (r : ℝ) at hrank
  by_contra hstar
  let R : Fin m → Fin m → Prop := fun i j => i ≠ j ∧ δ ≤ |C i j|
  have hout (i : Fin m) :
      (Finset.univ.filter fun j : Fin m => R i j).card < 2 * k := by
    by_contra hi
    have hle : 2 * k ≤
        (Finset.univ.filter fun j : Fin m => R i j).card := by
      omega
    rcases Finset.exists_subset_card_eq hle with ⟨T, hTsub, hTcard⟩
    apply hstar
    refine ⟨i, T, hTcard, ?_, ?_⟩
    · intro hiT
      have hmem := hTsub hiT
      exact (Finset.mem_filter.mp hmem).2.1 rfl
    · intro j hj
      have hmem := hTsub hj
      exact (Finset.mem_filter.mp hmem).2.2
  have hr_ne_one : r ≠ 1 := by
    intro hr1
    rw [hr1] at hroot
    norm_num at hroot
    linarith
  have hr_two : 2 ≤ r := by omega
  have hk_pos : 0 < k := by
    have hδpos : 0 < δ :=
      lt_of_le_of_lt (by positivity : 0 ≤ (1 : ℝ) / Real.sqrt (r : ℝ)) hroot
    dsimp [δ] at hδpos
    have hkR : (0 : ℝ) < k := by
      rcases (div_pos_iff.mp hδpos) with h | h
      · exact h.2
      · norm_num at h
    exact_mod_cast hkR
  have low_degree (S : Finset (Fin m)) (hSnonempty : S.Nonempty) :
      ∃ i ∈ S, (S.filter fun j => R i j ∨ R j i).card < 4 * k := by
    have houtS (i : Fin m) : (S.filter fun j => R i j).card < 2 * k := by
      apply lt_of_le_of_lt _ (hout i)
      apply Finset.card_le_card
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
    have hsum_out :
        (∑ i ∈ S, (S.filter fun j => R i j).card) < 2 * k * S.card := by
      calc
        (∑ i ∈ S, (S.filter fun j => R i j).card) ≤
            ∑ _i ∈ S, (2 * k - 1) := by
              apply Finset.sum_le_sum
              intro i hi
              have := houtS i
              omega
        _ = S.card * (2 * k - 1) := by simp
        _ < 2 * k * S.card := by
          rw [mul_comm (2 * k) S.card]
          exact Nat.mul_lt_mul_of_pos_left (by omega) hSnonempty.card_pos
    have hsum_swap :
        (∑ i ∈ S, (S.filter fun j => R j i).card) =
          ∑ i ∈ S, (S.filter fun j => R i j).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Finset.sum_comm]
    have hsum_both :
        (∑ i ∈ S,
          ((S.filter fun j => R i j).card + (S.filter fun j => R j i).card)) <
            4 * k * S.card := by
      rw [Finset.sum_add_distrib, hsum_swap]
      have := hsum_out
      nlinarith
    obtain ⟨i, hiS, hi⟩ :
        ∃ i ∈ S,
          (S.filter fun j => R i j).card + (S.filter fun j => R j i).card <
            4 * k := by
      by_contra hnone
      push Not at hnone
      have hge : 4 * k * S.card ≤
          ∑ i ∈ S,
            ((S.filter fun j => R i j).card + (S.filter fun j => R j i).card) := by
        calc
          4 * k * S.card = ∑ _i ∈ S, 4 * k := by simp [mul_comm]
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro i hiS
            exact hnone i hiS
      omega
    refine ⟨i, hiS, lt_of_le_of_lt ?_ hi⟩
    calc
      (S.filter fun j => R i j ∨ R j i).card ≤
          ((S.filter fun j => R i j) ∪ (S.filter fun j => R j i)).card := by
            apply Finset.card_le_card
            intro j hj
            rcases (Finset.mem_filter.mp hj).2 with h | h
            · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, h⟩)
            · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, h⟩)
      _ ≤ (S.filter fun j => R i j).card + (S.filter fun j => R j i).card :=
        Finset.card_union_le _ _
  have greedy : ∀ q : ℕ, ∀ S : Finset (Fin m),
      (4 * k + 1) * q ≤ S.card →
      ∃ T ⊆ S, T.card = q ∧
        ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ¬(R i j ∨ R j i) := by
    intro q
    induction q with
    | zero =>
        intro S hsize
        exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
    | succ q ih =>
        intro S hsize
        have hSnonempty : S.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hS
          rw [hS] at hsize
          simp at hsize
        rcases low_degree S hSnonempty with ⟨i, hiS, hiDegree⟩
        let N := S.filter fun j => R i j ∨ R j i
        let U := insert i N
        let S' := S \ U
        have hUcard : U.card ≤ 4 * k + 1 := by
          calc
            U.card ≤ N.card + 1 := Finset.card_insert_le _ _
            _ ≤ 4 * k + 1 := by dsimp [N]; omega
        have hS'card : (4 * k + 1) * q ≤ S'.card := by
          have hsplit : S.card ≤ S'.card + U.card := by
            exact Finset.card_le_card_sdiff_add_card
          nlinarith
        rcases ih S' hS'card with ⟨T, hTS', hTcard, hTind⟩
        refine ⟨insert i T, ?_, ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hxT
          · exact hiS
          · exact Finset.sdiff_subset (hTS' hxT)
        · rw [Finset.card_insert_of_notMem]
          · omega
          · intro hiT
            have hiS' := hTS' hiT
            exact (Finset.mem_sdiff.mp hiS').2 (Finset.mem_insert_self i N)
        · intro x hx y hy hxy
          rcases Finset.mem_insert.mp hx with rfl | hxT
          · have hyT : y ∈ T := (Finset.mem_insert.mp hy).resolve_left (Ne.symm hxy)
            have hyS' := hTS' hyT
            have hyN : y ∉ N := by
              intro hyN
              exact (Finset.mem_sdiff.mp hyS').2 (Finset.mem_insert_of_mem hyN)
            intro hadj
            apply hyN
            exact Finset.mem_filter.mpr ⟨Finset.sdiff_subset hyS', hadj⟩
          · rcases Finset.mem_insert.mp hy with rfl | hyT
            · have hxS' := hTS' hxT
              have hxN : x ∉ N := by
                intro hxN
                exact (Finset.mem_sdiff.mp hxS').2 (Finset.mem_insert_of_mem hxN)
              intro hadj
              apply hxN
              exact Finset.mem_filter.mpr ⟨Finset.sdiff_subset hxS', hadj.symm⟩
            · exact hTind x hxT y hyT hxy
  have hmr : (4 * k + 1) * r ≤ m := by
    dsimp [r]
    exact Nat.mul_div_le _ _
  have hruniv : (4 * k + 1) * r ≤ (Finset.univ : Finset (Fin m)).card := by
    simpa using hmr
  rcases greedy r Finset.univ hruniv with ⟨S, hSuniv, hScard, hSind⟩
  let e : S ≃ Fin r := Finset.equivFinOfCardEq hScard
  let f : Fin r → Fin m := fun a => (e.symm a : S).1
  let D : Matrix (Fin r) (Fin r) ℝ := C.submatrix f f
  have hDdiag : ∀ i, D i i = 1 := by
    intro i
    exact hdiag (f i)
  have hDrank_le : (D.rank : ℝ) ≤ C.rank := by
    exact_mod_cast Matrix.rank_submatrix_le C f f
  have hDrank : (D.rank : ℝ) <
      α * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) * Real.log (r : ℝ) :=
    lt_of_le_of_lt hDrank_le hrank
  rcases hAlon r k D hroot hhalf hDdiag hDrank with ⟨i, j, hij, hlarge⟩
  have hfij : f i ≠ f j := by
    intro hf
    apply hij
    apply e.symm.injective
    exact Subtype.ext hf
  have hnot := hSind (f i) (e.symm i).property (f j) (e.symm j).property hfij
  exact hnot (Or.inl ⟨hfij, hlarge⟩)

@[blueprint "lem:correlation-star-contradicts-threshold"
  (statement := /-- Let $m,k,d\in\mathbb N$ with $k\geq2$, let $A,B\in\mathbb R^{d\times m}$, and let $t\in\mathbb R^m$. Suppose that $(A,B,t)$ is a normalized threshold classifier for the $k$-sparse binary vectors in $\mathbb R^m$ and that $B^{\mathsf T}A$ has a large $k$-correlation star. Then these two assumptions are incompatible. -/)
  (proof := /-- Let $C=B^{\mathsf T}A$, and choose $i$ and $T^*$ as in \cref{def:large-correlation-star}. Partition $T^*$ according to whether $C_{ij}\geq2/k$ or $C_{ij}\leq-2/k$. These two sets cover $T^*$, so one of them contains at least $k$ elements.

  First suppose that at least $k$ correlations are positive, and choose a $k$-element subset $T$ of their indices. The indicator of $T$ is a $k$-sparse binary vector whose $i$th coordinate is zero. Its $i$th score is
  \[
    \sum_{j\in T}C_{ij}\geq k\frac2k=2.
  \]
  On the other hand, applying \cref{def:normalized-threshold-classifies} to the $i$th coordinate vector gives $t_i<1$. Thus this score is greater than $t_i$, contradicting the required classification of the zero $i$th coordinate.

  Now suppose that at least $k$ correlations are negative. Choose $k-1$ of their indices, and let $z$ be the indicator of their union with $\{i\}$. Since $k\geq2$, this is a $k$-sparse binary vector with $z_i=1$. Normalization and the negative bounds give
  \[
    (Cz)_i\leq1-(k-1)\frac2k=\frac2k-1\leq0.
  \]
  Applying \cref{def:normalized-threshold-classifies} to the zero vector gives $t_i\geq0$. Hence $(Cz)_i\leq t_i$, contradicting the classification equivalence for $z_i=1$. Both possible signs therefore yield a contradiction. -/)
  (title := /-- A large correlation star violates threshold classification -/)
  (latexEnv := "lemma")]
lemma correlation_star_contradicts_threshold {m k d : ℕ}
    {A B : Matrix (Fin d) (Fin m) ℝ} {t : Fin m → ℝ}
    (hk : 2 ≤ k)
    (hnorm : normalized_threshold_classifies m k d A B t)
    (hstar : large_correlation_star k (B.transpose * A)) : False := by
  classical
  rcases hstar with ⟨i, T, hTcard, hiT, hlarge⟩
  let P := T.filter fun j => 0 ≤ (B.transpose * A) i j
  let N := T.filter fun j => ¬ 0 ≤ (B.transpose * A) i j
  have hparts : P.card + N.card = 2 * k := by
    simpa [P, N, hTcard] using
      T.card_filter_add_card_filter_not (fun j => 0 ≤ (B.transpose * A) i j)
  have hcases : k ≤ P.card ∨ k ≤ N.card := by
    omega
  have indicator_sparse (S : Finset (Fin m)) (hS : S.card ≤ k) :
      sparse_vector k (fun j => if j ∈ S then (1 : ℝ) else 0) := by
    simpa [sparse_vector, Function.support] using hS
  have indicator_binary (S : Finset (Fin m)) :
      binary_vector (fun j => if j ∈ S then (1 : ℝ) else 0) := by
    intro j
    by_cases hj : j ∈ S
    · right
      simp [hj]
    · left
      simp [hj]
  have indicator_mulVec (S : Finset (Fin m)) :
      ((B.transpose * A).mulVec (fun j => if j ∈ S then (1 : ℝ) else 0)) i =
        ∑ j ∈ S, (B.transpose * A) i j := by
    simp [Matrix.mulVec, dotProduct]
  have ht_zero : 0 ≤ t i := by
    have hz := hnorm.1 i 0 (by simp [sparse_vector]) (by simp [binary_vector])
    simpa using hz
  have ht_one : t i < 1 := by
    have hs : sparse_vector k (Pi.single i (1 : ℝ)) := by
      simp [sparse_vector, Pi.support_single, show 1 ≤ k by omega]
    have hb : binary_vector (Pi.single i (1 : ℝ)) := by
      intro j
      by_cases hji : j = i
      · right
        subst j
        simp
      · left
        simp [Pi.single, hji]
    have he := hnorm.1 i (Pi.single i 1) hs hb
    simpa [Matrix.mulVec_single_one, hnorm.2 i] using he
  rcases hcases with hP | hN
  · rcases P.exists_subset_card_eq hP with ⟨S, hSP, hScard⟩
    have hST : S ⊆ T := hSP.trans (Finset.filter_subset _ _)
    have hiS : i ∉ S := fun hi => hiT (hST hi)
    let z : Fin m → ℝ := fun j => if j ∈ S then 1 else 0
    have hzSparse : sparse_vector k z := by
      exact indicator_sparse S (by omega)
    have hzBinary : binary_vector z := by
      exact indicator_binary S
    have hscore_le : ((B.transpose * A).mulVec z) i ≤ t i := by
      apply le_of_not_gt
      intro hgt
      have hzi := (hnorm.1 i z hzSparse hzBinary).mp hgt
      simp [z, hiS] at hzi
    have hentry (j : Fin m) (hj : j ∈ S) :
        (2 : ℝ) / (k : ℝ) ≤ (B.transpose * A) i j := by
      have hjP := hSP hj
      have hjT := hST hj
      have hjnonneg : 0 ≤ (B.transpose * A) i j := (Finset.mem_filter.mp hjP).2
      simpa [abs_of_nonneg hjnonneg] using hlarge j hjT
    have hsum : (2 : ℝ) ≤ ∑ j ∈ S, (B.transpose * A) i j := by
      calc
        (2 : ℝ) = (S.card : ℝ) * ((2 : ℝ) / (k : ℝ)) := by
          rw [hScard]
          field_simp [show (k : ℝ) ≠ 0 by positivity]
        _ = ∑ j ∈ S, ((2 : ℝ) / (k : ℝ)) := by simp
        _ ≤ ∑ j ∈ S, (B.transpose * A) i j := by
          exact Finset.sum_le_sum fun j hj => hentry j hj
    have hscore_eq :
        ((B.transpose * A).mulVec z) i = ∑ j ∈ S, (B.transpose * A) i j := by
      exact indicator_mulVec S
    linarith
  · have hkpred : k - 1 ≤ N.card := by omega
    rcases N.exists_subset_card_eq hkpred with ⟨S, hSN, hScard⟩
    have hST : S ⊆ T := hSN.trans (Finset.filter_subset _ _)
    have hiS : i ∉ S := fun hi => hiT (hST hi)
    let U : Finset (Fin m) := insert i S
    have hUcard : U.card = k := by
      simp [U, hiS, hScard]
      omega
    let z : Fin m → ℝ := fun j => if j ∈ U then 1 else 0
    have hzSparse : sparse_vector k z := by
      exact indicator_sparse U (by omega)
    have hzBinary : binary_vector z := by
      exact indicator_binary U
    have hentry (j : Fin m) (hj : j ∈ S) :
        (B.transpose * A) i j ≤ -((2 : ℝ) / (k : ℝ)) := by
      have hjN := hSN hj
      have hjT := hST hj
      have hjneg : (B.transpose * A) i j < 0 := lt_of_not_ge (Finset.mem_filter.mp hjN).2
      have habs := hlarge j hjT
      rw [abs_of_neg hjneg] at habs
      linarith
    have hsum :
        ∑ j ∈ S, (B.transpose * A) i j ≤
          (S.card : ℝ) * (-((2 : ℝ) / (k : ℝ))) := by
      calc
        ∑ j ∈ S, (B.transpose * A) i j ≤
            ∑ j ∈ S, (-((2 : ℝ) / (k : ℝ))) := by
          exact Finset.sum_le_sum fun j hj => hentry j hj
        _ = (S.card : ℝ) * (-((2 : ℝ) / (k : ℝ))) := by simp
    have hfrac : (2 : ℝ) / (k : ℝ) ≤ 1 := by
      apply (div_le_one (by positivity : (0 : ℝ) < (k : ℝ))).2
      exact_mod_cast hk
    have hscore_nonpos : ((B.transpose * A).mulVec z) i ≤ 0 := by
      rw [show ((B.transpose * A).mulVec z) i =
        ∑ j ∈ U, (B.transpose * A) i j by exact indicator_mulVec U]
      rw [Finset.sum_insert hiS, hnorm.2 i]
      calc
        1 + ∑ j ∈ S, (B.transpose * A) i j ≤
            1 + (S.card : ℝ) * (-((2 : ℝ) / (k : ℝ))) := by linarith
        _ = (2 : ℝ) / (k : ℝ) - 1 := by
          rw [hScard, Nat.cast_sub (by omega : 1 ≤ k)]
          field_simp [show (k : ℝ) ≠ 0 by positivity]
          ring
        _ ≤ 0 := sub_nonpos.mpr hfrac
    have hscore_gt : t i < ((B.transpose * A).mulVec z) i := by
      apply (hnorm.1 i z hzSparse hzBinary).mpr
      simp [z, U]
    linarith

@[blueprint "lem:low-rank-threshold-classifier-impossible"
  (statement := /-- There exists an absolute constant $\alpha>0$ with the following property. Let
  $m,k,d\in\mathbb N$, let $A,B\in\mathbb R^{d\times m}$, and let
  $t\in\mathbb R^m$. Set
  \[
    r=\left\lfloor\frac{m}{4k+1}\right\rfloor.
  \]
  If
  \[
    2\leq k,\qquad r>0,\qquad
    \frac{1}{\sqrt r}<\frac{2}{k}<\frac12,
    \qquad
    d<\alpha\frac{k^2}{\log k}\log r,
  \]
  then $(A,B,t)$ does not threshold-classify all $k$-sparse vectors in
  $\{0,1\}^m$ in the sense of \cref{def:threshold-classifies}. -/)
  (proof := /-- Assume that a threshold classifier exists. By \cref{lem:normalize-threshold-classifier}, rescale its rows of probes and its thresholds so that its correlation matrix $C=B^{\mathsf T}A$ has unit diagonal. The image of $C$ is contained in the image of $B^{\mathsf T}$, and consequently $\operatorname{rank}(C)\leq d$. The asserted upper bound on $d$ therefore permits \cref{lem:turan-extracts-large-correlation-star} to be applied to $C$. It yields a large $k$-correlation star, which contradicts normalized threshold classification by \cref{lem:correlation-star-contradicts-threshold}. -/)
  (title := /-- Low-rank threshold classification is impossible -/)
  (latexEnv := "lemma")]
lemma low_rank_threshold_classifier_impossible :
    ∃ α : ℝ, 0 < α ∧
      ∀ (m k d : ℕ)
        (A B : Matrix (Fin d) (Fin m) ℝ) (t : Fin m → ℝ),
        2 ≤ k →
        0 < m / (4 * k + 1) →
        (1 : ℝ) / Real.sqrt ((m / (4 * k + 1) : ℕ) : ℝ) <
          (2 : ℝ) / (k : ℝ) →
        (2 : ℝ) / (k : ℝ) < (1 : ℝ) / 2 →
        (d : ℝ) <
          α * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) *
            Real.log ((m / (4 * k + 1) : ℕ) : ℝ) →
        threshold_classifies m k d A B t →
        False := by
  rcases turan_extracts_large_correlation_star with ⟨α, hα, hTuran⟩
  refine ⟨α, hα, ?_⟩
  intro m k d A B t hk hr hroot hhalf hd hclass
  rcases normalize_threshold_classifier (by omega) hclass with ⟨B', t', hnorm⟩
  apply correlation_star_contradicts_threshold hk hnorm
  apply hTuran m k (B'.transpose * A) hr hroot hhalf hnorm.2
  have hrank_nat : (B'.transpose * A).rank ≤ d :=
    (Matrix.rank_mul_le_left B'.transpose A).trans
      (Matrix.rank_le_width B'.transpose)
  have hrank_real : ((B'.transpose * A).rank : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast hrank_nat
  exact hrank_real.trans_lt hd

@[blueprint "lem:recovery-produces-threshold-classifier"
  (statement := /-- Let $m,k,d\in\mathbb N$ and $\epsilon\in\mathbb R$ satisfy
  \[
    \tau(m,k)<\epsilon\leq\frac12.
  \]
  Suppose that there exist $A_0,B_0\in\mathbb R^{d\times m}$ such that
  \[
    \left|((B_0^{\mathsf T}A_0)z)_i-z_i\right|<\epsilon
  \]
  for every $k$-sparse $z\in[-1,1]^m$ and every $i\in[m]$. Then there exist $A,B\in\mathbb R^{d\times m}$ and $t\in\mathbb R^m$ such that, for every $i\in[m]$ and every $k$-sparse $z\in\{0,1\}^m$,
  \[
    (B^{\mathsf T}Az)_i>t_i\quad\Longleftrightarrow\quad z_i=1.
  \] -/)
  (proof := /-- Choose recovering matrices $A,B$ from \cref{def:linearly-recovers}, and put $t_i=1/2$ for every $i$. Every binary vector belongs to the unit cube. If $z$ is $k$-sparse and binary, uniform recovery gives
  \[
    \left|((B^{\mathsf T}A)z)_i-z_i\right|<\epsilon\leq\frac12
  \]
  for every $i$. When $z_i=1$, this inequality implies $((B^{\mathsf T}A)z)_i>1/2=t_i$. When $z_i=0$, it implies $((B^{\mathsf T}A)z)_i<1/2=t_i$. Since these are the only two possible coordinate values, the threshold equivalence in \cref{def:threshold-classifies} holds for every $i$ and every $k$-sparse binary $z$. -/)
  (title := /-- Pass from recovery to threshold classification -/)
  (latexEnv := "lemma")]
lemma recovery_produces_threshold_classifier {m k d : ℕ} {ε : ℝ}
    (hε_lower : epsilon_threshold m k < ε)
    (hε_upper : ε ≤ (1 : ℝ) / 2)
    (hrec : linearly_recovers m k d ε) :
    ∃ (A B : Matrix (Fin d) (Fin m) ℝ) (t : Fin m → ℝ),
      threshold_classifies m k d A B t := by
  rcases hrec with ⟨A, B, hrec⟩
  refine ⟨A, B, fun _ => (1 : ℝ) / 2, ?_⟩
  intro i z hz_sparse hz_binary
  have hz_cube : unit_cube_vector z := by
    intro j
    rcases hz_binary j with hj | hj
    · simp [hj]
    · simp [hj]
  have herror := hrec z hz_sparse hz_cube i
  rcases hz_binary i with hi | hi
  · rw [hi] at herror ⊢
    constructor
    · intro hlarge
      have hsmall : ((B.transpose * A).mulVec z) i < (1 : ℝ) / 2 := by
        calc
          ((B.transpose * A).mulVec z) i ≤ |((B.transpose * A).mulVec z) i| :=
            le_abs_self _
          _ < ε := by simpa using herror
          _ ≤ (1 : ℝ) / 2 := hε_upper
      linarith
    · norm_num
  · rw [hi] at herror ⊢
    constructor
    · intro _
      rfl
    · intro _
      have hlower : -ε < ((B.transpose * A).mulVec z) i - 1 :=
        (abs_lt.mp herror).1
      linarith

@[blueprint "lem:embedding-dimension-recovers-positive-error"
  (statement := /-- Let $m,k\in\mathbb N$ and let $\epsilon\in\mathbb R$ be positive. Then the minimal dimension $d(m,k,\epsilon)$ linearly recovers every $k$-sparse vector in $[-1,1]^m$ with coordinatewise error strictly smaller than $\epsilon$. -/)
  (proof := /-- By \cref{def:embedding-dimension}, it suffices to prove that the set of recovering dimensions is nonempty and then apply the well-ordering property of $\mathbb N$. The dimension $m$ belongs to this set: in \cref{def:linearly-recovers}, take both matrices to be the identity matrix. Their product fixes every vector, so every coordinate error is zero, which is strictly smaller than the positive number $\epsilon$. -/)
  (title := /-- The minimal recovery dimension is attained for positive error -/)
  (latexEnv := "lemma")]
lemma embedding_dimension_recovers_positive_error {m k : ℕ} {ε : ℝ} (hε : 0 < ε) :
    linearly_recovers m k (embedding_dimension m k ε) ε := by
  unfold embedding_dimension
  change sInf {d : ℕ | linearly_recovers m k d ε} ∈
    {d : ℕ | linearly_recovers m k d ε}
  apply Nat.sInf_mem
  refine ⟨m, ?_⟩
  refine ⟨1, 1, ?_⟩
  intro z _ _ i
  simpa [linearly_recovers] using hε

@[blueprint "lem:source-asymptotic-pair-estimates"
  (statement := /-- Let $m,k\in\mathbb N$ satisfy $1\leq m$ and $5\leq k$, and let $\epsilon\in\mathbb R$ satisfy $\tau(m,k)<\epsilon\leq 1/2$. Put $r=\lfloor m/(4k+1)\rfloor$. Then $r>0$, one has
  \[
    \frac1{\sqrt r}<\frac2k<\frac12,
  \]
  and the lower-bound scale is nonnegative and satisfies
  \[
    0\leq L(m,k)\leq 2\frac{k^2}{\log k}\log r.
  \] -/)
  (proof := /-- Unfold \cref{def:epsilon-threshold}. Positivity of $m$ permits multiplication by $\sqrt m$ in the admissibility inequality; squaring its nonnegative sides gives $20k^3<m$. Consequently
  \[
    4k^2\leq \left\lfloor\frac{m}{4k+1}\right\rfloor=r.
  \]
  This proves $r>0$, implies $2k\leq\sqrt r$, and hence gives the two strict reciprocal inequalities when $k\geq5$. The division algorithm gives $m<(r+1)(4k+1)$. Since $r\geq4k^2\geq100$, the bounds $r+1\leq2r$ and $4k+1\leq5k$ yield $m/k\leq r^2$. Monotonicity of the logarithm therefore gives $\log(m/k)\leq2\log r$. Finally, $k>1$ and $r\geq1$ make both logarithmic factors nonnegative, so multiplication by $k^2/\log k$ proves the asserted estimate for \cref{def:lower-bound-scale}. -/)
  (title := /-- Numerical estimates for admissible asymptotic pairs -/)
  (latexEnv := "lemma")]
lemma source_asymptotic_pair_estimates {m k : ℕ} {ε : ℝ}
    (hm : 1 ≤ m) (hk : 5 ≤ k)
    (hε_lower : epsilon_threshold m k < ε)
    (hε_upper : ε ≤ (1 : ℝ) / 2) :
    0 < m / (4 * k + 1) ∧
      (1 : ℝ) / Real.sqrt ((m / (4 * k + 1) : ℕ) : ℝ) <
        (2 : ℝ) / (k : ℝ) ∧
      (2 : ℝ) / (k : ℝ) < (1 : ℝ) / 2 ∧
      0 ≤ lower_bound_scale m k ∧
      lower_bound_scale m k ≤
        2 * (((k : ℝ) ^ 2 / Real.log (k : ℝ)) *
          Real.log ((m / (4 * k + 1) : ℕ) : ℝ)) := by
  let r := m / (4 * k + 1)
  change 0 < r ∧
    (1 : ℝ) / Real.sqrt (r : ℝ) < (2 : ℝ) / (k : ℝ) ∧
    (2 : ℝ) / (k : ℝ) < (1 : ℝ) / 2 ∧
    0 ≤ lower_bound_scale m k ∧
    lower_bound_scale m k ≤
      2 * (((k : ℝ) ^ 2 / Real.log (k : ℝ)) * Real.log (r : ℝ))
  have hm_real : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hk_real : (0 : ℝ) < (k : ℝ) := by positivity
  have hsqrt_m : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm_real
  have hthreshold :
      Real.sqrt ((k : ℝ) ^ 3) * Real.sqrt 5 / Real.sqrt (m : ℝ) <
        (1 : ℝ) / 2 := by
    have hlow :
        Real.sqrt ((k : ℝ) ^ 3) * Real.sqrt 5 / Real.sqrt (m : ℝ) < ε := by
      simpa [epsilon_threshold] using hε_lower
    exact hlow.trans_le hε_upper
  have hmul :
      Real.sqrt ((k : ℝ) ^ 3) * Real.sqrt 5 <
        ((1 : ℝ) / 2) * Real.sqrt (m : ℝ) :=
    (div_lt_iff₀ hsqrt_m).mp hthreshold
  have hsquare := (sq_lt_sq₀
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).2 hmul
  have htwenty_real : 20 * (k : ℝ) ^ 3 < (m : ℝ) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (k : ℝ) ^ 3 by positivity),
      Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
      Real.sq_sqrt (show 0 ≤ (m : ℝ) by positivity)]
  have htwenty : 20 * k ^ 3 < m := by exact_mod_cast htwenty_real
  have hden_pos : 0 < 4 * k + 1 := by omega
  have hproduct : (4 * k ^ 2) * (4 * k + 1) ≤ m := by
    calc
      (4 * k ^ 2) * (4 * k + 1) ≤ 20 * k ^ 3 := by nlinarith
      _ ≤ m := htwenty.le
  have hr_lower : 4 * k ^ 2 ≤ r := by
    apply (Nat.le_div_iff_mul_le hden_pos).2
    simpa [r] using hproduct
  have hr_pos : 0 < r := by nlinarith
  have hsqrt_r_pos : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hr_pos)
  have hsqrt_r_lower : 2 * (k : ℝ) ≤ Real.sqrt (r : ℝ) := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (show (0 : ℝ) ≤ (r : ℝ) by positivity)]
    have hr_lower_real : 4 * (k : ℝ) ^ 2 ≤ (r : ℝ) := by exact_mod_cast hr_lower
    nlinarith
  have hroot :
      (1 : ℝ) / Real.sqrt (r : ℝ) < (2 : ℝ) / (k : ℝ) := by
    apply (div_lt_iff₀ hsqrt_r_pos).2
    rw [div_mul_eq_mul_div, lt_div_iff₀ hk_real]
    nlinarith [hsqrt_r_lower]
  have hhalf : (2 : ℝ) / (k : ℝ) < (1 : ℝ) / 2 := by
    apply (div_lt_iff₀ hk_real).2
    have hk_real_five : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith
  have hmod : m % (4 * k + 1) < 4 * k + 1 := Nat.mod_lt _ hden_pos
  have hm_lt : m < (r + 1) * (4 * k + 1) := by
    calc
      m = r * (4 * k + 1) + m % (4 * k + 1) := by
        simpa [r, mul_comm] using (Nat.div_add_mod m (4 * k + 1)).symm
      _ < r * (4 * k + 1) + (4 * k + 1) := Nat.add_lt_add_left hmod _
      _ = (r + 1) * (4 * k + 1) := by ring
  have hk_sq : 25 ≤ k ^ 2 := by
    simpa [pow_two] using Nat.mul_self_le_mul_self hk
  have hr_hundred : 100 ≤ r := le_trans (by omega : 100 ≤ 4 * k ^ 2) hr_lower
  have hr_one : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 1 ≤ r by omega)
  have hprod_real :
      ((r + 1 : ℕ) : ℝ) * ((4 * k + 1 : ℕ) : ℝ) ≤
        (r : ℝ) ^ 2 * (k : ℝ) := by
    have hr_add : ((r + 1 : ℕ) : ℝ) ≤ 2 * (r : ℝ) := by
      norm_num
      exact_mod_cast (show r + 1 ≤ 2 * r by omega)
    have hk_add : ((4 * k + 1 : ℕ) : ℝ) ≤ 5 * (k : ℝ) := by
      norm_num
      exact_mod_cast (show 4 * k + 1 ≤ 5 * k by omega)
    calc
      ((r + 1 : ℕ) : ℝ) * ((4 * k + 1 : ℕ) : ℝ) ≤
          (2 * (r : ℝ)) * (5 * (k : ℝ)) :=
        mul_le_mul hr_add hk_add (by positivity) (by positivity)
      _ = 10 * ((k : ℝ) * (r : ℝ)) := by ring
      _ ≤ (r : ℝ) * ((k : ℝ) * (r : ℝ)) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast (show 10 ≤ r by omega)
        · positivity
      _ = (r : ℝ) ^ 2 * (k : ℝ) := by ring
  have hratio : (m : ℝ) / (k : ℝ) ≤ (r : ℝ) ^ 2 := by
    apply (div_le_iff₀ hk_real).2
    calc
      (m : ℝ) ≤ (((r + 1) * (4 * k + 1) : ℕ) : ℝ) := by exact_mod_cast hm_lt.le
      _ = ((r + 1 : ℕ) : ℝ) * ((4 * k + 1 : ℕ) : ℝ) := by norm_num
      _ ≤ (r : ℝ) ^ 2 * (k : ℝ) := hprod_real
  have hratio_pos : (0 : ℝ) < (m : ℝ) / (k : ℝ) := div_pos hm_real hk_real
  have hlog_ratio :
      Real.log ((m : ℝ) / (k : ℝ)) ≤ 2 * Real.log (r : ℝ) := by
    calc
      Real.log ((m : ℝ) / (k : ℝ)) ≤ Real.log ((r : ℝ) ^ 2) :=
        Real.log_le_log hratio_pos hratio
      _ = 2 * Real.log (r : ℝ) := by rw [Real.log_pow]; norm_num
  have hlog_k : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  have hfactor : 0 ≤ (k : ℝ) ^ 2 / Real.log (k : ℝ) :=
    div_nonneg (sq_nonneg _) hlog_k.le
  have hscale_nonneg : 0 ≤ lower_bound_scale m k := by
    unfold lower_bound_scale
    exact mul_nonneg hfactor (Real.log_nonneg (by
      apply (one_le_div₀ hk_real).2
      exact_mod_cast (show k ≤ m by nlinarith [htwenty])))
  have hscale :
      lower_bound_scale m k ≤
        2 * (((k : ℝ) ^ 2 / Real.log (k : ℝ)) * Real.log (r : ℝ)) := by
    unfold lower_bound_scale
    calc
      ((k : ℝ) ^ 2 / Real.log (k : ℝ)) * Real.log ((m : ℝ) / (k : ℝ)) ≤
          ((k : ℝ) ^ 2 / Real.log (k : ℝ)) * (2 * Real.log (r : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog_ratio hfactor
      _ = 2 * (((k : ℝ) ^ 2 / Real.log (k : ℝ)) * Real.log (r : ℝ)) := by ring
  exact ⟨hr_pos, hroot, hhalf, hscale_nonneg, hscale⟩

@[blueprint "lem:source-asymptotic-assembly"
  (statement := /-- Fix $\epsilon\in\mathbb R$ with $\epsilon\leq 1/2$. The function
  \[
    (m,k)\longmapsto \frac{k^2}{\log k}\log\frac{m}{k}
  \]
  is big-O of $(m,k)\mapsto d(m,k,\epsilon)$ along the joint at-top filter
  restricted by $\tau(m,k)<\epsilon$. -/)
  (proof := /-- Choose $\alpha>0$ as in
  \cref{lem:low-rank-threshold-classifier-impossible}; the big-O constant may
  depend on the fixed parameter $\epsilon$. Assume throughout that
  $\epsilon\leq 1/2$. By
  \cref{def:lower-bound-filter}, it suffices to consider pairs $(m,k)$ with
  $m\geq1$, $k\geq5$, and $\tau(m,k)<\epsilon$. For each such pair, put
  \[
    r=\left\lfloor\frac{m}{4k+1}\right\rfloor.
  \]
  The numerical comparison in
  \cref{lem:source-asymptotic-pair-estimates}, applied with the fixed upper
  bound on $\epsilon$, gives
  \[
    r>0,\qquad \frac1{\sqrt r}<\frac2k<\frac12,
    \qquad
    0\leq L(m,k)\leq
      2\frac{k^2}{\log k}\log r.
  \]
  The quantity $\tau(m,k)$ in \cref{def:epsilon-threshold} is nonnegative, so
  admissibility implies $\epsilon>0$. Therefore
  \cref{lem:embedding-dimension-recovers-positive-error} supplies linear
  recovery in dimension $d(m,k,\epsilon)$, and
  \cref{lem:recovery-produces-threshold-classifier}, applied with the same
  upper bound, converts these recovering matrices into matrices and thresholds
  that classify all $k$-sparse binary vectors.

  If
  \[
    d(m,k,\epsilon)<
      \alpha\frac{k^2}{\log k}\log r,
  \]
  these matrices and thresholds satisfy every hypothesis of
  \cref{lem:low-rank-threshold-classifier-impossible}, a contradiction.
  Hence
  \[
    \alpha\frac{k^2}{\log k}\log r
      \leq d(m,k,\epsilon).
  \]
  Since $\alpha>0$, multiplication by $2/\alpha$ and combination with the
  preceding bound for $L(m,k)$ yield
  \[
    L(m,k)\leq C_\epsilon d(m,k,\epsilon).
  \]
  Both sides inside the norms in the definition of big-O are nonnegative, so
  this eventual inequality proves the assertion. -/)
  (title := /-- Assemble the asymptotic lower bound -/)
  (latexEnv := "lemma")]
lemma source_asymptotic_assembly (ε : ℝ) (hε_upper : ε ≤ (1 : ℝ) / 2) :
    Asymptotics.IsBigO (lower_bound_filter ε)
      (fun p : ℕ × ℕ => lower_bound_scale p.1 p.2)
      (fun p : ℕ × ℕ => (embedding_dimension p.1 p.2 ε : ℝ)) := by
  rcases low_rank_threshold_classifier_impossible with ⟨α, hα, himpossible⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨2 / α, ?_⟩
  rw [lower_bound_filter, Filter.eventually_inf_principal]
  refine Filter.eventually_atTop.2 ⟨(1, 5), ?_⟩
  rintro ⟨m, k⟩ hmk hadmissible
  have hm : 1 ≤ m := hmk.1
  have hk : 5 ≤ k := hmk.2
  rcases source_asymptotic_pair_estimates hm hk hadmissible hε_upper with
    ⟨hr, hroot, hhalf, hscale_nonneg, hscale⟩
  have hthreshold_nonneg : 0 ≤ epsilon_threshold m k := by
    unfold epsilon_threshold
    positivity
  have hε_pos : 0 < ε := hthreshold_nonneg.trans_lt hadmissible
  have hrec := embedding_dimension_recovers_positive_error (m := m) (k := k) hε_pos
  rcases recovery_produces_threshold_classifier hadmissible hε_upper hrec with
    ⟨A, B, t, hclass⟩
  let q := ((k : ℝ) ^ 2 / Real.log (k : ℝ)) *
    Real.log ((m / (4 * k + 1) : ℕ) : ℝ)
  have hdimension :
      α * q ≤ (embedding_dimension m k ε : ℝ) := by
    apply le_of_not_gt
    intro hlt
    apply himpossible m k (embedding_dimension m k ε) A B t (by omega) hr hroot
      hhalf _ hclass
    simpa [q, mul_assoc] using hlt
  have hconstant_nonneg : 0 ≤ 2 / α := by positivity
  calc
    ‖lower_bound_scale m k‖ = lower_bound_scale m k :=
      Real.norm_of_nonneg hscale_nonneg
    _ ≤ 2 * q := hscale
    _ = (2 / α) * (α * q) := by field_simp
    _ ≤ (2 / α) * (embedding_dimension m k ε : ℝ) :=
      mul_le_mul_of_nonneg_left hdimension hconstant_nonneg
    _ = (2 / α) * ‖(embedding_dimension m k ε : ℝ)‖ := by
      rw [Real.norm_of_nonneg]
      positivity

@[blueprint "thm:lower-bound"
  (statement := /-- Fix $\epsilon\in\mathbb R$ with $\epsilon\leq 1/2$.
  As $(m,k)\in\mathbb N\times\mathbb N$ tend jointly to infinity subject to
  $k^{3/2}\sqrt5/\sqrt m<\epsilon$, the minimal linear-representation
  dimension satisfies
  \[
    d(m,k,\epsilon)
      =\Omega_\epsilon\!\left(
        \frac{k^2}{\log k}\log\frac{m}{k}
      \right).
  \] -/)
  (proof := /-- Apply \cref{lem:source-asymptotic-assembly} to the fixed
  parameter $\epsilon$ and the hypothesis $\epsilon\leq 1/2$. This gives the
  asserted $\Omega_\epsilon$ lower bound: the multiplicative constant may
  depend on $\epsilon$, while
  \cref{def:lower-bound-filter} restricts the asymptotic parameters to the
  pairs satisfying $\tau(m,k)<\epsilon$. -/)
  (title := /-- Lower bound for linear feature representations -/)
  (latexEnv := "theorem")]
theorem lower_bound (ε : ℝ) (hε_upper : ε ≤ (1 : ℝ) / 2) :
    Asymptotics.IsBigO (lower_bound_filter ε)
      (fun p : ℕ × ℕ => lower_bound_scale p.1 p.2)
      (fun p : ℕ × ℕ => (embedding_dimension p.1 p.2 ε : ℝ)) := by
  exact source_asymptotic_assembly ε hε_upper

import Architect
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:directed-regular"
  (statement := /-- A finite directed graph is $d$-regular if every vertex has exactly $d$ out-neighbours and exactly $d$ in-neighbours.  Loops are permitted, and adjacency is a proposition, so parallel edges are excluded. -/)
  (title := /-- Regular directed graphs -/)
  (latexEnv := "definition")]
noncomputable def directed_regular {V : Type*} [Fintype V]
    (G : Digraph V) (d : ℕ) : Prop := by
  classical
  exact
    (∀ v : V, (Finset.univ.filter fun w : V => G.Adj v w).card = d) ∧
      ∀ v : V, (Finset.univ.filter fun w : V => G.Adj w v).card = d

@[blueprint "def:directed-cycle-factors"
  (statement := /-- The cycle-factors of a finite directed graph $G$ are the permutations $\sigma$ of its vertex set for which $G$ contains the directed edge from $v$ to $\sigma(v)$ for every vertex $v$. -/)
  (title := /-- Directed cycle-factors -/)
  (latexEnv := "definition")]
noncomputable def directed_cycle_factors {V : Type*} [Fintype V]
    (G : Digraph V) : Finset (Equiv.Perm V) := by
  classical
  exact Finset.univ.filter fun σ : Equiv.Perm V => ∀ v : V, G.Adj v (σ v)

@[blueprint "def:permutation-cycle-count"
  (statement := /-- For a permutation $\sigma$ of a finite type, its number of cycles is the cardinality of the quotient by the relation of lying in the same $\sigma$-orbit.  Fixed points are counted as cycles. -/)
  (title := /-- Number of cycles of a permutation -/)
  (latexEnv := "definition")]
noncomputable def permutation_cycle_count {V : Type*} [Fintype V]
    (σ : Equiv.Perm V) : ℕ := by
  classical
  exact Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid σ))

@[blueprint "def:uniform-expected-cycle-count"
  (statement := /-- The uniform expected number of cycles of the cycle-factors of $G$ is the sum of their cycle counts divided by the number of cycle-factors.  If the finset is empty, Lean's division convention assigns the value zero. -/)
  (title := /-- Uniform cycle-factor expectation -/)
  (latexEnv := "definition")]
noncomputable def uniform_expected_cycle_count {V : Type*} [Fintype V]
    (G : Digraph V) : ℝ :=
  (∑ σ ∈ directed_cycle_factors G, (permutation_cycle_count σ : ℝ)) /
    ((directed_cycle_factors G).card : ℝ)

@[blueprint "def:remaining-neighbor-count"
  (statement := /-- Let the vertices be $[n]$.  Given a cycle-factor $\sigma$, an ordering $\tau$, and a vertex $i$, the remaining-neighbour count is the number of out-neighbours $j$ of $i$ for which $\sigma^{-1}(j)$ does not precede $i$ in the ordering $\tau$. -/)
  (title := /-- Remaining out-neighbours in an ordering -/)
  (latexEnv := "definition")]
noncomputable def remaining_neighbor_count {n : ℕ} (G : Digraph (Fin n))
    (σ τ : Equiv.Perm (Fin n)) (i : Fin n) : ℕ := by
  classical
  exact
    (Finset.univ.filter fun j : Fin n =>
      G.Adj i j ∧ ¬ ((τ.symm (σ.symm j)).val < (τ.symm i).val)).card

@[blueprint "def:harmonic-sum"
  (statement := /-- For a natural number $d$, set $H_d=\sum_{t=1}^{d}1/t$. -/)
  (title := /-- Finite harmonic sum -/)
  (latexEnv := "definition")]
noncomputable def harmonic_sum (d : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 d, ((t : ℝ)⁻¹)

@[blueprint "def:finite-shannon-entropy"
  (statement := /-- For a real-valued mass function $p$ on a finite type, its base-$2$ Shannon expression is $-\sum_x p(x)\log_2 p(x)$.  This definition is subsequently applied only to probability mass functions. -/)
  (title := /-- Finite Shannon entropy -/)
  (latexEnv := "definition")]
noncomputable def finite_shannon_entropy {α : Type*} [Fintype α]
    (p : α → ℝ) : ℝ :=
  ∑ x : α, -(p x) * Real.logb 2 (p x)

@[blueprint "def:cycle-factor-entropy-certificate"
  (statement := /-- For a directed graph $G$ on $[n]$, a number $L$ is an entropy certificate at degree $d$ if it is nonnegative, satisfies
  \[
  L\leq \frac{n\log_2(ed)}{d},
  \]
  and controls the expected cycle count by
  \[
  \mathbb E|\sigma|\leq \frac{2n}{d}H_d+L.
  \] -/)
  (title := /-- Entropy certificate for cycle-factors -/)
  (latexEnv := "definition")]
noncomputable def cycle_factor_entropy_certificate {n : ℕ}
    (G : Digraph (Fin n)) (d : ℕ) (L : ℝ) : Prop :=
  0 ≤ L ∧
    L ≤ (n : ℝ) * Real.logb 2 (Real.exp 1 * (d : ℝ)) / (d : ℝ) ∧
    uniform_expected_cycle_count G ≤
      (2 * (n : ℝ) / (d : ℝ)) * harmonic_sum d + L

@[blueprint "def:real-stable-mv-polynomial"
  (statement := /-- A real multivariate polynomial $p$ is real stable if it is the zero polynomial or if its complexification does not vanish whenever every variable has strictly positive imaginary part. -/)
  (title := /-- Real stability of a multivariate polynomial -/)
  (latexEnv := "definition")]
noncomputable def real_stable_mv_polynomial {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) : Prop :=
  p = 0 ∨
    ∀ z : ι → ℂ, (∀ i, 0 < (z i).im) →
      MvPolynomial.eval₂ (algebraMap ℝ ℂ) z p ≠ 0

@[blueprint "def:mv-polynomial-capacity"
  (statement := /-- Let $p$ be a real polynomial whose variables are indexed by a finite set $I$.  Its capacity is
  \[
  \operatorname{Cap}(p)=\inf_{x\in\mathbb R_{>0}^{I}}
  \frac{p(x)}{\prod_{i\in I}x_i}.
  \] -/)
  (title := /-- Capacity of a multivariate polynomial -/)
  (latexEnv := "definition")]
noncomputable def mv_polynomial_capacity {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) : ℝ :=
  sInf {r : ℝ | ∃ x : ι → ℝ, (∀ i, 0 < x i) ∧
    r = MvPolynomial.eval x p / ∏ i, x i}

@[blueprint "def:matrix-product-polynomial"
  (statement := /-- For a real $n\times n$ matrix $A=(a_{ij})$, define
  \[
  p_A(x_1,\ldots,x_n)=
  \prod_{i=1}^{n}\left(\sum_{j=1}^{n}a_{ij}x_j\right).
  \] -/)
  (title := /-- Product polynomial associated with a matrix -/)
  (latexEnv := "definition")]
noncomputable def matrix_product_polynomial {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∏ i, ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j

@[blueprint "def:mv-polynomial-derivative-specialization"
  (statement := /-- If $p$ is a polynomial in $k+1$ variables, its last-variable derivative specialization is the polynomial in the first $k$ variables obtained by differentiating with respect to the last variable and then setting that variable equal to zero. -/)
  (title := /-- Derivative specialization in the last variable -/)
  (latexEnv := "definition")]
noncomputable def mv_polynomial_derivative_specialization (k : ℕ)
    (p : MvPolynomial (Fin (k + 1)) ℝ) : MvPolynomial (Fin k) ℝ :=
  MvPolynomial.bind₁
    (fun i => if h : i.val < k then MvPolynomial.X ⟨i.val, h⟩ else 0)
    (MvPolynomial.pderiv (Fin.last k) p)

@[blueprint "lem:product-linear-forms-real-stable"
  (statement := /-- Let $n\in\mathbb N$, and let $A=(a_{ij})_{i,j\in[n]}$ be a real matrix.  If $a_{ij}\geq0$ for every $i,j\in[n]$ and every row of $A$ has sum $1$, then the product polynomial $p_A$ of \cref{def:matrix-product-polynomial} is real stable in the sense of \cref{def:real-stable-mv-polynomial}. -/)
  (proof := /-- Let $z=(z_j)_{j\in[n]}$ have strictly positive imaginary parts.  For every row $i$,
  \[
  \operatorname{Im}\left(\sum_j a_{ij}z_j\right)
  =\sum_j a_{ij}\operatorname{Im}(z_j)>0.
  \]
  Indeed, all summands are nonnegative, and the row-sum hypothesis implies that at least one coefficient in the row is positive.  Thus every linear factor in \cref{def:matrix-product-polynomial} is nonzero at $z$, so their product is nonzero.  This is precisely the nonvanishing alternative in \cref{def:real-stable-mv-polynomial}. -/)
  (title := /-- Stability of a product of nonnegative linear forms -/)
  (latexEnv := "lemma")]
lemma product_linear_forms_real_stable {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hnonnegative : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∑ j, A i j = 1) :
    real_stable_mv_polynomial (matrix_product_polynomial A) := by
  right
  intro z hz
  simp [matrix_product_polynomial]
  simp only [Finset.prod_ne_zero_iff]
  intro i _
  intro hzero
  have hcoeff : ∃ j ∈ Finset.univ, 0 < A i j :=
    (Finset.sum_pos_iff_of_nonneg (fun j _ => hnonnegative i j)).mp (by
      simpa [hrow i])
  have him : 0 < ∑ j, A i j * (z j).im :=
    Finset.sum_pos' (fun j _ =>
      mul_nonneg (hnonnegative i j) (le_of_lt (hz j))) (by
        obtain ⟨j, hj, hAj⟩ := hcoeff
        exact ⟨j, hj, mul_pos hAj (hz j)⟩)
  have him' : 0 < (∑ j, (A i j : ℂ) * z j).im := by
    simpa using him
  rw [hzero] at him'
  norm_num at him'

@[blueprint "lem:derivative-specialization-structure"
  (statement := /-- Let $k\in\mathbb N$, and let $p\in\mathbb R[x_1,\ldots,x_{k+1}]$ be homogeneous of degree $k+1$ with nonnegative coefficients.  Differentiating $p$ with respect to $x_{k+1}$ and then setting $x_{k+1}=0$ produces a polynomial in $x_1,\ldots,x_k$ that is homogeneous of degree $k$ and has nonnegative coefficients. -/)
  (proof := /-- Let $r=\partial p/\partial x_{k+1}$.  For every exponent vector $\alpha$, the coefficient formula for a partial derivative gives
  \[
  [x^\alpha]r=(\alpha_{k+1}+1)[x^{\alpha+e_{k+1}}]p.
  \]
  Thus every coefficient of $r$ is nonnegative.  Moreover, whenever the displayed coefficient is nonzero, homogeneity of $p$ implies $|\alpha+e_{k+1}|=k+1$, and hence $|\alpha|=k$; therefore $r$ is homogeneous of degree $k$.

  Let $g$ send each of the first $k$ variables to the corresponding indeterminate and send the last variable to zero.  Every $g(i)$ is homogeneous of degree one, since the zero polynomial is homogeneous of every degree.  Homogeneity under polynomial substitution therefore shows that $g(r)$ is homogeneous of degree $k$.  To verify coefficient nonnegativity, observe from the coefficient convolution formula that polynomials with nonnegative coefficients are closed under multiplication, and consequently under powers and finite products; they are also closed under finite sums.  Expand $r$ as the finite sum of its monomials.  The substitution of a monomial $c x^\alpha$ is
  \[
  c\prod_i g(i)^{\alpha_i},
  \]
  which has nonnegative coefficients because $c\geq0$ and every $g(i)$ does.  Summing over the support of $r$ proves that all coefficients of $g(r)$ are nonnegative.  By \cref{def:mv-polynomial-derivative-specialization}, the polynomial $g(r)$ is exactly the asserted derivative specialization. -/)
  (title := /-- Structure of a derivative specialization -/)
  (latexEnv := "lemma")]
lemma derivative_specialization_structure {k : ℕ}
    (p : MvPolynomial (Fin (k + 1)) ℝ)
    (hhomogeneous : p.IsHomogeneous (k + 1))
    (hnonnegative : ∀ m, 0 ≤ p.coeff m) :
    (mv_polynomial_derivative_specialization k p).IsHomogeneous k ∧
      (∀ m, 0 ≤ (mv_polynomial_derivative_specialization k p).coeff m) := by
  classical
  constructor
  · have hpderiv : (MvPolynomial.pderiv (Fin.last k) p).IsHomogeneous k := by
      intro m hm
      rw [MvPolynomial.coeff_pderiv] at hm
      have hd := hhomogeneous (left_ne_zero_of_mul hm)
      simpa only [map_add, Finsupp.weight_single, Pi.one_apply, smul_eq_mul, mul_one,
        Nat.add_right_cancel_iff] using hd
    let g : Fin (k + 1) → MvPolynomial (Fin k) ℝ :=
      fun i => if h : i.val < k then MvPolynomial.X ⟨i.val, h⟩ else 0
    have hg : ∀ i, (g i).IsHomogeneous 1 := by
      intro i
      dsimp only [g]
      by_cases h : i.val < k
      · rw [dif_pos h]
        exact MvPolynomial.isHomogeneous_X (R := ℝ) (σ := Fin k) ⟨i.val, h⟩
      · rw [dif_neg h]
        exact MvPolynomial.isHomogeneous_zero (R := ℝ) (σ := Fin k) 1
    rw [mv_polynomial_derivative_specialization]
    change (MvPolynomial.aeval g (MvPolynomial.pderiv (Fin.last k) p)).IsHomogeneous k
    simpa only [one_mul] using
      (MvPolynomial.IsHomogeneous.aeval (R := ℝ) (S := ℝ) (σ := Fin (k + 1))
        (τ := Fin k) (m := k) (n := 1) hpderiv g hg)
  · let NonnegativeCoeff (q : MvPolynomial (Fin k) ℝ) : Prop :=
      ∀ m, 0 ≤ q.coeff m
    have nn_zero : NonnegativeCoeff 0 := by
      intro m
      simp
    have nn_C (c : ℝ) (hc : 0 ≤ c) : NonnegativeCoeff (MvPolynomial.C c) := by
      intro m
      simp only [MvPolynomial.coeff_C]
      split_ifs <;> positivity
    have nn_X (i : Fin k) : NonnegativeCoeff (MvPolynomial.X i) := by
      intro m
      simp only [MvPolynomial.coeff_X]
      split_ifs <;> positivity
    have nn_mul (a b : MvPolynomial (Fin k) ℝ)
        (ha : NonnegativeCoeff a) (hb : NonnegativeCoeff b) :
        NonnegativeCoeff (a * b) := by
      intro m
      rw [MvPolynomial.coeff_mul]
      exact Finset.sum_nonneg fun x _ => mul_nonneg (ha x.1) (hb x.2)
    have nn_pow (a : MvPolynomial (Fin k) ℝ) (ha : NonnegativeCoeff a) :
        ∀ n : ℕ, NonnegativeCoeff (a ^ n) := by
      intro n
      induction n with
      | zero =>
          simpa using nn_C 1 zero_le_one
      | succ n ih =>
          rw [pow_succ]
          exact nn_mul _ _ ih ha
    have nn_prod (s : Finset (Fin (k + 1)))
        (f : Fin (k + 1) → MvPolynomial (Fin k) ℝ)
        (hf : ∀ i ∈ s, NonnegativeCoeff (f i)) :
        NonnegativeCoeff (∏ i ∈ s, f i) := by
      induction s using Finset.induction_on with
      | empty =>
          simpa using nn_C 1 zero_le_one
      | @insert i s hi ih =>
          rw [Finset.prod_insert hi]
          exact nn_mul _ _ (hf i (by simp)) (ih fun j hj => hf j (by simp [hj]))
    let g : Fin (k + 1) → MvPolynomial (Fin k) ℝ :=
      fun i => if h : i.val < k then MvPolynomial.X ⟨i.val, h⟩ else 0
    have nn_g (i : Fin (k + 1)) : NonnegativeCoeff (g i) := by
      dsimp only [g]
      by_cases h : i.val < k
      · rw [dif_pos h]
        exact nn_X ⟨i.val, h⟩
      · rw [dif_neg h]
        exact nn_zero
    have nn_bind_monomial (d : Fin (k + 1) →₀ ℕ) (c : ℝ) (hc : 0 ≤ c) :
        NonnegativeCoeff (MvPolynomial.bind₁ g (MvPolynomial.monomial d c)) := by
      rw [MvPolynomial.bind₁_monomial]
      apply nn_mul
      · exact nn_C c hc
      · apply nn_prod
        intro i hi
        exact nn_pow (g i) (nn_g i) (d i)
    have hpderiv_nonnegative :
        ∀ d, 0 ≤ (MvPolynomial.pderiv (Fin.last k) p).coeff d := by
      intro d
      rw [MvPolynomial.coeff_pderiv]
      exact mul_nonneg (hnonnegative _) (by positivity)
    intro m
    rw [mv_polynomial_derivative_specialization]
    change 0 ≤ (MvPolynomial.bind₁ g
      (MvPolynomial.pderiv (Fin.last k) p)).coeff m
    rw [MvPolynomial.as_sum (MvPolynomial.pderiv (Fin.last k) p)]
    simp only [map_sum, MvPolynomial.coeff_sum]
    exact Finset.sum_nonneg fun d hd =>
      nn_bind_monomial d _ (hpderiv_nonnegative d) m

@[blueprint "lem:mv-polynomial-positive-evaluation"
  (statement := /-- For every $n\in\mathbb N$ and every nonzero polynomial $p\in\mathbb R[x_i\mid i\in\operatorname{Fin}(n)]$, there is a vector $x\in\mathbb R_{>0}^{\operatorname{Fin}(n)}$ such that $p(x)\neq0$. -/)
  (proof := /-- Induct on $n$.  With no variables, evaluation is the canonical equivalence with the coefficient ring.  For $n+1$, use the canonical equivalence between multivariate polynomials in $n+1$ variables and univariate polynomials over the ring in the remaining $n$ variables.  By induction, choose positive values for the remaining variables at which the leading coefficient is nonzero.  The resulting nonzero real univariate polynomial has only finitely many roots, whereas the positive real axis is infinite, so one may choose a positive value of the first variable outside its root set. -/)
  (title := /-- Nonvanishing at a positive point -/)
  (latexEnv := "lemma")]
lemma mv_polynomial_positive_evaluation {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p ≠ 0) :
    ∃ x : Fin n → ℝ, (∀ i, 0 < x i) ∧ MvPolynomial.eval x p ≠ 0 := by
  induction n with
  | zero =>
      let x : Fin 0 → ℝ := fun i => Fin.elim0 i
      refine ⟨x, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro heval
        apply hp
        have hcoeff : p.coeff 0 = 0 := by
          have hsupp : p.support ⊆ {0} := by
            intro m hm
            simpa [Subsingleton.elim m 0]
          rw [MvPolynomial.eval_eq'] at heval
          simpa [Finset.sum_subset hsupp] using heval
        ext m
        simpa [Subsingleton.elim m 0] using hcoeff
  | succ n ih =>
      have eval_finSucc (q : MvPolynomial (Fin (n + 1)) ℝ)
          (y : Fin n → ℝ) (s : ℝ) :
          MvPolynomial.eval y
              (Polynomial.eval (MvPolynomial.C s)
                (MvPolynomial.finSuccEquiv ℝ n q)) =
            MvPolynomial.eval (Fin.cases s y) q := by
        let L : MvPolynomial (Fin (n + 1)) ℝ →+* ℝ :=
          (MvPolynomial.eval y).comp
            ((Polynomial.evalRingHom (MvPolynomial.C s)).comp
              (MvPolynomial.finSuccEquiv ℝ n).toRingHom)
        let R : MvPolynomial (Fin (n + 1)) ℝ →+* ℝ :=
          MvPolynomial.eval (Fin.cases s y)
        have hLR : L = R := MvPolynomial.ringHom_ext
          (by intro a; simp [L, R, MvPolynomial.finSuccEquiv_apply]) (by
            intro i
            cases i using Fin.cases <;>
              simp [L, R, MvPolynomial.finSuccEquiv_eq])
        exact DFunLike.congr_fun hLR q
      let P : Polynomial (MvPolynomial (Fin n) ℝ) :=
        MvPolynomial.finSuccEquiv ℝ n p
      have hP : P ≠ 0 := by
        exact (MvPolynomial.finSuccEquiv ℝ n).injective.ne hp
      have hlead : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
      obtain ⟨x, hxpos, hxlead⟩ := ih P.leadingCoeff hlead
      let F : Polynomial ℝ := P.map (MvPolynomial.eval x)
      have hF : F ≠ 0 := by
        intro hzero
        have hcoeff := congrArg (fun q : Polynomial ℝ => q.coeff P.natDegree) hzero
        apply hxlead
        simpa [F, Polynomial.coeff_map] using hcoeff
      have hexists : ∃ i : Fin (F.natDegree + 1),
          F.eval ((i.val : ℝ) + 1) ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hF
        apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq F 0
            (f := fun i : Fin (F.natDegree + 1) => (i.val : ℝ) + 1)
        · intro i j hij
          apply Fin.ext
          have hij' : (i.val : ℝ) = j.val := by linarith
          exact_mod_cast hij'
        · intro i
          simpa using hall i
        · simp
      obtain ⟨i, hi⟩ := hexists
      let r : ℝ := (i.val : ℝ) + 1
      have hrpos : 0 < r := by dsimp [r]; positivity
      have hreval : F.eval r ≠ 0 := by simpa [r] using hi
      refine ⟨Fin.cases r x, ?_, ?_⟩
      · intro i
        refine Fin.cases hrpos (fun j => ?_) i
        exact hxpos j
      · intro heval
        apply hreval
        have hmap : F.eval r =
            MvPolynomial.eval x (P.eval (MvPolynomial.C r)) := by
          simpa [F] using
            (Polynomial.eval_map_apply (p := P) (f := MvPolynomial.eval x)
              (MvPolynomial.C r))
        rw [hmap]
        change MvPolynomial.eval x
            (Polynomial.eval (MvPolynomial.C r)
              (MvPolynomial.finSuccEquiv ℝ n p)) = 0
        rw [eval_finSucc]
        exact heval

@[blueprint "lem:top-homogeneous-component-nonzero"
  (statement := /-- The homogeneous component in the total degree of a nonzero multivariate polynomial is nonzero. -/)
  (proof := /-- The finite support of a nonzero polynomial is nonempty, so the supremum defining its total degree is attained by some exponent $m$ in the support.  The coefficient of $m$ in the homogeneous component of that degree is therefore the original nonzero coefficient of $m$. -/)
  (title := /-- Nonvanishing of the top homogeneous component -/)
  (latexEnv := "lemma")]
lemma top_homogeneous_component_nonzero {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p ≠ 0) : MvPolynomial.homogeneousComponent p.totalDegree p ≠ 0 := by
  classical
  have hsupp : p.support.Nonempty := MvPolynomial.support_nonempty.mpr hp
  obtain ⟨m, hm, hmax⟩ :=
    Finset.exists_mem_eq_sup p.support hsupp (fun m => m.degree)
  have hdegree : p.totalDegree = m.degree := by
    rw [MvPolynomial.totalDegree_eq]
    convert hmax using 1 <;> simp [Finsupp.degree, Finsupp.sum]
  intro hzero
  have hcoeff := congrArg (fun q : MvPolynomial (Fin n) ℝ => q.coeff m) hzero
  rw [MvPolynomial.coeff_homogeneousComponent, if_pos hdegree.symm] at hcoeff
  simp at hcoeff
  exact (MvPolynomial.mem_support_iff.mp hm) hcoeff

@[blueprint "lem:line-polynomial-top-coefficient"
  (statement := /-- Let $p$ be a real polynomial in finitely many variables, let $z$ be a complex vector, and let $v$ be a real vector with no zero coordinate.  In the univariate polynomial $t\mapsto p(z+tv)$, the coefficient of degree $\deg p$ is the complexification of the value at $v$ of the top homogeneous component of $p$. -/)
  (proof := /-- Expand $p$ as a finite sum of monomials.  Substitution sends the monomial $x^m$ to $\prod_i(z_i+v_it)^{m_i}$, whose degree is $\lvert m\rvert$ and whose leading coefficient is $v^m$, since every $v_i$ is nonzero.  Monomials of degree below $\deg p$ contribute zero to the requested coefficient, while those of top degree sum to the evaluation at $v$ of the top homogeneous component. -/)
  (title := /-- Leading coefficient of a line restriction -/)
  (latexEnv := "lemma")]
lemma line_polynomial_top_coefficient {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (z : Fin n → ℂ) (v : Fin n → ℝ) (hv : ∀ i, v i ≠ 0) :
    (MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
        (fun i => Polynomial.C (z i) +
          Polynomial.C (v i : ℂ) * Polynomial.X) p).coeff p.totalDegree =
      algebraMap ℝ ℂ
        (MvPolynomial.eval v (MvPolynomial.homogeneousComponent p.totalDegree p)) := by
  classical
  let L : Fin n → Polynomial ℂ := fun i =>
    Polynomial.C (z i) + Polynomial.C (v i : ℂ) * Polynomial.X
  have hLne : ∀ i, L i ≠ 0 := by
    intro i hzero
    have hcoeff := congrArg (fun q : Polynomial ℂ => q.coeff 1) hzero
    simpa [L, hv i] using hcoeff
  have hLnat : ∀ i, (L i).natDegree = 1 := by
    intro i
    rw [show L i = Polynomial.C (v i : ℂ) * Polynomial.X +
        Polynomial.C (z i) by simp [L, add_comm]]
    calc
      _ = (Polynomial.C (v i : ℂ) * Polynomial.X).natDegree :=
        Polynomial.natDegree_add_eq_left_of_natDegree_lt (by simp [hv i])
      _ = 1 := by simp [hv i]
  have hLlead : ∀ i, (L i).leadingCoeff = (v i : ℂ) := by
    intro i
    rw [← Polynomial.coeff_natDegree, hLnat]
    simp [L]
  have hprod_nat (m : Fin n →₀ ℕ) :
      (∏ i, (L i) ^ m i).natDegree = m.degree := by
    rw [Polynomial.natDegree_prod]
    · simp [Polynomial.natDegree_pow, hLnat, Finsupp.degree_eq_sum]
    · intro i hi
      exact pow_ne_zero _ (hLne i)
  have hprod_lead (m : Fin n →₀ ℕ) :
      (∏ i, (L i) ^ m i).leadingCoeff =
        ∏ i, (v i : ℂ) ^ m i := by
    rw [Polynomial.leadingCoeff_prod]
    simp [Polynomial.leadingCoeff_pow, hLlead]
  have hprod_coeff (m : Fin n →₀ ℕ) (hm : m ∈ p.support) :
      (∏ i, (L i) ^ m i).coeff p.totalDegree =
        if m.degree = p.totalDegree then ∏ i, (v i : ℂ) ^ m i else 0 := by
    by_cases hdegree : m.degree = p.totalDegree
    · rw [if_pos hdegree, ← hdegree,
        show m.degree = (∏ i, (L i) ^ m i).natDegree from (hprod_nat m).symm,
        Polynomial.coeff_natDegree, hprod_lead]
    · rw [if_neg hdegree]
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [hprod_nat]
      exact lt_of_le_of_ne (MvPolynomial.le_totalDegree hm) hdegree
  rw [MvPolynomial.eval₂_eq']
  change (∑ m ∈ p.support,
      Polynomial.C ((algebraMap ℝ ℂ) (p.coeff m)) *
        ∏ i, (L i) ^ m i).coeff p.totalDegree =
    algebraMap ℝ ℂ
      (MvPolynomial.eval v (MvPolynomial.homogeneousComponent p.totalDegree p))
  rw [MvPolynomial.eval_eq', MvPolynomial.support_homogeneousComponent]
  rw [map_sum]
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul]
  calc
    ∑ m ∈ p.support, (algebraMap ℝ ℂ) (p.coeff m) *
        (∏ i, (L i) ^ m i).coeff p.totalDegree =
        ∑ m ∈ p.support, if m.degree = p.totalDegree then
          (algebraMap ℝ ℂ) (p.coeff m) * ∏ i, (v i : ℂ) ^ m i else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [hprod_coeff m hm]
      split <;> simp
    _ = ∑ m ∈ p.support.filter (fun m => m.degree = p.totalDegree),
        (algebraMap ℝ ℂ) (p.coeff m) * ∏ i, (v i : ℂ) ^ m i := by
      rw [Finset.sum_filter]
    _ = ∑ m ∈ p.support.filter (fun m => m.degree = p.totalDegree),
        (algebraMap ℝ ℂ)
          ((MvPolynomial.homogeneousComponent p.totalDegree p).coeff m) *
            ∏ i, (v i : ℂ) ^ m i := by
      apply Finset.sum_congr rfl
      intro m hm
      have hdegree := (Finset.mem_filter.mp hm).2
      simp [MvPolynomial.coeff_homogeneousComponent, hdegree]
    _ = ∑ m ∈ p.support.filter (fun m => m.degree = p.totalDegree),
        (algebraMap ℝ ℂ)
          ((MvPolynomial.homogeneousComponent p.totalDegree p).coeff m *
            ∏ i, v i ^ m i) := by
      push_cast
      rfl

@[blueprint "lem:positive-directional-derivative-nonvanishing"
  (statement := /-- Let $p$ be a nonzero real-stable polynomial of positive total degree in $n+1$ variables.  Let $v$ have strictly positive coordinates, and suppose that the top homogeneous component of $p$ does not vanish at $v$.  Then the directional derivative $D_vp=\sum_i v_i\partial_i p$ does not vanish when every variable lies in the open upper half-plane. -/)
  (proof := /-- Fix an upper-half-plane point $z$ and form the line restriction $f(t)=p(z+tv)$.  By \cref{lem:line-polynomial-top-coefficient}, the leading coefficient in the total degree of $p$ is the nonzero value of its top homogeneous component at $v$; hence $f$ has positive degree.  Every zero of $f$ has strictly negative imaginary part, since $v_i>0$ and real stability would otherwise make $p(z+tv)$ nonzero.  Gauss--Lucas places every zero of $f'$ in the convex hull of those zeros, which remains in the open lower half-plane.  Since $f'(0)=D_vp(z)$, the directional derivative is nonzero. -/)
  (title := /-- Nonvanishing of a positive directional derivative -/)
  (latexEnv := "lemma")]
lemma positive_directional_derivative_nonvanishing {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ)
    (hp : ∀ z : Fin (n + 1) → ℂ, (∀ i, 0 < (z i).im) →
      MvPolynomial.eval₂ (algebraMap ℝ ℂ) z p ≠ 0)
    (hdegree : 0 < p.totalDegree)
    (v : Fin (n + 1) → ℝ) (hv : ∀ i, 0 < v i)
    (htop : MvPolynomial.eval v
      (MvPolynomial.homogeneousComponent p.totalDegree p) ≠ 0) :
    ∀ z : Fin (n + 1) → ℂ, (∀ i, 0 < (z i).im) →
      MvPolynomial.eval₂ (algebraMap ℝ ℂ) z
        (∑ i, MvPolynomial.C (v i) * MvPolynomial.pderiv i p) ≠ 0 := by
  classical
  have derivative_line (z : Fin (n + 1) → ℂ)
      (q : MvPolynomial (Fin (n + 1)) ℝ) :
      (MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
        (fun i => Polynomial.C (z i) +
          Polynomial.C (v i : ℂ) * Polynomial.X) q).derivative =
      MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
        (fun i => Polynomial.C (z i) +
          Polynomial.C (v i : ℂ) * Polynomial.X)
        (∑ i, MvPolynomial.C (v i) * MvPolynomial.pderiv i q) := by
    induction q using MvPolynomial.induction_on with
    | C a => simp
    | add q r hq hr =>
        simp [hq, hr, mul_add, Finset.sum_add_distrib]
    | mul_X q j hq =>
        simp [Polynomial.derivative_mul, hq, Derivation.leibniz,
          Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul,
          Pi.single_apply]
        conv_rhs =>
          enter [2, x]
          rw [mul_add]
        conv_rhs => rw [Finset.sum_add_distrib]
        have hsingle :
            (∑ x, Polynomial.C (v x : ℂ) *
              MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
                (fun i => Polynomial.C (z i) +
                  Polynomial.C (v i : ℂ) * Polynomial.X)
                (if j = x then q else 0)) =
              Polynomial.C (v j : ℂ) *
                MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
                  (fun i => Polynomial.C (z i) +
                    Polynomial.C (v i : ℂ) * Polynomial.X) q := by
          rw [Finset.sum_eq_single j]
          · simp
          · intro b hb hbj
            simp [Ne.symm hbj]
          · simp
        rw [hsingle]
        have hsecond :
            (∑ x, Polynomial.C (v x : ℂ) *
              ((Polynomial.C (z j) + Polynomial.C (v j : ℂ) * Polynomial.X) *
                MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
                  (fun i => Polynomial.C (z i) +
                    Polynomial.C (v i : ℂ) * Polynomial.X)
                  (MvPolynomial.pderiv x q))) =
              (∑ x, Polynomial.C (v x : ℂ) *
                MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
                  (fun i => Polynomial.C (z i) +
                    Polynomial.C (v i : ℂ) * Polynomial.X)
                  (MvPolynomial.pderiv x q)) *
                (Polynomial.C (z j) + Polynomial.C (v j : ℂ) * Polynomial.X) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x hx
          ring
        rw [hsecond]
        rw [← Finset.sum_mul]
        ac_rfl
  intro z hz hzero
  let f : Polynomial ℂ :=
    MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
      (fun i => Polynomial.C (z i) +
        Polynomial.C (v i : ℂ) * Polynomial.X) p
  have eval_line (q : MvPolynomial (Fin (n + 1)) ℝ) (t : ℂ) :
      (MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
        (fun i => Polynomial.C (z i) +
          Polynomial.C (v i : ℂ) * Polynomial.X) q).eval t =
      MvPolynomial.eval₂ (algebraMap ℝ ℂ)
        (fun i => z i + (v i : ℂ) * t) q := by
    let L : MvPolynomial (Fin (n + 1)) ℝ →+* ℂ :=
      (Polynomial.evalRingHom t).comp
        (MvPolynomial.eval₂Hom (algebraMap ℝ (Polynomial ℂ))
          (fun i => Polynomial.C (z i) +
            Polynomial.C (v i : ℂ) * Polynomial.X))
    let R : MvPolynomial (Fin (n + 1)) ℝ →+* ℂ :=
      MvPolynomial.eval₂Hom (algebraMap ℝ ℂ)
        (fun i => z i + (v i : ℂ) * t)
    have hLR : L = R := MvPolynomial.ringHom_ext
      (by intro a; simp [L, R]) (by intro i; simp [L, R])
    exact DFunLike.congr_fun hLR q
  have hcoeff : f.coeff p.totalDegree =
      algebraMap ℝ ℂ (MvPolynomial.eval v
        (MvPolynomial.homogeneousComponent p.totalDegree p)) := by
    simpa [f] using line_polynomial_top_coefficient p z v (fun i => (hv i).ne')
  have hcoeff_ne : f.coeff p.totalDegree ≠ 0 := by
    rw [hcoeff]
    exact (map_ne_zero (algebraMap ℝ ℂ)).2 htop
  have hf : f ≠ 0 := by
    intro hf
    rw [hf] at hcoeff_ne
    simp at hcoeff_ne
  have hnat : p.totalDegree ≤ f.natDegree :=
    Polynomial.le_natDegree_of_ne_zero hcoeff_ne
  have hfdegree : 0 < f.degree := by
    rw [Polynomial.degree_eq_natDegree hf]
    exact_mod_cast lt_of_lt_of_le hdegree hnat
  have hroots : f.rootSet ℂ ⊆ {t : ℂ | t.im < 0} := by
    intro t ht
    have hteval : f.eval t = 0 := by
      simpa using (Polynomial.mem_rootSet.mp ht).2
    by_contra him
    have him' : 0 ≤ t.im := le_of_not_gt him
    have hz' : ∀ i, 0 < (z i + (v i : ℂ) * t).im := by
      intro i
      simp only [map_add, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
      nlinarith [hz i, hv i]
    exact hp _ hz' (by rw [← eval_line p t, hteval])
  have hderivative_eval : f.derivative.eval 0 = 0 := by
    rw [derivative_line z p]
    rw [eval_line]
    simpa using hzero
  have hderivative_ne : f.derivative ≠ 0 := by
    rw [Polynomial.derivative_ne_zero]
    exact (Nat.ne_of_gt (lt_of_lt_of_le hdegree hnat))
  have hmem : (0 : ℂ) ∈ f.derivative.rootSet ℂ := by
    exact Polynomial.mem_rootSet.mpr ⟨hderivative_ne, by simpa using hderivative_eval⟩
  have hconv := f.rootSet_derivative_subset_convexHull_rootSet hfdegree hmem
  have hconvex : Convex ℝ {t : ℂ | t.im < 0} :=
    convex_halfSpace_lt (.mk Complex.add_im Complex.smul_im) 0
  have hlower := convexHull_min hroots hconvex hconv
  simpa using hlower

@[blueprint "lem:polynomial-root-near-zero"
  (statement := /-- Let $f\in\mathbb C[X]$ be nonzero and let $\delta>0$.  If
  \[
  (\deg f)\lvert f(0)\rvert<\delta\lvert f'(0)\rvert,
  \]
  then $f$ has a zero of modulus less than $\delta$. -/)
  (proof := /-- If $f(0)=0$, take the zero itself.  Otherwise the logarithmic-derivative formula, applied after splitting $f$ over $\mathbb C$, gives
  \[
  \frac{f'(0)}{f(0)}=-\sum_{f(r)=0}\frac1r,
  \]
  with roots counted with multiplicity.  If every root had modulus at least $\delta$, the triangle inequality would yield
  $\lvert f'(0)/f(0)\rvert\leq(\deg f)/\delta$, contrary to the displayed strict inequality. -/)
  (title := /-- A root estimate from the logarithmic derivative -/)
  (latexEnv := "lemma")]
lemma polynomial_root_near_zero (f : Polynomial ℂ) (δ : ℝ)
    (hf : f ≠ 0) (hδ : 0 < δ)
    (hlarge : (f.natDegree : ℝ) * ‖f.eval 0‖ <
      δ * ‖f.derivative.eval 0‖) :
    ∃ r : ℂ, f.eval r = 0 ∧ ‖r‖ < δ := by
  classical
  by_cases h0 : f.eval 0 = 0
  · exact ⟨0, h0, by simpa using hδ⟩
  by_contra hroot
  push Not at hroot
  have hsplits : f.Splits := IsAlgClosed.splits f
  have hlog := hsplits.eval_derivative_div_eval_of_ne_zero h0
  have hterm : ∀ r ∈ f.roots, ‖1 / (0 - r)‖ ≤ 1 / δ := by
    intro r hr
    have hr0 : f.eval r = 0 := (Polynomial.mem_roots hf).mp hr
    have hrδ : δ ≤ ‖r‖ := hroot r hr0
    simpa [norm_div] using one_div_le_one_div_of_le hδ hrδ
  have hbound : ‖f.derivative.eval 0 / f.eval 0‖ ≤
      (f.natDegree : ℝ) / δ := by
    rw [hlog]
    calc
      ‖(f.roots.map fun r => 1 / (0 - r)).sum‖ ≤
          ((f.roots.map fun r => 1 / (0 - r)).map norm).sum :=
        norm_multiset_sum_le _
      _ ≤ (f.roots.map fun _ => 1 / δ).sum := by
        simpa only [Multiset.map_map, Function.comp_apply] using
          Multiset.sum_map_le_sum_map
            (fun r => ‖1 / (0 - r)‖) (fun _ : ℂ => 1 / δ) hterm
      _ = (f.roots.card : ℝ) / δ := by simp [div_eq_mul_inv]
      _ = (f.natDegree : ℝ) / δ := by rw [hsplits.natDegree_eq_card_roots]
  rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr h0), div_eq_mul_inv] at hbound
  have hδnorm : 0 < δ * ‖f.eval 0‖ :=
    mul_pos hδ (norm_pos_iff.mpr h0)
  apply (not_lt_of_ge ?_) hlarge
  calc
    δ * ‖f.derivative.eval 0‖ ≤
        δ * ((f.natDegree : ℝ) * δ⁻¹ * ‖f.eval 0‖) :=
      mul_le_mul_of_nonneg_left hbound hδ.le
    _ = (f.natDegree : ℝ) * ‖f.eval 0‖ := by
      field_simp

@[blueprint "lem:polynomial-family-root-near-zero"
  (statement := /-- Let $(f_n)$ be complex polynomials of uniformly bounded degree.  Suppose that $f_n(0)\to0$ and $f_n'(0)\to a\neq0$.  Then, for every $\delta>0$, all sufficiently large $n$ admit a zero of $f_n$ of modulus less than $\delta$. -/)
  (proof := /-- Fix a common degree bound $N$.  Convergence gives, for all sufficiently large $n$, an upper bound on $\lvert f_n(0)\rvert$ small enough that
  \[
  (\deg f_n)\lvert f_n(0)\rvert<\delta\lvert f_n'(0)\rvert,
  \]
  while convergence to $a\neq0$ bounds $\lvert f_n'(0)\rvert$ away from zero.  Apply \cref{lem:polynomial-root-near-zero}. -/)
  (title := /-- Persistence of a simple polynomial zero -/)
  (latexEnv := "lemma")]
lemma polynomial_family_root_near_zero (f : ℕ → Polynomial ℂ) (N : ℕ) (a : ℂ)
    (hdegree : ∀ n, (f n).natDegree ≤ N)
    (hvalue : Filter.Tendsto (fun n => (f n).eval 0) Filter.atTop (nhds 0))
    (hderivative : Filter.Tendsto (fun n => (f n).derivative.eval 0)
      Filter.atTop (nhds a))
    (ha : a ≠ 0) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in Filter.atTop, ∃ r : ℂ, (f n).eval r = 0 ∧ ‖r‖ < δ := by
  have ha_norm : 0 < ‖a‖ := norm_pos_iff.mpr ha
  let C : ℝ := (N : ℝ) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let ε : ℝ := δ * ‖a‖ / (2 * C)
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨n₀, hn₀⟩ := (Metric.tendsto_atTop.mp hvalue) ε hε
  obtain ⟨n₁, hn₁⟩ :=
    (Metric.tendsto_atTop.mp hderivative) (‖a‖ / 2) (by positivity)
  filter_upwards [Filter.eventually_ge_atTop (max n₀ n₁)] with n hn
  have hn0 : n₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : n₁ ≤ n := le_trans (le_max_right _ _) hn
  have hvalue_small : ‖(f n).eval 0‖ < ε := by
    simpa only [dist_zero_right] using hn₀ n hn0
  have hderivative_close : ‖(f n).derivative.eval 0 - a‖ < ‖a‖ / 2 := by
    simpa only [dist_eq_norm] using hn₁ n hn1
  have hderivative_large : ‖a‖ / 2 < ‖(f n).derivative.eval 0‖ := by
    have hreverse := norm_sub_norm_le a ((f n).derivative.eval 0)
    have hclose' : ‖a - (f n).derivative.eval 0‖ < ‖a‖ / 2 := by
      simpa [norm_sub_rev] using hderivative_close
    nlinarith
  have hfn : f n ≠ 0 := by
    intro hzero
    rw [hzero] at hderivative_large
    simp at hderivative_large
    linarith
  apply polynomial_root_near_zero (f n) δ hfn hδ
  have hdegree_real : ((f n).natDegree : ℝ) ≤ N := by
    exact_mod_cast hdegree n
  have hN_lt_C : (N : ℝ) < C := by dsimp [C]; linarith
  have hCε : C * ε = δ * ‖a‖ / 2 := by
    dsimp [ε]
    field_simp
  calc
    ((f n).natDegree : ℝ) * ‖(f n).eval 0‖ ≤
        (N : ℝ) * ‖(f n).eval 0‖ :=
      mul_le_mul_of_nonneg_right hdegree_real (norm_nonneg _)
    _ < C * ε := by nlinarith [norm_nonneg ((f n).eval 0)]
    _ = δ * ‖a‖ / 2 := hCε
    _ < δ * ‖(f n).derivative.eval 0‖ := by
      simpa [mul_div_assoc] using mul_lt_mul_of_pos_left hderivative_large hδ

@[blueprint "lem:iterate-derivative-roots-in-convex-hull"
  (statement := /-- For every complex polynomial $f$ and every $r\in\mathbb N$, every zero of the $r$-fold derivative of $f$ lies in the convex hull of the zeros of $f$. -/)
  (proof := /-- Induct on $r$.  The assertion for $r=0$ is immediate.  For the successor step, a zero of the derivative of $f^{(r)}$ guarantees that this derivative is nonzero, hence that $f^{(r)}$ has positive degree.  Gauss--Lucas places the zero in the convex hull of the zeros of $f^{(r)}$.  The induction hypothesis places those zeros in the convex hull of the zeros of $f$, and convexity of a convex hull completes the inclusion. -/)
  (title := /-- Zeros of iterated derivatives remain in the original convex hull -/)
  (latexEnv := "lemma")]
lemma iterate_derivative_roots_in_convex_hull (f : Polynomial ℂ) (r : ℕ) :
    (Polynomial.derivative^[r] f).rootSet ℂ ⊆
      convexHull ℝ (f.rootSet ℂ) := by
  induction r with
  | zero =>
      simpa using subset_convexHull ℝ (f.rootSet ℂ)
  | succ r ih =>
      intro z hz
      have hderivative_ne :
          (Polynomial.derivative^[r] f).derivative ≠ 0 := by
        simpa [Function.iterate_succ_apply'] using
          (Polynomial.mem_rootSet.mp hz).1
      have hbase_ne : Polynomial.derivative^[r] f ≠ 0 := by
        intro hzero
        rw [hzero] at hderivative_ne
        simp at hderivative_ne
      have hnat :
          (Polynomial.derivative^[r] f).natDegree ≠ 0 := by
        exact Polynomial.derivative_ne_zero.mp hderivative_ne
      have hdegree : 0 < (Polynomial.derivative^[r] f).degree := by
        rw [Polynomial.degree_eq_natDegree hbase_ne]
        exact_mod_cast Nat.pos_of_ne_zero hnat
      have hgauss :
          z ∈ convexHull ℝ ((Polynomial.derivative^[r] f).rootSet ℂ) := by
        apply
          (Polynomial.derivative^[r] f).rootSet_derivative_subset_convexHull_rootSet
            hdegree
        simpa [Function.iterate_succ_apply'] using hz
      exact convexHull_min ih (convex_convexHull ℝ (f.rootSet ℂ)) hgauss

@[blueprint "lem:polynomial-nonvanishing-sequence"
  (statement := /-- Every nonzero real polynomial admits a sequence of positive nonzeros converging to zero. -/)
  (proof := /-- For the $n$th term, test $deg(f)+1$ distinct points in the interval $(0,1/(n+1))$.  A nonzero polynomial of degree $deg(f)$ cannot vanish at all of them, so choose one nonzero point.  The chosen sequence is positive and bounded above by $1/(n+1)$, and therefore converges to zero by the squeeze theorem. -/)
  (title := /-- A nonvanishing sequence approaching zero -/)
  (latexEnv := "lemma")]
lemma polynomial_nonvanishing_sequence (f : Polynomial ℝ) (hf : f ≠ 0) :
    ∃ t : ℕ → ℝ, (∀ n, 0 < t n) ∧
      Filter.Tendsto t Filter.atTop (nhds 0) ∧
      ∀ n, f.eval (t n) ≠ 0 := by
  have hexists (n : ℕ) :
      ∃ x : ℝ, 0 < x ∧ x < (((n + 1 : ℕ) : ℝ))⁻¹ ∧ f.eval x ≠ 0 := by
    have hbound : 0 < (((n + 1 : ℕ) : ℝ))⁻¹ := by positivity
    have hcand : ∃ i : Fin (f.natDegree + 1),
        f.eval
          ((((i.val : ℝ) + 1) / ((f.natDegree : ℝ) + 2)) *
            (((n + 1 : ℕ) : ℝ))⁻¹) ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hf
      apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq f 0
          (f := fun i : Fin (f.natDegree + 1) =>
            (((i.val : ℝ) + 1) / ((f.natDegree : ℝ) + 2)) *
              (((n + 1 : ℕ) : ℝ))⁻¹)
      · intro i j hij
        apply Fin.ext
        have hden : 0 < (f.natDegree : ℝ) + 2 := by positivity
        have hinv : (((n + 1 : ℕ) : ℝ))⁻¹ ≠ 0 := ne_of_gt hbound
        have hij' : (i.val : ℝ) = j.val := by
          apply (add_left_inj (a := (1 : ℝ))).mp
          apply (div_left_inj' (ne_of_gt hden)).mp
          exact mul_right_cancel₀ hinv hij
        exact_mod_cast hij'
      · intro i
        simpa using hall i
      · simp
    obtain ⟨i, hi⟩ := hcand
    refine ⟨(((i.val : ℝ) + 1) / ((f.natDegree : ℝ) + 2)) *
        (((n + 1 : ℕ) : ℝ))⁻¹, ?_, ?_, hi⟩
    · positivity
    · have hi_le : (i.val : ℝ) + 1 < (f.natDegree : ℝ) + 2 := by
        have hi_nat : i.val + 1 < f.natDegree + 2 := by omega
        exact_mod_cast hi_nat
      have hratio :
          ((i.val : ℝ) + 1) / ((f.natDegree : ℝ) + 2) < 1 := by
        apply (div_lt_one (by positivity)).2
        exact hi_le
      nlinarith
  choose t htpos htbound htne using hexists
  refine ⟨t, htpos, ?_, htne⟩
  apply squeeze_zero (fun n => (htpos n).le) (fun n => (htbound n).le)
  simpa [Function.comp_def] using
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (Filter.tendsto_add_atTop_nat 1)

@[blueprint "lem:line-polynomial-degree-bound"
  (statement := /-- Restricting a multivariate polynomial of total degree $d$ to an affine line produces a univariate polynomial of degree at most $d$. -/)
  (proof := /-- Expand the multivariate polynomial into its supported monomials.  Each substituted variable is affine-linear, so the image of a monomial of exponent $m$ has degree at most $\lvert m\rvert$.  Every supported exponent has size at most the total degree, and the degree of a finite sum is bounded by the maximum of the degrees of its summands. -/)
  (title := /-- Degree bound for an affine-line restriction -/)
  (latexEnv := "lemma")]
lemma line_polynomial_degree_bound {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (z : Fin n → ℂ) (v : Fin n → ℝ) :
    (MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
      (fun i => Polynomial.C (z i) +
        Polynomial.C (v i : ℂ) * Polynomial.X) p).natDegree ≤ p.totalDegree := by
  classical
  rw [MvPolynomial.eval₂_eq']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  calc
    (∏ i, (Polynomial.C (z i) +
        Polynomial.C (v i : ℂ) * Polynomial.X) ^ m i).natDegree ≤
        ∑ i, ((Polynomial.C (z i) +
          Polynomial.C (v i : ℂ) * Polynomial.X) ^ m i).natDegree := by
      exact
        Polynomial.natDegree_prod_le (Finset.univ : Finset (Fin n))
          (fun i => (Polynomial.C (z i) +
            Polynomial.C (v i : ℂ) * Polynomial.X) ^ m i)
    _ ≤ ∑ i, m i := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        ((Polynomial.C (z i) +
            Polynomial.C (v i : ℂ) * Polynomial.X) ^ m i).natDegree ≤
            m i * (Polynomial.C (z i) +
              Polynomial.C (v i : ℂ) * Polynomial.X).natDegree :=
          Polynomial.natDegree_pow_le
        _ ≤ m i * 1 := Nat.mul_le_mul_left _ (by compute_degree)
        _ = m i := by simp
    _ = m.degree := by simp [Finsupp.degree_eq_sum]
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hm

@[blueprint "lem:line-polynomial-derivative"
  (statement := /-- The derivative of the restriction of a multivariate polynomial to the affine line $z+tv$ is the restriction to that line of the directional derivative $\sum_i v_i\partial_i p$. -/)
  (proof := /-- Both sides are derivations in the multivariate polynomial.  They agree on constants.  For a product by a variable, the ordinary product rule on the line and the multivariate Leibniz rule give the same two terms, with the derivative of the substituted variable equal to its direction coefficient.  Induction on multivariate polynomials proves the identity. -/)
  (title := /-- Derivative of an affine-line restriction -/)
  (latexEnv := "lemma")]
lemma line_polynomial_derivative {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (z : Fin n → ℂ) (v : Fin n → ℝ) :
    (MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
      (fun i => Polynomial.C (z i) +
        Polynomial.C (v i : ℂ) * Polynomial.X) p).derivative =
    MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
      (fun i => Polynomial.C (z i) +
        Polynomial.C (v i : ℂ) * Polynomial.X)
      (∑ i, MvPolynomial.C (v i) * MvPolynomial.pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      simp [hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p j hp =>
      simp [Polynomial.derivative_mul, hp, Derivation.leibniz,
        Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul,
        Pi.single_apply]
      conv_rhs =>
        enter [2, x]
        rw [mul_add]
      conv_rhs => rw [Finset.sum_add_distrib]
      have hsingle :
          (∑ x, Polynomial.C (v x : ℂ) *
            MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
              (fun i => Polynomial.C (z i) +
                Polynomial.C (v i : ℂ) * Polynomial.X)
              (if j = x then p else 0)) =
            Polynomial.C (v j : ℂ) *
              MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
                (fun i => Polynomial.C (z i) +
                  Polynomial.C (v i : ℂ) * Polynomial.X) p := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro b hb hbj
          simp [Ne.symm hbj]
        · simp
      rw [hsingle]
      have hsecond :
          (∑ x, Polynomial.C (v x : ℂ) *
            ((Polynomial.C (z j) + Polynomial.C (v j : ℂ) * Polynomial.X) *
              MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
                (fun i => Polynomial.C (z i) +
                  Polynomial.C (v i : ℂ) * Polynomial.X)
                (MvPolynomial.pderiv x p))) =
            (∑ x, Polynomial.C (v x : ℂ) *
              MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
                (fun i => Polynomial.C (z i) +
                  Polynomial.C (v i : ℂ) * Polynomial.X)
                (MvPolynomial.pderiv x p)) *
              (Polynomial.C (z j) + Polynomial.C (v j : ℂ) * Polynomial.X) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      rw [hsecond]
      rw [← Finset.sum_mul]
      ac_rfl

@[blueprint "lem:line-polynomial-family-convergence"
  (statement := /-- Let $q_i$ be finitely many fixed real multivariate polynomials.  If the base points $a_n$ and real coefficient vectors $v_n$ converge to $a$ and $v$, respectively, then every fixed iterated derivative at zero of the affine-line restrictions of $\sum_i(v_n)_iq_i$ converges to the corresponding iterated derivative for $\sum_i v_iq_i$. -/)
  (proof := /-- For zeroth derivatives, evaluation at zero is the finite sum
  \[
  \sum_i (v_n)_i q_i(a_n).
  \]
  Each summand converges by continuity of multivariate-polynomial evaluation, so the finite sum converges.  For the induction step, apply \cref{lem:line-polynomial-derivative}: differentiating a line restriction replaces every fixed $q_i$ by its directional derivative in the line direction.  These are again fixed polynomials, and the induction hypothesis applies. -/)
  (title := /-- Convergence of derivatives of polynomial line restrictions -/)
  (latexEnv := "lemma")]
lemma line_polynomial_family_convergence {n : ℕ}
    (q : Fin n → MvPolynomial (Fin n) ℝ)
    (a : ℕ → Fin n → ℂ) (a₀ : Fin n → ℂ)
    (v : ℕ → Fin n → ℝ) (v₀ : Fin n → ℝ)
    (b : Fin n → ℝ)
    (ha : Filter.Tendsto a Filter.atTop (nhds a₀))
    (hv : Filter.Tendsto v Filter.atTop (nhds v₀)) :
    ∀ r : ℕ,
      Filter.Tendsto
        (fun m =>
          (Polynomial.derivative^[r]
            (MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
              (fun i => Polynomial.C (a m i) +
                Polynomial.C (b i : ℂ) * Polynomial.X)
              (∑ i, MvPolynomial.C (v m i) * q i))).eval 0)
        Filter.atTop
        (nhds
          ((Polynomial.derivative^[r]
            (MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
              (fun i => Polynomial.C (a₀ i) +
                Polynomial.C (b i : ℂ) * Polynomial.X)
              (∑ i, MvPolynomial.C (v₀ i) * q i))).eval 0)) := by
  intro r
  induction r generalizing q with
  | zero =>
      have heval_tendsto (p : MvPolynomial (Fin n) ℝ) :
          Filter.Tendsto
            (fun m => MvPolynomial.eval₂ (algebraMap ℝ ℂ) (a m) p)
            Filter.atTop
            (nhds (MvPolynomial.eval₂ (algebraMap ℝ ℂ) a₀ p)) := by
        induction p using MvPolynomial.induction_on with
        | C x => simp
        | add p s hp hs =>
            simpa using hp.add hs
        | mul_X p j hp =>
            have haj : Filter.Tendsto (fun m => a m j) Filter.atTop (nhds (a₀ j)) :=
              (tendsto_pi_nhds.mp ha) j
            simpa using hp.mul haj
      have heval (c : Fin n → ℂ) (d : Fin n → ℝ) :
          (MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
            (fun i => Polynomial.C (c i) +
              Polynomial.C (b i : ℂ) * Polynomial.X)
            (∑ i, MvPolynomial.C (d i) * q i)).eval 0 =
            ∑ i, (d i : ℂ) *
              MvPolynomial.eval₂ (algebraMap ℝ ℂ) c (q i) := by
        let L : MvPolynomial (Fin n) ℝ →+* ℂ :=
          (Polynomial.evalRingHom 0).comp
            (MvPolynomial.eval₂Hom (algebraMap ℝ (Polynomial ℂ))
              (fun i => Polynomial.C (c i) +
                Polynomial.C (b i : ℂ) * Polynomial.X))
        let R : MvPolynomial (Fin n) ℝ →+* ℂ :=
          MvPolynomial.eval₂Hom (algebraMap ℝ ℂ) c
        have hLR : L = R := MvPolynomial.ringHom_ext
          (by intro x; simp [L, R]) (by intro i; simp [L, R])
        change L (∑ i, MvPolynomial.C (d i) * q i) = _
        rw [hLR]
        simp [R]
      simp only [Function.iterate_zero_apply]
      simp_rw [heval]
      apply tendsto_finset_sum
      intro i hi
      have hvi : Filter.Tendsto (fun m => v m i) Filter.atTop (nhds (v₀ i)) :=
        (tendsto_pi_nhds.mp hv) i
      have hai : Filter.Tendsto
          (fun m => MvPolynomial.eval₂ (algebraMap ℝ ℂ) (a m) (q i))
          Filter.atTop
          (nhds (MvPolynomial.eval₂ (algebraMap ℝ ℂ) a₀ (q i))) := by
        exact heval_tendsto (q i)
      exact (Complex.continuous_ofReal.tendsto (v₀ i) |>.comp hvi).mul hai
  | succ r ih =>
      let q' : Fin n → MvPolynomial (Fin n) ℝ := fun i =>
        ∑ j, MvPolynomial.C (b j) * MvPolynomial.pderiv j (q i)
      have hderivative (c : Fin n → ℂ) (d : Fin n → ℝ) :
          (MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
            (fun i => Polynomial.C (c i) +
              Polynomial.C (b i : ℂ) * Polynomial.X)
            (∑ i, MvPolynomial.C (d i) * q i)).derivative =
          MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
            (fun i => Polynomial.C (c i) +
              Polynomial.C (b i : ℂ) * Polynomial.X)
            (∑ i, MvPolynomial.C (d i) * q' i) := by
        rw [line_polynomial_derivative]
        simp only [map_sum, MvPolynomial.pderiv_C_mul]
        apply congrArg
          (MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
            (fun i => Polynomial.C (c i) +
              Polynomial.C (b i : ℂ) * Polynomial.X))
        simp only [q', Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      simpa only [Function.iterate_succ_apply, hderivative] using ih q'

@[blueprint "lem:derivative-specialization-evaluation"
  (statement := /-- Evaluating the last-variable derivative specialization at values $x_0,\ldots,x_{k-1}$ is equal to evaluating the original last partial derivative at those same values and at zero in the last coordinate. -/)
  (proof := /-- Unfold \cref{def:mv-polynomial-derivative-specialization}.  The evaluation homomorphism composed with the substitution sends each index $i<k$ to the corresponding value $x_i$ and sends the unique remaining index to zero.  The substitution--evaluation composition law gives the asserted identity. -/)
  (title := /-- Evaluation of a derivative specialization -/)
  (latexEnv := "lemma")]
lemma derivative_specialization_evaluation {k : ℕ}
    (p : MvPolynomial (Fin (k + 1)) ℝ) {S : Type*}
    [CommSemiring S] [Algebra ℝ S] (x : Fin k → S) :
    MvPolynomial.eval₂ (algebraMap ℝ S) x
        (mv_polynomial_derivative_specialization k p) =
      MvPolynomial.eval₂ (algebraMap ℝ S)
        (fun i => if h : i.val < k then x ⟨i.val, h⟩ else 0)
        (MvPolynomial.pderiv (Fin.last k) p) := by
  rw [mv_polynomial_derivative_specialization]
  change (MvPolynomial.eval₂Hom (algebraMap ℝ S) x)
      (MvPolynomial.bind₁ _ (MvPolynomial.pderiv (Fin.last k) p)) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  apply MvPolynomial.eval₂_congr
  intro i
  split <;> simp_all

@[blueprint "lem:line-polynomial-evaluation"
  (statement := /-- Evaluating the univariate restriction of a multivariate polynomial to the affine line $z+sv$ at $s=t$ gives the multivariate evaluation at $z+tv$. -/)
  (proof := /-- Compose the multivariate evaluation homomorphism into univariate polynomials with evaluation at $t$.  This composite and direct multivariate evaluation at $z+tv$ agree on coefficients and on every variable, so the multivariate-polynomial ring-homomorphism extensionality theorem makes them equal. -/)
  (title := /-- Evaluation of an affine-line restriction -/)
  (latexEnv := "lemma")]
lemma line_polynomial_evaluation {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (z : Fin n → ℂ) (v : Fin n → ℝ) (t : ℂ) :
    (MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
      (fun i => Polynomial.C (z i) +
        Polynomial.C (v i : ℂ) * Polynomial.X) p).eval t =
      MvPolynomial.eval₂ (algebraMap ℝ ℂ)
        (fun i => z i + (v i : ℂ) * t) p := by
  let L : MvPolynomial (Fin n) ℝ →+* ℂ :=
    (Polynomial.evalRingHom t).comp
      (MvPolynomial.eval₂Hom (algebraMap ℝ (Polynomial ℂ))
        (fun i => Polynomial.C (z i) +
          Polynomial.C (v i : ℂ) * Polynomial.X))
  let R : MvPolynomial (Fin n) ℝ →+* ℂ :=
    MvPolynomial.eval₂Hom (algebraMap ℝ ℂ)
      (fun i => z i + (v i : ℂ) * t)
  have hLR : L = R := MvPolynomial.ringHom_ext
    (by intro x; simp [L, R]) (by intro i; simp [L, R])
  exact DFunLike.congr_fun hLR p

@[blueprint "lem:real-stable-derivative-specialization"
  (statement := /-- For every $k\in\mathbb N$ and every polynomial $p\in\mathbb R[x_i\mid i\in\operatorname{Fin}(k+1)]$, if $p$ is real stable, then the polynomial in $\mathbb R[x_i\mid i\in\operatorname{Fin}(k)]$ obtained by differentiating $p$ with respect to its last variable and setting that variable equal to zero is real stable.  Real stability includes the zero polynomial, so this derivative specialization may vanish identically. -/)
  (proof := /-- Write $q$ for the derivative specialization in \cref{def:mv-polynomial-derivative-specialization}.  If $q=0$, the conclusion is the zero alternative in \cref{def:real-stable-mv-polynomial}.  Suppose instead that $q\neq0$ and that $q(z)=0$ at an upper-half-plane point $z$.  The case $k=0$ is impossible because a nonzero polynomial with no variables is a nonzero constant.

  By \cref{lem:top-homogeneous-component-nonzero, lem:mv-polynomial-positive-evaluation}, choose $w\in\mathbb R_{>0}^{\operatorname{Fin}(k)}$ at which the top homogeneous component of $q$ is nonzero.  Let
  \[
  Q(s)=q(z+sw).
  \]
  The coefficient identity in \cref{lem:line-polynomial-top-coefficient} makes $Q$ nonzero.  Since $Q(0)=0$, let $m$ be its root multiplicity at zero, put $r=m-1$, and set $A=Q^{(r)}$.  Then $A(0)=0$ and $A'(0)\neq0$.

  Apply \cref{lem:top-homogeneous-component-nonzero, lem:mv-polynomial-positive-evaluation} to $p$ and choose $u>0$ at which its top homogeneous component is nonzero.  The real polynomial obtained by evaluating that homogeneous component at
  \[
  (t u_0,\ldots,t u_{k-1},u_k)
  \]
  is nonzero at $t=1$.  Hence \cref{lem:polynomial-nonvanishing-sequence} supplies positive $t_n\to0$ at which it remains nonzero.  Define a positive direction $v_n$ by $(v_n)_i=t_nu_i$ for $i<k$ and $(v_n)_k=u_k$, and let
  \[
  D_n p=\sum_i(v_n)_i\partial_i p.
  \]
  By \cref{lem:positive-directional-derivative-nonvanishing}, every $D_np$ is nonvanishing on the open upper half-plane.

  Put the last coordinate at $it_n$, restrict the first $k$ coordinates to the line $z+sw$, and call the resulting univariate polynomial $F_n(s)$.  The identity in \cref{lem:derivative-specialization-evaluation} identifies the limiting line polynomial with $u_kQ$.  The convergence lemma \cref{lem:line-polynomial-family-convergence} therefore gives
  \[
  (F_n^{(r)})(0)\longrightarrow u_kA(0)=0,
  \qquad
  (F_n^{(r+1)})(0)\longrightarrow u_kA'(0)\neq0.
  \]
  By \cref{lem:line-polynomial-degree-bound}, the degrees of all $F_n^{(r)}$ have a common finite bound.

  Let
  \[
  \delta=\min_{i<k}\frac{\operatorname{Im}z_i}{w_i}>0.
  \]
  If $F_n(s)=0$ and $\operatorname{Im}s>-\delta$, every first coordinate $z_i+w_is$ has positive imaginary part, and so does the last coordinate $it_n$.  This contradicts the nonvanishing of $D_np$; the equality between these evaluations is \cref{lem:line-polynomial-evaluation}.  Thus every zero of $F_n$ lies in the closed half-plane $\operatorname{Im}s\leq-\delta$.

  Apply \cref{lem:polynomial-family-root-near-zero} to $G_n=F_n^{(r)}$.  For all sufficiently large $n$, it produces a zero $s_n$ of $G_n$ with $\lvert s_n\rvert<\delta$.  On the other hand, \cref{lem:iterate-derivative-roots-in-convex-hull} puts every zero of $G_n$ in the convex hull of the zeros of $F_n$.  The closed half-plane above is convex, so $\operatorname{Im}s_n\leq-\delta$ and consequently $\lvert s_n\rvert\geq\delta$, a contradiction.  Therefore a nonzero $q$ cannot vanish at any upper-half-plane point, which is the nonzero alternative in \cref{def:real-stable-mv-polynomial}. -/)
  (title := /-- Real stability under derivative specialization -/)
  (latexEnv := "lemma")]
lemma real_stable_derivative_specialization {k : ℕ}
    (p : MvPolynomial (Fin (k + 1)) ℝ)
    (hstable : real_stable_mv_polynomial p) :
    real_stable_mv_polynomial
      (mv_polynomial_derivative_specialization k p) := by
  classical
  let q : MvPolynomial (Fin k) ℝ :=
    mv_polynomial_derivative_specialization k p
  change real_stable_mv_polynomial q
  by_cases hq : q = 0
  · exact Or.inl hq
  refine Or.inr ?_
  have hpne : p ≠ 0 := by
    intro hpzero
    apply hq
    simp [q, mv_polynomial_derivative_specialization, hpzero]
  have hpstable : ∀ z : Fin (k + 1) → ℂ, (∀ i, 0 < (z i).im) →
      MvPolynomial.eval₂ (algebraMap ℝ ℂ) z p ≠ 0 :=
    hstable.resolve_left hpne
  intro z hz hqz
  by_cases hk : k = 0
  · subst k
    apply hq
    have hsupp : q.support ⊆ {0} := by
      intro m hm
      simpa [Subsingleton.elim m 0]
    have hcoeff : q.coeff 0 = 0 := by
      have hmap : algebraMap ℝ ℂ (q.coeff 0) = 0 := by
        rw [MvPolynomial.eval₂_eq'] at hqz
        simpa [Finset.sum_subset hsupp, Subsingleton.elim] using hqz
      exact (map_eq_zero (algebraMap ℝ ℂ)).mp hmap
    ext m
    simpa [Subsingleton.elim m 0] using hcoeff
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hkpos
  have hqtop :
      MvPolynomial.homogeneousComponent q.totalDegree q ≠ 0 :=
    top_homogeneous_component_nonzero q hq
  obtain ⟨w, hwpos, hwtop⟩ :=
    mv_polynomial_positive_evaluation
      (MvPolynomial.homogeneousComponent q.totalDegree q) hqtop
  let Q : Polynomial ℂ :=
    MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
      (fun i => Polynomial.C (z i) +
        Polynomial.C (w i : ℂ) * Polynomial.X) q
  have hQcoeff : Q.coeff q.totalDegree =
      algebraMap ℝ ℂ
        (MvPolynomial.eval w
          (MvPolynomial.homogeneousComponent q.totalDegree q)) := by
    simpa [Q] using
      line_polynomial_top_coefficient q z w (fun i => (hwpos i).ne')
  have hQne : Q ≠ 0 := by
    intro hzero
    have := congrArg (fun f : Polynomial ℂ => f.coeff q.totalDegree) hzero
    rw [hQcoeff] at this
    exact (map_ne_zero (algebraMap ℝ ℂ)).2 hwtop (by simpa using this)
  have hQzero : Q.eval 0 = 0 := by
    dsimp [Q]
    rw [line_polynomial_evaluation]
    simpa using hqz
  have hQroot : Q.IsRoot 0 := hQzero
  let m : ℕ := Q.rootMultiplicity 0
  have hmpos : 0 < m := by
    exact (Polynomial.rootMultiplicity_pos hQne).2 hQroot
  let r : ℕ := m - 1
  let A : Polynomial ℂ := Polynomial.derivative^[r] Q
  have hrlt : r < m := by
    dsimp [r]
    omega
  have hAzero : A.eval 0 = 0 := by
    exact Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity hrlt
  have hr_succ : r + 1 = m := by
    dsimp [r]
    omega
  have hAderivative_ne : A.derivative.eval 0 ≠ 0 := by
    have hfactor :
        (m.factorial : ℂ) *
          (Q /ₘ (Polynomial.X - Polynomial.C 0) ^ m).eval 0 ≠ 0 := by
      apply mul_ne_zero
      · exact_mod_cast Nat.factorial_ne_zero m
      · exact Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero 0 hQne
    rw [show A.derivative = Polynomial.derivative^[m] Q by
      simp [A, ← hr_succ, Function.iterate_succ_apply']]
    rw [Polynomial.eval_iterate_derivative_rootMultiplicity]
    simpa [m, nsmul_eq_mul] using hfactor
  have hpdegree : 0 < p.totalDegree := by
    apply Nat.pos_of_ne_zero
    intro hdegree
    have hpC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegree
    have hpder : MvPolynomial.pderiv (Fin.last k) p = 0 := by
      rw [hpC, MvPolynomial.pderiv_C]
    apply hq
    simp only [q, mv_polynomial_derivative_specialization, hpder, map_zero]
  have hptop :
      MvPolynomial.homogeneousComponent p.totalDegree p ≠ 0 :=
    top_homogeneous_component_nonzero p hpne
  obtain ⟨u, hupos, hutop⟩ :=
    mv_polynomial_positive_evaluation
      (MvPolynomial.homogeneousComponent p.totalDegree p) hptop
  let H : MvPolynomial (Fin (k + 1)) ℝ :=
    MvPolynomial.homogeneousComponent p.totalDegree p
  let B : Polynomial ℝ :=
    MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℝ))
      (fun i => if h : i.val < k then
        Polynomial.C (u i) * Polynomial.X else Polynomial.C (u i)) H
  have hBone : B.eval 1 = MvPolynomial.eval u H := by
    let L : MvPolynomial (Fin (k + 1)) ℝ →+* ℝ :=
      (Polynomial.evalRingHom 1).comp
        (MvPolynomial.eval₂Hom (algebraMap ℝ (Polynomial ℝ))
          (fun i => if h : i.val < k then
            Polynomial.C (u i) * Polynomial.X else Polynomial.C (u i)))
    let R : MvPolynomial (Fin (k + 1)) ℝ →+* ℝ := MvPolynomial.eval u
    have hLR : L = R := MvPolynomial.ringHom_ext
      (by intro x; simp [L, R]) (by
        intro i
        by_cases hi : i.val < k <;> simp [L, R, hi])
    exact DFunLike.congr_fun hLR H
  have hBne : B ≠ 0 := by
    intro hzero
    apply hutop
    rw [← hBone, hzero]
    simp
  obtain ⟨t, htpos, httend, htne⟩ :=
    polynomial_nonvanishing_sequence B hBne
  let v : ℕ → Fin (k + 1) → ℝ := fun n i =>
    if h : i.val < k then t n * u i else u i
  let v₀ : Fin (k + 1) → ℝ := fun i =>
    if h : i.val < k then 0 else u i
  let a : ℕ → Fin (k + 1) → ℂ := fun n i =>
    if h : i.val < k then z ⟨i.val, h⟩ else Complex.I * (t n : ℂ)
  let a₀ : Fin (k + 1) → ℂ := fun i =>
    if h : i.val < k then z ⟨i.val, h⟩ else 0
  let b : Fin (k + 1) → ℝ := fun i =>
    if h : i.val < k then w ⟨i.val, h⟩ else 0
  have hvpos (n : ℕ) : ∀ i, 0 < v n i := by
    intro i
    by_cases hi : i.val < k
    · simp [v, hi, mul_pos (htpos n) (hupos i)]
    · simp [v, hi, hupos i]
  have hvlim : Filter.Tendsto v Filter.atTop (nhds v₀) := by
    rw [tendsto_pi_nhds]
    intro i
    by_cases hi : i.val < k
    · simpa [v, v₀, hi] using httend.mul_const (u i)
    · simp [v, v₀, hi]
  have halim : Filter.Tendsto a Filter.atTop (nhds a₀) := by
    rw [tendsto_pi_nhds]
    intro i
    by_cases hi : i.val < k
    · simp [a, a₀, hi]
    · have htcomplex : Filter.Tendsto (fun n => (t n : ℂ))
          Filter.atTop (nhds 0) :=
        (Complex.continuous_ofReal.tendsto 0).comp httend
      simpa [a, a₀, hi] using tendsto_const_nhds.mul htcomplex
  have htopv (n : ℕ) : MvPolynomial.eval (v n) H ≠ 0 := by
    have heval : B.eval (t n) = MvPolynomial.eval (v n) H := by
      let L : MvPolynomial (Fin (k + 1)) ℝ →+* ℝ :=
        (Polynomial.evalRingHom (t n)).comp
          (MvPolynomial.eval₂Hom (algebraMap ℝ (Polynomial ℝ))
            (fun i => if h : i.val < k then
              Polynomial.C (u i) * Polynomial.X else Polynomial.C (u i)))
      let R : MvPolynomial (Fin (k + 1)) ℝ →+* ℝ :=
        MvPolynomial.eval (v n)
      have hLR : L = R := MvPolynomial.ringHom_ext
        (by intro x; simp [L, R]) (by
          intro i
          by_cases hi : i.val < k
          · simp [L, R, v, hi]
            ring
          · simp [L, R, v, hi])
      exact DFunLike.congr_fun hLR H
    rw [← heval]
    exact htne n
  let D : ℕ → MvPolynomial (Fin (k + 1)) ℝ := fun n =>
    ∑ i, MvPolynomial.C (v n i) * MvPolynomial.pderiv i p
  have hDstable (n : ℕ) :
      ∀ y : Fin (k + 1) → ℂ, (∀ i, 0 < (y i).im) →
        MvPolynomial.eval₂ (algebraMap ℝ ℂ) y (D n) ≠ 0 := by
    simpa [D, H] using
      positive_directional_derivative_nonvanishing p hpstable hpdegree
        (v n) (hvpos n) (htopv n)
  let F : ℕ → Polynomial ℂ := fun n =>
    MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
      (fun i => Polynomial.C (a n i) +
        Polynomial.C (b i : ℂ) * Polynomial.X) (D n)
  let F₀ : Polynomial ℂ :=
    MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
      (fun i => Polynomial.C (a₀ i) +
        Polynomial.C (b i : ℂ) * Polynomial.X)
      (∑ i, MvPolynomial.C (v₀ i) * MvPolynomial.pderiv i p)
  have hdirzero :
      (∑ i, MvPolynomial.C (v₀ i) * MvPolynomial.pderiv i p) =
        MvPolynomial.C (u (Fin.last k)) *
          MvPolynomial.pderiv (Fin.last k) p := by
    rw [Finset.sum_eq_single (Fin.last k)]
    · simp [v₀]
    · intro i hi hine
      have hilt : i.val < k := by
        have hle : i.val ≤ k := Nat.le_of_lt_succ i.isLt
        have hneval : i.val ≠ k := by
          intro heq
          apply hine
          apply Fin.ext
          simpa using heq
        omega
      simp [v₀, hilt]
    · simp
  have hspecial :
      Q = MvPolynomial.eval₂ (algebraMap ℝ (Polynomial ℂ))
        (fun i => Polynomial.C (a₀ i) +
          Polynomial.C (b i : ℂ) * Polynomial.X)
        (MvPolynomial.pderiv (Fin.last k) p) := by
    have h := derivative_specialization_evaluation p
      (fun i : Fin k => Polynomial.C (z i) +
        Polynomial.C (w i : ℂ) * Polynomial.X)
    change Q = _ at h
    rw [h]
    apply MvPolynomial.eval₂_congr
    intro i
    by_cases hi : i.val < k
    · simp [a₀, b, hi]
    · simp [a₀, b, hi]
  have hFzero : F₀ = Polynomial.C (u (Fin.last k) : ℂ) * Q := by
    dsimp [F₀]
    rw [hdirzero, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, hspecial]
    rfl
  let G : ℕ → Polynomial ℂ := fun n => Polynomial.derivative^[r] (F n)
  let N : ℕ := ∑ i, (MvPolynomial.pderiv i p).totalDegree
  have hFdegree (n : ℕ) : (F n).natDegree ≤ N := by
    calc
      (F n).natDegree ≤ (D n).totalDegree := by
        simpa [F] using line_polynomial_degree_bound (D n) (a n) b
      _ ≤ N := by
        apply MvPolynomial.totalDegree_finsetSum_le
        intro i hi
        calc
          (MvPolynomial.C (v n i) * MvPolynomial.pderiv i p).totalDegree ≤
              (MvPolynomial.pderiv i p).totalDegree := by
            simpa [← MvPolynomial.smul_eq_C_mul] using
              MvPolynomial.totalDegree_smul_le (v n i)
                (MvPolynomial.pderiv i p)
          _ ≤ N := by
            dsimp [N]
            exact Finset.single_le_sum
              (s := Finset.univ)
              (f := fun j => (MvPolynomial.pderiv j p).totalDegree)
              (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
  have hGdegree (n : ℕ) : (G n).natDegree ≤ N := by
    exact le_trans
      (Polynomial.natDegree_iterate_derivative (F n) r)
      (le_trans (Nat.sub_le _ _) (hFdegree n))
  have hconv (s : ℕ) :
      Filter.Tendsto (fun n => (Polynomial.derivative^[s] (F n)).eval 0)
        Filter.atTop
        (nhds ((Polynomial.derivative^[s] F₀).eval 0)) := by
    simpa [F, D, F₀] using
      line_polynomial_family_convergence
        (fun i : Fin (k + 1) => MvPolynomial.pderiv i p)
        a a₀ v v₀ b halim hvlim s
  have hGvalue : Filter.Tendsto (fun n => (G n).eval 0)
      Filter.atTop (nhds 0) := by
    have hc := hconv r
    rw [hFzero] at hc
    simpa [G, Polynomial.iterate_derivative_C_mul, hAzero, A] using hc
  let c : ℂ := (u (Fin.last k) : ℂ) * A.derivative.eval 0
  have hcne : c ≠ 0 := by
    exact mul_ne_zero
      ((map_ne_zero (algebraMap ℝ ℂ)).2 (hupos (Fin.last k)).ne')
      hAderivative_ne
  have hGderivative : Filter.Tendsto
      (fun n => (G n).derivative.eval 0) Filter.atTop (nhds c) := by
    have hc' := hconv (r + 1)
    rw [hFzero] at hc'
    simpa [G, c, A, Polynomial.iterate_derivative_C_mul,
      Function.iterate_succ_apply'] using hc'
  let ratios : Finset ℝ :=
    Finset.univ.image (fun i : Fin k => (z i).im / w i)
  have hratios : ratios.Nonempty :=
    Finset.univ_nonempty.image (fun i : Fin k => (z i).im / w i)
  let δ : ℝ := ratios.min' hratios
  have hδ : 0 < δ := by
    dsimp [δ]
    rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨i, hi, rfl⟩
    exact div_pos (hz i) (hwpos i)
  have hδle (i : Fin k) : δ ≤ (z i).im / w i := by
    apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hFroots (n : ℕ) :
      (F n).rootSet ℂ ⊆ {s : ℂ | s.im ≤ -δ} := by
    intro s hs
    have hseval : (F n).eval s = 0 :=
      (Polynomial.mem_rootSet.mp hs).2
    by_contra him
    have him' : -δ < s.im := lt_of_not_ge him
    have hcoords : ∀ i : Fin (k + 1),
        0 < (a n i + (b i : ℂ) * s).im := by
      intro i
      by_cases hi : i.val < k
      · have hbound := hδle ⟨i.val, hi⟩
        simp only [a, b, hi, Complex.add_im, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
        have hw := hwpos ⟨i.val, hi⟩
        have hz' := hz ⟨i.val, hi⟩
        have hmul : w ⟨i.val, hi⟩ * δ ≤ (z ⟨i.val, hi⟩).im := by
          simpa [mul_comm] using (le_div_iff₀ hw).mp hbound
        change 0 <
          (z ⟨i.val, hi⟩).im + w ⟨i.val, hi⟩ * s.im
        nlinarith
      · simp [a, b, hi, htpos n]
    apply hDstable n (fun i => a n i + (b i : ℂ) * s) hcoords
    rw [← line_polynomial_evaluation (D n) (a n) b s]
    exact hseval
  have hhalfconvex : Convex ℝ {s : ℂ | s.im ≤ -δ} :=
    convex_halfSpace_le (.mk Complex.add_im Complex.smul_im) (-δ)
  have hnear := polynomial_family_root_near_zero G N c hGdegree
    hGvalue hGderivative hcne hδ
  have hGderivative_ne : ∀ᶠ n in Filter.atTop,
      (G n).derivative.eval 0 ≠ 0 :=
    hGderivative.eventually_ne hcne
  have hevent : ∀ᶠ n in Filter.atTop,
      (∃ s : ℂ, (G n).eval s = 0 ∧ ‖s‖ < δ) ∧
        (G n).derivative.eval 0 ≠ 0 :=
    hnear.and hGderivative_ne
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp hevent
  obtain ⟨hn, hnder⟩ := hn n le_rfl
  obtain ⟨s, hsroot, hsnorm⟩ := hn
  have hGne : G n ≠ 0 := by
    intro hzero
    rw [hzero] at hnder
    simp at hnder
  have hsG : s ∈ (G n).rootSet ℂ :=
    Polynomial.mem_rootSet.mpr ⟨hGne, hsroot⟩
  have hsconv : s ∈ convexHull ℝ ((F n).rootSet ℂ) := by
    simpa [G] using iterate_derivative_roots_in_convex_hull (F n) r hsG
  have hslow : s.im ≤ -δ :=
    convexHull_min (hFroots n) hhalfconvex hsconv
  have habs : δ ≤ |s.im| := by
    rw [abs_of_nonpos (le_trans hslow (neg_nonpos.mpr hδ.le))]
    linarith
  exact (not_lt_of_ge (habs.trans (Complex.abs_im_le_norm s))) hsnorm

@[blueprint "lem:gurvits-slice-derivative"
  (statement := /-- Let $k\in\mathbb N$, let $p$ be a real polynomial in $k+1$ variables, and fix real values for the first $k$ variables.  Regard the resulting expression as a univariate polynomial in the last variable.  Its ordinary derivative is obtained by first taking the last partial derivative of $p$ and then making the same substitution. -/)
  (proof := /-- Apply induction on the multivariate polynomial.  The assertion is immediate for constants and is preserved by addition.  For multiplication by a variable, the ordinary product rule and the defining values of the last partial derivative give the result: a variable among the first $k$ specializes to a constant with derivative zero, whereas the last variable specializes to the univariate indeterminate with derivative one. -/)
  (title := /-- Differentiating a univariate slice -/)
  (latexEnv := "lemma")]
lemma gurvits_slice_derivative {k : ℕ}
    (p : MvPolynomial (Fin (k + 1)) ℝ) (x : Fin k → ℝ) :
    (MvPolynomial.eval₂Hom Polynomial.C
      (fun i => if h : i.val < k then
        Polynomial.C (x ⟨i.val, h⟩) else Polynomial.X) p).derivative =
      MvPolynomial.eval₂Hom Polynomial.C
        (fun i => if h : i.val < k then
          Polynomial.C (x ⟨i.val, h⟩) else Polynomial.X)
        (MvPolynomial.pderiv (Fin.last k) p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      rw [map_add, Polynomial.derivative_add, map_add]
      simpa only [map_add] using congrArg₂ (· + ·) hp hq
  | mul_X p i hp =>
      rw [map_mul, Polynomial.derivative_mul, hp, MvPolynomial.pderiv_mul,
        map_add, map_mul, map_mul]
      by_cases hi : i.val < k
      · have hilast : i ≠ Fin.last k := by
          intro h
          subst i
          simp at hi
        simp [hi, hilast]
      · have hilast : i = Fin.last k := by
          apply Fin.ext
          simp only [Fin.val_last]
          omega
        subst i
        simp

@[blueprint "lem:gurvits-slice-derivative-zero"
  (statement := /-- In the setting of \\cref{lem:gurvits-slice-derivative}, evaluation of the derivative of the univariate slice at zero equals evaluation of the last-variable derivative specialization at the fixed values of the first $k$ variables. -/)
  (proof := /-- Apply \\cref{lem:gurvits-slice-derivative}.  Evaluating the resulting polynomial identity at zero substitutes the fixed real values into the first $k$ variables and zero into the last variable, which is precisely the derivative specialization in \\cref{def:mv-polynomial-derivative-specialization}. -/)
  (title := /-- Derivative specialization as a slice derivative -/)
  (latexEnv := "lemma")]
lemma gurvits_slice_derivative_zero {k : ℕ}
    (p : MvPolynomial (Fin (k + 1)) ℝ) (x : Fin k → ℝ) :
    (MvPolynomial.eval₂Hom Polynomial.C
      (fun i => if h : i.val < k then
        Polynomial.C (x ⟨i.val, h⟩) else Polynomial.X) p).derivative.eval 0 =
      MvPolynomial.eval x (mv_polynomial_derivative_specialization k p) := by
  classical
  rw [gurvits_slice_derivative]
  change (Polynomial.evalRingHom 0)
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun i => if h : i.val < k then
          Polynomial.C (x ⟨i.val, h⟩) else Polynomial.X)
        (MvPolynomial.pderiv (Fin.last k) p)) =
      MvPolynomial.eval₂Hom (RingHom.id ℝ) x
        (mv_polynomial_derivative_specialization k p)
  rw [← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom]
  rw [mv_polynomial_derivative_specialization, MvPolynomial.eval₂Hom_bind₁]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    by_cases hi : i.val < k <;> simp [hi]

@[blueprint "lem:gurvits-homogeneous-eval-scaling"
  (statement := /-- Let $p$ be a homogeneous polynomial of degree $n$.  For every scalar $a$ and every tuple $z$ over a commutative coefficient extension, evaluating $p$ at $(a z_i)_i$ equals $a^n p(z)$. -/)
  (proof := /-- Expand the evaluation as a sum over the monomial support.  In each supported monomial, factor $a$ out of every variable power.  The total exponent of $a$ is the sum of the monomial exponents, which equals $n$ by homogeneity.  Factoring the common term $a^n$ out of the finite sum proves the identity. -/)
  (title := /-- Scaling evaluation of a homogeneous polynomial -/)
  (latexEnv := "lemma")]
lemma gurvits_homogeneous_eval_scaling {ι : Type*} [Fintype ι]
    {n : ℕ} (p : MvPolynomial ι ℝ) (hhomogeneous : p.IsHomogeneous n)
    (a : ℂ) (z : ι → ℂ) :
    MvPolynomial.eval₂ (algebraMap ℝ ℂ) (fun i => a * z i) p =
      a ^ n * MvPolynomial.eval₂ (algebraMap ℝ ℂ) z p := by
  classical
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.prod_congr rfl (fun i _ => mul_pow (a) (z i) (d i)),
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    ← hhomogeneous.degree_eq_sum_deg_support hd]
  ring

@[blueprint "lem:gurvits-slice-complex-evaluation"
  (statement := /-- Fix real values for the first $k$ variables of a real polynomial in $k+1$ variables, obtaining a real univariate polynomial in the last variable.  After complexifying its coefficients, evaluation at $t\in\mathbb C$ equals evaluation of the original multivariate polynomial at the fixed real values and $t$ in the last coordinate. -/)
  (proof := /-- Both sides are ring homomorphisms from the multivariate polynomial ring to $\mathbb C$.  They agree on real constants.  On each of the first $k$ variables both give the prescribed real value, and on the last variable both give $t$.  The universal property of the multivariate polynomial ring therefore gives the identity. -/)
  (title := /-- Complex evaluation of a univariate slice -/)
  (latexEnv := "lemma")]
lemma gurvits_slice_complex_evaluation {k : ℕ}
    (p : MvPolynomial (Fin (k + 1)) ℝ) (x : Fin k → ℝ) (t : ℂ) :
    ((MvPolynomial.eval₂Hom Polynomial.C
      (fun i => if h : i.val < k then
        Polynomial.C (x ⟨i.val, h⟩) else Polynomial.X) p).map
        (algebraMap ℝ ℂ)).eval t =
      MvPolynomial.eval₂ (algebraMap ℝ ℂ)
        (fun i => if h : i.val < k then (x ⟨i.val, h⟩ : ℂ) else t) p := by
  classical
  change (Polynomial.evalRingHom t)
      ((Polynomial.mapRingHom (algebraMap ℝ ℂ))
        (MvPolynomial.eval₂Hom Polynomial.C
          (fun i => if h : i.val < k then
            Polynomial.C (x ⟨i.val, h⟩) else Polynomial.X) p)) = _
  rw [← RingHom.comp_apply, ← RingHom.comp_apply]
  have hhom :
      ((Polynomial.evalRingHom t).comp
        (Polynomial.mapRingHom (algebraMap ℝ ℂ))).comp
          (MvPolynomial.eval₂Hom Polynomial.C
            (fun i : Fin (k + 1) => if h : i.val < k then
              Polynomial.C (x ⟨i.val, h⟩) else Polynomial.X)) =
        MvPolynomial.eval₂Hom (algebraMap ℝ ℂ)
          (fun i : Fin (k + 1) => if h : i.val < k then
            (x ⟨i.val, h⟩ : ℂ) else t) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      by_cases hi : i.val < k <;> simp [hi]
  change _ = (MvPolynomial.eval₂Hom (algebraMap ℝ ℂ)
    (fun i : Fin (k + 1) => if h : i.val < k then
      (x ⟨i.val, h⟩ : ℂ) else t)) p
  exact DFunLike.congr_fun hhom p

@[blueprint "lem:gurvits-slice-splits"
  (statement := /-- Let $p$ be a homogeneous real-stable polynomial in $k+1$ variables, and fix positive real values for its first $k$ variables.  The resulting real univariate polynomial in the last variable splits over $\mathbb R$. -/)
  (proof := /-- Complexify the univariate slice.  By the fundamental theorem of algebra it splits over $\mathbb C$.  We show that every complex root is real.  A root in the upper half-plane would, by \\cref{lem:gurvits-slice-complex-evaluation}, give a zero of $p$ with the first $k$ coordinates positive real.  Multiply all coordinates by a complex scalar with positive but sufficiently small imaginary part.  By \\cref{lem:gurvits-homogeneous-eval-scaling}, this remains a zero, while every coordinate now lies in the open upper half-plane, contradicting real stability.  A root in the lower half-plane has its conjugate in the upper half-plane because the slice has real coefficients.  Thus every complex root lies in the image of $\mathbb R$, and the complex factorization descends to a real factorization. -/)
  (title := /-- Real-rootedness of a positive univariate slice -/)
  (latexEnv := "lemma")]
lemma gurvits_slice_splits {k : ℕ}
    (p : MvPolynomial (Fin (k + 1)) ℝ)
    (hhomogeneous : p.IsHomogeneous (k + 1))
    (hstable : real_stable_mv_polynomial p)
    (x : Fin k → ℝ) (hx : ∀ i, 0 < x i) :
    (MvPolynomial.eval₂Hom Polynomial.C
      (fun i => if h : i.val < k then
        Polynomial.C (x ⟨i.val, h⟩) else Polynomial.X) p).Splits := by
  classical
  let f : Polynomial ℝ := MvPolynomial.eval₂Hom Polynomial.C
    (fun i => if h : i.val < k then
      Polynomial.C (x ⟨i.val, h⟩) else Polynomial.X) p
  change f.Splits
  rcases hstable with hp | hstable
  · subst p
    simp [f]
  refine Polynomial.Splits.of_splits_map_of_injective
    (algebraMap ℝ ℂ).injective (IsAlgClosed.splits _) ?_
  intro r hr
  have hroot : Polynomial.IsRoot (f.map (algebraMap ℝ ℂ)) r :=
    (Polynomial.mem_roots'.mp hr).2
  have no_upper : ∀ s : ℂ,
      Polynomial.IsRoot (f.map (algebraMap ℝ ℂ)) s → 0 < s.im → False := by
    intro s hsroot hsim
    let e : ℝ := s.im / (2 * (|s.re| + 1))
    have hden : 0 < 2 * (|s.re| + 1) := by positivity
    have he : 0 < e := div_pos hsim hden
    let a : ℂ := ⟨1, e⟩
    let w : Fin (k + 1) → ℂ := fun i => if h : i.val < k then
      (x ⟨i.val, h⟩ : ℂ) else s
    have hw : ∀ i, 0 < (a * w i).im := by
      intro i
      by_cases hi : i.val < k
      · rw [show w i = (x ⟨i.val, hi⟩ : ℂ) by simp [w, hi]]
        simp [a, Complex.mul_im, he, hx]
      · have hilast : i = Fin.last k := by
          apply Fin.ext
          simp only [Fin.val_last]
          omega
        subst i
        have heabs : e * |s.re| < s.im / 2 := by
          dsimp [e]
          rw [div_mul_eq_mul_div]
          apply (div_lt_iff₀ hden).2
          nlinarith [abs_nonneg s.re]
        have hre : -|s.re| ≤ s.re := neg_abs_le s.re
        have hmul : -(e * |s.re|) ≤ e * s.re := by
          nlinarith [mul_le_mul_of_nonneg_left hre (le_of_lt he)]
        rw [show w (Fin.last k) = s by simp [w]]
        simp only [Complex.mul_im]
        change 0 < 1 * s.im + e * s.re
        nlinarith
    have hbase : MvPolynomial.eval₂ (algebraMap ℝ ℂ) w p = 0 := by
      rw [← gurvits_slice_complex_evaluation p x s]
      simpa [f] using hsroot
    have hscaled :
        MvPolynomial.eval₂ (algebraMap ℝ ℂ) (fun i => a * w i) p = 0 := by
      rw [gurvits_homogeneous_eval_scaling p hhomogeneous, hbase, mul_zero]
    exact hstable (fun i => a * w i) hw hscaled
  have him : r.im = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hconjroot : Polynomial.IsRoot
          (f.map (algebraMap ℝ ℂ)) (starRingEnd ℂ r) := by
        have hroot_aeval : Polynomial.aeval r f = 0 := by
          change f.eval₂ (algebraMap ℝ ℂ) r = 0
          rw [← Polynomial.eval_map]
          exact hroot
        have hconj := Polynomial.aeval_conj (K := ℂ) f r
        rw [hroot_aeval, map_zero] at hconj
        change (f.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ r) = 0
        rw [Polynomial.eval_map]
        change Polynomial.aeval (starRingEnd ℂ r) f = 0
        exact hconj
      apply no_upper (starRingEnd ℂ r) hconjroot
      simp
      linarith
    · exact no_upper r hroot hpos
  refine ⟨r.re, ?_⟩
  apply Complex.ext
  · simp
  · simpa [him]

@[blueprint "lem:gurvits-slice-real-evaluation"
  (statement := /-- Fix real values for the first $k$ variables of a real polynomial in $k+1$ variables.  Evaluation of the resulting univariate polynomial at $t\in\mathbb R$ equals evaluation of the original polynomial at the fixed values and $t$ in the last coordinate. -/)
  (proof := /-- The two evaluations are ring homomorphisms from the multivariate polynomial ring to $\mathbb R$.  They agree on constants, on each of the first $k$ variables, and on the last variable.  Extensionality for multivariate-polynomial ring homomorphisms proves the identity. -/)
  (title := /-- Real evaluation of a univariate slice -/)
  (latexEnv := "lemma")]
lemma gurvits_slice_real_evaluation {k : ℕ}
    (p : MvPolynomial (Fin (k + 1)) ℝ) (x : Fin k → ℝ) (t : ℝ) :
    (MvPolynomial.eval₂Hom Polynomial.C
      (fun i => if h : i.val < k then
        Polynomial.C (x ⟨i.val, h⟩) else Polynomial.X) p).eval t =
      MvPolynomial.eval
        (fun i => if h : i.val < k then x ⟨i.val, h⟩ else t) p := by
  classical
  change (Polynomial.evalRingHom t)
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun i => if h : i.val < k then
          Polynomial.C (x ⟨i.val, h⟩) else Polynomial.X) p) =
    MvPolynomial.eval₂Hom (RingHom.id ℝ)
      (fun i => if h : i.val < k then x ⟨i.val, h⟩ else t) p
  rw [← RingHom.comp_apply]
  have hhom :
      (Polynomial.evalRingHom t).comp
          (MvPolynomial.eval₂Hom Polynomial.C
            (fun i : Fin (k + 1) => if h : i.val < k then
              Polynomial.C (x ⟨i.val, h⟩) else Polynomial.X)) =
        MvPolynomial.eval₂Hom (RingHom.id ℝ)
          (fun i : Fin (k + 1) => if h : i.val < k then
            x ⟨i.val, h⟩ else t) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      by_cases hi : i.val < k <;> simp [hi]
  exact DFunLike.congr_fun hhom p

@[blueprint "lem:gurvits-slice-roots-nonpositive"
  (statement := /-- Let $p$ be a nonzero real polynomial with nonnegative coefficients, and fix positive real values for its first $k$ variables.  Every real root of the resulting univariate polynomial in the last variable is nonpositive. -/)
  (proof := /-- Suppose that $r>0$ were a root.  By \\cref{lem:gurvits-slice-real-evaluation}, the corresponding evaluation of $p$ would vanish.  All variables in that evaluation are positive.  Every monomial contribution is nonnegative, and because the slice is nonzero, $p$ has a supported monomial whose coefficient and variable product are both strictly positive.  Hence the evaluation is strictly positive, a contradiction. -/)
  (title := /-- Nonpositive roots of a positive slice -/)
  (latexEnv := "lemma")]
lemma gurvits_slice_roots_nonpositive {k : ℕ}
    (p : MvPolynomial (Fin (k + 1)) ℝ)
    (hnonnegative : ∀ m, 0 ≤ p.coeff m)
    (x : Fin k → ℝ) (hx : ∀ i, 0 < x i) :
    ∀ r ∈ (MvPolynomial.eval₂Hom Polynomial.C
      (fun i => if h : i.val < k then
        Polynomial.C (x ⟨i.val, h⟩) else Polynomial.X) p).roots, r ≤ 0 := by
  classical
  intro r hr
  by_contra hnot
  have hrpos : 0 < r := lt_of_not_ge hnot
  let f : Polynomial ℝ := MvPolynomial.eval₂Hom Polynomial.C
    (fun i => if h : i.val < k then
      Polynomial.C (x ⟨i.val, h⟩) else Polynomial.X) p
  have hfne : f ≠ 0 := (Polynomial.mem_roots'.mp hr).1
  have hpne : p ≠ 0 := by
    intro hp
    subst p
    simp [f] at hfne
  let y : Fin (k + 1) → ℝ := fun i => if h : i.val < k then
    x ⟨i.val, h⟩ else r
  have hy : ∀ i, 0 < y i := by
    intro i
    by_cases hi : i.val < k
    · simp [y, hi, hx]
    · simp [y, hi, hrpos]
  have hpeval : 0 < MvPolynomial.eval y p := by
    rw [MvPolynomial.eval_eq]
    apply Finset.sum_pos'
    · intro d hd
      exact mul_nonneg (hnonnegative d)
        (Finset.prod_nonneg fun i _ => pow_nonneg (le_of_lt (hy i)) _)
    · obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hpne
      refine ⟨d, hd, mul_pos ?_ ?_⟩
      · exact lt_of_le_of_ne (hnonnegative d)
          (Ne.symm (MvPolynomial.mem_support_iff.mp hd))
      · exact Finset.prod_pos fun i _ => pow_pos (hy i) _
  have hfroot : f.eval r = 0 := (Polynomial.mem_roots'.mp hr).2
  have heval : f.eval r = MvPolynomial.eval y p := by
    simpa [f, y] using gurvits_slice_real_evaluation p x r
  linarith

@[blueprint "lem:gurvits-polynomial-eval-nonnegative"
  (statement := /-- A real multivariate polynomial with nonnegative coefficients takes nonnegative values whenever all variables are nonnegative. -/)
  (proof := /-- Expand the evaluation as the finite sum over the monomial support.  Each summand is the product of a nonnegative coefficient and nonnegative powers of the variable values, and is therefore nonnegative.  The finite sum is consequently nonnegative. -/)
  (title := /-- Nonnegative evaluation from nonnegative coefficients -/)
  (latexEnv := "lemma")]
lemma gurvits_polynomial_eval_nonnegative {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) (hcoeff : ∀ m, 0 ≤ p.coeff m)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ MvPolynomial.eval x p := by
  rw [MvPolynomial.eval_eq]
  exact Finset.sum_nonneg fun d _ => mul_nonneg (hcoeff d)
    (Finset.prod_nonneg fun i _ => pow_nonneg (hx i) _)

@[blueprint "lem:gurvits-finite-amgm"
  (statement := /-- Let $n\geq1$ and let $z_1,\ldots,z_n$ be nonnegative real numbers.  Then their product is at most the $n$th power of their arithmetic mean. -/)
  (proof := /-- Apply the weighted arithmetic--geometric mean inequality with every weight equal to $1$.  This bounds the $n$th root of the product by the arithmetic mean.  Both sides are nonnegative, so raising the inequality to the $n$th power yields the stated result. -/)
  (title := /-- Finite arithmetic--geometric mean inequality -/)
  (latexEnv := "lemma")]
lemma gurvits_finite_amgm {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) :
    ∏ i, z i ≤ ((∑ i, z i) / (n : ℝ)) ^ n := by
  have hgeom := Real.geom_mean_le_arith_mean (Finset.univ : Finset (Fin n))
    (fun _ => (1 : ℝ)) z (by simp) (by simp [hn]) (by simpa using hz)
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, one_mul,
    Finset.prod_pow, Real.rpow_one, mul_one, pow_one] at hgeom
  have hprod : 0 ≤ ∏ i, z i := Finset.prod_nonneg fun i _ => hz i
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hprod _) hgeom
    (Nat.cast_nonneg n)
  rw [← Real.rpow_mul hprod,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)), Real.rpow_one,
    Real.rpow_natCast] at hpow
  exact hpow

@[blueprint "lem:gurvits-product-amgm-bound"
  (statement := /-- Let $n\geq1$, let $b_1,\ldots,b_n$ be nonnegative, and let $t\geq0$.  Then
  \[
  \prod_{i=1}^n(1+t b_i)\leq
  \left(1+\frac{t}{n}\sum_{i=1}^n b_i\right)^n.
  \] -/)
  (proof := /-- Apply \\cref{lem:gurvits-finite-amgm} to the $n$ nonnegative numbers $1+t b_i$.  Their arithmetic mean is $1+(t/n)\sum_i b_i$, after distributing the finite sum and using $n>0$. -/)
  (title := /-- Product bound from arithmetic--geometric mean -/)
  (latexEnv := "lemma")]
lemma gurvits_product_amgm_bound {n : ℕ} (hn : 0 < n)
    (b : Fin n → ℝ) (hb : ∀ i, 0 ≤ b i) {t : ℝ} (ht : 0 ≤ t) :
    ∏ i, (1 + t * b i) ≤
      (1 + t * (∑ i, b i) / (n : ℝ)) ^ n := by
  calc
    ∏ i, (1 + t * b i) ≤
        ((∑ i, (1 + t * b i)) / (n : ℝ)) ^ n :=
      gurvits_finite_amgm hn _
        (fun i => add_nonneg zero_le_one (mul_nonneg ht (hb i)))
    _ = (1 + t * (∑ i, b i) / (n : ℝ)) ^ n := by
      congr 1
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin,
        nsmul_eq_mul, Finset.mul_sum]
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)]

@[blueprint "lem:gurvits-list-product-bound"
  (statement := /-- Let $n\geq1$, let $a_1,\ldots,a_m$ be positive real numbers with $m\leq n$, and let $t\geq0$.  Then
  \[
  \prod_{j=1}^m\left(1+\frac{t}{a_j}\right)
  \leq
  \left(1+\frac{t}{n}\sum_{j=1}^m\frac1{a_j}\right)^n.
  \] -/)
  (proof := /-- Append $n-m$ zeros to the list $(a_j^{-1})_{j=1}^m$.  Apply \\cref{lem:gurvits-product-amgm-bound} to the resulting list of length $n$.  The appended entries contribute factors $1$ to the product and $0$ to the sum, leaving exactly the displayed inequality. -/)
  (title := /-- Padded product bound -/)
  (latexEnv := "lemma")]
lemma gurvits_list_product_bound {n : ℕ} (hn : 0 < n)
    (a : List ℝ) (hlen : a.length ≤ n)
    (ha : ∀ r ∈ a, 0 < r) {t : ℝ} (ht : 0 ≤ t) :
    (a.map fun r => 1 + t * r⁻¹).prod ≤
      (1 + t * (a.map (·⁻¹)).sum / (n : ℝ)) ^ n := by
  let b : List ℝ := a.map (·⁻¹) ++ List.replicate (n - a.length) 0
  have hblen : b.length = n := by
    simp [b]
    omega
  have hb : ∀ i : Fin b.length, 0 ≤ b[i.val] := by
    intro i
    have hi : b[i.val] ∈ b := List.getElem_mem i.isLt
    rcases List.mem_append.mp hi with hi | hi
    · obtain ⟨r, hr, her⟩ := List.mem_map.mp hi
      rw [← her]
      exact inv_nonneg.mpr (le_of_lt (ha r hr))
    · have hi' := List.mem_replicate.mp hi
      rw [hi'.2]
  have h := gurvits_product_amgm_bound (n := b.length)
    (by simpa [hblen] using hn) (fun i : Fin b.length => b[i.val]) hb ht
  have hprod : (∏ i : Fin b.length, (1 + t * b[i.val])) =
      (b.map fun r => 1 + t * r).prod := by
    exact Fin.prod_univ_fun_getElem b (fun r => 1 + t * r)
  have hsum : (∑ i : Fin b.length, b[i.val]) = b.sum :=
    Fin.sum_univ_getElem b
  rw [hprod, hsum] at h
  simp [b, hblen, List.prod_append, List.sum_append] at h
  simpa only [show ((fun r => 1 + t * r) ∘ fun x : ℝ => x⁻¹) =
    (fun r => 1 + t * r⁻¹) by rfl] using h

@[blueprint "lem:gurvits-slice-nat-degree-le"
  (statement := /-- If a real multivariate polynomial is homogeneous of degree $n$, then every univariate slice obtained by fixing all variables except one has degree at most $n$. -/)
  (proof := /-- Induct through the homogeneous polynomial as a sum of homogeneous monomials.  A sum cannot have degree larger than the maximum degree of its summands.  For a monomial, specializing the fixed variables to constants leaves a scalar multiple of a power of the remaining variable, whose exponent is at most the sum of all exponents, namely $n$. -/)
  (title := /-- Degree bound for a univariate slice -/)
  (latexEnv := "lemma")]
lemma gurvits_slice_nat_degree_le {k : ℕ}
    (p : MvPolynomial (Fin (k + 1)) ℝ)
    (hhomogeneous : p.IsHomogeneous (k + 1)) (x : Fin k → ℝ) :
    (MvPolynomial.eval₂Hom Polynomial.C
      (fun i => if h : i.val < k then
        Polynomial.C (x ⟨i.val, h⟩) else Polynomial.X) p).natDegree ≤ k + 1 := by
  classical
  induction hhomogeneous using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
      simp
  | add p q hp hq ihp ihq =>
      rw [map_add]
      exact le_trans (Polynomial.natDegree_add_le _ _) (max_le ihp ihq)
  | monomial d r hr =>
      change (MvPolynomial.eval₂ Polynomial.C
        (fun i => if h : i.val < k then
          Polynomial.C (x ⟨i.val, h⟩) else Polynomial.X)
        (MvPolynomial.monomial d r)).natDegree ≤ k + 1
      rw [MvPolynomial.eval₂_monomial]
      have hprod :
          (d.prod fun i e => (if h : i.val < k then
            Polynomial.C (x ⟨i.val, h⟩) else Polynomial.X) ^ e).natDegree ≤
            ∑ i ∈ d.support, d i := by
        change (∏ i ∈ d.support, (if h : i.val < k then
          Polynomial.C (x ⟨i.val, h⟩) else Polynomial.X) ^ d i).natDegree ≤ _
        refine le_trans (Polynomial.natDegree_prod_le d.support
          (fun i => (if h : i.val < k then
            Polynomial.C (x ⟨i.val, h⟩) else Polynomial.X) ^ d i)) ?_
        apply Finset.sum_le_sum
        intro i hi
        by_cases hik : i.val < k
        · simp [hik]
        · simp [hik]
      calc
        (Polynomial.C r *
            d.prod fun i e => (if h : i.val < k then
              Polynomial.C (x ⟨i.val, h⟩) else Polynomial.X) ^ e).natDegree ≤
            (Polynomial.C r).natDegree +
              (d.prod fun i e => (if h : i.val < k then
                Polynomial.C (x ⟨i.val, h⟩) else Polynomial.X) ^ e).natDegree :=
          Polynomial.natDegree_mul_le
        _ ≤ ∑ i ∈ d.support, d i := by simpa using hprod
        _ = k + 1 := by
          simpa only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one,
            Finsupp.sum] using hr

@[blueprint "lem:gurvits-univariate-capacity-bound"
  (statement := /-- Let $k\in\mathbb N$, and let $f$ be a real polynomial of degree at most $k+1$ which splits over the reals, has only nonpositive roots, and is nonnegative on the nonnegative real axis.  Then
  \[
  \left(\frac{k}{k+1}\right)^k
  \inf_{t>0}\frac{f(t)}t\leq f'(0).
  \] -/)
  (proof := /-- The displayed infimum is nonnegative and bounded below.  For $k=0$, the degree bound writes $f(t)=f_1t+f_0$; hence $f(t)/t\to f_1=f'(0)$ as $t\to\infty$.  Now assume $k\geq1$.  If $f(0)=0$, the difference quotients $f(t)/t$ converge to $f'(0)$ as $t\downarrow0$, giving the assertion because the prefactor lies in $[0,1]$.  Suppose $f(0)>0$.  Write the roots as $-a_1,\ldots,-a_m$, where every $a_j>0$ and $m\leq k+1$.  If $m=0$, then $f$ is constant and $f(t)/t\to0$ as $t\to\infty$.  Otherwise put $S=\sum_j a_j^{-1}$ and choose $t=(k+1)/(kS)$.  The factorization and logarithmic derivative identities give
  \[
  f(t)=f(0)\prod_j(1+t/a_j),\qquad f'(0)=f(0)S.
  \]
  Applying \cref{lem:gurvits-list-product-bound} to the root list, padded to length $k+1$, bounds the product by $(1+tS/(k+1))^{k+1}$.  Substitution of the chosen $t$ and cancellation yields the result. -/)
  (title := /-- Univariate derivative--capacity inequality -/)
  (latexEnv := "lemma")]
lemma gurvits_univariate_capacity_bound {k : ℕ}
    (f : Polynomial ℝ) (hsplits : f.Splits)
    (hroots : ∀ r ∈ f.roots, r ≤ 0)
    (hdegree : f.natDegree ≤ k + 1)
    (heval : ∀ t : ℝ, 0 ≤ t → 0 ≤ f.eval t) :
    ((k : ℝ) / ((k : ℝ) + 1)) ^ k *
        sInf {r : ℝ | ∃ t : ℝ, 0 < t ∧ r = f.eval t / t} ≤
      f.derivative.eval 0 := by
  classical
  let S : Set ℝ := {r : ℝ | ∃ t : ℝ, 0 < t ∧ r = f.eval t / t}
  change ((k : ℝ) / ((k : ℝ) + 1)) ^ k * sInf S ≤
    f.derivative.eval 0
  have hSnonempty : S.Nonempty := by
    refine ⟨f.eval 1, 1, by norm_num, ?_⟩
    norm_num
  have hSbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with ⟨t, ht, rfl⟩
    exact div_nonneg (heval t (le_of_lt ht)) (le_of_lt ht)
  have hSnonneg : 0 ≤ sInf S := by
    apply le_csInf hSnonempty
    intro r hr
    rcases hr with ⟨t, ht, rfl⟩
    exact div_nonneg (heval t (le_of_lt ht)) (le_of_lt ht)
  by_cases hkzero : k = 0
  · subst k
    have hflinear :
        f = Polynomial.C (f.coeff 1) * Polynomial.X +
          Polynomial.C (f.coeff 0) :=
      Polynomial.eq_X_add_C_of_natDegree_le_one (by simpa using hdegree)
    have hlim :
        Filter.Tendsto (fun t : ℝ => f.eval t / t) Filter.atTop
          (nhds (f.derivative.eval 0)) := by
      have hbase :
          Filter.Tendsto
              (fun t : ℝ => f.coeff 1 + f.coeff 0 / t)
              Filter.atTop (nhds (f.coeff 1)) :=
        by
          simpa using
            ((tendsto_const_nhds :
              Filter.Tendsto (fun _ : ℝ => f.coeff 1) Filter.atTop
                (nhds (f.coeff 1))).add
              (Filter.Tendsto.const_div_atTop Filter.tendsto_id (f.coeff 0)))
      have heq : (fun t : ℝ => f.eval t / t) =ᶠ[Filter.atTop]
          (fun t : ℝ => f.coeff 1 + f.coeff 0 / t) := by
        filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
        have heval_linear :
            f.eval t = f.coeff 1 * t + f.coeff 0 := by
          conv_lhs => rw [hflinear]
          simp
        rw [heval_linear]
        field_simp [ne_of_gt ht]
        <;> ring
      have hderiv :
          f.derivative.eval 0 = f.coeff 1 := by
        conv_lhs => rw [hflinear]
        simp
      rw [hderiv]
      exact hbase.congr' heq.symm
    have hInf_le : sInf S ≤ f.derivative.eval 0 := by
      apply tendsto_le_of_eventuallyLE tendsto_const_nhds hlim
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
      exact csInf_le hSbdd ⟨t, ht, rfl⟩
    simpa using hInf_le
  have hk : 0 < k := Nat.pos_of_ne_zero hkzero
  have hbase_nonneg : 0 ≤ (k : ℝ) / ((k : ℝ) + 1) := by positivity
  have hbase_le_one : (k : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
    apply (div_le_one₀ (by positivity)).2
    norm_num
  have hfactor_nonneg :
      0 ≤ ((k : ℝ) / ((k : ℝ) + 1)) ^ k := pow_nonneg hbase_nonneg _
  have hfactor_le_one :
      ((k : ℝ) / ((k : ℝ) + 1)) ^ k ≤ 1 :=
    pow_le_one₀ hbase_nonneg hbase_le_one
  by_cases hfzero : f = 0
  · subst f
    have hSeq : S = {0} := by
      ext r
      constructor
      · rintro ⟨t, ht, hrt⟩
        simpa using hrt
      · intro hr
        have hrzero : r = 0 := by simpa using hr
        subst r
        exact ⟨1, by norm_num, by norm_num⟩
    rw [hSeq, csInf_singleton, mul_zero]
    simp
  by_cases hf0 : f.eval 0 = 0
  · have hslope :
        Filter.Tendsto (fun t : ℝ => f.eval t / t)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (f.derivative.eval 0)) := by
      simpa [hf0, div_eq_mul_inv, mul_comm] using
        (f.hasDerivAt 0).tendsto_slope_zero_right
    have hInf_le : sInf S ≤ f.derivative.eval 0 := by
      apply tendsto_le_of_eventuallyLE tendsto_const_nhds hslope
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact csInf_le hSbdd ⟨t, ht, rfl⟩
    calc
      ((k : ℝ) / ((k : ℝ) + 1)) ^ k * sInf S ≤ sInf S := by
        nlinarith
      _ ≤ f.derivative.eval 0 := hInf_le
  · have hf0pos : 0 < f.eval 0 :=
      lt_of_le_of_ne (heval 0 le_rfl) (Ne.symm hf0)
    let a : List ℝ := Quot.out (f.roots.map fun r => -r)
    have haout : (↑a : Multiset ℝ) = f.roots.map fun r => -r :=
      Quot.out_eq _
    have ha : ∀ u ∈ a, 0 < u := by
      intro u hu
      have hu' : u ∈ (↑a : Multiset ℝ) := hu
      rw [haout] at hu'
      obtain ⟨r, hr, hru⟩ := Multiset.mem_map.mp hu'
      rw [← hru]
      have hrne : r ≠ 0 := by
        intro hre
        subst r
        exact hf0 (Polynomial.mem_roots'.mp hr).2
      exact neg_pos.mpr (lt_of_le_of_ne (hroots r hr) hrne)
    have halen : a.length = f.roots.card := by
      have h := congrArg Multiset.card haout
      simpa using h
    have hlen : a.length ≤ k + 1 := by
      rw [halen, ← hsplits.natDegree_eq_card_roots]
      exact hdegree
    by_cases haempty : a = []
    · have hnatdegree : f.natDegree = 0 := by
        rw [hsplits.natDegree_eq_card_roots, ← halen, haempty]
        simp
      have hfconst : f = Polynomial.C (f.coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero hnatdegree
      have hlim :
          Filter.Tendsto (fun t : ℝ => f.eval t / t) Filter.atTop (nhds 0) := by
        rw [hfconst]
        simpa using
          (Filter.Tendsto.const_div_atTop Filter.tendsto_id (f.coeff 0))
      have hInf_le : sInf S ≤ 0 := by
        apply tendsto_le_of_eventuallyLE tendsto_const_nhds hlim
        filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
        exact csInf_le hSbdd ⟨t, ht, rfl⟩
      have hInfeq : sInf S = 0 := le_antisymm hInf_le hSnonneg
      have hderivzero : f.derivative.eval 0 = 0 := by
        rw [hfconst]
        simp
      rw [hInfeq, mul_zero, hderivzero]
    · have hsumpos : 0 < (a.map (·⁻¹)).sum := by
        apply List.sum_pos
        · intro u hu
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hu
          exact inv_pos.mpr (ha r hr)
        · intro h
          apply haempty
          have hlenmap := congrArg List.length h
          exact List.eq_nil_iff_length_eq_zero.mpr (by simpa using hlenmap)
      have hsum :
          (f.roots.map fun r => 1 / (0 - r)).sum =
            (a.map (·⁻¹)).sum := by
        change (f.roots.map fun r => 1 / (0 - r)).sum =
          (Multiset.map (·⁻¹) (↑a : Multiset ℝ)).sum
        rw [haout, Multiset.map_map]
        simp [one_div]
      have hderiv :
          f.derivative.eval 0 = f.eval 0 * (a.map (·⁻¹)).sum := by
        rw [hsplits.eval_derivative_eq_eval_mul_sum hf0]
        rw [hsum]
      have hfactorization : ∀ t : ℝ,
          f.eval t =
            f.eval 0 * (a.map fun u => 1 + t * u⁻¹).prod := by
        intro t
        have hrootprod :
            (f.roots.map (t - ·)).prod =
              (f.roots.map fun r => -r).prod *
                (f.roots.map fun r => 1 + t * (-r)⁻¹).prod := by
          calc
            (f.roots.map (t - ·)).prod =
                (f.roots.map fun r => (-r) * (1 + t * (-r)⁻¹)).prod := by
              apply congrArg Multiset.prod
              apply Multiset.map_congr rfl
              intro r hr
              have hrne : r ≠ 0 := by
                intro hre
                subst r
                exact hf0 (Polynomial.mem_roots'.mp hr).2
              field_simp
              ring
            _ = (f.roots.map fun r => -r).prod *
                (f.roots.map fun r => 1 + t * (-r)⁻¹).prod :=
              Multiset.prod_map_mul
        have hlistprod :
            (a.map fun u => 1 + t * u⁻¹).prod =
              (f.roots.map fun r => 1 + t * (-r)⁻¹).prod := by
          change (Multiset.map (fun u => 1 + t * u⁻¹)
            (↑a : Multiset ℝ)).prod = _
          rw [haout, Multiset.map_map]
          rfl
        rw [hsplits.eval_eq_prod_roots, hsplits.eval_eq_prod_roots, hrootprod,
          hlistprod]
        ring_nf
      let T : ℝ :=
        ((k : ℝ) + 1) / ((k : ℝ) * (a.map (·⁻¹)).sum)
      have hTpos : 0 < T := by
        dsimp [T]
        positivity
      have hprod_bound :=
        gurvits_list_product_bound (n := k + 1) (by omega) a hlen ha
          (le_of_lt hTpos)
      have hinside :
          1 + T * (a.map (·⁻¹)).sum / ((k + 1 : ℕ) : ℝ) =
            ((k : ℝ) + 1) / (k : ℝ) := by
        dsimp [T]
        push_cast
        field_simp [ne_of_gt hsumpos, Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)]
        <;> ring
      rw [hinside] at hprod_bound
      have halgebra :
          ((k : ℝ) / ((k : ℝ) + 1)) ^ k *
              (f.eval 0 * (((k : ℝ) + 1) / (k : ℝ)) ^ (k + 1)) / T =
            f.eval 0 * (a.map (·⁻¹)).sum := by
        dsimp [T]
        rw [div_pow, div_pow, pow_succ]
        field_simp [ne_of_gt hsumpos, Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)]
        <;> ring
      calc
        ((k : ℝ) / ((k : ℝ) + 1)) ^ k * sInf S ≤
            ((k : ℝ) / ((k : ℝ) + 1)) ^ k * (f.eval T / T) :=
          mul_le_mul_of_nonneg_left
            (csInf_le hSbdd ⟨T, hTpos, rfl⟩) hfactor_nonneg
        _ = ((k : ℝ) / ((k : ℝ) + 1)) ^ k *
              (f.eval 0 * (a.map fun u => 1 + T * u⁻¹).prod) / T := by
          rw [hfactorization]
          ring
        _ ≤ ((k : ℝ) / ((k : ℝ) + 1)) ^ k *
              (f.eval 0 * (((k : ℝ) + 1) / (k : ℝ)) ^ (k + 1)) / T := by
          apply (div_le_div_iff_of_pos_right hTpos).2
          gcongr
        _ = f.eval 0 * (a.map (·⁻¹)).sum := halgebra
        _ = f.derivative.eval 0 := hderiv.symm

@[blueprint "lem:gurvits-derivative-capacity-bound"
  (statement := /-- Let $k\in\mathbb N$, and let $p$ be a real polynomial in $k+1$ variables that is homogeneous of degree $k+1$, has nonnegative coefficients, and is real stable.  Let $q$ be the polynomial in the first $k$ variables obtained by differentiating $p$ with respect to the last variable and then setting that variable equal to zero.  Then
  \[
  \operatorname{Cap}(q)\geq
  \left(\frac{k}{k+1}\right)^k\operatorname{Cap}(p).
  \] -/)
  (proof := /-- Fix a positive vector $x$ in the first $k$ variables, put $D=\prod_i x_i$, and let $f(t)=p(x_1,\ldots,x_k,t)$.  The slice splits over $\mathbb R$ by \cref{lem:gurvits-slice-splits}, all its roots are nonpositive by \cref{lem:gurvits-slice-roots-nonpositive}, and its degree is at most $k+1$ by \cref{lem:gurvits-slice-nat-degree-le}.  Moreover, \cref{lem:gurvits-slice-real-evaluation} and \cref{lem:gurvits-polynomial-eval-nonnegative} show that $f(t)\geq0$ for $t\geq0$.  Hence \cref{lem:gurvits-univariate-capacity-bound} gives
  \[
  \left(\frac{k}{k+1}\right)^k\inf_{t>0}\frac{f(t)}t
  \leq f'(0).
  \]
  For every $t>0$, the point $(x,t)$ is admissible in \cref{def:mv-polynomial-capacity}; therefore
  \[
  D\,\operatorname{Cap}(p)\leq\inf_{t>0}\frac{f(t)}t.
  \]
  Multiplying this inequality by the nonnegative prefactor and combining it with the univariate bound yields
  \[
  \left(\frac{k}{k+1}\right)^k\operatorname{Cap}(p)
  \leq\frac{f'(0)}D.
  \]
  By \cref{lem:gurvits-slice-derivative-zero}, the numerator is the value at $x$ of the derivative specialization from \cref{def:mv-polynomial-derivative-specialization}.  The displayed bound holds for every positive $x$; taking their infimum according to \cref{def:mv-polynomial-capacity} proves the claim. -/)
  (title := /-- Quantitative derivative-capacity bound -/)
  (latexEnv := "lemma")]
lemma gurvits_derivative_capacity_bound {k : ℕ}
    (p : MvPolynomial (Fin (k + 1)) ℝ)
    (hhomogeneous : p.IsHomogeneous (k + 1))
    (hnonnegative : ∀ m, 0 ≤ p.coeff m)
    (hstable : real_stable_mv_polynomial p) :
    ((k : ℝ) / ((k : ℝ) + 1)) ^ k * mv_polynomial_capacity p ≤
      mv_polynomial_capacity
        (mv_polynomial_derivative_specialization k p) := by
  classical
  let q : MvPolynomial (Fin k) ℝ :=
    mv_polynomial_derivative_specialization k p
  let Q : Set ℝ := {r : ℝ | ∃ x : Fin k → ℝ, (∀ i, 0 < x i) ∧
    r = MvPolynomial.eval x q / ∏ i, x i}
  change ((k : ℝ) / ((k : ℝ) + 1)) ^ k *
      mv_polynomial_capacity p ≤ sInf Q
  apply le_csInf
  · refine ⟨MvPolynomial.eval (fun _ => 1) q, ?_⟩
    refine ⟨fun _ => 1, by simp, ?_⟩
    simp
  · intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    let f : Polynomial ℝ := MvPolynomial.eval₂Hom Polynomial.C
      (fun i => if h : i.val < k then
        Polynomial.C (x ⟨i.val, h⟩) else Polynomial.X) p
    let D : ℝ := ∏ i, x i
    have hDpos : 0 < D := Finset.prod_pos fun i _ => hx i
    have hpbdd : BddBelow {r : ℝ | ∃ y : Fin (k + 1) → ℝ,
        (∀ i, 0 < y i) ∧
        r = MvPolynomial.eval y p / ∏ i, y i} := by
      refine ⟨0, ?_⟩
      intro s hs
      rcases hs with ⟨y, hy, rfl⟩
      exact div_nonneg
        (gurvits_polynomial_eval_nonnegative p hnonnegative y
          (fun i => le_of_lt (hy i)))
        (Finset.prod_nonneg fun i _ => le_of_lt (hy i))
    have hfsplits : f.Splits := by
      simpa [f] using
        gurvits_slice_splits p hhomogeneous hstable x hx
    have hfroots : ∀ s ∈ f.roots, s ≤ 0 := by
      simpa [f] using
        gurvits_slice_roots_nonpositive p hnonnegative x hx
    have hfdegree : f.natDegree ≤ k + 1 := by
      simpa [f] using
        gurvits_slice_nat_degree_le p hhomogeneous x
    have hfeval : ∀ t : ℝ, 0 ≤ t → 0 ≤ f.eval t := by
      intro t ht
      rw [show f.eval t = MvPolynomial.eval
        (fun i => if h : i.val < k then x ⟨i.val, h⟩ else t) p by
          simpa [f] using gurvits_slice_real_evaluation p x t]
      apply gurvits_polynomial_eval_nonnegative p hnonnegative
      intro i
      by_cases hi : i.val < k
      · simp [hi, le_of_lt (hx ⟨i.val, hi⟩)]
      · simp [hi, ht]
    let U : Set ℝ :=
      {s : ℝ | ∃ t : ℝ, 0 < t ∧ s = f.eval t / t}
    have hUnonempty : U.Nonempty := by
      exact ⟨f.eval 1, 1, by norm_num, by norm_num⟩
    have hcapacity_slice :
        D * mv_polynomial_capacity p ≤ sInf U := by
      apply le_csInf hUnonempty
      intro s hs
      rcases hs with ⟨t, ht, rfl⟩
      let y : Fin (k + 1) → ℝ := fun i =>
        if h : i.val < k then x ⟨i.val, h⟩ else t
      have hy : ∀ i, 0 < y i := by
        intro i
        by_cases hi : i.val < k
        · simp [y, hi, hx]
        · simp [y, hi, ht]
      have hyprod : (∏ i, y i) = D * t := by
        rw [Fin.prod_univ_castSucc]
        simp [y, D]
      have hyeval : MvPolynomial.eval y p = f.eval t := by
        simpa [f, y] using (gurvits_slice_real_evaluation p x t).symm
      have hcap :
          mv_polynomial_capacity p ≤ f.eval t / (D * t) := by
        apply csInf_le hpbdd
        exact ⟨y, hy, by rw [hyeval, hyprod]⟩
      apply (le_div_iff₀ ht).2
      calc
        D * mv_polynomial_capacity p * t =
            mv_polynomial_capacity p * (D * t) := by ring
        _ ≤ f.eval t := (le_div_iff₀ (mul_pos hDpos ht)).1 hcap
    have hunivariate :
        ((k : ℝ) / ((k : ℝ) + 1)) ^ k * sInf U ≤
          f.derivative.eval 0 := by
      simpa [U] using
        gurvits_univariate_capacity_bound f hfsplits hfroots hfdegree hfeval
    have hfactor_nonneg :
        0 ≤ ((k : ℝ) / ((k : ℝ) + 1)) ^ k := by positivity
    change ((k : ℝ) / ((k : ℝ) + 1)) ^ k *
        mv_polynomial_capacity p ≤ MvPolynomial.eval x q / D
    apply (le_div_iff₀ hDpos).2
    calc
      ((k : ℝ) / ((k : ℝ) + 1)) ^ k *
            mv_polynomial_capacity p * D =
          ((k : ℝ) / ((k : ℝ) + 1)) ^ k *
            (D * mv_polynomial_capacity p) := by ring
      _ ≤ ((k : ℝ) / ((k : ℝ) + 1)) ^ k * sInf U :=
        mul_le_mul_of_nonneg_left hcapacity_slice hfactor_nonneg
      _ ≤ f.derivative.eval 0 := hunivariate
      _ = MvPolynomial.eval x q := by
        simpa [f, q] using gurvits_slice_derivative_zero p x

@[blueprint "lem:gurvits-derivative-capacity"
  (statement := /-- Let $k\in\mathbb N$, and let $p$ be a homogeneous real-stable polynomial of degree $k+1$ in $k+1$ variables with nonnegative coefficients.  If $q$ is obtained from $p$ by differentiating in the last variable and then setting that variable equal to zero, then $q$ is homogeneous of degree $k$, has nonnegative coefficients, is real stable, and satisfies
  \[
  \operatorname{Cap}(q)\geq
  \left(\frac{k}{k+1}\right)^k\operatorname{Cap}(p).
  \] -/)
  (proof := /-- Apply \cref{lem:derivative-specialization-structure} to obtain homogeneity of degree $k$ and coefficient nonnegativity.  Apply \cref{lem:real-stable-derivative-specialization} to obtain real stability, including the case of a zero specialization.  Finally, \cref{lem:gurvits-derivative-capacity-bound} supplies the stated capacity inequality.  These four conclusions are exactly the asserted conjunction. -/)
  (title := /-- Gurvits derivative-capacity inequality -/)
  (latexEnv := "lemma")]
lemma gurvits_derivative_capacity {k : ℕ}
    (p : MvPolynomial (Fin (k + 1)) ℝ)
    (hhomogeneous : p.IsHomogeneous (k + 1))
    (hnonnegative : ∀ m, 0 ≤ p.coeff m)
    (hstable : real_stable_mv_polynomial p) :
    (mv_polynomial_derivative_specialization k p).IsHomogeneous k ∧
      (∀ m, 0 ≤ (mv_polynomial_derivative_specialization k p).coeff m) ∧
      real_stable_mv_polynomial
        (mv_polynomial_derivative_specialization k p) ∧
      ((k : ℝ) / ((k : ℝ) + 1)) ^ k * mv_polynomial_capacity p ≤
        mv_polynomial_capacity
          (mv_polynomial_derivative_specialization k p) := by
  have hstructure :=
    derivative_specialization_structure p hhomogeneous hnonnegative
  constructor
  · exact hstructure.1
  constructor
  · exact hstructure.2
  constructor
  · exact real_stable_derivative_specialization p hstable
  · exact gurvits_derivative_capacity_bound p hhomogeneous hnonnegative hstable

@[blueprint "thm:gurvits-coefficient-capacity"
  (statement := /-- Let $n\in\mathbb N$, and let $p\in\mathbb R[x_i:i\in\operatorname{Fin}(n)]$ be homogeneous of degree $n$, have nonnegative coefficients, and be real stable.  Then its squarefree coefficient satisfies
  \[
  [x_1\cdots x_n]p\geq
  \frac{n!}{n^n}\operatorname{Cap}(p).
  \] -/)
  (proof := /-- Proceed by induction on $n$.  If $n=0$, the positive tuple in the infimum defining \cref{def:mv-polynomial-capacity} is unique and its coordinate product is $1$.  Evaluation at this empty tuple is the constant coefficient, so the claimed inequality is an equality.

  Suppose that $n=k+1$, and let $q$ be the last-variable derivative specialization of $p$ from \cref{def:mv-polynomial-derivative-specialization}.  By \cref{lem:gurvits-derivative-capacity}, the polynomial $q$ is homogeneous of degree $k$, has nonnegative coefficients, is real stable, and satisfies
  \[
  \left(\frac{k}{k+1}\right)^k\operatorname{Cap}(p)
  \leq \operatorname{Cap}(q).
  \]
  The induction hypothesis therefore gives
  \[
  \frac{k!}{k^k}\operatorname{Cap}(q)
  \leq [x_1\cdots x_k]q.
  \]
  Under the inclusion of the first $k$ variables into the first $k+1$ variables, specialization at zero kills the complementary last variable.  The coefficient formula for a partial derivative consequently gives
  \[
  [x_1\cdots x_k]q=[x_1\cdots x_kx_{k+1}]p:
  \]
  the embedded all-ones exponent has last coordinate zero, adding the last-variable singleton produces the all-ones exponent in $k+1$ variables, and the derivative multiplicity is therefore $0+1=1$.

  Finally, including the case $k=0$, direct factorial and power arithmetic yields
  \[
  \frac{(k+1)!}{(k+1)^{k+1}}
  =\frac{k!}{k^k}\left(\frac{k}{k+1}\right)^k.
  \]
  Since $k!/k^k$ is nonnegative, multiplication of the derivative-capacity inequality by this factor, followed by the induction hypothesis and the coefficient identity above, proves the result. -/)
  (title := /-- Gurvits squarefree coefficient bound -/)
  (latexEnv := "theorem")]
theorem gurvits_coefficient_capacity {n : ℕ}
    (p : MvPolynomial (Fin n) ℝ)
    (hhomogeneous : p.IsHomogeneous n)
    (hnonnegative : ∀ m, 0 ≤ p.coeff m)
    (hstable : real_stable_mv_polynomial p) :
    (Nat.factorial n : ℝ) / (n : ℝ) ^ n * mv_polynomial_capacity p ≤
      p.coeff (∑ i : Fin n, Finsupp.single i 1) := by
  classical
  induction n with
  | zero =>
      simp [mv_polynomial_capacity]
      rw [show (![] : Fin 0 → ℝ) = 0 by
        ext i
        exact Fin.elim0 i, MvPolynomial.eval_zero]
      rfl
  | succ k ih =>
      let q := mv_polynomial_derivative_specialization k p
      have hd :=
        gurvits_derivative_capacity p hhomogeneous hnonnegative hstable
      have hspecialization :
          q = (MvPolynomial.pderiv (Fin.last k) p).killCompl
            (Fin.castSucc_injective k) := by
        unfold q mv_polynomial_derivative_specialization
        change MvPolynomial.aeval _ _ = MvPolynomial.aeval _ _
        congr 1
        apply MvPolynomial.algHom_ext
        intro i
        simp only [MvPolynomial.aeval_X]
        have hrange :
            i ∈ Set.range (Fin.castSucc : Fin k → Fin (k + 1)) ↔
              i.val < k := by
          constructor
          · rintro ⟨j, rfl⟩
            exact j.isLt
          · intro hi
            exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
        by_cases hi : i.val < k
        · rw [dif_pos hi, dif_pos (hrange.mpr hi)]
          congr 1
          apply Fin.ext
          simp
        · rw [dif_neg hi, dif_neg (not_congr hrange |>.mpr hi)]
      have hcoeff :
          q.coeff (∑ i : Fin k, Finsupp.single i 1) =
            p.coeff (∑ i : Fin (k + 1), Finsupp.single i 1) := by
        rw [hspecialization, MvPolynomial.coeff_killCompl,
          MvPolynomial.coeff_pderiv]
        have hexponent :
            (∑ i : Fin k, Finsupp.single i 1).mapDomain Fin.castSucc +
                Finsupp.single (Fin.last k) 1 =
              ∑ i : Fin (k + 1), Finsupp.single i 1 := by
          change (Finsupp.mapDomain.addMonoidHom Fin.castSucc)
              (∑ i : Fin k, Finsupp.single i 1) +
                Finsupp.single (Fin.last k) 1 = _
          rw [map_sum]
          change (∑ i : Fin k,
              (Finsupp.single i 1).mapDomain Fin.castSucc) + _ = _
          simp_rw [Finsupp.mapDomain_single]
          rw [Fin.sum_univ_castSucc]
        have hlast :
            (∑ i : Fin k, Finsupp.single i 1).mapDomain Fin.castSucc
                (Fin.last k) = 0 := by
          change ((Finsupp.mapDomain.addMonoidHom Fin.castSucc)
            (∑ i : Fin k, Finsupp.single i 1)) (Fin.last k) = 0
          rw [map_sum]
          simp [Finsupp.mapDomain_single, Fin.castSucc_ne_last]
        rw [hexponent, hlast]
        norm_num
      have hscale :
          (Nat.factorial (k + 1) : ℝ) / (k + 1 : ℝ) ^ (k + 1) =
            (Nat.factorial k : ℝ) / (k : ℝ) ^ k *
              ((k : ℝ) / ((k : ℝ) + 1)) ^ k := by
        by_cases hk : k = 0
        · subst k
          norm_num
        · rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
            Nat.cast_one]
          have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
          have hk1R : (k : ℝ) + 1 ≠ 0 := by positivity
          rw [div_pow]
          field_simp
          ring
      have hi :
          (Nat.factorial k : ℝ) / (k : ℝ) ^ k *
              mv_polynomial_capacity q ≤
            q.coeff (∑ i : Fin k, Finsupp.single i 1) := by
        exact ih q (by simpa [q] using hd.1)
          (by simpa [q] using hd.2.1)
          (by simpa [q] using hd.2.2.1)
      calc
        (Nat.factorial (k + 1) : ℝ) / ((k + 1 : ℕ) : ℝ) ^ (k + 1) *
              mv_polynomial_capacity p =
            (Nat.factorial k : ℝ) / (k : ℝ) ^ k *
              (((k : ℝ) / ((k : ℝ) + 1)) ^ k *
                mv_polynomial_capacity p) := by
          simp only [Nat.cast_add, Nat.cast_one]
          rw [hscale]
          ring
        _ ≤ (Nat.factorial k : ℝ) / (k : ℝ) ^ k *
              mv_polynomial_capacity q := by
          apply mul_le_mul_of_nonneg_left
          · simpa [q] using hd.2.2.2
          · positivity
        _ ≤ q.coeff (∑ i : Fin k, Finsupp.single i 1) := hi
        _ = p.coeff (∑ i : Fin (k + 1), Finsupp.single i 1) := hcoeff

@[blueprint "lem:matrix-product-polynomial-capacity"
  (statement := /-- Let $n\in\mathbb N$, and let $A=(a_{ij})_{i,j\in[n]}$ be a real matrix such that $a_{ij}\geq 0$ for all $i,j\in[n]$, every row sum is $1$, and every column sum is $1$.  Then $p_A$ is homogeneous of degree $n$, every coefficient of $p_A$ is nonnegative, and $\operatorname{Cap}(p_A)\geq 1$. -/)
  (proof := /-- By \cref{def:matrix-product-polynomial}, every factor of $p_A$ is a sum of scalar multiples of variables and is therefore homogeneous of degree $1$.  The product of the $n$ factors is homogeneous of degree $n$.  Each factor has nonnegative coefficients, and the convolution formula for coefficients of a product, applied inductively to the factors, shows that every coefficient of $p_A$ is nonnegative.

  For a positive vector $x$, the weighted arithmetic--geometric mean inequality in row $i$, using $a_{ij}\geq0$ and $\sum_j a_{ij}=1$, gives
  \[
  \sum_j a_{ij}x_j\geq\prod_j x_j^{a_{ij}}.
  \]
  Multiplication over all rows and the column identities $\sum_i a_{ij}=1$ yield
  \[
  p_A(x)\geq\prod_j x_j^{\sum_i a_{ij}}
  =\prod_j x_j.
  \]
  Evaluation of the product polynomial at $x$ is the product of these row sums, so every quotient in the nonempty set whose infimum defines \cref{def:mv-polynomial-capacity} is at least $1$.  Hence $\operatorname{Cap}(p_A)\geq1$. -/)
  (title := /-- Capacity of the matrix product polynomial -/)
  (latexEnv := "lemma")]
lemma matrix_product_polynomial_capacity {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hnonnegative : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∑ j, A i j = 1)
    (hcolumn : ∀ j, ∑ i, A i j = 1) :
    (matrix_product_polynomial A).IsHomogeneous n ∧
      (∀ m, 0 ≤ (matrix_product_polynomial A).coeff m) ∧
      1 ≤ mv_polynomial_capacity (matrix_product_polynomial A) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · unfold matrix_product_polynomial
    simpa using
      MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin n))
        (fun i => ∑ j : Fin n, MvPolynomial.C (A i j) * MvPolynomial.X j)
        (fun _ => 1)
        (by
          intro i hi
          exact MvPolynomial.IsHomogeneous.sum (Finset.univ : Finset (Fin n))
            (fun j => MvPolynomial.C (A i j) * MvPolynomial.X j) 1
            (fun j hj => MvPolynomial.isHomogeneous_C_mul_X (A i j) j))
  · let f : Fin n → MvPolynomial (Fin n) ℝ :=
      fun i => ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j
    have hf : ∀ i m, 0 ≤ (f i).coeff m := by
      intro i m
      simp only [f, MvPolynomial.coeff_sum]
      exact Finset.sum_nonneg (fun j hj => by
        simp only [MvPolynomial.coeff_C_mul]
        exact mul_nonneg (hnonnegative i j) (by
          rw [MvPolynomial.coeff_X]
          split <;> norm_num))
    have hp : ∀ (s : Finset (Fin n)) m, 0 ≤ (∏ i ∈ s, f i).coeff m := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          intro m
          simp only [Finset.prod_empty, MvPolynomial.coeff_one]
          split <;> norm_num
      | @insert i s hi ih =>
          intro m
          rw [Finset.prod_insert hi, MvPolynomial.coeff_mul]
          exact Finset.sum_nonneg (fun x hx =>
            mul_nonneg (hf i x.1) (ih x.2))
    simpa [matrix_product_polynomial, f] using hp Finset.univ
  · rw [mv_polynomial_capacity]
    apply le_csInf
    · refine ⟨MvPolynomial.eval (fun _ => 1) (matrix_product_polynomial A) /
          ∏ i : Fin n, (1 : ℝ), ?_⟩
      exact ⟨fun _ => 1, by simp, rfl⟩
    · intro r hr
      rcases hr with ⟨x, hx, rfl⟩
      have hden : 0 < ∏ j, x j :=
        Finset.prod_pos (fun j hj => hx j)
      apply (le_div_iff₀ hden).2
      simp only [one_mul]
      have hrow_amgm (i : Fin n) :
          (∏ j, x j ^ A i j) ≤ ∑ j, A i j * x j := by
        simpa using
          Real.geom_mean_le_arith_mean_weighted
            (s := Finset.univ) (fun j => A i j) x
            (fun j hj => hnonnegative i j)
            (by simpa using hrow i)
            (fun j hj => (hx j).le)
      have hprod :
          (∏ i, ∏ j, x j ^ A i j) ≤
            ∏ i, ∑ j, A i j * x j := by
        exact Finset.prod_le_prod
          (fun i hi => Finset.prod_nonneg
            (fun j hj => Real.rpow_nonneg (hx j).le _))
          (fun i hi => hrow_amgm i)
      have hgeom : (∏ i, ∏ j, x j ^ A i j) = ∏ j, x j := by
        rw [Finset.prod_comm]
        apply Finset.prod_congr rfl
        intro j hj
        calc
          (∏ i, x j ^ A i j) = x j ^ (∑ i, A i j) := by
            symm
            simpa using
              Real.rpow_sum_of_pos (hx j) (fun i => A i j) Finset.univ
          _ = x j := by rw [hcolumn j, Real.rpow_one]
      have heval :
          MvPolynomial.eval x (matrix_product_polynomial A) =
            ∏ i, ∑ j, A i j * x j := by
        simp [matrix_product_polynomial]
      rw [heval, ← hgeom]
      assumption

@[blueprint "lem:matrix-product-polynomial-permanent-coefficient"
  (statement := /-- For every real $n\times n$ matrix $A$, the coefficient of $x_1\cdots x_n$ in $p_A$ is the permanent of $A$. -/)
  (proof := /-- Expand the product in \cref{def:matrix-product-polynomial} as a sum indexed by functions $f\colon [n]\to[n]$.  The summand indexed by $f$ is the monomial with exponent vector $\sum_i e_{f(i)}$ and coefficient $\prod_i a_{i,f(i)}$.  This exponent vector is the all-ones vector exactly when $f$ is bijective.  Indeed, equality of the exponent vectors implies that every $j\in[n]$ has a preimage under $f$, and a surjective self-map of the finite set $[n]$ is bijective; conversely, a bijection merely reindexes the sum of the standard basis vectors.  Hence the required coefficient is $\sum_{\sigma\in S_n}\prod_i a_{i,\sigma(i)}$.  Under the convention $\operatorname{per}(A)=\sum_{\sigma\in S_n}\prod_i a_{\sigma(i),i}$, this is $\operatorname{per}(A^{\mathsf T})$, which equals $\operatorname{per}(A)$ by invariance of the permanent under transposition. -/)
  (title := /-- The permanent as a squarefree coefficient -/)
  (latexEnv := "lemma")]
lemma matrix_product_polynomial_permanent_coefficient {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (matrix_product_polynomial A).coeff
      (∑ i : Fin n, Finsupp.single i 1) = A.permanent := by
  classical
  have h_bijective (f : Fin n → Fin n) :
      (∑ i, Finsupp.single (f i) 1) = (∑ i, Finsupp.single i 1) ↔
        Function.Bijective f := by
    constructor
    · intro h
      have hsurjective : Function.Surjective f := by
        intro j
        by_contra hj
        have hne : ∀ i, f i ≠ j := by
          intro i hij
          exact hj ⟨i, hij⟩
        have hvalue := congrArg (fun s : Fin n →₀ ℕ => s j) h
        simp [hne] at hvalue
      exact hsurjective.bijective_of_finite
    · intro hf
      simpa using
        (Equiv.sum_comp (Equiv.ofBijective f hf)
          (fun i => Finsupp.single i 1))
  rw [matrix_product_polynomial, ← Finset.sum_prod_piFinset,
    MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.C_mul_X_eq_monomial,
    ← MvPolynomial.monomial_sum_prod]
  simp only [MvPolynomial.coeff_monomial]
  simp_rw [h_bijective]
  calc
    (∑ f, if Function.Bijective f then ∏ i, A i (f i) else 0) =
        ∑ f : {f : Fin n → Fin n // Function.Bijective f}, ∏ i, A i (f.1 i) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_subtype
      intro f
      simp
    _ = ∑ σ : Equiv.Perm (Fin n), ∏ i, A i (σ i) := by
      apply Fintype.sum_equiv
        (Equiv.bijectiveEquiv :
          {f : Fin n → Fin n // Function.Bijective f} ≃ Equiv.Perm (Fin n))
      intro f
      rfl
    _ = A.permanent := by
      rw [← Matrix.permanent_transpose]
      rfl

@[blueprint "thm:van-der-waerden-permanent-lower-bound"
  (statement := /-- Let $n\in\mathbb N$, and let $A=(a_{ij})_{i,j\in[n]}$ be a matrix with nonnegative real entries.  Suppose that
  \[
  \sum_{j\in[n]}a_{ij}=1\quad\text{for every }i\in[n],
  \qquad
  \sum_{i\in[n]}a_{ij}=1\quad\text{for every }j\in[n].
  \]
  Then
  \[
  \operatorname{per}(A)\geq \frac{n!}{n^n}.
  \] -/)
  (proof := /-- Set $p=p_A$ as in \cref{def:matrix-product-polynomial}.  By \cref{lem:product-linear-forms-real-stable}, the polynomial $p$ is real stable.  By \cref{lem:matrix-product-polynomial-capacity}, it is homogeneous of degree $n$, has nonnegative coefficients, and satisfies $\operatorname{Cap}(p)\geq1$.  Therefore \cref{thm:gurvits-coefficient-capacity} gives
  \[
  [x_1\cdots x_n]p\geq
  \frac{n!}{n^n}\operatorname{Cap}(p)
  \geq\frac{n!}{n^n}.
  \]
  Finally, \cref{lem:matrix-product-polynomial-permanent-coefficient} identifies the coefficient on the left with $\operatorname{per}(A)$, proving the asserted inequality. -/)
  (title := /-- Van der Waerden permanent lower bound -/)
  (latexEnv := "theorem")]
theorem van_der_waerden_permanent_lower_bound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hnonnegative : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∑ j, A i j = 1)
    (hcolumn : ∀ j, ∑ i, A i j = 1) :
    (Nat.factorial n : ℝ) / (n : ℝ) ^ n ≤ A.permanent := by
  classical
  obtain ⟨hhomogeneous, hcoeff, hcapacity⟩ :=
    matrix_product_polynomial_capacity A hnonnegative hrow hcolumn
  calc
    (Nat.factorial n : ℝ) / (n : ℝ) ^ n ≤
        (Nat.factorial n : ℝ) / (n : ℝ) ^ n *
          mv_polynomial_capacity (matrix_product_polynomial A) := by
      simpa using
        mul_le_mul_of_nonneg_left hcapacity
          (show 0 ≤ (Nat.factorial n : ℝ) / (n : ℝ) ^ n by positivity)
    _ ≤ (matrix_product_polynomial A).coeff
        (∑ i : Fin n, Finsupp.single i 1) :=
      gurvits_coefficient_capacity _ hhomogeneous hcoeff
        (product_linear_forms_real_stable A hnonnegative hrow)
    _ = A.permanent := matrix_product_polynomial_permanent_coefficient A

@[blueprint "thm:vanderwaerdenbipperfmat"
  (statement := /-- Let $n,d\in\mathbb N$, and let $A=(a_{ij})_{i,j\in[n]}$ be a real matrix such that $a_{ij}\in\{0,1\}$ for every $i,j\in[n]$.  Suppose that every row sum and every column sum of $A$ is equal to $d$.  Then
  \[
  \operatorname{per}(A)\geq \frac{n!\,d^n}{n^n}.
  \] -/)
  (proof := /-- If $n=0$, then the quotient on the left and the permanent of the empty matrix are both equal to $1$.  Assume henceforth that $n>0$.  Since every entry of $A$ is either $0$ or $1$, the permanent of $A$ is nonnegative.  Thus, if $d=0$, the asserted inequality follows because its left-hand side is zero.

  It remains to suppose that $d>0$ and set $B=d^{-1}A$.  Every entry of $B$ is nonnegative.  For every row $i$ and every column $j$, the hypotheses give
  \[
  \sum_k B_{ik}=d^{-1}\sum_k A_{ik}=1,
  \qquad
  \sum_k B_{kj}=d^{-1}\sum_k A_{kj}=1.
  \]
  Hence \cref{thm:van-der-waerden-permanent-lower-bound} applies to $B$ and yields
  \[
  \frac{n!}{n^n}\leq\operatorname{per}(B).
  \]
  Homogeneity of the permanent gives
  $\operatorname{per}(B)=d^{-n}\operatorname{per}(A)$.  Multiplication by the positive number $d^n$ proves
  \[
  \frac{n!d^n}{n^n}\leq\operatorname{per}(A).
  \] -/)
  (title := /-- Van der Waerden bound for regular bipartite graphs -/)
  (latexEnv := "theorem")]
theorem vanderwaerdenbipperfmat {n d : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hzeroone : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hrow : ∀ i, ∑ j, A i j = (d : ℝ))
    (hcolumn : ∀ j, ∑ i, A i j = (d : ℝ)) :
    (Nat.factorial n : ℝ) * (d : ℝ) ^ n / (n : ℝ) ^ n ≤ A.permanent := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [Matrix.permanent]
  have hnonnegative : ∀ i j, 0 ≤ A i j := by
    intro i j
    rcases hzeroone i j with hij | hij <;> simp [hij]
  by_cases hd : d = 0
  · have hperm : 0 ≤ A.permanent := by
      rw [Matrix.permanent]
      exact Finset.sum_nonneg fun σ _ =>
        Finset.prod_nonneg fun i _ => hnonnegative _ _
    simpa [hd, hn] using hperm
  let B : Matrix (Fin n) (Fin n) ℝ := (d : ℝ)⁻¹ • A
  have hBrow : ∀ i, ∑ j, B i j = 1 := by
    intro i
    simp [B, ← Finset.mul_sum, hrow i, hd]
  have hBcolumn : ∀ j, ∑ i, B i j = 1 := by
    intro j
    simp [B, ← Finset.mul_sum, hcolumn j, hd]
  have hBnonnegative : ∀ i j, 0 ≤ B i j := by
    intro i j
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg d)) (hnonnegative i j)
  have hbound :=
    van_der_waerden_permanent_lower_bound B hBnonnegative hBrow hBcolumn
  calc
    (Nat.factorial n : ℝ) * (d : ℝ) ^ n / (n : ℝ) ^ n =
        (d : ℝ) ^ n * ((Nat.factorial n : ℝ) / (n : ℝ) ^ n) := by ring
    _ ≤ (d : ℝ) ^ n * B.permanent :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = A.permanent := by
      dsimp [B]
      rw [Matrix.permanent_smul, Fintype.card_fin]
      rw [← mul_assoc, ← mul_pow]
      simp [hd]

@[blueprint "lem:regular-cycle-factor-count-lower-bound"
  (statement := /-- Let $n,d\in\mathbb N$ with $d\geq 1$, and let $G$ be a directed $d$-regular graph on $[n]$.  If $\mathcal C$ is its set of cycle-factors, then
  \[
  |\mathcal C|\geq (d/e)^n.
  \] -/)
  (proof := /-- Form the $0$--$1$ matrix $A$ whose $(i,j)$-entry is $1$ exactly when $G$ has the directed edge $i\to j$.  By \cref{def:directed-regular}, every row sum and every column sum of $A$ is $d$.  Hence \cref{thm:vanderwaerdenbipperfmat} gives
  \[
  \operatorname{per}(A)\geq \frac{n!\,d^n}{n^n}.
  \]
  Expanding the permanent as a sum over permutations and using \cref{def:directed-cycle-factors} identifies $\operatorname{per}(A)$ with $|\mathcal C|$.  The lower form of Stirling's estimate, $n!\geq(n/e)^n$, now yields $|\mathcal C|\geq(d/e)^n$. -/)
  (title := /-- Lower bound for the number of cycle-factors -/)
  (latexEnv := "lemma")]
lemma regular_cycle_factor_count_lower_bound {n d : ℕ} (G : Digraph (Fin n))
    (hreg : directed_regular G d) (hd : 1 ≤ d) :
    ((d : ℝ) / Real.exp 1) ^ n ≤ ((directed_cycle_factors G).card : ℝ) := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [directed_cycle_factors]
  let A : Matrix (Fin n) (Fin n) ℝ :=
    fun i j => if G.Adj j i then 1 else 0
  have hzeroone : ∀ i j, A i j = 0 ∨ A i j = 1 := by
    intro i j
    simp only [A]
    split_ifs <;> simp
  have hrow : ∀ i, ∑ j, A i j = (d : ℝ) := by
    intro i
    simpa [A] using congrArg (fun x : ℕ => (x : ℝ)) (hreg.2 i)
  have hcolumn : ∀ j, ∑ i, A i j = (d : ℝ) := by
    intro j
    simpa [A] using congrArg (fun x : ℕ => (x : ℝ)) (hreg.1 j)
  have hpermanent :
      A.permanent = ((directed_cycle_factors G).card : ℝ) := by
    rw [Matrix.permanent]
    calc
      (∑ σ : Equiv.Perm (Fin n), ∏ i, A (σ i) i) =
          ∑ σ : Equiv.Perm (Fin n),
            if σ ∈ directed_cycle_factors G then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro σ hσ
        simp [A, directed_cycle_factors, Fintype.prod_boole]
      _ = ((directed_cycle_factors G).card : ℝ) := by
        simpa using
          (Finset.sum_boole (R := ℝ)
            (fun σ : Equiv.Perm (Fin n) =>
              σ ∈ directed_cycle_factors G) Finset.univ)
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hdpos : 0 < (d : ℝ) := by
    exact_mod_cast hd
  have hfactorial :
      ((n : ℝ) / Real.exp 1) ^ n ≤ (Nat.factorial n : ℝ) := by
    have hexp :=
      Real.pow_div_factorial_le_exp (x := (n : ℝ)) (le_of_lt hnpos) n
    have hexpn : Real.exp (n : ℝ) = Real.exp 1 ^ n := by
      simpa using Real.exp_nat_mul 1 n
    rw [div_pow]
    apply (div_le_iff₀ (pow_pos (Real.exp_pos 1) n)).2
    convert
      (div_le_iff₀ (show 0 < (Nat.factorial n : ℝ) by positivity)).1 hexp using 1 <;>
      rw [hexpn] <;> ring
  have hscale : 0 ≤ (d : ℝ) ^ n / (n : ℝ) ^ n := by
    exact le_of_lt (div_pos (pow_pos hdpos n) (pow_pos hnpos n))
  have hlower :
      ((d : ℝ) / Real.exp 1) ^ n ≤
        (Nat.factorial n : ℝ) * (d : ℝ) ^ n / (n : ℝ) ^ n := by
    calc
      ((d : ℝ) / Real.exp 1) ^ n =
          ((n : ℝ) / Real.exp 1) ^ n *
            ((d : ℝ) ^ n / (n : ℝ) ^ n) := by
              rw [div_pow]
              field_simp [pow_ne_zero n (ne_of_gt hnpos)]
              rw [div_pow]
              field_simp [pow_ne_zero n (ne_of_gt (Real.exp_pos 1))]
      _ ≤ (Nat.factorial n : ℝ) *
            ((d : ℝ) ^ n / (n : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_right hfactorial hscale
      _ = (Nat.factorial n : ℝ) * (d : ℝ) ^ n / (n : ℝ) ^ n := by
        ring
  calc
    ((d : ℝ) / Real.exp 1) ^ n ≤
        (Nat.factorial n : ℝ) * (d : ℝ) ^ n / (n : ℝ) ^ n := hlower
    _ ≤ A.permanent :=
      vanderwaerdenbipperfmat A hzeroone hrow hcolumn
    _ = ((directed_cycle_factors G).card : ℝ) := hpermanent

@[blueprint "lem:entropy-loss-skew"
  (statement := /-- Let $\mathcal X$ be a finite set of cardinality $s\geq2$, let $p$ be a probability mass function on $\mathcal X$, and put $\ell=\log_2s-H(p)$.  Then every $x\in\mathcal X$ satisfies
  \[
  p(x)\leq \frac{2}{s}+\ell.
  \] -/)
  (proof := /-- Fix $x\in\mathcal X$, put $q=p(x)$, and write $\log$ for the natural logarithm.  Expanding \cref{def:finite-shannon-entropy}, using $\sum_y p(y)=1$, and treating the zero terms separately gives
  \[
  (\log 2)\ell=\sum_{y\in\mathcal X}p(y)\log\bigl(sp(y)\bigr).
  \]
  For every $z\geq0$, the tangent-line inequality for the logarithm gives
  \[
  z-1\leq z\log z.
  \]
  Indeed, this is immediate for $z=0$, while for $z>0$ it follows by multiplying $1-z^{-1}\leq\log z$ by $z$.  Applying this inequality to $z=sp(y)$ and dividing by $s>0$ yields
  \[
  p(y)-\frac1s\leq p(y)\log\bigl(sp(y)\bigr).
  \]
  Summing over all $y$ shows that $(\log2)\ell\geq0$, and hence $\ell\geq0$.  Consequently the result is immediate if $q\leq2/s$.

  Suppose now that $q>2/s$.  Sum the preceding pointwise inequality only over $y\neq x$.  Since those $s-1$ masses sum to $1-q$, this gives
  \[
  (\log2)\ell\geq q\log(sq)+\frac1s-q.
  \]
  Set $t=sq>2$.  Applying $z-1\leq z\log z$ to $z=t/2$ gives
  \[
  t-2\leq t(\log t-\log2).
  \]
  Moreover, applying $\log u\leq u-1$ at $u=1/2$ gives $\log2\geq1/2$.  Adding these two inequalities and rearranging yields
  \[
  (\log2)(t-2)\leq t\log t+1-t.
  \]
  After division by $s$, the right-hand side is exactly $q\log(sq)+1/s-q$.  Thus $(\log2)(q-2/s)\leq(\log2)\ell$; since $\log2>0$, cancellation proves $q\leq2/s+\ell$. -/)
  (title := /-- Entropy deficit controls point masses -/)
  (latexEnv := "lemma")]
lemma entropy_loss_skew {α : Type*} [Fintype α] (p : α → ℝ) (s : ℕ)
    (ℓ : ℝ) (hs : 2 ≤ s) (hcard : Fintype.card α = s)
    (hnonneg : ∀ x : α, 0 ≤ p x) (hmass : ∑ x : α, p x = 1)
    (hloss : ℓ = Real.logb 2 (s : ℝ) - finite_shannon_entropy p)
    (x : α) :
    p x ≤ (2 : ℝ) / (s : ℝ) + ℓ := by
  classical
  have hspos : 0 < (s : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hs)
  have hsne : (s : ℝ) ≠ 0 := ne_of_gt hspos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt hlog2
  have hloghalf : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at h
    norm_num at h ⊢
    linarith
  have hmul_log (z : ℝ) (hz : 0 ≤ z) : z - 1 ≤ z * Real.log z := by
    rcases eq_or_lt_of_le hz with rfl | hzpos
    · simp
    · have h := Real.one_sub_inv_le_log_of_pos hzpos
      calc
        z - 1 = z * (1 - z⁻¹) := by
          field_simp [ne_of_gt hzpos]
          <;> ring
        _ ≤ z * Real.log z := mul_le_mul_of_nonneg_left h hz
  have hlog_mul (y : α) :
      p y * Real.log ((s : ℝ) * p y) =
        p y * Real.log (s : ℝ) + p y * Real.log (p y) := by
    by_cases hy : p y = 0
    · simp [hy]
    · rw [Real.log_mul hsne hy]
      ring
  have hsum_log :
      (∑ y : α, p y * Real.log ((s : ℝ) * p y)) =
        Real.log (s : ℝ) + ∑ y : α, p y * Real.log (p y) := by
    calc
      (∑ y : α, p y * Real.log ((s : ℝ) * p y)) =
          ∑ y : α, (p y * Real.log (s : ℝ) + p y * Real.log (p y)) := by
            apply Finset.sum_congr rfl
            intro y hy
            exact hlog_mul y
      _ = (∑ y : α, p y) * Real.log (s : ℝ) +
          ∑ y : α, p y * Real.log (p y) := by
            rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ = Real.log (s : ℝ) + ∑ y : α, p y * Real.log (p y) := by
            rw [hmass]
            ring
  have hcancel (y : α) :
      Real.log 2 * (-(p y) * (Real.log (p y) / Real.log 2)) =
        -(p y) * Real.log (p y) := by
    field_simp [hlog2ne]
  have hdef :
      Real.log 2 * ℓ = ∑ y : α, p y * Real.log ((s : ℝ) * p y) := by
    rw [hloss, finite_shannon_entropy]
    simp only [Real.logb]
    rw [mul_sub, mul_div_cancel₀ _ hlog2ne, Finset.mul_sum]
    simp_rw [hcancel]
    rw [hsum_log]
    rw [show (∑ y : α, -(p y) * Real.log (p y)) =
        -(∑ y : α, p y * Real.log (p y)) by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro y hy
      ring]
    ring
  have hterm (y : α) :
      p y - 1 / (s : ℝ) ≤ p y * Real.log ((s : ℝ) * p y) := by
    have hbase := hmul_log ((s : ℝ) * p y)
      (mul_nonneg (le_of_lt hspos) (hnonneg y))
    have hscaled :
        (s : ℝ) * (p y - 1 / (s : ℝ)) ≤
          (s : ℝ) * (p y * Real.log ((s : ℝ) * p y)) := by
      calc
        (s : ℝ) * (p y - 1 / (s : ℝ)) = (s : ℝ) * p y - 1 := by
          field_simp [hsne]
          <;> ring
        _ ≤ ((s : ℝ) * p y) * Real.log ((s : ℝ) * p y) := hbase
        _ = (s : ℝ) * (p y * Real.log ((s : ℝ) * p y)) := by ring
    exact le_of_mul_le_mul_left hscaled hspos
  have hall :
      (∑ y : α, (p y - 1 / (s : ℝ))) ≤
        ∑ y : α, p y * Real.log ((s : ℝ) * p y) := by
    apply Finset.sum_le_sum
    intro y hy
    exact hterm y
  have hleft_all : (∑ y : α, (p y - 1 / (s : ℝ))) = 0 := by
    rw [Finset.sum_sub_distrib, hmass]
    simp [hcard]
    field_simp [hsne]
    ring
  have hscaled_nonneg : 0 ≤ Real.log 2 * ℓ := by
    calc
      0 = ∑ y : α, (p y - 1 / (s : ℝ)) := hleft_all.symm
      _ ≤ ∑ y : α, p y * Real.log ((s : ℝ) * p y) := hall
      _ = Real.log 2 * ℓ := hdef.symm
  have hellnonneg : 0 ≤ ℓ := by
    by_contra hn
    have hn' : ℓ < 0 := lt_of_not_ge hn
    have : Real.log 2 * ℓ < 0 := mul_neg_of_pos_of_neg hlog2 hn'
    exact (not_lt_of_ge hscaled_nonneg) this
  by_cases hsmall : p x ≤ 2 / (s : ℝ)
  · linarith
  · have hlarge : 2 / (s : ℝ) < p x := lt_of_not_ge hsmall
    have ht : 2 < (s : ℝ) * p x := by
      have := (div_lt_iff₀ hspos).mp hlarge
      simpa [mul_comm] using this
    have hrest :
        (∑ y ∈ Finset.univ.erase x, (p y - 1 / (s : ℝ))) ≤
          ∑ y ∈ Finset.univ.erase x,
            p y * Real.log ((s : ℝ) * p y) := by
      apply Finset.sum_le_sum
      intro y hy
      exact hterm y
    have hp_erase :
        (∑ y ∈ Finset.univ.erase x, p y) = 1 - p x := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ x), hmass]
    have hcard_erase : (Finset.univ.erase x).card = s - 1 := by
      simp [hcard]
    have hleft_rest :
        (∑ y ∈ Finset.univ.erase x, (p y - 1 / (s : ℝ))) =
          1 / (s : ℝ) - p x := by
      rw [Finset.sum_sub_distrib, hp_erase]
      simp only [Finset.sum_const, nsmul_eq_mul, hcard_erase]
      push_cast [Nat.cast_sub (show 1 ≤ s by omega)]
      field_simp [hsne]
      ring
    have hscaled_lower :
        p x * Real.log ((s : ℝ) * p x) + (1 / (s : ℝ) - p x) ≤
          Real.log 2 * ℓ := by
      rw [hdef]
      rw [← Finset.sum_erase_add Finset.univ
        (fun y : α => p y * Real.log ((s : ℝ) * p y)) (Finset.mem_univ x)]
      linarith
    have htne : (s : ℝ) * p x ≠ 0 := by linarith
    have hu := hmul_log (((s : ℝ) * p x) / 2)
      (show 0 ≤ ((s : ℝ) * p x) / 2 by positivity)
    rw [Real.log_div htne (by norm_num)] at hu
    have hanalytic :
        Real.log 2 * (p x - 2 / (s : ℝ)) ≤
          p x * Real.log ((s : ℝ) * p x) + 1 / (s : ℝ) - p x := by
      apply le_of_mul_le_mul_left (a := (s : ℝ))
      have hleft :
          (s : ℝ) * (Real.log 2 * (p x - 2 / (s : ℝ))) =
            Real.log 2 * ((s : ℝ) * p x - 2) := by
        field_simp [hsne]
        <;> ring
      have hright :
          (s : ℝ) *
              (p x * Real.log ((s : ℝ) * p x) + 1 / (s : ℝ) - p x) =
            ((s : ℝ) * p x) * Real.log ((s : ℝ) * p x) + 1 -
              (s : ℝ) * p x := by
        field_simp [hsne]
        <;> ring
      rw [hleft, hright]
      nlinarith
      exact hspos
    have hmul :
        Real.log 2 * (p x - 2 / (s : ℝ)) ≤ Real.log 2 * ℓ :=
      le_trans hanalytic (by linarith [hscaled_lower])
    have hdiff : p x - 2 / (s : ℝ) ≤ ℓ :=
      le_of_mul_le_mul_left hmul hlog2
    linarith

@[blueprint "lem:remaining-neighbor-rank-uniform"
  (statement := /-- Let $G$ be directed $d$-regular on $[n]$, let $\sigma$ be a cycle-factor, and fix a vertex $i$.  If $1\leq t\leq d$, then exactly $n!/d$ orderings $\tau$ have $s(i,\sigma,\tau)=t$; equivalently, the number of such orderings multiplied by $d$ is $n!$. -/)
  (proof := /-- Let
  \[
  B=\{x\in[n]:(i,\sigma(x))\in E(G)\}.
  \]
  By \cref{def:directed-cycle-factors}, $i\in B$.  Since $\sigma$ is a bijection, \cref{def:directed-regular} gives $|B|=d$.  For an ordering $\tau$ and $x\in B$, define
  \[
  r_\tau(x)=\bigl|\{y\in B:\tau^{-1}(y)\geq\tau^{-1}(x)\}\bigr|.
  \]
  The map $x\mapsto r_\tau(x)-1$ from $B$ to $\{0,\ldots,d-1\}$ is injective.  Indeed, if $\tau^{-1}(x)<\tau^{-1}(y)$, then the upper set counted by $r_\tau(y)$ is a proper subset of the upper set counted by $r_\tau(x)$, and the reverse inequality is handled symmetrically.  The domain and codomain both have cardinality $d$, so this map is bijective.  Thus, for every $t$ with $1\leq t\leq d$, there is a unique $x\in B$ satisfying $r_\tau(x)=t$.

  Changing variables by $j=\sigma(x)$ in \cref{def:remaining-neighbor-count} shows that
  $s(i,\sigma,\tau)=r_\tau(i)$.  Let $S_t$ be the set of orderings for which this value is $t$.  Map a pair $(\tau,x)\in S_t\times B$ to the ordering obtained by transposing the labels $i$ and $x$ after applying $\tau$.  Since both transposed labels lie in $B$, the transposition preserves $B$, and the rank of $x$ in the resulting ordering is $t$.  Conversely, in any resulting ordering the unique element of $B$ of rank $t$ determines $x$, after which the same transposition recovers $\tau$.  Hence this map is a bijection from $S_t\times B$ to all permutations of $[n]$.  Therefore $|S_t|d=n!$, as required. -/)
  (title := /-- Uniform relative rank of the remaining-neighbour count -/)
  (latexEnv := "lemma")]
lemma remaining_neighbor_rank_uniform {n d : ℕ} (G : Digraph (Fin n))
    (σ : Equiv.Perm (Fin n)) (hreg : directed_regular G d)
    (hσ : σ ∈ directed_cycle_factors G) (i : Fin n) (t : ℕ)
    (ht₁ : 1 ≤ t) (htd : t ≤ d) :
    (Finset.univ.filter (fun τ : Equiv.Perm (Fin n) =>
      remaining_neighbor_count G σ τ i = t)).card * d = Nat.factorial n := by
  classical
  let B : Finset (Fin n) :=
    Finset.univ.filter fun x : Fin n => G.Adj i (σ x)
  have hσ' : ∀ v : Fin n, G.Adj v (σ v) := by
    simpa [directed_cycle_factors] using hσ
  have hiB : i ∈ B := by
    simp [B, hσ' i]
  have hBcard : B.card = d := by
    calc
      B.card =
          (Finset.univ.filter fun y : Fin n => G.Adj i y).card := by
            apply Finset.card_equiv σ
            intro x
            simp [B]
      _ = d := by
        simpa [directed_regular] using hreg.1 i
  let rank (τ : Equiv.Perm (Fin n)) (x : Fin n) : ℕ :=
    (B.filter fun y : Fin n =>
      ¬ ((τ.symm y).val < (τ.symm x).val)).card
  have hrank_pos (τ : Equiv.Perm (Fin n)) {x : Fin n} (hx : x ∈ B) :
      1 ≤ rank τ x := by
    have hx' :
        x ∈ B.filter (fun y : Fin n =>
          ¬ ((τ.symm y).val < (τ.symm x).val)) := by
      simp [hx]
    simpa [rank] using Finset.card_pos.mpr ⟨x, hx'⟩
  have hrank_le (τ : Equiv.Perm (Fin n)) (x : Fin n) :
      rank τ x ≤ d := by
    calc
      rank τ x ≤ B.card := by
        simpa [rank] using
          (Finset.card_filter_le B
            (fun y : Fin n =>
              ¬ ((τ.symm y).val < (τ.symm x).val)))
      _ = d := hBcard
  have hrank_unique (τ : Equiv.Perm (Fin n)) :
      ∃! x : {x // x ∈ B}, rank τ x = t := by
    let r : {x // x ∈ B} → Fin d := fun x =>
      ⟨rank τ x - 1, by
        have hp := hrank_pos τ x.property
        have hl := hrank_le τ x
        omega⟩
    have hr_inj : Function.Injective r := by
      intro x y hxy
      have hrank_eq : rank τ x = rank τ y := by
        have hv := congrArg Fin.val hxy
        dsimp [r] at hv
        have hxpos := hrank_pos τ x.property
        have hypos := hrank_pos τ y.property
        omega
      by_contra hne
      have hpos_ne : (τ.symm x).val ≠ (τ.symm y).val := by
        intro hpos
        apply hne
        apply Subtype.ext
        apply τ.symm.injective
        exact Fin.ext hpos
      rcases lt_or_gt_of_ne hpos_ne with hlt | hlt
      · have hsub :
            B.filter (fun z : Fin n =>
                ¬ ((τ.symm z).val < (τ.symm y).val)) ⊂
              B.filter (fun z : Fin n =>
                ¬ ((τ.symm z).val < (τ.symm x).val)) := by
          apply Finset.ssubset_iff_subset_ne.mpr
          constructor
          · intro z hz
            simp only [Finset.mem_filter] at hz ⊢
            constructor
            · exact hz.1
            · omega
          · intro heq
            have hm := congrArg (fun s : Finset (Fin n) => x.val ∈ s) heq
            simp [x.property, hlt] at hm
            omega
        have hc := Finset.card_lt_card hsub
        exact (Nat.ne_of_lt hc) hrank_eq.symm
      · have hsub :
            B.filter (fun z : Fin n =>
                ¬ ((τ.symm z).val < (τ.symm x).val)) ⊂
              B.filter (fun z : Fin n =>
                ¬ ((τ.symm z).val < (τ.symm y).val)) := by
          apply Finset.ssubset_iff_subset_ne.mpr
          constructor
          · intro z hz
            simp only [Finset.mem_filter] at hz ⊢
            constructor
            · exact hz.1
            · omega
          · intro heq
            have hm := congrArg (fun s : Finset (Fin n) => y.val ∈ s) heq
            simp [y.property, hlt] at hm
            omega
        have hc := Finset.card_lt_card hsub
        exact (Nat.ne_of_lt hc) hrank_eq
    have hr_surj : Function.Surjective r := by
      apply
        ((Fintype.bijective_iff_injective_and_card r).2
          ⟨hr_inj, ?_⟩).2
      simp [hBcard]
    let target : Fin d := ⟨t - 1, by omega⟩
    obtain ⟨x, hx⟩ := hr_surj target
    have hxrank : rank τ x = t := by
      have hv := congrArg Fin.val hx
      dsimp [r, target] at hv
      have hp := hrank_pos τ x.property
      omega
    refine ⟨x, hxrank, ?_⟩
    intro y hyrank
    apply hr_inj
    apply Fin.ext
    dsimp [r]
    omega
  have hswap_mem {j : Fin n} (hj : j ∈ B) (x : Fin n) :
      Equiv.swap i j x ∈ B ↔ x ∈ B := by
    by_cases hxi : x = i
    · subst x
      simp [hiB, hj]
    by_cases hxj : x = j
    · subst x
      simp [hiB, hj]
    simp [Equiv.swap_apply_def, hxi, hxj]
  have hrank_swap (τ : Equiv.Perm (Fin n)) {j : Fin n}
      (hj : j ∈ B) (x : Fin n) :
      rank (τ.trans (Equiv.swap i j)) (Equiv.swap i j x) =
        rank τ x := by
    dsimp [rank]
    apply Finset.card_equiv (Equiv.swap i j)
    intro y
    simp only [Finset.mem_filter]
    rw [hswap_mem hj]
    simp
  have hremaining (τ : Equiv.Perm (Fin n)) :
      remaining_neighbor_count G σ τ i = rank τ i := by
    unfold remaining_neighbor_count
    dsimp [rank]
    symm
    apply Finset.card_equiv σ
    intro x
    simp [B]
  let S : Finset (Equiv.Perm (Fin n)) :=
    Finset.univ.filter fun τ : Equiv.Perm (Fin n) => rank τ i = t
  have hfilter :
      (Finset.univ.filter (fun τ : Equiv.Perm (Fin n) =>
        remaining_neighbor_count G σ τ i = t)) = S := by
    ext τ
    simp [S, hremaining]
  have hcard :
      (S ×ˢ B).card =
        (Finset.univ : Finset (Equiv.Perm (Fin n))).card := by
    apply Finset.card_bij
        (fun p _ => p.1.trans (Equiv.swap i p.2))
    · intro p hp
      simp
    · intro p₁ hp₁ p₂ hp₂ heq
      obtain ⟨hτ₁, hj₁⟩ := Finset.mem_product.mp hp₁
      obtain ⟨hτ₂, hj₂⟩ := Finset.mem_product.mp hp₂
      have hri₁ : rank p₁.1 i = t := (Finset.mem_filter.mp hτ₁).2
      have hri₂ : rank p₂.1 i = t := (Finset.mem_filter.mp hτ₂).2
      have hrj₁ :
          rank (p₁.1.trans (Equiv.swap i p₁.2)) p₁.2 = t := by
        simpa using (hrank_swap p₁.1 hj₁ i).trans hri₁
      have hrj₂ :
          rank (p₁.1.trans (Equiv.swap i p₁.2)) p₂.2 = t := by
        rw [heq]
        simpa using (hrank_swap p₂.1 hj₂ i).trans hri₂
      obtain ⟨z, hz, hzuniq⟩ :=
        hrank_unique (p₁.1.trans (Equiv.swap i p₁.2))
      have hj_eq : p₁.2 = p₂.2 := by
        have h₁ := hzuniq ⟨p₁.2, hj₁⟩ hrj₁
        have h₂ := hzuniq ⟨p₂.2, hj₂⟩ hrj₂
        exact congrArg Subtype.val (h₁.trans h₂.symm)
      apply Prod.ext
      · apply Equiv.ext
        intro x
        apply (Equiv.swap i p₁.2).injective
        simpa [hj_eq] using DFunLike.congr_fun heq x
      · exact hj_eq
    · intro τ hτ
      obtain ⟨j, hjrank, hjuniq⟩ := hrank_unique τ
      let τ' : Equiv.Perm (Fin n) :=
        τ.trans (Equiv.swap i j)
      have hτ'rank : rank τ' i = t := by
        simpa [τ'] using (hrank_swap τ j.property j).trans hjrank
      refine ⟨(τ', j.val), ?_, ?_⟩
      · apply Finset.mem_product.mpr
        constructor
        · simp [S, hτ'rank]
        · exact j.property
      · dsimp [τ']
        apply Equiv.ext
        intro x
        simp
  rw [hfilter, ← hBcard, ← Finset.card_product, hcard]
  simpa using (Fintype.card_perm (α := Fin n))

@[blueprint "lem:permutation-cycle-closing-count-local"
  (statement := /-- Let $\sigma$ and $\tau$ be permutations of $[n]$.  In every $\sigma$-cycle, exactly one vertex is maximal in the order induced by $\tau$.  Consequently, the number of vertices $i$ such that every vertex in the $\sigma$-cycle of $i$ occurs no later than $i$ in this order is the number of cycles of $\sigma$. -/)
  (proof := /-- Map every vertex that is maximal in its $\sigma$-cycle to its class in the quotient from \cref{def:permutation-cycle-count}.  Two maximal vertices in the same class have order positions bounded by one another, hence have equal positions and are equal.  Conversely, in each quotient class, choose a vertex whose order position is maximal; finiteness of $[n]$ guarantees such a vertex, and it satisfies the required maximality condition.  This gives a bijection between the selected vertices and the quotient classes, so their cardinalities agree. -/)
  (title := /-- Closing vertices count permutation cycles -/)
  (latexEnv := "lemma")]
lemma permutation_cycle_closing_count_local {n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) :
    (∑ i : Fin n, if
      (∀ x : Fin n, σ.SameCycle i x →
        (τ.symm x).val ≤ (τ.symm i).val)
      then 1 else 0) = permutation_cycle_count σ := by
  classical
  let P := {i : Fin n //
    ∀ x : Fin n, σ.SameCycle i x →
      (τ.symm x).val ≤ (τ.symm i).val}
  let toQ : P → Quotient (Equiv.Perm.SameCycle.setoid σ) :=
    fun i => Quotient.mk _ i.1
  have hinj : Function.Injective toQ := by
    intro a b hab
    have hs : σ.SameCycle a.1 b.1 := Quotient.exact hab
    have habpos := a.2 b.1 hs
    have hbapos := b.2 a.1 hs.symm
    have hpos : (τ.symm a.1).val = (τ.symm b.1).val :=
      le_antisymm hbapos habpos
    have harg : τ.symm a.1 = τ.symm b.1 := Fin.ext hpos
    exact Subtype.ext (τ.symm.injective harg)
  have hsurj : Function.Surjective toQ := by
    intro q
    let r : Fin n := q.out
    let O : Finset (Fin n) :=
      Finset.univ.filter fun x => σ.SameCycle r x
    have hrO : r ∈ O := by
      simp [O, Equiv.Perm.SameCycle.rfl]
    obtain ⟨i, hiO, himax⟩ :=
      Finset.exists_max_image O (fun x => (τ.symm x).val) ⟨r, hrO⟩
    have hir : σ.SameCycle r i := (Finset.mem_filter.mp hiO).2
    have hiP :
        ∀ x : Fin n, σ.SameCycle i x →
          (τ.symm x).val ≤ (τ.symm i).val := by
      intro x hix
      apply himax x
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hir.trans hix⟩
    refine ⟨⟨i, hiP⟩, ?_⟩
    change Quotient.mk _ i = q
    rw [← Quotient.out_eq q]
    exact Quotient.sound hir.symm
  have hcard :
      Fintype.card P =
        Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid σ)) :=
    Fintype.card_congr (Equiv.ofBijective toQ ⟨hinj, hsurj⟩)
  unfold permutation_cycle_count
  rw [← hcard]
  simpa [P] using
    (Fintype.card_subtype (fun i : Fin n =>
      ∀ x : Fin n, σ.SameCycle i x →
        (τ.symm x).val ≤ (τ.symm i).val)).symm

@[blueprint "lem:permutation-cycle-closing-value-unique-local"
  (statement := /-- Let $\sigma_1,\sigma_2,$ and $\tau$ be permutations of $[n]$, and fix $i\in[n]$.  Suppose that $\sigma_1$ and $\sigma_2$ agree on every vertex preceding $i$ in the order induced by $\tau$, and that $i$ is maximal in its cycle for both permutations.  Then $\sigma_1(i)=\sigma_2(i)$. -/)
  (proof := /-- Put $a=\sigma_1(i)$.  If $a=i$, then $a$ is already in the $\sigma_2$-cycle of $i$.  Otherwise, follow the $\sigma_1$-orbit from $a$ until it first reaches $i$.  Every intermediate vertex belongs to the $\sigma_1$-cycle of $i$, is distinct from $i$, and hence precedes $i$.  The agreement hypothesis therefore shows inductively that the same orbit segment occurs for $\sigma_2$, so $a$ belongs to the $\sigma_2$-cycle of $i$ as well.  Let $x=\sigma_2^{-1}(a)$.  Then $x$ is in this cycle.  If $x\ne i$, maximality makes $x$ precede $i$, so agreement gives $\sigma_1(x)=a=\sigma_1(i)$, contradicting injectivity.  Thus $x=i$, and $\sigma_2(i)=a=\sigma_1(i)$. -/)
  (title := /-- Uniqueness of the closing value in a conditioning fiber -/)
  (latexEnv := "lemma")]
lemma permutation_cycle_closing_value_unique_local {n : ℕ}
    (σ₁ σ₂ τ : Equiv.Perm (Fin n)) (i : Fin n)
    (hagree : ∀ x : Fin n,
      (τ.symm x).val < (τ.symm i).val → σ₁ x = σ₂ x)
    (hclose₁ : ∀ x : Fin n, σ₁.SameCycle i x →
      (τ.symm x).val ≤ (τ.symm i).val)
    (hclose₂ : ∀ x : Fin n, σ₂.SameCycle i x →
      (τ.symm x).val ≤ (τ.symm i).val) :
    σ₁ i = σ₂ i := by
  classical
  have hcycle₂ : σ₂.SameCycle (σ₁ i) i := by
    by_cases hai : σ₁ i = i
    · simpa [hai] using
        (Equiv.Perm.SameCycle.rfl (f := σ₂) (x := i))
    · have hcycle₁ : σ₁.SameCycle (σ₁ i) i := by
        simpa using (Equiv.Perm.SameCycle.rfl (f := σ₁) (x := i))
      obtain ⟨k, hk⟩ := hcycle₁.exists_nat_pow_eq
      let hpow : ∃ k : ℕ, (σ₁ ^ k) (σ₁ i) = i := ⟨k, hk⟩
      let m : ℕ := Nat.find hpow
      have hm : (σ₁ ^ m) (σ₁ i) = i := Nat.find_spec hpow
      have hmpos : 0 < m := by
        by_contra h
        have hmzero : m = 0 := Nat.eq_zero_of_not_pos h
        have hfix : σ₁ i = i := by simpa [hmzero] using hm
        exact hai hfix
      have hprefix (r : ℕ) (hr : r < m) :
          (τ.symm ((σ₁ ^ r) (σ₁ i))).val < (τ.symm i).val := by
        have hsame :
            σ₁.SameCycle i ((σ₁ ^ r) (σ₁ i)) := by
          refine ⟨(r + 1 : ℕ), ?_⟩
          rw [zpow_natCast]
          rw [pow_succ]
          rw [Equiv.Perm.mul_apply]
        have hle := hclose₁ _ hsame
        have hne : (σ₁ ^ r) (σ₁ i) ≠ i := by
          intro heq
          have hmr : m ≤ r := Nat.find_min' hpow heq
          omega
        have hposne :
            (τ.symm ((σ₁ ^ r) (σ₁ i))).val ≠ (τ.symm i).val := by
          intro heq
          apply hne
          exact τ.symm.injective (Fin.ext heq)
        exact lt_of_le_of_ne hle hposne
      have hit (r : ℕ) (hr : r ≤ m) :
          (σ₂ ^ r) (σ₁ i) = (σ₁ ^ r) (σ₁ i) := by
        induction r with
        | zero => simp
        | succ r ihr =>
            have hrlt : r < m := Nat.lt_of_succ_le hr
            calc
              (σ₂ ^ (r + 1)) (σ₁ i) =
                  σ₂ ((σ₂ ^ r) (σ₁ i)) := by simp [pow_succ']
              _ = σ₂ ((σ₁ ^ r) (σ₁ i)) := by rw [ihr (Nat.le_of_lt hrlt)]
              _ = σ₁ ((σ₁ ^ r) (σ₁ i)) := (hagree _ (hprefix r hrlt)).symm
              _ = (σ₁ ^ (r + 1)) (σ₁ i) := by simp [pow_succ']
      refine ⟨(m : ℤ), ?_⟩
      rw [zpow_natCast]
      exact (hit m le_rfl).trans hm
  let x : Fin n := σ₂.symm (σ₁ i)
  have hxa : σ₂.SameCycle x (σ₁ i) := by
    simpa [x] using
      (Equiv.Perm.SameCycle.apply_left
        (Equiv.Perm.SameCycle.rfl (f := σ₂) (x := σ₁ i)))
  have hix : σ₂.SameCycle i x := hcycle₂.symm.trans hxa.symm
  have hx : x = i := by
    by_contra hxi
    have hxle := hclose₂ x hix
    have hxposne : (τ.symm x).val ≠ (τ.symm i).val := by
      intro heq
      apply hxi
      exact τ.symm.injective (Fin.ext heq)
    have hxlt : (τ.symm x).val < (τ.symm i).val :=
      lt_of_le_of_ne hxle hxposne
    have heq : σ₁ x = σ₁ i := by
      rw [hagree x hxlt]
      simp [x]
    exact hxi (σ₁.injective heq)
  have h := congrArg σ₂ hx
  simpa [x] using h

@[blueprint "lem:factorial-log-upper-local"
  (statement := /-- For every positive integer $d$,
  \[
  \log(d!)\leq (d+1)\log d-d+1.
  \] -/)
  (proof := /-- Proceed by induction on $d$.  The case $d=1$ is immediate.  For the induction step, apply $1-x^{-1}\leq\log x$ with $x=(d+1)/d$.  Since
  \[
  1-\left(\frac{d+1}{d}\right)^{-1}=\frac1{d+1},
  \]
  multiplication by $d+1$ gives
  \[
  1\leq(d+1)(\log(d+1)-\log d).
  \]
  Adding $\log(d+1)$ to the induction hypothesis and using this inequality yields the asserted bound for $(d+1)!$. -/)
  (title := /-- Elementary upper estimate for the logarithm of a factorial -/)
  (latexEnv := "lemma")]
lemma factorial_log_upper_local (d : ℕ) (hd : 1 ≤ d) :
    Real.log (Nat.factorial d : ℝ) ≤
      ((d : ℝ) + 1) * Real.log (d : ℝ) - (d : ℝ) + 1 := by
  induction d with
  | zero => omega
  | succ d ih =>
      by_cases hd0 : d = 0
      · subst d
        norm_num
      · have hdpos : 0 < (d : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hd0
        have hsuccpos : 0 < ((d + 1 : ℕ) : ℝ) := by positivity
        have hi := ih (Nat.one_le_iff_ne_zero.mpr hd0)
        have hratio :
            0 < (((d + 1 : ℕ) : ℝ) / (d : ℝ)) :=
          div_pos hsuccpos hdpos
        have hlog :=
          Real.one_sub_inv_le_log_of_pos hratio
        have hinv :
            ((((d + 1 : ℕ) : ℝ) / (d : ℝ))⁻¹) =
              (d : ℝ) / ((d + 1 : ℕ) : ℝ) := by
          rw [inv_div]
        rw [hinv, Real.log_div (ne_of_gt hsuccpos) (ne_of_gt hdpos)] at hlog
        have hstep :
            1 ≤ ((d + 1 : ℕ) : ℝ) *
              (Real.log ((d + 1 : ℕ) : ℝ) - Real.log (d : ℝ)) := by
          have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hsuccpos)
          field_simp [ne_of_gt hsuccpos] at hmul
          norm_num [Nat.cast_add] at hmul ⊢
          exact hmul
        rw [Nat.factorial_succ, Nat.cast_mul,
          Real.log_mul (by positivity : ((d + 1 : ℕ) : ℝ) ≠ 0)
            (by positivity : (Nat.factorial d : ℝ) ≠ 0)]
        push_cast
        norm_num [Nat.cast_add] at hstep ⊢
        nlinarith

@[blueprint "lem:finite-fiber-entropy-mark-bound-local"
  (statement := /-- Let $S$ be a finite family, let $g$ record a conditioning fiber, and let $v$ be a value lying in a nonempty finite allowed set $A$ that is constant on every fiber of $g$.  Suppose that among the marked members of any one fiber, the value $v$ is unique.  For each member $w$, let $p_w$ be the distribution of $v$ on its fiber and let
  \[
  \ell_w=\log_2|A(w)|-H(p_w).
  \]
  Then the number of marked members of $S$ is at most the sum over $w\in S$ of $2/|A(w)|+\ell_w$. -/)
  (proof := /-- Partition $S$ into the fibers of $g$.  In a nonempty fiber, choose a representative $w$.  Counting the members according to their values shows that $p_w$ is a probability mass function on $A(w)$.  If $|A(w)|=1$, the distribution is concentrated at its unique point, so its entropy loss is zero and the claimed fiber bound is immediate.  If $|A(w)|\geq2$ and the fiber has a marked member $u$, the uniqueness hypothesis puts every marked member among those with value $v(u)$.  Apply \cref{lem:entropy-loss-skew} to $p_w$ at this value, and multiply by the fiber cardinality.  If there is no marked member, the same lemma at any allowed value shows that the right-hand side is nonnegative.  Summing the resulting inequalities over all fibers proves the assertion. -/)
  (title := /-- Entropy loss bounds marked members fiberwise -/)
  (latexEnv := "lemma")]
lemma finite_fiber_entropy_mark_bound_local
    {Ω κ α : Type*} [Fintype Ω] [Fintype κ] [Fintype α]
    [DecidableEq κ] [DecidableEq α]
    (S : Finset Ω) (g : Ω → κ) (v : Ω → α)
    (A : Ω → Finset α) (mark : Ω → Prop) [DecidablePred mark]
    (hA : ∀ u ∈ S, ∀ w ∈ S, g u = g w → A u = A w)
    (hv : ∀ u ∈ S, v u ∈ A u)
    (hpos : ∀ u ∈ S, 1 ≤ (A u).card)
    (huniq : ∀ u ∈ S, ∀ w ∈ S,
      g u = g w → mark u → mark w → v u = v w) :
    let p := fun (w : Ω) (x : {x // x ∈ A w}) =>
      (((S.filter fun u => g u = g w).filter fun u => v u = x.1).card : ℝ) /
        ((S.filter fun u => g u = g w).card : ℝ)
    let ell := fun w =>
      Real.logb 2 ((A w).card : ℝ) - finite_shannon_entropy (p w)
    (∑ w ∈ S, if mark w then (1 : ℝ) else 0) ≤
      ∑ w ∈ S, ((2 : ℝ) / ((A w).card : ℝ) + ell w) := by
  classical
  dsimp only
  let p := fun (w : Ω) (x : {x // x ∈ A w}) =>
    (((S.filter fun u => g u = g w).filter fun u => v u = x.1).card : ℝ) /
      ((S.filter fun u => g u = g w).card : ℝ)
  let ell := fun w =>
    Real.logb 2 ((A w).card : ℝ) - finite_shannon_entropy (p w)
  let B := fun w => (2 : ℝ) / ((A w).card : ℝ) + ell w
  rw [← Finset.sum_fiberwise S g
    (fun w => if mark w then (1 : ℝ) else 0)]
  rw [← Finset.sum_fiberwise S g B]
  apply Finset.sum_le_sum
  intro k hk
  let F : Finset Ω := S.filter fun u => g u = k
  by_cases hF : F.Nonempty
  · obtain ⟨w, hwF⟩ := hF
    have hwS : w ∈ S := (Finset.mem_filter.mp hwF).1
    have hgw : g w = k := (Finset.mem_filter.mp hwF).2
    have hF_eq :
        S.filter (fun u => g u = g w) = F := by
      ext u
      simp [F, hgw]
    have hFpos : 0 < (F.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨w, hwF⟩
    have hmaps : (F : Set Ω).MapsTo v (A w : Set α) := by
      intro u hu
      have huF : u ∈ F := hu
      have huS : u ∈ S := (Finset.mem_filter.mp huF).1
      have hgu : g u = k := (Finset.mem_filter.mp huF).2
      have hAu : A u = A w := hA u huS w hwS (hgu.trans hgw.symm)
      simpa [hAu] using hv u huS
    have hcount :=
      Finset.card_eq_sum_card_fiberwise (s := F) (t := A w)
        (f := v) hmaps
    have hsumcount :
        (∑ x : {x // x ∈ A w},
          (((F.filter fun u => v u = x.1).card : ℝ))) =
            (F.card : ℝ) := by
      rw [← Finset.sum_subtype (A w) (by simp)
        (fun x => ((F.filter fun u => v u = x).card : ℝ))]
      exact_mod_cast hcount.symm
    have hmass : ∑ x : {x // x ∈ A w}, p w x = 1 := by
      simp only [p, hF_eq]
      rw [← Finset.sum_div, hsumcount]
      exact div_self (ne_of_gt hFpos)
    have hnonneg : ∀ x : {x // x ∈ A w}, 0 ≤ p w x := by
      intro x
      simp only [p, hF_eq]
      exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hFpos)
    have hBconst :
        ∀ u ∈ F, B u = B w := by
      intro u huF
      have huS : u ∈ S := (Finset.mem_filter.mp huF).1
      have hgu : g u = k := (Finset.mem_filter.mp huF).2
      have hkey : g u = g w := hgu.trans hgw.symm
      have hAu : A u = A w := hA u huS w hwS hkey
      simp only [B, ell, p]
      rw [hAu]
      congr 2
      apply congrArg finite_shannon_entropy
      funext x
      simp [hkey]
    have hsone_or : (A w).card = 1 ∨ 2 ≤ (A w).card := by
      have := hpos w hwS
      omega
    have hgroup :
        ((F.filter mark).card : ℝ) ≤ (F.card : ℝ) * B w := by
      rcases hsone_or with hsone | hs
      · have hcardtype :
            Fintype.card {x // x ∈ A w} = 1 := by simpa using hsone
        letI : Unique {x // x ∈ A w} :=
          Classical.choice
            (Fintype.card_eq_one_iff_nonempty_unique.mp hcardtype)
        have hpone (x : {x // x ∈ A w}) : p w x = 1 := by
          have hx : x = default := Subsingleton.elim _ _
          subst x
          simpa using hmass
        have hell : ell w = 0 := by
          simp [ell, finite_shannon_entropy, hsone, hpone, Real.logb]
        have hBtwo : B w = 2 := by
          simp [B, hell, hsone]
        have hcardle : (F.filter mark).card ≤ F.card :=
          Finset.card_filter_le _ _
        rw [hBtwo]
        exact_mod_cast hcardle.trans
          (show F.card ≤ F.card * 2 by omega)
      · have hBnonneg : 0 ≤ B w := by
          obtain ⟨x, hx⟩ := Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_two hs)
          let x' : {x // x ∈ A w} := ⟨x, hx⟩
          have hskew :=
            entropy_loss_skew (p w) (A w).card (ell w) hs
              (by simp) hnonneg hmass rfl x'
          dsimp [B]
          exact le_trans (hnonneg x') hskew
        by_cases hM : (F.filter mark).Nonempty
        · obtain ⟨u, huM⟩ := hM
          have huF : u ∈ F := (Finset.mem_filter.mp huM).1
          have humark : mark u := (Finset.mem_filter.mp huM).2
          have huS : u ∈ S := (Finset.mem_filter.mp huF).1
          have hvuA : v u ∈ A w := by
            have hgu : g u = k := (Finset.mem_filter.mp huF).2
            have hAu : A u = A w :=
              hA u huS w hwS (hgu.trans hgw.symm)
            simpa [hAu] using hv u huS
          let x' : {x // x ∈ A w} := ⟨v u, hvuA⟩
          have hsubset :
              F.filter mark ⊆ F.filter (fun z => v z = v u) := by
            intro z hz
            have hzF : z ∈ F := (Finset.mem_filter.mp hz).1
            have hzmark : mark z := (Finset.mem_filter.mp hz).2
            have hzS : z ∈ S := (Finset.mem_filter.mp hzF).1
            have hgz : g z = k := (Finset.mem_filter.mp hzF).2
            exact Finset.mem_filter.mpr ⟨hzF,
              huniq z hzS u huS
                (hgz.trans (Finset.mem_filter.mp huF).2.symm)
                hzmark humark⟩
          have hcardle :
              ((F.filter mark).card : ℝ) ≤
                ((F.filter fun z => v z = v u).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsubset
          have hskew :=
            entropy_loss_skew (p w) (A w).card (ell w) hs
              (by simp) hnonneg hmass rfl x'
          have hcountle :
              ((F.filter fun z => v z = v u).card : ℝ) ≤
                (F.card : ℝ) * B w := by
            have hdiv :
                ((F.filter fun z => v z = v u).card : ℝ) /
                    (F.card : ℝ) ≤ B w := by
              simpa [p, x', hF_eq, B] using hskew
            simpa [mul_comm] using (div_le_iff₀ hFpos).mp hdiv
          exact hcardle.trans hcountle
        · have hzero : (F.filter mark).card = 0 := by
            rw [Finset.card_eq_zero]
            exact Finset.not_nonempty_iff_eq_empty.mp hM
          rw [hzero]
          simpa using mul_nonneg (show 0 ≤ (F.card : ℝ) by positivity) hBnonneg
    calc
      (∑ w ∈ S with g w = k, if mark w then (1 : ℝ) else 0) =
          ((F.filter mark).card : ℝ) := by simp [F]
      _ ≤ (F.card : ℝ) * B w := hgroup
      _ = ∑ u ∈ S with g u = k, B u := by
        change (F.card : ℝ) * B w = ∑ u ∈ F, B u
        calc
          (F.card : ℝ) * B w = ∑ u ∈ F, B w := by simp
          _ = ∑ u ∈ F, B u := by
            apply Finset.sum_congr rfl
            intro u hu
            exact (hBconst u hu).symm
  · have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    have hfilter : S.filter (fun u => g u = k) = ∅ := by
      simpa [F] using hFempty
    simp [hfilter]

@[blueprint "lem:finite-fiber-entropy-loss-identity-local"
  (statement := /-- In the setting of a finite family $S$ partitioned by a key $g$, let $v$ take values in a nonempty allowed set $A$ that is constant on each fiber.  If $p_w$ is the distribution of $v$ on the fiber containing $w$ and
  \[
  \ell_w=\log_2|A(w)|-H(p_w),
  \]
  then
  \[
  \sum_{w\in S}\ell_w
  =\sum_{w\in S}\log_2|A(w)|
   +\sum_{w\in S}\log_2
    \frac{|\{u\in S:g(u)=g(w),\ v(u)=v(w)\}|}
         {|\{u\in S:g(u)=g(w)\}|}.
  \] -/)
  (proof := /-- Partition all three sums into fibers of $g$ and fix a nonempty fiber $F$ with representative $w$.  The allowed set and the distribution are constant on $F$.  Regrouping the sum over $u\in F$ according to $v(u)$ gives
  \[
  \sum_{u\in F}\log_2 p_w(v(u))
  =\sum_{x\in A(w)} |\{u\in F:v(u)=x\}|\log_2p_w(x).
  \]
  Since $p_w(x)$ is the displayed cardinality divided by $|F|$, the right-hand side is $-|F|H(p_w)$.  Hence the sum of the losses on $F$ equals $|F|\log_2|A(w)|$ plus the sum of the logarithmic fiber ratios.  Empty fibers contribute zero, and summing the fiber identities proves the formula. -/)
  (title := /-- Fiberwise expansion of entropy loss -/)
  (latexEnv := "lemma")]
lemma finite_fiber_entropy_loss_identity_local
    {Ω κ α : Type*} [Fintype Ω] [Fintype κ] [Fintype α]
    [DecidableEq κ] [DecidableEq α]
    (S : Finset Ω) (g : Ω → κ) (v : Ω → α)
    (A : Ω → Finset α)
    (hA : ∀ u ∈ S, ∀ w ∈ S, g u = g w → A u = A w)
    (hv : ∀ u ∈ S, v u ∈ A u)
    (hpos : ∀ u ∈ S, 1 ≤ (A u).card) :
    let p := fun (w : Ω) (x : {x // x ∈ A w}) =>
      (((S.filter fun u => g u = g w).filter fun u => v u = x.1).card : ℝ) /
        ((S.filter fun u => g u = g w).card : ℝ)
    let ell := fun w =>
      Real.logb 2 ((A w).card : ℝ) - finite_shannon_entropy (p w)
    let q := fun w =>
      (((S.filter fun u => g u = g w).filter fun u => v u = v w).card : ℝ) /
        ((S.filter fun u => g u = g w).card : ℝ)
    (∑ w ∈ S, ell w) =
      (∑ w ∈ S, Real.logb 2 ((A w).card : ℝ)) +
        ∑ w ∈ S, Real.logb 2 (q w) := by
  classical
  dsimp only
  let p := fun (w : Ω) (x : {x // x ∈ A w}) =>
    (((S.filter fun u => g u = g w).filter fun u => v u = x.1).card : ℝ) /
      ((S.filter fun u => g u = g w).card : ℝ)
  let ell := fun w =>
    Real.logb 2 ((A w).card : ℝ) - finite_shannon_entropy (p w)
  let q := fun w =>
    (((S.filter fun u => g u = g w).filter fun u => v u = v w).card : ℝ) /
      ((S.filter fun u => g u = g w).card : ℝ)
  rw [← Finset.sum_fiberwise S g ell]
  rw [← Finset.sum_fiberwise S g
    (fun w => Real.logb 2 ((A w).card : ℝ))]
  rw [← Finset.sum_fiberwise S g (fun w => Real.logb 2 (q w))]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  let F : Finset Ω := S.filter fun u => g u = k
  by_cases hF : F.Nonempty
  · obtain ⟨w, hwF⟩ := hF
    have hwS : w ∈ S := (Finset.mem_filter.mp hwF).1
    have hgw : g w = k := (Finset.mem_filter.mp hwF).2
    have hF_eq :
        S.filter (fun u => g u = g w) = F := by
      ext u
      simp [F, hgw]
    have hFpos : 0 < (F.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨w, hwF⟩
    have hellconst : ∀ u ∈ F, ell u = ell w := by
      intro u huF
      have huS : u ∈ S := (Finset.mem_filter.mp huF).1
      have hgu : g u = k := (Finset.mem_filter.mp huF).2
      have hkey : g u = g w := hgu.trans hgw.symm
      have hAu : A u = A w := hA u huS w hwS hkey
      simp only [ell, p]
      rw [hAu]
      congr 2
      funext x
      simp [hkey]
    have hlogconst :
        ∀ u ∈ F,
          Real.logb 2 ((A u).card : ℝ) =
            Real.logb 2 ((A w).card : ℝ) := by
      intro u huF
      have huS : u ∈ S := (Finset.mem_filter.mp huF).1
      have hgu : g u = k := (Finset.mem_filter.mp huF).2
      rw [hA u huS w hwS (hgu.trans hgw.symm)]
    have hallowed :
        ∀ u ∈ F, v u ∈ A w := by
      intro u huF
      have huS : u ∈ S := (Finset.mem_filter.mp huF).1
      have hgu : g u = k := (Finset.mem_filter.mp huF).2
      have hAu : A u = A w := hA u huS w hwS (hgu.trans hgw.symm)
      simpa [hAu] using hv u huS
    have hq (u : Ω) (huF : u ∈ F) :
        q u = p w ⟨v u, hallowed u huF⟩ := by
      have hgu : g u = k := (Finset.mem_filter.mp huF).2
      have hkey : g u = g w := hgu.trans hgw.symm
      simp [q, p, hkey]
    obtain ⟨a₀, ha₀⟩ :=
      Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_one (hpos w hwS))
    let vv : Ω → {x // x ∈ A w} := fun u =>
      if hu : u ∈ F then ⟨v u, hallowed u hu⟩ else ⟨a₀, ha₀⟩
    have hlogsum :
        (∑ u ∈ F, Real.logb 2 (q u)) =
          ∑ x : {x // x ∈ A w},
            ((F.filter fun u => v u = x.1).card : ℝ) *
              Real.logb 2 (p w x) := by
      rw [← Finset.sum_fiberwise F vv (fun u => Real.logb 2 (q u))]
      apply Finset.sum_congr rfl
      intro x hx
      have hfilter :
          F.filter (fun u => vv u = x) =
            F.filter (fun u => v u = x.1) := by
        ext u
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨huF, huv⟩
          refine ⟨huF, ?_⟩
          have := congrArg Subtype.val huv
          simpa [vv, huF] using this
        · rintro ⟨huF, huv⟩
          refine ⟨huF, ?_⟩
          apply Subtype.ext
          simpa [vv, huF] using huv
      rw [hfilter]
      calc
        (∑ u ∈ F with v u = x, Real.logb 2 (q u)) =
            ∑ u ∈ F with v u = x,
              Real.logb 2 (p w x) := by
                apply Finset.sum_congr rfl
                intro u hu
                have huF : u ∈ F := (Finset.mem_filter.mp hu).1
                have huv : v u = x := (Finset.mem_filter.mp hu).2
                rw [hq u huF]
                congr
        _ = ((F.filter fun u => v u = x).card : ℝ) *
              Real.logb 2 (p w x) := by simp
    have hscale :
        (F.card : ℝ) * finite_shannon_entropy (p w) =
          -(∑ u ∈ F, Real.logb 2 (q u)) := by
      rw [hlogsum, finite_shannon_entropy, Finset.mul_sum,
        ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      simp only [p, hF_eq]
      field_simp [ne_of_gt hFpos]
    change (∑ u ∈ F, ell u) =
      (∑ u ∈ F, Real.logb 2 ((A u).card : ℝ)) +
        ∑ u ∈ F, Real.logb 2 (q u)
    calc
      (∑ u ∈ F, ell u) =
          (F.card : ℝ) * ell w := by
            calc
              (∑ u ∈ F, ell u) = ∑ u ∈ F, ell w := by
                apply Finset.sum_congr rfl
                intro u hu
                exact hellconst u hu
              _ = (F.card : ℝ) * ell w := by simp
      _ = (F.card : ℝ) * Real.logb 2 ((A w).card : ℝ) -
          (F.card : ℝ) * finite_shannon_entropy (p w) := by
            dsimp [ell]
            ring
      _ = (F.card : ℝ) * Real.logb 2 ((A w).card : ℝ) +
          ∑ u ∈ F, Real.logb 2 (q u) := by rw [hscale]; ring
      _ = (∑ u ∈ F, Real.logb 2 ((A u).card : ℝ)) +
          ∑ u ∈ F, Real.logb 2 (q u) := by
            congr 1
            calc
              (F.card : ℝ) * Real.logb 2 ((A w).card : ℝ) =
                  ∑ u ∈ F, Real.logb 2 ((A w).card : ℝ) := by simp
              _ = ∑ u ∈ F, Real.logb 2 ((A u).card : ℝ) := by
                apply Finset.sum_congr rfl
                intro u hu
                exact (hlogconst u hu).symm
  · have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    have hfilter : S.filter (fun u => g u = k) = ∅ := by
      simpa [F] using hFempty
    simp [hfilter]

@[blueprint "lem:cycle-factor-entropy-certificate-exists"
  (statement := /-- Let $n,d\in\mathbb N$ with $d\geq2$, and let $G$ be a directed $d$-regular graph on $[n]$.  Then there exists a real number $L$ that is an entropy certificate for the uniform distribution on the cycle-factors of $G$. -/)
  (proof := /-- Let $\mathcal C$ be the set of cycle-factors of $G$.  By \cref{lem:regular-cycle-factor-count-lower-bound}, it is nonempty and
  \[
  (d/e)^n\leq |\mathcal C|.
  \]
  Fix an ordering $\tau$ and a vertex $i$, and partition $\mathcal C$ according to the images of the vertices preceding $i$.  In the fiber containing $\sigma$, the possible values of $\sigma(i)$ form the set of remaining out-neighbours; write its cardinality as $s(i,\sigma,\tau)$ and the corresponding entropy loss as $\ell(i,\sigma,\tau)$.  The fiberwise entropy identity in \cref{lem:finite-fiber-entropy-loss-identity-local} expands the sum of these losses into the support logarithms and the logarithms of successive fiber-cardinality ratios.  The latter telescope, while \cref{lem:remaining-neighbor-rank-uniform} makes $s(i,\sigma,\tau)$ uniform on $\{1,\ldots,d\}$ as $\tau$ varies.  Consequently the averaged total loss is
  \[
  A_0=\frac nd\log_2(d!)-\log_2|\mathcal C|.
  \]
  Taking logarithms in the lower bound for $|\mathcal C|$ and applying \cref{lem:factorial-log-upper-local} gives
  \[
  A_0\leq \frac n d\log_2(ed).
  \]

  Say that $i$ closes a cycle of $\sigma$ when it is maximal in that cycle with respect to $\tau$.  By \cref{lem:permutation-cycle-closing-count-local}, the number of closing vertices is exactly the number of cycles.  Moreover, \cref{lem:permutation-cycle-closing-value-unique-local} shows that within any conditioning fiber all closing members have the same value at $i$.  Thus \cref{lem:finite-fiber-entropy-mark-bound-local} bounds the number of closing members of each fiber by the sum of $2/s(i,\sigma,\tau)$ and the local losses.  Summing over $i$, $\sigma$, and $\tau$, and using \cref{lem:remaining-neighbor-rank-uniform} again, yields
  \[
  \mathbb E|\sigma|\leq\frac{2n}{d}H_d+A_0.
  \]
  Finally set $L=\max\{0,A_0\}$.  The preceding bound remains valid with $L$ in place of $A_0$; the displayed upper bound for $A_0$, together with the nonnegativity of $n\log_2(ed)/d$, gives $0\leq L\leq n\log_2(ed)/d$.  These are precisely the three entropy-certificate inequalities. -/)
  (title := /-- Existence of the entropy-loss certificate -/)
  (latexEnv := "lemma")]
lemma cycle_factor_entropy_certificate_exists {n d : ℕ} (G : Digraph (Fin n))
    (hreg : directed_regular G d) (hd : 2 ≤ d) :
    ∃ L : ℝ, cycle_factor_entropy_certificate G d L := by
  set_option maxHeartbeats 2000000 in {
  classical
  let C : Finset (Equiv.Perm (Fin n)) := directed_cycle_factors G
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hd)
  have hlower :=
    regular_cycle_factor_count_lower_bound G hreg (show 1 ≤ d by omega)
  have hCpos : 0 < (C.card : ℝ) := by
    have hbase : 0 < (d : ℝ) / Real.exp 1 :=
      div_pos hdpos (Real.exp_pos 1)
    have : 0 < ((d : ℝ) / Real.exp 1) ^ n := pow_pos hbase n
    exact lt_of_lt_of_le this (by simpa [C] using hlower)
  have hCnonempty : C.Nonempty := by
    exact Finset.card_pos.mp (by exact_mod_cast hCpos)
  let key (τ : Equiv.Perm (Fin n)) (i : Fin n)
      (σ : Equiv.Perm (Fin n)) : Fin n → Option (Fin n) :=
    fun x => if (τ.symm x).val < (τ.symm i).val then some (σ x) else none
  let R (τ : Equiv.Perm (Fin n)) (i : Fin n)
      (σ : Equiv.Perm (Fin n)) : Finset (Fin n) :=
    Finset.univ.filter fun j =>
      G.Adj i j ∧ ¬ ((τ.symm (σ.symm j)).val < (τ.symm i).val)
  let closes (τ : Equiv.Perm (Fin n)) (i : Fin n)
      (σ : Equiv.Perm (Fin n)) : Prop :=
    ∀ x : Fin n, σ.SameCycle i x →
      (τ.symm x).val ≤ (τ.symm i).val
  have hkey_agree (τ : Equiv.Perm (Fin n)) (i : Fin n)
      (σ₁ σ₂ : Equiv.Perm (Fin n))
      (hkey : key τ i σ₁ = key τ i σ₂) :
      ∀ x : Fin n, (τ.symm x).val < (τ.symm i).val →
        σ₁ x = σ₂ x := by
    intro x hx
    have h := congrFun hkey x
    change
      (if (τ.symm x).val < (τ.symm i).val then some (σ₁ x) else none) =
        if (τ.symm x).val < (τ.symm i).val then some (σ₂ x) else none at h
    rw [if_pos hx, if_pos hx] at h
    exact Option.some.inj h
  have hRconst (τ : Equiv.Perm (Fin n)) (i : Fin n)
      (σ₁ σ₂ : Equiv.Perm (Fin n))
      (hkey : key τ i σ₁ = key τ i σ₂) :
      R τ i σ₁ = R τ i σ₂ := by
    ext j
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hmem
      refine ⟨hmem.1, ?_⟩
      intro h₂
      apply hmem.2
      let x : Fin n := σ₂.symm j
      have hx : (τ.symm x).val < (τ.symm i).val := by simpa [x] using h₂
      have heq := hkey_agree τ i σ₁ σ₂ hkey x hx
      have hσ₁x : σ₁ x = j := by
        rw [heq]
        simp [x]
      have hx' : σ₁.symm j = x := by
        apply σ₁.injective
        simpa using hσ₁x.symm
      simpa [hx'] using hx
    · intro hmem
      refine ⟨hmem.1, ?_⟩
      intro h₁
      apply hmem.2
      let x : Fin n := σ₁.symm j
      have hx : (τ.symm x).val < (τ.symm i).val := by simpa [x] using h₁
      have heq := hkey_agree τ i σ₁ σ₂ hkey x hx
      have hσ₂x : σ₂ x = j := by
        rw [← heq]
        simp [x]
      have hx' : σ₂.symm j = x := by
        apply σ₂.injective
        simpa using hσ₂x.symm
      simpa [hx'] using hx
  have hvR (τ : Equiv.Perm (Fin n)) (i : Fin n)
      (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ C) :
      σ i ∈ R τ i σ := by
    have hadj : G.Adj i (σ i) := by
      have hall : ∀ v : Fin n, G.Adj v (σ v) := by
        simpa [C, directed_cycle_factors] using hσ
      exact hall i
    simp [R, hadj]
  have hRpos (τ : Equiv.Perm (Fin n)) (i : Fin n)
      (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ C) :
      1 ≤ (R τ i σ).card :=
    Finset.card_pos.mpr ⟨σ i, hvR τ i σ hσ⟩
  have hclose_unique (τ : Equiv.Perm (Fin n)) (i : Fin n)
      (σ₁ : Equiv.Perm (Fin n)) (hσ₁ : σ₁ ∈ C)
      (σ₂ : Equiv.Perm (Fin n)) (hσ₂ : σ₂ ∈ C)
      (hkey : key τ i σ₁ = key τ i σ₂)
      (hc₁ : closes τ i σ₁) (hc₂ : closes τ i σ₂) :
      σ₁ i = σ₂ i :=
    permutation_cycle_closing_value_unique_local σ₁ σ₂ τ i
      (hkey_agree τ i σ₁ σ₂ hkey) hc₁ hc₂
  let p (τ : Equiv.Perm (Fin n)) (i : Fin n)
      (σ : Equiv.Perm (Fin n)) (x : {x // x ∈ R τ i σ}) : ℝ :=
    (((C.filter fun u => key τ i u = key τ i σ).filter
      fun u => u i = x.1).card : ℝ) /
      ((C.filter fun u => key τ i u = key τ i σ).card : ℝ)
  let ell (τ : Equiv.Perm (Fin n)) (i : Fin n)
      (σ : Equiv.Perm (Fin n)) : ℝ :=
    Real.logb 2 ((R τ i σ).card : ℝ) -
      finite_shannon_entropy (p τ i σ)
  let q (τ : Equiv.Perm (Fin n)) (i : Fin n)
      (σ : Equiv.Perm (Fin n)) : ℝ :=
    (((C.filter fun u => key τ i u = key τ i σ).filter
      fun u => u i = σ i).card : ℝ) /
      ((C.filter fun u => key τ i u = key τ i σ).card : ℝ)
  have hmark (τ : Equiv.Perm (Fin n)) (i : Fin n) :
      (∑ σ ∈ C, if closes τ i σ then (1 : ℝ) else 0) ≤
        ∑ σ ∈ C,
          ((2 : ℝ) / ((R τ i σ).card : ℝ) + ell τ i σ) := by
    simpa [p, ell] using
      (finite_fiber_entropy_mark_bound_local C (key τ i)
        (fun σ : Equiv.Perm (Fin n) => σ i) (R τ i) (closes τ i)
        (fun u hu w hw h => hRconst τ i u w h)
        (fun u hu => hvR τ i u hu)
        (fun u hu => hRpos τ i u hu)
        (fun u hu w hw h hc₁ hc₂ =>
          hclose_unique τ i u hu w hw h hc₁ hc₂))
  have hloss (τ : Equiv.Perm (Fin n)) (i : Fin n) :
      (∑ σ ∈ C, ell τ i σ) =
        (∑ σ ∈ C, Real.logb 2 ((R τ i σ).card : ℝ)) +
          ∑ σ ∈ C, Real.logb 2 (q τ i σ) := by
    simpa [p, ell, q] using
      (finite_fiber_entropy_loss_identity_local C (key τ i)
        (fun σ : Equiv.Perm (Fin n) => σ i) (R τ i)
        (fun u hu w hw h => hRconst τ i u w h)
        (fun u hu => hvR τ i u hu)
        (fun u hu => hRpos τ i u hu))
  have hRcard (τ : Equiv.Perm (Fin n)) (i : Fin n)
      (σ : Equiv.Perm (Fin n)) :
      (R τ i σ).card = remaining_neighbor_count G σ τ i := by
    rfl
  have hRle (τ : Equiv.Perm (Fin n)) (i : Fin n)
      (σ : Equiv.Perm (Fin n)) :
      (R τ i σ).card ≤ d := by
    calc
      (R τ i σ).card ≤
          (Finset.univ.filter fun j : Fin n => G.Adj i j).card := by
            apply Finset.card_le_card
            intro j hj
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_univ j, (Finset.mem_filter.mp hj).2.1⟩
      _ = d := hreg.1 i
  have hrank_sum (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ C)
      (i : Fin n) (f : ℕ → ℝ) :
      (∑ τ : Equiv.Perm (Fin n), f (R τ i σ).card) =
        ((Nat.factorial n : ℝ) / (d : ℝ)) *
          ∑ t ∈ Finset.Icc 1 d, f t := by
    have hrange (τ : Equiv.Perm (Fin n)) :
        (R τ i σ).card ∈ Finset.Icc 1 d :=
      Finset.mem_Icc.mpr ⟨hRpos τ i σ hσ, hRle τ i σ⟩
    calc
      (∑ τ : Equiv.Perm (Fin n), f (R τ i σ).card) =
          ∑ τ ∈ (Finset.univ.filter fun τ : Equiv.Perm (Fin n) =>
            (R τ i σ).card ∈ Finset.Icc 1 d),
              f (R τ i σ).card := by
                apply Finset.sum_congr
                · ext τ
                  simp only [Finset.mem_univ, Finset.mem_filter, true_and]
                  exact ⟨fun _ => hrange τ, fun _ => True.intro⟩
                · intro τ hτ
                  rfl
      _ = ∑ t ∈ Finset.Icc 1 d,
          ∑ τ ∈ (Finset.univ.filter fun τ : Equiv.Perm (Fin n) =>
            (R τ i σ).card = t), f (R τ i σ).card := by
              symm
              exact Finset.sum_fiberwise_eq_sum_filter
                (Finset.univ : Finset (Equiv.Perm (Fin n)))
                (Finset.Icc 1 d) (fun τ => (R τ i σ).card)
                (fun τ => f (R τ i σ).card)
      _ = ∑ t ∈ Finset.Icc 1 d,
          ((Nat.factorial n : ℝ) / (d : ℝ)) * f t := by
            apply Finset.sum_congr rfl
            intro t ht
            have ht₁ : 1 ≤ t := (Finset.mem_Icc.mp ht).1
            have htd : t ≤ d := (Finset.mem_Icc.mp ht).2
            have hc :=
              remaining_neighbor_rank_uniform G σ hreg
                (by simpa [C] using hσ) i t ht₁ htd
            have hc' :
                ((Finset.univ.filter fun τ : Equiv.Perm (Fin n) =>
                  (R τ i σ).card = t).card : ℝ) =
                    (Nat.factorial n : ℝ) / (d : ℝ) := by
              rw [eq_div_iff (ne_of_gt hdpos)]
              exact_mod_cast (by simpa [hRcard] using hc)
            calc
              (∑ x ∈ (Finset.univ.filter fun τ : Equiv.Perm (Fin n) =>
                    (R τ i σ).card = t), f (R x i σ).card) =
                  ∑ x ∈ (Finset.univ.filter fun τ : Equiv.Perm (Fin n) =>
                    (R τ i σ).card = t), f t := by
                      apply Finset.sum_congr rfl
                      intro x hx
                      rw [(Finset.mem_filter.mp hx).2]
              _ = ((Finset.univ.filter fun τ : Equiv.Perm (Fin n) =>
                    (R τ i σ).card = t).card : ℝ) * f t := by simp
              _ = ((Nat.factorial n : ℝ) / (d : ℝ)) * f t := by rw [hc']
      _ = ((Nat.factorial n : ℝ) / (d : ℝ)) *
          ∑ t ∈ Finset.Icc 1 d, f t := by
            rw [Finset.mul_sum]
  have hsumlog (m : ℕ) :
      (∑ t ∈ Finset.Icc 1 m, Real.logb 2 (t : ℝ)) =
        Real.logb 2 (Nat.factorial m : ℝ) := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ih,
          Nat.factorial_succ, Nat.cast_mul,
          Real.logb_mul (by positivity) (by positivity)]
        ring
  have htel (a : ℕ → ℝ) (m : ℕ) :
      (∑ k : Fin m, (a (k.val + 1) - a k.val)) = a m - a 0 := by
    induction m generalizing a with
    | zero => simp
    | succ m ih =>
        rw [Fin.sum_univ_succ]
        have hi := ih (fun k => a (k + 1))
        have hi' :
            (∑ i : Fin m, (a (i.succ.val + 1) - a i.succ.val)) =
              a (m + 1) - a 1 := by
          simpa [Nat.add_assoc] using hi
        rw [hi']
        simp
  let F (τ : Equiv.Perm (Fin n)) (k : ℕ)
      (σ : Equiv.Perm (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
    C.filter fun u =>
      ∀ x : Fin n, (τ.symm x).val < k → u x = σ x
  have hFpos (τ : Equiv.Perm (Fin n)) (k : ℕ)
      (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ C) :
      0 < ((F τ k σ).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨σ, by simp [F, hσ]⟩
  have hFzero (τ : Equiv.Perm (Fin n))
      (σ : Equiv.Perm (Fin n)) :
      F τ 0 σ = C := by
    ext u
    simp [F]
  have hFn (τ : Equiv.Perm (Fin n))
      (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ C) :
      F τ n σ = {σ} := by
    ext u
    constructor
    · intro hu
      have hu' := Finset.mem_filter.mp hu
      have heq : u = σ := by
        apply Equiv.ext
        intro x
        exact hu'.2 x (τ.symm x).isLt
      simpa [heq]
    · intro hu
      have heq : u = σ := Finset.mem_singleton.mp hu
      subst u
      simp [F, hσ]
  have hqstep (τ : Equiv.Perm (Fin n)) (k : Fin n)
      (σ : Equiv.Perm (Fin n)) :
      q τ (τ k) σ =
        ((F τ (k.val + 1) σ).card : ℝ) / ((F τ k.val σ).card : ℝ) := by
    have hcurrent :
        C.filter (fun u => key τ (τ k) u = key τ (τ k) σ) =
          F τ k.val σ := by
      ext u
      simp only [F, Finset.mem_filter]
      constructor
      · rintro ⟨huC, hkey⟩
        refine ⟨huC, ?_⟩
        intro x hx
        apply hkey_agree τ (τ k) u σ hkey x
        simpa using hx
      · rintro ⟨huC, hu⟩
        refine ⟨huC, ?_⟩
        funext x
        by_cases hx : (τ.symm x).val < (τ.symm (τ k)).val
        · have hx' : (τ.symm x).val < k.val := by simpa using hx
          simp [key, hx, hu x hx']
        · simp only [key]
          rw [if_neg hx, if_neg hx]
    have hnext :
        (C.filter (fun u => key τ (τ k) u = key τ (τ k) σ)).filter
            (fun u => u (τ k) = σ (τ k)) =
          F τ (k.val + 1) σ := by
      ext u
      simp only [F, Finset.mem_filter]
      constructor
      · rintro ⟨⟨huC, hkey⟩, hui⟩
        refine ⟨huC, ?_⟩
        intro x hx
        by_cases hlt : (τ.symm x).val < k.val
        · exact hkey_agree τ (τ k) u σ hkey x (by simpa using hlt)
        · have heqval : (τ.symm x).val = k.val := by omega
          have heqx : x = τ k := by
            apply τ.symm.injective
            apply Fin.ext
            simpa using heqval
          simpa [heqx] using hui
      · rintro ⟨huC, hu⟩
        have hkey :
            key τ (τ k) u = key τ (τ k) σ := by
          funext x
          by_cases hx : (τ.symm x).val < (τ.symm (τ k)).val
          · have hx0 : (τ.symm x).val < k.val := by simpa using hx
            have hx' : (τ.symm x).val < k.val + 1 := by omega
            simp [key, hx, hu x hx']
          · simp only [key]
            rw [if_neg hx, if_neg hx]
        refine ⟨⟨huC, hkey⟩, ?_⟩
        apply hu (τ k)
        simp
    rw [hcurrent] at hnext
    simp only [q]
    rw [hcurrent, hnext]
  have hqsum (τ : Equiv.Perm (Fin n))
      (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ C) :
      (∑ i : Fin n, Real.logb 2 (q τ i σ)) =
        -Real.logb 2 (C.card : ℝ) := by
    rw [← Equiv.sum_comp τ]
    calc
      (∑ k : Fin n, Real.logb 2 (q τ (τ k) σ)) =
          ∑ k : Fin n,
            (Real.logb 2 ((F τ (k.val + 1) σ).card : ℝ) -
              Real.logb 2 ((F τ k.val σ).card : ℝ)) := by
                apply Finset.sum_congr rfl
                intro k hk
                rw [hqstep]
                simp only [Real.logb]
                rw [Real.log_div
                  (ne_of_gt (hFpos τ (k.val + 1) σ hσ))
                  (ne_of_gt (hFpos τ k.val σ hσ))]
                ring
      _ = Real.logb 2 ((F τ n σ).card : ℝ) -
          Real.logb 2 ((F τ 0 σ).card : ℝ) :=
            htel (fun k => Real.logb 2 ((F τ k σ).card : ℝ)) n
      _ = -Real.logb 2 (C.card : ℝ) := by
        rw [hFn τ σ hσ, hFzero]
        simp
  let A₀ : ℝ :=
    (n : ℝ) / (d : ℝ) * Real.logb 2 (Nat.factorial d : ℝ) -
      Real.logb 2 (C.card : ℝ)
  have htotal_mark :
      (∑ τ : Equiv.Perm (Fin n), ∑ i : Fin n,
        ∑ σ ∈ C, if closes τ i σ then (1 : ℝ) else 0) ≤
      ∑ τ : Equiv.Perm (Fin n), ∑ i : Fin n,
        ∑ σ ∈ C,
          ((2 : ℝ) / ((R τ i σ).card : ℝ) + ell τ i σ) := by
    apply Finset.sum_le_sum
    intro τ hτ
    apply Finset.sum_le_sum
    intro i hi
    exact hmark τ i
  have hperτ (τ : Equiv.Perm (Fin n)) :
      (∑ i : Fin n, ∑ σ ∈ C,
        if closes τ i σ then (1 : ℝ) else 0) =
      ∑ σ ∈ C, (permutation_cycle_count σ : ℝ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro σ hσ
    exact_mod_cast permutation_cycle_closing_count_local σ τ
  have hleft :
      (∑ τ : Equiv.Perm (Fin n), ∑ i : Fin n,
        ∑ σ ∈ C, if closes τ i σ then (1 : ℝ) else 0) =
      (Nat.factorial n : ℝ) *
        ∑ σ ∈ C, (permutation_cycle_count σ : ℝ) := by
    simp_rw [hperτ]
    simp [Fintype.card_perm]
  have htwo_i (i : Fin n) :
      (∑ τ : Equiv.Perm (Fin n), ∑ σ ∈ C,
        (2 : ℝ) / ((R τ i σ).card : ℝ)) =
      (C.card : ℝ) * ((Nat.factorial n : ℝ) / (d : ℝ)) *
        (2 * harmonic_sum d) := by
    rw [Finset.sum_comm]
    calc
      (∑ σ ∈ C, ∑ τ : Equiv.Perm (Fin n),
          (2 : ℝ) / ((R τ i σ).card : ℝ)) =
          ∑ σ ∈ C,
            (((Nat.factorial n : ℝ) / (d : ℝ)) *
              ∑ t ∈ Finset.Icc 1 d, (2 : ℝ) / (t : ℝ)) := by
                apply Finset.sum_congr rfl
                intro σ hσ
                exact hrank_sum σ hσ i (fun t => (2 : ℝ) / (t : ℝ))
      _ = ∑ σ ∈ C,
          (((Nat.factorial n : ℝ) / (d : ℝ)) *
            (2 * harmonic_sum d)) := by
              apply Finset.sum_congr rfl
              intro σ hσ
              congr 1
              unfold harmonic_sum
              simp only [div_eq_mul_inv, Finset.mul_sum]
      _ = (C.card : ℝ) * ((Nat.factorial n : ℝ) / (d : ℝ)) *
          (2 * harmonic_sum d) := by simp; ring
  have htwo :
      (∑ τ : Equiv.Perm (Fin n), ∑ i : Fin n,
        ∑ σ ∈ C, (2 : ℝ) / ((R τ i σ).card : ℝ)) =
      (n : ℝ) * (C.card : ℝ) *
        ((Nat.factorial n : ℝ) / (d : ℝ)) *
          (2 * harmonic_sum d) := by
    rw [Finset.sum_comm]
    simp_rw [htwo_i]
    simp
    ring
  have hlogR_i (i : Fin n) :
      (∑ τ : Equiv.Perm (Fin n), ∑ σ ∈ C,
        Real.logb 2 ((R τ i σ).card : ℝ)) =
      (C.card : ℝ) * ((Nat.factorial n : ℝ) / (d : ℝ)) *
        Real.logb 2 (Nat.factorial d : ℝ) := by
    rw [Finset.sum_comm]
    calc
      (∑ σ ∈ C, ∑ τ : Equiv.Perm (Fin n),
          Real.logb 2 ((R τ i σ).card : ℝ)) =
          ∑ σ ∈ C,
            (((Nat.factorial n : ℝ) / (d : ℝ)) *
              Real.logb 2 (Nat.factorial d : ℝ)) := by
                apply Finset.sum_congr rfl
                intro σ hσ
                rw [← hsumlog d]
                exact hrank_sum σ hσ i
                  (fun t => Real.logb 2 (t : ℝ))
      _ = (C.card : ℝ) * ((Nat.factorial n : ℝ) / (d : ℝ)) *
          Real.logb 2 (Nat.factorial d : ℝ) := by simp; ring
  have hlogR :
      (∑ τ : Equiv.Perm (Fin n), ∑ i : Fin n,
        ∑ σ ∈ C, Real.logb 2 ((R τ i σ).card : ℝ)) =
      (n : ℝ) * (C.card : ℝ) *
        ((Nat.factorial n : ℝ) / (d : ℝ)) *
          Real.logb 2 (Nat.factorial d : ℝ) := by
    rw [Finset.sum_comm]
    simp_rw [hlogR_i]
    simp
    ring
  have hqτ (τ : Equiv.Perm (Fin n)) :
      (∑ i : Fin n, ∑ σ ∈ C, Real.logb 2 (q τ i σ)) =
      (C.card : ℝ) * (-Real.logb 2 (C.card : ℝ)) := by
    rw [Finset.sum_comm]
    calc
      (∑ σ ∈ C, ∑ i : Fin n, Real.logb 2 (q τ i σ)) =
          ∑ σ ∈ C, (-Real.logb 2 (C.card : ℝ)) := by
            apply Finset.sum_congr rfl
            intro σ hσ
            exact hqsum τ σ hσ
      _ = (C.card : ℝ) * (-Real.logb 2 (C.card : ℝ)) := by simp
  have hqtotal :
      (∑ τ : Equiv.Perm (Fin n), ∑ i : Fin n,
        ∑ σ ∈ C, Real.logb 2 (q τ i σ)) =
      (Nat.factorial n : ℝ) * (C.card : ℝ) *
        (-Real.logb 2 (C.card : ℝ)) := by
    simp_rw [hqτ]
    simp [Fintype.card_perm]
    ring
  have helltotal :
      (∑ τ : Equiv.Perm (Fin n), ∑ i : Fin n,
        ∑ σ ∈ C, ell τ i σ) =
      (C.card : ℝ) * (Nat.factorial n : ℝ) * A₀ := by
    calc
      (∑ τ : Equiv.Perm (Fin n), ∑ i : Fin n,
          ∑ σ ∈ C, ell τ i σ) =
          (∑ τ : Equiv.Perm (Fin n), ∑ i : Fin n,
            ∑ σ ∈ C, Real.logb 2 ((R τ i σ).card : ℝ)) +
          (∑ τ : Equiv.Perm (Fin n), ∑ i : Fin n,
            ∑ σ ∈ C, Real.logb 2 (q τ i σ)) := by
              simp_rw [hloss, Finset.sum_add_distrib]
      _ = (C.card : ℝ) * (Nat.factorial n : ℝ) * A₀ := by
        rw [hlogR, hqtotal]
        dsimp [A₀]
        field_simp [ne_of_gt hdpos]
        ring
  have hright :
      (∑ τ : Equiv.Perm (Fin n), ∑ i : Fin n,
        ∑ σ ∈ C,
          ((2 : ℝ) / ((R τ i σ).card : ℝ) + ell τ i σ)) =
      (C.card : ℝ) * (Nat.factorial n : ℝ) *
        ((2 * (n : ℝ) / (d : ℝ)) * harmonic_sum d + A₀) := by
    calc
      (∑ τ : Equiv.Perm (Fin n), ∑ i : Fin n,
          ∑ σ ∈ C,
            ((2 : ℝ) / ((R τ i σ).card : ℝ) + ell τ i σ)) =
          (∑ τ : Equiv.Perm (Fin n), ∑ i : Fin n,
            ∑ σ ∈ C, (2 : ℝ) / ((R τ i σ).card : ℝ)) +
          (∑ τ : Equiv.Perm (Fin n), ∑ i : Fin n,
            ∑ σ ∈ C, ell τ i σ) := by
              simp_rw [Finset.sum_add_distrib]
      _ = (C.card : ℝ) * (Nat.factorial n : ℝ) *
          ((2 * (n : ℝ) / (d : ℝ)) * harmonic_sum d + A₀) := by
            rw [htwo, helltotal]
            ring
  have hscaled :
      (Nat.factorial n : ℝ) *
          (∑ σ ∈ C, (permutation_cycle_count σ : ℝ)) ≤
        (C.card : ℝ) * (Nat.factorial n : ℝ) *
          ((2 * (n : ℝ) / (d : ℝ)) * harmonic_sum d + A₀) := by
    rw [← hleft, ← hright]
    exact htotal_mark
  have hfactpos : 0 < (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hcore :
      uniform_expected_cycle_count G ≤
        (2 * (n : ℝ) / (d : ℝ)) * harmonic_sum d + A₀ := by
    have hsum :
        (∑ σ ∈ C, (permutation_cycle_count σ : ℝ)) ≤
          (C.card : ℝ) *
            ((2 * (n : ℝ) / (d : ℝ)) * harmonic_sum d + A₀) := by
      exact le_of_mul_le_mul_left
        (by simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled) hfactpos
    unfold uniform_expected_cycle_count
    rw [show directed_cycle_factors G = C by rfl]
    exact (div_le_iff₀ hCpos).2 (by simpa [mul_comm] using hsum)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbasepos : 0 < (d : ℝ) / Real.exp 1 :=
    div_pos hdpos (Real.exp_pos 1)
  have hlogC :
      (n : ℝ) * Real.logb 2 ((d : ℝ) / Real.exp 1) ≤
        Real.logb 2 (C.card : ℝ) := by
    have hlog :=
      Real.log_le_log (pow_pos hbasepos n) (by simpa [C] using hlower)
    rw [Real.log_pow] at hlog
    unfold Real.logb
    have hh := (div_le_div_iff_of_pos_right hlog2pos).2 hlog
    simpa [C, mul_div_assoc] using hh
  have hfact :=
    factorial_log_upper_local d (show 1 ≤ d by omega)
  have hfactb :
      Real.logb 2 (Nat.factorial d : ℝ) ≤
        (((d : ℝ) + 1) * Real.log (d : ℝ) - (d : ℝ) + 1) /
          Real.log 2 := by
    unfold Real.logb
    exact (div_le_div_iff_of_pos_right hlog2pos).2 hfact
  have hAupper :
      A₀ ≤ (n : ℝ) * Real.logb 2 (Real.exp 1 * (d : ℝ)) / (d : ℝ) := by
    calc
      A₀ ≤ (n : ℝ) / (d : ℝ) *
            ((((d : ℝ) + 1) * Real.log (d : ℝ) - (d : ℝ) + 1) /
              Real.log 2) -
          (n : ℝ) * Real.logb 2 ((d : ℝ) / Real.exp 1) := by
            dsimp [A₀]
            exact sub_le_sub
              (mul_le_mul_of_nonneg_left hfactb
                (div_nonneg (Nat.cast_nonneg n) (le_of_lt hdpos)))
              hlogC
      _ = (n : ℝ) * Real.logb 2 (Real.exp 1 * (d : ℝ)) /
          (d : ℝ) := by
            unfold Real.logb
            rw [Real.log_div (ne_of_gt hdpos) (Real.exp_ne_zero 1),
              Real.log_exp,
              Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hdpos),
              Real.log_exp]
            field_simp [ne_of_gt hdpos, ne_of_gt hlog2pos]
            ring
  have hU :
      0 ≤ (n : ℝ) * Real.logb 2 (Real.exp 1 * (d : ℝ)) / (d : ℝ) := by
    have hloged : 0 ≤ Real.logb 2 (Real.exp 1 * (d : ℝ)) := by
      unfold Real.logb
      apply div_nonneg
      · apply Real.log_nonneg
        have : 1 ≤ Real.exp 1 * (d : ℝ) := by
          have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
          have hd1 : 1 ≤ (d : ℝ) := by exact_mod_cast (show 1 ≤ d by omega)
          have hed : Real.exp 1 ≤ Real.exp 1 * (d : ℝ) :=
            (by simpa using
              mul_le_mul_of_nonneg_left hd1 (le_of_lt (Real.exp_pos 1)))
          exact he.trans hed
        exact this
      · exact le_of_lt hlog2pos
    positivity
  refine ⟨max 0 A₀, ?_⟩
  unfold cycle_factor_entropy_certificate
  refine ⟨le_max_left _ _, ?_, ?_⟩
  · exact max_le hU hAupper
  · exact hcore.trans (add_le_add_right (le_max_right 0 A₀) _)
  }

@[blueprint "lem:uniform-expected-cycle-count-le-card"
  (statement := /-- For every directed graph on $[n]$, the uniform expected number of cycles of its cycle-factors is at most $n$. -/)
  (proof := /-- By \cref{def:permutation-cycle-count}, the cycle count is the cardinality of the quotient by the same-cycle relation.  The canonical map onto this quotient is surjective, so every cycle-factor has at most $n$ cycles.  Summing this pointwise inequality over the finite set in \cref{def:directed-cycle-factors} gives an upper bound equal to $n$ times its cardinality.  If that set is nonempty, divide by its positive cardinality and apply \cref{def:uniform-expected-cycle-count}.  If it is empty, the latter definition makes the expectation zero, which is at most $n$. -/)
  (title := /-- Trivial bound for the expected cycle count -/)
  (latexEnv := "lemma")]
lemma uniform_expected_cycle_count_le_card {n : ℕ} (G : Digraph (Fin n)) :
    uniform_expected_cycle_count G ≤ (n : ℝ) := by
  classical
  unfold uniform_expected_cycle_count
  by_cases h : (directed_cycle_factors G).Nonempty
  · have hcard : 0 < ((directed_cycle_factors G).card : ℝ) := by
      exact_mod_cast h.card_pos
    have hsum :
        (∑ σ ∈ directed_cycle_factors G, (permutation_cycle_count σ : ℝ)) ≤
          ((directed_cycle_factors G).card : ℝ) * (n : ℝ) := by
      calc
        (∑ σ ∈ directed_cycle_factors G, (permutation_cycle_count σ : ℝ)) ≤
            ∑ σ ∈ directed_cycle_factors G, (n : ℝ) := by
              apply Finset.sum_le_sum
              intro σ hσ
              exact_mod_cast (show permutation_cycle_count σ ≤ n by
                simpa [permutation_cycle_count] using
                  Fintype.card_quotient_le (Equiv.Perm.SameCycle.setoid σ))
        _ = ((directed_cycle_factors G).card : ℝ) * (n : ℝ) := by simp
    calc
      (∑ σ ∈ directed_cycle_factors G, (permutation_cycle_count σ : ℝ)) /
            ((directed_cycle_factors G).card : ℝ) ≤
          (((directed_cycle_factors G).card : ℝ) * (n : ℝ)) /
            ((directed_cycle_factors G).card : ℝ) :=
        (div_le_div_iff_of_pos_right hcard).2 hsum
      _ = (n : ℝ) := by field_simp
  · simp [Finset.not_nonempty_iff_eq_empty.mp h]

@[blueprint "lem:harmonic-sum-le-one-add-log"
  (statement := /-- For every positive integer $d$, the harmonic sum satisfies
  \[
  H_d\leq 1+\log d,
  \]
  where $\log$ is the natural logarithm. -/)
  (proof := /-- By \cref{def:harmonic-sum}, the difference $H_{d+1}-H_d$ is $1/(d+1)$.  For $d\geq1$, the inequality $1-x^{-1}\leq\log x$, applied with $x=(d+1)/d$, gives
  \[
  \frac1{d+1}\leq \log(d+1)-\log d.
  \]
  The assertion follows by induction from $H_1=1$. -/)
  (title := /-- Harmonic sum bounded by a logarithm -/)
  (latexEnv := "lemma")]
lemma harmonic_sum_le_one_add_log (d : ℕ) (hd : 1 ≤ d) :
    harmonic_sum d ≤ 1 + Real.log (d : ℝ) := by
  induction d with
  | zero => omega
  | succ d ih =>
      by_cases hdz : d = 0
      · subst d
        norm_num [harmonic_sum]
      · have hdpos : 0 < (d : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hdz
        have hsuccpos : 0 < ((d + 1 : ℕ) : ℝ) := by positivity
        have hratio : 0 < (((d + 1 : ℕ) : ℝ) / (d : ℝ)) :=
          div_pos hsuccpos hdpos
        have hinv :
            1 - ((((d + 1 : ℕ) : ℝ) / (d : ℝ))⁻¹) =
              (((d + 1 : ℕ) : ℝ)⁻¹) := by
          field_simp [ne_of_gt hdpos, ne_of_gt hsuccpos]
          <;> norm_num [Nat.cast_add]
        have hstep :
            (((d + 1 : ℕ) : ℝ)⁻¹) ≤
              Real.log ((d + 1 : ℕ) : ℝ) - Real.log (d : ℝ) := by
          rw [← Real.log_div (ne_of_gt hsuccpos) (ne_of_gt hdpos), ← hinv]
          exact Real.one_sub_inv_le_log_of_pos hratio
        calc
          harmonic_sum (d + 1) =
              harmonic_sum d + (((d + 1 : ℕ) : ℝ)⁻¹) := by
                unfold harmonic_sum
                rw [Finset.sum_Icc_succ_top (by omega)]
          _ ≤ (1 + Real.log (d : ℝ)) +
                (Real.log ((d + 1 : ℕ) : ℝ) - Real.log (d : ℝ)) :=
              add_le_add (ih (Nat.one_le_iff_ne_zero.mpr hdz)) hstep
          _ = 1 + Real.log ((d + 1 : ℕ) : ℝ) := by ring

@[blueprint "lem:final-harmonic-estimate"
  (statement := /-- Let $n,d\in\mathbb N$ with $d\geq2$, and let $E,L\in\mathbb R$.  Suppose
  \[
  E\leq n,\qquad L\leq\frac{n\log_2(ed)}d,
  \qquad E\leq\frac{2n}{d}H_d+L.
  \]
  Then
  \[
  E\leq\frac{4n\log_2d}{d}.
  \] -/)
  (proof := /-- Put $a=\log 2$.  The elementary logarithmic inequalities $1-x^{-1}\leq\log x\leq x-1$ give $1/2\leq a\leq1$.  If $d<8$, monotonicity of the logarithm gives $\log_2d\geq1$ for $2\leq d\leq4$ and $\log_2d\geq2$ for $5\leq d<8$; hence $n\leq4n\log_2d/d$, and the conclusion follows from $E\leq n$.

  Suppose now that $d\geq8$.  Then $\log d\geq3a$.  By \cref{lem:harmonic-sum-le-one-add-log}, $H_d\leq1+\log d$.  Since $1/2\leq a\leq1$, both $(3-2a)(\log d-3a)$ and $(1-a)(6a-1)$ are nonnegative.  The identity
  \[
  4\log d-(2a+1)(1+\log d)
  =(3-2a)(\log d-3a)+(1-a)(6a-1)
  \]
  therefore gives
  \[
  (2a+1)(1+\log d)\leq4\log d.
  \]
  Dividing by $a$ and using $\log(ed)=1+\log d$ gives
  \[
  2H_d+\log_2(ed)\leq4\log_2d.
  \]
  Substitution into the two assumed bounds for $L$ and $E$ proves the result. -/)
  (title := /-- Final harmonic estimate -/)
  (latexEnv := "lemma")]
lemma final_harmonic_estimate {n d : ℕ} {E L : ℝ} (hd : 2 ≤ d)
    (htrivial : E ≤ (n : ℝ))
    (hloss : L ≤ (n : ℝ) * Real.logb 2 (Real.exp 1 * (d : ℝ)) / (d : ℝ))
    (hentropy : E ≤ (2 * (n : ℝ) / (d : ℝ)) * harmonic_sum d + L) :
    E ≤ 4 * (n : ℝ) * Real.logb 2 (d : ℝ) / (d : ℝ) := by
  have hdpos : 0 < (d : ℝ) := by positivity
  have hnnonneg : 0 ≤ (n : ℝ) := by positivity
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lower : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at h ⊢
    linarith
  have hlog2_upper : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at h ⊢
    exact h
  by_cases hsmall : d < 8
  · by_cases hdle : d ≤ 4
    · have hlogd : Real.log 2 ≤ Real.log (d : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hd)
      have hlogb : 1 ≤ Real.logb 2 (d : ℝ) := by
        rw [Real.logb, le_div_iff₀ hlog2pos]
        simpa using hlogd
      calc
        E ≤ (n : ℝ) := htrivial
        _ ≤ 4 * (n : ℝ) * Real.logb 2 (d : ℝ) / (d : ℝ) := by
          rw [le_div_iff₀ hdpos]
          have hdn : (d : ℝ) ≤ 4 := by exact_mod_cast hdle
          nlinarith [mul_nonneg hnnonneg (sub_nonneg.mpr hlogb)]
    · have hd4 : 4 ≤ d := by omega
      have hlogd : Real.log (4 : ℝ) ≤ Real.log (d : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hd4)
      have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num,
          Real.log_mul (by norm_num) (by norm_num)]
        ring
      have hlogb : 2 ≤ Real.logb 2 (d : ℝ) := by
        rw [Real.logb, le_div_iff₀ hlog2pos]
        rw [← hlog4]
        exact hlogd
      calc
        E ≤ (n : ℝ) := htrivial
        _ ≤ 4 * (n : ℝ) * Real.logb 2 (d : ℝ) / (d : ℝ) := by
          rw [le_div_iff₀ hdpos]
          have hdn : (d : ℝ) ≤ 8 := by exact_mod_cast (Nat.le_of_lt hsmall)
          nlinarith [mul_nonneg hnnonneg (sub_nonneg.mpr (show 0 ≤ Real.logb 2 (d : ℝ) by linarith))]
  · have hd8 : 8 ≤ d := by omega
    have hlogd : 3 * Real.log 2 ≤ Real.log (d : ℝ) := by
      have hmono : Real.log (8 : ℝ) ≤ Real.log (d : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hd8)
      have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = (2 * 2) * 2 by norm_num,
          Real.log_mul (by norm_num) (by norm_num),
          Real.log_mul (by norm_num) (by norm_num)]
        ring
      linarith
    have hharm := harmonic_sum_le_one_add_log d (by omega)
    have hcoef : 0 ≤ 3 - 2 * Real.log 2 := by linarith
    have hmove :
        0 ≤ (3 - 2 * Real.log 2) *
          (Real.log (d : ℝ) - 3 * Real.log 2) :=
      mul_nonneg hcoef (sub_nonneg.mpr hlogd)
    have hfactor :
        0 ≤ (1 - Real.log 2) * (6 * Real.log 2 - 1) :=
      mul_nonneg (sub_nonneg.mpr hlog2_upper) (by linarith)
    have hpoly :
        (2 * Real.log 2 + 1) * (1 + Real.log (d : ℝ)) ≤
          4 * Real.log (d : ℝ) := by
      nlinarith
    have hscaled :
        2 * Real.log 2 * harmonic_sum d + (1 + Real.log (d : ℝ)) ≤
          4 * Real.log (d : ℝ) := by
      nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (le_of_lt hlog2pos)) (sub_nonneg.mpr hharm)]
    have hloged :
        Real.log (Real.exp 1 * (d : ℝ)) = 1 + Real.log (d : ℝ) := by
      rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hdpos), Real.log_exp]
    have hsum :
        2 * harmonic_sum d + Real.logb 2 (Real.exp 1 * (d : ℝ)) ≤
          4 * Real.logb 2 (d : ℝ) := by
      rw [Real.logb, Real.logb, hloged]
      calc
        2 * harmonic_sum d + (1 + Real.log (d : ℝ)) / Real.log 2 =
            (2 * Real.log 2 * harmonic_sum d +
              (1 + Real.log (d : ℝ))) / Real.log 2 := by
                field_simp [ne_of_gt hlog2pos]
                <;> ring
        _ ≤ (4 * Real.log (d : ℝ)) / Real.log 2 :=
          (div_le_div_iff_of_pos_right hlog2pos).2 hscaled
        _ = 4 * (Real.log (d : ℝ) / Real.log 2) := by ring
    calc
      E ≤ (2 * (n : ℝ) / (d : ℝ)) * harmonic_sum d + L := hentropy
      _ ≤ (2 * (n : ℝ) / (d : ℝ)) * harmonic_sum d +
          (n : ℝ) * Real.logb 2 (Real.exp 1 * (d : ℝ)) / (d : ℝ) :=
        add_le_add_right hloss _
      _ = ((n : ℝ) / (d : ℝ)) *
          (2 * harmonic_sum d + Real.logb 2 (Real.exp 1 * (d : ℝ))) := by ring
      _ ≤ ((n : ℝ) / (d : ℝ)) * (4 * Real.logb 2 (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum (div_nonneg hnnonneg (le_of_lt hdpos))
      _ = 4 * (n : ℝ) * Real.logb 2 (d : ℝ) / (d : ℝ) := by ring

@[blueprint "thm:small-cycle-factor-directed"
  (statement := /-- Let $n,d\in\mathbb N$ with $d\geq2$, and let $G$ be a directed $d$-regular graph on $[n]$.  The expected number of cycles in a uniformly random cycle-factor of $G$ satisfies
  \[
  \mathbb E_{\sigma\in\mathcal C(G)}|\sigma|
  \leq \frac{4n\log_2d}{d}.
  \] -/)
  (proof := /-- By \cref{lem:cycle-factor-entropy-certificate-exists}, choose an entropy certificate $L$.  Its second component gives $L\leq n\log_2(ed)/d$, and its third component gives
  \[
  \mathbb E|\sigma|\leq\frac{2n}{d}H_d+L.
  \]
  Independently, \cref{lem:uniform-expected-cycle-count-le-card} gives $\mathbb E|\sigma|\leq n$.  Apply \cref{lem:final-harmonic-estimate} to these three inequalities to obtain the asserted constant-$4$ bound. -/)
  (title := /-- Few cycles in a random directed cycle-factor -/)
  (latexEnv := "theorem")]
theorem small_cycle_factor_directed {n d : ℕ} (G : Digraph (Fin n))
    (hreg : directed_regular G d) (hd : 2 ≤ d) :
    uniform_expected_cycle_count G ≤
      4 * (n : ℝ) * Real.logb 2 (d : ℝ) / (d : ℝ) := by
  obtain ⟨L, _, hloss, hentropy⟩ :=
    cycle_factor_entropy_certificate_exists G hreg hd
  apply final_harmonic_estimate (E := uniform_expected_cycle_count G) (L := L) hd
  · exact uniform_expected_cycle_count_le_card G
  · exact hloss
  · exact hentropy

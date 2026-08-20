import Architect
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:osgm-point"
  (statement := /-- For $n\in\mathbb{N}$, the optimization domain is the Euclidean space $\mathbb{R}^n$, represented with coordinates indexed by $\operatorname{Fin}(n)$. -/)
  (title := /-- Euclidean optimization domain -/)
  (latexEnv := "definition")]
abbrev osgm_point (n : ℕ) := EuclideanSpace ℝ (Fin n)

@[blueprint "def:osgm-matrix"
  (statement := /-- For $n\in\mathbb{N}$, a scaling matrix is represented by its $n^2$ real entries as a Euclidean vector indexed by $\operatorname{Fin}(n)\times\operatorname{Fin}(n)$.  Consequently its Euclidean norm is the Frobenius norm. -/)
  (title := /-- Scaling matrices -/)
  (latexEnv := "definition")]
abbrev osgm_matrix (n : ℕ) := EuclideanSpace ℝ (Fin n × Fin n)

@[blueprint "def:osgm-matrix-view"
  (statement := /-- The matrix view of a scaling vector $P$ is the matrix whose $(i,j)$ entry is the coordinate of $P$ indexed by $(i,j)$. -/)
  (title := /-- Matrix view of a scaling vector -/)
  (latexEnv := "definition")]
def osgm_matrix_view {n : ℕ} (P : osgm_matrix n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => P (i, j)

@[blueprint "def:ratio-surrogate"
  (statement := /-- Let $f:\mathbb{R}^n\to\mathbb{R}$, let $x^\star,x\in\mathbb{R}^n$, and let $P\in\mathbb{R}^{n\times n}$.  The ratio surrogate is
  \[
    r_x(P)=\frac{f\bigl(x-P\nabla f(x)\bigr)-f(x^\star)}
                   {f(x)-f(x^\star)}.
  \]
  The expression is used only under a hypothesis that its denominator is positive. -/)
  (title := /-- Ratio surrogate loss -/)
  (latexEnv := "definition")]
noncomputable def ratio_surrogate {n : ℕ} (f : osgm_point n → ℝ)
    (xStar x : osgm_point n) (P : osgm_matrix n) : ℝ :=
  (f (x - Matrix.toEuclideanLin (osgm_matrix_view P) (gradient f x)) - f xStar) /
    (f x - f xStar)

@[blueprint "def:metric-projection-map"
  (statement := /-- Let $\mathcal P$ be a set of scaling matrices.  A map $\Pi_{\mathcal P}$ is a metric projection onto $\mathcal P$ if, for every matrix $A$, its value belongs to $\mathcal P$ and has no larger Frobenius distance from $A$ than any other member of $\mathcal P$. -/)
  (title := /-- Metric projection onto the feasible set -/)
  (latexEnv := "definition")]
def metric_projection_map {n : ℕ} (Pset : Set (osgm_matrix n))
    (project : osgm_matrix n → osgm_matrix n) : Prop :=
  ∀ A, project A ∈ Pset ∧ ∀ Q ∈ Pset, ‖project A - A‖ ≤ ‖Q - A‖

@[blueprint "def:osgm-objective-assumptions"
  (statement := /-- Let $f:\mathbb{R}^n\to\mathbb{R}$, let $x^\star\in\mathbb{R}^n$, and let $L,\mu\in\mathbb{R}$.  The objective assumptions are: $L>0$, $\mu>0$, the function $f$ is differentiable and its gradient is differentiable at every point, $x^\star$ is a global minimizer, and, for every $x,y\in\mathbb{R}^n$,
  \[
  \left|f(x)-f(y)-\langle\nabla f(y),x-y\rangle\right|
      \leq \frac L2\lVert x-y\rVert^2
  \]
  and
  \[
  f(x)-f(y)-\langle\nabla f(y),x-y\rangle
      \geq \frac\mu2\lVert x-y\rVert^2.
  \] -/)
  (title := /-- Smooth strongly convex objective -/)
  (latexEnv := "definition")]
def osgm_objective_assumptions {n : ℕ} (f : osgm_point n → ℝ)
    (xStar : osgm_point n) (L μ : ℝ) : Prop :=
  0 < L ∧ 0 < μ ∧ Differentiable ℝ f ∧
    (∀ x, DifferentiableAt ℝ (gradient f) x) ∧
    (∀ x, f xStar ≤ f x) ∧
    (∀ x y,
      abs (f x - f y - inner ℝ (gradient f y) (x - y)) ≤
        L / 2 * ‖x - y‖ ^ 2) ∧
    (∀ x y,
      μ / 2 * ‖x - y‖ ^ 2 ≤
        f x - f y - inner ℝ (gradient f y) (x - y))

@[blueprint "def:positive-objective-gaps"
  (statement := /-- For an integer $K\geq 1$, the iterates $x^1,\ldots,x^K$ have positive objective gaps if $f(x^k)>f(x^\star)$ for every $1\leq k\leq K$.  These are precisely the denominators of the ratio surrogates evaluated during the first $K$ updates.  No positivity is imposed on the terminal gap at $x^{K+1}$, which may vanish if the final update reaches the optimal set. -/)
  (title := /-- Positivity of the active ratio denominators -/)
  (latexEnv := "definition")]
def positive_objective_gaps {n : ℕ} (f : osgm_point n → ℝ)
    (xStar : osgm_point n) (x : ℕ → osgm_point n) (K : ℕ) : Prop :=
  ∀ k, 1 ≤ k → k ≤ K → 0 < f (x k) - f xStar

@[blueprint "def:osgm-rx-run"
  (statement := /-- Fix $K\geq1$, a feasible set $\mathcal P$, its metric projection $\Pi_{\mathcal P}$, and a stepsize $\eta$.  Sequences $(x^k)$ and $(P_k)$ form an OSGM--Rx run through iteration $K$ if, for every $1\leq k\leq K$,
  \[
    x^{k+1}=x^k-P_k\nabla f(x^k),\qquad
    P_{k+1}=\Pi_{\mathcal P}\bigl(P_k-\eta\nabla r_{x^k}(P_k)\bigr).
  \] -/)
  (title := /-- OSGM--Rx recurrence -/)
  (latexEnv := "definition")]
noncomputable def osgm_rx_run {n : ℕ} (f : osgm_point n → ℝ)
    (xStar : osgm_point n) (x : ℕ → osgm_point n)
    (P : ℕ → osgm_matrix n) (project : osgm_matrix n → osgm_matrix n)
    (η : ℝ) (K : ℕ) : Prop :=
  (∀ k, 1 ≤ k → k ≤ K →
    x (k + 1) = x k -
      Matrix.toEuclideanLin (osgm_matrix_view (P k)) (gradient f (x k))) ∧
  (∀ k, 1 ≤ k → k ≤ K →
    P (k + 1) = project
      (P k - η • gradient (ratio_surrogate f xStar (x k)) (P k)))

@[blueprint "def:preconditioner-feasible"
  (statement := /-- Let $f:\mathbb{R}^n\to\mathbb{R}$ and let $\kappa>0$.  A positive-semidefinite matrix $P$ is feasible with condition number $\kappa$ if it admits a positive-semidefinite square root $R$, with $R^2=P$, such that for every $x,v\in\mathbb{R}^n$,
  \[
    \frac1\kappa\lVert v\rVert^2
    \leq \left\langle Rv,\nabla^2f(x)Rv\right\rangle
    \leq \lVert v\rVert^2.
  \]
  Here $\nabla^2f(x)$ is represented by the Fréchet derivative of the gradient. -/)
  (title := /-- Feasibility in the universal preconditioner problem -/)
  (latexEnv := "definition")]
noncomputable def preconditioner_feasible {n : ℕ} (f : osgm_point n → ℝ)
    (κ : ℝ) (P : osgm_matrix n) : Prop :=
  0 < κ ∧ Matrix.PosSemidef (osgm_matrix_view P) ∧
    ∃ R : osgm_matrix n, Matrix.PosSemidef (osgm_matrix_view R) ∧
      osgm_matrix_view R * osgm_matrix_view R = osgm_matrix_view P ∧
      ∀ x v,
        κ⁻¹ * ‖v‖ ^ 2 ≤
            inner ℝ (Matrix.toEuclideanLin (osgm_matrix_view R) v)
              ((fderiv ℝ (gradient f) x)
                (Matrix.toEuclideanLin (osgm_matrix_view R) v)) ∧
          inner ℝ (Matrix.toEuclideanLin (osgm_matrix_view R) v)
              ((fderiv ℝ (gradient f) x)
                (Matrix.toEuclideanLin (osgm_matrix_view R) v)) ≤
            ‖v‖ ^ 2

@[blueprint "def:universal-optimal-preconditioner"
  (statement := /-- Let $\mathcal P$ be the admissible set of scaling matrices.  A pair $(P_r^\star,\kappa^\star)$ is universally optimal if $P_r^\star\in\mathcal P$, it is feasible with condition number $\kappa^\star$, and $\kappa^\star$ is no larger than the condition number of any other feasible matrix in $\mathcal P$. -/)
  (title := /-- Universal optimal preconditioner -/)
  (latexEnv := "definition")]
noncomputable def universal_optimal_preconditioner {n : ℕ}
    (f : osgm_point n → ℝ) (Pset : Set (osgm_matrix n))
    (κStar : ℝ) (PStar : osgm_matrix n) : Prop :=
  PStar ∈ Pset ∧ preconditioner_feasible f κStar PStar ∧
    ∀ κ P, P ∈ Pset → preconditioner_feasible f κ P → κStar ≤ κ

@[blueprint "def:ratio-average"
  (statement := /-- For $K\geq1$, the average ratio loss of a matrix sequence $(Q_k)$ along the iterates $(x^k)$ is
  \[
    \overline r_K(Q)=\frac1K\sum_{k=1}^K r_{x^k}(Q_k).
  \]
  The same definition applies to a constant comparator sequence. -/)
  (title := /-- Average ratio loss -/)
  (latexEnv := "definition")]
noncomputable def ratio_average {n : ℕ} (f : osgm_point n → ℝ)
    (xStar : osgm_point n) (x : ℕ → osgm_point n)
    (Q : ℕ → osgm_matrix n) (K : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 K, ratio_surrogate f xStar (x k) (Q k)) / (K : ℝ)

@[blueprint "lem:ratio-surrogate-step-identity"
  (statement := /-- Let $n\in\mathbb N$, let $f:\mathbb R^n\to\mathbb R$, let $x^\star,x\in\mathbb R^n$, and let $P\in\mathbb R^{n\times n}$.  Set $x^+=x-P\nabla f(x)$.  If $f(x)-f(x^\star)>0$, then
  \[
    f(x^+)-f(x^\star)=r_x(P)\bigl(f(x)-f(x^\star)\bigr).
  \] -/)
  (proof := /-- By \cref{def:ratio-surrogate}, the right-hand side is the quotient of the next objective gap by the current objective gap, multiplied by the current objective gap.  The strict positivity hypothesis makes the current objective gap nonzero, so cancellation yields the next objective gap. -/)
  (title := /-- One-step ratio identity -/)
  (latexEnv := "lemma")]
lemma ratio_surrogate_step_identity {n : ℕ} (f : osgm_point n → ℝ)
    (xStar x : osgm_point n) (P : osgm_matrix n)
    (hgap : 0 < f x - f xStar) :
    f (x - Matrix.toEuclideanLin (osgm_matrix_view P) (gradient f x)) - f xStar =
      ratio_surrogate f xStar x P * (f x - f xStar) := by
  rw [ratio_surrogate, div_mul_cancel₀ _ (ne_of_gt hgap)]

@[blueprint "lem:ratio-online-to-convergence"
  (statement := /-- Let $n,K\in\mathbb N$ with $K\geq1$, let $f:\mathbb R^n\to\mathbb R$, let $x^\star\in\mathbb R^n$, let $q\in\mathbb R$, and let $(x^k)_{k\in\mathbb N}$ and $(P_k)_{k\in\mathbb N}$ be sequences in $\mathbb R^n$ and $\mathbb R^{n\times n}$, respectively.  Suppose that, for every $1\leq k\leq K$,
  \[
    x^{k+1}=x^k-P_k\nabla f(x^k)
    \quad\text{and}\quad
    f(x^k)-f(x^\star)>0.
  \]
  Suppose also that the terminal gap $f(x^{K+1})-f(x^\star)$ is nonnegative and that
  \[
    \frac1K\sum_{k=1}^K r_{x^k}(P_k)\leq q.
  \]
  Then
  \[
    f(x^{K+1})-f(x^\star)
      \leq \bigl(f(x^1)-f(x^\star)\bigr)q^K.
  \] -/)
  (proof := /-- Write $g_k=f(x^k)-f(x^\star)$ and $r_k=r_{x^k}(P_k)$.  By \cref{def:positive-objective-gaps}, $g_k>0$ for $1\leq k\leq K$.  For $1\leq k<K$, the numerator of $r_k$ is $g_{k+1}>0$, while the numerator of $r_K$ is $g_{K+1}\geq0$; hence all the numbers $r_1,\ldots,r_K$ are nonnegative.  For each $1\leq k\leq K$, the update equation and \cref{lem:ratio-surrogate-step-identity} give $g_{k+1}=r_k g_k$.  Induction on the upper endpoint of the product yields
  \[
    g_{K+1}=g_1\prod_{k=1}^K r_k.
  \]
  The arithmetic--geometric mean inequality for the nonnegative numbers $r_1,\ldots,r_K$ gives
  \[
    \prod_{k=1}^K r_k
      \leq\left(\frac1K\sum_{k=1}^K r_k\right)^K.
  \]
  By \cref{def:ratio-average}, the right-hand side is the assumed average ratio.  This average is nonnegative, and its assumed upper bound therefore implies $q\geq0$.  Monotonicity of the $K$th power on nonnegative real numbers now bounds the last display by $q^K$.  Multiplication by $g_1>0$ and the product identity prove the claim. -/)
  (title := /-- Online ratio bound implies convergence -/)
  (latexEnv := "lemma")]
lemma ratio_online_to_convergence {n K : ℕ} (f : osgm_point n → ℝ)
    (xStar : osgm_point n) (x : ℕ → osgm_point n)
    (P : ℕ → osgm_matrix n) (q : ℝ) (hK : 0 < K)
    (hstep : ∀ k, 1 ≤ k → k ≤ K →
      x (k + 1) = x k -
        Matrix.toEuclideanLin (osgm_matrix_view (P k)) (gradient f (x k)))
    (hpositive : positive_objective_gaps f xStar x K)
    (hterminal : 0 ≤ f (x (K + 1)) - f xStar)
    (haverage : ratio_average f xStar x P K ≤ q) :
    f (x (K + 1)) - f xStar ≤ (f (x 1) - f xStar) * q ^ K := by
  let gap : ℕ → ℝ := fun k => f (x k) - f xStar
  let r : ℕ → ℝ := fun k => ratio_surrogate f xStar (x k) (P k)
  have hgap (k : ℕ) (hk1 : 1 ≤ k) (hkK : k ≤ K) : 0 < gap k := by
    exact hpositive k hk1 hkK
  have hratio_step (k : ℕ) (hk1 : 1 ≤ k) (hkK : k ≤ K) :
      gap (k + 1) = r k * gap k := by
    change f (x (k + 1)) - f xStar =
      ratio_surrogate f xStar (x k) (P k) * (f (x k) - f xStar)
    rw [hstep k hk1 hkK]
    exact ratio_surrogate_step_identity f xStar (x k) (P k) (hgap k hk1 hkK)
  have hratio_div (k : ℕ) (hk1 : 1 ≤ k) (hkK : k ≤ K) :
      r k = gap (k + 1) / gap k := by
    apply (eq_div_iff (ne_of_gt (hgap k hk1 hkK))).2
    exact (hratio_step k hk1 hkK).symm
  have hr_nonneg (k : ℕ) (hk : k ∈ Finset.Icc 1 K) : 0 ≤ r k := by
    rcases Finset.mem_Icc.mp hk with ⟨hk1, hkK'⟩
    rw [hratio_div k hk1 hkK']
    apply div_nonneg
    · by_cases hkK : k = K
      · subst k
        exact hterminal
      · exact le_of_lt (hpositive (k + 1) (by omega) (by omega))
    · exact le_of_lt (hgap k hk1 hkK')
  have hweight_pos : 0 < ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) := by
    simp [Nat.card_Icc, hK]
  have hamgm := Real.geom_mean_le_arith_mean (Finset.Icc 1 K)
    (fun _ => (1 : ℝ)) r (by simp) hweight_pos hr_nonneg
  have hamgm' :
      (∏ k ∈ Finset.Icc 1 K, r k) ^ ((K : ℝ)⁻¹) ≤
        ratio_average f xStar x P K := by
    simpa [ratio_average, r, Nat.card_Icc] using hamgm
  have hprod_nonneg : 0 ≤ ∏ k ∈ Finset.Icc 1 K, r k := by
    exact Finset.prod_nonneg hr_nonneg
  have havg_nonneg : 0 ≤ ratio_average f xStar x P K := by
    rw [ratio_average]
    exact div_nonneg (Finset.sum_nonneg fun k hk => hr_nonneg k hk) (Nat.cast_nonneg K)
  have hprod_le_avg_pow :
      (∏ k ∈ Finset.Icc 1 K, r k) ≤ (ratio_average f xStar x P K) ^ K := by
    have hp := pow_le_pow_left₀ (Real.rpow_nonneg hprod_nonneg ((K : ℝ)⁻¹)) hamgm' K
    rw [Real.rpow_inv_natCast_pow hprod_nonneg (Nat.ne_of_gt hK)] at hp
    exact hp
  have hprod_le_q_pow : (∏ k ∈ Finset.Icc 1 K, r k) ≤ q ^ K := by
    exact hprod_le_avg_pow.trans (pow_le_pow_left₀ havg_nonneg haverage K)
  have htel (m : ℕ) (hm1 : 1 ≤ m) (hmK : m ≤ K) :
      gap (m + 1) = gap 1 * ∏ k ∈ Finset.Icc 1 m, r k := by
    induction m with
    | zero => omega
    | succ m ih =>
        by_cases hm0 : m = 0
        · subst m
          simpa [hratio_step 1 (by omega) hmK, mul_comm]
        · have hm1' : 1 ≤ m := by omega
          calc
            gap (m + 1 + 1) = r (m + 1) * gap (m + 1) :=
              hratio_step (m + 1) (by omega) hmK
            _ = r (m + 1) * (gap 1 * ∏ k ∈ Finset.Icc 1 m, r k) := by
              rw [ih hm1' (by omega)]
            _ = gap 1 * ((∏ k ∈ Finset.Icc 1 m, r k) * r (m + 1)) := by ring
            _ = gap 1 * ∏ k ∈ Finset.Icc 1 (m + 1), r k := by
              rw [Finset.prod_Icc_succ_top (by omega) r]
  have hgap_one : 0 < gap 1 := hgap 1 (by omega) (by omega)
  have hfinal : gap (K + 1) ≤ gap 1 * q ^ K := by
    rw [htel K hK le_rfl]
    exact mul_le_mul_of_nonneg_left hprod_le_q_pow (le_of_lt hgap_one)
  exact hfinal

@[blueprint "lem:universal-preconditioner-ratio-bound"
  (statement := /-- Let $f:\mathbb{R}^n\to\mathbb{R}$ be differentiable, suppose that $\nabla f$ is differentiable at every point, and let $L,\mu>0$.  Let $x^\star$ be a global minimizer of $f$, and assume that, for every $x,y\in\mathbb{R}^n$,
  \[
    \left|f(x)-f(y)-\langle\nabla f(y),x-y\rangle\right|
      \leq \frac L2\lVert x-y\rVert^2,
    \qquad
    \frac\mu2\lVert x-y\rVert^2
      \leq f(x)-f(y)-\langle\nabla f(y),x-y\rangle.
  \]
  Let $\mathcal P\subseteq\mathbb{R}^{n\times n}$ and $P_r^\star\in\mathcal P$.  Suppose that $\kappa^\star>0$, that $P_r^\star$ is positive semidefinite, and that there is a positive-semidefinite matrix $R$ with $R^2=P_r^\star$ such that, for every $z,v\in\mathbb{R}^n$,
  \[
    (\kappa^\star)^{-1}\lVert v\rVert^2
      \leq \langle Rv,D(\nabla f)(z)[Rv]\rangle
      \leq \lVert v\rVert^2.
  \]
  Assume moreover that $\kappa^\star\leq\kappa$ whenever $P\in\mathcal P$ is positive semidefinite and is feasible with condition number $\kappa>0$ in the same sense.  Then, for every $x\in\mathbb{R}^n$ satisfying $f(x)>f(x^\star)$,
  \[
    r_x(P_r^\star)\leq 1-\frac1{\kappa^\star}.
  \] -/)
  (proof := /-- Unpack the objective hypotheses from \cref{def:osgm-objective-assumptions} and the positive-semidefinite square root $R$ and Hessian bounds from \cref{def:universal-optimal-preconditioner, def:preconditioner-feasible}.  First prove the following linewise Taylor estimate.  If $f$ is differentiable, $\nabla f$ is differentiable everywhere, and
  \[
    a\leq\langle d,D(\nabla f)(z+td)[d]\rangle\leq b
    \qquad(t\in\mathbb R),
  \]
  then
  \[
    f(z)+\langle\nabla f(z),d\rangle+\frac a2
      \leq f(z+d)
      \leq f(z)+\langle\nabla f(z),d\rangle+\frac b2.
  \]
  To obtain this estimate using only the imported calculus primitives, prove Fermat's theorem from the positive tangent cone, deduce Rolle's theorem by applying the extreme-value theorem on a closed interval, and apply Rolle's theorem twice to the line restriction $t\mapsto f(z+td)$ after subtracting its affine part and a suitable quadratic.  This gives a point $\xi\in(0,1)$ at which twice the Taylor remainder equals $\langle d,D(\nabla f)(z+\xi d)[d]\rangle$, and the displayed bounds follow.

  The lower Hessian bound and $\kappa^\star>0$ imply that the linear map represented by $R$ is injective, hence surjective in finite dimension.  Symmetry of $R$ follows from its positive semidefiniteness, and $R^2=P_r^\star$ holds by \cref{def:osgm-matrix-view}.  Put $g=\nabla f(x)$ and apply the upper Taylor estimate with $v=-Rg$ and $d=Rv$.  Since
  \[
    x+d=x-P_r^\star g,
    \qquad
    \langle g,d\rangle=-\lVert Rg\rVert^2,
  \]
  it follows that
  \[
    f(x-P_r^\star g)-f(x^\star)
      \leq f(x)-f(x^\star)-\frac12\lVert Rg\rVert^2.
  \]
  By surjectivity, choose $w$ with $Rw=x^\star-x$.  The lower Taylor estimate and the fact that $x^\star$ is a minimizer give
  \[
    f(x)-f(x^\star)
      \leq-\langle Rg,w\rangle
        -\frac{1}{2\kappa^\star}\lVert w\rVert^2
      \leq\frac{\kappa^\star}{2}\lVert Rg\rVert^2,
  \]
  where the last inequality is Cauchy--Schwarz followed by Young's inequality.  Consequently $(\kappa^\star)^{-1}(f(x)-f(x^\star))\leq\lVert Rg\rVert^2/2$.  Substitute this inequality into the descent estimate and divide by the positive gap.  The definition in \cref{def:ratio-surrogate} then yields $r_x(P_r^\star)\leq1-(\kappa^\star)^{-1}$. -/)
  (title := /-- Hindsight bound for the universal preconditioner -/)
  (latexEnv := "lemma")]
lemma universal_preconditioner_ratio_bound {n : ℕ}
    (f : osgm_point n → ℝ) (xStar : osgm_point n) (L μ κStar : ℝ)
    (Pset : Set (osgm_matrix n)) (PStar : osgm_matrix n)
    (hobjective : osgm_objective_assumptions f xStar L μ)
    (huniversal : universal_optimal_preconditioner f Pset κStar PStar)
    (x : osgm_point n) (hgap : 0 < f x - f xStar) :
    ratio_surrogate f xStar x PStar ≤ 1 - κStar⁻¹ := by
  let D : ℝ →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.id ℝ ℝ).prod (ContinuousLinearMap.id ℝ ℝ)
  have hmul : IsBoundedBilinearMap ℝ (fun p : ℝ × ℝ => p.1 * p.2) :=
    isBoundedBilinearMap_mul
  have hsquare (t : ℝ) :
      HasFDerivAt ((fun p : ℝ × ℝ => p.1 * p.2) ∘ D)
        (hmul.deriv (D t) ∘L D) t := by
    exact (hmul.hasFDerivAt (D t)).comp t D.hasFDerivAt
  have hsquare_apply (t u : ℝ) : (hmul.deriv (D t) ∘L D) u = 2 * t * u := by
    simp [D, IsBoundedBilinearMap.deriv, ContinuousLinearMap.coe_deriv₂]
    ring
  have hmax_dir {q : ℝ → ℝ} {c : ℝ} {q' : ℝ →L[ℝ] ℝ}
      (hq : IsLocalMax q c) (hdq : HasFDerivAt q q' c) (y : ℝ) : q' y ≤ 0 := by
    have hy : y ∈ posTangentConeAt (Set.univ : Set ℝ) c := by
      change y ∈ tangentConeAt NNReal Set.univ c
      rw [tangentConeAt_univ]
      exact Set.mem_univ y
    rcases exists_fun_of_mem_tangentConeAt hy with
      ⟨ι, l, hl, k, d, hd0, hdmem, hkd⟩
    suffices ∀ᶠ m in l, k m • (q (c + d m) - q c) ≤ 0 from
      le_of_tendsto (hdq.hasFDerivWithinAt.lim hd0 hdmem hkd) this
    replace hdmem :
        Filter.Tendsto (fun m => c + d m) l (nhdsWithin (c + 0) Set.univ) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.add hd0, hdmem⟩
    rw [add_zero] at hdmem
    refine (hdmem.eventually (hq.on Set.univ)).mono ?_
    intro m hm
    exact mul_nonpos_of_nonneg_of_nonpos (k m).coe_nonneg (sub_nonpos.2 hm)
  have hfermat {q : ℝ → ℝ} {c : ℝ} {q' : ℝ →L[ℝ] ℝ}
      (hq : IsLocalExtr q c) (hdq : HasFDerivAt q q' c) : q' = 0 := by
    apply ContinuousLinearMap.ext
    intro y
    rcases hq with hmin | hmax
    · have hlow := hmax_dir hmin.neg hdq.neg y
      have hupp := hmax_dir hmin.neg hdq.neg (-y)
      have hq_nonneg : 0 ≤ q' y := by simpa using hlow
      have hq_nonpos : q' y ≤ 0 := by simpa using hupp
      exact le_antisymm hq_nonpos hq_nonneg
    · have hq_nonpos := hmax_dir hmax hdq y
      have hneg := hmax_dir hmax hdq (-y)
      have hq_nonneg : 0 ≤ q' y := by simpa using hneg
      exact le_antisymm hq_nonpos hq_nonneg
  have hrolle {q : ℝ → ℝ} {q' : ℝ → (ℝ →L[ℝ] ℝ)} {a b : ℝ}
      (hab : a < b) (hdq : ∀ t, HasFDerivAt q (q' t) t)
      (heq : q a = q b) : ∃ c ∈ Set.Ioo a b, q' c = 0 := by
    have hcont : ContinuousOn q (Set.Icc a b) := by
      intro t ht
      exact (hdq t).continuousAt.continuousWithinAt
    have hne : (Set.Icc a b).Nonempty := Set.nonempty_Icc.2 hab.le
    obtain ⟨c, cmem, cle⟩ :
        ∃ c ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, q c ≤ q t :=
      isCompact_Icc.exists_isMinOn hne hcont
    obtain ⟨C, Cmem, Cge⟩ :
        ∃ C ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, q t ≤ q C :=
      isCompact_Icc.exists_isMaxOn hne hcont
    have hextr : ∃ t ∈ Set.Ioo a b, IsExtrOn q (Set.Icc a b) t := by
      by_cases hc : q c = q a
      · by_cases hC : q C = q a
        · have hconst : ∀ t ∈ Set.Icc a b, q t = q a := by
            intro t ht
            exact le_antisymm (hC ▸ Cge t ht) (hc ▸ cle t ht)
          rcases Set.nonempty_Ioo.2 hab with ⟨t, ht⟩
          refine ⟨t, ht, Or.inl ?_⟩
          intro s hs
          simp only [Set.mem_setOf_eq, hconst s hs,
            hconst t (Set.Ioo_subset_Icc_self ht), le_rfl]
        · refine ⟨C, ⟨lt_of_le_of_ne Cmem.1 (mt ?_ hC),
              lt_of_le_of_ne Cmem.2 (mt ?_ hC)⟩, Or.inr Cge⟩
          · intro h
            rw [h]
          · intro h
            rw [h, heq]
      · refine ⟨c, ⟨lt_of_le_of_ne cmem.1 (mt ?_ hc),
            lt_of_le_of_ne cmem.2 (mt ?_ hc)⟩, Or.inl cle⟩
        · intro h
          rw [h]
        · intro h
          rw [h, heq]
    rcases hextr with ⟨t, ht, htext⟩
    refine ⟨t, ht, hfermat (htext.isLocalExtr (Icc_mem_nhds ht.1 ht.2)) (hdq t)⟩
  rcases hobjective with ⟨hL, hμ, hf, hgrad, hmin, hsmooth, hstrong⟩
  have hline (z d : osgm_point n) (t : ℝ) :
      HasDerivAt (fun s : ℝ => z + s • d) d t := by
    simpa using
      (((ContinuousLinearMap.toSpanSingleton ℝ d).hasFDerivAt.const_add z).hasDerivAt)
  have hφ (z d : osgm_point n) (t : ℝ) :
      HasFDerivAt (f ∘ fun s : ℝ => z + s • d)
        ((fderiv ℝ f (z + t • d)).comp
          (ContinuousLinearMap.toSpanSingleton ℝ d)) t := by
    exact (hf (z + t • d)).hasFDerivAt.comp t (hline z d t).hasFDerivAt
  have hψ (z d : osgm_point n) (t : ℝ) :
      HasFDerivAt
        ((InnerProductSpace.toDual ℝ (osgm_point n) d) ∘
          gradient f ∘ fun s : ℝ => z + s • d)
        ((InnerProductSpace.toDual ℝ (osgm_point n) d).comp
          ((fderiv ℝ (gradient f) (z + t • d)).comp
            (ContinuousLinearMap.toSpanSingleton ℝ d))) t := by
    have hg :=
      (hgrad (z + t • d)).hasFDerivAt.comp t (hline z d t).hasFDerivAt
    exact (InnerProductSpace.toDual ℝ (osgm_point n) d).hasFDerivAt.comp t hg
  have htaylor (z d : osgm_point n) (a b : ℝ)
      (hdir : ∀ t : ℝ,
        a ≤ inner ℝ d ((fderiv ℝ (gradient f) (z + t • d)) d) ∧
        inner ℝ d ((fderiv ℝ (gradient f) (z + t • d)) d) ≤ b) :
      f z + inner ℝ (gradient f z) d + a / 2 ≤ f (z + d) ∧
        f (z + d) ≤ f z + inner ℝ (gradient f z) d + b / 2 := by
    let line : ℝ → osgm_point n := fun t => z + t • d
    let φ : ℝ → ℝ := f ∘ line
    let ψ : ℝ → ℝ :=
      (InnerProductSpace.toDual ℝ (osgm_point n) d) ∘ gradient f ∘ line
    let sq : ℝ → ℝ := (fun p : ℝ × ℝ => p.1 * p.2) ∘ D
    let Fφ : ℝ → (ℝ →L[ℝ] ℝ) := fun t =>
      (fderiv ℝ f (line t)).comp (ContinuousLinearMap.toSpanSingleton ℝ d)
    let Fψ : ℝ → (ℝ →L[ℝ] ℝ) := fun t =>
      (InnerProductSpace.toDual ℝ (osgm_point n) d).comp
        ((fderiv ℝ (gradient f) (line t)).comp
          (ContinuousLinearMap.toSpanSingleton ℝ d))
    let A : ℝ := 2 * (φ 1 - φ 0 - ψ 0)
    let lin : ℝ →L[ℝ] ℝ := (ψ 0) • ContinuousLinearMap.id ℝ ℝ
    let q : ℝ → ℝ :=
      (fun t => φ t - φ 0) - (lin : ℝ → ℝ) - (A / 2) • sq
    let Fq : ℝ → (ℝ →L[ℝ] ℝ) := fun t =>
      Fφ t - lin - (A / 2) • (hmul.deriv (D t) ∘L D)
    have hdq (t : ℝ) : HasFDerivAt q (Fq t) t := by
      have hφt : HasFDerivAt φ (Fφ t) t := by
        simpa only [φ, line] using hφ z d t
      have hsqt : HasFDerivAt sq (hmul.deriv (D t) ∘L D) t := by
        simpa only [sq] using hsquare t
      have hlin : HasFDerivAt lin lin t := lin.hasFDerivAt
      simpa only [q, Fq] using
        ((hφt.sub_const (φ 0)).sub hlin).sub (hsqt.const_smul (A / 2))
    have hq01 : q 0 = q 1 := by
      simp [q, A, lin, sq, φ, line, D]
    rcases hrolle (a := (0 : ℝ)) (b := (1 : ℝ)) zero_lt_one hdq hq01 with
      ⟨c, hc, hFc⟩
    let Alin : ℝ →L[ℝ] ℝ := A • ContinuousLinearMap.id ℝ ℝ
    let r : ℝ → ℝ := (fun t => ψ t - ψ 0) - (Alin : ℝ → ℝ)
    let Fr : ℝ → (ℝ →L[ℝ] ℝ) := fun t =>
      Fψ t - Alin
    have hrc : r c = 0 := by
      have heval := DFunLike.congr_fun hFc 1
      simp only [Fq, Fφ, Fψ, line, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at heval ⊢
      rw [hsquare_apply] at heval
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply, one_smul] at heval
      rw [(hf (line c)).hasGradientAt.fderiv_apply] at heval
      simp [r, Alin, ψ, Function.comp_apply, line,
        InnerProductSpace.toDual_apply_apply, lin, real_inner_comm, smul_eq_mul] at heval ⊢
      nlinarith
    have hr0 : r 0 = 0 := by
      simp [r]
    have hdr (t : ℝ) : HasFDerivAt r (Fr t) t := by
      have hψt : HasFDerivAt ψ (Fψ t) t := by
        simpa only [ψ, line] using hψ z d t
      have hAlin :
          HasFDerivAt Alin Alin t := Alin.hasFDerivAt
      simpa only [r, Fr] using (hψt.sub_const (ψ 0)).sub hAlin
    rcases hrolle (a := (0 : ℝ)) (b := c) hc.1 hdr (hr0.trans hrc.symm) with
      ⟨ξ, hξ, hFξ⟩
    have hA : A = inner ℝ d ((fderiv ℝ (gradient f) (line ξ)) d) := by
      have heval := DFunLike.congr_fun hFξ 1
      simp only [Fr, Fψ, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
        one_smul, InnerProductSpace.toDual_apply_apply] at heval
      simp [Alin, smul_eq_mul] at heval
      linarith
    have hAbounds : a ≤ A ∧ A ≤ b := by
      rw [hA]
      simpa only [line] using hdir ξ
    constructor <;>
      simp only [A, φ, ψ, line, Function.comp_apply,
        InnerProductSpace.toDual_apply_apply, one_smul, zero_smul, add_zero,
        real_inner_comm] at hAbounds ⊢ <;>
      nlinarith
  rcases huniversal with
    ⟨hPmem, ⟨hκ, hPpsd, R, hRpsd, hRsq, hH⟩, hoptimal⟩
  let Rlin : osgm_point n →ₗ[ℝ] osgm_point n :=
    Matrix.toEuclideanLin (osgm_matrix_view R)
  let Plin : osgm_point n →ₗ[ℝ] osgm_point n :=
    Matrix.toEuclideanLin (osgm_matrix_view PStar)
  have hRT : (osgm_matrix_view R).transpose = osgm_matrix_view R := by
    have hherm := hRpsd.1
    change Matrix.conjTranspose (osgm_matrix_view R) = osgm_matrix_view R at hherm
    apply Matrix.ext
    intro i j
    have hij := congrFun (congrFun hherm i) j
    simpa [Matrix.conjTranspose_apply] using hij
  have hRinner (u v : osgm_point n) :
      inner ℝ u (Rlin v) = inner ℝ (Rlin u) v := by
    rw [EuclideanSpace.inner_eq_star_dotProduct,
      EuclideanSpace.inner_eq_star_dotProduct]
    change dotProduct (Matrix.mulVec (osgm_matrix_view R) (WithLp.ofLp v))
        (WithLp.ofLp u) =
      dotProduct (WithLp.ofLp v)
        (Matrix.mulVec (osgm_matrix_view R) (WithLp.ofLp u))
    rw [dotProduct_comm]
    rw [← Matrix.dotProduct_transpose_mulVec (osgm_matrix_view R)
      (WithLp.ofLp v) (WithLp.ofLp u)]
    rw [hRT]
  have hRsquare (v : osgm_point n) : Rlin (Rlin v) = Plin v := by
    apply PiLp.ext
    intro i
    simp only [Rlin, Plin, Matrix.toEuclideanLin_apply]
    change (Matrix.mulVec (osgm_matrix_view R)
        (Matrix.mulVec (osgm_matrix_view R) (WithLp.ofLp v))) i =
      (Matrix.mulVec (osgm_matrix_view PStar) (WithLp.ofLp v)) i
    rw [Matrix.mulVec_mulVec, hRsq]
  have hRinj : Function.Injective Rlin := by
    intro u v huv
    have hz : Rlin (u - v) = 0 := by
      rw [map_sub, huv, sub_self]
    have hb := (hH x (u - v)).1
    change κStar⁻¹ * ‖u - v‖ ^ 2 ≤
      inner ℝ (Rlin (u - v))
        ((fderiv ℝ (gradient f) x) (Rlin (u - v))) at hb
    rw [hz] at hb
    simp only [inner_zero_left] at hb
    have hinv : 0 < κStar⁻¹ := inv_pos.mpr hκ
    have hsle : ‖u - v‖ ^ 2 ≤ 0 := by
      exact nonpos_of_mul_nonpos_right hb hinv
    have hs0 : ‖u - v‖ ^ 2 = 0 :=
      le_antisymm hsle (sq_nonneg ‖u - v‖)
    have hnorm : ‖u - v‖ = 0 := by
      nlinarith [norm_nonneg (u - v)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  have hRsurj : Function.Surjective Rlin :=
    Rlin.surjective_of_injective hRinj
  let g : osgm_point n := gradient f x
  let v : osgm_point n := -Rlin g
  have hvbound : ∀ t : ℝ,
      κStar⁻¹ * ‖v‖ ^ 2 ≤
          inner ℝ (Rlin v) ((fderiv ℝ (gradient f) (x + t • Rlin v)) (Rlin v)) ∧
        inner ℝ (Rlin v) ((fderiv ℝ (gradient f) (x + t • Rlin v)) (Rlin v)) ≤
          ‖v‖ ^ 2 := by
    intro t
    simpa only [Rlin] using hH (x + t • Rlin v) v
  have hvstep :=
    (htaylor x (Rlin v) (κStar⁻¹ * ‖v‖ ^ 2) (‖v‖ ^ 2) hvbound).2
  have hinner_step : inner ℝ g (Rlin v) = -‖Rlin g‖ ^ 2 := by
    rw [hRinner]
    simp [v, real_inner_self_eq_norm_sq]
  have hstep_point : x + Rlin v = x - Plin g := by
    simp only [v, map_neg, hRsquare, sub_eq_add_neg]
  have hdescent :
      f (x - Plin g) - f xStar ≤
        f x - f xStar - ‖Rlin g‖ ^ 2 / 2 := by
    rw [← hstep_point]
    calc
      f (x + Rlin v) - f xStar ≤
          (f x + inner ℝ (gradient f x) (Rlin v) + ‖v‖ ^ 2 / 2) - f xStar :=
        sub_le_sub_right hvstep _
      _ = f x - f xStar - ‖Rlin g‖ ^ 2 / 2 := by
        rw [← show gradient f x = g by rfl, hinner_step]
        simp only [v, norm_neg]
        ring
  obtain ⟨w, hw⟩ := hRsurj (xStar - x)
  have hwbound : ∀ t : ℝ,
      κStar⁻¹ * ‖w‖ ^ 2 ≤
          inner ℝ (Rlin w) ((fderiv ℝ (gradient f) (x + t • Rlin w)) (Rlin w)) ∧
        inner ℝ (Rlin w) ((fderiv ℝ (gradient f) (x + t • Rlin w)) (Rlin w)) ≤
          ‖w‖ ^ 2 := by
    intro t
    simpa only [Rlin] using hH (x + t • Rlin w) w
  have hwlower :=
    (htaylor x (Rlin w) (κStar⁻¹ * ‖w‖ ^ 2) (‖w‖ ^ 2) hwbound).1
  have hwpoint : x + Rlin w = xStar := by
    rw [hw]
    abel
  have hgap_pre :
      f x - f xStar ≤
        -inner ℝ (Rlin g) w - κStar⁻¹ * ‖w‖ ^ 2 / 2 := by
    rw [hwpoint] at hwlower
    rw [show gradient f x = g by rfl, hRinner] at hwlower
    linarith
  have hcauchy :
      -inner ℝ (Rlin g) w ≤ ‖Rlin g‖ * ‖w‖ := by
    simpa using real_inner_le_norm (-Rlin g) w
  have hkinv : κStar * κStar⁻¹ = 1 := by
    exact mul_inv_cancel₀ hκ.ne'
  have hyoung :
      ‖Rlin g‖ * ‖w‖ ≤
        κStar / 2 * ‖Rlin g‖ ^ 2 + κStar⁻¹ / 2 * ‖w‖ ^ 2 := by
    nlinarith [sq_nonneg (κStar * ‖Rlin g‖ - ‖w‖)]
  have hgap_bound :
      f x - f xStar ≤ κStar / 2 * ‖Rlin g‖ ^ 2 := by
    linarith
  have hweighted :
      κStar⁻¹ * (f x - f xStar) ≤ ‖Rlin g‖ ^ 2 / 2 := by
    nlinarith
  unfold ratio_surrogate
  rw [div_le_iff₀ hgap]
  have hfinal :
      f (x - Plin g) - f xStar ≤
        (1 - κStar⁻¹) * (f x - f xStar) := by
    calc
      f (x - Plin g) - f xStar ≤
          f x - f xStar - ‖Rlin g‖ ^ 2 / 2 := hdescent
      _ ≤ (1 - κStar⁻¹) * (f x - f xStar) := by
        nlinarith
  simpa only [g, Plin] using hfinal

@[blueprint "lem:ratio-surrogate-first-order-bound"
  (statement := /-- Let \(f:\mathbb{R}^n\to\mathbb{R}\) satisfy the objective assumptions with minimizer \(x^\star\), and let \(x\in\mathbb{R}^n\) satisfy \(f(x)>f(x^\star)\).  Then, for all matrices \(P,Q\),
  \[
    r_x(P)-r_x(Q)\leq
      \left\langle\nabla_P r_x(P),P-Q\right\rangle_F.
  \] -/)
  (proof := /-- Apply the strong-convexity inequality from \cref{def:osgm-objective-assumptions} at the two trial points \(x-P\nabla f(x)\) and \(x-Q\nabla f(x)\), and discard its nonnegative quadratic term.  Divide the resulting first-order inequality by the positive gap \(f(x)-f(x^\star)\).  The chain rule for \cref{def:ratio-surrogate} identifies the remaining directional derivative with \(\langle\nabla_P r_x(P),P-Q\rangle_F\). -/)
  (title := /-- First-order inequality for the ratio surrogate -/)
  (latexEnv := "lemma")]
lemma ratio_surrogate_first_order_bound {n : ℕ}
    (f : osgm_point n → ℝ) (xStar x : osgm_point n) (L μ : ℝ)
    (hobjective : osgm_objective_assumptions f xStar L μ)
    (hgap : 0 < f x - f xStar)
    (P Q : osgm_matrix n) :
    ratio_surrogate f xStar x P - ratio_surrogate f xStar x Q ≤
      inner ℝ (gradient (ratio_surrogate f xStar x) P) (P - Q) := by
  rcases hobjective with
    ⟨hL, hμ, hfdiff, hgraddiff, hmin, hsmooth, hstrong⟩
  let g : osgm_point n := gradient f x
  let Blin : osgm_matrix n →ₗ[ℝ] osgm_point n :=
    { toFun := fun R =>
        Matrix.toEuclideanLin (osgm_matrix_view R) g
      map_add' := by
        intro A B
        apply PiLp.ext
        intro i
        simp [osgm_matrix_view, Matrix.toEuclideanLin_apply,
          Matrix.mulVec, dotProduct, Finset.sum_add_distrib, add_mul]
      map_smul' := by
        intro c A
        apply PiLp.ext
        intro i
        simp [osgm_matrix_view, Matrix.toEuclideanLin_apply,
          Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] }
  let B : osgm_matrix n →L[ℝ] osgm_point n :=
    LinearMap.toContinuousLinearMap Blin
  let step : osgm_matrix n → osgm_point n := fun R =>
    x - B R
  have hμterm : 0 ≤ μ / 2 * ‖step Q - step P‖ ^ 2 :=
    mul_nonneg (le_of_lt (half_pos hμ)) (sq_nonneg _)
  have hbase :
      f (step P) - f (step Q) ≤
        inner ℝ (gradient f (step P)) (step P - step Q) := by
    have hs := hstrong (step Q) (step P)
    have hinner :
        inner ℝ (gradient f (step P)) (step Q - step P) =
          -inner ℝ (gradient f (step P)) (step P - step Q) := by
      rw [← inner_neg_right]
      congr 1
      abel
    rw [hinner] at hs
    nlinarith
  have hstepderiv : HasFDerivAt step (-B) P := by
    simpa only [step] using B.hasFDerivAt.const_sub x
  have hcomp :
      HasFDerivAt (f ∘ step)
        ((fderiv ℝ f (step P)).comp (-B)) P := by
    exact HasFDerivAt.comp P (hfdiff (step P)).hasFDerivAt hstepderiv
  have hratio :
      HasFDerivAt (ratio_surrogate f xStar x)
        ((f x - f xStar)⁻¹ •
          ((fderiv ℝ f (step P)).comp (-B))) P := by
    have h := HasFDerivAt.const_smul
      (hcomp.sub_const (f xStar)) (f x - f xStar)⁻¹
    apply h.congr_of_eventuallyEq
    filter_upwards [] with R
    simp only [ratio_surrogate, step, B, Blin, g, Function.comp_apply,
      Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  have hstepdiff : (-B) (P - Q) = step P - step Q := by
    rw [map_sub]
    dsimp only [step]
    simp only [ContinuousLinearMap.neg_apply]
    abel
  have hdirection :
      inner ℝ (gradient (ratio_surrogate f xStar x) P) (P - Q) =
        inner ℝ (gradient f (step P)) (step P - step Q) /
          (f x - f xStar) := by
    rw [inner_gradient_left, hratio.fderiv]
    simp only [ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, hstepdiff, smul_eq_mul,
      ← inner_gradient_left, div_eq_mul_inv]
    ring
  rw [hdirection]
  change
    (f (step P) - f xStar) / (f x - f xStar) -
        (f (step Q) - f xStar) / (f x - f xStar) ≤
      inner ℝ (gradient f (step P)) (step P - step Q) /
        (f x - f xStar)
  rw [← sub_div]
  apply (div_le_div_iff_of_pos_right hgap).2
  linarith

@[blueprint "lem:ratio-surrogate-gradient-self-bound"
  (statement := /-- Let \(n\in\mathbb{N}\), let \(f:\mathbb{R}^n\to\mathbb{R}\), let \(x^\star,x\in\mathbb{R}^n\), and let \(L,\mu\in\mathbb{R}\).  Assume that \(L>0\), \(\mu>0\), \(f\) is differentiable, \(\nabla f\) is differentiable at every point, and \(x^\star\) is a global minimizer of \(f\).  Assume further that, for every \(u,v\in\mathbb{R}^n\),
  \[
    \left|f(u)-f(v)-\langle\nabla f(v),u-v\rangle\right|
      \leq \frac{L}{2}\lVert u-v\rVert^2
  \]
  and
  \[
    \frac{\mu}{2}\lVert u-v\rVert^2
      \leq f(u)-f(v)-\langle\nabla f(v),u-v\rangle.
  \]
  If \(f(x)-f(x^\star)>0\), then, for every \(P\in\mathbb{R}^{n\times n}\),
  \[
    \left\lVert\nabla_P r_x(P)\right\rVert_F^2
      \leq 4L^2 r_x(P).
  \] -/)
  (proof := /-- Put \(g=\nabla f(x)\), \(y=x-Pg\), and \(\Delta=f(x)-f(x^\star)>0\).  The upper smoothness inequality from \cref{def:osgm-objective-assumptions}, applied at an arbitrary point \(z\) with trial point \(z-L^{-1}\nabla f(z)\), gives
  \[
    f\bigl(z-L^{-1}\nabla f(z)\bigr)
      \leq f(z)-\frac{1}{2L}\lVert\nabla f(z)\rVert^2.
  \]
  Since \(x^\star\) is a global minimizer and \(L>0\), it follows that
  \[
    \lVert\nabla f(z)\rVert^2
      \leq 2L\bigl(f(z)-f(x^\star)\bigr)
  \]
  for every \(z\).  Apply this estimate at \(x\) and at \(y\).

  By the chain rule and \cref{def:ratio-surrogate}, the matrix gradient of \(r_x\) at \(P\) is the rank-one matrix
  \[
    -\frac{\nabla f(y)g^{\mathsf T}}{\Delta}.
  \]
  The Frobenius norm of an outer product is the product of the Euclidean norms of its factors.  Consequently,
  \[
    \left\lVert\nabla_P r_x(P)\right\rVert_F^2
      =\frac{\lVert\nabla f(y)\rVert^2\lVert g\rVert^2}{\Delta^2}
      \leq
      \frac{4L^2\bigl(f(y)-f(x^\star)\bigr)\Delta}{\Delta^2}
      =4L^2r_x(P),
  \]
  where the last equality again uses \cref{def:ratio-surrogate} and the positivity of \(\Delta\). -/)
  (title := /-- Self-bound for the ratio-surrogate gradient -/)
  (latexEnv := "lemma")]
lemma ratio_surrogate_gradient_self_bound {n : ℕ}
    (f : osgm_point n → ℝ) (xStar x : osgm_point n) (L μ : ℝ)
    (hobjective : osgm_objective_assumptions f xStar L μ)
    (hgap : 0 < f x - f xStar) (P : osgm_matrix n) :
    ‖gradient (ratio_surrogate f xStar x) P‖ ^ 2 ≤
      4 * L ^ 2 * ratio_surrogate f xStar x P := by
  rcases hobjective with
    ⟨hL, hμ, hfdiff, hgraddiff, hmin, hsmooth, hstrong⟩
  let g : osgm_point n := gradient f x
  let Blin : osgm_matrix n →ₗ[ℝ] osgm_point n :=
    { toFun := fun R =>
        Matrix.toEuclideanLin (osgm_matrix_view R) g
      map_add' := by
        intro A B
        apply PiLp.ext
        intro i
        simp [osgm_matrix_view, Matrix.toEuclideanLin_apply,
          Matrix.mulVec, dotProduct, Finset.sum_add_distrib, add_mul]
      map_smul' := by
        intro c A
        apply PiLp.ext
        intro i
        simp [osgm_matrix_view, Matrix.toEuclideanLin_apply,
          Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] }
  let B : osgm_matrix n →L[ℝ] osgm_point n :=
    LinearMap.toContinuousLinearMap Blin
  let step : osgm_matrix n → osgm_point n := fun R =>
    x - B R
  have hstepderiv : HasFDerivAt step (-B) P := by
    simpa only [step] using B.hasFDerivAt.const_sub x
  have hcomp :
      HasFDerivAt (f ∘ step)
        ((fderiv ℝ f (step P)).comp (-B)) P := by
    exact HasFDerivAt.comp P (hfdiff (step P)).hasFDerivAt hstepderiv
  have hratio :
      HasFDerivAt (ratio_surrogate f xStar x)
        ((f x - f xStar)⁻¹ •
          ((fderiv ℝ f (step P)).comp (-B))) P := by
    have h := HasFDerivAt.const_smul
      (hcomp.sub_const (f xStar)) (f x - f xStar)⁻¹
    apply h.congr_of_eventuallyEq
    filter_upwards [] with R
    simp only [ratio_surrogate, step, B, Blin, g, Function.comp_apply,
      Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  let outer : osgm_matrix n := WithLp.toLp 2 (fun ij =>
    -(gradient f (step P) ij.1 * g ij.2) / (f x - f xStar))
  have houter_inner (D : osgm_matrix n) :
      inner ℝ outer D =
        inner ℝ (gradient f (step P)) ((-B) D) /
          (f x - f xStar) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct,
      EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ ij, D ij * outer ij) =
      (∑ i, ((-B) D) i * gradient f (step P) i) /
        (f x - f xStar)
    have hBD : B D =
        Matrix.toEuclideanLin (osgm_matrix_view D) g := rfl
    simp only [outer, ContinuousLinearMap.neg_apply, hBD,
      Matrix.toEuclideanLin_apply, osgm_matrix_view, Matrix.mulVec,
      dotProduct, PiLp.neg_apply]
    rw [Fintype.sum_prod_type]
    rw [eq_div_iff hgap.ne']
    rw [Finset.sum_mul Finset.univ]
    congr with i
    simp only [Prod.fst, Prod.snd]
    rw [Finset.sum_mul Finset.univ]
    rw [neg_mul, Finset.sum_mul Finset.univ,
      ← Finset.sum_neg_distrib (s := Finset.univ)]
    congr with j
    field_simp [hgap.ne']
  have hdirection (D : osgm_matrix n) :
      inner ℝ (gradient (ratio_surrogate f xStar x) P) D =
        inner ℝ (gradient f (step P)) ((-B) D) /
          (f x - f xStar) := by
    rw [inner_gradient_left, hratio.fderiv]
    simp only [ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul,
      ← inner_gradient_left, div_eq_mul_inv]
    ring
  have hgradient :
      gradient (ratio_surrogate f xStar x) P = outer := by
    apply ext_inner_left ℝ
    intro D
    calc
      inner ℝ D (gradient (ratio_surrogate f xStar x) P) =
          inner ℝ (gradient (ratio_surrogate f xStar x) P) D :=
        real_inner_comm _ _
      _ = inner ℝ (gradient f (step P)) ((-B) D) /
          (f x - f xStar) := hdirection D
      _ = inner ℝ outer D := (houter_inner D).symm
      _ = inner ℝ D outer := real_inner_comm _ _
  have houter_norm :
      ‖outer‖ ^ 2 =
        ‖gradient f (step P)‖ ^ 2 * ‖g‖ ^ 2 /
          (f x - f xStar) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      EuclideanSpace.norm_sq_eq]
    simp only [outer, Real.norm_eq_abs, abs_div, abs_neg, abs_mul, sq_abs]
    rw [Fintype.sum_prod_type]
    simp only [Prod.fst, Prod.snd, div_pow, mul_pow, sq_abs,
      abs_of_pos hgap, div_eq_mul_inv]
    simp_rw [← Finset.sum_mul Finset.univ]
    rw [← Fintype.sum_mul_sum, inv_pow]
  have hgradient_bound (z : osgm_point n) :
      ‖gradient f z‖ ^ 2 ≤ 2 * L * (f z - f xStar) := by
    let gz : osgm_point n := gradient f z
    let trial : osgm_point n := z - L⁻¹ • gz
    have hs := hsmooth trial z
    have hupper :
        f trial - f z - inner ℝ (gradient f z) (trial - z) ≤
          L / 2 * ‖trial - z‖ ^ 2 :=
      (le_abs_self _).trans hs
    have hdiff : trial - z = -L⁻¹ • gz := by
      simp only [trial]
      module
    rw [hdiff] at hupper
    have hLinv_nonneg : 0 ≤ L⁻¹ := (inv_pos.mpr hL).le
    have hinner :
        inner ℝ (gradient f z) (-L⁻¹ • gz) =
          -L⁻¹ * ‖gz‖ ^ 2 := by
      simp only [gz, inner_neg_right, inner_smul_right,
        real_inner_self_eq_norm_sq, neg_mul]
    have hnorm :
        ‖-L⁻¹ • gz‖ ^ 2 = (L⁻¹) ^ 2 * ‖gz‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg hLinv_nonneg]
      ring
    rw [hinner, hnorm] at hupper
    have hcoef : L / 2 * (L⁻¹) ^ 2 = L⁻¹ / 2 := by
      field_simp [hL.ne']
    have hupper' :
        f trial - f z + L⁻¹ * ‖gz‖ ^ 2 ≤
          L⁻¹ / 2 * ‖gz‖ ^ 2 := by
      calc
        f trial - f z + L⁻¹ * ‖gz‖ ^ 2 =
            f trial - f z - (-L⁻¹ * ‖gz‖ ^ 2) := by ring
        _ ≤ L / 2 * ((L⁻¹) ^ 2 * ‖gz‖ ^ 2) := hupper
        _ = L⁻¹ / 2 * ‖gz‖ ^ 2 := by rw [← mul_assoc, hcoef]
    have htrial_min := hmin trial
    have hpre : L⁻¹ * ‖gz‖ ^ 2 ≤ 2 * (f z - f xStar) := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hpre hL.le
    have hLinv : L * L⁻¹ = 1 := mul_inv_cancel₀ hL.ne'
    rw [← mul_assoc, hLinv, one_mul] at hmul
    simpa only [gz] using (show
      ‖gz‖ ^ 2 ≤ 2 * L * (f z - f xStar) by
        nlinarith)
  have hx := hgradient_bound x
  have hy := hgradient_bound (step P)
  have hxgap : 0 ≤ f x - f xStar := hgap.le
  have hygap : 0 ≤ f (step P) - f xStar := by
    linarith [hmin (step P)]
  have hyrhs : 0 ≤ 2 * L * (f (step P) - f xStar) :=
    mul_nonneg (mul_nonneg (by norm_num) hL.le) hygap
  have hprod := mul_le_mul hy hx (sq_nonneg ‖gradient f x‖) hyrhs
  have hproduct :
      ‖gradient f (step P)‖ ^ 2 * ‖g‖ ^ 2 ≤
        4 * L ^ 2 * (f (step P) - f xStar) *
          (f x - f xStar) := by
    simpa only [g] using (show
      ‖gradient f (step P)‖ ^ 2 * ‖gradient f x‖ ^ 2 ≤
        4 * L ^ 2 * (f (step P) - f xStar) *
          (f x - f xStar) by
      nlinarith)
  rw [hgradient, houter_norm]
  unfold ratio_surrogate
  apply (div_le_iff₀ (sq_pos_of_pos hgap)).2
  calc
    ‖gradient f (step P)‖ ^ 2 * ‖g‖ ^ 2 ≤
        4 * L ^ 2 * (f (step P) - f xStar) *
          (f x - f xStar) := hproduct
    _ = 4 * L ^ 2 *
          ((f (x - Matrix.toEuclideanLin (osgm_matrix_view P)
              (gradient f x)) - f xStar) /
            (f x - f xStar)) *
          (f x - f xStar) ^ 2 := by
      rw [show step P =
        x - Matrix.toEuclideanLin (osgm_matrix_view P)
          (gradient f x) by rfl]
      field_simp [hgap.ne']

@[blueprint "lem:metric-projection-comparator-distance"
  (statement := /-- Let \(\mathcal P\subseteq\mathbb{R}^{n\times n}\) be convex, and let \(\Pi_{\mathcal P}\) be a metric projection onto \(\mathcal P\).  Then, for every matrix \(A\) and every \(Q\in\mathcal P\),
  \[
    \left\lVert\Pi_{\mathcal P}(A)-Q\right\rVert_F^2
      \leq \left\lVert A-Q\right\rVert_F^2.
  \] -/)
  (proof := /-- Put \(Y=\Pi_{\mathcal P}(A)\).  The metric-minimality property in \cref{def:metric-projection-map}, applied to every point \(Y+t(Q-Y)\) of the feasible segment, implies the variational inequality
  \(\langle Y-A,Q-Y\rangle_F\geq0\): if this inner product were negative, a sufficiently small positive \(t\leq1\) would make \(Y+t(Q-Y)\) strictly closer to \(A\) than \(Y\).  Expanding
  \[
    A-Q=(A-Y)+(Y-Q)
  \]
  and using the variational inequality gives
  \(\lVert Y-Q\rVert_F^2\leq\lVert A-Q\rVert_F^2\). -/)
  (title := /-- Comparator contraction of a metric projection -/)
  (latexEnv := "lemma")]
lemma metric_projection_comparator_distance {n : ℕ}
    (Pset : Set (osgm_matrix n))
    (project : osgm_matrix n → osgm_matrix n)
    (hconvex : Convex ℝ Pset)
    (hprojection : metric_projection_map Pset project)
    (A Q : osgm_matrix n) (hQ : Q ∈ Pset) :
    ‖project A - Q‖ ^ 2 ≤ ‖A - Q‖ ^ 2 := by
  let Y : osgm_matrix n := project A
  have hY : Y ∈ Pset := (hprojection A).1
  have hbest : ∀ Z ∈ Pset, ‖Y - A‖ ≤ ‖Z - A‖ := by
    intro Z hZ
    exact (hprojection A).2 Z hZ
  have hvariational :
      0 ≤ inner ℝ (Y - A) (Q - Y) := by
    by_contra hnot
    have hc : inner ℝ (Y - A) (Q - Y) < 0 :=
      lt_of_not_ge hnot
    have hw : Q - Y ≠ 0 := by
      intro hw
      rw [hw, inner_zero_right] at hc
      exact (lt_irrefl 0 hc)
    have hd : 0 < ‖Q - Y‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
    let t : ℝ := min (1 / 2) (-inner ℝ (Y - A) (Q - Y) / ‖Q - Y‖ ^ 2)
    have htpos : 0 < t := by
      apply lt_min
      · norm_num
      · exact div_pos (neg_pos.mpr hc) hd
    have hthalf : t ≤ 1 / 2 := min_le_left _ _
    have htone : t ≤ 1 := by linarith
    have htratio :
        t ≤ -inner ℝ (Y - A) (Q - Y) / ‖Q - Y‖ ^ 2 :=
      min_le_right _ _
    have htbound :
        t * ‖Q - Y‖ ^ 2 ≤ -inner ℝ (Y - A) (Q - Y) := by
      exact (le_div_iff₀ hd).mp htratio
    have hcoefficient :
        2 * inner ℝ (Y - A) (Q - Y) + t * ‖Q - Y‖ ^ 2 < 0 := by
      linarith
    have hdecrease :
        2 * t * inner ℝ (Y - A) (Q - Y) +
            t ^ 2 * ‖Q - Y‖ ^ 2 < 0 := by
      have hm := mul_neg_of_pos_of_neg htpos hcoefficient
      nlinarith
    let Z : osgm_matrix n := (1 - t) • Y + t • Q
    have hZ : Z ∈ Pset :=
      hconvex hY hQ (sub_nonneg.mpr htone) htpos.le (by ring)
    have hZA :
        Z - A = (Y - A) + t • (Q - Y) := by
      dsimp only [Z]
      module
    have hexpand :
        ‖Z - A‖ ^ 2 =
          ‖Y - A‖ ^ 2 +
            2 * t * inner ℝ (Y - A) (Q - Y) +
              t ^ 2 * ‖Q - Y‖ ^ 2 := by
      rw [hZA, ← real_inner_self_eq_norm_sq]
      simp only [inner_add_left, inner_add_right, inner_smul_left,
        inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm,
        RCLike.conj_to_real]
      ring
    have hnorm := hbest Z hZ
    have hsquares : ‖Y - A‖ ^ 2 ≤ ‖Z - A‖ ^ 2 := by
      nlinarith [norm_nonneg (Y - A), norm_nonneg (Z - A)]
    linarith
  have hidentity :
      ‖A - Q‖ ^ 2 =
        ‖A - Y‖ ^ 2 + ‖Y - Q‖ ^ 2 +
          2 * inner ℝ (A - Y) (Y - Q) := by
    rw [← real_inner_self_eq_norm_sq]
    have hvec : A - Q = (A - Y) + (Y - Q) := by abel
    rw [hvec]
    simp only [inner_add_left, inner_add_right,
      real_inner_self_eq_norm_sq, real_inner_comm]
    ring
  have hcross : 0 ≤ inner ℝ (A - Y) (Y - Q) := by
    have hneg :
        inner ℝ (A - Y) (Y - Q) =
          inner ℝ (Y - A) (Q - Y) := by
      rw [show A - Y = -(Y - A) by abel,
        show Y - Q = -(Q - Y) by abel, inner_neg_left, inner_neg_right,
        neg_neg]
    rw [hneg]
    exact hvariational
  dsimp only [Y] at hidentity ⊢
  rw [hidentity]
  nlinarith [sq_nonneg ‖A - project A‖]

@[blueprint "lem:self-bounding-projected-online-gradient-sum-bound"
  (statement := /-- Let \(n,K\in\mathbb N\) with \(K\geq1\), let \(L>0\), and let \(0<\eta\leq(4L^2)^{-1}\).  Let \(\ell_k:\mathbb R^{n\times n}\to\mathbb R\) be a sequence of losses, and let \(P_k,G_k\in\mathbb R^{n\times n}\) be sequences of matrices.  Suppose that \(\mathcal P\subseteq\mathbb R^{n\times n}\) is convex, that \(\Pi_{\mathcal P}\) is a metric projection onto \(\mathcal P\), and that \(Q\in\mathcal P\).  Assume that, for every \(1\leq k\leq K\),
  \[
    P_{k+1}=\Pi_{\mathcal P}(P_k-\eta G_k),\qquad
    \ell_k(P_k)-\ell_k(Q)\leq\langle G_k,P_k-Q\rangle_F,
  \]
  \[
    \lVert G_k\rVert_F^2\leq4L^2\ell_k(P_k),
    \qquad \ell_k(Q)\leq1.
  \]
  Then
  \[
    \sum_{k=1}^K\bigl(\ell_k(P_k)-\ell_k(Q)\bigr)
      \leq\frac{\lVert Q-P_1\rVert_F^2}{\eta}
        +4\eta L^2K.
  \] -/)
  (proof := /-- Apply \cref{lem:metric-projection-comparator-distance} to the \(k\)-th projected update and expand the squared norm.  The first-order inequality gives
  \[
    2\eta\bigl(\ell_k(P_k)-\ell_k(Q)\bigr)
      \leq \lVert P_k-Q\rVert_F^2-\lVert P_{k+1}-Q\rVert_F^2
        +\eta^2\lVert G_k\rVert_F^2.
  \]
  Sum these inequalities from \(1\) to \(K\), telescope the squared distances, discard the nonnegative terminal distance, and use the gradient self-bound.  If
  \[
    R=\sum_{k=1}^K\bigl(\ell_k(P_k)-\ell_k(Q)\bigr),
  \]
  then \(\sum_k\ell_k(P_k)=R+\sum_k\ell_k(Q)\leq R+K\), and hence
  \[
    2\eta R\leq\lVert P_1-Q\rVert_F^2
      +4\eta^2L^2(R+K).
  \]
  The stepsize cap implies \(4\eta^2L^2\leq\eta\).  The asserted right-hand side is nonnegative, so the result is immediate when \(R\leq0\).  If \(R>0\), multiplication of the coefficient bound by \(R\) and the preceding estimate give
  \[
    \eta R\leq\lVert P_1-Q\rVert_F^2+4\eta^2L^2K.
  \]
  Dividing by \(\eta>0\) and using \(\lVert P_1-Q\rVert_F=\lVert Q-P_1\rVert_F\) proves the claim. -/)
  (title := /-- Projected online-gradient bound for self-bounding losses -/)
  (latexEnv := "lemma")]
lemma self_bounding_projected_online_gradient_sum_bound {n K : ℕ}
    (loss : ℕ → osgm_matrix n → ℝ)
    (P G : ℕ → osgm_matrix n) (Pset : Set (osgm_matrix n))
    (project : osgm_matrix n → osgm_matrix n) (Q : osgm_matrix n)
    (L η : ℝ) (hK : 0 < K) (hL : 0 < L) (hη : 0 < η)
    (hηcap : η ≤ 1 / (4 * L ^ 2))
    (hconvex : Convex ℝ Pset)
    (hprojection : metric_projection_map Pset project)
    (hQ : Q ∈ Pset)
    (hupdate : ∀ k, 1 ≤ k → k ≤ K →
      P (k + 1) = project (P k - η • G k))
    (hfirst : ∀ k, 1 ≤ k → k ≤ K →
      loss k (P k) - loss k Q ≤ inner ℝ (G k) (P k - Q))
    (hself : ∀ k, 1 ≤ k → k ≤ K →
      ‖G k‖ ^ 2 ≤ 4 * L ^ 2 * loss k (P k))
    (hcomparator : ∀ k, 1 ≤ k → k ≤ K → loss k Q ≤ 1) :
    (∑ k ∈ Finset.Icc 1 K, (loss k (P k) - loss k Q)) ≤
      ‖Q - P 1‖ ^ 2 / η + 4 * η * L ^ 2 * (K : ℝ) := by
  have hKone : 1 ≤ K := by omega
  have hstep (k : ℕ) (hk : k ∈ Finset.Icc 1 K) :
      2 * η * (loss k (P k) - loss k Q) ≤
        ‖P k - Q‖ ^ 2 - ‖P (k + 1) - Q‖ ^ 2 + η ^ 2 * ‖G k‖ ^ 2 := by
    have hk' := Finset.mem_Icc.mp hk
    have hp := metric_projection_comparator_distance Pset project hconvex hprojection
      (P k - η • G k) Q hQ
    rw [← hupdate k hk'.1 hk'.2] at hp
    have hexpand :
        ‖P k - η • G k - Q‖ ^ 2 =
          ‖P k - Q‖ ^ 2 -
            2 * η * inner ℝ (G k) (P k - Q) + η ^ 2 * ‖G k‖ ^ 2 := by
      have hvec : P k - η • G k - Q = (P k - Q) - η • G k := by module
      rw [hvec, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, abs_of_pos hη]
      simp only [inner_smul_right, RCLike.conj_to_real]
      rw [real_inner_comm]
      ring
    rw [hexpand] at hp
    have hf := mul_le_mul_of_nonneg_left (hfirst k hk'.1 hk'.2)
      (by positivity : 0 ≤ 2 * η)
    calc
      2 * η * (loss k (P k) - loss k Q) ≤
          2 * η * inner ℝ (G k) (P k - Q) := hf
      _ ≤ ‖P k - Q‖ ^ 2 - ‖P (k + 1) - Q‖ ^ 2 + η ^ 2 * ‖G k‖ ^ 2 := by
        linarith [hp]
  have hsum := Finset.sum_le_sum fun k hk => hstep k hk
  have hforward := Finset.sum_Icc_sub hKone (fun k => ‖P k - Q‖ ^ 2)
  have htel :
      (∑ k ∈ Finset.Icc 1 K,
        (‖P k - Q‖ ^ 2 - ‖P (k + 1) - Q‖ ^ 2)) =
        ‖P 1 - Q‖ ^ 2 - ‖P (K + 1) - Q‖ ^ 2 := by
    calc
      (∑ k ∈ Finset.Icc 1 K,
          (‖P k - Q‖ ^ 2 - ‖P (k + 1) - Q‖ ^ 2)) =
          ∑ k ∈ Finset.Icc 1 K,
            -(‖P (k + 1) - Q‖ ^ 2 - ‖P k - Q‖ ^ 2) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = -(∑ k ∈ Finset.Icc 1 K,
          (‖P (k + 1) - Q‖ ^ 2 - ‖P k - Q‖ ^ 2)) := by
        rw [Finset.sum_neg_distrib]
      _ = -(‖P (K + 1) - Q‖ ^ 2 - ‖P 1 - Q‖ ^ 2) := by rw [hforward]
      _ = ‖P 1 - Q‖ ^ 2 - ‖P (K + 1) - Q‖ ^ 2 := by ring
  have henergy :
      2 * η * (∑ k ∈ Finset.Icc 1 K, (loss k (P k) - loss k Q)) ≤
        ‖P 1 - Q‖ ^ 2 - ‖P (K + 1) - Q‖ ^ 2 +
          η ^ 2 * (∑ k ∈ Finset.Icc 1 K, ‖G k‖ ^ 2) := by
    calc
      2 * η * (∑ k ∈ Finset.Icc 1 K, (loss k (P k) - loss k Q)) =
          ∑ k ∈ Finset.Icc 1 K, 2 * η * (loss k (P k) - loss k Q) := by
            rw [Finset.mul_sum]
      _ ≤ ∑ k ∈ Finset.Icc 1 K,
          (‖P k - Q‖ ^ 2 - ‖P (k + 1) - Q‖ ^ 2 + η ^ 2 * ‖G k‖ ^ 2) := hsum
      _ = (∑ k ∈ Finset.Icc 1 K,
          (‖P k - Q‖ ^ 2 - ‖P (k + 1) - Q‖ ^ 2)) +
            ∑ k ∈ Finset.Icc 1 K, η ^ 2 * ‖G k‖ ^ 2 := by
              rw [Finset.sum_add_distrib]
      _ = ‖P 1 - Q‖ ^ 2 - ‖P (K + 1) - Q‖ ^ 2 +
          η ^ 2 * (∑ k ∈ Finset.Icc 1 K, ‖G k‖ ^ 2) := by
            rw [htel, Finset.mul_sum]
  have henergy' :
      2 * η * (∑ k ∈ Finset.Icc 1 K, (loss k (P k) - loss k Q)) ≤
        ‖P 1 - Q‖ ^ 2 + η ^ 2 * (∑ k ∈ Finset.Icc 1 K, ‖G k‖ ^ 2) := by
    nlinarith [sq_nonneg ‖P (K + 1) - Q‖]
  have hgrad :
      (∑ k ∈ Finset.Icc 1 K, ‖G k‖ ^ 2) ≤
        4 * L ^ 2 * (∑ k ∈ Finset.Icc 1 K, loss k (P k)) := by
    calc
      (∑ k ∈ Finset.Icc 1 K, ‖G k‖ ^ 2) ≤
          ∑ k ∈ Finset.Icc 1 K, 4 * L ^ 2 * loss k (P k) := by
            apply Finset.sum_le_sum
            intro k hk
            have hk' := Finset.mem_Icc.mp hk
            exact hself k hk'.1 hk'.2
      _ = 4 * L ^ 2 * (∑ k ∈ Finset.Icc 1 K, loss k (P k)) := by
        rw [Finset.mul_sum]
  have hcomp :
      (∑ k ∈ Finset.Icc 1 K, loss k Q) ≤ (K : ℝ) := by
    calc
      (∑ k ∈ Finset.Icc 1 K, loss k Q) ≤
          ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro k hk
            have hk' := Finset.mem_Icc.mp hk
            exact hcomparator k hk'.1 hk'.2
      _ = (K : ℝ) := by simp [Nat.card_Icc, hKone]
  have hloss :
      (∑ k ∈ Finset.Icc 1 K, loss k (P k)) ≤
        (∑ k ∈ Finset.Icc 1 K, (loss k (P k) - loss k Q)) + (K : ℝ) := by
    rw [Finset.sum_sub_distrib]
    linarith
  have hgradscaled := mul_le_mul_of_nonneg_left hgrad (sq_nonneg η)
  have hlossscaled := mul_le_mul_of_nonneg_left hloss
    (by positivity : 0 ≤ 4 * η ^ 2 * L ^ 2)
  have hcore :
      2 * η * (∑ k ∈ Finset.Icc 1 K, (loss k (P k) - loss k Q)) ≤
        ‖P 1 - Q‖ ^ 2 + 4 * η ^ 2 * L ^ 2 *
          ((∑ k ∈ Finset.Icc 1 K, (loss k (P k) - loss k Q)) + (K : ℝ)) := by
    nlinarith
  have hden : 0 < 4 * L ^ 2 := by positivity
  have hcapmul : η * (4 * L ^ 2) ≤ 1 := (le_div_iff₀ hden).mp hηcap
  have hcoef : 4 * η ^ 2 * L ^ 2 ≤ η := by
    have hm := mul_le_mul_of_nonneg_left hcapmul hη.le
    nlinarith
  by_cases hregret :
      (∑ k ∈ Finset.Icc 1 K, (loss k (P k) - loss k Q)) ≤ 0
  · have hrhs :
        0 ≤ ‖Q - P 1‖ ^ 2 / η + 4 * η * L ^ 2 * (K : ℝ) := by positivity
    exact hregret.trans hrhs
  · have hregretpos :
        0 < ∑ k ∈ Finset.Icc 1 K, (loss k (P k) - loss k Q) :=
      lt_of_not_ge hregret
    have hcoefregret := mul_le_mul_of_nonneg_right hcoef hregretpos.le
    have hmove :
        η * (∑ k ∈ Finset.Icc 1 K, (loss k (P k) - loss k Q)) ≤
          ‖P 1 - Q‖ ^ 2 + 4 * η ^ 2 * L ^ 2 * (K : ℝ) := by
      nlinarith [hcore, hcoefregret]
    have hdiv :
        (∑ k ∈ Finset.Icc 1 K, (loss k (P k) - loss k Q)) ≤
          (‖P 1 - Q‖ ^ 2 + 4 * η ^ 2 * L ^ 2 * (K : ℝ)) / η := by
      apply (le_div_iff₀ hη).mpr
      nlinarith [hmove]
    calc
      (∑ k ∈ Finset.Icc 1 K, (loss k (P k) - loss k Q)) ≤
          (‖P 1 - Q‖ ^ 2 + 4 * η ^ 2 * L ^ 2 * (K : ℝ)) / η := hdiv
      _ = ‖Q - P 1‖ ^ 2 / η + 4 * η * L ^ 2 * (K : ℝ) := by
        have hnorm : ‖P 1 - Q‖ = ‖Q - P 1‖ := norm_sub_rev _ _
        rw [hnorm]
        field_simp

@[blueprint "lem:osgm-self-bounding-stepsize-error-bound"
  (statement := /-- Let \(K\geq1\), \(L>0\), and \(D>0\).  If
  \[
    \eta=\min\left\{\frac1{4L^2},\frac{D}{2L\sqrt K}\right\},
  \]
  then
  \[
    \frac{D^2}{\eta K}+4\eta L^2
      \leq\max\left\{\frac{4LD}{\sqrt K},
        \frac{8L^2D^2}{K}\right\}.
  \] -/)
  (proof := /-- Since \(K>0\), its square root is positive.  If the distance-controlled term is the minimum, substitute
  \(\eta=D/(2L\sqrt K)\); the left-hand side is then \(4LD/\sqrt K\).
  If the capped term is the minimum, substitute \(\eta=1/(4L^2)\).  The condition selecting this branch implies
  \(D^2/K\geq1/(4L^2)\), and therefore
  \[
    \frac{D^2}{\eta K}+4\eta L^2
      =\frac{4L^2D^2}{K}+1
      \leq\frac{8L^2D^2}{K}.
  \]
  Each branch is bounded by the corresponding entry of the displayed maximum. -/)
  (title := /-- Error bound for the self-bounding OSGM stepsize -/)
  (latexEnv := "lemma")]
lemma osgm_self_bounding_stepsize_error_bound (L D η : ℝ) {K : ℕ}
    (hK : 0 < K) (hL : 0 < L) (hD : 0 < D)
    (heta : η = min (1 / (4 * L ^ 2))
      (D / (2 * L * Real.sqrt (K : ℝ)))) :
    D ^ 2 / (η * (K : ℝ)) + 4 * η * L ^ 2 ≤
      max (4 * L * D / Real.sqrt (K : ℝ))
        (8 * L ^ 2 * D ^ 2 / (K : ℝ)) := by
  subst η
  have hKr : (0 : ℝ) < (K : ℝ) := by
    exact_mod_cast hK
  have hs : 0 < Real.sqrt (K : ℝ) := Real.sqrt_pos.2 hKr
  rcases le_total (1 / (4 * L ^ 2))
      (D / (2 * L * Real.sqrt (K : ℝ))) with h | h
  · rw [min_eq_left h]
    refine le_trans ?_ (le_max_right _ _)
    field_simp [ne_of_gt hL, ne_of_gt hD, ne_of_gt hs, ne_of_gt hKr] at h ⊢
    nlinarith [Real.sq_sqrt (le_of_lt hKr)]
  · rw [min_eq_right h]
    refine le_trans ?_ (le_max_left _ _)
    field_simp [ne_of_gt hL, ne_of_gt hD, ne_of_gt hs, ne_of_gt hKr]
    nlinarith [Real.sq_sqrt (le_of_lt hKr)]

@[blueprint "lem:osgm-rx-learnability"
  (statement := /-- Let \(n,K\in\mathbb N\) with \(K\geq1\), and let \(L,\mu\in\mathbb R\) be positive.  Let \(f:\mathbb{R}^n\to\mathbb{R}\) satisfy the objective assumptions with constants \(L,\mu\) and global minimizer \(x^\star\).  Let \(\mathcal P\) be a closed convex feasible set with metric projection \(\Pi_{\mathcal P}\), and suppose that \((x^k,P_k)\) is an OSGM--Rx run with \(P_1\in\mathcal P\) and \(f(x^k)>f(x^\star)\) for \(1\leq k\leq K\).  Let \(P_r^\star\in\mathcal P\) be a comparator satisfying
  \[
    r_{x^k}(P_r^\star)\leq1\qquad(1\leq k\leq K),
  \]
  and set
  \[
    \eta=\min\left\{\frac1{4L^2},
      \frac{\lVert P_r^\star-P_1\rVert_F}{2L\sqrt K}\right\}.
  \]
  Then
  \[
    \overline r_K(P_k)\leq \overline r_K(P_r^\star)
      +\max\left\{\frac{4L\lVert P_r^\star-P_1\rVert_F}{\sqrt K},
      \frac{8L^2\lVert P_r^\star-P_1\rVert_F^2}{K}\right\}.
  \] -/)
  (proof := /-- Write \(g_k=\nabla_P r_{x^k}(P_k)\) and \(D=\lVert P_r^\star-P_1\rVert_F\).  For \(1\leq k\leq K\), positivity of the active objective gap permits \cref{lem:ratio-surrogate-first-order-bound} to be applied, giving
  \[
    r_{x^k}(P_k)-r_{x^k}(P_r^\star)
      \leq\langle g_k,P_k-P_r^\star\rangle_F.
  \]
  Moreover, \cref{lem:ratio-surrogate-gradient-self-bound} gives
  \[
    \lVert g_k\rVert_F^2\leq4L^2r_{x^k}(P_k).
  \]
  Suppose first that \(D>0\).  Both entries in the minimum defining \(\eta\) are positive, and hence \(\eta>0\); the same identity gives \(\eta\leq(4L^2)^{-1}\).  The matrix recurrence from \cref{def:osgm-rx-run}, the preceding first-order and self-bounding inequalities, the assumed comparator bound, convexity, \cref{def:metric-projection-map}, and feasibility of \(P_r^\star\) satisfy the hypotheses of \cref{lem:self-bounding-projected-online-gradient-sum-bound}.  Therefore
  \[
    \sum_{k=1}^K\bigl(r_{x^k}(P_k)-r_{x^k}(P_r^\star)\bigr)
      \leq \frac{D^2}{\eta}+4\eta L^2K.
  \]
  Divide by \(K>0\) and use \cref{def:ratio-average}.  The remaining error is
  \(D^2/(\eta K)+4\eta L^2\), which \cref{lem:osgm-self-bounding-stepsize-error-bound} bounds by the displayed maximum.

  Finally, if \(D=0\), then \(P_r^\star=P_1\) and the prescribed minimum gives \(\eta=0\).  Since \(P_r^\star\) is feasible, \cref{def:metric-projection-map} gives \(\Pi_{\mathcal P}(P_r^\star)=P_r^\star\).  Induction in \cref{def:osgm-rx-run} yields \(P_k=P_r^\star\) for \(1\leq k\leq K\).  The two averages in \cref{def:ratio-average} are equal, while both entries of the maximum vanish. -/)
  (title := /-- Learnability of the ratio surrogate -/)
  (latexEnv := "lemma")]
lemma osgm_rx_learnability {n K : ℕ} (f : osgm_point n → ℝ)
    (xStar : osgm_point n) (x : ℕ → osgm_point n)
    (P : ℕ → osgm_matrix n) (Pset : Set (osgm_matrix n))
    (project : osgm_matrix n → osgm_matrix n) (PStar : osgm_matrix n)
    (L μ η : ℝ) (hK : 0 < K)
    (hobjective : osgm_objective_assumptions f xStar L μ)
    (hclosed : IsClosed Pset) (hconvex : Convex ℝ Pset)
    (hprojection : metric_projection_map Pset project)
    (hPone : P 1 ∈ Pset) (hPStar : PStar ∈ Pset)
    (hrun : osgm_rx_run f xStar x P project η K)
    (hpositive : positive_objective_gaps f xStar x K)
    (hcomparator : ∀ k, 1 ≤ k → k ≤ K →
      ratio_surrogate f xStar (x k) PStar ≤ 1)
    (heta : η = min (1 / (4 * L ^ 2))
      (‖PStar - P 1‖ / (2 * L * Real.sqrt (K : ℝ)))) :
    ratio_average f xStar x P K ≤
      ratio_average f xStar x (fun _ => PStar) K +
        max (4 * L * ‖PStar - P 1‖ / Real.sqrt (K : ℝ))
          (8 * L ^ 2 * ‖PStar - P 1‖ ^ 2 / (K : ℝ)) := by
  have hL : 0 < L := hobjective.1
  have hKr : (0 : ℝ) < (K : ℝ) := by
    exact_mod_cast hK
  by_cases hDzero : ‖PStar - P 1‖ = 0
  · have hPoneStar : P 1 = PStar := by
      exact (sub_eq_zero.mp (norm_eq_zero.mp hDzero)).symm
    have hcap : 0 ≤ 1 / (4 * L ^ 2) := by positivity
    have hηzero : η = 0 := by
      rw [heta, hDzero, zero_div, min_eq_right hcap]
    have hfixed (Q : osgm_matrix n) (hQ : Q ∈ Pset) : project Q = Q := by
      have hdist := (hprojection Q).2 Q hQ
      have hnorm : ‖project Q - Q‖ = 0 := by
        apply le_antisymm
        · simpa using hdist
        · exact norm_nonneg _
      exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
    have hP : ∀ k, 1 ≤ k → k ≤ K → P k = PStar := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
          intro hk1 hkK
          by_cases hkEq : k = 1
          · subst k
            exact hPoneStar
          · have hpred1 : 1 ≤ k - 1 := by omega
            have hpredlt : k - 1 < k := by omega
            have hprev := ih (k - 1) hpredlt hpred1 (by omega)
            have hupdate := hrun.2 (k - 1) hpred1 (by omega)
            rw [show k - 1 + 1 = k by omega] at hupdate
            rw [hηzero, zero_smul, sub_zero, hprev,
              hfixed PStar hPStar] at hupdate
            exact hupdate
    have havg : ratio_average f xStar x P K =
        ratio_average f xStar x (fun _ => PStar) K := by
      unfold ratio_average
      apply congrArg (fun z : ℝ => z / (K : ℝ))
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_Icc.mp hk
      rw [hP k hk'.1 hk'.2]
    rw [havg, hDzero]
    simp
  · have hDpos : 0 < ‖PStar - P 1‖ := by
      exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hDzero)
    have hsqrt : 0 < Real.sqrt (K : ℝ) := Real.sqrt_pos.2 hKr
    have hcap : 0 < 1 / (4 * L ^ 2) := by positivity
    have hdiststep :
        0 < ‖PStar - P 1‖ / (2 * L * Real.sqrt (K : ℝ)) := by
      positivity
    have hηpos : 0 < η := by
      rw [heta]
      exact lt_min hcap hdiststep
    have hηcap : η ≤ 1 / (4 * L ^ 2) := by
      rw [heta]
      exact min_le_left _ _
    have hsum :
        (∑ k ∈ Finset.Icc 1 K,
          (ratio_surrogate f xStar (x k) (P k) -
            ratio_surrogate f xStar (x k) PStar)) ≤
          ‖PStar - P 1‖ ^ 2 / η + 4 * η * L ^ 2 * (K : ℝ) := by
      refine self_bounding_projected_online_gradient_sum_bound
        (loss := fun k Q => ratio_surrogate f xStar (x k) Q)
        (P := P)
        (G := fun k => gradient (ratio_surrogate f xStar (x k)) (P k))
        (Pset := Pset) (project := project) (Q := PStar)
        (L := L) (η := η) hK hL hηpos hηcap hconvex hprojection hPStar
        hrun.2 ?_ ?_ hcomparator
      · intro k hk1 hkK
        exact ratio_surrogate_first_order_bound f xStar (x k) L μ hobjective
          (hpositive k hk1 hkK) (P k) PStar
      · intro k hk1 hkK
        exact ratio_surrogate_gradient_self_bound f xStar (x k) L μ hobjective
          (hpositive k hk1 hkK) (P k)
    have hsumdiff :
        (∑ k ∈ Finset.Icc 1 K, ratio_surrogate f xStar (x k) (P k)) -
            (∑ k ∈ Finset.Icc 1 K, ratio_surrogate f xStar (x k) PStar) ≤
          ‖PStar - P 1‖ ^ 2 / η + 4 * η * L ^ 2 * (K : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      exact hsum
    have hscaled := (div_le_div_iff_of_pos_right hKr).2 hsumdiff
    have hratio :
        ((∑ k ∈ Finset.Icc 1 K, ratio_surrogate f xStar (x k) (P k)) -
            (∑ k ∈ Finset.Icc 1 K, ratio_surrogate f xStar (x k) PStar)) /
              (K : ℝ) ≤
          ‖PStar - P 1‖ ^ 2 / (η * (K : ℝ)) + 4 * η * L ^ 2 := by
      calc
        _ ≤ (‖PStar - P 1‖ ^ 2 / η + 4 * η * L ^ 2 * (K : ℝ)) /
            (K : ℝ) := hscaled
        _ = ‖PStar - P 1‖ ^ 2 / (η * (K : ℝ)) + 4 * η * L ^ 2 := by
          field_simp [ne_of_gt hηpos, ne_of_gt hKr]
    have herr := osgm_self_bounding_stepsize_error_bound
      L ‖PStar - P 1‖ η hK hL hDpos heta
    unfold ratio_average
    calc
      (∑ k ∈ Finset.Icc 1 K, ratio_surrogate f xStar (x k) (P k)) / (K : ℝ) =
          (∑ k ∈ Finset.Icc 1 K, ratio_surrogate f xStar (x k) PStar) / (K : ℝ) +
            ((∑ k ∈ Finset.Icc 1 K, ratio_surrogate f xStar (x k) (P k)) -
              (∑ k ∈ Finset.Icc 1 K, ratio_surrogate f xStar (x k) PStar)) /
                (K : ℝ) := by ring
      _ ≤ (∑ k ∈ Finset.Icc 1 K, ratio_surrogate f xStar (x k) PStar) / (K : ℝ) +
          max (4 * L * ‖PStar - P 1‖ / Real.sqrt (K : ℝ))
            (8 * L ^ 2 * ‖PStar - P 1‖ ^ 2 / (K : ℝ)) := by
        exact add_le_add (le_refl _) (hratio.trans herr)

@[blueprint "lem:refined-average-ratio-bound"
  (statement := /-- Let $n,K\in\mathbb N$ with $K\geq1$.  Let $f:\mathbb{R}^n\to\mathbb{R}$ be differentiable, suppose that $\nabla f$ is differentiable at every point, and let $L,\mu>0$.  Assume that $x^\star$ is a global minimizer of $f$ and that, for every $u,v\in\mathbb{R}^n$,
  \[
    \left|f(u)-f(v)-\langle\nabla f(v),u-v\rangle\right|
      \leq \frac L2\lVert u-v\rVert^2,
    \qquad
    \frac\mu2\lVert u-v\rVert^2
      \leq f(u)-f(v)-\langle\nabla f(v),u-v\rangle.
  \]
  Let $\mathcal P$ be a closed convex set of scaling matrices with metric projection $\Pi_{\mathcal P}$.  Suppose that $(x^k,P_k)$ is an OSGM--Rx run through iteration $K$ with stepsize $\eta$, that $P_1\in\mathcal P$, and that $f(x^k)>f(x^\star)$ for every $1\leq k\leq K$.  Assume that $(P_r^\star,\kappa^\star)$ is a universal optimal preconditioner and
  \[
    \eta=\min\left\{\frac1{4L^2},
      \frac{\lVert P_r^\star-P_1\rVert_F}{2L\sqrt K}\right\}.
  \]
  Then
  \[
    \overline r_K(P_k)\leq 1-\frac1{\kappa^\star}
      +\max\left\{\frac{4L\lVert P_r^\star-P_1\rVert_F}{\sqrt K},
      \frac{8L^2\lVert P_r^\star-P_1\rVert_F^2}{K}\right\}.
  \] -/)
  (proof := /-- For every \(1\leq k\leq K\), positivity of the active objective gap permits \cref{lem:universal-preconditioner-ratio-bound} to be applied at \(x^k\), and hence
  \[
    r_{x^k}(P_r^\star)\leq1-(\kappa^\star)^{-1}.
  \]
  The feasibility component of \cref{def:universal-optimal-preconditioner} and \cref{def:preconditioner-feasible} gives \(\kappa^\star>0\).  Thus \((\kappa^\star)^{-1}>0\), so the preceding bound also yields \(r_{x^k}(P_r^\star)\leq1\).  Use these latter inequalities as the comparator hypotheses in \cref{lem:osgm-rx-learnability}.  Finally, by \cref{def:ratio-average}, summing the sharper inequalities over \(1\leq k\leq K\) and dividing by \(K>0\) bounds the comparator average by \(1-(\kappa^\star)^{-1}\).  Substitution in the learnability estimate proves the displayed inequality. -/)
  (title := /-- Refined average ratio estimate -/)
  (latexEnv := "lemma")]
lemma refined_average_ratio_bound {n K : ℕ} (f : osgm_point n → ℝ)
    (xStar : osgm_point n) (x : ℕ → osgm_point n)
    (P : ℕ → osgm_matrix n) (Pset : Set (osgm_matrix n))
    (project : osgm_matrix n → osgm_matrix n) (PStar : osgm_matrix n)
    (L μ η κStar : ℝ) (hK : 0 < K)
    (hobjective : osgm_objective_assumptions f xStar L μ)
    (hclosed : IsClosed Pset) (hconvex : Convex ℝ Pset)
    (hprojection : metric_projection_map Pset project)
    (hPone : P 1 ∈ Pset)
    (hrun : osgm_rx_run f xStar x P project η K)
    (hpositive : positive_objective_gaps f xStar x K)
    (huniversal : universal_optimal_preconditioner f Pset κStar PStar)
    (heta : η = min (1 / (4 * L ^ 2))
      (‖PStar - P 1‖ / (2 * L * Real.sqrt (K : ℝ)))) :
    ratio_average f xStar x P K ≤
      1 - κStar⁻¹ +
        max (4 * L * ‖PStar - P 1‖ / Real.sqrt (K : ℝ))
          (8 * L ^ 2 * ‖PStar - P 1‖ ^ 2 / (K : ℝ)) := by
  have hPStar : PStar ∈ Pset := huniversal.1
  have hκ : 0 < κStar := huniversal.2.1.1
  have hpoint (k : ℕ) (hk1 : 1 ≤ k) (hkK : k ≤ K) :
      ratio_surrogate f xStar (x k) PStar ≤ 1 - κStar⁻¹ := by
    exact universal_preconditioner_ratio_bound f xStar L μ κStar Pset PStar
      hobjective huniversal (x k) (hpositive k hk1 hkK)
  have hcomparator (k : ℕ) (hk1 : 1 ≤ k) (hkK : k ≤ K) :
      ratio_surrogate f xStar (x k) PStar ≤ 1 := by
    have hinv : 0 < κStar⁻¹ := inv_pos.mpr hκ
    exact (hpoint k hk1 hkK).trans (by linarith)
  have hlearn := osgm_rx_learnability f xStar x P Pset project PStar L μ η hK
    hobjective hclosed hconvex hprojection hPone hPStar hrun hpositive hcomparator heta
  have hKr : (0 : ℝ) < (K : ℝ) := by
    exact_mod_cast hK
  have havg :
      ratio_average f xStar x (fun _ => PStar) K ≤ 1 - κStar⁻¹ := by
    change
      (∑ k ∈ Finset.Icc 1 K, ratio_surrogate f xStar (x k) PStar) / (K : ℝ) ≤
        1 - κStar⁻¹
    apply (div_le_iff₀ hKr).2
    calc
      (∑ k ∈ Finset.Icc 1 K, ratio_surrogate f xStar (x k) PStar) ≤
          ∑ k ∈ Finset.Icc 1 K, (1 - κStar⁻¹) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' := Finset.mem_Icc.mp hk
        exact hpoint k hk'.1 hk'.2
      _ = (K : ℝ) * (1 - κStar⁻¹) := by
        simp [Nat.card_Icc, hK]
        ring
      _ = (1 - κStar⁻¹) * (K : ℝ) := by ring
  exact hlearn.trans (add_le_add havg (le_refl _))

@[blueprint "thm:rx-globalconv"
  (statement := /-- Let \(K\geq1\).  Assume that \(f:\mathbb{R}^n\to\mathbb{R}\) is differentiable, that its gradient is differentiable at every point, that \(f\) is \(L\)-smooth and \(\mu\)-strongly convex for \(L,\mu>0\), and that \(x^\star\) is a global minimizer.  Let \(\mathcal P\) be a closed convex set of scaling matrices, let \(\Pi_{\mathcal P}\) be its metric projection, and let \((x^k,P_k)\) be the OSGM--Rx iterates with \(P_1\in\mathcal P\) and \(f(x^k)>f(x^\star)\) for every \(1\leq k\leq K\).  If \((P_r^\star,\kappa^\star)\) is a universal optimal preconditioner and
  \[
    \eta=\min\left\{\frac1{4L^2},
      \frac{\lVert P_r^\star-P_1\rVert_F}{2L\sqrt K}\right\},
  \]
  then
  \[
  f(x^{K+1})-f(x^\star)\leq
  \bigl(f(x^1)-f(x^\star)\bigr)
  \left(1-\frac1{\kappa^\star}
  +\max\left\{\frac{4L\lVert P_r^\star-P_1\rVert_F}{\sqrt K},
  \frac{8L^2\lVert P_r^\star-P_1\rVert_F^2}{K}\right\}\right)^K.
  \] -/)
  (proof := /-- Apply \cref{lem:refined-average-ratio-bound}; its self-bounding online analysis bounds the average ratio of the OSGM--Rx decisions by the parenthesized factor using only the objective and run assumptions.  The state recurrence in \cref{def:osgm-rx-run} supplies the scaled-gradient recurrence required by \cref{lem:ratio-online-to-convergence}, while the positivity hypothesis supplies its active-gap condition.  By \cref{def:osgm-objective-assumptions}, the point \(x^\star\) is a global minimizer, so \(f(x^{K+1})-f(x^\star)\geq0\); this is the terminal-gap condition of \cref{lem:ratio-online-to-convergence}.  Applying that lemma with the average-ratio bound gives the displayed \(K\)-step objective-gap estimate. -/)
  (title := /-- Refined global convergence of OSGM--Rx -/)
  (latexEnv := "theorem")]
theorem rx_globalconv {n K : ℕ} (f : osgm_point n → ℝ)
    (xStar : osgm_point n) (x : ℕ → osgm_point n)
    (P : ℕ → osgm_matrix n) (Pset : Set (osgm_matrix n))
    (project : osgm_matrix n → osgm_matrix n) (PStar : osgm_matrix n)
    (L μ η κStar : ℝ) (hK : 0 < K)
    (hobjective : osgm_objective_assumptions f xStar L μ)
    (hclosed : IsClosed Pset) (hconvex : Convex ℝ Pset)
    (hprojection : metric_projection_map Pset project)
    (hPone : P 1 ∈ Pset)
    (hrun : osgm_rx_run f xStar x P project η K)
    (hpositive : positive_objective_gaps f xStar x K)
    (huniversal : universal_optimal_preconditioner f Pset κStar PStar)
    (heta : η = min (1 / (4 * L ^ 2))
      (‖PStar - P 1‖ / (2 * L * Real.sqrt (K : ℝ)))) :
    f (x (K + 1)) - f xStar ≤
      (f (x 1) - f xStar) *
        (1 - κStar⁻¹ +
          max (4 * L * ‖PStar - P 1‖ / Real.sqrt (K : ℝ))
            (8 * L ^ 2 * ‖PStar - P 1‖ ^ 2 / (K : ℝ))) ^ K := by
  exact ratio_online_to_convergence f xStar x P _ hK hrun.1 hpositive
    (sub_nonneg.mpr (hobjective.2.2.2.2.1 _))
    (refined_average_ratio_bound f xStar x P Pset project PStar L μ η κStar hK
      hobjective hclosed hconvex hprojection hPone hrun hpositive huniversal heta)

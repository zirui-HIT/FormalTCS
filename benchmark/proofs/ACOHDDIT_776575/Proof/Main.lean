import Architect
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators

@[blueprint "def:hamiltonian-point"
  (statement := /-- For a natural number \(d\), the optimization space is the real Euclidean space
  \(\mathbb{R}^{d}\), represented as functions from \(\operatorname{Fin}(d)\) to \(\mathbb{R}\)
  with the standard Euclidean norm and inner product. -/)
  (title := /-- Euclidean optimization space -/)
  (latexEnv := "definition")]
abbrev hamiltonian_point (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

@[blueprint "def:hamiltonian-objective"
  (statement := /-- Let \(f:\mathbb{R}^{d}\to\mathbb{R}\), let
  \(g:\mathbb{R}^{d}\to\mathbb{R}^{d}\), let \(L>0\), and let
  \(x^\star\in\mathbb{R}^{d}\).  We say that these data form a Hamiltonian
  optimization objective if \(g(x)\) is the gradient of \(f\) at every \(x\),
  if
  \[
    f(x')\geq f(x)+\langle g(x),x'-x\rangle
  \]
  and
  \[
    f(x')\leq f(x)+\langle g(x),x'-x\rangle
      +\frac{L}{2}\lVert x'-x\rVert^{2}
  \]
  for all \(x,x'\), and if \(x^\star\) is the unique global minimizer of
  \(f\). -/)
  (title := /-- Smooth convex optimization data -/)
  (latexEnv := "definition")]
def hamiltonian_objective {d : ℕ}
    (f : hamiltonian_point d → ℝ)
    (g : hamiltonian_point d → hamiltonian_point d)
    (L : ℝ) (xStar : hamiltonian_point d) : Prop :=
  0 < L ∧
    (∀ x, HasGradientAt f (g x) x) ∧
    (∀ x x', f x + inner ℝ (g x) (x' - x) ≤ f x') ∧
    (∀ x x',
      f x' ≤ f x + inner ℝ (g x) (x' - x) + (L / 2) * ‖x' - x‖ ^ 2) ∧
    (∀ x, f xStar ≤ f x) ∧
    (∀ x, f x = f xStar → x = xStar)

@[blueprint "def:extragradient-trajectory"
  (statement := /-- Given a gradient oracle \(g\), a step size \(\eta\), and initial data
  \((x_{0},y_{0})\), define the extragradient trajectory recursively.  If
  \((x_n,y_n)\) is the current state, put
  \[
    x_{n+\frac12}=x_n+\eta y_n,\qquad
    x_{n+1}=x_{n+\frac12}-\eta^2g(x_{n+\frac12}),\qquad
    y_{n+1}=y_n-\eta g(x_{n+1}).
  \] -/)
  (title := /-- Extragradient integrator -/)
  (latexEnv := "definition")]
def extragradient_trajectory {d : ℕ}
    (g : hamiltonian_point d → hamiltonian_point d) (η : ℝ)
    (x₀ y₀ : hamiltonian_point d) : ℕ → hamiltonian_point d × hamiltonian_point d
  | 0 => (x₀, y₀)
  | n + 1 =>
      let previous := extragradient_trajectory g η x₀ y₀ n
      let xHalf := previous.1 + η • previous.2
      let xNext := xHalf - (η ^ 2) • g xHalf
      let yNext := previous.2 - η • g xNext
      (xNext, yNext)

@[blueprint "def:weighted-extragradient-average"
  (statement := /-- For \(N\in\mathbb{N}\), define the triangularly weighted average of the
  first \(N\) positions of the extragradient trajectory started from
  \((x,0)\) by
  \[
    x^{\mathrm{avg}}(x;N)=
    \frac{2}{N(N+1)}\sum_{n=1}^{N}(N-n+1)x_n.
  \]
  The displayed formula is interpreted by the total operations of
  \(\mathbb{R}\) when \(N=0\). -/)
  (title := /-- Triangularly weighted extragradient average -/)
  (latexEnv := "definition")]
noncomputable def weighted_extragradient_average {d : ℕ}
    (g : hamiltonian_point d → hamiltonian_point d) (η : ℝ)
    (x : hamiltonian_point d) (N : ℕ) : hamiltonian_point d :=
  (2 / ((N : ℝ) * ((N + 1 : ℕ) : ℝ))) •
    ∑ i ∈ Finset.range N,
      (((N - i : ℕ) : ℝ) • (extragradient_trajectory g η x 0 (i + 1)).1)

@[blueprint "def:mixed-extragradient-point"
  (statement := /-- For a mixing parameter \(\lambda\), define
  \[
    x^{\mathrm{mix}}(x;N)=
    \frac{\lambda}{\lambda+1}x_N+
    \frac{1}{\lambda+1}x^{\mathrm{avg}}(x;N),
  \]
  where the extragradient trajectory is restarted from \((x,0)\). -/)
  (title := /-- Mixed extragradient output -/)
  (latexEnv := "definition")]
noncomputable def mixed_extragradient_point {d : ℕ}
    (g : hamiltonian_point d → hamiltonian_point d) (η lam : ℝ)
    (x : hamiltonian_point d) (N : ℕ) : hamiltonian_point d :=
  (lam / (lam + 1)) • (extragradient_trajectory g η x 0 N).1 +
    (1 / (lam + 1)) • weighted_extragradient_average g η x N

@[blueprint "def:accelerated-outer-iterate"
  (statement := /-- Let \(N:\mathbb{N}\to\mathbb{N}\) be a sequence of inner step counts.
  Starting from \(x_0\), recursively define
  \[
    x_{k+1}=x^{\mathrm{mix}}(x_k;N_{k+1}).
  \]
  At every outer iteration, the inner velocity is reset to zero. -/)
  (title := /-- Discretized Hamiltonian flow with averaging -/)
  (latexEnv := "definition")]
noncomputable def accelerated_outer_iterate {d : ℕ}
    (g : hamiltonian_point d → hamiltonian_point d) (η lam : ℝ)
    (N : ℕ → ℕ) (x₀ : hamiltonian_point d) : ℕ → hamiltonian_point d
  | 0 => x₀
  | k + 1 =>
      mixed_extragradient_point g η lam
        (accelerated_outer_iterate g η lam N x₀ k) (N (k + 1))

@[blueprint "def:inner-step-mass"
  (statement := /-- For \(N\in\mathbb{N}\), set \(Q(N)=N(N+1)\), regarded as a real
  number. -/)
  (title := /-- Quadratic inner-step mass -/)
  (latexEnv := "definition")]
def inner_step_mass (N : ℕ) : ℝ := (N : ℝ) * ((N + 1 : ℕ) : ℝ)

@[blueprint "def:mixing-parameter"
  (statement := /-- Fix the mixing parameter
  \(\lambda_\star=(\sqrt{3}+1)/2\). -/)
  (title := /-- Accelerating mixing parameter -/)
  (latexEnv := "definition")]
noncomputable def mixing_parameter : ℝ := (Real.sqrt 3 + 1) / 2

@[blueprint "def:convergence-rate"
  (statement := /-- Set
  \(\rho=(\sqrt{3}+1)/3\), the asserted contraction factor. -/)
  (title := /-- Geometric convergence factor -/)
  (latexEnv := "definition")]
noncomputable def convergence_rate : ℝ := (Real.sqrt 3 + 1) / 3

@[blueprint "def:mixed-contraction-coefficient"
  (statement := /-- For \(\lambda\neq0,-1\), define
  \[
    c_\lambda=\frac{6\lambda^2+4\lambda+1}{6\lambda(\lambda+1)}.
  \]
  This is the coefficient produced by the weighted-sum argument for one
  mixed extragradient run. -/)
  (title := /-- One-run contraction coefficient -/)
  (latexEnv := "definition")]
noncomputable def mixed_contraction_coefficient (lam : ℝ) : ℝ :=
  (6 * lam ^ 2 + 4 * lam + 1) / (6 * lam * (lam + 1))

@[blueprint "def:admissible-inner-schedule"
  (statement := /-- For \(K\in\mathbb{N}\), an inner-step sequence \(N\) is admissible if
  \(N_0=4\) and, for every \(k<K\),
  \[
    Q(N_{k+1})\geq
    \frac{3}{\sqrt{3}+1}Q(N_k).
  \] -/)
  (title := /-- Admissible discretization schedule -/)
  (latexEnv := "definition")]
def admissible_inner_schedule (N : ℕ → ℕ) (K : ℕ) : Prop :=
  N 0 = 4 ∧
    ∀ k, k < K →
      (3 / (Real.sqrt 3 + 1)) * inner_step_mass (N k) ≤
        inner_step_mass (N (k + 1))

@[blueprint "def:discrete-potential"
  (statement := /-- For a point \(x\), an inner-step count \(N\), and a step size \(\eta\),
  define
  \[
    \Phi_{\eta,N}(x)=f(x)-f(x^\star)+
      \frac{\lVert x-x^\star\rVert^2}
      {3\lambda_\star\eta^2Q(N)}.
  \] -/)
  (title := /-- Discrete Lyapunov potential -/)
  (latexEnv := "definition")]
noncomputable def discrete_potential {d : ℕ}
    (f : hamiltonian_point d → ℝ) (xStar : hamiltonian_point d)
    (η : ℝ) (N : ℕ) (x : hamiltonian_point d) : ℝ :=
  f x - f xStar +
    ‖x - xStar‖ ^ 2 /
      (3 * mixing_parameter * η ^ 2 * inner_step_mass N)

@[blueprint "lem:hamiltonian-gradient-lipschitz"
  (statement := /-- Assume \(\cref{def:hamiltonian-objective}\).  Then for all
  \(x,y\in\mathbb{R}^{d}\),
  \[
    \lVert g(x)-g(y)\rVert\leq L\lVert x-y\rVert.
  \] -/)
  (proof := /-- Unpack \(\cref{def:hamiltonian-objective}\).  Fix \(x,y\),
  set \(v=g(x)-g(y)\), and apply the smoothness inequality at \(x\) to
  \(x-L^{-1}v\).  Combining it with the convex supporting inequality at
  \(y\) gives
  \[
    \frac{\lVert v\rVert^2}{2L}
      \leq f(x)-f(y)-\langle g(y),x-y\rangle.
  \]
  Interchanging \(x\) and \(y\), adding the two estimates, and using the
  Cauchy--Schwarz inequality yields
  \(\lVert v\rVert^2\leq L\lVert v\rVert\lVert x-y\rVert\).
  Since \(L>0\), cancellation (with the zero-norm case separated) proves
  the claim. -/)
  (title := /-- Lipschitz continuity of the Hamiltonian gradient -/)
  (latexEnv := "lemma")]
lemma hamiltonian_gradient_lipschitz {d : ℕ}
    (f : hamiltonian_point d → ℝ)
    (g : hamiltonian_point d → hamiltonian_point d)
    (L : ℝ) (xStar : hamiltonian_point d)
    (hObjective : hamiltonian_objective f g L xStar) :
    ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖ := by
  intro x y
  rcases hObjective with ⟨hL, _, hConvex, hSmooth, _, _⟩
  have hLne : L ≠ 0 := ne_of_gt hL
  have hBregman (a b : hamiltonian_point d) :
      ‖g a - g b‖ ^ 2 ≤
        2 * L * (f a - f b - inner ℝ (g b) (a - b)) := by
    let v := g a - g b
    let z := a - (1 / L) • v
    have hraw := le_trans (hConvex b z) (hSmooth a z)
    have hzb : z - b = (a - b) - (1 / L) • v := by
      dsimp [z]
      abel
    have hza : z - a = -((1 / L) • v) := by
      dsimp [z]
      abel
    rw [hzb, hza, inner_sub_right, real_inner_smul_right, inner_neg_right,
      real_inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr hL)] at hraw
    have hvinner :
        inner ℝ (g a) v - inner ℝ (g b) v = ‖v‖ ^ 2 := by
      rw [← inner_sub_left]
      exact real_inner_self_eq_norm_sq v
    field_simp [hLne] at hraw
    dsimp [v] at hraw hvinner ⊢
    nlinarith
  let v := g x - g y
  have hxy := hBregman x y
  have hyx := hBregman y x
  have hnormswap : ‖g y - g x‖ ^ 2 = ‖v‖ ^ 2 := by
    have : g y - g x = -v := by
      dsimp [v]
      abel
    rw [this, norm_neg]
  have hdiv :
      (f x - f y - inner ℝ (g y) (x - y)) +
          (f y - f x - inner ℝ (g x) (y - x)) =
        inner ℝ v (x - y) := by
    have hyx' : y - x = -(x - y) := by abel
    rw [hyx', inner_neg_right]
    dsimp [v]
    rw [inner_sub_left]
    ring
  have hco : ‖v‖ ^ 2 ≤ L * inner ℝ v (x - y) := by
    rw [hnormswap] at hyx
    nlinarith
  have hcs := real_inner_le_norm v (x - y)
  have hcsL :
      L * inner ℝ v (x - y) ≤ L * (‖v‖ * ‖x - y‖) :=
    mul_le_mul_of_nonneg_left hcs (le_of_lt hL)
  have hprod : ‖v‖ ^ 2 ≤ L * (‖v‖ * ‖x - y‖) :=
    le_trans hco hcsL
  by_cases hv0 : ‖v‖ = 0
  · simpa [v, hv0] using mul_nonneg (le_of_lt hL) (norm_nonneg (x - y))
  · have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv0)
    have hcanc : ‖v‖ * ‖v‖ ≤ ‖v‖ * (L * ‖x - y‖) := by
      nlinarith [hprod]
    have := le_of_mul_le_mul_left hcanc hvpos
    simpa [v] using this

@[blueprint "lem:extragradient-hamiltonian-nonincrease"
  (statement := /-- Assume \(\cref{def:hamiltonian-objective}\), let
  \(0<\eta\leq L^{-1/2}\), and let \((x_n,y_n)\) be the trajectory of
  \(\cref{def:extragradient-trajectory}\).  Then for every \(n\),
  \[
    f(x_{n+1})+\frac12\lVert y_{n+1}\rVert^2
    \leq f(x_n)+\frac12\lVert y_n\rVert^2.
  \] -/)
  (proof := /-- Apply the convex supporting inequality at \(x_{n+1}\) to bound
  \(f(x_{n+1})-f(x_n)\), substitute all three recurrences from
  \cref{def:extragradient-trajectory}, and expand the difference of the
  kinetic energies.  The terms containing \(y_n\) cancel, leaving
  \[
    \frac{\eta^2}{2}\left(
      \lVert g(x_{n+1})-g(x_{n+1/2})\rVert^2
      -\lVert g(x_{n+1/2})\rVert^2\right).
  \]
  By \cref{lem:hamiltonian-gradient-lipschitz}, the first squared norm is at
  most
  \(L^2\eta^4\lVert g(x_{n+1/2})\rVert^2\).  Since
  \(\eta\leq L^{-1/2}\), the resulting coefficient
  \(\eta^2(L^2\eta^4-1)/2\) is nonpositive, proving the claim. -/)
  (title := /-- Hamiltonian dissipation of one extragradient step -/)
  (latexEnv := "lemma")]
lemma extragradient_hamiltonian_nonincrease {d : ℕ}
    (f : hamiltonian_point d → ℝ)
    (g : hamiltonian_point d → hamiltonian_point d)
    (L η : ℝ) (xStar x₀ y₀ : hamiltonian_point d) (n : ℕ)
    (hObjective : hamiltonian_objective f g L xStar)
    (hηpos : 0 < η) (hηmax : η ≤ 1 / Real.sqrt L) :
    f (extragradient_trajectory g η x₀ y₀ (n + 1)).1 +
        (1 / 2 : ℝ) * ‖(extragradient_trajectory g η x₀ y₀ (n + 1)).2‖ ^ 2
      ≤
    f (extragradient_trajectory g η x₀ y₀ n).1 +
        (1 / 2 : ℝ) * ‖(extragradient_trajectory g η x₀ y₀ n).2‖ ^ 2 := by
  let previous := extragradient_trajectory g η x₀ y₀ n
  let xHalf := previous.1 + η • previous.2
  let xNext := xHalf - (η ^ 2) • g xHalf
  have htraj :
      extragradient_trajectory g η x₀ y₀ (n + 1) =
        (xNext, previous.2 - η • g xNext) := by
    simp [extragradient_trajectory, previous, xHalf, xNext]
  rw [htraj]
  change
    f xNext + (1 / 2 : ℝ) * ‖previous.2 - η • g xNext‖ ^ 2 ≤
      f previous.1 + (1 / 2 : ℝ) * ‖previous.2‖ ^ 2
  have hLip :=
    hamiltonian_gradient_lipschitz f g L xStar hObjective xNext xHalf
  rcases hObjective with ⟨hL, _, hConvex, _, _, _⟩
  have hsqrt : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hsqrt_sq : (Real.sqrt L) ^ 2 = L :=
    Real.sq_sqrt (le_of_lt hL)
  have hηsqrt : η * Real.sqrt L ≤ 1 := by
    have hmul :=
      mul_le_mul_of_nonneg_right hηmax (le_of_lt hsqrt)
    field_simp [ne_of_gt hsqrt] at hmul
    exact hmul
  have hLη : L * η ^ 2 ≤ 1 := by
    have hηsqrt_nonneg :
        0 ≤ η * Real.sqrt L :=
      mul_nonneg (le_of_lt hηpos) (le_of_lt hsqrt)
    nlinarith [sq_nonneg (η * Real.sqrt L)]
  have hxstep : xNext - xHalf = -((η ^ 2) • g xHalf) := by
    dsimp [xNext]
    abel
  rw [hxstep, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg η)] at hLip
  have hdiff :
      ‖g xNext - g xHalf‖ ≤ ‖g xHalf‖ := by
    refine le_trans hLip ?_
    have hnorm : 0 ≤ ‖g xHalf‖ := norm_nonneg _
    nlinarith
  have hdiffsq :
      ‖g xNext - g xHalf‖ ^ 2 ≤ ‖g xHalf‖ ^ 2 := by
    have hnonneg :
        0 ≤ ‖g xHalf‖ + ‖g xNext - g xHalf‖ :=
      add_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith [mul_nonneg (sub_nonneg.mpr hdiff) hnonneg]
  have hfun := hConvex xNext previous.1
  have hxmove :
      xNext - previous.1 =
        η • previous.2 - (η ^ 2) • g xHalf := by
    dsimp [xNext, xHalf]
    abel
  have hxneg :
      previous.1 - xNext = -(xNext - previous.1) := by
    abel
  rw [hxneg, inner_neg_right] at hfun
  have hfun' :
      f xNext - f previous.1 ≤
        η * inner ℝ (g xNext) previous.2 -
          η ^ 2 * inner ℝ (g xNext) (g xHalf) := by
    have hfunRaw := hfun
    rw [hxmove, inner_sub_right, real_inner_smul_right,
      real_inner_smul_right] at hfunRaw
    linarith
  have hkin := norm_sub_sq_real previous.2 (η • g xNext)
  rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos hηpos] at hkin
  have hgraddiff := norm_sub_sq_real (g xNext) (g xHalf)
  have hinnercomm :
      inner ℝ previous.2 (g xNext) =
        inner ℝ (g xNext) previous.2 :=
    (real_inner_comm previous.2 (g xNext)).symm
  rw [hinnercomm] at hkin
  nlinarith [sq_nonneg η]

@[blueprint "lem:extragradient-gradient-step-estimates"
  (statement := /-- Let \(f,g,L,x^\star\) satisfy
  \(\cref{def:hamiltonian-objective}\), let \(\eta>0\) satisfy
  \(L\eta^2\leq1\), and put
  \(z=p+\eta v\) and \(q=z-\eta^2g(z)\).  Then
  \[
    f(q)\leq f(z)
  \]
  and
  \[
    \lVert q-x^\star\rVert^2
      \leq \lVert z-x^\star\rVert^2
        -2\eta^2\bigl(f(q)-f(x^\star)\bigr).
  \] -/)
  (proof := /-- Apply the smoothness clause of
  \(\cref{def:hamiltonian-objective}\) to the gradient step from \(z\) to
  \(q\).  Since \(L\eta^2\leq1\), it decreases the objective by at least
  \(\eta^2\lVert g(z)\rVert^2/2\).  The convex supporting inequality at
  \(z\), applied to \(x^\star\), bounds
  \(f(z)-f(x^\star)\) by
  \(\langle g(z),z-x^\star\rangle\).  Expanding the squared distance after
  the gradient step and combining these two estimates gives the second
  inequality. -/)
  (title := /-- Descent and distance estimates for the position substep -/)
  (latexEnv := "lemma")]
lemma extragradient_gradient_step_estimates {d : ℕ}
    (f : hamiltonian_point d → ℝ)
    (g : hamiltonian_point d → hamiltonian_point d)
    (L η : ℝ) (xStar p v z q : hamiltonian_point d)
    (hObjective : hamiltonian_objective f g L xStar)
    (hηpos : 0 < η) (hηL : L * η ^ 2 ≤ 1)
    (hz : z = p + η • v) (hq : q = z - (η ^ 2) • g z) :
    f q ≤ f z ∧
      ‖q - xStar‖ ^ 2 ≤
        ‖z - xStar‖ ^ 2 - 2 * η ^ 2 * (f q - f xStar) := by
  subst z
  subst q
  rcases hObjective with ⟨hL, hgrad, hconvex, hsmooth, hmin, hunique⟩
  have hs := hsmooth (p + η • v) ((p + η • v) - (η ^ 2) • g (p + η • v))
  have hc := hconvex (p + η • v) xStar
  have hηnonneg : 0 ≤ η := le_of_lt hηpos
  have hηsq : 0 ≤ η ^ 2 := sq_nonneg η
  have hcoef : 0 ≤ 1 - L * η ^ 2 / 2 := by nlinarith
  have hinner :
      inner ℝ (g (p + η • v))
          (((p + η • v) - (η ^ 2) • g (p + η • v)) - (p + η • v)) =
        -(η ^ 2) * ‖g (p + η • v)‖ ^ 2 := by
    simp only [sub_sub_cancel_left, inner_neg_right, inner_smul_right,
      real_inner_self_eq_norm_sq, RCLike.star_def, conj_trivial]
    ring
  have hnorm :
      ‖((p + η • v) - (η ^ 2) • g (p + η • v)) - (p + η • v)‖ ^ 2 =
        η ^ 4 * ‖g (p + η • v)‖ ^ 2 := by
    simp [norm_smul, abs_of_nonneg hηsq]
    ring
  rw [hinner, hnorm] at hs
  have hdescent :
      f ((p + η • v) - (η ^ 2) • g (p + η • v)) ≤
        f (p + η • v) -
          (η ^ 2 / 2) * ‖g (p + η • v)‖ ^ 2 := by
    nlinarith [mul_nonneg hcoef (mul_nonneg hηsq (sq_nonneg ‖g (p + η • v)‖))]
  constructor
  · nlinarith [mul_nonneg hηsq (sq_nonneg ‖g (p + η • v)‖)]
  · have hdist :
        ‖((p + η • v) - (η ^ 2) • g (p + η • v)) - xStar‖ ^ 2 =
          ‖(p + η • v) - xStar‖ ^ 2 -
            2 * η ^ 2 *
              inner ℝ (g (p + η • v)) ((p + η • v) - xStar) +
            η ^ 4 * ‖g (p + η • v)‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
        ← real_inner_self_eq_norm_sq]
      simp only [sub_eq_add_neg, inner_add_left, inner_add_right,
        inner_smul_left, inner_smul_right, real_inner_comm,
        RCLike.star_def, conj_trivial, neg_smul, inner_neg_left,
        inner_neg_right]
      ring
    have hc' :
        f (p + η • v) - f xStar ≤
          inner ℝ (g (p + η • v)) ((p + η • v) - xStar) := by
      have hneg :
          xStar - (p + η • v) = -((p + η • v) - xStar) := by abel
      rw [hneg, inner_neg_right] at hc
      linarith
    rw [hdist]
    nlinarith [mul_nonneg hηsq (sub_nonneg.mpr hc'),
      mul_nonneg hηsq (sq_nonneg ‖g (p + η • v)‖)]

@[blueprint "lem:extragradient-virial-step"
  (statement := /-- Under \(\cref{def:hamiltonian-objective}\), suppose that
  \(z=p+\eta v\), \(q=z-\eta^2g(z)\), and
  \(r=v-\eta g(q)\), where \(L\eta^2\leq1\).  Then the discrete virial
  quantity
  \[
    M(p,v)=\langle p-x^\star,v\rangle
      +\eta\bigl(f(p)-f(x^\star)\bigr)
  \]
  satisfies
  \[
    M(q,r)-M(p,v)
      \leq\eta\left(\lVert v\rVert^2-
        \bigl(f(q)-f(x^\star)\bigr)\right).
  \] -/)
  (proof := /-- By
  \(\cref{lem:extragradient-gradient-step-estimates}\), \(f(q)\leq f(z)\).
  The supporting inequality at \(z\), evaluated at \(p\), gives
  \(f(z)-f(p)\leq\eta\langle g(z),v\rangle\), while the supporting
  inequality at \(q\), evaluated at \(x^\star\), gives
  \(f(q)-f(x^\star)\leq\langle g(q),q-x^\star\rangle\).
  Substitute the three update formulas into the difference of the two
  virial quantities.  The two displayed inequalities and \(f(q)\leq f(z)\)
  yield the claimed bound. -/)
  (title := /-- One-step discrete virial inequality -/)
  (latexEnv := "lemma")]
lemma extragradient_virial_step {d : ℕ}
    (f : hamiltonian_point d → ℝ)
    (g : hamiltonian_point d → hamiltonian_point d)
    (L η : ℝ) (xStar p v z q r : hamiltonian_point d)
    (hObjective : hamiltonian_objective f g L xStar)
    (hηpos : 0 < η) (hηL : L * η ^ 2 ≤ 1)
    (hz : z = p + η • v) (hq : q = z - (η ^ 2) • g z)
    (hr : r = v - η • g q) :
    inner ℝ (q - xStar) r + η * (f q - f xStar) -
        (inner ℝ (p - xStar) v + η * (f p - f xStar))
      ≤ η * (‖v‖ ^ 2 - (f q - f xStar)) := by
  subst z
  have hdescent :=
    (extragradient_gradient_step_estimates f g L η xStar p v
      (p + η • v) q hObjective hηpos hηL rfl hq).1
  have ha := hObjective.2.2.1 (p + η • v) p
  have hb := hObjective.2.2.1 q xStar
  have ha' :
      f (p + η • v) - f p ≤ η * inner ℝ (g (p + η • v)) v := by
    have hpz : p - (p + η • v) = -(η • v) := by module
    rw [hpz, inner_neg_right, inner_smul_right] at ha
    linarith
  have hb' : f q - f xStar ≤ inner ℝ (g q) (q - xStar) := by
    have hxq : xStar - q = -(q - xStar) := by module
    rw [hxq, inner_neg_right] at hb
    linarith
  have hexpand :
      inner ℝ (q - xStar) r + η * (f q - f xStar) -
          (inner ℝ (p - xStar) v + η * (f p - f xStar)) =
        η * ‖v‖ ^ 2 - η ^ 2 * inner ℝ (g (p + η • v)) v -
          η * inner ℝ (g q) (q - xStar) +
          η * ((f q - f xStar) - (f p - f xStar)) := by
    rw [hr, hq, ← real_inner_self_eq_norm_sq]
    simp only [sub_eq_add_neg, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, inner_neg_left, inner_neg_right,
      RCLike.star_def, conj_trivial, real_inner_comm]
    ring
  rw [hexpand]
  nlinarith

@[blueprint "lem:extragradient-distance-step"
  (statement := /-- Under the hypotheses and notation of
  \(\cref{lem:extragradient-gradient-step-estimates}\), the position
  substep satisfies
  \[
    \lVert q-x^\star\rVert^2-\lVert p-x^\star\rVert^2
      \leq 2\eta\langle p-x^\star,v\rangle+\eta^2\lVert v\rVert^2
        -2\eta^2\bigl(f(q)-f(x^\star)\bigr).
  \] -/)
  (proof := /-- Apply the squared-distance estimate from
  \(\cref{lem:extragradient-gradient-step-estimates}\), and expand
  \(\lVert z-x^\star\rVert^2\) using \(z=p+\eta v\). -/)
  (title := /-- One-step squared-distance inequality -/)
  (latexEnv := "lemma")]
lemma extragradient_distance_step {d : ℕ}
    (f : hamiltonian_point d → ℝ)
    (g : hamiltonian_point d → hamiltonian_point d)
    (L η : ℝ) (xStar p v z q : hamiltonian_point d)
    (hObjective : hamiltonian_objective f g L xStar)
    (hηpos : 0 < η) (hηL : L * η ^ 2 ≤ 1)
    (hz : z = p + η • v) (hq : q = z - (η ^ 2) • g z) :
    ‖q - xStar‖ ^ 2 - ‖p - xStar‖ ^ 2 ≤
      2 * η * inner ℝ (p - xStar) v + η ^ 2 * ‖v‖ ^ 2 -
        2 * η ^ 2 * (f q - f xStar) := by
  have hd :=
    (extragradient_gradient_step_estimates f g L η xStar p v z q
      hObjective hηpos hηL hz hq).2
  have hexpand :
      ‖z - xStar‖ ^ 2 =
        ‖p - xStar‖ ^ 2 + 2 * η * inner ℝ (p - xStar) v +
          η ^ 2 * ‖v‖ ^ 2 := by
    rw [hz, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq]
    simp only [sub_eq_add_neg, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, RCLike.star_def, conj_trivial,
      real_inner_comm]
    ring
  rw [hexpand] at hd
  linarith

@[blueprint "lem:extragradient-virial-accumulation"
  (statement := /-- Under \(\cref{def:hamiltonian-objective}\), let
  \(0<\eta\leq L^{-1/2}\), and let \((x_n,y_n)\) be the extragradient
  trajectory from \((x,0)\).  Writing
  \(G_n=f(x_n)-f(x^\star)\) and
  \(M_n=\langle x_n-x^\star,y_n\rangle+\eta G_n\), one has
  \[
    M_n\leq\eta\left((2n+1)G_0
      -2\sum_{i=0}^{n-1}G_i-\sum_{i=1}^{n}G_i\right).
  \] -/)
  (proof := /-- Iterate \(\cref{lem:extragradient-virial-step}\).  At each
  index, \(\cref{lem:extragradient-hamiltonian-nonincrease}\) gives
  \(\lVert y_i\rVert^2\leq2(G_0-G_i)\).  Substitution in the virial
  recurrence and summation gives the displayed formula. -/)
  (title := /-- Accumulated discrete virial bound -/)
  (latexEnv := "lemma")]
lemma extragradient_virial_accumulation {d : ℕ}
    (f : hamiltonian_point d → ℝ)
    (g : hamiltonian_point d → hamiltonian_point d)
    (L η : ℝ) (xStar x : hamiltonian_point d) (n : ℕ)
    (hObjective : hamiltonian_objective f g L xStar)
    (hηpos : 0 < η) (hηmax : η ≤ 1 / Real.sqrt L)
    (hηL : L * η ^ 2 ≤ 1) :
    let X := extragradient_trajectory g η x 0
    inner ℝ (X n).1 (X n).2 - inner ℝ xStar (X n).2 +
          η * (f (X n).1 - f xStar)
      ≤
    η * (((2 * n + 1 : ℕ) : ℝ) * (f x - f xStar) -
      2 * ∑ i ∈ Finset.range n, (f (X i).1 - f xStar) -
      ∑ i ∈ Finset.range n, (f (X (i + 1)).1 - f xStar)) := by
  let X := extragradient_trajectory g η x 0
  have henergy : ∀ k : ℕ,
      f (X k).1 + (1 / 2 : ℝ) * ‖(X k).2‖ ^ 2 ≤ f x := by
    intro k
    induction k with
    | zero => simp [X, extragradient_trajectory]
    | succ k ih =>
        exact le_trans
          (extragradient_hamiltonian_nonincrease f g L η xStar x 0 k
            hObjective hηpos hηmax) ih
  have hvirial : ∀ k : ℕ,
      (inner ℝ ((X (k + 1)).1 - xStar) (X (k + 1)).2 +
          η * (f (X (k + 1)).1 - f xStar)) -
        (inner ℝ ((X k).1 - xStar) (X k).2 +
          η * (f (X k).1 - f xStar))
        ≤ η * (‖(X k).2‖ ^ 2 -
          (f (X (k + 1)).1 - f xStar)) := by
    intro k
    apply extragradient_virial_step f g L η xStar
      (X k).1 (X k).2
      ((X k).1 + η • (X k).2) (X (k + 1)).1 (X (k + 1)).2
      hObjective hηpos hηL
    · rfl
    · simp [X, extragradient_trajectory]
    · simp [X, extragradient_trajectory]
  induction n with
  | zero =>
      simp [X, extragradient_trajectory]
  | succ n ih =>
      have hv := hvirial n
      have he := henergy n
      have hV :
          ‖(X n).2‖ ^ 2 ≤
            2 * ((f x - f xStar) - (f (X n).1 - f xStar)) := by
        linarith
      have hVη := mul_le_mul_of_nonneg_left hV (le_of_lt hηpos)
      dsimp [X] at hv hVη
      simp only [Finset.sum_range_succ] at ih ⊢
      simp_rw [inner_sub_left] at hv
      norm_num [Nat.cast_add, Nat.cast_mul] at ih ⊢
      ring_nf at ih hv hVη ⊢
      nlinarith

@[blueprint "lem:extragradient-weighted-trajectory-sum"
  (statement := /-- Under \(\cref{def:hamiltonian-objective}\), let
  \(0<\eta\leq L^{-1/2}\), and restart the extragradient trajectory
  \((x_n,y_n)\) from \((x,0)\).  For every \(N\),
  \[
    6\eta^2\sum_{n=1}^{N}(N-n+1)
      \bigl(f(x_n)-f(x^\star)\bigr)+\lVert x_N-x^\star\rVert^2
    \leq
    2\eta^2N(N+1)\bigl(f(x)-f(x^\star)\bigr)
      +\lVert x-x^\star\rVert^2.
  \] -/)
  (proof := /-- Induct on \(N\).  The induction step uses
  \(\cref{lem:extragradient-distance-step}\) for the distance increment and
  \(\cref{lem:extragradient-virial-accumulation}\) for its cross term.
  Hamiltonian dissipation from
  \(\cref{lem:extragradient-hamiltonian-nonincrease}\) bounds the remaining
  kinetic energy, while minimality of \(x^\star\) bounds every objective gap
  between zero and the initial gap.  The identity obtained by increasing
  \(N\) adds the unweighted prefix of gaps to the triangularly weighted
  sum, and the resulting coefficients cancel exactly. -/)
  (title := /-- Triangularly weighted trajectory estimate -/)
  (latexEnv := "lemma")]
lemma extragradient_weighted_trajectory_sum {d : ℕ}
    (f : hamiltonian_point d → ℝ)
    (g : hamiltonian_point d → hamiltonian_point d)
    (L η : ℝ) (xStar x : hamiltonian_point d) (N : ℕ)
    (hObjective : hamiltonian_objective f g L xStar)
    (hηpos : 0 < η) (hηmax : η ≤ 1 / Real.sqrt L)
    (hηL : L * η ^ 2 ≤ 1) :
    6 * η ^ 2 *
          ∑ i ∈ Finset.range N,
            ((N - i : ℕ) : ℝ) *
              (f (extragradient_trajectory g η x 0 (i + 1)).1 - f xStar) +
        ‖(extragradient_trajectory g η x 0 N).1 - xStar‖ ^ 2
      ≤
    2 * η ^ 2 * inner_step_mass N * (f x - f xStar) +
      ‖x - xStar‖ ^ 2 := by
  let X := extragradient_trajectory g η x 0
  let G : ℕ → ℝ := fun k => f (X k).1 - f xStar
  have henergy : ∀ k : ℕ,
      f (X k).1 + (1 / 2 : ℝ) * ‖(X k).2‖ ^ 2 ≤ f x := by
    intro k
    induction k with
    | zero => simp [X, extragradient_trajectory]
    | succ k ih =>
        exact le_trans
          (extragradient_hamiltonian_nonincrease f g L η xStar x 0 k
            hObjective hηpos hηmax) ih
  have hsum : ∀ n : ℕ,
      (∑ i ∈ Finset.range n, G i) + G n =
        G 0 + ∑ i ∈ Finset.range n, G (i + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        simp only [Finset.sum_range_succ]
        linarith
  have hweighted : ∀ n : ℕ,
      (∑ i ∈ Finset.range (n + 1), (((n + 1 - i : ℕ) : ℝ) * G (i + 1))) =
        (∑ i ∈ Finset.range n, (((n - i : ℕ) : ℝ) * G (i + 1))) +
          ∑ i ∈ Finset.range (n + 1), G (i + 1) := by
    intro n
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hparts :
        (∑ i ∈ Finset.range n, (((n + 1 - i : ℕ) : ℝ) * G (i + 1))) =
          (∑ i ∈ Finset.range n, (((n - i : ℕ) : ℝ) * G (i + 1))) +
            ∑ i ∈ Finset.range n, G (i + 1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < n := Finset.mem_range.mp hi
      have hn : n + 1 - i = (n - i) + 1 := by omega
      rw [hn, Nat.cast_add, Nat.cast_one]
      ring
    rw [hparts]
    have hlast : n + 1 - n = 1 := by omega
    simp [hlast]
    ring
  induction N with
  | zero =>
      simp [X, G, extragradient_trajectory, inner_step_mass]
  | succ n ih =>
      have ha :=
        extragradient_virial_accumulation f g L η xStar x n
          hObjective hηpos hηmax hηL
      have hd :=
        extragradient_distance_step f g L η xStar
          (X n).1 (X n).2 ((X n).1 + η • (X n).2)
          (X (n + 1)).1 hObjective hηpos hηL rfl
          (by simp [X, extragradient_trajectory])
      have he := henergy n
      have heNext := henergy (n + 1)
      have hV :
          ‖(X n).2‖ ^ 2 ≤ 2 * (G 0 - G n) := by
        simp only [G, X, extragradient_trajectory] at he ⊢
        linarith
      have hGnext : G (n + 1) ≤ G 0 := by
        have hkin : 0 ≤ ‖(X (n + 1)).2‖ ^ 2 := sq_nonneg _
        simp only [G, X, extragradient_trajectory] at heNext ⊢
        nlinarith
      have haScaled :=
        mul_le_mul_of_nonneg_left ha
          (show 0 ≤ (2 : ℝ) * η from
            mul_nonneg (by norm_num) (le_of_lt hηpos))
      have hVScaled := mul_le_mul_of_nonneg_left hV (sq_nonneg η)
      have hGScaled :=
        mul_le_mul_of_nonneg_left hGnext
          (show 0 ≤ (4 : ℝ) * η ^ 2 from
            mul_nonneg (by norm_num) (sq_nonneg η))
      have hs := hsum n
      have hw := hweighted n
      have hzero : extragradient_trajectory g η x 0 0 = (x, 0) := rfl
      have hstep :
          ‖(X (n + 1)).1 - xStar‖ ^ 2 - ‖(X n).1 - xStar‖ ^ 2 +
              6 * η ^ 2 * ∑ i ∈ Finset.range (n + 1), G (i + 1)
            ≤ 4 * ((n + 1 : ℕ) : ℝ) * η ^ 2 * G 0 := by
        have haS := haScaled
        have hdS := hd
        have hVS := hVScaled
        have hGS := hGScaled
        have hsS := congrArg (fun t : ℝ => 4 * η ^ 2 * t) hs
        dsimp [X, G] at haS hdS hVS hGS hsS ⊢
        rw [hzero] at hVS hGS hsS ⊢
        simp only [Prod.fst, Nat.add_comm] at hVS hGS hsS ⊢
        simp_rw [inner_sub_left] at hdS
        simp only [Finset.sum_range_succ]
        simp only [Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_range] at haS hsS ⊢
        norm_num [Nat.cast_add, Nat.cast_mul] at haS ⊢
        ring_nf at haS hdS hVS hGS hsS ⊢
        nlinarith
      dsimp [X, G] at ih hstep hw ⊢
      rw [hzero] at hstep
      simp only [Prod.fst] at hstep
      rw [hw]
      norm_num [inner_step_mass, Nat.cast_add, Nat.cast_mul] at ih hstep ⊢
      nlinarith

@[blueprint "lem:extragradient-weighted-average-convexity"
  (statement := /-- Under \(\cref{def:hamiltonian-objective}\), let
  \(N\geq1\).  For the extragradient positions \(x_1,\ldots,x_N\) and their
  triangularly weighted average \(x^{\mathrm{avg}}\),
  \[
    Q(N)\bigl(f(x^{\mathrm{avg}})-f(x^\star)\bigr)
      \leq
    2\sum_{n=1}^{N}(N-n+1)\bigl(f(x_n)-f(x^\star)\bigr).
  \] -/)
  (proof := /-- The supporting-hyperplane clause of
  \(\cref{def:hamiltonian-objective}\) implies convexity of \(f\): apply it
  at a convex combination and take the corresponding convex combination
  of the two supporting inequalities.  Apply finite Jensen inequality with
  weights \(2(N-n+1)/Q(N)\).  These weights are nonnegative and sum to one,
  and their weighted point sum is precisely
  \(\cref{def:weighted-extragradient-average}\).  Multiplication by
  \(Q(N)>0\) gives the result. -/)
  (title := /-- Convexity bound for the triangular weighted average -/)
  (latexEnv := "lemma")]
lemma extragradient_weighted_average_convexity {d : ℕ}
    (f : hamiltonian_point d → ℝ)
    (g : hamiltonian_point d → hamiltonian_point d)
    (L η : ℝ) (xStar x : hamiltonian_point d) (N : ℕ)
    (hObjective : hamiltonian_objective f g L xStar) (hN : 1 ≤ N) :
    inner_step_mass N *
        (f (weighted_extragradient_average g η x N) - f xStar)
      ≤
    2 * ∑ i ∈ Finset.range N,
      ((N - i : ℕ) : ℝ) *
        (f (extragradient_trajectory g η x 0 (i + 1)).1 - f xStar) := by
  have hf : ConvexOn ℝ Set.univ f := by
    refine ⟨convex_univ, ?_⟩
    intro p hp q hq a b ha hb hab
    let z := a • p + b • q
    have hpa := hObjective.2.2.1 z p
    have hqb := hObjective.2.2.1 z q
    have hpa' := mul_le_mul_of_nonneg_left hpa ha
    have hqb' := mul_le_mul_of_nonneg_left hqb hb
    have hzero :
        a * inner ℝ (g z) (p - z) + b * inner ℝ (g z) (q - z) = 0 := by
      have hz : a • (p - z) + b • (q - z) = 0 := by
        calc
          a • (p - z) + b • (q - z) =
              (a • p + b • q) - (a + b) • z := by module
          _ = z - (1 : ℝ) • z := by rw [hab]
          _ = 0 := by simp
      calc
        a * inner ℝ (g z) (p - z) + b * inner ℝ (g z) (q - z) =
            inner ℝ (g z) (a • (p - z) + b • (q - z)) := by
              simp only [inner_add_right, inner_smul_right,
                RCLike.star_def, conj_trivial]
        _ = 0 := by rw [hz]; simp
    simp only [smul_eq_mul] at hpa' hqb' ⊢
    change f z ≤ a * f p + b * f q
    have habF : a * f z + b * f z = f z := by
      rw [← add_mul, hab, one_mul]
    nlinarith
  have hweightSumAll : ∀ M : ℕ,
      ∑ i ∈ Finset.range M, ((M - i : ℕ) : ℝ) =
        inner_step_mass M / 2 := by
    intro M
    induction M with
    | zero => simp [inner_step_mass]
    | succ n ih =>
        rw [Finset.sum_range_succ]
        have hparts :
            (∑ i ∈ Finset.range n, (((n + 1 - i : ℕ) : ℝ))) =
              (∑ i ∈ Finset.range n, (((n - i : ℕ) : ℝ))) + n := by
          calc
            (∑ i ∈ Finset.range n, (((n + 1 - i : ℕ) : ℝ))) =
                ∑ i ∈ Finset.range n, ((((n - i : ℕ) : ℝ)) + 1) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  have hi' : i < n := Finset.mem_range.mp hi
                  have hn : n + 1 - i = (n - i) + 1 := by omega
                  rw [hn, Nat.cast_add, Nat.cast_one]
            _ = (∑ i ∈ Finset.range n, (((n - i : ℕ) : ℝ))) + n := by
                  rw [Finset.sum_add_distrib]
                  simp
        rw [hparts]
        norm_num [inner_step_mass, Nat.cast_add, Nat.cast_mul] at ih ⊢
        nlinarith
  have hweightSum := hweightSumAll N
  have hmass : 0 < inner_step_mass N := by
    simp only [inner_step_mass]
    positivity
  let w : ℕ → ℝ := fun i =>
    2 * ((N - i : ℕ) : ℝ) / inner_step_mass N
  have hw0 : ∀ i ∈ Finset.range N, 0 ≤ w i := by
    intro i hi
    dsimp [w]
    positivity
  have hw1 : ∑ i ∈ Finset.range N, w i = 1 := by
    dsimp [w]
    calc
      (∑ i ∈ Finset.range N, 2 * ↑(N - i) / inner_step_mass N) =
          (2 / inner_step_mass N) *
            ∑ i ∈ Finset.range N, ↑(N - i) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = 1 := by
        rw [hweightSum]
        field_simp [ne_of_gt hmass]
  have hj := hf.map_sum_le (t := Finset.range N) (w := w)
    (p := fun i => (extragradient_trajectory g η x 0 (i + 1)).1)
    hw0 hw1 (fun i hi => Set.mem_univ _)
  have hpoint :
      (∑ i ∈ Finset.range N,
          w i • (extragradient_trajectory g η x 0 (i + 1)).1) =
        weighted_extragradient_average g η x N := by
    dsimp [w, weighted_extragradient_average, inner_step_mass]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    module
  rw [hpoint] at hj
  simp only [smul_eq_mul] at hj
  have hjScaled := mul_le_mul_of_nonneg_left hj (le_of_lt hmass)
  have hfunSum :
      inner_step_mass N *
          ∑ i ∈ Finset.range N,
            w i * f (extragradient_trajectory g η x 0 (i + 1)).1 =
        2 * ∑ i ∈ Finset.range N,
          ↑(N - i) * f (extragradient_trajectory g η x 0 (i + 1)).1 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [w]
    field_simp [ne_of_gt hmass]
  rw [hfunSum] at hjScaled
  have hgapExpand :
      2 * ∑ i ∈ Finset.range N,
          ↑(N - i) *
            (f (extragradient_trajectory g η x 0 (i + 1)).1 - f xStar) =
        2 * ∑ i ∈ Finset.range N,
          ↑(N - i) * f (extragradient_trajectory g η x 0 (i + 1)).1 -
            inner_step_mass N * f xStar := by
    calc
      2 * ∑ i ∈ Finset.range N,
          ↑(N - i) *
            (f (extragradient_trajectory g η x 0 (i + 1)).1 - f xStar) =
        2 * ((∑ i ∈ Finset.range N,
            ↑(N - i) * f (extragradient_trajectory g η x 0 (i + 1)).1) -
          ∑ i ∈ Finset.range N, ↑(N - i) * f xStar) := by
            congr 1
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = 2 * ∑ i ∈ Finset.range N,
          ↑(N - i) * f (extragradient_trajectory g η x 0 (i + 1)).1 -
            inner_step_mass N * f xStar := by
              rw [← Finset.sum_mul, hweightSum]
              ring
  rw [hgapExpand]
  nlinarith

@[blueprint "lem:extragradient-weighted-oracle-estimate"
  (statement := /-- Under \(\cref{def:hamiltonian-objective}\), let
  \(0<\eta\leq L^{-1/2}\), let \(N\geq1\), and restart the extragradient
  trajectory from \((x,0)\).  Then
  \[
  f(x^{\mathrm{avg}})-f(x^\star)
    +\frac{\lVert x_N-x^\star\rVert^2}{3\eta^2Q(N)}
  \leq
  \frac23\bigl(f(x)-f(x^\star)\bigr)
    +\frac{\lVert x-x^\star\rVert^2}{3\eta^2Q(N)}.
  \] -/)
  (proof := /-- The triangular trajectory estimate
  \(\cref{lem:extragradient-weighted-trajectory-sum}\) bounds six times the
  weighted sum of the objective gaps together with the terminal squared
  distance.  Convexity of the objective, in the form of
  \(\cref{lem:extragradient-weighted-average-convexity}\), bounds
  \(Q(N)(f(x^{\mathrm{avg}})-f(x^\star))\) by twice that weighted sum.
  Multiply the latter inequality by \(3\eta^2\), combine the two estimates,
  and divide by the positive quantity \(3\eta^2Q(N)\). -/)
  (title := /-- Weighted-average oracle estimate -/)
  (latexEnv := "lemma")]
lemma extragradient_weighted_oracle_estimate {d : ℕ}
    (f : hamiltonian_point d → ℝ)
    (g : hamiltonian_point d → hamiltonian_point d)
    (L η : ℝ) (xStar x : hamiltonian_point d) (N : ℕ)
    (hObjective : hamiltonian_objective f g L xStar)
    (hηpos : 0 < η) (hηmax : η ≤ 1 / Real.sqrt L) (hN : 1 ≤ N) :
    f (weighted_extragradient_average g η x N) - f xStar +
        ‖(extragradient_trajectory g η x 0 N).1 - xStar‖ ^ 2 /
          (3 * η ^ 2 * inner_step_mass N)
      ≤
    (2 / 3 : ℝ) * (f x - f xStar) +
        ‖x - xStar‖ ^ 2 / (3 * η ^ 2 * inner_step_mass N) := by
  have hL : 0 < L := hObjective.1
  have hsqrt : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hηsqrt : η * Real.sqrt L ≤ 1 := by
    calc
      η * Real.sqrt L ≤ (1 / Real.sqrt L) * Real.sqrt L :=
        mul_le_mul_of_nonneg_right hηmax (le_of_lt hsqrt)
      _ = 1 := by field_simp [ne_of_gt hsqrt]
  have hηsqrt_nonneg : 0 ≤ η * Real.sqrt L :=
    mul_nonneg (le_of_lt hηpos) (le_of_lt hsqrt)
  have hηsqrt_sq : (η * Real.sqrt L) ^ 2 ≤ 1 := by
    have hprod :=
      mul_nonneg (sub_nonneg.mpr hηsqrt)
        (by nlinarith : 0 ≤ 1 + η * Real.sqrt L)
    nlinarith
  have hsqrt_sq : (Real.sqrt L) ^ 2 = L :=
    Real.sq_sqrt (le_of_lt hL)
  have hηL : L * η ^ 2 ≤ 1 := by
    nlinarith [hηsqrt_sq]
  have hmass : 0 < inner_step_mass N := by
    simp only [inner_step_mass]
    positivity
  have havg :=
    extragradient_weighted_average_convexity f g L η xStar x N
      hObjective hN
  have htraj :=
    extragradient_weighted_trajectory_sum f g L η xStar x N
      hObjective hηpos hηmax hηL
  have havgScaled :=
    mul_le_mul_of_nonneg_left havg
      (show 0 ≤ (3 : ℝ) * η ^ 2 from
        mul_nonneg (by norm_num) (sq_nonneg η))
  have hcombined :
      3 * η ^ 2 * inner_step_mass N *
            (f (weighted_extragradient_average g η x N) - f xStar) +
          ‖(extragradient_trajectory g η x 0 N).1 - xStar‖ ^ 2
        ≤
      2 * η ^ 2 * inner_step_mass N * (f x - f xStar) +
        ‖x - xStar‖ ^ 2 := by
    nlinarith
  have hdenom : 0 < 3 * η ^ 2 * inner_step_mass N := by positivity
  calc
    f (weighted_extragradient_average g η x N) - f xStar +
          ‖(extragradient_trajectory g η x 0 N).1 - xStar‖ ^ 2 /
            (3 * η ^ 2 * inner_step_mass N) =
        (3 * η ^ 2 * inner_step_mass N *
              (f (weighted_extragradient_average g η x N) - f xStar) +
            ‖(extragradient_trajectory g η x 0 N).1 - xStar‖ ^ 2) /
            (3 * η ^ 2 * inner_step_mass N) := by
            field_simp [ne_of_gt hdenom]
    _ ≤
        (2 * η ^ 2 * inner_step_mass N * (f x - f xStar) +
            ‖x - xStar‖ ^ 2) /
          (3 * η ^ 2 * inner_step_mass N) :=
      (div_le_div_iff_of_pos_right hdenom).2 hcombined
    _ = (2 / 3 : ℝ) * (f x - f xStar) +
        ‖x - xStar‖ ^ 2 / (3 * η ^ 2 * inner_step_mass N) := by
          field_simp [ne_of_gt hdenom, ne_of_gt hηpos, ne_of_gt hmass]

@[blueprint "lem:extragradient-gradient-step-distance-nonincrease"
  (statement := /-- Let \(d\in\mathbb{N}\), let
  \(f:\mathbb{R}^{d}\to\mathbb{R}\) and
  \(g:\mathbb{R}^{d}\to\mathbb{R}^{d}\), and suppose that
  \((f,g,L,x^\star)\) satisfies \(\cref{def:hamiltonian-objective}\).
  If \(0<\eta\leq L^{-1/2}\), then, for every \(z\in\mathbb{R}^{d}\),
  \[
    \lVert z-\eta^2g(z)-x^\star\rVert^2
      \leq \lVert z-x^\star\rVert^2.
  \] -/)
  (proof := /-- Apply the smoothness inequality from
  \(\cref{def:hamiltonian-objective}\) between \(z\) and
  \(z-\eta^2g(z)\), and compare the resulting function value with the
  minimum at \(x^\star\).  The convex supporting inequality at \(z\),
  together with \(L\eta^2\leq1\), gives
  \(\eta^2\lVert g(z)\rVert^2\leq
  2\langle g(z),z-x^\star\rangle\).  Expanding the squared distance after
  the gradient step proves the claim. -/)
  (title := /-- Distance contraction of the gradient-position update -/)
  (latexEnv := "lemma")]
lemma extragradient_gradient_step_distance_nonincrease {d : ℕ}
    (f : hamiltonian_point d → ℝ)
    (g : hamiltonian_point d → hamiltonian_point d)
    (L η : ℝ) (xStar z : hamiltonian_point d)
    (hObjective : hamiltonian_objective f g L xStar)
    (hηpos : 0 < η) (hηmax : η ≤ 1 / Real.sqrt L) :
    ‖z - (η ^ 2) • g z - xStar‖ ^ 2 ≤ ‖z - xStar‖ ^ 2 := by
  rcases hObjective with ⟨hL, hgrad, hconv, hsmooth, hmin, hunique⟩
  have hsqrtpos : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hηsqrt : η * Real.sqrt L ≤ 1 := (le_div_iff₀ hsqrtpos).mp hηmax
  have hηsqrt_nonneg : 0 ≤ η * Real.sqrt L :=
    mul_nonneg hηpos.le hsqrtpos.le
  have hηL : η ^ 2 * L ≤ 1 := by
    have hprod := mul_nonneg hηsqrt_nonneg (sub_nonneg.mpr hηsqrt)
    nlinarith [Real.sq_sqrt hL.le]
  have hs := hsmooth z (z - (η ^ 2) • g z)
  have hm := hmin (z - (η ^ 2) • g z)
  have hc := hconv z xStar
  have hdiff : z - (η ^ 2) • g z - z = -((η ^ 2) • g z) := by
    module
  rw [hdiff, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq,
    norm_neg, norm_smul, Real.norm_of_nonneg (sq_nonneg η)] at hs
  have hstar :
      f z - f xStar ≤ inner ℝ (g z) (z - xStar) := by
    rw [show xStar - z = -(z - xStar) by module, inner_neg_right] at hc
    linarith
  have hmult :
      L * (η ^ 2) ^ 2 * ‖g z‖ ^ 2 ≤ (η ^ 2) * ‖g z‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_right hηL
      (mul_nonneg (sq_nonneg η) (sq_nonneg ‖g z‖))
    nlinarith
  have hfirst :
      (η ^ 2) * ‖g z‖ ^ 2 ≤
        2 * inner ℝ (g z) (z - xStar) := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hfirst (sq_nonneg η)
  rw [show z - (η ^ 2) • g z - xStar =
      (z - xStar) - (η ^ 2) • g z by module,
    @norm_sub_sq ℝ _ _ _ _ (z - xStar) ((η ^ 2) • g z), norm_smul,
    Real.norm_of_nonneg (sq_nonneg η),
    inner_smul_right]
  simp only [RCLike.re_to_real]
  rw [real_inner_comm] at hscaled
  nlinarith

@[blueprint "lem:extragradient-energy-bound-from-rest"
  (statement := /-- Under \(\cref{def:hamiltonian-objective}\), let
  \(0<\eta\leq L^{-1/2}\), and let \((x_n,y_n)\) be the trajectory of
  \(\cref{def:extragradient-trajectory}\) started from \((x,0)\).  Then, for
  every \(n\in\mathbb{N}\),
  \[
    f(x_n)+\frac12\lVert y_n\rVert^2\leq f(x).
  \] -/)
  (proof := /-- Induct on \(n\).  At \(n=0\), the identity follows from
  \(y_0=0\) in \(\cref{def:extragradient-trajectory}\).  The induction step
  is exactly \(\cref{lem:extragradient-hamiltonian-nonincrease}\), followed
  by the induction hypothesis. -/)
  (title := /-- Energy bound for a trajectory started from rest -/)
  (latexEnv := "lemma")]
lemma extragradient_energy_bound_from_rest {d : ℕ}
    (f : hamiltonian_point d → ℝ)
    (g : hamiltonian_point d → hamiltonian_point d)
    (L η : ℝ) (xStar x : hamiltonian_point d) (n : ℕ)
    (hObjective : hamiltonian_objective f g L xStar)
    (hηpos : 0 < η) (hηmax : η ≤ 1 / Real.sqrt L) :
    f (extragradient_trajectory g η x 0 n).1 +
        (1 / 2 : ℝ) * ‖(extragradient_trajectory g η x 0 n).2‖ ^ 2
      ≤ f x := by
  induction n with
  | zero => simp [extragradient_trajectory]
  | succ n ih =>
      exact le_trans
        (extragradient_hamiltonian_nonincrease f g L η xStar x 0 n
          hObjective hηpos hηmax) ih

@[blueprint "lem:extragradient-pairing-step-bound"
  (statement := /-- Suppose that \((f,g,L,x^\star)\) satisfies
  \(\cref{def:hamiltonian-objective}\), that \(\eta>0\), and that
  \(f(x_0)+\frac12\lVert y_0\rVert^2\leq f(x)\).  If
  \[
    x_{1/2}=x_0+\eta y_0,\qquad
    x_1=x_{1/2}-\eta^2g(x_{1/2}),\qquad
    y_1=y_0-\eta g(x_1),
  \]
  then
  \[
    \langle x_1-x^\star,y_1\rangle
      \leq \langle x_0-x^\star,y_0\rangle
        +2\eta\bigl(f(x)-f(x^\star)\bigr).
  \] -/)
  (proof := /-- The convex supporting inequality from
  \(\cref{def:hamiltonian-objective}\), first at \(x_{1/2}\) in the
  direction \(x_0-x_{1/2}=-\eta y_0\), controls the position-update term.
  The same inequality at \(x_1\) in the direction \(x^\star-x_1\) controls
  the velocity-update term.  Expand
  \(\langle x_1-x^\star,y_1\rangle\), use the assumed energy bound to
  control \(\lVert y_0\rVert^2\), and use global minimality of \(x^\star\)
  at \(x_0,x_{1/2},x_1\). -/)
  (title := /-- One-step bound for the position--velocity pairing -/)
  (latexEnv := "lemma")]
lemma extragradient_pairing_step_bound {d : ℕ}
    (f : hamiltonian_point d → ℝ)
    (g : hamiltonian_point d → hamiltonian_point d)
    (L η : ℝ) (xStar x x₀ y₀ xHalf x₁ y₁ : hamiltonian_point d)
    (hObjective : hamiltonian_objective f g L xStar)
    (hηpos : 0 < η)
    (hEnergy : f x₀ + (1 / 2 : ℝ) * ‖y₀‖ ^ 2 ≤ f x)
    (hHalf : xHalf = x₀ + η • y₀)
    (hNext : x₁ = xHalf - (η ^ 2) • g xHalf)
    (hVelocity : y₁ = y₀ - η • g x₁) :
    inner ℝ (x₁ - xStar) y₁ ≤
      inner ℝ (x₀ - xStar) y₀ + 2 * η * (f x - f xStar) := by
  subst xHalf
  subst x₁
  subst y₁
  rcases hObjective with ⟨hL, hgrad, hconv, hsmooth, hmin, hunique⟩
  have hhalf := hconv (x₀ + η • y₀) x₀
  rw [show x₀ - (x₀ + η • y₀) = -(η • y₀) by module,
    inner_neg_right, inner_smul_right] at hhalf
  have hhalf_scaled := mul_le_mul_of_nonneg_left hhalf hηpos.le
  have hstar := hconv (x₀ + η • y₀ - (η ^ 2) • g (x₀ + η • y₀)) xStar
  rw [show xStar - (x₀ + η • y₀ - (η ^ 2) • g (x₀ + η • y₀)) =
      -((x₀ + η • y₀ - (η ^ 2) • g (x₀ + η • y₀)) - xStar) by module,
    inner_neg_right] at hstar
  have hstar_scaled := mul_le_mul_of_nonneg_left hstar hηpos.le
  have hEnergy_scaled := mul_le_mul_of_nonneg_left hEnergy hηpos.le
  have hmin₀ := hmin x₀
  have hminHalf := hmin (x₀ + η • y₀)
  have hminNext := hmin (x₀ + η • y₀ - (η ^ 2) • g (x₀ + η • y₀))
  have hpair :
      inner ℝ
          (x₀ + η • y₀ - (η ^ 2) • g (x₀ + η • y₀) - xStar) y₀ =
        inner ℝ (x₀ - xStar) y₀ + η * ‖y₀‖ ^ 2 -
          (η ^ 2) * inner ℝ (g (x₀ + η • y₀)) y₀ := by
    rw [show x₀ + η • y₀ - (η ^ 2) • g (x₀ + η • y₀) - xStar =
        (x₀ - xStar) + η • y₀ - (η ^ 2) • g (x₀ + η • y₀) by module,
      inner_sub_left, inner_add_left,
      real_inner_comm y₀ (η • y₀), inner_smul_right,
      real_inner_self_eq_norm_sq,
      real_inner_comm y₀ ((η ^ 2) • g (x₀ + η • y₀)),
      inner_smul_right, real_inner_comm (g (x₀ + η • y₀)) y₀]
  rw [inner_sub_right, inner_smul_right, hpair,
    ← real_inner_comm
      (x₀ + η • y₀ - (η ^ 2) • g (x₀ + η • y₀) - xStar)
      (g (x₀ + η • y₀ - (η ^ 2) • g (x₀ + η • y₀)))]
  nlinarith

@[blueprint "lem:extragradient-pairing-bound-from-rest"
  (statement := /-- Under \(\cref{def:hamiltonian-objective}\), let
  \(0<\eta\leq L^{-1/2}\), and let \((x_n,y_n)\) be the trajectory of
  \(\cref{def:extragradient-trajectory}\) started from \((x,0)\).  Then, for
  every \(n\in\mathbb{N}\),
  \[
    \langle x_n-x^\star,y_n\rangle
      \leq 2n\eta\bigl(f(x)-f(x^\star)\bigr).
  \] -/)
  (proof := /-- Induct on \(n\).  The pairing vanishes at \(n=0\).  At each
  later step, \(\cref{lem:extragradient-energy-bound-from-rest}\) supplies
  the energy hypothesis required by
  \(\cref{lem:extragradient-pairing-step-bound}\), which increases the
  pairing bound by at most
  \(2\eta(f(x)-f(x^\star))\). -/)
  (title := /-- Position--velocity pairing along a restarted trajectory -/)
  (latexEnv := "lemma")]
lemma extragradient_pairing_bound_from_rest {d : ℕ}
    (f : hamiltonian_point d → ℝ)
    (g : hamiltonian_point d → hamiltonian_point d)
    (L η : ℝ) (xStar x : hamiltonian_point d) (n : ℕ)
    (hObjective : hamiltonian_objective f g L xStar)
    (hηpos : 0 < η) (hηmax : η ≤ 1 / Real.sqrt L) :
    inner ℝ
        ((extragradient_trajectory g η x 0 n).1 - xStar)
        (extragradient_trajectory g η x 0 n).2
      ≤ 2 * (n : ℝ) * η * (f x - f xStar) := by
  induction n with
  | zero => simp [extragradient_trajectory]
  | succ n ih =>
      let state := extragradient_trajectory g η x 0 n
      let xHalf := state.1 + η • state.2
      let xNext := xHalf - (η ^ 2) • g xHalf
      let yNext := state.2 - η • g xNext
      have hEnergy := extragradient_energy_bound_from_rest f g L η xStar x n
        hObjective hηpos hηmax
      have hstep := extragradient_pairing_step_bound f g L η xStar x
        state.1 state.2 xHalf xNext yNext hObjective hηpos hEnergy rfl rfl rfl
      change inner ℝ (xNext - xStar) yNext ≤
        2 * ((n + 1 : ℕ) : ℝ) * η * (f x - f xStar)
      push_cast
      nlinarith

@[blueprint "lem:extragradient-position-distance-bound-from-rest"
  (statement := /-- Under \(\cref{def:hamiltonian-objective}\), let
  \(0<\eta\leq L^{-1/2}\), and let \((x_n,y_n)\) be the trajectory of
  \(\cref{def:extragradient-trajectory}\) started from \((x,0)\).  Then, for
  every \(n\in\mathbb{N}\),
  \[
    \lVert x_n-x^\star\rVert^2-\lVert x-x^\star\rVert^2
      \leq 2\eta^2n^2\bigl(f(x)-f(x^\star)\bigr).
  \] -/)
  (proof := /-- Induct on \(n\).  For the induction step,
  \(\cref{lem:extragradient-gradient-step-distance-nonincrease}\) bounds
  the new position by the preceding half-step.  Expanding the squared norm
  of that half-step produces the position--velocity pairing and kinetic
  terms.  Bound the former by
  \(\cref{lem:extragradient-pairing-bound-from-rest}\) and the latter by
  \(\cref{lem:extragradient-energy-bound-from-rest}\); the resulting
  increment is
  \(2\eta^2(2n+1)(f(x)-f(x^\star))\), which completes the induction. -/)
  (title := /-- Pointwise distance growth along a restarted trajectory -/)
  (latexEnv := "lemma")]
lemma extragradient_position_distance_bound_from_rest {d : ℕ}
    (f : hamiltonian_point d → ℝ)
    (g : hamiltonian_point d → hamiltonian_point d)
    (L η : ℝ) (xStar x : hamiltonian_point d) (n : ℕ)
    (hObjective : hamiltonian_objective f g L xStar)
    (hηpos : 0 < η) (hηmax : η ≤ 1 / Real.sqrt L) :
    ‖(extragradient_trajectory g η x 0 n).1 - xStar‖ ^ 2 -
        ‖x - xStar‖ ^ 2
      ≤ 2 * η ^ 2 * (n : ℝ) ^ 2 * (f x - f xStar) := by
  induction n with
  | zero => simp [extragradient_trajectory]
  | succ n ih =>
      let state := extragradient_trajectory g η x 0 n
      let xHalf := state.1 + η • state.2
      let xNext := xHalf - (η ^ 2) • g xHalf
      have hcontract := extragradient_gradient_step_distance_nonincrease
        f g L η xStar xHalf hObjective hηpos hηmax
      have hpair := extragradient_pairing_bound_from_rest
        f g L η xStar x n hObjective hηpos hηmax
      have hEnergy := extragradient_energy_bound_from_rest
        f g L η xStar x n hObjective hηpos hηmax
      have hmin : ∀ z, f xStar ≤ f z := hObjective.2.2.2.2.1
      have hkinetic : ‖state.2‖ ^ 2 ≤ 2 * (f x - f xStar) := by
        have hminState := hmin state.1
        nlinarith
      have hpair_scaled := mul_le_mul_of_nonneg_left hpair
        (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hηpos.le)
      have hkinetic_scaled := mul_le_mul_of_nonneg_left hkinetic (sq_nonneg η)
      have hexpand :
          ‖xHalf - xStar‖ ^ 2 =
            ‖state.1 - xStar‖ ^ 2 +
              2 * η * inner ℝ (state.1 - xStar) state.2 +
              η ^ 2 * ‖state.2‖ ^ 2 := by
        dsimp [xHalf]
        rw [show state.1 + η • state.2 - xStar =
            (state.1 - xStar) + η • state.2 by module,
          norm_add_sq_real, inner_smul_right, norm_smul,
          Real.norm_of_nonneg hηpos.le]
        ring
      change ‖xNext - xStar‖ ^ 2 - ‖x - xStar‖ ^ 2 ≤
        2 * η ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 2 * (f x - f xStar)
      push_cast
      nlinarith [hmin x]

@[blueprint "lem:convex-squared-distance"
  (statement := /-- For every \(d\in\mathbb{N}\) and every
  \(x^\star\in\mathbb{R}^{d}\), the function
  \(z\mapsto\lVert z-x^\star\rVert^2\) is convex on
  \(\mathbb{R}^{d}\). -/)
  (proof := /-- Let \(a,b\geq0\) with \(a+b=1\).  Expand the squared norm of
  \(a(x-x^\star)+b(y-x^\star)\), bound the cross term by the real
  Cauchy--Schwarz inequality, and use
  \(ab(\lVert x-x^\star\rVert-\lVert y-x^\star\rVert)^2\geq0\). -/)
  (title := /-- Convexity of squared distance -/)
  (latexEnv := "lemma")]
lemma convex_squared_distance {d : ℕ} (xStar : hamiltonian_point d) :
    ConvexOn ℝ Set.univ (fun z : hamiltonian_point d => ‖z - xStar‖ ^ 2) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_univ] at hx hy ⊢
  rw [show a • x + b • y - xStar =
      a • (x - xStar) + b • (y - xStar) by
        calc
          a • x + b • y - xStar =
              a • x + b • y - (a + b) • xStar := by rw [hab, one_smul]
          _ = a • (x - xStar) + b • (y - xStar) := by module,
    norm_add_sq_real, norm_smul, Real.norm_of_nonneg ha,
    norm_smul, Real.norm_of_nonneg hb, real_inner_smul_left,
    real_inner_smul_right]
  simp only [smul_eq_mul]
  have hinner := real_inner_le_norm (x - xStar) (y - xStar)
  have hinner_scaled := mul_le_mul_of_nonneg_left hinner
    (mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) ha) hb)
  have hsquare := mul_nonneg (mul_nonneg ha hb)
    (sq_nonneg (‖x - xStar‖ - ‖y - xStar‖))
  have hbexpr : b = 1 - a := by linarith
  subst b
  nlinarith

@[blueprint "lem:triangular-weight-sum"
  (statement := /-- For every \(N\in\mathbb{N}\),
  \[
    \sum_{i=0}^{N-1}(N-i)=\frac{N(N+1)}2
  \]
  as an identity in \(\mathbb{R}\). -/)
  (proof := /-- Reflect the range \(\{0,\ldots,N-1\}\) to replace
  \(N-i\) by \(i+1\).  The result is the sum of the first \(N\) positive
  integers, and Gauss's finite-sum identity gives \(N(N+1)/2\). -/)
  (title := /-- Sum of the triangular weights -/)
  (latexEnv := "lemma")]
lemma triangular_weight_sum (N : ℕ) :
    (∑ i ∈ Finset.range N, ((N - i : ℕ) : ℝ)) =
      (N : ℝ) * ((N + 1 : ℕ) : ℝ) / 2 := by
  have hleft :
      (∑ i ∈ Finset.range N, ((N - i : ℕ) : ℝ)) =
        ∑ i ∈ Finset.range N, (((N - 1 - i : ℕ) : ℝ) + 1) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiN := Finset.mem_range.mp hi
    norm_cast
    omega
  have href := Finset.sum_range_reflect (fun i : ℕ => (i : ℝ) + 1) N
  have hshift :
      (∑ i ∈ Finset.range N, ((i : ℝ) + 1)) =
        ∑ i ∈ Finset.range (N + 1), (i : ℝ) := by
    rw [Finset.sum_range_succ, Finset.sum_add_distrib]
    simp
  have hgauss :
      (∑ i ∈ Finset.range (N + 1), (i : ℝ)) * 2 =
        ((N + 1 : ℕ) : ℝ) * (N : ℝ) := by
    have hn := Finset.sum_range_id_mul_two (N + 1)
    simp at hn
    rw [← Nat.cast_sum]
    exact_mod_cast hn
  rw [hleft, href, hshift]
  nlinarith

@[blueprint "lem:sum-positive-squares"
  (statement := /-- For every \(N\in\mathbb{N}\),
  \[
    \sum_{i=0}^{N-1}(i+1)^2=\frac{N(N+1)(2N+1)}6
  \]
  as an identity in \(\mathbb{R}\). -/)
  (proof := /-- Induct on \(N\).  Passing from \(N\) to \(N+1\) adds
  \((N+1)^2\) to the sum; substitution of the induction hypothesis and
  expansion of the resulting polynomial gives the displayed formula. -/)
  (title := /-- Sum of the first positive squares -/)
  (latexEnv := "lemma")]
lemma sum_positive_squares (N : ℕ) :
    (∑ i ∈ Finset.range N, (((i + 1 : ℕ) : ℝ) ^ 2)) =
      (N : ℝ) * ((N + 1 : ℕ) : ℝ) * (2 * (N : ℝ) + 1) / 6 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      push_cast at ih ⊢
      rw [ih]
      ring

@[blueprint "lem:triangular-weighted-square-sum"
  (statement := /-- For every \(N\in\mathbb{N}\),
  \[
    \sum_{i=0}^{N-1}(N-i)(i+1)^2
      =\frac{N(N+1)^2(N+2)}{12}
  \]
  as an identity in \(\mathbb{R}\). -/)
  (proof := /-- Induct on \(N\).  In the first \(N\) summands, increasing
  \(N\) by one adds \((i+1)^2\) to each weighted term, while the new final
  term is \((N+1)^2\).  Apply \(\cref{lem:sum-positive-squares}\) to the
  added sum and substitute the induction hypothesis; polynomial expansion
  yields the formula. -/)
  (title := /-- Second moment of the triangular weights -/)
  (latexEnv := "lemma")]
lemma triangular_weighted_square_sum (N : ℕ) :
    (∑ i ∈ Finset.range N,
      ((N - i : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) ^ 2)) =
      (N : ℝ) * ((N + 1 : ℕ) : ℝ) ^ 2 * ((N + 2 : ℕ) : ℝ) / 12 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hsplit :
          (∑ i ∈ Finset.range N,
              (((N + 1 - i : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) ^ 2))) =
            (∑ i ∈ Finset.range N,
              (((N - i : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) ^ 2))) +
            ∑ i ∈ Finset.range N, (((i + 1 : ℕ) : ℝ) ^ 2) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        have hiN := Finset.mem_range.mp hi
        have hnat : N + 1 - i = (N - i) + 1 := by omega
        rw [hnat]
        push_cast
        ring
      rw [hsplit, ih, sum_positive_squares]
      push_cast
      have hlast : 1 + N - N = 1 := by omega
      simp [hlast]
      ring

@[blueprint "lem:weighted-average-distance-estimate"
  (statement := /-- Let \(d\in\mathbb{N}\), let
  \(f:\mathbb{R}^{d}\to\mathbb{R}\) and
  \(g:\mathbb{R}^{d}\to\mathbb{R}^{d}\), and let \(L\in\mathbb{R}\) and
  \(x^\star\in\mathbb{R}^{d}\) be such that \((f,g,L,x^\star)\) satisfies
  \(\cref{def:hamiltonian-objective}\).  Let \(x\in\mathbb{R}^{d}\),
  \(\eta\in\mathbb{R}\), and \(N\in\mathbb{N}\) satisfy
  \(0<\eta\leq L^{-1/2}\) and \(N\geq4\).  For the extragradient trajectory
  restarted from \((x,0)\), one has
  \[
    \frac{\lVert x^{\mathrm{avg}}-x^\star\rVert^2}
         {3\eta^2Q(N)}
    \leq
    \frac{\lVert x-x^\star\rVert^2}{3\eta^2Q(N)}
      +\frac16\bigl(f(x)-f(x^\star)\bigr).
  \] -/)
  (proof := /-- By
  \(\cref{lem:extragradient-position-distance-bound-from-rest}\), each point
  of the trajectory from \((x,0)\) satisfies
  \[
    \lVert x_n-x^\star\rVert^2-\lVert x-x^\star\rVert^2
      \leq 2\eta^2n^2\bigl(f(x)-f(x^\star)\bigr).
  \]
  By \(\cref{lem:triangular-weight-sum}\), the coefficients
  \(2(N-n+1)/(N(N+1))\) are nonnegative and sum to one.  Thus the definition
  in \(\cref{def:weighted-extragradient-average}\) and Jensen's inequality
  from \(\cref{lem:convex-squared-distance}\) bound the squared distance of
  the weighted average by the corresponding weighted sum of the preceding
  pointwise bounds.  Finally,
  \(\cref{lem:triangular-weighted-square-sum}\) evaluates the required second
  moment of the weights, giving
  \[
    \lVert x^{\mathrm{avg}}-x^\star\rVert^2
    \leq \lVert x-x^\star\rVert^2+
      \frac{\eta^2(N+1)(N+2)}3
      \bigl(f(x)-f(x^\star)\bigr).
  \]
  The hypothesis \(N\geq4\) implies
  \((N+1)(N+2)\leq\frac32N(N+1)\).  Dividing by
  \(3\eta^2Q(N)\) yields the asserted estimate. -/)
  (title := /-- Distance control for the weighted average -/)
  (latexEnv := "lemma")]
lemma weighted_average_distance_estimate {d : ℕ}
    (f : hamiltonian_point d → ℝ)
    (g : hamiltonian_point d → hamiltonian_point d)
    (L η : ℝ) (xStar x : hamiltonian_point d) (N : ℕ)
    (hObjective : hamiltonian_objective f g L xStar)
    (hηpos : 0 < η) (hηmax : η ≤ 1 / Real.sqrt L) (hN : 4 ≤ N) :
    ‖weighted_extragradient_average g η x N - xStar‖ ^ 2 /
        (3 * η ^ 2 * inner_step_mass N)
      ≤
    ‖x - xStar‖ ^ 2 / (3 * η ^ 2 * inner_step_mass N) +
        (1 / 6 : ℝ) * (f x - f xStar) := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNp1pos : 0 < ((N + 1 : ℕ) : ℝ) := by positivity
  have hmasspos : 0 < inner_step_mass N := by
    unfold inner_step_mass
    positivity
  let w : ℕ → ℝ := fun i =>
    (2 / inner_step_mass N) * ((N - i : ℕ) : ℝ)
  let p : ℕ → hamiltonian_point d := fun i =>
    (extragradient_trajectory g η x 0 (i + 1)).1
  have hw_nonneg : ∀ i ∈ Finset.range N, 0 ≤ w i := by
    intro i hi
    dsimp [w]
    positivity
  have hwsum : (∑ i ∈ Finset.range N, w i) = 1 := by
    dsimp [w]
    rw [← Finset.mul_sum, triangular_weight_sum]
    unfold inner_step_mass
    field_simp
  have havg :
      weighted_extragradient_average g η x N =
        ∑ i ∈ Finset.range N, w i • p i := by
    simp [weighted_extragradient_average, inner_step_mass, w, p,
      Finset.smul_sum, smul_smul]
  have hjensen :
      ‖weighted_extragradient_average g η x N - xStar‖ ^ 2 ≤
        ∑ i ∈ Finset.range N, w i * ‖p i - xStar‖ ^ 2 := by
    rw [havg]
    simpa only [smul_eq_mul, Set.mem_univ, implies_true] using
      (convex_squared_distance xStar).map_sum_le hw_nonneg hwsum
        (fun i hi => Set.mem_univ (p i))
  have hmoment :
      (∑ i ∈ Finset.range N,
        w i * (((i + 1 : ℕ) : ℝ) ^ 2)) =
        ((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ) / 6 := by
    calc
      (∑ i ∈ Finset.range N,
          w i * (((i + 1 : ℕ) : ℝ) ^ 2)) =
          (2 / inner_step_mass N) *
            ∑ i ∈ Finset.range N,
              ((N - i : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            dsimp [w]
            ring
      _ = ((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ) / 6 := by
        rw [triangular_weighted_square_sum]
        unfold inner_step_mass
        field_simp
        ring
  have hsumBound :
      (∑ i ∈ Finset.range N, w i * ‖p i - xStar‖ ^ 2) ≤
        ∑ i ∈ Finset.range N,
          w i * (‖x - xStar‖ ^ 2 +
            2 * η ^ 2 * (((i + 1 : ℕ) : ℝ) ^ 2) *
              (f x - f xStar)) := by
    apply Finset.sum_le_sum
    intro i hi
    have hpoint := extragradient_position_distance_bound_from_rest
      f g L η xStar x (i + 1) hObjective hηpos hηmax
    have hpoint' :
        ‖p i - xStar‖ ^ 2 ≤ ‖x - xStar‖ ^ 2 +
          2 * η ^ 2 * (((i + 1 : ℕ) : ℝ) ^ 2) *
            (f x - f xStar) := by
      dsimp [p]
      linarith
    exact mul_le_mul_of_nonneg_left hpoint' (hw_nonneg i hi)
  have hrhs :
      (∑ i ∈ Finset.range N,
          w i * (‖x - xStar‖ ^ 2 +
            2 * η ^ 2 * (((i + 1 : ℕ) : ℝ) ^ 2) *
              (f x - f xStar))) =
        ‖x - xStar‖ ^ 2 +
          η ^ 2 * (((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ) / 3) *
            (f x - f xStar) := by
    calc
      (∑ i ∈ Finset.range N,
          w i * (‖x - xStar‖ ^ 2 +
            2 * η ^ 2 * (((i + 1 : ℕ) : ℝ) ^ 2) *
              (f x - f xStar))) =
          (∑ i ∈ Finset.range N, w i) * ‖x - xStar‖ ^ 2 +
            (2 * η ^ 2 * (f x - f xStar)) *
              ∑ i ∈ Finset.range N,
                w i * (((i + 1 : ℕ) : ℝ) ^ 2) := by
            rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = ‖x - xStar‖ ^ 2 +
          η ^ 2 * (((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ) / 3) *
            (f x - f xStar) := by
        rw [hwsum, hmoment]
        ring
  have hraw :
      ‖weighted_extragradient_average g η x N - xStar‖ ^ 2 ≤
        ‖x - xStar‖ ^ 2 +
          η ^ 2 * (((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ) / 3) *
            (f x - f xStar) := by
    rw [← hrhs]
    exact le_trans hjensen hsumBound
  have hmin : ∀ z, f xStar ≤ f z := hObjective.2.2.2.2.1
  have hgap : 0 ≤ f x - f xStar := sub_nonneg.mpr (hmin x)
  have hNreal : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hcoef :
      ((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ) / 3 ≤
        (1 / 2 : ℝ) * inner_step_mass N := by
    unfold inner_step_mass
    push_cast
    have hprod := mul_nonneg (show (0 : ℝ) ≤ N + 1 by positivity)
      (sub_nonneg.mpr hNreal)
    nlinarith
  have hcoef_scaled := mul_le_mul_of_nonneg_right hcoef
    (mul_nonneg (sq_nonneg η) hgap)
  have hraw' :
      ‖weighted_extragradient_average g η x N - xStar‖ ^ 2 ≤
        ‖x - xStar‖ ^ 2 +
          (1 / 2 : ℝ) * η ^ 2 * inner_step_mass N *
            (f x - f xStar) := by
    nlinarith
  have hdenpos : 0 < 3 * η ^ 2 * inner_step_mass N := by positivity
  apply (div_le_iff₀ hdenpos).2
  rw [add_mul, div_mul_cancel₀ _ hdenpos.ne']
  nlinarith

@[blueprint "lem:one-step-mixed-potential-bound"
  (statement := /-- Let \(d\in\mathbb{N}\), let
  \(f:\mathbb{R}^{d}\to\mathbb{R}\) and
  \(g:\mathbb{R}^{d}\to\mathbb{R}^{d}\), and let \(L\in\mathbb{R}\) and
  \(x^\star\in\mathbb{R}^{d}\) be such that \((f,g,L,x^\star)\) satisfies
  \(\cref{def:hamiltonian-objective}\).  For every
  \(x\in\mathbb{R}^{d}\), \(\eta,\lambda\in\mathbb{R}\), and
  \(N\in\mathbb{N}\) satisfying
  \(0<\eta\leq L^{-1/2}\), \(\lambda>0\), and \(N\geq4\), let
  \(x^{\mathrm{mix}}\) be the mixed extragradient point from
  \(\cref{def:mixed-extragradient-point}\).  Then
  \[
  \begin{aligned}
  f(x^{\mathrm{mix}})-f(x^\star)
    +\frac{\lVert x^{\mathrm{mix}}-x^\star\rVert^2}
      {3\lambda\eta^2Q(N)}
  \leq{}&
    c_\lambda\bigl(f(x)-f(x^\star)\bigr)\\
    &+\frac{\lVert x-x^\star\rVert^2}
      {3\lambda\eta^2Q(N)}.
  \end{aligned}
  \]
  where \(Q\) and \(c_\lambda\) are defined in
  \(\cref{def:inner-step-mass,def:mixed-contraction-coefficient}\),
  respectively. -/)
  (proof := /-- Induction on the inner-step index, using
  \cref{lem:extragradient-hamiltonian-nonincrease} at each step and the
  initial velocity \(y_0=0\), shows that
  \(f(x_N)+\lVert y_N\rVert^2/2\leq f(x)\).  Nonnegativity of the kinetic
  term therefore gives
  \(f(x_N)-f(x^\star)\leq f(x)-f(x^\star)\).
  Multiply this inequality by \(\lambda^2\), multiply
  \cref{lem:extragradient-weighted-oracle-estimate} by \(\lambda\), and add
  \cref{lem:weighted-average-distance-estimate}.

  The supporting-hyperplane clause of
  \cref{def:hamiltonian-objective} implies convexity of \(f\).  Apply it to
  the terminal point and weighted average with coefficients
  \(\lambda/(1+\lambda)\) and \(1/(1+\lambda)\), as in
  \cref{def:mixed-extragradient-point}, to obtain
  \[
    \lambda(1+\lambda)(f(x^{\mathrm{mix}})-f(x^\star))
    \leq \lambda^2(f(x_N)-f(x^\star))
      +\lambda(f(x^{\mathrm{avg}})-f(x^\star)).
  \]
  Applying \cref{lem:convex-squared-distance} with the same coefficients
  gives
  \[
    (1+\lambda)\lVert x^{\mathrm{mix}}-x^\star\rVert^2
    \leq \lambda\lVert x_N-x^\star\rVert^2
      +\lVert x^{\mathrm{avg}}-x^\star\rVert^2.
  \]
  Consequently, the sum of the three weighted estimates is at least
  \(\lambda(1+\lambda)\) times the asserted left-hand potential, while its
  right-hand side is
  \[
    \left(\lambda^2+\frac{2\lambda}{3}+\frac16\right)
      (f(x)-f(x^\star))
    +\frac{1+\lambda}{3\eta^2Q(N)}
      \lVert x-x^\star\rVert^2.
  \]
  Since \(\lambda>0\), \(\eta>0\), and \(Q(N)>0\), division by
  \(\lambda(1+\lambda)\) is order preserving.  Expanding
  \cref{def:mixed-contraction-coefficient} identifies the resulting
  objective-gap factor with \(c_\lambda\), proving the claim. -/)
  (title := /-- One-run mixed-potential inequality -/)
  (latexEnv := "lemma")]
lemma one_step_mixed_potential_bound {d : ℕ}
    (f : hamiltonian_point d → ℝ)
    (g : hamiltonian_point d → hamiltonian_point d)
    (L η lam : ℝ) (xStar x : hamiltonian_point d) (N : ℕ)
    (hObjective : hamiltonian_objective f g L xStar)
    (hηpos : 0 < η) (hηmax : η ≤ 1 / Real.sqrt L)
    (hLam : 0 < lam) (hN : 4 ≤ N) :
    f (mixed_extragradient_point g η lam x N) - f xStar +
        ‖mixed_extragradient_point g η lam x N - xStar‖ ^ 2 /
          (3 * lam * η ^ 2 * inner_step_mass N)
      ≤
    mixed_contraction_coefficient lam * (f x - f xStar) +
        ‖x - xStar‖ ^ 2 / (3 * lam * η ^ 2 * inner_step_mass N) := by
  let terminal := (extragradient_trajectory g η x 0 N).1
  let average := weighted_extragradient_average g η x N
  let mixed := mixed_extragradient_point g η lam x N
  let den := 3 * η ^ 2 * inner_step_mass N
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hmasspos : 0 < inner_step_mass N := by
    unfold inner_step_mass
    positivity
  have hdenpos : 0 < den := by
    dsimp [den]
    positivity
  have hLamOne : 0 < lam + 1 := by linarith
  have hEnergy : ∀ n : ℕ,
      f (extragradient_trajectory g η x 0 n).1 +
          (1 / 2 : ℝ) * ‖(extragradient_trajectory g η x 0 n).2‖ ^ 2 ≤ f x := by
    intro n
    induction n with
    | zero => simp [extragradient_trajectory]
    | succ n ih =>
        exact le_trans
          (extragradient_hamiltonian_nonincrease f g L η xStar x 0 n
            hObjective hηpos hηmax) ih
  have hTerminal : f terminal - f xStar ≤ f x - f xStar := by
    have hkinetic :
        0 ≤ (1 / 2 : ℝ) * ‖(extragradient_trajectory g η x 0 N).2‖ ^ 2 := by
      positivity
    dsimp [terminal]
    nlinarith [hEnergy N]
  have hNOne : 1 ≤ N := by omega
  have hOracle := extragradient_weighted_oracle_estimate
    f g L η xStar x N hObjective hηpos hηmax hNOne
  change f average - f xStar + ‖terminal - xStar‖ ^ 2 / den ≤
      (2 / 3 : ℝ) * (f x - f xStar) + ‖x - xStar‖ ^ 2 / den at hOracle
  have hDistance := weighted_average_distance_estimate
    f g L η xStar x N hObjective hηpos hηmax hN
  change ‖average - xStar‖ ^ 2 / den ≤
      ‖x - xStar‖ ^ 2 / den + (1 / 6 : ℝ) * (f x - f xStar) at hDistance
  have hConvex : ConvexOn ℝ Set.univ f := by
    refine ⟨convex_univ, ?_⟩
    intro p hp q hq a b ha hb hab
    let z := a • p + b • q
    have hpa := hObjective.2.2.1 z p
    have hqb := hObjective.2.2.1 z q
    have hpa' := mul_le_mul_of_nonneg_left hpa ha
    have hqb' := mul_le_mul_of_nonneg_left hqb hb
    have hzero :
        a * inner ℝ (g z) (p - z) + b * inner ℝ (g z) (q - z) = 0 := by
      have hz : a • (p - z) + b • (q - z) = 0 := by
        calc
          a • (p - z) + b • (q - z) =
              (a • p + b • q) - (a + b) • z := by module
          _ = z - (1 : ℝ) • z := by rw [hab]
          _ = 0 := by simp
      calc
        a * inner ℝ (g z) (p - z) + b * inner ℝ (g z) (q - z) =
            inner ℝ (g z) (a • (p - z) + b • (q - z)) := by
              simp only [inner_add_right, inner_smul_right,
                RCLike.star_def, conj_trivial]
        _ = 0 := by rw [hz]; simp
    simp only [smul_eq_mul] at hpa' hqb' ⊢
    change f z ≤ a * f p + b * f q
    have habF : a * f z + b * f z = f z := by
      rw [← add_mul, hab, one_mul]
    nlinarith
  have ha : 0 ≤ lam / (lam + 1) := by positivity
  have hb : 0 ≤ (1 : ℝ) / (lam + 1) := by positivity
  have hab : lam / (lam + 1) + 1 / (lam + 1) = (1 : ℝ) := by
    field_simp
  have hmixed :
      mixed = (lam / (lam + 1)) • terminal +
        (1 / (lam + 1)) • average := by
    rfl
  have hFunctionRaw := hConvex.2
    (Set.mem_univ terminal) (Set.mem_univ average) ha hb hab
  rw [← hmixed] at hFunctionRaw
  have hFunctionGap :
      f mixed - f xStar ≤
        (lam / (lam + 1)) * (f terminal - f xStar) +
          (1 / (lam + 1)) * (f average - f xStar) := by
    calc
      f mixed - f xStar ≤
          (lam / (lam + 1)) * f terminal +
              (1 / (lam + 1)) * f average - f xStar :=
        sub_le_sub_right hFunctionRaw (f xStar)
      _ = (lam / (lam + 1)) * (f terminal - f xStar) +
          (1 / (lam + 1)) * (f average - f xStar) := by
            field_simp [hLamOne.ne']
            ring
  have hFunctionMix :
      lam * (lam + 1) * (f mixed - f xStar) ≤
        lam ^ 2 * (f terminal - f xStar) +
          lam * (f average - f xStar) := by
    calc
      lam * (lam + 1) * (f mixed - f xStar) ≤
          lam * (lam + 1) *
            ((lam / (lam + 1)) * (f terminal - f xStar) +
              (1 / (lam + 1)) * (f average - f xStar)) :=
        mul_le_mul_of_nonneg_left hFunctionGap
          (mul_nonneg (le_of_lt hLam) (le_of_lt hLamOne))
      _ = lam ^ 2 * (f terminal - f xStar) +
          lam * (f average - f xStar) := by
            field_simp [hLamOne.ne']
  have hDistanceRaw := (convex_squared_distance xStar).2
    (Set.mem_univ terminal) (Set.mem_univ average) ha hb hab
  rw [← hmixed] at hDistanceRaw
  have hDistanceMix :
      (lam + 1) * ‖mixed - xStar‖ ^ 2 ≤
        lam * ‖terminal - xStar‖ ^ 2 + ‖average - xStar‖ ^ 2 := by
    calc
      (lam + 1) * ‖mixed - xStar‖ ^ 2 ≤
          (lam + 1) *
            ((lam / (lam + 1)) * ‖terminal - xStar‖ ^ 2 +
              (1 / (lam + 1)) * ‖average - xStar‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hDistanceRaw (le_of_lt hLamOne)
      _ = lam * ‖terminal - xStar‖ ^ 2 +
          ‖average - xStar‖ ^ 2 := by
            field_simp [hLamOne.ne']
  have hDistanceMixDiv :
      (lam + 1) * ‖mixed - xStar‖ ^ 2 / den ≤
        lam * ‖terminal - xStar‖ ^ 2 / den +
          ‖average - xStar‖ ^ 2 / den := by
    calc
      (lam + 1) * ‖mixed - xStar‖ ^ 2 / den ≤
          (lam * ‖terminal - xStar‖ ^ 2 +
            ‖average - xStar‖ ^ 2) / den :=
        (div_le_div_iff_of_pos_right hdenpos).2 hDistanceMix
      _ = lam * ‖terminal - xStar‖ ^ 2 / den +
          ‖average - xStar‖ ^ 2 / den := by ring
  have hTerminalScaled := mul_le_mul_of_nonneg_left hTerminal (sq_nonneg lam)
  have hOracleScaled := mul_le_mul_of_nonneg_left hOracle (le_of_lt hLam)
  have hCombined :
      lam ^ 2 * (f terminal - f xStar) +
          lam * (f average - f xStar) +
          lam * ‖terminal - xStar‖ ^ 2 / den +
          ‖average - xStar‖ ^ 2 / den ≤
        (lam ^ 2 + 2 * lam / 3 + 1 / 6) * (f x - f xStar) +
          (lam + 1) * ‖x - xStar‖ ^ 2 / den := by
    linear_combination hTerminalScaled + hOracleScaled + hDistance
  have hLow :
      lam * (lam + 1) *
          (f mixed - f xStar + ‖mixed - xStar‖ ^ 2 / (lam * den)) ≤
        lam ^ 2 * (f terminal - f xStar) +
          lam * (f average - f xStar) +
          lam * ‖terminal - xStar‖ ^ 2 / den +
          ‖average - xStar‖ ^ 2 / den := by
    calc
      lam * (lam + 1) *
          (f mixed - f xStar + ‖mixed - xStar‖ ^ 2 / (lam * den)) =
        lam * (lam + 1) * (f mixed - f xStar) +
          (lam + 1) * ‖mixed - xStar‖ ^ 2 / den := by
            field_simp [hLam.ne', hdenpos.ne']
      _ ≤ lam ^ 2 * (f terminal - f xStar) +
          lam * (f average - f xStar) +
          lam * ‖terminal - xStar‖ ^ 2 / den +
          ‖average - xStar‖ ^ 2 / den := by
            nlinarith
  have hscale : 0 < lam * (lam + 1) := mul_pos hLam hLamOne
  have hRight :
      ((lam ^ 2 + 2 * lam / 3 + 1 / 6) * (f x - f xStar) +
          (lam + 1) * ‖x - xStar‖ ^ 2 / den) /
          (lam * (lam + 1)) =
        mixed_contraction_coefficient lam * (f x - f xStar) +
          ‖x - xStar‖ ^ 2 / (lam * den) := by
    unfold mixed_contraction_coefficient
    field_simp [hLam.ne', hLamOne.ne', hdenpos.ne']
    ring
  have hResult :
      f mixed - f xStar + ‖mixed - xStar‖ ^ 2 / (lam * den) ≤
        mixed_contraction_coefficient lam * (f x - f xStar) +
          ‖x - xStar‖ ^ 2 / (lam * den) := by
    calc
      f mixed - f xStar + ‖mixed - xStar‖ ^ 2 / (lam * den) ≤
          (lam ^ 2 * (f terminal - f xStar) +
            lam * (f average - f xStar) +
            lam * ‖terminal - xStar‖ ^ 2 / den +
            ‖average - xStar‖ ^ 2 / den) / (lam * (lam + 1)) :=
        (le_div_iff₀ hscale).2 (by simpa only [mul_comm] using hLow)
      _ ≤ ((lam ^ 2 + 2 * lam / 3 + 1 / 6) * (f x - f xStar) +
            (lam + 1) * ‖x - xStar‖ ^ 2 / den) / (lam * (lam + 1)) :=
        (div_le_div_iff_of_pos_right hscale).2 hCombined
      _ = mixed_contraction_coefficient lam * (f x - f xStar) +
          ‖x - xStar‖ ^ 2 / (lam * den) := hRight
  change f mixed - f xStar +
      ‖mixed - xStar‖ ^ 2 / (3 * lam * η ^ 2 * inner_step_mass N) ≤
    mixed_contraction_coefficient lam * (f x - f xStar) +
      ‖x - xStar‖ ^ 2 / (3 * lam * η ^ 2 * inner_step_mass N)
  have hdenLam : 3 * lam * η ^ 2 * inner_step_mass N = lam * den := by
    dsimp [den]
    ring
  rw [hdenLam]
  exact hResult

@[blueprint "lem:fixed-mixing-parameter-identities"
  (statement := /-- For the mixing parameter \(\lambda_\star\), convergence rate
  \(\rho\), contraction coefficient \(c_\lambda\), and inner-step mass \(Q\)
  defined in \cref{def:mixing-parameter,def:convergence-rate,
  def:mixed-contraction-coefficient,def:inner-step-mass}, one has
  \[
    \lambda_\star>0,\qquad
    c_{\lambda_\star}=\rho,\qquad 0<\rho<1,
  \]
  and, for every \(\eta\in\mathbb{R}\) satisfying \(\eta>0\),
  \[
    \frac{1}{3\lambda_\star\eta^2Q(4)}
      =\frac{\sqrt3-1}{60\eta^2}.
  \] -/)
  (proof := /-- Unfold the definitions in
  \cref{def:mixing-parameter,def:convergence-rate,
  def:mixed-contraction-coefficient,def:inner-step-mass}, and write
  \(s=\sqrt3\).  The relations \(s>0\) and \(s^2=3\) imply
  \(\lambda_\star>0\), \(\rho>0\), and \(s<2\), whence \(\rho<1\).
  After clearing the positive denominators, the equality
  \(c_{\lambda_\star}=\rho\) reduces to \(s^2=3\).  Finally, if
  \(\eta>0\), then \(\eta\neq0\); using \(Q(4)=20\) and clearing
  denominators reduces the last equality to
  \((s+1)(s-1)=2\), which again follows from \(s^2=3\). -/)
  (title := /-- Identities for the accelerating constants -/)
  (latexEnv := "lemma")]
lemma fixed_mixing_parameter_identities :
    0 < mixing_parameter ∧
      mixed_contraction_coefficient mixing_parameter = convergence_rate ∧
      0 < convergence_rate ∧ convergence_rate < 1 ∧
      ∀ η : ℝ, 0 < η →
        1 / (3 * mixing_parameter * η ^ 2 * inner_step_mass 4) =
          (Real.sqrt 3 - 1) / (60 * η ^ 2) := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [mixing_parameter, mixed_contraction_coefficient, convergence_rate,
    inner_step_mass]
  constructor
  · nlinarith
  constructor
  · field_simp
    nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · intro η hη
    field_simp
    norm_num
    nlinarith

@[blueprint "lem:admissible-schedule-lower-bound"
  (statement := /-- Let \(K\in\mathbb{N}\) and \(N:\mathbb{N}\to\mathbb{N}\).
  If \(N\) is admissible through outer iteration \(K\) in the sense of
  \cref{def:admissible-inner-schedule}, then \(N_k\geq4\) for every
  \(k\in\mathbb{N}\) satisfying \(k\leq K\). -/)
  (proof := /-- By \cref{lem:fixed-mixing-parameter-identities} and
  \cref{def:convergence-rate}, one has \(0<\sqrt3+1\) and
  \(1\leq3/(\sqrt3+1)\).  Since \(Q(N_k)\geq0\), the recurrence in
  \cref{def:admissible-inner-schedule} therefore yields
  \(Q(N_k)\leq Q(N_{k+1})\) whenever \(k<K\).  We argue by induction on
  \(k\).  The base case is \(N_0=4\).  For the induction step, suppose
  \(k+1\leq K\) and \(N_k\geq4\).  By
  \cref{def:inner-step-mass}, \(Q(N_k)\geq20\).  If
  \(N_{k+1}<4\), then \(N_{k+1}\leq3\), so \(Q(N_{k+1})\leq12\),
  contradicting \(Q(N_k)\leq Q(N_{k+1})\).  Hence
  \(N_{k+1}\geq4\), which completes the induction. -/)
  (title := /-- Uniform lower bound for inner step counts -/)
  (latexEnv := "lemma")]
lemma admissible_schedule_lower_bound (N : ℕ → ℕ) (K : ℕ)
    (hSchedule : admissible_inner_schedule N K) :
    ∀ k, k ≤ K → 4 ≤ N k := by
  rcases fixed_mixing_parameter_identities with
    ⟨_, _, hRatePos, hRateLt, _⟩
  have hDenPos : 0 < Real.sqrt 3 + 1 := by
    rw [convergence_rate] at hRatePos
    nlinarith
  have hFactor : 1 ≤ 3 / (Real.sqrt 3 + 1) := by
    rw [le_div_iff₀ hDenPos]
    rw [convergence_rate] at hRateLt
    nlinarith
  intro k
  induction k with
  | zero =>
      intro hk
      have hBase := hSchedule.1
      omega
  | succ k ih =>
      intro hk
      have hklt : k < K := by omega
      have hPrev : 4 ≤ N k := ih (by omega)
      have hStep := hSchedule.2 k hklt
      have hMassNonneg : 0 ≤ inner_step_mass (N k) := by
        unfold inner_step_mass
        positivity
      have hMassMono : inner_step_mass (N k) ≤ inner_step_mass (N (k + 1)) := by
        calc
          inner_step_mass (N k) ≤
              (3 / (Real.sqrt 3 + 1)) * inner_step_mass (N k) := by
            nlinarith
          _ ≤ inner_step_mass (N (k + 1)) := hStep
      by_contra hNext
      have hNextUpper : N (k + 1) ≤ 3 := by omega
      have hPrevCast : (4 : ℝ) ≤ N k := by exact_mod_cast hPrev
      have hNextCast : (N (k + 1) : ℝ) ≤ 3 := by exact_mod_cast hNextUpper
      have hPrevNonneg : (0 : ℝ) ≤ N k := by positivity
      have hNextNonneg : (0 : ℝ) ≤ N (k + 1) := by positivity
      norm_num [inner_step_mass] at hMassMono
      nlinarith

@[blueprint "lem:outer-potential-geometric-bound"
  (statement := /-- Let \(d\in\mathbb{N}\), let
  \(f:\mathbb{R}^{d}\to\mathbb{R}\) and
  \(g:\mathbb{R}^{d}\to\mathbb{R}^{d}\), and let
  \(L,\eta\in\mathbb{R}\), \(x^\star,x_0\in\mathbb{R}^{d}\),
  \(N:\mathbb{N}\to\mathbb{N}\), and \(K\in\mathbb{N}\).  Assume that
  \((f,g,L,x^\star)\) satisfies
  \(\cref{def:hamiltonian-objective}\), that
  \(0<\eta\leq L^{-1/2}\), and that \(N\) is admissible through iteration
  \(K\) in the sense of \(\cref{def:admissible-inner-schedule}\).  Let
  \(x_K\) be the \(K\)-th accelerated outer iterate from
  \(\cref{def:accelerated-outer-iterate}\), started at \(x_0\) with oracle
  \(g\), step size \(\eta\), mixing parameter \(\lambda_\star\), and
  schedule \(N\), where \(\lambda_\star\) and \(\rho\) are defined in
  \(\cref{def:mixing-parameter,def:convergence-rate}\), one has
  \[
    \Phi_{\eta,N(K)}(x_K)
      \leq \rho^K\Phi_{\eta,N(0)}(x_0),
  \]
  where \(\Phi\) is the discrete potential from
  \(\cref{def:discrete-potential}\). -/)
  (proof := /-- Write \(Q_k=Q(N_k)\).  By
  \cref{lem:fixed-mixing-parameter-identities}, the mixing parameter is
  positive, its one-run contraction coefficient equals \(\rho>0\), and
  \[
    \rho\frac{3}{\sqrt{3}+1}=1.
  \]
  We prove the asserted inequality with \(K\) replaced by every
  \(k\leq K\), by induction on \(k\).  The case \(k=0\) is equality.

  Suppose the assertion holds at \(k\), where \(k+1\leq K\).  The lower
  bound \(N_k,N_{k+1}\geq4\) follows from
  \cref{lem:admissible-schedule-lower-bound}; hence both relevant potential
  denominators are positive.  Admissibility and the displayed constant
  identity give
  \[
    Q_k\leq \rho Q_{k+1}.
  \]
  Since the squared distance is nonnegative, division by the positive
  denominators yields
  \[
    \frac{\lVert x_k-x^\star\rVert^2}
      {3\lambda_\star\eta^2Q_{k+1}}
    \leq
    \rho\frac{\lVert x_k-x^\star\rVert^2}
      {3\lambda_\star\eta^2Q_k}.
  \]
  Apply \cref{lem:one-step-mixed-potential-bound} to the run from \(x_k\)
  with \(N_{k+1}\) inner steps, replace its contraction coefficient by
  \(\rho\), and use the last inequality.  This gives
  \(\Phi_{\eta,N_{k+1}}(x_{k+1})\leq
  \rho\Phi_{\eta,N_k}(x_k)\).  Multiplication of the induction hypothesis
  by \(\rho>0\) completes the induction. -/)
  (title := /-- Geometric contraction of the outer potential -/)
  (latexEnv := "lemma")]
lemma outer_potential_geometric_bound {d : ℕ}
    (f : hamiltonian_point d → ℝ)
    (g : hamiltonian_point d → hamiltonian_point d)
    (L η : ℝ) (xStar x₀ : hamiltonian_point d)
    (N : ℕ → ℕ) (K : ℕ)
    (hObjective : hamiltonian_objective f g L xStar)
    (hηpos : 0 < η) (hηmax : η ≤ 1 / Real.sqrt L)
    (hSchedule : admissible_inner_schedule N K) :
    discrete_potential f xStar η (N K)
        (accelerated_outer_iterate g η mixing_parameter N x₀ K)
      ≤
    convergence_rate ^ K * discrete_potential f xStar η (N 0) x₀ := by
  rcases fixed_mixing_parameter_identities with
    ⟨hMixPos, hCoeff, hRatePos, _, _⟩
  have hSqrtPos : 0 < Real.sqrt 3 + 1 := by positivity
  have hFactor :
      convergence_rate * (3 / (Real.sqrt 3 + 1)) = 1 := by
    rw [convergence_rate]
    field_simp [ne_of_gt hSqrtPos]
  have hContract : ∀ k : ℕ, k ≤ K →
      discrete_potential f xStar η (N k)
          (accelerated_outer_iterate g η mixing_parameter N x₀ k)
        ≤ convergence_rate ^ k *
          discrete_potential f xStar η (N 0) x₀ := by
    intro k
    induction k with
    | zero =>
        intro _
        simp [accelerated_outer_iterate]
    | succ k ih =>
        intro hk
        have hkLe : k ≤ K := by omega
        have hkLt : k < K := by omega
        have hNk : 4 ≤ N k :=
          admissible_schedule_lower_bound N K hSchedule k hkLe
        have hNnext : 4 ≤ N (k + 1) :=
          admissible_schedule_lower_bound N K hSchedule (k + 1) hk
        have hMassPrev : 0 < inner_step_mass (N k) := by
          unfold inner_step_mass
          have : 0 < N k := by omega
          positivity
        have hMassNext : 0 < inner_step_mass (N (k + 1)) := by
          unfold inner_step_mass
          have : 0 < N (k + 1) := by omega
          positivity
        have hRecurrence := hSchedule.2 k hkLt
        have hMassRate :
            inner_step_mass (N k) ≤
              convergence_rate * inner_step_mass (N (k + 1)) := by
          calc
            inner_step_mass (N k) =
                (convergence_rate * (3 / (Real.sqrt 3 + 1))) *
                  inner_step_mass (N k) := by simp [hFactor]
            _ = convergence_rate *
                ((3 / (Real.sqrt 3 + 1)) * inner_step_mass (N k)) := by
                  ring
            _ ≤ convergence_rate * inner_step_mass (N (k + 1)) :=
              mul_le_mul_of_nonneg_left hRecurrence (le_of_lt hRatePos)
        have hCommon : 0 < 3 * mixing_parameter * η ^ 2 := by positivity
        have hDenPrev :
            0 < 3 * mixing_parameter * η ^ 2 * inner_step_mass (N k) := by
          positivity
        have hDenNext :
            0 < 3 * mixing_parameter * η ^ 2 *
              inner_step_mass (N (k + 1)) := by
          positivity
        have hDenRate :
            3 * mixing_parameter * η ^ 2 * inner_step_mass (N k) ≤
              convergence_rate *
                (3 * mixing_parameter * η ^ 2 *
                  inner_step_mass (N (k + 1))) := by
          calc
            3 * mixing_parameter * η ^ 2 * inner_step_mass (N k) ≤
                (3 * mixing_parameter * η ^ 2) *
                  (convergence_rate * inner_step_mass (N (k + 1))) :=
              mul_le_mul_of_nonneg_left hMassRate (le_of_lt hCommon)
            _ = convergence_rate *
                (3 * mixing_parameter * η ^ 2 *
                  inner_step_mass (N (k + 1))) := by ring
        have hDistance :
            ‖accelerated_outer_iterate g η mixing_parameter N x₀ k - xStar‖ ^ 2 /
                (3 * mixing_parameter * η ^ 2 *
                  inner_step_mass (N (k + 1))) ≤
              convergence_rate *
                (‖accelerated_outer_iterate g η mixing_parameter N x₀ k - xStar‖ ^ 2 /
                  (3 * mixing_parameter * η ^ 2 * inner_step_mass (N k))) := by
          calc
            ‖accelerated_outer_iterate g η mixing_parameter N x₀ k - xStar‖ ^ 2 /
                (3 * mixing_parameter * η ^ 2 *
                  inner_step_mass (N (k + 1))) ≤
                (convergence_rate *
                    ‖accelerated_outer_iterate g η mixing_parameter N x₀ k - xStar‖ ^ 2) /
                  (3 * mixing_parameter * η ^ 2 * inner_step_mass (N k)) := by
              rw [div_le_div_iff₀ hDenNext hDenPrev]
              calc
                ‖accelerated_outer_iterate g η mixing_parameter N x₀ k - xStar‖ ^ 2 *
                    (3 * mixing_parameter * η ^ 2 * inner_step_mass (N k)) ≤
                    ‖accelerated_outer_iterate g η mixing_parameter N x₀ k - xStar‖ ^ 2 *
                      (convergence_rate *
                        (3 * mixing_parameter * η ^ 2 *
                          inner_step_mass (N (k + 1)))) :=
                  mul_le_mul_of_nonneg_left hDenRate (sq_nonneg _)
                _ = (convergence_rate *
                      ‖accelerated_outer_iterate g η mixing_parameter N x₀ k - xStar‖ ^ 2) *
                    (3 * mixing_parameter * η ^ 2 *
                      inner_step_mass (N (k + 1))) := by ring
            _ = convergence_rate *
                (‖accelerated_outer_iterate g η mixing_parameter N x₀ k - xStar‖ ^ 2 /
                  (3 * mixing_parameter * η ^ 2 * inner_step_mass (N k))) := by
              ring
        have hOne := one_step_mixed_potential_bound f g L η mixing_parameter
          xStar (accelerated_outer_iterate g η mixing_parameter N x₀ k)
          (N (k + 1)) hObjective hηpos hηmax hMixPos hNnext
        rw [hCoeff] at hOne
        calc
          discrete_potential f xStar η (N (k + 1))
              (accelerated_outer_iterate g η mixing_parameter N x₀ (k + 1)) ≤
              convergence_rate *
                  (f (accelerated_outer_iterate g η mixing_parameter N x₀ k) - f xStar) +
                ‖accelerated_outer_iterate g η mixing_parameter N x₀ k - xStar‖ ^ 2 /
                  (3 * mixing_parameter * η ^ 2 *
                    inner_step_mass (N (k + 1))) := by
            simpa only [discrete_potential, accelerated_outer_iterate] using hOne
          _ ≤ convergence_rate *
              discrete_potential f xStar η (N k)
                (accelerated_outer_iterate g η mixing_parameter N x₀ k) := by
            rw [discrete_potential]
            linarith
          _ ≤ convergence_rate *
              (convergence_rate ^ k *
                discrete_potential f xStar η (N 0) x₀) :=
            mul_le_mul_of_nonneg_left (ih hkLe) (le_of_lt hRatePos)
          _ = convergence_rate ^ (k + 1) *
              discrete_potential f xStar η (N 0) x₀ := by ring
  exact hContract K le_rfl

@[blueprint "lem:initial-potential-identity"
  (statement := /-- For every \(d\in\mathbb{N}\), every function
  \(f:\mathbb{R}^{d}\to\mathbb{R}\), every pair of points
  \(x^\star,x\in\mathbb{R}^{d}\), and every \(\eta\in\mathbb{R}\) satisfying
  \(\eta>0\),
  \[
    \Phi_{\eta,4}(x)=f(x)-f(x^\star)+
      \frac{\sqrt3-1}{60\eta^2}\lVert x-x^\star\rVert^2.
  \] -/)
  (proof := /-- Unfold \cref{def:discrete-potential}.  Apply the final identity
  of \cref{lem:fixed-mixing-parameter-identities} to the given
  \(\eta\in\mathbb{R}\) and the hypothesis \(\eta>0\), thereby identifying the
  reciprocal of \(3\lambda_\star\eta^2Q(4)\) with
  \((\sqrt3-1)/(60\eta^2)\).  Rewrite division by the former denominator as
  multiplication by its reciprocal and commute the two real factors. -/)
  (title := /-- Initial potential in closed form -/)
  (latexEnv := "lemma")]
lemma initial_potential_identity {d : ℕ}
    (f : hamiltonian_point d → ℝ) (xStar x : hamiltonian_point d)
    (η : ℝ) (hηpos : 0 < η) :
    discrete_potential f xStar η 4 x =
      f x - f xStar +
        ((Real.sqrt 3 - 1) / (60 * η ^ 2)) * ‖x - xStar‖ ^ 2 := by
  unfold discrete_potential
  have hcoeff := fixed_mixing_parameter_identities.2.2.2.2 η hηpos
  rw [one_div] at hcoeff
  rw [div_eq_mul_inv, hcoeff, mul_comm]

@[blueprint "lem:objective-gap-le-discrete-potential"
  (statement := /-- Let \(d,N\in\mathbb{N}\), let
  \(f:\mathbb{R}^{d}\to\mathbb{R}\), let \(x,x^\star\in\mathbb{R}^{d}\),
  and let \(\eta\in\mathbb{R}\).  If \(\eta>0\) and \(N\geq1\), then
  \[
    f(x)-f(x^\star)\leq\Phi_{\eta,N}(x).
  \] -/)
  (proof := /-- By \cref{lem:fixed-mixing-parameter-identities},
  \(\lambda_\star>0\).  The hypothesis \(N\geq1\), together with
  \cref{def:inner-step-mass}, gives \(Q(N)=N(N+1)>0\).  Since
  \(\eta>0\), one also has \(\eta^2>0\), and hence
  \(3\lambda_\star\eta^2Q(N)>0\).  The squared norm
  \(\lVert x-x^\star\rVert^2\) is nonnegative, so its quotient by this
  positive denominator is nonnegative.  The definition in
  \cref{def:discrete-potential} now shows that \(\Phi_{\eta,N}(x)\) is
  the objective gap plus a nonnegative term. -/)
  (title := /-- The potential dominates the objective gap -/)
  (latexEnv := "lemma")]
lemma objective_gap_le_discrete_potential {d : ℕ}
    (f : hamiltonian_point d → ℝ) (xStar x : hamiltonian_point d)
    (η : ℝ) (N : ℕ) (hηpos : 0 < η) (hN : 1 ≤ N) :
    f x - f xStar ≤ discrete_potential f xStar η N x := by
  rw [discrete_potential]
  apply le_add_of_nonneg_right
  have hmix : 0 < mixing_parameter := fixed_mixing_parameter_identities.1
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  unfold inner_step_mass
  exact div_nonneg (sq_nonneg _) (by positivity)

@[blueprint "thm:hf-extg-cvx"
  (statement := /-- Let \(d\in\mathbb{N}\), let
  \(f:\mathbb{R}^{d}\to\mathbb{R}\) and
  \(g:\mathbb{R}^{d}\to\mathbb{R}^{d}\), let \(L,\eta\in\mathbb{R}\),
  let \(x^\star,x_0\in\mathbb{R}^{d}\), let
  \(N:\mathbb{N}\to\mathbb{N}\), and let \(K\in\mathbb{N}\).  Assume
  that \((f,g,L,x^\star)\) satisfies
  \(\cref{def:hamiltonian-objective}\), that
  \(0<\eta\leq1/\sqrt L\), and that \(N_0=4\) and
  \[
    N_k(N_k+1)\geq
    \frac{3}{\sqrt3+1}N_{k-1}(N_{k-1}+1)
    \qquad(1\leq k\leq K).
  \]
  Define \(x_K\) to be the \(K\)-th iterate from
  \(\cref{def:accelerated-outer-iterate}\), started from \(x_0\) with
  oracle \(g\), step size \(\eta\), schedule \(N\), and mixing parameter
  \(\lambda=(\sqrt3+1)/2\).  Then
  \[
  f(x_K)-f(x^\star)\leq
  \left(\frac{\sqrt3+1}{3}\right)^K
  \left(
    f(x_0)-f(x^\star)+
    \frac{\sqrt3-1}{60\eta^2}\lVert x_0-x^\star\rVert^2
  \right).
  \] -/)
  (proof := /-- By \cref{lem:admissible-schedule-lower-bound} with \(k=K\),
  one has \(N_K\geq4\), and hence \(N_K\geq1\).  Therefore
  \cref{lem:objective-gap-le-discrete-potential} bounds the terminal
  objective gap by \(\Phi_{\eta,N_K}(x_K)\).  Applying
  \cref{lem:outer-potential-geometric-bound} gives
  \[
    f(x_K)-f(x^\star)\leq
    \rho^K\Phi_{\eta,N_0}(x_0).
  \]
  Admissibility gives \(N_0=4\), so
  \cref{lem:initial-potential-identity} rewrites the initial potential as
  \[
    f(x_0)-f(x^\star)+
    \frac{\sqrt3-1}{60\eta^2}\lVert x_0-x^\star\rVert^2.
  \]
  Substituting \(\rho=(\sqrt3+1)/3\) from
  \cref{def:convergence-rate} yields the asserted inequality. -/)
  (title := /-- Accelerated convergence of deterministic-time discretized Hamiltonian flow -/)
  (latexEnv := "theorem")]
theorem hf_extg_cvx {d : ℕ}
    (f : hamiltonian_point d → ℝ)
    (g : hamiltonian_point d → hamiltonian_point d)
    (L η : ℝ) (xStar x₀ : hamiltonian_point d)
    (N : ℕ → ℕ) (K : ℕ)
    (hObjective : hamiltonian_objective f g L xStar)
    (hηpos : 0 < η) (hηmax : η ≤ 1 / Real.sqrt L)
    (hSchedule : admissible_inner_schedule N K) :
    f (accelerated_outer_iterate g η mixing_parameter N x₀ K) - f xStar
      ≤
    ((Real.sqrt 3 + 1) / 3) ^ K *
      (f x₀ - f xStar +
        ((Real.sqrt 3 - 1) / (60 * η ^ 2)) * ‖x₀ - xStar‖ ^ 2) := by
  have hNK : 1 ≤ N K := by
    have hNK4 := admissible_schedule_lower_bound N K hSchedule K le_rfl
    omega
  calc
    f (accelerated_outer_iterate g η mixing_parameter N x₀ K) - f xStar ≤
        discrete_potential f xStar η (N K)
          (accelerated_outer_iterate g η mixing_parameter N x₀ K) :=
      objective_gap_le_discrete_potential f xStar _ η (N K) hηpos hNK
    _ ≤ convergence_rate ^ K * discrete_potential f xStar η (N 0) x₀ :=
      outer_potential_geometric_bound f g L η xStar x₀ N K
        hObjective hηpos hηmax hSchedule
    _ = ((Real.sqrt 3 + 1) / 3) ^ K *
        (f x₀ - f xStar +
          ((Real.sqrt 3 - 1) / (60 * η ^ 2)) * ‖x₀ - xStar‖ ^ 2) := by
      rw [hSchedule.1, initial_potential_identity f xStar x₀ η hηpos,
        convergence_rate]

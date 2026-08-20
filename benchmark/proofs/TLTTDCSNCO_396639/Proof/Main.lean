import Architect
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Order.LiminfLimsup
import Mathlib.Probability.Process.Filtration

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory

@[blueprint "def:clipped-vector"
  (statement := /-- For $\gamma \geq 0$ and $v\in\mathbb{R}^d$, the clipped vector is
  \[
    \operatorname{clip}_{\gamma}(v)
      = \min\left\{1,\frac{\gamma}{\lVert v\rVert}\right\}v.
  \]
  The convention at $v=0$ is immaterial, since the resulting vector is zero. -/)
  (title := /-- Clipping of a Euclidean vector -/)
  (latexEnv := "definition")]
noncomputable def clipped_vector {d : ℕ} (γ : ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  min 1 (γ / ‖v‖) • v

@[blueprint "def:clipped-step-size"
  (statement := /-- Let $p\in(1,2]$, and let the Lean index $t\geq0$ represent paper
  time $t+1$.  The step size attached to the Lean update at index $t$ is therefore
  \[
    \alpha_{t+1}=((t+1)+1)^{-p/(3p-2)}=(t+2)^{-p/(3p-2)}.
  \]
  Thus the zero-based definition below is exactly the source step size at the
  corresponding positive time. -/)
  (title := /-- Step size for clipped stochastic gradient descent -/)
  (latexEnv := "definition")]
noncomputable def clipped_step_size (p : ℝ) (t : ℕ) : ℝ :=
  Real.rpow (((t + 2 : ℕ) : ℝ)) (-p / (3 * p - 2))

@[blueprint "def:clipping-radius"
  (statement := /-- Let $G>0$ and $p\in(1,2]$, and let the Lean index $t\geq0$
  represent paper time $t+1$.  The clipping radius attached to the Lean update at
  index $t$ is the source radius $\gamma_{t+1}$, namely
  \[
    \gamma_{t+1}=
    \begin{cases}
      2G(t+2)^{(2-p)/(6p-4)},&1<p<2,\\
      2G\sqrt{\log(t+2)},&p=2.
    \end{cases}
  \]
  The definition uses the second branch exactly when $p=2$; under the standing range
  assumption these are precisely the two cases above.  Both branches consequently use
  the same zero-based translation of the source factor $(t+1)$. -/)
  (title := /-- Time-dependent clipping radius -/)
  (latexEnv := "definition")]
noncomputable def clipping_radius (G p : ℝ) (t : ℕ) : ℝ :=
  if p = 2 then
    2 * G * Real.sqrt (Real.log (((t + 2 : ℕ) : ℝ)))
  else
    2 * G * Real.rpow (((t + 2 : ℕ) : ℝ)) ((2 - p) / (6 * p - 4))

@[blueprint "def:nonconvex-cost-assumptions"
  (statement := /-- Let $f:\mathbb{R}^d\to\mathbb{R}$.  The cost assumptions with constants
  $G>0$ and $L\geq0$ mean that $f$ is bounded below and Fréchet differentiable, that
  $\lVert\nabla f(x)\rVert\leq G$ for every $x\in\mathbb{R}^d$, and that its gradient is
  $L$-Lipschitz. -/)
  (title := /-- Assumptions on the nonconvex objective -/)
  (latexEnv := "definition")]
def nonconvex_cost_assumptions {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (G : ℝ) (L : NNReal) : Prop :=
  0 < G ∧
    BddBelow (Set.range f) ∧
    Differentiable ℝ f ∧
    (∀ y, ‖gradient f y‖ ≤ G) ∧
    LipschitzWith L (gradient f)

@[blueprint "def:heavy-tail-noise-assumptions"
  (statement := /-- Fix a probability space $(\Omega,\mathcal A,\mu)$, a filtration
  $(\mathcal F_t)_{t\geq0}$, iterates $x_t$, and stochastic gradients $g_t$.  The
  heavy-tail noise assumptions of order $p$ and scale $\sigma$ require
  $1<p\leq2$, $\sigma\geq0$, integrability of $g_t$ and of
  $\lVert g_t-\nabla f(x_t)\rVert^p$, and, for every $t$, the almost-sure identities
  \[
    \mathbb E[g_t\mid\mathcal F_t]=\nabla f(x_t),\qquad
    \mathbb E[\lVert g_t-\nabla f(x_t)\rVert^p\mid\mathcal F_t]\leq\sigma^p.
  \] -/)
  (title := /-- Conditional heavy-tail assumptions on the stochastic gradient -/)
  (latexEnv := "definition")]
noncomputable def heavy_tail_noise_assumptions
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    {d : ℕ} (filtration : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x g : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (p σ : ℝ) : Prop :=
  1 < p ∧ p ≤ 2 ∧ 0 ≤ σ ∧
    (∀ t, MeasureTheory.Integrable (g t) μ) ∧
    (∀ t, MeasureTheory.Integrable
      (fun ω => Real.rpow ‖g t ω - gradient f (x t ω)‖ p) μ) ∧
    (∀ t, μ[g t | filtration t] =ᵐ[μ] fun ω => gradient f (x t ω)) ∧
    (∀ t, μ[(fun ω => Real.rpow ‖g t ω - gradient f (x t ω)‖ p) | filtration t]
      ≤ᵐ[μ] fun _ => Real.rpow σ p)

@[blueprint "def:clipped-sgd-run"
  (statement := /-- Fix the objects in \cref{def:heavy-tail-noise-assumptions}.  The sequence
  $(x_t)_{t\geq0}$ is the zero-based representation of a clipped-SGD run: Lean
  $x_t$, $g_t$, and $\mathcal F_t$ represent the paper objects at positive time
  $t+1$.  Thus $x_0$ represents the deterministic initialization $x_1$.  Every
  $x_t$ is $\mathcal F_t$-measurable, and for every $t\in\mathbb N$ and almost
  every $\omega$,
  \[
    x_{t+1}(\omega)=x_t(\omega)-\alpha_{t+1}
      \operatorname{clip}_{\gamma_{t+1}}(g_t(\omega)),
  \]
  where the subscripts on $\alpha$ and $\gamma$ are paper-time subscripts and their
  zero-based values are those of
  \cref{def:clipped-step-size,def:clipping-radius}. -/)
  (title := /-- A trajectory generated by clipped stochastic gradient descent -/)
  (latexEnv := "definition")]
noncomputable def clipped_sgd_run
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    {d : ℕ} (filtration : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (x g : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (G p : ℝ) : Prop :=
  (∃ x₀ : EuclideanSpace ℝ (Fin d), ∀ᵐ ω ∂μ, x 0 ω = x₀) ∧
    (∀ t, Measurable[filtration t, borel (EuclideanSpace ℝ (Fin d))] (x t)) ∧
    (∀ t, ∀ᵐ ω ∂μ,
      x (t + 1) ω = x t ω -
        clipped_step_size p t • clipped_vector (clipping_radius G p t) (g t ω))

@[blueprint "def:best-iterate-gradient-squared"
  (statement := /-- For $t\geq1$, define the best-iterate statistic
  \[
    F_t=\min_{0\leq k<t}\lVert\nabla f(x_k)\rVert^2.
  \]
  Here the Lean index $k=0$ represents the paper's first iterate $x_1$.  The arbitrary
  value $F_0=0$ has no effect on asymptotics along $t\to\infty$. -/)
  (title := /-- Best-iterate squared gradient norm -/)
  (latexEnv := "definition")]
noncomputable def best_iterate_gradient_squared
    {Ω : Type*} {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (t : ℕ) (ω : Ω) : ℝ :=
  if h : (Finset.range t).Nonempty then
    (Finset.range t).inf' h (fun k => ‖gradient f (x k ω)‖ ^ 2)
  else
    0

@[blueprint "def:ldp-upper-bound"
  (statement := /-- Let $F_t:\Omega\to\mathbb R$, let $n_t$ be a real-valued speed, and let
  $I:\mathbb R\to[-\infty,+\infty]$.  We say that $(F_t)$ satisfies the large-deviation
  upper bound with speed $(n_t)$ and rate $I$ if $n_t$ is eventually positive,
  $n_t\to+\infty$, and for every measurable $B\subseteq\mathbb R$,
  \[
    \limsup_{t\to\infty}\frac{1}{n_t}
      \log\mu\{\omega:F_t(\omega)\in B\}
      \leq-\inf_{y\in\overline B}I(y).
  \]
  The extended logarithm has value $-\infty$ at probability zero. -/)
  (title := /-- Large-deviation upper bound -/)
  (latexEnv := "definition")]
noncomputable def ldp_upper_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (F : ℕ → Ω → ℝ) (speed : ℕ → ℝ) (rate : ℝ → EReal) : Prop :=
  (∀ᶠ t in Filter.atTop, 0 < speed t) ∧
    Filter.Tendsto speed Filter.atTop Filter.atTop ∧
    ∀ B : Set ℝ, MeasurableSet B →
      Filter.limsup
          (fun t => ENNReal.log (μ ((F t) ⁻¹' B)) / (speed t : EReal))
          Filter.atTop
        ≤ -sInf (rate '' closure B)

@[blueprint "def:heavy-tail-ldp-speed"
  (statement := /-- For $1<p<2$, the claimed large-deviation speed is
  \[
    n_t=\frac{t^{4(p-1)/(3p-2)}}{\log t}.
  \] -/)
  (title := /-- LDP speed below the second-moment threshold -/)
  (latexEnv := "definition")]
noncomputable def heavy_tail_ldp_speed (p : ℝ) (t : ℕ) : ℝ :=
  Real.rpow (t : ℝ) (4 * (p - 1) / (3 * p - 2)) / Real.log (t : ℝ)

@[blueprint "def:critical-ldp-speed"
  (statement := /-- At $p=2$, the claimed large-deviation speed is
  \[
    n_t=\frac{t}{(\log t)^2}.
  \] -/)
  (title := /-- LDP speed at the second-moment threshold -/)
  (latexEnv := "definition")]
noncomputable def critical_ldp_speed (t : ℕ) : ℝ :=
  (t : ℝ) / (Real.log (t : ℝ)) ^ 2

@[blueprint "def:heavy-tail-rate-function"
  (statement := /-- For $1<p<2$, the asserted rate function is
  \[
    I_c(y)=
    \begin{cases}
      y^2/(768G^4),&y\geq0,\\
      +\infty,&y<0.
    \end{cases}
  \] -/)
  (title := /-- Rate function below the second-moment threshold -/)
  (latexEnv := "definition")]
noncomputable def heavy_tail_rate_function (G y : ℝ) : EReal :=
  if 0 ≤ y then (↑((y ^ 2 / (768 * G ^ 4) : ℝ)) : EReal) else ⊤

@[blueprint "def:critical-rate-function"
  (statement := /-- At $p=2$, the asserted rate function is
  \[
    I_c(y)=
    \begin{cases}
      y^2/(384G^4),&y\geq0,\\
      +\infty,&y<0.
    \end{cases}
  \] -/)
  (title := /-- Rate function at the second-moment threshold -/)
  (latexEnv := "definition")]
noncomputable def critical_rate_function (G y : ℝ) : EReal :=
  if 0 ≤ y then (↑((y ^ 2 / (384 * G ^ 4) : ℝ)) : EReal) else ⊤

@[blueprint "def:has-clipping-estimates"
  (statement := /-- Let $b_t$ and $u_t$ be random vectors.  They realize the clipping
  estimates if the clipped stochastic gradient decomposes almost surely as
  $\operatorname{clip}_{\gamma_t}(g_t)=\nabla f(x_t)+b_t+u_t$, if
  \[
    \lVert b_t\rVert\leq4\sigma^p\gamma_t^{1-p},
  \]
  and if every $\mathcal F_t$-measurable random vector $a$ satisfies
  \[
    \mathbb E[\exp\langle a,u_t\rangle\mid\mathcal F_t]
      \leq \exp(3\gamma_t^2\lVert a\rVert^2)
  \]
  almost surely. -/)
  (title := /-- Bias and exponential-moment estimates for clipping -/)
  (latexEnv := "definition")]
noncomputable def has_clipping_estimates
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    {d : ℕ} (filtration : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x g bias centered : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (G p σ : ℝ) : Prop :=
  (∀ t, ∀ᵐ ω ∂μ,
    clipped_vector (clipping_radius G p t) (g t ω) =
      gradient f (x t ω) + bias t ω + centered t ω) ∧
  (∀ t, ∀ᵐ ω ∂μ,
    ‖bias t ω‖ ≤ 4 * Real.rpow σ p *
      Real.rpow (clipping_radius G p t) (1 - p)) ∧
  (∀ t (a : Ω → EuclideanSpace ℝ (Fin d)),
    Measurable[filtration t, borel (EuclideanSpace ℝ (Fin d))] a →
    μ[(fun ω => Real.exp (inner ℝ (a ω) (centered t ω))) | filtration t]
      ≤ᵐ[μ] fun ω =>
        Real.exp (3 * (clipping_radius G p t) ^ 2 * ‖a ω‖ ^ 2))

@[blueprint "def:has-adapted-clipping-estimates"
  (statement := /-- The adapted clipping estimates strengthen
  \cref{def:has-clipping-estimates} by requiring the bias $b_t$ to be
  $\mathcal F_t$-measurable and the centered increment $u_t$ to be
  $\mathcal F_{t+1}$-measurable.  It also records the deterministic bound
  \[
    \lVert u_t\rVert\leq
      \gamma_t+G+4\sigma^p\gamma_t^{1-p},
  \]
  which follows from the clipping, gradient, and bias bounds.  Adaptedness and
  this bound make the finite-horizon conditional-MGF iteration well posed and
  ensure the required exponentials are integrable. -/)
  (title := /-- Adapted clipping estimates -/)
  (latexEnv := "definition")]
noncomputable def has_adapted_clipping_estimates
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    {d : ℕ} (filtration : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x g bias centered : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (G p σ : ℝ) : Prop :=
  has_clipping_estimates μ filtration f x g bias centered G p σ ∧
    (∀ t, Measurable[filtration t, borel (EuclideanSpace ℝ (Fin d))] (bias t)) ∧
    (∀ t, Measurable[filtration (t + 1), borel (EuclideanSpace ℝ (Fin d))]
      (centered t)) ∧
    (∀ t, ∀ᵐ ω ∂μ,
      ‖centered t ω‖ ≤
        clipping_radius G p t + G +
          4 * Real.rpow σ p * Real.rpow (clipping_radius G p t) (1 - p))

@[blueprint "lem:clipped-vector-norm-le-radius-local"
  (statement := /-- Let $d\in\mathbb N$, $v\in\mathbb R^d$, and $\gamma\geq0$.
  Then $\lVert\operatorname{clip}_{\gamma}(v)\rVert\leq\gamma$. -/)
  (proof := /-- Expand the definition in \cref{def:clipped-vector}.  If $v=0$, the
  assertion is immediate.  Otherwise, the scalar factor is nonnegative.  When
  $\gamma/\lVert v\rVert\leq1$, the clipped norm equals $\gamma$; in the complementary
  case it equals $\lVert v\rVert$, which is at most $\gamma$. -/)
  (title := /-- The norm of a clipped vector is at most its radius -/)
  (latexEnv := "lemma")]
lemma clipped_vector_norm_le_radius_local {d : ℕ} {γ : ℝ} (hγ : 0 ≤ γ)
    (v : EuclideanSpace ℝ (Fin d)) : ‖clipped_vector γ v‖ ≤ γ := by
  simp only [clipped_vector, norm_smul, Real.norm_eq_abs]
  by_cases hv : v = 0
  · simp [hv, hγ]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hdiv : 0 ≤ γ / ‖v‖ := div_nonneg hγ hvpos.le
  rw [abs_of_nonneg (le_min zero_le_one hdiv)]
  by_cases hle : γ / ‖v‖ ≤ 1
  · rw [min_eq_right hle, div_mul_cancel₀ _ (ne_of_gt hvpos)]
  · rw [min_eq_left (le_of_not_ge hle), one_mul]
    have hone : 1 ≤ γ / ‖v‖ := le_of_lt (lt_of_not_ge hle)
    simpa only [one_mul] using (le_div_iff₀ hvpos).mp hone

@[blueprint "lem:clipped-vector-norm-le-local"
  (statement := /-- Let $d\in\mathbb N$, $v\in\mathbb R^d$, and $\gamma\geq0$.
  Then clipping does not increase the norm:
  $\lVert\operatorname{clip}_{\gamma}(v)\rVert\leq\lVert v\rVert$. -/)
  (proof := /-- By \cref{def:clipped-vector}, the clipped vector is obtained by multiplying
  $v$ by the nonnegative scalar $\min\{1,\gamma/\lVert v\rVert\}$, which is at most one. -/)
  (title := /-- Clipping does not increase norm -/)
  (latexEnv := "lemma")]
lemma clipped_vector_norm_le_local {d : ℕ} {γ : ℝ} (hγ : 0 ≤ γ)
    (v : EuclideanSpace ℝ (Fin d)) : ‖clipped_vector γ v‖ ≤ ‖v‖ := by
  simp only [clipped_vector, norm_smul, Real.norm_eq_abs]
  have hdiv : 0 ≤ γ / ‖v‖ := div_nonneg hγ (norm_nonneg v)
  rw [abs_of_nonneg (le_min zero_le_one hdiv)]
  exact mul_le_of_le_one_left (norm_nonneg v) (min_le_left _ _)

@[blueprint "lem:clipping-radius-lower-local"
  (statement := /-- Let $G,p\in\mathbb R$ satisfy $G>0$ and $1<p\leq2$.  For every
  zero-based Lean index $t\in\mathbb N$, which represents paper time $t+1$, the
  clipping radius $\gamma_{t+1}=\operatorname{clipping\_radius}(G,p,t)$ defined in
  \cref{def:clipping-radius} satisfies $\gamma_{t+1}\geq4G/3$. -/)
  (proof := /-- Unfold \cref{def:clipping-radius} and distinguish whether $p=2$.  If
  $p=2$, then $t+2\geq2$, so monotonicity of the logarithm and the standard bound
  $1-2^{-1}\leq\log 2$ give
  $4/9\leq1/2\leq\log 2\leq\log(t+2)$.  The nonnegativity and square identity for
  the real square root therefore imply $2/3\leq\sqrt{\log(t+2)}$, and multiplication
  by $2G>0$ proves the desired inequality.  If $p\neq2$, then $1<p$ makes
  $6p-4>0$, while $p\leq2$ makes $2-p\geq0$; hence the exponent
  $(2-p)/(6p-4)$ is nonnegative.  Since $t+2\geq1$, its real power with this exponent
  is at least one.  Multiplication by $2G>0$ again yields the stated lower bound. -/)
  (title := /-- Uniform lower bound for the clipping radius -/)
  (latexEnv := "lemma")]
lemma clipping_radius_lower_local {G p : ℝ} (hG : 0 < G) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (t : ℕ) : 4 * G / 3 ≤ clipping_radius G p t := by
  unfold clipping_radius
  by_cases hp : p = 2
  · rw [if_pos hp]
    have ht : (2 : ℝ) ≤ ((t + 2 : ℕ) : ℝ) := by
      norm_num
    have hlogmono : Real.log 2 ≤ Real.log (((t + 2 : ℕ) : ℝ)) :=
      (Real.log_le_log_iff (by norm_num) (by positivity)).2 ht
    have hlog2 : (4 : ℝ) / 9 ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      linarith
    have hlog : (4 : ℝ) / 9 ≤ Real.log (((t + 2 : ℕ) : ℝ)) :=
      hlog2.trans hlogmono
    have hsqrt : (2 : ℝ) / 3 ≤ Real.sqrt (Real.log (((t + 2 : ℕ) : ℝ))) := by
      have hlog_nonneg : 0 ≤ Real.log (((t + 2 : ℕ) : ℝ)) := by linarith
      have hsquare := Real.sq_sqrt hlog_nonneg
      have hsqrt_nonneg := Real.sqrt_nonneg (Real.log (((t + 2 : ℕ) : ℝ)))
      nlinarith
    nlinarith
  · rw [if_neg hp]
    have hden : 0 < 6 * p - 4 := by nlinarith
    have hexponent : 0 ≤ (2 - p) / (6 * p - 4) :=
      div_nonneg (sub_nonneg.mpr hp2) hden.le
    have hbase : (1 : ℝ) ≤ ((t + 2 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ t + 2)
    have hrpow : (1 : ℝ) ≤
        Real.rpow (((t + 2 : ℕ) : ℝ)) ((2 - p) / (6 * p - 4)) :=
      Real.one_le_rpow hbase hexponent
    nlinarith

@[blueprint "lem:rpow-tail-bound-local"
  (statement := /-- Let $\gamma,z>0$ and $1<p\leq2$.  If $z\geq\gamma/4$, then
  $z\leq4z^p\gamma^{1-p}$. -/)
  (proof := /-- Put $q=p-1\in(0,1]$.  If $z/\gamma\leq1$, monotonicity of real
  powers in the exponent gives $(z/\gamma)^q\geq z/\gamma\geq1/4$; if
  $z/\gamma>1$, the same lower bound follows from $(z/\gamma)^q\geq1$.
  Multiplying by $4z$ and using
  $z^p\gamma^{1-p}=z(z/\gamma)^{p-1}$ proves the assertion. -/)
  (title := /-- A power-law tail comparison -/)
  (latexEnv := "lemma")]
lemma rpow_tail_bound_local {γ z p : ℝ} (hγ : 0 < γ) (hz : γ / 4 ≤ z)
    (hp1 : 1 < p) (hp2 : p ≤ 2) : z ≤ 4 * z ^ p * γ ^ (1 - p) := by
  have hzpos : 0 < z := lt_of_lt_of_le (by positivity) hz
  have hratio : (1 : ℝ) / 4 ≤ z / γ := (le_div_iff₀ hγ).2 (by nlinarith)
  have hqpos : 0 < p - 1 := by linarith
  have hpow : (1 : ℝ) / 4 ≤ (z / γ) ^ (p - 1) := by
    by_cases hle : z / γ ≤ 1
    · have hmono := Real.rpow_le_rpow_of_exponent_ge
        (by positivity : 0 < z / γ) hle (by linarith : p - 1 ≤ 1)
      rw [Real.rpow_one] at hmono
      exact hratio.trans hmono
    · have hone : 1 ≤ z / γ := le_of_lt (lt_of_not_ge hle)
      exact (by norm_num : (1 : ℝ) / 4 ≤ 1).trans
        (Real.one_le_rpow hone hqpos.le)
  have hmul : z ≤ 4 * z * (z / γ) ^ (p - 1) := by
    nlinarith
  calc
    z ≤ 4 * z * (z / γ) ^ (p - 1) := hmul
    _ = 4 * z ^ p * γ ^ (1 - p) := by
      have hzpow : z ^ p = z * z ^ (p - 1) := by
        calc
          z ^ p = z ^ (1 + (p - 1)) := by congr 1 <;> ring
          _ = z ^ 1 * z ^ (p - 1) := Real.rpow_add hzpos _ _
          _ = z * z ^ (p - 1) := by rw [Real.rpow_one]
      have hγpow : γ ^ (1 - p) = (γ ^ (p - 1))⁻¹ := by
        calc
          γ ^ (1 - p) = γ ^ (-(p - 1)) := by congr 1 <;> ring
          _ = (γ ^ (p - 1))⁻¹ := Real.rpow_neg hγ.le _
      rw [Real.div_rpow hzpos.le hγ.le]
      rw [hzpow, hγpow]
      simp only [div_eq_mul_inv]
      ring

@[blueprint "lem:clipping-error-bound-local"
  (statement := /-- Let $v,m\in\mathbb R^d$, let $G,\gamma>0$, and suppose
  $\lVert m\rVert\leq G$, $\gamma\geq4G/3$, and $1<p\leq2$.  Then
  \[
    \lVert\operatorname{clip}_{\gamma}(v)-v\rVert
      \leq4\lVert v-m\rVert^p\gamma^{1-p}.
  \] -/)
  (proof := /-- If $\lVert v\rVert\leq\gamma$, clipping fixes $v$.  Otherwise its
  displacement has norm $\lVert v\rVert-\gamma$.  The triangle inequality and
  $\lVert m\rVert\leq G\leq\gamma$ bound this displacement by $\lVert v-m\rVert$.
  They also imply $\lVert v-m\rVert\geq\gamma-G\geq\gamma/4$; applying
  \cref{lem:rpow-tail-bound-local} gives the stated power-law bound. -/)
  (title := /-- Pointwise clipping-error estimate -/)
  (latexEnv := "lemma")]
lemma clipping_error_bound_local {d : ℕ} {G γ p : ℝ} (hG : 0 < G) (hγ : 0 < γ)
    (hγG : 4 * G / 3 ≤ γ) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (v m : EuclideanSpace ℝ (Fin d)) (hm : ‖m‖ ≤ G) :
    ‖clipped_vector γ v - v‖ ≤ 4 * ‖v - m‖ ^ p * γ ^ (1 - p) := by
  by_cases hv : v = 0
  · subst v
    simp [clipped_vector]
    positivity
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  by_cases hvγ : ‖v‖ ≤ γ
  · have hone : 1 ≤ γ / ‖v‖ := (le_div_iff₀ hvpos).2 (by simpa using hvγ)
    simp [clipped_vector, min_eq_left hone]
    positivity
  · have hratio : γ / ‖v‖ < 1 := (div_lt_one hvpos).2 (lt_of_not_ge hvγ)
    have hratio0 : 0 ≤ γ / ‖v‖ := div_nonneg hγ.le hvpos.le
    have herr : ‖clipped_vector γ v - v‖ = ‖v‖ - γ := by
      rw [clipped_vector, min_eq_right hratio.le]
      have hvsmul : (γ / ‖v‖) • v - v = (γ / ‖v‖ - 1) • v := by module
      rw [hvsmul, norm_smul, Real.norm_eq_abs,
        abs_of_nonpos (by linarith : γ / ‖v‖ - 1 ≤ 0)]
      field_simp
      ring
    have htriangle : ‖v‖ ≤ ‖v - m‖ + ‖m‖ := by
      calc
        ‖v‖ = ‖(v - m) + m‖ := by congr 1 <;> abel
        _ ≤ ‖v - m‖ + ‖m‖ := norm_add_le _ _
    have hGγ : G ≤ γ := by nlinarith
    have herr_le : ‖v‖ - γ ≤ ‖v - m‖ := by linarith
    have htail : γ / 4 ≤ ‖v - m‖ := by nlinarith
    rw [herr]
    exact herr_le.trans (rpow_tail_bound_local hγ htail hp1 hp2)

@[blueprint "lem:exp-centered-quadratic-local"
  (statement := /-- If $r\geq0$ and $|y|\leq2r$, then
  $e^y\leq y+e^{3r^2}$. -/)
  (proof := /-- For $|y|\leq1$, the third-order Taylor bound for the exponential,
  followed by $|y|\leq2r$, gives $e^y-y\leq1+3r^2\leq e^{3r^2}$.
  For $|y|>1$ and $r\geq2/3$, monotonicity and $2r\leq3r^2$ suffice.  In the
  remaining compact range $1/2<r<2/3$, apply the fourth-order Taylor upper bound
  to $e^r$ and the fifth-power lower bound
  $(1+3r^2/5)^5\leq e^{3r^2}$; the resulting rational polynomial inequalities
  are nonnegative on this interval. -/)
  (title := /-- Quadratic exponential bound for a centered bounded variable -/)
  (latexEnv := "lemma")]
lemma exp_centered_quadratic_local {r y : ℝ} (hr : 0 ≤ r) (hy : |y| ≤ 2 * r) :
    Real.exp y ≤ y + Real.exp (3 * r ^ 2) := by
  by_cases hy1 : |y| ≤ 1
  · have hb := Real.exp_bound hy1 (n := 3) (by norm_num)
    norm_num [Finset.sum_range_succ] at hb
    have habs : |y| ^ 3 ≤ y ^ 2 := by
      calc
        |y| ^ 3 = |y| ^ 2 * |y| := by ring
        _ ≤ |y| ^ 2 * 1 := mul_le_mul_of_nonneg_left hy1 (sq_nonneg |y|)
        _ = y ^ 2 := by rw [mul_one, sq_abs]
    have hysq : y ^ 2 ≤ 4 * r ^ 2 := by
      have hs := (sq_le_sq₀ (abs_nonneg y) (by positivity : 0 ≤ 2 * r)).2 hy
      rw [sq_abs] at hs
      nlinarith [hs]
    have hexp := Real.add_one_le_exp (3 * r ^ 2)
    nlinarith [abs_sub_le_iff.mp hb |>.1, abs_sub_le_iff.mp hb |>.2]
  · have hygt : 1 < |y| := lt_of_not_ge hy1
    have hrhalf : (1 : ℝ) / 2 < r := by nlinarith
    by_cases hrlarge : (2 : ℝ) / 3 ≤ r
    · have hyr : y ≤ 2 * r := (le_abs_self y).trans hy
      by_cases hy0 : y ≤ 0
      · have hey : Real.exp y ≤ 1 := (Real.exp_le_one_iff.mpr hy0)
        have hlin := Real.add_one_le_exp (3 * r ^ 2)
        have hylow : -(2 * r) ≤ y := neg_le_of_abs_le hy
        nlinarith
      · have harg : y ≤ 3 * r ^ 2 := by nlinarith
        exact (Real.exp_le_exp.mpr harg).trans (le_add_of_nonneg_left (le_of_not_ge hy0))
    · have hrupper : r < (2 : ℝ) / 3 := lt_of_not_ge hrlarge
      let u : ℝ := 6 * r - 3
      have hu0 : 0 ≤ u := by dsimp [u]; nlinarith
      have hu1 : u ≤ 1 := by dsimp [u]; nlinarith
      have hlow : (1 + 3 * r ^ 2 / 5) ^ 5 ≤ Real.exp (3 * r ^ 2) := by
        have hbase := Real.add_one_le_exp (3 * r ^ 2 / 5)
        have hnonneg : 0 ≤ 1 + 3 * r ^ 2 / 5 := by positivity
        have hbase' : 1 + 3 * r ^ 2 / 5 ≤ Real.exp (3 * r ^ 2 / 5) := by
          simpa [add_comm] using hbase
        have hpow := pow_le_pow_left₀ hnonneg hbase' 5
        rw [← Real.exp_nat_mul] at hpow
        norm_num at hpow ⊢
        have heq : 5 * (3 * r ^ 2 / 5) = 3 * r ^ 2 := by ring
        rw [heq] at hpow
        exact hpow
      have hpolyneg : 1 + 2 * r ≤ (1 + 3 * r ^ 2 / 5) ^ 5 := by
        have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
        have hu3 : 0 ≤ u ^ 3 := by positivity
        have hu4 : 0 ≤ u ^ 4 := by positivity
        have hu5 : 0 ≤ u ^ 5 := by positivity
        have hu6 : 0 ≤ u ^ 6 := by positivity
        have hu7 : 0 ≤ u ^ 7 := by positivity
        have hu8 : 0 ≤ u ^ 8 := by positivity
        have hu9 : 0 ≤ u ^ 9 := by positivity
        have hu10 : 0 ≤ u ^ 10 := by positivity
        dsimp [u] at hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7 hu8 hu9 hu10 ⊢
        nlinarith
      have hP : Real.exp r ≤
          1 + r + r ^ 2 / 2 + r ^ 3 / 6 + 5 * r ^ 4 / 96 := by
        have hb := Real.exp_bound' hr (by linarith : r ≤ 1) (n := 4) (by norm_num)
        norm_num [Finset.sum_range_succ] at hb ⊢
        nlinarith
      have hP0 : 0 ≤ 1 + r + r ^ 2 / 2 + r ^ 3 / 6 + 5 * r ^ 4 / 96 :=
        le_trans (Real.exp_pos r).le hP
      have hP2 : Real.exp (2 * r) ≤
          (1 + r + r ^ 2 / 2 + r ^ 3 / 6 + 5 * r ^ 4 / 96) ^ 2 := by
        have hs := pow_le_pow_left₀ (Real.exp_pos r).le hP 2
        rw [← Real.exp_nat_mul] at hs
        norm_num at hs ⊢
        simpa [mul_comm] using hs
      have hpolypos :
          (1 + r + r ^ 2 / 2 + r ^ 3 / 6 + 5 * r ^ 4 / 96) ^ 2 - 1 ≤
            (1 + 3 * r ^ 2 / 5) ^ 5 := by
        have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
        have hu3 : 0 ≤ u ^ 3 := by positivity
        have hu4 : 0 ≤ u ^ 4 := by positivity
        have hu5 : 0 ≤ u ^ 5 := by positivity
        have hu6 : 0 ≤ u ^ 6 := by positivity
        have hu7 : 0 ≤ u ^ 7 := by positivity
        have hu8 : 0 ≤ u ^ 8 := by positivity
        have hu9 : 0 ≤ u ^ 9 := by positivity
        have hu10 : 0 ≤ u ^ 10 := by positivity
        have hconst : (18285377 : ℝ) / 552960000 ≤ 2151856147 / 7372800000 := by
          norm_num
        dsimp [u] at hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7 hu8 hu9 hu10 ⊢
        nlinarith
      by_cases hy0 : y ≤ 0
      · have hey : Real.exp y ≤ 1 := Real.exp_le_one_iff.mpr hy0
        have hylow : -(2 * r) ≤ y := neg_le_of_abs_le hy
        nlinarith
      · have hyone : 1 < y := by rw [abs_of_pos (lt_of_not_ge hy0)] at hygt; exact hygt
        have hyr : y ≤ 2 * r := (le_abs_self y).trans hy
        have hey : Real.exp y ≤ Real.exp (2 * r) := Real.exp_le_exp.mpr hyr
        nlinarith

@[blueprint "lem:conditional-simple-bilinear-local"
  (statement := /-- Let $B:F\times E\to H$ be a continuous bilinear map, let
  $s:\Omega\to F$ be a simple function measurable with respect to a sub-$\sigma$-algebra
  $\mathcal G$, and let $g:\Omega\to E$ be integrable.  Then
  \[
    \mathbb E[B(s,g)\mid\mathcal G]=B(s,\mathbb E[g\mid\mathcal G])
  \]
  almost surely. -/)
  (proof := /-- Induct over the measurable simple function.  For an indicator of a
  measurable set, use conditional expectation of indicators and commutation with the
  continuous linear map $B(c,\cdot)$.  The additive step follows from conditional
  linearity; boundedness of simple functions supplies integrability. -/)
  (title := /-- Pulling a simple bilinear factor through conditional expectation -/)
  (latexEnv := "lemma")]
lemma conditional_simple_bilinear_local
    {Ω F E H : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (B : F →L[ℝ] E →L[ℝ] H) (f : @SimpleFunc Ω m F) {g : Ω → E}
    (hg : Integrable g μ) :
    μ[(fun ω => B (f ω) (g ω)) | m] =ᵐ[μ]
      fun ω => B (f ω) (μ[g | m] ω) := by
  have hind : ∀ (s : Set Ω) (c : F) (u : Ω → E),
      (fun ω => B (s.indicator (Function.const Ω c) ω) (u ω)) =
        s.indicator (fun ω => B c (u ω)) := by
    intro s c u
    ext ω
    by_cases hω : ω ∈ s <;> simp [hω]
  apply @SimpleFunc.induction _ _ m _ (fun f => _)
    (fun c s hs => ?_) (fun f₁ f₂ _ h₁ h₂ => ?_) f
  · simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
      SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
    rw [hind, hind]
    refine (condExp_indicator ((B c).integrable_comp hg) hs).trans ?_
    filter_upwards [(B c).comp_condExp_comm hg (m := m)] with ω hω
    simp only [Function.comp_apply] at hω
    simp only [Set.indicator, hω, Function.comp_def]
  · have hadd := @SimpleFunc.coe_add _ _ m _ f₁ f₂
    calc
      μ[fun ω => B (f₁ ω + f₂ ω) (g ω) | m] =ᵐ[μ]
          μ[fun ω => B (f₁ ω) (g ω) | m] + μ[fun ω => B (f₂ ω) (g ω) | m] := by
        simp_rw [B.map_add]
        obtain ⟨C₁, hC₁⟩ := @SimpleFunc.exists_forall_norm_le _ _ m _ f₁
        obtain ⟨C₂, hC₂⟩ := @SimpleFunc.exists_forall_norm_le _ _ m _ f₂
        have hi₁ : Integrable (fun ω => B (f₁ ω) (g ω)) μ :=
          (hg.norm.const_mul (‖B‖ * C₁)).mono'
            (Continuous.comp_aestronglyMeasurable
              (g := fun z : F × E => B z.1 z.2) (by fun_prop)
              ((f₁.stronglyMeasurable.mono hm).aestronglyMeasurable.prodMk
                hg.aestronglyMeasurable))
            (Filter.Eventually.of_forall fun ω => by grw [B.le_opNorm₂, hC₁])
        have hi₂ : Integrable (fun ω => B (f₂ ω) (g ω)) μ :=
          (hg.norm.const_mul (‖B‖ * C₂)).mono'
            (Continuous.comp_aestronglyMeasurable
              (g := fun z : F × E => B z.1 z.2) (by fun_prop)
              ((f₂.stronglyMeasurable.mono hm).aestronglyMeasurable.prodMk
                hg.aestronglyMeasurable))
            (Filter.Eventually.of_forall fun ω => by grw [B.le_opNorm₂, hC₂])
        exact condExp_add hi₁ hi₂ m
      _ =ᵐ[μ] fun ω => B (f₁ ω) (μ[g | m] ω) + B (f₂ ω) (μ[g | m] ω) := h₁.add h₂
      _ =ᵐ[μ] fun ω => B ((f₁ + f₂) ω) (μ[g | m] ω) := by simp

@[blueprint "lem:conditional-bilinear-bounded-local"
  (statement := /-- Let $B:F\times E\to H$ be continuous bilinear, let
  $f:\Omega\to F$ be bounded and strongly measurable with respect to
  $\mathcal G$, and let $g:\Omega\to E$ be integrable on a finite measure space.
  Then $\mathbb E[B(f,g)\mid\mathcal G]=B(f,\mathbb E[g\mid\mathcal G])$ almost
  surely. -/)
  (proof := /-- Approximate $f$ by its uniformly bounded measurable simple-function
  approximants.  Apply \cref{lem:conditional-simple-bilinear-local} to every
  approximant.  Bilinear norm bounds provide integrable dominating functions on both
  sides, so dominated convergence and uniqueness of conditional-expectation limits
  pass the identity to $f$. -/)
  (title := /-- Pulling a bounded bilinear factor through conditional expectation -/)
  (latexEnv := "lemma")]
lemma conditional_bilinear_bounded_local
    {Ω F E H : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) [IsFiniteMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (B : F →L[ℝ] E →L[ℝ] H) {f : Ω → F} {g : Ω → E}
    (hf : StronglyMeasurable[m] f) (hg : Integrable g μ) (c : ℝ)
    (hf_bound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ c) :
    μ[(fun ω => B (f ω) (g ω)) | m] =ᵐ[μ]
      fun ω => B (f ω) (μ[g | m] ω) := by
  let fs := hf.approxBounded c
  have hfs_tendsto : ∀ᵐ ω ∂μ, Filter.Tendsto (fs · ω) Filter.atTop (nhds (f ω)) :=
    hf.tendsto_approxBounded_ae hf_bound
  by_cases hμ : μ = 0
  · simp only [hμ, ae_zero]
    norm_cast
  have : (ae μ).NeBot := ae_neBot.2 hμ
  have hc : 0 ≤ c := by
    rcases hf_bound.exists with ⟨ω, hω⟩
    exact (norm_nonneg (f ω)).trans hω
  have hfs_bound : ∀ n ω, ‖fs n ω‖ ≤ c := hf.norm_approxBounded_le hc
  have hbilin_int {u : Ω → F} {v : Ω → E} (hu : AEStronglyMeasurable[mΩ] u μ)
      (hv : Integrable v μ) (hub : ∀ᵐ ω ∂μ, ‖u ω‖ ≤ c) :
      Integrable (fun ω => B (u ω) (v ω)) μ :=
    (hv.norm.const_mul (‖B‖ * c)).mono'
      (Continuous.comp_aestronglyMeasurable
        (g := fun z : F × E => B z.1 z.2) (by fun_prop)
        (hu.prodMk hv.aestronglyMeasurable))
      (hub.mono fun ω hω => by grw [B.le_opNorm₂, hω])
  have hfixed : μ[fun ω => B (f ω) (μ[g | m] ω) | m] =
      fun ω => B (f ω) (μ[g | m] ω) := by
    refine condExp_of_stronglyMeasurable hm ?_ ?_
    · exact Continuous.comp_stronglyMeasurable
        (g := fun z : F × E => B z.1 z.2) (by fun_prop)
        (hf.prodMk stronglyMeasurable_condExp)
    · exact hbilin_int (hf.mono hm).aestronglyMeasurable integrable_condExp hf_bound
  rw [← hfixed]
  refine tendsto_condExp_unique (fun n ω => B (fs n ω) (g ω))
    (fun n ω => B (fs n ω) (μ[g | m] ω)) (fun ω => B (f ω) (g ω))
    (fun ω => B (f ω) (μ[g | m] ω)) ?_ ?_ ?_ ?_
    (‖B‖ * c * ‖g ·‖) ?_ (‖B‖ * c * ‖(μ[g | m]) ·‖) ?_ ?_ ?_ ?_
  · exact fun n => hbilin_int
      ((fs n).stronglyMeasurable.mono hm).aestronglyMeasurable hg
      (Filter.Eventually.of_forall (hfs_bound n))
  · exact fun n => hbilin_int
      ((fs n).stronglyMeasurable.mono hm).aestronglyMeasurable integrable_condExp
      (Filter.Eventually.of_forall (hfs_bound n))
  · filter_upwards [hfs_tendsto] with ω hω
    exact ((by fun_prop : Continuous (fun x => B x (g ω))).tendsto (f ω)).comp hω
  · filter_upwards [hfs_tendsto] with ω hω
    exact ((by fun_prop : Continuous (fun x => B x (μ[g | m] ω))).tendsto (f ω)).comp hω
  · exact hg.norm.const_mul _
  · fun_prop
  · refine fun n => Filter.Eventually.of_forall fun ω => ?_
    grw [B.le_opNorm₂, hfs_bound]
  · refine fun n => Filter.Eventually.of_forall fun ω => ?_
    grw [B.le_opNorm₂, hfs_bound]
  · intro n
    exact (conditional_simple_bilinear_local (mΩ := mΩ) μ m hm B (fs n) hg).trans (by
      nth_rw 2 [condExp_of_stronglyMeasurable hm]
      · exact Continuous.comp_stronglyMeasurable
          (g := fun z : F × E => B z.1 z.2) (by fun_prop)
          ((fs n).stronglyMeasurable.prodMk stronglyMeasurable_condExp)
      · exact hbilin_int
          ((fs n).stronglyMeasurable.mono hm).aestronglyMeasurable integrable_condExp
          (Filter.Eventually.of_forall (hfs_bound n)))

@[blueprint "lem:conditional-mgf-bounded-local"
  (statement := /-- Let $Y:\Omega\to\mathbb R^d$ be integrable and satisfy
  $\lVert Y\rVert\leq\gamma$ almost surely, where $\gamma\geq0$.  If
  $a:\Omega\to\mathbb R^d$ is $\mathcal G$-measurable and
  $\lVert a\rVert\leq C$ almost surely, then
  \[
    \mathbb E\!\left[\exp\langle a,Y-\mathbb E[Y\mid\mathcal G]\rangle
      \mid\mathcal G\right]
    \leq \exp(3\gamma^2\lVert a\rVert^2)
  \]
  almost surely. -/)
  (proof := /-- Conditional Jensen bounds the norm of
  $\mathbb E[Y\mid\mathcal G]$ by $\gamma$, so the centered residual has norm at
  most $2\gamma$.  By \cref{lem:conditional-bilinear-bounded-local}, the bounded
  $\mathcal G$-measurable vector $a$ may be pulled through conditional expectation;
  hence its inner product with the residual has conditional mean zero.  Apply
  \cref{lem:exp-centered-quadratic-local} pointwise.  The bounds on $a$ and the
  residual make both the exponential and its quadratic majorant integrable, so
  conditional monotonicity and additivity cancel the centered linear term and give
  the asserted estimate. -/)
  (title := /-- Conditional MGF bound for bounded predictable vectors -/)
  (latexEnv := "lemma")]
lemma conditional_mgf_bounded_local
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    {d : ℕ} (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Y : Ω → EuclideanSpace ℝ (Fin d)) (γ : ℝ) (hγ : 0 ≤ γ)
    (hYint : Integrable Y μ) (hYnorm : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ γ)
    (a : Ω → EuclideanSpace ℝ (Fin d)) (ha : StronglyMeasurable[m] a)
    (C : ℝ) (hC : 0 ≤ C) (haC : ∀ᵐ ω ∂μ, ‖a ω‖ ≤ C) :
    μ[(fun ω => Real.exp (inner ℝ (a ω) (Y ω - μ[Y | m] ω))) | m]
      ≤ᵐ[μ] fun ω => Real.exp (3 * γ ^ 2 * ‖a ω‖ ^ 2) := by
  let q : Ω → EuclideanSpace ℝ (Fin d) := μ[Y | m]
  let Z : Ω → EuclideanSpace ℝ (Fin d) := fun ω => Y ω - q ω
  let X : Ω → ℝ := fun ω => inner ℝ (a ω) (Z ω)
  let R : Ω → ℝ := fun ω => Real.exp (3 * γ ^ 2 * ‖a ω‖ ^ 2)
  have hqnorm₁ := norm_condExp_le (μ := μ) (m := m) Y
  have hqnorm₂ := condExp_le_nonneg_const (μ := μ) (m := m) hγ hYnorm
  have hZnorm : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ 2 * γ := by
    filter_upwards [hqnorm₁, hqnorm₂, hYnorm] with ω hq₁ hq₂ hY
    dsimp [Z, q]
    exact (norm_sub_le _ _).trans (by linarith)
  have hqint : Integrable q μ := by
    dsimp [q]
    exact integrable_condExp
  have hZint : Integrable Z μ := by
    dsimp [Z]
    exact hYint.sub hqint
  have hYae : AEStronglyMeasurable[mΩ] Y μ :=
    hYint.aestronglyMeasurable
  have hqae : AEStronglyMeasurable[mΩ] q μ := by
    dsimp [q]
    exact (stronglyMeasurable_condExp (μ := μ) (m := m) (f := Y)).mono hm |>.aestronglyMeasurable
  have hZae : AEStronglyMeasurable[mΩ] Z μ := by
    dsimp [Z]
    exact hYae.sub hqae
  have haae : AEStronglyMeasurable[mΩ] a μ :=
    (ha.mono hm).aestronglyMeasurable
  have hXae : AEStronglyMeasurable[mΩ] X μ := by
    dsimp [X]
    exact haae.inner hZae
  have hXbound : ∀ᵐ ω ∂μ, |X ω| ≤ 2 * γ * C := by
    filter_upwards [hZnorm, haC] with ω hZ haω
    dsimp [X]
    rw [← Real.norm_eq_abs]
    have hmul := mul_le_mul haω hZ (norm_nonneg (Z ω)) hC
    nlinarith [norm_inner_le_norm (𝕜 := ℝ) (a ω) (Z ω)]
  have hXint : Integrable X μ :=
    (integrable_const (2 * γ * C)).mono' hXae (hXbound.mono fun ω hω => by
      simpa [Real.norm_eq_abs] using hω)
  have hqidem := condExp_of_stronglyMeasurable (μ := μ) hm
    (stronglyMeasurable_condExp (μ := μ) (m := m) (f := Y)) hqint
  have hqidem_ae : μ[q | m] =ᵐ[μ] q := by
    dsimp [q]
    exact Filter.Eventually.of_forall (fun ω => congrFun hqidem ω)
  have hZcond₁ := condExp_sub hYint hqint m
  have hZcond : μ[Z | m] =ᵐ[μ] (0 : Ω → EuclideanSpace ℝ (Fin d)) := by
    change μ[Y - q | m] =ᵐ[μ] (0 : Ω → EuclideanSpace ℝ (Fin d))
    filter_upwards [hZcond₁, hqidem_ae] with ω hsub hid
    rw [hsub]
    change μ[Y | m] ω - μ[q | m] ω = 0
    rw [hid]
    simp [q]
  have hpull := conditional_bilinear_bounded_local (mΩ := mΩ) μ m hm
    (innerSL ℝ) ha hZint C haC
  have hXcond : μ[X | m] =ᵐ[μ] (0 : Ω → ℝ) := by
    change μ[fun ω => (innerSL ℝ) (a ω) (Z ω) | m] =ᵐ[μ] (0 : Ω → ℝ)
    filter_upwards [hpull, hZcond] with ω hp hz
    rw [hp, hz]
    simp
  have hpoint : ∀ᵐ ω ∂μ, Real.exp (X ω) ≤ X ω + R ω := by
    filter_upwards [hZnorm] with ω hZ
    dsimp [X, R]
    have h := exp_centered_quadratic_local
      (r := γ * ‖a ω‖) (y := inner ℝ (a ω) (Z ω))
      (mul_nonneg hγ (norm_nonneg _)) (by
        rw [← Real.norm_eq_abs]
        calc
          ‖inner ℝ (a ω) (Z ω)‖ ≤ ‖a ω‖ * ‖Z ω‖ :=
            norm_inner_le_norm (𝕜 := ℝ) (a ω) (Z ω)
          _ ≤ ‖a ω‖ * (2 * γ) :=
            mul_le_mul_of_nonneg_left hZ (norm_nonneg (a ω))
          _ = 2 * (γ * ‖a ω‖) := by ring)
    convert h using 1 <;> ring_nf
  have hexp_ae : AEStronglyMeasurable[mΩ] (fun ω => Real.exp (X ω)) μ :=
    Real.continuous_exp.comp_aestronglyMeasurable hXae
  have hexp_bound : ∀ᵐ ω ∂μ, ‖Real.exp (X ω)‖ ≤ Real.exp (2 * γ * C) := by
    filter_upwards [hXbound] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans hω)
  have hexp_int : Integrable (fun ω => Real.exp (X ω)) μ :=
    (integrable_const (Real.exp (2 * γ * C))).mono' hexp_ae hexp_bound
  have hRstrong : StronglyMeasurable[m] R := by
    dsimp [R]
    exact Real.continuous_exp.comp_stronglyMeasurable (by fun_prop)
  have hRbound : ∀ᵐ ω ∂μ, ‖R ω‖ ≤ Real.exp (3 * γ ^ 2 * C ^ 2) := by
    filter_upwards [haC] with ω haω
    dsimp [R]
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hs := (sq_le_sq₀ (norm_nonneg (a ω)) hC).2 haω
    nlinarith [sq_nonneg γ]
  have hRint : Integrable R μ :=
    (integrable_const (Real.exp (3 * γ ^ 2 * C ^ 2))).mono'
      (hRstrong.mono hm).aestronglyMeasurable hRbound
  have hmono := condExp_mono (μ := μ) (m := m) hexp_int (hXint.add hRint) hpoint
  have hadd := condExp_add (μ := μ) hXint hRint m
  have hRid := condExp_of_stronglyMeasurable (μ := μ) hm hRstrong hRint
  have hRid_ae : μ[R | m] =ᵐ[μ] R :=
    Filter.Eventually.of_forall (fun ω => congrFun hRid ω)
  filter_upwards [hmono, hadd, hXcond, hRid_ae] with ω hmonoω haddω hXω hRω
  dsimp [R] at hRω ⊢
  calc
    μ[fun ω => Real.exp (X ω) | m] ω ≤ μ[X + R | m] ω := hmonoω
    _ = μ[X | m] ω + μ[R | m] ω := haddω
    _ = Real.exp (3 * γ ^ 2 * ‖a ω‖ ^ 2) := by rw [hXω, hRω]; simp

@[blueprint "lem:conditional-mgf-local"
  (statement := /-- Let $Y:\Omega\to\mathbb R^d$ be integrable and satisfy
  $\lVert Y\rVert\leq\gamma$ almost surely, where $\gamma\geq0$.  For every
  $\mathcal G$-measurable $a:\Omega\to\mathbb R^d$,
  \[
    \mathbb E\!\left[\exp\langle a,Y-\mathbb E[Y\mid\mathcal G]\rangle
      \mid\mathcal G\right]
    \leq \exp(3\gamma^2\lVert a\rVert^2)
  \]
  almost surely. -/)
  (proof := /-- Truncate $a$ on the measurable sets
  $S_n=\{\lVert a\rVert\leq n\}$ and apply
  \cref{lem:conditional-mgf-bounded-local} to each truncation.  If the original
  exponential is not integrable, its conditional expectation is zero.  Otherwise,
  the conditional-expectation indicator identity shows on $S_n$ that the truncated
  and original conditional expectations agree.  The countable union of the sets
  $S_n$ is all of $\Omega$, so the truncated estimates yield the result. -/)
  (title := /-- Conditional MGF bound for predictable vectors -/)
  (latexEnv := "lemma")]
lemma conditional_mgf_local
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    {d : ℕ} (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Y : Ω → EuclideanSpace ℝ (Fin d)) (γ : ℝ) (hγ : 0 ≤ γ)
    (hYint : Integrable Y μ) (hYnorm : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ γ)
    (a : Ω → EuclideanSpace ℝ (Fin d)) (ha : StronglyMeasurable[m] a) :
    μ[(fun ω => Real.exp (inner ℝ (a ω) (Y ω - μ[Y | m] ω))) | m]
      ≤ᵐ[μ] fun ω => Real.exp (3 * γ ^ 2 * ‖a ω‖ ^ 2) := by
  let q : Ω → EuclideanSpace ℝ (Fin d) := μ[Y | m]
  let Z : Ω → EuclideanSpace ℝ (Fin d) := fun ω => Y ω - q ω
  let V : Ω → ℝ := fun ω => Real.exp (inner ℝ (a ω) (Z ω))
  let S : ℕ → Set Ω := fun n => {ω | ‖a ω‖ ≤ n}
  let aN : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun n => (S n).indicator a
  let VN : ℕ → Ω → ℝ := fun n ω => Real.exp (inner ℝ (aN n ω) (Z ω))
  have hqnorm₁ := norm_condExp_le (μ := μ) (m := m) Y
  have hqnorm₂ := condExp_le_nonneg_const (μ := μ) (m := m) hγ hYnorm
  have hZnorm : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ 2 * γ := by
    filter_upwards [hqnorm₁, hqnorm₂, hYnorm] with ω hq₁ hq₂ hY
    dsimp [Z, q]
    exact (norm_sub_le _ _).trans (by linarith)
  have hqint : Integrable q μ := by
    dsimp [q]
    exact integrable_condExp
  have hZint : Integrable Z μ := by
    dsimp [Z]
    exact hYint.sub hqint
  have hS (n : ℕ) : MeasurableSet[m] (S n) := by
    dsimp [S]
    exact measurableSet_le ha.norm.measurable measurable_const
  have haN (n : ℕ) : StronglyMeasurable[m] (aN n) := by
    dsimp [aN]
    exact ha.indicator (hS n)
  have haN_bound (n : ℕ) : ∀ᵐ ω ∂μ, ‖aN n ω‖ ≤ (n : ℝ) :=
    Filter.Eventually.of_forall (fun ω => by
      by_cases hω : ω ∈ S n
      · simpa [aN, Set.indicator_of_mem hω, S] using hω
      · simp [aN, Set.indicator_of_notMem hω])
  have hmgf (n : ℕ) : μ[VN n | m] ≤ᵐ[μ]
      fun ω => Real.exp (3 * γ ^ 2 * ‖aN n ω‖ ^ 2) := by
    dsimp [VN]
    exact conditional_mgf_bounded_local (mΩ := mΩ) μ m hm Y γ hγ hYint hYnorm
      (aN n) (haN n) n (Nat.cast_nonneg n) (haN_bound n)
  have hZae : AEStronglyMeasurable[mΩ] Z μ := by
    dsimp [Z, q]
    exact hYint.aestronglyMeasurable.sub
      ((stronglyMeasurable_condExp (μ := μ) (m := m) (f := Y)).mono hm).aestronglyMeasurable
  have hVNae (n : ℕ) : AEStronglyMeasurable[mΩ] (VN n) μ := by
    dsimp [VN]
    exact Real.continuous_exp.comp_aestronglyMeasurable
      (((haN n).mono hm).aestronglyMeasurable.inner hZae)
  have hVNbound (n : ℕ) : ∀ᵐ ω ∂μ, ‖VN n ω‖ ≤ Real.exp (2 * γ * n) := by
    filter_upwards [hZnorm, haN_bound n] with ω hZ haω
    dsimp [VN]
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      inner ℝ (aN n ω) (Z ω) ≤ |inner ℝ (aN n ω) (Z ω)| := le_abs_self _
      _ = ‖inner ℝ (aN n ω) (Z ω)‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖aN n ω‖ * ‖Z ω‖ :=
        norm_inner_le_norm (𝕜 := ℝ) (aN n ω) (Z ω)
      _ ≤ (n : ℝ) * (2 * γ) :=
        mul_le_mul haω hZ (norm_nonneg (Z ω)) (Nat.cast_nonneg n)
      _ = 2 * γ * n := by ring
  have hVNint (n : ℕ) : Integrable (VN n) μ :=
    (integrable_const (Real.exp (2 * γ * n))).mono' (hVNae n) (hVNbound n)
  change μ[V | m] ≤ᵐ[μ] fun ω => Real.exp (3 * γ ^ 2 * ‖a ω‖ ^ 2)
  by_cases hVint : Integrable V μ
  · have hlocal (n : ℕ) : ∀ᵐ ω ∂μ, ω ∈ S n → μ[VN n | m] ω = μ[V | m] ω := by
      have hVNind := condExp_indicator (μ := μ) (m := m) (hVNint n) (hS n)
      have hVind := condExp_indicator (μ := μ) (m := m) hVint (hS n)
      have hindicator : (S n).indicator (VN n) = (S n).indicator V := by
        funext ω
        by_cases hω : ω ∈ S n
        · simp [Set.indicator_of_mem hω, VN, V, aN]
        · simp [Set.indicator_of_notMem hω]
      rw [hindicator] at hVNind
      filter_upwards [hVNind, hVind] with ω hVNω hVω
      intro hω
      simpa [Set.indicator_of_mem hω] using hVNω.symm.trans hVω
    have hlocal_all : ∀ᵐ ω ∂μ, ∀ n, ω ∈ S n → μ[VN n | m] ω = μ[V | m] ω :=
      ae_all_iff.mpr hlocal
    have hmgf_all : ∀ᵐ ω ∂μ, ∀ n,
        μ[VN n | m] ω ≤ Real.exp (3 * γ ^ 2 * ‖aN n ω‖ ^ 2) :=
      ae_all_iff.mpr hmgf
    filter_upwards [hlocal_all, hmgf_all] with ω hlocalω hmgfω
    obtain ⟨n, hn⟩ := exists_nat_ge ‖a ω‖
    have hω : ω ∈ S n := by simpa [S] using hn
    have haNω : aN n ω = a ω := by simp [aN, Set.indicator_of_mem hω]
    rw [← hlocalω n hω, ← haNω]
    exact hmgfω n
  · rw [condExp_of_not_integrable hVint]
    exact Filter.Eventually.of_forall (fun ω => by positivity)

@[blueprint "lem:clipped-sgd-clipping-estimates"
  (statement := /-- Let $(\Omega,\mathcal A,\mu)$ be a probability space, let
  $(\mathcal F_t)_{t\in\mathbb N}$ be a filtration, and fix $d\in\mathbb N$,
  $f:\mathbb R^d\to\mathbb R$, sequences $x_t,g_t:\Omega\to\mathbb R^d$,
  constants $G,p,\sigma\in\mathbb R$, and $L\in\mathbb R_{\geq0}$.  Assume the cost,
  heavy-tail noise, and clipped-SGD-run conditions of
  \cref{def:nonconvex-cost-assumptions,def:heavy-tail-noise-assumptions,def:clipped-sgd-run}
  with these parameters.  Then there exist sequences
  $b_t,u_t:\Omega\to\mathbb R^d$ such that $b_t$ is
  $\mathcal F_t$-measurable, $u_t$ is $\mathcal F_{t+1}$-measurable, and, for
  every $t\in\mathbb N$, almost surely,
  \[
    \operatorname{clip}_{\gamma_t}(g_t)
      =\nabla f(x_t)+b_t+u_t,
    \qquad
    \lVert b_t\rVert
      \leq4\sigma^p\gamma_t^{1-p},
    \qquad
    \lVert u_t\rVert
      \leq\gamma_t+G+4\sigma^p\gamma_t^{1-p},
  \]
  where $\gamma_t$ is defined in \cref{def:clipping-radius}.  Moreover, for every
  $t\in\mathbb N$ and every $\mathcal F_t$-measurable random vector
  $a:\Omega\to\mathbb R^d$, one has almost surely
  \[
    \mathbb E_\mu\!\left[
      \exp\!\bigl(\langle a,u_t\rangle\bigr)\,\middle|\,\mathcal F_t
    \right]
    \leq \exp\!\left(3\gamma_t^2\lVert a\rVert^2\right).
  \] -/)
  (proof := /-- The step size in \cref{def:clipped-step-size} is positive.  For
  each $t$, define
  \[
    \widetilde c_t=\alpha_t^{-1}(x_t-x_{t+1}).
  \]
  The update identity in \cref{def:clipped-sgd-run} shows that
  $\widetilde c_t=\operatorname{clip}_{\gamma_t}(g_t)$ almost surely, while the
  measurability of $x_t$ and $x_{t+1}$ makes $\widetilde c_t$
  $\mathcal F_{t+1}$-measurable.  By
  \cref{lem:clipping-radius-lower-local}, $\gamma_t>0$ and
  $\gamma_t\geq4G/3$; hence
  \cref{lem:clipped-vector-norm-le-radius-local} gives
  $\lVert\widetilde c_t\rVert\leq\gamma_t$ almost surely.  Moreover,
  \cref{lem:clipped-vector-norm-le-local} gives
  $\lVert\widetilde c_t\rVert\leq\lVert g_t\rVert$ almost surely.  Since
  $\widetilde c_t$ is measurable and $g_t$ is integrable, this comparison makes
  $\widetilde c_t$ integrable.

  Put $q_t=\mathbb E_\mu[\widetilde c_t\mid\mathcal F_t]$,
  $b_t=q_t-\nabla f(x_t)$, and $u_t=\widetilde c_t-q_t$.  The almost-sure
  identity above gives the decomposition required by
  \cref{def:has-clipping-estimates}.  The conditional unbiasedness of $g_t$ and
  linearity of conditional expectation identify $b_t$ with the conditional
  expectation of $\widetilde c_t-g_t$.  By
  \cref{lem:clipping-error-bound-local},
  \[
    \lVert\widetilde c_t-g_t\rVert
      \leq4\lVert g_t-\nabla f(x_t)\rVert^p\gamma_t^{1-p}
  \]
  almost surely.  Conditional Jensen's inequality for the norm, conditional
  monotonicity, scalar linearity, and the assumed conditional $p$-moment bound
  therefore yield
  $\lVert b_t\rVert\leq4\sigma^p\gamma_t^{1-p}$ almost surely.

  The definition of conditional expectation makes $q_t$
  $\mathcal F_t$-measurable, and the Lipschitz gradient composed with $x_t$ is
  $\mathcal F_t$-measurable.  Thus $b_t$ is $\mathcal F_t$-measurable and
  $u_t$ is $\mathcal F_{t+1}$-measurable.  Applying
  \cref{lem:conditional-mgf-local} to $Y=\widetilde c_t$ and
  $\mathcal G=\mathcal F_t$ gives the required conditional exponential-moment
  estimate for every $\mathcal F_t$-measurable test vector.  Finally, the
  identity
  $u_t=(\widetilde c_t-\nabla f(x_t))-b_t$, the bounds
  $\lVert\widetilde c_t\rVert\leq\gamma_t$ and
  $\lVert\nabla f(x_t)\rVert\leq G$, and the bias estimate imply
  $\lVert u_t\rVert\leq\gamma_t+G+4\sigma^p\gamma_t^{1-p}$ by two applications
  of the triangle inequality.  These facts are precisely
  \cref{def:has-adapted-clipping-estimates}. -/)
  (title := /-- Adapted clipping bias and conditional exponential-moment bounds -/)
  (latexEnv := "lemma")]
lemma clipped_sgd_clipping_estimates
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    {d : ℕ} (filtration : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x g : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (G : ℝ) (L : NNReal) (p σ : ℝ)
    (hcost : nonconvex_cost_assumptions f G L)
    (hnoise : heavy_tail_noise_assumptions μ filtration f x g p σ)
    (hrun : clipped_sgd_run μ filtration x g G p) :
    ∃ bias centered : ℕ → Ω → EuclideanSpace ℝ (Fin d),
      has_adapted_clipping_estimates μ filtration f x g bias centered G p σ := by
  rcases hcost with ⟨hG, hbelow, hdiff, hgrad, hLip⟩
  rcases hnoise with ⟨hp1, hp2, hσ, hgint, hnoiseint, hunbiased, hmoment⟩
  rcases hrun with ⟨hxzero, hxmeas, hupdate⟩
  letI : MeasurableSpace (EuclideanSpace ℝ (Fin d)) :=
    borel (EuclideanSpace ℝ (Fin d))
  letI : BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩
  have hα (t : ℕ) : 0 < clipped_step_size p t := by
    unfold clipped_step_size
    exact Real.rpow_pos_of_pos (by positivity) _
  have hγlower (t : ℕ) : 4 * G / 3 ≤ clipping_radius G p t :=
    clipping_radius_lower_local hG hp1 hp2 t
  have hγ (t : ℕ) : 0 < clipping_radius G p t := by
    have hfour : 0 < 4 * G / 3 := by positivity
    exact hfour.trans_le (hγlower t)
  let Y : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun t ω =>
    (clipped_step_size p t)⁻¹ • (x t ω - x (t + 1) ω)
  let N : ℕ → Ω → ℝ := fun t ω =>
    Real.rpow ‖g t ω - gradient f (x t ω)‖ p
  let q : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun t => μ[Y t | filtration t]
  let bias : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun t ω =>
    q t ω - gradient f (x t ω)
  let centered : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun t ω =>
    Y t ω - q t ω
  have hYeq (t : ℕ) : Y t =ᵐ[μ] fun ω =>
      clipped_vector (clipping_radius G p t) (g t ω) := by
    filter_upwards [hupdate t] with ω hω
    dsimp [Y]
    rw [hω]
    simp [ne_of_gt (hα t)]
  have hYmeas (t : ℕ) :
      Measurable[filtration (t + 1), borel (EuclideanSpace ℝ (Fin d))] (Y t) := by
    dsimp [Y]
    exact (((hxmeas t).mono (filtration.mono (by omega)) le_rfl).sub
      (hxmeas (t + 1))).const_smul (clipped_step_size p t)⁻¹
  have hYnorm (t : ℕ) : ∀ᵐ ω ∂μ, ‖Y t ω‖ ≤ clipping_radius G p t := by
    filter_upwards [hYeq t] with ω hω
    rw [hω]
    exact clipped_vector_norm_le_radius_local (hγ t).le (g t ω)
  have hYnorm_g (t : ℕ) : ∀ᵐ ω ∂μ, ‖Y t ω‖ ≤ ‖g t ω‖ := by
    filter_upwards [hYeq t] with ω hω
    rw [hω]
    exact clipped_vector_norm_le_local (hγ t).le (g t ω)
  have hYint (t : ℕ) : Integrable (Y t) μ := by
    have hYstrong : StronglyMeasurable (Y t) :=
      ((hYmeas t).mono (filtration.le (t + 1)) le_rfl).stronglyMeasurable
    exact (hgint t).norm.mono' hYstrong.aestronglyMeasurable (hYnorm_g t)
  have hNint (t : ℕ) : Integrable (N t) μ := by
    simpa [N] using hnoiseint t
  have herror (t : ℕ) : ∀ᵐ ω ∂μ,
      ‖Y t ω - g t ω‖ ≤
        4 * N t ω * Real.rpow (clipping_radius G p t) (1 - p) := by
    filter_upwards [hYeq t] with ω hω
    rw [hω]
    exact clipping_error_bound_local hG (hγ t) (hγlower t) hp1 hp2
      (g t ω) (gradient f (x t ω)) (hgrad (x t ω))
  have hbias (t : ℕ) : ∀ᵐ ω ∂μ,
      ‖bias t ω‖ ≤ 4 * Real.rpow σ p *
        Real.rpow (clipping_radius G p t) (1 - p) := by
    let c : ℝ := 4 * Real.rpow (clipping_radius G p t) (1 - p)
    have hc : 0 ≤ c := by
      dsimp [c]
      exact mul_nonneg (by norm_num) (Real.rpow_nonneg (hγ t).le _)
    have herror' : (fun ω => ‖Y t ω - g t ω‖) ≤ᵐ[μ] c • N t := by
      filter_upwards [herror t] with ω hω
      simpa [c, Pi.smul_apply, mul_comm, mul_left_comm, mul_assoc] using hω
    have hsub := condExp_sub (hYint t) (hgint t) (filtration t)
    have hnorm := norm_condExp_le (μ := μ) (m := filtration t)
      (fun ω => Y t ω - g t ω)
    have hmono := condExp_mono (μ := μ) (m := filtration t)
      ((hYint t).sub (hgint t)).norm ((hNint t).smul c) herror'
    have hsmul := condExp_smul (μ := μ) c (N t) (filtration t)
    filter_upwards [hunbiased t, hsub, hnorm, hmono, hsmul, hmoment t] with
        ω hunbω hsubω hnormω hmonoω hsmulω hmomentω
    dsimp [bias, q]
    calc
      ‖μ[Y t | filtration t] ω - gradient f (x t ω)‖ =
          ‖μ[Y t | filtration t] ω - μ[g t | filtration t] ω‖ := by rw [hunbω]
      _ = ‖μ[Y t - g t | filtration t] ω‖ := (congrArg norm hsubω).symm
      _ ≤ μ[(fun ω => ‖Y t ω - g t ω‖) | filtration t] ω := hnormω
      _ ≤ μ[c • N t | filtration t] ω := hmonoω
      _ = c * μ[N t | filtration t] ω := by simpa [Pi.smul_apply] using hsmulω
      _ ≤ c * Real.rpow σ p := mul_le_mul_of_nonneg_left (by simpa [N] using hmomentω) hc
      _ = 4 * Real.rpow σ p *
          Real.rpow (clipping_radius G p t) (1 - p) := by dsimp [c]; ring
  refine ⟨bias, centered, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro t
      filter_upwards [hYeq t] with ω hω
      dsimp [bias, centered, q]
      rw [← hω]
      module
    · exact hbias
    · intro t a ha
      simpa [centered, q] using conditional_mgf_local μ (filtration t)
        (filtration.le t) (Y t) (clipping_radius G p t) (hγ t).le
        (hYint t) (hYnorm t) a ha.stronglyMeasurable
  · intro t
    dsimp [bias, q]
    exact (stronglyMeasurable_condExp (μ := μ) (m := filtration t) (f := Y t)).measurable.sub
      (hLip.continuous.measurable.comp (hxmeas t))
  · intro t
    dsimp [centered, q]
    exact (hYmeas t).sub
      ((stronglyMeasurable_condExp (μ := μ) (m := filtration t) (f := Y t)).measurable.mono
        (filtration.mono (by omega)) le_rfl)
  · intro t
    filter_upwards [hYnorm t, hbias t] with ω hYnω hbω
    dsimp [centered, bias, q] at hbω ⊢
    calc
      ‖Y t ω - μ[Y t | filtration t] ω‖ =
          ‖(Y t ω - gradient f (x t ω)) -
            (μ[Y t | filtration t] ω - gradient f (x t ω))‖ := by
              congr 1
              module
      _ ≤ ‖Y t ω - gradient f (x t ω)‖ +
          ‖μ[Y t | filtration t] ω - gradient f (x t ω)‖ := norm_sub_le _ _
      _ ≤ (‖Y t ω‖ + ‖gradient f (x t ω)‖) +
          ‖μ[Y t | filtration t] ω - gradient f (x t ω)‖ :=
            add_le_add (norm_sub_le _ _) (le_refl _)
      _ ≤ clipping_radius G p t + G +
          4 * Real.rpow σ p * Real.rpow (clipping_radius G p t) (1 - p) := by
            exact add_le_add (add_le_add hYnω (hgrad (x t ω))) hbω

@[blueprint "lem:finite-horizon-conditional-mgf"
  (statement := /-- Let $(\Omega,\mathcal A,\mu)$ be a probability space, let
  $(\mathcal F_t)_{t\geq0}$ be a filtration, and let
  $f:\mathbb R^d\to\mathbb R$ and $x_t,g_t,b_t,u_t:\Omega\to\mathbb R^d$.
  Fix $G,p,\sigma\in\mathbb R$, and assume that these objects satisfy
  \cref{def:has-adapted-clipping-estimates}, with $b_t$ as the bias and $u_t$ as
  the centered increment.  For every $t\in\mathbb N$, let
  $a_t:\Omega\to\mathbb R^d$ be $\mathcal F_t$-measurable and let
  $A_t\in[0,\infty)$ be deterministic, with
  $\lVert a_t\rVert\leq A_t$ almost surely.  For every
  $n\in\mathbb N$ and $r\geq0$, if
  \[
    V_n=\sum_{k<n}\gamma_k^2A_k^2>0,
  \]
  then
  \[
    \mu\left\{\omega:r\leq
      \sum_{k<n}\langle a_k(\omega),u_k(\omega)\rangle\right\}
      \leq \exp\left(-\frac{r^2}{12V_n}\right).
  \] -/)
  (proof := /-- Put
  $S_m=\sum_{k<m}\langle a_k,u_k\rangle$ and
  $V_m=\sum_{k<m}\gamma_k^2A_k^2$.  The adaptedness and deterministic bound in
  \cref{def:has-adapted-clipping-estimates}, together with
  $\lVert a_k\rVert\leq A_k$ almost surely, imply that $S_m$ is measurable and
  that $\exp(\lambda S_m)$ is integrable for every $m\in\mathbb N$ and
  $\lambda\geq0$.

  Fix such a $\lambda$.  For the induction step, set
  $P_m=\exp(\lambda S_m)$ and
  $Q_m=\exp(\langle\lambda a_m,u_m\rangle)$.  The random variable $P_m$ is
  $\mathcal F_m$-measurable and bounded.  The pull-out identity
  \[
    \mathbb E[P_mQ_m]
      =\mathbb E\!\left[P_m\,\mathbb E[Q_m\mid\mathcal F_m]\right]
  \]
  follows first for $\mathcal F_m$-measurable simple functions from the defining
  set-integral identity for conditional expectation.  Approximate $P_m$ by such
  simple functions in $L^1$; the almost-sure deterministic bounds on $Q_m$ and
  its conditional expectation allow passage to the limit in both products.
  Applying the conditional exponential-moment clause of
  \cref{def:has-adapted-clipping-estimates} to $\lambda a_m$ and using
  $\lVert\lambda a_m\rVert^2\leq\lambda^2A_m^2$ gives
  \[
    \mathbb E[Q_m\mid\mathcal F_m]
      \leq \exp(3\lambda^2\gamma_m^2A_m^2)
  \]
  almost surely.  Since $P_m\geq0$, induction yields
  \[
    \mathbb E\exp\!\left(\lambda S_n\right)
      \leq \exp(3\lambda^2V_n).
  \]

  If $r=0$, the conclusion is the bound of a probability by one.  If $r>0$,
  take $\lambda=r/(6V_n)>0$.  Markov's inequality, monotonicity of the
  exponential, and the preceding moment estimate give
  \[
    \mu\{S_n\geq r\}
      \leq\exp(-\lambda r+3\lambda^2V_n)
      =\exp\!\left(-\frac{r^2}{12V_n}\right),
  \]
  as required. -/)
  (title := /-- Finite-horizon concentration from conditional MGF bounds -/)
  (latexEnv := "lemma")]
lemma finite_horizon_conditional_mgf
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    {d : ℕ} (filtration : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x g bias centered : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (G p σ : ℝ)
    (hest : has_adapted_clipping_estimates μ filtration f x g bias centered G p σ)
    (a : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (A : ℕ → ℝ)
    (ha : ∀ t, Measurable[filtration t, borel (EuclideanSpace ℝ (Fin d))] (a t))
    (hA : ∀ t, 0 ≤ A t)
    (ha_bound : ∀ t, ∀ᵐ ω ∂μ, ‖a t ω‖ ≤ A t)
    (n : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hV : 0 < ∑ k ∈ Finset.range n,
      (clipping_radius G p k) ^ 2 * (A k) ^ 2) :
    μ {ω | r ≤ ∑ k ∈ Finset.range n, inner ℝ (a k ω) (centered k ω)} ≤
      ENNReal.ofReal (Real.exp
        (-(r ^ 2) / (12 * ∑ k ∈ Finset.range n,
          (clipping_radius G p k) ^ 2 * (A k) ^ 2))) := by
  rcases hest with ⟨⟨hdecomp, hbias_bound, hmgf⟩, hbias_meas, hcentered_meas,
    hcentered_bound⟩
  letI : MeasurableSpace (EuclideanSpace ℝ (Fin d)) :=
    borel (EuclideanSpace ℝ (Fin d))
  letI : BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩
  let X : ℕ → Ω → ℝ := fun m ω =>
    ∑ k ∈ Finset.range m, inner ℝ (a k ω) (centered k ω)
  let V : ℕ → ℝ := fun m =>
    ∑ k ∈ Finset.range m, (clipping_radius G p k) ^ 2 * (A k) ^ 2
  let B : ℕ → ℝ := fun k =>
    clipping_radius G p k + G +
      4 * Real.rpow σ p * Real.rpow (clipping_radius G p k) (1 - p)
  change μ {ω | r ≤ X n ω} ≤
    ENNReal.ofReal (Real.exp (-(r ^ 2) / (12 * V n)))
  have hX_meas_filtration (m : ℕ) :
      Measurable[filtration m, borel ℝ] (X m) := by
    letI : MeasurableSpace Ω := filtration m
    dsimp [X]
    refine Finset.measurable_sum _ fun k hk => ?_
    have hkm : k < m := Finset.mem_range.mp hk
    exact Continuous.measurable2 continuous_inner
      ((ha k).mono (filtration.mono hkm.le) le_rfl)
      ((hcentered_meas k).mono
        (filtration.mono (Nat.succ_le_iff.mpr hkm)) le_rfl)
  have hX_meas (m : ℕ) : Measurable (X m) :=
    (hX_meas_filtration m).mono (filtration.le m) le_rfl
  have h_exp_integrable (l : ℝ) (hl : 0 ≤ l) (m : ℕ) :
      Integrable (fun ω => Real.exp (l * X m ω)) μ := by
    apply Integrable.of_bound
      ((measurable_const.mul (hX_meas m)).exp.aestronglyMeasurable)
      (Real.exp (l * ∑ k ∈ Finset.range m, A k * B k))
    filter_upwards [ae_all_iff.mpr ha_bound, ae_all_iff.mpr hcentered_bound]
      with ω haω hcω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    change l * X m ω ≤ l * (∑ k ∈ Finset.range m, A k * B k)
    apply mul_le_mul_of_nonneg_left _ hl
    dsimp [X]
    refine Finset.sum_le_sum fun k hk => ?_
    calc
      inner ℝ (a k ω) (centered k ω)
          ≤ |inner ℝ (a k ω) (centered k ω)| := le_abs_self _
      _ ≤ ‖a k ω‖ * ‖centered k ω‖ := abs_real_inner_le_norm _ _
      _ ≤ A k * B k := by
        exact mul_le_mul (haω k) (by simpa [B] using hcω k)
          (norm_nonneg _) (hA k)
  have h_single_integrable (l : ℝ) (hl : 0 ≤ l) (k : ℕ) :
      Integrable
        (fun ω => Real.exp (inner ℝ (l • a k ω) (centered k ω))) μ := by
    have hla : Measurable[filtration k, borel (EuclideanSpace ℝ (Fin d))]
        (fun ω => l • a k ω) :=
      (continuous_id.const_smul l).measurable.comp (ha k)
    apply Integrable.of_bound
      ((Continuous.measurable2 continuous_inner
        (hla.mono (filtration.le k) le_rfl)
        ((hcentered_meas k).mono (filtration.le (k + 1)) le_rfl)).exp
        |>.aestronglyMeasurable)
      (Real.exp (l * A k * B k))
    filter_upwards [ha_bound k, hcentered_bound k] with ω haω hcω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    rw [real_inner_smul_left]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hl
    calc
      inner ℝ (a k ω) (centered k ω)
          ≤ |inner ℝ (a k ω) (centered k ω)| := le_abs_self _
      _ ≤ ‖a k ω‖ * ‖centered k ω‖ := abs_real_inner_le_norm _ _
      _ ≤ A k * B k := by
        exact mul_le_mul haω (by simpa [B] using hcω)
          (norm_nonneg _) (hA k)
  have h_moment (l : ℝ) (hl : 0 ≤ l) (m : ℕ) :
      ∫ ω, Real.exp (l * X m ω) ∂μ ≤ Real.exp (3 * l ^ 2 * V m) := by
    induction m with
    | zero => simp [X, V]
    | succ m ih =>
        let previous : Ω → ℝ := fun ω => Real.exp (l * X m ω)
        let current : Ω → ℝ := fun ω =>
          Real.exp (inner ℝ (l • a m ω) (centered m ω))
        let C : ℝ := Real.exp
          (3 * l ^ 2 * (clipping_radius G p m) ^ 2 * (A m) ^ 2)
        have hsplit : (fun ω => Real.exp (l * X (m + 1) ω)) =
            fun ω => previous ω * current ω := by
          funext ω
          simp only [previous, current, X, Finset.sum_range_succ]
          rw [mul_add, Real.exp_add, real_inner_smul_left]
        have hprod_int : Integrable (fun ω => previous ω * current ω) μ := by
          rw [← hsplit]
          exact h_exp_integrable l hl (m + 1)
        have hcurrent_int : Integrable current μ :=
          h_single_integrable l hl m
        have hprevious_strong :
            StronglyMeasurable[filtration m] previous :=
          (measurable_const.mul (hX_meas_filtration m)).exp.stronglyMeasurable
        let D : ℝ := Real.exp
          (l * ∑ k ∈ Finset.range m, A k * B k)
        have hprevious_bound : ∀ᵐ ω ∂μ, ‖previous ω‖ ≤ D := by
          filter_upwards [ae_all_iff.mpr ha_bound,
            ae_all_iff.mpr hcentered_bound] with ω haω hcω
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          apply Real.exp_le_exp.mpr
          change l * X m ω ≤ l * (∑ k ∈ Finset.range m, A k * B k)
          apply mul_le_mul_of_nonneg_left _ hl
          dsimp [X]
          refine Finset.sum_le_sum fun k hk => ?_
          calc
            inner ℝ (a k ω) (centered k ω) ≤
                |inner ℝ (a k ω) (centered k ω)| := le_abs_self _
            _ ≤ ‖a k ω‖ * ‖centered k ω‖ := abs_real_inner_le_norm _ _
            _ ≤ A k * B k := by
              exact mul_le_mul (haω k) (by simpa [B] using hcω k)
                (norm_nonneg _) (hA k)
        have hcond_local : ∀ᵐ ω ∂μ, μ[current | filtration m] ω ≤ C := by
          have hla : Measurable[filtration m,
              borel (EuclideanSpace ℝ (Fin d))] (fun ω => l • a m ω) :=
            (continuous_id.const_smul l).measurable.comp (ha m)
          filter_upwards
            [hmgf m (fun ω => l • a m ω) hla, ha_bound m]
            with ω hcondω haω
          refine hcondω.trans (Real.exp_le_exp.mpr ?_)
          have hsquare : ‖a m ω‖ ^ 2 ≤ (A m) ^ 2 :=
            (sq_le_sq₀ (norm_nonneg _) (hA m)).2 haω
          simp only [norm_smul, Real.norm_eq_abs]
          change 3 * (clipping_radius G p m) ^ 2 *
              (|l| * ‖a m ω‖) ^ 2 ≤
            3 * l ^ 2 * (clipping_radius G p m) ^ 2 * (A m) ^ 2
          calc
            3 * (clipping_radius G p m) ^ 2 *
                (|l| * ‖a m ω‖) ^ 2 =
                (3 * (clipping_radius G p m) ^ 2 * l ^ 2) *
                  ‖a m ω‖ ^ 2 := by rw [mul_pow, sq_abs]; ring
            _ ≤ (3 * (clipping_radius G p m) ^ 2 * l ^ 2) *
                  (A m) ^ 2 :=
              mul_le_mul_of_nonneg_left hsquare (by positivity)
            _ = 3 * l ^ 2 * (clipping_radius G p m) ^ 2 *
                  (A m) ^ 2 := by ring
        let M : ℝ := Real.exp (l * A m * B m)
        have hcurrent_bound : ∀ᵐ ω ∂μ, ‖current ω‖ ≤ M := by
          filter_upwards [ha_bound m, hcentered_bound m] with ω haω hcω
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          apply Real.exp_le_exp.mpr
          rw [real_inner_smul_left, mul_assoc]
          apply mul_le_mul_of_nonneg_left _ hl
          calc
            inner ℝ (a m ω) (centered m ω) ≤
                |inner ℝ (a m ω) (centered m ω)| := le_abs_self _
            _ ≤ ‖a m ω‖ * ‖centered m ω‖ := abs_real_inner_le_norm _ _
            _ ≤ A m * B m := by
              exact mul_le_mul haω (by simpa [B] using hcω)
                (norm_nonneg _) (hA m)
        have hcond_norm_bound :
            ∀ᵐ ω ∂μ, ‖μ[current | filtration m] ω‖ ≤ C := by
          filter_upwards [hcond_local,
            condExp_nonneg (μ := μ) (m := filtration m) (f := current)
              (ae_of_all μ fun _ => Real.exp_nonneg _)] with ω hc hn
          rw [Real.norm_eq_abs, abs_of_nonneg hn]
          exact hc
        have hpull_integral :
            ∫ ω, previous ω * current ω ∂μ =
              ∫ ω, previous ω * μ[current | filtration m] ω ∂μ := by
          let fs : ℕ → @SimpleFunc Ω (filtration m) ℝ :=
            by
              letI : MeasurableSpace Ω := filtration m
              exact fun j => SimpleFunc.approxOn previous
                (measurable_const.mul (hX_meas_filtration m)).exp
                (Set.range previous ∪ {0}) 0 (by simp) j
          have happrox : Filter.Tendsto
              (fun j => ∫ ω, ‖fs j ω - previous ω‖ ∂μ) Filter.atTop
              (nhds 0) := by
            simpa [fs, SimpleFunc.approxOn] using
              (tendsto_integral_norm_approxOn_sub
                (measurable_const.mul (hX_meas m)).exp
                (h_exp_integrable l hl m))
          have hsimple_mul_int (s : @SimpleFunc Ω (filtration m) ℝ)
              {q : Ω → ℝ} (hq : Integrable q μ) :
              Integrable (fun ω => s ω * q ω) μ := by
            obtain ⟨K, hK⟩ : ∃ K, ∀ ω, ‖s ω‖ ≤ K := by
              letI : MeasurableSpace Ω := filtration m
              exact SimpleFunc.exists_forall_norm_le s
            exact hq.bdd_mul
              (s.stronglyMeasurable.mono (filtration.le m)
                |>.aestronglyMeasurable) (ae_of_all μ hK)
          have hsimple (s : @SimpleFunc Ω (filtration m) ℝ) :
              ∫ ω, s ω * current ω ∂μ =
                ∫ ω, s ω * μ[current | filtration m] ω ∂μ := by
            apply @SimpleFunc.induction _ _ (filtration m) _
              (fun s => ∫ ω, s ω * current ω ∂μ =
                ∫ ω, s ω * μ[current | filtration m] ω ∂μ)
              (fun c s hs => ?_) (fun s₁ s₂ hdisj h₁ h₂ => ?_) s
            · simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise,
                SimpleFunc.coe_const, SimpleFunc.coe_zero,
                Set.piecewise_eq_indicator]
              have hindicator (q : Ω → ℝ) :
                  (fun ω => Set.indicator s (Function.const Ω c) ω * q ω) =
                    s.indicator (fun ω => c * q ω) := by
                funext ω
                by_cases hω : ω ∈ s <;> simp [hω]
              rw [hindicator current,
                hindicator (μ[current | filtration m])]
              rw [integral_indicator (filtration.le m s hs),
                integral_indicator (filtration.le m s hs),
                integral_const_mul, integral_const_mul,
                setIntegral_condExp (filtration.le m) hcurrent_int hs]
            · simp only [SimpleFunc.coe_add, Pi.add_apply, add_mul]
              calc
                ∫ ω, s₁ ω * current ω + s₂ ω * current ω ∂μ =
                    (∫ ω, s₁ ω * current ω ∂μ) +
                      ∫ ω, s₂ ω * current ω ∂μ := by
                  exact integral_add (hsimple_mul_int s₁ hcurrent_int)
                    (hsimple_mul_int s₂ hcurrent_int)
                _ = (∫ ω, s₁ ω * μ[current | filtration m] ω ∂μ) +
                      ∫ ω, s₂ ω * μ[current | filtration m] ω ∂μ := by
                  rw [h₁, h₂]
                _ = ∫ ω, s₁ ω * μ[current | filtration m] ω +
                      s₂ ω * μ[current | filtration m] ω ∂μ := by
                  exact (integral_add
                    (hsimple_mul_int s₁ integrable_condExp)
                    (hsimple_mul_int s₂ integrable_condExp)).symm
          have htendsto_mul {q : Ω → ℝ} (hq : Integrable q μ)
              (hprevq : Integrable (fun ω => previous ω * q ω) μ)
              (K : ℝ) (hq_bound : ∀ᵐ ω ∂μ, ‖q ω‖ ≤ K) :
              Filter.Tendsto (fun j => ∫ ω, fs j ω * q ω ∂μ)
                Filter.atTop (nhds (∫ ω, previous ω * q ω ∂μ)) := by
            rw [tendsto_iff_norm_sub_tendsto_zero]
            apply squeeze_zero (fun j => norm_nonneg _)
            · intro j
              have hfjq := hsimple_mul_int (fs j) hq
              have hdiff_int : Integrable
                  (fun ω => (fs j ω - previous ω) * q ω) μ := by
                exact (hfjq.sub hprevq).congr (ae_of_all μ fun ω => by
                  simp only [Pi.sub_apply, sub_mul])
              have hnormdiff_int : Integrable
                  (fun ω => ‖fs j ω - previous ω‖) μ := by
                obtain ⟨Kj, hKj⟩ : ∃ K, ∀ ω, ‖fs j ω‖ ≤ K := by
                  letI : MeasurableSpace Ω := filtration m
                  exact SimpleFunc.exists_forall_norm_le (fs j)
                have hfsj_int : Integrable (fun ω => fs j ω) μ :=
                  Integrable.of_bound
                    ((fs j).stronglyMeasurable.mono (filtration.le m)
                      |>.aestronglyMeasurable) Kj (ae_of_all μ hKj)
                exact (hfsj_int.sub (h_exp_integrable l hl m)).norm
              calc
                ‖(∫ ω, fs j ω * q ω ∂μ) -
                    ∫ ω, previous ω * q ω ∂μ‖ =
                    ‖∫ ω, (fs j ω - previous ω) * q ω ∂μ‖ := by
                  rw [← integral_sub hfjq hprevq]
                  congr 2
                  funext ω
                  ring
                _ ≤ ∫ ω, ‖(fs j ω - previous ω) * q ω‖ ∂μ :=
                  norm_integral_le_integral_norm _
                _ ≤ ∫ ω, K * ‖fs j ω - previous ω‖ ∂μ := by
                  apply integral_mono_ae hdiff_int.norm
                    (hnormdiff_int.const_mul K)
                  filter_upwards [hq_bound] with ω hqω
                  rw [norm_mul]
                  calc
                    ‖fs j ω - previous ω‖ * ‖q ω‖ ≤
                        ‖fs j ω - previous ω‖ * K :=
                      mul_le_mul_of_nonneg_left hqω (norm_nonneg _)
                    _ = K * ‖fs j ω - previous ω‖ := mul_comm _ _
                _ = K * ∫ ω, ‖fs j ω - previous ω‖ ∂μ :=
                  integral_const_mul _ _
            · simpa using (tendsto_const_nhds.mul happrox)
          have hleft_tendsto := htendsto_mul hcurrent_int hprod_int M
            hcurrent_bound
          have hprev_cond_int : Integrable
              (fun ω => previous ω * μ[current | filtration m] ω) μ :=
            integrable_condExp.bdd_mul
              (hprevious_strong.mono (filtration.le m)
                |>.aestronglyMeasurable) hprevious_bound
          have hright_tendsto := htendsto_mul integrable_condExp
            hprev_cond_int C hcond_norm_bound
          have hseq : (fun j => ∫ ω, fs j ω * current ω ∂μ) =
              fun j => ∫ ω, fs j ω * μ[current | filtration m] ω ∂μ := by
            funext j
            exact hsimple (fs j)
          rw [hseq] at hleft_tendsto
          exact tendsto_nhds_unique hleft_tendsto hright_tendsto
        have hcond : ∀ᵐ ω ∂μ, μ[current | filtration m] ω ≤ C := by
          have hla : Measurable[filtration m,
              borel (EuclideanSpace ℝ (Fin d))] (fun ω => l • a m ω) :=
            (continuous_id.const_smul l).measurable.comp (ha m)
          filter_upwards
            [hmgf m (fun ω => l • a m ω) hla, ha_bound m]
            with ω hcondω haω
          calc
            μ[current | filtration m] ω ≤
                Real.exp (3 * (clipping_radius G p m) ^ 2 *
                  ‖l • a m ω‖ ^ 2) := hcondω
            _ ≤ C := by
              apply Real.exp_le_exp.mpr
              have hsquare : ‖a m ω‖ ^ 2 ≤ (A m) ^ 2 := by
                exact (sq_le_sq₀ (norm_nonneg _) (hA m)).2 haω
              simp only [norm_smul, Real.norm_eq_abs]
              change 3 * (clipping_radius G p m) ^ 2 *
                  (|l| * ‖a m ω‖) ^ 2 ≤
                3 * l ^ 2 * (clipping_radius G p m) ^ 2 * (A m) ^ 2
              calc
                3 * (clipping_radius G p m) ^ 2 *
                    (|l| * ‖a m ω‖) ^ 2 =
                    (3 * (clipping_radius G p m) ^ 2 * l ^ 2) *
                      ‖a m ω‖ ^ 2 := by rw [mul_pow, sq_abs]; ring
                _ ≤ (3 * (clipping_radius G p m) ^ 2 * l ^ 2) *
                      (A m) ^ 2 :=
                  mul_le_mul_of_nonneg_left hsquare (by positivity)
                _ = 3 * l ^ 2 * (clipping_radius G p m) ^ 2 *
                      (A m) ^ 2 := by ring
        have hleft_int : Integrable
            (fun ω => previous ω * μ[current | filtration m] ω) μ :=
          integrable_condExp.bdd_mul
            (hprevious_strong.mono (filtration.le m)).aestronglyMeasurable
            hprevious_bound
        have hright_int : Integrable (fun ω => previous ω * C) μ :=
          (h_exp_integrable l hl m).mul_const C
        calc
          ∫ ω, Real.exp (l * X (m + 1) ω) ∂μ =
              ∫ ω, previous ω * current ω ∂μ := by rw [hsplit]
          _ = ∫ ω, previous ω * μ[current | filtration m] ω ∂μ :=
            hpull_integral
          _ ≤ ∫ ω, previous ω * C ∂μ := by
            apply integral_mono_ae hleft_int hright_int
            filter_upwards [hcond] with ω hcondω
            exact mul_le_mul_of_nonneg_left hcondω (Real.exp_nonneg _)
          _ = C * ∫ ω, previous ω ∂μ := by
            rw [integral_mul_const]
            ring
          _ ≤ C * Real.exp (3 * l ^ 2 * V m) := by
            exact mul_le_mul_of_nonneg_left ih (Real.exp_nonneg _)
          _ = Real.exp (3 * l ^ 2 * V (m + 1)) := by
            rw [← Real.exp_add]
            congr 1
            simp only [C, V, Finset.sum_range_succ]
            ring
  by_cases hr0 : r = 0
  · subst r
    simpa using (measure_mono (μ := μ)
      (Set.subset_univ {ω | 0 ≤ X n ω}))
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  let l : ℝ := r / (6 * V n)
  have hVpos : 0 < V n := by simpa [V] using hV
  have hlpos : 0 < l := div_pos hrpos (mul_pos (by norm_num) hVpos)
  have hl : 0 ≤ l := hlpos.le
  have hexp_int : Integrable (fun ω => Real.exp (l * X n ω)) μ :=
    h_exp_integrable l hl n
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun ω => Real.exp (l * X n ω))
    (ae_of_all μ fun _ => Real.exp_nonneg _) hexp_int (Real.exp (l * r))
  have hevent : {ω | Real.exp (l * r) ≤ Real.exp (l * X n ω)} =
      {ω | r ≤ X n ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Real.exp_le_exp]
    exact mul_le_mul_iff_of_pos_left hlpos
  rw [hevent] at hmarkov
  have hmom := h_moment l hl n
  have hreal : (μ {ω | r ≤ X n ω}).toReal ≤
      Real.exp (-(r ^ 2) / (12 * V n)) := by
    have hmul : Real.exp (l * r) * (μ {ω | r ≤ X n ω}).toReal ≤
        Real.exp (3 * l ^ 2 * V n) := hmarkov.trans hmom
    have hmul' : (μ {ω | r ≤ X n ω}).toReal * Real.exp (l * r) ≤
        Real.exp (3 * l ^ 2 * V n) := by simpa [mul_comm] using hmul
    have hdiv := (le_div_iff₀ (Real.exp_pos (l * r))).mpr hmul'
    rw [← Real.exp_sub] at hdiv
    convert hdiv using 1
    congr 1
    dsimp [l]
    field_simp
    ring_nf
  refine (ENNReal.toReal_le_toReal
    (a := μ {ω | r ≤ X n ω})
    (b := ENNReal.ofReal (Real.exp (-(r ^ 2) / (12 * V n))))
    (measure_ne_top μ _) ENNReal.ofReal_ne_top).mp ?_
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  exact hreal

@[blueprint "lem:lipschitz-gradient-quadratic-upper-local"
  (statement := /-- Let $f:\mathbb R^d\to\mathbb R$ be differentiable, and suppose
  that its gradient is $L$-Lipschitz for some $L\geq0$.  Then, for all
  $x,y\in\mathbb R^d$,
  \[
    f(y)\leq f(x)+\langle\nabla f(x),y-x\rangle
      +\frac L2\lVert y-x\rVert^2.
  \] -/)
  (proof := /-- Parametrize the segment from $x$ to $y$ by
  $x+t(y-x)$ for $0\leq t\leq1$.  The chain rule identifies the derivative of
  $t\mapsto f(x+t(y-x))$ with
  $\langle\nabla f(x+t(y-x)),y-x\rangle$.  The fundamental theorem of calculus
  therefore expresses the first-order remainder as the integral of
  $\langle\nabla f(x+t(y-x))-\nabla f(x),y-x\rangle$.  The Lipschitz hypothesis
  and Cauchy--Schwarz bound this integrand by
  $Lt\lVert y-x\rVert^2$.  Integration over $[0,1]$ gives the factor $L/2$. -/)
  (title := /-- Quadratic upper bound from a Lipschitz gradient -/)
  (latexEnv := "lemma")]
lemma lipschitz_gradient_quadratic_upper_local
    {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (L : NNReal)
    (hdiff : Differentiable ℝ f) (hLip : LipschitzWith L (gradient f))
    (x y : EuclideanSpace ℝ (Fin d)) :
    f y ≤ f x + inner ℝ (gradient f x) (y - x) +
      ((L : ℝ) / 2) * ‖y - x‖ ^ 2 := by
  let v := y - x
  have hline : Continuous (fun t : ℝ => x + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (x + s • v))
      (fderiv ℝ f (x + t • v) v) t := by
    intro t
    have hline_deriv : HasDerivAt (fun s : ℝ => x + s • v) v t := by
      simpa using (hasDerivAt_id t).smul_const v |>.const_add x
    simpa only [Function.comp_apply, Function.comp_def] using
      (hdiff (x + t • v)).hasFDerivAt.comp_hasDerivAt t hline_deriv
  have habs : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |inner ℝ (gradient f (x + t • v) - gradient f x) v| ≤
        (L : ℝ) * t * ‖v‖ ^ 2 := by
    intro t ht
    calc
      |inner ℝ (gradient f (x + t • v) - gradient f x) v| ≤
          ‖gradient f (x + t • v) - gradient f x‖ * ‖v‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ ((L : ℝ) * ‖(x + t • v) - x‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (hLip.norm_sub_le _ _) (norm_nonneg v)
      _ = (L : ℝ) * t * ‖v‖ ^ 2 := by
        simp [norm_smul, abs_of_nonneg ht.1]
        ring
  let c := fderiv ℝ f x v
  let q := (L : ℝ) / 2 * ‖v‖ ^ 2
  let model : ℝ → ℝ := fun t => f (x + t • v) - t * c - t ^ 2 * q
  have hmodel_deriv (t : ℝ) : HasDerivAt model
      (fderiv ℝ f (x + t • v) v - c -
        2 * t * q) t := by
    have hlinear : HasDerivAt (fun s : ℝ => s * c) c t := by
      simpa using (hasDerivAt_id t).mul_const c
    have hquadratic : HasDerivAt (fun s : ℝ => s ^ 2 * q) (2 * t * q) t := by
      simpa using ((hasDerivAt_id t).pow 2).mul_const q
    convert ((hderiv t).sub hlinear).sub hquadratic using 1 <;> try rfl
  let M := 2 * (L : ℝ) * ‖v‖ ^ 2
  let augmented := model + fun t : ℝ => t * M
  have haug_deriv (t : ℝ) : HasDerivAt augmented
      (fderiv ℝ f (x + t • v) v - c -
        2 * t * q + M) t := by
    have hshift : HasDerivAt (fun s : ℝ => s * M) M t := by
      simpa using (hasDerivAt_id t).mul_const M
    simpa only [augmented] using (hmodel_deriv t).add hshift
  have haug_range : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ deriv augmented t ∧ deriv augmented t ≤ M := by
    intro t ht
    rw [(haug_deriv t).deriv]
    have hbound := (abs_le.mp (habs t ht))
    have hcoef : 0 ≤ (L : ℝ) * ‖v‖ ^ 2 :=
      mul_nonneg (NNReal.coe_nonneg L) (sq_nonneg ‖v‖)
    have htbound : (L : ℝ) * t * ‖v‖ ^ 2 ≤ (L : ℝ) * ‖v‖ ^ 2 := by
      calc
        (L : ℝ) * t * ‖v‖ ^ 2 = t * ((L : ℝ) * ‖v‖ ^ 2) := by ring
        _ ≤ 1 * ((L : ℝ) * ‖v‖ ^ 2) :=
          mul_le_mul_of_nonneg_right ht.2 hcoef
        _ = (L : ℝ) * ‖v‖ ^ 2 := one_mul _
    simp only [inner_sub_left, inner_gradient_left] at hbound
    dsimp [c, q]
    dsimp [M]
    constructor <;> linarith
  have hmean : ‖augmented 1 - augmented 0‖ ≤ M * ‖(1 : ℝ) - 0‖ :=
    (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun t ht => (haug_deriv t).differentiableAt)
      (fun t ht => by
        have hrange := haug_range t ht
        rw [(haug_deriv t).deriv] at hrange
        rw [(haug_deriv t).deriv, Real.norm_eq_abs, abs_of_nonneg hrange.1]
        exact hrange.2)
      (by norm_num) (by norm_num)
  have hend : augmented 1 - augmented 0 ≤ M := by
    calc
      augmented 1 - augmented 0 ≤ ‖augmented 1 - augmented 0‖ := by
        rw [Real.norm_eq_abs]
        exact le_abs_self _
      _ ≤ M * ‖(1 : ℝ) - 0‖ := hmean
      _ = M := by norm_num
  dsimp [augmented, model] at hend
  simp only [zero_smul, add_zero, one_smul, zero_mul, one_mul, zero_pow,
    one_pow, sub_zero] at hend
  have hxy : x + v = y := by
    dsimp [v]
    abel
  rw [hxy] at hend
  dsimp [M, q, c, v] at hend ⊢
  rw [inner_gradient_left]
  linarith

@[blueprint "lem:clipped-sgd-descent-telescope"
  (statement := /-- Let $(\Omega,\mathcal A,\mu)$ be a probability space with a
  filtration $(\mathcal F_k)_{k\in\mathbb N}$, let $d\in\mathbb N$, and let
  $f:\mathbb R^d\to\mathbb R$ and
  $x_k,g_k,b_k,u_k:\Omega\to\mathbb R^d$ be given for every $k\in\mathbb N$.
  Fix $G,p,\sigma\in\mathbb R$ and $L\in\mathbb R_{\geq0}$.  Assume
  \cref{def:nonconvex-cost-assumptions,def:clipped-sgd-run} and that the
  bias--centered decomposition $(b_k,u_k)$ satisfies
  \cref{def:has-adapted-clipping-estimates}.  Then there exist
  $x_0\in\mathbb R^d$ and $f_{\mathrm{low}}\in\mathbb R$ such that
  $f_{\mathrm{low}}\leq f(y)$ for every $y\in\mathbb R^d$ and, for every
  $n\in\mathbb N$, the following inequality holds $\mu$-almost surely:
  \[
  \begin{split}
    \left(\sum_{k<n}\alpha_k\right)F_n
    \leq{}& f(x_0)-f_{\mathrm{low}}
      +4G\sigma^p\sum_{k<n}\alpha_k\gamma_k^{1-p}\\
      &+\frac L2\sum_{k<n}\alpha_k^2\gamma_k^2
      +\sum_{k<n}
        \langle-\alpha_k\nabla f(x_k),u_k\rangle .
  \end{split}
  \]
  Here $\alpha_k$, $\gamma_k$, and $F_n$ are the zero-based quantities from
  \cref{def:clipped-step-size,def:clipping-radius,def:best-iterate-gradient-squared}. -/)
  (proof := /-- The bounded-below clause in
  \cref{def:nonconvex-cost-assumptions} supplies $f_{\mathrm{low}}$, and the
  deterministic-initialization clause in \cref{def:clipped-sgd-run} supplies
  $x_0$.  Fix $n\in\mathbb N$ and intersect the almost-sure update,
  decomposition, and bias-bound events over the finite set $0\leq k<n$.
  The quadratic upper bound
  \cref{lem:lipschitz-gradient-quadratic-upper-local} gives, on this event and
  at every update,
  \[
    f(x_{k+1})\leq f(x_k)
      -\alpha_k\langle\nabla f(x_k),
        \nabla f(x_k)+b_k+u_k\rangle
      +\frac L2\alpha_k^2\gamma_k^2.
  \]
  Indeed, the update identity comes from \cref{def:clipped-sgd-run}, the
  decomposition from \cref{def:has-adapted-clipping-estimates}, and
  \cref{lem:clipped-vector-norm-le-radius-local} gives
  $\lVert\operatorname{clip}_{\gamma_k}(g_k)\rVert\leq\gamma_k$.
  Since $\lVert\nabla f(x_k)\rVert\leq G$ and
  $\lVert b_k\rVert\leq4\sigma^p\gamma_k^{1-p}$, Cauchy--Schwarz bounds the bias
  contribution by $4G\sigma^p\alpha_k\gamma_k^{1-p}$.  Sum from $k=0$ to
  $n-1$, telescope the function values, use
  $f(x_n)\geq f_{\mathrm{low}}$, and use
  $F_n\leq\lVert\nabla f(x_k)\rVert^2$ for every $k<n$.  These substitutions give
  precisely the asserted inequality. -/)
  (title := /-- Descent telescope for clipped stochastic gradient descent -/)
  (latexEnv := "lemma")]
lemma clipped_sgd_descent_telescope
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    {d : ℕ} (filtration : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x g bias centered : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (G : ℝ) (L : NNReal) (p σ : ℝ)
    (hcost : nonconvex_cost_assumptions f G L)
    (hrun : clipped_sgd_run μ filtration x g G p)
    (hest : has_adapted_clipping_estimates μ filtration f x g bias centered G p σ) :
    ∃ x₀ : EuclideanSpace ℝ (Fin d), ∃ f_lower : ℝ,
      (∀ y, f_lower ≤ f y) ∧
      ∀ n, ∀ᵐ ω ∂μ,
        (∑ k ∈ Finset.range n, clipped_step_size p k) *
            best_iterate_gradient_squared f x n ω ≤
          f x₀ - f_lower +
          4 * G * Real.rpow σ p *
            (∑ k ∈ Finset.range n,
              clipped_step_size p k *
                Real.rpow (clipping_radius G p k) (1 - p)) +
          ((L : ℝ) / 2) *
            (∑ k ∈ Finset.range n,
              (clipped_step_size p k) ^ 2 * (clipping_radius G p k) ^ 2) +
          ∑ k ∈ Finset.range n,
            inner ℝ
              (-(clipped_step_size p k) • gradient f (x k ω))
              (centered k ω) := by
  rcases hcost with ⟨hG, hbdd, hdiff, hgrad, hLip⟩
  rcases hrun with ⟨⟨x₀, hx₀⟩, _, hupdate⟩
  rcases hest with ⟨⟨hdecomp, hbias, _⟩, _, _, _⟩
  rcases hbdd with ⟨f_lower, hf_lower⟩
  refine ⟨x₀, f_lower, ?_, ?_⟩
  · intro y
    exact hf_lower ⟨y, rfl⟩
  · intro n
    have hupdates : ∀ᵐ ω ∂μ, ∀ k ∈ Finset.range n,
        x (k + 1) ω = x k ω -
          clipped_step_size p k •
            clipped_vector (clipping_radius G p k) (g k ω) :=
      (Filter.eventually_all_finset (Finset.range n)).2 fun k _ => hupdate k
    have hdecomps : ∀ᵐ ω ∂μ, ∀ k ∈ Finset.range n,
        clipped_vector (clipping_radius G p k) (g k ω) =
          gradient f (x k ω) + bias k ω + centered k ω :=
      (Filter.eventually_all_finset (Finset.range n)).2 fun k _ => hdecomp k
    have hbiases : ∀ᵐ ω ∂μ, ∀ k ∈ Finset.range n,
        ‖bias k ω‖ ≤ 4 * Real.rpow σ p *
          Real.rpow (clipping_radius G p k) (1 - p) :=
      (Filter.eventually_all_finset (Finset.range n)).2 fun k _ => hbias k
    filter_upwards [hx₀, hupdates, hdecomps, hbiases] with ω hx₀ω hupdateω
      hdecompω hbiasω
    have hstep : ∀ k ∈ Finset.range n,
        clipped_step_size p k * ‖gradient f (x k ω)‖ ^ 2 ≤
          f (x k ω) - f (x (k + 1) ω) +
          4 * G * Real.rpow σ p *
            (clipped_step_size p k *
              Real.rpow (clipping_radius G p k) (1 - p)) +
          ((L : ℝ) / 2) *
            ((clipped_step_size p k) ^ 2 *
              (clipping_radius G p k) ^ 2) +
          inner ℝ
            (-(clipped_step_size p k) • gradient f (x k ω))
            (centered k ω) := by
      intro k hk
      let α := clipped_step_size p k
      let γ := clipping_radius G p k
      let cvec := clipped_vector γ (g k ω)
      let gradv := gradient f (x k ω)
      let bv := bias k ω
      let uv := centered k ω
      have hα : 0 ≤ α := by
        dsimp [α, clipped_step_size]
        positivity
      have hγ : 0 ≤ γ := by
        dsimp [γ, clipping_radius]
        split <;> positivity
      have hcnorm : ‖cvec‖ ≤ γ :=
        clipped_vector_norm_le_radius_local hγ (g k ω)
      have hcnormsq : α ^ 2 * ‖cvec‖ ^ 2 ≤ α ^ 2 * γ ^ 2 := by
        have hsquare : ‖cvec‖ ^ 2 ≤ γ ^ 2 := by nlinarith [norm_nonneg cvec]
        exact mul_le_mul_of_nonneg_left hsquare (sq_nonneg α)
      have hbbound : ‖bv‖ ≤
          4 * Real.rpow σ p * Real.rpow γ (1 - p) := by
        simpa [bv, γ] using hbiasω k hk
      have hgbound : ‖gradv‖ ≤ G := by
        simpa [gradv] using hgrad (x k ω)
      have hbias_inner : -α * inner ℝ gradv bv ≤
          4 * G * Real.rpow σ p *
            (α * Real.rpow γ (1 - p)) := by
        have hinner : -inner ℝ gradv bv ≤ ‖gradv‖ * ‖bv‖ :=
          (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
        have hprod : ‖gradv‖ * ‖bv‖ ≤
            G * (4 * Real.rpow σ p * Real.rpow γ (1 - p)) :=
          mul_le_mul hgbound hbbound (norm_nonneg bv) hG.le
        have := mul_le_mul_of_nonneg_left (hinner.trans hprod) hα
        nlinarith
      have hsmooth := lipschitz_gradient_quadratic_upper_local
        f L hdiff hLip (x k ω) (x (k + 1) ω)
      rw [hupdateω k hk] at hsmooth
      have hsub :
          (x k ω - α • cvec) - x k ω = -α • cvec := by
        module
      rw [hsub] at hsmooth
      have hcdecomp : cvec = gradv + bv + uv := by
        simpa [cvec, gradv, bv, uv, γ] using hdecompω k hk
      have hinner_decomp : inner ℝ gradv cvec =
          ‖gradv‖ ^ 2 + inner ℝ gradv bv + inner ℝ gradv uv := by
        rw [hcdecomp]
        simp [inner_add_right, real_inner_self_eq_norm_sq]
      change f (x k ω - α • cvec) ≤
        f (x k ω) + inner ℝ gradv (-α • cvec) +
          ((L : ℝ) / 2) * ‖-α • cvec‖ ^ 2 at hsmooth
      have hsmooth_base : f (x k ω - α • cvec) ≤
          f (x k ω) - α * inner ℝ gradv cvec +
            ((L : ℝ) / 2) * (α ^ 2 * ‖cvec‖ ^ 2) := by
        have hs := hsmooth
        simp only [inner_smul_right, neg_mul, norm_smul, Real.norm_eq_abs,
          abs_neg, abs_of_nonneg hα, mul_pow] at hs
        nlinarith
      rw [hinner_decomp] at hsmooth_base
      have hsmooth' : f (x k ω - α • cvec) ≤
          f (x k ω) - α *
              (‖gradv‖ ^ 2 + inner ℝ gradv bv + inner ℝ gradv uv) +
            ((L : ℝ) / 2) * (α ^ 2 * ‖cvec‖ ^ 2) := by
        nlinarith [hsmooth_base]
      have hL : 0 ≤ (L : ℝ) / 2 := by positivity
      have hsmooth_bound : f (x k ω - α • cvec) ≤
          f (x k ω) - α *
              (‖gradv‖ ^ 2 + inner ℝ gradv bv + inner ℝ gradv uv) +
            ((L : ℝ) / 2) * (α ^ 2 * γ ^ 2) :=
        by
          have hquad := mul_le_mul_of_nonneg_left hcnormsq hL
          linarith
      dsimp [α, γ, gradv, bv, uv, cvec] at hsmooth_bound hbias_inner ⊢
      rw [hupdateω k hk]
      simp only [inner_neg_left, inner_smul_left, starRingEnd_apply,
        TrivialStar.star_trivial, neg_mul]
      linarith
    have hbest : ∀ k ∈ Finset.range n,
        best_iterate_gradient_squared f x n ω ≤ ‖gradient f (x k ω)‖ ^ 2 := by
      intro k hk
      unfold best_iterate_gradient_squared
      rw [dif_pos ⟨k, hk⟩]
      exact Finset.inf'_le (fun j => ‖gradient f (x j ω)‖ ^ 2) hk
    have hweighted :
        (∑ k ∈ Finset.range n, clipped_step_size p k) *
            best_iterate_gradient_squared f x n ω ≤
          ∑ k ∈ Finset.range n,
            clipped_step_size p k * ‖gradient f (x k ω)‖ ^ 2 := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun k hk =>
        mul_le_mul_of_nonneg_left (hbest k hk) (by
          unfold clipped_step_size
          exact (Real.rpow_pos_of_pos (by positivity) _).le)
    have hsum := Finset.sum_le_sum hstep
    have htel : f (x 0 ω) - f (x n ω) ≤ f x₀ - f_lower := by
      rw [hx₀ω]
      exact sub_le_sub_left (hf_lower ⟨x n ω, rfl⟩) _
    calc
      (∑ k ∈ Finset.range n, clipped_step_size p k) *
          best_iterate_gradient_squared f x n ω ≤
        ∑ k ∈ Finset.range n,
          clipped_step_size p k * ‖gradient f (x k ω)‖ ^ 2 := hweighted
      _ ≤ ∑ k ∈ Finset.range n,
          (f (x k ω) - f (x (k + 1) ω) +
            4 * G * Real.rpow σ p *
              (clipped_step_size p k *
                Real.rpow (clipping_radius G p k) (1 - p)) +
            ((L : ℝ) / 2) *
              ((clipped_step_size p k) ^ 2 *
                (clipping_radius G p k) ^ 2) +
            inner ℝ
              (-(clipped_step_size p k) • gradient f (x k ω))
              (centered k ω)) := hsum
      _ ≤ f x₀ - f_lower +
          4 * G * Real.rpow σ p *
            (∑ k ∈ Finset.range n,
              clipped_step_size p k *
                Real.rpow (clipping_radius G p k) (1 - p)) +
          ((L : ℝ) / 2) *
            (∑ k ∈ Finset.range n,
              (clipped_step_size p k) ^ 2 *
                (clipping_radius G p k) ^ 2) +
          ∑ k ∈ Finset.range n,
            inner ℝ
              (-(clipped_step_size p k) • gradient f (x k ω))
              (centered k ω) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_add_distrib, Finset.sum_range_sub', Finset.mul_sum,
          Finset.mul_sum]
        linarith

@[blueprint "lem:heavy-tail-schedule-speed-local"
  (statement := /-- If $1<p<2$, then the sequence
  $t^{4(p-1)/(3p-2)}/\log t$ is eventually positive and tends to $+\infty$. -/)
  (proof := /-- The exponent $4(p-1)/(3p-2)$ is positive.  For half of this
  exponent, the standard power bound on the logarithm shows that the displayed
  quotient eventually dominates a positive multiple of a positive power of
  $t$, which tends to $+\infty$. -/)
  (title := /-- Positivity and divergence of the heavy-tail speed -/)
  (latexEnv := "lemma")]
lemma heavy_tail_schedule_speed_local (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    (∀ᶠ t in Filter.atTop, 0 < heavy_tail_ldp_speed p t) ∧
      Filter.Tendsto (heavy_tail_ldp_speed p) Filter.atTop Filter.atTop := by
  have hden : 0 < 3 * p - 2 := by linarith
  let s : ℝ := 4 * (p - 1) / (3 * p - 2)
  have hs : 0 < s := by
    dsimp [s]
    positivity
  let r : ℝ := s / 2
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hsr : s = r + r := by
    dsimp [r]
    ring
  have hpos : ∀ᶠ t : ℕ in Filter.atTop, 0 < heavy_tail_ldp_speed p t := by
    filter_upwards [Filter.eventually_gt_atTop 1] with t ht
    unfold heavy_tail_ldp_speed
    have ht' : (1 : ℝ) < t := by exact_mod_cast ht
    exact div_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.log_pos ht')
  refine ⟨hpos, ?_⟩
  have hpow : Filter.Tendsto (fun t : ℕ => Real.rpow (t : ℝ) r)
      Filter.atTop Filter.atTop :=
    (_root_.tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop
  have hlower : Filter.Tendsto (fun t : ℕ => r * Real.rpow (t : ℝ) r)
      Filter.atTop Filter.atTop := hpow.const_mul_atTop hr
  apply Filter.tendsto_atTop_mono' Filter.atTop _ hlower
  filter_upwards [Filter.eventually_gt_atTop 1] with t ht
  have ht' : (1 : ℝ) < t := by exact_mod_cast ht
  have ht0 : 0 < (t : ℝ) := by positivity
  have hlog : 0 < Real.log (t : ℝ) := Real.log_pos ht'
  have hbound := Real.log_natCast_le_rpow_div t hr
  have hmul : r * Real.log (t : ℝ) ≤ Real.rpow (t : ℝ) r := by
    simpa [mul_comm] using (le_div_iff₀ hr).mp hbound
  unfold heavy_tail_ldp_speed
  change r * Real.rpow (t : ℝ) r ≤ Real.rpow (t : ℝ) s / Real.log (t : ℝ)
  rw [le_div_iff₀ hlog, hsr]
  simp only [Real.rpow_eq_pow, Real.rpow_add ht0 r r]
  have hmul' : r * Real.log (t : ℝ) ≤ (t : ℝ) ^ r := by
    simpa only [Real.rpow_eq_pow] using hmul
  calc
    r * (t : ℝ) ^ r * Real.log (t : ℝ) =
        (t : ℝ) ^ r * (r * Real.log (t : ℝ)) := by ring
    _ ≤ (t : ℝ) ^ r * (t : ℝ) ^ r :=
      mul_le_mul_of_nonneg_left hmul' (Real.rpow_pos_of_pos ht0 r).le

@[blueprint "lem:heavy-tail-schedule-variance-term-local"
  (statement := /-- If $1<p<2$ and $G>0$, then for every $k\in\mathbb N$,
  \[
    \alpha_k^2\gamma_k^2=\frac{4G^2}{k+2}.
  \] -/)
  (proof := /-- Expand \cref{def:clipped-step-size,def:clipping-radius}.  Since
  $p\ne2$, the power-law branch of the radius applies.  Multiplication of real
  powers and the identity
  $-2p/(3p-2)+(2-p)/(3p-2)=-1$ give the formula. -/)
  (title := /-- Exact variance weight below the second-moment threshold -/)
  (latexEnv := "lemma")]
lemma heavy_tail_schedule_variance_term_local (p G : ℝ) (hp1 : 1 < p)
    (hp2 : p < 2) (hG : 0 < G) (k : ℕ) :
    (clipped_step_size p k) ^ 2 * (clipping_radius G p k) ^ 2 =
      4 * G ^ 2 / (k + 2 : ℕ) := by
  have hne : p ≠ 2 := ne_of_lt hp2
  have hden : 3 * p - 2 ≠ 0 := by linarith
  have hden' : 6 * p - 4 ≠ 0 := by linarith
  have hk : 0 < (((k + 2 : ℕ) : ℝ)) := by positivity
  unfold clipped_step_size clipping_radius
  rw [if_neg hne]
  simp only [Real.rpow_eq_pow, pow_two]
  calc
    (((k + 2 : ℕ) : ℝ) ^ (-p / (3 * p - 2)) *
          ((k + 2 : ℕ) : ℝ) ^ (-p / (3 * p - 2))) *
        ((2 * G * ((k + 2 : ℕ) : ℝ) ^ ((2 - p) / (6 * p - 4))) *
          (2 * G * ((k + 2 : ℕ) : ℝ) ^ ((2 - p) / (6 * p - 4)))) =
        4 * (G * G) *
          ((((k + 2 : ℕ) : ℝ) ^ (-p / (3 * p - 2)) *
              ((k + 2 : ℕ) : ℝ) ^ (-p / (3 * p - 2))) *
            (((k + 2 : ℕ) : ℝ) ^ ((2 - p) / (6 * p - 4)) *
              ((k + 2 : ℕ) : ℝ) ^ ((2 - p) / (6 * p - 4)))) := by ring
    _ = 4 * (G * G) *
        (((k + 2 : ℕ) : ℝ) ^
          ((-p / (3 * p - 2) + -p / (3 * p - 2)) +
            ((2 - p) / (6 * p - 4) + (2 - p) / (6 * p - 4)))) := by
      rw [← Real.rpow_add hk, ← Real.rpow_add hk, ← Real.rpow_add hk]
    _ = 4 * (G * G) * (((k + 2 : ℕ) : ℝ) ^ (-1 : ℝ)) := by
      congr 2
      have hc : (3 * p - 2) * (3 * p - 2)⁻¹ = 1 := mul_inv_cancel₀ hden
      have hc' : (6 * p - 4) * (6 * p - 4)⁻¹ = 1 := mul_inv_cancel₀ hden'
      simp only [div_eq_mul_inv]
      nlinarith
    _ = 4 * (G * G) / (k + 2 : ℕ) := by
      rw [Real.rpow_neg_one]
      rfl

@[blueprint "lem:heavy-tail-schedule-reciprocal-sum-local"
  (statement := /-- For every $n\in\mathbb N$,
  \[
    \sum_{k<n}\frac1{k+2}\leq\log(n+1).
  \] -/)
  (proof := /-- Induct on $n$.  The induction step follows from
  $1-x^{-1}\leq\log x$ at $x=(n+2)/(n+1)$, which gives
  $1/(n+2)\leq\log(n+2)-\log(n+1)$. -/)
  (title := /-- A logarithmic bound for the shifted harmonic sum -/)
  (latexEnv := "lemma")]
lemma heavy_tail_schedule_reciprocal_sum_local (n : ℕ) :
    (∑ k ∈ Finset.range n, (1 : ℝ) / (k + 2 : ℕ)) ≤
      Real.log (n + 1 : ℕ) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hpos : 0 < ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := by positivity
      have hlog := Real.one_sub_inv_le_log_of_pos hpos
      rw [Real.log_div (by positivity) (by positivity)] at hlog
      have hcalc : 1 - (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))⁻¹ =
          (1 : ℝ) / (n + 2 : ℕ) := by
        field_simp
        norm_num
      have hstep : (1 : ℝ) / (n + 2 : ℕ) ≤
          Real.log (n + 2 : ℕ) - Real.log (n + 1 : ℕ) := by
        rw [← hcalc]
        exact hlog
      linarith

@[blueprint "lem:weighted-average-tendsto-zero-local"
  (statement := /-- Let $w_k>0$ and $z_k\geq0$.  If
  $\sum_{k<n}w_k\to+\infty$ and $z_k\to0$, then
  \[
    \frac{\sum_{k<n}w_kz_k}{\sum_{k<n}w_k}\longrightarrow0.
  \] -/)
  (proof := /-- Fix $\varepsilon>0$ and choose $N$ so that
  $z_k<\varepsilon/2$ for $k\geq N$.  Split the numerator at $N$.  The tail is
  at most $(\varepsilon/2)\sum_{k<n}w_k$, while the fixed prefix divided by
  the diverging denominator is eventually smaller than $\varepsilon/2$. -/)
  (title := /-- Vanishing of a positive weighted average -/)
  (latexEnv := "lemma")]
lemma weighted_average_tendsto_zero_local (w z : ℕ → ℝ)
    (hw : ∀ k, 0 < w k) (hz0 : ∀ k, 0 ≤ z k)
    (hW : Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, w k)
      Filter.atTop Filter.atTop)
    (hz : Filter.Tendsto z Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => (∑ k ∈ Finset.range n, w k * z k) /
        (∑ k ∈ Finset.range n, w k)) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hz) (ε / 2) (by positivity)
  let C := ∑ k ∈ Finset.range N₀, w k * z k
  have hC : 0 ≤ C := Finset.sum_nonneg fun k _ =>
    mul_nonneg (hw k).le (hz0 k)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    (hW.eventually (Filter.eventually_gt_atTop (2 * C / ε)))
  refine ⟨max (max N₀ 1) N₁, ?_⟩
  intro n hn
  have hN0n : N₀ ≤ n := le_trans (le_max_left N₀ 1)
    (le_trans (le_max_left (max N₀ 1) N₁) hn)
  have h1n : 1 ≤ n := le_trans (le_max_right N₀ 1)
    (le_trans (le_max_left (max N₀ 1) N₁) hn)
  have hN1n : N₁ ≤ n := le_trans (le_max_right (max N₀ 1) N₁) hn
  let W := ∑ k ∈ Finset.range n, w k
  have hWlarge : 2 * C / ε < W := hN₁ n hN1n
  have hWpos : 0 < W := by
    dsimp [W]
    apply Finset.sum_pos'
    · intro k hk
      exact (hw k).le
    · exact ⟨0, Finset.mem_range.mpr h1n, hw 0⟩
  have htail : (∑ k ∈ Finset.Ico N₀ n, w k * z k) ≤
      (ε / 2) * ∑ k ∈ Finset.Ico N₀ n, w k := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hkN : N₀ ≤ k := (Finset.mem_Ico.mp hk).1
    have hzkdist := hN₀ k hkN
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hz0 k)] at hzkdist
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hzkdist.le (hw k).le
  have htailW : (∑ k ∈ Finset.Ico N₀ n, w k * z k) ≤
      (ε / 2) * W := by
    refine htail.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    dsimp [W]
    rw [← Finset.sum_range_add_sum_Ico w hN0n]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun k _ => (hw k).le)
  have hnum : (∑ k ∈ Finset.range n, w k * z k) ≤ C + (ε / 2) * W := by
    rw [← Finset.sum_range_add_sum_Ico (fun k => w k * z k) hN0n]
    simpa [C, add_comm] using add_le_add_left htailW C
  have hprefix : C / W < ε / 2 := by
    rw [div_lt_iff₀ hWpos]
    have hε0 : 0 < ε := hε
    have := mul_lt_mul_of_pos_right hWlarge hε0
    field_simp at this ⊢
    nlinarith
  have hratio_nonneg : 0 ≤ (∑ k ∈ Finset.range n, w k * z k) / W :=
    div_nonneg (Finset.sum_nonneg fun k _ => mul_nonneg (hw k).le (hz0 k)) hWpos.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hratio_nonneg]
  calc
    (∑ k ∈ Finset.range n, w k * z k) / W ≤
        (C + (ε / 2) * W) / W := div_le_div_of_nonneg_right hnum hWpos.le
    _ = C / W + ε / 2 := by field_simp
    _ < ε / 2 + ε / 2 := by
      simpa [add_comm] using add_lt_add_right hprefix (ε / 2)
    _ = ε := by ring

@[blueprint "lem:heavy-tail-step-sum-diverges-local"
  (statement := /-- If $1<p<2$, then the partial sums of the clipped-SGD step
  sizes diverge to $+\infty$:
  \[
    \sum_{k<n}(k+2)^{-p/(3p-2)}\longrightarrow+\infty.
  \] -/)
  (proof := /-- Put $a=p/(3p-2)$ and $q=1-a>0$.  Every summand with $k<n$
  is at least $(n+1)^{-a}$.  Since $a\leq1$ and $n+1\leq2n$ for $n\geq1$,
  the whole sum is bounded below by
  $\frac12 n^q$, which tends to $+\infty$. -/)
  (title := /-- Divergence of the cumulative heavy-tail step size -/)
  (latexEnv := "lemma")]
lemma heavy_tail_step_sum_diverges_local (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, clipped_step_size p k)
      Filter.atTop Filter.atTop := by
  have hden : 0 < 3 * p - 2 := by linarith
  let a : ℝ := p / (3 * p - 2)
  let q : ℝ := 1 - a
  have ha0 : 0 < a := by
    dsimp [a]
    positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    rw [div_le_one hden]
    linarith
  have hq : 0 < q := by
    dsimp [q, a]
    rw [sub_pos, div_lt_one hden]
    linarith
  have hpow : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) * ((n : ℝ) ^ q))
      Filter.atTop Filter.atTop :=
    ((_root_.tendsto_rpow_atTop hq).comp tendsto_natCast_atTop_atTop).const_mul_atTop
      (by norm_num)
  apply Filter.tendsto_atTop_mono' Filter.atTop _ hpow
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hterm : ∀ k ∈ Finset.range n,
      (((n + 1 : ℕ) : ℝ) ^ (-a)) ≤ clipped_step_size p k := by
    intro k hk
    unfold clipped_step_size
    simp only [Real.rpow_eq_pow]
    rw [show -p / (3 * p - 2) = -a by dsimp [a]; ring]
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith [ha0])
    exact_mod_cast Nat.add_le_add_right (Finset.mem_range.mp hk) 1
  have hsum : (n : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (-a)) ≤
      ∑ k ∈ Finset.range n, clipped_step_size p k := by
    calc
      (n : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (-a)) =
          ∑ k ∈ Finset.range n, (((n + 1 : ℕ) : ℝ) ^ (-a)) := by simp
      _ ≤ ∑ k ∈ Finset.range n, clipped_step_size p k :=
        Finset.sum_le_sum hterm
  have hbase : ((2 : ℝ) * n) ^ (-a) ≤ (((n + 1 : ℕ) : ℝ) ^ (-a)) := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith [ha0])
    exact_mod_cast (show n + 1 ≤ 2 * n by omega)
  have htwo : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-a) := by
    convert Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
      (show (-1 : ℝ) ≤ -a by linarith) using 1 <;> norm_num
  have hlower : (1 / 2 : ℝ) * ((n : ℝ) ^ q) ≤
      (n : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (-a)) := by
    have hmul := mul_le_mul_of_nonneg_left hbase hn0.le
    calc
      (1 / 2 : ℝ) * ((n : ℝ) ^ q) =
          (n : ℝ) * ((1 / 2 : ℝ) * ((n : ℝ) ^ (-a))) := by
        rw [show q = 1 + -a by dsimp [q]; ring, Real.rpow_add hn0 1 (-a)]
        norm_num
        ring
      _ ≤ (n : ℝ) * (((2 : ℝ) ^ (-a)) * ((n : ℝ) ^ (-a))) := by
        gcongr
      _ = (n : ℝ) * (((2 : ℝ) * n) ^ (-a)) := by
        rw [Real.mul_rpow (by norm_num) hn0.le]
      _ ≤ (n : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (-a)) := hmul
  exact hlower.trans hsum

@[blueprint "lem:heavy-tail-schedule-smooth-term-local"
  (statement := /-- If $1<p<2$ and $G>0$, then for every $k\in\mathbb N$,
  \[
    \alpha_k\gamma_k^2
      =4G^2(k+2)^{-2(p-1)/(3p-2)}.
  \] -/)
  (proof := /-- Expand \cref{def:clipped-step-size,def:clipping-radius}, use
  the power-law radius branch, combine the real powers, and simplify their
  exponent. -/)
  (title := /-- Exact normalized smoothness weight -/)
  (latexEnv := "lemma")]
lemma heavy_tail_schedule_smooth_term_local (p G : ℝ) (hp1 : 1 < p)
    (hp2 : p < 2) (hG : 0 < G) (k : ℕ) :
    clipped_step_size p k * (clipping_radius G p k) ^ 2 =
      4 * G ^ 2 * Real.rpow ((k + 2 : ℕ) : ℝ)
        (-2 * (p - 1) / (3 * p - 2)) := by
  have hne : p ≠ 2 := ne_of_lt hp2
  have hden : 3 * p - 2 ≠ 0 := by linarith
  have hden' : 6 * p - 4 ≠ 0 := by linarith
  have hk : 0 < (((k + 2 : ℕ) : ℝ)) := by positivity
  unfold clipped_step_size clipping_radius
  rw [if_neg hne]
  simp only [Real.rpow_eq_pow, pow_two]
  calc
    ((k + 2 : ℕ) : ℝ) ^ (-p / (3 * p - 2)) *
        ((2 * G * ((k + 2 : ℕ) : ℝ) ^ ((2 - p) / (6 * p - 4))) *
          (2 * G * ((k + 2 : ℕ) : ℝ) ^ ((2 - p) / (6 * p - 4)))) =
      4 * (G * G) *
        (((k + 2 : ℕ) : ℝ) ^ (-p / (3 * p - 2)) *
          (((k + 2 : ℕ) : ℝ) ^ ((2 - p) / (6 * p - 4)) *
            ((k + 2 : ℕ) : ℝ) ^ ((2 - p) / (6 * p - 4)))) := by ring
    _ = 4 * (G * G) * (((k + 2 : ℕ) : ℝ) ^
        (-p / (3 * p - 2) +
          ((2 - p) / (6 * p - 4) + (2 - p) / (6 * p - 4)))) := by
      rw [← Real.rpow_add hk, ← Real.rpow_add hk]
    _ = 4 * (G * G) * (((k + 2 : ℕ) : ℝ) ^
        (-2 * (p - 1) / (3 * p - 2))) := by
      congr 2
      have hc : (3 * p - 2) * (3 * p - 2)⁻¹ = 1 := mul_inv_cancel₀ hden
      have hc' : (6 * p - 4) * (6 * p - 4)⁻¹ = 1 := mul_inv_cancel₀ hden'
      simp only [div_eq_mul_inv]
      nlinarith
    _ = 4 * (G * G) * Real.rpow ((k + 2 : ℕ) : ℝ)
        (-2 * (p - 1) / (3 * p - 2)) := by rw [Real.rpow_eq_pow]

@[blueprint "lem:heavy-tail-schedule-negligible-ratios-local"
  (statement := /-- If $1<p<2$ and $G>0$, then both deterministic schedule
  sums are negligible relative to the cumulative step size:
  \[
  \frac{\sum_{k<n}\alpha_k\gamma_k^{1-p}}{\sum_{k<n}\alpha_k}\to0,
  \qquad
  \frac{\sum_{k<n}\alpha_k^2\gamma_k^2}{\sum_{k<n}\alpha_k}\to0.
  \] -/)
  (proof := /-- Apply \cref{lem:weighted-average-tendsto-zero-local} with
  weights $w_k=\alpha_k$.  Their partial sums diverge by
  \cref{lem:heavy-tail-step-sum-diverges-local}.  For the first ratio,
  $z_k=\gamma_k^{1-p}\to0$ because $\gamma_k\to+\infty$ and $1-p<0$.
  For the second, \cref{lem:heavy-tail-schedule-smooth-term-local} gives
  $z_k=\alpha_k\gamma_k^2=4G^2(k+2)^{-2(p-1)/(3p-2)}\to0$. -/)
  (title := /-- Negligibility of the bias and smoothness schedules -/)
  (latexEnv := "lemma")]
lemma heavy_tail_schedule_negligible_ratios_local (p G : ℝ) (hp1 : 1 < p)
    (hp2 : p < 2) (hG : 0 < G) :
    Filter.Tendsto
        (fun n => (∑ k ∈ Finset.range n,
          clipped_step_size p k *
            Real.rpow (clipping_radius G p k) (1 - p)) /
          (∑ k ∈ Finset.range n, clipped_step_size p k))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun n => (∑ k ∈ Finset.range n,
          (clipped_step_size p k) ^ 2 * (clipping_radius G p k) ^ 2) /
          (∑ k ∈ Finset.range n, clipped_step_size p k))
        Filter.atTop (nhds 0) := by
  have hden : 0 < 3 * p - 2 := by linarith
  have hα (k : ℕ) : 0 < clipped_step_size p k := by
    unfold clipped_step_size
    exact Real.rpow_pos_of_pos (by positivity) _
  have hγ (k : ℕ) : 0 < clipping_radius G p k := by
    unfold clipping_radius
    rw [if_neg (ne_of_lt hp2)]
    exact mul_pos (mul_pos (by norm_num) hG) (Real.rpow_pos_of_pos (by positivity) _)
  have hW := heavy_tail_step_sum_diverges_local p hp1 hp2
  let b : ℝ := (2 - p) / (6 * p - 4)
  have hb : 0 < b := by
    dsimp [b]
    have : 0 < 6 * p - 4 := by linarith
    positivity
  have hbase : Filter.Tendsto (fun k : ℕ => (((k + 2 : ℕ) : ℝ)))
      Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono' Filter.atTop _ tendsto_natCast_atTop_atTop
    exact Filter.Eventually.of_forall fun k => by norm_num
  have hpow : Filter.Tendsto (fun k : ℕ => (((k + 2 : ℕ) : ℝ) ^ b))
      Filter.atTop Filter.atTop := (_root_.tendsto_rpow_atTop hb).comp hbase
  have hgamma : Filter.Tendsto (fun k => clipping_radius G p k)
      Filter.atTop Filter.atTop := by
    have hscaled : Filter.Tendsto
        (fun k : ℕ => (2 * G) * (((k + 2 : ℕ) : ℝ) ^ b))
        Filter.atTop Filter.atTop :=
      hpow.const_mul_atTop (mul_pos (by norm_num) hG)
    convert hscaled using 1
    funext k
    unfold clipping_radius
    rw [if_neg (ne_of_lt hp2)]
    simp only [Real.rpow_eq_pow]
    rw [show (2 - p) / (6 * p - 4) = b by rfl]
  have hbias : Filter.Tendsto
      (fun k => Real.rpow (clipping_radius G p k) (1 - p))
      Filter.atTop (nhds 0) := by
    have hneg := (_root_.tendsto_rpow_neg_atTop (sub_pos.mpr hp1)).comp hgamma
    convert hneg using 1
    funext k
    rw [Real.rpow_eq_pow]
    congr 1
    ring
  have hbias_ratio := weighted_average_tendsto_zero_local
    (fun k => clipped_step_size p k)
    (fun k => Real.rpow (clipping_radius G p k) (1 - p))
    hα (fun k => (Real.rpow_nonneg (hγ k).le _)) hW hbias
  refine ⟨hbias_ratio, ?_⟩
  let q : ℝ := 2 * (p - 1) / (3 * p - 2)
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hpowneg : Filter.Tendsto (fun k : ℕ => (((k + 2 : ℕ) : ℝ) ^ (-q)))
      Filter.atTop (nhds 0) := (_root_.tendsto_rpow_neg_atTop hq).comp hbase
  have hsmooth : Filter.Tendsto
      (fun k => clipped_step_size p k * (clipping_radius G p k) ^ 2)
      Filter.atTop (nhds 0) := by
    have hconst : Filter.Tendsto
        (fun k : ℕ => (4 * G ^ 2) * (((k + 2 : ℕ) : ℝ) ^ (-q)))
        Filter.atTop (nhds ((4 * G ^ 2) * 0)) :=
      tendsto_const_nhds.mul hpowneg
    simp only [mul_zero] at hconst
    convert hconst using 1
    funext k
    rw [heavy_tail_schedule_smooth_term_local p G hp1 hp2 hG k]
    simp only [Real.rpow_eq_pow]
    rw [show -2 * (p - 1) / (3 * p - 2) = -q by dsimp [q]; ring]
  have hsmooth_ratio := weighted_average_tendsto_zero_local
    (fun k => clipped_step_size p k)
    (fun k => clipped_step_size p k * (clipping_radius G p k) ^ 2)
    hα (fun k => mul_nonneg (hα k).le (sq_nonneg _)) hW hsmooth
  convert hsmooth_ratio using 1
  funext n
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  ring

@[blueprint "lem:heavy-tail-schedule-concentration-scale-local"
  (statement := /-- If $1<p<2$ and $G>0$, put
  $A_n=\sum_{k<n}\alpha_k$ and
  $V_n=\sum_{k<n}\gamma_k^2(\alpha_kG)^2$.  Eventually $V_n>0$ and
  \[
    n_nV_n\leq32G^4A_n^2,
  \]
  where $n_n=n^{4(p-1)/(3p-2)}/\log n$. -/)
  (proof := /-- Every step size is positive and
  $A_n\geq\frac12n^{2(p-1)/(3p-2)}$.  By
  \cref{lem:heavy-tail-schedule-variance-term-local,
  lem:heavy-tail-schedule-reciprocal-sum-local},
  $V_n\leq4G^4\log(n+1)\leq8G^4\log n$ eventually.  Squaring the lower bound
  on $A_n$ and cancelling the positive logarithm gives the claim. -/)
  (title := /-- Comparison of the concentration variance with the LDP speed -/)
  (latexEnv := "lemma")]
lemma heavy_tail_schedule_concentration_scale_local (p G : ℝ) (hp1 : 1 < p)
    (hp2 : p < 2) (hG : 0 < G) :
    ∀ᶠ n : ℕ in Filter.atTop,
      0 < ∑ k ∈ Finset.range n,
          (clipping_radius G p k) ^ 2 * (clipped_step_size p k * G) ^ 2 ∧
      heavy_tail_ldp_speed p n *
          (∑ k ∈ Finset.range n,
            (clipping_radius G p k) ^ 2 * (clipped_step_size p k * G) ^ 2) ≤
        32 * G ^ 4 *
          (∑ k ∈ Finset.range n, clipped_step_size p k) ^ 2 := by
  have hden : 0 < 3 * p - 2 := by linarith
  let a : ℝ := p / (3 * p - 2)
  let q : ℝ := 1 - a
  have ha0 : 0 < a := by
    dsimp [a]
    positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    rw [div_le_one hden]
    linarith
  have hq : 0 < q := by
    dsimp [q, a]
    rw [sub_pos, div_lt_one hden]
    linarith
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have hn1 : 1 ≤ n := hn.trans' (by omega)
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hα (k : ℕ) : 0 < clipped_step_size p k := by
    unfold clipped_step_size
    exact Real.rpow_pos_of_pos (by positivity) _
  have hγ (k : ℕ) : 0 < clipping_radius G p k := by
    unfold clipping_radius
    rw [if_neg (ne_of_lt hp2)]
    exact mul_pos (mul_pos (by norm_num) hG) (Real.rpow_pos_of_pos (by positivity) _)
  let A := ∑ k ∈ Finset.range n, clipped_step_size p k
  let V := ∑ k ∈ Finset.range n,
    (clipping_radius G p k) ^ 2 * (clipped_step_size p k * G) ^ 2
  have hVpos : 0 < V := by
    dsimp [V]
    apply Finset.sum_pos'
    · intro k hk
      positivity
    · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
      have := hγ 0
      have := hα 0
      positivity
  refine ⟨hVpos, ?_⟩
  have hterm : ∀ k ∈ Finset.range n,
      (((n + 1 : ℕ) : ℝ) ^ (-a)) ≤ clipped_step_size p k := by
    intro k hk
    unfold clipped_step_size
    simp only [Real.rpow_eq_pow]
    rw [show -p / (3 * p - 2) = -a by dsimp [a]; ring]
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith [ha0])
    exact_mod_cast Nat.add_le_add_right (Finset.mem_range.mp hk) 1
  have hsum : (n : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (-a)) ≤ A := by
    dsimp [A]
    calc
      (n : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (-a)) =
          ∑ k ∈ Finset.range n, (((n + 1 : ℕ) : ℝ) ^ (-a)) := by simp
      _ ≤ ∑ k ∈ Finset.range n, clipped_step_size p k :=
        Finset.sum_le_sum hterm
  have hbase : ((2 : ℝ) * n) ^ (-a) ≤ (((n + 1 : ℕ) : ℝ) ^ (-a)) := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith [ha0])
    exact_mod_cast (show n + 1 ≤ 2 * n by omega)
  have htwo : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-a) := by
    convert Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
      (show (-1 : ℝ) ≤ -a by linarith) using 1 <;> norm_num
  have hAlower : (1 / 2 : ℝ) * ((n : ℝ) ^ q) ≤ A := by
    have hmul := mul_le_mul_of_nonneg_left hbase hn0.le
    calc
      (1 / 2 : ℝ) * ((n : ℝ) ^ q) =
          (n : ℝ) * ((1 / 2 : ℝ) * ((n : ℝ) ^ (-a))) := by
        rw [show q = 1 + -a by dsimp [q]; ring, Real.rpow_add hn0 1 (-a)]
        norm_num
        ring
      _ ≤ (n : ℝ) * (((2 : ℝ) ^ (-a)) * ((n : ℝ) ^ (-a))) := by
        gcongr
      _ = (n : ℝ) * (((2 : ℝ) * n) ^ (-a)) := by
        rw [Real.mul_rpow (by norm_num) hn0.le]
      _ ≤ (n : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (-a)) := hmul
      _ ≤ A := hsum
  have hApos : 0 < A := lt_of_lt_of_le (mul_pos (by norm_num)
    (Real.rpow_pos_of_pos hn0 q)) hAlower
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hnquad : (((n + 1 : ℕ) : ℝ)) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast (show n + 1 ≤ n ^ 2 by nlinarith)
  have hlogcomp := Real.log_le_log (by positivity : (0 : ℝ) < (n + 1 : ℕ)) hnquad
  rw [Real.log_pow] at hlogcomp
  norm_num at hlogcomp
  have hQ : (∑ k ∈ Finset.range n,
      (clipped_step_size p k) ^ 2 * (clipping_radius G p k) ^ 2) ≤
      8 * G ^ 2 * Real.log (n : ℝ) := by
    calc
      (∑ k ∈ Finset.range n,
          (clipped_step_size p k) ^ 2 * (clipping_radius G p k) ^ 2) =
          ∑ k ∈ Finset.range n, 4 * G ^ 2 / (k + 2 : ℕ) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact heavy_tail_schedule_variance_term_local p G hp1 hp2 hG k
      _ = 4 * G ^ 2 *
          (∑ k ∈ Finset.range n, (1 : ℝ) / (k + 2 : ℕ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ 4 * G ^ 2 * Real.log (n + 1 : ℕ) :=
        mul_le_mul_of_nonneg_left (heavy_tail_schedule_reciprocal_sum_local n)
          (by positivity)
      _ ≤ 8 * G ^ 2 * Real.log (n : ℝ) := by
        calc
          4 * G ^ 2 * Real.log (n + 1 : ℕ) ≤
              4 * G ^ 2 * (2 * Real.log (n : ℝ)) :=
            mul_le_mul_of_nonneg_left (by simpa using hlogcomp)
              (show 0 ≤ 4 * G ^ 2 by positivity)
          _ = 8 * G ^ 2 * Real.log (n : ℝ) := by ring
  have hVupper : V ≤ 8 * G ^ 4 * Real.log (n : ℝ) := by
    calc
      V = G ^ 2 * (∑ k ∈ Finset.range n,
          (clipped_step_size p k) ^ 2 * (clipping_radius G p k) ^ 2) := by
        dsimp [V]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ G ^ 2 * (8 * G ^ 2 * Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hQ (sq_nonneg G)
      _ = 8 * G ^ 4 * Real.log (n : ℝ) := by ring
  have hqexp : 2 * q = 4 * (p - 1) / (3 * p - 2) := by
    dsimp [q, a]
    have hc : (3 * p - 2) * (3 * p - 2)⁻¹ = 1 := mul_inv_cancel₀ hden.ne'
    simp only [div_eq_mul_inv]
    nlinarith
  have hAsq : (1 / 4 : ℝ) * ((n : ℝ) ^ (2 * q)) ≤ A ^ 2 := by
    have hsquare := mul_self_le_mul_self
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hn0.le q)) hAlower
    calc
      (1 / 4 : ℝ) * ((n : ℝ) ^ (2 * q)) =
          ((1 / 2 : ℝ) * ((n : ℝ) ^ q)) ^ 2 := by
        rw [show 2 * q = q + q by ring, Real.rpow_add hn0 q q]
        ring
      _ ≤ A ^ 2 := by simpa [pow_two] using hsquare
  have hspeedV : heavy_tail_ldp_speed p n * V ≤
      8 * G ^ 4 * ((n : ℝ) ^ (2 * q)) := by
    unfold heavy_tail_ldp_speed
    rw [← hqexp]
    calc
      Real.rpow (n : ℝ) (2 * q) / Real.log (n : ℝ) * V ≤
          Real.rpow (n : ℝ) (2 * q) / Real.log (n : ℝ) *
            (8 * G ^ 4 * Real.log (n : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hVupper (div_nonneg
          (Real.rpow_nonneg hn0.le _) hlog.le)
      _ = 8 * G ^ 4 * ((n : ℝ) ^ (2 * q)) := by
        simp only [Real.rpow_eq_pow]
        field_simp
  have hmulA := mul_le_mul_of_nonneg_left hAsq
    (show 0 ≤ 32 * G ^ 4 by positivity)
  exact hspeedV.trans (by nlinarith)

@[blueprint "lem:heavy-tail-schedule-asymptotics"
  (statement := /-- Let $(\Omega,\mathcal A,\mu)$ be a probability space with a
  filtration $(\mathcal F_t)_{t\in\mathbb N}$, let $d\in\mathbb N$, and let
  $f:\mathbb R^d\to\mathbb R$ and
  $x_t,g_t,b_t,u_t:\Omega\to\mathbb R^d$ be given for every $t\in\mathbb N$.
  Fix $G,p,\sigma\in\mathbb R$ and $L\in\mathbb R_{\geq0}$.  Assume
  \cref{def:nonconvex-cost-assumptions,def:heavy-tail-noise-assumptions,
  def:clipped-sgd-run,def:has-adapted-clipping-estimates}, and assume $p<2$.
  Define
  $F_t=\min_{0\leq k<t}\lVert\nabla f(x_k)\rVert^2$, with $F_0=0$, as in
  \cref{def:best-iterate-gradient-squared}.  Then the speed
  $n_t=t^{4(p-1)/(3p-2)}/\log t$ from
  \cref{def:heavy-tail-ldp-speed} is eventually positive and tends to infinity.
  Moreover, for every $y\in\mathbb R$ with $y\geq0$,
  \[
    \limsup_{t\to\infty}\frac{1}{n_t}
      \log\mu\{F_t\geq y\}
      \leq-\frac{y^2}{768G^4}.
  \] -/)
  (proof := /-- By \cref{lem:heavy-tail-schedule-speed-local}, the displayed
  speed is eventually positive and tends to $+\infty$.  Apply
  \cref{lem:clipped-sgd-descent-telescope}, and write
  \[
    A_n=\sum_{k<n}\alpha_k,\quad
    B_n=\sum_{k<n}\alpha_k\gamma_k^{1-p},\quad
    Q_n=\sum_{k<n}\alpha_k^2\gamma_k^2.
  \]
  The step sum $A_n$ tends to $+\infty$ by
  \cref{lem:heavy-tail-step-sum-diverges-local}.  Together with
  \cref{lem:heavy-tail-schedule-negligible-ratios-local}, this implies that the
  deterministic remainder
  \[
    D_n=f(x_0)-f_{\mathrm{low}}+4G\sigma^pB_n+(L/2)Q_n
  \]
  satisfies $D_n/A_n\to0$.

  Fix $y>0$.  Eventually $D_n<A_ny/4$.  Hence the descent telescope shows,
  almost surely, that $F_n\geq y$ implies
  \[
    \frac34A_ny\leq
      \sum_{k<n}\langle-\alpha_k\nabla f(x_k),u_k\rangle.
  \]
  Put $V_n=\sum_{k<n}\gamma_k^2(\alpha_kG)^2$.  By
  \cref{lem:heavy-tail-schedule-concentration-scale-local}, eventually
  $V_n>0$ and $n_nV_n\leq32G^4A_n^2$.  Apply
  \cref{lem:finite-horizon-conditional-mgf} with
  $a_k=-\alpha_k\nabla f(x_k)$ and deterministic bound
  $A_k=\alpha_kG$.  It gives
  \[
    \mu\{F_n\geq y\}
      \leq\exp\!\left(-\frac{(3A_ny/4)^2}{12V_n}\right).
  \]
  Taking the extended logarithm, dividing by the positive speed, and using the
  scale comparison yields the asserted bound with constant $768G^4$.  If
  $y=0$, the logarithm of the probability is at most zero, which proves the
  same inequality. -/)
  (title := /-- One-sided tail asymptotics below the second-moment threshold -/)
  (latexEnv := "lemma")]
lemma heavy_tail_schedule_asymptotics
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    {d : ℕ} (filtration : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x g bias centered : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (G : ℝ) (L : NNReal) (p σ : ℝ)
    (hcost : nonconvex_cost_assumptions f G L)
    (hnoise : heavy_tail_noise_assumptions μ filtration f x g p σ)
    (hrun : clipped_sgd_run μ filtration x g G p)
    (hest : has_adapted_clipping_estimates μ filtration f x g bias centered G p σ)
    (hp2 : p < 2) :
    (∀ᶠ t in Filter.atTop, 0 < heavy_tail_ldp_speed p t) ∧
    Filter.Tendsto (heavy_tail_ldp_speed p) Filter.atTop Filter.atTop ∧
    ∀ y : ℝ, 0 ≤ y →
      Filter.limsup
          (fun t => ENNReal.log
            (μ {ω | y ≤ best_iterate_gradient_squared f x t ω}) /
              (heavy_tail_ldp_speed p t : EReal))
          Filter.atTop
        ≤ -(↑(y ^ 2 / (768 * G ^ 4) : ℝ) : EReal) := by
  have hp1 : 1 < p := hnoise.1
  have hG : 0 < G := hcost.1
  rcases heavy_tail_schedule_speed_local p hp1 hp2 with ⟨hspeed_pos, hspeed_top⟩
  refine ⟨hspeed_pos, hspeed_top, ?_⟩
  rcases clipped_sgd_descent_telescope μ filtration f x g bias centered G L p σ
      hcost hrun hest with ⟨x₀, f_lower, hf_lower, htelescope⟩
  let A : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, clipped_step_size p k
  let B : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n,
    clipped_step_size p k * Real.rpow (clipping_radius G p k) (1 - p)
  let Q : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n,
    (clipped_step_size p k) ^ 2 * (clipping_radius G p k) ^ 2
  let D : ℕ → ℝ := fun n => f x₀ - f_lower +
    4 * G * Real.rpow σ p * B n + ((L : ℝ) / 2) * Q n
  have hA_top : Filter.Tendsto A Filter.atTop Filter.atTop := by
    simpa [A] using heavy_tail_step_sum_diverges_local p hp1 hp2
  have hratios := heavy_tail_schedule_negligible_ratios_local p G hp1 hp2 hG
  have hB_zero : Filter.Tendsto (fun n => B n / A n) Filter.atTop (nhds 0) := by
    simpa [A, B] using hratios.1
  have hQ_zero : Filter.Tendsto (fun n => Q n / A n) Filter.atTop (nhds 0) := by
    simpa [A, Q] using hratios.2
  have hA_inv : Filter.Tendsto A⁻¹ Filter.atTop (nhds 0) := hA_top.inv_tendsto_atTop
  have hconst_zero : Filter.Tendsto (fun n => (f x₀ - f_lower) / A n)
      Filter.atTop (nhds 0) := by
    have hmul : Filter.Tendsto (fun n => (f x₀ - f_lower) * (A⁻¹ n))
        Filter.atTop (nhds ((f x₀ - f_lower) * 0)) := tendsto_const_nhds.mul hA_inv
    simpa [div_eq_mul_inv] using hmul
  have hD_zero : Filter.Tendsto (fun n => D n / A n) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto
        (fun n => (4 * G * Real.rpow σ p) * (B n / A n)) Filter.atTop
        (nhds ((4 * G * Real.rpow σ p) * 0)) :=
      tendsto_const_nhds.mul hB_zero
    have h2 : Filter.Tendsto
        (fun n => ((L : ℝ) / 2) * (Q n / A n)) Filter.atTop
        (nhds (((L : ℝ) / 2) * 0)) :=
      tendsto_const_nhds.mul hQ_zero
    simp only [mul_zero] at h1 h2
    have hadd := (hconst_zero.add h1).add h2
    convert hadd using 1
    · funext n
      dsimp [D]
      field_simp
    · norm_num
  intro y hy
  by_cases hy0 : y = 0
  · subst y
    refine Filter.limsup_le_of_le (h := ?_)
    filter_upwards [hspeed_pos] with n hn
    have hμ : μ {ω | 0 ≤ best_iterate_gradient_squared f x n ω} ≤ 1 := by
      calc
        μ {ω | 0 ≤ best_iterate_gradient_squared f x n ω} ≤ μ Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have hlog : ENNReal.log (μ {ω | 0 ≤ best_iterate_gradient_squared f x n ω}) ≤ 0 := by
      simpa using ENNReal.log_le_log hμ
    have hnc : (0 : EReal) ≤ (heavy_tail_ldp_speed p n : EReal) := by exact_mod_cast hn.le
    simpa using EReal.div_le_div_right_of_nonneg hnc hlog
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  have hDsmall : ∀ᶠ n : ℕ in Filter.atTop, D n / A n < y / 4 :=
    hD_zero.eventually (Iio_mem_nhds (by positivity))
  have hscale := heavy_tail_schedule_concentration_scale_local p G hp1 hp2 hG
  have hrun_meas := hrun.2.1
  have hgrad := hcost.2.2.2.1
  have hLip := hcost.2.2.2.2
  refine Filter.limsup_le_of_le (h := ?_)
  filter_upwards [hDsmall, hscale, hspeed_pos, Filter.eventually_ge_atTop 1]
    with n hDn hscale_n hspeed_n hn
  have hApos : 0 < A n := by
    dsimp [A]
    apply Finset.sum_pos'
    · intro k hk
      unfold clipped_step_size
      exact (Real.rpow_pos_of_pos (by positivity) _).le
    · refine ⟨0, Finset.mem_range.mpr hn, ?_⟩
      unfold clipped_step_size
      exact Real.rpow_pos_of_pos (by positivity) _
  have hDlt : D n < A n * y / 4 := by
    rw [div_lt_iff₀ hApos] at hDn
    nlinarith
  let V : ℝ := ∑ k ∈ Finset.range n,
    (clipping_radius G p k) ^ 2 * (clipped_step_size p k * G) ^ 2
  let r : ℝ := (3 / 4 : ℝ) * A n * y
  have hVpos : 0 < V := by simpa [V] using hscale_n.1
  have hrpos : 0 < r := by dsimp [r]; positivity
  let avec : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun k ω =>
    -(clipped_step_size p k) • gradient f (x k ω)
  let R : ℕ → ℝ := fun k => clipped_step_size p k * G
  letI : MeasurableSpace (EuclideanSpace ℝ (Fin d)) :=
    borel (EuclideanSpace ℝ (Fin d))
  letI : BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩
  have havec : ∀ k,
      Measurable[filtration k, borel (EuclideanSpace ℝ (Fin d))] (avec k) := by
    intro k
    dsimp [avec]
    exact (continuous_id.const_smul (-(clipped_step_size p k))).measurable.comp
      (hLip.continuous.measurable.comp (hrun_meas k))
  have hR : ∀ k, 0 ≤ R k := by
    intro k
    dsimp [R]
    exact mul_nonneg (Real.rpow_pos_of_pos (by positivity) _).le hG.le
  have havec_bound : ∀ k, ∀ᵐ ω ∂μ, ‖avec k ω‖ ≤ R k := by
    intro k
    filter_upwards [] with ω
    dsimp [avec, R]
    have hstep : 0 ≤ clipped_step_size p k := by
      unfold clipped_step_size
      exact (Real.rpow_pos_of_pos (by positivity) _).le
    simp only [norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg hstep]
    exact mul_le_mul_of_nonneg_left (hgrad (x k ω))
      hstep
  have hmgf := finite_horizon_conditional_mgf μ filtration f x g bias centered
    G p σ hest avec R havec hR havec_bound n r hrpos.le (by simpa [V, R] using hVpos)
  have hprob : μ {ω | y ≤ best_iterate_gradient_squared f x n ω} ≤
      ENNReal.ofReal (Real.exp (-(r ^ 2) / (12 * V))) := by
    refine (MeasureTheory.measure_mono_ae ?_).trans hmgf
    filter_upwards [htelescope n] with ω htelω
    intro hyω
    change A n * best_iterate_gradient_squared f x n ω ≤ D n +
      ∑ k ∈ Finset.range n,
        inner ℝ (-(clipped_step_size p k) • gradient f (x k ω))
          (centered k ω) at htelω
    change (3 / 4 : ℝ) * A n * y ≤
      ∑ k ∈ Finset.range n,
        inner ℝ (-(clipped_step_size p k) • gradient f (x k ω))
          (centered k ω)
    have hAy : A n * y ≤ A n * best_iterate_gradient_squared f x n ω :=
      mul_le_mul_of_nonneg_left hyω hApos.le
    nlinarith [hDlt]
  have hlogbound := ENNReal.log_le_log hprob
  rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp] at hlogbound
  have hreal : (-(r ^ 2) / (12 * V)) / heavy_tail_ldp_speed p n ≤
      -(y ^ 2 / (768 * G ^ 4)) := by
    dsimp [r]
    rw [div_le_iff₀ hspeed_n]
    have hscale' : heavy_tail_ldp_speed p n * V ≤ 32 * G ^ 4 * A n ^ 2 := by
      simpa [V, A] using hscale_n.2
    have hposbound : y ^ 2 / (768 * G ^ 4) * heavy_tail_ldp_speed p n ≤
        ((3 / 4 : ℝ) * A n * y) ^ 2 / (12 * V) := by
      rw [le_div_iff₀ (mul_pos (by norm_num) hVpos)]
      field_simp
      nlinarith [sq_nonneg (A n), sq_nonneg y, pow_pos hG 4]
    simpa only [neg_div, neg_mul] using neg_le_neg hposbound
  calc
    ENNReal.log (μ {ω | y ≤ best_iterate_gradient_squared f x n ω}) /
        (heavy_tail_ldp_speed p n : EReal) ≤
      ((↑((-(r ^ 2) / (12 * V) : ℝ)) : EReal) /
        (↑(heavy_tail_ldp_speed p n) : EReal)) := by
      exact EReal.div_le_div_right_of_nonneg (by exact_mod_cast hspeed_n.le) hlogbound
    _ = (↑(((-(r ^ 2) / (12 * V)) / heavy_tail_ldp_speed p n : ℝ)) : EReal) := by
      rw [← EReal.coe_div]
    _ ≤ (↑((-(y ^ 2 / (768 * G ^ 4)) : ℝ)) : EReal) := by exact_mod_cast hreal
    _ = -(↑(y ^ 2 / (768 * G ^ 4) : ℝ) : EReal) := by simp

@[blueprint "lem:critical-log-sum-bound-local"
  (statement := /-- For every $n\in\mathbb N$,
  \[
    \sum_{k<n}\frac{\log(k+2)}{k+2}\leq \log^2(n+1).
  \] -/)
  (proof := /-- For the induction step, the inequality
  $1/(n+2)\leq\log(n+2)-\log(n+1)$ follows from the standard lower bound
  $1-x^{-1}\leq\log x$ at $x=(n+2)/(n+1)$.  Since the logarithm is nonnegative
  and increasing on these arguments, multiplication by $\log(n+2)$ gives
  \[
    \frac{\log(n+2)}{n+2}
      \leq \log(n+2)\bigl(\log(n+2)-\log(n+1)\bigr)
      \leq \log^2(n+2)-\log^2(n+1).
  \]
  Adding this estimate to the induction hypothesis telescopes the squares. -/)
  (title := /-- A logarithmic harmonic-sum bound -/)
  (latexEnv := "lemma")]
lemma critical_log_sum_bound_local (n : ℕ) :
    (∑ k ∈ Finset.range n,
      Real.log (((k + 2 : ℕ) : ℝ)) / (((k + 2 : ℕ) : ℝ))) ≤
        (Real.log (((n + 1 : ℕ) : ℝ))) ^ 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hn1 : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
      have hn2 : 0 < (((n + 2 : ℕ) : ℝ)) := by positivity
      have hn12 : (((n + 1 : ℕ) : ℝ)) < (((n + 2 : ℕ) : ℝ)) := by
        exact_mod_cast Nat.lt_succ_self (n + 1)
      have hlog1 : 0 ≤ Real.log (((n + 1 : ℕ) : ℝ)) :=
        Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega : n + 1 ≠ 0))
      have hlog2 : 0 ≤ Real.log (((n + 2 : ℕ) : ℝ)) :=
        Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega : n + 2 ≠ 0))
      have hlog_mono :
          Real.log (((n + 1 : ℕ) : ℝ)) ≤ Real.log (((n + 2 : ℕ) : ℝ)) :=
        (Real.strictMonoOn_log hn1 hn2 hn12).le
      have hdiv :
          1 / (((n + 2 : ℕ) : ℝ)) ≤
            Real.log (((n + 2 : ℕ) : ℝ)) - Real.log (((n + 1 : ℕ) : ℝ)) := by
        have h := Real.one_sub_inv_le_log_of_pos
          (div_pos hn2 hn1)
        rw [Real.log_div (ne_of_gt hn2) (ne_of_gt hn1)] at h
        convert h using 1 <;> field_simp <;> norm_num
      calc
        (∑ k ∈ Finset.range n,
            Real.log (((k + 2 : ℕ) : ℝ)) / (((k + 2 : ℕ) : ℝ))) +
              Real.log (((n + 2 : ℕ) : ℝ)) / (((n + 2 : ℕ) : ℝ)) ≤
            Real.log (((n + 1 : ℕ) : ℝ)) ^ 2 +
              Real.log (((n + 2 : ℕ) : ℝ)) / (((n + 2 : ℕ) : ℝ)) :=
          add_le_add ih le_rfl
        _ ≤ Real.log (((n + 2 : ℕ) : ℝ)) ^ 2 := by
          have hterm :
              Real.log (((n + 2 : ℕ) : ℝ)) / (((n + 2 : ℕ) : ℝ)) ≤
                Real.log (((n + 2 : ℕ) : ℝ)) *
                  (Real.log (((n + 2 : ℕ) : ℝ)) -
                    Real.log (((n + 1 : ℕ) : ℝ))) := by
            rw [div_eq_mul_inv]
            simpa only [one_mul, one_div] using mul_le_mul_of_nonneg_left hdiv hlog2
          nlinarith

@[blueprint "lem:critical-step-sum-lower-local"
  (statement := /-- For every $n\in\mathbb N$, the critical step sizes satisfy
  \[
    \sqrt{n+1}-1\leq\sum_{k<n}\alpha_k,
  \]
  where $\alpha_k=(k+2)^{-1/2}$ is the zero-based step size at $p=2$. -/)
  (proof := /-- By \cref{def:clipped-step-size}, at $p=2$ one has
  $\alpha_k=1/\sqrt{k+2}$.  For $a=\sqrt{k+2}$ and $b=\sqrt{k+1}$, positivity,
  $b\leq a$, and $a^2-b^2=1$ imply
  $a-b\leq1/a=\alpha_k$.  Summing this inequality and using induction
  telescopes the square-root differences. -/)
  (title := /-- A lower bound for the critical step-size sum -/)
  (latexEnv := "lemma")]
lemma critical_step_sum_lower_local (n : ℕ) :
    Real.sqrt (((n + 1 : ℕ) : ℝ)) - 1 ≤
      ∑ k ∈ Finset.range n, clipped_step_size 2 k := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hn1 : 0 ≤ (((n + 1 : ℕ) : ℝ)) := by positivity
      have hn2 : 0 ≤ (((n + 2 : ℕ) : ℝ)) := by positivity
      have hsqrt_mono :
          Real.sqrt (((n + 1 : ℕ) : ℝ)) ≤ Real.sqrt (((n + 2 : ℕ) : ℝ)) := by
        exact Real.sqrt_le_sqrt (by norm_num)
      have hsqrt_pos : 0 < Real.sqrt (((n + 2 : ℕ) : ℝ)) := by positivity
      have hmul :
          Real.sqrt (((n + 1 : ℕ) : ℝ)) * Real.sqrt (((n + 1 : ℕ) : ℝ)) ≤
            Real.sqrt (((n + 2 : ℕ) : ℝ)) * Real.sqrt (((n + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hsqrt_mono (Real.sqrt_nonneg _)
      have hstep :
          Real.sqrt (((n + 2 : ℕ) : ℝ)) - Real.sqrt (((n + 1 : ℕ) : ℝ)) ≤
            (Real.sqrt (((n + 2 : ℕ) : ℝ)))⁻¹ := by
        rw [inv_eq_one_div]
        apply (le_div_iff₀ hsqrt_pos).2
        rw [sub_mul]
        have hs1 :
            Real.sqrt (((n + 1 : ℕ) : ℝ)) * Real.sqrt (((n + 1 : ℕ) : ℝ)) =
              (((n + 1 : ℕ) : ℝ)) := by
          simpa only [pow_two] using Real.sq_sqrt hn1
        have hs2 :
            Real.sqrt (((n + 2 : ℕ) : ℝ)) * Real.sqrt (((n + 2 : ℕ) : ℝ)) =
              (((n + 2 : ℕ) : ℝ)) := by
          simpa only [pow_two] using Real.sq_sqrt hn2
        rw [hs1] at hmul
        rw [hs2]
        norm_num at hmul ⊢
        linarith
      have halpha :
          clipped_step_size 2 n = (Real.sqrt (((n + 2 : ℕ) : ℝ)))⁻¹ := by
        simp only [clipped_step_size]
        norm_num
        rw [Real.rpow_neg (by positivity) (1 / 2 : ℝ)]
        rw [← Real.sqrt_eq_rpow]
      rw [halpha]
      linarith

@[blueprint "lem:weighted-sum-is-little-o-local"
  (statement := /-- Let $f,g:\mathbb N\to\mathbb R$.  If $f_n=o(g_n)$,
  $g_n\geq0$ for every $n$, and the partial sums of $g$ tend to $+\infty$,
  then
  \[
    \sum_{k<n}f_k=o\!\left(\sum_{k<n}g_k\right).
  \] -/)
  (proof := /-- Fix $\varepsilon>0$ and choose $N$ such that
  $|f_k|\leq(\varepsilon/2)g_k$ for $k\geq N$.  The fixed initial sum
  $\sum_{k<N}f_k$ is little-oh of the divergent nonnegative partial sums of
  $g$.  For $n\geq N$, split the sum at $N$, apply the preceding pointwise
  bound on the tail, and enlarge the nonnegative tail sum to the full partial
  sum.  The initial and tail contributions are each at most
  $(\varepsilon/2)\sum_{k<n}g_k$. -/)
  (title := /-- Little-oh transfer to nonnegative weighted partial sums -/)
  (latexEnv := "lemma")]
lemma weighted_sum_is_little_o_local {f g : ℕ → ℝ}
    (h : f =o[Filter.atTop] g) (hg : 0 ≤ g)
    (hg_top : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, g i)
      Filter.atTop Filter.atTop) :
    (fun n => ∑ i ∈ Finset.range n, f i) =o[Filter.atTop]
      fun n => ∑ i ∈ Finset.range n, g i := by
  have hgnorm : ∀ i, ‖g i‖ = g i := fun i => Real.norm_of_nonneg (hg i)
  have hsum_norm : ∀ n, ‖∑ i ∈ Finset.range n, g i‖ =
      ∑ i ∈ Finset.range n, g i := fun n => by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact Finset.sum_nonneg fun i _ => hg i
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ b : ℕ, N ≤ b →
      ‖f b‖ ≤ ε / 2 * g b := by
    simpa only [hgnorm, Filter.eventually_atTop] using
      Asymptotics.isLittleO_iff.mp h (half_pos hε)
  have hfixed : (fun _ : ℕ => ∑ i ∈ Finset.range N, f i) =o[Filter.atTop]
      fun n => ∑ i ∈ Finset.range n, g i := by
    apply Asymptotics.isLittleO_const_left.mpr
    exact Or.inr (hg_top.congr fun n => (hsum_norm n).symm)
  filter_upwards [Asymptotics.isLittleO_iff.mp hfixed (half_pos hε),
    Filter.Ici_mem_atTop N] with n hn hNn
  change N ≤ n at hNn
  calc
    ‖∑ i ∈ Finset.range n, f i‖ =
        ‖(∑ i ∈ Finset.range N, f i) + ∑ i ∈ Finset.Ico N n, f i‖ := by
      rw [Finset.sum_range_add_sum_Ico _ hNn]
    _ ≤ ‖∑ i ∈ Finset.range N, f i‖ + ‖∑ i ∈ Finset.Ico N n, f i‖ :=
      norm_add_le _ _
    _ ≤ ‖∑ i ∈ Finset.range N, f i‖ +
        ∑ i ∈ Finset.Ico N n, ε / 2 * g i :=
      add_le_add le_rfl (norm_sum_le_of_le _ fun i hi =>
        hN i (Finset.mem_Ico.mp hi).1)
    _ ≤ ‖∑ i ∈ Finset.range N, f i‖ +
        ∑ i ∈ Finset.range n, ε / 2 * g i := by
      gcongr
      · exact fun i _ _ => mul_nonneg (half_pos hε).le (hg i)
      · rw [Finset.range_eq_Ico]
        exact Finset.Ico_subset_Ico zero_le le_rfl
    _ ≤ ε / 2 * ‖∑ i ∈ Finset.range n, g i‖ +
        ε / 2 * ∑ i ∈ Finset.range n, g i := by
      rw [← Finset.mul_sum]
      exact add_le_add hn le_rfl
    _ = ε * ‖∑ i ∈ Finset.range n, g i‖ := by
      rw [hsum_norm]
      ring

@[blueprint "lem:critical-speed-properties-local"
  (statement := /-- The critical speed $n_t=t/(\log t)^2$ is eventually
  positive and tends to $+\infty$ as $t\to\infty$. -/)
  (proof := /-- The standard estimate $\log^2 t=o(t)$ implies that
  $(\log^2 t)/t$ tends to zero.  This quotient is eventually positive, so its
  reciprocal tends to $+\infty$.  On the same eventual set the reciprocal is
  exactly $t/(\log t)^2$, which is \cref{def:critical-ldp-speed}. -/)
  (title := /-- Positivity and divergence of the critical speed -/)
  (latexEnv := "lemma")]
lemma critical_speed_properties_local :
    (∀ᶠ t in Filter.atTop, 0 < critical_ldp_speed t) ∧
      Filter.Tendsto critical_ldp_speed Filter.atTop Filter.atTop := by
  have hsmall :
      Filter.Tendsto
          (fun n : ℕ => Real.log (n : ℝ) ^ 2 / (n : ℝ))
          Filter.atTop (nhds 0) := by
    have ho := (Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
      tendsto_natCast_atTop_atTop
    simpa only [Function.comp_apply, id_eq] using ho.tendsto_div_nhds_zero
  have hsmall_pos :
      ∀ᶠ n : ℕ in Filter.atTop, 0 < Real.log (n : ℝ) ^ 2 / (n : ℝ) := by
    filter_upwards [Filter.Ici_mem_atTop 2] with n hn
    change 2 ≤ n at hn
    have hn1 : 1 < n := by omega
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn1)
    have hnpos : 0 < (n : ℝ) := by positivity
    exact div_pos (sq_pos_of_pos hlog) hnpos
  have hsmall_within :
      Filter.Tendsto
          (fun n : ℕ => Real.log (n : ℝ) ^ 2 / (n : ℝ))
          Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hsmall, hsmall_pos⟩
  have hinv := hsmall_within.inv_tendsto_nhdsGT_zero
  have heq :
      (fun n : ℕ => (Real.log (n : ℝ) ^ 2 / (n : ℝ))⁻¹) =ᶠ[Filter.atTop]
        critical_ldp_speed := by
    filter_upwards [Filter.Ici_mem_atTop 2] with n hn
    simp only [critical_ldp_speed, inv_div]
  constructor
  · filter_upwards [Filter.Ici_mem_atTop 2] with n hn
    change 2 ≤ n at hn
    unfold critical_ldp_speed
    have hn1 : 1 < n := by omega
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn1)
    exact div_pos (by positivity) (sq_pos_of_pos hlog)
  · exact hinv.congr' heq

@[blueprint "lem:critical-schedule-asymptotics"
  (statement := /-- Let $(\Omega,\mathcal A,\mu)$ be a probability space with a
  filtration $(\mathcal F_t)_{t\in\mathbb N}$, let $d\in\mathbb N$, and let
  $f:\mathbb R^d\to\mathbb R$ and
  $x_t,g_t,b_t,u_t:\Omega\to\mathbb R^d$ be given for every $t\in\mathbb N$.
  Fix $G,p,\sigma\in\mathbb R$ and $L\in\mathbb R_{\geq0}$.  Assume that these
  objects satisfy
  \cref{def:nonconvex-cost-assumptions,def:heavy-tail-noise-assumptions,
  def:clipped-sgd-run,def:has-adapted-clipping-estimates}, and assume $p=2$.
  Write $F_t$ for
  \cref{def:best-iterate-gradient-squared}.  Then the speed
  $n_t=t/(\log t)^2$ is eventually positive and tends to infinity.  Moreover,
  for every $y\in\mathbb R$ with $y\geq0$,
  \[
    \limsup_{t\to\infty}\frac{1}{n_t}
      \log\mu\{F_t\geq y\}
      \leq-\frac{y^2}{384G^4}.
  \] -/)
  (proof := /-- Put $A_n=\sum_{k<n}\alpha_k$ and
  $Q_n=\sum_{k<n}\alpha_k^2\gamma_k^2$.  By
  \cref{lem:critical-step-sum-lower-local},
  $A_n\geq\sqrt{n+1}-1$, so $A_n\to\infty$.  At $p=2$, one has
  $\gamma_k^{-1}\to0$ and $\alpha_k\gamma_k^2\to0$; the latter follows from
  $\log^2 t=o(t)$.  Applying \cref{lem:weighted-sum-is-little-o-local} to the
  nonnegative weights $\alpha_k$ gives
  \[
    \sum_{k<n}\alpha_k\gamma_k^{-1}=o(A_n),\qquad Q_n=o(A_n).
  \]
  Hence the deterministic initial, bias, and smoothness terms in
  \cref{lem:clipped-sgd-descent-telescope} form a remainder $D_n=o(A_n)$.

  The positivity and divergence assertions for $n/(\log n)^2$ are
  \cref{lem:critical-speed-properties-local}.  Fix $y>0$.  Eventually
  $D_n\leq A_ny/100$.  Moreover,
  \cref{lem:critical-log-sum-bound-local} and
  $\log(n+1)\leq2\log n$ give
  \[
    A_n\geq\frac34\sqrt n,
    \qquad Q_n\leq16G^2(\log n)^2.
  \]
  The descent telescope therefore sends the event $\{F_n\geq y\}$, up to a
  null set, into the centered-sum event with threshold
  $r_n=(99/100)A_ny$.  Apply
  \cref{lem:finite-horizon-conditional-mgf} with
  $a_k=-\alpha_k\nabla f(x_k)$ and deterministic bound $\alpha_kG$.  Its
  variance parameter is $V_n=G^2Q_n$.  The displayed estimates imply
  $r_n^2\geq ny^2/2$ and
  $V_n\,n/(\log n)^2\leq16G^4n$, whence
  \[
    \frac{r_n^2}{12V_n}\frac{(\log n)^2}{n}
      \geq\frac{y^2}{384G^4}.
  \]
  Taking extended logarithms and then the limsup proves the asserted bound.
  If $y=0$, the logarithm is nonpositive because every event has probability
  at most one, and division by the eventually positive speed preserves this
  inequality. -/)
  (title := /-- One-sided tail asymptotics at the second-moment threshold -/)
  (latexEnv := "lemma")]
lemma critical_schedule_asymptotics
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    {d : ℕ} (filtration : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x g bias centered : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (G : ℝ) (L : NNReal) (p σ : ℝ)
    (hcost : nonconvex_cost_assumptions f G L)
    (hnoise : heavy_tail_noise_assumptions μ filtration f x g p σ)
    (hrun : clipped_sgd_run μ filtration x g G p)
    (hest : has_adapted_clipping_estimates μ filtration f x g bias centered G p σ)
    (hp2 : p = 2) :
    (∀ᶠ t in Filter.atTop, 0 < critical_ldp_speed t) ∧
    Filter.Tendsto critical_ldp_speed Filter.atTop Filter.atTop ∧
    ∀ y : ℝ, 0 ≤ y →
      Filter.limsup
          (fun t => ENNReal.log
            (μ {ω | y ≤ best_iterate_gradient_squared f x t ω}) /
              (critical_ldp_speed t : EReal))
          Filter.atTop
        ≤ -(↑(y ^ 2 / (384 * G ^ 4) : ℝ) : EReal) := by
  subst p
  letI : MeasurableSpace (EuclideanSpace ℝ (Fin d)) :=
    borel (EuclideanSpace ℝ (Fin d))
  letI : BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩
  have hG : 0 < G := hcost.1
  have hσ : 0 ≤ σ := hnoise.2.2.1
  let α : ℕ → ℝ := fun k => clipped_step_size 2 k
  let γ : ℕ → ℝ := fun k => clipping_radius G 2 k
  let A : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, α k
  let Q : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, (α k) ^ 2 * (γ k) ^ 2
  have hα_pos (k : ℕ) : 0 < α k := by
    dsimp [α, clipped_step_size]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hα_nonneg : 0 ≤ α := fun k => (hα_pos k).le
  have hγ_pos (k : ℕ) : 0 < γ k := by
    simp only [γ, clipping_radius, if_pos rfl]
    have hlog : 0 < Real.log (((k + 2 : ℕ) : ℝ)) :=
      Real.log_pos (by exact_mod_cast (show 1 < k + 2 by omega))
    exact mul_pos (mul_pos (by norm_num) hG) (Real.sqrt_pos.2 hlog)
  have hbase :
      Filter.Tendsto (fun n : ℕ => (((n + 2 : ℕ) : ℝ)))
        Filter.atTop Filter.atTop := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      Filter.tendsto_atTop_add_const_right Filter.atTop (2 : ℝ)
        tendsto_natCast_atTop_atTop
  have hA_top : Filter.Tendsto A Filter.atTop Filter.atTop := by
    have hsqrt :
        Filter.Tendsto (fun n : ℕ => Real.sqrt (((n + 1 : ℕ) : ℝ)) - 1)
          Filter.atTop Filter.atTop := by
      have hshift :
          Filter.Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)))
            Filter.atTop Filter.atTop := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
            tendsto_natCast_atTop_atTop
      exact Filter.tendsto_atTop_add_const_right Filter.atTop (-1 : ℝ)
        (Real.tendsto_sqrt_atTop.comp hshift)
    apply Filter.tendsto_atTop_mono
      (fun n => critical_step_sum_lower_local n)
    simpa only [A, α] using hsqrt
  have hA_nonneg (n : ℕ) : 0 ≤ A n := by
    exact Finset.sum_nonneg fun k _ => hα_nonneg k
  have hA_norm :
      Filter.Tendsto (norm ∘ A) Filter.atTop Filter.atTop := by
    apply hA_top.congr'
    exact Filter.Eventually.of_forall fun n => by
      simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (hA_nonneg n)]
  have hγ_top : Filter.Tendsto γ Filter.atTop Filter.atTop := by
    have hsqrtlog := Real.tendsto_sqrt_atTop.comp
      (Real.tendsto_log_atTop.comp hbase)
    have hmul := hsqrtlog.const_mul_atTop (by positivity : 0 < 2 * G)
    simpa [γ, clipping_radius, Function.comp_apply, mul_assoc] using hmul
  have hbias_z :
      Filter.Tendsto (fun k => Real.rpow (γ k) (1 - (2 : ℝ)))
        Filter.atTop (nhds 0) := by
    apply hγ_top.inv_tendsto_atTop.congr'
    exact Filter.Eventually.of_forall fun k => by
      norm_num [Real.rpow_neg_one]
  have hbias_point_o :
      (fun k => α k * Real.rpow (γ k) (1 - (2 : ℝ))) =o[Filter.atTop] α := by
    have hz := (Asymptotics.isLittleO_one_iff ℝ).mpr hbias_z
    simpa only [mul_one] using
      (Asymptotics.isBigO_refl α Filter.atTop).mul_isLittleO hz
  have hbias_sum_o :
      (fun n => ∑ k ∈ Finset.range n,
        α k * Real.rpow (γ k) (1 - (2 : ℝ))) =o[Filter.atTop] A := by
    simpa only [A] using
      weighted_sum_is_little_o_local hbias_point_o hα_nonneg hA_top
  have hlog_sqrt :
      Filter.Tendsto
          (fun n : ℕ => Real.log (((n + 2 : ℕ) : ℝ)) /
            Real.sqrt (((n + 2 : ℕ) : ℝ)))
          Filter.atTop (nhds 0) := by
    have ho := (Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto hbase
    have hsquare :
        Filter.Tendsto
            (fun n : ℕ => Real.log (((n + 2 : ℕ) : ℝ)) ^ 2 /
              (((n + 2 : ℕ) : ℝ))) Filter.atTop (nhds 0) := by
      simpa only [Function.comp_apply, id_eq] using ho.tendsto_div_nhds_zero
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
    simpa only [Real.sqrt_zero, Function.comp_apply] using
      hsqrt.congr' (Filter.Eventually.of_forall fun n => by
      have hlog_nonneg : 0 ≤ Real.log (((n + 2 : ℕ) : ℝ)) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 2 by omega))
      change Real.sqrt (Real.log (((n + 2 : ℕ) : ℝ)) ^ 2 /
          (((n + 2 : ℕ) : ℝ))) =
        Real.log (((n + 2 : ℕ) : ℝ)) / Real.sqrt (((n + 2 : ℕ) : ℝ))
      rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hlog_nonneg])
  have hsmooth_z :
      Filter.Tendsto (fun k => α k * (γ k) ^ 2)
        Filter.atTop (nhds 0) := by
    have hc : Filter.Tendsto (fun _ : ℕ => 4 * G ^ 2) Filter.atTop
        (nhds (4 * G ^ 2)) := tendsto_const_nhds
    have hlim := hc.mul hlog_sqrt
    simpa only [mul_zero] using hlim.congr' (Filter.Eventually.of_forall fun k => by
      have hlog_nonneg : 0 ≤ Real.log (((k + 2 : ℕ) : ℝ)) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ k + 2 by omega))
      dsimp [α, γ, clipped_step_size, clipping_radius]
      norm_num
      rw [Real.rpow_neg (by positivity) (1 / 2 : ℝ), ← Real.sqrt_eq_rpow]
      have hslog : Real.sqrt (Real.log (((k + 2 : ℕ) : ℝ))) ^ 2 =
          Real.log (((k + 2 : ℕ) : ℝ)) := Real.sq_sqrt hlog_nonneg
      have hgamma : (2 * G * Real.sqrt (Real.log (((k + 2 : ℕ) : ℝ)))) ^ 2 =
          4 * G ^ 2 * Real.log (((k + 2 : ℕ) : ℝ)) := by
        rw [mul_pow, mul_pow, hslog]
        norm_num
      norm_num [Nat.cast_add] at hgamma ⊢
      rw [hgamma, div_eq_mul_inv]
      ring)
  have hsmooth_point_o :
      (fun k => α k * (α k * (γ k) ^ 2)) =o[Filter.atTop] α := by
    have hz := (Asymptotics.isLittleO_one_iff ℝ).mpr hsmooth_z
    simpa only [mul_one] using
      (Asymptotics.isBigO_refl α Filter.atTop).mul_isLittleO hz
  have hQ_o : Q =o[Filter.atTop] A := by
    have hs := weighted_sum_is_little_o_local hsmooth_point_o hα_nonneg hA_top
    simpa only [Q, pow_two, mul_assoc] using hs
  rcases clipped_sgd_descent_telescope μ filtration f x g bias centered G L 2 σ
      hcost hrun hest with ⟨x₀, f_lower, hf_lower, htelescope⟩
  let D : ℕ → ℝ := fun n =>
    f x₀ - f_lower +
      4 * G * Real.rpow σ 2 *
        (∑ k ∈ Finset.range n,
          α k * Real.rpow (γ k) (1 - (2 : ℝ))) +
      ((L : ℝ) / 2) * Q n
  have hD_o : D =o[Filter.atTop] A := by
    have hconst : (fun _ : ℕ => f x₀ - f_lower) =o[Filter.atTop] A :=
      Asymptotics.isLittleO_const_left.mpr (Or.inr hA_norm)
    have hb := hbias_sum_o.const_mul_left
      (4 * G * Real.rpow σ 2)
    have hq := hQ_o.const_mul_left ((L : ℝ) / 2)
    simpa only [D] using hconst.add hb |>.add hq
  have hD_div :
      Filter.Tendsto (fun n => D n / A n) Filter.atTop (nhds 0) :=
    hD_o.tendsto_div_nhds_zero
  rcases critical_speed_properties_local with ⟨hspeed_pos, hspeed_top⟩
  refine ⟨hspeed_pos, hspeed_top, ?_⟩
  intro y hy
  by_cases hyzero : y = 0
  · subst y
    have hnonpos :
        (fun t => ENNReal.log
          (μ {ω | (0 : ℝ) ≤ best_iterate_gradient_squared f x t ω}) /
            (critical_ldp_speed t : EReal)) ≤ᶠ[Filter.atTop]
          (fun _ => (0 : EReal)) := by
      filter_upwards [hspeed_pos] with t ht
      have hlog : ENNReal.log
          (μ {ω | (0 : ℝ) ≤ best_iterate_gradient_squared f x t ω}) ≤ 0 := by
        calc
          ENNReal.log (μ {ω | (0 : ℝ) ≤ best_iterate_gradient_squared f x t ω}) ≤
              ENNReal.log 1 := ENNReal.log_monotone MeasureTheory.prob_le_one
          _ = 0 := by simp
      have hs : (0 : EReal) ≤ (critical_ldp_speed t : EReal) := by
        exact_mod_cast ht.le
      simpa using EReal.div_nonpos_of_nonpos_of_nonneg hlog hs
    calc
      Filter.limsup
          (fun t => ENNReal.log
            (μ {ω | (0 : ℝ) ≤ best_iterate_gradient_squared f x t ω}) /
              (critical_ldp_speed t : EReal)) Filter.atTop
        ≤ Filter.limsup (fun _ : ℕ => (0 : EReal)) Filter.atTop :=
          Filter.limsup_le_limsup hnonpos
      _ = 0 := by simp
      _ = -(↑((0 : ℝ) ^ 2 / (384 * G ^ 4) : ℝ) : EReal) := by simp
  · have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hyzero)
    have hsmallD : ∀ᶠ n : ℕ in Filter.atTop, D n ≤ A n * y / 100 := by
      have hratio : ∀ᶠ n : ℕ in Filter.atTop, D n / A n < y / 100 :=
        (tendsto_order.mp hD_div).2 (y / 100) (by positivity)
      have hAone : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ A n :=
        Filter.tendsto_atTop.mp hA_top 1
      filter_upwards [hratio, hAone] with n hn hAn
      have hApos : 0 < A n := lt_of_lt_of_le zero_lt_one hAn
      simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
        ((div_lt_iff₀ hApos).mp hn).le
    have hpoint :
        (fun t => ENNReal.log
          (μ {ω | y ≤ best_iterate_gradient_squared f x t ω}) /
            (critical_ldp_speed t : EReal)) ≤ᶠ[Filter.atTop]
          (fun _ => -(↑(y ^ 2 / (384 * G ^ 4) : ℝ) : EReal)) := by
      filter_upwards [hsmallD, Filter.Ici_mem_atTop 16, hspeed_pos] with n hDn hn hspeedn
      change 16 ≤ n at hn
      have hAn_lower : (3 / 4 : ℝ) * Real.sqrt (n : ℝ) ≤ A n := by
        have hsqrt4 : (4 : ℝ) ≤ Real.sqrt (n : ℝ) := by
          apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
          exact_mod_cast hn
        have hsqrt_mono : Real.sqrt (n : ℝ) ≤ Real.sqrt (((n + 1 : ℕ) : ℝ)) := by
          exact Real.sqrt_le_sqrt (by norm_num)
        have hs := critical_step_sum_lower_local n
        change Real.sqrt (((n + 1 : ℕ) : ℝ)) - 1 ≤ A n at hs
        nlinarith
      have hlog_pos : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      have hlog_bound :
          Real.log (((n + 1 : ℕ) : ℝ)) ≤ 2 * Real.log (n : ℝ) := by
        have hnn : (((n + 1 : ℕ) : ℝ)) ≤ (n : ℝ) ^ 2 := by
          exact_mod_cast (show n + 1 ≤ n ^ 2 by nlinarith)
        calc
          Real.log (((n + 1 : ℕ) : ℝ)) ≤ Real.log ((n : ℝ) ^ 2) :=
            Real.strictMonoOn_log.monotoneOn
              (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) hnn
          _ = 2 * Real.log (n : ℝ) := by
            rw [Real.log_pow]
            norm_num
      have hQ_bound : Q n ≤ 16 * G ^ 2 * Real.log (n : ℝ) ^ 2 := by
        have hsum := critical_log_sum_bound_local n
        have hQeq : Q n = 4 * G ^ 2 *
            (∑ k ∈ Finset.range n,
              Real.log (((k + 2 : ℕ) : ℝ)) / (((k + 2 : ℕ) : ℝ))) := by
          dsimp [Q, α, γ, clipped_step_size, clipping_radius]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          have hlog_nonneg : 0 ≤ Real.log (((k + 2 : ℕ) : ℝ)) :=
            Real.log_nonneg (by exact_mod_cast (show 1 ≤ k + 2 by omega))
          norm_num
          rw [Real.rpow_neg (by positivity) (1 / 2 : ℝ), ← Real.sqrt_eq_rpow]
          have hslog : Real.sqrt (Real.log (((k + 2 : ℕ) : ℝ))) ^ 2 =
              Real.log (((k + 2 : ℕ) : ℝ)) := Real.sq_sqrt hlog_nonneg
          have hgamma : (2 * G * Real.sqrt (Real.log (((k + 2 : ℕ) : ℝ)))) ^ 2 =
              4 * G ^ 2 * Real.log (((k + 2 : ℕ) : ℝ)) := by
            rw [mul_pow, mul_pow, hslog]
            norm_num
          have halpha : (Real.sqrt (((k + 2 : ℕ) : ℝ)))⁻¹ ^ 2 =
              ((((k + 2 : ℕ) : ℝ)))⁻¹ := by
            rw [inv_pow, Real.sq_sqrt (by positivity)]
          norm_num [Nat.cast_add] at hgamma halpha ⊢
          rw [hgamma, halpha]
          field_simp
        rw [hQeq]
        have hGsq : 0 ≤ 4 * G ^ 2 := by positivity
        have hs1 := mul_le_mul_of_nonneg_left hsum hGsq
        have hlog1 : 0 ≤ Real.log (((n + 1 : ℕ) : ℝ)) :=
          Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 1 by omega))
        have hsquare : Real.log (((n + 1 : ℕ) : ℝ)) ^ 2 ≤
            4 * Real.log (n : ℝ) ^ 2 := by
          nlinarith [sq_nonneg
            (Real.log (((n + 1 : ℕ) : ℝ)) - 2 * Real.log (n : ℝ))]
        have hs2 := mul_le_mul_of_nonneg_left hsquare hGsq
        nlinarith
      let r : ℝ := (99 / 100 : ℝ) * A n * y
      let V : ℝ := G ^ 2 * Q n
      have hApos : 0 < A n := lt_of_lt_of_le (by positivity) hAn_lower
      have hQpos : 0 < Q n := by
        dsimp [Q]
        have hmem : 0 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
        have hterm : 0 < (α 0) ^ 2 * (γ 0) ^ 2 := mul_pos (sq_pos_of_pos (hα_pos 0))
          (sq_pos_of_pos (hγ_pos 0))
        exact lt_of_lt_of_le hterm (Finset.single_le_sum
          (fun k _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hmem)
      have hVpos : 0 < V := mul_pos (sq_pos_of_pos hG) hQpos
      have hrnonneg : 0 ≤ r := by dsimp [r]; positivity
      have ha_meas (k : ℕ) :
          Measurable[filtration k, borel (EuclideanSpace ℝ (Fin d))]
            (fun ω => -(α k) • gradient f (x k ω)) := by
        exact (hcost.2.2.2.2.continuous.measurable.comp (hrun.2.1 k)).const_smul (-(α k))
      have ha_bound (k : ℕ) :
          ∀ᵐ ω ∂μ, ‖-(α k) • gradient f (x k ω)‖ ≤ α k * G := by
        filter_upwards [] with ω
        rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (hα_nonneg k)]
        exact mul_le_mul_of_nonneg_left (hcost.2.2.2.1 (x k ω)) (hα_nonneg k)
      have hmgf := finite_horizon_conditional_mgf μ filtration f x g bias centered G 2 σ
        hest (fun k ω => -(α k) • gradient f (x k ω)) (fun k => α k * G)
        ha_meas (fun k => mul_nonneg (hα_nonneg k) hG.le) ha_bound n r hrnonneg
      have hVeq :
          (∑ k ∈ Finset.range n,
            (clipping_radius G 2 k) ^ 2 * (α k * G) ^ 2) = V := by
        dsimp [V, Q, γ]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      have hmgf' :
          μ {ω | r ≤ ∑ k ∈ Finset.range n,
            inner ℝ (-(α k) • gradient f (x k ω)) (centered k ω)} ≤
            ENNReal.ofReal (Real.exp (-(r ^ 2) / (12 * V))) := by
        rw [← hVeq]
        exact hmgf (by rw [hVeq]; exact hVpos)
      have htel := htelescope n
      have htail_ae :
          {ω | y ≤ best_iterate_gradient_squared f x n ω} ≤ᵐ[μ]
            {ω | r ≤ ∑ k ∈ Finset.range n,
              inner ℝ (-(α k) • gradient f (x k ω)) (centered k ω)} := by
        filter_upwards [htel] with ω hω
        dsimp [A, D, Q, α, γ] at hω
        change y ≤ best_iterate_gradient_squared f x n ω → _
        intro hyω
        dsimp [r]
        have hAy : A n * y ≤
            A n * best_iterate_gradient_squared f x n ω :=
          mul_le_mul_of_nonneg_left hyω (hA_nonneg n)
        change A n * best_iterate_gradient_squared f x n ω ≤
            D n + ∑ k ∈ Finset.range n,
              inner ℝ (-(α k) • gradient f (x k ω)) (centered k ω) at hω
        calc
          (99 / 100 : ℝ) * A n * y = A n * y - A n * y / 100 := by ring
          _ ≤ A n * y - D n := sub_le_sub_left hDn _
          _ ≤ ∑ k ∈ Finset.range n,
              inner ℝ (-(α k) • gradient f (x k ω)) (centered k ω) := by
            linarith
      have hmeasure :
          μ {ω | y ≤ best_iterate_gradient_squared f x n ω} ≤
            ENNReal.ofReal (Real.exp (-(r ^ 2) / (12 * V))) :=
        (MeasureTheory.measure_mono_ae htail_ae).trans hmgf'
      have hlogmeasure :
          ENNReal.log (μ {ω | y ≤ best_iterate_gradient_squared f x n ω}) ≤
            (↑(-(r ^ 2) / (12 * V) : ℝ) : EReal) := by
        calc
          ENNReal.log (μ {ω | y ≤ best_iterate_gradient_squared f x n ω}) ≤
              ENNReal.log (ENNReal.ofReal (Real.exp (-(r ^ 2) / (12 * V)))) :=
            ENNReal.log_monotone hmeasure
          _ = (↑(-(r ^ 2) / (12 * V) : ℝ) : EReal) := by
            rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
      have hratio_real :
          (-(r ^ 2) / (12 * V)) / critical_ldp_speed n ≤
            -(y ^ 2 / (384 * G ^ 4)) := by
        have hVbound : V ≤ 16 * G ^ 4 * Real.log (n : ℝ) ^ 2 := by
          dsimp [V]
          nlinarith [mul_le_mul_of_nonneg_left hQ_bound (sq_nonneg G)]
        have hspeedform : critical_ldp_speed n =
            (n : ℝ) / Real.log (n : ℝ) ^ 2 := rfl
        have hspeedpos : 0 < critical_ldp_speed n := hspeedn
        have hVnonneg : 0 ≤ V := hVpos.le
        have hr_lower :
            (99 / 100 : ℝ) * ((3 / 4 : ℝ) * Real.sqrt (n : ℝ)) * y ≤ r := by
          dsimp [r]
          nlinarith
        have hsqrtn : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
          Real.sq_sqrt (by positivity)
        have hlower_nonneg :
            0 ≤ (99 / 100 : ℝ) * ((3 / 4 : ℝ) * Real.sqrt (n : ℝ)) * y := by
          positivity
        have hr_square := mul_self_le_mul_self hlower_nonneg hr_lower
        have hr2 : (n : ℝ) * y ^ 2 / 2 ≤ r ^ 2 := by
          ring_nf at hr_square ⊢
          rw [hsqrtn] at hr_square
          nlinarith
        have hVs : V * critical_ldp_speed n ≤
            16 * G ^ 4 * (n : ℝ) := by
          calc
            V * critical_ldp_speed n ≤
                (16 * G ^ 4 * Real.log (n : ℝ) ^ 2) * critical_ldp_speed n :=
              mul_le_mul_of_nonneg_right hVbound hspeedpos.le
            _ = 16 * G ^ 4 * (n : ℝ) := by
              rw [hspeedform]
              field_simp [ne_of_gt hlog_pos]
        have hdenpos : 0 < 12 * (V * critical_ldp_speed n) := by positivity
        have hconstpos : 0 < 384 * G ^ 4 := by positivity
        have hcross :
            y ^ 2 * (12 * (V * critical_ldp_speed n)) ≤
              r ^ 2 * (384 * G ^ 4) := by
          have h1 := mul_le_mul_of_nonneg_left hVs (sq_nonneg y)
          have h2 := mul_le_mul_of_nonneg_right hr2
            (show 0 ≤ 384 * G ^ 4 by positivity)
          nlinarith
        have hpositive_ratio :
            y ^ 2 / (384 * G ^ 4) ≤
              r ^ 2 / (12 * (V * critical_ldp_speed n)) :=
          (div_le_div_iff₀ hconstpos hdenpos).mpr hcross
        have hrewrite :
            (-(r ^ 2) / (12 * V)) / critical_ldp_speed n =
              -(r ^ 2 / (12 * (V * critical_ldp_speed n))) := by
          field_simp [ne_of_gt hVpos, ne_of_gt hspeedpos]
        rw [hrewrite, neg_le_neg_iff]
        exact hpositive_ratio
      have hsE : (0 : EReal) ≤ (critical_ldp_speed n : EReal) := by
        exact_mod_cast hspeedn.le
      have hdivlog := EReal.div_le_div_right_of_nonneg hsE hlogmeasure
      rw [← EReal.coe_div] at hdivlog
      exact hdivlog.trans (by exact_mod_cast hratio_real)
    calc
      Filter.limsup
          (fun t => ENNReal.log
            (μ {ω | y ≤ best_iterate_gradient_squared f x t ω}) /
              (critical_ldp_speed t : EReal)) Filter.atTop
        ≤ Filter.limsup
            (fun _ : ℕ => -(↑(y ^ 2 / (384 * G ^ 4) : ℝ) : EReal))
            Filter.atTop := Filter.limsup_le_limsup hpoint
      _ = -(↑(y ^ 2 / (384 * G ^ 4) : ℝ) : EReal) := by simp

@[blueprint "lem:ldp-upper-bound-of-one-sided-tail"
  (statement := /-- Let $(\Omega,\mathcal A,\mu)$ be a probability space.  For
  each $t\in\mathbb N$, let $F_t:\Omega\to\mathbb R$ satisfy
  $F_t(\omega)\geq0$ for every $\omega\in\Omega$.  Let $(s_t)_{t\in\mathbb N}$
  be a real sequence that is eventually positive and tends to $+\infty$, and
  let $C>0$.  Suppose that for every $y\geq0$,
  \[
    \limsup_{t\to\infty}s_t^{-1}\log\mu\{F_t\geq y\}
      \leq-y^2/C.
  \]
  Then $(F_t)$ satisfies the large-deviation upper bound of
  \cref{def:ldp-upper-bound} with speed $s_t$ and rate
  $I(y)=y^2/C$ for $y\geq0$ and $I(y)=+\infty$ for $y<0$. -/)
  (proof := /-- By \cref{def:ldp-upper-bound}, the eventual positivity and
  divergence hypotheses establish the first two clauses of the conclusion.
  Fix a measurable set $B\subseteq\mathbb R$ and put
  $A=\overline B\cap[0,\infty)$.  Suppose first that $A$ is nonempty.  It is
  closed and bounded below, so $a=\inf A$ belongs to $A$.  If
  $F_t(\omega)\in B$, then pointwise nonnegativity and
  $B\subseteq\overline B$ give $F_t(\omega)\in A$, whence
  $a\leq F_t(\omega)$.  Monotonicity of measure and of the extended logarithm,
  followed by division by the eventually positive speed, therefore gives
  [
    \limsup_{t\to\infty}\frac{\log\mu\{F_t\in B\}}{s_t}
    \leq
    \limsup_{t\to\infty}\frac{\log\mu\{F_t\geq a\}}{s_t}
    \leq-\frac{a^2}{C}.
  ]
  Since $a\in\overline B$, $a\geq0$, and hence $I(a)=a^2/C$, the infimum of
  $I$ over $\overline B$ is at most $a^2/C$; negating yields the required
  upper bound.  If $A$ is empty, pointwise nonnegativity makes every preimage
  $F_t^{-1}(B)$ empty.  For every eventually positive speed term, its normalized
  extended logarithm is therefore $-\infty$, so the limsup is $-\infty$.
  Moreover, every point of $\overline B$ is negative, where $I=+\infty$;
  thus the infimum of $I$ over $\overline B$ is $+\infty$, including when
  $\overline B$ is empty.  The right-hand side in
  \cref{def:ldp-upper-bound} is consequently also $-\infty$. -/)
  (title := /-- LDP upper bound from nonnegative one-sided tails -/)
  (latexEnv := "lemma")]
lemma ldp_upper_bound_of_one_sided_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (F : ℕ → Ω → ℝ) (speed : ℕ → ℝ) (C : ℝ)
    (hF : ∀ t ω, 0 ≤ F t ω) (hC : 0 < C)
    (hpos : ∀ᶠ t in Filter.atTop, 0 < speed t)
    (htendsto : Filter.Tendsto speed Filter.atTop Filter.atTop)
    (htail : ∀ y : ℝ, 0 ≤ y →
      Filter.limsup
          (fun t => ENNReal.log (μ {ω | y ≤ F t ω}) / (speed t : EReal))
          Filter.atTop
        ≤ -(↑(y ^ 2 / C) : EReal)) :
    ldp_upper_bound μ F speed
      (fun y => if 0 ≤ y then (↑(y ^ 2 / C) : EReal) else ⊤) := by
  refine ⟨hpos, htendsto, ?_⟩
  intro B hB
  classical
  let A : Set ℝ := closure B ∩ Set.Ici 0
  by_cases hA : A.Nonempty
  · have hAclosed : IsClosed A := isClosed_closure.inter isClosed_Ici
    have hAbdd : BddBelow A := ⟨0, by
      intro x hx
      exact hx.2⟩
    let a : ℝ := sInf A
    have ha_mem : a ∈ A := hAclosed.csInf_mem hA hAbdd
    have ha0 : 0 ≤ a := ha_mem.2
    have hpre : ∀ t, F t ⁻¹' B ⊆ {ω | a ≤ F t ω} := by
      intro t ω hω
      have hFA : F t ω ∈ A := ⟨subset_closure hω, hF t ω⟩
      exact csInf_le hAbdd hFA
    have hmono :
        (fun t => ENNReal.log (μ (F t ⁻¹' B)) / (speed t : EReal)) ≤ᶠ[Filter.atTop]
          (fun t => ENNReal.log (μ {ω | a ≤ F t ω}) / (speed t : EReal)) := by
      filter_upwards [hpos] with t ht
      apply EReal.div_le_div_right_of_nonneg
      · exact_mod_cast ht.le
      · apply ENNReal.log_monotone
        exact MeasureTheory.measure_mono (hpre t)
    calc
      Filter.limsup
          (fun t => ENNReal.log (μ (F t ⁻¹' B)) / (speed t : EReal))
          Filter.atTop
        ≤ Filter.limsup
            (fun t => ENNReal.log (μ {ω | a ≤ F t ω}) / (speed t : EReal))
            Filter.atTop := Filter.limsup_le_limsup hmono
      _ ≤ -(↑(a ^ 2 / C) : EReal) := htail a ha0
      _ ≤ -sInf
          ((fun y : ℝ => if 0 ≤ y then (↑(y ^ 2 / C) : EReal) else ⊤) ''
            closure B) := by
        rw [EReal.neg_le_neg_iff]
        apply sInf_le
        exact ⟨a, ha_mem.1, by simp [ha0]⟩
  · have hpre : ∀ t, F t ⁻¹' B = ∅ := by
      intro t
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      exact hA ⟨F t ω, subset_closure hω, hF t ω⟩
    have heq :
        (fun t => ENNReal.log (μ (F t ⁻¹' B)) / (speed t : EReal)) =ᶠ[Filter.atTop]
          (fun _ => (⊥ : EReal)) := by
      filter_upwards [hpos] with t ht
      rw [hpre t]
      simp only [MeasureTheory.measure_empty, ENNReal.log_zero]
      have htc : (0 : EReal) < (speed t : EReal) := by
        exact_mod_cast ht
      exact EReal.bot_div_of_pos_ne_top htc (by simp)
    have hrate :
        sInf
            ((fun y : ℝ => if 0 ≤ y then (↑(y ^ 2 / C) : EReal) else ⊤) ''
              closure B) =
          ⊤ := by
      apply top_unique
      apply le_sInf
      intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      have hyneg : ¬ 0 ≤ y := by
        intro hy0
        exact hA ⟨y, hy, hy0⟩
      simp [hyneg]
    rw [Filter.limsup_congr heq, hrate]
    simp

@[blueprint "lem:clipped-sgd-ldp-core"
  (statement := /-- Let $(\Omega,\mathcal A,\mu)$ be a probability space with a
  filtration $(\mathcal F_t)_{t\in\mathbb N}$, let $d\in\mathbb N$, let
  $f:\mathbb R^d\to\mathbb R$, and let
  $x_t,g_t:\Omega\to\mathbb R^d$ for every $t\in\mathbb N$.  Fix
  $G,p,\sigma\in\mathbb R$ and $L\in\mathbb R_{\geq0}$.  Assume the nonconvex-cost,
  heavy-tail-noise, and clipped-SGD-run conditions of
  \cref{def:nonconvex-cost-assumptions,def:heavy-tail-noise-assumptions,
  def:clipped-sgd-run}; in particular, $1<p\leq2$.  Let Lean $x_k$ represent the
  paper iterate $x_{k+1}$, as specified by \cref{def:clipped-sgd-run}, and define
  $F_t=\min_{0\leq k<t}\lVert\nabla f(x_k)\rVert^2$, with $F_0=0$, as in
  \cref{def:best-iterate-gradient-squared}.  Thus $F_t$ is the paper statistic
  $\min_{1\leq j\leq t}\lVert\nabla f(x_j)\rVert^2$ for $t\geq1$.

  If $p<2$, then $(F_t)$ satisfies the LDP upper bound of
  \cref{def:ldp-upper-bound} with speed
  $t^{4(p-1)/(3p-2)}/\log t$ and rate function
  $y^2/(768G^4)$ on $[0,\infty)$ and $+\infty$ on $(-\infty,0)$.  If $p=2$, then
  $(F_t)$ satisfies the same upper bound with speed $t/(\log t)^2$ and rate
  function $y^2/(384G^4)$ on $[0,\infty)$ and $+\infty$ on $(-\infty,0)$. -/)
  (proof := /-- Obtain $b_t,u_t$ from
  \cref{lem:clipped-sgd-clipping-estimates}.  If $1<p<2$, apply
  \cref{lem:heavy-tail-schedule-asymptotics}; its first two conclusions give
  eventual positivity and divergence of the heavy-tail speed, and its third
  conclusion gives the required upper bound for every half-line $[y,\infty)$.
  The statistic $F_t$ is nonnegative because it is the minimum of squared norms,
  and $768G^4>0$ because $G>0$.  Consequently
  \cref{lem:ldp-upper-bound-of-one-sided-tail} gives the first asserted LDP upper
  bound, whose rate is definitionally
  \cref{def:heavy-tail-rate-function}.  If $p=2$, use
  \cref{lem:critical-schedule-asymptotics} in the same way and apply
  \cref{lem:ldp-upper-bound-of-one-sided-tail} with $C=384G^4$; the resulting
  rate is \cref{def:critical-rate-function}.  These two implications are the
  two conjuncts of the conclusion. -/)
  (title := /-- Large-deviation argument for clipped SGD -/)
  (latexEnv := "lemma")]
lemma clipped_sgd_ldp_core
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    {d : ℕ} (filtration : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x g : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (G : ℝ) (L : NNReal) (p σ : ℝ)
    (hcost : nonconvex_cost_assumptions f G L)
    (hnoise : heavy_tail_noise_assumptions μ filtration f x g p σ)
    (hrun : clipped_sgd_run μ filtration x g G p) :
    (p < 2 →
      ldp_upper_bound μ (best_iterate_gradient_squared f x)
        (heavy_tail_ldp_speed p) (heavy_tail_rate_function G)) ∧
    (p = 2 →
      ldp_upper_bound μ (best_iterate_gradient_squared f x)
        critical_ldp_speed (critical_rate_function G)) := by
  rcases clipped_sgd_clipping_estimates μ filtration f x g G L p σ hcost hnoise hrun with
    ⟨bias, centered, hest⟩
  have hF : ∀ t ω, 0 ≤ best_iterate_gradient_squared f x t ω := by
    intro t ω
    rw [best_iterate_gradient_squared]
    split_ifs with ht
    · exact (Finset.le_inf'_iff ht (fun k => ‖gradient f (x k ω)‖ ^ 2)).2
        (fun k hk => sq_nonneg _)
    · norm_num
  constructor
  · intro hp2
    rcases heavy_tail_schedule_asymptotics μ filtration f x g bias centered G L p σ
        hcost hnoise hrun hest hp2 with ⟨hpos, htendsto, htail⟩
    have hC : 0 < 768 * G ^ 4 := by
      have hG : 0 < G := hcost.1
      positivity
    change ldp_upper_bound μ (best_iterate_gradient_squared f x) (heavy_tail_ldp_speed p)
      (fun y => if 0 ≤ y then (↑(y ^ 2 / (768 * G ^ 4) : ℝ) : EReal) else ⊤)
    exact ldp_upper_bound_of_one_sided_tail μ (best_iterate_gradient_squared f x)
      (heavy_tail_ldp_speed p) (768 * G ^ 4) hF hC hpos htendsto htail
  · intro hp2
    rcases critical_schedule_asymptotics μ filtration f x g bias centered G L p σ
        hcost hnoise hrun hest hp2 with ⟨hpos, htendsto, htail⟩
    have hC : 0 < 384 * G ^ 4 := by
      have hG : 0 < G := hcost.1
      positivity
    change ldp_upper_bound μ (best_iterate_gradient_squared f x) critical_ldp_speed
      (fun y => if 0 ≤ y then (↑(y ^ 2 / (384 * G ^ 4) : ℝ) : EReal) else ⊤)
    exact ldp_upper_bound_of_one_sided_tail μ (best_iterate_gradient_squared f x)
      critical_ldp_speed (384 * G ^ 4) hF hC hpos htendsto htail

@[blueprint "thm:main-non-conv-clip"
  (statement := /-- Let $(\Omega,\mathcal A,\mu)$ be a probability space with a
  filtration $(\mathcal F_t)_{t\in\mathbb N}$, let $d\in\mathbb N$, let
  $f:\mathbb R^d\to\mathbb R$, and let
  $x_t,g_t:\Omega\to\mathbb R^d$ for every $t\in\mathbb N$.  Fix
  $G,p,\sigma\in\mathbb R$ and $L\in\mathbb R_{\geq0}$.  Assume the nonconvex-cost,
  heavy-tail-noise, and clipped-SGD-run conditions of
  \cref{def:nonconvex-cost-assumptions,def:heavy-tail-noise-assumptions,
  def:clipped-sgd-run}; in particular, $G>0$ and $1<p\leq2$.  Let Lean $x_k$
  represent the paper iterate $x_{k+1}$, as specified by
  \cref{def:clipped-sgd-run}, and define
  $F_t=\min_{0\leq k<t}\lVert\nabla f(x_k)\rVert^2$, with $F_0=0$, as in
  \cref{def:best-iterate-gradient-squared}.  Thus, for $t\geq1$, $F_t$ is the paper
  statistic $\min_{1\leq j\leq t}\lVert\nabla f(x_j)\rVert^2$.

  If $p<2$, then $(F_t)$ satisfies the LDP upper bound of
  \cref{def:ldp-upper-bound} with speed
  $t^{4(p-1)/(3p-2)}/\log t$ and rate function
  \[
    I_c(y)=\begin{cases}y^2/(768G^4),&y\geq0,\\+\infty,&y<0.\end{cases}
  \]
  If $p=2$, then $(F_t)$ satisfies the same upper bound with speed
  $t/(\log t)^2$ and rate function
  \[
    I_c(y)=\begin{cases}y^2/(384G^4),&y\geq0,\\+\infty,&y<0.\end{cases}
  \] -/)
  (proof := /-- Apply \cref{lem:clipped-sgd-ldp-core}, whose two conjuncts are exactly the
  claimed conclusions in the regimes $1<p<2$ and $p=2$, respectively. -/)
  (title := /-- LDP upper bound for clipped SGD under heavy-tailed noise -/)
  (latexEnv := "theorem")]
theorem main_non_conv_clip
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    {d : ℕ} (filtration : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x g : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (G : ℝ) (L : NNReal) (p σ : ℝ)
    (hcost : nonconvex_cost_assumptions f G L)
    (hnoise : heavy_tail_noise_assumptions μ filtration f x g p σ)
    (hrun : clipped_sgd_run μ filtration x g G p) :
    (p < 2 →
      ldp_upper_bound μ (best_iterate_gradient_squared f x)
        (heavy_tail_ldp_speed p) (heavy_tail_rate_function G)) ∧
    (p = 2 →
      ldp_upper_bound μ (best_iterate_gradient_squared f x)
        critical_ldp_speed (critical_rate_function G)) := by
  exact clipped_sgd_ldp_core μ filtration f x g G L p σ hcost hnoise hrun

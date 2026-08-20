import Architect
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Process.Filtration
import Mathlib.Algebra.Order.Chebyshev

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory

@[blueprint "def:adagrad-grad-coord"
  (statement := /-- Let $d \in \mathbb{N}$ and let $F : \mathbb{R}^d \to \mathbb{R}$. For
    $\mathbf{x} \in \mathbb{R}^d$ and $i \in [d]$ we write
    $\nabla_i F(\mathbf{x})$ for the value of the Fr\'echet derivative of $F$ at
    $\mathbf{x}$ applied to the $i$-th standard basis vector $\mathbf{e}_i$, that is, for
    the $i$-th partial derivative of $F$ at $\mathbf{x}$. If $F$ is not differentiable at
    $\mathbf{x}$ this quantity is $0$ by convention; throughout the sequel $F$ is assumed
    differentiable, so that $\nabla_i F(\mathbf{x})$ is the genuine $i$-th partial
    derivative and $\nabla F(\mathbf{x}) = (\nabla_1 F(\mathbf{x}), \dots,
    \nabla_d F(\mathbf{x}))$. -/)
  (title := /-- Coordinates of the gradient -/)
  (latexEnv := "definition")]
noncomputable def adagrad_grad_coord {d : ℕ} (F : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (i : Fin d) : ℝ :=
  fderiv ℝ F x (Pi.single i 1)

@[blueprint "def:adagrad-l1-norm"
  (statement := /-- For $d \in \mathbb{N}$ and $\mathbf{v} \in \mathbb{R}^d$ the
    $\ell_1$-norm of $\mathbf{v}$ is $\|\mathbf{v}\|_1 = \sum_{i=1}^d |v_i|$. -/)
  (title := /-- The $\ell_1$-norm -/)
  (latexEnv := "definition")]
def adagrad_l1_norm {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  ∑ i, |v i|

@[blueprint "def:adagrad-linf-norm"
  (statement := /-- For $d \in \mathbb{N}$ and $\mathbf{v} \in \mathbb{R}^d$ the max-norm
    of $\mathbf{v}$ is $\|\mathbf{v}\|_\infty = \sup_{1 \le i \le d} |v_i|$, with the
    convention that the supremum of the empty family of reals is $0$, so that
    $\|\mathbf{v}\|_\infty = \max_{1 \le i \le d} |v_i|$ whenever $d \ge 1$. -/)
  (title := /-- The max-norm -/)
  (latexEnv := "definition")]
noncomputable def adagrad_linf_norm {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  ⨆ i, |v i|

@[blueprint "def:adagrad-setting"
  (statement := /-- An \emph{AdaGrad setting} consists of the following data.

    A dimension $d \ge 1$, a horizon $T \ge 1$, a scaling parameter $\eta > 0$ and a
    numerical-stability constant $\delta$ with $0 < \delta < 1/d$; an objective
    $F : \mathbb{R}^d \to \mathbb{R}$ which is Fr\'echet differentiable at every point;
    a real number $F^*$ with $F^* \le F(\mathbf{x})$ for all $\mathbf{x} \in \mathbb{R}^d$,
    which is Assumption~\emph{lower\_bounded} in the form in which the argument uses it;
    vectors $\mathbf{L} = (L_1, \dots, L_d)$ and $\bm\sigma = (\sigma_1, \dots, \sigma_d)$
    of nonnegative reals; and the coordinate-wise smoothness Assumption
    \emph{Lsmooth}, namely
    $$\Bigl| F(\mathbf{y}) - F(\mathbf{x})
      - \sum_{i=1}^d \nabla_i F(\mathbf{x}) (y_i - x_i) \Bigr|
      \le \sum_{i=1}^d \frac{L_i}{2} (x_i - y_i)^2
      \qquad \text{for all } \mathbf{x}, \mathbf{y} \in \mathbb{R}^d .$$

    A probability space $(\Omega, \mathcal{A}, \mathbb{P})$ together with a filtration
    $(\mathcal{F}_t)_{t \ge 0}$ of sub-$\sigma$-algebras of $\mathcal{A}$; a process
    $(\mathbf{w}_t)_{t \ge 1}$ of iterates and a process $(\mathbf{g}_t)_{t \ge 1}$ of
    stochastic gradients, both with values in $\mathbb{R}^d$, such that
    $\mathbf{w}_{t+1}$ is $\mathcal{F}_t$-measurable and $\mathbf{g}_t$ is
    $\mathcal{F}_t$-measurable for every $t$, such that every $g_{t,i}$ and every
    $g_{t,i}^2$ is integrable and every $F(\mathbf{w}_t)$ is integrable, and such that
    $\mathbf{w}_1$ is the deterministic point $\mathbf{w}_1 \in \mathbb{R}^d$.

    The iterates obey the coordinate-wise AdaGrad recursion: for every $t \ge 1$ and
    every $i \in [d]$,
    $$w_{t+1,i} = w_{t,i} - \eta \frac{g_{t,i}}{b_{t,i} + \delta},
      \qquad b_{t,i} = \sqrt{\sum_{s=1}^t g_{s,i}^2} .$$

    Finally, the stochastic gradients satisfy Assumption \emph{unbiased}, namely
    $\mathbb{E}[g_{t,i} \mid \mathcal{F}_{t-1}] = \nabla_i F(\mathbf{w}_t)$ almost surely
    for every $t \ge 1$ and every $i \in [d]$, and Assumption
    \emph{bounded-variance}, namely
    $\mathbb{E}[(g_{t,i} - \nabla_i F(\mathbf{w}_t))^2 \mid \mathcal{F}_{t-1}]
    \le \sigma_i^2$ almost surely for every $t \ge 1$ and every $i \in [d]$. Here
    $\nabla_i F$ is as in \cref{def:adagrad-grad-coord}. -/)
  (title := /-- The AdaGrad setting -/)
  (latexEnv := "definition")]
structure adagrad_setting (Ω : Type) [mΩ : MeasurableSpace Ω] where
  μ : Measure Ω
  isProbabilityMeasure : IsProbabilityMeasure μ
  ℱ : Filtration ℕ mΩ
  d : ℕ
  one_le_d : 1 ≤ d
  T : ℕ
  one_le_T : 1 ≤ T
  η : ℝ
  eta_pos : 0 < η
  δ : ℝ
  delta_pos : 0 < δ
  delta_lt : δ < 1 / (d : ℝ)
  obj : (Fin d → ℝ) → ℝ
  obj_differentiable : Differentiable ℝ obj
  objMin : ℝ
  obj_lower_bounded : ∀ x, objMin ≤ obj x
  L : Fin d → ℝ
  L_nonneg : ∀ i, 0 ≤ L i
  σ : Fin d → ℝ
  sigma_nonneg : ∀ i, 0 ≤ σ i
  obj_smooth : ∀ x y : Fin d → ℝ,
    |obj y - obj x - ∑ i, adagrad_grad_coord obj x i * (y i - x i)|
      ≤ ∑ i, L i / 2 * (x i - y i) ^ 2
  w : ℕ → Ω → Fin d → ℝ
  g : ℕ → Ω → Fin d → ℝ
  init : Fin d → ℝ
  w_one : ∀ ω, w 1 ω = init
  w_adapted : ∀ t : ℕ, Measurable[ℱ t] fun ω => w (t + 1) ω
  g_adapted : ∀ t : ℕ, Measurable[ℱ t] fun ω => g t ω
  g_integrable : ∀ (t : ℕ) (i : Fin d), Integrable (fun ω => g t ω i) μ
  g_sq_integrable : ∀ (t : ℕ) (i : Fin d), Integrable (fun ω => g t ω i ^ 2) μ
  obj_integrable : ∀ t : ℕ, Integrable (fun ω => obj (w t ω)) μ
  adagrad_update : ∀ t : ℕ, 1 ≤ t → ∀ (ω : Ω) (i : Fin d),
    w (t + 1) ω i
      = w t ω i - η * (g t ω i / (Real.sqrt (∑ s ∈ Finset.Icc 1 t, g s ω i ^ 2) + δ))
  g_unbiased : ∀ t : ℕ, 1 ≤ t → ∀ i : Fin d,
    μ[fun ω => g t ω i|ℱ (t - 1)] =ᵐ[μ] fun ω => adagrad_grad_coord obj (w t ω) i
  g_bounded_variance : ∀ t : ℕ, 1 ≤ t → ∀ i : Fin d,
    μ[fun ω => (g t ω i - adagrad_grad_coord obj (w t ω) i) ^ 2|ℱ (t - 1)]
      ≤ᵐ[μ] fun _ => σ i ^ 2

@[blueprint "def:adagrad-step"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting}. For
    $t \ge 1$, $i \in [d]$ and a sample point $\omega$, the \emph{effective step size} of
    coordinate $i$ at time $t$ is
    $$\eta_{t,i} = \frac{\eta}{b_{t,i} + \delta},
      \qquad b_{t,i} = \sqrt{\sum_{s=1}^t g_{s,i}^2},$$
    so that the AdaGrad recursion of \cref{def:adagrad-setting} reads
    $w_{t+1,i} = w_{t,i} - \eta_{t,i} g_{t,i}$. -/)
  (title := /-- The effective step size $\eta_{t,i}$ -/)
  (latexEnv := "definition")]
noncomputable def adagrad_step {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (ω : Ω) (t : ℕ) (i : Fin S.d) : ℝ :=
  S.η / (Real.sqrt (∑ s ∈ Finset.Icc 1 t, S.g s ω i ^ 2) + S.δ)

@[blueprint "def:adagrad-decorrelated-step"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting}. For
    $t \ge 1$, $i \in [d]$ and a sample point $\omega$, the \emph{decorrelated step size}
    of coordinate $i$ at time $t$ is
    $$\hat\eta_{t,i}
      = \frac{\eta}{\sqrt{\,b_{t-1,i}^2 + \sigma_i^2 + \nabla_i F(\mathbf{w}_t)^2\,}
        + \delta},
      \qquad b_{t-1,i}^2 = \sum_{s=1}^{t-1} g_{s,i}^2 .$$
    Unlike $\eta_{t,i}$ of \cref{def:adagrad-step}, the quantity $\hat\eta_{t,i}$ does not
    depend on the noise in $\mathbf{g}_t$, so that $\hat\eta_{t,i}$ and $g_{t,i}$ are
    conditionally decorrelated given $\mathcal{F}_{t-1}$. -/)
  (title := /-- The decorrelated step size $\hat\eta_{t,i}$ -/)
  (latexEnv := "definition")]
noncomputable def adagrad_decorrelated_step {Ω : Type} [MeasurableSpace Ω]
    (S : adagrad_setting Ω) (ω : Ω) (t : ℕ) (i : Fin S.d) : ℝ :=
  S.η / (Real.sqrt ((∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2) + S.σ i ^ 2
    + adagrad_grad_coord S.obj (S.w t ω) i ^ 2) + S.δ)

@[blueprint "def:adagrad-aux-step"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting}. For
    $i \in [d]$ and a sample point $\omega$, the \emph{auxiliary step size} of coordinate
    $i$ at the horizon $T$ is
    $$\tilde\eta_{T,i}
      = \frac{\eta}{\sqrt{\,b_{T-1,i}^2 + \sigma_i^2
        + \sum_{t=1}^T \nabla_i F(\mathbf{w}_t)^2\,} + \delta},
      \qquad b_{T-1,i}^2 = \sum_{s=1}^{T-1} g_{s,i}^2 .$$
    It is obtained from $\hat\eta_{t,i}$ of \cref{def:adagrad-decorrelated-step} at
    $t = T$ by replacing the single term $\nabla_i F(\mathbf{w}_T)^2$ by the full sum
    $\sum_{t=1}^T \nabla_i F(\mathbf{w}_t)^2$; consequently
    $\tilde\eta_{T,i} \le \hat\eta_{t,i}$ for every $t \le T$. -/)
  (title := /-- The auxiliary step size $\tilde\eta_{T,i}$ -/)
  (latexEnv := "definition")]
noncomputable def adagrad_aux_step {Ω : Type} [MeasurableSpace Ω]
    (S : adagrad_setting Ω) (ω : Ω) (i : Fin S.d) : ℝ :=
  S.η / (Real.sqrt ((∑ s ∈ Finset.Icc 1 (S.T - 1), S.g s ω i ^ 2) + S.σ i ^ 2
    + ∑ t ∈ Finset.Icc 1 S.T, adagrad_grad_coord S.obj (S.w t ω) i ^ 2) + S.δ)

@[blueprint "def:adagrad-gap"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting}. Its
    \emph{initial suboptimality gap} is $\Delta_F = F(\mathbf{w}_1) - F^*$, where
    $\mathbf{w}_1$ is the deterministic initialisation of $S$. It satisfies
    $\Delta_F \ge 0$ because $F^*$ lower bounds $F$. -/)
  (title := /-- The initial suboptimality gap $\Delta_F$ -/)
  (latexEnv := "definition")]
noncomputable def adagrad_gap {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω) : ℝ :=
  S.obj S.init - S.objMin

@[blueprint "def:adagrad-h"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting}. Put
    $$h(T) = \frac{T \|\bm\sigma\|_\infty^2 + T \|\nabla F(\mathbf{w}_1)\|_\infty^2
      + \eta^2 \|\mathbf{L}\|_\infty \|\mathbf{L}\|_1 T^3}{\delta^2},$$
    where the norms are those of \cref{def:adagrad-l1-norm} and
    \cref{def:adagrad-linf-norm} and $\nabla F$ is as in
    \cref{def:adagrad-grad-coord}. The quantity appearing in the main theorem is
    $\bigO(h(T))$; the hidden absolute constant is carried explicitly by
    \cref{def:adagrad-log-budget}, which also normalises the logarithm so that it is
    nonnegative. Since $\eta > 0$, $\delta > 0$ and the norms of
    \cref{def:adagrad-l1-norm} and \cref{def:adagrad-linf-norm} are nonnegative, one has
    $h(T) \ge 0$ for every setting. -/)
  (title := /-- The polynomial $h(T)$ -/)
  (latexEnv := "definition")]
noncomputable def adagrad_h {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω) : ℝ :=
  ((S.T : ℝ) * adagrad_linf_norm S.σ ^ 2
      + (S.T : ℝ) * adagrad_linf_norm (fun i => adagrad_grad_coord S.obj S.init i) ^ 2
      + S.η ^ 2 * adagrad_linf_norm S.L * adagrad_l1_norm S.L * (S.T : ℝ) ^ 3) / S.δ ^ 2

@[blueprint "def:adagrad-log-budget"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting} and let
    $c \ge 1$ be a real number. The \emph{logarithmic budget} of $S$ with constant $c$ is
    $$\Lambda_c(S) = \log\bigl(c \cdot (1 + h(T))\bigr),$$
    with $h(T)$ as in \cref{def:adagrad-h}. The parameter $c$ records the absolute
    constant hidden in the assertion $h(T) = \bigO(\cdot)$ of the main theorem: the
    statements below assert the existence of one such $c$, uniform over all AdaGrad
    settings.

    Every summand in the numerator of $h(T)$ is nonnegative and $\delta > 0$ by
    \cref{def:adagrad-setting}, so $h(T) \ge 0$ and hence $c \cdot (1 + h(T)) \ge c \ge 1$;
    consequently $\Lambda_c(S) \ge 0$ for every setting $S$ and every $c \ge 1$, and
    $\Lambda_c(S) \ge 1$ as soon as $c \ge e$. This normalisation is the reading under
    which the source's estimates are to be understood: there $\log h(T)$ occurs only as an
    upper bound for nonnegative quantities, and $h(T)$ is itself prescribed only up to an
    absolute multiplicative constant. It does not alter the asymptotic content of those
    estimates, since for $h(T) \ge 1$ one has
    $\log(c\,h(T)) \le \log\bigl(c(1 + h(T))\bigr) \le \log(c\,h(T)) + \log 2$, so the two
    quantities differ by $\bigO(1)$ uniformly over all settings. -/)
  (title := /-- The logarithmic budget $\log h(T)$ -/)
  (latexEnv := "definition")]
noncomputable def adagrad_log_budget {Ω : Type} [MeasurableSpace Ω]
    (S : adagrad_setting Ω) (c : ℝ) : ℝ :=
  Real.log (c * (1 + adagrad_h S))

@[blueprint "def:adagrad-gradient-budget"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting} and let
    $c \ge 1$. The \emph{gradient budget} of $S$ with constant $c$ is
    $$Q_c(S) = \Delta_F
      + \Bigl(2 \eta \|\bm\sigma\|_1 + \frac{\eta^2 \|\mathbf{L}\|_1}{2}\Bigr)
        \Lambda_c(S),$$
    where $\Delta_F$ is as in \cref{def:adagrad-gap}, $\Lambda_c(S)$ is as in
    \cref{def:adagrad-log-budget} and $\|\cdot\|_1$ is as in
    \cref{def:adagrad-l1-norm}. It is the quantity that bounds the expected weighted sum
    of squared gradients along the trajectory. It is nonnegative: $\Delta_F \ge 0$ by
    \cref{def:adagrad-gap}, the coefficient
    $2 \eta \|\bm\sigma\|_1 + \frac{\eta^2 \|\mathbf{L}\|_1}{2}$ is nonnegative because
    $\eta > 0$ and the norms of \cref{def:adagrad-l1-norm} are nonnegative, and
    $\Lambda_c(S) \ge 0$ by the normalisation recorded in
    \cref{def:adagrad-log-budget}. -/)
  (title := /-- The gradient budget $Q$ -/)
  (latexEnv := "definition")]
noncomputable def adagrad_gradient_budget {Ω : Type} [MeasurableSpace Ω]
    (S : adagrad_setting Ω) (c : ℝ) : ℝ :=
  adagrad_gap S
    + (2 * S.η * adagrad_l1_norm S.σ + S.η ^ 2 * adagrad_l1_norm S.L / 2)
      * adagrad_log_budget S c

@[blueprint "def:adagrad-stationarity"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting}. Its
    \emph{stationarity measure} is
    $$\mathcal{S}(S)
      = \mathbb{E}\Bigl[\frac{1}{T} \sum_{t=1}^T \|\nabla F(\mathbf{w}_t)\|_1\Bigr],$$
    with $\|\cdot\|_1$ as in \cref{def:adagrad-l1-norm} and $\nabla F$ as in
    \cref{def:adagrad-grad-coord}. This is the quantity bounded by the main
    theorem. -/)
  (title := /-- The stationarity measure -/)
  (latexEnv := "definition")]
noncomputable def adagrad_stationarity {Ω : Type} [MeasurableSpace Ω]
    (S : adagrad_setting Ω) : ℝ :=
  ∫ ω, (1 / (S.T : ℝ))
    * ∑ t ∈ Finset.Icc 1 S.T, adagrad_l1_norm (fun i => adagrad_grad_coord S.obj (S.w t ω) i)
    ∂S.μ

@[blueprint "lem:adagrad-per-step-amgm-bound"
  (statement := /-- Let $B,C,D,K\in\mathbb{R}$ with $B\ge0$ and $K\ge0$. If
    $sD\le B+sC+Ks^2$ for every $s>0$, then
    $D\le C+2\sqrt{BK}$. -/)
  (proof := /-- If $K=0$, apply the hypothesis with $s=(B+1)/\varepsilon$ and let
    $\varepsilon\downarrow0$. If $K>0$ and $B=0$, use
    $s=\varepsilon/(2K)$ and again let $\varepsilon\downarrow0$. Finally, if $B,K>0$,
    substitute $s=\sqrt{B}/\sqrt{K}$; then $Ks^2=B$ and
    $s\,2\sqrt{BK}=2B$, which gives the claimed inequality after division by $s>0$. -/)
  (title := /-- Optimisation of quadratic upper bounds -/)
  (latexEnv := "lemma")]
lemma adagrad_per_step_amgm_bound {B C D K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (h : ∀ s : ℝ, 0 < s → s * D ≤ B + s * C + K * s ^ 2) :
    D ≤ C + 2 * Real.sqrt (B * K) := by
  rcases eq_or_lt_of_le hK with hK0 | hKpos
  · subst hK0
    simp only [mul_zero, Real.sqrt_zero, mul_zero, add_zero] at h ⊢
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    have hs : 0 < (B + 1) / ε := by positivity
    have h2 := h _ hs
    have hsε : (B + 1) / ε * ε = B + 1 := by field_simp
    refine le_of_mul_le_mul_left ?_ hs
    calc (B + 1) / ε * D ≤ B + (B + 1) / ε * C := by nlinarith [h2]
      _ ≤ (B + 1) / ε * (C + ε) := by rw [mul_add, hsε]; linarith
  · rcases eq_or_lt_of_le hB with hB0 | hBpos
    · subst hB0
      simp only [zero_mul, Real.sqrt_zero, mul_zero, add_zero, zero_add] at h ⊢
      refine le_of_forall_pos_le_add ?_
      intro ε hε
      have hs : 0 < ε / (2 * K) := by positivity
      have h2 := h _ hs
      have hKs : K * (ε / (2 * K)) ^ 2 = ε / (2 * K) * (ε / 2) := by
        field_simp
      refine le_of_mul_le_mul_left ?_ hs
      calc ε / (2 * K) * D ≤ ε / (2 * K) * C + K * (ε / (2 * K)) ^ 2 := h2
        _ = ε / (2 * K) * C + ε / (2 * K) * (ε / 2) := by rw [hKs]
        _ ≤ ε / (2 * K) * (C + ε) := by rw [mul_add]; nlinarith
    · have hsb : 0 < Real.sqrt B := Real.sqrt_pos.2 hBpos
      have hsk : 0 < Real.sqrt K := Real.sqrt_pos.2 hKpos
      have hs : 0 < Real.sqrt B / Real.sqrt K := by positivity
      have h2 := h _ hs
      have hB' : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB
      have hK' : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK
      have hKs : K * (Real.sqrt B / Real.sqrt K) ^ 2 = B := by
        rw [div_pow, hB', hK']
        field_simp
      have hprod : Real.sqrt B / Real.sqrt K * (2 * Real.sqrt (B * K)) = 2 * B := by
        rw [Real.sqrt_mul hB]
        field_simp
        nlinarith [hB']
      rw [hKs] at h2
      refine le_of_mul_le_mul_left ?_ hs
      rw [mul_add, hprod]
      linarith

@[blueprint "lem:adagrad-per-step-grad-shift"
  (statement := /-- Let $S$ be an AdaGrad setting, let $\mathbf y\in\mathbb{R}^d$,
    $i\in[d]$, and $s\in\mathbb{R}$. If $\mathbf y'$ is obtained by replacing $y_i$ by
    $y_i+s$, then
    $\lvert F(\mathbf y')-F(\mathbf y)-s\nabla_iF(\mathbf y)\rvert
      \le (L_i/2)s^2$. -/)
  (proof := /-- Apply the coordinate smoothness condition in
    \cref{def:adagrad-setting} to $\mathbf y$ and its coordinate update. Every summand
    except the $i$th vanishes; the linear sum is
    $s\nabla_iF(\mathbf y)$ and the quadratic sum is $(L_i/2)s^2$. -/)
  (title := /-- Smoothness along one coordinate -/)
  (latexEnv := "lemma")]
lemma adagrad_per_step_grad_shift {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (y : Fin S.d → ℝ) (i : Fin S.d) (s : ℝ) :
    |S.obj (Function.update y i (y i + s)) - S.obj y
        - s * adagrad_grad_coord S.obj y i|
      ≤ S.L i / 2 * s ^ 2 := by
  have h := S.obj_smooth y (Function.update y i (y i + s))
  have h1 : ∑ j, adagrad_grad_coord S.obj y j * (Function.update y i (y i + s) j - y j)
      = s * adagrad_grad_coord S.obj y i := by
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · simp [mul_comm]
    · intro j _ hj
      simp [Function.update_of_ne hj]
  have h2 : ∑ j, S.L j / 2 * (y j - Function.update y i (y i + s) j) ^ 2
      = S.L i / 2 * s ^ 2 := by
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · simp
    · intro j _ hj
      simp [Function.update_of_ne hj]
  rw [h1] at h
  rw [h2] at h
  exact h

@[blueprint "lem:adagrad-per-step-grad-diff"
  (statement := /-- For an AdaGrad setting $S$, points $\mathbf x,\mathbf y\in\mathbb R^d$,
    and $i\in[d]$,
    $(\nabla_iF(\mathbf y)-\nabla_iF(\mathbf x))^2
      \le 9L_i\sum_jL_j(x_j-y_j)^2$. -/)
  (proof := /-- Put $B=\sum_jL_j(x_j-y_j)^2$. Applying coordinate smoothness at
    $\mathbf x$ to $\mathbf y$ and to the point obtained by shifting $y_i$ by $s>0$,
    and applying \cref{lem:adagrad-per-step-grad-shift} at $\mathbf y$, gives
    $s|\nabla_iF(\mathbf y)-\nabla_iF(\mathbf x)|
      \le B+sL_i|x_i-y_i|+L_is^2$.
    The optimisation lemma \cref{lem:adagrad-per-step-amgm-bound} yields an upper bound
    by $L_i|x_i-y_i|+2\sqrt{BL_i}$. Since
    $L_i(x_i-y_i)^2\le B$, this is at most $3\sqrt{L_i}\sqrt B$; squaring proves the
    assertion. -/)
  (title := /-- Coordinate Lipschitz estimate for the gradient -/)
  (latexEnv := "lemma")]
lemma adagrad_per_step_grad_diff {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (x y : Fin S.d → ℝ) (i : Fin S.d) :
    (adagrad_grad_coord S.obj y i - adagrad_grad_coord S.obj x i) ^ 2
      ≤ 9 * S.L i * ∑ j, S.L j * (x j - y j) ^ 2 := by
  set B : ℝ := ∑ j, S.L j * (x j - y j) ^ 2 with hBdef
  have hB : 0 ≤ B := Finset.sum_nonneg fun j _ => by
    have := S.L_nonneg j
    positivity
  have hLi : 0 ≤ S.L i := S.L_nonneg i
  have hBi : S.L i * (x i - y i) ^ 2 ≤ B :=
    Finset.single_le_sum (f := fun j => S.L j * (x j - y j) ^ 2)
      (fun j _ => by have := S.L_nonneg j; positivity) (Finset.mem_univ i)
  have hhalf : ∑ j, S.L j / 2 * (x j - y j) ^ 2 = B / 2 := by
    rw [hBdef, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  have key : ∀ s : ℝ, 0 < s →
      s * |adagrad_grad_coord S.obj y i - adagrad_grad_coord S.obj x i|
        ≤ B + s * (S.L i * |x i - y i|) + S.L i * s ^ 2 := by
    intro s hs
    have hy' := S.obj_smooth x (Function.update y i (y i + s))
    have hy := S.obj_smooth x y
    have hshift := adagrad_per_step_grad_shift S y i s
    have hlin : ∑ j, adagrad_grad_coord S.obj x j
          * (Function.update y i (y i + s) j - x j)
        = (∑ j, adagrad_grad_coord S.obj x j * (y j - x j))
          + s * adagrad_grad_coord S.obj x i := by
      have hd : ∑ j, (adagrad_grad_coord S.obj x j
            * (Function.update y i (y i + s) j - x j)
          - adagrad_grad_coord S.obj x j * (y j - x j))
          = s * adagrad_grad_coord S.obj x i := by
        rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
        · simp
          ring
        · intro j _ hj
          simp [Function.update_of_ne hj]
      rw [Finset.sum_sub_distrib] at hd
      linarith
    have hquad : ∑ j, S.L j / 2 * (x j - Function.update y i (y i + s) j) ^ 2
        = B / 2 + S.L i / 2 * (s ^ 2 - 2 * s * (x i - y i)) := by
      have hd : ∑ j, (S.L j / 2 * (x j - Function.update y i (y i + s) j) ^ 2
          - S.L j / 2 * (x j - y j) ^ 2)
          = S.L i / 2 * (s ^ 2 - 2 * s * (x i - y i)) := by
        rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
        · simp
          ring
        · intro j _ hj
          simp [Function.update_of_ne hj]
      rw [Finset.sum_sub_distrib] at hd
      linarith [hhalf]
    rw [hlin, hquad] at hy'
    rw [hhalf] at hy
    have habs1 := abs_le.1 hy'
    have habs2 := abs_le.1 hy
    have habs3 := abs_le.1 hshift
    have hcross : -(S.L i * s * (x i - y i)) ≤ s * (S.L i * |x i - y i|) := by
      have h1 : -(x i - y i) ≤ |x i - y i| := neg_le_abs _
      nlinarith [mul_nonneg hLi hs.le]
    rcases abs_cases (adagrad_grad_coord S.obj y i - adagrad_grad_coord S.obj x i)
      with ⟨heq, _⟩ | ⟨heq, _⟩
    · rw [heq]
      nlinarith [habs1.1, habs1.2, habs2.1, habs2.2, habs3.1, habs3.2, hcross]
    · rw [heq]
      nlinarith [habs1.1, habs1.2, habs2.1, habs2.2, habs3.1, habs3.2, hcross]
  have hD := adagrad_per_step_amgm_bound (B := B) (C := S.L i * |x i - y i|)
    (D := |adagrad_grad_coord S.obj y i - adagrad_grad_coord S.obj x i|)
    (K := S.L i) hB hLi key
  have hsL : Real.sqrt (S.L i) ^ 2 = S.L i := Real.sq_sqrt hLi
  have hsB : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB
  have hsL0 : 0 ≤ Real.sqrt (S.L i) := Real.sqrt_nonneg _
  have hsB0 : 0 ≤ Real.sqrt B := Real.sqrt_nonneg _
  have hmul : Real.sqrt (B * S.L i) = Real.sqrt B * Real.sqrt (S.L i) :=
    Real.sqrt_mul hB _
  have hlin2 : S.L i * |x i - y i| ≤ Real.sqrt (S.L i) * Real.sqrt B := by
    have h1 : Real.sqrt (S.L i * (x i - y i) ^ 2) ≤ Real.sqrt B :=
      Real.sqrt_le_sqrt hBi
    have h2 : Real.sqrt (S.L i * (x i - y i) ^ 2)
        = Real.sqrt (S.L i) * |x i - y i| := by
      rw [Real.sqrt_mul hLi, Real.sqrt_sq_eq_abs]
    rw [h2] at h1
    nlinarith [abs_nonneg (x i - y i), mul_le_mul_of_nonneg_left h1 hsL0]
  have hfinal : |adagrad_grad_coord S.obj y i - adagrad_grad_coord S.obj x i|
      ≤ 3 * (Real.sqrt (S.L i) * Real.sqrt B) := by
    rw [hmul] at hD
    nlinarith
  have hsq := sq_abs (adagrad_grad_coord S.obj y i - adagrad_grad_coord S.obj x i)
  nlinarith [abs_nonneg (adagrad_grad_coord S.obj y i - adagrad_grad_coord S.obj x i),
    mul_nonneg hsL0 hsB0]

@[blueprint "lem:adagrad-per-step-iterate-dist"
  (statement := /-- For every AdaGrad setting $S$, sample point $\omega$, coordinate
    $j\in[d]$, and $t\ge1$,
    $|w_{t,j}(\omega)-w_{1,j}|\le\eta(t-1)$. -/)
  (proof := /-- Induct on $t$. The base case is the deterministic initialisation in
    \cref{def:adagrad-setting}. At the induction step, the current squared stochastic
    gradient is one summand of $b_{t,j}^2$, so $|g_{t,j}|\le b_{t,j}$. Since
    $\delta>0$, the AdaGrad update therefore moves coordinate $j$ by at most $\eta$.
    The triangle inequality and the induction hypothesis finish the step. -/)
  (title := /-- Displacement of the iterates -/)
  (latexEnv := "lemma")]
lemma adagrad_per_step_iterate_dist {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (ω : Ω) (j : Fin S.d) (t : ℕ) (ht : 1 ≤ t) :
    |S.w t ω j - S.init j| ≤ S.η * ((t : ℝ) - 1) := by
  induction t, ht using Nat.le_induction with
  | base => simp [S.w_one ω]
  | succ n hn ih =>
    have hb : |S.g n ω j| ≤ Real.sqrt (∑ s ∈ Finset.Icc 1 n, S.g s ω j ^ 2) := by
      have hmem : n ∈ Finset.Icc 1 n := Finset.mem_Icc.2 ⟨hn, le_rfl⟩
      have hle : S.g n ω j ^ 2 ≤ ∑ s ∈ Finset.Icc 1 n, S.g s ω j ^ 2 :=
        Finset.single_le_sum (f := fun s => S.g s ω j ^ 2)
          (fun s _ => sq_nonneg _) hmem
      calc |S.g n ω j| = Real.sqrt (S.g n ω j ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ _ := Real.sqrt_le_sqrt hle
    have hden : (0 : ℝ) <
        Real.sqrt (∑ s ∈ Finset.Icc 1 n, S.g s ω j ^ 2) + S.δ := by
      have := Real.sqrt_nonneg (∑ s ∈ Finset.Icc 1 n, S.g s ω j ^ 2)
      linarith [S.delta_pos]
    have hstep : |S.w (n + 1) ω j - S.w n ω j| ≤ S.η := by
      rw [S.adagrad_update n hn ω j]
      have hq : |S.g n ω j /
          (Real.sqrt (∑ s ∈ Finset.Icc 1 n, S.g s ω j ^ 2) + S.δ)| ≤ 1 := by
        rw [abs_div, abs_of_pos hden, div_le_one hden]
        linarith [S.delta_pos]
      have hmul : |S.η * (S.g n ω j /
          (Real.sqrt (∑ s ∈ Finset.Icc 1 n, S.g s ω j ^ 2) + S.δ))| ≤ S.η * 1 := by
        rw [abs_mul, abs_of_pos S.eta_pos]
        exact mul_le_mul_of_nonneg_left hq S.eta_pos.le
      simpa [abs_sub_comm] using hmul
    have hsum : |S.w (n + 1) ω j - S.init j|
        ≤ |S.w (n + 1) ω j - S.w n ω j| + |S.w n ω j - S.init j| :=
      abs_sub_le _ _ _
    push_cast
    linarith [hsum, hstep, ih]

@[blueprint "lem:adagrad-per-step-grad-bound"
  (statement := /-- For every AdaGrad setting $S$, sample point $\omega$, coordinate
    $i\in[d]$, and $t\ge1$,
    $$\nabla_iF(\mathbf w_t(\omega))^2
      \le 2\nabla_iF(\mathbf w_1)^2
        +18L_i\|\mathbf L\|_1\eta^2(t-1)^2.$$ -/)
  (proof := /-- Apply \cref{lem:adagrad-per-step-grad-diff} to the initial point and
    $\mathbf w_t(\omega)$. By \cref{lem:adagrad-per-step-iterate-dist}, every coordinate
    displacement is at most $\eta(t-1)$. Multiplying the squared bounds by the
    nonnegative $L_j$ and summing gives
    $\sum_jL_j(w_{1,j}-w_{t,j})^2\le\|\mathbf L\|_1\eta^2(t-1)^2$.
    Finally use $a^2\le2(a-b)^2+2b^2$ for the current and initial gradients. -/)
  (title := /-- Deterministic bound on trajectory gradients -/)
  (latexEnv := "lemma")]
lemma adagrad_per_step_grad_bound {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (ω : Ω) (i : Fin S.d) (t : ℕ) (ht : 1 ≤ t) :
    adagrad_grad_coord S.obj (S.w t ω) i ^ 2
      ≤ 2 * adagrad_grad_coord S.obj S.init i ^ 2
        + 18 * S.L i * adagrad_l1_norm S.L * S.η ^ 2 * ((t : ℝ) - 1) ^ 2 := by
  have hdiff := adagrad_per_step_grad_diff S S.init (S.w t ω) i
  have ht1 : (0 : ℝ) ≤ (t : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    linarith
  have hbound : ∑ j, S.L j * (S.init j - S.w t ω j) ^ 2
      ≤ adagrad_l1_norm S.L * (S.η ^ 2 * ((t : ℝ) - 1) ^ 2) := by
    rw [adagrad_l1_norm, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    have hdist := adagrad_per_step_iterate_dist S ω j t ht
    have hsq : (S.init j - S.w t ω j) ^ 2 ≤ (S.η * ((t : ℝ) - 1)) ^ 2 := by
      have habs : |S.init j - S.w t ω j| ≤ S.η * ((t : ℝ) - 1) := by
        rw [abs_sub_comm]
        exact hdist
      have h0 : 0 ≤ S.η * ((t : ℝ) - 1) := mul_nonneg S.eta_pos.le ht1
      nlinarith [abs_nonneg (S.init j - S.w t ω j),
        sq_abs (S.init j - S.w t ω j)]
    rw [abs_of_nonneg (S.L_nonneg j)]
    calc S.L j * (S.init j - S.w t ω j) ^ 2
        ≤ S.L j * (S.η * ((t : ℝ) - 1)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (S.L_nonneg j)
      _ = S.L j * (S.η ^ 2 * ((t : ℝ) - 1) ^ 2) := by ring
  have hLi : 0 ≤ S.L i := S.L_nonneg i
  nlinarith [mul_le_mul_of_nonneg_left hbound
      (by positivity : (0 : ℝ) ≤ 9 * S.L i),
    sq_nonneg (adagrad_grad_coord S.obj (S.w t ω) i
      - 2 * adagrad_grad_coord S.obj S.init i)]

@[blueprint "lem:adagrad-per-step-memlp-g"
  (statement := /-- For every AdaGrad setting $S$, time $t$, and coordinate $i$, the
    stochastic-gradient coordinate $g_{t,i}$ belongs to $L^2(\mu)$. -/)
  (proof := /-- Adaptedness in \cref{def:adagrad-setting} makes $g_{t,i}$ ambient
    measurable. Its square is integrable by the same definition, so the standard
    characterisation of real-valued $L^2$ functions applies. -/)
  (title := /-- Square-integrability of stochastic gradients -/)
  (latexEnv := "lemma")]
lemma adagrad_per_step_memlp_g {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (i : Fin S.d) (t : ℕ) : MemLp (fun ω => S.g t ω i) 2 S.μ := by
  have hgm : Measurable (fun ω => S.g t ω i) :=
    (measurable_pi_apply i).comp ((S.g_adapted t).mono (S.ℱ.le t) le_rfl)
  exact (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).2 (S.g_sq_integrable t i)

@[blueprint "lem:adagrad-per-step-memlp-grad"
  (statement := /-- For every AdaGrad setting $S$, $t\ge1$, and coordinate $i$, the
    gradient coordinate $\nabla_iF(\mathbf w_t)$ belongs to $L^2(\mu)$. -/)
  (proof := /-- By \cref{lem:adagrad-per-step-memlp-g}, $g_{t,i}$ lies in $L^2$.
    Conditional expectation preserves $L^2$, and unbiasedness in
    \cref{def:adagrad-setting} identifies that conditional expectation almost everywhere
    with $\nabla_iF(\mathbf w_t)$. -/)
  (title := /-- Square-integrability of trajectory gradients -/)
  (latexEnv := "lemma")]
lemma adagrad_per_step_memlp_grad {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (i : Fin S.d) (t : ℕ) (ht : 1 ≤ t) :
    MemLp (fun ω => adagrad_grad_coord S.obj (S.w t ω) i) 2 S.μ := by
  haveI := S.isProbabilityMeasure
  exact (MemLp.condExp (m := S.ℱ (t - 1)) one_le_two
    (adagrad_per_step_memlp_g S i t)).ae_eq (S.g_unbiased t ht i)

@[blueprint "lem:adagrad-per-step-sqrt-dist"
  (statement := /-- If $p\ge0$ and $\sigma\ge0$, then for all $a,g\in\mathbb R$,
    $$\left|\sqrt{p+g^2}-\sqrt{p+\sigma^2+a^2}\right|
      \le |g-a|+\sigma.$$ -/)
  (proof := /-- The triangle inequalities give
    $|g|\le|a|+|g-a|$ and $|a|\le|g|+|g-a|$. Moreover
    $\sqrt{p+\sigma^2+a^2}\ge|a|$ and $\sqrt{p+g^2}\ge|g|$.
    Squaring the resulting nonnegative inequalities proves each of the two bounds
    obtained by removing the outer absolute value. -/)
  (title := /-- Distance between the two adaptive denominators -/)
  (latexEnv := "lemma")]
lemma adagrad_per_step_sqrt_dist {p a g σ : ℝ} (hp : 0 ≤ p) (hσ : 0 ≤ σ) :
    |Real.sqrt (p + g ^ 2) - Real.sqrt (p + σ ^ 2 + a ^ 2)| ≤ |g - a| + σ := by
  let r := Real.sqrt (p + g ^ 2)
  let q := Real.sqrt (p + σ ^ 2 + a ^ 2)
  let e := |g - a|
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have he0 : 0 ≤ e := abs_nonneg _
  have hr2 : r ^ 2 = p + g ^ 2 := Real.sq_sqrt (by positivity)
  have hq2 : q ^ 2 = p + σ ^ 2 + a ^ 2 := Real.sq_sqrt (by positivity)
  have hga : |g| ≤ |a| + e := by
    dsimp [e]
    have h := abs_sub_le g a 0
    simpa [add_comm] using h
  have hag : |a| ≤ |g| + e := by
    dsimp [e]
    have h := abs_sub_le a g 0
    simpa [add_comm, abs_sub_comm] using h
  have hqa : |a| ≤ q := by
    nlinarith [sq_abs a]
  have hrg : |g| ≤ r := by
    nlinarith [sq_abs g]
  have hrq : r ≤ q + e := by
    have hg2 : g ^ 2 ≤ (|a| + e) ^ 2 := by
      have h := mul_self_le_mul_self (abs_nonneg g) hga
      simpa [pow_two, sq_abs] using h
    have hsquares : r ^ 2 ≤ (q + e) ^ 2 := by
      nlinarith [sq_abs a, sq_nonneg σ]
    nlinarith [sq_nonneg (r + q + e)]
  have hqr : q ≤ r + e + σ := by
    have ha2 : a ^ 2 ≤ (|g| + e) ^ 2 := by
      have h := mul_self_le_mul_self (abs_nonneg a) hag
      simpa [pow_two, sq_abs] using h
    have hsquares : q ^ 2 ≤ (r + e + σ) ^ 2 := by
      nlinarith [sq_abs g]
    nlinarith [sq_nonneg (q + r + e + σ)]
  rw [abs_le]
  constructor <;> dsimp [r, q, e] at *
  · linarith
  · linarith

@[blueprint "lem:adagrad-per-step-step-bounds"
  (statement := /-- For an AdaGrad setting, a time $t\ge1$, coordinate $i$, and sample
    point $\omega$, both effective step sizes are positive and at most $\eta/\delta$,
    $\eta_{t,i}|g_{t,i}|\le\eta$,
    $\hat\eta_{t,i}|\nabla_iF(\mathbf w_t)|\le\eta$, and
    $$|\eta_{t,i}-\hat\eta_{t,i}|
      \le\frac{\eta_{t,i}\hat\eta_{t,i}}{\eta}
        (|g_{t,i}-\nabla_iF(\mathbf w_t)|+\sigma_i).$$ -/)
  (proof := /-- Every radicand is nonnegative and $\delta>0$, giving positivity and the
    bound $\eta/\delta$. The current square is a summand of the effective denominator,
    while the squared gradient is a summand of the decorrelated denominator, proving the
    two product bounds. Subtracting the two reciprocal denominators and applying
    \cref{lem:adagrad-per-step-sqrt-dist} gives the final estimate. -/)
  (title := /-- Bounds and comparison for the two step sizes -/)
  (latexEnv := "lemma")]
lemma adagrad_per_step_step_bounds {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (t : ℕ) (ht : 1 ≤ t) (i : Fin S.d) (ω : Ω) :
    0 < adagrad_step S ω t i ∧ adagrad_step S ω t i ≤ S.η / S.δ ∧
      adagrad_step S ω t i * |S.g t ω i| ≤ S.η ∧
      0 < adagrad_decorrelated_step S ω t i ∧
      adagrad_decorrelated_step S ω t i ≤ S.η / S.δ ∧
      adagrad_decorrelated_step S ω t i
          * |adagrad_grad_coord S.obj (S.w t ω) i| ≤ S.η ∧
      |adagrad_step S ω t i - adagrad_decorrelated_step S ω t i|
        ≤ adagrad_step S ω t i * adagrad_decorrelated_step S ω t i / S.η
          * (|S.g t ω i - adagrad_grad_coord S.obj (S.w t ω) i| + S.σ i) := by
  have hp : 0 ≤ ∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2 :=
    Finset.sum_nonneg fun s _ => sq_nonneg _
  have hp' : 0 ≤ ∑ s ∈ Finset.Icc 1 t, S.g s ω i ^ 2 :=
    Finset.sum_nonneg fun s _ => sq_nonneg _
  have hsplit : ∑ s ∈ Finset.Icc 1 t, S.g s ω i ^ 2
      = (∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2) + S.g t ω i ^ 2 := by
    conv_lhs => rw [← Nat.sub_add_cancel ht]
    rw [Finset.sum_Icc_succ_top (show 1 ≤ t - 1 + 1 by omega)]
    rw [Nat.sub_add_cancel ht]
  have hσ : 0 ≤ S.σ i := S.sigma_nonneg i
  have hd1 : 0 < Real.sqrt (∑ s ∈ Finset.Icc 1 t, S.g s ω i ^ 2) + S.δ := by
    linarith [Real.sqrt_nonneg (∑ s ∈ Finset.Icc 1 t, S.g s ω i ^ 2), S.delta_pos]
  have hd2 : 0 < Real.sqrt ((∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2)
      + S.σ i ^ 2 + adagrad_grad_coord S.obj (S.w t ω) i ^ 2) + S.δ := by
    have : 0 ≤ (∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2)
        + S.σ i ^ 2 + adagrad_grad_coord S.obj (S.w t ω) i ^ 2 := by positivity
    linarith [Real.sqrt_nonneg ((∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2)
      + S.σ i ^ 2 + adagrad_grad_coord S.obj (S.w t ω) i ^ 2), S.delta_pos]
  have hgroot : |S.g t ω i| ≤
      Real.sqrt (∑ s ∈ Finset.Icc 1 t, S.g s ω i ^ 2) := by
    have hle : S.g t ω i ^ 2 ≤ ∑ s ∈ Finset.Icc 1 t, S.g s ω i ^ 2 := by
      rw [hsplit]
      linarith
    calc |S.g t ω i| = Real.sqrt (S.g t ω i ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ _ := Real.sqrt_le_sqrt hle
  have haroot : |adagrad_grad_coord S.obj (S.w t ω) i| ≤
      Real.sqrt ((∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2)
        + S.σ i ^ 2 + adagrad_grad_coord S.obj (S.w t ω) i ^ 2) := by
    have hle : adagrad_grad_coord S.obj (S.w t ω) i ^ 2
        ≤ (∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2)
          + S.σ i ^ 2 + adagrad_grad_coord S.obj (S.w t ω) i ^ 2 := by
      nlinarith [hp, sq_nonneg (S.σ i)]
    calc |adagrad_grad_coord S.obj (S.w t ω) i|
          = Real.sqrt (adagrad_grad_coord S.obj (S.w t ω) i ^ 2) :=
            (Real.sqrt_sq_eq_abs _).symm
      _ ≤ _ := Real.sqrt_le_sqrt hle
  have hdist := adagrad_per_step_sqrt_dist hp hσ
    (a := adagrad_grad_coord S.obj (S.w t ω) i) (g := S.g t ω i)
  rw [← hsplit] at hdist
  unfold adagrad_step adagrad_decorrelated_step
  refine ⟨div_pos S.eta_pos hd1, ?_, ?_, div_pos S.eta_pos hd2, ?_, ?_, ?_⟩
  · exact div_le_div_of_nonneg_left S.eta_pos.le S.delta_pos
      (by linarith [Real.sqrt_nonneg (∑ s ∈ Finset.Icc 1 t, S.g s ω i ^ 2)])
  · rw [div_mul_eq_mul_div, div_le_iff₀ hd1]
    exact mul_le_mul_of_nonneg_left
      (by linarith [hgroot, S.delta_pos]) S.eta_pos.le
  · exact div_le_div_of_nonneg_left S.eta_pos.le S.delta_pos
      (by linarith [Real.sqrt_nonneg ((∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2)
        + S.σ i ^ 2 + adagrad_grad_coord S.obj (S.w t ω) i ^ 2)])
  · rw [div_mul_eq_mul_div, div_le_iff₀ hd2]
    exact mul_le_mul_of_nonneg_left
      (by linarith [haroot, S.delta_pos]) S.eta_pos.le
  · have heq :
        S.η / (Real.sqrt (∑ s ∈ Finset.Icc 1 t, S.g s ω i ^ 2) + S.δ)
            - S.η / (Real.sqrt ((∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2)
                + S.σ i ^ 2 + adagrad_grad_coord S.obj (S.w t ω) i ^ 2) + S.δ)
          = (S.η / (Real.sqrt (∑ s ∈ Finset.Icc 1 t, S.g s ω i ^ 2) + S.δ)
              * (S.η / (Real.sqrt ((∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2)
                + S.σ i ^ 2 + adagrad_grad_coord S.obj (S.w t ω) i ^ 2) + S.δ))
              / S.η)
            * (Real.sqrt ((∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2)
                + S.σ i ^ 2 + adagrad_grad_coord S.obj (S.w t ω) i ^ 2)
              - Real.sqrt (∑ s ∈ Finset.Icc 1 t, S.g s ω i ^ 2)) := by
        field_simp
        ring
    rw [heq, abs_mul]
    have hc : 0 ≤
        S.η / (Real.sqrt (∑ s ∈ Finset.Icc 1 t, S.g s ω i ^ 2) + S.δ)
          * (S.η / (Real.sqrt ((∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2)
            + S.σ i ^ 2 + adagrad_grad_coord S.obj (S.w t ω) i ^ 2) + S.δ))
          / S.η := by
      exact div_nonneg
        (mul_nonneg (div_nonneg S.eta_pos.le hd1.le) (div_nonneg S.eta_pos.le hd2.le))
        S.eta_pos.le
    rw [abs_of_nonneg hc, abs_sub_comm]
    exact mul_le_mul_of_nonneg_left hdist hc

@[blueprint "lem:adagrad-per-step-bias"
  (statement := /-- Let $S$ be an AdaGrad setting, $t\ge1$, and $i\in[d]$. Then
    $$\mathbb E\!\left[\frac{\hat\eta_{t,i}}2
      \nabla_iF(\mathbf w_t)^2\right]
      \le \mathbb E[\eta_{t,i}\nabla_iF(\mathbf w_t)g_{t,i}]
        +\frac{2\sigma_i}{\eta}\mathbb E[\eta_{t,i}^2g_{t,i}^2].$$ -/)
  (proof := /-- The functions $\nabla_iF(\mathbf w_t)$ and $g_{t,i}$ lie in $L^2$ by
    \cref{lem:adagrad-per-step-memlp-grad, lem:adagrad-per-step-memlp-g}. The former is
    bounded along the trajectory by \cref{lem:adagrad-per-step-grad-bound}. The
    denominator comparison in \cref{lem:adagrad-per-step-step-bounds} bounds
    $|\eta_{t,i}-\hat\eta_{t,i}|$ by the product of the two step sizes and
    $(|g_{t,i}-\nabla_iF(\mathbf w_t)|+\sigma_i)/\eta$.

    If $\sigma_i=0$, conditional bounded variance forces
    $g_{t,i}=\nabla_iF(\mathbf w_t)$ almost surely, and the assertion follows directly.
    Otherwise Young's inequality bounds the resulting bias product by half the
    decorrelated gradient term plus
    $(2\sigma_i/\eta)\eta_{t,i}^2g_{t,i}^2$. The conditional variance assumption in
    \cref{def:adagrad-setting} controls the first Young term after pulling out its bounded
    $\mathcal F_{t-1}$-measurable coefficient, while conditional unbiasedness identifies
    the decorrelated main term. Integrating these bounds gives the displayed inequality. -/)
  (title := /-- Bias estimate for the adaptive step -/)
  (latexEnv := "lemma")]
lemma adagrad_per_step_bias {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (t : ℕ) (ht : 1 ≤ t) (i : Fin S.d) :
    (∫ ω, adagrad_decorrelated_step S ω t i / 2
        * adagrad_grad_coord S.obj (S.w t ω) i ^ 2 ∂S.μ)
      ≤ (∫ ω, adagrad_step S ω t i
          * adagrad_grad_coord S.obj (S.w t ω) i * S.g t ω i ∂S.μ)
        + 2 * S.σ i / S.η
          * ∫ ω, adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2 ∂S.μ := by
  classical
  haveI := S.isProbabilityMeasure
  let a : Ω → ℝ := fun ω => adagrad_grad_coord S.obj (S.w t ω) i
  let z : Ω → ℝ := fun ω => S.g t ω i
  let α : Ω → ℝ := fun ω => adagrad_step S ω t i
  let β : Ω → ℝ := fun ω => adagrad_decorrelated_step S ω t i
  let e : Ω → ℝ := z - a
  let u : Ω → ℝ := α * z
  change (∫ ω, β ω / 2 * a ω ^ 2 ∂S.μ)
      ≤ (∫ ω, α ω * a ω * z ω ∂S.μ)
        + 2 * S.σ i / S.η * ∫ ω, α ω ^ 2 * z ω ^ 2 ∂S.μ
  have hz2 : MemLp z 2 S.μ := by
    simpa [z] using adagrad_per_step_memlp_g S i t
  have ha2 : MemLp a 2 S.μ := by
    simpa [a] using adagrad_per_step_memlp_grad S i t ht
  have he2 : MemLp e 2 S.μ := by
    exact hz2.sub ha2
  have hzint : Integrable z S.μ := hz2.integrable one_le_two
  have haint : Integrable a S.μ := ha2.integrable one_le_two
  have hesqint : Integrable (fun ω => e ω ^ 2) S.μ := he2.integrable_sq
  have ha_m : AEStronglyMeasurable[S.ℱ (t - 1)] a S.μ := by
    have hce : AEStronglyMeasurable[S.ℱ (t - 1)]
        (S.μ[z|S.ℱ (t - 1)]) S.μ :=
      stronglyMeasurable_condExp.aestronglyMeasurable
    refine hce.congr ?_
    simpa [a, z] using S.g_unbiased t ht i
  have hgpast : ∀ s ∈ Finset.Icc 1 (t - 1),
      StronglyMeasurable[S.ℱ (t - 1)] (fun ω => S.g s ω i) := by
    intro s hs
    have hm : Measurable[S.ℱ (t - 1)] (fun ω => S.g s ω i) :=
      (measurable_pi_apply i).comp ((S.g_adapted s).mono
        (S.ℱ.mono (Finset.mem_Icc.1 hs).2) le_rfl)
    letI : MeasurableSpace Ω := S.ℱ (t - 1)
    rw [stronglyMeasurable_iff_measurable]
    exact hm
  have hp_m : StronglyMeasurable[S.ℱ (t - 1)]
      (fun ω => ∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2) := by
    fun_prop
  have hβ_m : AEStronglyMeasurable[S.ℱ (t - 1)] β S.μ := by
    have hrad : AEStronglyMeasurable[S.ℱ (t - 1)]
        (fun ω => (∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2)
          + S.σ i ^ 2 + a ω ^ 2) S.μ :=
      ((hp_m.aestronglyMeasurable.add aestronglyMeasurable_const).add (ha_m.pow 2))
    have hsqrt := Real.continuous_sqrt.comp_aestronglyMeasurable hrad
    have hden : AEStronglyMeasurable[S.ℱ (t - 1)]
        (fun ω => Real.sqrt ((∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2)
          + S.σ i ^ 2 + a ω ^ 2) + S.δ) S.μ :=
      hsqrt.add aestronglyMeasurable_const
    have hnum : AEStronglyMeasurable[S.ℱ (t - 1)]
        (fun _ : Ω => S.η) S.μ := aestronglyMeasurable_const
    refine (hnum.div₀ hden).congr ?_
    filter_upwards with ω
    rfl
  have hgall : ∀ s : ℕ, StronglyMeasurable (fun ω => S.g s ω i) := by
    intro s
    exact (((S.g_adapted s).mono (S.ℱ.le s) le_rfl).eval).stronglyMeasurable
  have hα_meas : AEStronglyMeasurable α S.μ := by
    have hsum : StronglyMeasurable
        (fun ω => ∑ s ∈ Finset.Icc 1 t, S.g s ω i ^ 2) := by
      fun_prop
    have hsqrt := Real.continuous_sqrt.comp_stronglyMeasurable hsum
    have hden : StronglyMeasurable
        (fun ω => Real.sqrt (∑ s ∈ Finset.Icc 1 t, S.g s ω i ^ 2) + S.δ) :=
      hsqrt.add stronglyMeasurable_const
    have hnum : AEStronglyMeasurable (fun _ : Ω => S.η) S.μ :=
      aestronglyMeasurable_const
    refine (hnum.div₀ hden.aestronglyMeasurable).congr ?_
    filter_upwards with ω
    rfl
  have hzmeas : AEStronglyMeasurable z S.μ := hzint.aestronglyMeasurable
  have humeas : AEStronglyMeasurable u S.μ := by
    exact hα_meas.mul hzmeas
  have hβmeas : AEStronglyMeasurable β S.μ := hβ_m.mono (S.ℱ.le (t - 1))
  have hstep : ∀ ω, 0 < α ω ∧ α ω ≤ S.η / S.δ ∧
      α ω * |z ω| ≤ S.η ∧ 0 < β ω ∧ β ω ≤ S.η / S.δ ∧
      β ω * |a ω| ≤ S.η ∧
      |α ω - β ω| ≤ α ω * β ω / S.η * (|e ω| + S.σ i) := by
    intro ω
    simpa [α, β, a, z, e] using adagrad_per_step_step_bounds S t ht i ω
  have hubound : ∀ᵐ ω ∂S.μ, ‖u ω‖ ≤ S.η := by
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    change |α ω * z ω| ≤ S.η
    rw [abs_mul]
    simpa [abs_of_pos (hstep ω).1] using (hstep ω).2.2.1
  have huint : Integrable u S.μ :=
    Integrable.mono' (integrable_const S.η) humeas hubound
  have hu2int : Integrable (fun ω => u ω ^ 2) S.μ :=
    (huint.bdd_mul' humeas hubound).congr (Filter.Eventually.of_forall fun ω => by
      simp [pow_two])
  have hβa2int : Integrable (fun ω => β ω * a ω ^ 2) S.μ := by
    apply Integrable.bdd_mul' ha2.integrable_sq hβmeas
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_pos (hstep ω).2.2.2.1]
    exact (hstep ω).2.2.2.2.1
  have hβazint : Integrable (fun ω => β ω * a ω * z ω) S.μ := by
    have hβameas : AEStronglyMeasurable (fun ω => β ω * a ω) S.μ :=
      hβmeas.mul haint.aestronglyMeasurable
    apply Integrable.bdd_mul' hzint hβameas
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hstep ω).2.2.2.1]
    exact (hstep ω).2.2.2.2.2.1
  have hαazint : Integrable (fun ω => α ω * a ω * z ω) S.μ := by
    have h := Integrable.bdd_mul' haint humeas hubound
    exact h.congr (Filter.Eventually.of_forall fun ω => by
      simp [u]
      ring)
  have hvar : S.μ[fun ω => e ω ^ 2|S.ℱ (t - 1)]
      ≤ᵐ[S.μ] fun _ => S.σ i ^ 2 := by
    simpa [e, a, z] using S.g_bounded_variance t ht i
  by_cases hσ0 : S.σ i = 0
  · have heintle : (∫ ω, e ω ^ 2 ∂S.μ) ≤ 0 := by
      calc
        (∫ ω, e ω ^ 2 ∂S.μ) =
            ∫ ω, (S.μ[fun ω => e ω ^ 2|S.ℱ (t - 1)]) ω ∂S.μ :=
          (integral_condExp (S.ℱ.le (t - 1))).symm
        _ ≤ ∫ _ : Ω, 0 ∂S.μ := by
          refine integral_mono_ae integrable_condExp (integrable_const 0) ?_
          simpa [hσ0] using hvar
        _ = 0 := by simp
    have heinteq : (∫ ω, e ω ^ 2 ∂S.μ) = 0 := by
      have hnonneg : 0 ≤ ∫ ω, e ω ^ 2 ∂S.μ :=
        integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω => sq_nonneg _)
      linarith
    have hesqzero : (fun ω => e ω ^ 2) =ᵐ[S.μ] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall fun ω => sq_nonneg (e ω)) hesqint).1 heinteq
    have hezero : e =ᵐ[S.μ] 0 := by
      filter_upwards [hesqzero] with ω hω
      have heω : e ω = 0 := by
        simpa using (sq_eq_zero_iff.mp hω)
      simpa [heω]
    have hza : z =ᵐ[S.μ] a := by
      filter_upwards [hezero] with ω hω
      dsimp [e] at hω
      linarith
    have hαβ : α =ᵐ[S.μ] β := by
      filter_upwards [hezero] with ω hω
      have hd := (hstep ω).2.2.2.2.2.2
      rw [hσ0, hω] at hd
      simp only [Pi.zero_apply, abs_zero, zero_add, mul_zero] at hd
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hd (abs_nonneg _)))
    rw [hσ0]
    simp only [mul_zero, zero_div, zero_mul, add_zero]
    calc
      (∫ ω, β ω / 2 * a ω ^ 2 ∂S.μ)
          ≤ ∫ ω, β ω * a ω ^ 2 ∂S.μ := by
        have hleftint : Integrable (fun ω => β ω / 2 * a ω ^ 2) S.μ :=
          (hβa2int.div_const 2).congr
            (Filter.Eventually.of_forall fun ω => by ring)
        refine integral_mono_ae hleftint hβa2int ?_
        filter_upwards with ω
        have hb := (hstep ω).2.2.2.1
        nlinarith [sq_nonneg (a ω)]
      _ = ∫ ω, α ω * a ω * z ω ∂S.μ := by
        apply integral_congr_ae
        filter_upwards [hza, hαβ] with ω hzω hαω
        rw [hzω, hαω]
        ring
  · have hσ : 0 < S.σ i := lt_of_le_of_ne (S.sigma_nonneg i) (Ne.symm hσ0)
    let C : ℝ := 2 * adagrad_grad_coord S.obj S.init i ^ 2
      + 18 * S.L i * adagrad_l1_norm S.L * S.η ^ 2 * ((t : ℝ) - 1) ^ 2
    have hC0 : 0 ≤ C := by
      dsimp [C]
      have hL1 : 0 ≤ adagrad_l1_norm S.L := by
        rw [adagrad_l1_norm]
        positivity
      have hLi : 0 ≤ S.L i := S.L_nonneg i
      have hterm : 0 ≤ 18 * S.L i * adagrad_l1_norm S.L * S.η ^ 2
          * ((t : ℝ) - 1) ^ 2 := by
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hLi) hL1) (sq_nonneg _))
          (sq_nonneg _)
      nlinarith [sq_nonneg (adagrad_grad_coord S.obj S.init i)]
    have habound : ∀ ω, a ω ^ 2 ≤ C := by
      intro ω
      simpa [a, C] using adagrad_per_step_grad_bound S ω i t ht
    let K : Ω → ℝ := fun ω => β ω * a ω ^ 2 / (8 * S.σ i ^ 2)
    have hK_m : AEStronglyMeasurable[S.ℱ (t - 1)] K S.μ := by
      have hnum := hβ_m.mul (ha_m.pow 2)
      refine (hnum.const_mul (1 / (8 * S.σ i ^ 2))).congr ?_
      filter_upwards with ω
      dsimp [K]
      ring
    have hKmeas : AEStronglyMeasurable K S.μ := hK_m.mono (S.ℱ.le (t - 1))
    let M : ℝ := (S.η / S.δ * C) / (8 * S.σ i ^ 2)
    have hK0 : ∀ ω, 0 ≤ K ω := by
      intro ω
      dsimp [K]
      exact div_nonneg (mul_nonneg (hstep ω).2.2.2.1.le (sq_nonneg _)) (by positivity)
    have hKbound : ∀ᵐ ω ∂S.μ, ‖K ω‖ ≤ M := by
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hK0 ω)]
      dsimp [K, M]
      have hnum : β ω * a ω ^ 2 ≤ S.η / S.δ * C :=
        mul_le_mul (hstep ω).2.2.2.2.1 (habound ω) (sq_nonneg _)
          (div_nonneg S.eta_pos.le S.delta_pos.le)
      have hden : 0 ≤ 8 * S.σ i ^ 2 := by positivity
      exact div_le_div_of_nonneg_right hnum hden
    have hKesqint : Integrable (fun ω => K ω * e ω ^ 2) S.μ :=
      Integrable.bdd_mul' hesqint hKmeas hKbound
    have hKconstint : Integrable (fun ω => K ω * S.σ i ^ 2) S.μ :=
      Integrable.bdd_mul' (integrable_const (S.σ i ^ 2)) hKmeas hKbound
    have hKvar : (∫ ω, K ω * e ω ^ 2 ∂S.μ)
        ≤ ∫ ω, K ω * S.σ i ^ 2 ∂S.μ := by
      have hpull := condExp_stronglyMeasurable_mul_of_bound₀
        (S.ℱ.le (t - 1)) hK_m hesqint M hKbound
      have hpullint :
          (∫ ω, (S.μ[fun ω => K ω * e ω ^ 2|S.ℱ (t - 1)]) ω ∂S.μ)
            = ∫ ω, K ω * (S.μ[fun ω => e ω ^ 2|S.ℱ (t - 1)]) ω ∂S.μ :=
        integral_congr_ae hpull
      calc
        (∫ ω, K ω * e ω ^ 2 ∂S.μ)
            = ∫ ω, (S.μ[fun ω => K ω * e ω ^ 2|S.ℱ (t - 1)]) ω ∂S.μ :=
          (integral_condExp (S.ℱ.le (t - 1))).symm
        _ = ∫ ω, K ω * (S.μ[fun ω => e ω ^ 2|S.ℱ (t - 1)]) ω ∂S.μ :=
          hpullint
        _ ≤ ∫ ω, K ω * S.σ i ^ 2 ∂S.μ := by
          have hleft : Integrable
              (fun ω => K ω * (S.μ[fun ω => e ω ^ 2|S.ℱ (t - 1)]) ω) S.μ :=
            Integrable.bdd_mul' integrable_condExp hKmeas hKbound
          refine integral_mono_ae hleft hKconstint ?_
          filter_upwards [hvar] with ω hω
          exact mul_le_mul_of_nonneg_left hω (hK0 ω)
    have hXbound : ∀ ω, (|e ω| + S.σ i) ^ 2
        ≤ 2 * e ω ^ 2 + 2 * S.σ i ^ 2 := by
      intro ω
      nlinarith [sq_abs (e ω), sq_nonneg (|e ω| - S.σ i)]
    have hXint : Integrable (fun ω => (|e ω| + S.σ i) ^ 2) S.μ := by
      have heabs : Integrable (fun ω => |e ω|) S.μ :=
        (he2.integrable one_le_two).abs
      have hmeas : AEStronglyMeasurable (fun ω => (|e ω| + S.σ i) ^ 2) S.μ :=
        ((heabs.aestronglyMeasurable.add aestronglyMeasurable_const).pow 2)
      have hdom : Integrable (fun ω => 2 * e ω ^ 2 + 2 * S.σ i ^ 2) S.μ :=
        (hesqint.const_mul 2).add (integrable_const (2 * S.σ i ^ 2))
      refine Integrable.mono' hdom hmeas ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hXbound ω
    have hKXint : Integrable (fun ω => K ω * (|e ω| + S.σ i) ^ 2) S.μ :=
      Integrable.bdd_mul' hXint hKmeas hKbound
    have hKsumint : Integrable
        (fun ω => K ω * (2 * e ω ^ 2 + 2 * S.σ i ^ 2)) S.μ := by
      exact ((hKesqint.const_mul 2).add (hKconstint.const_mul 2)).congr
        (Filter.Eventually.of_forall fun ω => by simp only [Pi.add_apply]; ring)
    have hKXle : (∫ ω, K ω * (|e ω| + S.σ i) ^ 2 ∂S.μ)
        ≤ ∫ ω, β ω * a ω ^ 2 / 2 ∂S.μ := by
      have hmono : (∫ ω, K ω * (|e ω| + S.σ i) ^ 2 ∂S.μ)
          ≤ ∫ ω, K ω * (2 * e ω ^ 2 + 2 * S.σ i ^ 2) ∂S.μ := by
        refine integral_mono_ae hKXint hKsumint ?_
        filter_upwards with ω
        exact mul_le_mul_of_nonneg_left (hXbound ω) (hK0 ω)
      have hsum :
          (∫ ω, K ω * (2 * e ω ^ 2 + 2 * S.σ i ^ 2) ∂S.μ)
            = 2 * (∫ ω, K ω * e ω ^ 2 ∂S.μ)
              + 2 * (∫ ω, K ω * S.σ i ^ 2 ∂S.μ) := by
        calc
          (∫ ω, K ω * (2 * e ω ^ 2 + 2 * S.σ i ^ 2) ∂S.μ)
              = ∫ ω, 2 * (K ω * e ω ^ 2) + 2 * (K ω * S.σ i ^ 2) ∂S.μ := by
                apply integral_congr_ae
                filter_upwards with ω
                ring
          _ = (∫ ω, 2 * (K ω * e ω ^ 2) ∂S.μ)
                + ∫ ω, 2 * (K ω * S.σ i ^ 2) ∂S.μ :=
              integral_add (hKesqint.const_mul 2) (hKconstint.const_mul 2)
          _ = 2 * (∫ ω, K ω * e ω ^ 2 ∂S.μ)
                + 2 * (∫ ω, K ω * S.σ i ^ 2 ∂S.μ) := by
              rw [integral_const_mul, integral_const_mul]
      have hfour :
          2 * (∫ ω, K ω * e ω ^ 2 ∂S.μ)
              + 2 * (∫ ω, K ω * S.σ i ^ 2 ∂S.μ)
            ≤ 4 * (∫ ω, K ω * S.σ i ^ 2 ∂S.μ) := by
        linarith
      have hident :
          4 * (∫ ω, K ω * S.σ i ^ 2 ∂S.μ)
            = ∫ ω, β ω * a ω ^ 2 / 2 ∂S.μ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with ω
        dsimp [K]
        field_simp
        ring
      linarith
    have hβσ : ∀ ω, β ω * S.σ i ≤ S.η := by
      intro ω
      have hp : 0 ≤ ∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2 :=
        Finset.sum_nonneg fun s _ => sq_nonneg _
      have hr : S.σ i ≤ Real.sqrt ((∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2)
          + S.σ i ^ 2 + a ω ^ 2) := by
        have hs : S.σ i ^ 2 ≤ (∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2)
            + S.σ i ^ 2 + a ω ^ 2 := by nlinarith [hp, sq_nonneg (a ω)]
        calc
          S.σ i = Real.sqrt (S.σ i ^ 2) := (Real.sqrt_sq hσ.le).symm
          _ ≤ _ := Real.sqrt_le_sqrt hs
      dsimp [β]
      unfold adagrad_decorrelated_step
      have hd : 0 < Real.sqrt ((∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2)
          + S.σ i ^ 2 + a ω ^ 2) + S.δ := by
        linarith [Real.sqrt_nonneg ((∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2)
          + S.σ i ^ 2 + a ω ^ 2), S.delta_pos]
      rw [div_mul_eq_mul_div, div_le_iff₀ hd]
      exact mul_le_mul_of_nonneg_left (by linarith [hr, S.delta_pos]) S.eta_pos.le
    have herror : ∀ ω, |(α ω - β ω) * a ω * z ω|
        ≤ K ω * (|e ω| + S.σ i) ^ 2
          + 2 * S.σ i / S.η * u ω ^ 2 := by
      intro ω
      have herr1 : |(α ω - β ω) * a ω * z ω|
          ≤ β ω * |a ω| / S.η * (|e ω| + S.σ i) * |u ω| := by
        calc
          |(α ω - β ω) * a ω * z ω|
              = |α ω - β ω| * |a ω| * |z ω| := by rw [abs_mul, abs_mul]
          _ ≤ (α ω * β ω / S.η * (|e ω| + S.σ i)) * |a ω| * |z ω| := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hstep ω).2.2.2.2.2.2 (abs_nonneg _))
              (abs_nonneg _)
          _ = β ω * |a ω| / S.η * (|e ω| + S.σ i) * |u ω| := by
            change _ = _ * |α ω * z ω|
            rw [abs_mul, abs_of_pos (hstep ω).1]
            ring
      let x := Real.sqrt (β ω) * |a ω| * (|e ω| + S.σ i) / (2 * S.σ i)
      let y := 2 * Real.sqrt (β ω) * S.σ i * |u ω| / S.η
      have hβ0 : 0 ≤ β ω := (hstep ω).2.2.2.1.le
      have hsβ : Real.sqrt (β ω) ^ 2 = β ω := Real.sq_sqrt hβ0
      have hxy : x * y =
          β ω * |a ω| / S.η * (|e ω| + S.σ i) * |u ω| := by
        dsimp [x, y]
        field_simp
        rw [hsβ]
        ring
      have hx2 : x ^ 2 / 2 = K ω * (|e ω| + S.σ i) ^ 2 := by
        dsimp [x, K]
        field_simp
        rw [hsβ, sq_abs]
        ring
      have hy2 : y ^ 2 / 2 =
          2 * β ω * S.σ i ^ 2 / S.η ^ 2 * u ω ^ 2 := by
        dsimp [y]
        field_simp
        rw [hsβ, sq_abs]
      have hyoung : β ω * |a ω| / S.η * (|e ω| + S.σ i) * |u ω|
          ≤ K ω * (|e ω| + S.σ i) ^ 2
            + 2 * β ω * S.σ i ^ 2 / S.η ^ 2 * u ω ^ 2 := by
        rw [← hxy, ← hx2, ← hy2]
        nlinarith [sq_nonneg (x - y)]
      have hcoef : 2 * β ω * S.σ i ^ 2 / S.η ^ 2
          ≤ 2 * S.σ i / S.η := by
        calc
          2 * β ω * S.σ i ^ 2 / S.η ^ 2
              = (2 * S.σ i / S.η) * (β ω * S.σ i / S.η) := by ring
          _ ≤ (2 * S.σ i / S.η) * 1 := by
            exact mul_le_mul_of_nonneg_left
              ((div_le_one S.eta_pos).2 (hβσ ω))
              (div_nonneg (mul_nonneg (by norm_num) hσ.le) S.eta_pos.le)
          _ = 2 * S.σ i / S.η := by ring
      calc
        |(α ω - β ω) * a ω * z ω|
            ≤ β ω * |a ω| / S.η * (|e ω| + S.σ i) * |u ω| := herr1
        _ ≤ K ω * (|e ω| + S.σ i) ^ 2
            + 2 * β ω * S.σ i ^ 2 / S.η ^ 2 * u ω ^ 2 := hyoung
        _ ≤ K ω * (|e ω| + S.σ i) ^ 2
            + 2 * S.σ i / S.η * u ω ^ 2 :=
          by
            simpa [add_comm] using
              (add_le_add_left (mul_le_mul_of_nonneg_right hcoef (sq_nonneg (u ω)))
                (K ω * (|e ω| + S.σ i) ^ 2))
    have herrint : Integrable (fun ω => (α ω - β ω) * a ω * z ω) S.μ := by
      exact (hαazint.sub hβazint).congr
        (Filter.Eventually.of_forall fun ω => by simp only [Pi.sub_apply]; ring)
    have hrhsint : Integrable (fun ω =>
        K ω * (|e ω| + S.σ i) ^ 2 + 2 * S.σ i / S.η * u ω ^ 2) S.μ :=
      hKXint.add (hu2int.const_mul (2 * S.σ i / S.η))
    have herrabsle : (∫ ω, |(α ω - β ω) * a ω * z ω| ∂S.μ)
        ≤ (∫ ω, β ω * a ω ^ 2 / 2 ∂S.μ)
          + 2 * S.σ i / S.η * ∫ ω, u ω ^ 2 ∂S.μ := by
      calc
        (∫ ω, |(α ω - β ω) * a ω * z ω| ∂S.μ)
            ≤ ∫ ω, K ω * (|e ω| + S.σ i) ^ 2
                + 2 * S.σ i / S.η * u ω ^ 2 ∂S.μ := by
              exact integral_mono_ae herrint.abs hrhsint
                (Filter.Eventually.of_forall herror)
        _ = (∫ ω, K ω * (|e ω| + S.σ i) ^ 2 ∂S.μ)
              + 2 * S.σ i / S.η * ∫ ω, u ω ^ 2 ∂S.μ := by
            rw [integral_add hKXint (hu2int.const_mul (2 * S.σ i / S.η)),
              integral_const_mul]
        _ ≤ (∫ ω, β ω * a ω ^ 2 / 2 ∂S.μ)
              + 2 * S.σ i / S.η * ∫ ω, u ω ^ 2 ∂S.μ :=
            by
              simpa [add_comm] using
                (add_le_add_right hKXle
                  (2 * S.σ i / S.η * ∫ ω, u ω ^ 2 ∂S.μ))
    have hweight_m : AEStronglyMeasurable[S.ℱ (t - 1)]
        (fun ω => β ω * a ω) S.μ := hβ_m.mul ha_m
    have hweightbound : ∀ᵐ ω ∂S.μ, ‖β ω * a ω‖ ≤ S.η := by
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hstep ω).2.2.2.1]
      exact (hstep ω).2.2.2.2.2.1
    have hmain : (∫ ω, β ω * a ω * z ω ∂S.μ)
        = ∫ ω, β ω * a ω ^ 2 ∂S.μ := by
      have hpull := condExp_stronglyMeasurable_mul_of_bound₀
        (S.ℱ.le (t - 1)) hweight_m hzint S.η hweightbound
      calc
        (∫ ω, β ω * a ω * z ω ∂S.μ)
            = ∫ ω, (S.μ[fun ω => (β ω * a ω) * z ω|S.ℱ (t - 1)]) ω ∂S.μ := by
              rw [← integral_condExp (S.ℱ.le (t - 1))]
        _ = ∫ ω, (β ω * a ω)
            * (S.μ[z|S.ℱ (t - 1)]) ω ∂S.μ := integral_congr_ae hpull
        _ = ∫ ω, β ω * a ω ^ 2 ∂S.μ := by
          apply integral_congr_ae
          filter_upwards [S.g_unbiased t ht i] with ω hω
          change (β ω * a ω) * (S.μ[z|S.ℱ (t - 1)]) ω = β ω * a ω ^ 2
          rw [show (S.μ[z|S.ℱ (t - 1)]) ω = a ω by simpa [a, z] using hω]
          ring
    have hdecomp : (∫ ω, α ω * a ω * z ω ∂S.μ)
        = (∫ ω, β ω * a ω * z ω ∂S.μ)
          + ∫ ω, (α ω - β ω) * a ω * z ω ∂S.μ := by
      rw [← integral_add hβazint herrint]
      apply integral_congr_ae
      filter_upwards with ω
      ring
    have herrlower : -(∫ ω, |(α ω - β ω) * a ω * z ω| ∂S.μ)
        ≤ ∫ ω, (α ω - β ω) * a ω * z ω ∂S.μ := by
      have habs := abs_integral_le_integral_abs
        (μ := S.μ) (f := fun ω => (α ω - β ω) * a ω * z ω)
      exact neg_le_of_abs_le habs
    have hleft :
        (∫ ω, β ω / 2 * a ω ^ 2 ∂S.μ)
          = ∫ ω, β ω * a ω ^ 2 / 2 ∂S.μ := by
      apply integral_congr_ae
      filter_upwards with ω
      ring
    have huident :
        (∫ ω, α ω ^ 2 * z ω ^ 2 ∂S.μ) = ∫ ω, u ω ^ 2 ∂S.μ := by
      apply integral_congr_ae
      filter_upwards with ω
      simp only [u, Pi.mul_apply]
      ring
    have hhalfint : (∫ ω, β ω * a ω ^ 2 / 2 ∂S.μ)
        = (∫ ω, β ω * a ω ^ 2 ∂S.μ) / 2 := by
      rw [integral_div]
    rw [hleft, huident, hdecomp, hmain]
    rw [hhalfint] at herrabsle
    linarith

@[blueprint "lem:adagrad-per-step-term-integrable"
  (statement := /-- For an AdaGrad setting $S$, $t\ge1$, and $i\in[d]$, each of
    $$\frac{\hat\eta_{t,i}}2\nabla_iF(\mathbf w_t)^2,\qquad
      \eta_{t,i}\nabla_iF(\mathbf w_t)g_{t,i},\qquad
      \eta_{t,i}^2g_{t,i}^2$$
    is integrable. -/)
  (proof := /-- The gradient lies in $L^2$ by
    \cref{lem:adagrad-per-step-memlp-grad}. Adaptedness makes the stochastic gradient and
    both step sizes almost everywhere strongly measurable. By
    \cref{lem:adagrad-per-step-step-bounds}, the decorrelated step is bounded by
    $\eta/\delta$ and $|\eta_{t,i}g_{t,i}|\le\eta$. Thus the first term is a bounded
    multiple of an integrable square, the second is a bounded multiple of an integrable
    gradient, and the third is the square of a bounded measurable function. -/)
  (title := /-- Integrability of the per-coordinate descent terms -/)
  (latexEnv := "lemma")]
lemma adagrad_per_step_term_integrable {Ω : Type} [MeasurableSpace Ω]
    (S : adagrad_setting Ω) (t : ℕ) (ht : 1 ≤ t) (i : Fin S.d) :
    Integrable (fun ω => adagrad_decorrelated_step S ω t i / 2
        * adagrad_grad_coord S.obj (S.w t ω) i ^ 2) S.μ ∧
      Integrable (fun ω => adagrad_step S ω t i
        * adagrad_grad_coord S.obj (S.w t ω) i * S.g t ω i) S.μ ∧
      Integrable (fun ω => adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2) S.μ := by
  classical
  haveI := S.isProbabilityMeasure
  have hg : ∀ s : ℕ, StronglyMeasurable (fun ω => S.g s ω i) := by
    intro s
    exact (measurable_pi_apply i).comp ((S.g_adapted s).mono (S.ℱ.le s) le_rfl)
      |>.stronglyMeasurable
  have hα : AEStronglyMeasurable (fun ω => adagrad_step S ω t i) S.μ := by
    have hsum : StronglyMeasurable
        (fun ω => ∑ s ∈ Finset.Icc 1 t, S.g s ω i ^ 2) := by fun_prop
    have hsqrt := Real.continuous_sqrt.comp_stronglyMeasurable hsum
    have hden : StronglyMeasurable
        (fun ω => Real.sqrt (∑ s ∈ Finset.Icc 1 t, S.g s ω i ^ 2) + S.δ) :=
      hsqrt.add stronglyMeasurable_const
    have hnum : AEStronglyMeasurable (fun _ : Ω => S.η) S.μ :=
      aestronglyMeasurable_const
    refine (hnum.div₀ hden.aestronglyMeasurable).congr ?_
    filter_upwards with ω
    rfl
  have hgrad2 := adagrad_per_step_memlp_grad S i t ht
  have hgradmeas := hgrad2.integrable_sq.aestronglyMeasurable
  have hpast : StronglyMeasurable
      (fun ω => ∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2) := by fun_prop
  have hrad : AEStronglyMeasurable
      (fun ω => (∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2) + S.σ i ^ 2
        + adagrad_grad_coord S.obj (S.w t ω) i ^ 2) S.μ :=
    ((hpast.aestronglyMeasurable.add aestronglyMeasurable_const).add hgradmeas)
  have hsqrt := Real.continuous_sqrt.comp_aestronglyMeasurable hrad
  have hden : AEStronglyMeasurable
      (fun ω => Real.sqrt ((∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2) + S.σ i ^ 2
        + adagrad_grad_coord S.obj (S.w t ω) i ^ 2) + S.δ) S.μ :=
    hsqrt.add aestronglyMeasurable_const
  have hnum : AEStronglyMeasurable (fun _ : Ω => S.η) S.μ :=
    aestronglyMeasurable_const
  have hβ : AEStronglyMeasurable
      (fun ω => adagrad_decorrelated_step S ω t i) S.μ := by
    refine (hnum.div₀ hden).congr ?_
    filter_upwards with ω
    rfl
  have hst := fun ω => adagrad_per_step_step_bounds S t ht i ω
  have hu_meas : AEStronglyMeasurable
      (fun ω => adagrad_step S ω t i * S.g t ω i) S.μ :=
    hα.mul (hg t).aestronglyMeasurable
  have hu_bound : ∀ᵐ ω ∂S.μ,
      ‖adagrad_step S ω t i * S.g t ω i‖ ≤ S.η := by
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hst ω).1]
    exact (hst ω).2.2.1
  have hu_int : Integrable (fun ω => adagrad_step S ω t i * S.g t ω i) S.μ :=
    Integrable.mono' (integrable_const S.η) hu_meas hu_bound
  have hq : Integrable
      (fun ω => adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2) S.μ := by
    have hsquare := hu_int.bdd_mul' hu_meas hu_bound
    exact hsquare.congr (Filter.Eventually.of_forall fun ω => by ring)
  have hcross : Integrable (fun ω => adagrad_step S ω t i
      * adagrad_grad_coord S.obj (S.w t ω) i * S.g t ω i) S.μ := by
    have h := Integrable.bdd_mul'
      (hgrad2.integrable one_le_two) hu_meas hu_bound
    exact h.congr (Filter.Eventually.of_forall fun ω => by ring)
  have hfactor : AEStronglyMeasurable
      (fun ω => adagrad_decorrelated_step S ω t i / 2) S.μ :=
    (hβ.const_mul (1 / 2)).congr (Filter.Eventually.of_forall fun ω => by ring)
  have hfactor_bound : ∀ᵐ ω ∂S.μ,
      ‖adagrad_decorrelated_step S ω t i / 2‖ ≤ S.η / S.δ := by
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (hst ω).2.2.2.1 (by norm_num))]
    have hb := (hst ω).2.2.2.2.1
    have hb0 := (hst ω).2.2.2.1
    have hηδ : 0 < S.η / S.δ := div_pos S.eta_pos S.delta_pos
    nlinarith
  have hlhs := Integrable.bdd_mul' hgrad2.integrable_sq hfactor hfactor_bound
  exact ⟨hlhs, hcross, hq⟩

@[blueprint "lem:adagrad-per-step-smooth-descent"
  (statement := /-- For an AdaGrad setting $S$ and $t\ge1$,
    $$\mathbb E\!\left[\sum_i\eta_{t,i}\nabla_iF(\mathbf w_t)g_{t,i}\right]
      \le \mathbb E[F(\mathbf w_t)-F(\mathbf w_{t+1})]
        +\sum_i\frac{L_i}{2}\mathbb E[\eta_{t,i}^2g_{t,i}^2].$$ -/)
  (proof := /-- Apply coordinate smoothness from \cref{def:adagrad-setting} to
    $\mathbf w_t$ and $\mathbf w_{t+1}$. Substituting the AdaGrad update changes the
    linear remainder into $-\sum_i\eta_{t,i}\nabla_iF(\mathbf w_t)g_{t,i}$ and the
    quadratic remainder into $\sum_i(L_i/2)\eta_{t,i}^2g_{t,i}^2$. Taking the one-sided
    consequence of the absolute-value estimate gives the pointwise descent inequality.
    Every term is integrable by \cref{lem:adagrad-per-step-term-integrable}, so it may be
    integrated and the finite sums may be interchanged with the integral. -/)
  (title := /-- Smoothness contribution to one-step descent -/)
  (latexEnv := "lemma")]
lemma adagrad_per_step_smooth_descent {Ω : Type} [MeasurableSpace Ω]
    (S : adagrad_setting Ω) (t : ℕ) (ht : 1 ≤ t) :
    (∫ ω, ∑ i, adagrad_step S ω t i
        * adagrad_grad_coord S.obj (S.w t ω) i * S.g t ω i ∂S.μ)
      ≤ (∫ ω, S.obj (S.w t ω) - S.obj (S.w (t + 1) ω) ∂S.μ)
        + ∑ i, S.L i / 2
          * ∫ ω, adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2 ∂S.μ := by
  classical
  have hcross : Integrable (fun ω => ∑ i, adagrad_step S ω t i
      * adagrad_grad_coord S.obj (S.w t ω) i * S.g t ω i) S.μ :=
    integrable_finset_sum _ fun i _ => (adagrad_per_step_term_integrable S t ht i).2.1
  have hobj : Integrable
      (fun ω => S.obj (S.w t ω) - S.obj (S.w (t + 1) ω)) S.μ :=
    (S.obj_integrable t).sub (S.obj_integrable (t + 1))
  have hquad : ∀ i, Integrable
      (fun ω => S.L i / 2 * (adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2)) S.μ :=
    fun i => (adagrad_per_step_term_integrable S t ht i).2.2.const_mul (S.L i / 2)
  have hquadsum : Integrable (fun ω => ∑ i,
      S.L i / 2 * (adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2)) S.μ :=
    integrable_finset_sum _ fun i _ => hquad i
  have hpoint : ∀ ω, (∑ i, adagrad_step S ω t i
      * adagrad_grad_coord S.obj (S.w t ω) i * S.g t ω i)
      ≤ S.obj (S.w t ω) - S.obj (S.w (t + 1) ω)
        + ∑ i, S.L i / 2 * (adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2) := by
    intro ω
    have hs := S.obj_smooth (S.w t ω) (S.w (t + 1) ω)
    have hlin : ∑ i, adagrad_grad_coord S.obj (S.w t ω) i
          * (S.w (t + 1) ω i - S.w t ω i)
        = -(∑ i, adagrad_step S ω t i
          * adagrad_grad_coord S.obj (S.w t ω) i * S.g t ω i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [S.adagrad_update t ht ω i]
      unfold adagrad_step
      ring
    have hsq : ∑ i, S.L i / 2 * (S.w t ω i - S.w (t + 1) ω i) ^ 2
        = ∑ i, S.L i / 2
          * (adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [S.adagrad_update t ht ω i]
      unfold adagrad_step
      ring
    have hone := le_trans
      (le_abs_self (S.obj (S.w (t + 1) ω) - S.obj (S.w t ω)
        - ∑ i, adagrad_grad_coord S.obj (S.w t ω) i
          * (S.w (t + 1) ω i - S.w t ω i))) hs
    rw [hlin, hsq] at hone
    linarith
  calc
    (∫ ω, ∑ i, adagrad_step S ω t i
        * adagrad_grad_coord S.obj (S.w t ω) i * S.g t ω i ∂S.μ)
        ≤ ∫ ω, (S.obj (S.w t ω) - S.obj (S.w (t + 1) ω))
          + ∑ i, S.L i / 2
            * (adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2) ∂S.μ := by
          exact integral_mono_ae hcross (hobj.add hquadsum)
            (Filter.Eventually.of_forall hpoint)
    _ = (∫ ω, S.obj (S.w t ω) - S.obj (S.w (t + 1) ω) ∂S.μ)
        + ∑ i, S.L i / 2
          * ∫ ω, adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2 ∂S.μ := by
      rw [integral_add hobj hquadsum,
        integral_finset_sum _ (fun i _ => hquad i)]
      apply congrArg₂ (· + ·) rfl
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_const_mul]

@[blueprint "lem:adagrad-per-step-descent"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting} and let
    $1 \le t \le T$. Then
    $$\mathbb{E}\Bigl[\sum_{i=1}^d \frac{\hat\eta_{t,i}}{2} \nabla_i F(\mathbf{w}_t)^2\Bigr]
      \le \mathbb{E}\bigl[F(\mathbf{w}_t) - F(\mathbf{w}_{t+1})\bigr]
      + \sum_{i=1}^d \Bigl(\frac{L_i}{2} + \frac{2 \sigma_i}{\eta}\Bigr)
        \mathbb{E}\bigl[\eta_{t,i}^2 g_{t,i}^2\bigr],$$
    where $\eta_{t,i}$ is as in \cref{def:adagrad-step}, $\hat\eta_{t,i}$ is as in
    \cref{def:adagrad-decorrelated-step} and $\nabla_i F$ is as in
    \cref{def:adagrad-grad-coord}. -/)
  (proof := /-- For each coordinate $i$, the bias estimate
    \cref{lem:adagrad-per-step-bias} gives
    $$\mathbb E\!\left[\frac{\hat\eta_{t,i}}2
        \nabla_iF(\mathbf w_t)^2\right]
      \le \mathbb E[\eta_{t,i}\nabla_iF(\mathbf w_t)g_{t,i}]
        +\frac{2\sigma_i}{\eta}\mathbb E[\eta_{t,i}^2g_{t,i}^2].$$
    All three integrands are integrable by
    \cref{lem:adagrad-per-step-term-integrable}; hence summing over the finite coordinate
    set and interchanging each finite sum with expectation yields
    $$\mathbb E\!\left[\sum_i\frac{\hat\eta_{t,i}}2
        \nabla_iF(\mathbf w_t)^2\right]
      \le \mathbb E\!\left[\sum_i\eta_{t,i}
        \nabla_iF(\mathbf w_t)g_{t,i}\right]
        +\sum_i\frac{2\sigma_i}{\eta}\mathbb E[\eta_{t,i}^2g_{t,i}^2].$$

    The smoothness descent inequality \cref{lem:adagrad-per-step-smooth-descent} bounds the
    first expectation on the right by
    $$\mathbb E[F(\mathbf w_t)-F(\mathbf w_{t+1})]
      +\sum_i\frac{L_i}{2}\mathbb E[\eta_{t,i}^2g_{t,i}^2].$$
    Adding the two quadratic sums coordinatewise and using
    $\frac{L_i}{2}x+\frac{2\sigma_i}{\eta}x
      =(\frac{L_i}{2}+\frac{2\sigma_i}{\eta})x$
    proves the asserted estimate. -/)
  (title := /-- Per-step descent estimate -/)
  (latexEnv := "lemma")]
lemma adagrad_per_step_descent {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (t : ℕ) (ht : 1 ≤ t) (htT : t ≤ S.T) :
    ∫ ω, ∑ i, adagrad_decorrelated_step S ω t i / 2
          * adagrad_grad_coord S.obj (S.w t ω) i ^ 2 ∂S.μ
      ≤ (∫ ω, (S.obj (S.w t ω) - S.obj (S.w (t + 1) ω)) ∂S.μ)
        + ∑ i, (S.L i / 2 + 2 * S.σ i / S.η)
            * ∫ ω, adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2 ∂S.μ := by
  classical
  have hlhs : ∀ i, Integrable (fun ω => adagrad_decorrelated_step S ω t i / 2
      * adagrad_grad_coord S.obj (S.w t ω) i ^ 2) S.μ :=
    fun i => (adagrad_per_step_term_integrable S t ht i).1
  have hcross : ∀ i, Integrable (fun ω => adagrad_step S ω t i
      * adagrad_grad_coord S.obj (S.w t ω) i * S.g t ω i) S.μ :=
    fun i => (adagrad_per_step_term_integrable S t ht i).2.1
  have hbias : (∫ ω, ∑ i, adagrad_decorrelated_step S ω t i / 2
      * adagrad_grad_coord S.obj (S.w t ω) i ^ 2 ∂S.μ)
      ≤ (∫ ω, ∑ i, adagrad_step S ω t i
          * adagrad_grad_coord S.obj (S.w t ω) i * S.g t ω i ∂S.μ)
        + ∑ i, 2 * S.σ i / S.η
          * ∫ ω, adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2 ∂S.μ := by
    rw [integral_finset_sum _ (fun i _ => hlhs i),
      integral_finset_sum _ (fun i _ => hcross i), ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => adagrad_per_step_bias S t ht i
  have hsmooth := adagrad_per_step_smooth_descent S t ht
  calc
    (∫ ω, ∑ i, adagrad_decorrelated_step S ω t i / 2
        * adagrad_grad_coord S.obj (S.w t ω) i ^ 2 ∂S.μ)
        ≤ (∫ ω, ∑ i, adagrad_step S ω t i
            * adagrad_grad_coord S.obj (S.w t ω) i * S.g t ω i ∂S.μ)
          + ∑ i, 2 * S.σ i / S.η
            * ∫ ω, adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2 ∂S.μ := hbias
    _ ≤ ((∫ ω, S.obj (S.w t ω) - S.obj (S.w (t + 1) ω) ∂S.μ)
          + ∑ i, S.L i / 2
            * ∫ ω, adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2 ∂S.μ)
          + ∑ i, 2 * S.σ i / S.η
            * ∫ ω, adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2 ∂S.μ :=
      by
        simpa [add_comm] using
          (add_le_add_right hsmooth
            (∑ i, 2 * S.σ i / S.η
              * ∫ ω, adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2 ∂S.μ))
    _ = (∫ ω, S.obj (S.w t ω) - S.obj (S.w (t + 1) ω) ∂S.μ)
        + ∑ i, (S.L i / 2 + 2 * S.σ i / S.η)
            * ∫ ω, adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2 ∂S.μ := by
      rw [add_assoc, ← Finset.sum_add_distrib]
      apply congrArg₂ (· + ·) rfl
      apply Finset.sum_congr rfl
      intro i _
      ring

@[blueprint "lem:adagrad-qtb-log-step"
  (statement := /-- Let $\delta > 0$ and let $y \ge 0$ and $a \ge 0$ be real numbers. Then
    $$\frac{a}{\bigl(\sqrt{y+a}+\delta\bigr)^2}
      \le \log\Bigl(1 + \frac{y+a}{\delta^2}\Bigr)
        - \log\Bigl(1 + \frac{y}{\delta^2}\Bigr).$$ -/)
  (proof := /-- Write $X = \delta^2 + y$ and $Y = \delta^2 + y + a$; then $0 < X \le Y$,
    because $\delta^2 > 0$, $y \ge 0$ and $a \ge 0$.

    Since $y + a \ge 0$ we have $\sqrt{y+a}^2 = y+a$, and $\sqrt{y+a} \ge 0$ together with
    $\delta > 0$ gives
    $$\bigl(\sqrt{y+a}+\delta\bigr)^2 = (y+a) + 2\delta\sqrt{y+a} + \delta^2
      \ge (y+a) + \delta^2 = Y > 0 .$$
    As $a \ge 0$, enlarging the denominator does not increase the quotient, so
    $$\frac{a}{\bigl(\sqrt{y+a}+\delta\bigr)^2} \le \frac{a}{Y} .$$

    The inequality $\log s \le s - 1$, valid for every $s > 0$, applied to $s = X/Y > 0$
    gives $\log X - \log Y \le X/Y - 1$, where $\log(X/Y) = \log X - \log Y$ because
    $X \ne 0$ and $Y \ne 0$. Since $X/Y - 1 = -a/Y$, this reads
    $$\frac{a}{Y} \le \log Y - \log X .$$

    Finally $1 + \frac{y+a}{\delta^2} = \frac{Y}{\delta^2}$ and
    $1 + \frac{y}{\delta^2} = \frac{X}{\delta^2}$, so, again by the identity for the
    logarithm of a quotient with the nonzero arguments $\delta^2$, $X$ and $Y$,
    $$\log\Bigl(1+\frac{y+a}{\delta^2}\Bigr) - \log\Bigl(1+\frac{y}{\delta^2}\Bigr)
      = \bigl(\log Y - \log \delta^2\bigr) - \bigl(\log X - \log \delta^2\bigr)
      = \log Y - \log X .$$
    Combining the two displayed inequalities gives the assertion. -/)
  (title := /-- One step of the logarithmic telescoping estimate -/)
  (latexEnv := "lemma")]
lemma adagrad_qtb_log_step {δ y a : ℝ} (hδ : 0 < δ) (hy : 0 ≤ y) (ha : 0 ≤ a) :
    a / (Real.sqrt (y + a) + δ) ^ 2
      ≤ Real.log (1 + (y + a) / δ ^ 2) - Real.log (1 + y / δ ^ 2) := by
  have hδ2 : (0:ℝ) < δ ^ 2 := by positivity
  have hX : (0:ℝ) < δ ^ 2 + y := by linarith
  have hY : (0:ℝ) < δ ^ 2 + y + a := by linarith
  have hs : Real.sqrt (y + a) ^ 2 = y + a := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ Real.sqrt (y + a) := Real.sqrt_nonneg _
  have hden : δ ^ 2 + y + a ≤ (Real.sqrt (y + a) + δ) ^ 2 := by
    nlinarith [mul_nonneg hs0 hδ.le]
  have h1 : a / (Real.sqrt (y + a) + δ) ^ 2 ≤ a / (δ ^ 2 + y + a) := by
    gcongr
  have h2 : a / (δ ^ 2 + y + a) ≤ Real.log (δ ^ 2 + y + a) - Real.log (δ ^ 2 + y) := by
    have hlog := Real.log_le_sub_one_of_pos
      (show (0:ℝ) < (δ ^ 2 + y) / (δ ^ 2 + y + a) by positivity)
    rw [Real.log_div (ne_of_gt hX) (ne_of_gt hY)] at hlog
    have he : (δ ^ 2 + y) / (δ ^ 2 + y + a) - 1 = -(a / (δ ^ 2 + y + a)) := by
      field_simp
      ring
    rw [he] at hlog
    linarith
  have e1 : 1 + (y + a) / δ ^ 2 = (δ ^ 2 + y + a) / δ ^ 2 := by
    field_simp
    ring
  have e2 : 1 + y / δ ^ 2 = (δ ^ 2 + y) / δ ^ 2 := by field_simp
  rw [e1, e2, Real.log_div (ne_of_gt hY) (ne_of_gt hδ2),
    Real.log_div (ne_of_gt hX) (ne_of_gt hδ2)]
  linarith

@[blueprint "lem:adagrad-qtb-telescope"
  (statement := /-- Let $\delta > 0$, let $(a_t)_{t \in \mathbb{N}}$ be a sequence of
    nonnegative reals and let $T \in \mathbb{N}$. Then
    $$\sum_{t=1}^T \frac{a_t}{\bigl(\sqrt{\sum_{s=1}^t a_s} + \delta\bigr)^2}
      \le \log\Bigl(1 + \frac{\sum_{t=1}^T a_t}{\delta^2}\Bigr).$$ -/)
  (proof := /-- We argue by induction on $T$.

    For $T = 0$ both sides vanish: the index set $\{t : 1 \le t \le 0\}$ is empty, so the
    left-hand side is the empty sum $0$, and the right-hand side is
    $\log(1 + 0/\delta^2) = \log 1 = 0$.

    Assume the assertion for $T = n$ and put $Y = \sum_{s=1}^n a_s$, which is nonnegative
    as a sum of nonnegative terms. Splitting off the last index in both sums over
    $1 \le t \le n+1$ gives
    $$\sum_{t=1}^{n+1} \frac{a_t}{\bigl(\sqrt{\sum_{s=1}^t a_s}+\delta\bigr)^2}
      = \sum_{t=1}^{n} \frac{a_t}{\bigl(\sqrt{\sum_{s=1}^t a_s}+\delta\bigr)^2}
        + \frac{a_{n+1}}{\bigl(\sqrt{Y + a_{n+1}}+\delta\bigr)^2},
      \qquad \sum_{t=1}^{n+1} a_t = Y + a_{n+1} .$$
    By the induction hypothesis the first summand is at most
    $\log\bigl(1 + Y/\delta^2\bigr)$, and by \cref{lem:adagrad-qtb-log-step}, applied with
    $y = Y$ and $a = a_{n+1}$, the second summand is at most
    $\log\bigl(1 + (Y+a_{n+1})/\delta^2\bigr) - \log\bigl(1 + Y/\delta^2\bigr)$. Adding
    these two estimates, the terms $\log\bigl(1+Y/\delta^2\bigr)$ cancel and we obtain the
    bound $\log\bigl(1 + (Y + a_{n+1})/\delta^2\bigr)$, which is the assertion for
    $T = n+1$. -/)
  (title := /-- The logarithmic telescoping estimate -/)
  (latexEnv := "lemma")]
lemma adagrad_qtb_telescope {δ : ℝ} (hδ : 0 < δ) (a : ℕ → ℝ) (ha : ∀ t, 0 ≤ a t) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, a t / (Real.sqrt (∑ s ∈ Finset.Icc 1 t, a s) + δ) ^ 2
      ≤ Real.log (1 + (∑ t ∈ Finset.Icc 1 T, a t) / δ ^ 2) := by
  induction T with
  | zero => simp
  | succ n ih =>
    have hsum : (0:ℝ) ≤ ∑ s ∈ Finset.Icc 1 n, a s := Finset.sum_nonneg fun s _ => ha s
    have hstep := adagrad_qtb_log_step (δ := δ) (y := ∑ s ∈ Finset.Icc 1 n, a s)
      (a := a (n + 1)) hδ hsum (ha (n + 1))
    rw [Finset.sum_Icc_succ_top (show 1 ≤ n + 1 by omega)
        (fun t => a t / (Real.sqrt (∑ s ∈ Finset.Icc 1 t, a s) + δ) ^ 2),
      Finset.sum_Icc_succ_top (show 1 ≤ n + 1 by omega) a]
    linarith

@[blueprint "lem:adagrad-qtb-amgm-bound"
  (statement := /-- Let $B, C, D, K$ be real numbers with $B \ge 0$ and $K \ge 0$, and
    suppose that
    $$s D \le B + s C + K s^2 \qquad \text{for every real } s > 0 .$$
    Then $D \le C + 2\sqrt{BK}$. -/)
  (proof := /-- We distinguish three cases.

    Suppose first that $K = 0$. Then $\sqrt{BK} = 0$, so the assertion to be proved is
    $D \le C$, and the hypothesis reads $sD \le B + sC$ for every $s > 0$. Let
    $\varepsilon > 0$ and put $s = (B+1)/\varepsilon$, which is positive because
    $B + 1 > 0$. Then $s \varepsilon = B + 1$, hence
    $$s D \le B + s C < s C + (B + 1) = s C + s \varepsilon = s (C + \varepsilon),$$
    and dividing by $s > 0$ gives $D \le C + \varepsilon$. As $\varepsilon > 0$ was
    arbitrary, $D \le C$.

    Suppose next that $K > 0$ and $B = 0$. Then again $\sqrt{BK} = 0$ and the assertion is
    $D \le C$, while the hypothesis reads $sD \le sC + K s^2$ for every $s > 0$. Let
    $\varepsilon > 0$ and put $s = \varepsilon/(2K) > 0$. Then
    $K s^2 = s \cdot \frac{\varepsilon}{2} \le s \varepsilon$, because $s > 0$ and
    $\varepsilon/2 \le \varepsilon$, so
    $$sD \le sC + K s^2 \le sC + s\varepsilon = s(C + \varepsilon),$$
    and dividing by $s > 0$ gives $D \le C + \varepsilon$. Again $\varepsilon > 0$ was
    arbitrary, so $D \le C$.

    Suppose finally that $B > 0$ and $K > 0$, and put $s = \sqrt{B}/\sqrt{K}$, which is
    positive because $\sqrt{B} > 0$ and $\sqrt{K} > 0$. Since $\sqrt{B}^2 = B$ and
    $\sqrt{K}^2 = K$, we have $K s^2 = K \cdot B/K = B$, so the hypothesis at this $s$
    reads $sD \le 2B + sC$. On the other hand $\sqrt{BK} = \sqrt{B}\sqrt{K}$ because
    $B \ge 0$, whence
    $$s \bigl(2 \sqrt{BK}\bigr)
      = \frac{\sqrt{B}}{\sqrt{K}} \cdot 2 \sqrt{B}\sqrt{K} = 2B .$$
    Therefore $sD \le sC + s\bigl(2\sqrt{BK}\bigr) = s\bigl(C + 2\sqrt{BK}\bigr)$, and
    dividing by $s > 0$ gives $D \le C + 2\sqrt{BK}$. -/)
  (title := /-- Optimisation of a family of quadratic upper bounds -/)
  (latexEnv := "lemma")]
lemma adagrad_qtb_amgm_bound {B C D K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (h : ∀ s : ℝ, 0 < s → s * D ≤ B + s * C + K * s ^ 2) :
    D ≤ C + 2 * Real.sqrt (B * K) := by
  rcases eq_or_lt_of_le hK with hK0 | hKpos
  · subst hK0
    simp only [mul_zero, Real.sqrt_zero, mul_zero, add_zero] at h ⊢
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    have hs : 0 < (B + 1) / ε := by positivity
    have h2 := h _ hs
    have hsε : (B + 1) / ε * ε = B + 1 := by field_simp
    refine le_of_mul_le_mul_left ?_ hs
    calc (B + 1) / ε * D ≤ B + (B + 1) / ε * C := by nlinarith [h2]
      _ ≤ (B + 1) / ε * (C + ε) := by rw [mul_add, hsε]; linarith
  · rcases eq_or_lt_of_le hB with hB0 | hBpos
    · subst hB0
      simp only [zero_mul, Real.sqrt_zero, mul_zero, add_zero, zero_add] at h ⊢
      refine le_of_forall_pos_le_add ?_
      intro ε hε
      have hs : 0 < ε / (2 * K) := by positivity
      have h2 := h _ hs
      have hKs : K * (ε / (2 * K)) ^ 2 = ε / (2 * K) * (ε / 2) := by
        field_simp
      refine le_of_mul_le_mul_left ?_ hs
      calc ε / (2 * K) * D ≤ ε / (2 * K) * C + K * (ε / (2 * K)) ^ 2 := h2
        _ = ε / (2 * K) * C + ε / (2 * K) * (ε / 2) := by rw [hKs]
        _ ≤ ε / (2 * K) * (C + ε) := by rw [mul_add]; nlinarith
    · have hsb : 0 < Real.sqrt B := Real.sqrt_pos.2 hBpos
      have hsk : 0 < Real.sqrt K := Real.sqrt_pos.2 hKpos
      have hs : 0 < Real.sqrt B / Real.sqrt K := by positivity
      have h2 := h _ hs
      have hB' : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB
      have hK' : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK
      have hKs : K * (Real.sqrt B / Real.sqrt K) ^ 2 = B := by
        rw [div_pow, hB', hK']
        field_simp
      have hprod : Real.sqrt B / Real.sqrt K * (2 * Real.sqrt (B * K)) = 2 * B := by
        rw [Real.sqrt_mul hB]
        field_simp
        nlinarith [hB']
      rw [hKs] at h2
      refine le_of_mul_le_mul_left ?_ hs
      rw [mul_add, hprod]
      linarith

@[blueprint "lem:adagrad-qtb-log-integrable"
  (statement := /-- Let $(\Omega, \mathcal{A}, \mu)$ be a probability space and let
    $f : \Omega \to \mathbb{R}$ be $\mu$-integrable with $f \ge 0$ $\mu$-almost
    everywhere. Then $\omega \mapsto \log\bigl(1 + f(\omega)\bigr)$ is
    $\mu$-integrable. -/)
  (proof := /-- The function $\omega \mapsto \log(1 + f(\omega))$ is almost everywhere
    strongly measurable, being the composition of the measurable function $\log$ with the
    almost everywhere measurable function $1 + f$.

    At every $\omega$ with $f(\omega) \ge 0$ we have $1 + f(\omega) \ge 1$, so
    $\log(1 + f(\omega)) \ge 0$ and therefore
    $\bigl|\log(1+f(\omega))\bigr| = \log(1+f(\omega))$. Moreover the inequality
    $\log s \le s - 1$, valid for every $s > 0$, applied to $s = 1 + f(\omega) > 0$, gives
    $\log(1+f(\omega)) \le f(\omega)$. Hence
    $\bigl|\log(1+f(\omega))\bigr| \le f(\omega)$ almost everywhere, and since $f$ is
    integrable the assertion follows by domination. -/)
  (title := /-- Integrability of the logarithm -/)
  (latexEnv := "lemma")]
lemma adagrad_qtb_log_integrable {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (hf : Integrable f μ) (hf0 : 0 ≤ᵐ[μ] f) :
    Integrable (fun ω => Real.log (1 + f ω)) μ := by
  have hf0' : ∀ᵐ ω ∂μ, 0 ≤ f ω := hf0
  have hmeas : AEStronglyMeasurable (fun ω => Real.log (1 + f ω)) μ :=
    (Real.measurable_log.comp_aemeasurable
      (aemeasurable_const.add hf.1.aemeasurable)).aestronglyMeasurable
  refine Integrable.mono' hf hmeas ?_
  filter_upwards [hf0'] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith))]
  have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + f ω by linarith)
  linarith

@[blueprint "lem:adagrad-qtb-jensen-log"
  (statement := /-- Let $(\Omega, \mathcal{A}, \mu)$ be a probability space and let
    $f : \Omega \to \mathbb{R}$ be $\mu$-integrable with $f \ge 0$ $\mu$-almost
    everywhere. Then
    $$\int_\Omega \log\bigl(1 + f(\omega)\bigr) \, d\mu(\omega)
      \le \log\Bigl(1 + \int_\Omega f \, d\mu\Bigr).$$ -/)
  (proof := /-- Write $m = \int_\Omega f \, d\mu$. Since $f \ge 0$ almost everywhere,
    $m \ge 0$, hence $1 + m > 0$. The function $\log(1+f)$ is $\mu$-integrable by
    \cref{lem:adagrad-qtb-log-integrable}.

    At every $\omega$ with $f(\omega) \ge 0$ the quotient
    $\bigl(1+f(\omega)\bigr)/(1+m)$ is positive, so the inequality $\log s \le s - 1$
    applied to it, together with
    $\log\bigl((1+f(\omega))/(1+m)\bigr) = \log(1+f(\omega)) - \log(1+m)$, valid because
    $1 + f(\omega) \ne 0$ and $1 + m \ne 0$, yields
    $$\log\bigl(1 + f(\omega)\bigr)
      \le \log(1+m) - 1 + \frac{1 + f(\omega)}{1+m} .$$
    This holds $\mu$-almost everywhere, and the right-hand side is $\mu$-integrable, being
    the sum of a constant and the integrable function $(1+f)/(1+m)$; the constants are
    integrable because $\mu$ is a probability measure.

    Integrating the displayed inequality and using that $\mu$ is a probability measure, so
    that the integral of a constant equals that constant and
    $\int_\Omega (1 + f) \, d\mu = 1 + m$, we obtain
    $$\int_\Omega \log(1+f) \, d\mu
      \le \log(1+m) - 1 + \frac{1+m}{1+m} = \log(1+m),$$
    where the last equality uses $1 + m \ne 0$. -/)
  (title := /-- Jensen's inequality for the logarithm -/)
  (latexEnv := "lemma")]
lemma adagrad_qtb_jensen_log {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Integrable f μ) (hf0 : 0 ≤ᵐ[μ] f) :
    (∫ ω, Real.log (1 + f ω) ∂μ) ≤ Real.log (1 + ∫ ω, f ω ∂μ) := by
  have hf0' : ∀ᵐ ω ∂μ, 0 ≤ f ω := hf0
  have hm0 : 0 ≤ ∫ ω, f ω ∂μ := integral_nonneg_of_ae hf0
  have hM : (0:ℝ) < 1 + ∫ ω, f ω ∂μ := by linarith
  have hint : Integrable (fun ω => Real.log (1 + f ω)) μ :=
    adagrad_qtb_log_integrable μ f hf hf0
  have hif : Integrable (fun ω => 1 + f ω) μ := (integrable_const (1:ℝ)).add hf
  have hdiv : Integrable (fun ω => (1 + f ω) / (1 + ∫ ω, f ω ∂μ)) μ := hif.div_const _
  have hconst : Integrable (fun _ : Ω => Real.log (1 + ∫ ω, f ω ∂μ) - 1) μ :=
    integrable_const _
  have hint2 : Integrable
      (fun ω => Real.log (1 + ∫ ω, f ω ∂μ) - 1
        + (1 + f ω) / (1 + ∫ ω, f ω ∂μ)) μ := hconst.add hdiv
  have hbound : ∀ᵐ ω ∂μ, Real.log (1 + f ω)
      ≤ Real.log (1 + ∫ ω, f ω ∂μ) - 1 + (1 + f ω) / (1 + ∫ ω, f ω ∂μ) := by
    filter_upwards [hf0'] with ω hω
    have hfω : (0:ℝ) < 1 + f ω := by linarith
    have hlog := Real.log_le_sub_one_of_pos (div_pos hfω hM)
    rw [Real.log_div (ne_of_gt hfω) (ne_of_gt hM)] at hlog
    linarith
  calc (∫ ω, Real.log (1 + f ω) ∂μ)
      ≤ ∫ ω, (Real.log (1 + ∫ ω, f ω ∂μ) - 1
          + (1 + f ω) / (1 + ∫ ω, f ω ∂μ)) ∂μ := integral_mono_ae hint hint2 hbound
    _ = Real.log (1 + ∫ ω, f ω ∂μ) := by
        rw [integral_add hconst hdiv, integral_div, integral_add (integrable_const (1:ℝ)) hf]
        simp only [integral_const, smul_eq_mul, measureReal_univ_eq_one, one_mul]
        field_simp
        ring

@[blueprint "lem:adagrad-qtb-grad-shift"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting}, let
    $\mathbf{y} \in \mathbb{R}^d$, let $i \in [d]$ and let $s \in \mathbb{R}$. Denote by
    $\mathbf{y}'$ the point obtained from $\mathbf{y}$ by replacing its $i$-th coordinate
    by $y_i + s$. Then
    $$\bigl|F(\mathbf{y}') - F(\mathbf{y}) - s \nabla_i F(\mathbf{y})\bigr|
      \le \frac{L_i}{2} s^2,$$
    with $\nabla_i F$ as in \cref{def:adagrad-grad-coord}. -/)
  (proof := /-- Apply the coordinate-wise smoothness assumption of
    \cref{def:adagrad-setting} to the pair $\mathbf{x} = \mathbf{y}$,
    $\mathbf{y} = \mathbf{y}'$. It gives
    $$\Bigl|F(\mathbf{y}') - F(\mathbf{y})
      - \sum_{j=1}^d \nabla_j F(\mathbf{y}) (y'_j - y_j)\Bigr|
      \le \sum_{j=1}^d \frac{L_j}{2} (y_j - y'_j)^2 .$$

    By the definition of $\mathbf{y}'$ we have $y'_j - y_j = 0$ for $j \ne i$ and
    $y'_i - y_i = s$, so all terms of the first sum with $j \ne i$ vanish and the sum
    equals $s \nabla_i F(\mathbf{y})$. For the same reason $(y_j - y'_j)^2 = 0$ for
    $j \ne i$ and $(y_i - y'_i)^2 = s^2$, so the second sum equals
    $\frac{L_i}{2} s^2$. -/)
  (title := /-- Smoothness along a single coordinate -/)
  (latexEnv := "lemma")]
lemma adagrad_qtb_grad_shift {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (y : Fin S.d → ℝ) (i : Fin S.d) (s : ℝ) :
    |S.obj (Function.update y i (y i + s)) - S.obj y
        - s * adagrad_grad_coord S.obj y i|
      ≤ S.L i / 2 * s ^ 2 := by
  have h := S.obj_smooth y (Function.update y i (y i + s))
  have h1 : ∑ j, adagrad_grad_coord S.obj y j * (Function.update y i (y i + s) j - y j)
      = s * adagrad_grad_coord S.obj y i := by
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · simp [mul_comm]
    · intro j _ hj
      simp [Function.update_of_ne hj]
  have h2 : ∑ j, S.L j / 2 * (y j - Function.update y i (y i + s) j) ^ 2
      = S.L i / 2 * s ^ 2 := by
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · simp
    · intro j _ hj
      simp [Function.update_of_ne hj]
  rw [h1] at h
  rw [h2] at h
  exact h

@[blueprint "lem:adagrad-qtb-grad-diff"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting}, let
    $\mathbf{x}, \mathbf{y} \in \mathbb{R}^d$ and let $i \in [d]$. Then
    $$\bigl(\nabla_i F(\mathbf{y}) - \nabla_i F(\mathbf{x})\bigr)^2
      \le 9 L_i \sum_{j=1}^d L_j (x_j - y_j)^2,$$
    with $\nabla_i F$ as in \cref{def:adagrad-grad-coord}. -/)
  (proof := /-- Write $D = \bigl|\nabla_i F(\mathbf{y}) - \nabla_i F(\mathbf{x})\bigr|$ and
    $B = \sum_{j=1}^d L_j (x_j - y_j)^2$; note $B \ge 0$ because $L_j \ge 0$ by
    \cref{def:adagrad-setting}. Fix $s > 0$ and let $\mathbf{y}'$ be obtained from
    $\mathbf{y}$ by replacing its $i$-th coordinate by $y_i + s$.

    Applying the coordinate-wise smoothness assumption of \cref{def:adagrad-setting} to the
    pairs $(\mathbf{x}, \mathbf{y}')$ and $(\mathbf{x}, \mathbf{y})$ gives
    $$\Bigl|F(\mathbf{y}') - F(\mathbf{x})
        - \sum_{j=1}^d \nabla_j F(\mathbf{x})(y'_j - x_j)\Bigr|
      \le \sum_{j=1}^d \frac{L_j}{2}(x_j - y'_j)^2, \qquad
      \Bigl|F(\mathbf{y}) - F(\mathbf{x})
        - \sum_{j=1}^d \nabla_j F(\mathbf{x})(y_j - x_j)\Bigr|
      \le \sum_{j=1}^d \frac{L_j}{2}(x_j - y_j)^2 .$$
    Since $y'_j = y_j$ for $j \ne i$ and $y'_i = y_i + s$, subtracting the two arguments of
    the absolute values yields
    $$\sum_{j=1}^d \nabla_j F(\mathbf{x})(y'_j - x_j)
      - \sum_{j=1}^d \nabla_j F(\mathbf{x})(y_j - x_j) = s \nabla_i F(\mathbf{x}),$$
    while for the right-hand sides
    $$\sum_{j=1}^d \frac{L_j}{2}(x_j - y'_j)^2
      = \sum_{j=1}^d \frac{L_j}{2}(x_j - y_j)^2
        + \frac{L_i}{2}\bigl((x_i - y_i - s)^2 - (x_i - y_i)^2\bigr)
      = \frac{B}{2} + \frac{L_i}{2}\bigl(s^2 - 2 s (x_i - y_i)\bigr),$$
    because the two sums have identical terms for $j \ne i$.

    By \cref{lem:adagrad-qtb-grad-shift},
    $\bigl|F(\mathbf{y}') - F(\mathbf{y}) - s \nabla_i F(\mathbf{y})\bigr|
    \le \frac{L_i}{2} s^2$. Writing
    $$s\bigl(\nabla_i F(\mathbf{y}) - \nabla_i F(\mathbf{x})\bigr)
      = \bigl(F(\mathbf{y}') - F(\mathbf{y}) - s \nabla_i F(\mathbf{x})\bigr)
        - \bigl(F(\mathbf{y}') - F(\mathbf{y}) - s \nabla_i F(\mathbf{y})\bigr)$$
    and estimating the first bracket by the two displayed smoothness inequalities and the
    second by \cref{lem:adagrad-qtb-grad-shift}, we obtain, using
    $|x_i - y_i| \ge x_i - y_i$ and $s > 0$,
    $$s D \le B + s\bigl(L_i |x_i - y_i|\bigr) + L_i s^2 .$$

    This holds for every $s > 0$, so \cref{lem:adagrad-qtb-amgm-bound}, applied with the
    nonnegative quantities $B$ and $L_i$, gives
    $$D \le L_i |x_i - y_i| + 2 \sqrt{B L_i} .$$
    Since $L_i (x_i - y_i)^2 \le B$, we have
    $L_i |x_i-y_i| = \sqrt{L_i}\sqrt{L_i (x_i-y_i)^2} \le \sqrt{L_i}\sqrt{B}$, and
    $\sqrt{B L_i} = \sqrt{B}\sqrt{L_i}$, whence $D \le 3\sqrt{L_i}\sqrt{B}$. Squaring the
    inequality between the nonnegative quantities $D$ and $3\sqrt{L_i}\sqrt{B}$ and using
    $\sqrt{L_i}^2 = L_i$ and $\sqrt{B}^2 = B$ gives
    $D^2 \le 9 L_i B$, which is the assertion because
    $\bigl(\nabla_i F(\mathbf{y}) - \nabla_i F(\mathbf{x})\bigr)^2 = D^2$. -/)
  (title := /-- Coordinate-wise Lipschitz estimate for the gradient -/)
  (latexEnv := "lemma")]
lemma adagrad_qtb_grad_diff {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (x y : Fin S.d → ℝ) (i : Fin S.d) :
    (adagrad_grad_coord S.obj y i - adagrad_grad_coord S.obj x i) ^ 2
      ≤ 9 * S.L i * ∑ j, S.L j * (x j - y j) ^ 2 := by
  set B : ℝ := ∑ j, S.L j * (x j - y j) ^ 2 with hBdef
  have hB : 0 ≤ B := Finset.sum_nonneg fun j _ => by
    have := S.L_nonneg j
    positivity
  have hLi : 0 ≤ S.L i := S.L_nonneg i
  have hBi : S.L i * (x i - y i) ^ 2 ≤ B :=
    Finset.single_le_sum (f := fun j => S.L j * (x j - y j) ^ 2)
      (fun j _ => by have := S.L_nonneg j; positivity) (Finset.mem_univ i)
  have hhalf : ∑ j, S.L j / 2 * (x j - y j) ^ 2 = B / 2 := by
    rw [hBdef, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  have key : ∀ s : ℝ, 0 < s →
      s * |adagrad_grad_coord S.obj y i - adagrad_grad_coord S.obj x i|
        ≤ B + s * (S.L i * |x i - y i|) + S.L i * s ^ 2 := by
    intro s hs
    have hy' := S.obj_smooth x (Function.update y i (y i + s))
    have hy := S.obj_smooth x y
    have hshift := adagrad_qtb_grad_shift S y i s
    have hlin : ∑ j, adagrad_grad_coord S.obj x j
          * (Function.update y i (y i + s) j - x j)
        = (∑ j, adagrad_grad_coord S.obj x j * (y j - x j))
          + s * adagrad_grad_coord S.obj x i := by
      have hd : ∑ j, (adagrad_grad_coord S.obj x j
            * (Function.update y i (y i + s) j - x j)
          - adagrad_grad_coord S.obj x j * (y j - x j))
          = s * adagrad_grad_coord S.obj x i := by
        rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
        · simp
          ring
        · intro j _ hj
          simp [Function.update_of_ne hj]
      rw [Finset.sum_sub_distrib] at hd
      linarith
    have hquad : ∑ j, S.L j / 2 * (x j - Function.update y i (y i + s) j) ^ 2
        = B / 2 + S.L i / 2 * (s ^ 2 - 2 * s * (x i - y i)) := by
      have hd : ∑ j, (S.L j / 2 * (x j - Function.update y i (y i + s) j) ^ 2
          - S.L j / 2 * (x j - y j) ^ 2)
          = S.L i / 2 * (s ^ 2 - 2 * s * (x i - y i)) := by
        rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
        · simp
          ring
        · intro j _ hj
          simp [Function.update_of_ne hj]
      rw [Finset.sum_sub_distrib] at hd
      linarith [hhalf]
    rw [hlin, hquad] at hy'
    rw [hhalf] at hy
    have habs1 := abs_le.1 hy'
    have habs2 := abs_le.1 hy
    have habs3 := abs_le.1 hshift
    have hcross : -(S.L i * s * (x i - y i)) ≤ s * (S.L i * |x i - y i|) := by
      have h1 : -(x i - y i) ≤ |x i - y i| := neg_le_abs _
      nlinarith [mul_nonneg hLi hs.le]
    rcases abs_cases (adagrad_grad_coord S.obj y i - adagrad_grad_coord S.obj x i)
      with ⟨heq, _⟩ | ⟨heq, _⟩
    · rw [heq]
      nlinarith [habs1.1, habs1.2, habs2.1, habs2.2, habs3.1, habs3.2, hcross]
    · rw [heq]
      nlinarith [habs1.1, habs1.2, habs2.1, habs2.2, habs3.1, habs3.2, hcross]
  have hD := adagrad_qtb_amgm_bound (B := B) (C := S.L i * |x i - y i|)
    (D := |adagrad_grad_coord S.obj y i - adagrad_grad_coord S.obj x i|)
    (K := S.L i) hB hLi key
  have hsL : Real.sqrt (S.L i) ^ 2 = S.L i := Real.sq_sqrt hLi
  have hsB : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB
  have hsL0 : 0 ≤ Real.sqrt (S.L i) := Real.sqrt_nonneg _
  have hsB0 : 0 ≤ Real.sqrt B := Real.sqrt_nonneg _
  have hmul : Real.sqrt (B * S.L i) = Real.sqrt B * Real.sqrt (S.L i) :=
    Real.sqrt_mul hB _
  have hlin2 : S.L i * |x i - y i| ≤ Real.sqrt (S.L i) * Real.sqrt B := by
    have h1 : Real.sqrt (S.L i * (x i - y i) ^ 2) ≤ Real.sqrt B :=
      Real.sqrt_le_sqrt hBi
    have h2 : Real.sqrt (S.L i * (x i - y i) ^ 2)
        = Real.sqrt (S.L i) * |x i - y i| := by
      rw [Real.sqrt_mul hLi, Real.sqrt_sq_eq_abs]
    rw [h2] at h1
    nlinarith [abs_nonneg (x i - y i), mul_le_mul_of_nonneg_left h1 hsL0]
  have hfinal : |adagrad_grad_coord S.obj y i - adagrad_grad_coord S.obj x i|
      ≤ 3 * (Real.sqrt (S.L i) * Real.sqrt B) := by
    rw [hmul] at hD
    nlinarith
  have hsq := sq_abs (adagrad_grad_coord S.obj y i - adagrad_grad_coord S.obj x i)
  nlinarith [abs_nonneg (adagrad_grad_coord S.obj y i - adagrad_grad_coord S.obj x i),
    mul_nonneg hsL0 hsB0]

@[blueprint "lem:adagrad-qtb-iterate-dist"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting}, let
    $\omega \in \Omega$, let $j \in [d]$ and let $t \ge 1$. Then
    $$\bigl|w_{t,j}(\omega) - w_{1,j}\bigr| \le \eta (t - 1),$$
    where $\mathbf{w}_1$ is the deterministic initialisation of $S$. -/)
  (proof := /-- We argue by induction on $t \ge 1$.

    For $t = 1$ we have $w_{1,j}(\omega) = w_{1,j}$ by \cref{def:adagrad-setting}, so the
    left-hand side is $0$ and the right-hand side is $\eta \cdot 0 = 0$.

    Assume the bound for some $t \ge 1$. By the AdaGrad recursion of
    \cref{def:adagrad-setting},
    $$w_{t+1,j}(\omega) - w_{t,j}(\omega)
      = -\eta \frac{g_{t,j}(\omega)}{b_{t,j}(\omega) + \delta},
      \qquad b_{t,j}(\omega) = \sqrt{\sum_{s=1}^t g_{s,j}(\omega)^2} .$$
    Since $g_{t,j}(\omega)^2 \le \sum_{s=1}^t g_{s,j}(\omega)^2$, all terms of the sum
    being nonnegative and $t$ belonging to $\{1,\dots,t\}$, monotonicity of the square root
    together with $\sqrt{g_{t,j}(\omega)^2} = |g_{t,j}(\omega)|$ gives
    $|g_{t,j}(\omega)| \le b_{t,j}(\omega)$. As $\delta > 0$ and $b_{t,j}(\omega) \ge 0$,
    the denominator $b_{t,j}(\omega) + \delta$ is positive and exceeds
    $|g_{t,j}(\omega)|$, so
    $$\Bigl|\frac{g_{t,j}(\omega)}{b_{t,j}(\omega)+\delta}\Bigr| \le 1,
      \qquad\text{hence}\qquad
      \bigl|w_{t+1,j}(\omega) - w_{t,j}(\omega)\bigr| \le \eta,$$
    using $\eta > 0$.

    By the triangle inequality and the induction hypothesis,
    $$\bigl|w_{t+1,j}(\omega) - w_{1,j}\bigr|
      \le \bigl|w_{t+1,j}(\omega) - w_{t,j}(\omega)\bigr|
        + \bigl|w_{t,j}(\omega) - w_{1,j}\bigr|
      \le \eta + \eta (t-1) = \eta \bigl((t+1) - 1\bigr),$$
    which is the assertion for $t+1$. -/)
  (title := /-- Displacement of the iterates from the initialisation -/)
  (latexEnv := "lemma")]
lemma adagrad_qtb_iterate_dist {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (ω : Ω) (j : Fin S.d) (t : ℕ) (ht : 1 ≤ t) :
    |S.w t ω j - S.init j| ≤ S.η * ((t : ℝ) - 1) := by
  induction t, ht using Nat.le_induction with
  | base => simp [S.w_one ω]
  | succ n hn ih =>
    have hb : |S.g n ω j| ≤ Real.sqrt (∑ s ∈ Finset.Icc 1 n, S.g s ω j ^ 2) := by
      have hmem : n ∈ Finset.Icc 1 n := Finset.mem_Icc.2 ⟨hn, le_rfl⟩
      have hle : S.g n ω j ^ 2 ≤ ∑ s ∈ Finset.Icc 1 n, S.g s ω j ^ 2 :=
        Finset.single_le_sum (f := fun s => S.g s ω j ^ 2)
          (fun s _ => sq_nonneg _) hmem
      calc |S.g n ω j| = Real.sqrt (S.g n ω j ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ _ := Real.sqrt_le_sqrt hle
    have hden : (0:ℝ) < Real.sqrt (∑ s ∈ Finset.Icc 1 n, S.g s ω j ^ 2) + S.δ := by
      have := Real.sqrt_nonneg (∑ s ∈ Finset.Icc 1 n, S.g s ω j ^ 2)
      linarith [S.delta_pos]
    have hstep : |S.w (n + 1) ω j - S.w n ω j| ≤ S.η := by
      rw [S.adagrad_update n hn ω j]
      have hq : |S.g n ω j / (Real.sqrt (∑ s ∈ Finset.Icc 1 n, S.g s ω j ^ 2) + S.δ)|
          ≤ 1 := by
        rw [abs_div, abs_of_pos hden, div_le_one hden]
        linarith [S.delta_pos]
      have : |S.η * (S.g n ω j
          / (Real.sqrt (∑ s ∈ Finset.Icc 1 n, S.g s ω j ^ 2) + S.δ))| ≤ S.η * 1 := by
        rw [abs_mul, abs_of_pos S.eta_pos]
        exact mul_le_mul_of_nonneg_left hq S.eta_pos.le
      simpa [abs_sub_comm] using this
    have hsum : |S.w (n + 1) ω j - S.init j|
        ≤ |S.w (n + 1) ω j - S.w n ω j| + |S.w n ω j - S.init j| :=
      abs_sub_le _ _ _
    push_cast
    linarith [hsum, hstep, ih]

@[blueprint "lem:adagrad-qtb-grad-det-bound"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting}, let
    $\omega \in \Omega$, let $i \in [d]$ and let $t \ge 1$. Then
    $$\nabla_i F(\mathbf{w}_t(\omega))^2
      \le 2 \nabla_i F(\mathbf{w}_1)^2
        + 18 L_i \|\mathbf{L}\|_1 \eta^2 (t-1)^2,$$
    with $\nabla_i F$ as in \cref{def:adagrad-grad-coord}, $\|\cdot\|_1$ as in
    \cref{def:adagrad-l1-norm} and $\mathbf{w}_1$ the deterministic initialisation of
    $S$. -/)
  (proof := /-- By \cref{lem:adagrad-qtb-grad-diff}, applied with
    $\mathbf{x} = \mathbf{w}_1$ and $\mathbf{y} = \mathbf{w}_t(\omega)$,
    $$\bigl(\nabla_i F(\mathbf{w}_t(\omega)) - \nabla_i F(\mathbf{w}_1)\bigr)^2
      \le 9 L_i \sum_{j=1}^d L_j \bigl(w_{1,j} - w_{t,j}(\omega)\bigr)^2 .$$

    For each $j$, \cref{lem:adagrad-qtb-iterate-dist} gives
    $\bigl|w_{t,j}(\omega) - w_{1,j}\bigr| \le \eta (t-1)$, and since $t \ge 1$ the
    right-hand side is nonnegative; squaring this inequality between nonnegative quantities
    and using $\bigl(w_{1,j} - w_{t,j}(\omega)\bigr)^2
    = \bigl|w_{t,j}(\omega) - w_{1,j}\bigr|^2$ yields
    $\bigl(w_{1,j} - w_{t,j}(\omega)\bigr)^2 \le \eta^2 (t-1)^2$. Since $L_j \ge 0$ by
    \cref{def:adagrad-setting}, multiplying by $L_j$ and summing over $j$ gives
    $$\sum_{j=1}^d L_j \bigl(w_{1,j} - w_{t,j}(\omega)\bigr)^2
      \le \Bigl(\sum_{j=1}^d L_j\Bigr) \eta^2 (t-1)^2
      = \|\mathbf{L}\|_1 \eta^2 (t-1)^2,$$
    the last equality because $L_j \ge 0$ gives $|L_j| = L_j$ for every $j$, so that the
    sum equals the $\ell_1$-norm of \cref{def:adagrad-l1-norm}. As $L_i \ge 0$, this
    bounds the right-hand side of the first display by
    $9 L_i \|\mathbf{L}\|_1 \eta^2 (t-1)^2$.

    Finally, for all reals $a$ and $b$ one has $a^2 \le 2 (a-b)^2 + 2 b^2$, because
    $2(a-b)^2 + 2b^2 - a^2 = (a - 2b)^2 \ge 0$. Applying this with
    $a = \nabla_i F(\mathbf{w}_t(\omega))$ and $b = \nabla_i F(\mathbf{w}_1)$ and inserting
    the bound just obtained gives the assertion. -/)
  (title := /-- Deterministic bound on the gradient along the trajectory -/)
  (latexEnv := "lemma")]
lemma adagrad_qtb_grad_det_bound {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (ω : Ω) (i : Fin S.d) (t : ℕ) (ht : 1 ≤ t) :
    adagrad_grad_coord S.obj (S.w t ω) i ^ 2
      ≤ 2 * adagrad_grad_coord S.obj S.init i ^ 2
        + 18 * S.L i * adagrad_l1_norm S.L * S.η ^ 2 * ((t : ℝ) - 1) ^ 2 := by
  have hdiff := adagrad_qtb_grad_diff S S.init (S.w t ω) i
  have ht1 : (0:ℝ) ≤ (t : ℝ) - 1 := by
    have : (1:ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    linarith
  have hbound : ∑ j, S.L j * (S.init j - S.w t ω j) ^ 2
      ≤ adagrad_l1_norm S.L * (S.η ^ 2 * ((t : ℝ) - 1) ^ 2) := by
    rw [adagrad_l1_norm, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    have hdist := adagrad_qtb_iterate_dist S ω j t ht
    have hsq : (S.init j - S.w t ω j) ^ 2 ≤ (S.η * ((t : ℝ) - 1)) ^ 2 := by
      have habs : |S.init j - S.w t ω j| ≤ S.η * ((t : ℝ) - 1) := by
        rw [abs_sub_comm]; exact hdist
      have h0 : 0 ≤ S.η * ((t : ℝ) - 1) := mul_nonneg S.eta_pos.le ht1
      nlinarith [abs_nonneg (S.init j - S.w t ω j), sq_abs (S.init j - S.w t ω j)]
    rw [abs_of_nonneg (S.L_nonneg j)]
    calc S.L j * (S.init j - S.w t ω j) ^ 2
        ≤ S.L j * (S.η * ((t : ℝ) - 1)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (S.L_nonneg j)
      _ = S.L j * (S.η ^ 2 * ((t : ℝ) - 1) ^ 2) := by ring
  have hLi : 0 ≤ S.L i := S.L_nonneg i
  nlinarith [mul_le_mul_of_nonneg_left hbound (by positivity : (0:ℝ) ≤ 9 * S.L i),
    sq_nonneg (adagrad_grad_coord S.obj (S.w t ω) i
      - 2 * adagrad_grad_coord S.obj S.init i)]

@[blueprint "lem:adagrad-qtb-le-linf"
  (statement := /-- Let $d \ge 1$, let $\mathbf{v} \in \mathbb{R}^d$ and let
    $i \in [d]$. Then $v_i^2 \le \|\mathbf{v}\|_\infty^2$, with $\|\cdot\|_\infty$ as in
    \cref{def:adagrad-linf-norm}. -/)
  (proof := /-- The family $\bigl(|v_j|\bigr)_{j \in [d]}$ is indexed by a finite type,
    hence its range is bounded above, and therefore $|v_i| \le \sup_j |v_j|
    = \|\mathbf{v}\|_\infty$ by \cref{def:adagrad-linf-norm}. Since $|v_i| \ge 0$ and
    squaring is monotone on the nonnegative reals, $|v_i|^2 \le \|\mathbf{v}\|_\infty^2$,
    and $|v_i|^2 = v_i^2$. -/)
  (title := /-- Coordinates are bounded by the max-norm -/)
  (latexEnv := "lemma")]
lemma adagrad_qtb_le_linf {d : ℕ} (v : Fin d → ℝ) (i : Fin d) :
    v i ^ 2 ≤ adagrad_linf_norm v ^ 2 := by
  have h : |v i| ≤ adagrad_linf_norm v := Finite.le_ciSup (fun j => |v j|) i
  have h0 : 0 ≤ |v i| := abs_nonneg _
  nlinarith [sq_abs (v i)]

@[blueprint "lem:adagrad-qtb-memlp-g"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting}, let
    $i \in [d]$ and let $t \in \mathbb{N}$. Then the random variable
    $\omega \mapsto g_{t,i}(\omega)$ belongs to $L^2(\mu)$. -/)
  (proof := /-- The map $\omega \mapsto \mathbf{g}_t(\omega)$ is
    $\mathcal{F}_t$-measurable by \cref{def:adagrad-setting}, and $\mathcal{F}_t$ is
    contained in the ambient $\sigma$-algebra because $(\mathcal{F}_t)_t$ is a filtration
    of sub-$\sigma$-algebras; composing with the evaluation at the coordinate $i$, which is
    measurable, shows that $g_{t,i}$ is measurable, hence almost everywhere strongly
    measurable.

    By \cref{def:adagrad-setting} the function $g_{t,i}^2$ is $\mu$-integrable. For an
    almost everywhere strongly measurable real-valued function, membership in $L^2(\mu)$ is
    equivalent to the integrability of its square, so $g_{t,i} \in L^2(\mu)$. -/)
  (title := /-- Square-integrability of the stochastic gradient coordinates -/)
  (latexEnv := "lemma")]
lemma adagrad_qtb_memlp_g {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (i : Fin S.d) (t : ℕ) : MemLp (fun ω => S.g t ω i) 2 S.μ := by
  have hgm : Measurable (fun ω => S.g t ω i) :=
    (measurable_pi_apply i).comp ((S.g_adapted t).mono (S.ℱ.le t) le_rfl)
  exact (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).2 (S.g_sq_integrable t i)

@[blueprint "lem:adagrad-qtb-memlp-grad"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting}, let
    $i \in [d]$ and let $t \ge 1$. Then the random variable
    $\omega \mapsto \nabla_i F(\mathbf{w}_t(\omega))$ belongs to $L^2(\mu)$, with
    $\nabla_i F$ as in \cref{def:adagrad-grad-coord}. -/)
  (proof := /-- By \cref{lem:adagrad-qtb-memlp-g} the random variable $g_{t,i}$ belongs to
    $L^2(\mu)$.

    Since conditional expectation is a contraction on $L^p$ for $p \ge 1$, the conditional
    expectation $\mathbb{E}[g_{t,i} \mid \mathcal{F}_{t-1}]$ also belongs to $L^2(\mu)$. By
    the unbiasedness assumption of \cref{def:adagrad-setting} and $t \ge 1$, this
    conditional expectation agrees $\mu$-almost everywhere with
    $\nabla_i F(\mathbf{w}_t)$. Membership in $L^2$ is invariant under almost everywhere
    equality, so $\nabla_i F(\mathbf{w}_t) \in L^2(\mu)$. -/)
  (title := /-- Square-integrability of the gradient coordinates -/)
  (latexEnv := "lemma")]
lemma adagrad_qtb_memlp_grad {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (i : Fin S.d) (t : ℕ) (ht : 1 ≤ t) :
    MemLp (fun ω => adagrad_grad_coord S.obj (S.w t ω) i) 2 S.μ := by
  haveI := S.isProbabilityMeasure
  exact (MemLp.condExp (m := S.ℱ (t - 1)) one_le_two
    (adagrad_qtb_memlp_g S i t)).ae_eq (S.g_unbiased t ht i)

@[blueprint "lem:adagrad-qtb-noise-second-moment"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting}, let
    $i \in [d]$ and let $t \ge 1$. Then
    $$\mathbb{E}\bigl[\bigl(g_{t,i} - \nabla_i F(\mathbf{w}_t)\bigr)^2\bigr]
      \le \sigma_i^2,$$
    with $\nabla_i F$ as in \cref{def:adagrad-grad-coord}. -/)
  (proof := /-- Since $\mathcal{F}_{t-1}$ is a sub-$\sigma$-algebra of the ambient one and
    $\mu$ is a probability measure, the expectation of a conditional expectation equals the
    expectation of the original function, so
    $$\mathbb{E}\bigl[\bigl(g_{t,i} - \nabla_i F(\mathbf{w}_t)\bigr)^2\bigr]
      = \mathbb{E}\Bigl[\mathbb{E}\bigl[\bigl(g_{t,i}
        - \nabla_i F(\mathbf{w}_t)\bigr)^2 \bigm| \mathcal{F}_{t-1}\bigr]\Bigr].$$

    By the bounded-variance assumption of \cref{def:adagrad-setting} and $t \ge 1$, the
    inner conditional expectation is at most the constant $\sigma_i^2$ almost everywhere.
    Conditional expectations are integrable and constants are integrable because $\mu$ is a
    probability measure, so integrating this almost-everywhere inequality gives
    $$\mathbb{E}\Bigl[\mathbb{E}\bigl[\bigl(g_{t,i}
        - \nabla_i F(\mathbf{w}_t)\bigr)^2 \bigm| \mathcal{F}_{t-1}\bigr]\Bigr]
      \le \mathbb{E}\bigl[\sigma_i^2\bigr] = \sigma_i^2,$$
    the last equality because $\mu$ is a probability measure. -/)
  (title := /-- Second moment of the gradient noise -/)
  (latexEnv := "lemma")]
lemma adagrad_qtb_noise_second_moment {Ω : Type} [MeasurableSpace Ω]
    (S : adagrad_setting Ω) (i : Fin S.d) (t : ℕ) (ht : 1 ≤ t) :
    (∫ ω, (S.g t ω i - adagrad_grad_coord S.obj (S.w t ω) i) ^ 2 ∂S.μ) ≤ S.σ i ^ 2 := by
  haveI := S.isProbabilityMeasure
  calc (∫ ω, (S.g t ω i - adagrad_grad_coord S.obj (S.w t ω) i) ^ 2 ∂S.μ)
      = ∫ ω, (S.μ[fun ω => (S.g t ω i - adagrad_grad_coord S.obj (S.w t ω) i) ^ 2|
          S.ℱ (t - 1)]) ω ∂S.μ := (integral_condExp (S.ℱ.le (t - 1))).symm
    _ ≤ ∫ _ : Ω, S.σ i ^ 2 ∂S.μ := by
        refine integral_mono_ae integrable_condExp (integrable_const _) ?_
        exact S.g_bounded_variance t ht i
    _ = S.σ i ^ 2 := by simp

@[blueprint "lem:adagrad-qtb-sq-integral-bound"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting} and let
    $i \in [d]$. Then
    $$\mathbb{E}\Bigl[\sum_{t=1}^T g_{t,i}^2\Bigr]
      \le 2 T \|\bm\sigma\|_\infty^2
        + 4 T \|\nabla F(\mathbf{w}_1)\|_\infty^2
        + 36 L_i \|\mathbf{L}\|_1 \eta^2 T^3,$$
    with $\|\cdot\|_1$ as in \cref{def:adagrad-l1-norm}, $\|\cdot\|_\infty$ as in
    \cref{def:adagrad-linf-norm} and $\nabla F$ as in
    \cref{def:adagrad-grad-coord}. -/)
  (proof := /-- Fix $t \in \{1, \dots, T\}$. For all reals $a$ and $b$ one has
    $a^2 \le 2 (a-b)^2 + 2 b^2$, because $2(a-b)^2 + 2b^2 - a^2 = (a-2b)^2 \ge 0$; applied
    with $a = g_{t,i}$ and $b = \nabla_i F(\mathbf{w}_t)$ this gives, pointwise on
    $\Omega$,
    $$g_{t,i}^2 \le 2 \bigl(g_{t,i} - \nabla_i F(\mathbf{w}_t)\bigr)^2
      + 2 \nabla_i F(\mathbf{w}_t)^2 .$$
    Both summands on the right are integrable: the first because $g_{t,i}$ and
    $\nabla_i F(\mathbf{w}_t)$ are square-integrable by
    \cref{lem:adagrad-qtb-memlp-g} and \cref{lem:adagrad-qtb-memlp-grad}, so their
    difference is square-integrable and its square is integrable, and the second for the
    same reason. Hence, integrating and using
    \cref{lem:adagrad-qtb-noise-second-moment} for the first term,
    $$\mathbb{E}\bigl[g_{t,i}^2\bigr]
      \le 2 \sigma_i^2 + 2\, \mathbb{E}\bigl[\nabla_i F(\mathbf{w}_t)^2\bigr] .$$

    By \cref{lem:adagrad-qtb-grad-det-bound}, pointwise on $\Omega$,
    $$\nabla_i F(\mathbf{w}_t)^2 \le 2 \nabla_i F(\mathbf{w}_1)^2
      + 18 L_i \|\mathbf{L}\|_1 \eta^2 (t-1)^2 ,$$
    the right-hand side being a constant; since $\mathbb{P}$ is a probability measure, the
    integral of that constant is the constant itself, so
    $\mathbb{E}\bigl[\nabla_i F(\mathbf{w}_t)^2\bigr]$ is bounded by it. Combining,
    $$\mathbb{E}\bigl[g_{t,i}^2\bigr]
      \le 2 \sigma_i^2 + 4 \nabla_i F(\mathbf{w}_1)^2
        + 36 L_i \|\mathbf{L}\|_1 \eta^2 (t-1)^2 .$$
    By \cref{lem:adagrad-qtb-le-linf} we may replace $\sigma_i^2$ by
    $\|\bm\sigma\|_\infty^2$ and $\nabla_i F(\mathbf{w}_1)^2$ by
    $\|\nabla F(\mathbf{w}_1)\|_\infty^2$, and for $1 \le t \le T$ we have
    $0 \le t - 1 \le T$, hence $(t-1)^2 \le T^2$; the coefficient
    $36 L_i \|\mathbf{L}\|_1 \eta^2$ is nonnegative because $L_i \ge 0$, the $\ell_1$-norm
    of \cref{def:adagrad-l1-norm} is nonnegative and $\eta^2 \ge 0$. Therefore each term
    satisfies
    $$\mathbb{E}\bigl[g_{t,i}^2\bigr]
      \le 2 \|\bm\sigma\|_\infty^2 + 4 \|\nabla F(\mathbf{w}_1)\|_\infty^2
        + 36 L_i \|\mathbf{L}\|_1 \eta^2 T^2 .$$

    Since each $g_{t,i}^2$ is integrable by \cref{def:adagrad-setting}, the expectation of
    the finite sum $\sum_{t=1}^T g_{t,i}^2$ is the sum of the expectations, and summing the
    last display over the $T$ indices $t \in \{1,\dots,T\}$ gives
    $$\mathbb{E}\Bigl[\sum_{t=1}^T g_{t,i}^2\Bigr]
      \le T\Bigl(2\|\bm\sigma\|_\infty^2 + 4\|\nabla F(\mathbf{w}_1)\|_\infty^2
        + 36 L_i \|\mathbf{L}\|_1 \eta^2 T^2\Bigr),$$
    which is the assertion. -/)
  (title := /-- Bound on the expected accumulated squared stochastic gradients -/)
  (latexEnv := "lemma")]
lemma adagrad_qtb_sq_integral_bound {Ω : Type} [MeasurableSpace Ω]
    (S : adagrad_setting Ω) (i : Fin S.d) :
    (∫ ω, ∑ t ∈ Finset.Icc 1 S.T, S.g t ω i ^ 2 ∂S.μ)
      ≤ 2 * (S.T : ℝ) * adagrad_linf_norm S.σ ^ 2
        + 4 * (S.T : ℝ)
            * adagrad_linf_norm (fun j => adagrad_grad_coord S.obj S.init j) ^ 2
        + 36 * S.L i * adagrad_l1_norm S.L * S.η ^ 2 * (S.T : ℝ) ^ 3 := by
  haveI := S.isProbabilityMeasure
  have hL1 : 0 ≤ adagrad_l1_norm S.L :=
    Finset.sum_nonneg fun j _ => abs_nonneg _
  have hLi : 0 ≤ S.L i := S.L_nonneg i
  set C : ℝ := 2 * adagrad_linf_norm S.σ ^ 2
      + 4 * adagrad_linf_norm (fun j => adagrad_grad_coord S.obj S.init j) ^ 2
      + 36 * S.L i * adagrad_l1_norm S.L * S.η ^ 2 * (S.T : ℝ) ^ 2 with hCdef
  have hterm : ∀ t ∈ Finset.Icc 1 S.T, (∫ ω, S.g t ω i ^ 2 ∂S.μ) ≤ C := by
    intro t ht
    obtain ⟨ht1, htT⟩ := Finset.mem_Icc.1 ht
    have hnoise := adagrad_qtb_noise_second_moment S i t ht1
    have hgsq := S.g_sq_integrable t i
    have hdiff : Integrable
        (fun ω => (S.g t ω i - adagrad_grad_coord S.obj (S.w t ω) i) ^ 2) S.μ :=
      ((adagrad_qtb_memlp_g S i t).sub
        (adagrad_qtb_memlp_grad S i t ht1)).integrable_sq
    have hgradsq : Integrable
        (fun ω => adagrad_grad_coord S.obj (S.w t ω) i ^ 2) S.μ :=
      (adagrad_qtb_memlp_grad S i t ht1).integrable_sq
    have hgradbound : (∫ ω, adagrad_grad_coord S.obj (S.w t ω) i ^ 2 ∂S.μ)
        ≤ 2 * adagrad_grad_coord S.obj S.init i ^ 2
          + 18 * S.L i * adagrad_l1_norm S.L * S.η ^ 2 * ((t : ℝ) - 1) ^ 2 := by
      calc (∫ ω, adagrad_grad_coord S.obj (S.w t ω) i ^ 2 ∂S.μ)
          ≤ ∫ _ω : Ω, (2 * adagrad_grad_coord S.obj S.init i ^ 2
              + 18 * S.L i * adagrad_l1_norm S.L * S.η ^ 2
                * ((t : ℝ) - 1) ^ 2) ∂S.μ :=
            integral_mono hgradsq (integrable_const _)
              fun ω => adagrad_qtb_grad_det_bound S ω i t ht1
        _ = 2 * adagrad_grad_coord S.obj S.init i ^ 2
              + 18 * S.L i * adagrad_l1_norm S.L * S.η ^ 2
                * ((t : ℝ) - 1) ^ 2 := by simp
    have hsplit : (∫ ω, S.g t ω i ^ 2 ∂S.μ)
        ≤ 2 * (∫ ω, (S.g t ω i - adagrad_grad_coord S.obj (S.w t ω) i) ^ 2 ∂S.μ)
          + 2 * ∫ ω, adagrad_grad_coord S.obj (S.w t ω) i ^ 2 ∂S.μ := by
      calc (∫ ω, S.g t ω i ^ 2 ∂S.μ)
          ≤ ∫ ω, (2 * (S.g t ω i - adagrad_grad_coord S.obj (S.w t ω) i) ^ 2
              + 2 * adagrad_grad_coord S.obj (S.w t ω) i ^ 2) ∂S.μ :=
            integral_mono hgsq ((hdiff.const_mul 2).add (hgradsq.const_mul 2))
              fun ω => by
                nlinarith [sq_nonneg (S.g t ω i
                  - 2 * adagrad_grad_coord S.obj (S.w t ω) i)]
        _ = 2 * (∫ ω, (S.g t ω i - adagrad_grad_coord S.obj (S.w t ω) i) ^ 2 ∂S.μ)
              + 2 * ∫ ω, adagrad_grad_coord S.obj (S.w t ω) i ^ 2 ∂S.μ := by
            rw [integral_add (hdiff.const_mul 2) (hgradsq.const_mul 2),
              integral_const_mul, integral_const_mul]
    have htsq : ((t : ℝ) - 1) ^ 2 ≤ (S.T : ℝ) ^ 2 := by
      have h1 : (1:ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
      have h2 : (t : ℝ) ≤ (S.T : ℝ) := by exact_mod_cast htT
      nlinarith
    have hσ : S.σ i ^ 2 ≤ adagrad_linf_norm S.σ ^ 2 := adagrad_qtb_le_linf S.σ i
    have hg1 : adagrad_grad_coord S.obj S.init i ^ 2
        ≤ adagrad_linf_norm (fun j => adagrad_grad_coord S.obj S.init j) ^ 2 :=
      adagrad_qtb_le_linf (fun j => adagrad_grad_coord S.obj S.init j) i
    rw [hCdef]
    nlinarith [mul_le_mul_of_nonneg_left htsq
      (by positivity : (0:ℝ) ≤ 36 * S.L i * adagrad_l1_norm S.L * S.η ^ 2)]
  have hint : (∫ ω, ∑ t ∈ Finset.Icc 1 S.T, S.g t ω i ^ 2 ∂S.μ)
      = ∑ t ∈ Finset.Icc 1 S.T, ∫ ω, S.g t ω i ^ 2 ∂S.μ :=
    integral_finset_sum _ fun t _ => S.g_sq_integrable t i
  rw [hint]
  have hsum : ∑ t ∈ Finset.Icc 1 S.T, (∫ ω, S.g t ω i ^ 2 ∂S.μ)
      ≤ ∑ _t ∈ Finset.Icc 1 S.T, C := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Nat.card_Icc] at hsum
  have hcard : ((S.T + 1 - 1 : ℕ) : ℝ) = (S.T : ℝ) := by
    simp
  rw [nsmul_eq_mul, hcard] at hsum
  rw [hCdef] at hsum
  nlinarith [hsum]

@[blueprint "lem:adagrad-quadratic-term-bound"
  (statement := /-- There exists a real constant $c \ge 1$, absolute in the sense that it
    does not depend on any of the data of the setting, with the following property. For
    every AdaGrad setting $S$ as in \cref{def:adagrad-setting} and every $i \in [d]$,
    $$\mathbb{E}\Bigl[\sum_{t=1}^T \eta_{t,i}^2 g_{t,i}^2\Bigr] \le \eta^2 \Lambda_c(S),$$
    where $\eta_{t,i}$ is as in \cref{def:adagrad-step} and $\Lambda_c(S) =
    \log\bigl(c \cdot (1 + h(T))\bigr)$ is the normalised logarithmic budget of
    \cref{def:adagrad-log-budget} with $h(T)$ as in \cref{def:adagrad-h}. Since
    $\eta_{t,i} = \eta/(b_{t,i} + \delta)$, the assertion is equivalent to
    $$\mathbb{E}\Bigl[\sum_{t=1}^T
      \frac{g_{t,i}^2}{(b_{t,i} + \delta)^2}\Bigr] \le \Lambda_c(S),$$
    the factor $\eta^2 > 0$ cancelling; this second form is the one in which the source
    states the estimate, and it makes visible that the bound is invariant under rescaling
    of $\eta$. -/)
  (proof := /-- We prove the assertion with the explicit absolute constant $c = 37$, which
    satisfies $c \ge 1$. Fix an AdaGrad setting $S$ and a coordinate $i \in [d]$, and write
    $A_T(\omega) = \sum_{t=1}^T g_{t,i}(\omega)^2$. By \cref{def:adagrad-setting} each
    $g_{t,i}^2$ is $\mu$-integrable, hence so is the finite sum $A_T$, and $A_T \ge 0$
    pointwise, so $A_T/\delta^2 \ge 0$ because $\delta > 0$.

    \emph{Step 1: a pathwise logarithmic bound.} By \cref{def:adagrad-step} we have
    $\eta_{t,i}(\omega)^2 g_{t,i}(\omega)^2
    = \eta^2 \, g_{t,i}(\omega)^2/\bigl(\sqrt{\sum_{s=1}^t g_{s,i}(\omega)^2}
      + \delta\bigr)^2$
    for every $t$, so, factoring out $\eta^2$ from the finite sum,
    $$\sum_{t=1}^T \eta_{t,i}(\omega)^2 g_{t,i}(\omega)^2
      = \eta^2 \sum_{t=1}^T
        \frac{g_{t,i}(\omega)^2}{\bigl(\sqrt{\sum_{s=1}^t g_{s,i}(\omega)^2}
          + \delta\bigr)^2} .$$
    Applying \cref{lem:adagrad-qtb-telescope} with $\delta > 0$ and the nonnegative
    sequence $a_t = g_{t,i}(\omega)^2$ bounds the sum on the right by
    $\log\bigl(1 + A_T(\omega)/\delta^2\bigr)$, and multiplying by $\eta^2 \ge 0$ gives,
    for every $\omega$,
    $$\sum_{t=1}^T \eta_{t,i}(\omega)^2 g_{t,i}(\omega)^2
      \le \eta^2 \log\Bigl(1 + \frac{A_T(\omega)}{\delta^2}\Bigr) .$$

    \emph{Step 2: integration.} The left-hand side is nonnegative pointwise, being a finite
    sum of products of squares, and the right-hand side is $\mu$-integrable by
    \cref{lem:adagrad-qtb-log-integrable} applied to $A_T/\delta^2$. Integrating the
    inequality of Step 1 and pulling the constant $\eta^2$ out of the integral gives
    $$\mathbb{E}\Bigl[\sum_{t=1}^T \eta_{t,i}^2 g_{t,i}^2\Bigr]
      \le \eta^2 \, \mathbb{E}\Bigl[\log\Bigl(1
        + \frac{A_T}{\delta^2}\Bigr)\Bigr] .$$

    \emph{Step 3: Jensen's inequality.} By \cref{lem:adagrad-qtb-jensen-log}, applied to
    the integrable nonnegative function $A_T/\delta^2$,
    $$\mathbb{E}\Bigl[\log\Bigl(1 + \frac{A_T}{\delta^2}\Bigr)\Bigr]
      \le \log\Bigl(1 + \frac{\mathbb{E}[A_T]}{\delta^2}\Bigr),$$
    where we used that the expectation of $A_T/\delta^2$ equals
    $\mathbb{E}[A_T]/\delta^2$.

    \emph{Step 4: the moment bound.} By \cref{lem:adagrad-qtb-sq-integral-bound},
    $$\mathbb{E}[A_T] \le 2 T \|\bm\sigma\|_\infty^2
      + 4 T \|\nabla F(\mathbf{w}_1)\|_\infty^2
      + 36 L_i \|\mathbf{L}\|_1 \eta^2 T^3 .$$
    Since $L_j \ge 0$ for all $j$ by \cref{def:adagrad-setting}, we have
    $|L_i| = L_i$, and the coordinate $i$ is bounded by the supremum of
    \cref{def:adagrad-linf-norm} over the finite index set, so
    $L_i \le \|\mathbf{L}\|_\infty$; multiplying this by the nonnegative quantity
    $\|\mathbf{L}\|_1 \eta^2 T^3$ gives
    $36 L_i \|\mathbf{L}\|_1 \eta^2 T^3
    \le 36 \eta^2 \|\mathbf{L}\|_\infty \|\mathbf{L}\|_1 T^3$. As
    $2 \le 36$ and $4 \le 36$ and the two remaining summands
    $T \|\bm\sigma\|_\infty^2$ and $T\|\nabla F(\mathbf{w}_1)\|_\infty^2$ are nonnegative,
    we obtain
    $$\mathbb{E}[A_T] \le 36\bigl(T \|\bm\sigma\|_\infty^2
      + T \|\nabla F(\mathbf{w}_1)\|_\infty^2
      + \eta^2 \|\mathbf{L}\|_\infty \|\mathbf{L}\|_1 T^3\bigr),$$
    and dividing by $\delta^2 > 0$, the bracket being exactly $\delta^2 h(T)$ with $h(T)$
    as in \cref{def:adagrad-h}, this reads
    $\mathbb{E}[A_T]/\delta^2 \le 36 \, h(T)$.

    \emph{Step 5: conclusion.} Every summand of the numerator of $h(T)$ is nonnegative and
    $\delta^2 > 0$, so $h(T) \ge 0$ and therefore
    $$1 + \frac{\mathbb{E}[A_T]}{\delta^2} \le 1 + 36 h(T) \le 37\bigl(1 + h(T)\bigr) .$$
    Both sides are positive, so monotonicity of the logarithm gives
    $$\log\Bigl(1 + \frac{\mathbb{E}[A_T]}{\delta^2}\Bigr)
      \le \log\bigl(37 (1 + h(T))\bigr) = \Lambda_{37}(S)$$
    with $\Lambda_c(S)$ as in \cref{def:adagrad-log-budget}. Chaining this with Steps 2 and
    3 and multiplying by $\eta^2 \ge 0$ yields
    $\mathbb{E}\bigl[\sum_{t=1}^T \eta_{t,i}^2 g_{t,i}^2\bigr]
    \le \eta^2 \Lambda_{37}(S)$, which is the assertion for $c = 37$. -/)
  (title := /-- Bound on the accumulated quadratic term -/)
  (latexEnv := "lemma")]
lemma adagrad_quadratic_term_bound :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : adagrad_setting Ω)
      (i : Fin S.d),
      ∫ ω, ∑ t ∈ Finset.Icc 1 S.T, adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2 ∂S.μ
        ≤ S.η ^ 2 * adagrad_log_budget S c := by
  refine ⟨37, by norm_num, ?_⟩
  intro Ω _ S i
  haveI := S.isProbabilityMeasure
  have hδ : 0 < S.δ := S.delta_pos
  have hδ2 : (0:ℝ) < S.δ ^ 2 := by positivity
  have hAint : Integrable (fun ω => ∑ t ∈ Finset.Icc 1 S.T, S.g t ω i ^ 2) S.μ :=
    integrable_finset_sum _ fun t _ => S.g_sq_integrable t i
  have hfint : Integrable
      (fun ω => (∑ t ∈ Finset.Icc 1 S.T, S.g t ω i ^ 2) / S.δ ^ 2) S.μ :=
    hAint.div_const _
  have hf0 : 0 ≤ᵐ[S.μ] fun ω => (∑ t ∈ Finset.Icc 1 S.T, S.g t ω i ^ 2) / S.δ ^ 2 :=
    Filter.Eventually.of_forall fun ω =>
      div_nonneg (Finset.sum_nonneg fun t _ => sq_nonneg _) hδ2.le
  have hlogint : Integrable
      (fun ω => Real.log (1 + (∑ t ∈ Finset.Icc 1 S.T, S.g t ω i ^ 2) / S.δ ^ 2)) S.μ :=
    adagrad_qtb_log_integrable S.μ _ hfint hf0
  have hpoint : ∀ ω, ∑ t ∈ Finset.Icc 1 S.T, adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2
      ≤ S.η ^ 2
        * Real.log (1 + (∑ t ∈ Finset.Icc 1 S.T, S.g t ω i ^ 2) / S.δ ^ 2) := by
    intro ω
    have htel := adagrad_qtb_telescope (δ := S.δ) hδ (fun s => S.g s ω i ^ 2)
      (fun s => sq_nonneg _) S.T
    have heq : ∑ t ∈ Finset.Icc 1 S.T, adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2
        = S.η ^ 2 * ∑ t ∈ Finset.Icc 1 S.T, S.g t ω i ^ 2
            / (Real.sqrt (∑ s ∈ Finset.Icc 1 t, S.g s ω i ^ 2) + S.δ) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [adagrad_step, div_pow]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left htel (by positivity)
  have hstep1 : (∫ ω, ∑ t ∈ Finset.Icc 1 S.T,
        adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2 ∂S.μ)
      ≤ S.η ^ 2 * ∫ ω, Real.log (1
          + (∑ t ∈ Finset.Icc 1 S.T, S.g t ω i ^ 2) / S.δ ^ 2) ∂S.μ := by
    have := integral_mono_of_nonneg
      (f := fun ω => ∑ t ∈ Finset.Icc 1 S.T, adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2)
      (g := fun ω => S.η ^ 2 * Real.log (1
        + (∑ t ∈ Finset.Icc 1 S.T, S.g t ω i ^ 2) / S.δ ^ 2))
      (Filter.Eventually.of_forall fun ω =>
        Finset.sum_nonneg fun t _ => by positivity)
      (hlogint.const_mul _) (Filter.Eventually.of_forall hpoint)
    rwa [integral_const_mul] at this
  have hjensen := adagrad_qtb_jensen_log S.μ
    (fun ω => (∑ t ∈ Finset.Icc 1 S.T, S.g t ω i ^ 2) / S.δ ^ 2) hfint hf0
  rw [integral_div] at hjensen
  have hEA := adagrad_qtb_sq_integral_bound S i
  have hLi : S.L i ≤ adagrad_linf_norm S.L := by
    have h := Finite.le_ciSup (fun j => |S.L j|) i
    rwa [abs_of_nonneg (S.L_nonneg i)] at h
  have hLinf0 : 0 ≤ adagrad_linf_norm S.L := le_trans (S.L_nonneg i) hLi
  have hL1 : 0 ≤ adagrad_l1_norm S.L := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hnum0 : (0:ℝ) ≤ S.η ^ 2 * adagrad_linf_norm S.L * adagrad_l1_norm S.L
      * (S.T : ℝ) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg S.η) hLinf0) hL1) (by positivity)
  have hσ0 : (0:ℝ) ≤ (S.T : ℝ) * adagrad_linf_norm S.σ ^ 2 := by positivity
  have hg0 : (0:ℝ) ≤ (S.T : ℝ)
      * adagrad_linf_norm (fun j => adagrad_grad_coord S.obj S.init j) ^ 2 := by
    positivity
  have hh0 : 0 ≤ adagrad_h S := by
    rw [adagrad_h]
    exact div_nonneg (by linarith) hδ2.le
  have hnum : (∫ ω, ∑ t ∈ Finset.Icc 1 S.T, S.g t ω i ^ 2 ∂S.μ)
      ≤ 36 * ((S.T : ℝ) * adagrad_linf_norm S.σ ^ 2
        + (S.T : ℝ) * adagrad_linf_norm (fun j => adagrad_grad_coord S.obj S.init j) ^ 2
        + S.η ^ 2 * adagrad_linf_norm S.L * adagrad_l1_norm S.L * (S.T : ℝ) ^ 3) := by
    have hPQR : (0:ℝ) ≤ adagrad_l1_norm S.L * (S.η ^ 2 * (S.T : ℝ) ^ 3) :=
      mul_nonneg hL1 (by positivity)
    have hkey := mul_le_mul_of_nonneg_right hLi hPQR
    nlinarith [hEA, hkey, hσ0, hg0]
  have hratio : (∫ ω, ∑ t ∈ Finset.Icc 1 S.T, S.g t ω i ^ 2 ∂S.μ) / S.δ ^ 2
      ≤ 36 * adagrad_h S := by
    rw [adagrad_h, div_le_iff₀ hδ2, mul_assoc, div_mul_cancel₀ _ (ne_of_gt hδ2)]
    exact hnum
  have hfinal : Real.log (1
        + (∫ ω, ∑ t ∈ Finset.Icc 1 S.T, S.g t ω i ^ 2 ∂S.μ) / S.δ ^ 2)
      ≤ adagrad_log_budget S 37 := by
    rw [adagrad_log_budget]
    refine Real.log_le_log (by positivity) ?_
    nlinarith [hratio, hh0]
  have hη : (0:ℝ) ≤ S.η ^ 2 := sq_nonneg _
  calc (∫ ω, ∑ t ∈ Finset.Icc 1 S.T,
        adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2 ∂S.μ)
      ≤ S.η ^ 2 * ∫ ω, Real.log (1
          + (∑ t ∈ Finset.Icc 1 S.T, S.g t ω i ^ 2) / S.δ ^ 2) ∂S.μ := hstep1
    _ ≤ S.η ^ 2 * Real.log (1
          + (∫ ω, ∑ t ∈ Finset.Icc 1 S.T, S.g t ω i ^ 2 ∂S.μ) / S.δ ^ 2) :=
        mul_le_mul_of_nonneg_left hjensen hη
    _ ≤ S.η ^ 2 * adagrad_log_budget S 37 := mul_le_mul_of_nonneg_left hfinal hη

@[blueprint "lem:adagrad-bound-on-gradient"
  (statement := /-- There exists a real constant $c \ge 1$, uniform over all measurable
    spaces and all AdaGrad settings $S$ as in \cref{def:adagrad-setting}, such that
    $$\mathbb{E}\Bigl[\sum_{t=1}^T \sum_{i=1}^d \frac{\hat\eta_{t,i}}{2}
      \nabla_i F(\mathbf{w}_t)^2\Bigr]
      \le \Delta_F
      + \Bigl(2 \eta \|\bm\sigma\|_1 + \frac{\eta^2 \|\mathbf{L}\|_1}{2}\Bigr)
        \Lambda_c(S)
      = Q_c(S),$$
    with $\hat\eta_{t,i}$ as in \cref{def:adagrad-decorrelated-step}, $\Delta_F$ as in
    \cref{def:adagrad-gap}, $\Lambda_c(S)$ as in \cref{def:adagrad-log-budget},
    $\|\cdot\|_1$ as in \cref{def:adagrad-l1-norm} and $Q_c(S)$ as in
    \cref{def:adagrad-gradient-budget}. -/)
  (proof := /-- Choose the absolute constant $c \ge 1$ supplied by
    \cref{lem:adagrad-quadratic-term-bound}, and then fix a measurable space and an
    AdaGrad setting $S$. Summing the per-step estimate of
    \cref{lem:adagrad-per-step-descent} over $t = 1, \dots, T$ gives
    $$\mathbb{E}\Bigl[\sum_{t=1}^T \sum_{i=1}^d \frac{\hat\eta_{t,i}}{2}
        \nabla_i F(\mathbf{w}_t)^2\Bigr]
      \le \mathbb{E}\bigl[F(\mathbf{w}_1) - F(\mathbf{w}_{T+1})\bigr]
      + \sum_{i=1}^d \Bigl(\frac{L_i}{2} + \frac{2 \sigma_i}{\eta}\Bigr)
        \mathbb{E}\Bigl[\sum_{t=1}^T \eta_{t,i}^2 g_{t,i}^2\Bigr],$$
    The integrability assertions of \cref{lem:adagrad-per-step-term-integrable} justify
    moving the integrals through the finite time and coordinate sums. The first term on
    the right arises because the increments
    $F(\mathbf{w}_t) - F(\mathbf{w}_{t+1})$ telescope and each $F(\mathbf{w}_t)$ is
    integrable by \cref{def:adagrad-setting}; the finite sums over $t$ and $i$ may be
    interchanged.

    Since $\mathbf{w}_1$ is the deterministic point $\mathbf{w}_1$ of
    \cref{def:adagrad-setting}, we have $\mathbb{E}[F(\mathbf{w}_1)] = F(\mathbf{w}_1)$,
    and since $F^* \le F(\mathbf{x})$ for every $\mathbf{x}$ by the lower-boundedness
    assumption of \cref{def:adagrad-setting} and $\mathbb{P}$ is a probability measure,
    $\mathbb{E}[F(\mathbf{w}_{T+1})] \ge F^*$. Hence
    $\mathbb{E}[F(\mathbf{w}_1) - F(\mathbf{w}_{T+1})]
    \le F(\mathbf{w}_1) - F^* = \Delta_F$, the gap of \cref{def:adagrad-gap}.

    For the second term, each coefficient $\frac{L_i}{2} + \frac{2 \sigma_i}{\eta}$ is
    nonnegative because $\eta > 0$, $\sigma_i \ge 0$ and $L_i \ge 0$ in
    \cref{def:adagrad-setting}, so \cref{lem:adagrad-quadratic-term-bound} applied to each
    coordinate $i$, which bounds
    $\mathbb{E}\bigl[\sum_{t=1}^T \eta_{t,i}^2 g_{t,i}^2\bigr]$ by
    $\eta^2 \Lambda_c(S)$, bounds it by
    $$\sum_{i=1}^d \Bigl(\frac{L_i}{2} + \frac{2 \sigma_i}{\eta}\Bigr) \eta^2 \Lambda_c(S)
      = \sum_{i=1}^d \Bigl(2 \eta \sigma_i + \frac{L_i \eta^2}{2}\Bigr) \Lambda_c(S)
      = \Bigl(2 \eta \|\bm\sigma\|_1 + \frac{\eta^2 \|\mathbf{L}\|_1}{2}\Bigr)
        \Lambda_c(S),$$
    where the first equality uses $\eta > 0$ to compute
    $\frac{L_i}{2} \eta^2 = \frac{L_i \eta^2}{2}$ and
    $\frac{2 \sigma_i}{\eta} \eta^2 = 2 \eta \sigma_i$, so that the factor $\eta^2$ is
    accounted for exactly once, and the second equality uses $\sigma_i \ge 0$ and
    $L_i \ge 0$, so that
    $\sum_{i=1}^d \sigma_i = \|\bm\sigma\|_1$ and $\sum_{i=1}^d L_i = \|\mathbf{L}\|_1$
    for the norm of \cref{def:adagrad-l1-norm}. Adding the two bounds gives exactly
    $Q_c(S)$ of \cref{def:adagrad-gradient-budget}. -/)
  (title := /-- Bound on the weighted squared gradients -/)
  (latexEnv := "lemma")]
lemma adagrad_bound_on_gradient :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : adagrad_setting Ω),
      ∫ ω, ∑ t ∈ Finset.Icc 1 S.T, ∑ i, adagrad_decorrelated_step S ω t i / 2
            * adagrad_grad_coord S.obj (S.w t ω) i ^ 2 ∂S.μ
        ≤ adagrad_gradient_budget S c := by
  obtain ⟨c, hc, hquad⟩ := adagrad_quadratic_term_bound
  refine ⟨c, hc, ?_⟩
  intro Ω _ S
  classical
  haveI := S.isProbabilityMeasure
  have hweighted (t : ℕ) (ht : t ∈ Finset.Icc 1 S.T) : Integrable
      (fun ω => ∑ i, adagrad_decorrelated_step S ω t i / 2
        * adagrad_grad_coord S.obj (S.w t ω) i ^ 2) S.μ :=
    integrable_finset_sum _ fun i _ =>
      (adagrad_per_step_term_integrable S t (Finset.mem_Icc.mp ht).1 i).1
  have hquadint (t : ℕ) (ht : t ∈ Finset.Icc 1 S.T) (i : Fin S.d) : Integrable
      (fun ω => adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2) S.μ :=
    (adagrad_per_step_term_integrable S t (Finset.mem_Icc.mp ht).1 i).2.2
  have hsum :
      (∑ t ∈ Finset.Icc 1 S.T, ∫ ω, ∑ i, adagrad_decorrelated_step S ω t i / 2
        * adagrad_grad_coord S.obj (S.w t ω) i ^ 2 ∂S.μ)
        ≤ ∑ t ∈ Finset.Icc 1 S.T,
          ((∫ ω, S.obj (S.w t ω) - S.obj (S.w (t + 1) ω) ∂S.μ)
            + ∑ i, (S.L i / 2 + 2 * S.σ i / S.η)
              * ∫ ω, adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2 ∂S.μ) := by
    exact Finset.sum_le_sum fun t ht =>
      adagrad_per_step_descent S t (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp ht).2
  have hsum' :
      (∑ t ∈ Finset.Icc 1 S.T, ∫ ω, ∑ i, adagrad_decorrelated_step S ω t i / 2
        * adagrad_grad_coord S.obj (S.w t ω) i ^ 2 ∂S.μ)
        ≤ (∑ t ∈ Finset.Icc 1 S.T,
            ∫ ω, S.obj (S.w t ω) - S.obj (S.w (t + 1) ω) ∂S.μ)
          + ∑ i, (S.L i / 2 + 2 * S.σ i / S.η)
            * ∫ ω, ∑ t ∈ Finset.Icc 1 S.T,
              adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2 ∂S.μ := by
    calc
      _ ≤ ∑ t ∈ Finset.Icc 1 S.T,
          ((∫ ω, S.obj (S.w t ω) - S.obj (S.w (t + 1) ω) ∂S.μ)
            + ∑ i, (S.L i / 2 + 2 * S.σ i / S.η)
              * ∫ ω, adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2 ∂S.μ) := hsum
      _ = (∑ t ∈ Finset.Icc 1 S.T,
            ∫ ω, S.obj (S.w t ω) - S.obj (S.w (t + 1) ω) ∂S.μ)
          + ∑ i, (S.L i / 2 + 2 * S.σ i / S.η)
            * ∫ ω, ∑ t ∈ Finset.Icc 1 S.T,
              adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2 ∂S.μ := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        apply congrArg₂ (· + ·) rfl
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_finset_sum _ (fun t ht => hquadint t ht i), Finset.mul_sum]
  have htelescope :
      (∑ t ∈ Finset.Icc 1 S.T,
        ∫ ω, S.obj (S.w t ω) - S.obj (S.w (t + 1) ω) ∂S.μ)
        = S.obj S.init - ∫ ω, S.obj (S.w (S.T + 1) ω) ∂S.μ := by
    calc
      _ = ∑ t ∈ Finset.Icc 1 S.T,
          ((∫ ω, S.obj (S.w t ω) ∂S.μ)
            - ∫ ω, S.obj (S.w (t + 1) ω) ∂S.μ) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [integral_sub (S.obj_integrable t) (S.obj_integrable (t + 1))]
      _ = (∫ ω, S.obj (S.w 1 ω) ∂S.μ)
          - ∫ ω, S.obj (S.w (S.T + 1) ω) ∂S.μ := by
        simpa only [neg_sub_neg] using
          (Finset.sum_Icc_sub S.one_le_T
            (fun t => -(∫ ω, S.obj (S.w t ω) ∂S.μ)))
      _ = S.obj S.init - ∫ ω, S.obj (S.w (S.T + 1) ω) ∂S.μ := by
        congr 1
        simp [S.w_one]
  have hfinal : S.objMin ≤ ∫ ω, S.obj (S.w (S.T + 1) ω) ∂S.μ := by
    calc
      S.objMin = ∫ _ : Ω, S.objMin ∂S.μ := by simp
      _ ≤ ∫ ω, S.obj (S.w (S.T + 1) ω) ∂S.μ :=
        integral_mono_ae (integrable_const S.objMin) (S.obj_integrable (S.T + 1))
          (Filter.Eventually.of_forall fun ω => S.obj_lower_bounded (S.w (S.T + 1) ω))
  have hobj :
      (∑ t ∈ Finset.Icc 1 S.T,
        ∫ ω, S.obj (S.w t ω) - S.obj (S.w (t + 1) ω) ∂S.μ)
        ≤ adagrad_gap S := by
    rw [htelescope]
    unfold adagrad_gap
    linarith
  have hcoeff (i : Fin S.d) : 0 ≤ S.L i / 2 + 2 * S.σ i / S.η := by
    exact add_nonneg (div_nonneg (S.L_nonneg i) (by norm_num))
      (div_nonneg (mul_nonneg (by norm_num) (S.sigma_nonneg i)) S.eta_pos.le)
  have hqsum :
      (∑ i, (S.L i / 2 + 2 * S.σ i / S.η)
        * ∫ ω, ∑ t ∈ Finset.Icc 1 S.T,
          adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2 ∂S.μ)
        ≤ ∑ i, (S.L i / 2 + 2 * S.σ i / S.η)
          * (S.η ^ 2 * adagrad_log_budget S c) := by
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hquad Ω S i) (hcoeff i)
  have hsigma : (∑ i, S.σ i) = adagrad_l1_norm S.σ := by
    unfold adagrad_l1_norm
    apply Finset.sum_congr rfl
    intro i _
    rw [abs_of_nonneg (S.sigma_nonneg i)]
  have hL : (∑ i, S.L i) = adagrad_l1_norm S.L := by
    unfold adagrad_l1_norm
    apply Finset.sum_congr rfl
    intro i _
    rw [abs_of_nonneg (S.L_nonneg i)]
  have hη : S.η ≠ 0 := ne_of_gt S.eta_pos
  have hcoeffsum :
      (∑ i, (S.L i / 2 + 2 * S.σ i / S.η) * S.η ^ 2)
        = 2 * S.η * adagrad_l1_norm S.σ
          + S.η ^ 2 * adagrad_l1_norm S.L / 2 := by
    calc
      _ = ∑ i, (2 * S.η * S.σ i + S.η ^ 2 * S.L i / 2) := by
        apply Finset.sum_congr rfl
        intro i _
        field_simp [hη]
        <;> ring
      _ = 2 * S.η * (∑ i, S.σ i) + S.η ^ 2 * (∑ i, S.L i) / 2 := by
        rw [Finset.sum_add_distrib]
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
      _ = 2 * S.η * adagrad_l1_norm S.σ
          + S.η ^ 2 * adagrad_l1_norm S.L / 2 := by rw [hsigma, hL]
  have hbudget :
      adagrad_gap S
          + ∑ i, (S.L i / 2 + 2 * S.σ i / S.η)
            * (S.η ^ 2 * adagrad_log_budget S c)
        = adagrad_gradient_budget S c := by
    unfold adagrad_gradient_budget
    rw [show (∑ i, (S.L i / 2 + 2 * S.σ i / S.η)
        * (S.η ^ 2 * adagrad_log_budget S c))
        = (∑ i, (S.L i / 2 + 2 * S.σ i / S.η) * S.η ^ 2)
          * adagrad_log_budget S c by
      calc
        _ = ∑ i, ((S.L i / 2 + 2 * S.σ i / S.η) * S.η ^ 2)
            * adagrad_log_budget S c := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [Finset.sum_mul], hcoeffsum]
  calc
    (∫ ω, ∑ t ∈ Finset.Icc 1 S.T, ∑ i, adagrad_decorrelated_step S ω t i / 2
        * adagrad_grad_coord S.obj (S.w t ω) i ^ 2 ∂S.μ)
        = ∑ t ∈ Finset.Icc 1 S.T, ∫ ω, ∑ i,
          adagrad_decorrelated_step S ω t i / 2
            * adagrad_grad_coord S.obj (S.w t ω) i ^ 2 ∂S.μ := by
      rw [integral_finset_sum _ hweighted]
    _ ≤ (∑ t ∈ Finset.Icc 1 S.T,
          ∫ ω, S.obj (S.w t ω) - S.obj (S.w (t + 1) ω) ∂S.μ)
        + ∑ i, (S.L i / 2 + 2 * S.σ i / S.η)
          * ∫ ω, ∑ t ∈ Finset.Icc 1 S.T,
            adagrad_step S ω t i ^ 2 * S.g t ω i ^ 2 ∂S.μ := hsum'
    _ ≤ adagrad_gap S
        + ∑ i, (S.L i / 2 + 2 * S.σ i / S.η)
          * (S.η ^ 2 * adagrad_log_budget S c) := add_le_add hobj hqsum
    _ = adagrad_gradient_budget S c := hbudget

@[blueprint "lem:adagrad-etahat-sqrt-jensen"
  (statement := /-- Let $(\Omega, \mathcal{A}, \mu)$ be a probability space and let
    $f : \Omega \to \mathbb{R}$ be $\mu$-integrable and nonnegative $\mu$-almost
    everywhere. Then
    $$\int_\Omega \sqrt{f(\omega)}\, d\mu(\omega)
      \le \sqrt{\int_\Omega f(\omega)\, d\mu(\omega)}.$$ -/)
  (proof := /-- Write $c = \int_\Omega f \, d\mu$; since $f \ge 0$ almost everywhere,
    $c \ge 0$.

    Suppose first that $c = 0$. A nonnegative almost everywhere integrable function with
    vanishing integral vanishes almost everywhere, so $f = 0$ almost everywhere, hence
    $\sqrt{f} = 0$ almost everywhere and $\int_\Omega \sqrt{f}\, d\mu = 0 = \sqrt{0}
    = \sqrt{c}$.

    Suppose now that $c > 0$, so that $\sqrt{c} > 0$. For every $\omega$ with
    $f(\omega) \ge 0$ the inequality $\bigl(\sqrt{f(\omega)} - \sqrt{c}\bigr)^2 \ge 0$
    expands, using $\sqrt{f(\omega)}^2 = f(\omega)$ and $\sqrt{c}^2 = c$, to
    $2 \sqrt{c}\, \sqrt{f(\omega)} \le f(\omega) + c$, that is,
    $$\sqrt{f(\omega)} \le \frac{f(\omega) + c}{2 \sqrt{c}} .$$
    This holds almost everywhere. The right-hand side is integrable, being a constant
    multiple of the sum of the integrable function $f$ and a constant, and the left-hand
    side is nonnegative, so integrating the inequality gives
    $$\int_\Omega \sqrt{f}\, d\mu
      \le \frac{1}{2\sqrt{c}} \Bigl(\int_\Omega f \, d\mu + c\Bigr)
      = \frac{c + c}{2 \sqrt{c}} = \frac{c}{\sqrt{c}} = \sqrt{c},$$
    where the last equality uses $c = \sqrt{c}\,\sqrt{c}$ and $\sqrt{c} > 0$, and the
    integral of the constant $c$ equals $c$ because $\mu$ is a probability measure. -/)
  (title := /-- Jensen's inequality for the square root -/)
  (latexEnv := "lemma")]
lemma adagrad_etahat_sqrt_jensen {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Integrable f μ) (hf0 : 0 ≤ᵐ[μ] f) :
    (∫ ω, Real.sqrt (f ω) ∂μ) ≤ Real.sqrt (∫ ω, f ω ∂μ) := by
  have hc0 : 0 ≤ ∫ ω, f ω ∂μ := integral_nonneg_of_ae hf0
  rcases hc0.eq_or_lt with hc | hc
  · have hfz : f =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg_ae hf0 hf).1 hc.symm
    have hsq : (fun ω => Real.sqrt (f ω)) =ᵐ[μ] fun _ => (0 : ℝ) := by
      filter_upwards [hfz] with ω hω
      simp [hω]
    rw [integral_congr_ae hsq, ← hc]
    simp
  · set c := ∫ ω, f ω ∂μ with hcdef
    have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
    have key : (fun ω => Real.sqrt (f ω)) ≤ᵐ[μ] fun ω => (f ω + c) / (2 * Real.sqrt c) := by
      filter_upwards [hf0] with ω hω
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (Real.sqrt (f ω) - Real.sqrt c), Real.sq_sqrt hω,
        Real.sq_sqrt hc.le, Real.sqrt_nonneg (f ω)]
    calc (∫ ω, Real.sqrt (f ω) ∂μ)
        ≤ ∫ ω, (f ω + c) / (2 * Real.sqrt c) ∂μ := by
          refine integral_mono_of_nonneg ?_ ?_ key
          · filter_upwards with ω using Real.sqrt_nonneg _
          · exact (hf.add (integrable_const c)).div_const _
      _ = (c + c) / (2 * Real.sqrt c) := by
          rw [integral_div, integral_add hf (integrable_const c), integral_const]
          simp [← hcdef]
      _ = Real.sqrt c := by
          rw [div_eq_iff (by positivity)]
          nlinarith [Real.sq_sqrt hc.le]

@[blueprint "lem:adagrad-etahat-noise-second-moment"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting}, let
    $i \in [d]$ and let $t \ge 1$. Then
    $$\mathbb{E}\bigl[(g_{t,i} - \nabla_i F(\mathbf{w}_t))^2\bigr] \le \sigma_i^2,$$
    where $\nabla_i F$ is as in \cref{def:adagrad-grad-coord}. -/)
  (proof := /-- Write $X(\omega) = (g_{t,i}(\omega) - \nabla_i F(\mathbf{w}_t(\omega)))^2$
    and let $\mathcal{F}_{t-1}$ be the corresponding $\sigma$-algebra of the filtration of
    \cref{def:adagrad-setting}, which is contained in the ambient $\sigma$-algebra.

    By the tower property in the form
    $\mathbb{E}\bigl[\mathbb{E}[X \mid \mathcal{F}_{t-1}]\bigr] = \mathbb{E}[X]$, which
    holds for every $X$ because both sides vanish when $X$ fails to be integrable, we may
    replace $\mathbb{E}[X]$ by $\mathbb{E}\bigl[\mathbb{E}[X \mid
    \mathcal{F}_{t-1}]\bigr]$.

    By the coordinate-wise bounded-variance assumption of \cref{def:adagrad-setting},
    $\mathbb{E}[X \mid \mathcal{F}_{t-1}] \le \sigma_i^2$ almost surely. Conditional
    expectations are always integrable and the constant $\sigma_i^2$ is integrable because
    $\mu$ is a probability measure, so this almost sure inequality may be integrated,
    giving
    $\mathbb{E}\bigl[\mathbb{E}[X \mid \mathcal{F}_{t-1}]\bigr]
      \le \mathbb{E}[\sigma_i^2] = \sigma_i^2$,
    the last equality again because $\mu$ is a probability measure. Combining the two
    displays yields $\mathbb{E}[X] \le \sigma_i^2$. -/)
  (title := /-- Second moment of the gradient noise -/)
  (latexEnv := "lemma")]
lemma adagrad_etahat_noise_second_moment {Ω : Type} [MeasurableSpace Ω]
    (S : adagrad_setting Ω) (i : Fin S.d) (t : ℕ) (ht : 1 ≤ t) :
    (∫ ω, (S.g t ω i - adagrad_grad_coord S.obj (S.w t ω) i) ^ 2 ∂S.μ) ≤ S.σ i ^ 2 := by
  haveI := S.isProbabilityMeasure
  calc (∫ ω, (S.g t ω i - adagrad_grad_coord S.obj (S.w t ω) i) ^ 2 ∂S.μ)
      = ∫ ω, (S.μ[fun ω => (S.g t ω i - adagrad_grad_coord S.obj (S.w t ω) i) ^ 2|
          S.ℱ (t - 1)]) ω ∂S.μ := (integral_condExp (S.ℱ.le (t - 1))).symm
    _ ≤ ∫ _ : Ω, S.σ i ^ 2 ∂S.μ := by
        refine integral_mono_ae integrable_condExp (integrable_const _) ?_
        exact S.g_bounded_variance t ht i
    _ = S.σ i ^ 2 := by simp

@[blueprint "lem:adagrad-etahat-integrable-sqrt"
  (statement := /-- Let $(\Omega, \mathcal{A}, \mu)$ be a probability space and let
    $f : \Omega \to \mathbb{R}$ be $\mu$-integrable and nonnegative $\mu$-almost
    everywhere. Then $\sqrt{f}$ is $\mu$-integrable. -/)
  (proof := /-- The function $\sqrt{f}$ is almost everywhere strongly measurable, being
    the composition of the continuous function $\sqrt{\cdot}$ with the almost everywhere
    strongly measurable function $f$.

    For every $x \ge 0$ one has $(\sqrt{x} - 1)^2 \ge 0$, which together with
    $\sqrt{x}^2 = x$ gives $2\sqrt{x} \le x + 1$, that is,
    $\sqrt{x} \le \frac{x+1}{2}$. Applying this to $x = f(\omega)$ at every $\omega$ where
    $f(\omega) \ge 0$, and using $|\sqrt{f(\omega)}| = \sqrt{f(\omega)}$ because square
    roots are nonnegative, we obtain
    $\bigl|\sqrt{f(\omega)}\bigr| \le \frac{f(\omega)+1}{2}$ almost everywhere.

    The dominating function $\frac{f+1}{2}$ is integrable, being a constant multiple of the
    sum of the integrable function $f$ and the constant $1$, which is integrable because
    $\mu$ is a probability measure. Hence $\sqrt{f}$ is integrable by domination. -/)
  (title := /-- Integrability of the square root -/)
  (latexEnv := "lemma")]
lemma adagrad_etahat_integrable_sqrt {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Integrable f μ) (hf0 : 0 ≤ᵐ[μ] f) :
    Integrable (fun ω => Real.sqrt (f ω)) μ := by
  refine Integrable.mono' (g := fun ω => (f ω + 1) / 2)
    ((hf.add (integrable_const 1)).div_const 2)
    (Real.continuous_sqrt.comp_aestronglyMeasurable hf.1) ?_
  filter_upwards [hf0] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), le_div_iff₀ (by norm_num)]
  nlinarith [sq_nonneg (Real.sqrt (f ω) - 1), Real.sq_sqrt hω]

@[blueprint "lem:adagrad-etahat-memlp-g"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting}, let
    $i \in [d]$ and let $t \in \mathbb{N}$. Then the random variable
    $\omega \mapsto g_{t,i}(\omega)$ belongs to $L^2(\mu)$. -/)
  (proof := /-- The map $\omega \mapsto \mathbf{g}_t(\omega)$ is
    $\mathcal{F}_t$-measurable by \cref{def:adagrad-setting}, and $\mathcal{F}_t$ is
    contained in the ambient $\sigma$-algebra because $(\mathcal{F}_t)_t$ is a filtration
    of sub-$\sigma$-algebras; composing with the evaluation at the coordinate $i$, which
    is measurable, shows that $g_{t,i}$ is measurable, hence almost everywhere strongly
    measurable.

    By \cref{def:adagrad-setting} the function $g_{t,i}^2$ is $\mu$-integrable. For an
    almost everywhere strongly measurable real-valued function, membership in $L^2(\mu)$
    is equivalent to the integrability of its square, so $g_{t,i} \in L^2(\mu)$. -/)
  (title := /-- Square-integrability of the stochastic gradient coordinates -/)
  (latexEnv := "lemma")]
lemma adagrad_etahat_memlp_g {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (i : Fin S.d) (t : ℕ) : MemLp (fun ω => S.g t ω i) 2 S.μ := by
  have hgm : Measurable (fun ω => S.g t ω i) :=
    (measurable_pi_apply i).comp ((S.g_adapted t).mono (S.ℱ.le t) le_rfl)
  exact (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).2 (S.g_sq_integrable t i)

@[blueprint "lem:adagrad-etahat-memlp-grad"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting}, let
    $i \in [d]$ and let $t \ge 1$. Then the random variable
    $\omega \mapsto \nabla_i F(\mathbf{w}_t(\omega))$ belongs to $L^2(\mu)$, where
    $\nabla_i F$ is as in \cref{def:adagrad-grad-coord}. -/)
  (proof := /-- By \cref{lem:adagrad-etahat-memlp-g} the random variable $g_{t,i}$ belongs
    to $L^2(\mu)$.

    Since conditional expectation is a contraction on $L^p$ for $p \ge 1$, the conditional
    expectation $\mathbb{E}[g_{t,i} \mid \mathcal{F}_{t-1}]$ also belongs to $L^2(\mu)$.
    By the unbiasedness assumption of \cref{def:adagrad-setting} and $t \ge 1$, this
    conditional expectation agrees $\mu$-almost everywhere with
    $\nabla_i F(\mathbf{w}_t)$. Membership in $L^2$ is invariant under almost everywhere
    equality, so $\nabla_i F(\mathbf{w}_t) \in L^2(\mu)$. -/)
  (title := /-- Square-integrability of the gradient coordinates -/)
  (latexEnv := "lemma")]
lemma adagrad_etahat_memlp_grad {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (i : Fin S.d) (t : ℕ) (ht : 1 ≤ t) :
    MemLp (fun ω => adagrad_grad_coord S.obj (S.w t ω) i) 2 S.μ := by
  haveI := S.isProbabilityMeasure
  exact (MemLp.condExp (m := S.ℱ (t - 1)) one_le_two
    (adagrad_etahat_memlp_g S i t)).ae_eq (S.g_unbiased t ht i)

@[blueprint "lem:adagrad-etahat-sqrt-add-le"
  (statement := /-- For all real numbers $a, b \ge 0$ one has
    $\sqrt{a + b} \le \sqrt{a} + \sqrt{b}$. -/)
  (proof := /-- Both $\sqrt{a}$ and $\sqrt{b}$ are nonnegative, hence so is their product,
    and therefore
    $$\bigl(\sqrt{a} + \sqrt{b}\bigr)^2 = a + 2 \sqrt{a}\sqrt{b} + b \ge a + b,$$
    where we used $\sqrt{a}^2 = a$ and $\sqrt{b}^2 = b$, valid because $a, b \ge 0$.
    Since also $\sqrt{a+b}^2 = a + b$, valid because $a + b \ge 0$, we conclude
    $\sqrt{a+b}^2 \le \bigl(\sqrt{a}+\sqrt{b}\bigr)^2$. Both $\sqrt{a+b}$ and
    $\sqrt{a}+\sqrt{b}$ are nonnegative, and on nonnegative reals squaring is monotone
    with monotone inverse, so $\sqrt{a+b} \le \sqrt{a} + \sqrt{b}$. -/)
  (title := /-- Subadditivity of the square root -/)
  (latexEnv := "lemma")]
lemma adagrad_etahat_sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have h2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  have h3 : Real.sqrt (a + b) ^ 2 = a + b := Real.sq_sqrt (add_nonneg ha hb)
  have h4 : 0 ≤ Real.sqrt a * Real.sqrt b :=
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  nlinarith [Real.sqrt_nonneg (a + b), Real.sqrt_nonneg a, Real.sqrt_nonneg b]

@[blueprint "lem:adagrad-upper-bound-etahat"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting} and let
    $i \in [d]$. Then
    $$\mathbb{E}\Bigl[\frac{1}{\tilde\eta_{T,i}}\Bigr]
      \le \frac{\sigma_i \sqrt{2T} + \delta}{\eta}
      + \frac{\sqrt{3}}{\eta}
        \mathbb{E}\Bigl[\sqrt{\sum_{t=1}^T \nabla_i F(\mathbf{w}_t)^2}\Bigr],$$
    where $\tilde\eta_{T,i}$ is the auxiliary step size of
    \cref{def:adagrad-aux-step} and $\nabla_i F$ is as in
    \cref{def:adagrad-grad-coord}. -/)
  (proof := /-- Throughout, abbreviate $G_t(\omega) = \nabla_i F(\mathbf{w}_t(\omega))$ and
    $N_t(\omega) = g_{t,i}(\omega) - G_t(\omega)$, write
    $A(\omega) = 2 \sum_{t=1}^{T-1} N_t(\omega)^2 + \sigma_i^2$ and
    $P(\omega) = \sum_{t=1}^{T} G_t(\omega)^2$, and recall that the measure of $S$ is a
    probability measure.

    \emph{Step 1: integrability.} For every $t \ge 1$ the random variable $g_{t,i}$ lies in
    $L^2$ by \cref{lem:adagrad-etahat-memlp-g} and $G_t$ lies in $L^2$ by
    \cref{lem:adagrad-etahat-memlp-grad}; hence $N_t = g_{t,i} - G_t$ lies in $L^2$, so
    $N_t^2$ and $G_t^2$ are integrable. Consequently $P$ is integrable, being a finite sum
    of the integrable functions $G_t^2$ over $t \in \{1, \dots, T\}$, and $A$ is
    integrable, being a constant multiple of a finite sum of the integrable functions
    $N_t^2$ over $t \in \{1, \dots, T-1\}$ plus the constant $\sigma_i^2$, which is
    integrable because the measure is a probability measure.

    \emph{Step 2: a pointwise bound on $1/\tilde\eta_{T,i}$.} Fix $\omega$. For every
    $s$ one has $g_{s,i} = N_s + G_s$ and therefore, since
    $(N_s - G_s)^2 \ge 0$,
    $$g_{s,i}^2 = (N_s + G_s)^2 \le 2 N_s^2 + 2 G_s^2 .$$
    Summing over $s \in \{1, \dots, T-1\}$ gives
    $\sum_{s=1}^{T-1} g_{s,i}^2 \le 2\sum_{s=1}^{T-1} N_s^2 + 2\sum_{s=1}^{T-1} G_s^2$.
    Because $T - 1 \le T$ we have
    $\{1, \dots, T-1\} \subseteq \{1, \dots, T\}$ and each $G_t^2 \ge 0$, so
    $\sum_{s=1}^{T-1} G_s^2 \le P$. Adding $\sigma_i^2 + P$ to both sides yields
    $$\sum_{s=1}^{T-1} g_{s,i}^2 + \sigma_i^2 + P \le A + 3 P .$$
    Since $\sqrt{\cdot}$ is monotone, and since $A \ge 0$ and $3P \ge 0$ because squares
    and $\sigma_i^2$ are nonnegative, \cref{lem:adagrad-etahat-sqrt-add-le} applied to
    $A$ and $3P$ gives
    $$\sqrt{\sum_{s=1}^{T-1} g_{s,i}^2 + \sigma_i^2 + P}
      \le \sqrt{A + 3P} \le \sqrt{A} + \sqrt{3P} = \sqrt{A} + \sqrt{3}\sqrt{P},$$
    the last equality because $3 \ge 0$. By the definition of $\tilde\eta_{T,i}$ in
    \cref{def:adagrad-aux-step} we have
    $\frac{1}{\tilde\eta_{T,i}}
    = \frac{\sqrt{\sum_{s=1}^{T-1} g_{s,i}^2 + \sigma_i^2 + P} + \delta}{\eta}$, so
    dividing the previous display by $\eta > 0$ gives the pointwise bound
    $$\frac{1}{\tilde\eta_{T,i}}
      \le \frac{\sqrt{A} + \sqrt{3}\sqrt{P} + \delta}{\eta} .$$

    \emph{Step 3: the expectation of $A$.} By \cref{lem:adagrad-etahat-noise-second-moment}
    each $\mathbb{E}[N_t^2] \le \sigma_i^2$ for $t \ge 1$. Summing this over the
    $T-1$ indices $t \in \{1, \dots, T-1\}$ and using the integrability from Step 1 to
    exchange the finite sum with the integral gives
    $\mathbb{E}\bigl[\sum_{t=1}^{T-1} N_t^2\bigr] \le (T-1)\sigma_i^2$. Hence, using that
    the expectation of the constant $\sigma_i^2$ is $\sigma_i^2$ and that
    $2(T-1) + 1 \le 2T$ together with $\sigma_i^2 \ge 0$,
    $$\mathbb{E}[A] \le 2 (T-1) \sigma_i^2 + \sigma_i^2 \le 2 T \sigma_i^2 .$$

    \emph{Step 4: Jensen for $\sqrt{A}$.} The function $A$ is integrable by Step 1 and
    nonnegative, so \cref{lem:adagrad-etahat-sqrt-jensen} gives
    $\mathbb{E}[\sqrt{A}] \le \sqrt{\mathbb{E}[A]}$. Combining with Step 3 and the
    monotonicity of $\sqrt{\cdot}$,
    $$\mathbb{E}[\sqrt{A}] \le \sqrt{2 T \sigma_i^2} = \sigma_i \sqrt{2T},$$
    where the identity uses $\sqrt{2T\sigma_i^2} = \sqrt{2T}\sqrt{\sigma_i^2}$, valid since
    $2T \ge 0$, together with $\sqrt{\sigma_i^2} = \sigma_i$, valid since
    $\sigma_i \ge 0$ by \cref{def:adagrad-setting}.

    \emph{Step 5: integration and conclusion.} By
    \cref{lem:adagrad-etahat-integrable-sqrt} applied to $A$ and to $P$, both $\sqrt{A}$
    and $\sqrt{P}$ are integrable, so the dominating function
    $\frac{\sqrt{A} + \sqrt{3}\sqrt{P} + \delta}{\eta}$ of Step 2 is integrable. The
    integrand $\frac{1}{\tilde\eta_{T,i}}$ is nonnegative, since it equals
    $\frac{\sqrt{\cdots} + \delta}{\eta}$ with $\delta > 0$ and $\eta > 0$ by
    \cref{def:adagrad-setting}. Integrating the pointwise bound of Step 2 therefore gives
    $$\mathbb{E}\Bigl[\frac{1}{\tilde\eta_{T,i}}\Bigr]
      \le \frac{\mathbb{E}[\sqrt{A}] + \sqrt{3}\, \mathbb{E}[\sqrt{P}] + \delta}{\eta},$$
    where we used linearity of the integral and that the expectation of the constant
    $\delta$ is $\delta$. Substituting the bound of Step 4 for $\mathbb{E}[\sqrt{A}]$ and
    dividing by $\eta > 0$ yields
    $$\mathbb{E}\Bigl[\frac{1}{\tilde\eta_{T,i}}\Bigr]
      \le \frac{\sigma_i \sqrt{2T} + \delta}{\eta}
        + \frac{\sqrt{3}}{\eta} \mathbb{E}\bigl[\sqrt{P}\bigr],$$
    which is the assertion. -/)
  (title := /-- Bound on the reciprocal auxiliary step size -/)
  (latexEnv := "lemma")]
lemma adagrad_upper_bound_etahat {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (i : Fin S.d) :
    (∫ ω, 1 / adagrad_aux_step S ω i ∂S.μ)
      ≤ (S.σ i * Real.sqrt (2 * S.T) + S.δ) / S.η
        + Real.sqrt 3 / S.η
          * ∫ ω, Real.sqrt (∑ t ∈ Finset.Icc 1 S.T,
              adagrad_grad_coord S.obj (S.w t ω) i ^ 2) ∂S.μ := by
  haveI := S.isProbabilityMeasure
  set G : ℕ → Ω → ℝ := fun t ω => adagrad_grad_coord S.obj (S.w t ω) i with hGdef
  set N : ℕ → Ω → ℝ := fun t ω => S.g t ω i - G t ω with hNdef
  have hNint : ∀ t : ℕ, 1 ≤ t → Integrable (fun ω => N t ω ^ 2) S.μ := by
    intro t ht
    exact ((adagrad_etahat_memlp_g S i t).sub (adagrad_etahat_memlp_grad S i t ht)).integrable_sq
  have hGint : ∀ t : ℕ, 1 ≤ t → Integrable (fun ω => G t ω ^ 2) S.μ := fun t ht =>
    (adagrad_etahat_memlp_grad S i t ht).integrable_sq
  have hPint : Integrable (fun ω => ∑ t ∈ Finset.Icc 1 S.T, G t ω ^ 2) S.μ := by
    refine integrable_finset_sum _ ?_
    intro t ht
    exact hGint t (Finset.mem_Icc.1 ht).1
  have hAint : Integrable
      (fun ω => 2 * ∑ t ∈ Finset.Icc 1 (S.T - 1), N t ω ^ 2 + S.σ i ^ 2) S.μ := by
    refine Integrable.add (Integrable.const_mul (integrable_finset_sum _ ?_) 2)
      (integrable_const _)
    intro t ht
    exact hNint t (Finset.mem_Icc.1 ht).1
  have hsum_le : ∀ ω, (∑ s ∈ Finset.Icc 1 (S.T - 1), S.g s ω i ^ 2) + S.σ i ^ 2
      + ∑ t ∈ Finset.Icc 1 S.T, G t ω ^ 2
      ≤ (2 * ∑ t ∈ Finset.Icc 1 (S.T - 1), N t ω ^ 2 + S.σ i ^ 2)
        + 3 * ∑ t ∈ Finset.Icc 1 S.T, G t ω ^ 2 := by
    intro ω
    have hIcc : Finset.Icc 1 (S.T - 1) ⊆ Finset.Icc 1 S.T := by
      apply Finset.Icc_subset_Icc_right
      omega
    have hstep : ∑ s ∈ Finset.Icc 1 (S.T - 1), S.g s ω i ^ 2
        ≤ ∑ s ∈ Finset.Icc 1 (S.T - 1), (2 * N s ω ^ 2 + 2 * G s ω ^ 2) := by
      refine Finset.sum_le_sum ?_
      intro s _
      have : S.g s ω i = N s ω + G s ω := by simp [hNdef]
      rw [this]
      nlinarith [sq_nonneg (N s ω - G s ω)]
    have hGmono : ∑ s ∈ Finset.Icc 1 (S.T - 1), G s ω ^ 2
        ≤ ∑ t ∈ Finset.Icc 1 S.T, G t ω ^ 2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hIcc ?_
      intro t _ _
      positivity
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hstep
    linarith
  have hAnn : ∀ ω, 0 ≤ 2 * ∑ t ∈ Finset.Icc 1 (S.T - 1), N t ω ^ 2 + S.σ i ^ 2 := by
    intro ω
    have : 0 ≤ ∑ t ∈ Finset.Icc 1 (S.T - 1), N t ω ^ 2 :=
      Finset.sum_nonneg fun t _ => sq_nonneg _
    positivity
  have hPnn : ∀ ω, 0 ≤ ∑ t ∈ Finset.Icc 1 S.T, G t ω ^ 2 := fun ω =>
    Finset.sum_nonneg fun t _ => sq_nonneg _
  have hpt : ∀ ω, 1 / adagrad_aux_step S ω i
      ≤ (Real.sqrt (2 * ∑ t ∈ Finset.Icc 1 (S.T - 1), N t ω ^ 2 + S.σ i ^ 2)
          + Real.sqrt 3 * Real.sqrt (∑ t ∈ Finset.Icc 1 S.T, G t ω ^ 2) + S.δ) / S.η := by
    intro ω
    have hstep : 1 / adagrad_aux_step S ω i
        = (Real.sqrt ((∑ s ∈ Finset.Icc 1 (S.T - 1), S.g s ω i ^ 2) + S.σ i ^ 2
            + ∑ t ∈ Finset.Icc 1 S.T, G t ω ^ 2) + S.δ) / S.η := by
      rw [adagrad_aux_step, one_div_div]
    rw [hstep]
    refine div_le_div_of_nonneg_right ?_ S.eta_pos.le
    have h1 : Real.sqrt ((∑ s ∈ Finset.Icc 1 (S.T - 1), S.g s ω i ^ 2) + S.σ i ^ 2
        + ∑ t ∈ Finset.Icc 1 S.T, G t ω ^ 2)
        ≤ Real.sqrt ((2 * ∑ t ∈ Finset.Icc 1 (S.T - 1), N t ω ^ 2 + S.σ i ^ 2)
          + 3 * ∑ t ∈ Finset.Icc 1 S.T, G t ω ^ 2) :=
      Real.sqrt_le_sqrt (hsum_le ω)
    have h2 : Real.sqrt ((2 * ∑ t ∈ Finset.Icc 1 (S.T - 1), N t ω ^ 2 + S.σ i ^ 2)
          + 3 * ∑ t ∈ Finset.Icc 1 S.T, G t ω ^ 2)
        ≤ Real.sqrt (2 * ∑ t ∈ Finset.Icc 1 (S.T - 1), N t ω ^ 2 + S.σ i ^ 2)
          + Real.sqrt (3 * ∑ t ∈ Finset.Icc 1 S.T, G t ω ^ 2) :=
      adagrad_etahat_sqrt_add_le (hAnn ω) (by positivity)
    have h3 : Real.sqrt (3 * ∑ t ∈ Finset.Icc 1 S.T, G t ω ^ 2)
        = Real.sqrt 3 * Real.sqrt (∑ t ∈ Finset.Icc 1 S.T, G t ω ^ 2) :=
      Real.sqrt_mul (by norm_num) _
    linarith [h3 ▸ h2]
  have hnoise : (∫ ω, 2 * ∑ t ∈ Finset.Icc 1 (S.T - 1), N t ω ^ 2 + S.σ i ^ 2 ∂S.μ)
      ≤ 2 * S.T * S.σ i ^ 2 := by
    have hcard : 2 * ((Finset.Icc 1 (S.T - 1)).card : ℝ) + 1 ≤ 2 * S.T := by
      rw [Nat.card_Icc]
      have hT := S.one_le_T
      have h : 2 * (S.T - 1 + 1 - 1) + 1 ≤ 2 * S.T := by omega
      calc 2 * ((S.T - 1 + 1 - 1 : ℕ) : ℝ) + 1 = ((2 * (S.T - 1 + 1 - 1) + 1 : ℕ) : ℝ) := by
            push_cast
            ring
        _ ≤ ((2 * S.T : ℕ) : ℝ) := by exact_mod_cast h
        _ = 2 * S.T := by push_cast; ring
    have hsum : (∫ ω, ∑ t ∈ Finset.Icc 1 (S.T - 1), N t ω ^ 2 ∂S.μ)
        ≤ (Finset.Icc 1 (S.T - 1)).card * S.σ i ^ 2 := by
      rw [integral_finset_sum _ (fun t ht => hNint t (Finset.mem_Icc.1 ht).1)]
      calc ∑ t ∈ Finset.Icc 1 (S.T - 1), ∫ ω, N t ω ^ 2 ∂S.μ
          ≤ ∑ _t ∈ Finset.Icc 1 (S.T - 1), S.σ i ^ 2 := by
            refine Finset.sum_le_sum ?_
            intro t ht
            exact adagrad_etahat_noise_second_moment S i t (Finset.mem_Icc.1 ht).1
        _ = (Finset.Icc 1 (S.T - 1)).card * S.σ i ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hsig : 0 ≤ S.σ i ^ 2 := sq_nonneg _
    rw [integral_add (Integrable.const_mul (integrable_finset_sum _
      (fun t ht => hNint t (Finset.mem_Icc.1 ht).1)) 2) (integrable_const _),
      integral_const_mul, integral_const]
    rw [measureReal_univ_eq_one]
    rw [one_smul]
    nlinarith [hsum, hcard, hsig]
  have hJ1 : (∫ ω, Real.sqrt (2 * ∑ t ∈ Finset.Icc 1 (S.T - 1), N t ω ^ 2 + S.σ i ^ 2) ∂S.μ)
      ≤ S.σ i * Real.sqrt (2 * S.T) := by
    have hj := adagrad_etahat_sqrt_jensen S.μ _ hAint
      (Filter.Eventually.of_forall hAnn)
    have hmono : Real.sqrt (∫ ω, 2 * ∑ t ∈ Finset.Icc 1 (S.T - 1), N t ω ^ 2 + S.σ i ^ 2 ∂S.μ)
        ≤ Real.sqrt (2 * S.T * S.σ i ^ 2) := Real.sqrt_le_sqrt hnoise
    have hfact : Real.sqrt (2 * S.T * S.σ i ^ 2) = S.σ i * Real.sqrt (2 * S.T) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (S.sigma_nonneg i), mul_comm]
    linarith [hfact ▸ hmono]
  have hIntBound : Integrable
      (fun ω => (Real.sqrt (2 * ∑ t ∈ Finset.Icc 1 (S.T - 1), N t ω ^ 2 + S.σ i ^ 2)
        + Real.sqrt 3 * Real.sqrt (∑ t ∈ Finset.Icc 1 S.T, G t ω ^ 2) + S.δ) / S.η) S.μ := by
    refine Integrable.div_const (Integrable.add (Integrable.add ?_ ?_) (integrable_const _)) _
    · exact adagrad_etahat_integrable_sqrt S.μ _ hAint (Filter.Eventually.of_forall hAnn)
    · exact (adagrad_etahat_integrable_sqrt S.μ _ hPint
        (Filter.Eventually.of_forall hPnn)).const_mul _
  calc (∫ ω, 1 / adagrad_aux_step S ω i ∂S.μ)
      ≤ ∫ ω, (Real.sqrt (2 * ∑ t ∈ Finset.Icc 1 (S.T - 1), N t ω ^ 2 + S.σ i ^ 2)
          + Real.sqrt 3 * Real.sqrt (∑ t ∈ Finset.Icc 1 S.T, G t ω ^ 2) + S.δ) / S.η ∂S.μ := by
        refine integral_mono_of_nonneg ?_ hIntBound (Filter.Eventually.of_forall hpt)
        filter_upwards with ω
        have hd := S.delta_pos
        have hs := Real.sqrt_nonneg
          ((∑ s ∈ Finset.Icc 1 (S.T - 1), S.g s ω i ^ 2) + S.σ i ^ 2
            + ∑ t ∈ Finset.Icc 1 S.T, G t ω ^ 2)
        have hstep : 1 / adagrad_aux_step S ω i
            = (Real.sqrt ((∑ s ∈ Finset.Icc 1 (S.T - 1), S.g s ω i ^ 2) + S.σ i ^ 2
                + ∑ t ∈ Finset.Icc 1 S.T, G t ω ^ 2) + S.δ) / S.η := by
          rw [adagrad_aux_step, one_div_div]
        rw [hstep]
        have := S.eta_pos
        positivity
    _ = ((∫ ω, Real.sqrt (2 * ∑ t ∈ Finset.Icc 1 (S.T - 1), N t ω ^ 2 + S.σ i ^ 2) ∂S.μ)
          + Real.sqrt 3 * ∫ ω, Real.sqrt (∑ t ∈ Finset.Icc 1 S.T, G t ω ^ 2) ∂S.μ
          + S.δ) / S.η := by
        have hA := adagrad_etahat_integrable_sqrt S.μ _ hAint
          (Filter.Eventually.of_forall hAnn)
        have hP := (adagrad_etahat_integrable_sqrt S.μ _ hPint
          (Filter.Eventually.of_forall hPnn)).const_mul (Real.sqrt 3)
        have hAB : Integrable (fun ω =>
            Real.sqrt (2 * ∑ t ∈ Finset.Icc 1 (S.T - 1), N t ω ^ 2 + S.σ i ^ 2)
              + Real.sqrt 3 * Real.sqrt (∑ t ∈ Finset.Icc 1 S.T, G t ω ^ 2)) S.μ := hA.add hP
        rw [integral_div]
        congr 1
        rw [integral_add hAB (integrable_const _), integral_add hA hP,
          integral_const_mul, integral_const, measureReal_univ_eq_one, one_smul]
    _ ≤ (S.σ i * Real.sqrt (2 * S.T) + S.δ) / S.η
          + Real.sqrt 3 / S.η * ∫ ω, Real.sqrt (∑ t ∈ Finset.Icc 1 S.T, G t ω ^ 2) ∂S.μ := by
        rw [div_mul_eq_mul_div, ← add_div]
        refine div_le_div_of_nonneg_right ?_ S.eta_pos.le
        linarith [hJ1]

@[blueprint "lem:adagrad-cs-sq-integral-mul-le"
  (statement := /-- Let $(\Omega, \mathcal{A}, \mu)$ be a measure space and let
    $f, g : \Omega \to \mathbb{R}$ satisfy $f \ge 0$ and $g \ge 0$ $\mu$-almost everywhere
    and $f, g \in L^2(\mu)$. Then
    $$\Bigl(\int_\Omega f g \, d\mu\Bigr)^2
      \le \Bigl(\int_\Omega f^2 \, d\mu\Bigr)
        \Bigl(\int_\Omega g^2 \, d\mu\Bigr).$$ -/)
  (proof := /-- H\"older's inequality for the conjugate pair $(2,2)$, applied to the
    nonnegative functions $f$ and $g$ which lie in $L^2(\mu)$, gives
    $$\int_\Omega f g \, d\mu
      \le \Bigl(\int_\Omega f^2 \, d\mu\Bigr)^{1/2}
        \Bigl(\int_\Omega g^2 \, d\mu\Bigr)^{1/2}
      = \sqrt{\int_\Omega f^2 \, d\mu} \, \sqrt{\int_\Omega g^2 \, d\mu},$$
    where the identification of the exponent $1/2$ with the square root uses that both
    integrals $\int_\Omega f^2 \, d\mu$ and $\int_\Omega g^2 \, d\mu$ are nonnegative,
    being integrals of the nonnegative functions $f^2$ and $g^2$.

    Since $f g \ge 0$ $\mu$-almost everywhere, we also have
    $\int_\Omega f g \, d\mu \ge 0$, so squaring the displayed inequality preserves it:
    $$\Bigl(\int_\Omega f g \, d\mu\Bigr)^2
      \le \Bigl(\sqrt{\int_\Omega f^2 \, d\mu} \, \sqrt{\int_\Omega g^2 \, d\mu}\Bigr)^2
      = \Bigl(\int_\Omega f^2 \, d\mu\Bigr) \Bigl(\int_\Omega g^2 \, d\mu\Bigr),$$
    the last equality because $\bigl(\sqrt{x}\bigr)^2 = x$ for $x \ge 0$. -/)
  (title := /-- Cauchy--Schwarz inequality in squared form -/)
  (latexEnv := "lemma")]
lemma adagrad_cs_sq_integral_mul_le {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℝ) (hf : 0 ≤ᵐ[μ] f) (hg : 0 ≤ᵐ[μ] g) (hf2 : MemLp f 2 μ)
    (hg2 : MemLp g 2 μ) :
    (∫ ω, f ω * g ω ∂μ) ^ 2 ≤ (∫ ω, f ω ^ 2 ∂μ) * ∫ ω, g ω ^ 2 ∂μ := by
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by
    simp
  have hf2' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by rwa [h2]
  have hg2' : MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by rwa [h2]
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two hf hg hf2' hg2'
  have hrw : ∀ x : ℝ, x ^ (2 : ℝ) = x ^ 2 := by
    intro x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [hrw] at hH
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hH
  have hA : 0 ≤ ∫ ω, f ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have hB : 0 ≤ ∫ ω, g ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have hfg : 0 ≤ ∫ ω, f ω * g ω ∂μ := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hf, hg] with ω h1 h2 using mul_nonneg h1 h2
  calc (∫ ω, f ω * g ω ∂μ) ^ 2
      ≤ (Real.sqrt (∫ ω, f ω ^ 2 ∂μ) * Real.sqrt (∫ ω, g ω ^ 2 ∂μ)) ^ 2 := by
        exact pow_le_pow_left₀ hfg hH 2
    _ = (∫ ω, f ω ^ 2 ∂μ) * ∫ ω, g ω ^ 2 ∂μ := by
        rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]

@[blueprint "lem:adagrad-cs-memlp-sqrt"
  (statement := /-- Let $(\Omega, \mathcal{A}, \mu)$ be a measure space and let
    $u : \Omega \to \mathbb{R}$ be $\mu$-integrable with $u \ge 0$ $\mu$-almost everywhere.
    Then $\sqrt{u} \in L^2(\mu)$. -/)
  (proof := /-- The function $\sqrt{\cdot} : \mathbb{R} \to \mathbb{R}$ is continuous and
    $u$ is almost everywhere strongly measurable, being integrable, so the composition
    $\sqrt{u}$ is almost everywhere strongly measurable. For an almost everywhere strongly
    measurable real function, membership in $L^2(\mu)$ is equivalent to integrability of
    its square, so it suffices to show that $\bigl(\sqrt{u}\bigr)^2$ is integrable. Since
    $u \ge 0$ almost everywhere and $\bigl(\sqrt{x}\bigr)^2 = x$ for $x \ge 0$, we have
    $\bigl(\sqrt{u}\bigr)^2 = u$ almost everywhere, and $u$ is integrable by
    hypothesis. -/)
  (title := /-- Square roots of nonnegative integrable functions lie in $L^2$ -/)
  (latexEnv := "lemma")]
lemma adagrad_cs_memlp_sqrt {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (u : Ω → ℝ)
    (hu : 0 ≤ᵐ[μ] u) (huint : Integrable u μ) :
    MemLp (fun ω => Real.sqrt (u ω)) 2 μ := by
  have hm : AEStronglyMeasurable (fun ω => Real.sqrt (u ω)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable huint.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hm).2 ?_
  refine huint.congr ?_
  filter_upwards [hu] with ω hω
  exact (Real.sq_sqrt hω).symm

@[blueprint "lem:adagrad-cs-grad-memlp"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting}, let
    $i \in [d]$ and let $t \ge 1$. Then the function
    $\omega \mapsto \nabla_i F(\mathbf{w}_t(\omega))$ of \cref{def:adagrad-grad-coord}
    belongs to $L^2(\mathbb{P})$. -/)
  (proof := /-- Fix $t \ge 1$ and $i \in [d]$. The map $\omega \mapsto g_{t,i}(\omega)$ is
    $\mathcal{F}_t$-measurable by Assumption \emph{g\_adapted} of
    \cref{def:adagrad-setting}, hence $\mathcal{A}$-measurable because
    $\mathcal{F}_t \subseteq \mathcal{A}$, and $g_{t,i}^2$ is integrable by Assumption
    \emph{g\_sq\_integrable}. For an almost everywhere strongly measurable real function,
    integrability of its square is equivalent to membership in $L^2(\mathbb{P})$, so
    $g_{t,i} \in L^2(\mathbb{P})$.

    Conditional expectation with respect to $\mathcal{F}_{t-1}$ maps $L^2(\mathbb{P})$ into
    itself, since $1 \le 2$, so
    $\mathbb{E}[g_{t,i} \mid \mathcal{F}_{t-1}] \in L^2(\mathbb{P})$. By Assumption
    \emph{unbiased} of \cref{def:adagrad-setting} we have
    $\mathbb{E}[g_{t,i} \mid \mathcal{F}_{t-1}]
    = \nabla_i F(\mathbf{w}_t)$ almost surely, and membership in $L^2(\mathbb{P})$ is
    invariant under almost everywhere equality, whence
    $\nabla_i F(\mathbf{w}_t) \in L^2(\mathbb{P})$. -/)
  (title := /-- The gradient coordinates along the trajectory lie in $L^2$ -/)
  (latexEnv := "lemma")]
lemma adagrad_cs_grad_memlp {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (i : Fin S.d) (t : ℕ) (ht : 1 ≤ t) :
    MemLp (fun ω => adagrad_grad_coord S.obj (S.w t ω) i) 2 S.μ := by
  haveI := S.isProbabilityMeasure
  have hm : Measurable fun ω => S.g t ω i := ((S.g_adapted t).mono (S.ℱ.le t) le_rfl).eval
  have hg : MemLp (fun ω => S.g t ω i) 2 S.μ :=
    (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 (S.g_sq_integrable t i)
  exact MemLp.ae_eq (S.g_unbiased t ht i) (hg.condExp one_le_two)

@[blueprint "lem:adagrad-cs-gradsum-integrable"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting} and let
    $i \in [d]$. Then the function
    $\omega \mapsto \sum_{t=1}^T \nabla_i F(\mathbf{w}_t(\omega))^2$ is
    $\mathbb{P}$-integrable, where $\nabla_i F$ is as in
    \cref{def:adagrad-grad-coord}. -/)
  (proof := /-- For each $t \in \{1, \dots, T\}$ we have $t \ge 1$, so
    $\nabla_i F(\mathbf{w}_t) \in L^2(\mathbb{P})$ by \cref{lem:adagrad-cs-grad-memlp};
    consequently $\nabla_i F(\mathbf{w}_t)^2$ is integrable. A finite sum of integrable
    functions is integrable, and the index set $\{1, \dots, T\}$ is finite, so the sum
    $\sum_{t=1}^T \nabla_i F(\mathbf{w}_t)^2$ is integrable. -/)
  (title := /-- Integrability of the summed squared gradient coordinates -/)
  (latexEnv := "lemma")]
lemma adagrad_cs_gradsum_integrable {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (i : Fin S.d) :
    Integrable (fun ω => ∑ t ∈ Finset.Icc 1 S.T,
      adagrad_grad_coord S.obj (S.w t ω) i ^ 2) S.μ := by
  refine integrable_finset_sum _ fun t ht => ?_
  exact (adagrad_cs_grad_memlp S i t (Finset.mem_Icc.1 ht).1).integrable_sq

@[blueprint "lem:adagrad-cs-ratio-sqrt-pos-le"
  (statement := /-- Let $a, \delta, x \in \mathbb{R}$ with $a > 0$, $\delta > 0$ and
    $x \ge 0$. Then
    $$0 < \frac{a}{\sqrt{x} + \delta} \le \frac{a}{\delta}.$$ -/)
  (proof := /-- Since $x \ge 0$ we have $\sqrt{x} \ge 0$, so
    $\sqrt{x} + \delta \ge \delta > 0$; in particular the denominator is positive and,
    $a$ being positive, the quotient $a / (\sqrt{x} + \delta)$ is positive. For the upper
    bound, dividing the positive numerator $a$ by the larger positive denominator
    $\sqrt{x} + \delta \ge \delta$ gives
    $a / (\sqrt{x} + \delta) \le a / \delta$. -/)
  (title := /-- Two-sided bound for $a/(\sqrt{x} + \delta)$ -/)
  (latexEnv := "lemma")]
lemma adagrad_cs_ratio_sqrt_pos_le (a δ x : ℝ) (ha : 0 < a) (hδ : 0 < δ) (hx : 0 ≤ x) :
    0 < a / (Real.sqrt x + δ) ∧ a / (Real.sqrt x + δ) ≤ a / δ := by
  have hs : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hden : 0 < Real.sqrt x + δ := by linarith
  refine ⟨div_pos ha hden, ?_⟩
  exact div_le_div_of_nonneg_left ha.le hδ (by linarith)

@[blueprint "lem:adagrad-cs-ratio-sqrt-anti"
  (statement := /-- Let $a, \delta, x, y \in \mathbb{R}$ with $a \ge 0$, $\delta > 0$,
    $0 \le x$ and $x \le y$. Then
    $$\frac{a}{\sqrt{y} + \delta} \le \frac{a}{\sqrt{x} + \delta}.$$ -/)
  (proof := /-- From $0 \le x \le y$ and monotonicity of the square root we get
    $0 \le \sqrt{x} \le \sqrt{y}$, hence
    $0 < \delta \le \sqrt{x} + \delta \le \sqrt{y} + \delta$. Dividing the nonnegative
    numerator $a$ by the larger positive denominator gives the assertion. -/)
  (title := /-- Antitonicity of $a/(\sqrt{x} + \delta)$ in $x$ -/)
  (latexEnv := "lemma")]
lemma adagrad_cs_ratio_sqrt_anti (a δ x y : ℝ) (ha : 0 ≤ a) (hδ : 0 < δ) (hx : 0 ≤ x)
    (hxy : x ≤ y) :
    a / (Real.sqrt y + δ) ≤ a / (Real.sqrt x + δ) := by
  have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hmono : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
  exact div_le_div_of_nonneg_left ha (by linarith) (by linarith)

@[blueprint "lem:adagrad-cs-aux-le-decorrelated"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting}, let
    $i \in [d]$, let $\omega \in \Omega$ and let $t \in \{1, \dots, T\}$. Then
    $$\tilde\eta_{T,i}(\omega) \le \hat\eta_{t,i}(\omega),$$
    with $\hat\eta_{t,i}$ as in \cref{def:adagrad-decorrelated-step} and
    $\tilde\eta_{T,i}$ as in \cref{def:adagrad-aux-step}. -/)
  (proof := /-- Write the two step sizes as
    $\hat\eta_{t,i}(\omega) = \eta / (\sqrt{x} + \delta)$ and
    $\tilde\eta_{T,i}(\omega) = \eta / (\sqrt{y} + \delta)$ with
    $$x = \sum_{s=1}^{t-1} g_{s,i}(\omega)^2 + \sigma_i^2
        + \nabla_i F(\mathbf{w}_t(\omega))^2, \qquad
      y = \sum_{s=1}^{T-1} g_{s,i}(\omega)^2 + \sigma_i^2
        + \sum_{t'=1}^T \nabla_i F(\mathbf{w}_{t'}(\omega))^2 .$$
    All three summands of $x$ are nonnegative, so $x \ge 0$.

    We claim $x \le y$. Since $t \le T$ we have $t - 1 \le T - 1$, so
    $\{1, \dots, t-1\} \subseteq \{1, \dots, T-1\}$, and as every term $g_{s,i}(\omega)^2$
    is nonnegative this gives
    $\sum_{s=1}^{t-1} g_{s,i}(\omega)^2 \le \sum_{s=1}^{T-1} g_{s,i}(\omega)^2$. Moreover
    $t \in \{1, \dots, T\}$ and every term $\nabla_i F(\mathbf{w}_{t'}(\omega))^2$ is
    nonnegative, so the single term $\nabla_i F(\mathbf{w}_t(\omega))^2$ is at most the
    full sum $\sum_{t'=1}^T \nabla_i F(\mathbf{w}_{t'}(\omega))^2$. Adding these two
    inequalities and the common term $\sigma_i^2$ yields $x \le y$.

    Since $\eta > 0$ and $\delta > 0$ by \cref{def:adagrad-setting}, the antitonicity
    statement of \cref{lem:adagrad-cs-ratio-sqrt-anti} applied to $a = \eta$ and the pair
    $x \le y$ gives $\eta / (\sqrt{y} + \delta) \le \eta / (\sqrt{x} + \delta)$, which is
    the assertion. -/)
  (title := /-- The auxiliary step size is dominated by the decorrelated step sizes -/)
  (latexEnv := "lemma")]
lemma adagrad_cs_aux_le_decorrelated {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (i : Fin S.d) (ω : Ω) (t : ℕ) (ht : t ∈ Finset.Icc 1 S.T) :
    adagrad_aux_step S ω i ≤ adagrad_decorrelated_step S ω t i := by
  have htT : t ≤ S.T := (Finset.mem_Icc.1 ht).2
  have hsub : Finset.Icc 1 (t - 1) ⊆ Finset.Icc 1 (S.T - 1) :=
    Finset.Icc_subset_Icc le_rfl (Nat.sub_le_sub_right htT 1)
  have hg : (∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2)
      ≤ ∑ s ∈ Finset.Icc 1 (S.T - 1), S.g s ω i ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun s _ _ => sq_nonneg _
  have ha : adagrad_grad_coord S.obj (S.w t ω) i ^ 2
      ≤ ∑ t' ∈ Finset.Icc 1 S.T, adagrad_grad_coord S.obj (S.w t' ω) i ^ 2 :=
    Finset.single_le_sum (f := fun t' => adagrad_grad_coord S.obj (S.w t' ω) i ^ 2)
      (fun t' _ => sq_nonneg _) ht
  have hx : (0 : ℝ) ≤ (∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2) + S.σ i ^ 2
      + adagrad_grad_coord S.obj (S.w t ω) i ^ 2 := by
    have h1 : (0 : ℝ) ≤ ∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2 :=
      Finset.sum_nonneg fun s _ => sq_nonneg _
    have h2 : (0 : ℝ) ≤ S.σ i ^ 2 := sq_nonneg _
    have h3 : (0 : ℝ) ≤ adagrad_grad_coord S.obj (S.w t ω) i ^ 2 := sq_nonneg _
    linarith
  unfold adagrad_aux_step adagrad_decorrelated_step
  exact adagrad_cs_ratio_sqrt_anti S.η S.δ _ _ S.eta_pos.le S.delta_pos hx (by linarith)

@[blueprint "lem:adagrad-cs-step-bounds"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting}, let
    $i \in [d]$ and let $\omega \in \Omega$. Then
    $$0 < \tilde\eta_{T,i}(\omega) \le \frac{\eta}{\delta}, \qquad
      0 < \hat\eta_{t,i}(\omega) \le \frac{\eta}{\delta} \quad (t \in \mathbb{N}),$$
    with $\hat\eta_{t,i}$ as in \cref{def:adagrad-decorrelated-step} and
    $\tilde\eta_{T,i}$ as in \cref{def:adagrad-aux-step}. -/)
  (proof := /-- Both step sizes have the shape $\eta / (\sqrt{z} + \delta)$, where
    $\eta > 0$ and $\delta > 0$ by \cref{def:adagrad-setting} and where the radicand $z$ is
    a sum of squares together with the nonnegative term $\sigma_i^2$, hence $z \ge 0$: for
    $\tilde\eta_{T,i}(\omega)$ the radicand is
    $\sum_{s=1}^{T-1} g_{s,i}(\omega)^2 + \sigma_i^2
    + \sum_{t=1}^T \nabla_i F(\mathbf{w}_t(\omega))^2$, and for
    $\hat\eta_{t,i}(\omega)$ it is
    $\sum_{s=1}^{t-1} g_{s,i}(\omega)^2 + \sigma_i^2
    + \nabla_i F(\mathbf{w}_t(\omega))^2$. In both cases
    \cref{lem:adagrad-cs-ratio-sqrt-pos-le} applied with $a = \eta$ gives positivity and
    the upper bound $\eta / \delta$. -/)
  (title := /-- The step sizes are positive and bounded by $\eta/\delta$ -/)
  (latexEnv := "lemma")]
lemma adagrad_cs_step_bounds {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (i : Fin S.d) (ω : Ω) :
    (0 < adagrad_aux_step S ω i ∧ adagrad_aux_step S ω i ≤ S.η / S.δ) ∧
      ∀ t : ℕ, 0 < adagrad_decorrelated_step S ω t i ∧
        adagrad_decorrelated_step S ω t i ≤ S.η / S.δ := by
  have hσ : (0 : ℝ) ≤ S.σ i ^ 2 := sq_nonneg _
  constructor
  · have hx : (0 : ℝ) ≤ (∑ s ∈ Finset.Icc 1 (S.T - 1), S.g s ω i ^ 2) + S.σ i ^ 2
        + ∑ t ∈ Finset.Icc 1 S.T, adagrad_grad_coord S.obj (S.w t ω) i ^ 2 := by
      have h1 : (0 : ℝ) ≤ ∑ s ∈ Finset.Icc 1 (S.T - 1), S.g s ω i ^ 2 :=
        Finset.sum_nonneg fun s _ => sq_nonneg _
      have h2 : (0 : ℝ) ≤ ∑ t ∈ Finset.Icc 1 S.T,
          adagrad_grad_coord S.obj (S.w t ω) i ^ 2 :=
        Finset.sum_nonneg fun t _ => sq_nonneg _
      linarith
    exact adagrad_cs_ratio_sqrt_pos_le S.η S.δ _ S.eta_pos S.delta_pos hx
  · intro t
    have hx : (0 : ℝ) ≤ (∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2) + S.σ i ^ 2
        + adagrad_grad_coord S.obj (S.w t ω) i ^ 2 := by
      have h1 : (0 : ℝ) ≤ ∑ s ∈ Finset.Icc 1 (t - 1), S.g s ω i ^ 2 :=
        Finset.sum_nonneg fun s _ => sq_nonneg _
      have h3 : (0 : ℝ) ≤ adagrad_grad_coord S.obj (S.w t ω) i ^ 2 := sq_nonneg _
      linarith
    exact adagrad_cs_ratio_sqrt_pos_le S.η S.δ _ S.eta_pos S.delta_pos hx

@[blueprint "lem:adagrad-cs-step-aemeasurable"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting} and let
    $i \in [d]$. Then the function $\omega \mapsto \tilde\eta_{T,i}(\omega)$ of
    \cref{def:adagrad-aux-step} is almost everywhere strongly measurable, and so is
    $\omega \mapsto \hat\eta_{t,i}(\omega)$ of \cref{def:adagrad-decorrelated-step} for
    every $t \ge 1$. -/)
  (proof := /-- For every $s \in \mathbb{N}$ the map $\omega \mapsto g_{s,i}(\omega)$ is
    $\mathcal{F}_s$-measurable by Assumption \emph{g\_adapted} of
    \cref{def:adagrad-setting}, hence $\mathcal{A}$-measurable since
    $\mathcal{F}_s \subseteq \mathcal{A}$, and therefore almost everywhere strongly
    measurable; the same then holds for $g_{s,i}^2$ and for finite sums of such terms. For
    every $t \ge 1$ the map $\omega \mapsto \nabla_i F(\mathbf{w}_t(\omega))$ lies in
    $L^2(\mathbb{P})$ by \cref{lem:adagrad-cs-grad-memlp}, so its square is integrable and
    in particular almost everywhere strongly measurable; the sum
    $\sum_{t=1}^T \nabla_i F(\mathbf{w}_t)^2$ is integrable by
    \cref{lem:adagrad-cs-gradsum-integrable}, hence likewise almost everywhere strongly
    measurable.

    Consequently the radicands
    $\sum_{s=1}^{T-1} g_{s,i}^2 + \sigma_i^2
    + \sum_{t=1}^T \nabla_i F(\mathbf{w}_t)^2$ and
    $\sum_{s=1}^{t-1} g_{s,i}^2 + \sigma_i^2 + \nabla_i F(\mathbf{w}_t)^2$ are almost
    everywhere strongly measurable. The square root is continuous on $\mathbb{R}$, so
    composing preserves almost everywhere strong measurability, and adding the constant
    $\delta$ and dividing the constant $\eta$ by the result preserves it as well. -/)
  (title := /-- Measurability of the two step sizes -/)
  (latexEnv := "lemma")]
lemma adagrad_cs_step_aemeasurable {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (i : Fin S.d) :
    AEStronglyMeasurable (fun ω => adagrad_aux_step S ω i) S.μ ∧
      ∀ t : ℕ, 1 ≤ t →
        AEStronglyMeasurable (fun ω => adagrad_decorrelated_step S ω t i) S.μ := by
  have hg : ∀ s : ℕ, AEStronglyMeasurable (fun ω => S.g s ω i) S.μ := fun s =>
    (((S.g_adapted s).mono (S.ℱ.le s) le_rfl).eval).aestronglyMeasurable
  have hgsum : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω => ∑ s ∈ Finset.Icc 1 n, S.g s ω i ^ 2) S.μ := by
    intro n
    fun_prop
  have hsqrt : ∀ (n : ℕ) (u : Ω → ℝ), AEStronglyMeasurable u S.μ →
      AEStronglyMeasurable (fun ω => S.η /
        (Real.sqrt ((∑ s ∈ Finset.Icc 1 n, S.g s ω i ^ 2) + S.σ i ^ 2 + u ω) + S.δ)) S.μ := by
    intro n u hu
    have hrad : AEStronglyMeasurable
        (fun ω => (∑ s ∈ Finset.Icc 1 n, S.g s ω i ^ 2) + S.σ i ^ 2 + u ω) S.μ :=
      ((hgsum n).add aestronglyMeasurable_const).add hu
    have hs : AEMeasurable
        (fun ω => Real.sqrt ((∑ s ∈ Finset.Icc 1 n, S.g s ω i ^ 2) + S.σ i ^ 2 + u ω) + S.δ)
        S.μ :=
      ((Real.continuous_sqrt.comp_aestronglyMeasurable hrad).aemeasurable).add
        aemeasurable_const
    exact (aemeasurable_const.div hs).aestronglyMeasurable
  refine ⟨?_, fun t ht => ?_⟩
  · have hgrad : AEStronglyMeasurable
        (fun ω => ∑ t ∈ Finset.Icc 1 S.T,
          adagrad_grad_coord S.obj (S.w t ω) i ^ 2) S.μ :=
      (adagrad_cs_gradsum_integrable S i).aestronglyMeasurable
    exact hsqrt (S.T - 1) _ hgrad
  · have hgrad : AEStronglyMeasurable
        (fun ω => adagrad_grad_coord S.obj (S.w t ω) i ^ 2) S.μ :=
      (adagrad_cs_grad_memlp S i t ht).integrable_sq.aestronglyMeasurable
    exact hsqrt (t - 1) _ hgrad

@[blueprint "lem:adagrad-cs-inv-aux-integrable"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting} and let
    $i \in [d]$. Then the function $\omega \mapsto 1 / \tilde\eta_{T,i}(\omega)$ is
    $\mathbb{P}$-integrable, with $\tilde\eta_{T,i}$ as in
    \cref{def:adagrad-aux-step}. -/)
  (proof := /-- By definition
    $$\frac{1}{\tilde\eta_{T,i}}
      = \frac{\sqrt{R} + \delta}{\eta}, \qquad
      R = \sum_{s=1}^{T-1} g_{s,i}^2 + \sigma_i^2
        + \sum_{t=1}^T \nabla_i F(\mathbf{w}_t)^2 .$$
    The radicand $R$ is integrable: each $g_{s,i}^2$ is integrable by Assumption
    \emph{g\_sq\_integrable} of \cref{def:adagrad-setting} and the index set
    $\{1, \dots, T-1\}$ is finite; the constant $\sigma_i^2$ is integrable because
    $\mathbb{P}$ is a probability measure; and
    $\sum_{t=1}^T \nabla_i F(\mathbf{w}_t)^2$ is integrable by
    \cref{lem:adagrad-cs-gradsum-integrable}. Moreover $R \ge 0$, being a sum of squares
    and of the nonnegative constant $\sigma_i^2$.

    Hence $\sqrt{R} \in L^2(\mathbb{P})$ by \cref{lem:adagrad-cs-memlp-sqrt}, and since
    $\mathbb{P}$ is a probability measure, in particular a finite measure, membership in
    $L^2$ implies integrability, so $\sqrt{R}$ is integrable. Adding the integrable
    constant $\delta$ and dividing by the constant $\eta$ preserves integrability, which
    gives the assertion. -/)
  (title := /-- Integrability of the reciprocal auxiliary step size -/)
  (latexEnv := "lemma")]
lemma adagrad_cs_inv_aux_integrable {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (i : Fin S.d) :
    Integrable (fun ω => 1 / adagrad_aux_step S ω i) S.μ := by
  haveI := S.isProbabilityMeasure
  have hrad : Integrable (fun ω => (∑ s ∈ Finset.Icc 1 (S.T - 1), S.g s ω i ^ 2)
      + S.σ i ^ 2 + ∑ t ∈ Finset.Icc 1 S.T,
        adagrad_grad_coord S.obj (S.w t ω) i ^ 2) S.μ :=
    ((integrable_finset_sum _ fun s _ => S.g_sq_integrable s i).add
      (integrable_const _)).add (adagrad_cs_gradsum_integrable S i)
  have hsq := (adagrad_cs_memlp_sqrt S.μ _
    (Filter.Eventually.of_forall fun ω => by positivity) hrad).integrable one_le_two
  unfold adagrad_aux_step
  simpa [one_div_div] using (hsq.add (integrable_const S.δ)).div_const S.η

@[blueprint "lem:adagrad-cs-first-factor-integrable"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting} and let
    $i \in [d]$. Then the function
    $\omega \mapsto \sum_{t=1}^T \frac{\hat\eta_{t,i}(\omega)}{2}
    \nabla_i F(\mathbf{w}_t(\omega))^2$ is $\mathbb{P}$-integrable, with $\hat\eta_{t,i}$ as
    in \cref{def:adagrad-decorrelated-step}. -/)
  (proof := /-- It suffices to prove that each of the $T$ summands is integrable, since the
    index set $\{1, \dots, T\}$ is finite. Fix $t \in \{1, \dots, T\}$, so $t \ge 1$.

    The function $\omega \mapsto \hat\eta_{t,i}(\omega)/2$ is almost everywhere strongly
    measurable by \cref{lem:adagrad-cs-step-aemeasurable}, and it is bounded: by
    \cref{lem:adagrad-cs-step-bounds} we have
    $0 < \hat\eta_{t,i}(\omega) \le \eta/\delta$ for every $\omega$, so
    $\|\hat\eta_{t,i}(\omega)/2\| \le \eta/(2\delta)$.

    The function $\omega \mapsto \nabla_i F(\mathbf{w}_t(\omega))^2$ is integrable, because
    $\nabla_i F(\mathbf{w}_t) \in L^2(\mathbb{P})$ by \cref{lem:adagrad-cs-grad-memlp}.
    The product of a bounded almost everywhere strongly measurable function with an
    integrable function is integrable, which gives integrability of the summand
    $\frac{\hat\eta_{t,i}}{2} \nabla_i F(\mathbf{w}_t)^2$. -/)
  (title := /-- Integrability of the weighted squared gradient sum -/)
  (latexEnv := "lemma")]
lemma adagrad_cs_first_factor_integrable {Ω : Type} [MeasurableSpace Ω]
    (S : adagrad_setting Ω) (i : Fin S.d) :
    Integrable (fun ω => ∑ t ∈ Finset.Icc 1 S.T, adagrad_decorrelated_step S ω t i / 2
      * adagrad_grad_coord S.obj (S.w t ω) i ^ 2) S.μ := by
  refine integrable_finset_sum _ fun t ht => ?_
  have ht1 : 1 ≤ t := (Finset.mem_Icc.1 ht).1
  have hmeas : AEStronglyMeasurable
      (fun ω => adagrad_decorrelated_step S ω t i / 2) S.μ :=
    (((adagrad_cs_step_aemeasurable S i).2 t ht1).aemeasurable.div_const 2).aestronglyMeasurable
  have hbdd : ∀ᵐ ω ∂S.μ, ‖adagrad_decorrelated_step S ω t i / 2‖ ≤ S.η / S.δ := by
    filter_upwards with ω
    have h := (adagrad_cs_step_bounds S i ω).2 t
    have hηδ : 0 < S.η / S.δ := div_pos S.eta_pos S.delta_pos
    rw [Real.norm_of_nonneg (by linarith [h.1])]
    linarith [h.1, h.2]
  exact Integrable.bdd_mul' (adagrad_cs_grad_memlp S i t ht1).integrable_sq hmeas hbdd

@[blueprint "lem:adagrad-cs-sqrt-factor"
  (statement := /-- Let $a, x \in \mathbb{R}$ with $a > 0$ and $x \ge 0$. Then
    $$\sqrt{a x} \cdot \sqrt{1/a} = \sqrt{x}.$$ -/)
  (proof := /-- Since $a > 0$ and $x \ge 0$ we have $a x \ge 0$, so multiplicativity of the
    square root on nonnegative arguments gives
    $\sqrt{a x} \cdot \sqrt{1/a} = \sqrt{a x \cdot (1/a)}$. As $a \ne 0$, we have
    $a x \cdot (1/a) = x$, whence the right-hand side equals $\sqrt{x}$. -/)
  (title := /-- Factorisation of a square root through a positive weight -/)
  (latexEnv := "lemma")]
lemma adagrad_cs_sqrt_factor (a x : ℝ) (ha : 0 < a) (hx : 0 ≤ x) :
    Real.sqrt (a * x) * Real.sqrt (1 / a) = Real.sqrt x := by
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp

@[blueprint "lem:adagrad-cs-aux-mul-gradsum-le"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting}, let
    $i \in [d]$ and let $\omega \in \Omega$. Then
    $$\tilde\eta_{T,i}(\omega) \sum_{t=1}^T \nabla_i F(\mathbf{w}_t(\omega))^2
      \le 2 \sum_{t=1}^T \frac{\hat\eta_{t,i}(\omega)}{2}
        \nabla_i F(\mathbf{w}_t(\omega))^2,$$
    with $\hat\eta_{t,i}$ as in \cref{def:adagrad-decorrelated-step} and
    $\tilde\eta_{T,i}$ as in \cref{def:adagrad-aux-step}. -/)
  (proof := /-- Distributing the factors over the finite sum, it suffices to prove the
    termwise inequality
    $$\tilde\eta_{T,i}(\omega) \nabla_i F(\mathbf{w}_t(\omega))^2
      \le 2 \cdot \frac{\hat\eta_{t,i}(\omega)}{2}
        \nabla_i F(\mathbf{w}_t(\omega))^2$$
    for each $t \in \{1, \dots, T\}$. By \cref{lem:adagrad-cs-aux-le-decorrelated} we have
    $\tilde\eta_{T,i}(\omega) \le \hat\eta_{t,i}(\omega)$; multiplying this inequality by
    the nonnegative number $\nabla_i F(\mathbf{w}_t(\omega))^2$ gives
    $\tilde\eta_{T,i}(\omega) \nabla_i F(\mathbf{w}_t(\omega))^2
    \le \hat\eta_{t,i}(\omega) \nabla_i F(\mathbf{w}_t(\omega))^2$, and the right-hand side
    equals $2 \cdot \frac{\hat\eta_{t,i}(\omega)}{2}
    \nabla_i F(\mathbf{w}_t(\omega))^2$. -/)
  (title := /-- Replacing the auxiliary step size by the decorrelated ones -/)
  (latexEnv := "lemma")]
lemma adagrad_cs_aux_mul_gradsum_le {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (i : Fin S.d) (ω : Ω) :
    adagrad_aux_step S ω i * ∑ t ∈ Finset.Icc 1 S.T,
        adagrad_grad_coord S.obj (S.w t ω) i ^ 2
      ≤ 2 * ∑ t ∈ Finset.Icc 1 S.T, adagrad_decorrelated_step S ω t i / 2
          * adagrad_grad_coord S.obj (S.w t ω) i ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun t ht => ?_
  have h := adagrad_cs_aux_le_decorrelated S i ω t ht
  have hx : (0 : ℝ) ≤ adagrad_grad_coord S.obj (S.w t ω) i ^ 2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right h hx
  linarith

@[blueprint "lem:adagrad-cs-aux-mul-gradsum-integrable"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting} and let
    $i \in [d]$. Then the function
    $\omega \mapsto \tilde\eta_{T,i}(\omega) \sum_{t=1}^T
    \nabla_i F(\mathbf{w}_t(\omega))^2$ is $\mathbb{P}$-integrable, with $\tilde\eta_{T,i}$
    as in \cref{def:adagrad-aux-step}. -/)
  (proof := /-- The function
    $\omega \mapsto \sum_{t=1}^T \nabla_i F(\mathbf{w}_t(\omega))^2$ is integrable by
    \cref{lem:adagrad-cs-gradsum-integrable}. The function
    $\omega \mapsto \tilde\eta_{T,i}(\omega)$ is almost everywhere strongly measurable by
    \cref{lem:adagrad-cs-step-aemeasurable}, and by \cref{lem:adagrad-cs-step-bounds} it
    satisfies $0 < \tilde\eta_{T,i}(\omega) \le \eta/\delta$ for every $\omega$, so
    $\|\tilde\eta_{T,i}(\omega)\| \le \eta/\delta$. The product of a bounded almost
    everywhere strongly measurable function with an integrable function is integrable. -/)
  (title := /-- Integrability of the auxiliary step size times the squared gradient sum -/)
  (latexEnv := "lemma")]
lemma adagrad_cs_aux_mul_gradsum_integrable {Ω : Type} [MeasurableSpace Ω]
    (S : adagrad_setting Ω) (i : Fin S.d) :
    Integrable (fun ω => adagrad_aux_step S ω i * ∑ t ∈ Finset.Icc 1 S.T,
      adagrad_grad_coord S.obj (S.w t ω) i ^ 2) S.μ := by
  have hbdd : ∀ᵐ ω ∂S.μ, ‖adagrad_aux_step S ω i‖ ≤ S.η / S.δ := by
    filter_upwards with ω
    have h := (adagrad_cs_step_bounds S i ω).1
    rw [Real.norm_of_nonneg h.1.le]
    exact h.2
  exact Integrable.bdd_mul' (adagrad_cs_gradsum_integrable S i)
    (adagrad_cs_step_aemeasurable S i).1 hbdd

@[blueprint "lem:adagrad-cs-integral-first-factor-le"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting} and let
    $i \in [d]$. Then
    $$\mathbb{E}\Bigl[\tilde\eta_{T,i} \sum_{t=1}^T \nabla_i F(\mathbf{w}_t)^2\Bigr]
      \le 2 \, \mathbb{E}\Bigl[\sum_{t=1}^T \frac{\hat\eta_{t,i}}{2}
        \nabla_i F(\mathbf{w}_t)^2\Bigr],$$
    with $\hat\eta_{t,i}$ as in \cref{def:adagrad-decorrelated-step} and
    $\tilde\eta_{T,i}$ as in \cref{def:adagrad-aux-step}. -/)
  (proof := /-- The integrand on the left is integrable by
    \cref{lem:adagrad-cs-aux-mul-gradsum-integrable}. The integrand on the right is
    integrable as well: by
    \cref{lem:adagrad-cs-first-factor-integrable} the function
    $\omega \mapsto \sum_{t=1}^T \frac{\hat\eta_{t,i}(\omega)}{2}
    \nabla_i F(\mathbf{w}_t(\omega))^2$ is integrable, and multiplying by the constant $2$
    preserves integrability.

    By \cref{lem:adagrad-cs-aux-mul-gradsum-le} the left integrand is pointwise at most the
    right integrand, so monotonicity of the integral for integrable functions gives
    $$\mathbb{E}\Bigl[\tilde\eta_{T,i} \sum_{t=1}^T \nabla_i F(\mathbf{w}_t)^2\Bigr]
      \le \mathbb{E}\Bigl[2 \sum_{t=1}^T \frac{\hat\eta_{t,i}}{2}
        \nabla_i F(\mathbf{w}_t)^2\Bigr],$$
    and the right-hand side equals
    $2 \, \mathbb{E}\bigl[\sum_{t=1}^T \frac{\hat\eta_{t,i}}{2}
    \nabla_i F(\mathbf{w}_t)^2\bigr]$ because the integral is linear. -/)
  (title := /-- Integrated form of the step-size comparison -/)
  (latexEnv := "lemma")]
lemma adagrad_cs_integral_first_factor_le {Ω : Type} [MeasurableSpace Ω]
    (S : adagrad_setting Ω) (i : Fin S.d) :
    (∫ ω, adagrad_aux_step S ω i * ∑ t ∈ Finset.Icc 1 S.T,
        adagrad_grad_coord S.obj (S.w t ω) i ^ 2 ∂S.μ)
      ≤ 2 * ∫ ω, ∑ t ∈ Finset.Icc 1 S.T, adagrad_decorrelated_step S ω t i / 2
          * adagrad_grad_coord S.obj (S.w t ω) i ^ 2 ∂S.μ := by
  have hleft := adagrad_cs_aux_mul_gradsum_integrable S i
  have hright : Integrable (fun ω => 2 * ∑ t ∈ Finset.Icc 1 S.T,
      adagrad_decorrelated_step S ω t i / 2
        * adagrad_grad_coord S.obj (S.w t ω) i ^ 2) S.μ :=
    (adagrad_cs_first_factor_integrable S i).const_mul 2
  rw [← integral_const_mul]
  exact integral_mono hleft hright fun ω => adagrad_cs_aux_mul_gradsum_le S i ω

@[blueprint "lem:adagrad-cauchy-schwarz-step"
  (statement := /-- Let $S$ be an AdaGrad setting as in \cref{def:adagrad-setting} and let
    $i \in [d]$. Then
    $$\mathbb{E}\Bigl[\sqrt{\sum_{t=1}^T \nabla_i F(\mathbf{w}_t)^2}\Bigr]^2
      \le \mathbb{E}\Bigl[\sum_{t=1}^T \frac{\hat\eta_{t,i}}{2}
        \nabla_i F(\mathbf{w}_t)^2\Bigr]
        \cdot \mathbb{E}\Bigl[\frac{2}{\tilde\eta_{T,i}}\Bigr],$$
    with $\hat\eta_{t,i}$ as in \cref{def:adagrad-decorrelated-step} and
    $\tilde\eta_{T,i}$ as in \cref{def:adagrad-aux-step}. -/)
  (proof := /-- Write $G(\omega) = \sum_{t=1}^T \nabla_i F(\mathbf{w}_t(\omega))^2$; being a
    sum of squares, $G(\omega) \ge 0$ for every $\omega$. By
    \cref{lem:adagrad-cs-step-bounds} we have $\tilde\eta_{T,i}(\omega) > 0$ for every
    $\omega$, so \cref{lem:adagrad-cs-sqrt-factor} applied with
    $a = \tilde\eta_{T,i}(\omega)$ and $x = G(\omega)$ gives the pointwise factorisation
    $$\sqrt{G(\omega)}
      = \sqrt{\tilde\eta_{T,i}(\omega) G(\omega)}
        \cdot \sqrt{\frac{1}{\tilde\eta_{T,i}(\omega)}} .$$

    Both factors lie in $L^2(\mathbb{P})$. Indeed
    $\omega \mapsto \tilde\eta_{T,i}(\omega) G(\omega)$ is nonnegative and integrable by
    \cref{lem:adagrad-cs-aux-mul-gradsum-integrable}, and
    $\omega \mapsto 1/\tilde\eta_{T,i}(\omega)$ is nonnegative and integrable by
    \cref{lem:adagrad-cs-inv-aux-integrable}, so
    \cref{lem:adagrad-cs-memlp-sqrt} applies to each of them.

    Applying \cref{lem:adagrad-cs-sq-integral-mul-le} to the two nonnegative $L^2$
    functions $\sqrt{\tilde\eta_{T,i} G}$ and $\sqrt{1/\tilde\eta_{T,i}}$, and rewriting
    the product of their square roots by the factorisation above and their squares by
    $\bigl(\sqrt{x}\bigr)^2 = x$ for $x \ge 0$, yields
    $$\Bigl(\int_\Omega \sqrt{G} \, d\mathbb{P}\Bigr)^2
      \le \Bigl(\int_\Omega \tilde\eta_{T,i} G \, d\mathbb{P}\Bigr)
        \Bigl(\int_\Omega \frac{1}{\tilde\eta_{T,i}} \, d\mathbb{P}\Bigr).$$

    The second factor is nonnegative, being the integral of the nonnegative function
    $1/\tilde\eta_{T,i}$, so the first factor may be enlarged: by
    \cref{lem:adagrad-cs-integral-first-factor-le},
    $$\int_\Omega \tilde\eta_{T,i} G \, d\mathbb{P}
      \le 2 \int_\Omega \sum_{t=1}^T \frac{\hat\eta_{t,i}}{2}
        \nabla_i F(\mathbf{w}_t)^2 \, d\mathbb{P},$$
    whence
    $$\Bigl(\int_\Omega \sqrt{G} \, d\mathbb{P}\Bigr)^2
      \le \Bigl(2 \int_\Omega \sum_{t=1}^T \frac{\hat\eta_{t,i}}{2}
          \nabla_i F(\mathbf{w}_t)^2 \, d\mathbb{P}\Bigr)
        \Bigl(\int_\Omega \frac{1}{\tilde\eta_{T,i}} \, d\mathbb{P}\Bigr).$$

    Finally, linearity of the integral gives
    $\int_\Omega \frac{2}{\tilde\eta_{T,i}} \, d\mathbb{P}
    = 2 \int_\Omega \frac{1}{\tilde\eta_{T,i}} \, d\mathbb{P}$, and moving the factor $2$
    from the first factor to the second rearranges the last display into the assertion. -/)
  (title := /-- Cauchy--Schwarz pairing of the two step sizes -/)
  (latexEnv := "lemma")]
lemma adagrad_cauchy_schwarz_step {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω)
    (i : Fin S.d) :
    (∫ ω, Real.sqrt (∑ t ∈ Finset.Icc 1 S.T,
        adagrad_grad_coord S.obj (S.w t ω) i ^ 2) ∂S.μ) ^ 2
      ≤ (∫ ω, ∑ t ∈ Finset.Icc 1 S.T, adagrad_decorrelated_step S ω t i / 2
            * adagrad_grad_coord S.obj (S.w t ω) i ^ 2 ∂S.μ)
        * ∫ ω, 2 / adagrad_aux_step S ω i ∂S.μ := by
  set G : Ω → ℝ := fun ω => ∑ t ∈ Finset.Icc 1 S.T,
    adagrad_grad_coord S.obj (S.w t ω) i ^ 2 with hG
  have hGnonneg : ∀ ω, 0 ≤ G ω := fun ω => Finset.sum_nonneg fun t _ => sq_nonneg _
  have hstep : ∀ ω, 0 < adagrad_aux_step S ω i := fun ω => (adagrad_cs_step_bounds S i ω).1.1
  have hfactor : ∀ ω, Real.sqrt (adagrad_aux_step S ω i * G ω)
      * Real.sqrt (1 / adagrad_aux_step S ω i) = Real.sqrt (G ω) := fun ω =>
    adagrad_cs_sqrt_factor _ _ (hstep ω) (hGnonneg ω)
  have hf2 : MemLp (fun ω => Real.sqrt (adagrad_aux_step S ω i * G ω)) 2 S.μ :=
    adagrad_cs_memlp_sqrt S.μ _
      (Filter.Eventually.of_forall fun ω => (mul_nonneg (hstep ω).le (hGnonneg ω)))
      (adagrad_cs_aux_mul_gradsum_integrable S i)
  have hg2 : MemLp (fun ω => Real.sqrt (1 / adagrad_aux_step S ω i)) 2 S.μ :=
    adagrad_cs_memlp_sqrt S.μ _
      (Filter.Eventually.of_forall fun ω => (one_div_pos.2 (hstep ω)).le)
      (adagrad_cs_inv_aux_integrable S i)
  have hCS := adagrad_cs_sq_integral_mul_le S.μ
    (fun ω => Real.sqrt (adagrad_aux_step S ω i * G ω))
    (fun ω => Real.sqrt (1 / adagrad_aux_step S ω i))
    (Filter.Eventually.of_forall fun ω => Real.sqrt_nonneg _)
    (Filter.Eventually.of_forall fun ω => Real.sqrt_nonneg _) hf2 hg2
  simp only [hfactor] at hCS
  have hsq1 : ∀ ω, Real.sqrt (adagrad_aux_step S ω i * G ω) ^ 2
      = adagrad_aux_step S ω i * G ω := fun ω =>
    Real.sq_sqrt (mul_nonneg (hstep ω).le (hGnonneg ω))
  have hsq2 : ∀ ω, Real.sqrt (1 / adagrad_aux_step S ω i) ^ 2
      = 1 / adagrad_aux_step S ω i := fun ω =>
    Real.sq_sqrt (one_div_pos.2 (hstep ω)).le
  simp only [hsq1, hsq2] at hCS
  have hA := adagrad_cs_integral_first_factor_le S i
  have hBnonneg : 0 ≤ ∫ ω, 1 / adagrad_aux_step S ω i ∂S.μ :=
    integral_nonneg fun ω => (one_div_pos.2 (hstep ω)).le
  have hAnonneg : 0 ≤ ∫ ω, adagrad_aux_step S ω i * G ω ∂S.μ :=
    integral_nonneg fun ω => mul_nonneg (hstep ω).le (hGnonneg ω)
  have hB2 : (∫ ω, 2 / adagrad_aux_step S ω i ∂S.μ)
      = 2 * ∫ ω, 1 / adagrad_aux_step S ω i ∂S.μ := by
    rw [← integral_const_mul]
    congr 1 with ω
    rw [mul_one_div]
  rw [hB2]
  calc (∫ ω, Real.sqrt (G ω) ∂S.μ) ^ 2
      ≤ (∫ ω, adagrad_aux_step S ω i * G ω ∂S.μ)
          * ∫ ω, 1 / adagrad_aux_step S ω i ∂S.μ := hCS
    _ ≤ (2 * ∫ ω, ∑ t ∈ Finset.Icc 1 S.T, adagrad_decorrelated_step S ω t i / 2
            * adagrad_grad_coord S.obj (S.w t ω) i ^ 2 ∂S.μ)
          * ∫ ω, 1 / adagrad_aux_step S ω i ∂S.μ :=
        mul_le_mul_of_nonneg_right hA hBnonneg
    _ = (∫ ω, ∑ t ∈ Finset.Icc 1 S.T, adagrad_decorrelated_step S ω t i / 2
            * adagrad_grad_coord S.obj (S.w t ω) i ^ 2 ∂S.μ)
          * (2 * ∫ ω, 1 / adagrad_aux_step S ω i ∂S.μ) := by ring

@[blueprint "lem:adagrad-bound-on-sum-sqrt"
  (statement := /-- There exists a real constant $c \ge 1$, independent of the
    measurable space and of the AdaGrad setting, such that for every type $\Omega$
    equipped with a measurable space and every AdaGrad setting $S$ on $\Omega$ as in
    \cref{def:adagrad-setting},
    $$\sum_{i=1}^d
      \mathbb{E}\Bigl[\sqrt{\sum_{t=1}^T \nabla_i F(\mathbf{w}_t)^2}\Bigr]
      \le \frac{2\sqrt{3}}{\eta} Q_c(S) + \sqrt{\frac{2 d \delta\, Q_c(S)}{\eta}}
      + 2 \sqrt{\frac{\|\bm\sigma\|_1 Q_c(S)}{\eta}}\, T^{1/4}.$$
    Here the expectation is taken with respect to the probability measure of $S$,
    $Q_c(S)$ is the gradient budget of \cref{def:adagrad-gradient-budget}, and
    $\|\cdot\|_1$ is the norm of \cref{def:adagrad-l1-norm}. -/)
  (proof := /-- Choose $c \ge 1$ from \cref{lem:adagrad-bound-on-gradient}, and fix a
    measurable space and an AdaGrad setting $S$. For $i \in [d]$, set
    $$x_i=\mathbb{E}\Bigl[\sqrt{\sum_{t=1}^T
      \nabla_iF(\mathbf w_t)^2}\Bigr],\qquad
      A_i=\mathbb{E}\Bigl[\sum_{t=1}^T\frac{\hat\eta_{t,i}}2
      \nabla_iF(\mathbf w_t)^2\Bigr].$$
    Both quantities are nonnegative: this is immediate for $x_i$, while for $A_i$ it
    follows from the positivity of the decorrelated step size in
    \cref{lem:adagrad-cs-step-bounds}. The integrability assertion in
    \cref{lem:adagrad-per-step-term-integrable} permits interchange of the finite
    coordinate and time sums with the integral below.

    By \cref{lem:adagrad-cauchy-schwarz-step},
    $x_i^2\le A_i\mathbb{E}[2/\tilde\eta_{T,i}]$. Applying
    \cref{lem:adagrad-upper-bound-etahat} and multiplying its estimate by the
    nonnegative number $2A_i$ gives
    $$x_i^2\le \frac{2A_i}{\eta}
      \bigl(\sigma_i\sqrt{2T}+\delta+\sqrt3\,x_i\bigr).$$
    Put
    $$U_i=\frac2\eta(\sigma_i\sqrt{2T}+\delta),\qquad
      B_i=\frac{2\sqrt3}{\eta}A_i.$$
    Then $U_i,B_i\ge0$ and the preceding inequality is
    $x_i^2\le U_iA_i+B_ix_i$. Since $x_i\ge0$, comparison of squares yields
    $$x_i\le B_i+\sqrt{U_iA_i}.$$

    Summing this estimate and applying the finite Cauchy--Schwarz inequality gives
    $$\sum_{i=1}^d x_i\le \frac{2\sqrt3}{\eta}\sum_{i=1}^d A_i
      +\sqrt{\sum_{i=1}^dU_i}\sqrt{\sum_{i=1}^dA_i}.$$
    The nonnegativity of the coordinates of $\bm\sigma$ and
    \cref{def:adagrad-l1-norm} imply
    $$\sum_{i=1}^dU_i
      =\frac2\eta\bigl(\|\bm\sigma\|_1\sqrt{2T}+d\delta\bigr).$$
    Moreover, after the justified integral and finite-sum interchange,
    \cref{lem:adagrad-bound-on-gradient} yields
    $\sum_iA_i\le Q_c(S)$. In particular $Q_c(S)\ge0$, and therefore
    $$\sum_{i=1}^d x_i\le \frac{2\sqrt3}{\eta}Q_c(S)
      +\sqrt{\frac2\eta
        \bigl(\|\bm\sigma\|_1\sqrt{2T}+d\delta\bigr)}\sqrt{Q_c(S)}.$$

    Split the last square root into its $d\delta$ and
    $\|\bm\sigma\|_1\sqrt{2T}$ contributions. The former is
    $\sqrt{2d\delta Q_c(S)/\eta}$. For the latter, the elementary estimate
    $\sqrt{2T}\le2\sqrt T$ gives
    $$\sqrt{\frac{2\|\bm\sigma\|_1Q_c(S)}\eta\sqrt{2T}}
      \le2\sqrt{\frac{\|\bm\sigma\|_1Q_c(S)}\eta}\,
        \sqrt{\sqrt T}
      =2\sqrt{\frac{\|\bm\sigma\|_1Q_c(S)}\eta}\,T^{1/4}.$$
    Substitution proves the claimed bound. -/)
  (title := /-- Bound on the summed root gradient sums -/)
  (latexEnv := "lemma")]
lemma adagrad_bound_on_sum_sqrt :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : adagrad_setting Ω),
      (∑ i, ∫ ω, Real.sqrt (∑ t ∈ Finset.Icc 1 S.T,
          adagrad_grad_coord S.obj (S.w t ω) i ^ 2) ∂S.μ)
        ≤ 2 * Real.sqrt 3 / S.η * adagrad_gradient_budget S c
          + Real.sqrt (2 * S.d * S.δ * adagrad_gradient_budget S c / S.η)
          + 2 * Real.sqrt (adagrad_l1_norm S.σ * adagrad_gradient_budget S c / S.η)
            * (S.T : ℝ) ^ ((1 : ℝ) / 4) := by
  obtain ⟨c, hc, hbudget⟩ := adagrad_bound_on_gradient
  refine ⟨c, hc, ?_⟩
  intro Ω _ S
  classical
  let X : Fin S.d → ℝ := fun i =>
    ∫ ω, Real.sqrt (∑ t ∈ Finset.Icc 1 S.T,
      adagrad_grad_coord S.obj (S.w t ω) i ^ 2) ∂S.μ
  let A : Fin S.d → ℝ := fun i =>
    ∫ ω, ∑ t ∈ Finset.Icc 1 S.T, adagrad_decorrelated_step S ω t i / 2
      * adagrad_grad_coord S.obj (S.w t ω) i ^ 2 ∂S.μ
  let U : Fin S.d → ℝ := fun i =>
    2 / S.η * (S.σ i * Real.sqrt (2 * S.T) + S.δ)
  let B : Fin S.d → ℝ := fun i => 2 * Real.sqrt 3 / S.η * A i
  have hX (i : Fin S.d) : 0 ≤ X i := by
    dsimp [X]
    exact integral_nonneg fun ω => Real.sqrt_nonneg _
  have hA (i : Fin S.d) : 0 ≤ A i := by
    dsimp [A]
    refine integral_nonneg fun ω => Finset.sum_nonneg ?_
    intro t ht
    exact mul_nonneg (div_nonneg ((adagrad_cs_step_bounds S i ω).2 t).1.le (by norm_num))
      (sq_nonneg _)
  have hU (i : Fin S.d) : 0 ≤ U i := by
    dsimp [U]
    exact mul_nonneg (div_nonneg (by norm_num) S.eta_pos.le)
      (add_nonneg (mul_nonneg (S.sigma_nonneg i) (Real.sqrt_nonneg _)) S.delta_pos.le)
  have hB (i : Fin S.d) : 0 ≤ B i := by
    dsimp [B]
    exact mul_nonneg
      (div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) S.eta_pos.le) (hA i)
  have hcoord (i : Fin S.d) : X i ≤ B i + Real.sqrt (U i * A i) := by
    have hinv :
        (∫ ω, 2 / adagrad_aux_step S ω i ∂S.μ)
          = 2 * ∫ ω, 1 / adagrad_aux_step S ω i ∂S.μ := by
      rw [← integral_const_mul]
      congr 1 with ω
      rw [mul_one_div]
    have htwice :
        (∫ ω, 2 / adagrad_aux_step S ω i ∂S.μ)
          ≤ 2 * ((S.σ i * Real.sqrt (2 * S.T) + S.δ) / S.η
            + Real.sqrt 3 / S.η * X i) := by
      rw [hinv]
      gcongr
      simpa [X] using adagrad_upper_bound_etahat S i
    have hquad : X i ^ 2 ≤ U i * A i + B i * X i := by
      calc
        X i ^ 2 ≤ A i * ∫ ω, 2 / adagrad_aux_step S ω i ∂S.μ := by
          simpa [X, A] using adagrad_cauchy_schwarz_step S i
        _ ≤ A i * (2 * ((S.σ i * Real.sqrt (2 * S.T) + S.δ) / S.η
            + Real.sqrt 3 / S.η * X i)) := mul_le_mul_of_nonneg_left htwice (hA i)
        _ = U i * A i + B i * X i := by
          dsimp [U, B]
          ring
    have hsqrt_sq : Real.sqrt (U i * A i) ^ 2 = U i * A i :=
      Real.sq_sqrt (mul_nonneg (hU i) (hA i))
    nlinarith [Real.sqrt_nonneg (U i * A i), hX i, hB i]
  have hAint (i : Fin S.d) : Integrable
      (fun ω => ∑ t ∈ Finset.Icc 1 S.T, adagrad_decorrelated_step S ω t i / 2
        * adagrad_grad_coord S.obj (S.w t ω) i ^ 2) S.μ := by
    refine integrable_finset_sum _ ?_
    intro t ht
    exact (adagrad_per_step_term_integrable S t (Finset.mem_Icc.1 ht).1 i).1
  have hsumAeq :
      (∑ i, A i) =
        ∫ ω, ∑ t ∈ Finset.Icc 1 S.T, ∑ i,
          adagrad_decorrelated_step S ω t i / 2
            * adagrad_grad_coord S.obj (S.w t ω) i ^ 2 ∂S.μ := by
    calc
      (∑ i, A i) = ∫ ω, ∑ i, ∑ t ∈ Finset.Icc 1 S.T,
          adagrad_decorrelated_step S ω t i / 2
            * adagrad_grad_coord S.obj (S.w t ω) i ^ 2 ∂S.μ := by
        rw [integral_finset_sum _ (fun i _ => hAint i)]
      _ = _ := by
        congr 1 with ω
        rw [Finset.sum_comm]
  have hsumA : (∑ i, A i) ≤ adagrad_gradient_budget S c := by
    rw [hsumAeq]
    exact hbudget Ω S
  have hQ : 0 ≤ adagrad_gradient_budget S c :=
    (Finset.sum_nonneg fun i _ => hA i).trans hsumA
  have hsumcoord :
      (∑ i, X i) ≤ (∑ i, B i) + ∑ i, Real.sqrt (U i * A i) := by
    calc
      (∑ i, X i) ≤ ∑ i, (B i + Real.sqrt (U i * A i)) :=
        Finset.sum_le_sum fun i _ => hcoord i
      _ = _ := Finset.sum_add_distrib
  have hroot :
      (∑ i, Real.sqrt (U i * A i))
        ≤ Real.sqrt (∑ i, U i) * Real.sqrt (adagrad_gradient_budget S c) := by
    calc
      (∑ i, Real.sqrt (U i * A i))
          = ∑ i, Real.sqrt (U i) * Real.sqrt (A i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Real.sqrt_mul (hU i)]
      _ ≤ Real.sqrt (∑ i, U i) * Real.sqrt (∑ i, A i) := by
        simpa using Real.sum_sqrt_mul_sqrt_le Finset.univ hU hA
      _ ≤ Real.sqrt (∑ i, U i) * Real.sqrt (adagrad_gradient_budget S c) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsumA) (Real.sqrt_nonneg _)
  have hsigma : (∑ i, S.σ i) = adagrad_l1_norm S.σ := by
    simp [adagrad_l1_norm, abs_of_nonneg (S.sigma_nonneg _)]
  have hsumU :
      (∑ i, U i) =
        2 / S.η * (adagrad_l1_norm S.σ * Real.sqrt (2 * S.T) + S.d * S.δ) := by
    calc
      (∑ i, U i) = 2 / S.η *
          ∑ i, (S.σ i * Real.sqrt (2 * S.T) + S.δ) := by
        simpa [U] using
          (Finset.mul_sum Finset.univ
            (fun i : Fin S.d => S.σ i * Real.sqrt (2 * S.T) + S.δ) (2 / S.η)).symm
      _ = 2 / S.η *
          ((∑ i, S.σ i) * Real.sqrt (2 * S.T) + S.d * S.δ) := by
        congr 1
        rw [Finset.sum_add_distrib]
        congr 1
        · simpa using
            (Finset.sum_mul Finset.univ (fun i : Fin S.d => S.σ i)
              (Real.sqrt (2 * S.T))).symm
        · simp
      _ = _ := by rw [hsigma]
  let D : ℝ := 2 * S.d * S.δ / S.η
  let N : ℝ := 2 / S.η * adagrad_l1_norm S.σ * Real.sqrt (2 * S.T)
  let R : ℝ := adagrad_l1_norm S.σ * adagrad_gradient_budget S c / S.η
  have hl1 : 0 ≤ adagrad_l1_norm S.σ := by
    exact Finset.sum_nonneg fun i _ => abs_nonneg _
  have hD : 0 ≤ D := by
    dsimp [D]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg S.d)) S.delta_pos.le)
      S.eta_pos.le
  have hN : 0 ≤ N := by
    dsimp [N]
    exact mul_nonneg
      (mul_nonneg (div_nonneg (by norm_num) S.eta_pos.le) hl1) (Real.sqrt_nonneg _)
  have hR : 0 ≤ R := by
    dsimp [R]
    exact div_nonneg (mul_nonneg hl1 hQ) S.eta_pos.le
  have hsumU' : (∑ i, U i) = D + N := by
    rw [hsumU]
    dsimp [D, N]
    ring
  have hsqrtadd : Real.sqrt (D + N) ≤ Real.sqrt D + Real.sqrt N := by
    have hDN : 0 ≤ D + N := add_nonneg hD hN
    have h1 := Real.sq_sqrt hDN
    have h2 := Real.sq_sqrt hD
    have h3 := Real.sq_sqrt hN
    have h4 : 0 ≤ Real.sqrt D * Real.sqrt N :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith [Real.sqrt_nonneg (D + N), Real.sqrt_nonneg D, Real.sqrt_nonneg N]
  have hsplit :
      Real.sqrt (∑ i, U i) * Real.sqrt (adagrad_gradient_budget S c)
        ≤ Real.sqrt (D * adagrad_gradient_budget S c)
          + Real.sqrt (N * adagrad_gradient_budget S c) := by
    rw [hsumU']
    calc
      Real.sqrt (D + N) * Real.sqrt (adagrad_gradient_budget S c)
          ≤ (Real.sqrt D + Real.sqrt N) * Real.sqrt (adagrad_gradient_budget S c) :=
        mul_le_mul_of_nonneg_right hsqrtadd (Real.sqrt_nonneg _)
      _ = _ := by
        rw [add_mul, ← Real.sqrt_mul hD, ← Real.sqrt_mul hN]
  have hsqrt2 : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hsqrt2T : Real.sqrt (2 * (S.T : ℝ)) ≤ 2 * Real.sqrt (S.T : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_right hsqrt2 (Real.sqrt_nonneg _)
  have hT : 0 ≤ (S.T : ℝ) := Nat.cast_nonneg S.T
  have hsqrtsqrtT :
      Real.sqrt (Real.sqrt (S.T : ℝ)) = (S.T : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hT]
    congr 1
    norm_num
  have hNQ :
      N * adagrad_gradient_budget S c
        ≤ 4 * R * Real.sqrt (S.T : ℝ) := by
    calc
      N * adagrad_gradient_budget S c
          = (2 / S.η * adagrad_l1_norm S.σ * adagrad_gradient_budget S c)
              * Real.sqrt (2 * (S.T : ℝ)) := by
            dsimp [N]
            ring
      _ ≤ (2 / S.η * adagrad_l1_norm S.σ * adagrad_gradient_budget S c)
              * (2 * Real.sqrt (S.T : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hsqrt2T
              (mul_nonneg
                (mul_nonneg (div_nonneg (by norm_num) S.eta_pos.le) hl1) hQ)
      _ = 4 * R * Real.sqrt (S.T : ℝ) := by
        dsimp [R]
        ring
  have hsqrtnoise :
      Real.sqrt (N * adagrad_gradient_budget S c)
        ≤ 2 * Real.sqrt R * (S.T : ℝ) ^ ((1 : ℝ) / 4) := by
    calc
      Real.sqrt (N * adagrad_gradient_budget S c)
          ≤ Real.sqrt (4 * R * Real.sqrt (S.T : ℝ)) := Real.sqrt_le_sqrt hNQ
      _ = 2 * Real.sqrt R * (S.T : ℝ) ^ ((1 : ℝ) / 4) := by
        rw [show 4 * R * Real.sqrt (S.T : ℝ) = 4 * (R * Real.sqrt (S.T : ℝ)) by ring,
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_mul hR]
        have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
        rw [hsqrt4, hsqrtsqrtT]
        ring
  have hrootfinal :
      (∑ i, Real.sqrt (U i * A i))
        ≤ Real.sqrt (2 * S.d * S.δ * adagrad_gradient_budget S c / S.η)
          + 2 * Real.sqrt R * (S.T : ℝ) ^ ((1 : ℝ) / 4) := by
    calc
      (∑ i, Real.sqrt (U i * A i))
          ≤ Real.sqrt (∑ i, U i) * Real.sqrt (adagrad_gradient_budget S c) := hroot
      _ ≤ Real.sqrt (D * adagrad_gradient_budget S c)
          + Real.sqrt (N * adagrad_gradient_budget S c) := hsplit
      _ ≤ Real.sqrt (2 * S.d * S.δ * adagrad_gradient_budget S c / S.η)
          + 2 * Real.sqrt R * (S.T : ℝ) ^ ((1 : ℝ) / 4) := by
        apply add_le_add
        · rw [show D * adagrad_gradient_budget S c =
              2 * S.d * S.δ * adagrad_gradient_budget S c / S.η by
            dsimp [D]
            ring]
        · exact hsqrtnoise
  have hsumB :
      (∑ i, B i) ≤ 2 * Real.sqrt 3 / S.η * adagrad_gradient_budget S c := by
    calc
      (∑ i, B i) = 2 * Real.sqrt 3 / S.η * ∑ i, A i := by
        simpa [B] using
          (Finset.mul_sum Finset.univ (fun i : Fin S.d => A i)
            (2 * Real.sqrt 3 / S.η)).symm
      _ ≤ 2 * Real.sqrt 3 / S.η * adagrad_gradient_budget S c :=
        mul_le_mul_of_nonneg_left hsumA
          (div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) S.eta_pos.le)
  calc
    (∑ i, ∫ ω, Real.sqrt (∑ t ∈ Finset.Icc 1 S.T,
        adagrad_grad_coord S.obj (S.w t ω) i ^ 2) ∂S.μ)
        = ∑ i, X i := rfl
    _ ≤ (∑ i, B i) + ∑ i, Real.sqrt (U i * A i) := hsumcoord
    _ ≤ 2 * Real.sqrt 3 / S.η * adagrad_gradient_budget S c
        + (Real.sqrt (2 * S.d * S.δ * adagrad_gradient_budget S c / S.η)
          + 2 * Real.sqrt R * (S.T : ℝ) ^ ((1 : ℝ) / 4)) :=
      add_le_add hsumB hrootfinal
    _ = _ := by
      dsimp [R]
      ring

@[blueprint "lem:adagrad-avg-l1-coord-cauchy-schwarz"
  (statement := /-- Let $T \in \mathbb{N}$ and let $f : \mathbb{N} \to \mathbb{R}$. Then
    $$\sum_{t=1}^T |f(t)| \le \sqrt{T} \sqrt{\sum_{t=1}^T f(t)^2},$$
    both sums being taken over the finite index set $\{1, \dots, T\}$, which is empty when
    $T = 0$. -/)
  (proof := /-- Write $I = \{1, \dots, T\}$, so that $|I| = T$. The Cauchy--Schwarz
    inequality applied to the family $(|f(t)|)_{t \in I}$ and the constant family
    $(1)_{t \in I}$ states that
    $$\Bigl(\sum_{t \in I} |f(t)|\Bigr)^2 \le |I| \sum_{t \in I} |f(t)|^2 .$$
    Since $|f(t)|^2 = f(t)^2$ for every $t$ and $|I| = T$, this reads
    $$\Bigl(\sum_{t \in I} |f(t)|\Bigr)^2 \le T \sum_{t \in I} f(t)^2 .$$
    The sum $\sum_{t \in I} |f(t)|$ is nonnegative, being a finite sum of absolute values,
    hence it equals the square root of its own square. Since the square root is monotone
    on $[0, \infty)$, the displayed inequality gives
    $$\sum_{t \in I} |f(t)|
      = \sqrt{\Bigl(\sum_{t \in I} |f(t)|\Bigr)^2}
      \le \sqrt{T \sum_{t \in I} f(t)^2}.$$
    Finally $T \ge 0$, so $\sqrt{T \cdot s} = \sqrt{T}\sqrt{s}$ with
    $s = \sum_{t \in I} f(t)^2$, which yields the assertion. -/)
  (title := /-- Coordinatewise Cauchy--Schwarz bound for a sum of absolute values -/)
  (latexEnv := "lemma")]
lemma adagrad_avg_l1_coord_cauchy_schwarz {T : ℕ} (f : ℕ → ℝ) :
    ∑ t ∈ Finset.Icc 1 T, |f t|
      ≤ Real.sqrt T * Real.sqrt (∑ t ∈ Finset.Icc 1 T, f t ^ 2) := by
  have hcard : ((Finset.Icc 1 T).card : ℝ) = T := by
    simp
  have hnonneg : (0 : ℝ) ≤ ∑ t ∈ Finset.Icc 1 T, |f t| :=
    Finset.sum_nonneg fun t _ => abs_nonneg _
  have hkey : (∑ t ∈ Finset.Icc 1 T, |f t|) ^ 2
      ≤ (T : ℝ) * ∑ t ∈ Finset.Icc 1 T, f t ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.Icc 1 T) (f := fun t => |f t|)
    simpa [hcard, sq_abs] using h
  calc ∑ t ∈ Finset.Icc 1 T, |f t|
      = Real.sqrt ((∑ t ∈ Finset.Icc 1 T, |f t|) ^ 2) := (Real.sqrt_sq hnonneg).symm
    _ ≤ Real.sqrt ((T : ℝ) * ∑ t ∈ Finset.Icc 1 T, f t ^ 2) := Real.sqrt_le_sqrt hkey
    _ = Real.sqrt T * Real.sqrt (∑ t ∈ Finset.Icc 1 T, f t ^ 2) :=
        Real.sqrt_mul (Nat.cast_nonneg T) _

@[blueprint "lem:adagrad-avg-l1-sum-le-sqrt-mul"
  (statement := /-- Let $d, T \in \mathbb{N}$ and let $a : \mathbb{N} \times [d] \to
    \mathbb{R}$ be arbitrary, written $a_{t,i} = a(t, i)$. Then
    $$\sum_{t=1}^T \|a_t\|_1
      \le \sqrt{T} \sum_{i=1}^d \sqrt{\sum_{t=1}^T a_{t,i}^2},$$
    where $a_t = (a_{t,1}, \dots, a_{t,d}) \in \mathbb{R}^d$ and $\|\cdot\|_1$ is the
    $\ell_1$-norm of \cref{def:adagrad-l1-norm}. -/)
  (proof := /-- By \cref{def:adagrad-l1-norm} we have
    $\|a_t\|_1 = \sum_{i=1}^d |a_{t,i}|$, so the left-hand side is the finite double sum
    $\sum_{t=1}^T \sum_{i=1}^d |a_{t,i}|$. Both index sets $\{1, \dots, T\}$ and $[d]$
    are finite, so the order of summation may be interchanged, giving
    $$\sum_{t=1}^T \|a_t\|_1 = \sum_{i=1}^d \sum_{t=1}^T |a_{t,i}| .$$
    For each fixed $i \in [d]$, \cref{lem:adagrad-avg-l1-coord-cauchy-schwarz} applied to
    the function $t \mapsto a_{t,i}$ gives
    $$\sum_{t=1}^T |a_{t,i}| \le \sqrt{T} \sqrt{\sum_{t=1}^T a_{t,i}^2}.$$
    Summing these $d$ inequalities over $i \in [d]$ and taking the factor $\sqrt{T}$ out
    of the resulting sum yields the assertion. -/)
  (title := /-- Summed $\ell_1$-norms versus root sums of squares -/)
  (latexEnv := "lemma")]
lemma adagrad_avg_l1_sum_le_sqrt_mul {d T : ℕ} (a : ℕ → Fin d → ℝ) :
    ∑ t ∈ Finset.Icc 1 T, adagrad_l1_norm (fun i => a t i)
      ≤ Real.sqrt T * ∑ i, Real.sqrt (∑ t ∈ Finset.Icc 1 T, a t i ^ 2) := by
  have hswap : ∑ t ∈ Finset.Icc 1 T, adagrad_l1_norm (fun i => a t i)
      = ∑ i, ∑ t ∈ Finset.Icc 1 T, |a t i| := by
    simp only [adagrad_l1_norm]
    exact Finset.sum_comm
  rw [hswap, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => adagrad_avg_l1_coord_cauchy_schwarz (fun t => a t i)

@[blueprint "lem:adagrad-average-l1-le-sqrt-sum-sq"
  (statement := /-- Let $d, T \in \mathbb{N}$ with $T \ge 1$ and let
    $a : \mathbb{N} \times [d] \to \mathbb{R}$ be arbitrary, written
    $a_{t,i} = a(t, i)$. Then
    $$\frac{1}{T} \sum_{t=1}^T \|a_t\|_1
      \le \frac{1}{\sqrt{T}} \sum_{i=1}^d \sqrt{\sum_{t=1}^T a_{t,i}^2},$$
    where $a_t = (a_{t,1}, \dots, a_{t,d}) \in \mathbb{R}^d$ and
    $\|a_t\|_1 = \sum_{i=1}^d |a_{t,i}|$ is the $\ell_1$-norm of
    \cref{def:adagrad-l1-norm}, so that the left-hand side is the average over
    $t \in \{1, \dots, T\}$ of the $\ell_1$-norms of the vectors $a_t$. -/)
  (proof := /-- Since $T \ge 1$ we have $T > 0$ as a real number, and hence
    $\sqrt{T} > 0$ because the square root is strictly positive on $(0, \infty)$.

    By \cref{lem:adagrad-avg-l1-sum-le-sqrt-mul},
    $$\sum_{t=1}^T \|a_t\|_1
      \le \sqrt{T} \sum_{i=1}^d \sqrt{\sum_{t=1}^T a_{t,i}^2}.$$
    Multiplying this inequality by the nonnegative factor $1/T$ preserves it, so
    $$\frac{1}{T} \sum_{t=1}^T \|a_t\|_1
      \le \frac{1}{T}\Bigl(\sqrt{T} \sum_{i=1}^d \sqrt{\sum_{t=1}^T a_{t,i}^2}\Bigr)
      = \Bigl(\frac{\sqrt{T}}{T}\Bigr) \sum_{i=1}^d \sqrt{\sum_{t=1}^T a_{t,i}^2},$$
    the last equality being associativity and commutativity of multiplication.

    Finally $\frac{\sqrt{T}}{T} = \frac{1}{\sqrt{T}}$: since $\sqrt{T} \neq 0$, this
    identity is equivalent to $\frac{1}{T}\sqrt{T}\sqrt{T} = 1$, which holds because
    $\sqrt{T}\sqrt{T} = T$ for $T \ge 0$ and $T \neq 0$. Substituting this identity into
    the previous display yields the assertion. -/)
  (title := /-- Time-averaged $\ell_1$-norm versus root sums of squares -/)
  (latexEnv := "lemma")]
lemma adagrad_average_l1_le_sqrt_sum_sq {d T : ℕ} (hT : 1 ≤ T) (a : ℕ → Fin d → ℝ) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, adagrad_l1_norm (fun i => a t i)
      ≤ (1 / Real.sqrt T) * ∑ i, Real.sqrt (∑ t ∈ Finset.Icc 1 T, a t i ^ 2) := by
  have hT0 : (0 : ℝ) < T := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hT
  have hs0 : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
  have hsum := adagrad_avg_l1_sum_le_sqrt_mul (d := d) (T := T) a
  have hmul : (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, adagrad_l1_norm (fun i => a t i)
      ≤ (1 / (T : ℝ)) * (Real.sqrt T * ∑ i, Real.sqrt (∑ t ∈ Finset.Icc 1 T, a t i ^ 2)) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  have hcoeff : (1 / (T : ℝ)) * Real.sqrt T = 1 / Real.sqrt T := by
    rw [eq_div_iff hs0.ne', mul_assoc, Real.mul_self_sqrt hT0.le, one_div,
      inv_mul_cancel₀ hT0.ne']
  calc (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, adagrad_l1_norm (fun i => a t i)
      ≤ (1 / (T : ℝ))
          * (Real.sqrt T * ∑ i, Real.sqrt (∑ t ∈ Finset.Icc 1 T, a t i ^ 2)) := hmul
    _ = ((1 / (T : ℝ)) * Real.sqrt T)
          * ∑ i, Real.sqrt (∑ t ∈ Finset.Icc 1 T, a t i ^ 2) := by ring
    _ = (1 / Real.sqrt T) * ∑ i, Real.sqrt (∑ t ∈ Finset.Icc 1 T, a t i ^ 2) := by
        rw [hcoeff]

@[blueprint "lem:adagrad-coord-sqrt-budget-split"
  (statement := /-- Let $D,e,l,s,\Lambda\in\mathbb R$ satisfy
    $D,l,s,\Lambda\ge0$ and $e>0$. Then
    $$\sqrt{\frac{s}{e}\left(D+
      \left(2es+\frac{e^2l}{2}\right)\Lambda\right)}
      \le \frac{\sqrt{sD}}{\sqrt e}
        +\sqrt2\,s\sqrt\Lambda
        +\sqrt{\frac12}\sqrt{esl\Lambda}.$$ -/)
  (proof := /-- Split the radicand into the three nonnegative terms
    $sD/e$, $2s^2\Lambda$, and $esl\Lambda/2$. Applying
    \cref{lem:adagrad-etahat-sqrt-add-le} twice bounds the square root of their
    sum by the sum of their square roots. The three identities
    $$\sqrt{sD/e}=\frac{\sqrt{sD}}{\sqrt e},\qquad
      \sqrt{2s^2\Lambda}=\sqrt2\,s\sqrt\Lambda,\qquad
      \sqrt{esl\Lambda/2}=\sqrt{1/2}\sqrt{esl\Lambda}$$
    follow from $e>0$, $s\ge0$, and multiplicativity of the square root on
    nonnegative factors. Substitution gives the claimed inequality. -/)
  (title := /-- Square-root decomposition of the AdaGrad budget -/)
  (latexEnv := "lemma")]
lemma adagrad_coord_sqrt_budget_split {D e l s Λ : ℝ}
    (hD : 0 ≤ D) (he : 0 < e) (hl : 0 ≤ l) (hs : 0 ≤ s) (hΛ : 0 ≤ Λ) :
    Real.sqrt (s * (D + (2 * e * s + e ^ 2 * l / 2) * Λ) / e)
      ≤ Real.sqrt (s * D) / Real.sqrt e
        + Real.sqrt 2 * (s * Real.sqrt Λ)
        + Real.sqrt (1 / 2 : ℝ) * Real.sqrt (e * s * l * Λ) := by
  have hx : 0 ≤ s * D / e := div_nonneg (mul_nonneg hs hD) he.le
  have hy : 0 ≤ 2 * (s ^ 2 * Λ) :=
    mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) hΛ)
  have hz : 0 ≤ e * s * l * Λ / 2 :=
    div_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg he.le hs) hl) hΛ) (by norm_num)
  have hcoefexpand :
      s * ((2 * e * s + e ^ 2 * l / 2) * Λ) / e
        = 2 * (s ^ 2 * Λ) + e * s * l * Λ / 2 := by
    apply (div_eq_iff he.ne').2
    ring
  have hrad : s * (D + (2 * e * s + e ^ 2 * l / 2) * Λ) / e
      = s * D / e + 2 * (s ^ 2 * Λ) + e * s * l * Λ / 2 := by
    rw [mul_add, add_div, hcoefexpand]
    ring
  have hsplit :
      Real.sqrt (s * D / e + 2 * (s ^ 2 * Λ) + e * s * l * Λ / 2)
        ≤ Real.sqrt (s * D / e) + Real.sqrt (2 * (s ^ 2 * Λ))
          + Real.sqrt (e * s * l * Λ / 2) := by
    calc
      Real.sqrt (s * D / e + 2 * (s ^ 2 * Λ) + e * s * l * Λ / 2)
          ≤ Real.sqrt (s * D / e + 2 * (s ^ 2 * Λ))
              + Real.sqrt (e * s * l * Λ / 2) :=
        adagrad_etahat_sqrt_add_le (add_nonneg hx hy) hz
      _ ≤ (Real.sqrt (s * D / e) + Real.sqrt (2 * (s ^ 2 * Λ)))
              + Real.sqrt (e * s * l * Λ / 2) :=
        add_le_add (adagrad_etahat_sqrt_add_le hx hy) le_rfl
  have hxroot : Real.sqrt (s * D / e) = Real.sqrt (s * D) / Real.sqrt e :=
    Real.sqrt_div (mul_nonneg hs hD) e
  have hsroot : Real.sqrt (s ^ 2) = s := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hs]
  have hyroot : Real.sqrt (2 * (s ^ 2 * Λ))
      = Real.sqrt 2 * (s * Real.sqrt Λ) := by
    calc
      Real.sqrt (2 * (s ^ 2 * Λ))
          = Real.sqrt 2 * Real.sqrt (s ^ 2 * Λ) :=
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) _
      _ = Real.sqrt 2 * (Real.sqrt (s ^ 2) * Real.sqrt Λ) :=
        congrArg (fun x : ℝ => Real.sqrt 2 * x) (Real.sqrt_mul (sq_nonneg s) Λ)
      _ = Real.sqrt 2 * (s * Real.sqrt Λ) := by rw [hsroot]
  have hzarg : e * s * l * Λ / 2 = (1 / 2 : ℝ) * (e * s * l * Λ) := by ring
  have hzroot : Real.sqrt (e * s * l * Λ / 2)
      = Real.sqrt (1 / 2 : ℝ) * Real.sqrt (e * s * l * Λ) := by
    rw [hzarg]
    exact Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ)) _
  rw [hrad]
  exact hsplit.trans_eq (by rw [hxroot, hyroot, hzroot])

@[blueprint "lem:adagrad-coord-weighted-rate-le"
  (statement := /-- For nonnegative real numbers $r_1,\ldots,r_5$,
    $$2\left(r_3+\sqrt2\,r_5+\sqrt{\frac12}\,r_4\right)
      \le 2\left(1+\sqrt2+\sqrt{\frac12}\right)
        (r_1+r_2+r_3+r_4+r_5).$$ -/)
  (proof := /-- Each of $r_3,r_4,r_5$ is bounded above by the nonnegative sum
    $R=r_1+r_2+r_3+r_4+r_5$. Multiplication by the nonnegative coefficients
    $1$, $\sqrt2$, and $\sqrt{1/2}$ preserves these inequalities. Adding them and
    multiplying by $2$ gives the displayed bound after distributing the common
    factor $R$. -/)
  (title := /-- Weighted rate terms are controlled by their sum -/)
  (latexEnv := "lemma")]
lemma adagrad_coord_weighted_rate_le {r₁ r₂ r₃ r₄ r₅ : ℝ}
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hr₃ : 0 ≤ r₃)
    (hr₄ : 0 ≤ r₄) (hr₅ : 0 ≤ r₅) :
    2 * (r₃ + Real.sqrt 2 * r₅ + Real.sqrt (1 / 2 : ℝ) * r₄)
      ≤ 2 * (1 + Real.sqrt 2 + Real.sqrt (1 / 2 : ℝ))
        * (r₁ + r₂ + r₃ + r₄ + r₅) := by
  let R : ℝ := r₁ + r₂ + r₃ + r₄ + r₅
  have hr₃R : r₃ ≤ R := by dsimp [R]; linarith
  have hr₄R : r₄ ≤ R := by dsimp [R]; linarith
  have hr₅R : r₅ ≤ R := by dsimp [R]; linarith
  have hsum :
      r₃ + Real.sqrt 2 * r₅ + Real.sqrt (1 / 2 : ℝ) * r₄
        ≤ R + Real.sqrt 2 * R + Real.sqrt (1 / 2 : ℝ) * R :=
    add_le_add
      (add_le_add hr₃R
        (mul_le_mul_of_nonneg_left hr₅R (Real.sqrt_nonneg _)))
      (mul_le_mul_of_nonneg_left hr₄R (Real.sqrt_nonneg _))
  dsimp [R] at hsum ⊢
  nlinarith

@[blueprint "lem:adagrad-coord-source-normalize"
  (statement := /-- If $u\in\mathbb R$ is nonzero, then for all
    $a,q,b,d\in\mathbb R$,
    $$\frac{1}{u^2}(aq+b+2du)
      =a\frac{q}{u^2}+\frac{b}{u^2}+2\frac{d}{u}.$$ -/)
  (proof := /-- Multiply both sides by the nonzero quantity $u^2$. The resulting
    identity is $aq+b+2du=aq+b+2du$, so division by $u^2$ gives the claim. -/)
  (title := /-- Normalisation by the squared fourth-root scale -/)
  (latexEnv := "lemma")]
lemma adagrad_coord_source_normalize {u a q b d : ℝ} (hu : u ≠ 0) :
    (1 / u ^ 2) * (a * q + b + 2 * d * u)
      = a * (q / u ^ 2) + b / u ^ 2 + 2 * d / u := by
  field_simp [hu]

@[blueprint "lem:adagrad-coord-stationarity-source-bound"
  (statement := /-- Let $S$ be an AdaGrad setting and let $c_0,c\in\mathbb R$.
    Suppose that $Q_{c_0}(S)\le Q_c(S)$ and that
    $$\sum_i\mathbb E\sqrt{\sum_{t=1}^T\nabla_iF(\mathbf w_t)^2}
      \le \frac{2\sqrt3}{\eta}Q_{c_0}(S)
        +\sqrt{\frac{2d\delta Q_{c_0}(S)}{\eta}}
        +2T^{1/4}\sqrt{\frac{\|\bm\sigma\|_1Q_{c_0}(S)}{\eta}}.$$
    Then the stationarity measure satisfies the same bound with $Q_c(S)$,
    multiplied by $1/\sqrt T$. -/)
  (proof := /-- By \cref{lem:adagrad-cs-grad-memlp}, every gradient coordinate
    along the trajectory is integrable. The summed squared coordinates are integrable
    by \cref{lem:adagrad-cs-gradsum-integrable}, and their square roots are integrable
    by \cref{lem:adagrad-cs-memlp-sqrt}. Hence
    \cref{lem:adagrad-average-l1-le-sqrt-sum-sq} may be integrated pointwise, giving
    the stationarity measure at most $1/\sqrt T$ times the displayed coordinate sum.
    Each of the three summands in the assumed estimate is monotone in the nonnegative
    budget $Q$: the first by multiplication with a nonnegative coefficient, and the
    latter two by monotonicity of the square root. Replacing $Q_{c_0}(S)$ by $Q_c(S)$
    and composing the two inequalities proves the claim. -/)
  (title := /-- Stationarity from the coordinate root-sum estimate -/)
  (latexEnv := "lemma")]
lemma adagrad_coord_stationarity_source_bound {Ω : Type} [MeasurableSpace Ω]
    (S : adagrad_setting Ω) {c₀ c : ℝ}
    (hQmono : adagrad_gradient_budget S c₀ ≤ adagrad_gradient_budget S c)
    (hbound :
      (∑ i, ∫ ω, Real.sqrt (∑ t ∈ Finset.Icc 1 S.T,
          adagrad_grad_coord S.obj (S.w t ω) i ^ 2) ∂S.μ)
        ≤ 2 * Real.sqrt 3 / S.η * adagrad_gradient_budget S c₀
          + Real.sqrt (2 * S.d * S.δ * adagrad_gradient_budget S c₀ / S.η)
          + 2 * Real.sqrt (adagrad_l1_norm S.σ
              * adagrad_gradient_budget S c₀ / S.η)
            * (S.T : ℝ) ^ ((1 : ℝ) / 4)) :
    adagrad_stationarity S
      ≤ (1 / Real.sqrt S.T)
        * (2 * Real.sqrt 3 / S.η * adagrad_gradient_budget S c
          + Real.sqrt (2 * S.d * S.δ * adagrad_gradient_budget S c / S.η)
          + 2 * Real.sqrt (adagrad_l1_norm S.σ
              * adagrad_gradient_budget S c / S.η)
            * (S.T : ℝ) ^ ((1 : ℝ) / 4)) := by
  haveI := S.isProbabilityMeasure
  have hgradint (t : ℕ) (ht : t ∈ Finset.Icc 1 S.T) (i : Fin S.d) :
      Integrable (fun ω => adagrad_grad_coord S.obj (S.w t ω) i) S.μ :=
    (adagrad_cs_grad_memlp S i t (Finset.mem_Icc.1 ht).1).integrable one_le_two
  have hl1int (t : ℕ) (ht : t ∈ Finset.Icc 1 S.T) :
      Integrable (fun ω => adagrad_l1_norm
        (fun i => adagrad_grad_coord S.obj (S.w t ω) i)) S.μ := by
    simp only [adagrad_l1_norm]
    exact integrable_finset_sum _ fun i _ => (hgradint t ht i).abs
  have havgint : Integrable (fun ω => (1 / (S.T : ℝ))
      * ∑ t ∈ Finset.Icc 1 S.T, adagrad_l1_norm
        (fun i => adagrad_grad_coord S.obj (S.w t ω) i)) S.μ :=
    (integrable_finset_sum _ hl1int).const_mul _
  have hrootint (i : Fin S.d) : Integrable (fun ω =>
      Real.sqrt (∑ t ∈ Finset.Icc 1 S.T,
        adagrad_grad_coord S.obj (S.w t ω) i ^ 2)) S.μ :=
    (adagrad_cs_memlp_sqrt S.μ _
      (Filter.Eventually.of_forall fun ω => Finset.sum_nonneg fun t _ => sq_nonneg _)
      (adagrad_cs_gradsum_integrable S i)).integrable one_le_two
  have hrootssum : Integrable (fun ω => ∑ i, Real.sqrt
      (∑ t ∈ Finset.Icc 1 S.T,
        adagrad_grad_coord S.obj (S.w t ω) i ^ 2)) S.μ :=
    integrable_finset_sum _ fun i _ => hrootint i
  have hrightint : Integrable (fun ω => (1 / Real.sqrt S.T) * ∑ i,
      Real.sqrt (∑ t ∈ Finset.Icc 1 S.T,
        adagrad_grad_coord S.obj (S.w t ω) i ^ 2)) S.μ :=
    hrootssum.const_mul _
  have hpoint (ω : Ω) := adagrad_average_l1_le_sqrt_sum_sq S.one_le_T
    (fun t i => adagrad_grad_coord S.obj (S.w t ω) i)
  have hstat : adagrad_stationarity S
      ≤ (1 / Real.sqrt S.T) * ∑ i, ∫ ω,
          Real.sqrt (∑ t ∈ Finset.Icc 1 S.T,
            adagrad_grad_coord S.obj (S.w t ω) i ^ 2) ∂S.μ := by
    unfold adagrad_stationarity
    calc
      ∫ ω, (1 / (S.T : ℝ)) * ∑ t ∈ Finset.Icc 1 S.T,
          adagrad_l1_norm
            (fun i => adagrad_grad_coord S.obj (S.w t ω) i) ∂S.μ
          ≤ ∫ ω, (1 / Real.sqrt S.T) * ∑ i,
              Real.sqrt (∑ t ∈ Finset.Icc 1 S.T,
                adagrad_grad_coord S.obj (S.w t ω) i ^ 2) ∂S.μ :=
        integral_mono havgint hrightint hpoint
      _ = (1 / Real.sqrt S.T) * ∑ i, ∫ ω,
            Real.sqrt (∑ t ∈ Finset.Icc 1 S.T,
              adagrad_grad_coord S.obj (S.w t ω) i ^ 2) ∂S.μ := by
        rw [integral_const_mul, integral_finset_sum _ (fun i _ => hrootint i)]
  have hσnonneg : 0 ≤ adagrad_l1_norm S.σ :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  have hfirst : 2 * Real.sqrt 3 / S.η * adagrad_gradient_budget S c₀
      ≤ 2 * Real.sqrt 3 / S.η * adagrad_gradient_budget S c :=
    mul_le_mul_of_nonneg_left hQmono
      (div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg 3)) S.eta_pos.le)
  have hsecond : Real.sqrt (2 * S.d * S.δ
        * adagrad_gradient_budget S c₀ / S.η)
      ≤ Real.sqrt (2 * S.d * S.δ
        * adagrad_gradient_budget S c / S.η) := by
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hQmono
        (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg S.d)) S.delta_pos.le))
      S.eta_pos.le
  have hthird : 2 * Real.sqrt (adagrad_l1_norm S.σ
        * adagrad_gradient_budget S c₀ / S.η) * (S.T : ℝ) ^ ((1 : ℝ) / 4)
      ≤ 2 * Real.sqrt (adagrad_l1_norm S.σ
        * adagrad_gradient_budget S c / S.η) * (S.T : ℝ) ^ ((1 : ℝ) / 4) := by
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hQmono hσnonneg) S.eta_pos.le
  have hparent :
      (∑ i, ∫ ω, Real.sqrt (∑ t ∈ Finset.Icc 1 S.T,
          adagrad_grad_coord S.obj (S.w t ω) i ^ 2) ∂S.μ)
        ≤ 2 * Real.sqrt 3 / S.η * adagrad_gradient_budget S c
          + Real.sqrt (2 * S.d * S.δ * adagrad_gradient_budget S c / S.η)
          + 2 * Real.sqrt (adagrad_l1_norm S.σ
              * adagrad_gradient_budget S c / S.η)
            * (S.T : ℝ) ^ ((1 : ℝ) / 4) := by
    exact hbound.trans (add_le_add (add_le_add hfirst hsecond) hthird)
  exact hstat.trans (mul_le_mul_of_nonneg_left hparent (by positivity))

@[blueprint "thm:adagrad-coord-main-result"
  (statement := /-- There is an absolute constant $c \ge 1$ with the following property.
    Let $\{S_n\}_{n\ge0}$ be a family of AdaGrad settings as in
    \cref{def:adagrad-setting}, with horizon $T_n=n+1$. Assume that the dimension $d$, the
    step size $\eta$, the stability parameter $\delta$, the initial gap $\Delta_F$, the
    $\ell_1$- and $\ell_\infty$-norms of $\mathbf L$ and $\bm\sigma$, and the
    $\ell_\infty$-norm of the initial gradient are independent of $n$. Thus all scalar
    problem data entering the rate are fixed while $T_n\to\infty$. Then, with the
    big-$O$ constant allowed to depend on these fixed data,
    $$\left\{
      \mathbb{E}\Bigl[\frac{1}{T_n}\sum_{t=1}^{T_n}
        \|\nabla F_n(\mathbf{w}_{n,t})\|_1\Bigr]\right\}_{n\ge0}
      = O\left(\left\{
        \frac{\Delta_F}{\eta \sqrt{T_n}}
      + \frac{\eta \|\mathbf{L}\|_1 \Lambda_c(S_n)}{\sqrt{T_n}}
      + \frac{\sqrt{\|\bm\sigma\|_1 \Delta_F}}{\sqrt{\eta}\, T_n^{1/4}}
      + \frac{\sqrt{\eta \|\bm\sigma\|_1 \|\mathbf{L}\|_1
          \Lambda_c(S_n)}}{T_n^{1/4}}
      + \frac{\|\bm\sigma\|_1 \sqrt{\Lambda_c(S_n)}}{T_n^{1/4}}
      \right\}_{n\ge0}\right),$$
    where $\Delta_F = F_n(\mathbf{w}_{n,1})-F_n^*$ is the gap of
    \cref{def:adagrad-gap}, and
    $\Lambda_c(S_n)=\log\bigl(c(1+h(S_n))\bigr)$ is the logarithmic budget of
    \cref{def:adagrad-log-budget}, with $h$ as in \cref{def:adagrad-h}. The norms are
    those of \cref{def:adagrad-l1-norm} and \cref{def:adagrad-linf-norm}. Equivalently,
    the left-hand sequence is
    $O\bigl(R_n\bigr)$ along the filter at infinity, where $R_n$ is the displayed
    five-term rate. -/)
  (proof := /-- Choose the absolute constant $c\ge1$ furnished by
    \cref{lem:adagrad-bound-on-sum-sqrt}, and fix a family $\{S_n\}_{n\ge0}$ satisfying
    the stated constancy hypotheses. Write $\Delta_F$, $\Lambda_n$ and $Q_n$ for the
    quantities of
    \cref{def:adagrad-gap}, \cref{def:adagrad-log-budget} and
    \cref{def:adagrad-gradient-budget} evaluated at $S_n$ and $c$.

    The estimate \cref{lem:adagrad-bound-on-sum-sqrt}, together with
    \cref{lem:adagrad-coord-stationarity-source-bound}, yields
    $$\mathop{\rm Stat}(S_n)\le
      \frac{2\sqrt3}{\eta\sqrt{T_n}}Q_n
      +\frac1{\sqrt{T_n}}\sqrt{\frac{2d\delta Q_n}{\eta}}
      +\frac2{T_n^{1/4}}\sqrt{\frac{\|\bm\sigma\|_1Q_n}{\eta}}.$$
    Here
    $$Q_n=\Delta_F+
      \left(2\eta\|\bm\sigma\|_1+
        \frac{\eta^2\|\mathbf L\|_1}{2}\right)\Lambda_n.$$
    All coefficients in this identity are independent of $n$ and nonnegative.

    By the definition of \cref{def:adagrad-h} and the constancy hypotheses, $h(S_n)$ is
    a polynomial of degree at most three in $T_n=n+1$, divided by the fixed positive
    number $\delta^2$. Consequently
    $\Lambda_n=\log(c(1+h(S_n)))=O(\log(n+2))$, and hence
    $\Lambda_n=O(\sqrt{T_n})$. It follows that
    $\|\bm\sigma\|_1\Lambda_n/\sqrt{T_n}$ is bounded by a fixed multiple of
    $\|\bm\sigma\|_1\sqrt{\Lambda_n}/T_n^{1/4}$ for all sufficiently large $n$.

    Put $u_n=T_n^{1/4}$ and let $R_n$ be the displayed five-term rate. The preceding
    logarithmic estimate implies
    $$\frac{Q_n}{u_n^2}\le C_1R_n$$
    for a constant $C_1$ depending only on the fixed data. If
    $q_0=\Delta_F+2\eta\|\bm\sigma\|_1+
    \eta^2\|\mathbf L\|_1/2$, then $q_0\le Q_n$. When $q_0>0$ this gives
    $\sqrt{Q_n}\le Q_n/\sqrt{q_0}$; when $q_0=0$, all three nonnegative summands
    defining $q_0$ vanish and the same comparison follows directly. Thus the first two
    terms on the right-hand side are bounded by a fixed multiple of $R_n$. The algebraic
    rearrangement used here is exactly
    \cref{lem:adagrad-coord-source-normalize}.

    For the remaining square-root term,
    \cref{lem:adagrad-coord-sqrt-budget-split} gives
    $$\sqrt{\frac{\|\bm\sigma\|_1Q_n}{\eta}}
      \le \frac{\sqrt{\|\bm\sigma\|_1\Delta_F}}{\sqrt\eta}
        +\sqrt2\,\|\bm\sigma\|_1\sqrt{\Lambda_n}
        +\sqrt{\frac12}
          \sqrt{\eta\|\bm\sigma\|_1\|\mathbf L\|_1\Lambda_n}.$$
    After division by $u_n$, these are respectively the third, fifth, and fourth
    rate terms. Their weighted sum is bounded by a fixed multiple of $R_n$ by
    \cref{lem:adagrad-coord-weighted-rate-le}. Combining the three source-term
    comparisons supplies one constant valid eventually in $n$, which is precisely the
    asserted big-$O$ relation. -/)
  (title := /-- Convergence of coordinate-wise AdaGrad in the $\ell_1$ stationarity
    measure -/)
  (latexEnv := "theorem")]
theorem adagrad_coord_main_result :
    ∃ c : ℝ, 1 ≤ c ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : ℕ → adagrad_setting Ω),
        (∀ n, (S n).T = n + 1) →
        (∀ n, (S n).d = (S 0).d) →
        (∀ n, (S n).η = (S 0).η) →
        (∀ n, (S n).δ = (S 0).δ) →
        (∀ n, adagrad_gap (S n) = adagrad_gap (S 0)) →
        (∀ n, adagrad_l1_norm (S n).L = adagrad_l1_norm (S 0).L) →
        (∀ n, adagrad_linf_norm (S n).L = adagrad_linf_norm (S 0).L) →
        (∀ n, adagrad_l1_norm (S n).σ = adagrad_l1_norm (S 0).σ) →
        (∀ n, adagrad_linf_norm (S n).σ = adagrad_linf_norm (S 0).σ) →
        (∀ n, adagrad_linf_norm
          (fun i => adagrad_grad_coord (S n).obj (S n).init i)
            = adagrad_linf_norm
              (fun i => adagrad_grad_coord (S 0).obj (S 0).init i)) →
        Asymptotics.IsBigO Filter.atTop
          (fun n => adagrad_stationarity (S n))
          (fun n =>
            adagrad_gap (S n) / ((S n).η * Real.sqrt (S n).T)
              + (S n).η * adagrad_l1_norm (S n).L * adagrad_log_budget (S n) c
                  / Real.sqrt (S n).T
              + Real.sqrt (adagrad_l1_norm (S n).σ * adagrad_gap (S n))
                  / (Real.sqrt (S n).η * ((S n).T : ℝ) ^ ((1 : ℝ) / 4))
              + Real.sqrt ((S n).η * adagrad_l1_norm (S n).σ
                  * adagrad_l1_norm (S n).L * adagrad_log_budget (S n) c)
                    / ((S n).T : ℝ) ^ ((1 : ℝ) / 4)
              + adagrad_l1_norm (S n).σ * Real.sqrt (adagrad_log_budget (S n) c)
                  / ((S n).T : ℝ) ^ ((1 : ℝ) / 4)) := by
  obtain ⟨c₀, hc₀, hbound₀⟩ := adagrad_bound_on_sum_sqrt
  let c : ℝ := max c₀ (Real.exp 1)
  have hc : 1 ≤ c := le_trans hc₀ (le_max_left _ _)
  refine ⟨c, hc, ?_⟩
  intro Ω _ S hT hd hη hδ hgap hL1 hLinf hσ1 hσinf hgradinf
  have hstatnonneg (n : ℕ) : 0 ≤ adagrad_stationarity (S n) := by
    unfold adagrad_stationarity
    apply integral_nonneg
    intro ω
    apply mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg _))
    apply Finset.sum_nonneg
    intro t htmem
    unfold adagrad_l1_norm
    exact Finset.sum_nonneg fun i _ => abs_nonneg _
  have hL1nonneg (n : ℕ) : 0 ≤ adagrad_l1_norm (S n).L := by
    exact Finset.sum_nonneg fun i _ => abs_nonneg _
  have hσ1nonneg (n : ℕ) : 0 ≤ adagrad_l1_norm (S n).σ := by
    exact Finset.sum_nonneg fun i _ => abs_nonneg _
  have hLinfnonneg (n : ℕ) : 0 ≤ adagrad_linf_norm (S n).L := by
    let i : Fin (S n).d := ⟨0, (S n).one_le_d⟩
    exact le_trans (abs_nonneg ((S n).L i)) (Finite.le_ciSup (fun j => |(S n).L j|) i)
  have hσinfnonneg (n : ℕ) : 0 ≤ adagrad_linf_norm (S n).σ := by
    let i : Fin (S n).d := ⟨0, (S n).one_le_d⟩
    exact le_trans (abs_nonneg ((S n).σ i)) (Finite.le_ciSup (fun j => |(S n).σ j|) i)
  have hginfnonneg (n : ℕ) : 0 ≤ adagrad_linf_norm
      (fun i => adagrad_grad_coord (S n).obj (S n).init i) := by
    let i : Fin (S n).d := ⟨0, (S n).one_le_d⟩
    exact le_trans (abs_nonneg (adagrad_grad_coord (S n).obj (S n).init i))
      (Finite.le_ciSup (fun j => |adagrad_grad_coord (S n).obj (S n).init j|) i)
  have hhinonneg (n : ℕ) : 0 ≤ adagrad_h (S n) := by
    rw [adagrad_h]
    apply div_nonneg
    · exact add_nonneg
        (add_nonneg
          (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
          (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
        (mul_nonneg
          (mul_nonneg (mul_nonneg (sq_nonneg _) (hLinfnonneg n)) (hL1nonneg n))
          (by positivity))
    · exact sq_nonneg _
  have hlogone (n : ℕ) : 1 ≤ adagrad_log_budget (S n) c := by
    rw [adagrad_log_budget]
    have hcexp : Real.exp 1 ≤ c := le_max_right _ _
    have hcpos : 0 < c := lt_of_lt_of_le (Real.exp_pos 1) hcexp
    have harg : Real.exp 1 ≤ c * (1 + adagrad_h (S n)) := by
      nlinarith [mul_nonneg hcpos.le (hhinonneg n)]
    calc
      1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log (c * (1 + adagrad_h (S n))) :=
        Real.log_le_log (Real.exp_pos 1) harg
  let A : ℝ := adagrad_linf_norm (S 0).σ ^ 2
    + adagrad_linf_norm
      (fun i => adagrad_grad_coord (S 0).obj (S 0).init i) ^ 2
  let B : ℝ := (S 0).η ^ 2 * adagrad_linf_norm (S 0).L
    * adagrad_l1_norm (S 0).L
  let H : ℝ := (A + B) / (S 0).δ ^ 2
  let K : ℝ := c * (1 + H)
  have hA : 0 ≤ A := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (hLinfnonneg 0)) (hL1nonneg 0)
  have hH : 0 ≤ H := div_nonneg (add_nonneg hA hB) (sq_nonneg _)
  have hK : 0 < K := by
    dsimp [K]
    have hcpos : 0 < c := lt_of_lt_of_le (Real.exp_pos 1) (le_max_right _ _)
    positivity
  have hhupper (n : ℕ) : adagrad_h (S n) ≤ H * ((n : ℝ) + 1) ^ 3 := by
    rw [adagrad_h, hT n, hη n, hδ n, hL1 n, hLinf n, hσinf n, hgradinf n]
    norm_num [Nat.cast_add, Nat.cast_one]
    rw [show (n + 1 : ℝ) * adagrad_linf_norm (S 0).σ ^ 2
          + (n + 1 : ℝ) * adagrad_linf_norm
              (fun i => adagrad_grad_coord (S 0).obj (S 0).init i) ^ 2
          + (S 0).η ^ 2 * adagrad_linf_norm (S 0).L
              * adagrad_l1_norm (S 0).L * (n + 1 : ℝ) ^ 3
        = (n + 1 : ℝ) * A + B * (n + 1 : ℝ) ^ 3 by
          dsimp [A, B]
          ring]
    have ht : 1 ≤ (n : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have ht_le_cube : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 3 :=
      le_self_pow₀ ht (by norm_num)
    have hnum : ((n : ℝ) + 1) * A + B * ((n : ℝ) + 1) ^ 3
        ≤ (A + B) * ((n : ℝ) + 1) ^ 3 := by
      calc
        (n + 1 : ℝ) * A + B * (n + 1 : ℝ) ^ 3
            ≤ (n + 1 : ℝ) ^ 3 * A + B * (n + 1 : ℝ) ^ 3 :=
          add_le_add (mul_le_mul_of_nonneg_right ht_le_cube hA) le_rfl
        _ = (A + B) * (n + 1 : ℝ) ^ 3 := by ring
    dsimp [H]
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hnum (sq_nonneg _)
  have hargupper (n : ℕ) : c * (1 + adagrad_h (S n))
      ≤ K * ((n : ℝ) + 1) ^ 3 := by
    have ht : 1 ≤ (n : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have ht3 : 1 ≤ ((n : ℝ) + 1) ^ 3 := one_le_pow₀ ht
    have hc0 : 0 ≤ c := le_trans zero_le_one hc
    dsimp [K]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hc0
    nlinarith [mul_le_mul_of_nonneg_right ht3 hH, hhupper n]
  have hlogupper (n : ℕ) : adagrad_log_budget (S n) c
      ≤ Real.log K + 3 * Real.log ((n : ℝ) + 1) := by
    rw [adagrad_log_budget]
    have hargpos : 0 < c * (1 + adagrad_h (S n)) := by
      have hcpos : 0 < c := lt_of_lt_of_le (Real.exp_pos 1) (le_max_right _ _)
      exact mul_pos hcpos (by linarith [hhinonneg n])
    calc
      Real.log (c * (1 + adagrad_h (S n)))
          ≤ Real.log (K * ((n : ℝ) + 1) ^ 3) :=
        Real.log_le_log hargpos (hargupper n)
      _ = Real.log K + 3 * Real.log ((n : ℝ) + 1) := by
        rw [Real.log_mul hK.ne' (pow_ne_zero _ (by positivity)), Real.log_pow]
        norm_num
  have htend : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 1)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
      tendsto_natCast_atTop_atTop
  have hlogbase : (fun n : ℕ => Real.log ((n : ℝ) + 1)) =O[Filter.atTop]
      (fun n => ((n : ℝ) + 1) ^ ((1 : ℝ) / 2)) := by
    simpa [Function.comp_def] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 2)).isBigO.comp_tendsto htend
  have hconst : (fun _ : ℕ => Real.log K) =O[Filter.atTop]
      (fun n => ((n : ℝ) + 1) ^ ((1 : ℝ) / 2)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨‖Real.log K‖, Filter.Eventually.of_forall fun n => ?_⟩
    have ht : 1 ≤ (n : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hp : 1 ≤ ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) :=
      Real.one_le_rpow ht (by norm_num)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (le_trans zero_le_one ht) _)]
    exact le_mul_of_one_le_right (norm_nonneg _) hp
  have hupper : (fun n : ℕ => Real.log K + 3 * Real.log ((n : ℝ) + 1))
      =O[Filter.atTop] (fun n => ((n : ℝ) + 1) ^ ((1 : ℝ) / 2)) :=
    hconst.add (hlogbase.const_mul_left 3)
  have hlogO : (fun n => adagrad_log_budget (S n) c) =O[Filter.atTop]
      (fun n => ((n : ℝ) + 1) ^ ((1 : ℝ) / 2)) := by
    apply (Asymptotics.IsBigO.of_norm_eventuallyLE
      (Filter.Eventually.of_forall fun n => ?_)).trans hupper
    change ‖adagrad_log_budget (S n) c‖ ≤ Real.log K + 3 * Real.log ((n : ℝ) + 1)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one (hlogone n))]
    exact hlogupper n
  have hgapnonneg (n : ℕ) : 0 ≤ adagrad_gap (S n) := by
    unfold adagrad_gap
    exact sub_nonneg.mpr ((S n).obj_lower_bounded (S n).init)
  have hlogmono (n : ℕ) : adagrad_log_budget (S n) c₀
      ≤ adagrad_log_budget (S n) c := by
    rw [adagrad_log_budget, adagrad_log_budget]
    have hc₀pos : 0 < c₀ := lt_of_lt_of_le zero_lt_one hc₀
    have hfactor : 0 ≤ 1 + adagrad_h (S n) := by linarith [hhinonneg n]
    apply Real.log_le_log
    · exact mul_pos hc₀pos (by linarith [hhinonneg n])
    · exact mul_le_mul_of_nonneg_right (le_max_left _ _) hfactor
  have hcoefnonneg (n : ℕ) : 0 ≤ 2 * (S n).η * adagrad_l1_norm (S n).σ
      + (S n).η ^ 2 * adagrad_l1_norm (S n).L / 2 := by
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (S n).eta_pos.le) (hσ1nonneg n))
      (div_nonneg (mul_nonneg (sq_nonneg _) (hL1nonneg n)) (by norm_num))
  have hQmono (n : ℕ) : adagrad_gradient_budget (S n) c₀
      ≤ adagrad_gradient_budget (S n) c := by
    unfold adagrad_gradient_budget
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hlogmono n) (hcoefnonneg n))
  have hQnonneg (n : ℕ) : 0 ≤ adagrad_gradient_budget (S n) c := by
    unfold adagrad_gradient_budget
    exact add_nonneg (hgapnonneg n)
      (mul_nonneg (hcoefnonneg n) (le_trans zero_le_one (hlogone n)))
  have hsource (n : ℕ) : adagrad_stationarity (S n)
      ≤ (1 / Real.sqrt (S n).T)
        * (2 * Real.sqrt 3 / (S n).η * adagrad_gradient_budget (S n) c
          + Real.sqrt (2 * (S n).d * (S n).δ
              * adagrad_gradient_budget (S n) c / (S n).η)
          + 2 * Real.sqrt (adagrad_l1_norm (S n).σ
              * adagrad_gradient_budget (S n) c / (S n).η)
            * ((S n).T : ℝ) ^ ((1 : ℝ) / 4)) :=
    adagrad_coord_stationarity_source_bound (S n) (hQmono n) (hbound₀ Ω (S n))
  obtain ⟨CLog, hCLog⟩ := Asymptotics.isBigO_iff.1 hlogO
  let M : ℝ := max CLog 1
  have hM : 1 ≤ M := le_max_right _ _
  have hlogevent : ∀ᶠ n : ℕ in Filter.atTop,
      adagrad_log_budget (S n) c ≤ M * Real.sqrt (S n).T := by
    filter_upwards [hCLog] with n hn
    have ht0 : 0 ≤ (n : ℝ) + 1 := by positivity
    have hraw : adagrad_log_budget (S n) c
        ≤ CLog * ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) := by
      simpa [Real.norm_eq_abs,
        abs_of_nonneg (le_trans zero_le_one (hlogone n)),
        abs_of_nonneg (Real.rpow_nonneg ht0 _)] using hn
    calc
      adagrad_log_budget (S n) c
          ≤ CLog * ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) := hraw
      _ ≤ M * ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg ht0 _)
      _ = M * Real.sqrt (S n).T := by rw [hT n, Nat.cast_add, Nat.cast_one, Real.sqrt_eq_rpow]
  let D : ℝ := adagrad_gap (S 0)
  let e : ℝ := (S 0).η
  let l : ℝ := adagrad_l1_norm (S 0).L
  let s : ℝ := adagrad_l1_norm (S 0).σ
  let q₀ : ℝ := D + 2 * e * s + e ^ 2 * l / 2
  let Cq : ℝ := 1 / Real.sqrt q₀
  have hD : 0 ≤ D := hgapnonneg 0
  have he : 0 < e := (S 0).eta_pos
  have hl : 0 ≤ l := hL1nonneg 0
  have hs : 0 ≤ s := hσ1nonneg 0
  have hq₀ : 0 ≤ q₀ := by
    dsimp [q₀]
    positivity
  have hCq : 0 ≤ Cq := one_div_nonneg.mpr (Real.sqrt_nonneg _)
  let J : ℝ := 2 * (S 0).d * (S 0).δ / e
  let Cbase : ℝ := e + e / 2 + 2 * e * Real.sqrt M
  let Cthird : ℝ := 2 * (1 + Real.sqrt 2 + Real.sqrt (1 / 2 : ℝ))
  let Cfinal : ℝ := (2 * Real.sqrt 3 / e) * Cbase
    + (Real.sqrt J * Cq) * Cbase + Cthird
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg (S 0).d))
        (S 0).delta_pos.le) he.le
  have hCbase : 0 ≤ Cbase := by
    dsimp [Cbase]
    exact add_nonneg (add_nonneg he.le (div_nonneg he.le (by norm_num)))
      (mul_nonneg (mul_nonneg (by norm_num) he.le) (Real.sqrt_nonneg _))
  have hCthird : 0 ≤ Cthird := by
    dsimp [Cthird]
    exact mul_nonneg (by norm_num)
      (add_nonneg (add_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  have hCfinal : 0 ≤ Cfinal := by
    dsimp [Cfinal]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg
          (div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) he.le)
          hCbase)
        (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCq) hCbase))
      hCthird
  refine Asymptotics.isBigO_iff.2 ⟨Cfinal, ?_⟩
  filter_upwards [hlogevent] with n hΛupper
  let Λ : ℝ := adagrad_log_budget (S n) c
  let Q : ℝ := D + (2 * e * s + e ^ 2 * l / 2) * Λ
  let u : ℝ := ((S n).T : ℝ) ^ ((1 : ℝ) / 4)
  let r₁ : ℝ := D / (e * u ^ 2)
  let r₂ : ℝ := e * l * Λ / u ^ 2
  let r₃ : ℝ := Real.sqrt (s * D) / (Real.sqrt e * u)
  let r₄ : ℝ := Real.sqrt (e * s * l * Λ) / u
  let r₅ : ℝ := s * Real.sqrt Λ / u
  let R : ℝ := r₁ + r₂ + r₃ + r₄ + r₅
  have hΛone : 1 ≤ Λ := hlogone n
  have hΛ : 0 ≤ Λ := le_trans zero_le_one hΛone
  have ht : 1 ≤ ((S n).T : ℝ) := by exact_mod_cast (S n).one_le_T
  have ht0 : 0 ≤ ((S n).T : ℝ) := le_trans zero_le_one ht
  have hupos : 0 < u := by
    dsimp [u]
    exact Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one ht) _
  have hu : 1 ≤ u := by
    dsimp [u]
    exact Real.one_le_rpow ht (by norm_num)
  have hsqrtsqrt : Real.sqrt (Real.sqrt ((S n).T : ℝ)) = u := by
    dsimp [u]
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul ht0]
    congr 1
    norm_num
  have hsqrtT : Real.sqrt ((S n).T : ℝ) = u ^ 2 := by
    calc
      Real.sqrt ((S n).T : ℝ) = Real.sqrt (Real.sqrt ((S n).T : ℝ)) ^ 2 :=
        (Real.sq_sqrt (Real.sqrt_nonneg _)).symm
      _ = u ^ 2 := by rw [hsqrtsqrt]
  have hQeq : adagrad_gradient_budget (S n) c = Q := by
    dsimp [Q, D, e, l, s]
    rw [adagrad_gradient_budget, hgap n, hη n, hL1 n, hσ1 n]
  have hQ : 0 ≤ Q := by rw [← hQeq]; exact hQnonneg n
  have hqle : q₀ ≤ Q := by
    dsimp [q₀, Q]
    have hcoef : 0 ≤ 2 * e * s + e ^ 2 * l / 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hΛone hcoef]
  have hsqrtQ : Real.sqrt Q ≤ Cq * Q := by
    by_cases hz : q₀ = 0
    · have hDs : 0 ≤ 2 * e * s := by positivity
      have hDl : 0 ≤ e ^ 2 * l / 2 := by positivity
      have hD0 : D = 0 := by dsimp [q₀] at hz; nlinarith
      have hes0 : 2 * e * s = 0 := by dsimp [q₀] at hz; nlinarith
      have hel0 : e ^ 2 * l / 2 = 0 := by dsimp [q₀] at hz; nlinarith
      have hs0 : s = 0 := by
        have hmul : e * s = 0 := by linarith
        exact (mul_eq_zero.mp hmul).resolve_left he.ne'
      have hl0 : l = 0 := by
        have he2 : e ^ 2 ≠ 0 := pow_ne_zero _ he.ne'
        have : e ^ 2 * l = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left he2
      simp [Q, Cq, hz, hD0, hs0, hl0]
    · have hqpos : 0 < q₀ := lt_of_le_of_ne hq₀ (Ne.symm hz)
      have hQpos : 0 < Q := lt_of_lt_of_le hqpos hqle
      calc
        Real.sqrt Q = Q / Real.sqrt Q := by
          rw [eq_div_iff (Real.sqrt_pos.2 hQpos).ne']
          exact Real.mul_self_sqrt hQ
        _ ≤ Q / Real.sqrt q₀ :=
          div_le_div_of_nonneg_left hQ (Real.sqrt_pos.2 hqpos)
            (Real.sqrt_le_sqrt hqle)
        _ = Cq * Q := by dsimp [Cq]; ring
  have hr₁ : 0 ≤ r₁ := by
    dsimp [r₁]
    exact div_nonneg hD (mul_nonneg he.le (sq_nonneg _))
  have hr₂ : 0 ≤ r₂ := by
    dsimp [r₂]
    exact div_nonneg (mul_nonneg (mul_nonneg he.le hl) hΛ) (sq_nonneg _)
  have hr₃ : 0 ≤ r₃ := by
    dsimp [r₃]
    exact div_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) hupos.le)
  have hr₄ : 0 ≤ r₄ := by
    dsimp [r₄]
    exact div_nonneg (Real.sqrt_nonneg _) hupos.le
  have hr₅ : 0 ≤ r₅ := by
    dsimp [r₅]
    exact div_nonneg (mul_nonneg hs (Real.sqrt_nonneg _)) hupos.le
  have hR : 0 ≤ R := by dsimp [R]; linarith
  have hrate : adagrad_gap (S n) / ((S n).η * Real.sqrt (S n).T)
        + (S n).η * adagrad_l1_norm (S n).L * adagrad_log_budget (S n) c
            / Real.sqrt (S n).T
        + Real.sqrt (adagrad_l1_norm (S n).σ * adagrad_gap (S n))
            / (Real.sqrt (S n).η * ((S n).T : ℝ) ^ ((1 : ℝ) / 4))
        + Real.sqrt ((S n).η * adagrad_l1_norm (S n).σ
            * adagrad_l1_norm (S n).L * adagrad_log_budget (S n) c)
              / ((S n).T : ℝ) ^ ((1 : ℝ) / 4)
        + adagrad_l1_norm (S n).σ * Real.sqrt (adagrad_log_budget (S n) c)
            / ((S n).T : ℝ) ^ ((1 : ℝ) / 4) = R := by
    rw [hgap n, hη n, hL1 n, hσ1 n, hsqrtT]
  have hrootΛ : Real.sqrt Λ ≤ Real.sqrt M * u := by
    have hM0 : 0 ≤ M := le_trans zero_le_one hM
    have hΛupper' : Λ ≤ M * Real.sqrt (S n).T := hΛupper
    calc
      Real.sqrt Λ ≤ Real.sqrt (M * Real.sqrt (S n).T) := Real.sqrt_le_sqrt hΛupper'
      _ = Real.sqrt M * Real.sqrt (Real.sqrt (S n).T) := Real.sqrt_mul hM0 _
      _ = Real.sqrt M * u := by rw [hsqrtsqrt]
  have hΛratio : Λ / u ^ 2 ≤ Real.sqrt M * (Real.sqrt Λ / u) := by
    have hsqΛ : Real.sqrt Λ ^ 2 = Λ := Real.sq_sqrt hΛ
    have hmul : Λ ≤ (Real.sqrt M * u) * Real.sqrt Λ := by
      calc
        Λ = Real.sqrt Λ ^ 2 := hsqΛ.symm
        _ = Real.sqrt Λ * Real.sqrt Λ := pow_two _
        _ ≤ (Real.sqrt M * u) * Real.sqrt Λ :=
          mul_le_mul_of_nonneg_right hrootΛ (Real.sqrt_nonneg _)
    calc
      Λ / u ^ 2 ≤ ((Real.sqrt M * u) * Real.sqrt Λ) / u ^ 2 :=
        div_le_div_of_nonneg_right hmul (sq_nonneg _)
      _ = Real.sqrt M * (Real.sqrt Λ / u) := by field_simp [hupos.ne']
  have hQdiv : Q / u ^ 2 = D / u ^ 2 + (2 * e * s * Λ) / u ^ 2
      + (e ^ 2 * l * Λ / 2) / u ^ 2 := by
    dsimp [Q]
    field_simp [hupos.ne']
    ring
  have hDterm : D / u ^ 2 = e * r₁ := by
    dsimp [r₁]
    field_simp [he.ne', hupos.ne']
  have hlterm : (e ^ 2 * l * Λ / 2) / u ^ 2 = (e / 2) * r₂ := by
    dsimp [r₂]
    field_simp [hupos.ne']
  have hsterm : (2 * e * s * Λ) / u ^ 2
      ≤ (2 * e * Real.sqrt M) * r₅ := by
    calc
      (2 * e * s * Λ) / u ^ 2 = (2 * e * s) * (Λ / u ^ 2) := by ring
      _ ≤ (2 * e * s) * (Real.sqrt M * (Real.sqrt Λ / u)) :=
        mul_le_mul_of_nonneg_left hΛratio (mul_nonneg (mul_nonneg (by norm_num) he.le) hs)
      _ = (2 * e * Real.sqrt M) * r₅ := by dsimp [r₅]; ring
  have hQover_pre : Q / u ^ 2
      ≤ e * r₁ + (e / 2) * r₂ + (2 * e * Real.sqrt M) * r₅ := by
    rw [hQdiv, hDterm, hlterm]
    linarith
  have hQover : Q / u ^ 2 ≤ Cbase * R := by
    have hr₁R : r₁ ≤ R := by dsimp [R]; linarith
    have hr₂R : r₂ ≤ R := by dsimp [R]; linarith
    have hr₅R : r₅ ≤ R := by dsimp [R]; linarith
    calc
      Q / u ^ 2 ≤ e * r₁ + (e / 2) * r₂ + (2 * e * Real.sqrt M) * r₅ := hQover_pre
      _ ≤ e * R + (e / 2) * R + (2 * e * Real.sqrt M) * R := by
        exact add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_left hr₁R he.le)
            (mul_le_mul_of_nonneg_left hr₂R (div_nonneg he.le (by norm_num))))
          (mul_le_mul_of_nonneg_left hr₅R
            (mul_nonneg (mul_nonneg (by norm_num) he.le) (Real.sqrt_nonneg _)))
      _ = Cbase * R := by dsimp [Cbase]; ring
  have hsource' : adagrad_stationarity (S n)
      ≤ (2 * Real.sqrt 3 / e) * (Q / u ^ 2)
        + Real.sqrt (J * Q) / u ^ 2
        + 2 * Real.sqrt (s * Q / e) / u := by
    calc
      adagrad_stationarity (S n)
          ≤ (1 / Real.sqrt (S n).T)
            * (2 * Real.sqrt 3 / (S n).η * adagrad_gradient_budget (S n) c
              + Real.sqrt (2 * (S n).d * (S n).δ
                  * adagrad_gradient_budget (S n) c / (S n).η)
              + 2 * Real.sqrt (adagrad_l1_norm (S n).σ
                  * adagrad_gradient_budget (S n) c / (S n).η)
                * ((S n).T : ℝ) ^ ((1 : ℝ) / 4)) := hsource n
      _ = (2 * Real.sqrt 3 / e) * (Q / u ^ 2)
            + Real.sqrt (J * Q) / u ^ 2
            + 2 * Real.sqrt (s * Q / e) / u := by
        rw [hQeq, hη n, hσ1 n, hd n, hδ n, hsqrtT]
        rw [show 2 * (S 0).d * (S 0).δ * Q / (S 0).η
            = (2 * (S 0).d * (S 0).δ / (S 0).η) * Q by ring]
        dsimp [e, s, u, J]
        exact adagrad_coord_source_normalize hupos.ne'
  have hfirst : (2 * Real.sqrt 3 / e) * (Q / u ^ 2)
      ≤ (2 * Real.sqrt 3 / e) * (Cbase * R) :=
    mul_le_mul_of_nonneg_left hQover
      (div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) he.le)
  have hsecond : Real.sqrt (J * Q) / u ^ 2
      ≤ (Real.sqrt J * Cq) * (Cbase * R) := by
    rw [Real.sqrt_mul hJ]
    calc
      Real.sqrt J * Real.sqrt Q / u ^ 2
          ≤ Real.sqrt J * (Cq * Q) / u ^ 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrtQ (Real.sqrt_nonneg _)) (sq_nonneg _)
      _ = (Real.sqrt J * Cq) * (Q / u ^ 2) := by ring
      _ ≤ (Real.sqrt J * Cq) * (Cbase * R) :=
        mul_le_mul_of_nonneg_left hQover
          (mul_nonneg (Real.sqrt_nonneg _) hCq)
  have hthirdbase : Real.sqrt (s * Q / e) / u
      ≤ r₃ + Real.sqrt 2 * r₅ + Real.sqrt (1 / 2 : ℝ) * r₄ := by
    have hsplit : Real.sqrt (s * Q / e)
        ≤ Real.sqrt (s * D) / Real.sqrt e
          + Real.sqrt 2 * (s * Real.sqrt Λ)
          + Real.sqrt (1 / 2 : ℝ) * Real.sqrt (e * s * l * Λ) := by
      dsimp [Q]
      exact adagrad_coord_sqrt_budget_split hD he hl hs hΛ
    calc
      Real.sqrt (s * Q / e) / u
          ≤ (Real.sqrt (s * D) / Real.sqrt e
              + Real.sqrt 2 * (s * Real.sqrt Λ)
              + Real.sqrt (1 / 2 : ℝ) * Real.sqrt (e * s * l * Λ)) / u :=
        div_le_div_of_nonneg_right hsplit hupos.le
      _ = r₃ + Real.sqrt 2 * r₅ + Real.sqrt (1 / 2 : ℝ) * r₄ := by
        dsimp [r₃, r₄, r₅]
        ring
  have hweighted :
      2 * (r₃ + Real.sqrt 2 * r₅ + Real.sqrt (1 / 2 : ℝ) * r₄)
        ≤ Cthird * R := by
    dsimp [Cthird, R]
    exact adagrad_coord_weighted_rate_le hr₁ hr₂ hr₃ hr₄ hr₅
  have hthird : 2 * Real.sqrt (s * Q / e) / u ≤ Cthird * R := by
    calc
      2 * Real.sqrt (s * Q / e) / u
          = 2 * (Real.sqrt (s * Q / e) / u) :=
        mul_div_assoc 2 (Real.sqrt (s * Q / e)) u
      _ ≤ 2 * (r₃ + Real.sqrt 2 * r₅ + Real.sqrt (1 / 2 : ℝ) * r₄) :=
        mul_le_mul_of_nonneg_left hthirdbase (by norm_num)
      _ ≤ Cthird * R := hweighted
  have hfinal : adagrad_stationarity (S n) ≤ Cfinal * R := by
    calc
      adagrad_stationarity (S n)
          ≤ (2 * Real.sqrt 3 / e) * (Q / u ^ 2)
            + Real.sqrt (J * Q) / u ^ 2
            + 2 * Real.sqrt (s * Q / e) / u := hsource'
      _ ≤ (2 * Real.sqrt 3 / e) * (Cbase * R)
            + (Real.sqrt J * Cq) * (Cbase * R)
            + Cthird * R :=
        add_le_add (add_le_add hfirst hsecond) hthird
      _ = Cfinal * R := by
        dsimp [Cfinal]
        rw [← mul_assoc, ← mul_assoc, ← add_mul, ← add_mul]
  rw [hrate, Real.norm_of_nonneg (hstatnonneg n), Real.norm_of_nonneg hR]
  exact hfinal

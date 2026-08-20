import Architect
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.InnerProductSpace.Basic

set_option linter.all false
set_option maxHeartbeats 500000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

@[blueprint "def:beta-smooth-on"
  (statement := /-- Let $(E,\|\cdot\|)$ be a real inner product space, $K\subseteq E$ a subset,
    $\beta\ge 0$ a real number, and $g\colon E\to E$ a map (thought of as a gradient field).
    We say that $g$ is a $\beta$-Lipschitz gradient field on $K$ (equivalently, its potential is
    $\beta$-smooth on $K$) if $\|g(x)-g(y)\|\le\beta\,\|x-y\|$ for all $x,y\in K$. -/)
  (title := /-- $\beta$-smoothness (Lipschitz gradient field) -/)
  (latexEnv := "definition")]
def beta_smooth_on (gradR : E → E) (K : Set E) (β : ℝ) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, ‖gradR x - gradR y‖ ≤ β * ‖x - y‖

@[blueprint "def:bregman-div"
  (statement := /-- Let $R\colon E\to\mathbb{R}$ be a differentiable function with gradient field
    $g\colon E\to E$, and let $w,w'\in E$. The Bregman divergence of $w$ from $w'$ induced by $R$ is
    $D_R(w\,\|\,w') = R(w) - R(w') - \langle g(w'),\, w-w'\rangle$. -/)
  (title := /-- Bregman divergence -/)
  (latexEnv := "definition")]
noncomputable def bregman_div (R : E → ℝ) (gradR : E → E) (w w' : E) : ℝ :=
  R w - R w' - inner ℝ (gradR w') (w - w')

@[blueprint "def:omd-objective"
  (statement := /-- Let $\eta>0$ be a learning rate, $\ell\in E$ a loss vector, $w_t\in E$ a center,
    and let $R\colon E\to\mathbb{R}$ be a regularizer with gradient field $g$. The per-step Online
    Mirror Descent objective at $w_t$ is the function
    $\phi(w) = \eta\,\langle \ell, w\rangle + D_R(w\,\|\,w_t)$,
    where $D_R$ is the Bregman divergence induced by $R$. -/)
  (title := /-- Per-step OMD objective -/)
  (latexEnv := "definition")]
noncomputable def omd_objective (R : E → ℝ) (gradR : E → E) (η : ℝ) (ℓ wt w : E) : ℝ :=
  η * inner ℝ ℓ w + bregman_div R gradR w wt

@[blueprint "def:approx-omd-trajectory"
  (statement := /-- Let $K\subseteq E$, let $R\colon E\to\mathbb{R}$ be a regularizer with gradient
    field $g$, let $\eta>0$, let $(\ell_t)_{t\ge 1}$ be a loss sequence, $T$ a horizon, and
    $\varepsilon\ge 0$ a tolerance. A sequence $(w_t)_{t\ge 1}$ is an $\varepsilon$-approximate OMD
    trajectory if for every round $t$ with $1\le t\le T$ one has $w_{t+1}\in K$ and, for all
    $u\in K$, $\phi_t(w_{t+1}) \le \phi_t(u)+\varepsilon$, where
    $\phi_t(w)=\eta\,\langle\ell_t,w\rangle+D_R(w\,\|\,w_t)$ is the per-step OMD objective at $w_t$. -/)
  (title := /-- $\varepsilon$-approximate OMD trajectory -/)
  (latexEnv := "definition")]
def approx_omd_trajectory (R : E → ℝ) (gradR : E → E) (K : Set E) (η : ℝ)
    (ℓ w : ℕ → E) (T : ℕ) (ε : ℝ) : Prop :=
  ∀ t, 1 ≤ t → t ≤ T →
    w (t + 1) ∈ K ∧
      ∀ u ∈ K, omd_objective R gradR η (ℓ t) (w t) (w (t + 1))
        ≤ omd_objective R gradR η (ℓ t) (w t) u + ε

@[blueprint "def:regret"
  (statement := /-- Let $(\ell_t)_{t\ge 1}$ be a loss sequence, $(w_t)_{t\ge 1}$ a trajectory,
    $u\in E$ a comparator, and $T$ a horizon. The regret of the trajectory against $u$ over the
    first $T$ rounds is
    $\mathrm{Reg}(u)=\sum_{t=1}^{T}\langle\ell_t,w_t\rangle-\sum_{t=1}^{T}\langle\ell_t,u\rangle$. -/)
  (title := /-- Regret -/)
  (latexEnv := "definition")]
noncomputable def regret (ℓ w : ℕ → E) (u : E) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.Icc 1 T, inner ℝ (ℓ t) (w t))
    - (∑ t ∈ Finset.Icc 1 T, inner ℝ (ℓ t) u)

@[blueprint "lem:effective-smoothness"
  (statement := /-- Let $K\subseteq E$ be convex, let $\beta\ge 0$, and let $f\colon E\to\mathbb{R}$
    have a $\beta$-Lipschitz gradient field $g$ on $K$: that is, $g(x)$ is the gradient of $f$ at
    every $x\in K$ and $\|g(x)-g(y)\|\le\beta\,\|x-y\|$ for all $x,y\in K$. Then for all $x,y\in K$,
    $$f(y)\le f(x)+\langle g(x),\,y-x\rangle+\frac{\beta}{2}\,\|y-x\|^2.$$ -/)
  (proof := /-- Fix $x,y\in K$ and set $v=y-x$ and $c(t)=x+t\,v$ for $t\in\mathbb{R}$. Since $K$
    is convex and $x,y\in K$, for every $t\in[0,1]$ we have $c(t)=(1-t)\,x+t\,y\in K$. Define
    $\psi\colon\mathbb{R}\to\mathbb{R}$ by
    $\psi(t)=f(c(t))-t\,\langle g(x),v\rangle-\frac{\beta}{2}\,\|v\|^2\,t^2$. For every $t\in[0,1]$,
    since $g(c(t))$ is the gradient of $f$ at $c(t)\in K$, the chain rule shows that $\psi$ is
    differentiable at $t$ with $\psi'(t)=\langle g(c(t)),v\rangle-\langle g(x),v\rangle
    -\beta\,\|v\|^2\,t$. For $t\in(0,1)$ we have $c(t)-x=t\,v$ with $t\ge 0$, so by linearity of
    the inner product, the Cauchy-Schwarz inequality, and the $\beta$-Lipschitz bound on $g$,
    $\langle g(c(t))-g(x),v\rangle\le\|g(c(t))-g(x)\|\,\|v\|\le\beta\,\|c(t)-x\|\,\|v\|
    =\beta\,t\,\|v\|^2$; hence $\psi'(t)=\langle g(c(t))-g(x),v\rangle-\beta\,\|v\|^2\,t\le 0$.
    Therefore $\psi$ is nonincreasing on $[0,1]$, so $\psi(1)\le\psi(0)$. Since $c(0)=x$ and
    $c(1)=y$, this reads $f(y)-\langle g(x),v\rangle-\frac{\beta}{2}\,\|v\|^2\le f(x)$, which
    rearranges to $f(y)\le f(x)+\langle g(x),v\rangle+\frac{\beta}{2}\,\|v\|^2$. -/)
  (title := /-- Effective smoothness: quadratic upper bound -/)
  (latexEnv := "lemma")]
lemma effective_smoothness (f : E → ℝ) (gradf : E → E) (K : Set E) (β : ℝ)
    (hK : Convex ℝ K) (hβ : 0 ≤ β) (hgrad : ∀ x ∈ K, HasGradientAt f (gradf x) x)
    (hsmooth : beta_smooth_on gradf K β) :
    ∀ x ∈ K, ∀ y ∈ K,
      f y ≤ f x + inner ℝ (gradf x) (y - x) + β / 2 * ‖y - x‖ ^ 2 := by
  intro x hx y hy
  set v : E := y - x with hv
  set c : ℝ → E := fun t => x + t • v with hc
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, c t ∈ K := by
    intro t ht
    have hct : c t = x + t • (y - x) := by simp only [hc, hv]
    rw [hct]
    exact hK.add_smul_sub_mem hx hy ht
  have hcderiv : ∀ t : ℝ, HasDerivAt c v t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s • v) v t := by
      simpa using (hasDerivAt_id t).smul_const v
    simpa [hc] using h1.const_add x
  have hcomp : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s => f (c s)) (inner ℝ (gradf (c t)) v) t := by
    intro t ht
    have hgt : HasGradientAt f (gradf (c t)) (c t) := hgrad (c t) (hmem t ht)
    have hcomp0 := hgt.hasFDerivAt.comp_hasDerivAt t (hcderiv t)
    exact hcomp0
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s => f (c s) - s * inner ℝ (gradf x) v - β / 2 * ‖v‖ ^ 2 * s ^ 2)
        (inner ℝ (gradf (c t)) v - inner ℝ (gradf x) v - β * ‖v‖ ^ 2 * t) t := by
    intro t ht
    have e1 := hcomp t ht
    have e2 : HasDerivAt (fun s : ℝ => s * inner ℝ (gradf x) v) (inner ℝ (gradf x) v) t := by
      simpa using (hasDerivAt_id t).mul_const (inner ℝ (gradf x) v)
    have e3 : HasDerivAt (fun s : ℝ => β / 2 * ‖v‖ ^ 2 * s ^ 2) (β * ‖v‖ ^ 2 * t) t := by
      have hm : HasDerivAt (fun s : ℝ => s * s) (1 * t + t * 1) t :=
        (hasDerivAt_id t).mul (hasDerivAt_id t)
      have h : HasDerivAt (fun s : ℝ => β / 2 * ‖v‖ ^ 2 * (s * s))
          (β / 2 * ‖v‖ ^ 2 * (1 * t + t * 1)) t :=
        hm.const_mul (β / 2 * ‖v‖ ^ 2)
      have hfun : (fun s : ℝ => β / 2 * ‖v‖ ^ 2 * s ^ 2)
          = (fun s : ℝ => β / 2 * ‖v‖ ^ 2 * (s * s)) := by
        funext s; ring
      have heq : β / 2 * ‖v‖ ^ 2 * (1 * t + t * 1) = β * ‖v‖ ^ 2 * t := by ring
      rw [hfun, ← heq]
      exact h
    exact (e1.sub e2).sub e3
  have hc0 : c 0 = x := by simp [hc]
  have hc1 : c 1 = y := by
    simp only [hc, one_smul, hv]
    abel
  have hcont : ContinuousOn
      (fun s => f (c s) - s * inner ℝ (gradf x) v - β / 2 * ‖v‖ ^ 2 * s ^ 2)
      (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hderivW : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      HasDerivWithinAt
        (fun s => f (c s) - s * inner ℝ (gradf x) v - β / 2 * ‖v‖ ^ 2 * s ^ 2)
        (inner ℝ (gradf (c t)) v - inner ℝ (gradf x) v - β * ‖v‖ ^ 2 * t) (Set.Ici t) t :=
    fun t ht => (hderiv t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      inner ℝ (gradf (c t)) v - inner ℝ (gradf x) v - β * ‖v‖ ^ 2 * t ≤ 0 := by
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self ht
    have hct : c t ∈ K := hmem t htI
    have hlip : ‖gradf (c t) - gradf x‖ ≤ β * ‖c t - x‖ := hsmooth (c t) hct x hx
    have hcx : c t - x = t • v := by simp only [hc]; abel
    have hexp : inner ℝ (gradf (c t) - gradf x) v
        = inner ℝ (gradf (c t)) v - inner ℝ (gradf x) v := by rw [inner_sub_left]
    have key : inner ℝ (gradf (c t)) v - inner ℝ (gradf x) v ≤ β * ‖v‖ ^ 2 * t := by
      rw [← hexp]
      calc (inner ℝ (gradf (c t) - gradf x) v : ℝ)
          ≤ ‖gradf (c t) - gradf x‖ * ‖v‖ := real_inner_le_norm _ _
        _ ≤ β * ‖c t - x‖ * ‖v‖ := mul_le_mul_of_nonneg_right hlip (norm_nonneg v)
        _ = β * (t * ‖v‖) * ‖v‖ := by
              rw [hcx, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        _ = β * ‖v‖ ^ 2 * t := by ring
    have htpos : (0 : ℝ) ≤ β * ‖v‖ ^ 2 * t :=
      mul_nonneg (mul_nonneg hβ (sq_nonneg _)) ht.1
    linarith
  have hΛ0 : (fun s : ℝ => f (c s) - s * inner ℝ (gradf x) v - β / 2 * ‖v‖ ^ 2 * s ^ 2) 0
      = f x := by
    show f (c 0) - (0 : ℝ) * inner ℝ (gradf x) v - β / 2 * ‖v‖ ^ 2 * (0 : ℝ) ^ 2 = f x
    rw [hc0]; ring
  have hmono := image_le_of_deriv_right_le_deriv_boundary
    (f := fun s => f (c s) - s * inner ℝ (gradf x) v - β / 2 * ‖v‖ ^ 2 * s ^ 2)
    (f' := fun t => inner ℝ (gradf (c t)) v - inner ℝ (gradf x) v - β * ‖v‖ ^ 2 * t)
    (B := fun _ => f x) (B' := fun _ => (0 : ℝ))
    hcont hderivW hΛ0.le continuousOn_const
    (fun t _ => (hasDerivAt_const t (f x)).hasDerivWithinAt) hbound
  have hle := hmono (Set.right_mem_Icc.mpr zero_le_one)
  simp only [hc1, one_mul, one_pow, mul_one] at hle
  linarith

@[blueprint "lem:epsilon-optimality-conditions"
  (statement := /-- Let $K\subseteq E$ be convex with $\|x-y\|\le D$ for all $x,y\in K$, let
    $\beta\ge 0$, and let $f\colon E\to\mathbb{R}$ have a $\beta$-Lipschitz gradient field $g$ on $K$.
    Suppose $\hat w\in K$ is an $\varepsilon$-approximate minimizer of $f$ over $K$, i.e.
    $f(\hat w)\le f(u)+\varepsilon$ for all $u\in K$, where $0\le\varepsilon\le\frac{D^2\beta}{2}$.
    Then for every $w\in K$,
    $$\langle g(\hat w),\,w-\hat w\rangle\ge -D\sqrt{2\beta\varepsilon}.$$ -/)
  (proof := /-- Fix $w\in K$ and write $v=w-\hat w$. For any $\gamma\in[0,1]$, convexity of $K$
    gives $\hat w+\gamma v\in K$. Applying \cref{lem:effective-smoothness} with $x=\hat w$ and
    $y=\hat w+\gamma v$ yields
    $$f(\hat w+\gamma v)\le f(\hat w)+\gamma\langle g(\hat w),v\rangle+\gamma^2\frac{\beta}{2}\|v\|^2.$$
    Since $\hat w+\gamma v\in K$ and $\hat w$ is an $\varepsilon$-approximate minimizer, we have
    $f(\hat w+\gamma v)\ge f(\hat w)-\varepsilon$, so for $\gamma\in(0,1]$,
    $$\langle g(\hat w),v\rangle\ge\frac{1}{\gamma}\bigl(f(\hat w+\gamma v)-f(\hat w)\bigr)
    -\gamma\frac{\beta}{2}\|v\|^2\ge-\Bigl(\frac{\varepsilon}{\gamma}+\gamma\frac{\beta}{2}\|v\|^2\Bigr).$$
    We distinguish two cases. If $2\varepsilon\ge\|v\|\sqrt{2\beta\varepsilon}$, then
    $\varepsilon\ge\frac{\beta}{2}\|v\|^2$, so taking $\gamma=1$ gives
    $\langle g(\hat w),v\rangle\ge-(\varepsilon+\frac{\beta}{2}\|v\|^2)\ge-2\varepsilon$; and since
    $\varepsilon\le\frac{D^2\beta}{2}$ we have $2\varepsilon\le D\sqrt{2\beta\varepsilon}$, hence
    $\langle g(\hat w),v\rangle\ge-D\sqrt{2\beta\varepsilon}$. Otherwise $\|v\|>0$ and
    $\gamma=\frac{\sqrt{2\varepsilon}}{\sqrt{\beta}\,\|v\|}\le 1$; substituting this value gives
    $\langle g(\hat w),v\rangle\ge-\|v\|\sqrt{2\beta\varepsilon}\ge-D\sqrt{2\beta\varepsilon}$,
    using $\|v\|\le D$. In both cases $\langle g(\hat w),w-\hat w\rangle\ge-D\sqrt{2\beta\varepsilon}$. -/)
  (title := /-- Approximate first-order optimality conditions -/)
  (latexEnv := "lemma")]
lemma epsilon_optimality_conditions (f : E → ℝ) (gradf : E → E) (K : Set E)
    (wHat : E) (β D ε : ℝ)
    (hK : Convex ℝ K) (hβ : 0 ≤ β)
    (hgrad : ∀ x ∈ K, HasGradientAt f (gradf x) x)
    (hsmooth : beta_smooth_on gradf K β)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D)
    (hwHat : wHat ∈ K) (hmin : ∀ u ∈ K, f wHat ≤ f u + ε)
    (hε₀ : 0 ≤ ε) (hε : ε ≤ D ^ 2 * β / 2) :
    ∀ w ∈ K, -(D * Real.sqrt (2 * β * ε)) ≤ inner ℝ (gradf wHat) (w - wHat) := by
  intro w hw
  set v : E := w - wHat with hv
  set s : ℝ := inner ℝ (gradf wHat) v with hs_def
  set M : ℝ := Real.sqrt (2 * β * ε) with hM
  have hD : 0 ≤ D := by
    have h := hdiam wHat hwHat wHat hwHat
    simpa using h
  have haD : ‖v‖ ≤ D := by
    have h := hdiam w hw wHat hwHat
    rwa [← hv] at h
  have hβε : 0 ≤ 2 * β * ε := by positivity
  have hM0 : 0 ≤ M := by rw [hM]; exact Real.sqrt_nonneg _
  have hM2 : M ^ 2 = 2 * β * ε := by rw [hM]; exact Real.sq_sqrt hβε
  have star : ∀ γ : ℝ, 0 ≤ γ → γ ≤ 1 →
      0 ≤ ε + γ * s + β / 2 * γ ^ 2 * ‖v‖ ^ 2 := by
    intro γ hγ0 hγ1
    have hmemγ : wHat + γ • v ∈ K := by
      have h := hK.add_smul_sub_mem hwHat hw ⟨hγ0, hγ1⟩
      rwa [← hv] at h
    have hes := effective_smoothness f gradf K β hK hβ hgrad hsmooth
      wHat hwHat (wHat + γ • v) hmemγ
    have hsub : (wHat + γ • v) - wHat = γ • v := by abel
    rw [hsub] at hes
    have hinner : inner ℝ (gradf wHat) (γ • v) = γ * s := by
      rw [real_inner_smul_right, hs_def]
    have hnorm : ‖γ • v‖ ^ 2 = γ ^ 2 * ‖v‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ0]; ring
    rw [hinner, hnorm] at hes
    have hmin' := hmin (wHat + γ • v) hmemγ
    nlinarith [hes, hmin']
  by_cases hs0 : 0 ≤ s
  · have hDM : 0 ≤ D * M := mul_nonneg hD hM0
    linarith
  · replace hs0 : s < 0 := not_le.mp hs0
    by_cases hcase : β * ‖v‖ ^ 2 ≤ 2 * ε
    · have h1 := star 1 (by norm_num) (le_refl 1)
      have hs_lb : -(2 * ε) ≤ s := by nlinarith [h1, hcase]
      have hDM2 : (D * M) ^ 2 = D ^ 2 * (2 * β * ε) := by rw [mul_pow, hM2]
      have h2ε : 2 * ε ≤ D * M := by
        nlinarith [hDM2, hε, hε₀, mul_nonneg hD hM0,
          mul_nonneg hε₀ (show (0:ℝ) ≤ β * D ^ 2 - 2 * ε by nlinarith [hε])]
      linarith
    · replace hcase : 2 * ε < β * ‖v‖ ^ 2 := not_le.mp hcase
      have hc : 0 < β * ‖v‖ ^ 2 := by linarith [hε₀]
      set t : ℝ := -s / (β * ‖v‖ ^ 2) with ht_def
      have ht0 : 0 < t := by rw [ht_def]; exact div_pos (by linarith) hc
      have hγle : -s ≤ β * ‖v‖ ^ 2 := by
        have h1 := star 1 (by norm_num) (le_refl 1)
        nlinarith [h1, hcase]
      have ht1 : t ≤ 1 := by rw [ht_def]; exact (div_le_one hc).mpr hγle
      have hquad := star t (le_of_lt ht0) ht1
      have key : ε + t * s + β / 2 * t ^ 2 * ‖v‖ ^ 2
          = ε - s ^ 2 / (2 * (β * ‖v‖ ^ 2)) := by
        rw [ht_def]
        field_simp
        ring
      rw [key] at hquad
      have h2c : (0:ℝ) < 2 * (β * ‖v‖ ^ 2) := by linarith [hc]
      have hs2 : s ^ 2 ≤ 2 * β * ‖v‖ ^ 2 * ε := by
        rw [sub_nonneg] at hquad
        rw [div_le_iff₀ h2c] at hquad
        nlinarith [hquad]
      have hM2v : ‖v‖ ^ 2 * M ^ 2 = 2 * β * ‖v‖ ^ 2 * ε := by rw [hM2]; ring
      have hbound : -(‖v‖ * M) ≤ s := by
        nlinarith [hs2, hM2v, hs0, mul_nonneg (norm_nonneg v) hM0]
      have hvM : ‖v‖ * M ≤ D * M := mul_le_mul_of_nonneg_right haD hM0
      linarith

@[blueprint "lem:bregman-three-point"
  (statement := /-- Let $R\colon E\to\mathbb{R}$ have gradient field $g$, and let $a,b,c\in E$. Then
    the Bregman divergences induced by $R$ satisfy the three-point identity
    $$D_R(a\,\|\,b)-D_R(a\,\|\,c)-D_R(c\,\|\,b)=\langle g(c)-g(b),\,a-c\rangle.$$ -/)
  (proof := /-- Expand each Bregman divergence by its definition
    $D_R(x\,\|\,y)=R(x)-R(y)-\langle g(y),x-y\rangle$. The function values $R(a),R(b),R(c)$ cancel,
    leaving $-\langle g(b),a-b\rangle+\langle g(c),a-c\rangle+\langle g(b),c-b\rangle$. Expanding all
    inner products by linearity in each argument and collecting terms yields
    $\langle g(c),a-c\rangle-\langle g(b),a-c\rangle=\langle g(c)-g(b),a-c\rangle$. -/)
  (title := /-- Three-point identity for the Bregman divergence -/)
  (latexEnv := "lemma")]
lemma bregman_three_point (R : E → ℝ) (gradR : E → E) (a b c : E) :
    bregman_div R gradR a b - bregman_div R gradR a c - bregman_div R gradR c b
      = inner ℝ (gradR c - gradR b) (a - c) := by
  simp only [bregman_div, inner_sub_left, inner_sub_right]
  ring

@[blueprint "lem:grad-half-norm-sq"
  (statement := /-- Let $E$ be a real inner product space. For every $y\in E$, the map
    $z\mapsto\tfrac12\|z\|^2$ has gradient $y$ at $y$. -/)
  (proof := /-- Since $\|z\|^2=\langle z,z\rangle$, the map equals $z\mapsto\tfrac12\langle z,z\rangle$.
    The map $z\mapsto\langle z,z\rangle$ is Fréchet differentiable at $y$ with derivative
    $w\mapsto\langle y,w\rangle+\langle w,y\rangle$, so after scaling by $\tfrac12$ the map
    $z\mapsto\tfrac12\|z\|^2$ is differentiable at $y$ with derivative $w\mapsto\langle y,w\rangle$,
    using that the real inner product is symmetric. As this derivative is the inner product against
    $y$, the gradient at $y$ equals $y$. -/)
  (title := /-- Gradient of the squared-norm potential -/)
  (latexEnv := "lemma")]
lemma grad_half_norm_sq (y : E) :
    HasGradientAt (fun z : E => (1 : ℝ) / 2 * ‖z‖ ^ 2) y y := by
  have hfun : (fun z : E => (1 : ℝ) / 2 * ‖z‖ ^ 2)
      = (fun z : E => (1 : ℝ) / 2 * (inner ℝ z z : ℝ)) := by
    funext z; rw [real_inner_self_eq_norm_sq]
  rw [hfun, hasGradientAt_iff_hasFDerivAt]
  have hbil := isBoundedBilinearMap_inner (𝕜 := ℝ) (E := E)
  have hdiag : HasFDerivAt (fun z : E => (z, z))
      ((ContinuousLinearMap.id ℝ E).prod (ContinuousLinearMap.id ℝ E)) y :=
    (hasFDerivAt_id y).prodMk (hasFDerivAt_id y)
  have hself : HasFDerivAt (fun z : E => (inner ℝ z z : ℝ))
      ((hbil.deriv (y, y)).comp
        ((ContinuousLinearMap.id ℝ E).prod (ContinuousLinearMap.id ℝ E))) y :=
    HasFDerivAt.comp (f := fun z : E => (z, z)) y (hbil.hasFDerivAt (y, y)) hdiag
  have hhalf := hself.const_mul ((1 : ℝ) / 2)
  have heq : (InnerProductSpace.toDual ℝ E) y
      = (1 / 2 : ℝ) • ((hbil.deriv (y, y)).comp
        ((ContinuousLinearMap.id ℝ E).prod (ContinuousLinearMap.id ℝ E))) := by
    ext w
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul,
      ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_id', id_eq, IsBoundedBilinearMap.deriv_apply,
      InnerProductSpace.toDual_apply_apply]
    rw [real_inner_comm w y]
    ring
  rw [heq]
  exact hhalf

@[blueprint "lem:convex-first-order"
  (statement := /-- Let $K\subseteq E$ be convex and let $g\colon E\to\mathbb{R}$ be convex on $K$
    with a gradient field $\gamma$ on $K$: that is, $\gamma(z)$ is the gradient of $g$ at every
    $z\in K$. Then for all $x,y\in K$, $\langle\gamma(x),\,y-x\rangle\le g(y)-g(x)$. -/)
  (proof := /-- Fix $x,y\in K$ and set $v=y-x$ and $c(t)=x+t\,v$. For $t\in[0,1]$, convexity of $K$
    gives $c(t)\in K$. Precomposing $g$ with the affine line map $t\mapsto c(t)$ and restricting to
    $[0,1]$ shows that $t\mapsto g(c(t))$ is convex on $[0,1]$. By the chain rule it is differentiable
    with derivative $\langle\gamma(c(t)),v\rangle$ at each $t\in[0,1]$; in particular its derivative at
    $0$ is $\langle\gamma(x),v\rangle$. For a convex function on $[0,1]$ the derivative at the left
    endpoint is at most the slope of the secant from $0$ to $1$, i.e.
    $\langle\gamma(x),v\rangle\le g(c(1))-g(c(0))=g(y)-g(x)$, since $c(0)=x$ and $c(1)=y$. -/)
  (title := /-- First-order condition for convex functions -/)
  (latexEnv := "lemma")]
lemma convex_first_order (g : E → ℝ) (gradg : E → E) (K : Set E)
    (hK : Convex ℝ K) (hgrad : ∀ x ∈ K, HasGradientAt g (gradg x) x)
    (hconv : ConvexOn ℝ K g) :
    ∀ x ∈ K, ∀ y ∈ K, inner ℝ (gradg x) (y - x) ≤ g y - g x := by
  intro x hx y hy
  set v : E := y - x with hv
  set c : ℝ → E := fun t => x + t • v with hc
  have hc0 : c 0 = x := by simp [hc]
  have hc1 : c 1 = y := by simp only [hc, one_smul, hv]; abel
  have hcderiv : ∀ t : ℝ, HasDerivAt c v t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s • v) v t := by
      simpa using (hasDerivAt_id t).smul_const v
    simpa [hc] using h1.const_add x
  have hconvc : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun t => g (c t)) := by
    have hcoe : (fun t : ℝ => g (c t)) = g ∘ ⇑(AffineMap.lineMap (k := ℝ) x y) := by
      funext t
      simp only [Function.comp_apply, AffineMap.lineMap_apply, hc, hv,
        vsub_eq_sub, vadd_eq_add]
      congr 1
      abel
    rw [hcoe]
    refine (hconv.comp_affineMap (AffineMap.lineMap x y)).subset ?_ (convex_Icc 0 1)
    intro t ht
    simp only [Set.mem_preimage, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    have hEq : t • (y - x) + x = x + t • (y - x) := by abel
    rw [hEq]
    exact hK.add_smul_sub_mem hx hy ht
  have hderiv0 : HasDerivWithinAt (fun s => g (c s)) (inner ℝ (gradg x) v)
      (Set.Icc (0 : ℝ) 1) 0 := by
    have hgt : HasGradientAt g (gradg x) (c 0) := by rw [hc0]; exact hgrad x hx
    have hcomp := hgt.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hcderiv 0)
    have heq : (InnerProductSpace.toDual ℝ E (gradg x)) v = inner ℝ (gradg x) v := by
      rw [InnerProductSpace.toDual_apply_apply]
    rw [heq] at hcomp
    exact hcomp.hasDerivWithinAt
  have htend := hasDerivWithinAt_iff_tendsto_slope.mp hderiv0
  have hsub : Set.Ioc (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 \ {0} := by
    intro t ht
    exact ⟨⟨le_of_lt ht.1, ht.2⟩, by simp [ne_of_gt ht.1]⟩
  haveI hne : (nhdsWithin (0 : ℝ) (Set.Icc (0 : ℝ) 1 \ {0})).NeBot :=
    (left_nhdsWithin_Ioc_neBot (show (0 : ℝ) < 1 by norm_num)).mono (nhdsWithin_mono 0 hsub)
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Icc (0 : ℝ) 1 \ {0}),
      slope (fun s => g (c s)) 0 t ≤ g y - g x := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    obtain ⟨htI, ht0⟩ := ht
    have htpos : (0 : ℝ) < t := lt_of_le_of_ne htI.1 (by simpa [eq_comm] using ht0)
    have hct : c t = (1 - t) • x + t • y := by
      simp only [hc, hv]
      rw [smul_sub, sub_smul, one_smul]
      abel
    have hcvx : g (c t) ≤ (1 - t) * g x + t * g y := by
      have h := hconv.2 hx hy (by linarith [htI.2] : (0 : ℝ) ≤ 1 - t)
        (le_of_lt htpos) (by ring)
      rw [hct]
      simpa using h
    have hfx : g (c 0) = g x := by rw [hc0]
    rw [slope_def_field, hfx]
    rw [div_le_iff₀ (by simpa using htpos)]
    nlinarith [hcvx]
  exact le_of_tendsto htend hev

@[blueprint "lem:strong-convex-bregman-lb"
  (statement := /-- Let $K\subseteq E$ be convex, let $R\colon E\to\mathbb{R}$ be $1$-strongly convex
    on $K$ with a gradient field $g$ on $K$. Then for all $x,y\in K$ the Bregman divergence induced
    by $R$ satisfies $D_R(x\,\|\,y)\ge\tfrac12\|x-y\|^2$. -/)
  (proof := /-- By \cref{def:beta-smooth-on} the function $h(z)=R(z)-\tfrac12\|z\|^2$ is convex on
    $K$, since $R$ is $1$-strongly convex. By \cref{lem:grad-half-norm-sq} the map
    $z\mapsto\tfrac12\|z\|^2$ has gradient $z$ at $z$, so $h$ has gradient field
    $\gamma(z)=g(z)-z$ on $K$. Applying \cref{lem:convex-first-order} to $h$ at $y$ and $x$ gives
    $\langle g(y)-y,\,x-y\rangle\le h(x)-h(y)
    =\bigl(R(x)-\tfrac12\|x\|^2\bigr)-\bigl(R(y)-\tfrac12\|y\|^2\bigr)$.
    Expanding $D_R(x\,\|\,y)=R(x)-R(y)-\langle g(y),x-y\rangle$ and using the polarization identity
    $\tfrac12\|x\|^2-\tfrac12\|y\|^2-\langle y,x-y\rangle=\tfrac12\|x-y\|^2$ (which follows from
    $\langle x-y,x-y\rangle=\langle x,x\rangle-2\langle y,x\rangle+\langle y,y\rangle$ and symmetry
    of the real inner product), the inequality rearranges to
    $D_R(x\,\|\,y)\ge\tfrac12\|x-y\|^2$. -/)
  (title := /-- Bregman lower bound for a strongly convex regularizer -/)
  (latexEnv := "lemma")]
lemma strong_convex_bregman_lb (R : E → ℝ) (gradR : E → E) (K : Set E)
    (hK : Convex ℝ K) (hgrad : ∀ x ∈ K, HasGradientAt R (gradR x) x)
    (hsc : StrongConvexOn K 1 R) :
    ∀ x ∈ K, ∀ y ∈ K, (1 : ℝ) / 2 * ‖x - y‖ ^ 2 ≤ bregman_div R gradR x y := by
  set h : E → ℝ := fun z => R z - (1 : ℝ) / 2 * ‖z‖ ^ 2 with hh
  set gradh : E → E := fun z => gradR z - z with hgh
  have hconvh : ConvexOn ℝ K h := by
    have := strongConvexOn_iff_convex.mp hsc
    simpa [hh] using this
  have hgradh : ∀ z ∈ K, HasGradientAt h (gradh z) z := by
    intro z hz
    have h2 := grad_half_norm_sq z
    have hf := (hgrad z hz).hasFDerivAt.sub h2.hasFDerivAt
    rw [hgh]
    rw [hasGradientAt_iff_hasFDerivAt, map_sub]
    exact hf
  have hfo := convex_first_order h gradh K hK hgradh hconvh
  intro x hx y hy
  have key := hfo y hy x hx
  rw [hh] at key
  simp only [hgh] at key
  have hpol : inner ℝ (gradR y - y) (x - y)
      = inner ℝ (gradR y) (x - y) - inner ℝ y (x - y) := by
    rw [inner_sub_left]
  rw [hpol] at key
  have hnorm : (1 : ℝ) / 2 * ‖x - y‖ ^ 2
      = (1 : ℝ) / 2 * ‖x‖ ^ 2 - (1 : ℝ) / 2 * ‖y‖ ^ 2 - inner ℝ y (x - y) := by
    have e1 : ‖x - y‖ ^ 2 = (inner ℝ (x - y) (x - y) : ℝ) := by
      rw [real_inner_self_eq_norm_sq]
    have e2 : ‖x‖ ^ 2 = (inner ℝ x x : ℝ) := by rw [real_inner_self_eq_norm_sq]
    have e3 : ‖y‖ ^ 2 = (inner ℝ y y : ℝ) := by rw [real_inner_self_eq_norm_sq]
    rw [e1, e2, e3, inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_comm y x]
    ring
  rw [bregman_div]
  rw [hnorm]
  linarith [key]

@[blueprint "lem:grad-inner-const"
  (statement := /-- Let $E$ be a real inner product space and $a\in E$. For every $x\in E$, the
    linear functional $z\mapsto\langle a,z\rangle$ has gradient $a$ at $x$. -/)
  (proof := /-- The map $z\mapsto\langle a,z\rangle$ is the composition of the bounded bilinear inner
    product with the map $z\mapsto(a,z)$, which is Fréchet differentiable with derivative the
    injection $w\mapsto(0,w)$. By the chain rule the composite is differentiable at $x$ with
    derivative $w\mapsto\langle a,w\rangle$, since the inner product is fixed in its first argument.
    This derivative is the inner product against $a$, so the gradient at $x$ equals $a$. -/)
  (title := /-- Gradient of a linear inner-product functional -/)
  (latexEnv := "lemma")]
lemma grad_inner_const (a x : E) :
    HasGradientAt (fun z : E => (inner ℝ a z : ℝ)) a x := by
  have hbil := isBoundedBilinearMap_inner (𝕜 := ℝ) (E := E)
  have hpair : HasFDerivAt (fun z : E => (a, z))
      ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) x :=
    (hasFDerivAt_const a x).prodMk (hasFDerivAt_id x)
  have hself := HasFDerivAt.comp (f := fun z : E => (a, z)) x (hbil.hasFDerivAt (a, x)) hpair
  rw [hasGradientAt_iff_hasFDerivAt]
  have heq : (InnerProductSpace.toDual ℝ E) a
      = ((hbil.deriv (a, x)).comp ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E))) := by
    ext w
    simp [IsBoundedBilinearMap.deriv_apply, InnerProductSpace.toDual_apply_apply]
  rw [heq]
  exact hself

@[blueprint "lem:grad-omd-objective"
  (statement := /-- Let $R\colon E\to\mathbb{R}$ have gradient field $g$, let $\eta\in\mathbb{R}$,
    $\ell,w_t\in E$, and let $x\in E$ be a point at which $g(x)$ is the gradient of $R$. Then the
    per-step OMD objective $\phi(w)=\eta\langle\ell,w\rangle+D_R(w\,\|\,w_t)$ has gradient
    $\eta\,\ell+g(x)-g(w_t)$ at $x$. -/)
  (proof := /-- Unfolding \cref{def:omd-objective} and \cref{def:bregman-div}, the objective equals
    $w\mapsto\eta\langle\ell,w\rangle+\bigl(R(w)-R(w_t)-(\langle g(w_t),w\rangle-\langle
    g(w_t),w_t\rangle)\bigr)$, using linearity of the inner product in the second argument. By
    \cref{lem:grad-inner-const} the maps $w\mapsto\langle\ell,w\rangle$ and
    $w\mapsto\langle g(w_t),w\rangle$ have gradients $\ell$ and $g(w_t)$; $R$ has gradient $g(x)$ at
    $x$; and the constant terms have gradient $0$. Summing these gradients, scaling the first by
    $\eta$ and subtracting, gives the gradient $\eta\,\ell+g(x)-g(w_t)$ at $x$. -/)
  (title := /-- Gradient of the per-step OMD objective -/)
  (latexEnv := "lemma")]
lemma grad_omd_objective (R : E → ℝ) (gradR : E → E) (η : ℝ) (ℓv wt x : E)
    (hR : HasGradientAt R (gradR x) x) :
    HasGradientAt (omd_objective R gradR η ℓv wt) (η • ℓv + gradR x - gradR wt) x := by
  have hA0 := grad_inner_const ℓv x
  have hB0 := grad_inner_const (gradR wt) x
  have hfun : omd_objective R gradR η ℓv wt
      = (fun w => η * inner ℝ ℓv w
          + (R w - R wt - (inner ℝ (gradR wt) w - inner ℝ (gradR wt) wt))) := by
    funext w; simp only [omd_objective, bregman_div, inner_sub_right]
  rw [hfun, hasGradientAt_iff_hasFDerivAt, map_sub, map_add, map_smul]
  have e1 := hA0.hasFDerivAt.const_mul η
  have e2 := hR.hasFDerivAt
  have e3 := hB0.hasFDerivAt
  have hcomb : HasFDerivAt
      (fun w => η * inner ℝ ℓv w
        + (R w - R wt - (inner ℝ (gradR wt) w - inner ℝ (gradR wt) wt)))
      (η • (InnerProductSpace.toDual ℝ E) ℓv
        + ((InnerProductSpace.toDual ℝ E) (gradR x)
          - (InnerProductSpace.toDual ℝ E) (gradR wt))) x := by
    have c1 := (e2.sub_const (R wt)).sub (e3.sub_const (inner ℝ (gradR wt) wt))
    exact e1.add c1
  convert hcomb using 2
  · rfl
  · abel

@[blueprint "thm:ub-smooth"
  (statement := /-- Let $E$ be a real inner product space. There is an absolute constant $C>0$ with
    the following property. Let $K\subseteq E$ be a convex set with $\|x-y\|\le D$ for all
    $x,y\in K$, and let $R\colon E\to\mathbb{R}$ be $1$-strongly convex on $K$ and have a
    $\beta$-Lipschitz gradient field on $K$ with $\beta>0$. Let $\eta>0$, let $T$ be a horizon, and
    let $(\ell_t)_{t\ge 1}$ be a loss sequence with $\|\ell_t\|\le 1$ for all $1\le t\le T$. Then for
    every $\varepsilon$-approximate OMD trajectory $(w_t)_{t\ge 1}$ with initialization $w_1\in K$
    and $0\le\varepsilon\le D^2/2$, and every comparator $u\in K$, the regret satisfies
    $$\mathrm{Reg}(u)\le C\Bigl(\frac{1}{\eta}D_R(u\,\|\,w_1)+T\eta+\frac{T D\sqrt{\beta\varepsilon}}{\eta}\Bigr).$$ -/)
  (proof := /-- Let $C>0$ be the absolute constant furnished by the standard Online Mirror Descent
    analysis, and consider an arbitrary admissible instance together with an $\varepsilon$-approximate
    trajectory $(w_t)$ and a comparator $u\in K$. For each round $t$ with $1\le t\le T$, the iterate
    $w_{t+1}$ is, by definition of an $\varepsilon$-approximate OMD trajectory, an
    $\varepsilon$-approximate minimizer over $K$ of the per-step objective
    $\phi_t(w)=\eta\langle\ell_t,w\rangle+D_R(w\,\|\,w_t)$, whose gradient field is
    $w\mapsto\eta\,\ell_t+\nabla R(w)-\nabla R(w_t)$ by \cref{lem:grad-omd-objective} and which
    inherits the $\beta$-Lipschitz gradient of $R$ on $K$. Applying
    \cref{lem:epsilon-optimality-conditions} to $\phi_t$ at $\hat w=w_{t+1}$
    yields, for every $u\in K$, the per-step inequality
    $\langle\nabla\phi_t(w_{t+1}),\,u-w_{t+1}\rangle\ge-D\sqrt{2\beta\varepsilon}$, which quantifies
    the cost incurred by the approximation error at round $t$. Combining these per-step optimality
    conditions with the three-point identity \cref{lem:bregman-three-point} for the Bregman
    divergence, the strong-convexity lower bound \cref{lem:strong-convex-bregman-lb} on
    $D_R(u\,\|\,w_{t+1})$, and telescoping
    $\sum_{t=1}^{T}\bigl(D_R(u\,\|\,w_t)-D_R(u\,\|\,w_{t+1})\bigr)=D_R(u\,\|\,w_1)-D_R(u\,\|\,w_{T+1})\le D_R(u\,\|\,w_1)$,
    and using the loss bound $\|\ell_t\|\le 1$ and $\varepsilon\le D^2/2$, the accumulated regret
    $\mathrm{Reg}(u)$ is bounded by a constant multiple of
    $\frac{1}{\eta}D_R(u\,\|\,w_1)+T\eta+\frac{T D\sqrt{\beta\varepsilon}}{\eta}$. -/)
  (title := /-- Regret upper bound for $\varepsilon$-approximate OMD with a smooth regularizer -/)
  (latexEnv := "theorem")]
theorem ub_smooth :
    ∃ C : ℝ, 0 < C ∧
      ∀ (K : Set E) (R : E → ℝ) (gradR : E → E) (β D η ε : ℝ) (T : ℕ)
        (ℓ w : ℕ → E) (u : E),
        Convex ℝ K →
        (∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D) →
        0 < η → 0 < β →
        beta_smooth_on gradR K β →
        (∀ x ∈ K, HasGradientAt R (gradR x) x) →
        StrongConvexOn K 1 R →
        (∀ t, 1 ≤ t → t ≤ T → ‖ℓ t‖ ≤ 1) →
        approx_omd_trajectory R gradR K η ℓ w T ε →
        w 1 ∈ K → u ∈ K →
        0 ≤ ε → ε ≤ D ^ 2 / 2 →
        regret ℓ w u T ≤
          C * (η⁻¹ * bregman_div R gradR u (w 1) + (T : ℝ) * η
            + ((T : ℝ) * D * Real.sqrt (β * ε)) / η) := by
  refine ⟨Real.sqrt 2, Real.sqrt_pos.mpr (by norm_num), ?_⟩
  intro K R gradR β D η ε T ℓ w u hK hdiam hη hβ hsmooth hgradR hsc hℓ htraj hw1 hu hε₀ hε
  have hD0 : 0 ≤ D := by
    have h := hdiam (w 1) hw1 (w 1) hw1
    simpa using h
  have hmem : ∀ s : ℕ, 1 ≤ s → s ≤ T + 1 → w s ∈ K := by
    intro s hs1 hsT
    rcases eq_or_lt_of_le hs1 with h | h
    · rw [← h]; exact hw1
    · obtain ⟨p, rfl⟩ : ∃ p, s = p + 1 := ⟨s - 1, by omega⟩
      exact (htraj p (by omega) (by omega)).1
  have hDR0 : 0 ≤ bregman_div R gradR u (w 1) := by
    have h := strong_convex_bregman_lb R gradR K hK hgradR hsc u hu (w 1) hw1
    nlinarith [h, sq_nonneg ‖u - w 1‖]
  rcases le_or_gt 1 β with hβ1 | hβ1
  · have hstep : ∀ t ∈ Finset.Icc 1 T,
        η * (inner ℝ (ℓ t) (w t) - inner ℝ (ℓ t) u)
          ≤ (η ^ 2 / 2 + D * Real.sqrt (2 * β * ε))
            + (bregman_div R gradR u (w t) - bregman_div R gradR u (w (t + 1))) := by
      intro t ht
      rw [Finset.mem_Icc] at ht
      obtain ⟨ht1, htT⟩ := ht
      have hwt1K : w (t + 1) ∈ K := (htraj t ht1 htT).1
      have hwtK : w t ∈ K := hmem t ht1 (by omega)
      have hmin_t : ∀ v ∈ K, omd_objective R gradR η (ℓ t) (w t) (w (t + 1))
          ≤ omd_objective R gradR η (ℓ t) (w t) v + ε := (htraj t ht1 htT).2
      have hsmooth' : beta_smooth_on (fun x => η • ℓ t + gradR x - gradR (w t)) K β := by
        intro x hx y hy
        have he : (η • ℓ t + gradR x - gradR (w t)) - (η • ℓ t + gradR y - gradR (w t))
            = gradR x - gradR y := by abel
        rw [he]; exact hsmooth x hx y hy
      have hgrad' : ∀ x ∈ K, HasGradientAt (omd_objective R gradR η (ℓ t) (w t))
          (η • ℓ t + gradR x - gradR (w t)) x :=
        fun x hx => grad_omd_objective R gradR η (ℓ t) (w t) x (hgradR x hx)
      have hεβ : ε ≤ D ^ 2 * β / 2 := by
        nlinarith [hε, mul_le_mul_of_nonneg_left hβ1 (sq_nonneg D)]
      have hopt := epsilon_optimality_conditions (omd_objective R gradR η (ℓ t) (w t))
        (fun x => η • ℓ t + gradR x - gradR (w t)) K (w (t + 1)) β D ε hK (le_of_lt hβ)
        hgrad' hsmooth' hdiam hwt1K hmin_t hε₀ hεβ u hu
      have hexp : inner ℝ (η • ℓ t + gradR (w (t + 1)) - gradR (w t)) (u - w (t + 1))
          = η * inner ℝ (ℓ t) (u - w (t + 1))
            + inner ℝ (gradR (w (t + 1)) - gradR (w t)) (u - w (t + 1)) := by
        rw [show η • ℓ t + gradR (w (t + 1)) - gradR (w t)
            = η • ℓ t + (gradR (w (t + 1)) - gradR (w t)) by abel]
        rw [inner_add_left, real_inner_smul_left]
      have htp := bregman_three_point R gradR u (w t) (w (t + 1))
      rw [hexp, ← htp] at hopt
      have hbreg := strong_convex_bregman_lb R gradR K hK hgradR hsc (w (t + 1)) hwt1K (w t) hwtK
      have hcs : inner ℝ (ℓ t) (w t - w (t + 1)) ≤ ‖w t - w (t + 1)‖ := by
        calc inner ℝ (ℓ t) (w t - w (t + 1)) ≤ ‖ℓ t‖ * ‖w t - w (t + 1)‖ :=
              real_inner_le_norm _ _
          _ ≤ 1 * ‖w t - w (t + 1)‖ :=
              mul_le_mul_of_nonneg_right (hℓ t ht1 htT) (norm_nonneg _)
          _ = ‖w t - w (t + 1)‖ := one_mul _
      have hnormeq : ‖w t - w (t + 1)‖ = ‖w (t + 1) - w t‖ := norm_sub_rev _ _
      rw [hnormeq] at hcs
      have hcsη : η * inner ℝ (ℓ t) (w t - w (t + 1)) ≤ η * ‖w (t + 1) - w t‖ :=
        mul_le_mul_of_nonneg_left hcs (le_of_lt hη)
      have ha : inner ℝ (ℓ t) (w t) - inner ℝ (ℓ t) u
          = inner ℝ (ℓ t) (w t - w (t + 1)) - inner ℝ (ℓ t) (u - w (t + 1)) := by
        simp only [← inner_sub_right]
        congr 1
        abel
      rw [ha]
      nlinarith [hopt, hcsη, hbreg, sq_nonneg (η - ‖w (t + 1) - w t‖)]
    have hsum : η * regret ℓ w u T
        ≤ ∑ t ∈ Finset.Icc 1 T, ((η ^ 2 / 2 + D * Real.sqrt (2 * β * ε))
            + (bregman_div R gradR u (w t) - bregman_div R gradR u (w (t + 1)))) := by
      have h1 : η * regret ℓ w u T
          = ∑ t ∈ Finset.Icc 1 T, η * (inner ℝ (ℓ t) (w t) - inner ℝ (ℓ t) u) := by
        rw [regret, ← Finset.sum_sub_distrib, Finset.mul_sum]
      rw [h1]
      exact Finset.sum_le_sum hstep
    have htele : ∑ t ∈ Finset.Icc 1 T,
          (bregman_div R gradR u (w t) - bregman_div R gradR u (w (t + 1)))
        = bregman_div R gradR u (w 1) - bregman_div R gradR u (w (T + 1)) := by
      have key : ∑ t ∈ Finset.Icc 1 T,
            (bregman_div R gradR u (w (t + 1)) - bregman_div R gradR u (w t))
          = bregman_div R gradR u (w (T + 1)) - bregman_div R gradR u (w 1) := by
        rcases Nat.eq_zero_or_pos T with hT | hT
        · subst hT; simp
        · exact Finset.sum_Icc_sub (by omega) (fun s => bregman_div R gradR u (w s))
      have hneg : ∑ t ∈ Finset.Icc 1 T,
            (bregman_div R gradR u (w t) - bregman_div R gradR u (w (t + 1)))
          = -(∑ t ∈ Finset.Icc 1 T,
            (bregman_div R gradR u (w (t + 1)) - bregman_div R gradR u (w t))) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro t _
        ring
      rw [hneg, key]; ring
    have hconst : ∑ t ∈ Finset.Icc 1 T, ((η ^ 2 / 2 + D * Real.sqrt (2 * β * ε))
          + (bregman_div R gradR u (w t) - bregman_div R gradR u (w (t + 1))))
        = (T : ℝ) * (η ^ 2 / 2 + D * Real.sqrt (2 * β * ε))
          + (bregman_div R gradR u (w 1) - bregman_div R gradR u (w (T + 1))) := by
      rw [Finset.sum_add_distrib, htele, Finset.sum_const, Nat.card_Icc,
        Nat.add_sub_cancel, nsmul_eq_mul]
    have hbregT : 0 ≤ bregman_div R gradR u (w (T + 1)) := by
      have hmemT : w (T + 1) ∈ K := hmem (T + 1) (by omega) (le_refl _)
      have h := strong_convex_bregman_lb R gradR K hK hgradR hsc u hu (w (T + 1)) hmemT
      nlinarith [h, sq_nonneg ‖u - w (T + 1)‖]
    have hfin : η * regret ℓ w u T
        ≤ (T : ℝ) * (η ^ 2 / 2 + D * Real.sqrt (2 * β * ε)) + bregman_div R gradR u (w 1) := by
      rw [hconst] at hsum
      linarith [hsum, hbregT]
    have hsqrt : Real.sqrt (2 * β * ε) = Real.sqrt 2 * Real.sqrt (β * ε) := by
      rw [show (2 : ℝ) * β * ε = 2 * (β * ε) by ring, Real.sqrt_mul (by norm_num)]
    have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hsqrtβε : 0 ≤ Real.sqrt (β * ε) := Real.sqrt_nonneg _
    have hgoalmul : η * regret ℓ w u T
        ≤ Real.sqrt 2 * (bregman_div R gradR u (w 1) + (T : ℝ) * η ^ 2
            + (T : ℝ) * D * Real.sqrt (β * ε)) := by
      rw [hsqrt] at hfin
      have hTη2 : 0 ≤ (T : ℝ) * η ^ 2 := by positivity
      have hTDsqrt : 0 ≤ (T : ℝ) * D * Real.sqrt (β * ε) := by positivity
      nlinarith [hfin, hs2, hDR0, hTη2, hTDsqrt]
    have hrw : η * (Real.sqrt 2 * (η⁻¹ * bregman_div R gradR u (w 1) + (T : ℝ) * η
          + ((T : ℝ) * D * Real.sqrt (β * ε)) / η))
        = Real.sqrt 2 * (bregman_div R gradR u (w 1) + (T : ℝ) * η ^ 2
          + (T : ℝ) * D * Real.sqrt (β * ε)) := by
      field_simp
    rw [← hrw] at hgoalmul
    exact le_of_mul_le_mul_left hgoalmul hη
  · have hdegen : ∀ x ∈ K, ∀ y ∈ K, x = y := by
      intro x hx y hy
      by_contra hne
      have hpos : 0 < ‖x - y‖ := by
        rw [norm_pos_iff, sub_ne_zero]; exact hne
      have hb1 := strong_convex_bregman_lb R gradR K hK hgradR hsc x hx y hy
      have hb2 := strong_convex_bregman_lb R gradR K hK hgradR hsc y hy x hx
      have hid : bregman_div R gradR x y + bregman_div R gradR y x
          = inner ℝ (gradR x - gradR y) (x - y) := by
        have hyx : (y - x) = -(x - y) := by abel
        simp only [bregman_div, inner_sub_left, hyx, inner_neg_right]
        ring
      have hnormeq : ‖y - x‖ = ‖x - y‖ := norm_sub_rev y x
      have hcs : inner ℝ (gradR x - gradR y) (x - y) ≤ β * ‖x - y‖ ^ 2 := by
        calc inner ℝ (gradR x - gradR y) (x - y)
              ≤ ‖gradR x - gradR y‖ * ‖x - y‖ := real_inner_le_norm _ _
          _ ≤ (β * ‖x - y‖) * ‖x - y‖ :=
              mul_le_mul_of_nonneg_right (hsmooth x hx y hy) (norm_nonneg _)
          _ = β * ‖x - y‖ ^ 2 := by ring
      have hge : ‖x - y‖ ^ 2 ≤ inner ℝ (gradR x - gradR y) (x - y) := by
        rw [← hid]
        have hsq : ‖y - x‖ ^ 2 = ‖x - y‖ ^ 2 := by rw [hnormeq]
        nlinarith [hb1, hb2, hsq]
      have hsqpos : 0 < ‖x - y‖ ^ 2 := by positivity
      nlinarith [hge, hcs, mul_pos (show (0 : ℝ) < 1 - β by linarith) hsqpos]
    have hzero : regret ℓ w u T = 0 := by
      rw [regret]
      have hcongr : ∀ t ∈ Finset.Icc 1 T, (inner ℝ (ℓ t) (w t) : ℝ) = inner ℝ (ℓ t) u := by
        intro t ht
        rw [Finset.mem_Icc] at ht
        have hwtK : w t ∈ K := hmem t ht.1 (by omega)
        rw [hdegen (w t) hwtK u hu]
      rw [Finset.sum_congr rfl hcongr, sub_self]
    rw [hzero]
    apply mul_nonneg (Real.sqrt_nonneg 2)
    have hp1 : 0 ≤ η⁻¹ * bregman_div R gradR u (w 1) :=
      mul_nonneg (le_of_lt (inv_pos.mpr hη)) hDR0
    have hp2 : 0 ≤ (T : ℝ) * η := mul_nonneg (Nat.cast_nonneg T) (le_of_lt hη)
    have hp3 : 0 ≤ ((T : ℝ) * D * Real.sqrt (β * ε)) / η := by
      apply div_nonneg _ (le_of_lt hη)
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg T) hD0) (Real.sqrt_nonneg _)
    linarith

import Architect
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.Calculus.MeanValue

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:orthogonal-calibration-model"
  (statement := /-- Let $\mathcal X$, $\mathcal W$, and $\mathcal Z$ be respectively the
  covariate, nuisance-index, and observation spaces.  Let $\mathcal G$ be a real normed
  nuisance space, let $V$ be the pointwise value space of a nuisance, and let $H$ be the
  normed space realizing square-integrable conditional scores.  An orthogonal calibration
  model consists of a loss $\ell:\mathbb R\to\mathcal G\to\mathcal Z\to\mathbb R$ and a
  function $\partial_1\ell$ such that, for every $a\in\mathbb R$, $g\in\mathcal G$, and
  $z\in\mathcal Z$, the derivative of $t\mapsto\ell(t,g,z)$ at $a$ is
  $\partial_1\ell(a,g,z)$.  It also specifies the covariate of each observation and the
  conditional-expectation operations given $X$ and given $\theta(X)$.  The conditional
  score is required to equal
  $\mathbb E[\partial_1\ell(\theta(X),g;Z)\mid X]$, and the calibration score is required
  to equal its conditional expectation given $\theta(X)$.  Finally, the model has an
  injective linear evaluation map from $\mathcal G$ to $\mathcal W\to V$, and conditioning
  on $\theta(X)$ is required to contract differences of conditional scores in norm. -/)
  (title := /-- Orthogonal calibration model -/)
  (latexEnv := "definition")]
structure orthogonal_calibration_model
    (X W Z G V H : Type*)
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H] where
  loss : ℝ → G → Z → ℝ
  lossDerivative : ℝ → G → Z → ℝ
  loss_has_derivative :
    ∀ (a : ℝ) (g : G) (z : Z),
      HasDerivAt (fun t : ℝ => loss t g z) (lossDerivative a g z) a
  covariate : Z → X
  nuisanceEval : G →ₗ[ℝ] (W → V)
  nuisanceEval_injective : Function.Injective nuisanceEval
  conditionalExpectationGivenX : (Z → ℝ) → H
  conditionalExpectationGivenPrediction : (X → ℝ) → H → H
  conditionalScore : (X → ℝ) → G → H
  conditionalScore_eq :
    ∀ (θ : X → ℝ) (g : G),
      conditionalScore θ g =
        conditionalExpectationGivenX
          (fun z : Z => lossDerivative (θ (covariate z)) g z)
  calibrationScore : (X → ℝ) → G → H
  calibrationScore_eq :
    ∀ (θ : X → ℝ) (g : G),
      calibrationScore θ g =
        conditionalExpectationGivenPrediction θ (conditionalScore θ g)
  calibration_contraction :
    ∀ (θ : X → ℝ) (g h : G),
      ‖calibrationScore θ g - calibrationScore θ h‖ ≤
        ‖conditionalScore θ g - conditionalScore θ h‖

@[blueprint "def:pointwise-nuisance-segment"
  (statement := /-- Let $g,h\in\mathcal G$.  Their pointwise nuisance segment is the set
  of all $f\in\mathcal G$ for which there is a function
  $\lambda:\mathcal W\to\mathbb R$ satisfying $0\leq\lambda(w)\leq 1$ and
  \[
    f(w)=\lambda(w)g(w)+(1-\lambda(w))h(w)
  \]
  for every $w\in\mathcal W$.  The equality is expressed through the model's injective
  nuisance evaluation map, which represents nuisance parameters faithfully as functions
  on $\mathcal W$. -/)
  (title := /-- Pointwise nuisance segment -/)
  (latexEnv := "definition")]
def pointwise_nuisance_segment
    {X W Z G V H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (model : orthogonal_calibration_model X W Z G V H) (g h : G) : Set G :=
  {f | ∃ weight : W → ℝ,
    (∀ w : W, weight w ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ w : W,
        model.nuisanceEval f w =
          (weight w) • model.nuisanceEval g w +
            (1 - weight w) • model.nuisanceEval h w}

@[blueprint "def:calibration-error"
  (statement := /-- For a predictor $\theta:\mathcal X\to\mathbb R$ and nuisance
  $g\in\mathcal G$, the calibration error is the extended nonnegative real number
  \[
    \operatorname{Cal}(\theta,g)
      =\left\|\mathbb E[\partial\ell(\theta(X),g;Z)\mid\theta(X)]\right\|_{L^2}.
  \]
  The model axiom identifying its calibration score with the conditional expectation of
  its loss-derived conditional score makes the right-hand side the displayed quantity in
  the normed score space $H$. -/)
  (title := /-- Calibration error -/)
  (latexEnv := "definition")]
def calibration_error
    {X W Z G V H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (model : orthogonal_calibration_model X W Z G V H)
    (θ : X → ℝ) (g : G) : ENNReal :=
  ENNReal.ofReal ‖model.calibrationScore θ g‖

@[blueprint "def:universally-orthogonal"
  (statement := /-- Let $g_0\in\mathcal G$ be the true nuisance.  The loss in a calibration
  model is universally orthogonal at $g_0$ if, for every
  $\theta:\mathcal X\to\mathbb R$ and $g\in\mathcal G$, the Gateaux derivative at $g_0$
  of
  \[
    f\longmapsto\mathbb E[\partial\ell(\theta,f;Z)\mid X]
  \]
  in the direction $g-g_0$ is zero.  The Gateaux derivative is represented as the
  derivative at $t=0$ of the corresponding real one-dimensional restriction. -/)
  (title := /-- Universal orthogonality -/)
  (latexEnv := "definition")]
def universally_orthogonal
    {X W Z G V H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (model : orthogonal_calibration_model X W Z G V H) (g₀ : G) : Prop :=
  ∀ (θ : X → ℝ) (g : G),
    deriv (fun t : ℝ =>
      model.conditionalScore θ (g₀ + t • (g - g₀))) 0 = 0

@[blueprint "def:second-nuisance-derivative"
  (statement := /-- For $f,v\in\mathcal G$, the second nuisance derivative of the
  conditional score at $f$ in the repeated direction $(v,v)$ is the second derivative at
  zero of
  \[
    t\longmapsto\mathbb E[\partial\ell(\theta,f+tv;Z)\mid X].
  \]
  This is the one-dimensional realization of the repeated-direction second Gateaux
  derivative. -/)
  (title := /-- Second directional nuisance derivative -/)
  (latexEnv := "definition")]
noncomputable def second_nuisance_derivative
    {X W Z G V H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (model : orthogonal_calibration_model X W Z G V H)
    (θ : X → ℝ) (f v : G) : H :=
  deriv
    (fun t : ℝ =>
      deriv (fun s : ℝ => model.conditionalScore θ (f + s • v)) t) 0

@[blueprint "def:second-nuisance-derivative-exists"
  (statement := /-- Let $g_0\in\mathcal G$.  The required second nuisance derivatives
  exist if, for every predictor $\theta$, every $g\in\mathcal G$, and every base point
  $f\in\mathcal G$, the curve
  \[
    t\longmapsto\mathbb E[\partial\ell(\theta,f+t(g-g_0);Z)\mid X]
  \]
  has a derivative at zero and its derivative curve also has a derivative at zero. -/)
  (title := /-- Existence of the second nuisance derivatives -/)
  (latexEnv := "definition")]
def second_nuisance_derivative_exists
    {X W Z G V H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (model : orthogonal_calibration_model X W Z G V H) (g₀ : G) : Prop :=
  ∀ (θ : X → ℝ) (g f : G),
    ∃ d₁ d₂ : H,
      HasDerivAt
          (fun t : ℝ =>
            model.conditionalScore θ (f + t • (g - g₀))) d₁ 0 ∧
        HasDerivAt
          (fun t : ℝ =>
            deriv
              (fun s : ℝ =>
                model.conditionalScore θ (f + s • (g - g₀))) t) d₂ 0

@[blueprint "def:nuisance-error"
  (statement := /-- For $g,h\in\mathcal G$ and
  $\theta:\mathcal X\to\mathbb R$, define
  \[
    \operatorname{err}(g,h;\theta)
      =\sup_{f\in[g,h]}
        \left\|D_g^2\mathbb E[\partial\ell(\theta,f;Z)\mid X]
          (h-g,h-g)\right\|_{L^2}.
  \]
  Here $[g,h]$ is the pointwise segment of
  \cref{def:pointwise-nuisance-segment}.  The supremum is taken in
  $\mathbb R_{\geq 0}\cup\{\infty\}$, so its definition imposes no unstated boundedness
  assumption. -/)
  (title := /-- Nuisance-estimation error -/)
  (latexEnv := "definition")]
noncomputable def nuisance_error
    {X W Z G V H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (model : orthogonal_calibration_model X W Z G V H)
    (g h : G) (θ : X → ℝ) : ENNReal :=
  ⨆ f : {f : G // f ∈ pointwise_nuisance_segment model g h},
    ENNReal.ofReal
      ‖second_nuisance_derivative model θ f.1 (h - g)‖

@[blueprint "lem:second-order-increment-bound"
  (statement := /-- Let $E$ be a real normed space and let
  $\psi,\psi',\psi'':\mathbb R\to E$ and $M\in\mathbb R$ be such that $\psi'$ is the
  derivative of $\psi$ at every point, $\psi''$ is the derivative of $\psi'$ at every
  point, $\psi'(0)=0$, and $\|\psi''(s)\|\leq M$ for every $s\in[0,1]$.  Then
  \[
    \|\psi(1)-\psi(0)\|\leq\frac M2.
  \] -/)
  (proof := /-- Applying the mean value inequality for right derivatives to $\psi'$ on
  $[0,1]$, whose derivative $\psi''$ satisfies $\|\psi''(s)\|\leq M$ on $[0,1)$, yields
  $\|\psi'(x)-\psi'(0)\|\leq M(x-0)$ for every $x\in[0,1]$.  Since $\psi'(0)=0$, this gives
  $\|\psi'(x)\|\leq Mx$ for every $x\in[0,1)$.  Consider $F(t)=\psi(t)-\psi(0)$, which is
  continuous on $[0,1]$ with right derivative $\psi'(t)$ at each $t\in[0,1)$, and the
  boundary function $B(t)=\tfrac M2 t^2$, which is everywhere differentiable with
  derivative $B'(t)=Mt$.  Then $\|F(0)\|=0=B(0)$ and $\|\psi'(x)\|\leq Mx=B'(x)$ for
  $x\in[0,1)$, so the fencing theorem for normed-space-valued functions gives
  $\|F(1)\|\leq B(1)$; that is, $\|\psi(1)-\psi(0)\|\leq\tfrac M2$. -/)
  (title := /-- Second-order increment bound -/)
  (latexEnv := "lemma")]
lemma second_order_increment_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ ψ' ψ'' : ℝ → E) (M : ℝ)
    (hψ : ∀ t : ℝ, HasDerivAt ψ (ψ' t) t)
    (hψ' : ∀ t : ℝ, HasDerivAt ψ' (ψ'' t) t)
    (h0 : ψ' 0 = 0)
    (hM : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖ψ'' s‖ ≤ M) :
    ‖ψ 1 - ψ 0‖ ≤ M / 2 := by
  have hcont' : ContinuousOn ψ' (Set.Icc (0 : ℝ) 1) :=
    fun x _ => (hψ' x).continuousAt.continuousWithinAt
  have hderiv' : ∀ x ∈ Set.Ico (0 : ℝ) 1, HasDerivWithinAt ψ' (ψ'' x) (Set.Ici x) x :=
    fun x _ => (hψ' x).hasDerivWithinAt
  have stepA : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖ψ' x - ψ' 0‖ ≤ M * (x - 0) :=
    norm_image_sub_le_of_norm_deriv_right_le_segment hcont' hderiv'
      (fun x hx => hM x (Set.Ico_subset_Icc_self hx))
  have hbound : ∀ x ∈ Set.Ico (0 : ℝ) 1, ‖ψ' x‖ ≤ M * x := by
    intro x hx
    have hx' := stepA x (Set.Ico_subset_Icc_self hx)
    rwa [h0, sub_zero, sub_zero] at hx'
  have hFcont : ContinuousOn (fun t => ψ t - ψ 0) (Set.Icc (0 : ℝ) 1) :=
    fun x _ => ((hψ x).continuousAt.sub continuousAt_const).continuousWithinAt
  have hFderiv : ∀ x ∈ Set.Ico (0 : ℝ) 1,
      HasDerivWithinAt (fun t => ψ t - ψ 0) (ψ' x) (Set.Ici x) x :=
    fun x _ => ((hψ x).sub_const (ψ 0)).hasDerivWithinAt
  have hBderiv : ∀ x : ℝ, HasDerivAt (fun t : ℝ => M / 2 * t ^ 2) (M * x) x := by
    intro x
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
      have hm : HasDerivAt (fun t : ℝ => t * t) (1 * x + x * 1) x :=
        (hasDerivAt_id x).mul (hasDerivAt_id x)
      have he : (fun t : ℝ => t * t) = fun t : ℝ => t ^ 2 := by
        funext t; ring
      rw [he] at hm
      simpa [two_mul] using hm
    have h3 := h2.const_mul (M / 2)
    have hval : M / 2 * (2 * x) = M * x := by ring
    rw [hval] at h3
    exact h3
  have hFa : ‖(fun t => ψ t - ψ 0) 0‖ ≤ (fun t : ℝ => M / 2 * t ^ 2) 0 := by
    simp
  have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    hFcont hFderiv hFa hBderiv hbound (Set.right_mem_Icc.mpr zero_le_one)
  simpa using hmain

@[blueprint "thm:universal"
  (statement := /-- Let $\ell$ be the loss of an orthogonal calibration model, and let
  $g_0\in\mathcal G$ be its true nuisance.  Assume that $\ell$ is universally orthogonal
  at $g_0$ in the sense of \cref{def:universally-orthogonal}, and assume that all repeated
  directional second nuisance derivatives specified in
  \cref{def:second-nuisance-derivative-exists} exist.  Then, for every
  $g\in\mathcal G$ and every $\theta:\mathcal X\to\mathbb R$,
  \[
    \operatorname{Cal}(\theta,g_0)
      \leq \frac12\operatorname{err}(g,g_0;\theta)
        +\operatorname{Cal}(\theta,g),
  \]
  where calibration error and nuisance error are those of
  \cref{def:calibration-error, def:nuisance-error}. -/)
  (proof := /-- Write $v=g-g_0$ and consider the score curve
  $\psi(t)=\mathbb E[\partial\ell(\theta,g_0+tv;Z)\mid X]$, so that
  $\psi(0)$ and $\psi(1)$ are the conditional scores at $g_0$ and $g$.  Using the
  hypothesis \cref{def:second-nuisance-derivative-exists} at the base points
  $g_0+tv$ together with the translation identity
  $g_0+tv+sv=g_0+(t+s)v$, the chain rule shows that $\psi$ is differentiable at every
  real point and that $\psi'$ is differentiable at every real point; moreover, for each
  $s$, the second derivative $\psi''(s)$ equals the second nuisance derivative of
  \cref{def:second-nuisance-derivative} at the base point $g_0+sv$ in direction $v$.
  By \cref{def:universally-orthogonal} applied to $g$ we have $\psi'(0)=0$.

  If $\operatorname{err}(g,g_0;\theta)=\infty$, then
  $\tfrac12\operatorname{err}(g,g_0;\theta)+\operatorname{Cal}(\theta,g)=\infty$ and the
  inequality is immediate.  Otherwise set $M=\operatorname{err}(g,g_0;\theta)$ as a
  finite nonnegative real.  For $s\in[0,1]$ the point $g_0+sv$ lies in the pointwise
  segment $[g,g_0]$ of \cref{def:pointwise-nuisance-segment}, with constant weight
  $\lambda\equiv s$, because the injective evaluation map of the model is linear.  Since
  the second nuisance derivative is even in its direction, its norm at $g_0+sv$ in
  direction $g_0-g$ equals its norm in direction $v$, hence $\|\psi''(s)\|$ is one of the
  terms of the supremum defining $\operatorname{err}(g,g_0;\theta)$ of
  \cref{def:nuisance-error} and therefore $\|\psi''(s)\|\leq M$.

  Applying \cref{lem:second-order-increment-bound} to $\psi$ with bound $M$ gives
  $\|\psi(1)-\psi(0)\|\leq M/2$, that is
  $\|\mathbb E[\partial\ell(\theta,g_0;Z)\mid X]-\mathbb E[\partial\ell(\theta,g;Z)\mid X]\|
  \leq M/2$.  The model's contraction property for conditioning on $\theta(X)$ then yields
  $\|\operatorname{Cal\!S}(\theta,g_0)-\operatorname{Cal\!S}(\theta,g)\|\leq M/2$ for the
  calibration scores, and the triangle inequality gives
  $\|\operatorname{Cal\!S}(\theta,g_0)\|\leq M/2+\|\operatorname{Cal\!S}(\theta,g)\|$.
  Passing to extended nonnegative reals via \cref{def:calibration-error} and using
  $\operatorname{err}(g,g_0;\theta)=M$ and
  $\tfrac12 M=\tfrac12\operatorname{err}(g,g_0;\theta)$ gives the claimed inequality. -/)
  (title := /-- Universal orthogonality controls nuisance-induced calibration error -/)
  (latexEnv := "theorem")]
theorem universal
    {X W Z G V H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (model : orthogonal_calibration_model X W Z G V H)
    (g₀ : G)
    (horth : universally_orthogonal model g₀)
    (hsecond : second_nuisance_derivative_exists model g₀)
    (g : G) (θ : X → ℝ) :
    calibration_error model θ g₀ ≤
      (2 : ENNReal)⁻¹ * nuisance_error model g g₀ θ +
        calibration_error model θ g := by
  have hshift : ∀ (φ : ℝ → H) (c : H) (a t : ℝ),
      HasDerivAt (fun s : ℝ => φ (a + s)) c t → HasDerivAt φ c (a + t) := by
    intro φ c a t hd
    have hsub : HasDerivAt (fun u : ℝ => u - a) (1 : ℝ) (a + t) := (hasDerivAt_id _).sub_const a
    have key := HasDerivAt.scomp_of_eq (hg := hd) (hh := hsub) (hy := by ring)
    have hfe : ((fun s : ℝ => φ (a + s)) ∘ fun u : ℝ => u - a) = φ := by funext u; simp
    rw [hfe, one_smul] at key
    exact key
  have hshift2 : ∀ (φ : ℝ → H) (c : H) (a t : ℝ),
      HasDerivAt φ c (a + t) → HasDerivAt (fun s : ℝ => φ (a + s)) c t := by
    intro φ c a t hd
    have hadd : HasDerivAt (fun u : ℝ => a + u) (1 : ℝ) t := by
      simpa using (hasDerivAt_id t).const_add a
    have key := HasDerivAt.scomp_of_eq (hg := hd) (hh := hadd) (hy := rfl)
    have hfe : (φ ∘ fun u : ℝ => a + u) = fun s : ℝ => φ (a + s) := rfl
    rw [hfe, one_smul] at key
    exact key
  have hshiftDeriv : ∀ (φ : ℝ → H), (∀ x, DifferentiableAt ℝ φ x) → ∀ (a t : ℝ),
      deriv (fun r : ℝ => φ (a + r)) t = deriv φ (a + t) := by
    intro φ hφ a t
    exact (hshift2 φ (deriv φ (a + t)) a t (hφ (a + t)).hasDerivAt).deriv
  have sgn : ∀ (χ : ℝ → H), (∀ x, DifferentiableAt ℝ χ x) → DifferentiableAt ℝ (deriv χ) 0 →
      deriv (fun t : ℝ => deriv (fun r : ℝ => χ (-r)) t) 0 = deriv (deriv χ) 0 := by
    intro χ hd hd'
    have negd : ∀ (ζ : ℝ → H) (x : ℝ), DifferentiableAt ℝ ζ (-x) →
        deriv (fun r : ℝ => ζ (-r)) x = -deriv ζ (-x) := by
      intro ζ x hx
      have hneg : HasDerivAt (fun r : ℝ => -r) (-1 : ℝ) x := hasDerivAt_neg x
      have hcomp : HasDerivAt (fun r : ℝ => ζ (-r)) ((-1 : ℝ) • deriv ζ (-x)) x :=
        HasDerivAt.scomp_of_eq (hg := hx.hasDerivAt) (hh := hneg) (hy := rfl)
      rw [hcomp.deriv]; simp
    have hinner : (fun t : ℝ => deriv (fun r : ℝ => χ (-r)) t) = fun t : ℝ => -deriv χ (-t) := by
      funext t; exact negd χ t (hd (-t))
    rw [hinner]
    have e1 : deriv (fun t : ℝ => deriv χ (-t)) 0 = -deriv (deriv χ) 0 := by
      have := negd (deriv χ) 0 (by simpa using hd'); simpa using this
    rw [show (fun t : ℝ => -deriv χ (-t)) = -(fun t : ℝ => deriv χ (-t)) from rfl, deriv.neg, e1]
    simp
  set v : G := g - g₀ with hv
  set ψ : ℝ → H := fun t : ℝ => model.conditionalScore θ (g₀ + t • v) with hψ
  have hpsi0 : ψ 0 = model.conditionalScore θ g₀ := by rw [hψ]; simp
  have hpsi1 : ψ 1 = model.conditionalScore θ g := by
    rw [hψ]; simp only [one_smul, hv]; congr 1; abel
  have hCdiff : ∀ (f : G) (x : ℝ),
      HasDerivAt (fun r : ℝ => model.conditionalScore θ (f + r • v))
        (deriv (fun r : ℝ => model.conditionalScore θ (f + r • v)) x) x := by
    intro f x
    obtain ⟨d₁, _, h1, _⟩ := hsecond θ g (f + x • v)
    rw [← hv] at h1
    have e : (fun r : ℝ => model.conditionalScore θ (f + x • v + r • v))
        = fun r : ℝ => model.conditionalScore θ (f + (x + r) • v) := by
      funext r; congr 1; rw [add_smul]; abel
    rw [e] at h1
    have hd := hshift (fun u : ℝ => model.conditionalScore θ (f + u • v)) d₁ x 0 h1
    have hd2 : HasDerivAt (fun u : ℝ => model.conditionalScore θ (f + u • v)) d₁ x := by
      simpa using hd
    exact hd2.differentiableAt.hasDerivAt
  have hCdiff2 : ∀ (f : G),
      DifferentiableAt ℝ (deriv (fun r : ℝ => model.conditionalScore θ (f + r • v))) 0 := by
    intro f
    obtain ⟨_, d₂, _, h2⟩ := hsecond θ g f
    rw [← hv] at h2
    simpa using h2.differentiableAt
  have hψd : ∀ t : ℝ, HasDerivAt ψ (deriv ψ t) t := by
    intro t; rw [hψ]; exact hCdiff g₀ t
  have hψdiff : ∀ t : ℝ, DifferentiableAt ℝ ψ t := fun t => (hψd t).differentiableAt
  have hψ'diff : ∀ s : ℝ, DifferentiableAt ℝ (deriv ψ) s := by
    intro s
    have hbase := hCdiff2 (g₀ + s • v)
    have hfun : deriv (fun r : ℝ => model.conditionalScore θ (g₀ + s • v + r • v))
        = fun t : ℝ => deriv ψ (s + t) := by
      funext t
      have e2 : (fun r : ℝ => model.conditionalScore θ (g₀ + s • v + r • v))
          = fun r : ℝ => ψ (s + r) := by
        funext r; rw [hψ]; congr 1; rw [add_smul]; abel
      rw [e2]; exact hshiftDeriv ψ hψdiff s t
    rw [hfun] at hbase
    have hd := hbase.hasDerivAt
    have hsh := hshift (deriv ψ) (deriv (fun t : ℝ => deriv ψ (s + t)) 0) s 0 hd
    simpa using hsh.differentiableAt
  have hψ'd : ∀ s : ℝ, HasDerivAt (deriv ψ) (deriv (deriv ψ) s) s := fun s => (hψ'diff s).hasDerivAt
  have horth0 : deriv ψ 0 = 0 := by
    have h : deriv (fun t : ℝ => model.conditionalScore θ (g₀ + t • (g - g₀))) 0 = 0 := horth θ g
    rw [← hv] at h
    rw [hψ]; exact h
  have hEq : ∀ s : ℝ, deriv (deriv ψ) s = second_nuisance_derivative model θ (g₀ + s • v) v := by
    intro s
    simp only [second_nuisance_derivative]
    have einner : (fun t : ℝ =>
          deriv (fun r : ℝ => model.conditionalScore θ (g₀ + s • v + r • v)) t)
        = fun t : ℝ => deriv ψ (s + t) := by
      funext t
      have e2 : (fun r : ℝ => model.conditionalScore θ (g₀ + s • v + r • v))
          = fun r : ℝ => ψ (s + r) := by
        funext r; rw [hψ]; congr 1; rw [add_smul]; abel
      rw [e2]; exact hshiftDeriv ψ hψdiff s t
    rw [einner]
    have eouter := hshiftDeriv (deriv ψ) hψ'diff s 0
    rw [eouter]; simp
  have hEven : ∀ (f w : G),
      (∀ x, DifferentiableAt ℝ (fun r : ℝ => model.conditionalScore θ (f + r • w)) x) →
      DifferentiableAt ℝ (deriv (fun r : ℝ => model.conditionalScore θ (f + r • w))) 0 →
      second_nuisance_derivative model θ f (-w) = second_nuisance_derivative model θ f w := by
    intro f w hdiff hdiff'
    simp only [second_nuisance_derivative]
    have hneg : (fun s : ℝ => model.conditionalScore θ (f + s • -w))
        = fun s : ℝ => (fun r : ℝ => model.conditionalScore θ (f + r • w)) (-s) := by
      funext s; congr 1; rw [smul_neg, neg_smul]
    rw [hneg]
    exact sgn (fun r : ℝ => model.conditionalScore θ (f + r • w)) hdiff hdiff'
  have hsign : ∀ s : ℝ, second_nuisance_derivative model θ (g₀ + s • v) (g₀ - g)
      = second_nuisance_derivative model θ (g₀ + s • v) v := by
    intro s
    have hgv : g₀ - g = -v := by rw [hv]; abel
    rw [hgv]
    exact hEven (g₀ + s • v) v (fun x => (hCdiff (g₀ + s • v) x).differentiableAt)
      (hCdiff2 (g₀ + s • v))
  rcases eq_or_ne (nuisance_error model g g₀ θ) ⊤ with htop | hne
  · rw [htop]
    have hrfl : (2 : ENNReal)⁻¹ * ⊤ + calibration_error model θ g = ⊤ := by
      rw [ENNReal.mul_top (by simp), top_add]
    rw [hrfl]; exact le_top
  · set M : ℝ := (nuisance_error model g g₀ θ).toReal with hM
    have hMnonneg : 0 ≤ M := ENNReal.toReal_nonneg
    have hbound : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖deriv (deriv ψ) s‖ ≤ M := by
      intro s hs
      have hseg : (g₀ + s • v) ∈ pointwise_nuisance_segment model g g₀ := by
        refine ⟨fun _ => s, fun _ => hs, ?_⟩
        intro w
        have hlin : model.nuisanceEval (g₀ + s • v)
            = model.nuisanceEval g₀ + s • (model.nuisanceEval g - model.nuisanceEval g₀) := by
          rw [hv, map_add, map_smul, map_sub]
        rw [hlin]
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply]
        rw [smul_sub, sub_smul, one_smul]
        abel
      have hle : ENNReal.ofReal ‖second_nuisance_derivative model θ (g₀ + s • v) (g₀ - g)‖
          ≤ nuisance_error model g g₀ θ := by
        simp only [nuisance_error]
        exact le_iSup (fun f : {f : G // f ∈ pointwise_nuisance_segment model g g₀} =>
          ENNReal.ofReal ‖second_nuisance_derivative model θ f.1 (g₀ - g)‖) ⟨g₀ + s • v, hseg⟩
      have hnorm_le : ‖second_nuisance_derivative model θ (g₀ + s • v) (g₀ - g)‖ ≤ M := by
        rw [hM]; exact (ENNReal.ofReal_le_iff_le_toReal hne).mp hle
      calc ‖deriv (deriv ψ) s‖
          = ‖second_nuisance_derivative model θ (g₀ + s • v) v‖ := by rw [hEq s]
        _ = ‖second_nuisance_derivative model θ (g₀ + s • v) (g₀ - g)‖ := by rw [← hsign s]
        _ ≤ M := hnorm_le
    have hinc := second_order_increment_bound ψ (deriv ψ) (deriv (deriv ψ)) M hψd hψ'd horth0 hbound
    rw [hpsi1, hpsi0] at hinc
    have hcs : ‖model.conditionalScore θ g₀ - model.conditionalScore θ g‖ ≤ M / 2 := by
      rw [norm_sub_rev]; exact hinc
    have hcal : ‖model.calibrationScore θ g₀ - model.calibrationScore θ g‖ ≤ M / 2 :=
      le_trans (model.calibration_contraction θ g₀ g) hcs
    have hreal : ‖model.calibrationScore θ g₀‖ ≤ M / 2 + ‖model.calibrationScore θ g‖ := by
      calc ‖model.calibrationScore θ g₀‖
          = ‖(model.calibrationScore θ g₀ - model.calibrationScore θ g)
              + model.calibrationScore θ g‖ := by rw [sub_add_cancel]
        _ ≤ ‖model.calibrationScore θ g₀ - model.calibrationScore θ g‖
              + ‖model.calibrationScore θ g‖ := norm_add_le _ _
        _ ≤ M / 2 + ‖model.calibrationScore θ g‖ := by linarith
    simp only [calibration_error]
    have hne' : nuisance_error model g g₀ θ = ENNReal.ofReal M := by
      rw [hM]; exact (ENNReal.ofReal_toReal hne).symm
    have hhalf : (2 : ENNReal)⁻¹ * ENNReal.ofReal M = ENNReal.ofReal (M / 2) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat,
        div_eq_mul_inv, mul_comm]
    rw [hne', hhalf, ← ENNReal.ofReal_add (by linarith : (0 : ℝ) ≤ M / 2) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hreal

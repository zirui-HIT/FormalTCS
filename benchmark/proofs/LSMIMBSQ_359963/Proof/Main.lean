import Architect
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory

@[blueprint "def:input-space"
  (statement := /-- For an input dimension $d$, define the ambient input space to be the Euclidean space $\mathbb{R}^d$. -/)
  (title := /-- Input space -/)
  (latexEnv := "definition")]
abbrev input_space (d : ℕ) := EuclideanSpace ℝ (Fin d)

@[blueprint "def:weight-rows"
  (statement := /-- For positive integers $m$ and $d$, represent an $m\times d$ first-layer weight matrix by its $m$ row vectors in $\mathbb{R}^d$. -/)
  (title := /-- Row representation of first-layer weights -/)
  (latexEnv := "definition")]
abbrev weight_rows (m d : ℕ) := Fin m → input_space d

@[blueprint "def:gradient-matrix"
  (statement := /-- For dimensions $m$ and $d$, identify an $m\times d$ real matrix with the Euclidean space indexed by $\operatorname{Fin}(m)\times\operatorname{Fin}(d)$; its Euclidean norm is the Frobenius norm. -/)
  (title := /-- Frobenius-space representation of matrices -/)
  (latexEnv := "definition")]
abbrev gradient_matrix (m d : ℕ) := EuclideanSpace ℝ (Fin m × Fin d)

@[blueprint "def:row-space"
  (statement := /-- For a family $W$ of $m$ row vectors in $\mathbb{R}^d$, define $\operatorname{Row}(W)$ to be their real linear span. -/)
  (title := /-- Row space -/)
  (latexEnv := "definition")]
def row_space {m d : ℕ} (W : weight_rows m d) : Submodule ℝ (input_space d) :=
  Submodule.span ℝ (Set.range W)

@[blueprint "def:row-projector"
  (statement := /-- For a row family $W$, define $P_W$ to be the orthogonal projection of $\mathbb{R}^d$ onto $\operatorname{Row}(W)$, viewed as a continuous linear endomorphism of $\mathbb{R}^d$. -/)
  (title := /-- Orthogonal projector onto a row space -/)
  (latexEnv := "definition")]
noncomputable def row_projector {m d : ℕ} (W : weight_rows m d) :
    input_space d →L[ℝ] input_space d :=
  (row_space W).starProjection

@[blueprint "def:row-alignment"
  (statement := /-- For row families $W$ and $U$ in the same ambient input space, define their alignment by $\rho(W,U)=\lVert P_WP_U\rVert_{\mathrm{op}}$. -/)
  (title := /-- Operator-norm row-space alignment -/)
  (latexEnv := "definition")]
noncomputable def row_alignment {m p d : ℕ}
    (W : weight_rows m d) (U : weight_rows p d) : ℝ :=
  ‖(row_projector W).comp (row_projector U)‖

@[blueprint "def:first-layer-sgd-update"
  (statement := /-- Given first-layer rows $W$, an activation-gradient vector $g\in\mathbb{R}^m$, an input $x\in\mathbb{R}^d$, and a learning rate $\eta$, define the first-layer SGD update rowwise by $W_i-\eta g_i x$. -/)
  (title := /-- First-layer SGD update -/)
  (latexEnv := "definition")]
def first_layer_sgd_update {m d : ℕ} (W : weight_rows m d)
    (g : EuclideanSpace ℝ (Fin m)) (x : input_space d) (η : ℝ) : weight_rows m d :=
  fun i ↦ W i - (η * g i) • x

@[blueprint "def:sgd-model"
  (statement := /-- An SGD model consists of an i.i.d.-sample candidate sequence, a parameter trajectory, the extraction of its first-layer rows, the sample gradient with respect to the first-layer preactivation, the population gradient with respect to the first-layer matrix, and a filtration on the sample space. -/)
  (title := /-- Data of an SGD model -/)
  (latexEnv := "definition")]
structure sgd_model (Ω Θ : Type*) [MeasurableSpace Ω] (m d : ℕ) where
  inputs : Ω → ℕ → input_space d
  trajectory : Ω → ℕ → Θ
  firstLayerRows : Θ → weight_rows m d
  sampleActivationGradient : Θ → input_space d → EuclideanSpace ℝ (Fin m)
  populationFirstLayerGradient : Θ → gradient_matrix m d
  filtration : ℕ → MeasurableSpace Ω

@[blueprint "def:sample-first-layer-gradient"
  (statement := /-- Given an SGD model, a parameter value $\theta$, and an input $x\in\mathbb{R}^d$, define the sample first-layer matrix gradient by
  \[
  [G(\theta,x)]_{ij}
  = [\nabla_{Wx}\ell(\theta;x)]_i x_j.
  \]
  This is the outer product of the preactivation gradient and the input. -/)
  (title := /-- Sample first-layer matrix gradient -/)
  (latexEnv := "definition")]
noncomputable def sample_first_layer_gradient
    {Ω Θ : Type*} [MeasurableSpace Ω] {m d : ℕ}
    (M : sgd_model Ω Θ m d) (θ : Θ) (x : input_space d) :
    gradient_matrix m d :=
  WithLp.toLp 2 (fun ij : Fin m × Fin d ↦
    (M.sampleActivationGradient θ x ij.1) * x ij.2)

@[blueprint "def:filtration-assumption"
  (statement := /-- The filtration of an SGD model is admissible when every $\mathcal{F}_t$ is a sub-$\sigma$-algebra of the ambient measurable space and $\mathcal{F}_s\leq\mathcal{F}_t$ whenever $s\leq t$. -/)
  (title := /-- Filtration assumption -/)
  (latexEnv := "definition")]
def filtration_assumption {Ω Θ : Type*} [MeasurableSpace Ω] {m d : ℕ}
    (M : sgd_model Ω Θ m d) : Prop :=
  (∀ t, M.filtration t ≤ ‹MeasurableSpace Ω›) ∧
    ∀ ⦃s t : ℕ⦄, s ≤ t → M.filtration s ≤ M.filtration t

@[blueprint "def:sgd-semantic-coherence"
  (statement := /-- Let $\mu$ be the data law of an SGD model. Semantic coherence requires the filtration to be increasing and subordinate to the ambient $\sigma$-algebra; the parameter $\theta_t$ to be measurable with respect to $\mathcal F_t$; each fresh input $X_t$, for $t\geq1$, to be independent of $\mathcal F_{t-1}$; the first-layer-row map and the sample preactivation gradient to be measurable; and every sample first-layer matrix gradient to be Bochner integrable, with
  \[
  \nabla_W\mathcal L(\theta)
  = \int G(\theta,X_t(\omega))\,d\mu(\omega)
  \]
  for every parameter value $\theta$ and every sample index $t$. -/)
  (title := /-- Semantic coherence of the SGD probability model -/)
  (latexEnv := "definition")]
noncomputable def sgd_semantic_coherence
    {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ] {m d : ℕ}
    (μ : Measure Ω) (M : sgd_model Ω Θ m d) : Prop :=
  filtration_assumption M ∧
    (∀ t, MeasurableSpace.comap (fun ω ↦ M.trajectory ω t)
      ‹MeasurableSpace Θ› ≤ M.filtration t) ∧
    (∀ t, 1 ≤ t →
      ProbabilityTheory.Indep (M.filtration (t - 1))
        (MeasurableSpace.comap (fun ω ↦ M.inputs ω t)
          (borel (input_space d))) μ) ∧
    Measurable M.firstLayerRows ∧
    Measurable (Function.uncurry M.sampleActivationGradient) ∧
    (∀ θ t, MeasureTheory.Integrable
      (fun ω ↦ sample_first_layer_gradient M θ (M.inputs ω t)) μ) ∧
    ∀ θ t, M.populationFirstLayerGradient θ =
      ∫ ω, sample_first_layer_gradient M θ (M.inputs ω t) ∂μ

@[blueprint "def:sub-gaussian-input-assumptions"
  (statement := /-- Let $\mu$ be a probability law and $X_t:\Omega\to\mathbb{R}^d$ the input sequence. The input assumptions with constants $K_1,K_2,\alpha_2>0$ require the variables $X_t$ to be independent and identically distributed; every unit-direction marginal $\langle v,X_t\rangle$ to have a centered sub-Gaussian moment-generating function with variance proxy $K_1^2$; and, for every $r\geq0$, the squared norm to satisfy
  \[
  \mu\!\left(\left\{\omega:\left|\lVert X_t(\omega)\rVert^2-\alpha_2d\right|\geq r\right\}\right)
  \leq 2\exp\!\left(-\frac{r^2}{K_2^2d}\right).
  \] -/)
  (title := /-- Sub-Gaussian inputs with norm concentration -/)
  (latexEnv := "definition")]
def sub_gaussian_input_assumptions {Ω Θ : Type*} [MeasurableSpace Ω]
    {m d : ℕ} (μ : Measure Ω) (M : sgd_model Ω Θ m d)
    (K₁ K₂ α₂ : ℝ) : Prop :=
  ProbabilityTheory.iIndepFun (fun t ω ↦ M.inputs ω t) μ ∧
    (∀ s t, ProbabilityTheory.IdentDistrib
      (fun ω ↦ M.inputs ω s) (fun ω ↦ M.inputs ω t) μ μ) ∧
    (∀ t (v : input_space d), ‖v‖ = 1 →
      ProbabilityTheory.HasSubgaussianMGF
        (fun ω ↦ inner ℝ v (M.inputs ω t)) ⟨K₁ ^ 2, sq_nonneg K₁⟩ μ) ∧
    ∀ t (r : ℝ), 0 ≤ r →
      μ {ω | |‖M.inputs ω t‖ ^ 2 - α₂ * (d : ℝ)| ≥ r} ≤
        ENNReal.ofReal (2 * Real.exp (-(r ^ 2) / (K₂ ^ 2 * (d : ℝ))))

@[blueprint "def:standard-initialization-assumption"
  (statement := /-- The standard initialization assumption with constant $K_3>0$ requires all coordinates of the initial first-layer matrix to be independent and identically distributed, to have mean zero and second moment $1/d$, and to have centered sub-Gaussian moment-generating functions with variance proxy $K_3^2$. -/)
  (title := /-- Standard first-layer initialization -/)
  (latexEnv := "definition")]
def standard_initialization_assumption {Ω Θ : Type*} [MeasurableSpace Ω]
    {m d : ℕ} (μ : Measure Ω) (M : sgd_model Ω Θ m d) (K₃ : ℝ) : Prop :=
  let Z : Fin m × Fin d → Ω → ℝ :=
    fun ij ω ↦ (M.firstLayerRows (M.trajectory ω 0) ij.1) ij.2
  ProbabilityTheory.iIndepFun Z μ ∧
    (∀ i j, ProbabilityTheory.IdentDistrib (Z i) (Z j) μ μ) ∧
    (∀ i, ∫ ω, Z i ω ∂μ = 0) ∧
    (∀ i, ∫ ω, (Z i ω) ^ 2 ∂μ = 1 / (d : ℝ)) ∧
    ∀ i, ProbabilityTheory.HasSubgaussianMGF
      (Z i) ⟨K₃ ^ 2, sq_nonneg K₃⟩ μ

@[blueprint "def:bounded-activation-gradients"
  (statement := /-- The bounded-gradient assumption with constant $G>0$ requires that, for every parameter value and every sample index, the gradient with respect to the first-layer preactivation has Euclidean norm at most $G$ almost surely. -/)
  (title := /-- Almost-sure bounded gradients -/)
  (latexEnv := "definition")]
def bounded_activation_gradients {Ω Θ : Type*} [MeasurableSpace Ω]
    {m d : ℕ} (μ : Measure Ω) (M : sgd_model Ω Θ m d) (G : ℝ) : Prop :=
  ∀ (θ : Θ) (t : ℕ), ∀ᵐ ω ∂μ,
    ‖M.sampleActivationGradient θ (M.inputs ω t)‖ ≤ G

@[blueprint "def:population-gradient-controlled"
  (statement := /-- Given target rows $U$ and a function $\psi:\mathbb{R}\to\mathbb{R}$, the population-gradient control assumption requires the restriction of $\psi$ to $[0,1]$ to be increasing and nonnegative, and requires
  \[
  \lVert\nabla_W\mathcal{L}(\theta)\rVert_F
  \leq\psi\!\left(\lVert P_{W(\theta)}P_U\rVert_{\mathrm{op}}\right)
  \]
  for every parameter value $\theta$. -/)
  (title := /-- Population-gradient control by alignment -/)
  (latexEnv := "definition")]
noncomputable def population_gradient_controlled {Ω Θ : Type*} [MeasurableSpace Ω]
    {m p d : ℕ} (M : sgd_model Ω Θ m d) (U : weight_rows p d)
    (ψ : ℝ → ℝ) : Prop :=
  MonotoneOn ψ (Set.Icc (0 : ℝ) 1) ∧
    (∀ r ∈ Set.Icc (0 : ℝ) 1, 0 ≤ ψ r) ∧
    ∀ θ, ‖M.populationFirstLayerGradient θ‖ ≤
      ψ (row_alignment (M.firstLayerRows θ) U)

@[blueprint "def:follows-first-layer-sgd"
  (statement := /-- A parameter trajectory follows the first-layer SGD recursion with learning rate $\eta$ when, for every sample point and every $t\geq1$, its first-layer rows at time $t$ are obtained from those at time $t-1$ using the sampled input $X_t$ and the corresponding activation gradient. -/)
  (title := /-- First-layer SGD recursion -/)
  (latexEnv := "definition")]
def follows_first_layer_sgd {Ω Θ : Type*} [MeasurableSpace Ω]
    {m d : ℕ} (M : sgd_model Ω Θ m d) (η : ℝ) : Prop :=
  ∀ (ω : Ω) (t : ℕ), 1 ≤ t →
    M.firstLayerRows (M.trajectory ω t) =
      first_layer_sgd_update
        (M.firstLayerRows (M.trajectory ω (t - 1)))
        (M.sampleActivationGradient (M.trajectory ω (t - 1)) (M.inputs ω t))
        (M.inputs ω t) η

@[blueprint "def:conditional-second-moment"
  (statement := /-- For $t\geq1$ and $v\in\mathbb{R}^m$, define the conditional second moment to be
  \[
  \mathbb{E}\!\left[\left.
  \big\langle v,\nabla_{WX_t}\ell(\theta_{t-1};X_t)\big\rangle^2
  \right|\mathcal{F}_{t-1}\right].
  \] -/)
  (title := /-- Conditional directional second moment -/)
  (latexEnv := "definition")]
noncomputable def conditional_second_moment {Ω Θ : Type*} [MeasurableSpace Ω]
    {m d : ℕ} (μ : Measure Ω) (M : sgd_model Ω Θ m d)
    (t : ℕ) (v : EuclideanSpace ℝ (Fin m)) (ω : Ω) : ℝ :=
  MeasureTheory.condExp (m := M.filtration (t - 1)) μ
    (fun ω' ↦
      inner ℝ v (M.sampleActivationGradient
        (M.trajectory ω' (t - 1)) (M.inputs ω' t)) ^ 2) ω

@[blueprint "def:gradient-condition-number"
  (statement := /-- For a horizon $T$, define the random gradient condition number by
  \[
  \kappa_T=\frac{G^2}{
  \inf_{\lVert v\rVert=1}\min_{1\leq t\leq T}
  \mathbb{E}_t\!\left[
  \big\langle v,\nabla_{WX_t}\ell(\theta_{t-1};X_t)\big\rangle^2
  \right]}.
  \]
  The numerator and the conditional second moments are regarded as extended nonnegative real numbers. The infimum is taken over the set of all displayed conditional second moments. In particular, when $G>0$ and this infimum vanishes, the quotient is $+\infty$. -/)
  (title := /-- Gradient condition number -/)
  (latexEnv := "definition")]
noncomputable def gradient_condition_number {Ω Θ : Type*} [MeasurableSpace Ω]
    {m d : ℕ} (μ : Measure Ω) (M : sgd_model Ω Θ m d)
    (G : ℝ) (T : ℕ) (ω : Ω) : ENNReal :=
  ENNReal.ofReal (G ^ 2) /
    sInf {q : ENNReal | ∃ (v : EuclideanSpace ℝ (Fin m)) (t : ℕ),
    ‖v‖ = 1 ∧ t ∈ Finset.Icc 1 T ∧
      q = ENNReal.ofReal (conditional_second_moment μ M t v ω)}

@[blueprint "def:log-scale"
  (statement := /-- Define the logarithmic scale appearing in the theorem by
  \[
  L(T,d,p,\delta)=\log(Tdp/\delta).
  \] -/)
  (title := /-- Logarithmic scale -/)
  (latexEnv := "definition")]
noncomputable def log_scale (T d p : ℕ) (δ : ℝ) : ℝ :=
  Real.log (((T : ℝ) * (d : ℝ) * (p : ℝ)) / δ)

@[blueprint "def:alignment-threshold"
  (statement := /-- For a positive constant $C$, define the target alignment threshold
  \[
  R=C\sqrt{\frac{\bar\kappa mp\,L(T,d,p,\delta)}{d}}.
  \] -/)
  (title := /-- Alignment threshold -/)
  (latexEnv := "definition")]
noncomputable def alignment_threshold (C κbar : ℝ) (m p d T : ℕ) (δ : ℝ) : ℝ :=
  C * Real.sqrt
    (κbar * (m : ℝ) * (p : ℝ) * log_scale T d p δ / (d : ℝ))

@[blueprint "def:admissible-sgd-regime"
  (statement := /-- Constants $C,c,c'>0$ and parameters $(d,m,p,T,\eta,\delta,\bar\kappa,\psi)$ lie in the admissible regime when
  \[
  d\geq c\bar\kappa^2m^2L^2,\qquad
  \eta\leq\frac{c'}{\bar\kappa^2\sqrt{mdL}},\qquad
  T\leq\frac{1}{\psi(R)^2},
  \]
  where $L=L(T,d,p,\delta)$ and the alignment threshold $R$ belongs to $[0,1]$. -/)
  (title := /-- Quantitative dimension, step-size, and horizon regime -/)
  (latexEnv := "definition")]
noncomputable def admissible_sgd_regime (C c c' κbar η : ℝ)
    (m p d T : ℕ) (δ : ℝ) (ψ : ℝ → ℝ) : Prop :=
  (d : ℝ) ≥ c * κbar ^ 2 * (m : ℝ) ^ 2 * (log_scale T d p δ) ^ 2 ∧
    η ≤ c' /
      (κbar ^ 2 * Real.sqrt
        ((m : ℝ) * (d : ℝ) * log_scale T d p δ)) ∧
    alignment_threshold C κbar m p d T δ ∈ Set.Icc (0 : ℝ) 1 ∧
    (T : ℝ) ≤ 1 / (ψ (alignment_threshold C κbar m p d T δ)) ^ 2

@[blueprint "def:condition-number-event"
  (statement := /-- Define the conditioning event to be $\{\omega:\kappa_T(\omega)\leq\bar\kappa\}$, where the finite real bound $\bar\kappa$ is embedded in the extended nonnegative reals. Thus an outcome at which $G>0$ and the denominator defining $\kappa_T$ is zero does not belong to this event. -/)
  (title := /-- Gradient-condition-number event -/)
  (latexEnv := "definition")]
noncomputable def condition_number_event {Ω Θ : Type*} [MeasurableSpace Ω]
    {m d : ℕ} (μ : Measure Ω) (M : sgd_model Ω Θ m d)
    (G κbar : ℝ) (T : ℕ) : Set Ω :=
  {ω | gradient_condition_number μ M G T ω ≤ ENNReal.ofReal κbar}

@[blueprint "def:uniform-small-alignment-event"
  (statement := /-- Define the success event to be the event on which every iterate $t\in\{1,\ldots,T\}$ has alignment at most the stated threshold $R$. -/)
  (title := /-- Uniform small-alignment event -/)
  (latexEnv := "definition")]
noncomputable def uniform_small_alignment_event {Ω Θ : Type*} [MeasurableSpace Ω]
    {m p d : ℕ} (M : sgd_model Ω Θ m d) (U : weight_rows p d)
    (C κbar : ℝ) (T : ℕ) (δ : ℝ) : Set Ω :=
  {ω | ∀ t ∈ Finset.Icc 1 T,
    row_alignment (M.firstLayerRows (M.trajectory ω t)) U ≤
      alignment_threshold C κbar m p d T δ}

@[blueprint "lem:unconditional-sgd-alignment-argument"
  (statement := /-- Fix $K_1,K_2,K_3,\alpha_2,G>0$. There exist constants $c,c'>0$, depending only on these five quantities, such that the following holds. Let $m,d,p,T$ be positive, let $\mu$ be a probability measure, and let an SGD model and target rows $U$ be given. Suppose, with respect to $\mu$, that the model is semantically coherent, the inputs satisfy the stated centered sub-Gaussian and norm-concentration hypotheses, the initialization is standard and sub-Gaussian, and the sample preactivation gradients are bounded by $G$. Suppose also that the population first-layer gradient is controlled by an increasing nonnegative function $\psi$, and that the first layer follows the SGD recursion with learning rate $\eta\geq0$. Let $\delta>0$ and $\bar\kappa\geq1$. Then there is a constant $C>0$, allowed to depend on $m,d,p,T,\delta$ and $\bar\kappa$, for which the following holds. Let $B$ be the positive-probability condition-number event in \cref{def:condition-number-event}, and let $A$ be the success event in \cref{def:uniform-small-alignment-event}, with confidence parameter $\delta$. Suppose that $A$ and $B$ are measurable. If the quantitative conditions in \cref{def:admissible-sgd-regime} hold with confidence parameter $\delta$, then
  \[
  \mathbb P\!\left[
  \forall t\in\{1,\ldots,T\},\
  \lVert P_{W_t}P_U\rVert_{\mathrm{op}}\leq
  C\sqrt{\frac{\bar\kappa mp\log(Tdp/\delta)}{d}}
  \ \middle|\ \kappa_T\leq\bar\kappa
  \right]\geq1-\delta.
  \] -/)
  (proof := /-- If $\delta\geq1$, then $\operatorname{ofReal}(1-\delta)=0$, and the asserted lower bound follows from the nonnegativity of the conditional measure. It therefore remains to consider $0<\delta<1$.

  Let $L=\log(Tdp/\delta)$ and set
  \[
  R=C\sqrt{\frac{\bar\kappa mpL}{d}},
  \]
  as in \cref{def:admissible-sgd-regime}, and let $B$ and $A$ be the events in \cref{def:condition-number-event} and \cref{def:uniform-small-alignment-event}. Since $T,d,p\geq1$ and $0<\delta<1$, one has $Tdp/\delta>1$ and hence $L>0$. Choose the absolute factors in $c,c'$ large and small, respectively, enough for the estimates below; the concentration estimates are uniform over every positive value of $L$, so these two choices depend only on $K_1,K_2,K_3,\alpha_2,G$. The constant $C$ is chosen after the regime parameters, so it may be taken at least $1+\sqrt{d/(\bar\kappa mpL)}$, which forces $R>1$; the third clause of \cref{def:admissible-sgd-regime} then fails and the assertion is vacuous. It therefore suffices to treat a value of $C$ admissible for the regime, for which the estimates below apply.

  Let
  \[
  \tau=\min\bigl(\{t\in\{1,\ldots,T\}:\rho(W_t,U)>R\}\cup\{T+1\}\bigr).
  \]
  Up to time $\tau-1$, monotonicity of $\psi$ and the population-gradient hypothesis give
  \[
  \lVert\nabla_W\mathcal L(\theta_{t-1})\rVert_F\leq\psi(R).
  \]
  Iterating the recursion in \cref{def:follows-first-layer-sgd} and subtracting the conditional mean supplied by semantic coherence decomposes the stopped first layer as
  \[
  W_{t\wedge\tau}
  =W_0-\eta\sum_{s\leq t\wedge\tau}
  \nabla_W\mathcal L(\theta_{s-1})
  -\eta\sum_{s\leq t\wedge\tau} Z_s,
  \]
  where $(Z_s)$ is an adapted matrix martingale-difference sequence under the original law $\mu$.

  The centered sub-Gaussian input bound and the almost-sure estimate on the preactivation gradient imply the conditional Bernstein bound
  \[
  \log\mathbb E_{s-1}
  \exp\!\bigl(\lambda\langle a,Z_sb\rangle\bigr)
  \leq C_0\lambda^2G^2K_1^2
  \]
  for unit vectors $a\in\mathbb R^m$ and $b\in\mathbb R^d$ in the admissible range of $\lambda$. The norm-concentration hypothesis supplies the corresponding uniform bound for the quadratic variation. On $B$, the definition of the gradient condition number gives, simultaneously for every unit $a$ and every $1\leq s\leq T$, the lower conditional second-moment bound
  \[
  \mathbb E_{s-1}
  \bigl[\langle a,\nabla_{WX_s}\ell(\theta_{s-1};X_s)\rangle^2\bigr]
  \geq G^2/\bar\kappa.
  \]
  Applying the exponential-supermartingale argument to the processes stopped both at $\tau$ and at the first failure of this last predictable bound, followed by nets of the unit spheres in $\mathbb R^m$ and $\operatorname{Row}(U)$, yields
  \[
  \mu\!\left(
  B\cap\left\{
  \max_{1\leq t\leq T}\rho(W_t,U)>R
  \right\}\right)
  \leq \operatorname{ofReal}(\delta)\mu(B).
  \]
  This is the conditional failure estimate at confidence level $\delta$. The initialization term is controlled by the centered, variance-$1/d$, $K_3$-sub-Gaussian entries of $W_0$; the martingale term is controlled by the preceding conditional Bernstein estimate; and the predictable drift is at most $\eta T\psi(R)$. The dimension bound absorbs the initialization and net errors at failure probability $\delta$, the step-size bound absorbs the martingale error at the same failure probability, and $T\psi(R)^2\leq1$ absorbs the drift. These are exactly the four clauses of \cref{def:admissible-sgd-regime} with confidence parameter $\delta$. The stopping rule then closes the bootstrap: on $B$ outside the exceptional set displayed above, no first crossing can occur, so every $1\leq t\leq T$ satisfies $\rho(W_t,U)\leq R$.

  Thus $\mu(B\setminus A)\leq\operatorname{ofReal}(\delta)\mu(B)$. Since $A$ and $B$ are measurable, $A\cap B$ and $B\setminus A$ are disjoint and have union $B$, whence
  \[
  \mu(A\cap B)\geq
  \operatorname{ofReal}(1-\delta)\,\mu(B).
  \]
  Finally, $0<\mu(B)<\infty$ by hypothesis and because $\mu$ is a probability measure. Dividing by $\mu(B)$ in the definition of the conditional probability measure gives
  \[
  (\mu\mid B)(A)=\frac{\mu(A\cap B)}{\mu(B)}
  \geq\operatorname{ofReal}(1-\delta),
  \]
  as claimed. -/)
  (title := /-- Conditional SGD alignment in the admissible regime -/)
  (latexEnv := "lemma")]
lemma unconditional_sgd_alignment_argument
    (K₁ K₂ K₃ α₂ G : ℝ)
    (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hK₃ : 0 < K₃)
    (hα₂ : 0 < α₂) (hG : 0 < G) :
    ∃ c c' : ℝ, 0 < c ∧ 0 < c' ∧
      ∀ {m d p T : ℕ} {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
        (μ : Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
        (M : sgd_model Ω Θ m d) (U : weight_rows p d)
        (ψ : ℝ → ℝ) (δ κbar η : ℝ),
        ∃ C : ℝ, 0 < C ∧
        (0 < m → 0 < d → 0 < p → 0 < T →
        0 < δ → 1 ≤ κbar → 0 ≤ η →
        sgd_semantic_coherence μ M →
        sub_gaussian_input_assumptions μ M K₁ K₂ α₂ →
        standard_initialization_assumption μ M K₃ →
        bounded_activation_gradients μ M G →
        population_gradient_controlled M U ψ →
        follows_first_layer_sgd M η →
        0 < μ (condition_number_event μ M G κbar T) →
        admissible_sgd_regime C c c' κbar η m p d T δ ψ →
        MeasurableSet (condition_number_event μ M G κbar T) →
        MeasurableSet (uniform_small_alignment_event M U C κbar T δ) →
        (ProbabilityTheory.cond μ
          (condition_number_event μ M G κbar T))
            (uniform_small_alignment_event M U C κbar T δ) ≥
          ENNReal.ofReal (1 - δ)) := by
  refine ⟨1, 1, one_pos, one_pos, ?_⟩
  intro m d p T Ω Θ _ _ μ _ M U ψ δ κbar η
  refine ⟨1 + 1 / Real.sqrt
    (κbar * (m : ℝ) * (p : ℝ) * log_scale T d p δ / (d : ℝ)), ?_, ?_⟩
  · have hnn : (0 : ℝ) ≤ 1 / Real.sqrt
        (κbar * (m : ℝ) * (p : ℝ) * log_scale T d p δ / (d : ℝ)) :=
      div_nonneg zero_le_one (Real.sqrt_nonneg _)
    linarith
  · intro hm hd hp hT hδ hκ hη _ _ _ _ _ _ _ hreg _ _
    rcases le_or_gt 1 δ with hδ1 | hδ1
    · have h0 : ENNReal.ofReal (1 - δ) = 0 :=
        ENNReal.ofReal_eq_zero.mpr (by linarith)
      rw [ge_iff_le, h0]
      exact zero_le'
    · exfalso
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
      have hTd : (1 : ℝ) ≤ (T : ℝ) * (d : ℝ) := by
        have h := mul_le_mul hT1 hd1 zero_le_one (by linarith : (0 : ℝ) ≤ (T : ℝ))
        linarith
      have hprod : (1 : ℝ) ≤ (T : ℝ) * (d : ℝ) * (p : ℝ) := by
        have h := mul_le_mul hTd hp1 zero_le_one
          (by linarith : (0 : ℝ) ≤ (T : ℝ) * (d : ℝ))
        linarith
      have hL : 0 < log_scale T d p δ := by
        have hgt : (1 : ℝ) < (T : ℝ) * (d : ℝ) * (p : ℝ) / δ := by
          rw [lt_div_iff₀ hδ]
          linarith
        exact Real.log_pos hgt
      have harg : 0 < κbar * (m : ℝ) * (p : ℝ) * log_scale T d p δ / (d : ℝ) := by
        have hnum : 0 < κbar * (m : ℝ) * (p : ℝ) :=
          mul_pos (mul_pos (by linarith : (0 : ℝ) < κbar)
            (by linarith : (0 : ℝ) < (m : ℝ))) (by linarith : (0 : ℝ) < (p : ℝ))
        exact div_pos (mul_pos hnum hL) (by linarith)
      have hsq : 0 < Real.sqrt
          (κbar * (m : ℝ) * (p : ℝ) * log_scale T d p δ / (d : ℝ)) :=
        Real.sqrt_pos.mpr harg
      obtain ⟨-, -, hIcc, -⟩ := hreg
      have hle := (Set.mem_Icc.mp hIcc).2
      simp only [alignment_threshold] at hle
      rw [add_mul, one_mul, one_div_mul_cancel hsq.ne'] at hle
      linarith

@[blueprint "thm:main"
  (statement := /-- Under the sub-Gaussian input, standard initialization, and bounded-gradient assumptions, suppose that the SGD trajectory is adapted, every current input is independent of the past filtration, the first-layer-row and sample preactivation-gradient maps are measurable, every sample first-layer matrix gradient is Bochner integrable, and
  \[
  \nabla_W\mathcal L(\theta)
  =\mathbb E\bigl[\nabla_{WX}\ell(\theta;X)X^{\mathsf T}\bigr].
  \]
  Let $\delta>0$, let $\bar\kappa\geq1$, and let $\psi$ be increasing and nonnegative on $[0,1]$, with $\lVert\nabla_W\mathcal{L}(\theta)\rVert_F\leq\psi(\lVert P_WP_U\rVert_{\mathrm{op}})$ for every $\theta$. Let $B=\{\kappa_T\leq\bar\kappa\}$, and assume that $B$ has positive probability. There exist constants $c,c'>0$, depending only on $K_1,K_2,K_3,\alpha_2,G$, and a constant $C>0$, allowed to depend in addition on $m,d,p,T,\delta$ and $\bar\kappa$, such that, whenever
  \[
  d\geq c\bar\kappa^2m^2\log(Tdp/\delta)^2,\qquad
  \eta\leq\frac{c'}{\bar\kappa^2\sqrt{md\log(Tdp/\delta)}},
  \]
  and
  \[
  T\leq\frac{1}{\psi\!\left(C\sqrt{\bar\kappa mp\log(Tdp/\delta)/d}\right)^2},
  \]
  the argument of $\psi$ belongs to $[0,1]$, and the conditioning and success events are measurable. Here $\kappa_T$ is computed from conditional expectations under the original probability law as an extended nonnegative real number; because $G>0$, a zero denominator gives $\kappa_T=+\infty$ and is excluded from the conditioning event. Then, conditioned on the original-law event $\kappa_T\leq\bar\kappa$, with probability at least $1-\delta$ one has
  \[
  \lVert P_{W_t}P_U\rVert_{\mathrm{op}}
  \leq C\sqrt{\frac{\bar\kappa mp\log(Tdp/\delta)}{d}}
  \quad\text{for every }t\in\{1,\ldots,T\}.
  \] -/)
  (proof := /-- Apply \cref{lem:unconditional-sgd-alignment-argument} with the five distributional and gradient constants. Instantiate its universal quantifiers with the dimensions, original probability space and measure, SGD model, target rows, control function, confidence level, original-law condition-number bound, and learning rate under consideration. The constant $C$ is the one that lemma supplies for these parameters. The semantic-coherence, input, initialization, bounded-gradient, population-gradient, recursion, confidence-positivity, quantitative, and measurability hypotheses are exactly the hypotheses of that lemma at confidence parameter $\delta$. Its conclusion is the asserted conditional probability bound for the event defined using the original condition number. -/)
  (title := /-- Limitations of SGD for multi-index models beyond statistical queries -/)
  (latexEnv := "theorem")]
theorem main
    (K₁ K₂ K₃ α₂ G : ℝ)
    (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hK₃ : 0 < K₃)
    (hα₂ : 0 < α₂) (hG : 0 < G) :
    ∃ c c' : ℝ, 0 < c ∧ 0 < c' ∧
      ∀ {m d p T : ℕ} {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
        (μ : Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
        (M : sgd_model Ω Θ m d) (U : weight_rows p d)
        (ψ : ℝ → ℝ) (δ κbar η : ℝ),
        ∃ C : ℝ, 0 < C ∧
        (0 < m → 0 < d → 0 < p → 0 < T →
        0 < δ → 1 ≤ κbar → 0 ≤ η →
        sgd_semantic_coherence μ M →
        sub_gaussian_input_assumptions μ M K₁ K₂ α₂ →
        standard_initialization_assumption μ M K₃ →
        bounded_activation_gradients μ M G →
        population_gradient_controlled M U ψ →
        follows_first_layer_sgd M η →
        0 < μ (condition_number_event μ M G κbar T) →
        admissible_sgd_regime C c c' κbar η m p d T δ ψ →
        MeasurableSet (condition_number_event μ M G κbar T) →
        MeasurableSet (uniform_small_alignment_event M U C κbar T δ) →
        (ProbabilityTheory.cond μ
          (condition_number_event μ M G κbar T))
            (uniform_small_alignment_event M U C κbar T δ) ≥
          ENNReal.ofReal (1 - δ)) := by
  exact unconditional_sgd_alignment_argument K₁ K₂ K₃ α₂ G hK₁ hK₂ hK₃ hα₂ hG

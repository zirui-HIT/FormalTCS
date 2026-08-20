import Architect
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Probability.Moments.Variance

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory ProbabilityTheory

@[blueprint "def:euclidean-state"
  (statement := /-- For a dimension $d\in\mathbb{N}$, the state space is the Euclidean vector space $\mathbb{R}^{d}$, represented by functions from $\operatorname{Fin}(d)$ to $\mathbb{R}$. -/)
  (title := /-- Euclidean state space -/)
  (latexEnv := "definition")]
abbrev euclidean_state (d : ℕ) := Fin d → ℝ

@[blueprint "def:log-laplace-transform"
  (statement := /-- Let $d\in\mathbb{N}$ and let $\varphi:\mathbb{R}^{d}\to\mathbb{R}$.  Its log-Laplace transform is
  \[
    \varphi^\sharp(x)=\log\left(\int_{\mathbb{R}^{d}}
      \exp\left(\sum_{i=1}^{d}x_i y_i-\varphi(y)\right)\,dy\right).
  \]
  The integral is taken with respect to Lebesgue measure. -/)
  (title := /-- Log-Laplace transform -/)
  (latexEnv := "definition")]
noncomputable def log_laplace_transform {d : ℕ}
    (φ : euclidean_state d → ℝ) (x : euclidean_state d) : ℝ :=
  Real.log (∫ y, Real.exp (∑ i, x i * y i - φ y))

@[blueprint "def:chi-squared-divergence"
  (statement := /-- Let $\mu$ and $\nu$ be measures on a measurable space.  Their chi-squared divergence is
  \[
    \chi^2(\mu\Vert\nu)
      =\int\left(\frac{d\mu}{d\nu}-1\right)^2\,d\nu,
  \]
  as an extended nonnegative real number in $[0,+\infty]$, where the Radon--Nikodym derivative is interpreted through the canonical Lebesgue decomposition. -/)
  (title := /-- Chi-squared divergence -/)
  (latexEnv := "definition")]
noncomputable def chi_squared_divergence {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (((μ.rnDeriv ν x).toReal - 1) ^ 2) ∂ν

@[blueprint "def:coordinate-gradient"
  (statement := /-- For $f:\mathbb{R}^{d}\to\mathbb{R}$ and $x\in\mathbb{R}^{d}$, the coordinate gradient is the vector whose $i$th coordinate is the Fréchet derivative of $f$ at $x$ evaluated on the $i$th standard basis vector. -/)
  (title := /-- Coordinate gradient -/)
  (latexEnv := "definition")]
noncomputable def coordinate_gradient {d : ℕ}
    (f : euclidean_state d → ℝ) (x : euclidean_state d) : euclidean_state d :=
  fun i => (fderiv ℝ f x) (fun j => if j = i then 1 else 0)

@[blueprint "def:coordinate-hessian"
  (statement := /-- For $f:\mathbb{R}^{d}\to\mathbb{R}$ and $x\in\mathbb{R}^{d}$, the coordinate Hessian is the matrix obtained by differentiating each coordinate of the gradient in each standard coordinate direction. -/)
  (title := /-- Coordinate Hessian -/)
  (latexEnv := "definition")]
noncomputable def coordinate_hessian {d : ℕ}
    (f : euclidean_state d → ℝ) (x : euclidean_state d) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j =>
    (fderiv ℝ (fun z => coordinate_gradient f z j) x)
      (fun k => if k = i then 1 else 0)

@[blueprint "def:mirror-dirichlet-form"
  (statement := /-- Let $\pi$ be a measure on $\mathbb{R}^{d}$, and let $\psi,f:\mathbb{R}^{d}\to\mathbb{R}$.  The mirror Dirichlet form is
  \[
    \mathcal{E}_{\pi,\psi}(f)
      =\int \nabla f(x)^{\mathsf T}
        \bigl(\nabla^2\psi(x)\bigr)^{-1}\nabla f(x)\,d\pi(x),
  \]
  with the inverse interpreted as the nonsingular inverse of the coordinate Hessian. -/)
  (title := /-- Mirror Dirichlet form -/)
  (latexEnv := "definition")]
noncomputable def mirror_dirichlet_form {d : ℕ}
    (π : Measure (euclidean_state d)) (ψ f : euclidean_state d → ℝ) : ℝ :=
  ∫ x, ∑ i, coordinate_gradient f x i *
    ∑ j, (coordinate_hessian ψ x)⁻¹ i j * coordinate_gradient f x j ∂π

@[blueprint "def:functional-poincare"
  (statement := /-- Let $\pi$ be a measure on $\mathbb{R}^{d}$, let $\psi:\mathbb{R}^{d}\to\mathbb{R}$, and let $\alpha\in\mathbb{R}$.  The measure $\pi$ satisfies the $\alpha$--$\psi$ Poincaré inequality if every continuously differentiable, square-integrable $f:\mathbb{R}^{d}\to\mathbb{R}$ satisfies
  \[
    \operatorname{Var}_{\pi}(f)
      \leq \alpha^{-1}\mathcal{E}_{\pi,\psi}(f).
  \]
  The Dirichlet form is the one in \cref{def:mirror-dirichlet-form}. -/)
  (title := /-- Functional Poincaré inequality -/)
  (latexEnv := "definition")]
def functional_poincare {d : ℕ} (π : Measure (euclidean_state d))
    (ψ : euclidean_state d → ℝ) (α : ℝ) : Prop :=
  ∀ f : euclidean_state d → ℝ,
    ContDiff ℝ 1 f → MeasureTheory.MemLp f 2 π →
      ProbabilityTheory.variance f π ≤ α⁻¹ * mirror_dirichlet_form π ψ f

@[blueprint "def:normalized-measure"
  (statement := /-- For a measure $\mu$, its normalization is $(\mu(\Omega))^{-1}\mu$.  This convention is total: if the mass is zero or infinite, the extended-nonnegative scalar operations determine the resulting measure. -/)
  (title := /-- Normalization of a measure -/)
  (latexEnv := "definition")]
noncomputable def normalized_measure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) : Measure Ω :=
  (μ Set.univ)⁻¹ • μ

@[blueprint "def:gibbs-base-measure"
  (statement := /-- Given $\varphi:\mathbb{R}^{d}\to\mathbb{R}$, the unnormalized Gibbs base measure has density $\exp(-\varphi)$ with respect to Lebesgue measure. -/)
  (title := /-- Gibbs base measure -/)
  (latexEnv := "definition")]
noncomputable def gibbs_base_measure {d : ℕ}
    (φ : euclidean_state d → ℝ) : Measure (euclidean_state d) :=
  (volume : Measure (euclidean_state d)).withDensity
    (fun x => ENNReal.ofReal (Real.exp (-φ x)))

@[blueprint "def:measure-convolution-power"
  (statement := /-- For a measure $\rho$ on $\mathbb{R}^{d}$ and $\tau\in\mathbb{N}$, define $\rho^{*\tau}$ recursively by $\rho^{*0}=\delta_0$ and $\rho^{*(\tau+1)}=\rho^{*\tau}*\rho$. -/)
  (title := /-- Convolution power of a measure -/)
  (latexEnv := "definition")]
noncomputable def measure_convolution_power {d : ℕ}
    (ρ : Measure (euclidean_state d)) :
    ℕ → Measure (euclidean_state d)
  | 0 => Measure.dirac 0
  | n + 1 => (measure_convolution_power ρ n).conv ρ

@[blueprint "def:dual-conditional"
  (statement := /-- Let $\varphi:\mathbb{R}^{d}\to\mathbb{R}$ and $\tau\in\mathbb{N}$.  Conditional on $X=x$, the LLT-Prox auxiliary variable has the normalized exponential tilt by $y\mapsto\langle x,y\rangle$ of the $\tau$-fold convolution of the Gibbs base measure. -/)
  (title := /-- Auxiliary conditional law -/)
  (latexEnv := "definition")]
noncomputable def dual_conditional {d : ℕ}
    (φ : euclidean_state d → ℝ) (τ : ℕ) (x : euclidean_state d) :
    Measure (euclidean_state d) :=
  normalized_measure
    ((measure_convolution_power (gibbs_base_measure φ) τ).withDensity
      (fun y => ENNReal.ofReal (Real.exp (∑ i, x i * y i))))

@[blueprint "def:primal-conditional"
  (statement := /-- Let $\pi$ be the target measure, let $\psi:\mathbb{R}^{d}\to\mathbb{R}$, and let $\tau\in\mathbb{N}$.  Conditional on $Y=y$, the next LLT-Prox state has the normalized density
  \[
    x\longmapsto \exp\bigl(\langle x,y\rangle-\tau\psi(x)\bigr)
  \]
  with respect to $\pi$. -/)
  (title := /-- Primal conditional law -/)
  (latexEnv := "definition")]
noncomputable def primal_conditional {d : ℕ}
    (ψ : euclidean_state d → ℝ) (π : Measure (euclidean_state d))
    (τ : ℕ) (y : euclidean_state d) : Measure (euclidean_state d) :=
  normalized_measure
    (π.withDensity
      (fun x => ENNReal.ofReal
        (Real.exp (∑ i, x i * y i - (τ : ℝ) * ψ x))))

@[blueprint "def:dual-marginal"
  (statement := /-- The auxiliary marginal associated with $\varphi,\psi,\pi$, and $\tau$ is obtained by weighting the $\tau$-fold convolution of the Gibbs base measure at $y$ by
  \[
    \int\exp\bigl(\langle x,y\rangle-\tau\psi(x)\bigr)\,d\pi(x).
  \]
  This is the $Y$-marginal of the joint density used by LLT-Prox. -/)
  (title := /-- Auxiliary marginal of the LLT-Prox coupling -/)
  (latexEnv := "definition")]
noncomputable def dual_marginal {d : ℕ}
    (φ ψ : euclidean_state d → ℝ) (π : Measure (euclidean_state d))
    (τ : ℕ) : Measure (euclidean_state d) :=
  (measure_convolution_power (gibbs_base_measure φ) τ).withDensity
    (fun y => ∫⁻ x, ENNReal.ofReal
      (Real.exp (∑ i, x i * y i - (τ : ℝ) * ψ x)) ∂π)

@[blueprint "def:forward-conditional-expectation"
  (statement := /-- The forward conditional-expectation operator sends a real function $g$ of the auxiliary variable to
  \[
    (Kg)(x)=\int g(y)\,\widetilde{\pi}(dy\mid X=x),
  \]
  where the conditional law is \cref{def:dual-conditional}. -/)
  (title := /-- Forward conditional-expectation operator -/)
  (latexEnv := "definition")]
noncomputable def forward_conditional_expectation {d : ℕ}
    (φ : euclidean_state d → ℝ) (τ : ℕ)
    (g : euclidean_state d → ℝ) (x : euclidean_state d) : ℝ :=
  ∫ y, g y ∂(dual_conditional φ τ x)

@[blueprint "def:backward-conditional-expectation"
  (statement := /-- The backward conditional-expectation operator sends a real function $f$ of the primal variable to
  \[
    (K^\dagger f)(y)=\int f(x)\,\widetilde{\pi}(dx\mid Y=y),
  \]
  where the conditional law is \cref{def:primal-conditional}. -/)
  (title := /-- Backward conditional-expectation operator -/)
  (latexEnv := "definition")]
noncomputable def backward_conditional_expectation {d : ℕ}
    (ψ : euclidean_state d → ℝ) (π : Measure (euclidean_state d))
    (τ : ℕ) (f : euclidean_state d → ℝ) (y : euclidean_state d) : ℝ :=
  ∫ x, f x ∂(primal_conditional ψ π τ y)

@[blueprint "def:llt-prox-step"
  (statement := /-- Measures $\mu$ and $\nu$ form one LLT-Prox step if, for every measurable set $A$, the mass $\nu(A)$ is obtained by first drawing $x$ from $\mu$, then drawing $y$ from the auxiliary conditional law, and finally drawing the new state from the primal conditional law:
  \[
    \nu(A)=\int\!\!\int
      \widetilde{\pi}(A\mid Y=y)\,
      \widetilde{\pi}(dy\mid X=x)\,d\mu(x).
  \] -/)
  (title := /-- One LLT-Prox update -/)
  (latexEnv := "definition")]
def llt_prox_step {d : ℕ}
    (φ ψ : euclidean_state d → ℝ) (π : Measure (euclidean_state d))
    (τ : ℕ) (μ ν : Measure (euclidean_state d)) : Prop :=
  ∀ A : Set (euclidean_state d), MeasurableSet A →
    ν A = ∫⁻ x, ∫⁻ y, primal_conditional ψ π τ y A
      ∂(dual_conditional φ τ x) ∂μ

@[blueprint "def:llt-prox-trajectory"
  (statement := /-- A sequence $(\mu_k)_{k\geq 0}$ is an LLT-Prox trajectory for $(\varphi,\psi,\pi,\tau)$ if every $\mu_k$ is a probability measure and each consecutive pair $(\mu_k,\mu_{k+1})$ satisfies the update rule in \cref{def:llt-prox-step}. -/)
  (title := /-- LLT-Prox trajectory -/)
  (latexEnv := "definition")]
def llt_prox_trajectory {d : ℕ}
    (φ ψ : euclidean_state d → ℝ) (π : Measure (euclidean_state d))
    (τ : ℕ) (μ : ℕ → Measure (euclidean_state d)) : Prop :=
  (∀ k, IsProbabilityMeasure (μ k)) ∧
    ∀ k, llt_prox_step φ ψ π τ (μ k) (μ (k + 1))

@[blueprint "lem:llt-prox-total-variance"
  (statement := /-- Let $d,\tau\in\mathbb{N}$ with $\tau>0$, let $\varphi,\psi,g:\mathbb{R}^{d}\to\mathbb{R}$ satisfy $\psi=\varphi^\sharp$, and let $\pi$ be a probability measure on $\mathbb{R}^{d}$.  For each $x\in\mathbb{R}^{d}$, let $\widetilde{\pi}^{Y\mid X=x}$ be the probability measure in \cref{def:dual-conditional}.  Suppose that $x\mapsto\widetilde{\pi}^{Y\mid X=x}$ is $\pi$-almost everywhere measurable as a measure-valued map and that
  \[
    \widetilde{\pi}^{Y}
      =\int \widetilde{\pi}^{Y\mid X=x}\,d\pi(x)
  \]
  as measures.  If $g$ is square-integrable under $\widetilde{\pi}^{Y}$, then
  \[
    \operatorname{Var}_{\widetilde{\pi}^{Y}}(g)
      =\int \operatorname{Var}_{\widetilde{\pi}^{Y\mid X=x}}(g)\,d\pi(x)
       +\operatorname{Var}_{\pi}(Kg).
  \] -/)
  (proof := /-- Write $Q_x$ for the probability measure in \cref{def:dual-conditional}, $\nu$ for the measure in \cref{def:dual-marginal}, and $G(x)=\int g\,dQ_x$ for the function in \cref{def:forward-conditional-expectation}.  The marginal identity gives $\nu=\pi\mathbin{\operatorname{bind}}Q$, and the probability assumptions imply that this bind is a probability measure.

  We first justify integration through the bind.  If a real-valued function $f$ is integrable under $\pi\mathbin{\operatorname{bind}}Q$, decompose its integral into the lower integrals of its positive and negative parts.  The lower-integral bind formula and the assumed almost-everywhere measurability of $x\mapsto Q_x$ show that, for $\pi$-almost every $x$, $f$ is integrable under $Q_x$; they also show that $x\mapsto\int f\,dQ_x$ is integrable under $\pi$.  Applying the same positive--negative decomposition on each fibre and then integrating yields
  \[
    \int f\,d\nu=\int\!\left(\int f\,dQ_x\right)d\pi(x).
  \]

  Since $g\in L^2(\nu)$, both $g$ and $g^2$ are integrable.  Applying the preceding identity to these two functions gives, respectively,
  \[
    \int g^2\,d\nu=\int\!\left(\int g^2\,dQ_x\right)d\pi(x),
    \qquad
    \int g\,d\nu=\int G\,d\pi.
  \]
  It also gives $g\in L^2(Q_x)$ for $\pi$-almost every $x$ and integrability of $x\mapsto\int g^2\,dQ_x$.  For such $x$, nonnegativity of $\operatorname{Var}_{Q_x}(g)$ and the second-moment formula imply
  \[
    G(x)^2\leq\int g^2\,dQ_x.
  \]
  Hence $G^2$ is integrable under $\pi$, so $G\in L^2(\pi)$.

  Expanding the variance of $g$ under $\nu$, the variance of $G$ under $\pi$, and the conditional variances under $Q_x$ by their second-moment formulas, and using the two bind identities above, reduces the desired equality to
  \[
    \operatorname{Var}_{\nu}(g)
      =\int\!\left(\int g^2\,dQ_x-G(x)^2\right)d\pi(x)
       +\left(\int G^2\,d\pi-\left(\int G\,d\pi\right)^2\right).
  \]
  The two occurrences of $\int G^2\,d\pi$ cancel, proving the asserted identity. -/)
  (title := /-- Total variance for the LLT-Prox coupling -/)
  (latexEnv := "lemma")]
lemma llt_prox_total_variance {d τ : ℕ}
    {φ ψ g : euclidean_state d → ℝ}
    {π : Measure (euclidean_state d)}
    (hτ : 0 < τ) (hψ : ψ = log_laplace_transform φ)
    (hπ : IsProbabilityMeasure π)
    (hcond_prob : ∀ x, IsProbabilityMeasure (dual_conditional φ τ x))
    (hcond_meas : AEMeasurable (fun x => dual_conditional φ τ x) π)
    (hmarginal : dual_marginal φ ψ π τ =
      Measure.bind π (fun x => dual_conditional φ τ x))
    (hg : MeasureTheory.MemLp g 2 (dual_marginal φ ψ π τ)) :
    ProbabilityTheory.variance g (dual_marginal φ ψ π τ) =
      (∫ x, ProbabilityTheory.variance g (dual_conditional φ τ x) ∂π) +
      ProbabilityTheory.variance
        (forward_conditional_expectation φ τ g) π := by
  letI : IsProbabilityMeasure π := hπ
  have integral_bind_real {f : euclidean_state d → ℝ}
      (hf : Integrable f
        (Measure.bind π (fun x => dual_conditional φ τ x))) :
      (∀ᵐ x ∂π, Integrable f (dual_conditional φ τ x)) ∧
        Integrable (fun x => ∫ y, f y ∂(dual_conditional φ τ x)) π ∧
          (∫ y, f y ∂(Measure.bind π (fun x => dual_conditional φ τ x))) =
            ∫ x, ∫ y, f y ∂(dual_conditional φ τ x) ∂π := by
    have hf_ae : AEMeasurable f
        (Measure.bind π (fun x => dual_conditional φ τ x)) :=
      hf.aestronglyMeasurable.aemeasurable
    have hpos_ae : AEMeasurable (fun y => ENNReal.ofReal (f y))
        (Measure.bind π (fun x => dual_conditional φ τ x)) :=
      hf_ae.ennreal_ofReal
    have hneg_ae : AEMeasurable (fun y => ENNReal.ofReal (-f y))
        (Measure.bind π (fun x => dual_conditional φ τ x)) :=
      hf_ae.neg.ennreal_ofReal
    have hnorm_ae : AEMeasurable (fun y => ‖f y‖ₑ)
        (Measure.bind π (fun x => dual_conditional φ τ x)) :=
      hf_ae.enorm
    have hpos_outer_ae : AEMeasurable
        (fun x => ∫⁻ y, ENNReal.ofReal (f y) ∂(dual_conditional φ τ x)) π :=
      (Measure.aemeasurable_lintegral hpos_ae).comp_aemeasurable hcond_meas
    have hneg_outer_ae : AEMeasurable
        (fun x => ∫⁻ y, ENNReal.ofReal (-f y) ∂(dual_conditional φ τ x)) π :=
      (Measure.aemeasurable_lintegral hneg_ae).comp_aemeasurable hcond_meas
    have hnorm_outer_ae : AEMeasurable
        (fun x => ∫⁻ y, ‖f y‖ₑ ∂(dual_conditional φ τ x)) π :=
      (Measure.aemeasurable_lintegral hnorm_ae).comp_aemeasurable hcond_meas
    have hpos_ne_top :
        (∫⁻ x, ∫⁻ y, ENNReal.ofReal (f y) ∂(dual_conditional φ τ x) ∂π) ≠ ⊤ := by
      rw [← Measure.lintegral_bind hcond_meas hpos_ae]
      exact ne_of_lt hf.lintegral_lt_top
    have hneg_ne_top :
        (∫⁻ x, ∫⁻ y, ENNReal.ofReal (-f y) ∂(dual_conditional φ τ x) ∂π) ≠ ⊤ := by
      rw [← Measure.lintegral_bind hcond_meas hneg_ae]
      exact ne_of_lt hf.neg.lintegral_lt_top
    have hnorm_ne_top :
        (∫⁻ x, ∫⁻ y, ‖f y‖ₑ ∂(dual_conditional φ τ x) ∂π) ≠ ⊤ := by
      rw [← Measure.lintegral_bind hcond_meas hnorm_ae]
      exact ne_of_lt hf.hasFiniteIntegral
    have hpos_lt_top := ae_lt_top' hpos_outer_ae hpos_ne_top
    have hneg_lt_top := ae_lt_top' hneg_outer_ae hneg_ne_top
    have hnorm_lt_top := ae_lt_top' hnorm_outer_ae hnorm_ne_top
    have hf_cond_ae := hcond_meas.ae_of_bind hf_ae
    have hf_cond_int : ∀ᵐ x ∂π, Integrable f (dual_conditional φ τ x) := by
      filter_upwards [hf_cond_ae, hnorm_lt_top] with x hfx hnormx
      exact ⟨hfx.aestronglyMeasurable, hnormx⟩
    have hpos_int := integrable_toReal_of_lintegral_ne_top
      hpos_outer_ae hpos_ne_top
    have hneg_int := integrable_toReal_of_lintegral_ne_top
      hneg_outer_ae hneg_ne_top
    have hinner_eq :
        (fun x => ∫ y, f y ∂(dual_conditional φ τ x)) =ᵐ[π]
          (fun x => (∫⁻ y, ENNReal.ofReal (f y)
              ∂(dual_conditional φ τ x)).toReal -
            (∫⁻ y, ENNReal.ofReal (-f y)
              ∂(dual_conditional φ τ x)).toReal) := by
      filter_upwards [hf_cond_int] with x hfx
      exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfx
    refine ⟨hf_cond_int, (hpos_int.sub hneg_int).congr hinner_eq.symm, ?_⟩
    calc
      (∫ y, f y ∂(Measure.bind π (fun x => dual_conditional φ τ x))) =
          (∫⁻ y, ENNReal.ofReal (f y)
              ∂(Measure.bind π (fun x => dual_conditional φ τ x))).toReal -
            (∫⁻ y, ENNReal.ofReal (-f y)
              ∂(Measure.bind π (fun x => dual_conditional φ τ x))).toReal :=
        integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf
      _ = (∫⁻ x, ∫⁻ y, ENNReal.ofReal (f y)
              ∂(dual_conditional φ τ x) ∂π).toReal -
            (∫⁻ x, ∫⁻ y, ENNReal.ofReal (-f y)
              ∂(dual_conditional φ τ x) ∂π).toReal := by
        rw [Measure.lintegral_bind hcond_meas hpos_ae,
          Measure.lintegral_bind hcond_meas hneg_ae]
      _ = (∫ x, (∫⁻ y, ENNReal.ofReal (f y)
              ∂(dual_conditional φ τ x)).toReal ∂π) -
            ∫ x, (∫⁻ y, ENNReal.ofReal (-f y)
              ∂(dual_conditional φ τ x)).toReal ∂π := by
        rw [integral_toReal hpos_outer_ae hpos_lt_top,
          integral_toReal hneg_outer_ae hneg_lt_top]
      _ = ∫ x, ((∫⁻ y, ENNReal.ofReal (f y)
              ∂(dual_conditional φ τ x)).toReal -
            (∫⁻ y, ENNReal.ofReal (-f y)
              ∂(dual_conditional φ τ x)).toReal) ∂π :=
        (integral_sub hpos_int hneg_int).symm
      _ = ∫ x, ∫ y, f y ∂(dual_conditional φ τ x) ∂π := by
        exact integral_congr_ae hinner_eq.symm
  rw [hmarginal] at hg ⊢
  letI : IsProbabilityMeasure
      (Measure.bind π (fun x => dual_conditional φ τ x)) := by
    simp only [isProbabilityMeasure_iff, MeasurableSet.univ,
      Measure.bind_apply _ hcond_meas]
    have hprob : ∀ᵐ x ∂π,
        IsProbabilityMeasure (dual_conditional φ τ x) :=
      Filter.Eventually.of_forall hcond_prob
    simp_rw [isProbabilityMeasure_iff] at hprob
    exact lintegral_eq_const hprob
  have hg_int := hg.integrable one_le_two
  have hmean := integral_bind_real hg_int
  have hsecond := integral_bind_real hg.integrable_sq
  have hg_cond : ∀ᵐ x ∂π, MemLp g 2 (dual_conditional φ τ x) := by
    have hg_cond_ae := hcond_meas.ae_of_bind hg.aemeasurable
    filter_upwards [hg_cond_ae, hsecond.1] with x hgx_ae hgx_sq
    rw [memLp_two_iff_integrable_sq hgx_ae.aestronglyMeasurable]
    exact hgx_sq
  have hK_int : Integrable (forward_conditional_expectation φ τ g) π := by
    change Integrable
      (fun x => ∫ y, g y ∂(dual_conditional φ τ x)) π
    exact hmean.2.1
  have hK_sq_le : ∀ᵐ x ∂π,
      (forward_conditional_expectation φ τ g x) ^ 2 ≤
        ∫ y, g y ^ 2 ∂(dual_conditional φ τ x) := by
    filter_upwards [hg_cond] with x hgx
    letI : IsProbabilityMeasure (dual_conditional φ τ x) := hcond_prob x
    have hv := variance_nonneg g (dual_conditional φ τ x)
    rw [variance_eq_sub hgx] at hv
    simpa [forward_conditional_expectation] using (sub_nonneg.mp hv)
  have hK_sq_int : Integrable
      (fun x => (forward_conditional_expectation φ τ g x) ^ 2) π := by
    apply Integrable.mono' hsecond.2.1
    · exact hK_int.aestronglyMeasurable.pow 2
    · filter_upwards [hK_sq_le] with x hx
      simpa [Real.norm_eq_abs, abs_sq] using hx
  have hK_memLp : MemLp (forward_conditional_expectation φ τ g) 2 π := by
    rw [memLp_two_iff_integrable_sq hK_int.aestronglyMeasurable]
    exact hK_sq_int
  have hinner_sq_int : Integrable
      (fun x => (∫ y, g y ∂(dual_conditional φ τ x)) ^ 2) π := by
    change Integrable
      (fun x => (∫ y, g y ∂(dual_conditional φ τ x)) ^ 2) π at hK_sq_int
    exact hK_sq_int
  have hvar_cond :
      (fun x => variance g (dual_conditional φ τ x)) =ᵐ[π]
        (fun x => (∫ y, g y ^ 2 ∂(dual_conditional φ τ x)) -
          (∫ y, g y ∂(dual_conditional φ τ x)) ^ 2) := by
    filter_upwards [hg_cond] with x hgx
    letI : IsProbabilityMeasure (dual_conditional φ τ x) := hcond_prob x
    exact variance_eq_sub hgx
  rw [variance_eq_sub hg, variance_eq_sub hK_memLp,
    integral_congr_ae hvar_cond,
    integral_sub hsecond.2.1 hinner_sq_int]
  simp only [Pi.pow_apply]
  rw [hsecond.2.2, hmean.2.2]
  simp only [forward_conditional_expectation]
  ring

@[blueprint "lem:llt-prox-dual-poincare-comparison"
  (statement := /-- Let $d,\tau\in\mathbb{N}$ and $\alpha\in\mathbb{R}$ satisfy $\tau>0$ and $\alpha>0$.  Let $\varphi,\psi,g:\mathbb{R}^{d}\to\mathbb{R}$, assume that $\varphi$ is convex and $\psi=\varphi^\sharp$, and let $\pi$ be a probability measure on $\mathbb{R}^{d}$ satisfying the $\alpha$--$\psi$ Poincaré inequality.  Suppose that $g$ is continuously differentiable and square-integrable under the auxiliary marginal.  Define $G=Kg$, and suppose in addition that $G$ is continuously differentiable and square-integrable under $\pi$, and that
  \[
    \mathcal{E}_{\pi,\psi}(G)
      \leq \tau\int
        \operatorname{Var}_{\widetilde{\pi}^{Y\mid X=x}}(g)\,d\pi(x).
  \]
  Then
  \[
    \operatorname{Var}_{\pi}(Kg)
      \leq \frac{\tau}{\alpha}
        \int\operatorname{Var}_{\widetilde{\pi}^{Y\mid X=x}}(g)\,d\pi(x).
  \] -/)
  (proof := /-- Set $G=Kg$ using \cref{def:forward-conditional-expectation}.  The asserted regularity and square-integrability of $G$ permit its substitution into the functional Poincaré inequality in \cref{def:functional-poincare}, and hence
  \[
    \operatorname{Var}_{\pi}(G)
      \leq \alpha^{-1}\mathcal{E}_{\pi,\psi}(G).
  \]
  By the assumed comparison for the mirror Dirichlet form in \cref{def:mirror-dirichlet-form}, the right-hand side is at most
  \[
    \alpha^{-1}\tau\int
      \operatorname{Var}_{\widetilde{\pi}^{Y\mid X=x}}(g)\,d\pi(x).
  \]
  Since $\alpha>0$, one has $\alpha^{-1}\tau=\tau/\alpha$, which gives the claimed inequality. -/)
  (title := /-- Dual-Poincaré conditional variance comparison -/)
  (latexEnv := "lemma")]
lemma llt_prox_dual_poincare_comparison {d τ : ℕ} {α : ℝ}
    {φ ψ g : euclidean_state d → ℝ}
    {π : Measure (euclidean_state d)}
    (hconv : ConvexOn ℝ Set.univ φ)
    (hψ : ψ = log_laplace_transform φ)
    (hτ : 0 < τ) (hα : 0 < α)
    (hπ : IsProbabilityMeasure π)
    (hPI : functional_poincare π ψ α)
    (hg_smooth : ContDiff ℝ 1 g)
    (hg : MeasureTheory.MemLp g 2 (dual_marginal φ ψ π τ))
    (hG_smooth : ContDiff ℝ 1 (forward_conditional_expectation φ τ g))
    (hG : MeasureTheory.MemLp
      (forward_conditional_expectation φ τ g) 2 π)
    (hdirichlet : mirror_dirichlet_form π ψ
      (forward_conditional_expectation φ τ g) ≤
        (τ : ℝ) *
          ∫ x, ProbabilityTheory.variance g (dual_conditional φ τ x) ∂π) :
    ProbabilityTheory.variance
        (forward_conditional_expectation φ τ g) π ≤
      (τ : ℝ) / α *
        ∫ x, ProbabilityTheory.variance g (dual_conditional φ τ x) ∂π := by
  refine le_trans (hPI _ hG_smooth hG) ?_
  calc
    _ ≤ α⁻¹ * ((τ : ℝ) *
        (∫ x, ProbabilityTheory.variance g (dual_conditional φ τ x) ∂π)) :=
      mul_le_mul_of_nonneg_left hdirichlet (inv_nonneg.mpr hα.le)
    _ = (τ : ℝ) / α *
        (∫ x, ProbabilityTheory.variance g (dual_conditional φ τ x) ∂π) := by
      ring

@[blueprint "lem:llt-prox-smooth-forward-contraction"
  (statement := /-- Let $d,\tau\in\mathbb{N}$ and $\alpha\in\mathbb{R}$ satisfy $\tau>0$ and $\alpha>0$.  Let $\varphi,\psi,g:\mathbb{R}^{d}\to\mathbb{R}$, assume that $\varphi$ is convex and $\psi=\varphi^\sharp$, and let $\pi$ be a probability measure satisfying the $\alpha$--$\psi$ Poincaré inequality.  For every $x\in\mathbb{R}^{d}$, assume that the conditional measure $Q_x=\widetilde{\pi}^{Y\mid X=x}$ is a probability measure; assume that $x\mapsto Q_x$ is $\pi$-almost-everywhere measurable and that $\widetilde{\pi}^{Y}=\int Q_x\,d\pi(x)$ in the sense of measure bind.  Suppose that $g$ is $C^1$ and belongs to $L^2(\widetilde{\pi}^{Y})$.  Set $G=Kg$, assume that $G$ is $C^1$ and belongs to $L^2(\pi)$, and suppose that
  \[
    \mathcal{E}_{\pi,\psi}(G)
      \leq \tau\int
        \operatorname{Var}_{Q_x}(g)\,d\pi(x).
  \]
  Then
  \[
    \operatorname{Var}_{\pi}(Kg)
      \leq \frac{1}{1+\alpha/\tau}
        \operatorname{Var}_{\widetilde{\pi}^{Y}}(g).
  \] -/)
  (proof := /-- By \cref{lem:llt-prox-total-variance}, write
  \[
    \operatorname{Var}_{\widetilde{\pi}^{Y}}(g)=A+B,
  \]
  where $A$ is the mean conditional variance and $B=\operatorname{Var}_{\pi}(Kg)$.  By \cref{lem:llt-prox-dual-poincare-comparison}, $B\leq(\tau/\alpha)A$.  Since $\alpha,\tau>0$, this inequality is equivalent to $(1+\alpha/\tau)B\leq A+B$, which is the claimed contraction. -/)
  (title := /-- Smooth forward variance contraction -/)
  (latexEnv := "lemma")]
lemma llt_prox_smooth_forward_contraction {d τ : ℕ} {α : ℝ}
    {φ ψ g : euclidean_state d → ℝ}
    {π : Measure (euclidean_state d)}
    (hconv : ConvexOn ℝ Set.univ φ)
    (hψ : ψ = log_laplace_transform φ)
    (hτ : 0 < τ) (hα : 0 < α)
    (hπ : IsProbabilityMeasure π)
    (hPI : functional_poincare π ψ α)
    (hcond_prob : ∀ x, IsProbabilityMeasure (dual_conditional φ τ x))
    (hcond_meas : AEMeasurable (fun x => dual_conditional φ τ x) π)
    (hmarginal : dual_marginal φ ψ π τ =
      Measure.bind π (fun x => dual_conditional φ τ x))
    (hg_smooth : ContDiff ℝ 1 g)
    (hg : MeasureTheory.MemLp g 2 (dual_marginal φ ψ π τ))
    (hG_smooth : ContDiff ℝ 1 (forward_conditional_expectation φ τ g))
    (hG : MeasureTheory.MemLp
      (forward_conditional_expectation φ τ g) 2 π)
    (hdirichlet : mirror_dirichlet_form π ψ
      (forward_conditional_expectation φ τ g) ≤
        (τ : ℝ) *
          ∫ x, ProbabilityTheory.variance g (dual_conditional φ τ x) ∂π) :
    ProbabilityTheory.variance
        (forward_conditional_expectation φ τ g) π ≤
      1 / (1 + α / (τ : ℝ)) *
        ProbabilityTheory.variance g (dual_marginal φ ψ π τ) := by
  let A : ℝ :=
    ∫ x, ProbabilityTheory.variance g (dual_conditional φ τ x) ∂π
  let B : ℝ :=
    ProbabilityTheory.variance
      (forward_conditional_expectation φ τ g) π
  have htotal :
      ProbabilityTheory.variance g (dual_marginal φ ψ π τ) = A + B :=
    llt_prox_total_variance hτ hψ hπ hcond_prob hcond_meas hmarginal hg
  have hcomparison : B ≤ (τ : ℝ) / α * A :=
    llt_prox_dual_poincare_comparison hconv hψ hτ hα hπ hPI
      hg_smooth hg hG_smooth hG hdirichlet
  have hτ_real : (0 : ℝ) < (τ : ℝ) := by
    exact_mod_cast hτ
  have hscaled : α * B ≤ (τ : ℝ) * A := by
    calc
      α * B ≤ α * ((τ : ℝ) / α * A) :=
        mul_le_mul_of_nonneg_left hcomparison hα.le
      _ = (τ : ℝ) * A := by
        field_simp
  rw [htotal]
  have hden : 0 < 1 + α / (τ : ℝ) := by
    positivity
  have hfinal : B ≤ (A + B) / (1 + α / (τ : ℝ)) :=
    (le_div_iff₀ hden).2 <| by
      calc
        B * (1 + α / (τ : ℝ)) =
            B + (α * B) / (τ : ℝ) := by
          ring
        _ ≤ B + ((τ : ℝ) * A) / (τ : ℝ) :=
          by
            simpa [add_comm] using
              add_le_add_left
                (div_le_div_of_nonneg_right hscaled hτ_real.le) B
        _ = A + B := by
          field_simp
          ring
  simpa [B, div_eq_mul_inv, mul_comm] using hfinal

@[blueprint "lem:llt-prox-forward-contraction"
  (statement := /-- Let $\varphi:\mathbb{R}^{d}\to\mathbb{R}$ be convex, let $\psi=\varphi^\sharp$, let $\tau\in\mathbb{N}$ and $\alpha\in\mathbb{R}$ be positive, and suppose that $\pi$ is a probability measure satisfying the $\alpha$--$\psi$ Poincaré inequality.  Assume that, for every $x\in\mathbb{R}^{d}$, the measure $\widetilde{\pi}^{Y\mid X=x}$ is a probability measure, that the map $x\mapsto\widetilde{\pi}^{Y\mid X=x}$ is $\pi$-almost-everywhere measurable, and that
  \[
    \widetilde{\pi}^{Y}
      =\int \widetilde{\pi}^{Y\mid X=x}\,d\pi(x).
  \]
  Let $g:\mathbb{R}^{d}\to\mathbb{R}$ be continuously differentiable and square-integrable with respect to $\widetilde{\pi}^{Y}$.  Suppose that $Kg$ is continuously differentiable and square-integrable with respect to $\pi$, and assume the kernel-specific Dirichlet comparison
  \[
    \mathcal{E}_{\pi,\psi}(Kg)
      \leq \tau\int
        \operatorname{Var}_{\widetilde{\pi}^{Y\mid X=x}}(g)\,d\pi(x).
  \]
  Then
  \[
    \operatorname{Var}_{\pi}(Kg)
      \leq \frac{1}{1+\alpha/\tau}
        \operatorname{Var}_{\widetilde{\pi}^{Y}}(g).
  \] -/)
  (proof := /-- The hypotheses are precisely those of \cref{lem:llt-prox-smooth-forward-contraction}; applying that lemma to $g$ gives the asserted variance bound. -/)
  (title := /-- Forward variance contraction under the Dirichlet comparison -/)
  (latexEnv := "lemma")]
lemma llt_prox_forward_contraction {d τ : ℕ} {α : ℝ}
    {φ ψ g : euclidean_state d → ℝ}
    {π : Measure (euclidean_state d)}
    (hconv : ConvexOn ℝ Set.univ φ)
    (hψ : ψ = log_laplace_transform φ)
    (hτ : 0 < τ) (hα : 0 < α)
    (hπ : IsProbabilityMeasure π)
    (hPI : functional_poincare π ψ α)
    (hcond_prob : ∀ x, IsProbabilityMeasure (dual_conditional φ τ x))
    (hcond_meas : AEMeasurable (fun x => dual_conditional φ τ x) π)
    (hmarginal : dual_marginal φ ψ π τ =
      Measure.bind π (fun x => dual_conditional φ τ x))
    (hg_smooth : ContDiff ℝ 1 g)
    (hg : MeasureTheory.MemLp g 2 (dual_marginal φ ψ π τ))
    (hG_smooth : ContDiff ℝ 1 (forward_conditional_expectation φ τ g))
    (hG : MeasureTheory.MemLp
      (forward_conditional_expectation φ τ g) 2 π)
    (hdirichlet : mirror_dirichlet_form π ψ
      (forward_conditional_expectation φ τ g) ≤
        (τ : ℝ) *
          ∫ x, ProbabilityTheory.variance g (dual_conditional φ τ x) ∂π) :
    ProbabilityTheory.variance
        (forward_conditional_expectation φ τ g) π ≤
      1 / (1 + α / (τ : ℝ)) *
        ProbabilityTheory.variance g (dual_marginal φ ψ π τ) := by
  exact llt_prox_smooth_forward_contraction hconv hψ hτ hα hπ hPI
    hcond_prob hcond_meas hmarginal hg_smooth hg hG_smooth hG hdirichlet

@[blueprint "lem:llt-prox-backward-contraction"
  (statement := /-- Let $\varphi:\mathbb{R}^{d}\to\mathbb{R}$ be convex, let $\psi=\varphi^\sharp$, let $\tau\in\mathbb{N}$ and $\alpha\in\mathbb{R}$ be positive, and suppose that $\pi$ is a probability measure satisfying the $\alpha$--$\psi$ Poincaré inequality.  Assume that, for every $x\in\mathbb{R}^{d}$, the measure $\widetilde{\pi}^{Y\mid X=x}$ is a probability measure, that the map $x\mapsto\widetilde{\pi}^{Y\mid X=x}$ is $\pi$-almost-everywhere measurable, and that $\widetilde{\pi}^{Y}=\int\widetilde{\pi}^{Y\mid X=x}\,d\pi(x)$.  Write $K$ and $K^\dagger$ for the forward and backward conditional-expectation operators.  Assume that $K:L^{2}(\widetilde{\pi}^{Y})\to L^{2}(\pi)$ and $K^\dagger:L^{2}(\pi)\to L^{2}(\widetilde{\pi}^{Y})$, and assume the adjoint identity
  \[
    \int (Ku)(x)v(x)\,d\pi(x)
      =\int u(y)(K^\dagger v)(y)\,d\widetilde{\pi}^{Y}(y)
  \]
  for all $u\in L^{2}(\widetilde{\pi}^{Y})$ and $v\in L^{2}(\pi)$.  Assume moreover that, for every $v\in L^{2}(\pi)$, the functions $K^\dagger v$ and $KK^\dagger v$ are continuously differentiable and satisfy
  \[
    \mathcal{E}_{\pi,\psi}(KK^\dagger v)
      \leq \tau\int
        \operatorname{Var}_{\widetilde{\pi}^{Y\mid X=x}}(K^\dagger v)
        \,d\pi(x).
  \]
  Then every $f\in L^{2}(\pi)$ satisfies
  \[
    \operatorname{Var}_{\widetilde{\pi}^{Y}}(K^\dagger f)
      \leq \frac{1}{1+\alpha/\tau}\operatorname{Var}_{\pi}(f).
  \] -/)
  (proof := /-- Put $\nu=\widetilde{\pi}^{Y}$ and $c=(1+\alpha/\tau)^{-1}$, and let $K$ and $K^\dagger$ be the operators of \cref{def:forward-conditional-expectation, def:backward-conditional-expectation}.  The marginal identity, together with the probability and measurability assumptions on the forward conditionals, first shows that $\nu$ is a probability measure.  For every $g\in L^{2}(\nu)$, decompose the integral of $g$ into the lower integrals of its positive and negative parts and apply the bind formula to each part.  Their finiteness follows from integrability of $g$, and recombination gives
  \[
    \int Kg\,d\pi=\int g\,d\nu.
  \]

  Set $u=K^\dagger f$ and $w=Ku$.  The two $L^{2}$ mapping assumptions give $u\in L^{2}(\nu)$ and $w\in L^{2}(\pi)$.  Since the forward conditionals are probability measures, $K1=1$.  Applying adjointness to $1$ and $f$, and applying the preceding integral identity to $u$, yields
  \[
    \int u\,d\nu=\int f\,d\pi,
    \qquad
    \int w\,d\pi=\int u\,d\nu.
  \]
  Adjointness applied to $u$ and $f$ also gives
  \[
    \int wf\,d\pi=\int u^{2}\,d\nu.
  \]
  Expanding covariance and variance by their second-moment formulas therefore proves
  \[
    \operatorname{Var}_{\nu}(u)=\operatorname{Cov}_{\pi}(w,f).
  \]

  The regularity and Dirichlet hypotheses make \cref{lem:llt-prox-forward-contraction} applicable to $u$, so
  \[
    \operatorname{Var}_{\pi}(w)
      \leq c\operatorname{Var}_{\nu}(u).
  \]
  Applying the Cauchy--Schwarz inequality in $L^{2}(\pi)$ to the centered functions $w-\int w\,d\pi$ and $f-\int f\,d\pi$ gives
  \[
    \operatorname{Cov}_{\pi}(w,f)^{2}
      \leq \operatorname{Var}_{\pi}(w)\operatorname{Var}_{\pi}(f).
  \]
  Thus, with $V=\operatorname{Var}_{\nu}(u)$ and $F=\operatorname{Var}_{\pi}(f)$, one has $V^{2}\leq cVF$.  Both variances are nonnegative.  If $V=0$, the desired inequality is immediate; if $V>0$, division by $V$ gives $V\leq cF$, which is the asserted contraction. -/)
  (title := /-- Backward variance contraction on $L^2$ -/)
  (latexEnv := "lemma")]
lemma llt_prox_backward_contraction {d τ : ℕ} {α : ℝ}
    {φ ψ f : euclidean_state d → ℝ}
    {π : Measure (euclidean_state d)}
    (hconv : ConvexOn ℝ Set.univ φ)
    (hψ : ψ = log_laplace_transform φ)
    (hτ : 0 < τ) (hα : 0 < α)
    (hπ : IsProbabilityMeasure π)
    (hPI : functional_poincare π ψ α)
    (hcond_prob : ∀ x, IsProbabilityMeasure (dual_conditional φ τ x))
    (hcond_meas : AEMeasurable (fun x => dual_conditional φ τ x) π)
    (hmarginal : dual_marginal φ ψ π τ =
      Measure.bind π (fun x => dual_conditional φ τ x))
    (hadjoint :
      (∀ u, MeasureTheory.MemLp u 2 (dual_marginal φ ψ π τ) →
        MeasureTheory.MemLp
          (forward_conditional_expectation φ τ u) 2 π) ∧
      (∀ v, MeasureTheory.MemLp v 2 π →
        MeasureTheory.MemLp
          (backward_conditional_expectation ψ π τ v) 2
            (dual_marginal φ ψ π τ)) ∧
      ∀ u v,
        MeasureTheory.MemLp u 2 (dual_marginal φ ψ π τ) →
        MeasureTheory.MemLp v 2 π →
        ∫ x, forward_conditional_expectation φ τ u x * v x ∂π =
          ∫ y, u y * backward_conditional_expectation ψ π τ v y
            ∂(dual_marginal φ ψ π τ))
    (hforward_range :
      ∀ v, MeasureTheory.MemLp v 2 π →
        ContDiff ℝ 1 (backward_conditional_expectation ψ π τ v) ∧
        ContDiff ℝ 1 (forward_conditional_expectation φ τ
          (backward_conditional_expectation ψ π τ v)) ∧
        mirror_dirichlet_form π ψ
            (forward_conditional_expectation φ τ
              (backward_conditional_expectation ψ π τ v)) ≤
          (τ : ℝ) * ∫ x, ProbabilityTheory.variance
            (backward_conditional_expectation ψ π τ v)
            (dual_conditional φ τ x) ∂π)
    (hf : MeasureTheory.MemLp f 2 π) :
    ProbabilityTheory.variance
        (backward_conditional_expectation ψ π τ f)
        (dual_marginal φ ψ π τ) ≤
      1 / (1 + α / (τ : ℝ)) *
        ProbabilityTheory.variance f π := by
  letI : IsProbabilityMeasure π := hπ
  have hdual_prob : IsProbabilityMeasure (dual_marginal φ ψ π τ) := by
    rw [hmarginal]
    simp only [isProbabilityMeasure_iff, MeasurableSet.univ,
      Measure.bind_apply _ hcond_meas]
    have hprob : ∀ᵐ x ∂π,
        IsProbabilityMeasure (dual_conditional φ τ x) :=
      Filter.Eventually.of_forall hcond_prob
    simp_rw [isProbabilityMeasure_iff] at hprob
    exact lintegral_eq_const hprob
  letI : IsProbabilityMeasure (dual_marginal φ ψ π τ) := hdual_prob
  have integral_bind_real {g : euclidean_state d → ℝ}
      (hg : Integrable g
        (Measure.bind π (fun x => dual_conditional φ τ x))) :
      (∫ y, g y ∂(Measure.bind π (fun x => dual_conditional φ τ x))) =
        ∫ x, ∫ y, g y ∂(dual_conditional φ τ x) ∂π := by
    have hg_ae : AEMeasurable g
        (Measure.bind π (fun x => dual_conditional φ τ x)) :=
      hg.aestronglyMeasurable.aemeasurable
    have hpos_ae : AEMeasurable (fun y => ENNReal.ofReal (g y))
        (Measure.bind π (fun x => dual_conditional φ τ x)) :=
      hg_ae.ennreal_ofReal
    have hneg_ae : AEMeasurable (fun y => ENNReal.ofReal (-g y))
        (Measure.bind π (fun x => dual_conditional φ τ x)) :=
      hg_ae.neg.ennreal_ofReal
    have hnorm_ae : AEMeasurable (fun y => ‖g y‖ₑ)
        (Measure.bind π (fun x => dual_conditional φ τ x)) :=
      hg_ae.enorm
    have hpos_outer_ae : AEMeasurable
        (fun x => ∫⁻ y, ENNReal.ofReal (g y) ∂(dual_conditional φ τ x)) π :=
      (Measure.aemeasurable_lintegral hpos_ae).comp_aemeasurable hcond_meas
    have hneg_outer_ae : AEMeasurable
        (fun x => ∫⁻ y, ENNReal.ofReal (-g y) ∂(dual_conditional φ τ x)) π :=
      (Measure.aemeasurable_lintegral hneg_ae).comp_aemeasurable hcond_meas
    have hnorm_outer_ae : AEMeasurable
        (fun x => ∫⁻ y, ‖g y‖ₑ ∂(dual_conditional φ τ x)) π :=
      (Measure.aemeasurable_lintegral hnorm_ae).comp_aemeasurable hcond_meas
    have hpos_ne_top :
        (∫⁻ x, ∫⁻ y, ENNReal.ofReal (g y) ∂(dual_conditional φ τ x) ∂π) ≠ ⊤ := by
      rw [← Measure.lintegral_bind hcond_meas hpos_ae]
      exact ne_of_lt hg.lintegral_lt_top
    have hneg_ne_top :
        (∫⁻ x, ∫⁻ y, ENNReal.ofReal (-g y) ∂(dual_conditional φ τ x) ∂π) ≠ ⊤ := by
      rw [← Measure.lintegral_bind hcond_meas hneg_ae]
      exact ne_of_lt hg.neg.lintegral_lt_top
    have hnorm_ne_top :
        (∫⁻ x, ∫⁻ y, ‖g y‖ₑ ∂(dual_conditional φ τ x) ∂π) ≠ ⊤ := by
      rw [← Measure.lintegral_bind hcond_meas hnorm_ae]
      exact ne_of_lt hg.hasFiniteIntegral
    have hpos_lt_top := ae_lt_top' hpos_outer_ae hpos_ne_top
    have hneg_lt_top := ae_lt_top' hneg_outer_ae hneg_ne_top
    have hnorm_lt_top := ae_lt_top' hnorm_outer_ae hnorm_ne_top
    have hg_cond_ae := hcond_meas.ae_of_bind hg_ae
    have hg_cond_int : ∀ᵐ x ∂π, Integrable g (dual_conditional φ τ x) := by
      filter_upwards [hg_cond_ae, hnorm_lt_top] with x hgx hnormx
      exact ⟨hgx.aestronglyMeasurable, hnormx⟩
    have hpos_int := integrable_toReal_of_lintegral_ne_top
      hpos_outer_ae hpos_ne_top
    have hneg_int := integrable_toReal_of_lintegral_ne_top
      hneg_outer_ae hneg_ne_top
    have hinner_eq :
        (fun x => ∫ y, g y ∂(dual_conditional φ τ x)) =ᵐ[π]
          (fun x => (∫⁻ y, ENNReal.ofReal (g y)
              ∂(dual_conditional φ τ x)).toReal -
            (∫⁻ y, ENNReal.ofReal (-g y)
              ∂(dual_conditional φ τ x)).toReal) := by
      filter_upwards [hg_cond_int] with x hgx
      exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hgx
    calc
      (∫ y, g y ∂(Measure.bind π (fun x => dual_conditional φ τ x))) =
          (∫⁻ y, ENNReal.ofReal (g y)
              ∂(Measure.bind π (fun x => dual_conditional φ τ x))).toReal -
            (∫⁻ y, ENNReal.ofReal (-g y)
              ∂(Measure.bind π (fun x => dual_conditional φ τ x))).toReal :=
        integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg
      _ = (∫⁻ x, ∫⁻ y, ENNReal.ofReal (g y)
              ∂(dual_conditional φ τ x) ∂π).toReal -
            (∫⁻ x, ∫⁻ y, ENNReal.ofReal (-g y)
              ∂(dual_conditional φ τ x) ∂π).toReal := by
        rw [Measure.lintegral_bind hcond_meas hpos_ae,
          Measure.lintegral_bind hcond_meas hneg_ae]
      _ = (∫ x, (∫⁻ y, ENNReal.ofReal (g y)
              ∂(dual_conditional φ τ x)).toReal ∂π) -
            ∫ x, (∫⁻ y, ENNReal.ofReal (-g y)
              ∂(dual_conditional φ τ x)).toReal ∂π := by
        rw [integral_toReal hpos_outer_ae hpos_lt_top,
          integral_toReal hneg_outer_ae hneg_lt_top]
      _ = ∫ x, ((∫⁻ y, ENNReal.ofReal (g y)
              ∂(dual_conditional φ τ x)).toReal -
            (∫⁻ y, ENNReal.ofReal (-g y)
              ∂(dual_conditional φ τ x)).toReal) ∂π :=
        (integral_sub hpos_int hneg_int).symm
      _ = ∫ x, ∫ y, g y ∂(dual_conditional φ τ x) ∂π :=
        integral_congr_ae hinner_eq.symm
  have forward_integral_eq {g : euclidean_state d → ℝ}
      (hg : MeasureTheory.MemLp g 2 (dual_marginal φ ψ π τ)) :
      (∫ x, forward_conditional_expectation φ τ g x ∂π) =
        ∫ y, g y ∂(dual_marginal φ ψ π τ) := by
    have hg_bind : Integrable g
        (Measure.bind π (fun x => dual_conditional φ τ x)) := by
      rw [← hmarginal]
      exact hg.integrable one_le_two
    rw [hmarginal]
    exact (integral_bind_real hg_bind).symm
  rcases hadjoint with ⟨hforward_L2, hbackward_L2, hadjoint_inner⟩
  let u := backward_conditional_expectation ψ π τ f
  let w := forward_conditional_expectation φ τ u
  have hu : MeasureTheory.MemLp u 2 (dual_marginal φ ψ π τ) := by
    simpa [u] using hbackward_L2 f hf
  have hw : MeasureTheory.MemLp w 2 π := by
    simpa [w] using hforward_L2 u hu
  have hmean_wu : (∫ x, w x ∂π) =
      ∫ y, u y ∂(dual_marginal φ ψ π τ) := by
    simpa [w] using forward_integral_eq hu
  have hK_one :
      forward_conditional_expectation φ τ (fun _ => (1 : ℝ)) =
        fun _ => (1 : ℝ) := by
    funext x
    letI : IsProbabilityMeasure (dual_conditional φ τ x) := hcond_prob x
    simp [forward_conditional_expectation]
  have hmean_uf : (∫ y, u y ∂(dual_marginal φ ψ π τ)) =
      ∫ x, f x ∂π := by
    have hone : MeasureTheory.MemLp
        (fun _ : euclidean_state d => (1 : ℝ)) 2
          (dual_marginal φ ψ π τ) := memLp_const 1
    have hone_adjoint := hadjoint_inner
      (fun _ : euclidean_state d => (1 : ℝ)) f hone hf
    rw [hK_one] at hone_adjoint
    simpa [u] using hone_adjoint.symm
  have hinner : (∫ x, w x * f x ∂π) =
      ∫ y, u y * u y ∂(dual_marginal φ ψ π τ) := by
    simpa [u, w] using hadjoint_inner u f hu hf
  have hvar_cov : ProbabilityTheory.variance u
      (dual_marginal φ ψ π τ) =
        ProbabilityTheory.covariance w f π := by
    rw [variance_eq_sub hu, covariance_eq_sub hw hf]
    simp only [Pi.pow_apply, Pi.mul_apply]
    rw [hinner, hmean_wu, ← hmean_uf]
    simp only [pow_two]
  rcases hforward_range f hf with ⟨hu_smooth, hw_smooth, hdirichlet⟩
  have hforward_var : ProbabilityTheory.variance w π ≤
      1 / (1 + α / (τ : ℝ)) *
        ProbabilityTheory.variance u (dual_marginal φ ψ π τ) := by
    simpa [u, w] using
      (llt_prox_forward_contraction hconv hψ hτ hα hπ hPI hcond_prob
        hcond_meas hmarginal hu_smooth hu hw_smooth hw hdirichlet)
  let a : euclidean_state d → ℝ :=
    fun x => w x - ∫ z, w z ∂π
  let b : euclidean_state d → ℝ :=
    fun x => f x - ∫ z, f z ∂π
  have ha : MeasureTheory.MemLp a 2 π := by
    exact hw.sub (memLp_const _)
  have hb : MeasureTheory.MemLp b 2 π := by
    exact hf.sub (memLp_const _)
  have hinner_ab : inner ℝ (ha.toLp a) (hb.toLp b) =
      ∫ x, a x * b x ∂π := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hax hbx
    simp [hax, hbx, mul_comm]
  have hinner_aa : inner ℝ (ha.toLp a) (ha.toLp a) =
      ∫ x, a x ^ 2 ∂π := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp] with x hax
    simp [hax, pow_two]
  have hinner_bb : inner ℝ (hb.toLp b) (hb.toLp b) =
      ∫ x, b x ^ 2 ∂π := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hb.coeFn_toLp] with x hbx
    simp [hbx, pow_two]
  have hcov_sq : ProbabilityTheory.covariance w f π ^ 2 ≤
      ProbabilityTheory.variance w π * ProbabilityTheory.variance f π := by
    have hcs := real_inner_mul_inner_self_le (ha.toLp a) (hb.toLp b)
    rw [hinner_ab, hinner_aa, hinner_bb] at hcs
    rw [variance_eq_integral hw.aemeasurable,
      variance_eq_integral hf.aemeasurable]
    simpa [ProbabilityTheory.covariance, a, b, pow_two] using hcs
  have hvar_u_nonneg : 0 ≤ ProbabilityTheory.variance u
      (dual_marginal φ ψ π τ) := variance_nonneg _ _
  have hvar_f_nonneg : 0 ≤ ProbabilityTheory.variance f π :=
    variance_nonneg _ _
  have hsq : ProbabilityTheory.variance u
        (dual_marginal φ ψ π τ) ^ 2 ≤
      1 / (1 + α / (τ : ℝ)) *
        ProbabilityTheory.variance u (dual_marginal φ ψ π τ) *
          ProbabilityTheory.variance f π := by
    calc
      ProbabilityTheory.variance u (dual_marginal φ ψ π τ) ^ 2 =
          ProbabilityTheory.covariance w f π ^ 2 := by rw [hvar_cov]
      _ ≤ ProbabilityTheory.variance w π *
          ProbabilityTheory.variance f π := hcov_sq
      _ ≤ (1 / (1 + α / (τ : ℝ)) *
          ProbabilityTheory.variance u (dual_marginal φ ψ π τ)) *
            ProbabilityTheory.variance f π :=
        mul_le_mul_of_nonneg_right hforward_var hvar_f_nonneg
  by_cases hzero : ProbabilityTheory.variance u
      (dual_marginal φ ψ π τ) = 0
  · simpa [u, hzero] using
      mul_nonneg (by positivity : 0 ≤ 1 / (1 + α / (τ : ℝ))) hvar_f_nonneg
  · have hpos : 0 < ProbabilityTheory.variance u
        (dual_marginal φ ψ π τ) := lt_of_le_of_ne hvar_u_nonneg (Ne.symm hzero)
    change ProbabilityTheory.variance u (dual_marginal φ ψ π τ) ≤
      1 / (1 + α / (τ : ℝ)) * ProbabilityTheory.variance f π
    nlinarith

@[blueprint "lem:llt-prox-step-chi-squared-contraction"
  (statement := /-- Let $\varphi:\mathbb{R}^{d}\to\mathbb{R}$ be convex, let $\psi=\varphi^\sharp$, let $\tau\in\mathbb{N}$ and $\alpha\in\mathbb{R}$ be positive, and suppose that $\pi$ is a probability measure satisfying the $\alpha$--$\psi$ Poincaré inequality.  Assume that every auxiliary conditional $\widetilde{\pi}^{Y\mid X=x}$ is a probability measure, that $x\mapsto\widetilde{\pi}^{Y\mid X=x}$ is $\pi$-almost-everywhere measurable, and that $\widetilde{\pi}^{Y}=\int\widetilde{\pi}^{Y\mid X=x}\,d\pi(x)$.  Assume that the forward and backward conditional-expectation operators map the corresponding $L^{2}$ spaces into one another and satisfy the $L^{2}$ adjoint identity.  Assume also that, for every $v\in L^{2}(\pi)$, both $K^\dagger v$ and $KK^\dagger v$ are continuously differentiable and the kernel-specific Dirichlet comparison
  \[
    \mathcal{E}_{\pi,\psi}(KK^\dagger v)
      \leq \tau\int
        \operatorname{Var}_{\widetilde{\pi}^{Y\mid X=x}}(K^\dagger v)
        \,d\pi(x)
  \]
  holds.  Let $\mu$ be a probability measure with $\mu\ll\pi$, and let $\nu$ be obtained from $\mu$ by one LLT-Prox step.  Then $\nu\ll\pi$ and, as an inequality in $[0,+\infty]$,
  \[
    \chi^2(\nu\Vert\pi)
      \leq \frac{1}{(1+\alpha/\tau)^2}\chi^2(\mu\Vert\pi).
  \] -/)
  (proof := /-- The update formula in \cref{def:llt-prox-step}, applied to a measurable hull of an arbitrary $\pi$-null set, shows first that $\nu\ll\pi$: every primal conditional in \cref{def:primal-conditional} vanishes on such a hull.

  We distinguish two cases according to the extended value in \cref{def:chi-squared-divergence}.  Suppose first that $\chi^2(\mu\Vert\pi)<+\infty$.  Since $\mu\ll\pi$ and both $\mu$ and $\pi$ are probability measures, the Radon--Nikodym identity gives
  \[
    \int \frac{d\mu}{d\pi}\,d\pi=1.
  \]
  Finiteness of the lower integral defining $\chi^2(\mu\Vert\pi)$ is therefore equivalent to membership of the centered density
  \[
    r_0=\frac{d\mu}{d\pi}-1
  \]
  in $L^2(\pi)$, its mean is zero, and its variance equals $\chi^2(\mu\Vert\pi)$.

  Write $K$ and $K^\dagger$ for the operators in \cref{def:forward-conditional-expectation, def:backward-conditional-expectation}.  The marginal identity makes $\widetilde{\pi}^{Y}$ a probability measure.  Since $K1=1$, adjointness shows that $K^\dagger1$ has mean one.  Applying \cref{lem:llt-prox-backward-contraction} to the constant function gives zero variance, and hence
  \[
    K^\dagger1=1\qquad \widetilde{\pi}^{Y}\text{-almost everywhere}.
  \]
  This identity supplies the normalization needed to identify the updated density without assuming separately that every primal conditional is a probability measure.

  Indeed, let $A$ be measurable and put $v=\mathbf{1}_A$, $b=K^\dagger v$, and $t=Kb$.  The total normalization in \cref{def:primal-conditional} makes every primal conditional finite, so its mass on $A$ is $\operatorname{ofReal}(b)$.  The $L^2$ mapping hypotheses and the marginal bind identity imply that $b$ is integrable under the auxiliary conditional for $\pi$-almost every $x$.  Consequently \cref{def:llt-prox-step}, the Radon--Nikodym change-of-measure identity, and adjointness applied twice give
  \[
    \nu(A)
      =\operatorname{ofReal}\!\left(
        \int \left(1+KK^\dagger r_0\right)\mathbf{1}_A\,d\pi
        \right).
  \]
  The mean of $KK^\dagger r_0$ is zero.  Applying the preceding set identity to $A^c$ and using $\nu(A^c)\leq\nu(\mathbb{R}^d)$ shows that every measurable-set integral of $1+KK^\dagger r_0$ is nonnegative.  Hence this function is nonnegative $\pi$-almost everywhere, and the set identity proves
  \[
    \frac{d\nu}{d\pi}-1=KK^\dagger r_0
    \qquad \pi\text{-almost everywhere}.
  \]

  Applying \cref{lem:llt-prox-backward-contraction} to $r_0$ and then \cref{lem:llt-prox-forward-contraction} to $K^\dagger r_0$ yields
  \[
    \lVert KK^\dagger r_0\rVert_{L^2(\pi)}^2
      \leq \frac{1}{(1+\alpha/\tau)^2}
        \lVert r_0\rVert_{L^2(\pi)}^2.
  \]
  The density identity and \cref{def:chi-squared-divergence} convert this estimate into the asserted extended-valued inequality.

  Suppose instead that $\chi^2(\mu\Vert\pi)=+\infty$.  Positivity of $\alpha$ and $\tau$ implies
  \[
    \frac{1}{(1+\alpha/\tau)^2}>0.
  \]
  Hence the right-hand side of the desired inequality is $+\infty$, and the conclusion follows from the order-top property of $[0,+\infty]$. -/)
  (title := /-- One-step chi-squared contraction -/)
  (latexEnv := "lemma")]
lemma llt_prox_step_chi_squared_contraction {d τ : ℕ} {α : ℝ}
    {φ ψ : euclidean_state d → ℝ}
    {π μ ν : Measure (euclidean_state d)}
    (hconv : ConvexOn ℝ Set.univ φ)
    (hψ : ψ = log_laplace_transform φ)
    (hτ : 0 < τ) (hα : 0 < α)
    (hπ : IsProbabilityMeasure π)
    (hPI : functional_poincare π ψ α)
    (hcond_prob : ∀ x, IsProbabilityMeasure (dual_conditional φ τ x))
    (hcond_meas : AEMeasurable (fun x => dual_conditional φ τ x) π)
    (hmarginal : dual_marginal φ ψ π τ =
      Measure.bind π (fun x => dual_conditional φ τ x))
    (hadjoint :
      (∀ u, MeasureTheory.MemLp u 2 (dual_marginal φ ψ π τ) →
        MeasureTheory.MemLp
          (forward_conditional_expectation φ τ u) 2 π) ∧
      (∀ v, MeasureTheory.MemLp v 2 π →
        MeasureTheory.MemLp
          (backward_conditional_expectation ψ π τ v) 2
            (dual_marginal φ ψ π τ)) ∧
      ∀ u v,
        MeasureTheory.MemLp u 2 (dual_marginal φ ψ π τ) →
        MeasureTheory.MemLp v 2 π →
        ∫ x, forward_conditional_expectation φ τ u x * v x ∂π =
          ∫ y, u y * backward_conditional_expectation ψ π τ v y
            ∂(dual_marginal φ ψ π τ))
    (hforward_range :
      ∀ v, MeasureTheory.MemLp v 2 π →
        ContDiff ℝ 1 (backward_conditional_expectation ψ π τ v) ∧
        ContDiff ℝ 1 (forward_conditional_expectation φ τ
          (backward_conditional_expectation ψ π τ v)) ∧
        mirror_dirichlet_form π ψ
            (forward_conditional_expectation φ τ
              (backward_conditional_expectation ψ π τ v)) ≤
          (τ : ℝ) * ∫ x, ProbabilityTheory.variance
            (backward_conditional_expectation ψ π τ v)
            (dual_conditional φ τ x) ∂π)
    (hμ_prob : IsProbabilityMeasure μ)
    (hμ : μ ≪ π)
    (hstep : llt_prox_step φ ψ π τ μ ν) :
    ν ≪ π ∧
      chi_squared_divergence ν π ≤
        ENNReal.ofReal (1 / (1 + α / (τ : ℝ)) ^ 2) *
          chi_squared_divergence μ π := by
  have hν : ν ≪ π := by
    intro A hA
    refine measure_mono_null (subset_toMeasurable π A) ?_
    rw [hstep (toMeasurable π A) (measurableSet_toMeasurable π A)]
    simp [primal_conditional, normalized_measure, Measure.restrict_zero_set hA]
  refine ⟨hν, ?_⟩
  by_cases htop : chi_squared_divergence μ π = ⊤
  · have hc : ENNReal.ofReal (1 / (1 + α / (τ : ℝ)) ^ 2) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
    rw [htop, ENNReal.mul_top hc]
    exact le_top
  · let f : euclidean_state d → ℝ :=
      fun x => (μ.rnDeriv π x).toReal - 1
    letI : IsProbabilityMeasure π := hπ
    letI : IsProbabilityMeasure μ := hμ_prob
    have hf_meas : AEStronglyMeasurable f π :=
      ((Measure.measurable_rnDeriv μ π).ennreal_toReal.sub
        measurable_const).aestronglyMeasurable
    have hsq_ne_top :
        (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂π) ≠ ⊤ := by
      simpa [chi_squared_divergence, f] using htop
    have hsq_int : Integrable (fun x => f x ^ 2) π :=
      (lintegral_ofReal_ne_top_iff_integrable
        (hf_meas.pow 2) (Filter.Eventually.of_forall fun x => sq_nonneg (f x))).mp
        hsq_ne_top
    have hf : MeasureTheory.MemLp f 2 π :=
      (memLp_two_iff_integrable_sq hf_meas).mpr hsq_int
    have hr_lp : MeasureTheory.MemLp
        (fun x => (μ.rnDeriv π x).toReal) 2 π := by
      convert hf.add (memLp_const (1 : ℝ)) using 1
      ext x
      simp [f]
    have hf_mean : ∫ x, f x ∂π = 0 := by
      change (∫ x, (μ.rnDeriv π x).toReal - 1 ∂π) = 0
      have hr_int : Integrable (fun x => (μ.rnDeriv π x).toReal) π := by
        exact hr_lp.integrable one_le_two
      rw [integral_sub hr_int (integrable_const (1 : ℝ))]
      rw [Measure.integral_toReal_rnDeriv hμ]
      simp
    have hvar_f : ProbabilityTheory.variance f π = ∫ x, f x ^ 2 ∂π := by
      rw [variance_eq_sub hf]
      simp [hf_mean]
    have hchi_mu : chi_squared_divergence μ π =
        ENNReal.ofReal (ProbabilityTheory.variance f π) := by
      rw [chi_squared_divergence, hvar_f]
      exact (ofReal_integral_eq_lintegral_ofReal hsq_int
        (Filter.Eventually.of_forall fun x => sq_nonneg (f x))).symm
    have hprimal_mass : ∀ y,
        primal_conditional ψ π τ y Set.univ ≤ 1 := by
      intro y
      simp [primal_conditional, normalized_measure]
    have hprimal_finite : ∀ y A,
        primal_conditional ψ π τ y A ≠ ⊤ := by
      intro y A
      exact ne_of_lt (lt_of_le_of_lt
        (measure_mono (Set.subset_univ A))
        (lt_of_le_of_lt (hprimal_mass y) ENNReal.one_lt_top))
    have hprimal_indicator (A : Set (euclidean_state d))
        (hA : MeasurableSet A) (y : euclidean_state d) :
        primal_conditional ψ π τ y A =
          ENNReal.ofReal (backward_conditional_expectation ψ π τ
            (A.indicator (fun _ => (1 : ℝ))) y) := by
      change primal_conditional ψ π τ y A = ENNReal.ofReal
        (∫ x, A.indicator (1 : euclidean_state d → ℝ) x
          ∂(primal_conditional ψ π τ y))
      rw [integral_indicator_one hA]
      simp [Measure.real, ENNReal.ofReal_toReal, hprimal_finite y A]
    have hdual_prob : IsProbabilityMeasure (dual_marginal φ ψ π τ) := by
      rw [hmarginal]
      simp only [isProbabilityMeasure_iff, MeasurableSet.univ,
        Measure.bind_apply _ hcond_meas]
      have hprob : ∀ᵐ x ∂π,
          IsProbabilityMeasure (dual_conditional φ τ x) :=
        Filter.Eventually.of_forall hcond_prob
      simp_rw [isProbabilityMeasure_iff] at hprob
      exact lintegral_eq_const hprob
    letI : IsProbabilityMeasure (dual_marginal φ ψ π τ) := hdual_prob
    let one : euclidean_state d → ℝ := fun _ => 1
    have hone_pi : MeasureTheory.MemLp one 2 π := memLp_const 1
    have hone_dual : MeasureTheory.MemLp one 2
        (dual_marginal φ ψ π τ) := memLp_const 1
    let uone : euclidean_state d → ℝ :=
      backward_conditional_expectation ψ π τ one
    have huone : MeasureTheory.MemLp uone 2 (dual_marginal φ ψ π τ) := by
      simpa [uone] using hadjoint.2.1 one hone_pi
    have hKone : forward_conditional_expectation φ τ one = one := by
      funext x
      letI : IsProbabilityMeasure (dual_conditional φ τ x) := hcond_prob x
      simp [forward_conditional_expectation, one]
    have hmean_uone : ∫ y, uone y ∂(dual_marginal φ ψ π τ) = 1 := by
      have hadj := hadjoint.2.2 one one hone_dual hone_pi
      rw [hKone] at hadj
      simpa [uone, one] using hadj.symm
    have hvar_uone_le : ProbabilityTheory.variance uone
        (dual_marginal φ ψ π τ) ≤ 0 := by
      have hv := llt_prox_backward_contraction hconv hψ hτ hα hπ hPI
        hcond_prob hcond_meas hmarginal hadjoint hforward_range hone_pi
      have hone_var : ProbabilityTheory.variance one π = 0 := by
        rw [variance_eq_sub hone_pi]
        simp [one]
      simpa [uone, hone_var] using hv
    have hvar_uone : ProbabilityTheory.variance uone
        (dual_marginal φ ψ π τ) = 0 :=
      le_antisymm hvar_uone_le (variance_nonneg _ _)
    have huone_one : uone =ᵐ[dual_marginal φ ψ π τ] one := by
      have hc := ae_eq_integral_of_variance_eq_zero huone hvar_uone
      filter_upwards [hc] with y hy
      simpa [one, hmean_uone] using hy
    let u : euclidean_state d → ℝ :=
      backward_conditional_expectation ψ π τ f
    let w : euclidean_state d → ℝ :=
      forward_conditional_expectation φ τ u
    have hu : MeasureTheory.MemLp u 2 (dual_marginal φ ψ π τ) := by
      simpa [u] using hadjoint.2.1 f hf
    have hw : MeasureTheory.MemLp w 2 π := by
      simpa [w] using hadjoint.1 u hu
    have hback : ProbabilityTheory.variance u (dual_marginal φ ψ π τ) ≤
        1 / (1 + α / (τ : ℝ)) * ProbabilityTheory.variance f π := by
      simpa [u] using llt_prox_backward_contraction hconv hψ hτ hα hπ hPI
        hcond_prob hcond_meas hmarginal hadjoint hforward_range hf
    rcases hforward_range f hf with ⟨hu_smooth, hw_smooth, hdirichlet⟩
    have hforward : ProbabilityTheory.variance w π ≤
        1 / (1 + α / (τ : ℝ)) *
          ProbabilityTheory.variance u (dual_marginal φ ψ π τ) := by
      simpa [u, w] using llt_prox_forward_contraction hconv hψ hτ hα hπ hPI
        hcond_prob hcond_meas hmarginal hu_smooth hu hw_smooth hw hdirichlet
    have hvar : ProbabilityTheory.variance w π ≤
        1 / (1 + α / (τ : ℝ)) ^ 2 *
          ProbabilityTheory.variance f π := by
      calc
        ProbabilityTheory.variance w π ≤
            1 / (1 + α / (τ : ℝ)) *
              ProbabilityTheory.variance u (dual_marginal φ ψ π τ) := hforward
        _ ≤ 1 / (1 + α / (τ : ℝ)) *
              (1 / (1 + α / (τ : ℝ)) *
                ProbabilityTheory.variance f π) :=
          mul_le_mul_of_nonneg_left hback (by positivity)
        _ = 1 / (1 + α / (τ : ℝ)) ^ 2 *
              ProbabilityTheory.variance f π := by
          have hq : 1 + α / (τ : ℝ) ≠ 0 := ne_of_gt (by positivity)
          field_simp [hq]
    have hmean_u : ∫ y, u y ∂(dual_marginal φ ψ π τ) = 0 := by
      have hadj := hadjoint.2.2 one f hone_dual hf
      rw [hKone] at hadj
      calc
        (∫ y, u y ∂(dual_marginal φ ψ π τ)) =
            ∫ y, one y * u y ∂(dual_marginal φ ψ π τ) := by simp [one]
        _ = ∫ x, one x * f x ∂π := hadj.symm
        _ = ∫ x, f x ∂π := by simp [one]
        _ = 0 := hf_mean
    have hmean_w : ∫ x, w x ∂π = 0 := by
      have hadj := hadjoint.2.2 u one hu hone_pi
      calc
        (∫ x, w x ∂π) = ∫ x, w x * one x ∂π := by simp [one]
        _ = ∫ y, u y * uone y ∂(dual_marginal φ ψ π τ) := by
          simpa [w, uone] using hadj
        _ = ∫ y, u y * one y ∂(dual_marginal φ ψ π τ) := by
          apply integral_congr_ae
          filter_upwards [huone_one] with y hy
          rw [hy]
        _ = ∫ y, u y ∂(dual_marginal φ ψ π τ) := by simp [one]
        _ = 0 := hmean_u
    have hν_set (A : Set (euclidean_state d)) (hA : MeasurableSet A) :
        ν A = ENNReal.ofReal
          (∫ x, (w x + 1) * A.indicator (fun _ => (1 : ℝ)) x ∂π) := by
      let v : euclidean_state d → ℝ := A.indicator one
      let b : euclidean_state d → ℝ :=
        backward_conditional_expectation ψ π τ v
      let t : euclidean_state d → ℝ :=
        forward_conditional_expectation φ τ b
      have hv : MeasureTheory.MemLp v 2 π := by
        simpa [v] using hone_pi.indicator hA
      have hb : MeasureTheory.MemLp b 2 (dual_marginal φ ψ π τ) := by
        simpa [b] using hadjoint.2.1 v hv
      have ht : MeasureTheory.MemLp t 2 π := by
        simpa [t] using hadjoint.1 b hb
      have hb_nonneg : ∀ y, 0 ≤ b y := by
        intro y
        change 0 ≤ ∫ x, v x ∂(primal_conditional ψ π τ y)
        apply integral_nonneg_of_ae
        exact Filter.Eventually.of_forall fun x => by
          change 0 ≤ A.indicator (fun _ => (1 : ℝ)) x
          by_cases hx : x ∈ A <;> simp [Set.indicator, hx]
      have ht_nonneg : ∀ x, 0 ≤ t x := by
        intro x
        exact integral_nonneg_of_ae
          (Filter.Eventually.of_forall fun y => hb_nonneg y)
      have hb_bind : Integrable b
          (Measure.bind π (fun x => dual_conditional φ τ x)) := by
        rw [← hmarginal]
        exact hb.integrable one_le_two
      have hb_cond_meas : ∀ᵐ x ∂π,
          AEStronglyMeasurable b (dual_conditional φ τ x) := by
        filter_upwards [hcond_meas.ae_of_bind hb_bind.aemeasurable] with x hx
        exact hx.aestronglyMeasurable
      have hnorm_outer_ae : AEMeasurable
          (fun x => ∫⁻ y, ‖b y‖ₑ ∂(dual_conditional φ τ x)) π :=
        (Measure.aemeasurable_lintegral hb_bind.aemeasurable.enorm).comp_aemeasurable
          hcond_meas
      have hnorm_ne_top :
          (∫⁻ x, ∫⁻ y, ‖b y‖ₑ ∂(dual_conditional φ τ x) ∂π) ≠ ⊤ := by
        rw [← Measure.lintegral_bind hcond_meas hb_bind.aemeasurable.enorm]
        exact ne_of_lt hb_bind.hasFiniteIntegral
      have hnorm_lt_top := ae_lt_top' hnorm_outer_ae hnorm_ne_top
      have hb_cond_int : ∀ᵐ x ∂π, Integrable b (dual_conditional φ τ x) := by
        filter_upwards [hb_cond_meas, hnorm_lt_top] with x hbx hnormx
        exact ⟨hbx, hnormx⟩
      have hnested : ∀ᵐ x ∂π,
          (∫⁻ y, primal_conditional ψ π τ y A
            ∂(dual_conditional φ τ x)) = ENNReal.ofReal (t x) := by
        filter_upwards [hb_cond_int] with x hbx
        rw [show (∫⁻ y, primal_conditional ψ π τ y A
            ∂(dual_conditional φ τ x)) =
              ∫⁻ y, ENNReal.ofReal (b y) ∂(dual_conditional φ τ x) by
          apply lintegral_congr
          intro y
          simpa [b, v, one] using hprimal_indicator A hA y]
        exact (ofReal_integral_eq_lintegral_ofReal hbx
          (Filter.Eventually.of_forall fun y => hb_nonneg y)).symm
      have hrt_int : Integrable
          (fun x => (μ.rnDeriv π x).toReal * t x) π := by
        change Integrable ((fun x => (μ.rnDeriv π x).toReal) * t) π
        exact hr_lp.integrable_mul ht
      have ht_mu : Integrable t μ :=
        (integrable_toReal_rnDeriv_mul_iff hμ).mp hrt_int
      have hft_int : Integrable (fun x => f x * t x) π := by
        change Integrable (f * t) π
        exact hf.integrable_mul ht
      have hwv_int : Integrable (fun x => w x * v x) π := by
        change Integrable (w * v) π
        exact hw.integrable_mul hv
      have ht_int : Integrable t π := ht.integrable one_le_two
      have hv_int : Integrable v π := hv.integrable one_le_two
      have hft_eq : (∫ x, f x * t x ∂π) = ∫ x, w x * v x ∂π := by
        have h1 := hadjoint.2.2 b f hb hf
        have h2 := hadjoint.2.2 u v hu hv
        calc
          (∫ x, f x * t x ∂π) = ∫ x, t x * f x ∂π := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x => mul_comm _ _
          _ = ∫ y, b y * u y ∂(dual_marginal φ ψ π τ) := by
            simpa [t, u] using h1
          _ = ∫ y, u y * b y ∂(dual_marginal φ ψ π τ) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun y => mul_comm _ _
          _ = ∫ x, w x * v x ∂π := by
            simpa [w, b] using h2.symm
      have ht_eq : (∫ x, t x ∂π) = ∫ x, v x ∂π := by
        have h1 := hadjoint.2.2 b one hb hone_pi
        have h2 := hadjoint.2.2 one v hone_dual hv
        calc
          (∫ x, t x ∂π) = ∫ x, t x * one x ∂π := by simp [one]
          _ = ∫ y, b y * uone y ∂(dual_marginal φ ψ π τ) := by
            simpa [t, uone] using h1
          _ = ∫ y, b y * one y ∂(dual_marginal φ ψ π τ) := by
            apply integral_congr_ae
            filter_upwards [huone_one] with y hy
            rw [hy]
          _ = ∫ y, one y * b y ∂(dual_marginal φ ψ π τ) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun y => mul_comm _ _
          _ = ∫ x, forward_conditional_expectation φ τ one x * v x ∂π :=
            h2.symm
          _ = ∫ x, v x ∂π := by rw [hKone]; simp [one]
      have hself : (∫ x, (μ.rnDeriv π x).toReal * t x ∂π) =
          ∫ x, (w x + 1) * v x ∂π := by
        calc
          (∫ x, (μ.rnDeriv π x).toReal * t x ∂π) =
              ∫ x, f x * t x + t x ∂π := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x => by simp [f]; ring
          _ = (∫ x, f x * t x ∂π) + ∫ x, t x ∂π :=
            integral_add hft_int ht_int
          _ = (∫ x, w x * v x ∂π) + ∫ x, v x ∂π := by
            rw [hft_eq, ht_eq]
          _ = ∫ x, w x * v x + v x ∂π :=
            (integral_add hwv_int hv_int).symm
          _ = ∫ x, (w x + 1) * v x ∂π := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x => by ring
      rw [hstep A hA]
      calc
        (∫⁻ x, ∫⁻ y, primal_conditional ψ π τ y A
            ∂(dual_conditional φ τ x) ∂μ) =
            ∫⁻ x, ENNReal.ofReal (t x) ∂μ := by
          apply lintegral_congr_ae
          exact (Measure.ae_le_iff_absolutelyContinuous.mpr hμ) hnested
        _ = ENNReal.ofReal (∫ x, t x ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal ht_mu
            (Filter.Eventually.of_forall fun x => ht_nonneg x)).symm
        _ = ENNReal.ofReal
            (∫ x, (μ.rnDeriv π x).toReal * t x ∂π) := by
          apply congrArg ENNReal.ofReal
          simpa [smul_eq_mul] using
            (integral_rnDeriv_smul (μ := μ) (ν := π) (f := t) hμ).symm
        _ = ENNReal.ofReal (∫ x, (w x + 1) * v x ∂π) := by rw [hself]
        _ = ENNReal.ofReal
            (∫ x, (w x + 1) * A.indicator (fun _ => (1 : ℝ)) x ∂π) := by
          rfl
    let g : euclidean_state d → ℝ := fun x => w x + 1
    have hg_int : Integrable g π := by
      exact hw.integrable one_le_two |>.add (integrable_const (1 : ℝ))
    have hg_mean : ∫ x, g x ∂π = 1 := by
      rw [show (∫ x, g x ∂π) = (∫ x, w x ∂π) + ∫ _x, (1 : ℝ) ∂π by
        exact integral_add (hw.integrable one_le_two) (integrable_const (1 : ℝ))]
      simp [hmean_w]
    have hindicator (A : Set (euclidean_state d)) (hA : MeasurableSet A) :
        (∫ x, (w x + 1) * A.indicator (fun _ => (1 : ℝ)) x ∂π) =
          ∫ x in A, g x ∂π := by
      rw [← integral_indicator hA]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        by_cases hx : x ∈ A <;> simp [g, Set.indicator, hx]
    have hset_nonneg (A : Set (euclidean_state d)) (hA : MeasurableSet A) :
        0 ≤ ∫ x in A, g x ∂π := by
      have hcomp_le : ν Aᶜ ≤ ν Set.univ :=
        measure_mono (Set.subset_univ Aᶜ)
      rw [hν_set Aᶜ hA.compl, hν_set Set.univ MeasurableSet.univ,
        hindicator Aᶜ hA.compl, hindicator Set.univ MeasurableSet.univ] at hcomp_le
      simp only [Measure.restrict_univ, hg_mean, ENNReal.ofReal_one] at hcomp_le
      have hcomp_real : (∫ x in Aᶜ, g x ∂π) ≤ 1 :=
        ENNReal.ofReal_le_one.mp hcomp_le
      have hsplit := integral_add_compl hA hg_int
      rw [hg_mean] at hsplit
      linarith
    have hg_nonneg : 0 ≤ᵐ[π] g :=
      ae_nonneg_of_forall_setIntegral_nonneg hg_int
        (fun A hA _ => hset_nonneg A hA)
    have hmeasure : π.withDensity (fun x => ENNReal.ofReal (g x)) = ν := by
      apply Measure.ext
      intro A hA
      rw [withDensity_apply _ hA, hν_set A hA, hindicator A hA]
      exact (ofReal_integral_eq_lintegral_ofReal hg_int.integrableOn
        (ae_restrict_of_ae hg_nonneg)).symm
    have hgdens_meas : AEMeasurable (fun x => ENNReal.ofReal (g x)) π :=
      (hw.aemeasurable.add_const 1).ennreal_ofReal
    have hrn_ae : ν.rnDeriv π =ᵐ[π] fun x => ENNReal.ofReal (g x) := by
      have hrn := Measure.rnDeriv_withDensity₀ π hgdens_meas
      rw [hmeasure] at hrn
      exact hrn
    have hcentered : (fun x => (ν.rnDeriv π x).toReal - 1) =ᵐ[π] w := by
      filter_upwards [hrn_ae, hg_nonneg] with x hx hnonneg
      rw [hx]
      simp [g, ENNReal.toReal_ofReal hnonneg]
    have hvar_w : ProbabilityTheory.variance w π = ∫ x, w x ^ 2 ∂π := by
      rw [variance_eq_sub hw]
      simp [hmean_w]
    have hchi_nu : chi_squared_divergence ν π =
        ENNReal.ofReal (ProbabilityTheory.variance w π) := by
      rw [chi_squared_divergence, hvar_w]
      calc
        (∫⁻ x, ENNReal.ofReal (((ν.rnDeriv π x).toReal - 1) ^ 2) ∂π) =
            ∫⁻ x, ENNReal.ofReal (w x ^ 2) ∂π := by
          apply lintegral_congr_ae
          filter_upwards [hcentered] with x hx
          rw [hx]
        _ = ENNReal.ofReal (∫ x, w x ^ 2 ∂π) :=
          (ofReal_integral_eq_lintegral_ofReal hw.integrable_sq
            (Filter.Eventually.of_forall fun x => sq_nonneg (w x))).symm
    rw [hchi_nu, hchi_mu]
    calc
      ENNReal.ofReal (ProbabilityTheory.variance w π) ≤
          ENNReal.ofReal (1 / (1 + α / (τ : ℝ)) ^ 2 *
            ProbabilityTheory.variance f π) := ENNReal.ofReal_mono hvar
      _ = ENNReal.ofReal (1 / (1 + α / (τ : ℝ)) ^ 2) *
            ENNReal.ofReal (ProbabilityTheory.variance f π) :=
        ENNReal.ofReal_mul (by positivity)

@[blueprint "thm:mixing"
  (statement := /-- Let $\varphi:\mathbb{R}^{d}\to\mathbb{R}$ be convex, set $\psi=\varphi^\sharp$, let $\alpha\in\mathbb{R}$ and $\tau\in\mathbb{N}$ be positive, and let the probability measure $\pi$ satisfy the $\alpha$--$\psi$ Poincaré inequality.  Assume that every auxiliary conditional $\widetilde{\pi}^{Y\mid X=x}$ is a probability measure, that $x\mapsto\widetilde{\pi}^{Y\mid X=x}$ is $\pi$-almost-everywhere measurable, and that $\widetilde{\pi}^{Y}=\int\widetilde{\pi}^{Y\mid X=x}\,d\pi(x)$.  Assume that the forward and backward conditional-expectation operators map the corresponding $L^{2}$ spaces into one another and satisfy the $L^{2}$ adjoint identity.  Assume also that, for every $v\in L^{2}(\pi)$, both $K^\dagger v$ and $KK^\dagger v$ are continuously differentiable and satisfy the kernel-specific Dirichlet comparison
  \[
    \mathcal{E}_{\pi,\psi}(KK^\dagger v)
      \leq \tau\int
        \operatorname{Var}_{\widetilde{\pi}^{Y\mid X=x}}(K^\dagger v)
        \,d\pi(x).
  \]
  Let $(\mu_j)_{j\geq0}$ be an LLT-Prox trajectory and suppose only that $\mu_0\ll\pi$.  Then, for every $k\in\mathbb{N}$, the following inequality holds in $[0,+\infty]$:
  \[
    \chi^2(\mu_k\Vert\pi)
      \leq \frac{1}{(1+\alpha/\tau)^{2k}}
        \chi^2(\mu_0\Vert\pi).
  \] -/)
  (proof := /-- We prove by induction on $k$ that $\mu_k\ll\pi$ and that the asserted extended-valued bound holds.  At $k=0$, absolute continuity is the hypothesis and the inequality is equality.  Suppose both assertions hold at $k$.  By \cref{def:llt-prox-trajectory}, the trajectory hypothesis states that $\mu_k$ is a probability measure and supplies one LLT-Prox step from $\mu_k$ to $\mu_{k+1}$.  Consequently \cref{lem:llt-prox-step-chi-squared-contraction} gives $\mu_{k+1}\ll\pi$ and
  \[
    \chi^{2}(\mu_{k+1}\Vert\pi)
      \leq (1+\alpha/\tau)^{-2}\chi^{2}(\mu_k\Vert\pi).
  \]
  Multiplying the induction hypothesis by the nonnegative factor $(1+\alpha/\tau)^{-2}$ and using the laws of multiplication and natural powers in $[0,+\infty]$ gives
  \[
    \chi^{2}(\mu_{k+1}\Vert\pi)
      \leq (1+\alpha/\tau)^{-2(k+1)}
        \chi^{2}(\mu_0\Vert\pi).
  \]
  This completes the induction.  In particular, the argument includes initial laws of infinite chi-squared divergence: for those laws the initial right-hand side is $+\infty$, while absolute continuity is still propagated by the one-step result. -/)
  (title := /-- Geometric chi-squared mixing of LLT-Prox -/)
  (latexEnv := "theorem")]
theorem mixing {d τ k : ℕ} {α : ℝ}
    {φ ψ : euclidean_state d → ℝ}
    {π : Measure (euclidean_state d)}
    {μ : ℕ → Measure (euclidean_state d)}
    (hconv : ConvexOn ℝ Set.univ φ)
    (hψ : ψ = log_laplace_transform φ)
    (hτ : 0 < τ) (hα : 0 < α)
    (hπ : IsProbabilityMeasure π)
    (hPI : functional_poincare π ψ α)
    (hcond_prob : ∀ x, IsProbabilityMeasure (dual_conditional φ τ x))
    (hcond_meas : AEMeasurable (fun x => dual_conditional φ τ x) π)
    (hmarginal : dual_marginal φ ψ π τ =
      Measure.bind π (fun x => dual_conditional φ τ x))
    (hadjoint :
      (∀ u, MeasureTheory.MemLp u 2 (dual_marginal φ ψ π τ) →
        MeasureTheory.MemLp
          (forward_conditional_expectation φ τ u) 2 π) ∧
      (∀ v, MeasureTheory.MemLp v 2 π →
        MeasureTheory.MemLp
          (backward_conditional_expectation ψ π τ v) 2
            (dual_marginal φ ψ π τ)) ∧
      ∀ u v,
        MeasureTheory.MemLp u 2 (dual_marginal φ ψ π τ) →
        MeasureTheory.MemLp v 2 π →
        ∫ x, forward_conditional_expectation φ τ u x * v x ∂π =
          ∫ y, u y * backward_conditional_expectation ψ π τ v y
            ∂(dual_marginal φ ψ π τ))
    (hforward_range :
      ∀ v, MeasureTheory.MemLp v 2 π →
        ContDiff ℝ 1 (backward_conditional_expectation ψ π τ v) ∧
        ContDiff ℝ 1 (forward_conditional_expectation φ τ
          (backward_conditional_expectation ψ π τ v)) ∧
        mirror_dirichlet_form π ψ
            (forward_conditional_expectation φ τ
              (backward_conditional_expectation ψ π τ v)) ≤
          (τ : ℝ) * ∫ x, ProbabilityTheory.variance
            (backward_conditional_expectation ψ π τ v)
            (dual_conditional φ τ x) ∂π)
    (hμ0 : μ 0 ≪ π)
    (htrajectory : llt_prox_trajectory φ ψ π τ μ) :
    chi_squared_divergence (μ k) π ≤
      ENNReal.ofReal (1 / (1 + α / (τ : ℝ)) ^ (2 * k)) *
        chi_squared_divergence (μ 0) π := by
  have hmain : ∀ n : ℕ,
      μ n ≪ π ∧
        chi_squared_divergence (μ n) π ≤
          ENNReal.ofReal (1 / (1 + α / (τ : ℝ)) ^ (2 * n)) *
            chi_squared_divergence (μ 0) π := by
    intro n
    induction n with
    | zero =>
        exact ⟨hμ0, by simp⟩
    | succ n ih =>
        have hstep := llt_prox_step_chi_squared_contraction
          hconv hψ hτ hα hπ hPI hcond_prob hcond_meas hmarginal
          hadjoint hforward_range (htrajectory.1 n) ih.1 (htrajectory.2 n)
        refine ⟨hstep.1, ?_⟩
        calc
          chi_squared_divergence (μ (n + 1)) π ≤
              ENNReal.ofReal (1 / (1 + α / (τ : ℝ)) ^ 2) *
                chi_squared_divergence (μ n) π := hstep.2
          _ ≤ ENNReal.ofReal (1 / (1 + α / (τ : ℝ)) ^ 2) *
                (ENNReal.ofReal (1 / (1 + α / (τ : ℝ)) ^ (2 * n)) *
                  chi_squared_divergence (μ 0) π) :=
            mul_le_mul_left' ih.2 _
          _ = ENNReal.ofReal (1 / (1 + α / (τ : ℝ)) ^ (2 * (n + 1))) *
                chi_squared_divergence (μ 0) π := by
            rw [← mul_assoc]
            congr 1
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [← one_div_pow, ← one_div_pow, ← one_div_pow, ← pow_add]
            congr 1
            omega
  exact (hmain k).2

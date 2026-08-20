import Architect
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory

@[blueprint "def:mse"
  (statement := /-- Let $(\Omega, \mathcal{F}, P)$ be a probability space and let $Y : \Omega \to \mathbb{R}$ be the label variable. For a predictor $g : \Omega \to \mathbb{R}$, its \emph{mean squared error} is
  \[
    \mathrm{MSE}(g) := \mathbb{E}\big[(Y - g)^2\big] = \int_\Omega (Y(\omega) - g(\omega))^2 \, \mathrm{d}P(\omega).
  \] -/)
  (title := /-- Mean squared error -/)
  (latexEnv := "definition")]
noncomputable def mse {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y g : Ω → ℝ) : ℝ :=
  ∫ ω, (Y ω - g ω) ^ 2 ∂P

@[blueprint "def:disagreement"
  (statement := /-- Let $(\Omega, \mathcal{F}, P)$ be a probability space. For two predictors $g_1, g_2 : \Omega \to \mathbb{R}$, their \emph{disagreement} is
  \[
    D(g_1, g_2) := \mathbb{E}\big[(g_1 - g_2)^2\big] = \int_\Omega (g_1(\omega) - g_2(\omega))^2 \, \mathrm{d}P(\omega).
  \] -/)
  (title := /-- Disagreement between two predictors -/)
  (latexEnv := "definition")]
noncomputable def disagreement {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (g₁ g₂ : Ω → ℝ) : ℝ :=
  ∫ ω, (g₁ ω - g₂ ω) ^ 2 ∂P

@[blueprint "def:average-predictor"
  (statement := /-- For two predictors $g_1, g_2 : \Omega \to \mathbb{R}$, their \emph{midpoint} (average) predictor $\bar g : \Omega \to \mathbb{R}$ is defined pointwise by
  \[
    \bar g(\omega) := \tfrac{1}{2}\big(g_1(\omega) + g_2(\omega)\big).
  \] -/)
  (title := /-- Midpoint (average) predictor -/)
  (latexEnv := "definition")]
noncomputable def average_predictor {Ω : Type*} (g₁ g₂ : Ω → ℝ) : Ω → ℝ :=
  fun ω => (g₁ ω + g₂ ω) / 2

@[blueprint "def:population-risk"
  (statement := /-- Let $(\Omega, \mathcal{F}, P)$ be a probability space and let $Y : \Omega \to \mathbb{R}$ be the label variable. For a class of predictors $\mathcal{H} \subseteq (\Omega \to \mathbb{R})$, the \emph{population risk} of the class is the infimum of the mean squared error over the class:
  \[
    R(\mathcal{H}) := \inf_{g \in \mathcal{H}} \mathrm{MSE}(g).
  \]
  Here the infimum is taken over the image set $\{\,\mathrm{MSE}(g) : g \in \mathcal{H}\,\} \subseteq \mathbb{R}$. -/)
  (title := /-- Population risk of a predictor class -/)
  (latexEnv := "definition")]
noncomputable def population_risk {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℝ)
    (H : Set (Ω → ℝ)) : ℝ :=
  sInf ((fun g => mse P Y g) '' H)

@[blueprint "lem:mse-nonneg"
  (statement := /-- Let $(\Omega, \mathcal{F})$ be a measurable space equipped with a measure $P$, and let $Y, g : \Omega \to \mathbb{R}$. Then the mean squared error is nonnegative:
  \[
    0 \le \mathrm{MSE}(g) = \int_\Omega (Y(\omega) - g(\omega))^2 \, \mathrm{d}P(\omega).
  \] -/)
  (proof := /-- The integrand $\omega \mapsto (Y(\omega) - g(\omega))^2$ is nonnegative pointwise, being a square of a real number. Hence its integral against the measure $P$ is nonnegative. -/)
  (title := /-- Nonnegativity of the mean squared error -/)
  (latexEnv := "lemma")]
lemma mse_nonneg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y g : Ω → ℝ) :
    0 ≤ mse P Y g := by
  unfold mse
  apply integral_nonneg
  intro ω
  positivity

@[blueprint "lem:midpoint-identity"
  (statement := /-- Let $(\Omega, \mathcal{F}, P)$ be a probability space, let $Y : \Omega \to \mathbb{R}$ be the label variable, and let $f_1, f_2 : \Omega \to \mathbb{R}$ be predictors with $Y, f_1, f_2 \in L^2(P)$. Let $\bar f := \tfrac{1}{2}(f_1 + f_2)$ be their midpoint predictor. Then
  \[
    D(f_1, f_2) = 2\big(\mathrm{MSE}(f_1) + \mathrm{MSE}(f_2) - 2\,\mathrm{MSE}(\bar f)\big).
  \] -/)
  (proof := /-- The proof reduces the identity to a pointwise algebraic equality that is then integrated term by term.

  \emph{Integrability.} Since $Y, f_1, f_2 \in L^2(P)$, each difference $Y - f_1$, $Y - f_2$, and $Y - \bar f$ lies in $L^2(P)$: the first two by closure of $L^2(P)$ under subtraction, and $\bar f = \tfrac{1}{2}(f_1 + f_2)$ lies in $L^2(P)$ by closure under addition and scalar multiplication, so $Y - \bar f \in L^2(P)$ as well. Consequently the squares $(Y - f_1)^2$, $(Y - f_2)^2$, and $(Y - \bar f)^2$ are all integrable, and hence so are the functions $2(Y - f_1)^2 + 2(Y - f_2)^2$ and $4(Y - \bar f)^2$.

  \emph{Pointwise identity.} For every $\omega \in \Omega$, expanding $\bar f(\omega) = \tfrac{1}{2}(f_1(\omega) + f_2(\omega))$ gives the elementary real-number identity
  \[
    (f_1(\omega) - f_2(\omega))^2
    = 2\,(Y(\omega) - f_1(\omega))^2 + 2\,(Y(\omega) - f_2(\omega))^2 - 4\,(Y(\omega) - \bar f(\omega))^2 .
  \]

  \emph{Integration.} Integrating this identity over $P$ and using linearity of the integral, which applies because all the integrands above are integrable,
  \[
    D(f_1, f_2)
    = \int (f_1 - f_2)^2 \, \mathrm{d}P
    = 2\!\int (Y - f_1)^2 \mathrm{d}P + 2\!\int (Y - f_2)^2 \mathrm{d}P - 4\!\int (Y - \bar f)^2 \mathrm{d}P .
  \]
  Recognising $\int (Y - f_i)^2 \, \mathrm{d}P = \mathrm{MSE}(f_i)$ and $\int (Y - \bar f)^2 \, \mathrm{d}P = \mathrm{MSE}(\bar f)$, the right-hand side equals $2\big(\mathrm{MSE}(f_1) + \mathrm{MSE}(f_2) - 2\,\mathrm{MSE}(\bar f)\big)$, which is the claim. -/)
  (title := /-- Midpoint identity for squared loss -/)
  (latexEnv := "lemma")]
lemma midpoint_identity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y f₁ f₂ : Ω → ℝ)
    (hY : MemLp Y 2 P) (h₁ : MemLp f₁ 2 P) (h₂ : MemLp f₂ 2 P) :
    disagreement P f₁ f₂ =
      2 * (mse P Y f₁ + mse P Y f₂ - 2 * mse P Y (average_predictor f₁ f₂)) := by
  have i1 : Integrable (fun ω => (Y ω - f₁ ω) ^ 2) P := (hY.sub h₁).integrable_sq
  have i2 : Integrable (fun ω => (Y ω - f₂ ω) ^ 2) P := (hY.sub h₂).integrable_sq
  have hbar : MemLp (average_predictor f₁ f₂) 2 P := by
    have h := (h₁.add h₂).const_mul (2⁻¹ : ℝ)
    have he : (fun ω => (2⁻¹ : ℝ) * (f₁ + f₂) ω) = average_predictor f₁ f₂ := by
      funext ω
      simp only [average_predictor, Pi.add_apply]
      ring
    rwa [he] at h
  have i3 : Integrable (fun ω => (Y ω - average_predictor f₁ f₂ ω) ^ 2) P :=
    (hY.sub hbar).integrable_sq
  have iA : Integrable
      (fun ω => 2 * (Y ω - f₁ ω) ^ 2 + 2 * (Y ω - f₂ ω) ^ 2) P :=
    (i1.const_mul 2).add (i2.const_mul 2)
  have iB : Integrable (fun ω => 4 * (Y ω - average_predictor f₁ f₂ ω) ^ 2) P :=
    i3.const_mul 4
  have key : ∫ ω, (f₁ ω - f₂ ω) ^ 2 ∂P
      = ∫ ω, (2 * (Y ω - f₁ ω) ^ 2 + 2 * (Y ω - f₂ ω) ^ 2
          - 4 * (Y ω - average_predictor f₁ f₂ ω) ^ 2) ∂P := by
    apply integral_congr_ae
    filter_upwards with ω
    simp only [average_predictor]
    ring
  simp only [disagreement, mse]
  rw [key, integral_sub iA iB, integral_add (i1.const_mul 2) (i2.const_mul 2),
    integral_const_mul, integral_const_mul, integral_const_mul]
  ring

@[blueprint "lem:population-risk-le"
  (statement := /-- Let $(\Omega, \mathcal{F})$ be a measurable space equipped with a measure $P$, let $Y : \Omega \to \mathbb{R}$, and let $\mathcal{H} \subseteq (\Omega \to \mathbb{R})$ be a class of predictors. If $g \in \mathcal{H}$, then
  \[
    R(\mathcal{H}) \le \mathrm{MSE}(g).
  \] -/)
  (proof := /-- By \cref{def:population-risk}, $R(\mathcal{H})$ is the infimum of the set $S := \{\,\mathrm{MSE}(h) : h \in \mathcal{H}\,\}$. By \cref{lem:mse-nonneg}, every element of $S$ is at least $0$, so $S$ is bounded below by $0$. Since $g \in \mathcal{H}$, we have $\mathrm{MSE}(g) \in S$. The infimum of a set bounded below is a lower bound for each of its elements, hence $R(\mathcal{H}) = \inf S \le \mathrm{MSE}(g)$. -/)
  (title := /-- Population risk lower-bounds the error of any class member -/)
  (latexEnv := "lemma")]
lemma population_risk_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ) (H : Set (Ω → ℝ)) (g : Ω → ℝ) (hg : g ∈ H) :
    population_risk P Y H ≤ mse P Y g := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro x ⟨h, -, rfl⟩
    exact mse_nonneg P Y h
  · exact ⟨g, hg, rfl⟩

@[blueprint "thm:midpoint-anchor"
  (statement := /-- Let $(\Omega, \mathcal{F}, P)$ be a probability space, let $Y : \Omega \to \mathbb{R}$ be the label variable, and let $f_1, f_2 : \Omega \to \mathbb{R}$ be predictors with $Y, f_1, f_2 \in L^2(P)$. Let $\bar f := \tfrac{1}{2}(f_1 + f_2)$ be their midpoint predictor, and let $\mathcal{H} \subseteq (\Omega \to \mathbb{R})$ be a class of predictors. If $\bar f \in \mathcal{H}$, then
  \[
    D(f_1, f_2) \le 2\big(\mathrm{MSE}(f_1) - R(\mathcal{H})\big) + 2\big(\mathrm{MSE}(f_2) - R(\mathcal{H})\big).
  \] -/)
  (proof := /-- By \cref{lem:midpoint-identity}, using $Y, f_1, f_2 \in L^2(P)$,
  \[
    D(f_1, f_2) = 2\big(\mathrm{MSE}(f_1) + \mathrm{MSE}(f_2) - 2\,\mathrm{MSE}(\bar f)\big).
  \]
  Since $\bar f \in \mathcal{H}$, \cref{lem:population-risk-le} gives $R(\mathcal{H}) \le \mathrm{MSE}(\bar f)$, equivalently $-2\,\mathrm{MSE}(\bar f) \le -2\,R(\mathcal{H})$. Substituting this bound into the identity,
  \[
    D(f_1, f_2) \le 2\big(\mathrm{MSE}(f_1) + \mathrm{MSE}(f_2) - 2\,R(\mathcal{H})\big)
    = 2\big(\mathrm{MSE}(f_1) - R(\mathcal{H})\big) + 2\big(\mathrm{MSE}(f_2) - R(\mathcal{H})\big),
  \]
  which is the claim. -/)
  (title := /-- Disagreement via the midpoint anchor -/)
  (latexEnv := "theorem")]
theorem midpoint_anchor {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y f₁ f₂ : Ω → ℝ) (H : Set (Ω → ℝ))
    (hY : MemLp Y 2 P) (h₁ : MemLp f₁ 2 P) (h₂ : MemLp f₂ 2 P)
    (hmem : average_predictor f₁ f₂ ∈ H) :
    disagreement P f₁ f₂ ≤
      2 * (mse P Y f₁ - population_risk P Y H) +
      2 * (mse P Y f₂ - population_risk P Y H) := by
  rw [midpoint_identity P Y f₁ f₂ hY h₁ h₂]
  have hle : population_risk P Y H ≤ mse P Y (average_predictor f₁ f₂) :=
    population_risk_le P Y H (average_predictor f₁ f₂) hmem
  linarith

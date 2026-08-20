import Architect
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:domain-supremum"
  (statement := /-- Let $E$ be a type, let $\Omega\subseteq E$, and let $f:E\to\mathbb{R}$. The domain supremum of $f$ is
  \[
    \sup_{s\in\Omega} f(s).
  \] -/)
  (title := /-- Domain supremum -/)
  (latexEnv := "definition")]
noncomputable def domain_supremum {E : Type} (Ω : Set E) (f : E → ℝ) : ℝ :=
  sSup (f '' Ω)

@[blueprint "def:domain-infimum"
  (statement := /-- Let $E$ be a type, let $\Omega\subseteq E$, and let $g:E\to\mathbb{R}$. The domain infimum of $g$ is
  \[
    \inf_{s\in\Omega} g(s).
  \] -/)
  (title := /-- Domain infimum -/)
  (latexEnv := "definition")]
noncomputable def domain_infimum {E : Type} (Ω : Set E) (g : E → ℝ) : ℝ :=
  sInf (g '' Ω)

@[blueprint "def:scalar-transport-conditions"
  (statement := /-- Let $E$ be a real normed vector space, let $\Omega\subseteq E$, let $f,g:E\to\mathbb{R}$, and let $f^*,g_*\in\mathbb{R}$. The scalar transport conditions assert that $\Omega$ is nonempty, compact, and convex; that $f$ and $g$ are continuous on $\Omega$; that $g(s)\leq f(s)$ for every $s\in\Omega$; that $f^*=\sup_{s\in\Omega}f(s)$ and $g_*=\inf_{s\in\Omega}g(s)$; that $-1<g_*$; and that there is an $s\in\Omega$ for which $f(s)\neq0$ or $g(s)\neq0$. No sign is imposed on either extremum relative to zero. -/)
  (title := /-- Scalar transport conditions -/)
  (latexEnv := "definition")]
noncomputable def scalar_transport_conditions
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set E) (f g : E → ℝ) (fStar gStar : ℝ) : Prop :=
  Ω.Nonempty ∧
    IsCompact Ω ∧
    Convex ℝ Ω ∧
    ContinuousOn f Ω ∧
    ContinuousOn g Ω ∧
    (∀ s ∈ Ω, g s ≤ f s) ∧
    fStar = domain_supremum Ω f ∧
    gStar = domain_infimum Ω g ∧
    -1 < gStar ∧
    ∃ s ∈ Ω, f s ≠ 0 ∨ g s ≠ 0

@[blueprint "def:transport-upper-deviation"
  (statement := /-- Let $I$ be a nonempty finite index set and let $\sigma_i(s)$, for $i\in I$, be a finite family of real numbers depending on $s\in E$. Define
  \[
    f(s)=\max_{i\in I}\sigma_i(s)-1.
  \]
  For Jacobian eigenvalues this is the deviation of the largest eigenvalue from one. -/)
  (title := /-- Upper spectral deviation -/)
  (latexEnv := "definition")]
noncomputable def transport_upper_deviation
    {I E : Type} [Fintype I] [Nonempty I]
    (σ : E → I → ℝ) (s : E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (σ s) - 1

@[blueprint "def:transport-lower-deviation"
  (statement := /-- Let $I$ be a nonempty finite index set and let $\sigma_i(s)$, for $i\in I$, be a finite family of real numbers depending on $s\in E$. Define
  \[
    g(s)=\min_{i\in I}\sigma_i(s)-1.
  \]
  For Jacobian eigenvalues this is the deviation of the smallest eigenvalue from one. -/)
  (title := /-- Lower spectral deviation -/)
  (latexEnv := "definition")]
noncomputable def transport_lower_deviation
    {I E : Type} [Fintype I] [Nonempty I]
    (σ : E → I → ℝ) (s : E) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (σ s) - 1

@[blueprint "def:transport-conditions"
  (statement := /-- Let $d\geq1$, put $E=\mathbb{R}^{d}$ with its Euclidean structure, and let $\Omega\subseteq E$. Let $T:E\to E$, let $\mu$ and $\nu$ be Borel probability measures, and let $e_i(s)$ and $\sigma_i(s)$ be respectively an orthonormal basis and a real number for every $s\in E$ and $1\leq i\leq d$. The transport conditions assert that $\Omega$ is nonempty, compact, and convex; that $T$ is $C^1$ on $\Omega$; and that
  \[
    D T(s)e_i(s)=\sigma_i(s)e_i(s),\qquad \sigma_i(s)>0
  \]
  for every $s\in\Omega$ and $1\leq i\leq d$. Thus the derivative is represented by a symmetric positive-definite operator in a complete orthonormal eigenbasis. They further assert that $\mu$ and $\nu$ are absolutely continuous with respect to Lebesgue measure, are supported on $\Omega$, satisfy $T_{\sharp}\mu=\nu$, and that $\sigma_i(s)\neq1$ for at least one $s\in\Omega$ and one $1\leq i\leq d$. -/)
  (title := /-- Regular nonisometric transport data -/)
  (latexEnv := "definition")]
noncomputable def transport_conditions
    {d : ℕ} [NeZero d]
    (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (μ ν : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))
    (eigenbasis :
      EuclideanSpace ℝ (Fin d) →
        OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (σ : EuclideanSpace ℝ (Fin d) → Fin d → ℝ) : Prop :=
  Ω.Nonempty ∧
    IsCompact Ω ∧
    Convex ℝ Ω ∧
    ContDiffOn ℝ 1 T Ω ∧
    (∀ s ∈ Ω, ∀ i,
      fderivWithin ℝ T Ω s (eigenbasis s i) =
        (σ s i) • eigenbasis s i) ∧
    (∀ s ∈ Ω, ∀ i, 0 < σ s i) ∧
    MeasureTheory.IsProbabilityMeasure μ ∧
    MeasureTheory.IsProbabilityMeasure ν ∧
    MeasureTheory.Measure.AbsolutelyContinuous μ
      MeasureTheory.MeasureSpace.volume ∧
    MeasureTheory.Measure.AbsolutelyContinuous ν
      MeasureTheory.MeasureSpace.volume ∧
    μ Ωᶜ = 0 ∧
    ν Ωᶜ = 0 ∧
    MeasureTheory.Measure.map T μ = ν ∧
    ∃ s ∈ Ω, ∃ i, σ s i ≠ 1

@[blueprint "def:is-unit-schedule"
  (statement := /-- A unit schedule is a continuously differentiable, nondecreasing map $\tau:[0,1]\to[0,1]$ satisfying $\tau(0)=0$ and $\tau(1)=1$. It is represented by a function $\tau:\mathbb{R}\to\mathbb{R}$ together with conditions restricted to $[0,1]$. -/)
  (title := /-- Unit schedule -/)
  (latexEnv := "definition")]
noncomputable def is_unit_schedule (τ : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 1 τ (Set.Icc 0 1) ∧
    MonotoneOn τ (Set.Icc 0 1) ∧
    Set.MapsTo τ (Set.Icc 0 1) (Set.Icc 0 1) ∧
    τ 0 = 0 ∧
    τ 1 = 1

@[blueprint "def:l-inf-speed"
  (statement := /-- Let $\Omega\subseteq E$, let $f,g:E\to\mathbb{R}$, and let $x\in\mathbb{R}$. Define the reciprocal speed factor
  \[
    M(x)=\max\left\{
      \sup_{s\in\Omega}\left|\frac{f(s)}{1+xf(s)}\right|,
      \sup_{s\in\Omega}\left|\frac{g(s)}{1+xg(s)}\right|
    \right\}.
  \]
  Under the compactness and continuity hypotheses in the scalar transport conditions, these suprema agree with the corresponding $L^\infty$ norms in the source ODE. -/)
  (title := /-- Supremal ODE speed factor -/)
  (latexEnv := "definition")]
noncomputable def l_inf_speed {E : Type}
    (Ω : Set E) (f g : E → ℝ) (x : ℝ) : ℝ :=
  max
    (sSup ((fun s => |f s / (1 + x * f s)|) '' Ω))
    (sSup ((fun s => |g s / (1 + x * g s)|) '' Ω))

@[blueprint "def:solves-l-inf-ode"
  (statement := /-- Let $\Omega\subseteq E$ and let $f,g:E\to\mathbb{R}$. A function $\tau:\mathbb{R}\to\mathbb{R}$ solves the normalized $L^\infty$ schedule ODE when it is a unit schedule and there exists $Z>0$ such that, for every $t\in(0,1)$,
  \[
    \dot\tau(t)=\frac{1}{Z}\,M(\tau(t))^{-1},
  \]
  where $M$ is the supremal speed factor of \cref{def:l-inf-speed}. The endpoint conditions in \cref{def:is-unit-schedule} determine the normalization $Z$. -/)
  (title := /-- Normalized $L^\infty$ schedule ODE -/)
  (latexEnv := "definition")]
noncomputable def solves_l_inf_ode {E : Type}
    (Ω : Set E) (f g : E → ℝ) (τ : ℝ → ℝ) : Prop :=
  is_unit_schedule τ ∧
    ∃ Z : ℝ, 0 < Z ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt τ (Z⁻¹ * (l_inf_speed Ω f g (τ t))⁻¹) t

@[blueprint "def:transition-time"
  (statement := /-- For $f^*>0$ and $-1<g_*<0$, define the transition time
  \[
    t_0=
    \frac{\log\!\left(\frac12\left(1-\frac{f^*}{g_*}\right)\right)}
    {\log\!\left(\frac14\left(2-\frac{f^*}{g_*}-\frac{g_*}{f^*}\right)\right)
      -\log(g_*+1)}.
  \] -/)
  (title := /-- Transition time -/)
  (latexEnv := "definition")]
noncomputable def transition_time (fStar gStar : ℝ) : ℝ :=
  Real.log ((1 / 2) * (1 - fStar / gStar)) /
    (Real.log ((1 / 4) * (2 - fStar / gStar - gStar / fStar)) -
      Real.log (gStar + 1))

@[blueprint "def:transition-time-defined"
  (statement := /-- Let $f^*,g_*\in\mathbb{R}$. The displayed transition time is defined when
  \[
    g_*<0<f^*
  \]
  and its logarithmic denominator
  \[
    \log\!\left(\frac14\left(2-\frac{f^*}{g_*}-\frac{g_*}{f^*}\right)\right)
      -\log(g_*+1)
  \]
  is nonzero. Under the scalar transport conditions, the first inequalities also make both logarithmic arguments strictly positive. -/)
  (title := /-- Definedness of the transition time -/)
  (latexEnv := "definition")]
abbrev transition_time_defined (fStar gStar : ℝ) : Prop :=
  gStar < 0 ∧
    0 < fStar ∧
    Real.log ((1 / 4) * (2 - fStar / gStar - gStar / fStar)) -
        Real.log (gStar + 1) ≠ 0

@[blueprint "def:transition-value"
  (statement := /-- For nonzero $f^*,g_*\in\mathbb{R}$, define the transition value
  \[
    x_0=-\frac12\left(\frac1{f^*}+\frac1{g_*}\right).
  \] -/)
  (title := /-- Transition value -/)
  (latexEnv := "definition")]
noncomputable def transition_value (fStar gStar : ℝ) : ℝ :=
  -(1 / 2) * (1 / fStar + 1 / gStar)

@[blueprint "def:transition-left-formula"
  (statement := /-- For $f^*,g_*\in\mathbb{R}$ and $t\in\mathbb{R}$, define the first transition-regime branch
  \[
    \tau_-(t)=\frac1{f^*}
    \left\{\frac{1}{4(g_*+1)}
    \left(2-\frac{f^*}{g_*}-\frac{g_*}{f^*}\right)\right\}^{t}
    -\frac1{f^*}.
  \] -/)
  (title := /-- First transition-regime branch -/)
  (latexEnv := "definition")]
noncomputable def transition_left_formula (fStar gStar t : ℝ) : ℝ :=
  (1 / fStar) *
      (((1 / (4 * (gStar + 1))) *
        (2 - fStar / gStar - gStar / fStar)) ^ t) -
    1 / fStar

@[blueprint "def:transition-right-formula"
  (statement := /-- For $f^*,g_*\in\mathbb{R}$ and $t\in\mathbb{R}$, define the second transition-regime branch
  \[
    \tau_+(t)=
    \frac12\left(\frac1{g_*}-\frac1{f^*}\right)
    \left\{\frac{2(g_*+1)}{1-g_*/f^*}\right\}^{t}
    \left\{\frac12\left(1-\frac{f^*}{g_*}\right)\right\}^{1-t}
    -\frac1{g_*}.
  \] -/)
  (title := /-- Second transition-regime branch -/)
  (latexEnv := "definition")]
noncomputable def transition_right_formula (fStar gStar t : ℝ) : ℝ :=
  (1 / 2) * (1 / gStar - 1 / fStar) *
      ((2 * (gStar + 1) / (1 - gStar / fStar)) ^ t) *
      (((1 / 2) * (1 - fStar / gStar)) ^ (1 - t)) -
    1 / gStar

@[blueprint "def:expanding-formula"
  (statement := /-- For $f^*\in\mathbb{R}$ and $t\in\mathbb{R}$, define
  \[
    \tau_f(t)=\frac{(f^*+1)^t-1}{f^*}.
  \] -/)
  (title := /-- Expanding no-transition formula -/)
  (latexEnv := "definition")]
noncomputable def expanding_formula (fStar t : ℝ) : ℝ :=
  ((fStar + 1) ^ t - 1) / fStar

@[blueprint "def:contracting-formula"
  (statement := /-- For $g_*\in\mathbb{R}$ and $t\in\mathbb{R}$, define
  \[
    \tau_g(t)=\frac{(g_*+1)^t-1}{g_*}.
  \] -/)
  (title := /-- Contracting no-transition formula -/)
  (latexEnv := "definition")]
noncomputable def contracting_formula (gStar t : ℝ) : ℝ :=
  ((gStar + 1) ^ t - 1) / gStar

@[blueprint "def:has-transition-formula"
  (statement := /-- Let $\tau:\mathbb{R}\to\mathbb{R}$ and let $f^*,g_*\in\mathbb{R}$. The transition formula holds when, with $t_0$ as in \cref{def:transition-time}, one has
  \[
    \tau(t_0)=-\frac12\left(\frac1{f^*}+\frac1{g_*}\right),
  \]
  and, for every $t\in[0,1]$, the first displayed branch holds whenever $t\leq t_0$ and the second displayed branch holds whenever $t_0\leq t$. In particular, both branch identities are required at $t=t_0$. -/)
  (title := /-- The two-branch transition formula -/)
  (latexEnv := "definition")]
noncomputable def has_transition_formula
    (τ : ℝ → ℝ) (fStar gStar : ℝ) : Prop :=
  let t₀ := transition_time fStar gStar
  τ t₀ = transition_value fStar gStar ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (t ≤ t₀ → τ t = transition_left_formula fStar gStar t) ∧
      (t₀ ≤ t → τ t = transition_right_formula fStar gStar t)

@[blueprint "def:has-expanding-formula"
  (statement := /-- Let $\tau:\mathbb{R}\to\mathbb{R}$ and let $f^*\in\mathbb{R}$. The expanding no-transition formula holds when
  \[
    \tau(t)=\frac{(f^*+1)^t-1}{f^*}
  \]
  for every $t\in[0,1]$. -/)
  (title := /-- The expanding no-transition formula -/)
  (latexEnv := "definition")]
noncomputable def has_expanding_formula (τ : ℝ → ℝ) (fStar : ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1, τ t = expanding_formula fStar t

@[blueprint "def:has-contracting-formula"
  (statement := /-- Let $\tau:\mathbb{R}\to\mathbb{R}$ and let $g_*\in\mathbb{R}$. The contracting no-transition formula holds when
  \[
    \tau(t)=\frac{(g_*+1)^t-1}{g_*}
  \]
  for every $t\in[0,1]$. -/)
  (title := /-- The contracting no-transition formula -/)
  (latexEnv := "definition")]
noncomputable def has_contracting_formula (τ : ℝ → ℝ) (gStar : ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1, τ t = contracting_formula gStar t

@[blueprint "lem:transition-regime-speed-formula-aux"
  (statement := /-- Let $E$ be a real normed vector space, let $\Omega\subseteq E$, and suppose that $f,g:E\to\mathbb R$ have extrema $f^*,g_*$ satisfying the scalar transport conditions. If $g_*<0<f^*$ and $x\in[0,1]$, then the supremal speed factor is
  \[
    M(x)=\max\left\{\frac{f^*}{1+xf^*},\frac{-g_*}{1+xg_*}\right\}.
  \] -/)
  (proof := /-- By compactness and continuity in \cref{def:scalar-transport-conditions}, $f$ attains its maximum $f^*$ and $g$ attains its minimum $g_*$. Every value of either function therefore lies in $[g_*,f^*]$. Since $-1<g_*$ and $x\in[0,1]$, all denominators $1+xy$ on this interval are positive. On $[0,f^*]$ the quotient $y/(1+xy)$ is increasing, while on $[g_*,0)$ its absolute value is $-y/(1+xy)$ and is bounded by its value at $g_*$. Thus every term in each supremum defining \cref{def:l-inf-speed} is bounded by the displayed maximum. The points attaining $f^*$ and $g_*$ give the reverse inequalities. -/)
  (title := /-- Extremal formula for the transition-regime speed -/)
  (latexEnv := "lemma")]
lemma transition_regime_speed_formula_aux
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set E) (f g : E → ℝ) (fStar gStar x : ℝ)
    (hdata : scalar_transport_conditions Ω f g fStar gStar)
    (hdefined : transition_time_defined fStar gStar)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    l_inf_speed Ω f g x =
      max (fStar / (1 + x * fStar)) (-gStar / (1 + x * gStar)) := by
  classical
  rcases hdata with
    ⟨hΩne, hΩcompact, hΩconvex, hfcont, hgcont, horder, hfStar, hgStar,
      hgLower, hnonzero⟩
  rcases hdefined with ⟨hgneg, hfpos, hden⟩
  obtain ⟨sf, hsf, hmax⟩ := hΩcompact.exists_isMaxOn hΩne hfcont
  obtain ⟨sg, hsg, hmin⟩ := hΩcompact.exists_isMinOn hΩne hgcont
  have hsfStar : f sf = fStar := by
    rw [hfStar, domain_supremum]
    apply le_antisymm
      (le_csSup (hΩcompact.image_of_continuousOn hfcont).bddAbove
        ⟨sf, hsf, rfl⟩)
    exact csSup_le (Set.image_nonempty.mpr hΩne) (by
      rintro _ ⟨s, hs, rfl⟩
      exact hmax hs)
  have hsgStar : g sg = gStar := by
    rw [hgStar, domain_infimum]
    apply le_antisymm
    · exact le_csInf (Set.image_nonempty.mpr hΩne) (by
        rintro _ ⟨s, hs, rfl⟩
        show g sg ≤ g s
        exact hmin hs)
    · exact csInf_le (hΩcompact.image_of_continuousOn hgcont).bddBelow
        ⟨sg, hsg, rfl⟩
  have hbounds (s : E) (hs : s ∈ Ω) :
      gStar ≤ g s ∧ g s ≤ f s ∧ f s ≤ fStar := by
    constructor
    · rw [← hsgStar]
      show g sg ≤ g s
      exact hmin hs
    constructor
    · exact horder s hs
    · rw [← hsfStar]
      exact hmax hs
  have hratio (y : ℝ) (hylo : gStar ≤ y) (hyhi : y ≤ fStar) :
      |y / (1 + x * y)| ≤
        max (fStar / (1 + x * fStar)) (-gStar / (1 + x * gStar)) := by
    have hdy : 0 < 1 + x * y := by nlinarith [hx.1, hx.2, hgLower]
    have hdf : 0 < 1 + x * fStar := by nlinarith [hx.1, hfpos]
    have hdg : 0 < 1 + x * gStar := by nlinarith [hx.1, hx.2, hgLower]
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg (div_nonneg hy hdy.le)]
      apply le_max_of_le_left
      apply (div_le_div_iff₀ hdy hdf).2
      nlinarith
    · have hyneg : y < 0 := lt_of_not_ge hy
      rw [abs_of_neg (div_neg_of_neg_of_pos hyneg hdy), neg_div]
      apply le_max_of_le_right
      rw [show -(y / (1 + x * y)) = -y / (1 + x * y) by ring,
        show -(gStar / (1 + x * gStar)) = -gStar / (1 + x * gStar) by ring]
      apply (div_le_div_iff₀ hdy hdg).2
      nlinarith
  let A : Set ℝ := (fun s => |f s / (1 + x * f s)|) '' Ω
  let B : Set ℝ := (fun s => |g s / (1 + x * g s)|) '' Ω
  let M : ℝ := max (fStar / (1 + x * fStar)) (-gStar / (1 + x * gStar))
  have hAbdd : BddAbove A := by
    refine ⟨M, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact hratio (f s) (le_trans (hbounds s hs).1 (hbounds s hs).2.1)
      (hbounds s hs).2.2
  have hBbdd : BddAbove B := by
    refine ⟨M, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact hratio (g s) (hbounds s hs).1
      (le_trans (hbounds s hs).2.1 (hbounds s hs).2.2)
  have hdf : 0 < 1 + x * fStar := by nlinarith [hx.1, hfpos]
  have hdg : 0 < 1 + x * gStar := by nlinarith [hx.1, hx.2, hgLower]
  have hqf : fStar / (1 + x * fStar) ∈ A := by
    refine ⟨sf, hsf, ?_⟩
    change |f sf / (1 + x * f sf)| = fStar / (1 + x * fStar)
    rw [hsfStar, abs_of_pos (div_pos hfpos hdf)]
  have hqg : -gStar / (1 + x * gStar) ∈ B := by
    refine ⟨sg, hsg, ?_⟩
    change |g sg / (1 + x * g sg)| = -gStar / (1 + x * gStar)
    rw [hsgStar, abs_of_neg (div_neg_of_neg_of_pos hgneg hdg), neg_div]
  change max (sSup A) (sSup B) = M
  apply le_antisymm
  · exact max_le
      (csSup_le (Set.image_nonempty.mpr hΩne) (by
        rintro _ ⟨s, hs, rfl⟩
        exact hratio (f s) (le_trans (hbounds s hs).1 (hbounds s hs).2.1)
          (hbounds s hs).2.2))
      (csSup_le (Set.image_nonempty.mpr hΩne) (by
        rintro _ ⟨s, hs, rfl⟩
        exact hratio (g s) (hbounds s hs).1
          (le_trans (hbounds s hs).2.1 (hbounds s hs).2.2)))
  · exact max_le
      (le_trans (le_csSup hAbdd hqf) (le_max_left _ _))
      (le_trans (le_csSup hBbdd hqg) (le_max_right _ _))

@[blueprint "lem:transition-regime-algebra-aux"
  (statement := /-- Let $-1<g_*<0<f^*$, suppose that the transition time is defined, and assume that it belongs to $[0,1]$. Put
  \[
    H=\frac12\left(1-\frac{f^*}{g_*}\right),\quad
    R=\frac{2(g_*+1)}{1-g_*/f^*},\quad
    C=\frac{1}{4(g_*+1)}\left(2-\frac{f^*}{g_*}-\frac{g_*}{f^*}\right).
  \]
  Then the transition value belongs to $[0,1]$, the three constants are positive, $C>1$, $C=H/R$, and $t_0=\log H/\log C$. -/)
  (proof := /-- Set $Q=\frac14(2-f^*/g_*-g_*/f^*)$. The identity $Q=(f^*-g_*)^2/(4f^*(-g_*))$ and the nonnegativity of $(f^*+g_*)^2$ give $Q\geq1$. Since $0<g_*+1<1$, one has $C=Q/(g_*+1)>1$, and logarithmic additivity identifies the denominator defining \cref{def:transition-time} with $\log C>0$. The inequalities $0\leq t_0\leq1$ therefore imply $0\leq\log H\leq\log C$, hence $1\leq H\leq C$. Cross multiplication translates these two inequalities into $0\leq-\frac12(1/f^*+1/g_*)\leq1$. Direct field identities give the positivity of $H$ and $R$, the factorization $C=H/R$, and the asserted expression for $t_0$. -/)
  (title := /-- Algebra of the transition parameters -/)
  (latexEnv := "lemma")]
lemma transition_regime_algebra_aux
    (fStar gStar : ℝ) (hgLower : -1 < gStar)
    (hdefined : transition_time_defined fStar gStar)
    (ht₀ : transition_time fStar gStar ∈ Set.Icc (0 : ℝ) 1) :
    transition_value fStar gStar ∈ Set.Icc (0 : ℝ) 1 ∧
      (let H := (1 / 2 : ℝ) * (1 - fStar / gStar)
       let R := 2 * (gStar + 1) / (1 - gStar / fStar)
       let C := (1 / (4 * (gStar + 1))) *
          (2 - fStar / gStar - gStar / fStar)
       0 < H ∧ 0 < R ∧ 1 < C ∧ C = H / R ∧
         transition_time fStar gStar = Real.log H / Real.log C) := by
  rcases hdefined with ⟨hgneg, hfpos, hden⟩
  have hfne : fStar ≠ 0 := hfpos.ne'
  have hgne : gStar ≠ 0 := hgneg.ne
  have hgplus : 0 < gStar + 1 := by linarith
  let H : ℝ := (1 / 2 : ℝ) * (1 - fStar / gStar)
  let R : ℝ := 2 * (gStar + 1) / (1 - gStar / fStar)
  let Q : ℝ := (1 / 4 : ℝ) *
    (2 - fStar / gStar - gStar / fStar)
  let C : ℝ := (1 / (4 * (gStar + 1))) *
    (2 - fStar / gStar - gStar / fStar)
  have hQone : 1 ≤ Q := by
    dsimp [Q]
    rw [show (1 / 4 : ℝ) *
        (2 - fStar / gStar - gStar / fStar) =
        (fStar - gStar) ^ 2 / (4 * fStar * (-gStar)) by
      field_simp [hfne, hgne]
      <;> ring]
    rw [le_div_iff₀ (mul_pos (mul_pos (by norm_num) hfpos) (neg_pos.mpr hgneg))]
    nlinarith [sq_nonneg (fStar + gStar)]
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQone
  have hCeq : C = Q / (gStar + 1) := by
    dsimp [C, Q]
    field_simp [hgplus.ne']
    <;> ring
  have hCone : 1 < C := by
    rw [hCeq, one_lt_div hgplus]
    exact lt_of_lt_of_le (by linarith) hQone
  have hCpos : 0 < C := lt_trans zero_lt_one hCone
  have hHpos : 0 < H := by
    dsimp [H]
    have : fStar / gStar < 0 := div_neg_of_pos_of_neg hfpos hgneg
    linarith
  have hRpos : 0 < R := by
    dsimp [R]
    have : gStar / fStar < 0 := div_neg_of_neg_of_pos hgneg hfpos
    exact div_pos (mul_pos (by norm_num) hgplus) (by linarith)
  have hdenlog :
      Real.log Q - Real.log (gStar + 1) = Real.log C := by
    rw [hCeq, Real.log_div hQpos.ne' hgplus.ne']
  have htform : transition_time fStar gStar = Real.log H / Real.log C := by
    unfold transition_time
    change Real.log H /
      (Real.log Q - Real.log (gStar + 1)) = _
    rw [hdenlog]
  have hlogC : 0 < Real.log C := Real.log_pos hCone
  have htIcc : Real.log H / Real.log C ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [htform] using ht₀
  have hlogHnonneg : 0 ≤ Real.log H := by
    rcases div_nonneg_iff.mp htIcc.1 with h | h
    · exact h.1
    · exfalso
      linarith [h.2, hlogC]
  have hlogHle : Real.log H ≤ Real.log C :=
    (div_le_one hlogC).mp htIcc.2
  have hHone : 1 ≤ H := by
    have hexp := Real.exp_le_exp.mpr hlogHnonneg
    simpa [Real.exp_log hHpos] using hexp
  have hHC : H ≤ C := (Real.log_le_log_iff hHpos hCpos).mp hlogHle
  have hxnonneg : 0 ≤ transition_value fStar gStar := by
    have hdiv : fStar / gStar ≤ -1 := by
      dsimp [H] at hHone
      linarith
    have hsum : 0 ≤ fStar + gStar := by
      have := (div_le_iff_of_neg hgneg).mp hdiv
      linarith
    rw [show transition_value fStar gStar =
        (fStar + gStar) / (-2 * fStar * gStar) by
      unfold transition_value
      field_simp [hfne, hgne]
      <;> ring]
    have hdenx : 0 < -2 * fStar * gStar := by
      nlinarith [mul_neg_of_pos_of_neg hfpos hgneg]
    exact div_nonneg hsum hdenx.le
  have hxle : transition_value fStar gStar ≤ 1 := by
    have hid : C - H =
        (fStar - gStar) * (-2 * fStar * gStar - fStar - gStar) /
          (-4 * fStar * gStar * (gStar + 1)) := by
      dsimp [C, H]
      field_simp [hfne, hgne, hgplus.ne']
      <;> ring
    have hdiff : 0 ≤ C - H := sub_nonneg.mpr hHC
    rw [hid] at hdiff
    have hdenpos : 0 < -4 * fStar * gStar * (gStar + 1) := by
      have hfgneg := mul_neg_of_pos_of_neg hfpos hgneg
      have : 0 < -4 * fStar * gStar := by nlinarith
      exact mul_pos this hgplus
    have hprod : 0 ≤
        (fStar - gStar) * (-2 * fStar * gStar - fStar - gStar) := by
      rcases div_nonneg_iff.mp hdiff with h | h
      · exact h.1
      · exfalso
        linarith [h.2, hdenpos]
    have hcondition : fStar + gStar ≤ -2 * fStar * gStar := by
      have hfactor : 0 < fStar - gStar := by linarith
      have := nonneg_of_mul_nonneg_right hprod hfactor
      linarith
    rw [show transition_value fStar gStar =
        (fStar + gStar) / (-2 * fStar * gStar) by
      unfold transition_value
      field_simp [hfne, hgne]
      <;> ring]
    have hdenx : 0 < -2 * fStar * gStar := by
      nlinarith [mul_neg_of_pos_of_neg hfpos hgneg]
    exact (div_le_one hdenx).2 hcondition
  refine ⟨⟨hxnonneg, hxle⟩, ?_⟩
  change 0 < H ∧ 0 < R ∧ 1 < C ∧ C = H / R ∧
    transition_time fStar gStar = Real.log H / Real.log C
  refine ⟨hHpos, hRpos, hCone, ?_, htform⟩
  dsimp [C, H, R]
  field_simp [hfne, hgne, hgplus.ne']
  <;> ring

@[blueprint "lem:transition-regime-formula"
  (statement := /-- Let $E$ be a real normed vector space. Let $\Omega\subseteq E$, let $f,g:E\to\mathbb{R}$, and let $f^*,g_*\in\mathbb{R}$ satisfy the scalar transport conditions of \cref{def:scalar-transport-conditions}. Let $\tau$ solve the normalized $L^\infty$ schedule ODE of \cref{def:solves-l-inf-ode}. Assume that the transition time $t_0$ of \cref{def:transition-time} is defined in the sense of \cref{def:transition-time-defined} and belongs to $[0,1]$. Then $\tau$ satisfies the two-branch formula of \cref{def:has-transition-formula}. -/)
  (proof := /-- The hypothesis \cref{def:transition-time-defined} ensures that the displayed logarithms and
  quotients defining $t_0$ are taken on their stated domains; hence
  $g_*<0<f^*$ and the logarithmic denominator is nonzero. Together with
  the scalar transport inequality $-1<g_*$, these facts supply all hypotheses of
  \cref{lem:transition-regime-speed-formula-aux}. Thus, for every
  $x\in[0,1]$ the speed factor of \cref{def:l-inf-speed} is
  \[
    M(x)=\max\!\left\{\frac{f^*}{1+xf^*},
      \frac{-g_*}{1+xg_*}\right\}.
  \]
  Put
  \[
    x_0=-\frac12\left(\frac1{f^*}+\frac1{g_*}\right),\qquad
    H=\frac12\left(1-\frac{f^*}{g_*}\right),\qquad
    R=\frac{2(g_*+1)}{1-g_*/f^*},
  \]
  and
  \[
    C=\frac{1}{4(g_*+1)}
      \left(2-\frac{f^*}{g_*}-\frac{g_*}{f^*}\right).
  \]
  The same sign and lower-bound hypotheses, together with
  $t_0\in[0,1]$, allow us to apply
  \cref{lem:transition-regime-algebra-aux}; it gives
  \[
    x_0\in[0,1],\qquad H,R>0,\qquad C>1,\qquad
    C=H/R,\qquad t_0=\frac{\log H}{\log C}.
  \]

  Unpack \cref{def:solves-l-inf-ode}. The schedule is continuous and nondecreasing on $[0,1]$, maps this interval into itself, and satisfies $\tau(0)=0$ and $\tau(1)=1$. The intermediate value theorem therefore supplies $a\in[0,1]$ with $\tau(a)=x_0$. Monotonicity gives $\tau(t)\leq x_0$ for $t\leq a$ and $x_0\leq\tau(t)$ for $a\leq t$. Cross multiplication by the positive denominators in the displayed formula for $M$ consequently selects its first term before $a$ and its second term after $a$.

  Let $Z>0$ be the normalizing constant in \cref{def:solves-l-inf-ode}. On $(0,a)$ the chain rule gives
  \[
    \frac{d}{dt}\log(1+f^*\tau(t))=Z^{-1},
  \]
  while on $(a,1)$ it gives
  \[
    \frac{d}{dt}\log(1+g_*\tau(t))=-Z^{-1}.
  \]
  The logarithmic arguments are positive because $0\leq\tau(t)\leq1$, $f^*>0$, and $-1<g_*<0$. Applying the mean-value theorem on subintervals from $0$ and backward from $1$, respectively, yields
  \[
    \log(1+f^*\tau(t))=Z^{-1}t\quad(0\leq t\leq a)
  \]
  and
  \[
    \log(1+g_*\tau(t))=\log(g_*+1)+Z^{-1}(1-t)
    \quad(a\leq t\leq1).
  \]
  At $t=a$, the identities
  \[
    1+f^*x_0=H,\qquad
    1+g_*x_0=\frac12\left(1-\frac{g_*}{f^*}\right)
      =\frac{g_*+1}{R}
  \]
  show that
  \[
    \log H=Z^{-1}a,\qquad -\log R=Z^{-1}(1-a).
  \]
  Adding these equations and using $C=H/R$ gives $Z^{-1}=\log C$. Since $\log C>0$, the first equation then gives $a=\log H/\log C=t_0$. In particular, $\tau(t_0)=x_0$.

  For $t\leq t_0$, exponentiating the first logarithmic identity gives
  $1+f^*\tau(t)=C^t$, which rearranges to the formula in
  \cref{def:transition-left-formula}. For $t_0\leq t$, exponentiating the second gives
  \[
    1+g_*\tau(t)=(g_*+1)C^{1-t}.
  \]
  The positive-base identities $C=H/R$ and
  $(g_*+1)/R=\frac12(1-g_*/f^*)$ rewrite its right-hand side as
  \[
    \frac12\left(1-\frac{g_*}{f^*}\right)R^tH^{1-t}.
  \]
  Division by the nonzero number $g_*$ and the identity
  \[
    \frac{1}{2g_*}\left(1-\frac{g_*}{f^*}\right)
    =\frac12\left(\frac1{g_*}-\frac1{f^*}\right)
  \]
  give precisely the formula in
  \cref{def:transition-right-formula}. These two branch identities and the crossover value are exactly \cref{def:has-transition-formula}. -/)
  (title := /-- Formula in the transition regime -/)
  (latexEnv := "lemma")]
lemma transition_regime_formula
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set E) (f g : E → ℝ) (fStar gStar : ℝ) (τ : ℝ → ℝ)
    (hdata : scalar_transport_conditions Ω f g fStar gStar)
    (hode : solves_l_inf_ode Ω f g τ)
    (hdefined : transition_time_defined fStar gStar)
    (ht₀ : transition_time fStar gStar ∈ Set.Icc (0 : ℝ) 1) :
    has_transition_formula τ fStar gStar := by
  have hgneg : gStar < 0 := hdefined.1
  have hfpos : 0 < fStar := hdefined.2.1
  have hgLower : -1 < gStar := hdata.2.2.2.2.2.2.2.2.1
  have hfne : fStar ≠ 0 := hfpos.ne'
  have hgne : gStar ≠ 0 := hgneg.ne
  have hgplus : (0 : ℝ) < gStar + 1 := by linarith
  have h1mgf : (0 : ℝ) < 1 - gStar / fStar := by
    have : gStar / fStar < 0 := div_neg_of_neg_of_pos hgneg hfpos
    linarith
  have hfg_neg : fStar * gStar < 0 := mul_neg_of_pos_of_neg hfpos hgneg
  have h2fg_neg : 2 * fStar * gStar < 0 := by nlinarith [hfg_neg]
  have hspeed : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      l_inf_speed Ω f g x =
        max (fStar / (1 + x * fStar)) (-gStar / (1 + x * gStar)) :=
    fun x hx =>
      transition_regime_speed_formula_aux Ω f g fStar gStar x hdata hdefined hx
  obtain ⟨hxIcc, hHpos, hRpos, hCone, hCHR, ht0form⟩ :=
    transition_regime_algebra_aux fStar gStar hgLower hdefined ht₀
  set Hc : ℝ := (1 / 2 : ℝ) * (1 - fStar / gStar) with hHcdef
  set Rc : ℝ := 2 * (gStar + 1) / (1 - gStar / fStar) with hRcdef
  set Cc : ℝ :=
    (1 / (4 * (gStar + 1))) * (2 - fStar / gStar - gStar / fStar) with hCcdef
  have hCpos : 0 < Cc := lt_trans zero_lt_one hCone
  have hlogCpos : 0 < Real.log Cc := Real.log_pos hCone
  have hx0val :
      2 * fStar * gStar * transition_value fStar gStar = -(fStar + gStar) := by
    unfold transition_value
    field_simp [hfne, hgne]
    ring
  have key_le : ∀ y : ℝ, y ≤ transition_value fStar gStar →
      0 ≤ fStar + gStar + 2 * fStar * gStar * y := by
    intro y hy
    nlinarith [hx0val,
      mul_nonneg (sub_nonneg.mpr hy) (neg_nonneg.mpr (le_of_lt h2fg_neg))]
  have key_ge : ∀ y : ℝ, transition_value fStar gStar ≤ y →
      fStar + gStar + 2 * fStar * gStar * y ≤ 0 := by
    intro y hy
    nlinarith [hx0val,
      mul_nonneg (sub_nonneg.mpr hy) (neg_nonneg.mpr (le_of_lt h2fg_neg))]
  rcases hode with ⟨hschedule, Z, hZ, hτderiv⟩
  rcases hschedule with ⟨hτdiff, hτmono, hτmaps, hτzero, hτone⟩
  have hτcont : ContinuousOn τ (Set.Icc (0 : ℝ) 1) := hτdiff.continuousOn
  have hIVT := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hτcont
  rw [hτzero, hτone] at hIVT
  obtain ⟨a, haIcc, haτ⟩ := hIVT hxIcc
  have hbranch_le : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      τ t ≤ transition_value fStar gStar →
      l_inf_speed Ω f g (τ t) = fStar / (1 + τ t * fStar) := by
    intro t ht hle
    rw [hspeed (τ t) (hτmaps ht)]
    have h0 : 0 ≤ τ t := (hτmaps ht).1
    have h1 : τ t ≤ 1 := (hτmaps ht).2
    have hdf : 0 < 1 + τ t * fStar := by nlinarith [h0, hfpos]
    have hdg : 0 < 1 + τ t * gStar := by
      nlinarith [h0, h1, hgLower,
        mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - τ t)
          (by linarith : (0 : ℝ) ≤ -gStar)]
    apply max_eq_left
    rw [div_le_div_iff₀ hdg hdf]
    nlinarith [key_le (τ t) hle]
  have hbranch_ge : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      transition_value fStar gStar ≤ τ t →
      l_inf_speed Ω f g (τ t) = -gStar / (1 + τ t * gStar) := by
    intro t ht hge
    rw [hspeed (τ t) (hτmaps ht)]
    have h0 : 0 ≤ τ t := (hτmaps ht).1
    have h1 : τ t ≤ 1 := (hτmaps ht).2
    have hdf : 0 < 1 + τ t * fStar := by nlinarith [h0, hfpos]
    have hdg : 0 < 1 + τ t * gStar := by
      nlinarith [h0, h1, hgLower,
        mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - τ t)
          (by linarith : (0 : ℝ) ≤ -gStar)]
    apply max_eq_right
    rw [div_le_div_iff₀ hdf hdg]
    nlinarith [key_ge (τ t) hge]
  have harg_pos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < 1 + fStar * τ t := by
    intro t ht
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg hfpos.le (hτmaps ht).1)
  have hargg_pos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < 1 + gStar * τ t := by
    intro t ht
    have h0 : 0 ≤ τ t := (hτmaps ht).1
    have h1 : τ t ≤ 1 := (hτmaps ht).2
    nlinarith [h0, h1, hgLower,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - τ t)
        (by linarith : (0 : ℝ) ≤ -gStar)]
  have hlogf_cont : ContinuousOn (fun t => Real.log (1 + fStar * τ t))
      (Set.Icc (0 : ℝ) 1) :=
    (continuousOn_const.add (continuousOn_const.mul hτcont)).log
      (fun t ht => (harg_pos t ht).ne')
  have hlogg_cont : ContinuousOn (fun t => Real.log (1 + gStar * τ t))
      (Set.Icc (0 : ℝ) 1) :=
    (continuousOn_const.add (continuousOn_const.mul hτcont)).log
      (fun t ht => (hargg_pos t ht).ne')
  have hlogf_deriv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      τ t ≤ transition_value fStar gStar →
      HasDerivAt (fun u => Real.log (1 + fStar * τ u)) Z⁻¹ t := by
    intro t ht hle
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have hτderiv_at := hτderiv t ht
    rw [hbranch_le t htIcc hle] at hτderiv_at
    have harg_deriv_raw : HasDerivAt (fun u => 1 + fStar * τ u)
        (fStar * (Z⁻¹ * (fStar / (1 + τ t * fStar))⁻¹)) t :=
      (hτderiv_at.const_mul fStar).const_add 1
    have harg_deriv : HasDerivAt (fun u => 1 + fStar * τ u)
        (Z⁻¹ * (1 + fStar * τ t)) t := by
      convert harg_deriv_raw using 1
      field_simp [hfne, (harg_pos t htIcc).ne', mul_comm]
    have hlog := harg_deriv.log (harg_pos t htIcc).ne'
    convert hlog using 1
    field_simp [(harg_pos t htIcc).ne']
  have hlogg_deriv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      transition_value fStar gStar ≤ τ t →
      HasDerivAt (fun u => Real.log (1 + gStar * τ u)) (-Z⁻¹) t := by
    intro t ht hge
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have hτderiv_at := hτderiv t ht
    rw [hbranch_ge t htIcc hge] at hτderiv_at
    have harg_deriv_raw : HasDerivAt (fun u => 1 + gStar * τ u)
        (gStar * (Z⁻¹ * (-gStar / (1 + τ t * gStar))⁻¹)) t :=
      (hτderiv_at.const_mul gStar).const_add 1
    have harg_deriv : HasDerivAt (fun u => 1 + gStar * τ u)
        (-Z⁻¹ * (1 + gStar * τ t)) t := by
      convert harg_deriv_raw using 1
      field_simp [hgne, (hargg_pos t htIcc).ne', mul_comm]
    have hlog := harg_deriv.log (hargg_pos t htIcc).ne'
    convert hlog using 1
    field_simp [(hargg_pos t htIcc).ne']
  have hlogf_eq : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ≤ a →
      Real.log (1 + fStar * τ t) = Z⁻¹ * t := by
    intro t ht hta
    by_cases htzero : t = 0
    · subst t; simp [hτzero]
    · have hzero_lt_t : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htzero)
      obtain ⟨c, hc, hslope⟩ :=
        exists_hasDerivAt_eq_slope
          (fun u => Real.log (1 + fStar * τ u))
          (fun _ => Z⁻¹) hzero_lt_t
          (hlogf_cont.mono (by intro u hu; exact ⟨hu.1, hu.2.trans ht.2⟩))
          (by
            intro u hu
            have huIcc : u ∈ Set.Icc (0 : ℝ) 1 :=
              ⟨hu.1.le, (lt_of_lt_of_le hu.2 ht.2).le⟩
            have hule_a : u ≤ a := le_trans hu.2.le hta
            have hτle : τ u ≤ transition_value fStar gStar := by
              rw [← haτ]; exact hτmono huIcc haIcc hule_a
            exact hlogf_deriv u ⟨hu.1, lt_of_lt_of_le hu.2 ht.2⟩ hτle)
      simp [hτzero] at hslope
      exact (div_eq_iff hzero_lt_t.ne').mp hslope.symm
  have hlogg_eq : ∀ t ∈ Set.Icc (0 : ℝ) 1, a ≤ t →
      Real.log (1 + gStar * τ t) = Real.log (1 + gStar) + Z⁻¹ * (1 - t) := by
    intro t ht hat
    by_cases htone : t = 1
    · subst t; simp [hτone]
    · have ht_lt_one : t < 1 := lt_of_le_of_ne ht.2 htone
      obtain ⟨c, hc, hslope⟩ :=
        exists_hasDerivAt_eq_slope
          (fun u => Real.log (1 + gStar * τ u))
          (fun _ => -Z⁻¹) ht_lt_one
          (hlogg_cont.mono (by intro u hu; exact ⟨ht.1.trans hu.1, hu.2⟩))
          (by
            intro u hu
            have huIcc : u ∈ Set.Icc (0 : ℝ) 1 :=
              ⟨(lt_of_le_of_lt ht.1 hu.1).le, hu.2.le⟩
            have hau : a ≤ u := le_trans hat hu.1.le
            have hτge : transition_value fStar gStar ≤ τ u := by
              rw [← haτ]; exact hτmono haIcc huIcc hau
            exact hlogg_deriv u ⟨lt_of_le_of_lt ht.1 hu.1, hu.2⟩ hτge)
      rw [hτone, mul_one] at hslope
      have hh := (eq_div_iff (sub_pos.mpr ht_lt_one).ne').mp hslope
      linear_combination hh
  have hfx0 : 1 + fStar * transition_value fStar gStar = Hc := by
    rw [hHcdef]; unfold transition_value; field_simp [hfne, hgne]; ring
  have hgx0 : 1 + gStar * transition_value fStar gStar = (gStar + 1) / Rc := by
    rw [hRcdef]; unfold transition_value
    field_simp [hfne, hgne, hgplus.ne', h1mgf.ne']; ring
  have hlogHc : Real.log Hc = Z⁻¹ * a := by
    have h := hlogf_eq a haIcc (le_refl a)
    rw [haτ, hfx0] at h; exact h
  have hLg_a :
      Real.log ((gStar + 1) / Rc) = Real.log (1 + gStar) + Z⁻¹ * (1 - a) := by
    have h := hlogg_eq a haIcc (le_refl a)
    rw [haτ, hgx0] at h; exact h
  have hlogRc : Real.log Rc = -(Z⁻¹ * (1 - a)) := by
    rw [Real.log_div hgplus.ne' hRpos.ne', add_comm gStar 1] at hLg_a
    linarith [hLg_a]
  have hCloglog : Real.log Cc = Real.log Hc - Real.log Rc := by
    rw [hCHR, Real.log_div hHpos.ne' hRpos.ne']
  have hlogC_eq : Real.log Cc = Z⁻¹ := by
    rw [hCloglog, hlogHc, hlogRc]; ring
  have ha_eq : transition_time fStar gStar = a := by
    rw [ht0form, hlogHc, hlogC_eq, mul_comm, mul_div_assoc,
      div_self (inv_ne_zero hZ.ne'), mul_one]
  unfold has_transition_formula
  refine ⟨?_, ?_⟩
  · rw [ha_eq]; exact haτ
  · intro t ht
    refine ⟨fun htle => ?_, fun htge => ?_⟩
    · rw [ha_eq] at htle
      have harg_eqL : 1 + fStar * τ t = Cc ^ t := by
        have hlogt : Real.log (1 + fStar * τ t) = Real.log Cc * t := by
          rw [hlogf_eq t ht htle, hlogC_eq]
        rw [← Real.exp_log (harg_pos t ht),
          ← Real.exp_log (Real.rpow_pos_of_pos hCpos t), Real.log_rpow hCpos,
          hlogt, mul_comm]
      have hfinalL : τ t = (Cc ^ t - 1) / fStar := by
        rw [eq_div_iff hfne]; linear_combination harg_eqL
      rw [hfinalL]; unfold transition_left_formula
      rw [← hCcdef]; field_simp [hfne]
    · rw [ha_eq] at htge
      have hlog := hlogg_eq t ht htge
      have harg_eqR : 1 + gStar * τ t = (gStar + 1) * Cc ^ (1 - t) := by
        rw [← Real.exp_log (hargg_pos t ht),
          ← Real.exp_log
            (mul_pos hgplus (Real.rpow_pos_of_pos hCpos (1 - t)))]
        congr 1
        rw [Real.log_mul hgplus.ne' (Real.rpow_pos_of_pos hCpos _).ne',
          Real.log_rpow hCpos, hlog, hlogC_eq, add_comm gStar 1]
        ring
      have hCrpow : Cc ^ (1 - t) = Hc ^ (1 - t) / Rc ^ (1 - t) := by
        rw [hCHR, Real.div_rpow hHpos.le hRpos.le]
      have hR_rel : (gStar + 1) / Rc = (1 / 2 : ℝ) * (1 - gStar / fStar) := by
        rw [hRcdef]; field_simp [hfne, hgplus.ne', h1mgf.ne']
      have hkey : (gStar + 1) * Cc ^ (1 - t) =
          (1 / 2 : ℝ) * (1 - gStar / fStar) * Rc ^ t * Hc ^ (1 - t) := by
        rw [hCrpow, Real.rpow_sub hRpos 1 t, Real.rpow_one, ← hR_rel]
        field_simp [hRpos.ne', (Real.rpow_pos_of_pos hRpos t).ne']
      have hcomb : 1 + gStar * τ t =
          (1 / 2 : ℝ) * (1 - gStar / fStar) * Rc ^ t * Hc ^ (1 - t) := by
        rw [harg_eqR, hkey]
      have hfinalR : τ t =
          ((1 / 2 : ℝ) * (1 - gStar / fStar) * Rc ^ t * Hc ^ (1 - t) - 1)
            / gStar := by
        rw [eq_div_iff hgne]; linear_combination hcomb
      rw [hfinalR]; unfold transition_right_formula
      rw [← hRcdef, ← hHcdef]; field_simp [hgne, hfne]

@[blueprint "lem:expanding-transition-time-mem-icc"
  (statement := /-- Let $A,B\in\mathbb{R}$ satisfy $A>0$, $0<B<1$, and $B\leq A$. If $A-B\leq 2AB$, then the transition time defined by \cref{def:transition-time} for the pair $(A,-B)$ belongs to $[0,1]$. -/)
  (proof := /-- Rewrite the numerator as $\log((A+B)/(2B))$ and compare the denominator with it. The numerator is nonnegative because $B\leq A$. The denominator is positive because its logarithmic argument is at least $1$, whereas $1-B<1$. Finally, $A-B\leq2AB$ is equivalent to
  \[
    \frac{A+B}{2B}(1-B)\leq \frac{(A+B)^2}{4AB},
  \]
  so monotonicity and additivity of the logarithm show that the numerator does not exceed the denominator. Division by the positive denominator places the transition time in $[0,1]$. -/)
  (title := /-- An interior crossover gives an interior transition time -/)
  (latexEnv := "lemma")]
lemma expanding_transition_time_mem_icc
    {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hB1 : B < 1) (hBA : B ≤ A)
    (hcross : A - B ≤ 2 * A * B) :
    transition_time A (-B) ∈ Set.Icc (0 : ℝ) 1 := by
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hB0 : B ≠ 0 := ne_of_gt hB
  have h_one_sub_B : 0 < 1 - B := by linarith
  have hp : 0 < (1 / 2 : ℝ) * (1 + A / B) := by positivity
  have hp_one : 1 ≤ (1 / 2 : ℝ) * (1 + A / B) := by
    rw [show (1 / 2 : ℝ) * (1 + A / B) = (A + B) / (2 * B) by
      field_simp
      <;> ring]
    rw [le_div_iff₀ (mul_pos (by positivity) hB)]
    nlinarith
  have hq : 0 < (1 / 4 : ℝ) * (2 + A / B + B / A) := by positivity
  have hq_one : 1 ≤ (1 / 4 : ℝ) * (2 + A / B + B / A) := by
    rw [show 2 + A / B + B / A = (2 * A * B + A ^ 2 + B ^ 2) / (A * B) by
      field_simp
      <;> ring]
    rw [show (1 / 4 : ℝ) * ((2 * A * B + A ^ 2 + B ^ 2) / (A * B)) =
        (2 * A * B + A ^ 2 + B ^ 2) / (4 * A * B) by ring]
    rw [le_div_iff₀ (mul_pos (mul_pos (by positivity) hA) hB)]
    nlinarith [sq_nonneg (A - B)]
  have hnum : 0 ≤ Real.log ((1 / 2 : ℝ) * (1 + A / B)) :=
    Real.log_nonneg hp_one
  have hden :
      0 < Real.log ((1 / 4 : ℝ) * (2 + A / B + B / A)) -
        Real.log (1 - B) := by
    have hlt : 1 - B < (1 / 4 : ℝ) * (2 + A / B + B / A) :=
      lt_of_lt_of_le (by linarith) hq_one
    have := (Real.log_lt_log_iff h_one_sub_B hq).2 hlt
    linarith
  have hprod :
      (1 / 2 : ℝ) * (1 + A / B) * (1 - B) ≤
        (1 / 4 : ℝ) * (2 + A / B + B / A) := by
    rw [show (1 / 2 : ℝ) * (1 + A / B) = (A + B) / (2 * B) by
      field_simp
      <;> ring]
    rw [show (1 / 4 : ℝ) * (2 + A / B + B / A) =
        (A + B) ^ 2 / (4 * A * B) by
      field_simp
      <;> ring]
    rw [show (A + B) / (2 * B) * (1 - B) =
        ((A + B) * (1 - B)) / (2 * B) by ring]
    rw [div_le_div_iff₀ (mul_pos (by positivity) hB)
      (mul_pos (mul_pos (by positivity) hA) hB)]
    have hc : 0 ≤ 2 * A * B - (A - B) := by linarith
    have hm : 0 ≤ (2 * B * (A + B)) * (2 * A * B - (A - B)) :=
      mul_nonneg (by positivity) hc
    nlinarith
  have hnum_le_den :
      Real.log ((1 / 2 : ℝ) * (1 + A / B)) ≤
        Real.log ((1 / 4 : ℝ) * (2 + A / B + B / A)) -
          Real.log (1 - B) := by
    have hlog := (Real.log_le_log_iff (mul_pos hp h_one_sub_B) hq).2 hprod
    rw [Real.log_mul hp.ne' h_one_sub_B.ne'] at hlog
    linarith
  have hquot :
      Real.log ((1 / 2 : ℝ) * (1 + A / B)) /
          (Real.log ((1 / 4 : ℝ) * (2 + A / B + B / A)) -
            Real.log (1 - B)) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hnum hden.le, (div_le_one hden).2 hnum_le_den⟩
  simpa [transition_time, div_neg, neg_div, sub_eq_add_neg, add_assoc,
    add_comm, add_left_comm] using hquot

@[blueprint "lem:expanding-l-inf-speed"
  (statement := /-- Let $E$ be a real normed vector space, let $\Omega\subseteq E$, let $f,g:E\to\mathbb{R}$, and let $f^*,g_*\in\mathbb{R}$ satisfy the scalar transport conditions of \cref{def:scalar-transport-conditions}. Suppose that it is not the case that the transition time of \cref{def:transition-time} is both defined in the sense of \cref{def:transition-time-defined} and contained in $[0,1]$, and suppose that $-g_*\leq f^*$. Then $f^*>0$ and, for every $x\in[0,1]$, the supremal speed of \cref{def:l-inf-speed} is
  \[
    M(x)=\frac{f^*}{1+xf^*}.
  \] -/)
  (proof := /-- Unpack \cref{def:scalar-transport-conditions}. Compactness and continuity give points at which $f$ and $g$ attain their extrema. By \cref{def:domain-supremum,def:domain-infimum}, these values are respectively $f^*$ and $g_*$, and hence
  [
    g_*\leq g(s)\leq f(s)\leq f^*
  ]
  for every $s\in\Omega$. Together with $-g_*\leq f^*$, these inequalities imply $f^*\geq0$; equality would force both $f$ and $g$ to vanish throughout $\Omega$, contrary to the nonisometry clause. Thus $f^*>0$.

  Suppose that $g_*<0$. The arithmetic--geometric mean identity gives
  [
    1\leq \frac14\left(2-\frac{f^*}{g_*}-\frac{g_*}{f^*}\right).
  ]
  Since $0<g_*+1<1$, strict monotonicity of the logarithm shows that the logarithmic denominator in \cref{def:transition-time-defined} is positive. If
  [
    f^*-(-g_*)\leq2f^*(-g_*),
  ]
  then \cref{lem:expanding-transition-time-mem-icc} places this defined transition time in $[0,1]$, contradicting the hypothesis. Consequently the displayed inequality is strict in the opposite direction.

  Fix $x\in[0,1]$. For every $y\in[g_*,f^*]$, one has $1+xy>0$. If $y\geq0$, cross multiplication gives
  [
    \frac{y}{1+xy}\leq\frac{f^*}{1+xf^*}.
  ]
  If $y<0$, cross multiplication first bounds its absolute ratio by the ratio at $g_*$, and the strict endpoint separation above then bounds that ratio by the ratio at $f^*$. Thus every value in each image defining the two suprema in \cref{def:l-inf-speed} is at most $f^*/(1+xf^*)$. The point attaining $f^*$ belongs to the first image and realizes this bound, so its supremum equals the bound; the second supremum is no larger. Taking their maximum proves the stated formula. -/)
  (title := /-- Supremal speed in the expanding regime -/)
  (latexEnv := "lemma")]
lemma expanding_l_inf_speed
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set E) (f g : E → ℝ) (fStar gStar : ℝ)
    (hdata : scalar_transport_conditions Ω f g fStar gStar)
    (ht₀ : ¬ (transition_time_defined fStar gStar ∧
      transition_time fStar gStar ∈ Set.Icc (0 : ℝ) 1))
    (hdom : -gStar ≤ fStar) :
    0 < fStar ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        l_inf_speed Ω f g x = fStar / (1 + x * fStar) := by
  rcases hdata with
    ⟨hΩne, hΩcomp, _, hfcont, hgcont, hgf, hfStar, hgStar, hgneg, hnonzero⟩
  obtain ⟨sf, hsf, hsfmax⟩ := hΩcomp.exists_isMaxOn hΩne hfcont
  obtain ⟨sg, hsg, hsgmin⟩ := hΩcomp.exists_isMinOn hΩne hgcont
  have hfgreatest : IsGreatest (f '' Ω) (f sf) :=
    ⟨⟨sf, hsf, rfl⟩, by
      rintro _ ⟨s, hs, rfl⟩
      exact hsfmax hs⟩
  have hgleast : IsLeast (g '' Ω) (g sg) :=
    ⟨⟨sg, hsg, rfl⟩, by
      rintro _ ⟨s, hs, rfl⟩
      exact hsgmin hs⟩
  have hfsf : f sf = fStar := by
    rw [hfStar, domain_supremum]
    exact hfgreatest.csSup_eq.symm
  have hgsg : g sg = gStar := by
    rw [hgStar, domain_infimum]
    exact hgleast.csInf_eq.symm
  have hf_le (s : E) (hs : s ∈ Ω) : f s ≤ fStar := by
    rw [← hfsf]
    exact hsfmax hs
  have hg_le (s : E) (hs : s ∈ Ω) : gStar ≤ g s := by
    rw [← hgsg]
    exact hsgmin hs
  have hgfStar : gStar ≤ fStar := by
    calc
      gStar ≤ g sf := hg_le sf hsf
      _ ≤ f sf := hgf sf hsf
      _ = fStar := hfsf
  have hfnonneg : 0 ≤ fStar := by
    nlinarith
  have hfpos : 0 < fStar := by
    rcases hfnonneg.lt_or_eq with hfpos | hfzero
    · exact hfpos
    · have hgzero : gStar = 0 := by
        nlinarith
      exfalso
      rcases hnonzero with ⟨s, hs, hfs | hgs⟩
      · apply hfs
        have hlow : 0 ≤ f s := by
          calc
            0 = gStar := hgzero.symm
            _ ≤ g s := hg_le s hs
            _ ≤ f s := hgf s hs
        have hupp : f s ≤ 0 := by
          simpa [hfzero] using hf_le s hs
        linarith
      · apply hgs
        have hlow : 0 ≤ g s := by
          simpa [hgzero] using hg_le s hs
        have hupp : g s ≤ 0 := by
          calc
            g s ≤ f s := hgf s hs
            _ ≤ fStar := hf_le s hs
            _ = 0 := hfzero.symm
        linarith
  have hseparation (hglt : gStar < 0) :
      2 * fStar * (-gStar) < fStar - (-gStar) := by
    have hgplus : 0 < gStar + 1 := by linarith
    have hqone :
        1 ≤ (1 / 4 : ℝ) *
          (2 - fStar / gStar - gStar / fStar) := by
      rw [show (1 / 4 : ℝ) *
          (2 - fStar / gStar - gStar / fStar) =
          (fStar - gStar) ^ 2 / (4 * fStar * (-gStar)) by
        field_simp [hfpos.ne', hglt.ne]
        <;> ring]
      rw [le_div_iff₀
        (mul_pos (mul_pos (by norm_num) hfpos) (neg_pos.mpr hglt))]
      nlinarith [sq_nonneg (fStar + gStar)]
    have hqpos :
        0 < (1 / 4 : ℝ) *
          (2 - fStar / gStar - gStar / fStar) :=
      lt_of_lt_of_le zero_lt_one hqone
    have hden :
        0 < Real.log ((1 / 4 : ℝ) *
              (2 - fStar / gStar - gStar / fStar)) -
            Real.log (gStar + 1) := by
      have hlt :
          gStar + 1 <
            (1 / 4 : ℝ) *
              (2 - fStar / gStar - gStar / fStar) :=
        lt_of_lt_of_le (by linarith) hqone
      have hlog := (Real.log_lt_log_iff hgplus hqpos).2 hlt
      linarith
    have hdefined : transition_time_defined fStar gStar :=
      ⟨hglt, hfpos, hden.ne'⟩
    by_contra hnot
    have hcross :
        fStar - (-gStar) ≤ 2 * fStar * (-gStar) :=
      le_of_not_gt hnot
    apply ht₀
    refine ⟨hdefined, ?_⟩
    simpa only [neg_neg] using
      (expanding_transition_time_mem_icc hfpos (neg_pos.mpr hglt)
        (by linarith) hdom hcross)
  refine ⟨hfpos, ?_⟩
  intro x hx
  have hden_pos (y : ℝ) (hy : gStar ≤ y) : 0 < 1 + x * y := by
    have hynegone : -1 < y := lt_of_lt_of_le hgneg hy
    by_cases hyzero : 0 ≤ y
    · nlinarith [mul_nonneg hx.1 hyzero]
    · have hprod :
          0 ≤ (1 - x) * (-y) :=
        mul_nonneg (sub_nonneg.mpr hx.2) (by linarith)
      nlinarith
  have hfden : 0 < 1 + x * fStar := hden_pos fStar hgfStar
  have hratio_le (y : ℝ) (hgy : gStar ≤ y) (hyf : y ≤ fStar) :
      |y / (1 + x * y)| ≤ fStar / (1 + x * fStar) := by
    have hyden : 0 < 1 + x * y := hden_pos y hgy
    by_cases hyzero : 0 ≤ y
    · rw [abs_of_nonneg (div_nonneg hyzero hyden.le)]
      rw [div_le_div_iff₀ hyden hfden]
      nlinarith
    · have hylt : y < 0 := lt_of_not_ge hyzero
      have hglt : gStar < 0 := lt_of_le_of_lt hgy hylt
      have hgden : 0 < 1 + x * gStar := hden_pos gStar le_rfl
      have hnegative_endpoint :
          (-y) / (1 + x * y) ≤
            (-gStar) / (1 + x * gStar) := by
        rw [div_le_div_iff₀ hyden hgden]
        nlinarith
      have hsep := hseparation hglt
      have hxprod :
          0 ≤ (1 - x) * (-2 * fStar * gStar) :=
        mul_nonneg (sub_nonneg.mpr hx.2) (by
          have hfgneg : fStar * gStar < 0 :=
            mul_neg_of_pos_of_neg hfpos hglt
          nlinarith)
      have hendpoint :
          (-gStar) / (1 + x * gStar) ≤
            fStar / (1 + x * fStar) := by
        rw [div_le_div_iff₀ hgden hfden]
        nlinarith
      rw [abs_of_neg (div_neg_of_neg_of_pos hylt hyden)]
      simpa only [neg_div] using hnegative_endpoint.trans hendpoint
  have hfrange_nonempty :
      ((fun s => |f s / (1 + x * f s)|) '' Ω).Nonempty :=
    hΩne.image _
  have hfrange_upper :
      ∀ z ∈ (fun s => |f s / (1 + x * f s)|) '' Ω,
        z ≤ fStar / (1 + x * fStar) := by
    rintro _ ⟨s, hs, rfl⟩
    exact hratio_le (f s)
      (hg_le s hs |>.trans (hgf s hs)) (hf_le s hs)
  have hfrange_bdd :
      BddAbove ((fun s => |f s / (1 + x * f s)|) '' Ω) :=
    ⟨fStar / (1 + x * fStar), hfrange_upper⟩
  have hfat :
      |f sf / (1 + x * f sf)| =
        fStar / (1 + x * fStar) := by
    rw [hfsf, abs_of_pos (div_pos hfpos hfden)]
  have hfsup :
      sSup ((fun s => |f s / (1 + x * f s)|) '' Ω) =
        fStar / (1 + x * fStar) := by
    apply le_antisymm
    · exact csSup_le hfrange_nonempty hfrange_upper
    · rw [← hfat]
      exact le_csSup hfrange_bdd ⟨sf, hsf, rfl⟩
  have hgrange_nonempty :
      ((fun s => |g s / (1 + x * g s)|) '' Ω).Nonempty :=
    hΩne.image _
  have hgrange_upper :
      ∀ z ∈ (fun s => |g s / (1 + x * g s)|) '' Ω,
        z ≤ fStar / (1 + x * fStar) := by
    rintro _ ⟨s, hs, rfl⟩
    exact hratio_le (g s) (hg_le s hs) ((hgf s hs).trans (hf_le s hs))
  have hgsup :
      sSup ((fun s => |g s / (1 + x * g s)|) '' Ω) ≤
        fStar / (1 + x * fStar) :=
    csSup_le hgrange_nonempty hgrange_upper
  unfold l_inf_speed
  rw [hfsup]
  exact max_eq_left hgsup

@[blueprint "lem:expanding-regime-formula"
  (statement := /-- Let $E$ be a real normed vector space. Let $\Omega\subseteq E$, let $f,g:E\to\mathbb{R}$, and let $f^*,g_*\in\mathbb{R}$ satisfy the scalar transport conditions of \cref{def:scalar-transport-conditions}. Let $\tau:\mathbb{R}\to\mathbb{R}$ solve the normalized $L^\infty$ schedule ODE of \cref{def:solves-l-inf-ode}. Define $t_0$ from $f^*$ and $g_*$ by \cref{def:transition-time}. Suppose that it is not the case that $t_0$ is both defined in the sense of \cref{def:transition-time-defined} and contained in $[0,1]$. If $-g_*\leq f^*$, then, for every $t\in[0,1]$,
  \[
    \tau(t)=\frac{(f^*+1)^t-1}{f^*}.
  \]
  Equivalently, $\tau$ satisfies \cref{def:has-expanding-formula}. -/)
  (proof := /-- By \cref{lem:expanding-l-inf-speed}, one has $f^*>0$ and
  \[
    M(x)=\frac{f^*}{1+xf^*}
  \]
  for every $x\in[0,1]$. Unpack \cref{def:solves-l-inf-ode}, and let $Z>0$ be the normalizing constant. Since \cref{def:is-unit-schedule} maps $[0,1]$ into itself, the differential equation gives
  \[
    \dot\tau(t)=Z^{-1}\frac{1+f^*\tau(t)}{f^*}
    \qquad(0<t<1).
  \]
  The quantity $1+f^*\tau(t)$ is positive. The chain rule therefore shows that
  \[
    \frac{d}{dt}\log(1+f^*\tau(t))=Z^{-1}.
  \]
  This logarithmic composite is continuous on $[0,1]$. For each $t\in(0,1]$, the mean-value theorem on $[0,t]$, using the displayed derivative on $(0,t)$ and $\tau(0)=0$, yields
  \[
    \log(1+f^*\tau(t))=t/Z
  \]
  and the same identity holds at $t=0$. Evaluating at $t=1$ and using $\tau(1)=1$ gives $Z^{-1}=\log(1+f^*)$. Exponentiation and division by the nonzero number $f^*$ now give
  \[
    \tau(t)=\frac{(1+f^*)^t-1}{f^*},
  \]
  which is precisely \cref{def:has-expanding-formula}. -/)
  (title := /-- Formula in the expanding no-transition regime -/)
  (latexEnv := "lemma")]
lemma expanding_regime_formula
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set E) (f g : E → ℝ) (fStar gStar : ℝ) (τ : ℝ → ℝ)
    (hdata : scalar_transport_conditions Ω f g fStar gStar)
    (hode : solves_l_inf_ode Ω f g τ)
    (ht₀ : ¬ (transition_time_defined fStar gStar ∧
      transition_time fStar gStar ∈ Set.Icc (0 : ℝ) 1))
    (hdom : -gStar ≤ fStar) :
    has_expanding_formula τ fStar := by
  obtain ⟨hfstar_pos, hspeed⟩ :=
    expanding_l_inf_speed Ω f g fStar gStar hdata ht₀ hdom
  rcases hode with ⟨hschedule, Z, hZ, hτderiv⟩
  rcases hschedule with ⟨hτdiff, _, hτmaps, hτzero, hτone⟩
  have harg_pos : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      0 < 1 + fStar * τ t := by
    intro t ht
    have hτmem := hτmaps ht
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg hfstar_pos.le hτmem.1)
  have harg_cont : ContinuousOn (fun t => 1 + fStar * τ t)
      (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.add (continuousOn_const.mul hτdiff.continuousOn)
  have hlog_cont : ContinuousOn (fun t => Real.log (1 + fStar * τ t))
      (Set.Icc (0 : ℝ) 1) :=
    harg_cont.log (fun t ht => (harg_pos t ht).ne')
  have hlog_deriv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun u => Real.log (1 + fStar * τ u)) Z⁻¹ t := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have hτmem := hτmaps htIcc
    have hτderiv_at := hτderiv t ht
    rw [hspeed (τ t) hτmem] at hτderiv_at
    have harg_deriv_raw : HasDerivAt (fun u => 1 + fStar * τ u)
        (fStar * (Z⁻¹ * (fStar / (1 + τ t * fStar))⁻¹)) t := by
      exact (hτderiv_at.const_mul fStar).const_add 1
    have harg_deriv : HasDerivAt (fun u => 1 + fStar * τ u)
        (Z⁻¹ * (1 + fStar * τ t)) t := by
      convert harg_deriv_raw using 1
      field_simp [hfstar_pos.ne', (harg_pos t htIcc).ne', mul_comm]
      <;> ring
    have hlog := harg_deriv.log (harg_pos t htIcc).ne'
    convert hlog using 1
    field_simp [hfstar_pos.ne', (harg_pos t htIcc).ne']
  have hlog_eq : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.log (1 + fStar * τ t) = Z⁻¹ * t := by
    intro t ht
    by_cases htzero : t = 0
    · subst t
      simp [hτzero]
    · have hzero_lt_t : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htzero)
      obtain ⟨c, hc, hslope⟩ :=
        exists_hasDerivAt_eq_slope
          (fun u => Real.log (1 + fStar * τ u))
          (fun _ => Z⁻¹) hzero_lt_t
          (hlog_cont.mono (by
            intro u hu
            exact ⟨hu.1, hu.2.trans ht.2⟩))
          (by
            intro u hu
            exact hlog_deriv u ⟨hu.1, lt_of_lt_of_le hu.2 ht.2⟩)
      simp [hτzero] at hslope
      exact (div_eq_iff hzero_lt_t.ne').mp hslope.symm
  have hnormalization : Real.log (1 + fStar) = Z⁻¹ := by
    have := hlog_eq 1 ⟨zero_le_one, le_rfl⟩
    simpa [hτone] using this
  unfold has_expanding_formula
  intro t ht
  have hlog_power :
      Real.log (1 + fStar * τ t) = t * Real.log (1 + fStar) := by
    rw [hlog_eq t ht, hnormalization]
    ring
  have hbase_pos : 0 < fStar + 1 := by linarith
  have harg_eq_power : 1 + fStar * τ t = (fStar + 1) ^ t := by
    calc
      1 + fStar * τ t = Real.exp (Real.log (1 + fStar * τ t)) :=
        (Real.exp_log (harg_pos t ht)).symm
      _ = Real.exp (Real.log (fStar + 1) * t) := by
        rw [hlog_power]
        congr 1
        ring_nf
      _ = (fStar + 1) ^ t := by
        rw [Real.rpow_def_of_pos hbase_pos]
  unfold expanding_formula
  apply (eq_div_iff hfstar_pos.ne').2
  nlinarith

@[blueprint "lem:contracting-l-inf-speed"
  (statement := /-- Let $E$ be a real normed vector space. Let $\Omega\subseteq E$, let $f,g:E\to\mathbb{R}$, and let $f^*,g_*\in\mathbb{R}$ satisfy the scalar transport conditions of \cref{def:scalar-transport-conditions}. If $f^*<-g_*$, then $g_*<0$ and, for every $x\in[0,1]$, the supremal speed of \cref{def:l-inf-speed} is
  \[
    M(x)=\frac{-g_*}{1+xg_*}.
  \] -/)
  (proof := /-- Compactness and continuity give points where $f$ attains $f^*$ and $g$ attains $g_*$. Hence
  \[
    g_*\leq g(s)\leq f(s)\leq f^*
  \]
  on $\Omega$. Nonemptiness and $f^*<-g_*$ imply $g_*<0$, while the scalar transport conditions give $-1<g_*$. Thus every denominator $1+xy$ is positive for $x\in[0,1]$ and $g_*\leq y\leq f^*$. If $y\leq0$, cross multiplication shows
  \[
    \frac{|y|}{1+xy}\leq\frac{-g_*}{1+xg_*}
  \]
  from $g_*\leq y$. If $0\leq y$, the same inequality follows from $y\leq f^*<-g_*$ and $xyg_*\leq0$. Applying these bounds to both images in \cref{def:l-inf-speed} gives the upper bound, and the point where $g=g_*$ gives equality. -/)
  (title := /-- Supremal speed in the contracting regime -/)
  (latexEnv := "lemma")]
lemma contracting_l_inf_speed
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set E) (f g : E → ℝ) (fStar gStar : ℝ)
    (hdata : scalar_transport_conditions Ω f g fStar gStar)
    (hdom : fStar < -gStar) :
    gStar < 0 ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        l_inf_speed Ω f g x = (-gStar) / (1 + x * gStar) := by
  rcases hdata with
    ⟨hΩne, hΩcompact, _, hfcont, hgcont, horder, hfstar, hgstar,
      hgstar_bound, _⟩
  obtain ⟨smax, hsmax, hsmax_ge⟩ :=
    hΩcompact.exists_isMaxOn hΩne hfcont
  obtain ⟨smin, hsmin, hsmin_le⟩ :=
    hΩcompact.exists_isMinOn hΩne hgcont
  have hfstar_eq : fStar = f smax := by
    rw [hfstar]
    unfold domain_supremum
    exact (show IsGreatest (f '' Ω) (f smax) from
      ⟨⟨smax, hsmax, rfl⟩, by
        rintro y ⟨s, hs, rfl⟩
        exact hsmax_ge hs⟩).csSup_eq
  have hgstar_eq : gStar = g smin := by
    rw [hgstar]
    unfold domain_infimum
    exact (show IsLeast (g '' Ω) (g smin) from
      ⟨⟨smin, hsmin, rfl⟩, by
        rintro y ⟨s, hs, rfl⟩
        exact hsmin_le hs⟩).csInf_eq
  have hg_le : ∀ s ∈ Ω, gStar ≤ g s := by
    intro s hs
    rw [hgstar_eq]
    exact hsmin_le hs
  have hf_le : ∀ s ∈ Ω, f s ≤ fStar := by
    intro s hs
    rw [hfstar_eq]
    exact hsmax_ge hs
  have hgstar_le_fstar : gStar ≤ fStar := by
    calc
      gStar ≤ g smax := hg_le smax hsmax
      _ ≤ f smax := horder smax hsmax
      _ = fStar := hfstar_eq.symm
  have hgstar_neg : gStar < 0 := by
    linarith
  refine ⟨hgstar_neg, ?_⟩
  intro x hx
  have hden (y : ℝ) (hy : gStar ≤ y) : 0 < 1 + x * y := by
    by_cases hy0 : 0 ≤ y
    · nlinarith [mul_nonneg hx.1 hy0]
    · have hxy : y ≤ x * y := by
        simpa using mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hy0)
      linarith
  have hden_star : 0 < 1 + x * gStar := hden gStar le_rfl
  have hbound (y : ℝ) (hgy : gStar ≤ y) (hyf : y ≤ fStar) :
      |y / (1 + x * y)| ≤ (-gStar) / (1 + x * gStar) := by
    rw [abs_div, abs_of_pos (hden y hgy)]
    by_cases hy0 : 0 ≤ y
    · rw [abs_of_nonneg hy0]
      rw [div_le_div_iff₀ (hden y hgy) hden_star]
      have hxyg : x * y * gStar ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hx.1 hy0) hgstar_neg.le
      nlinarith
    · rw [abs_of_nonpos (le_of_not_ge hy0)]
      rw [div_le_div_iff₀ (hden y hgy) hden_star]
      nlinarith
  have hf_sup_le :
      sSup ((fun s => |f s / (1 + x * f s)|) '' Ω) ≤
        (-gStar) / (1 + x * gStar) := by
    refine csSup_le (hΩne.image _) ?_
    rintro y ⟨s, hs, rfl⟩
    exact hbound (f s) ((hg_le s hs).trans (horder s hs)) (hf_le s hs)
  have hg_sup_le :
      sSup ((fun s => |g s / (1 + x * g s)|) '' Ω) ≤
        (-gStar) / (1 + x * gStar) := by
    refine csSup_le (hΩne.image _) ?_
    rintro y ⟨s, hs, rfl⟩
    exact hbound (g s) (hg_le s hs) ((horder s hs).trans (hf_le s hs))
  have hg_bdd :
      BddAbove ((fun s => |g s / (1 + x * g s)|) '' Ω) := by
    refine ⟨(-gStar) / (1 + x * gStar), ?_⟩
    rintro y ⟨s, hs, rfl⟩
    exact hbound (g s) (hg_le s hs) ((horder s hs).trans (hf_le s hs))
  have hg_lower :
      (-gStar) / (1 + x * gStar) ≤
        sSup ((fun s => |g s / (1 + x * g s)|) '' Ω) := by
    have hmem : |g smin / (1 + x * g smin)| ∈
        (fun s => |g s / (1 + x * g s)|) '' Ω :=
      ⟨smin, hsmin, rfl⟩
    have hle := le_csSup hg_bdd hmem
    rw [← hgstar_eq, abs_div, abs_of_neg hgstar_neg,
      abs_of_pos hden_star] at hle
    exact hle
  unfold l_inf_speed
  apply le_antisymm
  · exact max_le hf_sup_le hg_sup_le
  · exact hg_lower.trans (le_max_right _ _)

@[blueprint "lem:contracting-regime-formula"
  (statement := /-- Let $E$ be a real normed vector space. Let $\Omega\subseteq E$, let $f,g:E\to\mathbb{R}$, and let $f^*,g_*\in\mathbb{R}$ satisfy the scalar transport conditions of \cref{def:scalar-transport-conditions}. Let $\tau:\mathbb{R}\to\mathbb{R}$ solve the normalized $L^\infty$ schedule ODE of \cref{def:solves-l-inf-ode}. Suppose that it is not the case that the transition time is both defined in the sense of \cref{def:transition-time-defined} and contained in $[0,1]$. If $f^*<-g_*$, then $\tau$ satisfies the contracting formula of \cref{def:has-contracting-formula}. -/)
  (proof := /-- The scalar transport conditions in \cref{def:scalar-transport-conditions} give $-1<g_*$. By \cref{lem:contracting-l-inf-speed}, one also has $g_*<0$ and
  \[
    M(x)=\frac{-g_*}{1+xg_*}
  \]
  for every $x\in[0,1]$. Unpack \cref{def:solves-l-inf-ode}, and let $Z>0$ be its normalizing constant. By the range condition in \cref{def:is-unit-schedule}, $0\leq\tau(t)\leq1$ on $[0,1]$, so $1+g_*\tau(t)>0$. For $0<t<1$, substituting the displayed identity into the differential equation gives

  \[
    \dot\tau(t)=Z^{-1}\frac{1+g_*\tau(t)}{-g_*}
  \]
  and the chain rule therefore gives
  \[
    \frac{d}{dt}\log(1+g_*\tau(t))=-Z^{-1}.
  \]
  The schedule is continuous on $[0,1]$, as is the logarithmic composite because its argument is positive. For each $t\in(0,1]$, the mean-value theorem on $[0,t]$, together with $\tau(0)=0$, yields
  \[
    \log(1+g_*\tau(t))=-Z^{-1}t.
  \]
  The same identity holds at $t=0$. Evaluating it at $t=1$ and using $\tau(1)=1$ gives $-Z^{-1}=\log(1+g_*)$. Hence
  \[
    \log(1+g_*\tau(t))=t\log(1+g_*)
  \]
  for every $t\in[0,1]$. Since $1+g_*>0$, exponentiation identifies the right-hand side with the real power $(1+g_*)^t$. Finally, $g_*\neq0$, so rearranging gives
  \[
    \tau(t)=\frac{(1+g_*)^t-1}{g_*}
  \]
  for every $t\in[0,1]$, exactly as required by \cref{def:has-contracting-formula}. -/)
  (title := /-- Formula in the contracting no-transition regime -/)
  (latexEnv := "lemma")]
lemma contracting_regime_formula
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set E) (f g : E → ℝ) (fStar gStar : ℝ) (τ : ℝ → ℝ)
    (hdata : scalar_transport_conditions Ω f g fStar gStar)
    (hode : solves_l_inf_ode Ω f g τ)
    (ht₀ : ¬ (transition_time_defined fStar gStar ∧
      transition_time fStar gStar ∈ Set.Icc (0 : ℝ) 1))
    (hdom : fStar < -gStar) :
    has_contracting_formula τ gStar := by
  obtain ⟨hgstar_neg, hspeed⟩ :=
    contracting_l_inf_speed Ω f g fStar gStar hdata hdom
  rcases hdata with
    ⟨_, _, _, _, _, _, _, _, hgstar_bound, _⟩
  rcases hode with ⟨hschedule, Z, hZ, hτderiv⟩
  rcases hschedule with ⟨hτdiff, _, hτmaps, hτzero, hτone⟩
  have harg_pos : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      0 < 1 + gStar * τ t := by
    intro t ht
    have hτmem := hτmaps ht
    have hprod : gStar ≤ τ t * gStar := by
      simpa using mul_le_mul_of_nonpos_right hτmem.2 hgstar_neg.le
    nlinarith
  have harg_cont : ContinuousOn (fun t => 1 + gStar * τ t)
      (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.add (continuousOn_const.mul hτdiff.continuousOn)
  have hlog_cont : ContinuousOn (fun t => Real.log (1 + gStar * τ t))
      (Set.Icc (0 : ℝ) 1) :=
    harg_cont.log (fun t ht => (harg_pos t ht).ne')
  have hlog_deriv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun u => Real.log (1 + gStar * τ u)) (-Z⁻¹) t := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have hτmem := hτmaps htIcc
    have hτderiv_at := hτderiv t ht
    rw [hspeed (τ t) hτmem] at hτderiv_at
    have harg_deriv_raw : HasDerivAt (fun u => 1 + gStar * τ u)
        (gStar * (Z⁻¹ * (-gStar / (1 + τ t * gStar))⁻¹)) t := by
      exact (hτderiv_at.const_mul gStar).const_add 1
    have harg_deriv : HasDerivAt (fun u => 1 + gStar * τ u)
        (-Z⁻¹ * (1 + gStar * τ t)) t := by
      convert harg_deriv_raw using 1
      field_simp [hgstar_neg.ne, (harg_pos t htIcc).ne', mul_comm]
      <;> ring
    have hlog := harg_deriv.log (harg_pos t htIcc).ne'
    convert hlog using 1
    field_simp [hgstar_neg.ne', (harg_pos t htIcc).ne']
  have hlog_eq : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.log (1 + gStar * τ t) = (-Z⁻¹) * t := by
    intro t ht
    by_cases htzero : t = 0
    · subst t
      simp [hτzero]
    · have hzero_lt_t : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htzero)
      obtain ⟨c, hc, hslope⟩ :=
        exists_hasDerivAt_eq_slope
          (fun u => Real.log (1 + gStar * τ u))
          (fun _ => -Z⁻¹) hzero_lt_t
          (hlog_cont.mono (by
            intro u hu
            exact ⟨hu.1, hu.2.trans ht.2⟩))
          (by
            intro u hu
            exact hlog_deriv u ⟨hu.1, lt_of_lt_of_le hu.2 ht.2⟩)
      simp [hτzero] at hslope
      exact (div_eq_iff hzero_lt_t.ne').mp hslope.symm
  have hnormalization : Real.log (1 + gStar) = -Z⁻¹ := by
    have := hlog_eq 1 ⟨zero_le_one, le_rfl⟩
    simpa [hτone] using this
  unfold has_contracting_formula
  intro t ht
  have hlog_power :
      Real.log (1 + gStar * τ t) = t * Real.log (1 + gStar) := by
    rw [hlog_eq t ht, hnormalization]
    ring
  have hbase_pos : 0 < gStar + 1 := by linarith
  have harg_eq_power : 1 + gStar * τ t = (gStar + 1) ^ t := by
    calc
      1 + gStar * τ t = Real.exp (Real.log (1 + gStar * τ t)) :=
        (Real.exp_log (harg_pos t ht)).symm
      _ = Real.exp (Real.log (gStar + 1) * t) := by
        rw [hlog_power]
        congr 1
        ring_nf
      _ = (gStar + 1) ^ t := by
        rw [Real.rpow_def_of_pos hbase_pos]
  unfold contracting_formula
  apply (eq_div_iff hgstar_neg.ne).2
  nlinarith

@[blueprint "lem:transport-to-scalar-conditions"
  (statement := /-- Let $d\geq1$, let $E=\mathbb{R}^{d}$, and suppose that $\Omega$, $T$, $\mu$, $\nu$, the orthonormal eigenbasis $e_i(s)$, and the eigenvalues $\sigma_i(s)$ satisfy the transport conditions of \cref{def:transport-conditions}. Define
  \[
    f(s)=\max_{1\leq i\leq d}\sigma_i(s)-1,
    \qquad
    g(s)=\min_{1\leq i\leq d}\sigma_i(s)-1,
  \]
  as in \cref{def:transport-upper-deviation, def:transport-lower-deviation}, and set
  \[
    f^*=\sup_{s\in\Omega}f(s),
    \qquad
    g_*=\inf_{s\in\Omega}g(s).
  \]
  Then $\Omega,f,g,f^*,g_*$ satisfy the scalar transport conditions of \cref{def:scalar-transport-conditions}. -/)
  (proof := /-- Unpack \cref{def:transport-conditions}. The probability measure $\mu$ gives positive mass to $\Omega$, because it is supported there, and absolute continuity of $\mu$ then implies that $\Omega$ has positive Lebesgue measure. A proper affine subspace has Lebesgue measure zero; hence the affine span of $\Omega$ is the whole Euclidean space. Convexity consequently makes $\Omega$ a set of unique differentiability, so the $C^1$ hypothesis makes $s\mapsto D T(s)$ continuous on $\Omega$ in operator norm.

  Expand an arbitrary vector in the orthonormal eigenbasis at $s$. The resulting Rayleigh identity expresses $\langle D T(s)x,x\rangle$ as the sum of $\sigma_i(s)$ times the squared basis coefficients. It bounds this quantity between the smallest and largest $\sigma_i(s)$ times $\lVert x\rVert^2$. Applying these bounds to a unit eigenvector realizing an extremum shows that the change in either extremal eigenvalue between $s$ and $t$ is bounded by $\lVert D T(s)-D T(t)\rVert$. Thus the functions in \cref{def:transport-upper-deviation, def:transport-lower-deviation} are continuous on $\Omega$.

  The finite minimum is at most the finite maximum, so $g\leq f$. Compactness makes the continuous function $g$ attain its domain infimum. At its minimizer, positivity of every eigenvalue gives $g>-1$, and therefore $-1<g_*$. The nonisometry clause supplies $s$ and $i$ with $\sigma_i(s)\neq1$: according as $\sigma_i(s)\leq1$ or $1<\sigma_i(s)$, respectively the minimum or maximum deviation is nonzero. The two extremal identities are reflexive instances of \cref{def:domain-supremum, def:domain-infimum}. Together with nonemptiness, compactness, and convexity, these are exactly the clauses of \cref{def:scalar-transport-conditions}. -/)
  (title := /-- Scalar consequences of the transport hypotheses -/)
  (latexEnv := "lemma")]
lemma transport_to_scalar_conditions
    {d : ℕ} [NeZero d]
    (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (μ ν : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))
    (eigenbasis :
      EuclideanSpace ℝ (Fin d) →
        OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (σ : EuclideanSpace ℝ (Fin d) → Fin d → ℝ)
    (htransport :
      transport_conditions Ω T μ ν eigenbasis σ) :
    scalar_transport_conditions Ω
      (transport_upper_deviation σ)
      (transport_lower_deviation σ)
      (domain_supremum Ω (transport_upper_deviation σ))
      (domain_infimum Ω (transport_lower_deviation σ)) := by
  unfold transport_conditions at htransport
  rcases htransport with
    ⟨hΩne, hΩcompact, hΩconvex, hT, heigen, hpos, hμprob, hνprob,
      hμac, hνac, hμsupport, hνsupport, hmap, hnoniso⟩
  letI := hμprob
  have hμΩ : μ Ω ≠ 0 := by
    intro hz
    have hsum := MeasureTheory.measure_add_measure_compl (μ := μ) hΩcompact.measurableSet
    simpa [hz, hμsupport] using hsum
  have hvolΩ : MeasureTheory.volume Ω ≠ 0 := fun hz => hμΩ (hμac hz)
  have haff : affineSpan ℝ Ω = ⊤ := by
    by_contra hne
    apply hvolΩ
    exact MeasureTheory.measure_mono_null (subset_affineSpan ℝ Ω)
      (MeasureTheory.Measure.addHaar_affineSubspace MeasureTheory.volume (affineSpan ℝ Ω) hne)
  have hvec : vectorSpan ℝ Ω = ⊤ := by
    rw [← direction_affineSpan, haff]
    simp
  have hunique : UniqueDiffOn ℝ Ω := by
    intro x hx
    refine ⟨?_, subset_closure hx⟩
    have htanspan : Submodule.span ℝ (tangentConeAt ℝ Ω x) = ⊤ := by
      apply top_unique
      rw [← hvec, vectorSpan_eq_span_vsub_set_right (k := ℝ) hx]
      apply Submodule.span_mono
      rintro v ⟨y, hy, rfl⟩
      exact mem_tangentConeAt_of_segment_subset (hΩconvex.segment_subset hx hy)
    rw [htanspan]
    exact dense_univ
  have hAcont : ContinuousOn (fderivWithin ℝ T Ω) Ω :=
    hT.continuousOn_fderivWithin hunique (by norm_num)
  have hdiag (s : EuclideanSpace ℝ (Fin d)) (hs : s ∈ Ω)
      (x : EuclideanSpace ℝ (Fin d)) :
      inner ℝ (fderivWithin ℝ T Ω s x) x =
        ∑ i : Fin d, σ s i * (inner ℝ (eigenbasis s i) x) ^ 2 := by
    nth_rw 1 [← (eigenbasis s).sum_repr' x]
    simp_rw [map_sum, map_smul, heigen s hs, sum_inner, real_inner_smul_left]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hupper (s : EuclideanSpace ℝ (Fin d)) (hs : s ∈ Ω)
      (x : EuclideanSpace ℝ (Fin d)) :
      inner ℝ (fderivWithin ℝ T Ω s x) x ≤
        Finset.univ.sup' Finset.univ_nonempty (σ s) * ‖x‖ ^ 2 := by
    rw [hdiag s hs x, ← (eigenbasis s).sum_sq_inner_right x, Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_right (Finset.le_sup' (σ s) hi) (sq_nonneg _)
  have hlower (s : EuclideanSpace ℝ (Fin d)) (hs : s ∈ Ω)
      (x : EuclideanSpace ℝ (Fin d)) :
      Finset.univ.inf' Finset.univ_nonempty (σ s) * ‖x‖ ^ 2 ≤
        inner ℝ (fderivWithin ℝ T Ω s x) x := by
    rw [hdiag s hs x, ← (eigenbasis s).sum_sq_inner_right x, Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_right (Finset.inf'_le (σ s) hi) (sq_nonneg _)
  have hmaxpert (s t : EuclideanSpace ℝ (Fin d)) (hs : s ∈ Ω) (ht : t ∈ Ω) :
      Finset.univ.sup' Finset.univ_nonempty (σ s) -
        Finset.univ.sup' Finset.univ_nonempty (σ t) ≤
        ‖fderivWithin ℝ T Ω s - fderivWithin ℝ T Ω t‖ := by
    obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (σ s)
    have hvnorm : ‖eigenbasis s i‖ = 1 := (eigenbasis s).norm_eq_one i
    have hvnormsq : ‖eigenbasis s i‖ ^ 2 = 1 := by rw [hvnorm]; norm_num
    have hAs :
        inner ℝ (fderivWithin ℝ T Ω s (eigenbasis s i)) (eigenbasis s i) =
          Finset.univ.sup' Finset.univ_nonempty (σ s) := by
      rw [heigen s hs i, real_inner_smul_left, hmax]
      simp
    have hBt := hupper t ht (eigenbasis s i)
    have hop :
        inner ℝ ((fderivWithin ℝ T Ω s - fderivWithin ℝ T Ω t)
          (eigenbasis s i)) (eigenbasis s i) ≤
          ‖fderivWithin ℝ T Ω s - fderivWithin ℝ T Ω t‖ := by
      calc
        _ ≤ ‖(fderivWithin ℝ T Ω s - fderivWithin ℝ T Ω t)
            (eigenbasis s i)‖ * ‖eigenbasis s i‖ := real_inner_le_norm _ _
        _ ≤ _ := by
          rw [hvnorm, mul_one]
          simpa using
            (fderivWithin ℝ T Ω s - fderivWithin ℝ T Ω t).le_opNorm (eigenbasis s i)
    have hdiff :
        inner ℝ ((fderivWithin ℝ T Ω s - fderivWithin ℝ T Ω t)
          (eigenbasis s i)) (eigenbasis s i) =
          inner ℝ (fderivWithin ℝ T Ω s (eigenbasis s i)) (eigenbasis s i) -
            inner ℝ (fderivWithin ℝ T Ω t (eigenbasis s i)) (eigenbasis s i) := by
      rw [ContinuousLinearMap.sub_apply, inner_sub_left]
    rw [hdiff, hAs] at hop
    rw [hvnormsq] at hBt
    linarith
  have hminpert (s t : EuclideanSpace ℝ (Fin d)) (hs : s ∈ Ω) (ht : t ∈ Ω) :
      Finset.univ.inf' Finset.univ_nonempty (σ t) -
        Finset.univ.inf' Finset.univ_nonempty (σ s) ≤
        ‖fderivWithin ℝ T Ω s - fderivWithin ℝ T Ω t‖ := by
    obtain ⟨i, hi, hmin⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (σ s)
    have hvnorm : ‖eigenbasis s i‖ = 1 := (eigenbasis s).norm_eq_one i
    have hvnormsq : ‖eigenbasis s i‖ ^ 2 = 1 := by rw [hvnorm]; norm_num
    have hAs :
        inner ℝ (fderivWithin ℝ T Ω s (eigenbasis s i)) (eigenbasis s i) =
          Finset.univ.inf' Finset.univ_nonempty (σ s) := by
      rw [heigen s hs i, real_inner_smul_left, hmin]
      simp
    have hBt := hlower t ht (eigenbasis s i)
    have hop :
        -‖fderivWithin ℝ T Ω s - fderivWithin ℝ T Ω t‖ ≤
          inner ℝ ((fderivWithin ℝ T Ω s - fderivWithin ℝ T Ω t)
            (eigenbasis s i)) (eigenbasis s i) := by
      calc
        _ ≤ -|inner ℝ ((fderivWithin ℝ T Ω s - fderivWithin ℝ T Ω t)
              (eigenbasis s i)) (eigenbasis s i)| := by
          rw [neg_le_neg_iff]
          calc
            _ ≤ ‖(fderivWithin ℝ T Ω s - fderivWithin ℝ T Ω t)
                (eigenbasis s i)‖ := by
              simpa [hvnorm] using
                (abs_real_inner_le_norm
                  ((fderivWithin ℝ T Ω s - fderivWithin ℝ T Ω t)
                    (eigenbasis s i)) (eigenbasis s i))
            _ ≤ _ := by
              simpa [hvnorm] using
                (fderivWithin ℝ T Ω s - fderivWithin ℝ T Ω t).le_opNorm
                  (eigenbasis s i)
        _ ≤ _ := neg_abs_le _
    have hdiff :
        inner ℝ ((fderivWithin ℝ T Ω s - fderivWithin ℝ T Ω t)
          (eigenbasis s i)) (eigenbasis s i) =
          inner ℝ (fderivWithin ℝ T Ω s (eigenbasis s i)) (eigenbasis s i) -
            inner ℝ (fderivWithin ℝ T Ω t (eigenbasis s i)) (eigenbasis s i) := by
      rw [ContinuousLinearMap.sub_apply, inner_sub_left]
    rw [hdiff, hAs] at hop
    rw [hvnormsq] at hBt
    linarith
  have hmaxcont :
      ContinuousOn (fun s => Finset.univ.sup' Finset.univ_nonempty (σ s)) Ω := by
    intro s hs
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hAδ⟩ :=
      (Metric.continuousWithinAt_iff.mp (hAcont s hs)) ε hε
    refine ⟨δ, hδ, ?_⟩
    intro t ht hdist
    rw [Real.dist_eq]
    apply abs_lt.2
    have hnorm :
        ‖fderivWithin ℝ T Ω t - fderivWithin ℝ T Ω s‖ < ε := by
      simpa [dist_eq_norm] using hAδ ht hdist
    constructor
    · have h := hmaxpert s t hs ht
      rw [norm_sub_rev] at h
      linarith
    · exact lt_of_le_of_lt (hmaxpert t s ht hs) hnorm
  have hmincont :
      ContinuousOn (fun s => Finset.univ.inf' Finset.univ_nonempty (σ s)) Ω := by
    intro s hs
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hAδ⟩ :=
      (Metric.continuousWithinAt_iff.mp (hAcont s hs)) ε hε
    refine ⟨δ, hδ, ?_⟩
    intro t ht hdist
    rw [Real.dist_eq]
    apply abs_lt.2
    have hnorm :
        ‖fderivWithin ℝ T Ω t - fderivWithin ℝ T Ω s‖ < ε := by
      simpa [dist_eq_norm] using hAδ ht hdist
    constructor
    · have h := hminpert t s ht hs
      linarith
    · have h := hminpert s t hs ht
      rw [norm_sub_rev] at h
      exact lt_of_le_of_lt h hnorm
  have hfcont : ContinuousOn (transport_upper_deviation σ) Ω := by
    exact hmaxcont.sub continuousOn_const
  have hgcont : ContinuousOn (transport_lower_deviation σ) Ω := by
    exact hmincont.sub continuousOn_const
  have horder : ∀ s ∈ Ω, transport_lower_deviation σ s ≤
      transport_upper_deviation σ s := by
    intro s hs
    unfold transport_lower_deviation transport_upper_deviation
    obtain ⟨i, hi⟩ := Finset.univ_nonempty
    exact sub_le_sub_right
      ((Finset.inf'_le (σ s) hi).trans (Finset.le_sup' (σ s) hi)) 1
  have hminpos : ∀ s ∈ Ω, 0 < Finset.univ.inf' Finset.univ_nonempty (σ s) := by
    intro s hs
    obtain ⟨i, hi, hmin⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (σ s)
    rw [hmin]
    exact hpos s hs i
  obtain ⟨smin, hsmin, hsmin_le⟩ :=
    hΩcompact.exists_isMinOn hΩne hgcont
  have hgstar :
      domain_infimum Ω (transport_lower_deviation σ) =
        transport_lower_deviation σ smin := by
    unfold domain_infimum
    exact (show IsLeast (transport_lower_deviation σ '' Ω)
      (transport_lower_deviation σ smin) from
        ⟨⟨smin, hsmin, rfl⟩, by
          rintro y ⟨s, hs, rfl⟩
          exact hsmin_le hs⟩).csInf_eq
  have hgstar_bound :
      -1 < domain_infimum Ω (transport_lower_deviation σ) := by
    rw [hgstar]
    unfold transport_lower_deviation
    linarith [hminpos smin hsmin]
  have hnonzero :
      ∃ s ∈ Ω, transport_upper_deviation σ s ≠ 0 ∨
        transport_lower_deviation σ s ≠ 0 := by
    obtain ⟨s, hs, i, hi⟩ := hnoniso
    refine ⟨s, hs, ?_⟩
    by_cases hle : σ s i ≤ 1
    · right
      unfold transport_lower_deviation
      have hleinf := Finset.inf'_le (σ s) (Finset.mem_univ i)
      intro hz
      have hinf : Finset.univ.inf' Finset.univ_nonempty (σ s) = 1 := by linarith
      exact hi (le_antisymm hle (by linarith [hpos s hs i, hleinf]))
    · left
      unfold transport_upper_deviation
      have hlesup := Finset.le_sup' (σ s) (Finset.mem_univ i)
      intro hz
      linarith
  unfold scalar_transport_conditions
  exact
    ⟨hΩne, hΩcompact, hΩconvex, hfcont, hgcont, horder, rfl, rfl,
      hgstar_bound, hnonzero⟩

@[blueprint "thm:solution-of-l-inf-ode"
  (statement := /-- Let $d\geq1$, put $E=\mathbb{R}^{d}$, and let $\Omega\subseteq E$. Let $T:E\to E$, let $\mu$ and $\nu$ be Borel probability measures, and let $e_i(s)$ and $\sigma_i(s)$, for $1\leq i\leq d$, be a complete orthonormal eigenbasis and the corresponding eigenvalues of $D T(s)$. Assume the regularity, positive-definiteness, absolute-continuity, pushforward, and nonisometry hypotheses of \cref{def:transport-conditions}. Define
  \[
    f(s)=\max_{1\leq i\leq d}\sigma_i(s)-1,
    \qquad
    g(s)=\min_{1\leq i\leq d}\sigma_i(s)-1,
  \]
  by \cref{def:transport-upper-deviation, def:transport-lower-deviation}, and put $f^*=\sup_{s\in\Omega}f(s)$ and $g_*=\inf_{s\in\Omega}g(s)$. Let $\tau$ solve the normalized $L^\infty$ schedule ODE of \cref{def:solves-l-inf-ode} for these functions. If the transition time $t_0$ is defined in the sense of \cref{def:transition-time-defined} and belongs to $[0,1]$, then $\tau$ satisfies the transition value and both displayed branches in \cref{def:has-transition-formula}. Otherwise, if $f^*\geq-g_*$, then $\tau$ satisfies the formula in \cref{def:has-expanding-formula}; if $f^*<-g_*$, then $\tau$ satisfies the formula in \cref{def:has-contracting-formula}. -/)
  (proof := /-- By \cref{lem:transport-to-scalar-conditions}, the functions obtained from the Jacobian eigenvalues satisfy exactly the scalar hypotheses required by the three regime lemmas. If the transition time is defined in the sense of \cref{def:transition-time-defined} and belongs to $[0,1]$, apply \cref{lem:transition-regime-formula}. Otherwise, if $-g_*\leq f^*$, apply \cref{lem:expanding-regime-formula}; if this inequality fails, then $f^*<-g_*$ and \cref{lem:contracting-regime-formula} applies. These cases are exhaustive. -/)
  (title := /-- Solution of the normalized $L^\infty$ schedule ODE -/)
  (latexEnv := "theorem")]
theorem solution_of_l_inf_ode
    {d : ℕ} [NeZero d]
    (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (μ ν : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))
    (eigenbasis :
      EuclideanSpace ℝ (Fin d) →
        OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (σ : EuclideanSpace ℝ (Fin d) → Fin d → ℝ)
    (τ : ℝ → ℝ)
    (htransport :
      transport_conditions Ω T μ ν eigenbasis σ)
    (hode :
      solves_l_inf_ode Ω
        (transport_upper_deviation σ)
        (transport_lower_deviation σ) τ) :
    (let f := transport_upper_deviation σ
      let g := transport_lower_deviation σ
      let fStar := domain_supremum Ω f
      let gStar := domain_infimum Ω g
      let t₀ := transition_time fStar gStar
      if transition_time_defined fStar gStar ∧
          t₀ ∈ Set.Icc (0 : ℝ) 1 then
        has_transition_formula τ fStar gStar
      else if -gStar ≤ fStar then
        has_expanding_formula τ fStar
      else
        has_contracting_formula τ gStar) := by
  intro f g fStar gStar t₀
  have hdata := transport_to_scalar_conditions Ω T μ ν eigenbasis σ htransport
  by_cases hdef : transition_time_defined fStar gStar ∧ t₀ ∈ Set.Icc (0 : ℝ) 1
  · rw [if_pos hdef]
    exact transition_regime_formula Ω _ _ _ _ τ hdata hode hdef.1 hdef.2
  · rw [if_neg hdef]
    by_cases hdom : -gStar ≤ fStar
    · rw [if_pos hdom]
      exact expanding_regime_formula Ω _ _ _ _ τ hdata hode hdef hdom
    · rw [if_neg hdom]
      exact contracting_regime_formula Ω _ _ _ _ τ hdata hode hdef (not_le.mp hdom)

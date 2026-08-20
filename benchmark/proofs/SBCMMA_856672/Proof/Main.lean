import Architect
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.EMetricSpace.Lipschitz

set_option linter.all false
set_option maxHeartbeats 500000

open scoped ContDiff

@[blueprint "def:chebyshev-first"
  (statement := /-- For \(n\in\mathbb N\) and \(x\in\mathbb R\), define
  \(T_n(x)\) to be the evaluation at \(x\) of Mathlib's \(n\)-th Chebyshev
  polynomial of the first kind. -/)
  (title := /-- Chebyshev Polynomial of the First Kind -/)
  (latexEnv := "definition")]
noncomputable def chebyshev_first (n : ℕ) (x : ℝ) : ℝ :=
  (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x

@[blueprint "def:normalized-chebyshev-first"
  (statement := /-- For \(n\in\mathbb N\), define the normalized first-kind
  Chebyshev function by
  \[
    \mathcal T_n(x)=
    \begin{cases}
      T_0(x)/\sqrt{\pi},&n=0,\\
      T_n(x)/\sqrt{\pi/2},&n\geq 1.
    \end{cases}
  \]
  Thus the normalization agrees with the norms for the Chebyshev weight
  \((1-x^2)^{-1/2}\) on \([-1,1]\). -/)
  (title := /-- Normalized Chebyshev Function -/)
  (latexEnv := "definition")]
noncomputable def normalized_chebyshev_first (n : ℕ) (x : ℝ) : ℝ :=
  if n = 0 then
    chebyshev_first n x / Real.sqrt Real.pi
  else
    chebyshev_first n x / Real.sqrt (Real.pi / 2)

@[blueprint "def:chebyshev-moment"
  (statement := /-- Let \(p\) be a probability measure on \(\mathbb R\).
  Its \(n\)-th Chebyshev moment is
  \[
    m_n(p)=\int_{\mathbb R}T_n(x)\,dp(x).
  \] -/)
  (title := /-- Chebyshev Moment -/)
  (latexEnv := "definition")]
noncomputable def chebyshev_moment
    (p : MeasureTheory.ProbabilityMeasure ℝ) (n : ℕ) : ℝ :=
  ∫ x, chebyshev_first n x ∂(p : MeasureTheory.Measure ℝ)

@[blueprint "def:normalized-chebyshev-moment"
  (statement := /-- Let \(p\) be a probability measure on \(\mathbb R\).
  Its \(n\)-th normalized Chebyshev moment is
  \[
    \widetilde m_n(p)=\int_{\mathbb R}\mathcal T_n(x)\,dp(x).
  \] -/)
  (title := /-- Normalized Chebyshev Moment -/)
  (latexEnv := "definition")]
noncomputable def normalized_chebyshev_moment
    (p : MeasureTheory.ProbabilityMeasure ℝ) (n : ℕ) : ℝ :=
  ∫ x, normalized_chebyshev_first n x
    ∂(p : MeasureTheory.Measure ℝ)

@[blueprint "def:weighted-moment-discrepancy-sq"
  (statement := /-- For probability measures \(p,q\) and \(k\in\mathbb N\),
  define the squared weighted discrepancy of their first \(k\) Chebyshev
  moments by
  \[
    D_k(p,q)^2=\sum_{j=1}^{k}
      \frac{(m_j(p)-m_j(q))^2}{j^2}.
  \] -/)
  (title := /-- Squared Weighted Chebyshev-Moment Discrepancy -/)
  (latexEnv := "definition")]
noncomputable def weighted_moment_discrepancy_sq
    (p q : MeasureTheory.ProbabilityMeasure ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 k,
    (chebyshev_moment p j - chebyshev_moment q j) ^ 2 / (j : ℝ) ^ 2

@[blueprint "def:chebyshev-coefficient"
  (statement := /-- For a function \(f:\mathbb R\to\mathbb R\) and
  \(j\in\mathbb N\), define its normalized Chebyshev coefficient by
  \[
    c_j(f)=\int_{-1}^{1} f(x)\mathcal T_j(x)
      \frac{dx}{\sqrt{1-x^2}},
  \]
  where the integral is expressed using Mathlib's first-kind Chebyshev
  measure. -/)
  (title := /-- Normalized Chebyshev Coefficient -/)
  (latexEnv := "definition")]
noncomputable def chebyshev_coefficient (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  ∫ x, f x * normalized_chebyshev_first j x
    ∂Polynomial.Chebyshev.measureT

@[blueprint "def:damped-chebyshev-approximation"
  (statement := /-- Given \(f:\mathbb R\to\mathbb R\), a degree
  \(k\in\mathbb N\), and damping factors \(b:\mathbb N\to\mathbb R\), define
  \[
    J_{k,b}f(x)=\sum_{j=0}^{k}b_jc_j(f)\mathcal T_j(x).
  \] -/)
  (title := /-- Damped Chebyshev Approximation -/)
  (latexEnv := "definition")]
noncomputable def damped_chebyshev_approximation
    (f : ℝ → ℝ) (k : ℕ) (b : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    b j * chebyshev_coefficient f j * normalized_chebyshev_first j x

@[blueprint "def:is-coupling"
  (statement := /-- A measure \(\gamma\) on \(\mathbb R\times\mathbb R\) is
  a coupling of probability measures \(p\) and \(q\) if its first marginal
  is \(p\) and its second marginal is \(q\). -/)
  (title := /-- Coupling of Probability Measures -/)
  (latexEnv := "definition")]
def is_coupling
    (p q : MeasureTheory.ProbabilityMeasure ℝ)
    (γ : MeasureTheory.Measure (ℝ × ℝ)) : Prop :=
  γ.fst = (p : MeasureTheory.Measure ℝ) ∧
    γ.snd = (q : MeasureTheory.Measure ℝ)

@[blueprint "def:wasserstein-one"
  (statement := /-- For probability measures \(p,q\) on \(\mathbb R\),
  define their Wasserstein--\(1\) distance by
  \[
    W_1(p,q)=\inf_{\gamma\in\Pi(p,q)}
      \int_{\mathbb R^2}|x-y|\,d\gamma(x,y),
  \]
  where \(\Pi(p,q)\) is the set of couplings from
  \cref{def:is-coupling}. -/)
  (title := /-- Wasserstein--One Distance -/)
  (latexEnv := "definition")]
noncomputable def wasserstein_one
    (p q : MeasureTheory.ProbabilityMeasure ℝ) : ℝ :=
  sInf {c : ℝ | ∃ γ : MeasureTheory.Measure (ℝ × ℝ),
    is_coupling p q γ ∧ c = ∫ z, |z.1 - z.2| ∂γ}

@[blueprint "lem:kantorovich-rubinstein-lipschitz-duality"
  (statement := /-- Let \(p\) and \(q\) be probability measures on
  \(\mathbb R\) whose supports are contained in \([-1,1]\). Then
  \[
    W_1(p,q)=\sup_f\left(\int_{\mathbb R}f\,dp-
      \int_{\mathbb R}f\,dq\right),
  \]
  where the supremum ranges over all globally \(1\)-Lipschitz functions
  \(f:\mathbb R\to\mathbb R\). -/)
  (proof := /-- For a probability measure \(\mu\), put
  \(F_\mu(x)=\mu((-\infty,x])\) and, for \(0<u<1\), define
  \[
    Q_\mu(u)=\inf\{x\in\mathbb R:u\leq F_\mu(x)\}.
  \]
  The support hypothesis gives \(F_\mu(1)=1\), bounds the defining set
  below by \(-1\), and implies
  \[
    Q_\mu(u)\leq x\quad\Longleftrightarrow\quad u\leq F_\mu(x).
  \]
  For the nontrivial implication at \(x=Q_\mu(u)\), apply continuity from
  above to the decreasing intervals
  \((-\infty,Q_\mu(u)+1/(n+1)]\). Consequently \(Q_\mu\) is monotone on
  \((0,1)\), is measurable there, and pushes Lebesgue measure restricted
  to \((0,1)\) forward to \(\mu\).

  Let \(\lambda\) be Lebesgue measure on \((0,1)\), and push \(\lambda\)
  forward by \(u\mapsto(Q_p(u),Q_q(u))\). Its marginals are \(p\) and
  \(q\), so it is a coupling in the sense of \cref{def:is-coupling}.
  Set
  \[
    D(t)=F_p(t)-F_q(t),\qquad
    \sigma(t)=
    \begin{cases}
      -1,&D(t)<0,\\
      1,&D(t)>0,\\
      0,&D(t)=0,
    \end{cases}
    \qquad
    \varphi(x)=\int_x^1\sigma(t)\,dt.
  \]
  The function \(\sigma\) is measurable and bounded in absolute value by
  one, hence \(\varphi\) is globally \(1\)-Lipschitz. If
  \(Q_p(u)\leq Q_q(u)\), then
  \(F_p(t)\geq u>F_q(t)\) for almost every
  \(t\in(Q_p(u),Q_q(u)]\), and therefore \(\sigma(t)=1\) there. The
  reversed inequality similarly gives \(\sigma(t)=-1\) between the two
  quantiles. Thus, for every \(0<u<1\),
  \[
    \varphi(Q_p(u))-\varphi(Q_q(u))
      =|Q_p(u)-Q_q(u)|.
  \]
  Change of variables under the quantile pushforwards and integration of
  this identity show that the cost of the constructed coupling equals
  \(\int\varphi\,dp-\int\varphi\,dq\).

  Finally, let \(\gamma\) be any coupling and let \(f\) be globally
  \(1\)-Lipschitz. Compact support makes all relevant functions
  integrable, the marginal identities give
  \[
    \int f\,dp-\int f\,dq
      =\int\bigl(f(x)-f(y)\bigr)\,d\gamma(x,y)
      \leq\int|x-y|\,d\gamma(x,y).
  \]
  Hence the dual supremum is at most every coupling cost and therefore at
  most the infimum in \cref{def:wasserstein-one}. The constructed coupling
  and \(\varphi\) give the reverse inequality, proving equality. -/)
  (title := /-- Kantorovich--Rubinstein Duality on the Real Line -/)
  (latexEnv := "lemma")]
lemma kantorovich_rubinstein_lipschitz_duality
    (p q : MeasureTheory.ProbabilityMeasure ℝ)
    (hp : (p : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
    (hq : (q : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1) :
    wasserstein_one p q =
      sSup {a : ℝ | ∃ f : ℝ → ℝ,
        LipschitzWith 1 f ∧
          a = (∫ x, f x ∂(p : MeasureTheory.Measure ℝ)) -
            ∫ x, f x ∂(q : MeasureTheory.Measure ℝ)} := by
  classical
  have ae_mem_interval
      (μ : MeasureTheory.ProbabilityMeasure ℝ)
      (hμ : (μ : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1) :
      ∀ᵐ x ∂(μ : MeasureTheory.Measure ℝ), x ∈ Set.Icc (-1 : ℝ) 1 := by
    filter_upwards [(μ : MeasureTheory.Measure ℝ).support_mem_ae] with x hx
    exact hμ hx
  have measure_Iic_one
      (μ : MeasureTheory.ProbabilityMeasure ℝ)
      (hμ : (μ : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1) :
      (μ : MeasureTheory.Measure ℝ) (Set.Iic (1 : ℝ)) = 1 := by
    calc
      (μ : MeasureTheory.Measure ℝ) (Set.Iic (1 : ℝ)) =
          (μ : MeasureTheory.Measure ℝ) Set.univ := by
            apply MeasureTheory.measure_congr
            filter_upwards [ae_mem_interval μ hμ] with x hx
            apply propext
            constructor
            · intro _
              trivial
            · intro _
              exact hx.2
      _ = 1 := MeasureTheory.measure_univ
  have measure_Iic_eq_zero_of_lt
      (μ : MeasureTheory.ProbabilityMeasure ℝ)
      (hμ : (μ : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
      {x : ℝ} (hx : x < -1) :
      (μ : MeasureTheory.Measure ℝ) (Set.Iic x) = 0 := by
    calc
      (μ : MeasureTheory.Measure ℝ) (Set.Iic x) =
          (μ : MeasureTheory.Measure ℝ) ∅ := by
            apply MeasureTheory.measure_congr
            filter_upwards [ae_mem_interval μ hμ] with y hy
            apply propext
            constructor
            · intro hyx
              exact (not_le_of_gt hx) (hy.1.trans hyx)
            · intro hyempty
              exact False.elim hyempty
      _ = 0 := MeasureTheory.measure_empty
  let quantile (μ : MeasureTheory.ProbabilityMeasure ℝ) (u : ℝ) : ℝ :=
    sInf {x : ℝ | ENNReal.ofReal u ≤
      (μ : MeasureTheory.Measure ℝ) (Set.Iic x)}
  have quantile_set_nonempty
      (μ : MeasureTheory.ProbabilityMeasure ℝ)
      (hμ : (μ : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
      {u : ℝ} (hu : u < 1) :
      ({x : ℝ | ENNReal.ofReal u ≤
        (μ : MeasureTheory.Measure ℝ) (Set.Iic x)} : Set ℝ).Nonempty := by
    refine ⟨1, ?_⟩
    change ENNReal.ofReal u ≤
      (μ : MeasureTheory.Measure ℝ) (Set.Iic (1 : ℝ))
    rw [measure_Iic_one μ hμ]
    exact ENNReal.ofReal_le_one.mpr hu.le
  have quantile_set_bddBelow
      (μ : MeasureTheory.ProbabilityMeasure ℝ)
      (hμ : (μ : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
      {u : ℝ} (hu : 0 < u) :
      BddBelow {x : ℝ | ENNReal.ofReal u ≤
        (μ : MeasureTheory.Measure ℝ) (Set.Iic x)} := by
    refine ⟨-1, ?_⟩
    intro x hx
    change ENNReal.ofReal u ≤
      (μ : MeasureTheory.Measure ℝ) (Set.Iic x) at hx
    by_contra hbound
    have hxlt : x < -1 := lt_of_not_ge hbound
    rw [measure_Iic_eq_zero_of_lt μ hμ hxlt] at hx
    exact (not_le_of_gt (ENNReal.ofReal_pos.mpr hu)) hx
  have quantile_le_of_level_le
      (μ : MeasureTheory.ProbabilityMeasure ℝ)
      (hμ : (μ : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
      {u x : ℝ} (hu : 0 < u)
      (hux : ENNReal.ofReal u ≤
        (μ : MeasureTheory.Measure ℝ) (Set.Iic x)) :
      quantile μ u ≤ x := by
    exact csInf_le (quantile_set_bddBelow μ hμ hu) hux
  have le_quantile_of_level_lt
      (μ : MeasureTheory.ProbabilityMeasure ℝ)
      (hμ : (μ : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
      {u x : ℝ} (hu : u < 1)
      (hxu : (μ : MeasureTheory.Measure ℝ) (Set.Iic x) <
        ENNReal.ofReal u) :
      x ≤ quantile μ u := by
    apply le_csInf (quantile_set_nonempty μ hμ hu)
    intro y hy
    change ENNReal.ofReal u ≤
      (μ : MeasureTheory.Measure ℝ) (Set.Iic y) at hy
    by_contra hyx
    have hy_le_x : y ≤ x := le_of_not_ge hyx
    have hmono : (μ : MeasureTheory.Measure ℝ) (Set.Iic y) ≤
        (μ : MeasureTheory.Measure ℝ) (Set.Iic x) :=
      MeasureTheory.measure_mono (Set.Iic_subset_Iic.mpr hy_le_x)
    exact (not_lt_of_ge (hy.trans hmono)) hxu
  have level_le_measure_quantile
      (μ : MeasureTheory.ProbabilityMeasure ℝ)
      (hμ : (μ : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
      {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
      ENNReal.ofReal u ≤
        (μ : MeasureTheory.Measure ℝ) (Set.Iic (quantile μ u)) := by
    let A : ℕ → Set ℝ := fun n =>
      Set.Iic (quantile μ u + 1 / (n + 1 : ℝ))
    have hAanti : Antitone A := by
      intro n m hnm
      apply Set.Iic_subset_Iic.mpr
      gcongr
    have hInter : (⋂ n, A n) = Set.Iic (quantile μ u) := by
      ext x
      simp only [Set.mem_iInter]
      change (∀ n : ℕ, x ≤ quantile μ u + 1 / (n + 1 : ℝ)) ↔
        x ≤ quantile μ u
      constructor
      · intro hx
        by_contra hle
        have hlt : quantile μ u < x := lt_of_not_ge hle
        obtain ⟨n, hn⟩ :=
          exists_nat_one_div_lt (sub_pos.mpr hlt)
        have hxn := hx n
        linarith
      · intro hx n
        exact hx.trans (le_add_of_nonneg_right (by positivity))
    have hlevel : ∀ n, ENNReal.ofReal u ≤
        (μ : MeasureTheory.Measure ℝ) (A n) := by
      intro n
      have hpos : 0 < 1 / (n + 1 : ℝ) := by positivity
      have hq_lt : quantile μ u <
          quantile μ u + 1 / (n + 1 : ℝ) := lt_add_of_pos_right _ hpos
      obtain ⟨y, hy, hylt⟩ :=
        exists_lt_of_csInf_lt (quantile_set_nonempty μ hμ hu1) hq_lt
      change ENNReal.ofReal u ≤
        (μ : MeasureTheory.Measure ℝ) (Set.Iic y) at hy
      exact hy.trans (MeasureTheory.measure_mono
        (Set.Iic_subset_Iic.mpr hylt.le))
    have hmeasure : (μ : MeasureTheory.Measure ℝ) (⋂ n, A n) =
        ⨅ n, (μ : MeasureTheory.Measure ℝ) (A n) := by
      apply hAanti.measure_iInter
      · intro n
        exact (measurableSet_Iic.nullMeasurableSet)
      · exact ⟨0, MeasureTheory.measure_ne_top _ _⟩
    rw [← hInter, hmeasure]
    exact le_iInf hlevel
  have quantile_monotoneOn
      (μ : MeasureTheory.ProbabilityMeasure ℝ)
      (hμ : (μ : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1) :
      MonotoneOn (quantile μ) (Set.Ioo (0 : ℝ) 1) := by
    intro u hu v hv huv
    apply quantile_le_of_level_le μ hμ hu.1
    exact (ENNReal.ofReal_le_ofReal huv).trans
      (level_le_measure_quantile μ hμ hv.1 hv.2)
  have quantile_le_iff
      (μ : MeasureTheory.ProbabilityMeasure ℝ)
      (hμ : (μ : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
      {u x : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
      quantile μ u ≤ x ↔
        ENNReal.ofReal u ≤
          (μ : MeasureTheory.Measure ℝ) (Set.Iic x) := by
    constructor
    · intro hqx
      exact (level_le_measure_quantile μ hμ hu0 hu1).trans
        (MeasureTheory.measure_mono (Set.Iic_subset_Iic.mpr hqx))
    · exact quantile_le_of_level_le μ hμ hu0
  have quantile_aemeasurable
      (μ : MeasureTheory.ProbabilityMeasure ℝ)
      (hμ : (μ : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1) :
      AEMeasurable (quantile μ)
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    exact aemeasurable_restrict_of_monotoneOn measurableSet_Ioo
      (quantile_monotoneOn μ hμ)
  let uniformMeasure : MeasureTheory.Measure ℝ :=
    MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)
  letI : MeasureTheory.IsFiniteMeasure uniformMeasure := by
    constructor
    change (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) Set.univ <
      (⊤ : ENNReal)
    rw [MeasureTheory.Measure.restrict_apply' measurableSet_Ioo]
    simp
  have map_quantile
      (μ : MeasureTheory.ProbabilityMeasure ℝ)
      (hμ : (μ : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1) :
      MeasureTheory.Measure.map (quantile μ) uniformMeasure =
        (μ : MeasureTheory.Measure ℝ) := by
    apply MeasureTheory.Measure.ext_of_Iic
    intro x
    rw [MeasureTheory.Measure.map_apply_of_aemeasurable
      (quantile_aemeasurable μ hμ) measurableSet_Iic]
    change (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1))
        ((quantile μ) ⁻¹' Set.Iic x) =
      (μ : MeasureTheory.Measure ℝ) (Set.Iic x)
    rw [MeasureTheory.Measure.restrict_apply' measurableSet_Ioo]
    let M := (μ : MeasureTheory.Measure ℝ) (Set.Iic x)
    have hMtop : M ≠ (⊤ : ENNReal) := MeasureTheory.measure_ne_top _ _
    have hMle : M ≤ 1 := by
      dsimp [M]
      simpa only [MeasureTheory.measure_univ] using
        (MeasureTheory.measure_mono (Set.subset_univ (Set.Iic x)) :
          (μ : MeasureTheory.Measure ℝ) (Set.Iic x) ≤
            (μ : MeasureTheory.Measure ℝ) Set.univ)
    have hrle : M.toReal ≤ 1 := by
      rw [← ENNReal.toReal_one]
      exact ENNReal.toReal_mono ENNReal.one_ne_top hMle
    calc
      MeasureTheory.volume
          ((quantile μ ⁻¹' Set.Iic x) ∩ Set.Ioo (0 : ℝ) 1) =
          MeasureTheory.volume (Set.Ioc 0 M.toReal) := by
            apply MeasureTheory.measure_congr
            filter_upwards [MeasureTheory.volume.ae_ne (0 : ℝ),
              MeasureTheory.volume.ae_ne (1 : ℝ)] with u hu0ne hu1ne
            apply propext
            constructor
            · rintro ⟨hqx, hu0, hu1⟩
              refine ⟨hu0, ?_⟩
              exact (ENNReal.ofReal_le_iff_le_toReal hMtop).mp
                ((quantile_le_iff μ hμ hu0 hu1).mp hqx)
            · rintro ⟨hu0, hur⟩
              have hu_le_one : u ≤ 1 := hur.trans hrle
              have hu1 : u < 1 := lt_of_le_of_ne hu_le_one hu1ne
              refine ⟨(quantile_le_iff μ hμ hu0 hu1).mpr ?_, hu0, hu1⟩
              exact (ENNReal.ofReal_le_iff_le_toReal hMtop).mpr hur
      _ = M := by
            rw [Real.volume_Ioc]
            simp only [sub_zero, ENNReal.ofReal_toReal hMtop]
      _ = (μ : MeasureTheory.Measure ℝ) (Set.Iic x) := rfl
  let cdfDiff : ℝ → ℝ := fun x =>
    ((p : MeasureTheory.Measure ℝ) (Set.Iic x)).toReal -
      ((q : MeasureTheory.Measure ℝ) (Set.Iic x)).toReal
  let slope : ℝ → ℝ := fun x =>
    if cdfDiff x < 0 then -1 else if 0 < cdfDiff x then 1 else 0
  have cdfReal_monotone
      (μ : MeasureTheory.ProbabilityMeasure ℝ) :
      Monotone (fun x : ℝ =>
        ((μ : MeasureTheory.Measure ℝ) (Set.Iic x)).toReal) := by
    intro x y hxy
    exact ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _)
      (MeasureTheory.measure_mono (Set.Iic_subset_Iic.mpr hxy))
  have slope_measurable : Measurable slope := by
    have hdiff : Measurable cdfDiff := by
      exact (cdfReal_monotone p).measurable.sub
        (cdfReal_monotone q).measurable
    dsimp [slope]
    apply Measurable.ite
      (measurableSet_lt hdiff measurable_const) measurable_const
    exact Measurable.ite
      (measurableSet_lt measurable_const hdiff)
      measurable_const measurable_const
  have slope_norm_le (x : ℝ) : ‖slope x‖ ≤ 1 := by
    dsimp [slope]
    split_ifs <;> norm_num
  have slope_intervalIntegrable (a b : ℝ) :
      IntervalIntegrable slope MeasureTheory.volume a b := by
    constructor
    · apply MeasureTheory.Measure.integrableOn_of_bounded
        (ne_of_lt measure_Ioc_lt_top)
        slope_measurable.aestronglyMeasurable
      filter_upwards [] with x
      exact slope_norm_le x
    · apply MeasureTheory.Measure.integrableOn_of_bounded
        (ne_of_lt measure_Ioc_lt_top)
        slope_measurable.aestronglyMeasurable
      filter_upwards [] with x
      exact slope_norm_le x
  let potential : ℝ → ℝ := fun x =>
    ∫ t in x..1, slope t
  have potential_lipschitz : LipschitzWith 1 potential := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hsub : potential x - potential y =
        ∫ t in x..y, slope t := by
      dsimp [potential]
      simpa using intervalIntegral.integral_interval_sub_interval_comm
        (slope_intervalIntegrable x 1)
        (slope_intervalIntegrable y 1)
        (slope_intervalIntegrable x y)
    rw [Real.dist_eq, Real.dist_eq, hsub]
    simpa [abs_sub_comm] using
      (intervalIntegral.norm_integral_le_of_norm_le_const
        (a := x) (b := y) (C := (1 : ℝ))
        (fun t _ => slope_norm_le t))
  have potential_quantile_gap {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
      potential (quantile p u) - potential (quantile q u) =
        |quantile p u - quantile q u| := by
    have hsub : potential (quantile p u) - potential (quantile q u) =
        ∫ t in quantile p u..quantile q u, slope t := by
      dsimp [potential]
      simpa using intervalIntegral.integral_interval_sub_interval_comm
        (slope_intervalIntegrable (quantile p u) 1)
        (slope_intervalIntegrable (quantile q u) 1)
        (slope_intervalIntegrable (quantile p u) (quantile q u))
    rw [hsub]
    rcases le_total (quantile p u) (quantile q u) with hpq | hqp
    · have hslope : (∫ t in quantile p u..quantile q u, slope t) =
          ∫ _t in quantile p u..quantile q u, (1 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [MeasureTheory.volume.ae_ne (quantile q u)] with t htne
        intro ht
        rw [Set.uIoc_of_le hpq] at ht
        have htq : t < quantile q u :=
          lt_of_le_of_ne ht.2 htne
        have hp_level : ENNReal.ofReal u ≤
            (p : MeasureTheory.Measure ℝ) (Set.Iic t) :=
          (quantile_le_iff p hp hu0 hu1).mp ht.1.le
        have hq_level : (q : MeasureTheory.Measure ℝ) (Set.Iic t) <
            ENNReal.ofReal u := by
          apply lt_of_not_ge
          intro hlevel
          exact (not_le_of_gt htq)
            (quantile_le_of_level_le q hq hu0 hlevel)
        have hmeasure : (q : MeasureTheory.Measure ℝ) (Set.Iic t) <
            (p : MeasureTheory.Measure ℝ) (Set.Iic t) :=
          hq_level.trans_le hp_level
        have hreal :
            ((q : MeasureTheory.Measure ℝ) (Set.Iic t)).toReal <
              ((p : MeasureTheory.Measure ℝ) (Set.Iic t)).toReal :=
          (ENNReal.toReal_lt_toReal
            (MeasureTheory.measure_ne_top _ _)
            (MeasureTheory.measure_ne_top _ _)).mpr hmeasure
        have hpos : 0 < cdfDiff t := by
          dsimp [cdfDiff]
          linarith
        dsimp [slope]
        simp [not_lt_of_ge hpos.le, hpos]
      rw [hslope]
      rw [abs_of_nonpos (sub_nonpos.mpr hpq)]
      simp
    · have hslope : (∫ t in quantile p u..quantile q u, slope t) =
          ∫ _t in quantile p u..quantile q u, (-1 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [MeasureTheory.volume.ae_ne (quantile p u)] with t htne
        intro ht
        rw [Set.uIoc_of_ge hqp] at ht
        have htp : t < quantile p u :=
          lt_of_le_of_ne ht.2 htne
        have hq_level : ENNReal.ofReal u ≤
            (q : MeasureTheory.Measure ℝ) (Set.Iic t) :=
          (quantile_le_iff q hq hu0 hu1).mp ht.1.le
        have hp_level : (p : MeasureTheory.Measure ℝ) (Set.Iic t) <
            ENNReal.ofReal u := by
          apply lt_of_not_ge
          intro hlevel
          exact (not_le_of_gt htp)
            (quantile_le_of_level_le p hp hu0 hlevel)
        have hmeasure : (p : MeasureTheory.Measure ℝ) (Set.Iic t) <
            (q : MeasureTheory.Measure ℝ) (Set.Iic t) :=
          hp_level.trans_le hq_level
        have hreal :
            ((p : MeasureTheory.Measure ℝ) (Set.Iic t)).toReal <
              ((q : MeasureTheory.Measure ℝ) (Set.Iic t)).toReal :=
          (ENNReal.toReal_lt_toReal
            (MeasureTheory.measure_ne_top _ _)
            (MeasureTheory.measure_ne_top _ _)).mpr hmeasure
        have hneg : cdfDiff t < 0 := by
          dsimp [cdfDiff]
          linarith
        dsimp [slope]
        simp [hneg]
      rw [hslope]
      rw [abs_of_nonneg (sub_nonneg.mpr hqp)]
      simp
  have integrable_of_supported_lipschitz
      (μ : MeasureTheory.ProbabilityMeasure ℝ)
      (hμ : (μ : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
      (f : ℝ → ℝ) (hf : LipschitzWith 1 f) :
      MeasureTheory.Integrable f (μ : MeasureTheory.Measure ℝ) := by
    have hmem := ae_mem_interval μ hμ
    have hres := MeasureTheory.Measure.restrict_eq_self_of_ae_mem hmem
    rw [← hres]
    exact hf.continuous.continuousOn.integrableOn_compact isCompact_Icc
  apply le_antisymm
  swap
  rw [wasserstein_one]
  refine le_csInf ?_ ?_
  · refine ⟨∫ z, |z.1 - z.2| ∂((p : MeasureTheory.Measure ℝ).prod
      (q : MeasureTheory.Measure ℝ)), ?_⟩
    refine ⟨(p : MeasureTheory.Measure ℝ).prod
      (q : MeasureTheory.Measure ℝ), ?_, rfl⟩
    simp [is_coupling]
  · rintro b ⟨γ, hγ, rfl⟩
    refine csSup_le ?_ ?_
    · refine ⟨0, ⟨fun _ => 0, LipschitzWith.const' 0, ?_⟩⟩
      simp
    · rintro a ⟨f, hf, rfl⟩
      have hfp := integrable_of_supported_lipschitz p hp f hf
      have hfq := integrable_of_supported_lipschitz q hq f hf
      have hxp := integrable_of_supported_lipschitz p hp id LipschitzWith.id
      have hxq := integrable_of_supported_lipschitz q hq id LipschitzWith.id
      have hfpγ : MeasureTheory.Integrable (fun z : ℝ × ℝ => f z.1) γ := by
        have h : MeasureTheory.Integrable f γ.fst := by
          rw [hγ.1]
          exact hfp
        rw [MeasureTheory.Measure.fst] at h
        exact h.comp_measurable measurable_fst
      have hfqγ : MeasureTheory.Integrable (fun z : ℝ × ℝ => f z.2) γ := by
        have h : MeasureTheory.Integrable f γ.snd := by
          rw [hγ.2]
          exact hfq
        rw [MeasureTheory.Measure.snd] at h
        exact h.comp_measurable measurable_snd
      have hxpγ : MeasureTheory.Integrable (fun z : ℝ × ℝ => z.1) γ := by
        have h : MeasureTheory.Integrable id γ.fst := by
          rw [hγ.1]
          exact hxp
        rw [MeasureTheory.Measure.fst] at h
        exact h.comp_measurable measurable_fst
      have hxqγ : MeasureTheory.Integrable (fun z : ℝ × ℝ => z.2) γ := by
        have h : MeasureTheory.Integrable id γ.snd := by
          rw [hγ.2]
          exact hxq
        rw [MeasureTheory.Measure.snd] at h
        exact h.comp_measurable measurable_snd
      calc
        (∫ x, f x ∂(p : MeasureTheory.Measure ℝ)) -
              ∫ x, f x ∂(q : MeasureTheory.Measure ℝ) =
            (∫ z, f z.1 ∂γ) - ∫ z, f z.2 ∂γ := by
              rw [← hγ.1, ← hγ.2, MeasureTheory.Measure.fst,
                MeasureTheory.Measure.snd,
                MeasureTheory.integral_map measurable_fst.aemeasurable
                  hf.continuous.aestronglyMeasurable,
                MeasureTheory.integral_map measurable_snd.aemeasurable
                  hf.continuous.aestronglyMeasurable]
        _ = ∫ z, (f z.1 - f z.2) ∂γ := by
              rw [MeasureTheory.integral_sub hfpγ hfqγ]
        _ ≤ ∫ z, |z.1 - z.2| ∂γ := by
              apply MeasureTheory.integral_mono_ae
                (hfpγ.sub hfqγ) ((hxpγ.sub hxqγ).abs)
              filter_upwards [] with z
              calc
                f z.1 - f z.2 ≤ |f z.1 - f z.2| := le_abs_self _
                _ ≤ |z.1 - z.2| := by
                  simpa [Real.dist_eq] using hf.dist_le_mul z.1 z.2
  have hquantilePair : AEMeasurable
      (fun u => (quantile p u, quantile q u)) uniformMeasure :=
    (quantile_aemeasurable p hp).prodMk
      (quantile_aemeasurable q hq)
  let optimalCoupling : MeasureTheory.Measure (ℝ × ℝ) :=
    MeasureTheory.Measure.map
      (fun u => (quantile p u, quantile q u)) uniformMeasure
  have optimalCoupling_is_coupling :
      is_coupling p q optimalCoupling := by
    constructor
    · rw [MeasureTheory.Measure.fst]
      change (MeasureTheory.Measure.map
        (fun u => (quantile p u, quantile q u)) uniformMeasure).map
          Prod.fst = _
      rw [measurable_fst.aemeasurable.map_map_of_aemeasurable hquantilePair]
      simpa [Function.comp_def] using map_quantile p hp
    · rw [MeasureTheory.Measure.snd]
      change (MeasureTheory.Measure.map
        (fun u => (quantile p u, quantile q u)) uniformMeasure).map
          Prod.snd = _
      rw [measurable_snd.aemeasurable.map_map_of_aemeasurable hquantilePair]
      simpa [Function.comp_def] using map_quantile q hq
  have potential_integrable_p :=
    integrable_of_supported_lipschitz p hp potential potential_lipschitz
  have potential_integrable_q :=
    integrable_of_supported_lipschitz q hq potential potential_lipschitz
  have potential_quantile_integrable_p :
      MeasureTheory.Integrable (fun u => potential (quantile p u))
        uniformMeasure := by
    have h : MeasureTheory.Integrable potential
        (MeasureTheory.Measure.map (quantile p) uniformMeasure) := by
      rw [map_quantile p hp]
      exact potential_integrable_p
    exact h.comp_aemeasurable (quantile_aemeasurable p hp)
  have potential_quantile_integrable_q :
      MeasureTheory.Integrable (fun u => potential (quantile q u))
        uniformMeasure := by
    have h : MeasureTheory.Integrable potential
        (MeasureTheory.Measure.map (quantile q) uniformMeasure) := by
      rw [map_quantile q hq]
      exact potential_integrable_q
    exact h.comp_aemeasurable (quantile_aemeasurable q hq)
  have optimal_cost_eq_pairing :
      (∫ z, |z.1 - z.2| ∂optimalCoupling) =
        (∫ x, potential x ∂(p : MeasureTheory.Measure ℝ)) -
          ∫ x, potential x ∂(q : MeasureTheory.Measure ℝ) := by
    calc
      (∫ z, |z.1 - z.2| ∂optimalCoupling) =
          ∫ u, |quantile p u - quantile q u| ∂uniformMeasure := by
            change (∫ z, |z.1 - z.2| ∂(MeasureTheory.Measure.map
              (fun u => (quantile p u, quantile q u)) uniformMeasure)) = _
            rw [MeasureTheory.integral_map hquantilePair]
            exact Continuous.aestronglyMeasurable
              (continuous_fst.sub continuous_snd).abs
      _ = ∫ u, (potential (quantile p u) -
          potential (quantile q u)) ∂uniformMeasure := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo]
              with u hu
            exact (potential_quantile_gap hu.1 hu.2).symm
      _ = (∫ u, potential (quantile p u) ∂uniformMeasure) -
          ∫ u, potential (quantile q u) ∂uniformMeasure := by
            rw [MeasureTheory.integral_sub
              potential_quantile_integrable_p
              potential_quantile_integrable_q]
      _ = (∫ x, potential x ∂(p : MeasureTheory.Measure ℝ)) -
          ∫ x, potential x ∂(q : MeasureTheory.Measure ℝ) := by
            rw [← map_quantile p hp, ← map_quantile q hq,
              MeasureTheory.integral_map
                (quantile_aemeasurable p hp)
                potential_lipschitz.continuous.aestronglyMeasurable,
              MeasureTheory.integral_map
                (quantile_aemeasurable q hq)
                potential_lipschitz.continuous.aestronglyMeasurable]
  have dual_bddAbove : BddAbove {a : ℝ | ∃ f : ℝ → ℝ,
      LipschitzWith 1 f ∧
        a = (∫ x, f x ∂(p : MeasureTheory.Measure ℝ)) -
          ∫ x, f x ∂(q : MeasureTheory.Measure ℝ)} := by
    refine ⟨∫ z, |z.1 - z.2| ∂optimalCoupling, ?_⟩
    rintro a ⟨f, hf, rfl⟩
    have hfp := integrable_of_supported_lipschitz p hp f hf
    have hfq := integrable_of_supported_lipschitz q hq f hf
    have hxp := integrable_of_supported_lipschitz p hp id LipschitzWith.id
    have hxq := integrable_of_supported_lipschitz q hq id LipschitzWith.id
    have hfpγ : MeasureTheory.Integrable
        (fun z : ℝ × ℝ => f z.1) optimalCoupling := by
      have h : MeasureTheory.Integrable f optimalCoupling.fst := by
        rw [optimalCoupling_is_coupling.1]
        exact hfp
      rw [MeasureTheory.Measure.fst] at h
      exact h.comp_measurable measurable_fst
    have hfqγ : MeasureTheory.Integrable
        (fun z : ℝ × ℝ => f z.2) optimalCoupling := by
      have h : MeasureTheory.Integrable f optimalCoupling.snd := by
        rw [optimalCoupling_is_coupling.2]
        exact hfq
      rw [MeasureTheory.Measure.snd] at h
      exact h.comp_measurable measurable_snd
    have hxpγ : MeasureTheory.Integrable
        (fun z : ℝ × ℝ => z.1) optimalCoupling := by
      have h : MeasureTheory.Integrable id optimalCoupling.fst := by
        rw [optimalCoupling_is_coupling.1]
        exact hxp
      rw [MeasureTheory.Measure.fst] at h
      exact h.comp_measurable measurable_fst
    have hxqγ : MeasureTheory.Integrable
        (fun z : ℝ × ℝ => z.2) optimalCoupling := by
      have h : MeasureTheory.Integrable id optimalCoupling.snd := by
        rw [optimalCoupling_is_coupling.2]
        exact hxq
      rw [MeasureTheory.Measure.snd] at h
      exact h.comp_measurable measurable_snd
    calc
      (∫ x, f x ∂(p : MeasureTheory.Measure ℝ)) -
            ∫ x, f x ∂(q : MeasureTheory.Measure ℝ) =
          (∫ z, f z.1 ∂optimalCoupling) -
            ∫ z, f z.2 ∂optimalCoupling := by
              rw [← optimalCoupling_is_coupling.1,
                ← optimalCoupling_is_coupling.2,
                MeasureTheory.Measure.fst, MeasureTheory.Measure.snd,
                MeasureTheory.integral_map measurable_fst.aemeasurable
                  hf.continuous.aestronglyMeasurable,
                MeasureTheory.integral_map measurable_snd.aemeasurable
                  hf.continuous.aestronglyMeasurable]
      _ = ∫ z, (f z.1 - f z.2) ∂optimalCoupling := by
            rw [MeasureTheory.integral_sub hfpγ hfqγ]
      _ ≤ ∫ z, |z.1 - z.2| ∂optimalCoupling := by
            apply MeasureTheory.integral_mono_ae
              (hfpγ.sub hfqγ) ((hxpγ.sub hxqγ).abs)
            filter_upwards [] with z
            exact (le_abs_self _).trans (by
              simpa [Real.dist_eq] using hf.dist_le_mul z.1 z.2)
  have coupling_costs_bddBelow : BddBelow {c : ℝ |
      ∃ γ : MeasureTheory.Measure (ℝ × ℝ),
        is_coupling p q γ ∧ c = ∫ z, |z.1 - z.2| ∂γ} := by
    refine ⟨0, ?_⟩
    rintro c ⟨γ, _hγ, rfl⟩
    exact MeasureTheory.integral_nonneg (fun _ => abs_nonneg _)
  rw [wasserstein_one]
  calc
    sInf {c : ℝ | ∃ γ : MeasureTheory.Measure (ℝ × ℝ),
        is_coupling p q γ ∧ c = ∫ z, |z.1 - z.2| ∂γ} ≤
        ∫ z, |z.1 - z.2| ∂optimalCoupling :=
      csInf_le coupling_costs_bddBelow
        ⟨optimalCoupling, optimalCoupling_is_coupling, rfl⟩
    _ = (∫ x, potential x ∂(p : MeasureTheory.Measure ℝ)) -
        ∫ x, potential x ∂(q : MeasureTheory.Measure ℝ) :=
      optimal_cost_eq_pairing
    _ ≤ sSup {a : ℝ | ∃ f : ℝ → ℝ,
        LipschitzWith 1 f ∧
          a = (∫ x, f x ∂(p : MeasureTheory.Measure ℝ)) -
            ∫ x, f x ∂(q : MeasureTheory.Measure ℝ)} :=
      le_csSup dual_bddAbove ⟨potential, potential_lipschitz, rfl⟩

@[blueprint "lem:smooth-lipschitz-uniform-approximation"
  (statement := /-- Let \(f:\mathbb R\to\mathbb R\) be globally
  \(1\)-Lipschitz. For every \(\varepsilon>0\), there exists a globally
  \(1\)-Lipschitz \(C^\infty\) function \(g:\mathbb R\to\mathbb R\) such
  that
  \[
    |g(x)-f(x)|\leq\varepsilon
    \qquad\text{for every }x\in[-1,1].
  \] -/)
  (proof := /-- Put \(\delta=\varepsilon/2\). First construct the flat
  function
  \[
    \psi(u)=
    \begin{cases}
      0,&u\leq0,\\
      \exp(-u^{-1}),&u>0.
    \end{cases}
  \]
  For every polynomial \(P\), the function
  \(P(u^{-1})\psi(u)\) tends to zero as \(u\to0\), since exponential
  decay dominates polynomial growth. Its derivative is again of this
  form, namely
  \[
    \frac{d}{du}\bigl(P(u^{-1})\psi(u)\bigr)
      =\bigl[X^2(P-P')\bigr](u^{-1})\psi(u).
  \]
  Induction on the differentiability order therefore proves that
  \(\psi\) is \(C^\infty\).

  Define \(\varphi(t)=\psi(\delta^2-t^2)\). Then \(\varphi\) is smooth,
  nonnegative, supported on \([-\delta,\delta]\), and positive at zero.
  Consequently its integral \(c\) is positive, and
  \(\rho(t)=\varphi(t)/c\) is an even, nonnegative, compactly supported
  \(C^\infty\) function with integral one. Set
  \[
    g(x)=\int_{\mathbb R}f(t)\rho(x-t)\,dt.
  \]
  Translation invariance of Lebesgue measure and evenness of \(\rho\)
  give the equivalent formula
  \[
    g(x)=\int_{\mathbb R}\rho(t)f(x+t)\,dt.
  \]
  Convolution with the compactly supported smooth kernel \(\rho\) shows
  that \(g\) is \(C^\infty\).

  For \(x,y\in\mathbb R\), nonnegativity and unit mass give
  \[
    |g(x)-g(y)|
      \leq\int\rho(t)|f(x+t)-f(y+t)|\,dt
      \leq|x-y|,
  \]
  so \(g\) is globally \(1\)-Lipschitz. Likewise, for every
  \(x\in\mathbb R\),
  \[
    |g(x)-f(x)|
      \leq\int\rho(t)|f(x+t)-f(x)|\,dt
      \leq\int\rho(t)|t|\,dt
      \leq\delta\leq\varepsilon.
  \]
  This global estimate implies the required bound on \([-1,1]\). -/)
  (title := /-- Smooth Approximation of a Lipschitz Function -/)
  (latexEnv := "lemma")]
lemma smooth_lipschitz_uniform_approximation
    (f : ℝ → ℝ) (hf : LipschitzWith 1 f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℝ → ℝ,
      LipschitzWith 1 g ∧ ContDiff ℝ ∞ g ∧
        ∀ x ∈ Set.Icc (-1 : ℝ) 1, |g x - f x| ≤ ε := by
  let ψ : ℝ → ℝ := fun x => if x ≤ 0 then 0 else Real.exp (-x⁻¹)
  have ψ_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : ψ x = 0 := by
    simp [ψ, hx]
  have ψ_zero : ψ 0 = 0 := ψ_zero_of_nonpos le_rfl
  have ψ_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < ψ x := by
    simp [ψ, not_le.2 hx, Real.exp_pos]
  have ψ_nonneg (x : ℝ) : 0 ≤ ψ x := by
    rcases le_or_gt x 0 with hx | hx
    · exact ge_of_eq (ψ_zero_of_nonpos hx)
    · exact (ψ_pos_of_pos hx).le
  have polynomial_tendsto (p : Polynomial ℝ) :
      Filter.Tendsto (fun x => p.eval x / Real.exp x) Filter.atTop (nhds 0) := by
    induction p using Polynomial.induction_on' with
    | monomial n a =>
      simpa [Real.exp_neg, div_eq_mul_inv, mul_assoc] using
        tendsto_const_nhds.mul
          (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n)
    | add p q hp hq => simpa [add_div] using hp.add hq
  have ψ_tendsto (p : Polynomial ℝ) :
      Filter.Tendsto (fun x => p.eval x⁻¹ * ψ x)
        (nhds 0) (nhds 0) := by
    simp only [ψ, mul_ite, mul_zero]
    refine tendsto_const_nhds.if ?_
    simp only [not_le]
    have hp : Filter.Tendsto (fun x => p.eval x⁻¹ / Real.exp x⁻¹)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      (polynomial_tendsto p).comp tendsto_inv_nhdsGT_zero
    refine hp.congr' <| Filter.mem_of_superset self_mem_nhdsWithin fun x hx => ?_
    simp [Real.exp_neg, div_eq_mul_inv]
  have polynomial_hasDeriv (p : Polynomial ℝ) (x : ℝ) :
      HasDerivAt (fun x => p.eval x) (Polynomial.derivative p |>.eval x) x := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa using! hp.add hq
    | monomial n a =>
      simpa [mul_assoc, Polynomial.derivative_monomial] using
        (hasDerivAt_pow n x).const_mul a
  have ψ_hasDeriv (p : Polynomial ℝ) (x : ℝ) :
      HasDerivAt (fun x => p.eval x⁻¹ * ψ x)
        ((Polynomial.X ^ 2 * (p - Polynomial.derivative p)).eval x⁻¹ * ψ x) x := by
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · rw [ψ_zero_of_nonpos hx.le, mul_zero]
      refine (hasDerivAt_const _ 0).congr_of_eventuallyEq ?_
      filter_upwards [gt_mem_nhds hx] with y hy
      rw [ψ_zero_of_nonpos hy.le, mul_zero]
    · rw [ψ_zero, mul_zero, hasDerivAt_iff_tendsto_slope]
      refine ((ψ_tendsto (p * Polynomial.X)).mono_left inf_le_left).congr fun x => ?_
      simp [slope_def_field, ψ_zero, div_eq_mul_inv, mul_right_comm]
    · have hp := ((polynomial_hasDeriv p x⁻¹).mul (hasDerivAt_neg _).exp).comp x
        (hasDerivAt_inv hx.ne')
      convert! hp.congr_of_eventuallyEq _ using 1
      · simp [ψ, hx.not_ge]
        ring
      · filter_upwards [lt_mem_nhds hx] with y hy
        simp [ψ, hy.not_ge]
  have ψ_differentiable (p : Polynomial ℝ) :
      Differentiable ℝ (fun x => p.eval x⁻¹ * ψ x) := fun x =>
    (ψ_hasDeriv p x).differentiableAt
  have ψ_continuous (p : Polynomial ℝ) :
      Continuous (fun x => p.eval x⁻¹ * ψ x) :=
    (ψ_differentiable p).continuous
  have ψ_contDiff_poly {n : ℕ∞} (p : Polynomial ℝ) :
      ContDiff ℝ n (fun x => p.eval x⁻¹ * ψ x) := by
    apply contDiff_all_iff_nat.2 (fun m => ?_) n
    induction m generalizing p with
    | zero => exact contDiff_zero.2 (ψ_continuous p)
    | succ m ihm =>
      rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = m + 1 from rfl]
      refine contDiff_succ_iff_deriv.2 ⟨ψ_differentiable p, by simp, ?_⟩
      convert! ihm (Polynomial.X ^ 2 * (p - Polynomial.derivative p)) using 2
      exact (ψ_hasDeriv p _).deriv
  have ψ_smooth {n : ℕ∞} : ContDiff ℝ n ψ := by
    simpa using ψ_contDiff_poly (1 : Polynomial ℝ)
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  let φ : ℝ → ℝ := fun t => ψ (δ ^ 2 - t ^ 2)
  have hφ_smooth : ContDiff ℝ ∞ φ := by
    exact ψ_smooth.comp (contDiff_const.sub (contDiff_id.pow 2))
  have hφ_nonneg (t : ℝ) : 0 ≤ φ t := by
    exact ψ_nonneg _
  have hφ_compact : HasCompactSupport φ := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-δ) δ))
    intro t ht
    apply ψ_zero_of_nonpos
    simp only [Set.mem_Icc, not_and_or] at ht
    rcases ht with ht | ht <;> nlinarith
  have hφ_integrable : MeasureTheory.Integrable φ :=
    hφ_smooth.continuous.integrable_of_hasCompactSupport hφ_compact
  let c : ℝ := ∫ t, φ t
  have hc_pos : 0 < c := by
    apply hφ_smooth.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      hφ_compact hφ_nonneg
    change φ 0 ≠ 0
    exact ne_of_gt (ψ_pos_of_pos (by
      change 0 < δ ^ 2 - (0 : ℝ) ^ 2
      nlinarith [sq_pos_of_pos hδ]))
  let ρ : ℝ → ℝ := fun t => φ t / c
  have hρ_nonneg (t : ℝ) : 0 ≤ ρ t := by
    exact div_nonneg (hφ_nonneg t) hc_pos.le
  have hρ_integral : ∫ t, ρ t = 1 := by
    dsimp [ρ]
    rw [MeasureTheory.integral_div]
    exact div_self hc_pos.ne'
  have hρ_integrable : MeasureTheory.Integrable ρ := by
    exact hφ_integrable.div_const c
  have hρ_smooth : ContDiff ℝ ∞ ρ := by
    exact hφ_smooth.div_const c
  have hρ_compact : HasCompactSupport ρ := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-δ) δ))
    intro t ht
    have hφt : φ t = 0 := by
      apply ψ_zero_of_nonpos
      simp only [Set.mem_Icc, not_and_or] at ht
      rcases ht with ht | ht <;> nlinarith
    simp [ρ, hφt]
  have hρ_even (t : ℝ) : ρ (-t) = ρ t := by
    simp [ρ, φ]
  let g : ℝ → ℝ := fun x => ∫ t, f t * ρ (x - t)
  have hg_repr (x : ℝ) : g x = ∫ t, ρ t * f (x + t) := by
    dsimp [g]
    rw [← MeasureTheory.integral_add_left_eq_self
      (fun t => f t * ρ (x - t)) x]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with t
    rw [show x - (x + t) = -t by ring, hρ_even]
    ring
  have hg_integrable (x : ℝ) :
      MeasureTheory.Integrable (fun t => ρ t * f (x + t)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hρ_smooth.continuous.mul
        (hf.continuous.comp (continuous_const.add continuous_id))
    · exact hρ_compact.mul_right
  have hg_lipschitz : LipschitzWith 1 g :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq]
      rw [hg_repr x, hg_repr y]
      change |(∫ t, ρ t * f (x + t)) - ∫ t, ρ t * f (y + t)| ≤
        (1 : ℝ) * dist x y
      rw [← MeasureTheory.integral_sub (hg_integrable x) (hg_integrable y)]
      calc
        |∫ t, ρ t * f (x + t) - ρ t * f (y + t)| ≤
            ∫ t, |ρ t * f (x + t) - ρ t * f (y + t)| :=
          MeasureTheory.abs_integral_le_integral_abs
        _ ≤ ∫ t, |x - y| * ρ t := by
          apply MeasureTheory.integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall fun t => abs_nonneg _
          · exact hρ_integrable.const_mul |x - y|
          · exact Filter.Eventually.of_forall fun t => by
              have hxy := hf.dist_le_mul (x + t) (y + t)
              have hxy' : |f (x + t) - f (y + t)| ≤ |x - y| := by
                simpa [Real.dist_eq] using hxy
              calc
                |ρ t * f (x + t) - ρ t * f (y + t)| =
                    ρ t * |f (x + t) - f (y + t)| := by
                  rw [← mul_sub, abs_mul, abs_of_nonneg (hρ_nonneg t)]
                _ ≤ ρ t * |x - y| :=
                  mul_le_mul_of_nonneg_left hxy' (hρ_nonneg t)
                _ = |x - y| * ρ t := mul_comm _ _
        _ = |x - y| * ∫ t, ρ t := by
          rw [MeasureTheory.integral_const_mul]
        _ = (1 : ℝ) * dist x y := by
          rw [hρ_integral]
          simp [Real.dist_eq]
  have hg_smooth : ContDiff ℝ ∞ g := by
    change ContDiff ℝ ∞
      (MeasureTheory.convolution f ρ
        (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume)
    exact hρ_compact.contDiff_convolution_right
      (ContinuousLinearMap.mul ℝ ℝ) hf.continuous.locallyIntegrable hρ_smooth
  refine ⟨g, hg_lipschitz, hg_smooth, ?_⟩
  intro x _hx
  rw [hg_repr x]
  change |(∫ t, ρ t * f (x + t)) - f x| ≤ ε
  calc
    |(∫ t, ρ t * f (x + t)) - f x| =
        |(∫ t, ρ t * f (x + t)) - f x * ∫ t, ρ t| := by
      rw [hρ_integral, mul_one]
    _ = |(∫ t, ρ t * f (x + t)) - ∫ t, f x * ρ t| := by
      rw [MeasureTheory.integral_const_mul]
    _ = |∫ t, ρ t * f (x + t) - f x * ρ t| := by
      rw [MeasureTheory.integral_sub (hg_integrable x)
        (hρ_integrable.const_mul (f x))]
    _ ≤ ∫ t, |ρ t * f (x + t) - f x * ρ t| :=
      MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ t, δ * ρ t := by
      apply MeasureTheory.integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun t => abs_nonneg _
      · exact hρ_integrable.const_mul δ
      · exact Filter.Eventually.of_forall fun t => by
          have hxt := hf.dist_le_mul (x + t) x
          have hxt' : |f (x + t) - f x| ≤ |t| := by
            simpa [Real.dist_eq] using hxt
          have ht : ρ t * |t| ≤ δ * ρ t := by
            by_cases hρt : ρ t = 0
            · simp [hρt]
            · have hφt : φ t ≠ 0 := by
                intro hφt
                exact hρt (by simp [ρ, hφt])
              have harg : 0 < δ ^ 2 - t ^ 2 := by
                by_contra harg
                exact hφt (by
                  apply ψ_zero_of_nonpos
                  exact le_of_not_gt harg)
              have ht_sq : |t| ^ 2 = t ^ 2 := by
                exact sq_abs t
              have ht_lt : |t| < δ := by
                nlinarith [abs_nonneg t]
              calc
                ρ t * |t| ≤ ρ t * δ :=
                  mul_le_mul_of_nonneg_left (le_of_lt ht_lt) (hρ_nonneg t)
                _ = δ * ρ t := mul_comm _ _
          calc
            |ρ t * f (x + t) - f x * ρ t| =
                ρ t * |f (x + t) - f x| := by
              rw [mul_comm (f x), ← mul_sub, abs_mul,
                abs_of_nonneg (hρ_nonneg t)]
            _ ≤ ρ t * |t| :=
              mul_le_mul_of_nonneg_left hxt' (hρ_nonneg t)
            _ ≤ δ * ρ t := ht
    _ = δ * ∫ t, ρ t := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ ε := by
      rw [hρ_integral]
      dsimp [δ]
      linarith

@[blueprint "lem:kantorovich-rubinstein-smooth-duality"
  (statement := /-- Let \(p,q\) be probability measures on \(\mathbb R\)
  whose supports are contained in \([-1,1]\). Then
  \[
    W_1(p,q)=\sup_f\left(\int f\,dp-\int f\,dq\right),
  \]
  where the supremum is taken over all globally \(1\)-Lipschitz,
  \(C^\infty\) functions \(f:\mathbb R\to\mathbb R\). -/)
  (proof := /-- By
  \cref{lem:kantorovich-rubinstein-lipschitz-duality}, it is enough to show
  that restricting the dual supremum to smooth test functions does not
  change its value. The smooth class is contained in the full Lipschitz
  class, so its supremum is no larger.

  For the reverse inequality, fix a globally \(1\)-Lipschitz function
  \(f:\mathbb R\to\mathbb R\) and \(\varepsilon>0\). By
  \cref{lem:smooth-lipschitz-uniform-approximation}, there is a globally
  \(1\)-Lipschitz \(C^\infty\) function \(g\) with
  \(|g-f|\leq\varepsilon\) on \([-1,1]\). Since both measures have total
  mass one and are supported on this interval,
  \[
    \left|\left(\int f\,dp-\int f\,dq\right)
      -\left(\int g\,dp-\int g\,dq\right)\right|\leq2\varepsilon.
  \]
  The smooth supremum is nonempty, because it contains the pairing of the
  zero function, and is bounded above by the full Lipschitz supremum.
  Hence the preceding estimate, followed by
  \(\varepsilon\downarrow0\), shows that every full Lipschitz pairing is at
  most the smooth supremum. Taking the supremum over \(f\) proves the
  reverse inequality and therefore the asserted equality. -/)
  (title := /-- Smooth Kantorovich--Rubinstein Duality -/)
  (latexEnv := "lemma")]
lemma kantorovich_rubinstein_smooth_duality
    (p q : MeasureTheory.ProbabilityMeasure ℝ)
    (hp : (p : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
    (hq : (q : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1) :
    wasserstein_one p q =
      sSup {a : ℝ | ∃ f : ℝ → ℝ,
        LipschitzWith 1 f ∧ ContDiff ℝ ∞ f ∧
          a = (∫ x, f x ∂(p : MeasureTheory.Measure ℝ)) -
            ∫ x, f x ∂(q : MeasureTheory.Measure ℝ)} := by
  have ae_mem_interval
      (μ : MeasureTheory.ProbabilityMeasure ℝ)
      (hμ : (μ : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1) :
      ∀ᵐ x ∂(μ : MeasureTheory.Measure ℝ), x ∈ Set.Icc (-1 : ℝ) 1 := by
    filter_upwards [(μ : MeasureTheory.Measure ℝ).support_mem_ae] with x hx
    exact hμ hx
  have integrable_of_supported_lipschitz
      (μ : MeasureTheory.ProbabilityMeasure ℝ)
      (hμ : (μ : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
      (f : ℝ → ℝ) (hf : LipschitzWith 1 f) :
      MeasureTheory.Integrable f (μ : MeasureTheory.Measure ℝ) := by
    have hmem := ae_mem_interval μ hμ
    have hres := MeasureTheory.Measure.restrict_eq_self_of_ae_mem hmem
    rw [← hres]
    exact hf.continuous.continuousOn.integrableOn_compact isCompact_Icc
  have integral_gap_bound
      (μ : MeasureTheory.ProbabilityMeasure ℝ)
      (hμ : (μ : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
      (f g : ℝ → ℝ) (hf : LipschitzWith 1 f) (hg : LipschitzWith 1 g)
      (ε : ℝ) (hfg : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |g x - f x| ≤ ε) :
      |(∫ x, f x ∂(μ : MeasureTheory.Measure ℝ)) -
        ∫ x, g x ∂(μ : MeasureTheory.Measure ℝ)| ≤ ε := by
    have hfi := integrable_of_supported_lipschitz μ hμ f hf
    have hgi := integrable_of_supported_lipschitz μ hμ g hg
    rw [← MeasureTheory.integral_sub hfi hgi]
    have hbound := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := (μ : MeasureTheory.Measure ℝ)) (f := fun x => f x - g x) (by
        filter_upwards [ae_mem_interval μ hμ] with x hx
        simpa [Real.norm_eq_abs, abs_sub_comm] using hfg x hx)
    simpa [Real.norm_eq_abs] using hbound
  have pairing_le_two (f : ℝ → ℝ) (hf : LipschitzWith 1 f) :
      (∫ x, f x ∂(p : MeasureTheory.Measure ℝ)) -
        ∫ x, f x ∂(q : MeasureTheory.Measure ℝ) ≤ 2 := by
    have hconst : LipschitzWith 1 (fun _ : ℝ => f 0) :=
      LipschitzWith.const' (f 0)
    have happrox :
        ∀ x ∈ Set.Icc (-1 : ℝ) 1, |(fun _ : ℝ => f 0) x - f x| ≤ 1 := by
      intro x hx
      have hdist : |f 0 - f x| ≤ |x| := by
        simpa [Real.dist_eq] using hf.dist_le_mul 0 x
      exact hdist.trans (abs_le.2 hx)
    have hp0 : |(∫ x, f x ∂(p : MeasureTheory.Measure ℝ)) - f 0| ≤ 1 := by
      simpa using integral_gap_bound p hp f (fun _ => f 0) hf hconst 1 happrox
    have hq0 : |(∫ x, f x ∂(q : MeasureTheory.Measure ℝ)) - f 0| ≤ 1 := by
      simpa using integral_gap_bound q hq f (fun _ => f 0) hf hconst 1 happrox
    linarith [le_abs_self
      ((∫ x, f x ∂(p : MeasureTheory.Measure ℝ)) - f 0),
      neg_le_abs ((∫ x, f x ∂(q : MeasureTheory.Measure ℝ)) - f 0)]
  let fullPairings : Set ℝ := {a : ℝ | ∃ f : ℝ → ℝ,
    LipschitzWith 1 f ∧
      a = (∫ x, f x ∂(p : MeasureTheory.Measure ℝ)) -
        ∫ x, f x ∂(q : MeasureTheory.Measure ℝ)}
  let smoothPairings : Set ℝ := {a : ℝ | ∃ f : ℝ → ℝ,
    LipschitzWith 1 f ∧ ContDiff ℝ ∞ f ∧
      a = (∫ x, f x ∂(p : MeasureTheory.Measure ℝ)) -
        ∫ x, f x ∂(q : MeasureTheory.Measure ℝ)}
  have full_nonempty : fullPairings.Nonempty := by
    refine ⟨0, ?_⟩
    change ∃ f : ℝ → ℝ, LipschitzWith 1 f ∧
      0 = (∫ x, f x ∂(p : MeasureTheory.Measure ℝ)) -
        ∫ x, f x ∂(q : MeasureTheory.Measure ℝ)
    exact ⟨fun _ => 0, LipschitzWith.const' 0, by simp⟩
  have smooth_nonempty : smoothPairings.Nonempty := by
    refine ⟨0, ?_⟩
    change ∃ f : ℝ → ℝ, LipschitzWith 1 f ∧ ContDiff ℝ ∞ f ∧
      0 = (∫ x, f x ∂(p : MeasureTheory.Measure ℝ)) -
        ∫ x, f x ∂(q : MeasureTheory.Measure ℝ)
    exact ⟨fun _ => 0, LipschitzWith.const' 0, contDiff_const, by simp⟩
  have full_bddAbove : BddAbove fullPairings := by
    refine ⟨2, ?_⟩
    intro a ha
    change (∃ f : ℝ → ℝ, LipschitzWith 1 f ∧
      a = (∫ x, f x ∂(p : MeasureTheory.Measure ℝ)) -
        ∫ x, f x ∂(q : MeasureTheory.Measure ℝ)) at ha
    rcases ha with ⟨f, hf, rfl⟩
    exact pairing_le_two f hf
  have smooth_bddAbove : BddAbove smoothPairings := by
    refine ⟨2, ?_⟩
    intro a ha
    change (∃ f : ℝ → ℝ, LipschitzWith 1 f ∧ ContDiff ℝ ∞ f ∧
      a = (∫ x, f x ∂(p : MeasureTheory.Measure ℝ)) -
        ∫ x, f x ∂(q : MeasureTheory.Measure ℝ)) at ha
    rcases ha with ⟨f, hf, _hf_smooth, rfl⟩
    exact pairing_le_two f hf
  change wasserstein_one p q = sSup smoothPairings
  rw [kantorovich_rubinstein_lipschitz_duality p q hp hq]
  change sSup fullPairings = sSup smoothPairings
  apply le_antisymm
  · refine csSup_le full_nonempty ?_
    intro a ha
    change (∃ f : ℝ → ℝ, LipschitzWith 1 f ∧
      a = (∫ x, f x ∂(p : MeasureTheory.Measure ℝ)) -
        ∫ x, f x ∂(q : MeasureTheory.Measure ℝ)) at ha
    rcases ha with ⟨f, hf, rfl⟩
    by_contra hle
    have hlt : sSup smoothPairings <
        (∫ x, f x ∂(p : MeasureTheory.Measure ℝ)) -
          ∫ x, f x ∂(q : MeasureTheory.Measure ℝ) :=
      lt_of_not_ge hle
    let ε : ℝ := ((∫ x, f x ∂(p : MeasureTheory.Measure ℝ)) -
      ∫ x, f x ∂(q : MeasureTheory.Measure ℝ) -
        sSup smoothPairings) / 4
    have hε : 0 < ε := by
      dsimp [ε]
      positivity
    obtain ⟨g, hg, hg_smooth, hfg⟩ :=
      smooth_lipschitz_uniform_approximation f hf ε hε
    have hgap_p := integral_gap_bound p hp f g hf hg ε hfg
    have hgap_q := integral_gap_bound q hq f g hf hg ε hfg
    have hg_mem :
        ((∫ x, g x ∂(p : MeasureTheory.Measure ℝ)) -
          ∫ x, g x ∂(q : MeasureTheory.Measure ℝ)) ∈ smoothPairings := by
      change ∃ u : ℝ → ℝ, LipschitzWith 1 u ∧ ContDiff ℝ ∞ u ∧
        (∫ x, g x ∂(p : MeasureTheory.Measure ℝ)) -
          ∫ x, g x ∂(q : MeasureTheory.Measure ℝ) =
            (∫ x, u x ∂(p : MeasureTheory.Measure ℝ)) -
              ∫ x, u x ∂(q : MeasureTheory.Measure ℝ)
      exact ⟨g, hg, hg_smooth, rfl⟩
    have hg_le :
        (∫ x, g x ∂(p : MeasureTheory.Measure ℝ)) -
          ∫ x, g x ∂(q : MeasureTheory.Measure ℝ) ≤
            sSup smoothPairings :=
      le_csSup smooth_bddAbove hg_mem
    have hpair :
        (∫ x, f x ∂(p : MeasureTheory.Measure ℝ)) -
          ∫ x, f x ∂(q : MeasureTheory.Measure ℝ) ≤
            ((∫ x, g x ∂(p : MeasureTheory.Measure ℝ)) -
              ∫ x, g x ∂(q : MeasureTheory.Measure ℝ)) + 2 * ε := by
      linarith [le_abs_self
        ((∫ x, f x ∂(p : MeasureTheory.Measure ℝ)) -
          ∫ x, g x ∂(p : MeasureTheory.Measure ℝ)),
        neg_le_abs
          ((∫ x, f x ∂(q : MeasureTheory.Measure ℝ)) -
            ∫ x, g x ∂(q : MeasureTheory.Measure ℝ))]
    dsimp [ε] at hpair
    linarith
  · refine csSup_le smooth_nonempty ?_
    intro a ha
    change (∃ f : ℝ → ℝ, LipschitzWith 1 f ∧ ContDiff ℝ ∞ f ∧
      a = (∫ x, f x ∂(p : MeasureTheory.Measure ℝ)) -
        ∫ x, f x ∂(q : MeasureTheory.Measure ℝ)) at ha
    rcases ha with ⟨f, hf, _hf_smooth, rfl⟩
    apply le_csSup full_bddAbove
    change ∃ u : ℝ → ℝ, LipschitzWith 1 u ∧
      (∫ x, f x ∂(p : MeasureTheory.Measure ℝ)) -
        ∫ x, f x ∂(q : MeasureTheory.Measure ℝ) =
          (∫ x, u x ∂(p : MeasureTheory.Measure ℝ)) -
            ∫ x, u x ∂(q : MeasureTheory.Measure ℝ)
    exact ⟨f, hf, rfl⟩

@[blueprint "lem:source-normalization-conversion"
  (statement := /-- Let \(p,q\) be probability measures on \(\mathbb R\)
  whose supports are contained in \([-1,1]\), and let \(j\) be a positive
  integer. Then the ordinary and normalized moment differences satisfy
  \[
    \sqrt{\frac{\pi}{2}}\,
      \bigl(\widetilde m_j(p)-\widetilde m_j(q)\bigr)
      =m_j(p)-m_j(q).
  \] -/)
  (proof := /-- Since \(j\geq1\),
  \cref{def:normalized-chebyshev-first} gives
  \(\mathcal T_j=T_j/\sqrt{\pi/2}\). The number
  \(\sqrt{\pi/2}\) is nonzero because \(\pi>0\). Linearity of integration
  in \cref{def:normalized-chebyshev-moment} and
  \cref{def:chebyshev-moment} therefore gives
  \[
    \widetilde m_j(r)=\frac{m_j(r)}{\sqrt{\pi/2}}
  \]
  for \(r=p\) and for \(r=q\). Subtracting these two identities and
  multiplying by \(\sqrt{\pi/2}\) proves the claim. -/)
  (title := /-- Source Normalization Conversion -/)
  (latexEnv := "lemma")]
lemma source_normalization_conversion
    (p q : MeasureTheory.ProbabilityMeasure ℝ)
    (hp : (p : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
    (hq : (q : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
    (j : ℕ) (hj : 0 < j) :
    Real.sqrt (Real.pi / 2) *
      (normalized_chebyshev_moment p j -
        normalized_chebyshev_moment q j) =
      chebyshev_moment p j - chebyshev_moment q j := by
  simp only [normalized_chebyshev_moment, normalized_chebyshev_first,
    if_neg (Nat.ne_of_gt hj), chebyshev_moment, div_eq_mul_inv,
    MeasureTheory.integral_mul_const]
  have hs : Real.sqrt (Real.pi / 2) ≠ 0 := by positivity
  field_simp [hs]

@[blueprint "lem:global-chebyshev-coefficient-decay"
  (statement := /-- Let \(f:\mathbb R\to\mathbb R\) be \(C^\infty\) and
  \(\ell\)-Lipschitz, where \(\ell\geq 0\). If \(c_j(f)\) denotes the
  normalized coefficient from \cref{def:chebyshev-coefficient}, then the
  series \(\sum_{j\geq 0}(jc_j(f))^2\) is summable and
  \[
    \sum_{j=0}^{\infty}(jc_j(f))^2\leq \frac{\pi}{2}\ell^2.
  \] -/)
  (proof := /-- Put \(h(\theta)=f(\cos\theta)\) for
  \(0\leq\theta\leq\pi\). By
  \cref{def:chebyshev-coefficient} and
  \cref{def:normalized-chebyshev-first}, for every \(j\geq1\),
  \[
    c_j(f)=\sqrt{\frac{2}{\pi}}
      \int_0^\pi h(\theta)\cos(j\theta)\,d\theta.
  \]
  The function \(h\) is absolutely continuous and satisfies
  \(h'(\theta)=-\sin(\theta)f'(\cos\theta)\). Integration by parts, whose
  boundary term vanishes because \(\sin(j\theta)=0\) at both endpoints,
  gives
  \[
    j c_j(f)=-\sqrt{\frac{2}{\pi}}
      \int_0^\pi h'(\theta)\sin(j\theta)\,d\theta.
  \]
  Bessel's inequality for the normalized sine system on \([0,\pi]\)
  consequently yields
  \[
    \sum_{j=1}^{\infty}(j c_j(f))^2
      \leq\int_0^\pi|h'(\theta)|^2\,d\theta.
  \]
  Since \(f\) is \(\ell\)-Lipschitz, \(|f'|\leq\ell\) everywhere, and
  therefore
  \[
    \int_0^\pi|h'(\theta)|^2\,d\theta
      \leq\ell^2\int_0^\pi\sin^2\theta\,d\theta
      =\frac{\pi}{2}\ell^2.
  \]
  The finite bound also proves summability of the nonnegative series. The
  term with \(j=0\) vanishes, so this is exactly the asserted series. -/)
  (title := /-- Global Chebyshev-Coefficient Decay -/)
  (latexEnv := "lemma")]
lemma global_chebyshev_coefficient_decay
    (f : ℝ → ℝ) (ℓ : NNReal)
    (hf : LipschitzWith ℓ f) (hf_smooth : ContDiff ℝ ⊤ f) :
    Summable (fun j : ℕ =>
      (((j : ℝ) * chebyshev_coefficient f j) ^ 2)) ∧
      (∑' j : ℕ, (((j : ℝ) * chebyshev_coefficient f j) ^ 2)) ≤
        Real.pi / 2 * (ℓ : ℝ) ^ 2 := by
  let g : ℝ → ℝ := fun θ => -(Real.sin θ) * deriv f (Real.cos θ)
  have hg_cont : Continuous g := by
    dsimp [g]
    fun_prop (disch := aesop)
  have hcomp_deriv (θ : ℝ) :
      HasDerivAt (fun t : ℝ => f (Real.cos t)) (g θ) θ := by
    rw [show g θ = deriv f (Real.cos θ) * (-Real.sin θ) by
      dsimp [g]
      ring]
    simpa only [Function.comp_def] using
      (hf_smooth.differentiable (by simp) (Real.cos θ)).hasDerivAt.comp θ
        (Real.hasDerivAt_cos θ)
  have hcoeff (j : ℕ) (hj : 0 < j) :
      (j : ℝ) * chebyshev_coefficient f j =
        -((Real.sqrt (Real.pi / 2))⁻¹ * ∫ θ in (0 : ℝ)..Real.pi,
          g θ * Real.sin ((j : ℝ) * θ)) := by
    rw [chebyshev_coefficient,
      Polynomial.Chebyshev.integral_measureT_eq_integral_cos]
    simp only [normalized_chebyshev_first, hj.ne', ↓reduceIte,
      chebyshev_first, Polynomial.Chebyshev.T_real_cos]
    have hsin_deriv (θ : ℝ) :
        HasDerivAt (fun t : ℝ => Real.sin ((j : ℝ) * t))
          ((j : ℝ) * Real.cos ((j : ℝ) * θ)) θ := by
      rw [show (j : ℝ) * Real.cos ((j : ℝ) * θ) =
        Real.cos ((j : ℝ) * θ) * (j : ℝ) by ring]
      simpa only [Function.comp_def, mul_one] using
        (Real.hasDerivAt_sin ((j : ℝ) * θ)).comp θ
          ((hasDerivAt_id θ).const_mul (j : ℝ))
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun θ _ => hcomp_deriv θ) (fun θ _ => hsin_deriv θ)
      (hg_cont.intervalIntegrable 0 Real.pi)
      ((continuous_const.mul (Real.continuous_cos.comp
        (continuous_const.mul continuous_id))).intervalIntegrable 0 Real.pi)
    simp only [Real.sin_zero, Real.sin_nat_mul_pi, mul_zero, sub_zero,
      zero_sub] at hibp
    calc
      (j : ℝ) * ∫ θ in (0 : ℝ)..Real.pi,
          f (Real.cos θ) *
            (Real.cos ((j : ℤ) * θ) / Real.sqrt (Real.pi / 2)) =
          (Real.sqrt (Real.pi / 2))⁻¹ * ∫ θ in (0 : ℝ)..Real.pi,
            f (Real.cos θ) *
              ((j : ℝ) * Real.cos ((j : ℝ) * θ)) := by
              rw [← intervalIntegral.integral_const_mul,
                ← intervalIntegral.integral_const_mul]
              apply intervalIntegral.integral_congr
              intro θ _
              norm_cast
              ring
      _ = (Real.sqrt (Real.pi / 2))⁻¹ *
            (-∫ θ in (0 : ℝ)..Real.pi,
              g θ * Real.sin ((j : ℝ) * θ)) := by
            rw [hibp]
      _ = -((Real.sqrt (Real.pi / 2))⁻¹ *
            ∫ θ in (0 : ℝ)..Real.pi,
              g θ * Real.sin ((j : ℝ) * θ)) := by ring
  have hcos_int (k : ℤ) :
      (∫ θ in (0 : ℝ)..Real.pi, Real.cos ((k : ℝ) * θ)) =
        if k = 0 then Real.pi else 0 := by
    by_cases hk : k = 0
    · subst k
      simp
    · rw [if_neg hk]
      have hk_real : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      have hanti (x : ℝ) :
          HasDerivAt
            (fun t : ℝ => (k : ℝ)⁻¹ * Real.sin ((k : ℝ) * t))
            (Real.cos ((k : ℝ) * x)) x := by
        have h := ((Real.hasDerivAt_sin ((k : ℝ) * x)).comp x
          ((hasDerivAt_id x).const_mul (k : ℝ))).const_mul (k : ℝ)⁻¹
        have hder : (k : ℝ)⁻¹ *
            (Real.cos ((k : ℝ) * x) * ((k : ℝ) * 1)) =
            Real.cos ((k : ℝ) * x) := by
          field_simp
        rw [← hder]
        simpa only [Function.comp_def] using h
      have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hanti x)
        ((Real.continuous_cos.comp
          (continuous_const.mul continuous_id)).intervalIntegrable 0 Real.pi)
      simpa only [Real.sin_zero, Real.sin_int_mul_pi, mul_zero,
        sub_self] using hfund
  have hsine_orth (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
      (∫ θ in (0 : ℝ)..Real.pi,
        Real.sin ((i : ℝ) * θ) * Real.sin ((j : ℝ) * θ)) =
          if i = j then Real.pi / 2 else 0 := by
    have hprod :
        2 * (∫ θ in (0 : ℝ)..Real.pi,
          Real.sin ((i : ℝ) * θ) * Real.sin ((j : ℝ) * θ)) =
        (∫ θ in (0 : ℝ)..Real.pi,
          Real.cos (((i : ℝ) - (j : ℝ)) * θ)) -
        (∫ θ in (0 : ℝ)..Real.pi,
          Real.cos (((i : ℝ) + (j : ℝ)) * θ)) := by
      rw [← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub]
      · apply intervalIntegral.integral_congr
        intro θ _
        change 2 *
            (Real.sin ((i : ℝ) * θ) * Real.sin ((j : ℝ) * θ)) =
          Real.cos (((i : ℝ) - (j : ℝ)) * θ) -
            Real.cos (((i : ℝ) + (j : ℝ)) * θ)
        rw [show ((i : ℝ) - (j : ℝ)) * θ =
          (i : ℝ) * θ - (j : ℝ) * θ by ring]
        rw [show ((i : ℝ) + (j : ℝ)) * θ =
          (i : ℝ) * θ + (j : ℝ) * θ by ring]
        rw [← mul_assoc]
        exact Real.two_mul_sin_mul_sin ((i : ℝ) * θ) ((j : ℝ) * θ)
      · apply Continuous.intervalIntegrable
        fun_prop
      · apply Continuous.intervalIntegrable
        fun_prop
    have hminus := hcos_int ((i : ℤ) - (j : ℤ))
    have hplus := hcos_int ((i : ℤ) + (j : ℤ))
    simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast] at hminus hplus
    rw [hminus, hplus] at hprod
    by_cases hij : i = j
    · subst j
      simp [hi.ne'] at hprod ⊢
      linarith
    · have hsub : (i : ℤ) - (j : ℤ) ≠ 0 :=
        sub_ne_zero.mpr (by exact_mod_cast hij)
      have hadd : (i : ℤ) + (j : ℤ) ≠ 0 := by positivity
      simp [hij, hsub, hadd] at hprod ⊢
      linarith
  let κ : ℝ := (Real.sqrt (Real.pi / 2))⁻¹
  have hsqrt_sq : (Real.sqrt (Real.pi / 2)) ^ 2 = Real.pi / 2 := by
    rw [Real.sq_sqrt]
    positivity
  have hκ : κ ^ 2 * (Real.pi / 2) = 1 := by
    dsimp [κ]
    rw [inv_pow, hsqrt_sq]
    field_simp
  let e : ℕ → ℝ → ℝ :=
    fun j θ => κ * Real.sin (((j + 1 : ℕ) : ℝ) * θ)
  have he_cont (j : ℕ) : Continuous (e j) := by
    dsimp [e]
    fun_prop
  have horth (i j : ℕ) :
      (∫ θ in (0 : ℝ)..Real.pi, e i θ * e j θ) =
        if i = j then 1 else 0 := by
    rw [show (fun θ => e i θ * e j θ) =
      fun θ => κ ^ 2 * (Real.sin (((i + 1 : ℕ) : ℝ) * θ) *
        Real.sin (((j + 1 : ℕ) : ℝ) * θ)) by
          funext θ
          dsimp [e]
          ring]
    rw [intervalIntegral.integral_const_mul,
      hsine_orth (i + 1) (j + 1) (by omega) (by omega)]
    by_cases hij : i = j
    · simp [hij, hκ]
    · simp [hij]
  let a : ℕ → ℝ := fun j =>
    ∫ θ in (0 : ℝ)..Real.pi, g θ * e j θ
  let S : ℕ → ℝ → ℝ := fun n θ =>
    ∑ j ∈ Finset.range n, a j * e j θ
  have hS_cont (n : ℕ) : Continuous (S n) := by
    dsimp [S]
    fun_prop
  have hgs (n : ℕ) :
      (∫ θ in (0 : ℝ)..Real.pi, g θ * S n θ) =
        ∑ j ∈ Finset.range n, (a j) ^ 2 := by
    rw [show (fun θ => g θ * S n θ) =
      fun θ => ∑ j ∈ Finset.range n, g θ * (a j * e j θ) by
        funext θ
        dsimp [S]
        rw [Finset.mul_sum]]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [show (fun θ => g θ * (a j * e j θ)) =
        fun θ => a j * (g θ * e j θ) by
          funext θ
          ring]
      rw [intervalIntegral.integral_const_mul]
      dsimp [a]
      ring
    · intro j hj
      apply Continuous.intervalIntegrable
      exact hg_cont.mul (continuous_const.mul (he_cont j))
  have hse (n i : ℕ) (hi : i ∈ Finset.range n) :
      (∫ θ in (0 : ℝ)..Real.pi, e i θ * S n θ) = a i := by
    rw [show (fun θ => e i θ * S n θ) =
      fun θ => ∑ j ∈ Finset.range n, a j * (e i θ * e j θ) by
        funext θ
        dsimp [S]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring]
    rw [intervalIntegral.integral_finsetSum]
    · calc
        ∑ j ∈ Finset.range n,
            ∫ θ in (0 : ℝ)..Real.pi, a j * (e i θ * e j θ) =
          ∑ j ∈ Finset.range n, a j *
            (if i = j then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [intervalIntegral.integral_const_mul, horth]
        _ = a i := by
          rw [Finset.sum_eq_single i]
          · simp
          · intro b hb hbi
            simp [hbi.symm]
          · exact fun h => (h hi).elim
    · intro j hj
      apply Continuous.intervalIntegrable
      exact continuous_const.mul ((he_cont i).mul (he_cont j))
  have hss (n : ℕ) :
      (∫ θ in (0 : ℝ)..Real.pi, S n θ * S n θ) =
        ∑ j ∈ Finset.range n, (a j) ^ 2 := by
    rw [show (fun θ => S n θ * S n θ) =
      fun θ => ∑ i ∈ Finset.range n, a i * (e i θ * S n θ) by
        funext θ
        dsimp [S]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [intervalIntegral.integral_const_mul, hse n i hi]
      ring
    · intro i hi
      apply Continuous.intervalIntegrable
      exact continuous_const.mul ((he_cont i).mul (hS_cont n))
  have hpartial (n : ℕ) :
      ∑ j ∈ Finset.range n, (a j) ^ 2 ≤
        ∫ θ in (0 : ℝ)..Real.pi, g θ * g θ := by
    have hres :
        0 ≤ ∫ θ in (0 : ℝ)..Real.pi, (g θ - S n θ) ^ 2 := by
      apply intervalIntegral.integral_nonneg Real.pi_pos.le
      intro θ hθ
      positivity
    have hexpand :
        (∫ θ in (0 : ℝ)..Real.pi, (g θ - S n θ) ^ 2) =
        (∫ θ in (0 : ℝ)..Real.pi, g θ * g θ) -
          2 * (∫ θ in (0 : ℝ)..Real.pi, g θ * S n θ) +
          (∫ θ in (0 : ℝ)..Real.pi, S n θ * S n θ) := by
      rw [show (fun θ => (g θ - S n θ) ^ 2) =
        fun θ => g θ * g θ - 2 * (g θ * S n θ) +
          S n θ * S n θ by
            funext θ
            ring]
      rw [intervalIntegral.integral_add,
        intervalIntegral.integral_sub,
        intervalIntegral.integral_const_mul]
      all_goals apply Continuous.intervalIntegrable
      all_goals fun_prop
    rw [hexpand, hgs n, hss n] at hres
    linarith
  have hg_pointwise (θ : ℝ) :
      g θ * g θ ≤ (ℓ : ℝ) ^ 2 *
        (Real.sin θ * Real.sin θ) := by
    have hd : |deriv f (Real.cos θ)| ≤ (ℓ : ℝ) := by
      simpa only [Real.norm_eq_abs] using
        norm_deriv_le_of_lipschitz (x₀ := Real.cos θ) hf
    have hd_bounds := abs_le.mp hd
    have hd_sq :
        (deriv f (Real.cos θ)) ^ 2 ≤ (ℓ : ℝ) ^ 2 := by
      nlinarith
    have hmul := mul_nonneg (sq_nonneg (Real.sin θ))
      (sub_nonneg.mpr hd_sq)
    dsimp [g]
    nlinarith
  have hg_integral :
      (∫ θ in (0 : ℝ)..Real.pi, g θ * g θ) ≤
        Real.pi / 2 * (ℓ : ℝ) ^ 2 := by
    calc
      (∫ θ in (0 : ℝ)..Real.pi, g θ * g θ) ≤
          ∫ θ in (0 : ℝ)..Real.pi,
            (ℓ : ℝ) ^ 2 * (Real.sin θ * Real.sin θ) := by
        apply intervalIntegral.integral_mono_on
        · exact Real.pi_pos.le
        · apply Continuous.intervalIntegrable
          fun_prop
        · apply Continuous.intervalIntegrable
          fun_prop
        · intro θ hθ
          exact hg_pointwise θ
      _ = (ℓ : ℝ) ^ 2 * (Real.pi / 2) := by
        rw [intervalIntegral.integral_const_mul]
        have hone :
            (∫ θ in (0 : ℝ)..Real.pi,
              Real.sin θ * Real.sin θ) = Real.pi / 2 := by
          simpa using hsine_orth 1 1 (by omega) (by omega)
        rw [hone]
      _ = Real.pi / 2 * (ℓ : ℝ) ^ 2 := by ring
  have ha_summable : Summable (fun j => (a j) ^ 2) :=
    summable_of_sum_range_le (fun j => sq_nonneg (a j))
      (fun n => (hpartial n).trans hg_integral)
  have ha_tsum_le :
      (∑' j : ℕ, (a j) ^ 2) ≤ Real.pi / 2 * (ℓ : ℝ) ^ 2 :=
    ha_summable.tsum_le_of_sum_range_le
      (fun n => (hpartial n).trans hg_integral)
  have hshift (j : ℕ) :
      (((j + 1 : ℕ) : ℝ) *
        chebyshev_coefficient f (j + 1)) ^ 2 = (a j) ^ 2 := by
    rw [hcoeff (j + 1) (by omega)]
    have ha_eq :
        a j = κ * (∫ θ in (0 : ℝ)..Real.pi,
          g θ * Real.sin (((j + 1 : ℕ) : ℝ) * θ)) := by
      dsimp [a, e]
      rw [show (fun θ => g θ *
        (κ * Real.sin (((j + 1 : ℕ) : ℝ) * θ))) =
        fun θ => κ * (g θ *
          Real.sin (((j + 1 : ℕ) : ℝ) * θ)) by
            funext θ
            ring]
      rw [intervalIntegral.integral_const_mul]
    rw [ha_eq]
    dsimp [κ]
    ring
  have htail : Summable (fun j : ℕ =>
      (((j + 1 : ℕ) : ℝ) *
        chebyshev_coefficient f (j + 1)) ^ 2) :=
    ha_summable.congr (fun j => (hshift j).symm)
  have hsum : Summable (fun j : ℕ =>
      ((j : ℝ) * chebyshev_coefficient f j) ^ 2) :=
    (summable_nat_add_iff 1).mp
      (by simpa only [Nat.add_comm] using htail)
  refine ⟨hsum, ?_⟩
  have hdecomp := hsum.sum_add_tsum_nat_add 1
  calc
    (∑' j : ℕ, ((j : ℝ) * chebyshev_coefficient f j) ^ 2) =
        ∑' j : ℕ, (((j + 1 : ℕ) : ℝ) *
          chebyshev_coefficient f (j + 1)) ^ 2 := by
            rw [← hdecomp]
            simp
    _ = ∑' j : ℕ, (a j) ^ 2 := tsum_congr hshift
    _ ≤ Real.pi / 2 * (ℓ : ℝ) ^ 2 := ha_tsum_le

@[blueprint "def:jackson-kernel"
  (statement := /-- For \(k\in\mathbb N\), put
  \(n_k=\lfloor k/2\rfloor+1\) and define
  \[
    F_k(t)=n_k+2\sum_{r=1}^{n_k-1}(n_k-r)\cos(rt).
  \]
  The Jackson kernel of degree at most \(k\) is the normalized square
  \[
    K_k(t)=
    \frac{F_k(t)^2}
    {\displaystyle\int_{-\pi}^{\pi}F_k(u)^2\,du}.
  \]
  This definition is made for every \(k\); its normalization properties
  below require \(k\geq1\). -/)
  (title := /-- Normalized Squared-Fejér Jackson Kernel -/)
  (latexEnv := "definition")]
noncomputable def jackson_kernel (k : ℕ) (θ : ℝ) : ℝ :=
  let n : ℕ := k / 2 + 1
  let F : ℝ → ℝ := fun t =>
    (n : ℝ) + 2 * ∑ r ∈ Finset.Icc 1 (n - 1),
      ((n - r : ℕ) : ℝ) * Real.cos ((r : ℝ) * t)
  (F θ) ^ 2 /
    ∫ t in Set.Icc (-Real.pi) Real.pi, (F t) ^ 2

@[blueprint "lem:jackson-kernel-properties"
  (statement := /-- Let \(k\in\mathbb N\) satisfy \(k\geq1\). The function
  \(K_k\) from \cref{def:jackson-kernel} is continuous, nonnegative, even,
  and \(2\pi\)-periodic, and it has unit mass:
  \[
    \int_{-\pi}^{\pi}K_k(t)\,dt=1.
  \] -/)
  (proof := /-- Put \(n=\lfloor k/2\rfloor+1\) and let \(F_k\) be the finite
  cosine sum in \cref{def:jackson-kernel}. It is continuous because each
  summand is continuous, it is even because cosine is even, and it is
  \(2\pi\)-periodic because each frequency is an integer. At the origin,
  every summand is nonnegative and the constant term \(n\) is positive;
  hence \(F_k(0)>0\). Consequently, \(F_k^2\) is continuous and nonnegative
  on \([-\pi,\pi]\), and it is positive at the origin. Positivity of the
  integral of such a function gives
  \(D:=\int_{-\pi}^{\pi}F_k(t)^2\,dt>0\).

  By \cref{def:jackson-kernel}, \(K_k=F_k^2/D\). Division by the positive
  constant \(D\) preserves continuity and nonnegativity, while the evenness
  and \(2\pi\)-periodicity of \(F_k\) pass to \(K_k\). Finally, linearity of
  the integral yields
  \(\int_{-\pi}^{\pi}K_k(t)\,dt=D/D=1\). -/)
  (title := /-- Positivity and Normalization of the Jackson Kernel -/)
  (latexEnv := "lemma")]
lemma jackson_kernel_properties (k : ℕ) (hk : 0 < k) :
    Continuous (jackson_kernel k) ∧
    (∀ θ : ℝ, 0 ≤ jackson_kernel k θ) ∧
    (∫ θ in Set.Icc (-Real.pi) Real.pi, jackson_kernel k θ) = 1 ∧
    Function.Even (jackson_kernel k) ∧
    Function.Periodic (jackson_kernel k) (2 * Real.pi) := by
  let n : ℕ := k / 2 + 1
  let F : ℝ → ℝ := fun t =>
    (n : ℝ) + 2 * ∑ r ∈ Finset.Icc 1 (n - 1),
      ((n - r : ℕ) : ℝ) * Real.cos ((r : ℝ) * t)
  have hn : 0 < n := by
    dsimp [n]
    omega
  have hFcont : Continuous F := by
    dsimp [F]
    fun_prop
  have hFeven : Function.Even F := by
    intro θ
    simp [F]
  have hFperiod : Function.Periodic F (2 * Real.pi) := by
    intro θ
    dsimp [F]
    simp only [mul_add, Real.cos_add_nat_mul_two_pi]
  have hFzero : 0 < F 0 := by
    dsimp [F]
    simp only [mul_zero, Real.cos_zero, mul_one]
    positivity
  have hDpos :
      0 < ∫ t in Set.Icc (-Real.pi) Real.pi, (F t) ^ 2 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le
      (le_of_lt (neg_lt_self Real.pi_pos))]
    exact intervalIntegral.integral_pos
      (neg_lt_self Real.pi_pos)
      (hFcont.pow 2).continuousOn
      (by
        intro x hx
        positivity)
      ⟨0, by constructor <;> linarith [Real.pi_pos], by positivity⟩
  have hjackson : jackson_kernel k = fun θ =>
      (F θ) ^ 2 /
        ∫ t in Set.Icc (-Real.pi) Real.pi, (F t) ^ 2 := by
    rfl
  rw [hjackson]
  refine ⟨(hFcont.pow 2).div_const _, ?_, ?_, ?_, ?_⟩
  · intro θ
    exact div_nonneg (sq_nonneg _) hDpos.le
  · rw [MeasureTheory.integral_div]
    exact div_self hDpos.ne'
  · intro θ
    dsimp
    rw [hFeven θ]
  · intro θ
    dsimp
    rw [hFperiod θ]

@[blueprint "lem:jackson-kernel-fourier-multipliers"
  (statement := /-- Let \(k\in\mathbb N\) satisfy \(k\geq1\). There is a sequence
  \(b:\mathbb N\to\mathbb R\) with \(b_0=1\) and
  \(0\leq b_j\leq1\) for \(1\leq j\leq k\) such that
  \[
    K_k(t)=\frac1{2\pi}
      \left(1+2\sum_{j=1}^{k}b_j\cos(jt)\right)
    \qquad(t\in\mathbb R).
  \] -/)
  (proof := /-- Put \(n=\lfloor k/2\rfloor+1\), and write the cosine
  polynomial in \cref{def:jackson-kernel} as
  \(F_k(t)=\sum_{r=0}^{n-1}a_r\cos(rt)\), where \(a_0=n\) and
  \(a_r=2(n-r)\) for \(1\leq r<n\). Apply
  \(2\cos(rt)\cos(st)=\cos((r+s)t)+\cos((r-s)t)\) to every pair of
  summands. Collecting the contributions at frequencies \(r+s\) and
  \(\lvert r-s\rvert\) gives nonnegative numbers \(d_j\) such that
  \[
    F_k(t)^2=d_0+\sum_{j=1}^{k}d_j\cos(jt).
  \]
  Indeed, all contributions are nonnegative, the pair \((0,0)\) makes
  \(d_0>0\), and no frequency exceeds
  \(2(n-1)=2\lfloor k/2\rfloor\leq k\); the remaining coefficients are
  zero.

  Cosine orthogonality on \([-\pi,\pi]\) gives
  \[
    \int_{-\pi}^{\pi}F_k(t)^2\,dt=2\pi d_0,
    \qquad
    \int_{-\pi}^{\pi}F_k(t)^2\cos(jt)\,dt=\pi d_j
  \]
  for \(1\leq j\leq k\). Define \(b_0=1\) and
  \(b_j=d_j/(2d_0)\) for \(j>0\). The definition of \(K_k\) then yields
  the asserted expansion and gives \(b_j\geq0\). Orthogonality also
  identifies
  \(b_j=\int_{-\pi}^{\pi}K_k(t)\cos(jt)\,dt\). Finally, continuity,
  nonnegativity, and unit mass from
  \cref{lem:jackson-kernel-properties}, together with
  \(\cos(jt)\leq1\), imply
  \[
    b_j\leq\int_{-\pi}^{\pi}K_k(t)\,dt=1.
  \] -/)
  (title := /-- Fourier Multipliers of the Jackson Kernel -/)
  (latexEnv := "lemma")]
lemma jackson_kernel_fourier_multipliers (k : ℕ) (hk : 0 < k) :
    ∃ b : ℕ → ℝ,
      b 0 = 1 ∧
      (∀ j ∈ Finset.Icc 1 k, 0 ≤ b j ∧ b j ≤ 1) ∧
      ∀ θ : ℝ,
        jackson_kernel k θ =
          (1 / (2 * Real.pi)) *
            (1 + 2 * ∑ j ∈ Finset.Icc 1 k,
              b j * Real.cos ((j : ℝ) * θ)) := by
  classical
  let n : ℕ := k / 2 + 1
  let S : Finset ℕ := Finset.Icc 0 (n - 1)
  let a : ℕ → ℝ := fun r => if r = 0 then n else 2 * (n - r : ℕ)
  let F : ℝ → ℝ := fun θ => ∑ r ∈ S, a r * Real.cos ((r : ℝ) * θ)
  let d : ℕ →₀ ℝ := ∑ r ∈ S, ∑ s ∈ S, (
    Finsupp.single (r + s) (a r * a s / 2) +
      Finsupp.single (max r s - min r s) (a r * a s / 2))
  have hd_eval (θ : ℝ) :
      d.sum (fun j c => c * Real.cos ((j : ℝ) * θ)) = (F θ) ^ 2 := by
    let L : (ℕ →₀ ℝ) →+ ℝ :=
      { toFun := fun p => p.sum (fun j c => c * Real.cos ((j : ℝ) * θ))
        map_zero' := by simp
        map_add' := by
          intro p q
          apply Finsupp.sum_add_index'
          · intro j
            simp
          · intro j x y
            ring }
    have hL_single (j : ℕ) (c : ℝ) :
        L (Finsupp.single j c) = c * Real.cos ((j : ℝ) * θ) := by
      simp [L]
    change L d = (F θ) ^ 2
    simp only [d, map_sum, map_add, hL_single]
    calc
      (∑ r ∈ S, ∑ s ∈ S, (
          (a r * a s / 2) * Real.cos (((r + s : ℕ) : ℝ) * θ) +
            (a r * a s / 2) * Real.cos (((max r s - min r s : ℕ) : ℝ) * θ))) =
          ∑ r ∈ S, ∑ s ∈ S,
            (a r * Real.cos ((r : ℝ) * θ)) *
              (a s * Real.cos ((s : ℝ) * θ)) := by
                apply Finset.sum_congr rfl
                intro r hr
                apply Finset.sum_congr rfl
                intro s hs
                rw [show Real.cos (((max r s - min r s : ℕ) : ℝ) * θ) =
                    Real.cos (((r : ℝ) * θ) - ((s : ℝ) * θ)) by
                      rcases le_total r s with hrs | hsr
                      · rw [max_eq_right hrs, min_eq_left hrs]
                        rw [show ((s - r : ℕ) : ℝ) * θ =
                            -(((r : ℝ) * θ) - ((s : ℝ) * θ)) by
                              push_cast [hrs]
                              ring]
                        exact Real.cos_neg _
                      · rw [max_eq_left hsr, min_eq_right hsr]
                        simp only [Nat.cast_sub hsr]
                        congr 1
                        ring]
                rw [show Real.cos (((r + s : ℕ) : ℝ) * θ) =
                    Real.cos (((r : ℝ) * θ) + ((s : ℝ) * θ)) by
                      congr 1
                      push_cast
                      ring]
                calc
                  (a r * a s / 2) *
                        Real.cos (((r : ℝ) * θ) + ((s : ℝ) * θ)) +
                      (a r * a s / 2) *
                        Real.cos (((r : ℝ) * θ) - ((s : ℝ) * θ)) =
                      (a r * a s / 2) *
                        (Real.cos (((r : ℝ) * θ) - ((s : ℝ) * θ)) +
                          Real.cos (((r : ℝ) * θ) + ((s : ℝ) * θ))) := by ring
                  _ = (a r * a s / 2) *
                        (2 * Real.cos ((r : ℝ) * θ) * Real.cos ((s : ℝ) * θ)) := by
                          rw [Real.two_mul_cos_mul_cos]
                  _ = (a r * Real.cos ((r : ℝ) * θ)) *
                        (a s * Real.cos ((s : ℝ) * θ)) := by ring
      _ = (F θ) ^ 2 := by
        simp only [F, Finset.sum_mul]
        rw [← Finset.sum_mul_sum]
        ring
  have hn : 0 < n := by
    dsimp [n]
    omega
  have hS_alt : S = insert 0 (Finset.Icc 1 (n - 1)) := by
    ext r
    simp only [S, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hF (θ : ℝ) : F θ =
      (n : ℝ) + 2 * ∑ r ∈ Finset.Icc 1 (n - 1),
        ((n - r : ℕ) : ℝ) * Real.cos ((r : ℝ) * θ) := by
    dsimp [F]
    rw [hS_alt, Finset.sum_insert]
    · simp only [a, if_pos, Nat.cast_zero, zero_mul, Real.cos_zero, mul_one]
      apply congrArg ((n : ℝ) + ·)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      have hr0 : r ≠ 0 := by
        simp only [Finset.mem_Icc] at hr
        omega
      rw [if_neg hr0]
      ring
    · simp
  have ha_nonneg {r : ℕ} (hr : r ∈ S) : 0 ≤ a r := by
    dsimp [a]
    split_ifs
    · positivity
    · positivity
  have hd_nonneg (j : ℕ) : 0 ≤ d j := by
    dsimp [d]
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.add_apply,
      Finsupp.single_apply]
    apply Finset.sum_nonneg
    intro r hr
    apply Finset.sum_nonneg
    intro s hs
    have hrs : 0 ≤ a r * a s / 2 := by positivity
    split_ifs <;> positivity
  have hfrequency {r s : ℕ} (hr : r ∈ S) (hs : s ∈ S) :
      r + s ≤ k ∧ max r s - min r s ≤ k := by
    simp only [S, Finset.mem_Icc] at hr hs
    dsimp [n] at hr hs
    constructor <;> omega
  have hd_zero {j : ℕ} (hj : k < j) : d j = 0 := by
    dsimp [d]
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.add_apply,
      Finsupp.single_apply]
    apply Finset.sum_eq_zero
    intro r hr
    apply Finset.sum_eq_zero
    intro s hs
    obtain ⟨hadd, hdist⟩ := hfrequency hr hs
    have hne_add : r + s ≠ j := by omega
    have hne_dist : max r s - min r s ≠ j := by omega
    simp [hne_add, hne_dist]
  have hzero_mem : 0 ∈ S := by
    simp only [S, Finset.mem_Icc]
    omega
  let g : ℕ → ℕ → ℝ := fun r s =>
    (Finsupp.single (r + s) (a r * a s / 2) +
      Finsupp.single (max r s - min r s) (a r * a s / 2)) 0
  have hg_nonneg {r s : ℕ} (hr : r ∈ S) (hs : s ∈ S) : 0 ≤ g r s := by
    dsimp [g]
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    have hrs : 0 ≤ a r * a s / 2 := by positivity
    split_ifs <;> positivity
  have hd_apply_zero : d 0 = ∑ r ∈ S, ∑ s ∈ S, g r s := by
    dsimp [d]
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
    rfl
  have hg_zero : g 0 0 = (n : ℝ) ^ 2 := by
    simp [g, a]
    ring
  have hd_pos : 0 < d 0 := by
    rw [hd_apply_zero]
    calc
      0 < g 0 0 := by rw [hg_zero]; positivity
      _ ≤ ∑ s ∈ S, g 0 s := by
        apply Finset.single_le_sum
        · intro s hs
          exact hg_nonneg hzero_mem hs
        · exact hzero_mem
      _ ≤ ∑ r ∈ S, ∑ s ∈ S, g r s := by
        exact Finset.single_le_sum (s := S)
          (f := fun r => ∑ s ∈ S, g r s)
          (fun r hr => Finset.sum_nonneg fun s hs => hg_nonneg hr hs) hzero_mem
  have hsupport : d.support ⊆ Finset.Icc 0 k := by
    intro j hj
    simp only [Finset.mem_Icc, Nat.zero_le, true_and]
    by_contra hjk
    have hkj : k < j := by omega
    exact (Finsupp.mem_support_iff.mp hj) (hd_zero hkj)
  have hd_sum (θ : ℝ) :
      d.sum (fun j c => c * Real.cos ((j : ℝ) * θ)) =
        ∑ j ∈ Finset.Icc 0 k, d j * Real.cos ((j : ℝ) * θ) := by
    change (∑ j ∈ d.support, d j * Real.cos ((j : ℝ) * θ)) = _
    apply Finset.sum_subset hsupport
    intro j hjIcc hjnot
    have hdj : d j = 0 := Finsupp.notMem_support_iff.mp hjnot
    simp [hdj]
  have hIcc_zero : Finset.Icc 0 k = insert 0 (Finset.Icc 1 k) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hd_expansion (θ : ℝ) :
      (F θ) ^ 2 = d 0 + ∑ j ∈ Finset.Icc 1 k,
        d j * Real.cos ((j : ℝ) * θ) := by
    rw [← hd_eval, hd_sum, hIcc_zero, Finset.sum_insert]
    · norm_num
    · simp
  have hcos_integral {j : ℕ} (hj : 0 < j) :
      (∫ t in Set.Icc (-Real.pi) Real.pi,
        Real.cos ((j : ℝ) * t)) = 0 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    have hjR : (j : ℝ) ≠ 0 := by positivity
    rw [show (∫ t in (-Real.pi)..Real.pi, Real.cos ((j : ℝ) * t)) =
        (1 / (j : ℝ)) * Real.sin ((j : ℝ) * Real.pi) -
          (1 / (j : ℝ)) * Real.sin ((j : ℝ) * (-Real.pi)) by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun x => (1 / (j : ℝ)) * Real.sin ((j : ℝ) * x))
        (f' := fun x => Real.cos ((j : ℝ) * x))
      · intro x hx
        convert (((Real.hasDerivAt_sin ((j : ℝ) * x)).comp x
          ((hasDerivAt_id x).const_mul (j : ℝ))).const_mul (1 / (j : ℝ))) using 1
        · rfl
        · rfl
        · field_simp
      · exact (by fun_prop : Continuous (fun x : ℝ =>
          Real.cos ((j : ℝ) * x))).intervalIntegrable _ _]
    rw [show Real.sin ((j : ℝ) * Real.pi) = 0 by
      simpa only [Nat.cast_ofNat] using Real.sin_nat_mul_pi j]
    rw [show Real.sin ((j : ℝ) * (-Real.pi)) = 0 by
      rw [mul_neg, Real.sin_neg]
      simp]
    simp
  have hconst_integral :
      (∫ _t in Set.Icc (-Real.pi) Real.pi, (1 : ℝ)) = 2 * Real.pi := by
    simp [Real.volume_Icc]
    rw [max_eq_left]
    · ring
    · positivity
  have hcos_product {j l : ℕ} (hj : 0 < j) (hl : 0 < l) :
      (∫ t in Set.Icc (-Real.pi) Real.pi,
        Real.cos ((j : ℝ) * t) * Real.cos ((l : ℝ) * t)) =
          if j = l then Real.pi else 0 := by
    have hoff {p q : ℕ} (hpq : p < q) :
        (∫ t in Set.Icc (-Real.pi) Real.pi,
          Real.cos ((p : ℝ) * t) * Real.cos ((q : ℝ) * t)) = 0 := by
      have hdiff : 0 < q - p := by omega
      have hsum : 0 < p + q := by omega
      have hpoint (t : ℝ) :
          2 * (Real.cos ((p : ℝ) * t) * Real.cos ((q : ℝ) * t)) =
            Real.cos (((q - p : ℕ) : ℝ) * t) +
              Real.cos (((p + q : ℕ) : ℝ) * t) := by
        rw [show Real.cos (((q - p : ℕ) : ℝ) * t) =
            Real.cos (((p : ℝ) * t) - ((q : ℝ) * t)) by
          rw [Nat.cast_sub (le_of_lt hpq)]
          rw [show (((q : ℝ) - (p : ℝ)) * t) =
              -(((p : ℝ) * t) - ((q : ℝ) * t)) by ring]
          exact Real.cos_neg _]
        rw [show Real.cos (((p + q : ℕ) : ℝ) * t) =
            Real.cos (((p : ℝ) * t) + ((q : ℝ) * t)) by
          congr 1
          push_cast
          ring]
        simpa only [mul_assoc] using
          Real.two_mul_cos_mul_cos ((p : ℝ) * t) ((q : ℝ) * t)
      have hint_diff : MeasureTheory.IntegrableOn
          (fun t : ℝ => Real.cos (((q - p : ℕ) : ℝ) * t))
          (Set.Icc (-Real.pi) Real.pi) := (by fun_prop : Continuous
            (fun t : ℝ => Real.cos (((q - p : ℕ) : ℝ) * t))).integrableOn_Icc
      have hint_sum : MeasureTheory.IntegrableOn
          (fun t : ℝ => Real.cos (((p + q : ℕ) : ℝ) * t))
          (Set.Icc (-Real.pi) Real.pi) := (by fun_prop : Continuous
            (fun t : ℝ => Real.cos (((p + q : ℕ) : ℝ) * t))).integrableOn_Icc
      calc
        (∫ t in Set.Icc (-Real.pi) Real.pi,
            Real.cos ((p : ℝ) * t) * Real.cos ((q : ℝ) * t)) =
            (1 / 2 : ℝ) * ∫ t in Set.Icc (-Real.pi) Real.pi,
              2 * (Real.cos ((p : ℝ) * t) * Real.cos ((q : ℝ) * t)) := by
                rw [MeasureTheory.integral_const_mul]
                ring
        _ = (1 / 2 : ℝ) * ∫ t in Set.Icc (-Real.pi) Real.pi,
              (Real.cos (((q - p : ℕ) : ℝ) * t) +
                Real.cos (((p + q : ℕ) : ℝ) * t)) := by
                congr 2
                funext t
                exact hpoint t
        _ = 0 := by
          rw [MeasureTheory.integral_add hint_diff hint_sum]
          rw [hcos_integral hdiff, hcos_integral hsum]
          ring
    by_cases hjl : j = l
    · subst l
      simp only [↓reduceIte]
      have hdouble : 0 < j + j := by omega
      have hint_one : MeasureTheory.IntegrableOn (fun _t : ℝ => (1 : ℝ))
          (Set.Icc (-Real.pi) Real.pi) := (by fun_prop : Continuous
            (fun _t : ℝ => (1 : ℝ))).integrableOn_Icc
      have hint_double : MeasureTheory.IntegrableOn
          (fun t : ℝ => Real.cos (((j + j : ℕ) : ℝ) * t))
          (Set.Icc (-Real.pi) Real.pi) := (by fun_prop : Continuous
            (fun t : ℝ => Real.cos (((j + j : ℕ) : ℝ) * t))).integrableOn_Icc
      calc
        (∫ t in Set.Icc (-Real.pi) Real.pi,
            Real.cos ((j : ℝ) * t) * Real.cos ((j : ℝ) * t)) =
            (1 / 2 : ℝ) * ∫ t in Set.Icc (-Real.pi) Real.pi,
              2 * (Real.cos ((j : ℝ) * t) * Real.cos ((j : ℝ) * t)) := by
                rw [MeasureTheory.integral_const_mul]
                ring
        _ =
            (1 / 2 : ℝ) * ∫ t in Set.Icc (-Real.pi) Real.pi,
              (1 + Real.cos (((j + j : ℕ) : ℝ) * t)) := by
                congr 2
                funext t
                rw [show Real.cos (((j + j : ℕ) : ℝ) * t) =
                    Real.cos (2 * ((j : ℝ) * t)) by
                      congr 1
                      push_cast
                      ring]
                rw [Real.cos_two_mul]
                ring
        _ = Real.pi := by
          rw [MeasureTheory.integral_add hint_one hint_double]
          rw [hconst_integral, hcos_integral hdouble]
          ring
    · simp only [hjl, ↓reduceIte]
      rcases lt_or_gt_of_ne hjl with hjlt | hljt
      · exact hoff hjlt
      · simpa only [mul_comm] using hoff hljt
  let D : ℝ := ∫ t in Set.Icc (-Real.pi) Real.pi, (F t) ^ 2
  have hterm_integrable (j : ℕ) : MeasureTheory.IntegrableOn
      (fun t : ℝ => d j * Real.cos ((j : ℝ) * t))
      (Set.Icc (-Real.pi) Real.pi) := (by fun_prop : Continuous
        (fun t : ℝ => d j * Real.cos ((j : ℝ) * t))).integrableOn_Icc
  have hsum_integrable : MeasureTheory.IntegrableOn
      (fun t : ℝ => ∑ j ∈ Finset.Icc 1 k,
        d j * Real.cos ((j : ℝ) * t))
      (Set.Icc (-Real.pi) Real.pi) := (by fun_prop : Continuous
        (fun t : ℝ => ∑ j ∈ Finset.Icc 1 k,
          d j * Real.cos ((j : ℝ) * t))).integrableOn_Icc
  have hconst_d_integrable : MeasureTheory.IntegrableOn (fun _t : ℝ => d 0)
      (Set.Icc (-Real.pi) Real.pi) := (by fun_prop : Continuous
        (fun _t : ℝ => d 0)).integrableOn_Icc
  have hD : D = 2 * Real.pi * d 0 := by
    dsimp [D]
    simp_rw [hd_expansion]
    rw [MeasureTheory.integral_add hconst_d_integrable hsum_integrable]
    have hconst_d :
        (∫ _t in Set.Icc (-Real.pi) Real.pi, d 0) = d 0 * (2 * Real.pi) := by
      rw [show d 0 = d 0 * (1 : ℝ) by ring]
      rw [MeasureTheory.integral_const_mul, hconst_integral]
      ring
    rw [hconst_d]
    rw [MeasureTheory.integral_finsetSum]
    · have hzero_terms : (∑ j ∈ Finset.Icc 1 k,
          ∫ t in Set.Icc (-Real.pi) Real.pi,
            d j * Real.cos ((j : ℝ) * t)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        simp only [Finset.mem_Icc] at hj
        rw [MeasureTheory.integral_const_mul, hcos_integral hj.1]
        ring
      rw [hzero_terms]
      ring
    · intro j hj
      exact hterm_integrable j
  have hD_pos : 0 < D := by
    rw [hD]
    positivity
  have hkernel (θ : ℝ) : jackson_kernel k θ = (F θ) ^ 2 / D := by
    dsimp only [jackson_kernel]
    rw [show ((k / 2 + 1 : ℕ) : ℝ) +
          2 * ∑ r ∈ Finset.Icc 1 (k / 2 + 1 - 1),
            ((k / 2 + 1 - r : ℕ) : ℝ) * Real.cos ((r : ℝ) * θ) = F θ by
      simpa only [n] using (hF θ).symm]
    congr 1
    dsimp [D]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with t
    rw [show ((k / 2 + 1 : ℕ) : ℝ) +
          2 * ∑ r ∈ Finset.Icc 1 (k / 2),
            ((k / 2 + 1 - r : ℕ) : ℝ) * Real.cos ((r : ℝ) * t) = F t by
      simpa only [n, Nat.add_sub_cancel] using (hF t).symm]
  let b : ℕ → ℝ := fun j => if j = 0 then 1 else d j / (2 * d 0)
  have hb_zero : b 0 = 1 := by simp [b]
  have hb_formula {j : ℕ} (hj : 0 < j) : b j = d j / (2 * d 0) := by
    simp [b, ne_of_gt hj]
  have hK_expansion (θ : ℝ) : jackson_kernel k θ =
      (1 / (2 * Real.pi)) *
        (1 + 2 * ∑ j ∈ Finset.Icc 1 k,
          b j * Real.cos ((j : ℝ) * θ)) := by
    rw [hkernel, hD, hd_expansion]
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hd0 : d 0 ≠ 0 := ne_of_gt hd_pos
    field_simp
    rw [mul_add, mul_one, Finset.mul_sum]
    rw [Finset.mul_sum]
    apply congrArg (d 0 + ·)
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_Icc] at hj
    rw [hb_formula hj.1]
    field_simp
  have hraw_coefficient {j : ℕ} (hj : j ∈ Finset.Icc 1 k) :
      (∫ t in Set.Icc (-Real.pi) Real.pi,
        (F t) ^ 2 * Real.cos ((j : ℝ) * t)) = Real.pi * d j := by
    have hjpos : 0 < j := (Finset.mem_Icc.mp hj).1
    have hconst_prod : MeasureTheory.IntegrableOn
        (fun t : ℝ => d 0 * Real.cos ((j : ℝ) * t))
        (Set.Icc (-Real.pi) Real.pi) := (by fun_prop : Continuous
          (fun t : ℝ => d 0 * Real.cos ((j : ℝ) * t))).integrableOn_Icc
    have hprod_term (l : ℕ) : MeasureTheory.IntegrableOn
        (fun t : ℝ => d l * Real.cos ((l : ℝ) * t) *
          Real.cos ((j : ℝ) * t))
        (Set.Icc (-Real.pi) Real.pi) := (by fun_prop : Continuous
          (fun t : ℝ => d l * Real.cos ((l : ℝ) * t) *
            Real.cos ((j : ℝ) * t))).integrableOn_Icc
    have hprod_sum : MeasureTheory.IntegrableOn
        (fun t : ℝ => ∑ l ∈ Finset.Icc 1 k,
          d l * Real.cos ((l : ℝ) * t) * Real.cos ((j : ℝ) * t))
        (Set.Icc (-Real.pi) Real.pi) := (by fun_prop : Continuous
          (fun t : ℝ => ∑ l ∈ Finset.Icc 1 k,
            d l * Real.cos ((l : ℝ) * t) *
              Real.cos ((j : ℝ) * t))).integrableOn_Icc
    simp_rw [hd_expansion, add_mul, Finset.sum_mul]
    rw [MeasureTheory.integral_add hconst_prod hprod_sum]
    rw [MeasureTheory.integral_const_mul, hcos_integral hjpos]
    simp only [mul_zero, zero_add]
    rw [MeasureTheory.integral_finsetSum]
    · calc
        (∑ l ∈ Finset.Icc 1 k,
            ∫ t in Set.Icc (-Real.pi) Real.pi,
              d l * Real.cos ((l : ℝ) * t) * Real.cos ((j : ℝ) * t)) =
            ∑ l ∈ Finset.Icc 1 k,
              d l * (if l = j then Real.pi else 0) := by
                apply Finset.sum_congr rfl
                intro l hl
                rw [show (fun t : ℝ =>
                    d l * Real.cos ((l : ℝ) * t) * Real.cos ((j : ℝ) * t)) =
                    fun t : ℝ => d l * (Real.cos ((l : ℝ) * t) *
                      Real.cos ((j : ℝ) * t)) by
                        funext t
                        ring]
                rw [MeasureTheory.integral_const_mul]
                rw [hcos_product (Finset.mem_Icc.mp hl).1 hjpos]
        _ = Real.pi * d j := by
          rw [Finset.sum_eq_single j]
          · simp
            ring
          · intro l hl hlj
            simp [hlj]
          · exact fun hnot => (hnot hj).elim
    · intro l hl
      exact hprod_term l
  have hkernel_coefficient {j : ℕ} (hj : j ∈ Finset.Icc 1 k) :
      (∫ t in Set.Icc (-Real.pi) Real.pi,
        jackson_kernel k t * Real.cos ((j : ℝ) * t)) = b j := by
    simp_rw [hkernel]
    have hrewrite (t : ℝ) :
        F t ^ 2 / D * Real.cos ((j : ℝ) * t) =
          (1 / D) * (F t ^ 2 * Real.cos ((j : ℝ) * t)) := by ring
    simp_rw [hrewrite]
    rw [MeasureTheory.integral_const_mul, hraw_coefficient hj, hD]
    rw [hb_formula (Finset.mem_Icc.mp hj).1]
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hd0 : d 0 ≠ 0 := ne_of_gt hd_pos
    field_simp
  obtain ⟨hK_cont, hK_nonneg, hK_mass, _, _⟩ := jackson_kernel_properties k hk
  refine ⟨b, hb_zero, ?_, hK_expansion⟩
  intro j hj
  constructor
  · rw [hb_formula (Finset.mem_Icc.mp hj).1]
    exact div_nonneg (hd_nonneg j) (by positivity)
  · rw [← hkernel_coefficient hj, ← hK_mass]
    have hintK : MeasureTheory.IntegrableOn (jackson_kernel k)
        (Set.Icc (-Real.pi) Real.pi) := hK_cont.integrableOn_Icc
    have hintProd : MeasureTheory.IntegrableOn
        (fun t : ℝ => jackson_kernel k t * Real.cos ((j : ℝ) * t))
        (Set.Icc (-Real.pi) Real.pi) := (hK_cont.mul (by fun_prop)).integrableOn_Icc
    apply MeasureTheory.setIntegral_mono_on hintProd hintK measurableSet_Icc
    intro t ht
    nlinarith [hK_nonneg t, Real.neg_one_le_cos ((j : ℝ) * t),
      Real.cos_le_one ((j : ℝ) * t)]

@[blueprint "lem:jackson-convolution-expansion"
  (statement := /-- Let \(f:\mathbb R\to\mathbb R\) be continuous and
  let \(k\geq1\). There is a sequence \(b:\mathbb N\to\mathbb R\)
  with \(b_0=1\) and \(0\leq b_j\leq1\) for \(1\leq j\leq k\) such
  that, for every \(\theta\in\mathbb R\),
  \[
    \int_{-\pi}^{\pi}K_k(t)f(\cos(\theta-t))\,dt
      =J_{k,b}f(\cos\theta).
  \] -/)
  (proof := /-- Choose \(b\) from
  \cref{lem:jackson-kernel-fourier-multipliers}, and put
  \(h(u)=f(\cos u)\). Continuity of \(f\) makes all the integrands below
  integrable, while \(h\) is even and \(2\pi\)-periodic. Translation
  invariance of the integral over one period, the substitution
  \(u=\theta-t\), and the cosine subtraction formula give, for every
  \(j\geq1\),
  \[
    \int_{-\pi}^{\pi}\cos(jt)h(\theta-t)\,dt
      =2\cos(j\theta)\int_0^\pi h(u)\cos(ju)\,du.
  \]
  Indeed, the cosine product is even and the corresponding sine product
  is odd, so its integral on \([-\pi,\pi]\) vanishes. The same argument
  at frequency zero gives
  \(\int_{-\pi}^{\pi}h(\theta-t)\,dt=2\int_0^\pi h(u)\,du\).

  By \cref{def:chebyshev-coefficient}, the change of variables
  \(x=\cos u\), and \(T_j(\cos u)=\cos(ju)\), the normalization in
  \cref{def:normalized-chebyshev-first} yields
  \[
    c_0(f)\mathcal T_0(\cos\theta)
      =\frac1\pi\int_0^\pi h(u)\,du,
    \qquad
    c_j(f)\mathcal T_j(\cos\theta)
      =\frac2\pi\cos(j\theta)\int_0^\pi h(u)\cos(ju)\,du
  \]
  for \(j\geq1\). Insert the finite cosine expansion from
  \cref{lem:jackson-kernel-fourier-multipliers} into the convolution and
  use finite-sum linearity. The frequency-zero identity and the identities
  above identify every resulting term with
  \(b_jc_j(f)\mathcal T_j(\cos\theta)\). Their sum is
  \cref{def:damped-chebyshev-approximation}, proving the claim. -/)
  (title := /-- Jackson Convolution as a Damped Chebyshev Expansion -/)
  (latexEnv := "lemma")]
lemma jackson_convolution_expansion
    (f : ℝ → ℝ) (hf : Continuous f) (k : ℕ) (hk : 0 < k) :
    ∃ b : ℕ → ℝ,
      b 0 = 1 ∧
      (∀ j ∈ Finset.Icc 1 k, 0 ≤ b j ∧ b j ≤ 1) ∧
      ∀ θ : ℝ,
        (∫ t in Set.Icc (-Real.pi) Real.pi,
          jackson_kernel k t * f (Real.cos (θ - t))) =
            damped_chebyshev_approximation f k b (Real.cos θ) := by
  obtain ⟨b, hb_zero, hb_bounds, hkernel⟩ :=
    jackson_kernel_fourier_multipliers k hk
  refine ⟨b, hb_zero, hb_bounds, ?_⟩
  intro θ
  let g : ℝ → ℝ := fun u => f (Real.cos u)
  have hg_cont : Continuous g := by
    dsimp [g]
    fun_prop
  have hg_periodic : Function.Periodic g (2 * Real.pi) := by
    intro u
    dsimp [g]
    rw [show u + 2 * Real.pi = u + (1 : ℤ) * (2 * Real.pi) by norm_num]
    rw [Real.cos_add_int_mul_two_pi]
  have hg_even (u : ℝ) : g (-u) = g u := by
    simp [g]
  have hsymmetric_even (q : ℝ → ℝ) (hq : Continuous q)
      (hq_even : ∀ u : ℝ, q (-u) = q u) :
      (∫ u in -Real.pi..Real.pi, q u) =
        2 * ∫ u in (0 : ℝ)..Real.pi, q u := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hq.intervalIntegrable (-Real.pi) 0)
      (hq.intervalIntegrable 0 Real.pi)]
    have hneg : (∫ u in -Real.pi..(0 : ℝ), q u) =
        ∫ u in (0 : ℝ)..Real.pi, q (-u) := by
      symm
      simpa using (intervalIntegral.integral_comp_neg
        (f := q) (a := (0 : ℝ)) (b := Real.pi))
    rw [hneg]
    simp_rw [hq_even]
    ring
  have hsymmetric_odd (q : ℝ → ℝ) (hq : Continuous q)
      (hq_odd : ∀ u : ℝ, q (-u) = -q u) :
      (∫ u in -Real.pi..Real.pi, q u) = 0 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hq.intervalIntegrable (-Real.pi) 0)
      (hq.intervalIntegrable 0 Real.pi)]
    have hneg : (∫ u in -Real.pi..(0 : ℝ), q u) =
        ∫ u in (0 : ℝ)..Real.pi, q (-u) := by
      symm
      simpa using (intervalIntegral.integral_comp_neg
        (f := q) (a := (0 : ℝ)) (b := Real.pi))
    rw [hneg]
    simp_rw [hq_odd]
    rw [intervalIntegral.integral_neg]
    ring
  have hcos_periodic (j : ℕ) :
      Function.Periodic (fun u : ℝ => Real.cos ((j : ℝ) * u))
        (2 * Real.pi) := by
    intro u
    convert Real.cos_add_int_mul_two_pi ((j : ℝ) * u) (j : ℤ) using 1 <;>
      push_cast <;> ring_nf
  have hsin_periodic (j : ℕ) :
      Function.Periodic (fun u : ℝ => Real.sin ((j : ℝ) * u))
        (2 * Real.pi) := by
    intro u
    convert Real.sin_add_int_mul_two_pi ((j : ℝ) * u) (j : ℤ) using 1 <;>
      push_cast <;> ring_nf
  have hfull_period (q : ℝ → ℝ)
      (hq : Function.Periodic q (2 * Real.pi)) :
      (∫ u in θ - Real.pi..θ + Real.pi, q u) =
        ∫ u in -Real.pi..Real.pi, q u := by
    convert hq.intervalIntegral_add_eq (θ - Real.pi) (-Real.pi) using 1 <;>
      ring_nf
  have hconvolution_one :
      (∫ t in -Real.pi..Real.pi, g (θ - t)) =
        2 * ∫ u in (0 : ℝ)..Real.pi, g u := by
    rw [intervalIntegral.integral_comp_sub_left]
    rw [show θ - -Real.pi = θ + Real.pi by ring]
    rw [hfull_period g hg_periodic]
    exact hsymmetric_even g hg_cont hg_even
  have hconvolution_cos (j : ℕ) :
      (∫ t in -Real.pi..Real.pi,
          Real.cos ((j : ℝ) * t) * g (θ - t)) =
        2 * Real.cos ((j : ℝ) * θ) *
          ∫ u in (0 : ℝ)..Real.pi,
            Real.cos ((j : ℝ) * u) * g u := by
    let qc : ℝ → ℝ := fun u => Real.cos ((j : ℝ) * u) * g u
    let qs : ℝ → ℝ := fun u => Real.sin ((j : ℝ) * u) * g u
    have hqc_cont : Continuous qc := by
      dsimp [qc]
      fun_prop
    have hqs_cont : Continuous qs := by
      dsimp [qs]
      fun_prop
    have hqc_periodic : Function.Periodic qc (2 * Real.pi) :=
      (hcos_periodic j).mul hg_periodic
    have hqs_periodic : Function.Periodic qs (2 * Real.pi) :=
      (hsin_periodic j).mul hg_periodic
    have hqc_even (u : ℝ) : qc (-u) = qc u := by
      simp [qc, hg_even]
    have hqs_odd (u : ℝ) : qs (-u) = -qs u := by
      simp [qs, hg_even]
    rw [show (fun t : ℝ => Real.cos ((j : ℝ) * t) * g (θ - t)) =
        fun t => (fun u : ℝ =>
          Real.cos ((j : ℝ) * (θ - u)) * g u) (θ - t) by
      funext t
      congr 2 <;> ring]
    have hsub := intervalIntegral.integral_comp_sub_left
      (f := fun u : ℝ => Real.cos ((j : ℝ) * (θ - u)) * g u)
      (d := θ) (a := -Real.pi) (b := Real.pi)
    rw [hsub]
    rw [show θ - -Real.pi = θ + Real.pi by ring]
    simp_rw [show ∀ u : ℝ, (j : ℝ) * (θ - u) =
        (j : ℝ) * θ - (j : ℝ) * u by intro u; ring, Real.cos_sub]
    rw [show (fun u : ℝ =>
        (Real.cos ((j : ℝ) * θ) * Real.cos ((j : ℝ) * u) +
          Real.sin ((j : ℝ) * θ) * Real.sin ((j : ℝ) * u)) * g u) =
        fun u => Real.cos ((j : ℝ) * θ) * qc u +
          Real.sin ((j : ℝ) * θ) * qs u by
      funext u
      simp [qc, qs]
      ring]
    rw [intervalIntegral.integral_add
      ((hqc_cont.const_mul _).intervalIntegrable
        (θ - Real.pi) (θ + Real.pi))
      ((hqs_cont.const_mul _).intervalIntegrable
        (θ - Real.pi) (θ + Real.pi))]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    rw [hfull_period qc hqc_periodic, hfull_period qs hqs_periodic]
    rw [hsymmetric_even qc hqc_cont hqc_even,
      hsymmetric_odd qs hqs_cont hqs_odd]
    dsimp [qc]
    ring
  have hzero :
      b 0 * chebyshev_coefficient f 0 *
          normalized_chebyshev_first 0 (Real.cos θ) =
        (1 / (2 * Real.pi)) *
          (2 * ∫ u in (0 : ℝ)..Real.pi, g u) := by
    rw [hb_zero]
    rw [chebyshev_coefficient,
      Polynomial.Chebyshev.integral_measureT_eq_integral_cos]
    simp only [normalized_chebyshev_first, if_pos, chebyshev_first,
      Polynomial.Chebyshev.T_real_cos, Int.cast_zero, Nat.cast_zero, zero_mul,
      Real.cos_zero, one_mul]
    rw [← intervalIntegral.integral_mul_const]
    have hsqrt : Real.sqrt Real.pi ^ 2 = Real.pi :=
      Real.sq_sqrt Real.pi_pos.le
    have hsqrt_ne : Real.sqrt Real.pi ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
    dsimp [g]
    rw [show (fun x : ℝ =>
        f (Real.cos x) * (1 / Real.sqrt Real.pi) *
          (1 / Real.sqrt Real.pi)) =
        fun x => (1 / Real.sqrt Real.pi ^ 2) * f (Real.cos x) by
      funext x
      ring]
    rw [intervalIntegral.integral_const_mul, hsqrt]
    field_simp
  have hpositive (j : ℕ) (hj : 0 < j) :
      b j * chebyshev_coefficient f j *
          normalized_chebyshev_first j (Real.cos θ) =
        (1 / (2 * Real.pi)) *
          (2 * b j * (2 * Real.cos ((j : ℝ) * θ) *
            ∫ u in (0 : ℝ)..Real.pi,
              Real.cos ((j : ℝ) * u) * g u)) := by
    rw [chebyshev_coefficient,
      Polynomial.Chebyshev.integral_measureT_eq_integral_cos]
    simp only [normalized_chebyshev_first, if_neg hj.ne',
      chebyshev_first, Polynomial.Chebyshev.T_real_cos, Int.cast_natCast]
    simp only [Real.sqrt_div (by positivity : (0 : ℝ) ≤ Real.pi),
      show (2 : ℝ) ≠ 0 by norm_num]
    have hnorm_sq :
        (Real.sqrt Real.pi / Real.sqrt 2) ^ 2 = Real.pi / 2 := by
      rw [div_pow, Real.sq_sqrt Real.pi_pos.le,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hnorm_ne : Real.sqrt Real.pi / Real.sqrt 2 ≠ 0 := by
      positivity
    rw [show (fun u : ℝ =>
        f (Real.cos u) *
          (Real.cos ((j : ℝ) * u) /
            (Real.sqrt Real.pi / Real.sqrt 2))) =
        fun u => (1 / (Real.sqrt Real.pi / Real.sqrt 2)) *
          (Real.cos ((j : ℝ) * u) * g u) by
      funext u
      dsimp [g]
      ring]
    rw [intervalIntegral.integral_const_mul]
    field_simp
    rw [Real.sq_sqrt Real.pi_pos.le,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hleft :
      (∫ t in Set.Icc (-Real.pi) Real.pi,
          jackson_kernel k t * f (Real.cos (θ - t))) =
        (1 / (2 * Real.pi)) *
            (2 * ∫ u in (0 : ℝ)..Real.pi, g u) +
          ∑ j ∈ Finset.Icc 1 k,
            (1 / (2 * Real.pi)) *
              (2 * b j * (2 * Real.cos ((j : ℝ) * θ) *
                ∫ u in (0 : ℝ)..Real.pi,
                  Real.cos ((j : ℝ) * u) * g u)) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (by
      linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    simp_rw [hkernel]
    change (∫ t in -Real.pi..Real.pi,
      (1 / (2 * Real.pi) *
        (1 + 2 * ∑ j ∈ Finset.Icc 1 k,
          b j * Real.cos ((j : ℝ) * t))) * g (θ - t)) = _
    rw [show (fun t : ℝ =>
        (1 / (2 * Real.pi) *
          (1 + 2 * ∑ j ∈ Finset.Icc 1 k,
            b j * Real.cos ((j : ℝ) * t))) * g (θ - t)) =
        fun t => (1 / (2 * Real.pi)) * g (θ - t) +
          ∑ j ∈ Finset.Icc 1 k,
            ((1 / (2 * Real.pi)) * (2 * b j)) *
              (Real.cos ((j : ℝ) * t) * g (θ - t)) by
      funext t
      calc
        (1 / (2 * Real.pi) *
            (1 + 2 * ∑ j ∈ Finset.Icc 1 k,
              b j * Real.cos ((j : ℝ) * t))) * g (θ - t) =
            (1 / (2 * Real.pi)) * g (θ - t) +
              (1 / (2 * Real.pi)) *
                (2 * ∑ j ∈ Finset.Icc 1 k,
                  b j * Real.cos ((j : ℝ) * t)) * g (θ - t) := by ring
        _ = _ := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          apply congrArg₂ (· + ·) rfl
          apply Finset.sum_congr rfl
          intro j hj
          ring]
    rw [intervalIntegral.integral_add
      ((by fun_prop : Continuous (fun t : ℝ =>
        (1 / (2 * Real.pi)) * g (θ - t))).intervalIntegrable
          (-Real.pi) Real.pi)
      ((by fun_prop : Continuous (fun t : ℝ =>
        ∑ j ∈ Finset.Icc 1 k,
          ((1 / (2 * Real.pi)) * (2 * b j)) *
            (Real.cos ((j : ℝ) * t) * g (θ - t)))).intervalIntegrable
              (-Real.pi) Real.pi)]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_finsetSum (fun j hj =>
      (by fun_prop : Continuous (fun t : ℝ =>
        ((1 / (2 * Real.pi)) * (2 * b j)) *
          (Real.cos ((j : ℝ) * t) * g (θ - t)))).intervalIntegrable
            (-Real.pi) Real.pi)]
    simp_rw [intervalIntegral.integral_const_mul, hconvolution_one,
      hconvolution_cos]
    apply congrArg₂ (· + ·) rfl
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hleft]
  rw [damped_chebyshev_approximation]
  have herase : (Finset.range (k + 1)).erase 0 = Finset.Icc 1 k := by
    ext j
    simp
    omega
  have hsplit :
      (∑ j ∈ Finset.range (k + 1),
        b j * chebyshev_coefficient f j *
          normalized_chebyshev_first j (Real.cos θ)) =
        b 0 * chebyshev_coefficient f 0 *
            normalized_chebyshev_first 0 (Real.cos θ) +
          ∑ j ∈ Finset.Icc 1 k,
            b j * chebyshev_coefficient f j *
              normalized_chebyshev_first j (Real.cos θ) := by
    rw [← herase]
    exact (Finset.add_sum_erase (Finset.range (k + 1)) _ (by simp)).symm
  rw [hsplit, hzero]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro j hj
  exact (hpositive j (Finset.mem_Icc.mp hj).1).symm

@[blueprint "lem:jackson-fejer-cosine-identity"
  (statement := /-- For every \(n\in\mathbb N\) and \(\theta\in\mathbb R\),
  the finite cosine polynomial occurring in the Jackson kernel satisfies
  \[
    (1-\cos\theta)
    \left(n+2\sum_{r=1}^{n-1}(n-r)\cos(r\theta)\right)
    =1-\cos(n\theta).
  \] -/)
  (proof := /-- Write the polynomial of order \(n+1\) as the polynomial
  of order \(n\) plus the Dirichlet sum
  \(1+2\sum_{r=1}^{n}\cos(r\theta)\). Multiplication of this Dirichlet
  sum by \(1-\cos\theta\), followed by
  \[
    2\cos\theta\cos(r\theta)
      =\cos((r+1)\theta)+\cos((r-1)\theta),
  \]
  telescopes to
  \(\cos(n\theta)-\cos((n+1)\theta)\). Induction on \(n\) now gives
  the displayed identity. -/)
  (title := /-- Fejér Cosine Identity -/)
  (latexEnv := "lemma")]
lemma jackson_fejer_cosine_identity (n : ℕ) (θ : ℝ) :
    (1 - Real.cos θ) *
      ((n : ℝ) + 2 * ∑ r ∈ Finset.Icc 1 (n - 1),
        ((n - r : ℕ) : ℝ) * Real.cos ((r : ℝ) * θ)) =
      1 - Real.cos ((n : ℝ) * θ) := by
  let F : ℕ → ℝ := fun m =>
    (m : ℝ) + 2 * ∑ r ∈ Finset.Icc 1 (m - 1),
      ((m - r : ℕ) : ℝ) * Real.cos ((r : ℝ) * θ)
  let D : ℕ → ℝ := fun m =>
    1 + 2 * ∑ r ∈ Finset.Icc 1 m, Real.cos ((r : ℝ) * θ)
  have hF : ∀ m : ℕ, F (m + 1) = F m + D m := by
    intro m
    rcases m with _ | m
    · simp [F, D]
    · simp only [F, D, Nat.succ_eq_add_one]
      rw [show m + 1 + 1 - 1 = m + 1 by omega]
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [show m + 1 - 1 = m by omega]
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hsum :
          ∑ r ∈ Finset.Icc 1 m,
              (((m + 1 + 1 - r : ℕ) : ℝ) *
                Real.cos ((r : ℝ) * θ)) =
            ∑ r ∈ Finset.Icc 1 m,
              ((((m + 1 - r : ℕ) : ℝ) + 1) *
                Real.cos ((r : ℝ) * θ)) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrle : r ≤ m := (Finset.mem_Icc.mp hr).2
        have heq : m + 1 + 1 - r = (m + 1 - r) + 1 := by omega
        rw [heq]
        norm_num
      rw [hsum]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      have heq : m + 1 + 1 - (m + 1) = 1 := by omega
      rw [heq]
      norm_num
      push_cast
      ring
  have hD : ∀ m : ℕ,
      (1 - Real.cos θ) * D m =
        Real.cos ((m : ℝ) * θ) -
          Real.cos (((m + 1 : ℕ) : ℝ) * θ) := by
    intro m
    induction m with
    | zero =>
        simp [D]
    | succ m ih =>
        rw [show D (m + 1) = D m +
            2 * Real.cos (((m + 1 : ℕ) : ℝ) * θ) by
          simp only [D]
          rw [Finset.sum_Icc_succ_top (by omega)]
          ring]
        rw [mul_add, ih]
        calc
          Real.cos ((m : ℝ) * θ) -
                Real.cos (((m + 1 : ℕ) : ℝ) * θ) +
              (1 - Real.cos θ) *
                (2 * Real.cos (((m + 1 : ℕ) : ℝ) * θ)) =
              Real.cos ((m : ℝ) * θ) +
                Real.cos (((m + 1 : ℕ) : ℝ) * θ) -
                2 * Real.cos θ *
                  Real.cos (((m + 1 : ℕ) : ℝ) * θ) := by ring
          _ = Real.cos ((m : ℝ) * θ) +
                Real.cos (((m + 1 : ℕ) : ℝ) * θ) -
              (Real.cos (θ - ((m + 1 : ℕ) : ℝ) * θ) +
                Real.cos (θ + ((m + 1 : ℕ) : ℝ) * θ)) := by
              rw [Real.two_mul_cos_mul_cos]
          _ = Real.cos (((m + 1 : ℕ) : ℝ) * θ) -
                Real.cos (((m + 1 + 1 : ℕ) : ℝ) * θ) := by
              rw [show Real.cos (θ - ((m + 1 : ℕ) : ℝ) * θ) =
                  Real.cos ((m : ℝ) * θ) by
                rw [← Real.cos_neg]
                congr 1
                push_cast
                ring]
              rw [show Real.cos (θ + ((m + 1 : ℕ) : ℝ) * θ) =
                  Real.cos (((m + 1 + 1 : ℕ) : ℝ) * θ) by
                congr 1
                push_cast
                ring]
              ring
  have hmain : ∀ m : ℕ,
      (1 - Real.cos θ) * F m = 1 - Real.cos ((m : ℝ) * θ) := by
    intro m
    induction m with
    | zero =>
        simp [F]
    | succ m ih =>
        rw [show F (m + 1) = F m + D m by simpa using hF m]
        rw [mul_add, ih, hD]
        push_cast
        ring
  simpa [F] using hmain n

@[blueprint "lem:jackson-fejer-square-integral"
  (statement := /-- For every positive integer \(n\), the finite Fejér
  cosine polynomial satisfies the two integral identities
  \[
    \int_{-\pi}^{\pi}
      \left(n+2\sum_{r=1}^{n-1}(n-r)\cos(r\theta)\right)^2d\theta
    =\frac{2\pi}{3}n(2n^2+1)
  \]
  and
  \[
    \int_{-\pi}^{\pi}(1-\cos\theta)
      \left(n+2\sum_{r=1}^{n-1}(n-r)\cos(r\theta)\right)^2d\theta
    =2\pi n.
  \] -/)
  (proof := /-- Expand the square and integrate term by term. The integral
  of every nonconstant cosine over \([-\pi,\pi]\) is zero, while cosine
  orthogonality gives integral \(\pi\) for equal positive frequencies and
  zero for distinct frequencies. Hence the integral is
  \(2\pi n^2+4\pi\sum_{r=1}^{n-1}(n-r)^2\). The standard formula for
  the sum of the first \(n-1\) squares reduces this expression to the
  first asserted value. For the second identity, multiply
  \cref{lem:jackson-fejer-cosine-identity} by the Fejér polynomial.
  Orthogonality eliminates every resulting nonconstant frequency, leaving
  only the constant term \(n\), whose integral is \(2\pi n\). -/)
  (title := /-- Fejér Polynomial Integral Identities -/)
  (latexEnv := "lemma")]
lemma jackson_fejer_square_integral (n : ℕ) (hn : 0 < n) :
    (∫ θ in Set.Icc (-Real.pi) Real.pi,
      ((n : ℝ) + 2 * ∑ r ∈ Finset.Icc 1 (n - 1),
        ((n - r : ℕ) : ℝ) * Real.cos ((r : ℝ) * θ)) ^ 2) =
      (2 * Real.pi / 3) * (n : ℝ) * (2 * (n : ℝ) ^ 2 + 1) ∧
    (∫ θ in Set.Icc (-Real.pi) Real.pi,
      (1 - Real.cos θ) *
        ((n : ℝ) + 2 * ∑ r ∈ Finset.Icc 1 (n - 1),
          ((n - r : ℕ) : ℝ) * Real.cos ((r : ℝ) * θ)) ^ 2) =
      2 * Real.pi * (n : ℝ) := by
  have hcos (r : ℤ) (hr : r ≠ 0) :
      (∫ θ in Set.Icc (-Real.pi) Real.pi,
        Real.cos ((r : ℝ) * θ)) = 0 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le
      (le_of_lt (neg_lt_self Real.pi_pos))]
    have hscale := intervalIntegral.integral_comp_mul_left
      (f := Real.cos) (a := -Real.pi) (b := Real.pi)
      (c := (r : ℝ)) (by exact_mod_cast hr)
    rw [hscale]
    rw [intervalIntegral.integral_deriv_eq_sub' Real.sin
      (by funext x; simp) (by intro x hx; fun_prop) (by fun_prop)]
    simp [hr]
  have hcoscos (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
      (∫ θ in Set.Icc (-Real.pi) Real.pi,
        Real.cos ((r : ℝ) * θ) * Real.cos ((s : ℝ) * θ)) =
        if r = s then Real.pi else 0 := by
    have hpoint : (fun θ : ℝ =>
        Real.cos ((r : ℝ) * θ) * Real.cos ((s : ℝ) * θ)) =
        fun θ : ℝ =>
          (Real.cos ((((r : ℤ) - (s : ℤ) : ℤ) : ℝ) * θ) +
            Real.cos ((((r : ℤ) + (s : ℤ) : ℤ) : ℝ) * θ)) / 2 := by
      funext θ
      rw [show (((r : ℤ) - (s : ℤ) : ℤ) : ℝ) * θ =
          (r : ℝ) * θ - (s : ℝ) * θ by push_cast; ring]
      rw [show (((r : ℤ) + (s : ℤ) : ℤ) : ℝ) * θ =
          (r : ℝ) * θ + (s : ℝ) * θ by push_cast; ring]
      rw [← Real.two_mul_cos_mul_cos]
      ring
    rw [hpoint, MeasureTheory.integral_div]
    rw [MeasureTheory.integral_add]
    · rcases eq_or_ne r s with hrs | hrs
      · subst s
        rw [hcos ((r : ℤ) + (r : ℤ)) (by omega)]
        simp [Real.volume_Icc]
        rw [max_eq_left (by positivity : 0 ≤ Real.pi + Real.pi)]
        ring
      · rw [hcos ((r : ℤ) - (s : ℤ))
          (sub_ne_zero.mpr (by exact_mod_cast hrs))]
        rw [hcos ((r : ℤ) + (s : ℤ)) (by omega)]
        simp [hrs]
    · exact (by fun_prop : Continuous (fun a : ℝ =>
          Real.cos ((((r : ℤ) - (s : ℤ) : ℤ) : ℝ) * a))).continuousOn
          |>.integrableOn_compact isCompact_Icc
    · exact (by fun_prop : Continuous (fun a : ℝ =>
          Real.cos ((((r : ℤ) + (s : ℤ) : ℤ) : ℝ) * a))).continuousOn
          |>.integrableOn_compact isCompact_Icc
  let I : Finset ℕ := Finset.Icc 1 (n - 1)
  let a : ℕ → ℝ := fun r => ((n - r : ℕ) : ℝ)
  let S : ℝ → ℝ := fun θ =>
    ∑ r ∈ I, a r * Real.cos ((r : ℝ) * θ)
  have hSint :
      (∫ θ in Set.Icc (-Real.pi) Real.pi, S θ) = 0 := by
    dsimp [S]
    rw [MeasureTheory.integral_finset_sum]
    · apply Finset.sum_eq_zero
      intro r hrmem
      rw [MeasureTheory.integral_const_mul]
      have hcr :
          (∫ θ in Set.Icc (-Real.pi) Real.pi,
            Real.cos ((r : ℝ) * θ)) = 0 := by
        simpa using hcos (r : ℤ) (by
          have := (Finset.mem_Icc.mp hrmem).1
          omega)
      rw [hcr]
      simp
    · intro r hrmem
      exact (by fun_prop : Continuous (fun θ : ℝ =>
        a r * Real.cos ((r : ℝ) * θ))).continuousOn
        |>.integrableOn_compact isCompact_Icc
  have hterm (r s : ℕ) (hrmem : r ∈ I) (hsmem : s ∈ I) :
      (∫ θ in Set.Icc (-Real.pi) Real.pi,
        (a r * Real.cos ((r : ℝ) * θ)) *
          (a s * Real.cos ((s : ℝ) * θ))) =
        a r * a s * (if r = s then Real.pi else 0) := by
    rw [show (fun θ : ℝ =>
        (a r * Real.cos ((r : ℝ) * θ)) *
          (a s * Real.cos ((s : ℝ) * θ))) =
        fun θ : ℝ => (a r * a s) *
          (Real.cos ((r : ℝ) * θ) * Real.cos ((s : ℝ) * θ)) by
      funext θ
      ring]
    rw [MeasureTheory.integral_const_mul]
    rw [hcoscos r s
      (by have := (Finset.mem_Icc.mp hrmem).1; omega)
      (by have := (Finset.mem_Icc.mp hsmem).1; omega)]
  have hSsq :
      (∫ θ in Set.Icc (-Real.pi) Real.pi, (S θ) ^ 2) =
        Real.pi * ∑ r ∈ I, (a r) ^ 2 := by
    rw [show (fun θ : ℝ => (S θ) ^ 2) =
        fun θ : ℝ =>
          ∑ r ∈ I, ∑ s ∈ I,
            (a r * Real.cos ((r : ℝ) * θ)) *
              (a s * Real.cos ((s : ℝ) * θ)) by
      funext θ
      dsimp [S]
      rw [pow_two, Finset.sum_mul_sum]]
    rw [MeasureTheory.integral_finset_sum]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hrmem
      rw [MeasureTheory.integral_finset_sum]
      · rw [show (∑ s ∈ I,
            ∫ θ in Set.Icc (-Real.pi) Real.pi,
              (a r * Real.cos ((r : ℝ) * θ)) *
                (a s * Real.cos ((s : ℝ) * θ))) =
            ∑ s ∈ I, a r * a s *
              (if r = s then Real.pi else 0) by
          apply Finset.sum_congr rfl
          intro s hsmem
          exact hterm r s hrmem hsmem]
        simp [hrmem]
        ring
      · intro s hsmem
        exact (by fun_prop : Continuous (fun θ : ℝ =>
          (a r * Real.cos ((r : ℝ) * θ)) *
            (a s * Real.cos ((s : ℝ) * θ)))).continuousOn
          |>.integrableOn_compact isCompact_Icc
    · intro r hrmem
      exact MeasureTheory.integrable_finsetSum I (fun s hsmem =>
        (by fun_prop : Continuous (fun θ : ℝ =>
          (a r * Real.cos ((r : ℝ) * θ)) *
            (a s * Real.cos ((s : ℝ) * θ)))).continuousOn
          |>.integrableOn_compact isCompact_Icc)
  have hI : I = Finset.Ico 1 n := by
    ext r
    simp only [I, Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hreflect :
      (∑ r ∈ I, (a r) ^ 2) =
        ∑ r ∈ Finset.Ico 1 n, (r : ℝ) ^ 2 := by
    rw [hI]
    dsimp [a]
    have hleft : n + 1 - n = 1 := by omega
    have hright : n + 1 - 1 = n := by omega
    simpa [hleft, hright] using
      (Finset.sum_Ico_reflect (fun r : ℕ => (r : ℝ) ^ 2)
        1 (n := n) (m := n) (by omega))
  have hsquares : ∀ m : ℕ,
      6 * (∑ r ∈ Finset.range m, (r : ℝ) ^ 2) =
        (m : ℝ) * ((m - 1 : ℕ) : ℝ) * (2 * (m : ℝ) - 1) := by
    intro m
    induction m with
    | zero =>
        simp
    | succ m ih =>
        rcases m with _ | m
        · norm_num
        · simp only [Finset.sum_range_succ]
          push_cast at ih ⊢
          rw [← Finset.sum_range_succ]
          calc
            6 * (∑ x ∈ Finset.range (m + 1), (x : ℝ) ^ 2 +
                ((m : ℝ) + 1) ^ 2) =
                6 * (∑ x ∈ Finset.range (m + 1), (x : ℝ) ^ 2) +
                  6 * ((m : ℝ) + 1) ^ 2 := by ring
            _ = ((m : ℝ) + 1 + 1) * ((m : ℝ) + 1) *
                (2 * ((m : ℝ) + 1 + 1) - 1) := by
              rw [ih]
              ring
  have hrange :
      (∑ r ∈ Finset.range n, (r : ℝ) ^ 2) =
        ∑ r ∈ Finset.Ico 1 n, (r : ℝ) ^ 2 := by
    rw [Finset.sum_range_eq_add_Ico _ hn]
    norm_num
  have hsum_sq :
      6 * (∑ r ∈ I, (a r) ^ 2) =
        (n : ℝ) * ((n - 1 : ℕ) : ℝ) * (2 * (n : ℝ) - 1) := by
    rw [hreflect, ← hrange]
    exact hsquares n
  have hSintg : MeasureTheory.Integrable S
      (MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi)) := by
    exact (by
      dsimp [S]
      fun_prop : Continuous S).continuousOn
        |>.integrableOn_compact isCompact_Icc
  have hSsqintg : MeasureTheory.Integrable (fun θ => (S θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi)) := by
    exact (by
      dsimp [S]
      fun_prop : Continuous (fun θ => (S θ) ^ 2)).continuousOn
        |>.integrableOn_compact isCompact_Icc
  have hconst :
      (∫ θ in Set.Icc (-Real.pi) Real.pi, ((n : ℝ) ^ 2)) =
        2 * Real.pi * (n : ℝ) ^ 2 := by
    simp [Real.volume_Icc, hn.ne']
    rw [max_eq_left (by positivity : 0 ≤ Real.pi + Real.pi)]
    ring
  constructor
  · change (∫ θ in Set.Icc (-Real.pi) Real.pi,
        ((n : ℝ) + 2 * S θ) ^ 2) =
      (2 * Real.pi / 3) * (n : ℝ) * (2 * (n : ℝ) ^ 2 + 1)
    rw [show (fun θ : ℝ => ((n : ℝ) + 2 * S θ) ^ 2) =
        fun θ : ℝ =>
          ((n : ℝ) ^ 2 + (4 * (n : ℝ)) * S θ) +
            4 * (S θ) ^ 2 by
      funext θ
      ring]
    have houter :
        (∫ θ in Set.Icc (-Real.pi) Real.pi,
          (((n : ℝ) ^ 2 + (4 * (n : ℝ)) * S θ) +
            4 * (S θ) ^ 2)) =
          (∫ θ in Set.Icc (-Real.pi) Real.pi,
            ((n : ℝ) ^ 2 + (4 * (n : ℝ)) * S θ)) +
          ∫ θ in Set.Icc (-Real.pi) Real.pi, 4 * (S θ) ^ 2 := by
      exact MeasureTheory.integral_add
        ((MeasureTheory.integrable_const _).add
          (hSintg.const_mul (4 * (n : ℝ))))
        (hSsqintg.const_mul 4)
    rw [houter]
    have hinner :
        (∫ θ in Set.Icc (-Real.pi) Real.pi,
          ((n : ℝ) ^ 2 + (4 * (n : ℝ)) * S θ)) =
          (∫ θ in Set.Icc (-Real.pi) Real.pi, (n : ℝ) ^ 2) +
          ∫ θ in Set.Icc (-Real.pi) Real.pi,
            (4 * (n : ℝ)) * S θ := by
      exact MeasureTheory.integral_add
        (MeasureTheory.integrable_const _)
        (hSintg.const_mul (4 * (n : ℝ)))
    rw [hinner]
    rw [hconst, MeasureTheory.integral_const_mul, hSint,
      MeasureTheory.integral_const_mul, hSsq]
    have hncast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn]
      norm_num
    rw [hncast] at hsum_sq
    nlinarith [Real.pi_pos]
  · have hcosn :
        (∫ θ in Set.Icc (-Real.pi) Real.pi,
          Real.cos ((n : ℝ) * θ)) = 0 := by
      simpa using hcos (n : ℤ) (by exact_mod_cast hn.ne')
    have hScos :
        (∫ θ in Set.Icc (-Real.pi) Real.pi,
          S θ * Real.cos ((n : ℝ) * θ)) = 0 := by
      dsimp [S]
      rw [show (fun θ : ℝ =>
          (∑ r ∈ I, a r * Real.cos ((r : ℝ) * θ)) *
            Real.cos ((n : ℝ) * θ)) =
          fun θ : ℝ => ∑ r ∈ I,
            (a r * Real.cos ((r : ℝ) * θ)) *
              Real.cos ((n : ℝ) * θ) by
        funext θ
        rw [Finset.sum_mul]]
      rw [MeasureTheory.integral_finset_sum]
      · apply Finset.sum_eq_zero
        intro r hrmem
        rw [show (fun θ : ℝ =>
            a r * Real.cos ((r : ℝ) * θ) *
              Real.cos ((n : ℝ) * θ)) =
            fun θ : ℝ => a r *
              (Real.cos ((r : ℝ) * θ) *
                Real.cos ((n : ℝ) * θ)) by
          funext θ
          ring]
        rw [MeasureTheory.integral_const_mul]
        rw [hcoscos r n
          (by have := (Finset.mem_Icc.mp hrmem).1; omega) hn]
        have hrn : r ≠ n := by
          have := (Finset.mem_Icc.mp hrmem).2
          omega
        simp [hrn]
      · intro r hrmem
        exact (by fun_prop : Continuous (fun θ : ℝ =>
          a r * Real.cos ((r : ℝ) * θ) *
            Real.cos ((n : ℝ) * θ))).continuousOn
          |>.integrableOn_compact isCompact_Icc
    have hScosintg : MeasureTheory.Integrable
        (fun θ => S θ * Real.cos ((n : ℝ) * θ))
        (MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi)) := by
      exact (by
        dsimp [S]
        fun_prop : Continuous (fun θ =>
          S θ * Real.cos ((n : ℝ) * θ))).continuousOn
          |>.integrableOn_compact isCompact_Icc
    change (∫ θ in Set.Icc (-Real.pi) Real.pi,
        (1 - Real.cos θ) * ((n : ℝ) + 2 * S θ) ^ 2) =
      2 * Real.pi * (n : ℝ)
    rw [show (fun θ : ℝ =>
        (1 - Real.cos θ) * ((n : ℝ) + 2 * S θ) ^ 2) =
        fun θ : ℝ =>
          ((n : ℝ) + 2 * S θ) *
            (1 - Real.cos ((n : ℝ) * θ)) by
      funext θ
      have hid := jackson_fejer_cosine_identity n θ
      change (1 - Real.cos θ) * ((n : ℝ) + 2 * S θ) =
        1 - Real.cos ((n : ℝ) * θ) at hid
      calc
        (1 - Real.cos θ) * ((n : ℝ) + 2 * S θ) ^ 2 =
            ((n : ℝ) + 2 * S θ) *
              ((1 - Real.cos θ) * ((n : ℝ) + 2 * S θ)) := by ring
        _ = ((n : ℝ) + 2 * S θ) *
              (1 - Real.cos ((n : ℝ) * θ)) := by rw [hid]]
    rw [show (fun θ : ℝ =>
        ((n : ℝ) + 2 * S θ) *
          (1 - Real.cos ((n : ℝ) * θ))) =
        fun θ : ℝ =>
          ((n : ℝ) + 2 * S θ) -
            ((n : ℝ) * Real.cos ((n : ℝ) * θ) +
              2 * (S θ * Real.cos ((n : ℝ) * θ))) by
      funext θ
      ring]
    have hleft :
        (∫ θ in Set.Icc (-Real.pi) Real.pi,
          ((n : ℝ) + 2 * S θ)) =
          (∫ θ in Set.Icc (-Real.pi) Real.pi, (n : ℝ)) +
          ∫ θ in Set.Icc (-Real.pi) Real.pi, 2 * S θ := by
      exact MeasureTheory.integral_add
        (MeasureTheory.integrable_const _)
        (hSintg.const_mul 2)
    have hright :
        (∫ θ in Set.Icc (-Real.pi) Real.pi,
          ((n : ℝ) * Real.cos ((n : ℝ) * θ) +
            2 * (S θ * Real.cos ((n : ℝ) * θ)))) =
          (∫ θ in Set.Icc (-Real.pi) Real.pi,
            (n : ℝ) * Real.cos ((n : ℝ) * θ)) +
          ∫ θ in Set.Icc (-Real.pi) Real.pi,
            2 * (S θ * Real.cos ((n : ℝ) * θ)) := by
      exact MeasureTheory.integral_add
        ((by fun_prop : Continuous (fun θ : ℝ =>
          (n : ℝ) * Real.cos ((n : ℝ) * θ))).continuousOn
          |>.integrableOn_compact isCompact_Icc)
        (hScosintg.const_mul 2)
    have hsub :
        (∫ θ in Set.Icc (-Real.pi) Real.pi,
          ((n : ℝ) + 2 * S θ) -
            ((n : ℝ) * Real.cos ((n : ℝ) * θ) +
              2 * (S θ * Real.cos ((n : ℝ) * θ)))) =
          (∫ θ in Set.Icc (-Real.pi) Real.pi,
            ((n : ℝ) + 2 * S θ)) -
          ∫ θ in Set.Icc (-Real.pi) Real.pi,
            ((n : ℝ) * Real.cos ((n : ℝ) * θ) +
              2 * (S θ * Real.cos ((n : ℝ) * θ))) := by
      exact MeasureTheory.integral_sub
        ((MeasureTheory.integrable_const _).add (hSintg.const_mul 2))
        (((by fun_prop : Continuous (fun θ : ℝ =>
            (n : ℝ) * Real.cos ((n : ℝ) * θ))).continuousOn
            |>.integrableOn_compact isCompact_Icc).add
          (hScosintg.const_mul 2))
    rw [hsub]
    rw [hleft, hright, MeasureTheory.integral_const_mul, hSint,
      MeasureTheory.integral_const_mul, hcosn,
      MeasureTheory.integral_const_mul, hScos]
    simp [Real.volume_Icc, hn.ne']
    rw [max_eq_left (by positivity : 0 ≤ Real.pi + Real.pi)]
    ring

@[blueprint "lem:jackson-kernel-first-moment"
  (statement := /-- For every integer \(k\geq1\), the normalized Jackson
  kernel satisfies the quantitative first-moment estimate
  \[
    \int_{-\pi}^{\pi}K_k(t)|t|\,dt\leq\frac{18}{k}.
  \] -/)
  (proof := /-- Put \(n=\lfloor k/2\rfloor+1\), let \(F\) be the finite
  cosine polynomial in \cref{def:jackson-kernel}, and write
  \(D=\int_{-\pi}^{\pi}F(t)^2\,dt\). By
  \cref{lem:jackson-fejer-square-integral},
  \[
    D=\frac{2\pi}{3}n(2n^2+1),\qquad
    \int_{-\pi}^{\pi}(1-\cos t)F(t)^2\,dt=2\pi n.
  \]
  In particular, \(D>0\).

  We first record a pointwise estimate on \([-\pi,\pi]\). The half-angle
  identity, the fifth-order sine remainder estimate on
  \(|t|/2\leq1\), and monotonicity of sine on
  \([-\pi/2,\pi/2]\) when \(|t|/2>1\) give
  \[
    t^2\leq32(1-\cos t).
  \]
  The nonnegativity of
  \((2(n/8)|t|-1)^2\) also gives
  \[
    |t|\leq\frac n8t^2+\frac2n
      \leq4n(1-\cos t)+\frac2n.
  \]
  Since \cref{def:jackson-kernel} gives \(K_k(t)=F(t)^2/D\), integration
  of this pointwise inequality and the two preceding identities yields
  \[
  \begin{aligned}
    \int_{-\pi}^{\pi}K_k(t)|t|\,dt
    &\leq \frac{4n}{D}\int_{-\pi}^{\pi}
        (1-\cos t)F(t)^2\,dt
      +\frac{2}{nD}\int_{-\pi}^{\pi}F(t)^2\,dt\\
    &=\frac{12n}{2n^2+1}+\frac2n
      \leq\frac8n.
  \end{aligned}
  \]
  Finally, \(n=\lfloor k/2\rfloor+1>k/2\), so
  \(8/n\leq18/k\). -/)
  (title := /-- First Moment of the Jackson Kernel -/)
  (latexEnv := "lemma")]
lemma jackson_kernel_first_moment (k : ℕ) (hk : 0 < k) :
    (∫ θ in Set.Icc (-Real.pi) Real.pi,
      jackson_kernel k θ * |θ|) ≤ 18 / (k : ℝ) := by
  let n : ℕ := k / 2 + 1
  let F : ℝ → ℝ := fun θ =>
    (n : ℝ) + 2 * ∑ r ∈ Finset.Icc 1 (n - 1),
      ((n - r : ℕ) : ℝ) * Real.cos ((r : ℝ) * θ)
  let D : ℝ :=
    ∫ θ in Set.Icc (-Real.pi) Real.pi, (F θ) ^ 2
  have hn : 0 < n := by
    dsimp [n]
    omega
  obtain ⟨hD, hW⟩ := jackson_fejer_square_integral n hn
  change D = (2 * Real.pi / 3) * (n : ℝ) *
      (2 * (n : ℝ) ^ 2 + 1) at hD
  change (∫ θ in Set.Icc (-Real.pi) Real.pi,
      (1 - Real.cos θ) * (F θ) ^ 2) =
        2 * Real.pi * (n : ℝ) at hW
  have hnR : 0 < (n : ℝ) := by positivity
  have hDpos : 0 < D := by
    rw [hD]
    positivity
  have hjackson : ∀ θ : ℝ,
      jackson_kernel k θ = (F θ) ^ 2 / D := by
    intro θ
    rfl
  have habs_bound (θ : ℝ) (hθ : θ ∈ Set.Icc (-Real.pi) Real.pi) :
      |θ| ≤
        (4 * (n : ℝ)) * (1 - Real.cos θ) +
          2 / (n : ℝ) := by
    have hθabs : |θ| ≤ Real.pi := by
      rw [abs_le]
      exact hθ
    let x : ℝ := |θ| / 2
    have hx0 : 0 ≤ x := by
      dsimp [x]
      positivity
    have hxpi : x ≤ Real.pi / 2 := by
      dsimp [x]
      linarith
    have hsin_one : (1 : ℝ) / 2 ≤ Real.sin 1 := by
      have hb := Real.sin_bound (x := (1 : ℝ)) (by norm_num)
      rw [abs_le] at hb
      norm_num at hb ⊢
      linarith
    have hid : 1 - Real.cos θ = 2 * (Real.sin x) ^ 2 := by
      calc
        1 - Real.cos θ = 1 - Real.cos |θ| := by rw [Real.cos_abs]
        _ = 1 - Real.cos (2 * (|θ| / 2)) := by
          congr 2
          ring
        _ = 2 * (Real.sin (|θ| / 2)) ^ 2 := by
          rw [Real.cos_two_mul]
          nlinarith [Real.sin_sq_add_cos_sq (|θ| / 2)]
        _ = 2 * (Real.sin x) ^ 2 := by rfl
    have hcos' : θ ^ 2 ≤ 32 * (1 - Real.cos θ) := by
      rcases le_or_gt x 1 with hx1 | hx1
      · have hb := Real.sin_bound (x := x) (by
          rw [abs_of_nonneg hx0]
          exact hx1)
        have hlower := (abs_le.mp hb).1
        rw [abs_of_nonneg hx0] at hlower
        have hx2 : x ^ 2 ≤ 1 := by
          nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
        have hx3 : x ^ 3 ≤ x := by
          have hm := mul_nonneg hx0 (sub_nonneg.mpr hx2)
          nlinarith
        have hx5 : x ^ 5 ≤ x ^ 3 := by
          have hm := mul_le_mul_of_nonneg_left hx2 (by positivity : 0 ≤ x ^ 3)
          nlinarith
        have hs : x / 2 ≤ Real.sin x := by
          nlinarith
        have hs0 : 0 ≤ Real.sin x := le_trans (by positivity) hs
        have hs_sq : (x / 2) ^ 2 ≤ (Real.sin x) ^ 2 :=
          (sq_le_sq₀ (by positivity) hs0).mpr hs
        have hθx : θ ^ 2 = 4 * x ^ 2 := by
          dsimp [x]
          rw [← sq_abs θ]
          ring
        rw [hid]
        nlinarith
      · have hxmem : x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
          constructor <;> linarith [Real.pi_pos]
        have h1mem : (1 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
          constructor
          · linarith [Real.pi_pos]
          · exact Real.one_le_pi_div_two
        have hsmono : Real.sin 1 ≤ Real.sin x :=
          Real.strictMonoOn_sin.monotoneOn h1mem hxmem hx1.le
        have hs : (1 : ℝ) / 2 ≤ Real.sin x := hsin_one.trans hsmono
        have hs_sq : ((1 : ℝ) / 2) ^ 2 ≤ (Real.sin x) ^ 2 :=
          (sq_le_sq₀ (by norm_num) (by linarith)).mpr hs
        have hθ4 : θ ^ 2 ≤ (4 : ℝ) ^ 2 := by
          calc
            θ ^ 2 = |θ| ^ 2 := (sq_abs θ).symm
            _ ≤ (4 : ℝ) ^ 2 :=
              (sq_le_sq₀ (abs_nonneg θ) (by norm_num)).mpr
                (hθabs.trans Real.pi_le_four)
        rw [hid]
        nlinarith
    have hquad : |θ| ≤ ((n : ℝ) / 8) * θ ^ 2 +
        2 / (n : ℝ) := by
      have hmul :
          4 * ((n : ℝ) / 8) * |θ| ≤
            4 * ((n : ℝ) / 8) *
              (((n : ℝ) / 8) * θ ^ 2) + 1 := by
        nlinarith [sq_nonneg
          (2 * ((n : ℝ) / 8) * |θ| - 1), sq_abs θ]
      calc
        |θ| = (4 * ((n : ℝ) / 8) * |θ|) /
            (4 * ((n : ℝ) / 8)) := by
          field_simp
        _ ≤ (4 * ((n : ℝ) / 8) *
              (((n : ℝ) / 8) * θ ^ 2) + 1) /
            (4 * ((n : ℝ) / 8)) :=
          div_le_div_of_nonneg_right hmul (by positivity)
        _ = ((n : ℝ) / 8) * θ ^ 2 + 2 / (n : ℝ) := by
          field_simp
          ring
    calc
      |θ| ≤ ((n : ℝ) / 8) * θ ^ 2 + 2 / (n : ℝ) := hquad
      _ ≤ ((n : ℝ) / 8) * (32 * (1 - Real.cos θ)) +
            2 / (n : ℝ) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hcos'
            (div_nonneg hnR.le
              (show (0 : ℝ) ≤ 8 by norm_num))) le_rfl
      _ = (4 * (n : ℝ)) * (1 - Real.cos θ) +
            2 / (n : ℝ) := by ring
  let G : ℝ → ℝ := fun θ => (F θ) ^ 2 / D * |θ|
  let H : ℝ → ℝ := fun θ =>
    ((4 * (n : ℝ)) / D) *
        ((F θ) ^ 2 * (1 - Real.cos θ)) +
      ((2 / (n : ℝ)) / D) * (F θ) ^ 2
  have hGH (θ : ℝ) (hθ : θ ∈ Set.Icc (-Real.pi) Real.pi) :
      G θ ≤ H θ := by
    have hFnonneg : 0 ≤ (F θ) ^ 2 / D :=
      div_nonneg (sq_nonneg _) hDpos.le
    calc
      G θ = (F θ) ^ 2 / D * |θ| := rfl
      _ ≤ (F θ) ^ 2 / D *
          ((4 * (n : ℝ)) * (1 - Real.cos θ) +
            2 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (habs_bound θ hθ) hFnonneg
      _ = H θ := by
        dsimp [H]
        field_simp
  have hGint : MeasureTheory.Integrable G
      (MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi)) := by
    exact (by
      dsimp [G, F]
      fun_prop : Continuous G).continuousOn
        |>.integrableOn_compact isCompact_Icc
  have hHint : MeasureTheory.Integrable H
      (MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi)) := by
    exact (by
      dsimp [H, F]
      fun_prop : Continuous H).continuousOn
        |>.integrableOn_compact isCompact_Icc
  have hmono :
      (∫ θ in Set.Icc (-Real.pi) Real.pi, G θ) ≤
        ∫ θ in Set.Icc (-Real.pi) Real.pi, H θ := by
    apply MeasureTheory.integral_mono_ae hGint hHint
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact hGH θ hθ
  have hWrev :
      (∫ θ in Set.Icc (-Real.pi) Real.pi,
        (F θ) ^ 2 * (1 - Real.cos θ)) =
          2 * Real.pi * (n : ℝ) := by
    simpa [mul_comm] using hW
  have hH :
      (∫ θ in Set.Icc (-Real.pi) Real.pi, H θ) =
        ((4 * (n : ℝ)) / D) *
            (2 * Real.pi * (n : ℝ)) +
          ((2 / (n : ℝ)) / D) * D := by
    dsimp [H]
    rw [MeasureTheory.integral_add]
    · rw [MeasureTheory.integral_const_mul, hWrev,
        MeasureTheory.integral_const_mul]
    · exact (by
        dsimp [F]
        fun_prop : Continuous (fun θ : ℝ =>
          ((4 * (n : ℝ)) / D) *
            ((F θ) ^ 2 * (1 - Real.cos θ)))).continuousOn
          |>.integrableOn_compact isCompact_Icc
    · exact (by
        dsimp [F]
        fun_prop : Continuous (fun θ : ℝ =>
          ((2 / (n : ℝ)) / D) * (F θ) ^ 2)).continuousOn
          |>.integrableOn_compact isCompact_Icc
  have hfirst :
      (12 * (n : ℝ)) / (2 * (n : ℝ) ^ 2 + 1) ≤
        6 / (n : ℝ) := by
    apply (div_le_div_iff₀ (by positivity)
      hnR).2
    nlinarith [sq_nonneg (n : ℝ)]
  have hbound :
      ((4 * (n : ℝ)) / D) *
          (2 * Real.pi * (n : ℝ)) +
        ((2 / (n : ℝ)) / D) * D ≤
          8 / (n : ℝ) := by
    rw [hD]
    have hsimp :
        (((4 * (n : ℝ)) /
              ((2 * Real.pi / 3) * (n : ℝ) *
                (2 * (n : ℝ) ^ 2 + 1))) *
            (2 * Real.pi * (n : ℝ)) +
          ((2 / (n : ℝ)) /
              ((2 * Real.pi / 3) * (n : ℝ) *
                (2 * (n : ℝ) ^ 2 + 1))) *
            ((2 * Real.pi / 3) * (n : ℝ) *
              (2 * (n : ℝ) ^ 2 + 1))) =
          (12 * (n : ℝ)) / (2 * (n : ℝ) ^ 2 + 1) +
            2 / (n : ℝ) := by
      field_simp
      ring
    rw [hsimp]
    calc
      (12 * (n : ℝ)) / (2 * (n : ℝ) ^ 2 + 1) +
          2 / (n : ℝ) ≤
        6 / (n : ℝ) + 2 / (n : ℝ) :=
          add_le_add hfirst le_rfl
      _ = 8 / (n : ℝ) := by ring
  have hkn : (k : ℝ) < 2 * (n : ℝ) := by
    exact_mod_cast (show k < 2 * n by
      dsimp [n]
      omega)
  have hlast : 8 / (n : ℝ) ≤ 18 / (k : ℝ) := by
    have hkR : 0 < (k : ℝ) := by positivity
    apply (div_le_div_iff₀ hnR hkR).2
    nlinarith
  rw [show (fun θ : ℝ => jackson_kernel k θ * |θ|) = G by
    funext θ
    rw [hjackson]]
  exact hmono.trans (hH.le.trans (hbound.trans hlast))

@[blueprint "lem:jackson-chebyshev-approximation"
  (statement := /-- Let \(f:\mathbb R\to\mathbb R\) be \(C^\infty\), and
  let \(\ell\geq0\) be such that \(f\) is globally
  \(\ell\)-Lipschitz. For every positive integer \(k\), there exists a
  sequence \(b:\mathbb N\to\mathbb R\) such that \(b_0=1\),
  \(0\leq b_j\leq1\) for every \(1\leq j\leq k\), and
  \[
    |f(x)-J_{k,b}f(x)|\leq\frac{18\ell}{k}
    \qquad\text{for every }x\in[-1,1],
  \]
  where \(J_{k,b}f\) is the approximant from
  \cref{def:damped-chebyshev-approximation}. -/)
  (proof := /-- Since a Lipschitz function is continuous,
  \cref{lem:jackson-convolution-expansion} supplies coefficients \(b_j\)
  in the required ranges and identifies \(J_{k,b}f(\cos\theta)\) with
  convolution by \(K_k\). By the nonnegativity and unit-mass assertions of
  \cref{lem:jackson-kernel-properties}, for every \(\theta\in\mathbb R\),
  \[
  \begin{aligned}
    |f(\cos\theta)-J_{k,b}f(\cos\theta)|
    &\leq\int_{-\pi}^{\pi}K_k(t)
      |f(\cos\theta)-f(\cos(\theta-t))|\,dt\\
    &\leq\ell\int_{-\pi}^{\pi}K_k(t)|t|\,dt.
  \end{aligned}
  \]
  Here the second inequality uses the \(\ell\)-Lipschitz hypothesis. To
  justify the remaining elementary estimate, the cosine-difference identity,
  \(|\sin u|\leq1\), and \(|\sin v|\leq|v|\) give
  \(|\cos\theta-\cos(\theta-t)|\leq|t|\). The latter sine bound follows
  from the fifth-order Taylor remainder when \(|v|\leq1\), and from
  \(|\sin v|\leq1<|v|\) otherwise. The estimate
  \cref{lem:jackson-kernel-first-moment} bounds the last expression by
  \(18\ell/k\). Finally, if \(x\in[-1,1]\), take
  \(\theta=\arccos x\); then \(\cos\theta=x\), and the asserted uniform
  estimate follows. -/)
  (title := /-- Quantitative Jackson Approximation -/)
  (latexEnv := "lemma")]
lemma jackson_chebyshev_approximation
    (f : ℝ → ℝ) (ℓ : NNReal) (k : ℕ)
    (hk : 0 < k) (hf : LipschitzWith ℓ f)
    (hf_smooth : ContDiff ℝ ⊤ f) :
    ∃ b : ℕ → ℝ,
      b 0 = 1 ∧
      (∀ j ∈ Finset.Icc 1 k, 0 ≤ b j ∧ b j ≤ 1) ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        |f x - damped_chebyshev_approximation f k b x| ≤
          18 * (ℓ : ℝ) / (k : ℝ) := by
  obtain ⟨b, hb_zero, hb_bounds, hconvolution⟩ :=
    jackson_convolution_expansion f hf.continuous k hk
  refine ⟨b, hb_zero, hb_bounds, ?_⟩
  intro x hx
  obtain ⟨hK_cont, hK_nonneg, hK_mass, _, _⟩ :=
    jackson_kernel_properties k hk
  let θ : ℝ := Real.arccos x
  have hx_cos : Real.cos θ = x := by
    dsimp [θ]
    exact Real.cos_arccos hx.1 hx.2
  rw [← hx_cos, ← hconvolution θ]
  have hshift_cont : Continuous
      (fun t : ℝ => f (Real.cos (θ - t))) := by
    exact hf.continuous.comp
      (Real.continuous_cos.comp (continuous_const.sub continuous_id))
  have hleft_integrable : MeasureTheory.IntegrableOn
      (fun t : ℝ => f (Real.cos θ) * jackson_kernel k t)
      (Set.Icc (-Real.pi) Real.pi) :=
    (continuous_const.mul hK_cont).integrableOn_Icc
  have hright_integrable : MeasureTheory.IntegrableOn
      (fun t : ℝ => jackson_kernel k t * f (Real.cos (θ - t)))
      (Set.Icc (-Real.pi) Real.pi) :=
    (hK_cont.mul hshift_cont).integrableOn_Icc
  have hmoment_integrable : MeasureTheory.IntegrableOn
      (fun t : ℝ => jackson_kernel k t * |t|)
      (Set.Icc (-Real.pi) Real.pi) :=
    (hK_cont.mul continuous_abs).integrableOn_Icc
  have hpointwise (t : ℝ) :
      |f (Real.cos θ) * jackson_kernel k t -
          jackson_kernel k t * f (Real.cos (θ - t))| ≤
        (ℓ : ℝ) * (jackson_kernel k t * |t|) := by
    have hf_bound := hf.dist_le_mul (Real.cos θ) (Real.cos (θ - t))
    have hf_bound' :
        |f (Real.cos θ) - f (Real.cos (θ - t))| ≤
          (ℓ : ℝ) * |Real.cos θ - Real.cos (θ - t)| := by
      simpa [Real.dist_eq] using hf_bound
    have habs_sin_le_abs (z : ℝ) : |Real.sin z| ≤ |z| := by
      by_cases hz : |z| ≤ 1
      · have hz0 : 0 ≤ |z| := abs_nonneg z
        have hzsq : z ^ 2 ≤ 1 := by
          rw [← sq_abs]
          nlinarith
        have hfactor : 0 ≤ 1 - z ^ 2 / 6 := by nlinarith
        have happ := Real.sin_bound hz
        have habs_poly :
            |z - z ^ 3 / 6| = |z| * (1 - z ^ 2 / 6) := by
          rw [show z - z ^ 3 / 6 = z * (1 - z ^ 2 / 6) by ring,
            abs_mul, abs_of_nonneg hfactor]
        have hzpow : |z| ^ 5 ≤ |z| ^ 3 := by
          have hzsq_abs : |z| ^ 2 ≤ 1 := by nlinarith
          have hnonneg : 0 ≤ |z| ^ 3 := by positivity
          nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hzsq_abs)]
        calc
          |Real.sin z| =
              |(Real.sin z - (z - z ^ 3 / 6)) +
                (z - z ^ 3 / 6)| := by
                  congr 1
                  ring
          _ ≤ |Real.sin z - (z - z ^ 3 / 6)| +
                |z - z ^ 3 / 6| := abs_add_le _ _
          _ ≤ |z| ^ 5 / 100 + |z - z ^ 3 / 6| :=
            add_le_add happ le_rfl
          _ = |z| ^ 5 / 100 + |z| * (1 - z ^ 2 / 6) := by
            rw [habs_poly]
          _ ≤ |z| := by
            rw [← sq_abs z]
            nlinarith
      · have hsone : |Real.sin z| ≤ 1 := Real.abs_sin_le_one z
        exact hsone.trans (le_of_lt (lt_of_not_ge hz))
    have hcos :
        |Real.cos θ - Real.cos (θ - t)| ≤ |t| := by
      rw [Real.cos_sub_cos, abs_mul, abs_mul]
      have hfirst := Real.abs_sin_le_one
        (x := (θ + (θ - t)) / 2)
      have hsecond := habs_sin_le_abs ((θ - (θ - t)) / 2)
      calc
        |-2| * |Real.sin ((θ + (θ - t)) / 2)| *
            |Real.sin ((θ - (θ - t)) / 2)| ≤
            2 * 1 * |(θ - (θ - t)) / 2| := by
              calc
                |-2| * |Real.sin ((θ + (θ - t)) / 2)| *
                    |Real.sin ((θ - (θ - t)) / 2)| =
                    2 * (|Real.sin ((θ + (θ - t)) / 2)| *
                      |Real.sin ((θ - (θ - t)) / 2)|) := by
                        norm_num
                        ring
                _ ≤ 2 * (1 * |(θ - (θ - t)) / 2|) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul hfirst hsecond (abs_nonneg _) (by norm_num))
                    (by norm_num)
                _ = 2 * 1 * |(θ - (θ - t)) / 2| := by ring
        _ = |t| := by
          rw [show θ - (θ - t) = t by ring, abs_div]
          norm_num
          ring
    calc
      |f (Real.cos θ) * jackson_kernel k t -
          jackson_kernel k t * f (Real.cos (θ - t))| =
          jackson_kernel k t *
            |f (Real.cos θ) - f (Real.cos (θ - t))| := by
              rw [show f (Real.cos θ) * jackson_kernel k t -
                  jackson_kernel k t * f (Real.cos (θ - t)) =
                    jackson_kernel k t *
                      (f (Real.cos θ) - f (Real.cos (θ - t))) by ring,
                abs_mul, abs_of_nonneg (hK_nonneg t)]
      _ ≤ jackson_kernel k t * ((ℓ : ℝ) * |t|) := by
        apply mul_le_mul_of_nonneg_left _ (hK_nonneg t)
        exact hf_bound'.trans
          (mul_le_mul_of_nonneg_left hcos (by positivity))
      _ = (ℓ : ℝ) * (jackson_kernel k t * |t|) := by ring
  have hmono :
      (∫ t in Set.Icc (-Real.pi) Real.pi,
        |f (Real.cos θ) * jackson_kernel k t -
          jackson_kernel k t * f (Real.cos (θ - t))|) ≤
      ∫ t in Set.Icc (-Real.pi) Real.pi,
        (ℓ : ℝ) * (jackson_kernel k t * |t|) := by
    apply MeasureTheory.setIntegral_mono_on
      (hleft_integrable.sub hright_integrable).abs
      (hmoment_integrable.const_mul (ℓ : ℝ)) measurableSet_Icc
    intro t _ht
    exact hpointwise t
  calc
    |f (Real.cos θ) -
        ∫ t in Set.Icc (-Real.pi) Real.pi,
          jackson_kernel k t * f (Real.cos (θ - t))| =
        |f (Real.cos θ) *
            (∫ t in Set.Icc (-Real.pi) Real.pi, jackson_kernel k t) -
          ∫ t in Set.Icc (-Real.pi) Real.pi,
            jackson_kernel k t * f (Real.cos (θ - t))| := by
              rw [hK_mass, mul_one]
    _ = |(∫ t in Set.Icc (-Real.pi) Real.pi,
            f (Real.cos θ) * jackson_kernel k t) -
          ∫ t in Set.Icc (-Real.pi) Real.pi,
            jackson_kernel k t * f (Real.cos (θ - t))| := by
              rw [MeasureTheory.integral_const_mul]
    _ = |∫ t in Set.Icc (-Real.pi) Real.pi,
          (f (Real.cos θ) * jackson_kernel k t -
            jackson_kernel k t * f (Real.cos (θ - t)))| := by
              rw [MeasureTheory.integral_sub hleft_integrable
                hright_integrable]
    _ ≤ ∫ t in Set.Icc (-Real.pi) Real.pi,
          |f (Real.cos θ) * jackson_kernel k t -
            jackson_kernel k t * f (Real.cos (θ - t))| :=
      MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ t in Set.Icc (-Real.pi) Real.pi,
          (ℓ : ℝ) * (jackson_kernel k t * |t|) := hmono
    _ = (ℓ : ℝ) *
        (∫ t in Set.Icc (-Real.pi) Real.pi,
          jackson_kernel k t * |t|) := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ (ℓ : ℝ) * (18 / (k : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (jackson_kernel_first_moment k hk) (by positivity)
    _ = 18 * (ℓ : ℝ) / (k : ℝ) := by ring

@[blueprint "lem:chebyshev-approximation-pairing"
  (statement := /-- Let \(p,q\) be probability measures on \(\mathbb R\)
  whose supports are contained in \([-1,1]\). For every
  \(f:\mathbb R\to\mathbb R\), every \(k\in\mathbb N\), and every sequence
  \(b:\mathbb N\to\mathbb R\),
  \[
  \begin{aligned}
    \int J_{k,b}f\,dp-\int J_{k,b}f\,dq
    =\sum_{j=1}^{k} b_jc_j(f)
      \bigl(\widetilde m_j(p)-\widetilde m_j(q)\bigr).
  \end{aligned}
  \] -/)
  (proof := /-- Each function \(\mathcal T_j\) from
  \cref{def:normalized-chebyshev-first} is continuous. Since the supports of
  \(p\) and \(q\) are contained in the compact interval \([-1,1]\), it is
  integrable with respect to both measures. Expand the finite sum in
  \cref{def:damped-chebyshev-approximation} and apply linearity of the
  integral term by term. By \cref{def:normalized-chebyshev-moment}, the
  resulting summand of index \(j\) is
  \(b_jc_j(f)(\widetilde m_j(p)-\widetilde m_j(q))\). At \(j=0\), the
  normalized Chebyshev function is the constant \(1/\sqrt{\pi}\); because
  both measures have total mass one, this summand vanishes. The remaining
  indices are precisely \(1,\ldots,k\), which gives the stated identity. -/)
  (title := /-- Pairing of a Chebyshev Approximant with a Measure Difference -/)
  (latexEnv := "lemma")]
lemma chebyshev_approximation_pairing
    (p q : MeasureTheory.ProbabilityMeasure ℝ)
    (hp : (p : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
    (hq : (q : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
    (f : ℝ → ℝ) (k : ℕ) (b : ℕ → ℝ) :
    (∫ x, damped_chebyshev_approximation f k b x
        ∂(p : MeasureTheory.Measure ℝ)) -
      (∫ x, damped_chebyshev_approximation f k b x
        ∂(q : MeasureTheory.Measure ℝ)) =
      ∑ j ∈ Finset.Icc 1 k,
        b j * chebyshev_coefficient f j *
          (normalized_chebyshev_moment p j -
            normalized_chebyshev_moment q j) := by
  have basis_integrable
      (r : MeasureTheory.ProbabilityMeasure ℝ)
      (hr : (r : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
      (j : ℕ) :
      MeasureTheory.Integrable (normalized_chebyshev_first j)
        (r : MeasureTheory.Measure ℝ) := by
    have hmem : ∀ᵐ x ∂(r : MeasureTheory.Measure ℝ), x ∈ Set.Icc (-1 : ℝ) 1 := by
      filter_upwards [MeasureTheory.Measure.support_mem_ae
        (μ := (r : MeasureTheory.Measure ℝ))] with x hx
      exact hr hx
    rw [← MeasureTheory.Measure.restrict_eq_self_of_ae_mem hmem]
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    unfold normalized_chebyshev_first chebyshev_first
    split_ifs
    · exact (Polynomial.Chebyshev.T ℝ (j : ℤ)).continuous.div_const _ |>.continuousOn
    · exact (Polynomial.Chebyshev.T ℝ (j : ℤ)).continuous.div_const _ |>.continuousOn
  have integral_damped
      (r : MeasureTheory.ProbabilityMeasure ℝ)
      (hr : (r : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1) :
      (∫ x, damped_chebyshev_approximation f k b x
        ∂(r : MeasureTheory.Measure ℝ)) =
        ∑ j ∈ Finset.range (k + 1),
          b j * chebyshev_coefficient f j * normalized_chebyshev_moment r j := by
    unfold damped_chebyshev_approximation
    rw [MeasureTheory.integral_finsetSum]
    · simp only [MeasureTheory.integral_const_mul]
      rfl
    · intro j hj
      exact (basis_integrable r hr j).const_mul _
  have hzero :
      normalized_chebyshev_moment p 0 = normalized_chebyshev_moment q 0 := by
    simp [normalized_chebyshev_moment, normalized_chebyshev_first, chebyshev_first]
  have hrange : Finset.range (k + 1) = insert 0 (Finset.Icc 1 k) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [integral_damped p hp, integral_damped q hq, ← Finset.sum_sub_distrib,
    hrange, Finset.sum_insert (by simp), hzero]
  simp only [sub_self, mul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro j hj
  ring

@[blueprint "lem:smooth-lipschitz-pairing-bound"
  (statement := /-- Let \(p,q\) be probability measures supported on
  \([-1,1]\), let \(k\geq1\), and let \(\Gamma\geq0\). If
  \(D_k(p,q)^2\leq\Gamma^2\), then every globally \(1\)-Lipschitz,
  \(C^\infty\) function \(f:\mathbb R\to\mathbb R\) satisfies
  \[
    \int f\,dp-\int f\,dq\leq \frac{36}{k}+\Gamma.
  \] -/)
  (proof := /-- Apply \cref{lem:jackson-chebyshev-approximation} with
  \(\ell=1\), and denote the resulting approximant by \(f_k\). The uniform
  error bound and the fact that \(p\) and \(q\) each have mass one give
  \[
    \int f\,dp-\int f\,dq
      \leq \int f_k\,dp-\int f_k\,dq+\frac{36}{k}.
  \]
  By \cref{lem:chebyshev-approximation-pairing}, the remaining difference is
  the finite sum of the damped coefficients against the first \(k\) moment
  differences. Multiply this identity by \(\sqrt{\pi/2}\). By
  \cref{lem:source-normalization-conversion}, the resulting sum contains
  the ordinary moment differences. Insert the factors \(j\) and \(1/j\)
  and apply finite Cauchy--Schwarz. Since \(0\leq b_j\leq1\),
  \cref{lem:global-chebyshev-coefficient-decay} bounds the squared
  coefficient factor by \(\pi/2\), while the squared moment factor is
  \(D_k(p,q)^2\). Consequently,
  \[
    \frac{\pi}{2}
      \left(\int f_k\,dp-\int f_k\,dq\right)^2
      \leq \frac{\pi}{2}D_k(p,q)^2
      \leq \frac{\pi}{2}\Gamma^2.
  \]
  Since \(\pi/2>0\) and \(\Gamma\geq0\), the pairing with the
  approximant is at most \(\Gamma\). Combining the two estimates gives
  the asserted inequality. -/)
  (title := /-- Smooth Lipschitz Pairing Bound -/)
  (latexEnv := "lemma")]
lemma smooth_lipschitz_pairing_bound
    (p q : MeasureTheory.ProbabilityMeasure ℝ)
    (hp : (p : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
    (hq : (q : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
    (k : ℕ) (hk : 0 < k) (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hmom : weighted_moment_discrepancy_sq p q k ≤ Γ ^ 2)
    (f : ℝ → ℝ) (hf : LipschitzWith 1 f)
    (hf_smooth : ContDiff ℝ ⊤ f) :
    (∫ x, f x ∂(p : MeasureTheory.Measure ℝ)) -
      (∫ x, f x ∂(q : MeasureTheory.Measure ℝ)) ≤
        36 / (k : ℝ) + Γ := by
  obtain ⟨b, _, hb_bounds, happrox⟩ :=
    jackson_chebyshev_approximation f 1 k hk hf hf_smooth
  let g : ℝ → ℝ := damped_chebyshev_approximation f k b
  have normalized_continuous (j : ℕ) :
      Continuous (normalized_chebyshev_first j) := by
    unfold normalized_chebyshev_first chebyshev_first
    split_ifs <;> fun_prop
  have hg_cont : Continuous g := by
    unfold g damped_chebyshev_approximation
    fun_prop (disch := exact normalized_continuous _)
  have support_ae
      (r : MeasureTheory.ProbabilityMeasure ℝ)
      (hr : (r : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1) :
      ∀ᵐ x ∂(r : MeasureTheory.Measure ℝ), x ∈ Set.Icc (-1 : ℝ) 1 := by
    filter_upwards [MeasureTheory.Measure.support_mem_ae
      (μ := (r : MeasureTheory.Measure ℝ))] with x hx
    exact hr hx
  have hf_integrable
      (r : MeasureTheory.ProbabilityMeasure ℝ)
      (hr : (r : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1) :
      MeasureTheory.Integrable f (r : MeasureTheory.Measure ℝ) := by
    rw [← MeasureTheory.Measure.restrict_eq_self_of_ae_mem (support_ae r hr)]
    exact hf.continuous.continuousOn.integrableOn_compact isCompact_Icc
  have hg_integrable
      (r : MeasureTheory.ProbabilityMeasure ℝ)
      (hr : (r : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1) :
      MeasureTheory.Integrable g (r : MeasureTheory.Measure ℝ) := by
    rw [← MeasureTheory.Measure.restrict_eq_self_of_ae_mem (support_ae r hr)]
    exact hg_cont.continuousOn.integrableOn_compact isCompact_Icc
  have error_integral
      (r : MeasureTheory.ProbabilityMeasure ℝ)
      (hr : (r : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1) :
      |∫ x, f x - g x ∂(r : MeasureTheory.Measure ℝ)| ≤
        18 / (k : ℝ) := by
    have hdiff := (hf_integrable r hr).sub (hg_integrable r hr)
    calc
      |∫ x, f x - g x ∂(r : MeasureTheory.Measure ℝ)| ≤
          ∫ x, |f x - g x| ∂(r : MeasureTheory.Measure ℝ) :=
        MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ _x, 18 / (k : ℝ) ∂(r : MeasureTheory.Measure ℝ) := by
        apply MeasureTheory.integral_mono_ae hdiff.abs
          (MeasureTheory.integrable_const _)
        filter_upwards [support_ae r hr] with x hx
        simpa [g] using happrox x hx
      _ = 18 / (k : ℝ) := by simp
  let A : ℝ :=
    (∫ x, g x ∂(p : MeasureTheory.Measure ℝ)) -
      ∫ x, g x ∂(q : MeasureTheory.Measure ℝ)
  have original_le_approximant :
      (∫ x, f x ∂(p : MeasureTheory.Measure ℝ)) -
          ∫ x, f x ∂(q : MeasureTheory.Measure ℝ) ≤
        A + 36 / (k : ℝ) := by
    have hp_sub := MeasureTheory.integral_sub
      (hf_integrable p hp) (hg_integrable p hp)
    have hq_sub := MeasureTheory.integral_sub
      (hf_integrable q hq) (hg_integrable q hq)
    have hp_error := error_integral p hp
    have hq_error := error_integral q hq
    have hconstants : 36 / (k : ℝ) = 2 * (18 / (k : ℝ)) := by ring
    dsimp [A]
    rw [hconstants]
    nlinarith [le_abs_self
      (∫ x, f x - g x ∂(p : MeasureTheory.Measure ℝ)),
      neg_le_abs (∫ x, f x - g x ∂(q : MeasureTheory.Measure ℝ))]
  let S : Finset ℕ := Finset.Icc 1 k
  let a : ℕ → ℝ := fun j =>
    b j * ((j : ℝ) * chebyshev_coefficient f j)
  let d : ℕ → ℝ := fun j =>
    (chebyshev_moment p j - chebyshev_moment q j) / (j : ℝ)
  let R : ℝ := ∑ j ∈ S, a j * d j
  have scaled_pairing : Real.sqrt (Real.pi / 2) * A = R := by
    rw [show A =
      (∫ x, damped_chebyshev_approximation f k b x
          ∂(p : MeasureTheory.Measure ℝ)) -
        ∫ x, damped_chebyshev_approximation f k b x
          ∂(q : MeasureTheory.Measure ℝ) by rfl]
    rw [chebyshev_approximation_pairing p q hp hq f k b]
    dsimp [R, S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj_pos : 0 < j := (Finset.mem_Icc.mp hj).1
    have hj_ne : (j : ℝ) ≠ 0 := by positivity
    have hnormalization :=
      source_normalization_conversion p q hp hq j hj_pos
    dsimp [a, d]
    rw [show Real.sqrt (Real.pi / 2) *
        (b j * chebyshev_coefficient f j *
          (normalized_chebyshev_moment p j -
            normalized_chebyshev_moment q j)) =
        b j * chebyshev_coefficient f j *
          (Real.sqrt (Real.pi / 2) *
            (normalized_chebyshev_moment p j -
              normalized_chebyshev_moment q j)) by ring,
      hnormalization]
    field_simp [hj_ne]
  have moment_sum :
      (∑ j ∈ S, (d j) ^ 2) =
        weighted_moment_discrepancy_sq p q k := by
    dsimp [S, d, weighted_moment_discrepancy_sq]
    apply Finset.sum_congr rfl
    intro j hj
    rw [div_pow]
  obtain ⟨hcoeff_summable, hcoeff_tsum⟩ :=
    global_chebyshev_coefficient_decay f 1 hf hf_smooth
  have coefficient_sum :
      (∑ j ∈ S, (a j) ^ 2) ≤ Real.pi / 2 := by
    have hdamped :
        (∑ j ∈ S, (a j) ^ 2) ≤
          ∑ j ∈ S, (((j : ℝ) * chebyshev_coefficient f j) ^ 2) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hb_nonneg, hb_le_one⟩ := hb_bounds j hj
      have hb_sq : (b j) ^ 2 ≤ 1 := by
        nlinarith [mul_nonneg hb_nonneg (sub_nonneg.mpr hb_le_one)]
      dsimp [a]
      rw [mul_pow]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hb_sq
          (sq_nonneg ((j : ℝ) * chebyshev_coefficient f j))
    have hfinite :
        (∑ j ∈ S, (((j : ℝ) * chebyshev_coefficient f j) ^ 2)) ≤
          ∑' j : ℕ, (((j : ℝ) * chebyshev_coefficient f j) ^ 2) :=
      hcoeff_summable.sum_le_tsum S (fun j _ => sq_nonneg _)
    have htsum :
        (∑' j : ℕ, (((j : ℝ) * chebyshev_coefficient f j) ^ 2)) ≤
          Real.pi / 2 := by
      simpa using hcoeff_tsum
    exact hdamped.trans (hfinite.trans htsum)
  have cauchy_schwarz :
      R ^ 2 ≤
        (∑ j ∈ S, (a j) ^ 2) * ∑ j ∈ S, (d j) ^ 2 := by
    dsimp [R]
    exact Finset.sum_mul_sq_le_sq_mul_sq S a d
  have R_sq : R ^ 2 ≤ Real.pi / 2 * Γ ^ 2 := by
    calc
      R ^ 2 ≤
          (∑ j ∈ S, (a j) ^ 2) * ∑ j ∈ S, (d j) ^ 2 :=
        cauchy_schwarz
      _ ≤ Real.pi / 2 * ∑ j ∈ S, (d j) ^ 2 :=
        mul_le_mul_of_nonneg_right coefficient_sum
          (Finset.sum_nonneg (fun j _ => sq_nonneg (d j)))
      _ ≤ Real.pi / 2 * Γ ^ 2 := by
        apply mul_le_mul_of_nonneg_left
        · simpa [moment_sum] using hmom
        · positivity
  have hsqrt_sq :
      (Real.sqrt (Real.pi / 2)) ^ 2 = Real.pi / 2 :=
    Real.sq_sqrt (by positivity)
  have A_sq : A ^ 2 ≤ Γ ^ 2 := by
    rw [← scaled_pairing, mul_pow, hsqrt_sq] at R_sq
    have hpi : 0 < Real.pi / 2 := by positivity
    nlinarith
  have A_le : A ≤ Γ := by
    nlinarith [sq_nonneg (A + Γ)]
  exact original_le_approximant.trans (by linarith)

@[blueprint "lem:master-chebyshev-moment-matching-coefficient-decay"
  (statement := /-- Let \(f:\mathbb R\to\mathbb R\) be \(C^\infty\) and
  globally \(\ell\)-Lipschitz. Then the weighted Chebyshev coefficients
  are square summable and satisfy
  \[
    \sum_{j=0}^{\infty}(j c_j(f))^2
      \leq \frac{\pi}{2}\ell^2.
  \] -/)
  (proof := /-- Unfold the coefficient from
  \cref{def:chebyshev-coefficient} and set
  \(g(\theta)=-\sin(\theta)f'(\cos\theta)\). Smoothness and the chain
  rule identify \(g\) as the derivative of
  \(f\circ\cos\). Integration by parts expresses \(j c_j(f)\) as the
  Fourier sine coefficient of \(g\). The normalized sine functions are
  shown directly to be orthonormal on \([0,\pi]\), and expansion of the
  nonnegative integral of the squared finite Fourier remainder gives
  Bessel's inequality. Finally, the Lipschitz derivative bound yields
  \(|g(\theta)|^2\leq\ell^2\sin^2\theta\); integration and passage
  from the bounded partial sums to the infinite sum prove both summability
  and the stated estimate. -/)
  (title := /-- Smooth Chebyshev-Coefficient Decay for the Master Bound -/)
  (latexEnv := "lemma")]
lemma master_chebyshev_moment_matching_coefficient_decay
    (f : ℝ → ℝ) (ℓ : NNReal)
    (hf : LipschitzWith ℓ f) (hf_smooth : ContDiff ℝ ∞ f) :
    Summable (fun j : ℕ =>
      (((j : ℝ) * chebyshev_coefficient f j) ^ 2)) ∧
      (∑' j : ℕ, (((j : ℝ) * chebyshev_coefficient f j) ^ 2)) ≤
        Real.pi / 2 * (ℓ : ℝ) ^ 2 := by
  let g : ℝ → ℝ := fun θ => -(Real.sin θ) * deriv f (Real.cos θ)
  have hg_cont : Continuous g := by
    dsimp [g]
    fun_prop (disch := aesop)
  have hcomp_deriv (θ : ℝ) :
      HasDerivAt (fun t : ℝ => f (Real.cos t)) (g θ) θ := by
    rw [show g θ = deriv f (Real.cos θ) * (-Real.sin θ) by
      dsimp [g]
      ring]
    simpa only [Function.comp_def] using
      (hf_smooth.differentiable (by simp) (Real.cos θ)).hasDerivAt.comp θ
        (Real.hasDerivAt_cos θ)
  have hcoeff (j : ℕ) (hj : 0 < j) :
      (j : ℝ) * chebyshev_coefficient f j =
        -((Real.sqrt (Real.pi / 2))⁻¹ * ∫ θ in (0 : ℝ)..Real.pi,
          g θ * Real.sin ((j : ℝ) * θ)) := by
    rw [chebyshev_coefficient,
      Polynomial.Chebyshev.integral_measureT_eq_integral_cos]
    simp only [normalized_chebyshev_first, hj.ne', ↓reduceIte,
      chebyshev_first, Polynomial.Chebyshev.T_real_cos]
    have hsin_deriv (θ : ℝ) :
        HasDerivAt (fun t : ℝ => Real.sin ((j : ℝ) * t))
          ((j : ℝ) * Real.cos ((j : ℝ) * θ)) θ := by
      rw [show (j : ℝ) * Real.cos ((j : ℝ) * θ) =
        Real.cos ((j : ℝ) * θ) * (j : ℝ) by ring]
      simpa only [Function.comp_def, mul_one] using
        (Real.hasDerivAt_sin ((j : ℝ) * θ)).comp θ
          ((hasDerivAt_id θ).const_mul (j : ℝ))
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun θ _ => hcomp_deriv θ) (fun θ _ => hsin_deriv θ)
      (hg_cont.intervalIntegrable 0 Real.pi)
      ((continuous_const.mul (Real.continuous_cos.comp
        (continuous_const.mul continuous_id))).intervalIntegrable 0 Real.pi)
    simp only [Real.sin_zero, Real.sin_nat_mul_pi, mul_zero, sub_zero,
      zero_sub] at hibp
    calc
      (j : ℝ) * ∫ θ in (0 : ℝ)..Real.pi,
          f (Real.cos θ) *
            (Real.cos ((j : ℤ) * θ) / Real.sqrt (Real.pi / 2)) =
          (Real.sqrt (Real.pi / 2))⁻¹ * ∫ θ in (0 : ℝ)..Real.pi,
            f (Real.cos θ) *
              ((j : ℝ) * Real.cos ((j : ℝ) * θ)) := by
              rw [← intervalIntegral.integral_const_mul,
                ← intervalIntegral.integral_const_mul]
              apply intervalIntegral.integral_congr
              intro θ _
              norm_cast
              ring
      _ = (Real.sqrt (Real.pi / 2))⁻¹ *
            (-∫ θ in (0 : ℝ)..Real.pi,
              g θ * Real.sin ((j : ℝ) * θ)) := by
            rw [hibp]
      _ = -((Real.sqrt (Real.pi / 2))⁻¹ *
            ∫ θ in (0 : ℝ)..Real.pi,
              g θ * Real.sin ((j : ℝ) * θ)) := by ring
  have hcos_int (k : ℤ) :
      (∫ θ in (0 : ℝ)..Real.pi, Real.cos ((k : ℝ) * θ)) =
        if k = 0 then Real.pi else 0 := by
    by_cases hk : k = 0
    · subst k
      simp
    · rw [if_neg hk]
      have hk_real : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      have hanti (x : ℝ) :
          HasDerivAt
            (fun t : ℝ => (k : ℝ)⁻¹ * Real.sin ((k : ℝ) * t))
            (Real.cos ((k : ℝ) * x)) x := by
        have h := ((Real.hasDerivAt_sin ((k : ℝ) * x)).comp x
          ((hasDerivAt_id x).const_mul (k : ℝ))).const_mul (k : ℝ)⁻¹
        have hder : (k : ℝ)⁻¹ *
            (Real.cos ((k : ℝ) * x) * ((k : ℝ) * 1)) =
            Real.cos ((k : ℝ) * x) := by
          field_simp
        rw [← hder]
        simpa only [Function.comp_def] using h
      have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hanti x)
        ((Real.continuous_cos.comp
          (continuous_const.mul continuous_id)).intervalIntegrable 0 Real.pi)
      simpa only [Real.sin_zero, Real.sin_int_mul_pi, mul_zero,
        sub_self] using hfund
  have hsine_orth (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
      (∫ θ in (0 : ℝ)..Real.pi,
        Real.sin ((i : ℝ) * θ) * Real.sin ((j : ℝ) * θ)) =
          if i = j then Real.pi / 2 else 0 := by
    have hprod :
        2 * (∫ θ in (0 : ℝ)..Real.pi,
          Real.sin ((i : ℝ) * θ) * Real.sin ((j : ℝ) * θ)) =
        (∫ θ in (0 : ℝ)..Real.pi,
          Real.cos (((i : ℝ) - (j : ℝ)) * θ)) -
        (∫ θ in (0 : ℝ)..Real.pi,
          Real.cos (((i : ℝ) + (j : ℝ)) * θ)) := by
      rw [← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub]
      · apply intervalIntegral.integral_congr
        intro θ _
        change 2 *
            (Real.sin ((i : ℝ) * θ) * Real.sin ((j : ℝ) * θ)) =
          Real.cos (((i : ℝ) - (j : ℝ)) * θ) -
            Real.cos (((i : ℝ) + (j : ℝ)) * θ)
        rw [show ((i : ℝ) - (j : ℝ)) * θ =
          (i : ℝ) * θ - (j : ℝ) * θ by ring]
        rw [show ((i : ℝ) + (j : ℝ)) * θ =
          (i : ℝ) * θ + (j : ℝ) * θ by ring]
        rw [← mul_assoc]
        exact Real.two_mul_sin_mul_sin ((i : ℝ) * θ) ((j : ℝ) * θ)
      · apply Continuous.intervalIntegrable
        fun_prop
      · apply Continuous.intervalIntegrable
        fun_prop
    have hminus := hcos_int ((i : ℤ) - (j : ℤ))
    have hplus := hcos_int ((i : ℤ) + (j : ℤ))
    simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast] at hminus hplus
    rw [hminus, hplus] at hprod
    by_cases hij : i = j
    · subst j
      simp [hi.ne'] at hprod ⊢
      linarith
    · have hsub : (i : ℤ) - (j : ℤ) ≠ 0 :=
        sub_ne_zero.mpr (by exact_mod_cast hij)
      have hadd : (i : ℤ) + (j : ℤ) ≠ 0 := by positivity
      simp [hij, hsub, hadd] at hprod ⊢
      linarith
  let κ : ℝ := (Real.sqrt (Real.pi / 2))⁻¹
  have hsqrt_sq : (Real.sqrt (Real.pi / 2)) ^ 2 = Real.pi / 2 := by
    rw [Real.sq_sqrt]
    positivity
  have hκ : κ ^ 2 * (Real.pi / 2) = 1 := by
    dsimp [κ]
    rw [inv_pow, hsqrt_sq]
    field_simp
  let e : ℕ → ℝ → ℝ :=
    fun j θ => κ * Real.sin (((j + 1 : ℕ) : ℝ) * θ)
  have he_cont (j : ℕ) : Continuous (e j) := by
    dsimp [e]
    fun_prop
  have horth (i j : ℕ) :
      (∫ θ in (0 : ℝ)..Real.pi, e i θ * e j θ) =
        if i = j then 1 else 0 := by
    rw [show (fun θ => e i θ * e j θ) =
      fun θ => κ ^ 2 * (Real.sin (((i + 1 : ℕ) : ℝ) * θ) *
        Real.sin (((j + 1 : ℕ) : ℝ) * θ)) by
          funext θ
          dsimp [e]
          ring]
    rw [intervalIntegral.integral_const_mul,
      hsine_orth (i + 1) (j + 1) (by omega) (by omega)]
    by_cases hij : i = j
    · simp [hij, hκ]
    · simp [hij]
  let a : ℕ → ℝ := fun j =>
    ∫ θ in (0 : ℝ)..Real.pi, g θ * e j θ
  let S : ℕ → ℝ → ℝ := fun n θ =>
    ∑ j ∈ Finset.range n, a j * e j θ
  have hS_cont (n : ℕ) : Continuous (S n) := by
    dsimp [S]
    fun_prop
  have hgs (n : ℕ) :
      (∫ θ in (0 : ℝ)..Real.pi, g θ * S n θ) =
        ∑ j ∈ Finset.range n, (a j) ^ 2 := by
    rw [show (fun θ => g θ * S n θ) =
      fun θ => ∑ j ∈ Finset.range n, g θ * (a j * e j θ) by
        funext θ
        dsimp [S]
        rw [Finset.mul_sum]]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [show (fun θ => g θ * (a j * e j θ)) =
        fun θ => a j * (g θ * e j θ) by
          funext θ
          ring]
      rw [intervalIntegral.integral_const_mul]
      dsimp [a]
      ring
    · intro j hj
      apply Continuous.intervalIntegrable
      exact hg_cont.mul (continuous_const.mul (he_cont j))
  have hse (n i : ℕ) (hi : i ∈ Finset.range n) :
      (∫ θ in (0 : ℝ)..Real.pi, e i θ * S n θ) = a i := by
    rw [show (fun θ => e i θ * S n θ) =
      fun θ => ∑ j ∈ Finset.range n, a j * (e i θ * e j θ) by
        funext θ
        dsimp [S]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring]
    rw [intervalIntegral.integral_finsetSum]
    · calc
        ∑ j ∈ Finset.range n,
            ∫ θ in (0 : ℝ)..Real.pi, a j * (e i θ * e j θ) =
          ∑ j ∈ Finset.range n, a j *
            (if i = j then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [intervalIntegral.integral_const_mul, horth]
        _ = a i := by
          rw [Finset.sum_eq_single i]
          · simp
          · intro b hb hbi
            simp [hbi.symm]
          · exact fun h => (h hi).elim
    · intro j hj
      apply Continuous.intervalIntegrable
      exact continuous_const.mul ((he_cont i).mul (he_cont j))
  have hss (n : ℕ) :
      (∫ θ in (0 : ℝ)..Real.pi, S n θ * S n θ) =
        ∑ j ∈ Finset.range n, (a j) ^ 2 := by
    rw [show (fun θ => S n θ * S n θ) =
      fun θ => ∑ i ∈ Finset.range n, a i * (e i θ * S n θ) by
        funext θ
        dsimp [S]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [intervalIntegral.integral_const_mul, hse n i hi]
      ring
    · intro i hi
      apply Continuous.intervalIntegrable
      exact continuous_const.mul ((he_cont i).mul (hS_cont n))
  have hpartial (n : ℕ) :
      ∑ j ∈ Finset.range n, (a j) ^ 2 ≤
        ∫ θ in (0 : ℝ)..Real.pi, g θ * g θ := by
    have hres :
        0 ≤ ∫ θ in (0 : ℝ)..Real.pi, (g θ - S n θ) ^ 2 := by
      apply intervalIntegral.integral_nonneg Real.pi_pos.le
      intro θ hθ
      positivity
    have hexpand :
        (∫ θ in (0 : ℝ)..Real.pi, (g θ - S n θ) ^ 2) =
        (∫ θ in (0 : ℝ)..Real.pi, g θ * g θ) -
          2 * (∫ θ in (0 : ℝ)..Real.pi, g θ * S n θ) +
          (∫ θ in (0 : ℝ)..Real.pi, S n θ * S n θ) := by
      rw [show (fun θ => (g θ - S n θ) ^ 2) =
        fun θ => g θ * g θ - 2 * (g θ * S n θ) +
          S n θ * S n θ by
            funext θ
            ring]
      rw [intervalIntegral.integral_add,
        intervalIntegral.integral_sub,
        intervalIntegral.integral_const_mul]
      all_goals apply Continuous.intervalIntegrable
      all_goals fun_prop
    rw [hexpand, hgs n, hss n] at hres
    linarith
  have hg_pointwise (θ : ℝ) :
      g θ * g θ ≤ (ℓ : ℝ) ^ 2 *
        (Real.sin θ * Real.sin θ) := by
    have hd : |deriv f (Real.cos θ)| ≤ (ℓ : ℝ) := by
      simpa only [Real.norm_eq_abs] using
        norm_deriv_le_of_lipschitz (x₀ := Real.cos θ) hf
    have hd_bounds := abs_le.mp hd
    have hd_sq :
        (deriv f (Real.cos θ)) ^ 2 ≤ (ℓ : ℝ) ^ 2 := by
      nlinarith
    have hmul := mul_nonneg (sq_nonneg (Real.sin θ))
      (sub_nonneg.mpr hd_sq)
    dsimp [g]
    nlinarith
  have hg_integral :
      (∫ θ in (0 : ℝ)..Real.pi, g θ * g θ) ≤
        Real.pi / 2 * (ℓ : ℝ) ^ 2 := by
    calc
      (∫ θ in (0 : ℝ)..Real.pi, g θ * g θ) ≤
          ∫ θ in (0 : ℝ)..Real.pi,
            (ℓ : ℝ) ^ 2 * (Real.sin θ * Real.sin θ) := by
        apply intervalIntegral.integral_mono_on
        · exact Real.pi_pos.le
        · apply Continuous.intervalIntegrable
          fun_prop
        · apply Continuous.intervalIntegrable
          fun_prop
        · intro θ hθ
          exact hg_pointwise θ
      _ = (ℓ : ℝ) ^ 2 * (Real.pi / 2) := by
        rw [intervalIntegral.integral_const_mul]
        have hone :
            (∫ θ in (0 : ℝ)..Real.pi,
              Real.sin θ * Real.sin θ) = Real.pi / 2 := by
          simpa using hsine_orth 1 1 (by omega) (by omega)
        rw [hone]
      _ = Real.pi / 2 * (ℓ : ℝ) ^ 2 := by ring
  have ha_summable : Summable (fun j => (a j) ^ 2) :=
    summable_of_sum_range_le (fun j => sq_nonneg (a j))
      (fun n => (hpartial n).trans hg_integral)
  have ha_tsum_le :
      (∑' j : ℕ, (a j) ^ 2) ≤ Real.pi / 2 * (ℓ : ℝ) ^ 2 :=
    ha_summable.tsum_le_of_sum_range_le
      (fun n => (hpartial n).trans hg_integral)
  have hshift (j : ℕ) :
      (((j + 1 : ℕ) : ℝ) *
        chebyshev_coefficient f (j + 1)) ^ 2 = (a j) ^ 2 := by
    rw [hcoeff (j + 1) (by omega)]
    have ha_eq :
        a j = κ * (∫ θ in (0 : ℝ)..Real.pi,
          g θ * Real.sin (((j + 1 : ℕ) : ℝ) * θ)) := by
      dsimp [a, e]
      rw [show (fun θ => g θ *
        (κ * Real.sin (((j + 1 : ℕ) : ℝ) * θ))) =
        fun θ => κ * (g θ *
          Real.sin (((j + 1 : ℕ) : ℝ) * θ)) by
            funext θ
            ring]
      rw [intervalIntegral.integral_const_mul]
    rw [ha_eq]
    dsimp [κ]
    ring
  have htail : Summable (fun j : ℕ =>
      (((j + 1 : ℕ) : ℝ) *
        chebyshev_coefficient f (j + 1)) ^ 2) :=
    ha_summable.congr (fun j => (hshift j).symm)
  have hsum : Summable (fun j : ℕ =>
      ((j : ℝ) * chebyshev_coefficient f j) ^ 2) :=
    (summable_nat_add_iff 1).mp
      (by simpa only [Nat.add_comm] using htail)
  refine ⟨hsum, ?_⟩
  have hdecomp := hsum.sum_add_tsum_nat_add 1
  calc
    (∑' j : ℕ, ((j : ℝ) * chebyshev_coefficient f j) ^ 2) =
        ∑' j : ℕ, (((j + 1 : ℕ) : ℝ) *
          chebyshev_coefficient f (j + 1)) ^ 2 := by
            rw [← hdecomp]
            simp
    _ = ∑' j : ℕ, (a j) ^ 2 := tsum_congr hshift
    _ ≤ Real.pi / 2 * (ℓ : ℝ) ^ 2 := ha_tsum_le

@[blueprint "lem:master-chebyshev-moment-matching-jackson-approximation"
  (statement := /-- Let \(f:\mathbb R\to\mathbb R\) be globally
  \(\ell\)-Lipschitz, and let \(k\) be a positive integer. There is a
  sequence \(b:\mathbb N\to\mathbb R\) such that \(b_0=1\),
  \(0\leq b_j\leq1\) for \(1\leq j\leq k\), and
  \[
    |f(x)-J_{k,b}f(x)|\leq\frac{18\ell}{k}
    \qquad(x\in[-1,1]).
  \] -/)
  (proof := /-- Apply
  \cref{lem:jackson-convolution-expansion} to the continuous Lipschitz
  function to obtain the coefficients and convolution identity.
  The nonnegativity and unit-mass conclusions of
  \cref{lem:jackson-kernel-properties}, together with the Lipschitz bound
  and \(|\cos\theta-\cos(\theta-t)|\leq|t|\), bound the approximation
  error by \(\ell\int_{-\pi}^{\pi}K_k(t)|t|\,dt\).
  The latter integral is at most \(18\ell/k\) by
  \cref{lem:jackson-kernel-first-moment}. Writing
  \(x=\cos(\arccos x)\) gives the result on \([-1,1]\). -/)
  (title := /-- Lipschitz Jackson Approximation for the Master Bound -/)
  (latexEnv := "lemma")]
lemma master_chebyshev_moment_matching_jackson_approximation
    (f : ℝ → ℝ) (ℓ : NNReal) (k : ℕ)
    (hk : 0 < k) (hf : LipschitzWith ℓ f) :
    ∃ b : ℕ → ℝ,
      b 0 = 1 ∧
      (∀ j ∈ Finset.Icc 1 k, 0 ≤ b j ∧ b j ≤ 1) ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        |f x - damped_chebyshev_approximation f k b x| ≤
          18 * (ℓ : ℝ) / (k : ℝ) := by
  obtain ⟨b, hb_zero, hb_bounds, hconvolution⟩ :=
    jackson_convolution_expansion f hf.continuous k hk
  refine ⟨b, hb_zero, hb_bounds, ?_⟩
  intro x hx
  obtain ⟨hK_cont, hK_nonneg, hK_mass, _, _⟩ :=
    jackson_kernel_properties k hk
  let θ : ℝ := Real.arccos x
  have hx_cos : Real.cos θ = x := by
    dsimp [θ]
    exact Real.cos_arccos hx.1 hx.2
  rw [← hx_cos, ← hconvolution θ]
  have hshift_cont : Continuous
      (fun t : ℝ => f (Real.cos (θ - t))) := by
    exact hf.continuous.comp
      (Real.continuous_cos.comp (continuous_const.sub continuous_id))
  have hleft_integrable : MeasureTheory.IntegrableOn
      (fun t : ℝ => f (Real.cos θ) * jackson_kernel k t)
      (Set.Icc (-Real.pi) Real.pi) :=
    (continuous_const.mul hK_cont).integrableOn_Icc
  have hright_integrable : MeasureTheory.IntegrableOn
      (fun t : ℝ => jackson_kernel k t * f (Real.cos (θ - t)))
      (Set.Icc (-Real.pi) Real.pi) :=
    (hK_cont.mul hshift_cont).integrableOn_Icc
  have hmoment_integrable : MeasureTheory.IntegrableOn
      (fun t : ℝ => jackson_kernel k t * |t|)
      (Set.Icc (-Real.pi) Real.pi) :=
    (hK_cont.mul continuous_abs).integrableOn_Icc
  have hpointwise (t : ℝ) :
      |f (Real.cos θ) * jackson_kernel k t -
          jackson_kernel k t * f (Real.cos (θ - t))| ≤
        (ℓ : ℝ) * (jackson_kernel k t * |t|) := by
    have hf_bound := hf.dist_le_mul (Real.cos θ) (Real.cos (θ - t))
    have hf_bound' :
        |f (Real.cos θ) - f (Real.cos (θ - t))| ≤
          (ℓ : ℝ) * |Real.cos θ - Real.cos (θ - t)| := by
      simpa [Real.dist_eq] using hf_bound
    have habs_sin_le_abs (z : ℝ) : |Real.sin z| ≤ |z| := by
      by_cases hz : |z| ≤ 1
      · have hz0 : 0 ≤ |z| := abs_nonneg z
        have hzsq : z ^ 2 ≤ 1 := by
          rw [← sq_abs]
          nlinarith
        have hfactor : 0 ≤ 1 - z ^ 2 / 6 := by nlinarith
        have happ := Real.sin_bound hz
        have habs_poly :
            |z - z ^ 3 / 6| = |z| * (1 - z ^ 2 / 6) := by
          rw [show z - z ^ 3 / 6 = z * (1 - z ^ 2 / 6) by ring,
            abs_mul, abs_of_nonneg hfactor]
        have hzpow : |z| ^ 5 ≤ |z| ^ 3 := by
          have hzsq_abs : |z| ^ 2 ≤ 1 := by nlinarith
          have hnonneg : 0 ≤ |z| ^ 3 := by positivity
          nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hzsq_abs)]
        calc
          |Real.sin z| =
              |(Real.sin z - (z - z ^ 3 / 6)) +
                (z - z ^ 3 / 6)| := by
                  congr 1
                  ring
          _ ≤ |Real.sin z - (z - z ^ 3 / 6)| +
                |z - z ^ 3 / 6| := abs_add_le _ _
          _ ≤ |z| ^ 5 / 100 + |z - z ^ 3 / 6| :=
            add_le_add happ le_rfl
          _ = |z| ^ 5 / 100 + |z| * (1 - z ^ 2 / 6) := by
            rw [habs_poly]
          _ ≤ |z| := by
            rw [← sq_abs z]
            nlinarith
      · have hsone : |Real.sin z| ≤ 1 := Real.abs_sin_le_one z
        exact hsone.trans (le_of_lt (lt_of_not_ge hz))
    have hcos :
        |Real.cos θ - Real.cos (θ - t)| ≤ |t| := by
      rw [Real.cos_sub_cos, abs_mul, abs_mul]
      have hfirst := Real.abs_sin_le_one
        (x := (θ + (θ - t)) / 2)
      have hsecond := habs_sin_le_abs ((θ - (θ - t)) / 2)
      calc
        |-2| * |Real.sin ((θ + (θ - t)) / 2)| *
            |Real.sin ((θ - (θ - t)) / 2)| ≤
            2 * 1 * |(θ - (θ - t)) / 2| := by
              calc
                |-2| * |Real.sin ((θ + (θ - t)) / 2)| *
                    |Real.sin ((θ - (θ - t)) / 2)| =
                    2 * (|Real.sin ((θ + (θ - t)) / 2)| *
                      |Real.sin ((θ - (θ - t)) / 2)|) := by
                        norm_num
                        ring
                _ ≤ 2 * (1 * |(θ - (θ - t)) / 2|) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul hfirst hsecond (abs_nonneg _) (by norm_num))
                    (by norm_num)
                _ = 2 * 1 * |(θ - (θ - t)) / 2| := by ring
        _ = |t| := by
          rw [show θ - (θ - t) = t by ring, abs_div]
          norm_num
          ring
    calc
      |f (Real.cos θ) * jackson_kernel k t -
          jackson_kernel k t * f (Real.cos (θ - t))| =
          jackson_kernel k t *
            |f (Real.cos θ) - f (Real.cos (θ - t))| := by
              rw [show f (Real.cos θ) * jackson_kernel k t -
                  jackson_kernel k t * f (Real.cos (θ - t)) =
                    jackson_kernel k t *
                      (f (Real.cos θ) - f (Real.cos (θ - t))) by ring,
                abs_mul, abs_of_nonneg (hK_nonneg t)]
      _ ≤ jackson_kernel k t * ((ℓ : ℝ) * |t|) := by
        apply mul_le_mul_of_nonneg_left _ (hK_nonneg t)
        exact hf_bound'.trans
          (mul_le_mul_of_nonneg_left hcos (by positivity))
      _ = (ℓ : ℝ) * (jackson_kernel k t * |t|) := by ring
  have hmono :
      (∫ t in Set.Icc (-Real.pi) Real.pi,
        |f (Real.cos θ) * jackson_kernel k t -
          jackson_kernel k t * f (Real.cos (θ - t))|) ≤
      ∫ t in Set.Icc (-Real.pi) Real.pi,
        (ℓ : ℝ) * (jackson_kernel k t * |t|) := by
    apply MeasureTheory.setIntegral_mono_on
      (hleft_integrable.sub hright_integrable).abs
      (hmoment_integrable.const_mul (ℓ : ℝ)) measurableSet_Icc
    intro t _ht
    exact hpointwise t
  calc
    |f (Real.cos θ) -
        ∫ t in Set.Icc (-Real.pi) Real.pi,
          jackson_kernel k t * f (Real.cos (θ - t))| =
        |f (Real.cos θ) *
            (∫ t in Set.Icc (-Real.pi) Real.pi, jackson_kernel k t) -
          ∫ t in Set.Icc (-Real.pi) Real.pi,
            jackson_kernel k t * f (Real.cos (θ - t))| := by
              rw [hK_mass, mul_one]
    _ = |(∫ t in Set.Icc (-Real.pi) Real.pi,
            f (Real.cos θ) * jackson_kernel k t) -
          ∫ t in Set.Icc (-Real.pi) Real.pi,
            jackson_kernel k t * f (Real.cos (θ - t))| := by
              rw [MeasureTheory.integral_const_mul]
    _ = |∫ t in Set.Icc (-Real.pi) Real.pi,
          (f (Real.cos θ) * jackson_kernel k t -
            jackson_kernel k t * f (Real.cos (θ - t)))| := by
              rw [MeasureTheory.integral_sub hleft_integrable
                hright_integrable]
    _ ≤ ∫ t in Set.Icc (-Real.pi) Real.pi,
          |f (Real.cos θ) * jackson_kernel k t -
            jackson_kernel k t * f (Real.cos (θ - t))| :=
      MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ t in Set.Icc (-Real.pi) Real.pi,
          (ℓ : ℝ) * (jackson_kernel k t * |t|) := hmono
    _ = (ℓ : ℝ) *
        (∫ t in Set.Icc (-Real.pi) Real.pi,
          jackson_kernel k t * |t|) := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ (ℓ : ℝ) * (18 / (k : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (jackson_kernel_first_moment k hk) (by positivity)
    _ = 18 * (ℓ : ℝ) / (k : ℝ) := by ring

@[blueprint "lem:master-chebyshev-moment-matching-pairing-bound"
  (statement := /-- Let \(p,q\) be probability measures supported on
  \([-1,1]\), let \(k\) be a positive integer, and let \(\Gamma\geq0\).
  If \(D_k(p,q)^2\leq\Gamma^2\), then every globally
  \(1\)-Lipschitz \(C^\infty\) function \(f:\mathbb R\to\mathbb R\)
  satisfies
  \[
    \int f\,dp-\int f\,dq\leq\frac{36}{k}+\Gamma.
  \] -/)
  (proof := /-- Choose the approximant supplied by
  \cref{lem:master-chebyshev-moment-matching-jackson-approximation}.
  Its uniform error changes the two integrals by at most \(36/k\).
  By \cref{lem:chebyshev-approximation-pairing} and
  \cref{lem:source-normalization-conversion}, the approximant pairing is
  a finite scalar product between the weighted ordinary moment differences
  and the damped weighted coefficients. Cauchy--Schwarz, the bounds on the
  damping factors, and
  \cref{lem:master-chebyshev-moment-matching-coefficient-decay} show that
  its square is at most \(\Gamma^2\). Since \(\Gamma\geq0\), the
  approximant pairing is at most \(\Gamma\), and combining the estimates
  proves the claim. -/)
  (title := /-- Smooth Pairing Bound for the Master Theorem -/)
  (latexEnv := "lemma")]
lemma master_chebyshev_moment_matching_pairing_bound
    (p q : MeasureTheory.ProbabilityMeasure ℝ)
    (hp : (p : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
    (hq : (q : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
    (k : ℕ) (hk : 0 < k) (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hmom : weighted_moment_discrepancy_sq p q k ≤ Γ ^ 2)
    (f : ℝ → ℝ) (hf : LipschitzWith 1 f)
    (hf_smooth : ContDiff ℝ ∞ f) :
    (∫ x, f x ∂(p : MeasureTheory.Measure ℝ)) -
      (∫ x, f x ∂(q : MeasureTheory.Measure ℝ)) ≤
        36 / (k : ℝ) + Γ := by
  obtain ⟨b, _, hb_bounds, happrox⟩ :=
    master_chebyshev_moment_matching_jackson_approximation f 1 k hk hf
  let g : ℝ → ℝ := damped_chebyshev_approximation f k b
  have normalized_continuous (j : ℕ) :
      Continuous (normalized_chebyshev_first j) := by
    unfold normalized_chebyshev_first chebyshev_first
    split_ifs <;> fun_prop
  have hg_cont : Continuous g := by
    unfold g damped_chebyshev_approximation
    fun_prop (disch := exact normalized_continuous _)
  have support_ae
      (r : MeasureTheory.ProbabilityMeasure ℝ)
      (hr : (r : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1) :
      ∀ᵐ x ∂(r : MeasureTheory.Measure ℝ), x ∈ Set.Icc (-1 : ℝ) 1 := by
    filter_upwards [MeasureTheory.Measure.support_mem_ae
      (μ := (r : MeasureTheory.Measure ℝ))] with x hx
    exact hr hx
  have hf_integrable
      (r : MeasureTheory.ProbabilityMeasure ℝ)
      (hr : (r : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1) :
      MeasureTheory.Integrable f (r : MeasureTheory.Measure ℝ) := by
    rw [← MeasureTheory.Measure.restrict_eq_self_of_ae_mem (support_ae r hr)]
    exact hf.continuous.continuousOn.integrableOn_compact isCompact_Icc
  have hg_integrable
      (r : MeasureTheory.ProbabilityMeasure ℝ)
      (hr : (r : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1) :
      MeasureTheory.Integrable g (r : MeasureTheory.Measure ℝ) := by
    rw [← MeasureTheory.Measure.restrict_eq_self_of_ae_mem (support_ae r hr)]
    exact hg_cont.continuousOn.integrableOn_compact isCompact_Icc
  have error_integral
      (r : MeasureTheory.ProbabilityMeasure ℝ)
      (hr : (r : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1) :
      |∫ x, f x - g x ∂(r : MeasureTheory.Measure ℝ)| ≤
        18 / (k : ℝ) := by
    have hdiff := (hf_integrable r hr).sub (hg_integrable r hr)
    calc
      |∫ x, f x - g x ∂(r : MeasureTheory.Measure ℝ)| ≤
          ∫ x, |f x - g x| ∂(r : MeasureTheory.Measure ℝ) :=
        MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ _x, 18 / (k : ℝ) ∂(r : MeasureTheory.Measure ℝ) := by
        apply MeasureTheory.integral_mono_ae hdiff.abs
          (MeasureTheory.integrable_const _)
        filter_upwards [support_ae r hr] with x hx
        simpa [g] using happrox x hx
      _ = 18 / (k : ℝ) := by simp
  let A : ℝ :=
    (∫ x, g x ∂(p : MeasureTheory.Measure ℝ)) -
      ∫ x, g x ∂(q : MeasureTheory.Measure ℝ)
  have original_le_approximant :
      (∫ x, f x ∂(p : MeasureTheory.Measure ℝ)) -
          ∫ x, f x ∂(q : MeasureTheory.Measure ℝ) ≤
        A + 36 / (k : ℝ) := by
    have hp_sub := MeasureTheory.integral_sub
      (hf_integrable p hp) (hg_integrable p hp)
    have hq_sub := MeasureTheory.integral_sub
      (hf_integrable q hq) (hg_integrable q hq)
    have hp_error := error_integral p hp
    have hq_error := error_integral q hq
    have hconstants : 36 / (k : ℝ) = 2 * (18 / (k : ℝ)) := by ring
    dsimp [A]
    rw [hconstants]
    nlinarith [le_abs_self
      (∫ x, f x - g x ∂(p : MeasureTheory.Measure ℝ)),
      neg_le_abs (∫ x, f x - g x ∂(q : MeasureTheory.Measure ℝ))]
  let S : Finset ℕ := Finset.Icc 1 k
  let a : ℕ → ℝ := fun j =>
    b j * ((j : ℝ) * chebyshev_coefficient f j)
  let d : ℕ → ℝ := fun j =>
    (chebyshev_moment p j - chebyshev_moment q j) / (j : ℝ)
  let R : ℝ := ∑ j ∈ S, a j * d j
  have scaled_pairing : Real.sqrt (Real.pi / 2) * A = R := by
    rw [show A =
      (∫ x, damped_chebyshev_approximation f k b x
          ∂(p : MeasureTheory.Measure ℝ)) -
        ∫ x, damped_chebyshev_approximation f k b x
          ∂(q : MeasureTheory.Measure ℝ) by rfl]
    rw [chebyshev_approximation_pairing p q hp hq f k b]
    dsimp [R, S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj_pos : 0 < j := (Finset.mem_Icc.mp hj).1
    have hj_ne : (j : ℝ) ≠ 0 := by positivity
    have hnormalization :=
      source_normalization_conversion p q hp hq j hj_pos
    dsimp [a, d]
    rw [show Real.sqrt (Real.pi / 2) *
        (b j * chebyshev_coefficient f j *
          (normalized_chebyshev_moment p j -
            normalized_chebyshev_moment q j)) =
        b j * chebyshev_coefficient f j *
          (Real.sqrt (Real.pi / 2) *
            (normalized_chebyshev_moment p j -
              normalized_chebyshev_moment q j)) by ring,
      hnormalization]
    field_simp [hj_ne]
  have moment_sum :
      (∑ j ∈ S, (d j) ^ 2) =
        weighted_moment_discrepancy_sq p q k := by
    dsimp [S, d, weighted_moment_discrepancy_sq]
    apply Finset.sum_congr rfl
    intro j hj
    rw [div_pow]
  obtain ⟨hcoeff_summable, hcoeff_tsum⟩ :=
    master_chebyshev_moment_matching_coefficient_decay f 1 hf hf_smooth
  have coefficient_sum :
      (∑ j ∈ S, (a j) ^ 2) ≤ Real.pi / 2 := by
    have hdamped :
        (∑ j ∈ S, (a j) ^ 2) ≤
          ∑ j ∈ S, (((j : ℝ) * chebyshev_coefficient f j) ^ 2) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hb_nonneg, hb_le_one⟩ := hb_bounds j hj
      have hb_sq : (b j) ^ 2 ≤ 1 := by
        nlinarith [mul_nonneg hb_nonneg (sub_nonneg.mpr hb_le_one)]
      dsimp [a]
      rw [mul_pow]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hb_sq
          (sq_nonneg ((j : ℝ) * chebyshev_coefficient f j))
    have hfinite :
        (∑ j ∈ S, (((j : ℝ) * chebyshev_coefficient f j) ^ 2)) ≤
          ∑' j : ℕ, (((j : ℝ) * chebyshev_coefficient f j) ^ 2) :=
      hcoeff_summable.sum_le_tsum S (fun j _ => sq_nonneg _)
    have htsum :
        (∑' j : ℕ, (((j : ℝ) * chebyshev_coefficient f j) ^ 2)) ≤
          Real.pi / 2 := by
      simpa using hcoeff_tsum
    exact hdamped.trans (hfinite.trans htsum)
  have cauchy_schwarz :
      R ^ 2 ≤
        (∑ j ∈ S, (a j) ^ 2) * ∑ j ∈ S, (d j) ^ 2 := by
    dsimp [R]
    exact Finset.sum_mul_sq_le_sq_mul_sq S a d
  have R_sq : R ^ 2 ≤ Real.pi / 2 * Γ ^ 2 := by
    calc
      R ^ 2 ≤
          (∑ j ∈ S, (a j) ^ 2) * ∑ j ∈ S, (d j) ^ 2 :=
        cauchy_schwarz
      _ ≤ Real.pi / 2 * ∑ j ∈ S, (d j) ^ 2 :=
        mul_le_mul_of_nonneg_right coefficient_sum
          (Finset.sum_nonneg (fun j _ => sq_nonneg (d j)))
      _ ≤ Real.pi / 2 * Γ ^ 2 := by
        apply mul_le_mul_of_nonneg_left
        · simpa [moment_sum] using hmom
        · positivity
  have hsqrt_sq :
      (Real.sqrt (Real.pi / 2)) ^ 2 = Real.pi / 2 :=
    Real.sq_sqrt (by positivity)
  have A_sq : A ^ 2 ≤ Γ ^ 2 := by
    rw [← scaled_pairing, mul_pow, hsqrt_sq] at R_sq
    have hpi : 0 < Real.pi / 2 := by positivity
    nlinarith
  have A_le : A ≤ Γ := by
    nlinarith [sq_nonneg (A + Γ)]
  exact original_le_approximant.trans (by linarith)

@[blueprint "thm:master-chebyshev-moment-matching"
  (statement := /-- Let \(p,q\) be probability measures supported on
  \([-1,1]\), let \(k\) be a positive integer, and let \(\Gamma\geq0\).
  If
  \[
    \sum_{j=1}^{k}\frac{(m_j(p)-m_j(q))^2}{j^2}\leq\Gamma^2,
  \]
  then
  \[
    W_1(p,q)\leq\frac{36}{k}+\Gamma.
  \] -/)
  (proof := /-- By \cref{lem:kantorovich-rubinstein-smooth-duality},
  \(W_1(p,q)\) is the supremum of the pairings against globally
  \(1\)-Lipschitz \(C^\infty\) functions. The set of such pairings is
  nonempty because it contains the pairing of the zero function. For a test
  function satisfying the stronger analytic differentiability hypothesis,
  \cref{lem:smooth-lipschitz-pairing-bound} gives the required bound; in the
  complementary case it follows from
  \cref{lem:master-chebyshev-moment-matching-pairing-bound}. Thus every
  member is at most \(36/k+\Gamma\), so the supremum satisfies the same
  bound. -/)
  (title := /-- Sharper Bound for Chebyshev Moment Matching -/)
  (latexEnv := "theorem")]
theorem master_chebyshev_moment_matching
    (p q : MeasureTheory.ProbabilityMeasure ℝ)
    (hp : (p : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
    (hq : (q : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
    (k : ℕ) (hk : 0 < k) (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hmom : weighted_moment_discrepancy_sq p q k ≤ Γ ^ 2) :
    wasserstein_one p q ≤ 36 / (k : ℝ) + Γ := by
  rw [kantorovich_rubinstein_smooth_duality p q hp hq]
  apply csSup_le
  · use 0, fun _ => 0
    exact ⟨(LipschitzWith.const (0 : ℝ)).weaken (by norm_num),
      contDiff_const, by simp⟩
  · rintro a ⟨f, hf, hf_smooth, rfl⟩
    by_cases hf_analytic : ContDiff ℝ ⊤ f
    · exact smooth_lipschitz_pairing_bound
        p q hp hq k hk Γ hΓ hmom f hf hf_analytic
    · exact master_chebyshev_moment_matching_pairing_bound
        p q hp hq k hk Γ hΓ hmom f hf hf_smooth

@[blueprint "thm:coordinatewise-moment-special-case"
  (statement := /-- Let \(p,q\) be probability measures supported on
  \([-1,1]\), let \(k\geq1\), and let \(\Gamma\geq0\). Suppose that for every
  \(j\in\{1,\ldots,k\}\),
  \[
    |m_j(p)-m_j(q)|
      \leq\Gamma\sqrt{\frac{j}{1+\log k}}.
  \]
  Then \(D_k(p,q)^2\leq\Gamma^2\). -/)
  (proof := /-- By \cref{def:weighted-moment-discrepancy-sq}, it suffices
  to bound the weighted sum of the squared moment differences. Since
  \(k\geq1\), one has \(1+\log k>0\). For each
  \(j\in\{1,\ldots,k\}\), both sides of the coordinatewise bound are
  nonnegative. Squaring that bound, using
  \(\bigl(\sqrt{j/(1+\log k)}\bigr)^2=j/(1+\log k)\), and dividing by
  \(j^2>0\) gives
  \[
    \frac{(m_j(p)-m_j(q))^2}{j^2}
      \leq \frac{\Gamma^2}{1+\log k}\frac1j.
  \]
  We prove \(\sum_{j=1}^{n}j^{-1}\leq1+\log n\) for every positive
  integer \(n\) by induction. The case \(n=1\) is an equality. For
  \(n\geq1\), the inequality \(1-x^{-1}\leq\log x\), applied to
  \(x=(n+1)/n\), yields
  \[
    \frac1{n+1}\leq\log(n+1)-\log n.
  \]
  Adding this to the induction hypothesis proves the harmonic estimate at
  \(n+1\). Summing the coordinatewise squared bounds and applying this
  estimate at \(n=k\) gives
  \[
    D_k(p,q)^2\leq
      \frac{\Gamma^2}{1+\log k}(1+\log k)=\Gamma^2,
  \]
  as required. -/)
  (title := /-- Coordinatewise Chebyshev-Moment Special Case -/)
  (latexEnv := "theorem")]
theorem coordinatewise_moment_special_case
    (p q : MeasureTheory.ProbabilityMeasure ℝ)
    (hp : (p : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
    (hq : (q : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
    (k : ℕ) (hk : 0 < k) (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hcoordinate : ∀ j ∈ Finset.Icc 1 k,
      |chebyshev_moment p j - chebyshev_moment q j| ≤
        Γ * Real.sqrt ((j : ℝ) / (1 + Real.log (k : ℝ)))) :
    weighted_moment_discrepancy_sq p q k ≤ Γ ^ 2 := by
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hk
  have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk_real
  have hdenom : 0 < 1 + Real.log (k : ℝ) := by
    linarith
  have hharmonic_general : ∀ n : ℕ, 0 < n →
      ∑ j ∈ Finset.Icc 1 n, (j : ℝ)⁻¹ ≤ 1 + Real.log (n : ℝ) := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
      by_cases hn_zero : n = 0
      · subst n
        norm_num
      · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn_zero
        have hn_real : 0 < (n : ℝ) := by
          exact_mod_cast hn_pos
        have hn_succ_real : 0 < ((n + 1 : ℕ) : ℝ) := by
          positivity
        have hlog_step :
            ((n + 1 : ℕ) : ℝ)⁻¹ ≤
              Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
          calc
            ((n + 1 : ℕ) : ℝ)⁻¹ =
                1 - (((n + 1 : ℕ) : ℝ) / (n : ℝ))⁻¹ := by
              field_simp
              norm_num
            _ ≤ Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) :=
              Real.one_sub_inv_le_log_of_pos
                (div_pos hn_succ_real hn_real)
            _ = Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
              rw [Real.log_div (ne_of_gt hn_succ_real) (ne_of_gt hn_real)]
        rw [Finset.sum_Icc_succ_top (by omega)]
        calc
          (∑ j ∈ Finset.Icc 1 n, (j : ℝ)⁻¹) + ((n + 1 : ℕ) : ℝ)⁻¹ ≤
              (1 + Real.log (n : ℝ)) + ((n + 1 : ℕ) : ℝ)⁻¹ :=
            by linarith [ih hn_pos]
          _ ≤ (1 + Real.log (n : ℝ)) +
              (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) :=
            by linarith
          _ = 1 + Real.log ((n + 1 : ℕ) : ℝ) := by
            ring
  have hharmonic := hharmonic_general k hk
  unfold weighted_moment_discrepancy_sq
  calc
    ∑ j ∈ Finset.Icc 1 k,
        (chebyshev_moment p j - chebyshev_moment q j) ^ 2 / (j : ℝ) ^ 2 ≤
        ∑ j ∈ Finset.Icc 1 k,
          Γ ^ 2 / (1 + Real.log (k : ℝ)) * (j : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      have hj_nat : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hj_real : 0 < (j : ℝ) := by
        exact_mod_cast hj_nat
      have hroot_nonneg :
          0 ≤ Real.sqrt ((j : ℝ) / (1 + Real.log (k : ℝ))) :=
        Real.sqrt_nonneg _
      have hsquared_abs :
          |chebyshev_moment p j - chebyshev_moment q j| ^ 2 ≤
            (Γ * Real.sqrt ((j : ℝ) / (1 + Real.log (k : ℝ)))) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hΓ hroot_nonneg)).2
          (hcoordinate j hj)
      have hsquared :
          (chebyshev_moment p j - chebyshev_moment q j) ^ 2 ≤
            Γ ^ 2 * ((j : ℝ) / (1 + Real.log (k : ℝ))) := by
        calc
          (chebyshev_moment p j - chebyshev_moment q j) ^ 2 =
              |chebyshev_moment p j - chebyshev_moment q j| ^ 2 := by
            rw [sq_abs]
          _ ≤ (Γ * Real.sqrt
              ((j : ℝ) / (1 + Real.log (k : ℝ)))) ^ 2 := hsquared_abs
          _ = Γ ^ 2 * ((j : ℝ) / (1 + Real.log (k : ℝ))) := by
            rw [mul_pow, Real.sq_sqrt]
            positivity
      calc
        (chebyshev_moment p j - chebyshev_moment q j) ^ 2 / (j : ℝ) ^ 2 ≤
            (Γ ^ 2 * ((j : ℝ) / (1 + Real.log (k : ℝ)))) /
              (j : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hsquared (sq_nonneg (j : ℝ))
        _ = Γ ^ 2 / (1 + Real.log (k : ℝ)) * (j : ℝ)⁻¹ := by
          field_simp
    _ = Γ ^ 2 / (1 + Real.log (k : ℝ)) *
        ∑ j ∈ Finset.Icc 1 k, (j : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ Γ ^ 2 / (1 + Real.log (k : ℝ)) *
        (1 + Real.log (k : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hharmonic
        (div_nonneg (sq_nonneg Γ) hdenom.le)
    _ = Γ ^ 2 := by
      field_simp

import Architect
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Interval.Set.OrdConnected

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

@[blueprint "def:binary-decision-loss"
  (statement := /-- The \emph{binary decision loss} at threshold $\tau \in [0,1]$ for an
    outcome $y \in \{0,1\}$ and a decision $\hat y \in \{0,1\}$ is
    $\ell_{\mathrm{bd}}(y, \hat y; \tau) := \tau (1 - y)\hat y + (1 - \tau) y (1 - \hat y)$. -/)
  (title := "Binary decision loss")
  (latexEnv := "definition")]
def binary_decision_loss (τ y yhat : ℝ) : ℝ :=
  τ * (1 - y) * yhat + (1 - τ) * y * (1 - yhat)

@[blueprint "def:risk-bd"
  (statement := /-- Let $(\Omega, \mu)$ be a probability space, $Y : \Omega \to \mathbb{R}$ an
    outcome, $g : \Omega \to \mathbb{R}$ a real forecast, and $\tau \in [0,1]$ a threshold.
    The \emph{plug-in decision risk} of $g$ is
    $R_{\mathrm{bd}}(g; \tau) := \mathbb{E}_\mu\bigl[\ell_{\mathrm{bd}}(Y, \mathbf 1\{g \ge \tau\}; \tau)\bigr]$,
    where the plug-in decision $\mathbf 1\{g(\omega) \ge \tau\}$ equals $1$ when
    $\tau \le g(\omega)$ and $0$ otherwise, and $\ell_{\mathrm{bd}}$ is \cref{def:binary-decision-loss}. -/)
  (title := "Plug-in decision risk")
  (latexEnv := "definition")]
noncomputable def risk_bd (μ : Measure Ω) (Y g : Ω → ℝ) (τ : ℝ) : ℝ :=
  ∫ ω, binary_decision_loss τ (Y ω)
      (Set.indicator {x : ℝ | τ ≤ x} (fun _ => (1 : ℝ)) (g ω)) ∂μ

@[blueprint "def:cutoff-cal-error"
  (statement := /-- Let $(\Omega, \mu)$ be a probability space with outcome $Y : \Omega \to \mathbb{R}$
    and forecast $V : \Omega \to \mathbb{R}$. The \emph{Cutoff Calibration Error} of $V$ is
    $\Delta_{\mathrm{Cutoff}}(V) := \sup_{I} \bigl| \mathbb{E}_\mu\bigl[(Y - V)\,\mathbf 1\{V \in I\}\bigr] \bigr|$,
    where the supremum ranges over all order-connected sets $I \subseteq \mathbb{R}$, i.e. over the
    intervals of $\mathbb{R}$. -/)
  (title := "Cutoff Calibration Error")
  (latexEnv := "definition")]
noncomputable def cutoff_cal_error (μ : Measure Ω) (Y V : Ω → ℝ) : ℝ :=
  ⨆ I : {s : Set ℝ // s.OrdConnected},
    |∫ ω, (Y ω - V ω) * Set.indicator I.1 (fun _ => (1 : ℝ)) (V ω) ∂μ|

@[blueprint "def:monotone-wrapper-risk"
  (statement := /-- Let $(\Omega, \mu)$ be a probability space, $Y, V : \Omega \to \mathbb{R}$, and
    $\tau \in [0,1]$. The \emph{best monotone-wrapper risk} is
    $\inf_{h} R_{\mathrm{bd}}(h \circ V; \tau)$, where the infimum ranges over all monotone maps
    $h : \mathbb{R} \to \mathbb{R}$ sending $[0,1]$ into $[0,1]$, the composition satisfies
    $(h \circ V)(\omega) = h(V(\omega))$, and $R_{\mathrm{bd}}$ is \cref{def:risk-bd}. -/)
  (title := "Best monotone-wrapper risk")
  (latexEnv := "definition")]
noncomputable def monotone_wrapper_risk (μ : Measure Ω) (Y V : Ω → ℝ) (τ : ℝ) : ℝ :=
  ⨅ h : {h : ℝ → ℝ // Monotone h ∧ Set.MapsTo h (Set.Icc 0 1) (Set.Icc 0 1)},
    risk_bd μ Y (fun ω => h.1 (V ω)) τ

@[blueprint "lem:upper-level-set-ord-connected"
  (statement := /-- Let $h : \mathbb{R} \to \mathbb{R}$ be monotone and let $\tau \in \mathbb{R}$.
    Then the super-level set $\{z \in \mathbb{R} : \tau \le h(z)\}$ is order-connected, i.e. an
    interval of $\mathbb{R}$. -/)
  (proof := /-- Let $a, b$ belong to the set with $a \le b$, and let $c$ satisfy $a \le c \le b$.
    Since $h$ is monotone and $a \le c$, we have $h(a) \le h(c)$, hence $\tau \le h(a) \le h(c)$,
    so $c$ belongs to the set. As this holds for every such $a, b, c$, the set is order-connected. -/)
  (title := "Super-level set of a monotone map is an interval")
  (latexEnv := "lemma")]
lemma upper_level_set_ord_connected (h : ℝ → ℝ) (hmono : Monotone h) (τ : ℝ) :
    Set.OrdConnected {z : ℝ | τ ≤ h z} := by
  refine ⟨fun x hx _ _ z hz => ?_⟩
  exact le_trans hx (hmono hz.1)

@[blueprint "lem:lower-level-set-ord-connected"
  (statement := /-- Let $h : \mathbb{R} \to \mathbb{R}$ be monotone and let $\tau \in \mathbb{R}$.
    Then the sub-level set $\{z \in \mathbb{R} : h(z) < \tau\}$ is order-connected, i.e. an
    interval of $\mathbb{R}$. -/)
  (proof := /-- Let $a, b$ belong to the set with $a \le b$, and let $c$ satisfy $a \le c \le b$.
    Since $h$ is monotone and $c \le b$, we have $h(c) \le h(b) < \tau$, so $c$ belongs to the set.
    As this holds for every such $a, b, c$, the set is order-connected. -/)
  (title := "Sub-level set of a monotone map is an interval")
  (latexEnv := "lemma")]
lemma lower_level_set_ord_connected (h : ℝ → ℝ) (hmono : Monotone h) (τ : ℝ) :
    Set.OrdConnected {z : ℝ | h z < τ} := by
  refine ⟨fun x _ y hy z hz => ?_⟩
  exact lt_of_le_of_lt (hmono hz.2) hy

@[blueprint "lem:risk-gap-rearrangement"
  (statement := /-- Let $(\Omega, \mu)$ be a probability space, $Y : \Omega \to \mathbb{R}$ a
    measurable outcome with $Y(\omega) \in \{0,1\}$, $V : \Omega \to \mathbb{R}$ a measurable
    forecast with $V(\omega) \in [0,1]$, $\tau \in [0,1]$, and $h : \mathbb{R} \to \mathbb{R}$
    monotone. Then
    $R_{\mathrm{bd}}(V; \tau) - R_{\mathrm{bd}}(h \circ V; \tau)
      = \mathbb{E}_\mu\bigl[(Y - \tau)\,\mathbf 1\{V < \tau\}\,\mathbf 1\{\tau \le h(V)\}\bigr]
      + \mathbb{E}_\mu\bigl[(\tau - Y)\,\mathbf 1\{\tau \le V\}\,\mathbf 1\{h(V) < \tau\}\bigr]$,
    where $R_{\mathrm{bd}}$ is \cref{def:risk-bd}. -/)
  (proof := /-- This is the rearrangement identity for the decision-risk gap. Pointwise, writing
    $a = \mathbf 1\{v \ge \tau\}$ and $b = \mathbf 1\{w \ge \tau\}$, one has
    $\ell_{\mathrm{bd}}(y, a; \tau) - \ell_{\mathrm{bd}}(y, b; \tau) = (\tau - y)(a - b)$, and
    $a - b = \mathbf 1\{v \ge \tau\}\mathbf 1\{w < \tau\} - \mathbf 1\{v < \tau\}\mathbf 1\{w \ge \tau\}$.
    Substituting $v = V(\omega)$ and $w = h(V(\omega))$ gives, pointwise,
    $\ell_{\mathrm{bd}}(Y, \mathbf 1\{V \ge \tau\}; \tau) - \ell_{\mathrm{bd}}(Y, \mathbf 1\{h(V) \ge \tau\}; \tau)
      = (Y - \tau)\mathbf 1\{V < \tau\}\mathbf 1\{\tau \le h(V)\} + (\tau - Y)\mathbf 1\{\tau \le V\}\mathbf 1\{h(V) < \tau\}$.
    Since $Y$ and $V$ are measurable and bounded and $\mu$ is a probability measure, both decision
    losses are integrable; integrating the identity over $\mu$ and using linearity of the integral
    yields the claim. -/)
  (title := "Rearrangement of the decision-risk gap")
  (latexEnv := "lemma")]
lemma risk_gap_rearrangement (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y V : Ω → ℝ) (hYmeas : Measurable Y) (hVmeas : Measurable V)
    (hYbin : ∀ ω, Y ω = 0 ∨ Y ω = 1) (hVmem : ∀ ω, V ω ∈ Set.Icc (0 : ℝ) 1)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (h : ℝ → ℝ) (hmono : Monotone h) :
    risk_bd μ Y V τ - risk_bd μ Y (fun ω => h (V ω)) τ =
      (∫ ω, (Y ω - τ)
          * Set.indicator {x : ℝ | x < τ} (fun _ => (1 : ℝ)) (V ω)
          * Set.indicator {x : ℝ | τ ≤ x} (fun _ => (1 : ℝ)) (h (V ω)) ∂μ)
      + (∫ ω, (τ - Y ω)
          * Set.indicator {x : ℝ | τ ≤ x} (fun _ => (1 : ℝ)) (V ω)
          * Set.indicator {x : ℝ | x < τ} (fun _ => (1 : ℝ)) (h (V ω)) ∂μ) := by
  have hτ0 : (0 : ℝ) ≤ τ := hτ.1
  have hτ1 : τ ≤ 1 := hτ.2
  have hhVmeas : Measurable (fun ω => h (V ω)) := hmono.measurable.comp hVmeas
  have hint : ∀ (f : Ω → ℝ) (C : ℝ), Measurable f → (∀ ω, |f ω| ≤ C) → Integrable f μ := by
    intro f C hf hb
    refine ⟨hf.aestronglyMeasurable,
      MeasureTheory.HasFiniteIntegral.of_bounded (C := C) (ae_of_all μ ?_)⟩
    intro ω; simpa [Real.norm_eq_abs] using hb ω
  have hindmeas : ∀ (g : Ω → ℝ) (S : Set ℝ), MeasurableSet S → Measurable g →
      Measurable (fun ω => Set.indicator S (fun _ => (1 : ℝ)) (g ω)) := by
    intro g S hS hg
    exact (measurable_const.indicator hS).comp hg
  have hindabs : ∀ (S : Set ℝ) (x : ℝ), |Set.indicator S (fun _ => (1 : ℝ)) x| ≤ 1 := by
    intro S x
    rcases em (x ∈ S) with hx | hx
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hlossmeas : ∀ (g : Ω → ℝ), Measurable g →
      Measurable (fun ω => binary_decision_loss τ (Y ω)
        (Set.indicator {x : ℝ | τ ≤ x} (fun _ => (1 : ℝ)) (g ω))) := by
    intro g hg
    unfold binary_decision_loss
    have hind : Measurable (fun ω => Set.indicator {x : ℝ | τ ≤ x} (fun _ => (1 : ℝ)) (g ω)) :=
      hindmeas g {x : ℝ | τ ≤ x} (measurableSet_le measurable_const measurable_id) hg
    exact ((measurable_const.mul (measurable_const.sub hYmeas)).mul hind).add
      ((measurable_const.mul hYmeas).mul (measurable_const.sub hind))
  have hlossbd : ∀ (g : Ω → ℝ) (ω : Ω),
      |binary_decision_loss τ (Y ω)
        (Set.indicator {x : ℝ | τ ≤ x} (fun _ => (1 : ℝ)) (g ω))| ≤ 1 := by
    intro g ω
    unfold binary_decision_loss
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rcases hYbin ω with hy | hy <;> split_ifs <;>
      rw [hy, abs_le] <;> constructor <;> nlinarith
  have hlossint : ∀ (g : Ω → ℝ), Measurable g →
      Integrable (fun ω => binary_decision_loss τ (Y ω)
        (Set.indicator {x : ℝ | τ ≤ x} (fun _ => (1 : ℝ)) (g ω))) μ :=
    fun g hg => hint _ 1 (hlossmeas g hg) (hlossbd g)
  have htermmeas : ∀ (a : Ω → ℝ) (S T : Set ℝ), Measurable a → MeasurableSet S →
      MeasurableSet T → Measurable (fun ω => a ω
        * Set.indicator S (fun _ => (1 : ℝ)) (V ω)
        * Set.indicator T (fun _ => (1 : ℝ)) (h (V ω))) := by
    intro a S T ha hS hT
    exact (ha.mul (hindmeas V S hS hVmeas)).mul (hindmeas (fun ω => h (V ω)) T hT hhVmeas)
  have htermbd : ∀ (a : Ω → ℝ) (S T : Set ℝ), (∀ ω, |a ω| ≤ 1) → ∀ ω,
      |a ω * Set.indicator S (fun _ => (1 : ℝ)) (V ω)
        * Set.indicator T (fun _ => (1 : ℝ)) (h (V ω))| ≤ 1 := by
    intro a S T ha ω
    rw [abs_mul, abs_mul]
    have h1 : |a ω| * |Set.indicator S (fun _ => (1 : ℝ)) (V ω)| ≤ 1 * 1 :=
      mul_le_mul (ha ω) (hindabs S (V ω)) (abs_nonneg _) (by norm_num)
    have h2 : |a ω| * |Set.indicator S (fun _ => (1 : ℝ)) (V ω)|
        * |Set.indicator T (fun _ => (1 : ℝ)) (h (V ω))| ≤ 1 * 1 :=
      mul_le_mul (by simpa using h1) (hindabs T (h (V ω))) (abs_nonneg _) (by norm_num)
    simpa using h2
  have hYabs : ∀ ω, |Y ω - τ| ≤ 1 := by
    intro ω; rcases hYbin ω with hy | hy <;> rw [hy] <;> rw [abs_le] <;> constructor <;> linarith
  have hτYabs : ∀ ω, |τ - Y ω| ≤ 1 := by
    intro ω; rcases hYbin ω with hy | hy <;> rw [hy] <;> rw [abs_le] <;> constructor <;> linarith
  have hterm1int : Integrable (fun ω => (Y ω - τ)
      * Set.indicator {x : ℝ | x < τ} (fun _ => (1 : ℝ)) (V ω)
      * Set.indicator {x : ℝ | τ ≤ x} (fun _ => (1 : ℝ)) (h (V ω))) μ :=
    hint _ 1 (htermmeas _ _ _ (hYmeas.sub measurable_const)
      (measurableSet_lt measurable_id measurable_const)
      (measurableSet_le measurable_const measurable_id))
      (htermbd _ _ _ hYabs)
  have hterm2int : Integrable (fun ω => (τ - Y ω)
      * Set.indicator {x : ℝ | τ ≤ x} (fun _ => (1 : ℝ)) (V ω)
      * Set.indicator {x : ℝ | x < τ} (fun _ => (1 : ℝ)) (h (V ω))) μ :=
    hint _ 1 (htermmeas _ _ _ (measurable_const.sub hYmeas)
      (measurableSet_le measurable_const measurable_id)
      (measurableSet_lt measurable_id measurable_const))
      (htermbd _ _ _ hτYabs)
  have key : ∀ ω, binary_decision_loss τ (Y ω)
        (Set.indicator {x : ℝ | τ ≤ x} (fun _ => (1 : ℝ)) (V ω))
      - binary_decision_loss τ (Y ω)
        (Set.indicator {x : ℝ | τ ≤ x} (fun _ => (1 : ℝ)) (h (V ω)))
      = (Y ω - τ) * Set.indicator {x : ℝ | x < τ} (fun _ => (1 : ℝ)) (V ω)
          * Set.indicator {x : ℝ | τ ≤ x} (fun _ => (1 : ℝ)) (h (V ω))
        + (τ - Y ω) * Set.indicator {x : ℝ | τ ≤ x} (fun _ => (1 : ℝ)) (V ω)
          * Set.indicator {x : ℝ | x < τ} (fun _ => (1 : ℝ)) (h (V ω)) := by
    intro ω
    unfold binary_decision_loss
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    split_ifs <;> first | (exfalso; linarith) | ring
  unfold risk_bd
  rw [← MeasureTheory.integral_sub (hlossint V hVmeas) (hlossint (fun ω => h (V ω)) hhVmeas)]
  rw [MeasureTheory.integral_congr_ae (ae_of_all μ key)]
  exact MeasureTheory.integral_add hterm1int hterm2int

@[blueprint "lem:risk-gap-le-centered"
  (statement := /-- Let $(\Omega, \mu)$ be a probability space, $Y : \Omega \to \mathbb{R}$ a
    measurable outcome with $Y(\omega) \in \{0,1\}$, $V : \Omega \to \mathbb{R}$ a measurable
    forecast with $V(\omega) \in [0,1]$, $\tau \in [0,1]$, and $h : \mathbb{R} \to \mathbb{R}$
    monotone. Then
    $\mathbb{E}_\mu\bigl[(Y - \tau)\,\mathbf 1\{V < \tau\}\,\mathbf 1\{\tau \le h(V)\}\bigr]
      + \mathbb{E}_\mu\bigl[(\tau - Y)\,\mathbf 1\{\tau \le V\}\,\mathbf 1\{h(V) < \tau\}\bigr]
      \le \mathbb{E}_\mu\bigl[(Y - V)\,\mathbf 1\{V < \tau\}\,\mathbf 1\{\tau \le h(V)\}\bigr]
      + \mathbb{E}_\mu\bigl[(V - Y)\,\mathbf 1\{\tau \le V\}\,\mathbf 1\{h(V) < \tau\}\bigr]$. -/)
  (proof := /-- On the event $\{V < \tau\}$ we have $\tau > V$, hence $-\tau \le -V$ and therefore
    $Y - \tau \le Y - V$; multiplying by the nonnegative factor
    $\mathbf 1\{V < \tau\}\,\mathbf 1\{\tau \le h(V)\}$ preserves the inequality. Likewise, on the
    event $\{\tau \le V\}$ we have $\tau \le V$, hence $\tau - Y \le V - Y$; multiplying by the
    nonnegative factor $\mathbf 1\{\tau \le V\}\,\mathbf 1\{h(V) < \tau\}$ preserves it. Both
    pointwise inequalities involve bounded measurable integrands, which are integrable because
    $\mu$ is a probability measure; integrating each inequality over $\mu$ by monotonicity of the
    integral and adding the two results gives the claim. -/)
  (title := "Centering the decision-risk gap")
  (latexEnv := "lemma")]
lemma risk_gap_le_centered (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y V : Ω → ℝ) (hYmeas : Measurable Y) (hVmeas : Measurable V)
    (hYbin : ∀ ω, Y ω = 0 ∨ Y ω = 1) (hVmem : ∀ ω, V ω ∈ Set.Icc (0 : ℝ) 1)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (h : ℝ → ℝ) (hmono : Monotone h) :
    (∫ ω, (Y ω - τ)
        * Set.indicator {x : ℝ | x < τ} (fun _ => (1 : ℝ)) (V ω)
        * Set.indicator {x : ℝ | τ ≤ x} (fun _ => (1 : ℝ)) (h (V ω)) ∂μ)
    + (∫ ω, (τ - Y ω)
        * Set.indicator {x : ℝ | τ ≤ x} (fun _ => (1 : ℝ)) (V ω)
        * Set.indicator {x : ℝ | x < τ} (fun _ => (1 : ℝ)) (h (V ω)) ∂μ)
    ≤ (∫ ω, (Y ω - V ω)
        * Set.indicator {x : ℝ | x < τ} (fun _ => (1 : ℝ)) (V ω)
        * Set.indicator {x : ℝ | τ ≤ x} (fun _ => (1 : ℝ)) (h (V ω)) ∂μ)
    + (∫ ω, (V ω - Y ω)
        * Set.indicator {x : ℝ | τ ≤ x} (fun _ => (1 : ℝ)) (V ω)
        * Set.indicator {x : ℝ | x < τ} (fun _ => (1 : ℝ)) (h (V ω)) ∂μ) := by
  have hint : ∀ f : Ω → ℝ, Measurable f → (∀ ω, |f ω| ≤ 1) → Integrable f μ := by
    intro f hf hb
    refine Integrable.mono' (integrable_const 1) hf.aestronglyMeasurable (ae_of_all μ ?_)
    intro ω; rw [Real.norm_eq_abs]; exact hb ω
  have hbound : ∀ e a b : ℝ, |e| ≤ 1 → |a| ≤ 1 → |b| ≤ 1 → |e * a * b| ≤ 1 := by
    intro e a b he ha hb
    rw [abs_mul, abs_mul]
    calc |e| * |a| * |b| ≤ 1 * 1 * 1 :=
          mul_le_mul (mul_le_mul he ha (abs_nonneg a) zero_le_one) hb (abs_nonneg b) (by norm_num)
      _ = 1 := by norm_num
  have habs1 : ∀ z : ℝ, |Set.indicator {x : ℝ | x < τ} (fun _ => (1 : ℝ)) z| ≤ 1 := by
    intro z; by_cases hz : z ∈ {x : ℝ | x < τ}
    · rw [Set.indicator_of_mem hz]; norm_num
    · rw [Set.indicator_of_notMem hz]; norm_num
  have habs2 : ∀ z : ℝ, |Set.indicator {x : ℝ | τ ≤ x} (fun _ => (1 : ℝ)) z| ≤ 1 := by
    intro z; by_cases hz : z ∈ {x : ℝ | τ ≤ x}
    · rw [Set.indicator_of_mem hz]; norm_num
    · rw [Set.indicator_of_notMem hz]; norm_num
  have hYtau : ∀ ω, |Y ω - τ| ≤ 1 := by
    intro ω; rw [Set.mem_Icc] at hτ
    rcases hYbin ω with hy | hy <;> rw [hy] <;> rw [abs_le] <;> constructor <;> linarith [hτ.1, hτ.2]
  have hYV : ∀ ω, |Y ω - V ω| ≤ 1 := by
    intro ω; have hv := hVmem ω; rw [Set.mem_Icc] at hv
    rcases hYbin ω with hy | hy <;> rw [hy] <;> rw [abs_le] <;> constructor <;> linarith [hv.1, hv.2]
  have htauY : ∀ ω, |τ - Y ω| ≤ 1 := fun ω => by rw [abs_sub_comm]; exact hYtau ω
  have hVY : ∀ ω, |V ω - Y ω| ≤ 1 := fun ω => by rw [abs_sub_comm]; exact hYV ω
  have hs1 : MeasurableSet {x : ℝ | x < τ} := measurableSet_Iio
  have hs2 : MeasurableSet {x : ℝ | τ ≤ x} := measurableSet_Ici
  have mV1 : Measurable (fun ω => Set.indicator {x : ℝ | x < τ} (fun _ => (1 : ℝ)) (V ω)) :=
    (measurable_const.indicator hs1).comp hVmeas
  have mV2 : Measurable (fun ω => Set.indicator {x : ℝ | τ ≤ x} (fun _ => (1 : ℝ)) (V ω)) :=
    (measurable_const.indicator hs2).comp hVmeas
  have mhV1 : Measurable (fun ω => Set.indicator {x : ℝ | x < τ} (fun _ => (1 : ℝ)) (h (V ω))) :=
    (measurable_const.indicator hs1).comp (hmono.measurable.comp hVmeas)
  have mhV2 : Measurable (fun ω => Set.indicator {x : ℝ | τ ≤ x} (fun _ => (1 : ℝ)) (h (V ω))) :=
    (measurable_const.indicator hs2).comp (hmono.measurable.comp hVmeas)
  refine add_le_add (integral_mono ?_ ?_ ?_) (integral_mono ?_ ?_ ?_)
  · exact hint _ (((hYmeas.sub measurable_const).mul mV1).mul mhV2)
      (fun ω => hbound _ _ _ (hYtau ω) (habs1 _) (habs2 _))
  · exact hint _ (((hYmeas.sub hVmeas).mul mV1).mul mhV2)
      (fun ω => hbound _ _ _ (hYV ω) (habs1 _) (habs2 _))
  · intro ω
    have hB : (0 : ℝ) ≤ Set.indicator {x : ℝ | τ ≤ x} (fun _ => (1 : ℝ)) (h (V ω)) :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    refine mul_le_mul_of_nonneg_right ?_ hB
    by_cases hmem : V ω ∈ {x : ℝ | x < τ}
    · rw [Set.indicator_of_mem hmem, mul_one, mul_one]
      have hlt : V ω < τ := hmem
      exact sub_le_sub_left hlt.le (Y ω)
    · rw [Set.indicator_of_notMem hmem]; simp
  · exact hint _ (((measurable_const.sub hYmeas).mul mV2).mul mhV1)
      (fun ω => hbound _ _ _ (htauY ω) (habs2 _) (habs1 _))
  · exact hint _ (((hVmeas.sub hYmeas).mul mV2).mul mhV1)
      (fun ω => hbound _ _ _ (hVY ω) (habs2 _) (habs1 _))
  · intro ω
    have hD : (0 : ℝ) ≤ Set.indicator {x : ℝ | x < τ} (fun _ => (1 : ℝ)) (h (V ω)) :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    refine mul_le_mul_of_nonneg_right ?_ hD
    by_cases hmem : V ω ∈ {x : ℝ | τ ≤ x}
    · rw [Set.indicator_of_mem hmem, mul_one, mul_one]
      have hle : τ ≤ V ω := hmem
      exact sub_le_sub_right hle (Y ω)
    · rw [Set.indicator_of_notMem hmem]; simp

@[blueprint "lem:abs-centered-integral-le-cal-error"
  (statement := /-- Let $(\Omega, \mu)$ be a probability space with $Y, V : \Omega \to \mathbb{R}$,
    let $I \subseteq \mathbb{R}$ be order-connected, and suppose the family
    $\bigl(\,\bigl|\mathbb{E}_\mu[(Y - V)\,\mathbf 1\{V \in J\}]\bigr|\,\bigr)_{J}$, indexed by the
    order-connected sets $J \subseteq \mathbb{R}$, is bounded above. Then
    $\bigl|\mathbb{E}_\mu[(Y - V)\,\mathbf 1\{V \in I\}]\bigr| \le \Delta_{\mathrm{Cutoff}}(V)$,
    where $\Delta_{\mathrm{Cutoff}}$ is \cref{def:cutoff-cal-error}. -/)
  (proof := /-- By definition, $\Delta_{\mathrm{Cutoff}}(V)$ is the supremum over all order-connected
    sets $J$ of $\bigl|\mathbb{E}_\mu[(Y - V)\,\mathbf 1\{V \in J\}]\bigr|$. The order-connected set
    $I$ is one index of this family, and the family is bounded above by hypothesis, so its value at
    $I$ is at most the supremum. This is exactly the stated inequality. -/)
  (title := "Interval calibration term is bounded by the Cutoff Calibration Error")
  (latexEnv := "lemma")]
lemma abs_centered_integral_le_cal_error (μ : Measure Ω) (Y V : Ω → ℝ)
    (I : Set ℝ) (hI : Set.OrdConnected I)
    (hbdd : BddAbove (Set.range (fun J : {s : Set ℝ // s.OrdConnected} =>
      |∫ ω, (Y ω - V ω) * Set.indicator J.1 (fun _ => (1 : ℝ)) (V ω) ∂μ|))) :
    |∫ ω, (Y ω - V ω) * Set.indicator I (fun _ => (1 : ℝ)) (V ω) ∂μ|
      ≤ cutoff_cal_error μ Y V := by
  exact le_ciSup hbdd (⟨I, hI⟩ : {s : Set ℝ // s.OrdConnected})

@[blueprint "lem:risk-gap-le-two-cal-error-wrapper"
  (statement := /-- Let $(\Omega, \mu)$ be a probability space, $Y : \Omega \to \mathbb{R}$ a
    measurable outcome with $Y(\omega) \in \{0,1\}$, $V : \Omega \to \mathbb{R}$ a measurable
    forecast with $V(\omega) \in [0,1]$, $\tau \in [0,1]$, and $h : \mathbb{R} \to \mathbb{R}$ a
    monotone map with $h([0,1]) \subseteq [0,1]$. Suppose the family defining
    $\Delta_{\mathrm{Cutoff}}(V)$ is bounded above. Then
    $R_{\mathrm{bd}}(V; \tau) - R_{\mathrm{bd}}(h \circ V; \tau) \le 2\,\Delta_{\mathrm{Cutoff}}(V)$,
    where $R_{\mathrm{bd}}$ is \cref{def:risk-bd} and $\Delta_{\mathrm{Cutoff}}$ is
    \cref{def:cutoff-cal-error}. -/)
  (proof := /-- By \cref{lem:risk-gap-rearrangement}, the gap
    $R_{\mathrm{bd}}(V; \tau) - R_{\mathrm{bd}}(h \circ V; \tau)$ equals
    $\mathbb{E}_\mu[(Y - \tau)\mathbf 1\{V < \tau\}\mathbf 1\{\tau \le h(V)\}]
      + \mathbb{E}_\mu[(\tau - Y)\mathbf 1\{\tau \le V\}\mathbf 1\{h(V) < \tau\}]$.
    By \cref{lem:risk-gap-le-centered}, this is at most
    $\mathbb{E}_\mu[(Y - V)\mathbf 1\{V \in I\}] + \mathbb{E}_\mu[(V - Y)\mathbf 1\{V \in I'\}]$,
    where $I = \{z : z < \tau\} \cap \{z : \tau \le h(z)\}$ and
    $I' = \{z : \tau \le z\} \cap \{z : h(z) < \tau\}$, using the pointwise identities
    $\mathbf 1\{V < \tau\}\mathbf 1\{\tau \le h(V)\} = \mathbf 1\{V \in I\}$ and
    $\mathbf 1\{\tau \le V\}\mathbf 1\{h(V) < \tau\} = \mathbf 1\{V \in I'\}$. By
    \cref{lem:upper-level-set-ord-connected} the set $\{z : \tau \le h(z)\}$ is order-connected and
    by \cref{lem:lower-level-set-ord-connected} the set $\{z : h(z) < \tau\}$ is order-connected;
    since $\{z : z < \tau\}$ and $\{z : \tau \le z\}$ are order-connected, their intersections $I$
    and $I'$ are order-connected. Applying \cref{lem:abs-centered-integral-le-cal-error} to $I$
    gives $\mathbb{E}_\mu[(Y - V)\mathbf 1\{V \in I\}] \le \Delta_{\mathrm{Cutoff}}(V)$, and applying
    it to $I'$ gives
    $\mathbb{E}_\mu[(V - Y)\mathbf 1\{V \in I'\}] = -\mathbb{E}_\mu[(Y - V)\mathbf 1\{V \in I'\}]
      \le \Delta_{\mathrm{Cutoff}}(V)$. Adding the two bounds yields $2\,\Delta_{\mathrm{Cutoff}}(V)$. -/)
  (title := "Per-wrapper decision-risk gap bound")
  (latexEnv := "lemma")]
lemma risk_gap_le_two_cal_error_wrapper (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y V : Ω → ℝ) (hYmeas : Measurable Y) (hVmeas : Measurable V)
    (hYbin : ∀ ω, Y ω = 0 ∨ Y ω = 1) (hVmem : ∀ ω, V ω ∈ Set.Icc (0 : ℝ) 1)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (h : ℝ → ℝ) (hmono : Monotone h)
    (hmaps : Set.MapsTo h (Set.Icc 0 1) (Set.Icc 0 1))
    (hbdd : BddAbove (Set.range (fun J : {s : Set ℝ // s.OrdConnected} =>
      |∫ ω, (Y ω - V ω) * Set.indicator J.1 (fun _ => (1 : ℝ)) (V ω) ∂μ|))) :
    risk_bd μ Y V τ - risk_bd μ Y (fun ω => h (V ω)) τ
      ≤ 2 * cutoff_cal_error μ Y V := by
  rw [risk_gap_rearrangement μ Y V hYmeas hVmeas hYbin hVmem τ hτ h hmono]
  refine (risk_gap_le_centered μ Y V hYmeas hVmeas hYbin hVmem τ hτ h hmono).trans ?_
  have hC :
      (∫ ω, (Y ω - V ω)
          * Set.indicator {x : ℝ | x < τ} (fun _ => (1 : ℝ)) (V ω)
          * Set.indicator {x : ℝ | τ ≤ x} (fun _ => (1 : ℝ)) (h (V ω)) ∂μ)
        ≤ cutoff_cal_error μ Y V := by
    have hoc : Set.OrdConnected (Set.Iio τ ∩ {z : ℝ | τ ≤ h z}) :=
      Set.ordConnected_Iio.inter (upper_level_set_ord_connected h hmono τ)
    have hbound :=
      abs_centered_integral_le_cal_error μ Y V (Set.Iio τ ∩ {z : ℝ | τ ≤ h z}) hoc hbdd
    refine le_trans (le_of_eq ?_) (le_trans (le_abs_self _) hbound)
    refine integral_congr_ae (ae_of_all μ (fun ω => ?_))
    simp only [Set.indicator_apply, Set.mem_Iio, Set.mem_inter_iff, Set.mem_setOf_eq]
    split_ifs <;> simp_all
  have hD :
      (∫ ω, (V ω - Y ω)
          * Set.indicator {x : ℝ | τ ≤ x} (fun _ => (1 : ℝ)) (V ω)
          * Set.indicator {x : ℝ | x < τ} (fun _ => (1 : ℝ)) (h (V ω)) ∂μ)
        ≤ cutoff_cal_error μ Y V := by
    have hoc : Set.OrdConnected (Set.Ici τ ∩ {z : ℝ | h z < τ}) :=
      Set.ordConnected_Ici.inter (lower_level_set_ord_connected h hmono τ)
    have hbound :=
      abs_centered_integral_le_cal_error μ Y V (Set.Ici τ ∩ {z : ℝ | h z < τ}) hoc hbdd
    refine le_trans (le_of_eq ?_) (le_trans (neg_le_abs _) hbound)
    rw [← integral_neg]
    refine integral_congr_ae (ae_of_all μ (fun ω => ?_))
    simp only [Set.indicator_apply, Set.mem_Ici, Set.mem_inter_iff, Set.mem_setOf_eq]
    split_ifs <;> simp_all
  have hsum := add_le_add hC hD
  linarith [hsum]

@[blueprint "thm:monotone-risk-gap-le-two-cal-error"
  (statement := /-- Let $(\Omega, \mu)$ be a probability space, $Y : \Omega \to \mathbb{R}$ a
    measurable outcome with $Y(\omega) \in \{0,1\}$, and $V : \Omega \to \mathbb{R}$ a measurable
    forecast with $V(\omega) \in [0,1]$. Suppose the family defining $\Delta_{\mathrm{Cutoff}}(V)$
    is bounded above. Then for every $\tau \in [0,1]$,
    $R_{\mathrm{bd}}(V; \tau) - \inf_{\substack{h : [0,1] \to [0,1]\\ \text{monotone}}}
      R_{\mathrm{bd}}(h \circ V; \tau) \le 2\,\Delta_{\mathrm{Cutoff}}(V)$,
    where $R_{\mathrm{bd}}$ is \cref{def:risk-bd}, the infimum
    $\inf_h R_{\mathrm{bd}}(h \circ V; \tau)$ is \cref{def:monotone-wrapper-risk}, and
    $\Delta_{\mathrm{Cutoff}}$ is \cref{def:cutoff-cal-error}. -/)
  (proof := /-- Fix $\tau \in [0,1]$. By \cref{lem:risk-gap-le-two-cal-error-wrapper}, for every
    monotone map $h : \mathbb{R} \to \mathbb{R}$ with $h([0,1]) \subseteq [0,1]$ we have
    $R_{\mathrm{bd}}(V; \tau) - R_{\mathrm{bd}}(h \circ V; \tau) \le 2\,\Delta_{\mathrm{Cutoff}}(V)$,
    equivalently $R_{\mathrm{bd}}(h \circ V; \tau) \ge R_{\mathrm{bd}}(V; \tau) - 2\,\Delta_{\mathrm{Cutoff}}(V)$.
    The right-hand side is a fixed lower bound independent of $h$, so taking the infimum over all
    such $h$ gives $\inf_h R_{\mathrm{bd}}(h \circ V; \tau) \ge R_{\mathrm{bd}}(V; \tau) - 2\,\Delta_{\mathrm{Cutoff}}(V)$.
    Rearranging this inequality yields the claim. -/)
  (title := "Monotone decision-risk gap bounded by twice the Cutoff Calibration Error")
  (latexEnv := "theorem")]
theorem monotone_risk_gap_le_two_cal_error (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y V : Ω → ℝ) (hYmeas : Measurable Y) (hVmeas : Measurable V)
    (hYbin : ∀ ω, Y ω = 0 ∨ Y ω = 1) (hVmem : ∀ ω, V ω ∈ Set.Icc (0 : ℝ) 1)
    (hbdd : BddAbove (Set.range (fun J : {s : Set ℝ // s.OrdConnected} =>
      |∫ ω, (Y ω - V ω) * Set.indicator J.1 (fun _ => (1 : ℝ)) (V ω) ∂μ|)))
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    risk_bd μ Y V τ - monotone_wrapper_risk μ Y V τ
      ≤ 2 * cutoff_cal_error μ Y V := by
  haveI : Nonempty {h : ℝ → ℝ // Monotone h ∧ Set.MapsTo h (Set.Icc 0 1) (Set.Icc 0 1)} :=
    ⟨⟨id, monotone_id, Set.mapsTo_id _⟩⟩
  have key : risk_bd μ Y V τ - 2 * cutoff_cal_error μ Y V
      ≤ monotone_wrapper_risk μ Y V τ := by
    refine le_ciInf (fun h => ?_)
    have hgap := risk_gap_le_two_cal_error_wrapper μ Y V hYmeas hVmeas hYbin hVmem τ hτ
      h.1 h.2.1 h.2.2 hbdd
    linarith
  linarith [key]

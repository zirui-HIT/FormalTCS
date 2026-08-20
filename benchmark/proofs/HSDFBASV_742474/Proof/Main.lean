import Architect
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.Support

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory
open scoped BigOperators

@[blueprint "def:feature-vector"
  (statement := /-- For a natural number $d$, the feature space is the Euclidean product
  $\mathbb{R}^{d}$, represented as the space of functions from $\operatorname{Fin}(d)$ to
  $\mathbb{R}$. -/)
  (title := /-- Finite-dimensional feature vectors -/)
  (latexEnv := "definition")]
abbrev feature_vector (d : ℕ) := Fin d → ℝ

@[blueprint "def:extended-distribution"
  (statement := /-- Let $\mu$ be a probability measure on $\mathbb{R}^{d}$.  For each
  $j\in\operatorname{Fin}(d)$, let $\mu_j$ be the push-forward of $\mu$ by the $j$th
  coordinate projection.  The extended distribution $\mu^*$ is the product
  $\prod_j\mu_j$. -/)
  (title := /-- Extended product-of-marginals distribution -/)
  (latexEnv := "definition")]
noncomputable def extended_distribution {d : ℕ}
    (μ : ProbabilityMeasure (feature_vector d)) : ProbabilityMeasure (feature_vector d) :=
  ProbabilityMeasure.pi fun j => μ.map (measurable_pi_apply j).aemeasurable

@[blueprint "def:mix-features"
  (statement := /-- Given $S\subseteq\operatorname{Fin}(d)$ and $x,y\in\mathbb{R}^{d}$,
  define $(x_S,y_{S^c})$ to be the feature vector whose $j$th coordinate is $x_j$ for
  $j\in S$ and $y_j$ for $j\notin S$. -/)
  (title := /-- Splicing two feature vectors -/)
  (latexEnv := "definition")]
def mix_features {d : ℕ} (S : Finset (Fin d))
    (x y : feature_vector d) : feature_vector d :=
  fun j => if j ∈ S then x j else y j

@[blueprint "def:interventional-value"
  (statement := /-- Let $\nu$ be a probability measure on $\mathbb{R}^{d}$, let
  $f:\mathbb{R}^{d}\to\mathbb{R}$, let $S\subseteq\operatorname{Fin}(d)$, and let
  $x\in\mathbb{R}^{d}$.  The interventional value of $f$ at $x$ along $S$ is
  \[
    v_S(\nu,f,x)=\int f(x_S,y_{S^c})\,d\nu(y).
  \] -/)
  (title := /-- Interventional value function -/)
  (latexEnv := "definition")]
noncomputable def interventional_value {d : ℕ}
    (ν : ProbabilityMeasure (feature_vector d)) (f : feature_vector d → ℝ)
    (S : Finset (Fin d)) (x : feature_vector d) : ℝ :=
  ∫ y, f (mix_features S x y) ∂(ν : Measure (feature_vector d))

@[blueprint "def:positive-shap-operator"
  (statement := /-- Let $i\in\operatorname{Fin}(d)$.  The positive SHAP operator is
  \[
    (A_i f)(x)=\frac{1}{d}\sum_{S\subseteq\operatorname{Fin}(d)\setminus\{i\}}
    \binom{d-1}{|S|}^{-1}v_{S\cup\{i\}}(\nu,f,x).
  \] -/)
  (title := /-- Positive part of the SHAP operator -/)
  (latexEnv := "definition")]
noncomputable def positive_shap_operator {d : ℕ}
    (ν : ProbabilityMeasure (feature_vector d)) (f : feature_vector d → ℝ)
    (i : Fin d) (x : feature_vector d) : ℝ :=
  (d : ℝ)⁻¹ * ∑ S ∈ (Finset.univ.erase i).powerset,
    (Nat.choose (d - 1) S.card : ℝ)⁻¹ * interventional_value ν f (insert i S) x

@[blueprint "def:negative-shap-operator"
  (statement := /-- Let $i\in\operatorname{Fin}(d)$.  The negative SHAP operator is
  \[
    (B_i f)(x)=\frac{1}{d}\sum_{S\subseteq\operatorname{Fin}(d)\setminus\{i\}}
    \binom{d-1}{|S|}^{-1}v_S(\nu,f,x).
  \] -/)
  (title := /-- Negative part of the SHAP operator -/)
  (latexEnv := "definition")]
noncomputable def negative_shap_operator {d : ℕ}
    (ν : ProbabilityMeasure (feature_vector d)) (f : feature_vector d → ℝ)
    (i : Fin d) (x : feature_vector d) : ℝ :=
  (d : ℝ)⁻¹ * ∑ S ∈ (Finset.univ.erase i).powerset,
    (Nat.choose (d - 1) S.card : ℝ)⁻¹ * interventional_value ν f S x

@[blueprint "def:shap-value"
  (statement := /-- For $i\in\operatorname{Fin}(d)$, the $i$th interventional SHAP value is
  \[
    \phi_i(\nu,f,x)=\frac{1}{d}
    \sum_{S\subseteq\operatorname{Fin}(d)\setminus\{i\}}
    \binom{d-1}{|S|}^{-1}
    \bigl(v_{S\cup\{i\}}(\nu,f,x)-v_S(\nu,f,x)\bigr).
  \] -/)
  (title := /-- Interventional SHAP value -/)
  (latexEnv := "definition")]
noncomputable def shap_value {d : ℕ}
    (ν : ProbabilityMeasure (feature_vector d)) (f : feature_vector d → ℝ)
    (i : Fin d) (x : feature_vector d) : ℝ :=
  (d : ℝ)⁻¹ * ∑ S ∈ (Finset.univ.erase i).powerset,
    (Nat.choose (d - 1) S.card : ℝ)⁻¹ *
      (interventional_value ν f (insert i S) x - interventional_value ν f S x)

@[blueprint "def:aggregate-shap-value"
  (statement := /-- The aggregate SHAP value of feature $i$ under a probability measure
  $\nu$ is the expected absolute pointwise SHAP value,
  \[
    \overline{\phi_i}(\nu,f)=\int |\phi_i(\nu,f,x)|\,d\nu(x).
  \] -/)
  (title := /-- Aggregate SHAP value -/)
  (latexEnv := "definition")]
noncomputable def aggregate_shap_value {d : ℕ}
    (ν : ProbabilityMeasure (feature_vector d)) (f : feature_vector d → ℝ)
    (i : Fin d) : ℝ :=
  ∫ x, |shap_value ν f i x| ∂(ν : Measure (feature_vector d))

@[blueprint "def:is-determined-except-on"
  (statement := /-- Let $\nu$ be a probability measure on $\mathbb{R}^{d}$ and let
  $i\in\operatorname{Fin}(d)$.  A function $g:\mathbb{R}^{d}\to\mathbb{R}$ belongs to
  $F_{\operatorname{Fin}(d)\setminus\{i\}}$ on $\operatorname{supp}(\nu)$ if it is
  measurable and if, whenever $x,y\in\operatorname{supp}(\nu)$ agree in every coordinate
  other than $i$, one has $g(x)=g(y)$. -/)
  (title := /-- Functions determined by all features except one -/)
  (latexEnv := "definition")]
def is_determined_except_on {d : ℕ}
    (ν : ProbabilityMeasure (feature_vector d)) (i : Fin d)
    (g : feature_vector d → ℝ) : Prop :=
  Measurable g ∧
    ∀ x, x ∈ (ν : Measure (feature_vector d)).support →
      ∀ y, y ∈ (ν : Measure (feature_vector d)).support →
        (∀ j, j ≠ i → x j = y j) → g x = g y

@[blueprint "lem:shap-operator-decomposition"
  (statement := /-- Let $d$ be a natural number, let $\nu$ be a probability measure on
  $\mathbb{R}^{d}$, let $f:\mathbb{R}^{d}\to\mathbb{R}$, and let
  $i\in\operatorname{Fin}(d)$.  Then, for every $x\in\mathbb{R}^{d}$,
  \[
    \phi_i(\nu,f,x)=(A_i f)(x)-(B_i f)(x).
  \] -/)
  (proof := /-- Expand the three finite sums from
  \cref{def:shap-value,def:positive-shap-operator,def:negative-shap-operator}.  The two
  summands indexed by each $S$ have the same coefficient; distributivity of finite sums
  therefore identifies the sum of their differences with the difference of their sums. -/)
  (title := /-- SHAP as the difference of two value operators -/)
  (latexEnv := "lemma")]
lemma shap_operator_decomposition {d : ℕ}
    (ν : ProbabilityMeasure (feature_vector d)) (f : feature_vector d → ℝ)
    (i : Fin d) (x : feature_vector d) :
    shap_value ν f i x = positive_shap_operator ν f i x - negative_shap_operator ν f i x := by
  simp only [shap_value, positive_shap_operator, negative_shap_operator, mul_sub,
    Finset.sum_sub_distrib]

@[blueprint "lem:negative-shap-operator-determined"
  (statement := /-- Let $\mu$ be a probability measure on $\mathbb{R}^{d}$, let
  $f:\mathbb{R}^{d}\to[0,1]$ be measurable, and let $i\in\operatorname{Fin}(d)$.  The
  function $B_i f$, formed using the extended distribution $\mu^*$, is measurable and is
  determined on $\operatorname{supp}(\mu^*)$ by all coordinates except $i$. -/)
  (proof := /-- By \cref{def:is-determined-except-on}, it suffices to prove measurability
  and invariance under changing the $i$th coordinate.  For each finite set $S$, the map
  $(x,y)\mapsto(x_S,y_{S^c})$ is measurable coordinatewise by
  \cref{def:mix-features}.  Since $f$ is nonnegative, its Bochner integral in
  \cref{def:interventional-value} is the real part of the corresponding lower integral.
  Measurability of parameterized lower integrals therefore shows that
  $x\mapsto v_S(\mu^*,f,x)$ is measurable.  Hence the finite weighted sum in
  \cref{def:negative-shap-operator} is measurable.

  Now let $x$ and $y$ agree in every coordinate other than $i$.  If
  $S\subseteq\operatorname{Fin}(d)\setminus\{i\}$, then every $j\in S$ differs from
  $i$, so $(x_S,z_{S^c})=(y_S,z_{S^c})$ for every $z$.  Thus the two integrands, their
  interventional values, every weighted summand, and finally the two values of $B_i f$
  are equal. -/)
  (title := /-- The negative SHAP operator discards the selected feature -/)
  (latexEnv := "lemma")]
lemma negative_shap_operator_determined {d : ℕ}
    (μ : ProbabilityMeasure (feature_vector d)) (f : feature_vector d → ℝ)
    (i : Fin d) (hf : Measurable f) (hf_range : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    is_determined_except_on (extended_distribution μ) i
      (negative_shap_operator (extended_distribution μ) f i) := by
  have hinterventional (S : Finset (Fin d)) :
      Measurable (interventional_value (extended_distribution μ) f S) := by
    unfold interventional_value
    have hmix : Measurable
        (fun p : feature_vector d × feature_vector d => mix_features S p.1 p.2) := by
      apply measurable_pi_lambda
      intro j
      simp only [mix_features]
      split
      · fun_prop
      · fun_prop
    have hlin : Measurable
        (fun x => ∫⁻ y, ENNReal.ofReal (f (mix_features S x y))
          ∂(extended_distribution μ : Measure (feature_vector d))) :=
      ((hf.comp hmix).ennreal_ofReal).lintegral_prod_right'
    rw [show (fun x => ∫ y, f (mix_features S x y)
        ∂(extended_distribution μ : Measure (feature_vector d))) =
      (fun x => ENNReal.toReal (∫⁻ y, ENNReal.ofReal (f (mix_features S x y))
        ∂(extended_distribution μ : Measure (feature_vector d)))) by
      funext x
      apply integral_eq_lintegral_of_nonneg_ae
      · exact Filter.Eventually.of_forall (fun y => (hf_range _).1)
      · exact (hf.comp (hmix.comp measurable_prodMk_left)).aestronglyMeasurable]
    exact hlin.ennreal_toReal
  refine ⟨?_, ?_⟩
  · unfold negative_shap_operator
    fun_prop
  · intro x _ y _ hxy
    unfold negative_shap_operator
    congr 1
    apply Finset.sum_congr rfl
    intro S hS
    congr 1
    unfold interventional_value
    apply integral_congr_ae
    filter_upwards [] with z
    apply congrArg f
    funext j
    unfold mix_features
    by_cases hj : j ∈ S
    · simp only [hj, if_true]
      apply hxy j
      intro hji
      subst j
      simpa using (Finset.mem_powerset.mp hS) hj
    · simp only [hj, if_false]

@[blueprint "lem:aggregate-shap-controls-operator-difference"
  (statement := /-- Let $d$ be a natural number, let $\mu$ be a probability measure on
  $\mathbb{R}^{d}$, let $f:\mathbb{R}^{d}\to[0,1]$ be measurable, let
  $i\in\operatorname{Fin}(d)$, and let $\epsilon\in\mathbb{R}$.  If
  $\overline{\phi_i}(\mu^*,f)\leq\epsilon$, then
  \[
    \int\bigl((A_i f)(x)-(B_i f)(x)\bigr)^2\,d\mu^*(x)\leq\epsilon.
  \] -/)
  (proof := /-- Since $i\in\operatorname{Fin}(d)$, one has $d>0$.  Group the subsets of
  $\operatorname{Fin}(d)\setminus\{i\}$ by cardinality.  For each $0\leq k<d$, there are
  $\binom{d-1}{k}$ subsets of cardinality $k$; hence the nonnegative coefficients in
  \cref{def:shap-value} have total mass
  \[
    \frac1d\sum_{k=0}^{d-1}\binom{d-1}{k}\binom{d-1}{k}^{-1}=1.
  \]
  By \cref{def:interventional-value}, the hypothesis $0\leq f\leq1$ and the fact that
  $\mu^*$ is a probability measure imply that every interventional value lies in
  $[0,1]$.  Measurability of the feature-mixing map and of $f$, together with the
  nonnegativity of $f$, also shows through the corresponding parameterized lower
  integral that each interventional value is measurable in $x$.  Thus every difference
  in \cref{def:shap-value} has absolute value at most $1$.  The triangle inequality and
  the preceding coefficient identity give $|\phi_i(\mu^*,f,x)|\leq1$ for every $x$.
  Consequently
  $\phi_i(\mu^*,f,x)^2\leq|\phi_i(\mu^*,f,x)|$ pointwise, and both functions are
  integrable because they are measurable and bounded.  Finally,
  \cref{lem:shap-operator-decomposition} identifies the squared operator difference
  with the squared SHAP value.  Integrating the pointwise inequality and using
  \cref{def:aggregate-shap-value} and the assumed aggregate bound proves the claim. -/)
  (title := /-- Aggregate SHAP control gives squared operator control -/)
  (latexEnv := "lemma")]
lemma aggregate_shap_controls_operator_difference {d : ℕ}
    (μ : ProbabilityMeasure (feature_vector d)) (f : feature_vector d → ℝ)
    (i : Fin d) (ε : ℝ) (hf : Measurable f)
    (hf_range : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (haggregate : aggregate_shap_value (extended_distribution μ) f i ≤ ε) :
    (∫ x, (positive_shap_operator (extended_distribution μ) f i x -
      negative_shap_operator (extended_distribution μ) f i x) ^ 2
      ∂(extended_distribution μ : Measure (feature_vector d))) ≤ ε := by
  have hd : 0 < d := Nat.zero_lt_of_lt i.isLt
  have hweights :
      (d : ℝ)⁻¹ * ∑ S ∈ (Finset.univ.erase i).powerset,
        (Nat.choose (d - 1) S.card : ℝ)⁻¹ = 1 := by
    have hgroup := Finset.sum_powerset_apply_card
      (f := fun k => (Nat.choose (d - 1) k : ℝ)⁻¹)
      (x := Finset.univ.erase i)
    rw [hgroup]
    simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin, Nat.sub_add_cancel hd]
    have hsum :
        (∑ m ∈ Finset.range d,
          (d - 1).choose m • (Nat.choose (d - 1) m : ℝ)⁻¹) =
          ∑ m ∈ Finset.range d, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mem_range] at hm
      have hc : Nat.choose (d - 1) m ≠ 0 := Nat.choose_ne_zero (by omega)
      simp [nsmul_eq_mul, hc]
    rw [hsum]
    simp [Nat.ne_of_gt hd]
  have hinterventional (S : Finset (Fin d)) (x : feature_vector d) :
      interventional_value (extended_distribution μ) f S x ∈ Set.Icc (0 : ℝ) 1 := by
    have hmeas : Measurable (fun y => f (mix_features S x y)) := by
      apply hf.comp
      apply measurable_pi_lambda
      intro j
      simp only [mix_features]
      split <;> fun_prop
    have hint : Integrable (fun y => f (mix_features S x y))
        (extended_distribution μ : Measure (feature_vector d)) := by
      apply Integrable.of_bound hmeas.aestronglyMeasurable 1
      filter_upwards [] with y
      rw [Real.norm_eq_abs]
      exact abs_le.2 ⟨by linarith [(hf_range (mix_features S x y)).1],
        (hf_range (mix_features S x y)).2⟩
    unfold interventional_value
    constructor
    · apply integral_nonneg_of_ae
      filter_upwards [] with y
      exact (hf_range (mix_features S x y)).1
    · calc
        (∫ y, f (mix_features S x y)
            ∂(extended_distribution μ : Measure (feature_vector d))) ≤
            ∫ _y, (1 : ℝ)
              ∂(extended_distribution μ : Measure (feature_vector d)) := by
          apply integral_mono_ae hint (integrable_const 1)
          filter_upwards [] with y
          exact (hf_range (mix_features S x y)).2
        _ = 1 := by simp
  have hinterventional_meas (S : Finset (Fin d)) :
      Measurable (interventional_value (extended_distribution μ) f S) := by
    unfold interventional_value
    have hmix : Measurable
        (fun p : feature_vector d × feature_vector d => mix_features S p.1 p.2) := by
      apply measurable_pi_lambda
      intro j
      simp only [mix_features]
      split <;> fun_prop
    have hlin : Measurable
        (fun x => ∫⁻ y, ENNReal.ofReal (f (mix_features S x y))
          ∂(extended_distribution μ : Measure (feature_vector d))) :=
      ((hf.comp hmix).ennreal_ofReal).lintegral_prod_right'
    rw [show (fun x => ∫ y, f (mix_features S x y)
        ∂(extended_distribution μ : Measure (feature_vector d))) =
      (fun x => ENNReal.toReal (∫⁻ y, ENNReal.ofReal (f (mix_features S x y))
        ∂(extended_distribution μ : Measure (feature_vector d)))) by
      funext x
      apply integral_eq_lintegral_of_nonneg_ae
      · exact Filter.Eventually.of_forall (fun y => (hf_range _).1)
      · exact (hf.comp (hmix.comp measurable_prodMk_left)).aestronglyMeasurable]
    exact hlin.ennreal_toReal
  have hshap (x : feature_vector d) :
      |shap_value (extended_distribution μ) f i x| ≤ 1 := by
    unfold shap_value
    calc
      |(d : ℝ)⁻¹ * ∑ S ∈ (Finset.univ.erase i).powerset,
          (Nat.choose (d - 1) S.card : ℝ)⁻¹ *
            (interventional_value (extended_distribution μ) f (insert i S) x -
              interventional_value (extended_distribution μ) f S x)| =
          (d : ℝ)⁻¹ * |∑ S ∈ (Finset.univ.erase i).powerset,
            (Nat.choose (d - 1) S.card : ℝ)⁻¹ *
              (interventional_value (extended_distribution μ) f (insert i S) x -
                interventional_value (extended_distribution μ) f S x)| := by
        rw [abs_mul, abs_of_nonneg]
        positivity
      _ ≤ (d : ℝ)⁻¹ * ∑ S ∈ (Finset.univ.erase i).powerset,
          |(Nat.choose (d - 1) S.card : ℝ)⁻¹ *
            (interventional_value (extended_distribution μ) f (insert i S) x -
              interventional_value (extended_distribution μ) f S x)| := by
        apply mul_le_mul_of_nonneg_left
          (Finset.abs_sum_le_sum_abs
            (fun S => (Nat.choose (d - 1) S.card : ℝ)⁻¹ *
              (interventional_value (extended_distribution μ) f (insert i S) x -
                interventional_value (extended_distribution μ) f S x))
            (Finset.univ.erase i).powerset)
        positivity
      _ ≤ (d : ℝ)⁻¹ * ∑ S ∈ (Finset.univ.erase i).powerset,
          (Nat.choose (d - 1) S.card : ℝ)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro S hS
        have hdiff :
            |interventional_value (extended_distribution μ) f (insert i S) x -
              interventional_value (extended_distribution μ) f S x| ≤ 1 := by
          rcases hinterventional (insert i S) x with ⟨hpos_lo, hpos_hi⟩
          rcases hinterventional S x with ⟨hneg_lo, hneg_hi⟩
          rw [abs_le]
          constructor <;> linarith
        rw [abs_mul, abs_of_nonneg]
        · simpa using mul_le_mul_of_nonneg_left hdiff
            (show 0 ≤ (Nat.choose (d - 1) S.card : ℝ)⁻¹ by positivity)
        · positivity
      _ = 1 := hweights
  have hshap_meas :
      Measurable (shap_value (extended_distribution μ) f i) := by
    unfold shap_value
    fun_prop
  have habs_meas : Measurable
      (fun x => |shap_value (extended_distribution μ) f i x|) := by
    simpa only [← Real.norm_eq_abs] using hshap_meas.norm
  have habs_int : Integrable
      (fun x => |shap_value (extended_distribution μ) f i x|)
      (extended_distribution μ : Measure (feature_vector d)) := by
    apply Integrable.of_bound habs_meas.aestronglyMeasurable 1
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_abs] using hshap x
  have hsq_meas : Measurable
      (fun x => shap_value (extended_distribution μ) f i x ^ 2) := by
    fun_prop
  have hsq_int : Integrable
      (fun x => shap_value (extended_distribution μ) f i x ^ 2)
      (extended_distribution μ : Measure (feature_vector d)) := by
    apply Integrable.of_bound hsq_meas.aestronglyMeasurable 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_sq, ← sq_abs]
    nlinarith [hshap x, abs_nonneg (shap_value (extended_distribution μ) f i x)]
  calc
    (∫ x, (positive_shap_operator (extended_distribution μ) f i x -
        negative_shap_operator (extended_distribution μ) f i x) ^ 2
        ∂(extended_distribution μ : Measure (feature_vector d))) =
        ∫ x, shap_value (extended_distribution μ) f i x ^ 2
          ∂(extended_distribution μ : Measure (feature_vector d)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [shap_operator_decomposition]
    _ ≤ ∫ x, |shap_value (extended_distribution μ) f i x|
        ∂(extended_distribution μ : Measure (feature_vector d)) := by
      apply integral_mono_ae hsq_int habs_int
      filter_upwards [] with x
      rw [← sq_abs]
      nlinarith [hshap x, abs_nonneg (shap_value (extended_distribution μ) f i x)]
    _ ≤ ε := haggregate

@[blueprint "lem:operator-image-near-determined"
  (statement := /-- Let $d$ be a natural number, let $\mu$ be a probability measure on
  $\mathbb{R}^{d}$, let $f:\mathbb{R}^{d}\to\mathbb{R}$ be measurable with
  $0\leq f(x)\leq 1$ for every $x\in\mathbb{R}^{d}$, let
  $i\in\operatorname{Fin}(d)$, and let $\epsilon\in\mathbb{R}$.  Suppose that the
  aggregate SHAP value computed and averaged under the extended distribution satisfies
  $\overline{\phi_i}(\mu^*,f)\leq\epsilon$.  Then there exists a measurable function
  $h:\mathbb{R}^{d}\to\mathbb{R}$ such that, whenever
  $x,y\in\operatorname{supp}(\mu^*)$ agree in every coordinate other than $i$, one has
  $h(x)=h(y)$, and
  \[
    \int\bigl((A_i f)(x)-h(x)\bigr)^2\,d\mu^*(x)\leq\epsilon.
  \] -/)
  (proof := /-- Take $h=B_i f$.  The function $h$ has the required measurability and
  determination properties by \cref{lem:negative-shap-operator-determined}.  With this
  choice, the asserted error inequality is exactly
  \cref{lem:aggregate-shap-controls-operator-difference}. -/)
  (title := /-- The positive operator image is near the determined subspace -/)
  (latexEnv := "lemma")]
lemma operator_image_near_determined {d : ℕ}
    (μ : ProbabilityMeasure (feature_vector d)) (f : feature_vector d → ℝ)
    (i : Fin d) (ε : ℝ) (hf : Measurable f)
    (hf_range : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (haggregate : aggregate_shap_value (extended_distribution μ) f i ≤ ε) :
    ∃ h : feature_vector d → ℝ,
      is_determined_except_on (extended_distribution μ) i h ∧
      (∫ x, (positive_shap_operator (extended_distribution μ) f i x - h x) ^ 2
        ∂(extended_distribution μ : Measure (feature_vector d))) ≤ ε := by
  refine ⟨negative_shap_operator (extended_distribution μ) f i, ?_, ?_⟩
  · exact negative_shap_operator_determined μ f i hf hf_range
  · exact aggregate_shap_controls_operator_difference μ f i ε hf hf_range haggregate

@[blueprint "lem:spectral-pullback-full-average-determined"
  (statement := /-- Let $\nu$ be a probability measure on $\mathbb{R}^{d}$,
  let $f:\mathbb{R}^{d}\to[0,1]$ be measurable, and fix
  $i\in\operatorname{Fin}(d)$.  Averaging $f$ over the $i$th coordinate
  produces a measurable function determined by every coordinate except
  $i$ on $\operatorname{supp}(\nu)$. -/)
  (proof := /-- By \cref{def:interventional-value}, the asserted function is
  the integral of $f(x_{-i},y_i)$ in the variable $y$.  Nonnegativity permits
  this integral to be written as the real part of a lower integral.  Tonelli
  measurability for lower integrals then proves measurability in $x$.
  The integrand depends on $x$ only through coordinates different from $i$,
  so two such vectors with the same remaining coordinates give identical
  integrals. -/)
  (title := /-- The full complementary average discards one feature -/)
  (latexEnv := "lemma")]
lemma spectral_pullback_full_average_determined {d : ℕ}
    (ν : ProbabilityMeasure (feature_vector d)) (f : feature_vector d → ℝ)
    (i : Fin d) (hf : Measurable f)
    (hf_range : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    is_determined_except_on ν i
      (fun x => interventional_value ν f (Finset.univ.erase i) x) := by
  have hmix : Measurable (fun p : feature_vector d × feature_vector d =>
      mix_features (Finset.univ.erase i) p.1 p.2) := by
    apply measurable_pi_lambda
    intro j
    unfold mix_features
    split
    · exact (measurable_pi_apply j).comp measurable_fst
    · exact (measurable_pi_apply j).comp measurable_snd
  have hparam : Measurable (fun x : feature_vector d =>
      ∫⁻ y, ENNReal.ofReal (f (mix_features (Finset.univ.erase i) x y))
        ∂(ν : Measure (feature_vector d))) :=
    (hf.comp hmix).ennreal_ofReal.lintegral_prod_right'
  constructor
  · have heq : (fun x => interventional_value ν f (Finset.univ.erase i) x) =
        fun x => (∫⁻ y, ENNReal.ofReal
          (f (mix_features (Finset.univ.erase i) x y))
          ∂(ν : Measure (feature_vector d))).toReal := by
      funext x
      unfold interventional_value
      rw [integral_eq_lintegral_of_nonneg_ae]
      · exact Filter.Eventually.of_forall fun y => (hf_range _).1
      · exact (hf.comp (hmix.comp measurable_prodMk_left)).aestronglyMeasurable
    rw [heq]
    exact hparam.ennreal_toReal
  · intro x hx y hy hxy
    unfold interventional_value
    apply integral_congr_ae
    filter_upwards [] with z
    congr 1
    funext j
    unfold mix_features
    split
    · exact hxy j (Finset.ne_of_mem_erase ‹j ∈ Finset.univ.erase i›)
    · rfl

@[blueprint "lem:spectral-pullback-integral-prod-bounded"
  (statement := /-- Let $\mu$ and $\nu$ be probability measures.  If a
  measurable function $F$ on the product is bounded in absolute value by a
  nonnegative constant, then its product integral equals the iterated
  integral in which the second variable is integrated first. -/)
  (proof := /-- Write each real integral as the difference of the lower
  integrals of the positive and negative parts.  The uniform bound makes
  every resulting real-valued function integrable and every lower integral
  finite.  Tonelli's theorem identifies each product lower integral with
  its iterated counterpart, and subtraction gives the stated identity. -/)
  (title := /-- Fubini's theorem for bounded real-valued functions -/)
  (latexEnv := "lemma")]
lemma spectral_pullback_integral_prod_bounded
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (F : α × β → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hF : Measurable F) (hbound : ∀ z, |F z| ≤ C) :
    (∫ z, F z ∂(μ.prod ν)) = ∫ x, ∫ y, F (x, y) ∂ν ∂μ := by
  let P : α → ENNReal := fun x => ∫⁻ y, ENNReal.ofReal (F (x, y)) ∂ν
  let N : α → ENNReal := fun x => ∫⁻ y, ENNReal.ofReal (-F (x, y)) ∂ν
  have hPm : Measurable P := hF.ennreal_ofReal.lintegral_prod_right'
  have hNm : Measurable N := hF.neg.ennreal_ofReal.lintegral_prod_right'
  have hP_bound (x : α) : P x ≤ ENNReal.ofReal C := by
    apply le_trans (lintegral_mono fun y => ENNReal.ofReal_le_ofReal
      (le_trans (le_abs_self _) (hbound (x, y))))
    simp [hC]
  have hN_bound (x : α) : N x ≤ ENNReal.ofReal C := by
    apply le_trans (lintegral_mono fun y => ENNReal.ofReal_le_ofReal
      (le_trans (neg_le_abs _) (hbound (x, y))))
    simp [hC]
  have hP_top : ∀ x, P x ≠ ⊤ := fun x =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hP_bound x)
  have hN_top : ∀ x, N x ≠ ⊤ := fun x =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hN_bound x)
  have hP_int : Integrable (fun x => (P x).toReal) μ := by
    apply Integrable.of_bound hPm.ennreal_toReal.aestronglyMeasurable C
    filter_upwards [] with x
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    simpa [ENNReal.toReal_ofReal hC] using
      ((ENNReal.toReal_le_toReal (hP_top x) ENNReal.ofReal_ne_top).2
        (hP_bound x))
  have hN_int : Integrable (fun x => (N x).toReal) μ := by
    apply Integrable.of_bound hNm.ennreal_toReal.aestronglyMeasurable C
    filter_upwards [] with x
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    simpa [ENNReal.toReal_ofReal hC] using
      ((ENNReal.toReal_le_toReal (hN_top x) ENNReal.ofReal_ne_top).2
        (hN_bound x))
  have hF_int : Integrable F (μ.prod ν) := by
    apply Integrable.of_bound hF.aestronglyMeasurable C
    exact Filter.Eventually.of_forall fun z => by
      simpa [Real.norm_eq_abs] using hbound z
  have hsection (x : α) : Integrable (fun y => F (x, y)) ν := by
    apply Integrable.of_bound
      (hF.comp measurable_prodMk_left).aestronglyMeasurable C
    exact Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hbound (x, y)
  have hinner : (fun x => ∫ y, F (x, y) ∂ν) =
      fun x => (P x).toReal - (N x).toReal := by
    funext x
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hsection x)
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hF_int, hinner,
    integral_sub hP_int hN_int,
    integral_toReal hPm.aemeasurable (Filter.Eventually.of_forall fun x =>
      lt_top_iff_ne_top.2 (hP_top x)),
    integral_toReal hNm.aemeasurable (Filter.Eventually.of_forall fun x =>
      lt_top_iff_ne_top.2 (hN_top x))]
  congr 1
  · exact congrArg ENNReal.toReal
      (lintegral_prod _ hF.ennreal_ofReal.aemeasurable)
  · exact congrArg ENNReal.toReal
      (lintegral_prod _ hF.neg.ennreal_ofReal.aemeasurable)

@[blueprint "lem:spectral-pullback-fiber-inner-nonnegative"
  (statement := /-- Let $\mu$ and $\nu$ be probability measures and let
  $F$ be a bounded measurable real-valued function on their product.  If
  $P(a)=\int F(a,b)\,d\nu(b)$, then
  \[
    0\leq \int F(a,b)P(a)\,d(\mu\otimes\nu)(a,b).
  \] -/)
  (proof := /-- The fiber average $P$ is measurable by writing it as the
  difference of the lower integrals of the positive and negative parts.
  It has the same uniform bound as $F$.  Apply
  \cref{lem:spectral-pullback-integral-prod-bounded} to the product
  $F(a,b)P(a)$.  Its inner integral is $P(a)^2$, whose outer integral is
  nonnegative. -/)
  (title := /-- Positivity of a fiber-averaging projection -/)
  (latexEnv := "lemma")]
lemma spectral_pullback_fiber_inner_nonnegative
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (F : α × β → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hF : Measurable F) (hbound : ∀ z, |F z| ≤ C) :
    0 ≤ ∫ z, F z * (∫ y, F (z.1, y) ∂ν) ∂(μ.prod ν) := by
  let P : α → ℝ := fun x => ∫ y, F (x, y) ∂ν
  let Ppos : α → ENNReal := fun x => ∫⁻ y, ENNReal.ofReal (F (x, y)) ∂ν
  let Pneg : α → ENNReal := fun x => ∫⁻ y, ENNReal.ofReal (-F (x, y)) ∂ν
  have hPposm : Measurable Ppos := hF.ennreal_ofReal.lintegral_prod_right'
  have hPnegm : Measurable Pneg := hF.neg.ennreal_ofReal.lintegral_prod_right'
  have hsection (x : α) : Integrable (fun y => F (x, y)) ν := by
    apply Integrable.of_bound
      (hF.comp measurable_prodMk_left).aestronglyMeasurable C
    exact Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hbound (x, y)
  have hP_eq : P = fun x => (Ppos x).toReal - (Pneg x).toReal := by
    funext x
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hsection x)
  have hPm : Measurable P := by
    rw [hP_eq]
    exact hPposm.ennreal_toReal.sub hPnegm.ennreal_toReal
  have hP_bound (x : α) : |P x| ≤ C := by
    calc
      |P x| = ‖∫ y, F (x, y) ∂ν‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∫ y, ‖F (x, y)‖ ∂ν := norm_integral_le_integral_norm _
      _ ≤ ∫ _ : β, C ∂ν := by
        apply integral_mono_ae (hsection x).norm
          (integrable_const C)
        exact Filter.Eventually.of_forall fun y => by
          simpa [Real.norm_eq_abs] using hbound (x, y)
      _ = C := by simp
  have hprod_m : Measurable (fun z : α × β => F z * P z.1) :=
    hF.mul (hPm.comp measurable_fst)
  have hprod_bound (z : α × β) : |F z * P z.1| ≤ C * C := by
    rw [abs_mul]
    exact mul_le_mul (hbound z) (hP_bound z.1) (abs_nonneg _) hC
  rw [spectral_pullback_integral_prod_bounded μ ν
    (fun z : α × β => F z * P z.1) (C * C) (mul_nonneg hC hC)
    hprod_m hprod_bound]
  apply integral_nonneg
  intro x
  change 0 ≤ ∫ y, F (x, y) * P x ∂ν
  rw [integral_mul_const]
  change 0 ≤ P x * P x
  exact mul_self_nonneg (P x)

@[blueprint "lem:spectral-pullback-interventional-inner-nonnegative"
  (statement := /-- Let $\nu$ be a finite product of probability measures,
  let $S$ be a set of coordinates, and let $u$ be a bounded measurable
  real-valued function.  Then
  \[
    0\leq\int u(x)v_S(\nu,u,x)\,d\nu(x).
  \] -/)
  (proof := /-- Split the product coordinates into $S$ and its complement
  by the measure-preserving product equivalence.  Under this equivalence,
  \cref{def:interventional-value} is the fiber average over the
  complementary coordinates.  The required inequality is therefore
  \cref{lem:spectral-pullback-fiber-inner-nonnegative}; the two changes of
  variables and their iterated integrals are justified by
  \cref{lem:spectral-pullback-integral-prod-bounded}. -/)
  (title := /-- Positivity of interventional averaging -/)
  (latexEnv := "lemma")]
lemma spectral_pullback_interventional_inner_nonnegative {d : ℕ}
    (ρ : Fin d → ProbabilityMeasure ℝ) (u : feature_vector d → ℝ)
    (S : Finset (Fin d)) (C : ℝ) (hC : 0 ≤ C) (hu : Measurable u)
    (hub : ∀ x, |u x| ≤ C) :
    0 ≤ ∫ x, u x * interventional_value (ProbabilityMeasure.pi ρ) u S x
      ∂(ProbabilityMeasure.pi ρ : Measure (feature_vector d)) := by
  let p : Fin d → Prop := fun j => j ∈ S
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ) p
  letI : Fintype (Subtype p) := Subtype.fintype p
  letI : Fintype {j // ¬p j} := Subtype.fintype fun j => ¬p j
  let νS : ProbabilityMeasure (∀ j : Subtype p, ℝ) :=
    ProbabilityMeasure.pi fun j => ρ j
  let νC : ProbabilityMeasure (∀ j : {j // ¬p j}, ℝ) :=
    ProbabilityMeasure.pi fun j => ρ j
  have he : MeasurePreserving e
      (ProbabilityMeasure.pi ρ : Measure (feature_vector d))
      ((νS : Measure (∀ j : Subtype p, ℝ)).prod
        (νC : Measure (∀ j : {j // ¬p j}, ℝ))) := by
    simpa [e, νS, νC] using
      (measurePreserving_piEquivPiSubtypeProd
        (μ := fun j => (ρ j : Measure ℝ)) p)
  have hmix (a : ∀ j : Subtype p, ℝ) (b : ∀ j : {j // ¬p j}, ℝ)
      (a' : ∀ j : Subtype p, ℝ) (b' : ∀ j : {j // ¬p j}, ℝ) :
      mix_features S (e.symm (a, b)) (e.symm (a', b')) =
        e.symm (a, b') := by
    ext j
    by_cases hj : j ∈ S <;> simp [e, p, mix_features, hj]
  have hinter (a : ∀ j : Subtype p, ℝ) (b : ∀ j : {j // ¬p j}, ℝ) :
      interventional_value (ProbabilityMeasure.pi ρ) u S (e.symm (a, b)) =
        ∫ b', u (e.symm (a, b')) ∂(νC : Measure (∀ j : {j // ¬p j}, ℝ)) := by
    unfold interventional_value
    calc
      (∫ y, u (mix_features S (e.symm (a, b)) y)
          ∂(ProbabilityMeasure.pi ρ : Measure (feature_vector d))) =
          ∫ y, u (mix_features S (e.symm (a, b)) (e.symm (e y)))
            ∂(ProbabilityMeasure.pi ρ : Measure (feature_vector d)) := by
              congr 1
              funext y
              simp
      _ = ∫ z, u (mix_features S (e.symm (a, b)) (e.symm z))
            ∂((νS : Measure (∀ j : Subtype p, ℝ)).prod
              (νC : Measure (∀ j : {j // ¬p j}, ℝ))) :=
        he.integral_comp'
          (fun z => u (mix_features S (e.symm (a, b)) (e.symm z)))
      _ = ∫ a', ∫ b', u
            (mix_features S (e.symm (a, b)) (e.symm (a', b')))
            ∂(νC : Measure (∀ j : {j // ¬p j}, ℝ))
            ∂(νS : Measure (∀ j : Subtype p, ℝ)) := by
        apply spectral_pullback_integral_prod_bounded
        · exact hC
        · apply hu.comp
          apply measurable_pi_lambda
          intro j
          unfold mix_features
          split
          · exact measurable_const
          · exact (measurable_pi_apply j).comp e.symm.measurable
        · exact fun z => hub _
      _ = ∫ b', u (e.symm (a, b'))
            ∂(νC : Measure (∀ j : {j // ¬p j}, ℝ)) := by
        simp_rw [hmix]
        simp
  let F : (∀ j : Subtype p, ℝ) × (∀ j : {j // ¬p j}, ℝ) → ℝ :=
    fun z => u (e.symm z)
  have hFm : Measurable F := hu.comp e.symm.measurable
  have hFb : ∀ z, |F z| ≤ C := fun z => hub _
  calc
    0 ≤ ∫ z, F z * (∫ b', F (z.1, b')
          ∂(νC : Measure (∀ j : {j // ¬p j}, ℝ)))
          ∂((νS : Measure (∀ j : Subtype p, ℝ)).prod
            (νC : Measure (∀ j : {j // ¬p j}, ℝ))) :=
      spectral_pullback_fiber_inner_nonnegative
        (νS : Measure (∀ j : Subtype p, ℝ))
        (νC : Measure (∀ j : {j // ¬p j}, ℝ)) F C hC hFm hFb
    _ = ∫ x, u x * interventional_value (ProbabilityMeasure.pi ρ) u S x
          ∂(ProbabilityMeasure.pi ρ : Measure (feature_vector d)) := by
      rw [← he.integral_comp'
        (fun z => F z * (∫ b', F (z.1, b')
          ∂(νC : Measure (∀ j : {j // ¬p j}, ℝ))))]
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [F]
      rw [e.symm_apply_apply]
      change u x * (∫ b', u (e.symm ((e x).1, b'))
        ∂(νC : Measure (∀ j : {j // ¬p j}, ℝ))) =
          u x * interventional_value (ProbabilityMeasure.pi ρ) u S x
      rw [← hinter (e x).1 (e x).2]
      simp

@[blueprint "lem:spectral-pullback-interventional-measurable-bounded"
  (statement := /-- Let $\nu$ be a probability measure, let $u$ be a
  measurable real-valued function bounded in absolute value by a
  nonnegative constant $C$, and let $S$ be a set of coordinates.  Then
  $v_S(\nu,u,\cdot)$ is measurable and is also bounded in absolute value
  by $C$. -/)
  (proof := /-- By \cref{def:interventional-value}, the function is a
  parameterized integral.  Express it as the difference of the lower
  integrals of the positive and negative parts to obtain measurability.
  The norm inequality for the integral, followed by integration of the
  constant bound against the probability measure, gives the same bound
  $C$. -/)
  (title := /-- Measurability and boundedness of interventional averages -/)
  (latexEnv := "lemma")]
lemma spectral_pullback_interventional_measurable_bounded {d : ℕ}
    (ν : ProbabilityMeasure (feature_vector d)) (u : feature_vector d → ℝ)
    (S : Finset (Fin d)) (C : ℝ) (hC : 0 ≤ C) (hu : Measurable u)
    (hub : ∀ x, |u x| ≤ C) :
    Measurable (fun x => interventional_value ν u S x) ∧
      ∀ x, |interventional_value ν u S x| ≤ C := by
  have hmix : Measurable (fun p : feature_vector d × feature_vector d =>
      mix_features S p.1 p.2) := by
    apply measurable_pi_lambda
    intro j
    unfold mix_features
    split
    · exact (measurable_pi_apply j).comp measurable_fst
    · exact (measurable_pi_apply j).comp measurable_snd
  let P : feature_vector d → ENNReal := fun x =>
    ∫⁻ y, ENNReal.ofReal (u (mix_features S x y))
      ∂(ν : Measure (feature_vector d))
  let N : feature_vector d → ENNReal := fun x =>
    ∫⁻ y, ENNReal.ofReal (-u (mix_features S x y))
      ∂(ν : Measure (feature_vector d))
  have hPm : Measurable P := (hu.comp hmix).ennreal_ofReal.lintegral_prod_right'
  have hNm : Measurable N := (hu.comp hmix).neg.ennreal_ofReal.lintegral_prod_right'
  have hsection (x : feature_vector d) :
      Integrable (fun y => u (mix_features S x y))
        (ν : Measure (feature_vector d)) := by
    apply Integrable.of_bound
      (hu.comp (hmix.comp measurable_prodMk_left)).aestronglyMeasurable C
    exact Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hub (mix_features S x y)
  have heq : (fun x => interventional_value ν u S x) =
      fun x => (P x).toReal - (N x).toReal := by
    funext x
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hsection x)
  constructor
  · rw [heq]
    exact hPm.ennreal_toReal.sub hNm.ennreal_toReal
  · intro x
    unfold interventional_value
    calc
      |∫ y, u (mix_features S x y) ∂(ν : Measure (feature_vector d))| =
          ‖∫ y, u (mix_features S x y)
            ∂(ν : Measure (feature_vector d))‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∫ y, ‖u (mix_features S x y)‖
            ∂(ν : Measure (feature_vector d)) :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ _ : feature_vector d, C
            ∂(ν : Measure (feature_vector d)) := by
        apply integral_mono_ae (hsection x).norm (integrable_const C)
        exact Filter.Eventually.of_forall fun y => by
          simpa [Real.norm_eq_abs] using hub (mix_features S x y)
      _ = C := by simp

@[blueprint "lem:spectral-pullback-positive-operator-coercive"
  (statement := /-- Let $\nu$ be a finite product of probability measures,
  let $i$ be a feature, and let $u$ be a bounded measurable real-valued
  function.  Then
  \[
    d^{-1}\int u(x)^2\,d\nu(x)
      \leq \int u(x)(A_i u)(x)\,d\nu(x).
  \] -/)
  (proof := /-- Expand \cref{def:positive-shap-operator}.  Every coefficient
  is nonnegative, and each inner product with an interventional average is
  nonnegative by
  \cref{lem:spectral-pullback-interventional-inner-nonnegative}.  The term
  indexed by the full complement of $i$ is $d^{-1}\int u^2$, because its
  interventional value retains every coordinate.  Keeping this term and
  discarding all remaining nonnegative terms proves the estimate.
  Measurability and integrability of the finite sum follow from
  \cref{lem:spectral-pullback-interventional-measurable-bounded}. -/)
  (title := /-- Coercivity of the positive SHAP operator -/)
  (latexEnv := "lemma")]
lemma spectral_pullback_positive_operator_coercive {d : ℕ}
    (ρ : Fin d → ProbabilityMeasure ℝ) (u : feature_vector d → ℝ)
    (i : Fin d) (C : ℝ) (hC : 0 ≤ C) (hu : Measurable u)
    (hub : ∀ x, |u x| ≤ C) :
    (d : ℝ)⁻¹ * (∫ x, u x ^ 2
      ∂(ProbabilityMeasure.pi ρ : Measure (feature_vector d))) ≤
      ∫ x, u x * positive_shap_operator (ProbabilityMeasure.pi ρ) u i x
        ∂(ProbabilityMeasure.pi ρ : Measure (feature_vector d)) := by
  let ν := ProbabilityMeasure.pi ρ
  let U := Finset.univ.erase i
  have hv (S : Finset (Fin d)) :
      Measurable (fun x => interventional_value ν u S x) ∧
        ∀ x, |interventional_value ν u S x| ≤ C :=
    spectral_pullback_interventional_measurable_bounded ν u S C hC hu hub
  have hint (S : Finset (Fin d)) :
      Integrable (fun x => u x * interventional_value ν u S x)
        (ν : Measure (feature_vector d)) := by
    apply Integrable.of_bound (hu.mul (hv S).1).aestronglyMeasurable (C * C)
    exact Filter.Eventually.of_forall fun x => by
      change |u x * interventional_value ν u S x| ≤ C * C
      rw [abs_mul]
      exact mul_le_mul (hub x) ((hv S).2 x) (abs_nonneg _) hC
  have hnonneg (S : Finset (Fin d)) :
      0 ≤ (Nat.choose (d - 1) S.card : ℝ)⁻¹ *
        (∫ x, u x * interventional_value ν u (insert i S) x
          ∂(ν : Measure (feature_vector d))) := by
    apply mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
    exact spectral_pullback_interventional_inner_nonnegative ρ u
      (insert i S) C hC hu hub
  have hvU (x : feature_vector d) :
      interventional_value ν u (insert i U) x = u x := by
    have hi : insert i U = Finset.univ := by simp [U]
    rw [hi]
    unfold interventional_value
    have hfun : (fun y => u (mix_features Finset.univ x y)) =
        fun _ : feature_vector d => u x := by
      funext y
      congr 1
      funext j
      simp [mix_features]
    rw [hfun]
    simp
  have hsum :
      (∫ x, u x ^ 2 ∂(ν : Measure (feature_vector d))) ≤
        ∑ S ∈ U.powerset, (Nat.choose (d - 1) S.card : ℝ)⁻¹ *
          (∫ x, u x * interventional_value ν u (insert i S) x
            ∂(ν : Measure (feature_vector d))) := by
    have hmem : U ∈ U.powerset := Finset.mem_powerset.2 (Finset.Subset.refl U)
    have hsingle := Finset.single_le_sum
      (fun S hS => hnonneg S) hmem
    have hterm : (Nat.choose (d - 1) U.card : ℝ)⁻¹ *
        (∫ x, u x * interventional_value ν u (insert i U) x
          ∂(ν : Measure (feature_vector d))) =
          ∫ x, u x ^ 2 ∂(ν : Measure (feature_vector d)) := by
      have hc : (Nat.choose (d - 1) U.card : ℝ)⁻¹ = 1 := by
        simp [U]
      rw [hc, one_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hvU]
      ring
    rw [hterm] at hsingle
    exact hsingle
  have hexpand :
      (∫ x, u x * positive_shap_operator ν u i x
        ∂(ν : Measure (feature_vector d))) =
        (d : ℝ)⁻¹ *
          ∑ S ∈ U.powerset, (Nat.choose (d - 1) S.card : ℝ)⁻¹ *
            (∫ x, u x * interventional_value ν u (insert i S) x
              ∂(ν : Measure (feature_vector d))) := by
    unfold positive_shap_operator
    change (∫ x, u x * ((d : ℝ)⁻¹ *
      ∑ S ∈ U.powerset, (Nat.choose (d - 1) S.card : ℝ)⁻¹ *
        interventional_value ν u (insert i S) x)
      ∂(ν : Measure (feature_vector d))) = _
    calc
      (∫ x, u x * ((d : ℝ)⁻¹ *
          ∑ S ∈ U.powerset, (Nat.choose (d - 1) S.card : ℝ)⁻¹ *
            interventional_value ν u (insert i S) x)
          ∂(ν : Measure (feature_vector d))) =
          ∫ x, (d : ℝ)⁻¹ *
            (∑ S ∈ U.powerset, (Nat.choose (d - 1) S.card : ℝ)⁻¹ *
              (u x * interventional_value ν u (insert i S) x))
            ∂(ν : Measure (feature_vector d)) := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [show u x * ((d : ℝ)⁻¹ *
          ∑ S ∈ U.powerset, (Nat.choose (d - 1) S.card : ℝ)⁻¹ *
            interventional_value ν u (insert i S) x) =
          (d : ℝ)⁻¹ * (u x *
            ∑ S ∈ U.powerset, (Nat.choose (d - 1) S.card : ℝ)⁻¹ *
              interventional_value ν u (insert i S) x) by ring]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        ring
      _ = (d : ℝ)⁻¹ * ∫ x,
            (∑ S ∈ U.powerset, (Nat.choose (d - 1) S.card : ℝ)⁻¹ *
              (u x * interventional_value ν u (insert i S) x))
            ∂(ν : Measure (feature_vector d)) := by rw [integral_const_mul]
      _ = (d : ℝ)⁻¹ *
          ∑ S ∈ U.powerset, ∫ x,
            (Nat.choose (d - 1) S.card : ℝ)⁻¹ *
              (u x * interventional_value ν u (insert i S) x)
            ∂(ν : Measure (feature_vector d)) := by
        congr 1
        apply integral_finsetSum
        intro S hS
        exact (hint (insert i S)).const_mul _
      _ = (d : ℝ)⁻¹ *
          ∑ S ∈ U.powerset, (Nat.choose (d - 1) S.card : ℝ)⁻¹ *
            (∫ x, u x * interventional_value ν u (insert i S) x
              ∂(ν : Measure (feature_vector d))) := by
        congr 1
        apply Finset.sum_congr rfl
        intro S hS
        rw [integral_const_mul]
  rw [hexpand]
  exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 (Nat.cast_nonneg d))

@[blueprint "lem:spectral-pullback-full-average-global"
  (statement := /-- Under the hypotheses of
  \cref{lem:spectral-pullback-full-average-determined}, the complementary
  average $g=v_{[d]\setminus\{i\}}(\nu,f,\cdot)$ is globally independent
  of coordinate $i$, and averaging the residual $f-g$ over that coordinate
  gives zero at every point. -/)
  (proof := /-- The first assertion follows directly from
  \cref{def:mix-features}: the evaluation point enters the integral only in
  coordinates different from $i$.  Consequently a second complementary
  average leaves $g$ fixed.  Linearity of the integral then shows that the
  complementary average of $f-g$ is $g-g=0$. -/)
  (title := /-- Global invariance and centering of the complementary average -/)
  (latexEnv := "lemma")]
lemma spectral_pullback_full_average_global {d : ℕ}
    (ν : ProbabilityMeasure (feature_vector d)) (f : feature_vector d → ℝ)
    (i : Fin d) (hf : Measurable f)
    (hf_range : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    let g := fun x => interventional_value ν f (Finset.univ.erase i) x
    (∀ x y, (∀ j, j ≠ i → x j = y j) → g x = g y) ∧
      ∀ x, interventional_value ν (fun z => f z - g z)
        (Finset.univ.erase i) x = 0 := by
  let g := fun x => interventional_value ν f (Finset.univ.erase i) x
  have hg (x y : feature_vector d) (hxy : ∀ j, j ≠ i → x j = y j) :
      g x = g y := by
    unfold g interventional_value
    apply integral_congr_ae
    filter_upwards [] with z
    congr 1
    funext j
    unfold mix_features
    split
    · exact hxy j (Finset.ne_of_mem_erase ‹j ∈ Finset.univ.erase i›)
    · rfl
  constructor
  · exact fun x y => hg x y
  · intro x
    have hfg : Integrable (fun y =>
        f (mix_features (Finset.univ.erase i) x y))
        (ν : Measure (feature_vector d)) := by
      apply Integrable.of_bound (hf.comp (by
          apply measurable_pi_lambda
          intro j
          unfold mix_features
          split
          · exact measurable_const
          · exact measurable_pi_apply j)).aestronglyMeasurable 1
      exact Filter.Eventually.of_forall fun y => by
        change |f (mix_features (Finset.univ.erase i) x y)| ≤ 1
        rw [abs_of_nonneg (hf_range _).1]
        exact (hf_range _).2
    have hgg : Integrable (fun y =>
        g (mix_features (Finset.univ.erase i) x y))
        (ν : Measure (feature_vector d)) := by
      have hconst : (fun y =>
          g (mix_features (Finset.univ.erase i) x y)) =
          fun _ : feature_vector d => g x := by
        funext y
        apply hg
        intro j hji
        simp [mix_features, hji]
      rw [hconst]
      exact integrable_const _
    unfold interventional_value
    change (∫ y, f (mix_features (Finset.univ.erase i) x y) -
      g (mix_features (Finset.univ.erase i) x y)
      ∂(ν : Measure (feature_vector d))) = 0
    rw [integral_sub hfg hgg]
    change (∫ y, f (mix_features (Finset.univ.erase i) x y)
      ∂(ν : Measure (feature_vector d))) -
      (∫ y, g (mix_features (Finset.univ.erase i) x y)
      ∂(ν : Measure (feature_vector d))) = 0
    change g x - _ = 0
    have hconst : (fun y =>
        g (mix_features (Finset.univ.erase i) x y)) =
        fun _ : feature_vector d => g x := by
      funext y
      apply hg
      intro j hji
      simp [mix_features, hji]
    rw [hconst]
    simp

@[blueprint "lem:spectral-pullback-positive-operator-preserves-invariance"
  (statement := /-- Let $\nu$ be a finite product of probability measures.
  If a bounded measurable function $q$ is globally independent of feature
  $i$, then $A_iq$ is measurable and globally independent of feature $i$;
  in particular it is determined off $i$ on $\operatorname{supp}(\nu)$. -/)
  (proof := /-- Every summand in \cref{def:positive-shap-operator} is an
  interventional average over a set containing $i$.  Since $q$ itself does
  not depend on $i$, changing the $i$th coordinate of the evaluation point
  leaves the integrand unchanged.  Measurability of every summand follows
  from \cref{lem:spectral-pullback-interventional-measurable-bounded}, and
  finite sums and scalar multiplication preserve measurability. -/)
  (title := /-- The positive operator preserves feature invariance -/)
  (latexEnv := "lemma")]
lemma spectral_pullback_positive_operator_preserves_invariance {d : ℕ}
    (ρ : Fin d → ProbabilityMeasure ℝ) (q : feature_vector d → ℝ)
    (i : Fin d) (C : ℝ) (hC : 0 ≤ C) (hq : Measurable q)
    (hqb : ∀ x, |q x| ≤ C)
    (hqi : ∀ x y, (∀ j, j ≠ i → x j = y j) → q x = q y) :
    is_determined_except_on (ProbabilityMeasure.pi ρ) i
      (fun x => positive_shap_operator (ProbabilityMeasure.pi ρ) q i x) := by
  let ν := ProbabilityMeasure.pi ρ
  have hv (S : Finset (Fin d)) :
      Measurable (fun x => interventional_value ν q (insert i S) x) :=
    (spectral_pullback_interventional_measurable_bounded
      ν q (insert i S) C hC hq hqb).1
  constructor
  · unfold positive_shap_operator
    fun_prop
  · intro x hx y hy hxy
    unfold positive_shap_operator
    change (d : ℝ)⁻¹ *
      (∑ S ∈ (Finset.univ.erase i).powerset,
        (Nat.choose (d - 1) S.card : ℝ)⁻¹ *
          interventional_value ν q (insert i S) x) =
      (d : ℝ)⁻¹ *
      (∑ S ∈ (Finset.univ.erase i).powerset,
        (Nat.choose (d - 1) S.card : ℝ)⁻¹ *
          interventional_value ν q (insert i S) y)
    apply congrArg (fun z : ℝ => (d : ℝ)⁻¹ * z)
    apply Finset.sum_congr rfl
    intro S hS
    apply congrArg (fun z : ℝ =>
      (Nat.choose (d - 1) S.card : ℝ)⁻¹ * z)
    unfold interventional_value
    apply integral_congr_ae
    filter_upwards [] with z
    apply hqi
    intro j hji
    unfold mix_features
    split
    · by_cases hje : j = i
      · exact (hji hje).elim
      · exact hxy j hji
    · rfl

@[blueprint "lem:spectral-pullback-interventional-integral"
  (statement := /-- Let $\nu$ be a finite product of probability measures,
  let $S$ be a set of coordinates, and let $w$ be a bounded measurable
  real-valued function.  Then interventional averaging preserves its
  expectation:
  \[
    \int v_S(\nu,w,x)\,d\nu(x)=\int w(x)\,d\nu(x).
  \] -/)
  (proof := /-- Split the coordinates into $S$ and its complement by the
  measure-preserving product equivalence.  The interventional value from
  \cref{def:interventional-value} is the inner integral over complementary
  coordinates.  The measurability of this inner average follows from
  \cref{lem:spectral-pullback-interventional-measurable-bounded}, and its
  uniform bound follows from the integral norm inequality.  Applying
  \cref{lem:spectral-pullback-integral-prod-bounded} on both sides and
  integrating the redundant probability coordinate proves the equality. -/)
  (title := /-- Interventional averaging preserves expectation -/)
  (latexEnv := "lemma")]
lemma spectral_pullback_interventional_integral {d : ℕ}
    (ρ : Fin d → ProbabilityMeasure ℝ) (w : feature_vector d → ℝ)
    (S : Finset (Fin d)) (C : ℝ) (hC : 0 ≤ C) (hw : Measurable w)
    (hwb : ∀ x, |w x| ≤ C) :
    (∫ x, interventional_value (ProbabilityMeasure.pi ρ) w S x
      ∂(ProbabilityMeasure.pi ρ : Measure (feature_vector d))) =
      ∫ x, w x ∂(ProbabilityMeasure.pi ρ : Measure (feature_vector d)) := by
  let p : Fin d → Prop := fun j => j ∈ S
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ) p
  letI : Fintype (Subtype p) := Subtype.fintype p
  letI : Fintype {j // ¬p j} := Subtype.fintype fun j => ¬p j
  let νS : ProbabilityMeasure (∀ j : Subtype p, ℝ) :=
    ProbabilityMeasure.pi fun j => ρ j
  let νC : ProbabilityMeasure (∀ j : {j // ¬p j}, ℝ) :=
    ProbabilityMeasure.pi fun j => ρ j
  have he : MeasurePreserving e
      (ProbabilityMeasure.pi ρ : Measure (feature_vector d))
      ((νS : Measure (∀ j : Subtype p, ℝ)).prod
        (νC : Measure (∀ j : {j // ¬p j}, ℝ))) := by
    simpa [e, νS, νC] using
      (measurePreserving_piEquivPiSubtypeProd
        (μ := fun j => (ρ j : Measure ℝ)) p)
  have hmix (a : ∀ j : Subtype p, ℝ) (b : ∀ j : {j // ¬p j}, ℝ)
      (a' : ∀ j : Subtype p, ℝ) (b' : ∀ j : {j // ¬p j}, ℝ) :
      mix_features S (e.symm (a, b)) (e.symm (a', b')) =
        e.symm (a, b') := by
    ext j
    by_cases hj : j ∈ S <;> simp [e, p, mix_features, hj]
  have hinter (a : ∀ j : Subtype p, ℝ) (b : ∀ j : {j // ¬p j}, ℝ) :
      interventional_value (ProbabilityMeasure.pi ρ) w S (e.symm (a, b)) =
        ∫ b', w (e.symm (a, b')) ∂(νC : Measure (∀ j : {j // ¬p j}, ℝ)) := by
    unfold interventional_value
    calc
      (∫ y, w (mix_features S (e.symm (a, b)) y)
          ∂(ProbabilityMeasure.pi ρ : Measure (feature_vector d))) =
          ∫ y, w (mix_features S (e.symm (a, b)) (e.symm (e y)))
            ∂(ProbabilityMeasure.pi ρ : Measure (feature_vector d)) := by
              congr 1
              funext y
              simp
      _ = ∫ z, w (mix_features S (e.symm (a, b)) (e.symm z))
            ∂((νS : Measure (∀ j : Subtype p, ℝ)).prod
              (νC : Measure (∀ j : {j // ¬p j}, ℝ))) :=
        he.integral_comp'
          (fun z => w (mix_features S (e.symm (a, b)) (e.symm z)))
      _ = ∫ a', ∫ b', w
            (mix_features S (e.symm (a, b)) (e.symm (a', b')))
            ∂(νC : Measure (∀ j : {j // ¬p j}, ℝ))
            ∂(νS : Measure (∀ j : Subtype p, ℝ)) := by
        apply spectral_pullback_integral_prod_bounded
        · exact hC
        · apply hw.comp
          apply measurable_pi_lambda
          intro j
          unfold mix_features
          split
          · exact measurable_const
          · exact (measurable_pi_apply j).comp e.symm.measurable
        · exact fun z => hwb _
      _ = ∫ b', w (e.symm (a, b'))
            ∂(νC : Measure (∀ j : {j // ¬p j}, ℝ)) := by
        simp_rw [hmix]
        simp
  have hleft := he.integral_comp' (fun z =>
    interventional_value (ProbabilityMeasure.pi ρ) w S (e.symm z))
  simp only [e.symm_apply_apply] at hleft
  rw [hleft]
  simp_rw [hinter]
  have hbase : Measurable (fun x =>
      interventional_value (ProbabilityMeasure.pi ρ) w S x) :=
    (spectral_pullback_interventional_measurable_bounded
      (ProbabilityMeasure.pi ρ) w S C hC hw hwb).1
  have hPm : Measurable (fun a : (∀ j : Subtype p, ℝ) =>
      ∫ b', w (e.symm (a, b'))
        ∂(νC : Measure (∀ j : {j // ¬p j}, ℝ))) := by
    have hpair : Measurable (fun a : (∀ j : Subtype p, ℝ) =>
        (a, (0 : ∀ j : {j // ¬p j}, ℝ))) :=
      measurable_id.prodMk measurable_const
    have hc := hbase.comp (e.symm.measurable.comp hpair)
    have heq : (fun a : (∀ j : Subtype p, ℝ) =>
        ∫ b', w (e.symm (a, b'))
          ∂(νC : Measure (∀ j : {j // ¬p j}, ℝ))) =
        fun a => interventional_value (ProbabilityMeasure.pi ρ) w S
          (e.symm (a, 0)) := by
      funext a
      rw [hinter]
    rw [heq]
    simpa [Function.comp_def] using hc
  have hPb : ∀ a : (∀ j : Subtype p, ℝ),
      |∫ b', w (e.symm (a, b'))
        ∂(νC : Measure (∀ j : {j // ¬p j}, ℝ))| ≤ C := by
    intro a
    calc
      |∫ b', w (e.symm (a, b'))
          ∂(νC : Measure (∀ j : {j // ¬p j}, ℝ))| =
          ‖∫ b', w (e.symm (a, b'))
            ∂(νC : Measure (∀ j : {j // ¬p j}, ℝ))‖ := by
              rw [Real.norm_eq_abs]
      _ ≤ ∫ b', ‖w (e.symm (a, b'))‖
          ∂(νC : Measure (∀ j : {j // ¬p j}, ℝ)) :=
            norm_integral_le_integral_norm _
      _ ≤ ∫ _ : (∀ j : {j // ¬p j}, ℝ), C
          ∂(νC : Measure (∀ j : {j // ¬p j}, ℝ)) := by
            apply integral_mono_ae
            · apply Integrable.norm
              apply Integrable.of_bound
                (hw.comp (e.symm.measurable.comp
                  measurable_prodMk_left)).aestronglyMeasurable C
              exact Filter.Eventually.of_forall fun b => by
                simpa [Real.norm_eq_abs] using hwb _
            · exact integrable_const C
            · exact Filter.Eventually.of_forall fun b => by
                simpa [Real.norm_eq_abs] using hwb _
      _ = C := by simp
  rw [spectral_pullback_integral_prod_bounded
    (νS : Measure (∀ j : Subtype p, ℝ))
    (νC : Measure (∀ j : {j // ¬p j}, ℝ))
    (fun z => ∫ b', w (e.symm (z.1, b'))
      ∂(νC : Measure (∀ j : {j // ¬p j}, ℝ))) C hC]
  · simp
    have hright := he.integral_comp' (fun z => w (e.symm z))
    simp only [e.symm_apply_apply] at hright
    change _ = ∫ x, w x
      ∂(ProbabilityMeasure.pi ρ : Measure (feature_vector d))
    rw [hright]
    symm
    apply spectral_pullback_integral_prod_bounded
    · exact hC
    · exact hw.comp e.symm.measurable
    · exact fun z => hwb _
  · exact hPm.comp measurable_fst
  · exact fun z => hPb z.1

@[blueprint "lem:spectral-pullback-resampling-support"
  (statement := /-- Let $\nu$ be a finite product of probability measures
  and fix a feature $i$.  For $\nu$-almost every $x$, one has
  $x\in\operatorname{supp}(\nu)$ and, for $\nu$-almost every $y$, the
  vector obtained from $x$ by replacing coordinate $i$ with that of $y$
  also belongs to $\operatorname{supp}(\nu)$. -/)
  (proof := /-- The complement of the support has measure zero.  Apply
  \cref{lem:spectral-pullback-interventional-integral} to its measurable
  indicator and the complementary coordinate set.  By
  \cref{lem:spectral-pullback-interventional-measurable-bounded}, the
  resulting average is measurable and bounded.  Its nonnegative iterated
  integral is zero, so the inner indicator vanishes almost everywhere.
  This is precisely the asserted support property after resampling
  coordinate $i$. -/)
  (title := /-- Coordinate resampling remains in product support almost surely -/)
  (latexEnv := "lemma")]
lemma spectral_pullback_resampling_support {d : ℕ}
    (ρ : Fin d → ProbabilityMeasure ℝ) (i : Fin d) :
    let ν := ProbabilityMeasure.pi ρ
    ∀ᵐ x ∂(ν : Measure (feature_vector d)),
      x ∈ (ν : Measure (feature_vector d)).support ∧
        ∀ᵐ y ∂(ν : Measure (feature_vector d)),
          mix_features (Finset.univ.erase i) x y ∈
            (ν : Measure (feature_vector d)).support := by
  let ν := ProbabilityMeasure.pi ρ
  let s := (ν : Measure (feature_vector d)).support
  let bad : feature_vector d → ℝ := sᶜ.indicator fun _ => 1
  have hs : MeasurableSet s := Measure.isClosed_support.measurableSet
  have hbadm : Measurable bad := measurable_const.indicator hs.compl
  have hbadb : ∀ x, |bad x| ≤ 1 := by
    intro x
    by_cases hx : x ∈ sᶜ <;> simp [bad, hx]
  have hbad_nonneg : ∀ x, 0 ≤ bad x := by
    intro x
    by_cases hx : x ∈ sᶜ <;> simp [bad, hx]
  have hbad_int : Integrable bad (ν : Measure (feature_vector d)) :=
    Integrable.of_bound hbadm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hbadb x)
  have hbad_zero : (∫ x, bad x ∂(ν : Measure (feature_vector d))) = 0 := by
    rw [show bad = sᶜ.indicator (fun _ => 1) from rfl,
      integral_indicator hs.compl]
    simp [s, Measure.measure_compl_support]
  have havg_zero : (∫ x,
      interventional_value ν bad (Finset.univ.erase i) x
      ∂(ν : Measure (feature_vector d))) = 0 := by
    rw [spectral_pullback_interventional_integral ρ bad
      (Finset.univ.erase i) 1 (by norm_num) hbadm hbadb]
    exact hbad_zero
  have havgm : Measurable (fun x =>
      interventional_value ν bad (Finset.univ.erase i) x) :=
    (spectral_pullback_interventional_measurable_bounded ν bad
      (Finset.univ.erase i) 1 (by norm_num) hbadm hbadb).1
  have havg_nonneg : ∀ x,
      0 ≤ interventional_value ν bad (Finset.univ.erase i) x := by
    intro x
    unfold interventional_value
    exact integral_nonneg fun y => hbad_nonneg _
  have havg_int : Integrable (fun x =>
      interventional_value ν bad (Finset.univ.erase i) x)
      (ν : Measure (feature_vector d)) := by
    apply Integrable.of_bound havgm.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (havg_nonneg x)]
      exact le_trans (le_abs_self _)
        ((spectral_pullback_interventional_measurable_bounded ν bad
          (Finset.univ.erase i) 1 (by norm_num) hbadm hbadb).2 x)
  have havg_ae : (fun x =>
      interventional_value ν bad (Finset.univ.erase i) x) =ᵐ[
        (ν : Measure (feature_vector d))] 0 :=
    (integral_eq_zero_iff_of_nonneg havg_nonneg havg_int).1 havg_zero
  have hx_support : ∀ᵐ x ∂(ν : Measure (feature_vector d)), x ∈ s := by
    simpa [s] using (ν : Measure (feature_vector d)).support_mem_ae
  filter_upwards [hx_support, havg_ae] with x hxs hxavg
  refine ⟨hxs, ?_⟩
  have hinner_int : Integrable (fun y =>
      bad (mix_features (Finset.univ.erase i) x y))
      (ν : Measure (feature_vector d)) := by
    apply Integrable.of_bound (hbadm.comp (by
        apply measurable_pi_lambda
        intro j
        unfold mix_features
        split
        · exact measurable_const
        · exact measurable_pi_apply j)).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hbadb
        (mix_features (Finset.univ.erase i) x y)
  have hinner_zero : (∫ y,
      bad (mix_features (Finset.univ.erase i) x y)
      ∂(ν : Measure (feature_vector d))) = 0 := by
    simpa [interventional_value] using hxavg
  have hinner_ae := (integral_eq_zero_iff_of_nonneg
    (fun y => hbad_nonneg _) hinner_int).1 hinner_zero
  filter_upwards [hinner_ae] with y hy
  change mix_features (Finset.univ.erase i) x y ∈
    (ν : Measure (feature_vector d)).support
  simpa [bad, s] using hy

@[blueprint "lem:spectral-pullback-centered-orthogonal"
  (statement := /-- Let $\nu$ be a finite product of probability measures.
  Suppose that bounded measurable functions $u$ and $k$ satisfy
  $v_{[d]\setminus\{i\}}(\nu,u,\cdot)=0$ and that $k$ is determined by
  every coordinate except $i$ on $\operatorname{supp}(\nu)$.  Then
  \[
    \int u(x)k(x)\,d\nu(x)=0.
  \] -/)
  (proof := /-- Apply
  \cref{lem:spectral-pullback-interventional-integral} to the product
  $uk$.  By \cref{lem:spectral-pullback-resampling-support}, almost every
  resampled point and the original point lie in the support; determination
  of $k$ therefore lets it be pulled out of the inner integral.  The
  remaining inner integral is zero by the centering hypothesis. -/)
  (title := /-- Centered functions are orthogonal to feature-invariant functions -/)
  (latexEnv := "lemma")]
lemma spectral_pullback_centered_orthogonal {d : ℕ}
    (ρ : Fin d → ProbabilityMeasure ℝ) (u k : feature_vector d → ℝ)
    (i : Fin d) (Cu Ck : ℝ) (hCu : 0 ≤ Cu) (hCk : 0 ≤ Ck)
    (hu : Measurable u) (hk : Measurable k)
    (hub : ∀ x, |u x| ≤ Cu) (hkb : ∀ x, |k x| ≤ Ck)
    (hcenter : ∀ x, interventional_value (ProbabilityMeasure.pi ρ) u
      (Finset.univ.erase i) x = 0)
    (hdet : is_determined_except_on (ProbabilityMeasure.pi ρ) i k) :
    (∫ x, u x * k x
      ∂(ProbabilityMeasure.pi ρ : Measure (feature_vector d))) = 0 := by
  let ν := ProbabilityMeasure.pi ρ
  have hw_m : Measurable (fun x => u x * k x) := hu.mul hk
  have hw_b : ∀ x, |u x * k x| ≤ Cu * Ck := by
    intro x
    rw [abs_mul]
    exact mul_le_mul (hub x) (hkb x) (abs_nonneg _) hCu
  rw [← spectral_pullback_interventional_integral ρ
    (fun x => u x * k x) (Finset.univ.erase i) (Cu * Ck)
    (mul_nonneg hCu hCk) hw_m hw_b]
  apply integral_eq_zero_of_ae
  filter_upwards [spectral_pullback_resampling_support ρ i] with x hxs
  unfold interventional_value
  have hki : ∀ᵐ y ∂(ν : Measure (feature_vector d)),
      k (mix_features (Finset.univ.erase i) x y) = k x := by
    filter_upwards [hxs.2] with y hys
    apply hdet.2 (mix_features (Finset.univ.erase i) x y) hys x hxs.1
    intro j hji
    simp [mix_features, hji]
  calc
    (∫ y, u (mix_features (Finset.univ.erase i) x y) *
        k (mix_features (Finset.univ.erase i) x y)
        ∂(ν : Measure (feature_vector d))) =
        ∫ y, u (mix_features (Finset.univ.erase i) x y) * k x
          ∂(ν : Measure (feature_vector d)) :=
      integral_congr_ae (hki.mono fun y hy => by
        change u (mix_features (Finset.univ.erase i) x y) *
          k (mix_features (Finset.univ.erase i) x y) =
          u (mix_features (Finset.univ.erase i) x y) * k x
        rw [hy])
    _ = (∫ y, u (mix_features (Finset.univ.erase i) x y)
          ∂(ν : Measure (feature_vector d))) * k x := by
            rw [integral_mul_const]
    _ = 0 := by
      change interventional_value (ProbabilityMeasure.pi ρ) u
        (Finset.univ.erase i) x * k x = 0
      rw [hcenter]
      simp

@[blueprint "lem:spectral-pullback-centered-orthogonal-general"
  (statement := /-- The conclusion of
  \cref{lem:spectral-pullback-centered-orthogonal} remains valid for an
  arbitrary measurable support-determined function $k$, without a boundedness
  assumption. -/)
  (proof := /-- If $uk$ is not integrable, its Bochner integral is zero by
  definition.  Otherwise truncate $k$ to $[-n,n]$.  Every truncation remains
  measurable and support-determined, so
  \cref{lem:spectral-pullback-centered-orthogonal} gives zero integral.
  The products with the truncations converge pointwise to $uk$ and are
  dominated by $|uk|$; dominated convergence therefore passes the zero
  identity to the limit. -/)
  (title := /-- Orthogonality to arbitrary support-determined functions -/)
  (latexEnv := "lemma")]
lemma spectral_pullback_centered_orthogonal_general {d : ℕ}
    (ρ : Fin d → ProbabilityMeasure ℝ) (u k : feature_vector d → ℝ)
    (i : Fin d) (Cu : ℝ) (hCu : 0 ≤ Cu) (hu : Measurable u)
    (hub : ∀ x, |u x| ≤ Cu)
    (hcenter : ∀ x, interventional_value (ProbabilityMeasure.pi ρ) u
      (Finset.univ.erase i) x = 0)
    (hdet : is_determined_except_on (ProbabilityMeasure.pi ρ) i k) :
    (∫ x, u x * k x
      ∂(ProbabilityMeasure.pi ρ : Measure (feature_vector d))) = 0 := by
  let ν := ProbabilityMeasure.pi ρ
  by_cases hInt : Integrable (fun x => u x * k x)
      (ν : Measure (feature_vector d))
  · let kt : ℕ → feature_vector d → ℝ := fun n x =>
      max (-(n : ℝ)) (min (n : ℝ) (k x))
    have hktm (n : ℕ) : Measurable (kt n) := by
      dsimp [kt]
      exact measurable_const.max (measurable_const.min hdet.1)
    have hktb (n : ℕ) (x : feature_vector d) : |kt n x| ≤ (n : ℝ) := by
      dsimp [kt]
      rw [abs_le]
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      constructor
      · exact le_max_left _ _
      · exact max_le (by linarith)
          (min_le_left _ _)
    have hktdet (n : ℕ) :
        is_determined_except_on (ProbabilityMeasure.pi ρ) i (kt n) := by
      constructor
      · exact hktm n
      · intro x hx y hy hxy
        dsimp [kt]
        rw [hdet.2 x hx y hy hxy]
    have hzero (n : ℕ) : (∫ x, u x * kt n x
        ∂(ν : Measure (feature_vector d))) = 0 :=
      spectral_pullback_centered_orthogonal ρ u (kt n) i Cu n
        hCu (Nat.cast_nonneg n) hu (hktm n) hub (hktb n) hcenter (hktdet n)
    have hdom : Integrable (fun x => |u x * k x|)
        (ν : Measure (feature_vector d)) := hInt.norm
    have hle (n : ℕ) : ∀ᵐ x ∂(ν : Measure (feature_vector d)),
        ‖u x * kt n x‖ ≤ |u x * k x| := by
      exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        dsimp [kt]
        rw [abs_le]
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        constructor
        · exact le_trans (le_min
            (by linarith [abs_nonneg (k x)])
            (neg_abs_le (k x)))
            (le_max_right _ _)
        · exact max_le
            (by linarith [abs_nonneg (k x)])
            (le_trans (min_le_right (n : ℝ) (k x)) (le_abs_self (k x)))
    have hlim : ∀ᵐ x ∂(ν : Measure (feature_vector d)),
        Filter.Tendsto (fun n => u x * kt n x) Filter.atTop
          (nhds (u x * k x)) := by
      exact Filter.Eventually.of_forall fun x => by
        obtain ⟨N, hN⟩ := exists_nat_gt |k x|
        have hev : (fun n => u x * kt n x) =ᶠ[Filter.atTop]
            fun _ => u x * k x := by
          filter_upwards [Filter.eventually_ge_atTop N] with n hn
          have hk_upper : k x ≤ (n : ℝ) :=
            le_trans (le_abs_self _)
              (le_trans (le_of_lt hN) (Nat.cast_le.2 hn))
          have hk_lower : -(n : ℝ) ≤ k x := by
            have hnabs : (n : ℝ) ≥ |k x| :=
              le_trans (le_of_lt hN) (Nat.cast_le.2 hn)
            nlinarith [neg_abs_le (k x)]
          simp [kt, min_eq_right hk_upper, max_eq_right hk_lower]
        exact hev.tendsto
    have ht := tendsto_integral_of_dominated_convergence
      (fun x => |u x * k x|)
      (fun n => (hu.mul (hktm n)).aestronglyMeasurable) hdom hle hlim
    have ht0 : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop
        (nhds (∫ x, u x * k x ∂(ν : Measure (feature_vector d)))) := by
      simpa [hzero] using ht
    exact tendsto_nhds_unique ht0 tendsto_const_nhds
  · exact integral_undef hInt

@[blueprint "lem:spectral-pullback-positive-operator-bounded"
  (statement := /-- Let $\nu$ be a finite product of probability measures.
  The positive SHAP operator sends every bounded measurable real-valued
  function to a bounded measurable real-valued function. -/)
  (proof := /-- Each interventional summand is measurable and has the same
  bound as the input by
  \cref{lem:spectral-pullback-interventional-measurable-bounded}.  The
  finite weighted sum in \cref{def:positive-shap-operator} is therefore
  measurable and is bounded by the corresponding finite sum of the
  absolute values of its coefficients. -/)
  (title := /-- Boundedness of the positive SHAP operator -/)
  (latexEnv := "lemma")]
lemma spectral_pullback_positive_operator_bounded {d : ℕ}
    (ρ : Fin d → ProbabilityMeasure ℝ) (q : feature_vector d → ℝ)
    (i : Fin d) (C : ℝ) (hC : 0 ≤ C) (hq : Measurable q)
    (hqb : ∀ x, |q x| ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧
      Measurable (fun x => positive_shap_operator
        (ProbabilityMeasure.pi ρ) q i x) ∧
      ∀ x, |positive_shap_operator (ProbabilityMeasure.pi ρ) q i x| ≤ D := by
  let ν := ProbabilityMeasure.pi ρ
  let U := Finset.univ.erase i
  let D : ℝ := |(d : ℝ)⁻¹| *
    ∑ S ∈ U.powerset, |(Nat.choose (d - 1) S.card : ℝ)⁻¹| * C
  refine ⟨D, mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun S hS =>
    mul_nonneg (abs_nonneg _) hC), ?_, ?_⟩
  · unfold positive_shap_operator
    apply measurable_const.mul
    apply Finset.measurable_fun_sum
    intro S hS
    apply measurable_const.mul
    exact (spectral_pullback_interventional_measurable_bounded
      ν q (insert i S) C hC hq hqb).1
  · intro x
    unfold positive_shap_operator
    calc
      |(d : ℝ)⁻¹ * ∑ S ∈ U.powerset,
          (Nat.choose (d - 1) S.card : ℝ)⁻¹ *
            interventional_value ν q (insert i S) x| =
          |(d : ℝ)⁻¹| * |∑ S ∈ U.powerset,
            (Nat.choose (d - 1) S.card : ℝ)⁻¹ *
              interventional_value ν q (insert i S) x| := abs_mul _ _
      _ ≤ |(d : ℝ)⁻¹| * ∑ S ∈ U.powerset,
          |(Nat.choose (d - 1) S.card : ℝ)⁻¹ *
            interventional_value ν q (insert i S) x| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
      _ ≤ |(d : ℝ)⁻¹| * ∑ S ∈ U.powerset,
          |(Nat.choose (d - 1) S.card : ℝ)⁻¹| * C := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Finset.sum_le_sum
        intro S hS
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact (spectral_pullback_interventional_measurable_bounded
          ν q (insert i S) C hC hq hqb).2 x
      _ = D := rfl

@[blueprint "lem:spectral-pullback-positive-operator-sub"
  (statement := /-- On bounded measurable real-valued functions, the positive
  SHAP operator is additive under subtraction:
  $A_i(f-g)=A_if-A_ig$. -/)
  (proof := /-- For each interventional term, the two mixed functions are
  integrable because they are bounded and measurable.  Linearity of the
  integral gives the subtraction identity term by term in
  \cref{def:positive-shap-operator}; distributivity over the finite Shapley
  sum completes the proof. -/)
  (title := /-- Linearity of the positive operator under subtraction -/)
  (latexEnv := "lemma")]
lemma spectral_pullback_positive_operator_sub {d : ℕ}
    (ν : ProbabilityMeasure (feature_vector d)) (f g : feature_vector d → ℝ)
    (i : Fin d) (Cf Cg : ℝ) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ x, |f x| ≤ Cf) (hgb : ∀ x, |g x| ≤ Cg) :
    ∀ x, positive_shap_operator ν (fun z => f z - g z) i x =
      positive_shap_operator ν f i x - positive_shap_operator ν g i x := by
  have hint (q : feature_vector d → ℝ) (C : ℝ) (hq : Measurable q)
      (hqb : ∀ x, |q x| ≤ C) (S : Finset (Fin d)) (x : feature_vector d) :
      Integrable (fun y => q (mix_features S x y))
        (ν : Measure (feature_vector d)) := by
    apply Integrable.of_bound (by
      apply Measurable.aestronglyMeasurable
      apply hq.comp
      apply measurable_pi_lambda
      intro j
      unfold mix_features
      split
      · exact measurable_const
      · exact measurable_pi_apply j) C
    exact Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hqb (mix_features S x y)
  intro x
  unfold positive_shap_operator
  rw [← mul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  rw [← mul_sub]
  congr 1
  unfold interventional_value
  rw [integral_sub (hint f Cf hf hfb _ x) (hint g Cg hg hgb _ x)]

@[blueprint "lem:spectral-pullback-bound"
  (statement := /-- Let $\mu$ be a probability measure on $\mathbb{R}^{d}$, let
  $f:\mathbb{R}^{d}\to[0,1]$ be measurable, let $i\in\operatorname{Fin}(d)$, and let
  $\epsilon\in\mathbb{R}$.  Suppose that a measurable function $h$, determined on
  $\operatorname{supp}(\mu^*)$ by all features except $i$, satisfies
  \[
    \int\bigl((A_i f)(x)-h(x)\bigr)^2\,d\mu^*(x)\leq\epsilon.
  \]
  Then there exists a measurable function $g$, determined on
  $\operatorname{supp}(\mu^*)$ by all features except $i$, such that
  \[
    \int(f(x)-g(x))^2\,d\mu^*(x)\leq d^2\epsilon.
  \] -/)
  (proof := /-- Write the extended distribution from
  \cref{def:extended-distribution} as the product measure $\nu$.  Using
  \cref{def:interventional-value}, let $g$ be the interventional average of $f$
  over every coordinate except $i$, and put $u=f-g$.
  By \cref{lem:spectral-pullback-full-average-determined}, $g$ is measurable and
  determined off $i$ in the sense of \cref{def:is-determined-except-on}; moreover,
  \cref{lem:spectral-pullback-interventional-measurable-bounded} gives
  $|g|\leq 1$, while \cref{lem:spectral-pullback-full-average-global} gives that
  the complementary interventional average of $u$ vanishes.

  The measurability and boundedness conclusion of
  \cref{lem:spectral-pullback-positive-operator-bounded}, applied to $f$ and
  $g$, controls both positive SHAP images.  By
  \cref{lem:spectral-pullback-positive-operator-preserves-invariance}, $A_i g$
  is determined off $i$.  Thus $k=A_i g-h$ is also determined off $i$, and
  \cref{lem:spectral-pullback-centered-orthogonal-general} yields
  $\int uk\,d\nu=0$.  Linearity from
  \cref{lem:spectral-pullback-positive-operator-sub} gives
  $A_i u=A_i f-A_i g$, so, for $r=A_i f-h$, one has $r=A_i u+k$.

  Suppose first that $r^2$ is integrable.  The preceding bounds make all
  products below integrable, and the orthogonality identity gives
  $\int uA_i u\,d\nu=\int ur\,d\nu$.  The coercive estimate
  \cref{lem:spectral-pullback-positive-operator-coercive} therefore implies
  \[
    \int u^2\,d\nu\leq d\int ur\,d\nu.
  \]
  Integrating the pointwise inequality
  $2d\,ur\leq u^2+d^2r^2$ and combining the two estimates gives
  $\int u^2\,d\nu\leq d^2\int r^2\,d\nu\leq d^2\epsilon$.

  If $r^2$ is not integrable, the Bochner integral convention makes its
  integral zero, so the assumed error estimate implies $\epsilon\geq0$.
  Boundedness makes $(A_i f-f)^2$ integrable.  If $(f-h)^2$ were also
  integrable, the pointwise inequality
  $r^2\leq2(A_i f-f)^2+2(f-h)^2$ would make $r^2$ integrable, a contradiction.
  Hence the integral of $(f-h)^2$ is zero under the same convention, and
  choosing $g=h$ proves the result in this remaining case. -/)
  (title := /-- Spectral pullback from the operator image -/)
  (latexEnv := "lemma")]
lemma spectral_pullback_bound {d : ℕ}
    (μ : ProbabilityMeasure (feature_vector d)) (f h : feature_vector d → ℝ)
    (i : Fin d) (ε : ℝ) (hf : Measurable f)
    (hf_range : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hh : is_determined_except_on (extended_distribution μ) i h)
    (herror : (∫ x, (positive_shap_operator (extended_distribution μ) f i x - h x) ^ 2
      ∂(extended_distribution μ : Measure (feature_vector d))) ≤ ε) :
    ∃ g : feature_vector d → ℝ,
      is_determined_except_on (extended_distribution μ) i g ∧
      (∫ x, (f x - g x) ^ 2
        ∂(extended_distribution μ : Measure (feature_vector d))) ≤ (d : ℝ) ^ 2 * ε := by
  let ρ : Fin d → ProbabilityMeasure ℝ :=
    fun j => μ.map (measurable_pi_apply j).aemeasurable
  have hext : extended_distribution μ = ProbabilityMeasure.pi ρ := rfl
  rw [hext] at hh herror ⊢
  let ν := ProbabilityMeasure.pi ρ
  let g : feature_vector d → ℝ :=
    fun x => interventional_value ν f (Finset.univ.erase i) x
  let u : feature_vector d → ℝ := fun x => f x - g x
  have hf_bound : ∀ x, |f x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (hf_range x).1]
    exact (hf_range x).2
  have hgdet : is_determined_except_on ν i g :=
    spectral_pullback_full_average_determined ν f i hf hf_range
  have hgglobal := spectral_pullback_full_average_global ν f i hf hf_range
  have hg_bound : ∀ x, |g x| ≤ 1 :=
    (spectral_pullback_interventional_measurable_bounded ν f
      (Finset.univ.erase i) 1 (by norm_num) hf hf_bound).2
  have hu : Measurable u := hf.sub hgdet.1
  have hu_bound : ∀ x, |u x| ≤ 2 := fun x => by
    dsimp [u]
    calc
      |f x - g x| ≤ |f x| + |g x| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (hf_bound x) (hg_bound x)
      _ = 2 := by norm_num
  have hcenter : ∀ x, interventional_value ν u
      (Finset.univ.erase i) x = 0 := by
    simpa [ν, g, u] using hgglobal.2
  obtain ⟨Dg, hDg, hAgm, hAgb⟩ :=
    spectral_pullback_positive_operator_bounded ρ g i 1 (by norm_num)
      hgdet.1 hg_bound
  obtain ⟨Df, hDf, hAfm, hAfb⟩ :=
    spectral_pullback_positive_operator_bounded ρ f i 1 (by norm_num)
      hf hf_bound
  have hAgdet : is_determined_except_on ν i
      (fun x => positive_shap_operator ν g i x) := by
    apply spectral_pullback_positive_operator_preserves_invariance
      ρ g i 1 (by norm_num) hgdet.1 hg_bound
    exact hgglobal.1
  let k : feature_vector d → ℝ :=
    fun x => positive_shap_operator ν g i x - h x
  have hkdet : is_determined_except_on ν i k := by
    constructor
    · exact hAgm.sub hh.1
    · intro x hx y hy hxy
      dsimp [k]
      have ha := hAgdet.2 x hx y hy hxy
      have hb := hh.2 x hx y hy hxy
      change positive_shap_operator ν g i x = positive_shap_operator ν g i y at ha
      rw [ha, hb]
  have huk_zero : (∫ x, u x * k x
      ∂(ν : Measure (feature_vector d))) = 0 :=
    spectral_pullback_centered_orthogonal_general ρ u k i 2
      (by norm_num) hu hu_bound hcenter hkdet
  have hlinear : ∀ x, positive_shap_operator ν u i x =
      positive_shap_operator ν f i x - positive_shap_operator ν g i x := by
    simpa [u] using spectral_pullback_positive_operator_sub
      ν f g i 1 1 (by norm_num) (by norm_num) hf hgdet.1 hf_bound hg_bound
  let r : feature_vector d → ℝ :=
    fun x => positive_shap_operator ν f i x - h x
  have hrm : Measurable r := hAfm.sub hh.1
  have hr_eq (x : feature_vector d) :
      r x = positive_shap_operator ν u i x + k x := by
    dsimp [r, k]
    rw [hlinear]
    ring
  have hdpos : (0 : ℝ) < d := by
    exact_mod_cast Nat.zero_lt_of_lt i.isLt
  by_cases hr2 : Integrable (fun x => r x ^ 2)
      (ν : Measure (feature_vector d))
  · have hr : Integrable r (ν : Measure (feature_vector d)) := by
      apply Integrable.mono
        (hr2.add (integrable_const (1 : ℝ)))
        hrm.aestronglyMeasurable
      exact Filter.Eventually.of_forall fun x => by
        change |r x| ≤ |r x ^ 2 + 1|
        have hsq : 0 ≤ r x ^ 2 + 1 := by
          nlinarith [sq_nonneg (r x)]
        rw [abs_of_nonneg hsq]
        nlinarith [sq_nonneg (|r x| - (1 / 2 : ℝ)), sq_abs (r x)]
    have hAum : Measurable (fun x => positive_shap_operator ν u i x) := by
      rw [show (fun x => positive_shap_operator ν u i x) =
        fun x => positive_shap_operator ν f i x -
          positive_shap_operator ν g i x by
            funext x
            exact hlinear x]
      exact hAfm.sub hAgm
    have hAu_bound : ∀ x,
        |positive_shap_operator ν u i x| ≤ Df + Dg := fun x => by
      rw [hlinear]
      exact le_trans (abs_sub _ _)
        (add_le_add (hAfb x) (hAgb x))
    have huAu : Integrable (fun x =>
        u x * positive_shap_operator ν u i x)
        (ν : Measure (feature_vector d)) := by
      apply Integrable.of_bound (hu.mul hAum).aestronglyMeasurable
        (2 * (Df + Dg))
      exact Filter.Eventually.of_forall fun x => by
        change |u x * positive_shap_operator ν u i x| ≤ 2 * (Df + Dg)
        rw [abs_mul]
        exact mul_le_mul (hu_bound x) (hAu_bound x) (abs_nonneg _) (by norm_num)
    have hur : Integrable (fun x => u x * r x)
        (ν : Measure (feature_vector d)) := by
      apply Integrable.mono (hr.const_mul 2) (hu.mul hrm).aestronglyMeasurable
      exact Filter.Eventually.of_forall fun x => by
        change |u x * r x| ≤ ‖(2 : ℝ) * r x‖
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        norm_num
        exact mul_le_mul_of_nonneg_right (hu_bound x) (abs_nonneg _)
    have huk_int : Integrable (fun x => u x * k x)
        (ν : Measure (feature_vector d)) := by
      apply Integrable.congr (hur.sub huAu)
      exact Filter.Eventually.of_forall fun x => by
        change u x * r x - u x * positive_shap_operator ν u i x = u x * k x
        rw [hr_eq]
        ring
    have hinner : (∫ x,
        u x * positive_shap_operator ν u i x
        ∂(ν : Measure (feature_vector d))) =
        ∫ x, u x * r x ∂(ν : Measure (feature_vector d)) := by
      have hadd := integral_add huAu huk_int
      rw [huk_zero, add_zero] at hadd
      rw [← hadd]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change u x * positive_shap_operator ν u i x + u x * k x = u x * r x
        rw [hr_eq]
        ring
    have hcoercive := spectral_pullback_positive_operator_coercive
      ρ u i 2 (by norm_num) hu hu_bound
    rw [hinner] at hcoercive
    let U2 := ∫ x, u x ^ 2 ∂(ν : Measure (feature_vector d))
    let R2 := ∫ x, r x ^ 2 ∂(ν : Measure (feature_vector d))
    have hU2_nonneg : 0 ≤ U2 := integral_nonneg fun x => sq_nonneg (u x)
    have hR2_nonneg : 0 ≤ R2 := integral_nonneg fun x => sq_nonneg (r x)
    have hUI : U2 ≤ (d : ℝ) *
        (∫ x, u x * r x ∂(ν : Measure (feature_vector d))) := by
      dsimp [U2] at *
      have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
      calc
        (∫ x, u x ^ 2 ∂(ν : Measure (feature_vector d))) =
            (d : ℝ) * ((d : ℝ)⁻¹ *
              ∫ x, u x ^ 2 ∂(ν : Measure (feature_vector d))) := by
                field_simp
        _ ≤ (d : ℝ) * (∫ x, u x * r x
              ∂(ν : Measure (feature_vector d))) :=
          mul_le_mul_of_nonneg_left hcoercive (le_of_lt hdpos)
    have hyoung_point : ∀ x,
        2 * (d : ℝ) * (u x * r x) ≤ u x ^ 2 + (d : ℝ) ^ 2 * r x ^ 2 :=
      fun x => by nlinarith [sq_nonneg (u x - (d : ℝ) * r x)]
    have hyoung : 2 * (d : ℝ) *
        (∫ x, u x * r x ∂(ν : Measure (feature_vector d))) ≤
        U2 + (d : ℝ) ^ 2 * R2 := by
      have hu2 : Integrable (fun x => u x ^ 2)
          (ν : Measure (feature_vector d)) := by
        apply Integrable.of_bound (hu.pow_const 2).aestronglyMeasurable 4
        exact Filter.Eventually.of_forall fun x => by
          change |u x ^ 2| ≤ 4
          rw [abs_of_nonneg (sq_nonneg _)]
          have hm := mul_self_le_mul_self (abs_nonneg (u x)) (hu_bound x)
          nlinarith [sq_abs (u x)]
      have hleft : (∫ x, 2 * (d : ℝ) * (u x * r x)
          ∂(ν : Measure (feature_vector d))) =
          2 * (d : ℝ) * (∫ x, u x * r x
            ∂(ν : Measure (feature_vector d))) := by
        rw [integral_const_mul]
      have hright : (∫ x, u x ^ 2 + (d : ℝ) ^ 2 * r x ^ 2
          ∂(ν : Measure (feature_vector d))) =
          U2 + (d : ℝ) ^ 2 * R2 := by
        rw [integral_add hu2 (hr2.const_mul _), integral_const_mul]
      rw [← hleft, ← hright]
      exact integral_mono_ae
        ((hur.const_mul (2 * d)))
        (hu2.add (hr2.const_mul _))
        (Filter.Eventually.of_forall hyoung_point)
    have hmain : U2 ≤ (d : ℝ) ^ 2 * R2 := by
      nlinarith
    refine ⟨g, hgdet, ?_⟩
    change U2 ≤ (d : ℝ) ^ 2 * ε
    exact le_trans hmain (mul_le_mul_of_nonneg_left herror
      (sq_nonneg (d : ℝ)))
  · refine ⟨h, hh, ?_⟩
    have hr_zero : (∫ x, r x ^ 2
        ∂(ν : Measure (feature_vector d))) = 0 := integral_undef hr2
    have heps : 0 ≤ ε := by
      have : (∫ x, r x ^ 2 ∂(ν : Measure (feature_vector d))) ≤ ε := herror
      linarith
    have hAf_sub_f_sq : Integrable (fun x =>
        (positive_shap_operator ν f i x - f x) ^ 2)
        (ν : Measure (feature_vector d)) := by
      apply Integrable.of_bound ((hAfm.sub hf).pow_const 2).aestronglyMeasurable
        ((Df + 1) ^ 2)
      exact Filter.Eventually.of_forall fun x => by
        change |(positive_shap_operator ν f i x - f x) ^ 2| ≤ (Df + 1) ^ 2
        rw [abs_of_nonneg (sq_nonneg _)]
        have hb : |positive_shap_operator ν f i x - f x| ≤ Df + 1 :=
          le_trans (abs_sub _ _) (add_le_add (hAfb x) (hf_bound x))
        have hm := mul_self_le_mul_self (abs_nonneg
          (positive_shap_operator ν f i x - f x)) hb
        nlinarith [sq_abs (positive_shap_operator ν f i x - f x)]
    have hfh_not : ¬ Integrable (fun x => (f x - h x) ^ 2)
        (ν : Measure (feature_vector d)) := by
      intro hfh
      apply hr2
      apply Integrable.mono
        ((hAf_sub_f_sq.const_mul 2).add (hfh.const_mul 2))
        (hrm.pow_const 2).aestronglyMeasurable
      exact Filter.Eventually.of_forall fun x => by
        change |r x ^ 2| ≤ |2 * (positive_shap_operator ν f i x - f x) ^ 2 +
          2 * (f x - h x) ^ 2|
        rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (by positivity)]
        have heq : r x =
            (positive_shap_operator ν f i x - f x) + (f x - h x) := by
          dsimp [r]
          ring
        rw [heq]
        nlinarith [sq_nonneg
          ((positive_shap_operator ν f i x - f x) - (f x - h x))]
    rw [integral_undef hfh_not]
    exact mul_nonneg (sq_nonneg (d : ℝ)) heps

@[blueprint "lem:nonstrict-robust-distribution-bound"
  (statement := /-- Let $\mu$ be a probability measure on $\mathbb{R}^{d}$, let
  $f:\mathbb{R}^{d}\to[0,1]$ be measurable, let $i\in\operatorname{Fin}(d)$, and let
  $\epsilon\in\mathbb{R}$.  If
  $\overline{\phi_i}(\mu^*,f)\leq\epsilon$, then there exists a measurable function $g$,
  determined on $\operatorname{supp}(\mu^*)$ by every feature except $i$, such that
  \[
    \int(f(x)-g(x))^2\,d\mu^*(x)\leq d^2\epsilon.
  \] -/)
  (proof := /-- By \cref{lem:operator-image-near-determined}, choose a determined function
  $h$ whose squared distance from $A_i f$ is at most $\epsilon$.  Apply
  \cref{lem:spectral-pullback-bound} to $f$ and this $h$.  The resulting function $g$ is
  determined off feature $i$ on the extended support and satisfies the stated non-strict
  squared-error estimate. -/)
  (title := /-- Non-strict robust feature-discarding estimate -/)
  (latexEnv := "lemma")]
lemma nonstrict_robust_distribution_bound {d : ℕ}
    (μ : ProbabilityMeasure (feature_vector d)) (f : feature_vector d → ℝ)
    (i : Fin d) (ε : ℝ) (hf : Measurable f)
    (hf_range : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (haggregate : aggregate_shap_value (extended_distribution μ) f i ≤ ε) :
    ∃ g : feature_vector d → ℝ,
      is_determined_except_on (extended_distribution μ) i g ∧
      (∫ x, (f x - g x) ^ 2
        ∂(extended_distribution μ : Measure (feature_vector d))) ≤ (d : ℝ) ^ 2 * ε := by
  obtain ⟨h, hh, herror⟩ :=
    operator_image_near_determined μ f i ε hf hf_range haggregate
  exact spectral_pullback_bound μ f h i ε hf hf_range hh herror

@[blueprint "lem:bounded-extended-shap-value"
  (statement := /-- Let $d\in\mathbb{N}$, let $\mu$ be a probability measure on
  $\mathbb{R}^{d}$, let $f:\mathbb{R}^{d}\to\mathbb{R}$ be measurable and take values
  in $[0,1]$, and let $i\in\operatorname{Fin}(d)$.  Then
  $x\mapsto\phi_i(\mu^*,f,x)$ is measurable and
  $|\phi_i(\mu^*,f,x)|\leq1$ for every $x\in\mathbb{R}^{d}$. -/)
  (proof := /-- By \cref{def:interventional-value}, every interventional value is a
  measurable function with values in $[0,1]$.  The Shapley coefficients in
  \cref{def:shap-value} are nonnegative and have total mass one: grouping subsets by
  cardinality cancels each binomial coefficient, leaving $d$ terms multiplied by
  $d^{-1}$.  Thus the SHAP value is a measurable weighted average of differences of
  two numbers in $[0,1]$, and its absolute value is at most one. -/)
  (title := /-- Measurability and boundedness of the extended SHAP value -/)
  (latexEnv := "lemma")]
lemma bounded_extended_shap_value {d : ℕ}
    (μ : ProbabilityMeasure (feature_vector d)) (f : feature_vector d → ℝ)
    (i : Fin d) (hf : Measurable f)
    (hf_range : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    Measurable (shap_value (extended_distribution μ) f i) ∧
      ∀ x, |shap_value (extended_distribution μ) f i x| ≤ 1 := by
  have hd : 0 < d := Nat.zero_lt_of_lt i.isLt
  have hweights :
      (d : ℝ)⁻¹ * ∑ S ∈ (Finset.univ.erase i).powerset,
        (Nat.choose (d - 1) S.card : ℝ)⁻¹ = 1 := by
    have hgroup := Finset.sum_powerset_apply_card
      (f := fun k => (Nat.choose (d - 1) k : ℝ)⁻¹)
      (x := Finset.univ.erase i)
    rw [hgroup]
    simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin, Nat.sub_add_cancel hd]
    have hsum :
        (∑ m ∈ Finset.range d,
          (d - 1).choose m • (Nat.choose (d - 1) m : ℝ)⁻¹) =
          ∑ m ∈ Finset.range d, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mem_range] at hm
      have hc : Nat.choose (d - 1) m ≠ 0 := Nat.choose_ne_zero (by omega)
      simp [nsmul_eq_mul, hc]
    rw [hsum]
    simp [Nat.ne_of_gt hd]
  have hinterventional (S : Finset (Fin d)) (x : feature_vector d) :
      interventional_value (extended_distribution μ) f S x ∈ Set.Icc (0 : ℝ) 1 := by
    have hmeas : Measurable (fun y => f (mix_features S x y)) := by
      apply hf.comp
      apply measurable_pi_lambda
      intro j
      simp only [mix_features]
      split <;> fun_prop
    have hint : Integrable (fun y => f (mix_features S x y))
        (extended_distribution μ : Measure (feature_vector d)) := by
      apply Integrable.of_bound hmeas.aestronglyMeasurable 1
      filter_upwards [] with y
      rw [Real.norm_eq_abs]
      exact abs_le.2 ⟨by linarith [(hf_range (mix_features S x y)).1],
        (hf_range (mix_features S x y)).2⟩
    unfold interventional_value
    constructor
    · apply integral_nonneg_of_ae
      filter_upwards [] with y
      exact (hf_range (mix_features S x y)).1
    · calc
        (∫ y, f (mix_features S x y)
            ∂(extended_distribution μ : Measure (feature_vector d))) ≤
            ∫ _y, (1 : ℝ)
              ∂(extended_distribution μ : Measure (feature_vector d)) := by
          apply integral_mono_ae hint (integrable_const 1)
          filter_upwards [] with y
          exact (hf_range (mix_features S x y)).2
        _ = 1 := by simp
  have hinterventional_meas (S : Finset (Fin d)) :
      Measurable (interventional_value (extended_distribution μ) f S) := by
    unfold interventional_value
    have hmix : Measurable
        (fun p : feature_vector d × feature_vector d => mix_features S p.1 p.2) := by
      apply measurable_pi_lambda
      intro j
      simp only [mix_features]
      split <;> fun_prop
    have hlin : Measurable
        (fun x => ∫⁻ y, ENNReal.ofReal (f (mix_features S x y))
          ∂(extended_distribution μ : Measure (feature_vector d))) :=
      ((hf.comp hmix).ennreal_ofReal).lintegral_prod_right'
    rw [show (fun x => ∫ y, f (mix_features S x y)
        ∂(extended_distribution μ : Measure (feature_vector d))) =
      (fun x => ENNReal.toReal (∫⁻ y, ENNReal.ofReal (f (mix_features S x y))
        ∂(extended_distribution μ : Measure (feature_vector d)))) by
      funext x
      apply integral_eq_lintegral_of_nonneg_ae
      · exact Filter.Eventually.of_forall (fun y => (hf_range _).1)
      · exact (hf.comp (hmix.comp measurable_prodMk_left)).aestronglyMeasurable]
    exact hlin.ennreal_toReal
  constructor
  · unfold shap_value
    fun_prop
  · intro x
    unfold shap_value
    calc
      |(d : ℝ)⁻¹ * ∑ S ∈ (Finset.univ.erase i).powerset,
          (Nat.choose (d - 1) S.card : ℝ)⁻¹ *
            (interventional_value (extended_distribution μ) f (insert i S) x -
              interventional_value (extended_distribution μ) f S x)| =
          (d : ℝ)⁻¹ * |∑ S ∈ (Finset.univ.erase i).powerset,
            (Nat.choose (d - 1) S.card : ℝ)⁻¹ *
              (interventional_value (extended_distribution μ) f (insert i S) x -
                interventional_value (extended_distribution μ) f S x)| := by
        rw [abs_mul, abs_of_nonneg]
        positivity
      _ ≤ (d : ℝ)⁻¹ * ∑ S ∈ (Finset.univ.erase i).powerset,
          |(Nat.choose (d - 1) S.card : ℝ)⁻¹ *
            (interventional_value (extended_distribution μ) f (insert i S) x -
              interventional_value (extended_distribution μ) f S x)| := by
        apply mul_le_mul_of_nonneg_left
          (Finset.abs_sum_le_sum_abs
            (fun S => (Nat.choose (d - 1) S.card : ℝ)⁻¹ *
              (interventional_value (extended_distribution μ) f (insert i S) x -
                interventional_value (extended_distribution μ) f S x))
            (Finset.univ.erase i).powerset)
        positivity
      _ ≤ (d : ℝ)⁻¹ * ∑ S ∈ (Finset.univ.erase i).powerset,
          (Nat.choose (d - 1) S.card : ℝ)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro S hS
        have hdiff :
            |interventional_value (extended_distribution μ) f (insert i S) x -
              interventional_value (extended_distribution μ) f S x| ≤ 1 := by
          rcases hinterventional (insert i S) x with ⟨hpos_lo, hpos_hi⟩
          rcases hinterventional S x with ⟨hneg_lo, hneg_hi⟩
          rw [abs_le]
          constructor <;> linarith
        rw [abs_mul, abs_of_nonneg]
        · simpa using mul_le_mul_of_nonneg_left hdiff
            (show 0 ≤ (Nat.choose (d - 1) S.card : ℝ)⁻¹ by positivity)
        · positivity
      _ = 1 := hweights

@[blueprint "lem:linear-robust-distribution-bound"
  (statement := /-- Let $d\in\mathbb{N}$, let $\mu$ be a probability measure on
  $\mathbb{R}^{d}$, let $f:\mathbb{R}^{d}\to\mathbb{R}$ be measurable and take values
  in $[0,1]$, let $i\in\operatorname{Fin}(d)$, and let $\epsilon\in\mathbb{R}$. If
  $\overline{\phi_i}(\mu^*,f)\leq\epsilon$, then there exists a measurable function
  $g:\mathbb{R}^{d}\to\mathbb{R}$, determined on
  $\operatorname{supp}(\mu^*)$ by every feature except $i$, such that
  \[
    \int(f(x)-g(x))^2\,d\mu^*(x)\leq d\epsilon.
  \] -/)
  (proof := /-- Write $\mu^*$ as the product measure from
  \cref{def:extended-distribution}, let $g$ be the complementary interventional average
  from \cref{lem:spectral-pullback-full-average-determined}, and put $u=f-g$.
  The range assumption gives $|u|\leq1$, while
  \cref{lem:spectral-pullback-full-average-global} says that the complementary average
  of $u$ vanishes.

  Put $h=B_i f$.  The function $h$ is determined off $i$ by
  \cref{lem:negative-shap-operator-determined}.  The boundedness and invariance results
  \cref{lem:spectral-pullback-positive-operator-bounded,
  lem:spectral-pullback-positive-operator-preserves-invariance} show that
  $k=A_i g-h$ is also determined off $i$.  Hence
  \cref{lem:spectral-pullback-centered-orthogonal-general} gives
  $\int uk\,d\mu^*=0$.  Linearity from
  \cref{lem:spectral-pullback-positive-operator-sub} and the decomposition
  \cref{lem:shap-operator-decomposition} identify
  $r=A_i f-h$ with the SHAP value and yield
  $\int uA_i u\,d\mu^*=\int ur\,d\mu^*$.

  By \cref{lem:spectral-pullback-positive-operator-coercive},
  $\int u^2\,d\mu^*\leq d\int ur\,d\mu^*$.  The estimate $|u|\leq1$ implies
  $ur\leq|r|$ pointwise.  Measurability and integrability follow from
  \cref{lem:bounded-extended-shap-value}.  Integration, the definition
  \cref{def:aggregate-shap-value}, and the assumed aggregate bound therefore give
  $\int u^2\,d\mu^*\leq d\overline{\phi_i}(\mu^*,f)\leq d\epsilon$. -/)
  (title := /-- Linear robust feature-discarding estimate -/)
  (latexEnv := "lemma")]
lemma linear_robust_distribution_bound {d : ℕ}
    (μ : ProbabilityMeasure (feature_vector d)) (f : feature_vector d → ℝ)
    (i : Fin d) (ε : ℝ) (hf : Measurable f)
    (hf_range : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (haggregate : aggregate_shap_value (extended_distribution μ) f i ≤ ε) :
    ∃ g : feature_vector d → ℝ,
      is_determined_except_on (extended_distribution μ) i g ∧
      (∫ x, (f x - g x) ^ 2
        ∂(extended_distribution μ : Measure (feature_vector d))) ≤ (d : ℝ) * ε := by
  let ρ : Fin d → ProbabilityMeasure ℝ :=
    fun j => μ.map (measurable_pi_apply j).aemeasurable
  have hext : extended_distribution μ = ProbabilityMeasure.pi ρ := rfl
  have hshap :=
    bounded_extended_shap_value μ f i hf hf_range
  have hh :=
    negative_shap_operator_determined μ f i hf hf_range
  rw [hext] at haggregate hshap hh ⊢
  let ν := ProbabilityMeasure.pi ρ
  change aggregate_shap_value ν f i ≤ ε at haggregate
  change Measurable (shap_value ν f i) ∧
    (∀ x, |shap_value ν f i x| ≤ 1) at hshap
  change is_determined_except_on ν i
    (negative_shap_operator ν f i) at hh
  let g : feature_vector d → ℝ :=
    fun x => interventional_value ν f (Finset.univ.erase i) x
  let u : feature_vector d → ℝ := fun x => f x - g x
  have hf_bound : ∀ x, |f x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (hf_range x).1]
    exact (hf_range x).2
  have hgdet : is_determined_except_on ν i g :=
    spectral_pullback_full_average_determined ν f i hf hf_range
  have hgglobal := spectral_pullback_full_average_global ν f i hf hf_range
  have hg_range (x : feature_vector d) : g x ∈ Set.Icc (0 : ℝ) 1 := by
    have hmeas : Measurable (fun y =>
        f (mix_features (Finset.univ.erase i) x y)) := by
      apply hf.comp
      apply measurable_pi_lambda
      intro j
      simp only [mix_features]
      split <;> fun_prop
    have hint : Integrable (fun y =>
        f (mix_features (Finset.univ.erase i) x y))
        (ν : Measure (feature_vector d)) := by
      apply Integrable.of_bound hmeas.aestronglyMeasurable 1
      filter_upwards [] with y
      rw [Real.norm_eq_abs]
      exact abs_le.2 ⟨by
        linarith [(hf_range (mix_features (Finset.univ.erase i) x y)).1], by
        exact (hf_range (mix_features (Finset.univ.erase i) x y)).2⟩
    dsimp [g]
    unfold interventional_value
    constructor
    · apply integral_nonneg_of_ae
      filter_upwards [] with y
      exact (hf_range _).1
    · calc
        (∫ y, f (mix_features (Finset.univ.erase i) x y)
            ∂(ν : Measure (feature_vector d))) ≤
            ∫ _y, (1 : ℝ) ∂(ν : Measure (feature_vector d)) := by
          apply integral_mono_ae hint (integrable_const 1)
          filter_upwards [] with y
          exact (hf_range _).2
        _ = 1 := by simp
  have hg_bound : ∀ x, |g x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (hg_range x).1]
    exact (hg_range x).2
  have hu : Measurable u := hf.sub hgdet.1
  have hu_bound : ∀ x, |u x| ≤ 1 := fun x => by
    rw [abs_le]
    dsimp [u]
    constructor <;> linarith [(hf_range x).1, (hf_range x).2,
      (hg_range x).1, (hg_range x).2]
  have hcenter : ∀ x, interventional_value ν u
      (Finset.univ.erase i) x = 0 := by
    simpa [g, u] using hgglobal.2
  obtain ⟨Dg, hDg, hAgm, hAgb⟩ :=
    spectral_pullback_positive_operator_bounded ρ g i 1 (by norm_num)
      hgdet.1 hg_bound
  obtain ⟨Df, hDf, hAfm, hAfb⟩ :=
    spectral_pullback_positive_operator_bounded ρ f i 1 (by norm_num)
      hf hf_bound
  have hAgdet : is_determined_except_on ν i
      (fun x => positive_shap_operator ν g i x) := by
    apply spectral_pullback_positive_operator_preserves_invariance
      ρ g i 1 (by norm_num) hgdet.1 hg_bound
    exact hgglobal.1
  let k : feature_vector d → ℝ :=
    fun x => positive_shap_operator ν g i x -
      negative_shap_operator ν f i x
  have hkdet : is_determined_except_on ν i k := by
    constructor
    · exact hAgm.sub hh.1
    · intro x hx y hy hxy
      dsimp [k]
      have ha := hAgdet.2 x hx y hy hxy
      have hb := hh.2 x hx y hy hxy
      change positive_shap_operator ν g i x =
        positive_shap_operator ν g i y at ha
      rw [ha, hb]
  have huk_zero : (∫ x, u x * k x
      ∂(ν : Measure (feature_vector d))) = 0 :=
    spectral_pullback_centered_orthogonal_general ρ u k i 1
      (by norm_num) hu hu_bound hcenter hkdet
  have hlinear : ∀ x, positive_shap_operator ν u i x =
      positive_shap_operator ν f i x - positive_shap_operator ν g i x := by
    simpa [u] using spectral_pullback_positive_operator_sub
      ν f g i 1 1 (by norm_num) (by norm_num) hf hgdet.1 hf_bound hg_bound
  let r : feature_vector d → ℝ :=
    fun x => positive_shap_operator ν f i x -
      negative_shap_operator ν f i x
  have hrm : Measurable r := hAfm.sub hh.1
  have hr_shap (x : feature_vector d) :
      r x = shap_value ν f i x := by
    dsimp [r]
    rw [shap_operator_decomposition]
  have hr_bound : ∀ x, |r x| ≤ 1 := fun x => by
    rw [hr_shap]
    exact hshap.2 x
  have hr : Integrable r (ν : Measure (feature_vector d)) := by
    apply Integrable.of_bound hrm.aestronglyMeasurable 1
    filter_upwards [] with x
    simpa [Real.norm_eq_abs] using hr_bound x
  have hAum : Measurable (fun x => positive_shap_operator ν u i x) := by
    rw [show (fun x => positive_shap_operator ν u i x) =
      fun x => positive_shap_operator ν f i x -
        positive_shap_operator ν g i x by
          funext x
          exact hlinear x]
    exact hAfm.sub hAgm
  have hAu_bound : ∀ x,
      |positive_shap_operator ν u i x| ≤ Df + Dg := fun x => by
    rw [hlinear]
    exact le_trans (abs_sub _ _) (add_le_add (hAfb x) (hAgb x))
  have huAu : Integrable (fun x =>
      u x * positive_shap_operator ν u i x)
      (ν : Measure (feature_vector d)) := by
    apply Integrable.of_bound (hu.mul hAum).aestronglyMeasurable (Df + Dg)
    filter_upwards [] with x
    change |u x * positive_shap_operator ν u i x| ≤ Df + Dg
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (hu_bound x) (hAu_bound x)
      (abs_nonneg (positive_shap_operator ν u i x)) (by linarith)
  have hur : Integrable (fun x => u x * r x)
      (ν : Measure (feature_vector d)) := by
    apply Integrable.mono hr (hu.mul hrm).aestronglyMeasurable
    filter_upwards [] with x
    change |u x * r x| ≤ ‖r x‖
    rw [Real.norm_eq_abs, abs_mul]
    simpa using mul_le_mul_of_nonneg_right (hu_bound x) (abs_nonneg (r x))
  have hr_eq (x : feature_vector d) :
      r x = positive_shap_operator ν u i x + k x := by
    dsimp [r, k]
    rw [hlinear]
    ring
  have huk_int : Integrable (fun x => u x * k x)
      (ν : Measure (feature_vector d)) := by
    apply Integrable.congr (hur.sub huAu)
    exact Filter.Eventually.of_forall fun x => by
      change u x * r x - u x * positive_shap_operator ν u i x = u x * k x
      rw [hr_eq]
      ring
  have hinner : (∫ x,
      u x * positive_shap_operator ν u i x
      ∂(ν : Measure (feature_vector d))) =
      ∫ x, u x * r x ∂(ν : Measure (feature_vector d)) := by
    have hadd := integral_add huAu huk_int
    rw [huk_zero, add_zero] at hadd
    rw [← hadd]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change u x * positive_shap_operator ν u i x + u x * k x = u x * r x
      rw [hr_eq]
      ring
  have hdpos : (0 : ℝ) < d := by
    exact_mod_cast Nat.zero_lt_of_lt i.isLt
  have hcoercive := spectral_pullback_positive_operator_coercive
    ρ u i 1 (by norm_num) hu hu_bound
  rw [hinner] at hcoercive
  let U2 := ∫ x, u x ^ 2 ∂(ν : Measure (feature_vector d))
  have hUI : U2 ≤ (d : ℝ) *
      (∫ x, u x * r x ∂(ν : Measure (feature_vector d))) := by
    dsimp [U2] at *
    have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
    calc
      (∫ x, u x ^ 2 ∂(ν : Measure (feature_vector d))) =
          (d : ℝ) * ((d : ℝ)⁻¹ *
            ∫ x, u x ^ 2 ∂(ν : Measure (feature_vector d))) := by
              field_simp
      _ ≤ (d : ℝ) * (∫ x, u x * r x
            ∂(ν : Measure (feature_vector d))) :=
        mul_le_mul_of_nonneg_left hcoercive (le_of_lt hdpos)
  have habsr : Integrable (fun x => |r x|)
      (ν : Measure (feature_vector d)) := by
    simpa [Real.norm_eq_abs] using hr.norm
  have hcorr : (∫ x, u x * r x
      ∂(ν : Measure (feature_vector d))) ≤
      ∫ x, |r x| ∂(ν : Measure (feature_vector d)) := by
    apply integral_mono_ae hur habsr
    filter_upwards [] with x
    calc
      u x * r x ≤ |u x * r x| := le_abs_self _
      _ = |u x| * |r x| := abs_mul _ _
      _ ≤ 1 * |r x| :=
        mul_le_mul_of_nonneg_right (hu_bound x) (abs_nonneg (r x))
      _ = |r x| := one_mul _
  have habs_eq : (∫ x, |r x| ∂(ν : Measure (feature_vector d))) =
      aggregate_shap_value ν f i := by
    unfold aggregate_shap_value
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hr_shap]
  refine ⟨g, hgdet, ?_⟩
  change U2 ≤ (d : ℝ) * ε
  calc
    U2 ≤ (d : ℝ) * (∫ x, u x * r x
        ∂(ν : Measure (feature_vector d))) := hUI
    _ ≤ (d : ℝ) * (∫ x, |r x|
        ∂(ν : Measure (feature_vector d))) :=
      mul_le_mul_of_nonneg_left hcorr (le_of_lt hdpos)
    _ = (d : ℝ) * aggregate_shap_value ν f i := by rw [habs_eq]
    _ ≤ (d : ℝ) * ε :=
      mul_le_mul_of_nonneg_left haggregate (le_of_lt hdpos)

@[blueprint "lem:one-dimensional-strict-distribution-bound"
  (statement := /-- Let $\mu$ be a probability measure on $\mathbb{R}$, let
  $f:\mathbb{R}\to\mathbb{R}$ be measurable and take values in $[0,1]$, and let
  $\epsilon>0$. If $\overline{\phi_0}(\mu^*,f)\leq\epsilon$, then there exists a
  measurable function $g:\mathbb{R}\to\mathbb{R}$, constant on
  $\operatorname{supp}(\mu^*)$, such that
  \[
    \int(f(x)-g(x))^2\,d\mu^*(x)<\epsilon.
  \] -/)
  (proof := /-- Let $m=\int f\,d\mu^*$ and take $g\equiv m$.  The range assumption
  gives $0\leq m\leq1$.  When $d=1$, expansion of
  \cref{def:shap-value,def:interventional-value} gives
  $\phi_0(\mu^*,f,x)=f(x)-m$.

  Put $u=f-m$.  For every $x$, splitting according to the sign of $u(x)$ and using
  $0\leq f(x),m\leq1$ gives
  \[
    u(x)^2\leq\tfrac12|u(x)|+(\tfrac12-m)u(x).
  \]
  Since $\int u\,d\mu^*=0$, integration and
  \cref{def:aggregate-shap-value} yield
  $\int u^2\,d\mu^*\leq\tfrac12\overline{\phi_0}(\mu^*,f)
  \leq\epsilon/2<\epsilon$. -/)
  (title := /-- Strict one-dimensional feature-discarding estimate -/)
  (latexEnv := "lemma")]
lemma one_dimensional_strict_distribution_bound
    (μ : ProbabilityMeasure (feature_vector 1)) (f : feature_vector 1 → ℝ)
    (ε : ℝ) (hε : 0 < ε) (hf : Measurable f)
    (hf_range : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (haggregate :
      aggregate_shap_value (extended_distribution μ) f (0 : Fin 1) ≤ ε) :
    ∃ g : feature_vector 1 → ℝ,
      is_determined_except_on (extended_distribution μ) (0 : Fin 1) g ∧
      (∫ x, (f x - g x) ^ 2
        ∂(extended_distribution μ : Measure (feature_vector 1))) < ε := by
  let ν := extended_distribution μ
  let m : ℝ := ∫ x, f x ∂(ν : Measure (feature_vector 1))
  let u : feature_vector 1 → ℝ := fun x => f x - m
  let g : feature_vector 1 → ℝ := fun _ => m
  have hf_int : Integrable f (ν : Measure (feature_vector 1)) := by
    apply Integrable.of_bound hf.aestronglyMeasurable 1
    filter_upwards [] with x
    change |f x| ≤ 1
    rw [abs_of_nonneg (hf_range x).1]
    exact (hf_range x).2
  have hm : m ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [m]
      apply integral_nonneg_of_ae
      filter_upwards [] with x
      exact (hf_range x).1
    · dsimp [m]
      calc
        (∫ x, f x ∂(ν : Measure (feature_vector 1))) ≤
            ∫ _x, (1 : ℝ) ∂(ν : Measure (feature_vector 1)) := by
          apply integral_mono_ae hf_int (integrable_const 1)
          filter_upwards [] with x
          exact (hf_range x).2
        _ = 1 := by simp
  have hu : Measurable u := hf.sub measurable_const
  have hu_bound : ∀ x, |u x| ≤ 1 := fun x => by
    rw [abs_le]
    dsimp [u]
    constructor <;> linarith [(hf_range x).1, (hf_range x).2, hm.1, hm.2]
  have hu_int : Integrable u (ν : Measure (feature_vector 1)) := by
    dsimp [u]
    exact hf_int.sub (integrable_const m)
  have habsu_int : Integrable (fun x => |u x|)
      (ν : Measure (feature_vector 1)) := by
    simpa [Real.norm_eq_abs] using hu_int.norm
  have hu2_int : Integrable (fun x => u x ^ 2)
      (ν : Measure (feature_vector 1)) := by
    apply Integrable.of_bound (hu.pow_const 2).aestronglyMeasurable 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_sq, ← sq_abs]
    nlinarith [hu_bound x, abs_nonneg (u x)]
  have hzero : (∫ x, u x ∂(ν : Measure (feature_vector 1))) = 0 := by
    dsimp [u, m]
    rw [integral_sub hf_int (integrable_const _)]
    simp
  have hshap (x : feature_vector 1) :
      shap_value ν f (0 : Fin 1) x = u x := by
    have hfull (y : feature_vector 1) :
        mix_features ({0} : Finset (Fin 1)) x y = x := by
      funext j
      fin_cases j
      simp [mix_features]
    have hempty (y : feature_vector 1) :
        mix_features (∅ : Finset (Fin 1)) x y = y := by
      funext j
      simp [mix_features]
    dsimp [ν, u, m]
    simp [shap_value, interventional_value, hfull, hempty]
  have hagg_eq : aggregate_shap_value ν f (0 : Fin 1) =
      ∫ x, |u x| ∂(ν : Measure (feature_vector 1)) := by
    unfold aggregate_shap_value
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hshap]
  have hpoint (x : feature_vector 1) :
      u x ^ 2 ≤ (1 / 2 : ℝ) * |u x| + (1 / 2 - m) * u x := by
    dsimp [u]
    by_cases hx : 0 ≤ f x - m
    · rw [abs_of_nonneg hx]
      nlinarith [(hf_range x).2, hm.2]
    · have hx' : f x - m ≤ 0 := le_of_not_ge hx
      rw [abs_of_nonpos hx']
      nlinarith [(hf_range x).1, hm.1]
  have hright_int : Integrable
      (fun x => (1 / 2 : ℝ) * |u x| + (1 / 2 - m) * u x)
      (ν : Measure (feature_vector 1)) :=
    (habsu_int.const_mul (1 / 2 : ℝ)).add
      (hu_int.const_mul (1 / 2 - m))
  have hsq_le :
      (∫ x, u x ^ 2 ∂(ν : Measure (feature_vector 1))) ≤
        (1 / 2 : ℝ) * ∫ x, |u x| ∂(ν : Measure (feature_vector 1)) := by
    calc
      (∫ x, u x ^ 2 ∂(ν : Measure (feature_vector 1))) ≤
          ∫ x, ((1 / 2 : ℝ) * |u x| + (1 / 2 - m) * u x)
            ∂(ν : Measure (feature_vector 1)) := by
        apply integral_mono_ae hu2_int hright_int
        exact Filter.Eventually.of_forall hpoint
      _ = (1 / 2 : ℝ) * ∫ x, |u x|
            ∂(ν : Measure (feature_vector 1)) := by
        rw [integral_add (habsu_int.const_mul _) (hu_int.const_mul _),
          integral_const_mul, integral_const_mul, hzero, mul_zero, add_zero]
  refine ⟨g, ?_, ?_⟩
  · constructor
    · exact measurable_const
    · intro x hx y hy hxy
      rfl
  · change (∫ x, u x ^ 2 ∂(ν : Measure (feature_vector 1))) < ε
    calc
      (∫ x, u x ^ 2 ∂(ν : Measure (feature_vector 1))) ≤
          (1 / 2 : ℝ) * ∫ x, |u x|
            ∂(ν : Measure (feature_vector 1)) := hsq_le
      _ = (1 / 2 : ℝ) * aggregate_shap_value ν f (0 : Fin 1) := by
        rw [hagg_eq]
      _ ≤ (1 / 2 : ℝ) * ε :=
        mul_le_mul_of_nonneg_left haggregate (by norm_num)
      _ < ε := by linarith

@[blueprint "lem:strict-bound-from-source"
  (statement := /-- Let $d\in\mathbb{N}$, let $\mu$ be a probability measure on
  $\mathbb{R}^{d}$, let $f:\mathbb{R}^{d}\to\mathbb{R}$ be measurable and take values in
  $[0,1]$, let $i\in\operatorname{Fin}(d)$, and let $\epsilon\in\mathbb{R}$ satisfy
  $0<\epsilon$. If $\overline{\phi_i}(\mu^*,f)\leq\epsilon$, then there exists a measurable
  function $g:\mathbb{R}^{d}\to\mathbb{R}$, determined on
  $\operatorname{supp}(\mu^*)$ by every feature except $i$, such that
  \[
    \int(f(x)-g(x))^2\,d\mu^*(x)<d^2\epsilon.
  \] -/)
  (proof := /-- First apply
  \cref{lem:nonstrict-robust-distribution-bound}.  If its witness has squared error
  strictly below $d^2\epsilon$, it proves the result directly.  It remains to treat the
  case in which that error equals $d^2\epsilon$.

  If $d=1$, replace the witness using
  \cref{lem:one-dimensional-strict-distribution-bound}; its constant witness has squared
  error strictly less than $\epsilon=d^2\epsilon$.  If $d\neq1$, then
  $i\in\operatorname{Fin}(d)$ implies $d\geq2$.  Apply
  \cref{lem:linear-robust-distribution-bound} to obtain a measurable function $g$,
  determined on $\operatorname{supp}(\mu^*)$ by every feature except $i$, such that
  \[
    \int(f(x)-g(x))^2\,d\mu^*(x)\leq d\epsilon.
  \]
  The inequalities $d\geq2$ and $\epsilon>0$ imply
  $d\epsilon<d^2\epsilon$, which proves the required strict estimate. -/)
  (title := /-- Strict robust feature-discarding bound -/)
  (latexEnv := "lemma")]
lemma strict_bound_from_source {d : ℕ}
    (μ : ProbabilityMeasure (feature_vector d)) (f : feature_vector d → ℝ)
    (i : Fin d) (ε : ℝ) (hε : 0 < ε) (hf : Measurable f)
    (hf_range : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (haggregate : aggregate_shap_value (extended_distribution μ) f i ≤ ε) :
    ∃ g : feature_vector d → ℝ,
      is_determined_except_on (extended_distribution μ) i g ∧
      (∫ x, (f x - g x) ^ 2
        ∂(extended_distribution μ : Measure (feature_vector d))) < (d : ℝ) ^ 2 * ε := by
  obtain ⟨g₀, hg₀, hbound₀⟩ :=
    nonstrict_robust_distribution_bound μ f i ε hf hf_range haggregate
  by_cases heq : (∫ x, (f x - g₀ x) ^ 2
      ∂(extended_distribution μ : Measure (feature_vector d))) =
      (d : ℝ) ^ 2 * ε
  · by_cases hd : d = 1
    · subst d
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      simpa using one_dimensional_strict_distribution_bound
        μ f ε hε hf hf_range haggregate
    · have hdpos_nat : 0 < d := Nat.zero_lt_of_lt i.isLt
      have hd_two : 2 ≤ d := by omega
      obtain ⟨g, hg, hbound⟩ :=
        linear_robust_distribution_bound μ f i ε hf hf_range haggregate
      refine ⟨g, hg, lt_of_le_of_lt hbound ?_⟩
      have hdpos : (0 : ℝ) < d := by exact_mod_cast hdpos_nat
      have hone_lt_d : (1 : ℝ) < d := by exact_mod_cast hd_two
      have hdlt : (d : ℝ) < (d : ℝ) ^ 2 := by
        calc
          (d : ℝ) = (d : ℝ) * 1 := by ring
          _ < (d : ℝ) * (d : ℝ) :=
            mul_lt_mul_of_pos_left hone_lt_d hdpos
          _ = (d : ℝ) ^ 2 := by ring
      exact mul_lt_mul_of_pos_right hdlt hε
  · exact ⟨g₀, hg₀, lt_of_le_of_ne hbound₀ heq⟩

@[blueprint "thm:small-mu-star-shap-allows-discard-feature"
  (statement := /-- Let $d\in\mathbb{N}$, let $\mu$ be a probability measure on
  $\mathbb{R}^{d}$, and let $f:\mathbb{R}^{d}\to\mathbb{R}$ be measurable and satisfy
  $0\leq f(x)\leq1$ for every $x\in\mathbb{R}^{d}$.  Let
  $i\in\operatorname{Fin}(d)$ and $\epsilon\in\mathbb{R}$ satisfy $0<\epsilon$.  Suppose
  that the aggregate SHAP value, computed and averaged under the extended distribution,
  satisfies $\overline{\phi_i}(\mu^*,f)\leq\epsilon$.  Then there exists a measurable
  function $g:\mathbb{R}^{d}\to\mathbb{R}$ such that, whenever
  $x,y\in\operatorname{supp}(\mu^*)$ agree in every coordinate other than $i$, one has
  $g(x)=g(y)$, and
  \[
    \int(f(x)-g(x))^2\,d\mu^*(x)<d^2\epsilon.
  \] -/)
  (proof := /-- Apply \cref{lem:strict-bound-from-source} with the given probability
  measure, bounded measurable function, feature, positive tolerance, and non-strict aggregate
  SHAP bound. Its witness $g$ has precisely the required determination property on the extended
  support and the asserted strict squared-error estimate. -/)
  (title := /-- Small aggregate SHAP value allows a feature to be discarded -/)
  (latexEnv := "theorem")]
theorem small_mu_star_shap_allows_discard_feature {d : ℕ}
    (μ : ProbabilityMeasure (feature_vector d)) (f : feature_vector d → ℝ)
    (i : Fin d) (ε : ℝ) (hε : 0 < ε) (hf : Measurable f)
    (hf_range : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (haggregate : aggregate_shap_value (extended_distribution μ) f i ≤ ε) :
    ∃ g : feature_vector d → ℝ,
      is_determined_except_on (extended_distribution μ) i g ∧
      (∫ x, (f x - g x) ^ 2
        ∂(extended_distribution μ : Measure (feature_vector d))) < (d : ℝ) ^ 2 * ε := by
  exact strict_bound_from_source μ f i ε hε hf hf_range haggregate

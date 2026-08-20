import Architect
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators Interval
open MeasureTheory Set

@[blueprint "def:coordinate-laws-supported"
  (statement := /-- A family of coordinate probability laws is supported on the unit interval if, for every coordinate, the sampled real number belongs to $[0,1]$ almost surely. -/)
  (title := /-- Coordinate Laws Supported on the Unit Interval -/)
  (latexEnv := "definition")]
def coordinate_laws_supported {n : ℕ}
    (D : Fin n → ProbabilityMeasure ℝ) : Prop :=
  ∀ i, ∀ᵐ y ∂(D i : Measure ℝ), y ∈ Icc (0 : ℝ) 1

@[blueprint "def:distribution-means"
  (statement := /-- For coordinate probability laws $D_i$, define the mean vector $x$ by $x_i=\int_{\mathbb{R}} y\,dD_i(y)$. -/)
  (title := /-- Vector of Coordinate Means -/)
  (latexEnv := "definition")]
noncomputable def distribution_means {n : ℕ}
    (D : Fin n → ProbabilityMeasure ℝ) : Fin n → ℝ :=
  fun i ↦ ∫ y, y ∂(D i : Measure ℝ)

@[blueprint "def:vector-mean"
  (statement := /-- For $x\in\mathbb{R}^n$, define $\mu(x)=n^{-1}\sum_{i=1}^n x_i$. -/)
  (title := /-- Arithmetic Mean of a Finite Vector -/)
  (latexEnv := "definition")]
noncomputable def vector_mean {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (∑ i, x i) / (n : ℝ)

@[blueprint "def:vector-variance"
  (statement := /-- For $x\in\mathbb{R}^n$, define $\sigma^2(x)=n^{-1}\sum_{i=1}^n x_i^2-\mu(x)^2$. -/)
  (title := /-- Variance of a Finite Vector -/)
  (latexEnv := "definition")]
noncomputable def vector_variance {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (∑ i, (x i) ^ 2) / (n : ℝ) - (vector_mean x) ^ 2

@[blueprint "def:strict-pair-sum"
  (statement := /-- For a function $f$ of two indices, define its strict-pair sum by summing $f(i,j)$ over all pairs with $i<j$. -/)
  (title := /-- Sum over Strictly Ordered Pairs -/)
  (latexEnv := "definition")]
def strict_pair_sum {n : ℕ} (f : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n ↦ i < j), f i j

@[blueprint "def:bernoulli-kernel"
  (statement := /-- For distinct indices $i,j$, define the Bernoulli kernel by
  \[
    K_{i,j}(x)=\int_0^1\prod_{k\ne i,j}(1-tx_k)\,dt.
  \] -/)
  (title := /-- Bernoulli Pair Kernel -/)
  (latexEnv := "definition")]
noncomputable def bernoulli_kernel {n : ℕ}
    (x : Fin n → ℝ) (i j : Fin n) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    ∏ k ∈ Finset.univ.filter (fun k : Fin n ↦ k ≠ i ∧ k ≠ j), (1 - t * x k)

@[blueprint "def:bernoulli-weight"
  (statement := /-- The $i$th coordinate of the Bernoulli-derived multilinear strategy is
  \[
    q_i(x)=x_i\int_0^1\prod_{k\ne i}(1-tx_k)\,dt
      +\frac1n\prod_{k=1}^n(1-x_k).
  \]
  This is the multilinear extension of the rule that chooses uniformly among the coordinates equal to one, with the uniform distribution on all coordinates at the all-zero vertex. -/)
  (title := /-- Bernoulli-Derived Multilinear Weight -/)
  (latexEnv := "definition")]
noncomputable def bernoulli_weight {n : ℕ}
    (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  x i * (∫ t in (0 : ℝ)..1,
    ∏ k ∈ Finset.univ.filter (fun k : Fin n ↦ k ≠ i), (1 - t * x k))
    + (n : ℝ)⁻¹ * ∏ k, (1 - x k)

@[blueprint "def:strategy-value"
  (statement := /-- Given coordinate laws $D_i$ and a weight rule $S$, define
  \[
    \operatorname{val}(S;D)
      =\int_{\mathbb{R}^n}\sum_{i=1}^n x_i S(y)_i\,
        d\Bigl(\mathop{\times}_{i=1}^n D_i\Bigr)(y),
  \]
  where $x_i=\int y\,dD_i(y)$ and the product measure represents independent coordinate samples. -/)
  (title := /-- Value of a Weighting Strategy -/)
  (latexEnv := "definition")]
noncomputable def strategy_value {n : ℕ}
    (D : Fin n → ProbabilityMeasure ℝ)
    (S : (Fin n → ℝ) → Fin n → ℝ) : ℝ :=
  ∫ y, ∑ i, distribution_means D i * S y i
    ∂(ProbabilityMeasure.pi D : Measure (Fin n → ℝ))

@[blueprint "lem:distribution-means-unit-interval"
  (statement := /-- Let $n\in\mathbb{N}$, and for each $i\in\operatorname{Fin}(n)$ let $D_i$ be a probability measure on $\mathbb{R}$ such that $D_i$-almost every $y$ lies in $[0,1]$. Define $x_i=\int_{\mathbb{R}} y\,dD_i(y)$ as in \cref{def:distribution-means}. Then $x_i\in[0,1]$ for every $i\in\operatorname{Fin}(n)$. -/)
  (proof := /-- Fix $i\in\operatorname{Fin}(n)$. By \cref{def:coordinate-laws-supported}, one has $0\leq y\leq1$ for $D_i$-almost every $y$. Hence $|y|\leq1$ almost everywhere. Since $D_i$ is a probability measure, the constant function $1$ is integrable, so domination proves that the identity function is integrable. Almost-everywhere nonnegativity and monotonicity of the integral now give
  \[
    0\leq \int_{\mathbb{R}} y\,dD_i(y)
      \leq \int_{\mathbb{R}}1\,dD_i(y)=1.
  \]
  By \cref{def:distribution-means}, the middle integral is $x_i$, and therefore $x_i\in[0,1]$. -/)
  (title := /-- Supported Laws Have Means in the Unit Interval -/)
  (latexEnv := "lemma")]
lemma distribution_means_unit_interval {n : ℕ}
    (D : Fin n → ProbabilityMeasure ℝ)
    (hD : coordinate_laws_supported D) :
    ∀ i, distribution_means D i ∈ Icc (0 : ℝ) 1 := by
  intro i
  change (∫ y, y ∂(D i : Measure ℝ)) ∈ Icc 0 1
  have hy_int : Integrable (fun y : ℝ => y) (D i : Measure ℝ) :=
    (integrable_const (μ := (D i : Measure ℝ)) (1 : ℝ)).mono'
      continuous_id.aestronglyMeasurable
      ((hD i).mono fun y hy => by
        simpa [Real.norm_eq_abs, abs_of_nonneg hy.1] using hy.2)
  constructor
  · exact integral_nonneg_of_ae ((hD i).mono fun y hy => hy.1)
  · simpa using
      (integral_mono_ae hy_int
        (integrable_const (μ := (D i : Measure ℝ)) (1 : ℝ))
        ((hD i).mono fun y hy => hy.2))

@[blueprint "lem:bernoulli-weights-sum-one"
  (statement := /-- Let $n$ be a positive integer. For every $x\in\mathbb{R}^n$, the weights from \cref{def:bernoulli-weight} satisfy $\sum_i q_i(x)=1$. -/)
  (proof := /-- Define $P(t)=\prod_k(1-tx_k)$. The finite-product rule gives
  \[
    P'(t)=-\sum_i x_i\prod_{k\ne i}(1-tx_k).
  \]
  This derivative is continuous, so the fundamental theorem of calculus yields
  \[
    \int_0^1\sum_i x_i\prod_{k\ne i}(1-tx_k)\,dt
      =P(0)-P(1)=1-\prod_k(1-x_k).
  \]
  Expand the weights using \cref{def:bernoulli-weight} and commute the finite sum with the interval integral. The preceding identity evaluates the sum of the integral terms. The remaining term is
  \[
    \sum_i \frac1n\prod_k(1-x_k)=\prod_k(1-x_k),
  \]
  because $n>0$. Adding the two contributions gives $1$. -/)
  (title := /-- Normalization of the Bernoulli Weights -/)
  (latexEnv := "lemma")]
lemma bernoulli_weights_sum_one {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) :
    ∑ i, bernoulli_weight x i = 1 := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast hn.ne'
  let p : ℝ → ℝ := fun t ↦ ∏ k : Fin n, (1 - t * x k)
  have hp_deriv (t : ℝ) :
      HasDerivAt p
        (-∑ i : Fin n, x i *
          ∏ k ∈ Finset.univ.filter (fun k : Fin n ↦ k ≠ i), (1 - t * x k)) t := by
    dsimp [p]
    convert HasDerivAt.finsetProd
      (u := Finset.univ)
      (f := fun k : Fin n ↦ fun s : ℝ ↦ 1 - s * x k)
      (f' := fun k : Fin n ↦ -x k)
      (x := t) (fun i hi ↦ by
        simpa using ((hasDerivAt_id t).mul_const (x i)).const_sub 1) using 1
    · rfl
    · rfl
    · funext s
      simp
    · simp [Finset.filter_ne', mul_comm]
  have hinterval : IntervalIntegrable
      (fun t : ℝ ↦ -∑ i : Fin n, x i *
        ∏ k ∈ Finset.univ.filter (fun k : Fin n ↦ k ≠ i), (1 - t * x k))
      volume 0 1 := by
    exact (by fun_prop : Continuous (fun t : ℝ ↦ -∑ i : Fin n, x i *
      ∏ k ∈ Finset.univ.filter (fun k : Fin n ↦ k ≠ i), (1 - t * x k))).intervalIntegrable 0 1
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := p)
    (f' := fun t : ℝ ↦ -∑ i : Fin n, x i *
      ∏ k ∈ Finset.univ.filter (fun k : Fin n ↦ k ≠ i), (1 - t * x k))
    (a := (0 : ℝ)) (b := 1) (fun t ht ↦ hp_deriv t) hinterval
  have hmain :
      (∫ t in (0 : ℝ)..1, ∑ i : Fin n, x i *
        ∏ k ∈ Finset.univ.filter (fun k : Fin n ↦ k ≠ i), (1 - t * x k)) =
        1 - ∏ k : Fin n, (1 - x k) := by
    simp only [intervalIntegral.integral_neg] at hfund
    dsimp [p] at hfund
    simp only [zero_mul, sub_zero, one_mul, Finset.prod_const_one] at hfund
    linarith
  have hsum_integral :
      (∫ t in (0 : ℝ)..1, ∑ i : Fin n, x i *
        ∏ k ∈ Finset.univ.filter (fun k : Fin n ↦ k ≠ i), (1 - t * x k)) =
      ∑ i : Fin n, x i * (∫ t in (0 : ℝ)..1,
        ∏ k ∈ Finset.univ.filter (fun k : Fin n ↦ k ≠ i), (1 - t * x k)) := by
    rw [intervalIntegral.integral_finsetSum]
    · simp
    · intro i hi
      exact (by fun_prop : Continuous (fun t : ℝ ↦ x i *
        ∏ k ∈ Finset.univ.filter (fun k : Fin n ↦ k ≠ i),
          (1 - t * x k))).intervalIntegrable 0 1
  unfold bernoulli_weight
  rw [Finset.sum_add_distrib, ← hsum_integral, hmain]
  simp [hn0]

@[blueprint "lem:bernoulli-weight-expectation-lintegral-prod"
  (statement := /-- Let $n\in\mathbb{N}$, let $(D_i)_{i\in\operatorname{Fin}(n)}$ be probability measures on $\mathbb{R}$, and let $f_i\colon\mathbb{R}\to[0,\infty]$ be measurable. Then
  \[
    \int \prod_k f_k(y_k)\,d\!\left(\bigotimes_k D_k\right)(y)
      =\prod_k\int_{\mathbb{R}} f_k(y)\,dD_k(y),
  \]
  where both sides are lower Lebesgue integrals. -/)
  (proof := /-- Induct on $n$. The assertion is immediate for the empty product. For the successor step, use the measure-preserving equivalence that separates the zeroth coordinate from the remaining coordinates. Tonelli's theorem factors the resulting two-variable lower integral, and the induction hypothesis evaluates the lower integral over the remaining coordinates. -/)
  (title := /-- Lower Integral of a Product of Coordinate Functions -/)
  (latexEnv := "lemma")]
lemma bernoulli_weight_expectation_lintegral_prod {n : ℕ}
    (D : Fin n → ProbabilityMeasure ℝ) (f : Fin n → ℝ → ENNReal)
    (hf : ∀ k, Measurable (f k)) :
    (∫⁻ y, ∏ k, f k (y k)
      ∂(ProbabilityMeasure.pi D : Measure (Fin n → ℝ))) =
      ∏ k, ∫⁻ z, f k z ∂(D k : Measure ℝ) := by
  simp only [ProbabilityMeasure.toMeasure_pi]
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        _ = ∫⁻ x : ℝ × (Fin n → ℝ),
            f 0 x.1 * ∏ j : Fin n, f j.succ (x.2 j)
            ∂((D 0 : Measure ℝ).prod
              (Measure.pi fun j => (D j.succ : Measure ℝ))) := by
          rw [← ((measurePreserving_piFinSuccAbove
            (fun k => (D k : Measure ℝ)) 0).symm).lintegral_comp]
          · simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
              Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
              Fin.zero_succAbove, cast_eq, Fin.cons_zero]
          · fun_prop
        _ = (∫⁻ x, f 0 x ∂(D 0 : Measure ℝ)) *
            ∏ j : Fin n, ∫⁻ z, f j.succ z ∂(D j.succ : Measure ℝ) := by
          have hG : Measurable (fun y : Fin n → ℝ =>
              ∏ j : Fin n, f j.succ (y j)) := by
            fun_prop
          rw [lintegral_prod]
          · simp_rw [lintegral_const_mul _ hG]
            rw [lintegral_mul_const _ (hf 0),
              ih (fun j => D j.succ) (fun j => f j.succ) (fun j => hf j.succ)]
          · fun_prop
        _ = ∏ k, ∫⁻ z, f k z ∂(D k : Measure ℝ) := by
          rw [Fin.prod_univ_succ]

@[blueprint "lem:bernoulli-weight-expectation-integral-prod-nonnegative"
  (statement := /-- Let $n\in\mathbb{N}$, let $(D_i)_{i\in\operatorname{Fin}(n)}$ be probability measures on $\mathbb{R}$, and let $f_i\colon\mathbb{R}\to\mathbb{R}$ be measurable and nonnegative almost everywhere with respect to $D_i$. Under the product law,
  \[
    \int \prod_k f_k(y_k)\,d\!\left(\bigotimes_k D_k\right)(y)
      =\prod_k\int_{\mathbb{R}}f_k(y)\,dD_k(y).
  \] -/)
  (proof := /-- Almost-everywhere nonnegativity in every coordinate implies almost-everywhere nonnegativity of the product under the product law. Convert the real integrals to lower integrals and use \cref{lem:bernoulli-weight-expectation-lintegral-prod} to factor the lower integral. The conversion maps commute with finite products of nonnegative factors, yielding the claimed real-valued equality. -/)
  (title := /-- Product-Law Integral of Nonnegative Coordinate Factors -/)
  (latexEnv := "lemma")]
lemma bernoulli_weight_expectation_integral_prod_nonnegative {n : ℕ}
    (D : Fin n → ProbabilityMeasure ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ k, Measurable (f k))
    (hf0 : ∀ k, 0 ≤ᵐ[(D k : Measure ℝ)] f k) :
    (∫ y, ∏ k, f k (y k)
      ∂(ProbabilityMeasure.pi D : Measure (Fin n → ℝ))) =
      ∏ k, ∫ z, f k z ∂(D k : Measure ℝ) := by
  have hpi : ∀ᵐ y ∂(ProbabilityMeasure.pi D : Measure (Fin n → ℝ)),
      ∀ k, 0 ≤ f k (y k) := by
    simp only [ProbabilityMeasure.toMeasure_pi]
    filter_upwards [Measure.ae_le_pi (μ := fun k => (D k : Measure ℝ)) hf0]
      with y hy
    intro k
    exact hy k
  rw [integral_eq_lintegral_of_nonneg_ae
    (hpi.mono fun y hy => Finset.prod_nonneg fun k hk => hy k)
    (Finset.measurable_prod Finset.univ (fun k hk =>
      (hf k).comp (measurable_pi_apply k))).aestronglyMeasurable]
  simp_rw [integral_eq_lintegral_of_nonneg_ae (hf0 _) (hf _).aestronglyMeasurable]
  rw [← ENNReal.toReal_prod]
  congr 1
  calc
    _ = ∫⁻ y, ∏ k, ENNReal.ofReal (f k (y k))
        ∂(ProbabilityMeasure.pi D : Measure (Fin n → ℝ)) := by
      apply lintegral_congr_ae
      filter_upwards [hpi] with y hy
      exact ENNReal.ofReal_prod_of_nonneg (fun k hk => hy k)
    _ = _ := bernoulli_weight_expectation_lintegral_prod D
      (fun k z => ENNReal.ofReal (f k z))
      (fun k => ENNReal.measurable_ofReal.comp (hf k))

@[blueprint "lem:bernoulli-weight-expectation-monomial"
  (statement := /-- Let $n\in\mathbb{N}$, let $(D_i)_{i\in\operatorname{Fin}(n)}$ be probability measures on $\mathbb{R}$ that are almost surely supported on $[0,1]$, and let $S\subseteq\operatorname{Fin}(n)$. If $x_i=\int_{\mathbb{R}}y\,dD_i(y)$, then
  \[
    \int \prod_{k\in S} y_k\,d\!\left(\bigotimes_k D_k\right)(y)
      =\prod_{k\in S}x_k.
  \] -/)
  (proof := /-- For each coordinate, take the factor $y_k$ when $k\in S$ and the constant factor $1$ otherwise. By \cref{def:coordinate-laws-supported}, every selected factor is nonnegative almost everywhere. Apply \cref{lem:bernoulli-weight-expectation-integral-prod-nonnegative}; the integrals of the selected factors are the corresponding coordinates of \cref{def:distribution-means}, while the remaining factors integrate to one because each coordinate law is a probability measure. -/)
  (title := /-- Product-Law Expectation of a Squarefree Monomial -/)
  (latexEnv := "lemma")]
lemma bernoulli_weight_expectation_monomial {n : ℕ}
    (D : Fin n → ProbabilityMeasure ℝ) (hD : coordinate_laws_supported D)
    (S : Finset (Fin n)) :
    (∫ y, ∏ k ∈ S, y k
      ∂(ProbabilityMeasure.pi D : Measure (Fin n → ℝ))) =
      ∏ k ∈ S, distribution_means D k := by
  have hf0 : ∀ k, 0 ≤ᵐ[(D k : Measure ℝ)]
      (fun z : ℝ => if k ∈ S then z else 1) := by
    intro k
    filter_upwards [hD k] with z hz
    split_ifs
    · exact hz.1
    · norm_num
  calc
    _ = ∫ y, ∏ k, (if k ∈ S then y k else 1)
        ∂(ProbabilityMeasure.pi D : Measure (Fin n → ℝ)) := by simp
    _ = ∏ k, ∫ z, (if k ∈ S then z else 1) ∂(D k : Measure ℝ) :=
      bernoulli_weight_expectation_integral_prod_nonnegative D
        (fun k z => if k ∈ S then z else 1)
        (fun k => by
          by_cases hk : k ∈ S
          · simp only [if_pos hk]
            exact measurable_id
          · simp [hk]) hf0
    _ = ∏ k, (if k ∈ S then distribution_means D k else 1) := by
      apply Finset.prod_congr rfl
      intro k hk
      by_cases hks : k ∈ S
      · simp [hks, distribution_means]
      · simp [hks]
    _ = _ := by simp

@[blueprint "lem:bernoulli-weight-expectation-monomial-integrable"
  (statement := /-- Let $n\in\mathbb{N}$, let $(D_i)_{i\in\operatorname{Fin}(n)}$ be probability measures on $\mathbb{R}$ that are almost surely supported on $[0,1]$, and let $S\subseteq\operatorname{Fin}(n)$. Then the squarefree monomial $y\mapsto\prod_{k\in S}y_k$ is integrable under the product law. -/)
  (proof := /-- The monomial is measurable as a finite product of coordinate projections. By \cref{def:coordinate-laws-supported}, every coordinate belongs to $[0,1]$ almost surely; the finite-product almost-everywhere comparison transfers both coordinate bounds to the product law. Hence the monomial also belongs to $[0,1]$ almost surely and is integrable because the product law is finite. -/)
  (title := /-- Integrability of Supported Squarefree Monomials -/)
  (latexEnv := "lemma")]
lemma bernoulli_weight_expectation_monomial_integrable {n : ℕ}
    (D : Fin n → ProbabilityMeasure ℝ) (hD : coordinate_laws_supported D)
    (S : Finset (Fin n)) :
    Integrable (fun y : Fin n → ℝ => ∏ k ∈ S, y k)
      (ProbabilityMeasure.pi D : Measure (Fin n → ℝ)) := by
  have h0 : ∀ k, (fun _ : ℝ => (0 : ℝ)) ≤ᵐ[(D k : Measure ℝ)]
      (fun z : ℝ => z) := by
    intro k
    exact (hD k).mono fun z hz => hz.1
  have h1 : ∀ k, (fun z : ℝ => z) ≤ᵐ[(D k : Measure ℝ)] (fun _ => (1 : ℝ)) := by
    intro k
    exact (hD k).mono fun z hz => hz.2
  have hpi0 : ∀ᵐ y ∂(ProbabilityMeasure.pi D : Measure (Fin n → ℝ)),
      ∀ k, 0 ≤ y k := by
    simp only [ProbabilityMeasure.toMeasure_pi]
    filter_upwards [Measure.ae_le_pi (μ := fun k => (D k : Measure ℝ)) h0]
      with y hy
    intro k
    exact hy k
  have hpi1 : ∀ᵐ y ∂(ProbabilityMeasure.pi D : Measure (Fin n → ℝ)),
      ∀ k, y k ≤ 1 := by
    simp only [ProbabilityMeasure.toMeasure_pi]
    filter_upwards [Measure.ae_le_pi (μ := fun k => (D k : Measure ℝ)) h1]
      with y hy
    intro k
    exact hy k
  apply Integrable.of_bound
    (Finset.measurable_prod S (fun k hk => measurable_pi_apply k)).aestronglyMeasurable 1
  filter_upwards [hpi0, hpi1] with y hy0 hy1
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun k hk => hy0 k)]
  exact Finset.prod_le_one (fun k hk => hy0 k) (fun k hk => hy1 k)

@[blueprint "lem:bernoulli-weight-expectation-multilinear-expansion"
  (statement := /-- For $n\in\mathbb{N}$, $x\in\mathbb{R}^n$, and $i\in\operatorname{Fin}(n)$, put $A_i=\{k:k\ne i\}$. Then the Bernoulli weight has the squarefree expansion
  \[
  \begin{aligned}
    q_i(x)={}&\sum_{S\subseteq A_i}
      \left(\int_0^1\prod_{k\in S}(-t)\,dt\right)
      \prod_{k\in S\cup\{i\}}x_k\\
    &+\frac1n\sum_{S\subseteq\operatorname{Fin}(n)}
      \left(\prod_{k\in S}(-1)\right)\prod_{k\in S}x_k.
  \end{aligned}
  \] -/)
  (proof := /-- Expand each product in \cref{def:bernoulli-weight} with the finite product identity $\prod_k(1+u_k)=\sum_S\prod_{k\in S}u_k$. Distribute the finite sum through the interval integral in the first term. Since $i\notin A_i$, adjoining $i$ to each subset multiplies its monomial by $x_i$. Finally, separate every factor $-t x_k$ as $(-t)x_k$ and every factor $-x_k$ as $(-1)x_k$. -/)
  (title := /-- Squarefree Expansion of a Bernoulli Weight -/)
  (latexEnv := "lemma")]
lemma bernoulli_weight_expectation_multilinear_expansion {n : ℕ}
    (x : Fin n → ℝ) (i : Fin n) :
    bernoulli_weight x i =
      (∑ S ∈ (Finset.univ.filter (fun k : Fin n => k ≠ i)).powerset,
        (∫ t in (0 : ℝ)..1, ∏ k ∈ S, (-t)) * ∏ k ∈ insert i S, x k) +
      (n : ℝ)⁻¹ *
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          (∏ k ∈ S, (-1 : ℝ)) * ∏ k ∈ S, x k := by
  classical
  unfold bernoulli_weight
  simp_rw [sub_eq_add_neg, Finset.prod_one_add]
  have hprod_t (S : Finset (Fin n)) (t : ℝ) :
      (∏ k ∈ S, -(t * x k)) =
        (∏ k ∈ S, (-t)) * ∏ k ∈ S, x k := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k hk
    ring
  have hprod_one (S : Finset (Fin n)) :
      (∏ k ∈ S, -x k) =
        (∏ k ∈ S, (-1 : ℝ)) * ∏ k ∈ S, x k := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k hk
    ring
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [hprod_t, intervalIntegral.integral_mul_const]
    rw [Finset.mul_sum]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro S hS
      have hiS : i ∉ S := by
        intro hi
        have hsub := Finset.mem_powerset.mp hS hi
        exact (Finset.mem_filter.mp hsub).2 rfl
      rw [Finset.prod_insert hiS]
      ring
    · apply congrArg ((n : ℝ)⁻¹ * ·)
      apply Finset.sum_congr rfl
      intro S hS
      exact hprod_one S
  · intro S hS
    exact (by fun_prop : Continuous (fun t : ℝ => ∏ k ∈ S, -(t * x k))).intervalIntegrable 0 1

@[blueprint "lem:bernoulli-weight-expectation"
  (statement := /-- Let $n\in\mathbb{N}$, and let $(D_i)_{i\in\operatorname{Fin}(n)}$ be probability measures on $\mathbb{R}$ that are almost surely supported on $[0,1]$. Let $y$ have the product law of the $D_i$, and set $x_i=\int_{\mathbb{R}} y\,dD_i(y)$. Then, for every $i\in\operatorname{Fin}(n)$,
  \[
    \mathbb{E}[q_i(y)]=q_i(x).
  \] -/)
  (proof := /-- Apply \cref{lem:bernoulli-weight-expectation-multilinear-expansion} to both $q_i(y)$ and $q_i(x)$. This writes each weight as the same finite linear combination of squarefree monomials, with coefficients independent of the sampled vector. By \cref{lem:bernoulli-weight-expectation-monomial-integrable}, every monomial in these finite sums is integrable, so linearity of the integral applies term by term. Then \cref{lem:bernoulli-weight-expectation-monomial} replaces the expectation of each sampled monomial by the corresponding monomial in the coordinate means. The resulting two finite sums are exactly the expansion of $q_i(x)$. -/)
  (title := /-- Expectation of a Bernoulli Weight -/)
  (latexEnv := "lemma")]
lemma bernoulli_weight_expectation {n : ℕ}
    (D : Fin n → ProbabilityMeasure ℝ)
    (hD : coordinate_laws_supported D) (i : Fin n) :
    (∫ y, bernoulli_weight y i
      ∂(ProbabilityMeasure.pi D : Measure (Fin n → ℝ))) =
      bernoulli_weight (distribution_means D) i := by
  classical
  simp_rw [bernoulli_weight_expectation_multilinear_expansion]
  have hsum₁ : Integrable
      (fun y : Fin n → ℝ =>
        ∑ S ∈ (Finset.univ.filter (fun k : Fin n => k ≠ i)).powerset,
          (∫ t in (0 : ℝ)..1, ∏ k ∈ S, (-t)) * ∏ k ∈ insert i S, y k)
      (ProbabilityMeasure.pi D : Measure (Fin n → ℝ)) := by
    apply integrable_finsetSum
    intro S hS
    exact (bernoulli_weight_expectation_monomial_integrable D hD (insert i S)).const_mul _
  have hsum₂ : Integrable
      (fun y : Fin n → ℝ =>
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          (∏ k ∈ S, (-1 : ℝ)) * ∏ k ∈ S, y k)
      (ProbabilityMeasure.pi D : Measure (Fin n → ℝ)) := by
    apply integrable_finsetSum
    intro S hS
    exact (bernoulli_weight_expectation_monomial_integrable D hD S).const_mul _
  rw [integral_add hsum₁ (hsum₂.const_mul (n : ℝ)⁻¹)]
  apply congrArg₂ (· + ·)
  · rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro S hS
      rw [integral_const_mul_of_integrable
        (bernoulli_weight_expectation_monomial_integrable D hD (insert i S))]
      rw [bernoulli_weight_expectation_monomial D hD (insert i S)]
    · intro S hS
      exact (bernoulli_weight_expectation_monomial_integrable D hD (insert i S)).const_mul _
  · rw [integral_const_mul_of_integrable hsum₂, integral_finsetSum]
    · apply congrArg ((n : ℝ)⁻¹ * ·)
      apply Finset.sum_congr rfl
      intro S hS
      rw [integral_const_mul_of_integrable
        (bernoulli_weight_expectation_monomial_integrable D hD S)]
      rw [bernoulli_weight_expectation_monomial D hD S]
    · intro S hS
      exact (bernoulli_weight_expectation_monomial_integrable D hD S).const_mul _

@[blueprint "lem:bernoulli-weight-integrable"
  (statement := /-- Let $n\in\mathbb{N}$, let $(D_i)_{i\in\operatorname{Fin}(n)}$ be probability measures on $\mathbb{R}$ that are almost surely supported on $[0,1]$, and let $i\in\operatorname{Fin}(n)$. Then $y\mapsto q_i(y)$ is integrable under the independent product law of the $D_i$. -/)
  (proof := /-- By \cref{lem:bernoulli-weight-expectation-multilinear-expansion}, the function $q_i$ is a finite sum of scalar multiples of squarefree coordinate monomials. Each such monomial is integrable under the product law by \cref{lem:bernoulli-weight-expectation-monomial-integrable}. Integrability is preserved by scalar multiplication and finite sums, so $q_i$ is integrable. -/)
  (title := /-- Integrability of a Bernoulli Weight -/)
  (latexEnv := "lemma")]
lemma bernoulli_weight_integrable {n : ℕ}
    (D : Fin n → ProbabilityMeasure ℝ)
    (hD : coordinate_laws_supported D) (i : Fin n) :
    Integrable (fun y : Fin n → ℝ => bernoulli_weight y i)
      (ProbabilityMeasure.pi D : Measure (Fin n → ℝ)) := by
  classical
  simp_rw [bernoulli_weight_expectation_multilinear_expansion]
  apply Integrable.add
  · apply integrable_finsetSum
    intro S hS
    exact (bernoulli_weight_expectation_monomial_integrable D hD (insert i S)).const_mul _
  · apply Integrable.const_mul
    apply integrable_finsetSum
    intro S hS
    exact (bernoulli_weight_expectation_monomial_integrable D hD S).const_mul _

@[blueprint "lem:strategy-value-at-means"
  (statement := /-- Let $n\in\mathbb{N}$, and let $(D_i)_{i\in\operatorname{Fin}(n)}$ be probability measures on $\mathbb{R}$ such that $D_i$-almost every point belongs to $[0,1]$ for every $i\in\operatorname{Fin}(n)$. Set $x_i=\int_{\mathbb{R}}y\,dD_i(y)$, and let $q_i$ be the $i$th Bernoulli-derived weight. Then, under the independent product law of the $D_i$, the strategy value satisfies
  \[
    \operatorname{val}(S_{\mathrm{Ber}};D)
      =\sum_{i=1}^n x_iq_i(x),
  \]
  where $x$ is the vector of coordinate means. -/)
  (proof := /-- Expand \cref{def:strategy-value}. By \cref{lem:bernoulli-weight-integrable}, every summand is integrable under the product law, so linearity of the integral over the finite sum gives
  \[
    \operatorname{val}(S_{\mathrm{Ber}};D)
      =\sum_i x_i\,\mathbb{E}[q_i(y)].
  \]
  Apply \cref{lem:bernoulli-weight-expectation} to every index to replace $\mathbb{E}[q_i(y)]$ by $q_i(x)$. -/)
  (title := /-- Reduction of Strategy Value to the Mean Vector -/)
  (latexEnv := "lemma")]
lemma strategy_value_at_means {n : ℕ}
    (D : Fin n → ProbabilityMeasure ℝ)
    (hD : coordinate_laws_supported D) :
    strategy_value D bernoulli_weight =
      ∑ i, distribution_means D i *
        bernoulli_weight (distribution_means D) i := by
  classical
  unfold strategy_value
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_const_mul_of_integrable (bernoulli_weight_integrable D hD i),
      bernoulli_weight_expectation D hD i]
  · intro i hi
    exact (bernoulli_weight_integrable D hD i).const_mul _

@[blueprint "lem:finite-dot-product-decomposition"
  (statement := /-- Let $n$ be a positive integer and let $a,b\in\mathbb{R}^n$. Then
  \[
    \sum_i a_i b_i
      =\frac1n\Bigl(\sum_i a_i\Bigr)\Bigl(\sum_i b_i\Bigr)
       +\frac1n\sum_{i<j}(a_i-a_j)(b_i-b_j).
  \] -/)
  (proof := /-- Put $f(i,j)=(a_i-a_j)(b_i-b_j)$. This function is symmetric and vanishes on the diagonal. Consequently, splitting the off-diagonal ordered pairs into the two possible orientations shows, using \cref{def:strict-pair-sum}, that twice the strict-pair sum is the sum of $f(i,j)$ over all ordered pairs. Expanding this double sum and distributing the finite sums gives
  \[
    \sum_{i,j}f(i,j)=2n\sum_i a_i b_i
      -2\Bigl(\sum_i a_i\Bigr)\Bigl(\sum_i b_i\Bigr).
  \]
  Cancelling the factor $2$ therefore identifies the strict-pair sum with $n\sum_i a_i b_i-(\sum_i a_i)(\sum_i b_i)$. Since $n$ is positive, division by $n$ and rearrangement give the stated identity. -/)
  (title := /-- Finite Dot-Product Decomposition -/)
  (latexEnv := "lemma")]
lemma finite_dot_product_decomposition {n : ℕ} (hn : 0 < n)
    (a b : Fin n → ℝ) :
    ∑ i, a i * b i =
      (∑ i, a i) * (∑ i, b i) / (n : ℝ) +
        strict_pair_sum (fun i j ↦ (a i - a j) * (b i - b j)) / (n : ℝ) := by
  classical
  have hba : ∑ i, ∑ j, a j * b i = (∑ i, a i) * (∑ j, b j) := by
    simpa [mul_comm] using (Finset.sum_mul_sum Finset.univ Finset.univ b a).symm
  have hconst : ∑ x, a x * (∑ i, b i) = (∑ x, a x) * (∑ i, b i) := by
    rw [Finset.sum_mul]
  let f : Fin n → Fin n → ℝ := fun i j => (a i - a j) * (b i - b j)
  have hall : (∑ i, ∑ j, f i j) =
      2 * ((n : ℝ) * ∑ i, a i * b i - (∑ i, a i) * (∑ i, b i)) := by
    dsimp [f]
    simp_rw [sub_mul, mul_sub]
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_mul,
      Finset.mul_sum]
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [hconst, hba]
    ring
  have hf_symm (i j : Fin n) : f j i = f i j := by
    dsimp [f]
    ring
  have hoff (i : Fin n) :
      ∑ j ∈ ({i}ᶜ : Finset (Fin n)), f j i = ∑ j, f j i := by
    simpa [f] using
      Finset.sum_compl_add_sum ({i} : Finset (Fin n)) (fun j => f j i)
  have horder := Finset.sum_sum_Ioi_add_eq_sum_sum_off_diag f
  simp_rw [hoff] at horder
  simp_rw [hf_symm] at horder
  simp_rw [Finset.sum_add_distrib] at horder
  rw [hall] at horder
  have hpair : (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, f i j) =
      (n : ℝ) * ∑ i, a i * b i - (∑ i, a i) * (∑ i, b i) := by
    linear_combination horder / 2
  have hfilter (i : Fin n) :
      Finset.univ.filter (fun j : Fin n => i < j) = Finset.Ioi i := by
    ext j
    simp
  field_simp
  change _ = _ + strict_pair_sum f
  unfold strict_pair_sum
  simp_rw [hfilter]
  linarith [hpair]

@[blueprint "lem:bernoulli-weight-difference"
  (statement := /-- For every $n\in\mathbb{N}$, every $x\in\mathbb{R}^n$, and all distinct indices $i,j\in[n]$, the Bernoulli weights and kernel satisfy
  \[
    q_i(x)-q_j(x)=(x_i-x_j)K_{i,j}(x).
  \] -/)
  (proof := /-- Define
  \[
    P(t)=\prod_{k\ne i,j}(1-tx_k).
  \]
  Since $i\ne j$, separating the factor indexed by $j$ in the product omitting $i$, and the factor indexed by $i$ in the product omitting $j$, gives
  \[
    \prod_{k\ne i}(1-tx_k)=(1-tx_j)P(t),\qquad
    \prod_{k\ne j}(1-tx_k)=(1-tx_i)P(t).
  \]
  Expand $q_i(x)$ and $q_j(x)$ using \cref{def:bernoulli-weight}; their common all-zero contribution cancels. The functions in the remaining interval integrals are finite products of polynomial functions and hence are continuous and interval integrable. Linearity of the interval integral therefore reduces their difference to the integral of the pointwise difference. For every $t\in[0,1]$,
  \[
    x_i(1-tx_j)P(t)-x_j(1-tx_i)P(t)=(x_i-x_j)P(t).
  \]
  Pulling the constant $x_i-x_j$ out of the integral and applying \cref{def:bernoulli-kernel} proves the identity. -/)
  (title := /-- Difference of Bernoulli Weights -/)
  (latexEnv := "lemma")]
lemma bernoulli_weight_difference {n : ℕ}
    (x : Fin n → ℝ) {i j : Fin n} (hij : i ≠ j) :
    bernoulli_weight x i - bernoulli_weight x j =
      (x i - x j) * bernoulli_kernel x i j := by
  classical
  have hji : j ≠ i := Ne.symm hij
  let P : ℝ → ℝ := fun t ↦
    ∏ k ∈ Finset.univ.filter (fun k : Fin n ↦ k ≠ i ∧ k ≠ j), (1 - t * x k)
  have hi : Finset.univ.filter (fun k : Fin n ↦ k ≠ i) =
      insert j (Finset.univ.filter (fun k : Fin n ↦ k ≠ i ∧ k ≠ j)) := by
    ext k
    by_cases hkj : k = j <;> simp_all
  have hj : Finset.univ.filter (fun k : Fin n ↦ k ≠ j) =
      insert i (Finset.univ.filter (fun k : Fin n ↦ k ≠ i ∧ k ≠ j)) := by
    ext k
    by_cases hki : k = i <;> simp_all
  have hprod_i (t : ℝ) :
      (∏ k ∈ Finset.univ.filter (fun k : Fin n ↦ k ≠ i), (1 - t * x k)) =
        (1 - t * x j) * P t := by
    rw [hi]
    simp [P]
  have hprod_j (t : ℝ) :
      (∏ k ∈ Finset.univ.filter (fun k : Fin n ↦ k ≠ j), (1 - t * x k)) =
        (1 - t * x i) * P t := by
    rw [hj]
    simp [P]
  have hP : Continuous P := by
    dsimp [P]
    fun_prop
  unfold bernoulli_weight bernoulli_kernel
  simp_rw [hprod_i, hprod_j]
  rw [add_sub_add_right_eq_sub]
  change x i * (∫ t in (0 : ℝ)..1, (1 - t * x j) * P t) -
      x j * (∫ t in (0 : ℝ)..1, (1 - t * x i) * P t) =
    (x i - x j) * (∫ t in (0 : ℝ)..1, P t)
  have hfi : IntervalIntegrable
      (fun t : ℝ ↦ x i * ((1 - t * x j) * P t)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hfj : IntervalIntegrable
      (fun t : ℝ ↦ x j * ((1 - t * x i) * P t)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_sub hfi hfj]
  apply congrArg (fun f : ℝ → ℝ ↦ ∫ t in (0 : ℝ)..1, f t)
  funext t
  ring

@[blueprint "lem:weighted-value-kernel-identity"
  (statement := /-- Let $n$ be a positive integer and let $x\in\mathbb{R}^n$. Then the Bernoulli weights satisfy
  \[
    \sum_i x_iq_i(x)
      =\mu(x)+\frac1n\sum_{i<j}(x_i-x_j)^2K_{i,j}(x).
  \] -/)
  (proof := /-- Apply \cref{lem:finite-dot-product-decomposition} with $a_i=x_i$ and $b_i=q_i(x)$. By \cref{lem:bernoulli-weights-sum-one}, the product-of-sums term is $\mu(x)$ as defined in \cref{def:vector-mean}. For every pair $i<j$, the indices are distinct, so \cref{lem:bernoulli-weight-difference} changes
  \[
    (x_i-x_j)(q_i(x)-q_j(x))
  \]
  into $(x_i-x_j)^2K_{i,j}(x)$. Summation over the strict pairs defined in \cref{def:strict-pair-sum} gives the formula. -/)
  (title := /-- Kernel Identity for the Deterministic Value -/)
  (latexEnv := "lemma")]
lemma weighted_value_kernel_identity {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) :
    ∑ i, x i * bernoulli_weight x i =
      vector_mean x +
        strict_pair_sum (fun i j ↦
          (x i - x j) ^ 2 * bernoulli_kernel x i j) / (n : ℝ) := by
  rw [finite_dot_product_decomposition hn x (bernoulli_weight x),
    bernoulli_weights_sum_one hn x]
  simp only [mul_one, vector_mean]
  congr 2
  unfold strict_pair_sum
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j hj
  dsimp
  rw [bernoulli_weight_difference x
    (ne_of_lt (Finset.mem_filter.mp hj).2)]
  ring

@[blueprint "lem:pairwise-squares-variance"
  (statement := /-- For every $n\in\mathbb{N}$ and every $x\in\mathbb{R}^n$,
  \[
    \sum_{i<j}(x_i-x_j)^2=n^2\sigma^2(x).
  \] -/)
  (proof := /-- Set $f_{i,j}=(x_i-x_j)^2$. The diagonal terms $f_{i,i}$ vanish, and $f_{j,i}=f_{i,j}$. Partitioning the ordered double sum into the cases $i<j$, $i=j$, and $j<i$, and using \cref{def:strict-pair-sum}, therefore gives
  \[
    \sum_{i,j}f_{i,j}=2\sum_{i<j}f_{i,j}.
  \]
  Distributivity of finite sums and the identity
  $(\sum_i x_i)(\sum_j x_j)=\sum_{i,j}x_ix_j$ give
  \[
    \sum_{i,j}(x_i-x_j)^2
      =2n\sum_i x_i^2-2\Bigl(\sum_i x_i\Bigr)^2.
  \]
  Comparing the two equalities and cancelling $2$ yields
  \[
    \sum_{i<j}(x_i-x_j)^2
      =n\sum_i x_i^2-\Bigl(\sum_i x_i\Bigr)^2.
  \]
  When $n=0$, both sides of the asserted identity vanish. When $n\ne0$, substituting \cref{def:vector-mean,def:vector-variance} and clearing the nonzero denominator $n$ identifies the final expression with $n^2\sigma^2(x)$. -/)
  (title := /-- Pairwise-Square Formula for Variance -/)
  (latexEnv := "lemma")]
lemma pairwise_squares_variance {n : ℕ} (x : Fin n → ℝ) :
    strict_pair_sum (fun i j ↦ (x i - x j) ^ 2) =
      (n : ℝ) ^ 2 * vector_variance x := by
  classical
  have hprod :
      (∑ i : Fin n, ∑ j : Fin n, x i * x j) = (∑ i, x i) ^ 2 := by
    rw [pow_two, Finset.sum_mul_sum]
  have hcross :
      (∑ i : Fin n, ∑ j : Fin n, 2 * x i * x j) =
        2 * (∑ i, x i) ^ 2 := by
    calc
      _ = 2 * (∑ i : Fin n, ∑ j : Fin n, x i * x j) := by
        simp_rw [← Finset.mul_sum]
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum]
      _ = 2 * (∑ i, x i) ^ 2 := by rw [hprod]
  have hsquare :
      (∑ i : Fin n, (n : ℝ) * (x i) ^ 2) +
          (∑ i : Fin n, (n : ℝ) * (x i) ^ 2) =
        ∑ i : Fin n, 2 * (n : ℝ) * (x i) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hdouble :
      (∑ i : Fin n, ∑ j : Fin n, (x i - x j) ^ 2) =
        2 * (n : ℝ) * (∑ i, (x i) ^ 2) - 2 * (∑ i, x i) ^ 2 := by
    simp [sub_sq, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.mul_sum, Finset.sum_mul, hcross]
    rw [← hsquare]
    ring
  have hup :
      (∑ i : Fin n, ∑ j : Fin n,
        if i < j then (x i - x j) ^ 2 else 0) =
        strict_pair_sum (fun i j ↦ (x i - x j) ^ 2) := by
    unfold strict_pair_sum
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_filter]
  have hdown :
      (∑ i : Fin n, ∑ j : Fin n,
        if j < i then (x i - x j) ^ 2 else 0) =
      (∑ i : Fin n, ∑ j : Fin n,
        if i < j then (x i - x j) ^ 2 else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> ring
  have hsplit :
      (∑ i : Fin n, ∑ j : Fin n, (x i - x j) ^ 2) =
        (∑ i : Fin n, ∑ j : Fin n,
          if i < j then (x i - x j) ^ 2 else 0) +
        (∑ i : Fin n, ∑ j : Fin n,
          if j < i then (x i - x j) ^ 2 else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt_of_ge h.le]
    · simp
    · simp [h, not_lt_of_ge h.le]
  have hpair :
      (∑ i : Fin n, ∑ j : Fin n, (x i - x j) ^ 2) =
        2 * strict_pair_sum (fun i j ↦ (x i - x j) ^ 2) := by
    rw [hsplit, hdown, hup]
    ring
  have hcore :
      strict_pair_sum (fun i j ↦ (x i - x j) ^ 2) =
        (n : ℝ) * (∑ i, (x i) ^ 2) - (∑ i, x i) ^ 2 := by
    linarith [hpair, hdouble]
  by_cases hn : n = 0
  · subst n
    simp [strict_pair_sum, vector_variance, vector_mean]
  · rw [hcore]
    unfold vector_variance vector_mean
    have hn_real : (n : ℝ) ≠ 0 := by
      exact_mod_cast hn
    field_simp

@[blueprint "lem:bernoulli-kernel-easy-lower-bound"
  (statement := /-- Let $n\geq2$, let $x\in[0,1]^n$, and let $i,j\in[n]$ be distinct. Then
  \[
    K_{i,j}(x)\geq\frac1{n-1}.
  \] -/)
  (proof := /-- The set of indices distinct from $i$ and $j$ has cardinality $n-2$. Fix $t\in[0,1]$. For each such index $k$, the inequalities $0\leq x_k\leq1$ give $0\leq1-t\leq1-tx_k$. Multiplying these inequalities yields
  \[
    \prod_{k\ne i,j}(1-tx_k)\geq(1-t)^{n-2}.
  \]
  Both sides are continuous in $t$, so monotonicity of the interval integral and \cref{def:bernoulli-kernel} give
  \[
    K_{i,j}(x)\geq\int_0^1(1-t)^{n-2}\,dt.
  \]
  The substitution $u=1-t$ and the power-integral formula show that
  \[
    \int_0^1(1-t)^{n-2}\,dt=\frac1{n-1},
  \]
  which proves the bound. -/)
  (title := /-- Uniform Lower Bound for the Bernoulli Kernel -/)
  (latexEnv := "lemma")]
lemma bernoulli_kernel_easy_lower_bound {n : ℕ} (hn : 2 ≤ n)
    (x : Fin n → ℝ) (hx : ∀ k, x k ∈ Icc (0 : ℝ) 1)
    {i j : Fin n} (hij : i ≠ j) :
    1 / ((n : ℝ) - 1) ≤ bernoulli_kernel x i j := by
  classical
  have hcard :
      (Finset.univ.filter (fun k : Fin n ↦ k ≠ i ∧ k ≠ j)).card = n - 2 := by
    simp [Finset.filter_and, Finset.filter_ne', hij, Nat.sub_sub]
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
      (1 - t) ^ (n - 2) ≤
        ∏ k ∈ Finset.univ.filter (fun k : Fin n ↦ k ≠ i ∧ k ≠ j),
          (1 - t * x k) := by
    intro t ht
    rw [← hcard, ← Finset.prod_const]
    apply Finset.prod_le_prod
    · intro k hk
      exact sub_nonneg.mpr ht.2
    · intro k hk
      simpa using
        sub_le_sub_left (mul_le_mul_of_nonneg_left (hx k).2 ht.1) 1
  have hleft : IntervalIntegrable (fun t : ℝ ↦ (1 - t) ^ (n - 2)) volume 0 1 := by
    exact (by fun_prop : Continuous (fun t : ℝ ↦ (1 - t) ^ (n - 2))).intervalIntegrable 0 1
  have hright : IntervalIntegrable
      (fun t : ℝ ↦
        ∏ k ∈ Finset.univ.filter (fun k : Fin n ↦ k ≠ i ∧ k ≠ j),
          (1 - t * x k)) volume 0 1 := by
    exact (by fun_prop : Continuous
      (fun t : ℝ ↦
        ∏ k ∈ Finset.univ.filter (fun k : Fin n ↦ k ≠ i ∧ k ≠ j),
          (1 - t * x k))).intervalIntegrable 0 1
  have hmono :
      (∫ t in (0 : ℝ)..1, (1 - t) ^ (n - 2)) ≤
        ∫ t in (0 : ℝ)..1,
          ∏ k ∈ Finset.univ.filter (fun k : Fin n ↦ k ≠ i ∧ k ≠ j),
            (1 - t * x k) :=
    intervalIntegral.integral_mono_on (by norm_num) hleft hright hpoint
  have hsub := intervalIntegral.integral_comp_sub_left
    (f := fun u : ℝ ↦ u ^ (n - 2)) (a := (0 : ℝ)) (b := 1) 1
  norm_num at hsub
  have hden : ((n - 2 : ℕ) : ℝ) + 1 = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    ring
  have heval :
      (∫ t in (0 : ℝ)..1, (1 - t) ^ (n - 2)) = 1 / ((n : ℝ) - 1) := by
    simpa [one_div, hden] using hsub
  unfold bernoulli_kernel
  rw [← heval]
  exact hmono

@[blueprint "lem:bernoulli-kernel-global-lower-bound"
  (statement := /-- For every natural number $n$ and every
  $x=(x_1,\ldots,x_n)\in[0,1]^n$, the Bernoulli kernels satisfy the weighted
  aggregate bound
  \[
    \frac{1-\prod_{k=1}^n(1-x_k)}{\sum_{k=1}^n x_k}
      \sum_{i<j}(x_i-x_j)^2
    \leq
      \sum_{i<j}(x_i-x_j)^2K_{i,j}(x).
  \] -/)
  (proof := /-- If $n=0$, both strict-pair sums in
  \cref{def:strict-pair-sum} vanish. Assume henceforth that $n>0$, and set
  \[
    A_i=\int_0^1\prod_{k\ne i}(1-tx_k)\,dt,\quad
    S=\sum_i x_i,\quad Q=\sum_i x_i^2,\quad
    P=\prod_i(1-x_i),
  \]
  \[
    U=\sum_i x_i^2A_i,\qquad V=\sum_i x_iA_i,qquad
    K=\sum_{i<j}(x_i-x_j)^2K_{i,j}(x).
  \]
  If $S=0$, the coordinate inequalities $x_i\geq0$ imply $x_i=0$ for every
  $i$, and the desired inequality follows.

  Suppose that $S>0$. For distinct $i,j$ with $x_i\leq x_j$, factor the
  products defining $A_i$ and $A_j$ as
  \[
    (1-tx_j)\prod_{k\ne i,j}(1-tx_k),\qquad
    (1-tx_i)\prod_{k\ne i,j}(1-tx_k).
  \]
  Every factor in the common product is nonnegative for $0\leq t\leq1$.
  Hence the first integrand is at most the second, so $A_i\leq A_j$.
  Consequently
  \[
    (x_i-x_j)(A_i-A_j)\geq0
  \]
  for all $i,j$. Multiplication by $x_ix_j\geq0$ and summation give
  \[
    0\leq\sum_{i,j}x_ix_j(x_i-x_j)(A_i-A_j)
      =2(SU-QV).
  \]

  Expanding the Bernoulli weights from \cref{def:bernoulli-weight} in
  \cref{lem:bernoulli-weights-sum-one} yields $V=1-P$. Expanding the same
  weights and \cref{def:vector-mean} in
  \cref{lem:weighted-value-kernel-identity} yields
  \[
    K=nU-S(1-P).
  \]
  The covariance inequality and $S>0$ therefore imply
  \[
    U\geq\frac{Q(1-P)}{S}.
  \]
  Finally, unfolding \cref{def:vector-mean,def:vector-variance} in
  \cref{lem:pairwise-squares-variance} gives
  \[
    \sum_{i<j}(x_i-x_j)^2=nQ-S^2.
  \]
  Substitution into the formula for $K$ proves
  \[
    K\geq\frac{1-P}{S}\sum_{i<j}(x_i-x_j)^2,
  \]
  as required. -/)
  (title := /-- Weighted Aggregate Lower Bound for the Bernoulli Kernel -/)
  (latexEnv := "lemma")]
lemma bernoulli_kernel_global_lower_bound {n : ℕ}
    (x : Fin n → ℝ) (hx : ∀ k, x k ∈ Icc (0 : ℝ) 1) :
    (1 - ∏ k, (1 - x k)) / (∑ k, x k) *
        strict_pair_sum (fun i j ↦ (x i - x j) ^ 2) ≤
      strict_pair_sum (fun i j ↦
        (x i - x j) ^ 2 * bernoulli_kernel x i j) := by
  classical
  by_cases hn0 : n = 0
  · subst n
    simp [strict_pair_sum]
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast hn0
  let A : Fin n → ℝ := fun i ↦
    ∫ t in (0 : ℝ)..1,
      ∏ k ∈ Finset.univ.filter (fun k : Fin n ↦ k ≠ i), (1 - t * x k)
  let S : ℝ := ∑ i, x i
  let Q : ℝ := ∑ i, (x i) ^ 2
  let P : ℝ := ∏ i, (1 - x i)
  let U : ℝ := ∑ i, (x i) ^ 2 * A i
  let V : ℝ := ∑ i, x i * A i
  let K : ℝ := strict_pair_sum (fun i j ↦
    (x i - x j) ^ 2 * bernoulli_kernel x i j)
  have hx0 (i : Fin n) : 0 ≤ x i := (hx i).1
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i _ ↦ hx0 i
  by_cases hS : S = 0
  · have hxzero : x = 0 := by
      funext i
      have hle : x i ≤ S := by
        dsimp [S]
        exact Finset.single_le_sum (fun j _ ↦ hx0 j) (Finset.mem_univ i)
      simp only [Pi.zero_apply]
      linarith [hx0 i]
    subst x
    simp [strict_pair_sum]
  have hSpos : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hS)
  have hAmono {i j : Fin n} (hij : i ≠ j) (hijx : x i ≤ x j) : A i ≤ A j := by
    have hji : j ≠ i := Ne.symm hij
    let R : ℝ → ℝ := fun t ↦
      ∏ k ∈ Finset.univ.filter (fun k : Fin n ↦ k ≠ i ∧ k ≠ j),
        (1 - t * x k)
    have hi : Finset.univ.filter (fun k : Fin n ↦ k ≠ i) =
        insert j (Finset.univ.filter (fun k : Fin n ↦ k ≠ i ∧ k ≠ j)) := by
      ext k
      by_cases hkj : k = j <;> simp_all
    have hj : Finset.univ.filter (fun k : Fin n ↦ k ≠ j) =
        insert i (Finset.univ.filter (fun k : Fin n ↦ k ≠ i ∧ k ≠ j)) := by
      ext k
      by_cases hki : k = i <;> simp_all
    have hprod_i (t : ℝ) :
        (∏ k ∈ Finset.univ.filter (fun k : Fin n ↦ k ≠ i), (1 - t * x k)) =
          (1 - t * x j) * R t := by
      rw [hi]
      simp [R]
    have hprod_j (t : ℝ) :
        (∏ k ∈ Finset.univ.filter (fun k : Fin n ↦ k ≠ j), (1 - t * x k)) =
          (1 - t * x i) * R t := by
      rw [hj]
      simp [R]
    have hIi : IntervalIntegrable
        (fun t : ℝ ↦
          ∏ k ∈ Finset.univ.filter (fun k : Fin n ↦ k ≠ i), (1 - t * x k))
        volume 0 1 := by
      exact (by fun_prop : Continuous
        (fun t : ℝ ↦
          ∏ k ∈ Finset.univ.filter (fun k : Fin n ↦ k ≠ i),
            (1 - t * x k))).intervalIntegrable 0 1
    have hIj : IntervalIntegrable
        (fun t : ℝ ↦
          ∏ k ∈ Finset.univ.filter (fun k : Fin n ↦ k ≠ j), (1 - t * x k))
        volume 0 1 := by
      exact (by fun_prop : Continuous
        (fun t : ℝ ↦
          ∏ k ∈ Finset.univ.filter (fun k : Fin n ↦ k ≠ j),
            (1 - t * x k))).intervalIntegrable 0 1
    dsimp [A]
    apply intervalIntegral.integral_mono_on (by norm_num) hIi hIj
    intro t ht
    rw [hprod_i, hprod_j]
    have hR : 0 ≤ R t := by
      dsimp [R]
      apply Finset.prod_nonneg
      intro k hk
      have htk : t * x k ≤ t := by
        simpa using mul_le_mul_of_nonneg_left (hx k).2 ht.1
      linarith [ht.2]
    have hfactor : 1 - t * x j ≤ 1 - t * x i := by
      exact sub_le_sub_left (mul_le_mul_of_nonneg_left hijx ht.1) 1
    exact mul_le_mul_of_nonneg_right hfactor hR
  have hAalign (i j : Fin n) :
      0 ≤ (x i - x j) * (A i - A j) := by
    by_cases hij : i = j
    · subst j
      simp
    rcases le_total (x i) (x j) with hle | hge
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hle)
        (sub_nonpos.mpr (hAmono hij hle))
    · exact mul_nonneg (sub_nonneg.mpr hge)
        (sub_nonneg.mpr (hAmono (Ne.symm hij) hge))
  have hdouble_nonneg :
      0 ≤ ∑ i : Fin n, ∑ j : Fin n,
        x i * x j * ((x i - x j) * (A i - A j)) := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (mul_nonneg (hx0 i) (hx0 j)) (hAalign i j)
  have hdouble :
      (∑ i : Fin n, ∑ j : Fin n,
        x i * x j * ((x i - x j) * (A i - A j))) =
        2 * (S * U - Q * V) := by
    have h₁ :
        (∑ i : Fin n, ∑ j : Fin n, (x i) ^ 2 * x j * A i) = U * S := by
      dsimp [U, S]
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have h₂ :
        (∑ i : Fin n, ∑ j : Fin n, x i * (x j) ^ 2 * A i) = V * Q := by
      dsimp [V, Q]
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have h₃ :
        (∑ i : Fin n, ∑ j : Fin n, (x i) ^ 2 * x j * A j) = Q * V := by
      dsimp [Q, V]
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have h₄ :
        (∑ i : Fin n, ∑ j : Fin n, x i * (x j) ^ 2 * A j) = S * U := by
      dsimp [S, U]
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have h₁' :
        (∑ i : Fin n, ∑ j : Fin n, x i * x j * (x i * A i)) = U * S := by
      calc
        _ = ∑ i : Fin n, ∑ j : Fin n, (x i) ^ 2 * x j * A i := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = U * S := h₁
    have h₂' :
        (∑ i : Fin n, ∑ j : Fin n, x i * x j * (x j * A i)) = V * Q := by
      calc
        _ = ∑ i : Fin n, ∑ j : Fin n, x i * (x j) ^ 2 * A i := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = V * Q := h₂
    have h₃' :
        (∑ i : Fin n, ∑ j : Fin n, x i * x j * (x i * A j)) = Q * V := by
      calc
        _ = ∑ i : Fin n, ∑ j : Fin n, (x i) ^ 2 * x j * A j := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = Q * V := h₃
    have h₄' :
        (∑ i : Fin n, ∑ j : Fin n, x i * x j * (x j * A j)) = S * U := by
      calc
        _ = ∑ i : Fin n, ∑ j : Fin n, x i * (x j) ^ 2 * A j := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = S * U := h₄
    simp only [mul_sub, sub_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    rw [h₁', h₂', h₃', h₄']
    ring
  have hcov : 0 ≤ S * U - Q * V := by
    linarith [hdouble_nonneg, hdouble]
  have hV : V = 1 - P := by
    have hw := bernoulli_weights_sum_one hn x
    unfold bernoulli_weight at hw
    dsimp [V, A, P]
    rw [Finset.sum_add_distrib] at hw
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hw
    field_simp [hnR] at hw
    linarith
  have hK : K = (n : ℝ) * U - S * (1 - P) := by
    have hw := weighted_value_kernel_identity hn x
    unfold bernoulli_weight vector_mean at hw
    dsimp [K, U, S, P, A]
    simp_rw [mul_add] at hw
    rw [Finset.sum_add_distrib] at hw
    rw [← Finset.sum_mul] at hw
    field_simp [hnR] at hw
    ring_nf at hw ⊢
    linarith [hw]
  have hU : Q * (1 - P) / S ≤ U := by
    rw [← hV]
    apply (div_le_iff₀ hSpos).2
    nlinarith [hcov]
  have hpair :
      strict_pair_sum (fun i j ↦ (x i - x j) ^ 2) =
        (n : ℝ) * Q - S ^ 2 := by
    rw [pairwise_squares_variance]
    dsimp [Q, S]
    unfold vector_variance vector_mean
    field_simp [hnR]
  change (1 - P) / S * strict_pair_sum (fun i j ↦ (x i - x j) ^ 2) ≤ K
  rw [hK, hpair]
  have heq :
      (1 - P) / S * ((n : ℝ) * Q - S ^ 2) =
        (n : ℝ) * (Q * (1 - P) / S) - S * (1 - P) := by
    field_simp [hS]
  rw [heq]
  exact sub_le_sub_right
    (mul_le_mul_of_nonneg_left hU (Nat.cast_nonneg n)) (S * (1 - P))

@[blueprint "lem:first-deterministic-lower-bound"
  (statement := /-- For every natural number $n\geq2$ and every $x\in[0,1]^n$,
  \[
    \sum_i x_iq_i(x)\geq
      \mu(x)+\frac{n}{n-1}\sigma^2(x).
  \] -/)
  (proof := /-- Since $n\geq2$, both $n$ and $n-1$ are positive. For every strict pair $i<j$, \cref{lem:bernoulli-kernel-easy-lower-bound} and the nonnegativity of $(x_i-x_j)^2$ give
  \[
    \frac{(x_i-x_j)^2}{n-1}
      \leq (x_i-x_j)^2K_{i,j}(x).
  \]
  Summing these inequalities and applying \cref{lem:pairwise-squares-variance} yields
  \[
    \frac{n^2}{n-1}\sigma^2(x)
      \leq\sum_{i<j}(x_i-x_j)^2K_{i,j}(x).
  \]
  Multiplication by the positive scalar $1/n$ gives
  \[
    \frac{n}{n-1}\sigma^2(x)
      \leq\frac1n\sum_{i<j}(x_i-x_j)^2K_{i,j}(x).
  \]
  Adding $\mu(x)$ and using \cref{lem:weighted-value-kernel-identity} identifies the right-hand side with $\sum_i x_iq_i(x)$ and proves the claim. -/)
  (title := /-- First Deterministic Value Lower Bound -/)
  (latexEnv := "lemma")]
lemma first_deterministic_lower_bound {n : ℕ} (hn : 2 ≤ n)
    (x : Fin n → ℝ) (hx : ∀ k, x k ∈ Icc (0 : ℝ) 1) :
    vector_mean x + (n : ℝ) / ((n : ℝ) - 1) * vector_variance x ≤
      ∑ i, x i * bernoulli_weight x i := by
  classical
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hnone : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 1 < n by omega)
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hden0 : (n : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hnone)
  have hpair :
      1 / ((n : ℝ) - 1) *
          strict_pair_sum (fun i j ↦ (x i - x j) ^ 2) ≤
        strict_pair_sum (fun i j ↦
          (x i - x j) ^ 2 * bernoulli_kernel x i j) := by
    unfold strict_pair_sum
    simp_rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    have hk := bernoulli_kernel_easy_lower_bound hn x hx
      (ne_of_lt (Finset.mem_filter.mp hj).2)
    nlinarith [sq_nonneg (x i - x j)]
  rw [pairwise_squares_variance] at hpair
  rw [weighted_value_kernel_identity (by omega) x]
  have hmain :
      (n : ℝ) / ((n : ℝ) - 1) * vector_variance x ≤
        strict_pair_sum (fun i j ↦
          (x i - x j) ^ 2 * bernoulli_kernel x i j) / (n : ℝ) := by
    calc
      (n : ℝ) / ((n : ℝ) - 1) * vector_variance x =
          (1 / (n : ℝ)) *
            (1 / ((n : ℝ) - 1) *
              ((n : ℝ) ^ 2 * vector_variance x)) := by
                field_simp [hn0, hden0]
                <;> ring
      _ ≤ (1 / (n : ℝ)) *
          strict_pair_sum (fun i j ↦
            (x i - x j) ^ 2 * bernoulli_kernel x i j) :=
        mul_le_mul_of_nonneg_left hpair (by positivity)
      _ = strict_pair_sum (fun i j ↦
            (x i - x j) ^ 2 * bernoulli_kernel x i j) / (n : ℝ) := by
        simp [div_eq_mul_inv, mul_comm]
  linarith

@[blueprint "lem:second-deterministic-lower-bound"
  (statement := /-- Let $n\in\mathbb{N}$ satisfy $n\geq2$, and let
  $x\in[0,1]^n$. Then
  \[
    \sum_i x_iq_i(x)\geq
      \mu(x)+\left(1-\prod_{k=1}^n(1-x_k)\right)
        \frac{\sigma^2(x)}{\mu(x)}.
  \] -/)
  (proof := /-- Put $\mu=\mu(x)$. Since $n\geq2$, the real number $n$ is
  positive and nonzero. By \cref{def:vector-mean},
  $\sum_kx_k=n\mu$. Suppose first that $\mu=0$. Then $\sum_kx_k=0$.
  Every coordinate is nonnegative, and each $x_i$ is bounded above by this
  sum, so $x_i=0$ for every $i$. Substitution into
  \cref{def:vector-mean,def:vector-variance} makes both sides of the desired
  inequality equal to zero.

  Now suppose that $\mu\neq0$. Divide the inequality in
  \cref{lem:bernoulli-kernel-global-lower-bound} by the positive real number
  $n$. By \cref{lem:pairwise-squares-variance}, the resulting left-hand side
  is
  \[
    \frac1n\frac{1-\prod_k(1-x_k)}{\sum_kx_k}
      \sum_{i<j}(x_i-x_j)^2
    =\left(1-\prod_k(1-x_k)\right)\frac{\sigma^2(x)}{\mu},
  \]
  where the equality uses $\sum_kx_k=n\mu$ and cancels the nonzero factor
  $n^2$. Add $\mu$ to this inequality and use
  \cref{lem:weighted-value-kernel-identity} to identify its right-hand side
  with $\sum_i x_iq_i(x)$. This proves the asserted lower bound. -/)
  (title := /-- Second Deterministic Value Lower Bound -/)
  (latexEnv := "lemma")]
lemma second_deterministic_lower_bound {n : ℕ} (hn : 2 ≤ n)
    (x : Fin n → ℝ) (hx : ∀ k, x k ∈ Icc (0 : ℝ) 1) :
    vector_mean x + (1 - ∏ k, (1 - x k)) *
        (vector_variance x / vector_mean x) ≤
      ∑ i, x i * bernoulli_weight x i := by
  classical
  have hnpos : 0 < n := by omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hnRpos : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hsum_mean : (∑ k, x k) = (n : ℝ) * vector_mean x := by
    rw [vector_mean]
    field_simp
  by_cases hmean : vector_mean x = 0
  · have hsum : ∑ k, x k = 0 := by rw [hsum_mean, hmean, mul_zero]
    have hxzero : x = 0 := by
      funext i
      have hxi_le : x i ≤ ∑ k, x k :=
        Finset.single_le_sum (fun j _ ↦ (hx j).1) (Finset.mem_univ i)
      exact le_antisymm (by simpa [hsum] using hxi_le) (hx i).1
    rw [hxzero]
    simp [vector_mean, vector_variance]
  · have hglobal := bernoulli_kernel_global_lower_bound x hx
    have hdiv := (div_le_div_iff_of_pos_right hnRpos).2 hglobal
    calc
      vector_mean x + (1 - ∏ k, (1 - x k)) *
          (vector_variance x / vector_mean x) =
        vector_mean x +
          ((1 - ∏ k, (1 - x k)) / (∑ k, x k) *
            strict_pair_sum (fun i j ↦ (x i - x j) ^ 2)) / (n : ℝ) := by
              congr 1
              rw [hsum_mean, pairwise_squares_variance]
              field_simp [hmean, hnR]
              <;> ring
      _ ≤ vector_mean x +
          strict_pair_sum (fun i j ↦
            (x i - x j) ^ 2 * bernoulli_kernel x i j) / (n : ℝ) :=
        by linarith
      _ = ∑ i, x i * bernoulli_weight x i :=
        (weighted_value_kernel_identity hnpos x).symm

@[blueprint "thm:adaptive-weighted-averaging-lower-bounds"
  (statement := /-- Let $n\geq2$. Let $D_1,\ldots,D_n$ be probability measures supported on $[0,1]$, let $D=\mathop{\times}_{i=1}^nD_i$, and put $x_i=\mathbb{E}_{D_i}[y_i]$. For the Bernoulli-derived multilinear strategy $S_{\mathrm{Ber}}$, both inequalities
  \[
    \operatorname{val}(S_{\mathrm{Ber}};D)
      \geq\mu(x)+\frac{n}{n-1}\sigma^2(x)
  \]
  and
  \[
    \operatorname{val}(S_{\mathrm{Ber}};D)
      \geq\mu(x)+\left(1-\prod_{k=1}^n(1-x_k)\right)
        \frac{\sigma^2(x)}{\mu(x)}
  \]
  hold. -/)
  (proof := /-- Let $x$ be the vector from \cref{def:distribution-means}. By \cref{lem:distribution-means-unit-interval}, every $x_i$ belongs to $[0,1]$. The value reduction \cref{lem:strategy-value-at-means} identifies $\operatorname{val}(S_{\mathrm{Ber}};D)$ with $\sum_i x_iq_i(x)$. Apply \cref{lem:first-deterministic-lower-bound} to obtain the first inequality and \cref{lem:second-deterministic-lower-bound} to obtain the second. Pairing these two conclusions proves the theorem. -/)
  (title := /-- Value Lower Bounds for Adaptive Weighted Averaging -/)
  (latexEnv := "theorem")]
theorem adaptive_weighted_averaging_lower_bounds {n : ℕ} (hn : 2 ≤ n)
    (D : Fin n → ProbabilityMeasure ℝ)
    (hD : coordinate_laws_supported D) :
    (vector_mean (distribution_means D) +
        (n : ℝ) / ((n : ℝ) - 1) * vector_variance (distribution_means D) ≤
      strategy_value D bernoulli_weight) ∧
    (vector_mean (distribution_means D) +
        (1 - ∏ k, (1 - distribution_means D k)) *
          (vector_variance (distribution_means D) /
            vector_mean (distribution_means D)) ≤
      strategy_value D bernoulli_weight) := by
  have hx := distribution_means_unit_interval D hD
  have hval := strategy_value_at_means D hD
  refine ⟨?_, ?_⟩
  · rw [hval]
    exact first_deterministic_lower_bound hn (distribution_means D) hx
  · rw [hval]
    exact second_deterministic_lower_bound hn (distribution_means D) hx

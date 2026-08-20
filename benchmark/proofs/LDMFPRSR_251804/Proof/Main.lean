import Architect
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory ProbabilityTheory
open Asymptotics

@[blueprint "def:standard-gaussian-measure"
  (statement := /-- The standard Gaussian measure $\gamma$ on $\mathbb R$ is the normal law with mean $0$ and variance $1$. -/)
  (title := /-- Standard Gaussian measure -/)
  (latexEnv := "definition")]
noncomputable def standard_gaussian_measure : Measure ℝ :=
  gaussianReal 0 1

@[blueprint "def:isotropic-gaussian-measure"
  (statement := /-- For $n\in\mathbb N$, the standard isotropic Gaussian measure $G_n$ on $\mathbb R^n$ is the product of $n$ copies of the standard Gaussian measure $\gamma$ from \cref{def:standard-gaussian-measure}. -/)
  (title := /-- Standard isotropic Gaussian measure -/)
  (latexEnv := "definition")]
noncomputable def isotropic_gaussian_measure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n ↦ standard_gaussian_measure)

@[blueprint "def:gaussian-scale-mixture"
  (statement := /-- For $n\in\mathbb N$, let $Q_n$ be the law of $\lambda Z\in\mathbb R^n$, where $\lambda\sim\mathcal N(0,1)$, $Z\sim\mathcal N(0,I_n)$, and $\lambda$ and $Z$ are independent. Equivalently, $Q_n$ is the pushforward of the product of the measures in \cref{def:standard-gaussian-measure,def:isotropic-gaussian-measure} under $(\lambda,z)\mapsto (\lambda z_i)_{i=1}^n$. -/)
  (title := /-- Gaussian scale mixture -/)
  (latexEnv := "definition")]
noncomputable def gaussian_scale_mixture (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.map
    (fun z : ℝ × (Fin n → ℝ) ↦ fun i ↦ z.1 * z.2 i)
    (standard_gaussian_measure.prod (isotropic_gaussian_measure n))

@[blueprint "def:origin-contamination"
  (statement := /-- Let $Q$ be a measure on a measurable space with a distinguished origin, and let $\alpha\in\mathbb R_{\geq 0}$. Its origin contamination is the measure
  \[
    P_\alpha=(1-\alpha)Q+\alpha\delta_0,
  \]
  where subtraction in $\mathbb R_{\geq0}$ is truncated. In every subsequent use one assumes $\alpha\leq1$, so the displayed coefficients are the intended mixture weights. -/)
  (title := /-- Contamination by a point mass at the origin -/)
  (latexEnv := "definition")]
noncomputable def origin_contamination {Ω : Type*} [MeasurableSpace Ω] [Zero Ω]
    (α : NNReal) (Q : Measure Ω) : Measure Ω :=
  ((↑(1 - α) : ENNReal) • Q) + ((↑α : ENNReal) • Measure.dirac 0)

@[blueprint "def:iid-product-measure"
  (statement := /-- For a measure $\mu$ on $\Omega$ and $m\in\mathbb N$, the measure $\mu^{\otimes m}$ on $\Omega^m$ is the finite product having the same marginal $\mu$ at every coordinate. -/)
  (title := /-- Finite i.i.d. product measure -/)
  (latexEnv := "definition")]
noncomputable def iid_product_measure {Ω : Type*} [MeasurableSpace Ω]
    (m : ℕ) (μ : Measure Ω) : Measure (Fin m → Ω) :=
  Measure.pi (fun _ : Fin m ↦ μ)

@[blueprint "def:sample-polynomial-observable"
  (statement := /-- A polynomial $p\in\mathbb R[x_{i,j}:i\in[m],\ j\in[n]]$ determines an observable on $m$ samples from $\mathbb R^n$ by assigning the variable $x_{i,j}$ the $j$th coordinate of the $i$th sample. -/)
  (title := /-- Polynomial observable on a sample tuple -/)
  (latexEnv := "definition")]
noncomputable def sample_polynomial_observable {n m : ℕ}
    (p : MvPolynomial (Fin m × Fin n) ℝ) (x : Fin m → Fin n → ℝ) : ℝ :=
  p.eval (fun ij ↦ x ij.1 ij.2)

@[blueprint "def:sample-polynomial-expectation"
  (statement := /-- Given a measure $\mu$ on $\mathbb R^n$ and a polynomial observable $p$ as in \cref{def:sample-polynomial-observable}, define $\mathbb E_{\mu^{\otimes m}}[p]$ to be the integral of that observable against the i.i.d. product measure from \cref{def:iid-product-measure}. -/)
  (title := /-- Expectation of a sample polynomial -/)
  (latexEnv := "definition")]
noncomputable def sample_polynomial_expectation {n m : ℕ}
    (μ : Measure (Fin n → ℝ)) (p : MvPolynomial (Fin m × Fin n) ℝ) : ℝ :=
  ∫ x, sample_polynomial_observable p x ∂iid_product_measure m μ

@[blueprint "def:sample-polynomial-variance"
  (statement := /-- Given a measure $\mu$ on $\mathbb R^n$ and a polynomial observable $p$ as in \cref{def:sample-polynomial-observable}, define $\operatorname{Var}_{\mu^{\otimes m}}(p)$ to be its real-valued variance under the i.i.d. product measure from \cref{def:iid-product-measure}. -/)
  (title := /-- Variance of a sample polynomial -/)
  (latexEnv := "definition")]
noncomputable def sample_polynomial_variance {n m : ℕ}
    (μ : Measure (Fin n → ℝ)) (p : MvPolynomial (Fin m × Fin n) ℝ) : ℝ :=
  variance (sample_polynomial_observable p) (iid_product_measure m μ)

@[blueprint "def:low-degree-advantage"
  (statement := /-- Let $P$ and $Q$ be measures on $\mathbb R^n$. For $m,k\in\mathbb N$, their degree-at-most-$k$ low-degree advantage on $m$ samples is
  \[
  \operatorname{LDA}^{(m)}_{\leq k}(P,Q)
  =\sup_{\substack{p\in\mathbb R[x_{i,j}]\\ \deg p\leq k\\
  \operatorname{Var}_{Q^{\otimes m}}(p)>0}}
  \frac{\left|\mathbb E_{P^{\otimes m}}[p]-\mathbb E_{Q^{\otimes m}}[p]\right|}
  {\sqrt{\operatorname{Var}_{Q^{\otimes m}}(p)}}.
  \]
  Here total degree, rather than a separate degree bound in each sample, is used. The supremum formulation agrees with the maximum in the paper whenever the finite-dimensional quotient by zero-variance polynomials is nondegenerate. -/)
  (title := /-- Low-degree advantage -/)
  (latexEnv := "definition")]
noncomputable def low_degree_advantage (n m k : ℕ)
    (P Q : Measure (Fin n → ℝ)) : ℝ :=
  sSup {r : ℝ | ∃ p : MvPolynomial (Fin m × Fin n) ℝ,
    p.totalDegree ≤ k ∧
    0 < sample_polynomial_variance Q p ∧
    r = |sample_polynomial_expectation P p - sample_polynomial_expectation Q p| /
      Real.sqrt (sample_polynomial_variance Q p)}

@[blueprint "def:gaussian-mean-variance-constant"
  (statement := /-- A real number $C$ is a Gaussian polynomial mean--variance constant if, for every $d\in\mathbb N$ and every polynomial $q\in\mathbb R[t]$ of degree at most $d$ with $q(0)=0$,
  \[
    \left|\mathbb E_{g\sim\mathcal N(0,1)}q(g)\right|
    \leq C\sqrt{d\,\operatorname{Var}_{g\sim\mathcal N(0,1)}(q(g))}.
  \]
  This is the precise interface for the universal constant cited in the theorem statement. -/)
  (title := /-- Universal Gaussian polynomial mean--variance property -/)
  (latexEnv := "definition")]
def gaussian_mean_variance_constant (C : ℝ) : Prop :=
  ∀ (d : ℕ) (q : Polynomial ℝ),
    q.natDegree ≤ d → q.coeff 0 = 0 →
      |∫ x, q.eval x ∂standard_gaussian_measure| ≤
        C * Real.sqrt ((d : ℝ) * variance (fun x ↦ q.eval x) standard_gaussian_measure)

@[blueprint "lem:low-degree-advantage-nonnegative"
  (statement := /-- For all $n,m,k\in\mathbb N$ and all measures $P,Q$ on $\mathbb R^n$, the quantity $\operatorname{LDA}^{(m)}_{\leq k}(P,Q)$ from \cref{def:low-degree-advantage} is nonnegative. -/)
  (proof := /-- Every admissible normalized expectation gap in \cref{def:low-degree-advantage} is nonnegative because its numerator is an absolute value and its denominator is the square root of a strictly positive variance. The supremum of these values is therefore nonnegative; if there is no admissible polynomial, the real supremum of the empty set is $0$. -/)
  (title := /-- Nonnegativity of low-degree advantage -/)
  (latexEnv := "lemma")]
lemma low_degree_advantage_nonnegative (n m k : ℕ)
    (P Q : Measure (Fin n → ℝ)) :
    0 ≤ low_degree_advantage n m k P Q := by
  unfold low_degree_advantage
  apply Real.sSup_nonneg
  rintro r ⟨p, hpdeg, hpvar, rfl⟩
  exact div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)

@[blueprint "lem:single-sample-lda-squared-bound"
  (statement := /-- Let $n,k\in\mathbb N$, let $0\leq\alpha\leq1$, and let $C>0$ satisfy the universal Gaussian polynomial mean--variance property of \cref{def:gaussian-mean-variance-constant}. For $Q_n$ from \cref{def:gaussian-scale-mixture} and $P_{n,\alpha}=(1-\alpha)Q_n+\alpha\delta_0$ from \cref{def:origin-contamination},
  \[
    \left(\operatorname{LDA}^{(1)}_{\leq k}(P_{n,\alpha},Q_n)\right)^2
    \leq C^2\alpha^2k.
  \] -/)
  (proof := /-- Write $Q_n$ as the law of $TZ$, where $T$ has the standard
  Gaussian law and $Z$ has the independent isotropic Gaussian law, as in
  \cref{def:standard-gaussian-measure,def:isotropic-gaussian-measure,def:gaussian-scale-mixture}.
  For an admissible one-sample polynomial $p$ in
  \cref{def:low-degree-advantage}, define
  \[
    q_0(t)=\mathbb E_Z[p(tZ)]
    \qquad\text{and}\qquad
    q(t)=q_0(t)-p(0).
  \]
  Expanding $p$ into monomials and integrating the spatial coordinates shows
  that $q$ is a univariate polynomial of degree at most $k$ and that its
  constant coefficient vanishes. All Gaussian monomials are integrable, so
  the product-measure and iterated-integral identities used below apply.

  Let $F(t,z)=p(tz)$ and let $m=\mathbb E[F(T,Z)]$. Conditional Jensen,
  applied to $F-m$, gives
  \[
    \mathbb E_T[(q_0(T)-m)^2]
      \leq \mathbb E_{T,Z}[(F(T,Z)-m)^2].
  \]
  Subtracting constants does not change variance, and the measurable
  pushforward representation of $Q_n$ therefore yields
  \[
    \operatorname{Var}(q(T))
      \leq \operatorname{Var}_{Q_n}(p).
  \]
  The same product-integral calculation gives
  $\mathbb E[q(T)]=\mathbb E_{Q_n}[p]-p(0)$, with expectations and variances
  interpreted through
  \cref{def:iid-product-measure,def:sample-polynomial-observable,def:sample-polynomial-expectation,def:sample-polynomial-variance}.

  By \cref{def:origin-contamination},
  \[
    \mathbb E_{P_{n,\alpha}}[p]-\mathbb E_{Q_n}[p]
      =-\alpha\,\mathbb E[q(T)].
  \]
  Applying \cref{def:gaussian-mean-variance-constant} to $q$, using the
  preceding variance contraction and $C>0$, gives
  \[
    \left|\mathbb E_{P_{n,\alpha}}[p]-\mathbb E_{Q_n}[p]\right|
      \leq C\alpha\sqrt{k}\,
        \sqrt{\operatorname{Var}_{Q_n}(p)}.
  \]
  Division by the positive standard deviation bounds every admissible ratio
  by $C\alpha\sqrt{k}$, hence bounds the supremum by the same quantity. If
  the admissible set is empty, its real supremum is zero. Finally,
  \cref{lem:low-degree-advantage-nonnegative} and the nonnegativity of
  $C\alpha\sqrt{k}$ allow the inequality to be squared, which gives the
  stated bound. -/)
  (title := /-- Single-sample low-degree estimate -/)
  (latexEnv := "lemma")]
lemma single_sample_lda_squared_bound (C : ℝ) (hCpos : 0 < C)
    (hC : gaussian_mean_variance_constant C) (n k : ℕ) (α : NNReal)
    (hα : α ≤ 1) :
    (low_degree_advantage n 1 k
      (origin_contamination α (gaussian_scale_mixture n))
      (gaussian_scale_mixture n)) ^ 2 ≤
      C ^ 2 * (α : ℝ) ^ 2 * (k : ℝ) := by
  let L : ℝ := C * (α : ℝ) * Real.sqrt (k : ℝ)
  have hL0 : 0 ≤ L := by
    dsimp [L]
    positivity
  have hA0 := low_degree_advantage_nonnegative n 1 k
    (origin_contamination α (gaussian_scale_mixture n)) (gaussian_scale_mixture n)
  suffices hA : low_degree_advantage n 1 k
      (origin_contamination α (gaussian_scale_mixture n))
      (gaussian_scale_mixture n) ≤ L by
    have hs : (low_degree_advantage n 1 k
        (origin_contamination α (gaussian_scale_mixture n))
        (gaussian_scale_mixture n)) ^ 2 ≤ L ^ 2 :=
      (sq_le_sq₀ hA0 hL0).mpr hA
    dsimp [L] at hs
    simpa [mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)] using hs
  unfold low_degree_advantage
  by_cases he : {r : ℝ | ∃ p : MvPolynomial (Fin 1 × Fin n) ℝ,
      p.totalDegree ≤ k ∧
      0 < sample_polynomial_variance (gaussian_scale_mixture n) p ∧
      r = |sample_polynomial_expectation
        (origin_contamination α (gaussian_scale_mixture n)) p -
        sample_polynomial_expectation (gaussian_scale_mixture n) p| /
        Real.sqrt (sample_polynomial_variance (gaussian_scale_mixture n) p)}.Nonempty
  · apply csSup_le he
    intro r hr
    rcases hr with ⟨p, hpdeg, hpvar, rfl⟩
    have hpmeas : StronglyMeasurable (sample_polynomial_observable p) := by
      rw [stronglyMeasurable_iff_measurable]
      clear hpdeg hpvar
      unfold sample_polynomial_observable
      induction p using MvPolynomial.induction_on with
      | C a =>
          simp only [MvPolynomial.eval_C]
          fun_prop
      | add p q hp hq =>
          simp only [MvPolynomial.eval_add]
          fun_prop
      | mul_X p ij hp =>
          simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X]
          exact hp.mul ((measurable_pi_apply ij.2 :
            Measurable (fun y : Fin n → ℝ => y ij.2)).comp
            (measurable_pi_apply ij.1 :
              Measurable (fun x : Fin 1 → Fin n → ℝ => x ij.1)))
    letI : IsProbabilityMeasure standard_gaussian_measure := by
      unfold standard_gaussian_measure
      infer_instance
    letI : IsProbabilityMeasure (isotropic_gaussian_measure n) := by
      unfold isotropic_gaussian_measure
      infer_instance
    have hx (e : ℕ) : Integrable (fun x : ℝ => x ^ e)
        standard_gaussian_measure := by
      rw [← integrable_norm_iff (by fun_prop)]
      simpa [standard_gaussian_measure] using
        (memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := (1 : NNReal))
          (e : ENNReal) (by simp)).integrable_norm_pow'
    have hz (s : (Fin 1 × Fin n) →₀ ℕ) : Integrable
        (fun z : Fin n → ℝ => s.prod fun ij e => z ij.2 ^ e)
        (isotropic_gaussian_measure n) := by
      simpa [isotropic_gaussian_measure, Finsupp.prod_fintype,
        Fintype.prod_prod_type] using
        Integrable.fintype_prod
          (μ := fun _ : Fin n => standard_gaussian_measure)
          (fun j => hx (s (0, j)))
    let q₀ : Polynomial ℝ := ∑ s ∈ p.support,
      Polynomial.monomial (s.sum fun _ e => e)
        (p.coeff s * ∫ z, s.prod (fun ij e => z ij.2 ^ e)
          ∂isotropic_gaussian_measure n)
    let p₀ : ℝ := p.eval 0
    let q : Polynomial ℝ := q₀ - Polynomial.C p₀
    have hq₀deg : q₀.natDegree ≤ p.totalDegree := by
      dsimp [q₀]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro s hs
      exact (Polynomial.natDegree_monomial_le _).trans
        (MvPolynomial.le_totalDegree hs)
    have hqdeg : q.natDegree ≤ k := by
      apply le_trans (Polynomial.natDegree_sub_le q₀ (Polynomial.C p₀))
      rw [Polynomial.natDegree_C]
      exact max_le (hq₀deg.trans hpdeg) (Nat.zero_le k)
    have hq₀zero : q₀.eval 0 = p₀ := by
      dsimp [q₀, p₀]
      rw [MvPolynomial.eval_zero]
      change _ = p.coeff 0
      simp only [MvPolynomial.constantCoeff, Polynomial.eval_finset_sum,
        Polynomial.eval_monomial, Finsupp.prod_fintype]
      classical
      by_cases hzero : (0 : (Fin 1 × Fin n) →₀ ℕ) ∈ p.support
      · rw [Finset.sum_eq_single 0]
        · simp
        · intro s hs hszero
          have hsum : 0 < s.sum (fun _ e => e) :=
            Finsupp.sum_pos
              (fun i hi => Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)) hszero
          simp [zero_pow hsum.ne']
        · exact fun h => (h hzero).elim
      · have hcoeff : p.coeff 0 = 0 := by
          simpa [MvPolynomial.mem_support_iff] using hzero
        rw [hcoeff]
        exact Finset.sum_eq_zero fun s hs => by
          have hszero : s ≠ 0 := by
            intro h
            subst s
            exact hzero hs
          have hsum : 0 < s.sum (fun _ e => e) :=
            Finsupp.sum_pos
              (fun i hi => Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)) hszero
          simp [zero_pow hsum.ne']
    have hqzero : q.coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      simp [q, hq₀zero]
    have hfactor (s : (Fin 1 × Fin n) →₀ ℕ) (t : ℝ) (z : Fin n → ℝ) :
        s.prod (fun ij e => (t * z ij.2) ^ e) =
          t ^ (s.sum fun _ e => e) * s.prod (fun ij e => z ij.2 ^ e) := by
      simp [mul_pow, Finsupp.prod_mul, Finsupp.prod_pow,
        Finsupp.sum_fintype, ← Finset.prod_pow_eq_pow_sum]
    have hmonint (s : (Fin 1 × Fin n) →₀ ℕ) (t : ℝ) : Integrable
        (fun z : Fin n → ℝ => p.coeff s *
          s.prod (fun ij e => (t * z ij.2) ^ e))
        (isotropic_gaussian_measure n) := by
      have h := (hz s).const_mul (p.coeff s * t ^ (s.sum fun _ e => e))
      convert h using 1
      ext z
      rw [hfactor]
      ring
    have hq₀eval (t : ℝ) : q₀.eval t =
        ∫ z, sample_polynomial_observable p (fun _ j => t * z j)
          ∂isotropic_gaussian_measure n := by
      rw [p.as_sum]
      dsimp [q₀, sample_polynomial_observable]
      simp only [Polynomial.eval_finset_sum, Polynomial.eval_monomial,
        MvPolynomial.eval_sum, MvPolynomial.eval_monomial]
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro s hs
        rw [show (fun z : Fin n → ℝ => p.coeff s *
            s.prod (fun ij e => (t * z ij.2) ^ e)) =
            (fun z => (p.coeff s * t ^ (s.sum fun _ e => e)) *
              s.prod (fun ij e => z ij.2 ^ e)) by
          funext z
          rw [hfactor]
          ring]
        rw [integral_const_mul]
        ring
      · intro s hs
        exact hmonint s t
    let μ₀ : Measure (ℝ × (Fin n → ℝ)) :=
      standard_gaussian_measure.prod (isotropic_gaussian_measure n)
    let φ : ℝ × (Fin n → ℝ) → (Fin n → ℝ) :=
      fun w i => w.1 * w.2 i
    let Φ : ℝ × (Fin n → ℝ) → (Fin 1 → Fin n → ℝ) :=
      fun w _ i => w.1 * w.2 i
    have hφmeas : Measurable φ := by
      dsimp [φ]
      fun_prop
    have hΦmeas : Measurable Φ := by
      dsimp [Φ]
      fun_prop
    have hmapφ : Measure.map φ μ₀ = gaussian_scale_mixture n := by
      rfl
    have hmapΦ : Measure.map Φ μ₀ =
        iid_product_measure 1 (gaussian_scale_mixture n) := by
      let e := MeasurableEquiv.piUnique (fun _ : Fin 1 => Fin n → ℝ)
      rw [show Φ = e.symm ∘ φ by
        funext w i
        exact Subsingleton.elim i default ▸ rfl]
      rw [← Measure.map_map e.symm.measurable hφmeas, hmapφ]
      unfold iid_product_measure
      exact ((measurePreserving_piUnique
        (fun _ : Fin 1 => gaussian_scale_mixture n)).symm).map_eq
    letI : IsProbabilityMeasure μ₀ := by
      dsimp [μ₀]
      infer_instance
    letI : IsProbabilityMeasure (gaussian_scale_mixture n) := by
      rw [← hmapφ]
      exact Measure.isProbabilityMeasure_map hφmeas.aemeasurable
    letI : IsProbabilityMeasure
        (iid_product_measure 1 (gaussian_scale_mixture n)) := by
      unfold iid_product_measure
      infer_instance
    have hpLp : MemLp (sample_polynomial_observable p) 2
        (iid_product_measure 1 (gaussian_scale_mixture n)) := by
      apply memLp_two_of_variance_ne_zero hpmeas.aestronglyMeasurable
      exact ne_of_gt hpvar
    have hfLp : MemLp (sample_polynomial_observable p ∘ Φ) 2 μ₀ :=
      hpLp.comp_measurePreserving ⟨hΦmeas, hmapΦ⟩
    have hvarmap : variance (sample_polynomial_observable p ∘ Φ) μ₀ =
        sample_polynomial_variance (gaussian_scale_mixture n) p := by
      unfold sample_polynomial_variance
      rw [← hmapΦ]
      exact (variance_map hpmeas.aestronglyMeasurable.aemeasurable
        hΦmeas.aemeasurable).symm
    have hpolyLp (u : Polynomial ℝ) : MemLp (fun t => u.eval t) 2
        standard_gaussian_measure := by
      rw [u.as_sum_support]
      simp only [Polynomial.eval_finset_sum, Polynomial.eval_monomial]
      apply memLp_finsetSum
      intro i hi
      rw [memLp_two_iff_integrable_sq (by fun_prop)]
      have h := (hx (i + i)).const_mul ((u.coeff i) ^ 2)
      convert h using 1
      ext t
      simp [pow_two, pow_add]
      ring
    let F : ℝ → (Fin n → ℝ) → ℝ :=
      fun t z => sample_polynomial_observable p (fun _ j => t * z j)
    have hq₀evalF (t : ℝ) : q₀.eval t =
        ∫ z, F t z ∂isotropic_gaussian_measure n := by
      exact hq₀eval t
    have hFLp : MemLp (fun w : ℝ × (Fin n → ℝ) => F w.1 w.2) 2 μ₀ := by
      simpa [F, Φ, Function.comp_def] using hfLp
    let m₀ : ℝ := ∫ w, F w.1 w.2 ∂μ₀
    have hcenterLp : MemLp
        (fun w : ℝ × (Fin n → ℝ) => F w.1 w.2 - m₀) 2 μ₀ :=
      hFLp.sub (memLp_const m₀)
    have hcenterInt := hcenterLp.integrable one_le_two
    have hcenterSqInt := hcenterLp.integrable_sq
    have hslice : ∀ᵐ t ∂standard_gaussian_measure,
        MemLp (fun z => F t z - m₀) 2 (isotropic_gaussian_measure n) := by
      have hsliceInt := hcenterInt.prod_right_ae
      have hsliceSqInt := hcenterSqInt.prod_right_ae
      filter_upwards [hsliceInt, hsliceSqInt] with t ht ht2
      rw [memLp_two_iff_integrable_sq ht.aestronglyMeasurable]
      exact ht2
    have hJensen : ∀ᵐ t ∂standard_gaussian_measure,
        (q₀.eval t - m₀) ^ 2 ≤
          ∫ z, (F t z - m₀) ^ 2 ∂isotropic_gaussian_measure n := by
      filter_upwards [hslice] with t ht
      have hv := variance_nonneg (fun z => F t z - m₀)
        (isotropic_gaussian_measure n)
      rw [variance_eq_sub ht] at hv
      have htF : Integrable (F t) (isotropic_gaussian_measure n) := by
        have h := (ht.integrable one_le_two).add (integrable_const m₀)
        exact h.congr (Filter.Eventually.of_forall fun z => by simp)
      have hmean : ∫ z, (F t z - m₀) ∂isotropic_gaussian_measure n =
          q₀.eval t - m₀ := by
        calc
          ∫ z, (F t z - m₀) ∂isotropic_gaussian_measure n =
              (∫ z, F t z ∂isotropic_gaussian_measure n) -
                ∫ _z, m₀ ∂isotropic_gaussian_measure n := by
            exact integral_sub htF (integrable_const m₀)
          _ = (∫ z, F t z ∂isotropic_gaussian_measure n) - m₀ := by simp
          _ = q₀.eval t - m₀ := by rw [hq₀evalF]
      rw [hmean] at hv
      simpa only [Pi.pow_apply] using sub_nonneg.mp hv
    have hleftInt : Integrable (fun t => (q₀.eval t - m₀) ^ 2)
        standard_gaussian_measure :=
      ((hpolyLp q₀).sub (memLp_const m₀)).integrable_sq
    have hrightInt : Integrable
        (fun t => ∫ z, (F t z - m₀) ^ 2 ∂isotropic_gaussian_measure n)
        standard_gaussian_measure := hcenterSqInt.integral_prod_left
    have hvarq₀le : variance (fun t => q₀.eval t) standard_gaussian_measure ≤
        variance (fun w : ℝ × (Fin n → ℝ) => F w.1 w.2) μ₀ := by
      rw [← variance_sub_const (hpolyLp q₀).aestronglyMeasurable m₀]
      calc
        variance (fun t => q₀.eval t - m₀) standard_gaussian_measure
            ≤ ∫ t, (q₀.eval t - m₀) ^ 2 ∂standard_gaussian_measure :=
          variance_le_expectation_sq (by fun_prop)
        _ ≤ ∫ t, ∫ z, (F t z - m₀) ^ 2
              ∂isotropic_gaussian_measure n ∂standard_gaussian_measure :=
          integral_mono_ae hleftInt hrightInt hJensen
        _ = ∫ w, (F w.1 w.2 - m₀) ^ 2 ∂μ₀ := by
          dsimp [μ₀]
          exact (integral_prod _ hcenterSqInt).symm
        _ = variance (fun w : ℝ × (Fin n → ℝ) => F w.1 w.2) μ₀ := by
          exact (variance_eq_integral hFLp.aestronglyMeasurable.aemeasurable).symm
    have hqvar : variance (fun t => q.eval t) standard_gaussian_measure ≤
        sample_polynomial_variance (gaussian_scale_mixture n) p := by
      calc
        variance (fun t => q.eval t) standard_gaussian_measure =
            variance (fun t => q₀.eval t - p₀) standard_gaussian_measure :=
          variance_congr (Filter.Eventually.of_forall fun t => by simp [q])
        _ = variance (fun t => q₀.eval t) standard_gaussian_measure :=
          variance_sub_const (hpolyLp q₀).aestronglyMeasurable p₀
        _ ≤ variance (fun w : ℝ × (Fin n → ℝ) => F w.1 w.2) μ₀ := hvarq₀le
        _ = variance (sample_polynomial_observable p ∘ Φ) μ₀ :=
          variance_congr (Filter.Eventually.of_forall fun w => by
            rfl)
        _ = sample_polynomial_variance (gaussian_scale_mixture n) p := hvarmap
    have hEQ : sample_polynomial_expectation (gaussian_scale_mixture n) p =
        ∫ w, F w.1 w.2 ∂μ₀ := by
      unfold sample_polynomial_expectation
      rw [← hmapΦ]
      rw [integral_map hΦmeas.aemeasurable hpmeas.aestronglyMeasurable]
    have hqmean : (∫ t, q.eval t ∂standard_gaussian_measure) =
        sample_polynomial_expectation (gaussian_scale_mixture n) p - p₀ := by
      calc
        (∫ t, q.eval t ∂standard_gaussian_measure) =
            ∫ t, (q₀.eval t - p₀) ∂standard_gaussian_measure := by
          apply integral_congr_ae
          filter_upwards with t
          simp [q]
        _ = (∫ t, q₀.eval t ∂standard_gaussian_measure) - p₀ := by
          rw [integral_sub ((hpolyLp q₀).integrable one_le_two)
            (integrable_const p₀)]
          simp
        _ = (∫ t, ∫ z, F t z ∂isotropic_gaussian_measure n
              ∂standard_gaussian_measure) - p₀ := by
          congr 1
          apply integral_congr_ae
          filter_upwards with t
          exact hq₀evalF t
        _ = (∫ w, F w.1 w.2 ∂μ₀) - p₀ := by
          rw [integral_prod _ (hFLp.integrable one_le_two)]
        _ = sample_polynomial_expectation (gaussian_scale_mixture n) p - p₀ := by
          rw [hEQ]
    let g : (Fin n → ℝ) → ℝ :=
      fun y => sample_polynomial_observable p (fun _ => y)
    have hsingle (μ : Measure (Fin n → ℝ)) :
        sample_polynomial_expectation μ p = ∫ y, g y ∂μ := by
      unfold sample_polynomial_expectation iid_product_measure
      let e := MeasurableEquiv.piUnique (fun _ : Fin 1 => Fin n → ℝ)
      calc
        (∫ x, sample_polynomial_observable p x ∂Measure.pi fun _ : Fin 1 => μ) =
            ∫ x, g (e x) ∂Measure.pi fun _ : Fin 1 => μ := by
          apply integral_congr_ae
          filter_upwards with x
          unfold g sample_polynomial_observable
          apply congrArg (fun f : (Fin 1 × Fin n) → ℝ => p.eval f)
          funext ij
          rw [Subsingleton.elim ij.1 default]
          rfl
        _ = ∫ y, g y ∂μ :=
          (measurePreserving_piUnique (fun _ : Fin 1 => μ)).integral_comp' g
    have hgintQ : Integrable g (gaussian_scale_mixture n) := by
      let e := MeasurableEquiv.piUnique (fun _ : Fin 1 => Fin n → ℝ)
      apply ((measurePreserving_piUnique
        (fun _ : Fin 1 => gaussian_scale_mixture n)).integrable_comp_emb
          e.measurableEmbedding).mp
      have h := hpLp.integrable one_le_two
      apply h.congr
      filter_upwards with x
      unfold g sample_polynomial_observable
      change p.eval (fun ij => x ij.1 ij.2) =
        p.eval (fun ij => (fun _ => e x) ij.1 ij.2)
      apply congrArg (fun f : (Fin 1 × Fin n) → ℝ => p.eval f)
      funext ij
      rw [Subsingleton.elim ij.1 default]
      rfl
    have hgintDirac : Integrable g (Measure.dirac 0) :=
      integrable_dirac (by simp)
    have h_one_sub :
        (↑(1 - α) : ENNReal).toReal = 1 - (α : ℝ) := by
      rw [ENNReal.coe_toReal, NNReal.coe_sub hα]
      norm_num
    have h_alpha :
        (↑α : ENNReal).toReal = (α : ℝ) :=
      ENNReal.coe_toReal α
    have hEP : sample_polynomial_expectation
        (origin_contamination α (gaussian_scale_mixture n)) p =
        (1 - (α : ℝ)) * sample_polynomial_expectation
          (gaussian_scale_mixture n) p + (α : ℝ) * p₀ := by
      rw [hsingle, origin_contamination]
      rw [integral_add_measure (hgintQ.smul_measure _)
        (hgintDirac.smul_measure _)]
      simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
      rw [← hsingle]
      have hgzero : g 0 = p₀ := by
        simp [g, p₀, sample_polynomial_observable]
      rw [hgzero]
      rw [h_one_sub, h_alpha]
      all_goals simp
    have hqbound := hC k q hqdeg hqzero
    have hqabs :
        |∫ t, q.eval t ∂standard_gaussian_measure| ≤
          C * (Real.sqrt (k : ℝ) *
            Real.sqrt (sample_polynomial_variance
              (gaussian_scale_mixture n) p)) := by
      calc
        |∫ t, q.eval t ∂standard_gaussian_measure| ≤
            C * Real.sqrt ((k : ℝ) *
              variance (fun t => q.eval t) standard_gaussian_measure) :=
          hqbound
        _ = C * (Real.sqrt (k : ℝ) *
              Real.sqrt (variance (fun t => q.eval t)
                standard_gaussian_measure)) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg k)]
        _ ≤ C * (Real.sqrt (k : ℝ) *
              Real.sqrt (sample_polynomial_variance
                (gaussian_scale_mixture n) p)) := by
          gcongr
    have hα0 : (0 : ℝ) ≤ (α : ℝ) := NNReal.coe_nonneg α
    have hgap :
        |sample_polynomial_expectation
            (origin_contamination α (gaussian_scale_mixture n)) p -
          sample_polynomial_expectation (gaussian_scale_mixture n) p| =
          (α : ℝ) *
            |∫ t, q.eval t ∂standard_gaussian_measure| := by
      rw [hEP, hqmean]
      rw [show
          (1 - (α : ℝ)) *
                sample_polynomial_expectation (gaussian_scale_mixture n) p +
              (α : ℝ) * p₀ -
                sample_polynomial_expectation (gaussian_scale_mixture n) p =
            -((α : ℝ) *
              (sample_polynomial_expectation (gaussian_scale_mixture n) p -
                p₀)) by
        ring]
      rw [abs_neg, abs_mul, abs_of_nonneg hα0]
    have hscaled :
        |sample_polynomial_expectation
            (origin_contamination α (gaussian_scale_mixture n)) p -
          sample_polynomial_expectation (gaussian_scale_mixture n) p| ≤
          L * Real.sqrt (sample_polynomial_variance
            (gaussian_scale_mixture n) p) := by
      calc
        |sample_polynomial_expectation
            (origin_contamination α (gaussian_scale_mixture n)) p -
          sample_polynomial_expectation (gaussian_scale_mixture n) p| =
            (α : ℝ) *
              |∫ t, q.eval t ∂standard_gaussian_measure| := hgap
        _ ≤ (α : ℝ) *
              (C * (Real.sqrt (k : ℝ) *
                Real.sqrt (sample_polynomial_variance
                  (gaussian_scale_mixture n) p))) :=
          mul_le_mul_of_nonneg_left hqabs hα0
        _ = L * Real.sqrt (sample_polynomial_variance
              (gaussian_scale_mixture n) p) := by
          dsimp [L]
          ring
    exact (div_le_iff₀ (Real.sqrt_pos.2 hpvar)).2 hscaled
  · rw [Set.not_nonempty_iff_eq_empty.mp he]
    simp [hL0]

@[blueprint "lem:lda-sq-le-of-gap-bound"
  (statement := /-- Let $n,m,k\in\mathbb N$, let $P,Q$ be measures on $\mathbb R^n$, and let $B\in\mathbb R$ with $B\geq0$. Suppose that for every polynomial observable $p$ on $m$ samples with $\deg p\leq k$ and $\operatorname{Var}_{Q^{\otimes m}}(p)>0$ one has
  \[
    \left(\mathbb E_{P^{\otimes m}}[p]-\mathbb E_{Q^{\otimes m}}[p]\right)^2
      \leq B\,\operatorname{Var}_{Q^{\otimes m}}(p).
  \]
  Then $\left(\operatorname{LDA}^{(m)}_{\leq k}(P,Q)\right)^2\leq B$. -/)
  (proof := /-- By \cref{lem:low-degree-advantage-nonnegative} the advantage is nonnegative, so it suffices to bound it by $\sqrt B$. By \cref{def:low-degree-advantage} the advantage is the supremum of the normalized gaps over admissible polynomials, and $\sqrt B\geq0$, so it is enough to bound each admissible normalized gap. Fix an admissible $p$ with $\operatorname{Var}_{Q^{\otimes m}}(p)>0$. Multiplying through by the positive $\sqrt{\operatorname{Var}_{Q^{\otimes m}}(p)}$ reduces the claim to $\left|\mathbb E_{P^{\otimes m}}[p]-\mathbb E_{Q^{\otimes m}}[p]\right|\leq\sqrt B\,\sqrt{\operatorname{Var}_{Q^{\otimes m}}(p)}=\sqrt{B\,\operatorname{Var}_{Q^{\otimes m}}(p)}$. Writing the absolute value as $\sqrt{(\cdots)^2}$ and using monotonicity of the square root, this follows from the hypothesis. Squaring the resulting bound gives $\left(\operatorname{LDA}^{(m)}_{\leq k}(P,Q)\right)^2\leq(\sqrt B)^2=B$. -/)
  (title := /-- Squared low-degree advantage from a uniform gap bound -/)
  (latexEnv := "lemma")]
lemma lda_sq_le_of_gap_bound (n m k : ℕ) (P Q : Measure (Fin n → ℝ)) (B : ℝ)
    (hB : 0 ≤ B)
    (hbound : ∀ p : MvPolynomial (Fin m × Fin n) ℝ, p.totalDegree ≤ k →
      0 < sample_polynomial_variance Q p →
      (sample_polynomial_expectation P p - sample_polynomial_expectation Q p) ^ 2
        ≤ B * sample_polynomial_variance Q p) :
    (low_degree_advantage n m k P Q) ^ 2 ≤ B := by
  have hn := low_degree_advantage_nonnegative n m k P Q
  have hle : low_degree_advantage n m k P Q ≤ Real.sqrt B := by
    unfold low_degree_advantage
    apply Real.sSup_le
    · rintro r ⟨p, hpdeg, hpvar, rfl⟩
      rw [div_le_iff₀ (Real.sqrt_pos.2 hpvar), ← Real.sqrt_mul hB,
        ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (hbound p hpdeg hpvar)
    · exact Real.sqrt_nonneg B
  calc (low_degree_advantage n m k P Q) ^ 2
        ≤ (Real.sqrt B) ^ 2 := (sq_le_sq₀ hn (Real.sqrt_nonneg B)).mpr hle
    _ = B := Real.sq_sqrt hB

@[blueprint "lem:integral-mul-sq-le-of-memLp"
  (statement := /-- Let $(\Omega,\mu)$ be a measure space and let $F,G:\Omega\to\mathbb R$ both lie in $L^2(\mu)$. Then
  \[
    \Bigl(\int_\Omega FG\,d\mu\Bigr)^2
      \leq \Bigl(\int_\Omega F^2\,d\mu\Bigr)\Bigl(\int_\Omega G^2\,d\mu\Bigr).
  \] -/)
  (proof := /-- Since $F,G\in L^2(\mu)$, the product $FG$ is integrable. Hölder's inequality with the conjugate pair $p=q=2$ gives
  \[
    \int_\Omega \lVert F\rVert\,\lVert G\rVert\,d\mu
      \leq \Bigl(\int_\Omega \lVert F\rVert^2\,d\mu\Bigr)^{1/2}
           \Bigl(\int_\Omega \lVert G\rVert^2\,d\mu\Bigr)^{1/2},
  \]
  and for real-valued functions $\lVert F\rVert^2=F^2$ pointwise, so the two factors are $\bigl(\int F^2\bigr)^{1/2}$ and $\bigl(\int G^2\bigr)^{1/2}$. Bounding the integral by the integral of the absolute value and using $|FG|=\lVert F\rVert\,\lVert G\rVert$ yields
  \[
    \Bigl|\int_\Omega FG\,d\mu\Bigr|
      \leq \sqrt{\int_\Omega F^2\,d\mu}\ \sqrt{\int_\Omega G^2\,d\mu}.
  \]
  Both integrals $\int F^2$ and $\int G^2$ are nonnegative because their integrands are squares, so the right-hand side is nonnegative. Squaring this inequality between nonnegative numbers, and using $\bigl(\int FG\bigr)^2=\bigl|\int FG\bigr|^2$ together with $(\sqrt a)^2=a$ for $a\geq0$, gives the assertion. -/)
  (title := /-- Cauchy--Schwarz inequality for square-integrable functions -/)
  (latexEnv := "lemma")]
lemma integral_mul_sq_le_of_memLp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F G : Ω → ℝ) (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    (∫ ω, F ω * G ω ∂μ) ^ 2 ≤ (∫ ω, F ω ^ 2 ∂μ) * (∫ ω, G ω ^ 2 ∂μ) := by
  have hFG : Integrable (fun ω => F ω * G ω) μ := hF.integrable_mul hG
  have hcs := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) (p := 2) (q := 2) (f := F) (g := G)
    (Real.HolderConjugate.two_two) (by simpa using hF) (by simpa using hG)
  have hnorm2 : ∀ H : Ω → ℝ, (∫ ω, ‖H ω‖ ^ (2 : ℝ) ∂μ) = ∫ ω, H ω ^ 2 ∂μ := by
    intro H
    apply integral_congr_ae
    filter_upwards with ω
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [hnorm2 F, hnorm2 G] at hcs
  have hA : 0 ≤ ∫ ω, F ω ^ 2 ∂μ :=
    integral_nonneg fun ω => sq_nonneg _
  have hB : 0 ≤ ∫ ω, G ω ^ 2 ∂μ :=
    integral_nonneg fun ω => sq_nonneg _
  have hle : |∫ ω, F ω * G ω ∂μ| ≤
      Real.sqrt (∫ ω, F ω ^ 2 ∂μ) * Real.sqrt (∫ ω, G ω ^ 2 ∂μ) := by
    refine (abs_integral_le_integral_abs).trans ?_
    have hEq : ∫ ω, |F ω * G ω| ∂μ = ∫ ω, ‖F ω‖ * ‖G ω‖ ∂μ := by
      apply integral_congr_ae
      filter_upwards with ω
      rw [Real.norm_eq_abs, Real.norm_eq_abs, ← abs_mul]
    rw [hEq]
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    exact hcs
  calc (∫ ω, F ω * G ω ∂μ) ^ 2
      = |∫ ω, F ω * G ω ∂μ| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.sqrt (∫ ω, F ω ^ 2 ∂μ) * Real.sqrt (∫ ω, G ω ^ 2 ∂μ)) ^ 2 := by
        have hrhs : 0 ≤ Real.sqrt (∫ ω, F ω ^ 2 ∂μ) * Real.sqrt (∫ ω, G ω ^ 2 ∂μ) :=
          mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        exact pow_le_pow_left₀ (abs_nonneg _) hle 2
    _ = (∫ ω, F ω ^ 2 ∂μ) * (∫ ω, G ω ^ 2 ∂μ) := by
        rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]

@[blueprint "lem:gaussian-scale-mixture-isOpenPosMeasure"
  (statement := /-- For every $n\in\mathbb N$, the Gaussian scale mixture $Q_n$ of \cref{def:gaussian-scale-mixture} assigns strictly positive mass to every nonempty open subset of $\mathbb R^n$. -/)
  (proof := /-- The standard Gaussian measure $\gamma$ of \cref{def:standard-gaussian-measure} is the law $\mathcal N(0,1)$, whose variance $1$ is nonzero, so Lebesgue measure on $\mathbb R$ is absolutely continuous with respect to $\gamma$; a measure dominating Lebesgue measure in this sense charges every nonempty open set, so $\gamma$ has this property. The isotropic Gaussian measure of \cref{def:isotropic-gaussian-measure} is a finite product of copies of $\gamma$, and a product of finitely many probability measures each charging nonempty open sets again charges nonempty open sets; the same closure property applies to the binary product $\gamma\otimes G_n$. Finally, $Q_n$ is by \cref{def:gaussian-scale-mixture} the pushforward of $\gamma\otimes G_n$ along $(\lambda,z)\mapsto(\lambda z_i)_{i=1}^n$. This map is continuous, and it is surjective because any target point $y$ is the image of $(1,y)$. The pushforward of a measure charging nonempty open sets along a continuous surjection again charges nonempty open sets, which gives the claim. -/)
  (title := /-- Full support of the Gaussian scale mixture -/)
  (latexEnv := "lemma")]
lemma gaussian_scale_mixture_isOpenPosMeasure (n : ℕ) :
    (gaussian_scale_mixture n).IsOpenPosMeasure := by
  haveI hstdprob : IsProbabilityMeasure standard_gaussian_measure := by
    unfold standard_gaussian_measure; infer_instance
  haveI hstd : (standard_gaussian_measure).IsOpenPosMeasure := by
    have h : (volume : Measure ℝ) ≪ standard_gaussian_measure := by
      unfold standard_gaussian_measure
      exact gaussianReal_absolutelyContinuous' 0 (by norm_num)
    exact h.isOpenPosMeasure
  haveI hiso : (isotropic_gaussian_measure n).IsOpenPosMeasure := by
    unfold isotropic_gaussian_measure
    infer_instance
  haveI hprod : (standard_gaussian_measure.prod
      (isotropic_gaussian_measure n)).IsOpenPosMeasure := by
    haveI : IsProbabilityMeasure (isotropic_gaussian_measure n) := by
      unfold isotropic_gaussian_measure; infer_instance
    exact MeasureTheory.Measure.prod.instIsOpenPosMeasure
  unfold gaussian_scale_mixture
  have hcont : Continuous (fun z : ℝ × (Fin n → ℝ) => fun i => z.1 * z.2 i) := by
    fun_prop
  have hsurj : Function.Surjective
      (fun z : ℝ × (Fin n → ℝ) => fun i => z.1 * z.2 i) := by
    intro y
    exact ⟨(1, y), by simp⟩
  exact hcont.isOpenPosMeasure_map hsurj

@[blueprint "lem:gsm-map-eq"
  (statement := /-- For every $n\in\mathbb N$, the pushforward of the product of the measures of \cref{def:standard-gaussian-measure,def:isotropic-gaussian-measure} along $(\lambda,z)\mapsto(\lambda z_i)_{i=1}^n$ equals the Gaussian scale mixture $Q_n$ of \cref{def:gaussian-scale-mixture}. -/)
  (proof := /-- This is exactly the defining formula for $Q_n$ recorded in \cref{def:gaussian-scale-mixture}, so the two sides are definitionally equal. -/)
  (title := /-- Pushforward presentation of the Gaussian scale mixture -/)
  (latexEnv := "lemma")]
lemma gsm_map_eq (n : ℕ) :
    Measure.map (fun w : ℝ × (Fin n → ℝ) ↦ fun i ↦ w.1 * w.2 i)
      (standard_gaussian_measure.prod (isotropic_gaussian_measure n)) =
      gaussian_scale_mixture n := rfl

@[blueprint "lem:std-pow-integrable"
  (statement := /-- For every $e\in\mathbb N$, the function $x\mapsto x^e$ is integrable with respect to the standard Gaussian measure of \cref{def:standard-gaussian-measure}. -/)
  (proof := /-- The measure $\mathcal N(0,1)$ is a probability measure. The identity function on $\mathbb R$ belongs to $L^{e}(\mathcal N(0,1))$ for every finite exponent, since all moments of a real Gaussian law are finite. Membership of the identity in $L^{e}$ yields integrability of the $e$-th power of its norm, that is of $x\mapsto|x|^{e}$. Because a real-valued function is integrable exactly when its norm is, and $\lVert x^{e}\rVert=|x|^{e}$, the function $x\mapsto x^{e}$ is integrable. -/)
  (title := /-- Integrability of Gaussian power moments -/)
  (latexEnv := "lemma")]
lemma std_pow_integrable (e : ℕ) :
    Integrable (fun x : ℝ => x ^ e) standard_gaussian_measure := by
  letI : IsProbabilityMeasure standard_gaussian_measure := by
    unfold standard_gaussian_measure; infer_instance
  rw [← integrable_norm_iff (by fun_prop)]
  simpa [standard_gaussian_measure] using
    (memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := (1 : NNReal))
      (e : ENNReal) (by simp)).integrable_norm_pow'

@[blueprint "lem:iso-prod-integrable"
  (statement := /-- Let $n\in\mathbb N$ and let $s:\{1,\dots,n\}\to\mathbb N$ be finitely supported. Then the monomial $z\mapsto\prod_{j=1}^n z_j^{s_j}$ is integrable with respect to the isotropic Gaussian measure of \cref{def:isotropic-gaussian-measure}. -/)
  (proof := /-- By \cref{def:isotropic-gaussian-measure} the measure is the product over the $n$ coordinates of the standard Gaussian measure, which is a probability measure. Each factor $z_j\mapsto z_j^{s_j}$ is integrable for the corresponding marginal by \cref{lem:std-pow-integrable}. A product of coordinatewise integrable functions is integrable for a finite product of probability measures, and rewriting the finitely supported product as a product over all $n$ coordinates gives the claim. -/)
  (title := /-- Integrability of monomials under the isotropic Gaussian -/)
  (latexEnv := "lemma")]
lemma iso_prod_integrable (n : ℕ) (s : Fin n →₀ ℕ) :
    Integrable (fun z : Fin n → ℝ => s.prod fun j e => z j ^ e)
      (isotropic_gaussian_measure n) := by
  letI : IsProbabilityMeasure standard_gaussian_measure := by
    unfold standard_gaussian_measure; infer_instance
  simpa [isotropic_gaussian_measure, Finsupp.prod_fintype] using
    Integrable.fintype_prod
      (μ := fun _ : Fin n => standard_gaussian_measure)
      (fun j => std_pow_integrable (s j))

@[blueprint "lem:gsm-monomial-integrable"
  (statement := /-- Let $n\in\mathbb N$ and let $s:\{1,\dots,n\}\to\mathbb N$ be finitely supported. Then the monomial $y\mapsto\prod_{j=1}^n y_j^{s_j}$ is integrable with respect to the Gaussian scale mixture $Q_n$ of \cref{def:gaussian-scale-mixture}. -/)
  (proof := /-- The monomial is continuous, being a finite product of continuous coordinate powers. By \cref{lem:gsm-map-eq} the measure $Q_n$ is the pushforward of $\gamma\otimes G_n$ along the measurable map $(\lambda,z)\mapsto(\lambda z_i)_{i=1}^n$, so integrability against $Q_n$ is equivalent to integrability of the composition against $\gamma\otimes G_n$. Substituting $y_j=\lambda z_j$ and collecting the scalar factors, the composition equals
  \[
    (\lambda,z)\mapsto \lambda^{\sum_j s_j}\prod_{j=1}^n z_j^{s_j}.
  \]
  The first factor is integrable for $\gamma$ by \cref{lem:std-pow-integrable}, and the second is integrable for $G_n$ by \cref{lem:iso-prod-integrable}. A product of functions of separate variables, each integrable for its own marginal probability measure, is integrable for the product measure, which proves the claim. -/)
  (title := /-- Integrability of monomials under the Gaussian scale mixture -/)
  (latexEnv := "lemma")]
lemma gsm_monomial_integrable (n : ℕ) (s : Fin n →₀ ℕ) :
    Integrable (fun y : Fin n → ℝ => s.prod fun j e => y j ^ e)
      (gaussian_scale_mixture n) := by
  letI : IsProbabilityMeasure standard_gaussian_measure := by
    unfold standard_gaussian_measure; infer_instance
  letI : IsProbabilityMeasure (isotropic_gaussian_measure n) := by
    unfold isotropic_gaussian_measure; infer_instance
  have hmeas : AEMeasurable (fun w : ℝ × (Fin n → ℝ) ↦ fun i ↦ w.1 * w.2 i)
      (standard_gaussian_measure.prod (isotropic_gaussian_measure n)) := by
    fun_prop
  have hcont : Continuous (fun y : Fin n → ℝ => s.prod fun j e => y j ^ e) := by
    simp only [Finsupp.prod]
    exact continuous_finset_prod _ (fun j _ => (continuous_apply j).pow _)
  rw [← gsm_map_eq n,
    integrable_map_measure hcont.aestronglyMeasurable hmeas]
  have hfactor : (fun w : ℝ × (Fin n → ℝ) =>
        (s.prod fun j e => (fun i => w.1 * w.2 i) j ^ e)) =
      (fun w : ℝ × (Fin n → ℝ) =>
        w.1 ^ (s.sum fun _ e => e) * (s.prod fun j e => w.2 j ^ e)) := by
    funext w
    simp only [Function.comp]
    rw [Finsupp.prod, Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    rw [mul_pow]
  rw [Function.comp_def, hfactor]
  exact (std_pow_integrable (s.sum fun _ e => e)).mul_prod (iso_prod_integrable n s)

@[blueprint "lem:gsm-poly-integrable"
  (statement := /-- For every $n\in\mathbb N$ and every polynomial $g\in\mathbb R[y_1,\dots,y_n]$, the evaluation $y\mapsto g(y)$ is integrable with respect to the Gaussian scale mixture $Q_n$ of \cref{def:gaussian-scale-mixture}. -/)
  (proof := /-- Write $g$ as the finite sum of its monomials $\sum_{s}c_s\,y^{s}$ over its support. Each monomial $y\mapsto y^{s}$ is integrable for $Q_n$ by \cref{lem:gsm-monomial-integrable}, hence so is each scalar multiple $c_s\,y^{s}$. A finite sum of integrable functions is integrable, which gives the claim. -/)
  (title := /-- Integrability of polynomials under the Gaussian scale mixture -/)
  (latexEnv := "lemma")]
lemma gsm_poly_integrable (n : ℕ) (g : MvPolynomial (Fin n) ℝ) :
    Integrable (fun y : Fin n → ℝ => MvPolynomial.eval y g)
      (gaussian_scale_mixture n) := by
  rw [g.as_sum]
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_monomial]
  apply integrable_finset_sum
  intro s hs
  exact (gsm_monomial_integrable n s).const_mul (MvPolynomial.coeff s g)

@[blueprint "lem:gsm-mul-integrable"
  (statement := /-- For every $n\in\mathbb N$ and all polynomials $p,q\in\mathbb R[y_1,\dots,y_n]$, the function $y\mapsto p(y)q(y)$ is integrable with respect to the Gaussian scale mixture $Q_n$ of \cref{def:gaussian-scale-mixture}. -/)
  (proof := /-- The product $pq$ is itself a polynomial, so $y\mapsto (pq)(y)$ is integrable for $Q_n$ by \cref{lem:gsm-poly-integrable}. Evaluation is a ring homomorphism, so $(pq)(y)=p(y)q(y)$ for every $y$; the two functions therefore agree everywhere and integrability transfers. -/)
  (title := /-- Integrability of products of polynomials -/)
  (latexEnv := "lemma")]
lemma gsm_mul_integrable (n : ℕ) (p q : MvPolynomial (Fin n) ℝ) :
    Integrable (fun y => MvPolynomial.eval y p * MvPolynomial.eval y q)
      (gaussian_scale_mixture n) := by
  have h := gsm_poly_integrable n (p * q)
  refine h.congr (Filter.Eventually.of_forall ?_)
  intro y
  simp [MvPolynomial.eval_mul]

@[blueprint "lem:mvpoly-continuous-eval"
  (statement := /-- Let $\sigma$ be a type and let $r\in\mathbb R[x_\sigma]$ be a multivariate polynomial. Then the evaluation map $y\mapsto r(y)$ from $\sigma\to\mathbb R$ to $\mathbb R$ is continuous. -/)
  (proof := /-- Argue by induction on the structure of $r$. If $r=C(a)$ is a constant, the evaluation is the constant function $y\mapsto a$, which is continuous. If $r=p+q$ and both evaluations are continuous, then the evaluation of $r$ is their pointwise sum, hence continuous. If $r=p\cdot X_j$ and the evaluation of $p$ is continuous, then the evaluation of $r$ is the pointwise product of that map with the coordinate projection $y\mapsto y_j$, which is continuous; a product of continuous real-valued maps is continuous. These three cases exhaust the induction. -/)
  (title := /-- Continuity of polynomial evaluation -/)
  (latexEnv := "lemma")]
lemma mvpoly_continuous_eval {σ : Type*} (r : MvPolynomial σ ℝ) :
    Continuous (fun y : σ → ℝ => MvPolynomial.eval y r) := by
  induction r using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.eval_C]; exact continuous_const
  | add p q hp hq => simp only [MvPolynomial.eval_add]; exact hp.add hq
  | mul_X p j hp =>
      simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X]
      exact hp.mul (continuous_apply j)

@[blueprint "lem:mvpoly-eval-zero-of-forall"
  (statement := /-- Let $N\in\mathbb N$ and let $p\in\mathbb R[x_1,\dots,x_N]$ satisfy $p(y)=0$ for every $y\in\mathbb R^N$. Then $p=0$ as a polynomial. -/)
  (proof := /-- Induct on $N$. For $N=0$ there are no variables, so $p$ is a constant $C(a)$; evaluating at the unique point of $\mathbb R^0$ gives $a=0$, hence $p=0$.

  For the inductive step, suppose the statement holds for $N=n$ and let $p\in\mathbb R[x_0,\dots,x_n]$ vanish identically on $\mathbb R^{n+1}$. View $p$ through the isomorphism that presents it as a univariate polynomial in $x_0$ with coefficients in $\mathbb R[x_1,\dots,x_n]$. Fix $s\in\mathbb R^{n}$ and specialise the coefficients at $s$: the resulting univariate real polynomial vanishes at every $y_0\in\mathbb R$, because its value at $y_0$ is $p$ evaluated at the point obtained by prepending $y_0$ to $s$. A univariate real polynomial vanishing at every real number is the zero polynomial, so each of its coefficients is zero. Comparing coefficients in degree $j$, the coefficient of $x_0^j$, an element of $\mathbb R[x_1,\dots,x_n]$, vanishes at every $s\in\mathbb R^{n}$, hence is the zero polynomial by the inductive hypothesis. All coefficients vanish, so the image of $p$ under the isomorphism is zero; since the isomorphism is injective, $p=0$. -/)
  (title := /-- A polynomial vanishing on all of $\mathbb R^N$ is zero -/)
  (latexEnv := "lemma")]
lemma mvpoly_eval_zero_of_forall : ∀ (N : ℕ) (p : MvPolynomial (Fin N) ℝ),
    (∀ y : Fin N → ℝ, MvPolynomial.eval y p = 0) → p = 0 := by
  intro N
  induction N with
  | zero =>
      intro p h
      have h0 := h (fun i => i.elim0)
      rw [MvPolynomial.eq_C_of_isEmpty p, MvPolynomial.eval_C] at h0
      rw [MvPolynomial.eq_C_of_isEmpty p, h0, map_zero]
  | succ n ih =>
      intro p h
      have hf : (MvPolynomial.finSuccEquiv ℝ n p) = 0 := by
        apply Polynomial.ext
        intro j
        rw [Polynomial.coeff_zero]
        apply ih
        intro s
        have hpoly : Polynomial.map (MvPolynomial.eval s)
            (MvPolynomial.finSuccEquiv ℝ n p) = 0 := by
          apply Polynomial.funext
          intro y0
          rw [Polynomial.eval_zero, ← MvPolynomial.eval_eq_eval_mv_eval']
          exact h (Fin.cons y0 s)
        have hc := congrArg (fun P => Polynomial.coeff P j) hpoly
        simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using hc
      have hinj := (MvPolynomial.finSuccEquiv ℝ n).injective
      apply hinj
      rw [hf, map_zero]

@[blueprint "lem:gsm-exists-representative"
  (statement := /-- Let $n,k\in\mathbb N$ and let $Q=Q_n$ be the Gaussian scale mixture of \cref{def:gaussian-scale-mixture}. Then there exists a polynomial $\rho\in\mathbb R[y_1,\dots,y_n]$ with $\deg\rho\leq k$ such that for every $q\in\mathbb R[y_1,\dots,y_n]$ with $\deg q\leq k$ one has
  \[
    \int_{\mathbb R^n}\rho\,q\;dQ = q(0)-\int_{\mathbb R^n}q\;dQ.
  \] -/)
  (proof := /-- Let $V\subseteq\mathbb R[y_1,\dots,y_n]$ be the span of the monomials $y^{s}$ with $\deg s\leq k$. There are finitely many such $s$, so $V$ is finite dimensional, and $V$ is contained in the subspace $D$ of polynomials of total degree at most $k$, since each spanning monomial has total degree at most $k$ and $D$ is closed under sums and scalar multiples. Conversely every $q$ with $\deg q\leq k$ lies in $V$: expanding $q$ into its monomials, each occurring exponent $s$ satisfies $\deg s\leq\deg q\leq k$, so each term is a scalar multiple of a spanning monomial.

  Define the bilinear form $B(p,q)=\int p\,q\;dQ$ on $V$. It is well defined and bilinear, since the relevant integrands are integrable by \cref{lem:gsm-mul-integrable} and integration is linear in each argument. The form $B$ is anisotropic: if $B(p,p)=\int p^2\,dQ=0$ with $p\in V$, then, as the integrand is nonnegative and integrable, $p^2=0$ holds $Q$-almost everywhere; the map $y\mapsto p(y)^2$ is continuous by \cref{lem:mvpoly-continuous-eval}, and $Q$ charges every nonempty open set by \cref{lem:gaussian-scale-mixture-isOpenPosMeasure}, so a continuous function vanishing $Q$-almost everywhere vanishes identically. Thus $p(y)=0$ for all $y$, whence $p=0$ by \cref{lem:mvpoly-eval-zero-of-forall}. An anisotropic bilinear form on a finite-dimensional space is nondegenerate.

  Consider the linear functional $G(q)=q(0)-\int q\;dQ$ on $V$; it is linear because evaluation at $0$ is linear and integration is linear, the integrals existing by \cref{lem:gsm-poly-integrable}. Since $B$ is nondegenerate on the finite-dimensional space $V$, the induced map from $V$ to its dual is an isomorphism, so there is $\rho\in V$ with $B(\rho,q)=G(q)$ for all $q\in V$. As $\rho\in V\subseteq D$ we get $\deg\rho\leq k$, and for any $q$ with $\deg q\leq k$ we have $q\in V$, so $\int\rho q\;dQ=B(\rho,q)=G(q)=q(0)-\int q\;dQ$, as required. -/)
  (title := /-- Riesz representative of the origin-evaluation gap functional -/)
  (latexEnv := "lemma")]
lemma gsm_exists_representative (n k : ℕ) :
    ∃ ρ : MvPolynomial (Fin n) ℝ, ρ.totalDegree ≤ k ∧
      ∀ q : MvPolynomial (Fin n) ℝ, q.totalDegree ≤ k →
        ∫ y, MvPolynomial.eval y ρ * MvPolynomial.eval y q
            ∂(gaussian_scale_mixture n)
          = MvPolynomial.eval 0 q -
            ∫ y, MvPolynomial.eval y q ∂(gaussian_scale_mixture n) := by
  classical
  letI hstd : IsProbabilityMeasure standard_gaussian_measure := by
    unfold standard_gaussian_measure; infer_instance
  haveI hpos := gaussian_scale_mixture_isOpenPosMeasure n
  set Q := gaussian_scale_mixture n with hQdef
  have hint : ∀ p q : MvPolynomial (Fin n) ℝ,
      Integrable (fun y => MvPolynomial.eval y p * MvPolynomial.eval y q) Q :=
    fun p q => gsm_mul_integrable n p q
  have hpint : ∀ q : MvPolynomial (Fin n) ℝ,
      Integrable (fun y => MvPolynomial.eval y q) Q :=
    fun q => gsm_poly_integrable n q
  let B₀ : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ
      (fun p q => ∫ y, MvPolynomial.eval y p * MvPolynomial.eval y q ∂Q)
      (by
        intro p₁ p₂ q
        rw [← integral_add (hint p₁ q) (hint p₂ q)]
        apply integral_congr_ae; filter_upwards with y
        simp only [MvPolynomial.eval_add]; ring)
      (by
        intro c p q
        rw [smul_eq_mul, ← integral_const_mul]
        apply integral_congr_ae; filter_upwards with y
        simp only [MvPolynomial.smul_eval]; ring)
      (by
        intro p q₁ q₂
        rw [← integral_add (hint p q₁) (hint p q₂)]
        apply integral_congr_ae; filter_upwards with y
        simp only [MvPolynomial.eval_add]; ring)
      (by
        intro c p q
        rw [smul_eq_mul, ← integral_const_mul]
        apply integral_congr_ae; filter_upwards with y
        simp only [MvPolynomial.smul_eval]; ring)
  let Sset : Set (Fin n →₀ ℕ) := {s | s.degree ≤ k}
  have hSfin : Sset.Finite := Finsupp.finite_of_degree_le k
  let Mset : Set (MvPolynomial (Fin n) ℝ) :=
    (fun s => (MvPolynomial.monomial s (1 : ℝ))) '' Sset
  have hMfin : Mset.Finite := hSfin.image _
  let D : Submodule ℝ (MvPolynomial (Fin n) ℝ) :=
    { carrier := {p | p.totalDegree ≤ k}
      add_mem' := fun {a b} ha hb =>
        (MvPolynomial.totalDegree_add a b).trans (max_le ha hb)
      zero_mem' := by simpa using Nat.zero_le k
      smul_mem' := fun c p hp =>
        (MvPolynomial.totalDegree_smul_le c p).trans hp }
  have hMD : Mset ⊆ (D : Set (MvPolynomial (Fin n) ℝ)) := by
    rintro _ ⟨s, hs, rfl⟩
    show (MvPolynomial.monomial s (1 : ℝ)).totalDegree ≤ k
    refine (MvPolynomial.totalDegree_monomial_le s 1).trans ?_
    have e1 : (s.sum fun _ => (id : ℕ → ℕ)) = ∑ i, s i :=
      Finsupp.sum_fintype _ _ (fun _ => rfl)
    have e2 : s.degree = ∑ i, s i := Finsupp.degree_eq_sum s
    rw [e1, ← e2]; exact hs
  let V : Submodule ℝ (MvPolynomial (Fin n) ℝ) := Submodule.span ℝ Mset
  haveI hVfin : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ hMfin
  have hVD : V ≤ D := Submodule.span_le.mpr hMD
  have hmemdeg : ∀ p : MvPolynomial (Fin n) ℝ, p ∈ V → p.totalDegree ≤ k :=
    fun p hp => hVD hp
  have hqmem : ∀ q : MvPolynomial (Fin n) ℝ, q.totalDegree ≤ k → q ∈ V := by
    intro q hq
    rw [q.as_sum]
    apply Submodule.sum_mem
    intro s hs
    have hsdeg : s.degree ≤ k := by
      have h1 : (s.sum fun _ e => e) ≤ q.totalDegree := MvPolynomial.le_totalDegree hs
      have e2 : s.degree = ∑ i, s i := Finsupp.degree_eq_sum s
      have e1 : (s.sum fun _ e => e) = ∑ i, s i :=
        Finsupp.sum_fintype _ _ (fun _ => rfl)
      rw [e2, ← e1]; exact h1.trans hq
    have hmono : MvPolynomial.monomial s (1 : ℝ) ∈ V :=
      Submodule.subset_span ⟨s, hsdeg, rfl⟩
    have hrw : MvPolynomial.monomial s (MvPolynomial.coeff s q)
        = (MvPolynomial.coeff s q) • MvPolynomial.monomial s (1 : ℝ) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [hrw]
    exact Submodule.smul_mem _ _ hmono
  let B : LinearMap.BilinForm ℝ V := B₀.domRestrict₁₂ V V
  have hBapp : ∀ p q : V, B p q =
      ∫ y, MvPolynomial.eval y (p : MvPolynomial (Fin n) ℝ) *
        MvPolynomial.eval y (q : MvPolynomial (Fin n) ℝ) ∂Q := by
    intro p q
    simp only [B, LinearMap.domRestrict₁₂_apply, B₀, LinearMap.mk₂_apply]
  have hnd : B.Nondegenerate := by
    apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
    apply LinearMap.BilinForm.separatingLeft_of_anisotropic
    intro p hp
    rw [LinearMap.BilinMap.toQuadraticMap_apply, hBapp] at hp
    have hnn : 0 ≤ fun y => MvPolynomial.eval y (p : MvPolynomial (Fin n) ℝ) *
        MvPolynomial.eval y (p : MvPolynomial (Fin n) ℝ) := by
      intro y; exact mul_self_nonneg _
    have hae := (integral_eq_zero_iff_of_nonneg hnn (hint _ _)).mp hp
    have hcont : Continuous (fun y => MvPolynomial.eval y (p : MvPolynomial (Fin n) ℝ) *
        MvPolynomial.eval y (p : MvPolynomial (Fin n) ℝ)) :=
      (mvpoly_continuous_eval _).mul (mvpoly_continuous_eval _)
    have heq : (fun y => MvPolynomial.eval y (p : MvPolynomial (Fin n) ℝ) *
        MvPolynomial.eval y (p : MvPolynomial (Fin n) ℝ)) = 0 :=
      (hcont.ae_eq_iff_eq (μ := Q) continuous_const).mp hae
    have hzero : (p : MvPolynomial (Fin n) ℝ) = 0 := by
      apply mvpoly_eval_zero_of_forall n
      intro y
      have := congrFun heq y
      simp only [Pi.zero_apply, MvPolynomial.eval_zero] at this ⊢
      exact mul_self_eq_zero.mp this
    exact Submodule.coe_eq_zero.mp hzero
  let G₀ : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun q => MvPolynomial.eval 0 q - ∫ y, MvPolynomial.eval y q ∂Q
      map_add' := by
        intro q₁ q₂
        simp only [MvPolynomial.eval_add]
        rw [integral_add (hpint q₁) (hpint q₂)]; ring
      map_smul' := by
        intro c q
        simp only [MvPolynomial.smul_eval, RingHom.id_apply, smul_eq_mul]
        rw [integral_const_mul]; ring }
  let G : V →ₗ[ℝ] ℝ := G₀.comp V.subtype
  let ρV : V := (LinearMap.BilinForm.toDual B hnd).symm G
  refine ⟨(ρV : MvPolynomial (Fin n) ℝ), ?_, ?_⟩
  · exact hmemdeg _ ρV.property
  · intro q hq
    have hqV : q ∈ V := hqmem q hq
    have hkey := LinearMap.BilinForm.apply_toDual_symm_apply
      (B := B) (hB := hnd) G ⟨q, hqV⟩
    rw [hBapp ρV ⟨q, hqV⟩] at hkey
    simpa only [G, G₀, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearMap.coe_mk, AddHom.coe_mk] using hkey

@[blueprint "lem:gsm-prob"
  (statement := /-- For every $n\in\mathbb N$, the Gaussian scale mixture $Q_n$ of \cref{def:gaussian-scale-mixture} is a probability measure. -/)
  (proof := /-- The standard Gaussian measure of \cref{def:standard-gaussian-measure} is a probability measure, and by \cref{def:isotropic-gaussian-measure} the isotropic Gaussian measure is a finite product of copies of it, hence also a probability measure; therefore so is their binary product. By \cref{lem:gsm-map-eq} the measure $Q_n$ is the pushforward of that product along a measurable map, and a pushforward of a probability measure along a measurable map is a probability measure. -/)
  (title := /-- The Gaussian scale mixture is a probability measure -/)
  (latexEnv := "lemma")]
lemma gsm_prob (n : ℕ) : IsProbabilityMeasure (gaussian_scale_mixture n) := by
  letI : IsProbabilityMeasure standard_gaussian_measure := by
    unfold standard_gaussian_measure; infer_instance
  letI : IsProbabilityMeasure (isotropic_gaussian_measure n) := by
    unfold isotropic_gaussian_measure; infer_instance
  rw [← gsm_map_eq n]
  exact Measure.isProbabilityMeasure_map (by fun_prop)

@[blueprint "lem:oc-integral"
  (statement := /-- Let $\Omega$ be a measurable space with measurable singletons and a distinguished origin, let $\alpha\in\mathbb R_{\geq0}$ with $\alpha\leq1$, let $Q$ be a measure on $\Omega$, and let $f:\Omega\to\mathbb R$ be $Q$-integrable. Then, for the origin contamination $P_\alpha$ of \cref{def:origin-contamination},
  \[
    \int_\Omega f\;dP_\alpha=(1-\alpha)\int_\Omega f\;dQ+\alpha f(0).
  \] -/)
  (proof := /-- By \cref{def:origin-contamination} the measure $P_\alpha$ is the sum of the scaled measures $(1-\alpha)Q$ and $\alpha\delta_0$, where truncated subtraction in $\mathbb R_{\geq0}$ agrees with ordinary subtraction because $\alpha\leq1$. The function $f$ is integrable for $Q$ by hypothesis and for $\delta_0$ because Dirac measures integrate every function, and integrability is preserved under scaling a measure by a finite constant. Hence the integral against a sum of measures splits as the sum of the integrals, and each scaled-measure integral is the corresponding scalar multiple. Finally the integral of $f$ against $\delta_0$ is $f(0)$. Combining these identities gives the displayed formula. -/)
  (title := /-- Integration against an origin contamination -/)
  (latexEnv := "lemma")]
lemma oc_integral {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Zero Ω] (α : NNReal) (hα : α ≤ 1) (Q : Measure Ω) (f : Ω → ℝ)
    (hf : Integrable f Q) :
    ∫ x, f x ∂(origin_contamination α Q) =
      (1 - (α : ℝ)) * ∫ x, f x ∂Q + (α : ℝ) * f 0 := by
  have h_one_sub : (↑(1 - α) : ENNReal).toReal = 1 - (α : ℝ) := by
    rw [ENNReal.coe_toReal, NNReal.coe_sub hα]; norm_num
  have h_alpha : (↑α : ENNReal).toReal = (α : ℝ) := ENNReal.coe_toReal α
  have hdirac : Integrable f (Measure.dirac 0) := integrable_dirac (by simp)
  rw [origin_contamination,
    integral_add_measure (hf.smul_measure (by simp)) (hdirac.smul_measure (by simp)),
    integral_smul_measure, integral_smul_measure, integral_dirac,
    h_one_sub, h_alpha, smul_eq_mul, smul_eq_mul]

@[blueprint "lem:oc-poly-integrable"
  (statement := /-- For every $n\in\mathbb N$, every $\alpha\in\mathbb R_{\geq0}$ and every polynomial $g\in\mathbb R[y_1,\dots,y_n]$, the evaluation $y\mapsto g(y)$ is integrable with respect to the origin contamination of \cref{def:origin-contamination} of the Gaussian scale mixture of \cref{def:gaussian-scale-mixture}. -/)
  (proof := /-- By \cref{def:origin-contamination} the measure is the sum of a scalar multiple of $Q_n$ and a scalar multiple of the Dirac mass at the origin. The evaluation of $g$ is integrable for $Q_n$ by \cref{lem:gsm-poly-integrable} and integrable for the Dirac mass because every function is Dirac-integrable; scaling a measure by a finite constant preserves integrability. Integrability for a finite sum of measures follows from integrability for each summand. -/)
  (title := /-- Integrability of polynomials under origin contamination -/)
  (latexEnv := "lemma")]
lemma oc_poly_integrable (n : ℕ) (α : NNReal) (g : MvPolynomial (Fin n) ℝ) :
    Integrable (fun y => MvPolynomial.eval y g)
      (origin_contamination α (gaussian_scale_mixture n)) := by
  rw [origin_contamination]
  refine Integrable.add_measure ?_ ?_
  · exact (gsm_poly_integrable n g).smul_measure (by simp)
  · exact (integrable_dirac (by simp)).smul_measure (by simp)

@[blueprint "lem:prod-poly-observable-integral"
  (statement := /-- Let $n,m\in\mathbb N$ and let $h_1,\dots,h_m\in\mathbb R[y_1,\dots,y_n]$. Then, with $Q_n$ as in \cref{def:gaussian-scale-mixture} and the product measure of \cref{def:iid-product-measure},
  \[
    \int\prod_{i=1}^m h_i(x_i)\;dQ_n^{\otimes m}
      =\prod_{i=1}^m\int h_i\;dQ_n.
  \] -/)
  (proof := /-- By \cref{lem:gsm-prob} the measure $Q_n$ is a probability measure, in particular $\sigma$-finite, and by \cref{def:iid-product-measure} the measure $Q_n^{\otimes m}$ is the product of $m$ copies of it. For a finite product of $\sigma$-finite probability measures, the integral of a product of functions of the separate coordinates factors as the product of the coordinatewise integrals, which is the assertion. -/)
  (title := /-- Factorization of product observables under a product measure -/)
  (latexEnv := "lemma")]
lemma prod_poly_observable_integral (n m : ℕ) (h : Fin m → MvPolynomial (Fin n) ℝ) :
    ∫ x, ∏ i, MvPolynomial.eval (x i) (h i)
        ∂(iid_product_measure m (gaussian_scale_mixture n)) =
      ∏ i, ∫ y, MvPolynomial.eval y (h i) ∂(gaussian_scale_mixture n) := by
  haveI := gsm_prob n
  unfold iid_product_measure
  haveI : ∀ i : Fin m, SigmaFinite (gaussian_scale_mixture n) := fun _ => inferInstance
  exact integral_fintype_prod_eq_prod (fun i y => MvPolynomial.eval y (h i))

@[blueprint "lem:prod-poly-observable-integrable"
  (statement := /-- Let $n,m\in\mathbb N$ and let $h_1,\dots,h_m\in\mathbb R[y_1,\dots,y_n]$. Then $x\mapsto\prod_{i=1}^m h_i(x_i)$ is integrable with respect to the product measure $Q_n^{\otimes m}$ of \cref{def:iid-product-measure,def:gaussian-scale-mixture}. -/)
  (proof := /-- By \cref{lem:gsm-prob} each marginal $Q_n$ is a probability measure, hence $\sigma$-finite, and by \cref{def:iid-product-measure} the measure $Q_n^{\otimes m}$ is their product. Each factor $y\mapsto h_i(y)$ is integrable for $Q_n$ by \cref{lem:gsm-poly-integrable}. A product of coordinatewise integrable functions is integrable for a finite product of probability measures. -/)
  (title := /-- Integrability of product observables -/)
  (latexEnv := "lemma")]
lemma prod_poly_observable_integrable (n m : ℕ) (h : Fin m → MvPolynomial (Fin n) ℝ) :
    Integrable (fun x => ∏ i, MvPolynomial.eval (x i) (h i))
      (iid_product_measure m (gaussian_scale_mixture n)) := by
  haveI := gsm_prob n
  unfold iid_product_measure
  haveI : ∀ i : Fin m, SigmaFinite (gaussian_scale_mixture n) := fun _ => inferInstance
  exact Integrable.fintype_prod (fun i => gsm_poly_integrable n (h i))

@[blueprint "lem:oc-prob"
  (statement := /-- For every $n\in\mathbb N$ and every $\alpha\in\mathbb R_{\geq0}$ with $\alpha\leq1$, the origin contamination of \cref{def:origin-contamination} of the Gaussian scale mixture of \cref{def:gaussian-scale-mixture} is a probability measure. -/)
  (proof := /-- By \cref{lem:gsm-prob} the measure $Q_n$ has total mass $1$, and the Dirac mass at the origin has total mass $1$. Evaluating the defining sum of \cref{def:origin-contamination} on the whole space therefore gives total mass $(1-\alpha)+\alpha$, where the truncated difference $1-\alpha$ agrees with the ordinary one because $\alpha\leq1$. Hence the total mass is $1$. -/)
  (title := /-- Origin contamination of a probability measure is a probability measure -/)
  (latexEnv := "lemma")]
lemma oc_prob (n : ℕ) (α : NNReal) (hα : α ≤ 1) :
    IsProbabilityMeasure (origin_contamination α (gaussian_scale_mixture n)) := by
  haveI := gsm_prob n
  unfold origin_contamination
  constructor
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ, measure_univ]
  simp only [smul_eq_mul, mul_one]
  rw [← ENNReal.coe_add, tsub_add_cancel_of_le hα]
  simp

@[blueprint "lem:prod-obs-integral-oc"
  (statement := /-- Let $n,m\in\mathbb N$, let $\alpha\in\mathbb R_{\geq0}$ with $\alpha\leq1$, and let $g_1,\dots,g_m\in\mathbb R[y_1,\dots,y_n]$. Writing $P$ for the origin contamination of \cref{def:origin-contamination} of the measure of \cref{def:gaussian-scale-mixture},
  \[
    \int\prod_{i=1}^m g_i(x_i)\;dP^{\otimes m}=\prod_{i=1}^m\int g_i\;dP.
  \] -/)
  (proof := /-- By \cref{lem:oc-prob} the measure $P$ is a probability measure, in particular $\sigma$-finite, and by \cref{def:iid-product-measure} the measure $P^{\otimes m}$ is the product of $m$ copies of it. For a finite product of $\sigma$-finite probability measures, the integral of a product of functions of the separate coordinates equals the product of the coordinatewise integrals. -/)
  (title := /-- Factorization of product observables under contaminated products -/)
  (latexEnv := "lemma")]
lemma prod_obs_integral_oc (n m : ℕ) (α : NNReal) (hα : α ≤ 1)
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    ∫ x, ∏ i, MvPolynomial.eval (x i) (g i)
        ∂(iid_product_measure m (origin_contamination α (gaussian_scale_mixture n))) =
      ∏ i, ∫ y, MvPolynomial.eval y (g i)
        ∂(origin_contamination α (gaussian_scale_mixture n)) := by
  haveI := oc_prob n α hα
  unfold iid_product_measure
  haveI : ∀ i : Fin m,
      SigmaFinite (origin_contamination α (gaussian_scale_mixture n)) := fun _ => inferInstance
  exact integral_fintype_prod_eq_prod (fun i y => MvPolynomial.eval y (g i))

@[blueprint "lem:prod-poly-observable-integrable-oc"
  (statement := /-- Let $n,m\in\mathbb N$, let $\alpha\in\mathbb R_{\geq0}$ with $\alpha\leq1$, and let $h_1,\dots,h_m\in\mathbb R[y_1,\dots,y_n]$. Then $x\mapsto\prod_{i=1}^m h_i(x_i)$ is integrable with respect to $P^{\otimes m}$, where $P$ is the origin contamination of \cref{def:origin-contamination} of the measure of \cref{def:gaussian-scale-mixture}. -/)
  (proof := /-- By \cref{lem:oc-prob} the measure $P$ is a probability measure, hence $\sigma$-finite, and by \cref{def:iid-product-measure} the measure $P^{\otimes m}$ is the product of $m$ copies of it. Each factor $y\mapsto h_i(y)$ is $P$-integrable by \cref{lem:oc-poly-integrable}, and a product of coordinatewise integrable functions is integrable for a finite product of probability measures. -/)
  (title := /-- Integrability of product observables under contaminated products -/)
  (latexEnv := "lemma")]
lemma prod_poly_observable_integrable_oc (n m : ℕ) (α : NNReal) (hα : α ≤ 1)
    (h : Fin m → MvPolynomial (Fin n) ℝ) :
    Integrable (fun x => ∏ i, MvPolynomial.eval (x i) (h i))
      (iid_product_measure m (origin_contamination α (gaussian_scale_mixture n))) := by
  haveI := oc_prob n α hα
  unfold iid_product_measure
  haveI : ∀ i : Fin m,
      SigmaFinite (origin_contamination α (gaussian_scale_mixture n)) := fun _ => inferInstance
  exact Integrable.fintype_prod (fun i => oc_poly_integrable n α (h i))

@[blueprint "lem:sample-obs-monomial-factor"
  (statement := /-- Let $n,m\in\mathbb N$, let $s$ be a finitely supported exponent on the index set $[m]\times[n]$ and let $c\in\mathbb R$. Then the observable of \cref{def:sample-polynomial-observable} attached to the monomial $c\,x^{s}$ satisfies, for every sample tuple $x$,
  \[
    (c\,x^{s})(x)=c\prod_{i=1}^m \bigl(y\mapsto y^{s(i,\cdot)}\bigr)(x_i),
  \]
  where $s(i,\cdot)$ denotes the exponent in the $i$-th block of variables. -/)
  (proof := /-- By \cref{def:sample-polynomial-observable} the observable is the evaluation of the monomial at the assignment sending the variable indexed by $(i,j)$ to the $j$-th coordinate of the $i$-th sample. Evaluating a monomial yields the coefficient $c$ times the product of the assigned values raised to the corresponding exponents. Splitting that product over the index set $[m]\times[n]$ into the iterated product over $i$ and then $j$, the inner product over $j$ is exactly the evaluation of the monomial with exponent $s(i,\cdot)$ and coefficient $1$ at the $i$-th sample, since currying $s$ at $i$ reproduces the exponents $j\mapsto s(i,j)$. -/)
  (title := /-- Factorization of a monomial observable across samples -/)
  (latexEnv := "lemma")]
lemma sample_obs_monomial_factor (n m : ℕ) (s : (Fin m × Fin n) →₀ ℕ) (c : ℝ) :
    sample_polynomial_observable (MvPolynomial.monomial s c)
      = fun x : Fin m → Fin n → ℝ =>
        c * ∏ i, MvPolynomial.eval (x i) (MvPolynomial.monomial (s.curry i) (1 : ℝ)) := by
  funext x
  unfold sample_polynomial_observable
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp),
    Fintype.prod_prod_type]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun _ => by simp)]
  apply Finset.prod_congr rfl
  intro j _
  rw [Finsupp.curry_apply]

@[blueprint "lem:sample-obs-continuous"
  (statement := /-- For all $n,m\in\mathbb N$ and every $p\in\mathbb R[x_{i,j}]$, the observable of \cref{def:sample-polynomial-observable} is a continuous function of the sample tuple. -/)
  (proof := /-- By \cref{def:sample-polynomial-observable} the observable is the composition of the evaluation of $p$ with the map sending a sample tuple $x$ to the assignment $(i,j)\mapsto x_i(j)$. The latter map is continuous, since each of its coordinates is a coordinate projection. The evaluation of $p$ is continuous by \cref{lem:mvpoly-continuous-eval}, and a composition of continuous maps is continuous. -/)
  (title := /-- Continuity of polynomial observables -/)
  (latexEnv := "lemma")]
lemma sample_obs_continuous (n m : ℕ) (p : MvPolynomial (Fin m × Fin n) ℝ) :
    Continuous (sample_polynomial_observable p) := by
  unfold sample_polynomial_observable
  have hc : Continuous (fun x : Fin m → Fin n → ℝ =>
      (fun ij : Fin m × Fin n => x ij.1 ij.2)) := by fun_prop
  exact (mvpoly_continuous_eval p).comp hc

@[blueprint "lem:sample-obs-integrable-gsm"
  (statement := /-- For all $n,m\in\mathbb N$ and every $p\in\mathbb R[x_{i,j}]$, the observable of \cref{def:sample-polynomial-observable} is integrable with respect to the product measure $Q_n^{\otimes m}$ of \cref{def:iid-product-measure,def:gaussian-scale-mixture}. -/)
  (proof := /-- Expand $p$ as the finite sum of its monomials over its support. Since evaluation is additive, the observable of the sum is the pointwise sum of the observables of the monomials, so it suffices to treat a single monomial. For a monomial with exponent $s$ and coefficient $c$, \cref{lem:sample-obs-monomial-factor} identifies the observable with $c$ times a product of one polynomial per sample, which is integrable by \cref{lem:prod-poly-observable-integrable}; multiplying by the constant $c$ preserves integrability. Finally a finite sum of integrable functions is integrable. -/)
  (title := /-- Integrability of polynomial observables -/)
  (latexEnv := "lemma")]
lemma sample_obs_integrable_gsm (n m : ℕ) (p : MvPolynomial (Fin m × Fin n) ℝ) :
    Integrable (sample_polynomial_observable p)
      (iid_product_measure m (gaussian_scale_mixture n)) := by
  rw [p.as_sum]
  have hsum : (sample_polynomial_observable
        (∑ s ∈ p.support, MvPolynomial.monomial s (MvPolynomial.coeff s p)))
      = fun x => ∑ s ∈ p.support,
          sample_polynomial_observable (MvPolynomial.monomial s (MvPolynomial.coeff s p)) x := by
    funext x; unfold sample_polynomial_observable; rw [MvPolynomial.eval_sum]
  rw [hsum]
  apply integrable_finset_sum
  intro s hs
  rw [sample_obs_monomial_factor]
  exact Integrable.const_mul
    (prod_poly_observable_integrable n m (fun i => MvPolynomial.monomial (s.curry i) 1)) _

@[blueprint "lem:reproduce-single"
  (statement := /-- Let $n,k\in\mathbb N$, let $\alpha\in\mathbb R_{\geq0}$ with $\alpha\leq1$, write $Q=Q_n$ for the measure of \cref{def:gaussian-scale-mixture} and $P$ for its origin contamination of \cref{def:origin-contamination}, and let $\rho\in\mathbb R[y_1,\dots,y_n]$ satisfy
  \[
    \int\rho\,q\;dQ=q(0)-\int q\;dQ
    \qquad\text{for all }q\text{ with }\deg q\leq k.
  \]
  Then for every $q$ with $\deg q\leq k$,
  \[
    \int q\;dP=\int (1+\alpha\rho)\,q\;dQ.
  \] -/)
  (proof := /-- The functions $y\mapsto q(y)$ and $y\mapsto\rho(y)q(y)$ are $Q$-integrable by \cref{lem:gsm-poly-integrable} and \cref{lem:gsm-mul-integrable} respectively. By \cref{lem:oc-integral},
  \[
    \int q\;dP=(1-\alpha)\int q\;dQ+\alpha\,q(0).
  \]
  On the other side, evaluation is a ring homomorphism, so $(1+\alpha\rho)q$ evaluates pointwise to $q(y)+\alpha\,\rho(y)q(y)$. Splitting the integral of this sum, which is legitimate by the two integrability facts, and pulling the constant $\alpha$ out gives
  \[
    \int(1+\alpha\rho)q\;dQ=\int q\;dQ+\alpha\int\rho\,q\;dQ
      =\int q\;dQ+\alpha\Bigl(q(0)-\int q\;dQ\Bigr),
  \]
  where the representative hypothesis was applied to $q$. The two displayed right-hand sides coincide, which proves the identity. -/)
  (title := /-- Likelihood-ratio reproduction of the contaminated expectation -/)
  (latexEnv := "lemma")]
lemma reproduce_single (n k : ℕ) (α : NNReal) (hα : α ≤ 1)
    (ρ : MvPolynomial (Fin n) ℝ)
    (hρrep : ∀ q : MvPolynomial (Fin n) ℝ, q.totalDegree ≤ k →
      ∫ y, MvPolynomial.eval y ρ * MvPolynomial.eval y q ∂(gaussian_scale_mixture n)
        = MvPolynomial.eval 0 q - ∫ y, MvPolynomial.eval y q ∂(gaussian_scale_mixture n))
    (q : MvPolynomial (Fin n) ℝ) (hq : q.totalDegree ≤ k) :
    ∫ y, MvPolynomial.eval y q ∂(origin_contamination α (gaussian_scale_mixture n))
      = ∫ y, MvPolynomial.eval y ((1 + (α : ℝ) • ρ) * q)
          ∂(gaussian_scale_mixture n) := by
  have hintq : Integrable (fun y => MvPolynomial.eval y q) (gaussian_scale_mixture n) :=
    gsm_poly_integrable n q
  have hintρq : Integrable (fun y => MvPolynomial.eval y ρ * MvPolynomial.eval y q)
      (gaussian_scale_mixture n) := gsm_mul_integrable n ρ q
  rw [oc_integral α hα _ _ hintq]
  have hexpand : (fun y => MvPolynomial.eval y ((1 + (α : ℝ) • ρ) * q))
      = fun y => MvPolynomial.eval y q
          + (α : ℝ) * (MvPolynomial.eval y ρ * MvPolynomial.eval y q) := by
    funext y
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_add, map_one,
      MvPolynomial.smul_eval]
    ring
  rw [hexpand]
  rw [integral_add hintq (hintρq.const_mul _), integral_const_mul,
    hρrep q hq]
  ring

@[blueprint "lem:curry-monomial-degree-le"
  (statement := /-- Let $n,m,k\in\mathbb N$ and let $s$ be a finitely supported exponent on $[m]\times[n]$ whose total degree $\sum_{i,j}s(i,j)$ is at most $k$. Then for every $i\in[m]$ the monomial with exponent $s(i,\cdot)$ and coefficient $1$ has total degree at most $k$. -/)
  (proof := /-- The total degree of a monomial is at most the sum of its exponents, so it suffices to bound $\sum_j s(i,j)$ by $k$. Writing the total degree of $s$ as the double sum $\sum_{i'}\sum_j s(i',j)$ over the product index set, every inner sum is a nonnegative term of that double sum, hence the single term indexed by $i$ is at most the whole sum. Combining with the hypothesis that the whole sum is at most $k$ gives the bound. -/)
  (title := /-- Degree bound for the blockwise factors of a monomial -/)
  (latexEnv := "lemma")]
lemma curry_monomial_degree_le (n m k : ℕ) (s : (Fin m × Fin n) →₀ ℕ)
    (hs : (s.sum fun _ e => e) ≤ k) (i : Fin m) :
    (MvPolynomial.monomial (s.curry i) (1 : ℝ)).totalDegree ≤ k := by
  refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
  have e1 : (s.sum fun _ e => e) = ∑ ij : Fin m × Fin n, s ij :=
    Finsupp.sum_fintype _ _ (fun _ => rfl)
  have e2 : ((s.curry i).sum fun _ => (id : ℕ → ℕ)) = ∑ j, s (i, j) := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finsupp.curry_apply]; rfl
  rw [e2]; rw [e1] at hs
  refine le_trans ?_ hs
  rw [Fintype.sum_prod_type]
  exact Finset.single_le_sum (f := fun i' => ∑ j, s (i', j))
    (fun _ _ => Finset.sum_nonneg (fun _ _ => Nat.zero_le _)) (Finset.mem_univ i)

@[blueprint "lem:weight-monomial-observable"
  (statement := /-- Let $n,m\in\mathbb N$, let $w\in\mathbb R[y_1,\dots,y_n]$, let $s$ be a finitely supported exponent on $[m]\times[n]$, let $c\in\mathbb R$ and let $x$ be a sample tuple. Writing $w^{(i)}$ for the polynomial obtained from $w$ by renaming its variables into the $i$-th block, the observable of \cref{def:sample-polynomial-observable} satisfies
  \[
    \Bigl(\prod_{i=1}^m w^{(i)}\cdot c\,x^{s}\Bigr)(x)
      = c\prod_{i=1}^m \bigl(w\cdot y^{s(i,\cdot)}\bigr)(x_i).
  \] -/)
  (proof := /-- By \cref{def:sample-polynomial-observable} the observable is the evaluation of the product at the assignment $(i,j)\mapsto x_i(j)$. Evaluation is multiplicative, so the value is the evaluation of $\prod_i w^{(i)}$ times the evaluation of the monomial. The evaluation of the monomial is $c$ times the product over $[m]\times[n]$ of the assigned values raised to the exponents, and splitting that product into the iterated product over $i$ then $j$ identifies the $i$-th inner factor as the evaluation of $y^{s(i,\cdot)}$ at $x_i$, using that currying $s$ at $i$ gives $j\mapsto s(i,j)$. Likewise evaluation commutes with the finite product $\prod_i w^{(i)}$, and evaluating a renamed polynomial equals evaluating $w$ at the composed assignment, which for the $i$-th block is $x_i$. Grouping the $i$-th factors and using multiplicativity of evaluation once more gives the displayed identity. -/)
  (title := /-- Factorization of a weighted monomial observable -/)
  (latexEnv := "lemma")]
lemma weight_monomial_observable (n m : ℕ) (w : MvPolynomial (Fin n) ℝ)
    (s : (Fin m × Fin n) →₀ ℕ) (c : ℝ) (x : Fin m → Fin n → ℝ) :
    sample_polynomial_observable
        ((∏ i, MvPolynomial.rename (fun j => (i, j)) w) * MvPolynomial.monomial s c) x
      = c * ∏ i, MvPolynomial.eval (x i) (w * MvPolynomial.monomial (s.curry i) 1) := by
  unfold sample_polynomial_observable
  rw [MvPolynomial.eval_mul, map_prod, MvPolynomial.eval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => by simp), Fintype.prod_prod_type,
    show ∀ a b : ℝ, a * (c * b) = c * (a * b) from fun a b => by ring,
    ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_rename, MvPolynomial.eval_monomial,
    one_mul, Finsupp.prod_fintype _ _ (fun _ => by simp)]
  refine congr_arg₂ (· * ·) rfl ?_
  apply Finset.prod_congr rfl
  intro j _
  rw [Finsupp.curry_apply]

@[blueprint "lem:weight-gap-identity"
  (statement := /-- Let $n,m,k\in\mathbb N$, let $\alpha\in\mathbb R_{\geq0}$ with $\alpha\leq1$, write $Q=Q_n$ and let $P$ be its origin contamination of \cref{def:origin-contamination}. Let $\rho\in\mathbb R[y_1,\dots,y_n]$ satisfy
  \[
    \int q\;dP=\int(1+\alpha\rho)\,q\;dQ
    \qquad\text{for all }q\text{ with }\deg q\leq k,
  \]
  and let $p\in\mathbb R[x_{i,j}]$ with $\deg p\leq k$. Writing $W=\prod_{i=1}^m(1+\alpha\rho)^{(i)}$ for the product over samples of the renamed weight, the expectations of \cref{def:sample-polynomial-expectation} satisfy
  \[
    \mathbb E_{P^{\otimes m}}[p]=\mathbb E_{Q^{\otimes m}}[W\cdot p].
  \] -/)
  (proof := /-- Expand $p$ as the finite sum of its monomials over its support and distribute $W$ over that sum. Since evaluation is additive, both observables are the corresponding finite sums of monomial observables. Each summand is integrable, on the left by \cref{lem:sample-obs-monomial-factor} together with \cref{lem:prod-poly-observable-integrable-oc}, and on the right by \cref{lem:weight-monomial-observable} together with \cref{lem:prod-poly-observable-integrable}, so both integrals split as finite sums and it suffices to match them monomialwise.

  Fix a monomial of $p$ with exponent $s$ and coefficient $c$. Its total degree $\sum_{i,j}s(i,j)$ is at most $\deg p\leq k$. By \cref{lem:sample-obs-monomial-factor} the left observable equals $c$ times the product over samples of the blockwise monomials, and by \cref{lem:weight-monomial-observable} the right observable equals $c$ times the product over samples of the weighted blockwise monomials. Pulling the constant $c$ out of both integrals and factoring the products by \cref{lem:prod-obs-integral-oc} on the left and \cref{lem:prod-poly-observable-integral} on the right, the claim reduces to the coordinatewise identity
  \[
    \int y^{s(i,\cdot)}\;dP=\int(1+\alpha\rho)\,y^{s(i,\cdot)}\;dQ
  \]
  for each $i$. Each blockwise monomial has total degree at most $k$ by \cref{lem:curry-monomial-degree-le}, so this is exactly the hypothesis on $\rho$ applied to it. -/)
  (title := /-- Weighted representation of the contaminated sample expectation -/)
  (latexEnv := "lemma")]
lemma weight_gap_identity (n m k : ℕ) (α : NNReal) (hα : α ≤ 1)
    (ρ : MvPolynomial (Fin n) ℝ)
    (hrep : ∀ q : MvPolynomial (Fin n) ℝ, q.totalDegree ≤ k →
      ∫ y, MvPolynomial.eval y q ∂(origin_contamination α (gaussian_scale_mixture n))
        = ∫ y, MvPolynomial.eval y ((1 + (α : ℝ) • ρ) * q) ∂(gaussian_scale_mixture n))
    (p : MvPolynomial (Fin m × Fin n) ℝ) (hpdeg : p.totalDegree ≤ k) :
    sample_polynomial_expectation (origin_contamination α (gaussian_scale_mixture n)) p
      = sample_polynomial_expectation (gaussian_scale_mixture n)
          ((∏ i, MvPolynomial.rename (fun j => (i, j)) (1 + (α : ℝ) • ρ)) * p) := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [Finset.mul_sum]
  unfold sample_polynomial_expectation
  have hobsL : (sample_polynomial_observable
        (∑ s ∈ p.support, MvPolynomial.monomial s (MvPolynomial.coeff s p)))
      = fun x => ∑ s ∈ p.support,
          sample_polynomial_observable (MvPolynomial.monomial s (MvPolynomial.coeff s p)) x := by
    funext x; unfold sample_polynomial_observable; rw [MvPolynomial.eval_sum]
  have hobsR : (sample_polynomial_observable
        (∑ s ∈ p.support,
          (∏ i, MvPolynomial.rename (fun j => (i, j)) (1 + (α : ℝ) • ρ)) *
            MvPolynomial.monomial s (MvPolynomial.coeff s p)))
      = fun x => ∑ s ∈ p.support,
          sample_polynomial_observable
            ((∏ i, MvPolynomial.rename (fun j => (i, j)) (1 + (α : ℝ) • ρ)) *
              MvPolynomial.monomial s (MvPolynomial.coeff s p)) x := by
    funext x; unfold sample_polynomial_observable; rw [MvPolynomial.eval_sum]
  rw [hobsL, hobsR]
  rw [integral_finset_sum _ (fun s hs => ?_), integral_finset_sum _ (fun s hs => ?_)]
  · apply Finset.sum_congr rfl
    intro s hs
    have hsk : (s.sum fun _ e => e) ≤ k :=
      (MvPolynomial.le_totalDegree hs).trans hpdeg
    have hmono := weight_monomial_observable n m (1 + (α : ℝ) • ρ) s (MvPolynomial.coeff s p)
    rw [sample_obs_monomial_factor]
    simp_rw [hmono]
    rw [integral_const_mul, integral_const_mul,
      prod_obs_integral_oc n m α hα, prod_poly_observable_integral]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    exact hrep _ (curry_monomial_degree_le n m k s hsk i)
  · have hfun : (sample_polynomial_observable
        ((∏ i, MvPolynomial.rename (fun j => (i, j)) (1 + (α : ℝ) • ρ)) *
          MvPolynomial.monomial s (MvPolynomial.coeff s p)))
      = fun x => (MvPolynomial.coeff s p) *
          ∏ i, MvPolynomial.eval (x i)
            ((1 + (α : ℝ) • ρ) * MvPolynomial.monomial (s.curry i) 1) := by
      funext x
      exact weight_monomial_observable n m (1 + (α : ℝ) • ρ) s (MvPolynomial.coeff s p) x
    rw [hfun]
    exact Integrable.const_mul
      (prod_poly_observable_integrable n m
        (fun i => (1 + (α : ℝ) • ρ) * MvPolynomial.monomial (s.curry i) 1)) _
  · rw [sample_obs_monomial_factor]
    exact Integrable.const_mul
      (prod_poly_observable_integrable_oc n m α hα
        (fun i => MvPolynomial.monomial (s.curry i) 1)) _

@[blueprint "lem:prod-rename-observable"
  (statement := /-- Let $n,m\in\mathbb N$, let $w\in\mathbb R[y_1,\dots,y_n]$ and let $x$ be a sample tuple. Writing $w^{(i)}$ for $w$ with its variables renamed into the $i$-th block, the observable of \cref{def:sample-polynomial-observable} satisfies
  \[
    \Bigl(\prod_{i=1}^m w^{(i)}\Bigr)(x)=\prod_{i=1}^m w(x_i).
  \] -/)
  (proof := /-- By \cref{def:sample-polynomial-observable} the observable is the evaluation of $\prod_i w^{(i)}$ at the assignment $(i,j)\mapsto x_i(j)$. Evaluation is a ring homomorphism, so it commutes with the finite product, reducing the claim to the corresponding statement for each factor. Evaluating a renamed polynomial equals evaluating $w$ at the composition of the assignment with the renaming, and for the $i$-th block that composition is $j\mapsto x_i(j)$, that is $x_i$. -/)
  (title := /-- Product of renamed polynomials as a product observable -/)
  (latexEnv := "lemma")]
lemma prod_rename_observable (n m : ℕ) (w : MvPolynomial (Fin n) ℝ)
    (x : Fin m → Fin n → ℝ) :
    sample_polynomial_observable
        (∏ i, MvPolynomial.rename (fun j => (i, j)) w) x
      = ∏ i, MvPolynomial.eval (x i) w := by
  unfold sample_polynomial_observable
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [MvPolynomial.eval_rename]
  rfl

@[blueprint "lem:sample-obs-memLp-two"
  (statement := /-- For all $n,m\in\mathbb N$ and every $p\in\mathbb R[x_{i,j}]$, the observable of \cref{def:sample-polynomial-observable} lies in $L^2(Q_n^{\otimes m})$, for $Q_n^{\otimes m}$ as in \cref{def:iid-product-measure,def:gaussian-scale-mixture}. -/)
  (proof := /-- A real-valued strongly measurable function lies in $L^2$ exactly when its square is integrable. The observable is continuous, hence strongly measurable, by \cref{lem:sample-obs-continuous}. The observable of $p\cdot p$ is integrable by \cref{lem:sample-obs-integrable-gsm}, and since evaluation is multiplicative that observable equals the pointwise square of the observable of $p$. Hence the square is integrable and the membership follows. -/)
  (title := /-- Square integrability of polynomial observables -/)
  (latexEnv := "lemma")]
lemma sample_obs_memLp_two (n m : ℕ) (p : MvPolynomial (Fin m × Fin n) ℝ) :
    MemLp (sample_polynomial_observable p) 2
      (iid_product_measure m (gaussian_scale_mixture n)) := by
  rw [memLp_two_iff_integrable_sq (sample_obs_continuous n m p).aestronglyMeasurable]
  refine (sample_obs_integrable_gsm n m (p * p)).congr
    (Filter.Eventually.of_forall ?_)
  intro x
  show MvPolynomial.eval (fun ij => x ij.1 ij.2) (p * p)
      = (sample_polynomial_observable p x) ^ 2
  unfold sample_polynomial_observable
  rw [MvPolynomial.eval_mul, sq]

@[blueprint "lem:prod-obs-expectation-gsm"
  (statement := /-- Let $n,m\in\mathbb N$ and $w\in\mathbb R[y_1,\dots,y_n]$, and write $w^{(i)}$ for $w$ renamed into the $i$-th block. Then the expectation of \cref{def:sample-polynomial-expectation} satisfies
  \[
    \mathbb E_{Q_n^{\otimes m}}\Bigl[\prod_{i=1}^m w^{(i)}\Bigr]
      =\Bigl(\int w\;dQ_n\Bigr)^m.
  \] -/)
  (proof := /-- By \cref{def:sample-polynomial-expectation} the left side is the integral of the corresponding observable, which by \cref{lem:prod-rename-observable} is the product $x\mapsto\prod_i w(x_i)$. By \cref{lem:prod-poly-observable-integral} that integral factors as the product over $i$ of the integrals $\int w\;dQ_n$. All $m$ factors are equal, so the product is the $m$-th power. -/)
  (title := /-- Expectation of a product weight under the null product measure -/)
  (latexEnv := "lemma")]
lemma prod_obs_expectation_gsm (n m : ℕ) (w : MvPolynomial (Fin n) ℝ) :
    sample_polynomial_expectation (gaussian_scale_mixture n)
        (∏ i : Fin m, MvPolynomial.rename (fun j => (i, j)) w)
      = (∫ y, MvPolynomial.eval y w ∂(gaussian_scale_mixture n)) ^ m := by
  unfold sample_polynomial_expectation
  simp only [prod_rename_observable]
  rw [prod_poly_observable_integral, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

@[blueprint "lem:prod-obs-expectation-oc"
  (statement := /-- Let $n,m\in\mathbb N$, let $\alpha\in\mathbb R_{\geq0}$ with $\alpha\leq1$, let $w\in\mathbb R[y_1,\dots,y_n]$, and let $P$ be the origin contamination of \cref{def:origin-contamination} of the measure of \cref{def:gaussian-scale-mixture}. Writing $w^{(i)}$ for $w$ renamed into the $i$-th block, the expectation of \cref{def:sample-polynomial-expectation} satisfies
  \[
    \mathbb E_{P^{\otimes m}}\Bigl[\prod_{i=1}^m w^{(i)}\Bigr]
      =\Bigl(\int w\;dP\Bigr)^m.
  \] -/)
  (proof := /-- By \cref{def:sample-polynomial-expectation} the left side is the integral of the corresponding observable, which by \cref{lem:prod-rename-observable} equals $x\mapsto\prod_i w(x_i)$. By \cref{lem:prod-obs-integral-oc} that integral factors as the product over $i$ of the integrals $\int w\;dP$, and since all $m$ factors coincide the product is the $m$-th power. -/)
  (title := /-- Expectation of a product weight under the contaminated product measure -/)
  (latexEnv := "lemma")]
lemma prod_obs_expectation_oc (n m : ℕ) (α : NNReal) (hα : α ≤ 1)
    (w : MvPolynomial (Fin n) ℝ) :
    sample_polynomial_expectation
        (origin_contamination α (gaussian_scale_mixture n))
        (∏ i : Fin m, MvPolynomial.rename (fun j => (i, j)) w)
      = (∫ y, MvPolynomial.eval y w
          ∂(origin_contamination α (gaussian_scale_mixture n))) ^ m := by
  unfold sample_polynomial_expectation
  simp only [prod_rename_observable]
  rw [prod_obs_integral_oc n m α hα, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

@[blueprint "lem:prod-obs-sq-integral-gsm"
  (statement := /-- Let $n,m\in\mathbb N$ and $w\in\mathbb R[y_1,\dots,y_n]$, and write $w^{(i)}$ for $w$ renamed into the $i$-th block. Then, for the observable of \cref{def:sample-polynomial-observable} and the measure of \cref{def:iid-product-measure,def:gaussian-scale-mixture},
  \[
    \int\Bigl(\prod_{i=1}^m w^{(i)}\Bigr)^2\;dQ_n^{\otimes m}
      =\Bigl(\int w^2\;dQ_n\Bigr)^m.
  \] -/)
  (proof := /-- By \cref{lem:prod-rename-observable} the observable equals $x\mapsto\prod_i w(x_i)$, so its square is $\prod_i w(x_i)^2$; distributing the square over the finite product and using multiplicativity of evaluation, this is the product observable attached to the family constantly equal to $w\cdot w$. By \cref{lem:prod-poly-observable-integral} the integral factors as the product over $i$ of $\int w\cdot w\;dQ_n$, and that integral equals $\int w^2\;dQ_n$ because evaluation is multiplicative. All $m$ factors agree, giving the $m$-th power. -/)
  (title := /-- Second moment of a product weight -/)
  (latexEnv := "lemma")]
lemma prod_obs_sq_integral_gsm (n m : ℕ) (w : MvPolynomial (Fin n) ℝ) :
    (∫ x, (sample_polynomial_observable
        (∏ i : Fin m, MvPolynomial.rename (fun j => (i, j)) w) x) ^ 2
        ∂(iid_product_measure m (gaussian_scale_mixture n)))
      = (∫ y, (MvPolynomial.eval y w) ^ 2 ∂(gaussian_scale_mixture n)) ^ m := by
  have hfun : (fun x : Fin m → Fin n → ℝ =>
      (sample_polynomial_observable
        (∏ i : Fin m, MvPolynomial.rename (fun j => (i, j)) w) x) ^ 2)
      = fun x => ∏ i, MvPolynomial.eval (x i) (w * w) := by
    funext x
    rw [prod_rename_observable, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [MvPolynomial.eval_mul, sq]
  rw [hfun, prod_poly_observable_integral]
  have hsq : (∫ y, MvPolynomial.eval y (w * w) ∂(gaussian_scale_mixture n))
      = ∫ y, (MvPolynomial.eval y w) ^ 2 ∂(gaussian_scale_mixture n) := by
    apply integral_congr_ae
    filter_upwards with y
    rw [MvPolynomial.eval_mul, sq]
  simp only [hsq]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

@[blueprint "lem:iid-gsm-isProbabilityMeasure"
  (statement := /-- For all $n,m\in\mathbb N$, the product measure $Q_n^{\otimes m}$ of \cref{def:iid-product-measure,def:gaussian-scale-mixture} is a probability measure. -/)
  (proof := /-- By \cref{lem:gsm-prob} the marginal $Q_n$ is a probability measure, and by \cref{def:iid-product-measure} the measure $Q_n^{\otimes m}$ is the product of $m$ copies of it. A finite product of probability measures is a probability measure. -/)
  (title := /-- The i.i.d. product of the null measure is a probability measure -/)
  (latexEnv := "lemma")]
lemma iid_gsm_isProbabilityMeasure (n m : ℕ) :
    IsProbabilityMeasure (iid_product_measure m (gaussian_scale_mixture n)) := by
  haveI := gsm_prob n
  unfold iid_product_measure
  infer_instance

@[blueprint "lem:gsm-sq-integrable"
  (statement := /-- For every $n\in\mathbb N$ and every $g\in\mathbb R[y_1,\dots,y_n]$, the function $y\mapsto g(y)^2$ is integrable with respect to the Gaussian scale mixture of \cref{def:gaussian-scale-mixture}. -/)
  (proof := /-- By \cref{lem:gsm-mul-integrable} the function $y\mapsto g(y)g(y)$ is integrable for $Q_n$. This function agrees pointwise with $y\mapsto g(y)^2$, so integrability transfers. -/)
  (title := /-- Integrability of squares of polynomials -/)
  (latexEnv := "lemma")]
lemma gsm_sq_integrable (n : ℕ) (g : MvPolynomial (Fin n) ℝ) :
    Integrable (fun y => (MvPolynomial.eval y g) ^ 2) (gaussian_scale_mixture n) := by
  refine (gsm_mul_integrable n g g).congr (Filter.Eventually.of_forall ?_)
  intro y
  exact (sq (MvPolynomial.eval y g)).symm

@[blueprint "lem:gsm-representative-mean-zero"
  (statement := /-- Let $n,k\in\mathbb N$, write $Q=Q_n$ for the measure of \cref{def:gaussian-scale-mixture}, and let $\rho\in\mathbb R[y_1,\dots,y_n]$ satisfy
  \[
    \int\rho\,q\;dQ=q(0)-\int q\;dQ
    \qquad\text{for all }q\text{ with }\deg q\leq k.
  \]
  Then $\int\rho\;dQ=0$. -/)
  (proof := /-- Apply the hypothesis to $q=1$, whose total degree is $0$ and hence at most $k$. The left-hand side becomes $\int\rho\;dQ$ because $\rho\cdot 1=\rho$. On the right, $q(0)=1$ and $\int 1\;dQ$ is the total mass of $Q$, which equals $1$ since $Q$ is a probability measure by \cref{lem:gsm-prob}. Hence $\int\rho\;dQ=1-1=0$. -/)
  (title := /-- The representative has zero null-mean -/)
  (latexEnv := "lemma")]
lemma gsm_representative_mean_zero (n k : ℕ) (ρ : MvPolynomial (Fin n) ℝ)
    (hρrep : ∀ q : MvPolynomial (Fin n) ℝ, q.totalDegree ≤ k →
      ∫ y, MvPolynomial.eval y ρ * MvPolynomial.eval y q ∂(gaussian_scale_mixture n)
        = MvPolynomial.eval 0 q -
          ∫ y, MvPolynomial.eval y q ∂(gaussian_scale_mixture n)) :
    ∫ y, MvPolynomial.eval y ρ ∂(gaussian_scale_mixture n) = 0 := by
  haveI := gsm_prob n
  have hone : (1 : MvPolynomial (Fin n) ℝ).totalDegree ≤ k := by
    rw [MvPolynomial.totalDegree_one]; exact Nat.zero_le k
  have h := hρrep 1 hone
  simp only [map_one, mul_one, integral_const, measureReal_univ_eq_one,
    smul_eq_mul, one_mul] at h
  rw [h, sub_self]

@[blueprint "lem:gsm-weight-mean"
  (statement := /-- Let $n,k\in\mathbb N$, let $\alpha\in\mathbb R_{\geq0}$, write $Q=Q_n$, and let $\rho\in\mathbb R[y_1,\dots,y_n]$ be a representative in the sense that $\int\rho\,q\;dQ=q(0)-\int q\;dQ$ for all $q$ with $\deg q\leq k$. Then
  \[
    \int(1+\alpha\rho)\;dQ=1.
  \] -/)
  (proof := /-- By \cref{lem:gsm-representative-mean-zero} we have $\int\rho\;dQ=0$. Evaluation is additive and commutes with scalar multiples, so $1+\alpha\rho$ evaluates pointwise to $1+\alpha\rho(y)$. Splitting the integral, which is legitimate because constants are integrable for the probability measure $Q$ of \cref{lem:gsm-prob} and $\rho$ is integrable by \cref{lem:gsm-poly-integrable}, gives $\int 1\;dQ+\alpha\int\rho\;dQ=1+0=1$. -/)
  (title := /-- The likelihood weight has unit null-mean -/)
  (latexEnv := "lemma")]
lemma gsm_weight_mean (n k : ℕ) (α : NNReal) (ρ : MvPolynomial (Fin n) ℝ)
    (hρrep : ∀ q : MvPolynomial (Fin n) ℝ, q.totalDegree ≤ k →
      ∫ y, MvPolynomial.eval y ρ * MvPolynomial.eval y q ∂(gaussian_scale_mixture n)
        = MvPolynomial.eval 0 q -
          ∫ y, MvPolynomial.eval y q ∂(gaussian_scale_mixture n)) :
    ∫ y, MvPolynomial.eval y (1 + (α : ℝ) • ρ) ∂(gaussian_scale_mixture n) = 1 := by
  haveI := gsm_prob n
  have hρ0 := gsm_representative_mean_zero n k ρ hρrep
  have hfun : (fun y => MvPolynomial.eval y (1 + (α : ℝ) • ρ))
      = fun y => 1 + (α : ℝ) * MvPolynomial.eval y ρ := by
    funext y
    simp only [map_add, map_one, MvPolynomial.smul_eval]
  rw [hfun, integral_add (integrable_const 1)
    ((gsm_poly_integrable n ρ).const_mul _), integral_const_mul, hρ0]
  simp

@[blueprint "lem:gsm-weight-sq-moment"
  (statement := /-- Let $n,k\in\mathbb N$, let $\alpha\in\mathbb R_{\geq0}$, write $Q=Q_n$, and let $\rho\in\mathbb R[y_1,\dots,y_n]$ be a representative in the sense that $\int\rho\,q\;dQ=q(0)-\int q\;dQ$ for all $q$ with $\deg q\leq k$. Then
  \[
    \int(1+\alpha\rho)^2\;dQ=1+\alpha^2\int\rho^2\;dQ.
  \] -/)
  (proof := /-- By \cref{lem:gsm-representative-mean-zero} we have $\int\rho\;dQ=0$. Expanding the square pointwise, $(1+\alpha\rho(y))^2=\bigl(1+2\alpha\rho(y)\bigr)+\alpha^2\rho(y)^2$. Each part is integrable: constants are integrable because $Q$ is a probability measure by \cref{lem:gsm-prob}, $\rho$ is integrable by \cref{lem:gsm-poly-integrable}, and $\rho^2$ is integrable by \cref{lem:gsm-sq-integrable}. Splitting the integral and pulling out the constants gives $1+2\alpha\int\rho\;dQ+\alpha^2\int\rho^2\;dQ$, and the middle term vanishes. -/)
  (title := /-- Second moment of the likelihood weight -/)
  (latexEnv := "lemma")]
lemma gsm_weight_sq_moment (n k : ℕ) (α : NNReal) (ρ : MvPolynomial (Fin n) ℝ)
    (hρrep : ∀ q : MvPolynomial (Fin n) ℝ, q.totalDegree ≤ k →
      ∫ y, MvPolynomial.eval y ρ * MvPolynomial.eval y q ∂(gaussian_scale_mixture n)
        = MvPolynomial.eval 0 q -
          ∫ y, MvPolynomial.eval y q ∂(gaussian_scale_mixture n)) :
    ∫ y, (MvPolynomial.eval y (1 + (α : ℝ) • ρ)) ^ 2 ∂(gaussian_scale_mixture n)
      = 1 + (α : ℝ) ^ 2 *
          ∫ y, (MvPolynomial.eval y ρ) ^ 2 ∂(gaussian_scale_mixture n) := by
  haveI := gsm_prob n
  have hρ0 := gsm_representative_mean_zero n k ρ hρrep
  have hfun : (fun y => (MvPolynomial.eval y (1 + (α : ℝ) • ρ)) ^ 2)
      = fun y => (1 + 2 * (α : ℝ) * MvPolynomial.eval y ρ)
          + (α : ℝ) ^ 2 * (MvPolynomial.eval y ρ) ^ 2 := by
    funext y
    simp only [map_add, map_one, MvPolynomial.smul_eval]
    ring
  rw [hfun]
  rw [integral_add
    (μ := gaussian_scale_mixture n)
    (f := fun y => 1 + 2 * (α : ℝ) * MvPolynomial.eval y ρ)
    (g := fun y => (α : ℝ) ^ 2 * (MvPolynomial.eval y ρ) ^ 2)
    ((integrable_const 1).add ((gsm_poly_integrable n ρ).const_mul _))
    ((gsm_sq_integrable n ρ).const_mul _),
    integral_add (integrable_const (1 : ℝ))
      ((gsm_poly_integrable n ρ).const_mul _),
    integral_const_mul, integral_const_mul, hρ0]
  simp

@[blueprint "lem:sample-var-eq-centered-integral"
  (statement := /-- For all $n,m\in\mathbb N$ and every $p\in\mathbb R[x_{i,j}]$, the variance of \cref{def:sample-polynomial-variance} equals the integral of the squared centered observable:
  \[
    \operatorname{Var}_{Q_n^{\otimes m}}(p)
      =\int\bigl(p(x)-\mathbb E_{Q_n^{\otimes m}}[p]\bigr)^2\;dQ_n^{\otimes m}.
  \] -/)
  (proof := /-- By \cref{def:sample-polynomial-variance} the left side is the variance of the observable under the product measure, and by \cref{def:sample-polynomial-expectation} the constant subtracted on the right is the mean of that observable. The variance of an almost-everywhere measurable real random variable equals the integral of the square of its deviation from its mean; the observable is measurable because it is continuous by \cref{lem:sample-obs-continuous}. -/)
  (title := /-- Variance as the second central moment -/)
  (latexEnv := "lemma")]
lemma sample_var_eq_centered_integral (n m : ℕ)
    (p : MvPolynomial (Fin m × Fin n) ℝ) :
    sample_polynomial_variance (gaussian_scale_mixture n) p
      = ∫ x, (sample_polynomial_observable p x -
          sample_polynomial_expectation (gaussian_scale_mixture n) p) ^ 2
          ∂(iid_product_measure m (gaussian_scale_mixture n)) := by
  unfold sample_polynomial_variance sample_polynomial_expectation
  exact variance_eq_integral (sample_obs_continuous n m p).aemeasurable

@[blueprint "lem:mean-zero-gap-sq-le"
  (statement := /-- Let $(\Omega,\mu)$ be a probability space, let $H,F\in L^2(\mu)$ with $\int H\;d\mu=0$, and let $c\in\mathbb R$. Then
  \[
    \Bigl(\int HF\;d\mu\Bigr)^2
      \leq\Bigl(\int H^2\;d\mu\Bigr)\Bigl(\int (F-c)^2\;d\mu\Bigr).
  \] -/)
  (proof := /-- The function $F-c$ lies in $L^2(\mu)$, being the difference of $F\in L^2(\mu)$ and a constant, which lies in $L^2$ of a finite measure. Applying \cref{lem:integral-mul-sq-le-of-memLp} to the pair $H$ and $F-c$ gives
  \[
    \Bigl(\int H\,(F-c)\;d\mu\Bigr)^2
      \leq\Bigl(\int H^2\;d\mu\Bigr)\Bigl(\int(F-c)^2\;d\mu\Bigr).
  \]
  It remains to identify the left-hand sides. Pointwise $H(F-c)=HF-cH$. The product $HF$ is integrable since $H,F\in L^2(\mu)$, and $cH$ is integrable since $H\in L^2(\mu)\subseteq L^1(\mu)$ for the probability measure $\mu$. Hence the integral splits, and
  \[
    \int H\,(F-c)\;d\mu=\int HF\;d\mu-c\int H\;d\mu=\int HF\;d\mu
  \]
  because $\int H\;d\mu=0$. Substituting this identity yields the assertion. -/)
  (title := /-- Covariance Cauchy--Schwarz bound for a centered factor -/)
  (latexEnv := "lemma")]
lemma mean_zero_gap_sq_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (H F : Ω → ℝ) (c : ℝ)
    (hH : MemLp H 2 μ) (hF : MemLp F 2 μ) (hH0 : ∫ ω, H ω ∂μ = 0) :
    (∫ ω, H ω * F ω ∂μ) ^ 2
      ≤ (∫ ω, H ω ^ 2 ∂μ) * (∫ ω, (F ω - c) ^ 2 ∂μ) := by
  have hFc : MemLp (fun ω => F ω - c) 2 μ := hF.sub (memLp_const c)
  have key := integral_mul_sq_le_of_memLp μ H (fun ω => F ω - c) hH hFc
  have heq : ∫ ω, H ω * (F ω - c) ∂μ = ∫ ω, H ω * F ω ∂μ := by
    have hHF : Integrable (fun ω => H ω * F ω) μ := hH.integrable_mul hF
    have hHc : Integrable (fun ω => H ω * c) μ :=
      (hH.integrable (by norm_num)).mul_const c
    have hsplit : (fun ω => H ω * (F ω - c)) = fun ω => H ω * F ω - H ω * c := by
      funext ω; ring
    rw [hsplit, integral_sub hHF hHc, integral_mul_const, hH0, zero_mul, sub_zero]
  rw [heq] at key
  exact key

@[blueprint "lem:sample-obs-mul"
  (statement := /-- For all $n,m\in\mathbb N$, all $p,q\in\mathbb R[x_{i,j}]$ and every sample tuple $x$, the observable of \cref{def:sample-polynomial-observable} is multiplicative:
  \[
    (pq)(x)=p(x)\,q(x).
  \] -/)
  (proof := /-- By \cref{def:sample-polynomial-observable} each side is an evaluation at the same assignment $(i,j)\mapsto x_i(j)$, and evaluation of multivariate polynomials is a ring homomorphism, hence multiplicative. -/)
  (title := /-- Multiplicativity of polynomial observables -/)
  (latexEnv := "lemma")]
lemma sample_obs_mul (n m : ℕ) (p q : MvPolynomial (Fin m × Fin n) ℝ)
    (x : Fin m → Fin n → ℝ) :
    sample_polynomial_observable (p * q) x
      = sample_polynomial_observable p x * sample_polynomial_observable q x := by
  unfold sample_polynomial_observable
  rw [MvPolynomial.eval_mul]

@[blueprint "lem:gap-sq-le-weight-moment"
  (statement := /-- Let $n,m,k\in\mathbb N$, let $\alpha\in\mathbb R_{\geq0}$ with $\alpha\leq1$, write $Q=Q_n$ for the measure of \cref{def:gaussian-scale-mixture} and $P$ for its origin contamination of \cref{def:origin-contamination}. Let $\rho\in\mathbb R[y_1,\dots,y_n]$ satisfy
  \[
    \int\rho\,q\;dQ=q(0)-\int q\;dQ
    \qquad\text{for all }q\text{ with }\deg q\leq k,
  \]
  and let $p\in\mathbb R[x_{i,j}]$ with $\deg p\leq k$. Then, with the expectation and variance of \cref{def:sample-polynomial-expectation,def:sample-polynomial-variance},
  \[
    \bigl(\mathbb E_{P^{\otimes m}}[p]-\mathbb E_{Q^{\otimes m}}[p]\bigr)^2
      \leq\Bigl(\bigl(1+\alpha^2\textstyle\int\rho^2\,dQ\bigr)^m-1\Bigr)
        \operatorname{Var}_{Q^{\otimes m}}(p).
  \] -/)
  (proof := /-- Write $w=1+\alpha\rho$ and let $W=\prod_{i=1}^m w^{(i)}$ be the product over samples of $w$ renamed into the $i$-th block. Let $F$ be the observable of $p$ and let $H(x)=W(x)-1$. The measure $Q^{\otimes m}$ is a probability measure by \cref{lem:iid-gsm-isProbabilityMeasure}.

  First, $\int W\;dQ^{\otimes m}=1$: by \cref{lem:prod-obs-expectation-gsm} this integral is $\bigl(\int w\;dQ\bigr)^m$, and $\int w\;dQ=1$ by \cref{lem:gsm-weight-mean}. Second,
  \[
    \int W^2\;dQ^{\otimes m}
      =\Bigl(\int w^2\;dQ\Bigr)^m
      =\Bigl(1+\alpha^2\int\rho^2\;dQ\Bigr)^m,
  \]
  using \cref{lem:prod-obs-sq-integral-gsm} and then \cref{lem:gsm-weight-sq-moment}. Both $W$ and $F$ lie in $L^2(Q^{\otimes m})$ by \cref{lem:sample-obs-memLp-two}, hence so does $H$, being $W$ minus a constant.

  The centered weight has zero mean: splitting $\int H\;dQ^{\otimes m}=\int W\;dQ^{\otimes m}-1$, which is legitimate since $W$ is integrable and constants are integrable for a probability measure, gives $1-1=0$. Its second moment is
  \[
    \int H^2\;dQ^{\otimes m}
      =\int W^2\;dQ^{\otimes m}-2\int W\;dQ^{\otimes m}+1
      =\Bigl(1+\alpha^2\int\rho^2\;dQ\Bigr)^m-1,
  \]
  where the expansion $H^2=W^2-2W+1$ is integrated termwise, all three terms being integrable, and the two moments computed above were substituted.

  Next, $H$ reproduces the expectation gap. Since $\rho$ is a representative, \cref{lem:reproduce-single} gives $\int q\;dP=\int w\,q\;dQ$ for every $q$ with $\deg q\leq k$, so \cref{lem:weight-gap-identity} applies to $p$ and yields $\mathbb E_{P^{\otimes m}}[p]=\mathbb E_{Q^{\otimes m}}[W p]$. Pointwise $H(x)F(x)=(Wp)(x)-p(x)$ by \cref{lem:sample-obs-mul}, and both observables are integrable by \cref{lem:sample-obs-integrable-gsm}, so
  \[
    \int HF\;dQ^{\otimes m}
      =\mathbb E_{Q^{\otimes m}}[Wp]-\mathbb E_{Q^{\otimes m}}[p]
      =\mathbb E_{P^{\otimes m}}[p]-\mathbb E_{Q^{\otimes m}}[p].
  \]

  Finally apply \cref{lem:mean-zero-gap-sq-le} to $H$ and $F$ with the constant $c=\mathbb E_{Q^{\otimes m}}[p]$. Its right-hand factor $\int(F-c)^2\;dQ^{\otimes m}$ equals $\operatorname{Var}_{Q^{\otimes m}}(p)$ by \cref{lem:sample-var-eq-centered-integral}, and its left-hand side and the factor $\int H^2$ were identified above. This is exactly the claimed inequality. -/)
  (title := /-- Gap bound in terms of the weight second moment -/)
  (latexEnv := "lemma")]
lemma gap_sq_le_weight_moment (n m k : ℕ) (α : NNReal) (hα : α ≤ 1)
    (ρ : MvPolynomial (Fin n) ℝ)
    (hρrep : ∀ q : MvPolynomial (Fin n) ℝ, q.totalDegree ≤ k →
      ∫ y, MvPolynomial.eval y ρ * MvPolynomial.eval y q ∂(gaussian_scale_mixture n)
        = MvPolynomial.eval 0 q -
          ∫ y, MvPolynomial.eval y q ∂(gaussian_scale_mixture n))
    (p : MvPolynomial (Fin m × Fin n) ℝ) (hpdeg : p.totalDegree ≤ k) :
    (sample_polynomial_expectation
        (origin_contamination α (gaussian_scale_mixture n)) p -
      sample_polynomial_expectation (gaussian_scale_mixture n) p) ^ 2 ≤
      ((1 + (α : ℝ) ^ 2 *
          ∫ y, (MvPolynomial.eval y ρ) ^ 2 ∂(gaussian_scale_mixture n)) ^ m - 1) *
        sample_polynomial_variance (gaussian_scale_mixture n) p := by
  haveI := iid_gsm_isProbabilityMeasure n m
  set Q := gaussian_scale_mixture n with hQ
  set μ := iid_product_measure m Q with hμ
  set w : MvPolynomial (Fin n) ℝ := 1 + (α : ℝ) • ρ with hwdef
  set W : MvPolynomial (Fin m × Fin n) ℝ :=
    ∏ i : Fin m, MvPolynomial.rename (fun j => (i, j)) w with hWdef
  set F : (Fin m → Fin n → ℝ) → ℝ := sample_polynomial_observable p with hFdef
  set H : (Fin m → Fin n → ℝ) → ℝ :=
    fun x => sample_polynomial_observable W x - 1 with hHdef
  have hWmean : ∫ x, sample_polynomial_observable W x ∂μ = 1 := by
    have h : sample_polynomial_expectation Q W
        = (∫ y, MvPolynomial.eval y w ∂Q) ^ m := prod_obs_expectation_gsm n m w
    rw [gsm_weight_mean n k α ρ hρrep, one_pow] at h
    exact h
  have hWsq : ∫ x, (sample_polynomial_observable W x) ^ 2 ∂μ
      = (1 + (α : ℝ) ^ 2 * ∫ y, (MvPolynomial.eval y ρ) ^ 2 ∂Q) ^ m := by
    rw [prod_obs_sq_integral_gsm n m w, gsm_weight_sq_moment n k α ρ hρrep]
  have hWLp : MemLp (sample_polynomial_observable W) 2 μ := sample_obs_memLp_two n m W
  have hFLp : MemLp F 2 μ := sample_obs_memLp_two n m p
  have hHLp : MemLp H 2 μ := hWLp.sub (memLp_const 1)
  have hH0 : ∫ x, H x ∂μ = 0 := by
    rw [hHdef]
    rw [integral_sub (hWLp.integrable (by norm_num)) (integrable_const 1)]
    rw [hWmean]
    simp
  have hHsq : ∫ x, (H x) ^ 2 ∂μ
      = (1 + (α : ℝ) ^ 2 * ∫ y, (MvPolynomial.eval y ρ) ^ 2 ∂Q) ^ m - 1 := by
    have hexp : (fun x => (H x) ^ 2)
        = fun x => ((sample_polynomial_observable W x) ^ 2
            - 2 * sample_polynomial_observable W x) + 1 := by
      funext x
      rw [hHdef]
      ring
    rw [hexp]
    rw [integral_add (μ := μ)
        (f := fun x => (sample_polynomial_observable W x) ^ 2
          - 2 * sample_polynomial_observable W x)
        (g := fun _ => (1 : ℝ))
        ((hWLp.integrable_sq).sub ((hWLp.integrable (by norm_num)).const_mul 2))
        (integrable_const 1),
      integral_sub hWLp.integrable_sq ((hWLp.integrable (by norm_num)).const_mul 2),
      integral_const_mul, hWmean, hWsq]
    simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, mul_one]
    ring
  have hgap : ∫ x, H x * F x ∂μ
      = sample_polynomial_expectation
          (origin_contamination α Q) p - sample_polynomial_expectation Q p := by
    have hrep : ∀ q : MvPolynomial (Fin n) ℝ, q.totalDegree ≤ k →
        ∫ y, MvPolynomial.eval y q ∂(origin_contamination α Q)
          = ∫ y, MvPolynomial.eval y (w * q) ∂Q :=
      fun q hq => reproduce_single n k α hα ρ hρrep q hq
    have hid := weight_gap_identity n m k α hα ρ hrep p hpdeg
    have hsplit : (fun x => H x * F x)
        = fun x => sample_polynomial_observable (W * p) x
            - sample_polynomial_observable p x := by
      funext x
      rw [hHdef, hFdef, sample_obs_mul]
      ring
    rw [hsplit, integral_sub (sample_obs_integrable_gsm n m (W * p))
      (sample_obs_integrable_gsm n m p)]
    rw [hid]
    rfl
  have hvar : sample_polynomial_variance Q p
      = ∫ x, (F x - sample_polynomial_expectation Q p) ^ 2 ∂μ :=
    sample_var_eq_centered_integral n m p
  have key := mean_zero_gap_sq_le μ H F
    (sample_polynomial_expectation Q p) hHLp hFLp hH0
  rw [hgap, hHsq] at key
  rw [hvar]
  exact key

@[blueprint "lem:representative-moment-le-single-lda-sq"
  (statement := /-- Let $n,k\in\mathbb N$, let $\alpha\in\mathbb R_{\geq0}$ with $\alpha\leq1$, write $Q=Q_n$ for the measure of \cref{def:gaussian-scale-mixture} and $P$ for its origin contamination of \cref{def:origin-contamination}. Let $\rho\in\mathbb R[y_1,\dots,y_n]$ satisfy $\deg\rho\leq k$ and
  \[
    \int\rho\,q\;dQ=q(0)-\int q\;dQ
    \qquad\text{for all }q\text{ with }\deg q\leq k.
  \]
  Then, with $\operatorname{LDA}$ as in \cref{def:low-degree-advantage},
  \[
    \alpha^2\int\rho^2\;dQ
      \leq\bigl(\operatorname{LDA}^{(1)}_{\leq k}(P,Q)\bigr)^2.
  \] -/)
  (proof := /-- Set $V=\int\rho^2\;dQ$ and $\delta=\operatorname{LDA}^{(1)}_{\leq k}(P,Q)$. The quantity $V$ is nonnegative because its integrand is a square, and $\delta$ is nonnegative by \cref{lem:low-degree-advantage-nonnegative}. If $V=0$ the left side is $0$ and the claim is the nonnegativity of $\delta^2$; assume therefore $V>0$.

  Let $q$ be the one-sample observable polynomial obtained from $\rho$ by renaming its variables into the single sample block. Its total degree is at most that of $\rho$, hence at most $k$, since renaming does not increase total degree. By \cref{lem:gsm-representative-mean-zero} we have $\int\rho\;dQ=0$, so \cref{lem:prod-obs-expectation-gsm} with $m=1$ gives $\mathbb E_{Q^{\otimes1}}[q]=0$. Likewise \cref{lem:prod-obs-expectation-oc} with $m=1$ gives $\mathbb E_{P^{\otimes1}}[q]=\int\rho\;dP$, and by \cref{lem:reproduce-single} applied to $\rho$ this equals $\int(1+\alpha\rho)\rho\;dQ$. Expanding pointwise and integrating termwise, which is legitimate because $\rho$ is integrable by \cref{lem:gsm-poly-integrable} and $\rho^2$ by \cref{lem:gsm-sq-integrable}, this is $\int\rho\;dQ+\alpha V=\alpha V$. For the variance, \cref{lem:sample-var-eq-centered-integral} with the vanishing mean and \cref{lem:prod-obs-sq-integral-gsm} with $m=1$ give $\operatorname{Var}_{Q^{\otimes1}}(q)=V>0$.

  Hence $q$ is admissible in \cref{def:low-degree-advantage} and its normalized gap is
  \[
    \frac{|\alpha V-0|}{\sqrt V}=\frac{\alpha V}{\sqrt V}=\alpha\sqrt V,
  \]
  using $\alpha\geq0$, $V\geq0$ and $V=\sqrt V\sqrt V$. So $\alpha\sqrt V$ belongs to the set whose supremum defines $\delta$.

  That set is bounded above by $\alpha\sqrt V$ itself. Indeed, let $p'$ be any admissible polynomial, so $\deg p'\leq k$ and $\operatorname{Var}_{Q^{\otimes1}}(p')>0$. Applying \cref{lem:gap-sq-le-weight-moment} with $m=1$ gives
  \[
    \bigl(\mathbb E_{P^{\otimes1}}[p']-\mathbb E_{Q^{\otimes1}}[p']\bigr)^2
      \leq\bigl(\alpha\sqrt V\bigr)^2\operatorname{Var}_{Q^{\otimes1}}(p'),
  \]
  since $\bigl(1+\alpha^2V\bigr)^1-1=\alpha^2V=(\alpha\sqrt V)^2$. Taking square roots, using $\sqrt{t^2}=|t|$ and the nonnegativity of $\alpha\sqrt V$, and dividing by the positive $\sqrt{\operatorname{Var}_{Q^{\otimes1}}(p')}$ bounds the normalized gap of $p'$ by $\alpha\sqrt V$.

  Therefore the supremum satisfies $\alpha\sqrt V\leq\delta$. Both sides are nonnegative, so squaring preserves the inequality, and $(\alpha\sqrt V)^2=\alpha^2V$ because $V\geq0$. This is the assertion. -/)
  (title := /-- The representative second moment is bounded by the one-sample advantage -/)
  (latexEnv := "lemma")]
lemma representative_moment_le_single_lda_sq (n k : ℕ) (α : NNReal) (hα : α ≤ 1)
    (ρ : MvPolynomial (Fin n) ℝ) (hρdeg : ρ.totalDegree ≤ k)
    (hρrep : ∀ q : MvPolynomial (Fin n) ℝ, q.totalDegree ≤ k →
      ∫ y, MvPolynomial.eval y ρ * MvPolynomial.eval y q ∂(gaussian_scale_mixture n)
        = MvPolynomial.eval 0 q -
          ∫ y, MvPolynomial.eval y q ∂(gaussian_scale_mixture n)) :
    (α : ℝ) ^ 2 * ∫ y, (MvPolynomial.eval y ρ) ^ 2 ∂(gaussian_scale_mixture n)
      ≤ (low_degree_advantage n 1 k
          (origin_contamination α (gaussian_scale_mixture n))
          (gaussian_scale_mixture n)) ^ 2 := by
  haveI := iid_gsm_isProbabilityMeasure n 1
  set Q := gaussian_scale_mixture n with hQ
  set P := origin_contamination α Q with hP
  set V : ℝ := ∫ y, (MvPolynomial.eval y ρ) ^ 2 ∂Q with hV
  set δ : ℝ := low_degree_advantage n 1 k P Q with hδ
  have hVnonneg : 0 ≤ V := integral_nonneg fun y => sq_nonneg _
  have hδnonneg : 0 ≤ δ := low_degree_advantage_nonnegative n 1 k P Q
  have hα0 : (0 : ℝ) ≤ (α : ℝ) := NNReal.coe_nonneg α
  rcases eq_or_lt_of_le hVnonneg with hV0 | hVpos
  · rw [← hV0, mul_zero]
    exact sq_nonneg δ
  set q : MvPolynomial (Fin 1 × Fin n) ℝ :=
    ∏ i : Fin 1, MvPolynomial.rename (fun j => (i, j)) ρ with hqdef
  have hqdeg : q.totalDegree ≤ k := by
    rw [hqdef, Fin.prod_univ_one]
    exact (MvPolynomial.totalDegree_rename_le _ ρ).trans hρdeg
  have hρ0 : ∫ y, MvPolynomial.eval y ρ ∂Q = 0 :=
    gsm_representative_mean_zero n k ρ hρrep
  have hEQ : sample_polynomial_expectation Q q = 0 := by
    rw [hqdef, prod_obs_expectation_gsm n 1 ρ, hρ0, pow_one]
  have hEP : sample_polynomial_expectation P q = (α : ℝ) * V := by
    rw [hqdef, hP, prod_obs_expectation_oc n 1 α hα ρ, pow_one]
    rw [reproduce_single n k α hα ρ hρrep ρ hρdeg]
    have hexpand : (fun y => MvPolynomial.eval y ((1 + (α : ℝ) • ρ) * ρ))
        = fun y => MvPolynomial.eval y ρ
            + (α : ℝ) * (MvPolynomial.eval y ρ) ^ 2 := by
      funext y
      simp only [MvPolynomial.eval_mul, map_add, map_one, MvPolynomial.smul_eval]
      ring
    rw [hexpand, integral_add (gsm_poly_integrable n ρ)
      ((gsm_sq_integrable n ρ).const_mul _), integral_const_mul, hρ0, zero_add]
  have hvarq : sample_polynomial_variance Q q = V := by
    rw [sample_var_eq_centered_integral n 1 q, hEQ]
    have hsimp : (fun x : Fin 1 → Fin n → ℝ =>
        (sample_polynomial_observable q x - 0) ^ 2)
        = fun x => (sample_polynomial_observable q x) ^ 2 := by
      funext x; rw [sub_zero]
    rw [hsimp, hqdef, prod_obs_sq_integral_gsm n 1 ρ, pow_one]
  have hmem : (α : ℝ) * Real.sqrt V ∈ {r : ℝ |
      ∃ p : MvPolynomial (Fin 1 × Fin n) ℝ, p.totalDegree ≤ k ∧
        0 < sample_polynomial_variance Q p ∧
        r = |sample_polynomial_expectation P p -
          sample_polynomial_expectation Q p| /
          Real.sqrt (sample_polynomial_variance Q p)} := by
    refine ⟨q, hqdeg, by rw [hvarq]; exact hVpos, ?_⟩
    rw [hEP, hEQ, hvarq, sub_zero, abs_of_nonneg (mul_nonneg hα0 hVnonneg)]
    rw [eq_div_iff (ne_of_gt (Real.sqrt_pos.2 hVpos)), mul_assoc,
      Real.mul_self_sqrt hVnonneg]
  have hbdd : BddAbove {r : ℝ |
      ∃ p : MvPolynomial (Fin 1 × Fin n) ℝ, p.totalDegree ≤ k ∧
        0 < sample_polynomial_variance Q p ∧
        r = |sample_polynomial_expectation P p -
          sample_polynomial_expectation Q p| /
          Real.sqrt (sample_polynomial_variance Q p)} := by
    refine ⟨(α : ℝ) * Real.sqrt V, ?_⟩
    rintro r ⟨p', hp'deg, hp'var, rfl⟩
    have hgapsq := gap_sq_le_weight_moment n 1 k α hα ρ hρrep p' hp'deg
    rw [pow_one] at hgapsq
    have hsimp : (1 + (α : ℝ) ^ 2 * V - 1) = ((α : ℝ) * Real.sqrt V) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hVnonneg]; ring
    rw [hsimp] at hgapsq
    rw [div_le_iff₀ (Real.sqrt_pos.2 hp'var), ← Real.sqrt_sq_eq_abs]
    calc Real.sqrt ((sample_polynomial_expectation P p' -
            sample_polynomial_expectation Q p') ^ 2)
          ≤ Real.sqrt (((α : ℝ) * Real.sqrt V) ^ 2 *
              sample_polynomial_variance Q p') := Real.sqrt_le_sqrt hgapsq
      _ = (α : ℝ) * Real.sqrt V *
            Real.sqrt (sample_polynomial_variance Q p') := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq
            (mul_nonneg hα0 (Real.sqrt_nonneg V))]
  have hle : (α : ℝ) * Real.sqrt V ≤ δ := by
    rw [hδ]
    unfold low_degree_advantage
    exact le_csSup hbdd hmem
  have hsq : ((α : ℝ) * Real.sqrt V) ^ 2 ≤ δ ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hα0 (Real.sqrt_nonneg V)) hδnonneg).mpr hle
  rw [mul_pow, Real.sq_sqrt hVnonneg] at hsq
  exact hsq

@[blueprint "lem:tensorization-gap-bound"
  (statement := /-- Let $n,m,k\in\mathbb N$ and let $\alpha\in\mathbb R_{\geq0}$ with $\alpha\leq1$; write $Q=Q_n$ for the measure of \cref{def:gaussian-scale-mixture} and $P$ for its origin contamination of \cref{def:origin-contamination}, and set $\delta=\operatorname{LDA}^{(1)}_{\leq k}(P,Q)$ as in \cref{def:low-degree-advantage}. Then for every $p\in\mathbb R[x_{i,j}]$ with $\deg p\leq k$ and $\operatorname{Var}_{Q^{\otimes m}}(p)>0$,
  \[
    \bigl(\mathbb E_{P^{\otimes m}}[p]-\mathbb E_{Q^{\otimes m}}[p]\bigr)^2
      \leq\bigl((1+\delta^2)^m-1\bigr)\operatorname{Var}_{Q^{\otimes m}}(p),
  \]
  with expectation and variance as in \cref{def:sample-polynomial-expectation,def:sample-polynomial-variance}. -/)
  (proof := /-- By \cref{lem:gsm-exists-representative} choose $\rho$ with $\deg\rho\leq k$ satisfying $\int\rho\,q\;dQ=q(0)-\int q\;dQ$ for every $q$ with $\deg q\leq k$, and set $V=\int\rho^2\;dQ$, which is nonnegative since its integrand is a square; consequently $\alpha^2V\geq0$.

  By \cref{lem:gap-sq-le-weight-moment} applied to $\rho$ and $p$,
  \[
    \bigl(\mathbb E_{P^{\otimes m}}[p]-\mathbb E_{Q^{\otimes m}}[p]\bigr)^2
      \leq\bigl((1+\alpha^2V)^m-1\bigr)\operatorname{Var}_{Q^{\otimes m}}(p).
  \]
  By \cref{lem:representative-moment-le-single-lda-sq} we have $\alpha^2V\leq\delta^2$, so $1+\alpha^2V\leq1+\delta^2$ with both sides nonnegative, whence $(1+\alpha^2V)^m\leq(1+\delta^2)^m$ by monotonicity of the $m$-th power on nonnegative reals. Subtracting $1$ preserves this, so the bracketed factor above is at most $(1+\delta^2)^m-1$. Since $\operatorname{Var}_{Q^{\otimes m}}(p)>0$, multiplying this comparison of factors by the variance preserves the inequality, and combining with the displayed bound gives the assertion. -/)
  (title := /-- Per-polynomial tensorized gap bound -/)
  (latexEnv := "lemma")]
lemma tensorization_gap_bound (n m k : ℕ) (α : NNReal) (hα : α ≤ 1)
    (p : MvPolynomial (Fin m × Fin n) ℝ) (hpdeg : p.totalDegree ≤ k)
    (hpvar : 0 < sample_polynomial_variance (gaussian_scale_mixture n) p) :
    (sample_polynomial_expectation
        (origin_contamination α (gaussian_scale_mixture n)) p -
      sample_polynomial_expectation (gaussian_scale_mixture n) p) ^ 2 ≤
      ((1 + (low_degree_advantage n 1 k
          (origin_contamination α (gaussian_scale_mixture n))
          (gaussian_scale_mixture n)) ^ 2) ^ m - 1) *
        sample_polynomial_variance (gaussian_scale_mixture n) p := by
  obtain ⟨ρ, hρdeg, hρrep⟩ := gsm_exists_representative n k
  have hbase := gap_sq_le_weight_moment n m k α hα ρ hρrep p hpdeg
  have hmoment := representative_moment_le_single_lda_sq n k α hα ρ hρdeg hρrep
  have hVnonneg : (0 : ℝ) ≤ (α : ℝ) ^ 2 *
      ∫ y, (MvPolynomial.eval y ρ) ^ 2 ∂(gaussian_scale_mixture n) :=
    mul_nonneg (sq_nonneg _) (integral_nonneg fun y => sq_nonneg _)
  refine hbase.trans (mul_le_mul_of_nonneg_right ?_ (le_of_lt hpvar))
  have hpow : (1 + (α : ℝ) ^ 2 *
        ∫ y, (MvPolynomial.eval y ρ) ^ 2 ∂(gaussian_scale_mixture n)) ^ m
      ≤ (1 + (low_degree_advantage n 1 k
          (origin_contamination α (gaussian_scale_mixture n))
          (gaussian_scale_mixture n)) ^ 2) ^ m := by
    apply pow_le_pow_left₀ (by linarith)
    linarith
  linarith

@[blueprint "lem:low-degree-advantage-tensorization"
  (statement := /-- Let $n,m,k\in\mathbb N$ and $0\leq\alpha\leq1$. For $Q_n$ from \cref{def:gaussian-scale-mixture} and $P_{n,\alpha}$ from \cref{def:origin-contamination}, set $\delta=\operatorname{LDA}^{(1)}_{\leq k}(P_{n,\alpha},Q_n)$. Then
  \[
    \left(\operatorname{LDA}^{(m)}_{\leq k}(P_{n,\alpha},Q_n)\right)^2
    \leq (1+\delta^2)^m-1.
  \] -/)
  (proof := /-- Write $Q=Q_n$ and $P=P_{n,\alpha}$ for the measures of
  \cref{def:gaussian-scale-mixture,def:origin-contamination}, and set
  $\delta=\operatorname{LDA}^{(1)}_{\leq k}(P,Q)$ and
  $B=(1+\delta^2)^m-1$.

  By \cref{lem:lda-sq-le-of-gap-bound} it suffices to check that $B\geq0$ and
  that the uniform gap bound
  \[
    \bigl(\mathbb E_{P^{\otimes m}}[p]-\mathbb E_{Q^{\otimes m}}[p]\bigr)^2
      \leq B\,\operatorname{Var}_{Q^{\otimes m}}(p)
  \]
  holds for every polynomial observable $p$ on $m$ samples with
  $\deg p\leq k$ and $\operatorname{Var}_{Q^{\otimes m}}(p)>0$, the
  expectation and variance being those of
  \cref{def:sample-polynomial-expectation,def:sample-polynomial-variance} and
  the advantage that of \cref{def:low-degree-advantage}.

  For nonnegativity of $B$, note that $\delta^2\geq0$, so $1+\delta^2\geq1$
  and hence $(1+\delta^2)^m\geq1$ by monotonicity of powers; subtracting $1$
  gives $B\geq0$.

  The uniform gap bound is exactly \cref{lem:tensorization-gap-bound}, applied
  to each admissible $p$ with the hypothesis $\alpha\leq1$. This completes the
  proof. -/)
  (title := /-- Tensorization from one sample to many samples -/)
  (latexEnv := "lemma")]
lemma low_degree_advantage_tensorization (n m k : ℕ) (α : NNReal)
    (hα : α ≤ 1) :
    (low_degree_advantage n m k
      (origin_contamination α (gaussian_scale_mixture n))
      (gaussian_scale_mixture n)) ^ 2 ≤
      (1 + (low_degree_advantage n 1 k
        (origin_contamination α (gaussian_scale_mixture n))
        (gaussian_scale_mixture n)) ^ 2) ^ m - 1 := by
  refine lda_sq_le_of_gap_bound n m k
    (origin_contamination α (gaussian_scale_mixture n))
    (gaussian_scale_mixture n) _ ?_ ?_
  · have h1 : (1 : ℝ) ≤
        (1 + (low_degree_advantage n 1 k
          (origin_contamination α (gaussian_scale_mixture n))
          (gaussian_scale_mixture n)) ^ 2) ^ m := by
      apply one_le_pow₀
      nlinarith [sq_nonneg (low_degree_advantage n 1 k
        (origin_contamination α (gaussian_scale_mixture n))
        (gaussian_scale_mixture n))]
    linarith
  · intro p hpdeg hpvar
    exact tensorization_gap_bound n m k α hα p hpdeg hpvar

@[blueprint "lem:lda-squared-bound"
  (statement := /-- Let $C>0$ be a real number satisfying
  \cref{def:gaussian-mean-variance-constant}, let $n,m,k\in\mathbb N$, and let
  $\alpha\in\mathbb R_{\geq0}$ with $\alpha\leq1$. Let $Q_n$ be the Gaussian
  scale mixture of \cref{def:gaussian-scale-mixture} and let
  $P_{n,\alpha}$ be its origin contamination from
  \cref{def:origin-contamination}. Then, for the low-degree advantage of
  \cref{def:low-degree-advantage},
  \[
    \left(\operatorname{LDA}^{(m)}_{\leq k}(P_{n,\alpha},Q_n)\right)^2
    \leq (1+C^2\alpha^2k)^m-1.
  \] -/)
  (proof := /-- Write $Q=Q_n$ and $P=P_{n,\alpha}$, and set
  $\delta=\operatorname{LDA}^{(1)}_{\leq k}(P,Q)$.

  By \cref{lem:low-degree-advantage-tensorization}, applied with the
  hypothesis $\alpha\leq1$,
  \[
    \left(\operatorname{LDA}^{(m)}_{\leq k}(P,Q)\right)^2
      \leq (1+\delta^2)^m-1 .
  \]
  By \cref{lem:single-sample-lda-squared-bound}, applied with the same
  hypothesis $\alpha\leq1$ together with $C>0$ and
  \cref{def:gaussian-mean-variance-constant}, one has
  $\delta^2\leq C^2\alpha^2k$, hence
  $1+\delta^2\leq 1+C^2\alpha^2k$.

  The base $1+\delta^2$ is nonnegative because $\delta^2\geq0$, so raising
  the last inequality to the $m$th power preserves it:
  \[
    (1+\delta^2)^m\leq(1+C^2\alpha^2k)^m .
  \]
  Subtracting $1$ and chaining with the tensorization estimate gives
  \[
    \left(\operatorname{LDA}^{(m)}_{\leq k}(P,Q)\right)^2
      \leq (1+C^2\alpha^2k)^m-1,
  \]
  which is the assertion. -/)
  (title := /-- Squared low-degree advantage bound -/)
  (latexEnv := "lemma")]
lemma lda_squared_bound (C : ℝ) (hCpos : 0 < C)
    (hC : gaussian_mean_variance_constant C) (n m k : ℕ) (α : NNReal)
    (hα : α ≤ 1) :
    (low_degree_advantage n m k
      (origin_contamination α (gaussian_scale_mixture n))
      (gaussian_scale_mixture n)) ^ 2 ≤
      (1 + C ^ 2 * (α : ℝ) ^ 2 * (k : ℝ)) ^ m - 1 := by
  have htensor := low_degree_advantage_tensorization n m k α hα
  have hsingle := single_sample_lda_squared_bound C hCpos hC n k α hα
  have hmono : (1 + (low_degree_advantage n 1 k
        (origin_contamination α (gaussian_scale_mixture n))
        (gaussian_scale_mixture n)) ^ 2) ^ m ≤
      (1 + C ^ 2 * (α : ℝ) ^ 2 * (k : ℝ)) ^ m :=
    pow_le_pow_left₀ (by positivity) (by linarith) m
  linarith

@[blueprint "thm:lda-bound"
  (statement := /-- Let $n,m,k\in\mathbb N$, let $0\leq\alpha\leq1$, and let $C>0$ be a universal constant satisfying \cref{def:gaussian-mean-variance-constant}. Let $Q_n$ be the Gaussian scale mixture of \cref{def:gaussian-scale-mixture}, and let $P_{n,\alpha}=(1-\alpha)Q_n+\alpha\delta_0$ as in \cref{def:origin-contamination}. Then
  \[
    \operatorname{LDA}^{(m)}_{\leq k}(P_{n,\alpha},Q_n)
    \leq \sqrt{(1+C^2\alpha^2k)^m-1}.
  \] -/)
  (proof := /-- Write $L=\operatorname{LDA}^{(m)}_{\leq k}(P_{n,\alpha},Q_n)$.

  By \cref{lem:low-degree-advantage-nonnegative}, applied to the measures
  $P_{n,\alpha}$ and $Q_n$, we have $L\geq0$.

  By \cref{lem:lda-squared-bound}, applied with $C>0$ satisfying
  \cref{def:gaussian-mean-variance-constant} and with the hypothesis
  $\alpha\leq1$, we have $L^2\leq(1+C^2\alpha^2k)^m-1$.

  Since $C^2\alpha^2k\geq0$, the base satisfies $1+C^2\alpha^2k\geq1$, so
  $(1+C^2\alpha^2k)^m\geq1$ and therefore the radicand
  $(1+C^2\alpha^2k)^m-1$ is nonnegative.

  For real numbers $x\geq0$ and $y\geq0$ one has $x\leq\sqrt y$ if and only
  if $x^2\leq y$. Applying this with $x=L$ and $y=(1+C^2\alpha^2k)^m-1$,
  both shown nonnegative above, the inequality $L^2\leq y$ yields
  \[
    \operatorname{LDA}^{(m)}_{\leq k}(P_{n,\alpha},Q_n)
    \leq \sqrt{(1+C^2\alpha^2k)^m-1},
  \]
  which is the assertion. -/)
  (title := /-- Low-degree advantage bound -/)
  (latexEnv := "theorem")]
theorem lda_bound (C : ℝ) (hCpos : 0 < C)
    (hC : gaussian_mean_variance_constant C) (n m k : ℕ)
    (α : NNReal) (hα : α ≤ 1) :
    low_degree_advantage n m k
      (origin_contamination α (gaussian_scale_mixture n))
      (gaussian_scale_mixture n) ≤
      Real.sqrt ((1 + C ^ 2 * (α : ℝ) ^ 2 * (k : ℝ)) ^ m - 1) := by
  have hnonneg := low_degree_advantage_nonnegative n m k
    (origin_contamination α (gaussian_scale_mixture n))
    (gaussian_scale_mixture n)
  have hsq := lda_squared_bound C hCpos hC n m k α hα
  have hterm : (0 : ℝ) ≤ C ^ 2 * (α : ℝ) ^ 2 * (k : ℝ) := by positivity
  have hbase : (1 : ℝ) ≤ (1 + C ^ 2 * (α : ℝ) ^ 2 * (k : ℝ)) ^ m :=
    one_le_pow₀ (by linarith)
  exact (Real.le_sqrt hnonneg (by linarith)).mpr hsq

@[blueprint "lem:one-add-pow-le-exp"
  (statement := /-- Let $x\in\mathbb R$ satisfy $x\geq0$ and let $m\in\mathbb N$. Then
  \[
    (1+x)^m\leq e^{mx}.
  \] -/)
  (proof := /-- For every real $t$ one has $t+1\leq e^{t}$; applied with $t=x$ this
  gives $1+x\leq e^{x}$.

  Since $x\geq0$, the base satisfies $1+x\geq0$, so raising the inequality
  $1+x\leq e^{x}$ to the $m$th power preserves it:
  \[
    (1+x)^m\leq\left(e^{x}\right)^m .
  \]
  Finally $\left(e^{x}\right)^m=e^{mx}$, which yields the assertion. -/)
  (title := /-- Exponential bound for powers of $1+x$ -/)
  (latexEnv := "lemma")]
lemma one_add_pow_le_exp (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    (1 + x) ^ m ≤ Real.exp ((m : ℝ) * x) := by
  have h1 : 1 + x ≤ Real.exp x := by
    have h := Real.add_one_le_exp x
    linarith
  calc (1 + x) ^ m ≤ (Real.exp x) ^ m := pow_le_pow_left₀ (by linarith) h1 m
    _ = Real.exp ((m : ℝ) * x) := (Real.exp_nat_mul x m).symm

@[blueprint "lem:lda-le-sqrt-exp-of-degree-bound"
  (statement := /-- Let $n,m,k\in\mathbb N$, let $0\leq\alpha\leq1$, and let $C>0$ be a universal constant satisfying \cref{def:gaussian-mean-variance-constant}. Let $Q_n$ be the Gaussian scale mixture of \cref{def:gaussian-scale-mixture}, and let $P_{n,\alpha}$ be its origin contamination as in \cref{def:origin-contamination}. Let $A\in\mathbb R$ satisfy $\alpha^2km\leq A$. Then
  \[
    \operatorname{LDA}^{(m)}_{\leq k}(P_{n,\alpha},Q_n)
    \leq\sqrt{e^{C^2A}-1}.
  \] -/)
  (proof := /-- By \cref{thm:lda-bound}, applied with $C>0$ satisfying
  \cref{def:gaussian-mean-variance-constant} and with the hypothesis
  $\alpha\leq1$, we have
  \[
    \operatorname{LDA}^{(m)}_{\leq k}(P_{n,\alpha},Q_n)
    \leq\sqrt{(1+C^2\alpha^2k)^m-1}.
  \]

  The quantity $x=C^2\alpha^2k$ is nonnegative, being a product of squares and
  of the nonnegative real $k$. Hence \cref{lem:one-add-pow-le-exp}, applied with
  this $x$ and with the exponent $m$, gives
  \[
    (1+C^2\alpha^2k)^m\leq e^{mC^2\alpha^2k}.
  \]

  Since $C^2\geq0$ and $\alpha^2km\leq A$, multiplying the latter inequality by
  $C^2$ gives $mC^2\alpha^2k=C^2(\alpha^2km)\leq C^2A$, and the exponential is
  monotone, so $e^{mC^2\alpha^2k}\leq e^{C^2A}$. Chaining the two displayed
  estimates yields
  \[
    (1+C^2\alpha^2k)^m-1\leq e^{C^2A}-1 .
  \]

  The square root is monotone on the reals, so
  $\sqrt{(1+C^2\alpha^2k)^m-1}\leq\sqrt{e^{C^2A}-1}$, and combining this with the
  first display gives the assertion. -/)
  (title := /-- Uniform exponential form of the low-degree advantage bound -/)
  (latexEnv := "lemma")]
lemma lda_le_sqrt_exp_of_degree_bound (C : ℝ) (hCpos : 0 < C)
    (hC : gaussian_mean_variance_constant C) (n m k : ℕ) (α : NNReal)
    (hα : α ≤ 1) (A : ℝ) (hA : (α : ℝ) ^ 2 * (k : ℝ) * (m : ℝ) ≤ A) :
    low_degree_advantage n m k
      (origin_contamination α (gaussian_scale_mixture n))
      (gaussian_scale_mixture n) ≤
      Real.sqrt (Real.exp (C ^ 2 * A) - 1) := by
  have hbase := lda_bound C hCpos hC n m k α hα
  have hx : (0 : ℝ) ≤ C ^ 2 * (α : ℝ) ^ 2 * (k : ℝ) := by positivity
  have hpow : (1 + C ^ 2 * (α : ℝ) ^ 2 * (k : ℝ)) ^ m ≤
      Real.exp ((m : ℝ) * (C ^ 2 * (α : ℝ) ^ 2 * (k : ℝ))) :=
    one_add_pow_le_exp _ hx m
  have hCsq : (0 : ℝ) ≤ C ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hA hCsq
  have hrw : (m : ℝ) * (C ^ 2 * (α : ℝ) ^ 2 * (k : ℝ)) =
      C ^ 2 * ((α : ℝ) ^ 2 * (k : ℝ) * (m : ℝ)) := by ring
  have hexp : Real.exp ((m : ℝ) * (C ^ 2 * (α : ℝ) ^ 2 * (k : ℝ))) ≤
      Real.exp (C ^ 2 * A) := Real.exp_le_exp.mpr (by linarith)
  exact hbase.trans (Real.sqrt_le_sqrt (by linarith))

@[blueprint "thm:lda-bound-is-big-o"
  (statement := /-- Let $C>0$ satisfy \cref{def:gaussian-mean-variance-constant}. For every $n\in\mathbb N$, let $\alpha_n\in[0,1]$ and $m_n,k_n\in\mathbb N$. Suppose that
  \[
    k_n=O\!\left(\frac{1}{\alpha_n^2m_n}\right)
    \qquad(n\to\infty),
  \]
  then, for the measures $Q_n$ and $P_{n,\alpha_n}$ from \cref{def:gaussian-scale-mixture,def:origin-contamination},
  \[
    \operatorname{LDA}^{(m_n)}_{\leq k_n}(P_{n,\alpha_n},Q_n)=O(1)
    \qquad(n\to\infty).
  \] -/)
  (proof := /-- By the definition of the big-$O$ hypothesis there exist a real
  constant $A$ and a set of indices that is eventually true along $n\to\infty$ on
  which
  \[
    \left\lvert k_n\right\rvert
      \leq A\left\lvert\frac{1}{\alpha_n^2m_n}\right\rvert .
  \]
  Put $B=\max(A,0)$, so that $B\geq0$ and the same estimate holds with $A$
  replaced by $B$, because $A\leq B$ and the factor
  $\left\lvert1/(\alpha_n^2m_n)\right\rvert$ is nonnegative.

  We claim that $\alpha_n^2k_nm_n\leq B$ for every index $n$ in that eventual
  set. The quantity $\alpha_n^2m_n$ is nonnegative, so either it vanishes or it
  is positive. If $\alpha_n^2m_n=0$, then
  $\alpha_n^2k_nm_n=k_n\left(\alpha_n^2m_n\right)=0\leq B$. If
  $\alpha_n^2m_n>0$, then $1/(\alpha_n^2m_n)$ and $k_n$ are nonnegative, so the
  displayed estimate reads $k_n\leq B\left(\alpha_n^2m_n\right)^{-1}$;
  multiplying it by the nonnegative quantity $\alpha_n^2m_n$ and cancelling
  $\left(\alpha_n^2m_n\right)^{-1}\alpha_n^2m_n=1$, which is licit since
  $\alpha_n^2m_n\neq0$, gives
  $\alpha_n^2k_nm_n=k_n\left(\alpha_n^2m_n\right)\leq B$.

  Fix such an index $n$. By \cref{lem:lda-le-sqrt-exp-of-degree-bound}, applied
  with $C>0$ satisfying \cref{def:gaussian-mean-variance-constant}, with the
  hypothesis $\alpha_n\leq1$, and with the bound $\alpha_n^2k_nm_n\leq B$ just
  established,
  \[
    \operatorname{LDA}^{(m_n)}_{\leq k_n}(P_{n,\alpha_n},Q_n)
      \leq\sqrt{e^{C^2B}-1}.
  \]
  By \cref{lem:low-degree-advantage-nonnegative}, applied to the measures
  $P_{n,\alpha_n}$ and $Q_n$, the left-hand side is nonnegative, so its absolute
  value equals itself, and $\left\lvert1\right\rvert=1$. Hence
  \[
    \left\lvert\operatorname{LDA}^{(m_n)}_{\leq k_n}(P_{n,\alpha_n},Q_n)\right\rvert
      \leq\sqrt{e^{C^2B}-1}\cdot\left\lvert1\right\rvert
  \]
  holds for all sufficiently large $n$. Since $\sqrt{e^{C^2B}-1}$ does not depend
  on $n$, this is precisely the assertion
  $\operatorname{LDA}^{(m_n)}_{\leq k_n}(P_{n,\alpha_n},Q_n)=O(1)$ as
  $n\to\infty$. -/)
  (title := /-- Constant-order low-degree advantage in the small-degree regime -/)
  (latexEnv := "theorem")]
theorem lda_bound_is_big_o (C : ℝ) (hCpos : 0 < C)
    (hC : gaussian_mean_variance_constant C)
    (α : ℕ → NNReal) (m k : ℕ → ℕ) (hα : ∀ n, α n ≤ 1)
    (hdegree : (fun n ↦ (k n : ℝ)) =O[Filter.atTop]
      (fun n ↦ 1 / ((α n : ℝ) ^ 2 * (m n : ℝ)))) :
    (fun n ↦ low_degree_advantage n (m n) (k n)
      (origin_contamination (α n) (gaussian_scale_mixture n))
      (gaussian_scale_mixture n)) =O[Filter.atTop]
      (fun _ : ℕ ↦ (1 : ℝ)) := by
  obtain ⟨A, hA⟩ := hdegree.bound
  set B : ℝ := max A 0 with hBdef
  have hB0 : (0 : ℝ) ≤ B := le_max_right _ _
  refine IsBigO.of_bound (Real.sqrt (Real.exp (C ^ 2 * B) - 1)) ?_
  filter_upwards [hA] with n hn
  have hn' : ‖(k n : ℝ)‖ ≤ B * ‖1 / ((α n : ℝ) ^ 2 * (m n : ℝ))‖ :=
    hn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hprod : (0 : ℝ) ≤ (α n : ℝ) ^ 2 * (m n : ℝ) := by positivity
  have hkey : (α n : ℝ) ^ 2 * (k n : ℝ) * (m n : ℝ) ≤ B := by
    rcases eq_or_lt_of_le hprod with hzero | hpos
    · have hrw : (α n : ℝ) ^ 2 * (k n : ℝ) * (m n : ℝ) =
          (k n : ℝ) * ((α n : ℝ) ^ 2 * (m n : ℝ)) := by ring
      rw [hrw, ← hzero, mul_zero]
      exact hB0
    · rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity),
        one_div] at hn'
      have hne : (α n : ℝ) ^ 2 * (m n : ℝ) ≠ 0 := ne_of_gt hpos
      have hmul := mul_le_mul_of_nonneg_right hn' hprod
      have hcancel : B * ((α n : ℝ) ^ 2 * (m n : ℝ))⁻¹ * ((α n : ℝ) ^ 2 * (m n : ℝ))
          = B := by rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
      rw [hcancel] at hmul
      have hcomm : (α n : ℝ) ^ 2 * (k n : ℝ) * (m n : ℝ)
          = (k n : ℝ) * ((α n : ℝ) ^ 2 * (m n : ℝ)) := by ring
      rw [hcomm]
      exact hmul
  have hnonneg := low_degree_advantage_nonnegative n (m n) (k n)
    (origin_contamination (α n) (gaussian_scale_mixture n))
    (gaussian_scale_mixture n)
  rw [Real.norm_of_nonneg hnonneg, norm_one, mul_one]
  exact lda_le_sqrt_exp_of_degree_bound C hCpos hC n (m n) (k n) (α n) (hα n) B hkey

import Architect
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

@[blueprint "def:marginal-moment"
  (statement := /-- Let $d \in \mathbb{N}$, let $(\Omega, \mu)$ be a probability space, and let
  $X : \Omega \to \mathbb{R}^d$ be a random vector. For a vector $u \in \mathbb{R}^d$ and a real
  exponent $p \ge 1$, the \emph{marginal moment functional} is defined by
  \[ M_X(u,p) \;:=\; \int_{\Omega} \bigl|\langle u, X(\omega)\rangle\bigr|^{p}\, d\mu(\omega)
  \;\in\; [0,\infty], \]
  the $p$-th absolute moment of the one-dimensional marginal $\langle u, X\rangle$, where
  $\langle \cdot,\cdot\rangle$ denotes the Euclidean inner product on $\mathbb{R}^d$. The integral is
  taken as a lower Lebesgue integral of the nonnegative extended-real-valued integrand. -/)
  (title := /-- Marginal moment functional $M_X(u,p)$ -/)
  (latexEnv := "definition")]
noncomputable def marginal_moment {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d)) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (|⟪u, X ω⟫| ^ p) ∂μ

@[blueprint "def:aggregated-moment"
  (statement := /-- With the marginal moment functional of \cref{def:marginal-moment}, let
  $\mathbb{P}_0$ be a probability measure on $\mathbb{R}^d$ and let $U \sim \mathbb{P}_0$. The
  \emph{aggregated moment} is the expectation of $M_X(U,p)$ under $U \sim \mathbb{P}_0$,
  \[ \mathbb{E}_0\bigl(M_X(U,p)\bigr) \;:=\; \int_{\mathbb{R}^d} M_X(u,p)\, d\mathbb{P}_0(u)
  \;\in\; [0,\infty], \]
  again taken as a lower Lebesgue integral of a nonnegative extended-real-valued integrand. -/)
  (title := /-- Aggregated moment $\mathbb{E}_0(M_X(U,p))$ -/)
  (latexEnv := "definition")]
noncomputable def aggregated_moment {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → EuclideanSpace ℝ (Fin d))
    (P₀ : Measure (EuclideanSpace ℝ (Fin d))) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, marginal_moment μ X u p ∂P₀

@[blueprint "def:norm-pth-moment"
  (statement := /-- Let $d \in \mathbb{N}$, let $(\Omega, \mu)$ be a probability space, let
  $\|\cdot\|$ be a seminorm on $\mathbb{R}^d$ (modelling the prescribed norm of the ambient space),
  and let $X : \Omega \to \mathbb{R}^d$ be a random vector. For a real exponent $p \ge 1$ the
  \emph{norm $p$-th moment} is
  \[ \mathbb{E}\bigl(\|X\|^{p}\bigr) \;:=\; \int_{\Omega} \|X(\omega)\|^{p}\, d\mu(\omega)
  \;\in\; [0,\infty], \]
  taken as a lower Lebesgue integral of the nonnegative extended-real-valued integrand. -/)
  (title := /-- Norm $p$-th moment $\mathbb{E}(\|X\|^p)$ -/)
  (latexEnv := "definition")]
noncomputable def norm_pth_moment {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (nrm : Seminorm ℝ (EuclideanSpace ℝ (Fin d)))
    (X : Ω → EuclideanSpace ℝ (Fin d)) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (nrm (X ω) ^ p) ∂μ

@[blueprint "def:nu-measure"
  (statement := /-- Let $\|\cdot\|$ be a seminorm on $\mathbb{R}^d$ with unit ball
  $\mathcal{B} := \{y \in \mathbb{R}^d : \|y\| \le 1\}$, let $\partial\mathcal{B}$ denote its
  topological frontier, and let $\mathbb{P}_0$ be a probability measure on $\mathbb{R}^d$ with
  $U \sim \mathbb{P}_0$. The covering quantity controlling $\mathbb{P}_0$ is
  \[ \nu(\mathbb{P}_0) \;:=\; \sup_{x \in \partial\mathcal{B}}
  \frac{1}{\mathbb{P}_0\bigl(|\langle U, x\rangle| \ge 1\bigr)} \;\in\; [0,\infty], \]
  the supremum over boundary directions of the reciprocal mass placed by $\mathbb{P}_0$ on the slab
  $\{u : |\langle u, x\rangle| \ge 1\}$. -/)
  (title := /-- Covering quantity $\nu(\mathbb{P}_0)$ -/)
  (latexEnv := "definition")]
noncomputable def nu_measure {d : ℕ} (nrm : Seminorm ℝ (EuclideanSpace ℝ (Fin d)))
    (P₀ : Measure (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  ⨆ x ∈ frontier {y : EuclideanSpace ℝ (Fin d) | nrm y ≤ 1},
    1 / P₀ {u : EuclideanSpace ℝ (Fin d) | 1 ≤ |⟪u, x⟫|}

@[blueprint "def:tail-bound-value"
  (statement := /-- With the aggregated moment of \cref{def:aggregated-moment} and the covering
  quantity of \cref{def:nu-measure}, and given a confidence parameter $t \ge 0$, the optimized
  tail-bound value is
  \[ \Phi(t) \;:=\; \inf_{\substack{\mathbb{P}_0 :\, \nu(\mathbb{P}_0) < \infty}}\;\inf_{p \ge 1} \; e^{t/p}\,
  \bigl(\mathbb{E}_0(M_X(U,p))\bigr)^{1/p}\, \nu(\mathbb{P}_0)^{1/p} \;\in\; [0,\infty], \]
  the joint infimum, over all \emph{admissible} probability measures $\mathbb{P}_0$ on
  $\mathbb{R}^d$ — those whose covering quantity is finite, $\nu(\mathbb{P}_0) < \infty$ — and over
  all real exponents $p \ge 1$, of the per-pair bound
  $e^{t/p}(\mathbb{E}_0(M_X(U,p)))^{1/p} \nu(\mathbb{P}_0)^{1/p}$. The admissibility restriction
  $\nu(\mathbb{P}_0) < \infty$ is the non-degeneracy condition under which the per-pair bound is
  meaningful; it is exactly the hypothesis carried by \cref{lem:single-exponent-tail-bound}, and
  without it a degenerate aggregating measure (for instance a Dirac mass concentrating
  $\langle U, X\rangle$ at $0$) would force the infimum to collapse to $0$ in $[0,\infty]$. The
  optimization over the aggregating measure $\mathbb{P}_0$ is the variational content of the bound;
  here both the aggregated moment $\mathbb{E}_0(M_X(U,p))$ of \cref{def:aggregated-moment} and the
  covering quantity $\nu(\mathbb{P}_0)$ of \cref{def:nu-measure} depend on $\mathbb{P}_0$. -/)
  (title := /-- Optimized tail-bound value $\Phi(t)$ -/)
  (latexEnv := "definition")]
noncomputable def tail_bound_value {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (nrm : Seminorm ℝ (EuclideanSpace ℝ (Fin d)))
    (X : Ω → EuclideanSpace ℝ (Fin d)) (t : ℝ) : ℝ≥0∞ :=
  ⨅ P₀ ∈ {ν : Measure (EuclideanSpace ℝ (Fin d)) |
      IsProbabilityMeasure ν ∧ nu_measure nrm ν ≠ ⊤},
    ⨅ p ∈ Set.Ici (1 : ℝ),
      ENNReal.ofReal (Real.exp (t / p))
        * aggregated_moment μ X P₀ p ^ (1 / p)
        * nu_measure nrm P₀ ^ (1 / p)

@[blueprint "lem:seminorm-frontier-mem"
  (statement := /-- Let $d \in \mathbb{N}$, let $\|\cdot\|$ be a seminorm on $\mathbb{R}^d$, and let
  $x \in \mathbb{R}^d$ satisfy $\|x\| = 1$. Then $x$ belongs to the topological frontier of the closed
  unit ball $\{y \in \mathbb{R}^d : \|y\| \le 1\}$. -/)
  (proof := /-- Let $\mathcal{B} := \{y \in \mathbb{R}^d : \|y\| \le 1\}$. The frontier of
  $\mathcal{B}$ equals $\overline{\mathcal{B}} \cap \overline{\mathcal{B}^{c}}$, so it suffices to
  prove $x \in \overline{\mathcal{B}}$ and $x \in \overline{\mathcal{B}^{c}}$. Since $\|x\| = 1 \le 1$
  we have $x \in \mathcal{B} \subseteq \overline{\mathcal{B}}$. For the second membership, consider the
  curve $t \mapsto (1+t)x$ for $t > 0$; by positive homogeneity of the seminorm
  $\|(1+t)x\| = |1+t|\,\|x\| = 1 + t > 1$, so $(1+t)x \in \mathcal{B}^{c}$ for every $t > 0$. As
  $t \to 0^{+}$ this curve converges to $x$, whence $x \in \overline{\mathcal{B}^{c}}$. Therefore
  $x$ lies in the frontier of $\mathcal{B}$. -/)
  (title := /-- Unit-seminorm vectors lie on the frontier of the unit ball -/)
  (latexEnv := "lemma")]
lemma seminorm_frontier_mem {d : ℕ}
    (nrm : Seminorm ℝ (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) (hx : nrm x = 1) :
    x ∈ frontier {y : EuclideanSpace ℝ (Fin d) | nrm y ≤ 1} := by
  rw [frontier_eq_closure_inter_closure]
  refine ⟨subset_closure ?_, ?_⟩
  · show nrm x ≤ 1
    exact le_of_eq hx
  · have hcont : Continuous (fun t : ℝ => (1 + t) • x) :=
      (continuous_const.add continuous_id).smul continuous_const
    have htend : Filter.Tendsto (fun t : ℝ => (1 + t) • x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds x) := by
      have h1 := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      simpa using h1
    refine mem_closure_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : (0:ℝ) < t := ht
    show (1 + t) • x ∈ {y : EuclideanSpace ℝ (Fin d) | nrm y ≤ 1}ᶜ
    rw [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, map_smul_eq_mul, hx, mul_one,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith

@[blueprint "lem:moment-bound-pointwise"
  (statement := /-- Let $d \in \mathbb{N}$, let $\|\cdot\|$ be a seminorm on $\mathbb{R}^d$, let
  $\mathbb{P}_0$ be a probability measure on $\mathbb{R}^d$ satisfying the non-degeneracy condition
  $\nu(\mathbb{P}_0) < \infty$ of \cref{def:nu-measure}, and let $p \ge 1$ be a real exponent. Then for
  every $v \in \mathbb{R}^d$,
  \[ \|v\|^{p} \;\le\; \Bigl(\int_{\mathbb{R}^d} |\langle u, v\rangle|^{p}\, d\mathbb{P}_0(u)\Bigr)\,
  \nu(\mathbb{P}_0), \]
  where the power and the integral are taken in $[0,\infty]$ through the extended-nonnegative-real
  coercion. -/)
  (proof := /-- Fix $v \in \mathbb{R}^d$. If $\|v\| = 0$ then, since $p \ge 1 > 0$, we have
  $\|v\|^{p} = 0$, so the left-hand side is $0$ and the inequality holds trivially. Assume
  $\|v\| > 0$ and set $x := \|v\|^{-1} v$, so that $\|x\| = \bigl|\|v\|^{-1}\bigr|\,\|v\| = 1$ by
  positive homogeneity of the seminorm. By \cref{lem:seminorm-frontier-mem}, $x$ lies in the frontier
  $\partial\mathcal{B}$ of the unit ball $\mathcal{B} = \{y : \|y\| \le 1\}$. Writing
  $S := \{u : |\langle u, x\rangle| \ge 1\}$, the definition of $\nu(\mathbb{P}_0)$ in
  \cref{def:nu-measure} gives $1/\mathbb{P}_0(S) \le \nu(\mathbb{P}_0)$. Because $\nu(\mathbb{P}_0) <
  \infty$, this forces $\mathbb{P}_0(S) > 0$, and $\mathbb{P}_0(S) \le 1 < \infty$. For $u \in S$ we
  have $\langle u, x\rangle = \|v\|^{-1}\langle u, v\rangle$, hence
  $|\langle u, v\rangle| = \|v\|\,|\langle u, x\rangle| \ge \|v\|$, and therefore
  $|\langle u, v\rangle|^{p} \ge \|v\|^{p}$ since $t \mapsto t^{p}$ is nondecreasing on
  $[0,\infty)$. Integrating this pointwise bound over $S$ yields
  $\int_{\mathbb{R}^d} |\langle u, v\rangle|^{p}\, d\mathbb{P}_0(u) \ge \int_S |\langle u, v\rangle|^{p}
  \, d\mathbb{P}_0(u) \ge \|v\|^{p}\,\mathbb{P}_0(S)$. Multiplying by $\nu(\mathbb{P}_0) \ge
  1/\mathbb{P}_0(S)$ and cancelling $\mathbb{P}_0(S)\,\mathbb{P}_0(S)^{-1} = 1$ gives
  $\|v\|^{p} \le \bigl(\int_{\mathbb{R}^d} |\langle u, v\rangle|^{p}\, d\mathbb{P}_0(u)\bigr)\,
  \nu(\mathbb{P}_0)$, as claimed. -/)
  (title := /-- Pointwise moment bound for a fixed vector -/)
  (latexEnv := "lemma")]
lemma moment_bound_pointwise {d : ℕ}
    (nrm : Seminorm ℝ (EuclideanSpace ℝ (Fin d)))
    (P₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P₀]
    (hnu : nu_measure nrm P₀ ≠ ⊤)
    (p : ℝ) (hp : 1 ≤ p)
    (v : EuclideanSpace ℝ (Fin d)) :
    ENNReal.ofReal (nrm v ^ p)
      ≤ (∫⁻ u, ENNReal.ofReal (|⟪u, v⟫| ^ p) ∂P₀) * nu_measure nrm P₀ := by
  have hp0 : (0:ℝ) ≤ p := le_trans zero_le_one hp
  have hrpow : Measurable (fun a : ℝ≥0∞ => a ^ p) :=
    Monotone.measurable (fun a b hab => ENNReal.rpow_le_rpow hab hp0)
  have hg : Measurable fun u : EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal (|⟪u, v⟫| ^ p) := by
    have hbase : Measurable fun u : EuclideanSpace ℝ (Fin d) => ENNReal.ofReal |⟪u, v⟫| :=
      (continuous_abs.measurable.comp (measurable_id.inner measurable_const)).ennreal_ofReal
    simp_rw [fun u : EuclideanSpace ℝ (Fin d) =>
      (ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (⟪u, v⟫)) hp0).symm]
    exact hrpow.comp hbase
  rcases eq_or_lt_of_le (apply_nonneg nrm v) with hr | hr
  · rw [hr.symm, Real.zero_rpow (zero_lt_one.trans_le hp).ne', ENNReal.ofReal_zero]
    exact zero_le'
  · set r := nrm v with hrdef
    set x := (r⁻¹ : ℝ) • v with hxdef
    have hnrmx : nrm x = 1 := by
      rw [hxdef, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), ← hrdef,
        inv_mul_cancel₀ (ne_of_gt hr)]
    have hxfront : x ∈ frontier {y : EuclideanSpace ℝ (Fin d) | nrm y ≤ 1} :=
      seminorm_frontier_mem nrm x hnrmx
    set S := {u : EuclideanSpace ℝ (Fin d) | 1 ≤ |⟪u, x⟫|} with hSdef
    have hle : 1 / P₀ S ≤ nu_measure nrm P₀ := by
      simp only [nu_measure]
      exact le_iSup₂ (f := fun y _ => 1 / P₀ {u : EuclideanSpace ℝ (Fin d) | 1 ≤ |⟪u, y⟫|})
        x hxfront
    have hPfin : P₀ S ≠ ⊤ := measure_ne_top P₀ S
    have hPpos : P₀ S ≠ 0 := by
      intro h0
      apply hnu
      rw [h0, one_div, ENNReal.inv_zero] at hle
      exact top_le_iff.mp hle
    have hint : ENNReal.ofReal (r ^ p) * P₀ S
        ≤ ∫⁻ u, ENNReal.ofReal (|⟪u, v⟫| ^ p) ∂P₀ := by
      calc ENNReal.ofReal (r ^ p) * P₀ S
          = ∫⁻ _ in S, ENNReal.ofReal (r ^ p) ∂P₀ := (setLIntegral_const S _).symm
        _ ≤ ∫⁻ u in S, ENNReal.ofReal (|⟪u, v⟫| ^ p) ∂P₀ := by
            refine setLIntegral_mono hg ?_
            intro u hu
            have huS : (1:ℝ) ≤ |⟪u, x⟫| := hu
            apply ENNReal.ofReal_le_ofReal
            apply Real.rpow_le_rpow (le_of_lt hr) ?_ hp0
            have hxu : ⟪u, x⟫ = r⁻¹ * ⟪u, v⟫ := by
              rw [hxdef]; exact real_inner_smul_right u v r⁻¹
            have h1 : |⟪u, v⟫| = r * |⟪u, x⟫| := by
              rw [hxu, abs_mul, abs_of_pos (inv_pos.mpr hr), ← mul_assoc,
                mul_inv_cancel₀ (ne_of_gt hr), one_mul]
            rw [h1]
            calc r = r * 1 := (mul_one r).symm
              _ ≤ r * |⟪u, x⟫| := mul_le_mul_of_nonneg_left huS (le_of_lt hr)
        _ ≤ ∫⁻ u, ENNReal.ofReal (|⟪u, v⟫| ^ p) ∂P₀ := setLIntegral_le_lintegral S _
    calc ENNReal.ofReal (r ^ p)
        = ENNReal.ofReal (r ^ p) * (P₀ S * (P₀ S)⁻¹) := by
          rw [ENNReal.mul_inv_cancel hPpos hPfin, mul_one]
      _ = ENNReal.ofReal (r ^ p) * P₀ S * (P₀ S)⁻¹ := by rw [mul_assoc]
      _ ≤ (∫⁻ u, ENNReal.ofReal (|⟪u, v⟫| ^ p) ∂P₀) * (P₀ S)⁻¹ :=
          mul_le_mul_right' hint _
      _ ≤ (∫⁻ u, ENNReal.ofReal (|⟪u, v⟫| ^ p) ∂P₀) * nu_measure nrm P₀ := by
          apply mul_le_mul_left'
          rw [← one_div]; exact hle

@[blueprint "thm:moment-bound"
  (statement := /-- Let $d \in \mathbb{N}$, let $(\Omega, \mu)$ be a probability space, let
  $\|\cdot\|$ be a seminorm on $\mathbb{R}^d$, let $X : \Omega \to \mathbb{R}^d$ be a measurable
  random vector, let $\mathbb{P}_0$ be a probability measure on $\mathbb{R}^d$ with
  $U \sim \mathbb{P}_0$ satisfying the non-degeneracy condition $\nu(\mathbb{P}_0) < \infty$, and
  let $p \ge 1$ be a real exponent. Then, with the notation of
  \cref{def:marginal-moment,def:aggregated-moment,def:norm-pth-moment,def:nu-measure},
  \[ \mathbb{E}\bigl(\|X\|^{p}\bigr) \;\le\; \mathbb{E}_0\bigl(M_X(U,p)\bigr)\, \nu(\mathbb{P}_0). \] -/)
  (proof := /-- Unfolding the norm $p$-th moment of \cref{def:norm-pth-moment}, the left-hand side is
  $\mathbb{E}(\|X\|^{p}) = \int_{\Omega} \|X(\omega)\|^{p}\, d\mu(\omega)$, an integral in
  $[0,\infty]$ of the extended-nonnegative-real integrand $\omega \mapsto \|X(\omega)\|^{p}$. Fix
  $\omega \in \Omega$ and apply the pointwise bound of \cref{lem:moment-bound-pointwise} to the vector
  $v = X(\omega)$: under the non-degeneracy hypothesis $\nu(\mathbb{P}_0) < \infty$ it gives
  \[ \|X(\omega)\|^{p} \;\le\; \Bigl(\int_{\mathbb{R}^d} |\langle u, X(\omega)\rangle|^{p}\,
  d\mathbb{P}_0(u)\Bigr)\, \nu(\mathbb{P}_0). \]
  Integrating this inequality over $\omega \in \Omega$ under $\mu$ and using monotonicity of the
  lower Lebesgue integral yields
  $\mathbb{E}(\|X\|^{p}) \le \int_{\Omega}\bigl(\int_{\mathbb{R}^d} |\langle u, X(\omega)\rangle|^{p}
  \, d\mathbb{P}_0(u)\bigr) d\mu(\omega)\,\nu(\mathbb{P}_0)$, where the constant factor
  $\nu(\mathbb{P}_0)$ is pulled out of the integral. By Tonelli's theorem the nonnegative integrand
  $(u,\omega) \mapsto |\langle u, X(\omega)\rangle|^{p}$, which is jointly measurable because $X$ is
  measurable, may have its order of integration exchanged, giving
  $\int_{\Omega}\int_{\mathbb{R}^d} |\langle u, X(\omega)\rangle|^{p}\, d\mathbb{P}_0(u)\, d\mu(\omega)
  = \int_{\mathbb{R}^d}\int_{\Omega} |\langle u, X(\omega)\rangle|^{p}\, d\mu(\omega)\, d\mathbb{P}_0(u)$.
  The inner integral is the marginal moment $M_X(u,p)$ of \cref{def:marginal-moment}, and the outer
  integral is the aggregated moment $\mathbb{E}_0(M_X(U,p))$ of \cref{def:aggregated-moment}. Therefore
  $\mathbb{E}(\|X\|^{p}) \le \mathbb{E}_0(M_X(U,p))\,\nu(\mathbb{P}_0)$. -/)
  (title := /-- Moment bound for the norm of a random vector -/)
  (latexEnv := "theorem")]
theorem moment_bound {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (nrm : Seminorm ℝ (EuclideanSpace ℝ (Fin d)))
    (X : Ω → EuclideanSpace ℝ (Fin d)) (hX : Measurable X)
    (P₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P₀]
    (hnu : nu_measure nrm P₀ ≠ ⊤)
    (p : ℝ) (hp : 1 ≤ p) :
    norm_pth_moment μ nrm X p ≤ aggregated_moment μ X P₀ p * nu_measure nrm P₀ := by
  have hp0 : (0:ℝ) ≤ p := le_trans zero_le_one hp
  have hrpow : Measurable (fun a : ℝ≥0∞ => a ^ p) :=
    Monotone.measurable (fun a b hab => ENNReal.rpow_le_rpow hab hp0)
  have hmeas : Measurable fun z : Ω × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal (|⟪z.2, X z.1⟫| ^ p) := by
    have hbase : Measurable fun z : Ω × EuclideanSpace ℝ (Fin d) =>
        ENNReal.ofReal |⟪z.2, X z.1⟫| :=
      (continuous_abs.measurable.comp
        (measurable_snd.inner (hX.comp measurable_fst))).ennreal_ofReal
    simp_rw [fun z : Ω × EuclideanSpace ℝ (Fin d) =>
      (ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (⟪z.2, X z.1⟫)) hp0).symm]
    exact hrpow.comp hbase
  calc norm_pth_moment μ nrm X p
      = ∫⁻ ω, ENNReal.ofReal (nrm (X ω) ^ p) ∂μ := rfl
    _ ≤ ∫⁻ ω, (∫⁻ u, ENNReal.ofReal (|⟪u, X ω⟫| ^ p) ∂P₀) * nu_measure nrm P₀ ∂μ := by
        refine lintegral_mono (fun ω => ?_)
        exact moment_bound_pointwise nrm P₀ hnu p hp (X ω)
    _ = (∫⁻ ω, ∫⁻ u, ENNReal.ofReal (|⟪u, X ω⟫| ^ p) ∂P₀ ∂μ) * nu_measure nrm P₀ := by
        rw [lintegral_mul_const]
        exact (hmeas.lintegral_prod_right')
    _ = (∫⁻ u, ∫⁻ ω, ENNReal.ofReal (|⟪u, X ω⟫| ^ p) ∂μ ∂P₀) * nu_measure nrm P₀ := by
        rw [lintegral_lintegral_swap hmeas.aemeasurable]
    _ = aggregated_moment μ X P₀ p * nu_measure nrm P₀ := rfl

@[blueprint "lem:seminorm-continuous-euclidean"
  (statement := /-- Let $d \in \mathbb{N}$ and let $\|\cdot\|$ be a seminorm on the Euclidean space
  $\mathbb{R}^d$. Then the seminorm, regarded as a map $\mathbb{R}^d \to \mathbb{R}$, is continuous. -/)
  (proof := /-- Write $e_i := \mathrm{single}(i,1)$ for the standard basis vectors of $\mathbb{R}^d$
  and set $C := \sum_{i} \|e_i\|$; note $C \ge 0$ as a sum of nonnegative terms. First, every vector
  $x \in \mathbb{R}^d$ satisfies $x = \sum_i x_i\, e_i$, so by subadditivity of the seminorm and its
  homogeneity $\|x\| \le \sum_i \|x_i\, e_i\| = \sum_i |x_i|\,\|e_i\|$. Since $|x_i| \le \|x\|$ for the
  Euclidean norm, this gives $\|x\| \le \sum_i \|x\|\,\|e_i\| = C\,\|x\|$. Consequently, by the reverse
  triangle inequality for seminorms, for all $x,y$ we have
  $\bigl|\,\|x\| - \|y\|\,\bigr| \le \|x - y\| \le C\,\|x-y\|$, so the seminorm is Lipschitz with
  constant $C$ and therefore continuous. -/)
  (title := /-- Continuity of a seminorm on Euclidean space -/)
  (latexEnv := "lemma")]
lemma seminorm_continuous_euclidean {d : ℕ}
    (nrm : Seminorm ℝ (EuclideanSpace ℝ (Fin d))) :
    Continuous (nrm : EuclideanSpace ℝ (Fin d) → ℝ) := by
  set C : ℝ := ∑ i : Fin d, nrm (EuclideanSpace.single i (1 : ℝ)) with hC
  have hsum : ∀ f : Fin d → EuclideanSpace ℝ (Fin d), nrm (∑ i, f i) ≤ ∑ i, nrm (f i) :=
    fun f => Finset.le_sum_of_subadditive nrm (map_zero nrm).le
      (fun a b => map_add_le_add nrm a b) _ _
  have hcoord : ∀ (x : EuclideanSpace ℝ (Fin d)) (i : Fin d), |x i| ≤ ‖x‖ := by
    intro x i
    have := PiLp.norm_apply_le x i
    simpa [Real.norm_eq_abs] using this
  have hbound : ∀ x : EuclideanSpace ℝ (Fin d), nrm x ≤ C * ‖x‖ := by
    intro x
    calc nrm x = nrm (∑ i : Fin d, (x i) • EuclideanSpace.single i (1 : ℝ)) := by
          congr 1
          have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x
          simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using this.symm
      _ ≤ ∑ i : Fin d, nrm ((x i) • EuclideanSpace.single i (1 : ℝ)) := hsum _
      _ = ∑ i : Fin d, |x i| * nrm (EuclideanSpace.single i (1 : ℝ)) := by
          simp [map_smul_eq_mul]
      _ ≤ ∑ i : Fin d, ‖x‖ * nrm (EuclideanSpace.single i (1 : ℝ)) :=
          Finset.sum_le_sum
            (fun i _ => mul_le_mul_of_nonneg_right (hcoord x i) (apply_nonneg _ _))
      _ = C * ‖x‖ := by rw [hC, Finset.sum_mul]; congr 1; ext i; ring
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun i _ => apply_nonneg _ _)
  have hlip : LipschitzWith C.toNNReal (nrm : EuclideanSpace ℝ (Fin d) → ℝ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    calc |nrm x - nrm y| ≤ nrm (x - y) := nrm.norm_sub_map_le_sub x y
      _ ≤ C * ‖x - y‖ := hbound _
      _ = (C.toNNReal : ℝ) * dist x y := by rw [Real.coe_toNNReal C hC0, dist_eq_norm]
  exact hlip.continuous

@[blueprint "lem:single-exponent-tail-bound"
  (statement := /-- Under the hypotheses of \cref{thm:moment-bound}, fix a real exponent $p \ge 1$
  and a confidence parameter $t \ge 0$. Then, with probability at least $1 - e^{-t}$,
  \[ \|X\| \;\le\; e^{t/p}\,\bigl(\mathbb{E}_0(M_X(U,p))\bigr)^{1/p}\, \nu(\mathbb{P}_0)^{1/p}; \]
  equivalently, writing $C_p := e^{t/p}(\mathbb{E}_0(M_X(U,p)))^{1/p}\nu(\mathbb{P}_0)^{1/p}$, the
  event $\{\omega : \|X(\omega)\| \le C_p\}$ has $\mu$-measure at least $1 - e^{-t}$. -/)
  (proof := /-- Write $C := e^{t/p}(\mathbb{E}_0(M_X(U,p)))^{1/p}\nu(\mathbb{P}_0)^{1/p}$ and set
  $E := e^{t}$ and $M := \mathbb{E}_0(M_X(U,p))\,\nu(\mathbb{P}_0)$. Since $p \ge 1 > 0$, a direct
  computation with real powers gives $C^{p} = E\cdot M$, and moreover $e^{-t} = E^{-1}$. The map
  $\omega \mapsto \|X(\omega)\|$ is measurable because the seminorm is continuous on the
  finite-dimensional space $\mathbb{R}^d$ by \cref{lem:seminorm-continuous-euclidean}; hence
  $g(\omega) := \|X(\omega)\|^{p}$, read in $[0,\infty]$, is measurable and its lower Lebesgue
  integral equals $\mathbb{E}(\|X\|^{p})$, which by \cref{thm:moment-bound} is at most $M$. Let
  $S := \{\omega : \|X(\omega)\| \le C\}$; it suffices to prove $\mu(S^{c}) \le E^{-1}$, because then
  $1 = \mu(S) + \mu(S^{c}) \le \mu(S) + E^{-1}$ yields $1 - E^{-1} \le \mu(S)$. We bound $\mu(S^{c})$
  by cases on $M$. If $M = \infty$, then $C^{p} = E\cdot M = \infty$, so $C = \infty$ and
  $S^{c} = \{\omega : \infty < \|X(\omega)\|\} = \varnothing$, giving $\mu(S^{c}) = 0 \le E^{-1}$. If
  $M = 0$, then $\int_{\Omega} g\,d\mu \le M = 0$, so $g = 0$ almost everywhere; since
  $C < \|X(\omega)\|$ forces $\|X(\omega)\| > 0$ and hence $g(\omega) > 0$, we get
  $S^{c} \subseteq \{g \ne 0\}$, a $\mu$-null set, so again $\mu(S^{c}) = 0 \le E^{-1}$. Finally, if
  $0 < M < \infty$, then $E\cdot M$ is finite and nonzero, and since $x \mapsto x^{p}$ is strictly
  increasing, $C < \|X(\omega)\|$ implies $E\cdot M = C^{p} \le g(\omega)$; thus by Markov's
  inequality $\mu(S^{c}) \le \mu\{\omega : E\cdot M \le g(\omega)\}
  \le \bigl(\int_{\Omega} g\,d\mu\bigr)/(E\cdot M) \le M/(E\cdot M) = E^{-1}$. -/)
  (title := /-- Single-exponent tail bound -/)
  (latexEnv := "lemma")]
lemma single_exponent_tail_bound {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (nrm : Seminorm ℝ (EuclideanSpace ℝ (Fin d)))
    (X : Ω → EuclideanSpace ℝ (Fin d)) (hX : Measurable X)
    (P₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P₀]
    (hnu : nu_measure nrm P₀ ≠ ⊤)
    (t : ℝ) (ht : 0 ≤ t) (p : ℝ) (hp : 1 ≤ p) :
    1 - ENNReal.ofReal (Real.exp (-t))
      ≤ μ {ω | ENNReal.ofReal (nrm (X ω))
          ≤ ENNReal.ofReal (Real.exp (t / p))
              * aggregated_moment μ X P₀ p ^ (1 / p)
              * nu_measure nrm P₀ ^ (1 / p)} := by
  have hp0 : (0 : ℝ) ≤ p := le_trans zero_le_one hp
  have p0 : (0 : ℝ) < p := lt_of_lt_of_le one_pos hp
  set A := aggregated_moment μ X P₀ p with hAdef
  set ν := nu_measure nrm P₀ with hνdef
  set K := ENNReal.ofReal (Real.exp (t / p)) with hKdef
  set C := K * A ^ (1 / p) * ν ^ (1 / p) with hCdef
  set E := ENNReal.ofReal (Real.exp t) with hEdef
  have hEne0 : E ≠ 0 := by
    rw [hEdef]; exact (ENNReal.ofReal_pos.mpr (Real.exp_pos t)).ne'
  have hEtop : E ≠ ⊤ := by rw [hEdef]; exact ENNReal.ofReal_ne_top
  have hent : ENNReal.ofReal (Real.exp (-t)) = E⁻¹ := by
    rw [Real.exp_neg, ENNReal.ofReal_inv_of_pos (Real.exp_pos t), ← hEdef]
  have hCp : C ^ p = E * (A * ν) := by
    have hApow : (A ^ (1 / p)) ^ p = A := by
      rw [← ENNReal.rpow_mul, one_div_mul_cancel (ne_of_gt p0), ENNReal.rpow_one]
    have hνpow : (ν ^ (1 / p)) ^ p = ν := by
      rw [← ENNReal.rpow_mul, one_div_mul_cancel (ne_of_gt p0), ENNReal.rpow_one]
    have hKpow : K ^ p = E := by
      rw [hKdef, ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul,
        div_mul_cancel₀ t (ne_of_gt p0), ← hEdef]
    rw [hCdef, ENNReal.mul_rpow_of_nonneg _ _ hp0, ENNReal.mul_rpow_of_nonneg _ _ hp0,
      hApow, hνpow, hKpow, mul_assoc]
  have e4 : Measurable (fun ω => ENNReal.ofReal (nrm (X ω))) :=
    ((seminorm_continuous_euclidean nrm).measurable.comp hX).ennreal_ofReal
  have hrpow : Measurable (fun a : ℝ≥0∞ => a ^ p) :=
    Monotone.measurable (fun a b hab => ENNReal.rpow_le_rpow hab hp0)
  have hgp : Measurable (fun ω => ENNReal.ofReal (nrm (X ω)) ^ p) := hrpow.comp e4
  have hmom : (∫⁻ ω, ENNReal.ofReal (nrm (X ω)) ^ p ∂μ) ≤ A * ν := by
    have hmb := moment_bound μ nrm X hX P₀ hnu p hp
    have heq : (∫⁻ ω, ENNReal.ofReal (nrm (X ω)) ^ p ∂μ) = norm_pth_moment μ nrm X p := by
      unfold norm_pth_moment
      refine lintegral_congr (fun ω => ?_)
      rw [ENNReal.ofReal_rpow_of_nonneg (apply_nonneg _ _) hp0]
    rw [heq]; exact hmb
  have key : μ {ω | ENNReal.ofReal (nrm (X ω)) ≤ C}ᶜ ≤ E⁻¹ := by
    rcases eq_or_ne (A * ν) ⊤ with hMtop | hMtop
    · have hCtop : C = ⊤ := by
        by_contra hCne
        have h1 : C ^ p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp0 hCne
        rw [hCp, hMtop, ENNReal.mul_top hEne0] at h1
        exact h1 rfl
      have hemp : {ω | ENNReal.ofReal (nrm (X ω)) ≤ C}ᶜ = ∅ := by
        ext ω
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
          not_not, hCtop, le_top]
      rw [hemp, measure_empty]
      exact zero_le'
    · rcases eq_or_ne (A * ν) 0 with hM0 | hM0
      · have hzero : (∫⁻ ω, ENNReal.ofReal (nrm (X ω)) ^ p ∂μ) = 0 :=
          le_antisymm (by rw [← hM0]; exact hmom) (zero_le')
        have hae : (fun ω => ENNReal.ofReal (nrm (X ω)) ^ p) =ᵐ[μ] 0 :=
          (lintegral_eq_zero_iff hgp).1 hzero
        have hnull : μ {ω | ENNReal.ofReal (nrm (X ω)) ^ p ≠ 0} = 0 := by
          have h := hae
          rw [Filter.EventuallyEq, ae_iff] at h
          simpa using h
        have hsub : {ω | ENNReal.ofReal (nrm (X ω)) ≤ C}ᶜ
            ⊆ {ω | ENNReal.ofReal (nrm (X ω)) ^ p ≠ 0} := by
          intro ω hω
          simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
          have hpos : 0 < ENNReal.ofReal (nrm (X ω)) := lt_of_le_of_lt (zero_le') hω
          simp only [Set.mem_setOf_eq]
          exact (ENNReal.rpow_pos_of_nonneg hpos hp0).ne'
        exact le_trans (le_trans (measure_mono hsub) (le_of_eq hnull)) zero_le'
      · have hεne0 : E * (A * ν) ≠ 0 := mul_ne_zero hEne0 hM0
        have hεtop : E * (A * ν) ≠ ⊤ := ENNReal.mul_ne_top hEtop hMtop
        have hsub : {ω | ENNReal.ofReal (nrm (X ω)) ≤ C}ᶜ
            ⊆ {ω | E * (A * ν) ≤ ENNReal.ofReal (nrm (X ω)) ^ p} := by
          intro ω hω
          simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
          have hlt : C ^ p < ENNReal.ofReal (nrm (X ω)) ^ p := ENNReal.rpow_lt_rpow hω p0
          rw [hCp] at hlt
          exact le_of_lt hlt
        calc μ {ω | ENNReal.ofReal (nrm (X ω)) ≤ C}ᶜ
            ≤ μ {ω | E * (A * ν) ≤ ENNReal.ofReal (nrm (X ω)) ^ p} := measure_mono hsub
          _ ≤ (∫⁻ ω, ENNReal.ofReal (nrm (X ω)) ^ p ∂μ) / (E * (A * ν)) :=
              meas_ge_le_lintegral_div hgp.aemeasurable hεne0 hεtop
          _ ≤ E⁻¹ := by
              rw [ENNReal.div_le_iff hεne0 hεtop]
              calc (∫⁻ ω, ENNReal.ofReal (nrm (X ω)) ^ p ∂μ)
                  ≤ A * ν := hmom
                _ = E⁻¹ * (E * (A * ν)) := by
                    rw [← mul_assoc, ENNReal.inv_mul_cancel hEne0 hEtop, one_mul]
  have hSmeas : MeasurableSet {ω | ENNReal.ofReal (nrm (X ω)) ≤ C} :=
    measurableSet_le e4 measurable_const
  have hprob : μ {ω | ENNReal.ofReal (nrm (X ω)) ≤ C}
      + μ {ω | ENNReal.ofReal (nrm (X ω)) ≤ C}ᶜ = 1 := prob_add_prob_compl hSmeas
  rw [hent, tsub_le_iff_right]
  calc (1 : ℝ≥0∞)
      = μ {ω | ENNReal.ofReal (nrm (X ω)) ≤ C}
        + μ {ω | ENNReal.ofReal (nrm (X ω)) ≤ C}ᶜ := hprob.symm
    _ ≤ μ {ω | ENNReal.ofReal (nrm (X ω)) ≤ C} + E⁻¹ := by gcongr

@[blueprint "lem:measure-le-sInf"
  (statement := /-- Let $(\Omega,\mu)$ be a probability space and let $g : \Omega \to [0,\infty]$ be
  a measurable function into the extended nonnegative reals. Let $V \subseteq [0,\infty]$ be a set of
  thresholds and let $c \in [0,\infty]$ satisfy $c \le 1$. Suppose that for every $K \in V$ the event
  $\{\omega : g(\omega) \le K\}$ has $\mu$-measure at least $c$. Then the event
  $\{\omega : g(\omega) \le \inf V\}$ governed by the infimum threshold $\inf V$ also has
  $\mu$-measure at least $c$. -/)
  (proof := /-- If $V = \varnothing$ then $\inf V = \infty$, so $\{\omega : g(\omega) \le \infty\} =
  \Omega$ has measure $1$, and $c \le 1$ gives the claim. Assume now $V \neq \varnothing$. Since
  $[0,\infty]$ is a first-countable conditionally complete linear order and $V$ is bounded below by
  $0$, there is an antitone sequence $(u_n)_{n\in\mathbb{N}}$ with $u_n \in V$ for all $n$ and
  $u_n \to \inf V$. Because $u_n \ge \inf V$ and the sequence is antitone, the family
  $n \mapsto \{\omega : g(\omega) \le u_n\}^{c} = \{\omega : u_n < g(\omega)\}$ is monotone. Its union
  equals the complement $\{\omega : g(\omega) \le \inf V\}^{c} = \{\omega : \inf V < g(\omega)\}$: if
  $\inf V < g(\omega)$ then, since $u_n \to \inf V$, eventually $u_n < g(\omega)$, so $\omega$ lies in
  some member of the family; conversely $u_n < g(\omega)$ forces $\inf V \le u_n < g(\omega)$. By
  continuity of measure from below,
  $\mu\{\omega : \inf V < g(\omega)\} = \sup_n \mu\{\omega : u_n < g(\omega)\}$. Writing
  $A_n := \{\omega : g(\omega) \le u_n\}$, which is measurable since $g$ is measurable, we have
  $\mu(A_n^{c}) = 1 - \mu(A_n) \le 1 - c$ because $u_n \in V$ gives $\mu(A_n) \ge c$. Hence the
  supremum is at most $1 - c$, so $\mu\{\omega : g(\omega) \le \inf V\}^{c} \le 1 - c$. Finally, from
  $\mu\{\omega : g(\omega) \le \inf V\} = 1 - \mu\{\omega : g(\omega) \le \inf V\}^{c}$ and
  $c \le 1$ we obtain $c = 1 - (1 - c) \le 1 - \mu\{\omega : g(\omega) \le \inf V\}^{c}
  = \mu\{\omega : g(\omega) \le \inf V\}$. -/)
  (title := /-- Measure lower bound survives passage to the infimum threshold -/)
  (latexEnv := "lemma")]
lemma measure_le_sInf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ≥0∞) (hg : Measurable g) (V : Set ℝ≥0∞) (c : ℝ≥0∞) (hc : c ≤ 1)
    (h : ∀ K ∈ V, c ≤ μ {ω | g ω ≤ K}) :
    c ≤ μ {ω | g ω ≤ sInf V} := by
  rcases V.eq_empty_or_nonempty with hV | hV
  · rw [hV, sInf_empty]
    have huniv : {ω | g ω ≤ (⊤ : ℝ≥0∞)} = Set.univ := by
      ext ω; simp
    rw [huniv, measure_univ]
    exact hc
  · obtain ⟨u, huAnti, huTend, huMem⟩ := exists_seq_tendsto_sInf hV (OrderBot.bddBelow V)
    have hSmeas : MeasurableSet {ω | g ω ≤ sInf V} := measurableSet_le hg measurable_const
    have hAmeas : ∀ n, MeasurableSet {ω | g ω ≤ u n} :=
      fun n => measurableSet_le hg measurable_const
    have hcompl : {ω | g ω ≤ sInf V}ᶜ = ⋃ n, {ω | g ω ≤ u n}ᶜ := by
      ext ω
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion, not_le]
      constructor
      · intro hgt
        exact (huTend.eventually_lt_const hgt).exists
      · rintro ⟨n, hn⟩
        exact lt_of_le_of_lt (sInf_le (huMem n)) hn
    have hmono : Monotone (fun n => {ω | g ω ≤ u n}ᶜ) := by
      intro m n hmn ω hω
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω ⊢
      exact lt_of_le_of_lt (huAnti hmn) hω
    have hbound : μ {ω | g ω ≤ sInf V}ᶜ ≤ 1 - c := by
      rw [hcompl, hmono.measure_iUnion]
      refine iSup_le (fun n => ?_)
      rw [prob_compl_eq_one_sub (hAmeas n)]
      exact tsub_le_tsub_left (h (u n) (huMem n)) 1
    have hμc : μ {ω | g ω ≤ sInf V}ᶜ ≠ ⊤ := measure_ne_top μ _
    have hsum : μ {ω | g ω ≤ sInf V} + μ {ω | g ω ≤ sInf V}ᶜ = 1 := prob_add_prob_compl hSmeas
    refine (ENNReal.add_le_add_iff_right hμc).mp ?_
    rw [hsum]
    calc c + μ {ω | g ω ≤ sInf V}ᶜ ≤ c + (1 - c) := by gcongr
      _ = 1 := add_tsub_cancel_of_le hc

@[blueprint "thm:tail-bound"
  (statement := /-- Let $d \in \mathbb{N}$, let $(\Omega, \mu)$ be a probability space, let
  $\|\cdot\|$ be a seminorm on $\mathbb{R}^d$, let $X : \Omega \to \mathbb{R}^d$ be a measurable
  random vector, and let $t \ge 0$. Then, with the optimized value $\Phi(t)$ of
  \cref{def:tail-bound-value} — the joint infimum over all probability measures $\mathbb{P}_0$ on
  $\mathbb{R}^d$ (with $U \sim \mathbb{P}_0$) that are admissible, i.e. have $\nu(\mathbb{P}_0) <
  \infty$, and all real exponents $p \ge 1$ — with probability at least $1 - e^{-t}$,
  \[ \|X\| \;\le\; \Phi(t) \;=\; \inf_{\substack{\mathbb{P}_0 :\, \nu(\mathbb{P}_0) < \infty}}\;\inf_{p \ge 1}\; e^{t/p}\,
  \bigl(\mathbb{E}_0(M_X(U,p))\bigr)^{1/p}\, \nu(\mathbb{P}_0)^{1/p}; \]
  that is, the event $\{\omega : \|X(\omega)\| \le \Phi(t)\}$ has $\mu$-measure at least
  $1 - e^{-t}$. -/)
  (proof := /-- The map $\omega \mapsto \|X(\omega)\|$, read in $[0,\infty]$, is measurable because
  the seminorm is continuous on the finite-dimensional space $\mathbb{R}^d$ by
  \cref{lem:seminorm-continuous-euclidean} and $X$ is measurable. Let $V$ be the set of all
  thresholds $C_{p,\mathbb{P}_0} := e^{t/p}(\mathbb{E}_0(M_X(U,p)))^{1/p}\nu(\mathbb{P}_0)^{1/p}$ as
  $\mathbb{P}_0$ ranges over the admissible probability measures on $\mathbb{R}^d$ (those with
  $\nu(\mathbb{P}_0) < \infty$) and $p$ ranges over $[1,\infty)$. Unfolding
  \cref{def:tail-bound-value} and comparing the nested infimum with the infimum over $V$ termwise
  proves $\Phi(t) = \inf V$: each threshold $C_{p,\mathbb{P}_0}$ bounds the nested infimum from
  above, so $\inf V \ge \Phi(t)$; and $\inf V$ is a lower bound for every threshold, so
  $\Phi(t) \ge \inf V$. By \cref{lem:single-exponent-tail-bound}, for every admissible
  $\mathbb{P}_0$ and every real exponent $p \ge 1$ the event $\{\|X\| \le C_{p,\mathbb{P}_0}\}$ has
  $\mu$-measure at least $1 - e^{-t}$; equivalently, every $K \in V$ satisfies
  $\mu\{\omega : \|X(\omega)\| \le K\} \ge 1 - e^{-t}$. Since $1 - e^{-t} \le 1$, applying
  \cref{lem:measure-le-sInf} to $\omega \mapsto \|X(\omega)\|$, the set $V$, and the confidence
  level $1 - e^{-t}$ yields $1 - e^{-t} \le \mu\{\omega : \|X(\omega)\| \le \inf V\}
  = \mu\{\omega : \|X(\omega)\| \le \Phi(t)\}$, which is the claim. -/)
  (title := /-- Variational tail bound for the norm of a random vector -/)
  (latexEnv := "theorem")]
theorem tail_bound {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (nrm : Seminorm ℝ (EuclideanSpace ℝ (Fin d)))
    (X : Ω → EuclideanSpace ℝ (Fin d)) (hX : Measurable X)
    (t : ℝ) (ht : 0 ≤ t) :
    1 - ENNReal.ofReal (Real.exp (-t))
      ≤ μ {ω | ENNReal.ofReal (nrm (X ω)) ≤ tail_bound_value μ nrm X t} := by
  have hg : Measurable (fun ω => ENNReal.ofReal (nrm (X ω))) :=
    ((seminorm_continuous_euclidean nrm).measurable.comp hX).ennreal_ofReal
  set V : Set ℝ≥0∞ :=
    {y | ∃ P₀ : Measure (EuclideanSpace ℝ (Fin d)),
        (IsProbabilityMeasure P₀ ∧ nu_measure nrm P₀ ≠ ⊤) ∧
        ∃ p : ℝ, 1 ≤ p ∧
          y = ENNReal.ofReal (Real.exp (t / p))
              * aggregated_moment μ X P₀ p ^ (1 / p)
              * nu_measure nrm P₀ ^ (1 / p)} with hVdef
  have hval : tail_bound_value μ nrm X t = sInf V := by
    unfold tail_bound_value
    apply le_antisymm
    · refine le_sInf ?_
      rintro y ⟨P₀, hmem, p, hp, rfl⟩
      exact iInf₂_le_of_le P₀ hmem (iInf₂_le_of_le p hp le_rfl)
    · exact le_iInf₂ (fun P₀ hmem => le_iInf₂ (fun p hp => sInf_le ⟨P₀, hmem, p, hp, rfl⟩))
  rw [hval]
  refine measure_le_sInf μ (fun ω => ENNReal.ofReal (nrm (X ω))) hg V
    (1 - ENNReal.ofReal (Real.exp (-t))) tsub_le_self ?_
  rintro K ⟨P₀, ⟨hprob, hnu⟩, p, hp, rfl⟩
  haveI := hprob
  exact single_exponent_tail_bound μ nrm X hX P₀ hnu t ht p hp

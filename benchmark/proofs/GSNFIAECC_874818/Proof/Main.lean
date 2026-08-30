import Architect
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Data.Finset.Powerset
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators ENNReal

open MeasureTheory

@[blueprint "def:full-support-pmf"
  (statement := /-- A probability mass function $\mu$ on a finite space $\Omega$ has full support if $\mu(x)>0$ for every $x\in\Omega$. -/)
  (title := /-- Full-support probability mass functions -/)
  (latexEnv := "definition")]
def full_support_pmf {Ω : Type*} (μ : PMF Ω) : Prop :=
  ∀ x, μ x ≠ 0

@[blueprint "def:one-coordinate-mean"
  (statement := /-- For a probability mass function $\mu$ on a finite space $\Omega$ and $f:\Omega\to\mathbb R$, define
  \[
    \mathbb E_\mu f=\sum_{x\in\Omega}\mu(x)f(x).
  \] -/)
  (title := /-- Expectation on a finite probability space -/)
  (latexEnv := "definition")]
noncomputable def one_coordinate_mean {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω) (f : Ω → ℝ) : ℝ :=
  ∑ x, (μ x).toReal * f x

@[blueprint "def:one-coordinate-noise"
  (statement := /-- For $\rho\in\mathbb R$, the one-coordinate noise operator associated with $\mu$ is
  \[
    (T_\rho f)(x)=\rho f(x)+(1-\rho)\mathbb E_\mu f.
  \] -/)
  (title := /-- The one-coordinate noise operator -/)
  (latexEnv := "definition")]
noncomputable def one_coordinate_noise {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω) (ρ : ℝ) (f : Ω → ℝ) : Ω → ℝ :=
  fun x ↦ ρ * f x + (1 - ρ) * one_coordinate_mean μ f

@[blueprint "def:product-measure"
  (statement := /-- For $n\in\mathbb N$, let $\mu^{\otimes n}$ be the product measure on $\Omega^n$ whose coordinate marginals are all $\mu$. -/)
  (title := /-- Finite product measure -/)
  (latexEnv := "definition")]
noncomputable def product_measure {Ω : Type*} [MeasurableSpace Ω]
    (μ : PMF Ω) (n : ℕ) : Measure (Fin n → Ω) :=
  Measure.pi fun _ : Fin n ↦ μ.toMeasure

@[blueprint "def:weighted-lp-norm"
  (statement := /-- For a measure $\nu$, an exponent $q\in[0,\infty]$, and a real-valued function $f$, write
  \[
    \|f\|_{L^q(\nu)}=\operatorname{eLpNorm}(f,q,\nu).
  \]
  At $q=\infty$ this is the essential supremum. -/)
  (title := /-- Extended weighted \(L^q\) norm -/)
  (latexEnv := "definition")]
noncomputable def weighted_lp_norm {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (q : ℝ≥0∞) (f : α → ℝ) : ℝ≥0∞ :=
  eLpNorm f q ν

@[blueprint "def:coordinate-conditional-average"
  (statement := /-- Let $S\subseteq\{1,\ldots,n\}$.  For $f:\Omega^n\to\mathbb R$ and $x\in\Omega^n$, define
  \[
    \mathbb E_\mu(f\mid S)(x)
      =\sum_{\substack{y\in\Omega^n\\y_i=x_i\ {\rm for}\ i\in S}}
        \left(\prod_{i\notin S}\mu(y_i)\right)f(y).
  \]
  Thus the coordinates in $S$ are held fixed and all remaining coordinates are averaged independently according to $\mu$. -/)
  (title := /-- Conditional averaging over complementary coordinates -/)
  (latexEnv := "definition")]
noncomputable def coordinate_conditional_average {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω) {n : ℕ} (S : Finset (Fin n))
    (f : (Fin n → Ω) → ℝ) : (Fin n → Ω) → ℝ := by
  classical
  exact fun x ↦
    ∑ y, if ∀ i ∈ S, y i = x i then
      (∏ i ∈ Sᶜ, (μ (y i)).toReal) * f y
    else 0

@[blueprint "def:product-noise"
  (statement := /-- For $f:\Omega^n\to\mathbb R$, define the product noise operator by
  \[
    (T_\rho f)(x)=\sum_{y\in\Omega^n}
      \prod_{i=1}^n\left(\rho\,\mathbf 1_{\{y_i=x_i\}}+
      (1-\rho)\mu(y_i)\right)f(y).
  \]
  Equivalently, each coordinate is independently retained with probability $\rho$ and otherwise resampled from $\mu$. -/)
  (title := /-- The product noise operator -/)
  (latexEnv := "definition")]
noncomputable def product_noise {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω) (ρ : ℝ) {n : ℕ}
    (f : (Fin n → Ω) → ℝ) : (Fin n → Ω) → ℝ := by
  classical
  exact fun x ↦
    ∑ y, (∏ i, if y i = x i then
      ρ + (1 - ρ) * (μ (y i)).toReal
    else
      (1 - ρ) * (μ (y i)).toReal) * f y

@[blueprint "def:bernoulli-subset-weight"
  (statement := /-- If every coordinate of $\{1,\ldots,n\}$ is included independently with probability $\lambda$, then a subset $S$ has mass
  \[
    \lambda^{|S|}(1-\lambda)^{n-|S|}.
  \] -/)
  (title := /-- Bernoulli weight of a coordinate subset -/)
  (latexEnv := "definition")]
def bernoulli_subset_weight {n : ℕ} (lam : ℝ) (S : Finset (Fin n)) : ℝ :=
  lam ^ S.card * (1 - lam) ^ (n - S.card)

@[blueprint "def:minimum-mass-spike"
  (statement := /-- A nonnegative function $f:\Omega\to\mathbb R$ is a minimum-mass spike if there are $c\geq0$ and $x^*\in\Omega$ such that $\mu(x^*)\leq\mu(y)$ for every $y\in\Omega$, and
  \[
    f(x)=c\,\mathbf 1_{\{x^*\}}(x)
  \]
  for every $x\in\Omega$. -/)
  (title := /-- Nonnegative spikes at minimum-mass points -/)
  (latexEnv := "definition")]
def minimum_mass_spike {Ω : Type*} [DecidableEq Ω]
    (μ : PMF Ω) (f : Ω → ℝ) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ ∃ xStar : Ω,
    (∀ y, μ xStar ≤ μ y) ∧
      f = fun x ↦ if x = xStar then c else 0

@[blueprint "def:one-coordinate-extremal-property"
  (statement := /-- Fix a full-support probability mass function $\mu$, $q\in[2,\infty]$, and $\rho\in(0,1)$.  A real number $\lambda$ has the one-coordinate extremal property if $0<\lambda<1$ and, for every nonnegative $f:\Omega\to\mathbb R$,
  \[
    \|T_\rho f\|_{L^q(\mu)}
      \leq \|f\|_{L^1(\mu)}^{1-\lambda}
             \|f\|_{L^q(\mu)}^\lambda,
  \]
  with equality if and only if $f$ is a nonnegative constant or a minimum-mass spike. -/)
  (title := /-- One-coordinate extremal Samorodnitsky property -/)
  (latexEnv := "definition")]
noncomputable def one_coordinate_extremal_property {Ω : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [DecidableEq Ω]
    (μ : PMF Ω) (q : ℝ≥0∞) (ρ lam : ℝ) : Prop :=
  0 < lam ∧ lam < 1 ∧
    ∀ f : Ω → ℝ, (∀ x, 0 ≤ f x) →
      let lhs := weighted_lp_norm μ.toMeasure q (one_coordinate_noise μ ρ f)
      let rhs :=
        ENNReal.rpow (weighted_lp_norm μ.toMeasure 1 f) (1 - lam) *
          ENNReal.rpow (weighted_lp_norm μ.toMeasure q f) lam
      lhs ≤ rhs ∧
        (lhs = rhs ↔
          (∃ c : ℝ, 0 ≤ c ∧ f = fun _ ↦ c) ∨ minimum_mass_spike μ f)

@[blueprint "def:tensorized-samorodnitsky-property"
  (statement := /-- Fix $\mu,q,\rho,\lambda$.  The tensorized Samorodnitsky property asserts that, for every $n\in\mathbb N$ and every nonnegative $f:\Omega^n\to\mathbb R$,
  \[
    \log\|T_\rho f\|_{L^q(\mu^{\otimes n})}
      \leq
      \sum_{S\subseteq\{1,\ldots,n\}}
      \lambda^{|S|}(1-\lambda)^{n-|S|}
      \log\|\mathbb E_\mu(f\mid S)\|_{L^q(\mu^{\otimes n})}.
  \]
  The logarithm is the extended logarithm, so the assertion includes the zero function. -/)
  (title := /-- Tensorized Samorodnitsky property -/)
  (latexEnv := "definition")]
noncomputable def tensorized_samorodnitsky_property {Ω : Type*}
    [Fintype Ω] [MeasurableSpace Ω]
    (μ : PMF Ω) (q : ℝ≥0∞) (ρ lam : ℝ) : Prop :=
  ∀ (n : ℕ) (f : (Fin n → Ω) → ℝ), (∀ x, 0 ≤ f x) →
    ENNReal.log
        (weighted_lp_norm (product_measure μ n) q (product_noise μ ρ f)) ≤
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        (bernoulli_subset_weight lam S : EReal) *
          ENNReal.log
            (weighted_lp_norm (product_measure μ n) q
              (coordinate_conditional_average μ S f))

@[blueprint "def:two-point-moment"
  (statement := /-- For a real exponent $r$, a parameter $s$, and positive numbers $a,b$, define
  \[
    B_r(s;a,b)
      =\frac{a(1+sb)^r+b(1-sa)^r}{a+b}.
  \]
  This is the $r$th moment of $1+sY$ when $Y$ has mean zero and takes the values $b$ and $-a$. -/)
  (title := /-- Moment of a centered two-point law -/)
  (latexEnv := "definition")]
noncomputable def two_point_moment (r s a b : ℝ) : ℝ :=
  (a * Real.rpow (1 + s * b) r + b * Real.rpow (1 - s * a) r) / (a + b)

@[blueprint "def:minimum-atom-mass"
  (statement := /-- For a probability mass function $\mu$ on a finite
  space $\Omega$, define
  \[
    \mu^*=\inf\{\mu(x):x\in\Omega\}.
  \]
  Since the support of a probability mass function is nonempty, this is
  the mass of an atom; under full support it is positive. -/)
  (title := /-- Minimum atom mass -/)
  (latexEnv := "definition")]
noncomputable def minimum_atom_mass {Ω : Type*} [Fintype Ω] (μ : PMF Ω) : ℝ :=
  sInf (Set.range fun x ↦ (μ x).toReal)

@[blueprint "def:optimal-samorodnitsky-parameter"
  (statement := /-- Let $q\in[2,\infty]$, let $0<\rho<1$, and let
  $p\in(0,1]$ denote a minimum atom mass.  Put $k=p^{-1}$ and
  $\alpha=k-1$.  The optimal Samorodnitsky parameter is
  \[
    \lambda(q,p,\rho)=
    \begin{cases}
      \tfrac12,&p=1,\\
      \dfrac{\log(1+\rho\alpha)}{\log(1+\alpha)},&q=\infty,\ p<1,\\
      \dfrac{\log B_q(\rho;1,\alpha)}
        {\log B_q(1;1,\alpha)},&q<\infty,\ p<1.
    \end{cases}
  \]
  Here $B_q$ is the centered two-point moment from
  \cref{def:two-point-moment}.  In the finite-exponent case,
  $B_q(1;1,k-1)=k^{q-1}$, so this is exactly
  \[
    \frac1{q-1}\log_k\!\left(
      \frac1k(1+(k-1)\rho)^q+
      \left(1-\frac1k\right)(1-\rho)^q\right).
  \]
  The value $1/2$ is the fixed convention for the degenerate one-point
  space, where every parameter in $(0,1)$ yields equality. -/)
  (title := /-- Optimal generalized Samorodnitsky parameter -/)
  (latexEnv := "definition")]
noncomputable def optimal_samorodnitsky_parameter
    (q : ℝ≥0∞) (p ρ : ℝ) : ℝ :=
  if p = 1 then
    1 / 2
  else
    let α := 1 / p - 1
    if q = ⊤ then
      Real.log (1 + ρ * α) / Real.log (1 + α)
    else
      Real.log (two_point_moment q.toReal ρ 1 α) /
        Real.log (two_point_moment q.toReal 1 1 α)

@[blueprint "lem:mul-log-one-add-contraction"
  (statement := /-- Let $u,z\in\mathbb R$ satisfy $0<u<1$ and $z>0$.  Then
  \[
    (1+uz)\log(1+uz)<u(1+z)\log(1+z).
  \] -/)
  (proof := /-- Apply the strict convexity of $x\mapsto x\log x$ on
  $[0,\infty)$ to the distinct points $1$ and $1+z$, with positive
  weights $1-u$ and $u$.  Their convex combination is $1+uz$, while the
  value of $x\log x$ at $1$ is zero, which gives the asserted strict
  inequality. -/)
  (title := /-- Strict contraction for the logarithmic entropy function -/)
  (latexEnv := "lemma")]
lemma mul_log_one_add_contraction
    (u z : ℝ) (hu₀ : 0 < u) (hu₁ : u < 1) (hz : 0 < z) :
    (1 + u * z) * Real.log (1 + u * z) <
      u * ((1 + z) * Real.log (1 + z)) := by
  let f : ℝ → ℝ :=
    id * Real.log / (id - fun _ ↦ (1 : ℝ))
  have hcont : ContinuousOn f (Set.Ioi 1) := by
    intro x hx
    have hx' : 1 < x := hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx')
    have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hx')
    exact ((continuousAt_id.mul (Real.continuousAt_log hx0)).div
      (continuousAt_id.sub continuousAt_const) hx1).continuousWithinAt
  have hderiv (x : ℝ) (hx : x ∈ interior (Set.Ioi (1 : ℝ))) :
      HasDerivWithinAt f ((x - 1 - Real.log x) / (x - 1) ^ 2)
        (interior (Set.Ioi (1 : ℝ))) x := by
    have hx' : 1 < x := by simpa only [interior_Ioi, Set.mem_Ioi] using hx
    have hx0 : x ≠ 0 := by linarith
    have hx1 : x - 1 ≠ 0 := by linarith
    have hnum := (hasDerivAt_id x).mul (Real.hasDerivAt_log hx0)
    have hden := (hasDerivAt_id x).sub (hasDerivAt_const x 1)
    have hcoeff :
        (Real.log x + 1) * (x - 1) - x * Real.log x =
          x - 1 - Real.log x := by ring
    have hquot := hnum.div hden hx1
    dsimp only [id_eq, Pi.mul_apply, Pi.sub_apply] at hquot
    rw [show 1 * Real.log x + x * x⁻¹ = Real.log x + 1 by
      rw [one_mul, mul_inv_cancel₀ hx0]] at hquot
    simp only [sub_zero, mul_one] at hquot
    rw [hcoeff] at hquot
    simpa only [f] using hquot.hasDerivWithinAt
  have hderiv_pos (x : ℝ) (hx : x ∈ interior (Set.Ioi (1 : ℝ))) :
      0 < (x - 1 - Real.log x) / (x - 1) ^ 2 := by
    have hx' : 1 < x := by simpa only [interior_Ioi, Set.mem_Ioi] using hx
    exact div_pos (sub_pos.mpr (Real.log_lt_sub_one_of_pos (by linarith)
      (by linarith))) (sq_pos_of_ne_zero (by linarith))
  have hmono : StrictMonoOn f (Set.Ioi 1) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioi 1) hcont hderiv hderiv_pos
  have hleft : 1 + u * z ∈ Set.Ioi (1 : ℝ) := by
    simp only [Set.mem_Ioi]
    nlinarith [mul_pos hu₀ hz]
  have hright : 1 + z ∈ Set.Ioi (1 : ℝ) := by
    simp only [Set.mem_Ioi]
    linarith
  have harg : 1 + u * z < 1 + z := by
    nlinarith [mul_lt_mul_of_pos_right hu₁ hz]
  have hratio := hmono hleft hright harg
  simp only [f, id_eq, Pi.mul_apply, Pi.sub_apply, Pi.div_apply] at hratio
  rw [show 1 + u * z - 1 = u * z by ring,
    show 1 + z - 1 = z by ring] at hratio
  have hcross := (div_lt_div_iff₀ (mul_pos hu₀ hz) hz).mp hratio
  nlinarith

@[blueprint "lem:two-point-moment-two"
  (statement := /-- For $s,a,b\in\mathbb R$ with $a+b\ne0$, the
  two-point moment at exponent $2$ is
  \[
    B_2(s;a,b)=1+s^2ab.
  \] -/)
  (proof := /-- Expand the definition in
  \cref{def:two-point-moment}, replace both real second powers by ordinary
  squares, clear the nonzero denominator $a+b$, and expand the resulting
  polynomial identity. -/)
  (title := /-- Quadratic centered two-point moment -/)
  (latexEnv := "lemma")]
lemma two_point_moment_two (s a b : ℝ) (hab : a + b ≠ 0) :
    two_point_moment 2 s a b = 1 + s ^ 2 * a * b := by
  rw [two_point_moment,
    show Real.rpow (1 + s * b) 2 = (1 + s * b) ^ 2 by
      exact Real.rpow_two _,
    show Real.rpow (1 - s * a) 2 = (1 - s * a) ^ 2 by
      exact Real.rpow_two _]
  field_simp [hab]
  ring

@[blueprint "lem:two-point-log-ratio-quadratic-core"
  (statement := /-- Let $t,a,b\in\mathbb R$ satisfy $0<t<1$, $a>0$, and
  $b>0$.  Then
  \[
    t^2(a+b)^2B_2(1;a,b)\log B_2(1;a,b)
      -(a+b)^2B_2(t;a,b)\log B_2(t;a,b)>0.
  \] -/)
  (proof := /-- By \cref{lem:two-point-moment-two}, the two moments are
  $1+ab$ and $1+t^2ab$.  Apply
  \cref{lem:mul-log-one-add-contraction} with $u=t^2$ and $z=ab$, and
  multiply its strict inequality by the positive factor $(a+b)^2$. -/)
  (title := /-- Quadratic two-point logarithmic gap -/)
  (latexEnv := "lemma")]
lemma two_point_log_ratio_quadratic_core
    (t a b : ℝ) (ht₀ : 0 < t) (ht₁ : t < 1)
    (ha₀ : 0 < a) (hb₀ : 0 < b) :
    0 <
      t ^ 2 * (a + b) ^ 2 * two_point_moment 2 1 a b *
          Real.log (two_point_moment 2 1 a b) -
        (a + b) ^ 2 * two_point_moment 2 t a b *
          Real.log (two_point_moment 2 t a b) := by
  have hab : a + b ≠ 0 := ne_of_gt (add_pos ha₀ hb₀)
  have ht2₀ : 0 < t ^ 2 := sq_pos_of_pos ht₀
  have ht2₁ : t ^ 2 < 1 := by
    nlinarith [mul_pos (sub_pos.mpr ht₁) (by linarith : 0 < 1 + t)]
  have hz : 0 < a * b := mul_pos ha₀ hb₀
  have hent :=
    mul_log_one_add_contraction (t ^ 2) (a * b) ht2₀ ht2₁ hz
  rw [two_point_moment_two 1 a b hab,
    two_point_moment_two t a b hab]
  norm_num only [one_pow, one_mul] at hent ⊢
  rw [show 1 + t ^ 2 * (a * b) = 1 + t ^ 2 * a * b by ring] at hent
  have hscale : 0 < (a + b) ^ 2 := sq_pos_of_pos (add_pos ha₀ hb₀)
  calc
    0 < (a + b) ^ 2 *
        (t ^ 2 * ((1 + a * b) * Real.log (1 + a * b)) -
          (1 + t ^ 2 * a * b) * Real.log (1 + t ^ 2 * a * b)) :=
      mul_pos hscale (sub_pos.mpr hent)
    _ = t ^ 2 * (a + b) ^ 2 * (1 + a * b) *
          Real.log (1 + a * b) -
        (a + b) ^ 2 * (1 + t ^ 2 * a * b) *
          Real.log (1 + t ^ 2 * a * b) := by ring

@[blueprint "lem:normalized-boundary-log-curvature"
  (statement := /-- Let $r,k,d\in\mathbb R$ satisfy $r>2$, $k>0$, and
  $d>0$.  Put
  \[
  \begin{aligned}
    G&=1+d\frac{(1+k)^r-1}{k},\\
    G_1&=d\left(r(1+k)^{r-1}-\frac{(1+k)^r-1}{k}\right),\\
    G_2&=d\left(r(r-1)k(1+k)^{r-2}
      -r(1+k)^{r-1}+\frac{(1+k)^r-1}{k}\right).
  \end{aligned}
  \]
  Then $GG_2-G_1^2>0$. -/)
  (proof := /-- Write $A=(1+k)^r$ and
  $P=(r-1)^2k^2-(r-2)k+1$.  Clearing the positive denominator
  $k(1+k)^2$ shows that the asserted curvature has numerator
  \[
    drA(A-1-rk)+AP-(1+k)^2.
  \]
  Strict Bernoulli gives $A>1+rk$.  Moreover,
  \[
    4(r-1)^2P=
      \bigl(2(r-1)^2k-(r-2)\bigr)^2+r(3r-4)>0,
  \]
  so $P>0$, and
  \[
    (1+rk)P=(1+k)^2+k^3r(r-1)^2>(1+k)^2.
  \]
  Both summands in the displayed numerator are therefore positive. -/)
  (title := /-- Positive normalized boundary logarithmic curvature -/)
  (latexEnv := "lemma")]
lemma normalized_boundary_log_curvature
    (r k d : ℝ) (hr : 2 < r) (hk : 0 < k) (hd : 0 < d) :
    0 <
      (1 + d * ((1 + k).rpow r - 1) / k) *
          (d * (r * (r - 1) * k * (1 + k).rpow (r - 2) -
            r * (1 + k).rpow (r - 1) +
            ((1 + k).rpow r - 1) / k)) -
        (d * (r * (1 + k).rpow (r - 1) -
          ((1 + k).rpow r - 1) / k)) ^ 2 := by
  let A : ℝ := (1 + k).rpow r
  let P : ℝ := (r - 1) ^ 2 * k ^ 2 - (r - 2) * k + 1
  have hr1 : 1 < r := lt_trans one_lt_two hr
  have hA : 1 + r * k < A := by
    dsimp [A]
    exact one_add_mul_self_lt_rpow_one_add (by linarith)
      (ne_of_gt hk) hr1
  have hApos : 0 < A := by
    dsimp [A]
    exact Real.rpow_pos_of_pos (by linarith) r
  have hP : 0 < P := by
    have hsquare :
        0 ≤ (2 * (r - 1) ^ 2 * k - (r - 2)) ^ 2 := sq_nonneg _
    have hfactor : 0 < 4 * (r - 1) ^ 2 := by positivity
    have hrem : 0 < r * (3 * r - 4) := by
      have : 0 < r := by linarith
      exact mul_pos this (by linarith)
    have hid :
        4 * (r - 1) ^ 2 * P =
          (2 * (r - 1) ^ 2 * k - (r - 2)) ^ 2 +
            r * (3 * r - 4) := by
      dsimp [P]
      ring
    nlinarith
  have hk3 : 0 < k ^ 3 * r * (r - 1) ^ 2 := by positivity
  have hpoly :
      (1 + r * k) * P =
        (1 + k) ^ 2 + k ^ 3 * r * (r - 1) ^ 2 := by
    dsimp [P]
    ring
  have hAP : (1 + k) ^ 2 < A * P := by
    have := mul_lt_mul_of_pos_right hA hP
    nlinarith
  have hfirst : 0 < d * r * A * (A - 1 - r * k) := by
    have : 0 < A - 1 - r * k := by linarith
    positivity
  have hnum :
      0 < d * r * A * (A - 1 - r * k) +
        (A * P - (1 + k) ^ 2) := by
    nlinarith
  have hden : 0 < k * (1 + k) ^ 2 := by positivity
  have hid :
      k * (1 + k) ^ 2 *
          ((1 + d * ((1 + k).rpow r - 1) / k) *
              (d * (r * (r - 1) * k * (1 + k).rpow (r - 2) -
                r * (1 + k).rpow (r - 1) +
                ((1 + k).rpow r - 1) / k)) -
            (d * (r * (1 + k).rpow (r - 1) -
              ((1 + k).rpow r - 1) / k)) ^ 2) =
        d * (d * r * A * (A - 1 - r * k) +
          (A * P - (1 + k) ^ 2)) := by
    dsimp [A, P]
    have hk1 : 1 + k ≠ 0 := ne_of_gt (by linarith)
    have hkpos : 0 < 1 + k := by linarith
    rw [Real.rpow_sub hkpos r 1, Real.rpow_sub hkpos r 2,
      Real.rpow_one, Real.rpow_two]
    field_simp [ne_of_gt hk, ne_of_gt (by linarith : 0 < 1 + k)]
    ring
  have : 0 < k * (1 + k) ^ 2 *
      ((1 + d * ((1 + k).rpow r - 1) / k) *
          (d * (r * (r - 1) * k * (1 + k).rpow (r - 2) -
            r * (1 + k).rpow (r - 1) +
            ((1 + k).rpow r - 1) / k)) -
        (d * (r * (1 + k).rpow (r - 1) -
          ((1 + k).rpow r - 1) / k)) ^ 2) := by
    rw [hid]
    exact mul_pos hd hnum
  rcases mul_pos_iff.mp this with h | h
  · exact h.2
  · exact False.elim (not_lt_of_ge hden.le h.1)

@[blueprint "lem:secant-strictly-below-endpoint-derivative"
  (statement := /-- Let $x<y$, let $f:[x,y]\to\mathbb R$ be continuous
  and differentiable on $(x,y)$ with derivative $f'$, and suppose that
  $f'$ is strictly increasing on $[x,y]$.  Then
  \[
    \frac{f(y)-f(x)}{y-x}<f'(y).
  \] -/)
  (proof := /-- The mean value theorem supplies $c\in(x,y)$ for which
  the secant slope equals $f'(c)$.  Since $c<y$ and $f'$ is strictly
  increasing on the closed interval, $f'(c)<f'(y)$. -/)
  (title := /-- A secant slope lies below the endpoint derivative -/)
  (latexEnv := "lemma")]
lemma secant_strictly_below_endpoint_derivative
    (f f' : ℝ → ℝ) (x y : ℝ) (hxy : x < y)
    (hcont : ContinuousOn f (Set.Icc x y))
    (hderiv : ∀ z ∈ Set.Ioo x y, HasDerivAt f (f' z) z)
    (hmono : StrictMonoOn f' (Set.Icc x y)) :
    (f y - f x) / (y - x) < f' y := by
  obtain ⟨c, hc, hcderiv⟩ :=
    exists_hasDerivAt_eq_slope f f' hxy hcont hderiv
  rw [← hcderiv]
  exact hmono ⟨hc.1.le, hc.2.le⟩ ⟨hxy.le, le_rfl⟩ hc.2

@[blueprint "lem:normalized-boundary-secant-derivative"
  (statement := /-- Let $r,d,x\in\mathbb R$ satisfy $r>2$, $d>0$, and
  $x>1$, and define
  \[
    G(k)=1+d\frac{(1+k)^r-1}{k}.
  \]
  Then the logarithmic secant from $d$ to $dx$, in logarithmic
  coordinates, lies strictly below the logarithmic derivative at $dx$:
  \[
    \frac{\log G(dx)-\log G(d)}{\log x}
      <
    \frac{d\left(r(1+dx)^{r-1}
      -\frac{(1+dx)^r-1}{dx}\right)}{G(dx)}.
  \] -/)
  (proof := /-- Put $k(y)=de^y$ and $h(y)=\log G(k(y))$.  Direct
  differentiation gives
  \[
    h'(y)=\frac{G_1(k(y))}{G(k(y))},\qquad
    h''(y)=\frac{G(k(y))G_2(k(y))-G_1(k(y))^2}{G(k(y))^2}.
  \]
  The numerator in the second formula is strictly positive by
  \cref{lem:normalized-boundary-log-curvature}; hence $h'$ is strictly
  increasing.  Apply
  \cref{lem:secant-strictly-below-endpoint-derivative} on
  $[0,\log x]$ and use $e^{\log x}=x$. -/)
  (title := /-- Boundary logarithmic secant--derivative inequality -/)
  (latexEnv := "lemma")]
lemma normalized_boundary_secant_derivative
    (r d x : ℝ) (hr : 2 < r) (hd : 0 < d) (hx : 1 < x) :
    (Real.log
          (1 + d * ((1 + d * x).rpow r - 1) / (d * x)) -
        Real.log (1 + d * ((1 + d).rpow r - 1) / d)) /
        Real.log x <
      (d * (r * (1 + d * x).rpow (r - 1) -
          ((1 + d * x).rpow r - 1) / (d * x))) /
        (1 + d * ((1 + d * x).rpow r - 1) / (d * x)) := by
  let G : ℝ → ℝ := fun k ↦ 1 + d * (((1 + k).rpow r - 1) / k)
  let G1 : ℝ → ℝ := fun k ↦
    d * (r * (1 + k).rpow (r - 1) - ((1 + k).rpow r - 1) / k)
  let G2 : ℝ → ℝ := fun k ↦
    d * (r * (r - 1) * k * (1 + k).rpow (r - 2) -
      r * (1 + k).rpow (r - 1) + ((1 + k).rpow r - 1) / k)
  have hrpowDeriv (p k : ℝ) (hk : 0 < k) :
      HasDerivAt (fun z : ℝ ↦ (1 + z).rpow p)
        (p * (1 + k).rpow (p - 1)) k := by
    have hbase : HasDerivAt (fun z : ℝ ↦ 1 + z) 1 k :=
      (hasDerivAt_id k).const_add 1
    have hlog :=
      (Real.hasDerivAt_log (ne_of_gt (by linarith : 0 < 1 + k))).comp k hbase
    have hmul := hlog.const_mul p
    have hexp := (Real.hasDerivAt_exp (p * Real.log (1 + k))).comp k hmul
    have hev :
        (fun z : ℝ ↦ (1 + z).rpow p) =ᶠ[nhds k]
          (fun z : ℝ ↦ Real.exp (p * Real.log (1 + z))) := by
      filter_upwards [isOpen_Ioi.eventually_mem
        (show k ∈ Set.Ioi (-1 : ℝ) by
          simp only [Set.mem_Ioi]
          linarith)] with z hz
      have hzpos : 0 < 1 + z := by
        have : -1 < z := hz
        linarith
      calc
        (1 + z).rpow p =
            Real.exp (Real.log (1 + z) * p) :=
          Real.rpow_def_of_pos hzpos p
        _ = Real.exp (p * Real.log (1 + z)) := by congr 1 <;> ring
    have hfinal := hexp.congr_of_eventuallyEq hev
    have hcoef :
        Real.exp (p * Real.log (1 + k)) *
            (p * ((1 + k)⁻¹ * 1)) =
          p * (1 + k).rpow (p - 1) := by
      have hexpeq : Real.exp (p * Real.log (1 + k)) =
          (1 + k).rpow p := by
        symm
        calc
          (1 + k).rpow p =
              Real.exp (Real.log (1 + k) * p) :=
            Real.rpow_def_of_pos (by linarith) p
          _ = Real.exp (p * Real.log (1 + k)) := by congr 1 <;> ring
      have hsub :
          (1 + k).rpow (p - 1) = (1 + k).rpow p / (1 + k) :=
        Real.rpow_sub_one (ne_of_gt (by linarith : 0 < 1 + k)) p
      rw [hexpeq, hsub]
      field_simp [ne_of_gt (by linarith : 0 < 1 + k)]
    rw [hcoef] at hfinal
    exact hfinal
  have hGpos (k : ℝ) (hk : 0 < k) : 0 < G k := by
    have hbern :=
      one_add_mul_self_lt_rpow_one_add (by linarith : -1 ≤ k)
        (ne_of_gt hk) (lt_trans one_lt_two hr)
    dsimp [G]
    have hrk : 0 < r * k := mul_pos (by linarith) hk
    have hpow1 : 1 < (1 + k).rpow r := lt_trans (by linarith) hbern
    have hfrac : 0 < ((1 + k).rpow r - 1) / k :=
      div_pos (sub_pos.mpr hpow1) hk
    exact add_pos zero_lt_one (mul_pos hd hfrac)
  have hGderiv (k : ℝ) (hk : 0 < k) :
      HasDerivAt G (G1 k / k) k := by
    have hbase : HasDerivAt (fun z : ℝ ↦ 1 + z) 1 k :=
      (hasDerivAt_id k).const_add 1
    have hpow := hrpowDeriv r k hk
    have hnum := hpow.sub_const 1
    have hquot := hnum.div (hasDerivAt_id k) (ne_of_gt hk)
    have hscaled := hquot.const_mul d
    have htotal := hscaled.const_add 1
    have hcoef :
        d * ((r * (1 + k).rpow (r - 1) * k -
          ((1 + k).rpow r - 1) * 1) / k ^ 2) = G1 k / k := by
      dsimp [G1]
      field_simp [ne_of_gt hk]
    simp only [id_eq] at htotal
    rw [hcoef] at htotal
    exact htotal.congr_of_eventuallyEq (by
      filter_upwards with y
      rfl)
  have hG1deriv (k : ℝ) (hk : 0 < k) :
      HasDerivAt G1 (G2 k / k) k := by
    have hbase : HasDerivAt (fun z : ℝ ↦ 1 + z) 1 k :=
      (hasDerivAt_id k).const_add 1
    have hp := hrpowDeriv r k hk
    have hp1 := hrpowDeriv (r - 1) k hk
    rw [show r - 1 - 1 = r - 2 by ring] at hp1
    have hnum := hp.sub_const 1
    have hquot := hnum.div (hasDerivAt_id k) (ne_of_gt hk)
    have hfirst := hp1.const_mul r
    have hdiff := hfirst.sub hquot
    have hscaled := hdiff.const_mul d
    simp only [id_eq] at hscaled
    have hcoef :
        d * (r * ((r - 1) * (1 + k).rpow (r - 2)) -
          (r * (1 + k).rpow (r - 1) * k -
            ((1 + k).rpow r - 1) * 1) / k ^ 2) = G2 k / k := by
      dsimp [G2]
      field_simp [ne_of_gt hk]
      ring
    rw [hcoef] at hscaled
    exact hscaled.congr_of_eventuallyEq (by
      filter_upwards with y
      rfl)
  let K : ℝ → ℝ := fun y ↦ d * Real.exp y
  let H : ℝ → ℝ := Real.log ∘ G ∘ K
  let H1 : ℝ → ℝ := (G1 ∘ K) / (G ∘ K)
  have hKpos (y : ℝ) : 0 < K y := by
    dsimp [K]
    positivity
  have hHderiv (y : ℝ) : HasDerivAt H (H1 y) y := by
    have hK : HasDerivAt K (K y) y := by
      dsimp [K]
      simpa only [mul_comm] using Real.hasDerivAt_exp y |>.const_mul d
    have hGK := (hGderiv (K y) (hKpos y)).comp y hK
    have hGK' : HasDerivAt (G ∘ K) (G1 (K y)) y := by
      rw [div_mul_cancel₀ _ (ne_of_gt (hKpos y))] at hGK
      exact hGK
    have hlog :=
      (Real.hasDerivAt_log (ne_of_gt (hGpos (K y) (hKpos y)))).comp y hGK'
    dsimp only [H1]
    simpa only [H, Function.comp_apply, Pi.div_apply, div_eq_mul_inv,
      mul_comm] using hlog
  have hH1deriv (y : ℝ) :
      HasDerivAt H1
        ((G (K y) * G2 (K y) - (G1 (K y)) ^ 2) / (G (K y)) ^ 2) y := by
    have hK : HasDerivAt K (K y) y := by
      dsimp [K]
      simpa only [mul_comm] using Real.hasDerivAt_exp y |>.const_mul d
    have hnum := (hG1deriv (K y) (hKpos y)).comp y hK
    have hden := (hGderiv (K y) (hKpos y)).comp y hK
    have hnum' : HasDerivAt (G1 ∘ K) (G2 (K y)) y := by
      rw [div_mul_cancel₀ _ (ne_of_gt (hKpos y))] at hnum
      exact hnum
    have hden' : HasDerivAt (G ∘ K) (G1 (K y)) y := by
      rw [div_mul_cancel₀ _ (ne_of_gt (hKpos y))] at hden
      exact hden
    have hquot := hnum'.div hden' (ne_of_gt (hGpos (K y) (hKpos y)))
    simp only [Function.comp_apply] at hquot
    have hcoef :
        (G2 (K y) * G (K y) - G1 (K y) * G1 (K y)) /
            G (K y) ^ 2 =
          (G (K y) * G2 (K y) - (G1 (K y)) ^ 2) /
            (G (K y)) ^ 2 := by ring
    rw [hcoef] at hquot
    exact hquot
  have hcurv (y : ℝ) :
      0 < (G (K y) * G2 (K y) - (G1 (K y)) ^ 2) /
          (G (K y)) ^ 2 := by
    exact div_pos
      (by
        simpa only [G, G1, G2, mul_div_assoc] using
          normalized_boundary_log_curvature r (K y) d hr (hKpos y) hd)
      (sq_pos_of_pos (hGpos (K y) (hKpos y)))
  have hH1mono : StrictMonoOn H1 Set.univ := by
    apply strictMonoOn_of_hasDerivWithinAt_pos convex_univ
    · intro y hy
      exact (hH1deriv y).continuousAt.continuousWithinAt
    · intro y hy
      exact (hH1deriv y).hasDerivWithinAt
    · intro y hy
      exact hcurv y
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hsec :=
    secant_strictly_below_endpoint_derivative H H1 0 (Real.log x)
      hlogx
      (fun y hy ↦ (hHderiv y).continuousAt.continuousWithinAt)
      (fun y hy ↦ hHderiv y)
      (hH1mono.mono (Set.subset_univ _))
  have hexp : Real.exp (Real.log x) = x := Real.exp_log (by linarith)
  simpa only [H, H1, K, G, G1, Function.comp_apply, Pi.div_apply,
    Real.exp_zero, mul_one, hexp, sub_zero, mul_div_assoc] using hsec

@[blueprint "lem:two-point-boundary-derivative-sign"
  (statement := /-- Let $r,t,b\in\mathbb R$ satisfy $r>2$, $0<t<1$,
  and $b>0$.  At the boundary $a=1$, the numerator of the
  $b$-derivative of
  $\log B_r(t;1,b)/\log B_r(1;1,b)$ is strictly positive. -/)
  (proof := /-- Put $c=1-t$, $d=t/c$, and $x=1+b$.  Algebra gives
  \[
    B_r(t;1,b)=c^rG(dx),\qquad c^rG(d)=1,
  \]
  for the function $G$ in
  \cref{lem:normalized-boundary-secant-derivative}, and identifies its
  logarithmic derivative at $dx$ with
  $V_t/(xB_r(t;1,b))$.  That lemma therefore yields
  \[
    \frac{\log B_r(t;1,b)}{\log x}
      <\frac{V_t}{xB_r(t;1,b)}.
  \]
  Clearing the positive denominators and using
  $B_r(1;1,b)=x^{r-1}$ and $V_1=(r-1)x^r$ proves the claim. -/)
  (title := /-- Positive boundary derivative numerator -/)
  (latexEnv := "lemma")]
lemma two_point_boundary_derivative_sign
    (r t b : ℝ) (hr : 2 < r) (ht₀ : 0 < t) (ht₁ : t < 1)
    (hb₀ : 0 < b) :
    0 <
      (r * (t * (1 + b)) * (1 + t * b).rpow (r - 1) -
          (1 + t * b).rpow r + (1 - t).rpow r) *
        two_point_moment r 1 1 b *
          Real.log (two_point_moment r 1 1 b) -
      (r * (1 + b) * (1 + b).rpow (r - 1) -
          (1 + b).rpow r) *
        two_point_moment r t 1 b *
          Real.log (two_point_moment r t 1 b) := by
  let c : ℝ := 1 - t
  let d : ℝ := t / c
  let x : ℝ := 1 + b
  have hc : 0 < c := by dsimp [c]; linarith
  have hd : 0 < d := div_pos ht₀ hc
  have hx : 1 < x := by dsimp [x]; linarith
  have hsec := normalized_boundary_secant_derivative r d x hr hd hx
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hcpow : 0 < c.rpow r := Real.rpow_pos_of_pos hc r
  have hA : 0 < 1 + t * b := by positivity
  have hdivrpow (u v p : ℝ) (hu : 0 < u) (hv : 0 < v) :
      (u / v).rpow p = u.rpow p / v.rpow p := by
    calc
      (u / v).rpow p =
          Real.exp (Real.log (u / v) * p) :=
        Real.rpow_def_of_pos (div_pos hu hv) p
      _ = Real.exp ((Real.log u - Real.log v) * p) := by
        rw [Real.log_div (ne_of_gt hu) (ne_of_gt hv)]
      _ = Real.exp (Real.log u * p) / Real.exp (Real.log v * p) := by
        rw [sub_mul, Real.exp_sub]
      _ = u.rpow p / v.rpow p := by
        congr 1
        · exact (Real.rpow_def_of_pos hu p).symm
        · exact (Real.rpow_def_of_pos hv p).symm
  have hone : 1 + d = 1 / c := by
    dsimp [d, c]
    field_simp [ne_of_gt (sub_pos.mpr ht₁)]
    ring
  have honeX : 1 + d * x = (1 + t * b) / c := by
    dsimp [d, x, c]
    field_simp [ne_of_gt (sub_pos.mpr ht₁)]
    ring
  have hdx : d * x = t * (1 + b) / c := by
    dsimp [d, x]
    ring
  have hGd :
      1 + d * ((1 + d).rpow r - 1) / d = 1 / c.rpow r := by
    have hdiv : (1 / c).rpow r = 1 / c.rpow r := by
      rw [hdivrpow 1 c r zero_lt_one hc]
      have honepow : Real.rpow 1 r = 1 := by
        calc
          Real.rpow 1 r = Real.exp (Real.log 1 * r) :=
            Real.rpow_def_of_pos zero_lt_one r
          _ = 1 := by rw [Real.log_one, zero_mul, Real.exp_zero]
      rw [honepow]
    calc
      1 + d * ((1 + d).rpow r - 1) / d =
          1 + d * ((1 / c).rpow r - 1) / d := by rw [hone]
      _ = (1 / c).rpow r := by
        field_simp [hd0]
        ring
      _ = 1 / c.rpow r := hdiv
  have hMtpos : 0 < two_point_moment r t 1 b := by
    rw [two_point_moment]
    apply div_pos
    · exact add_pos
        (mul_pos zero_lt_one (Real.rpow_pos_of_pos hA r))
        (mul_pos hb₀ (Real.rpow_pos_of_pos (by linarith : 0 < 1 - t * 1) r))
    · linarith
  have hGx :
      1 + d * ((1 + d * x).rpow r - 1) / (d * x) =
        two_point_moment r t 1 b / c.rpow r := by
    have hdiv :
        ((1 + t * b) / c).rpow r =
          (1 + t * b).rpow r / c.rpow r := by
      exact hdivrpow (1 + t * b) c r hA hc
    rw [honeX, hdiv]
    rw [two_point_moment]
    dsimp only [d, x]
    simp only [one_mul, mul_one]
    change
      1 + (t / c) *
          ((1 + t * b).rpow r / c.rpow r - 1) /
            ((t / c) * (1 + b)) =
        (((1 + t * b).rpow r + b * c.rpow r) / (1 + b)) /
          c.rpow r
    field_simp [ne_of_gt ht₀, ne_of_gt hb₀, ne_of_gt (by linarith : 0 < 1 + b),
      hc0, ne_of_gt hcpow]
    ring
  have hlog :
      Real.log
          (1 + d * ((1 + d * x).rpow r - 1) / (d * x)) -
        Real.log (1 + d * ((1 + d).rpow r - 1) / d) =
        Real.log (two_point_moment r t 1 b) := by
    rw [hGx, hGd, ← Real.log_div
      (div_ne_zero (ne_of_gt hMtpos) (ne_of_gt hcpow))
      (one_div_ne_zero (ne_of_gt hcpow))]
    congr 1
    field_simp [ne_of_gt hcpow]
  have hright :
      (d * (r * (1 + d * x).rpow (r - 1) -
          ((1 + d * x).rpow r - 1) / (d * x))) /
          (1 + d * ((1 + d * x).rpow r - 1) / (d * x)) =
        (r * (t * (1 + b)) * (1 + t * b).rpow (r - 1) -
            (1 + t * b).rpow r + (1 - t).rpow r) /
          (x * two_point_moment r t 1 b) := by
    have hdiv1 :
        ((1 + t * b) / c).rpow (r - 1) =
          (1 + t * b).rpow (r - 1) / c.rpow (r - 1) := by
      exact hdivrpow (1 + t * b) c (r - 1) hA hc
    have hdiv :
        ((1 + t * b) / c).rpow r =
          (1 + t * b).rpow r / c.rpow r := by
      exact hdivrpow (1 + t * b) c r hA hc
    rw [hGx, honeX, hdiv1, hdiv]
    have hcsub :
        c.rpow (r - 1) = c.rpow r / c :=
      Real.rpow_sub_one hc0 r
    have hAsub :
        (1 + t * b).rpow (r - 1) =
          (1 + t * b).rpow r / (1 + t * b) :=
      Real.rpow_sub_one (ne_of_gt hA) r
    rw [hcsub, hAsub]
    dsimp only [d, x]
    rw [show 1 - t = c by rfl]
    field_simp [ne_of_gt ht₀, ne_of_gt hb₀, ne_of_gt hA,
      ne_of_gt (by linarith : 0 < 1 + b), hc0, ne_of_gt hcpow,
      ne_of_gt hMtpos]
    ring
  rw [hlog, hright] at hsec
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hxMt : 0 < x * two_point_moment r t 1 b :=
    mul_pos (lt_trans zero_lt_one hx) hMtpos
  have hcross :=
    (div_lt_div_iff₀ hlogx hxMt).mp hsec
  have hM1 :
      two_point_moment r 1 1 b = x.rpow (r - 1) := by
    rw [two_point_moment]
    have hr0 : r ≠ 0 := by linarith
    have hzpow : Real.rpow 0 r = 0 := Real.zero_rpow hr0
    rw [show 1 + 1 * b = x by dsimp [x]; ring,
      show 1 - 1 * 1 = (0 : ℝ) by ring, hzpow]
    have hxsub : x.rpow (r - 1) = x.rpow r / x :=
      Real.rpow_sub_one hx0 r
    rw [hxsub]
    dsimp [x]
    field_simp [ne_of_gt (by linarith : 0 < 1 + b)]
    ring
  have hV1 :
      r * (1 + b) * (1 + b).rpow (r - 1) -
          (1 + b).rpow r =
        (r - 1) * x.rpow r := by
    have hxsub : x.rpow (r - 1) = x.rpow r / x :=
      Real.rpow_sub_one hx0 r
    dsimp [x] at hxsub ⊢
    rw [hxsub]
    field_simp [ne_of_gt (by linarith : 0 < 1 + b)]
  have hlogM1 :
      Real.log (two_point_moment r 1 1 b) =
        (r - 1) * Real.log x := by
    rw [hM1]
    exact Real.log_rpow (lt_trans zero_lt_one hx) (r - 1)
  rw [hlogM1, hM1, hV1]
  have hrm : 0 < r - 1 := by linarith
  have hxpow : 0 < x.rpow (r - 1) :=
    Real.rpow_pos_of_pos (lt_trans zero_lt_one hx) _
  have hfactor : 0 < (r - 1) * x.rpow (r - 1) :=
    mul_pos hrm hxpow
  have hcore :
      0 <
        (r * (t * (1 + b)) * (1 + t * b).rpow (r - 1) -
            (1 + t * b).rpow r + (1 - t).rpow r) *
            Real.log x -
          x * two_point_moment r t 1 b *
            Real.log (two_point_moment r t 1 b) := by
    nlinarith
  calc
    0 < (r - 1) * x.rpow (r - 1) *
        ((r * (t * (1 + b)) * (1 + t * b).rpow (r - 1) -
            (1 + t * b).rpow r + (1 - t).rpow r) *
            Real.log x -
          x * two_point_moment r t 1 b *
            Real.log (two_point_moment r t 1 b)) :=
      mul_pos hfactor hcore
    _ = (r * (t * (1 + b)) * (1 + t * b).rpow (r - 1) -
          (1 + t * b).rpow r + (1 - t).rpow r) *
            x.rpow (r - 1) * ((r - 1) * Real.log x) -
        ((r - 1) * x.rpow r) * two_point_moment r t 1 b *
          Real.log (two_point_moment r t 1 b) := by
      have hxsub : x.rpow (r - 1) = x.rpow r / x :=
        Real.rpow_sub_one hx0 r
      rw [hxsub]
      field_simp [hx0]

@[blueprint "lem:rpow-secant-above-geometric-derivative"
  (statement := /-- If $p>1$ and $y>1$, then
  \[
    p y^{(p-1)/2}(y-1)<y^p-1.
  \] -/)
  (proof := /-- Put $m=(p+1)/2$ and
  $F(y)=y^m-y^{1-m}-(2m-1)(y-1)$.  Its derivative vanishes at
  $y=1$, while its second derivative is
  \[
    m(m-1)\bigl(y^{m-2}-y^{-m-1}\bigr)>0
  \]
  for $y>1$.  Thus $F$ is strictly increasing to the right of $1$ and
  $F(y)>F(1)=0$.  Multiplication by $y^{m-1}>0$ and the identities
  $2m-1=p$ and $2m-2=p-1$ give the displayed inequality. -/)
  (title := /-- A strict power secant bound -/)
  (latexEnv := "lemma")]
lemma rpow_secant_above_geometric_derivative
    (p y : ℝ) (hp : 1 < p) (hy : 1 < y) :
    p * y.rpow ((p - 1) / 2) * (y - 1) < y.rpow p - 1 := by
  let m : ℝ := (p + 1) / 2
  let F : ℝ → ℝ := fun z ↦
    z.rpow m - z.rpow (1 - m) - (2 * m - 1) * (z - 1)
  let F1 : ℝ → ℝ := fun z ↦
    m * z.rpow (m - 1) - (1 - m) * z.rpow (-m) - (2 * m - 1)
  have hm : 1 < m := by dsimp [m]; linarith
  have hrpowDeriv (q z : ℝ) (hz : 0 < z) :
      HasDerivAt (fun w : ℝ ↦ w.rpow q)
        (q * z.rpow (q - 1)) z := by
    have hlog := Real.hasDerivAt_log (ne_of_gt hz)
    have hmul := hlog.const_mul q
    have hexp := (Real.hasDerivAt_exp (q * Real.log z)).comp z hmul
    have hev :
        (fun w : ℝ ↦ w.rpow q) =ᶠ[nhds z]
          (fun w : ℝ ↦ Real.exp (q * Real.log w)) := by
      filter_upwards [isOpen_Ioi.eventually_mem
        (show z ∈ Set.Ioi (0 : ℝ) by exact hz)] with w hw
      calc
        w.rpow q = Real.exp (Real.log w * q) :=
          Real.rpow_def_of_pos hw q
        _ = Real.exp (q * Real.log w) := by congr 1 <;> ring
    have hfinal := hexp.congr_of_eventuallyEq hev
    have hcoef :
        Real.exp (q * Real.log z) * (q * z⁻¹) =
          q * z.rpow (q - 1) := by
      have hexpeq : Real.exp (q * Real.log z) = z.rpow q := by
        symm
        calc
          z.rpow q = Real.exp (Real.log z * q) :=
            Real.rpow_def_of_pos hz q
          _ = Real.exp (q * Real.log z) := by congr 1 <;> ring
      have hsub : z.rpow (q - 1) = z.rpow q / z :=
        Real.rpow_sub_one (ne_of_gt hz) q
      rw [hexpeq, hsub]
      field_simp [ne_of_gt hz]
    rw [hcoef] at hfinal
    exact hfinal
  have hFderiv (z : ℝ) (hz : 0 < z) : HasDerivAt F (F1 z) z := by
    have h₁ := hrpowDeriv m z hz
    have h₂ := hrpowDeriv (1 - m) z hz
    have h₃ := ((hasDerivAt_id z).sub_const 1).const_mul (2 * m - 1)
    have h := h₁.sub h₂ |>.sub h₃
    rw [show 1 - m - 1 = -m by ring] at h
    have h' : HasDerivAt F
        (m * z.rpow (m - 1) -
          (1 - m) * z.rpow (-m) - (2 * m - 1) * 1) z :=
      h.congr_of_eventuallyEq (by
        filter_upwards with w
        rfl)
    have hcoef :
        m * z.rpow (m - 1) -
            (1 - m) * z.rpow (-m) - (2 * m - 1) * 1 =
          F1 z := by
      dsimp only [F1]
      ring
    rw [hcoef] at h'
    exact h'
  have hF1deriv (z : ℝ) (hz : 0 < z) :
      HasDerivAt F1
        (m * (m - 1) *
          (z.rpow (m - 2) - z.rpow (-m - 1))) z := by
    have h₁ := (hrpowDeriv (m - 1) z hz).const_mul m
    have h₂ := (hrpowDeriv (-m) z hz).const_mul (1 - m)
    have h := h₁.sub h₂ |>.sub_const (2 * m - 1)
    have h' : HasDerivAt F1
        (m * ((m - 1) * z.rpow (m - 1 - 1)) -
          (1 - m) * (-m * z.rpow (-m - 1))) z :=
      h.congr_of_eventuallyEq (by
        filter_upwards with w
        rfl)
    have hcoef :
        m * ((m - 1) * z.rpow (m - 1 - 1)) -
            (1 - m) * (-m * z.rpow (-m - 1)) =
          m * (m - 1) *
            (z.rpow (m - 2) - z.rpow (-m - 1)) := by
      rw [show m - 1 - 1 = m - 2 by ring]
      ring
    rw [hcoef] at h'
    exact h'
  have hF1mono : StrictMonoOn F1 (Set.Ici 1) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 1)
    · intro z hz
      have hz' : 1 ≤ z := hz
      exact (hF1deriv z (by linarith)).continuousAt.continuousWithinAt
    · intro z hz
      have hz' : 1 < z := by
        simpa only [interior_Ici, Set.mem_Ioi] using hz
      exact (hF1deriv z (by linarith)).hasDerivWithinAt
    · intro z hz
      have hz' : 1 < z := by
        simpa only [interior_Ici, Set.mem_Ioi] using hz
      have hpow :
          z.rpow (-m - 1) < z.rpow (m - 2) :=
        Real.strictMono_rpow_of_base_gt_one hz' (by linarith)
      have hmm : 0 < m * (m - 1) := by positivity
      exact mul_pos hmm (sub_pos.mpr hpow)
  have hF1pos (z : ℝ) (hz : 1 < z) : 0 < F1 z := by
    have h := hF1mono (show 1 ∈ Set.Ici (1 : ℝ) by simp)
      (show z ∈ Set.Ici (1 : ℝ) by exact hz.le) hz
    have hzero : F1 1 = 0 := by
      have honepow (q : ℝ) : Real.rpow 1 q = 1 := by
        calc
          Real.rpow 1 q = Real.exp (Real.log 1 * q) :=
            Real.rpow_def_of_pos zero_lt_one q
          _ = 1 := by rw [Real.log_one, zero_mul, Real.exp_zero]
      rw [show F1 1 =
          m * Real.rpow 1 (m - 1) -
            (1 - m) * Real.rpow 1 (-m) - (2 * m - 1) by rfl,
        honepow, honepow]
      ring
    linarith
  have hFmono : StrictMonoOn F (Set.Ici 1) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 1)
    · intro z hz
      have hz' : 1 ≤ z := hz
      exact (hFderiv z (by linarith)).continuousAt.continuousWithinAt
    · intro z hz
      have hz' : 1 < z := by
        simpa only [interior_Ici, Set.mem_Ioi] using hz
      exact (hFderiv z (by linarith)).hasDerivWithinAt
    · intro z hz
      exact hF1pos z (by simpa only [interior_Ici, Set.mem_Ioi] using hz)
  have hFy : 0 < F y := by
    have h := hFmono (show 1 ∈ Set.Ici (1 : ℝ) by simp)
      (show y ∈ Set.Ici (1 : ℝ) by exact hy.le) hy
    have hzero : F 1 = 0 := by
      have honepow (q : ℝ) : Real.rpow 1 q = 1 := by
        calc
          Real.rpow 1 q = Real.exp (Real.log 1 * q) :=
            Real.rpow_def_of_pos zero_lt_one q
          _ = 1 := by rw [Real.log_one, zero_mul, Real.exp_zero]
      rw [show F 1 =
          Real.rpow 1 m - Real.rpow 1 (1 - m) -
            (2 * m - 1) * (1 - 1) by rfl,
        honepow, honepow]
      ring
    linarith
  have hym : 0 < y.rpow (m - 1) :=
    Real.rpow_pos_of_pos (lt_trans zero_lt_one hy) _
  have hmul := mul_pos hym hFy
  have hrpow :
      y.rpow (m - 1) * y.rpow m = y.rpow p := by
    calc
      y.rpow (m - 1) * y.rpow m =
          y.rpow ((m - 1) + m) :=
        (Real.rpow_add (lt_trans zero_lt_one hy) (m - 1) m).symm
      _ = y.rpow p := by
        congr 1
        dsimp [m]
        ring
  have hrpow' :
      y.rpow (m - 1) * y.rpow (1 - m) = 1 := by
    calc
      y.rpow (m - 1) * y.rpow (1 - m) =
          y.rpow ((m - 1) + (1 - m)) :=
        (Real.rpow_add (lt_trans zero_lt_one hy) (m - 1) (1 - m)).symm
      _ = 1 := by
        rw [show m - 1 + (1 - m) = 0 by ring]
        exact Real.rpow_zero y
  have hfactor :
      y.rpow (m - 1) = y.rpow ((p - 1) / 2) := by
    congr 1
    dsimp [m]
    ring
  have hexpand :
      y.rpow (m - 1) * F y =
        y.rpow p - 1 -
          p * y.rpow ((p - 1) / 2) * (y - 1) := by
    calc
      y.rpow (m - 1) * F y =
          y.rpow (m - 1) * y.rpow m -
            y.rpow (m - 1) * y.rpow (1 - m) -
            y.rpow (m - 1) * (2 * m - 1) * (y - 1) := by
        dsimp only [F]
        ring
      _ = y.rpow p - 1 -
          p * y.rpow ((p - 1) / 2) * (y - 1) := by
        rw [hrpow, hrpow', hfactor]
        dsimp [m]
        ring
  rw [hexpand] at hmul
  nlinarith

@[blueprint "lem:rpow-bregman-scaling-ratio"
  (statement := /-- Let $r>2$, $0<\lambda<1$, and $0<x<y$.  For
  $h(z)=(1+z)^r-1-rz$, one has
  \[
    h(\lambda y)h(x)<h(\lambda x)h(y).
  \] -/)
  (proof := /-- The strict secant estimate in
  \cref{lem:rpow-secant-above-geometric-derivative}, applied with
  exponent $r-1$, shows after squaring that the elasticity
  \[
    E(z)=\frac{zr((1+z)^{r-1}-1)}
                 {(1+z)^r-1-rz}
  \]
  has positive derivative for $z>0$.  Thus $E(\lambda z)<E(z)$.
  Differentiating $h(\lambda z)/h(z)$ and clearing its positive
  denominator shows that this ratio has negative derivative.  It is
  therefore strictly decreasing, and evaluation at $x<y$ gives the
  claim. -/)
  (title := /-- Strict decrease of a scaled power remainder ratio -/)
  (latexEnv := "lemma")]
lemma rpow_bregman_scaling_ratio
    (r lam x y : ℝ) (hr : 2 < r) (hlam₀ : 0 < lam)
    (hlam₁ : lam < 1) (hx : 0 < x) (hxy : x < y) :
    ((1 + lam * y).rpow r - 1 - r * (lam * y)) *
        ((1 + x).rpow r - 1 - r * x) <
      ((1 + lam * x).rpow r - 1 - r * (lam * x)) *
        ((1 + y).rpow r - 1 - r * y) := by
  let H : ℝ → ℝ := fun z ↦ (1 + z).rpow r - 1 - r * z
  let H1 : ℝ → ℝ := fun z ↦ r * ((1 + z).rpow (r - 1) - 1)
  let H2 : ℝ → ℝ := fun z ↦
    r * (r - 1) * (1 + z).rpow (r - 2)
  let E : ℝ → ℝ := fun z ↦ z * H1 z / H z
  let R : ℝ → ℝ := fun z ↦ H (lam * z) / H z
  have hHpos (z : ℝ) (hz : 0 < z) : 0 < H z := by
    have hbern :=
      one_add_mul_self_lt_rpow_one_add (by linarith : -1 ≤ z)
        (ne_of_gt hz) (by linarith : 1 < r)
    have hbern' : 1 + r * z < (1 + z).rpow r := hbern
    dsimp only [H]
    linarith
  have hrpowDeriv (q z : ℝ) (hz : 0 < z) :
      HasDerivAt (fun w : ℝ ↦ (1 + w).rpow q)
        (q * (1 + z).rpow (q - 1)) z := by
    have hbase : HasDerivAt (fun w : ℝ ↦ 1 + w) 1 z :=
      (hasDerivAt_id z).const_add 1
    have hlog :=
      (Real.hasDerivAt_log (ne_of_gt (by linarith : 0 < 1 + z))).comp z hbase
    have hmul := hlog.const_mul q
    have hexp := (Real.hasDerivAt_exp (q * Real.log (1 + z))).comp z hmul
    have hev :
        (fun w : ℝ ↦ (1 + w).rpow q) =ᶠ[nhds z]
          (fun w : ℝ ↦ Real.exp (q * Real.log (1 + w))) := by
      filter_upwards [isOpen_Ioi.eventually_mem
        (show z ∈ Set.Ioi (-1 : ℝ) by
          simp only [Set.mem_Ioi]
          linarith)] with w hw
      have hwpos : 0 < 1 + w := by
        have : -1 < w := hw
        linarith
      calc
        (1 + w).rpow q =
            Real.exp (Real.log (1 + w) * q) :=
          Real.rpow_def_of_pos hwpos q
        _ = Real.exp (q * Real.log (1 + w)) := by congr 1 <;> ring
    have hfinal := hexp.congr_of_eventuallyEq hev
    have hcoef :
        Real.exp (q * Real.log (1 + z)) *
            (q * ((1 + z)⁻¹ * 1)) =
          q * (1 + z).rpow (q - 1) := by
      have hexpeq : Real.exp (q * Real.log (1 + z)) =
          (1 + z).rpow q := by
        symm
        calc
          (1 + z).rpow q =
              Real.exp (Real.log (1 + z) * q) :=
            Real.rpow_def_of_pos (by linarith) q
          _ = Real.exp (q * Real.log (1 + z)) := by congr 1 <;> ring
      have hsub :
          (1 + z).rpow (q - 1) = (1 + z).rpow q / (1 + z) :=
        Real.rpow_sub_one (ne_of_gt (by linarith : 0 < 1 + z)) q
      rw [hexpeq, hsub]
      field_simp [ne_of_gt (by linarith : 0 < 1 + z)]
    rw [hcoef] at hfinal
    exact hfinal
  have hHderiv (z : ℝ) (hz : 0 < z) :
      HasDerivAt H (H1 z) z := by
    have hp := hrpowDeriv r z hz
    have hlin := (hasDerivAt_id z).const_mul r
    have h := hp.sub_const 1 |>.sub hlin
    have h' : HasDerivAt H
        (r * (1 + z).rpow (r - 1) - r * 1) z :=
      h.congr_of_eventuallyEq (by
        filter_upwards with w
        dsimp only [H, id_eq, Pi.sub_apply])
    have hcoef :
        r * (1 + z).rpow (r - 1) - r * 1 = H1 z := by
      dsimp only [H1]
      ring
    rw [hcoef] at h'
    exact h'
  have hH1deriv (z : ℝ) (hz : 0 < z) :
      HasDerivAt H1 (H2 z) z := by
    have hp := (hrpowDeriv (r - 1) z hz).const_mul r
    have h := hp.sub_const r
    have h' : HasDerivAt H1
        (r * ((r - 1) * (1 + z).rpow (r - 1 - 1))) z :=
      h.congr_of_eventuallyEq (by
        filter_upwards with w
        dsimp only [H1]
        ring)
    have hcoef :
        r * ((r - 1) * (1 + z).rpow (r - 1 - 1)) = H2 z := by
      dsimp only [H2]
      rw [show r - 1 - 1 = r - 2 by ring]
      ring
    rw [hcoef] at h'
    exact h'
  have hEderiv (z : ℝ) (hz : 0 < z) :
      HasDerivAt E
        (((H1 z + z * H2 z) * H z - z * (H1 z) ^ 2) /
          (H z) ^ 2) z := by
    have hnum := (hasDerivAt_id z).mul (hH1deriv z hz)
    have hquot := hnum.div (hHderiv z hz) (ne_of_gt (hHpos z hz))
    have h' : HasDerivAt E
        (((1 * H1 z + z * H2 z) * H z -
          z * H1 z * H1 z) / H z ^ 2) z :=
      hquot.congr_of_eventuallyEq (by
        filter_upwards with w
        rfl)
    have hcoef :
        ((1 * H1 z + z * H2 z) * H z -
            z * H1 z * H1 z) / H z ^ 2 =
          ((H1 z + z * H2 z) * H z - z * (H1 z) ^ 2) /
            (H z) ^ 2 := by ring
    rw [hcoef] at h'
    exact h'
  have hEderivpos (z : ℝ) (hz : 0 < z) :
      0 < ((H1 z + z * H2 z) * H z - z * (H1 z) ^ 2) /
        (H z) ^ 2 := by
    have hsec :=
      rpow_secant_above_geometric_derivative (r - 1) (1 + z)
        (by linarith) (by linarith)
    have hsec' :
        (r - 1) * (1 + z).rpow ((r - 2) / 2) * z <
          (1 + z).rpow (r - 1) - 1 := by
      convert hsec using 1 <;> ring
    have hleft :
        0 < (r - 1) * (1 + z).rpow ((r - 2) / 2) * z := by
      exact mul_pos
        (mul_pos (by linarith) (Real.rpow_pos_of_pos (by linarith) _)) hz
    have hright : 0 < (1 + z).rpow (r - 1) - 1 :=
      lt_trans hleft hsec'
    have hsquares :
        ((r - 1) * (1 + z).rpow ((r - 2) / 2) * z) ^ 2 <
          ((1 + z).rpow (r - 1) - 1) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hsec') (add_pos hright hleft)]
    have hpowhalf :
        (1 + z).rpow ((r - 2) / 2) *
            (1 + z).rpow ((r - 2) / 2) =
          (1 + z).rpow (r - 2) := by
      calc
        _ = (1 + z).rpow (((r - 2) / 2) + ((r - 2) / 2)) :=
          (Real.rpow_add (by linarith : 0 < 1 + z) _ _).symm
        _ = _ := by congr 1 <;> ring
    have hcore :
        0 < ((1 + z).rpow (r - 1) - 1) ^ 2 -
          (r - 1) ^ 2 * (1 + z).rpow (r - 2) * z ^ 2 := by
      rw [← hpowhalf]
      nlinarith
    have hrsub :
        (1 + z).rpow (r - 1) =
          (1 + z).rpow r / (1 + z) :=
      Real.rpow_sub_one (ne_of_gt (by linarith : 0 < 1 + z)) r
    have hrsub₂ :
        (1 + z).rpow (r - 2) =
          (1 + z).rpow (r - 1) / (1 + z) := by
      have h := Real.rpow_sub_one
        (ne_of_gt (by linarith : 0 < 1 + z)) (r - 1)
      rw [show r - 1 - 1 = r - 2 by ring] at h
      exact h
    have hrmul :
        (1 + z).rpow r =
          (1 + z).rpow (r - 1) * (1 + z) := by
      rw [hrsub]
      field_simp [ne_of_gt (by linarith : 0 < 1 + z)]
    have hrmul₂ :
        (1 + z).rpow (r - 1) =
          (1 + z).rpow (r - 2) * (1 + z) := by
      rw [hrsub₂]
      field_simp [ne_of_gt (by linarith : 0 < 1 + z)]
    have hid :
        (H1 z + z * H2 z) * H z - z * (H1 z) ^ 2 =
          r * (((1 + z).rpow (r - 1) - 1) ^ 2 -
            (r - 1) ^ 2 * (1 + z).rpow (r - 2) * z ^ 2) := by
      dsimp only [H, H1, H2]
      rw [hrmul, hrmul₂]
      ring
    rw [hid]
    exact div_pos (mul_pos (by linarith) hcore)
      (sq_pos_of_pos (hHpos z hz))
  have hEmono : StrictMonoOn E (Set.Ioi 0) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioi 0)
    · intro z hz
      exact (hEderiv z hz).continuousAt.continuousWithinAt
    · intro z hz
      have hz' : 0 < z := by
        simpa only [interior_Ioi, Set.mem_Ioi] using hz
      exact (hEderiv z hz').hasDerivWithinAt
    · intro z hz
      have hz' : 0 < z := by
        simpa only [interior_Ioi, Set.mem_Ioi] using hz
      exact hEderivpos z hz'
  have hRderiv (z : ℝ) (hz : 0 < z) :
      HasDerivAt R
        ((lam * H1 (lam * z) * H z - H (lam * z) * H1 z) /
          (H z) ^ 2) z := by
    have hlz : 0 < lam * z := mul_pos hlam₀ hz
    have hcomp :=
      (hHderiv (lam * z) hlz).comp z ((hasDerivAt_id z).const_mul lam)
    have hquot := hcomp.div (hHderiv z hz) (ne_of_gt (hHpos z hz))
    have h' : HasDerivAt R
        (((H1 (lam * z) * (lam * 1)) * H z -
          H (lam * z) * H1 z) / H z ^ 2) z :=
      hquot.congr_of_eventuallyEq (by
        filter_upwards with w
        dsimp only [R, Function.comp_apply, Pi.div_apply])
    have hcoef :
        ((H1 (lam * z) * (lam * 1)) * H z -
            H (lam * z) * H1 z) / H z ^ 2 =
          (lam * H1 (lam * z) * H z -
            H (lam * z) * H1 z) / H z ^ 2 := by ring
    rw [hcoef] at h'
    exact h'
  have hRderivneg (z : ℝ) (hz : 0 < z) :
      (lam * H1 (lam * z) * H z - H (lam * z) * H1 z) /
          (H z) ^ 2 < 0 := by
    have hlz : 0 < lam * z := mul_pos hlam₀ hz
    have hlzlt : lam * z < z := by
      nlinarith [mul_lt_mul_of_pos_right hlam₁ hz]
    have hE := hEmono hlz hz hlzlt
    have hcross :=
      (div_lt_div_iff₀ (hHpos (lam * z) hlz) (hHpos z hz)).mp hE
    have hnum :
        lam * H1 (lam * z) * H z <
          H (lam * z) * H1 z := by
      have hzmul :
          z * (lam * H1 (lam * z) * H z) <
            z * (H (lam * z) * H1 z) := by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using hcross
      exact lt_of_mul_lt_mul_left hzmul (le_of_lt hz)
    exact div_neg_of_neg_of_pos (sub_neg.mpr hnum)
      (sq_pos_of_pos (hHpos z hz))
  have hRanti : StrictAntiOn R (Set.Ioi 0) := by
    apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Ioi 0)
    · intro z hz
      exact (hRderiv z hz).continuousAt.continuousWithinAt
    · intro z hz
      have hz' : 0 < z := by
        simpa only [interior_Ioi, Set.mem_Ioi] using hz
      exact (hRderiv z hz').hasDerivWithinAt
    · intro z hz
      have hz' : 0 < z := by
        simpa only [interior_Ioi, Set.mem_Ioi] using hz
      exact hRderivneg z hz'
  have hy : 0 < y := lt_trans hx hxy
  have hratio := hRanti hx hy hxy
  have hcross :=
    (div_lt_div_iff₀ (hHpos y hy) (hHpos x hx)).mp hratio
  simpa only [R, H] using hcross

@[blueprint "lem:rpow-bregman-subhomogeneous"
  (statement := /-- Let $r>2$, $0<\lambda<1$, and $x>0$.  For
  $h(x)=(1+x)^r-1-rx$, one has
  \[
    \lambda^r h(x)<h(\lambda x).
  \] -/)
  (proof := /-- The strict Bernoulli inequality with exponent $r-1$
  gives
  \[
    xh'(x)-rh(x)
      =-r\bigl((1+x)^{r-1}-1-(r-1)x\bigr)<0.
  \]
  Hence $h(x)/x^r$ is strictly decreasing on the positive half-line.
  Comparing its values at $\lambda x<x$, and using
  $(\lambda x)^r=\lambda^r x^r$, proves the claim. -/)
  (title := /-- Strict subhomogeneity of the power remainder -/)
  (latexEnv := "lemma")]
lemma rpow_bregman_subhomogeneous
    (r lam x : ℝ) (hr : 2 < r) (hlam₀ : 0 < lam)
    (hlam₁ : lam < 1) (hx : 0 < x) :
    lam.rpow r * ((1 + x).rpow r - 1 - r * x) <
      (1 + lam * x).rpow r - 1 - r * (lam * x) := by
  let H : ℝ → ℝ := fun z ↦ (1 + z).rpow r - 1 - r * z
  let H1 : ℝ → ℝ := fun z ↦ r * ((1 + z).rpow (r - 1) - 1)
  let S : ℝ → ℝ := fun z ↦ H z / z.rpow r
  have hHpos (z : ℝ) (hz : 0 < z) : 0 < H z := by
    have hbern :
        1 + r * z < (1 + z).rpow r :=
      one_add_mul_self_lt_rpow_one_add (by linarith : -1 ≤ z)
        (ne_of_gt hz) (by linarith : 1 < r)
    dsimp only [H]
    linarith
  have hrpowDeriv (q z : ℝ) (hz : 0 < z) :
      HasDerivAt (fun w : ℝ ↦ w.rpow q)
        (q * z.rpow (q - 1)) z := by
    have hlog := Real.hasDerivAt_log (ne_of_gt hz)
    have hmul := hlog.const_mul q
    have hexp := (Real.hasDerivAt_exp (q * Real.log z)).comp z hmul
    have hev :
        (fun w : ℝ ↦ w.rpow q) =ᶠ[nhds z]
          (fun w : ℝ ↦ Real.exp (q * Real.log w)) := by
      filter_upwards [isOpen_Ioi.eventually_mem
        (show z ∈ Set.Ioi (0 : ℝ) by exact hz)] with w hw
      calc
        w.rpow q = Real.exp (Real.log w * q) :=
          Real.rpow_def_of_pos hw q
        _ = Real.exp (q * Real.log w) := by congr 1 <;> ring
    have hfinal := hexp.congr_of_eventuallyEq hev
    have hcoef :
        Real.exp (q * Real.log z) * (q * z⁻¹) =
          q * z.rpow (q - 1) := by
      have hexpeq : Real.exp (q * Real.log z) = z.rpow q := by
        symm
        calc
          z.rpow q = Real.exp (Real.log z * q) :=
            Real.rpow_def_of_pos hz q
          _ = Real.exp (q * Real.log z) := by congr 1 <;> ring
      have hsub : z.rpow (q - 1) = z.rpow q / z :=
        Real.rpow_sub_one (ne_of_gt hz) q
      rw [hexpeq, hsub]
      field_simp [ne_of_gt hz]
    rw [hcoef] at hfinal
    exact hfinal
  have hrpowShiftDeriv (q z : ℝ) (hz : 0 < z) :
      HasDerivAt (fun w : ℝ ↦ (1 + w).rpow q)
        (q * (1 + z).rpow (q - 1)) z := by
    have hbase : HasDerivAt (fun w : ℝ ↦ 1 + w) 1 z :=
      (hasDerivAt_id z).const_add 1
    have hlog :=
      (Real.hasDerivAt_log (ne_of_gt (by linarith : 0 < 1 + z))).comp z hbase
    have hmul := hlog.const_mul q
    have hexp := (Real.hasDerivAt_exp (q * Real.log (1 + z))).comp z hmul
    have hev :
        (fun w : ℝ ↦ (1 + w).rpow q) =ᶠ[nhds z]
          (fun w : ℝ ↦ Real.exp (q * Real.log (1 + w))) := by
      filter_upwards [isOpen_Ioi.eventually_mem
        (show z ∈ Set.Ioi (-1 : ℝ) by
          simp only [Set.mem_Ioi]
          linarith)] with w hw
      have hwpos : 0 < 1 + w := by
        have : -1 < w := hw
        linarith
      calc
        (1 + w).rpow q =
            Real.exp (Real.log (1 + w) * q) :=
          Real.rpow_def_of_pos hwpos q
        _ = Real.exp (q * Real.log (1 + w)) := by congr 1 <;> ring
    have hfinal := hexp.congr_of_eventuallyEq hev
    have hcoef :
        Real.exp (q * Real.log (1 + z)) *
            (q * ((1 + z)⁻¹ * 1)) =
          q * (1 + z).rpow (q - 1) := by
      have hexpeq : Real.exp (q * Real.log (1 + z)) =
          (1 + z).rpow q := by
        symm
        calc
          (1 + z).rpow q =
              Real.exp (Real.log (1 + z) * q) :=
            Real.rpow_def_of_pos (by linarith) q
          _ = Real.exp (q * Real.log (1 + z)) := by congr 1 <;> ring
      have hsub :
          (1 + z).rpow (q - 1) = (1 + z).rpow q / (1 + z) :=
        Real.rpow_sub_one (ne_of_gt (by linarith : 0 < 1 + z)) q
      rw [hexpeq, hsub]
      field_simp [ne_of_gt (by linarith : 0 < 1 + z)]
    rw [hcoef] at hfinal
    exact hfinal
  have hHderiv (z : ℝ) (hz : 0 < z) :
      HasDerivAt H (H1 z) z := by
    have hp := hrpowShiftDeriv r z hz
    have hlin := (hasDerivAt_id z).const_mul r
    have h := hp.sub_const 1 |>.sub hlin
    have h' : HasDerivAt H
        (r * (1 + z).rpow (r - 1) - r * 1) z :=
      h.congr_of_eventuallyEq (by
        filter_upwards with w
        dsimp only [H, id_eq, Pi.sub_apply])
    have hcoef :
        r * (1 + z).rpow (r - 1) - r * 1 = H1 z := by
      dsimp only [H1]
      ring
    rw [hcoef] at h'
    exact h'
  have hSderiv (z : ℝ) (hz : 0 < z) :
      HasDerivAt S
        ((H1 z * z.rpow r -
          H z * (r * z.rpow (r - 1))) / (z.rpow r) ^ 2) z := by
    have hquot :=
      (hHderiv z hz).div (hrpowDeriv r z hz)
        (ne_of_gt (Real.rpow_pos_of_pos hz r))
    exact hquot.congr_of_eventuallyEq (by
      filter_upwards with w
      dsimp only [S, Pi.div_apply])
  have hSderivneg (z : ℝ) (hz : 0 < z) :
      (H1 z * z.rpow r -
          H z * (r * z.rpow (r - 1))) / (z.rpow r) ^ 2 < 0 := by
    have hbern :
        1 + (r - 1) * z < (1 + z).rpow (r - 1) :=
      one_add_mul_self_lt_rpow_one_add (by linarith : -1 ≤ z)
        (ne_of_gt hz) (by linarith : 1 < r - 1)
    have hrem :
        0 < (1 + z).rpow (r - 1) - 1 - (r - 1) * z := by
      linarith
    have hzsub :
        z.rpow (r - 1) = z.rpow r / z :=
      Real.rpow_sub_one (ne_of_gt hz) r
    have hzmul : z.rpow r = z.rpow (r - 1) * z := by
      rw [hzsub]
      field_simp [ne_of_gt hz]
    have hid :
        H1 z * z.rpow r - H z * (r * z.rpow (r - 1)) =
          -r * z.rpow (r - 1) *
            ((1 + z).rpow (r - 1) - 1 - (r - 1) * z) := by
      have hshift :
          (1 + z).rpow r =
            (1 + z).rpow (r - 1) * (1 + z) := by
        have h :
            (1 + z).rpow (r - 1) =
              (1 + z).rpow r / (1 + z) :=
          Real.rpow_sub_one
            (ne_of_gt (by linarith : 0 < 1 + z)) r
        rw [h]
        field_simp [ne_of_gt (by linarith : 0 < 1 + z)]
      dsimp only [H, H1]
      rw [hzmul, hshift]
      ring
    rw [hid]
    have hprod :
        0 < r * z.rpow (r - 1) *
          ((1 + z).rpow (r - 1) - 1 - (r - 1) * z) :=
      mul_pos (mul_pos (by linarith)
        (Real.rpow_pos_of_pos hz _)) hrem
    exact div_neg_of_neg_of_pos (by nlinarith)
      (sq_pos_of_pos (Real.rpow_pos_of_pos hz r))
  have hSanti : StrictAntiOn S (Set.Ioi 0) := by
    apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Ioi 0)
    · intro z hz
      exact (hSderiv z hz).continuousAt.continuousWithinAt
    · intro z hz
      have hz' : 0 < z := by
        simpa only [interior_Ioi, Set.mem_Ioi] using hz
      exact (hSderiv z hz').hasDerivWithinAt
    · intro z hz
      have hz' : 0 < z := by
        simpa only [interior_Ioi, Set.mem_Ioi] using hz
      exact hSderivneg z hz'
  have hlx : 0 < lam * x := mul_pos hlam₀ hx
  have hlxlt : lam * x < x := by
    nlinarith [mul_lt_mul_of_pos_right hlam₁ hx]
  have hratio := hSanti hlx hx hlxlt
  dsimp only [S] at hratio
  have hcross :=
    (div_lt_div_iff₀ (Real.rpow_pos_of_pos hx r)
      (Real.rpow_pos_of_pos hlx r)).mp hratio
  have hcross' :
      H x * (lam * x).rpow r <
        H (lam * x) * x.rpow r := hcross
  have hmulrpow :
      (lam * x).rpow r = lam.rpow r * x.rpow r := by
    exact Real.mul_rpow (le_of_lt hlam₀) (le_of_lt hx)
  rw [hmulrpow] at hcross'
  have hxpow : 0 < x.rpow r := Real.rpow_pos_of_pos hx r
  have hscaled :
      x.rpow r *
          (lam.rpow r * H x) <
        x.rpow r * H (lam * x) := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hcross'
  have hresult :=
    lt_of_mul_lt_mul_left hscaled (le_of_lt hxpow)
  simpa only [H] using hresult

@[blueprint "lem:two-point-u-q-cross"
  (statement := /-- Let $r>2$, $0<t<1$, $0<a\leq1$, and $b>0$.
  Write $M_s=B_r(s;a,b)$ and
  \[
    U_s=(1+sb)^r-(1-sa)^r-rs(a+b)(1-sa)^{r-1}.
  \]
  Then
  \[
    U_t(M_1-1)-U_1(M_t-1)>0.
  \] -/)
  (proof := /-- Put $\lambda=a/(a+b)$ and
  $h(x)=(1+x)^r-1-rx$.  If $a<1$, set
  $x_s=s(a+b)/(1-sa)$.  Direct normalization gives
  \[
    U_s=(1-sa)^rh(x_s),\qquad
    M_s-1=\lambda U_s-(1-sa)^rh(\lambda x_s).
  \]
  Since $0<x_t<x_1$, the strict scaling-ratio inequality
  \cref{lem:rpow-bregman-scaling-ratio} yields the claim after the
  terms containing $\lambda U_tU_1$ cancel.

  If $a=1$, the same identities are used only at $s=t$.  At $s=1$,
  $U_1=(1+b)^r$ and $M_1-1=(1+b)^{r-1}-1$.  The remaining normalized
  inequality is precisely the strict subhomogeneity in
  \cref{lem:rpow-bregman-subhomogeneous}, with
  $\lambda=(1+b)^{-1}$ and $x=t(1+b)/(1-t)$. -/)
  (title := /-- Cross inequality for the two-point power remainders -/)
  (latexEnv := "lemma")]
lemma two_point_u_q_cross
    (r t a b : ℝ) (hr : 2 < r) (ht₀ : 0 < t) (ht₁ : t < 1)
    (ha₀ : 0 < a) (ha₁ : a ≤ 1) (hb₀ : 0 < b) :
    0 <
      (Real.rpow (1 + t * b) r - Real.rpow (1 - t * a) r -
          r * (t * (a + b)) * Real.rpow (1 - t * a) (r - 1)) *
        (two_point_moment r 1 a b - 1) -
      (Real.rpow (1 + b) r - Real.rpow (1 - a) r -
          r * (a + b) * Real.rpow (1 - a) (r - 1)) *
        (two_point_moment r t a b - 1) := by
  let lam : ℝ := a / (a + b)
  let H : ℝ → ℝ := fun x ↦ (1 + x).rpow r - 1 - r * x
  have hab : 0 < a + b := add_pos ha₀ hb₀
  have hlam₀ : 0 < lam := div_pos ha₀ hab
  have hlam₁ : lam < 1 := by
    dsimp only [lam]
    exact (div_lt_one hab).mpr (by linarith)
  have hdivrpow (u v p : ℝ) (hu : 0 < u) (hv : 0 < v) :
      (u / v).rpow p = u.rpow p / v.rpow p := by
    calc
      (u / v).rpow p =
          Real.exp (Real.log (u / v) * p) :=
        Real.rpow_def_of_pos (div_pos hu hv) p
      _ = Real.exp ((Real.log u - Real.log v) * p) := by
        rw [Real.log_div (ne_of_gt hu) (ne_of_gt hv)]
      _ = Real.exp (Real.log u * p) / Real.exp (Real.log v * p) := by
        rw [sub_mul, Real.exp_sub]
      _ = u.rpow p / v.rpow p := by
        congr 1
        · exact (Real.rpow_def_of_pos hu p).symm
        · exact (Real.rpow_def_of_pos hv p).symm
  have hU (s : ℝ) (hs : 0 < s) (hc : 0 < 1 - s * a) :
      Real.rpow (1 + s * b) r - Real.rpow (1 - s * a) r -
          r * (s * (a + b)) * Real.rpow (1 - s * a) (r - 1) =
        Real.rpow (1 - s * a) r *
          H (s * (a + b) / (1 - s * a)) := by
    have hA : 0 < 1 + s * b := by positivity
    have hbase :
        1 + s * (a + b) / (1 - s * a) =
          (1 + s * b) / (1 - s * a) := by
      field_simp [ne_of_gt hc]
      ring
    have hdiv :
        ((1 + s * b) / (1 - s * a)).rpow r =
          (1 + s * b).rpow r / (1 - s * a).rpow r :=
      hdivrpow (1 + s * b) (1 - s * a) r hA hc
    have hcsub :
        (1 - s * a).rpow (r - 1) =
          (1 - s * a).rpow r / (1 - s * a) :=
      Real.rpow_sub_one (ne_of_gt hc) r
    dsimp only [H]
    rw [hbase, hdiv, hcsub]
    field_simp [ne_of_gt hc,
      ne_of_gt (Real.rpow_pos_of_pos hc r)]
  have hW (s : ℝ) (hs : 0 < s) (hc : 0 < 1 - s * a) :
      Real.rpow (1 - s * a) r *
          H (lam * (s * (a + b) / (1 - s * a))) =
        1 - Real.rpow (1 - s * a) r -
          r * (s * a) * Real.rpow (1 - s * a) (r - 1) := by
    have hbase :
        1 + lam * (s * (a + b) / (1 - s * a)) =
          1 / (1 - s * a) := by
      dsimp only [lam]
      field_simp [ne_of_gt hab, ne_of_gt hc,
        ne_of_gt (by nlinarith : 0 < 1 - a * s)]
      ring
    have hdiv :
        (1 / (1 - s * a)).rpow r =
          1 / (1 - s * a).rpow r := by
      rw [hdivrpow 1 (1 - s * a) r zero_lt_one hc]
      have honepow : Real.rpow 1 r = 1 := by
        calc
          Real.rpow 1 r = Real.exp (Real.log 1 * r) :=
            Real.rpow_def_of_pos zero_lt_one r
          _ = 1 := by rw [Real.log_one, zero_mul, Real.exp_zero]
      rw [honepow]
    have hcsub :
        (1 - s * a).rpow (r - 1) =
          (1 - s * a).rpow r / (1 - s * a) :=
      Real.rpow_sub_one (ne_of_gt hc) r
    dsimp only [H, lam]
    rw [hbase, hdiv, hcsub]
    field_simp [ne_of_gt hc,
      ne_of_gt (Real.rpow_pos_of_pos hc r)]
  have hQ (s : ℝ) (hs : 0 < s) (hc : 0 < 1 - s * a) :
      two_point_moment r s a b - 1 =
        lam *
            (Real.rpow (1 + s * b) r -
              Real.rpow (1 - s * a) r -
              r * (s * (a + b)) *
                Real.rpow (1 - s * a) (r - 1)) -
          Real.rpow (1 - s * a) r *
            H (lam * (s * (a + b) / (1 - s * a))) := by
    rw [hW s hs hc]
    rw [two_point_moment]
    dsimp only [lam]
    field_simp [ne_of_gt hab]
    ring
  rcases lt_or_eq_of_le ha₁ with ha₁' | rfl
  · have hct : 0 < 1 - t * a := by nlinarith [mul_lt_mul_of_pos_left ht₁ ha₀]
    have hc1 : 0 < 1 - a := sub_pos.mpr ha₁'
    let xt : ℝ := t * (a + b) / (1 - t * a)
    let x1 : ℝ := (a + b) / (1 - a)
    have hxt : 0 < xt := div_pos (mul_pos ht₀ hab) hct
    have hx1 : 0 < x1 := div_pos hab hc1
    have htx : xt < x1 := by
      dsimp only [xt, x1]
      apply (div_lt_div_iff₀ hct hc1).mpr
      nlinarith [mul_pos (sub_pos.mpr ht₁) hab]
    have hratio :=
      rpow_bregman_scaling_ratio r lam xt x1 hr hlam₀ hlam₁ hxt htx
    have hctpow : 0 < (1 - t * a).rpow r :=
      Real.rpow_pos_of_pos hct r
    have hc1pow : 0 < (1 - a).rpow r :=
      Real.rpow_pos_of_pos hc1 r
    have hscaled :
        0 < (1 - t * a).rpow r * (1 - a).rpow r *
          (H (lam * xt) * H x1 - H (lam * x1) * H xt) :=
      mul_pos (mul_pos hctpow hc1pow) (sub_pos.mpr hratio)
    have hUt := hU t ht₀ hct
    have hU1 := hU 1 zero_lt_one
      (by simpa only [one_mul] using hc1)
    have hQt := hQ t ht₀ hct
    have hQ1 := hQ 1 zero_lt_one
      (by simpa only [one_mul] using hc1)
    simp only [one_mul] at hU1 hQ1
    change
      (1 + t * b).rpow r - (1 - t * a).rpow r -
          r * (t * (a + b)) * (1 - t * a).rpow (r - 1) =
        (1 - t * a).rpow r * H xt at hUt
    change
      (1 + b).rpow r - (1 - a).rpow r -
          r * (a + b) * (1 - a).rpow (r - 1) =
        (1 - a).rpow r * H x1 at hU1
    change
      two_point_moment r t a b - 1 =
        lam * ((1 + t * b).rpow r - (1 - t * a).rpow r -
          r * (t * (a + b)) * (1 - t * a).rpow (r - 1)) -
        (1 - t * a).rpow r * H (lam * xt) at hQt
    change
      two_point_moment r 1 a b - 1 =
        lam * ((1 + b).rpow r - (1 - a).rpow r -
          r * (a + b) * (1 - a).rpow (r - 1)) -
        (1 - a).rpow r * H (lam * x1) at hQ1
    rw [hQt, hQ1, hUt, hU1]
    nlinarith [hscaled]
  · have hct : 0 < 1 - t := by linarith
    let xt : ℝ := t * (1 + b) / (1 - t)
    have hxt : 0 < xt := div_pos (mul_pos ht₀ (by linarith)) hct
    have hlam :
        lam = 1 / (1 + b) := by rfl
    have hsub :=
      rpow_bregman_subhomogeneous r lam xt hr hlam₀ hlam₁ hxt
    change lam.rpow r * H xt < H (lam * xt) at hsub
    have hbase :
        1 + b = 1 / lam := by
      rw [hlam]
      field_simp [ne_of_gt (by linarith : 0 < 1 + b)]
    have hlampow : 0 < lam.rpow r :=
      Real.rpow_pos_of_pos hlam₀ r
    have hprod :
        (1 + b).rpow r * lam.rpow r = 1 := by
      rw [hbase, hdivrpow 1 lam r zero_lt_one hlam₀]
      have honepow : Real.rpow 1 r = 1 := by
        calc
          Real.rpow 1 r = Real.exp (Real.log 1 * r) :=
            Real.rpow_def_of_pos zero_lt_one r
          _ = 1 := by rw [Real.log_one, zero_mul, Real.exp_zero]
      rw [honepow]
      field_simp [ne_of_gt hlampow]
    have hnorm :
        H xt <
          (1 + b).rpow r * H (lam * xt) := by
      have hmulsub :
          (1 + b).rpow r * (lam.rpow r * H xt) <
            (1 + b).rpow r * H (lam * xt) :=
        mul_lt_mul_of_pos_left hsub
          (Real.rpow_pos_of_pos (by linarith : 0 < 1 + b) r)
      calc
        H xt = 1 * H xt := by ring
        _ = ((1 + b).rpow r * lam.rpow r) * H xt := by rw [hprod]
        _ = (1 + b).rpow r * (lam.rpow r * H xt) := by ring
        _ < (1 + b).rpow r * H (lam * xt) := hmulsub
    have hctpow : 0 < (1 - t).rpow r :=
      Real.rpow_pos_of_pos hct r
    have hscaled :
        0 < (1 - t).rpow r *
          ((1 + b).rpow r * H (lam * xt) - H xt) :=
      mul_pos hctpow (sub_pos.mpr hnorm)
    have hUt := hU t ht₀ (by simpa only [mul_one] using hct)
    have hQt := hQ t ht₀ (by simpa only [mul_one] using hct)
    simp only [mul_one] at hUt hQt
    change
      (1 + t * b).rpow r - (1 - t).rpow r -
          r * (t * (1 + b)) * (1 - t).rpow (r - 1) =
        (1 - t).rpow r * H xt at hUt
    change
      two_point_moment r t 1 b - 1 =
        lam * ((1 + t * b).rpow r - (1 - t).rpow r -
          r * (t * (1 + b)) * (1 - t).rpow (r - 1)) -
        (1 - t).rpow r * H (lam * xt) at hQt
    have hr0 : r ≠ 0 := by linarith
    have hrm0 : r - 1 ≠ 0 := by linarith
    have hzero_r : Real.rpow 0 r = 0 := Real.zero_rpow hr0
    have hzero_rm : Real.rpow 0 (r - 1) = 0 :=
      Real.zero_rpow hrm0
    have hU1 :
        Real.rpow (1 + b) r - Real.rpow (1 - 1) r -
            r * (1 + b) * Real.rpow (1 - 1) (r - 1) =
          Real.rpow (1 + b) r := by
      rw [show 1 - (1 : ℝ) = 0 by ring, hzero_r, hzero_rm]
      ring
    have hM1 :
        two_point_moment r 1 1 b =
          (1 + b).rpow (r - 1) := by
      rw [two_point_moment]
      norm_num only [one_mul]
      rw [hzero_r]
      have hsubpow :
          (1 + b).rpow (r - 1) =
            (1 + b).rpow r / (1 + b) :=
        Real.rpow_sub_one (ne_of_gt (by linarith : 0 < 1 + b)) r
      rw [hsubpow]
      field_simp [ne_of_gt (by linarith : 0 < 1 + b)]
      ring
    have hQ1 :
        (1 + b).rpow (r - 1) - 1 =
          lam * (1 + b).rpow r -
            1 := by
      rw [hlam]
      have hsubpow :
          (1 + b).rpow (r - 1) =
            (1 + b).rpow r / (1 + b) :=
        Real.rpow_sub_one (ne_of_gt (by linarith : 0 < 1 + b)) r
      rw [hsubpow]
      field_simp [ne_of_gt (by linarith : 0 < 1 + b)]
    simp only [mul_one]
    rw [hQt, hM1, hU1, hUt, hQ1]
    nlinarith [hscaled]

@[blueprint "lem:two-point-log-ratio-derivative-sign"
  (statement := /-- Let $r,t,a,b\in\mathbb R$ satisfy $r\geq2$, $0<t<1$,
  $0<a\leq1$, and $b>0$.  For
  $s\in\{t,1\}$ put
  \[
    M_s=B_r(s;a,b),\quad d_s=s(a+b),\quad A_s=1+sb,\quad C_s=1-sa,
  \]
  and
  \[
    U_s=A_s^r-C_s^r-rd_sC_s^{r-1},\qquad
    V_s=rd_sA_s^{r-1}-A_s^r+C_s^r.
  \]
  Then
  \[
    U_tM_1\log M_1-U_1M_t\log M_t>0.
  \]
  If, in addition, $a=1$, then
  \[
    V_tM_1\log M_1-V_1M_t\log M_t>0.
  \] -/)
  (proof := /-- First suppose that $r=2$.  Expanding the real powers
  gives
  \[
    U_t=t^2(a+b)^2,\qquad U_1=(a+b)^2.
  \]
  The first assertion is therefore exactly
  \cref{lem:two-point-log-ratio-quadratic-core}.  If $a=1$, the same
  expansion gives $V_t=t^2(1+b)^2$ and $V_1=(1+b)^2$, so the second
  assertion follows from the same lemma.

  Now suppose that $r>2$, and write $M_s=B_r(s;a,b)$ and
  $Q_s=M_s-1$.  From \cref{def:two-point-moment}, the strict Bernoulli
  inequality applied to the positive branch and the weak Bernoulli
  inequality applied to the nonnegative branch show that $M_s>1$ for
  $0<s\leq1$.  Strict convexity of $x\mapsto x^r$ also gives
  $M_t<M_1$.  Consequently,
  \[
    0<Q_t<Q_1,\qquad M_1\log M_1>0.
  \]
  A further strict Bernoulli estimate, after scaling by $(1-a)^r$ when
  $a<1$ and by direct evaluation when $a=1$, gives $U_1>0$.

  By \cref{lem:two-point-u-q-cross},
  \[
    U_1Q_t<U_tQ_1,
  \]
  and hence $U_1(Q_t/Q_1)<U_t$.  Applying
  \cref{lem:mul-log-one-add-contraction} with
  $u=Q_t/Q_1$ and $z=Q_1$ yields
  \[
    M_t\log M_t
      <\frac{Q_t}{Q_1}M_1\log M_1.
  \]
  Multiplication by the positive quantities $U_1$ and
  $M_1\log M_1$, respectively, now gives
  \[
    U_1M_t\log M_t
      <U_1\frac{Q_t}{Q_1}M_1\log M_1
      <U_tM_1\log M_1,
  \]
  which is the first assertion.

  Finally, if $a=1$, the second assertion is precisely
  \cref{lem:two-point-boundary-derivative-sign}, after simplifying
  $1-a=0$ and $0^r=0$, the latter being valid because $r>2$. -/)
  (title := /-- Strict signs of the two-point quotient numerators -/)
  (latexEnv := "lemma")]
lemma two_point_log_ratio_derivative_sign
    (r t a b : ℝ) (hr : 2 ≤ r) (ht₀ : 0 < t) (ht₁ : t < 1)
    (ha₀ : 0 < a) (ha₁ : a ≤ 1) (hb₀ : 0 < b) :
    0 <
        (Real.rpow (1 + t * b) r - Real.rpow (1 - t * a) r -
            r * (t * (a + b)) * Real.rpow (1 - t * a) (r - 1)) *
          two_point_moment r 1 a b * Real.log (two_point_moment r 1 a b) -
        (Real.rpow (1 + b) r - Real.rpow (1 - a) r -
            r * (a + b) * Real.rpow (1 - a) (r - 1)) *
          two_point_moment r t a b * Real.log (two_point_moment r t a b) ∧
      (a = 1 →
        0 <
          (r * (t * (a + b)) * Real.rpow (1 + t * b) (r - 1) -
              Real.rpow (1 + t * b) r + Real.rpow (1 - t * a) r) *
            two_point_moment r 1 a b * Real.log (two_point_moment r 1 a b) -
          (r * (a + b) * Real.rpow (1 + b) (r - 1) -
              Real.rpow (1 + b) r + Real.rpow (1 - a) r) *
            two_point_moment r t a b * Real.log (two_point_moment r t a b)) := by
  rcases eq_or_lt_of_le hr with rfl | hr'
  · constructor
    · have hUt :
          Real.rpow (1 + t * b) 2 - Real.rpow (1 - t * a) 2 -
              2 * (t * (a + b)) * Real.rpow (1 - t * a) (2 - 1) =
            t ^ 2 * (a + b) ^ 2 := by
        rw [show Real.rpow (1 + t * b) 2 = (1 + t * b) ^ 2 by
          exact Real.rpow_two _,
          show Real.rpow (1 - t * a) 2 = (1 - t * a) ^ 2 by
            exact Real.rpow_two _,
          show Real.rpow (1 - t * a) (2 - 1) = 1 - t * a by
            norm_num]
        ring
      have hU1 :
          Real.rpow (1 + b) 2 - Real.rpow (1 - a) 2 -
              2 * (a + b) * Real.rpow (1 - a) (2 - 1) =
            (a + b) ^ 2 := by
        rw [show Real.rpow (1 + b) 2 = (1 + b) ^ 2 by
          exact Real.rpow_two _,
          show Real.rpow (1 - a) 2 = (1 - a) ^ 2 by
            exact Real.rpow_two _,
          show Real.rpow (1 - a) (2 - 1) = 1 - a by
            norm_num]
        ring
      rw [hUt, hU1]
      exact two_point_log_ratio_quadratic_core t a b ht₀ ht₁ ha₀ hb₀
    · intro ha
      subst a
      have hVt :
          2 * (t * (1 + b)) * Real.rpow (1 + t * b) (2 - 1) -
              Real.rpow (1 + t * b) 2 + Real.rpow (1 - t) 2 =
            t ^ 2 * (1 + b) ^ 2 := by
        rw [show Real.rpow (1 + t * b) 2 = (1 + t * b) ^ 2 by
          exact Real.rpow_two _,
          show Real.rpow (1 + t * b) (2 - 1) = 1 + t * b by
            norm_num,
          show Real.rpow (1 - t) 2 = (1 - t) ^ 2 by
            exact Real.rpow_two _]
        ring
      have hV1 :
          2 * (1 + b) * Real.rpow (1 + b) (2 - 1) -
              Real.rpow (1 + b) 2 + Real.rpow (1 - 1) 2 =
            (1 + b) ^ 2 := by
        rw [show Real.rpow (1 + b) 2 = (1 + b) ^ 2 by
          exact Real.rpow_two _,
          show Real.rpow (1 + b) (2 - 1) = 1 + b by
            norm_num,
          show Real.rpow (1 - 1) 2 = (1 - 1) ^ 2 by
            exact Real.rpow_two _]
        ring
      simp only [mul_one]
      rw [hVt, hV1]
      exact
        two_point_log_ratio_quadratic_core t 1 b ht₀ ht₁ zero_lt_one hb₀
  · have hab : 0 < a + b := add_pos ha₀ hb₀
    have hr1 : 1 < r := lt_trans one_lt_two hr'
    have honepow : Real.rpow 1 r = 1 := by
      calc
        Real.rpow 1 r = Real.exp (Real.log 1 * r) :=
          Real.rpow_def_of_pos zero_lt_one r
        _ = 1 := by rw [Real.log_one, zero_mul, Real.exp_zero]
    have hMgt (s : ℝ) (hs₀ : 0 < s) (hs₁ : s ≤ 1) :
        1 < two_point_moment r s a b := by
      have hsa : s * a ≤ 1 := by
        have hmul := mul_le_mul_of_nonneg_left ha₁ hs₀.le
        nlinarith
      have hA :
          1 + r * (s * b) < (1 + s * b).rpow r :=
        one_add_mul_self_lt_rpow_one_add
          (by
            have : 0 ≤ s * b := mul_nonneg hs₀.le hb₀.le
            linarith)
          (ne_of_gt (mul_pos hs₀ hb₀)) hr1
      have hC :
          1 + r * (-s * a) ≤ (1 + (-s * a)).rpow r :=
        one_add_mul_self_le_rpow_one_add
          (by linarith : -1 ≤ -s * a) hr1.le
      have hweighted :
          a * (1 + r * (s * b)) +
              b * (1 + r * (-s * a)) <
            a * (1 + s * b).rpow r +
              b * (1 - s * a).rpow r := by
        have hA' := mul_lt_mul_of_pos_left hA ha₀
        have hC' := mul_le_mul_of_nonneg_left hC hb₀.le
        rw [show 1 + -s * a = 1 - s * a by ring] at hC'
        nlinarith
      rw [two_point_moment]
      apply (lt_div_iff₀ hab).2
      nlinarith
    have hMt : 1 < two_point_moment r t a b :=
      hMgt t ht₀ ht₁.le
    have hM1 : 1 < two_point_moment r 1 a b :=
      hMgt 1 zero_lt_one le_rfl
    have hMtM1 :
        two_point_moment r t a b < two_point_moment r 1 a b := by
      have hAseg :=
        (strictConvexOn_rpow hr1).2
          (show (1 : ℝ) ∈ Set.Ici 0 by simp)
          (show 1 + b ∈ Set.Ici (0 : ℝ) by
            simp only [Set.mem_Ici]
            linarith)
          (by linarith : (1 : ℝ) ≠ 1 + b)
          (sub_pos.mpr ht₁) ht₀ (by ring : (1 - t) + t = 1)
      have hCseg :=
        (strictConvexOn_rpow hr1).2
          (show (1 : ℝ) ∈ Set.Ici 0 by simp)
          (show 1 - a ∈ Set.Ici (0 : ℝ) by
            simpa only [Set.mem_Ici] using sub_nonneg.mpr ha₁)
          (by linarith : (1 : ℝ) ≠ 1 - a)
          (sub_pos.mpr ht₁) ht₀ (by ring : (1 - t) + t = 1)
      have hAseg' :
          (1 + t * b).rpow r <
            (1 - t) * 1 + t * (1 + b).rpow r := by
        have hAseg0 :
            ((1 - t) * 1 + t * (1 + b)).rpow r <
              (1 - t) * (1 : ℝ).rpow r +
                t * (1 + b).rpow r := hAseg
        rw [honepow] at hAseg0
        convert hAseg0 using 1 <;> ring
      have hCseg' :
          (1 - t * a).rpow r <
            (1 - t) * 1 + t * (1 - a).rpow r := by
        have hCseg0 :
            ((1 - t) * 1 + t * (1 - a)).rpow r <
              (1 - t) * (1 : ℝ).rpow r +
                t * (1 - a).rpow r := hCseg
        rw [honepow] at hCseg0
        convert hCseg0 using 1 <;> ring
      rw [two_point_moment, two_point_moment]
      norm_num only [one_mul]
      have hnumA := mul_lt_mul_of_pos_left hAseg' ha₀
      have hnumC := mul_lt_mul_of_pos_left hCseg' hb₀
      have hnum1 :
          a + b <
            a * (1 + b).rpow r + b * (1 - a).rpow r := by
        have h := hM1
        rw [two_point_moment] at h
        have h' := (lt_div_iff₀ hab).mp h
        norm_num only [one_mul] at h'
        exact h'
      apply (div_lt_div_iff_of_pos_right hab).2
      nlinarith [mul_pos (sub_pos.mpr ht₁) (sub_pos.mpr hnum1)]
    have hU1pos :
        0 <
          Real.rpow (1 + b) r - Real.rpow (1 - a) r -
            r * (a + b) * Real.rpow (1 - a) (r - 1) := by
      rcases lt_or_eq_of_le ha₁ with ha₁' | rfl
      · let x : ℝ := (a + b) / (1 - a)
        have hc : 0 < 1 - a := sub_pos.mpr ha₁'
        have hx : 0 < x := div_pos hab hc
        have hbase :
            1 + x = (1 + b) / (1 - a) := by
          dsimp only [x]
          field_simp [ne_of_gt hc]
          ring
        have hdiv :
            ((1 + b) / (1 - a)).rpow r =
              (1 + b).rpow r / (1 - a).rpow r := by
          have hA : 0 < 1 + b := by linarith
          calc
            ((1 + b) / (1 - a)).rpow r =
                Real.exp (Real.log ((1 + b) / (1 - a)) * r) :=
              Real.rpow_def_of_pos (div_pos hA hc) r
            _ = Real.exp ((Real.log (1 + b) - Real.log (1 - a)) * r) := by
              rw [Real.log_div (ne_of_gt hA) (ne_of_gt hc)]
            _ = Real.exp (Real.log (1 + b) * r) /
                Real.exp (Real.log (1 - a) * r) := by
              rw [sub_mul, Real.exp_sub]
            _ = (1 + b).rpow r / (1 - a).rpow r := by
              congr 1
              · exact (Real.rpow_def_of_pos hA r).symm
              · exact (Real.rpow_def_of_pos hc r).symm
        have hcsub :
            (1 - a).rpow (r - 1) =
              (1 - a).rpow r / (1 - a) :=
          Real.rpow_sub_one (ne_of_gt hc) r
        have hbern :
            0 < (1 + x).rpow r - 1 - r * x := by
          have h :
              1 + r * x < (1 + x).rpow r :=
            one_add_mul_self_lt_rpow_one_add
              (by linarith : -1 ≤ x) (ne_of_gt hx) hr1
          linarith
        have hcpow : 0 < (1 - a).rpow r :=
          Real.rpow_pos_of_pos hc r
        have hscaled := mul_pos hcpow hbern
        rw [hbase, hdiv] at hscaled
        dsimp only [x] at hscaled
        have hid :
            (1 - a).rpow r *
                ((1 + b).rpow r / (1 - a).rpow r - 1 -
                  r * ((a + b) / (1 - a))) =
              (1 + b).rpow r - (1 - a).rpow r -
                r * (a + b) * (1 - a).rpow (r - 1) := by
          rw [hcsub]
          field_simp [ne_of_gt hc, ne_of_gt hcpow]
        rw [hid] at hscaled
        exact hscaled
      · have hr0 : r ≠ 0 := by linarith
        have hrm0 : r - 1 ≠ 0 := by linarith
        have hz : Real.rpow 0 r = 0 := Real.zero_rpow hr0
        have hz' : Real.rpow 0 (r - 1) = 0 :=
          Real.zero_rpow hrm0
        rw [show 1 - (1 : ℝ) = 0 by ring, hz, hz']
        have hpos : 0 < (1 + b).rpow r :=
          Real.rpow_pos_of_pos (by linarith) r
        nlinarith
    constructor
    · have hcross :=
        two_point_u_q_cross r t a b hr' ht₀ ht₁ ha₀ ha₁ hb₀
      let Mt : ℝ := two_point_moment r t a b
      let M1 : ℝ := two_point_moment r 1 a b
      let qt : ℝ := Mt - 1
      let q1 : ℝ := M1 - 1
      let Ut : ℝ :=
        Real.rpow (1 + t * b) r - Real.rpow (1 - t * a) r -
          r * (t * (a + b)) * Real.rpow (1 - t * a) (r - 1)
      let U1 : ℝ :=
        Real.rpow (1 + b) r - Real.rpow (1 - a) r -
          r * (a + b) * Real.rpow (1 - a) (r - 1)
      have hqt : 0 < qt := by dsimp only [qt, Mt]; linarith
      have hq1 : 0 < q1 := by dsimp only [q1, M1]; linarith
      have hqtq1 : qt < q1 := by
        dsimp only [qt, q1, Mt, M1]
        linarith
      have hu₀ : 0 < qt / q1 := div_pos hqt hq1
      have hu₁ : qt / q1 < 1 := (div_lt_one hq1).mpr hqtq1
      have hent :=
        mul_log_one_add_contraction (qt / q1) q1 hu₀ hu₁ hq1
      have hcancel : 1 + qt / q1 * q1 = Mt := by
        have hden : M1 - 1 ≠ 0 := by
          dsimp only [q1] at hq1
          linarith
        dsimp only [qt, q1]
        field_simp [hden]
        ring
      have honeq : 1 + q1 = M1 := by
        dsimp only [q1]
        ring
      rw [hcancel, honeq] at hent
      have hF1pos : 0 < M1 * Real.log M1 := by
        exact mul_pos (lt_trans zero_lt_one (by simpa only [M1] using hM1))
          (Real.log_pos (by simpa only [M1] using hM1))
      have hratioU : U1 * (qt / q1) < Ut := by
        have hscaledcross : U1 * qt < Ut * q1 := by
          dsimp only [Ut, U1, qt, q1, Mt, M1] at hcross ⊢
          nlinarith
        calc
          U1 * (qt / q1) = (U1 * qt) / q1 := by ring
          _ < (Ut * q1) / q1 :=
            div_lt_div_of_pos_right hscaledcross hq1
          _ = Ut := by field_simp [ne_of_gt hq1]
      have hleft :
          U1 * (Mt * Real.log Mt) <
            U1 * ((qt / q1) * (M1 * Real.log M1)) :=
        mul_lt_mul_of_pos_left hent (by simpa only [U1] using hU1pos)
      have hright :
          U1 * ((qt / q1) * (M1 * Real.log M1)) <
            Ut * (M1 * Real.log M1) := by
        have := mul_lt_mul_of_pos_right hratioU hF1pos
        nlinarith
      dsimp only [Ut, U1, Mt, M1] at hleft hright ⊢
      nlinarith
    · intro ha
      subst a
      have hrne : r ≠ 0 := by linarith
      have hz : Real.rpow 0 r = 0 := Real.zero_rpow hrne
      simp only [mul_one, sub_self]
      rw [hz]
      simpa only [add_zero] using
        two_point_boundary_derivative_sign r t b hr' ht₀ ht₁ hb₀

@[blueprint "lem:two-point-log-ratio-comparison"
  (statement := /-- Let $r\geq2$, $0<t<1$, $\alpha>0$, $0<a\leq1$, and $0<b\leq\alpha$.  Then
  \[
    \frac{\log B_r(t;a,b)}{\log B_r(1;a,b)}
      \leq
    \frac{\log B_r(t;1,\alpha)}{\log B_r(1;1,\alpha)}.
  \]
  Equality holds if and only if $a=1$ and $b=\alpha$. -/)
  (proof := /-- Write $M_s=B_r(s;a,b)$, $A_s=1+sb$, $C_s=1-sa$, and
  $d_s=s(a+b)$.  Under the hypotheses, $A_s>C_s\geq0$ for
  $0<s\leq1$, and strict convexity of $u\mapsto u^r$ gives $M_s>1$.
  Thus every logarithm and denominator below is positive.

  Direct differentiation of \cref{def:two-point-moment} gives
  \[
  \begin{aligned}
    \partial_aM_s&=\frac{b}{(a+b)^2}U_s,&
    U_s&=A_s^r-C_s^r-rd_sC_s^{r-1},\\
    \partial_bM_s&=\frac{a}{(a+b)^2}V_s,&
    V_s&=rd_sA_s^{r-1}-A_s^r+C_s^r.
  \end{aligned}                                                    \tag{1}
  \]
  These identities follow by the quotient rule: after multiplication by
  $(a+b)^2$, the $a$-derivative is
  $bA_s^r-bC_s^r-rsb(a+b)C_s^{r-1}$, and the $b$-derivative is
  $rsa(a+b)A_s^{r-1}-aA_s^r+aC_s^r$.

  Put $F(a,b)=\log M_t/\log M_1$.  A second application of the quotient
  rule gives the required explicit derivative identities
  \[
  \begin{aligned}
   \partial_aF
    &=\frac{b\{U_tM_1\log M_1-U_1M_t\log M_t\}}
            {(a+b)^2M_tM_1(\log M_1)^2},\\
   \partial_bF
    &=\frac{a\{V_tM_1\log M_1-V_1M_t\log M_t\}}
            {(a+b)^2M_tM_1(\log M_1)^2}.                         \tag{2}
  \end{aligned}
  \]
  The first assertion of
  \cref{lem:two-point-log-ratio-derivative-sign} makes the first brace in
  (2) strictly positive throughout $0<a\leq1$ and $b>0$.  Hence
  $\partial_aF(a,b)>0$.  The mean value theorem on $[a,1]$ consequently
  gives $F(a,b)\leq F(1,b)$, and the inequality is strict when $a<1$.

  We use the second derivative identity only on the boundary $a=1$.
  The second assertion of
  \cref{lem:two-point-log-ratio-derivative-sign}, with its additional
  hypothesis $a=1$, makes the second brace in (2) strictly positive
  there.  Thus $\partial_bF(1,b)>0$ for every $b>0$.  The mean value
  theorem on $[b,\alpha]$ gives
  $F(1,b)\leq F(1,\alpha)$, with strict inequality when $b<\alpha$.
  Composing the two inequalities proves the comparison.  Equality in
  the composition holds precisely when neither step is strict, namely
  when $a=1$ and $b=\alpha$. -/)
  (title := /-- Sharp logarithmic comparison for centered two-point laws -/)
  (latexEnv := "lemma")]
lemma two_point_log_ratio_comparison
    (r t α a b : ℝ) (hr : 2 ≤ r) (ht₀ : 0 < t) (ht₁ : t < 1)
    (hα : 0 < α) (ha₀ : 0 < a) (ha₁ : a ≤ 1)
    (hb₀ : 0 < b) (hbα : b ≤ α) :
    Real.log (two_point_moment r t a b) /
          Real.log (two_point_moment r 1 a b) ≤
        Real.log (two_point_moment r t 1 α) /
          Real.log (two_point_moment r 1 1 α) ∧
      (Real.log (two_point_moment r t a b) /
            Real.log (two_point_moment r 1 a b) =
          Real.log (two_point_moment r t 1 α) /
            Real.log (two_point_moment r 1 1 α) ↔
        a = 1 ∧ b = α) := by
  have hr1 : 1 ≤ r := by linarith
  have hMgt (s x y : ℝ) (hs₀ : 0 < s) (hs₁ : s ≤ 1)
      (hx₀ : 0 < x) (hx₁ : x ≤ 1) (hy₀ : 0 < y) :
      1 < two_point_moment r s x y := by
    have hxy : 0 < x + y := add_pos hx₀ hy₀
    have hsx : s * x ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_left hx₁ hs₀.le
      nlinarith
    have hA :
        1 + r * (s * y) < Real.rpow (1 + s * y) r :=
      one_add_mul_self_lt_rpow_one_add
        (by
          have : 0 ≤ s * y := mul_nonneg hs₀.le hy₀.le
          linarith)
        (ne_of_gt (mul_pos hs₀ hy₀)) (by linarith)
    have hC :
        1 + r * (-s * x) ≤ Real.rpow (1 + (-s * x)) r :=
      one_add_mul_self_le_rpow_one_add
        (by linarith : -1 ≤ -s * x) (by linarith)
    have hweighted :
        x * (1 + r * (s * y)) +
            y * (1 + r * (-s * x)) <
          x * Real.rpow (1 + s * y) r +
            y * Real.rpow (1 - s * x) r := by
      have hA' := mul_lt_mul_of_pos_left hA hx₀
      have hC' := mul_le_mul_of_nonneg_left hC hy₀.le
      rw [show 1 + -s * x = 1 - s * x by ring] at hC'
      nlinarith
    rw [two_point_moment]
    apply (lt_div_iff₀ hxy).2
    nlinarith
  have hrpowDeriv (p z : ℝ) (hz : 0 < z) :
      HasDerivAt (fun w : ℝ ↦ Real.rpow w p)
        (p * Real.rpow z (p - 1)) z := by
    have hlog := Real.hasDerivAt_log (ne_of_gt hz)
    have hmul := hlog.const_mul p
    have hexp := (Real.hasDerivAt_exp (p * Real.log z)).comp z hmul
    have hev :
        (fun w : ℝ ↦ Real.rpow w p) =ᶠ[nhds z]
          (fun w : ℝ ↦ Real.exp (p * Real.log w)) := by
      filter_upwards [isOpen_Ioi.eventually_mem
        (show z ∈ Set.Ioi (0 : ℝ) by exact hz)] with w hw
      calc
        Real.rpow w p = Real.exp (Real.log w * p) :=
          Real.rpow_def_of_pos hw p
        _ = Real.exp (p * Real.log w) := by congr 1 <;> ring
    have hfinal := hexp.congr_of_eventuallyEq hev
    have hcoef :
        Real.exp (p * Real.log z) * (p * z⁻¹) =
          p * Real.rpow z (p - 1) := by
      have hexpeq : Real.exp (p * Real.log z) = Real.rpow z p := by
        symm
        calc
          Real.rpow z p = Real.exp (Real.log z * p) :=
            Real.rpow_def_of_pos hz p
          _ = Real.exp (p * Real.log z) := by congr 1 <;> ring
      have hsub : Real.rpow z (p - 1) = Real.rpow z p / z :=
        Real.rpow_sub_one (ne_of_gt hz) p
      rw [hexpeq, hsub]
      field_simp [ne_of_gt hz]
    rw [hcoef] at hfinal
    exact hfinal
  have hMderiv_a (s x y : ℝ) (hxy : x + y ≠ 0)
      (hCpos : 0 < 1 - s * x) :
      HasDerivAt (fun z : ℝ ↦ two_point_moment r s z y)
        (y * (Real.rpow (1 + s * y) r -
            Real.rpow (1 - s * x) r -
            r * (s * (x + y)) * Real.rpow (1 - s * x) (r - 1)) /
          (x + y) ^ 2) x := by
    have hCbase : HasDerivAt (fun z : ℝ ↦ 1 - s * z) ((0 : ℝ) - s) x := by
      have h :=
        (hasDerivAt_const x 1).sub ((hasDerivAt_id x).const_mul s)
      have h' : HasDerivAt (fun z : ℝ ↦ 1 - s * z) (0 - s * 1) x :=
        h.congr_of_eventuallyEq (f₁ := fun z : ℝ ↦ 1 - s * z) (by
          filter_upwards with z
          rfl)
      simpa only [mul_one] using h'
    have hCr :=
      (hrpowDeriv r (1 - s * x) hCpos).comp x hCbase
    have hnum :=
      ((hasDerivAt_id x).mul_const (Real.rpow (1 + s * y) r)).add
        (hCr.const_mul y)
    have hden : HasDerivAt (fun z : ℝ ↦ z + y) 1 x :=
      (hasDerivAt_id x).add_const y
    have hquot := hnum.div hden hxy
    have hquot' :=
      hquot.congr_of_eventuallyEq
        (f₁ := fun z : ℝ ↦ two_point_moment r s z y) (by
          filter_upwards with z
          rfl)
    apply hquot'.congr_deriv
    simp only [Pi.add_apply, Function.comp_apply, id_eq, one_mul, zero_add, zero_sub]
    field_simp [hxy]
    ring_nf
  have hMderiv_b (s x y : ℝ) (hxy : x + y ≠ 0)
      (hApos : 0 < 1 + s * y) :
      HasDerivAt (fun z : ℝ ↦ two_point_moment r s x z)
        (x * (r * (s * (x + y)) * Real.rpow (1 + s * y) (r - 1) -
            Real.rpow (1 + s * y) r + Real.rpow (1 - s * x) r) /
          (x + y) ^ 2) y := by
    have hAbase : HasDerivAt (fun z : ℝ ↦ 1 + s * z) ((0 : ℝ) + s) y := by
      have h :=
        (hasDerivAt_const y 1).add ((hasDerivAt_id y).const_mul s)
      have h' : HasDerivAt (fun z : ℝ ↦ 1 + s * z) (0 + s * 1) y :=
        h.congr_of_eventuallyEq (f₁ := fun z : ℝ ↦ 1 + s * z) (by
          filter_upwards with z
          rfl)
      simpa only [mul_one] using h'
    have hAr :=
      (hrpowDeriv r (1 + s * y) hApos).comp y hAbase
    have hnum :=
      (hAr.const_mul x).add
        ((hasDerivAt_id y).mul_const (Real.rpow (1 - s * x) r))
    have hden : HasDerivAt (fun z : ℝ ↦ x + z) 1 y :=
      (hasDerivAt_id y).const_add x
    have hquot := hnum.div hden hxy
    have hquot' :=
      hquot.congr_of_eventuallyEq
        (f₁ := fun z : ℝ ↦ two_point_moment r s x z) (by
          filter_upwards with z
          rfl)
    apply hquot'.congr_deriv
    simp only [Pi.add_apply, Function.comp_apply, id_eq, one_mul, zero_add, zero_sub]
    field_simp [hxy]
    ring_nf
  have hMcont_a (s x y : ℝ) (hxy : x + y ≠ 0) :
      ContinuousAt (fun z : ℝ ↦ two_point_moment r s z y) x := by
    have hCbase : ContinuousAt (fun z : ℝ ↦ 1 - s * z) x := by fun_prop
    have hCr := hCbase.rpow_const (Or.inr (by linarith : 0 ≤ r))
    have hfirst :
        ContinuousAt (fun z : ℝ ↦ z * Real.rpow (1 + s * y) r) x :=
      continuousAt_id.mul continuousAt_const
    have hsecond :
        ContinuousAt (fun z : ℝ ↦ y * Real.rpow (1 - s * z) r) x :=
      continuousAt_const.mul hCr
    have hnum := hfirst.add hsecond
    have hden : ContinuousAt (fun z : ℝ ↦ z + y) x := by fun_prop
    have hquot := hnum.div hden hxy
    exact hquot.congr_of_eventuallyEq
      (g := fun z : ℝ ↦ two_point_moment r s z y) (by
        filter_upwards with z
        rfl)
  have hMcont_b (s x y : ℝ) (hxy : x + y ≠ 0) :
      ContinuousAt (fun z : ℝ ↦ two_point_moment r s x z) y := by
    have hAbase : ContinuousAt (fun z : ℝ ↦ 1 + s * z) y := by fun_prop
    have hAr := hAbase.rpow_const (Or.inr (by linarith : 0 ≤ r))
    have hfirst :
        ContinuousAt (fun z : ℝ ↦ x * Real.rpow (1 + s * z) r) y :=
      continuousAt_const.mul hAr
    have hsecond :
        ContinuousAt (fun z : ℝ ↦ z * Real.rpow (1 - s * x) r) y :=
      continuousAt_id.mul continuousAt_const
    have hnum := hfirst.add hsecond
    have hden : ContinuousAt (fun z : ℝ ↦ x + z) y := by fun_prop
    have hquot := hnum.div hden hxy
    exact hquot.congr_of_eventuallyEq
      (g := fun z : ℝ ↦ two_point_moment r s x z) (by
        filter_upwards with z
        rfl)
  let F : ℝ → ℝ := fun x ↦
    Real.log (two_point_moment r t x b) /
      Real.log (two_point_moment r 1 x b)
  have hFderiv (x : ℝ) (hx₀ : 0 < x) (hx₁ : x < 1) :
      HasDerivAt F
        (b * ((Real.rpow (1 + t * b) r - Real.rpow (1 - t * x) r -
              r * (t * (x + b)) * Real.rpow (1 - t * x) (r - 1)) *
            two_point_moment r 1 x b * Real.log (two_point_moment r 1 x b) -
          (Real.rpow (1 + b) r - Real.rpow (1 - x) r -
              r * (x + b) * Real.rpow (1 - x) (r - 1)) *
            two_point_moment r t x b * Real.log (two_point_moment r t x b)) /
          ((x + b) ^ 2 * two_point_moment r t x b *
            two_point_moment r 1 x b *
            Real.log (two_point_moment r 1 x b) ^ 2)) x := by
    have hxy : x + b ≠ 0 := ne_of_gt (add_pos hx₀ hb₀)
    have hMtgt := hMgt t x b ht₀ ht₁.le hx₀ hx₁.le hb₀
    have hM1gt := hMgt 1 x b zero_lt_one le_rfl hx₀ hx₁.le hb₀
    have hMt := hMderiv_a t x b hxy (by nlinarith)
    have hM1 := hMderiv_a 1 x b hxy (by nlinarith)
    have hlogt :=
      (Real.hasDerivAt_log (ne_of_gt (lt_trans zero_lt_one hMtgt))).comp x hMt
    have hlog1 :=
      (Real.hasDerivAt_log (ne_of_gt (lt_trans zero_lt_one hM1gt))).comp x hM1
    have hquot := hlogt.div hlog1 (ne_of_gt (Real.log_pos hM1gt))
    change HasDerivAt F _ x at hquot
    convert hquot using 1
    simp only [Function.comp_apply]
    field_simp [ne_of_gt (lt_trans zero_lt_one hMtgt),
      ne_of_gt (lt_trans zero_lt_one hM1gt),
      ne_of_gt (Real.log_pos hM1gt)]
  have hFderiv_pos (x : ℝ) (hx₀ : 0 < x) (hx₁ : x ≤ 1) :
      0 <
        b * ((Real.rpow (1 + t * b) r - Real.rpow (1 - t * x) r -
              r * (t * (x + b)) * Real.rpow (1 - t * x) (r - 1)) *
            two_point_moment r 1 x b * Real.log (two_point_moment r 1 x b) -
          (Real.rpow (1 + b) r - Real.rpow (1 - x) r -
              r * (x + b) * Real.rpow (1 - x) (r - 1)) *
            two_point_moment r t x b * Real.log (two_point_moment r t x b)) /
          ((x + b) ^ 2 * two_point_moment r t x b *
            two_point_moment r 1 x b *
            Real.log (two_point_moment r 1 x b) ^ 2) := by
    have hsign :=
      (two_point_log_ratio_derivative_sign r t x b hr ht₀ ht₁ hx₀ hx₁ hb₀).1
    have hMtgt := hMgt t x b ht₀ ht₁.le hx₀ hx₁ hb₀
    have hM1gt := hMgt 1 x b zero_lt_one le_rfl hx₀ hx₁ hb₀
    have hxypos : 0 < (x + b) ^ 2 := sq_pos_of_pos (add_pos hx₀ hb₀)
    have hMtpos : 0 < two_point_moment r t x b := lt_trans zero_lt_one hMtgt
    have hM1pos : 0 < two_point_moment r 1 x b := lt_trans zero_lt_one hM1gt
    have hlogpos : 0 < Real.log (two_point_moment r 1 x b) :=
      Real.log_pos hM1gt
    exact div_pos (mul_pos hb₀ hsign)
      (mul_pos (mul_pos (mul_pos hxypos hMtpos) hM1pos) (sq_pos_of_pos hlogpos))
  have hFcont (x : ℝ) (hx₀ : 0 < x) (hx₁ : x ≤ 1) :
      ContinuousAt F x := by
    have hxy : x + b ≠ 0 := ne_of_gt (add_pos hx₀ hb₀)
    have hMtgt := hMgt t x b ht₀ ht₁.le hx₀ hx₁ hb₀
    have hM1gt := hMgt 1 x b zero_lt_one le_rfl hx₀ hx₁ hb₀
    have hlogt :=
      (hMcont_a t x b hxy).log (ne_of_gt (lt_trans zero_lt_one hMtgt))
    have hlog1 :=
      (hMcont_a 1 x b hxy).log (ne_of_gt (lt_trans zero_lt_one hM1gt))
    have hquot := hlogt.div hlog1 (ne_of_gt (Real.log_pos hM1gt))
    exact hquot.congr_of_eventuallyEq (g := F) (by
      filter_upwards with z
      rfl)
  have hFmono : StrictMonoOn F (Set.Icc a 1) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc a 1)
    · intro x hx
      exact (hFcont x (lt_of_lt_of_le ha₀ hx.1) hx.2).continuousWithinAt
    · intro x hx
      have hx' : x ∈ Set.Ioo a 1 := by
        simpa only [interior_Icc] using hx
      exact (hFderiv x (lt_trans ha₀ hx'.1) hx'.2).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Set.Icc a 1 := interior_subset hx
      exact hFderiv_pos x (lt_of_lt_of_le ha₀ hx'.1) hx'.2
  have ha_mem : a ∈ Set.Icc a 1 := ⟨le_rfl, ha₁⟩
  have hone_mem : (1 : ℝ) ∈ Set.Icc a 1 := ⟨ha₁, le_rfl⟩
  have hFa_le : F a ≤ F 1 := hFmono.monotoneOn ha_mem hone_mem ha₁
  have hFa_eq : F a = F 1 ↔ a = 1 := by
    constructor
    · intro heq
      by_contra hne
      have halt : a < 1 := lt_of_le_of_ne ha₁ hne
      exact (ne_of_lt (hFmono ha_mem hone_mem halt)) heq
    · intro heq
      subst a
      rfl
  let G : ℝ → ℝ := fun y ↦
    Real.log (two_point_moment r t 1 y) /
      Real.log (two_point_moment r 1 1 y)
  have hGderiv (y : ℝ) (hy₀ : 0 < y) :
      HasDerivAt G
        (((r * (t * (1 + y)) * Real.rpow (1 + t * y) (r - 1) -
              Real.rpow (1 + t * y) r + Real.rpow (1 - t) r) *
            two_point_moment r 1 1 y * Real.log (two_point_moment r 1 1 y) -
          (r * (1 + y) * Real.rpow (1 + y) (r - 1) -
              Real.rpow (1 + y) r + Real.rpow (1 - 1) r) *
            two_point_moment r t 1 y * Real.log (two_point_moment r t 1 y)) /
          ((1 + y) ^ 2 * two_point_moment r t 1 y *
            two_point_moment r 1 1 y *
            Real.log (two_point_moment r 1 1 y) ^ 2)) y := by
    have hxy : 1 + y ≠ 0 := ne_of_gt (add_pos zero_lt_one hy₀)
    have hMtgt := hMgt t 1 y ht₀ ht₁.le zero_lt_one le_rfl hy₀
    have hM1gt := hMgt 1 1 y zero_lt_one le_rfl zero_lt_one le_rfl hy₀
    have hMt := hMderiv_b t 1 y hxy (by positivity)
    have hM1 := hMderiv_b 1 1 y hxy (by positivity)
    have hlogt :=
      (Real.hasDerivAt_log (ne_of_gt (lt_trans zero_lt_one hMtgt))).comp y hMt
    have hlog1 :=
      (Real.hasDerivAt_log (ne_of_gt (lt_trans zero_lt_one hM1gt))).comp y hM1
    have hquot := hlogt.div hlog1 (ne_of_gt (Real.log_pos hM1gt))
    change HasDerivAt G _ y at hquot
    convert hquot using 1
    simp only [Function.comp_apply]
    field_simp [ne_of_gt (lt_trans zero_lt_one hMtgt),
      ne_of_gt (lt_trans zero_lt_one hM1gt),
      ne_of_gt (Real.log_pos hM1gt)]
  have hGderiv_pos (y : ℝ) (hy₀ : 0 < y) :
      0 <
        ((r * (t * (1 + y)) * Real.rpow (1 + t * y) (r - 1) -
              Real.rpow (1 + t * y) r + Real.rpow (1 - t) r) *
            two_point_moment r 1 1 y * Real.log (two_point_moment r 1 1 y) -
          (r * (1 + y) * Real.rpow (1 + y) (r - 1) -
              Real.rpow (1 + y) r + Real.rpow (1 - 1) r) *
            two_point_moment r t 1 y * Real.log (two_point_moment r t 1 y)) /
          ((1 + y) ^ 2 * two_point_moment r t 1 y *
            two_point_moment r 1 1 y *
            Real.log (two_point_moment r 1 1 y) ^ 2) := by
    have hsign :=
      (two_point_log_ratio_derivative_sign r t 1 y hr ht₀ ht₁
        zero_lt_one le_rfl hy₀).2 rfl
    have hMtgt := hMgt t 1 y ht₀ ht₁.le zero_lt_one le_rfl hy₀
    have hM1gt := hMgt 1 1 y zero_lt_one le_rfl zero_lt_one le_rfl hy₀
    have hxypos : 0 < (1 + y) ^ 2 := sq_pos_of_pos (add_pos zero_lt_one hy₀)
    have hMtpos : 0 < two_point_moment r t 1 y := lt_trans zero_lt_one hMtgt
    have hM1pos : 0 < two_point_moment r 1 1 y := lt_trans zero_lt_one hM1gt
    have hlogpos : 0 < Real.log (two_point_moment r 1 1 y) :=
      Real.log_pos hM1gt
    exact div_pos (by simpa only [mul_one] using hsign)
      (mul_pos (mul_pos (mul_pos hxypos hMtpos) hM1pos) (sq_pos_of_pos hlogpos))
  have hGcont (y : ℝ) (hy₀ : 0 < y) :
      ContinuousAt G y := by
    have hxy : 1 + y ≠ 0 := ne_of_gt (add_pos zero_lt_one hy₀)
    have hMtgt := hMgt t 1 y ht₀ ht₁.le zero_lt_one le_rfl hy₀
    have hM1gt := hMgt 1 1 y zero_lt_one le_rfl zero_lt_one le_rfl hy₀
    have hlogt :=
      (hMcont_b t 1 y hxy).log (ne_of_gt (lt_trans zero_lt_one hMtgt))
    have hlog1 :=
      (hMcont_b 1 1 y hxy).log (ne_of_gt (lt_trans zero_lt_one hM1gt))
    have hquot := hlogt.div hlog1 (ne_of_gt (Real.log_pos hM1gt))
    exact hquot.congr_of_eventuallyEq (g := G) (by
      filter_upwards with z
      rfl)
  have hGmono : StrictMonoOn G (Set.Icc b α) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc b α)
    · intro y hy
      exact (hGcont y (lt_of_lt_of_le hb₀ hy.1)).continuousWithinAt
    · intro y hy
      have hy' : y ∈ Set.Icc b α := interior_subset hy
      exact (hGderiv y (lt_of_lt_of_le hb₀ hy'.1)).hasDerivWithinAt
    · intro y hy
      have hy' : y ∈ Set.Icc b α := interior_subset hy
      exact hGderiv_pos y (lt_of_lt_of_le hb₀ hy'.1)
  have hb_mem : b ∈ Set.Icc b α := ⟨le_rfl, hbα⟩
  have hα_mem : α ∈ Set.Icc b α := ⟨hbα, le_rfl⟩
  have hGb_le : G b ≤ G α := hGmono.monotoneOn hb_mem hα_mem hbα
  have hGb_eq : G b = G α ↔ b = α := by
    constructor
    · intro heq
      by_contra hne
      have hblt : b < α := lt_of_le_of_ne hbα hne
      exact (ne_of_lt (hGmono hb_mem hα_mem hblt)) heq
    · intro heq
      subst b
      rfl
  have hmid : F 1 = G b := by rfl
  have hleft : F a =
      Real.log (two_point_moment r t a b) /
        Real.log (two_point_moment r 1 a b) := by rfl
  have hright : G α =
      Real.log (two_point_moment r t 1 α) /
        Real.log (two_point_moment r 1 1 α) := by rfl
  rw [← hleft, ← hright]
  constructor
  · calc
      F a ≤ F 1 := hFa_le
      _ = G b := hmid
      _ ≤ G α := hGb_le
  · constructor
    · intro heq
      have hFa_eq' : F a = F 1 := by
        have : F 1 ≤ G α := by simpa only [hmid] using hGb_le
        linarith
      have hGb_eq' : G b = G α := by
        rw [← hmid]
        linarith
      exact ⟨hFa_eq.mp hFa_eq', hGb_eq.mp hGb_eq'⟩
    · rintro ⟨rfl, rfl⟩
      rfl

@[blueprint "lem:centered-finite-law-two-point-decomposition"
  (statement := /-- Let $\mu$ be a full-support probability mass function on a finite space $\Omega$, and let $X:\Omega\to\mathbb R$ be nonzero with $\mathbb E_\mu X=0$.  Put
  \[
    z=\sum_{x\in\Omega}\mu(x)\mathbf 1_{\{X(x)=0\}}.
  \]
  There are nonnegative weights $w_{ij}$, positive exactly when
  $X(i)<0<X(j)$, such that
  \[
    \sum_{i,j}w_{ij}+z=1
  \]
  and, for every function $\varphi:\mathbb R\to\mathbb R$,
  \[
    \sum_x\mu(x)\varphi(X(x))
      =z\varphi(0)+
        \sum_{i,j}w_{ij}
        \frac{-X(i)\varphi(X(j))+X(j)\varphi(X(i))}
             {X(j)-X(i)}.
  \]
  Thus the law of $X$ is the convex combination of the zero law and
  centered two-point laws supported on pairs of its negative and positive
  values. -/)
  (proof := /-- Since $X$ is nonzero, has mean zero, and every atom has
  positive $\mu$-mass, $X$ assumes both a negative and a positive value.
  Define
  \[
    m=\sum_{X(i)<0}\mu(i)(-X(i))
      =\sum_{X(j)>0}\mu(j)X(j)>0,
  \]
  where the equality follows from \cref{def:one-coordinate-mean}.  For
  $X(i)<0<X(j)$ set
  \[
    w_{ij}=\frac{\mu(i)\mu(j)(X(j)-X(i))}{m},
  \]
  and set $w_{ij}=0$ for all other pairs.  Full support, as specified in
  \cref{def:full-support-pmf}, gives the asserted nonnegativity and strict
  positivity criterion.

  For fixed negative $i$, the contribution of the atom $X(i)$ from the
  two-point laws is
  \[
    \sum_{X(j)>0}w_{ij}\frac{X(j)}{X(j)-X(i)}
      =\mu(i)\frac{\sum_{X(j)>0}\mu(j)X(j)}{m}=\mu(i).
  \]
  Similarly, for fixed positive $j$, its total coefficient is
  \[
    \sum_{X(i)<0}w_{ij}\frac{-X(i)}{X(j)-X(i)}
      =\mu(j).
  \]
  The zero atoms have total mass $z$.  These three coefficient identities
  prove the formula for every $\varphi$.  Taking $\varphi=1$ proves
  $\sum_{i,j}w_{ij}+z=1$. -/)
  (title := /-- Decomposition of a centered finite law into two-point laws -/)
  (latexEnv := "lemma")]
lemma centered_finite_law_two_point_decomposition {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω) (X : Ω → ℝ) (hμ : full_support_pmf μ)
    (hX : one_coordinate_mean μ X = 0) (hXne : X ≠ (fun _ ↦ 0)) :
    ∃ w : Ω → Ω → ℝ,
      (∀ i j, 0 ≤ w i j) ∧
      (∀ i j, 0 < w i j ↔ X i < 0 ∧ 0 < X j) ∧
      (∑ i, ∑ j, w i j) +
          ∑ x, (μ x).toReal * (if X x = 0 then 1 else 0) = 1 ∧
      ∀ φ : ℝ → ℝ,
        ∑ x, (μ x).toReal * φ (X x) =
          (∑ x, (μ x).toReal * (if X x = 0 then 1 else 0)) * φ 0 +
            ∑ i, ∑ j, w i j *
              ((-X i) * φ (X j) + X j * φ (X i)) / (X j - X i) := by
  classical
  let p : Ω → ℝ := fun x ↦ (μ x).toReal
  have hp (x : Ω) : 0 < p x := by
    exact ENNReal.toReal_pos (hμ x)
      (ne_of_lt ((PMF.coe_le_one μ x).trans_lt ENNReal.one_lt_top))
  have hmean : ∑ x, p x * X x = 0 := by
    simpa [p, one_coordinate_mean] using hX
  have hXpoint : ∃ x, X x ≠ 0 := by
    by_contra h
    apply hXne
    funext x
    by_contra hx
    exact h ⟨x, hx⟩
  have hterm : ∃ x ∈ Finset.univ, p x * X x ≠ 0 := by
    obtain ⟨x, hx⟩ := hXpoint
    exact ⟨x, Finset.mem_univ x, mul_ne_zero (ne_of_gt (hp x)) hx⟩
  obtain ⟨ipos, _, hipos⟩ :=
    Finset.exists_pos_of_sum_zero_of_exists_nonzero
      (s := Finset.univ) (fun x ↦ p x * X x) hmean hterm
  have hXpos : 0 < X ipos := by
    nlinarith [hp ipos]
  let n : ℝ := ∑ i, if X i < 0 then p i * (-X i) else 0
  let m : ℝ := ∑ j, if 0 < X j then p j * X j else 0
  have hmpos : 0 < m := by
    dsimp [m]
    refine Finset.sum_pos' ?_ ⟨ipos, Finset.mem_univ ipos, ?_⟩
    · intro j hj
      by_cases hXj : 0 < X j
      · simpa [hXj] using (mul_pos (hp j) hXj).le
      · simp [hXj]
    · simpa [hXpos] using mul_pos (hp ipos) hXpos
  have hsplit : ∑ x, p x * X x = -n + m := by
    dsimp [n, m]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hXxneg : X x < 0
    · have hXxpos : ¬ 0 < X x := not_lt_of_ge hXxneg.le
      simp [hXxneg, hXxpos]
    · by_cases hXxpos : 0 < X x
      · simp [hXxneg, hXxpos]
      · have hXxzero : X x = 0 :=
          le_antisymm (le_of_not_gt hXxpos) (le_of_not_gt hXxneg)
        simp [hXxneg, hXxpos, hXxzero]
  have hbalance : n = m := by
    linarith [hmean, hsplit]
  let w : Ω → Ω → ℝ := fun i j ↦
    if X i < 0 ∧ 0 < X j then
      p i * p j * (X j - X i) / m
    else 0
  have hw_nonneg : ∀ i j, 0 ≤ w i j := by
    intro i j
    by_cases hij : X i < 0 ∧ 0 < X j
    · rw [show w i j = p i * p j * (X j - X i) / m by simp [w, hij]]
      exact div_nonneg
        (mul_nonneg (mul_nonneg (hp i).le (hp j).le)
          (sub_nonneg.mpr (le_trans hij.1.le hij.2.le)))
        hmpos.le
    · simp [w, hij]
  have hw_pos : ∀ i j, 0 < w i j ↔ X i < 0 ∧ 0 < X j := by
    intro i j
    constructor
    · intro hwij
      by_contra hij
      simp [w, hij] at hwij
    · intro hij
      rw [show w i j = p i * p j * (X j - X i) / m by simp [w, hij]]
      exact div_pos
        (mul_pos (mul_pos (hp i) (hp j))
          (sub_pos.mpr (lt_trans hij.1 hij.2)))
        hmpos
  have hprod (a b : Ω → ℝ) :
      (∑ i, ∑ j, a i * b j) = (∑ i, a i) * ∑ j, b j := by
    symm
    simpa using
      (Finset.sum_mul_sum Finset.univ Finset.univ a b)
  have hprod_div (a b : Ω → ℝ) :
      (∑ i, ∑ j, a i * b j / m) =
        ((∑ i, a i) * ∑ j, b j) / m := by
    rw [← hprod]
    simp only [Finset.sum_div]
  have hpair (φ : ℝ → ℝ) :
      (∑ i, ∑ j, w i j *
          ((-X i) * φ (X j) + X j * φ (X i)) / (X j - X i)) =
        (∑ j, if 0 < X j then p j * φ (X j) else 0) +
          ∑ i, if X i < 0 then p i * φ (X i) else 0 := by
    have hcancel (i j : Ω) :
        w i j * ((-X i) * φ (X j) + X j * φ (X i)) / (X j - X i) =
          if X i < 0 ∧ 0 < X j then
            ((p i * (-X i)) * (p j * φ (X j)) +
              (p i * φ (X i)) * (p j * X j)) / m
          else 0 := by
      by_cases hij : X i < 0 ∧ 0 < X j
      · have hden : X j - X i ≠ 0 :=
          ne_of_gt (sub_pos.mpr (lt_trans hij.1 hij.2))
        simp only [w, if_pos hij]
        field_simp [hden, ne_of_gt hmpos]
      · simp [w, hij]
    calc
      (∑ i, ∑ j, w i j *
          ((-X i) * φ (X j) + X j * φ (X i)) / (X j - X i)) =
          ∑ i, ∑ j,
            if X i < 0 ∧ 0 < X j then
              ((p i * (-X i)) * (p j * φ (X j)) +
                (p i * φ (X i)) * (p j * X j)) / m
            else 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              exact hcancel i j
      _ = ∑ i, ∑ j,
            (((if X i < 0 then p i * (-X i) else 0) *
                (if 0 < X j then p j * φ (X j) else 0)) +
              ((if X i < 0 then p i * φ (X i) else 0) *
                (if 0 < X j then p j * X j else 0))) / m := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              by_cases hXi : X i < 0 <;> by_cases hXj : 0 < X j <;>
                simp [hXi, hXj]
      _ = (((∑ i, if X i < 0 then p i * (-X i) else 0) *
              ∑ j, if 0 < X j then p j * φ (X j) else 0) +
            ((∑ i, if X i < 0 then p i * φ (X i) else 0) *
              ∑ j, if 0 < X j then p j * X j else 0)) / m := by
              simp only [add_div, Finset.sum_add_distrib, Finset.sum_div]
              rw [hprod_div, hprod_div]
      _ = (∑ j, if 0 < X j then p j * φ (X j) else 0) +
            ∑ i, if X i < 0 then p i * φ (X i) else 0 := by
              change (n * (∑ j, if 0 < X j then p j * φ (X j) else 0) +
                  (∑ i, if X i < 0 then p i * φ (X i) else 0) * m) / m =
                (∑ j, if 0 < X j then p j * φ (X j) else 0) +
                  ∑ i, if X i < 0 then p i * φ (X i) else 0
              rw [hbalance]
              field_simp [ne_of_gt hmpos]
  have hdecomp (φ : ℝ → ℝ) :
      ∑ x, p x * φ (X x) =
        (∑ x, p x * (if X x = 0 then 1 else 0)) * φ 0 +
          ∑ i, ∑ j, w i j *
            ((-X i) * φ (X j) + X j * φ (X i)) / (X j - X i) := by
    have hclass :
        ∑ x, p x * φ (X x) =
          (∑ x, p x * (if X x = 0 then 1 else 0)) * φ 0 +
            (∑ j, if 0 < X j then p j * φ (X j) else 0) +
              ∑ i, if X i < 0 then p i * φ (X i) else 0 := by
      rw [Finset.sum_mul]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      rcases lt_trichotomy (X x) 0 with hXxneg | hXxzero | hXxpos
      · have hXxpos' : ¬ 0 < X x := not_lt_of_ge hXxneg.le
        simp [hXxneg, hXxpos', ne_of_lt hXxneg]
      · simp [hXxzero]
      · have hXxneg' : ¬ X x < 0 := not_lt_of_ge hXxpos.le
        simp [hXxpos, hXxneg', ne_of_gt hXxpos]
    calc
      ∑ x, p x * φ (X x) =
          (∑ x, p x * (if X x = 0 then 1 else 0)) * φ 0 +
            (∑ j, if 0 < X j then p j * φ (X j) else 0) +
              ∑ i, if X i < 0 then p i * φ (X i) else 0 := hclass
      _ = (∑ x, p x * (if X x = 0 then 1 else 0)) * φ 0 +
            ∑ i, ∑ j, w i j *
              ((-X i) * φ (X j) + X j * φ (X i)) / (X j - X i) := by
              rw [hpair]
              ring
  have hnotop (x : Ω) : μ x ≠ ⊤ := by
    exact ne_of_lt ((PMF.coe_le_one μ x).trans_lt ENNReal.one_lt_top)
  have hmassENN : ∑ x, μ x = 1 := by
    simpa only [tsum_fintype] using PMF.tsum_coe μ
  have hmass : ∑ x, p x = 1 := by
    calc
      ∑ x, p x = ENNReal.toReal (∑ x, μ x) := by
        simpa [p] using
          (ENNReal.toReal_sum (s := Finset.univ)
            (f := fun x ↦ μ x) (fun x hx ↦ hnotop x)).symm
      _ = 1 := by rw [hmassENN]; simp
  have hpair_one :
      (∑ i, ∑ j, w i j * ((-X i) + X j) / (X j - X i)) =
        ∑ i, ∑ j, w i j := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : X i < 0 ∧ 0 < X j
    · have hden : X j - X i ≠ 0 :=
        ne_of_gt (sub_pos.mpr (lt_trans hij.1 hij.2))
      simp only [w, if_pos hij]
      field_simp [hden, ne_of_gt hmpos]
      ring
    · simp [w, hij]
  have hnorm :
      (∑ i, ∑ j, w i j) +
          ∑ x, p x * (if X x = 0 then 1 else 0) = 1 := by
    have hone := hdecomp (fun _ ↦ 1)
    simp only [mul_one] at hone
    rw [hpair_one] at hone
    linarith [hmass]
  refine ⟨w, hw_nonneg, hw_pos, ?_, ?_⟩
  · simpa [p] using hnorm
  · intro φ
    simpa [p] using hdecomp φ

@[blueprint "lem:bounded-mean-zero-real-rpow-jensen"
  (statement := /-- Let $I$ be finite, let $0<\lambda<1$, and let
  $(w_i)_{i\in I}$ be nonnegative weights with sum $1$.  For every
  nonnegative family $(u_i)_{i\in I}$,
  \[
    \sum_i w_i u_i^\lambda
      \leq \left(\sum_i w_i u_i\right)^\lambda.
  \]
  Equality holds if and only if all $u_i$ carrying nonzero weight are
  equal. -/)
  (proof := /-- Apply the strict concavity of $u\mapsto u^\lambda$ on
  $[0,\infty)$ to the given probability weights.  Jensen's inequality
  gives the asserted bound, and its strict equality criterion says exactly
  that the points with nonzero weight coincide. -/)
  (title := /-- Weighted Jensen inequality for a fractional real power -/)
  (latexEnv := "lemma")]
lemma bounded_mean_zero_real_rpow_jensen {ι : Type*} [Fintype ι]
    (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1)
    (w u : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hu : ∀ i, 0 ≤ u i) :
    (∑ i, w i * Real.rpow (u i) lam) ≤
        Real.rpow (∑ i, w i * u i) lam ∧
      ((∑ i, w i * Real.rpow (u i) lam) =
          Real.rpow (∑ i, w i * u i) lam ↔
        ∀ i j, w i ≠ 0 → w j ≠ 0 → u i = u j) := by
  classical
  have hlamne : lam ≠ 0 := ne_of_gt hlam₀
  let q : ℝ := lam⁻¹
  have hqpos : 0 < q := by
    exact inv_pos.mpr hlam₀
  have hq : 1 < q := by
    have hprod : lam * q = 1 := by
      dsimp only [q]
      exact mul_inv_cancel₀ hlamne
    nlinarith [mul_pos (sub_pos.mpr hlam₁) hqpos]
  let v : ι → ℝ := fun i ↦ Real.rpow (u i) lam
  let A : ℝ := ∑ i, w i * v i
  let B : ℝ := ∑ i, w i * u i
  have hv (i : ι) : 0 ≤ v i := Real.rpow_nonneg (hu i) lam
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact Finset.sum_nonneg fun i hi ↦ mul_nonneg (hw i) (hv i)
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact Finset.sum_nonneg fun i hi ↦ mul_nonneg (hw i) (hu i)
  have hvq (i : ι) : Real.rpow (v i) q = u i := by
    dsimp only [v, q]
    exact Real.rpow_rpow_inv (hu i) hlamne
  have hAq : Real.rpow (Real.rpow A q) lam = A := by
    dsimp only [q]
    exact Real.rpow_inv_rpow hA hlamne
  have hBlamq : Real.rpow (Real.rpow B lam) q = B := by
    dsimp only [q]
    exact Real.rpow_rpow_inv hB hlamne
  have hf : StrictConvexOn ℝ (Set.Ici 0) (fun x : ℝ ↦ Real.rpow x q) :=
    strictConvexOn_rpow hq
  have hweights : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ w i := by
    intro i hi
    exact hw i
  have hpoints : ∀ i ∈ (Finset.univ : Finset ι), v i ∈ Set.Ici (0 : ℝ) := by
    intro i hi
    exact hv i
  have hsum' : ∑ i ∈ (Finset.univ : Finset ι), w i = 1 := by
    simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using hsum
  have hjensen := hf.convexOn.map_sum_le hweights hsum' hpoints
  have hjensen' : Real.rpow A q ≤ B := by
    calc
      Real.rpow A q ≤ ∑ i, w i * Real.rpow (v i) q := by
        simpa only [A, smul_eq_mul, Finset.sum_filter, Finset.mem_univ,
          ↓reduceIte] using hjensen
      _ = B := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hvq]
  have heq_criterion := hf.map_sum_eq_iff_of_nonneg hweights hsum' hpoints
  constructor
  · have hp := Real.rpow_le_rpow (Real.rpow_nonneg hA q) hjensen' hlam₀.le
    change Real.rpow (Real.rpow A q) lam ≤ Real.rpow B lam at hp
    rw [hAq] at hp
    change A ≤ Real.rpow B lam
    exact hp
  · constructor
    · intro heq
      have hp := congrArg (fun z : ℝ ↦ Real.rpow z q) heq
      have hjEq : Real.rpow A q = B := by
        rw [hBlamq] at hp
        exact hp
      have hall := heq_criterion.mp (by
        calc
          Real.rpow (∑ i ∈ (Finset.univ : Finset ι), w i • v i) q =
              Real.rpow A q := by
            simp only [A, smul_eq_mul, Finset.sum_filter, Finset.mem_univ,
              ↓reduceIte]
          _ = B := hjEq
          _ = ∑ i ∈ (Finset.univ : Finset ι), w i • Real.rpow (v i) q := by
            simp only [B, smul_eq_mul, Finset.sum_filter, Finset.mem_univ,
              ↓reduceIte]
            apply Finset.sum_congr rfl
            intro i hi
            rw [hvq])
      intro i j hi hj
      have hvij := hall (Finset.mem_univ i) hi (Finset.mem_univ j) hj
      have hpij := congrArg (fun z : ℝ ↦ Real.rpow z q) hvij
      simpa only [hvq] using hpij
    · intro hall
      have hall' :
          ∀ ⦃i⦄, i ∈ (Finset.univ : Finset ι) → w i ≠ 0 →
            ∀ ⦃j⦄, j ∈ (Finset.univ : Finset ι) → w j ≠ 0 → v i = v j := by
        intro i hi hwi j hj hwj
        exact congrArg (fun z : ℝ ↦ Real.rpow z lam) (hall i j hwi hwj)
      have hjEqRaw := heq_criterion.mpr hall'
      have hjEq : Real.rpow A q = B := by
        calc
          Real.rpow A q =
              Real.rpow (∑ i ∈ (Finset.univ : Finset ι), w i • v i) q := by
            simp only [A, smul_eq_mul, Finset.sum_filter, Finset.mem_univ,
              ↓reduceIte]
          _ = ∑ i ∈ (Finset.univ : Finset ι), w i • Real.rpow (v i) q := hjEqRaw
          _ = B := by
            simp only [B, smul_eq_mul, Finset.sum_filter, Finset.mem_univ,
              ↓reduceIte]
            apply Finset.sum_congr rfl
            intro i hi
            rw [hvq]
      have hp := congrArg (fun z : ℝ ↦ Real.rpow z lam) hjEq
      rw [hAq] at hp
      exact hp

@[blueprint "lem:bounded-mean-zero-real-weighted-comparison"
  (statement := /-- Let $I$ be finite, let $0<\lambda<1$, and let
  $(w_i)_{i\in I}$ be nonnegative weights with sum $1$.  If
  $u_i\geq0$ and $v_i\leq u_i^\lambda$ for every $i$, then
  \[
    \sum_iw_iv_i\leq\left(\sum_iw_iu_i\right)^\lambda.
  \]
  Equality holds if and only if $v_i=u_i^\lambda$ at every nonzero-weight
  index and all $u_i$ carrying nonzero weight are equal. -/)
  (proof := /-- Sum the pointwise comparisons and then apply
  \cref{lem:bounded-mean-zero-real-rpow-jensen}.  Equality in the composed
  inequality forces equality in both steps.  Equality in the first step
  forces every positive-weight pointwise comparison to be an equality,
  while the cited strict Jensen criterion characterizes equality in the
  second step.  The two conditions conversely make both steps equalities. -/)
  (title := /-- Weighted comparison through a fractional power -/)
  (latexEnv := "lemma")]
lemma bounded_mean_zero_real_weighted_comparison {ι : Type*} [Fintype ι]
    (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1)
    (w u v : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hu : ∀ i, 0 ≤ u i)
    (hvu : ∀ i, v i ≤ Real.rpow (u i) lam) :
    (∑ i, w i * v i) ≤ Real.rpow (∑ i, w i * u i) lam ∧
      ((∑ i, w i * v i) = Real.rpow (∑ i, w i * u i) lam ↔
        (∀ i, w i ≠ 0 → v i = Real.rpow (u i) lam) ∧
          ∀ i j, w i ≠ 0 → w j ≠ 0 → u i = u j) := by
  classical
  obtain ⟨hjensen, hjensen_eq⟩ :=
    bounded_mean_zero_real_rpow_jensen lam hlam₀ hlam₁ w u hw hsum hu
  have hpoint :
      (∑ i, w i * v i) ≤ ∑ i, w i * Real.rpow (u i) lam := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hvu i) (hw i)
  constructor
  · exact hpoint.trans hjensen
  · constructor
    · intro heq
      have hfirst :
          (∑ i, w i * v i) = ∑ i, w i * Real.rpow (u i) lam := by
        apply le_antisymm hpoint
        nlinarith
      have hsecond :
          (∑ i, w i * Real.rpow (u i) lam) =
            Real.rpow (∑ i, w i * u i) lam := by
        apply le_antisymm hjensen
        nlinarith
      constructor
      · intro i hwi
        by_contra hne
        have hwipos : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hwi)
        have hstrict : w i * v i < w i * Real.rpow (u i) lam :=
          mul_lt_mul_of_pos_left (lt_of_le_of_ne (hvu i) hne) hwipos
        have hsumstrict :
            (∑ j, w j * v j) < ∑ j, w j * Real.rpow (u j) lam := by
          apply Finset.sum_lt_sum
          · intro j hj
            exact mul_le_mul_of_nonneg_left (hvu j) (hw j)
          · exact ⟨i, Finset.mem_univ i, hstrict⟩
        exact (ne_of_lt hsumstrict) hfirst
      · exact hjensen_eq.mp hsecond
    · rintro ⟨hpoint_eq, hu_eq⟩
      have hfirst :
          (∑ i, w i * v i) = ∑ i, w i * Real.rpow (u i) lam := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hwi : w i = 0
        · simp [hwi]
        · rw [hpoint_eq i hwi]
      calc
        ∑ i, w i * v i = ∑ i, w i * Real.rpow (u i) lam := hfirst
        _ = Real.rpow (∑ i, w i * u i) lam := hjensen_eq.mpr hu_eq

@[blueprint "lem:bounded-mean-zero-real-two-point-power-comparison"
  (statement := /-- Let $r\geq2$, $0<\rho<1$, and $\alpha>0$, and set
  \[
    \lambda=\frac{\log B_r(\rho;1,\alpha)}
                       {\log B_r(1;1,\alpha)}.
  \]
  Then $0<\lambda<1$.  Moreover, if $0<a\leq1$ and
  $0<b\leq\alpha$, then
  \[
    B_r(1;a,b)>1,\qquad
    B_r(\rho;a,b)\leq B_r(1;a,b)^\lambda,
  \]
  with equality if and only if $a=1$ and $b=\alpha$. -/)
  (proof := /-- For the moments defined in
  \cref{def:two-point-moment}, strict convexity of the real $r$th power
  shows that every nondegenerate centered two-point moment at a positive scale is greater
  than $1$, and that its moment at scale $\rho$ is strictly smaller than
  its moment at scale $1$.  Hence the two endpoint logarithms are positive
  and their ratio lies in $(0,1)$.  Apply
  \cref{lem:two-point-log-ratio-comparison}, multiply by the positive
  denominator logarithm, and exponentiate.  Injectivity of the exponential
  transfers the equality criterion from the logarithmic comparison. -/)
  (title := /-- Sharp power comparison for centered two-point moments -/)
  (latexEnv := "lemma")]
lemma bounded_mean_zero_real_two_point_power_comparison
    (r ρ α : ℝ) (hr : 2 ≤ r) (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1)
    (hα : 0 < α) :
    let lam := Real.log (two_point_moment r ρ 1 α) /
      Real.log (two_point_moment r 1 1 α)
    0 < lam ∧ lam < 1 ∧
      ∀ a b : ℝ, 0 < a → a ≤ 1 → 0 < b → b ≤ α →
        1 < two_point_moment r 1 a b ∧
          two_point_moment r ρ a b ≤
              Real.rpow (two_point_moment r 1 a b) lam ∧
            (two_point_moment r ρ a b =
                Real.rpow (two_point_moment r 1 a b) lam ↔
              a = 1 ∧ b = α) := by
  have hr1 : 1 < r := lt_of_lt_of_le one_lt_two hr
  have hMgt (s x y : ℝ) (hs₀ : 0 < s) (hs₁ : s ≤ 1)
      (hx₀ : 0 < x) (hx₁ : x ≤ 1) (hy₀ : 0 < y) :
      1 < two_point_moment r s x y := by
    have hxy : 0 < x + y := add_pos hx₀ hy₀
    have hsx : s * x ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_left hx₁ hs₀.le
      nlinarith
    have hA :
        1 + r * (s * y) < Real.rpow (1 + s * y) r :=
      one_add_mul_self_lt_rpow_one_add
        (by
          have : 0 ≤ s * y := mul_nonneg hs₀.le hy₀.le
          linarith)
        (ne_of_gt (mul_pos hs₀ hy₀)) hr1
    have hC :
        1 + r * (-s * x) ≤ Real.rpow (1 + (-s * x)) r :=
      one_add_mul_self_le_rpow_one_add (by linarith : -1 ≤ -s * x) hr1.le
    have hweighted :
        x * (1 + r * (s * y)) + y * (1 + r * (-s * x)) <
          x * Real.rpow (1 + s * y) r +
            y * Real.rpow (1 - s * x) r := by
      have hA' := mul_lt_mul_of_pos_left hA hx₀
      have hC' := mul_le_mul_of_nonneg_left hC hy₀.le
      rw [show 1 + -s * x = 1 - s * x by ring] at hC'
      nlinarith
    rw [two_point_moment]
    apply (lt_div_iff₀ hxy).2
    nlinarith
  have hMlt (s x y : ℝ) (hs₀ : 0 < s) (hs₁ : s < 1)
      (hx₀ : 0 < x) (hx₁ : x ≤ 1) (hy₀ : 0 < y) :
      two_point_moment r s x y < two_point_moment r 1 x y := by
    have hxy : 0 < x + y := add_pos hx₀ hy₀
    have honepow : Real.rpow 1 r = 1 := by simp
    have hAseg :=
      (strictConvexOn_rpow hr1).2
        (show (1 : ℝ) ∈ Set.Ici 0 by simp)
        (show 1 + y ∈ Set.Ici (0 : ℝ) by
          simp only [Set.mem_Ici]
          linarith)
        (by linarith : (1 : ℝ) ≠ 1 + y)
        (sub_pos.mpr hs₁) hs₀ (by ring : (1 - s) + s = 1)
    have hCseg :=
      (strictConvexOn_rpow hr1).2
        (show (1 : ℝ) ∈ Set.Ici 0 by simp)
        (show 1 - x ∈ Set.Ici (0 : ℝ) by
          simpa only [Set.mem_Ici] using sub_nonneg.mpr hx₁)
        (by linarith : (1 : ℝ) ≠ 1 - x)
        (sub_pos.mpr hs₁) hs₀ (by ring : (1 - s) + s = 1)
    have hAseg' :
        Real.rpow (1 + s * y) r <
          (1 - s) * 1 + s * Real.rpow (1 + y) r := by
      have hAseg0 :
          Real.rpow ((1 - s) * 1 + s * (1 + y)) r <
            (1 - s) * Real.rpow 1 r + s * Real.rpow (1 + y) r := hAseg
      rw [honepow] at hAseg0
      convert hAseg0 using 1 <;> ring_nf
    have hCseg' :
        Real.rpow (1 - s * x) r <
          (1 - s) * 1 + s * Real.rpow (1 - x) r := by
      have hCseg0 :
          Real.rpow ((1 - s) * 1 + s * (1 - x)) r <
            (1 - s) * Real.rpow 1 r + s * Real.rpow (1 - x) r := hCseg
      rw [honepow] at hCseg0
      convert hCseg0 using 1 <;> ring_nf
    have hM1 : 1 < two_point_moment r 1 x y :=
      hMgt 1 x y zero_lt_one le_rfl hx₀ hx₁ hy₀
    rw [two_point_moment, two_point_moment]
    norm_num only [one_mul]
    have hnumA := mul_lt_mul_of_pos_left hAseg' hx₀
    have hnumC := mul_lt_mul_of_pos_left hCseg' hy₀
    have hnum1 :
        x + y < x * Real.rpow (1 + y) r +
          y * Real.rpow (1 - x) r := by
      rw [two_point_moment] at hM1
      have h' := (lt_div_iff₀ hxy).mp hM1
      norm_num only [one_mul] at h'
      exact h'
    apply (div_lt_div_iff_of_pos_right hxy).2
    nlinarith [mul_pos (sub_pos.mpr hs₁) (sub_pos.mpr hnum1)]
  let lam := Real.log (two_point_moment r ρ 1 α) /
    Real.log (two_point_moment r 1 1 α)
  have hMρ : 1 < two_point_moment r ρ 1 α :=
    hMgt ρ 1 α hρ₀ hρ₁.le zero_lt_one le_rfl hα
  have hM1 : 1 < two_point_moment r 1 1 α :=
    hMgt 1 1 α zero_lt_one le_rfl zero_lt_one le_rfl hα
  have hMρM1 : two_point_moment r ρ 1 α < two_point_moment r 1 1 α :=
    hMlt ρ 1 α hρ₀ hρ₁ zero_lt_one le_rfl hα
  have hlogρ : 0 < Real.log (two_point_moment r ρ 1 α) := Real.log_pos hMρ
  have hlog1 : 0 < Real.log (two_point_moment r 1 1 α) := Real.log_pos hM1
  have hloglt :
      Real.log (two_point_moment r ρ 1 α) <
        Real.log (two_point_moment r 1 1 α) :=
    Real.strictMonoOn_log
      (show two_point_moment r ρ 1 α ∈ Set.Ioi (0 : ℝ) by
        exact Set.mem_Ioi.mpr (lt_trans zero_lt_one hMρ))
      (show two_point_moment r 1 1 α ∈ Set.Ioi (0 : ℝ) by
        exact Set.mem_Ioi.mpr (lt_trans zero_lt_one hM1)) hMρM1
  refine ⟨div_pos hlogρ hlog1, (div_lt_one hlog1).2 hloglt, ?_⟩
  intro a b ha₀ ha₁ hb₀ hbα
  have hMaρ : 1 < two_point_moment r ρ a b :=
    hMgt ρ a b hρ₀ hρ₁.le ha₀ ha₁ hb₀
  have hMa1 : 1 < two_point_moment r 1 a b :=
    hMgt 1 a b zero_lt_one le_rfl ha₀ ha₁ hb₀
  have hloga1 : 0 < Real.log (two_point_moment r 1 a b) := Real.log_pos hMa1
  obtain ⟨hratio, hratio_eq⟩ :=
    two_point_log_ratio_comparison r ρ α a b hr hρ₀ hρ₁ hα ha₀ ha₁ hb₀ hbα
  have hratio' :
      Real.log (two_point_moment r ρ a b) /
          Real.log (two_point_moment r 1 a b) ≤ lam := by
    simpa only [lam] using hratio
  have hlogle :
      Real.log (two_point_moment r ρ a b) ≤
        Real.log (two_point_moment r 1 a b) * lam := by
    have := (div_le_iff₀ hloga1).mp hratio'
    nlinarith
  have hpower :
      two_point_moment r ρ a b ≤
        Real.rpow (two_point_moment r 1 a b) lam := by
    calc
      two_point_moment r ρ a b =
          Real.exp (Real.log (two_point_moment r ρ a b)) :=
        (Real.exp_log (lt_trans zero_lt_one hMaρ)).symm
      _ ≤ Real.exp (Real.log (two_point_moment r 1 a b) * lam) :=
        Real.exp_le_exp.mpr hlogle
      _ = Real.rpow (two_point_moment r 1 a b) lam :=
        (Real.rpow_def_of_pos (lt_trans zero_lt_one hMa1) lam).symm
  refine ⟨hMa1, hpower, ?_⟩
  constructor
  · intro heq
    change two_point_moment r ρ a b =
      Real.rpow (two_point_moment r 1 a b) lam at heq
    have heqexp :
        two_point_moment r ρ a b =
          Real.exp (Real.log (two_point_moment r 1 a b) * lam) := by
      exact heq.trans
        (Real.rpow_def_of_pos (lt_trans zero_lt_one hMa1) lam)
    have hlogeq := congrArg Real.log heqexp
    rw [Real.log_exp] at hlogeq
    have hratio_lam :
        Real.log (two_point_moment r ρ a b) /
            Real.log (two_point_moment r 1 a b) = lam := by
      apply (div_eq_iff (ne_of_gt hloga1)).2
      nlinarith
    apply hratio_eq.mp
    simpa only [lam] using hratio_lam
  · rintro ⟨ha, hb⟩
    rw [ha, hb]
    have hden : Real.log (two_point_moment r 1 1 α) ≠ 0 := ne_of_gt hlog1
    calc
      two_point_moment r ρ 1 α =
          Real.exp (Real.log (two_point_moment r ρ 1 α)) :=
        (Real.exp_log (lt_trans zero_lt_one hMρ)).symm
      _ = Real.exp (Real.log (two_point_moment r 1 1 α) * lam) := by
        congr 1
        dsimp only [lam]
        field_simp [hden]
      _ = Real.rpow (two_point_moment r 1 1 α) lam :=
        (Real.rpow_def_of_pos (lt_trans zero_lt_one hM1) lam).symm

@[blueprint "lem:bounded-mean-zero-real-moment-comparison"
  (statement := /-- Let $\mu$ be a full-support probability mass function
  on a finite space, let $r\geq2$, let $0<\rho<1$, and let $\alpha>0$.
  Define
  \[
    \lambda=
      \frac{\log B_r(\rho;1,\alpha)}
           {\log B_r(1;1,\alpha)}.
  \]
  Then $\lambda\in(0,1)$, and every
  $X:\Omega\to\mathbb R$ satisfying
  \[
    \mathbb E_\mu X=0,\qquad -1\leq X\leq\alpha
  \]
  obeys
  \[
    \sum_x\mu(x)(1+\rho X(x))^r
      \leq
      \left(\sum_x\mu(x)(1+X(x))^r\right)^\lambda.
  \]
  Equality holds if and only if $X=0$ or every value of $X$ belongs to
  $\{-1,\alpha\}$. -/)
  (proof := /-- Define
  \[
    \lambda=
      \frac{\log B_r(\rho;1,\alpha)}
           {\log B_r(1;1,\alpha)},
  \]
  where $B_r$ is the centered two-point moment from
  \cref{def:two-point-moment}.  By
  \cref{lem:bounded-mean-zero-real-two-point-power-comparison}, one has
  $0<\lambda<1$, and for $0<a\leq1$ and $0<b\leq\alpha$,
  \[
    B_r(\rho;a,b)\leq B_r(1;a,b)^\lambda,                 \tag{1}
  \]
  with equality exactly when $a=1$ and $b=\alpha$; moreover
  $B_r(1;a,b)>1$.

  If $X=0$, the probability-mass identity makes both displayed moments
  equal to $1$.  Otherwise apply
  \cref{lem:centered-finite-law-two-point-decomposition}.  Adjoin the zero
  component to its pairs $(i,j)$ to obtain a finite probability vector:
  its zero weight is
  $z=\sum_x\mu(x)\mathbf1_{\{X(x)=0\}}$, and its pair weight is $w_{ij}$.
  Give the zero component denominator and numerator moments both equal to
  $1$.  At a positive pair weight put $a=-X(i)$ and $b=X(j)$ and use
  $B_r(1;a,b)$ and $B_r(\rho;a,b)$; at a zero pair weight assign both
  moments the harmless value $1$.  Applying the decomposition identity to
  $u\mapsto(1+su)^r$, first for $s=\rho$ and then for $s=1$, identifies the
  corresponding weighted sums with the two moments in the statement.

  The pointwise bound (1), followed by
  \cref{lem:bounded-mean-zero-real-weighted-comparison}, proves the desired
  inequality.  For equality, that lemma requires both equality in every
  positive-weight instance of (1) and equality in strict Jensen.  Since a
  nonzero function centered in the sense of
  \cref{def:one-coordinate-mean} under the full-support condition
  \cref{def:full-support-pmf} assumes a negative and a positive value, the
  positivity criterion in
  \cref{lem:centered-finite-law-two-point-decomposition} supplies a positive
  pair weight.  Equality in (1) then forces every negative value to be
  $-1$ and every positive value to be $\alpha$.  The zero component cannot
  have positive weight: strict Jensen would equate its denominator moment
  $1$ with that of a positive pair, which is strictly greater than $1$.
  Thus every value of $X$ belongs to $\{-1,\alpha\}$.  Conversely, for an
  endpoint-valued $X$, the zero component vanishes, every positive pair is
  the pair $(-1,\alpha)$, and both equality conditions in the cited weighted
  comparison hold.  This proves the converse equality implication. -/)
  (title := /-- Sharp comparison of real moments for bounded centered laws -/)
  (latexEnv := "lemma")]
lemma bounded_mean_zero_real_moment_comparison {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω) (r ρ α : ℝ) (hμ : full_support_pmf μ)
    (hr : 2 ≤ r) (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) (hα : 0 < α) :
    0 < Real.log (two_point_moment r ρ 1 α) /
          Real.log (two_point_moment r 1 1 α) ∧
      Real.log (two_point_moment r ρ 1 α) /
          Real.log (two_point_moment r 1 1 α) < 1 ∧
      ∀ X : Ω → ℝ, one_coordinate_mean μ X = 0 →
        (∀ x, -1 ≤ X x ∧ X x ≤ α) →
        (∑ x, (μ x).toReal * Real.rpow (1 + ρ * X x) r) ≤
            Real.rpow
              (∑ x, (μ x).toReal * Real.rpow (1 + X x) r)
              (Real.log (two_point_moment r ρ 1 α) /
                Real.log (two_point_moment r 1 1 α)) ∧
          ((∑ x, (μ x).toReal * Real.rpow (1 + ρ * X x) r) =
                Real.rpow
                  (∑ x, (μ x).toReal * Real.rpow (1 + X x) r)
                  (Real.log (two_point_moment r ρ 1 α) /
                    Real.log (two_point_moment r 1 1 α)) ↔
            X = (fun _ ↦ 0) ∨ ∀ x, X x = -1 ∨ X x = α) := by
  classical
  let lam := Real.log (two_point_moment r ρ 1 α) /
    Real.log (two_point_moment r 1 1 α)
  obtain ⟨hlam₀, hlam₁, htwo⟩ :=
    bounded_mean_zero_real_two_point_power_comparison
      r ρ α hr hρ₀ hρ₁ hα
  change 0 < lam ∧ lam < 1 ∧ _
  refine ⟨hlam₀, hlam₁, ?_⟩
  intro X hmean hbounds
  by_cases hXzero : X = (fun _ ↦ 0)
  · subst X
    have hnotop (x : Ω) : μ x ≠ ⊤ := by
      exact ne_of_lt ((PMF.coe_le_one μ x).trans_lt ENNReal.one_lt_top)
    have hmassENN : ∑ x, μ x = 1 := by
      simpa only [tsum_fintype] using PMF.tsum_coe μ
    have hmass : ∑ x, (μ x).toReal = 1 := by
      calc
        ∑ x, (μ x).toReal = ENNReal.toReal (∑ x, μ x) := by
          simpa using
            (ENNReal.toReal_sum (s := Finset.univ)
              (f := fun x ↦ μ x) (fun x hx ↦ hnotop x)).symm
        _ = 1 := by rw [hmassENN]; simp
    simp [hmass]
  · obtain ⟨w, hw, hwpos, htotal, hdecomp⟩ :=
      centered_finite_law_two_point_decomposition μ X hμ hmean hXzero
    let W : Ω ⊕ (Ω × Ω) → ℝ
      | Sum.inl x => (μ x).toReal * (if X x = 0 then 1 else 0)
      | Sum.inr ij => w ij.1 ij.2
    let M (s : ℝ) : Ω ⊕ (Ω × Ω) → ℝ
      | Sum.inl _ => 1
      | Sum.inr ij =>
          if w ij.1 ij.2 = 0 then 1
          else two_point_moment r s (-X ij.1) (X ij.2)
    have hW_nonneg : ∀ k, 0 ≤ W k := by
      intro k
      cases k with
      | inl x =>
          simp only [W]
          positivity
      | inr ij =>
          exact hw ij.1 ij.2
    have hW_sum : ∑ k, W k = 1 := by
      rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
      change (∑ x, (μ x).toReal * (if X x = 0 then 1 else 0)) +
          ∑ i, ∑ j, w i j = 1
      linarith
    have hmoment (s : ℝ) (i j : Ω) :
        ((-X i) * Real.rpow (1 + s * X j) r +
              X j * Real.rpow (1 + s * X i) r) /
            (X j - X i) =
          two_point_moment r s (-X i) (X j) := by
      rw [two_point_moment]
      ring_nf
    have hsumM (s : ℝ) :
        (∑ k, W k * M s k) =
          ∑ x, (μ x).toReal * Real.rpow (1 + s * X x) r := by
      rw [hdecomp (fun y ↦ Real.rpow (1 + s * y) r)]
      rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
      simp only [W, M, mul_one, mul_zero, add_zero, Real.one_rpow]
      have hone : Real.rpow (1 : ℝ) r = 1 := by
        simp [Real.rpow]
      rw [hone, mul_one]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hwij : w i j = 0
      · simp [hwij]
      · rw [if_neg hwij, ← hmoment]
        ring
    have hM_nonneg : ∀ k, 0 ≤ M 1 k := by
      intro k
      cases k with
      | inl x => simp [M]
      | inr ij =>
          rcases ij with ⟨i, j⟩
          by_cases hwij : w i j = 0
          · simp [M, hwij]
          · have hwijpos : 0 < w i j :=
              lt_of_le_of_ne (hw i j) (Ne.symm hwij)
            have hij := (hwpos i j).mp hwijpos
            have hlocal := htwo (-X i) (X j)
              (by linarith) (by linarith [((hbounds i).1)])
              hij.2 (hbounds j).2
            simpa [M, hwij] using (le_trans zero_le_one hlocal.1.le)
    have hpoint : ∀ k, M ρ k ≤ Real.rpow (M 1 k) lam := by
      intro k
      cases k with
      | inl x => simp [M]
      | inr ij =>
          rcases ij with ⟨i, j⟩
          by_cases hwij : w i j = 0
          · simp [M, hwij]
          · have hwijpos : 0 < w i j :=
              lt_of_le_of_ne (hw i j) (Ne.symm hwij)
            have hij := (hwpos i j).mp hwijpos
            have hlocal := htwo (-X i) (X j)
              (by linarith) (by linarith [((hbounds i).1)])
              hij.2 (hbounds j).2
            simpa [M, hwij] using hlocal.2.1
    obtain ⟨hcomparison, hequality⟩ :=
      bounded_mean_zero_real_weighted_comparison
        lam hlam₀ hlam₁ W (M 1) (M ρ) hW_nonneg hW_sum hM_nonneg hpoint
    rw [hsumM ρ, hsumM 1] at hcomparison hequality
    constructor
    · simpa [lam] using hcomparison
    · constructor
      · intro heq
        have hcriteria := hequality.mp (by simpa [lam] using heq)
        right
        have hp (x : Ω) : 0 < (μ x).toReal := by
          exact ENNReal.toReal_pos (hμ x)
            (ne_of_lt ((PMF.coe_le_one μ x).trans_lt ENNReal.one_lt_top))
        have hXpoint : ∃ x, X x ≠ 0 := by
          by_contra h
          apply hXzero
          funext x
          by_contra hx
          exact h ⟨x, hx⟩
        have hterm :
            ∃ x ∈ (Finset.univ : Finset Ω), (μ x).toReal * X x ≠ 0 := by
          obtain ⟨x, hx⟩ := hXpoint
          exact ⟨x, Finset.mem_univ x, mul_ne_zero (ne_of_gt (hp x)) hx⟩
        have hmean' : ∑ x, (μ x).toReal * X x = 0 := by
          simpa [one_coordinate_mean] using hmean
        obtain ⟨ipos, hipos_mem, hipos⟩ :=
          Finset.exists_pos_of_sum_zero_of_exists_nonzero
            (s := Finset.univ) (fun x ↦ (μ x).toReal * X x) hmean' hterm
        have hXpos : 0 < X ipos := by
          nlinarith [hp ipos]
        have hmean_neg : ∑ x, -((μ x).toReal * X x) = 0 := by
          rw [Finset.sum_neg_distrib, hmean']
          simp
        have hterm_neg :
            ∃ x ∈ (Finset.univ : Finset Ω), -((μ x).toReal * X x) ≠ 0 := by
          obtain ⟨x, hxmem, hx⟩ := hterm
          exact ⟨x, hxmem, neg_ne_zero.mpr hx⟩
        obtain ⟨ineg, hineg_mem, hineg⟩ :=
          Finset.exists_pos_of_sum_zero_of_exists_nonzero
            (s := Finset.univ) (fun x ↦ -((μ x).toReal * X x))
            hmean_neg hterm_neg
        have hXneg : X ineg < 0 := by
          nlinarith [hp ineg]
        intro x
        rcases lt_trichotomy (X x) 0 with hxneg | hxzero | hxpos
        · have hwxi : 0 < w x ipos := (hwpos x ipos).2 ⟨hxneg, hXpos⟩
          have hpair_eq := hcriteria.1 (Sum.inr (x, ipos)) (by
            simpa [W] using ne_of_gt hwxi)
          have hlocal := htwo (-X x) (X ipos)
            (by linarith) (by linarith [((hbounds x).1)])
            hXpos (hbounds ipos).2
          have hend := hlocal.2.2.mp (by
            simpa [M, ne_of_gt hwxi] using hpair_eq)
          left
          linarith [hend.1]
        · have hwip : 0 < w ineg ipos :=
            (hwpos ineg ipos).2 ⟨hXneg, hXpos⟩
          have hzero_weight : 0 < W (Sum.inl x) := by
            simp [W, hxzero, hp x]
          have hpair_weight : 0 < W (Sum.inr (ineg, ipos)) := by
            simpa [W] using hwip
          have hu_eq := hcriteria.2 (Sum.inl x) (Sum.inr (ineg, ipos))
            (ne_of_gt hzero_weight) (ne_of_gt hpair_weight)
          have hlocal := htwo (-X ineg) (X ipos)
            (by linarith) (by linarith [((hbounds ineg).1)])
            hXpos (hbounds ipos).2
          have huneq : M 1 (Sum.inr (ineg, ipos)) =
              two_point_moment r 1 (-X ineg) (X ipos) := by
            simp [M, ne_of_gt hwip]
          have : (1 : ℝ) = two_point_moment r 1 (-X ineg) (X ipos) := by
            simpa [M, huneq] using hu_eq
          linarith [hlocal.1]
        · have hwix : 0 < w ineg x := (hwpos ineg x).2 ⟨hXneg, hxpos⟩
          have hpair_eq := hcriteria.1 (Sum.inr (ineg, x)) (by
            simpa [W] using ne_of_gt hwix)
          have hlocal := htwo (-X ineg) (X x)
            (by linarith) (by linarith [((hbounds ineg).1)])
            hxpos (hbounds x).2
          have hend := hlocal.2.2.mp (by
            simpa [M, ne_of_gt hwix] using hpair_eq)
          right
          exact hend.2
      · intro hcases
        rcases hcases with hzero | hend
        · exact (hXzero hzero).elim
        · have hpair_end (i j : Ω) (hwij : w i j ≠ 0) :
              X i = -1 ∧ X j = α := by
            have hwijpos : 0 < w i j :=
              lt_of_le_of_ne (hw i j) (Ne.symm hwij)
            have hij := (hwpos i j).mp hwijpos
            constructor
            · rcases hend i with hi | hi
              · exact hi
              · linarith
            · rcases hend j with hj | hj
              · linarith
              · exact hj
          have hresult :
              ∑ x, (μ x).toReal * Real.rpow (1 + ρ * X x) r =
                Real.rpow
                  (∑ x, (μ x).toReal * Real.rpow (1 + 1 * X x) r) lam := by
            apply hequality.mpr
            constructor
            · intro k hk
              cases k with
              | inl x => simp [M]
              | inr ij =>
                  rcases ij with ⟨i, j⟩
                  have hwij : w i j ≠ 0 := by simpa [W] using hk
                  obtain ⟨hi, hj⟩ := hpair_end i j hwij
                  have hlocal := htwo 1 α zero_lt_one le_rfl hα le_rfl
                  have he := hlocal.2.2.mpr ⟨rfl, rfl⟩
                  simpa [M, hwij, hi, hj] using he
            · have hconstant (k : Ω ⊕ (Ω × Ω)) (hk : W k ≠ 0) :
                  M 1 k = two_point_moment r 1 1 α := by
                cases k with
                | inl x =>
                    exfalso
                    have hxzero : X x = 0 := by
                      by_contra hx
                      simp [W, hx] at hk
                    rcases hend x with hx | hx <;> linarith
                | inr ij =>
                    rcases ij with ⟨i, j⟩
                    have hwij : w i j ≠ 0 := by simpa [W] using hk
                    obtain ⟨hi, hj⟩ := hpair_end i j hwij
                    simp [M, hwij, hi, hj]
              intro i j hi hj
              exact (hconstant i hi).trans (hconstant j hj).symm
          simpa [lam] using hresult

@[blueprint "lem:weighted-lp-norm-finite-moment"
  (statement := /-- Let $\Omega$ be a finite measurable space in which every
  singleton is measurable, let $\mu$ be a probability mass function on
  $\Omega$, let $q\in\mathbb R_{\geq 0}\cup\{\infty\}$ satisfy
  $q\ne 0$ and $q\ne\infty$, write $r=q.toReal$, and let
  $f:\Omega\to\mathbb R$.
  Then
  \[
    \|f\|_{L^q(\mu)}
      =
      \left(
        \sum_{x\in\Omega}\mu(x)|f(x)|^r
      \right)^{1/r},
  \]
  where the sum is embedded in $\mathbb R_{\geq0}\cup\{\infty\}$. -/)
  (proof := /-- Unfold \cref{def:weighted-lp-norm} and use
  \(\texttt{MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal}\),
  whose exponent hypotheses are $q\ne0$ and $q\ne\infty$.  Then
  \(\texttt{MeasureTheory.lintegral_fintype}\) and
  \(\texttt{PMF.toMeasure_apply_singleton}\) rewrite the base of the
  resulting power as
  \[
    \sum_x\mu(x)\,\lVert f(x)\rVert_{\mathbb R_{\geq0}\cup\{\infty\}}^{q.toReal}.
  \]
  For every $x$, the identity
  \(\texttt{Real.enorm_eq_ofReal_abs}\), preservation of nonnegative real
  powers and products by \(\texttt{ENNReal.ofReal}\), and finiteness of
  $\mu(x)$ identify this summand with
  \[
    \operatorname{ofReal}\!\left(\mu(x).toReal\,|f(x)|^{q.toReal}\right).
  \]
  Each real summand is nonnegative, so
  \(\texttt{ENNReal.ofReal_sum_of_nonneg}\) moves
  \(\texttt{ENNReal.ofReal}\) through the finite sum.  The bases, and hence
  their powers by $1/q.toReal$, are therefore equal. -/)
  (title := /-- Finite-sum formula for the weighted \(L^q\) norm -/)
  (latexEnv := "lemma")]
lemma weighted_lp_norm_finite_moment {Ω : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : PMF Ω) (q : ℝ≥0∞) (f : Ω → ℝ)
    (hq₀ : q ≠ 0) (hqtop : q ≠ ⊤) :
    weighted_lp_norm μ.toMeasure q f =
      ENNReal.rpow
        (ENNReal.ofReal
          (∑ x, (μ x).toReal * Real.rpow (|f x|) q.toReal))
        (1 / q.toReal) := by
  rw [weighted_lp_norm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hq₀ hqtop,
    lintegral_fintype]
  congr 1
  rw [show ENNReal.ofReal
      (∑ x, (μ x).toReal * Real.rpow |f x| q.toReal) =
        ∑ x, ENNReal.ofReal
          ((μ x).toReal * Real.rpow |f x| q.toReal) by
    simpa using ENNReal.ofReal_sum_of_nonneg
      (s := Finset.univ)
      (f := fun x ↦ (μ x).toReal * Real.rpow |f x| q.toReal)
      (by
        intro i hi
        exact mul_nonneg ENNReal.toReal_nonneg
          (Real.rpow_nonneg (abs_nonneg _) _))]
  apply Finset.sum_congr rfl
  intro x hx
  rw [μ.toMeasure_apply_singleton x (MeasurableSet.singleton x),
    Real.enorm_eq_ofReal_abs,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) ENNReal.toReal_nonneg,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (PMF.apply_ne_top μ x), mul_comm,
    ← Real.rpow_eq_pow]

@[blueprint "lem:bounded-mean-zero-moment-comparison"
  (statement := /-- Let $\Omega$ be a finite measurable space in which every
  singleton is measurable, let $\mu$ be a full-support probability mass
  function on $\Omega$, let $2\leq q<\infty$, let $0<\rho<1$, and let
  $\alpha>0$.  Define
  \[
    \lambda=
      \frac{\log B_{q.toReal}(\rho;1,\alpha)}
           {\log B_{q.toReal}(1;1,\alpha)}.
  \]
  Then $\lambda\in(0,1)$, and every
  $X:\Omega\to\mathbb R$ with
  \[
    \mathbb E_\mu X=0,\qquad -1\leq X\leq\alpha
  \]
  satisfies
  \[
    \|1+\rho X\|_{L^q(\mu)}
      \leq\|1+X\|_{L^q(\mu)}^\lambda.
  \]
  Equality holds exactly when $X=0$ or every value of $X$ belongs to $\{-1,\alpha\}$. -/)
  (proof := /-- Put $r=q.toReal$.  The assumptions $2\leq q<\infty$
  imply $2\leq r$.  Apply
  \cref{lem:bounded-mean-zero-real-moment-comparison} with this exponent;
  its parameter is precisely the displayed ratio, and it lies in $(0,1)$.

  Fix an admissible $X$, and write
  \[
    A_\rho=\sum_x\mu(x)(1+\rho X(x))^r,
    \qquad A_1=\sum_x\mu(x)(1+X(x))^r.
  \]
  The bounds $-1\leq X\leq\alpha$ and $0<\rho<1$ imply
  \[
    1+X(x)\geq0,\qquad 1+\rho X(x)>0
  \]
  for every $x$.  Apply
  \cref{lem:weighted-lp-norm-finite-moment} to the functions
  $x\mapsto1+X(x)$ and $x\mapsto1+\rho X(x)$.  The absolute values in
  the two finite-moment formulae therefore disappear, and the norms are
  $A_\rho^{1/r}$ and $A_1^{1/r}$, respectively.

  The moment comparison gives $A_\rho\leq A_1^\lambda$.  Both moments
  are nonnegative.  Embed this inequality into
  $\mathbb R_{\geq0}\cup\{\infty\}$ and apply the monotone map
  $u\mapsto u^{1/r}$.  Since the embedding commutes with nonnegative
  real powers and
  \[
    (u^\lambda)^{1/r}=(u^{1/r})^\lambda,
  \]
  this is the required norm inequality.

  Because $1/r>0$, the map $u\mapsto u^{1/r}$ is injective on
  $\mathbb R_{\geq0}\cup\{\infty\}$; the nonnegative-real embedding is
  also injective on the two moments.  Thus equality of the norms is
  equivalent to $A_\rho=A_1^\lambda$.  The equality clause of
  \cref{lem:bounded-mean-zero-real-moment-comparison} then gives exactly
  $X=0$ or $X(x)\in\{-1,\alpha\}$ for every $x$, and each of those two
  alternatives yields equality by the converse direction of that same
  clause. -/)
  (title := /-- Sharp finite-exponent comparison for bounded centered laws -/)
  (latexEnv := "lemma")]
lemma bounded_mean_zero_moment_comparison {Ω : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : PMF Ω) (q : ℝ≥0∞) (ρ α : ℝ)
    (hμ : full_support_pmf μ) (hq : (2 : ℝ≥0∞) ≤ q) (hqtop : q ≠ ⊤)
    (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) (hα : 0 < α) :
    0 < Real.log (two_point_moment q.toReal ρ 1 α) /
          Real.log (two_point_moment q.toReal 1 1 α) ∧
      Real.log (two_point_moment q.toReal ρ 1 α) /
          Real.log (two_point_moment q.toReal 1 1 α) < 1 ∧
      ∀ X : Ω → ℝ, one_coordinate_mean μ X = 0 →
        (∀ x, -1 ≤ X x ∧ X x ≤ α) →
        weighted_lp_norm μ.toMeasure q (fun x ↦ 1 + ρ * X x) ≤
            ENNReal.rpow
              (weighted_lp_norm μ.toMeasure q (fun x ↦ 1 + X x))
              (Real.log (two_point_moment q.toReal ρ 1 α) /
                Real.log (two_point_moment q.toReal 1 1 α)) ∧
          (weighted_lp_norm μ.toMeasure q (fun x ↦ 1 + ρ * X x) =
              ENNReal.rpow
                (weighted_lp_norm μ.toMeasure q (fun x ↦ 1 + X x))
                (Real.log (two_point_moment q.toReal ρ 1 α) /
                  Real.log (two_point_moment q.toReal 1 1 α)) ↔
            X = (fun _ ↦ 0) ∨ ∀ x, X x = -1 ∨ X x = α) := by
  have hq₀ : q ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hq)
  have hr : 2 ≤ q.toReal := by
    simpa using
      (ENNReal.toReal_le_toReal (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hqtop).2 hq
  obtain ⟨hlam₀, hlam₁, hcomparison⟩ :=
    bounded_mean_zero_real_moment_comparison μ q.toReal ρ α hμ hr hρ₀ hρ₁ hα
  refine ⟨hlam₀, hlam₁, ?_⟩
  intro X hmean hbounds
  obtain ⟨hmoment, hequality⟩ := hcomparison X hmean hbounds
  let lam := Real.log (two_point_moment q.toReal ρ 1 α) /
    Real.log (two_point_moment q.toReal 1 1 α)
  let Mρ := ∑ x, (μ x).toReal * Real.rpow (1 + ρ * X x) q.toReal
  let M₁ := ∑ x, (μ x).toReal * Real.rpow (1 + X x) q.toReal
  change Mρ ≤ Real.rpow M₁ lam at hmoment
  change (Mρ = Real.rpow M₁ lam ↔
    X = (fun _ ↦ 0) ∨ ∀ x, X x = -1 ∨ X x = α) at hequality
  have hbaseρ (x : Ω) : 0 ≤ 1 + ρ * X x := by
    have hmul := mul_le_mul_of_nonneg_left (hbounds x).1 hρ₀.le
    nlinarith
  have hbase₁ (x : Ω) : 0 ≤ 1 + X x := by
    linarith [(hbounds x).1]
  have hMρ : 0 ≤ Mρ := by
    apply Finset.sum_nonneg
    intro x hx
    exact mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (hbaseρ x) _)
  have hM₁ : 0 ≤ M₁ := by
    apply Finset.sum_nonneg
    intro x hx
    exact mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (hbase₁ x) _)
  have hqreal_pos : 0 < q.toReal := lt_of_lt_of_le (by norm_num) hr
  have hinv_pos : 0 < 1 / q.toReal := one_div_pos.mpr hqreal_pos
  have hlam_nonneg : 0 ≤ lam := by
    exact hlam₀.le
  have hnormρ :
      weighted_lp_norm μ.toMeasure q (fun x ↦ 1 + ρ * X x) =
        ENNReal.rpow (ENNReal.ofReal Mρ) (1 / q.toReal) := by
    simpa only [Mρ, abs_of_nonneg (hbaseρ _)] using
      (weighted_lp_norm_finite_moment μ q (fun x ↦ 1 + ρ * X x) hq₀ hqtop)
  have hnorm₁ :
      weighted_lp_norm μ.toMeasure q (fun x ↦ 1 + X x) =
        ENNReal.rpow (ENNReal.ofReal M₁) (1 / q.toReal) := by
    simpa only [M₁, abs_of_nonneg (hbase₁ _)] using
      (weighted_lp_norm_finite_moment μ q (fun x ↦ 1 + X x) hq₀ hqtop)
  change weighted_lp_norm μ.toMeasure q (fun x ↦ 1 + ρ * X x) ≤
      ENNReal.rpow (weighted_lp_norm μ.toMeasure q (fun x ↦ 1 + X x)) lam ∧
    (weighted_lp_norm μ.toMeasure q (fun x ↦ 1 + ρ * X x) =
        ENNReal.rpow (weighted_lp_norm μ.toMeasure q (fun x ↦ 1 + X x)) lam ↔
      X = (fun _ ↦ 0) ∨ ∀ x, X x = -1 ∨ X x = α)
  constructor
  · rw [hnormρ, hnorm₁]
    calc
      ENNReal.rpow (ENNReal.ofReal Mρ) (1 / q.toReal) ≤
          ENNReal.rpow (ENNReal.rpow (ENNReal.ofReal M₁) lam) (1 / q.toReal) := by
        apply ENNReal.rpow_le_rpow
        · calc
            ENNReal.ofReal Mρ ≤ ENNReal.ofReal (Real.rpow M₁ lam) :=
              ENNReal.ofReal_le_ofReal hmoment
            _ = ENNReal.rpow (ENNReal.ofReal M₁) lam :=
              (ENNReal.ofReal_rpow_of_nonneg hM₁ hlam_nonneg).symm
        · exact hinv_pos.le
      _ = ENNReal.rpow (ENNReal.rpow (ENNReal.ofReal M₁) (1 / q.toReal)) lam := by
        calc
          ENNReal.rpow (ENNReal.rpow (ENNReal.ofReal M₁) lam) (1 / q.toReal) =
              ENNReal.rpow (ENNReal.ofReal M₁) (lam * (1 / q.toReal)) :=
            (ENNReal.rpow_mul (ENNReal.ofReal M₁) lam (1 / q.toReal)).symm
          _ = ENNReal.rpow (ENNReal.ofReal M₁) ((1 / q.toReal) * lam) := by
            congr 1
            ring
          _ = ENNReal.rpow (ENNReal.rpow (ENNReal.ofReal M₁) (1 / q.toReal)) lam :=
            ENNReal.rpow_mul (ENNReal.ofReal M₁) (1 / q.toReal) lam
  · rw [hnormρ, hnorm₁]
    have hreorder :
        ENNReal.rpow (ENNReal.rpow (ENNReal.ofReal M₁) (1 / q.toReal)) lam =
          ENNReal.rpow (ENNReal.rpow (ENNReal.ofReal M₁) lam) (1 / q.toReal) := by
      calc
        ENNReal.rpow (ENNReal.rpow (ENNReal.ofReal M₁) (1 / q.toReal)) lam =
            ENNReal.rpow (ENNReal.ofReal M₁) ((1 / q.toReal) * lam) :=
          (ENNReal.rpow_mul (ENNReal.ofReal M₁) (1 / q.toReal) lam).symm
        _ = ENNReal.rpow (ENNReal.ofReal M₁) (lam * (1 / q.toReal)) := by
          congr 1
          ring
        _ = ENNReal.rpow (ENNReal.rpow (ENNReal.ofReal M₁) lam) (1 / q.toReal) :=
          ENNReal.rpow_mul (ENNReal.ofReal M₁) lam (1 / q.toReal)
    rw [hreorder, show ENNReal.rpow (ENNReal.ofReal M₁) lam =
      ENNReal.ofReal (Real.rpow M₁ lam) from
        ENNReal.ofReal_rpow_of_nonneg hM₁ hlam_nonneg]
    have hroot :
        (ENNReal.rpow (ENNReal.ofReal Mρ) (1 / q.toReal) =
            ENNReal.rpow (ENNReal.ofReal (Real.rpow M₁ lam)) (1 / q.toReal) ↔
          Mρ = Real.rpow M₁ lam) := by
      constructor
      · intro h
        apply (ENNReal.ofReal_eq_ofReal_iff hMρ (Real.rpow_nonneg hM₁ _)).mp
        exact ENNReal.rpow_left_injective (ne_of_gt hinv_pos) h
      · intro h
        apply congrArg (fun z : ℝ≥0∞ ↦ ENNReal.rpow z (1 / q.toReal))
        exact (ENNReal.ofReal_eq_ofReal_iff hMρ (Real.rpow_nonneg hM₁ _)).2 h
    exact hroot.trans hequality

@[blueprint "lem:bounded-mean-zero-sup-scalar-comparison"
  (statement := /-- Let $0<\rho<1$ and $\alpha>0$, and define
  \[
    \lambda=\frac{\log(1+\rho\alpha)}{\log(1+\alpha)}.
  \]
  Then $\lambda\in(0,1)$ and, for every $\beta\in[0,\alpha]$,
  \[
    1+\rho\beta\leq(1+\beta)^\lambda,
  \]
  and equality holds if and only if $\beta=0$ or $\beta=\alpha$. -/)
  (proof := /-- Set
  \[
    \lambda=\frac{\log(1+\rho\alpha)}{\log(1+\alpha)}.
  \]
  Put $s=\sqrt\rho$.  Then $0<s<1$ and $s^2=\rho$.  Apply
  \cref{lem:bounded-mean-zero-real-two-point-power-comparison} with
  exponent $2$, scale $s$, and endpoint parameter $\alpha$.  By
  \cref{lem:two-point-moment-two},
  \[
    B_2(s;1,b)=1+\rho b
    \quad\text{and}\quad
    B_2(1;1,b)=1+b.
  \]
  Consequently, the cited power comparison gives $0<\lambda<1$ and,
  for every $0<\beta\leq\alpha$,
  \[
    1+\rho\beta\leq(1+\beta)^\lambda,
  \]
  with equality if and only if $\beta=\alpha$.  When $\beta=0$, both
  sides are $1$; since $\alpha>0$, this is the other and only other
  equality case. -/)
  (title := /-- Sharp scalar comparison at the essential-supremum endpoint -/)
  (latexEnv := "lemma")]
lemma bounded_mean_zero_sup_scalar_comparison (ρ α : ℝ)
    (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) (hα : 0 < α) :
    0 < Real.log (1 + ρ * α) / Real.log (1 + α) ∧
      Real.log (1 + ρ * α) / Real.log (1 + α) < 1 ∧
      ∀ β : ℝ, 0 ≤ β → β ≤ α →
        1 + ρ * β ≤
            (1 + β) ^ (Real.log (1 + ρ * α) / Real.log (1 + α)) ∧
          (1 + ρ * β =
              (1 + β) ^ (Real.log (1 + ρ * α) / Real.log (1 + α)) ↔
            β = 0 ∨ β = α) := by
  have hsqrt₀ : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ₀
  have hsqrt_sq : (Real.sqrt ρ) ^ 2 = ρ := Real.sq_sqrt hρ₀.le
  have hsqrt₁ : Real.sqrt ρ < 1 := by
    nlinarith [Real.sqrt_nonneg ρ]
  obtain ⟨hlam₀, hlam₁, hcomp⟩ :=
    bounded_mean_zero_real_two_point_power_comparison
      2 (Real.sqrt ρ) α (by norm_num) hsqrt₀ hsqrt₁ hα
  have hαne : 1 + α ≠ 0 := ne_of_gt (by linarith)
  have hMαsqrt :
      two_point_moment 2 (Real.sqrt ρ) 1 α = 1 + ρ * α := by
    rw [two_point_moment_two (Real.sqrt ρ) 1 α hαne, hsqrt_sq]
    ring
  have hMαone : two_point_moment 2 1 1 α = 1 + α := by
    rw [two_point_moment_two 1 1 α hαne]
    ring
  rw [hMαsqrt, hMαone] at hlam₀ hlam₁
  refine ⟨hlam₀, hlam₁, ?_⟩
  intro β hβ₀ hβα
  by_cases hβzero : β = 0
  · subst β
    norm_num
  · have hβpos : 0 < β := lt_of_le_of_ne hβ₀ (Ne.symm hβzero)
    have hβne : 1 + β ≠ 0 := ne_of_gt (by linarith)
    obtain ⟨_, hle, heq⟩ :=
      hcomp 1 β zero_lt_one le_rfl hβpos hβα
    have hMβsqrt :
        two_point_moment 2 (Real.sqrt ρ) 1 β = 1 + ρ * β := by
      rw [two_point_moment_two (Real.sqrt ρ) 1 β hβne, hsqrt_sq]
      ring
    have hMβone : two_point_moment 2 1 1 β = 1 + β := by
      rw [two_point_moment_two 1 1 β hβne]
      ring
    rw [hMαsqrt, hMαone, hMβsqrt, hMβone] at hle heq
    refine ⟨hle, ?_⟩
    constructor
    · intro h
      exact Or.inr (heq.mp h).2
    · intro h
      rcases h with h | h
      · exact (hβzero h).elim
      · exact heq.mpr ⟨rfl, h⟩

@[blueprint "lem:bounded-mean-zero-sup-comparison"
  (statement := /-- Let $\Omega$ be a finite measurable space whose singletons are measurable, let $\mu$ be a full-support probability mass function on $\Omega$, let $0<\rho<1$, and let $\alpha>0$.  Suppose that
  \[
    \mu(x)\geq (1+\alpha)^{-1}\qquad\text{for every }x\in\Omega.
  \]
  Define
  \[
    \lambda=\frac{\log(1+\rho\alpha)}{\log(1+\alpha)}.
  \]
  Then $\lambda\in(0,1)$, and every function $X:\Omega\to\mathbb R$ satisfying
  \[
    \sum_{x\in\Omega}\mu(x)X(x)=0
    \quad\text{and}\quad
    -1\leq X(x)\leq\alpha\qquad(x\in\Omega)
  \]
  obeys
  \[
    \|1+\rho X\|_{L^\infty(\mu)}
      \leq\|1+X\|_{L^\infty(\mu)}^\lambda.
  \]
  Equality holds if and only if $X$ is the zero function or $X(x)\in\{-1,\alpha\}$ for every $x\in\Omega$. -/)
  (proof := /-- The parameter in
  \cref{lem:bounded-mean-zero-sup-scalar-comparison} is the displayed
  logarithmic ratio and belongs to $(0,1)$.  Since a probability
  mass function has nonempty support, the finite function $X$ attains a
  maximum $\beta$.  Full support, as in \cref{def:full-support-pmf}, makes
  every singleton have positive measure.  The essential-supremum formula
  in \cref{def:weighted-lp-norm} therefore gives
  \[
    \|1+sX\|_{L^\infty(\mu)}=1+s\beta
    \qquad(0\leq s\leq1).
  \]
  The pointwise lower bound and the zero-mean identity from
  \cref{def:one-coordinate-mean} imply $\beta\geq0$, while the upper bound
  gives $\beta\leq\alpha$.  Applying the scalar comparison at $\beta$
  proves the norm inequality.

  It remains to identify equality.  The scalar comparison says that it can
  occur only when $\beta=0$ or $\beta=\alpha$.  If $\beta=0$, every summand
  $\mu(x)X(x)$ is nonpositive, and their sum is zero; full support forces
  every summand, and hence every $X(x)$, to vanish.  If $\beta=\alpha$, let
  $x_\beta$ attain the maximum.  The nonnegative quantities
  $\mu(x)(X(x)+1)$ sum to $1$, whereas the atom bound gives
  \[
    \mu(x_\beta)(X(x_\beta)+1)
      =\mu(x_\beta)(1+\alpha)\geq1.
  \]
  Thus all remaining terms vanish, so $X(x)=-1$ away from $x_\beta$ and
  every value belongs to $\{-1,\alpha\}$.  Conversely, the zero function
  has $\beta=0$.  An endpoint-valued centered function cannot be constantly
  $-1$, so it assumes the value $\alpha$ and has $\beta=\alpha$; the scalar
  equality characterization then proves equality of the two norms. -/)
  (title := /-- Sharp essential-supremum comparison for bounded centered laws -/)
  (latexEnv := "lemma")]
lemma bounded_mean_zero_sup_comparison {Ω : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : PMF Ω) (ρ α : ℝ)
    (hμ : full_support_pmf μ) (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1)
    (hα : 0 < α)
    (hatom : ∀ x, 1 / (1 + α) ≤ (μ x).toReal) :
    0 < Real.log (1 + ρ * α) / Real.log (1 + α) ∧
      Real.log (1 + ρ * α) / Real.log (1 + α) < 1 ∧
      ∀ X : Ω → ℝ, one_coordinate_mean μ X = 0 →
        (∀ x, -1 ≤ X x ∧ X x ≤ α) →
        weighted_lp_norm μ.toMeasure ⊤ (fun x ↦ 1 + ρ * X x) ≤
            ENNReal.rpow
              (weighted_lp_norm μ.toMeasure ⊤ (fun x ↦ 1 + X x))
              (Real.log (1 + ρ * α) / Real.log (1 + α)) ∧
          (weighted_lp_norm μ.toMeasure ⊤ (fun x ↦ 1 + ρ * X x) =
              ENNReal.rpow
                (weighted_lp_norm μ.toMeasure ⊤ (fun x ↦ 1 + X x))
                (Real.log (1 + ρ * α) / Real.log (1 + α)) ↔
            X = (fun _ ↦ 0) ∨ ∀ x, X x = -1 ∨ X x = α) := by
  classical
  letI : Nonempty Ω := μ.support_nonempty.to_type
  obtain ⟨hlam₀, hlam₁, hscalar⟩ :=
    bounded_mean_zero_sup_scalar_comparison ρ α hρ₀ hρ₁ hα
  refine ⟨hlam₀, hlam₁, ?_⟩
  intro X hmean hbounds
  obtain ⟨xβ, hxβ⟩ := Finite.exists_max X
  let β := X xβ
  have hp (x : Ω) : 0 < (μ x).toReal := by
    exact ENNReal.toReal_pos (hμ x)
      (ne_of_lt ((PMF.coe_le_one μ x).trans_lt ENNReal.one_lt_top))
  have hnotop (x : Ω) : μ x ≠ ⊤ := by
    exact ne_of_lt ((PMF.coe_le_one μ x).trans_lt ENNReal.one_lt_top)
  have hmassENN : ∑ x, μ x = 1 := by
    simpa only [tsum_fintype] using PMF.tsum_coe μ
  have hmass : ∑ x, (μ x).toReal = 1 := by
    calc
      ∑ x, (μ x).toReal = ENNReal.toReal (∑ x, μ x) := by
        simpa using
          (ENNReal.toReal_sum (s := Finset.univ)
            (f := fun x ↦ μ x) (fun x hx ↦ hnotop x)).symm
      _ = 1 := by rw [hmassENN]; simp
  have hmean' : ∑ x, (μ x).toReal * X x = 0 := by
    simpa [one_coordinate_mean] using hmean
  have hβ₀ : 0 ≤ β := by
    by_contra hβ
    have hsumneg : ∑ x, (μ x).toReal * X x < 0 := by
      apply Fintype.sum_neg
      refine lt_of_le_of_ne ?_ ?_
      · intro x
        exact (mul_neg_of_pos_of_neg (hp x)
          (lt_of_le_of_lt (hxβ x) (lt_of_not_ge hβ))).le
      · intro heq
        have hxβzero := congrFun heq xβ
        simp only [Pi.zero_apply] at hxβzero
        exact (ne_of_lt (mul_neg_of_pos_of_neg (hp xβ)
          (lt_of_le_of_lt (hxβ xβ) (lt_of_not_ge hβ)))) hxβzero
    linarith
  have hβα : β ≤ α := (hbounds xβ).2
  have hsingleton (x : Ω) : μ.toMeasure {x} ≠ 0 := by
    rw [μ.toMeasure_apply_singleton x (MeasurableSet.singleton x)]
    exact hμ x
  have hnorm (s : ℝ) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
      weighted_lp_norm μ.toMeasure ⊤ (fun x ↦ 1 + s * X x) =
        ENNReal.ofReal (1 + s * β) := by
    rw [weighted_lp_norm, eLpNorm_exponent_top, eLpNormEssSup,
      essSup_eq_iSup hsingleton]
    apply le_antisymm
    · refine iSup_le fun x ↦ ?_
      have hxnonneg : 0 ≤ 1 + s * X x := by
        have := mul_le_mul_of_nonneg_left (hbounds x).1 hs₀
        nlinarith
      rw [Real.enorm_eq_ofReal hxnonneg]
      exact ENNReal.ofReal_le_ofReal (by
        simpa [β, add_comm] using
          (add_le_add_left (mul_le_mul_of_nonneg_left (hxβ x) hs₀) 1))
    · calc
        ENNReal.ofReal (1 + s * β) = ‖1 + s * X xβ‖ₑ := by
          exact (Real.enorm_eq_ofReal (by positivity)).symm
        _ ≤ ⨆ x, ‖1 + s * X x‖ₑ := le_iSup (fun x ↦ ‖1 + s * X x‖ₑ) xβ
  have hbasepos : 0 < 1 + β := by linarith
  have hscalarβ := hscalar β hβ₀ hβα
  have hnorm_one :
      weighted_lp_norm μ.toMeasure ⊤ (fun x ↦ 1 + X x) =
        ENNReal.ofReal (1 + β) := by
    simpa using hnorm 1 zero_le_one le_rfl
  rw [hnorm ρ hρ₀.le hρ₁.le, hnorm_one, ENNReal.rpow_eq_pow,
    ENNReal.ofReal_rpow_of_pos hbasepos]
  constructor
  · exact ENNReal.ofReal_le_ofReal hscalarβ.1
  · rw [ENNReal.ofReal_eq_ofReal_iff (by positivity)
      (Real.rpow_nonneg hbasepos.le _)]
    constructor
    · intro heq
      rcases hscalarβ.2.mp heq with hβzero | hβαeq
      · left
        funext x
        have hxnonpos : X x ≤ 0 := by simpa [β, hβzero] using hxβ x
        have hterms : (fun y ↦ (μ y).toReal * X y) ≤ 0 := by
          intro y
          exact mul_nonpos_of_nonneg_of_nonpos (hp y).le
            (by simpa [β, hβzero] using hxβ y)
        have hz := (Fintype.sum_eq_zero_iff_of_nonpos hterms).mp hmean'
        have hzx := congrFun hz x
        simp only [Pi.zero_apply] at hzx
        exact (mul_eq_zero.mp hzx).resolve_left (ne_of_gt (hp x))
      · right
        have hβvalue : X xβ = α := by simpa [β] using hβαeq
        have hterm_nonneg (x : Ω) :
            0 ≤ (μ x).toReal * (X x + 1) := by
          exact mul_nonneg (hp x).le (by linarith [(hbounds x).1])
        have hterm_sum : ∑ x, (μ x).toReal * (X x + 1) = 1 := by
          calc
            ∑ x, (μ x).toReal * (X x + 1) =
                (∑ x, (μ x).toReal * X x) + ∑ x, (μ x).toReal := by
                  simp only [mul_add, mul_one, Finset.sum_add_distrib]
            _ = 1 := by rw [hmean', hmass]; norm_num
        have hxβlarge : 1 ≤ (μ xβ).toReal * (X xβ + 1) := by
          rw [hβvalue]
          calc
            1 = (1 / (1 + α)) * (α + 1) := by
              field_simp [ne_of_gt (by linarith : 0 < 1 + α)]
              <;> ring
            _ ≤ (μ xβ).toReal * (α + 1) := by
              exact mul_le_mul_of_nonneg_right (hatom xβ) (by linarith)
        intro x
        by_cases hx : x = xβ
        · right
          simpa [hx] using hβvalue
        · left
          have hrest_nonneg :
              0 ≤ ∑ y ∈ Finset.univ.erase xβ, (μ y).toReal * (X y + 1) := by
            exact Finset.sum_nonneg fun y hy ↦ hterm_nonneg y
          have hrest_zero :
              ∑ y ∈ Finset.univ.erase xβ, (μ y).toReal * (X y + 1) = 0 := by
            have hsplit := Finset.sum_erase_add Finset.univ
              (fun y ↦ (μ y).toReal * (X y + 1)) (Finset.mem_univ xβ)
            rw [hterm_sum] at hsplit
            linarith
          have hzero := (Finset.sum_eq_zero_iff_of_nonneg
            (fun y hy ↦ hterm_nonneg y)).mp hrest_zero x (by simp [hx])
          have hxplus : X x + 1 = 0 :=
            (mul_eq_zero.mp hzero).resolve_left (ne_of_gt (hp x))
          linarith
    · intro hcase
      apply hscalarβ.2.mpr
      rcases hcase with hzero | hend
      · left
        simpa [β, hzero]
      · right
        rcases hend xβ with hleft | hright
        · exfalso
          rw [show β = -1 by simpa [β] using hleft] at hβ₀
          norm_num at hβ₀
        · simpa [β] using hright

@[blueprint "lem:one-coordinate-extremal-parameter-exists"
  (statement := /-- Let $\Omega$ be a finite measurable space whose
  singleton sets are measurable and whose equality is decidable, and let
  $\mu$ be a full-support probability mass function on $\Omega$.  Put
  $\mu^*=\min_{x\in\Omega}\mu(x)$, let $q\in[2,\infty]$, and let
  $\rho\in(0,1)$.  Then the canonical value
  \[
    \lambda=\lambda(q,\mu^*,\rho)
  \]
  from \cref{def:optimal-samorodnitsky-parameter} has the one-coordinate
  extremal Samorodnitsky property with respect to $\mu$, $q$, and
  $\rho$. -/)
  (proof := /-- We use the notions in
  \cref{def:full-support-pmf,def:one-coordinate-mean,def:one-coordinate-noise,def:weighted-lp-norm,def:minimum-mass-spike,def:one-coordinate-extremal-property,def:minimum-atom-mass,def:optimal-samorodnitsky-parameter}.
  The real weights of the atoms of $\mu$ sum to one.  If $\Omega$ is a
  singleton, then $\mu^*=1$ and the canonical convention gives
  $\lambda=1/2$.  Every nonnegative function is constant, the noise
  operator fixes it, and both sides of the asserted inequality are equal
  by homogeneity of the norm.

  Suppose now that $\Omega$ has at least two points.  Choose $x_0$ whose
  atom has minimum real mass, and write
  \[
    p=\mu(x_0),\qquad \alpha=p^{-1}-1.
  \]
  Full support gives $p>0$.  Comparing with two distinct positive-mass
  atoms gives $p<1$, hence $\alpha>0$, and minimality gives
  $(1+\alpha)^{-1}=p\leq\mu(x)$ for every $x$.  If $q<\infty$, apply
  \cref{lem:bounded-mean-zero-moment-comparison}; if $q=\infty$, apply
  \cref{lem:bounded-mean-zero-sup-comparison}.  Their displayed
  parameters are exactly the corresponding branches of
  $\lambda(q,\mu^*,\rho)$ in
  \cref{def:optimal-samorodnitsky-parameter}.  Thus this canonical
  $\lambda$ belongs to $(0,1)$, and every centered $X$ with
  $-1\leq X\leq\alpha$ satisfies
  \[
    \|1+\rho X\|_{L^q(\mu)}
      \leq \|1+X\|_{L^q(\mu)}^\lambda,
  \]
  with equality exactly when $X=0$ or each value of $X$ belongs to
  $\{-1,\alpha\}$.

  Let $f:\Omega\to\mathbb R$ be nonnegative and put
  $m=\mathbb E_\mu f$.  If $m=0$, positivity of every atom forces $f=0$,
  and the desired inequality is an equality.  If $m>0$, set
  $X=f/m-1$.  Then $\mathbb E_\mu X=0$ and $X\geq-1$.  Moreover,
  \[
    \mu(x)f(x)\leq m,qquad p\leq\mu(x),
  \]
  so $X(x)\leq p^{-1}-1=\alpha$.  Applying the preceding comparison and
  using the homogeneity of the noise operator and the $L^q$ norm gives
  the required inequality.  The identity
  $\|f\|_{L^1(\mu)}=m$ used in this rescaling is the case $q=1$ of
  \cref{lem:weighted-lp-norm-finite-moment}.

  It remains to transport the equality cases through normalization.  The
  alternative $X=0$ is equivalent to $f$ being a nonnegative constant.
  In the endpoint-valued alternative, some point $x^*$ has
  $X(x^*)=\alpha$, since otherwise the mean of $X$ would be $-1$.  The
  nonnegative summands in
  \[
    \sum_x\mu(x)(X(x)+1)=1
  \]
  show first that $\mu(x^*)=p$ and then that $X(x)=-1$ for every
  $x\ne x^*$.  Thus $f$ is a nonnegative multiple of the indicator of a
  minimum-mass point.  Conversely, a nonzero minimum-mass spike
  normalizes to the values $\alpha$ at its supporting point and $-1$
  elsewhere, while the zero spike was already covered by the constant
  case.  These are precisely the equality cases in
  \cref{def:one-coordinate-extremal-property}. -/)
  (title := /-- Existence of the one-coordinate extremal parameter -/)
  (latexEnv := "lemma")]
lemma one_coordinate_extremal_parameter_exists {Ω : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [DecidableEq Ω] (μ : PMF Ω) (q : ℝ≥0∞) (ρ : ℝ)
    (hμ : full_support_pmf μ) (hq : (2 : ℝ≥0∞) ≤ q)
    (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) :
    one_coordinate_extremal_property μ q ρ
      (optimal_samorodnitsky_parameter q (minimum_atom_mass μ) ρ) := by
  classical
  letI : Nonempty Ω := μ.support_nonempty.to_type
  obtain ⟨x₀, hx₀mem, hx₀⟩ :=
    Finset.exists_min_image (Finset.univ : Finset Ω)
      (fun x ↦ (μ x).toReal) Finset.univ_nonempty
  have hmin (x : Ω) : (μ x₀).toReal ≤ (μ x).toReal :=
    hx₀ x (Finset.mem_univ x)
  let p : ℝ := (μ x₀).toReal
  have hnotop (x : Ω) : μ x ≠ ⊤ :=
    ne_of_lt ((PMF.coe_le_one μ x).trans_lt ENNReal.one_lt_top)
  have hp₀ : 0 < p := ENNReal.toReal_pos (hμ x₀) (hnotop x₀)
  have hp₁ : p ≤ 1 := by
    simpa [p] using ENNReal.toReal_mono (by simp) (PMF.coe_le_one μ x₀)
  have hmassENN : ∑ x, μ x = 1 := by
    simpa only [tsum_fintype] using PMF.tsum_coe μ
  have hmass : ∑ x, (μ x).toReal = 1 := by
    calc
      ∑ x, (μ x).toReal = ENNReal.toReal (∑ x, μ x) := by
        simpa using
          (ENNReal.toReal_sum (s := Finset.univ) (f := fun x ↦ μ x)
            (fun x hx ↦ hnotop x)).symm
      _ = 1 := by rw [hmassENN]; norm_num
  have hpmin : minimum_atom_mass μ = p := by
    unfold minimum_atom_mass
    apply le_antisymm
    · exact csInf_le
        ⟨0, by rintro _ ⟨x, rfl⟩; exact ENNReal.toReal_nonneg⟩
        ⟨x₀, rfl⟩
    · exact le_csInf (Set.range_nonempty _)
        (by rintro _ ⟨x, rfl⟩; exact hmin x)
  rw [hpmin]
  let lam := optimal_samorodnitsky_parameter q p ρ
  change one_coordinate_extremal_property μ q ρ lam
  unfold one_coordinate_extremal_property
  by_cases hp_one : p = 1
  · have hμx₀ : μ x₀ = 1 := by
      exact (ENNReal.toReal_eq_one_iff (μ x₀)).mp (by simpa [p] using hp_one)
    have hsupp : μ.support = {x₀} :=
      (PMF.apply_eq_one_iff μ x₀).mp hμx₀
    have hsub (x : Ω) : x = x₀ := by
      have hxmem : x ∈ μ.support :=
        (μ.mem_support_iff x).2 (hμ x)
      rw [hsupp] at hxmem
      simpa using hxmem
    have hlam : lam = 1 / 2 := by
      simp [lam, optimal_samorodnitsky_parameter, hp_one]
    refine ⟨by rw [hlam]; norm_num, by rw [hlam]; norm_num, ?_⟩
    intro f hf
    dsimp only
    have hfconst : f = fun _ ↦ f x₀ := by
      funext x
      rw [hsub x]
    have hmean : one_coordinate_mean μ f = f x₀ := by
      rw [hfconst]
      simp only [one_coordinate_mean]
      rw [← Finset.sum_mul, hmass, one_mul]
    have hnoise : one_coordinate_noise μ ρ f = f := by
      funext x
      rw [one_coordinate_noise, hmean, hfconst]
      ring
    have hq₀ : q ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le (by norm_num) hq)
    have hnorm (r : ℝ≥0∞) (hr : r ≠ 0) :
        weighted_lp_norm μ.toMeasure r f = ENNReal.ofReal (f x₀) := by
      have hmeasure : μ.toMeasure ≠ 0 := by
        intro hz
        have hx := μ.toMeasure_apply_singleton x₀
          (MeasurableSet.singleton x₀)
        simp [hz, hμx₀] at hx
      rw [hfconst]
      rw [weighted_lp_norm, eLpNorm_const (f x₀) hr hmeasure]
      simp [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hf x₀)]
    have hpow :
        ENNReal.rpow (ENNReal.ofReal (f x₀)) (1 - (1 / 2 : ℝ)) *
            ENNReal.rpow (ENNReal.ofReal (f x₀)) (1 / 2 : ℝ) =
          ENNReal.ofReal (f x₀) := by
      by_cases hc : f x₀ = 0
      · simp [hc]
      · calc
          _ = ENNReal.rpow (ENNReal.ofReal (f x₀))
                ((1 - (1 / 2 : ℝ)) + (1 / 2 : ℝ)) :=
              (ENNReal.rpow_add _ _
                (ne_of_gt (ENNReal.ofReal_pos.mpr
                  (lt_of_le_of_ne (hf x₀) (Ne.symm hc))))
                ENNReal.ofReal_ne_top).symm
          _ = ENNReal.ofReal (f x₀) := by norm_num
    have heq :
        weighted_lp_norm μ.toMeasure q (one_coordinate_noise μ ρ f) =
          ENNReal.rpow (weighted_lp_norm μ.toMeasure 1 f)
              (1 - (1 / 2 : ℝ)) *
            ENNReal.rpow (weighted_lp_norm μ.toMeasure q f) (1 / 2 : ℝ) := by
      rw [hnoise, hnorm q hq₀, hnorm 1 (by norm_num), hpow]
    rw [hlam]
    refine ⟨heq.le, ?_⟩
    constructor
    · intro h
      exact Or.inl ⟨f x₀, hf x₀, hfconst⟩
    · intro h
      exact heq
  · have hp₁' : p < 1 := lt_of_le_of_ne hp₁ hp_one
    let α : ℝ := 1 / p - 1
    have hα : 0 < α := by
      have hinv : 1 < 1 / p := by
        rw [lt_div_iff₀ hp₀]
        simpa using hp₁'
      simpa [α] using sub_pos.mpr hinv
    have halpha : 1 / (1 + α) = p := by
      dsimp [α]
      field_simp [ne_of_gt hp₀]
      ring
    have halpha' : α + 1 = 1 / p := by
      dsimp [α]
      ring
    have hatom (x : Ω) : 1 / (1 + α) ≤ (μ x).toReal := by
      rw [halpha]
      exact hmin x
    obtain ⟨hlam₀, hlam₁, hcomparison⟩ :
        0 < lam ∧ lam < 1 ∧
          ∀ X : Ω → ℝ, one_coordinate_mean μ X = 0 →
            (∀ x, -1 ≤ X x ∧ X x ≤ α) →
            weighted_lp_norm μ.toMeasure q (fun x ↦ 1 + ρ * X x) ≤
                ENNReal.rpow
                  (weighted_lp_norm μ.toMeasure q (fun x ↦ 1 + X x)) lam ∧
              (weighted_lp_norm μ.toMeasure q (fun x ↦ 1 + ρ * X x) =
                  ENNReal.rpow
                    (weighted_lp_norm μ.toMeasure q (fun x ↦ 1 + X x)) lam ↔
                X = (fun _ ↦ 0) ∨ ∀ x, X x = -1 ∨ X x = α) := by
      by_cases hqtop : q = ⊤
      · subst q
        simpa [lam, optimal_samorodnitsky_parameter, hp_one, α] using
          bounded_mean_zero_sup_comparison μ ρ α hμ hρ₀ hρ₁ hα hatom
      · simpa [lam, optimal_samorodnitsky_parameter, hp_one, hqtop, α] using
          bounded_mean_zero_moment_comparison μ q ρ α hμ hq hqtop
            hρ₀ hρ₁ hα
    refine ⟨hlam₀, hlam₁, ?_⟩
    intro f hf
    dsimp only
    let m : ℝ := one_coordinate_mean μ f
    have hm₀ : 0 ≤ m := by
      dsimp [m, one_coordinate_mean]
      exact Finset.sum_nonneg fun x hx ↦
        mul_nonneg ENNReal.toReal_nonneg (hf x)
    by_cases hmzero : m = 0
    · have hsumzero :
          ∑ x, (μ x).toReal * f x = 0 := by
        simpa [m, one_coordinate_mean] using hmzero
      have hfzero : f = fun _ ↦ 0 := by
        funext x
        have hterm :
            (μ x).toReal * f x = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun y hy ↦ mul_nonneg ENNReal.toReal_nonneg (hf y))).mp
              hsumzero x (Finset.mem_univ x)
        exact (mul_eq_zero.mp hterm).resolve_left
          (ne_of_gt (ENNReal.toReal_pos (hμ x) (hnotop x)))
      rw [hfzero]
      have hnoisezero :
          one_coordinate_noise μ ρ (fun _ : Ω ↦ 0) = fun _ ↦ 0 := by
        funext x
        simp [one_coordinate_noise, one_coordinate_mean]
      have hnormzero (r : ℝ≥0∞) :
          weighted_lp_norm μ.toMeasure r (fun _ : Ω ↦ 0) = 0 := by
        simp [weighted_lp_norm]
      have hz₁ : ENNReal.rpow 0 (1 - lam) = 0 :=
        ENNReal.zero_rpow_of_pos (sub_pos.mpr hlam₁)
      have hzq : ENNReal.rpow 0 lam = 0 :=
        ENNReal.zero_rpow_of_pos hlam₀
      rw [hnoisezero, hnormzero q, hnormzero 1, hz₁, hzq]
      exact ⟨by simp, iff_of_true (by simp) (Or.inl ⟨0, le_rfl, rfl⟩)⟩
    · have hmpos : 0 < m := lt_of_le_of_ne hm₀ (Ne.symm hmzero)
      let X : Ω → ℝ := fun x ↦ f x / m - 1
      have hmeanX : one_coordinate_mean μ X = 0 := by
        dsimp [one_coordinate_mean, X]
        calc
          ∑ x, (μ x).toReal * (f x / m - 1) =
              (∑ x, (μ x).toReal * f x) / m -
                ∑ x, (μ x).toReal := by
                  have hterm (x : Ω) :
                      (μ x).toReal * (f x / m - 1) =
                        (μ x).toReal * f x / m - (μ x).toReal := by
                    ring
                  rw [Finset.sum_congr rfl (fun x hx ↦ hterm x)]
                  rw [Finset.sum_sub_distrib, Finset.sum_div]
          _ = m / m - 1 := by
            rw [show ∑ x, (μ x).toReal * f x = m by
              rfl, hmass]
          _ = 0 := by field_simp [ne_of_gt hmpos]
                       <;> ring
      have hterm_le (x : Ω) : (μ x).toReal * f x ≤ m := by
        change (μ x).toReal * f x ≤
          ∑ y, (μ y).toReal * f y
        exact Finset.single_le_sum
          (fun y hy ↦ mul_nonneg ENNReal.toReal_nonneg (hf y))
          (Finset.mem_univ x)
      have hbounds (x : Ω) : -1 ≤ X x ∧ X x ≤ α := by
        constructor
        · dsimp [X]
          have := div_nonneg (hf x) hmpos.le
          linarith
        · have hpf : p * f x ≤ m := by
            calc
              p * f x ≤ (μ x).toReal * f x :=
                mul_le_mul_of_nonneg_right (hmin x) (hf x)
              _ ≤ m := hterm_le x
          have hratio : f x / m ≤ 1 / p := by
            rw [div_le_div_iff₀ hmpos hp₀]
            nlinarith
          dsimp [X, α]
          linarith
      obtain ⟨hineqX, heqX⟩ := hcomparison X hmeanX hbounds
      have hf_repr : (fun x ↦ m * (1 + X x)) = f := by
        funext x
        dsimp [X]
        field_simp [ne_of_gt hmpos]
        ring
      have hnoise_repr :
          one_coordinate_noise μ ρ f =
            fun x ↦ m * (1 + ρ * X x) := by
        funext x
        rw [one_coordinate_noise, show one_coordinate_mean μ f = m by rfl]
        dsimp [X]
        field_simp [ne_of_gt hmpos]
        ring
      have hscale (g : Ω → ℝ) (r : ℝ≥0∞) :
          weighted_lp_norm μ.toMeasure r (fun x ↦ m * g x) =
            ENNReal.ofReal m * weighted_lp_norm μ.toMeasure r g := by
        unfold weighted_lp_norm
        rw [show (fun x ↦ m * g x) = m • g by rfl,
          eLpNorm_const_smul]
        simp [Real.enorm_eq_ofReal_abs, abs_of_nonneg hmpos.le]
      have hnormone :
          weighted_lp_norm μ.toMeasure 1 f = ENNReal.ofReal m := by
        have habs :
            ∑ x, (μ x).toReal * |f x| = m := by
          dsimp [m, one_coordinate_mean]
          apply Finset.sum_congr rfl
          intro x hx
          rw [abs_of_nonneg (hf x)]
        simpa [habs] using
          weighted_lp_norm_finite_moment μ 1 f (by norm_num) (by norm_num)
      have hnormf :
          weighted_lp_norm μ.toMeasure q f =
            ENNReal.ofReal m *
              weighted_lp_norm μ.toMeasure q (fun x ↦ 1 + X x) := by
        rw [← hf_repr]
        exact hscale (fun x ↦ 1 + X x) q
      have hnormnoise :
          weighted_lp_norm μ.toMeasure q (one_coordinate_noise μ ρ f) =
            ENNReal.ofReal m *
              weighted_lp_norm μ.toMeasure q (fun x ↦ 1 + ρ * X x) := by
        rw [hnoise_repr]
        exact hscale (fun x ↦ 1 + ρ * X x) q
      have hM₀ : ENNReal.ofReal m ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr hmpos)
      have hMtop : ENNReal.ofReal m ≠ ⊤ := ENNReal.ofReal_ne_top
      have hfactor (B : ℝ≥0∞) :
          ENNReal.rpow (ENNReal.ofReal m) (1 - lam) *
              ENNReal.rpow (ENNReal.ofReal m * B) lam =
            ENNReal.ofReal m * ENNReal.rpow B lam := by
        calc
          _ = ENNReal.rpow (ENNReal.ofReal m) (1 - lam) *
                (ENNReal.rpow (ENNReal.ofReal m) lam *
                  ENNReal.rpow B lam) := by
              congr 1
              exact ENNReal.mul_rpow_of_nonneg _ _ hlam₀.le
          _ = (ENNReal.rpow (ENNReal.ofReal m) (1 - lam) *
                ENNReal.rpow (ENNReal.ofReal m) lam) *
                  ENNReal.rpow B lam := by ac_rfl
          _ = ENNReal.rpow (ENNReal.ofReal m) ((1 - lam) + lam) *
                  ENNReal.rpow B lam := by
              congr 1
              exact (ENNReal.rpow_add _ _ hM₀ hMtop).symm
          _ = ENNReal.ofReal m * ENNReal.rpow B lam := by
              norm_num
      rw [hnormnoise, hnormone, hnormf, hfactor]
      refine ⟨mul_le_mul_left' hineqX _, ?_⟩
      rw [ENNReal.mul_right_inj hM₀ hMtop, heqX]
      constructor
      · rintro (hXzero | hend)
        · left
          refine ⟨m, hmpos.le, ?_⟩
          rw [← hf_repr, hXzero]
          funext x
          ring
        · right
          have hex : ∃ xStar, X xStar = α := by
            by_contra hnone
            have hnone' (x : Ω) : X x ≠ α := by
              intro hx
              exact hnone ⟨x, hx⟩
            have hXneg : X = fun _ ↦ -1 := by
              funext x
              rcases hend x with hx | hx
              · exact hx
              · exact (hnone' x hx).elim
            rw [hXneg] at hmeanX
            simp [one_coordinate_mean, hmass] at hmeanX
          obtain ⟨xStar, hxStar⟩ := hex
          have hterm_nonneg (x : Ω) :
              0 ≤ (μ x).toReal * (X x + 1) :=
            mul_nonneg ENNReal.toReal_nonneg (by linarith [(hbounds x).1])
          have hterm_sum :
              ∑ x, (μ x).toReal * (X x + 1) = 1 := by
            calc
              ∑ x, (μ x).toReal * (X x + 1) =
                  (∑ x, (μ x).toReal * X x) +
                    ∑ x, (μ x).toReal := by
                      simp only [mul_add, mul_one, Finset.sum_add_distrib]
              _ = 1 := by
                have hmeanX' : ∑ x, (μ x).toReal * X x = 0 := by
                  simpa [one_coordinate_mean] using hmeanX
                rw [hmeanX', hmass]
                norm_num
          have hxlarge :
              1 ≤ (μ xStar).toReal * (X xStar + 1) := by
            rw [hxStar, halpha']
            have hle : 1 ≤ (μ xStar).toReal / p :=
              (le_div_iff₀ hp₀).2 (by simpa [p] using hmin xStar)
            simpa [div_eq_mul_inv, mul_comm] using hle
          have hrest_zero :
              ∑ x ∈ Finset.univ.erase xStar,
                  (μ x).toReal * (X x + 1) = 0 := by
            have hsplit := Finset.sum_erase_add Finset.univ
              (fun x ↦ (μ x).toReal * (X x + 1))
              (Finset.mem_univ xStar)
            rw [hterm_sum] at hsplit
            have hrest_nonneg :
                0 ≤ ∑ x ∈ Finset.univ.erase xStar,
                  (μ x).toReal * (X x + 1) :=
              Finset.sum_nonneg fun x hx ↦ hterm_nonneg x
            linarith
          have hoff (x : Ω) (hx : x ≠ xStar) : X x = -1 := by
            have hzero :=
              (Finset.sum_eq_zero_iff_of_nonneg
                (fun y hy ↦ hterm_nonneg y)).mp hrest_zero x (by simp [hx])
            have hxplus : X x + 1 = 0 :=
              (mul_eq_zero.mp hzero).resolve_left
                (ne_of_gt (ENNReal.toReal_pos (hμ x) (hnotop x)))
            linarith
          have hxmass : (μ xStar).toReal = p := by
            have hxle :
                (μ xStar).toReal * (X xStar + 1) ≤ 1 := by
              have hsingle := Finset.single_le_sum
                (fun x hx ↦ hterm_nonneg x) (Finset.mem_univ xStar)
              simpa [hterm_sum] using hsingle
            rw [hxStar, halpha'] at hxle
            have hdiv : (μ xStar).toReal / p ≤ 1 := by
              simpa [div_eq_mul_inv] using hxle
            have : (μ xStar).toReal ≤ p := by
              simpa using (div_le_iff₀ hp₀).mp hdiv
            exact le_antisymm this (hmin xStar)
          refine ⟨m / p, div_nonneg hmpos.le hp₀.le, xStar, ?_, ?_⟩
          · intro y
            exact (ENNReal.toReal_le_toReal (hnotop xStar) (hnotop y)).mp
              (hxmass.trans_le (hmin y))
          · rw [← hf_repr]
            funext x
            by_cases hx : x = xStar
            · subst x
              simp only [if_pos]
              rw [hxStar, add_comm 1 α, halpha']
              simp [div_eq_mul_inv]
            · simp [hx, hoff x hx]
      · rintro (⟨c, hc, hfconst⟩ | ⟨c, hc, xStar, hxminimal, hfspike⟩)
        · left
          funext x
          dsimp [X]
          have hmconst : m = c := by
            dsimp [m, one_coordinate_mean]
            rw [hfconst]
            rw [← Finset.sum_mul, hmass, one_mul]
          rw [hfconst, hmconst]
          have hcpos : 0 < c := by simpa [hmconst] using hmpos
          field_simp [ne_of_gt hcpos]
          ring
        · right
          have hcpos : 0 < c := by
            have hcne : c ≠ 0 := by
              intro hc0
              have hfzero' : f = fun _ ↦ 0 := by
                rw [hfspike, hc0]
                simp
              have hmzero' : m = 0 := by
                dsimp [m, one_coordinate_mean]
                rw [hfzero']
                simp
              exact hmzero hmzero'
            exact lt_of_le_of_ne hc (Ne.symm hcne)
          have hxreal : (μ xStar).toReal = p := by
            apply le_antisymm
            · exact (ENNReal.toReal_le_toReal (hnotop xStar) (hnotop x₀)).mpr
                (hxminimal x₀)
            · exact hmin xStar
          have hmspike : m = p * c := by
            dsimp [m, one_coordinate_mean]
            rw [hfspike]
            simp [hxreal]
          intro x
          by_cases hx : x = xStar
          · right
            subst x
            dsimp [X, α]
            rw [hfspike, hmspike]
            simp [ne_of_gt hp₀, ne_of_gt hcpos]
            field_simp [ne_of_gt hp₀, ne_of_gt hcpos]
          · left
            dsimp [X]
            simp [hfspike, hx]

@[blueprint "lem:finite-weighted-geometric-mean"
  (statement := /-- Let $I$ be finite, let $w_i,A_i,B_i$ be extended
  nonnegative reals, and let $0<\lambda<1$.  Then
  \[
    \sum_i w_i A_i^{1-\lambda}B_i^\lambda
    \leq
    \left(\sum_i w_iA_i\right)^{1-\lambda}
    \left(\sum_i w_iB_i\right)^\lambda.
  \] -/)
  (proof := /-- Apply Hölder's inequality with conjugate exponents
  $(1-\lambda)^{-1}$ and $\lambda^{-1}$ to the sequences
  $(w_iA_i)^{1-\lambda}$ and $(w_iB_i)^\lambda$.  The laws for
  nonnegative real powers and $(1-\lambda)+\lambda=1$ identify the
  resulting expressions with the asserted ones. -/)
  (title := /-- Weighted geometric-mean inequality for finite sums -/)
  (latexEnv := "lemma")]
lemma finite_weighted_geometric_mean {ι : Type*} [Fintype ι]
    (w A B : ι → ℝ≥0∞) (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1) :
    ∑ i, w i * (ENNReal.rpow (A i) (1 - lam) * ENNReal.rpow (B i) lam) ≤
      ENNReal.rpow (∑ i, w i * A i) (1 - lam) *
        ENNReal.rpow (∑ i, w i * B i) lam := by
  classical
  let p : ℝ := (1 - lam)⁻¹
  let r : ℝ := lam⁻¹
  have hleft : 0 < 1 - lam := sub_pos.mpr hlam₁
  have hpq : Real.HolderConjugate p r := by
    exact Real.HolderConjugate.inv_inv hleft hlam₀ (by ring)
  have hholder := ENNReal.inner_le_Lp_mul_Lq
    (s := (Finset.univ : Finset ι))
    (f := fun i ↦ ENNReal.rpow (w i * A i) (1 - lam))
    (g := fun i ↦ ENNReal.rpow (w i * B i) lam) hpq
  calc
    ∑ i, w i * (ENNReal.rpow (A i) (1 - lam) * ENNReal.rpow (B i) lam) =
        ∑ i, ENNReal.rpow (w i * A i) (1 - lam) *
          ENNReal.rpow (w i * B i) lam := by
            apply Finset.sum_congr rfl
            intro i hi
            symm
            have hWA := ENNReal.mul_rpow_of_nonneg (w i) (A i) hleft.le
            have hWB := ENNReal.mul_rpow_of_nonneg (w i) (B i) hlam₀.le
            have hw := ENNReal.rpow_add_of_nonneg (x := w i)
              (1 - lam) lam hleft.le hlam₀.le
            change ENNReal.rpow (w i) ((1 - lam) + lam) =
              ENNReal.rpow (w i) (1 - lam) * ENNReal.rpow (w i) lam at hw
            simp only [ENNReal.rpow_eq_pow] at hw
            calc
              ENNReal.rpow (w i * A i) (1 - lam) *
                    ENNReal.rpow (w i * B i) lam =
                  (ENNReal.rpow (w i) (1 - lam) *
                      ENNReal.rpow (A i) (1 - lam)) *
                    (ENNReal.rpow (w i) lam * ENNReal.rpow (B i) lam) := by
                      exact congrArg₂ (· * ·) hWA hWB
              _ = (ENNReal.rpow (w i) (1 - lam) * ENNReal.rpow (w i) lam) *
                    (ENNReal.rpow (A i) (1 - lam) * ENNReal.rpow (B i) lam) := by
                      ac_rfl
              _ = w i *
                    (ENNReal.rpow (A i) (1 - lam) * ENNReal.rpow (B i) lam) := by
                      simp only [ENNReal.rpow_eq_pow]
                      rw [← hw]
                      have hsum : (1 - lam) + lam = 1 := by ring
                      rw [hsum, ENNReal.rpow_one]
    _ ≤ (∑ i, (ENNReal.rpow (w i * A i) (1 - lam)) ^ p) ^ (1 / p) *
          (∑ i, (ENNReal.rpow (w i * B i) lam) ^ r) ^ (1 / r) := hholder
    _ = ENNReal.rpow (∑ i, w i * A i) (1 - lam) *
          ENNReal.rpow (∑ i, w i * B i) lam := by
            have hp : (1 - lam) * p = 1 := by
              dsimp [p]
              field_simp [ne_of_gt hleft]
            have hr : lam * r = 1 := by
              dsimp [r]
              field_simp [ne_of_gt hlam₀]
            have hinvp : 1 / p = 1 - lam := by
              dsimp [p]
              field_simp [ne_of_gt hleft]
            have hinvr : 1 / r = lam := by
              dsimp [r]
              field_simp [ne_of_gt hlam₀]
            have hsumA :
                ∑ i, (ENNReal.rpow (w i * A i) (1 - lam)) ^ p =
                  ∑ i, w i * A i := by
              apply Finset.sum_congr rfl
              intro i hi
              change ENNReal.rpow (ENNReal.rpow (w i * A i) (1 - lam)) p =
                w i * A i
              simp only [ENNReal.rpow_eq_pow]
              have hpow := ENNReal.rpow_mul (w i * A i) (1 - lam) p
              rw [← hpow, hp, ENNReal.rpow_one]
            have hsumB :
                ∑ i, (ENNReal.rpow (w i * B i) lam) ^ r =
                  ∑ i, w i * B i := by
              apply Finset.sum_congr rfl
              intro i hi
              change ENNReal.rpow (ENNReal.rpow (w i * B i) lam) r =
                w i * B i
              simp only [ENNReal.rpow_eq_pow]
              have hpow := ENNReal.rpow_mul (w i * B i) lam r
              rw [← hpow, hr, ENNReal.rpow_one]
            rw [hinvp, hinvr]
            rw [hsumA, hsumB]
            rfl

@[blueprint "lem:weighted-lp-norm-product-finite"
  (statement := /-- Let $A$ and $B$ be finite measurable spaces with
  measurable singletons, let $\mu$ and $\nu$ be probability mass functions
  on them, and let $0<q<\infty$.  For every real-valued function $F$ on
  $B\times A$, its product-space $L^q$ norm satisfies
  \[
    \|F\|_{L^q(\nu\otimes\mu)}=
    \left(\sum_b\nu(b)\|F(b,\cdot)\|_{L^q(\mu)}^q\right)^{1/q}.
  \] -/)
  (proof := /-- Apply the finite-sum norm formula from
  \cref{lem:weighted-lp-norm-finite-moment} first to the product measure,
  viewed as its associated probability mass function, and then to every
  fiber.  The mass of the singleton $(b,a)$ is $\nu(b)\mu(a)$; rearranging
  the resulting finite sum and cancelling the reciprocal powers gives the
  displayed identity. -/)
  (title := /-- Finite product disintegration of the (L^q) norm -/)
  (latexEnv := "lemma")]
lemma weighted_lp_norm_product_finite {A B : Type*}
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (μ : PMF A) (ν : PMF B) (q : ℝ≥0∞) (F : B → A → ℝ)
    (hq₀ : q ≠ 0) (hqtop : q ≠ ⊤) :
    weighted_lp_norm (ν.toMeasure.prod μ.toMeasure) q
        (fun z ↦ F z.1 z.2) =
      ENNReal.rpow
        (∑ b, ν b * ENNReal.rpow
          (weighted_lp_norm μ.toMeasure q (F b)) q.toReal)
        (1 / q.toReal) := by
  classical
  let ξ : PMF (B × A) := (ν.toMeasure.prod μ.toMeasure).toPMF
  have hξmeasure : ξ.toMeasure = ν.toMeasure.prod μ.toMeasure := by
    simpa [ξ] using
      (Measure.toPMF_toMeasure (μ := ν.toMeasure.prod μ.toMeasure))
  rw [← hξmeasure, weighted_lp_norm_finite_moment ξ q
    (fun z ↦ F z.1 z.2) hq₀ hqtop]
  have hqreal : 0 < q.toReal := ENNReal.toReal_pos hq₀ hqtop
  have hinner (b : B) :
      ENNReal.rpow (weighted_lp_norm μ.toMeasure q (F b)) q.toReal =
        ENNReal.ofReal
          (∑ a, (μ a).toReal * Real.rpow (|F b a|) q.toReal) := by
    rw [weighted_lp_norm_finite_moment μ q (F b) hq₀ hqtop]
    simp only [ENNReal.rpow_eq_pow]
    rw [← ENNReal.rpow_mul]
    have hcancel : (1 / q.toReal) * q.toReal = 1 := by
      field_simp [ne_of_gt hqreal]
    rw [hcancel, ENNReal.rpow_one]
  congr 1
  rw [show (∑ b, ν b * ENNReal.rpow
      (weighted_lp_norm μ.toMeasure q (F b)) q.toReal) =
      ENNReal.ofReal
        (∑ b, (ν b).toReal *
          (∑ a, (μ a).toReal * Real.rpow (|F b a|) q.toReal)) by
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro b hb
      rw [hinner]
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (PMF.apply_ne_top ν b)]
    · intro b hb
      exact mul_nonneg ENNReal.toReal_nonneg
        (Finset.sum_nonneg fun a ha ↦ mul_nonneg ENNReal.toReal_nonneg
          (Real.rpow_nonneg (abs_nonneg _) _))]
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hmass : ξ (b, a) = ν b * μ a := by
    change (ν.toMeasure.prod μ.toMeasure) ({(b, a)} : Set (B × A)) =
      ν b * μ a
    rw [← Set.singleton_prod_singleton, Measure.prod_prod,
      ν.toMeasure_apply_singleton b (MeasurableSet.singleton b),
      μ.toMeasure_apply_singleton a (MeasurableSet.singleton a)]
  rw [hmass, ENNReal.toReal_mul]
  ring

@[blueprint "lem:weighted-lp-norm-product-top"
  (statement := /-- Let $A$ and $B$ be finite measurable spaces with
  measurable singletons, and let $\mu$ and $\nu$ be full-support
  probability mass functions.  For every real-valued function $F$ on
  $B\times A$,
  \[
    \|F\|_{L^\infty(\nu\otimes\mu)}
      =\sup_b\|F(b,\cdot)\|_{L^\infty(\mu)}.
  \] -/)
  (proof := /-- Full support makes every singleton have positive measure.
  Hence each essential supremum in
  \cref{def:weighted-lp-norm} is the supremum over all points.  The
  supremum over the product $B\times A$ is the iterated supremum over $b$
  and $a$, which is the asserted fiber formula. -/)
  (title := /-- Product disintegration of the essential-supremum norm -/)
  (latexEnv := "lemma")]
lemma weighted_lp_norm_product_top {A B : Type*}
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (μ : PMF A) (ν : PMF B) (hμ : full_support_pmf μ)
    (hν : full_support_pmf ν) (F : B → A → ℝ) :
    weighted_lp_norm (ν.toMeasure.prod μ.toMeasure) ⊤
        (fun z ↦ F z.1 z.2) =
      ⨆ b, weighted_lp_norm μ.toMeasure ⊤ (F b) := by
  classical
  have hprod (z : B × A) :
      (ν.toMeasure.prod μ.toMeasure) ({z} : Set (B × A)) ≠ 0 := by
    rcases z with ⟨b, a⟩
    rw [← Set.singleton_prod_singleton, Measure.prod_prod,
      ν.toMeasure_apply_singleton b (MeasurableSet.singleton b),
      μ.toMeasure_apply_singleton a (MeasurableSet.singleton a)]
    exact mul_ne_zero (hν b) (hμ a)
  rw [weighted_lp_norm, eLpNorm_exponent_top, eLpNormEssSup,
    essSup_eq_iSup hprod, iSup_prod]
  congr 1
  funext b
  rw [weighted_lp_norm, eLpNorm_exponent_top, eLpNormEssSup,
    essSup_eq_iSup (fun a ↦ by
      rw [μ.toMeasure_apply_singleton a (MeasurableSet.singleton a)]
      exact hμ a)]

@[blueprint "lem:one-coordinate-mean-constant-norm"
  (statement := /-- Let $\mu$ be a probability mass function on a finite
  measurable space with measurable singletons, let $q\ne0$, and let
  $f$ be nonnegative.  The $L^q(\mu)$ norm of the constant
  $\mathbb E_\mu f$ equals the $L^1(\mu)$ norm of $f$. -/)
  (proof := /-- By nonnegativity, the finite-sum formula
  \cref{lem:weighted-lp-norm-finite-moment} identifies the $L^1$ norm
  with $\mathbb E_\mu f$.  The norm of a constant on a probability space
  is its absolute value, which is the same nonnegative quantity. -/)
  (title := /-- Norm of a nonnegative function's mean -/)
  (latexEnv := "lemma")]
lemma one_coordinate_mean_constant_norm {A : Type*}
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : PMF A) (q : ℝ≥0∞) (f : A → ℝ) (hq₀ : q ≠ 0)
    (hf : ∀ a, 0 ≤ f a) :
    weighted_lp_norm μ.toMeasure q (fun _ ↦ one_coordinate_mean μ f) =
      weighted_lp_norm μ.toMeasure 1 f := by
  have hmean_nonneg : 0 ≤ one_coordinate_mean μ f := by
    exact Finset.sum_nonneg fun a ha ↦
      mul_nonneg ENNReal.toReal_nonneg (hf a)
  have hmass : μ.toMeasure Set.univ = 1 := by simp
  have hmeasure : μ.toMeasure ≠ 0 := by
    exact IsProbabilityMeasure.ne_zero μ.toMeasure
  rw [weighted_lp_norm, eLpNorm_const _ hq₀ hmeasure, hmass]
  simp only [one_div, ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal_abs,
    abs_of_nonneg hmean_nonneg]
  have habs :
      ∑ a, (μ a).toReal * |f a| = one_coordinate_mean μ f := by
    unfold one_coordinate_mean
    apply Finset.sum_congr rfl
    intro a ha
    rw [abs_of_nonneg (hf a)]
  symm
  simpa [habs] using
    (weighted_lp_norm_finite_moment μ 1 f (by norm_num) (by norm_num))

@[blueprint "lem:one-coordinate-vector-inequality"
  (statement := /-- Let $\mu$ and $\nu$ be full-support probability mass
  functions on finite spaces $A$ and $B$.  Suppose that $0<\lambda<1$ and
  the one-coordinate extremal inequality holds on $A$.  Then every
  nonnegative $F:B\times A\to\mathbb R$ satisfies
  \[
    \|(\mathrm{id}\otimes T_\rho)F\|_{L^q(\nu\otimes\mu)}
    \leq
    \|(\mathrm{id}\otimes\mathbb E_\mu)F\|_{L^q(\nu\otimes\mu)}^{1-\lambda}
    \|F\|_{L^q(\nu\otimes\mu)}^\lambda.
  \] -/)
  (proof := /-- For finite $q$, disintegrate all three product norms with
  \cref{lem:weighted-lp-norm-product-finite}, apply the one-coordinate
  inequality on every fiber, and sum the resulting powered inequalities by
  \cref{lem:finite-weighted-geometric-mean}.  The constant-fiber norm is
  identified with the fiber's $L^1$ norm by
  \cref{lem:one-coordinate-mean-constant-norm}.  For $q=\infty$, use the
  supremum disintegration in \cref{lem:weighted-lp-norm-product-top} and
  take the supremum of the pointwise fiber inequalities. -/)
  (title := /-- Vector-valued one-coordinate extremal inequality -/)
  (latexEnv := "lemma")]
lemma one_coordinate_vector_inequality {A B : Type*}
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [DecidableEq A]
    [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (μ : PMF A) (ν : PMF B) (q : ℝ≥0∞) (ρ lam : ℝ)
    (hμ : full_support_pmf μ) (hν : full_support_pmf ν)
    (hq : (2 : ℝ≥0∞) ≤ q)
    (hone : one_coordinate_extremal_property μ q ρ lam)
    (F : B → A → ℝ) (hF : ∀ b a, 0 ≤ F b a) :
    weighted_lp_norm (ν.toMeasure.prod μ.toMeasure) q
        (fun z ↦ one_coordinate_noise μ ρ (F z.1) z.2) ≤
      ENNReal.rpow
          (weighted_lp_norm (ν.toMeasure.prod μ.toMeasure) q
            (fun z ↦ one_coordinate_mean μ (F z.1))) (1 - lam) *
        ENNReal.rpow
          (weighted_lp_norm (ν.toMeasure.prod μ.toMeasure) q
            (fun z ↦ F z.1 z.2)) lam := by
  classical
  have hlam₀ : 0 < lam := hone.1
  have hlam₁ : lam < 1 := hone.2.1
  have hq₀ : q ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hq)
  by_cases hqtop : q = ⊤
  · subst q
    rw [weighted_lp_norm_product_top μ ν hμ hν
        (fun b a ↦ one_coordinate_noise μ ρ (F b) a),
      weighted_lp_norm_product_top μ ν hμ hν
        (fun b _ ↦ one_coordinate_mean μ (F b)),
      weighted_lp_norm_product_top μ ν hμ hν F]
    refine iSup_le fun b ↦ ?_
    have hb := (hone.2.2 (F b) (hF b)).1
    rw [← one_coordinate_mean_constant_norm μ ⊤ (F b)
      (by norm_num) (hF b)] at hb
    exact hb.trans (mul_le_mul'
      (ENNReal.rpow_le_rpow (le_iSup (fun c ↦
        weighted_lp_norm μ.toMeasure ⊤
          (fun _ ↦ one_coordinate_mean μ (F c))) b)
        (sub_nonneg.mpr hlam₁.le))
      (ENNReal.rpow_le_rpow (le_iSup (fun c ↦
        weighted_lp_norm μ.toMeasure ⊤ (F c)) b) hlam₀.le))
  · let r : ℝ := q.toReal
    have hr : 0 < r := ENNReal.toReal_pos hq₀ hqtop
    rw [weighted_lp_norm_product_finite μ ν q
        (fun b a ↦ one_coordinate_noise μ ρ (F b) a) hq₀ hqtop,
      weighted_lp_norm_product_finite μ ν q
        (fun b _ ↦ one_coordinate_mean μ (F b)) hq₀ hqtop,
      weighted_lp_norm_product_finite μ ν q F hq₀ hqtop]
    have hpoint (b : B) :
        ENNReal.rpow
            (weighted_lp_norm μ.toMeasure q
              (one_coordinate_noise μ ρ (F b))) r ≤
          ENNReal.rpow
              (ENNReal.rpow
                (weighted_lp_norm μ.toMeasure q
                  (fun _ ↦ one_coordinate_mean μ (F b))) r) (1 - lam) *
            ENNReal.rpow
              (ENNReal.rpow (weighted_lp_norm μ.toMeasure q (F b)) r) lam := by
      have hb := (hone.2.2 (F b) (hF b)).1
      rw [← one_coordinate_mean_constant_norm μ q (F b) hq₀ (hF b)] at hb
      have hp := ENNReal.rpow_le_rpow hb hr.le
      calc
        ENNReal.rpow
            (weighted_lp_norm μ.toMeasure q
              (one_coordinate_noise μ ρ (F b))) r ≤
            ENNReal.rpow
              (ENNReal.rpow
                  (weighted_lp_norm μ.toMeasure q
                    (fun _ ↦ one_coordinate_mean μ (F b))) (1 - lam) *
                ENNReal.rpow (weighted_lp_norm μ.toMeasure q (F b)) lam) r := hp
        _ = ENNReal.rpow
              (ENNReal.rpow
                (weighted_lp_norm μ.toMeasure q
                  (fun _ ↦ one_coordinate_mean μ (F b))) r) (1 - lam) *
            ENNReal.rpow
              (ENNReal.rpow (weighted_lp_norm μ.toMeasure q (F b)) r) lam := by
          simp only [ENNReal.rpow_eq_pow]
          rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le]
          congr 1
          · calc
              _ = weighted_lp_norm μ.toMeasure q
                    (fun _ ↦ one_coordinate_mean μ (F b)) ^
                  ((1 - lam) * r) :=
                    (ENNReal.rpow_mul _ (1 - lam) r).symm
              _ = weighted_lp_norm μ.toMeasure q
                    (fun _ ↦ one_coordinate_mean μ (F b)) ^
                  (r * (1 - lam)) := by ring
              _ = _ := ENNReal.rpow_mul _ r (1 - lam)
          · calc
              _ = weighted_lp_norm μ.toMeasure q (F b) ^ (lam * r) :=
                    (ENNReal.rpow_mul _ lam r).symm
              _ = weighted_lp_norm μ.toMeasure q (F b) ^ (r * lam) := by ring
              _ = _ := ENNReal.rpow_mul _ r lam
    have hsum :
        ∑ b, ν b * ENNReal.rpow
            (weighted_lp_norm μ.toMeasure q
              (one_coordinate_noise μ ρ (F b))) r ≤
          ENNReal.rpow
              (∑ b, ν b * ENNReal.rpow
                (weighted_lp_norm μ.toMeasure q
                  (fun _ ↦ one_coordinate_mean μ (F b))) r) (1 - lam) *
            ENNReal.rpow
              (∑ b, ν b * ENNReal.rpow
                (weighted_lp_norm μ.toMeasure q (F b)) r) lam := by
      calc
        _ ≤ ∑ b, ν b *
              (ENNReal.rpow
                  (ENNReal.rpow
                    (weighted_lp_norm μ.toMeasure q
                      (fun _ ↦ one_coordinate_mean μ (F b))) r) (1 - lam) *
                ENNReal.rpow
                  (ENNReal.rpow
                    (weighted_lp_norm μ.toMeasure q (F b)) r) lam) := by
              exact Finset.sum_le_sum fun b hb ↦ mul_le_mul_left' (hpoint b) _
        _ ≤ _ := finite_weighted_geometric_mean ν
          (fun b ↦ ENNReal.rpow
            (weighted_lp_norm μ.toMeasure q
              (fun _ ↦ one_coordinate_mean μ (F b))) r)
          (fun b ↦ ENNReal.rpow
            (weighted_lp_norm μ.toMeasure q (F b)) r)
          lam hlam₀ hlam₁
    have hroot := ENNReal.rpow_le_rpow hsum (by positivity : 0 ≤ 1 / r)
    calc
      _ ≤ ENNReal.rpow
          (ENNReal.rpow
              (∑ b, ν b * ENNReal.rpow
                (weighted_lp_norm μ.toMeasure q
                  (fun _ ↦ one_coordinate_mean μ (F b))) r) (1 - lam) *
            ENNReal.rpow
              (∑ b, ν b * ENNReal.rpow
                (weighted_lp_norm μ.toMeasure q (F b)) r) lam)
          (1 / r) := hroot
      _ = _ := by
        simp only [ENNReal.rpow_eq_pow]
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / r)]
        congr 1
        · calc
            _ = (∑ b, ν b * ENNReal.rpow
                  (weighted_lp_norm μ.toMeasure q
                    (fun _ ↦ one_coordinate_mean μ (F b))) r) ^
                ((1 - lam) * (1 / r)) :=
                  (ENNReal.rpow_mul _ (1 - lam) (1 / r)).symm
            _ = (∑ b, ν b * ENNReal.rpow
                  (weighted_lp_norm μ.toMeasure q
                    (fun _ ↦ one_coordinate_mean μ (F b))) r) ^
                ((1 / r) * (1 - lam)) := by ring
            _ = _ := ENNReal.rpow_mul _ (1 / r) (1 - lam)
        · calc
            _ = (∑ b, ν b * ENNReal.rpow
                  (weighted_lp_norm μ.toMeasure q (F b)) r) ^
                (lam * (1 / r)) :=
                  (ENNReal.rpow_mul _ lam (1 / r)).symm
            _ = (∑ b, ν b * ENNReal.rpow
                  (weighted_lp_norm μ.toMeasure q (F b)) r) ^
                ((1 / r) * lam) := by ring
            _ = _ := ENNReal.rpow_mul _ (1 / r) lam

@[blueprint "lem:product-noise-snoc"
  (statement := /-- Splitting the last coordinate of a function on
  $A^{n+1}$ factors product noise into product noise on the first $n$
  coordinates followed by one-coordinate noise on the last coordinate. -/)
  (proof := /-- Reindex the finite sum defining
  \cref{def:product-noise} by the bijection between an $(n+1)$-tuple and
  its first $n$ entries together with its last entry.  The product kernel
  factors by the last-coordinate product formula, and distributivity
  gives exactly the one-coordinate noise expression. -/)
  (title := /-- Last-coordinate factorization of product noise -/)
  (latexEnv := "lemma")]
lemma product_noise_snoc {A : Type*} [Fintype A] [DecidableEq A]
    (μ : PMF A) (ρ : ℝ) {n : ℕ} (f : (Fin (n + 1) → A) → ℝ)
    (x : Fin n → A) (a : A) :
    product_noise μ ρ f (Fin.snoc x a) =
      one_coordinate_noise μ ρ
        (fun b ↦ product_noise μ ρ (fun y ↦ f (Fin.snoc y b)) x) a := by
  classical
  unfold product_noise one_coordinate_noise one_coordinate_mean
  conv_lhs =>
    rw [← Equiv.sum_comp (Fin.insertNthEquiv
      (fun _ : Fin (n + 1) ↦ A) (Fin.last n))]
  rw [Fintype.sum_prod_type]
  simp only [Fin.insertNthEquiv_last]
  have hsnoc (z : A × (Fin n → A)) :
      (Fin.snocEquiv (fun _ : Fin (n + 1) ↦ A)) z = Fin.snoc z.2 z.1 := rfl
  simp_rw [hsnoc]
  simp only [Fin.prod_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc]
  simp_rw [show ∀ b : A,
      (if b = a then ρ + (1 - ρ) * (μ b).toReal
        else (1 - ρ) * (μ b).toReal) =
      (if b = a then ρ else 0) + (1 - ρ) * (μ b).toReal by
    intro b
    split_ifs <;> ring]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
  simp_rw [mul_ite, ite_mul, Finset.sum_ite_irrel]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hfirst :
      (∑ y : Fin n → A,
        (∏ j, if y j = x j then
          ρ + (1 - ρ) * (μ (y j)).toReal
        else (1 - ρ) * (μ (y j)).toReal) * ρ * f (Fin.snoc y a)) =
        ρ * ∑ y : Fin n → A,
          (∏ j, if y j = x j then
            ρ + (1 - ρ) * (μ (y j)).toReal
          else (1 - ρ) * (μ (y j)).toReal) * f (Fin.snoc y a) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  have hsecond :
      (∑ b : A, ∑ y : Fin n → A,
        (∏ j, if y j = x j then
          ρ + (1 - ρ) * (μ (y j)).toReal
        else (1 - ρ) * (μ (y j)).toReal) *
          ((1 - ρ) * (μ b).toReal) * f (Fin.snoc y b)) =
        (1 - ρ) * ∑ b : A, (μ b).toReal *
          ∑ y : Fin n → A,
            (∏ j, if y j = x j then
              ρ + (1 - ρ) * (μ (y j)).toReal
            else (1 - ρ) * (μ (y j)).toReal) * f (Fin.snoc y b) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    calc
      ∑ y : Fin n → A,
          (∏ j, if y j = x j then
            ρ + (1 - ρ) * (μ (y j)).toReal
          else (1 - ρ) * (μ (y j)).toReal) *
            ((1 - ρ) * (μ b).toReal) * f (Fin.snoc y b) =
        ∑ y : Fin n → A, (1 - ρ) *
          ((μ b).toReal *
            ((∏ j, if y j = x j then
              ρ + (1 - ρ) * (μ (y j)).toReal
            else (1 - ρ) * (μ (y j)).toReal) * f (Fin.snoc y b))) := by
              apply Finset.sum_congr rfl
              intro y hy
              ring
      _ = (1 - ρ) * ∑ y : Fin n → A, (μ b).toReal *
            ((∏ j, if y j = x j then
              ρ + (1 - ρ) * (μ (y j)).toReal
            else (1 - ρ) * (μ (y j)).toReal) * f (Fin.snoc y b)) := by
              simpa using (Finset.mul_sum
                (s := (Finset.univ : Finset (Fin n → A)))
                (f := fun y ↦ (μ b).toReal *
                  ((∏ j, if y j = x j then
                    ρ + (1 - ρ) * (μ (y j)).toReal
                  else (1 - ρ) * (μ (y j)).toReal) * f (Fin.snoc y b)))
                (a := 1 - ρ)).symm
      _ = (1 - ρ) * ((μ b).toReal * ∑ y : Fin n → A,
            (∏ j, if y j = x j then
              ρ + (1 - ρ) * (μ (y j)).toReal
            else (1 - ρ) * (μ (y j)).toReal) * f (Fin.snoc y b)) := by
              congr 1
              simpa using (Finset.mul_sum
                (s := (Finset.univ : Finset (Fin n → A)))
                (f := fun y ↦
                  (∏ j, if y j = x j then
                    ρ + (1 - ρ) * (μ (y j)).toReal
                  else (1 - ρ) * (μ (y j)).toReal) * f (Fin.snoc y b))
                (a := (μ b).toReal)).symm
  rw [hfirst, hsecond]
  congr <;> funext y <;> congr
  all_goals funext z
  all_goals congr
  all_goals funext j
  all_goals congr

@[blueprint "lem:conditional-average-snoc-without-last"
  (statement := /-- If a retained-coordinate set in $A^{n+1}$ is obtained
  from $S\subseteq\operatorname{Fin}(n)$ and does not contain the last
  coordinate, then conditional averaging first averages the last coordinate
  and then applies the $n$-coordinate conditional average for $S$. -/)
  (proof := /-- Reindex the defining finite sum from
  \cref{def:coordinate-conditional-average} by the decomposition of a tuple
  into its first $n$ entries and its last entry.  The matching condition is
  precisely the one for $S$, while the complementary product gains the last
  atom weight.  Interchanging the two finite sums gives the result. -/)
  (title := /-- Conditional averaging when the last coordinate is averaged -/)
  (latexEnv := "lemma")]
lemma conditional_average_snoc_without_last {A : Type*}
    [Fintype A] [DecidableEq A] (μ : PMF A) {n : ℕ}
    (S : Finset (Fin n)) (f : (Fin (n + 1) → A) → ℝ)
    (x : Fin n → A) (a : A) :
    coordinate_conditional_average μ (S.map Fin.castSuccEmb) f (Fin.snoc x a) =
      coordinate_conditional_average μ S
        (fun y ↦ one_coordinate_mean μ (fun b ↦ f (Fin.snoc y b))) x := by
  classical
  unfold coordinate_conditional_average one_coordinate_mean
  conv_lhs =>
    rw [← Equiv.sum_comp (Fin.insertNthEquiv
      (fun _ : Fin (n + 1) ↦ A) (Fin.last n))]
  rw [Fintype.sum_prod_type]
  simp only [Fin.insertNthEquiv_last]
  have hsnoc (z : A × (Fin n → A)) :
      (Fin.snocEquiv (fun _ : Fin (n + 1) ↦ A)) z = Fin.snoc z.2 z.1 := rfl
  simp_rw [hsnoc]
  have hcompl : (S.map Fin.castSuccEmb)ᶜ =
      insert (Fin.last n) (Sᶜ.map Fin.castSuccEmb) := by
    ext k
    refine Fin.lastCases ?_ (fun j ↦ ?_) k <;> simp
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Finset.mem_map,
    Function.Embedding.coeFn_mk]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  have hmatch_iff (b : A) :
      (∀ k : Fin (n + 1),
        (∃ j ∈ S, Fin.castSuccEmb j = k) →
          (Fin.snoc y b : Fin (n + 1) → A) k =
            (Fin.snoc x a : Fin (n + 1) → A) k) ↔
        ∀ j ∈ S, y j = x j := by
    constructor
    · intro h j hj
      simpa using h (Fin.castSucc j) ⟨j, hj, rfl⟩
    · intro h k hk
      obtain ⟨j, hj, rfl⟩ := hk
      simpa using h j hj
  simp_rw [hmatch_iff]
  by_cases hmatch : ∀ i ∈ S, y i = x i
  · simp_rw [if_pos hmatch]
    rw [hcompl]
    simp [Finset.prod_insert]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  · simp_rw [if_neg hmatch]
    simp

@[blueprint "lem:conditional-average-snoc-with-last"
  (statement := /-- If the retained-coordinate set in $A^{n+1}$ is
  $S\subseteq\operatorname{Fin}(n)$ together with the last coordinate, then
  conditional averaging fixes the last entry and is the $n$-coordinate
  conditional average for $S$ on the corresponding slice. -/)
  (proof := /-- Reindex the finite sum in
  \cref{def:coordinate-conditional-average} by first $n$ entries and the last
  entry.  The last-coordinate matching condition forces that entry to equal
  the displayed value, while the complementary weight is exactly the
  $S$-complementary product on the first $n$ coordinates. -/)
  (title := /-- Conditional averaging when the last coordinate is retained -/)
  (latexEnv := "lemma")]
lemma conditional_average_snoc_with_last {A : Type*}
    [Fintype A] [DecidableEq A] (μ : PMF A) {n : ℕ}
    (S : Finset (Fin n)) (f : (Fin (n + 1) → A) → ℝ)
    (x : Fin n → A) (a : A) :
    coordinate_conditional_average μ
        (insert (Fin.last n) (S.map Fin.castSuccEmb)) f (Fin.snoc x a) =
      coordinate_conditional_average μ S (fun y ↦ f (Fin.snoc y a)) x := by
  classical
  unfold coordinate_conditional_average
  conv_lhs =>
    rw [← Equiv.sum_comp (Fin.insertNthEquiv
      (fun _ : Fin (n + 1) ↦ A) (Fin.last n))]
  rw [Fintype.sum_prod_type]
  simp only [Fin.insertNthEquiv_last]
  have hsnoc (z : A × (Fin n → A)) :
      (Fin.snocEquiv (fun _ : Fin (n + 1) ↦ A)) z = Fin.snoc z.2 z.1 := rfl
  simp_rw [hsnoc]
  have hcompl : (insert (Fin.last n) (S.map Fin.castSuccEmb))ᶜ =
      Sᶜ.map Fin.castSuccEmb := by
    ext k
    refine Fin.lastCases ?_ (fun j ↦ ?_) k <;> simp
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Finset.mem_insert,
    Finset.mem_map, Function.Embedding.coeFn_mk]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  have hmatch_iff (b : A) :
      (∀ k : Fin (n + 1),
        (k = Fin.last n ∨ ∃ j ∈ S, Fin.castSuccEmb j = k) →
          (Fin.snoc y b : Fin (n + 1) → A) k =
            (Fin.snoc x a : Fin (n + 1) → A) k) ↔
        (b = a ∧ ∀ j ∈ S, y j = x j) := by
    constructor
    · intro h
      constructor
      · simpa using h (Fin.last n) (Or.inl rfl)
      · intro j hj
        simpa using h (Fin.castSucc j) (Or.inr ⟨j, hj, rfl⟩)
    · rintro ⟨hba, h⟩ k (hk | hk)
      · subst k
        simpa using hba
      · obtain ⟨j, hj, rfl⟩ := hk
        simpa using h j hj
  simp_rw [hmatch_iff]
  by_cases hmatch : ∀ i ∈ S, y i = x i
  · simp only [hcompl, Finset.prod_map,
      Function.Embedding.coeFn_mk]
    have hsnoc_cast (b : A) (i : Fin n) :
        (Fin.snoc y b : Fin (n + 1) → A) (Fin.castSuccEmb i) = y i := by
      simpa using Fin.snoc_castSucc (p := fun _ : Fin n ↦ A) y b i
    simp_rw [hsnoc_cast]
    have hcond (b : A) :
        (b = a ∧ ∀ i ∈ S, y i = x i) ↔ b = a := by
      constructor
      · exact And.left
      · intro hb
        exact ⟨hb, hmatch⟩
    simp_rw [hcond]
    rw [if_pos hmatch]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · have hcond (b : A) :
        ¬(b = a ∧ ∀ i ∈ S, y i = x i) := fun hb ↦ hmatch hb.2
    simp_rw [if_neg (hcond _)]
    rw [if_neg hmatch]
    simp only [Finset.sum_const_zero]

@[blueprint "lem:weighted-lp-norm-product-constant"
  (statement := /-- Let \(\nu\) and \(\mu\) be probability measures on
  finite measurable spaces \(B\) and \(A\), respectively.  For every
  \(q\in[0,\infty]\) and every \(g:B\to\mathbb R\), the \(L^q\)-norm of
  \((b,a)\mapsto g(b)\) with respect to \(\nu\otimes\mu\) equals the
  \(L^q(\nu)\)-norm of \(g\). -/)
  (proof := /-- The first-coordinate projection sends
  \(\nu\otimes\mu\) to \(\nu\), since \(\mu\) is a probability
  measure.  Invariance of the extended \(L^q\)-norm under this
  measure-preserving projection gives the equality. -/)
  (title := /-- Product norm of a function constant in one coordinate -/)
  (latexEnv := "lemma")]
lemma weighted_lp_norm_product_constant {A B : Type*}
    [MeasurableSpace A] [Fintype B] [MeasurableSpace B]
    [MeasurableSingletonClass B]
    (μ : PMF A) (ν : PMF B) (q : ℝ≥0∞) (g : B → ℝ) :
    weighted_lp_norm (ν.toMeasure.prod μ.toMeasure) q
        (fun z ↦ g z.1) =
      weighted_lp_norm ν.toMeasure q g := by
  unfold weighted_lp_norm
  exact eLpNorm_comp_measurePreserving
    (Measurable.aestronglyMeasurable (measurable_of_finite g))
    MeasureTheory.measurePreserving_fst

@[blueprint "lem:product-noise-commutes-last-mean"
  (statement := /-- Let \(f:A^{n+1}\to\mathbb R\).  Averaging the last
  coordinate after applying product noise in the first \(n\) coordinates
  equals applying that product noise after averaging the last coordinate. -/)
  (proof := /-- Expand \cref{def:product-noise} and
  \cref{def:one-coordinate-mean}.  Both sides are the same finite double
  sum; interchanging its two summations proves the identity. -/)
  (title := /-- Product noise commutes with the last-coordinate mean -/)
  (latexEnv := "lemma")]
lemma product_noise_commutes_last_mean {A : Type*} [Fintype A]
    (μ : PMF A) (ρ : ℝ) {n : ℕ} (f : (Fin (n + 1) → A) → ℝ)
    (x : Fin n → A) :
    one_coordinate_mean μ
        (fun a ↦ product_noise μ ρ (fun y ↦ f (Fin.snoc y a)) x) =
      product_noise μ ρ
        (fun y ↦ one_coordinate_mean μ (fun a ↦ f (Fin.snoc y a))) x := by
  classical
  unfold one_coordinate_mean product_noise
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc, mul_left_comm, mul_comm]

@[blueprint "lem:ereal-positive-scalar-add"
  (statement := /-- If \(c>0\) and \(x,y\in[-\infty,\infty)\), then
  multiplication by the embedded scalar \(c\) distributes over
  \(x+y\). -/)
  (proof := /-- If either summand is \(-\infty\), positivity of \(c\)
  reduces both sides to \(-\infty\).  Otherwise both summands are real;
  replace them by their real projections and use distributivity in
  \(\mathbb R\). -/)
  (title := /-- Positive finite scalar multiplication distributes on extended reals -/)
  (latexEnv := "lemma")]
lemma ereal_positive_scalar_add (c : ℝ) (hc : 0 < c)
    (x y : EReal) (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    (c : EReal) * (x + y) = (c : EReal) * x + (c : EReal) * y := by
  by_cases hxb : x = ⊥
  · subst x
    simp [EReal.coe_mul_bot_of_pos hc, hy]
  by_cases hyb : y = ⊥
  · subst y
    simp [EReal.coe_mul_bot_of_pos hc, hx]
  rw [← EReal.coe_toReal hx hxb, ← EReal.coe_toReal hy hyb]
  norm_cast
  ring

@[blueprint "lem:ereal-positive-scalar-ne-top"
  (statement := /-- If \(c>0\) and \(x<+\infty\) in the extended reals,
  then \(cx<+\infty\). -/)
  (proof := /-- If \(x=-\infty\), then positivity gives
  \(cx=-\infty\).  Otherwise \(x\) is real, so the product is real. -/)
  (title := /-- A positive finite multiple stays below positive infinity -/)
  (latexEnv := "lemma")]
lemma ereal_positive_scalar_ne_top (c : ℝ) (hc : 0 < c)
    (x : EReal) (hx : x ≠ ⊤) : (c : EReal) * x ≠ ⊤ := by
  by_cases hxb : x = ⊥
  · subst x
    simp [EReal.coe_mul_bot_of_pos hc]
  rw [← EReal.coe_toReal hx hxb]
  rw [← EReal.coe_mul]
  exact EReal.coe_ne_top _

@[blueprint "lem:ereal-positive-scalar-mul"
  (statement := /-- If \(c,d>0\) and \(x<+\infty\) in the extended
  reals, then \((cd)x=c(dx)\). -/)
  (proof := /-- The case \(x=-\infty\) follows from positivity.  In the
  remaining case \(x\) is real, and the identity is associativity in
  \(\mathbb R\). -/)
  (title := /-- Associativity of positive finite scalars on extended reals -/)
  (latexEnv := "lemma")]
lemma ereal_positive_scalar_mul (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (x : EReal) (hx : x ≠ ⊤) :
    ((c * d : ℝ) : EReal) * x =
      (c : EReal) * ((d : EReal) * x) := by
  by_cases hxb : x = ⊥
  · subst x
    rw [EReal.coe_mul_bot_of_pos (mul_pos hc hd),
      EReal.coe_mul_bot_of_pos hd, EReal.coe_mul_bot_of_pos hc]
  rw [← EReal.coe_toReal hx hxb]
  norm_cast
  ring

@[blueprint "lem:ereal-positive-scalar-sum"
  (statement := /-- If \(c>0\) and every member of a finite family of
  extended real numbers is strictly below \(+\infty\), then multiplication
  by \(c\) distributes over the sum of that family. -/)
  (proof := /-- Induct on the finite index set.  The empty case is
  immediate.  The insertion step uses
  \cref{lem:ereal-positive-scalar-add}; the partial sum remains below
  \(+\infty\) because each of its summands does. -/)
  (title := /-- Positive finite scalar multiplication distributes over finite sums -/)
  (latexEnv := "lemma")]
lemma ereal_positive_scalar_sum {ι : Type*} (c : ℝ) (hc : 0 < c)
    (s : Finset ι) (F : ι → EReal) (hF : ∀ i ∈ s, F i ≠ ⊤) :
    (c : EReal) * ∑ i ∈ s, F i = ∑ i ∈ s, (c : EReal) * F i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hFa : F a ≠ ⊤ := hF a (by simp)
      have hFs : ∀ i ∈ s, F i ≠ ⊤ := fun i hi ↦ hF i (by simp [hi])
      have hsum : (∑ i ∈ s, F i) ≠ ⊤ := by
        have sum_ne_top (t : Finset ι) (ht : ∀ i ∈ t, F i ≠ ⊤) :
            (∑ i ∈ t, F i) ≠ ⊤ := by
          induction t using Finset.induction_on with
          | empty => simp
          | @insert b t hb iht =>
              rw [Finset.sum_insert hb]
              exact EReal.add_ne_top (ht b (by simp))
                (iht (fun i hi ↦ ht i (by simp [hi])))
        exact sum_ne_top s hFs
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [ereal_positive_scalar_add c hc (F a) (∑ i ∈ s, F i) hFa hsum,
        ih hFs]

@[blueprint "lem:bernoulli-powerset-snoc"
  (statement := /-- For every function \(H\) on subsets of
  \(\operatorname{Fin}(n+1)\), its Bernoulli-weighted powerset sum splits
  into the subsets omitting the last coordinate, with factor \(1-\lambda\),
  and the subsets containing it, with factor \(\lambda\). -/)
  (proof := /-- Write the universal set as the disjoint insertion of the
  last coordinate into the image of \(\operatorname{Fin}(n)\).  The
  powerset insertion formula gives the two sums.  Reindex both along
  \(\operatorname{castSucc}\); preservation of cardinality gives the two
  identities for the weights from
  \cref{def:bernoulli-subset-weight}.  The positive scalar factors may be
  moved through the extended-real sums by
  \cref{lem:ereal-positive-scalar-sum}; their summands remain below
  \(+\infty\) by \cref{lem:ereal-positive-scalar-ne-top}, and
  \cref{lem:ereal-positive-scalar-mul} associates the two positive real
  factors in each summand. -/)
  (title := /-- Last-coordinate decomposition of a Bernoulli powerset sum -/)
  (latexEnv := "lemma")]
lemma bernoulli_powerset_snoc {n : ℕ} (lam : ℝ)
    (hlam₀ : 0 < lam) (hlam₁ : lam < 1)
    (H : Finset (Fin (n + 1)) → EReal) (hH : ∀ U, H U ≠ ⊤) :
    ∑ U ∈ (Finset.univ : Finset (Fin (n + 1))).powerset,
        (bernoulli_subset_weight lam U : EReal) * H U =
      ((1 - lam : ℝ) : EReal) *
          ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
            (bernoulli_subset_weight lam S : EReal) *
              H (S.map Fin.castSuccEmb) +
        (lam : EReal) *
          ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
            (bernoulli_subset_weight lam S : EReal) *
              H (insert (Fin.last n) (S.map Fin.castSuccEmb)) := by
  classical
  let e : Finset (Fin n) ↪ Finset (Fin (n + 1)) :=
    (Finset.mapEmbedding Fin.castSuccEmb).toEmbedding
  have huniv :
      (Finset.univ : Finset (Fin (n + 1))) =
        insert (Fin.last n)
          ((Finset.univ : Finset (Fin n)).map Fin.castSuccEmb) := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
  have hlast :
      Fin.last n ∉ (Finset.univ : Finset (Fin n)).map Fin.castSuccEmb := by
    simp
  have hpowerset :
      (((Finset.univ : Finset (Fin n)).map Fin.castSuccEmb).powerset) =
        ((Finset.univ : Finset (Fin n)).powerset).map e := by
    ext T
    constructor
    · intro hT
      have hsub := Finset.mem_powerset.mp hT
      let S : Finset (Fin n) :=
        T.preimage Fin.castSuccEmb (Fin.castSucc_injective n).injOn
      have hmap : S.map Fin.castSuccEmb = T := by
        ext i
        constructor
        · intro hi
          rcases Finset.mem_map.mp hi with ⟨j, hj, rfl⟩
          simpa [S] using hj
        · intro hi
          have hi' := hsub hi
          simp only [Finset.mem_map, Finset.mem_univ, true_and] at hi'
          rcases hi' with ⟨j, rfl⟩
          exact Finset.mem_map.mpr ⟨j, by simpa [S] using hi, rfl⟩
      rw [Finset.mem_map]
      exact ⟨S, Finset.mem_powerset.mpr (by simp), by simpa [e] using hmap⟩
    · intro hT
      rw [Finset.mem_map] at hT
      rcases hT with ⟨S, hS, rfl⟩
      exact Finset.mem_powerset.mpr (by
        intro i hi
        change i ∈ S.map Fin.castSuccEmb at hi
        rcases Finset.mem_map.mp hi with ⟨j, hj, rfl⟩
        simp)
  rw [huniv, Finset.sum_powerset_insert hlast, hpowerset]
  simp only [Finset.sum_map, e]
  have hcard (S : Finset (Fin n)) :
      (S.map Fin.castSuccEmb).card = S.card := Finset.card_map _
  have hcard_insert (S : Finset (Fin n)) :
      (insert (Fin.last n) (S.map Fin.castSuccEmb)).card = S.card + 1 := by
    rw [Finset.card_insert_of_notMem (by simp), hcard]
  have hsub (S : Finset (Fin n)) (hS : S ∈ Finset.univ.powerset) :
      n + 1 - (S.map Fin.castSuccEmb).card = (n - S.card) + 1 := by
    rw [hcard]
    have hc : S.card ≤ n := by
      simpa using Finset.card_le_card (Finset.mem_powerset.mp hS)
    omega
  have hsub_insert (S : Finset (Fin n))
      (hS : S ∈ Finset.univ.powerset) :
      n + 1 - (insert (Fin.last n) (S.map Fin.castSuccEmb)).card =
        n - S.card := by
    rw [hcard_insert]
    have hc : S.card ≤ n := by
      simpa using Finset.card_le_card (Finset.mem_powerset.mp hS)
    omega
  have htop₀ :
      ∀ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        (bernoulli_subset_weight lam S : EReal) *
            H (S.map Fin.castSuccEmb) ≠ ⊤ := by
    intro S hS
    apply ereal_positive_scalar_ne_top
    · unfold bernoulli_subset_weight
      exact mul_pos (pow_pos hlam₀ _) (pow_pos (sub_pos.mpr hlam₁) _)
    · exact hH _
  have htop₁ :
      ∀ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        (bernoulli_subset_weight lam S : EReal) *
            H (insert (Fin.last n) (S.map Fin.castSuccEmb)) ≠ ⊤ := by
    intro S hS
    apply ereal_positive_scalar_ne_top
    · unfold bernoulli_subset_weight
      exact mul_pos (pow_pos hlam₀ _) (pow_pos (sub_pos.mpr hlam₁) _)
    · exact hH _
  rw [ereal_positive_scalar_sum (1 - lam) (sub_pos.mpr hlam₁)
      _ _ htop₀,
    ereal_positive_scalar_sum lam hlam₀ _ _ htop₁]
  congr 1
  · apply Finset.sum_congr rfl
    intro S hS
    change (bernoulli_subset_weight lam (S.map Fin.castSuccEmb) : EReal) *
        H (S.map Fin.castSuccEmb) =
      ((1 - lam : ℝ) : EReal) * ((bernoulli_subset_weight lam S : EReal) *
        H (S.map Fin.castSuccEmb))
    have hw : 0 < bernoulli_subset_weight lam S := by
      unfold bernoulli_subset_weight
      exact mul_pos (pow_pos hlam₀ _) (pow_pos (sub_pos.mpr hlam₁) _)
    have heq :
        bernoulli_subset_weight lam (S.map Fin.castSuccEmb) =
          (1 - lam) * bernoulli_subset_weight lam S := by
      rw [bernoulli_subset_weight, bernoulli_subset_weight, hsub S hS, hcard,
        pow_succ]
      ring
    rw [heq]
    exact ereal_positive_scalar_mul (1 - lam)
      (bernoulli_subset_weight lam S) (sub_pos.mpr hlam₁) hw _ (hH _)
  · apply Finset.sum_congr rfl
    intro S hS
    change (bernoulli_subset_weight lam
          (insert (Fin.last n) (S.map Fin.castSuccEmb)) : EReal) *
        H (insert (Fin.last n) (S.map Fin.castSuccEmb)) =
      (lam : EReal) * ((bernoulli_subset_weight lam S : EReal) *
        H (insert (Fin.last n) (S.map Fin.castSuccEmb)))
    have hw : 0 < bernoulli_subset_weight lam S := by
      unfold bernoulli_subset_weight
      exact mul_pos (pow_pos hlam₀ _) (pow_pos (sub_pos.mpr hlam₁) _)
    have heq :
        bernoulli_subset_weight lam
            (insert (Fin.last n) (S.map Fin.castSuccEmb)) =
          lam * bernoulli_subset_weight lam S := by
      rw [bernoulli_subset_weight, bernoulli_subset_weight, hsub_insert S hS,
        hcard_insert, pow_succ]
      ring
    rw [heq]
    exact ereal_positive_scalar_mul lam
      (bernoulli_subset_weight lam S) hlam₀ hw _ (hH _)

@[blueprint "lem:product-noise-nonnegative"
  (statement := /-- If \(0<\rho<1\) and \(f\geq0\), then product noise
  preserves nonnegativity in every finite dimension. -/)
  (proof := /-- Expand \cref{def:product-noise}.  Each kernel factor is
  nonnegative because both \(\rho\) and \(1-\rho\) are nonnegative and
  every mass of \(\mu\) is nonnegative.  Thus every summand is
  nonnegative. -/)
  (title := /-- Product noise preserves nonnegativity -/)
  (latexEnv := "lemma")]
lemma product_noise_nonnegative {A : Type*} [Fintype A]
    (μ : PMF A) (ρ : ℝ) (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1)
    {n : ℕ} (f : (Fin n → A) → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∀ x, 0 ≤ product_noise μ ρ f x := by
  classical
  intro x
  unfold product_noise
  apply Finset.sum_nonneg
  intro y hy
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro i hi
    split_ifs
    · positivity
    · positivity
  · exact hf y

@[blueprint "lem:weighted-lp-norm-log-ne-top"
  (statement := /-- On a finite measurable space with a finite measure, the
  extended logarithm of the \(L^q\)-norm of every real-valued function is
  strictly below \(+\infty\). -/)
  (proof := /-- The extended \(L^q\)-norm of a function on a finite space
  is finite.  Since the extended logarithm equals \(+\infty\) exactly at
  \(+\infty\), its value is strictly below \(+\infty\). -/)
  (title := /-- Finite-space norm logarithms are below positive infinity -/)
  (latexEnv := "lemma")]
lemma weighted_lp_norm_log_ne_top {X : Type*} [Finite X]
    [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    (q : ℝ≥0∞) (f : X → ℝ) :
    ENNReal.log (weighted_lp_norm ν q f) ≠ ⊤ := by
  rw [ne_eq, ENNReal.log_eq_top_iff]
  exact ne_of_lt (by
    unfold weighted_lp_norm
    exact eLpNorm_lt_top_of_finite)

@[blueprint "lem:measure-preserving-base-snoc"
  (statement := /-- Splitting the last coordinate identifies
  \(\nu\otimes\mu^{\otimes(n+1)}\) with
  \((\nu\otimes\mu^{\otimes n})\otimes\mu\). -/)
  (proof := /-- The standard measurable equivalence splitting a
  \(\operatorname{Fin}(n+1)\)-tuple at its last coordinate preserves the
  corresponding product measures.  Taking its product with the identity on
  the base space and then reassociating products gives the stated map. -/)
  (title := /-- Measure-preserving last-coordinate splitting with a base -/)
  (latexEnv := "lemma")]
lemma measure_preserving_base_snoc {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] (μ : PMF A) (ν : PMF B)
    (n : ℕ) :
    MeasurePreserving
        (fun z : B × (Fin (n + 1) → A) ↦
          ((z.1, fun i ↦ z.2 i.castSucc), z.2 (Fin.last n)))
        (ν.toMeasure.prod (product_measure μ (n + 1)))
        ((ν.toMeasure.prod (product_measure μ n)).prod μ.toMeasure) := by
  letI : IsProbabilityMeasure (product_measure μ n) := by
    unfold product_measure
    infer_instance
  letI : IsProbabilityMeasure (product_measure μ (n + 1)) := by
    unfold product_measure
    infer_instance
  let e₀ := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) ↦ A) (Fin.last n)
  let e₁ : (Fin (n + 1) → A) ≃ᵐ (Fin n → A) × A :=
    e₀.trans MeasurableEquiv.prodComm
  have he₁ : MeasurePreserving e₁ (product_measure μ (n + 1))
      ((product_measure μ n).prod μ.toMeasure) := by
    have he₀ := measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) ↦ μ.toMeasure) (Fin.last n)
    have hswap : MeasurePreserving Prod.swap
        (μ.toMeasure.prod (product_measure μ n))
        ((product_measure μ n).prod μ.toMeasure) :=
      Measure.measurePreserving_swap
    exact hswap.comp he₀
  have hprod := (MeasurePreserving.id ν.toMeasure).prod he₁
  have hassoc :=
    (MeasureTheory.measurePreserving_prodAssoc ν.toMeasure
      (product_measure μ n) μ.toMeasure).symm MeasurableEquiv.prodAssoc
  have hcomp := hassoc.comp hprod
  have hfun :
      (fun z : B × (Fin (n + 1) → A) ↦
        ((z.1, fun i ↦ z.2 i.castSucc), z.2 (Fin.last n))) =
        MeasurableEquiv.prodAssoc.symm ∘ Prod.map id e₁ := by
    funext z
    rcases z with ⟨b, x⟩
    simp [e₁, e₀, Function.comp_def, MeasurableEquiv.prodComm,
      Fin.removeNth_last, Fin.init]
    congr 2
  rw [hfun]
  exact hcomp

@[blueprint "lem:measure-preserving-base-swap"
  (statement := /-- The rearrangement
  \(((b,x),a)\mapsto((b,a),x)\) preserves the corresponding three-factor
  product measure. -/)
  (proof := /-- Reassociate the first product, swap the final two factors,
  and reassociate back.  Each of these measurable equivalences preserves
  product measure, so their composition does as well. -/)
  (title := /-- Measure-preserving swap past a base coordinate -/)
  (latexEnv := "lemma")]
lemma measure_preserving_base_swap {A B X : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace X]
    (μ : Measure A) (ν : Measure B) (ξ : Measure X)
    [SFinite μ] [SFinite ν] [SFinite ξ] :
    MeasurePreserving
        (fun z : (B × X) × A ↦ ((z.1.1, z.2), z.1.2))
        ((ν.prod ξ).prod μ) ((ν.prod μ).prod ξ) := by
  have h₁ := MeasureTheory.measurePreserving_prodAssoc ν ξ μ
  have hswap := (MeasurePreserving.id ν).prod
    (Measure.measurePreserving_swap (μ := ξ) (ν := μ))
  have h₂ :=
    (MeasureTheory.measurePreserving_prodAssoc ν μ ξ).symm
      MeasurableEquiv.prodAssoc
  have hcomp := h₂.comp (hswap.comp h₁)
  simpa [Function.comp_def, MeasurableEquiv.prodAssoc,
    MeasurableEquiv.prodComm] using hcomp

@[blueprint "lem:measure-preserving-snoc"
  (statement := /-- Appending the last coordinate identifies
  \(\mu^{\otimes n}\otimes\mu\) with
  \(\mu^{\otimes(n+1)}\). -/)
  (proof := /-- The measurable equivalence which removes the last
  coordinate preserves product measure by the finite-coordinate product
  formula.  Taking its inverse gives the append map. -/)
  (title := /-- Measure-preserving append of a last coordinate -/)
  (latexEnv := "lemma")]
lemma measure_preserving_snoc {A : Type*} [MeasurableSpace A]
    (μ : PMF A) (n : ℕ) :
    MeasurePreserving
        (fun z : (Fin n → A) × A ↦ Fin.snoc z.1 z.2)
        ((product_measure μ n).prod μ.toMeasure)
        (product_measure μ (n + 1)) := by
  letI : IsProbabilityMeasure (product_measure μ n) := by
    unfold product_measure
    infer_instance
  letI : IsProbabilityMeasure (product_measure μ (n + 1)) := by
    unfold product_measure
    infer_instance
  let e₀ := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) ↦ A) (Fin.last n)
  let e : (Fin (n + 1) → A) ≃ᵐ (Fin n → A) × A :=
    e₀.trans MeasurableEquiv.prodComm
  have he : MeasurePreserving e (product_measure μ (n + 1))
      ((product_measure μ n).prod μ.toMeasure) := by
    have he₀ := measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) ↦ μ.toMeasure) (Fin.last n)
    exact Measure.measurePreserving_swap.comp he₀
  have hinv := he.symm e
  have hfun :
      (fun z : (Fin n → A) × A ↦ Fin.snoc z.1 z.2) = e.symm := by
    funext z
    rcases z with ⟨x, a⟩
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;>
      simp [e, e₀, MeasurableEquiv.prodComm, Fin.removeNth_last, Fin.init]
  rw [hfun]
  exact hinv

@[blueprint "lem:tensorized-vector-log-inequality"
  (statement := /-- Let \(A\) be a finite measurable space with a
  full-support probability mass function \(\mu\), and suppose
  \(\lambda\in(0,1)\) has the one-coordinate extremal property for
  \((\mu,q,\rho)\).  For every \(m,n\) and every nonnegative
  \(F:A^m\times A^n\to\mathbb R\), applying product noise in the final
  \(n\) coordinates satisfies the Bernoulli-weighted logarithmic
  conditional-average inequality, with the first \(m\) coordinates left
  untouched. -/)
  (proof := /-- Induct on \(n\), allowing an arbitrary number of
  auxiliary coordinates.  Split off the last active
  coordinate, apply the vector-valued one-coordinate estimate
  \cref{lem:one-coordinate-vector-inequality}, and take extended
  logarithms.  The averaged branch is the induction hypothesis with the
  same auxiliary space; the retained branch is the induction hypothesis
  after adjoining the last coordinate to that space.  The identities
  \cref{lem:product-noise-snoc,lem:product-noise-commutes-last-mean,
  lem:conditional-average-snoc-without-last,
  lem:conditional-average-snoc-with-last} identify the two branches.
  Measure invariance under
  \cref{lem:measure-preserving-base-snoc,lem:measure-preserving-base-swap,
  lem:measure-preserving-snoc} identifies their norms, while
  \cref{lem:weighted-lp-norm-product-constant} removes a coordinate on
  which a function is constant.  Nonnegativity needed at the inductive
  application follows from \cref{lem:product-noise-nonnegative}, and
  \cref{lem:weighted-lp-norm-log-ne-top} supplies the finiteness condition
  for the extended-real sum.  Finally
  \cref{lem:bernoulli-powerset-snoc} combines the two powerset sums. -/)
  (title := /-- Vector-valued tensorized logarithmic inequality -/)
  (latexEnv := "lemma")]
lemma tensorized_vector_log_inequality {A : Type*}
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [DecidableEq A]
    (μ : PMF A) (q : ℝ≥0∞) (ρ lam : ℝ)
    (hμ : full_support_pmf μ)
    (hq : (2 : ℝ≥0∞) ≤ q)
    (hone : one_coordinate_extremal_property μ q ρ lam)
    (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1)
    (n m : ℕ) (F : (Fin m → A) → (Fin n → A) → ℝ)
    (hF : ∀ b x, 0 ≤ F b x) :
    ENNReal.log
        (weighted_lp_norm ((product_measure μ m).prod (product_measure μ n)) q
          (fun z ↦ product_noise μ ρ (F z.1) z.2)) ≤
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        (bernoulli_subset_weight lam S : EReal) *
          ENNReal.log
            (weighted_lp_norm ((product_measure μ m).prod (product_measure μ n)) q
              (fun z ↦ coordinate_conditional_average μ S (F z.1) z.2)) := by
  classical
  induction n generalizing m with
  | zero =>
      simp [product_noise, coordinate_conditional_average,
        bernoulli_subset_weight]
  | succ n ih =>
      letI : IsProbabilityMeasure (product_measure μ n) := by
        unfold product_measure
        infer_instance
      letI : IsProbabilityMeasure (product_measure μ (n + 1)) := by
        unfold product_measure
        infer_instance
      letI : IsProbabilityMeasure (product_measure μ m) := by
        unfold product_measure
        infer_instance
      let ν : PMF (Fin m → A) := (product_measure μ m).toPMF
      have hνmeasure : ν.toMeasure = product_measure μ m := by
        simpa [ν] using
          (Measure.toPMF_toMeasure (μ := product_measure μ m))
      have hν : full_support_pmf ν := by
        intro x
        change ((product_measure μ m).toPMF x) ≠ 0
        rw [Measure.toPMF_apply]
        rw [product_measure, Measure.pi_singleton]
        apply Finset.prod_ne_zero_iff.mpr
        intro i hi
        rw [μ.toMeasure_apply_singleton (x i) (MeasurableSet.singleton (x i))]
        exact hμ (x i)
      let ξ : PMF ((Fin m → A) × (Fin n → A)) :=
        (ν.toMeasure.prod (product_measure μ n)).toPMF
      have hξmeasure :
          ξ.toMeasure = ν.toMeasure.prod (product_measure μ n) := by
        simpa [ξ] using
          (Measure.toPMF_toMeasure
            (μ := ν.toMeasure.prod (product_measure μ n)))
      have hξ : full_support_pmf ξ := by
        intro z
        rcases z with ⟨b, x⟩
        change ((ν.toMeasure.prod (product_measure μ n)).toPMF (b, x)) ≠ 0
        rw [Measure.toPMF_apply]
        rw [← Set.singleton_prod_singleton, Measure.prod_prod,
          ν.toMeasure_apply_singleton b (MeasurableSet.singleton b)]
        apply mul_ne_zero (hν b)
        rw [product_measure, Measure.pi_singleton]
        apply Finset.prod_ne_zero_iff.mpr
        intro i hi
        rw [μ.toMeasure_apply_singleton (x i) (MeasurableSet.singleton (x i))]
        exact hμ (x i)
      let G : ((Fin m → A) × (Fin n → A)) → A → ℝ := fun z a ↦
        product_noise μ ρ (fun y ↦ F z.1 (Fin.snoc y a)) z.2
      have hG : ∀ z a, 0 ≤ G z a := by
        intro z a
        exact product_noise_nonnegative μ ρ hρ₀ hρ₁
          (fun y ↦ F z.1 (Fin.snoc y a)) (fun y ↦ hF _ _) z.2
      have hvec := one_coordinate_vector_inequality μ ξ q ρ lam
        hμ hξ hq hone G hG
      have hlog := ENNReal.log_le_log hvec
      rw [ENNReal.log_mul_add] at hlog
      rw [show ENNReal.log
            (ENNReal.rpow
              (weighted_lp_norm (ξ.toMeasure.prod μ.toMeasure) q
                (fun z ↦ one_coordinate_mean μ (G z.1))) (1 - lam)) =
            ((1 - lam : ℝ) : EReal) *
              ENNReal.log
                (weighted_lp_norm (ξ.toMeasure.prod μ.toMeasure) q
                  (fun z ↦ one_coordinate_mean μ (G z.1))) from
          ENNReal.log_rpow] at hlog
      rw [show ENNReal.log
            (ENNReal.rpow
              (weighted_lp_norm (ξ.toMeasure.prod μ.toMeasure) q
                (fun z ↦ G z.1 z.2)) lam) =
            (lam : EReal) *
              ENNReal.log
                (weighted_lp_norm (ξ.toMeasure.prod μ.toMeasure) q
                  (fun z ↦ G z.1 z.2)) from
          ENNReal.log_rpow] at hlog
      have hnorm_snoc
          (K : (((Fin m → A) × (Fin n → A)) × A) → ℝ) :
          weighted_lp_norm
              ((product_measure μ m).prod (product_measure μ (n + 1))) q
              (fun z ↦ K ((z.1, fun i ↦ z.2 i.castSucc),
                z.2 (Fin.last n))) =
            weighted_lp_norm
              ((ν.toMeasure.prod (product_measure μ n)).prod μ.toMeasure)
              q K := by
        unfold weighted_lp_norm
        rw [← hνmeasure]
        exact eLpNorm_comp_measurePreserving
          (Measurable.aestronglyMeasurable (measurable_of_finite K))
          (measure_preserving_base_snoc μ ν n)
      have hlhs :
          weighted_lp_norm
              ((product_measure μ m).prod (product_measure μ (n + 1))) q
              (fun z ↦ product_noise μ ρ (F z.1) z.2) =
            weighted_lp_norm
              ((ν.toMeasure.prod (product_measure μ n)).prod μ.toMeasure) q
              (fun z ↦ one_coordinate_noise μ ρ (G z.1) z.2) := by
        rw [← hnorm_snoc]
        congr 1
        funext z
        conv_lhs => rw [← Fin.snoc_init_self z.2]
        rw [product_noise_snoc]
        unfold G
        change one_coordinate_noise μ ρ
            (fun a ↦ product_noise μ ρ
              (fun y ↦ F z.1 (Fin.snoc y a)) (Fin.init z.2))
            (z.2 (Fin.last n)) =
          one_coordinate_noise μ ρ
            (fun a ↦ product_noise μ ρ
              (fun y ↦ F z.1 (Fin.snoc y a))
              (fun i ↦ z.2 i.castSucc))
            (z.2 (Fin.last n))
        congr 2
      let F₀ : (Fin m → A) → (Fin n → A) → ℝ := fun b x ↦
        one_coordinate_mean μ (fun a ↦ F b (Fin.snoc x a))
      have hF₀ : ∀ b x, 0 ≤ F₀ b x := by
        intro b x
        unfold F₀ one_coordinate_mean
        exact Finset.sum_nonneg fun a ha ↦
          mul_nonneg ENNReal.toReal_nonneg (hF _ _)
      have hmean :
          weighted_lp_norm
              ((ν.toMeasure.prod (product_measure μ n)).prod μ.toMeasure) q
              (fun z ↦ one_coordinate_mean μ (G z.1)) =
            weighted_lp_norm
              ((product_measure μ m).prod (product_measure μ n)) q
              (fun z ↦ product_noise μ ρ (F₀ z.1) z.2) := by
        rw [← hξmeasure, weighted_lp_norm_product_constant μ ξ q
          (fun z ↦ one_coordinate_mean μ (G z)), hξmeasure, hνmeasure]
        congr 1
        funext z
        exact product_noise_commutes_last_mean μ ρ (F z.1) z.2
      have ih₀ := ih m F₀ hF₀
      let F₁ : (Fin (m + 1) → A) → (Fin n → A) → ℝ := fun z x ↦
        F (Fin.init z) (Fin.snoc x (z (Fin.last m)))
      have hF₁ : ∀ z x, 0 ≤ F₁ z x := fun z x ↦ hF _ _
      have ih₁ := ih (m + 1) F₁ hF₁
      have hnorm_retain
          (K : (Fin (m + 1) → A) × (Fin n → A) → ℝ) :
          weighted_lp_norm
              ((ν.toMeasure.prod (product_measure μ n)).prod μ.toMeasure)
              q (fun z ↦ K (Fin.snoc z.1.1 z.2, z.1.2)) =
            weighted_lp_norm
              ((product_measure μ (m + 1)).prod (product_measure μ n))
              q K := by
        have hswap := measure_preserving_base_swap μ.toMeasure ν.toMeasure
          (product_measure μ n)
        have hsnoc := measure_preserving_snoc μ m
        rw [← hνmeasure] at hsnoc
        have hmp :=
          (hsnoc.prod
            (MeasurePreserving.id (product_measure μ n))).comp
              hswap
        unfold weighted_lp_norm
        exact eLpNorm_comp_measurePreserving
          (Measurable.aestronglyMeasurable (measurable_of_finite K))
          (by
            simpa [Function.comp_def] using hmp)
      have hretain :
          weighted_lp_norm
              ((ν.toMeasure.prod (product_measure μ n)).prod μ.toMeasure)
              q (fun z ↦ G z.1 z.2) =
            weighted_lp_norm
              ((product_measure μ (m + 1)).prod (product_measure μ n))
              q (fun z ↦ product_noise μ ρ (F₁ z.1) z.2) := by
        rw [← hnorm_retain]
        congr 1
        funext z
        simp [F₁, G]
      rw [hξmeasure, ← hlhs, hmean, hretain] at hlog
      have hwithout (S : Finset (Fin n)) :
          weighted_lp_norm
              ((product_measure μ m).prod (product_measure μ (n + 1))) q
              (fun z ↦ coordinate_conditional_average μ
                (S.map Fin.castSuccEmb) (F z.1) z.2) =
            weighted_lp_norm
              ((product_measure μ m).prod (product_measure μ n)) q
              (fun z ↦ coordinate_conditional_average μ S (F₀ z.1) z.2) := by
        let K : (((Fin m → A) × (Fin n → A)) × A) → ℝ := fun z ↦
          coordinate_conditional_average μ (S.map Fin.castSuccEmb)
            (F z.1.1) (Fin.snoc z.1.2 z.2)
        calc
          weighted_lp_norm
                ((product_measure μ m).prod (product_measure μ (n + 1))) q
                (fun z ↦ coordinate_conditional_average μ
                  (S.map Fin.castSuccEmb) (F z.1) z.2) =
              weighted_lp_norm
                ((ν.toMeasure.prod (product_measure μ n)).prod μ.toMeasure)
                q K := by
                  rw [← hnorm_snoc]
                  congr 1
                  funext z
                  unfold K
                  change coordinate_conditional_average μ
                      (S.map Fin.castSuccEmb) (F z.1) z.2 =
                    coordinate_conditional_average μ
                      (S.map Fin.castSuccEmb) (F z.1)
                      (Fin.snoc (Fin.init z.2) (z.2 (Fin.last n)))
                  rw [Fin.snoc_init_self]
          _ = weighted_lp_norm
                ((ν.toMeasure.prod (product_measure μ n)).prod μ.toMeasure)
                q (fun z ↦ coordinate_conditional_average μ S
                  (F₀ z.1.1) z.1.2) := by
                  congr 1
                  funext z
                  exact conditional_average_snoc_without_last μ S
                    (F z.1.1) z.1.2 z.2
          _ = weighted_lp_norm
                ((product_measure μ m).prod (product_measure μ n)) q
                (fun z ↦ coordinate_conditional_average μ S
                  (F₀ z.1) z.2) := by
                  rw [← hξmeasure,
                    weighted_lp_norm_product_constant μ ξ q
                      (fun z ↦ coordinate_conditional_average μ S
                        (F₀ z.1) z.2),
                    hξmeasure, hνmeasure]
      have hwith (S : Finset (Fin n)) :
          weighted_lp_norm
              ((product_measure μ m).prod (product_measure μ (n + 1))) q
              (fun z ↦ coordinate_conditional_average μ
                (insert (Fin.last n) (S.map Fin.castSuccEmb))
                (F z.1) z.2) =
            weighted_lp_norm
              ((product_measure μ (m + 1)).prod (product_measure μ n)) q
              (fun z ↦ coordinate_conditional_average μ S (F₁ z.1) z.2) := by
        let K : (Fin (m + 1) → A) × (Fin n → A) → ℝ := fun z ↦
          coordinate_conditional_average μ S (F₁ z.1) z.2
        calc
          weighted_lp_norm
                ((product_measure μ m).prod (product_measure μ (n + 1))) q
                (fun z ↦ coordinate_conditional_average μ
                  (insert (Fin.last n) (S.map Fin.castSuccEmb))
                  (F z.1) z.2) =
              weighted_lp_norm
                ((ν.toMeasure.prod (product_measure μ n)).prod μ.toMeasure)
                q (fun z ↦ K (Fin.snoc z.1.1 z.2, z.1.2)) := by
                  rw [← hnorm_snoc]
                  congr 1
                  funext z
                  conv_lhs => rw [← Fin.snoc_init_self z.2]
                  unfold K F₁
                  simp only [Fin.init_snoc, Fin.snoc_last]
                  change coordinate_conditional_average μ
                      (insert (Fin.last n) (S.map Fin.castSuccEmb))
                      (F z.1)
                      (Fin.snoc (Fin.init z.2) (z.2 (Fin.last n))) =
                    coordinate_conditional_average μ S
                      (fun y ↦ F z.1 (Fin.snoc y (z.2 (Fin.last n))))
                      (Fin.init z.2)
                  exact conditional_average_snoc_with_last μ S
                    (F z.1) (Fin.init z.2) (z.2 (Fin.last n))
          _ = weighted_lp_norm
                ((product_measure μ (m + 1)).prod (product_measure μ n))
                q K := hnorm_retain K
          _ = weighted_lp_norm
                ((product_measure μ (m + 1)).prod (product_measure μ n)) q
                (fun z ↦ coordinate_conditional_average μ S
                  (F₁ z.1) z.2) := rfl
      have hlam₀ : 0 < lam := hone.1
      have hlam₁ : lam < 1 := hone.2.1
      have htop (U : Finset (Fin (n + 1))) :
          ENNReal.log
              (weighted_lp_norm
                ((product_measure μ m).prod (product_measure μ (n + 1))) q
                (fun z ↦ coordinate_conditional_average μ U (F z.1) z.2)) ≠
            ⊤ := by
        apply weighted_lp_norm_log_ne_top
      calc
        ENNReal.log
              (weighted_lp_norm
                ((product_measure μ m).prod (product_measure μ (n + 1))) q
                (fun z ↦ product_noise μ ρ (F z.1) z.2)) ≤
            ((1 - lam : ℝ) : EReal) *
                ENNReal.log
                  (weighted_lp_norm
                    ((product_measure μ m).prod (product_measure μ n)) q
                    (fun z ↦ product_noise μ ρ (F₀ z.1) z.2)) +
              (lam : EReal) *
                ENNReal.log
                  (weighted_lp_norm
                    ((product_measure μ (m + 1)).prod (product_measure μ n)) q
                    (fun z ↦ product_noise μ ρ (F₁ z.1) z.2)) := hlog
        _ ≤ ((1 - lam : ℝ) : EReal) *
                ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
                  (bernoulli_subset_weight lam S : EReal) *
                    ENNReal.log
                      (weighted_lp_norm
                        ((product_measure μ m).prod (product_measure μ n)) q
                        (fun z ↦ coordinate_conditional_average μ S
                          (F₀ z.1) z.2)) +
              (lam : EReal) *
                ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
                  (bernoulli_subset_weight lam S : EReal) *
                    ENNReal.log
                      (weighted_lp_norm
                        ((product_measure μ (m + 1)).prod
                          (product_measure μ n)) q
                        (fun z ↦ coordinate_conditional_average μ S
                          (F₁ z.1) z.2)) := by
              gcongr
        _ = ∑ U ∈ (Finset.univ : Finset (Fin (n + 1))).powerset,
              (bernoulli_subset_weight lam U : EReal) *
                ENNReal.log
                  (weighted_lp_norm
                    ((product_measure μ m).prod (product_measure μ (n + 1))) q
                    (fun z ↦ coordinate_conditional_average μ U
                      (F z.1) z.2)) := by
              rw [bernoulli_powerset_snoc lam hlam₀ hlam₁ _ htop]
              simp_rw [hwithout, hwith]

@[blueprint "lem:extremal-parameter-tensorizes"
  (statement := /-- Let $\Omega$ be a finite measurable space in which
  every singleton is measurable and equality is decidable, and let $\mu$
  be a full-support probability mass function on $\Omega$.  Let
  $q\in[2,\infty]$ and $\rho\in(0,1)$, put
  $\mu^*=\min_{x\in\Omega}\mu(x)$, and define
  $\lambda=\lambda(q,\mu^*,\rho)$ as in
  \cref{def:optimal-samorodnitsky-parameter}.  Then this same $\lambda$
  has both the one-coordinate extremal property of
  \cref{def:one-coordinate-extremal-property} and the tensorized
  Samorodnitsky property of
  \cref{def:tensorized-samorodnitsky-property}. -/)
  (proof := /-- Take the canonical $\lambda$ supplied by
  \cref{lem:one-coordinate-extremal-parameter-exists}.  The strengthened
  induction, including the auxiliary coordinates used below, is formalized
  in \cref{lem:tensorized-vector-log-inequality}; apply it with no
  auxiliary coordinates, and remove the resulting one-point product
  factor by the measure-preserving second projection.  For completeness,
  denote the one-coordinate inequality by
  one-coordinate inequality by
  \[
    \|T_\rho g\|_q
      \leq \|\mathbb E_\mu g\|_q^{,1-\lambda}
             \|g\|_q^{,\lambda}.
    \tag{1}
  \]
  Here the first norm on the right is the norm of the constant
  $\mathbb E_\mu g$; this is exactly the $L^1(\mu)$ norm of $g$ because
  $g\geq0$.  This interpretation follows directly from
  \cref{def:one-coordinate-mean,def:one-coordinate-noise,def:weighted-lp-norm,def:one-coordinate-extremal-property}.

  We first prove the vector-valued form of (1).  Let $(B,\nu)$ be any
  finite probability space with full support, and let
  $G:B\times\Omega\to\mathbb R$ be nonnegative.  If $q<\infty$, put
  $r=q.toReal$.  For each $b\in B$, apply (1) to
  $g_b(x)=G(b,x)$.  Taking the $r$th power, summing with weights
  $\nu(b)$, and applying Hölder with conjugate exponents
  $(1-\lambda)^{-1}$ and $\lambda^{-1}$ gives
  \[
    \|(\mathrm{id}\otimes T_\rho)G\|_{L^q(\nu\otimes\mu)}
      \leq
      \|(\mathrm{id}\otimes\mathbb E_\mu)G\|_{L^q(\nu)}^{,1-\lambda}
      \|G\|_{L^q(\nu\otimes\mu)}^{,\lambda}.
    \tag{2}
  \]
  Indeed, if
  \[
    A_b=\|T_\rho g_b\|_{L^q(\mu)},\quad
    B_b=\mathbb E_\mu g_b,\quad
    C_b=\|g_b\|_{L^q(\mu)},
  \]
  then (1) says $A_b\leq B_b^{1-\lambda}C_b^\lambda$, while Hölder
  says
  \[
    \sum_b\nu(b)A_b^r
      \leq
      \left(\sum_b\nu(b)B_b^r\right)^{1-\lambda}
      \left(\sum_b\nu(b)C_b^r\right)^\lambda.
  \]
  The three sums are respectively the $r$th powers of the three norms
  in (2).  If $q=\infty$, the same conclusion follows without Hölder:
  take the maximum over $b$ in
  $A_b\leq B_b^{1-\lambda}C_b^\lambda$ and use
  \[
    \max_b B_b^{1-\lambda}C_b^\lambda
      \leq (\max_b B_b)^{1-\lambda}(\max_b C_b)^\lambda.
  \]
  Full support and finiteness identify these maxima with the relevant
  essential suprema.  Thus (2) holds for every
  $q\in[2,\infty]$.

  We now prove a strengthened tensorization statement.  For all
  $n,m\in\mathbb N$ and every nonnegative
  $F:\Omega^n\times\Omega^m\to\mathbb R$, noise only the first
  $n$ coordinates and leave the last $m$ coordinates auxiliary.  We
  claim
  \[
    \log\|(T_\rho^{\otimes n}\otimes\mathrm{id})F\|_q
      \leq
      \sum_{S\subseteq[ n ]}
        \lambda^{|S|}(1-\lambda)^{n-|S|}
        \log\| (\mathbb E_{[ n ]\setminus S}\otimes\mathrm{id})F\|_q.
    \tag{3}
  \]
  Every norm in (3) is taken with respect to the appropriate product of
  copies of $\mu$ as in
  \cref{def:product-measure,def:weighted-lp-norm}.  The case $n=0$ is
  equality: there is only the empty subset, its weight is one, and both
  operators are the identity.

  Suppose (3) holds for $n$ and for every number of auxiliary
  coordinates.  Split
  $\Omega^{n+1}\times\Omega^m$ as
  $\Omega^n\times\Omega^m\times\Omega$, with the last factor the
  new active coordinate.  Apply (2), with
  $B=\Omega^n\times\Omega^m$, to the function obtained after applying
  noise in the first $n$ active coordinates.  The coordinate-average
  operator and the coordinate-noise operators commute because they are
  finite sums in distinct variables.  Hence
  \[
  \begin{aligned}
    \|(T_\rho^{\otimes(n+1)}\otimes\mathrm{id})F\|_q
    \leq{}&
      \|(T_\rho^{\otimes n}\otimes\mathrm{id})
             \mathbb E_{n+1}F\|_q^{,1-\lambda}\\
    &\cdot
      \|(T_\rho^{\otimes n}\otimes\mathrm{id})F\|_q^{,\lambda}.
  \end{aligned}
  \tag{4}
  \]
  Apply the induction hypothesis with $m$ auxiliary coordinates to
  $\mathbb E_{n+1}F$, and with $m+1$ auxiliary coordinates to $F$,
  treating the new coordinate as auxiliary in the latter application.
  Taking logarithms in (4), the first resulting sum is multiplied by
  $1-\lambda$ and indexes subsets not containing the new coordinate;
  the second is multiplied by $\lambda$ and indexes subsets containing
  it.

  For completeness, these identifications agree exactly with the Lean
  definitions.  Use the bijection
  \[
    (\operatorname{Fin}(n+1)\to\Omega)
      \longleftrightarrow
    (\operatorname{Fin}(n)\to\Omega)\times\Omega,
    \qquad
    x\longmapsto
      \bigl(x\circ\operatorname{castSucc},x(\operatorname{last}n)\bigr).
  \]
  Reindexing the finite sums along this bijection shows that
  \cref{def:product-measure} is transported to the product of the
  $n$-coordinate measure and $\mu$.  Fubini's identity for these finite
  sums gives the iterated-$L^q$ equalities used above when $q<\infty$;
  the corresponding identity for $q=\infty$ is the equality between
  the maximum over a product and the iterated maximum.  Unfolding
  \cref{def:product-noise,def:coordinate-conditional-average} and
  interchanging the two finite sums proves respectively the noise
  factorization and the commutation asserted in (4).

  Let $\iota:\operatorname{Fin}(n)\hookrightarrow
  \operatorname{Fin}(n+1)$ be $\operatorname{castSucc}$ and let
  $j=\operatorname{last}n$.  Every subset of
  $\operatorname{Fin}(n+1)$ is uniquely either $\iota(S)$ or
  $\iota(S)\cup\{j\}$.  Since the two sets have cardinalities
  $|S|$ and $|S|+1$, respectively,
  \[
  \begin{aligned}
    (1-\lambda)\lambda^{|S|}(1-\lambda)^{n-|S|}
      &=\lambda^{|\iota(S)|}
        (1-\lambda)^{n+1-|\iota(S)|},\\
    \lambda\lambda^{|S|}(1-\lambda)^{n-|S|}
      &=\lambda^{|\iota(S)\cup\{j\}|}
        (1-\lambda)^{n+1-|\iota(S)\cup\{j\}|}.
  \end{aligned}
  \]
  Thus the two sums obtained from (4) combine into precisely the
  powerset sum with the weights of
  \cref{def:bernoulli-subset-weight}, proving (3) for $n+1$.

  It remains only to justify the extended logarithms.  If $F=0$, every
  term in (3) is $\log0=-\infty$, and (3) holds.  Otherwise,
  \cref{def:full-support-pmf} and nonnegativity imply that every
  conditional average occurring in (3) is nonzero: a positive value of
  $F$ contributes with a strictly positive product weight.  On the
  finite product space all of its norms are therefore positive and
  finite, as are the noisy norms.  The ordinary identities for the
  logarithm of a product and of a positive real power consequently
  justify the passage from (4) to the displayed logarithmic sums.

  Taking $m=0$ in (3), and translating through
  \cref{def:tensorized-samorodnitsky-property}, proves the tensorized
  conjunct for every $n$.  The same $\lambda$ already has the
  one-coordinate extremal property by its choice, so the two required
  conjuncts hold simultaneously. -/)
  (title := /-- Tensorization of the extremal parameter -/)
  (latexEnv := "lemma")]
lemma extremal_parameter_tensorizes {Ω : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [DecidableEq Ω] (μ : PMF Ω) (q : ℝ≥0∞) (ρ : ℝ)
    (hμ : full_support_pmf μ) (hq : (2 : ℝ≥0∞) ≤ q)
    (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) :
    one_coordinate_extremal_property μ q ρ
        (optimal_samorodnitsky_parameter q (minimum_atom_mass μ) ρ) ∧
      tensorized_samorodnitsky_property μ q ρ
        (optimal_samorodnitsky_parameter q (minimum_atom_mass μ) ρ) := by
  let lam := optimal_samorodnitsky_parameter q (minimum_atom_mass μ) ρ
  have hone : one_coordinate_extremal_property μ q ρ lam :=
    one_coordinate_extremal_parameter_exists μ q ρ hμ hq hρ₀ hρ₁
  refine ⟨hone, ?_⟩
  unfold tensorized_samorodnitsky_property
  intro n f hf
  letI : IsProbabilityMeasure (product_measure μ 0) := by
    unfold product_measure
    infer_instance
  letI : IsProbabilityMeasure (product_measure μ n) := by
    unfold product_measure
    infer_instance
  have hnorm (g : (Fin n → Ω) → ℝ) :
      weighted_lp_norm
          ((product_measure μ 0).prod (product_measure μ n)) q
          (fun z ↦ g z.2) =
        weighted_lp_norm (product_measure μ n) q g := by
    unfold weighted_lp_norm
    exact eLpNorm_comp_measurePreserving
      (Measurable.aestronglyMeasurable (measurable_of_finite g))
      MeasureTheory.measurePreserving_snd
  have ht := tensorized_vector_log_inequality μ q ρ lam hμ hq hone
    hρ₀ hρ₁ n 0 (fun _ x ↦ f x) (fun _ x ↦ hf x)
  simp_rw [hnorm] at ht
  simpa [lam] using ht

@[blueprint "thm:generalized-samorodnitsky-inequality"
  (statement := /-- Let $\Omega$ be a finite measurable space in which
  every singleton is measurable and equality is decidable.  Let $\mu$ be
  a full-support probability distribution on $\Omega$, and put
  $\mu^*=\min_{x\in\Omega}\mu(x)$, let $q\in[2,\infty]$, and let
  $\rho\in(0,1)$.  The optimal parameter
  $\lambda=\lambda(q,\mu^*,\rho)$ of
  \cref{def:optimal-samorodnitsky-parameter} lies in $(0,1)$.  For this
  parameter, every nonnegative
  $f:\Omega\to\mathbb R$ satisfies
  \[
    \|T_\rho f\|_{L^q(\mu)}
      \leq \|f\|_{L^1(\mu)}^{1-\lambda}
             \|f\|_{L^q(\mu)}^\lambda.
  \]
  Equality holds if and only if $f$ is a nonnegative constant or is a
  nonnegative multiple of the indicator of a point $x^*$ satisfying
  $\mu(x^*)=\min_x\mu(x)$.  For this same $\lambda$, every
  $n\in\mathbb N$ and every nonnegative $f:\Omega^n\to\mathbb R$ satisfy
  \[
    \log\|T_\rho f\|_{L^q(\mu^{\otimes n})}
      \leq \mathbb E_{S\sim\lambda}
        \log\|\mathbb E_\mu(f\mid S)\|_{L^q(\mu^{\otimes n})},
  \]
  where the coordinates belong to $S$ independently with probability $\lambda$. -/)
  (proof := /-- Apply \cref{lem:extremal-parameter-tensorizes} with
  $\lambda=\lambda(q,\mu^*,\rho)$.  Its first conjunct is precisely
  the one-coordinate inequality, including $0<\lambda<1$ and the stated
  equality characterization, while its second conjunct is precisely the
  product-space inequality for all dimensions. -/)
  (title := /-- Generalized Samorodnitsky inequality -/)
  (latexEnv := "theorem")]
theorem generalized_samorodnitsky_inequality {Ω : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [DecidableEq Ω] (μ : PMF Ω) (q : ℝ≥0∞) (ρ : ℝ)
    (hμ : full_support_pmf μ) (hq : (2 : ℝ≥0∞) ≤ q)
    (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) :
    one_coordinate_extremal_property μ q ρ
        (optimal_samorodnitsky_parameter q (minimum_atom_mass μ) ρ) ∧
      tensorized_samorodnitsky_property μ q ρ
        (optimal_samorodnitsky_parameter q (minimum_atom_mass μ) ρ) := by
  exact extremal_parameter_tensorizes μ q ρ hμ hq hρ₀ hρ₁

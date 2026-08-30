import Architect
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:polynomial-factor"
  (statement := /-- For a model of dimension $n$, a polynomial factor is the exponent vector
  $k=(k_1,\ldots,k_n)\in\mathbb N^n$ of a monomial. -/)
  (title := /-- Polynomial factors -/)
  (latexEnv := "definition")]
abbrev polynomial_factor (n : ℕ) := Fin n → ℕ

@[blueprint "def:factor-support"
  (statement := /-- The support $\partial k$ of a polynomial factor $k$ is the set of coordinates
  whose exponents are strictly positive. -/)
  (title := /-- Support of a polynomial factor -/)
  (latexEnv := "definition")]
def factor_support {n : ℕ} (factor : polynomial_factor n) : Finset (Fin n) :=
  Finset.univ.filter fun j => 0 < factor j

@[blueprint "def:factors-at"
  (statement := /-- Given a finite factor family $\mathcal K$ and a coordinate $j$, the set
  $\mathcal K_j$ consists of precisely those factors whose support contains $j$. -/)
  (title := /-- Factors incident to a coordinate -/)
  (latexEnv := "definition")]
def factors_at {n : ℕ} (factors : Finset (polynomial_factor n)) (j : Fin n) :
    Finset (polynomial_factor n) :=
  factors.filter fun factor => j ∈ factor_support factor

@[blueprint "def:maximal-factors"
  (statement := /-- A factor in $\mathcal K$ is maximal when its support is not a proper subset of
  the support of any other factor in $\mathcal K$. The finite set of all such factors is denoted
  $\mathcal M_{\mathrm{fac}}(G)$. -/)
  (title := /-- Maximal factors of the family factor graph -/)
  (latexEnv := "definition")]
def maximal_factors {n : ℕ} (factors : Finset (polynomial_factor n)) :
    Finset (polynomial_factor n) :=
  factors.filter fun factor =>
    ¬ ∃ larger ∈ factors,
      factor_support factor ⊆ factor_support larger ∧
        factor_support factor ≠ factor_support larger

@[blueprint "def:incident-maximal-factors"
  (statement := /-- For a fixed coordinate $i$, define
  $\widehat{\mathcal K}=\{k\in\mathcal M_{\mathrm{fac}}(G):i\in\partial k\}$,
  the maximal factors adjacent to $i$ in the family factor graph. -/)
  (title := /-- Maximal factors incident to the distinguished coordinate -/)
  (latexEnv := "definition")]
def incident_maximal_factors {n : ℕ} (factors : Finset (polynomial_factor n)) (i : Fin n) :
    Finset (polynomial_factor n) :=
  (maximal_factors factors).filter fun factor => i ∈ factor_support factor

@[blueprint "def:interaction-order"
  (statement := /-- The interaction order $w$ of a finite factor family is the largest cardinality
  of a factor support, with value zero for the empty family. -/)
  (title := /-- Interaction order -/)
  (latexEnv := "definition")]
def interaction_order {n : ℕ} (factors : Finset (polynomial_factor n)) : ℕ :=
  factors.sup fun factor => (factor_support factor).card

@[blueprint "def:family-degree-at-most"
  (statement := /-- A factor family has degree at most $d$ if every exponent vector in the family
  has total degree at most $d$. -/)
  (title := /-- Uniform degree bound -/)
  (latexEnv := "definition")]
def family_degree_at_most {n : ℕ} (factors : Finset (polynomial_factor n)) (d : ℕ) : Prop :=
  ∀ factor ∈ factors, (∑ j, factor j) ≤ d

@[blueprint "def:monomial-value"
  (statement := /-- For $k\in\mathbb N^n$ and $x\in\mathbb R^n$, let
  $f_k(x)=\prod_{j=1}^n x_j^{k_j}$. -/)
  (title := /-- Evaluation of a monomial factor -/)
  (latexEnv := "definition")]
def monomial_value {n : ℕ} (factor : polynomial_factor n) (x : Fin n → ℝ) : ℝ :=
  ∏ j, x j ^ factor j

@[blueprint "def:monomial-first-partial"
  (statement := /-- For a coordinate $i$, the first formal partial derivative of $f_k$ is
  $k_i x_i^{k_i-1}\prod_{j\ne i}x_j^{k_j}$. The formula is valid also when $k_i=0$, because its
  leading coefficient then vanishes. -/)
  (title := /-- First coordinate derivative of a monomial -/)
  (latexEnv := "definition")]
def monomial_first_partial {n : ℕ} (factor : polynomial_factor n) (i : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  (factor i : ℝ) * x i ^ (factor i - 1) *
    ∏ j ∈ Finset.univ.erase i, x j ^ factor j

@[blueprint "def:monomial-second-partial"
  (statement := /-- For a coordinate $i$, the second formal partial derivative of $f_k$ is
  $k_i(k_i-1)x_i^{k_i-2}\prod_{j\ne i}x_j^{k_j}$. The coefficient makes this formula valid when
  $k_i<2$. -/)
  (title := /-- Second coordinate derivative of a monomial -/)
  (latexEnv := "definition")]
def monomial_second_partial {n : ℕ} (factor : polynomial_factor n) (i : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  (factor i : ℝ) * ((factor i - 1 : ℕ) : ℝ) * x i ^ (factor i - 2) *
    ∏ j ∈ Finset.univ.erase i, x j ^ factor j

@[blueprint "def:exponential-energy"
  (statement := /-- Given parameters $\theta=(\theta_k)_{k\in\mathcal K}$, define the polynomial
  exponential-family energy $E_\theta(x)=\sum_{k\in\mathcal K}\theta_k f_k(x)$. -/)
  (title := /-- Polynomial exponential-family energy -/)
  (latexEnv := "definition")]
def exponential_energy {n : ℕ} (factors : Finset (polynomial_factor n))
    (theta : polynomial_factor n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ factor ∈ factors, theta factor * monomial_value factor x

@[blueprint "def:energy-first-partial"
  (statement := /-- The first coordinate derivative of $E_\theta$ is obtained by differentiating
  every monomial in the finite factor expansion. -/)
  (title := /-- First coordinate derivative of the energy -/)
  (latexEnv := "definition")]
def energy_first_partial {n : ℕ} (factors : Finset (polynomial_factor n))
    (theta : polynomial_factor n → ℝ) (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  ∑ factor ∈ factors, theta factor * monomial_first_partial factor i x

@[blueprint "def:energy-second-partial"
  (statement := /-- The second coordinate derivative of $E_\theta$ is obtained by differentiating
  every monomial in the finite factor expansion twice in the same coordinate. -/)
  (title := /-- Second coordinate derivative of the energy -/)
  (latexEnv := "definition")]
def energy_second_partial {n : ℕ} (factors : Finset (polynomial_factor n))
    (theta : polynomial_factor n → ℝ) (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  ∑ factor ∈ factors, theta factor * monomial_second_partial factor i x

@[blueprint "def:local-score-matching-loss"
  (statement := /-- For a unit-base exponential family, the local Hyv\"arinen score-matching loss
  in coordinate $i$ is
  $\mathcal L_i(\theta,x)=\partial_i^2E_\theta(x)+\frac12(\partial_iE_\theta(x))^2$.
  The normalizing constant has zero coordinate derivatives and therefore does not occur. -/)
  (title := /-- Local score-matching loss -/)
  (latexEnv := "definition")]
noncomputable def local_score_matching_loss {n : ℕ} (factors : Finset (polynomial_factor n))
    (theta : polynomial_factor n → ℝ) (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  energy_second_partial factors theta i x +
    (1 / 2 : ℝ) * (energy_first_partial factors theta i x) ^ 2

@[blueprint "def:empirical-local-score-matching-loss"
  (statement := /-- For observations $x_1,\ldots,x_M$, the empirical local loss is
  $M^{-1}\sum_{m=1}^M\mathcal L_i(\theta,x_m)$. When $M=0$, the inverse convention in the formal
  definition gives value zero; the theorem's positive sample threshold excludes that case. -/)
  (title := /-- Empirical local score-matching loss -/)
  (latexEnv := "definition")]
noncomputable def empirical_local_score_matching_loss {n M : ℕ}
    (factors : Finset (polynomial_factor n)) (theta : polynomial_factor n → ℝ) (i : Fin n)
    (observations : Fin M → (Fin n → ℝ)) : ℝ :=
  (M : ℝ)⁻¹ * ∑ m, local_score_matching_loss factors theta i (observations m)

@[blueprint "def:parameter-feasible"
  (statement := /-- A parameter vector is feasible at radius $B$ if, for every coordinate $j$,
  the $\ell_1$-sum of coefficients of factors incident to $j$ is at most $B$. -/)
  (title := /-- Coordinatewise parameter feasibility -/)
  (latexEnv := "definition")]
def parameter_feasible {n : ℕ} (factors : Finset (polynomial_factor n)) (B : ℝ)
    (theta : polynomial_factor n → ℝ) : Prop :=
  ∀ j, ∑ factor ∈ factors_at factors j, |theta factor| ≤ B

@[blueprint "def:constrained-empirical-minimizer"
  (statement := /-- A vector $\widehat\theta$ is a constrained empirical minimizer when it is
  feasible and its empirical local score-matching loss is no larger than that of every feasible
  parameter vector. -/)
  (title := /-- Constrained empirical score-matching minimizer -/)
  (latexEnv := "definition")]
def constrained_empirical_minimizer {n M : ℕ}
    (factors : Finset (polynomial_factor n)) (B : ℝ) (i : Fin n)
    (observations : Fin M → (Fin n → ℝ)) (thetaHat : polynomial_factor n → ℝ) : Prop :=
  parameter_feasible factors B thetaHat ∧
    ∀ theta, parameter_feasible factors B theta →
      empirical_local_score_matching_loss factors thetaHat i observations ≤
        empirical_local_score_matching_loss factors theta i observations

@[blueprint "def:unit-base-polynomial-exponential-family"
  (statement := /-- A probability measure $p_\theta$ is the unit-base polynomial exponential
  family generated by $(\mathcal K,\theta)$ when, for a positive normalizing constant
  $Z_\theta=\int_{\mathbb R^n}\exp(E_\theta(x))\,dx$, it has Lebesgue density
  $Z_\theta^{-1}\exp(E_\theta(x))$. This is precisely the condition $h(x)=1$. -/)
  (title := /-- Unit-base polynomial exponential family -/)
  (latexEnv := "definition")]
def unit_base_polynomial_exponential_family {n : ℕ}
    (factors : Finset (polynomial_factor n)) (theta : polynomial_factor n → ℝ)
    (p : MeasureTheory.Measure (Fin n → ℝ)) : Prop :=
  ∃ Z : ℝ, 0 < Z ∧
    Z = ∫ x, Real.exp (exponential_energy factors theta x) ∂MeasureTheory.volume ∧
    p = MeasureTheory.Measure.withDensity MeasureTheory.volume
      (fun x => ENNReal.ofReal (Real.exp (exponential_energy factors theta x) / Z))

@[blueprint "def:tail-decay-condition"
  (statement := /-- Let $d\ge2$, let $k>0$, and let the integer $C_t$ satisfy
  $\max\{(\log 2/k)^{1/(d-1)},1\}\le C_t\le e^n$. A probability measure $p$ satisfies the
  required tail condition if
  $p\{x:\lVert x\rVert_\infty>s\}\le\exp(-k s^{d-1})$ for every real $s\ge C_t$.
  The norm on the finite product $\mathbb R^n$ is its supremum norm. -/)
  (title := /-- Exponential tail-decay condition -/)
  (latexEnv := "definition")]
def tail_decay_condition {n : ℕ} (d : ℕ) (tailRate : ℝ) (Ct : ℕ)
    (p : MeasureTheory.Measure (Fin n → ℝ)) : Prop :=
  0 < tailRate ∧ 2 ≤ d ∧
    max (Real.rpow (Real.log 2 / tailRate) (1 / ((d : ℝ) - 1))) 1 ≤ (Ct : ℝ) ∧
    (Ct : ℝ) ≤ Real.exp (n : ℝ) ∧
    ∀ s : ℝ, (Ct : ℝ) ≤ s →
      p.real {x | s < ‖x‖} ≤ Real.exp (-tailRate * s ^ (d - 1))

@[blueprint "def:iid-samples"
  (statement := /-- A family $(X_m)_{m=1}^M$ is sampled independently from $p$ when the random
  variables are jointly independent and every $X_m$ has distribution $p$. -/)
  (title := /-- Independent identically distributed samples -/)
  (latexEnv := "definition")]
def iid_samples {n M : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (mu : MeasureTheory.Measure Ω) (p : MeasureTheory.Measure (Fin n → ℝ))
    (samples : Fin M → Ω → (Fin n → ℝ)) : Prop :=
  ProbabilityTheory.iIndepFun samples mu ∧
    ∀ m, ProbabilityTheory.IdentDistrib (samples m) id mu p

@[blueprint "def:family-structure-sample-scale"
  (statement := /-- Fix an absolute real constant $A_0>1$ and a positive integer exponent
  constant $C$, independently of the degree $d$, the parameter bound $B$, the tail constant
  $C_t$, and the interaction order $w$. Put
  $\overline u=\max\{1+2^{-10},dBC_t^d\}$. A real number $M^*$ has the asserted scale relative
  to $(A_0,C)$ when $M^*\geq 1$ and
  $M^*\leq\max\{A_0,\overline u^{C d^2w}\}$. Thus the dimensionless base in the source's
  asymptotic notation is regularized below by a universal constant, rather than by an additional
  hypothesis on the model parameters. -/)
  (title := /-- Asymptotic sample-scale predicate -/)
  (latexEnv := "definition")]
def family_structure_sample_scale (A0 : ℝ) (C d : ℕ) (B : ℝ) (Ct w : ℕ)
    (Mstar : ℝ) : Prop :=
  1 < A0 ∧ 0 < C ∧ 1 ≤ Mstar ∧
    Mstar ≤ max A0 ((max (1 + (1 / 1024 : ℝ))
      ((d : ℝ) * B * (Ct : ℝ) ^ d)) ^ (C * d ^ 2 * w))

@[blueprint "def:family-structure-recovery-at-scale"
  (statement := /-- Fix the true family and a candidate scale $M^*$. The recovery guarantee at
  $M^*$ means the following uniformly over all later choices. For every $M$, every probability
  space, every $M$-tuple of independent samples from $p_{\theta^*}$, every constrained empirical
  minimizer selection $\widehat\theta$ for which
  $\omega\mapsto\widehat\theta_k(\omega)$ is measurable for every maximal factor $k$ adjacent to
  $i$, every $\rho\ge1$, and every $0<\epsilon\le1$, if
  $M\ge\rho n^{d+1}M^*/\epsilon^2$, then with probability greater than
  $1-(\rho nC_t)^{-1}$ one has
  $(\theta_k^*-\widehat\theta_k)^2\le\epsilon$ simultaneously for every maximal factor adjacent
  to $i$. -/)
  (title := /-- Uniform coefficient recovery at a fixed sample scale -/)
  (latexEnv := "definition")]
def family_structure_recovery_at_scale {n : ℕ} (d : ℕ)
    (factors : Finset (polynomial_factor n)) (thetaStar : polynomial_factor n → ℝ)
    (i : Fin n) (B : ℝ) (Ct : ℕ) (p : MeasureTheory.Measure (Fin n → ℝ))
    (Mstar : ℝ) : Prop :=
  ∀ (M : ℕ) (Ω : Type) [MeasurableSpace Ω]
    (mu : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure mu]
    (samples : Fin M → Ω → (Fin n → ℝ))
    (thetaHat : Ω → polynomial_factor n → ℝ)
    (rho epsilon : ℝ),
    iid_samples mu p samples →
    (∀ omega, constrained_empirical_minimizer factors B i
      (fun m => samples m omega) (thetaHat omega)) →
    (∀ factor ∈ incident_maximal_factors factors i,
      Measurable (fun omega => thetaHat omega factor)) →
    1 ≤ rho → 0 < epsilon → epsilon ≤ 1 →
    rho * (n : ℝ) ^ (d + 1) * Mstar / epsilon ^ 2 ≤ (M : ℝ) →
    1 - 1 / (rho * (n : ℝ) * (Ct : ℝ)) <
      mu.real {omega | ∀ factor ∈ incident_maximal_factors factors i,
        (thetaStar factor - thetaHat omega factor) ^ 2 ≤ epsilon}

@[blueprint "def:family-structure-conclusion"
  (statement := /-- For fixed absolute constants $A_0>1$ and $C>0$ and a fixed model, the
  family-structure conclusion asserts the existence of a scale $M^*$ satisfying
  $1\leq M^*\leq\max\{A_0,\overline u^{C d^2w}\}$, where
  $\overline u=\max\{1+2^{-10},dBC_t^d\}$, for which the uniform recovery guarantee in
  \cref{def:family-structure-recovery-at-scale} holds. -/)
  (title := /-- Packaged family-structure conclusion -/)
  (latexEnv := "definition")]
def family_structure_conclusion {n : ℕ} (A0 : ℝ) (C d : ℕ)
    (factors : Finset (polynomial_factor n)) (thetaStar : polynomial_factor n → ℝ)
    (i : Fin n) (B : ℝ) (Ct : ℕ) (p : MeasureTheory.Measure (Fin n → ℝ)) : Prop :=
  ∃ Mstar : ℝ,
    family_structure_sample_scale A0 C d B Ct (interaction_order factors) Mstar ∧
      family_structure_recovery_at_scale d factors thetaStar i B Ct p Mstar

@[blueprint "def:population-local-score-matching-loss"
  (statement := /-- The population local score-matching loss at the coordinate $i$ is the
  expectation
  \[
    \mathcal L_i(\theta)
      =\int_{\mathbb R^n}\mathcal L_i(\theta,x)\,dp_{\theta^*}(x)
  \]
  of the local Hyv\"arinen loss under the true distribution $p_{\theta^*}$. -/)
  (title := /-- Population local score-matching loss -/)
  (latexEnv := "definition")]
noncomputable def population_local_score_matching_loss {n : ℕ}
    (factors : Finset (polynomial_factor n)) (theta : polynomial_factor n → ℝ)
    (i : Fin n) (p : MeasureTheory.Measure (Fin n → ℝ)) : ℝ :=
  ∫ x, local_score_matching_loss factors theta i x ∂p

@[blueprint "lem:tail-decay-integrable-norm-pow"
  (statement := /-- Let $n,d,C_t,m\in\mathbb N$, let $k\in\mathbb R$, and let $p$ be a
  probability measure on $\mathbb R^n$. If $m>0$ and $p$ satisfies the tail-decay condition
  of \cref{def:tail-decay-condition} with parameters $(d,k,C_t)$, then
  $x\mapsto\lVert x\rVert^m$ is integrable with respect to $p$. -/)
  (proof := /-- For each $j\in\mathbb N$, let
  $A_j=\{x:\lceil\lVert x\rVert\rceil=j\}$. These sets cover $\mathbb R^n$, and
  $\lVert x\rVert^m\le j^m$ on $A_j$. If $j\le C_t$, bound $p(A_j)$ by one. If $j>C_t$, then
  $C_t\le j-1<\lVert x\rVert$ on $A_j$, so \cref{def:tail-decay-condition} gives

  \[
    p(A_j)\le \exp\bigl(-k(j-1)^{d-1}\bigr)
      \le \exp\bigl(-k(j-1)\bigr).
  \]

  The second inequality follows from $j-1\ge C_t\ge1$, $d-1\ge1$, and $k>0$. Consequently the
  lower integral of $\lVert x\rVert^m$ is bounded by a finite initial sum plus a constant multiple
  of $\sum_{j=0}^{\infty}j^m\exp(-kj)$, which converges because $k>0$. The norm power is
  nonnegative and strongly measurable, so finiteness of its lower integral proves its
  integrability with respect to $p$. -/)
  (title := /-- Polynomial moments from exponential tails -/)
  (latexEnv := "lemma")]
lemma tail_decay_integrable_norm_pow {n : ℕ} (d : ℕ) (tailRate : ℝ) (Ct m : ℕ)
    (p : MeasureTheory.Measure (Fin n → ℝ)) [MeasureTheory.IsProbabilityMeasure p]
    (htail : tail_decay_condition d tailRate Ct p) (hm : 0 < m) :
    MeasureTheory.Integrable (fun x : Fin n → ℝ => ‖x‖ ^ m) p := by
  rcases htail with ⟨htailRate, hd, hCt, hCtUpper, htail⟩
  have hCtOneReal : (1 : ℝ) ≤ (Ct : ℝ) :=
    (le_max_right _ _).trans hCt
  have hCtOne : 1 ≤ Ct := by exact_mod_cast hCtOneReal
  have hdegree : 0 < d - 1 := by omega
  let shell : ℕ → Set (Fin n → ℝ) := fun k => {x | ⌈‖x‖⌉₊ = k}
  let bound : ℕ → ℝ := fun k =>
    (if k ≤ Ct then (k : ℝ) ^ m else 0) +
      Real.exp tailRate * ((k : ℝ) ^ m * Real.exp (-tailRate * (k : ℝ)))
  have hprefix : Summable (fun k : ℕ => if k ≤ Ct then (k : ℝ) ^ m else 0) := by
    apply summable_of_finite_support
    refine (Set.finite_Iic Ct).subset ?_
    intro k hk
    simp only [Function.mem_support] at hk
    simp only [Set.mem_Iic]
    by_contra hle
    simp [hle] at hk
  have hdecay : Summable (fun k : ℕ =>
      Real.exp tailRate * ((k : ℝ) ^ m * Real.exp (-tailRate * (k : ℝ)))) :=
    (Real.summable_pow_mul_exp_neg_nat_mul m htailRate).mul_left _
  have hbound : Summable bound := by
    simpa [bound] using hprefix.add hdecay
  have hboundNonneg (k : ℕ) : 0 ≤ bound k := by
    dsimp [bound]
    positivity
  have hcover : (⋃ k, shell k) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, shell, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ⟨⌈‖x‖⌉₊, rfl⟩
  have hshell (k : ℕ) :
      (∫⁻ x in shell k, ENNReal.ofReal (‖x‖ ^ m) ∂p) ≤ ENNReal.ofReal (bound k) := by
    have hnorm (x : Fin n → ℝ) (hx : x ∈ shell k) : ‖x‖ ≤ (k : ℝ) := by
      have hle := Nat.le_ceil (‖x‖)
      change ⌈‖x‖⌉₊ = k at hx
      rwa [hx] at hle
    have hintegral :
        (∫⁻ x in shell k, ENNReal.ofReal (‖x‖ ^ m) ∂p) ≤
          ENNReal.ofReal ((k : ℝ) ^ m) * p (shell k) := by
      calc
        (∫⁻ x in shell k, ENNReal.ofReal (‖x‖ ^ m) ∂p) ≤
            ∫⁻ _x in shell k, ENNReal.ofReal ((k : ℝ) ^ m) ∂p := by
          apply MeasureTheory.setLIntegral_mono measurable_const
          intro x hx
          apply ENNReal.ofReal_le_ofReal
          exact pow_le_pow_left₀ (norm_nonneg x) (hnorm x hx) m
        _ = ENNReal.ofReal ((k : ℝ) ^ m) * p (shell k) :=
          MeasureTheory.setLIntegral_const _ _
    by_cases hk : k ≤ Ct
    · calc
        (∫⁻ x in shell k, ENNReal.ofReal (‖x‖ ^ m) ∂p) ≤
            ENNReal.ofReal ((k : ℝ) ^ m) * p (shell k) := hintegral
        _ ≤ ENNReal.ofReal ((k : ℝ) ^ m) := by
          simpa using mul_le_mul_left' (MeasureTheory.prob_le_one
            (μ := p) (s := shell k)) (ENNReal.ofReal ((k : ℝ) ^ m))
        _ ≤ ENNReal.ofReal (bound k) := by
          apply ENNReal.ofReal_le_ofReal
          dsimp [bound]
          simp only [if_pos hk]
          exact le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le
            (mul_nonneg (pow_nonneg (Nat.cast_nonneg k) m) (Real.exp_pos _).le))
    · have hCtThreshold : Ct ≤ k - 1 := by omega
      have hkPositive : 0 < k := by omega
      have hshellSubset : shell k ⊆
          {x : Fin n → ℝ | ((k - 1 : ℕ) : ℝ) < ‖x‖} := by
        intro x hx
        change ⌈‖x‖⌉₊ = k at hx
        change ((k - 1 : ℕ) : ℝ) < ‖x‖
        exact Nat.lt_ceil.mp (by rw [hx]; omega)
      have hmeasure : p (shell k) ≤
          ENNReal.ofReal (Real.exp (-tailRate * (((k - 1 : ℕ) : ℝ) ^ (d - 1)))) := by
        calc
          p (shell k) ≤ p {x : Fin n → ℝ | ((k - 1 : ℕ) : ℝ) < ‖x‖} :=
            MeasureTheory.measure_mono hshellSubset
          _ = ENNReal.ofReal
              (p.real {x : Fin n → ℝ | ((k - 1 : ℕ) : ℝ) < ‖x‖}) := by
            rw [MeasureTheory.ofReal_measureReal]
          _ ≤ ENNReal.ofReal
              (Real.exp (-tailRate * (((k - 1 : ℕ) : ℝ) ^ (d - 1)))) :=
            ENNReal.ofReal_le_ofReal (htail ((k - 1 : ℕ) : ℝ) (by exact_mod_cast hCtThreshold))
      have hpowerNat : k - 1 ≤ (k - 1) ^ (d - 1) := Nat.le_pow hdegree
      have hpowerReal : ((k - 1 : ℕ) : ℝ) ≤ (((k - 1 : ℕ) : ℝ) ^ (d - 1)) := by
        exact_mod_cast hpowerNat
      have hexp : Real.exp (-tailRate * (((k - 1 : ℕ) : ℝ) ^ (d - 1))) ≤
          Real.exp (-tailRate * ((k - 1 : ℕ) : ℝ)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonpos_left hpowerReal (by linarith)
      have hmeasureLinear : p (shell k) ≤
          ENNReal.ofReal (Real.exp (-tailRate * ((k - 1 : ℕ) : ℝ))) :=
        hmeasure.trans (ENNReal.ofReal_le_ofReal hexp)
      calc
        (∫⁻ x in shell k, ENNReal.ofReal (‖x‖ ^ m) ∂p) ≤
            ENNReal.ofReal ((k : ℝ) ^ m) * p (shell k) := hintegral
        _ ≤ ENNReal.ofReal ((k : ℝ) ^ m) *
            ENNReal.ofReal (Real.exp (-tailRate * ((k - 1 : ℕ) : ℝ))) :=
          mul_le_mul_left' hmeasureLinear _
        _ = ENNReal.ofReal (Real.exp tailRate *
            ((k : ℝ) ^ m * Real.exp (-tailRate * (k : ℝ)))) := by
          rw [← ENNReal.ofReal_mul (pow_nonneg (Nat.cast_nonneg k) m)]
          congr 1
          rw [Nat.cast_sub (by omega : 1 ≤ k)]
          norm_num only [Nat.cast_one]
          rw [show -tailRate * ((k : ℝ) - 1) = tailRate + -tailRate * (k : ℝ) by ring]
          rw [Real.exp_add]
          ring
        _ ≤ ENNReal.ofReal (bound k) := by
          apply ENNReal.ofReal_le_ofReal
          dsimp [bound]
          simp [hk]
  have hsumFinite : (∑' k, ENNReal.ofReal (bound k)) < (⊤ : ENNReal) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hboundNonneg hbound]
    simp
  have hintegralFinite :
      (∫⁻ x, ENNReal.ofReal (‖x‖ ^ m) ∂p) < (⊤ : ENNReal) := by
    refine lt_of_le_of_lt ?_ hsumFinite
    calc
      (∫⁻ x, ENNReal.ofReal (‖x‖ ^ m) ∂p) =
          ∫⁻ x in ⋃ k, shell k, ENNReal.ofReal (‖x‖ ^ m) ∂p := by
        rw [hcover]
        simp
      _ ≤ ∑' k, ∫⁻ x in shell k, ENNReal.ofReal (‖x‖ ^ m) ∂p :=
        MeasureTheory.lintegral_iUnion_le shell _
      _ ≤ ∑' k, ENNReal.ofReal (bound k) := ENNReal.tsum_le_tsum hshell
  have hmeasurable : MeasureTheory.AEStronglyMeasurable
      (fun x : Fin n → ℝ => ‖x‖ ^ m) p :=
    (continuous_norm.pow m).stronglyMeasurable.aestronglyMeasurable
  have hnonneg : 0 ≤ᵐ[p] (fun x : Fin n → ℝ => ‖x‖ ^ m) :=
    Filter.Eventually.of_forall fun x => pow_nonneg (norm_nonneg x) m
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeasurable hnonneg).mp
    (ne_of_lt hintegralFinite)

@[blueprint "lem:population-score-excess-identity"
  (statement := /-- Let $\mathcal K$ have degree at most $d$, let $p_{\theta^*}$ be the
  unit-base polynomial exponential family generated by $(\mathcal K,\theta^*)$, and suppose that
  $p_{\theta^*}$ satisfies the tail condition with parameters $(d,k,C_t)$. Then, for every
  parameter vector $\theta$ and every coordinate $i$,
  \[
    \mathcal L_i(\theta)-\mathcal L_i(\theta^*)
      =\frac12\int_{\mathbb R^n}
        \bigl(\partial_i E_{\theta-\theta^*}(x)\bigr)^2\,dp_{\theta^*}(x).
  \] -/)
  (proof := /-- Put $\Delta=\theta-\theta^*$. By
  \cref{def:population-local-score-matching-loss,def:local-score-matching-loss}, the difference
  of the two population losses is the integral of
  \[
    \partial_i^2E_\Delta+
    (\partial_iE_{\theta^*})(\partial_iE_\Delta)
    +\frac12(\partial_iE_\Delta)^2.
  \]
  Each monomial, each of its first two coordinate derivatives, and every product needed here is
  bounded by a fixed polynomial in $\lVert x\rVert$. Consequently
  \cref{lem:tail-decay-integrable-norm-pow}, applied using
  \cref{def:tail-decay-condition}, makes all of these functions integrable under
  $p_{\theta^*}$. Write the unit-base density from
  \cref{def:unit-base-polynomial-exponential-family} as
  $Z^{-1}\exp(E_{\theta^*})$. Direct coordinate differentiation shows that the derivative of

  \[
    x\longmapsto Z^{-1}\exp(E_{\theta^*}(x))\,\partial_iE_\Delta(x)
  \]
  is its density multiplied by
  $\partial_i^2E_\Delta+(\partial_iE_{\theta^*})(\partial_iE_\Delta)$.
  Separate the $i$th coordinate by the measure-preserving identification
  $\mathbb R^n\simeq\mathbb R\times\mathbb R^{n-1}$. Fubini's theorem makes the function and its
  derivative integrable on almost every one-dimensional fibre. The integral over each such fibre
  of the derivative is zero, and a second application of Fubini therefore gives
  \[
    \int\partial_i^2E_\Delta\,dp_{\theta^*}
      =-\int(\partial_iE_{\theta^*})(\partial_iE_\Delta)\,dp_{\theta^*}.
  \]
  Substitution cancels the first two displayed cross terms and leaves precisely one half of the
  integral of $(\partial_iE_\Delta)^2$. -/)
  (title := /-- Population score excess as a squared derivative -/)
  (latexEnv := "lemma")]
lemma population_score_excess_identity {n : ℕ} (d : ℕ)
    (factors : Finset (polynomial_factor n)) (thetaStar theta : polynomial_factor n → ℝ)
    (i : Fin n) (tailRate : ℝ) (Ct : ℕ) (p : MeasureTheory.Measure (Fin n → ℝ))
    [MeasureTheory.IsProbabilityMeasure p] :
    family_degree_at_most factors d →
    unit_base_polynomial_exponential_family factors thetaStar p →
    tail_decay_condition d tailRate Ct p →
    population_local_score_matching_loss factors theta i p -
        population_local_score_matching_loss factors thetaStar i p =
      (1 / 2 : ℝ) * ∫ x,
        (energy_first_partial factors
          (fun factor => theta factor - thetaStar factor) i x) ^ 2 ∂p := by
  intro hdegree hfamily htail
  have hmonomial_norm (factor : polynomial_factor n) (x : Fin n → ℝ) :
      ‖monomial_value factor x‖ ≤ max 1 ‖x‖ ^ (∑ j, factor j) := by
    calc
      ‖monomial_value factor x‖ ≤ ∏ j, ‖x j ^ factor j‖ := by
        exact Finset.norm_prod_le Finset.univ _
      _ ≤ ∏ j, (max 1 ‖x‖) ^ factor j := by
        apply Finset.prod_le_prod
        · intro j hj
          positivity
        · intro j hj
          rw [norm_pow]
          gcongr
          exact le_max_of_le_right (norm_le_pi_norm x j)
      _ = max 1 ‖x‖ ^ (∑ j, factor j) := by
        exact Finset.prod_pow_eq_pow_sum Finset.univ factor _
  have hfirst_as_monomial (factor : polynomial_factor n) (x : Fin n → ℝ) :
      monomial_first_partial factor i x =
        (factor i : ℝ) *
          monomial_value (Function.update factor i (factor i - 1)) x := by
    unfold monomial_first_partial monomial_value
    by_cases hzero : factor i = 0
    · simp [hzero]
    · have hcast : (factor i : ℝ) ≠ 0 := by exact_mod_cast hzero
      apply mul_left_cancel₀ hcast
      rw [mul_assoc]
      have hprod :
          (∏ j ∈ Finset.univ.erase i, x j ^ factor j) =
            ∏ j ∈ Finset.univ.erase i,
              x j ^ Function.update factor i (factor i - 1) j := by
        apply Finset.prod_congr rfl
        intro j hj
        simp [Function.update, Finset.ne_of_mem_erase hj]
      rw [← Finset.mul_prod_erase Finset.univ
        (fun j => x j ^ Function.update factor i (factor i - 1) j)
        (Finset.mem_univ i)]
      rw [Function.update_self, hprod]
  have hsecond_as_monomial (factor : polynomial_factor n) (x : Fin n → ℝ) :
      monomial_second_partial factor i x =
        (factor i : ℝ) * ((factor i - 1 : ℕ) : ℝ) *
          monomial_value (Function.update factor i (factor i - 2)) x := by
    unfold monomial_second_partial monomial_value
    have hprod :
        (∏ j ∈ Finset.univ.erase i, x j ^ factor j) =
          ∏ j ∈ Finset.univ.erase i,
            x j ^ Function.update factor i (factor i - 2) j := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [Function.update, Finset.ne_of_mem_erase hj]
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j => x j ^ Function.update factor i (factor i - 2) j)
      (Finset.mem_univ i)]
    rw [Function.update_self, hprod]
    ring
  have hsum_update (factor : polynomial_factor n) (k : ℕ) (hk : k ≤ factor i) :
      (∑ j, Function.update factor i k j) ≤ ∑ j, factor j := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
    have hsum : (∑ j, factor j) =
        factor i + ∑ j ∈ Finset.univ \ {i}, factor j := by
      exact Finset.sum_eq_add_sum_sdiff_singleton i factor (by simp)
    rw [hsum]
    exact Nat.add_le_add_right hk _
  have hmax_pow (r : ℝ) (hr : 0 ≤ r) (m : ℕ) :
      (max 1 r) ^ m ≤ 1 + r ^ (m + 1) := by
    rcases le_total r 1 with h | h
    · rw [max_eq_left h, one_pow]
      exact le_add_of_nonneg_right (pow_nonneg hr _)
    · rw [max_eq_right h]
      have hp : r ^ m ≤ r ^ (m + 1) :=
        pow_le_pow_right₀ h (Nat.le_succ m)
      linarith
  have hmoment (m : ℕ) :
      MeasureTheory.Integrable (fun x : Fin n → ℝ => 1 + ‖x‖ ^ (m + 1)) p := by
    exact (MeasureTheory.integrable_const (1 : ℝ)).add
      (tail_decay_integrable_norm_pow d tailRate Ct (m + 1) p htail (by omega))
  have hmonomial_integrable (factor : polynomial_factor n) :
      MeasureTheory.Integrable (monomial_value factor) p := by
    refine (hmoment (∑ j, factor j)).mono' ?_ ?_
    · have hcontinuous : Continuous (monomial_value factor) := by
        unfold monomial_value
        fun_prop
      exact hcontinuous.aestronglyMeasurable
    · filter_upwards with x
      exact (hmonomial_norm factor x).trans
        (hmax_pow ‖x‖ (norm_nonneg x) (∑ j, factor j))
  have hmonomial_mul_integrable (factor₁ factor₂ : polynomial_factor n) :
      MeasureTheory.Integrable
        (fun x => monomial_value factor₁ x * monomial_value factor₂ x) p := by
    convert hmonomial_integrable (fun j => factor₁ j + factor₂ j) using 1
    funext x
    simp only [monomial_value, pow_add, Finset.prod_mul_distrib]
  have hderiv_monomial (factor : polynomial_factor n) (x : Fin n → ℝ) (t : ℝ) :
      HasDerivAt (fun s => monomial_value factor (Function.update x i s))
        (monomial_first_partial factor i (Function.update x i t)) t := by
    have hfun :
        (fun s => monomial_value factor (Function.update x i s)) =
          fun s => s ^ factor i * ∏ j ∈ Finset.univ.erase i, x j ^ factor j := by
      funext s
      unfold monomial_value
      rw [← Finset.mul_prod_erase Finset.univ
        (fun j => Function.update x i s j ^ factor j) (Finset.mem_univ i)]
      rw [Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      simp [Function.update, Finset.ne_of_mem_erase hj]
    have hfirst_eval :
        monomial_first_partial factor i (Function.update x i t) =
          (factor i : ℝ) * t ^ (factor i - 1) *
            ∏ j ∈ Finset.univ.erase i, x j ^ factor j := by
      unfold monomial_first_partial
      rw [Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      simp [Function.update, Finset.ne_of_mem_erase hj]
    rw [hfun, hfirst_eval]
    exact (hasDerivAt_pow (factor i) t).mul_const
      (∏ j ∈ Finset.univ.erase i, x j ^ factor j)
  have henergy_first_integrable (parameter : polynomial_factor n → ℝ) :
      MeasureTheory.Integrable (energy_first_partial factors parameter i) p := by
    unfold energy_first_partial
    refine MeasureTheory.integrable_finsetSum factors ?_
    intro factor hfactor
    rw [show (fun x => parameter factor * monomial_first_partial factor i x) =
        fun x => (parameter factor * (factor i : ℝ)) *
          monomial_value (Function.update factor i (factor i - 1)) x by
      funext x
      rw [hfirst_as_monomial]
      ring]
    exact (hmonomial_integrable
      (Function.update factor i (factor i - 1))).const_mul _
  have henergy_second_integrable (parameter : polynomial_factor n → ℝ) :
      MeasureTheory.Integrable (energy_second_partial factors parameter i) p := by
    unfold energy_second_partial
    refine MeasureTheory.integrable_finsetSum factors ?_
    intro factor hfactor
    rw [show (fun x => parameter factor * monomial_second_partial factor i x) =
        fun x => (parameter factor * (factor i : ℝ) * ((factor i - 1 : ℕ) : ℝ)) *
          monomial_value (Function.update factor i (factor i - 2)) x by
      funext x
      rw [hsecond_as_monomial]
      ring]
    exact (hmonomial_integrable
      (Function.update factor i (factor i - 2))).const_mul _
  have henergy_first_mul_integrable
      (parameter₁ parameter₂ : polynomial_factor n → ℝ) :
      MeasureTheory.Integrable (fun x =>
        energy_first_partial factors parameter₁ i x *
          energy_first_partial factors parameter₂ i x) p := by
    simp_rw [energy_first_partial, Finset.sum_mul, Finset.mul_sum]
    refine MeasureTheory.integrable_finsetSum factors ?_
    intro factor₁ hfactor₁
    refine MeasureTheory.integrable_finsetSum factors ?_
    intro factor₂ hfactor₂
    rw [show (fun x =>
        parameter₁ factor₁ * monomial_first_partial factor₁ i x *
          (parameter₂ factor₂ * monomial_first_partial factor₂ i x)) =
        fun x =>
          (parameter₁ factor₁ * (factor₁ i : ℝ) *
            (parameter₂ factor₂ * (factor₂ i : ℝ))) *
          (monomial_value (Function.update factor₁ i (factor₁ i - 1)) x *
            monomial_value (Function.update factor₂ i (factor₂ i - 1)) x) by
      funext x
      rw [hfirst_as_monomial, hfirst_as_monomial]
      ring]
    exact (hmonomial_mul_integrable
      (Function.update factor₁ i (factor₁ i - 1))
      (Function.update factor₂ i (factor₂ i - 1))).const_mul _
  have hderiv_energy (parameter : polynomial_factor n → ℝ)
      (x : Fin n → ℝ) (t : ℝ) :
      HasDerivAt (fun s =>
        exponential_energy factors parameter (Function.update x i s))
        (energy_first_partial factors parameter i (Function.update x i t)) t := by
    unfold exponential_energy energy_first_partial
    have hsumfun :
        (fun s => ∑ factor ∈ factors,
          parameter factor * monomial_value factor (Function.update x i s)) =
        ∑ factor ∈ factors, fun s =>
          parameter factor * monomial_value factor (Function.update x i s) := by
      funext s
      simp
    rw [hsumfun]
    exact HasDerivAt.sum (u := factors) (fun factor hfactor =>
      (hderiv_monomial factor x t).const_mul (parameter factor))
  have hderiv_first_monomial (factor : polynomial_factor n)
      (x : Fin n → ℝ) (t : ℝ) :
      HasDerivAt (fun s =>
        monomial_first_partial factor i (Function.update x i s))
        (monomial_second_partial factor i (Function.update x i t)) t := by
    have hfun :
        (fun s => monomial_first_partial factor i (Function.update x i s)) =
          fun s => (factor i : ℝ) *
            monomial_value (Function.update factor i (factor i - 1))
              (Function.update x i s) := by
      funext s
      rw [hfirst_as_monomial]
    have hvalue :
        monomial_second_partial factor i (Function.update x i t) =
          (factor i : ℝ) *
            monomial_first_partial (Function.update factor i (factor i - 1)) i
              (Function.update x i t) := by
      rw [hsecond_as_monomial, hfirst_as_monomial]
      simp [Function.update, Nat.sub_sub, mul_assoc]
    rw [hfun, hvalue]
    exact (hderiv_monomial
      (Function.update factor i (factor i - 1)) x t).const_mul (factor i : ℝ)
  have hderiv_energy_first (parameter : polynomial_factor n → ℝ)
      (x : Fin n → ℝ) (t : ℝ) :
      HasDerivAt (fun s =>
        energy_first_partial factors parameter i (Function.update x i s))
        (energy_second_partial factors parameter i (Function.update x i t)) t := by
    unfold energy_first_partial energy_second_partial
    have hsumfun :
        (fun s => ∑ factor ∈ factors,
          parameter factor * monomial_first_partial factor i (Function.update x i s)) =
        ∑ factor ∈ factors, fun s =>
          parameter factor * monomial_first_partial factor i (Function.update x i s) := by
      funext s
      simp
    rw [hsumfun]
    exact HasDerivAt.sum (u := factors) (fun factor hfactor =>
      (hderiv_first_monomial factor x t).const_mul (parameter factor))
  let delta : polynomial_factor n → ℝ := fun factor =>
    theta factor - thetaStar factor
  have hdelta_square_integrable :
      MeasureTheory.Integrable (fun x =>
        energy_first_partial factors delta i x ^ 2) p := by
    simpa only [pow_two] using henergy_first_mul_integrable delta delta
  have hcross_integrable :
      MeasureTheory.Integrable (fun x =>
        energy_second_partial factors delta i x +
          energy_first_partial factors thetaStar i x *
            energy_first_partial factors delta i x) p :=
    (henergy_second_integrable delta).add
      (henergy_first_mul_integrable thetaStar delta)
  rcases hfamily with ⟨Z, hZ, hnormalization, hp⟩
  let density : (Fin n → ℝ) → ENNReal := fun x =>
    ENNReal.ofReal (Real.exp (exponential_energy factors thetaStar x) / Z)
  have hdensity_measurable : Measurable density := by
    unfold density exponential_energy monomial_value
    fun_prop
  have hdensity_lt_top : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)),
      density x < ⊤ := by
    filter_upwards with x
    simp [density]
  have hdensity_toReal (x : Fin n → ℝ) :
      (density x).toReal =
        Real.exp (exponential_energy factors thetaStar x) / Z := by
    simp [density, div_nonneg (Real.exp_pos _).le hZ.le]
  have hweighted_cross_integrable :
      MeasureTheory.Integrable (fun x =>
        (Real.exp (exponential_energy factors thetaStar x) / Z) *
          (energy_second_partial factors delta i x +
            energy_first_partial factors thetaStar i x *
              energy_first_partial factors delta i x))
        (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) := by
    have h := (MeasureTheory.integrable_withDensity_iff
      hdensity_measurable hdensity_lt_top).mp
      (show MeasureTheory.Integrable (fun x =>
          energy_second_partial factors delta i x +
            energy_first_partial factors thetaStar i x *
              energy_first_partial factors delta i x)
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)).withDensity density) from
          hp ▸ hcross_integrable)
    simpa only [hdensity_toReal, mul_comm] using h
  have hweighted_delta_integrable :
      MeasureTheory.Integrable (fun x =>
        (Real.exp (exponential_energy factors thetaStar x) / Z) *
          energy_first_partial factors delta i x)
        (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) := by
    have h := (MeasureTheory.integrable_withDensity_iff
      hdensity_measurable hdensity_lt_top).mp
      (show MeasureTheory.Integrable (energy_first_partial factors delta i)
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)).withDensity density) from
          hp ▸ henergy_first_integrable delta)
    simpa only [hdensity_toReal, mul_comm] using h
  have hderiv_weighted_delta (x : Fin n → ℝ) (t : ℝ) :
      HasDerivAt (fun s =>
        (Real.exp (exponential_energy factors thetaStar (Function.update x i s)) / Z) *
          energy_first_partial factors delta i (Function.update x i s))
        ((Real.exp (exponential_energy factors thetaStar (Function.update x i t)) / Z) *
          (energy_second_partial factors delta i (Function.update x i t) +
            energy_first_partial factors thetaStar i (Function.update x i t) *
              energy_first_partial factors delta i (Function.update x i t))) t := by
    have hleft := ((hderiv_energy thetaStar x t).exp).div_const Z
    have hright := hderiv_energy_first delta x t
    convert hleft.mul hright using 1 <;> first | rfl | ring
  have hweighted_cross_zero :
      ∫ x,
        (Real.exp (exponential_energy factors thetaStar x) / Z) *
          (energy_second_partial factors delta i x +
            energy_first_partial factors thetaStar i x *
              energy_first_partial factors delta i x)
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) = 0 := by
    cases n with
    | zero => exact Fin.elim0 i
    | succ m =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i
      have he_update (t : ℝ) (y : Fin m → ℝ) :
          e.symm (t, y) = Function.update (e.symm (0, y)) i t := by
        change i.insertNth t y =
          Function.update (i.insertNth (0 : ℝ) y : Fin (m + 1) → ℝ) i t
        rw [Fin.update_insertNth]
      let weightedDelta : (Fin (m + 1) → ℝ) → ℝ := fun x =>
        (Real.exp (exponential_energy factors thetaStar x) / Z) *
          energy_first_partial factors delta i x
      let weightedCross : (Fin (m + 1) → ℝ) → ℝ := fun x =>
        (Real.exp (exponential_energy factors thetaStar x) / Z) *
          (energy_second_partial factors delta i x +
            energy_first_partial factors thetaStar i x *
              energy_first_partial factors delta i x)
      have hpres :=
        (MeasureTheory.volume_preserving_piFinSuccAbove
          (fun _ : Fin (m + 1) => ℝ) i).symm
      have hweightedDelta_comp_integrable :
          MeasureTheory.Integrable (weightedDelta ∘ e.symm)
            (MeasureTheory.volume : MeasureTheory.Measure (ℝ × (Fin m → ℝ))) :=
        (hpres.integrable_comp hweighted_delta_integrable.aestronglyMeasurable).2
          hweighted_delta_integrable
      have hweightedCross_comp_integrable :
          MeasureTheory.Integrable (weightedCross ∘ e.symm)
            (MeasureTheory.volume : MeasureTheory.Measure (ℝ × (Fin m → ℝ))) :=
        (hpres.integrable_comp hweighted_cross_integrable.aestronglyMeasurable).2
          hweighted_cross_integrable
      have hweightedDelta_slice_integrable :
          ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)),
            MeasureTheory.Integrable (fun t => weightedDelta (e.symm (t, y)))
              (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
        simpa only [Function.comp_apply] using
          ((MeasureTheory.integrable_prod_iff'
            hweightedDelta_comp_integrable.aestronglyMeasurable).1
              hweightedDelta_comp_integrable).1
      have hweightedCross_slice_integrable :
          ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)),
            MeasureTheory.Integrable (fun t => weightedCross (e.symm (t, y)))
              (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
        simpa only [Function.comp_apply] using
          ((MeasureTheory.integrable_prod_iff'
            hweightedCross_comp_integrable.aestronglyMeasurable).1
              hweightedCross_comp_integrable).1
      have hslice_zero :
          ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)),
            ∫ t, weightedCross (e.symm (t, y)) = 0 := by
        filter_upwards [hweightedDelta_slice_integrable,
          hweightedCross_slice_integrable] with y hdelta_slice hcross_slice
        apply MeasureTheory.integral_eq_zero_of_hasDerivAt_of_integrable
          (f := fun t => weightedDelta (e.symm (t, y)))
        · intro t
          have hfun :
              (fun s => weightedDelta (e.symm (s, y))) = fun s =>
                (Real.exp (exponential_energy factors thetaStar
                    (Function.update (e.symm (0, y)) i s)) / Z) *
                  energy_first_partial factors delta i
                    (Function.update (e.symm (0, y)) i s) := by
            funext s
            rw [he_update]
          have hvalue :
              weightedCross (e.symm (t, y)) =
                (Real.exp (exponential_energy factors thetaStar
                    (Function.update (e.symm (0, y)) i t)) / Z) *
                  (energy_second_partial factors delta i
                      (Function.update (e.symm (0, y)) i t) +
                    energy_first_partial factors thetaStar i
                        (Function.update (e.symm (0, y)) i t) *
                      energy_first_partial factors delta i
                        (Function.update (e.symm (0, y)) i t)) := by
            rw [he_update]
          rw [hfun, hvalue]
          exact hderiv_weighted_delta (e.symm (0, y)) t
        · exact hcross_slice
        · exact hdelta_slice
      calc
        ∫ x, weightedCross x
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin (m + 1) → ℝ)) =
            ∫ z, weightedCross (e.symm z)
              ∂(MeasureTheory.volume : MeasureTheory.Measure (ℝ × (Fin m → ℝ))) := by
                symm
                exact hpres.integral_comp' weightedCross
        _ = ∫ y, ∫ t, weightedCross (e.symm (t, y)) := by
          exact MeasureTheory.integral_prod_symm _ hweightedCross_comp_integrable
        _ = 0 := by
          rw [MeasureTheory.integral_congr_ae hslice_zero]
          rw [MeasureTheory.integral_zero]
  have hp_density :
      p = (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)).withDensity density := by
    simpa only [density] using hp
  have hcross_zero :
      (∫ x,
        energy_second_partial factors delta i x +
          energy_first_partial factors thetaStar i x *
            energy_first_partial factors delta i x ∂p) = 0 := by
    rw [hp_density, integral_withDensity_eq_integral_toReal_smul
      hdensity_measurable hdensity_lt_top]
    simpa only [hdensity_toReal, smul_eq_mul] using hweighted_cross_zero
  have hfirst_split (x : Fin n → ℝ) :
      energy_first_partial factors theta i x =
        energy_first_partial factors thetaStar i x +
          energy_first_partial factors delta i x := by
    unfold energy_first_partial delta
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    ring
  have hsecond_split (x : Fin n → ℝ) :
      energy_second_partial factors theta i x =
        energy_second_partial factors thetaStar i x +
          energy_second_partial factors delta i x := by
    unfold energy_second_partial delta
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    ring
  have hlocal_integrable (parameter : polynomial_factor n → ℝ) :
      MeasureTheory.Integrable (local_score_matching_loss factors parameter i) p := by
    unfold local_score_matching_loss
    apply (henergy_second_integrable parameter).add
    have hsquare : MeasureTheory.Integrable (fun x =>
        energy_first_partial factors parameter i x ^ 2) p := by
      simpa only [pow_two] using henergy_first_mul_integrable parameter parameter
    exact hsquare.const_mul (1 / 2 : ℝ)
  have hloss_diff (x : Fin n → ℝ) :
      local_score_matching_loss factors theta i x -
          local_score_matching_loss factors thetaStar i x =
        (energy_second_partial factors delta i x +
          energy_first_partial factors thetaStar i x *
            energy_first_partial factors delta i x) +
          (1 / 2 : ℝ) * energy_first_partial factors delta i x ^ 2 := by
    unfold local_score_matching_loss
    rw [hfirst_split, hsecond_split]
    ring
  calc
    population_local_score_matching_loss factors theta i p -
        population_local_score_matching_loss factors thetaStar i p =
        ∫ x, local_score_matching_loss factors theta i x -
          local_score_matching_loss factors thetaStar i x ∂p := by
      unfold population_local_score_matching_loss
      rw [MeasureTheory.integral_sub (hlocal_integrable theta)
        (hlocal_integrable thetaStar)]
    _ = ∫ x,
        (energy_second_partial factors delta i x +
          energy_first_partial factors thetaStar i x *
            energy_first_partial factors delta i x) +
          (1 / 2 : ℝ) * energy_first_partial factors delta i x ^ 2 ∂p := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      exact hloss_diff x
    _ = (∫ x,
          energy_second_partial factors delta i x +
            energy_first_partial factors thetaStar i x *
              energy_first_partial factors delta i x ∂p) +
        ∫ x, (1 / 2 : ℝ) * energy_first_partial factors delta i x ^ 2 ∂p := by
      rw [MeasureTheory.integral_add hcross_integrable
        (hdelta_square_integrable.const_mul (1 / 2 : ℝ))]
    _ = (1 / 2 : ℝ) * ∫ x, energy_first_partial factors delta i x ^ 2 ∂p := by
      rw [hcross_zero, MeasureTheory.integral_const_mul]
      ring
    _ = (1 / 2 : ℝ) * ∫ x,
        energy_first_partial factors
          (fun factor => theta factor - thetaStar factor) i x ^ 2 ∂p := by
      rfl

@[blueprint "lem:univariate-polynomial-interval-sampling"
  (statement := /-- Let $d$ be a positive integer, let $a,h\in\mathbb R$ with $h>0$, and let
  $f:\mathbb R\to\mathbb R$ be continuous and nonnegative. There are points
  $x_0,\ldots,x_{d-1}\in[a,a+h]$, separated pairwise by at least $h/(3d)$, such that
  \[
    \sum_{i<d}f(x_i)\leq \frac{3d}{h}\int_{[a,a+h]}f(t)\,dt.
  \] -/)
  (proof := /-- Divide $[a,a+h]$ into $d$ equal pieces and, in each piece, retain the
  closed middle third. Each retained interval has measure $h/(3d)$, distinct retained
  intervals are separated by at least $h/(3d)$, and their union lies in $[a,a+h]$.
  On each retained interval, the first-moment inequality supplies a point at which $f$ is
  at most its average. Summing these inequalities, using additivity over the pairwise
  disjoint retained intervals and monotonicity of the integral of the nonnegative function
  $f$, proves the claim. -/)
  (title := /-- Separated interval samples controlled by an integral -/)
  (latexEnv := "lemma")]
lemma univariate_polynomial_interval_sampling :
    ∀ (d : ℕ), 0 < d →
      ∀ (a h : ℝ) (f : ℝ → ℝ),
        0 < h → Continuous f → (∀ t, 0 ≤ f t) →
        ∃ x : Fin d → ℝ,
          (∀ i, x i ∈ Set.Icc a (a + h)) ∧
          (∀ i j, i ≠ j → h / (3 * (d : ℝ)) ≤ |x i - x j|) ∧
          ∑ i, f (x i) ≤
            (3 * (d : ℝ) / h) * ∫ t in Set.Icc a (a + h), f t ∂MeasureTheory.volume := by
  intro d hd a h f hh hfcont hfnonneg
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  let δ : ℝ := h / (3 * (d : ℝ))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  let L : Fin d → ℝ := fun i => a + (3 * (i.val : ℝ) + 1) * δ
  let R : Fin d → ℝ := fun i => a + (3 * (i.val : ℝ) + 2) * δ
  let S : Fin d → Set ℝ := fun i => Set.Icc (L i) (R i)
  have hRL (i : Fin d) : R i - L i = δ := by
    dsimp [L, R]
    ring
  have hLR (i : Fin d) : L i ≤ R i := by
    linarith [hRL i]
  have hSsub (i : Fin d) : S i ⊆ Set.Icc a (a + h) := by
    intro t ht
    have hi : (i.val : ℝ) + 1 ≤ d := by
      exact_mod_cast i.isLt
    have hcoef : 3 * (i.val : ℝ) + 2 ≤ 3 * (d : ℝ) := by linarith
    have hscale : (3 * (i.val : ℝ) + 2) * δ ≤ h := by
      calc
        (3 * (i.val : ℝ) + 2) * δ ≤ (3 * (d : ℝ)) * δ :=
          mul_le_mul_of_nonneg_right hcoef hδ.le
        _ = h := by
          dsimp [δ]
          field_simp
    change L i ≤ t ∧ t ≤ R i at ht
    change a ≤ t ∧ t ≤ a + h
    constructor
    · calc
        a ≤ L i := by
          dsimp [L]
          nlinarith
        _ ≤ t := ht.1
    · calc
        t ≤ R i := ht.2
        _ ≤ a + h := by
          dsimp [R]
          linarith
  have hdisj : Set.Pairwise (Set.univ : Set (Fin d))
      (fun i j => Disjoint (S i) (S j)) := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · apply Set.disjoint_left.2
      intro t hit hjt
      have hijR : R i < L j := by
        have hc : (i.val : ℝ) + 1 ≤ j.val := by
          exact_mod_cast hijlt
        dsimp [L, R]
        nlinarith
      exact (not_lt_of_ge hjt.1) (lt_of_le_of_lt hit.2 hijR)
    · apply Set.disjoint_left.2
      intro t hit hjt
      have hjiR : R j < L i := by
        have hc : (j.val : ℝ) + 1 ≤ i.val := by
          exact_mod_cast hjilt
        dsimp [L, R]
        nlinarith
      exact (not_lt_of_ge hit.1) (lt_of_le_of_lt hjt.2 hjiR)
  have havg (i : Fin d) :
      ∃ t ∈ S i, f t ≤ (3 * (d : ℝ) / h) * ∫ u in S i, f u ∂MeasureTheory.volume := by
    have hμ0 : MeasureTheory.volume (S i) ≠ 0 := by
      simp [S, Real.volume_Icc, hRL i, hδ]
    have hμtop : MeasureTheory.volume (S i) ≠ ⊤ := by simp [S, Real.volume_Icc]
    have hfint : MeasureTheory.IntegrableOn f (S i) MeasureTheory.volume := by
      exact hfcont.integrableOn_Icc
    obtain ⟨t, ht, htle⟩ := MeasureTheory.exists_le_setAverage hμ0 hμtop hfint
    refine ⟨t, ht, ?_⟩
    rw [MeasureTheory.setAverage_eq, Real.volume_real_Icc_of_le (hLR i), hRL i] at htle
    have hinv : δ⁻¹ = 3 * (d : ℝ) / h := by
      dsimp [δ]
      field_simp
    simpa [hinv] using htle
  choose x hxS hxf using havg
  refine ⟨x, fun i => hSsub i (hxS i), ?_, ?_⟩
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · have hc : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hijlt
      have hgap : x i + δ ≤ x j := by
        have hiR := (hxS i).2
        have hjL := (hxS j).1
        dsimp [L, R] at hiR hjL
        nlinarith
      rw [abs_of_nonpos (by linarith : x i - x j ≤ 0)]
      dsimp [δ] at hgap ⊢
      linarith
    · have hc : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast hjilt
      have hgap : x j + δ ≤ x i := by
        have hjR := (hxS j).2
        have hiL := (hxS i).1
        dsimp [L, R] at hjR hiL
        nlinarith
      rw [abs_of_nonneg (by linarith : 0 ≤ x i - x j)]
      dsimp [δ] at hgap ⊢
      linarith
  · have hsumint :
        (∑ i, ∫ u in S i, f u ∂MeasureTheory.volume) =
          ∫ u in ⋃ i, S i, f u ∂MeasureTheory.volume := by
      symm
      simpa using MeasureTheory.integral_biUnion_finset (f := f) (μ := MeasureTheory.volume)
        Finset.univ
        (fun i _ => measurableSet_Icc)
        (by simpa using hdisj)
        (fun i _ => hfcont.integrableOn_Icc)
    have hUsub : (⋃ i, S i) ⊆ Set.Icc a (a + h) :=
      Set.iUnion_subset fun i => hSsub i
    have hmono :
        (∫ u in ⋃ i, S i, f u ∂MeasureTheory.volume) ≤
          ∫ u in Set.Icc a (a + h), f u ∂MeasureTheory.volume := by
      apply MeasureTheory.setIntegral_mono_set hfcont.integrableOn_Icc
      · exact Filter.Eventually.of_forall fun t => hfnonneg t
      · exact Filter.Eventually.of_forall fun t ht => hUsub ht
    have hfactor : 0 ≤ 3 * (d : ℝ) / h := by positivity
    calc
      ∑ i, f (x i) ≤
          ∑ i, (3 * (d : ℝ) / h) * ∫ u in S i, f u ∂MeasureTheory.volume :=
        Finset.sum_le_sum fun i _ => hxf i
      _ = (3 * (d : ℝ) / h) *
          ∑ i, ∫ u in S i, f u ∂MeasureTheory.volume := by
        rw [Finset.mul_sum]
      _ = (3 * (d : ℝ) / h) *
          ∫ u in ⋃ i, S i, f u ∂MeasureTheory.volume := by rw [hsumint]
      _ ≤ (3 * (d : ℝ) / h) *
          ∫ u in Set.Icc a (a + h), f u ∂MeasureTheory.volume :=
        mul_le_mul_of_nonneg_left hmono hfactor

@[blueprint "lem:univariate-polynomial-esymm-bound"
  (statement := /-- Let $s$ be a finite multiset of real numbers, let $C\geq0$, and suppose
  $|z|\leq C$ for every $z\in s$. For every nonnegative integer $k$,
  \[
    |e_k(s)|\leq 2^{|s|}C^k,
  \]
  where $e_k$ is the $k$th elementary symmetric function. -/)
  (proof := /-- Expand $e_k(s)$ as the sum of the products over all $k$-element
  submultisets. Each product has absolute value at most $C^k$. The number of summands is
  $\binom{|s|}{k}$, which is at most $2^{|s|}$. The triangle inequality gives the result. -/)
  (title := /-- A uniform bound for elementary symmetric functions -/)
  (latexEnv := "lemma")]
lemma univariate_polynomial_esymm_bound (s : Multiset ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hs : ∀ z ∈ s, |z| ≤ C) (k : ℕ) :
    |s.esymm k| ≤ (2 : ℝ) ^ s.card * C ^ k := by
  have hprod : ∀ t : Multiset ℝ, (∀ z ∈ t, |z| ≤ C) → |t.prod| ≤ C ^ t.card := by
    intro t
    induction t using Multiset.induction_on with
    | empty => simp
    | @cons z t ih =>
        intro hzt
        rw [Multiset.prod_cons, abs_mul, Multiset.card_cons]
        calc
          |z| * |t.prod| ≤ C * C ^ t.card :=
            mul_le_mul (hzt z (by simp)) (ih (fun w hw => hzt w (by simp [hw])))
              (abs_nonneg _) hC
          _ = C ^ (t.card + 1) := by rw [pow_succ]; ring
  rw [Multiset.esymm]
  calc
    |((s.powersetCard k).map Multiset.prod).sum| ≤
        (((s.powersetCard k).map Multiset.prod).map abs).sum :=
      Multiset.abs_sum_le_sum_abs
    _ ≤ ((s.powersetCard k).map fun _ => C ^ k).sum := by
      rw [Multiset.map_map]
      apply Multiset.sum_map_le_sum_map
      intro t ht
      rw [Multiset.mem_powersetCard] at ht
      rw [ht.2.symm]
      exact hprod t fun z hz => hs z (Multiset.mem_of_le ht.1 hz)
    _ = (s.card.choose k : ℝ) * C ^ k := by simp
    _ ≤ (2 : ℝ) ^ s.card * C ^ k := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_two_pow s.card k)
        (pow_nonneg hC k)

@[blueprint "lem:univariate-polynomial-lagrange-coefficient-bound"
  (statement := /-- Let $d$ be a positive integer, let $C\geq1$ and $\delta>0$, and let
  $x_0,\ldots,x_{d-1}\in[-C,C]$ be pairwise separated by at least $\delta$. For real
  coefficients $(c_j)_{j<d}$ and every $r<d$,
  \[
    |c_r|^2\leq d\left(2^{d-1}C^{d-1-r}\delta^{-(d-1)}\right)^2
      \sum_{i<d}\left|\sum_{j<d}c_jx_i^j\right|^2.
  \] -/)
  (proof := /-- Form the polynomial $q(X)=\sum_{j<d}c_jX^j$ and interpolate it at the
  $d$ distinct nodes. The numerator of each Lagrange basis polynomial is a product of
  $d-1$ factors $X-x_j$. Its coefficient of degree $r$ is, up to sign, the
  $(d-1-r)$th elementary symmetric function of the omitted nodes, so
  \cref{lem:univariate-polynomial-esymm-bound} bounds it by
  $2^{d-1}C^{d-1-r}$. The denominator is at least $\delta^{d-1}$ in absolute value.
  Taking the coefficient of degree $r$ in the interpolation identity and applying
  Cauchy--Schwarz to the resulting sum proves the estimate. -/)
  (title := /-- Lagrange interpolation bound for one coefficient -/)
  (latexEnv := "lemma")]
lemma univariate_polynomial_lagrange_coefficient_bound :
    ∀ (d : ℕ), 0 < d →
      ∀ (C δ : ℝ) (x : Fin d → ℝ) (coeff : Fin d → ℝ) (r : Fin d),
        1 ≤ C → 0 < δ → (∀ i, |x i| ≤ C) →
        (∀ i j, i ≠ j → δ ≤ |x i - x j|) →
        |coeff r| ^ 2 ≤
          (d : ℝ) *
            ((2 : ℝ) ^ (d - 1) * C ^ (d - 1 - r.val) * δ⁻¹ ^ (d - 1)) ^ 2 *
            ∑ i, |∑ j, coeff j * (x i) ^ j.val| ^ 2 := by
  intro d hd C δ x coeff r hC hδ hxbound hxsep
  classical
  let p : Polynomial ℝ := ∑ j : Fin d, Polynomial.C (coeff j) * Polynomial.X ^ j.val
  have hpcoeff (j : Fin d) : p.coeff j.val = coeff j := by
    rw [show p = ∑ b : Fin d, Polynomial.C (coeff b) * Polynomial.X ^ b.val by rfl]
    simp only [Polynomial.finsetSum_coeff]
    simp_rw [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b hb hbj
      have hv : j.val ≠ b.val := by
        intro hv
        exact hbj (Fin.ext hv.symm)
      simp [hv]
    · simp
  have hpeval (t : ℝ) : p.eval t = ∑ j, coeff j * t ^ j.val := by
    rw [show p = ∑ j : Fin d, Polynomial.C (coeff j) * Polynomial.X ^ j.val by rfl]
    rw [Polynomial.eval_finset_sum]
    simp
  have hpdeg : p.degree < d := by
    simpa [p] using Polynomial.degree_sum_fin_lt coeff
  have hinj : Set.InjOn x (↑(Finset.univ : Finset (Fin d)) : Set (Fin d)) := by
    intro i hi j hj hij
    by_contra hne
    have hpos := hxsep i j hne
    rw [hij, sub_self, abs_zero] at hpos
    linarith
  have hpinterp : p = Lagrange.interpolate Finset.univ x fun i => p.eval (x i) :=
    Lagrange.eq_interpolate hinj (by simpa using hpdeg)
  let B : ℝ :=
    (2 : ℝ) ^ (d - 1) * C ^ (d - 1 - r.val) * δ⁻¹ ^ (d - 1)
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hbasis (i : Fin d) : |(Lagrange.basis Finset.univ x i).coeff r.val| ≤ B := by
    let s : Multiset ℝ := (Finset.univ.erase i).val.map x
    have hcard : s.card = d - 1 := by
      simp [s, hd]
    have hsbound : ∀ z ∈ s, |z| ≤ C := by
      intro z hz
      simp only [s, Multiset.mem_map, Finset.mem_val, Finset.mem_erase] at hz
      obtain ⟨j, hj, rfl⟩ := hz
      exact hxbound j
    have hrle : r.val ≤ s.card := by
      rw [hcard]
      omega
    have hnum :
        |((s.map fun z => Polynomial.X - Polynomial.C z).prod).coeff r.val| ≤
          (2 : ℝ) ^ (d - 1) * C ^ (d - 1 - r.val) := by
      rw [Multiset.prod_X_sub_C_coeff s hrle, abs_mul]
      have hsign : |(-1 : ℝ) ^ (s.card - r.val)| = 1 := by
        rw [abs_pow, abs_neg, abs_one, one_pow]
      rw [hsign, one_mul]
      simpa [hcard] using
        univariate_polynomial_esymm_bound s C (by linarith) hsbound (s.card - r.val)
    have hinv (j : Fin d) (hj : j ∈ Finset.univ.erase i) :
        |(x i - x j)⁻¹| ≤ δ⁻¹ := by
      have hne : i ≠ j := by
        exact (Finset.mem_erase.mp hj).1.symm
      have hsep := hxsep i j hne
      have habs : 0 < |x i - x j| := lt_of_lt_of_le hδ hsep
      rw [abs_inv]
      exact (inv_le_inv₀ habs hδ).2 hsep
    have hden :
        |∏ j ∈ Finset.univ.erase i, (x i - x j)⁻¹| ≤ δ⁻¹ ^ (d - 1) := by
      rw [Finset.abs_prod]
      calc
        ∏ j ∈ Finset.univ.erase i, |(x i - x j)⁻¹| ≤
            ∏ _j ∈ Finset.univ.erase i, δ⁻¹ := by
          gcongr with j hj
          exact hinv j hj
        _ = δ⁻¹ ^ (d - 1) := by simp [hd]
    have hbform :
        (Lagrange.basis Finset.univ x i).coeff r.val =
          (∏ j ∈ Finset.univ.erase i, (x i - x j)⁻¹) *
            (∏ j ∈ Finset.univ.erase i,
              (Polynomial.X - Polynomial.C (x j))).coeff r.val := by
      rw [Lagrange.basis]
      simp only [Lagrange.basisDivisor]
      rw [Finset.prod_mul_distrib]
      simp only [← map_prod]
      simp
    rw [hbform, abs_mul]
    have hnum' :
        |(∏ j ∈ Finset.univ.erase i,
            (Polynomial.X - Polynomial.C (x j))).coeff r.val| ≤
          (2 : ℝ) ^ (d - 1) * C ^ (d - 1 - r.val) := by
      have hsprod :
          (s.map fun z => Polynomial.X - Polynomial.C z).prod =
            ∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (x j)) := by
        dsimp [s]
        rw [Multiset.map_map]
        rw [← Finset.erase_val]
        rw [Finset.prod_eq_multiset_prod]
        simp only [Function.comp_apply]
      rw [← hsprod]
      exact hnum
    calc
      |∏ j ∈ Finset.univ.erase i, (x i - x j)⁻¹| *
          |(∏ j ∈ Finset.univ.erase i,
            (Polynomial.X - Polynomial.C (x j))).coeff r.val| ≤
          δ⁻¹ ^ (d - 1) *
            ((2 : ℝ) ^ (d - 1) * C ^ (d - 1 - r.val)) :=
        mul_le_mul hden hnum' (abs_nonneg _) (by positivity)
      _ = B := by
        dsimp [B]
        ring
  have hcoeffsum :
      coeff r = ∑ i, p.eval (x i) * (Lagrange.basis Finset.univ x i).coeff r.val := by
    have hc := congrArg (fun q : Polynomial ℝ => q.coeff r.val) hpinterp
    rw [hpcoeff r] at hc
    simpa [Lagrange.interpolate, Polynomial.finsetSum_coeff] using hc
  have hterm (i : Fin d) :
      (p.eval (x i) * (Lagrange.basis Finset.univ x i).coeff r.val) ^ 2 ≤
        (B * |p.eval (x i)|) ^ 2 := by
    have habs :
        |p.eval (x i) * (Lagrange.basis Finset.univ x i).coeff r.val| ≤
          B * |p.eval (x i)| := by
      rw [abs_mul]
      nlinarith [hbasis i, abs_nonneg (p.eval (x i))]
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg hB (abs_nonneg (p.eval (x i))))).2 habs
  calc
    |coeff r| ^ 2 =
        (∑ i, p.eval (x i) * (Lagrange.basis Finset.univ x i).coeff r.val) ^ 2 := by
      rw [hcoeffsum, sq_abs]
    _ ≤ (d : ℝ) *
        ∑ i, (p.eval (x i) * (Lagrange.basis Finset.univ x i).coeff r.val) ^ 2 := by
      simpa using (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => p.eval (x i) * (Lagrange.basis Finset.univ x i).coeff r.val))
    _ ≤ (d : ℝ) * ∑ i, (B * |p.eval (x i)|) ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum fun i _ => hterm i
      · positivity
    _ = (d : ℝ) * B ^ 2 * ∑ i, |p.eval (x i)| ^ 2 := by
      simp_rw [mul_pow]
      rw [← Finset.mul_sum]
      ring
    _ = (d : ℝ) *
          ((2 : ℝ) ^ (d - 1) * C ^ (d - 1 - r.val) * δ⁻¹ ^ (d - 1)) ^ 2 *
          ∑ i, |∑ j, coeff j * (x i) ^ j.val| ^ 2 := by
      simp_rw [hpeval]
      rfl

@[blueprint "lem:univariate-polynomial-coefficient-l2-bound"
  (statement := /-- Let $d$ be a positive integer, let $C_t,h,a\in\mathbb R$ satisfy
  $C_t\geq1$, $h>0$, and $[a,a+h]\subseteq[-C_t,C_t]$, and let
  $(c_j)_{0\leq j<d}$ be real coefficients. Define
  $q(t)=\sum_{0\leq j<d}c_jt^j$ for $t\in\mathbb R$. Then, for every integer
  $r$ with $0\leq r<d$,
  \[
    |c_r|^2\leq d\frac{3d}{h}
      \left(2^{d-1}C_t^{d-1-r}\left(\frac{3d}{h}\right)^{d-1}\right)^2
      \int_{[a,a+h]}|q(t)|^2\,dt.
  \]
  Thus every coefficient is controlled uniformly by the unweighted $L^2$ norm on any
  nondegenerate subinterval of the truncation interval. -/)
  (proof := /-- Apply \cref{lem:univariate-polynomial-interval-sampling} to the continuous
  nonnegative function $f(t)=|q(t)|^2$. This gives points $x_0,\ldots,x_{d-1}\in[a,a+h]$
  separated pairwise by at least $\delta=h/(3d)$ and satisfying
  \[
    \sum_{i<d}|q(x_i)|^2\leq \frac{3d}{h}
      \int_{[a,a+h]}|q(t)|^2\,dt.
  \]
  The containment $[a,a+h]\subseteq[-C_t,C_t]$ implies $|x_i|\leq C_t$ for every $i$.
  Therefore \cref{lem:univariate-polynomial-lagrange-coefficient-bound}, applied with these
  nodes and this value of $\delta$, bounds $|c_r|^2$ by
  $d(2^{d-1}C_t^{d-1-r}\delta^{-(d-1)})^2$ times the displayed sum. Substitute the sampling
  estimate and the identity $\delta^{-1}=3d/h$ to obtain the asserted inequality. -/)
  (title := /-- Univariate coefficient control by an interval $L^2$ norm -/)
  (latexEnv := "lemma")]
lemma univariate_polynomial_coefficient_l2_bound :
    ∀ (d : ℕ), 0 < d →
      ∀ (Ct h a : ℝ) (coeff : Fin d → ℝ) (r : Fin d),
        1 ≤ Ct → 0 < h → Set.Icc a (a + h) ⊆ Set.Icc (-Ct) Ct →
        |coeff r| ^ 2 ≤
          (d : ℝ) * (3 * (d : ℝ) / h) *
            ((2 : ℝ) ^ (d - 1) * Ct ^ (d - 1 - r.val) *
              (3 * (d : ℝ) / h) ^ (d - 1)) ^ 2 *
            ∫ t in Set.Icc a (a + h),
              |∑ j, coeff j * t ^ j.val| ^ 2 ∂MeasureTheory.volume := by
  intro d hd Ct h a coeff r hCt hh hsubset
  let f : ℝ → ℝ := fun t => |∑ j, coeff j * t ^ j.val| ^ 2
  have hfcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hfnonneg : ∀ t, 0 ≤ f t := by
    intro t
    dsimp [f]
    positivity
  obtain ⟨x, hxmem, hxsep, hsum⟩ :=
    univariate_polynomial_interval_sampling d hd a h f hh hfcont hfnonneg
  have hxbound (i : Fin d) : |x i| ≤ Ct := by
    exact abs_le.mpr (hsubset (hxmem i))
  let δ : ℝ := h / (3 * (d : ℝ))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hlag := univariate_polynomial_lagrange_coefficient_bound d hd Ct δ x coeff r
    hCt hδ hxbound hxsep
  have hinv : δ⁻¹ = 3 * (d : ℝ) / h := by
    dsimp [δ]
    field_simp
  have hfactor :
      0 ≤ (d : ℝ) *
        ((2 : ℝ) ^ (d - 1) * Ct ^ (d - 1 - r.val) * δ⁻¹ ^ (d - 1)) ^ 2 := by
    positivity
  calc
    |coeff r| ^ 2 ≤
        (d : ℝ) *
          ((2 : ℝ) ^ (d - 1) * Ct ^ (d - 1 - r.val) * δ⁻¹ ^ (d - 1)) ^ 2 *
          ∑ i, |∑ j, coeff j * (x i) ^ j.val| ^ 2 := hlag
    _ ≤ (d : ℝ) *
          ((2 : ℝ) ^ (d - 1) * Ct ^ (d - 1 - r.val) * δ⁻¹ ^ (d - 1)) ^ 2 *
          ((3 * (d : ℝ) / h) *
            ∫ t in Set.Icc a (a + h),
              |∑ j, coeff j * t ^ j.val| ^ 2 ∂MeasureTheory.volume) := by
      exact mul_le_mul_of_nonneg_left hsum hfactor
    _ = (d : ℝ) * (3 * (d : ℝ) / h) *
          ((2 : ℝ) ^ (d - 1) * Ct ^ (d - 1 - r.val) *
            (3 * (d : ℝ) / h) ^ (d - 1)) ^ 2 *
          ∫ t in Set.Icc a (a + h),
            |∑ j, coeff j * t ^ j.val| ^ 2 ∂MeasureTheory.volume := by
      rw [hinv]
      ring

@[blueprint "lem:finite-product-box-integral-fubini"
  (statement := /-- Let $s\in\mathbb N$, let $a\in\mathbb R^{s+1}$ and $h\in\mathbb R$,
  and let $f:\mathbb R^{s+1}\to\mathbb R$ be continuous. Writing a point as
  $(x,y)\in\mathbb R\times\mathbb R^s$, integration over the box with lower corner $a$
  and common side length $h$ satisfies
  \[
    \int_{\prod_{j=0}^{s}[a_j,a_j+h]}f(z)\,dz
      =\int_{\prod_{j=1}^{s}[a_j,a_j+h]}
        \int_{a_0}^{a_0+h}f(x,y)\,dx\,dy.
  \] -/)
  (proof := /-- Split the finite product at its zeroth coordinate using the standard measurable
  equivalence between $\mathbb R^{s+1}$ and $\mathbb R\times\mathbb R^s$. This equivalence
  preserves Lebesgue measure and carries the original box to the product of the zeroth interval
  and the tail box. The integrand is integrable on this compact product because it is continuous.
  Swapping the two product coordinates and applying Fubini's theorem for set integrals yields the
  asserted order of integration. -/)
  (title := /-- Fubini decomposition of a finite-dimensional box integral -/)
  (latexEnv := "lemma")]
lemma finite_product_box_integral_fubini :
    ∀ {s : ℕ} (lower : Fin (s + 1) → ℝ) (h : ℝ) (f : (Fin (s + 1) → ℝ) → ℝ),
      Continuous f →
      (∫ z in {z | ∀ j, lower j ≤ z j ∧ z j ≤ lower j + h},
          f z ∂MeasureTheory.volume) =
        ∫ y in {y | ∀ j, lower j.succ ≤ y j ∧ y j ≤ lower j.succ + h},
          ∫ x in Set.Icc (lower 0) (lower 0 + h),
            f (Fin.cons x y) ∂MeasureTheory.volume ∂MeasureTheory.volume := by
  intro s lower h f hf
  let A : Set ℝ := Set.Icc (lower 0) (lower 0 + h)
  let B : Set (Fin s → ℝ) :=
    {y | ∀ j, lower j.succ ≤ y j ∧ y j ≤ lower j.succ + h}
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (s + 1) => ℝ) 0
  have he := MeasureTheory.volume_preserving_piFinSuccAbove
    (fun _ : Fin (s + 1) => ℝ) 0
  have hgcont : Continuous (fun p : ℝ × (Fin s → ℝ) => f (Fin.cons p.1 p.2)) := by
    fun_prop
  have hBcompact : IsCompact B := by
    rw [show B = Set.Icc (fun j : Fin s => lower j.succ)
      (fun j : Fin s => lower j.succ + h) by
        ext y
        simp only [B, Set.mem_setOf_eq, Set.mem_Icc]
        constructor
        · intro hy
          exact ⟨fun j => (hy j).1, fun j => (hy j).2⟩
        · rintro ⟨hy₁, hy₂⟩ j
          exact ⟨hy₁ j, hy₂ j⟩]
    exact isCompact_Icc
  have hgint : MeasureTheory.IntegrableOn
      (fun p : ℝ × (Fin s → ℝ) => f (Fin.cons p.1 p.2)) (A ×ˢ B)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin s → ℝ))) := by
    exact hgcont.continuousOn.integrableOn_compact (isCompact_Icc.prod hBcompact)
  have hpre :
      e ⁻¹' (A ×ˢ B) =
        {z | ∀ j, lower j ≤ z j ∧ z j ≤ lower j + h} := by
    ext z
    change ((z 0, Fin.tail z) ∈ A ×ˢ B) ↔
      ∀ j, lower j ≤ z j ∧ z j ≤ lower j + h
    constructor
    · rintro ⟨hz, htail⟩ j
      refine Fin.cases ?_ (fun k => ?_) j
      · exact hz
      · exact htail k
    · intro hz
      exact ⟨hz 0, fun j => hz j.succ⟩
  have hchange :
      (∫ z in {z | ∀ j, lower j ≤ z j ∧ z j ≤ lower j + h},
          f z ∂MeasureTheory.volume) =
        ∫ p in A ×ˢ B, f (Fin.cons p.1 p.2)
          ∂MeasureTheory.volume := by
    rw [← hpre]
    simpa [e] using
      (he.setIntegral_preimage_emb e.measurableEmbedding
        (fun p : ℝ × (Fin s → ℝ) => f (Fin.cons p.1 p.2)) (A ×ˢ B))
  rw [hchange]
  rw [MeasureTheory.Measure.volume_eq_prod]
  rw [← MeasureTheory.setIntegral_prod_swap A B
    (fun p : ℝ × (Fin s → ℝ) => f (Fin.cons p.1 p.2))]
  simpa [A, B] using
    (MeasureTheory.setIntegral_prod
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (Fin s → ℝ)))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (fun p : (Fin s → ℝ) × ℝ => f (Fin.cons p.2 p.1)) hgint.swap)

@[blueprint "lem:univariate-polynomial-coefficient-l2-uniform-envelope"
  (statement := /-- Let $d,N\in\mathbb N$ satisfy $d>0$ and $d+1\leq N$, and let
  $C_t,h,a\in\mathbb R$ satisfy $C_t\geq1$, $h>0$, $Nh=2C_t$, and
  $[a,a+h]\subseteq[-C_t,C_t]$. For real coefficients $(c_j)_{j<d}$ and every $r<d$,
  \[
    |c_r|^2\leq \frac{(12dN)^{2d}}{h}
      \int_{[a,a+h]}\left|\sum_{j<d}c_jt^j\right|^2\,dt.
  \] -/)
  (proof := /-- Apply
  \cref{lem:univariate-polynomial-coefficient-l2-bound}. Since $C_t\geq1$, replace
  $C_t^{d-1-r}$ by $C_t^{d-1}$. The identity $Nh=2C_t$ then turns the remaining
  interpolation factor into $(3dN)^{d-1}$. The prefactor $3d^2$ and this squared factor
  are bounded by $(12dN)^{2d}$, giving the stated uniform envelope after retaining the
  factor $h^{-1}$. -/)
  (title := /-- Uniform univariate coefficient envelope at the box scale -/)
  (latexEnv := "lemma")]
lemma univariate_polynomial_coefficient_l2_uniform_envelope :
    ∀ (d N : ℕ), 0 < d → d + 1 ≤ N →
      ∀ (Ct h a : ℝ) (coeff : Fin d → ℝ) (r : Fin d),
        1 ≤ Ct → 0 < h → (N : ℝ) * h = 2 * Ct →
        Set.Icc a (a + h) ⊆ Set.Icc (-Ct) Ct →
        |coeff r| ^ 2 ≤
          (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d) / h *
            ∫ t in Set.Icc a (a + h),
              |∑ j, coeff j * t ^ j.val| ^ 2 ∂MeasureTheory.volume := by
  intro d N hd hdN Ct h a coeff r hCt hh hNh hsubset
  have hdR : 0 ≤ (d : ℝ) := by positivity
  have hNR : 1 ≤ (N : ℝ) := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hCt0 : 0 ≤ Ct := le_trans (by norm_num) hCt
  have hpowCt : Ct ^ (d - 1 - r.val) ≤ Ct ^ (d - 1) := by
    exact pow_le_pow_right₀ hCt (Nat.sub_le (d - 1) r.val)
  have hbase : 2 * Ct * (3 * (d : ℝ) / h) = 3 * (d : ℝ) * (N : ℝ) := by
    field_simp
    nlinarith
  have hinterp :
      (2 : ℝ) ^ (d - 1) * Ct ^ (d - 1 - r.val) *
          (3 * (d : ℝ) / h) ^ (d - 1) ≤
        (3 * (d : ℝ) * (N : ℝ)) ^ (d - 1) := by
    calc
      (2 : ℝ) ^ (d - 1) * Ct ^ (d - 1 - r.val) *
            (3 * (d : ℝ) / h) ^ (d - 1) ≤
          (2 : ℝ) ^ (d - 1) * Ct ^ (d - 1) *
            (3 * (d : ℝ) / h) ^ (d - 1) := by
              gcongr
      _ = (2 * Ct * (3 * (d : ℝ) / h)) ^ (d - 1) := by
            rw [mul_pow, mul_pow]
      _ = (3 * (d : ℝ) * (N : ℝ)) ^ (d - 1) := by rw [hbase]
  have hinterp0 :
      0 ≤ (2 : ℝ) ^ (d - 1) * Ct ^ (d - 1 - r.val) *
        (3 * (d : ℝ) / h) ^ (d - 1) := by positivity
  have hsmall : 3 * (d : ℝ) ^ 2 ≤
      (12 * (d : ℝ) * (N : ℝ)) ^ 2 := by
    nlinarith [mul_self_nonneg (12 * (d : ℝ) * ((N : ℝ) - 1))]
  have hbase_le :
      3 * (d : ℝ) * (N : ℝ) ≤ 12 * (d : ℝ) * (N : ℝ) := by
    nlinarith [mul_nonneg hdR (le_trans (by norm_num) hNR)]
  have hfactor :
      (d : ℝ) * (3 * (d : ℝ) / h) *
          ((2 : ℝ) ^ (d - 1) * Ct ^ (d - 1 - r.val) *
            (3 * (d : ℝ) / h) ^ (d - 1)) ^ 2 ≤
        (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d) / h := by
    apply (le_div_iff₀ hh).2
    calc
      ((d : ℝ) * (3 * (d : ℝ) / h) *
          ((2 : ℝ) ^ (d - 1) * Ct ^ (d - 1 - r.val) *
            (3 * (d : ℝ) / h) ^ (d - 1)) ^ 2) * h =
          3 * (d : ℝ) ^ 2 *
            ((2 : ℝ) ^ (d - 1) * Ct ^ (d - 1 - r.val) *
              (3 * (d : ℝ) / h) ^ (d - 1)) ^ 2 := by
                field_simp
      _ ≤ 3 * (d : ℝ) ^ 2 *
          ((3 * (d : ℝ) * (N : ℝ)) ^ (d - 1)) ^ 2 := by
            gcongr
      _ = (3 * (d : ℝ) ^ 2) *
          (3 * (d : ℝ) * (N : ℝ)) ^ (2 * (d - 1)) := by
            rw [← pow_mul]
            ring
      _ ≤ (12 * (d : ℝ) * (N : ℝ)) ^ 2 *
          (12 * (d : ℝ) * (N : ℝ)) ^ (2 * (d - 1)) := by
            apply mul_le_mul hsmall
              (pow_le_pow_left₀ (by positivity) hbase_le (2 * (d - 1)))
            · positivity
            · positivity
      _ = (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d) := by
            rw [← pow_add]
            congr 1
            omega
  have huni := univariate_polynomial_coefficient_l2_bound d hd Ct h a coeff r
    hCt hh hsubset
  have hintnonneg :
      0 ≤ ∫ t in Set.Icc a (a + h),
        |∑ j, coeff j * t ^ j.val| ^ 2 ∂MeasureTheory.volume := by
    exact MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun t => sq_nonneg _)
  exact le_trans huni (mul_le_mul_of_nonneg_right hfactor hintnonneg)

@[blueprint "lem:exponential-energy-fin-cons-regroup"
  (statement := /-- Let $s,d\in\mathbb N$, let $F\subseteq\mathbb N^{s+1}$ be finite,
  and suppose that $\beta_0<d$ for every $\beta\in F$. For real coefficients $c_\beta$,
  $x\in\mathbb R$, and $y\in\mathbb R^s$, the polynomial energy satisfies
  \[
    E_c(x,y)=\sum_{r<d}\left(
      \sum_{\beta\in F\,:\,\beta_0=r}
        c_\beta y^{\operatorname{tail}(\beta)}\right)x^r.
  \] -/)
  (proof := /-- Expand every monomial into its zeroth-coordinate factor and its tail product.
  Interchange the two finite sums. For each exponent vector $\beta$, exactly one index
  $r<d$ contributes, namely $r=\beta_0$; the degree hypothesis supplies this index in
  $\operatorname{Fin}(d)$. -/)
  (title := /-- Regrouping a finite polynomial by its first-coordinate exponent -/)
  (latexEnv := "lemma")]
lemma exponential_energy_fin_cons_regroup :
    ∀ {s : ℕ} (d : ℕ) (terms : Finset (polynomial_factor (s + 1)))
      (coeff : polynomial_factor (s + 1) → ℝ) (x : ℝ) (y : Fin s → ℝ),
      (∀ beta ∈ terms, beta 0 < d) →
      exponential_energy terms coeff (Fin.cons x y) =
        ∑ r : Fin d,
          (∑ beta ∈ terms,
            if beta 0 = r.val then
              coeff beta * monomial_value (Fin.tail beta) y
            else 0) * x ^ r.val := by
  intro s d terms coeff x y hdeg
  simp_rw [exponential_energy, monomial_value, Fin.prod_univ_succ]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro beta hbeta
  let r : Fin d := ⟨beta 0, hdeg beta hbeta⟩
  rw [Finset.sum_eq_single r]
  · dsimp [r]
    rw [if_pos rfl]
    simp [Fin.tail]
    ring
  · intro b hb hbr
    have hne : beta 0 ≠ b.val := by
      intro heq
      apply hbr
      exact Fin.ext heq.symm
    simp [hne]
  · simp

@[blueprint "lem:exponential-energy-head-coefficient"
  (statement := /-- Let $F\subseteq\mathbb N^{s+1}$ be finite and fix
  $\alpha\in\mathbb N^{s+1}$. Project the exponent vectors in $F$ whose zeroth exponent is
  $\alpha_0$ to their tails. The polynomial on $\mathbb R^s$ with the correspondingly
  reconstructed coefficients is exactly
  \[
    \sum_{\beta\in F\,:\,\beta_0=\alpha_0}
      c_\beta y^{\operatorname{tail}(\beta)}.
  \] -/)
  (proof := /-- On exponent vectors with fixed zeroth coordinate, the tail projection is
  injective. Rewrite the sum over the image as a sum over the filtered exponent vectors.
  Prepending the common zeroth exponent to each projected tail reconstructs the original
  exponent vector, which identifies every summand. -/)
  (title := /-- Identification of a first-coordinate coefficient polynomial -/)
  (latexEnv := "lemma")]
lemma exponential_energy_head_coefficient :
    ∀ {s : ℕ} (terms : Finset (polynomial_factor (s + 1)))
      (coeff : polynomial_factor (s + 1) → ℝ)
      (alpha : polynomial_factor (s + 1)) (y : Fin s → ℝ),
      exponential_energy
          ((terms.filter fun beta => beta 0 = alpha 0).image Fin.tail)
          (fun gamma => coeff (Fin.cons (alpha 0) gamma)) y =
        ∑ beta ∈ terms,
          if beta 0 = alpha 0 then
            coeff beta * monomial_value (Fin.tail beta) y
          else 0 := by
  intro s terms coeff alpha y
  rw [show (∑ beta ∈ terms,
      if beta 0 = alpha 0 then
        coeff beta * monomial_value (Fin.tail beta) y
      else 0) =
      ∑ beta ∈ terms.filter (fun beta => beta 0 = alpha 0),
        coeff beta * monomial_value (Fin.tail beta) y by
          exact (Finset.sum_filter
            (s := terms)
            (p := fun beta => beta 0 = alpha 0)
            (f := fun beta => coeff beta * monomial_value (Fin.tail beta) y)).symm]
  simp only [exponential_energy]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro beta hbeta
    have hhead : beta 0 = alpha 0 := (Finset.mem_filter.mp hbeta).2
    rw [← hhead]
    simp [Fin.cons_self_tail]
  · intro beta₁ hbeta₁ beta₂ hbeta₂ htail
    have hhead₁ : beta₁ 0 = alpha 0 := (Finset.mem_filter.mp hbeta₁).2
    have hhead₂ : beta₂ 0 = alpha 0 := (Finset.mem_filter.mp hbeta₂).2
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact hhead₁.trans hhead₂.symm
    · exact congrFun htail k

@[blueprint "lem:finite-product-polynomial-coefficient-l2-bound-normalized"
  (statement := /-- Under the hypotheses of the finite-product coefficient estimate, let
  $Q=\prod_{j=1}^s[a_j,a_j+h]$. For every supported exponent $\alpha$,
  \[
    |c_\alpha|^2\leq
      \frac{(12dN)^{2ds}}{h^s}\int_Q|P(z)|^2\,dz.
  \] -/)
  (proof := /-- Induct on $s$. The zero-dimensional assertion follows because the supported
  polynomial has a single possible exponent vector. For the induction step, filter the support
  to the terms whose first exponent equals $\alpha_1$ and project them to the remaining
  coordinates. By \cref{lem:exponential-energy-head-coefficient}, this is the coefficient
  polynomial to which the induction hypothesis applies. By
  \cref{lem:exponential-energy-fin-cons-regroup} and
  \cref{lem:univariate-polynomial-coefficient-l2-uniform-envelope}, its squared value at every
  tail point is at most $(12dN)^{2d}/h$ times the integral of the original polynomial over the
  first interval. Integrate this pointwise inequality over the tail box and use
  \cref{lem:finite-product-box-integral-fubini}. Multiplying the one-coordinate factor by the
  inductive factor gives $(12dN)^{2d(s+1)}/h^{s+1}$. -/)
  (title := /-- Normalized finite-product polynomial coefficient estimate -/)
  (latexEnv := "lemma")]
lemma finite_product_polynomial_coefficient_l2_bound_normalized :
    ∀ {s : ℕ} (d N : ℕ) (Ct h : ℝ) (lower : Fin s → ℝ)
      (terms : Finset (polynomial_factor s)) (coeff : polynomial_factor s → ℝ)
      (alpha : polynomial_factor s),
      0 < d → d + 1 ≤ N → 1 ≤ Ct → 0 < h → (N : ℝ) * h = 2 * Ct →
      (∀ j, Set.Icc (lower j) (lower j + h) ⊆ Set.Icc (-Ct) Ct) →
      (∀ beta ∈ terms, ∀ j, beta j < d) → alpha ∈ terms →
      |coeff alpha| ^ 2 ≤
        (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d * s) / h ^ s *
          ∫ z in {z | ∀ j, lower j ≤ z j ∧ z j ≤ lower j + h},
            |exponential_energy terms coeff z| ^ 2 ∂MeasureTheory.volume := by
  intro s
  induction s with
  | zero =>
      intro d N Ct h lower terms coeff alpha hd hdN hCt hh hNh hsubset hdeg halpha
      have hterms : terms = {alpha} := by
        ext beta
        have hba : beta = alpha := Subsingleton.elim beta alpha
        subst beta
        simp [halpha]
      subst terms
      have hvol0 :
          (MeasureTheory.volume :
            MeasureTheory.Measure (Fin 0 → ℝ)).real Set.univ = 1 := by
        rw [show (Set.univ : Set (Fin 0 → ℝ)) = Set.Icc lower lower by
          ext z
          constructor
          · intro _
            rw [Subsingleton.elim z lower]
            exact ⟨le_rfl, le_rfl⟩
          · intro _
            trivial]
        change (MeasureTheory.volume (Set.Icc lower lower)).toReal = 1
        rw [Real.volume_Icc_pi_toReal]
        · simp
        · intro j
          exact Fin.elim0 j
      simp [exponential_energy, monomial_value, Subsingleton.elim, hvol0]
  | succ s ih =>
      intro d N Ct h lower terms coeff alpha hd hdN hCt hh hNh hsubset hdeg halpha
      let tailTerms : Finset (polynomial_factor s) :=
        (terms.filter fun beta => beta 0 = alpha 0).image Fin.tail
      let tailCoeff : polynomial_factor s → ℝ :=
        fun gamma => coeff (Fin.cons (alpha 0) gamma)
      let tailAlpha : polynomial_factor s := Fin.tail alpha
      let tailLower : Fin s → ℝ := Fin.tail lower
      have htailSubset :
          ∀ j, Set.Icc (tailLower j) (tailLower j + h) ⊆ Set.Icc (-Ct) Ct := by
        intro j
        exact hsubset j.succ
      have htailDeg : ∀ gamma ∈ tailTerms, ∀ j, gamma j < d := by
        intro gamma hgamma j
        rcases Finset.mem_image.mp hgamma with ⟨beta, hbeta, rfl⟩
        exact hdeg beta (Finset.mem_filter.mp hbeta).1 j.succ
      have htailAlpha : tailAlpha ∈ tailTerms := by
        exact Finset.mem_image.mpr
          ⟨alpha, Finset.mem_filter.mpr ⟨halpha, rfl⟩, rfl⟩
      have htail := ih d N Ct h tailLower tailTerms tailCoeff tailAlpha
        hd hdN hCt hh hNh htailSubset htailDeg htailAlpha
      have htailCoeffAlpha : tailCoeff tailAlpha = coeff alpha := by
        dsimp [tailCoeff, tailAlpha]
        simp [Fin.cons_self_tail]
      let headCoeff : (Fin s → ℝ) → Fin d → ℝ :=
        fun y r => ∑ beta ∈ terms,
          if beta 0 = r.val then
            coeff beta * monomial_value (Fin.tail beta) y
          else 0
      let rAlpha : Fin d := ⟨alpha 0, hdeg alpha halpha 0⟩
      have hheadCoeff (y : Fin s → ℝ) :
          headCoeff y rAlpha =
            exponential_energy tailTerms tailCoeff y := by
        dsimp [headCoeff, rAlpha, tailTerms, tailCoeff]
        exact (exponential_energy_head_coefficient terms coeff alpha y).symm
      have hregroup (x : ℝ) (y : Fin s → ℝ) :
          (∑ r : Fin d, headCoeff y r * x ^ r.val) =
            exponential_energy terms coeff (Fin.cons x y) := by
        symm
        exact exponential_energy_fin_cons_regroup d terms coeff x y
          (fun beta hbeta => hdeg beta hbeta 0)
      have hpoint (y : Fin s → ℝ) :
          |exponential_energy tailTerms tailCoeff y| ^ 2 ≤
            (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d) / h *
              ∫ x in Set.Icc (lower 0) (lower 0 + h),
                |exponential_energy terms coeff (Fin.cons x y)| ^ 2
                  ∂MeasureTheory.volume := by
        have hone :=
          univariate_polynomial_coefficient_l2_uniform_envelope d N hd hdN
            Ct h (lower 0) (headCoeff y) rAlpha hCt hh hNh (hsubset 0)
        rw [hheadCoeff] at hone
        simpa only [hregroup] using hone
      let B : Set (Fin s → ℝ) :=
        {y | ∀ j, tailLower j ≤ y j ∧ y j ≤ tailLower j + h}
      have hBcompact : IsCompact B := by
        rw [show B = Set.Icc tailLower (fun j => tailLower j + h) by
          ext y
          simp only [B, Set.mem_setOf_eq, Set.mem_Icc]
          constructor
          · intro hy
            exact ⟨fun j => (hy j).1, fun j => (hy j).2⟩
          · rintro ⟨hy₁, hy₂⟩ j
            exact ⟨hy₁ j, hy₂ j⟩]
        exact isCompact_Icc
      have hleftCont :
          Continuous (fun y : Fin s → ℝ =>
            |exponential_energy tailTerms tailCoeff y| ^ 2) := by
        unfold exponential_energy monomial_value
        fun_prop
      have hleftInt : MeasureTheory.IntegrableOn
          (fun y : Fin s → ℝ =>
            |exponential_energy tailTerms tailCoeff y| ^ 2) B
          MeasureTheory.volume :=
        hleftCont.continuousOn.integrableOn_compact hBcompact
      let A : Set ℝ := Set.Icc (lower 0) (lower 0 + h)
      have hgcont : Continuous (fun p : ℝ × (Fin s → ℝ) =>
          |exponential_energy terms coeff (Fin.cons p.1 p.2)| ^ 2) := by
        unfold exponential_energy monomial_value
        fun_prop
      have hgint : MeasureTheory.IntegrableOn
          (fun p : ℝ × (Fin s → ℝ) =>
            |exponential_energy terms coeff (Fin.cons p.1 p.2)| ^ 2)
          (A ×ˢ B)
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
            (MeasureTheory.volume : MeasureTheory.Measure (Fin s → ℝ))) := by
        exact hgcont.continuousOn.integrableOn_compact
          (isCompact_Icc.prod hBcompact)
      have hgint' : MeasureTheory.Integrable
          (fun p : ℝ × (Fin s → ℝ) =>
            |exponential_energy terms coeff (Fin.cons p.1 p.2)| ^ 2)
          ((MeasureTheory.volume.restrict A).prod
            (MeasureTheory.volume.restrict B)) := by
        rw [MeasureTheory.Measure.prod_restrict]
        exact hgint
      have hinnerInt : MeasureTheory.IntegrableOn
          (fun y : Fin s → ℝ =>
            ∫ x in A, |exponential_energy terms coeff (Fin.cons x y)| ^ 2
              ∂MeasureTheory.volume) B MeasureTheory.volume := by
        exact hgint'.integral_prod_right
      have hrightInt : MeasureTheory.IntegrableOn
          (fun y : Fin s → ℝ =>
            (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d) / h *
              ∫ x in Set.Icc (lower 0) (lower 0 + h),
                |exponential_energy terms coeff (Fin.cons x y)| ^ 2
                  ∂MeasureTheory.volume) B MeasureTheory.volume :=
        hinnerInt.const_mul _
      have hintegral :
          (∫ y in B, |exponential_energy tailTerms tailCoeff y| ^ 2
            ∂MeasureTheory.volume) ≤
            (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d) / h *
              ∫ y in B,
                ∫ x in Set.Icc (lower 0) (lower 0 + h),
                  |exponential_energy terms coeff (Fin.cons x y)| ^ 2
                    ∂MeasureTheory.volume ∂MeasureTheory.volume := by
        calc
          (∫ y in B, |exponential_energy tailTerms tailCoeff y| ^ 2
              ∂MeasureTheory.volume) ≤
              ∫ y in B,
                (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d) / h *
                  ∫ x in Set.Icc (lower 0) (lower 0 + h),
                    |exponential_energy terms coeff (Fin.cons x y)| ^ 2
                      ∂MeasureTheory.volume ∂MeasureTheory.volume := by
                exact MeasureTheory.setIntegral_mono_on hleftInt hrightInt
                  hBcompact.measurableSet (fun y _ => hpoint y)
          _ = (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d) / h *
              ∫ y in B,
                ∫ x in Set.Icc (lower 0) (lower 0 + h),
                  |exponential_energy terms coeff (Fin.cons x y)| ^ 2
                    ∂MeasureTheory.volume ∂MeasureTheory.volume := by
                rw [MeasureTheory.integral_const_mul]
      have hfullCont :
          Continuous (fun z : Fin (s + 1) → ℝ =>
            |exponential_energy terms coeff z| ^ 2) := by
        unfold exponential_energy monomial_value
        fun_prop
      have hfubini :=
        finite_product_box_integral_fubini lower h
          (fun z : Fin (s + 1) → ℝ => |exponential_energy terms coeff z| ^ 2)
          hfullCont
      have hfubini' :
          (∫ z in {z | ∀ j, lower j ≤ z j ∧ z j ≤ lower j + h},
              |exponential_energy terms coeff z| ^ 2
                ∂MeasureTheory.volume) =
            ∫ y in B,
              ∫ x in Set.Icc (lower 0) (lower 0 + h),
                |exponential_energy terms coeff (Fin.cons x y)| ^ 2
                  ∂MeasureTheory.volume ∂MeasureTheory.volume := by
        simpa [B, tailLower, Fin.tail] using hfubini
      have htailNonneg :
          0 ≤ (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d * s) / h ^ s := by
        positivity
      rw [htailCoeffAlpha] at htail
      calc
        |coeff alpha| ^ 2 ≤
            (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d * s) / h ^ s *
              ∫ y in B, |exponential_energy tailTerms tailCoeff y| ^ 2
                ∂MeasureTheory.volume := by
                  simpa [B] using htail
        _ ≤ (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d * s) / h ^ s *
            ((12 * (d : ℝ) * (N : ℝ)) ^ (2 * d) / h *
              ∫ y in B,
                ∫ x in Set.Icc (lower 0) (lower 0 + h),
                  |exponential_energy terms coeff (Fin.cons x y)| ^ 2
                    ∂MeasureTheory.volume ∂MeasureTheory.volume) :=
              mul_le_mul_of_nonneg_left hintegral htailNonneg
        _ = (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d * (s + 1)) / h ^ (s + 1) *
            ∫ z in {z | ∀ j, lower j ≤ z j ∧ z j ≤ lower j + h},
              |exponential_energy terms coeff z| ^ 2
                ∂MeasureTheory.volume := by
              rw [hfubini']
              have hnum :
                  (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d * s) *
                      (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d) =
                    (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d * (s + 1)) := by
                rw [← pow_add]
                congr 1
              have hden : h ^ s * h = h ^ (s + 1) := by
                rw [pow_succ]
              rw [← hnum, ← hden]
              field_simp

@[blueprint "lem:finite-product-polynomial-coefficient-l2-bound"
  (statement := /-- Let $s,d,N\in\mathbb N$ satisfy $d>0$ and $d+1\leq N$, and let
  $C_t,h\in\mathbb R$ satisfy $C_t\geq1$, $h>0$, and $Nh=2C_t$. For
  $a=(a_1,\ldots,a_s)\in\mathbb R^s$, suppose that
  $Q=\prod_{j=1}^s[a_j,a_j+h]$ is contained in $[-C_t,C_t]^s$. Let
  $F\subseteq\mathbb N^s$ be finite, let $(c_\beta)_{\beta\in F}$ be real coefficients,
  and assume that $\beta_j<d$ for every $\beta\in F$ and every $1\leq j\leq s$. Define
  $P(z)=\sum_{\beta\in F}c_\beta z^\beta$. Then, for every $\alpha\in F$,
  \[
    |c_\alpha|^2\leq
      (12dN)^{2ds}\frac1{\operatorname{vol}(Q)}
      \int_Q|P(z)|^2\,dz.
  \]
  The estimate is uniform in the finite support $F$ and in the position of the box. -/)
  (proof := /-- Apply
  \cref{lem:finite-product-polynomial-coefficient-l2-bound-normalized}, which gives the same
  coefficient estimate with denominator $h^s$. The product formula for Lebesgue measure on a
  finite real coordinate space gives
  $\operatorname{vol}(\prod_j[a_j,a_j+h])=\prod_j h=h^s$, because $h>0$. Substituting this
  identity yields the asserted volume-normalized inequality. -/)
  (title := /-- Finite-product coefficient extraction from a box $L^2$ norm -/)
  (latexEnv := "lemma")]
lemma finite_product_polynomial_coefficient_l2_bound :
    ∀ {s : ℕ} (d N : ℕ) (Ct h : ℝ) (lower : Fin s → ℝ)
      (terms : Finset (polynomial_factor s)) (coeff : polynomial_factor s → ℝ)
      (alpha : polynomial_factor s),
      0 < d → d + 1 ≤ N → 1 ≤ Ct → 0 < h → (N : ℝ) * h = 2 * Ct →
      (∀ j, Set.Icc (lower j) (lower j + h) ⊆ Set.Icc (-Ct) Ct) →
      (∀ beta ∈ terms, ∀ j, beta j < d) → alpha ∈ terms →
      |coeff alpha| ^ 2 ≤
        (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d * s) /
            (MeasureTheory.volume : MeasureTheory.Measure (Fin s → ℝ)).real
              {z | ∀ j, lower j ≤ z j ∧ z j ≤ lower j + h} *
          ∫ z in {z | ∀ j, lower j ≤ z j ∧ z j ≤ lower j + h},
            |exponential_energy terms coeff z| ^ 2 ∂MeasureTheory.volume := by
  intro s d N Ct h lower terms coeff alpha hd hdN hCt hh hNh hsubset hdeg halpha
  have hnormalized :=
    finite_product_polynomial_coefficient_l2_bound_normalized d N Ct h lower
      terms coeff alpha hd hdN hCt hh hNh hsubset hdeg halpha
  have hbox :
      {z : Fin s → ℝ | ∀ j, lower j ≤ z j ∧ z j ≤ lower j + h} =
        Set.Icc lower (fun j => lower j + h) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · intro hz
      exact ⟨fun j => (hz j).1, fun j => (hz j).2⟩
    · rintro ⟨hz₁, hz₂⟩ j
      exact ⟨hz₁ j, hz₂ j⟩
  have hvol :
      (MeasureTheory.volume : MeasureTheory.Measure (Fin s → ℝ)).real
          {z | ∀ j, lower j ≤ z j ∧ z j ≤ lower j + h} = h ^ s := by
    rw [hbox]
    change (MeasureTheory.volume
      (Set.Icc lower (fun j => lower j + h))).toReal = h ^ s
    rw [Real.volume_Icc_pi_toReal]
    · simp
    · intro j
      linarith
  rw [hvol]
  exact hnormalized

@[blueprint "lem:support-cell-density-comparison"
  (statement := /-- For every $s\in\mathbb N$, let $C\subset\mathbb R^s$ be measurable with
  positive finite volume, and let $f,P:\mathbb R^s\to\mathbb R$. Assume that $f$, $P^2$, and
  $P^2f$ are integrable on $C$, that $f$ is positive on $C$, that
  $\int_C f>0$, and that $f(z)\leq e^{1/32}f(z')$ for every $z,z'\in C$. Then
  \[
    \frac1{\operatorname{vol}(C)}\int_C P^2
      \leq \frac{e^{1/32}}{\int_Cf}\int_C P^2f.
  \]
  This compares normalized cell averages and makes no inference from isolated point values. -/)
  (proof := /-- Write $m_C=\int_Cf$, which is positive by hypothesis. For fixed $z\in C$,
  integrate the inequality $f(z')\leq e^{1/32}f(z)$ over $z'\in C$ to obtain
  $m_C\leq e^{1/32}\operatorname{vol}(C)f(z)$. Hence
  $\operatorname{vol}(C)^{-1}\leq e^{1/32}f(z)/m_C$ throughout $C$. Multiply this pointwise
  inequality by the nonnegative function $P(z)^2$ and integrate. The stated integrability
  assumptions justify monotonicity and the extraction of the two positive constants. -/)
  (title := /-- Density comparison for normalized support-cell averages -/)
  (latexEnv := "lemma")]
lemma support_cell_density_comparison :
    ∀ {s : ℕ} (C : Set (Fin s → ℝ)) (f P : (Fin s → ℝ) → ℝ),
      MeasurableSet C →
      0 < (MeasureTheory.volume : MeasureTheory.Measure (Fin s → ℝ)).real C →
      MeasureTheory.IntegrableOn f C MeasureTheory.volume →
      MeasureTheory.IntegrableOn (fun z => P z ^ 2) C MeasureTheory.volume →
      MeasureTheory.IntegrableOn (fun z => P z ^ 2 * f z) C MeasureTheory.volume →
      (∀ z ∈ C, 0 < f z) →
      (∀ z ∈ C, ∀ z' ∈ C, f z ≤ Real.exp (1 / 32 : ℝ) * f z') →
      0 < ∫ z in C, f z ∂MeasureTheory.volume →
      (∫ z in C, P z ^ 2 ∂MeasureTheory.volume) /
          (MeasureTheory.volume : MeasureTheory.Measure (Fin s → ℝ)).real C ≤
        Real.exp (1 / 32 : ℝ) / (∫ z in C, f z ∂MeasureTheory.volume) *
          ∫ z in C, P z ^ 2 * f z ∂MeasureTheory.volume := by
  intro s C f P hC hvol hf hP hPf hpos hratio hmass
  have hCfinite : MeasureTheory.volume C ≠ ⊤ :=
    (ENNReal.toReal_pos_iff.mp hvol).2.ne
  have hmass_le : ∀ z ∈ C, (∫ x in C, f x ∂MeasureTheory.volume) ≤
      Real.exp (1 / 32 : ℝ) * MeasureTheory.volume.real C * f z := by
    intro z hz
    have hconst : MeasureTheory.IntegrableOn
        (fun _ : Fin s → ℝ => Real.exp (1 / 32 : ℝ) * f z) C MeasureTheory.volume :=
      MeasureTheory.integrableOn_const hCfinite
    have h := MeasureTheory.setIntegral_mono_on hf hconst hC
      (fun z' hz' => hratio z' hz' z hz)
    rw [MeasureTheory.setIntegral_const] at h
    simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using h
  have hpoint : ∀ z ∈ C,
      (∫ x in C, f x ∂MeasureTheory.volume) * P z ^ 2 ≤
        (Real.exp (1 / 32 : ℝ) * MeasureTheory.volume.real C) *
          (P z ^ 2 * f z) := by
    intro z hz
    have h := mul_le_mul_of_nonneg_right (hmass_le z hz) (sq_nonneg (P z))
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have hint := MeasureTheory.setIntegral_mono_on
    (hP.const_mul (∫ x in C, f x ∂MeasureTheory.volume))
    (hPf.const_mul (Real.exp (1 / 32 : ℝ) * MeasureTheory.volume.real C))
    hC hpoint
  rw [integral_const_mul_of_integrable hP, integral_const_mul_of_integrable hPf] at hint
  calc
    (∫ z in C, P z ^ 2 ∂MeasureTheory.volume) / MeasureTheory.volume.real C ≤
        (Real.exp (1 / 32 : ℝ) *
          (∫ z in C, P z ^ 2 * f z ∂MeasureTheory.volume)) /
            (∫ z in C, f z ∂MeasureTheory.volume) := by
      apply (div_le_div_iff₀ hvol hmass).2
      simpa [mul_assoc, mul_left_comm, mul_comm] using hint
    _ = Real.exp (1 / 32 : ℝ) / (∫ z in C, f z ∂MeasureTheory.volume) *
        ∫ z in C, P z ^ 2 * f z ∂MeasureTheory.volume := by ring

@[blueprint "lem:support-box-weighted-coefficient-bound"
  (statement := /-- Let $n,d\in\mathbb N$, let $\mathcal K\subseteq\mathbb N^n$ be a finite
  family of factors of total degree at most $d$, let $\theta^*:\mathbb N^n\to\mathbb R$, and
  fix $i\in[n]$. Let $B,k\in\mathbb R$, let $C_t\in\mathbb N$, and let $p$ be a probability
  measure on $\mathbb R^n$. Assume that $B>0$, that $\theta^*$ is feasible at radius $B$, that
  $p$ is the unit-base polynomial exponential family generated by $(\mathcal K,\theta^*)$, and
  that $p$ satisfies the degree-$d$ tail-decay condition with rate $k$ and threshold $C_t$.
  Suppose moreover that
  \[
    1+2^{-10}\leq dBC_t^d.
  \]
  Put $w=\operatorname{ord}(\mathcal K)$. Then, for every parameter vector $\theta$ feasible
  at radius $B$ and every support-maximal factor $a\in\mathcal K$ incident to $i$,
  \[
    (\theta_a^*-\theta_a)^2\leq
      4e^{1/32}(792d^2u)^{2dw}\,
      \frac12\int
        \bigl(\partial_iE_{\theta-\theta^*}(x)\bigr)^2\,dp_{\theta^*}(x).
  \]
  The constant is uniform over all feasible $\theta$ and all incident maximal factors. -/)
  (proof := /-- Fix an incident maximal factor $a$, let $S=\partial a$, and lower its $i$th
  exponent by one to obtain $\alpha$. The tail hypothesis gives
  $p_{\theta^*}([-C_t,C_t]^n)\geq1/2$. Partition each support coordinate into
  $N=\max\{d+1,\lceil64|S|u\rceil\}$ intervals. Feasibility and the degree bound imply that the
  energy oscillates by at most $1/32$ on every support cell. Apply
  \cref{lem:finite-product-polynomial-coefficient-l2-bound} to
  $P_y(z)=\partial_iE_{\theta-\theta^*}(z,y)$ and then
  \cref{lem:support-cell-density-comparison} to the exponential-family density on that cell.
  Maximality of $a$ excludes any factor with an exterior coordinate from contributing to the
  coefficient of $z^\alpha$; the remaining coefficient is
  $a_i(\theta_a-\theta_a^*)$, whose absolute value dominates
  $|\theta_a-\theta_a^*|$. Sum over support cells, integrate over the exterior box by Fubini,
  and use the cube-mass lower bound. The polynomial moment estimate
  \cref{lem:tail-decay-integrable-norm-pow} makes the squared energy derivative integrable, so
  its integral over the cube is at most its integral over the whole space. Finally
  $|S|\leq w$, $|S|\leq d$, and
  $N\leq66du$ give the displayed uniform constant. -/)
  (title := /-- Weighted support-box estimate for a maximal-factor coefficient -/)
  (latexEnv := "lemma")]
lemma support_box_weighted_coefficient_bound :
    ∀ {n : ℕ} (d : ℕ)
      (factors : Finset (polynomial_factor n)) (thetaStar : polynomial_factor n → ℝ)
      (i : Fin n) (B tailRate : ℝ) (Ct : ℕ) (p : MeasureTheory.Measure (Fin n → ℝ))
      [MeasureTheory.IsProbabilityMeasure p],
      family_degree_at_most factors d →
      unit_base_polynomial_exponential_family factors thetaStar p →
      0 < B → parameter_feasible factors B thetaStar →
      1 + (1 / 1024 : ℝ) ≤ (d : ℝ) * B * (Ct : ℝ) ^ d →
      tail_decay_condition d tailRate Ct p →
      ∀ theta, parameter_feasible factors B theta →
        ∀ factor ∈ incident_maximal_factors factors i,
          (thetaStar factor - theta factor) ^ 2 ≤
            (4 * Real.exp (1 / 32 : ℝ) *
              (792 * (d : ℝ) ^ 2 * ((d : ℝ) * B * (Ct : ℝ) ^ d)) ^
                (2 * d * interaction_order factors)) *
              ((1 / 2 : ℝ) * ∫ x,
                (energy_first_partial factors
                  (fun a => theta a - thetaStar a) i x) ^ 2 ∂p) := by
  intro n d factors thetaStar i B tailRate Ct p _ hdegree hfamily hB hthetaStar
    hu htail theta htheta factor hfactor
  have hfactorMax : factor ∈ maximal_factors factors := by
    exact (Finset.mem_filter.mp hfactor).1
  have hiSupport : i ∈ factor_support factor := by
    exact (Finset.mem_filter.mp hfactor).2
  have hfactorMem : factor ∈ factors := by
    exact (Finset.mem_filter.mp hfactorMax).1
  have hmaximal : ¬ ∃ larger ∈ factors,
      factor_support factor ⊆ factor_support larger ∧
        factor_support factor ≠ factor_support larger := by
    exact (Finset.mem_filter.mp hfactorMax).2
  have hiPositive : 0 < factor i := by
    simpa [factor_support] using hiSupport
  have hdTwo : 2 ≤ d := htail.2.1
  have hdPositive : 0 < d := by omega
  have hCtOne : 1 ≤ (Ct : ℝ) :=
    (le_max_right _ _).trans htail.2.2.1
  have hCtPositive : 0 < (Ct : ℝ) := lt_of_lt_of_le (by norm_num) hCtOne
  let support := factor_support factor
  let s := support.card
  have hsPositive : 0 < s := by
    dsimp [s, support]
    exact Finset.card_pos.mpr ⟨i, hiSupport⟩
  have hsDegree : s ≤ d := by
    calc
      s = ∑ j ∈ support, 1 := by simp [s]
      _ ≤ ∑ j ∈ support, factor j := by
        apply Finset.sum_le_sum
        intro j hj
        have hjPositive : 0 < factor j := by
          simpa [support, factor_support] using hj
        omega
      _ ≤ ∑ j, factor j := by
        exact Finset.sum_le_sum_of_subset (by simp [support])
      _ ≤ d := hdegree factor hfactorMem
  have hsOrder : s ≤ interaction_order factors := by
    dsimp [interaction_order]
    exact Finset.le_sup (f := fun a => (factor_support a).card) hfactorMem
  have htailRate : 0 < tailRate := htail.1
  have hdReal : 0 < (d : ℝ) - 1 := by
    have hdTwoReal : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdTwo
    linarith
  have hdSub : (d : ℝ) - 1 = ((d - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hroot :
      Real.rpow (Real.log 2 / tailRate) (1 / ((d : ℝ) - 1)) ≤ (Ct : ℝ) :=
    (le_max_left _ _).trans htail.2.2.1
  have hlogPositive : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratioNonnegative : 0 ≤ Real.log 2 / tailRate :=
    div_nonneg hlogPositive.le htailRate.le
  have htailExponent : Real.log 2 ≤ tailRate * (Ct : ℝ) ^ (d - 1) := by
    have hpower := Real.rpow_le_rpow
      (Real.rpow_nonneg hratioNonnegative _) hroot hdReal.le
    have hmul : (1 / ((d : ℝ) - 1)) * ((d : ℝ) - 1) = 1 := by
      field_simp
    rw [← Real.rpow_mul hratioNonnegative, hmul, Real.rpow_one, hdSub,
      Real.rpow_natCast] at hpower
    calc
      Real.log 2 = tailRate * (Real.log 2 / tailRate) := by
        field_simp [ne_of_gt htailRate]
      _ ≤ tailRate * (Ct : ℝ) ^ (d - 1) :=
        mul_le_mul_of_nonneg_left hpower htailRate.le
  let cube : Set (Fin n → ℝ) := {x | ‖x‖ ≤ (Ct : ℝ)}
  have hcubeMeasurable : MeasurableSet cube := by
    dsimp [cube]
    exact measurableSet_le continuous_norm.measurable measurable_const
  have hcubeComplement : cubeᶜ = {x : Fin n → ℝ | (Ct : ℝ) < ‖x‖} := by
    ext x
    simp [cube]
  have htailHalf : p.real cubeᶜ ≤ (1 / 2 : ℝ) := by
    rw [hcubeComplement]
    calc
      p.real {x : Fin n → ℝ | (Ct : ℝ) < ‖x‖} ≤
          Real.exp (-tailRate * (Ct : ℝ) ^ (d - 1)) :=
        htail.2.2.2.2 (Ct : ℝ) le_rfl
      _ ≤ Real.exp (-Real.log 2) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = 1 / 2 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
  have hcubeMass : (1 / 2 : ℝ) ≤ p.real cube := by
    have hsum := MeasureTheory.probReal_add_probReal_compl (μ := p) hcubeMeasurable
    linarith
  let u : ℝ := (d : ℝ) * B * (Ct : ℝ) ^ d
  have huLower : 1 + (1 / 1024 : ℝ) ≤ u := by
    simpa [u] using hu
  have huOne : 1 ≤ u := by linarith
  have huPositive : 0 < u := lt_of_lt_of_le (by norm_num) huOne
  let N : ℕ := max (d + 1) ⌈64 * (s : ℝ) * u⌉₊
  have hNLower : d + 1 ≤ N := by
    exact le_max_left _ _
  have hNPositive : 0 < N := lt_of_lt_of_le (by omega) hNLower
  have hNRealPositive : 0 < (N : ℝ) := by exact_mod_cast hNPositive
  have hNUpper : (N : ℝ) ≤ 66 * (d : ℝ) * u := by
    rw [show (N : ℝ) = max ((d + 1 : ℕ) : ℝ)
        ((⌈64 * (s : ℝ) * u⌉₊ : ℕ) : ℝ) by
      simp [N, Nat.cast_max]]
    apply max_le
    · norm_num [Nat.cast_add]
      have hdRealLower : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdTwo
      nlinarith
    · have hsReal : (s : ℝ) ≤ (d : ℝ) := by exact_mod_cast hsDegree
      have hargNonnegative : 0 ≤ 64 * (s : ℝ) * u := by positivity
      have hceil := Nat.ceil_lt_add_one hargNonnegative
      have hdRealLower : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdTwo
      nlinarith
  let h : ℝ := 2 * (Ct : ℝ) / (N : ℝ)
  have hhPositive : 0 < h := by
    dsimp [h]
    positivity
  have hNh : (N : ℝ) * h = 2 * (Ct : ℝ) := by
    dsimp [h]
    field_simp
  letI supportFintype : Fintype {j : Fin n // j ∈ support} := Fintype.ofFinite _
  let e : Fin s ≃ {j : Fin n // j ∈ support} := (Finset.equivFin support).symm
  let reindex : (Fin s → ℝ) ≃ᵐ ({j : Fin n // j ∈ support} → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : {j : Fin n // j ∈ support} => ℝ) e
  let split : (Fin n → ℝ) ≃ᵐ
      (({j : Fin n // j ∈ support} → ℝ) ×
        ({j : Fin n // j ∉ support} → ℝ)) :=
    MeasurableEquiv.piEquivPiSubtypeProd (π := fun _ : Fin n => ℝ)
      (fun j : Fin n => j ∈ support)
  let combine (z : Fin s → ℝ) (y : {j : Fin n // j ∉ support} → ℝ) :
      Fin n → ℝ := split.symm (reindex z, y)
  have hcombineSupport (z : Fin s → ℝ)
      (y : {j : Fin n // j ∉ support} → ℝ) (j : Fin s) :
      combine z y (e j).1 = z j := by
    simp [combine, split]
    exact MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : {j : Fin n // j ∈ support} => ℝ) e z j
  have hcombineExterior (z : Fin s → ℝ)
      (y : {j : Fin n // j ∉ support} → ℝ)
      (j : {j : Fin n // j ∉ support}) :
      combine z y j.1 = y j := by
    simp [combine, split, j.property]
  let active := factors_at factors i
  have hfactorActive : factor ∈ active := by
    simp [active, factors_at, hfactorMem, factor_support, hiPositive]
  let derivExponent (a : polynomial_factor n) : polynomial_factor n :=
    Function.update a i (a i - 1)
  let project (a : polynomial_factor n) : polynomial_factor s := fun j =>
    derivExponent a (e j).1
  let terms : Finset (polynomial_factor s) := active.image project
  let alpha : polynomial_factor s := project factor
  have halpha : alpha ∈ terms := by
    exact Finset.mem_image.mpr ⟨factor, hfactorActive, rfl⟩
  have htermsDegree : ∀ beta ∈ terms, ∀ j, beta j < d := by
    intro beta hbeta j
    rcases Finset.mem_image.mp hbeta with ⟨a, ha, rfl⟩
    have haActive := (Finset.mem_filter.mp ha)
    have haMem : a ∈ factors := haActive.1
    have haiSupport : i ∈ factor_support a := haActive.2
    have haiPositive : 0 < a i := by
      simpa [factor_support] using haiSupport
    have haDegree : (∑ k, a k) ≤ d := hdegree a haMem
    by_cases hj : (e j).1 = i
    · simp [project, derivExponent, Function.update, hj]
      have haiLe : a i ≤ ∑ k, a k :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    · simp [project, derivExponent, Function.update, hj]
      have hpair : a (e j).1 + a i ≤ ∑ k, a k := by
        calc
          a (e j).1 + a i = ∑ k ∈ {(e j).1, i}, a k := by
            simp [hj, add_comm]
          _ ≤ ∑ k, a k := by
            exact Finset.sum_le_sum_of_subset (by simp)
      omega
  have hprojectUnique : ∀ a ∈ active, project a = alpha → a = factor := by
    intro a ha hproject
    have haInfo := Finset.mem_filter.mp ha
    have haMem : a ∈ factors := haInfo.1
    have haiPositive : 0 < a i := by
      simpa [factor_support] using haInfo.2
    have hsupportSubset : factor_support factor ⊆ factor_support a := by
      intro j hj
      let k : Fin s := e.symm ⟨j, by simpa [support] using hj⟩
      have hek : (e k).1 = j := by
        exact congrArg Subtype.val (e.apply_symm_apply
          ⟨j, by simpa [support] using hj⟩)
      have hcoord := congrFun hproject k
      have hjPositive : 0 < factor j := by
        simpa [factor_support] using hj
      have hajPositive : 0 < a j := by
        by_cases hji : j = i
        · simpa [hji] using haiPositive
        · have hji' : i ≠ j := Ne.symm hji
          have hvalue : a j = factor j := by
            simpa [alpha, project, derivExponent, Function.update, hek, hji, hji'] using
              hcoord
          simpa [hvalue] using hjPositive
      simpa [factor_support] using hajPositive
    have hsupportEq : factor_support factor = factor_support a := by
      by_contra hne
      exact hmaximal ⟨a, haMem, hsupportSubset, hne⟩
    funext j
    by_cases hj : j ∈ factor_support factor
    · let k : Fin s := e.symm ⟨j, by simpa [support] using hj⟩
      have hek : (e k).1 = j := by
        exact congrArg Subtype.val (e.apply_symm_apply
          ⟨j, by simpa [support] using hj⟩)
      have hcoord := congrFun hproject k
      by_cases hji : j = i
      · have hsub : a j - 1 = factor j - 1 := by
          simpa [alpha, project, derivExponent, Function.update, hek, hji] using hcoord
        have hajPositive : 0 < a j := by simpa [hji] using haiPositive
        have hjPositive : 0 < factor j := by
          simpa [factor_support] using hj
        omega
      · have hji' : i ≠ j := Ne.symm hji
        simpa [alpha, project, derivExponent, Function.update, hek, hji, hji'] using hcoord
    · have hja : j ∉ factor_support a := by simpa [hsupportEq] using hj
      have hfactorZero : factor j = 0 := by
        simpa [factor_support, Nat.not_lt] using hj
      have haZero : a j = 0 := by
        simpa [factor_support, Nat.not_lt] using hja
      rw [haZero, hfactorZero]
  let outsideMonomial (a : polynomial_factor n)
      (y : {j : Fin n // j ∉ support} → ℝ) : ℝ :=
    ∏ j, y j ^ a j.1
  have houtsideFactor (y : {j : Fin n // j ∉ support} → ℝ) :
      outsideMonomial factor y = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    have hzero : factor j.1 = 0 := by
      have := j.property
      simp only [support] at this
      simpa [factor_support, Nat.not_lt] using this
    simp [hzero]
  let coeff (y : {j : Fin n // j ∉ support} → ℝ)
      (beta : polynomial_factor s) : ℝ :=
    ∑ a ∈ active with project a = beta,
      (theta a - thetaStar a) * (a i : ℝ) * outsideMonomial a y
  have hcoeffAlpha (y : {j : Fin n // j ∉ support} → ℝ) :
      coeff y alpha = (theta factor - thetaStar factor) * (factor i : ℝ) := by
    rw [show coeff y alpha =
        ∑ a ∈ active with project a = alpha,
          (theta a - thetaStar a) * (a i : ℝ) * outsideMonomial a y by rfl]
    rw [Finset.sum_eq_single factor]
    · rw [houtsideFactor]
      ring
    · intro a ha hne
      simp only [Finset.mem_filter] at ha
      exact (hne (hprojectUnique a ha.1 ha.2)).elim
    · simp [hfactorActive, alpha]
  have hfirstAsMonomial (a : polynomial_factor n) (x : Fin n → ℝ) :
      monomial_first_partial a i x =
        (a i : ℝ) * monomial_value (derivExponent a) x := by
    unfold monomial_first_partial monomial_value
    by_cases hai : a i = 0
    · simp [hai]
    · have hcast : (a i : ℝ) ≠ 0 := by exact_mod_cast hai
      apply mul_left_cancel₀ hcast
      rw [mul_assoc]
      have hprod :
          (∏ j ∈ Finset.univ.erase i, x j ^ a j) =
            ∏ j ∈ Finset.univ.erase i, x j ^ derivExponent a j := by
        apply Finset.prod_congr rfl
        intro j hj
        simp [derivExponent, Function.update, Finset.ne_of_mem_erase hj]
      rw [← Finset.mul_prod_erase Finset.univ
        (fun j => x j ^ derivExponent a j) (Finset.mem_univ i)]
      rw [show derivExponent a i = a i - 1 by simp [derivExponent], hprod]
  have hmonomialSplit (a : polynomial_factor n) (z : Fin s → ℝ)
      (y : {j : Fin n // j ∉ support} → ℝ) :
      monomial_value (derivExponent a) (combine z y) =
        monomial_value (project a) z * outsideMonomial a y := by
    have hsupportProduct :
        (∏ j ∈ support, combine z y j ^ derivExponent a j) =
          ∏ k, z k ^ project a k := by
      rw [Finset.prod_subtype support (fun _ => Iff.rfl)]
      symm
      apply Fintype.prod_equiv e
      intro k
      rw [hcombineSupport]
    have hexteriorProduct :
        (∏ j ∈ Finset.univ \ support, combine z y j ^ derivExponent a j) =
          ∏ j, y j ^ a j.1 := by
      rw [Finset.prod_subtype (p := fun x => x ∉ support)
        (Finset.univ \ support) (by simp)]
      apply Fintype.prod_congr
      intro j
      have hji : j.1 ≠ i := by
        intro hji
        apply j.property
        simpa [support, hji] using hiSupport
      rw [hcombineExterior]
      simp [derivExponent, Function.update, hji]
    unfold monomial_value outsideMonomial
    rw [← hsupportProduct, ← hexteriorProduct]
    rw [mul_comm]
    exact (Finset.prod_sdiff (s₁ := support) (s₂ := Finset.univ)
      (fun _ _ => Finset.mem_univ _)).symm
  let delta : polynomial_factor n → ℝ := fun a => theta a - thetaStar a
  have henergyActive (x : Fin n → ℝ) :
      energy_first_partial factors delta i x =
        ∑ a ∈ active, delta a * monomial_first_partial a i x := by
    unfold energy_first_partial
    symm
    apply Finset.sum_subset
    · exact Finset.filter_subset _ _
    · intro a haFactors haNotActive
      have haiZero : a i = 0 := by
        simp only [active, factors_at, Finset.mem_filter, haFactors, true_and,
          factor_support, Finset.mem_filter, Finset.mem_univ, true_and] at haNotActive
        omega
      simp [monomial_first_partial, haiZero]
  have hpolynomialIdentity (z : Fin s → ℝ)
      (y : {j : Fin n // j ∉ support} → ℝ) :
      exponential_energy terms (coeff y) z =
        energy_first_partial factors delta i (combine z y) := by
    calc
      exponential_energy terms (coeff y) z =
          ∑ beta ∈ terms, ∑ a ∈ active with project a = beta,
            ((theta a - thetaStar a) * (a i : ℝ) * outsideMonomial a y) *
              monomial_value beta z := by
        unfold exponential_energy coeff
        simp_rw [Finset.sum_mul]
      _ = ∑ beta ∈ terms, ∑ a ∈ active with project a = beta,
            ((theta a - thetaStar a) * (a i : ℝ) * outsideMonomial a y) *
              monomial_value (project a) z := by
        apply Finset.sum_congr rfl
        intro beta hbeta
        apply Finset.sum_congr rfl
        intro a ha
        simp only [Finset.mem_filter] at ha
        rw [ha.2]
      _ = ∑ a ∈ active with project a ∈ terms,
            ((theta a - thetaStar a) * (a i : ℝ) * outsideMonomial a y) *
              monomial_value (project a) z := by
        exact Finset.sum_fiberwise_eq_sum_filter active terms project
          (fun a => ((theta a - thetaStar a) * (a i : ℝ) * outsideMonomial a y) *
            monomial_value (project a) z)
      _ = ∑ a ∈ active,
            ((theta a - thetaStar a) * (a i : ℝ) * outsideMonomial a y) *
              monomial_value (project a) z := by
        rw [Finset.filter_eq_self.mpr]
        intro a ha
        exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
      _ = energy_first_partial factors delta i (combine z y) := by
        rw [henergyActive]
        apply Finset.sum_congr rfl
        intro a ha
        rw [hfirstAsMonomial, hmonomialSplit]
        simp only [delta]
        ring
  have hcoordinateBound (x : Fin n → ℝ) (hx : x ∈ cube) (j : Fin n) :
      |x j| ≤ (Ct : ℝ) := by
    calc
      |x j| = ‖x j‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x‖ := norm_le_pi_norm x j
      _ ≤ (Ct : ℝ) := hx
  have hmonomialPartialBound (a : polynomial_factor n) (ha : a ∈ factors)
      (j : Fin n) (haj : 0 < a j) (x : Fin n → ℝ) (hx : x ∈ cube) :
      |monomial_first_partial a j x| ≤
        (d : ℝ) * (Ct : ℝ) ^ (d - 1) := by
    have haDegree : (∑ k, a k) ≤ d := hdegree a ha
    have hajLe : a j ≤ d := by
      have : a j ≤ ∑ k, a k :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      omega
    have hsum : (∑ k, a k) = a j + ∑ k ∈ Finset.univ.erase j, a k := by
      simpa only [Finset.sdiff_singleton_eq_erase] using
        (Finset.sum_eq_add_sum_sdiff_singleton j a (by simp))
    have hpower : a j - 1 + ∑ k ∈ Finset.univ.erase j, a k =
        (∑ k, a k) - 1 := by omega
    calc
      |monomial_first_partial a j x| =
          (a j : ℝ) * |x j| ^ (a j - 1) *
            ∏ k ∈ Finset.univ.erase j, |x k| ^ a k := by
        unfold monomial_first_partial
        rw [abs_mul, abs_mul, Finset.abs_prod]
        rw [abs_of_nonneg (Nat.cast_nonneg _)]
        simp only [abs_pow]
      _ ≤ (a j : ℝ) * (Ct : ℝ) ^ (a j - 1) *
            ∏ k ∈ Finset.univ.erase j, (Ct : ℝ) ^ a k := by
        gcongr
        · exact hcoordinateBound x hx j
        · exact hcoordinateBound x hx _
      _ = (a j : ℝ) * (Ct : ℝ) ^ ((∑ k, a k) - 1) := by
        rw [Finset.prod_pow_eq_pow_sum]
        rw [mul_assoc, ← pow_add, hpower]
      _ ≤ (d : ℝ) * (Ct : ℝ) ^ (d - 1) := by
        apply mul_le_mul
        · exact_mod_cast hajLe
        · apply pow_le_pow_right₀ hCtOne
          omega
        · positivity
        · positivity
  have hpartialBound (j : Fin n) (x : Fin n → ℝ) (hx : x ∈ cube) :
      |energy_first_partial factors thetaStar j x| ≤
        (d : ℝ) * B * (Ct : ℝ) ^ (d - 1) := by
    have hactiveSum : energy_first_partial factors thetaStar j x =
        ∑ a ∈ factors_at factors j,
          thetaStar a * monomial_first_partial a j x := by
      unfold energy_first_partial
      symm
      apply Finset.sum_subset
      · exact Finset.filter_subset _ _
      · intro a haFactors haNotActive
        have hajZero : a j = 0 := by
          simp only [factors_at, Finset.mem_filter, haFactors, true_and,
            factor_support, Finset.mem_filter, Finset.mem_univ, true_and] at haNotActive
          omega
        simp [monomial_first_partial, hajZero]
    rw [hactiveSum]
    calc
      |∑ a ∈ factors_at factors j,
          thetaStar a * monomial_first_partial a j x| ≤
          ∑ a ∈ factors_at factors j,
            |thetaStar a * monomial_first_partial a j x| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ factors_at factors j,
            |thetaStar a| * ((d : ℝ) * (Ct : ℝ) ^ (d - 1)) := by
        apply Finset.sum_le_sum
        intro a ha
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left
        · have haInfo := Finset.mem_filter.mp ha
          have hajPositive : 0 < a j := by
            simpa [factor_support] using haInfo.2
          exact hmonomialPartialBound a haInfo.1 j hajPositive x hx
        · positivity
      _ = (∑ a ∈ factors_at factors j, |thetaStar a|) *
            ((d : ℝ) * (Ct : ℝ) ^ (d - 1)) := by
        rw [Finset.sum_mul]
      _ ≤ B * ((d : ℝ) * (Ct : ℝ) ^ (d - 1)) := by
        apply mul_le_mul_of_nonneg_right (hthetaStar j)
        positivity
      _ = (d : ℝ) * B * (Ct : ℝ) ^ (d - 1) := by ring
  have hderivMonomial (a : polynomial_factor n) (j : Fin n)
      (x : Fin n → ℝ) (t : ℝ) :
      HasDerivAt (fun q => monomial_value a (Function.update x j q))
        (monomial_first_partial a j (Function.update x j t)) t := by
    have hfun :
        (fun q => monomial_value a (Function.update x j q)) =
          fun q => q ^ a j * ∏ k ∈ Finset.univ.erase j, x k ^ a k := by
      funext q
      unfold monomial_value
      rw [← Finset.mul_prod_erase Finset.univ
        (fun k => Function.update x j q k ^ a k) (Finset.mem_univ j)]
      rw [Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro k hk
      simp [Function.update, Finset.ne_of_mem_erase hk]
    have hvalue :
        monomial_first_partial a j (Function.update x j t) =
          (a j : ℝ) * t ^ (a j - 1) *
            ∏ k ∈ Finset.univ.erase j, x k ^ a k := by
      unfold monomial_first_partial
      rw [Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro k hk
      simp [Function.update, Finset.ne_of_mem_erase hk]
    rw [hfun, hvalue]
    exact (hasDerivAt_pow (a j) t).mul_const
      (∏ k ∈ Finset.univ.erase j, x k ^ a k)
  have hderivEnergy (j : Fin n) (x : Fin n → ℝ) (t : ℝ) :
      HasDerivAt
        (fun q => exponential_energy factors thetaStar (Function.update x j q))
        (energy_first_partial factors thetaStar j (Function.update x j t)) t := by
    unfold exponential_energy energy_first_partial
    have hsumfun :
        (fun q => ∑ a ∈ factors,
          thetaStar a * monomial_value a (Function.update x j q)) =
          ∑ a ∈ factors, fun q =>
            thetaStar a * monomial_value a (Function.update x j q) := by
      funext q
      simp
    rw [hsumfun]
    exact HasDerivAt.sum (u := factors) (fun a ha =>
      (hderivMonomial a j x t).const_mul (thetaStar a))
  have hupdateCube (x : Fin n → ℝ) (hx : x ∈ cube) (j : Fin n)
      (t : ℝ) (ht : t ∈ Set.Icc (-(Ct : ℝ)) (Ct : ℝ)) :
      Function.update x j t ∈ cube := by
    change ‖Function.update x j t‖ ≤ (Ct : ℝ)
    apply (pi_norm_le_iff_of_nonneg hCtPositive.le).2
    intro k
    by_cases hkj : k = j
    · subst k
      rw [Function.update_self, Real.norm_eq_abs]
      exact abs_le.mpr ht
    · simp only [Function.update, hkj, ↓reduceIte]
      rw [Real.norm_eq_abs]
      exact hcoordinateBound x hx k
  have hcoordinateLipschitz (x : Fin n → ℝ) (hx : x ∈ cube) (j : Fin n)
      (a b : ℝ) (ha : a ∈ Set.Icc (-(Ct : ℝ)) (Ct : ℝ))
      (hb : b ∈ Set.Icc (-(Ct : ℝ)) (Ct : ℝ)) :
      |exponential_energy factors thetaStar (Function.update x j a) -
          exponential_energy factors thetaStar (Function.update x j b)| ≤
        ((d : ℝ) * B * (Ct : ℝ) ^ (d - 1)) * |a - b| := by
    let f : ℝ → ℝ := fun t =>
      exponential_energy factors thetaStar (Function.update x j t)
    have hf : ∀ t ∈ Set.Icc (-(Ct : ℝ)) (Ct : ℝ), DifferentiableAt ℝ f t := by
      intro t ht
      exact (hderivEnergy j x t).differentiableAt
    have hbound : ∀ t ∈ Set.Icc (-(Ct : ℝ)) (Ct : ℝ),
        ‖deriv f t‖ ≤ (d : ℝ) * B * (Ct : ℝ) ^ (d - 1) := by
      intro t ht
      rw [(hderivEnergy j x t).deriv]
      rw [Real.norm_eq_abs]
      exact hpartialBound j (Function.update x j t) (hupdateCube x hx j t ht)
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le hf hbound
      (convex_Icc (-(Ct : ℝ)) (Ct : ℝ)) hb ha
    simpa [f, Real.norm_eq_abs] using hmv
  have htelescoping : ∀ T : Finset (Fin n), T ⊆ support →
      ∀ x x' : Fin n → ℝ, x ∈ cube → x' ∈ cube →
        (∀ j, j ∉ T → x j = x' j) →
        (∀ j ∈ T, |x j - x' j| ≤ h) →
        |exponential_energy factors thetaStar x -
            exponential_energy factors thetaStar x'| ≤
          (T.card : ℝ) * ((d : ℝ) * B * (Ct : ℝ) ^ (d - 1)) * h := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        intro hsubset x x' hx hx' hagree hdiff
        have hxx' : x = x' := by
          funext j
          exact hagree j (by simp)
        simp [hxx']
    | @insert j T hj ih =>
        intro hsubset x x' hx hx' hagree hdiff
        have hjSupport : j ∈ support := hsubset (by simp)
        have hTSubset : T ⊆ support := fun k hk => hsubset (by simp [hk])
        let mid : Fin n → ℝ := Function.update x j (x' j)
        have hxjInterval : x j ∈ Set.Icc (-(Ct : ℝ)) (Ct : ℝ) :=
          abs_le.mp (hcoordinateBound x hx j)
        have hxj'Interval : x' j ∈ Set.Icc (-(Ct : ℝ)) (Ct : ℝ) :=
          abs_le.mp (hcoordinateBound x' hx' j)
        have hmidCube : mid ∈ cube := by
          exact hupdateCube x hx j (x' j) hxj'Interval
        have hfirst :
            |exponential_energy factors thetaStar x -
                exponential_energy factors thetaStar mid| ≤
              ((d : ℝ) * B * (Ct : ℝ) ^ (d - 1)) * h := by
          have hlip := hcoordinateLipschitz x hx j (x j) (x' j)
            hxjInterval hxj'Interval
          have hupdateSelf : Function.update x j (x j) = x := by
            funext k
            by_cases hkj : k = j <;> simp [Function.update, hkj]
          rw [hupdateSelf] at hlip
          exact hlip.trans (mul_le_mul_of_nonneg_left (hdiff j (by simp)) (by positivity))
        have hmidAgree : ∀ k, k ∉ T → mid k = x' k := by
          intro k hk
          by_cases hkj : k = j
          · subst k
            simp [mid]
          · simp only [mid, Function.update, hkj, ↓reduceIte]
            exact hagree k (by simp [hk, hkj])
        have hmidDiff : ∀ k ∈ T, |mid k - x' k| ≤ h := by
          intro k hk
          have hkj : k ≠ j := by
            intro hEq
            subst k
            exact hj hk
          simp only [mid, Function.update, hkj, ↓reduceIte]
          exact hdiff k (by simp [hk])
        have hrest := ih hTSubset mid x' hmidCube hx' hmidAgree hmidDiff
        calc
          |exponential_energy factors thetaStar x -
              exponential_energy factors thetaStar x'| ≤
              |exponential_energy factors thetaStar x -
                exponential_energy factors thetaStar mid| +
              |exponential_energy factors thetaStar mid -
                exponential_energy factors thetaStar x'| := by
            exact abs_sub_le _ _ _
          _ ≤ ((d : ℝ) * B * (Ct : ℝ) ^ (d - 1)) * h +
              (T.card : ℝ) * ((d : ℝ) * B * (Ct : ℝ) ^ (d - 1)) * h :=
            add_le_add hfirst hrest
          _ = ((insert j T).card : ℝ) *
              ((d : ℝ) * B * (Ct : ℝ) ^ (d - 1)) * h := by
            rw [Finset.card_insert_of_notMem hj]
            push_cast
            ring
  have henergyOscillation (x x' : Fin n → ℝ) (hx : x ∈ cube) (hx' : x' ∈ cube)
      (hagree : ∀ j, j ∉ support → x j = x' j)
      (hdiff : ∀ j ∈ support, |x j - x' j| ≤ h) :
      |exponential_energy factors thetaStar x -
          exponential_energy factors thetaStar x'| ≤
        (s : ℝ) * ((d : ℝ) * B * (Ct : ℝ) ^ (d - 1)) * h := by
    simpa [s] using htelescoping support (fun _ hmem => hmem) x x' hx hx' hagree hdiff
  have hcellCountLower : 64 * (s : ℝ) * u ≤ (N : ℝ) := by
    calc
      64 * (s : ℝ) * u ≤ (⌈64 * (s : ℝ) * u⌉₊ : ℕ) :=
        Nat.le_ceil (64 * (s : ℝ) * u)
      _ ≤ (N : ℕ) := by
        dsimp [N]
        exact_mod_cast (le_max_right (d + 1) ⌈64 * (s : ℝ) * u⌉₊)
  have hoscillationSmall :
      (s : ℝ) * ((d : ℝ) * B * (Ct : ℝ) ^ (d - 1)) * h ≤ 1 / 32 := by
    have hpow : (Ct : ℝ) ^ (d - 1) * (Ct : ℝ) = (Ct : ℝ) ^ d := by
      conv_rhs => rw [show d = (d - 1) + 1 by omega]
      rw [pow_succ]
    have heq :
        (s : ℝ) * ((d : ℝ) * B * (Ct : ℝ) ^ (d - 1)) * h =
          (2 * (s : ℝ) * u) / (N : ℝ) := by
      dsimp [h, u]
      rw [div_eq_mul_inv]
      rw [← hpow]
      ring
    rw [heq]
    apply (div_le_iff₀ hNRealPositive).2
    nlinarith [hcellCountLower]
  let lower (q : Fin s → Fin N) (j : Fin s) : ℝ :=
    -(Ct : ℝ) + (q j : ℝ) * h
  let cell (q : Fin s → Fin N) : Set (Fin s → ℝ) :=
    {z | ∀ j, lower q j ≤ z j ∧ z j ≤ lower q j + h}
  have hcellSubset (q : Fin s → Fin N) (j : Fin s) :
      Set.Icc (lower q j) (lower q j + h) ⊆
        Set.Icc (-(Ct : ℝ)) (Ct : ℝ) := by
    intro t ht
    constructor
    · calc
        -(Ct : ℝ) ≤ lower q j := by
          dsimp [lower]
          exact le_add_of_nonneg_right
            (mul_nonneg (Nat.cast_nonneg _) hhPositive.le)
        _ ≤ t := ht.1
    · have hq : ((q j : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by
        exact_mod_cast (q j).isLt
      dsimp [lower] at ht ⊢
      calc
        t ≤ -(Ct : ℝ) + (q j : ℝ) * h + h := ht.2
        _ = -(Ct : ℝ) + (((q j : ℕ) : ℝ) + 1) * h := by ring
        _ ≤ -(Ct : ℝ) + (N : ℝ) * h := by gcongr
        _ = (Ct : ℝ) := by rw [hNh]; ring
  have hcellMeasurable (q : Fin s → Fin N) : MeasurableSet (cell q) := by
    have hEq : cell q = Set.Icc (lower q) (fun j => lower q j + h) := by
      ext z
      simp only [cell, Set.mem_setOf_eq, Set.mem_Icc]
      constructor
      · intro hz
        exact ⟨fun j => (hz j).1, fun j => (hz j).2⟩
      · rintro ⟨hz, hz'⟩ j
        exact ⟨hz j, hz' j⟩
    rw [hEq]
    exact measurableSet_Icc
  have hcellVolume (q : Fin s → Fin N) :
      0 < (MeasureTheory.volume : MeasureTheory.Measure (Fin s → ℝ)).real (cell q) := by
    have hEq : cell q = Set.Icc (lower q) (fun j => lower q j + h) := by
      ext z
      simp only [cell, Set.mem_setOf_eq, Set.mem_Icc]
      constructor
      · intro hz
        exact ⟨fun j => (hz j).1, fun j => (hz j).2⟩
      · rintro ⟨hz, hz'⟩ j
        exact ⟨hz j, hz' j⟩
    rw [hEq]
    change 0 < (MeasureTheory.volume
      (Set.Icc (lower q) (fun j => lower q j + h))).toReal
    rw [Real.volume_Icc_pi_toReal]
    · simp only [add_sub_cancel_left]
      positivity
    · intro j
      linarith
  let exteriorCube : Set ({j : Fin n // j ∉ support} → ℝ) :=
    {y | ∀ j, |y j| ≤ (Ct : ℝ)}
  have hcombineCube (q : Fin s → Fin N) (z : Fin s → ℝ) (hz : z ∈ cell q)
      (y : {j : Fin n // j ∉ support} → ℝ) (hy : y ∈ exteriorCube) :
      combine z y ∈ cube := by
    change ‖combine z y‖ ≤ (Ct : ℝ)
    apply (pi_norm_le_iff_of_nonneg hCtPositive.le).2
    intro k
    rw [Real.norm_eq_abs]
    by_cases hk : k ∈ support
    · let j : Fin s := e.symm ⟨k, hk⟩
      have hej : (e j).1 = k := by
        exact congrArg Subtype.val (e.apply_symm_apply ⟨k, hk⟩)
      rw [← hej, hcombineSupport]
      exact abs_le.mpr (hcellSubset q j (hz j))
    · have hout := hcombineExterior z y ⟨k, hk⟩
      rw [hout]
      exact hy ⟨k, hk⟩
  have hcombineAgree (z z' : Fin s → ℝ)
      (y : {j : Fin n // j ∉ support} → ℝ) :
      ∀ k, k ∉ support → combine z y k = combine z' y k := by
    intro k hk
    let k' : {j : Fin n // j ∉ support} := ⟨k, hk⟩
    rw [show k = k'.1 by rfl, hcombineExterior, hcombineExterior]
  have hcombineDistance (q : Fin s → Fin N) (z z' : Fin s → ℝ)
      (hz : z ∈ cell q) (hz' : z' ∈ cell q) :
      ∀ k ∈ support, |combine z (fun _ => 0) k -
          combine z' (fun _ => 0) k| ≤ h := by
    intro k hk
    let j : Fin s := e.symm ⟨k, hk⟩
    have hej : (e j).1 = k := by
      exact congrArg Subtype.val (e.apply_symm_apply ⟨k, hk⟩)
    rw [← hej, hcombineSupport, hcombineSupport]
    apply abs_le.mpr
    constructor <;> linarith [(hz j).1, (hz j).2, (hz' j).1, (hz' j).2]
  rcases hfamily with ⟨Z, hZ, hnormalization, hp⟩
  let densityReal (x : Fin n → ℝ) : ℝ :=
    Real.exp (exponential_energy factors thetaStar x) / Z
  let fiberDensity (y : {j : Fin n // j ∉ support} → ℝ) (z : Fin s → ℝ) : ℝ :=
    densityReal (combine z y)
  have hfiberPositive (y : {j : Fin n // j ∉ support} → ℝ) (z : Fin s → ℝ) :
      0 < fiberDensity y z := by
    dsimp [fiberDensity, densityReal]
    positivity
  have hfiberRatio (q : Fin s → Fin N)
      (y : {j : Fin n // j ∉ support} → ℝ) (hy : y ∈ exteriorCube)
      (z : Fin s → ℝ) (hz : z ∈ cell q)
      (z' : Fin s → ℝ) (hz' : z' ∈ cell q) :
      fiberDensity y z ≤ Real.exp (1 / 32 : ℝ) * fiberDensity y z' := by
    have hx := hcombineCube q z hz y hy
    have hx' := hcombineCube q z' hz' y hy
    have hdiff : ∀ k ∈ support, |combine z y k - combine z' y k| ≤ h := by
      intro k hk
      let j : Fin s := e.symm ⟨k, hk⟩
      have hej : (e j).1 = k := by
        exact congrArg Subtype.val (e.apply_symm_apply ⟨k, hk⟩)
      rw [← hej, hcombineSupport, hcombineSupport]
      apply abs_le.mpr
      constructor <;> linarith [(hz j).1, (hz j).2, (hz' j).1, (hz' j).2]
    have hosc := (henergyOscillation (combine z y) (combine z' y) hx hx'
      (hcombineAgree z z' y) hdiff).trans hoscillationSmall
    have henergyLe : exponential_energy factors thetaStar (combine z y) ≤
        (1 / 32 : ℝ) + exponential_energy factors thetaStar (combine z' y) := by
      have := (le_abs_self
        (exponential_energy factors thetaStar (combine z y) -
          exponential_energy factors thetaStar (combine z' y))).trans hosc
      linarith
    dsimp [fiberDensity, densityReal]
    rw [← mul_div_assoc]
    apply (div_le_div_iff_of_pos_right hZ).2
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr henergyLe
  let P (y : {j : Fin n // j ∉ support} → ℝ) (z : Fin s → ℝ) : ℝ :=
    exponential_energy terms (coeff y) z
  have hPContinuous (y : {j : Fin n // j ∉ support} → ℝ) : Continuous (P y) := by
    unfold P exponential_energy monomial_value
    fun_prop
  have hcombineContinuous (y : {j : Fin n // j ∉ support} → ℝ) :
      Continuous (fun z => combine z y) := by
    rw [continuous_pi_iff]
    intro k
    by_cases hk : k ∈ support
    · let j : Fin s := e.symm ⟨k, hk⟩
      have hej : (e j).1 = k := by
        exact congrArg Subtype.val (e.apply_symm_apply ⟨k, hk⟩)
      have hfun : (fun z => combine z y k) = fun z => z j := by
        funext z
        rw [← hej, hcombineSupport]
      rw [hfun]
      fun_prop
    · have hfun : (fun z => combine z y k) = fun _ => y ⟨k, hk⟩ := by
        funext z
        exact hcombineExterior z y ⟨k, hk⟩
      rw [hfun]
      fun_prop
  have hfiberContinuous (y : {j : Fin n // j ∉ support} → ℝ) :
      Continuous (fiberDensity y) := by
    have henergyContinuous : Continuous
        (fun x => exponential_energy factors thetaStar x) := by
      unfold exponential_energy monomial_value
      fun_prop
    exact (Real.continuous_exp.comp
      (henergyContinuous.comp (hcombineContinuous y))).div_const Z
  have hcellCompact (q : Fin s → Fin N) : IsCompact (cell q) := by
    have hEq : cell q = Set.Icc (lower q) (fun j => lower q j + h) := by
      ext z
      simp only [cell, Set.mem_setOf_eq, Set.mem_Icc]
      constructor
      · intro hz
        exact ⟨fun j => (hz j).1, fun j => (hz j).2⟩
      · rintro ⟨hz, hz'⟩ j
        exact ⟨hz j, hz' j⟩
    rw [hEq]
    exact isCompact_Icc
  have hcoefficientDominates (y : {j : Fin n // j ∉ support} → ℝ) :
      (thetaStar factor - theta factor) ^ 2 ≤ |coeff y alpha| ^ 2 := by
    rw [hcoeffAlpha]
    rw [abs_mul, mul_pow, sq_abs]
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    have hiOne : (1 : ℝ) ≤ (factor i : ℝ) := by exact_mod_cast hiPositive
    have hiSquare : 1 ≤ (factor i : ℝ) ^ 2 := one_le_pow₀ hiOne
    nlinarith [sq_nonneg (theta factor - thetaStar factor)]
  have hcellWeighted (q : Fin s → Fin N)
      (y : {j : Fin n // j ∉ support} → ℝ) (hy : y ∈ exteriorCube) :
      (thetaStar factor - theta factor) ^ 2 *
          (∫ z in cell q, fiberDensity y z ∂MeasureTheory.volume) ≤
        (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d * s) * Real.exp (1 / 32 : ℝ) *
          ∫ z in cell q, P y z ^ 2 * fiberDensity y z ∂MeasureTheory.volume := by
    let mass : ℝ := ∫ z in cell q, fiberDensity y z ∂MeasureTheory.volume
    let plain : ℝ := ∫ z in cell q, P y z ^ 2 ∂MeasureTheory.volume
    let weighted : ℝ :=
      ∫ z in cell q, P y z ^ 2 * fiberDensity y z ∂MeasureTheory.volume
    let A : ℝ := (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d * s)
    have hfIntegrable : MeasureTheory.IntegrableOn (fiberDensity y) (cell q)
        MeasureTheory.volume :=
      (hfiberContinuous y).continuousOn.integrableOn_compact (hcellCompact q)
    have hPIntegrable : MeasureTheory.IntegrableOn (fun z => P y z ^ 2) (cell q)
        MeasureTheory.volume :=
      ((hPContinuous y).pow 2).continuousOn.integrableOn_compact (hcellCompact q)
    have hweightedIntegrable :
        MeasureTheory.IntegrableOn (fun z => P y z ^ 2 * fiberDensity y z) (cell q)
          MeasureTheory.volume :=
      (((hPContinuous y).pow 2).mul (hfiberContinuous y)).continuousOn.integrableOn_compact
        (hcellCompact q)
    have hmassPositive : 0 < mass := by
      apply (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
        (Filter.Eventually.of_forall fun z => (hfiberPositive y z).le) hfIntegrable).2
      have hsupportEq : Function.support (fiberDensity y) ∩ cell q = cell q := by
        ext z
        simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_setOf_eq]
        constructor
        · exact fun hz => hz.2
        · intro hz
          exact ⟨ne_of_gt (hfiberPositive y z), hz⟩
      rw [hsupportEq]
      exact (ENNReal.toReal_pos_iff.mp (hcellVolume q)).1
    have hcoefficient := finite_product_polynomial_coefficient_l2_bound
      d N (Ct : ℝ) h (lower q) terms (coeff y) alpha hdPositive hNLower hCtOne
        hhPositive hNh (hcellSubset q) htermsDegree halpha
    have hdensity := support_cell_density_comparison (cell q) (fiberDensity y) (P y)
      (hcellMeasurable q) (hcellVolume q) hfIntegrable hPIntegrable hweightedIntegrable
      (fun z hz => hfiberPositive y z) (hfiberRatio q y hy)
      (by simpa [mass] using hmassPositive)
    have hcoefficient' : |coeff y alpha| ^ 2 ≤ A /
        (MeasureTheory.volume : MeasureTheory.Measure (Fin s → ℝ)).real (cell q) * plain := by
      simpa [A, plain, P, cell, sq_abs] using hcoefficient
    have hfirst : |coeff y alpha| ^ 2 ≤ A * (plain /
        (MeasureTheory.volume : MeasureTheory.Measure (Fin s → ℝ)).real (cell q)) := by
      calc
        |coeff y alpha| ^ 2 ≤ A /
            (MeasureTheory.volume : MeasureTheory.Measure (Fin s → ℝ)).real (cell q) *
              plain := hcoefficient'
        _ = A * (plain /
            (MeasureTheory.volume : MeasureTheory.Measure (Fin s → ℝ)).real (cell q)) := by
          ring
    have hsecond : A * (plain /
          (MeasureTheory.volume : MeasureTheory.Measure (Fin s → ℝ)).real (cell q)) ≤
        A * (Real.exp (1 / 32 : ℝ) / mass * weighted) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [plain, mass, weighted] using hdensity
      · positivity
    have hthird := mul_le_mul_of_nonneg_right (hfirst.trans hsecond) hmassPositive.le
    have hcombined : |coeff y alpha| ^ 2 * mass ≤
        A * Real.exp (1 / 32 : ℝ) * weighted := by
      calc
        |coeff y alpha| ^ 2 * mass ≤
            (A * (Real.exp (1 / 32 : ℝ) / mass * weighted)) * mass := hthird
        _ = A * Real.exp (1 / 32 : ℝ) * weighted := by
          field_simp [ne_of_gt hmassPositive]
          <;> ring
    have hmassNonnegative : 0 ≤ mass := hmassPositive.le
    have hdominated := mul_le_mul_of_nonneg_right (hcoefficientDominates y) hmassNonnegative
    exact (hdominated.trans hcombined : _)
  let supportCube : Set (Fin s → ℝ) :=
    {z | ∀ j, -(Ct : ℝ) ≤ z j ∧ z j ≤ (Ct : ℝ)}
  have hintervalCover (t : ℝ) (ht : t ∈ Set.Icc (-(Ct : ℝ)) (Ct : ℝ)) :
      ∃ k : Fin N, -(Ct : ℝ) + (k : ℝ) * h ≤ t ∧
        t ≤ -(Ct : ℝ) + (k : ℝ) * h + h := by
    by_cases htop : t = (Ct : ℝ)
    · have hNOne : 1 ≤ N := by omega
      let k : Fin N := ⟨N - 1, Nat.sub_lt hNPositive (by omega)⟩
      refine ⟨k, ?_, ?_⟩
      · subst t
        dsimp [k]
        rw [Nat.cast_sub hNOne]
        norm_num only [Nat.cast_one]
        nlinarith [hNh, hhPositive]
      · subst t
        dsimp [k]
        rw [Nat.cast_sub hNOne]
        norm_num only [Nat.cast_one]
        nlinarith [hNh]
    · have htTop : t < (Ct : ℝ) := lt_of_le_of_ne ht.2 htop
      let r : ℝ := (t + (Ct : ℝ)) / h
      have hrNonnegative : 0 ≤ r := by
        dsimp [r]
        apply div_nonneg
        · linarith [ht.1]
        · exact hhPositive.le
      have hrN : r < (N : ℝ) := by
        apply (div_lt_iff₀ hhPositive).2
        nlinarith [hNh]
      have hkN : ⌊r⌋₊ < N := by
        exact_mod_cast (lt_of_le_of_lt (Nat.floor_le hrNonnegative) hrN)
      let k : Fin N := ⟨⌊r⌋₊, hkN⟩
      have hkLower : ((k : ℕ) : ℝ) * h ≤ t + (Ct : ℝ) := by
        apply (le_div_iff₀ hhPositive).mp
        exact Nat.floor_le hrNonnegative
      have hkUpper : t + (Ct : ℝ) < (((k : ℕ) : ℝ) + 1) * h := by
        apply (div_lt_iff₀ hhPositive).mp
        exact Nat.lt_floor_add_one r
      refine ⟨k, ?_, ?_⟩ <;> dsimp [k] at hkLower hkUpper ⊢ <;> linarith
  have hcellUnion : (⋃ q : Fin s → Fin N, cell q) = supportCube := by
    ext z
    simp only [Set.mem_iUnion, supportCube, Set.mem_setOf_eq]
    constructor
    · rintro ⟨q, hz⟩ j
      exact hcellSubset q j (hz j)
    · intro hz
      choose q hq using fun j => hintervalCover (z j) (hz j)
      refine ⟨q, ?_⟩
      intro j
      exact hq j
  have hcellsAEDisjoint : Pairwise (fun q q' =>
      MeasureTheory.AEDisjoint MeasureTheory.volume (cell q) (cell q')) := by
    intro q q' hqq'
    have hexists : ∃ j, q j ≠ q' j := by
      by_contra hnone
      apply hqq'
      funext j
      by_contra hj
      exact hnone ⟨j, hj⟩
    rcases hexists with ⟨j, hj⟩
    show (MeasureTheory.volume : MeasureTheory.Measure (Fin s → ℝ))
      (cell q ∩ cell q') = 0
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · have hsubset : cell q ∩ cell q' ⊆ {z : Fin s → ℝ | z j = lower q' j} := by
        intro z hz
        have hstepNat : (q j : ℕ) + 1 ≤ (q' j : ℕ) := by omega
        have hstepReal : ((q j : ℕ) : ℝ) + 1 ≤ ((q' j : ℕ) : ℝ) := by
          exact_mod_cast hstepNat
        have hlower : lower q j + h ≤ lower q' j := by
          dsimp [lower]
          nlinarith [mul_le_mul_of_nonneg_right hstepReal hhPositive.le]
        exact le_antisymm ((hz.1 j).2.trans hlower) (hz.2 j).1
      exact MeasureTheory.measure_mono_null hsubset
        (MeasureTheory.Measure.pi_hyperplane
          (fun _ : Fin s => (MeasureTheory.volume : MeasureTheory.Measure ℝ)) j (lower q' j))
    · have hsubset : cell q ∩ cell q' ⊆ {z : Fin s → ℝ | z j = lower q j} := by
        intro z hz
        have hstepNat : (q' j : ℕ) + 1 ≤ (q j : ℕ) := by omega
        have hstepReal : ((q' j : ℕ) : ℝ) + 1 ≤ ((q j : ℕ) : ℝ) := by
          exact_mod_cast hstepNat
        have hlower : lower q' j + h ≤ lower q j := by
          dsimp [lower]
          nlinarith [mul_le_mul_of_nonneg_right hstepReal hhPositive.le]
        exact le_antisymm ((hz.2 j).2.trans hlower) (hz.1 j).1
      exact MeasureTheory.measure_mono_null hsubset
        (MeasureTheory.Measure.pi_hyperplane
          (fun _ : Fin s => (MeasureTheory.volume : MeasureTheory.Measure ℝ)) j (lower q j))
  have hsupportCubeCompact : IsCompact supportCube := by
    have hEq : supportCube = Set.Icc (fun _ => -(Ct : ℝ)) (fun _ => (Ct : ℝ)) := by
      ext z
      simp only [supportCube, Set.mem_setOf_eq, Set.mem_Icc]
      constructor
      · intro hz
        exact ⟨fun j => (hz j).1, fun j => (hz j).2⟩
      · rintro ⟨hz, hz'⟩ j
        exact ⟨hz j, hz' j⟩
    rw [hEq]
    exact isCompact_Icc
  have hcellIntegralSum (F : (Fin s → ℝ) → ℝ) (hF : Continuous F) :
      (∑ q : Fin s → Fin N, ∫ z in cell q, F z ∂MeasureTheory.volume) =
        ∫ z in supportCube, F z ∂MeasureTheory.volume := by
    have hIntegrable : MeasureTheory.IntegrableOn F supportCube MeasureTheory.volume :=
      hF.continuousOn.integrableOn_compact hsupportCubeCompact
    have hUnionIntegrable : MeasureTheory.IntegrableOn F
        (⋃ q : Fin s → Fin N, cell q) MeasureTheory.volume := by
      simpa only [hcellUnion] using hIntegrable
    have hsum := MeasureTheory.integral_iUnion_ae
      (f := F) (μ := (MeasureTheory.volume : MeasureTheory.Measure (Fin s → ℝ)))
      (fun q => (hcellMeasurable q).nullMeasurableSet) hcellsAEDisjoint hUnionIntegrable
    rw [hcellUnion] at hsum
    simpa only [tsum_fintype] using hsum.symm
  have hsupportWeighted
      (y : {j : Fin n // j ∉ support} → ℝ) (hy : y ∈ exteriorCube) :
      (thetaStar factor - theta factor) ^ 2 *
          (∫ z in supportCube, fiberDensity y z ∂MeasureTheory.volume) ≤
        (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d * s) * Real.exp (1 / 32 : ℝ) *
          ∫ z in supportCube, P y z ^ 2 * fiberDensity y z ∂MeasureTheory.volume := by
    calc
      (thetaStar factor - theta factor) ^ 2 *
          (∫ z in supportCube, fiberDensity y z ∂MeasureTheory.volume) =
          ∑ q : Fin s → Fin N,
            (thetaStar factor - theta factor) ^ 2 *
              (∫ z in cell q, fiberDensity y z ∂MeasureTheory.volume) := by
        rw [← hcellIntegralSum (fiberDensity y) (hfiberContinuous y)]
        rw [Finset.mul_sum]
      _ ≤ ∑ q : Fin s → Fin N,
          (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d * s) * Real.exp (1 / 32 : ℝ) *
            ∫ z in cell q, P y z ^ 2 * fiberDensity y z ∂MeasureTheory.volume :=
        Finset.sum_le_sum fun q hq => hcellWeighted q y hy
      _ = (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d * s) * Real.exp (1 / 32 : ℝ) *
          ∫ z in supportCube, P y z ^ 2 * fiberDensity y z ∂MeasureTheory.volume := by
        change (∑ q : Fin s → Fin N,
          ((12 * (d : ℝ) * (N : ℝ)) ^ (2 * d * s) * Real.exp (1 / 32 : ℝ)) *
            ∫ z in cell q, P y z ^ 2 * fiberDensity y z ∂MeasureTheory.volume) = _
        rw [← Finset.mul_sum]
        rw [hcellIntegralSum]
        exact ((hPContinuous y).pow 2).mul (hfiberContinuous y)
  have hexteriorCubeMeasurable : MeasurableSet exteriorCube := by
    have hEq : exteriorCube =
        Set.Icc (fun _ => -(Ct : ℝ)) (fun _ => (Ct : ℝ)) := by
      ext y
      simp only [exteriorCube, Set.mem_setOf_eq, Set.mem_Icc]
      constructor
      · intro hy
        exact ⟨fun j => (abs_le.mp (hy j)).1, fun j => (abs_le.mp (hy j)).2⟩
      · rintro ⟨hy, hy'⟩ j
        exact abs_le.mpr ⟨hy j, hy' j⟩
    rw [hEq]
    exact measurableSet_Icc
  have hexteriorCubeCompact : IsCompact exteriorCube := by
    have hEq : exteriorCube =
        Set.Icc (fun _ => -(Ct : ℝ)) (fun _ => (Ct : ℝ)) := by
      ext y
      simp only [exteriorCube, Set.mem_setOf_eq, Set.mem_Icc]
      constructor
      · intro hy
        exact ⟨fun j => (abs_le.mp (hy j)).1, fun j => (abs_le.mp (hy j)).2⟩
      · rintro ⟨hy, hy'⟩ j
        exact abs_le.mpr ⟨hy j, hy' j⟩
    rw [hEq]
    exact isCompact_Icc
  have hcombinePairContinuous : Continuous
      (fun zy : (Fin s → ℝ) × ({j : Fin n // j ∉ support} → ℝ) =>
        combine zy.1 zy.2) := by
    rw [continuous_pi_iff]
    intro k
    by_cases hk : k ∈ support
    · let j : Fin s := e.symm ⟨k, hk⟩
      have hej : (e j).1 = k := by
        exact congrArg Subtype.val (e.apply_symm_apply ⟨k, hk⟩)
      have hfun : (fun zy : (Fin s → ℝ) × ({j : Fin n // j ∉ support} → ℝ) =>
          combine zy.1 zy.2 k) = fun zy => zy.1 j := by
        funext zy
        rw [← hej, hcombineSupport]
      rw [hfun]
      fun_prop
    · have hfun : (fun zy : (Fin s → ℝ) × ({j : Fin n // j ∉ support} → ℝ) =>
          combine zy.1 zy.2 k) = fun zy => zy.2 ⟨k, hk⟩ := by
        funext zy
        exact hcombineExterior zy.1 zy.2 ⟨k, hk⟩
      rw [hfun]
      fun_prop
  have hdensityJointContinuous : Continuous
      (fun zy : (Fin s → ℝ) × ({j : Fin n // j ∉ support} → ℝ) =>
        fiberDensity zy.2 zy.1) := by
    have henergyContinuous : Continuous
        (fun x => exponential_energy factors thetaStar x) := by
      unfold exponential_energy monomial_value
      fun_prop
    exact (Real.continuous_exp.comp
      (henergyContinuous.comp hcombinePairContinuous)).div_const Z
  have hPJointContinuous : Continuous
      (fun zy : (Fin s → ℝ) × ({j : Fin n // j ∉ support} → ℝ) => P zy.2 zy.1) := by
    have henergyDerivativeContinuous : Continuous
        (fun x => energy_first_partial factors delta i x) := by
      unfold energy_first_partial monomial_first_partial
      fun_prop
    have hfun : (fun zy : (Fin s → ℝ) × ({j : Fin n // j ∉ support} → ℝ) =>
        P zy.2 zy.1) = fun zy => energy_first_partial factors delta i (combine zy.1 zy.2) := by
      funext zy
      exact hpolynomialIdentity zy.1 zy.2
    rw [hfun]
    exact henergyDerivativeContinuous.comp hcombinePairContinuous
  let productCube : Set ((Fin s → ℝ) × ({j : Fin n // j ∉ support} → ℝ)) :=
    supportCube ×ˢ exteriorCube
  have hproductCubeMeasurable : MeasurableSet productCube :=
    hsupportCubeCompact.measurableSet.prod hexteriorCubeMeasurable
  have hproductCubeCompact : IsCompact productCube :=
    hsupportCubeCompact.prod hexteriorCubeCompact
  let jointDensity
      (zy : (Fin s → ℝ) × ({j : Fin n // j ∉ support} → ℝ)) : ℝ :=
    fiberDensity zy.2 zy.1
  let jointWeighted
      (zy : (Fin s → ℝ) × ({j : Fin n // j ∉ support} → ℝ)) : ℝ :=
    P zy.2 zy.1 ^ 2 * fiberDensity zy.2 zy.1
  have hjointDensityContinuous : Continuous jointDensity := by
    exact hdensityJointContinuous
  have hjointWeightedContinuous : Continuous jointWeighted := by
    exact (hPJointContinuous.pow 2).mul hdensityJointContinuous
  have hjointDensityOn : MeasureTheory.IntegrableOn jointDensity productCube
      MeasureTheory.volume :=
    hjointDensityContinuous.continuousOn.integrableOn_compact hproductCubeCompact
  have hjointWeightedOn : MeasureTheory.IntegrableOn jointWeighted productCube
      MeasureTheory.volume :=
    hjointWeightedContinuous.continuousOn.integrableOn_compact hproductCubeCompact
  have hjointDensityIndicator : MeasureTheory.Integrable
      (productCube.indicator jointDensity) MeasureTheory.volume :=
    hjointDensityOn.integrable_indicator hproductCubeMeasurable
  have hjointWeightedIndicator : MeasureTheory.Integrable
      (productCube.indicator jointWeighted) MeasureTheory.volume :=
    hjointWeightedOn.integrable_indicator hproductCubeMeasurable
  let innerMass (y : {j : Fin n // j ∉ support} → ℝ) : ℝ :=
    ∫ z in supportCube, fiberDensity y z ∂MeasureTheory.volume
  let innerWeighted (y : {j : Fin n // j ∉ support} → ℝ) : ℝ :=
    ∫ z in supportCube, P y z ^ 2 * fiberDensity y z ∂MeasureTheory.volume
  have hdensitySlice (y : {j : Fin n // j ∉ support} → ℝ) :
      (∫ z, productCube.indicator jointDensity (z, y) ∂MeasureTheory.volume) =
        exteriorCube.indicator innerMass y := by
    by_cases hy : y ∈ exteriorCube
    · rw [Set.indicator_of_mem hy]
      change (∫ z, productCube.indicator jointDensity (z, y) ∂MeasureTheory.volume) =
        ∫ z in supportCube, fiberDensity y z ∂MeasureTheory.volume
      rw [← MeasureTheory.integral_indicator hsupportCubeCompact.measurableSet]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ supportCube
      · simp [productCube, jointDensity, innerMass, hz, hy]
      · simp [productCube, jointDensity, innerMass, hz, hy]
    · simp only [Set.indicator, hy, ↓reduceIte]
      apply MeasureTheory.integral_eq_zero_of_ae
      filter_upwards with z
      simp [productCube, jointDensity, hy]
  have hweightedSlice (y : {j : Fin n // j ∉ support} → ℝ) :
      (∫ z, productCube.indicator jointWeighted (z, y) ∂MeasureTheory.volume) =
        exteriorCube.indicator innerWeighted y := by
    by_cases hy : y ∈ exteriorCube
    · rw [Set.indicator_of_mem hy]
      change (∫ z, productCube.indicator jointWeighted (z, y) ∂MeasureTheory.volume) =
        ∫ z in supportCube, P y z ^ 2 * fiberDensity y z ∂MeasureTheory.volume
      rw [← MeasureTheory.integral_indicator hsupportCubeCompact.measurableSet]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ supportCube
      · simp [productCube, jointWeighted, innerWeighted, hz, hy]
      · simp [productCube, jointWeighted, innerWeighted, hz, hy]
    · simp only [Set.indicator, hy, ↓reduceIte]
      apply MeasureTheory.integral_eq_zero_of_ae
      filter_upwards with z
      simp [productCube, jointWeighted, hy]
  have hinnerMassIntegrable : MeasureTheory.IntegrableOn innerMass exteriorCube
      MeasureTheory.volume := by
    have hpartial := hjointDensityIndicator.integral_prod_right
    have hfun : (fun y => ∫ z, productCube.indicator jointDensity (z, y)
        ∂MeasureTheory.volume) = exteriorCube.indicator innerMass := by
      funext y
      exact hdensitySlice y
    rw [hfun] at hpartial
    exact (MeasureTheory.integrable_indicator_iff hexteriorCubeMeasurable).1 hpartial
  have hinnerWeightedIntegrable : MeasureTheory.IntegrableOn innerWeighted exteriorCube
      MeasureTheory.volume := by
    have hpartial := hjointWeightedIndicator.integral_prod_right
    have hfun : (fun y => ∫ z, productCube.indicator jointWeighted (z, y)
        ∂MeasureTheory.volume) = exteriorCube.indicator innerWeighted := by
      funext y
      exact hweightedSlice y
    rw [hfun] at hpartial
    exact (MeasureTheory.integrable_indicator_iff hexteriorCubeMeasurable).1 hpartial
  have houterWeighted :
      (thetaStar factor - theta factor) ^ 2 *
          (∫ y in exteriorCube, innerMass y ∂MeasureTheory.volume) ≤
        ((12 * (d : ℝ) * (N : ℝ)) ^ (2 * d * s) * Real.exp (1 / 32 : ℝ)) *
          ∫ y in exteriorCube, innerWeighted y ∂MeasureTheory.volume := by
    have hmono := MeasureTheory.setIntegral_mono_on
      (hinnerMassIntegrable.const_mul ((thetaStar factor - theta factor) ^ 2))
      (hinnerWeightedIntegrable.const_mul
        ((12 * (d : ℝ) * (N : ℝ)) ^ (2 * d * s) * Real.exp (1 / 32 : ℝ)))
      hexteriorCubeMeasurable
      (fun y hy => by
        simpa [innerMass, innerWeighted, mul_assoc] using hsupportWeighted y hy)
    rw [integral_const_mul_of_integrable hinnerMassIntegrable,
      integral_const_mul_of_integrable hinnerWeightedIntegrable] at hmono
    exact hmono
  have hmassIterated :
      (∫ y in exteriorCube, innerMass y ∂MeasureTheory.volume) =
        ∫ zy in productCube, jointDensity zy ∂MeasureTheory.volume := by
    calc
      (∫ y in exteriorCube, innerMass y ∂MeasureTheory.volume) =
          ∫ y, exteriorCube.indicator innerMass y ∂MeasureTheory.volume := by
        symm
        exact MeasureTheory.integral_indicator hexteriorCubeMeasurable
      _ = ∫ y, ∫ z, productCube.indicator jointDensity (z, y)
          ∂MeasureTheory.volume ∂MeasureTheory.volume := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with y
        exact (hdensitySlice y).symm
      _ = ∫ zy, productCube.indicator jointDensity zy ∂MeasureTheory.volume := by
        symm
        exact MeasureTheory.integral_prod_symm _ hjointDensityIndicator
      _ = ∫ zy in productCube, jointDensity zy ∂MeasureTheory.volume :=
        MeasureTheory.integral_indicator hproductCubeMeasurable
  have hweightedIterated :
      (∫ y in exteriorCube, innerWeighted y ∂MeasureTheory.volume) =
        ∫ zy in productCube, jointWeighted zy ∂MeasureTheory.volume := by
    calc
      (∫ y in exteriorCube, innerWeighted y ∂MeasureTheory.volume) =
          ∫ y, exteriorCube.indicator innerWeighted y ∂MeasureTheory.volume := by
        symm
        exact MeasureTheory.integral_indicator hexteriorCubeMeasurable
      _ = ∫ y, ∫ z, productCube.indicator jointWeighted (z, y)
          ∂MeasureTheory.volume ∂MeasureTheory.volume := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with y
        exact (hweightedSlice y).symm
      _ = ∫ zy, productCube.indicator jointWeighted zy ∂MeasureTheory.volume := by
        symm
        exact MeasureTheory.integral_prod_symm _ hjointWeightedIndicator
      _ = ∫ zy in productCube, jointWeighted zy ∂MeasureTheory.volume :=
        MeasureTheory.integral_indicator hproductCubeMeasurable
  have hcombineCubeIff (z : Fin s → ℝ)
      (y : {j : Fin n // j ∉ support} → ℝ) :
      combine z y ∈ cube ↔ z ∈ supportCube ∧ y ∈ exteriorCube := by
    constructor
    · intro hzy
      constructor
      · intro j
        have hbound := abs_le.mp (hcoordinateBound (combine z y) hzy (e j).1)
        rw [hcombineSupport] at hbound
        exact hbound
      · intro j
        have hbound := hcoordinateBound (combine z y) hzy j.1
        rw [hcombineExterior] at hbound
        exact hbound
    · rintro ⟨hz, hy⟩
      change ‖combine z y‖ ≤ (Ct : ℝ)
      apply (pi_norm_le_iff_of_nonneg hCtPositive.le).2
      intro k
      rw [Real.norm_eq_abs]
      by_cases hk : k ∈ support
      · let j : Fin s := e.symm ⟨k, hk⟩
        have hej : (e j).1 = k := by
          exact congrArg Subtype.val (e.apply_symm_apply ⟨k, hk⟩)
        rw [← hej, hcombineSupport]
        exact abs_le.mpr (hz j)
      · have hout := hcombineExterior z y ⟨k, hk⟩
        rw [hout]
        exact hy ⟨k, hk⟩
  let indexEquiv : Fin s ⊕ {j : Fin n // j ∉ support} ≃ Fin n :=
    (Equiv.sumCongr e (Equiv.refl _)).trans
      (Equiv.sumCompl (fun j : Fin n => j ∈ support))
  let productToSum :
      ((Fin s → ℝ) × ({j : Fin n // j ∉ support} → ℝ)) ≃ᵐ
        (Fin s ⊕ {j : Fin n // j ∉ support} → ℝ) :=
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Fin s ⊕ {j : Fin n // j ∉ support} => ℝ)).symm
  let sumToFull : (Fin s ⊕ {j : Fin n // j ∉ support} → ℝ) ≃ᵐ
      (Fin n → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) indexEquiv
  have hcanonicalCombine
      (zy : (Fin s → ℝ) × ({j : Fin n // j ∉ support} → ℝ)) :
      sumToFull (productToSum zy) = combine zy.1 zy.2 := by
    funext k
    by_cases hk : k ∈ support
    · let j : Fin s := e.symm ⟨k, hk⟩
      have hej : (e j).1 = k := by
        exact congrArg Subtype.val (e.apply_symm_apply ⟨k, hk⟩)
      have hindex : indexEquiv (Sum.inl j) = k := by
        simp [indexEquiv, hej, Equiv.sumCompl]
      rw [← hindex]
      rw [MeasurableEquiv.piCongrLeft_apply_apply]
      change zy.1 j = combine zy.1 zy.2 (e j).1
      rw [hcombineSupport]
    · let k' : {j : Fin n // j ∉ support} := ⟨k, hk⟩
      have hindex : indexEquiv (Sum.inr k') = k := by
        simp [indexEquiv, k', Equiv.sumCompl]
      rw [← hindex]
      rw [MeasurableEquiv.piCongrLeft_apply_apply]
      change zy.2 k' = combine zy.1 zy.2 k'.1
      rw [hcombineExterior]
  have hproductToSumPreserving : MeasureTheory.MeasurePreserving productToSum
      MeasureTheory.volume MeasureTheory.volume := by
    exact MeasureTheory.volume_measurePreserving_sumPiEquivProdPi_symm
      (fun _ : Fin s ⊕ {j : Fin n // j ∉ support} => ℝ)
  have hsumToFullPreserving : MeasureTheory.MeasurePreserving sumToFull
      MeasureTheory.volume MeasureTheory.volume := by
    exact MeasureTheory.volume_measurePreserving_piCongrLeft
      (fun _ : Fin n => ℝ) indexEquiv
  have hcombinePreserving : MeasureTheory.MeasurePreserving
      (fun zy : (Fin s → ℝ) × ({j : Fin n // j ∉ support} → ℝ) =>
        combine zy.1 zy.2) MeasureTheory.volume MeasureTheory.volume := by
    have hcomp := hsumToFullPreserving.comp hproductToSumPreserving
    convert hcomp using 1
    funext zy
    simpa only [Function.comp_apply] using (hcanonicalCombine zy).symm
  have hproductDensityCube :
      (∫ zy in productCube, jointDensity zy ∂MeasureTheory.volume) =
        ∫ x in cube, densityReal x ∂MeasureTheory.volume := by
    calc
      (∫ zy in productCube, jointDensity zy ∂MeasureTheory.volume) =
          ∫ zy, productCube.indicator jointDensity zy ∂MeasureTheory.volume := by
        symm
        exact MeasureTheory.integral_indicator hproductCubeMeasurable
      _ = ∫ (zy : (Fin s → ℝ) × ({j : Fin n // j ∉ support} → ℝ)),
          cube.indicator densityReal (combine zy.1 zy.2)
          ∂MeasureTheory.volume := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with zy
        by_cases hzy : combine zy.1 zy.2 ∈ cube
        · have hprod : zy ∈ productCube := by
            exact (hcombineCubeIff zy.1 zy.2).mp hzy
          simp [hzy, hprod, jointDensity, fiberDensity]
        · have hprod : zy ∉ productCube := by
            intro hp'
            exact hzy ((hcombineCubeIff zy.1 zy.2).mpr hp')
          simp [hzy, hprod]
      _ = ∫ x, cube.indicator densityReal x ∂MeasureTheory.volume := by
        generalize cube.indicator densityReal = g
        calc
          (∫ (zy : (Fin s → ℝ) × ({j : Fin n // j ∉ support} → ℝ)),
              g (combine zy.1 zy.2) ∂MeasureTheory.volume) =
              ∫ zy, g (sumToFull (productToSum zy)) ∂MeasureTheory.volume := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with zy
            exact congrArg g (hcanonicalCombine zy).symm
          _ = ∫ q, g (sumToFull q) ∂MeasureTheory.volume :=
            hproductToSumPreserving.integral_comp' (fun q => g (sumToFull q))
          _ = ∫ x, g x ∂MeasureTheory.volume :=
            hsumToFullPreserving.integral_comp' g
      _ = ∫ x in cube, densityReal x ∂MeasureTheory.volume :=
        MeasureTheory.integral_indicator hcubeMeasurable
  let fullWeighted (x : Fin n → ℝ) : ℝ :=
    energy_first_partial factors delta i x ^ 2 * densityReal x
  have hproductWeightedCube :
      (∫ zy in productCube, jointWeighted zy ∂MeasureTheory.volume) =
        ∫ x in cube, fullWeighted x ∂MeasureTheory.volume := by
    calc
      (∫ zy in productCube, jointWeighted zy ∂MeasureTheory.volume) =
          ∫ zy, productCube.indicator jointWeighted zy ∂MeasureTheory.volume := by
        symm
        exact MeasureTheory.integral_indicator hproductCubeMeasurable
      _ = ∫ (zy : (Fin s → ℝ) × ({j : Fin n // j ∉ support} → ℝ)),
          cube.indicator fullWeighted (combine zy.1 zy.2)
          ∂MeasureTheory.volume := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with zy
        by_cases hzy : combine zy.1 zy.2 ∈ cube
        · have hprod : zy ∈ productCube :=
            (hcombineCubeIff zy.1 zy.2).mp hzy
          rw [Set.indicator_of_mem hprod, Set.indicator_of_mem hzy]
          simp only [jointWeighted, fullWeighted, P, fiberDensity]
          rw [hpolynomialIdentity]
        · have hprod : zy ∉ productCube := by
            intro hp'
            exact hzy ((hcombineCubeIff zy.1 zy.2).mpr hp')
          simp [hzy, hprod]
      _ = ∫ x, cube.indicator fullWeighted x ∂MeasureTheory.volume := by
        generalize cube.indicator fullWeighted = g
        calc
          (∫ (zy : (Fin s → ℝ) × ({j : Fin n // j ∉ support} → ℝ)),
              g (combine zy.1 zy.2) ∂MeasureTheory.volume) =
              ∫ zy, g (sumToFull (productToSum zy)) ∂MeasureTheory.volume := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with zy
            exact congrArg g (hcanonicalCombine zy).symm
          _ = ∫ q, g (sumToFull q) ∂MeasureTheory.volume :=
            hproductToSumPreserving.integral_comp' (fun q => g (sumToFull q))
          _ = ∫ x, g x ∂MeasureTheory.volume :=
            hsumToFullPreserving.integral_comp' g
      _ = ∫ x in cube, fullWeighted x ∂MeasureTheory.volume :=
        MeasureTheory.integral_indicator hcubeMeasurable
  let density : (Fin n → ℝ) → ENNReal := fun x => ENNReal.ofReal (densityReal x)
  have hdensityMeasurable : Measurable density := by
    unfold density densityReal exponential_energy monomial_value
    fun_prop
  have hdensityLtTop : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)),
      density x < ⊤ := by
    filter_upwards with x
    simp [density]
  have hdensityToReal (x : Fin n → ℝ) : (density x).toReal = densityReal x := by
    simp [density, densityReal, div_nonneg (Real.exp_pos _).le hZ.le]
  have hpDensity :
      p = (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)).withDensity density := by
    simpa only [density, densityReal] using hp
  have hcubeDensityMass :
      (∫ x in cube, densityReal x ∂MeasureTheory.volume) = p.real cube := by
    calc
      (∫ x in cube, densityReal x ∂MeasureTheory.volume) =
          ∫ x in cube, (density x).toReal • (1 : ℝ) ∂MeasureTheory.volume := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        simp [hdensityToReal]
      _ = ∫ _x in cube, (1 : ℝ) ∂((MeasureTheory.volume :
          MeasureTheory.Measure (Fin n → ℝ)).withDensity density) := by
        symm
        exact setIntegral_withDensity_eq_setIntegral_toReal_smul
          hdensityMeasurable (Filter.Eventually.of_forall fun x => by simp [density])
          (fun _ => (1 : ℝ)) hcubeMeasurable
      _ = ∫ _x in cube, (1 : ℝ) ∂p := by rw [← hpDensity]
      _ = p.real cube := MeasureTheory.setIntegral_one_eq_measureReal
  have hboxWeighted :
      (thetaStar factor - theta factor) ^ 2 * p.real cube ≤
        (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d * s) * Real.exp (1 / 32 : ℝ) *
          ∫ x in cube, fullWeighted x ∂MeasureTheory.volume := by
    calc
      (thetaStar factor - theta factor) ^ 2 * p.real cube =
          (thetaStar factor - theta factor) ^ 2 *
            ∫ y in exteriorCube, innerMass y ∂MeasureTheory.volume := by
        rw [hmassIterated, hproductDensityCube, hcubeDensityMass]
      _ ≤ (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d * s) * Real.exp (1 / 32 : ℝ) *
          ∫ y in exteriorCube, innerWeighted y ∂MeasureTheory.volume := houterWeighted
      _ = (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d * s) * Real.exp (1 / 32 : ℝ) *
          ∫ x in cube, fullWeighted x ∂MeasureTheory.volume := by
        rw [hweightedIterated, hproductWeightedCube]
  have hcubeWeightedIntegral :
      (∫ x in cube, fullWeighted x ∂MeasureTheory.volume) =
        ∫ x in cube, energy_first_partial factors delta i x ^ 2 ∂p := by
    calc
      (∫ x in cube, fullWeighted x ∂MeasureTheory.volume) =
          ∫ x in cube, (density x).toReal •
            energy_first_partial factors delta i x ^ 2 ∂MeasureTheory.volume := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        simp only [fullWeighted, hdensityToReal, smul_eq_mul, mul_comm]
      _ = ∫ x in cube, energy_first_partial factors delta i x ^ 2
          ∂((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)).withDensity density) := by
        symm
        exact setIntegral_withDensity_eq_setIntegral_toReal_smul
          hdensityMeasurable (Filter.Eventually.of_forall fun x => by simp [density])
          (fun x => energy_first_partial factors delta i x ^ 2) hcubeMeasurable
      _ = ∫ x in cube, energy_first_partial factors delta i x ^ 2 ∂p := by
        rw [← hpDensity]
  have hmonomialNorm (a : polynomial_factor n) (x : Fin n → ℝ) :
      ‖monomial_value a x‖ ≤ max 1 ‖x‖ ^ (∑ j, a j) := by
    calc
      ‖monomial_value a x‖ ≤ ∏ j, ‖x j ^ a j‖ := by
        exact Finset.norm_prod_le Finset.univ _
      _ ≤ ∏ j, (max 1 ‖x‖) ^ a j := by
        apply Finset.prod_le_prod
        · intro j hj
          positivity
        · intro j hj
          rw [norm_pow]
          gcongr
          exact le_max_of_le_right (norm_le_pi_norm x j)
      _ = max 1 ‖x‖ ^ (∑ j, a j) := by
        exact Finset.prod_pow_eq_pow_sum Finset.univ a _
  have hmaxPow (r : ℝ) (hr : 0 ≤ r) (m : ℕ) :
      (max 1 r) ^ m ≤ 1 + r ^ (m + 1) := by
    rcases le_total r 1 with hle | hle
    · rw [max_eq_left hle, one_pow]
      exact le_add_of_nonneg_right (pow_nonneg hr _)
    · rw [max_eq_right hle]
      have hp : r ^ m ≤ r ^ (m + 1) :=
        pow_le_pow_right₀ hle (Nat.le_succ m)
      linarith
  have hmoment (m : ℕ) :
      MeasureTheory.Integrable (fun x : Fin n → ℝ => 1 + ‖x‖ ^ (m + 1)) p := by
    exact (MeasureTheory.integrable_const (1 : ℝ)).add
      (tail_decay_integrable_norm_pow d tailRate Ct (m + 1) p htail (by omega))
  have hmonomialIntegrable (a : polynomial_factor n) :
      MeasureTheory.Integrable (monomial_value a) p := by
    refine (hmoment (∑ j, a j)).mono' ?_ ?_
    · have hcontinuous : Continuous (monomial_value a) := by
        unfold monomial_value
        fun_prop
      exact hcontinuous.aestronglyMeasurable
    · filter_upwards with x
      exact (hmonomialNorm a x).trans
        (hmaxPow ‖x‖ (norm_nonneg x) (∑ j, a j))
  have hmonomialMulIntegrable (a₁ a₂ : polynomial_factor n) :
      MeasureTheory.Integrable
        (fun x => monomial_value a₁ x * monomial_value a₂ x) p := by
    convert hmonomialIntegrable (fun j => a₁ j + a₂ j) using 1
    funext x
    simp only [monomial_value, pow_add, Finset.prod_mul_distrib]
  have henergyMulIntegrable :
      MeasureTheory.Integrable (fun x =>
        energy_first_partial factors delta i x *
          energy_first_partial factors delta i x) p := by
    simp_rw [energy_first_partial, Finset.sum_mul, Finset.mul_sum]
    refine MeasureTheory.integrable_finsetSum factors ?_
    intro a₁ ha₁
    refine MeasureTheory.integrable_finsetSum factors ?_
    intro a₂ ha₂
    rw [show (fun x =>
        delta a₁ * monomial_first_partial a₁ i x *
          (delta a₂ * monomial_first_partial a₂ i x)) =
        fun x =>
          (delta a₁ * (a₁ i : ℝ) * (delta a₂ * (a₂ i : ℝ))) *
            (monomial_value (derivExponent a₁) x *
              monomial_value (derivExponent a₂) x) by
      funext x
      rw [hfirstAsMonomial, hfirstAsMonomial]
      ring]
    exact (hmonomialMulIntegrable (derivExponent a₁) (derivExponent a₂)).const_mul _
  have henergySquareIntegrable :
      MeasureTheory.Integrable
        (fun x => energy_first_partial factors delta i x ^ 2) p := by
    simpa only [pow_two] using henergyMulIntegrable
  have henergySquareNonnegative :
      0 ≤ ∫ x, energy_first_partial factors delta i x ^ 2 ∂p := by
    exact MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  have hrestrictedLe :
      (∫ x in cube, energy_first_partial factors delta i x ^ 2 ∂p) ≤
        ∫ x, energy_first_partial factors delta i x ^ 2 ∂p := by
    have hnonnegative :
        0 ≤ᵐ[p.restrict Set.univ]
          (fun x => energy_first_partial factors delta i x ^ 2) := by
      filter_upwards with x
      exact sq_nonneg _
    have hsubset : cube ≤ᵐ[p] Set.univ := by
      filter_upwards with x
      exact fun hx => Set.mem_univ x
    simpa only [MeasureTheory.setIntegral_univ] using
      (MeasureTheory.setIntegral_mono_set
        (s := cube) (t := Set.univ) henergySquareIntegrable.integrableOn
        hnonnegative hsubset)
  have hdRealOne : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast (show 1 ≤ d by omega)
  have hdSquareOne : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by
    exact one_le_pow₀ hdRealOne
  have hlargeBaseOne :
      (1 : ℝ) ≤ 792 * (d : ℝ) ^ 2 * u := by
    calc
      (1 : ℝ) ≤ 792 * 1 := by norm_num
      _ ≤ 792 * (d : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hdSquareOne (by norm_num)
      _ ≤ 792 * (d : ℝ) ^ 2 * u :=
        le_mul_of_one_le_right (by positivity) huOne
  have hcellBaseNonnegative :
      0 ≤ 12 * (d : ℝ) * (N : ℝ) := by positivity
  have hcellBaseLe :
      12 * (d : ℝ) * (N : ℝ) ≤ 792 * (d : ℝ) ^ 2 * u := by
    calc
      12 * (d : ℝ) * (N : ℝ) ≤ 12 * (d : ℝ) * (66 * (d : ℝ) * u) := by
        gcongr
      _ = 792 * (d : ℝ) ^ 2 * u := by ring
  have hexponentLe :
      2 * d * s ≤ 2 * d * interaction_order factors := by
    exact Nat.mul_le_mul_left (2 * d) hsOrder
  have hpowerLe :
      (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d * s) ≤
        (792 * (d : ℝ) ^ 2 * u) ^ (2 * d * interaction_order factors) := by
    calc
      (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d * s) ≤
          (792 * (d : ℝ) ^ 2 * u) ^ (2 * d * s) :=
        pow_le_pow_left₀ hcellBaseNonnegative hcellBaseLe _
      _ ≤ (792 * (d : ℝ) ^ 2 * u) ^
          (2 * d * interaction_order factors) :=
        pow_le_pow_right₀ hlargeBaseOne hexponentLe
  have hconstantLe :
      (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d * s) * Real.exp (1 / 32 : ℝ) ≤
        Real.exp (1 / 32 : ℝ) *
          (792 * (d : ℝ) ^ 2 * u) ^ (2 * d * interaction_order factors) := by
    calc
      (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d * s) * Real.exp (1 / 32 : ℝ) =
          Real.exp (1 / 32 : ℝ) *
            (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d * s) := by ring
      _ ≤ Real.exp (1 / 32 : ℝ) *
          (792 * (d : ℝ) ^ 2 * u) ^ (2 * d * interaction_order factors) := by
        gcongr
  have hhalfBound :
      (thetaStar factor - theta factor) ^ 2 * (1 / 2 : ℝ) ≤
        Real.exp (1 / 32 : ℝ) *
          (792 * (d : ℝ) ^ 2 * u) ^ (2 * d * interaction_order factors) *
            ∫ x, energy_first_partial factors delta i x ^ 2 ∂p := by
    calc
      (thetaStar factor - theta factor) ^ 2 * (1 / 2 : ℝ) ≤
          (thetaStar factor - theta factor) ^ 2 * p.real cube := by
        exact mul_le_mul_of_nonneg_left hcubeMass (sq_nonneg _)
      _ ≤ (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d * s) * Real.exp (1 / 32 : ℝ) *
          ∫ x in cube, energy_first_partial factors delta i x ^ 2 ∂p := by
        simpa only [hcubeWeightedIntegral] using hboxWeighted
      _ ≤ (12 * (d : ℝ) * (N : ℝ)) ^ (2 * d * s) * Real.exp (1 / 32 : ℝ) *
          ∫ x, energy_first_partial factors delta i x ^ 2 ∂p := by
        exact mul_le_mul_of_nonneg_left hrestrictedLe
          (mul_nonneg (pow_nonneg hcellBaseNonnegative _) (Real.exp_pos _).le)
      _ ≤ Real.exp (1 / 32 : ℝ) *
          (792 * (d : ℝ) ^ 2 * u) ^ (2 * d * interaction_order factors) *
            ∫ x, energy_first_partial factors delta i x ^ 2 ∂p := by
        exact mul_le_mul_of_nonneg_right hconstantLe henergySquareNonnegative
  have hfinal :
      (thetaStar factor - theta factor) ^ 2 ≤
        (4 * Real.exp (1 / 32 : ℝ) *
          (792 * (d : ℝ) ^ 2 * u) ^ (2 * d * interaction_order factors)) *
            ((1 / 2 : ℝ) *
              ∫ x, energy_first_partial factors delta i x ^ 2 ∂p) := by
    calc
      (thetaStar factor - theta factor) ^ 2 =
          2 * ((thetaStar factor - theta factor) ^ 2 * (1 / 2 : ℝ)) := by ring
      _ ≤ 2 * (Real.exp (1 / 32 : ℝ) *
          (792 * (d : ℝ) ^ 2 * u) ^ (2 * d * interaction_order factors) *
            ∫ x, energy_first_partial factors delta i x ^ 2 ∂p) := by gcongr
      _ = (4 * Real.exp (1 / 32 : ℝ) *
          (792 * (d : ℝ) ^ 2 * u) ^ (2 * d * interaction_order factors)) *
            ((1 / 2 : ℝ) *
              ∫ x, energy_first_partial factors delta i x ^ 2 ∂p) := by ring
  simpa only [u, delta] using hfinal

@[blueprint "lem:support-box-constant-envelope"
  (statement := /-- There are absolute constants $A_{0,\mathrm{box}}>1$ and
  $C_{\mathrm{box}}\in\mathbb N_{>0}$ such that, for every $d,w\in\mathbb N$ and every
  $u\geq1+2^{-10}$, the explicit support-box constant
  \[
    A(d,w,u)=4e^{1/32}(792d^2u)^{2dw}
  \]
  satisfies
  \[
    1\leq A(d,w,u)\leq
      \max\{A_{0,\mathrm{box}},u^{C_{\mathrm{box}}d^2w}\}.
  \] -/)
  (proof := /-- Take $A_{0,\mathrm{box}}=8$ and $C_{\mathrm{box}}=2^{21}$. The exponential
  estimate $e^x<(1-x)^{-1}$ for $0<x<1$ gives $e^{1/32}<32/31<2$. Moreover, Bernoulli's
  inequality and $u\geq1+2^{-10}$ imply
  \[
    u^n\geq (1+2^{-10})^n\geq1+n2^{-10}
    \qquad(n\in\mathbb N).
  \]
  In particular, $u^{7168}\geq8$, $u^{809984}\geq792$, and
  $u^{1024d}\geq1+d\geq d$. Hence
  \[
    d^2\leq u^{2048d},\qquad
    792d^2u\leq u^{809985+2048d}.
  \]
  If $d,w\geq1$, multiplication and exponentiation preserve these inequalities, and therefore
  \[
    4e^{1/32}(792d^2u)^{2dw}
      \leq u^{7168+(809985+2048d)(2dw)}.
  \]
  Since $dw\leq d^2w$ and $1\leq d^2w$, expansion of the exponent gives
  \[
    7168+(809985+2048d)(2dw)
      \leq1631234d^2w<2^{21}d^2w.
  \]
  This proves the upper bound in the positive case. If $d=0$ or $w=0$, the powered factor is
  $1$, so the upper bound follows from $4e^{1/32}<8=A_{0,\mathrm{box}}$. Finally, in the
  positive case the base $792d^2u$ is at least $1$, while in either degenerate case its natural
  exponent is zero; together with $e^{1/32}\geq1$, this proves the lower bound in all cases. -/)
  (title := /-- Absolute polynomial envelope for the support-box constant -/)
  (latexEnv := "lemma")]
lemma support_box_constant_envelope :
    ∃ A0 : ℝ, 1 < A0 ∧
      ∃ Cbox : ℕ, 0 < Cbox ∧
        ∀ (d w : ℕ) (u : ℝ), 1 + (1 / 1024 : ℝ) ≤ u →
          1 ≤ 4 * Real.exp (1 / 32 : ℝ) *
              (792 * (d : ℝ) ^ 2 * u) ^ (2 * d * w) ∧
          4 * Real.exp (1 / 32 : ℝ) *
              (792 * (d : ℝ) ^ 2 * u) ^ (2 * d * w) ≤
            max A0 (u ^ (Cbox * d ^ 2 * w)) := by
  refine ⟨8, by norm_num, 2 ^ 21, by norm_num, ?_⟩
  intro d w u hu
  have hu0 : 0 ≤ u := by
    norm_num at hu ⊢
    linarith
  have hu1 : 1 ≤ u := by
    norm_num at hu ⊢
    linarith
  have hexp : Real.exp (1 / 32 : ℝ) < 2 := by
    calc
      Real.exp (1 / 32 : ℝ) < 1 / (1 - (1 / 32 : ℝ)) :=
        Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
      _ < 2 := by norm_num
  have hexpLower : 1 ≤ Real.exp (1 / 32 : ℝ) :=
    Real.one_le_exp (by norm_num)
  have hbern (n : ℕ) : 1 + (n : ℝ) / 1024 ≤ u ^ n := by
    calc
      1 + (n : ℝ) / 1024 = 1 + (n : ℝ) * (1 / 1024 : ℝ) := by ring
      _ ≤ (1 + (1 / 1024 : ℝ)) ^ n :=
        one_add_mul_le_pow (by norm_num) n
      _ ≤ u ^ n := by gcongr
  constructor
  · by_cases hd : d = 0
    · simp [hd]
      nlinarith
    · by_cases hw : w = 0
      · simp [hw]
        nlinarith
      · have hd1 : 1 ≤ (d : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hd)
        have hbase : 1 ≤ 792 * (d : ℝ) ^ 2 * u := by
          nlinarith [sq_nonneg ((d : ℝ) - 1)]
        have hp : 1 ≤ (792 * (d : ℝ) ^ 2 * u) ^ (2 * d * w) :=
          one_le_pow₀ hbase
        have hprod : 1 ≤ Real.exp (1 / 32 : ℝ) *
            (792 * (d : ℝ) ^ 2 * u) ^ (2 * d * w) :=
          by simpa using mul_le_mul hexpLower hp (by norm_num) (Real.exp_pos _).le
        nlinarith
  · by_cases hd : d = 0
    · simp [hd]
      nlinarith [le_max_left (8 : ℝ) 1]
    · by_cases hw : w = 0
      · simp [hw]
        nlinarith [le_max_left (8 : ℝ) 1]
      · have hdNat : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
        have hwNat : 1 ≤ w := Nat.one_le_iff_ne_zero.mpr hw
        have h8 : (8 : ℝ) ≤ u ^ 7168 := by
          have h := hbern 7168
          norm_num at h
          exact h
        have h792 : (792 : ℝ) ≤ u ^ 809984 := by
          have h := hbern 809984
          norm_num at h
          exact h
        have hdPow : (d : ℝ) ≤ u ^ (1024 * d) := by
          have h := hbern (1024 * d)
          norm_num [Nat.cast_mul] at h
          have hd_le : (d : ℝ) ≤ 1 + d := by linarith
          exact hd_le.trans (by simpa [Nat.mul_comm] using h)
        have hdSq : (d : ℝ) ^ 2 ≤ u ^ (2048 * d) := by
          calc
            (d : ℝ) ^ 2 ≤ (u ^ (1024 * d)) ^ 2 := by gcongr
            _ = u ^ (2048 * d) := by
              rw [← pow_mul]
              congr 1
              omega
        have hbase : 792 * (d : ℝ) ^ 2 * u ≤ u ^ (809985 + 2048 * d) := by
          calc
            792 * (d : ℝ) ^ 2 * u ≤ u ^ 809984 * u ^ (2048 * d) * u := by
              gcongr
            _ = u ^ (809984 + 2048 * d) * u := by
              exact congrArg (fun z => z * u) (pow_add u 809984 (2048 * d)).symm
            _ = u ^ ((809984 + 2048 * d) + 1) := by
              simpa only [pow_one] using (pow_add u (809984 + 2048 * d) 1).symm
            _ = u ^ (809985 + 2048 * d) := by
              congr 1
              omega
        have hmain :
            (792 * (d : ℝ) ^ 2 * u) ^ (2 * d * w) ≤
              u ^ ((809985 + 2048 * d) * (2 * d * w)) := by
          calc
            (792 * (d : ℝ) ^ 2 * u) ^ (2 * d * w) ≤
                (u ^ (809985 + 2048 * d)) ^ (2 * d * w) := by gcongr
            _ = u ^ ((809985 + 2048 * d) * (2 * d * w)) := by
              rw [← pow_mul]
        have hfactor : 4 * Real.exp (1 / 32 : ℝ) ≤ u ^ 7168 := by
          nlinarith
        have hexponents :
            7168 + (809985 + 2048 * d) * (2 * d * w) ≤
              (2 ^ 21) * d ^ 2 * w := by
          have hd_le_sq : d ≤ d ^ 2 := by nlinarith
          have hdw_le : d * w ≤ d ^ 2 * w := Nat.mul_le_mul_right w hd_le_sq
          have hone_le : 1 ≤ d ^ 2 * w :=
            Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hd) hw)
          nlinarith
        calc
          4 * Real.exp (1 / 32 : ℝ) *
                (792 * (d : ℝ) ^ 2 * u) ^ (2 * d * w) ≤
              u ^ 7168 * u ^ ((809985 + 2048 * d) * (2 * d * w)) := by
            gcongr
          _ = u ^ (7168 + (809985 + 2048 * d) * (2 * d * w)) := by
            rw [pow_add]
          _ ≤ u ^ ((2 ^ 21) * d ^ 2 * w) :=
            pow_le_pow_right₀ hu1 hexponents
          _ ≤ max 8 (u ^ ((2 ^ 21) * d ^ 2 * w)) := le_max_right _ _

@[blueprint "lem:support-box-density-comparison"
  (statement := /-- There are an absolute real constant $A_{0,\mathrm{box}}>1$ and a positive
  integer $C_{\mathrm{box}}$ with the following property. Let $n,d\in\mathbb N$, let
  $\mathcal K\subseteq\mathbb N^n$ be a finite family of factors of total degree at most $d$,
  let $\theta^*:\mathbb N^n\to\mathbb R$, and fix $i\in[n]$. Let $B,k\in\mathbb R$, let
  $C_t\in\mathbb N$, and let $p$ be a probability measure on $\mathbb R^n$. Assume that $B>0$,
  that $\theta^*$ is feasible at radius $B$, that $p$ is the unit-base polynomial exponential
  family generated by $(\mathcal K,\theta^*)$, that $p$ satisfies the degree-$d$ tail-decay
  condition with rate $k$ and threshold $C_t$, and that
  $dBC_t^d\geq1+2^{-10}$. Put $w=\operatorname{ord}(\mathcal K)$. Then there is a real number
  $A_{\mathrm{box}}$ such that
  \[
    1\leq A_{\mathrm{box}}\leq
    \max\{A_{0,\mathrm{box}},
      (dBC_t^d)^{C_{\mathrm{box}}d^2w}\}.
  \]
  For every parameter vector $\theta$ feasible at radius $B$ and every support-maximal factor
  $a\in\mathcal K$ incident to $i$,
  \[
    (\theta_a^*-\theta_a)^2
      \leq A_{\mathrm{box}}\,
        \frac12\int
          \bigl(\partial_iE_{\theta-\theta^*}(x)\bigr)^2\,dp_{\theta^*}(x).
  \] -/)
  (proof := /-- Put $u=dBC_t^d$ and $w=\operatorname{ord}(\mathcal K)$. By
  \cref{lem:support-box-constant-envelope}, there are absolute constants
  $A_{0,\mathrm{box}}>1$ and $C_{\mathrm{box}}>0$ for which
  \[
    1\leq 4e^{1/32}(792d^2u)^{2dw}
      \leq \max\{A_{0,\mathrm{box}},u^{C_{\mathrm{box}}d^2w}\}.
  \]
  Choose $A_{\mathrm{box}}=4e^{1/32}(792d^2u)^{2dw}$. The displayed inequalities give
  the required lower and upper bounds for $A_{\mathrm{box}}$, and
  \cref{lem:support-box-weighted-coefficient-bound} gives, simultaneously for every feasible
  $\theta$ and every incident support-maximal factor $a$,
  \[
    (\theta_a^*-\theta_a)^2\leq
      A_{\mathrm{box}}\,\frac12\int
        \bigl(\partial_iE_{\theta-\theta^*}(x)\bigr)^2\,dp_{\theta^*}(x).
  \]
  This is the asserted conclusion. -/)
  (title := /-- Support-box density comparison and maximal coefficient extraction -/)
  (latexEnv := "lemma")]
lemma support_box_density_comparison :
    ∃ A0 : ℝ, 1 < A0 ∧
      ∃ Cbox : ℕ, 0 < Cbox ∧
        ∀ {n : ℕ} (d : ℕ)
        (factors : Finset (polynomial_factor n)) (thetaStar : polynomial_factor n → ℝ)
        (i : Fin n) (B tailRate : ℝ) (Ct : ℕ) (p : MeasureTheory.Measure (Fin n → ℝ))
        [MeasureTheory.IsProbabilityMeasure p],
        family_degree_at_most factors d →
        unit_base_polynomial_exponential_family factors thetaStar p →
        0 < B → parameter_feasible factors B thetaStar →
        1 + (1 / 1024 : ℝ) ≤ (d : ℝ) * B * (Ct : ℝ) ^ d →
        tail_decay_condition d tailRate Ct p →
        ∃ Abox : ℝ,
          1 ≤ Abox ∧
          Abox ≤
            max A0 (((d : ℝ) * B * (Ct : ℝ) ^ d) ^
              (Cbox * d ^ 2 * interaction_order factors)) ∧
          ∀ theta, parameter_feasible factors B theta →
            ∀ factor ∈ incident_maximal_factors factors i,
              (thetaStar factor - theta factor) ^ 2 ≤
                Abox * ((1 / 2 : ℝ) * ∫ x,
                  (energy_first_partial factors
                    (fun a => theta a - thetaStar a) i x) ^ 2 ∂p) := by
  obtain ⟨A0, hA0, Cbox, hCbox, hEnvelope⟩ := support_box_constant_envelope
  refine ⟨A0, hA0, Cbox, hCbox, ?_⟩
  intro n d factors thetaStar i B tailRate Ct p _ hdegree hfamily hB hthetaStar hu htail
  have hEnvelope' := hEnvelope d (interaction_order factors)
    ((d : ℝ) * B * (Ct : ℝ) ^ d) hu
  refine ⟨4 * Real.exp (1 / 32 : ℝ) *
      (792 * (d : ℝ) ^ 2 * ((d : ℝ) * B * (Ct : ℝ) ^ d)) ^
        (2 * d * interaction_order factors), hEnvelope'.1, hEnvelope'.2, ?_⟩
  exact support_box_weighted_coefficient_bound d factors thetaStar i B tailRate Ct p
    hdegree hfamily hB hthetaStar hu htail

@[blueprint "lem:maximal-factor-curvature"
  (statement := /-- There exist an absolute real constant $A_{0,{\rm curv}}>1$ and a positive
  absolute integer $C_{\rm curv}$ with the following property. Let $n,d\in\mathbb N$, let
  $\mathcal K\subseteq\mathbb N^n$ be a finite family of factors, let
  $\theta^*:\mathbb N^n\to\mathbb R$, and fix $i\in[n]$. Let $B,k\in\mathbb R$, let
  $C_t\in\mathbb N$, and let $p$ be a probability measure on $\mathbb R^n$. Assume that
  $\mathcal K$ has total degree at most $d$, that $p$ is the unit-base polynomial exponential
  family generated by $(\mathcal K,\theta^*)$, that $B>0$, that $\theta^*$ is feasible at
  coordinatewise radius $B$, that $dBC_t^d\geq1+2^{-10}$, and that $p$ satisfies the
  degree-$d$ tail-decay condition with rate $k$ and threshold $C_t$. Write
  $w=\operatorname{ord}(\mathcal K)$. Then there is a real number $A_{\rm curv}$ satisfying
  \[
    1\le A_{\rm curv}\le
    \max\{A_{0,{\rm curv}},(dBC_t^d)^{C_{\rm curv}d^2w}\}
  \]
  such that, for every parameter vector $\theta$ feasible at radius $B$ and every
  support-maximal factor $a\in\mathcal K$ incident to $i$,
  \[
    (\theta_a-\theta_a^*)^2
      \le A_{\rm curv}\bigl(\mathcal L_i(\theta)-\mathcal L_i(\theta^*)\bigr).
  \] -/)
  (proof := /-- Choose the absolute constants and the model-dependent number
  $A_{\mathrm{curv}}$ supplied by
  \cref{lem:support-box-density-comparison}. For every feasible $\theta$ and every incident
  maximal factor $a$, that lemma gives
  \[
    (\theta_a^*-\theta_a)^2
      \leq A_{\mathrm{curv}}\,
        \frac12\int
          \bigl(\partial_iE_{\theta-\theta^*}(x)\bigr)^2\,dp_{\theta^*}(x).
  \]
  All hypotheses of \cref{lem:population-score-excess-identity} are among the present
  hypotheses. Applying it identifies the last factor with
  $\mathcal L_i(\theta)-\mathcal L_i(\theta^*)$. The lower and upper bounds for
  $A_{\mathrm{curv}}$ are unchanged, so this is precisely the asserted curvature inequality,
  simultaneously for every feasible parameter and every maximal factor incident to $i$. -/)
  (title := /-- Quantitative curvature on incident maximal factors -/)
  (latexEnv := "lemma")]
lemma maximal_factor_curvature :
    ∃ A0 : ℝ, 1 < A0 ∧
      ∃ Ccurv : ℕ, 0 < Ccurv ∧
        ∀ {n : ℕ} (d : ℕ)
        (factors : Finset (polynomial_factor n)) (thetaStar : polynomial_factor n → ℝ)
        (i : Fin n) (B tailRate : ℝ) (Ct : ℕ) (p : MeasureTheory.Measure (Fin n → ℝ))
        [MeasureTheory.IsProbabilityMeasure p],
        family_degree_at_most factors d →
        unit_base_polynomial_exponential_family factors thetaStar p →
        0 < B → parameter_feasible factors B thetaStar →
        1 + (1 / 1024 : ℝ) ≤ (d : ℝ) * B * (Ct : ℝ) ^ d →
        tail_decay_condition d tailRate Ct p →
        ∃ Acurv : ℝ,
          1 ≤ Acurv ∧
          Acurv ≤
            max A0 (((d : ℝ) * B * (Ct : ℝ) ^ d) ^
              (Ccurv * d ^ 2 * interaction_order factors)) ∧
          ∀ theta, parameter_feasible factors B theta →
            ∀ factor ∈ incident_maximal_factors factors i,
              (thetaStar factor - theta factor) ^ 2 ≤
                Acurv * (population_local_score_matching_loss factors theta i p -
                  population_local_score_matching_loss factors thetaStar i p) := by
  obtain ⟨A0, hA0, Ccurv, hCcurv, hcomparison⟩ := support_box_density_comparison
  refine ⟨A0, hA0, Ccurv, hCcurv, ?_⟩
  intro n d factors thetaStar i B tailRate Ct p _ hdegree hfamily hB hthetaStar hu htail
  obtain ⟨Acurv, hAcurv, hAcurvBound, hcoefficient⟩ :=
    hcomparison d factors thetaStar i B tailRate Ct p
      hdegree hfamily hB hthetaStar hu htail
  refine ⟨Acurv, hAcurv, hAcurvBound, ?_⟩
  intro theta htheta factor hfactor
  rw [population_score_excess_identity d factors thetaStar theta i tailRate Ct p
    hdegree hfamily htail]
  exact hcoefficient theta htheta factor hfactor

@[blueprint "lem:independent-centered-even-moment-count"
  (statement := /-- For positive integers (j) with (2j\leq r), the number of ways to
  choose (j) labels from (M), multiplied by (j^r), is at most
  (4^r r^{r-j}M^j). -/)
  (proof := /-- The standard estimate
  \(inom{M}{j}\leq M^j/j!\), Stirling's lower bound
  \((j/e)^j\leq j!\), and (e<3<4) give
  \(j^j/j!\leq4^r\). The remaining factor (j^{r-j}) is at most
  (r^{r-j}). -/)
  (title := /-- A coarse labelled-partition count -/)
  (latexEnv := "lemma")]
lemma independent_centered_even_moment_count (M r j : ℕ) (hj : 0 < j)
    (hjr : 2 * j ≤ r) :
    (M.choose j : ℝ) * (j : ℝ) ^ r ≤
      (4 : ℝ) ^ r * (r : ℝ) ^ (r - j) * (M : ℝ) ^ j := by
  have hjr' : j ≤ r := by omega
  have hjpos : (0 : ℝ) < (j : ℝ) := by positivity
  have hfacpos : (0 : ℝ) < (j.factorial : ℝ) := by positivity
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * (j : ℝ)) := by
    have harg : (0 : ℝ) ≤ 2 * Real.pi * (j : ℝ) := by positivity
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hjone : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hargone : (1 : ℝ) ≤ 2 * Real.pi * (j : ℝ) := by nlinarith
    nlinarith [Real.sq_sqrt harg, Real.sqrt_nonneg (2 * Real.pi * (j : ℝ))]
  have hstirling : ((j : ℝ) / Real.exp 1) ^ j ≤ (j.factorial : ℝ) := by
    exact le_trans (le_mul_of_one_le_left (by positivity) hsqrt)
      (Stirling.le_factorial_stirling j)
  have hexp : (Real.exp 1) ^ j ≤ (4 : ℝ) ^ r := by
    calc
      (Real.exp 1) ^ j ≤ (3 : ℝ) ^ j :=
        pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le j
      _ ≤ (4 : ℝ) ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
      _ ≤ (4 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num) hjr'
  have hjpow : (j : ℝ) ^ j ≤ (4 : ℝ) ^ r * (j.factorial : ℝ) := by
    calc
      (j : ℝ) ^ j = (Real.exp 1) ^ j * (((j : ℝ) / Real.exp 1) ^ j) := by
        rw [← mul_pow]
        field_simp
      _ ≤ (Real.exp 1) ^ j * (j.factorial : ℝ) :=
        mul_le_mul_of_nonneg_left hstirling (by positivity)
      _ ≤ (4 : ℝ) ^ r * (j.factorial : ℝ) :=
        mul_le_mul_of_nonneg_right hexp (by positivity)
  have hchoose : (M.choose j : ℝ) ≤ (M : ℝ) ^ j / (j.factorial : ℝ) :=
    Nat.choose_le_pow_div j M
  have hjbase : (j : ℝ) ≤ (r : ℝ) := by exact_mod_cast hjr'
  calc
    (M.choose j : ℝ) * (j : ℝ) ^ r ≤
        ((M : ℝ) ^ j / (j.factorial : ℝ)) * (j : ℝ) ^ r :=
      mul_le_mul_of_nonneg_right hchoose (by positivity)
    _ = (M : ℝ) ^ j * (j : ℝ) ^ (r - j) *
        ((j : ℝ) ^ j / (j.factorial : ℝ)) := by
      have hpow : (j : ℝ) ^ r = (j : ℝ) ^ (r - j) * (j : ℝ) ^ j := by
        conv_lhs => rw [show r = (r - j) + j by omega]
        exact pow_add _ _ _
      rw [hpow]
      field_simp
    _ ≤ (M : ℝ) ^ j * (r : ℝ) ^ (r - j) * (4 : ℝ) ^ r := by
      have ha : (j : ℝ) ^ (r - j) ≤ (r : ℝ) ^ (r - j) :=
        pow_le_pow_left₀ (by positivity) hjbase (r - j)
      have hb : (j : ℝ) ^ j / (j.factorial : ℝ) ≤ (4 : ℝ) ^ r :=
        (div_le_iff₀ hfacpos).2 hjpow
      exact mul_le_mul (mul_le_mul_of_nonneg_left ha (by positivity)) hb
        (by positivity) (by positivity)
    _ = (4 : ℝ) ^ r * (r : ℝ) ^ (r - j) * (M : ℝ) ^ j := by ring

@[blueprint "lem:independent-centered-even-moment-multiset-count"
  (statement := /-- Among multisets of cardinality (r) drawn from (M) labels, the sum
  of the multinomial coefficients of those having exactly (j) distinct labels is at most
  \(inom Mj j^r\). -/)
  (proof := /-- Send each multiset to its support together with the multiset itself. This is
  an injection into the pairs consisting of a (j)-element subset and an (r)-multiset on
  that subset. For each fixed support, the multinomial theorem at the constant vector (1)
  says that the sum of the multinomial coefficients is (j^r). -/)
  (title := /-- Multinomial mass with fixed support size -/)
  (latexEnv := "lemma")]
lemma independent_centered_even_moment_multiset_count (M r j : ℕ) :
    ∑ k ∈ (Finset.univ.sym r).filter (fun k : Sym (Fin M) r => k.val.toFinset.card = j),
        (k.val.countPerms : ℝ) ≤
      (M.choose j : ℝ) * (j : ℝ) ^ r := by
  classical
  let source :=
    (Finset.univ.sym r).filter (fun k : Sym (Fin M) r => k.val.toFinset.card = j)
  let target : Finset (Σ _s : Finset (Fin M), Sym (Fin M) r) :=
    ((Finset.univ : Finset (Fin M)).powersetCard j).sigma (fun s => s.sym r)
  let e : Sym (Fin M) r → Σ _s : Finset (Fin M), Sym (Fin M) r :=
    fun k => ⟨k.val.toFinset, k⟩
  have he_mem : ∀ k ∈ source, e k ∈ target := by
    intro k hk
    simp only [source, Finset.mem_filter] at hk
    rcases hk with ⟨hk_univ, hkcard⟩
    simp only [target, Finset.mem_sigma]
    constructor
    · simp only [e, Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hkcard⟩
    · rw [Finset.mem_sym_iff]
      intro a ha
      exact Multiset.mem_toFinset.mpr ha
  have he_inj : Set.InjOn e source := by
    intro k₁ hk₁ k₂ hk₂ h
    exact congrArg Sigma.snd h
  have himage : source.image e ⊆ target := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨k, hk, rfl⟩
    exact he_mem k hk
  have hsource :
      ∑ k ∈ source, (k.val.countPerms : ℝ) =
        ∑ z ∈ source.image e, (z.2.val.countPerms : ℝ) := by
    rw [Finset.sum_image]
    intro k₁ hk₁ k₂ hk₂ h
    exact he_inj hk₁ hk₂ h
  have hfixed (s : Finset (Fin M)) :
      ∑ k ∈ s.sym r, (k.val.countPerms : ℝ) = (s.card : ℝ) ^ r := by
    have h := Finset.sum_pow (s := s) (fun _ : Fin M => (1 : ℝ)) r
    simpa using h.symm
  calc
    ∑ k ∈ (Finset.univ.sym r).filter
          (fun k : Sym (Fin M) r => k.val.toFinset.card = j),
        (k.val.countPerms : ℝ) = ∑ k ∈ source, (k.val.countPerms : ℝ) := by rfl
    _ = ∑ z ∈ source.image e, (z.2.val.countPerms : ℝ) := hsource
    _ ≤ ∑ z ∈ target, (z.2.val.countPerms : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg himage (fun _ _ _ => by positivity)
    _ = ∑ s ∈ (Finset.univ : Finset (Fin M)).powersetCard j,
          ∑ k ∈ s.sym r, (k.val.countPerms : ℝ) := by
      rw [show target = ((Finset.univ : Finset (Fin M)).powersetCard j).sigma
        (fun s => s.sym r) by rfl, Finset.sum_sigma]
    _ = ∑ s ∈ (Finset.univ : Finset (Fin M)).powersetCard j, (s.card : ℝ) ^ r := by
      apply Finset.sum_congr rfl
      intro s hs
      exact hfixed s
    _ = ∑ _s ∈ (Finset.univ : Finset (Fin M)).powersetCard j, (j : ℝ) ^ r := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [(Finset.mem_powersetCard.mp hs).2]
    _ = (M.choose j : ℝ) * (j : ℝ) ^ r := by
      simp

@[blueprint "lem:independent-centered-even-moment-interpolation"
  (statement := /-- Let (2\leq a\leq r), with (r>2). If a measurable real random
  variable has (L^2)-norm at most (A) and (L^r)-norm at most (B), then its absolute
  (a)-th moment is at most
  \(A^{2(r-a)/(r-2)}B^{r(a-2)/(r-2)}\). -/)
  (proof := /-- Write (a=2\theta+r(1-\theta)), where
  \(\theta=(r-a)/(r-2)\). Hölder's inequality applied to
  \(|X|^{2\theta}|X|^{r(1-\theta)}\), followed by the two norm hypotheses, gives the
  result. The endpoint cases (a=2) and (a=r) follow directly from the definition of
  the corresponding (L^p)-norm. -/)
  (title := /-- Interpolation of an intermediate absolute moment -/)
  (latexEnv := "lemma")]
lemma independent_centered_even_moment_interpolation
    {Ω : Type} [MeasurableSpace Ω] (mu : MeasureTheory.Measure Ω)
    (f : Ω → ℝ) (A B : ℝ) (r a : ℕ) (hf : Measurable f)
    (hA : MeasureTheory.eLpNorm f (2 : ENNReal) mu ≤ ENNReal.ofReal A)
    (hB : MeasureTheory.eLpNorm f (r : ENNReal) mu ≤ ENNReal.ofReal B)
    (hr : 2 < r) (ha₂ : 2 ≤ a) (har : a ≤ r) :
    ∫⁻ ω, ‖f ω‖ₑ ^ (a : ℝ) ∂mu ≤
      ENNReal.ofReal A ^ (2 * ((r : ℝ) - (a : ℝ)) / ((r : ℝ) - 2)) *
        ENNReal.ofReal B ^ ((r : ℝ) * ((a : ℝ) - 2) / ((r : ℝ) - 2)) := by
  have hrpos : (0 : ℝ) < (r : ℝ) := by positivity
  have hrR : (2 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hrden : (0 : ℝ) < (r : ℝ) - 2 := by linarith
  have hmoment (n : ℕ) (hn : 0 < n) :
      ∫⁻ ω, ‖f ω‖ₑ ^ (n : ℝ) ∂mu =
        MeasureTheory.eLpNorm f (n : ENNReal) mu ^ (n : ℝ) := by
    rw [MeasureTheory.lintegral_rpow_enorm_eq_rpow_eLpNorm' (q := (n : ℝ))
      (by positivity)]
    congr 1
    rw [MeasureTheory.eLpNorm_eq_eLpNorm']
    · simp
    · norm_cast
      omega
    · exact ENNReal.coe_ne_top
  have htwo :
      ∫⁻ ω, ‖f ω‖ₑ ^ (2 : ℝ) ∂mu ≤ ENNReal.ofReal A ^ (2 : ℝ) := by
    change (∫⁻ ω, ‖f ω‖ₑ ^ ((2 : ℕ) : ℝ) ∂mu) ≤
      ENNReal.ofReal A ^ ((2 : ℕ) : ℝ)
    rw [hmoment 2 (by omega)]
    exact ENNReal.rpow_le_rpow hA (by norm_num)
  have hrmom :
      ∫⁻ ω, ‖f ω‖ₑ ^ (r : ℝ) ∂mu ≤ ENNReal.ofReal B ^ (r : ℝ) := by
    rw [hmoment r (by omega)]
    exact ENNReal.rpow_le_rpow hB (by positivity)
  rcases eq_or_lt_of_le ha₂ with rfl | ha₂'
  · simpa [hrden.ne'] using htwo
  rcases eq_or_lt_of_le har with rfl | har'
  · simpa [hrden.ne'] using hrmom
  let θ : ℝ := ((r : ℝ) - (a : ℝ)) / ((r : ℝ) - 2)
  have hθpos : 0 < θ := by
    dsimp [θ]
    have harR : (a : ℝ) < (r : ℝ) := by exact_mod_cast har'
    exact div_pos (sub_pos.mpr harR) hrden
  have hθlt : θ < 1 := by
    dsimp [θ]
    rw [div_lt_one hrden]
    have haR : (2 : ℝ) < (a : ℝ) := by exact_mod_cast ha₂'
    linarith
  have hθnonneg : 0 ≤ θ := hθpos.le
  have hθone : 0 ≤ 1 - θ := sub_nonneg.mpr hθlt.le
  have hconj : θ⁻¹.HolderConjugate (1 - θ)⁻¹ :=
    Real.HolderConjugate.inv_inv hθpos (sub_pos.mpr hθlt) (by ring)
  have hN : AEMeasurable (fun ω => ‖f ω‖ₑ) mu := hf.enorm.aemeasurable
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq mu hconj
    (hN.pow_const (2 * θ)) (hN.pow_const ((r : ℝ) * (1 - θ)))
  have hrewrite :
      (fun ω => ‖f ω‖ₑ ^ (2 * θ) * ‖f ω‖ₑ ^ ((r : ℝ) * (1 - θ))) =
        (fun ω => ‖f ω‖ₑ ^ (a : ℝ)) := by
    funext ω
    rw [← ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg (by norm_num) hθnonneg)
      (mul_nonneg hrpos.le hθone)]
    congr 2
    dsimp [θ]
    field_simp
    ring
  change (∫⁻ ω, ‖f ω‖ₑ ^ (2 * θ) *
    ‖f ω‖ₑ ^ ((r : ℝ) * (1 - θ)) ∂mu) ≤ _ at hholder
  have hholder' :
      ∫⁻ ω, ‖f ω‖ₑ ^ (a : ℝ) ∂mu ≤
        (∫⁻ ω, ‖f ω‖ₑ ^ (2 : ℝ) ∂mu) ^ θ *
          (∫⁻ ω, ‖f ω‖ₑ ^ (r : ℝ) ∂mu) ^ (1 - θ) := by
    have hpow2 :
        (fun ω => (‖f ω‖ₑ ^ (2 * θ)) ^ θ⁻¹) =
          (fun ω => ‖f ω‖ₑ ^ (2 : ℝ)) := by
      funext ω
      rw [← ENNReal.rpow_mul]
      congr 2
      field_simp [ne_of_gt hθpos]
    have hpowr :
        (fun ω => (‖f ω‖ₑ ^ ((r : ℝ) * (1 - θ))) ^ (1 - θ)⁻¹) =
          (fun ω => ‖f ω‖ₑ ^ (r : ℝ)) := by
      funext ω
      rw [← ENNReal.rpow_mul]
      congr 2
      field_simp [ne_of_gt (sub_pos.mpr hθlt)]
    have hinvθ : 1 / θ⁻¹ = θ := by field_simp
    have hinvone : 1 / (1 - θ)⁻¹ = 1 - θ := by field_simp
    rw [hpow2, hpowr, hinvθ, hinvone] at hholder
    rw [show (∫⁻ ω, ‖f ω‖ₑ ^ (a : ℝ) ∂mu) =
        ∫⁻ ω, ‖f ω‖ₑ ^ (2 * θ) * ‖f ω‖ₑ ^ ((r : ℝ) * (1 - θ)) ∂mu by
          apply MeasureTheory.lintegral_congr
          intro ω
          exact congrFun hrewrite.symm ω]
    exact hholder
  calc
    ∫⁻ ω, ‖f ω‖ₑ ^ (a : ℝ) ∂mu ≤
        (∫⁻ ω, ‖f ω‖ₑ ^ (2 : ℝ) ∂mu) ^ θ *
          (∫⁻ ω, ‖f ω‖ₑ ^ (r : ℝ) ∂mu) ^ (1 - θ) := hholder'
    _ ≤ (ENNReal.ofReal A ^ (2 : ℝ)) ^ θ *
          (ENNReal.ofReal B ^ (r : ℝ)) ^ (1 - θ) :=
      mul_le_mul (ENNReal.rpow_le_rpow htwo hθpos.le)
        (ENNReal.rpow_le_rpow hrmom (sub_nonneg.mpr hθlt.le)) (by positivity) (by positivity)
    _ = ENNReal.ofReal A ^ (2 * ((r : ℝ) - (a : ℝ)) / ((r : ℝ) - 2)) *
        ENNReal.ofReal B ^ ((r : ℝ) * ((a : ℝ) - 2) / ((r : ℝ) - 2)) := by
      simp only [← ENNReal.rpow_mul]
      dsimp [θ]
      congr 2 <;> field_simp <;> ring

@[blueprint "lem:independent-centered-even-moment-monomial"
  (statement := /-- Under the hypotheses of the even-moment estimate, the expectation of
  a monomial indexed by an (r)-multiset in which every used label occurs at least twice is
  bounded by the product of the interpolated moments of its fibers. -/)
  (proof := /-- Regroup the monomial by its support. Independence factors its expectation
  into the product of the expectations of the corresponding powers. Bound the norm of each
  integral by the integral of the absolute value and apply
  \cref{lem:independent-centered-even-moment-interpolation} at the fiber multiplicity. -/)
  (title := /-- Bound for one surviving independent monomial -/)
  (latexEnv := "lemma")]
lemma independent_centered_even_moment_monomial
    {M : ℕ} {Ω : Type} [MeasurableSpace Ω] (mu : MeasureTheory.Measure Ω)
    (X : Fin M → Ω → ℝ) (A B : ℝ) (r : ℕ)
    (hIndep : ProbabilityTheory.iIndepFun X mu) (hMeas : ∀ m, Measurable (X m))
    (hA : ∀ m, MeasureTheory.eLpNorm (X m) (2 : ENNReal) mu ≤ ENNReal.ofReal A)
    (hB : ∀ m, MeasureTheory.eLpNorm (X m) (r : ENNReal) mu ≤ ENNReal.ofReal B)
    (hr : 2 < r) (k : Sym (Fin M) r)
    (hk : ∀ m ∈ k.val.toFinset, 2 ≤ k.val.count m) :
    ‖∫ ω, (k.val.map fun m => X m ω).prod ∂mu‖ₑ ≤
      ∏ m ∈ k.val.toFinset,
        ENNReal.ofReal A ^
            (2 * ((r : ℝ) - (k.val.count m : ℝ)) / ((r : ℝ) - 2)) *
          ENNReal.ofReal B ^
            ((r : ℝ) * ((k.val.count m : ℝ) - 2) / ((r : ℝ) - 2)) := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure mu := hIndep.isProbabilityMeasure
  let S := k.val.toFinset
  let Y : Fin M → Ω → ℝ := fun m ω => X m ω ^ k.val.count m
  have hYIndep : ProbabilityTheory.iIndepFun Y mu := by
    apply hIndep.comp (fun m x => x ^ k.val.count m)
    intro m
    fun_prop
  have hYMeas : ∀ m, Measurable (Y m) := by
    intro m
    exact (hMeas m).pow_const _
  have hfactor :
      (∫ ω, ∏ m, Y m ω ∂mu) = ∏ m, ∫ ω, Y m ω ∂mu :=
    hYIndep.integral_fun_prod_eq_prod_integral
      (fun m => (hYMeas m).aestronglyMeasurable)
  have hregroup :
      (fun ω => (k.val.map fun m => X m ω).prod) =
        (fun ω => ∏ m, Y m ω) := by
    funext ω
    rw [Finset.prod_multiset_map_count]
    apply Fintype.prod_subset
    intro m hm
    by_contra hnot
    have hm0 : k.val.count m = 0 := Multiset.count_eq_zero.mpr
      (by simpa [S] using hnot)
    exact hm (by rw [hm0]; simp)
  have hfactorSupport :
      (∏ m, ∫ ω, Y m ω ∂mu) = ∏ m ∈ S, ∫ ω, Y m ω ∂mu := by
    symm
    apply Fintype.prod_subset
    intro m hm
    by_contra hnot
    have hm0 : k.val.count m = 0 := Multiset.count_eq_zero.mpr
      (by simpa [S] using hnot)
    apply hm
    rw [show Y m = (fun _ω : Ω => (1 : ℝ)) by
      funext ω
      change X m ω ^ k.val.count m = 1
      rw [hm0]
      simp]
    simp
  rw [hregroup, hfactor, hfactorSupport, Real.enorm_eq_ofReal_abs, Finset.abs_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => abs_nonneg _)]
  simp only [← Real.enorm_eq_ofReal_abs]
  change (∏ m ∈ S, ‖∫ ω, Y m ω ∂mu‖ₑ) ≤ _
  apply Finset.prod_le_prod
  · intro m hm
    positivity
  intro m hm
  change ‖∫ ω, X m ω ^ k.val.count m ∂mu‖ₑ ≤ _
  calc
    ‖∫ ω, X m ω ^ k.val.count m ∂mu‖ₑ ≤
        ∫⁻ ω, ‖X m ω ^ k.val.count m‖ₑ ∂mu :=
      MeasureTheory.enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ ω, ‖X m ω‖ₑ ^ (k.val.count m : ℝ) ∂mu := by
      apply MeasureTheory.lintegral_congr
      intro ω
      simp [ENNReal.rpow_natCast]
    _ ≤ ENNReal.ofReal A ^
            (2 * ((r : ℝ) - (k.val.count m : ℝ)) / ((r : ℝ) - 2)) *
          ENNReal.ofReal B ^
            ((r : ℝ) * ((k.val.count m : ℝ) - 2) / ((r : ℝ) - 2)) := by
      apply independent_centered_even_moment_interpolation mu (X m) A B r
        (k.val.count m) (hMeas m) (hA m) (hB m) hr (hk m (by simpa [S] using hm))
      simpa using Multiset.count_le_card m k.val

@[blueprint "lem:independent-centered-even-moment-singleton"
  (statement := /-- For independent centered real random variables, the expectation of
  any monomial containing an index with multiplicity one is zero. -/)
  (proof := /-- Regroup the monomial by index and use independence to factor its
  expectation. The factor corresponding to the index of multiplicity one is its
  centered first moment, hence vanishes. -/)
  (title := /-- Vanishing of monomials with a singleton index -/)
  (latexEnv := "lemma")]
lemma independent_centered_even_moment_singleton
    {M : ℕ} {Ω : Type} [MeasurableSpace Ω] (mu : MeasureTheory.Measure Ω)
    (X : Fin M → Ω → ℝ) (r : ℕ)
    (hIndep : ProbabilityTheory.iIndepFun X mu) (hMeas : ∀ m, Measurable (X m))
    (hCenter : ∀ m, ∫ omega, X m omega ∂mu = 0)
    (k : Sym (Fin M) r) (m : Fin M) (hm : k.val.count m = 1) :
    ∫ omega, (k.val.map fun i => X i omega).prod ∂mu = 0 := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure mu := hIndep.isProbabilityMeasure
  let Y : Fin M → Ω → ℝ := fun i omega => X i omega ^ k.val.count i
  have hYIndep : ProbabilityTheory.iIndepFun Y mu := by
    apply hIndep.comp (fun i x => x ^ k.val.count i)
    intro i
    fun_prop
  have hYMeas : ∀ i, Measurable (Y i) := by
    intro i
    exact (hMeas i).pow_const _
  have hfactor :
      (∫ omega, ∏ i, Y i omega ∂mu) = ∏ i, ∫ omega, Y i omega ∂mu :=
    hYIndep.integral_fun_prod_eq_prod_integral
      (fun i => (hYMeas i).aestronglyMeasurable)
  have hregroup :
      (fun omega => (k.val.map fun i => X i omega).prod) =
        (fun omega => ∏ i, Y i omega) := by
    funext omega
    rw [Finset.prod_multiset_map_count]
    apply Fintype.prod_subset
    intro i hi
    by_contra hnot
    have hi0 : k.val.count i = 0 := Multiset.count_eq_zero.mpr
      (by simpa using hnot)
    exact hi (by rw [hi0]; simp)
  rw [hregroup, hfactor]
  apply Finset.prod_eq_zero (Finset.mem_univ m)
  change ∫ omega, X m omega ^ k.val.count m ∂mu = 0
  rw [hm]
  simpa using hCenter m

@[blueprint "lem:independent-centered-even-moment-integrable"
  (statement := /-- If every variable belongs to (L^r), then every degree-(r)
  monomial in the variables is integrable on a probability space. -/)
  (proof := /-- Regroup the monomial by labels. For a label of multiplicity (a),
  its power belongs to (L^{r/a}). Generalized Hölder over the support applies because
  the reciprocal exponents sum to (sum a/r=1), proving integrability. -/)
  (title := /-- Integrability of degree-(r) monomials -/)
  (latexEnv := "lemma")]
lemma independent_centered_even_moment_integrable
    {M : ℕ} {Ω : Type} [MeasurableSpace Ω] (mu : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure mu] (X : Fin M → Ω → ℝ) (B : ℝ) (r : ℕ)
    (hMeas : ∀ m, Measurable (X m))
    (hB : ∀ m, MeasureTheory.eLpNorm (X m) (r : ENNReal) mu ≤ ENNReal.ofReal B)
    (hr : 0 < r) (k : Sym (Fin M) r) :
    MeasureTheory.Integrable
      (fun omega => (k.val.map fun m => X m omega).prod) mu := by
  classical
  let S := k.val.toFinset
  let p : Fin M → ENNReal := fun m => (r : ENNReal) / (k.val.count m : ENNReal)
  have hmem (m : Fin M) :
      MeasureTheory.MemLp (X m) (r : ENNReal) mu := by
    refine ⟨(hMeas m).aestronglyMeasurable, lt_of_le_of_lt (hB m) ?_⟩
    exact ENNReal.ofReal_lt_top
  have hpow (m : Fin M) (hm : m ∈ S) :
      MeasureTheory.MemLp (fun omega => X m omega ^ k.val.count m) (p m) mu := by
    have h := (hmem m).norm_rpow_div (k.val.count m : ENNReal)
    apply h.congr_enorm ((hMeas m).pow_const _).aestronglyMeasurable
    filter_upwards with omega
    simp [p, ENNReal.toReal_natCast, Real.norm_eq_abs, abs_pow]
  have hinv (m : Fin M) (hm : m ∈ S) :
      (p m)⁻¹ = (k.val.count m : ENNReal) / (r : ENNReal) := by
    apply ENNReal.inv_div
    · left
      simp
    · right
      exact_mod_cast hr.ne'
  have hsumNat : ∑ m ∈ S, k.val.count m = r := by
    calc
      ∑ m ∈ S, k.val.count m = k.val.card :=
        Multiset.sum_count_eq_card
          (fun a ha => by simpa [S] using Multiset.mem_toFinset.mpr ha)
      _ = r := k.property
  have hsum : ∑ m ∈ S, (p m)⁻¹ = 1 := by
    calc
      ∑ m ∈ S, (p m)⁻¹ =
          ∑ m ∈ S, (k.val.count m : ENNReal) / (r : ENNReal) := by
        apply Finset.sum_congr rfl
        intro m hm
        exact hinv m hm
      _ = ∑ m ∈ S, (k.val.count m : ENNReal) * (r : ENNReal)⁻¹ := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [div_eq_mul_inv]
      _ = (∑ m ∈ S, (k.val.count m : ENNReal)) * (r : ENNReal)⁻¹ := by
        rw [Finset.sum_mul]
      _ = (r : ENNReal) * (r : ENNReal)⁻¹ := by
        congr 1
        exact_mod_cast hsumNat
      _ = 1 := ENNReal.mul_inv_cancel (by exact_mod_cast hr.ne') (by simp)
  have hprod :
      MeasureTheory.MemLp
        (fun omega => ∏ m ∈ S, X m omega ^ k.val.count m) 1 mu := by
    have h := MeasureTheory.MemLp.prod' (s := S) (p := p)
      (f := fun m omega => X m omega ^ k.val.count m) hpow
    simpa [hsum] using h
  apply (hprod.integrable (by norm_num)).congr
  filter_upwards with omega
  rw [Finset.prod_multiset_map_count]

@[blueprint "lem:independent-centered-even-moment-support-bound"
  (statement := /-- For a surviving degree-(r) monomial with (j) distinct
  indices, its expected absolute contribution is at most
  (A^{2(rj-r)/(r-2)}B^{r(r-2j)/(r-2)}). -/)
  (proof := /-- Apply
  \cref{lem:independent-centered-even-moment-monomial}. Multiplying its
  interpolated fiber bounds, the (A)-exponents sum to
  (2(rj-r)/(r-2)), while the (B)-exponents sum to
  (r(r-2j)/(r-2)), because the fiber multiplicities sum to (r). -/)
  (title := /-- Support-size form of the monomial bound -/)
  (latexEnv := "lemma")]
lemma independent_centered_even_moment_support_bound
    {M : ℕ} {Ω : Type} [MeasurableSpace Ω] (mu : MeasureTheory.Measure Ω)
    (X : Fin M → Ω → ℝ) (A B : ℝ) (r : ℕ)
    (hIndep : ProbabilityTheory.iIndepFun X mu) (hMeas : ∀ m, Measurable (X m))
    (hA : ∀ m, MeasureTheory.eLpNorm (X m) (2 : ENNReal) mu ≤ ENNReal.ofReal A)
    (hB : ∀ m, MeasureTheory.eLpNorm (X m) (r : ENNReal) mu ≤ ENNReal.ofReal B)
    (hApos : 0 < A) (hBpos : 0 < B) (hr : 2 < r)
    (k : Sym (Fin M) r) (hk : ∀ m ∈ k.val.toFinset, 2 ≤ k.val.count m) :
    ‖∫ omega, (k.val.map fun m => X m omega).prod ∂mu‖ₑ ≤
      ENNReal.ofReal A ^
          (2 * ((r : ℝ) * (k.val.toFinset.card : ℝ) - (r : ℝ)) /
            ((r : ℝ) - 2)) *
        ENNReal.ofReal B ^
          ((r : ℝ) * ((r : ℝ) - 2 * (k.val.toFinset.card : ℝ)) /
            ((r : ℝ) - 2)) := by
  classical
  let S := k.val.toFinset
  have hbaseA0 : ENNReal.ofReal A ≠ 0 := (ENNReal.ofReal_pos.mpr hApos).ne'
  have hbaseB0 : ENNReal.ofReal B ≠ 0 := (ENNReal.ofReal_pos.mpr hBpos).ne'
  have hbaseAtop : ENNReal.ofReal A ≠ ⊤ := ENNReal.ofReal_ne_top
  have hbaseBtop : ENNReal.ofReal B ≠ ⊤ := ENNReal.ofReal_ne_top
  have hrpow_sum (C : ENNReal) (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
      (s : Finset (Fin M)) (e : Fin M → ℝ) :
      ∏ m ∈ s, C ^ e m = C ^ (∑ m ∈ s, e m) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert m s hm ih =>
        simp only [Finset.mem_insert, Finset.sum_insert hm, Finset.prod_insert hm]
        rw [ih, ENNReal.rpow_add _ _ hC0 hCtop]
  have hsumCount : ∑ m ∈ S, k.val.count m = r := by
    calc
      ∑ m ∈ S, k.val.count m = k.val.card :=
        Multiset.sum_count_eq_card
          (fun a ha => by simpa [S] using Multiset.mem_toFinset.mpr ha)
      _ = r := k.property
  have hsumCountR : ∑ m ∈ S, (k.val.count m : ℝ) = (r : ℝ) := by
    exact_mod_cast hsumCount
  have hsumA :
      ∑ m ∈ S,
          (2 * ((r : ℝ) - (k.val.count m : ℝ)) / ((r : ℝ) - 2)) =
        2 * ((r : ℝ) * (S.card : ℝ) - (r : ℝ)) / ((r : ℝ) - 2) := by
    rw [← Finset.sum_div]
    congr 1
    calc
      ∑ m ∈ S, 2 * ((r : ℝ) - (k.val.count m : ℝ)) =
          2 * ∑ m ∈ S, ((r : ℝ) - (k.val.count m : ℝ)) := by
            rw [Finset.mul_sum]
      _ = 2 * ((∑ _m ∈ S, (r : ℝ)) -
          ∑ m ∈ S, (k.val.count m : ℝ)) := by
            rw [Finset.sum_sub_distrib]
      _ = 2 * ((r : ℝ) * (S.card : ℝ) - (r : ℝ)) := by
            rw [hsumCountR]
            simp only [Finset.sum_const, nsmul_eq_mul]
            ring
  have hsumB :
      ∑ m ∈ S,
          ((r : ℝ) * ((k.val.count m : ℝ) - 2) / ((r : ℝ) - 2)) =
        (r : ℝ) * ((r : ℝ) - 2 * (S.card : ℝ)) / ((r : ℝ) - 2) := by
    rw [← Finset.sum_div]
    congr 1
    calc
      ∑ m ∈ S, (r : ℝ) * ((k.val.count m : ℝ) - 2) =
          (r : ℝ) * ∑ m ∈ S, ((k.val.count m : ℝ) - 2) := by
            rw [Finset.mul_sum]
      _ = (r : ℝ) * ((∑ m ∈ S, (k.val.count m : ℝ)) -
          ∑ _m ∈ S, (2 : ℝ)) := by
            rw [Finset.sum_sub_distrib]
      _ = (r : ℝ) * ((r : ℝ) - 2 * (S.card : ℝ)) := by
            rw [hsumCountR]
            simp only [Finset.sum_const, nsmul_eq_mul]
            ring
  calc
    ‖∫ omega, (k.val.map fun m => X m omega).prod ∂mu‖ₑ ≤
        ∏ m ∈ S,
          ENNReal.ofReal A ^
              (2 * ((r : ℝ) - (k.val.count m : ℝ)) / ((r : ℝ) - 2)) *
            ENNReal.ofReal B ^
              ((r : ℝ) * ((k.val.count m : ℝ) - 2) / ((r : ℝ) - 2)) := by
      exact independent_centered_even_moment_monomial mu X A B r hIndep hMeas
        hA hB hr k (by simpa [S] using hk)
    _ = (∏ m ∈ S,
          ENNReal.ofReal A ^
            (2 * ((r : ℝ) - (k.val.count m : ℝ)) / ((r : ℝ) - 2))) *
        ∏ m ∈ S,
          ENNReal.ofReal B ^
            ((r : ℝ) * ((k.val.count m : ℝ) - 2) / ((r : ℝ) - 2)) := by
      rw [Finset.prod_mul_distrib]
    _ = ENNReal.ofReal A ^
          (2 * ((r : ℝ) * (S.card : ℝ) - (r : ℝ)) / ((r : ℝ) - 2)) *
        ENNReal.ofReal B ^
          ((r : ℝ) * ((r : ℝ) - 2 * (S.card : ℝ)) / ((r : ℝ) - 2)) := by
      rw [hrpow_sum _ hbaseA0 hbaseAtop, hrpow_sum _ hbaseB0 hbaseBtop,
        hsumA, hsumB]
    _ = _ := by rfl

@[blueprint "lem:independent-centered-even-moment-expansion"
  (statement := /-- If the summands belong to (L^r), the (r)-th moment of
  their finite sum is the multinomial sum of the expectations of its degree-(r)
  monomials. -/)
  (proof := /-- Every degree-(r) monomial is integrable by
  \cref{lem:independent-centered-even-moment-integrable}. Apply the multinomial
  theorem pointwise, commute the finite sum with the integral, and pull each
  constant multinomial coefficient outside its integral. -/)
  (title := /-- Multinomial expansion of the finite-sum moment -/)
  (latexEnv := "lemma")]
lemma independent_centered_even_moment_expansion
    {M : ℕ} {Ω : Type} [MeasurableSpace Ω] (mu : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure mu] (X : Fin M → Ω → ℝ) (B : ℝ) (r : ℕ)
    (hMeas : ∀ m, Measurable (X m))
    (hB : ∀ m, MeasureTheory.eLpNorm (X m) (r : ENNReal) mu ≤ ENNReal.ofReal B)
    (hr : 0 < r) :
    (∫ omega, (∑ m, X m omega) ^ r ∂mu) =
      ∑ k ∈ Finset.univ.sym r,
        (k.val.countPerms : ℝ) *
          ∫ omega, (k.val.map fun m => X m omega).prod ∂mu := by
  classical
  have hMonomialInt (k : Sym (Fin M) r) :
      MeasureTheory.Integrable
        (fun omega => (k.val.map fun m => X m omega).prod) mu :=
    independent_centered_even_moment_integrable mu X B r hMeas hB hr k
  have hpoint :
      (fun omega => (∑ m, X m omega) ^ r) =
        (fun omega => ∑ k ∈ Finset.univ.sym r,
          (k.val.countPerms : ℝ) *
            (k.val.map fun m => X m omega).prod) := by
    funext omega
    simpa using Finset.sum_pow (s := (Finset.univ : Finset (Fin M)))
      (fun m => X m omega) r
  rw [hpoint, MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [MeasureTheory.integral_const_mul]
  · intro k hk
    exact (hMonomialInt k).const_mul _

@[blueprint "lem:independent-centered-even-moment-centered-expansion"
  (statement := /-- In the multinomial expansion of the (r)-th moment of
  independent centered variables, only monomials in which every used index has
  multiplicity at least two contribute. -/)
  (proof := /-- Start from
  \cref{lem:independent-centered-even-moment-expansion}. Every term outside the
  displayed subfamily has a used index of positive multiplicity less than two,
  hence multiplicity one, and its expectation vanishes by
  \cref{lem:independent-centered-even-moment-singleton}. -/)
  (title := /-- Centered multinomial moment expansion -/)
  (latexEnv := "lemma")]
lemma independent_centered_even_moment_centered_expansion
    {M : ℕ} {Ω : Type} [MeasurableSpace Ω] (mu : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure mu] (X : Fin M → Ω → ℝ) (B : ℝ) (r : ℕ)
    (hIndep : ProbabilityTheory.iIndepFun X mu) (hMeas : ∀ m, Measurable (X m))
    (hCenter : ∀ m, ∫ omega, X m omega ∂mu = 0)
    (hB : ∀ m, MeasureTheory.eLpNorm (X m) (r : ENNReal) mu ≤ ENNReal.ofReal B)
    (hr : 0 < r) :
    (∫ omega, (∑ m, X m omega) ^ r ∂mu) =
      ∑ k ∈ (Finset.univ.sym r).filter
          (fun k : Sym (Fin M) r =>
            ∀ m ∈ k.val.toFinset, 2 ≤ k.val.count m),
        (k.val.countPerms : ℝ) *
          ∫ omega, (k.val.map fun m => X m omega).prod ∂mu := by
  classical
  rw [independent_centered_even_moment_expansion mu X B r hMeas hB hr]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro k hkUniv hkNot
  simp only [Finset.mem_filter, hkUniv, true_and] at hkNot
  push Not at hkNot
  obtain ⟨m, hm, hmLt⟩ := hkNot
  have hmPos : 0 < k.val.count m := Multiset.count_pos.mpr
    (Multiset.mem_toFinset.mp hm)
  have hmOne : k.val.count m = 1 := by omega
  rw [independent_centered_even_moment_singleton mu X r hIndep hMeas hCenter k m hmOne,
    mul_zero]

@[blueprint "lem:independent-centered-even-moment-grouped-bound"
  (statement := /-- For even (r>2), the extended norm of the (r)-th moment
  integral is bounded by the sum, over support sizes (1leq jleq r/2), of
  the multinomial mass bound times
  (A^{2(rj-r)/(r-2)}B^{r(r-2j)/(r-2)}). -/)
  (proof := /-- Use
  \cref{lem:independent-centered-even-moment-centered-expansion} and the
  triangle inequality, then group surviving multisets by support cardinality.
  The support has cardinality between (1) and (r/2). On the fiber of
  cardinality (j), apply
  \cref{lem:independent-centered-even-moment-support-bound}, factor out the
  common bound, and control the remaining multinomial mass with
  \cref{lem:independent-centered-even-moment-multiset-count}. -/)
  (title := /-- Grouped bound for the centered moment expansion -/)
  (latexEnv := "lemma")]
lemma independent_centered_even_moment_grouped_bound
    {M : ℕ} {Ω : Type} [MeasurableSpace Ω] (mu : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure mu] (X : Fin M → Ω → ℝ)
    (A B : ℝ) (r : ℕ)
    (hIndep : ProbabilityTheory.iIndepFun X mu) (hMeas : ∀ m, Measurable (X m))
    (hCenter : ∀ m, ∫ omega, X m omega ∂mu = 0)
    (hApos : 0 < A) (hBpos : 0 < B)
    (hA : ∀ m, MeasureTheory.eLpNorm (X m) (2 : ENNReal) mu ≤ ENNReal.ofReal A)
    (hB : ∀ m, MeasureTheory.eLpNorm (X m) (r : ENNReal) mu ≤ ENNReal.ofReal B)
    (hr : 2 < r) :
    ‖∫ omega, (∑ m, X m omega) ^ r ∂mu‖ₑ ≤
      ∑ j ∈ Finset.Icc 1 (r / 2),
        ((M.choose j : ENNReal) * (j : ENNReal) ^ r) *
          (ENNReal.ofReal A ^
              (2 * ((r : ℝ) * (j : ℝ) - (r : ℝ)) / ((r : ℝ) - 2)) *
            ENNReal.ofReal B ^
              ((r : ℝ) * ((r : ℝ) - 2 * (j : ℝ)) / ((r : ℝ) - 2))) := by
  classical
  let Good : Finset (Sym (Fin M) r) :=
    (Finset.univ.sym r).filter
      (fun k => ∀ m ∈ k.val.toFinset, 2 ≤ k.val.count m)
  let J := Finset.Icc 1 (r / 2)
  let F : Sym (Fin M) r → ENNReal := fun k =>
    (k.val.countPerms : ENNReal) *
      ‖∫ omega, (k.val.map fun m => X m omega).prod ∂mu‖ₑ
  have hGoodJ : ∀ k ∈ Good, k.val.toFinset.card ∈ J := by
    intro k hk
    simp only [Good, Finset.mem_filter] at hk
    rcases hk with ⟨hkUniv, hkGood⟩
    have hsum : ∑ m ∈ k.val.toFinset, k.val.count m = r := by
      calc
        ∑ m ∈ k.val.toFinset, k.val.count m = k.val.card :=
          Multiset.sum_count_eq_card (fun a ha => Multiset.mem_toFinset.mpr ha)
        _ = r := k.property
    have htwice : 2 * k.val.toFinset.card ≤ r := by
      calc
        2 * k.val.toFinset.card =
            ∑ _m ∈ k.val.toFinset, 2 := by simp [mul_comm]
        _ ≤ ∑ m ∈ k.val.toFinset, k.val.count m :=
          Finset.sum_le_sum fun m hm => hkGood m hm
        _ = r := hsum
    have hcardPos : 0 < k.val.toFinset.card := by
      rw [Finset.card_pos, Multiset.toFinset_nonempty]
      intro hz
      have hk0 : r = 0 := by
        rw [← k.property, hz]
        simp
      omega
    simp only [J, Finset.mem_Icc]
    constructor
    · omega
    · omega
  have hGrouped :
      ∑ k ∈ Good, F k =
        ∑ j ∈ J, ∑ k ∈ Good with k.val.toFinset.card = j, F k := by
    rw [Finset.sum_fiberwise_eq_sum_filter]
    apply Finset.sum_congr
    · symm
      apply Finset.filter_eq_self.mpr
      exact hGoodJ
    · intro k hk
      rfl
  have hMass (j : ℕ) :
      ∑ k ∈ (Finset.univ.sym r).filter
          (fun k : Sym (Fin M) r => k.val.toFinset.card = j),
          (k.val.countPerms : ENNReal) ≤
        (M.choose j : ENNReal) * (j : ENNReal) ^ r := by
    have h := independent_centered_even_moment_multiset_count M r j
    exact_mod_cast h
  rw [independent_centered_even_moment_centered_expansion mu X B r hIndep hMeas
    hCenter hB (by omega)]
  calc
    ‖∑ k ∈ Good,
        (k.val.countPerms : ℝ) *
          ∫ omega, (k.val.map fun m => X m omega).prod ∂mu‖ₑ ≤
        ∑ k ∈ Good, F k := by
      calc
        _ ≤ ∑ k ∈ Good,
            ‖(k.val.countPerms : ℝ) *
              ∫ omega, (k.val.map fun m => X m omega).prod ∂mu‖ₑ :=
          enorm_sum_le Good _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro k hk
          simp [F, Real.enorm_eq_ofReal_abs]
    _ = ∑ j ∈ J, ∑ k ∈ Good with k.val.toFinset.card = j, F k := hGrouped
    _ ≤ ∑ j ∈ J,
        ((M.choose j : ENNReal) * (j : ENNReal) ^ r) *
          (ENNReal.ofReal A ^
              (2 * ((r : ℝ) * (j : ℝ) - (r : ℝ)) / ((r : ℝ) - 2)) *
            ENNReal.ofReal B ^
              ((r : ℝ) * ((r : ℝ) - 2 * (j : ℝ)) / ((r : ℝ) - 2))) := by
      apply Finset.sum_le_sum
      intro j hj
      let C : ENNReal :=
        ENNReal.ofReal A ^
            (2 * ((r : ℝ) * (j : ℝ) - (r : ℝ)) / ((r : ℝ) - 2)) *
          ENNReal.ofReal B ^
            ((r : ℝ) * ((r : ℝ) - 2 * (j : ℝ)) / ((r : ℝ) - 2))
      calc
        ∑ k ∈ Good with k.val.toFinset.card = j, F k ≤
            ∑ k ∈ Good with k.val.toFinset.card = j,
              (k.val.countPerms : ENNReal) * C := by
          apply Finset.sum_le_sum
          intro k hk
          simp only [Finset.mem_filter] at hk
          rcases hk with ⟨hkGoodMem, hkCard⟩
          simp only [Good, Finset.mem_filter] at hkGoodMem
          rcases hkGoodMem with ⟨hkUniv, hkGood⟩
          apply mul_le_mul_left'
          have hsupp :=
            independent_centered_even_moment_support_bound mu X A B r hIndep hMeas
              hA hB hApos hBpos hr k hkGood
          rw [hkCard] at hsupp
          exact hsupp
        _ = (∑ k ∈ Good with k.val.toFinset.card = j,
              (k.val.countPerms : ENNReal)) * C := by
          rw [Finset.sum_mul]
        _ ≤ ((M.choose j : ENNReal) * (j : ENNReal) ^ r) * C := by
          apply mul_le_mul_right'
          calc
            ∑ k ∈ Good with k.val.toFinset.card = j,
                (k.val.countPerms : ENNReal) ≤
                ∑ k ∈ (Finset.univ.sym r).filter
                    (fun k : Sym (Fin M) r => k.val.toFinset.card = j),
                  (k.val.countPerms : ENNReal) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro k hk
                simp only [Finset.mem_filter] at hk ⊢
                exact ⟨(Finset.mem_filter.mp hk.1).1, hk.2⟩
              · intro k hk hnot
                positivity
            _ ≤ (M.choose j : ENNReal) * (j : ENNReal) ^ r := hMass j
        _ = _ := by rfl
    _ = _ := by rfl

@[blueprint "lem:independent-centered-even-moment-summand-bound"
  (statement := /-- If (r>2), (1leq j), and (2jleq r), then the
  support-(j) summand in the grouped moment estimate is at most
  (4^r(U+V)^r), where
  (U=r^{1/2}M^{1/2}A) and (V=rM^{1/r}B). -/)
  (proof := /-- First apply
  \cref{lem:independent-centered-even-moment-count}. Write the two interpolation
  exponents as (E_A=2(rj-r)/(r-2)) and
  (E_B=r(r-2j)/(r-2)). They are nonnegative, satisfy
  (E_A+E_B=r) and (E_A/2+E_B/r=j), while
  (r-jleq E_A/2+E_B). Thus the remaining powers are bounded by
  (U^{E_A}V^{E_B}), which is at most ((U+V)^r) by monotonicity. -/)
  (title := /-- Algebraic bound for one support-size summand -/)
  (latexEnv := "lemma")]
lemma independent_centered_even_moment_summand_bound
    (M r j : ℕ) (A B : ℝ) (hr : 2 < r) (hj : 0 < j) (hjr : 2 * j ≤ r) :
    ((M.choose j : ENNReal) * (j : ENNReal) ^ r) *
        (ENNReal.ofReal A ^
            (2 * ((r : ℝ) * (j : ℝ) - (r : ℝ)) / ((r : ℝ) - 2)) *
          ENNReal.ofReal B ^
            ((r : ℝ) * ((r : ℝ) - 2 * (j : ℝ)) / ((r : ℝ) - 2))) ≤
      (4 : ENNReal) ^ r *
        (((r : ENNReal) ^ (1 / 2 : ℝ) * (M : ENNReal) ^ (1 / 2 : ℝ) *
              ENNReal.ofReal A) +
          (r : ENNReal) * (M : ENNReal) ^ (1 / (r : ℝ)) *
              ENNReal.ofReal B) ^ (r : ℝ) := by
  let EA : ℝ := 2 * ((r : ℝ) * (j : ℝ) - (r : ℝ)) / ((r : ℝ) - 2)
  let EB : ℝ := (r : ℝ) * ((r : ℝ) - 2 * (j : ℝ)) / ((r : ℝ) - 2)
  let R : ENNReal := (r : ENNReal)
  let N : ENNReal := (M : ENNReal)
  let U : ENNReal := R ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ) * ENNReal.ofReal A
  let V : ENNReal := R * N ^ (1 / (r : ℝ)) * ENNReal.ofReal B
  have hrR : (2 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by positivity
  have hEA : 0 ≤ EA := by
    dsimp [EA]
    have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hnum : 0 ≤ (r : ℝ) * (j : ℝ) - (r : ℝ) := by
      nlinarith
    exact div_nonneg (mul_nonneg (by norm_num) hnum) (sub_nonneg.mpr hrR.le)
  have hEB : 0 ≤ EB := by
    dsimp [EB]
    have hjrR : 2 * (j : ℝ) ≤ (r : ℝ) := by exact_mod_cast hjr
    exact div_nonneg (mul_nonneg hrpos.le (sub_nonneg.mpr hjrR))
      (sub_nonneg.mpr hrR.le)
  have hsumExp : EA + EB = (r : ℝ) := by
    dsimp [EA, EB]
    field_simp [ne_of_gt (sub_pos.mpr hrR)]
    ring
  have hNExp : EA / 2 + EB / (r : ℝ) = (j : ℝ) := by
    dsimp [EA, EB]
    field_simp [ne_of_gt (sub_pos.mpr hrR), ne_of_gt hrpos]
    ring
  have hRExp : (r - j : ℕ) ≤ EA / 2 + EB := by
    have hjr' : j ≤ r := by omega
    have hjrR : 2 * (j : ℝ) ≤ (r : ℝ) := by exact_mod_cast hjr
    rw [Nat.cast_sub hjr']
    have hrem : 0 ≤ ((r : ℝ) - 2 * (j : ℝ)) / ((r : ℝ) - 2) :=
      div_nonneg (sub_nonneg.mpr hjrR) (sub_nonneg.mpr hrR.le)
    have hid :
        EA / 2 + EB =
          ((r : ℝ) - (j : ℝ)) +
            ((r : ℝ) - 2 * (j : ℝ)) / ((r : ℝ) - 2) := by
      dsimp [EA, EB]
      field_simp [ne_of_gt (sub_pos.mpr hrR)]
      ring
    rw [hid]
    exact le_add_of_nonneg_right hrem
  have hcount :
      (M.choose j : ENNReal) * (j : ENNReal) ^ r ≤
        (4 : ENNReal) ^ r * R ^ (r - j) * N ^ j := by
    dsimp [R, N]
    exact_mod_cast independent_centered_even_moment_count M r j hj hjr
  have hscaled :
      R ^ (r - j) * N ^ j * ENNReal.ofReal A ^ EA * ENNReal.ofReal B ^ EB ≤
        U ^ EA * V ^ EB := by
    have hRone : 1 ≤ R := by
      dsimp [R]
      exact_mod_cast (show 1 ≤ r by omega)
    have hRp :
        R ^ (r - j) ≤ R ^ (EA / 2 + EB) := by
      rw [← ENNReal.rpow_natCast]
      exact ENNReal.rpow_le_rpow_of_exponent_le hRone hRExp
    have hNp : N ^ j = N ^ (EA / 2 + EB / (r : ℝ)) := by
      rw [← ENNReal.rpow_natCast, hNExp]
    have hUexp :
        U ^ EA =
          R ^ (EA / 2) * N ^ (EA / 2) * ENNReal.ofReal A ^ EA := by
      dsimp [U]
      rw [ENNReal.mul_rpow_of_nonneg _ _ hEA,
        ENNReal.mul_rpow_of_nonneg _ _ hEA,
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      congr 2 <;> ring_nf
    have hVexp :
        V ^ EB =
          R ^ EB * N ^ (EB / (r : ℝ)) * ENNReal.ofReal B ^ EB := by
      dsimp [V]
      rw [ENNReal.mul_rpow_of_nonneg _ _ hEB,
        ENNReal.mul_rpow_of_nonneg _ _ hEB,
        ← ENNReal.rpow_mul]
      congr 2
      ring_nf
    have hRcombine :
        R ^ (EA / 2 + EB) = R ^ (EA / 2) * R ^ EB :=
      ENNReal.rpow_add_of_nonneg _ _ (by positivity) hEB
    have hNcombine :
        N ^ (EA / 2 + EB / (r : ℝ)) =
          N ^ (EA / 2) * N ^ (EB / (r : ℝ)) :=
      ENNReal.rpow_add_of_nonneg _ _ (by positivity)
        (div_nonneg hEB hrpos.le)
    calc
      R ^ (r - j) * N ^ j * ENNReal.ofReal A ^ EA * ENNReal.ofReal B ^ EB ≤
          R ^ (EA / 2 + EB) * N ^ j *
            ENNReal.ofReal A ^ EA * ENNReal.ofReal B ^ EB := by
        gcongr
      _ = R ^ (EA / 2 + EB) * N ^ (EA / 2 + EB / (r : ℝ)) *
            ENNReal.ofReal A ^ EA * ENNReal.ofReal B ^ EB := by
        rw [← hNp]
      _ = U ^ EA * V ^ EB := by
        rw [hUexp, hVexp, hRcombine, hNcombine]
        ring
  have hUV : U ^ EA * V ^ EB ≤ (U + V) ^ (r : ℝ) := by
    calc
      U ^ EA * V ^ EB ≤ (U + V) ^ EA * (U + V) ^ EB := by
        exact mul_le_mul (ENNReal.rpow_le_rpow (by exact le_add_right (le_refl U)) hEA)
          (ENNReal.rpow_le_rpow (by exact le_add_left (le_refl V)) hEB)
          (by positivity) (by positivity)
      _ = (U + V) ^ (EA + EB) := by
        rw [ENNReal.rpow_add_of_nonneg _ _ hEA hEB]
      _ = (U + V) ^ (r : ℝ) := by rw [hsumExp]
  change ((M.choose j : ENNReal) * (j : ENNReal) ^ r) *
      (ENNReal.ofReal A ^ EA * ENNReal.ofReal B ^ EB) ≤
    (4 : ENNReal) ^ r * (U + V) ^ (r : ℝ)
  calc
    ((M.choose j : ENNReal) * (j : ENNReal) ^ r) *
        (ENNReal.ofReal A ^ EA * ENNReal.ofReal B ^ EB) ≤
      ((4 : ENNReal) ^ r * R ^ (r - j) * N ^ j) *
        (ENNReal.ofReal A ^ EA * ENNReal.ofReal B ^ EB) :=
      mul_le_mul_right' hcount _
    _ = (4 : ENNReal) ^ r *
        (R ^ (r - j) * N ^ j * ENNReal.ofReal A ^ EA * ENNReal.ofReal B ^ EB) := by
      ring
    _ ≤ (4 : ENNReal) ^ r * (U ^ EA * V ^ EB) := mul_le_mul_left' hscaled _
    _ ≤ (4 : ENNReal) ^ r * (U + V) ^ (r : ℝ) := mul_le_mul_left' hUV _

@[blueprint "lem:independent-centered-even-moment-integral-bound"
  (statement := /-- Under the hypotheses of the even-moment estimate with
  (r>2), the extended norm of the (r)-th moment integral is at most
  (8^r(U+V)^r), with
  (U=r^{1/2}M^{1/2}A) and (V=rM^{1/r}B). -/)
  (proof := /-- Apply
  \cref{lem:independent-centered-even-moment-grouped-bound} and bound every
  support-size summand by
  \cref{lem:independent-centered-even-moment-summand-bound}. There are at most
  (r/2leq2^r) support sizes, and (2^r4^r=8^r). -/)
  (title := /-- Final bound for the even-moment integral -/)
  (latexEnv := "lemma")]
lemma independent_centered_even_moment_integral_bound
    {M : ℕ} {Ω : Type} [MeasurableSpace Ω] (mu : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure mu] (X : Fin M → Ω → ℝ)
    (A B : ℝ) (r : ℕ)
    (hIndep : ProbabilityTheory.iIndepFun X mu) (hMeas : ∀ m, Measurable (X m))
    (hCenter : ∀ m, ∫ omega, X m omega ∂mu = 0)
    (hApos : 0 < A) (hBpos : 0 < B)
    (hA : ∀ m, MeasureTheory.eLpNorm (X m) (2 : ENNReal) mu ≤ ENNReal.ofReal A)
    (hB : ∀ m, MeasureTheory.eLpNorm (X m) (r : ENNReal) mu ≤ ENNReal.ofReal B)
    (hr : 2 < r) :
    ‖∫ omega, (∑ m, X m omega) ^ r ∂mu‖ₑ ≤
      (8 : ENNReal) ^ r *
        (((r : ENNReal) ^ (1 / 2 : ℝ) * (M : ENNReal) ^ (1 / 2 : ℝ) *
              ENNReal.ofReal A) +
          (r : ENNReal) * (M : ENNReal) ^ (1 / (r : ℝ)) *
              ENNReal.ofReal B) ^ (r : ℝ) := by
  let J := Finset.Icc 1 (r / 2)
  let W : ENNReal :=
    ((r : ENNReal) ^ (1 / 2 : ℝ) * (M : ENNReal) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal A) +
      (r : ENNReal) * (M : ENNReal) ^ (1 / (r : ℝ)) * ENNReal.ofReal B
  have hJcard : J.card ≤ 2 ^ r := by
    have hcard : J.card = r / 2 := by
      dsimp [J]
      rw [Nat.card_Icc]
      omega
    rw [hcard]
    have hpow : r ≤ 2 ^ r := by
      have hbern : 1 + r * 1 ≤ (1 + 1) ^ r :=
        one_add_le_pow_of_two_add_nonneg (R := ℕ) (a := 1) (by omega) r
      norm_num at hbern ⊢
      omega
    omega
  calc
    ‖∫ omega, (∑ m, X m omega) ^ r ∂mu‖ₑ ≤
        ∑ j ∈ J,
          ((M.choose j : ENNReal) * (j : ENNReal) ^ r) *
            (ENNReal.ofReal A ^
                (2 * ((r : ℝ) * (j : ℝ) - (r : ℝ)) / ((r : ℝ) - 2)) *
              ENNReal.ofReal B ^
                ((r : ℝ) * ((r : ℝ) - 2 * (j : ℝ)) / ((r : ℝ) - 2))) := by
      exact independent_centered_even_moment_grouped_bound mu X A B r hIndep hMeas
        hCenter hApos hBpos hA hB hr
    _ ≤ ∑ _j ∈ J, (4 : ENNReal) ^ r * W ^ (r : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_Icc.mp hj
      dsimp [W]
      exact independent_centered_even_moment_summand_bound M r j A B hr
        (by omega) (by omega)
    _ = (J.card : ENNReal) * ((4 : ENNReal) ^ r * W ^ (r : ℝ)) := by
      simp
    _ ≤ (2 : ENNReal) ^ r * ((4 : ENNReal) ^ r * W ^ (r : ℝ)) := by
      gcongr
      exact_mod_cast hJcard
    _ = (8 : ENNReal) ^ r * W ^ (r : ℝ) := by
      rw [show (2 : ENNReal) ^ r * ((4 : ENNReal) ^ r * W ^ (r : ℝ)) =
          ((2 : ENNReal) ^ r * (4 : ENNReal) ^ r) * W ^ (r : ℝ) by ring,
        ← mul_pow]
      norm_num
    _ = _ := by rfl

@[blueprint "lem:independent-centered-second-moment-sum"
  (statement := /-- Independent centered real random variables whose individual
  (L^2)-norms are at most (A>0) satisfy
  (|sum_{m=1}^M X_m|_2leqsqrt M,A). -/)
  (proof := /-- Pairwise independence makes the variance of the sum equal the sum
  of the individual variances. Centering identifies every variance with its second
  moment, and the (L^2)-norm hypotheses bound those moments by (A^2).
  Taking square roots proves the result. -/)
  (title := /-- Second moment of an independent centered sum -/)
  (latexEnv := "lemma")]
lemma independent_centered_second_moment_sum
    {M : ℕ} {Ω : Type} [MeasurableSpace Ω] (mu : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure mu] (X : Fin M → Ω → ℝ) (A : ℝ)
    (hIndep : ProbabilityTheory.iIndepFun X mu) (hMeas : ∀ m, Measurable (X m))
    (hCenter : ∀ m, ∫ omega, X m omega ∂mu = 0) (hApos : 0 < A)
    (hA : ∀ m, MeasureTheory.eLpNorm (X m) (2 : ENNReal) mu ≤ ENNReal.ofReal A) :
    MeasureTheory.eLpNorm (fun omega => ∑ m, X m omega) (2 : ENNReal) mu ≤
      ENNReal.ofReal (Real.sqrt (M : ℝ) * A) := by
  classical
  let S : Ω → ℝ := fun omega => ∑ m, X m omega
  have hMem (m : Fin M) : MeasureTheory.MemLp (X m) (2 : ENNReal) mu := by
    refine ⟨(hMeas m).aestronglyMeasurable, lt_of_le_of_lt (hA m) ?_⟩
    exact ENNReal.ofReal_lt_top
  have hSMem : MeasureTheory.MemLp S (2 : ENNReal) mu := by
    dsimp [S]
    exact MeasureTheory.memLp_finsetSum Finset.univ
      (fun m hm => hMem m)
  have hScenter : ∫ omega, S omega ∂mu = 0 := by
    dsimp [S]
    rw [MeasureTheory.integral_finsetSum]
    · simp [hCenter]
    · intro m hm
      exact (hMem m).integrable (by norm_num)
  have hVar :
      ProbabilityTheory.variance S mu =
        ∑ m, ProbabilityTheory.variance (X m) mu := by
    have hv := ProbabilityTheory.IndepFun.variance_sum
      (μ := mu) (X := X) (s := (Finset.univ : Finset (Fin M)))
      (fun m hm => hMem m)
      (by
        intro i hi j hj hij
        exact hIndep.indepFun hij)
    rw [show S = ∑ m, X m by
      funext omega
      simp [S]]
    exact hv
  have hVarEach (m : Fin M) :
      ProbabilityTheory.variance (X m) mu ≤ A ^ 2 := by
    rw [ProbabilityTheory.variance_of_integral_eq_zero
      (hMeas m).aemeasurable (hCenter m)]
    have heq := (hMem m).eLpNorm_eq_integral_rpow_norm
      (p := (2 : ENNReal)) (by norm_num) (by norm_num)
    have hbound := hA m
    rw [heq] at hbound
    simp only [ENNReal.toReal_ofNat, invOf_eq_inv] at hbound
    have hnorm :
        (∫ omega, ‖X m omega‖ ^ (2 : ℝ) ∂mu) =
          ∫ omega, X m omega ^ 2 ∂mu := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with omega
      rw [Real.rpow_two]
      simp [Real.norm_eq_abs, sq_abs]
    rw [hnorm] at hbound
    have hhalf : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    rw [hhalf] at hbound
    have hroot :
        Real.sqrt (∫ omega, X m omega ^ 2 ∂mu) ≤ A := by
      rw [Real.sqrt_eq_rpow]
      exact (ENNReal.ofReal_le_ofReal_iff hApos.le).mp hbound
    have hnonneg : 0 ≤ ∫ omega, X m omega ^ 2 ∂mu := by positivity
    have hsqrtNonneg :
        0 ≤ Real.sqrt (∫ omega, X m omega ^ 2 ∂mu) := Real.sqrt_nonneg _
    nlinarith [Real.sq_sqrt hnonneg]
  have hMoment :
      ∫ omega, S omega ^ 2 ∂mu ≤ (M : ℝ) * A ^ 2 := by
    rw [← ProbabilityTheory.variance_of_integral_eq_zero
      (hSMem.aemeasurable) hScenter, hVar]
    calc
      ∑ m, ProbabilityTheory.variance (X m) mu ≤ ∑ _m : Fin M, A ^ 2 :=
        Finset.sum_le_sum fun m hm => hVarEach m
      _ = (M : ℝ) * A ^ 2 := by simp
  have hMomentNonneg : 0 ≤ ∫ omega, S omega ^ 2 ∂mu := by positivity
  have hnormS := hSMem.eLpNorm_eq_integral_rpow_norm
    (p := (2 : ENNReal)) (by norm_num) (by norm_num)
  rw [hnormS]
  simp only [ENNReal.toReal_ofNat, invOf_eq_inv]
  have hnorm :
      (∫ omega, ‖S omega‖ ^ (2 : ℝ) ∂mu) =
        ∫ omega, S omega ^ 2 ∂mu := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with omega
    rw [Real.rpow_two]
    simp [Real.norm_eq_abs, sq_abs]
  rw [hnorm]
  have hhalf : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
  rw [hhalf, ← Real.sqrt_eq_rpow]
  apply ENNReal.ofReal_le_ofReal
  calc
    Real.sqrt (∫ omega, S omega ^ 2 ∂mu) ≤
        Real.sqrt ((M : ℝ) * A ^ 2) := Real.sqrt_le_sqrt hMoment
    _ = Real.sqrt (M : ℝ) * A := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_pos hApos]

@[blueprint "lem:independent-centered-even-moment-root"
  (statement := /-- Let \(r>0\) be even, let \(f\) belong to \(L^r(\mu)\), and let
  \(Z\in[0,\infty]\). If the extended norm of the \(r\)-th moment integral of
  \(f\) is at most \(Z^r\), then \(\lVert f\rVert_{L^r(\mu)}\leq Z\). -/)
  (proof := /-- Evenness makes (f^r) nonnegative and identifies it with
  (|f|^r). The integral formula for the (L^r)-norm therefore identifies its
  (r)-th power with the extended norm of the moment integral. Apply the
  increasing (1/r)-power to the assumed inequality. -/)
  (title := /-- Taking the root of an even-moment bound -/)
  (latexEnv := "lemma")]
lemma independent_centered_even_moment_root
    {Ω : Type} [MeasurableSpace Ω] (mu : MeasureTheory.Measure Ω)
    (f : Ω → ℝ) (r : ℕ) (Z : ENNReal)
    (hf : MeasureTheory.MemLp f (r : ENNReal) mu)
    (hr : 0 < r) (hEven : Even r)
    (hBound : ‖∫ omega, f omega ^ r ∂mu‖ₑ ≤ Z ^ (r : ℝ)) :
    MeasureTheory.eLpNorm f (r : ENNReal) mu ≤ Z := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hMomentNonneg : 0 ≤ ∫ omega, f omega ^ r ∂mu := by
    apply MeasureTheory.integral_nonneg
    intro omega
    exact hEven.pow_nonneg (f omega)
  have hOfRealBound :
      ENNReal.ofReal (∫ omega, f omega ^ r ∂mu) ≤ Z ^ (r : ℝ) := by
    simpa [Real.enorm_eq_ofReal_abs, abs_of_nonneg hMomentNonneg] using hBound
  have hNormMoment :
      (∫ omega, ‖f omega‖ ^ (r : ℝ) ∂mu) =
        ∫ omega, f omega ^ r ∂mu := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with omega
    rw [Real.rpow_natCast, Real.norm_eq_abs, ← abs_pow,
      abs_of_nonneg (hEven.pow_nonneg (f omega))]
  have hNormEq := hf.eLpNorm_eq_integral_rpow_norm
    (p := (r : ENNReal)) (by exact_mod_cast hr.ne') (by simp)
  rw [hNormEq]
  simp only [ENNReal.toReal_natCast, ENNReal.coe_ne_top, not_false_eq_true]
  rw [hNormMoment]
  have hrootNonneg : 0 ≤ 1 / (r : ℝ) := by positivity
  calc
    ENNReal.ofReal ((∫ omega, f omega ^ r ∂mu) ^ (r : ℝ)⁻¹) =
        ENNReal.ofReal (∫ omega, f omega ^ r ∂mu) ^ (1 / (r : ℝ)) := by
      rw [show (r : ℝ)⁻¹ = 1 / (r : ℝ) by rw [one_div],
        ENNReal.ofReal_rpow_of_nonneg hMomentNonneg hrootNonneg]
    _ ≤ (Z ^ (r : ℝ)) ^ (1 / (r : ℝ)) :=
      ENNReal.rpow_le_rpow hOfRealBound hrootNonneg
    _ = Z := by
      rw [← ENNReal.rpow_mul]
      have hmul : (r : ℝ) * (1 / (r : ℝ)) = 1 := by field_simp
      rw [hmul, ENNReal.rpow_one]

@[blueprint "lem:independent-centered-even-moment-sum"
  (statement := /-- Let \(M\geq1\), let \((\Omega,\mathcal F,\mu)\) be a probability space, and
  let \(X_1,\ldots,X_M\) be independent, measurable, integrable, centered real random
  variables. Let \(r\geq2\) be even, and let \(A,B>0\). If
  \[
    \lVert X_m\rVert_{L^2(\mu)}\leq A
    \quad\text{and}\quad
    \lVert X_m\rVert_{L^r(\mu)}\leq B
    \qquad (1\leq m\leq M),
  \]
  then
  \[
    \left\lVert\sum_{m=1}^M X_m\right\rVert_{L^r(\mu)}
      \leq8\left(\sqrt r\,\sqrt M\,A+rM^{1/r}B\right).
  \] -/)
  (proof := /-- Since \(r\) is even,
  \[
    \left\lVert\sum_mX_m\right\rVert_r^r
      =\mathbb E\left(\sum_mX_m\right)^r.
  \]
  Expand the power as a sum indexed by maps
  \(\phi:\{1,\ldots,r\}\to\{1,\ldots,M\}\). Such a map partitions
  \(\{1,\ldots,r\}\) into its nonempty fibers. Independence factors the expectation of
  the corresponding monomial over these fibers. If a fiber is a singleton, its factor is
  \(\mathbb EX_m=0\); hence only partitions having \(j\) blocks, each of cardinality at
  least \(2\), remain. In particular, \(1\leq j\leq r/2\).

  We first dispose of \(r=2\). By
  \cref{lem:independent-centered-second-moment-sum}, the preceding expansion then
  contains only the \(M\) diagonal terms, so
  \[
    \left\lVert\sum_mX_m\right\rVert_2^2
      =\sum_m\lVert X_m\rVert_2^2\leq MA^2.
  \]
  Taking square roots gives a bound stronger than the asserted one. We may therefore
  assume \(r\geq4\). In this case,
  \cref{lem:independent-centered-even-moment-integral-bound} supplies the moment
  estimate proved by the expansion and counting argument below.

  Fix a surviving partition with block sizes \(a_1,\ldots,a_j\), so that
  \(a_b\geq2\) and \(\sum_ba_b=r\). Log-convexity of \(L^p\)-norms between \(2\) and
  \(r\) gives, for every block assigned the index \(m\),
  \[
    \mathbb E|X_m|^{a_b}
      \leq
      A^{\,2(r-a_b)/(r-2)}
      B^{\,r(a_b-2)/(r-2)}.                                      \tag{1}
  \]
  Put
  \[
    \alpha_j=\frac{2(j-1)}{r-2}.
  \]
  Multiplication of (1) over the blocks shows that the absolute value of the contribution
  of the partition is at most
  \(A^{r\alpha_j}B^{r(1-\alpha_j)}\).

  It remains to count the surviving partitions. Denote by \(N_{r,j}\) the number of
  partitions of \(r\) labelled positions into \(j\) unlabeled blocks of size at least
  \(2\). Choose an unordered pair of distinguished positions in every block and then
  assign each of the remaining \(r-2j\) positions to one of the distinguished pairs.
  Every such partition is obtained at least once, whence
  \[
    N_{r,j}\leq
      \frac{r!}{2^j j!(r-2j)!}\,j^{\,r-2j}.                         \tag{2}
  \]
  We claim that
  \[
    N_{r,j}\leq4^r r^{\,r(1-\alpha_j/2)}.                           \tag{3}
  \]
  Indeed, \(r!/(r-2j)!\leq r^{2j}\) and
  \(j!\geq(j/e)^j\), so the right-hand side of (2) is at most
  \[
    (e/2)^j r^{2j}j^{\,r-3j}.                                      \tag{4}
  \]
  If \(3j\leq r\), then \(j^{r-3j}\leq r^{r-3j}\), and (4) is at most
  \(2^r r^{r-j}\). If \(3j>r\), then \(j/r>1/3\), and (4) is at most
  \[
    (e/2)^j3^{\,3j-r}r^{r-j}\leq4^r r^{r-j}.
  \]
  Finally,
  \[
    r\left(1-\frac{\alpha_j}{2}\right)-(r-j)
      =\frac{r-2j}{r-2}\geq0,
  \]
  proving (3).

  There are at most \(M^j\) injective assignments of random-variable indices to the
  \(j\) blocks. Consequently, the absolute-value estimate for the expanded moment,
  followed by (3), yields
  \[
    \mathbb E\left|\sum_mX_m\right|^r
      \leq\sum_{j=1}^{r/2}
        4^r r^{\,r(1-\alpha_j/2)}
        M^j A^{r\alpha_j}B^{r(1-\alpha_j)}.                         \tag{5}
  \]
  Set \(U=\sqrt r\,\sqrt M\,A\) and \(V=rM^{1/r}B\). The identity
  \[
    \frac{r\alpha_j}{2}+1-\alpha_j=j
  \]
  shows that the \(j\)-th summand in (5) is
  \(4^rU^{r\alpha_j}V^{r(1-\alpha_j)}\). Weighted arithmetic--geometric mean gives
  \(U^{\alpha_j}V^{1-\alpha_j}\leq U+V\). Since there are at most \(r/2\) summands and
  \(r/2\leq2^r\), (5) is at most
  \[
    \bigl[8(U+V)\bigr]^r.
  \]
  Applying \cref{lem:independent-centered-even-moment-root} and taking \(r\)-th
  roots proves the assertion. -/)
  (title := /-- Even moment bound for a finite independent centered sum -/)
  (latexEnv := "lemma")]
lemma independent_centered_even_moment_sum :
    ∀ {M : ℕ} {Ω : Type} [MeasurableSpace Ω]
      (mu : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure mu]
      (X : Fin M → Ω → ℝ) (A B : ℝ) (r : ℕ),
      ProbabilityTheory.iIndepFun X mu →
      (∀ m, Measurable (X m)) →
      (∀ m, MeasureTheory.Integrable (X m) mu) →
      (∀ m, ∫ omega, X m omega ∂mu = 0) →
      0 < A → 0 < B →
      (∀ m, MeasureTheory.eLpNorm (X m) (2 : ENNReal) mu ≤ ENNReal.ofReal A) →
      (∀ m, MeasureTheory.eLpNorm (X m) (r : ENNReal) mu ≤ ENNReal.ofReal B) →
      2 ≤ r → Even r → 0 < M →
        MeasureTheory.eLpNorm (fun omega => ∑ m, X m omega) (r : ENNReal) mu ≤
          ENNReal.ofReal
            (8 * (Real.sqrt (r : ℝ) * Real.sqrt (M : ℝ) * A +
              (r : ℝ) * Real.rpow (M : ℝ) (1 / (r : ℝ)) * B)) := by
  intro M Ω instMeas mu instProb X A B r hIndep hMeas hInt hCenter hApos hBpos
    hA hB hr hEven hM
  classical
  rcases eq_or_lt_of_le hr with rfl | hrgt
  · calc
      MeasureTheory.eLpNorm (fun omega => ∑ m, X m omega) (2 : ENNReal) mu ≤
          ENNReal.ofReal (Real.sqrt (M : ℝ) * A) :=
        independent_centered_second_moment_sum mu X A hIndep hMeas hCenter hApos hA
      _ ≤ ENNReal.ofReal
          (8 * (Real.sqrt (2 : ℝ) * Real.sqrt (M : ℝ) * A +
            (2 : ℝ) * Real.rpow (M : ℝ) (1 / (2 : ℝ)) * B)) := by
        apply ENNReal.ofReal_le_ofReal
        have hsqrtTwo : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
        have hMA : 0 ≤ Real.sqrt (M : ℝ) * A := by positivity
        have hfirst :
            Real.sqrt (M : ℝ) * A ≤ Real.sqrt 2 * Real.sqrt (M : ℝ) * A := by
          nlinarith
        have hsecond :
            0 ≤ (2 : ℝ) * Real.rpow (M : ℝ) (1 / (2 : ℝ)) * B := by
          exact mul_nonneg
            (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))
            hBpos.le
        nlinarith
  · let S : Ω → ℝ := fun omega => ∑ m, X m omega
    let W : ENNReal :=
      ((r : ENNReal) ^ (1 / 2 : ℝ) * (M : ENNReal) ^ (1 / 2 : ℝ) *
            ENNReal.ofReal A) +
        (r : ENNReal) * (M : ENNReal) ^ (1 / (r : ℝ)) * ENNReal.ofReal B
    have hrpos : (0 : ℝ) < (r : ℝ) := by positivity
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have hSMem : MeasureTheory.MemLp S (r : ENNReal) mu := by
      dsimp [S]
      apply MeasureTheory.memLp_finsetSum Finset.univ
      intro m hm
      refine ⟨(hMeas m).aestronglyMeasurable, lt_of_le_of_lt (hB m) ?_⟩
      exact ENNReal.ofReal_lt_top
    have hMomentBound :
        ‖∫ omega, S omega ^ r ∂mu‖ₑ ≤ ((8 : ENNReal) * W) ^ (r : ℝ) := by
      calc
        ‖∫ omega, S omega ^ r ∂mu‖ₑ ≤
            (8 : ENNReal) ^ r * W ^ (r : ℝ) := by
          exact independent_centered_even_moment_integral_bound mu X A B r hIndep
            hMeas hCenter hApos hBpos hA hB hrgt
        _ = ((8 : ENNReal) * W) ^ (r : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
          conv_rhs => lhs; rw [ENNReal.rpow_natCast]
    have hRoot :
        MeasureTheory.eLpNorm S (r : ENNReal) mu ≤ (8 : ENNReal) * W :=
      independent_centered_even_moment_root mu S r ((8 : ENNReal) * W) hSMem
        (by omega) hEven hMomentBound
    have hRroot :
        (r : ENNReal) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt (r : ℝ)) := by
      rw [show (r : ENNReal) = ENNReal.ofReal (r : ℝ) by simp,
        ENNReal.ofReal_rpow_of_pos hrpos, ← Real.sqrt_eq_rpow]
    have hMroot :
        (M : ENNReal) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt (M : ℝ)) := by
      rw [show (M : ENNReal) = ENNReal.ofReal (M : ℝ) by simp,
        ENNReal.ofReal_rpow_of_pos hMpos, ← Real.sqrt_eq_rpow]
    have hMrpow :
        (M : ENNReal) ^ (1 / (r : ℝ)) =
          ENNReal.ofReal (Real.rpow (M : ℝ) (1 / (r : ℝ))) := by
      calc
        (M : ENNReal) ^ (1 / (r : ℝ)) =
            ENNReal.ofReal (M : ℝ) ^ (1 / (r : ℝ)) := by simp
        _ = ENNReal.ofReal ((M : ℝ) ^ (1 / (r : ℝ))) :=
          ENNReal.ofReal_rpow_of_pos hMpos
        _ = ENNReal.ofReal (Real.rpow (M : ℝ) (1 / (r : ℝ))) := by rfl
    have htermA :
        0 ≤ Real.sqrt (r : ℝ) * Real.sqrt (M : ℝ) * A := by positivity
    have htermB :
        0 ≤ (r : ℝ) * Real.rpow (M : ℝ) (1 / (r : ℝ)) * B := by
      exact mul_nonneg
        (mul_nonneg hrpos.le (Real.rpow_nonneg hMpos.le _)) hBpos.le
    have hOfTermA :
        ENNReal.ofReal
            (Real.sqrt (r : ℝ) * Real.sqrt (M : ℝ) * A) =
          ENNReal.ofReal (Real.sqrt (r : ℝ)) *
            ENNReal.ofReal (Real.sqrt (M : ℝ)) * ENNReal.ofReal A := by
      rw [ENNReal.ofReal_mul
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
        ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    have hOfTermB :
        ENNReal.ofReal
            ((r : ℝ) * Real.rpow (M : ℝ) (1 / (r : ℝ)) * B) =
          ENNReal.ofReal (r : ℝ) *
            ENNReal.ofReal (Real.rpow (M : ℝ) (1 / (r : ℝ))) *
              ENNReal.ofReal B := by
      have hpref :
          0 ≤ (r : ℝ) * Real.rpow (M : ℝ) (1 / (r : ℝ)) :=
        mul_nonneg hrpos.le (Real.rpow_pos_of_pos hMpos _).le
      calc
        ENNReal.ofReal
            ((r : ℝ) * Real.rpow (M : ℝ) (1 / (r : ℝ)) * B) =
          ENNReal.ofReal
              ((r : ℝ) * Real.rpow (M : ℝ) (1 / (r : ℝ))) *
            ENNReal.ofReal B := ENNReal.ofReal_mul hpref
        _ = ENNReal.ofReal (r : ℝ) *
              ENNReal.ofReal (Real.rpow (M : ℝ) (1 / (r : ℝ))) *
                ENNReal.ofReal B := by
          rw [ENNReal.ofReal_mul hrpos.le]
    have hWeq :
        W = ENNReal.ofReal
            (Real.sqrt (r : ℝ) * Real.sqrt (M : ℝ) * A) +
          ENNReal.ofReal
            ((r : ℝ) * Real.rpow (M : ℝ) (1 / (r : ℝ)) * B) := by
      rw [hOfTermA, hOfTermB]
      dsimp [W]
      rw [hRroot, hMroot, hMrpow]
      simp
    calc
      MeasureTheory.eLpNorm (fun omega => ∑ m, X m omega) (r : ENNReal) mu ≤
          (8 : ENNReal) * W := hRoot
      _ = ENNReal.ofReal
          (8 * (Real.sqrt (r : ℝ) * Real.sqrt (M : ℝ) * A +
            (r : ℝ) * Real.rpow (M : ℝ) (1 / (r : ℝ)) * B)) := by
        rw [hWeq, ← ENNReal.ofReal_add htermA htermB,
          show (8 : ENNReal) = ENNReal.ofReal (8 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num)]

set_option maxHeartbeats 2000000 in
@[blueprint "lem:independent-centered-quadratic-moment-average"
  (statement := /-- Let \(M\geq1\), let \((\Omega,\mathcal F,\mu)\) be a probability space, and
  let \(Z_1,\ldots,Z_M\) be independent, measurable, integrable, centered real random
  variables. Suppose that \(K>0\) and that, for every integer \(s\geq2\),
  \[
    \lVert Z_m\rVert_{L^s(\mu)}\leq Ks^2
    \qquad (1\leq m\leq M).
  \]
  Then, for every integer \(r\geq2\),
  \[
    \left\lVert\frac1M\sum_{m=1}^M Z_m\right\rVert_{L^r(\mu)}
      \leq 64K\left(\sqrt{\frac rM}
        +r^3M^{-1+1/r}\right).
  \] -/)
  (proof := /-- Suppose first that \(r\) is even. The hypotheses at \(s=2\) and \(s=r\)
  give, respectively,
  \[
    \lVert Z_m\rVert_2\leq4K
    \quad\text{and}\quad
    \lVert Z_m\rVert_r\leq Kr^2
    \qquad (1\leq m\leq M).
  \]
  Apply \cref{lem:independent-centered-even-moment-sum} with
  \(A=4K\) and \(B=Kr^2\). It gives
  \[
    \left\lVert\sum_mZ_m\right\rVert_r
      \leq32K\sqrt r\,\sqrt M+8Kr^3M^{1/r}.
  \]
  Since \(M\geq1\), homogeneity of the \(L^r\)-norm and division by \(M\) yield
  \[
    \left\lVert M^{-1}\sum_mZ_m\right\rVert_r
      \leq32K\sqrt{r/M}+8Kr^3M^{-1+1/r},
  \]
  which is bounded by the asserted right-hand side.

  It remains to consider an odd integer \(r\geq3\). Put \(q=r+1\), so that \(q\) is even
  and \(q\leq2r\). Monotonicity of \(L^p\)-norms on a probability space and the even estimate
  at exponent \(q\) yield
  \[
    \left\lVert M^{-1}\sum_mZ_m\right\rVert_r
      \leq32K\sqrt{q/M}+8Kq^3M^{-1+1/q}.
  \]
  Since \(M\geq1\), we have
  \(M^{-1+1/q}\leq M^{-1+1/r}\). Moreover,
  \(\sqrt q\leq2\sqrt r\) and \(q^3\leq8r^3\). Consequently,
  \[
    \left\lVert M^{-1}\sum_mZ_m\right\rVert_r
      \leq64K\left(\sqrt{r/M}+r^3M^{-1+1/r}\right),
  \]
  as required. -/)
  (title := /-- Moment bound for an average with quadratic moment growth -/)
  (latexEnv := "lemma")]
lemma independent_centered_quadratic_moment_average :
    ∀ {M : ℕ} {Ω : Type} [MeasurableSpace Ω]
      (mu : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure mu]
      (Z : Fin M → Ω → ℝ) (K : ℝ),
      ProbabilityTheory.iIndepFun Z mu →
      (∀ m, Measurable (Z m)) →
      (∀ m, MeasureTheory.Integrable (Z m) mu) →
      (∀ m, ∫ omega, Z m omega ∂mu = 0) →
      0 < K →
      (∀ m (s : ℕ), 2 ≤ s →
        MeasureTheory.eLpNorm (Z m) (s : ENNReal) mu ≤
          ENNReal.ofReal (K * (s : ℝ) ^ 2)) →
      ∀ r : ℕ, 2 ≤ r → 0 < M →
        MeasureTheory.eLpNorm
            (fun omega => (M : ℝ)⁻¹ * ∑ m, Z m omega) (r : ENNReal) mu ≤
          ENNReal.ofReal
            (64 * K * (Real.sqrt ((r : ℝ) / (M : ℝ)) +
              (r : ℝ) ^ 3 * Real.rpow (M : ℝ) (-1 + 1 / (r : ℝ)))) := by
  intro M Ω instMeas mu instProb Z K hIndep hMeas hInt hCenter hK hMoment r hr hM
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hMone : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hAverageMeas :
      Measurable (fun omega => (M : ℝ)⁻¹ * ∑ m, Z m omega) := by
    apply Measurable.const_mul
    exact Finset.measurable_sum _ fun m _ => hMeas m
  have hEvenEstimate (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q) :
      MeasureTheory.eLpNorm
          (fun omega => (M : ℝ)⁻¹ * ∑ m, Z m omega) (q : ENNReal) mu ≤
        ENNReal.ofReal
          (32 * K * Real.sqrt ((q : ℝ) / (M : ℝ)) +
            8 * K * (q : ℝ) ^ 3 *
              Real.rpow (M : ℝ) (-1 + 1 / (q : ℝ))) := by
    have hTwo : ∀ m,
        MeasureTheory.eLpNorm (Z m) (2 : ENNReal) mu ≤
          ENNReal.ofReal (4 * K) := by
      intro m
      have hm := hMoment m 2 (by omega)
      rw [show K * (((2 : ℕ) : ℝ) ^ 2) = 4 * K by ring] at hm
      exact hm
    have hQ : ∀ m,
        MeasureTheory.eLpNorm (Z m) (q : ENNReal) mu ≤
          ENNReal.ofReal (K * (q : ℝ) ^ 2) := by
      intro m
      exact hMoment m q hq
    have hSum := independent_centered_even_moment_sum mu Z (4 * K)
      (K * (q : ℝ) ^ 2) q hIndep hMeas hInt hCenter (by positivity)
      (by positivity) hTwo hQ hq hqEven hM
    have hScaleFun :
        (fun omega => (M : ℝ)⁻¹ * ∑ m, Z m omega) =
          (M : ℝ)⁻¹ • (fun omega => ∑ m, Z m omega) := by
      funext omega
      simp [smul_eq_mul]
    have hMinvSqrt :
        (M : ℝ)⁻¹ * Real.sqrt (M : ℝ) =
          (Real.sqrt (M : ℝ))⁻¹ := by
      field_simp [ne_of_gt hMpos, ne_of_gt (Real.sqrt_pos.2 hMpos)]
      nlinarith [Real.sq_sqrt hMpos.le]
    have hSqrtScale :
        (M : ℝ)⁻¹ * Real.sqrt (q : ℝ) * Real.sqrt (M : ℝ) =
          Real.sqrt ((q : ℝ) / (M : ℝ)) := by
      rw [Real.sqrt_div (by positivity)]
      rw [div_eq_mul_inv, ← hMinvSqrt]
      ring
    have hRpowScale :
        (M : ℝ)⁻¹ * Real.rpow (M : ℝ) (1 / (q : ℝ)) =
          Real.rpow (M : ℝ) (-1 + 1 / (q : ℝ)) := by
      calc
        (M : ℝ)⁻¹ * Real.rpow (M : ℝ) (1 / (q : ℝ)) =
            Real.rpow (M : ℝ) (-1 : ℝ) *
              Real.rpow (M : ℝ) (1 / (q : ℝ)) := by
          exact congrArg
            (fun x : ℝ => x * Real.rpow (M : ℝ) (1 / (q : ℝ)))
            (Real.rpow_neg_one (M : ℝ)).symm
        _ = Real.rpow (M : ℝ) ((-1 : ℝ) + 1 / (q : ℝ)) :=
          (Real.rpow_add hMpos _ _).symm
        _ = Real.rpow (M : ℝ) (-1 + 1 / (q : ℝ)) := by ring
    calc
      MeasureTheory.eLpNorm
          (fun omega => (M : ℝ)⁻¹ * ∑ m, Z m omega) (q : ENNReal) mu =
          ‖(M : ℝ)⁻¹‖ₑ *
            MeasureTheory.eLpNorm (fun omega => ∑ m, Z m omega)
              (q : ENNReal) mu := by
        rw [hScaleFun]
        exact MeasureTheory.eLpNorm_const_smul (M : ℝ)⁻¹
          (fun omega => ∑ m, Z m omega) (q : ENNReal) mu
      _ ≤ ENNReal.ofReal ((M : ℝ)⁻¹) *
          ENNReal.ofReal
            (8 * (Real.sqrt (q : ℝ) * Real.sqrt (M : ℝ) * (4 * K) +
              (q : ℝ) * Real.rpow (M : ℝ) (1 / (q : ℝ)) *
                (K * (q : ℝ) ^ 2))) := by
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hMpos)]
        exact mul_le_mul_left' hSum _
      _ = ENNReal.ofReal
          ((M : ℝ)⁻¹ *
            (8 * (Real.sqrt (q : ℝ) * Real.sqrt (M : ℝ) * (4 * K) +
              (q : ℝ) * Real.rpow (M : ℝ) (1 / (q : ℝ)) *
                (K * (q : ℝ) ^ 2)))) := by
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr hMpos.le)]
      _ = ENNReal.ofReal
          (32 * K * Real.sqrt ((q : ℝ) / (M : ℝ)) +
            8 * K * (q : ℝ) ^ 3 *
              Real.rpow (M : ℝ) (-1 + 1 / (q : ℝ))) := by
        congr 1
        rw [← hSqrtScale, ← hRpowScale]
        ring
  by_cases hEven : Even r
  · calc
      MeasureTheory.eLpNorm
          (fun omega => (M : ℝ)⁻¹ * ∑ m, Z m omega) (r : ENNReal) mu ≤
          ENNReal.ofReal
            (32 * K * Real.sqrt ((r : ℝ) / (M : ℝ)) +
              8 * K * (r : ℝ) ^ 3 *
                Real.rpow (M : ℝ) (-1 + 1 / (r : ℝ))) :=
        hEvenEstimate r hr hEven
      _ ≤ ENNReal.ofReal
          (64 * K * (Real.sqrt ((r : ℝ) / (M : ℝ)) +
            (r : ℝ) ^ 3 *
              Real.rpow (M : ℝ) (-1 + 1 / (r : ℝ)))) := by
        apply ENNReal.ofReal_le_ofReal
        have hFirstNonneg :
            0 ≤ K * Real.sqrt ((r : ℝ) / (M : ℝ)) := by positivity
        have hSecondNonneg :
            0 ≤ K * (r : ℝ) ^ 3 *
              Real.rpow (M : ℝ) (-1 + 1 / (r : ℝ)) := by
          exact mul_nonneg (mul_nonneg hK.le (pow_nonneg (by positivity) _))
            (Real.rpow_nonneg hMpos.le _)
        nlinarith
  · have hSuccEven : Even (r + 1) :=
      (Nat.not_even_iff_odd.mp hEven).add_one
    have hRq : (r : ENNReal) ≤ ((r + 1 : ℕ) : ENNReal) := by norm_cast; omega
    have hMono :
        MeasureTheory.eLpNorm
            (fun omega => (M : ℝ)⁻¹ * ∑ m, Z m omega) (r : ENNReal) mu ≤
          MeasureTheory.eLpNorm
            (fun omega => (M : ℝ)⁻¹ * ∑ m, Z m omega)
              ((r + 1 : ℕ) : ENNReal) mu :=
      MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le hRq
        hAverageMeas.aestronglyMeasurable
    have hSucc := hEvenEstimate (r + 1) (by omega) hSuccEven
    have hqTwoR : ((r + 1 : ℕ) : ℝ) ≤ 2 * (r : ℝ) := by
      exact_mod_cast (show r + 1 ≤ 2 * r by omega)
    have hArg :
        ((r + 1 : ℕ) : ℝ) / (M : ℝ) ≤
          4 * ((r : ℝ) / (M : ℝ)) := by
      calc
        ((r + 1 : ℕ) : ℝ) / (M : ℝ) ≤
            (4 * (r : ℝ)) / (M : ℝ) := by gcongr; linarith
        _ = 4 * ((r : ℝ) / (M : ℝ)) := by ring
    have hSqrt :
        Real.sqrt (((r + 1 : ℕ) : ℝ) / (M : ℝ)) ≤
          2 * Real.sqrt ((r : ℝ) / (M : ℝ)) := by
      have hqNonneg : 0 ≤ ((r + 1 : ℕ) : ℝ) / (M : ℝ) := by positivity
      have hrNonneg : 0 ≤ (r : ℝ) / (M : ℝ) := by positivity
      nlinarith [Real.sq_sqrt hqNonneg, Real.sq_sqrt hrNonneg,
        Real.sqrt_nonneg (((r + 1 : ℕ) : ℝ) / (M : ℝ)),
        Real.sqrt_nonneg ((r : ℝ) / (M : ℝ))]
    have hCube : ((r + 1 : ℕ) : ℝ) ^ 3 ≤ 8 * (r : ℝ) ^ 3 := by
      calc
        ((r + 1 : ℕ) : ℝ) ^ 3 ≤ (2 * (r : ℝ)) ^ 3 := by gcongr
        _ = 8 * (r : ℝ) ^ 3 := by ring
    have hInv : 1 / ((r + 1 : ℕ) : ℝ) ≤ 1 / (r : ℝ) := by
      apply (one_div_le_one_div (by positivity) (by positivity)).2
      norm_num
    have hRpow :
        Real.rpow (M : ℝ) (-1 + 1 / ((r + 1 : ℕ) : ℝ)) ≤
          Real.rpow (M : ℝ) (-1 + 1 / (r : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hMone (by linarith)
    have hSecond :
        ((r + 1 : ℕ) : ℝ) ^ 3 *
            Real.rpow (M : ℝ) (-1 + 1 / ((r + 1 : ℕ) : ℝ)) ≤
          8 * (r : ℝ) ^ 3 *
            Real.rpow (M : ℝ) (-1 + 1 / (r : ℝ)) := by
      calc
        ((r + 1 : ℕ) : ℝ) ^ 3 *
            Real.rpow (M : ℝ) (-1 + 1 / ((r + 1 : ℕ) : ℝ)) ≤
            (8 * (r : ℝ) ^ 3) *
              Real.rpow (M : ℝ) (-1 + 1 / ((r + 1 : ℕ) : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hCube (Real.rpow_nonneg hMpos.le _)
        _ ≤ (8 * (r : ℝ) ^ 3) *
            Real.rpow (M : ℝ) (-1 + 1 / (r : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hRpow (by positivity)
    calc
      MeasureTheory.eLpNorm
          (fun omega => (M : ℝ)⁻¹ * ∑ m, Z m omega) (r : ENNReal) mu ≤
          MeasureTheory.eLpNorm
            (fun omega => (M : ℝ)⁻¹ * ∑ m, Z m omega)
              ((r + 1 : ℕ) : ENNReal) mu := hMono
      _ ≤ ENNReal.ofReal
          (32 * K * Real.sqrt (((r + 1 : ℕ) : ℝ) / (M : ℝ)) +
            8 * K * ((r + 1 : ℕ) : ℝ) ^ 3 *
              Real.rpow (M : ℝ) (-1 + 1 / ((r + 1 : ℕ) : ℝ))) := hSucc
      _ ≤ ENNReal.ofReal
          (64 * K * (Real.sqrt ((r : ℝ) / (M : ℝ)) +
            (r : ℝ) ^ 3 *
              Real.rpow (M : ℝ) (-1 + 1 / (r : ℝ)))) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith

@[blueprint "lem:polynomial-score-feature-moment"
  (statement := /-- Let \(n,d,C_t\in\mathbb N\), let \(k\in\mathbb R\), and let \(p\) be a
  probability measure on \(\mathbb R^n\) satisfying \cref{def:tail-decay-condition} with
  parameters \((d,k,C_t)\). Let \(Y:\mathbb R^n\to\mathbb R\) be measurable, let \(H>0\),
  and suppose that
  \[
    |Y(x)|\leq H\left\{1+
      \left(\frac{\lVert x\rVert_\infty}{C_t}\right)^{2(d-1)}\right\}
    \quad\text{for every }x.
  \]
  Then \(Y\) is integrable and, for every integer \(r\geq2\),
  \[
    \lVert Y-\mathbb EY\rVert_{L^r(p)}\leq64Hr^2.
  \] -/)
  (proof := /-- Put
  \(S(x)=(\lVert x\rVert_\infty/C_t)^{d-1}\). The lower bound on \(C_t\) in
  \cref{def:tail-decay-condition} implies
  \(kC_t^{d-1}\geq\log 2\). If \(t>1\), apply the tail condition at
  \(C_t t^{1/(d-1)}\). Since \(\log 2\geq1/2\), this gives
  \[
    p\{S>t\}\leq \exp(-(\log 2)t)\leq e^{-t/2}.                       \tag{1}
  \]
  For every integer \(q\geq4\), the layer-cake identity, split over
  \((0,1]\) and \((1,\infty)\), therefore yields
  \[
    \mathbb E S^q
      \leq q\left(1+\int_0^\infty t^{q-1}e^{-t/2}\,dt\right)
      =q\left(1+2^q(q-1)!\right).
  \]
  Using \(q!\leq q^q\), \(q\leq\frac12(2q)^q\), and
  \(\frac32\leq(9/8)^q\), we obtain
  \[
    \mathbb E S^q\leq\left(\frac94q\right)^q,
    \qquad \lVert S\rVert_q\leq\frac94q.                              \tag{2}
  \]
  Taking \(q=2r\), the power rule for \(L^r\)-norms and the assumed envelope give
  \[
    \lVert Y\rVert_r
      \leq H\bigl(1+\lVert S\rVert_{2r}^2\bigr)
      \leq H\left(1+\frac{81}{4}r^2\right)
      \leq\frac{41}{2}Hr^2.                                         \tag{3}
  \]
  The case \(r=2\) proves that \(Y\) is integrable. Since \(p\) is a probability measure,
  the \(L^1\)-to-\(L^r\) monotonicity and the integral triangle inequality imply
  \(\lvert\mathbb EY\rvert\leq\lVert Y\rVert_r\). Minkowski's inequality and (3) now give
  \[
    \lVert Y-\mathbb EY\rVert_r
      \leq2\lVert Y\rVert_r
      \leq41Hr^2
      \leq64Hr^2,
  \]
  as required. -/)
  (title := /-- Explicit centered moments of polynomial score features -/)
  (latexEnv := "lemma")]
lemma polynomial_score_feature_moment :
    ∀ {n : ℕ} (d : ℕ) (tailRate : ℝ) (Ct : ℕ)
      (p : MeasureTheory.Measure (Fin n → ℝ)) [MeasureTheory.IsProbabilityMeasure p]
      (Y : (Fin n → ℝ) → ℝ) (H : ℝ),
      tail_decay_condition d tailRate Ct p →
      0 < H →
      Measurable Y →
      (∀ x, |Y x| ≤
        H * (1 + (‖x‖ / (Ct : ℝ)) ^ (2 * (d - 1)))) →
      MeasureTheory.Integrable Y p ∧
        ∀ r : ℕ, 2 ≤ r →
          MeasureTheory.eLpNorm (fun x => Y x - ∫ y, Y y ∂p)
              (r : ENNReal) p ≤
            ENNReal.ofReal (64 * H * (r : ℝ) ^ 2) := by
  intro n d tailRate Ct p inst Y H htail hH hY hbound
  rcases htail with ⟨hRate, hd, hCt, hCtUpper, htail⟩
  have hdreal : 0 < (d : ℝ) - 1 := by
    have hdreal' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hdsub : (d : ℝ) - 1 = ((d - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hmne : d - 1 ≠ 0 := by omega
  have hCtOne : 1 ≤ (Ct : ℝ) := le_trans (le_max_right _ _) hCt
  have hCtPos : 0 < (Ct : ℝ) := lt_of_lt_of_le zero_lt_one hCtOne
  have hlogPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hroot :
      Real.rpow (Real.log 2 / tailRate) (1 / ((d : ℝ) - 1)) ≤ (Ct : ℝ) :=
    le_trans (le_max_left _ _) hCt
  have hratioNonneg : 0 ≤ Real.log 2 / tailRate :=
    div_nonneg hlogPos.le hRate.le
  have hcoef : Real.log 2 ≤ tailRate * (Ct : ℝ) ^ (d - 1) := by
    have hp := Real.rpow_le_rpow
      (Real.rpow_nonneg hratioNonneg _) hroot hdreal.le
    have hmul : (1 / ((d : ℝ) - 1)) * ((d : ℝ) - 1) = 1 := by
      field_simp
    rw [← Real.rpow_mul hratioNonneg, hmul, Real.rpow_one, hdsub,
      Real.rpow_natCast] at hp
    calc
      Real.log 2 = tailRate * (Real.log 2 / tailRate) := by
        field_simp [ne_of_gt hRate]
      _ ≤ tailRate * (Ct : ℝ) ^ (d - 1) :=
        mul_le_mul_of_nonneg_left hp hRate.le
  let V : (Fin n → ℝ) → ℝ := fun x => (‖x‖ / (Ct : ℝ)) ^ (d - 1)
  have hVNonneg : ∀ x, 0 ≤ V x := by
    intro x
    exact pow_nonneg (div_nonneg (norm_nonneg _) hCtPos.le) _
  have hVMeas : Measurable V := by
    dsimp [V]
    fun_prop
  have htailV : ∀ t : ℝ, 1 < t →
      p {x | t < V x} ≤ ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ) * t)) := by
    intro t ht
    let root : ℝ := Real.rpow t (1 / ((d : ℝ) - 1))
    let s : ℝ := (Ct : ℝ) * root
    have hrootNonneg : 0 ≤ root := Real.rpow_nonneg (le_trans zero_le_one ht.le) _
    have hrootOne : 1 < root :=
      Real.one_lt_rpow ht (one_div_pos.mpr hdreal)
    have hrootpow : root ^ (d - 1) = t := by
      dsimp [root]
      have hmul' : (1 / ((d : ℝ) - 1)) * ((d : ℝ) - 1) = 1 := by
        field_simp
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_trans zero_le_one ht.le),
        ← hdsub, hmul', Real.rpow_one]
    have hsCt : (Ct : ℝ) ≤ s := by
      dsimp [s]
      exact le_mul_of_one_le_right hCtPos.le hrootOne.le
    have hsubset : {x | t < V x} ⊆ {x | s < ‖x‖} := by
      intro x hx
      have hbaseNonneg : 0 ≤ ‖x‖ / (Ct : ℝ) :=
        div_nonneg (norm_nonneg _) hCtPos.le
      have hrootlt : root < ‖x‖ / (Ct : ℝ) := by
        apply (pow_lt_pow_iff_left₀ hrootNonneg hbaseNonneg hmne).mp
        rw [hrootpow]
        exact hx
      dsimp [s]
      nlinarith [(lt_div_iff₀ hCtPos).mp hrootlt]
    have hsPow : s ^ (d - 1) = (Ct : ℝ) ^ (d - 1) * t := by
      dsimp [s]
      rw [mul_pow, hrootpow]
    have hlogHalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    have hExpArg :
        -tailRate * s ^ (d - 1) ≤ -(1 / 2 : ℝ) * t := by
      rw [hsPow]
      have hc := mul_le_mul_of_nonneg_right hcoef (le_trans zero_le_one ht.le)
      nlinarith
    calc
      p {x | t < V x} ≤ p {x | s < ‖x‖} := MeasureTheory.measure_mono hsubset
      _ = ENNReal.ofReal (p.real {x | s < ‖x‖}) :=
        (MeasureTheory.ofReal_measureReal).symm
      _ ≤ ENNReal.ofReal (Real.exp (-tailRate * s ^ (d - 1))) :=
        ENNReal.ofReal_le_ofReal (htail s hsCt)
      _ ≤ ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ) * t)) :=
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hExpArg)
  have hMoment : ∀ q : ℕ, 4 ≤ q →
      ∫⁻ x, ENNReal.ofReal ((V x) ^ (q : ℝ)) ∂p ≤
        ENNReal.ofReal (((9 / 4 : ℝ) * (q : ℝ)) ^ q) := by
    intro q hq
    let F : ℝ → ENNReal := fun t =>
      p {x | t < V x} * ENNReal.ofReal (t ^ ((q : ℝ) - 1))
    have hqPos : (0 : ℝ) < (q : ℝ) := by positivity
    have hsmall : ∫⁻ t in Set.Ioc (0 : ℝ) 1, F t ≤ 1 := by
      calc
        ∫⁻ t in Set.Ioc (0 : ℝ) 1, F t ≤
            ∫⁻ _t in Set.Ioc (0 : ℝ) 1, (1 : ENNReal) := by
          apply MeasureTheory.setLIntegral_mono' measurableSet_Ioc
          intro t ht
          have hmeasure : p {x | t < V x} ≤ 1 := by
            calc
              p {x | t < V x} ≤ p Set.univ :=
                MeasureTheory.measure_mono (Set.subset_univ _)
              _ = 1 := MeasureTheory.measure_univ
          have hrpow : t ^ ((q : ℝ) - 1) ≤ 1 :=
            Real.rpow_le_one ht.1.le ht.2 (by
              have hqReal : (1 : ℝ) ≤ (q : ℝ) := by
                exact_mod_cast (show 1 ≤ q by omega)
              linarith)
          dsimp [F]
          calc
            p {x | t < V x} * ENNReal.ofReal (t ^ ((q : ℝ) - 1)) ≤
                1 * ENNReal.ofReal 1 :=
              mul_le_mul hmeasure (ENNReal.ofReal_le_ofReal hrpow) (by positivity) (by positivity)
            _ = 1 := by norm_num
        _ = 1 := by simp
    have hgammaInt : MeasureTheory.IntegrableOn
        (fun t : ℝ => t ^ ((q : ℝ) - 1) * Real.exp (-((1 / 2 : ℝ) * t)))
        (Set.Ioi 0) := by
      exact .of_integral_ne_zero (by
        rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hqPos
          (by norm_num : (0 : ℝ) < 1 / 2)]
        positivity)
    have hgammaNonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
        (fun t : ℝ => t ^ ((q : ℝ) - 1) * Real.exp (-((1 / 2 : ℝ) * t))) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _)
    have hGamma : Real.Gamma (q : ℝ) = ((q - 1).factorial : ℝ) := by
      rw [show (q : ℝ) = ((q - 1 : ℕ) : ℝ) + 1 by
        norm_cast
        omega]
      exact Real.Gamma_nat_eq_factorial (q - 1)
    have hlarge : ∫⁻ t in Set.Ioi (1 : ℝ), F t ≤
        ENNReal.ofReal ((2 : ℝ) ^ q * ((q - 1).factorial : ℝ)) := by
      calc
        ∫⁻ t in Set.Ioi (1 : ℝ), F t ≤
            ∫⁻ t in Set.Ioi (1 : ℝ),
              ENNReal.ofReal
                (t ^ ((q : ℝ) - 1) * Real.exp (-((1 / 2 : ℝ) * t))) := by
          apply MeasureTheory.setLIntegral_mono' measurableSet_Ioi
          intro t ht
          have htv := htailV t ht
          have htNonneg : 0 ≤ t ^ ((q : ℝ) - 1) :=
            Real.rpow_nonneg (le_trans zero_le_one ht.le) _
          dsimp [F]
          rw [ENNReal.ofReal_mul htNonneg]
          calc
            p {x | t < V x} * ENNReal.ofReal (t ^ ((q : ℝ) - 1)) ≤
                ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ) * t)) *
                  ENNReal.ofReal (t ^ ((q : ℝ) - 1)) :=
              mul_le_mul_right' htv _
            _ = ENNReal.ofReal (t ^ ((q : ℝ) - 1)) *
                  ENNReal.ofReal (Real.exp (-((1 / 2 : ℝ) * t))) := by
              rw [mul_comm]
              congr 2
              ring_nf
        _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ),
              ENNReal.ofReal
                (t ^ ((q : ℝ) - 1) * Real.exp (-((1 / 2 : ℝ) * t))) :=
          MeasureTheory.lintegral_mono_set (by
            intro t ht
            exact lt_trans zero_lt_one (Set.mem_Ioi.mp ht))
        _ = ENNReal.ofReal
              (∫ t : ℝ in Set.Ioi (0 : ℝ),
                t ^ ((q : ℝ) - 1) * Real.exp (-((1 / 2 : ℝ) * t))) := by
          symm
          exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
            hgammaInt hgammaNonneg
        _ = ENNReal.ofReal ((2 : ℝ) ^ q * ((q - 1).factorial : ℝ)) := by
          rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hqPos
            (by norm_num : (0 : ℝ) < 1 / 2), hGamma]
          congr 2
          norm_num [Real.rpow_natCast]
    have hsplit : ∫⁻ t in Set.Ioi (0 : ℝ), F t ≤
        (∫⁻ t in Set.Ioc (0 : ℝ) 1, F t) +
          ∫⁻ t in Set.Ioi (1 : ℝ), F t := by
      rw [show Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 by
        ext t
        simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
        constructor <;> intro ht
        · by_cases h : t ≤ 1
          · exact Or.inl ⟨ht, h⟩
          · exact Or.inr (lt_of_not_ge h)
        · rcases ht with ht | ht
          · exact ht.1
          · linarith]
      exact MeasureTheory.lintegral_union_le _ _ _
    have hfact : q * (q - 1).factorial = q.factorial := by
      calc
        q * (q - 1).factorial =
            ((q - 1) + 1) * (q - 1).factorial := by
          congr 1
          omega
        _ = ((q - 1) + 1).factorial := (Nat.factorial_succ _).symm
        _ = q.factorial := by congr 1 <;> omega
    have hfacReal : (q.factorial : ℝ) ≤ (q : ℝ) ^ q := by
      exact_mod_cast Nat.factorial_le_pow q
    have htailTerm :
        (q : ℝ) * ((2 : ℝ) ^ q * ((q - 1).factorial : ℝ)) ≤
          (2 * (q : ℝ)) ^ q := by
      calc
        (q : ℝ) * ((2 : ℝ) ^ q * ((q - 1).factorial : ℝ)) =
            (2 : ℝ) ^ q * (q.factorial : ℝ) := by
          have hfactReal :
              (q : ℝ) * ((q - 1).factorial : ℝ) = (q.factorial : ℝ) := by
            exact_mod_cast hfact
          rw [show (q : ℝ) * ((2 : ℝ) ^ q * ((q - 1).factorial : ℝ)) =
            (2 : ℝ) ^ q * ((q : ℝ) * ((q - 1).factorial : ℝ)) by ring,
            hfactReal]
        _ ≤ (2 : ℝ) ^ q * (q : ℝ) ^ q :=
          mul_le_mul_of_nonneg_left hfacReal (by positivity)
        _ = (2 * (q : ℝ)) ^ q := by rw [mul_pow]
    have hqTerm : (q : ℝ) ≤
        (1 / 2 : ℝ) * (2 * (q : ℝ)) ^ q := by
      have hqReal : (4 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      have hbase : (2 : ℝ) * (q : ℝ) ≤ (2 * (q : ℝ)) ^ q := by
        simpa using pow_le_pow_right₀
          (show (1 : ℝ) ≤ 2 * (q : ℝ) by linarith) (show 1 ≤ q by omega)
      nlinarith
    have hratioPow : (3 / 2 : ℝ) ≤ (9 / 8 : ℝ) ^ q := by
      calc
        (3 / 2 : ℝ) ≤ (9 / 8 : ℝ) ^ 4 := by norm_num
        _ ≤ (9 / 8 : ℝ) ^ q :=
          pow_le_pow_right₀ (by norm_num) hq
    have hnumeric :
        (q : ℝ) * (1 + (2 : ℝ) ^ q * ((q - 1).factorial : ℝ)) ≤
          ((9 / 4 : ℝ) * (q : ℝ)) ^ q := by
      have hA : 0 ≤ (2 * (q : ℝ)) ^ q := by positivity
      calc
        (q : ℝ) * (1 + (2 : ℝ) ^ q * ((q - 1).factorial : ℝ)) =
            (q : ℝ) +
              (q : ℝ) * ((2 : ℝ) ^ q * ((q - 1).factorial : ℝ)) := by ring
        _ ≤ (1 / 2 : ℝ) * (2 * (q : ℝ)) ^ q +
              (2 * (q : ℝ)) ^ q := add_le_add hqTerm htailTerm
        _ = (3 / 2 : ℝ) * (2 * (q : ℝ)) ^ q := by ring
        _ ≤ (9 / 8 : ℝ) ^ q * (2 * (q : ℝ)) ^ q :=
          mul_le_mul_of_nonneg_right hratioPow hA
        _ = ((9 / 4 : ℝ) * (q : ℝ)) ^ q := by
          rw [← mul_pow]
          apply congrArg (fun z : ℝ => z ^ q)
          ring
    rw [MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul
      (μ := p) (f := V) (Filter.Eventually.of_forall hVNonneg)
      hVMeas.aemeasurable hqPos]
    calc
      ENNReal.ofReal (q : ℝ) * ∫⁻ t in Set.Ioi (0 : ℝ), F t ≤
          ENNReal.ofReal (q : ℝ) *
            ((∫⁻ t in Set.Ioc (0 : ℝ) 1, F t) +
              ∫⁻ t in Set.Ioi (1 : ℝ), F t) :=
        mul_le_mul_left' hsplit _
      _ ≤ ENNReal.ofReal (q : ℝ) *
            (1 + ENNReal.ofReal ((2 : ℝ) ^ q * ((q - 1).factorial : ℝ))) :=
        mul_le_mul_left' (add_le_add hsmall hlarge) _
      _ = ENNReal.ofReal
            ((q : ℝ) * (1 + (2 : ℝ) ^ q * ((q - 1).factorial : ℝ))) := by
        rw [← ENNReal.ofReal_one]
        rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
          (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ q * ((q - 1).factorial : ℝ))]
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (q : ℝ))]
      _ ≤ ENNReal.ofReal (((9 / 4 : ℝ) * (q : ℝ)) ^ q) :=
        ENNReal.ofReal_le_ofReal hnumeric
  have hLpV : ∀ q : ℕ, 4 ≤ q →
      MeasureTheory.eLpNorm V (q : ENNReal) p ≤
        ENNReal.ofReal ((9 / 4 : ℝ) * (q : ℝ)) := by
    intro q hq
    have hqPos : (0 : ℝ) < (q : ℝ) := by positivity
    have hApos : 0 < (9 / 4 : ℝ) * (q : ℝ) := by positivity
    have hInt :
        ∫⁻ x, ‖V x‖ₑ ^ ((q : ENNReal).toReal) ∂p ≤
          ENNReal.ofReal (((9 / 4 : ℝ) * (q : ℝ)) ^ q) := by
      calc
        ∫⁻ x, ‖V x‖ₑ ^ ((q : ENNReal).toReal) ∂p =
            ∫⁻ x, ENNReal.ofReal ((V x) ^ (q : ℝ)) ∂p := by
          apply MeasureTheory.lintegral_congr
          intro x
          calc
            ‖V x‖ₑ ^ ((q : ENNReal).toReal) =
                ENNReal.ofReal (V x) ^ (q : ℝ) := by
              rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hVNonneg x)]
              simp
            _ = ENNReal.ofReal ((V x) ^ (q : ℝ)) :=
              (ENNReal.ofReal_rpow_of_nonneg (hVNonneg x)
                (by positivity : (0 : ℝ) ≤ (q : ℝ)))
        _ ≤ ENNReal.ofReal (((9 / 4 : ℝ) * (q : ℝ)) ^ q) :=
          hMoment q hq
    have hqNe : (q : ENNReal) ≠ 0 := by
      norm_cast
      omega
    have hqTop : (q : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
      hqNe hqTop]
    calc
      (∫⁻ x, ‖V x‖ₑ ^ ((q : ENNReal).toReal) ∂p) ^
            (1 / (q : ENNReal).toReal) ≤
          ENNReal.ofReal (((9 / 4 : ℝ) * (q : ℝ)) ^ q) ^
            (1 / (q : ENNReal).toReal) :=
        ENNReal.rpow_le_rpow hInt (by positivity)
      _ = ENNReal.ofReal ((9 / 4 : ℝ) * (q : ℝ)) := by
        rw [show ((q : ENNReal).toReal) = (q : ℝ) by simp,
          ← Real.rpow_natCast,
          ← ENNReal.ofReal_rpow_of_pos hApos,
          ← ENNReal.rpow_mul]
        have hmulq : (q : ℝ) * (1 / (q : ℝ)) = 1 := by
          field_simp
        rw [hmulq, ENNReal.rpow_one]
  have hNormY : ∀ r : ℕ, 2 ≤ r →
      MeasureTheory.eLpNorm Y (r : ENNReal) p ≤
        ENNReal.ofReal ((41 / 2 : ℝ) * H * (r : ℝ) ^ 2) := by
    intro r hr
    have hrNe : (r : ENNReal) ≠ 0 := by
      norm_cast
      omega
    have hrTop : (r : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hrOne : (1 : ENNReal) ≤ (r : ENNReal) := by
      norm_cast
      omega
    have hpoint : ∀ x, ‖Y x‖ ≤ ‖H * (1 + (V x) ^ 2)‖ := by
      intro x
      rw [Real.norm_eq_abs, Real.norm_of_nonneg]
      · simpa [V, Nat.mul_comm 2 (d - 1), pow_mul] using hbound x
      · exact mul_nonneg hH.le (by positivity)
    have hmono :
        MeasureTheory.eLpNorm Y (r : ENNReal) p ≤
          MeasureTheory.eLpNorm (fun x => H * (1 + (V x) ^ 2))
            (r : ENNReal) p :=
      MeasureTheory.eLpNorm_mono_ae (Filter.Eventually.of_forall hpoint)
    have hconst :
        MeasureTheory.eLpNorm (fun _x : Fin n → ℝ => (1 : ℝ))
            (r : ENNReal) p = 1 := by
      rw [MeasureTheory.eLpNorm_const' (1 : ℝ) hrNe hrTop]
      simp
    have hV2 :
        MeasureTheory.eLpNorm (fun x => (V x) ^ 2) (r : ENNReal) p ≤
          ENNReal.ofReal (((9 / 2 : ℝ) * (r : ℝ)) ^ 2) := by
      have hnormfun :
          (fun x => (V x) ^ 2) = (fun x => ‖V x‖ ^ (2 : ℝ)) := by
        funext x
        rw [Real.norm_eq_abs, abs_of_nonneg (hVNonneg x),
          Real.rpow_two]
      rw [hnormfun, MeasureTheory.eLpNorm_norm_rpow V
        (p := (r : ENNReal)) (q := (2 : ℝ)) (by norm_num)]
      have hindex :
          (r : ENNReal) * ENNReal.ofReal (2 : ℝ) = ((2 * r : ℕ) : ENNReal) := by
        norm_num
        ring
      rw [hindex]
      calc
        MeasureTheory.eLpNorm V ((2 * r : ℕ) : ENNReal) p ^ (2 : ℝ) ≤
            ENNReal.ofReal ((9 / 4 : ℝ) * ((2 * r : ℕ) : ℝ)) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow (hLpV (2 * r) (by omega)) (by norm_num)
        _ = ENNReal.ofReal (((9 / 2 : ℝ) * (r : ℝ)) ^ 2) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity)
            (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two]
          congr 2
          norm_num
          ring
    have hsum :
        MeasureTheory.eLpNorm (fun x => 1 + (V x) ^ 2) (r : ENNReal) p ≤
          1 + ENNReal.ofReal (((9 / 2 : ℝ) * (r : ℝ)) ^ 2) := by
      calc
        MeasureTheory.eLpNorm (fun x => 1 + (V x) ^ 2) (r : ENNReal) p ≤
            MeasureTheory.eLpNorm (fun _x : Fin n → ℝ => (1 : ℝ))
                (r : ENNReal) p +
              MeasureTheory.eLpNorm (fun x => (V x) ^ 2)
                (r : ENNReal) p := by
          change MeasureTheory.eLpNorm
              ((fun _x : Fin n → ℝ => (1 : ℝ)) + fun x => (V x) ^ 2)
                (r : ENNReal) p ≤ _
          exact MeasureTheory.eLpNorm_add_le
            (MeasureTheory.aestronglyMeasurable_const :
              MeasureTheory.AEStronglyMeasurable
                (fun _x : Fin n → ℝ => (1 : ℝ)) p)
            (hVMeas.pow_const 2).aestronglyMeasurable hrOne
        _ ≤ 1 + ENNReal.ofReal (((9 / 2 : ℝ) * (r : ℝ)) ^ 2) :=
          add_le_add (le_of_eq hconst) hV2
    calc
      MeasureTheory.eLpNorm Y (r : ENNReal) p ≤
          MeasureTheory.eLpNorm (fun x => H * (1 + (V x) ^ 2))
            (r : ENNReal) p := hmono
      _ = ‖H‖ₑ *
          MeasureTheory.eLpNorm (fun x => 1 + (V x) ^ 2)
            (r : ENNReal) p := by
        have hfun :
            (fun x => H * (1 + (V x) ^ 2)) =
              H • (fun x => 1 + (V x) ^ 2) := by
          funext x
          simp [smul_eq_mul]
        rw [hfun]
        exact MeasureTheory.eLpNorm_const_smul H
          (fun x => 1 + (V x) ^ 2) (r : ENNReal) p
      _ ≤ ENNReal.ofReal H *
          (1 + ENNReal.ofReal (((9 / 2 : ℝ) * (r : ℝ)) ^ 2)) := by
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_pos hH]
        exact mul_le_mul_left' hsum _
      _ = ENNReal.ofReal
          (H * (1 + ((9 / 2 : ℝ) * (r : ℝ)) ^ 2)) := by
        rw [← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add (by norm_num) (by positivity),
          ← ENNReal.ofReal_mul hH.le]
      _ ≤ ENNReal.ofReal ((41 / 2 : ℝ) * H * (r : ℝ) ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        have hrReal : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
        have hrSq : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
        have hh := mul_le_mul_of_nonneg_left hrSq hH.le
        have hquarter : H ≤ (1 / 4 : ℝ) * H * (r : ℝ) ^ 2 := by
          nlinarith
        calc
          H * (1 + ((9 / 2 : ℝ) * (r : ℝ)) ^ 2) =
              H + (81 / 4 : ℝ) * H * (r : ℝ) ^ 2 := by ring
          _ ≤ (1 / 4 : ℝ) * H * (r : ℝ) ^ 2 +
              (81 / 4 : ℝ) * H * (r : ℝ) ^ 2 :=
            add_le_add hquarter le_rfl
          _ = (41 / 2 : ℝ) * H * (r : ℝ) ^ 2 := by ring
  have hMemTwo : MeasureTheory.MemLp Y (2 : ENNReal) p := by
    refine ⟨hY.aestronglyMeasurable, ?_⟩
    exact lt_of_le_of_lt (hNormY 2 (by omega)) ENNReal.ofReal_lt_top
  have hIntY : MeasureTheory.Integrable Y p :=
    hMemTwo.integrable (by norm_num)
  refine ⟨hIntY, ?_⟩
  intro r hr
  have hrNe : (r : ENNReal) ≠ 0 := by
    norm_cast
    omega
  have hrTop : (r : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hrOne : (1 : ENNReal) ≤ (r : ENNReal) := by
    norm_cast
    omega
  have hmean :
      ‖∫ y, Y y ∂p‖ₑ ≤ MeasureTheory.eLpNorm Y (r : ENNReal) p := by
    calc
      ‖∫ y, Y y ∂p‖ₑ ≤ ∫⁻ y, ‖Y y‖ₑ ∂p :=
        MeasureTheory.enorm_integral_le_lintegral_enorm Y
      _ = MeasureTheory.eLpNorm Y 1 p :=
        MeasureTheory.eLpNorm_one_eq_lintegral_enorm.symm
      _ ≤ MeasureTheory.eLpNorm Y (r : ENNReal) p :=
        MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le
          hrOne hY.aestronglyMeasurable
  have hconstMean :
      MeasureTheory.eLpNorm (fun _x : Fin n → ℝ => ∫ y, Y y ∂p)
          (r : ENNReal) p = ‖∫ y, Y y ∂p‖ₑ := by
    rw [MeasureTheory.eLpNorm_const' (∫ y, Y y ∂p) hrNe hrTop]
    simp
  have hsub :
      MeasureTheory.eLpNorm
          (fun x => Y x - ∫ y, Y y ∂p) (r : ENNReal) p ≤
        MeasureTheory.eLpNorm Y (r : ENNReal) p +
          MeasureTheory.eLpNorm (fun _x : Fin n → ℝ => ∫ y, Y y ∂p)
            (r : ENNReal) p := by
    change MeasureTheory.eLpNorm
        (Y - fun _x : Fin n → ℝ => ∫ y, Y y ∂p) (r : ENNReal) p ≤ _
    exact MeasureTheory.eLpNorm_sub_le hY.aestronglyMeasurable
      MeasureTheory.aestronglyMeasurable_const hrOne
  have hYbound := hNormY r hr
  calc
    MeasureTheory.eLpNorm
        (fun x => Y x - ∫ y, Y y ∂p) (r : ENNReal) p ≤
      MeasureTheory.eLpNorm Y (r : ENNReal) p +
        MeasureTheory.eLpNorm (fun _x : Fin n → ℝ => ∫ y, Y y ∂p)
          (r : ENNReal) p := hsub
    _ = MeasureTheory.eLpNorm Y (r : ENNReal) p + ‖∫ y, Y y ∂p‖ₑ := by
      rw [hconstMean]
    _ ≤ MeasureTheory.eLpNorm Y (r : ENNReal) p +
        MeasureTheory.eLpNorm Y (r : ENNReal) p :=
      add_le_add le_rfl hmean
    _ ≤ ENNReal.ofReal ((41 / 2 : ℝ) * H * (r : ℝ) ^ 2) +
        ENNReal.ofReal ((41 / 2 : ℝ) * H * (r : ℝ) ^ 2) :=
      add_le_add hYbound hYbound
    _ = ENNReal.ofReal
        (((41 / 2 : ℝ) * H * (r : ℝ) ^ 2) +
          ((41 / 2 : ℝ) * H * (r : ℝ) ^ 2)) := by
      rw [ENNReal.ofReal_add] <;> positivity
    _ ≤ ENNReal.ofReal (64 * H * (r : ℝ) ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      have hz : 0 ≤ H * (r : ℝ) ^ 2 :=
        mul_nonneg hH.le (sq_nonneg (r : ℝ))
      nlinarith

@[blueprint "lem:uniform-score-base-growth"
  (statement := /-- If \(u\geq1+2^{-10}\), then \(u^{1024}\geq2\). -/)
  (proof := /-- Apply Bernoulli's inequality first with exponent \(16\), obtaining
  \(u^{16}\geq 65/64\). A second application with exponent \(64\) gives
  \((65/64)^{64}\geq2\). Monotonicity of nonnegative integral powers and
  \((u^{16})^{64}=u^{1024}\) yield the claim. -/)
  (title := /-- Growth above the score-scale threshold -/)
  (latexEnv := "lemma")]
lemma uniform_score_base_growth (u : ℝ) (hu : 1 + (1 / 1024 : ℝ) ≤ u) :
    (2 : ℝ) ≤ u ^ 1024 := by
  have ha : (-2 : ℝ) ≤ u - 1 := by nlinarith only [hu]
  have hbern_u := one_add_mul_le_pow ha 16
  rw [show (1 : ℝ) + (u - 1) = u by ring] at hbern_u
  have hu_sixteen : (65 / 64 : ℝ) ≤ u ^ 16 := by
    norm_num only [Nat.cast_ofNat] at hbern_u
    apply (show (65 / 64 : ℝ) ≤ 1 + 16 * (u - 1) by
      norm_num at hu ⊢
      linarith only [hu]).trans
    exact hbern_u
  have hbern_block := one_add_mul_le_pow (a := (1 / 64 : ℝ)) (by norm_num) 64
  have hblock : (2 : ℝ) ≤ (65 / 64 : ℝ) ^ 64 := by
    norm_num only [Nat.cast_ofNat] at hbern_block
    convert hbern_block using 1 <;> norm_num
  have hmono := pow_le_pow_left₀ (show (0 : ℝ) ≤ 65 / 64 by norm_num) hu_sixteen 64
  calc
    (2 : ℝ) ≤ (65 / 64 : ℝ) ^ 64 := hblock
    _ ≤ (u ^ 16) ^ 64 := hmono
    _ = u ^ 1024 := by rw [← pow_mul]

@[blueprint "lem:uniform-score-power-absorption"
  (statement := /-- Let \(d,w\in\mathbb N\) with \(d\geq2\) and \(w\geq1\), and let
  \(u,H\in\mathbb R\) satisfy \(u\geq1+2^{-10}\) and
  \(0<H\leq8(1+du+u^2)\). Then
  \[
    8192eH\bigl(8d+32768d^6e^{d+2}\bigr)
      \leq u^{2^{30}d^2w}.
  \] -/)
  (proof := /-- By \cref{lem:uniform-score-base-growth}, \(u^{1024}\geq2\).
  The exponent \(2^{30}d^2w\) is at least
  \(2+1024(10d+100)\), so the right-hand side is at least
  \(u^2 2^{10d+100}\). Bernoulli's inequality gives the cited base-growth
  estimate. Moreover, \(H\leq24du^2\), \(e<3\),
  \(e^{d+2}\leq2^{2d+4}\), and \(d^7\leq2^{7d}\). These inequalities bound
  the left-hand side by \(u^2 2^{9d+40}\), which is no larger than
  \(u^2 2^{10d+100}\). -/)
  (title := /-- Absorption by the uniform score power -/)
  (latexEnv := "lemma")]
lemma uniform_score_power_absorption (d w : ℕ) (u H : ℝ)
    (hd : 2 ≤ d) (hw : 0 < w) (hu : 1 + (1 / 1024 : ℝ) ≤ u)
    (hHpos : 0 < H) (hH : H ≤ 8 * (1 + (d : ℝ) * u + u ^ 2)) :
    8192 * Real.exp 1 * H *
        (8 * (d : ℝ) + 32768 * (d : ℝ) ^ 6 * Real.exp ((d : ℝ) + 2)) ≤
      u ^ (2 ^ 30 * d ^ 2 * w) := by
  have hu_one : (1 : ℝ) ≤ u := by norm_num at hu ⊢; linarith
  have hd_one : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hu_block := uniform_score_base_growth u hu
  have hd_dsqw : d ≤ d ^ 2 * w := by
    have hd_sq : d ≤ d ^ 2 := by
      rw [pow_two]
      calc
        d = d * 1 := by omega
        _ ≤ d * d := Nat.mul_le_mul_left d (by omega)
    calc
      d ≤ d ^ 2 := hd_sq
      _ = d ^ 2 * 1 := by omega
      _ ≤ d ^ 2 * w := Nat.mul_le_mul_left _ (by omega)
  have hK : 2 + 1024 * (10 * d + 100) ≤ 2 ^ 30 * d ^ 2 * w := by
    have hlarge : 2 + 1024 * (10 * d + 100) ≤ 2 ^ 30 * d := by omega
    apply hlarge.trans
    calc
      2 ^ 30 * d ≤ 2 ^ 30 * (d ^ 2 * w) := Nat.mul_le_mul_left _ hd_dsqw
      _ = 2 ^ 30 * d ^ 2 * w := by rw [Nat.mul_assoc]
  have hlarge_power : u ^ 2 * (2 : ℝ) ^ (10 * d + 100) ≤
      u ^ (2 ^ 30 * d ^ 2 * w) := by
    have hblock_pow := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 by norm_num)
      hu_block (10 * d + 100)
    have hfactor : u ^ 2 * (2 : ℝ) ^ (10 * d + 100) ≤
        u ^ 2 * (u ^ 1024) ^ (10 * d + 100) :=
      mul_le_mul_of_nonneg_left hblock_pow (by positivity)
    apply hfactor.trans
    calc
      u ^ 2 * (u ^ 1024) ^ (10 * d + 100) =
          u ^ (2 + 1024 * (10 * d + 100)) := by rw [← pow_mul, ← pow_add]
      _ ≤ u ^ (2 ^ 30 * d ^ 2 * w) := pow_le_pow_right₀ hu_one hK
  have hu_le_sq : u ≤ u ^ 2 := by
    rw [pow_two]
    calc
      u = u * 1 := by ring
      _ ≤ u * u := mul_le_mul_of_nonneg_left hu_one (by positivity)
  have hone_du_sq : (1 : ℝ) ≤ d * u ^ 2 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (d : ℝ) * u ^ 2 := mul_le_mul hd_one (one_le_pow₀ hu_one) (by positivity) (by norm_num)
  have hdu_sq : (d : ℝ) * u ≤ d * u ^ 2 :=
    mul_le_mul_of_nonneg_left hu_le_sq (by positivity)
  have hu_sq_du_sq : u ^ 2 ≤ (d : ℝ) * u ^ 2 := by
    calc
      u ^ 2 = 1 * u ^ 2 := by ring
      _ ≤ (d : ℝ) * u ^ 2 := mul_le_mul_of_nonneg_right hd_one (by positivity)
  have hH_coarse : H ≤ 24 * (d : ℝ) * u ^ 2 := by
    apply hH.trans
    calc
      8 * (1 + (d : ℝ) * u + u ^ 2) ≤
          8 * ((d : ℝ) * u ^ 2 + d * u ^ 2 + d * u ^ 2) := by
        gcongr
      _ = 24 * (d : ℝ) * u ^ 2 := by ring
  have hexp_one : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have hexp_d : Real.exp ((d : ℝ) + 2) ≤ (2 : ℝ) ^ (2 * (d + 2)) := by
    calc
      Real.exp ((d : ℝ) + 2) = Real.exp 1 ^ (d + 2) := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ ≤ (3 : ℝ) ^ (d + 2) := pow_le_pow_left₀ (by positivity) hexp_one _
      _ ≤ (4 : ℝ) ^ (d + 2) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = (2 : ℝ) ^ (2 * (d + 2)) := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hd_six : (d : ℝ) ≤ d ^ 6 := by
    simpa only [pow_one] using pow_le_pow_right₀ hd_one (show 1 ≤ 6 by norm_num)
  have hC : 8 * (d : ℝ) + 32768 * (d : ℝ) ^ 6 * Real.exp ((d : ℝ) + 2) ≤
      65536 * (d : ℝ) ^ 6 * Real.exp ((d : ℝ) + 2) := by
    have hfirst : 8 * (d : ℝ) ≤ 8 * d ^ 6 * Real.exp ((d : ℝ) + 2) := by
      calc
        8 * (d : ℝ) ≤ 8 * d ^ 6 := mul_le_mul_of_nonneg_left hd_six (by norm_num)
        _ = 8 * d ^ 6 * 1 := by ring
        _ ≤ 8 * d ^ 6 * Real.exp ((d : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left (Real.one_le_exp (by positivity)) (by positivity)
    calc
      8 * (d : ℝ) + 32768 * d ^ 6 * Real.exp ((d : ℝ) + 2) ≤
          8 * d ^ 6 * Real.exp ((d : ℝ) + 2) +
            32768 * d ^ 6 * Real.exp ((d : ℝ) + 2) := add_le_add hfirst le_rfl
      _ ≤ 65536 * d ^ 6 * Real.exp ((d : ℝ) + 2) := by
        nlinarith only [mul_nonneg (show (0 : ℝ) ≤ d ^ 6 by positivity)
          (show (0 : ℝ) ≤ Real.exp ((d : ℝ) + 2) by positivity)]
  have hd_two : (d : ℝ) ≤ (2 : ℝ) ^ d := by
    exact_mod_cast (Nat.lt_two_pow_self (n := d)).le
  have hd_seven : (d : ℝ) ^ 7 ≤ (2 : ℝ) ^ (7 * d) := by
    calc
      (d : ℝ) ^ 7 ≤ ((2 : ℝ) ^ d) ^ 7 :=
        pow_le_pow_left₀ (by positivity) hd_two 7
      _ = (2 : ℝ) ^ (7 * d) := by rw [← pow_mul]; congr 1 <;> omega
  have hraw : 8192 * Real.exp 1 * H *
        (8 * (d : ℝ) + 32768 * d ^ 6 * Real.exp ((d : ℝ) + 2)) ≤
      (2 : ℝ) ^ 36 * u ^ 2 * d ^ 7 * Real.exp ((d : ℝ) + 2) := by
    calc
      8192 * Real.exp 1 * H *
          (8 * (d : ℝ) + 32768 * d ^ 6 * Real.exp ((d : ℝ) + 2)) ≤
        8192 * 3 * (24 * d * u ^ 2) *
          (65536 * d ^ 6 * Real.exp ((d : ℝ) + 2)) := by
            gcongr
      _ ≤ (2 : ℝ) ^ 36 * u ^ 2 * d ^ 7 * Real.exp ((d : ℝ) + 2) := by
        norm_num only [Nat.reducePow]
        have hnonneg : 0 ≤ u ^ 2 * d ^ 7 * Real.exp ((d : ℝ) + 2) := by positivity
        nlinarith only [hnonneg]
  have hfinal_power : (2 : ℝ) ^ 36 * u ^ 2 * d ^ 7 * Real.exp ((d : ℝ) + 2) ≤
      u ^ 2 * (2 : ℝ) ^ (10 * d + 100) := by
    have hde : (d : ℝ) ^ 7 * Real.exp ((d : ℝ) + 2) ≤
        (2 : ℝ) ^ (7 * d) * (2 : ℝ) ^ (2 * (d + 2)) :=
      mul_le_mul hd_seven hexp_d (by positivity) (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hde
      (show (0 : ℝ) ≤ (2 : ℝ) ^ 36 * u ^ 2 by positivity)
    calc
      (2 : ℝ) ^ 36 * u ^ 2 * d ^ 7 * Real.exp ((d : ℝ) + 2) ≤
          (2 : ℝ) ^ 36 * u ^ 2 * ((2 : ℝ) ^ (7 * d) * (2 : ℝ) ^ (2 * (d + 2))) := by
        nlinarith only [hmul]
      _ = u ^ 2 * ((2 : ℝ) ^ 36 * ((2 : ℝ) ^ (7 * d) * (2 : ℝ) ^ (2 * (d + 2)))) := by ring
      _ = u ^ 2 * (2 : ℝ) ^ (36 + (7 * d + 2 * (d + 2))) := by
        rw [← pow_add, ← pow_add]
      _ = u ^ 2 * (2 : ℝ) ^ (9 * d + 40) := by congr 2 <;> omega
      _ ≤ u ^ 2 * (2 : ℝ) ^ (10 * d + 100) := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) (by omega)) (by positivity)
  exact hraw.trans (hfinal_power.trans hlarge_power)

@[blueprint "lem:uniform-score-cutoff-bound"
  (statement := /-- Under the admissibility hypotheses on
  \(n,d,C_t,q,\rho\), let
  \(r=\max\{2,\lceil\log(8q\rho nC_t)\rceil\}\) and
  \(b=\rho n^{d+1}\). Then \(r\geq2\), \(b\geq1\), and
  \[
    r\leq32d^2b,\qquad
    r^3b^{-1+1/r}\leq32768d^6e^{d+2}.
  \] -/)
  (proof := /-- The logarithm laws, the bounds on \(q\) and \(C_t\), and
  \(\log\rho\leq3\rho^{1/3}\) give
  \(r\leq16d^2(\rho^{1/3}+n)\). Cubing and using
  \((x+y)^3\leq4(x^3+y^3)\) gives
  \(r^3\leq32768d^6b\), while the linear estimate gives
  \(r\leq32d^2b\). Finally, the cutoff dominates both
  \(\log\rho\) and \(\log n\); hence
  \(\log b\leq(d+2)r\), so \(b^{1/r}\leq e^{d+2}\).
  Combining the last two inequalities proves the fractional-power estimate. -/)
  (title := /-- Bounds for the logarithmic score cutoff -/)
  (latexEnv := "lemma")]
lemma uniform_score_cutoff_bound
    (n d Ct q r : ℕ) (rho : ℝ)
    (hn : 0 < n) (hd : 2 ≤ d) (hCt : 1 ≤ Ct)
    (hCt_exp : (Ct : ℝ) ≤ Real.exp (n : ℝ))
    (hq : 0 < q) (hq_bound : q ≤ 2 * (n + d) ^ (2 * d))
    (hrho : 1 ≤ rho)
    (hr : r = max 2 ⌈Real.log (8 * (q : ℝ) * rho * (n : ℝ) * (Ct : ℝ))⌉₊) :
    2 ≤ r ∧
      1 ≤ rho * (n : ℝ) ^ (d + 1) ∧
      (r : ℝ) ≤ 32 * (d : ℝ) ^ 2 * (rho * (n : ℝ) ^ (d + 1)) ∧
      (r : ℝ) ^ 3 *
          Real.rpow (rho * (n : ℝ) ^ (d + 1)) (-1 + 1 / (r : ℝ)) ≤
        32768 * (d : ℝ) ^ 6 * Real.exp ((d : ℝ) + 2) := by
  have hn_one : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn)
  have hq_one : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq)
  have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast hn_one
  have hq_real : (1 : ℝ) ≤ q := by exact_mod_cast hq_one
  have hCt_real : (1 : ℝ) ≤ Ct := by exact_mod_cast hCt
  have hz_one : (1 : ℝ) ≤ 8 * (q : ℝ) * rho * n * Ct := by
    calc
      1 ≤ 8 * (q : ℝ) := by nlinarith
      _ = (8 * (q : ℝ)) * 1 := by ring
      _ ≤ (8 * (q : ℝ)) * rho := mul_le_mul_of_nonneg_left hrho (by positivity)
      _ = (8 * (q : ℝ) * rho) * 1 := by ring
      _ ≤ (8 * (q : ℝ) * rho) * n := mul_le_mul_of_nonneg_left hn_real (by positivity)
      _ = (8 * (q : ℝ) * rho * n) * 1 := by ring
      _ ≤ (8 * (q : ℝ) * rho * n) * Ct :=
        mul_le_mul_of_nonneg_left hCt_real (by positivity)
  have hz_pos : 0 < 8 * (q : ℝ) * rho * n * Ct := lt_of_lt_of_le zero_lt_one hz_one
  have hlog_nonneg : 0 ≤ Real.log (8 * (q : ℝ) * rho * n * Ct) :=
    Real.log_nonneg hz_one
  have hr_two : 2 ≤ r := by
    rw [hr]
    exact le_max_left _ _
  have hr_real_two : (2 : ℝ) ≤ r := by exact_mod_cast hr_two
  have hr_log_bound : (r : ℝ) < Real.log (8 * (q : ℝ) * rho * n * Ct) + 3 := by
    have hceil := Nat.ceil_lt_add_one hlog_nonneg
    have hr_nat : r ≤ 2 + ⌈Real.log (8 * (q : ℝ) * rho * n * Ct)⌉₊ := by
      rw [hr]
      omega
    have hr_cast : (r : ℝ) ≤ 2 + (⌈Real.log (8 * (q : ℝ) * rho * n * Ct)⌉₊ : ℝ) := by
      exact_mod_cast hr_nat
    linarith
  have hq_bound_real : (q : ℝ) ≤ 2 * ((n + d : ℕ) : ℝ) ^ (2 * d) := by
    exact_mod_cast hq_bound
  have hlog_q : Real.log (q : ℝ) ≤
      Real.log 2 + (2 * d : ℕ) * Real.log ((n + d : ℕ) : ℝ) := by
    calc
      Real.log (q : ℝ) ≤ Real.log (2 * (((n + d : ℕ) : ℝ) ^ (2 * d))) :=
        (Real.log_le_log_iff (by positivity) (by positivity)).2 hq_bound_real
      _ = Real.log 2 + (2 * d : ℕ) * Real.log ((n + d : ℕ) : ℝ) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have hlog_Ct : Real.log (Ct : ℝ) ≤ n := by
    calc
      Real.log (Ct : ℝ) ≤ Real.log (Real.exp (n : ℝ)) :=
        (Real.log_le_log_iff (by positivity) (Real.exp_pos _)).2 hCt_exp
      _ = n := Real.log_exp _
  have hlog_rho : Real.log rho ≤ rho ^ (1 / 3 : ℝ) / (1 / 3 : ℝ) := by
    exact Real.log_le_rpow_div (by positivity) (by norm_num)
  have hlog_n : Real.log (n : ℝ) ≤ n := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < n)
    linarith
  have hlog_nd : Real.log ((n + d : ℕ) : ℝ) ≤ n + d := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (n + d : ℕ))
    norm_num only [Nat.cast_add] at h ⊢
    linarith
  have hlog_eight : Real.log 8 ≤ 7 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
    norm_num at h ⊢
    linarith
  have hlog_expand :
      Real.log (8 * (q : ℝ) * rho * n * Ct) =
        Real.log 8 + Real.log q + Real.log rho + Real.log n + Real.log Ct := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity)]
  have hd_real : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog_two : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hlog_q_simple : Real.log (q : ℝ) ≤ 1 + 4 * (d : ℝ) ^ 2 * n := by
    have hnd : (n : ℝ) + d ≤ 2 * d * n := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hd_real) (sub_nonneg.mpr hn_real)]
    have hmul := mul_le_mul_of_nonneg_left hnd (show (0 : ℝ) ≤ 2 * d by positivity)
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hlog_q
    nlinarith [hlog_q, hlog_two, hlog_nd, hmul]
  have hlog_rho_simple : Real.log rho ≤ 3 * rho ^ (1 / 3 : ℝ) := by
    norm_num at hlog_rho ⊢
    linarith
  have hr_coarse : (r : ℝ) ≤
      16 * (d : ℝ) ^ 2 * (rho ^ (1 / 3 : ℝ) + n) := by
    have ht_one : (1 : ℝ) ≤ rho ^ (1 / 3 : ℝ) :=
      Real.one_le_rpow hrho (by norm_num)
    have hd_sq_one : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
    have hsmall : 11 + 3 * rho ^ (1 / 3 : ℝ) + 2 * n ≤
        8 * (rho ^ (1 / 3 : ℝ) + n) := by
      nlinarith
    have hscale := mul_le_mul_of_nonneg_right hsmall (show (0 : ℝ) ≤ d ^ 2 by positivity)
    rw [hlog_expand] at hr_log_bound
    nlinarith [hlog_eight, hlog_q_simple, hlog_rho_simple, hlog_n, hlog_Ct,
      hscale, mul_nonneg (show (0 : ℝ) ≤ d ^ 2 by positivity) (show (0 : ℝ) ≤ n by positivity),
      mul_nonneg (show (0 : ℝ) ≤ d ^ 2 by positivity)
        (show (0 : ℝ) ≤ rho ^ (1 / 3 : ℝ) by positivity)]
  let base : ℝ := rho * (n : ℝ) ^ (d + 1)
  have hbase_one : 1 ≤ base := by
    dsimp [base]
    have hn_pow_one : (1 : ℝ) ≤ (n : ℝ) ^ (d + 1) := one_le_pow₀ hn_real
    nlinarith [mul_nonneg (sub_nonneg.mpr hrho) (sub_nonneg.mpr hn_pow_one)]
  have hbase_pos : 0 < base := lt_of_lt_of_le zero_lt_one hbase_one
  have ht_cube : (rho ^ (1 / 3 : ℝ)) ^ 3 = rho := by
    rw [← Real.rpow_mul_natCast (le_of_lt (show 0 < rho by positivity))]
    norm_num
  have ht_le_rho : rho ^ (1 / 3 : ℝ) ≤ rho := by
    calc
      rho ^ (1 / 3 : ℝ) ≤ rho ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hrho (by norm_num)
      _ = rho := Real.rpow_one rho
  have hn_cube_le : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ (d + 1) := by
    exact pow_le_pow_right₀ hn_real (by omega)
  have hn_le_pow : (n : ℝ) ≤ (n : ℝ) ^ (d + 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hn_real (show 1 ≤ d + 1 by omega)
  have hsum_cube (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
      (x + y) ^ 3 ≤ 4 * (x ^ 3 + y ^ 3) := by
    nlinarith [mul_nonneg (add_nonneg hx hy) (sq_nonneg (x - y))]
  have hsum_base : (rho ^ (1 / 3 : ℝ) + n) ^ 3 ≤ 8 * base := by
    have h1 := hsum_cube (rho ^ (1 / 3 : ℝ)) (n : ℝ) (by positivity) (by positivity)
    have h2 : (rho ^ (1 / 3 : ℝ)) ^ 3 + (n : ℝ) ^ 3 ≤ 2 * base := by
      rw [ht_cube]
      have hnp := one_le_pow₀ hn_real (n := d + 1)
      have hrho_base : rho ≤ base := by
        dsimp [base]
        calc
          rho = rho * 1 := by ring
          _ ≤ rho * (n : ℝ) ^ (d + 1) := mul_le_mul_of_nonneg_left hnp (by positivity)
      have hn_cube_base : (n : ℝ) ^ 3 ≤ base := by
        apply hn_cube_le.trans
        dsimp [base]
        calc
          (n : ℝ) ^ (d + 1) = 1 * (n : ℝ) ^ (d + 1) := by ring
          _ ≤ rho * (n : ℝ) ^ (d + 1) := mul_le_mul_of_nonneg_right hrho (by positivity)
      calc
        rho + (n : ℝ) ^ 3 ≤ base + base := add_le_add hrho_base hn_cube_base
        _ = 2 * base := by ring
    calc
      (rho ^ (1 / 3 : ℝ) + n) ^ 3 ≤
          4 * ((rho ^ (1 / 3 : ℝ)) ^ 3 + (n : ℝ) ^ 3) := h1
      _ ≤ 4 * (2 * base) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 8 * base := by ring
  have hr_cube_base : (r : ℝ) ^ 3 ≤ 32768 * (d : ℝ) ^ 6 * base := by
    have hpow := pow_le_pow_left₀ (show (0 : ℝ) ≤ r by positivity) hr_coarse 3
    have hmul := mul_le_mul_of_nonneg_left hsum_base
      (show (0 : ℝ) ≤ 4096 * (d : ℝ) ^ 6 by positivity)
    calc
      (r : ℝ) ^ 3 ≤ (16 * (d : ℝ) ^ 2 * (rho ^ (1 / 3 : ℝ) + n)) ^ 3 := hpow
      _ = 4096 * (d : ℝ) ^ 6 * (rho ^ (1 / 3 : ℝ) + n) ^ 3 := by ring
      _ ≤ 4096 * (d : ℝ) ^ 6 * (8 * base) := hmul
      _ = 32768 * (d : ℝ) ^ 6 * base := by ring
  have hr_base : (r : ℝ) ≤ 32 * (d : ℝ) ^ 2 * base := by
    have hsum : rho ^ (1 / 3 : ℝ) + (n : ℝ) ≤ 2 * base := by
      have hnp := one_le_pow₀ hn_real (n := d + 1)
      have hrho_base : rho ≤ base := by
        dsimp [base]
        calc
          rho = rho * 1 := by ring
          _ ≤ rho * (n : ℝ) ^ (d + 1) := mul_le_mul_of_nonneg_left hnp (by positivity)
      have hn_base : (n : ℝ) ≤ base := by
        apply hn_le_pow.trans
        dsimp [base]
        calc
          (n : ℝ) ^ (d + 1) = 1 * (n : ℝ) ^ (d + 1) := by ring
          _ ≤ rho * (n : ℝ) ^ (d + 1) := mul_le_mul_of_nonneg_right hrho (by positivity)
      calc
        rho ^ (1 / 3 : ℝ) + (n : ℝ) ≤ base + base :=
          add_le_add (ht_le_rho.trans hrho_base) hn_base
        _ = 2 * base := by ring
    have hmul := mul_le_mul_of_nonneg_left hsum
      (show (0 : ℝ) ≤ 16 * (d : ℝ) ^ 2 by positivity)
    apply hr_coarse.trans
    calc
      16 * (d : ℝ) ^ 2 * (rho ^ (1 / 3 : ℝ) + n) ≤
          16 * (d : ℝ) ^ 2 * (2 * base) := hmul
      _ = 32 * (d : ℝ) ^ 2 * base := by ring
  have hlog_le_r : Real.log (8 * (q : ℝ) * rho * n * Ct) ≤ r := by
    apply (Nat.le_ceil _).trans
    exact_mod_cast (show ⌈Real.log (8 * (q : ℝ) * rho * n * Ct)⌉₊ ≤ r by
      rw [hr]
      exact le_max_right _ _)
  have hlog_rho_le_r : Real.log rho ≤ r := by
    rw [hlog_expand] at hlog_le_r
    linarith only [hlog_le_r, Real.log_nonneg hq_real, Real.log_nonneg hn_real,
      Real.log_nonneg hCt_real, Real.log_nonneg (show (1 : ℝ) ≤ 8 by norm_num)]
  have hlog_n_le_r : Real.log (n : ℝ) ≤ r := by
    rw [hlog_expand] at hlog_le_r
    linarith only [hlog_le_r, Real.log_nonneg hq_real, Real.log_nonneg hrho,
      Real.log_nonneg hCt_real, Real.log_nonneg (show (1 : ℝ) ≤ 8 by norm_num)]
  have hlog_base : Real.log base = Real.log rho + (d + 1 : ℕ) * Real.log (n : ℝ) := by
    dsimp [base]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hlog_base_bound : Real.log base ≤ ((d : ℝ) + 2) * r := by
    rw [hlog_base]
    have hmul := mul_le_mul_of_nonneg_left hlog_n_le_r
      (show (0 : ℝ) ≤ (d + 1 : ℕ) by positivity)
    norm_num only [Nat.cast_add, Nat.cast_one] at hmul ⊢
    calc
      Real.log rho + ((d : ℝ) + 1) * Real.log (n : ℝ) ≤
          (r : ℝ) + ((d : ℝ) + 1) * r := add_le_add hlog_rho_le_r hmul
      _ = ((d : ℝ) + 2) * r := by ring
  have hbase_root : base ^ (1 / (r : ℝ)) ≤ Real.exp ((d : ℝ) + 2) := by
    rw [Real.rpow_def_of_pos hbase_pos]
    apply Real.exp_le_exp.mpr
    calc
      Real.log base * (1 / (r : ℝ)) ≤
          (((d : ℝ) + 2) * r) * (1 / (r : ℝ)) :=
        mul_le_mul_of_nonneg_right hlog_base_bound (by positivity)
      _ = (d : ℝ) + 2 := by
        field_simp
  have hbase_mul_rpow :
      base * base ^ (-1 + 1 / (r : ℝ)) ≤ Real.exp ((d : ℝ) + 2) := by
    rw [show (-1 + 1 / (r : ℝ)) = 1 / (r : ℝ) - 1 by ring,
      Real.rpow_sub_one (ne_of_gt hbase_pos)]
    field_simp
    exact hbase_root
  have hrpow_base :
      (r : ℝ) ^ 3 * base ^ (-1 + 1 / (r : ℝ)) ≤
        32768 * (d : ℝ) ^ 6 * Real.exp ((d : ℝ) + 2) := by
    calc
      (r : ℝ) ^ 3 * base ^ (-1 + 1 / (r : ℝ)) ≤
          (32768 * (d : ℝ) ^ 6 * base) * base ^ (-1 + 1 / (r : ℝ)) :=
        mul_le_mul_of_nonneg_right hr_cube_base (by positivity)
      _ = 32768 * (d : ℝ) ^ 6 *
          (base * base ^ (-1 + 1 / (r : ℝ))) := by ring
      _ ≤ 32768 * (d : ℝ) ^ 6 * Real.exp ((d : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left hbase_mul_rpow (by positivity)
  refine ⟨hr_two, by simpa only [base] using hbase_one,
    by simpa only [base] using hr_base, ?_⟩
  change (r : ℝ) ^ 3 * (rho * (n : ℝ) ^ (d + 1)) ^ (-1 + 1 / (r : ℝ)) ≤
    32768 * (d : ℝ) ^ 6 * Real.exp ((d : ℝ) + 2)
  simpa only [base] using hrpow_base

@[blueprint "lem:uniform-score-sample-term-bound"
  (statement := /-- Let \(n,d,C_t,q,M,r\in\mathbb N\) and
  \(A,\rho,\epsilon\in\mathbb R\). Assume \(n,q\geq1\), \(d\geq2\),
  \(1\leq C_t\leq e^n\), \(q\leq2(n+d)^{2d}\), \(A,\rho\geq1\),
  \(0<\epsilon\leq1\), and
  \[
    \rho n^{d+1}A^4/\epsilon^2\leq M,\qquad
    r=\max\{2,\lceil\log(8q\rho nC_t)\rceil\}.
  \]
  Then
  \[
    \sqrt{\frac rM}+r^3M^{-1+1/r}
      \leq\frac{\epsilon}{A^2}
        \left(8d+32768d^6e^{d+2}\right).
  \] -/)
  (proof := /-- Apply \cref{lem:uniform-score-cutoff-bound} with
  \(b=\rho n^{d+1}\). It gives
  \[
    r\leq32d^2b,\qquad
    r^3b^{-1+1/r}\leq32768d^6e^{d+2}.
  \]
  Put \(X=bA^4/\epsilon^2\) and \(s=A^2/\epsilon\). The hypotheses imply
  \(M\geq X>0\), \(s\geq1\), and \(r\geq2\). Hence
  \[
    \sqrt{\frac rM}\leq 8d\frac{\epsilon}{A^2}.
  \]
  Since \(-1+1/r\leq0\) and
  \(2(-1+1/r)\leq-1\), monotonicity of real powers gives
  \[
    M^{-1+1/r}\leq X^{-1+1/r}
      \leq\frac{\epsilon}{A^2}b^{-1+1/r}.
  \]
  Multiplying the latter estimate by \(r^3\), applying the cutoff bound, and
  adding the square-root estimate proves the claim. -/)
  (title := /-- Uniform normalized score-sample terms -/)
  (latexEnv := "lemma")]
lemma uniform_score_sample_term_bound
    (n d Ct q M r : ℕ) (A rho epsilon : ℝ)
    (hn : 0 < n) (hd : 2 ≤ d) (hCt : 1 ≤ Ct)
    (hCt_exp : (Ct : ℝ) ≤ Real.exp (n : ℝ))
    (hq : 0 < q) (hq_bound : q ≤ 2 * (n + d) ^ (2 * d))
    (hA : 1 ≤ A) (hrho : 1 ≤ rho)
    (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1)
    (hM : rho * (n : ℝ) ^ (d + 1) * A ^ 4 / epsilon ^ 2 ≤ (M : ℝ))
    (hr : r = max 2 ⌈Real.log (8 * (q : ℝ) * rho * (n : ℝ) * (Ct : ℝ))⌉₊) :
    Real.sqrt ((r : ℝ) / (M : ℝ)) +
        (r : ℝ) ^ 3 * Real.rpow (M : ℝ) (-1 + 1 / (r : ℝ)) ≤
      (epsilon / A ^ 2) *
        (8 * (d : ℝ) + 32768 * (d : ℝ) ^ 6 * Real.exp ((d : ℝ) + 2)) := by
  let base : ℝ := rho * (n : ℝ) ^ (d + 1)
  obtain ⟨hr_two, hbase_one, hr_base, hrpow_base⟩ :=
    uniform_score_cutoff_bound n d Ct q r rho hn hd hCt hCt_exp hq hq_bound hrho hr
  have hr_real_two : (2 : ℝ) ≤ r := by exact_mod_cast hr_two
  have hbase_pos : 0 < base := lt_of_lt_of_le zero_lt_one (by simpa only [base] using hbase_one)
  have hr_base : (r : ℝ) ≤ 32 * (d : ℝ) ^ 2 * base := by simpa only [base] using hr_base
  have hrpow_base :
      (r : ℝ) ^ 3 * Real.rpow base (-1 + 1 / (r : ℝ)) ≤
        32768 * (d : ℝ) ^ 6 * Real.exp ((d : ℝ) + 2) := by
    simpa only [base] using hrpow_base
  let X : ℝ := base * A ^ 4 / epsilon ^ 2
  let scale : ℝ := A ^ 2 / epsilon
  have hscale_one : 1 ≤ scale := by
    dsimp [scale]
    apply (le_div_iff₀ hepsilon).2
    simpa only [one_mul] using hepsilon_one.trans (one_le_pow₀ hA (n := 2))
  have hscale_pos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale_one
  have hX_scale : X = base * scale ^ 2 := by
    dsimp [X, scale]
    field_simp
  have hX_pos : 0 < X := by
    rw [hX_scale]
    positivity
  have hM_bound : X ≤ (M : ℝ) := by
    dsimp [X, base]
    exact hM
  have hM_pos : (0 : ℝ) < M := hX_pos.trans_le hM_bound
  have hinv_r : 1 / (r : ℝ) ≤ 1 / 2 := by
    exact one_div_le_one_div_of_le (by norm_num) hr_real_two
  have hexponent_nonpos : -1 + 1 / (r : ℝ) ≤ 0 := by linarith
  have hexponent_twice : 2 * (-1 + 1 / (r : ℝ)) ≤ -1 := by linarith
  have hscale_rpow : (scale ^ 2) ^ (-1 + 1 / (r : ℝ)) ≤ epsilon / A ^ 2 := by
    calc
      (scale ^ 2) ^ (-1 + 1 / (r : ℝ)) =
          scale ^ (2 * (-1 + 1 / (r : ℝ))) := by
        rw [← Real.rpow_natCast]
        exact (Real.rpow_mul (le_of_lt hscale_pos) (2 : ℝ) _).symm
      scale ^ (2 * (-1 + 1 / (r : ℝ))) ≤ scale ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hscale_one hexponent_twice
      _ = epsilon / A ^ 2 := by
        rw [Real.rpow_neg_one]
        dsimp [scale]
        field_simp
  have hX_rpow : X ^ (-1 + 1 / (r : ℝ)) ≤
      (epsilon / A ^ 2) * base ^ (-1 + 1 / (r : ℝ)) := by
    rw [hX_scale, Real.mul_rpow (le_of_lt hbase_pos) (by positivity)]
    have hmul := mul_le_mul_of_nonneg_left hscale_rpow
      (show 0 ≤ base ^ (-1 + 1 / (r : ℝ)) by positivity)
    nlinarith only [hmul]
  have hM_rpow : (M : ℝ) ^ (-1 + 1 / (r : ℝ)) ≤
      (epsilon / A ^ 2) * base ^ (-1 + 1 / (r : ℝ)) := by
    exact (Real.rpow_le_rpow_of_nonpos hX_pos hM_bound hexponent_nonpos).trans hX_rpow
  have hsecond : (r : ℝ) ^ 3 * (M : ℝ) ^ (-1 + 1 / (r : ℝ)) ≤
      (epsilon / A ^ 2) *
        (32768 * (d : ℝ) ^ 6 * Real.exp ((d : ℝ) + 2)) := by
    calc
      (r : ℝ) ^ 3 * (M : ℝ) ^ (-1 + 1 / (r : ℝ)) ≤
          (r : ℝ) ^ 3 * ((epsilon / A ^ 2) * base ^ (-1 + 1 / (r : ℝ))) :=
        mul_le_mul_of_nonneg_left hM_rpow (by positivity)
      _ = (epsilon / A ^ 2) *
          ((r : ℝ) ^ 3 * base ^ (-1 + 1 / (r : ℝ))) := by ring
      _ ≤ (epsilon / A ^ 2) *
          (32768 * (d : ℝ) ^ 6 * Real.exp ((d : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hrpow_base (by positivity)
  have hratio_base : (r : ℝ) / base ≤ 32 * (d : ℝ) ^ 2 := by
    exact (div_le_iff₀ hbase_pos).2 (by simpa only [mul_assoc] using hr_base)
  have hratio_M : (r : ℝ) / M ≤
      32 * (d : ℝ) ^ 2 * (epsilon / A ^ 2) ^ 2 := by
    have hinvM : (1 : ℝ) / M ≤ 1 / X := one_div_le_one_div_of_le hX_pos hM_bound
    calc
      (r : ℝ) / M = r * (1 / M) := by ring
      _ ≤ r * (1 / X) := mul_le_mul_of_nonneg_left hinvM (by positivity)
      _ = (epsilon / A ^ 2) ^ 2 * (r / base) := by
        rw [hX_scale]
        dsimp [scale]
        field_simp
      _ ≤ (epsilon / A ^ 2) ^ 2 * (32 * (d : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hratio_base (by positivity)
      _ = 32 * (d : ℝ) ^ 2 * (epsilon / A ^ 2) ^ 2 := by ring
  have hsqrt : Real.sqrt ((r : ℝ) / M) ≤
      8 * (d : ℝ) * (epsilon / A ^ 2) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · calc
        (r : ℝ) / M ≤ 32 * (d : ℝ) ^ 2 * (epsilon / A ^ 2) ^ 2 := hratio_M
        _ ≤ (8 * (d : ℝ) * (epsilon / A ^ 2)) ^ 2 := by
          nlinarith only [sq_nonneg ((d : ℝ) * (epsilon / A ^ 2))]
  let C : ℝ := 8 * (d : ℝ) + 32768 * (d : ℝ) ^ 6 * Real.exp ((d : ℝ) + 2)
  have hsum_terms : Real.sqrt ((r : ℝ) / M) +
      (r : ℝ) ^ 3 * Real.rpow (M : ℝ) (-1 + 1 / (r : ℝ)) ≤
        (epsilon / A ^ 2) * C := by
    dsimp [C]
    calc
      Real.sqrt ((r : ℝ) / M) +
          (r : ℝ) ^ 3 * (M : ℝ) ^ (-1 + 1 / (r : ℝ)) ≤
        8 * (d : ℝ) * (epsilon / A ^ 2) +
          (epsilon / A ^ 2) *
            (32768 * (d : ℝ) ^ 6 * Real.exp ((d : ℝ) + 2)) :=
        add_le_add hsqrt hsecond
      _ = (epsilon / A ^ 2) *
          (8 * (d : ℝ) + 32768 * (d : ℝ) ^ 6 * Real.exp ((d : ℝ) + 2)) := by ring
  exact hsum_terms

@[blueprint "lem:uniform-score-constant-absorption"
  (statement := /-- There are an absolute real constant \(A_0>1\) and an absolute integer
  \(C_{\rm conc}\in\mathbb N_{>0}\) with the following property. Let
  \(n,d,C_t,w,q\in\mathbb N\) satisfy
  \[
    n\geq1,\qquad d\geq2,\qquad 1\leq C_t\leq e^n,\qquad
    w\geq1,\qquad 1\leq q\leq2(n+d)^{2d},
  \]
  and let \(u,H\in\mathbb R\) satisfy
  \[
    u\geq1+2^{-10},\qquad 0<H\leq8(1+du+u^2).
  \]
  There is \(A_{\rm conc}\) with
  \(1\leq A_{\rm conc}\leq\max\{A_0,u^{C_{\rm conc}d^2w}\}\) such that, for every
  \(M,r\in\mathbb N\) and \(\rho,\epsilon\in\mathbb R\) satisfying
  \[
    \rho\geq1,\qquad 0<\epsilon\leq1,\qquad
    M\geq\frac{\rho n^{d+1}A_{\rm conc}^4}{\epsilon^2},\qquad
    r=\max\left\{2,\left\lceil
      \log(8q\rho nC_t)\right\rceil\right\},
  \]
  one has
  \[
    4096eH\left(\sqrt{\frac rM}+r^3M^{-1+1/r}\right)
      \leq\frac{\epsilon}{4A_{\rm conc}}.
  \] -/)
  (proof := /-- Take \(A_0=2\), \(C_{\rm conc}=2^{31}\), and, for each
  admissible parameter tuple, set
  \[
    A_{\rm conc}=u^{2^{31}d^2w}.
  \]
  Since \(u\geq1\), this choice satisfies
  \(1\leq A_{\rm conc}\leq\max\{A_0,u^{C_{\rm conc}d^2w}\}\).

  Fix \(M,r,\rho,\epsilon\) satisfying the remaining hypotheses and put
  \[
    C=8d+32768d^6e^{d+2}.
  \]
  By \cref{lem:uniform-score-sample-term-bound},
  \[
    \sqrt{\frac rM}+r^3M^{-1+1/r}
      \leq \frac{\epsilon}{A_{\rm conc}^2}C.
  \]
  Put \(P=2^{30}d^2w\). By \cref{lem:uniform-score-power-absorption},
  \(8192eHC\leq u^P\), whereas \cref{lem:uniform-score-base-growth} gives
  \(2\leq u^{1024}\). Since \(u\geq1\), \(d\geq2\), and \(w\geq1\), we have
  \(P+1024\leq2P=2^{31}d^2w\). It follows that
  \[
    16384eHC\leq2u^P\leq u^{P+1024}
      \leq u^{2^{31}d^2w}=A_{\rm conc}.
  \]
  Therefore
  \[
    4096eH\frac{\epsilon}{A_{\rm conc}^2}C
      =\frac{\epsilon}{4A_{\rm conc}}
        \frac{16384eHC}{A_{\rm conc}}
      \leq\frac{\epsilon}{4A_{\rm conc}},
  \]
  which proves the asserted estimate. -/)
  (title := /-- Explicit absorption of the score-concentration constants -/)
  (latexEnv := "lemma")]
lemma uniform_score_constant_absorption :
    ∃ A0 : ℝ, 1 < A0 ∧
      ∃ Cconc : ℕ, 0 < Cconc ∧
        ∀ (n d Ct w q : ℕ) (u H : ℝ),
          0 < n → 2 ≤ d → 1 ≤ Ct → (Ct : ℝ) ≤ Real.exp (n : ℝ) →
          0 < w → 0 < q →
          1 + (1 / 1024 : ℝ) ≤ u →
          0 < H → H ≤ 8 * (1 + (d : ℝ) * u + u ^ 2) →
          q ≤ 2 * (n + d) ^ (2 * d) →
          ∃ Aconc : ℝ,
            1 ≤ Aconc ∧
            Aconc ≤ max A0 (u ^ (Cconc * d ^ 2 * w)) ∧
            ∀ (M r : ℕ) (rho epsilon : ℝ),
              1 ≤ rho → 0 < epsilon → epsilon ≤ 1 →
              rho * (n : ℝ) ^ (d + 1) * Aconc ^ 4 / epsilon ^ 2 ≤ (M : ℝ) →
              r =
                max 2 ⌈Real.log
                  (8 * (q : ℝ) * rho * (n : ℝ) * (Ct : ℝ))⌉₊ →
              4096 * Real.exp 1 * H *
                  (Real.sqrt ((r : ℝ) / (M : ℝ)) +
                    (r : ℝ) ^ 3 *
                      Real.rpow (M : ℝ) (-1 + 1 / (r : ℝ))) ≤
                epsilon / (4 * Aconc) := by
  refine ⟨2, by norm_num, 2 ^ 31, by norm_num, ?_⟩
  intro n d Ct w q u H hn hd hCt hCt_exp hw hq hu hHpos hH hq_bound
  have hu_one : (1 : ℝ) ≤ u := by
    norm_num at hu ⊢
    linarith
  let Aconc : ℝ := u ^ (2 ^ 31 * d ^ 2 * w)
  have hAconc : (1 : ℝ) ≤ Aconc := by
    exact one_le_pow₀ hu_one
  refine ⟨Aconc, hAconc, ?_, ?_⟩
  · exact le_max_right _ _
  · intro M r rho epsilon hrho hepsilon hepsilon_one hM hr
    let C : ℝ := 8 * (d : ℝ) +
      32768 * (d : ℝ) ^ 6 * Real.exp ((d : ℝ) + 2)
    let P : ℕ := 2 ^ 30 * d ^ 2 * w
    have hsample : Real.sqrt ((r : ℝ) / (M : ℝ)) +
        (r : ℝ) ^ 3 * Real.rpow (M : ℝ) (-1 + 1 / (r : ℝ)) ≤
          (epsilon / Aconc ^ 2) * C := by
      simpa only [C] using
        uniform_score_sample_term_bound n d Ct q M r Aconc rho epsilon
          hn hd hCt hCt_exp hq hq_bound hAconc hrho hepsilon hepsilon_one hM hr
    have hpower : 8192 * Real.exp 1 * H * C ≤ u ^ P := by
      simpa only [C, P] using
        uniform_score_power_absorption d w u H hd hw hu hHpos hH
    have hbase : (2 : ℝ) ≤ u ^ 1024 := uniform_score_base_growth u hu
    have hdw_one : 1 ≤ d ^ 2 * w := by
      have hd_pos : 0 < d := by omega
      exact Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (Nat.mul_pos (pow_pos hd_pos 2) hw))
    have hP : 1024 ≤ P := by
      calc
        1024 ≤ 2 ^ 30 := by norm_num
        _ = 2 ^ 30 * 1 := by norm_num
        _ ≤ 2 ^ 30 * (d ^ 2 * w) := Nat.mul_le_mul_left _ hdw_one
        _ = P := by simp [P, Nat.mul_assoc]
    have hexponent : 1024 + P ≤ 2 ^ 31 * d ^ 2 * w := by
      calc
        1024 + P ≤ P + P := Nat.add_le_add_right hP P
        _ = 2 ^ 31 * d ^ 2 * w := by simp [P]; ring
    have habsorb : 16384 * Real.exp 1 * H * C ≤ Aconc := by
      calc
        16384 * Real.exp 1 * H * C ≤ 2 * u ^ P := by
          nlinarith only [hpower]
        _ ≤ u ^ 1024 * u ^ P :=
          mul_le_mul_of_nonneg_right hbase (by positivity)
        _ = u ^ (1024 + P) := by rw [pow_add]
        _ ≤ u ^ (2 ^ 31 * d ^ 2 * w) :=
          pow_le_pow_right₀ hu_one hexponent
        _ = Aconc := by rfl
    have hAconc_pos : 0 < Aconc := lt_of_lt_of_le zero_lt_one hAconc
    have hratio : (16384 * Real.exp 1 * H * C) / Aconc ≤ 1 :=
      (div_le_one hAconc_pos).2 habsorb
    calc
      4096 * Real.exp 1 * H *
          (Real.sqrt ((r : ℝ) / (M : ℝ)) +
            (r : ℝ) ^ 3 * Real.rpow (M : ℝ) (-1 + 1 / (r : ℝ))) ≤
        4096 * Real.exp 1 * H * ((epsilon / Aconc ^ 2) * C) :=
          mul_le_mul_of_nonneg_left hsample (by positivity)
      _ = (epsilon / (4 * Aconc)) *
          ((16384 * Real.exp 1 * H * C) / Aconc) := by
            field_simp [ne_of_gt hAconc_pos]
            <;> ring
      _ ≤ (epsilon / (4 * Aconc)) * 1 :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = epsilon / (4 * Aconc) := by ring

@[blueprint "lem:independent-centered-quadratic-moment-average-ae"
  (statement := /-- The conclusion of
  \cref{lem:independent-centered-quadratic-moment-average} remains valid when the random
  variables are only almost everywhere measurable rather than everywhere measurable. -/)
  (proof := /-- Replace each random variable by its measurable representative. Almost
  everywhere equality preserves independence, integrability, integrals, and all $L^p$
  seminorms. Apply \cref{lem:independent-centered-quadratic-moment-average} to these measurable
  representatives. Their finite averages agree almost everywhere with the original average,
  so the resulting $L^r$ estimate transfers back. -/)
  (title := /-- Quadratic-moment average bound under a.e. measurability -/)
  (latexEnv := "lemma")]
lemma independent_centered_quadratic_moment_average_ae :
    ∀ {M : ℕ} {Ω : Type} [MeasurableSpace Ω]
      (mu : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure mu]
      (Z : Fin M → Ω → ℝ) (K : ℝ),
      ProbabilityTheory.iIndepFun Z mu →
      (∀ m, AEMeasurable (Z m) mu) →
      (∀ m, MeasureTheory.Integrable (Z m) mu) →
      (∀ m, ∫ omega, Z m omega ∂mu = 0) →
      0 < K →
      (∀ m (s : ℕ), 2 ≤ s →
        MeasureTheory.eLpNorm (Z m) (s : ENNReal) mu ≤
          ENNReal.ofReal (K * (s : ℝ) ^ 2)) →
      ∀ r : ℕ, 2 ≤ r → 0 < M →
        MeasureTheory.eLpNorm
            (fun omega => (M : ℝ)⁻¹ * ∑ m, Z m omega) (r : ENNReal) mu ≤
          ENNReal.ofReal
            (64 * K * (Real.sqrt ((r : ℝ) / (M : ℝ)) +
              (r : ℝ) ^ 3 * Real.rpow (M : ℝ) (-1 + 1 / (r : ℝ)))) := by
  intro M Ω instMeas mu instProb Z K hIndep hMeas hInt hCenter hK hMoment r hr hM
  let Zm : Fin M → Ω → ℝ := fun m => (hMeas m).mk (Z m)
  have hEq (m : Fin M) : Z m =ᵐ[mu] Zm m := (hMeas m).ae_eq_mk
  have hIndepm : ProbabilityTheory.iIndepFun Zm mu := hIndep.congr hEq
  have hMeasm (m : Fin M) : Measurable (Zm m) := (hMeas m).measurable_mk
  have hIntm (m : Fin M) : MeasureTheory.Integrable (Zm m) mu :=
    (hInt m).congr (hEq m)
  have hCenterm (m : Fin M) : ∫ omega, Zm m omega ∂mu = 0 := by
    rw [← hCenter m]
    exact MeasureTheory.integral_congr_ae (hEq m).symm
  have hMomentm (m : Fin M) (s : ℕ) (hs : 2 ≤ s) :
      MeasureTheory.eLpNorm (Zm m) (s : ENNReal) mu ≤
        ENNReal.ofReal (K * (s : ℝ) ^ 2) := by
    rw [MeasureTheory.eLpNorm_congr_ae (hEq m).symm]
    exact hMoment m s hs
  have hbound := independent_centered_quadratic_moment_average mu Zm K hIndepm hMeasm
    hIntm hCenterm hK hMomentm r hr hM
  have hAll : ∀ᵐ omega ∂mu, ∀ m, Z m omega = Zm m omega :=
    MeasureTheory.ae_all_iff.mpr hEq
  have hAverage :
      (fun omega => (M : ℝ)⁻¹ * ∑ m, Z m omega) =ᵐ[mu]
        fun omega => (M : ℝ)⁻¹ * ∑ m, Zm m omega := by
    filter_upwards [hAll] with omega homega
    simp_rw [homega]
  rw [MeasureTheory.eLpNorm_congr_ae hAverage]
  exact hbound

@[blueprint "lem:elpnorm-exponential-tail-bound"
  (statement := /-- Let $r\ge2$ be an integer, let $R>0$, and let $F$ be an almost everywhere
  strongly measurable real function with $\lVert F\rVert_r\le R$. Then
  \[
    \mu\{|F|>eR\}\le e^{-r}.
  \] -/)
  (proof := /-- Apply the $L^r$ Markov inequality at the threshold $eR$. The resulting upper
  bound is $(eR)^{-r}\lVert F\rVert_r^r$, which is at most $e^{-r}$ by the assumed seminorm
  estimate. -/)
  (title := /-- Exponential tail bound from an integer moment -/)
  (latexEnv := "lemma")]
lemma elpnorm_exponential_tail_bound {Ω : Type} [MeasurableSpace Ω]
    (mu : MeasureTheory.Measure Ω) (F : Ω → ℝ) (r : ℕ) (R : ℝ)
    (hr : 2 ≤ r) (hR : 0 < R)
    (hMeas : MeasureTheory.AEStronglyMeasurable F mu)
    (hNorm : MeasureTheory.eLpNorm F (r : ENNReal) mu ≤ ENNReal.ofReal R) :
    mu {omega | Real.exp 1 * R < |F omega|} ≤
      ENNReal.ofReal ((Real.exp 1)⁻¹ ^ r) := by
  let epsilon : ENNReal := ENNReal.ofReal (Real.exp 1 * R)
  have hepsilon : epsilon ≠ 0 := by
    dsimp [epsilon]
    exact (ENNReal.ofReal_pos.mpr (mul_pos (Real.exp_pos 1) hR)).ne'
  have hpzero : (r : ENNReal) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have hptop : (r : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top r
  have hmarkov := MeasureTheory.meas_ge_le_mul_pow_eLpNorm_enorm mu hpzero hptop
    hMeas hepsilon (by simp)
  have hsubset : {omega | Real.exp 1 * R < |F omega|} ⊆
      {omega | epsilon ≤ ‖F omega‖ₑ} := by
    intro omega homega
    dsimp [epsilon]
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal homega.le
  calc
    mu {omega | Real.exp 1 * R < |F omega|} ≤
        mu {omega | epsilon ≤ ‖F omega‖ₑ} := MeasureTheory.measure_mono hsubset
    _ ≤ epsilon⁻¹ ^ (r : ENNReal).toReal *
        MeasureTheory.eLpNorm F (r : ENNReal) mu ^ (r : ENNReal).toReal := hmarkov
    _ ≤ epsilon⁻¹ ^ (r : ENNReal).toReal *
        ENNReal.ofReal R ^ (r : ENNReal).toReal := by
      exact mul_le_mul_left' (ENNReal.rpow_le_rpow hNorm (by positivity)) _
    _ = (epsilon⁻¹ * ENNReal.ofReal R) ^ (r : ENNReal).toReal := by
      rw [ENNReal.mul_rpow_of_nonneg]
      positivity
    _ = ENNReal.ofReal ((Real.exp 1)⁻¹ ^ r) := by
      have hbase : epsilon⁻¹ * ENNReal.ofReal R = ENNReal.ofReal (Real.exp 1)⁻¹ := by
        dsimp [epsilon]
        rw [← ENNReal.ofReal_inv_of_pos (mul_pos (Real.exp_pos 1) hR)]
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (Real.exp 1 * R)⁻¹)]
        congr 1
        field_simp [ne_of_gt (Real.exp_pos 1), ne_of_gt hR]
      rw [hbase, ENNReal.ofReal_rpow_of_pos (inv_pos.mpr (Real.exp_pos 1))]
      simp only [ENNReal.toReal_natCast, Real.rpow_natCast]

@[blueprint "lem:finite-feature-uniform-probability"
  (statement := /-- Let $S$ be a finite family of almost everywhere strongly measurable real
  random variables $D_j$. Let $r\ge2$ and $R>0$, and assume
  $\lVert D_j\rVert_r\le R$ for every $j\in S$. If $\delta\ge eR$, then
  \[
    \mu\{\omega:|D_j(\omega)|\le\delta\text{ for every }j\in S\}
      \ge 1-|S|e^{-r}.
  \] -/)
  (proof := /-- Choose measurable representatives of all $D_j$. By
  \cref{lem:elpnorm-exponential-tail-bound}, each representative violates the threshold
  $delta\ge eR$ on a set of probability at most $e^{-r}$. A finite union bound controls the
  probability that any representative violates it. The complementary event is measurable and
  has probability at least $1-|S|e^{-r}$. Almost everywhere equality of the representatives
  and the original variables transfers this lower bound to the asserted event. -/)
  (title := /-- Uniform finite-feature probability bound -/)
  (latexEnv := "lemma")]
lemma finite_feature_uniform_probability {Ω ι : Type} [MeasurableSpace Ω]
    (mu : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure mu]
    (s : Finset ι) (D : ι → Ω → ℝ) (r : ℕ) (R delta : ℝ)
    (hr : 2 ≤ r) (hR : 0 < R) (hdelta : Real.exp 1 * R ≤ delta)
    (hMeas : ∀ j ∈ s, MeasureTheory.AEStronglyMeasurable (D j) mu)
    (hNorm : ∀ j ∈ s,
      MeasureTheory.eLpNorm (D j) (r : ENNReal) mu ≤ ENNReal.ofReal R) :
    1 - (s.card : ℝ) * (Real.exp 1)⁻¹ ^ r ≤
      mu.real {omega | ∀ j ∈ s, |D j omega| ≤ delta} := by
  classical
  let Dm : ι → Ω → ℝ := fun j => if hj : j ∈ s then (hMeas j hj).mk (D j) else 0
  have hDm (j : ι) (hj : j ∈ s) : Measurable (Dm j) := by
    dsimp [Dm]
    rw [dif_pos hj]
    exact (hMeas j hj).measurable_mk
  have hEq (j : ι) (hj : j ∈ s) : D j =ᵐ[mu] Dm j := by
    dsimp [Dm]
    rw [dif_pos hj]
    exact (hMeas j hj).ae_eq_mk
  let bad : ι → Set Ω := fun j => {omega | delta < |Dm j omega|}
  have hbadMeas (j : ι) (hj : j ∈ s) : MeasurableSet (bad j) := by
    exact measurableSet_lt measurable_const (hDm j hj).abs
  have hbad (j : ι) (hj : j ∈ s) :
      mu.real (bad j) ≤ (Real.exp 1)⁻¹ ^ r := by
    have hNormm : MeasureTheory.eLpNorm (Dm j) (r : ENNReal) mu ≤ ENNReal.ofReal R := by
      rw [MeasureTheory.eLpNorm_congr_ae (hEq j hj).symm]
      exact hNorm j hj
    have htail := elpnorm_exponential_tail_bound mu (Dm j) r R hr hR
      (hDm j hj).aestronglyMeasurable hNormm
    have hsubset : bad j ⊆ {omega | Real.exp 1 * R < |Dm j omega|} := by
      intro omega homega
      exact lt_of_le_of_lt hdelta homega
    have hmeasure : mu (bad j) ≤ ENNReal.ofReal ((Real.exp 1)⁻¹ ^ r) :=
      (MeasureTheory.measure_mono hsubset).trans htail
    rw [MeasureTheory.Measure.real]
    calc
      (mu (bad j)).toReal ≤ (ENNReal.ofReal ((Real.exp 1)⁻¹ ^ r)).toReal :=
        ENNReal.toReal_mono (by finiteness) hmeasure
      _ = (Real.exp 1)⁻¹ ^ r := ENNReal.toReal_ofReal (by positivity)
  let badUnion : Set Ω := ⋃ j ∈ s, bad j
  have hbadUnionMeas : MeasurableSet badUnion := by
    dsimp [badUnion]
    exact Finset.measurableSet_biUnion s hbadMeas
  have hbadUnion : mu.real badUnion ≤ (s.card : ℝ) * (Real.exp 1)⁻¹ ^ r := by
    calc
      mu.real badUnion ≤ ∑ j ∈ s, mu.real (bad j) := by
        exact MeasureTheory.measureReal_biUnion_finset_le s bad
      _ ≤ ∑ j ∈ s, (Real.exp 1)⁻¹ ^ r := Finset.sum_le_sum hbad
      _ = (s.card : ℝ) * (Real.exp 1)⁻¹ ^ r := by simp
  let good : Set Ω := badUnionᶜ
  have hgoodMeasure : 1 - (s.card : ℝ) * (Real.exp 1)⁻¹ ^ r ≤ mu.real good := by
    rw [show mu.real good = 1 - mu.real badUnion by
      dsimp [good]
      rw [MeasureTheory.measureReal_compl hbadUnionMeas]
      simp]
    linarith
  have hAll : ∀ᵐ omega ∂mu, ∀ j : s, D j omega = Dm j omega := by
    rw [MeasureTheory.ae_all_iff]
    intro j
    exact hEq j j.property
  have hgoodSubset : ∀ᵐ omega ∂mu,
      omega ∈ good → omega ∈ {omega | ∀ j ∈ s, |D j omega| ≤ delta} := by
    filter_upwards [hAll] with omega homega hgood
    intro j hj
    rw [homega ⟨j, hj⟩]
    apply le_of_not_gt
    intro hviol
    apply hgood
    dsimp [good, badUnion]
    exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hj, hviol⟩⟩
  have hmeasureMono : mu good ≤
      mu {omega | ∀ j ∈ s, |D j omega| ≤ delta} :=
    MeasureTheory.measure_mono_ae hgoodSubset
  have hrealMono : mu.real good ≤
      mu.real {omega | ∀ j ∈ s, |D j omega| ≤ delta} := by
    rw [MeasureTheory.Measure.real, MeasureTheory.Measure.real]
    exact ENNReal.toReal_mono (by finiteness) hmeasureMono
  exact hgoodMeasure.trans hrealMono

@[blueprint "lem:polynomial-feature-empirical-moment-bound"
  (statement := /-- Let $Y:\mathbb R^n\to\mathbb R$ be measurable and satisfy the polynomial
  envelope in \cref{lem:polynomial-score-feature-moment} with constant $H>0$. For an IID sample
  of positive size $M$ from a distribution satisfying the tail condition, and every integer
  $r\ge2$,
  \[
    \left\lVert M^{-1}\sum_mY(X_m)-\mathbb EY\right\rVert_r
      \le4096H\left(\sqrt{r/M}+r^3M^{-1+1/r}\right).
  \]
  Moreover, $Y$ is integrable. -/)
  (proof := /-- By \cref{lem:polynomial-score-feature-moment}, $Y$ is integrable and the
  centered variable $Y-\mathbb EY$ has $s$th seminorm at most $64Hs^2$ for every $s\ge2$.
  Identical distribution transfers integrability, centering, and these seminorms to every
  sample variable, while independence is preserved by measurable composition. Apply
  \cref{lem:independent-centered-quadratic-moment-average-ae} with $K=64H$ and rewrite the
  average of the centered variables. -/)
  (title := /-- Empirical moment bound for one polynomial feature -/)
  (latexEnv := "lemma")]
lemma polynomial_feature_empirical_moment_bound {n M : ℕ} {Ω : Type}
    [MeasurableSpace Ω] (mu : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure mu]
    (d : ℕ) (tailRate : ℝ) (Ct : ℕ)
    (p : MeasureTheory.Measure (Fin n → ℝ)) [MeasureTheory.IsProbabilityMeasure p]
    (samples : Fin M → Ω → (Fin n → ℝ)) (Y : (Fin n → ℝ) → ℝ) (H : ℝ)
    (htail : tail_decay_condition d tailRate Ct p) (hH : 0 < H)
    (hY : Measurable Y)
    (henvelope : ∀ x, |Y x| ≤
      H * (1 + (‖x‖ / (Ct : ℝ)) ^ (2 * (d - 1))))
    (hiid : iid_samples mu p samples) (r : ℕ) (hr : 2 ≤ r) (hM : 0 < M) :
    MeasureTheory.Integrable Y p ∧
      MeasureTheory.AEStronglyMeasurable
        (fun omega => (M : ℝ)⁻¹ * ∑ m, Y (samples m omega) - ∫ x, Y x ∂p) mu ∧
      MeasureTheory.eLpNorm
          (fun omega => (M : ℝ)⁻¹ * ∑ m, Y (samples m omega) - ∫ x, Y x ∂p)
          (r : ENNReal) mu ≤
        ENNReal.ofReal (4096 * H *
          (Real.sqrt ((r : ℝ) / (M : ℝ)) +
            (r : ℝ) ^ 3 * Real.rpow (M : ℝ) (-1 + 1 / (r : ℝ)))) := by
  rcases polynomial_score_feature_moment d tailRate Ct p Y H htail hH hY henvelope with
    ⟨hYInt, hYMoment⟩
  refine ⟨hYInt, ?_⟩
  rcases hiid with ⟨hIndep, hIdent⟩
  let mean : ℝ := ∫ x, Y x ∂p
  let Z : Fin M → Ω → ℝ := fun m omega => Y (samples m omega) - mean
  have hIndepZ : ProbabilityTheory.iIndepFun Z mu := by
    have hcomp := hIndep.comp (fun _ => fun x => Y x - mean)
      (fun _ => hY.sub measurable_const)
    simpa [Z, Function.comp_def] using hcomp
  have hIdentZ (m : Fin M) : ProbabilityTheory.IdentDistrib (Z m)
      (fun x => Y x - mean) mu p := by
    have hcenter : Measurable (fun x : Fin n → ℝ => Y x - mean) :=
      hY.sub measurable_const
    convert ((hIdent m).comp hcenter) using 1 <;> simp [Z, Function.comp_def]
  have hMeasZ (m : Fin M) : AEMeasurable (Z m) mu := (hIdentZ m).aemeasurable_fst
  have hIntZ (m : Fin M) : MeasureTheory.Integrable (Z m) mu := by
    rw [(hIdentZ m).integrable_iff]
    exact hYInt.sub (MeasureTheory.integrable_const mean)
  have hCenterZ (m : Fin M) : ∫ omega, Z m omega ∂mu = 0 := by
    rw [(hIdentZ m).integral_eq]
    dsimp [mean]
    rw [MeasureTheory.integral_sub hYInt (MeasureTheory.integrable_const _)]
    simp
  have hMomentZ (m : Fin M) (s : ℕ) (hs : 2 ≤ s) :
      MeasureTheory.eLpNorm (Z m) (s : ENNReal) mu ≤
        ENNReal.ofReal ((64 * H) * (s : ℝ) ^ 2) := by
    rw [(hIdentZ m).eLpNorm_eq]
    simpa [mean] using hYMoment s hs
  have hbound := independent_centered_quadratic_moment_average_ae mu Z (64 * H)
    hIndepZ hMeasZ hIntZ hCenterZ (by positivity) hMomentZ r hr hM
  have hMReal : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
  have haverage :
      (fun omega => (M : ℝ)⁻¹ * ∑ m, Z m omega) =
        fun omega => (M : ℝ)⁻¹ * ∑ m, Y (samples m omega) - ∫ x, Y x ∂p := by
    funext omega
    dsimp [Z, mean]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hMReal]
  have hAverageInt : MeasureTheory.Integrable
      (fun omega => (M : ℝ)⁻¹ * ∑ m, Z m omega) mu := by
    exact (MeasureTheory.integrable_finsetSum Finset.univ fun m _ => hIntZ m).const_mul _
  refine ⟨?_, ?_⟩
  · rw [← haverage]
    exact hAverageInt.aestronglyMeasurable
  rw [← haverage]
  convert hbound using 1 <;> ring_nf

@[blueprint "lem:uniform-score-cutoff-failure-bound"
  (statement := /-- Let $n,C_t,q$ be positive integers, let $\rho\ge1$, and let
  \[
    r=\max\{2,\lceil\log(8q\rho nC_t)\rceil\}.
  \]
  If $N\le q$, then
  \[
    N e^{-r}<\frac1{\rho nC_t}.
  \] -/)
  (proof := /-- Put $T=8q\rho nC_t>0$. The definition of $r$ gives
  $\log T\le r$, hence $T\le e^r$ and $e^{-r}\le T^{-1}$. Multiplying by $N\le q$ gives
  $Ne^{-r}\le(8\rho nC_t)^{-1}$, which is strictly smaller than
  $(\rho nC_t)^{-1}$. -/)
  (title := /-- Failure probability from the logarithmic cutoff -/)
  (latexEnv := "lemma")]
lemma uniform_score_cutoff_failure_bound (n Ct q N r : ℕ) (rho : ℝ)
    (hn : 0 < n) (hCt : 0 < Ct) (hq : 0 < q) (hN : N ≤ q) (hrho : 1 ≤ rho)
    (hr : r = max 2 ⌈Real.log (8 * (q : ℝ) * rho * (n : ℝ) * (Ct : ℝ))⌉₊) :
    (N : ℝ) * (Real.exp 1)⁻¹ ^ r < 1 / (rho * (n : ℝ) * (Ct : ℝ)) := by
  let T : ℝ := 8 * (q : ℝ) * rho * (n : ℝ) * (Ct : ℝ)
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hCtReal : (0 : ℝ) < Ct := by exact_mod_cast hCt
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
  have hT : 0 < T := by dsimp [T]; positivity
  have hceil : ⌈Real.log T⌉₊ ≤ r := by
    rw [hr]
    exact le_max_right _ _
  have hlog : Real.log T ≤ (r : ℝ) := by
    exact (Nat.le_ceil (Real.log T)).trans (by exact_mod_cast hceil)
  have hTexp : T ≤ Real.exp (r : ℝ) := by
    rw [← Real.exp_log hT]
    exact Real.exp_le_exp.mpr hlog
  have hdecay : (Real.exp 1)⁻¹ ^ r ≤ 1 / T := by
    have heq : (Real.exp 1)⁻¹ ^ r = (Real.exp (r : ℝ))⁻¹ := by
      rw [← Real.exp_neg, ← Real.exp_nat_mul]
      rw [show (r : ℝ) * -1 = -(r : ℝ) by ring, Real.exp_neg]
    rw [heq, one_div]
    exact (inv_le_inv₀ (Real.exp_pos _) hT).2 hTexp
  have hNq : (N : ℝ) ≤ q := by exact_mod_cast hN
  calc
    (N : ℝ) * (Real.exp 1)⁻¹ ^ r ≤ (q : ℝ) * (1 / T) :=
      mul_le_mul hNq hdecay (by positivity) hqReal.le
    _ = 1 / (8 * rho * (n : ℝ) * (Ct : ℝ)) := by
      dsimp [T]
      field_simp [ne_of_gt hqReal, ne_of_gt hnReal, ne_of_gt hCtReal,
        ne_of_gt (lt_of_lt_of_le zero_lt_one hrho)]
    _ < 1 / (rho * (n : ℝ) * (Ct : ℝ)) := by
      have hdenom : 0 < rho * (n : ℝ) * (Ct : ℝ) := by positivity
      rw [show 8 * rho * (n : ℝ) * (Ct : ℝ) = 8 *
        (rho * (n : ℝ) * (Ct : ℝ)) by ring]
      rw [one_div, one_div]
      exact (inv_lt_inv₀ (by positivity) hdenom).2 (by nlinarith)

@[blueprint "lem:monomial-value-absolute-bound"
  (statement := /-- For every exponent vector $a\in\mathbb N^n$ and every
  $x\in\mathbb R^n$,
  \[
    |x^a|\le \max\{1,\lVert x\rVert_\infty\}^{\sum_j a_j}.
  \] -/)
  (proof := /-- The absolute value of the product defining $x^a$ is bounded by the product of
  the absolute values of its factors. Each coordinate absolute value is at most
  $\lVert x\rVert_\infty$ and hence at most $\max\{1,\lVert x\rVert_\infty\}$. Multiplying the
  resulting power bounds and collecting exponents proves the claim by
  \cref{def:monomial-value}. -/)
  (title := /-- Uniform absolute bound for a monomial -/)
  (latexEnv := "lemma")]
lemma monomial_value_absolute_bound {n : ℕ} (factor : polynomial_factor n)
    (x : Fin n → ℝ) :
    |monomial_value factor x| ≤ max 1 ‖x‖ ^ (∑ j, factor j) := by
  change ‖monomial_value factor x‖ ≤ max 1 ‖x‖ ^ (∑ j, factor j)
  calc
    ‖monomial_value factor x‖ ≤ ∏ j, ‖x j ^ factor j‖ := by
      exact Finset.norm_prod_le Finset.univ _
    _ ≤ ∏ j, (max 1 ‖x‖) ^ factor j := by
      apply Finset.prod_le_prod
      · intro j hj
        positivity
      · intro j hj
        rw [norm_pow]
        gcongr
        exact le_max_of_le_right (norm_le_pi_norm x j)
    _ = max 1 ‖x‖ ^ (∑ j, factor j) := by
      exact Finset.prod_pow_eq_pow_sum Finset.univ factor _

@[blueprint "lem:monomial-partials-as-monomials"
  (statement := /-- For a monomial $x^a$ and a coordinate $i$, its first and second formal
  partial derivatives are respectively
  \[
    a_i x^{a-e_i},\qquad a_i(a_i-1)x^{a-2e_i},
  \]
  where subtraction of exponents is truncated in $\mathbb N$. -/)
  (proof := /-- Expand \cref{def:monomial-first-partial,def:monomial-second-partial}. In each
  formula, the product away from $i$ agrees with the corresponding updated exponent vector.
  Inserting the $i$th factor into that product gives the asserted monomial from
  \cref{def:monomial-value}; the vanishing leading coefficient handles the truncated cases. -/)
  (title := /-- Formal monomial partials as updated monomials -/)
  (latexEnv := "lemma")]
lemma monomial_partials_as_monomials {n : ℕ} (factor : polynomial_factor n)
    (i : Fin n) (x : Fin n → ℝ) :
    monomial_first_partial factor i x =
        (factor i : ℝ) *
          monomial_value (Function.update factor i (factor i - 1)) x ∧
      monomial_second_partial factor i x =
        (factor i : ℝ) * ((factor i - 1 : ℕ) : ℝ) *
          monomial_value (Function.update factor i (factor i - 2)) x := by
  constructor
  · unfold monomial_first_partial monomial_value
    by_cases hzero : factor i = 0
    · simp [hzero]
    · have hcast : (factor i : ℝ) ≠ 0 := by exact_mod_cast hzero
      apply mul_left_cancel₀ hcast
      rw [mul_assoc]
      have hprod :
          (∏ j ∈ Finset.univ.erase i, x j ^ factor j) =
            ∏ j ∈ Finset.univ.erase i,
              x j ^ Function.update factor i (factor i - 1) j := by
        apply Finset.prod_congr rfl
        intro j hj
        simp [Function.update, Finset.ne_of_mem_erase hj]
      rw [← Finset.mul_prod_erase Finset.univ
        (fun j => x j ^ Function.update factor i (factor i - 1) j)
        (Finset.mem_univ i)]
      rw [Function.update_self, hprod]
  · unfold monomial_second_partial monomial_value
    have hprod :
        (∏ j ∈ Finset.univ.erase i, x j ^ factor j) =
          ∏ j ∈ Finset.univ.erase i,
            x j ^ Function.update factor i (factor i - 2) j := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [Function.update, Finset.ne_of_mem_erase hj]
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j => x j ^ Function.update factor i (factor i - 2) j)
      (Finset.mem_univ i)]
    rw [Function.update_self, hprod]
    ring

@[blueprint "lem:monomial-partials-absolute-bound"
  (statement := /-- Let $a\in\mathbb N^n$ have total degree at most $d$. For every coordinate
  $i$ and every $x\in\mathbb R^n$,
  \[
    |\partial_i x^a|\le d\max\{1,\lVert x\rVert_\infty\}^{d-1},\qquad
    |\partial_i^2 x^a|\le d^2\max\{1,\lVert x\rVert_\infty\}^{d-2}.
  \]
  The second estimate is asserted when $d\ge2$. -/)
  (proof := /-- Rewrite the derivatives by \cref{lem:monomial-partials-as-monomials} and bound
  the updated monomials using \cref{lem:monomial-value-absolute-bound}. If $a_i>0$, the first
  updated exponent vector has total degree one less than $a$; if $a_i\ge2$, the second has total
  degree two less. Their leading coefficients are at most $d$ and $d^2$, respectively. The
  remaining cases have zero derivative. -/)
  (title := /-- Degree bounds for formal monomial partials -/)
  (latexEnv := "lemma")]
lemma monomial_partials_absolute_bound {n d : ℕ} (factor : polynomial_factor n)
    (i : Fin n) (x : Fin n → ℝ) (hdegree : (∑ j, factor j) ≤ d) (hd : 2 ≤ d) :
    |monomial_first_partial factor i x| ≤
        (d : ℝ) * max 1 ‖x‖ ^ (d - 1) ∧
      |monomial_second_partial factor i x| ≤
        (d : ℝ) ^ 2 * max 1 ‖x‖ ^ (d - 2) := by
  have hfactor_le : factor i ≤ d :=
    le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) hdegree
  have hbase : (1 : ℝ) ≤ max 1 ‖x‖ := le_max_left _ _
  constructor
  · by_cases hzero : factor i = 0
    · simp [monomial_first_partial, hzero]
    · have hone : 1 ≤ factor i := Nat.one_le_iff_ne_zero.mpr hzero
      have hsum : (∑ j, Function.update factor i (factor i - 1) j) =
          (∑ j, factor j) - 1 := by
        rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
        have hsplit : (∑ j, factor j) = factor i + ∑ j ∈ Finset.univ \ {i}, factor j :=
          Finset.sum_eq_add_sum_sdiff_singleton i factor (by simp)
        rw [hsplit]
        omega
      have hsum_le : (∑ j, Function.update factor i (factor i - 1) j) ≤ d - 1 := by
        rw [hsum]
        omega
      rw [(monomial_partials_as_monomials factor i x).1, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul (by exact_mod_cast hfactor_le)
        ((monomial_value_absolute_bound _ _).trans
          (pow_le_pow_right₀ hbase hsum_le)) (by positivity) (by positivity)
  · by_cases hsmall : factor i < 2
    · have hcases : factor i = 0 ∨ factor i = 1 := by omega
      rcases hcases with hzero | hone
      · simp [monomial_second_partial, hzero]
      · simp [monomial_second_partial, hone]
    · have htwo : 2 ≤ factor i := by omega
      have hsum : (∑ j, Function.update factor i (factor i - 2) j) =
          (∑ j, factor j) - 2 := by
        rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
        have hsplit : (∑ j, factor j) = factor i + ∑ j ∈ Finset.univ \ {i}, factor j :=
          Finset.sum_eq_add_sum_sdiff_singleton i factor (by simp)
        rw [hsplit]
        omega
      have hsum_le : (∑ j, Function.update factor i (factor i - 2) j) ≤ d - 2 := by
        rw [hsum]
        omega
      have hcoeff :
          (factor i : ℝ) * ((factor i - 1 : ℕ) : ℝ) ≤ (d : ℝ) ^ 2 := by
        have hsub : factor i - 1 ≤ d := le_trans (Nat.sub_le _ _) hfactor_le
        norm_num [pow_two]
        exact_mod_cast Nat.mul_le_mul hfactor_le hsub
      rw [(monomial_partials_as_monomials factor i x).2, abs_mul, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
      calc
        (factor i : ℝ) * ((factor i - 1 : ℕ) : ℝ) *
            |monomial_value (Function.update factor i (factor i - 2)) x| ≤
          (d : ℝ) ^ 2 *
            |monomial_value (Function.update factor i (factor i - 2)) x| :=
          mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _)
        _ ≤ (d : ℝ) ^ 2 * max 1 ‖x‖ ^ (d - 2) :=
          mul_le_mul_of_nonneg_left
            ((monomial_value_absolute_bound _ _).trans
              (pow_le_pow_right₀ hbase hsum_le)) (sq_nonneg _)

@[blueprint "lem:normalized-power-envelope"
  (statement := /-- Let $C\ge1$, $r\ge0$, and $0\le m\le q$ be integers. Then
  \[
    \max\{1,r\}^m\le C^m\left(1+(r/C)^q\right).
  \] -/)
  (proof := /-- If $r\le C$, then $\max\{1,r\}\le C$, and the result follows from the
  nonnegativity of the second summand. If $C\le r$, then $r/C\ge1$, so its $m$th power is at
  most its $q$th power. Substituting $r=C(r/C)$ gives the asserted estimate. -/)
  (title := /-- Normalized envelope for a bounded power -/)
  (latexEnv := "lemma")]
lemma normalized_power_envelope (C r : ℝ) (m q : ℕ) (hC : 1 ≤ C)
    (hr : 0 ≤ r) (hmq : m ≤ q) :
    max 1 r ^ m ≤ C ^ m * (1 + (r / C) ^ q) := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hratio : 0 ≤ r / C := div_nonneg hr hCpos.le
  rcases le_total r C with hle | hle
  · have hmax : max 1 r ≤ C := max_le hC hle
    calc
      max 1 r ^ m ≤ C ^ m := pow_le_pow_left₀ (by positivity) hmax m
      _ ≤ C ^ m * (1 + (r / C) ^ q) := by
        nlinarith [pow_nonneg hratio q, pow_nonneg hCpos.le m]
  · have hone : (1 : ℝ) ≤ r / C := (le_div_iff₀ hCpos).2 (by simpa using hle)
    have hpow : (r / C) ^ m ≤ (r / C) ^ q := pow_le_pow_right₀ hone hmq
    have hrone : (1 : ℝ) ≤ r := le_trans hC hle
    rw [max_eq_right hrone]
    calc
      r ^ m = C ^ m * (r / C) ^ m := by
        rw [div_pow]
        field_simp [ne_of_gt hCpos]
      _ ≤ C ^ m * (r / C) ^ q :=
        mul_le_mul_of_nonneg_left hpow (pow_nonneg hCpos.le m)
      _ ≤ C ^ m * (1 + (r / C) ^ q) := by
        nlinarith [pow_nonneg hratio q, pow_nonneg hCpos.le m]

@[blueprint "lem:polynomial-score-scaled-feature-envelope"
  (statement := /-- Let $\mathcal K$ have degree at most $d\ge2$, let $B>0$ and $C_t\ge1$,
  and put $u=dBC_t^d$ and $H=8(1+du+u^2)$. For every incident factor $a$, the scaled feature
  $B\partial_i^2f_a$ satisfies
  \[
    |B\partial_i^2f_a(x)|\le H\left(1+
      (\lVert x\rVert_\infty/C_t)^{2(d-1)}\right).
  \]
  For every two incident factors $a,b$, the same envelope bounds
  $\frac12B^2(\partial_if_a)(\partial_if_b)$. -/)
  (proof := /-- Apply \cref{lem:monomial-partials-absolute-bound} to the first two formal
  derivatives and use \cref{lem:normalized-power-envelope} with exponent $2(d-1)$. The
  coefficient of the scaled second derivative is at most $du$, while that of the product of
  first derivatives is at most $u^2/2$. Both are bounded by $H=8(1+du+u^2)$. -/)
  (title := /-- Common envelope for scaled score features -/)
  (latexEnv := "lemma")]
lemma polynomial_score_scaled_feature_envelope {n d Ct : ℕ}
    (factors : Finset (polynomial_factor n)) (i : Fin n) (B : ℝ)
    (hdegree : family_degree_at_most factors d) (hd : 2 ≤ d)
    (hB : 0 < B) (hCt : 1 ≤ Ct) :
    let u := (d : ℝ) * B * (Ct : ℝ) ^ d
    let H := 8 * (1 + (d : ℝ) * u + u ^ 2)
    (∀ a ∈ factors_at factors i, ∀ x,
      |B * monomial_second_partial a i x| ≤
        H * (1 + (‖x‖ / (Ct : ℝ)) ^ (2 * (d - 1)))) ∧
    (∀ a ∈ factors_at factors i, ∀ b ∈ factors_at factors i, ∀ x,
      |(1 / 2 : ℝ) * B ^ 2 *
          (monomial_first_partial a i x * monomial_first_partial b i x)| ≤
        H * (1 + (‖x‖ / (Ct : ℝ)) ^ (2 * (d - 1)))) := by
  dsimp only
  let u : ℝ := (d : ℝ) * B * (Ct : ℝ) ^ d
  let H : ℝ := 8 * (1 + (d : ℝ) * u + u ^ 2)
  have hCtReal : (1 : ℝ) ≤ Ct := by exact_mod_cast hCt
  have hCtPos : (0 : ℝ) < Ct := lt_of_lt_of_le zero_lt_one hCtReal
  have hdReal : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hd)
  have hu : 0 < u := by dsimp [u]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hq : d - 2 ≤ 2 * (d - 1) := by omega
  have hpowLin : (Ct : ℝ) ^ (d - 2) ≤ (Ct : ℝ) ^ d :=
    pow_le_pow_right₀ hCtReal (Nat.sub_le d 2)
  have hpowQuad : (Ct : ℝ) ^ (2 * (d - 1)) ≤ (Ct : ℝ) ^ (2 * d) := by
    apply pow_le_pow_right₀ hCtReal
    omega
  constructor
  · intro a ha x
    have haFactor : a ∈ factors := (Finset.mem_filter.mp ha).1
    have hpartial := (monomial_partials_absolute_bound a i x
      (hdegree a haFactor) hd).2
    have hnorm := normalized_power_envelope (Ct : ℝ) ‖x‖ (d - 2)
      (2 * (d - 1)) hCtReal (norm_nonneg x) hq
    have hcoef : B * (d : ℝ) ^ 2 * (Ct : ℝ) ^ (d - 2) ≤ H := by
      have hstep : B * (d : ℝ) ^ 2 * (Ct : ℝ) ^ (d - 2) ≤ (d : ℝ) * u := by
        dsimp [u]
        have := mul_le_mul_of_nonneg_left hpowLin (by positivity : 0 ≤ B * (d : ℝ) ^ 2)
        nlinarith
      dsimp [H]
      nlinarith [hu.le, hdReal.le]
    rw [abs_mul, abs_of_pos hB]
    calc
      B * |monomial_second_partial a i x| ≤
          B * ((d : ℝ) ^ 2 * max 1 ‖x‖ ^ (d - 2)) :=
        mul_le_mul_of_nonneg_left hpartial hB.le
      _ ≤ B * ((d : ℝ) ^ 2 *
          ((Ct : ℝ) ^ (d - 2) *
            (1 + (‖x‖ / (Ct : ℝ)) ^ (2 * (d - 1))))) := by
        gcongr
      _ = (B * (d : ℝ) ^ 2 * (Ct : ℝ) ^ (d - 2)) *
          (1 + (‖x‖ / (Ct : ℝ)) ^ (2 * (d - 1))) := by ring
      _ ≤ H * (1 + (‖x‖ / (Ct : ℝ)) ^ (2 * (d - 1))) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
  · intro a ha b hb x
    have haFactor : a ∈ factors := (Finset.mem_filter.mp ha).1
    have hbFactor : b ∈ factors := (Finset.mem_filter.mp hb).1
    have haPartial := (monomial_partials_absolute_bound a i x
      (hdegree a haFactor) hd).1
    have hbPartial := (monomial_partials_absolute_bound b i x
      (hdegree b hbFactor) hd).1
    have hprod :
        |monomial_first_partial a i x * monomial_first_partial b i x| ≤
          (d : ℝ) ^ 2 * max 1 ‖x‖ ^ (2 * (d - 1)) := by
      rw [abs_mul]
      calc
        |monomial_first_partial a i x| * |monomial_first_partial b i x| ≤
            ((d : ℝ) * max 1 ‖x‖ ^ (d - 1)) *
              ((d : ℝ) * max 1 ‖x‖ ^ (d - 1)) :=
          mul_le_mul haPartial hbPartial (abs_nonneg _) (by positivity)
        _ = (d : ℝ) ^ 2 * max 1 ‖x‖ ^ (2 * (d - 1)) := by
          calc
            ((d : ℝ) * max 1 ‖x‖ ^ (d - 1)) *
                ((d : ℝ) * max 1 ‖x‖ ^ (d - 1)) =
              (d : ℝ) ^ 2 *
                (max 1 ‖x‖ ^ (d - 1) * max 1 ‖x‖ ^ (d - 1)) := by ring
            _ = (d : ℝ) ^ 2 * max 1 ‖x‖ ^ ((d - 1) + (d - 1)) := by
              rw [pow_add]
            _ = (d : ℝ) ^ 2 * max 1 ‖x‖ ^ (2 * (d - 1)) := by
              congr 2
              omega
    have hnorm := normalized_power_envelope (Ct : ℝ) ‖x‖ (2 * (d - 1))
      (2 * (d - 1)) hCtReal (norm_nonneg x) le_rfl
    have hcoef : (1 / 2 : ℝ) * B ^ 2 * (d : ℝ) ^ 2 *
        (Ct : ℝ) ^ (2 * (d - 1)) ≤ H := by
      have hstep : B ^ 2 * (d : ℝ) ^ 2 * (Ct : ℝ) ^ (2 * (d - 1)) ≤ u ^ 2 := by
        calc
          B ^ 2 * (d : ℝ) ^ 2 * (Ct : ℝ) ^ (2 * (d - 1)) ≤
              B ^ 2 * (d : ℝ) ^ 2 * (Ct : ℝ) ^ (2 * d) :=
            mul_le_mul_of_nonneg_left hpowQuad (by positivity)
          _ = u ^ 2 := by
            dsimp [u]
            rw [show 2 * d = d * 2 by omega, pow_mul]
            ring
      dsimp [H]
      nlinarith [hstep, hu.le]
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
      abs_of_nonneg (sq_nonneg B)]
    calc
      (1 / 2 : ℝ) * B ^ 2 *
          |monomial_first_partial a i x * monomial_first_partial b i x| ≤
        (1 / 2 : ℝ) * B ^ 2 *
          ((d : ℝ) ^ 2 * max 1 ‖x‖ ^ (2 * (d - 1))) := by
            gcongr
      _ ≤ (1 / 2 : ℝ) * B ^ 2 *
          ((d : ℝ) ^ 2 * ((Ct : ℝ) ^ (2 * (d - 1)) *
            (1 + (‖x‖ / (Ct : ℝ)) ^ (2 * (d - 1))))) := by
            gcongr
      _ = ((1 / 2 : ℝ) * B ^ 2 * (d : ℝ) ^ 2 *
          (Ct : ℝ) ^ (2 * (d - 1))) *
            (1 + (‖x‖ / (Ct : ℝ)) ^ (2 * (d - 1))) := by ring
      _ ≤ H * (1 + (‖x‖ / (Ct : ℝ)) ^ (2 * (d - 1))) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)

@[blueprint "lem:finite-feature-empirical-deviation"
  (statement := /-- Let $S$ be a finite index set, let $c_j\in\mathbb R$, and let
  $F_j:X\to\mathbb R$ be integrable functions. Suppose that
  $\sum_{j\in S}|c_j|\le C$, and that the empirical mean of every $F_j$ differs from its
  integral by at most $\delta\ge0$. Then the empirical mean of
  $\sum_{j\in S}c_jF_j$ differs from its integral by at most $C\delta$. -/)
  (proof := /-- Finite-sum linearity rewrites the deviation of the linear combination as the
  sum, over $j\in S$, of $c_j$ times the individual deviation of $F_j$. The triangle
  inequality bounds its absolute value by the sum of $|c_j|$ times the corresponding absolute
  deviation. Applying the two assumed bounds gives $C\delta$. -/)
  (title := /-- Empirical deviation of a finite linear combination -/)
  (latexEnv := "lemma")]
lemma finite_feature_empirical_deviation {ι X : Type} [MeasurableSpace X]
    {M : ℕ} (s : Finset ι) (c : ι → ℝ) (F : ι → X → ℝ)
    (observations : Fin M → X) (p : MeasureTheory.Measure X) (C delta : ℝ)
    (hintegrable : ∀ j ∈ s, MeasureTheory.Integrable (F j) p)
    (hcoeff : ∑ j ∈ s, |c j| ≤ C) (hdelta : 0 ≤ delta)
    (hdeviation : ∀ j ∈ s,
      |(M : ℝ)⁻¹ * ∑ m, F j (observations m) - ∫ x, F j x ∂p| ≤ delta) :
    |(M : ℝ)⁻¹ * ∑ m, ∑ j ∈ s, c j * F j (observations m) -
        ∫ x, ∑ j ∈ s, c j * F j x ∂p| ≤ C * delta := by
  have hempirical :
      (M : ℝ)⁻¹ * ∑ m, ∑ j ∈ s, c j * F j (observations m) =
        ∑ j ∈ s, c j * ((M : ℝ)⁻¹ * ∑ m, F j (observations m)) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hpopulation :
      (∫ x, ∑ j ∈ s, c j * F j x ∂p) =
        ∑ j ∈ s, c j * ∫ x, F j x ∂p := by
    rw [MeasureTheory.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [MeasureTheory.integral_const_mul]
    · intro j hj
      exact (hintegrable j hj).const_mul (c j)
  rw [hempirical, hpopulation, ← Finset.sum_sub_distrib]
  calc
    |∑ j ∈ s,
        (c j * ((M : ℝ)⁻¹ * ∑ m, F j (observations m)) -
          c j * ∫ x, F j x ∂p)| ≤
        ∑ j ∈ s,
          |c j * ((M : ℝ)⁻¹ * ∑ m, F j (observations m)) -
            c j * ∫ x, F j x ∂p| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ s, |c j| *
          |(M : ℝ)⁻¹ * ∑ m, F j (observations m) - ∫ x, F j x ∂p| := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← mul_sub, abs_mul]
    _ ≤ ∑ j ∈ s, |c j| * delta := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hdeviation j hj) (abs_nonneg _)
    _ = (∑ j ∈ s, |c j|) * delta := by rw [Finset.sum_mul]
    _ ≤ C * delta := mul_le_mul_of_nonneg_right hcoeff hdelta

@[blueprint "lem:energy-partials-eq-sum-factors-at"
  (statement := /-- Let $\mathcal K$ be a finite family of monomial factors on $\mathbb R^n$
  and fix $i\in[n]$. For every parameter vector $\theta$ and every $x\in\mathbb R^n$, each of
  the first two $i$th energy derivatives is equal to the corresponding sum over the factors
  incident to $i$. -/)
  (proof := /-- By \cref{def:factors-at,def:factor-support}, a factor omitted from the incident
  subfamily has $i$th exponent zero. Its first and second $i$th partial derivatives therefore
  vanish by \cref{def:monomial-first-partial,def:monomial-second-partial}. Removing these zero
  summands from the finite sums in \cref{def:energy-first-partial,def:energy-second-partial}
  proves both identities. -/)
  (title := /-- Energy derivatives restricted to incident factors -/)
  (latexEnv := "lemma")]
lemma energy_partials_eq_sum_factors_at {n : ℕ}
    (factors : Finset (polynomial_factor n)) (theta : polynomial_factor n → ℝ)
    (i : Fin n) (x : Fin n → ℝ) :
    energy_first_partial factors theta i x =
        ∑ factor ∈ factors_at factors i,
          theta factor * monomial_first_partial factor i x ∧
      energy_second_partial factors theta i x =
        ∑ factor ∈ factors_at factors i,
          theta factor * monomial_second_partial factor i x := by
  have hzero (factor : polynomial_factor n) (hfactor : factor ∈ factors)
      (hnot : factor ∉ factors_at factors i) : factor i = 0 := by
    simp only [factors_at, Finset.mem_filter, hfactor, true_and, factor_support,
      Finset.mem_filter, Finset.mem_univ, true_and] at hnot
    omega
  constructor
  · rw [energy_first_partial]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro factor hfactor hnot
    simp [monomial_first_partial, hzero factor hfactor hnot]
  · rw [energy_second_partial]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro factor hfactor hnot
    simp [monomial_second_partial, hzero factor hfactor hnot]

@[blueprint "lem:feasible-local-score-deviation-of-features"
  (statement := /-- Fix a finite monomial family $\mathcal K$, a coordinate $i$, a radius
  $B>0$, and a feasible parameter vector $\theta$. Scale every incident second-derivative
  feature by $B$ and every product of two incident first-derivative features by $B^2/2$.
  If all these features are integrable and each empirical mean differs from its population
  mean by at most $\delta\ge0$, then the empirical local score of $\theta$ differs from its
  population value by at most $2\delta$. -/)
  (proof := /-- By \cref{lem:energy-partials-eq-sum-factors-at}, expanding
  \cref{def:energy-first-partial,def:energy-second-partial} in
  \cref{def:local-score-matching-loss} expresses the local score as the sum of a linear
  combination of the scaled second-derivative features and a linear combination of the scaled
  products of first derivatives. Feasibility from \cref{def:parameter-feasible} makes the absolute
  coefficient sum of the first combination at most one. The coefficient sum of the second is
  the square of the first and is also at most one. Apply
  \cref{lem:finite-feature-empirical-deviation} to both combinations and use the triangle
  inequality. -/)
  (title := /-- Feasible score deviation from feature deviations -/)
  (latexEnv := "lemma")]
lemma feasible_local_score_deviation_of_features {n M : ℕ}
    (factors : Finset (polynomial_factor n)) (theta : polynomial_factor n → ℝ)
    (i : Fin n) (B : ℝ) (observations : Fin M → (Fin n → ℝ))
    (p : MeasureTheory.Measure (Fin n → ℝ)) (delta : ℝ)
    (hB : 0 < B) (hfeasible : parameter_feasible factors B theta)
    (hdelta : 0 ≤ delta)
    (hlin_integrable : ∀ a ∈ factors_at factors i,
      MeasureTheory.Integrable (fun x => B * monomial_second_partial a i x) p)
    (hquad_integrable : ∀ a ∈ factors_at factors i, ∀ b ∈ factors_at factors i,
      MeasureTheory.Integrable (fun x =>
        (1 / 2 : ℝ) * B ^ 2 *
          (monomial_first_partial a i x * monomial_first_partial b i x)) p)
    (hlin_deviation : ∀ a ∈ factors_at factors i,
      |(M : ℝ)⁻¹ * ∑ m, B * monomial_second_partial a i (observations m) -
        ∫ x, B * monomial_second_partial a i x ∂p| ≤ delta)
    (hquad_deviation : ∀ a ∈ factors_at factors i, ∀ b ∈ factors_at factors i,
      |(M : ℝ)⁻¹ * ∑ m, (1 / 2 : ℝ) * B ^ 2 *
          (monomial_first_partial a i (observations m) *
            monomial_first_partial b i (observations m)) -
        ∫ x, (1 / 2 : ℝ) * B ^ 2 *
          (monomial_first_partial a i x * monomial_first_partial b i x) ∂p| ≤ delta) :
    |empirical_local_score_matching_loss factors theta i observations -
      population_local_score_matching_loss factors theta i p| ≤ 2 * delta := by
  classical
  let J := factors_at factors i
  let lin : polynomial_factor n → (Fin n → ℝ) → ℝ := fun a x =>
    B * monomial_second_partial a i x
  let quad : (polynomial_factor n × polynomial_factor n) → (Fin n → ℝ) → ℝ :=
    fun ab x => (1 / 2 : ℝ) * B ^ 2 *
      (monomial_first_partial ab.1 i x * monomial_first_partial ab.2 i x)
  let clin : polynomial_factor n → ℝ := fun a => theta a / B
  let cquad : (polynomial_factor n × polynomial_factor n) → ℝ := fun ab =>
    theta ab.1 * theta ab.2 / B ^ 2
  have hBne : B ≠ 0 := ne_of_gt hB
  have hsum : ∑ a ∈ J, |theta a| ≤ B := hfeasible i
  have hclin : ∑ a ∈ J, |clin a| ≤ 1 := by
    simp only [clin, abs_div, abs_of_pos hB]
    rw [← Finset.sum_div]
    exact (div_le_one hB).2 hsum
  have hcquad : ∑ ab ∈ J ×ˢ J, |cquad ab| ≤ 1 := by
    have heq : ∑ ab ∈ J ×ˢ J, |cquad ab| =
        (∑ a ∈ J, |theta a|) ^ 2 / B ^ 2 := by
      simp only [cquad, abs_div, abs_mul, abs_pow, abs_of_pos hB]
      rw [Finset.sum_product]
      simp_rw [← Finset.sum_div]
      rw [← Finset.sum_mul_sum]
      ring
    rw [heq]
    exact (div_le_one (sq_pos_of_pos hB)).2
      ((sq_le_sq₀ (by positivity) hB.le).2 hsum)
  have hlin_bound :
      |(M : ℝ)⁻¹ * ∑ m, ∑ a ∈ J, clin a * lin a (observations m) -
          ∫ x, ∑ a ∈ J, clin a * lin a x ∂p| ≤ delta := by
    simpa [J, lin] using finite_feature_empirical_deviation J clin lin observations p
      1 delta (by simpa [J, lin] using hlin_integrable) hclin hdelta
      (by simpa [J, lin] using hlin_deviation)
  have hquad_bound :
      |(M : ℝ)⁻¹ * ∑ m, ∑ ab ∈ J ×ˢ J, cquad ab * quad ab (observations m) -
          ∫ x, ∑ ab ∈ J ×ˢ J, cquad ab * quad ab x ∂p| ≤ delta := by
    simpa [J, quad] using finite_feature_empirical_deviation (J ×ˢ J) cquad quad
      observations p 1 delta
      (by
        intro ab hab
        simp only [Finset.mem_product] at hab
        exact hquad_integrable ab.1 hab.1 ab.2 hab.2)
      hcquad hdelta
      (by
        intro ab hab
        simp only [Finset.mem_product] at hab
        exact hquad_deviation ab.1 hab.1 ab.2 hab.2)
  have hloss (x : Fin n → ℝ) :
      local_score_matching_loss factors theta i x =
        (∑ a ∈ J, clin a * lin a x) +
          ∑ ab ∈ J ×ˢ J, cquad ab * quad ab x := by
    rw [local_score_matching_loss,
      (energy_partials_eq_sum_factors_at factors theta i x).1,
      (energy_partials_eq_sum_factors_at factors theta i x).2]
    simp only [J, clin, lin, cquad, quad, Finset.sum_product, Prod.fst, Prod.snd]
    rw [pow_two, Finset.sum_mul, Finset.mul_sum]
    field_simp [hBne]
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  have hlin_int : MeasureTheory.Integrable (fun x => ∑ a ∈ J, clin a * lin a x) p := by
    apply MeasureTheory.integrable_finsetSum J
    intro a ha
    exact (hlin_integrable a (by simpa [J] using ha)).const_mul (clin a)
  have hquad_int :
      MeasureTheory.Integrable (fun x => ∑ ab ∈ J ×ˢ J, cquad ab * quad ab x) p := by
    apply MeasureTheory.integrable_finsetSum (J ×ˢ J)
    intro ab hab
    simp only [Finset.mem_product] at hab
    exact (hquad_integrable ab.1 (by simpa [J] using hab.1) ab.2
      (by simpa [J] using hab.2)).const_mul (cquad ab)
  unfold empirical_local_score_matching_loss population_local_score_matching_loss
  simp_rw [hloss]
  rw [MeasureTheory.integral_add hlin_int hquad_int]
  have hsplit :
      (M : ℝ)⁻¹ *
          ∑ m, ((∑ a ∈ J, clin a * lin a (observations m)) +
            ∑ ab ∈ J ×ˢ J, cquad ab * quad ab (observations m)) -
        ((∫ x, ∑ a ∈ J, clin a * lin a x ∂p) +
          ∫ x, ∑ ab ∈ J ×ˢ J, cquad ab * quad ab x ∂p) =
      ((M : ℝ)⁻¹ * ∑ m, ∑ a ∈ J, clin a * lin a (observations m) -
        ∫ x, ∑ a ∈ J, clin a * lin a x ∂p) +
      ((M : ℝ)⁻¹ * ∑ m, ∑ ab ∈ J ×ˢ J, cquad ab * quad ab (observations m) -
        ∫ x, ∑ ab ∈ J ×ˢ J, cquad ab * quad ab x ∂p) := by
    rw [Finset.sum_add_distrib]
    ring
  rw [hsplit]
  calc
    |_ + _| ≤
        |(M : ℝ)⁻¹ * ∑ m, ∑ a ∈ J, clin a * lin a (observations m) -
          ∫ x, ∑ a ∈ J, clin a * lin a x ∂p| +
        |(M : ℝ)⁻¹ * ∑ m, ∑ ab ∈ J ×ˢ J, cquad ab * quad ab (observations m) -
          ∫ x, ∑ ab ∈ J ×ˢ J, cquad ab * quad ab x ∂p| := abs_add_le _ _
    _ ≤ delta + delta := add_le_add hlin_bound hquad_bound
    _ = 2 * delta := by ring

@[blueprint "lem:incident-factor-card-bound"
  (statement := /-- Let $n,d\in\mathbb N$, let $\mathcal K$ be a finite family of monomial
  factors on $\mathbb R^n$ of total degree at most $d$, and fix $i\in[n]$. Then the number of
  factors incident to $i$ is at most $(n+d)^d$. -/)
  (proof := /-- Adjoin one slack coordinate to every exponent vector, with exponent equal to
  $d$ minus its total degree. This injects $\mathcal K$ into the set of $(n+1)$-tuples of
  nonnegative integers summing to $d$. By the stars-and-bars count this set has cardinality
  $\binom{n+d}{d}$, which is at most $(n+d)^d$. The incident subfamily is a subset of
  $\mathcal K$, so it satisfies the same bound. -/)
  (title := /-- Cardinality bound for incident polynomial factors -/)
  (latexEnv := "lemma")]
lemma incident_factor_card_bound {n d : ℕ}
    (factors : Finset (polynomial_factor n)) (i : Fin n)
    (hdegree : family_degree_at_most factors d) :
    (factors_at factors i).card ≤ (n + d) ^ d := by
  classical
  let code : polynomial_factor n → Fin (n + 1) → ℕ := fun factor j =>
    if hj : (j : ℕ) < n then factor ⟨j, hj⟩ else d - ∑ k, factor k
  have hcode_mem (factor : polynomial_factor n) (hfactor : factor ∈ factors) :
      code factor ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (n + 1))) d := by
    rw [Finset.mem_piAntidiag]
    constructor
    · rw [Fin.sum_univ_castSucc]
      simp only [code, Fin.val_castSucc, Fin.is_lt, ↓reduceDIte, Fin.val_last, lt_self_iff_false,
        ↓reduceDIte]
      exact Nat.add_sub_of_le (hdegree factor hfactor)
    · simp
  have hcode_inj : Set.InjOn code (factors : Set (polynomial_factor n)) := by
    intro factor₁ hfactor₁ factor₂ hfactor₂ heq
    funext j
    have hj := congr_fun heq j.castSucc
    simpa [code] using hj
  have hcard_factors : factors.card ≤
      (Finset.piAntidiag (Finset.univ : Finset (Fin (n + 1))) d).card :=
    Finset.card_le_card_of_injOn code
      (fun factor hfactor => hcode_mem factor hfactor) hcode_inj
  have hcard_antidiag :
      (Finset.piAntidiag (Finset.univ : Finset (Fin (n + 1))) d).card =
        (n + d).choose d := by
    rw [← Finset.map_sym_eq_piAntidiag]
    simp [Sym.card_sym_eq_choose]
  calc
    (factors_at factors i).card ≤ factors.card := Finset.card_filter_le _ _
    _ ≤ (Finset.piAntidiag (Finset.univ : Finset (Fin (n + 1))) d).card := hcard_factors
    _ = (n + d).choose d := hcard_antidiag
    _ ≤ (n + d) ^ d := Nat.choose_le_pow _ _

@[blueprint "lem:local-score-loss-eq-zero-of-no-factors-at"
  (statement := /-- Let $\mathcal K$ be a finite family of monomial factors on $\mathbb R^n$,
  let $i\in[n]$, and suppose that no factor of $\mathcal K$ is incident to $i$. Then the local
  score-matching loss in coordinate $i$ vanishes for every parameter vector and every point of
  $\mathbb R^n$. -/)
  (proof := /-- By \cref{lem:energy-partials-eq-sum-factors-at}, both energy derivatives are
  sums over the empty incident subfamily, hence vanish. Substitution into
  \cref{def:local-score-matching-loss} gives zero. -/)
  (title := /-- Vanishing local score when no factor is incident -/)
  (latexEnv := "lemma")]
lemma local_score_loss_eq_zero_of_no_factors_at {n : ℕ}
    (factors : Finset (polynomial_factor n)) (theta : polynomial_factor n → ℝ)
    (i : Fin n) (x : Fin n → ℝ) (h : factors_at factors i = ∅) :
    local_score_matching_loss factors theta i x = 0 := by
  have hfirst : energy_first_partial factors theta i x = 0 := by
    rw [(energy_partials_eq_sum_factors_at factors theta i x).1, h]
    simp
  have hsecond : energy_second_partial factors theta i x = 0 := by
    rw [(energy_partials_eq_sum_factors_at factors theta i x).2, h]
    simp
  simp [local_score_matching_loss, hfirst, hsecond]

@[blueprint "lem:uniform-empirical-score-concentration-empty-case"
  (statement := /-- Let $n,d,C_{\rm conc},C_t\in\mathbb N$, let $A_0,u\in\mathbb R$ with
  $A_0>1$, let $\mathcal K$ be a finite factor family on $\mathbb R^n$, and fix $i\in[n]$.
  If $C_t\ge1$ and no factor of $\mathcal K$ is incident to $i$, then the conclusion of the
  uniform empirical-score concentration estimate holds with $A_{\rm conc}=1$. -/)
  (proof := /-- Set $A_{\rm conc}=1$. Its required upper bound follows from $A_0>1$. By
  \cref{lem:local-score-loss-eq-zero-of-no-factors-at}, every samplewise local loss is zero;
  consequently both \cref{def:empirical-local-score-matching-loss} and
  \cref{def:population-local-score-matching-loss} vanish for every parameter. The uniform
  deviation event is therefore the whole probability space. Since $i\in[n]$, $C_t\ge1$, and
  $\rho\ge1$, the quantity $(\rho nC_t)^{-1}$ is positive, so the probability one of this event
  is strictly greater than $1-(\rho nC_t)^{-1}$. -/)
  (title := /-- Uniform score concentration with no incident factors -/)
  (latexEnv := "lemma")]
lemma uniform_empirical_score_concentration_empty_case {n d Cconc Ct : ℕ}
    (factors : Finset (polynomial_factor n)) (i : Fin n) (B u A0 : ℝ)
    (p : MeasureTheory.Measure (Fin n → ℝ))
    (hA0 : 1 < A0) (hCt : 1 ≤ Ct) (hempty : factors_at factors i = ∅) :
    ∃ Aconc : ℝ,
      1 ≤ Aconc ∧
      Aconc ≤ max A0 (u ^ (Cconc * d ^ 2 * interaction_order factors)) ∧
      ∀ (M : ℕ) (Ω : Type) [MeasurableSpace Ω]
        (mu : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure mu]
        (samples : Fin M → Ω → (Fin n → ℝ)) (rho epsilon : ℝ),
        1 ≤ rho → 0 < epsilon →
        1 - 1 / (rho * (n : ℝ) * (Ct : ℝ)) <
          mu.real {omega | ∀ theta, parameter_feasible factors B theta →
            |empirical_local_score_matching_loss factors theta i
                (fun m => samples m omega) -
              population_local_score_matching_loss factors theta i p| ≤
                epsilon / (2 * Aconc)} := by
  refine ⟨1, le_rfl, ?_, ?_⟩
  · exact le_trans hA0.le (le_max_left _ _)
  · intro M Ω instMeas mu instProb samples rho epsilon hrho hepsilon
    have hevent :
        {omega | ∀ theta, parameter_feasible factors B theta →
          |empirical_local_score_matching_loss factors theta i
              (fun m => samples m omega) -
            population_local_score_matching_loss factors theta i p| ≤
              epsilon / (2 * (1 : ℝ))} =
          Set.univ := by
      ext omega
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro theta htheta
      have hempirical : empirical_local_score_matching_loss factors theta i
          (fun m => samples m omega) = 0 := by
        simp [empirical_local_score_matching_loss,
          local_score_loss_eq_zero_of_no_factors_at factors theta i _ hempty]
      have hpopulation : population_local_score_matching_loss factors theta i p = 0 := by
        simp [population_local_score_matching_loss,
          local_score_loss_eq_zero_of_no_factors_at factors theta i _ hempty]
      rw [hempirical, hpopulation]
      norm_num
      linarith
    rw [hevent]
    have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
    have hCtReal : (0 : ℝ) < Ct := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hCt)
    have hdenom : 0 < rho * (n : ℝ) * (Ct : ℝ) := by positivity
    simpa using sub_lt_self (1 : ℝ) (one_div_pos.mpr hdenom)

@[blueprint "lem:uniform-empirical-score-concentration"
  (statement := /-- There exist an absolute constant $A_0>1$ and a positive integer
  $C_{\rm conc}$ with the following property. Let $n,d\in\mathbb N$, let $\mathcal K$ be a
  finite family of monomial factors on $\mathbb R^n$, let $\theta^*$ be a parameter vector,
  let $i\in[n]$, let $B,k\in\mathbb R$, let $C_t\in\mathbb N$, and let $p$ be a probability
  measure on $\mathbb R^n$. Assume that $\mathcal K$ has degree at most $d$, that $p$ is the
  unit-base polynomial exponential family generated by $(\mathcal K,\theta^*)$, that $B>0$,
  that $\theta^*$ is feasible at radius $B$, that
  \[
    1+2^{-10}\le dBC_t^d,
  \]
  and that $p$ satisfies the tail-decay condition with parameters $(d,k,C_t)$. Then there is
  a real number $A_{\rm conc}$ such that
  \[
    1\le A_{\rm conc}\le
    \max\{A_0,(dBC_t^d)^{C_{\rm conc}d^2\operatorname{ord}(\mathcal K)}\}.
  \]
  For every $M\in\mathbb N$, every probability space $(\Omega,\mathcal F,\mu)$, every family
  $(X_m)_{m=1}^M$ of independent random variables with common distribution $p$, and every
  $\rho,\epsilon\in\mathbb R$ satisfying
  \[
    \rho\ge1,\qquad 0<\epsilon\le1,
    \qquad M\ge\frac{\rho n^{d+1}A_{\rm conc}^4}{\epsilon^2},
  \]
  one has
  \[
    \mu\!\left\{\omega:\ \text{for every $\theta$ feasible at radius $B$},\
      \left|\mathcal L_i^{(M)}(\theta;(X_m(\omega))_{m=1}^M)
        -\mathcal L_i(\theta;p)\right|
      \le \frac{\epsilon}{2A_{\rm conc}}\right\}
      >1-\frac1{\rho nC_t}.
  \] -/)
  (proof := /-- Take the absolute constants \(A_0\) and \(C_{\rm conc}\) from
  \cref{lem:uniform-score-constant-absorption}, and fix an admissible model. Put
  \(u=dBC_t^d\), \(w=\operatorname{ord}(\mathcal K)\), and let \(J\) be the set of factors
  incident to \(i\), as in \cref{def:factors-at,def:interaction-order}. If \(J\) is empty,
  \cref{lem:uniform-empirical-score-concentration-empty-case} supplies
  \(A_{\rm conc}=1\) and the desired probability estimate. Hence assume that \(J\) is
  nonempty; then \(w\geq1\).

  Put \(P=(n+d)^d\), \(q=2P^2\), and form the feature family consisting of
  \(B\partial_i^2f_a\) for \(a\in J\) and
  \(\frac12B^2\partial_if_a\partial_if_b\) for \((a,b)\in J^2\).
  By \cref{lem:incident-factor-card-bound}, \(|J|\leq P\); therefore the feature family has
  positive cardinality at most
  \[
    |J|+|J|^2\leq 2P^2=q=2(n+d)^{2d}.                                \tag{1}
  \]
  By \cref{lem:feasible-local-score-deviation-of-features}, the feasibility condition from
  \cref{def:parameter-feasible} ensures that if every feature mean differs from its population
  mean by at most \(\delta\), then
  \[
    \sup_{\theta\ {\rm feasible}}
      |\mathcal L_i^{(M)}(\theta)-\mathcal L_i(\theta)|\leq2\delta.  \tag{2}
  \]

  Let
  \[
    H=8(1+du+u^2).
  \]
  The tail condition \cref{def:tail-decay-condition} implies \(d\geq2\) and \(C_t\geq1\).
  Hence \cref{lem:polynomial-score-scaled-feature-envelope} shows that every feature \(Y\)
  satisfies
  \[
    |Y(x)|\leq H\left\{1+
      \left(\frac{\lVert x\rVert_\infty}{C_t}\right)^{2(d-1)}\right\}. \tag{3}
  \]

  Now fix \(M,\rho,\epsilon\) as in the statement and define
  \[
    r=\max\{2,\lceil\log(8q\rho nC_t)\rceil\}.
  \]
  By \cref{def:iid-samples} and
  \cref{lem:polynomial-feature-empirical-moment-bound}, every feature is integrable, its
  empirical deviation is almost everywhere strongly measurable, and
  \[
    \left\lVert\frac1M\sum_{m=1}^M Y(X_m)-\mathbb EY\right\rVert_r
      \leq R:=4096H\left(\sqrt{\frac rM}+r^3M^{-1+1/r}\right).      \tag{4}
  \]
  The sample-size estimate supplied below makes \(eR\leq\delta\), where
  \(\delta=\epsilon/(4A_{\rm conc})\). Applying
  \cref{lem:finite-feature-uniform-probability} to the finite feature family gives the
  simultaneous deviation event probability at least \(1-|S|e^{-r}\). By
  \cref{lem:uniform-score-cutoff-failure-bound}, \(|S|e^{-r}< (\rho nC_t)^{-1}\).

  Finally apply \cref{lem:uniform-score-constant-absorption} with the values of \(u,H,q,w\)
  above. It supplies \(A_{\rm conc}\) satisfying
  \[
    1\leq A_{\rm conc}\leq
      \max\{A_0,u^{C_{\rm conc}d^2w}\}
  \]
  and turns the simultaneous bound into
  \(\delta=\epsilon/(4A_{\rm conc})\) under the asserted lower bound on \(M\).
  Equation (2) then gives the required uniform deviation
  \(\epsilon/(2A_{\rm conc})\). The simultaneous feature event is contained in this uniform
  score event, whose probability is therefore strictly larger than
  \(1-(\rho nC_t)^{-1}\), as required. -/)
  (title := /-- Uniform concentration of the feasible empirical score -/)
  (latexEnv := "lemma")]
lemma uniform_empirical_score_concentration :
    ∃ A0 : ℝ, 1 < A0 ∧
      ∃ Cconc : ℕ, 0 < Cconc ∧
        ∀ {n : ℕ} (d : ℕ)
        (factors : Finset (polynomial_factor n)) (thetaStar : polynomial_factor n → ℝ)
        (i : Fin n) (B tailRate : ℝ) (Ct : ℕ) (p : MeasureTheory.Measure (Fin n → ℝ))
        [MeasureTheory.IsProbabilityMeasure p],
        family_degree_at_most factors d →
        unit_base_polynomial_exponential_family factors thetaStar p →
        0 < B → parameter_feasible factors B thetaStar →
        1 + (1 / 1024 : ℝ) ≤ (d : ℝ) * B * (Ct : ℝ) ^ d →
        tail_decay_condition d tailRate Ct p →
        ∃ Aconc : ℝ,
          1 ≤ Aconc ∧
          Aconc ≤
            max A0 (((d : ℝ) * B * (Ct : ℝ) ^ d) ^
              (Cconc * d ^ 2 * interaction_order factors)) ∧
          ∀ (M : ℕ) (Ω : Type) [MeasurableSpace Ω]
            (mu : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure mu]
            (samples : Fin M → Ω → (Fin n → ℝ)) (rho epsilon : ℝ),
            iid_samples mu p samples →
            1 ≤ rho → 0 < epsilon → epsilon ≤ 1 →
            rho * (n : ℝ) ^ (d + 1) * Aconc ^ 4 / epsilon ^ 2 ≤ (M : ℝ) →
            1 - 1 / (rho * (n : ℝ) * (Ct : ℝ)) <
              mu.real {omega | ∀ theta, parameter_feasible factors B theta →
                |empirical_local_score_matching_loss factors theta i
                    (fun m => samples m omega) -
                  population_local_score_matching_loss factors theta i p| ≤
                    epsilon / (2 * Aconc)} := by
  classical
  rcases uniform_score_constant_absorption with ⟨A0, hA0, Cconc, hCconc, habsorb⟩
  refine ⟨A0, hA0, Cconc, hCconc, ?_⟩
  intro n d factors thetaStar i B tailRate Ct p instProb hdegree hfamily hB hthetaStar
    hu htail
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hd : 2 ≤ d := htail.2.1
  have hCtReal : (1 : ℝ) ≤ Ct := (le_max_right _ _).trans htail.2.2.1
  have hCt : 1 ≤ Ct := by exact_mod_cast hCtReal
  have hCtUpper : (Ct : ℝ) ≤ Real.exp (n : ℝ) := htail.2.2.2.1
  let J := factors_at factors i
  by_cases hJ : J = ∅
  · rcases uniform_empirical_score_concentration_empty_case factors i B
      ((d : ℝ) * B * (Ct : ℝ) ^ d) A0 p hA0 hCt hJ with
      ⟨Aconc, hAconc, hAconcUpper, hprob⟩
    refine ⟨Aconc, hAconc, hAconcUpper, ?_⟩
    intro M Ω instMeas mu instMu samples rho epsilon hiid hrho hepsilon hepsilonOne hsample
    exact hprob M Ω mu samples rho epsilon hrho hepsilon
  · have hJnonempty : J.Nonempty := Finset.nonempty_iff_ne_empty.mpr hJ
    rcases hJnonempty with ⟨a0, ha0⟩
    have ha0Factor : a0 ∈ factors := (Finset.mem_filter.mp ha0).1
    have hiSupport : i ∈ factor_support a0 := (Finset.mem_filter.mp ha0).2
    have hsupportPos : 0 < (factor_support a0).card := Finset.card_pos.mpr ⟨i, hiSupport⟩
    let w := interaction_order factors
    have hwLower : (factor_support a0).card ≤ w := by
      exact Finset.le_sup (s := factors) (f := fun factor => (factor_support factor).card)
        ha0Factor
    have hw : 0 < w := lt_of_lt_of_le hsupportPos hwLower
    let P : ℕ := (n + d) ^ d
    let q : ℕ := 2 * P ^ 2
    let u : ℝ := (d : ℝ) * B * (Ct : ℝ) ^ d
    let H : ℝ := 8 * (1 + (d : ℝ) * u + u ^ 2)
    have hP : 0 < P := by dsimp [P]; positivity
    have hq : 0 < q := by dsimp [q]; positivity
    have hH : 0 < H := by dsimp [H, u]; positivity
    have hqBound : q ≤ 2 * (n + d) ^ (2 * d) := by
      dsimp [q, P]
      rw [show 2 * d = d * 2 by omega, pow_mul]
    rcases habsorb n d Ct w q u H hn hd hCt hCtUpper hw hq hu hH le_rfl hqBound with
      ⟨Aconc, hAconc, hAconcUpper, hAconcAbsorb⟩
    refine ⟨Aconc, hAconc, ?_, ?_⟩
    · simpa [u, w] using hAconcUpper
    · intro M Ω instMeas mu instMu samples rho epsilon hiid hrho hepsilon hepsilonOne hsample
      let r : ℕ := max 2 ⌈Real.log
        (8 * (q : ℝ) * rho * (n : ℝ) * (Ct : ℝ))⌉₊
      have hr : 2 ≤ r := by dsimp [r]; exact le_max_left _ _
      have hMReal : (0 : ℝ) < M := by
        have hleft : 0 < rho * (n : ℝ) ^ (d + 1) * Aconc ^ 4 / epsilon ^ 2 := by
          positivity
        exact lt_of_lt_of_le hleft hsample
      have hM : 0 < M := by exact_mod_cast hMReal
      let R : ℝ := 4096 * H *
        (Real.sqrt ((r : ℝ) / (M : ℝ)) +
          (r : ℝ) ^ 3 * Real.rpow (M : ℝ) (-1 + 1 / (r : ℝ)))
      let delta : ℝ := epsilon / (4 * Aconc)
      have hR : 0 < R := by
        dsimp [R]
        have hratio : 0 < (r : ℝ) / (M : ℝ) := by positivity
        have hsqrt : 0 < Real.sqrt ((r : ℝ) / (M : ℝ)) := Real.sqrt_pos.2 hratio
        positivity
      have hdelta : 0 < delta := by dsimp [delta]; positivity
      have hthreshold : Real.exp 1 * R ≤ delta := by
        have h := hAconcAbsorb M r rho epsilon hrho hepsilon hepsilonOne hsample rfl
        calc
          Real.exp 1 * R = 4096 * Real.exp 1 * H *
              (Real.sqrt ((r : ℝ) / (M : ℝ)) +
                (r : ℝ) ^ 3 * Real.rpow (M : ℝ) (-1 + 1 / (r : ℝ))) := by
            dsimp [R]
            ring
          _ ≤ epsilon / (4 * Aconc) := h
          _ = delta := by rfl
      let linEmb : polynomial_factor n ↪
          Sum (polynomial_factor n) (polynomial_factor n × polynomial_factor n) :=
        ⟨Sum.inl, Sum.inl_injective⟩
      let quadEmb : (polynomial_factor n × polynomial_factor n) ↪
          Sum (polynomial_factor n) (polynomial_factor n × polynomial_factor n) :=
        ⟨Sum.inr, Sum.inr_injective⟩
      let featureSet : Finset
          (Sum (polynomial_factor n) (polynomial_factor n × polynomial_factor n)) :=
        J.map linEmb ∪ (J ×ˢ J).map quadEmb
      let Y : Sum (polynomial_factor n) (polynomial_factor n × polynomial_factor n) →
          (Fin n → ℝ) → ℝ := fun z => Sum.elim
        (fun a x => B * monomial_second_partial a i x)
        (fun ab x => (1 / 2 : ℝ) * B ^ 2 *
          (monomial_first_partial ab.1 i x * monomial_first_partial ab.2 i x)) z
      have hfeatureMem (z) (hz : z ∈ featureSet) :
          (∃ a ∈ J, z = Sum.inl a) ∨
            ∃ ab ∈ J ×ˢ J, z = Sum.inr ab := by
        simpa [featureSet, linEmb, quadEmb, eq_comm] using hz
      have hfeatureCard : featureSet.card ≤ q := by
        have hJcard : J.card ≤ P := by
          simpa [J, P] using incident_factor_card_bound factors i hdegree
        have hJcardPos : 0 < J.card := Finset.card_pos.mpr ⟨a0, ha0⟩
        have hprodCard : (J ×ˢ J).card = J.card ^ 2 := by simp [pow_two]
        calc
          featureSet.card ≤ (J.map linEmb).card + ((J ×ˢ J).map quadEmb).card :=
            Finset.card_union_le _ _
          _ = J.card + J.card ^ 2 := by simp [hprodCard]
          _ ≤ 2 * P ^ 2 := by nlinarith [Nat.mul_le_mul hJcard hJcard]
          _ = q := by rfl
      have hEnv := polynomial_score_scaled_feature_envelope factors i B hdegree hd hB hCt
      have hYMeas (z) (hz : z ∈ featureSet) : Measurable (Y z) := by
        rcases hfeatureMem z hz with ⟨a, ha, rfl⟩ | ⟨ab, hab, rfl⟩
        · dsimp [Y]
          unfold monomial_second_partial
          fun_prop
        · dsimp [Y]
          unfold monomial_first_partial
          fun_prop
      have hYEnvelope (z) (hz : z ∈ featureSet) (x : Fin n → ℝ) :
          |Y z x| ≤ H * (1 + (‖x‖ / (Ct : ℝ)) ^ (2 * (d - 1))) := by
        rcases hfeatureMem z hz with ⟨a, ha, rfl⟩ | ⟨ab, hab, rfl⟩
        · exact hEnv.1 a (by simpa [J] using ha) x
        · rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
          exact hEnv.2 ab.1 (by simpa [J] using ha) ab.2
            (by simpa [J] using hb) x
      let D : Sum (polynomial_factor n) (polynomial_factor n × polynomial_factor n) →
          Ω → ℝ := fun z omega =>
        (M : ℝ)⁻¹ * ∑ m, Y z (samples m omega) - ∫ x, Y z x ∂p
      have hFeatureMoment (z) (hz : z ∈ featureSet) :
          MeasureTheory.Integrable (Y z) p ∧
            MeasureTheory.AEStronglyMeasurable (D z) mu ∧
            MeasureTheory.eLpNorm (D z) (r : ENNReal) mu ≤ ENNReal.ofReal R := by
        have h := polynomial_feature_empirical_moment_bound mu d tailRate Ct p samples
          (Y z) H htail hH (hYMeas z hz) (hYEnvelope z hz) hiid r hr hM
        simpa [D, R] using h
      have hprob := finite_feature_uniform_probability mu featureSet D r R delta hr hR
        hthreshold (fun z hz => (hFeatureMoment z hz).2.1)
        (fun z hz => (hFeatureMoment z hz).2.2)
      have hfailure : (featureSet.card : ℝ) * (Real.exp 1)⁻¹ ^ r <
          1 / (rho * (n : ℝ) * (Ct : ℝ)) :=
        uniform_score_cutoff_failure_bound n Ct q featureSet.card r rho hn
          (lt_of_lt_of_le Nat.zero_lt_one hCt) hq hfeatureCard hrho rfl
      have hfeatureEvent :
          1 - 1 / (rho * (n : ℝ) * (Ct : ℝ)) <
            mu.real {omega | ∀ z ∈ featureSet, |D z omega| ≤ delta} := by
        linarith
      refine lt_of_lt_of_le hfeatureEvent (MeasureTheory.measureReal_mono ?_)
      intro omega homega
      intro theta htheta
      have hdev := feasible_local_score_deviation_of_features factors theta i B
        (fun m => samples m omega) p delta hB htheta hdelta.le
        (by
          intro a ha
          have hz : Sum.inl a ∈ featureSet := by
            simp [featureSet, linEmb, J, ha]
          simpa [Y] using (hFeatureMoment (Sum.inl a) hz).1)
        (by
          intro a ha b hb
          have hz : Sum.inr (a, b) ∈ featureSet := by
            simp [featureSet, quadEmb, J, ha, hb]
          simpa [Y] using (hFeatureMoment (Sum.inr (a, b)) hz).1)
        (by
          intro a ha
          have hz : Sum.inl a ∈ featureSet := by
            simp [featureSet, linEmb, J, ha]
          simpa [D, Y] using homega (Sum.inl a) hz)
        (by
          intro a ha b hb
          have hz : Sum.inr (a, b) ∈ featureSet := by
            simp [featureSet, quadEmb, J, ha, hb]
          simpa [D, Y] using homega (Sum.inr (a, b)) hz)
      convert hdev using 1 <;> dsimp [delta] <;> field_simp <;> ring

@[blueprint "lem:family-structure-recovery"
  (statement := /-- Let $n,M\in\mathbb N$, let $\mathcal K$ be a finite family of polynomial
  factors on $n$ coordinates, let $\theta^*,\widehat\theta$ be parameter vectors, fix
  $i\in\operatorname{Fin}(n)$ and $B\in\mathbb R$, let $p$ be a measure on $\mathbb R^n$, and
  let $(x_m)_{m\in\operatorname{Fin}(M)}$ be observations. Fix $A,\epsilon\in\mathbb R$ with
  $A>0$. Assume that $\theta^*$ is feasible at radius $B$, that $\widehat\theta$ is a feasible
  minimizer of the empirical local loss, and that every feasible parameter $\theta$ satisfies
  \[
    \left|\mathcal L_i^{(M)}(\theta)-\mathcal L_i(\theta)\right|
      \leq \frac{\epsilon}{2A}.
  \]
  Suppose moreover that, for every feasible $\theta$ and every
  $a\in\widehat{\mathcal K}_i$, one has
  \[
    (\theta_a^*-\theta_a)^2
      \leq A\bigl(\mathcal L_i(\theta)-\mathcal L_i(\theta^*)\bigr).
  \]
  Then $(\theta_a^*-\widehat\theta_a)^2\leq\epsilon$ for every
  $a\in\widehat{\mathcal K}_i$. -/)
  (proof := /-- By
  \cref{def:constrained-empirical-minimizer}, empirical minimality and feasibility of
  $\theta^*$ give
  $\mathcal L_i^{(M)}(\widehat\theta)\leq
  \mathcal L_i^{(M)}(\theta^*)$. Apply the assumed uniform deviation once to
  $\widehat\theta$ and once to $\theta^*$. Using
  \cref{def:empirical-local-score-matching-loss,def:population-local-score-matching-loss} yields
  \[
    \mathcal L_i(\widehat\theta)-\mathcal L_i(\theta^*)
      \leq \frac{\epsilon}{2A}+\frac{\epsilon}{2A}
      =\frac{\epsilon}{A}.
  \]
  For an arbitrary maximal factor $a$ incident to $i$, the curvature hypothesis now gives
  \[
    (\theta_a^*-\widehat\theta_a)^2
      \leq A\bigl(\mathcal L_i(\widehat\theta)-\mathcal L_i(\theta^*)\bigr)
      \leq\epsilon.
  \]
  Since $a$ was arbitrary, the inequalities hold simultaneously for every such factor. -/)
  (title := /-- Recovery from curvature and uniform score deviation -/)
  (latexEnv := "lemma")]
lemma family_structure_recovery {n M : ℕ}
    (factors : Finset (polynomial_factor n)) (thetaStar thetaHat : polynomial_factor n → ℝ)
    (i : Fin n) (B : ℝ) (p : MeasureTheory.Measure (Fin n → ℝ))
    (observations : Fin M → (Fin n → ℝ)) (A epsilon : ℝ) :
    0 < A →
    parameter_feasible factors B thetaStar →
    constrained_empirical_minimizer factors B i observations thetaHat →
    (∀ theta, parameter_feasible factors B theta →
      |empirical_local_score_matching_loss factors theta i observations -
        population_local_score_matching_loss factors theta i p| ≤ epsilon / (2 * A)) →
    (∀ theta, parameter_feasible factors B theta →
      ∀ factor ∈ incident_maximal_factors factors i,
        (thetaStar factor - theta factor) ^ 2 ≤
          A * (population_local_score_matching_loss factors theta i p -
            population_local_score_matching_loss factors thetaStar i p)) →
    ∀ factor ∈ incident_maximal_factors factors i,
      (thetaStar factor - thetaHat factor) ^ 2 ≤ epsilon := by
  rintro hA hStar hMin hDev hCurv factor hFactor
  have hHatFeasible := hMin.1
  have hEmpiricalOrder := hMin.2 thetaStar hStar
  have hHatDeviation := hDev thetaHat hHatFeasible
  have hStarDeviation := hDev thetaStar hStar
  have hHatLower := (abs_le.mp hHatDeviation).1
  have hStarUpper := (abs_le.mp hStarDeviation).2
  have hPopulationOrder :
      population_local_score_matching_loss factors thetaHat i p -
          population_local_score_matching_loss factors thetaStar i p ≤
        epsilon / (2 * A) + epsilon / (2 * A) := by
    linarith
  calc
    (thetaStar factor - thetaHat factor) ^ 2 ≤
        A * (population_local_score_matching_loss factors thetaHat i p -
          population_local_score_matching_loss factors thetaStar i p) :=
      hCurv thetaHat hHatFeasible factor hFactor
    _ ≤ A * (epsilon / (2 * A) + epsilon / (2 * A)) :=
      mul_le_mul_of_nonneg_left hPopulationOrder hA.le
    _ = epsilon := by
      field_simp [ne_of_gt hA]
      ring

@[blueprint "lem:family-structure-statistical-estimate"
  (statement := /-- There exist an absolute real constant $A_0>1$ and an absolute positive
  integer $C$ with the following property. For every dimension $n$, degree bound $d$, finite
  factor family $\mathcal K$ of interaction order $w$, parameter vector $\theta^*$, coordinate
  $i\in[n]$, real numbers $B>0$ and $k$, integer $C_t$, and probability measure $p$, assume that
  $\mathcal K$ has degree at most $d$, that $p$ is the unit-base polynomial exponential family
  determined by $(\mathcal K,\theta^*)$, that $\theta^*$ is feasible at coordinatewise radius
  $B$, and that $p$ satisfies the tail-decay condition with parameters $(d,k,C_t)$. Put
  $\overline u=\max\{1+2^{-10},dBC_t^d\}$. Then there exists a real number $M^*$ such that
  \[
    1\leq M^*\leq\max\{A_0,\overline u^{C d^2w}\}.
  \]
  For every natural number $M$, every probability space $(\Omega,\mathcal F,\mu)$, every
  $M$-tuple of independent samples with common distribution $p$, every selection
  $\widehat\theta:\Omega\to(\mathbb N^n\to\mathbb R)$ that is a constrained empirical local
  score-matching minimizer at radius $B$ for each outcome, and every $\rho,\epsilon\in\mathbb R$,
  assume that each coordinate map $\omega\mapsto\widehat\theta_a(\omega)$ is measurable for
  every maximal factor $a$ incident to $i$, that $\rho\geq1$, that $0<\epsilon\leq1$, and that
  \[
    M\geq\frac{\rho n^{d+1}M^*}{\epsilon^2}.
  \]
  Then, with probability strictly greater than $1-(\rho nC_t)^{-1}$, the inequalities
  $(\theta_a^*-\widehat\theta_a)^2\leq\epsilon$ hold simultaneously for every maximal factor
  $a$ incident to $i$. -/)
  (proof := /-- Let $\tau=1+2^{-10}$ and $u=dBC_t^d$. The tail-decay hypothesis includes
  $d\geq2$ and $C_t\geq1$, so $dC_t^d>0$. Define
  \[
    B^\dagger=\max\left\{B,\frac{\tau}{dC_t^d}\right\},
    \qquad \overline u=dB^\dagger C_t^d=\max\{u,\tau\}.
  \]
  Then $B^\dagger\geq B>0$, and feasibility at radius $B$ implies feasibility at radius
  $B^\dagger$ directly from \cref{def:parameter-feasible}. Moreover,
  $dB^\dagger C_t^d=\overline u\geq\tau$, so the auxiliary radius satisfies the quantitative
  base hypotheses of
  \cref{lem:maximal-factor-curvature,lem:uniform-empirical-score-concentration}.

  Let $A_{0,\mathrm{curv}}>1$, $C_{\rm curv}>0$,
  $A_{0,\mathrm{conc}}>1$, and $C_{\rm conc}>0$ be the absolute constants supplied by those two
  lemmas, applied at radius $B^\dagger$. Write $A_{\rm curv}$ and $A_{\rm conc}$ for the
  corresponding model-dependent constants and put
  $A=\max\{A_{\rm curv},A_{\rm conc}\}$. The two cited estimates hold uniformly on the larger
  feasible set of radius $B^\dagger$ and therefore, in particular, on the original feasible set
  of radius $B$. Their quantitative bounds are powers of $\overline u$.

  Set $A_0=\max\{A_{0,\mathrm{curv}},A_{0,\mathrm{conc}}\}^4$ and
  $C=4(C_{\rm curv}+C_{\rm conc}+1)$. Since $\overline u\geq\tau>1$, the two bounds imply
  \[
    1\leq M^*:=A^4\leq
    \max\{A_0,\overline u^{Cd^2w}\}.
  \]
  Indeed,
  \[
    A\leq
    \max\!\left\{
      \max\{A_{0,\mathrm{curv}},A_{0,\mathrm{conc}}\},
      \overline u^{(C_{\rm curv}+C_{\rm conc}+1)d^2w}
    \right\},
  \]
  and taking fourth powers and enlarging the exponent gives the asserted inequality. This is
  precisely the bound in \cref{def:family-structure-sample-scale}.

  Fix now $\rho\geq1$, $0<\epsilon\leq1$, and an admissible independent sample of size
  $M\geq\rho n^{d+1}M^*/\epsilon^2$. Apply the concentration lemma with accuracy
  $\epsilon A_{\rm conc}/A$, which lies in $(0,1]$. The required sample threshold is
  \[
    \rho n^{d+1}\frac{A_{\rm conc}^4}
      {(\epsilon A_{\rm conc}/A)^2}
    =\rho n^{d+1}\frac{A_{\rm conc}^2A^2}{\epsilon^2}
    \leq\rho n^{d+1}\frac{A^4}{\epsilon^2},
  \]
  so it is implied by the displayed bound. The concentration lemma therefore yields, outside a
  set of probability less than
  $(\rho nC_t)^{-1}$, the uniform deviation estimate
  \[
    |\mathcal L_i^{(M)}(\theta)-\mathcal L_i(\theta)|
      \leq\frac{\epsilon}{2A}
  \]
  for every parameter feasible at radius $B^\dagger$, hence for every parameter feasible at
  radius $B$. For each incident maximal factor, the original curvature bound and the
  nonnegativity of its squared left-hand side imply that the corresponding score excess is
  nonnegative, since $A_{\rm curv}\geq1$. Hence the curvature inequality remains valid on the
  original feasible set with $A$ in place of $A_{\rm curv}$.

  On this uniform event, apply \cref{lem:family-structure-recovery} pointwise to the constrained
  empirical minimizer. It gives
  $(\theta_a^*-\widehat\theta_a)^2\leq\epsilon$ simultaneously for every incident maximal factor
  $a$. Thus the uniform deviation event is contained in the simultaneous recovery event, and
  monotonicity of the measure shows that the latter has probability strictly greater than
  $1-(\rho nC_t)^{-1}$. This proves
  \cref{def:family-structure-recovery-at-scale}, while the preceding bound on $M^*$ proves
  \cref{def:family-structure-sample-scale}, and together they establish
  \cref{def:family-structure-conclusion}. -/)
  (title := /-- The isolated finite-sample statistical estimate -/)
  (latexEnv := "lemma")]
lemma family_structure_statistical_estimate :
    ∃ A0 : ℝ, 1 < A0 ∧
      ∃ C : ℕ, 0 < C ∧
        ∀ {n : ℕ} (d : ℕ)
        (factors : Finset (polynomial_factor n)) (thetaStar : polynomial_factor n → ℝ)
        (i : Fin n) (B tailRate : ℝ) (Ct : ℕ) (p : MeasureTheory.Measure (Fin n → ℝ))
        [MeasureTheory.IsProbabilityMeasure p],
        family_degree_at_most factors d →
        unit_base_polynomial_exponential_family factors thetaStar p →
        0 < B → parameter_feasible factors B thetaStar →
        tail_decay_condition d tailRate Ct p →
        family_structure_conclusion A0 C d factors thetaStar i B Ct p := by
  classical
  rcases maximal_factor_curvature with
    ⟨A0curv, hA0curv, Ccurv, hCcurv, hcurvature⟩
  rcases uniform_empirical_score_concentration with
    ⟨A0conc, hA0conc, Cconc, hCconc, hconcentration⟩
  let A0 : ℝ := (max A0curv A0conc) ^ 4
  let C : ℕ := 4 * (Ccurv + Cconc + 1)
  have hbaseAbsolute : 1 < max A0curv A0conc :=
    hA0curv.trans_le (le_max_left _ _)
  have hA0 : 1 < A0 := by
    dsimp [A0]
    nlinarith [sq_nonneg ((max A0curv A0conc) ^ 2 - 1)]
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨A0, hA0, C, hC, ?_⟩
  intro n d factors thetaStar i B tailRate Ct p instProb hdegree hfamily hB
    hthetaStar htail
  let tau : ℝ := 1 + 1 / 1024
  let denominator : ℝ := (d : ℝ) * (Ct : ℝ) ^ d
  let Bdagger : ℝ := max B (tau / denominator)
  have hdNat : 0 < d := lt_of_lt_of_le (by norm_num) htail.2.1
  have hdReal : 0 < (d : ℝ) := by exact_mod_cast hdNat
  have hCtOne : (1 : ℝ) ≤ (Ct : ℝ) :=
    (le_max_right _ _).trans htail.2.2.1
  have hCtReal : 0 < (Ct : ℝ) := zero_lt_one.trans_le hCtOne
  have hdenominator : 0 < denominator := by
    exact mul_pos hdReal (pow_pos hCtReal d)
  have htau : 1 < tau := by norm_num [tau]
  have hBdagger : 0 < Bdagger :=
    hB.trans_le (le_max_left _ _)
  have hthetaStarDagger : parameter_feasible factors Bdagger thetaStar := by
    intro j
    exact (hthetaStar j).trans (le_max_left _ _)
  have hlargeBase :
      tau ≤ (d : ℝ) * Bdagger * (Ct : ℝ) ^ d := by
    calc
      tau = denominator * (tau / denominator) := by
        field_simp [ne_of_gt hdenominator]
      _ ≤ denominator * Bdagger :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) hdenominator.le
      _ = (d : ℝ) * Bdagger * (Ct : ℝ) ^ d := by
        dsimp [denominator]
        ring
  rcases hcurvature d factors thetaStar i Bdagger tailRate Ct p hdegree hfamily
      hBdagger hthetaStarDagger hlargeBase htail with
    ⟨Acurv, hAcurv, hAcurvBound, hcurv⟩
  rcases hconcentration d factors thetaStar i Bdagger tailRate Ct p hdegree hfamily
      hBdagger hthetaStarDagger hlargeBase htail with
    ⟨Aconc, hAconc, hAconcBound, hconc⟩
  let u : ℝ := max tau ((d : ℝ) * B * (Ct : ℝ) ^ d)
  have hscale : (d : ℝ) * Bdagger * (Ct : ℝ) ^ d = u := by
    calc
      (d : ℝ) * Bdagger * (Ct : ℝ) ^ d = denominator * Bdagger := by
        dsimp [denominator]
        ring
      _ = max (denominator * B) (denominator * (tau / denominator)) := by
        exact mul_max_of_nonneg B (tau / denominator) hdenominator.le
      _ = max ((d : ℝ) * B * (Ct : ℝ) ^ d) tau := by
        congr 1
        · dsimp [denominator]
          ring
        · field_simp [ne_of_gt hdenominator]
      _ = u := by simp [u, max_comm]
  rw [hscale] at hAcurvBound hAconcBound
  let exponent : ℕ := (Ccurv + Cconc + 1) * d ^ 2 * interaction_order factors
  let absoluteBase : ℝ := max A0curv A0conc
  let commonBound : ℝ := max absoluteBase (u ^ exponent)
  have hu : 1 ≤ u := by
    exact htau.le.trans (le_max_left _ _)
  have hcurvPower :
      u ^ (Ccurv * d ^ 2 * interaction_order factors) ≤ u ^ exponent := by
    apply pow_le_pow_right₀ hu
    dsimp [exponent]
    exact Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ (by omega : Ccurv ≤ Ccurv + Cconc + 1))
  have hconcPower :
      u ^ (Cconc * d ^ 2 * interaction_order factors) ≤ u ^ exponent := by
    apply pow_le_pow_right₀ hu
    dsimp [exponent]
    exact Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ (by omega : Cconc ≤ Ccurv + Cconc + 1))
  have hAcurvCommon : Acurv ≤ commonBound := by
    exact hAcurvBound.trans (max_le_max (le_max_left _ _) hcurvPower)
  have hAconcCommon : Aconc ≤ commonBound := by
    exact hAconcBound.trans (max_le_max (le_max_right _ _) hconcPower)
  let A : ℝ := max Acurv Aconc
  have hAcurvA : Acurv ≤ A := le_max_left _ _
  have hAconcA : Aconc ≤ A := le_max_right _ _
  have hA : 0 < A := zero_lt_one.trans_le (hAcurv.trans hAcurvA)
  have hACommon : A ≤ commonBound := max_le hAcurvCommon hAconcCommon
  have hACommonFourth : A ^ 4 ≤ commonBound ^ 4 := by
    gcongr
  have hFourthBound :
      commonBound ^ 4 ≤
        max A0 (u ^ (C * d ^ 2 * interaction_order factors)) := by
    rcases le_total absoluteBase (u ^ exponent) with hleft | hright
    · rw [show commonBound = u ^ exponent by
        exact max_eq_right hleft]
      apply le_max_of_le_right
      rw [← pow_mul]
      congr 1
      dsimp [C, exponent]
      ring_nf
      exact le_rfl
    · rw [show commonBound = absoluteBase by
        exact max_eq_left hright]
      exact le_max_of_le_left (by rfl)
  refine ⟨A ^ 4, ?_, ?_⟩
  · refine ⟨hA0, hC, ?_, ?_⟩
    · nlinarith [sq_nonneg (A ^ 2 - 1)]
    · change A ^ 4 ≤ max A0 (u ^ (C * d ^ 2 * interaction_order factors))
      exact hACommonFourth.trans hFourthBound
  · intro M Ω instMeas mu instMuProb samples thetaHat rho epsilon hiid hminimizer
      hmeasurable hrho hepsilon hepsilonOne hsample
    let epsilonConc : ℝ := epsilon * Aconc / A
    have hAconcPos : 0 < Aconc := zero_lt_one.trans_le hAconc
    have hepsilonConc : 0 < epsilonConc := by
      exact div_pos (mul_pos hepsilon hAconcPos) hA
    have hratioNonneg : 0 ≤ Aconc / A := (div_pos hAconcPos hA).le
    have hratioOne : Aconc / A ≤ 1 := (div_le_one hA).2 hAconcA
    have hepsilonConcOne : epsilonConc ≤ 1 := by
      calc
        epsilonConc = epsilon * (Aconc / A) := by ring
        _ ≤ 1 * 1 := mul_le_mul hepsilonOne hratioOne hratioNonneg (by norm_num)
        _ = 1 := by ring
    have hAconcSquare : Aconc ^ 2 ≤ A ^ 2 := by
      nlinarith [mul_self_le_mul_self hAconcPos.le hAconcA]
    have hmixedFourth : Aconc ^ 2 * A ^ 2 ≤ A ^ 4 := by
      nlinarith [mul_le_mul_of_nonneg_right hAconcSquare (sq_nonneg A)]
    have hsampleConc :
        rho * (n : ℝ) ^ (d + 1) * Aconc ^ 4 / epsilonConc ^ 2 ≤ (M : ℝ) := by
      calc
        rho * (n : ℝ) ^ (d + 1) * Aconc ^ 4 / epsilonConc ^ 2 =
            rho * (n : ℝ) ^ (d + 1) * (Aconc ^ 2 * A ^ 2) / epsilon ^ 2 := by
              dsimp [epsilonConc]
              field_simp [ne_of_gt hepsilon, ne_of_gt hAconcPos, ne_of_gt hA]
        _ ≤ rho * (n : ℝ) ^ (d + 1) * A ^ 4 / epsilon ^ 2 := by
              gcongr
        _ ≤ (M : ℝ) := hsample
    have hprobability := hconc M Ω mu samples rho epsilonConc hiid hrho
      hepsilonConc hepsilonConcOne hsampleConc
    have hdeviationScale : epsilonConc / (2 * Aconc) = epsilon / (2 * A) := by
      dsimp [epsilonConc]
      field_simp [ne_of_gt hAconcPos, ne_of_gt hA]
    have hsubset :
        {omega | ∀ theta, parameter_feasible factors Bdagger theta →
          |empirical_local_score_matching_loss factors theta i
                (fun m => samples m omega) -
            population_local_score_matching_loss factors theta i p| ≤
              epsilonConc / (2 * Aconc)} ⊆
        {omega | ∀ factor ∈ incident_maximal_factors factors i,
          (thetaStar factor - thetaHat omega factor) ^ 2 ≤ epsilon} := by
      intro omega homega
      apply family_structure_recovery factors thetaStar (thetaHat omega) i B p
        (fun m => samples m omega) A epsilon hA hthetaStar (hminimizer omega)
      · intro theta htheta
        rw [← hdeviationScale]
        exact homega theta fun j => (htheta j).trans (le_max_left _ _)
      · intro theta htheta factor hfactor
        have hthetaDagger : parameter_feasible factors Bdagger theta := fun j =>
          (htheta j).trans (le_max_left _ _)
        have hcurvAtFactor := hcurv theta hthetaDagger factor hfactor
        have hexcess : 0 ≤
            population_local_score_matching_loss factors theta i p -
              population_local_score_matching_loss factors thetaStar i p := by
          nlinarith [sq_nonneg (thetaStar factor - theta factor)]
        exact hcurvAtFactor.trans
          (mul_le_mul_of_nonneg_right hAcurvA hexcess)
    calc
      1 - 1 / (rho * (n : ℝ) * (Ct : ℝ)) <
          mu.real {omega | ∀ theta, parameter_feasible factors Bdagger theta →
            |empirical_local_score_matching_loss factors theta i
                  (fun m => samples m omega) -
              population_local_score_matching_loss factors theta i p| ≤
                epsilonConc / (2 * Aconc)} := hprobability
      _ ≤ mu.real {omega | ∀ factor ∈ incident_maximal_factors factors i,
          (thetaStar factor - thetaHat omega factor) ^ 2 ≤ epsilon} := by
        exact ENNReal.toReal_mono (MeasureTheory.measure_ne_top mu _)
          (MeasureTheory.measure_mono hsubset)

@[blueprint "thm:family-structure-learning"
  (statement := /-- There exist an absolute real constant $A_0>1$ and an absolute positive
  integer $C$ with the following property. Let $n,d\in\mathbb N$, let $\mathcal K$ be a finite
  family of polynomial factors on $n$ coordinates, let
  $\theta^*:\mathbb N^n\to\mathbb R$, let $i\in[n]$, let $B,k\in\mathbb R$, let
  $C_t\in\mathbb N$, and let $p$ be a probability measure on $\mathbb R^n$. Assume that every
  factor in $\mathcal K$ has total degree at most $d$, that $p$ is the unit-base polynomial
  exponential family determined by $(\mathcal K,\theta^*)$, that $B>0$, and that
  $\sum_{a\in\mathcal K_j}|\theta_a^*|\leq B$ for every coordinate $j$. Assume also that
  $k>0$, $d\geq2$,
  \[
    \max\!\left\{\left(\frac{\log 2}{k}\right)^{1/(d-1)},1\right\}
      \leq C_t\leq e^n,
  \]
  and
  \[
    p\{x:\lVert x\rVert_\infty>s\}\leq e^{-ks^{d-1}}
    \qquad\text{for every }s\geq C_t.
  \]
  Write $w=\max_{a\in\mathcal K}|\partial a|$ and
  $\overline u=\max\{1+2^{-10},dBC_t^d\}$. Then there exists $M^*\in\mathbb R$ such that
  \[
    1\leq M^*\leq\max\{A_0,\overline u^{C d^2w}\}.
  \]
  For every natural number $M$, every probability space $(\Omega,\mathcal F,\mu)$, every
  $M$-tuple of independent samples with common distribution $p$, every selection
  $\widehat\theta:\Omega\to(\mathbb N^n\to\mathbb R)$ that is, for each outcome, a
  constrained empirical local score-matching minimizer at radius $B$, and every
  $\rho,\epsilon\in\mathbb R$, assume that
  $\omega\mapsto\widehat\theta_a(\omega)$ is measurable for every maximal factor $a$ incident
  to $i$, that $\rho\geq1$, that $0<\epsilon\leq1$, and that
  \[
    M\geq\frac{\rho n^{d+1}M^*}{\epsilon^2}.
  \]
  Then, with probability strictly greater than $1-(\rho nC_t)^{-1}$, one has
  $(\theta_a^*-\widehat\theta_a)^2\leq\epsilon$ simultaneously for every maximal factor $a$
  incident to $i$. -/)
  (proof := /-- Apply the isolated statistical estimate
  \cref{lem:family-structure-statistical-estimate}. It supplies an absolute prefactor $A_0>1$ and
  a positive exponent constant $C$ before any model parameter is quantified. For an arbitrary
  model satisfying the stated hypotheses, the estimate applies without a quantitative lower
  bound on $dBC_t^d$. Unfolding its packaged conclusion in
  \cref{def:family-structure-conclusion} gives a scale $M^*$ with the bound determined by these
  same constants, together with the uniform recovery statement over the sample size, probability
  space, independent sample family, measurable empirical-minimizer selection, confidence
  parameter, and accuracy parameter. -/)
  (title := /-- Family Structure Learning -/)
  (latexEnv := "theorem")]
theorem family_structure_learning :
    ∃ A0 : ℝ, 1 < A0 ∧
      ∃ C : ℕ, 0 < C ∧
        ∀ {n : ℕ} (d : ℕ)
        (factors : Finset (polynomial_factor n)) (thetaStar : polynomial_factor n → ℝ)
        (i : Fin n) (B tailRate : ℝ) (Ct : ℕ) (p : MeasureTheory.Measure (Fin n → ℝ))
        [MeasureTheory.IsProbabilityMeasure p],
        family_degree_at_most factors d →
        unit_base_polynomial_exponential_family factors thetaStar p →
        0 < B → parameter_feasible factors B thetaStar →
        tail_decay_condition d tailRate Ct p →
        ∃ Mstar : ℝ,
          family_structure_sample_scale A0 C d B Ct (interaction_order factors) Mstar ∧
            family_structure_recovery_at_scale d factors thetaStar i B Ct p Mstar := by
  exact family_structure_statistical_estimate

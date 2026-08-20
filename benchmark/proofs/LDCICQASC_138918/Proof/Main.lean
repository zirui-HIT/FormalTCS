import Architect
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.InformationTheory.Hamming
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:qary-linear-code"
  (statement := /-- Let $\mathbb F$ be a finite field and let $n\in\mathbb N$.  A $q$-ary linear code of block length $n$ is an $\mathbb F$-linear subspace of $\mathbb F^{\{0,\ldots,n-1\}}$. -/)
  (title := /-- Linear codes -/)
  (latexEnv := "definition")]
abbrev qary_linear_code (𝔽 : Type*) [Field 𝔽] (n : ℕ) :=
  Submodule 𝔽 (Fin n → 𝔽)

@[blueprint "def:qary-code-family"
  (statement := /-- Let $\mathbb F$ be a finite field.  A family of $q$-ary linear codes is a sequence $(C_n)_{n\geq 0}$ in which $C_n$ is a linear code of block length $n$. -/)
  (title := /-- Families of linear codes -/)
  (latexEnv := "definition")]
abbrev qary_code_family (𝔽 : Type*) [Field 𝔽] :=
  (n : ℕ) → qary_linear_code 𝔽 n

@[blueprint "def:qary-entropy"
  (statement := /-- For an integer $q\geq 2$ and $p\in\mathbb R$, define the $q$-ary entropy by
  \[
    h_q(p)=(1-p)\log_q\!\left(\frac1{1-p}\right)
      +p\log_q\!\left(\frac{q-1}{p}\right).
  \] -/)
  (title := /-- The $q$-ary entropy function -/)
  (latexEnv := "definition")]
noncomputable def qary_entropy (q : ℕ) (p : ℝ) : ℝ :=
  (1 - p) * Real.logb (q : ℝ) (1 / (1 - p)) +
    p * Real.logb (q : ℝ) (((q - 1 : ℕ) : ℝ) / p)

@[blueprint "def:linear-code-rate"
  (statement := /-- Let $\mathbb F$ be a finite field of cardinality $q$, let $n\in\mathbb N$, and let $C\leq \mathbb F^n$ be a linear code.  Its rate is
  \[
    R(C)=\frac{\log_q |C|}{n}.
  \] -/)
  (title := /-- Rate of a finite-field code -/)
  (latexEnv := "definition")]
noncomputable def linear_code_rate {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    {n : ℕ} (C : qary_linear_code 𝔽 n) : ℝ :=
  letI : Fintype C := Fintype.ofFinite C
  Real.logb (Fintype.card 𝔽 : ℝ) (Fintype.card C : ℝ) / (n : ℝ)

@[blueprint "def:linear-code-minimum-distance"
  (statement := /-- Let $C\leq\mathbb F^n$ be a linear code.  Its minimum distance is the infimum of the Hamming weights of its nonzero codewords; for the zero code this convention gives $0$. -/)
  (title := /-- Minimum distance -/)
  (latexEnv := "definition")]
noncomputable def linear_code_minimum_distance {𝔽 : Type*} [Field 𝔽]
    [DecidableEq 𝔽] {n : ℕ} (C : qary_linear_code 𝔽 n) : ℕ :=
  sInf {d : ℕ | ∃ c : C, c ≠ 0 ∧ d = hammingDist (c : Fin n → 𝔽) 0}

@[blueprint "def:list-decodable"
  (statement := /-- Let $C\leq\mathbb F^n$, let $p\in\mathbb R$, and let $L\in\mathbb N$.  The code $C$ is $(p,L)$-list-decodable if every word $y\in\mathbb F^n$ has at most $L$ codewords at Hamming distance at most $pn$ from $y$. -/)
  (title := /-- List decodability -/)
  (latexEnv := "definition")]
noncomputable def list_decodable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    [DecidableEq 𝔽] {n : ℕ} (C : qary_linear_code 𝔽 n) (p : ℝ) (L : ℕ) : Prop :=
  letI : Fintype C := Fintype.ofFinite C
  ∀ y : Fin n → 𝔽,
    (Finset.univ.filter
      (fun c : C => (hammingDist y (c : Fin n → 𝔽) : ℝ) ≤ p * (n : ℝ))).card ≤ L

@[blueprint "def:qary-decoder"
  (statement := /-- Let $C\leq\mathbb F^n$.  A randomized decoder for $C$ assigns to every received word $y\in\mathbb F^n$ a probability mass function on the codewords of $C$. -/)
  (title := /-- Randomized decoders -/)
  (latexEnv := "definition")]
abbrev qary_decoder {𝔽 : Type*} [Field 𝔽] {n : ℕ}
    (C : qary_linear_code 𝔽 n) :=
  (Fin n → 𝔽) → PMF C

@[blueprint "def:qsc-error-mass"
  (statement := /-- Let $\mathbb F$ have cardinality $q$, let $n\in\mathbb N$, and let $p\in\mathbb R$.  The mass assigned by the $q$-ary symmetric channel to an error vector $z\in\mathbb F^n$ is
  \[
    \prod_{i=1}^n\left(\mathbf 1_{z_i=0}(1-p)
      +\mathbf 1_{z_i\neq0}\frac{p}{q-1}\right).
  \]
  For $0\leq p\leq1$, this is the law in which coordinates are independently unchanged with probability $1-p$ and otherwise replaced by a uniformly chosen nonzero field element. -/)
  (title := /-- Error law of the $q$-ary symmetric channel -/)
  (latexEnv := "definition")]
noncomputable def qsc_error_mass {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    [DecidableEq 𝔽] {n : ℕ} (p : ℝ) (z : Fin n → 𝔽) : ENNReal :=
  ∏ i : Fin n,
    if z i = 0 then ENNReal.ofReal (1 - p)
    else ENNReal.ofReal (p / ((Fintype.card 𝔽 : ℝ) - 1))

@[blueprint "def:qsc-success-probability"
  (statement := /-- Let $C\leq\mathbb F^n$, let $D$ be a randomized decoder, let $p\in\mathbb R$, and let $c\in C$.  The success probability of $D$ on the $q$-ary symmetric channel with noise parameter $p$ is
  \[
    \sum_{z\in\mathbb F^n}\Pr_p[z]D(c+z)(c).
  \] -/)
  (title := /-- Decoding success on the $q$-ary symmetric channel -/)
  (latexEnv := "definition")]
noncomputable def qsc_success_probability {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    [DecidableEq 𝔽] {n : ℕ} (C : qary_linear_code 𝔽 n)
    (D : qary_decoder C) (p : ℝ) (c : C) : ENNReal :=
  ∑ z : Fin n → 𝔽,
    qsc_error_mass p z * D ((c : Fin n → 𝔽) + z) c

@[blueprint "def:has-asymptotic-rate"
  (statement := /-- A family $(C_n)_{n\geq0}$ of $q$-ary linear codes has asymptotic rate $R$ if $R(C_n)$ tends to $R$ as $n\to\infty$. -/)
  (title := /-- Asymptotic rate -/)
  (latexEnv := "definition")]
noncomputable def has_asymptotic_rate {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    (C : qary_code_family 𝔽) (R : ℝ) : Prop :=
  Filter.Tendsto (fun n => linear_code_rate (C n)) Filter.atTop (nhds R)

@[blueprint "def:achieves-list-decoding-capacity"
  (statement := /-- Let $p\in(0,1)$ and let $(C_n)_{n\geq0}$ be a family of linear codes over a field of cardinality $q$.  The family achieves list-decoding capacity at corruption fraction $p$ if its rate tends to $1-h_q(p)$ and, for every integer-valued function $L(n)\to\infty$, there is a real function $\varepsilon(n)\to0$ such that $C_n$ is $(p-\varepsilon(n),L(n))$-list-decodable for all sufficiently large $n$. -/)
  (title := /-- Capacity for adversarial list decoding -/)
  (latexEnv := "definition")]
noncomputable def achieves_list_decoding_capacity {𝔽 : Type*} [Field 𝔽]
    [Fintype 𝔽] [DecidableEq 𝔽] (C : qary_code_family 𝔽) (p : ℝ) : Prop :=
  has_asymptotic_rate C (1 - qary_entropy (Fintype.card 𝔽) p) ∧
    ∀ L : ℕ → ℕ, Filter.Tendsto L Filter.atTop Filter.atTop →
      ∃ ε : ℕ → ℝ,
        Filter.Tendsto ε Filter.atTop (nhds 0) ∧
          ∀ᶠ n in Filter.atTop, list_decodable (C n) (p - ε n) (L n)

@[blueprint "def:achieves-qsc-capacity"
  (statement := /-- Let $p\in(0,1)$ and let $(C_n)_{n\geq0}$ be a family of linear codes over a field of cardinality $q$.  The family achieves capacity on the $q$-ary symmetric channel at parameter $p$ if its rate tends to $1-h_q(p)$ and there exist nonnegative slacks $\varepsilon(n)\to0$ and randomized decoders $D_n$ such that, for all sufficiently large $n$, the channel parameter $p-\varepsilon(n)$ is nonnegative and
  \[
    \Pr_{z\sim\mathrm{qSC}_{p-\varepsilon(n)}}
      [D_n(c+z)=c]\geq1-\varepsilon(n)
  \]
  for every $c\in C_n$. -/)
  (title := /-- Capacity on the $q$-ary symmetric channel -/)
  (latexEnv := "definition")]
noncomputable def achieves_qsc_capacity {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    [DecidableEq 𝔽] (C : qary_code_family 𝔽) (p : ℝ) : Prop :=
  has_asymptotic_rate C (1 - qary_entropy (Fintype.card 𝔽) p) ∧
    ∃ ε : ℕ → ℝ, ∃ D : (n : ℕ) → qary_decoder (C n),
      Filter.Tendsto ε Filter.atTop (nhds 0) ∧
        ∀ᶠ n in Filter.atTop,
          0 ≤ ε n ∧ ε n ≤ p ∧
            ∀ c : C n,
              ENNReal.ofReal (1 - ε n) ≤
                qsc_success_probability (C n) (D n) (p - ε n) c

@[blueprint "def:minimum-distance-growth"
  (statement := /-- Let $p\in(0,1)$ and let $(C_n)_{n\geq0}$ be a family of linear codes over a field of cardinality $q$.  The assertion
  \[
    d_{\min}(C_n)=\omega\!\left(\frac{q^3}{(1-p)^2}\right)
  \]
  means that the constant function $q^3/(1-p)^2$ is little-$o$ of the real-valued sequence $d_{\min}(C_n)$ along $n\to\infty$. -/)
  (title := /-- The minimum-distance growth hypothesis -/)
  (latexEnv := "definition")]
noncomputable def minimum_distance_growth {𝔽 : Type*} [Field 𝔽]
    [Fintype 𝔽] [DecidableEq 𝔽] (C : qary_code_family 𝔽) (p : ℝ) : Prop :=
  (fun _ : ℕ => (Fintype.card 𝔽 : ℝ) ^ 3 / (1 - p) ^ 2) =o[Filter.atTop]
    (fun n => (linear_code_minimum_distance (C n) : ℝ))

@[blueprint "def:sampling-slack"
  (statement := /-- For $n\in\mathbb N$, define the preliminary channel slack by $s_n=n^{-1/4}$. -/)
  (title := /-- Preliminary channel slack -/)
  (latexEnv := "definition")]
noncomputable def sampling_slack (n : ℕ) : ℝ :=
  Real.rpow (n : ℝ) (-(1 / 4 : ℝ))

@[blueprint "def:sharp-threshold-lower-bound"
  (statement := /-- For integers $q,d,L\geq0$ and real parameters $p,\delta$, define
  \[
    B(q,d,L,p,\delta)
      =1-2L\exp\!\left(-\frac{1-p}{4}
        \frac{\sqrt d}{q^{3/2}}\delta\right).
  \] -/)
  (title := /-- Quantitative sharp-threshold bound -/)
  (latexEnv := "definition")]
noncomputable def sharp_threshold_lower_bound
    (q d L : ℕ) (p δ : ℝ) : ℝ :=
  1 - 2 * (L : ℝ) *
    Real.exp (-((1 - p) / 4) *
      (Real.sqrt (d : ℝ) / Real.rpow (q : ℝ) (3 / 2 : ℝ)) * δ)

@[blueprint "def:is-symmetric-maximum-likelihood-decoder"
  (statement := /-- Let $C\leq\mathbb F^n$ and let $D$ be a randomized decoder.  We call $D$ a symmetric nearest-neighbor decoder if it assigns positive mass only to codewords at minimum Hamming distance from the received word and if, for every channel parameter, its success probability is independent of the transmitted codeword.  On the $q$-ary symmetric channel this is a maximum-likelihood rule whenever the channel parameter $r$ satisfies $0\leq r\leq1-1/q$, where $q=|\mathbb F|$. -/)
  (title := /-- Symmetric nearest-neighbor decoders -/)
  (latexEnv := "definition")]
noncomputable def is_symmetric_maximum_likelihood_decoder
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (C : qary_linear_code 𝔽 n) (D : qary_decoder C) : Prop :=
  (∀ y : Fin n → 𝔽, ∀ c : C, D y c ≠ 0 →
      ∀ c' : C, hammingDist y (c : Fin n → 𝔽) ≤ hammingDist y (c' : Fin n → 𝔽)) ∧
    (∀ r : ℝ, ∀ c c' : C,
      qsc_success_probability C D r c = qsc_success_probability C D r c')

@[blueprint "def:qary-noise-expectation"
  (statement := /-- Let $\mathbb F$ be a finite field, let $n\in\mathbb N$, let $p\in\mathbb R$, and let $f\colon\mathbb F^n\to\mathbb R$.  The $q$-ary $p$-biased expectation of $f$ is
  \[
    \mathbb E_p[f]=\sum_{z\in\mathbb F^n}
      \prod_{i=1}^n\left(\mathbf 1_{z_i=0}(1-p)
        +\mathbf 1_{z_i\ne0}\frac{p}{|\mathbb F|-1}\right)f(z).
  \]
  When $0\leq p\leq1$, this is expectation with respect to independent coordinates that equal zero with probability $1-p$ and otherwise are uniform on $\mathbb F\setminus\{0\}$. -/)
  (title := /-- Expectation under the finite q-ary biased product law -/)
  (latexEnv := "definition")]
noncomputable def qary_noise_expectation
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (p : ℝ) (f : (Fin n → 𝔽) → ℝ) : ℝ :=
  ∑ z : Fin n → 𝔽,
    (∏ i : Fin n,
      if z i = 0 then 1 - p
      else p / ((Fintype.card 𝔽 : ℝ) - 1)) * f z

@[blueprint "def:qary-downward-monotone"
  (statement := /-- Let $\mathbb F$ be a type with zero and let $n\in\mathbb N$.  A function $f\colon\mathbb F^n\to\mathbb R$ is downward monotone if, whenever $x$ is obtained from $y$ by replacing an arbitrary set of coordinates by zero, the implication $f(y)=1\Rightarrow f(x)=1$ holds. -/)
  (title := /-- Downward monotonicity on a q-ary product -/)
  (latexEnv := "definition")]
def qary_downward_monotone
    {𝔽 : Type*} [Zero 𝔽] {n : ℕ} (f : (Fin n → 𝔽) → ℝ) : Prop :=
  ∀ ⦃x y : Fin n → 𝔽⦄,
    (∀ i : Fin n, x i = 0 ∨ x i = y i) → f y = 1 → f x = 1

@[blueprint "def:qary-hamming-boundary"
  (statement := /-- Let $f\colon\mathbb F^n\to\{0,1\}$.  For $z\in\mathbb F^n$, its outgoing downward Hamming boundary count $h_f(z)$ is zero when $f(z)=0$; when $f(z)=1$, it is the number of zero coordinates $i$ for which changing $z_i$ to some nonzero symbol produces a vector on which $f$ vanishes. -/)
  (title := /-- Outgoing Hamming boundary count -/)
  (latexEnv := "definition")]
noncomputable def qary_hamming_boundary
    {𝔽 : Type*} [Zero 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (f : (Fin n → 𝔽) → ℝ) (z : Fin n → 𝔽) : ℕ :=
  if f z = 1 then
    (Finset.univ.filter (fun i : Fin n =>
      z i = 0 ∧ ∃ a : 𝔽, a ≠ 0 ∧ f (Function.update z i a) = 0)).card
  else 0

@[blueprint "def:minimum-positive-boundary"
  (statement := /-- Let $f\colon\mathbb F^n\to\{0,1\}$.  Its minimum positive boundary $\Delta_f$ is the infimum of the positive values assumed by $h_f$.  By convention this infimum is zero when $h_f$ has no positive value. -/)
  (title := /-- Minimum positive Hamming boundary -/)
  (latexEnv := "definition")]
noncomputable def minimum_positive_boundary
    {𝔽 : Type*} [Zero 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (f : (Fin n → 𝔽) → ℝ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ ∃ z : Fin n → 𝔽, qary_hamming_boundary f z = k}

@[blueprint "def:qary-decoding-region-indicator"
  (statement := /-- Let $C\leq\mathbb F^n$ be a linear code and let $D$ be a randomized decoder.  The real-valued indicator of the decoding region of the zero codeword is the function $z\mapsto D(z)(0)$, with the decoder mass regarded as a real number. -/)
  (title := /-- Indicator of the zero-codeword decoding region -/)
  (latexEnv := "definition")]
noncomputable def qary_decoding_region_indicator
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (C : qary_linear_code 𝔽 n) (D : qary_decoder C)
    (z : Fin n → 𝔽) : ℝ :=
  (D z 0).toReal

@[blueprint "def:is-sharp-threshold-decoder"
  (statement := /-- Let $C\leq\mathbb F^n$ and let $D$ be a decoder.  We call $D$ a sharp-threshold nearest-neighbor decoder if it is a symmetric maximum-likelihood decoder, it is deterministic, the decoding region of the zero codeword is downward monotone under replacement of nonzero coordinates by zero, and the minimum positive outgoing boundary of that region is at least $d_{\min}(C)/|\mathbb F|-3$. -/)
  (title := /-- Symmetric nearest-neighbor decoders with monotone regions -/)
  (latexEnv := "definition")]
noncomputable def is_sharp_threshold_decoder
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (C : qary_linear_code 𝔽 n) (D : qary_decoder C) : Prop :=
  is_symmetric_maximum_likelihood_decoder C D ∧
    (∀ y : Fin n → 𝔽, ∀ c : C, D y c = 0 ∨ D y c = 1) ∧
    qary_downward_monotone (qary_decoding_region_indicator C D) ∧
    (linear_code_minimum_distance C : ℝ) / (Fintype.card 𝔽 : ℝ) - 3 ≤
      (minimum_positive_boundary (qary_decoding_region_indicator C D) : ℝ)

@[blueprint "lem:random-list-decoder-baseline-good-error-mass"
  (statement := /-- Let $\mathbb F$ be a finite field, let $n\in\mathbb N$ be positive, and let $p\in\mathbb R$ satisfy $n^{-1/4}\leq p$.  At channel parameter $p-n^{-1/4}$, the total qSC mass of error vectors of Hamming weight at most $pn$ is at least $1/2$. -/)
  (proof := /-- Write the error weight as the sum of its coordinate error indicators.  The product formula in \cref{def:qsc-error-mass} shows directly that their weighted mean is $nr$ and that the weighted second moment about the mean is $nr(1-r)$, where $r=p-n^{-1/4}$.  This variance is at most $n/4$.  By \cref{def:sampling-slack}, the square of the gap between $rn$ and $pn$ is $(n^{-1/4}n)^2=n^{3/2}\geq n$; summing the pointwise second-moment bound therefore shows that the mass above $pn$ is at most $1/4$.  Thus the mass at or below $pn$ is at least $3/4$, and hence at least $1/2$.  If $p\geq1$, every error vector has weight at most $pn$, while the product of the coordinate masses is at least $1$, which proves the same conclusion. -/)
  (title := /-- Sampling slack captures at least half of the qSC error mass -/)
  (latexEnv := "lemma")]
lemma random_list_decoder_baseline_good_error_mass
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : sampling_slack n ≤ p) :
    ENNReal.ofReal (1 / 2) ≤
      ∑ z : Fin n → 𝔽,
        if (hammingDist z 0 : ℝ) ≤ p * (n : ℝ) then
          qsc_error_mass (p - sampling_slack n) z
        else 0 := by
  classical
  let r : ℝ := p - sampling_slack n
  have hs0 : 0 ≤ sampling_slack n := by
    unfold sampling_slack
    exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hr0 : 0 ≤ r := sub_nonneg.mpr hp
  have hq : 1 < Fintype.card 𝔽 := Fintype.one_lt_card
  have hcard : Fintype.card {x : 𝔽 // x ≠ 0} = Fintype.card 𝔽 - 1 := by
    simpa using Fintype.card_subtype_compl (fun x : 𝔽 => x = 0)
  have hcardR : ((Fintype.card 𝔽 - 1 : ℕ) : ℝ) =
      (Fintype.card 𝔽 : ℝ) - 1 := by
    norm_num [Nat.cast_sub hq.le]
  have hqR : (0 : ℝ) < (Fintype.card 𝔽 : ℝ) - 1 := by
    have hq' : (1 : ℝ) < (Fintype.card 𝔽 : ℝ) := by exact_mod_cast hq
    linarith
  have hmass : 1 ≤ ENNReal.ofReal (1 - r) + ENNReal.ofReal r := by
    by_cases hr1 : r ≤ 1
    · rw [← ENNReal.ofReal_add (sub_nonneg.mpr hr1) hr0]
      norm_num
    · have hr1' : 1 ≤ r := le_of_not_ge hr1
      have hone : (1 : ENNReal) ≤ ENNReal.ofReal r := by
        simpa only [ENNReal.one_le_ofReal] using hr1'
      exact hone.trans (le_add_left (le_refl _))
  by_cases hp_one : 1 ≤ p
  · have hgood (z : Fin n → 𝔽) :
        (hammingDist z 0 : ℝ) ≤ p * (n : ℝ) := by
      have hd : (hammingDist z 0 : ℝ) ≤ (n : ℝ) := by
        have hd' : hammingDist z 0 ≤ n := by
          simpa using (hammingDist_le_card_fintype (x := z) (y := 0))
        exact_mod_cast hd'
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      nlinarith
    simp_rw [if_pos (hgood _)]
    simp only [qsc_error_mass]
    let f : Fin n → 𝔽 → ENNReal := fun _ a =>
      if a = 0 then ENNReal.ofReal (1 - r)
      else ENNReal.ofReal (r / ((Fintype.card 𝔽 : ℝ) - 1))
    change ENNReal.ofReal (1 / 2) ≤ ∑ x : Fin n → 𝔽, ∏ i, f i (x i)
    rw [← Fintype.prod_sum]
    calc
      ENNReal.ofReal (1 / 2) ≤ 1 := by norm_num
      _ ≤ ∏ i, ∑ j, f i j := by
        apply Finset.one_le_prod
        intro i hi
        rw [Fintype.sum_eq_add_sum_subtype_ne _ 0]
        simp only [f, if_pos]
        have hx (x : {x : 𝔽 // x ≠ 0}) : (x : 𝔽) ≠ 0 := x.property
        simp_rw [if_neg (hx _)]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [Finset.card_univ, hcard]
        rw [ENNReal.ofReal_div_of_pos hqR]
        have hden : ENNReal.ofReal ((Fintype.card 𝔽 : ℝ) - 1) =
            (Fintype.card 𝔽 - 1 : ℕ) := by
          have hreal : (Fintype.card 𝔽 : ℝ) - 1 =
              ((Fintype.card 𝔽 - 1 : ℕ) : ℝ) := by
            norm_num [Nat.cast_sub hq.le]
          rw [hreal]
          simp
        rw [hden, ENNReal.mul_div_cancel]
        · exact hmass
        · exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt hq)
        · exact ENNReal.natCast_ne_top _
  · have hr1 : r < 1 := by
      dsimp [r]
      linarith
    let a : 𝔽 → ℝ := fun x =>
      if x = 0 then 1 - r else r / ((Fintype.card 𝔽 : ℝ) - 1)
    let indicator : 𝔽 → ℝ := fun x => if x = 0 then 0 else 1
    have ha_sum : ∑ x : 𝔽, a x = 1 := by
      rw [Fintype.sum_eq_add_sum_subtype_ne _ 0]
      simp only [a, if_pos]
      have hx (x : {x : 𝔽 // x ≠ 0}) : (x : 𝔽) ≠ 0 := x.property
      simp_rw [if_neg (hx _)]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcard]
      rw [hcardR]
      field_simp
      ring
    have ha_indicator_sum : ∑ x : 𝔽, a x * indicator x = r := by
      rw [Fintype.sum_eq_add_sum_subtype_ne _ 0]
      simp only [a, indicator, if_pos, mul_zero, zero_add]
      have hx (x : {x : 𝔽 // x ≠ 0}) : (x : 𝔽) ≠ 0 := x.property
      simp_rw [if_neg (hx _)]
      simp only [mul_one, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcard]
      rw [hcardR]
      field_simp
    let W : (Fin n → 𝔽) → ℝ := fun z => ∏ i, a (z i)
    let X : (Fin n → 𝔽) → ℝ := fun z => ∑ i, indicator (z i)
    have ha0 (x : 𝔽) : 0 ≤ a x := by
      dsimp [a]
      split_ifs
      · linarith
      · positivity
    have hW0 (z : Fin n → 𝔽) : 0 ≤ W z := by
      exact Finset.prod_nonneg fun i hi => ha0 (z i)
    have hW_sum : ∑ z : Fin n → 𝔽, W z = 1 := by
      rw [show (∑ z : Fin n → 𝔽, W z) =
          ∏ i : Fin n, ∑ x : 𝔽, a x by
        exact (Fintype.prod_sum (fun _ : Fin n => a)).symm]
      simp [ha_sum]
    have hWI (i : Fin n) :
        ∑ z : Fin n → 𝔽, W z * indicator (z i) = r := by
      let b : Fin n → 𝔽 → ℝ := fun j x =>
        a x * if j = i then indicator x else 1
      rw [show (∑ z : Fin n → 𝔽, W z * indicator (z i)) =
          ∑ z : Fin n → 𝔽, ∏ j, b j (z j) by
        apply Finset.sum_congr rfl
        intro z hz
        dsimp [W, b]
        rw [Finset.prod_mul_distrib]
        simp]
      rw [← Fintype.prod_sum]
      simp [b, ha_sum, ha_indicator_sum]
    have hWIJ (i j : Fin n) :
        ∑ z : Fin n → 𝔽, W z * indicator (z i) * indicator (z j) =
          if i = j then r else r ^ 2 := by
      by_cases hij : i = j
      · subst j
        rw [if_pos rfl, ← hWI i]
        apply Finset.sum_congr rfl
        intro z hz
        dsimp [indicator]
        split_ifs <;> ring
      · rw [if_neg hij]
        let b : Fin n → 𝔽 → ℝ := fun k x =>
          a x * if k = i then indicator x else if k = j then indicator x else 1
        rw [show (∑ z : Fin n → 𝔽, W z * indicator (z i) * indicator (z j)) =
            ∑ z : Fin n → 𝔽, ∏ k, b k (z k) by
          apply Finset.sum_congr rfl
          intro z hz
          dsimp [W, b]
          rw [Finset.prod_mul_distrib]
          rw [show (∏ k : Fin n, if k = i then indicator (z k) else
              if k = j then indicator (z k) else 1) =
              (∏ k : Fin n, if k = i then indicator (z k) else 1) *
                ∏ k : Fin n, if k = j then indicator (z k) else 1 by
            rw [← Finset.prod_mul_distrib]
            apply Finset.prod_congr rfl
            intro k hk
            by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all]
          simp
          ring]
        rw [← Fintype.prod_sum]
        simp only [b]
        simp_rw [show ∀ k : Fin n,
            (∑ x : 𝔽, a x * if k = i then indicator x else
              if k = j then indicator x else 1) =
              if k = i then r else if k = j then r else 1 by
          intro k
          by_cases hki : k = i
          · simp [hki, ha_indicator_sum]
          · by_cases hkj : k = j
            · simp [hki, hkj, ha_indicator_sum]
            · simp [hki, hkj, ha_sum]]
        rw [show (∏ k : Fin n, if k = i then r else if k = j then r else 1) =
            (∏ k : Fin n, if k = i then r else 1) *
              ∏ k : Fin n, if k = j then r else 1 by
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro k hk
          by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all]
        simp [pow_two]
    have hEX : ∑ z : Fin n → 𝔽, W z * X z = (n : ℝ) * r := by
      simp_rw [X, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp [hWI, nsmul_eq_mul]
    have hEX2 : ∑ z : Fin n → 𝔽, W z * (X z) ^ 2 =
        (n : ℝ) * r + (n : ℝ) * ((n : ℝ) - 1) * r ^ 2 := by
      rw [show (∑ z : Fin n → 𝔽, W z * (X z) ^ 2) =
          ∑ i : Fin n, ∑ j : Fin n,
            ∑ z : Fin n → 𝔽, W z * indicator (z i) * indicator (z j) by
        simp only [X, pow_two, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro z hz
        ring]
      simp_rw [hWIJ]
      rw [show (∑ i : Fin n, ∑ j : Fin n, if i = j then r else r ^ 2) =
          ∑ i : Fin n, (r + ((n : ℝ) - 1) * r ^ 2) by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Fintype.sum_eq_add_sum_subtype_ne _ i]
        simp only [if_pos]
        have hj (j : {j : Fin n // j ≠ i}) : i ≠ (j : Fin n) := by
          exact fun h => j.property h.symm
        simp_rw [if_neg (hj _)]
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        have hcardi : Fintype.card {j : Fin n // j ≠ i} = n - 1 := by
          simpa using Fintype.card_subtype_compl (fun j : Fin n => j = i)
        rw [hcardi]
        have hnR : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          norm_num [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn))]
        rw [hnR]]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_fin]
      ring
    have hVar : ∑ z : Fin n → 𝔽, W z * (X z - (n : ℝ) * r) ^ 2 =
        (n : ℝ) * r * (1 - r) := by
      rw [show (∑ z : Fin n → 𝔽, W z * (X z - (n : ℝ) * r) ^ 2) =
          ∑ z : Fin n → 𝔽,
            (W z * (X z) ^ 2 - 2 * ((n : ℝ) * r) * (W z * X z) +
              ((n : ℝ) * r) ^ 2 * W z) by
        apply Finset.sum_congr rfl
        intro z hz
        ring]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
      rw [hEX2, hEX, hW_sum]
      ring
    have hX (z : Fin n → 𝔽) : X z = (hammingDist z 0 : ℝ) := by
      change (∑ i : Fin n, if z i = 0 then 0 else 1) =
        ((Finset.univ.filter (fun i : Fin n => z i ≠ 0)).card : ℝ)
      rw [Finset.card_eq_sum_ones]
      push_cast
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hzi : z i = 0 <;> simp [hzi]
    have hweight (z : Fin n → 𝔽) :
        ENNReal.toReal (qsc_error_mass (p - sampling_slack n) z) = W z := by
      have hr1' : 0 ≤ 1 - r := sub_nonneg.mpr hr1.le
      have hrq : 0 ≤ r / ((Fintype.card 𝔽 : ℝ) - 1) :=
        div_nonneg hr0 hqR.le
      simp only [qsc_error_mass, ENNReal.toReal_prod]
      change (∏ i : Fin n,
          (if z i = 0 then ENNReal.ofReal (1 - r)
          else ENNReal.ofReal (r / ((Fintype.card 𝔽 : ℝ) - 1))).toReal) =
        ∏ i : Fin n, a (z i)
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hzi : z i = 0 <;> simp [a, hzi, hr1', hrq]
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hslack_sq : (n : ℝ) ≤
        (sampling_slack n * (n : ℝ)) ^ 2 := by
      have hpow : (n : ℝ) ≤ Real.rpow (n : ℝ) (3 / 2 : ℝ) := by
        simpa using Real.rpow_le_rpow_of_exponent_le hnR1
          (show (1 : ℝ) ≤ 3 / 2 by norm_num)
      calc
        (n : ℝ) ≤ Real.rpow (n : ℝ) (3 / 2 : ℝ) := hpow
        _ = (Real.rpow (n : ℝ) (3 / 4 : ℝ)) ^ 2 := by
          have h := Real.rpow_mul_natCast hnR.le (3 / 4 : ℝ) 2
          convert h using 1 <;> norm_num
        _ = (sampling_slack n * (n : ℝ)) ^ 2 := by
          congr 1
          unfold sampling_slack
          have h := Real.rpow_add hnR (-(1 / 4 : ℝ)) 1
          rw [Real.rpow_one] at h
          convert h using 1 <;> norm_num
    have hrvar : r * (1 - r) ≤ 1 / 4 := by
      nlinarith [sq_nonneg (r - 1 / 2)]
    have hVar_le : ∑ z : Fin n → 𝔽, W z * (X z - (n : ℝ) * r) ^ 2 ≤
        (n : ℝ) / 4 := by
      rw [hVar]
      nlinarith [mul_nonneg hnR.le (sub_nonneg.mpr hrvar)]
    let B : ℝ := ∑ z : Fin n → 𝔽,
      if p * (n : ℝ) < X z then W z else 0
    have hbad_point (z : Fin n → 𝔽) :
        (if p * (n : ℝ) < X z then W z else 0) * (n : ℝ) ≤
          W z * (X z - (n : ℝ) * r) ^ 2 := by
      split_ifs with hz
      · have hrdef : p = r + sampling_slack n := by
          dsimp [r]
          ring
        have hdev : sampling_slack n * (n : ℝ) <
            X z - (n : ℝ) * r := by
          nlinarith
        have hsprod0 : 0 ≤ sampling_slack n * (n : ℝ) :=
          mul_nonneg hs0 hnR.le
        have hdev0 : 0 ≤ X z - (n : ℝ) * r := le_trans hsprod0 hdev.le
        have hsq : (sampling_slack n * (n : ℝ)) ^ 2 ≤
            (X z - (n : ℝ) * r) ^ 2 := by nlinarith
        have hn_sq : (n : ℝ) ≤ (X z - (n : ℝ) * r) ^ 2 :=
          hslack_sq.trans hsq
        nlinarith [mul_nonneg (hW0 z) (sub_nonneg.mpr hn_sq)]
      · simp only [if_neg hz, zero_mul]
        exact mul_nonneg (hW0 z) (sq_nonneg _)
    have hBn : B * (n : ℝ) ≤ (n : ℝ) / 4 := by
      calc
        B * (n : ℝ) = ∑ z : Fin n → 𝔽,
            (if p * (n : ℝ) < X z then W z else 0) * (n : ℝ) := by
          dsimp [B]
          rw [Finset.sum_mul]
        _ ≤ ∑ z : Fin n → 𝔽, W z * (X z - (n : ℝ) * r) ^ 2 := by
          apply Finset.sum_le_sum
          intro z hz
          exact hbad_point z
        _ ≤ (n : ℝ) / 4 := hVar_le
    have hB : B ≤ 1 / 4 := by
      nlinarith
    let G : ℝ := ∑ z : Fin n → 𝔽,
      if X z ≤ p * (n : ℝ) then W z else 0
    have hGB : G + B = 1 := by
      rw [← hW_sum]
      dsimp [G, B]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hgood : X z ≤ p * (n : ℝ)
      · simp [hgood, not_lt.mpr hgood]
      · have hbad : p * (n : ℝ) < X z := lt_of_not_ge hgood
        simp [hgood, hbad]
    have hG : 1 / 2 ≤ G := by
      nlinarith
    have hterm_top (z : Fin n → 𝔽) :
        (if (hammingDist z 0 : ℝ) ≤ p * (n : ℝ) then
          qsc_error_mass (p - sampling_slack n) z else 0) ≠ ⊤ := by
      split_ifs
      · unfold qsc_error_mass
        apply ENNReal.prod_ne_top
        intro i hi
        split_ifs <;> exact ENNReal.ofReal_ne_top
      · exact ENNReal.zero_ne_top
    have hsum_top : (∑ z : Fin n → 𝔽,
        if (hammingDist z 0 : ℝ) ≤ p * (n : ℝ) then
          qsc_error_mass (p - sampling_slack n) z else 0) ≠ ⊤ := by
      exact (ENNReal.sum_ne_top).2 fun z hz => hterm_top z
    apply (ENNReal.ofReal_le_iff_le_toReal hsum_top).2
    rw [ENNReal.toReal_sum (fun z hz => hterm_top z)]
    simp only [apply_ite, ENNReal.toReal_zero]
    calc
      1 / 2 ≤ G := hG
      _ = ∑ z : Fin n → 𝔽,
          if (hammingDist z 0 : ℝ) ≤ p * (n : ℝ) then
            ENNReal.toReal (qsc_error_mass (p - sampling_slack n) z)
          else 0 := by
        dsimp [G]
        apply Finset.sum_congr rfl
        intro z hz
        rw [hX z, hweight z]
        rfl

@[blueprint "lem:random-list-decoder-baseline"
  (statement := /-- Let $\mathbb F$ be a finite field, let $n\in\mathbb N$ be positive, let $p\in\mathbb R$, let $L\in\mathbb N$ be positive, and let $C\leq\mathbb F^n$ be $(p,L)$-list-decodable.  If $n^{-1/4}\leq p$, then there exists a randomized decoder $D$ for $C$ such that, for every $c\in C$, its success mass at channel parameter $p-n^{-1/4}$ is at least $1/(2L)$. -/)
  (proof := /-- For each received word whose radius-$pn$ list is nonempty, let $D$ be uniform on that list; if the list is empty, let it output the zero codeword.  This defines a probability mass function as required by \cref{def:qary-decoder}.  By \cref{def:list-decodable}, every nonempty list has cardinality at most $L$.  Whenever the channel error has weight at most $pn$, the transmitted codeword belongs to the corresponding list, so $D$ assigns it mass at least $1/L$.  By \cref{lem:random-list-decoder-baseline-good-error-mass}, such errors have total channel mass at least $1/2$.  Summing their contributions in \cref{def:qsc-success-probability} gives success mass at least $(1/L)(1/2)=1/(2L)$ for every transmitted codeword. -/)
  (title := /-- The random-list decoder has a nonnegligible baseline success probability -/)
  (latexEnv := "lemma")]
lemma random_list_decoder_baseline
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (hn : 0 < n) (C : qary_linear_code 𝔽 n)
    {p : ℝ} {L : ℕ} (hp : sampling_slack n ≤ p) (hL : 0 < L)
    (hlist : list_decodable C p L) :
    ∃ D : qary_decoder C, ∀ c : C,
      ENNReal.ofReal (1 / (2 * (L : ℝ))) ≤
        qsc_success_probability C D (p - sampling_slack n) c := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  let S : (Fin n → 𝔽) → Finset C := fun y =>
    Finset.univ.filter
      (fun c : C => (hammingDist y (c : Fin n → 𝔽) : ℝ) ≤ p * (n : ℝ))
  have hS_card (y : Fin n → 𝔽) : (S y).card ≤ L := by
    simpa [list_decodable, S] using hlist y
  let uniform (s : Finset C) (hs : s.Nonempty) : PMF C := by
    refine ⟨(fun a => if a ∈ s then (s.card : ENNReal)⁻¹ else 0), ?_⟩
    have hsum : ∑ a ∈ s,
        (if a ∈ s then (s.card : ENNReal)⁻¹ else 0) = 1 := by
      simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const,
        nsmul_eq_mul]
      have hs0 : (s.card : ENNReal) ≠ 0 := by
        simpa only [ne_eq, Nat.cast_eq_zero, Finset.card_eq_zero] using hs.ne_empty
      exact ENNReal.mul_inv_cancel hs0 (ENNReal.natCast_ne_top s.card)
    exact hsum ▸ hasSum_sum_of_ne_finset_zero (fun a ha => by simp [ha])
  let D : qary_decoder C := fun y =>
    if hs : (S y).Nonempty then uniform (S y) hs
    else uniform {0} (by simp)
  refine ⟨D, ?_⟩
  intro c
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hpoint (z : Fin n → 𝔽)
      (hz : (hammingDist z 0 : ℝ) ≤ p * (n : ℝ)) :
      ENNReal.ofReal (1 / (L : ℝ)) ≤
        D ((c : Fin n → 𝔽) + z) c := by
    have hc_mem : c ∈ S ((c : Fin n → 𝔽) + z) := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [hammingDist] using hz
    have hS_nonempty : (S ((c : Fin n → 𝔽) + z)).Nonempty := ⟨c, hc_mem⟩
    rw [show D ((c : Fin n → 𝔽) + z) c =
        ((S ((c : Fin n → 𝔽) + z)).card : ENNReal)⁻¹ by
      simp only [D, dif_pos hS_nonempty]
      change (if c ∈ S ((c : Fin n → 𝔽) + z) then
        ((S ((c : Fin n → 𝔽) + z)).card : ENNReal)⁻¹ else 0) = _
      simp [hc_mem]]
    rw [ENNReal.ofReal_div_of_pos hLr]
    simpa using
      (ENNReal.inv_le_inv.mpr
        (show ((S ((c : Fin n → 𝔽) + z)).card : ENNReal) ≤ (L : ENNReal) by
          exact_mod_cast hS_card ((c : Fin n → 𝔽) + z)))
  rw [qsc_success_probability]
  calc
    ENNReal.ofReal (1 / (2 * (L : ℝ))) =
        ENNReal.ofReal (1 / 2) * ENNReal.ofReal (1 / (L : ℝ)) := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / 2)]
      congr 1
      field_simp
    _ ≤ (∑ z : Fin n → 𝔽,
          if (hammingDist z 0 : ℝ) ≤ p * (n : ℝ) then
            qsc_error_mass (p - sampling_slack n) z
          else 0) * ENNReal.ofReal (1 / (L : ℝ)) :=
      mul_le_mul_right'
        (random_list_decoder_baseline_good_error_mass hn hp)
        (ENNReal.ofReal (1 / (L : ℝ)))
    _ = ∑ z : Fin n → 𝔽,
          (if (hammingDist z 0 : ℝ) ≤ p * (n : ℝ) then
            qsc_error_mass (p - sampling_slack n) z
          else 0) * ENNReal.ofReal (1 / (L : ℝ)) := by
      rw [Finset.sum_mul]
    _ ≤ ∑ z : Fin n → 𝔽,
          qsc_error_mass (p - sampling_slack n) z *
            D ((c : Fin n → 𝔽) + z) c := by
      apply Finset.sum_le_sum
      intro z hzmem
      split_ifs with hz
      · exact mul_le_mul_left' (hpoint z hz) _
      · simp

@[blueprint "lem:symmetric-maximum-likelihood-baseline-error-mass-by-weight"
  (statement := /-- Let $\mathbb F$ be a finite field of cardinality $q$, let $n\in\mathbb N$, let $r\in\mathbb R$, and let $z\in\mathbb F^n$.  Then the qSC mass of $z$ is
  \[
    (1-r)^{n-\operatorname{wt}(z)}
      \left(\frac{r}{q-1}\right)^{\operatorname{wt}(z)},
  \]
  where real factors are embedded in the extended nonnegative reals by taking their nonnegative parts. -/)
  (proof := /-- Partition the coordinates into the zero and nonzero coordinates in the product defining the qSC error mass in \cref{def:qsc-error-mass}.  The second part has cardinality $\operatorname{wt}(z)$, and the first has the complementary cardinality $n-\operatorname{wt}(z)$, giving the displayed product. -/)
  (title := /-- The qSC error mass depends only on Hamming weight -/)
  (latexEnv := "lemma")]
lemma symmetric_maximum_likelihood_baseline_error_mass_by_weight
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (r : ℝ) (z : Fin n → 𝔽) :
    qsc_error_mass r z =
      ENNReal.ofReal (1 - r) ^ (n - hammingDist z 0) *
        ENNReal.ofReal (r / ((Fintype.card 𝔽 : ℝ) - 1)) ^ hammingDist z 0 := by
  classical
  unfold qsc_error_mass
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have hpart := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun i : Fin n => z i = 0)
  have hnonzero :
      (Finset.univ.filter (fun i : Fin n => ¬z i = 0)).card =
        hammingDist z 0 := by
    simp [hammingDist]
  have hzero :
      (Finset.univ.filter (fun i : Fin n => z i = 0)).card =
        n - hammingDist z 0 := by
    rw [hnonzero, Finset.card_univ, Fintype.card_fin] at hpart
    omega
  rw [hzero, hnonzero]

@[blueprint "lem:symmetric-maximum-likelihood-baseline-error-mass-antitone"
  (statement := /-- Let $\mathbb F$ be a finite field of cardinality $q$, let $0\leq r\leq1-1/q$, and let $z,z'\in\mathbb F^n$.  If $\operatorname{wt}(z)\leq\operatorname{wt}(z')$, then the qSC mass of $z'$ is at most that of $z$. -/)
  (proof := /-- The range assumption gives $r/(q-1)\leq1-r$.  Apply the weight formula in \cref{lem:symmetric-maximum-likelihood-baseline-error-mass-by-weight}; replacing each of the additional nonzero-coordinate factors in $z'$ by a zero-coordinate factor can only increase the product. -/)
  (title := /-- qSC error mass decreases with Hamming weight in the maximum-likelihood range -/)
  (latexEnv := "lemma")]
lemma symmetric_maximum_likelihood_baseline_error_mass_antitone
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} {r : ℝ} (hr₀ : 0 ≤ r)
    (hrML : r ≤ 1 - 1 / (Fintype.card 𝔽 : ℝ))
    {z z' : Fin n → 𝔽} (hweight : hammingDist z 0 ≤ hammingDist z' 0) :
    qsc_error_mass r z' ≤ qsc_error_mass r z := by
  have hq : 1 < Fintype.card 𝔽 := Fintype.one_lt_card
  have hqR : (0 : ℝ) < (Fintype.card 𝔽 : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hqR' : (1 : ℝ) < (Fintype.card 𝔽 : ℝ) := by exact_mod_cast hq
  have hqm1R : (0 : ℝ) < (Fintype.card 𝔽 : ℝ) - 1 := by linarith
  have hscaled := mul_le_mul_of_nonneg_right hrML hqR.le
  have hscaled' : r * (Fintype.card 𝔽 : ℝ) ≤ (Fintype.card 𝔽 : ℝ) - 1 := by
    calc
      r * (Fintype.card 𝔽 : ℝ) ≤
          (1 - 1 / (Fintype.card 𝔽 : ℝ)) * (Fintype.card 𝔽 : ℝ) := hscaled
      _ = (Fintype.card 𝔽 : ℝ) - 1 := by field_simp
  have hratio : r / ((Fintype.card 𝔽 : ℝ) - 1) ≤ 1 - r := by
    rw [div_le_iff₀ hqm1R]
    nlinarith
  have hab : ENNReal.ofReal (r / ((Fintype.card 𝔽 : ℝ) - 1)) ≤
      ENNReal.ofReal (1 - r) := ENNReal.ofReal_le_ofReal hratio
  have hweight_le_n : hammingDist z' 0 ≤ n := by
    simpa using (hammingDist_le_card_fintype (x := z') (y := 0))
  have hsplit_weight : hammingDist z' 0 =
      (hammingDist z' 0 - hammingDist z 0) + hammingDist z 0 := by
    omega
  have hsplit_zero : n - hammingDist z 0 =
      (n - hammingDist z' 0) + (hammingDist z' 0 - hammingDist z 0) := by
    omega
  have hpow_weight :
      ENNReal.ofReal (r / ((Fintype.card 𝔽 : ℝ) - 1)) ^ hammingDist z' 0 =
        ENNReal.ofReal (r / ((Fintype.card 𝔽 : ℝ) - 1)) ^
            (hammingDist z' 0 - hammingDist z 0) *
          ENNReal.ofReal (r / ((Fintype.card 𝔽 : ℝ) - 1)) ^
            hammingDist z 0 := by
    conv_lhs => rw [hsplit_weight]
    rw [pow_add]
  have hpow_zero :
      ENNReal.ofReal (1 - r) ^ (n - hammingDist z 0) =
        ENNReal.ofReal (1 - r) ^ (n - hammingDist z' 0) *
          ENNReal.ofReal (1 - r) ^
            (hammingDist z' 0 - hammingDist z 0) := by
    conv_lhs => rw [hsplit_zero]
    rw [pow_add]
  rw [symmetric_maximum_likelihood_baseline_error_mass_by_weight r z',
    symmetric_maximum_likelihood_baseline_error_mass_by_weight r z]
  calc
    ENNReal.ofReal (1 - r) ^ (n - hammingDist z' 0) *
          ENNReal.ofReal (r / ((Fintype.card 𝔽 : ℝ) - 1)) ^ hammingDist z' 0 =
        ENNReal.ofReal (1 - r) ^ (n - hammingDist z' 0) *
          (ENNReal.ofReal (r / ((Fintype.card 𝔽 : ℝ) - 1)) ^
              (hammingDist z' 0 - hammingDist z 0) *
            ENNReal.ofReal (r / ((Fintype.card 𝔽 : ℝ) - 1)) ^
              hammingDist z 0) := by rw [hpow_weight]
    _ ≤ ENNReal.ofReal (1 - r) ^ (n - hammingDist z' 0) *
          (ENNReal.ofReal (1 - r) ^
              (hammingDist z' 0 - hammingDist z 0) *
            ENNReal.ofReal (r / ((Fintype.card 𝔽 : ℝ) - 1)) ^
              hammingDist z 0) := by gcongr
    _ = ENNReal.ofReal (1 - r) ^ (n - hammingDist z 0) *
          ENNReal.ofReal (r / ((Fintype.card 𝔽 : ℝ) - 1)) ^
            hammingDist z 0 := by rw [hpow_zero]; ac_rfl

@[blueprint "lem:symmetric-maximum-likelihood-baseline"
  (statement := /-- Let $\mathbb F$ be a finite field of cardinality $q$, let $C\leq\mathbb F^n$, and let $0\leq r<1$ satisfy $r\leq1-1/q$.  If a randomized decoder $D$ succeeds on every codeword with probability at least $b$, then there exists a symmetric nearest-neighbor decoder $D^*$ whose success probability on every codeword is at least $b$. -/)
  (proof := /-- For a received word $y$, let $S_y$ be the nonempty set of codewords at minimum Hamming distance from $y$, and let $D^*(y)$ be the uniform probability mass function on $S_y$; this is a decoder in the sense of \cref{def:qary-decoder}.  Translation by any $c\in C$ bijects $S_z$ with $S_{c+z}$ and sends $0$ to $c$.  Hence
  \[
    D^*(c+z)(c)=D^*(z)(0).
  \]
  It follows directly from \cref{def:qsc-success-probability} that the success probability of $D^*$ is independent of the transmitted codeword for every real channel parameter.  Its support is $S_y$, so it also satisfies the nearest-neighbor clause of \cref{def:is-symmetric-maximum-likelihood-decoder}.

  Fix $y$ and choose $m_y\in S_y$.  By \cref{lem:symmetric-maximum-likelihood-baseline-error-mass-antitone}, for every $d\in C$,
  \[
    \Pr_r[y-d]\leq \Pr_r[y-m_y],
  \]
  with equality whenever $d\in S_y$.  Since both $D(y)$ and $D^*(y)$ have total mass one, their likelihood-weighted averages therefore satisfy
  \[
    \sum_{d\in C}\Pr_r[y-d]D(y)(d)
      \leq \Pr_r[y-m_y]
      =\sum_{d\in C}\Pr_r[y-d]D^*(y)(d).
  \]
  Reindexing each channel-error sum by $y=c+z$, summing this pointwise inequality over $y$, and using \cref{def:qsc-success-probability} gives
  \[
    \sum_{c\in C}\Pr[D(c+z)=c]
      \leq \sum_{c\in C}\Pr[D^*(c+z)=c].
  \]
  The hypothesis bounds the left-hand side below by $|C|\,\operatorname{ofReal}(b)$, while symmetry makes the right-hand side equal to $|C|$ times the success probability of $D^*$ at the zero codeword.  Since $C$ is nonempty and finite, cancellation yields the required lower bound at zero; symmetry gives the same bound for every codeword. -/)
  (title := /-- Symmetric maximum-likelihood replacement -/)
  (latexEnv := "lemma")]
lemma symmetric_maximum_likelihood_baseline
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (C : qary_linear_code 𝔽 n) {r b : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (hrML : r ≤ 1 - 1 / (Fintype.card 𝔽 : ℝ)) (D : qary_decoder C)
    (hD : ∀ c : C, ENNReal.ofReal b ≤ qsc_success_probability C D r c) :
    ∃ Dstar : qary_decoder C,
      is_symmetric_maximum_likelihood_decoder C Dstar ∧
        ∀ c : C, ENNReal.ofReal b ≤ qsc_success_probability C Dstar r c := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  let S : (Fin n → 𝔽) → Finset C := fun y =>
    Finset.univ.filter (fun c : C =>
      ∀ c' : C, hammingDist y (c : Fin n → 𝔽) ≤ hammingDist y (c' : Fin n → 𝔽))
  have hS_nonempty (y : Fin n → 𝔽) : (S y).Nonempty := by
    obtain ⟨c, hc, hmin⟩ := Finset.exists_min_image
      (Finset.univ : Finset C) (fun c : C => hammingDist y (c : Fin n → 𝔽))
      ⟨0, Finset.mem_univ 0⟩
    refine ⟨c, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun c' => hmin c' (Finset.mem_univ c')
  let uniform (s : Finset C) (hs : s.Nonempty) : PMF C := by
    refine ⟨(fun a => if a ∈ s then (s.card : ENNReal)⁻¹ else 0), ?_⟩
    have hsum : ∑ a ∈ s,
        (if a ∈ s then (s.card : ENNReal)⁻¹ else 0) = 1 := by
      simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const,
        nsmul_eq_mul]
      have hs0 : (s.card : ENNReal) ≠ 0 := by
        simpa only [ne_eq, Nat.cast_eq_zero, Finset.card_eq_zero] using hs.ne_empty
      exact ENNReal.mul_inv_cancel hs0 (ENNReal.natCast_ne_top s.card)
    exact hsum ▸ hasSum_sum_of_ne_finset_zero (fun a ha => by simp [ha])
  let Dstar : qary_decoder C := fun y => uniform (S y) (hS_nonempty y)
  have htranslate (a x y : Fin n → 𝔽) :
      hammingDist (a + x) (a + y) = hammingDist x y := by
    change hammingDist (fun i => a i + x i) (fun i => a i + y i) = hammingDist x y
    exact hammingDist_comp (fun i (u : 𝔽) => a i + u)
      (fun i => add_right_injective (a i))
  have hdist_translate (z : Fin n → 𝔽) (c d : C) :
      hammingDist ((c : Fin n → 𝔽) + z) (d : Fin n → 𝔽) =
        hammingDist z ((d - c : C) : Fin n → 𝔽) := by
    rw [show (d : Fin n → 𝔽) =
        (c : Fin n → 𝔽) + ((d - c : C) : Fin n → 𝔽) by ext i; simp]
    exact htranslate (c : Fin n → 𝔽) z ((d - c : C) : Fin n → 𝔽)
  have hS_translate_mem (z : Fin n → 𝔽) (c d : C) :
      d ∈ S ((c : Fin n → 𝔽) + z) ↔ d - c ∈ S z := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hd e
      calc
        hammingDist z (((d - c : C) : C) : Fin n → 𝔽) =
            hammingDist ((c : Fin n → 𝔽) + z) (d : Fin n → 𝔽) :=
          (hdist_translate z c d).symm
        _ ≤ hammingDist ((c : Fin n → 𝔽) + z) ((e + c : C) : Fin n → 𝔽) :=
          hd (e + c)
        _ = hammingDist z (e : Fin n → 𝔽) := by
          rw [hdist_translate]
          congr 2
          simp
    · intro hd e
      calc
        hammingDist ((c : Fin n → 𝔽) + z) (d : Fin n → 𝔽) =
            hammingDist z ((d - c : C) : Fin n → 𝔽) := hdist_translate z c d
        _ ≤ hammingDist z ((e - c : C) : Fin n → 𝔽) := hd (e - c)
        _ = hammingDist ((c : Fin n → 𝔽) + z) (e : Fin n → 𝔽) :=
          (hdist_translate z c e).symm
  have hS_translate_card (z : Fin n → 𝔽) (c : C) :
      (S ((c : Fin n → 𝔽) + z)).card = (S z).card := by
    apply Finset.card_bij'
      (fun d _ => d - c) (fun e _ => e + c)
    · intro d hd
      exact (hS_translate_mem z c d).mp hd
    · intro e he
      apply (hS_translate_mem z c (e + c)).mpr
      simpa using he
    · intro d hd
      simp
    · intro e he
      simp
  have hDstar_translate (z : Fin n → 𝔽) (c : C) :
      Dstar ((c : Fin n → 𝔽) + z) c = Dstar z 0 := by
    change (if c ∈ S ((c : Fin n → 𝔽) + z) then
        ((S ((c : Fin n → 𝔽) + z)).card : ENNReal)⁻¹ else 0) =
      (if (0 : C) ∈ S z then ((S z).card : ENNReal)⁻¹ else 0)
    rw [hS_translate_card]
    by_cases hc : c ∈ S ((c : Fin n → 𝔽) + z)
    · have hzero : (0 : C) ∈ S z := by
        simpa using (hS_translate_mem z c c).mp hc
      simp [hc, hzero]
    · have hzero : (0 : C) ∉ S z := by
        intro hzero
        apply hc
        apply (hS_translate_mem z c c).mpr
        simpa using hzero
      simp [hc, hzero]
  have hsym : is_symmetric_maximum_likelihood_decoder C Dstar := by
    constructor
    · intro y c hc c'
      have hcS : c ∈ S y := by
        by_contra hcn
        apply hc
        change (if c ∈ S y then ((S y).card : ENNReal)⁻¹ else 0) = 0
        simp [hcn]
      have hcmin : ∀ d : C,
          hammingDist y (c : Fin n → 𝔽) ≤ hammingDist y (d : Fin n → 𝔽) := by
        simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hcS
      exact hcmin c'
    · intro t c c'
      rw [qsc_success_probability, qsc_success_probability]
      apply Finset.sum_congr rfl
      intro z hz
      rw [hDstar_translate z c, hDstar_translate z c']
  refine ⟨Dstar, hsym, ?_⟩
  intro c
  have hweight_sub (y : Fin n → 𝔽) (d : C) :
      hammingDist (y - (d : Fin n → 𝔽)) 0 =
        hammingDist y (d : Fin n → 𝔽) := by
    simp [hammingDist, sub_eq_zero]
  let m : (Fin n → 𝔽) → C := fun y => (hS_nonempty y).choose
  have hm_mem (y : Fin n → 𝔽) : m y ∈ S y := (hS_nonempty y).choose_spec
  have hm_min (y : Fin n → 𝔽) (d : C) :
      hammingDist y (m y : Fin n → 𝔽) ≤ hammingDist y (d : Fin n → 𝔽) := by
    have hm := hm_mem y
    have hm' : ∀ e : C,
        hammingDist y (m y : Fin n → 𝔽) ≤ hammingDist y (e : Fin n → 𝔽) := by
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hm
    exact hm' d
  have hmass_max (y : Fin n → 𝔽) (d : C) :
      qsc_error_mass r (y - (d : Fin n → 𝔽)) ≤
        qsc_error_mass r (y - (m y : Fin n → 𝔽)) := by
    apply symmetric_maximum_likelihood_baseline_error_mass_antitone hr₀ hrML
    rw [hweight_sub, hweight_sub]
    exact hm_min y d
  have hmass_eq_of_mem (y : Fin n → 𝔽) (d : C) (hd : d ∈ S y) :
      qsc_error_mass r (y - (d : Fin n → 𝔽)) =
        qsc_error_mass r (y - (m y : Fin n → 𝔽)) := by
    apply le_antisymm (hmass_max y d)
    apply symmetric_maximum_likelihood_baseline_error_mass_antitone hr₀ hrML
    rw [hweight_sub, hweight_sub]
    have hdmin : ∀ e : C,
        hammingDist y (d : Fin n → 𝔽) ≤ hammingDist y (e : Fin n → 𝔽) := by
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hd
    exact hdmin (m y)
  have hpmf_sum (E : qary_decoder C) (y : Fin n → 𝔽) :
      ∑ d : C, E y d = 1 := by
    simpa only [tsum_fintype] using PMF.tsum_coe (E y)
  have hpoint_D (y : Fin n → 𝔽) :
      (∑ d : C, qsc_error_mass r (y - (d : Fin n → 𝔽)) * D y d) ≤
        qsc_error_mass r (y - (m y : Fin n → 𝔽)) := by
    calc
      (∑ d : C, qsc_error_mass r (y - (d : Fin n → 𝔽)) * D y d) ≤
          ∑ d : C, qsc_error_mass r (y - (m y : Fin n → 𝔽)) * D y d := by
        apply Finset.sum_le_sum
        intro d hd
        exact mul_le_mul_right' (hmass_max y d) _
      _ = qsc_error_mass r (y - (m y : Fin n → 𝔽)) * ∑ d : C, D y d := by
        rw [Finset.mul_sum]
      _ = qsc_error_mass r (y - (m y : Fin n → 𝔽)) := by rw [hpmf_sum, mul_one]
  have hpoint_Dstar (y : Fin n → 𝔽) :
      (∑ d : C, qsc_error_mass r (y - (d : Fin n → 𝔽)) * Dstar y d) =
        qsc_error_mass r (y - (m y : Fin n → 𝔽)) := by
    calc
      (∑ d : C, qsc_error_mass r (y - (d : Fin n → 𝔽)) * Dstar y d) =
          ∑ d : C, qsc_error_mass r (y - (m y : Fin n → 𝔽)) * Dstar y d := by
        apply Finset.sum_congr rfl
        intro d hd
        by_cases hdS : d ∈ S y
        · rw [hmass_eq_of_mem y d hdS]
        · have hzero : Dstar y d = 0 := by
            change (if d ∈ S y then ((S y).card : ENNReal)⁻¹ else 0) = 0
            simp [hdS]
          simp [hzero]
      _ = qsc_error_mass r (y - (m y : Fin n → 𝔽)) * ∑ d : C, Dstar y d := by
        rw [Finset.mul_sum]
      _ = qsc_error_mass r (y - (m y : Fin n → 𝔽)) := by rw [hpmf_sum, mul_one]
  have hsum_success (E : qary_decoder C) :
      (∑ d : C, qsc_success_probability C E r d) =
        ∑ d : C, ∑ y : Fin n → 𝔽,
          qsc_error_mass r (y - (d : Fin n → 𝔽)) * E y d := by
    unfold qsc_success_probability
    apply Finset.sum_congr rfl
    intro d hd
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      (Equiv.sum_comp (Equiv.addLeft (d : Fin n → 𝔽))
        (fun y : Fin n → 𝔽 =>
          qsc_error_mass r (y - (d : Fin n → 𝔽)) * E y d))
  have htotal :
      (∑ d : C, qsc_success_probability C D r d) ≤
        ∑ d : C, qsc_success_probability C Dstar r d := by
    calc
      (∑ d : C, qsc_success_probability C D r d) =
          ∑ d : C, ∑ y : Fin n → 𝔽,
            qsc_error_mass r (y - (d : Fin n → 𝔽)) * D y d := hsum_success D
      _ = ∑ y : Fin n → 𝔽, ∑ d : C,
            qsc_error_mass r (y - (d : Fin n → 𝔽)) * D y d := Finset.sum_comm
      _ ≤ ∑ y : Fin n → 𝔽, ∑ d : C,
            qsc_error_mass r (y - (d : Fin n → 𝔽)) * Dstar y d := by
        apply Finset.sum_le_sum
        intro y hy
        rw [hpoint_Dstar y]
        exact hpoint_D y
      _ = ∑ d : C, ∑ y : Fin n → 𝔽,
            qsc_error_mass r (y - (d : Fin n → 𝔽)) * Dstar y d := Finset.sum_comm
      _ = ∑ d : C, qsc_success_probability C Dstar r d := (hsum_success Dstar).symm
  have hcard0 : (Fintype.card C : ENNReal) ≠ 0 := by simp
  have hcardtop : (Fintype.card C : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hzero_sym (d : C) :
      qsc_success_probability C Dstar r d = qsc_success_probability C Dstar r 0 :=
    hsym.2 r d 0
  have hscaled : ENNReal.ofReal b * (Fintype.card C : ENNReal) ≤
      qsc_success_probability C Dstar r 0 * (Fintype.card C : ENNReal) := by
    calc
      ENNReal.ofReal b * (Fintype.card C : ENNReal) =
          ∑ d : C, ENNReal.ofReal b := by
        simp [nsmul_eq_mul, mul_comm]
      _ ≤ ∑ d : C, qsc_success_probability C D r d := by
        apply Finset.sum_le_sum
        intro d hd
        exact hD d
      _ ≤ ∑ d : C, qsc_success_probability C Dstar r d := htotal
      _ = ∑ d : C, qsc_success_probability C Dstar r 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        exact hzero_sym d
      _ = qsc_success_probability C Dstar r 0 * (Fintype.card C : ENNReal) := by
        simp [nsmul_eq_mul, mul_comm]
  have hbase_zero : ENNReal.ofReal b ≤ qsc_success_probability C Dstar r 0 :=
    (ENNReal.mul_le_mul_iff_left hcard0 hcardtop).mp hscaled
  exact hbase_zero.trans_eq (hsym.2 r 0 c)

@[blueprint "lem:large-support-outside-error"
  (statement := /-- Let $\mathbb F$ be a finite field, let $n\in\mathbb N$, let $C\leq\mathbb F^n$, let $0\ne c\in C$, let $z\in\mathbb F^n$, and let $\nu\in\mathbb N$.  Suppose that $d(z,0)\leq d(z,c)$ and that
  $d(z,c)\leq d(z,c')+\nu$ for every $c'\in C$.  Then
  \[
    d_{\min}(C)\leq |\mathbb F|
      \left(\left|\operatorname{supp}(c)
        \setminus\operatorname{supp}(z)\right|+\nu\right).
  \] -/)
  (proof := /-- Put
  $S=\operatorname{supp}(c)\setminus\operatorname{supp}(z)$,
  $I=\operatorname{supp}(c)\cap\operatorname{supp}(z)$, and
  $T=\{i\in I:z_i=c_i\}$.  Counting the contribution of each coordinate gives
  \[
    d(z,0)+|S|=d(z,c)+|T|.
  \]
  Hence $d(z,0)\leq d(z,c)$ implies $|T|\leq|S|$.

  Let $A=\mathbb F\setminus\{0\}$, and for $a\in A$ put
  $B_a=\{i\in I:z_i/c_i=a\}$.  The sets $B_a$ partition $I$.  Choose
  $\alpha\in A$ for which $|B_\alpha|$ is maximal.  Double counting and
  $|A|=|\mathbb F|-1$ give
  \[
    |I|=\sum_{a\in A}|B_a|
      \leq (|\mathbb F|-1)|B_\alpha|.
  \]
  A second coordinatewise count gives
  \[
    d(z,c)+|T|=d(z,\alpha c)+|B_\alpha|.
  \]
  Applying the near-nearest hypothesis to the codeword $\alpha c$ yields
  $|B_\alpha|\leq|T|+\nu\leq|S|+\nu$.  Consequently
  $|I|\leq(|\mathbb F|-1)(|S|+\nu)$.

  The support of $c$ is the disjoint union of $S$ and $I$, so
  \[
    \operatorname{wt}(c)=|S|+|I|
      \leq |\mathbb F|(|S|+\nu).
  \]
  Since $c\ne0$, \cref{def:linear-code-minimum-distance} gives
  $d_{\min}(C)\leq\operatorname{wt}(c)$, which proves the claim. -/)
  (title := /-- A near-nearest codeword has many fresh support coordinates -/)
  (latexEnv := "lemma")]
lemma large_support_outside_error
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (C : qary_linear_code 𝔽 n) (z : Fin n → 𝔽)
    (c : C) (hc : c ≠ 0) (ν : ℕ)
    (hzero : hammingDist z 0 ≤ hammingDist z (c : Fin n → 𝔽))
    (hnear : ∀ c' : C,
      hammingDist z (c : Fin n → 𝔽) ≤
        hammingDist z (c' : Fin n → 𝔽) + ν) :
    linear_code_minimum_distance C ≤ Fintype.card 𝔽 *
      ((Finset.univ.filter (fun i : Fin n =>
        (c : Fin n → 𝔽) i ≠ 0 ∧ z i = 0)).card + ν) := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun i =>
    (c : Fin n → 𝔽) i ≠ 0 ∧ z i = 0)
  let I : Finset (Fin n) := Finset.univ.filter (fun i =>
    (c : Fin n → 𝔽) i ≠ 0 ∧ z i ≠ 0)
  let T : Finset (Fin n) := Finset.univ.filter (fun i =>
    (c : Fin n → 𝔽) i ≠ 0 ∧ z i = (c : Fin n → 𝔽) i)
  have hbalance :
      hammingDist z 0 + S.card =
        hammingDist z (c : Fin n → 𝔽) + T.card := by
    simp only [hammingDist, S, T, Finset.card_eq_sum_ones]
    repeat rw [Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hci : (c : Fin n → 𝔽) i = 0
    · simp [hci]
    by_cases hzi : z i = 0
    · simp [hci, Ne.symm hci, hzi]
    by_cases hzci : z i = (c : Fin n → 𝔽) i <;>
      simp [hci, Ne.symm hci, hzi, hzci]
  have hTleS : T.card ≤ S.card := by
    omega
  let A : Finset 𝔽 := Finset.univ.filter (fun a => a ≠ 0)
  let f : Fin n → 𝔽 := fun i => z i / (c : Fin n → 𝔽) i
  let B : 𝔽 → Finset (Fin n) := fun a => I.filter (fun i => f i = a)
  have hAnonempty : A.Nonempty := by
    refine ⟨1, ?_⟩
    simp [A]
  obtain ⟨α, hαA, hαmax⟩ :=
    Finset.exists_max_image A (fun a => (B a).card) hAnonempty
  have hα0 : α ≠ 0 := by
    simpa [A] using hαA
  have hf_maps : ∀ i ∈ I, f i ∈ A := by
    intro i hi
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [A, f, Finset.mem_filter, Finset.mem_univ, true_and]
    exact div_ne_zero hi.2 hi.1
  have hIavg : I.card ≤ A.card * (B α).card := by
    have hsum : ∑ a ∈ A, (B a).card = I.card := by
      calc
        ∑ a ∈ A, (B a).card =
            ∑ a ∈ A, ∑ i ∈ I, if f i = a then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          change (I.filter (fun i => f i = a)).card = _
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        _ = ∑ i ∈ I, ∑ a ∈ A, if f i = a then 1 else 0 := by
          rw [Finset.sum_comm]
        _ = ∑ i ∈ I, 1 := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [hf_maps i hi]
        _ = I.card := by rw [Finset.card_eq_sum_ones]
    rw [← hsum]
    calc
      ∑ a ∈ A, (B a).card ≤ ∑ _a ∈ A, (B α).card := by
        exact Finset.sum_le_sum fun a ha => hαmax a ha
      _ = A.card * (B α).card := by simp
  have hdistance :
      hammingDist z (c : Fin n → 𝔽) + T.card =
        hammingDist z ((α • c : C) : Fin n → 𝔽) + (B α).card := by
    simp only [hammingDist, B, I, f, T, Finset.card_eq_sum_ones]
    repeat rw [Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hci : (c : Fin n → 𝔽) i = 0
    · simp [hci]
    by_cases hzi : z i = 0
    · simp [hci, Ne.symm hci, hzi, hα0]
    have hdiv : z i / (c : Fin n → 𝔽) i = α ↔
        z i = α * (c : Fin n → 𝔽) i := div_eq_iff hci
    by_cases hzci : z i = (c : Fin n → 𝔽) i <;>
      by_cases hzαci : z i = α * (c : Fin n → 𝔽) i <;>
        simp [hci, Ne.symm hci, hzi, hα0, hdiv, hzci, hzαci] <;>
          by_cases hα1 : α = 1 <;> simp_all
  have hB : (B α).card ≤ T.card + ν := by
    have hnearα := hnear (α • c)
    omega
  have hI : I.card ≤ A.card * (S.card + ν) := by
    calc
      I.card ≤ A.card * (B α).card := hIavg
      _ ≤ A.card * (T.card + ν) := Nat.mul_le_mul_left _ hB
      _ ≤ A.card * (S.card + ν) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_right hTleS ν)
  have hweight :
      hammingDist (c : Fin n → 𝔽) 0 = S.card + I.card := by
    simp only [hammingDist, S, I, Finset.card_eq_sum_ones]
    repeat rw [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hci : (c : Fin n → 𝔽) i = 0
    · simp [hci]
    by_cases hzi : z i = 0 <;> simp [hci, Ne.symm hci, hzi]
  have hdmin :
      linear_code_minimum_distance C ≤
        hammingDist (c : Fin n → 𝔽) 0 := by
    unfold linear_code_minimum_distance
    exact Nat.sInf_le ⟨c, hc, rfl⟩
  have hAcard : A.card = Fintype.card 𝔽 - 1 := by
    have hpart := Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (fun a : 𝔽 => a = 0)
    have hzeroCard :
        (Finset.univ.filter (fun a : 𝔽 => a = 0)).card = 1 := by
      have hset : Finset.univ.filter (fun a : 𝔽 => a = 0) = {0} := by
        ext a
        simp
      rw [hset]
      simp
    have hnonzeroCard :
        (Finset.univ.filter (fun a : 𝔽 => ¬a = 0)).card = A.card := by rfl
    rw [hzeroCard, hnonzeroCard, Finset.card_univ] at hpart
    omega
  have hq : 1 < Fintype.card 𝔽 := Fintype.one_lt_card
  have hAq : A.card + 1 = Fintype.card 𝔽 := by
    rw [hAcard]
    omega
  calc
    linear_code_minimum_distance C ≤
        hammingDist (c : Fin n → 𝔽) 0 := hdmin
    _ = S.card + I.card := hweight
    _ ≤ S.card + A.card * (S.card + ν) := Nat.add_le_add_left hI _
    _ ≤ (A.card + 1) * (S.card + ν) := by nlinarith
    _ = Fintype.card 𝔽 * (S.card + ν) := by rw [hAq]
    _ = Fintype.card 𝔽 *
        ((Finset.univ.filter (fun i : Fin n =>
          (c : Fin n → 𝔽) i ≠ 0 ∧ z i = 0)).card + ν) := by rfl

@[blueprint "lem:sharp-threshold-maximum-likelihood-baseline"
  (statement := /-- Let $C\leq\mathbb F^n$, let $b,r\in\mathbb R$ satisfy $0\leq r<1$ and $r\leq1-1/|\mathbb F|$, and let $D$ be a randomized decoder such that, for every $c\in C$, its success probability at parameter $r$ is at least $\operatorname{ofReal}(b)$.  Then there exists a deterministic symmetric nearest-neighbor decoder $D^*$ whose zero-codeword decoding region is downward monotone, whose minimum positive outgoing boundary is at least $d_{\min}(C)/|\mathbb F|-3$, and whose success probability at parameter $r$ is at least $\operatorname{ofReal}(b)$ for every $c\in C$. -/)
  (proof := /-- For each received word $y$, consider the finite set of errors $y-c$, with $c\in C$.  Among those of minimum Hamming weight, choose the error having the largest lexicographic key, where the symbol $0$ has key $0$ and every nonzero field symbol has a distinct positive key.  Decode to the corresponding codeword and put unit mass there.  Translation by a codeword leaves the error set, the chosen error, and the tie key unchanged; hence this decoder is deterministic, translation symmetric, and nearest-neighbour.  First apply \cref{lem:symmetric-maximum-likelihood-baseline} to the original decoder, obtaining a maximum-likelihood decoder $D_{\mathrm{ml}}$ with the same common success lower bound.  By \cref{lem:symmetric-maximum-likelihood-baseline-error-mass-antitone}, the channel mass of every competing error is at most that of the chosen minimum-weight error.  Multiplying these pointwise inequalities by the probabilities of $D_{\mathrm{ml}}$ and summing first over codewords and then over received words shows that the deterministic decoder has at least the total success of $D_{\mathrm{ml}}$.  Translation symmetry makes all of the deterministic decoder's per-codeword successes equal, so the common lower bound is preserved.

  To prove downward monotonicity, suppose that $y$ is decoded to zero and that $x$ is obtained from $y$ by replacing coordinates by zero.  For every codeword $c$, a coordinatewise comparison gives
  \[
    d(x,0)+d(y,c)\leq d(x,c)+d(y,0).
  \]
  Since $y$ is nearest to zero, $x$ is also nearest to zero.  Equality for a codeword tied with zero at $x$ forces that codeword to vanish on every removed coordinate.  Consequently the lexicographic comparison between the errors $y-c$ and $y$ is preserved between $x-c$ and $x$, so the maximal-key rule decodes $x$ to zero.

  Now let $z$ have positive outgoing boundary, and let changing its zero coordinate $i$ to a nonzero symbol produce a word decoded to a nonzero codeword $c$.  The triangle inequality and nearest-neighbour property give
  \[
    d(z,0)\leq d(z,c)\leq d(z,0)+2.
  \]
  With $S=\{j:c_j\ne0,\ z_j=0\}$, \cref{lem:large-support-outside-error} applied with $\nu=2$ yields
  \[
    d_{\min}(C)\leq |\mathbb F|\,(|S|+2).
  \]
  Let $m$ be the least element of $S$.  For each $j\in S\setminus\{m\}$, change $z_j$ to $c_j$.  If this word were still decoded to zero, distance comparison would force the extremal equality $d(z,c)=d(z,0)+2$.  The triggering update at $i$ then also gives a distance tie and forces $i\in S$, so $m\leq i$.  Its tie comparison says that the key of the zero-codeword error is no larger than the key of the $c$-error.  The prefixes before $m$ are unchanged by both the triggering update and the update at $j$, while at $m$ the new zero-codeword error has symbol $0$ and the $c$-error has the nonzero symbol $-c_m$.  Thus the latter key is strictly larger, contradicting the assumption that the update at $j$ is decoded to zero.  Hence $S\setminus\{m\}$ lies in the outgoing boundary, and every positive boundary $h$ satisfies
  \[
    d_{\min}(C)\leq |\mathbb F|\,(h+3).
  \]
  If $d_{\min}(C)=0$, the required real inequality is immediate.  Otherwise a nonzero codeword is outside the zero decoding region.  Choose an outside word of minimum Hamming weight and erase one nonzero coordinate; minimality places the erased word inside the region and makes its boundary positive.  The set of positive boundary values is therefore nonempty, so its natural-number infimum is attained.  Applying the preceding bound at a minimizer and dividing by $|\mathbb F|>0$ gives the required minimum-boundary inequality. -/)
  (title := /-- A monotone symmetric maximum-likelihood decoder attains the baseline -/)
  (latexEnv := "lemma")]
lemma sharp_threshold_maximum_likelihood_baseline
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (C : qary_linear_code 𝔽 n) {r b : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (hrML : r ≤ 1 - 1 / (Fintype.card 𝔽 : ℝ)) (D : qary_decoder C)
    (hD : ∀ c : C, ENNReal.ofReal b ≤ qsc_success_probability C D r c) :
    ∃ Dstar : qary_decoder C,
      is_sharp_threshold_decoder C Dstar ∧
        ∀ c : C, ENNReal.ofReal b ≤
          qsc_success_probability C Dstar r c := by
  classical
  let support (z : Fin n → 𝔽) : Finset (Fin n) :=
    Finset.univ.filter (fun i => z i ≠ 0)
  let symbolCode (a : 𝔽) : ℕ :=
    if a = 0 then 0 else ((Fintype.equivFin 𝔽) a : ℕ) + 1
  let tieKey (z : Fin n → 𝔽) : List ℕ :=
    List.ofFn (fun i => symbolCode (z i))
  let errors (y : Fin n → 𝔽) : Finset (Fin n → 𝔽) :=
    Finset.univ.image (fun c : C => y - (c : Fin n → 𝔽))
  have herrors_nonempty (y : Fin n → 𝔽) : (errors y).Nonempty := by
    refine ⟨y, ?_⟩
    simp [errors]
  let nearest (y : Fin n → 𝔽) : Finset (Fin n → 𝔽) :=
    (errors y).filter (fun z =>
      ∀ w ∈ errors y, hammingDist z 0 ≤ hammingDist w 0)
  have hnearest_nonempty (y : Fin n → 𝔽) : (nearest y).Nonempty := by
    obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image
      (errors y) (fun z => hammingDist z 0) (herrors_nonempty y)
    refine ⟨z, ?_⟩
    simp only [nearest, Finset.mem_filter, hz, true_and]
    exact fun w hw => hmin w hw
  let best (y : Fin n → 𝔽) : Finset (Fin n → 𝔽) :=
    (nearest y).filter (fun z =>
      ∀ w ∈ nearest y, tieKey w ≤ tieKey z)
  have hbest_nonempty (y : Fin n → 𝔽) : (best y).Nonempty := by
    obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image
      (nearest y) tieKey (hnearest_nonempty y)
    refine ⟨z, ?_⟩
    simp only [best, Finset.mem_filter, hz, true_and]
    exact fun w hw => hmax w hw
  let leader (y : Fin n → 𝔽) : Fin n → 𝔽 := (hbest_nonempty y).choose
  have hleader_best (y : Fin n → 𝔽) : leader y ∈ best y :=
    (hbest_nonempty y).choose_spec
  have hleader_nearest (y : Fin n → 𝔽) : leader y ∈ nearest y :=
    (Finset.mem_filter.mp (hleader_best y)).1
  have hleader_errors (y : Fin n → 𝔽) : leader y ∈ errors y :=
    (Finset.mem_filter.mp (hleader_nearest y)).1
  have hleader_min (y : Fin n → 𝔽) (w : Fin n → 𝔽)
      (hw : w ∈ errors y) :
      hammingDist (leader y) 0 ≤ hammingDist w 0 :=
    (Finset.mem_filter.mp (hleader_nearest y)).2 w hw
  have hleader_max (y : Fin n → 𝔽) (w : Fin n → 𝔽)
      (hw : w ∈ nearest y) :
      tieKey w ≤ tieKey (leader y) :=
    (Finset.mem_filter.mp (hleader_best y)).2 w hw
  let chosen (y : Fin n → 𝔽) : C :=
    ⟨y - leader y, by
      obtain ⟨c, hc, hcy⟩ := Finset.mem_image.mp (hleader_errors y)
      simp only [Finset.mem_univ] at hc
      have hyc : y - leader y = (c : Fin n → 𝔽) := by
        rw [← hcy]
        abel
      rw [hyc]
      exact c.property⟩
  let point (a : C) : PMF C := by
    refine ⟨(fun c => if c ∈ ({a} : Finset C) then
      (({a} : Finset C).card : ENNReal)⁻¹ else 0), ?_⟩
    have hsum : ∑ c ∈ ({a} : Finset C),
        (if c ∈ ({a} : Finset C) then
          (({a} : Finset C).card : ENNReal)⁻¹ else 0) = 1 := by
      simp
    exact hsum ▸ hasSum_sum_of_ne_finset_zero (fun c hc => by simp [hc])
  have hpoint_apply (a c : C) :
      point a c = if c = a then 1 else 0 := by
    change (if c ∈ ({a} : Finset C) then
      (({a} : Finset C).card : ENNReal)⁻¹ else 0) =
        if c = a then 1 else 0
    simp
  let Dstar : qary_decoder C := fun y => point (chosen y)
  have herrors_translate (y : Fin n → 𝔽) (c : C) :
      errors ((c : Fin n → 𝔽) + y) = errors y := by
    ext z
    simp only [errors, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨d, rfl⟩
      refine ⟨d - c, ?_⟩
      simp only [Submodule.coe_sub]
      abel
    · rintro ⟨d, rfl⟩
      refine ⟨c + d, ?_⟩
      simp only [Submodule.coe_add]
      abel
  have hnearest_translate (y : Fin n → 𝔽) (c : C) :
      nearest ((c : Fin n → 𝔽) + y) = nearest y := by
    simp only [nearest, herrors_translate]
  have hbest_translate (y : Fin n → 𝔽) (c : C) :
      best ((c : Fin n → 𝔽) + y) = best y := by
    simp only [best, hnearest_translate]
  have hleader_translate (y : Fin n → 𝔽) (c : C) :
      leader ((c : Fin n → 𝔽) + y) = leader y := by
    simp only [leader, hbest_translate]
  have hchosen_translate (y : Fin n → 𝔽) (c : C) :
      chosen ((c : Fin n → 𝔽) + y) = c + chosen y := by
    apply Subtype.ext
    simp only [chosen, Submodule.coe_add, hleader_translate]
    abel
  have hDstar_translate (z : Fin n → 𝔽) (c : C) :
      Dstar ((c : Fin n → 𝔽) + z) c = Dstar z 0 := by
    rw [show Dstar ((c : Fin n → 𝔽) + z) c =
      point (chosen ((c : Fin n → 𝔽) + z)) c by rfl]
    rw [show Dstar z 0 = point (chosen z) 0 by rfl]
    rw [hpoint_apply, hpoint_apply, hchosen_translate]
    by_cases h : chosen z = 0
    · simp [h]
    · have h' : (0 : C) ≠ chosen z := by exact Ne.symm h
      simp [h, h']
  have hchosen_error (y : Fin n → 𝔽) :
      y - (chosen y : Fin n → 𝔽) = leader y := by
    simp only [chosen]
    abel
  have hweight_sub (y : Fin n → 𝔽) (c : C) :
      hammingDist (y - (c : Fin n → 𝔽)) 0 =
        hammingDist y (c : Fin n → 𝔽) := by
    simp [hammingDist, sub_eq_zero]
  have hsym : is_symmetric_maximum_likelihood_decoder C Dstar := by
    constructor
    · intro y c hc c'
      have hcy : c = chosen y := by
        rw [show Dstar y c = point (chosen y) c by rfl, hpoint_apply] at hc
        by_contra hne
        simp [hne] at hc
      subst c
      rw [← hweight_sub y (chosen y), ← hweight_sub y c', hchosen_error]
      exact hleader_min y (y - (c' : Fin n → 𝔽)) (by simp [errors])
    · intro t c c'
      rw [qsc_success_probability, qsc_success_probability]
      apply Finset.sum_congr rfl
      intro z hz
      rw [hDstar_translate z c, hDstar_translate z c']
  have hdet : ∀ y : Fin n → 𝔽, ∀ c : C, Dstar y c = 0 ∨ Dstar y c = 1 := by
    intro y c
    rw [show Dstar y c = point (chosen y) c by rfl, hpoint_apply]
    by_cases hc : c = chosen y
    · simp [hc]
    · simp [hc]
  obtain ⟨Dml, _, hDml⟩ :=
    symmetric_maximum_likelihood_baseline C hr₀ hr₁ hrML D hD
  have hmass_max (y : Fin n → 𝔽) (d : C) :
      qsc_error_mass r (y - (d : Fin n → 𝔽)) ≤
        qsc_error_mass r (leader y) := by
    apply symmetric_maximum_likelihood_baseline_error_mass_antitone hr₀ hrML
    exact hleader_min y (y - (d : Fin n → 𝔽)) (by simp [errors])
  have hpmf_sum (E : qary_decoder C) (y : Fin n → 𝔽) :
      ∑ d : C, E y d = 1 := by
    simpa only [tsum_fintype] using PMF.tsum_coe (E y)
  have hpoint_Dml (y : Fin n → 𝔽) :
      (∑ d : C, qsc_error_mass r (y - (d : Fin n → 𝔽)) * Dml y d) ≤
        qsc_error_mass r (leader y) := by
    calc
      (∑ d : C, qsc_error_mass r (y - (d : Fin n → 𝔽)) * Dml y d) ≤
          ∑ d : C, qsc_error_mass r (leader y) * Dml y d := by
        apply Finset.sum_le_sum
        intro d hd
        exact mul_le_mul_right' (hmass_max y d) _
      _ = qsc_error_mass r (leader y) * ∑ d : C, Dml y d := by
        rw [Finset.mul_sum]
      _ = qsc_error_mass r (leader y) := by rw [hpmf_sum, mul_one]
  have hpoint_Dstar (y : Fin n → 𝔽) :
      (∑ d : C, qsc_error_mass r (y - (d : Fin n → 𝔽)) * Dstar y d) =
        qsc_error_mass r (leader y) := by
    rw [Finset.sum_eq_single (chosen y)]
    · rw [show Dstar y (chosen y) = point (chosen y) (chosen y) by rfl,
        hpoint_apply, if_pos rfl, mul_one, hchosen_error]
    · intro d hd hne
      rw [show Dstar y d = point (chosen y) d by rfl, hpoint_apply,
        if_neg hne, mul_zero]
    · intro h
      simp at h
  have hsum_success (E : qary_decoder C) :
      (∑ d : C, qsc_success_probability C E r d) =
        ∑ d : C, ∑ y : Fin n → 𝔽,
          qsc_error_mass r (y - (d : Fin n → 𝔽)) * E y d := by
    unfold qsc_success_probability
    apply Finset.sum_congr rfl
    intro d hd
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      (Equiv.sum_comp (Equiv.addLeft (d : Fin n → 𝔽))
        (fun y : Fin n → 𝔽 =>
          qsc_error_mass r (y - (d : Fin n → 𝔽)) * E y d))
  have htotal :
      (∑ d : C, qsc_success_probability C Dml r d) ≤
        ∑ d : C, qsc_success_probability C Dstar r d := by
    calc
      (∑ d : C, qsc_success_probability C Dml r d) =
          ∑ d : C, ∑ y : Fin n → 𝔽,
            qsc_error_mass r (y - (d : Fin n → 𝔽)) * Dml y d := hsum_success Dml
      _ = ∑ y : Fin n → 𝔽, ∑ d : C,
            qsc_error_mass r (y - (d : Fin n → 𝔽)) * Dml y d := Finset.sum_comm
      _ ≤ ∑ y : Fin n → 𝔽, ∑ d : C,
            qsc_error_mass r (y - (d : Fin n → 𝔽)) * Dstar y d := by
        apply Finset.sum_le_sum
        intro y hy
        rw [hpoint_Dstar y]
        exact hpoint_Dml y
      _ = ∑ d : C, ∑ y : Fin n → 𝔽,
            qsc_error_mass r (y - (d : Fin n → 𝔽)) * Dstar y d := Finset.sum_comm
      _ = ∑ d : C, qsc_success_probability C Dstar r d :=
        (hsum_success Dstar).symm
  have hcard0 : (Fintype.card C : ENNReal) ≠ 0 := by simp
  have hcardtop : (Fintype.card C : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hzero_sym (d : C) :
      qsc_success_probability C Dstar r d = qsc_success_probability C Dstar r 0 :=
    hsym.2 r d 0
  have hscaled : ENNReal.ofReal b * (Fintype.card C : ENNReal) ≤
      qsc_success_probability C Dstar r 0 * (Fintype.card C : ENNReal) := by
    calc
      ENNReal.ofReal b * (Fintype.card C : ENNReal) =
          ∑ d : C, ENNReal.ofReal b := by simp [nsmul_eq_mul, mul_comm]
      _ ≤ ∑ d : C, qsc_success_probability C Dml r d := by
        apply Finset.sum_le_sum
        intro d hd
        exact hDml d
      _ ≤ ∑ d : C, qsc_success_probability C Dstar r d := htotal
      _ = ∑ d : C, qsc_success_probability C Dstar r 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        exact hzero_sym d
      _ = qsc_success_probability C Dstar r 0 * (Fintype.card C : ENNReal) := by
        simp [nsmul_eq_mul, mul_comm]
  have hbase_zero : ENNReal.ofReal b ≤ qsc_success_probability C Dstar r 0 :=
    (ENNReal.mul_le_mul_iff_left hcard0 hcardtop).mp hscaled
  have hbase : ∀ c : C,
      ENNReal.ofReal b ≤ qsc_success_probability C Dstar r c := by
    intro c
    exact hbase_zero.trans_eq (hsym.2 r 0 c)
  have hsymbolCode_injective : Function.Injective symbolCode := by
    intro a d h
    by_cases ha : a = 0
    · subst a
      by_contra hd
      have hd' : d ≠ 0 := Ne.symm hd
      simp [symbolCode, hd'] at h
    · by_cases hd : d = 0
      · subst d
        simp [symbolCode, ha] at h
      · apply (Fintype.equivFin 𝔽).injective
        apply Fin.ext
        simpa [symbolCode, ha, hd] using h
  have htieKey_injective : Function.Injective tieKey := by
    intro z w h
    have hf : (fun i => symbolCode (z i)) =
        (fun i => symbolCode (w i)) := by
      exact List.ofFn_inj.mp (by simpa [tieKey] using h)
    funext i
    exact hsymbolCode_injective (congrFun hf i)
  have hchosen_zero (z : Fin n → 𝔽) :
      chosen z = 0 ↔ leader z = z := by
    constructor
    · intro h
      have hv := congrArg Subtype.val h
      simp only [chosen, Submodule.coe_zero] at hv
      exact (sub_eq_zero.mp hv).symm
    · intro h
      apply Subtype.ext
      simp only [chosen, Submodule.coe_zero]
      exact sub_eq_zero.mpr h.symm
  have hregion (z : Fin n → 𝔽) :
      qary_decoding_region_indicator C Dstar z = 1 ↔ leader z = z := by
    change (Dstar z 0).toReal = 1 ↔ leader z = z
    rw [show Dstar z 0 = point (chosen z) 0 by rfl, hpoint_apply]
    by_cases h : chosen z = 0
    · have h' : (0 : C) = chosen z := h.symm
      simp [h', (hchosen_zero z).mp h]
    · have h' : (0 : C) ≠ chosen z := Ne.symm h
      have hl : leader z ≠ z := fun hz => h ((hchosen_zero z).mpr hz)
      simp [h', hl]
  have hleader_eq_of_max (y : Fin n → 𝔽) (hy : y ∈ nearest y)
      (hmax : tieKey (leader y) ≤ tieKey y) : leader y = y := by
    apply htieKey_injective
    exact le_antisymm hmax (hleader_max y y hy)
  have hlex_preserve :
      ∀ (m : ℕ) (a b a' b' : Fin m → ℕ),
        (∀ i, (a' i = a i ∧ b' i = b i) ∨
          (a i = b i ∧ a' i = b' i)) →
        List.ofFn a ≤ List.ofFn b → List.ofFn a' ≤ List.ofFn b' := by
    intro m
    induction m with
    | zero =>
        intro a b a' b' hp hle
        simp
    | succ m ih =>
        intro a b a' b' hp hle
        simp only [List.ofFn_succ] at hle ⊢
        have hp0 := hp 0
        have hpt : ∀ i : Fin m,
            (a' i.succ = a i.succ ∧ b' i.succ = b i.succ) ∨
            (a i.succ = b i.succ ∧ a' i.succ = b' i.succ) :=
          fun i => hp i.succ
        rcases hp0 with hsame | hequal
        · rcases lt_or_eq_of_le hle with hlt | heq
          · have hlex := (List.lt_iff_lex_lt _ _).mp hlt
            rw [List.cons_lex_cons_iff] at hlex
            rcases hlex with hhead | ⟨hhead, htail⟩
            · apply le_of_lt
              exact List.Lex.rel (by simpa [hsame.1, hsame.2] using hhead)
            · rw [hsame.1, hsame.2, hhead]
              exact List.cons_le_cons _ (ih _ _ _ _ hpt (le_of_lt htail))
          · have hparts := List.cons.inj heq
            rw [hsame.1, hsame.2, hparts.1]
            exact List.cons_le_cons _ (ih _ _ _ _ hpt hparts.2.le)
        · have htail : List.ofFn (fun i => a i.succ) ≤
              List.ofFn (fun i => b i.succ) := by
            rcases lt_or_eq_of_le hle with hlt | heq
            · have hlex := (List.lt_iff_lex_lt _ _).mp hlt
              rw [List.cons_lex_cons_iff] at hlex
              rcases hlex with hhead | ⟨hhead, htail⟩
              · exact (lt_irrefl _ (hequal.1 ▸ hhead)).elim
              · exact le_of_lt htail
            · exact (List.cons.inj heq).2.le
          rw [hequal.2]
          exact List.cons_le_cons _ (ih _ _ _ _ hpt htail)
  have hdown :
      qary_downward_monotone (qary_decoding_region_indicator C Dstar) := by
    intro x y hxy hy
    rw [hregion] at hy ⊢
    have hymin (c : C) :
        hammingDist y 0 ≤ hammingDist y (c : Fin n → 𝔽) := by
      have hm := hleader_min y (y - (c : Fin n → 𝔽)) (by simp [errors])
      rw [hweight_sub] at hm
      simpa only [hy] using hm
    have hquad (c : C) :
        hammingDist x 0 + hammingDist y (c : Fin n → 𝔽) ≤
          hammingDist x (c : Fin n → 𝔽) + hammingDist y 0 := by
      simp only [hammingDist, Finset.card_eq_sum_ones]
      repeat rw [Finset.sum_filter]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i hi
      rcases hxy i with hxi | hxi
      · rw [hxi]
        by_cases hyi : y i = 0 <;>
          by_cases hci : (c : Fin n → 𝔽) i = 0 <;>
            by_cases hyci : y i = (c : Fin n → 𝔽) i <;>
              simp [hyi, hci, hyci] <;> omega
      · rw [hxi]
        by_cases hyi : y i = 0 <;>
          by_cases hci : (c : Fin n → 𝔽) i = 0 <;>
            by_cases hyci : y i = (c : Fin n → 𝔽) i <;>
              simp [hyi, hci, hyci] <;> omega
    have hxmin (c : C) :
        hammingDist x 0 ≤ hammingDist x (c : Fin n → 𝔽) := by
      have := hquad c
      have := hymin c
      omega
    have hxnear : x ∈ nearest x := by
      simp only [nearest, Finset.mem_filter]
      constructor
      · simp [errors]
      · intro w hw
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hw
        rw [hweight_sub]
        exact hxmin c
    let c : C := chosen x
    have hcx : hammingDist x (c : Fin n → 𝔽) = hammingDist x 0 := by
      apply le_antisymm
      · rw [← hweight_sub x c, hchosen_error]
        exact hleader_min x x (by simp [errors])
      · exact hxmin c
    have hcy : hammingDist y (c : Fin n → 𝔽) = hammingDist y 0 := by
      apply le_antisymm
      · have := hquad c
        omega
      · exact hymin c
    have hyerror_near : y - (c : Fin n → 𝔽) ∈ nearest y := by
      simp only [nearest, Finset.mem_filter]
      constructor
      · simp [errors]
      · intro w hw
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hw
        rw [hweight_sub, hweight_sub, hcy]
        exact hymin d
    have hkey_y :
        tieKey (y - (c : Fin n → 𝔽)) ≤ tieKey y := by
      simpa only [hy] using
        (hleader_max y (y - (c : Fin n → 𝔽)) hyerror_near)
    have hquad_eq :
        hammingDist x 0 + hammingDist y (c : Fin n → 𝔽) =
          hammingDist x (c : Fin n → 𝔽) + hammingDist y 0 := by
      omega
    have hc_removed (i : Fin n) (hxi : x i = 0) (hxyi : x i ≠ y i) :
        (c : Fin n → 𝔽) i = 0 := by
      by_contra hci
      have hstrict :
          hammingDist x 0 + hammingDist y (c : Fin n → 𝔽) <
            hammingDist x (c : Fin n → 𝔽) + hammingDist y 0 := by
        simp only [hammingDist, Finset.card_eq_sum_ones]
        repeat rw [Finset.sum_filter]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_lt_sum
        · intro j hj
          rcases hxy j with hxj | hxj
          · rw [hxj]
            by_cases hyj : y j = 0 <;>
              by_cases hcj : (c : Fin n → 𝔽) j = 0 <;>
                by_cases hycj : y j = (c : Fin n → 𝔽) j <;>
                  simp [hyj, hcj, hycj] <;> omega
          · rw [hxj]
            by_cases hyj : y j = 0 <;>
              by_cases hcj : (c : Fin n → 𝔽) j = 0 <;>
                by_cases hycj : y j = (c : Fin n → 𝔽) j <;>
                  simp [hyj, hcj, hycj] <;> omega
        · refine ⟨i, Finset.mem_univ i, ?_⟩
          change ((if x i ≠ 0 then 1 else 0) +
              if y i ≠ (c : Fin n → 𝔽) i then 1 else 0) <
            (if x i ≠ (c : Fin n → 𝔽) i then 1 else 0) +
              if y i ≠ 0 then 1 else 0
          have hyi : y i ≠ 0 := by
            intro hyi
            exact hxyi (hxi.trans hyi.symm)
          have hci' : (0 : 𝔽) ≠ (c : Fin n → 𝔽) i := Ne.symm hci
          by_cases hyci : y i = (c : Fin n → 𝔽) i <;>
            simp [hxi, hyi, hci, hci', hyci] <;> omega
      omega
    have hkey_x : tieKey (leader x) ≤ tieKey x := by
      rw [← hchosen_error x]
      simp only [tieKey]
      apply hlex_preserve n
        (fun i => symbolCode ((y - (c : Fin n → 𝔽)) i))
        (fun i => symbolCode (y i))
        (fun i => symbolCode ((x - (c : Fin n → 𝔽)) i))
        (fun i => symbolCode (x i))
      · intro i
        by_cases hsame : x i = y i
        · left
          simp [hsame]
        · right
          have hxi : x i = 0 := by
            rcases hxy i with hxi | hxi
            · exact hxi
            · exact (hsame hxi).elim
          have hci := hc_removed i hxi hsame
          change symbolCode (y i - (c : Fin n → 𝔽) i) = symbolCode (y i) ∧
            symbolCode (x i - (c : Fin n → 𝔽) i) = symbolCode (x i)
          simp [hxi, hci]
      · simpa only [tieKey] using hkey_y
    exact hleader_eq_of_max x hxnear hkey_x
  have hupdate_dist_le_one (z : Fin n → 𝔽) (i : Fin n) (a : 𝔽) :
      hammingDist z (Function.update z i a) ≤ 1 := by
    unfold hammingDist
    calc
      (Finset.univ.filter
          (fun j => z j ≠ Function.update z i a j)).card ≤ ({i} : Finset (Fin n)).card := by
        apply Finset.card_le_card
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp only [Finset.mem_singleton]
        by_contra hji
        have hsame : Function.update z i a j = z j := by
          simp [Function.update, hji]
        exact hj hsame.symm
      _ = 1 := by simp
  have hupdate_dist_eq_add_one (z u : Fin n → 𝔽) (i : Fin n) (a : 𝔽)
      (hzu : z i = u i) (hau : a ≠ u i) :
      hammingDist (Function.update z i a) u = hammingDist z u + 1 := by
    simp only [hammingDist, Finset.card_eq_sum_ones]
    repeat rw [Finset.sum_filter]
    rw [← Finset.sum_erase_add Finset.univ
        (fun k => if Function.update z i a k ≠ u k then 1 else 0)
        (Finset.mem_univ i),
      ← Finset.sum_erase_add Finset.univ
        (fun k => if z k ≠ u k then 1 else 0) (Finset.mem_univ i)]
    have hrest :
        ∑ k ∈ Finset.univ.erase i,
            (if Function.update z i a k ≠ u k then 1 else 0) =
          ∑ k ∈ Finset.univ.erase i, (if z k ≠ u k then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hki : k ≠ i := Finset.ne_of_mem_erase hk
      simp [hki]
    rw [hrest]
    simp [hzu, hau]
  have hupdate_dist_add_one_eq (z u : Fin n → 𝔽) (i : Fin n)
      (hzu : z i ≠ u i) :
      hammingDist (Function.update z i (u i)) u + 1 = hammingDist z u := by
    simp only [hammingDist, Finset.card_eq_sum_ones]
    repeat rw [Finset.sum_filter]
    rw [← Finset.sum_erase_add Finset.univ
        (fun k => if Function.update z i (u i) k ≠ u k then 1 else 0)
        (Finset.mem_univ i),
      ← Finset.sum_erase_add Finset.univ
        (fun k => if z k ≠ u k then 1 else 0) (Finset.mem_univ i)]
    have hrest :
        ∑ k ∈ Finset.univ.erase i,
            (if Function.update z i (u i) k ≠ u k then 1 else 0) =
          ∑ k ∈ Finset.univ.erase i, (if z k ≠ u k then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hki : k ≠ i := Finset.ne_of_mem_erase hk
      simp [hki]
    rw [hrest]
    simp [hzu]
  have hsplit_tieKey (u : Fin n → 𝔽) (i : Fin n) :
      tieKey u = (tieKey u).take i.val ++
        symbolCode (u i) :: (tieKey u).drop (i.val + 1) := by
    conv_lhs => rw [← List.take_append_drop i.val (tieKey u)]
    rw [List.drop_eq_getElem_cons]
    · simp [tieKey]
    · simp [tieKey, i.isLt]
  have htake_tieKey_update (u : Fin n → 𝔽) (i : Fin n) (a : 𝔽) :
      (tieKey (Function.update u i a)).take i.val =
        (tieKey u).take i.val := by
    apply List.ext_get
    · simp [tieKey]
    · intro k hk₁ hk₂
      have hklt : k < i.val := by
        simpa [tieKey] using hk₂
      have hkn : k < n := lt_trans hklt i.isLt
      have hki : (⟨k, hkn⟩ : Fin n) ≠ i := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
        omega
      simpa [tieKey, hki]
  have htake_tieKey_update_of_le (u : Fin n → 𝔽) (k i : Fin n)
      (a : 𝔽) (hki : k.val ≤ i.val) :
      (tieKey (Function.update u i a)).take k.val =
        (tieKey u).take k.val := by
    calc
      (tieKey (Function.update u i a)).take k.val =
          ((tieKey (Function.update u i a)).take i.val).take k.val := by
        simp [List.take_take, Nat.min_eq_left hki]
      _ = ((tieKey u).take i.val).take k.val := by
        rw [htake_tieKey_update]
      _ = (tieKey u).take k.val := by
        simp [List.take_take, Nat.min_eq_left hki]
  have htail_le {a : ℕ} {s t : List ℕ} :
      a :: s ≤ a :: t → s ≤ t := by
    intro h
    rcases lt_or_eq_of_le h with hlt | heq
    · have hlex := (List.lt_iff_lex_lt _ _).mp hlt
      rw [List.cons_lex_cons_iff] at hlex
      rcases hlex with hbad | ⟨heq, htail⟩
      · exact (lt_irrefl _ hbad).elim
      · exact le_of_lt htail
    · exact (List.cons.inj heq).2.le
  have htail_lt {a : ℕ} {s t : List ℕ} :
      a :: s < a :: t → s < t := by
    intro h
    have hlex := (List.lt_iff_lex_lt _ _).mp h
    rw [List.cons_lex_cons_iff] at hlex
    rcases hlex with hbad | ⟨heq, htail⟩
    · exact (lt_irrefl _ hbad).elim
    · exact htail
  have hlex_force_at :
      ∀ (p q : List ℕ), p.length = q.length →
        ∀ (a₀ b₀ a₁ b₁ : ℕ) (s₀ t₀ s₁ t₁ : List ℕ),
          a₀ < b₀ →
          p ++ a₁ :: s₁ ≤ q ++ b₁ :: t₁ →
          p ++ a₀ :: s₀ < q ++ b₀ :: t₀ := by
    intro p
    induction p with
    | nil =>
        intro q hlen
        cases q with
        | nil =>
            intro a₀ b₀ a₁ b₁ s₀ t₀ s₁ t₁ hab hmod
            exact List.Lex.rel hab
        | cons qh qt => simp at hlen
    | cons ph pt ih =>
        intro q hlen
        cases q with
        | nil => simp at hlen
        | cons qh qt =>
            simp only [List.length_cons, Nat.succ.injEq] at hlen
            intro a₀ b₀ a₁ b₁ s₀ t₀ s₁ t₁ hab hmod
            simp only [List.cons_append] at hmod ⊢
            rcases lt_trichotomy ph qh with hpq | hpq | hpq
            · exact List.Lex.rel hpq
            · subst qh
              exact List.Lex.cons
                (ih qt hlen a₀ b₀ a₁ b₁ s₀ t₀ s₁ t₁ hab
                  (htail_le hmod))
            · have hcontra :
                  qh :: (qt ++ b₁ :: t₁) < ph :: (pt ++ a₁ :: s₁) :=
                List.Lex.rel hpq
              exact (not_lt_of_ge hmod hcontra).elim
  have hlex_keep_after :
      ∀ (p q : List ℕ), p.length = q.length →
        ∀ (a₀ b₀ : ℕ) (s₀ t₀ s₁ t₁ : List ℕ),
          a₀ < b₀ →
          p ++ a₀ :: s₀ < q ++ b₀ :: t₀ →
          p ++ a₀ :: s₁ < q ++ b₀ :: t₁ := by
    intro p
    induction p with
    | nil =>
        intro q hlen
        cases q with
        | nil =>
            intro a₀ b₀ s₀ t₀ s₁ t₁ hab hbase
            exact List.Lex.rel hab
        | cons qh qt => simp at hlen
    | cons ph pt ih =>
        intro q hlen
        cases q with
        | nil => simp at hlen
        | cons qh qt =>
            simp only [List.length_cons, Nat.succ.injEq] at hlen
            intro a₀ b₀ s₀ t₀ s₁ t₁ hab hbase
            simp only [List.cons_append] at hbase ⊢
            rcases lt_trichotomy ph qh with hpq | hpq | hpq
            · exact List.Lex.rel hpq
            · subst qh
              exact List.Lex.cons
                (ih qt hlen a₀ b₀ s₀ t₀ s₁ t₁ hab
                  (htail_lt hbase))
            · have hcontra :
                  qh :: (qt ++ b₀ :: t₀) < ph :: (pt ++ a₀ :: s₀) :=
                List.Lex.rel hpq
              exact (asymm hbase hcontra).elim
  let f := qary_decoding_region_indicator C Dstar
  have hboundary_bound (z : Fin n → 𝔽)
      (hk : 0 < qary_hamming_boundary f z) :
      linear_code_minimum_distance C ≤ Fintype.card 𝔽 *
        (qary_hamming_boundary f z + 3) := by
    have hfz : f z = 1 := by
      by_contra hfz
      simp [qary_hamming_boundary, hfz] at hk
    let B : Finset (Fin n) := Finset.univ.filter (fun i =>
      z i = 0 ∧ ∃ a : 𝔽, a ≠ 0 ∧ f (Function.update z i a) = 0)
    have hBpos : 0 < B.card := by
      simpa only [qary_hamming_boundary, hfz, if_pos, B] using hk
    obtain ⟨i, hiB⟩ := Finset.card_pos.mp hBpos
    have hi := hiB
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨hzi, a, ha0, hfa⟩ := hi
    let w : Fin n → 𝔽 := Function.update z i a
    let c : C := chosen w
    have hcw : Dstar w c = 1 := by
      rw [show Dstar w c = point (chosen w) c by rfl, hpoint_apply]
      simp [c]
    have hc0 : c ≠ 0 := by
      intro hc
      have hc' : chosen w = 0 := by simpa [c] using hc
      have hlw : leader w = w := (hchosen_zero w).mp hc'
      have hfw : f w = 1 := by
        exact (hregion w).mpr hlw
      exact zero_ne_one (hfa.symm.trans hfw)
    have hzl : leader z = z := (hregion z).mp hfz
    have hzero :
        hammingDist z 0 ≤ hammingDist z (c : Fin n → 𝔽) := by
      have hm := hleader_min z (z - (c : Fin n → 𝔽)) (by simp [errors])
      rw [hweight_sub] at hm
      simpa only [hzl] using hm
    have hwz : hammingDist w z ≤ 1 := by
      rw [hammingDist_comm]
      exact hupdate_dist_le_one z i a
    have hzw : hammingDist z w ≤ 1 := hupdate_dist_le_one z i a
    have hwmin (d : C) :
        hammingDist w (c : Fin n → 𝔽) ≤
          hammingDist w (d : Fin n → 𝔽) :=
      hsym.1 w c (by simpa [hcw]) d
    have hnear (d : C) :
        hammingDist z (c : Fin n → 𝔽) ≤
          hammingDist z (d : Fin n → 𝔽) + 2 := by
      calc
        hammingDist z (c : Fin n → 𝔽) ≤
            hammingDist z w + hammingDist w (c : Fin n → 𝔽) :=
          hammingDist_triangle _ _ _
        _ ≤ 1 + hammingDist w (c : Fin n → 𝔽) :=
          Nat.add_le_add_right hzw _
        _ ≤ 1 + hammingDist w (d : Fin n → 𝔽) :=
          Nat.add_le_add_left (hwmin d) _
        _ ≤ 1 + (hammingDist w z + hammingDist z (d : Fin n → 𝔽)) :=
          Nat.add_le_add_left (hammingDist_triangle _ _ _) _
        _ ≤ hammingDist z (d : Fin n → 𝔽) + 2 := by omega
    let S : Finset (Fin n) := Finset.univ.filter (fun j =>
      (c : Fin n → 𝔽) j ≠ 0 ∧ z j = 0)
    have hdS : linear_code_minimum_distance C ≤
        Fintype.card 𝔽 * (S.card + 2) := by
      simpa only [S] using
        (large_support_outside_error C z c hc0 2 hzero hnear)
    have hScard : S.card ≤ qary_hamming_boundary f z + 1 := by
      rw [qary_hamming_boundary, if_pos hfz]
      change S.card ≤ B.card + 1
      by_cases hS : S = ∅
      · simp [hS]
      have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
      let m : Fin n := S.min' hSne
      have hmS : m ∈ S := Finset.min'_mem S hSne
      have hsub : S.erase m ⊆ B := by
        intro j hj
        have hjS : j ∈ S := (Finset.mem_erase.mp hj).2
        have hjm : j ≠ m := (Finset.mem_erase.mp hj).1
        have hmj : m < j :=
          Finset.min'_lt_of_mem_erase_min' S hSne hj
        have hjS' := hjS
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hjS'
        obtain ⟨hcj, hzj⟩ := hjS'
        let v : Fin n → 𝔽 :=
          Function.update z j ((c : Fin n → 𝔽) j)
        let delta (u₁ u₂ : Fin n → 𝔽) (k : Fin n) : ℕ :=
          if u₁ k ≠ u₂ k then 1 else 0
        have hdist_sum (u₁ u₂ : Fin n → 𝔽) :
            hammingDist u₁ u₂ = ∑ k : Fin n, delta u₁ u₂ k := by
          simp only [hammingDist, Finset.card_eq_sum_ones]
          rw [Finset.sum_filter]
        have hrest0 :
            ∑ k ∈ (Finset.univ.erase j), delta v 0 k =
              ∑ k ∈ (Finset.univ.erase j), delta z 0 k := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkj : k ≠ j := Finset.ne_of_mem_erase hk
          simp [delta, v, hkj]
        have hrestc :
            ∑ k ∈ (Finset.univ.erase j), delta v (c : Fin n → 𝔽) k =
              ∑ k ∈ (Finset.univ.erase j), delta z (c : Fin n → 𝔽) k := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkj : k ≠ j := Finset.ne_of_mem_erase hk
          simp [delta, v, hkj]
        have hv0 : hammingDist v 0 = hammingDist z 0 + 1 := by
          rw [hdist_sum, hdist_sum,
            ← Finset.sum_erase_add Finset.univ (delta v 0) (Finset.mem_univ j),
            ← Finset.sum_erase_add Finset.univ (delta z 0) (Finset.mem_univ j),
            hrest0]
          have hcj' : (0 : 𝔽) ≠ (c : Fin n → 𝔽) j := Ne.symm hcj
          simp [delta, v, hzj, hcj, hcj']
        have hvc : hammingDist v (c : Fin n → 𝔽) + 1 =
            hammingDist z (c : Fin n → 𝔽) := by
          rw [hdist_sum, hdist_sum,
            ← Finset.sum_erase_add Finset.univ
              (delta v (c : Fin n → 𝔽)) (Finset.mem_univ j),
            ← Finset.sum_erase_add Finset.univ
              (delta z (c : Fin n → 𝔽)) (Finset.mem_univ j),
            hrestc]
          have hcj' : (0 : 𝔽) ≠ (c : Fin n → 𝔽) j := Ne.symm hcj
          simp [delta, v, hzj, hcj, hcj']
        have hfv : f v = 0 := by
          by_contra hfv
          have hfv1 : f v = 1 := by
            have hvbool := hdet v 0
            change (Dstar v 0).toReal ≠ 0 at hfv
            rcases hvbool with hvbool | hvbool
            · rw [hvbool] at hfv
              simp at hfv
            · change (Dstar v 0).toReal = 1
              rw [hvbool]
              simp
          have hvl : leader v = v := (hregion v).mp hfv1
          have hvnearest :
              hammingDist v 0 ≤ hammingDist v (c : Fin n → 𝔽) := by
            have hm := hleader_min v (v - (c : Fin n → 𝔽)) (by simp [errors])
            rw [hweight_sub] at hm
            simpa only [hvl] using hm
          by_cases hgap :
              hammingDist z (c : Fin n → 𝔽) < hammingDist z 0 + 2
          · have hzlower :
                hammingDist z 0 + 2 ≤ hammingDist z (c : Fin n → 𝔽) := by
              calc
                hammingDist z 0 + 2 =
                    (hammingDist z 0 + 1) + 1 := by omega
                _ = hammingDist v 0 + 1 := by rw [hv0]
                _ ≤ hammingDist v (c : Fin n → 𝔽) + 1 :=
                  Nat.add_le_add_right hvnearest 1
                _ = hammingDist z (c : Fin n → 𝔽) := hvc
            exact (not_lt_of_ge hzlower hgap).elim
          · have hgap' :
                hammingDist z (c : Fin n → 𝔽) = hammingDist z 0 + 2 := by
              have hzupper := hnear 0
              simpa only [Submodule.coe_zero] using
                Nat.le_antisymm (by simpa using hzupper) (Nat.le_of_not_gt hgap)
            have hvtie :
                hammingDist v 0 = hammingDist v (c : Fin n → 𝔽) := by
              apply Nat.le_antisymm hvnearest
              have heq :
                  hammingDist v (c : Fin n → 𝔽) + 1 =
                    hammingDist v 0 + 1 := by
                calc
                  hammingDist v (c : Fin n → 𝔽) + 1 =
                      hammingDist z (c : Fin n → 𝔽) := hvc
                  _ = hammingDist z 0 + 2 := hgap'
                  _ = (hammingDist z 0 + 1) + 1 := by omega
                  _ = hammingDist v 0 + 1 := by rw [hv0]
              exact (Nat.add_right_cancel heq).le
            have hw0eq : hammingDist w 0 = hammingDist z 0 + 1 := by
              simpa [w] using hupdate_dist_eq_add_one z 0 i a hzi ha0
            have hzc_le :
                hammingDist z (c : Fin n → 𝔽) ≤
                  1 + hammingDist w (c : Fin n → 𝔽) := by
              calc
                hammingDist z (c : Fin n → 𝔽) ≤
                    hammingDist z w + hammingDist w (c : Fin n → 𝔽) :=
                  hammingDist_triangle _ _ _
                _ ≤ 1 + hammingDist w (c : Fin n → 𝔽) :=
                  Nat.add_le_add_right hzw _
            have hwtie :
                hammingDist w 0 = hammingDist w (c : Fin n → 𝔽) := by
              have hwle := hwmin 0
              simp only [Submodule.coe_zero] at hwle
              omega
            have hci : (c : Fin n → 𝔽) i ≠ 0 := by
              intro hci
              have hwc := hupdate_dist_eq_add_one z (c : Fin n → 𝔽) i a
                (by simpa [hzi, hci]) (by simpa [hci] using ha0)
              change hammingDist w (c : Fin n → 𝔽) =
                hammingDist z (c : Fin n → 𝔽) + 1 at hwc
              omega
            have hai : a = (c : Fin n → 𝔽) i := by
              by_contra hai
              have hzci : z i ≠ (c : Fin n → 𝔽) i := by
                intro h
                exact hci (h.symm.trans hzi)
              have hremove := hupdate_dist_add_one_eq z
                (c : Fin n → 𝔽) i hzci
              have hadd := hupdate_dist_eq_add_one
                (Function.update z i ((c : Fin n → 𝔽) i))
                (c : Fin n → 𝔽) i a (by simp) hai
              have hwc_eq :
                  hammingDist w (c : Fin n → 𝔽) =
                    hammingDist z (c : Fin n → 𝔽) := by
                calc
                  hammingDist w (c : Fin n → 𝔽) =
                      hammingDist
                        (Function.update z i ((c : Fin n → 𝔽) i))
                        (c : Fin n → 𝔽) + 1 := by
                    simpa [w] using hadd
                  _ = hammingDist z (c : Fin n → 𝔽) := hremove
              omega
            have hiS : i ∈ S := by
              simp [S, hci, hzi]
            have hmi : m ≤ i := by
              simpa [m] using Finset.min'_le (s := S) i hiS
            have hlw : leader w = w - (c : Fin n → 𝔽) := by
              simpa [c] using (hchosen_error w).symm
            have hwnear : w ∈ nearest w := by
              simp only [nearest, Finset.mem_filter]
              constructor
              · simp [errors]
              · intro u hu
                obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hu
                have hmd := hleader_min w (w - (d : Fin n → 𝔽))
                  (by simp [errors])
                rw [hlw, hweight_sub] at hmd
                exact hwtie.le.trans hmd
            have hkeyw :
                tieKey w ≤ tieKey (w - (c : Fin n → 𝔽)) := by
              simpa only [hlw] using hleader_max w w hwnear
            have hvcompnear : v - (c : Fin n → 𝔽) ∈ nearest v := by
              simp only [nearest, Finset.mem_filter]
              constructor
              · simp [errors]
              · intro u hu
                obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hu
                rw [hweight_sub, ← hvtie]
                simpa only [hvl] using
                  hleader_min v (v - (d : Fin n → 𝔽)) (by simp [errors])
            have hkeyv :
                tieKey (v - (c : Fin n → 𝔽)) ≤ tieKey v := by
              simpa only [hvl] using
                hleader_max v (v - (c : Fin n → 𝔽)) hvcompnear
            have hmS' := hmS
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hmS'
            obtain ⟨hcm, hzm⟩ := hmS'
            have hvprefix :
                (tieKey v).take m.val = (tieKey w).take m.val := by
              calc
                (tieKey v).take m.val = (tieKey z).take m.val := by
                  simpa [v] using htake_tieKey_update_of_le z m j
                    ((c : Fin n → 𝔽) j) (le_of_lt hmj)
                _ = (tieKey w).take m.val := by
                  symm
                  simpa [w] using htake_tieKey_update_of_le z m i a hmi
            have hvsub :
                v - (c : Fin n → 𝔽) =
                  Function.update (z - (c : Fin n → 𝔽)) j 0 := by
              funext k
              by_cases hkj : k = j
              · subst k
                simp [v]
              · simp [v, hkj]
            have hwsub :
                w - (c : Fin n → 𝔽) =
                  Function.update (z - (c : Fin n → 𝔽)) i
                    (a - (c : Fin n → 𝔽) i) := by
              funext k
              by_cases hki : k = i
              · subst k
                simp [w]
              · simp [w, hki]
            have hvsubprefix :
                (tieKey (v - (c : Fin n → 𝔽))).take m.val =
                  (tieKey (w - (c : Fin n → 𝔽))).take m.val := by
              rw [hvsub, hwsub]
              calc
                (tieKey (Function.update (z - (c : Fin n → 𝔽)) j 0)).take m.val =
                    (tieKey (z - (c : Fin n → 𝔽))).take m.val := by
                  exact htake_tieKey_update_of_le _ m j 0 (le_of_lt hmj)
                _ = (tieKey (Function.update (z - (c : Fin n → 𝔽)) i
                    (a - (c : Fin n → 𝔽) i))).take m.val := by
                  symm
                  exact htake_tieKey_update_of_le _ m i _ hmi
            have hmj_ne : m ≠ j := ne_of_lt hmj
            have hvm : v m = 0 := by
              simp [v, hmj_ne, hzm]
            have hvc_m :
                (v - (c : Fin n → 𝔽)) m = -(c : Fin n → 𝔽) m := by
              change v m - (c : Fin n → 𝔽) m = -(c : Fin n → 𝔽) m
              rw [hvm, zero_sub]
            have hnegcm : -(c : Fin n → 𝔽) m ≠ 0 := neg_ne_zero.mpr hcm
            have hcode :
                symbolCode (v m) <
                  symbolCode ((v - (c : Fin n → 𝔽)) m) := by
              simp [hvm, hvc_m, symbolCode, hnegcm]
            have hkeyw' := hkeyw
            rw [hsplit_tieKey w m,
              hsplit_tieKey (w - (c : Fin n → 𝔽)) m] at hkeyw'
            have hpref_len :
                ((tieKey w).take m.val).length =
                  ((tieKey (w - (c : Fin n → 𝔽))).take m.val).length := by
              simp [tieKey]
            have hstrict :
                tieKey v < tieKey (v - (c : Fin n → 𝔽)) := by
              rw [hsplit_tieKey v m,
                hsplit_tieKey (v - (c : Fin n → 𝔽)) m,
                hvprefix, hvsubprefix]
              exact hlex_force_at _ _ hpref_len _ _ _ _ _ _ _ _ hcode hkeyw'
            exact (not_lt_of_ge hkeyv hstrict).elim
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hzj, (c : Fin n → 𝔽) j, hcj, by simpa [v] using hfv⟩
      calc
        S.card = (S.erase m).card + 1 := by
          rw [Finset.card_erase_of_mem hmS]
          exact (Nat.sub_add_cancel (Finset.one_le_card.mpr hSne)).symm
        _ ≤ B.card + 1 := Nat.add_le_add_right (Finset.card_le_card hsub) 1
    apply hdS.trans
    apply Nat.mul_le_mul_left
    simpa [Nat.add_assoc] using Nat.add_le_add_right hScard 2
  refine ⟨Dstar, ?_, hbase⟩
  refine ⟨hsym, hdet, hdown, ?_⟩
  by_cases hd0 : linear_code_minimum_distance C = 0
  · rw [hd0]
    have hnonneg :
        0 ≤ (minimum_positive_boundary f : ℝ) := by positivity
    norm_num
    linarith
  · have hweights :
        ({d : ℕ | ∃ c : C, c ≠ 0 ∧
          d = hammingDist (c : Fin n → 𝔽) 0} : Set ℕ).Nonempty := by
      by_contra hempty
      have heq :
          ({d : ℕ | ∃ c : C, c ≠ 0 ∧
            d = hammingDist (c : Fin n → 𝔽) 0} : Set ℕ) = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hempty
      apply hd0
      unfold linear_code_minimum_distance
      rw [heq, Nat.sInf_empty]
    obtain ⟨d, c, hc0, hdc⟩ := hweights
    have hleader_zero : leader 0 = 0 := by
      have hm := hleader_min 0 0 (by
        simp only [errors, Finset.mem_image, Finset.mem_univ, true_and]
        refine ⟨0, ?_⟩
        simp)
      apply eq_of_hammingDist_eq_zero
      exact Nat.eq_zero_of_le_zero (by simpa using hm)
    have hfzero : f 0 = 1 := (hregion 0).mpr hleader_zero
    have hleader_c : leader (c : Fin n → 𝔽) = 0 := by
      have hm := hleader_min (c : Fin n → 𝔽) 0 (by
        simp only [errors, Finset.mem_image, Finset.mem_univ, true_and]
        refine ⟨c, ?_⟩
        exact sub_self (c : Fin n → 𝔽))
      apply eq_of_hammingDist_eq_zero
      exact Nat.eq_zero_of_le_zero (by simpa using hm)
    have hf_zero_or_one (u : Fin n → 𝔽) : f u = 0 ∨ f u = 1 := by
      rcases hdet u 0 with hu | hu
      · left
        change (Dstar u 0).toReal = 0
        rw [hu]
        simp
      · right
        change (Dstar u 0).toReal = 1
        rw [hu]
        simp
    have hfc_ne : f (c : Fin n → 𝔽) ≠ 1 := by
      intro hfc
      have hlc := (hregion (c : Fin n → 𝔽)).mp hfc
      rw [hleader_c] at hlc
      apply hc0
      apply Subtype.ext
      exact hlc.symm
    have hfc : f (c : Fin n → 𝔽) = 0 :=
      (hf_zero_or_one (c : Fin n → 𝔽)).resolve_right hfc_ne
    let outside : Finset (Fin n → 𝔽) :=
      Finset.univ.filter (fun u => f u = 0)
    have houtside : outside.Nonempty := by
      refine ⟨(c : Fin n → 𝔽), ?_⟩
      simp [outside, hfc]
    obtain ⟨y, hyout, hymin⟩ := Finset.exists_min_image outside
      (fun u => hammingDist u 0) houtside
    have hfy : f y = 0 := by
      simpa [outside] using hyout
    have hyne : y ≠ 0 := by
      intro hy
      subst y
      exact one_ne_zero (hfzero.symm.trans hfy)
    have hycoord : ∃ i : Fin n, y i ≠ 0 := by
      by_contra h
      push Not at h
      apply hyne
      funext i
      exact h i
    obtain ⟨i, hyi⟩ := hycoord
    let z : Fin n → 𝔽 := Function.update y i 0
    have hzweight : hammingDist z 0 + 1 = hammingDist y 0 := by
      simpa [z] using hupdate_dist_add_one_eq y 0 i hyi
    have hfz_one : f z = 1 := by
      rcases hf_zero_or_one z with hfz | hfz
      · have hzout : z ∈ outside := by
          simp [outside, hfz]
        have hmin := hymin z hzout
        omega
      · exact hfz
    have hzcoord : z i = 0 := by simp [z]
    have hrecover : Function.update z i (y i) = y := by
      funext k
      by_cases hki : k = i
      · subst k
        simp [z]
      · simp [z, hki]
    have hbpos : 0 < qary_hamming_boundary f z := by
      rw [qary_hamming_boundary, if_pos hfz_one]
      apply Finset.card_pos.mpr
      refine ⟨i, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hzcoord, y i, hyi, by rw [hrecover]; exact hfy⟩
    have hpositive_nonempty :
        ({k : ℕ | 0 < k ∧ ∃ u : Fin n → 𝔽,
          qary_hamming_boundary f u = k} : Set ℕ).Nonempty := by
      exact ⟨qary_hamming_boundary f z, hbpos, z, rfl⟩
    have hminmem := Nat.sInf_mem hpositive_nonempty
    change 0 < minimum_positive_boundary f ∧
      ∃ u : Fin n → 𝔽,
        qary_hamming_boundary f u = minimum_positive_boundary f at hminmem
    obtain ⟨hminpos, u, hu⟩ := hminmem
    have hbound := hboundary_bound u (by simpa [hu] using hminpos)
    rw [hu] at hbound
    have hbound_real :
        (linear_code_minimum_distance C : ℝ) ≤
          (Fintype.card 𝔽 : ℝ) *
            ((minimum_positive_boundary f : ℝ) + 3) := by
      exact_mod_cast hbound
    have hqpos : 0 < (Fintype.card 𝔽 : ℝ) := by positivity
    apply (sub_le_iff_le_add).2
    apply (div_le_iff₀ hqpos).2
    nlinarith

@[blueprint "lem:qary-russo-formula"
  (statement := /-- Let $\mathbb F$ be a finite field of cardinality $q$, let $n\in\mathbb N$, and let $f\colon\mathbb F^n\to\mathbb R$ be a function such that $f(z)\in\{0,1\}$ for every $z\in\mathbb F^n$ and such that $f$ is downward monotone in the sense of \cref{def:qary-downward-monotone}.  For every $p\in\mathbb R$ with $0\leq p<1$,
  \[
    \frac{d}{dp}\mathbb E_p[f]
      \leq-\frac{1}{q-1}\mathbb E_p[h_f].
  \]
  Here $\mathbb E_p$ is the biased expectation of \cref{def:qary-noise-expectation}, and $h_f$ is the outgoing Hamming-boundary count of \cref{def:qary-hamming-boundary}. -/)
  (proof := /-- Unfold the finite sum in \cref{def:qary-noise-expectation}.  The product and sum rules give its derivative as the sum over coordinates $i$ and words $z$ of the product of all coordinate weights except the $i$th, multiplied by $-f(z)$ when $z_i=0$ and by $f(z)/(q-1)$ when $z_i\ne0$.  For each fixed $i$, split a word into its $i$th symbol $a\in\mathbb F$ and the remaining coordinates, and denote the product of the remaining coordinate weights by $W\geq0$.

  Let $z$ be the word in this fibre whose $i$th coordinate is zero.  If $f(z)=0$, downward monotonicity from \cref{def:qary-downward-monotone}, together with the fact that $f$ is Boolean-valued, forces $f(z^{i\leftarrow a})=0$ for every $a$, so this fibre contributes zero.  Suppose that $f(z)=1$.  If no nonzero replacement makes $f$ vanish, every replacement has value one and the fibre derivative is
  \[
    W\left(-1+\frac{q-1}{q-1}\right)=0.
  \]
  Otherwise choose a nonzero $a_0$ for which $f(z^{i\leftarrow a_0})=0$.  All other nonzero replacements have value at most one, so their sum is at most $q-2$ and the fibre derivative is at most
  \[
    W\left(-1+\frac{q-2}{q-1}\right)=-\frac{W}{q-1}.
  \]
  In precisely this last case, the contribution of coordinate $i$ to the boundary expectation in \cref{def:qary-hamming-boundary} is $(1-p)W$.  Since $0\leq1-p\leq1$, one has
  \[
    -\frac{W}{q-1}\leq-\frac{(1-p)W}{q-1}.
  \]
  Summing this fibrewise estimate over the remaining coordinates and then over $i$ proves the inequality. -/)
  (title := /-- Russo's inequality for the q-ary biased product law -/)
  (latexEnv := "lemma")]
lemma qary_russo_formula
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (f : (Fin n → 𝔽) → ℝ)
    (hf01 : ∀ z, f z = 0 ∨ f z = 1)
    (hfmono : qary_downward_monotone f) {p : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p < 1) :
    deriv (fun r => qary_noise_expectation r f) p ≤
      -(1 / ((Fintype.card 𝔽 : ℝ) - 1)) *
        qary_noise_expectation p
          (fun z => (qary_hamming_boundary f z : ℝ)) := by
  classical
  have hfactor (z : Fin n → 𝔽) (i : Fin n) :
      HasDerivAt
        (fun r : ℝ => if z i = 0 then 1 - r
          else r / ((Fintype.card 𝔽 : ℝ) - 1))
        (if z i = 0 then -1 else 1 / ((Fintype.card 𝔽 : ℝ) - 1)) p := by
    by_cases hzi : z i = 0
    · simpa [hzi, id_eq] using (hasDerivAt_id (x := p)).const_sub 1
    · simpa [hzi, id_eq] using
        (hasDerivAt_id (x := p)).div_const ((Fintype.card 𝔽 : ℝ) - 1)
  have hterm (z : Fin n → 𝔽) :
      HasDerivAt
        (fun r : ℝ =>
          (∏ i : Fin n, if z i = 0 then 1 - r
            else r / ((Fintype.card 𝔽 : ℝ) - 1)) * f z)
        ((∑ i : Fin n,
          (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
            if z j = 0 then 1 - p
            else p / ((Fintype.card 𝔽 : ℝ) - 1)) *
              (if z i = 0 then -1
                else 1 / ((Fintype.card 𝔽 : ℝ) - 1))) * f z) p := by
    simpa only [smul_eq_mul] using
      (HasDerivAt.fun_finsetProd
        (u := (Finset.univ : Finset (Fin n)))
        (f := fun i r => if z i = 0 then 1 - r
          else r / ((Fintype.card 𝔽 : ℝ) - 1))
        (f' := fun i => if z i = 0 then -1
          else 1 / ((Fintype.card 𝔽 : ℝ) - 1))
        (fun i _ => hfactor z i)).mul_const (f z)
  have hsum : HasDerivAt (fun r => qary_noise_expectation r f)
      (∑ z : Fin n → 𝔽,
        ((∑ i : Fin n,
          (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
            if z j = 0 then 1 - p
            else p / ((Fintype.card 𝔽 : ℝ) - 1)) *
              (if z i = 0 then -1
                else 1 / ((Fintype.card 𝔽 : ℝ) - 1))) * f z)) p := by
    unfold qary_noise_expectation
    exact HasDerivAt.fun_sum fun z _ => hterm z
  rw [hsum.deriv]
  have hboundary (z : Fin n → 𝔽) :
      (qary_hamming_boundary f z : ℝ) =
        ∑ i : Fin n, if f z = 1 ∧ z i = 0 ∧
          ∃ a : 𝔽, a ≠ 0 ∧ f (Function.update z i a) = 0 then 1 else 0 := by
    by_cases hfz : f z = 1
    · simp only [qary_hamming_boundary, hfz, if_pos, true_and,
        Finset.sum_boole]
    · simp [qary_hamming_boundary, hfz]
  unfold qary_noise_expectation
  simp_rw [hboundary]
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_le_sum ?_
  intro i hi
  let L : (Fin n → 𝔽) → ℝ := fun x =>
    (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
      if x j = 0 then 1 - p
      else p / ((Fintype.card 𝔽 : ℝ) - 1)) *
        ((if x i = 0 then -1
          else 1 / ((Fintype.card 𝔽 : ℝ) - 1)) * f x)
  let R : (Fin n → 𝔽) → ℝ := fun x =>
    -(1 / ((Fintype.card 𝔽 : ℝ) - 1)) *
      ((∏ j : Fin n, if x j = 0 then 1 - p
        else p / ((Fintype.card 𝔽 : ℝ) - 1)) *
        if f x = 1 ∧ x i = 0 ∧
          ∃ a : 𝔽, a ≠ 0 ∧ f (Function.update x i a) = 0 then 1 else 0)
  change (∑ x, L x) ≤ ∑ x, R x
  have hL : (∑ x, L x) =
      ∑ x : 𝔽 × ({j : Fin n // j ≠ i} → 𝔽),
        L ((Equiv.funSplitAt i 𝔽).symm x) :=
    Fintype.sum_equiv (Equiv.funSplitAt i 𝔽) L
      (fun x => L ((Equiv.funSplitAt i 𝔽).symm x))
      (fun x => (congrArg L ((Equiv.funSplitAt i 𝔽).symm_apply_apply x)).symm)
  have hR : (∑ x, R x) =
      ∑ x : 𝔽 × ({j : Fin n // j ≠ i} → 𝔽),
        R ((Equiv.funSplitAt i 𝔽).symm x) :=
    Fintype.sum_equiv (Equiv.funSplitAt i 𝔽) R
      (fun x => R ((Equiv.funSplitAt i 𝔽).symm x))
      (fun x => (congrArg R ((Equiv.funSplitAt i 𝔽).symm_apply_apply x)).symm)
  rw [hL, hR, Fintype.sum_prod_type_right, Fintype.sum_prod_type_right]
  refine Finset.sum_le_sum ?_
  intro y hy
  let z : Fin n → 𝔽 := (Equiv.funSplitAt i 𝔽).symm (0, y)
  have hzi : z i = 0 := by
    simp [z, Equiv.funSplitAt, Equiv.piSplitAt]
  have hsplit (a : 𝔽) :
      (Equiv.funSplitAt i 𝔽).symm (a, y) = Function.update z i a := by
    ext j
    by_cases hji : j = i <;>
      simp [z, Equiv.funSplitAt, Equiv.piSplitAt, hji]
  simp_rw [hsplit]
  let W : ℝ :=
    ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
      if z j = 0 then 1 - p
      else p / ((Fintype.card 𝔽 : ℝ) - 1)
  have hWupdate (a : 𝔽) :
      (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        if (Function.update z i a) j = 0 then 1 - p
        else p / ((Fintype.card 𝔽 : ℝ) - 1)) = W := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [W, Function.update, hji]
  have hupdate_zero : Function.update z i (0 : 𝔽) = z := by
    ext j
    by_cases hji : j = i <;> simp [Function.update, hji, hzi]
  have hLupdate (a : 𝔽) :
      L (Function.update z i a) = W *
        ((if a = 0 then -1
          else 1 / ((Fintype.card 𝔽 : ℝ) - 1)) *
          f (Function.update z i a)) := by
    unfold L
    rw [hWupdate]
    simp [Function.update]
  rcases hf01 z with hfz | hfz
  · have hzero (a : 𝔽) : f (Function.update z i a) = 0 := by
      rcases hf01 (Function.update z i a) with hzero | hone
      · exact hzero
      · have hrel : ∀ j : Fin n,
            z j = 0 ∨ z j = (Function.update z i a) j := by
          intro j
          by_cases hji : j = i
          · left
            simpa [hji] using hzi
          · right
            simp [Function.update, hji]
        have := hfmono hrel hone
        rw [hfz] at this
        norm_num at this
    simp [L, R, hzero, hzi]
  · have hc : (1 : ℝ) < (Fintype.card 𝔽 : ℝ) := by
      exact_mod_cast (Fintype.one_lt_card (α := 𝔽))
    have hQpos : 0 < (Fintype.card 𝔽 : ℝ) - 1 := sub_pos.mpr hc
    have hQne : (Fintype.card 𝔽 : ℝ) - 1 ≠ 0 := ne_of_gt hQpos
    by_cases hb : ∃ a : 𝔽,
      a ≠ 0 ∧ f (Function.update z i a) = 0
    · rcases hb with ⟨a₀, ha₀, hfa₀⟩
      have ha₀mem : a₀ ∈ (Finset.univ : Finset 𝔽).erase 0 := by
        simp [ha₀]
      have hvalue_le (a : 𝔽) : f (Function.update z i a) ≤ 1 := by
        rcases hf01 (Function.update z i a) with hzero | hone
        · linarith
        · linarith
      have hsum_le :
          (∑ a ∈ (Finset.univ : Finset 𝔽).erase 0,
            f (Function.update z i a)) ≤
          (((Finset.univ : Finset 𝔽).erase 0).erase a₀).card := by
        calc
          (∑ a ∈ (Finset.univ : Finset 𝔽).erase 0,
              f (Function.update z i a)) =
              (∑ a ∈ ((Finset.univ : Finset 𝔽).erase 0).erase a₀,
                f (Function.update z i a)) + f (Function.update z i a₀) := by
                symm
                exact Finset.sum_erase_add _ _ ha₀mem
          _ = ∑ a ∈ ((Finset.univ : Finset 𝔽).erase 0).erase a₀,
                f (Function.update z i a) := by rw [hfa₀, add_zero]
          _ ≤ ∑ _a ∈ ((Finset.univ : Finset 𝔽).erase 0).erase a₀,
                (1 : ℝ) := Finset.sum_le_sum fun a _ => hvalue_le a
          _ = (((Finset.univ : Finset 𝔽).erase 0).erase a₀).card := by
                simp
      have hcardNat :
          (((Finset.univ : Finset 𝔽).erase 0).erase a₀).card + 2 =
            Fintype.card 𝔽 := by
        rw [Finset.card_erase_of_mem ha₀mem]
        simp
        have hcardtwo : 2 ≤ Fintype.card 𝔽 :=
          Fintype.one_lt_card (α := 𝔽)
        omega
      have hcardReal :
          ((((Finset.univ : Finset 𝔽).erase 0).erase a₀).card : ℝ) + 1 =
            (Fintype.card 𝔽 : ℝ) - 1 := by
        have hcast :
            ((((Finset.univ : Finset 𝔽).erase 0).erase a₀).card : ℝ) + 2 =
              (Fintype.card 𝔽 : ℝ) := by exact_mod_cast hcardNat
        linarith
      have hWnonneg : 0 ≤ W := by
        unfold W
        apply Finset.prod_nonneg
        intro j hj
        split_ifs
        · linarith
        · positivity
      have hLform :
          (∑ a : 𝔽, L (Function.update z i a)) =
            W * (-1 + (1 / ((Fintype.card 𝔽 : ℝ) - 1)) *
              ∑ a ∈ (Finset.univ : Finset 𝔽).erase 0,
                f (Function.update z i a)) := by
        calc
          (∑ a : 𝔽, L (Function.update z i a)) =
              L (Function.update z i 0) +
                ∑ a ∈ (Finset.univ : Finset 𝔽).erase 0,
                  L (Function.update z i a) := by
                    symm
                    exact Finset.add_sum_erase (Finset.univ : Finset 𝔽)
                      (fun a : 𝔽 => L (Function.update z i a))
                      (Finset.mem_univ (0 : 𝔽))
          _ = -W + ∑ a ∈ (Finset.univ : Finset 𝔽).erase 0,
                W * (1 / ((Fintype.card 𝔽 : ℝ) - 1) *
                  f (Function.update z i a)) := by
                congr 1
                · rw [hLupdate]
                  simp [hupdate_zero, hfz]
                · apply Finset.sum_congr rfl
                  intro a ha
                  rw [hLupdate]
                  have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
                  simp [ha0]
          _ = W * (-1 + (1 / ((Fintype.card 𝔽 : ℝ) - 1)) *
                ∑ a ∈ (Finset.univ : Finset 𝔽).erase 0,
                  f (Function.update z i a)) := by
                rw [← Finset.mul_sum, ← Finset.mul_sum]
                ring
      have hfullz :
          (∏ j : Fin n, if z j = 0 then 1 - p
            else p / ((Fintype.card 𝔽 : ℝ) - 1)) = (1 - p) * W := by
        rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
          (fun j => if z j = 0 then 1 - p
            else p / ((Fintype.card 𝔽 : ℝ) - 1)) (Finset.mem_univ i)]
        simp [hzi, W]
      have hRnonzero (a : 𝔽) (ha : a ≠ 0) :
          R (Function.update z i a) = 0 := by
        simp [R, Function.update, ha]
      have hRsum :
          (∑ a : 𝔽, R (Function.update z i a)) =
            -(1 / ((Fintype.card 𝔽 : ℝ) - 1)) * ((1 - p) * W) := by
        have hbz : ∃ a : 𝔽,
            a ≠ 0 ∧ f (Function.update z i a) = 0 := ⟨a₀, ha₀, hfa₀⟩
        rw [Finset.sum_eq_single 0]
        · rw [hupdate_zero]
          unfold R
          rw [hfullz]
          simp [hfz, hzi, hbz]
        · intro a ha_mem ha
          exact hRnonzero a ha
        · simp
      rw [hLform, hRsum]
      have hp_le : 1 - p ≤ 1 := by linarith
      have hsum_le' :
          (∑ a ∈ (Finset.univ : Finset 𝔽).erase 0,
            f (Function.update z i a)) ≤
            (Fintype.card 𝔽 : ℝ) - 2 := by
        linarith
      have hQinv : 0 < 1 / ((Fintype.card 𝔽 : ℝ) - 1) := by positivity
      have hQmul :
          (1 / ((Fintype.card 𝔽 : ℝ) - 1)) *
            ((Fintype.card 𝔽 : ℝ) - 1) = 1 := by
        field_simp
      have hscaled := mul_le_mul_of_nonneg_left hsum_le' (le_of_lt hQinv)
      have hbracket :
          -1 + (1 / ((Fintype.card 𝔽 : ℝ) - 1)) *
              (∑ a ∈ (Finset.univ : Finset 𝔽).erase 0,
                f (Function.update z i a)) ≤
            -(1 / ((Fintype.card 𝔽 : ℝ) - 1)) := by
        nlinarith
      have hLbound := mul_le_mul_of_nonneg_left hbracket hWnonneg
      have hnoiseBase : (1 - p) * W ≤ W := by
        nlinarith
      have hnoise := mul_le_mul_of_nonpos_left hnoiseBase (by
        have := hQinv
        linarith : -(1 / ((Fintype.card 𝔽 : ℝ) - 1)) ≤ 0)
      calc
        W * (-1 + (1 / ((Fintype.card 𝔽 : ℝ) - 1)) *
            ∑ a ∈ (Finset.univ : Finset 𝔽).erase 0,
              f (Function.update z i a)) ≤
            W * (-(1 / ((Fintype.card 𝔽 : ℝ) - 1))) := hLbound
        _ = -(1 / ((Fintype.card 𝔽 : ℝ) - 1)) * W := by ring
        _ ≤ -(1 / ((Fintype.card 𝔽 : ℝ) - 1)) * ((1 - p) * W) := hnoise
    · have hone (a : 𝔽) : f (Function.update z i a) = 1 := by
        by_cases ha : a = 0
        · subst a
          simpa [hupdate_zero] using hfz
        · rcases hf01 (Function.update z i a) with hzero | hone
          · exact False.elim (hb ⟨a, ha, hzero⟩)
          · exact hone
      have hRzero (a : 𝔽) : R (Function.update z i a) = 0 := by
        by_cases ha : a = 0
        · subst a
          rw [hupdate_zero]
          simp [R, hfz, hzi, hb]
        · simp [R, Function.update, ha]
      rw [show (∑ a : 𝔽, L (Function.update z i a)) = 0 by
        simp_rw [hLupdate, hone, mul_one]
        rw [← Finset.mul_sum]
        suffices (∑ a : 𝔽, if a = 0 then (-1 : ℝ)
            else 1 / ((Fintype.card 𝔽 : ℝ) - 1)) = 0 by
          rw [this, mul_zero]
        simp [Finset.sum_ite, hQne]
        field_simp
        have heqcard :
            ((Finset.univ : Finset 𝔽).filter fun x => x = 0).card = 1 := by
          rw [show ((Finset.univ : Finset 𝔽).filter fun x => x = 0) = {0} by
            ext x
            simp]
          simp
        have hnecard :
            ((Finset.univ : Finset 𝔽).filter fun x => ¬x = 0).card =
              Fintype.card 𝔽 - 1 := by
          rw [show ((Finset.univ : Finset 𝔽).filter fun x => ¬x = 0) =
              Finset.univ.erase 0 by ext x; simp]
          simp
        rw [heqcard, hnecard,
          Nat.cast_sub (Nat.le_of_lt (Fintype.one_lt_card (α := 𝔽)))]
        ring]
      simp [hRzero]

@[blueprint "lem:qary-noise-expectation-one"
  (statement := /-- Let $\mathbb F$ be a finite field, let $n\in\mathbb N$, and let $0\leq p\leq1$.  The expectation of the constant function $1$ under the $q$-ary biased product law is equal to $1$. -/)
  (proof := /-- Expand the finite product in \cref{def:qary-noise-expectation} one coordinate at a time.  The coordinate weights consist of the mass $1-p$ at zero and equal masses $p/(|\mathbb F|-1)$ at the $|\mathbb F|-1$ nonzero field elements, and therefore sum to $1$.  Induction on the number of coordinates now shows that the full product weights sum to $1$. -/)
  (title := /-- Normalization of the q-ary product law -/)
  (latexEnv := "lemma")]
lemma qary_noise_expectation_one
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    qary_noise_expectation p (fun _ : Fin n → 𝔽 => 1) = 1 := by
  classical
  induction n with
  | zero =>
      simp [qary_noise_expectation]
  | succ n ih =>
      have hc : (1 : ℕ) < Fintype.card 𝔽 := Fintype.one_lt_card
      have hcr : (1 : ℝ) < Fintype.card 𝔽 := by
        exact_mod_cast hc
      have hd : (Fintype.card 𝔽 : ℝ) - 1 ≠ 0 :=
        ne_of_gt (sub_pos.mpr hcr)
      have hz : Fintype.card {a : 𝔽 // a = 0} = 1 :=
        Fintype.card_subtype_eq 0
      have hnz : Fintype.card {a : 𝔽 // a ≠ 0} = Fintype.card 𝔽 - 1 :=
        Fintype.card_subtype_compl (fun a : 𝔽 => a = 0)
      have hcoord :
          (∑ a : 𝔽, if a = 0 then 1 - p
            else p / ((Fintype.card 𝔽 : ℝ) - 1)) = 1 := by
        simp [Finset.sum_ite, ← Fintype.card_subtype, hz, hnz, hd]
        rw [Nat.cast_sub (le_of_lt hc)]
        field_simp
        ring
      calc
        qary_noise_expectation p (fun _ : Fin (n + 1) → 𝔽 => 1) =
            ∑ a : 𝔽, (if a = 0 then 1 - p
              else p / ((Fintype.card 𝔽 : ℝ) - 1)) *
                qary_noise_expectation p (fun _ : Fin n → 𝔽 => 1) := by
          simp [qary_noise_expectation,
            ← (Fin.consEquiv (fun _ => 𝔽)).sum_comp, Fin.prod_univ_succ,
            Finset.mul_sum, mul_assoc, Fintype.sum_prod_type, Fin.consEquiv]
        _ = ∑ a : 𝔽, if a = 0 then 1 - p
              else p / ((Fintype.card 𝔽 : ℝ) - 1) := by
          simp [ih]
        _ = 1 := hcoord

@[blueprint "lem:qary-noise-expectation-boolean-bounds"
  (statement := /-- Let $\mathbb F$ be a finite field, let $f\colon\mathbb F^n\to\{0,1\}$, and let $0\leq p\leq1$.  Then $0\leq\mathbb E_p[f]\leq1$. -/)
  (proof := /-- Every coordinate factor in \cref{def:qary-noise-expectation} is nonnegative, so every product weight is nonnegative.  Booleanity gives $0\leq f\leq1$ pointwise.  Summing the lower pointwise inequality proves nonnegativity, while summing the upper one and applying \cref{lem:qary-noise-expectation-one} proves that the expectation is at most $1$. -/)
  (title := /-- Bounds for Boolean q-ary expectations -/)
  (latexEnv := "lemma")]
lemma qary_noise_expectation_boolean_bounds
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (f : (Fin n → 𝔽) → ℝ)
    (hf01 : ∀ z, f z = 0 ∨ f z = 1) {p : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    0 ≤ qary_noise_expectation p f ∧ qary_noise_expectation p f ≤ 1 := by
  classical
  have hc : (1 : ℕ) < Fintype.card 𝔽 := Fintype.one_lt_card
  have hcr : (1 : ℝ) < Fintype.card 𝔽 := by
    exact_mod_cast hc
  have hw (z : Fin n → 𝔽) :
      0 ≤ ∏ i : Fin n, if z i = 0 then 1 - p
        else p / ((Fintype.card 𝔽 : ℝ) - 1) := by
    positivity
  have hf₀ (z : Fin n → 𝔽) : 0 ≤ f z := by
    rcases hf01 z with h | h <;> simp [h]
  have hf₁ (z : Fin n → 𝔽) : f z ≤ 1 := by
    rcases hf01 z with h | h <;> simp [h]
  constructor
  · simp only [qary_noise_expectation]
    exact Finset.sum_nonneg (fun z _ => mul_nonneg (hw z) (hf₀ z))
  · rw [← qary_noise_expectation_one (𝔽 := 𝔽) (n := n) hp₀ hp₁]
    simp only [qary_noise_expectation]
    exact Finset.sum_le_sum (fun z _ =>
      mul_le_mul_of_nonneg_left (hf₁ z) (hw z))

@[blueprint "lem:qary-noise-expectation-linear"
  (statement := /-- The $q$-ary finite-product expectation is linear: for functions $g,h$ and scalars $r,s$,
  \[
    \mathbb E_p[rg+sh]=r\mathbb E_p[g]+s\mathbb E_p[h].
  \] -/)
  (proof := /-- Expand \cref{def:qary-noise-expectation}, distribute each product weight across the pointwise linear combination, split the finite sum, and factor out the two scalar coefficients. -/)
  (title := /-- Linearity of q-ary expectation -/)
  (latexEnv := "lemma")]
lemma qary_noise_expectation_linear
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (p r s : ℝ) (g h : (Fin n → 𝔽) → ℝ) :
    qary_noise_expectation p (fun z => r * g z + s * h z) =
      r * qary_noise_expectation p g + s * qary_noise_expectation p h := by
  simp only [qary_noise_expectation]
  simp_rw [mul_add, ← mul_assoc]
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro z hz
    ring
  · apply Finset.sum_congr rfl
    intro z hz
    ring

@[blueprint "lem:qary-hamming-boundary-slice-le"
  (statement := /-- Fixing the first coordinate of a function on $\mathbb F^{n+1}$ cannot increase its outgoing Hamming boundary: for every $a\in\mathbb F$ and $z\in\mathbb F^n$, the boundary of the $a$-slice at $z$ is at most the boundary of the original function at $(a,z)$. -/)
  (proof := /-- Unfold \cref{def:qary-hamming-boundary}.  Every boundary coordinate $i$ of the slice maps injectively to the successor coordinate $i+1$ of the original vector.  The corresponding coordinate values and one-coordinate updates agree under this embedding, so the induced map sends the filtered slice-boundary set into the full boundary set.  Taking cardinalities proves the inequality. -/)
  (title := /-- Slice boundaries embed in the full boundary -/)
  (latexEnv := "lemma")]
lemma qary_hamming_boundary_slice_le
    {𝔽 : Type*} [Zero 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (f : (Fin (n + 1) → 𝔽) → ℝ) (a : 𝔽)
    (z : Fin n → 𝔽) :
    qary_hamming_boundary (fun x => f (Fin.cons a x)) z ≤
      qary_hamming_boundary f (Fin.cons a z) := by
  classical
  by_cases hf : f (Fin.cons a z) = 1
  · simp only [qary_hamming_boundary, hf, if_true]
    let e : Fin n ↪ Fin (n + 1) :=
      ⟨fun i => i.succ, Fin.succ_injective n⟩
    calc
      (Finset.univ.filter (fun i : Fin n =>
          z i = 0 ∧ ∃ b : 𝔽, b ≠ 0 ∧
            f (Fin.cons a (Function.update z i b)) = 0)).card =
          ((Finset.univ.filter (fun i : Fin n =>
            z i = 0 ∧ ∃ b : 𝔽, b ≠ 0 ∧
              f (Fin.cons a (Function.update z i b)) = 0)).map e).card := by
        simp
      _ ≤ (Finset.univ.filter (fun i : Fin (n + 1) =>
          (Fin.cons a z : Fin (n + 1) → 𝔽) i = 0 ∧ ∃ b : 𝔽, b ≠ 0 ∧
            f (Function.update (Fin.cons a z : Fin (n + 1) → 𝔽) i b) = 0)).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        rcases hi with ⟨j, hj, rfl⟩
        rcases hj with ⟨hz, b, hb, hfb⟩
        refine ⟨?_, b, hb, ?_⟩
        · simpa [e] using hz
        · simpa [e, Function.update, Fin.cons] using hfb
  · simp [qary_hamming_boundary, hf]

@[blueprint "lem:qary-hamming-boundary-zero-slice-cross"
  (statement := /-- Let $a\ne0$.  At a point $z$ of the zero slice, the full outgoing boundary is at least the boundary inside that slice, plus one whenever the zero slice has value $1$ and the $a$-slice has value $0$. -/)
  (proof := /-- If the two slice values do not form a $1$-to-$0$ transition, the claim is \cref{lem:qary-hamming-boundary-slice-le}.  Otherwise, unfold \cref{def:qary-hamming-boundary}.  The successor embedding supplies all boundary coordinates of the zero slice, while the first coordinate is an additional boundary coordinate because changing it from zero to $a$ makes the function vanish.  These coordinates are disjoint, and their union embeds in the full filtered boundary set, giving the asserted cardinality bound. -/)
  (title := /-- The first coordinate contributes a cross-slice boundary -/)
  (latexEnv := "lemma")]
lemma qary_hamming_boundary_zero_slice_cross
    {𝔽 : Type*} [Zero 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (f : (Fin (n + 1) → 𝔽) → ℝ) (a : 𝔽) (ha : a ≠ 0)
    (z : Fin n → 𝔽) :
    qary_hamming_boundary (fun x => f (Fin.cons 0 x)) z +
        (if f (Fin.cons 0 z) = 1 ∧ f (Fin.cons a z) = 0 then 1 else 0) ≤
      qary_hamming_boundary f (Fin.cons 0 z) := by
  classical
  by_cases hcross : f (Fin.cons 0 z) = 1 ∧ f (Fin.cons a z) = 0
  · rcases hcross with ⟨hf0, hfa⟩
    simp only [hf0, hfa, true_and, if_true, qary_hamming_boundary]
    let e : Fin n ↪ Fin (n + 1) :=
      ⟨fun i => i.succ, Fin.succ_injective n⟩
    let s := Finset.univ.filter (fun i : Fin n =>
      z i = 0 ∧ ∃ b : 𝔽, b ≠ 0 ∧
        f (Fin.cons 0 (Function.update z i b)) = 0)
    let t := Finset.univ.filter (fun i : Fin (n + 1) =>
      (Fin.cons 0 z : Fin (n + 1) → 𝔽) i = 0 ∧ ∃ b : 𝔽, b ≠ 0 ∧
        f (Function.update (Fin.cons 0 z : Fin (n + 1) → 𝔽) i b) = 0)
    change s.card + 1 ≤ t.card
    calc
      s.card + 1 = (insert 0 (s.map e)).card := by
        rw [Finset.card_insert_of_notMem]
        · simp
        · simp [e]
      _ ≤ t.card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · simp only [t, Finset.mem_filter, Finset.mem_univ, true_and,
            Fin.cons_zero]
          exact ⟨a, ha, by simpa [Function.update, Fin.cons] using hfa⟩
        · simp only [Finset.mem_map] at hi
          rcases hi with ⟨j, hj, rfl⟩
          simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hj
          rcases hj with ⟨hz, b, hb, hfb⟩
          simp only [t, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨?_, b, hb, ?_⟩
          · simpa [e] using hz
          · simpa [e, Function.update, Fin.cons] using hfb
  · simp only [hcross, if_false, add_zero]
    exact qary_hamming_boundary_slice_le f 0 z

@[blueprint "lem:qary-talagrand-sqrt-step"
  (statement := /-- Let $h\in\mathbb N$, let $d\in\{0,1\}$, and let $0\leq D\leq1$.  Then
  \[
    \left(1-\frac{D^2}{2}\right)\sqrt h+\frac D2d
      \leq\sqrt{h+d}.
  \] -/)
  (proof := /-- For $d=0$, the coefficient of $\sqrt h$ lies in $[0,1]$.  For $d=1$, put $x=\sqrt h$, $\alpha=1-D^2/2$, and $\beta=D/2$.  The bounds on $D$ give $\alpha,\beta\geq0$ and $\alpha^2+\beta^2\leq1$.  Cauchy--Schwarz in two dimensions yields $(\alpha x+\beta)^2\leq x^2+1=h+1$; both sides are nonnegative, so taking square roots gives the claim. -/)
  (title := /-- A square-root increment estimate -/)
  (latexEnv := "lemma")]
lemma qary_talagrand_sqrt_step
    (h d : ℕ) (hd : d = 0 ∨ d = 1) {D : ℝ}
    (hD₀ : 0 ≤ D) (hD₁ : D ≤ 1) :
    (1 - D ^ 2 / 2) * Real.sqrt (h : ℝ) + D / 2 * d ≤
      Real.sqrt ((h + d : ℕ) : ℝ) := by
  rcases hd with rfl | rfl
  · simp only [Nat.cast_zero, mul_zero, add_zero]
    have hsqrt : 0 ≤ Real.sqrt (h : ℝ) := Real.sqrt_nonneg _
    have hcoef : 1 - D ^ 2 / 2 ≤ 1 := by nlinarith [sq_nonneg D]
    exact mul_le_of_le_one_left hsqrt hcoef
  · simp only [Nat.cast_one, mul_one, Nat.cast_add]
    have hx₀ : 0 ≤ Real.sqrt (h : ℝ) := Real.sqrt_nonneg _
    have hx2 : (Real.sqrt (h : ℝ)) ^ 2 = (h : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    have hDsq : D ^ 2 ≤ 1 := by nlinarith [sq_nonneg D]
    have ha₀ : 0 ≤ 1 - D ^ 2 / 2 := by nlinarith
    have hb₀ : 0 ≤ D / 2 := by positivity
    have hab : (1 - D ^ 2 / 2) ^ 2 + (D / 2) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (sq_nonneg D) (sub_nonneg.mpr hDsq)]
    have hcs :
        ((1 - D ^ 2 / 2) * Real.sqrt (h : ℝ) + D / 2) ^ 2 ≤
          ((1 - D ^ 2 / 2) ^ 2 + (D / 2) ^ 2) *
            ((Real.sqrt (h : ℝ)) ^ 2 + 1) := by
      nlinarith [sq_nonneg
        ((1 - D ^ 2 / 2) - (D / 2) * Real.sqrt (h : ℝ))]
    have hsq :
        ((1 - D ^ 2 / 2) * Real.sqrt (h : ℝ) + D / 2) ^ 2 ≤
          (h : ℝ) + 1 := by
      rw [hx2] at hcs
      nlinarith [mul_nonneg (sub_nonneg.mpr hab) (by positivity : 0 ≤ (h : ℝ) + 1)]
    rw [Real.le_sqrt (by positivity)]
    · exact hsq
    · positivity

@[blueprint "lem:qary-weighted-variance-range-bound"
  (statement := /-- Let $(w_i)$ be nonnegative weights of total mass $1$, and suppose that $\ell\leq x_i\leq u$ for every $i$.  If $\mu=\sum_iw_ix_i$, then
  \[
    \mu(1-\mu)\leq\sum_iw_ix_i(1-x_i)+\frac{(u-\ell)^2}{4}.
  \] -/)
  (proof := /-- The difference between the two Bernoulli-variance expressions is the weighted variance $\sum_iw_i(x_i-\mu)^2$.  Centering instead at $(\ell+u)/2$ adds the nonnegative square $(\mu-(\ell+u)/2)^2$.  Since every $x_i$ lies in $[\ell,u]$, its squared distance from this midpoint is at most $(u-\ell)^2/4$.  Averaging with the normalized nonnegative weights gives the result. -/)
  (title := /-- Weighted variance is bounded by one quarter of the squared range -/)
  (latexEnv := "lemma")]
lemma qary_weighted_variance_range_bound
    {ι : Type*} [Fintype ι] (w x : ι → ℝ) (μ : ℝ) {l u : ℝ}
    (hμ : μ = ∑ i, w i * x i)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (hxl : ∀ i, l ≤ x i) (hxu : ∀ i, x i ≤ u) :
    μ * (1 - μ) ≤ ∑ i, w i * (x i * (1 - x i)) + (u - l) ^ 2 / 4 := by
  classical
  let c := (l + u) / 2
  have hpoint (i : ι) : (x i - c) ^ 2 ≤ (u - l) ^ 2 / 4 := by
    dsimp [c]
    nlinarith [sq_nonneg (x i - l), sq_nonneg (u - x i),
      mul_nonneg (sub_nonneg.mpr (hxl i)) (sub_nonneg.mpr (hxu i))]
  have hcenter : ∑ i, w i * (x i - c) ^ 2 ≤ (u - l) ^ 2 / 4 := by
    calc
      ∑ i, w i * (x i - c) ^ 2 ≤
          ∑ i, w i * ((u - l) ^ 2 / 4) := by
        exact Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_left (hpoint i) (hw i))
      _ = (u - l) ^ 2 / 4 := by
        rw [← Finset.sum_mul]
        simp [hwsum]
  have hshift :
      ∑ i, w i * (x i - c) ^ 2 =
        ∑ i, w i * (x i - μ) ^ 2 + (μ - c) ^ 2 := by
    have hcross : ∑ i, w i * (x i - μ) = 0 := by
      calc
        ∑ i, w i * (x i - μ) =
            ∑ i, (w i * x i - μ * w i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ =
            (∑ i, w i * x i) - μ * ∑ i, w i := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
        _ = 0 := by rw [← hμ, hwsum]; ring
    calc
      ∑ i, w i * (x i - c) ^ 2 =
          ∑ i, (w i * (x i - μ) ^ 2 +
            (2 * (μ - c)) * (w i * (x i - μ)) +
            w i * (μ - c) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i, w i * (x i - μ) ^ 2) +
          (2 * (μ - c)) * (∑ i, w i * (x i - μ)) +
          (∑ i, w i) * (μ - c) ^ 2 := by
        simp_rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
      _ = ∑ i, w i * (x i - μ) ^ 2 + (μ - c) ^ 2 := by
        rw [hcross, hwsum]
        ring
  have hvar : ∑ i, w i * (x i - μ) ^ 2 ≤ (u - l) ^ 2 / 4 := by
    rw [hshift] at hcenter
    nlinarith [sq_nonneg (μ - c)]
  have hid :
      μ * (1 - μ) - ∑ i, w i * (x i * (1 - x i)) =
        ∑ i, w i * (x i - μ) ^ 2 := by
    have hvar_expand :
        ∑ i, w i * (x i - μ) ^ 2 =
          (∑ i, w i * x i ^ 2) - μ ^ 2 := by
      have hmid :
          ∑ i, 2 * μ * (w i * x i) = 2 * μ * ∑ i, w i * x i := by
        rw [← Finset.mul_sum]
      have hlast : ∑ i, μ ^ 2 * w i = μ ^ 2 * ∑ i, w i := by
        rw [← Finset.mul_sum]
      calc
        ∑ i, w i * (x i - μ) ^ 2 =
            ∑ i, (w i * x i ^ 2 - 2 * μ * (w i * x i) + μ ^ 2 * w i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (∑ i, w i * x i ^ 2) - 2 * μ * (∑ i, w i * x i) +
            μ ^ 2 * (∑ i, w i) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hmid, hlast]
        _ = (∑ i, w i * x i ^ 2) - μ ^ 2 := by
          rw [← hμ, hwsum]
          ring
    rw [hvar_expand]
    have hbern :
        ∑ i, w i * (x i * (1 - x i)) =
          μ - ∑ i, w i * x i ^ 2 := by
      calc
        ∑ i, w i * (x i * (1 - x i)) =
            ∑ i, (w i * x i - w i * x i ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = μ - ∑ i, w i * x i ^ 2 := by
          rw [Finset.sum_sub_distrib]
          rw [← hμ]
    rw [hbern]
    ring
  nlinarith [hid, hvar]

@[blueprint "thm:qary-product-talagrand"
  (statement := /-- Let $\mathbb F$ be a finite field, let $f\colon\mathbb F^n\to\{0,1\}$ be downward monotone, and let $0\leq p\leq1$.  Then
  \[
    \mathbb E_p[\sqrt{h_f}]
      \geq\frac{1-p}{2}\,
        \mathbb E_p[f]\bigl(1-\mathbb E_p[f]\bigr).
  \] -/)
  (proof := /-- We argue by induction on $n$.  For $n=0$, Booleanity makes $f$ constant, so both sides vanish.  Suppose the result holds in dimension $n$, write $f_a(z)=f(a,z)$ for the first-coordinate slices, and put $E_a=\mathbb E_p[f_a]$.  Expanding \cref{def:qary-noise-expectation} gives
  \[
    \mathbb E_p[f]=(1-p)E_0+
      \frac{p}{|\mathbb F|-1}\sum_{a\ne0}E_a.
  \]
  Each $f_a$ is Boolean and downward monotone.  Moreover, \cref{def:qary-downward-monotone} gives $f_a\leq f_0$ pointwise, hence $E_a\leq E_0$; all slice means lie in $[0,1]$ by \cref{lem:qary-noise-expectation-boolean-bounds}.

  Choose a nonzero $a_*$ minimizing $E_a$ among the nonzero slices and set $D=E_0-E_{a_*}$.  Then every $E_a$ lies in $[E_{a_*},E_0]$.  Applying \cref{lem:qary-weighted-variance-range-bound} to the coordinate weights yields
  \[
    \mathbb E_p[f](1-\mathbb E_p[f])
      \leq \sum_a w_aE_a(1-E_a)+\frac{D^2}{4},
  \]
  where $w_0=1-p$ and $w_a=p/(|\mathbb F|-1)$ for $a\ne0$.

  Define $\delta(z)$ to be $1$ when $f_0(z)=1$ and $f_{a_*}(z)=0$, and $0$ otherwise.  Booleanity and the pointwise order give $\delta=f_0-f_{a_*}$, so linearity from \cref{lem:qary-noise-expectation-linear} implies $\mathbb E_p[\delta]=D$.  By \cref{lem:qary-hamming-boundary-zero-slice-cross},
  $h_f(0,z)\geq h_{f_0}(z)+\delta(z)$.  The scalar estimate \cref{lem:qary-talagrand-sqrt-step}, with this $D$, therefore shows pointwise that
  \[
    \sqrt{h_f(0,z)}\geq
      \left(1-\frac{D^2}{2}\right)\sqrt{h_{f_0}(z)}
        +\frac D2\delta(z).
  \]
  After taking expectations and applying the induction hypothesis to $f_0$, this gives an additional contribution of at least $D^2/4$ on the zero slice.  For every slice, \cref{lem:qary-hamming-boundary-slice-le} embeds its internal boundary in the full boundary, so the induction hypothesis supplies
  $(1-p)E_a(1-E_a)/2$ there.  Averaging these estimates with the weights $w_a$, the zero-slice bonus dominates $(1-p)D^2/8$, while the weighted slice terms dominate
  $(1-p)\sum_aw_aE_a(1-E_a)/2$.  The preceding variance bound now gives exactly
  \[
    \mathbb E_p[\sqrt{h_f}]
      \geq\frac{1-p}{2}\mathbb E_p[f](1-\mathbb E_p[f]),
  \]
  completing the induction. -/)
  (title := /-- Talagrand's boundary inequality on a q-ary product -/)
  (latexEnv := "theorem")]
theorem qary_product_talagrand
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (f : (Fin n → 𝔽) → ℝ)
    (hf01 : ∀ z, f z = 0 ∨ f z = 1)
    (hfmono : qary_downward_monotone f) {p : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    (1 - p) / 2 * qary_noise_expectation p f *
        (1 - qary_noise_expectation p f) ≤
      qary_noise_expectation p
        (fun z => Real.sqrt (qary_hamming_boundary f z : ℝ)) := by
  classical
  induction n with
  | zero =>
      rcases hf01 default with h | h <;>
        simp [qary_noise_expectation, qary_hamming_boundary, h]
  | succ n ih =>
      let slice : 𝔽 → (Fin n → 𝔽) → ℝ := fun a z => f (Fin.cons a z)
      have h_expect :
          qary_noise_expectation p f =
            ∑ a : 𝔽, (if a = 0 then 1 - p
              else p / ((Fintype.card 𝔽 : ℝ) - 1)) *
                qary_noise_expectation p (slice a) := by
        simp [qary_noise_expectation, slice, ← (Fin.consEquiv (fun _ => 𝔽)).sum_comp,
          Fin.prod_univ_succ, Finset.mul_sum, mul_assoc, Fintype.sum_prod_type,
          Fin.consEquiv]
      let E : 𝔽 → ℝ := fun a => qary_noise_expectation p (slice a)
      let W : 𝔽 → ℝ := fun a =>
        if a = 0 then 1 - p else p / ((Fintype.card 𝔽 : ℝ) - 1)
      have hs01 (a : 𝔽) (z : Fin n → 𝔽) :
          slice a z = 0 ∨ slice a z = 1 := hf01 (Fin.cons a z)
      have hsmono (a : 𝔽) : qary_downward_monotone (slice a) := by
        intro x y hxy hy
        apply hfmono (y := Fin.cons a y)
        · intro i
          refine Fin.cases (Or.inr rfl) (fun j => ?_) i
          simpa using hxy j
        · exact hy
      have hsle (a : 𝔽) (z : Fin n → 𝔽) : slice a z ≤ slice 0 z := by
        rcases hs01 a z with ha0 | ha1
        · rcases hs01 0 z with h00 | h01
          · simp [ha0, h00]
          · simp [ha0, h01]
        · have h01 : slice 0 z = 1 := by
            apply hfmono (y := Fin.cons a z)
            · intro i
              refine Fin.cases (Or.inl rfl) (fun j => Or.inr rfl) i
            · exact ha1
          simp [ha1, h01]
      have hc : (1 : ℕ) < Fintype.card 𝔽 := Fintype.one_lt_card
      have hcr : (1 : ℝ) < Fintype.card 𝔽 := by
        exact_mod_cast hc
      have hwz (z : Fin n → 𝔽) :
          0 ≤ ∏ i : Fin n, if z i = 0 then 1 - p
            else p / ((Fintype.card 𝔽 : ℝ) - 1) := by
        positivity
      have hEle (a : 𝔽) : E a ≤ E 0 := by
        simp only [E, qary_noise_expectation]
        exact Finset.sum_le_sum (fun z _ =>
          mul_le_mul_of_nonneg_left (hsle a z) (hwz z))
      have hEb (a : 𝔽) : 0 ≤ E a ∧ E a ≤ 1 :=
        qary_noise_expectation_boolean_bounds (slice a) (hs01 a) hp₀ hp₁
      have hW (a : 𝔽) : 0 ≤ W a := by
        dsimp [W]
        split_ifs <;> positivity
      have hzcard : Fintype.card {a : 𝔽 // a = 0} = 1 :=
        Fintype.card_subtype_eq 0
      have hnzcard : Fintype.card {a : 𝔽 // a ≠ 0} = Fintype.card 𝔽 - 1 :=
        Fintype.card_subtype_compl (fun a : 𝔽 => a = 0)
      have hWsum : ∑ a : 𝔽, W a = 1 := by
        dsimp [W]
        have hd : (Fintype.card 𝔽 : ℝ) - 1 ≠ 0 :=
          ne_of_gt (sub_pos.mpr hcr)
        simp [Finset.sum_ite, ← Fintype.card_subtype, hzcard, hnzcard, hd]
        rw [Nat.cast_sub (le_of_lt hc)]
        field_simp
        ring
      let oneNZ : {a : 𝔽 // a ≠ 0} := ⟨1, one_ne_zero⟩
      obtain ⟨amin, hamin, hmin⟩ := Finset.exists_min_image Finset.univ
        (fun a : {a : 𝔽 // a ≠ 0} => E a.1)
        (show Finset.univ.Nonempty from ⟨oneNZ, Finset.mem_univ oneNZ⟩)
      let a : 𝔽 := amin.1
      have ha : a ≠ 0 := amin.2
      have hminE (b : 𝔽) (hb : b ≠ 0) : E a ≤ E b := by
        exact hmin ⟨b, hb⟩ (Finset.mem_univ _)
      let D : ℝ := E 0 - E a
      let δ : (Fin n → 𝔽) → ℕ := fun z =>
        if slice 0 z = 1 ∧ slice a z = 0 then 1 else 0
      have hD₀ : 0 ≤ D := by
        dsimp [D]
        exact sub_nonneg.mpr (hEle a)
      have hD₁ : D ≤ 1 := by
        dsimp [D]
        nlinarith [(hEb 0).2, (hEb a).1]
      have hδ01 (z : Fin n → 𝔽) : δ z = 0 ∨ δ z = 1 := by
        dsimp [δ]
        split_ifs <;> simp
      have hδpoint (z : Fin n → 𝔽) :
          (δ z : ℝ) = slice 0 z - slice a z := by
        rcases hs01 0 z with h00 | h01
        · rcases hs01 a z with ha0 | ha1
          · simp [δ, h00, ha0]
          · exfalso
            have := hsle a z
            simp [h00, ha1] at this
            norm_num at this
        · rcases hs01 a z with ha0 | ha1
          · simp [δ, h01, ha0]
          · simp [δ, h01, ha1]
      have hδexp :
          qary_noise_expectation p (fun z => (δ z : ℝ)) = D := by
        dsimp [D, E]
        simp only [qary_noise_expectation]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro z hz
        rw [hδpoint]
        ring
      have hElower (b : 𝔽) : E a ≤ E b := by
        by_cases hb : b = 0
        · subst b
          exact hEle a
        · exact hminE b hb
      have hmean : qary_noise_expectation p f = ∑ b : 𝔽, W b * E b := by
        simpa [W, E] using h_expect
      have hvariance :
          qary_noise_expectation p f * (1 - qary_noise_expectation p f) ≤
            ∑ b : 𝔽, W b * (E b * (1 - E b)) + D ^ 2 / 4 := by
        simpa [D] using qary_weighted_variance_range_bound W E
          (qary_noise_expectation p f) hmean hW hWsum hElower hEle
      let c : ℝ := (1 - p) / 2
      let B : 𝔽 → ℝ := fun b => qary_noise_expectation p
        (fun z => Real.sqrt (qary_hamming_boundary (slice b) z : ℝ))
      let G : 𝔽 → ℝ := fun b => qary_noise_expectation p
        (fun z => Real.sqrt (qary_hamming_boundary f (Fin.cons b z) : ℝ))
      have hc₀ : 0 ≤ c := by
        dsimp [c]
        positivity
      have hIH (b : 𝔽) : c * E b * (1 - E b) ≤ B b := by
        simpa [c, E, B] using ih (slice b) (hs01 b) (hsmono b)
      have hBG (b : 𝔽) : B b ≤ G b := by
        simp only [B, G, qary_noise_expectation]
        apply Finset.sum_le_sum
        intro z hz
        apply mul_le_mul_of_nonneg_left _ (hwz z)
        apply Real.sqrt_le_sqrt
        exact_mod_cast qary_hamming_boundary_slice_le f b z
      have hstep (z : Fin n → 𝔽) :
          (1 - D ^ 2 / 2) *
                Real.sqrt (qary_hamming_boundary (slice 0) z : ℝ) +
              D / 2 * (δ z : ℝ) ≤
            Real.sqrt (qary_hamming_boundary f (Fin.cons 0 z) : ℝ) := by
        calc
          (1 - D ^ 2 / 2) *
                Real.sqrt (qary_hamming_boundary (slice 0) z : ℝ) +
              D / 2 * (δ z : ℝ) ≤
              Real.sqrt ((qary_hamming_boundary (slice 0) z + δ z : ℕ) : ℝ) :=
            qary_talagrand_sqrt_step _ _ (hδ01 z) hD₀ hD₁
          _ ≤ Real.sqrt (qary_hamming_boundary f (Fin.cons 0 z) : ℝ) := by
            apply Real.sqrt_le_sqrt
            exact_mod_cast (show qary_hamming_boundary (slice 0) z + δ z ≤
              qary_hamming_boundary f (Fin.cons 0 z) by
                simpa [slice, δ] using
                  qary_hamming_boundary_zero_slice_cross f a ha z)
      have hGzero :
          (1 - D ^ 2 / 2) * B 0 + D / 2 * D ≤ G 0 := by
        have hlin :
            qary_noise_expectation p (fun z =>
                (1 - D ^ 2 / 2) *
                    Real.sqrt (qary_hamming_boundary (slice 0) z : ℝ) +
                  D / 2 * (δ z : ℝ)) =
              (1 - D ^ 2 / 2) * B 0 + D / 2 * D := by
          rw [qary_noise_expectation_linear, hδexp]
        rw [← hlin]
        simp only [G, B, qary_noise_expectation]
        exact Finset.sum_le_sum (fun z _ =>
          mul_le_mul_of_nonneg_left (hstep z) (hwz z))
      let A : ℝ := c * E 0 * (1 - E 0)
      have hA₀ : 0 ≤ A := by
        dsimp [A]
        exact mul_nonneg (mul_nonneg hc₀ (hEb 0).1)
          (sub_nonneg.mpr (hEb 0).2)
      have hA₁ : A ≤ 1 / 2 := by
        dsimp [A, c]
        nlinarith [sq_nonneg (E 0 - 1 / 2), hp₀, hp₁,
          (hEb 0).1, (hEb 0).2]
      have hzero_bonus : A + D ^ 2 / 4 ≤ G 0 := by
        have hcoef : 0 ≤ 1 - D ^ 2 / 2 := by
          nlinarith [sq_nonneg D]
        have hscaled := mul_le_mul_of_nonneg_left (hIH 0) hcoef
        nlinarith [hGzero, hA₀, hA₁, sq_nonneg D]
      have hfull :
          qary_noise_expectation p
              (fun z => Real.sqrt (qary_hamming_boundary f z : ℝ)) =
            ∑ b : 𝔽, W b * G b := by
        simp [qary_noise_expectation, W, G,
          ← (Fin.consEquiv (fun _ => 𝔽)).sum_comp, Fin.prod_univ_succ,
          Finset.mul_sum, mul_assoc, Fintype.sum_prod_type, Fin.consEquiv]
      have hpointsum (b : 𝔽) :
          W b * (c * E b * (1 - E b)) +
              (if b = 0 then c * D ^ 2 / 4 else 0) ≤
            W b * G b := by
        by_cases hb : b = 0
        · subst b
          have hmul := mul_le_mul_of_nonneg_left hzero_bonus (hW 0)
          have hW0 : W 0 = 1 - p := by simp [W]
          have hcW : 1 - p = 2 * c := by
            dsimp [c]
            ring
          simp only [if_pos]
          dsimp [A] at hmul
          rw [hW0, hcW] at hmul ⊢
          nlinarith [mul_nonneg hc₀ (sq_nonneg D)]
        · simp only [if_neg hb, add_zero]
          exact mul_le_mul_of_nonneg_left ((hIH b).trans (hBG b)) (hW b)
      have hsum :
          (∑ b : 𝔽, W b * (c * E b * (1 - E b))) + c * D ^ 2 / 4 ≤
            ∑ b : 𝔽, W b * G b := by
        calc
          (∑ b : 𝔽, W b * (c * E b * (1 - E b))) + c * D ^ 2 / 4 =
              ∑ b : 𝔽, (W b * (c * E b * (1 - E b)) +
                if b = 0 then c * D ^ 2 / 4 else 0) := by
            rw [Finset.sum_add_distrib]
            simp
          _ ≤ ∑ b : 𝔽, W b * G b :=
            Finset.sum_le_sum (fun b _ => hpointsum b)
      have hvarc :
          c * qary_noise_expectation p f *
              (1 - qary_noise_expectation p f) ≤
            (∑ b : 𝔽, W b * (c * E b * (1 - E b))) +
              c * D ^ 2 / 4 := by
        have hm := mul_le_mul_of_nonneg_left hvariance hc₀
        calc
          c * qary_noise_expectation p f *
                (1 - qary_noise_expectation p f) =
              c * (qary_noise_expectation p f *
                (1 - qary_noise_expectation p f)) := by ring
          _ ≤ c * ((∑ b : 𝔽, W b * (E b * (1 - E b))) + D ^ 2 / 4) := hm
          _ = (∑ b : 𝔽, W b * (c * E b * (1 - E b))) +
                c * D ^ 2 / 4 := by
            rw [mul_add, Finset.mul_sum]
            apply congrArg₂ (· + ·)
            · apply Finset.sum_congr rfl
              intro b hb
              ring
            · ring
      change c * qary_noise_expectation p f *
          (1 - qary_noise_expectation p f) ≤
        qary_noise_expectation p
          (fun z => Real.sqrt (qary_hamming_boundary f z : ℝ))
      rw [hfull]
      exact hvarc.trans hsum

@[blueprint "thm:qary-edge-isoperimetry"
  (statement := /-- Let $\mathbb F$ be a finite field, let $n\in\mathbb N$, let $f\colon\mathbb F^n\to\{0,1\}$ be downward monotone, let $0\leq p\leq1$, and let $\Delta_f$ be its minimum positive outgoing Hamming boundary.  Then
  \[
    \mathbb E_p[h_f]\geq
      \frac{1-p}{2}\sqrt{\Delta_f}\,
      \mathbb E_p[f]\bigl(1-\mathbb E_p[f]\bigr).
  \] -/)
  (proof := /-- By the definition in \cref{def:minimum-positive-boundary}, every positive value of $h_f$ is at least $\Delta_f$.  Thus, at every $z$, if $h_f(z)=0$ then
  $\sqrt{\Delta_f}\sqrt{h_f(z)}\leq h_f(z)$ is immediate, whereas if $h_f(z)>0$ then
  \[
    \sqrt{\Delta_f}\sqrt{h_f(z)}
      \leq \sqrt{h_f(z)}\sqrt{h_f(z)}=h_f(z).
  \]
  Since all weights of the biased product law are nonnegative, taking expectations gives
  \[
    \sqrt{\Delta_f}\,\mathbb E_p[\sqrt{h_f}]
      \leq \mathbb E_p[h_f].
  \]
  Multiplying the inequality of \cref{thm:qary-product-talagrand} by the nonnegative number $\sqrt{\Delta_f}$ and combining it with this expectation bound proves the assertion. -/)
  (title := /-- Edge isoperimetry for a q-ary biased product -/)
  (latexEnv := "theorem")]
theorem qary_edge_isoperimetry
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (f : (Fin n → 𝔽) → ℝ)
    (hf01 : ∀ z, f z = 0 ∨ f z = 1)
    (hfmono : qary_downward_monotone f) {p : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    (1 - p) / 2 * Real.sqrt (minimum_positive_boundary f : ℝ) *
        qary_noise_expectation p f * (1 - qary_noise_expectation p f) ≤
      qary_noise_expectation p
        (fun z => (qary_hamming_boundary f z : ℝ)) := by
  classical
  have hpoint (z : Fin n → 𝔽) :
      Real.sqrt (minimum_positive_boundary f : ℝ) *
          Real.sqrt (qary_hamming_boundary f z : ℝ) ≤
        (qary_hamming_boundary f z : ℝ) := by
    by_cases hz : qary_hamming_boundary f z = 0
    · simp [hz]
    · have hzpos : 0 < qary_hamming_boundary f z := Nat.pos_of_ne_zero hz
      have hminNat :
          minimum_positive_boundary f ≤ qary_hamming_boundary f z := by
        apply Nat.sInf_le
        exact ⟨hzpos, z, rfl⟩
      have hmin :
          (minimum_positive_boundary f : ℝ) ≤
            (qary_hamming_boundary f z : ℝ) := by
        exact_mod_cast hminNat
      calc
        Real.sqrt (minimum_positive_boundary f : ℝ) *
              Real.sqrt (qary_hamming_boundary f z : ℝ) ≤
            Real.sqrt (qary_hamming_boundary f z : ℝ) *
              Real.sqrt (qary_hamming_boundary f z : ℝ) :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hmin)
            (Real.sqrt_nonneg _)
        _ = (qary_hamming_boundary f z : ℝ) :=
          Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hweight (z : Fin n → 𝔽) :
      0 ≤ ∏ i : Fin n, if z i = 0 then 1 - p
        else p / ((Fintype.card 𝔽 : ℝ) - 1) := by
    have hq : (1 : ℝ) < Fintype.card 𝔽 := by
      exact_mod_cast Fintype.one_lt_card (α := 𝔽)
    positivity
  have hexpect :
      Real.sqrt (minimum_positive_boundary f : ℝ) *
          qary_noise_expectation p
            (fun z => Real.sqrt (qary_hamming_boundary f z : ℝ)) ≤
        qary_noise_expectation p
          (fun z => (qary_hamming_boundary f z : ℝ)) := by
    simp only [qary_noise_expectation]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z hz
    calc
      Real.sqrt (minimum_positive_boundary f : ℝ) *
            ((∏ i : Fin n, if z i = 0 then 1 - p
              else p / ((Fintype.card 𝔽 : ℝ) - 1)) *
                Real.sqrt (qary_hamming_boundary f z : ℝ)) =
          (∏ i : Fin n, if z i = 0 then 1 - p
            else p / ((Fintype.card 𝔽 : ℝ) - 1)) *
              (Real.sqrt (minimum_positive_boundary f : ℝ) *
                Real.sqrt (qary_hamming_boundary f z : ℝ)) := by ring
      _ ≤ (∏ i : Fin n, if z i = 0 then 1 - p
            else p / ((Fintype.card 𝔽 : ℝ) - 1)) *
              (qary_hamming_boundary f z : ℝ) :=
        mul_le_mul_of_nonneg_left (hpoint z) (hweight z)
  have ht := qary_product_talagrand f hf01 hfmono hp₀ hp₁
  have hmul := mul_le_mul_of_nonneg_left ht
    (Real.sqrt_nonneg (minimum_positive_boundary f : ℝ))
  calc
    (1 - p) / 2 * Real.sqrt (minimum_positive_boundary f : ℝ) *
          qary_noise_expectation p f * (1 - qary_noise_expectation p f) =
        Real.sqrt (minimum_positive_boundary f : ℝ) *
          ((1 - p) / 2 * qary_noise_expectation p f *
            (1 - qary_noise_expectation p f)) := by ring
    _ ≤ Real.sqrt (minimum_positive_boundary f : ℝ) *
          qary_noise_expectation p
            (fun z => Real.sqrt (qary_hamming_boundary f z : ℝ)) := hmul
    _ ≤ qary_noise_expectation p
          (fun z => (qary_hamming_boundary f z : ℝ)) := hexpect

@[blueprint "lem:maximum-likelihood-region-boundary"
  (statement := /-- Let $\mathbb F$ be a finite field, let $n\in\mathbb N$, let $C\leq\mathbb F^n$ be a linear code, and let $D^*$ be a sharp-threshold decoder for $C$.  Write $\Delta$ for the minimum positive boundary of the zero-codeword decoding region of $D^*$.  Then
  \[
    \Delta\geq \frac{d_{\min}(C)}{|\mathbb F|}-3.
  \] -/)
  (proof := /-- The final clause of \cref{def:is-sharp-threshold-decoder} is precisely the asserted lower bound for the minimum positive boundary of the zero-codeword decoding region. -/)
  (title := /-- Boundary size of a nearest-neighbor decoding region -/)
  (latexEnv := "lemma")]
lemma maximum_likelihood_region_boundary
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (C : qary_linear_code 𝔽 n) (Dstar : qary_decoder C)
    (hDstar : is_sharp_threshold_decoder C Dstar) :
    (linear_code_minimum_distance C : ℝ) / (Fintype.card 𝔽 : ℝ) - 3 ≤
      (minimum_positive_boundary
        (qary_decoding_region_indicator C Dstar) : ℝ) := by
  exact hDstar.2.2.2

@[blueprint "lem:sharp-threshold-decoder-success-polynomial"
  (statement := /-- Let $\mathbb F$ be a finite field, let $n\in\mathbb N$, let $C\leq\mathbb F^n$ be a linear code, and let $D^*$ be a sharp-threshold decoder for $C$.  For every $p\in\mathbb R$ with $0\leq p\leq1$, the $q$-ary biased expectation of the real-valued indicator of the zero decoding region equals the real value of the success probability for transmission of zero over $\mathrm{qSC}_p$:
  \[
    \mathbb E_p\!\left[z\mapsto D^*(z)(0)\right]
      = \Pr_{z\sim\mathrm{qSC}_p}[D^*(z)=0].
  \] -/)
  (proof := /-- Expand the success probability and its channel weights using \cref{def:qsc-success-probability, def:qsc-error-mass}, and expand the other side using \cref{def:qary-noise-expectation, def:qary-decoding-region-indicator}.  A finite field has cardinality at least two.  Hence $0\leq p\leq1$ implies that both $1-p$ and $p/(|\mathbb F|-1)$ are nonnegative.  Consequently, taking the real value of each channel factor recovers the corresponding real factor.  Every decoder weight is finite because it belongs to a probability mass function, and every channel factor is finite; therefore taking real values commutes with the finite products, their multiplication by decoder weights, and the finite sum over error vectors.  The summands on the two sides are thus equal term by term. -/)
  (title := /-- Decoding success as a finite biased-product polynomial -/)
  (latexEnv := "lemma")]
lemma sharp_threshold_decoder_success_polynomial
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (C : qary_linear_code 𝔽 n) (Dstar : qary_decoder C)
    (hDstar : is_sharp_threshold_decoder C Dstar) {p : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    qary_noise_expectation p (qary_decoding_region_indicator C Dstar) =
      (qsc_success_probability C Dstar p 0).toReal := by
  have hcard : (1 : ℝ) ≤ (Fintype.card 𝔽 : ℝ) := by
    exact_mod_cast (Nat.le_of_lt (Fintype.one_lt_card : 1 < Fintype.card 𝔽))
  have hden : 0 ≤ (Fintype.card 𝔽 : ℝ) - 1 := sub_nonneg.mpr hcard
  rw [qsc_success_probability, ENNReal.toReal_sum]
  · unfold qary_noise_expectation qary_decoding_region_indicator
    apply Finset.sum_congr rfl
    intro z hz
    simp only [Submodule.coe_zero, zero_add]
    rw [ENNReal.toReal_mul, qsc_error_mass, ENNReal.toReal_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hzi : z i = 0
    · simp [hzi, sub_nonneg.mpr hp₁]
    · simp [hzi, div_nonneg hp₀ hden]
  · intro z hz
    apply ENNReal.mul_ne_top
    · apply ENNReal.prod_ne_top
      intro i hi
      split <;> exact ENNReal.ofReal_ne_top
    · exact PMF.apply_ne_top _ _

@[blueprint "lem:maximum-likelihood-success-derivative"
  (statement := /-- Let $\mathbb F$ be a finite field, let $n\in\mathbb N$, let $C\leq\mathbb F^n$ be a linear code, and let $D^*$ be a sharp-threshold decoder for $C$ in the sense of \cref{def:is-sharp-threshold-decoder}.  Assume that
  $d_{\min}(C)\geq4|\mathbb F|$, and define the real-valued zero-codeword success function by
  \[
    g(t)=\Pr_{z\sim\mathrm{qSC}_t}[D^*(z)=0].
  \]
  Then, for every $r\in\mathbb R$ with $0<r<1$, the function $g$ is differentiable at $r$ and
  \[
    g'(r)\leq-\frac{1-r}{4}
      \frac{\sqrt{d_{\min}(C)}}{|\mathbb F|^{3/2}}
      g(r)(1-g(r)).
  \] -/)
  (proof := /-- Fix $r\in(0,1)$.  There is an open neighborhood of $r$ contained in $(0,1)$.  On this neighborhood, \cref{lem:sharp-threshold-decoder-success-polynomial} identifies $g$ with the finite biased-product expectation of the zero-region indicator from \cref{def:qary-decoding-region-indicator}.  Expanding \cref{def:qary-noise-expectation} expresses this expectation as a finite sum of products of affine functions of the channel parameter, so it is differentiable at $r$; local equality then gives the differentiability of $g$ and equality of the two derivatives at $r$.

  Apply \cref{lem:qary-russo-formula} to the downward-monotone zero-region indicator at $r$, and bound its boundary expectation from below with \cref{thm:qary-edge-isoperimetry}.  The estimate in \cref{lem:maximum-likelihood-region-boundary}, together with $d_{\min}(C)\geq4|\mathbb F|$, gives
  \[
    \frac{1}{|\mathbb F|-1}
      \sqrt{\frac{d_{\min}(C)}{|\mathbb F|}-3}
      \geq \frac12
      \frac{\sqrt{d_{\min}(C)}}{|\mathbb F|^{3/2}}.
  \]
  Indeed, $d_{\min}(C)/|\mathbb F|-3\geq d_{\min}(C)/(4|\mathbb F|)$, while $1/(|\mathbb F|-1)\geq1/|\mathbb F|$; taking square roots and using $|\mathbb F|^{3/2}=|\mathbb F|\sqrt{|\mathbb F|}$ proves the displayed comparison.  Finally, \cref{lem:qary-noise-expectation-boolean-bounds} gives $0\leq g(r)\leq1$, so $g(r)(1-g(r))\geq0$.  Multiplying the coefficient comparison by this nonnegative factor and combining it with the Russo and isoperimetric inequalities yields the asserted differential inequality. -/)
  (title := /-- Differential inequality for maximum-likelihood success -/)
  (latexEnv := "lemma")]
lemma maximum_likelihood_success_derivative
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (C : qary_linear_code 𝔽 n) (Dstar : qary_decoder C)
    (hDstar : is_sharp_threshold_decoder C Dstar)
    (hdist : 4 * Fintype.card 𝔽 ≤ linear_code_minimum_distance C)
    {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    DifferentiableAt ℝ
        (fun t => (qsc_success_probability C Dstar t 0).toReal) r ∧
      deriv (fun t => (qsc_success_probability C Dstar t 0).toReal) r ≤
        -((1 - r) / 4) *
          (Real.sqrt (linear_code_minimum_distance C : ℝ) /
            Real.rpow (Fintype.card 𝔽 : ℝ) (3 / 2 : ℝ)) *
          (qsc_success_probability C Dstar r 0).toReal *
          (1 - (qsc_success_probability C Dstar r 0).toReal) := by
  classical
  let f := qary_decoding_region_indicator C Dstar
  have hf01 : ∀ z, f z = 0 ∨ f z = 1 := by
    intro z
    rcases hDstar.2.1 z 0 with h | h
    · left
      simp [f, qary_decoding_region_indicator, h]
    · right
      simp [f, qary_decoding_region_indicator, h]
  have hfmono : qary_downward_monotone f := by
    simpa [f] using hDstar.2.2.1
  have hevent :
      (fun t => (qsc_success_probability C Dstar t 0).toReal) =ᶠ[nhds r]
        (fun t => qary_noise_expectation t f) := by
    filter_upwards [eventually_gt_nhds hr₀, eventually_lt_nhds hr₁] with t ht₀ ht₁
    exact (sharp_threshold_decoder_success_polynomial C Dstar hDstar
      ht₀.le ht₁.le).symm
  have hdiff_noise :
      DifferentiableAt ℝ (fun t => qary_noise_expectation t f) r := by
    unfold qary_noise_expectation
    apply DifferentiableAt.fun_sum
    intro z hz
    apply DifferentiableAt.mul_const
    apply DifferentiableAt.fun_finsetProd
    intro i hi
    by_cases hzi : z i = 0
    · simp [hzi]
      fun_prop
    · simp [hzi]
  have hdiff : DifferentiableAt ℝ
      (fun t => (qsc_success_probability C Dstar t 0).toReal) r :=
    hdiff_noise.congr_of_eventuallyEq hevent
  have hq_nat : 2 ≤ Fintype.card 𝔽 :=
    Nat.succ_le_iff.mpr Fintype.one_lt_card
  have hq : (2 : ℝ) ≤ (Fintype.card 𝔽 : ℝ) := by
    exact_mod_cast hq_nat
  have hqpos : (0 : ℝ) < (Fintype.card 𝔽 : ℝ) := by positivity
  have hqm1pos : (0 : ℝ) < (Fintype.card 𝔽 : ℝ) - 1 := by linarith
  have hd : (4 : ℝ) * (Fintype.card 𝔽 : ℝ) ≤
      (linear_code_minimum_distance C : ℝ) := by
    exact_mod_cast hdist
  have hratio : (4 : ℝ) ≤
      (linear_code_minimum_distance C : ℝ) / (Fintype.card 𝔽 : ℝ) :=
    (le_div_iff₀ hqpos).2 hd
  have hquarter_eq :
      (linear_code_minimum_distance C : ℝ) /
          (4 * (Fintype.card 𝔽 : ℝ)) =
        ((linear_code_minimum_distance C : ℝ) / (Fintype.card 𝔽 : ℝ)) / 4 := by
    field_simp
  have hquarter :
      (linear_code_minimum_distance C : ℝ) /
          (4 * (Fintype.card 𝔽 : ℝ)) ≤
        (linear_code_minimum_distance C : ℝ) / (Fintype.card 𝔽 : ℝ) - 3 := by
    rw [hquarter_eq]
    nlinarith
  have hboundary := maximum_likelihood_region_boundary C Dstar hDstar
  have hsmall :
      (linear_code_minimum_distance C : ℝ) /
          (4 * (Fintype.card 𝔽 : ℝ)) ≤
        (minimum_positive_boundary f : ℝ) := by
    exact hquarter.trans (by simpa [f] using hboundary)
  have hsqrt0 := Real.sqrt_le_sqrt hsmall
  have hdnonneg : (0 : ℝ) ≤ (linear_code_minimum_distance C : ℝ) := by
    positivity
  have hsqrt_den :
      Real.sqrt (4 * (Fintype.card 𝔽 : ℝ)) =
        2 * Real.sqrt (Fintype.card 𝔽 : ℝ) := by
    have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
      norm_num
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hsqrt4]
  have hsqrt :
      Real.sqrt (linear_code_minimum_distance C : ℝ) /
          (2 * Real.sqrt (Fintype.card 𝔽 : ℝ)) ≤
        Real.sqrt (minimum_positive_boundary f : ℝ) := by
    rw [← hsqrt_den, ← Real.sqrt_div hdnonneg]
    exact hsqrt0
  have hrecip :
      1 / (Fintype.card 𝔽 : ℝ) ≤
        1 / ((Fintype.card 𝔽 : ℝ) - 1) :=
    (one_div_le_one_div hqpos hqm1pos).2 (by linarith)
  have hcoeff :
      (1 / (Fintype.card 𝔽 : ℝ)) *
          (Real.sqrt (linear_code_minimum_distance C : ℝ) /
            (2 * Real.sqrt (Fintype.card 𝔽 : ℝ))) ≤
        (1 / ((Fintype.card 𝔽 : ℝ) - 1)) *
          Real.sqrt (minimum_positive_boundary f : ℝ) := by
    exact mul_le_mul hrecip hsqrt (by positivity) (by positivity)
  have hqpow :
      Real.rpow (Fintype.card 𝔽 : ℝ) (3 / 2 : ℝ) =
        (Fintype.card 𝔽 : ℝ) * Real.sqrt (Fintype.card 𝔽 : ℝ) := by
    rw [Real.rpow_eq_pow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hqpos, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have htotal_coeff :
      (1 - r) / 4 *
          (Real.sqrt (linear_code_minimum_distance C : ℝ) /
            Real.rpow (Fintype.card 𝔽 : ℝ) (3 / 2 : ℝ)) ≤
        (1 / ((Fintype.card 𝔽 : ℝ) - 1)) *
          ((1 - r) / 2 * Real.sqrt (minimum_positive_boundary f : ℝ)) := by
    rw [hqpow]
    calc
      (1 - r) / 4 *
            (Real.sqrt (linear_code_minimum_distance C : ℝ) /
              ((Fintype.card 𝔽 : ℝ) * Real.sqrt (Fintype.card 𝔽 : ℝ))) =
          (1 - r) / 2 *
            ((1 / (Fintype.card 𝔽 : ℝ)) *
              (Real.sqrt (linear_code_minimum_distance C : ℝ) /
                (2 * Real.sqrt (Fintype.card 𝔽 : ℝ)))) := by ring
      _ ≤ (1 - r) / 2 *
            ((1 / ((Fintype.card 𝔽 : ℝ) - 1)) *
              Real.sqrt (minimum_positive_boundary f : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hcoeff (by positivity)
      _ = (1 / ((Fintype.card 𝔽 : ℝ) - 1)) *
            ((1 - r) / 2 * Real.sqrt (minimum_positive_boundary f : ℝ)) := by ring
  have hE := qary_noise_expectation_boolean_bounds f hf01 hr₀.le hr₁.le
  have hEprod :
      0 ≤ qary_noise_expectation r f * (1 - qary_noise_expectation r f) :=
    mul_nonneg hE.1 (sub_nonneg.mpr hE.2)
  have hrusso := qary_russo_formula f hf01 hfmono hr₀.le hr₁
  have hedge := qary_edge_isoperimetry f hf01 hfmono hr₀.le hr₁.le
  have hsuccess := sharp_threshold_decoder_success_polynomial C Dstar hDstar
    hr₀.le hr₁.le
  constructor
  · exact hdiff
  · rw [hevent.deriv_eq, ← hsuccess]
    calc
      deriv (fun t => qary_noise_expectation t f) r ≤
          -(1 / ((Fintype.card 𝔽 : ℝ) - 1)) *
            qary_noise_expectation r
              (fun z => (qary_hamming_boundary f z : ℝ)) := hrusso
      _ ≤ -(1 / ((Fintype.card 𝔽 : ℝ) - 1)) *
            ((1 - r) / 2 * Real.sqrt (minimum_positive_boundary f : ℝ) *
              qary_noise_expectation r f * (1 - qary_noise_expectation r f)) := by
        exact mul_le_mul_of_nonpos_left hedge
          (neg_nonpos.mpr (le_of_lt (one_div_pos.mpr hqm1pos)))
      _ ≤ -((1 - r) / 4) *
            (Real.sqrt (linear_code_minimum_distance C : ℝ) /
              Real.rpow (Fintype.card 𝔽 : ℝ) (3 / 2 : ℝ)) *
            qary_noise_expectation r f * (1 - qary_noise_expectation r f) := by
        have hneg := mul_le_mul_of_nonneg_right (neg_le_neg htotal_coeff) hEprod
        nlinarith

@[blueprint "lem:logistic-threshold-integration"
  (statement := /-- Let $p_0,p_1,\kappa\in\mathbb R$ satisfy $p_0\leq p_1$ and $0\leq\kappa$.  Let $g\colon\mathbb R\to\mathbb R$ be differentiable on $[p_0,p_1]$, and suppose that $0<g(t)<1$ for every $t\in[p_0,p_1]$.  If
  \[
    g'(t)\leq-\kappa g(t)(1-g(t))
    \qquad(p_0\leq t\leq p_1),
  \]
  then
  \[
    g(p_1)(1-g(p_0))\leq
      \exp\bigl(-\kappa(p_1-p_0)\bigr).
  \] -/)
  (proof := /-- Define
  \[
    G(t)=\log g(t)-\log(1-g(t))+\kappa t.
  \]
  The strict bounds on $g$ ensure that $G$ is differentiable on the interval.  At every interior point, the chain rule and the differential inequality give
  \[
    G'(t)=\frac{g'(t)}{g(t)(1-g(t))}+\kappa\leq0.
  \]
  Hence $G$ is nonincreasing on $[p_0,p_1]$, so $G(p_1)\leq G(p_0)$.  Since $g(p_0)\leq1$ and $1-g(p_1)\leq1$, their logarithms are nonpositive.  Rearranging the endpoint inequality and using the logarithm product rule therefore yields
  \[
    \log\bigl(g(p_1)(1-g(p_0))\bigr)\leq-\kappa(p_1-p_0).
  \]
  The product on the left is positive, so exponentiating proves the result. -/)
  (title := /-- Integration of a logistic differential inequality -/)
  (latexEnv := "lemma")]
lemma logistic_threshold_integration
    (g : ℝ → ℝ) {p₀ p₁ κ : ℝ}
    (hp : p₀ ≤ p₁) (hκ : 0 ≤ κ)
    (hgdiff : DifferentiableOn ℝ g (Set.Icc p₀ p₁))
    (hg₀ : ∀ t ∈ Set.Icc p₀ p₁, 0 < g t)
    (hg₁ : ∀ t ∈ Set.Icc p₀ p₁, g t < 1)
    (hderiv : ∀ t ∈ Set.Icc p₀ p₁,
      deriv g t ≤ -κ * g t * (1 - g t)) :
    g p₁ * (1 - g p₀) ≤ Real.exp (-κ * (p₁ - p₀)) := by
  let G : ℝ → ℝ :=
    (fun t => Real.log (g t)) - (fun t => Real.log (1 - g t)) + (fun t => κ * t)
  have hg_ne : ∀ t ∈ Set.Icc p₀ p₁, g t ≠ 0 :=
    fun t ht => (hg₀ t ht).ne'
  have hone_ne : ∀ t ∈ Set.Icc p₀ p₁, 1 - g t ≠ 0 :=
    fun t ht => (sub_pos.mpr (hg₁ t ht)).ne'
  have hGdiff : DifferentiableOn ℝ G (Set.Icc p₀ p₁) := by
    have hlogg : DifferentiableOn ℝ (fun t => Real.log (g t)) (Set.Icc p₀ p₁) :=
      hgdiff.log hg_ne
    have hlogone : DifferentiableOn ℝ (fun t => Real.log (1 - g t))
        (Set.Icc p₀ p₁) :=
      ((differentiableOn_const (1 : ℝ)).sub hgdiff).log hone_ne
    have hlin : DifferentiableOn ℝ (fun t : ℝ => κ * t) (Set.Icc p₀ p₁) := by
      fun_prop
    exact (hlogg.sub hlogone).add hlin
  have hGderiv : ∀ t ∈ interior (Set.Icc p₀ p₁), deriv G t ≤ 0 := by
    intro t ht
    have htI : t ∈ Set.Icc p₀ p₁ := interior_subset ht
    have hgd : HasDerivAt g (deriv g t) t :=
      (hgdiff.differentiableAt (mem_interior_iff_mem_nhds.mp ht)).hasDerivAt
    have hone := (hasDerivAt_const (x := t) (c := (1 : ℝ))).sub hgd
    have hGraw :=
      ((hgd.log (hg_ne t htI)).sub (hone.log (hone_ne t htI))).add
        (hasDerivAt_const_mul (x := t) κ)
    have hGderiv_eq : deriv G t =
        deriv g t / g t + deriv g t / (1 - g t) + κ := by
      dsimp only [G]
      simpa only [Pi.sub_apply, Pi.add_apply, zero_sub, neg_div, sub_neg_eq_add]
        using hGraw.deriv
    rw [hGderiv_eq]
    have hden : 0 < g t * (1 - g t) :=
      mul_pos (hg₀ t htI) (sub_pos.mpr (hg₁ t htI))
    have hquot : deriv g t / (g t * (1 - g t)) ≤ -κ := by
      rw [div_le_iff₀ hden]
      nlinarith [hderiv t htI]
    have hid : deriv g t / g t + deriv g t / (1 - g t) =
        deriv g t / (g t * (1 - g t)) := by
      field_simp [hg_ne t htI, hone_ne t htI]
      <;> ring
    rw [hid]
    linarith
  have hGanti : AntitoneOn G (Set.Icc p₀ p₁) :=
    antitoneOn_of_deriv_nonpos (convex_Icc p₀ p₁) hGdiff.continuousOn
      (hGdiff.mono interior_subset) hGderiv
  have hp₀mem : p₀ ∈ Set.Icc p₀ p₁ := ⟨le_rfl, hp⟩
  have hp₁mem : p₁ ∈ Set.Icc p₀ p₁ := ⟨hp, le_rfl⟩
  have hends : G p₁ ≤ G p₀ := hGanti hp₀mem hp₁mem hp
  have hlog₀ : Real.log (g p₀) ≤ 0 :=
    Real.log_nonpos (hg₀ p₀ hp₀mem).le (hg₁ p₀ hp₀mem).le
  have hlog₁ : Real.log (1 - g p₁) ≤ 0 :=
    Real.log_nonpos (sub_pos.mpr (hg₁ p₁ hp₁mem)).le (by linarith [hg₀ p₁ hp₁mem])
  have hlogprod : Real.log (g p₁ * (1 - g p₀)) ≤ -κ * (p₁ - p₀) := by
    rw [Real.log_mul (hg_ne p₁ hp₁mem) (hone_ne p₀ hp₀mem)]
    simp only [G, Pi.add_apply, Pi.sub_apply] at hends
    linarith
  have hprod : 0 < g p₁ * (1 - g p₀) :=
    mul_pos (hg₀ p₁ hp₁mem) (sub_pos.mpr (hg₁ p₀ hp₀mem))
  calc
    g p₁ * (1 - g p₀) = Real.exp (Real.log (g p₁ * (1 - g p₀))) :=
      (Real.exp_log hprod).symm
    _ ≤ Real.exp (-κ * (p₁ - p₀)) := Real.exp_le_exp.mpr hlogprod

@[blueprint "lem:sharp-threshold-amplification"
  (statement := /-- Let $\mathbb F$ be a finite field of cardinality $q$, let $n\in\mathbb N$, let $C\leq\mathbb F^n$, and let $p,\delta\in\mathbb R$ and $L\in\mathbb N$.  Suppose that $L\geq1$, $\delta>0$, $p<1$, $0\leq p-n^{-1/4}-\delta$, and $d_{\min}(C)\geq4q$.  Let $D^*$ be a sharp-threshold decoder for $C$ in the sense of \cref{def:is-sharp-threshold-decoder}: it is a deterministic symmetric nearest-neighbor decoder, its zero-codeword decoding region is downward monotone, and the minimum positive boundary of that region is at least $d_{\min}(C)/q-3$.  Suppose further that, for every $c\in C$, its success probability on $\mathrm{qSC}_{p-n^{-1/4}}$ is at least $1/(2L)$.  Then, for every $c\in C$, its success probability on $\mathrm{qSC}_{p-n^{-1/4}-\delta}$ is at least
  \[
    1-2L\exp\!\left(-\frac{1-p}{4}
      \frac{\sqrt{d_{\min}(C)}}{q^{3/2}}\delta\right).
  \] -/)
  (proof := /-- Put $p_1=p-n^{-1/4}$ and $p_0=p_1-\delta$, and let
  \[
    g(t)=\Pr_{z\sim\mathrm{qSC}_t}[D^*(z)=0].
  \]
  The hypotheses and the nonnegativity of $n^{-1/4}$ give
  $0\leq p_0<p_1<1$.  The zero-region indicator is Boolean by
  \cref{def:is-sharp-threshold-decoder}.  Hence
  \cref{lem:sharp-threshold-decoder-success-polynomial} and
  \cref{lem:qary-noise-expectation-boolean-bounds} imply
  $0\leq g(t)\leq1$ throughout $[p_0,p_1]$.  Moreover, the finite sum and
  finite products in \cref{def:qsc-success-probability,def:qsc-error-mass}
  show that every success probability is finite, so the baseline hypothesis
  gives $g(p_1)\geq1/(2L)>0$ after taking real values.

  Set
  \[
    A=\frac{\sqrt{d_{\min}(C)}}{q^{3/2}},
    \qquad \kappa=\frac{1-p}{4}A.
  \]
  First suppose that $p_0=0$.  If $D^*(0)$ assigns positive mass to a
  codeword $c$, its nearest-neighbor property, compared with the zero
  codeword, forces $d(0,c)=0$ and therefore $c=0$.  Since a probability mass
  function has nonempty support, $D^*(0)$ is the point mass at zero.
  Evaluating \cref{def:qary-noise-expectation} at parameter zero and using
  \cref{lem:sharp-threshold-decoder-success-polynomial} therefore gives
  $g(p_0)=1$.  The quantity in
  \cref{def:sharp-threshold-lower-bound} is at most $1$, so the conclusion
  follows in this case.

  Now suppose that $p_0>0$.  For every $t\in[p_0,p_1]$,
  \cref{lem:maximum-likelihood-success-derivative} makes $g$
  differentiable at $t$ and gives
  \[
    g'(t)\leq-\frac{1-t}{4}A\,g(t)(1-g(t))
      \leq-\kappa g(t)(1-g(t)),
  \]
  because $t\leq p_1\leq p$ and $g(t)(1-g(t))\geq0$.  In particular,
  $g$ is nonincreasing on $[p_0,p_1]$.  If $g$ equals $1$ anywhere on this
  interval, antitonicity gives $g(p_0)=1$, and the conclusion again follows.
  Otherwise, antitonicity and the positive baseline give
  $0<g(t)<1$ throughout the interval.  Applying
  \cref{lem:logistic-threshold-integration} yields
  \[
    g(p_1)(1-g(p_0))\leq
      \exp\!\left(-\kappa(p_1-p_0)\right)
      =\exp\!\left(-\frac{1-p}{4}
        \frac{\sqrt{d_{\min}(C)}}{q^{3/2}}\delta\right).
  \]
  Combining this with $g(p_1)\geq1/(2L)$ gives precisely the lower bound in
  \cref{def:sharp-threshold-lower-bound}.  Finally, the symmetry clause of
  \cref{def:is-sharp-threshold-decoder} transfers the zero-codeword estimate
  to every transmitted codeword, and the real inequality converts to the
  asserted extended-nonnegative-real inequality. -/)
  (title := /-- Sharp-threshold amplification for symmetric maximum-likelihood decoding -/)
  (latexEnv := "lemma")]
lemma sharp_threshold_amplification
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (C : qary_linear_code 𝔽 n) {p δ : ℝ} {L : ℕ}
    (Dstar : qary_decoder C)
    (hnoise : 0 ≤ p - sampling_slack n - δ) (hp : p < 1)
    (hδ : 0 < δ) (hL : 0 < L)
    (hdist : 4 * Fintype.card 𝔽 ≤ linear_code_minimum_distance C)
    (hML : is_sharp_threshold_decoder C Dstar)
    (hbase : ∀ c : C,
      ENNReal.ofReal (1 / (2 * (L : ℝ))) ≤
        qsc_success_probability C Dstar (p - sampling_slack n) c) :
    ∀ c : C,
      ENNReal.ofReal
        (sharp_threshold_lower_bound (Fintype.card 𝔽)
          (linear_code_minimum_distance C) L p δ) ≤
        qsc_success_probability C Dstar (p - sampling_slack n - δ) c := by
  classical
  let p₁ : ℝ := p - sampling_slack n
  let p₀ : ℝ := p₁ - δ
  let g : ℝ → ℝ :=
    fun t => (qsc_success_probability C Dstar t 0).toReal
  let f := qary_decoding_region_indicator C Dstar
  have hslack : 0 ≤ sampling_slack n := by
    unfold sampling_slack
    exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hp₀ : 0 ≤ p₀ := by
    dsimp [p₀, p₁]
    exact hnoise
  have hp₀₁ : p₀ < p₁ := by
    dsimp [p₀]
    linarith
  have hp₁pos : 0 < p₁ := lt_of_le_of_lt hp₀ hp₀₁
  have hp₁lt : p₁ < 1 := by
    dsimp [p₁]
    linarith
  have hf01 : ∀ z, f z = 0 ∨ f z = 1 := by
    intro z
    rcases hML.2.1 z 0 with h | h
    · left
      simp [f, qary_decoding_region_indicator, h]
    · right
      simp [f, qary_decoding_region_indicator, h]
  have hg_bounds (t : ℝ) (ht : t ∈ Set.Icc p₀ p₁) :
      0 ≤ g t ∧ g t ≤ 1 := by
    have ht1 : t ≤ 1 := ht.2.trans hp₁lt.le
    have hbounds :=
      qary_noise_expectation_boolean_bounds f hf01 (hp₀.trans ht.1) ht1
    have hpoly :=
      sharp_threshold_decoder_success_polynomial C Dstar hML
        (hp₀.trans ht.1) ht1
    rw [hpoly] at hbounds
    exact hbounds
  have hfinite (t : ℝ) :
      qsc_success_probability C Dstar t 0 ≠ ⊤ := by
    unfold qsc_success_probability
    apply (ENNReal.sum_ne_top).2
    intro z hz
    apply ENNReal.mul_ne_top
    · unfold qsc_error_mass
      apply ENNReal.prod_ne_top
      intro i hi
      split_ifs <;> exact ENNReal.ofReal_ne_top
    · exact PMF.apply_ne_top _ _
  have hbase_real : 1 / (2 * (L : ℝ)) ≤ g p₁ := by
    have h := (ENNReal.ofReal_le_iff_le_toReal (hfinite p₁)).1 (hbase 0)
    exact h
  have hLreal : (0 : ℝ) < L := by
    exact_mod_cast hL
  have hbase_pos : 0 < g p₁ := by
    have : 0 < 1 / (2 * (L : ℝ)) := by positivity
    exact this.trans_le hbase_real
  let A : ℝ :=
    Real.sqrt (linear_code_minimum_distance C : ℝ) /
      Real.rpow (Fintype.card 𝔽 : ℝ) (3 / 2 : ℝ)
  let κ : ℝ := (1 - p) / 4 * A
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hκ : 0 ≤ κ := by
    dsimp [κ]
    positivity
  have hbound_le_one :
      sharp_threshold_lower_bound (Fintype.card 𝔽)
          (linear_code_minimum_distance C) L p δ ≤ 1 := by
    unfold sharp_threshold_lower_bound
    have : 0 ≤ 2 * (L : ℝ) *
        Real.exp (-((1 - p) / 4) *
          (Real.sqrt (linear_code_minimum_distance C : ℝ) /
            Real.rpow (Fintype.card 𝔽 : ℝ) (3 / 2 : ℝ)) * δ) := by
      positivity
    linarith
  have hzero_success :
      qsc_success_probability C Dstar 0 0 = 1 := by
    have hsupp_sub : (Dstar 0).support ⊆ ({0} : Set C) := by
      intro c hc
      have hdist := hML.1.1 0 c hc 0
      have hdist0 : hammingDist (0 : Fin n → 𝔽) (c : Fin n → 𝔽) = 0 := by
        have : hammingDist (0 : Fin n → 𝔽) (c : Fin n → 𝔽) ≤ 0 := by
          simpa using hdist
        exact Nat.eq_zero_of_le_zero this
      have hdist0' : hammingDist (c : Fin n → 𝔽) 0 = 0 := by
        simpa [hammingDist_comm] using hdist0
      have hc0 : (c : Fin n → 𝔽) = 0 := hammingDist_eq_zero.mp hdist0'
      exact Set.mem_singleton_iff.mpr (Subtype.ext hc0)
    have hsupp_eq : (Dstar 0).support = ({0} : Set C) := by
      apply Set.Subset.antisymm hsupp_sub
      intro c hc
      have hc0 : c = 0 := Set.mem_singleton_iff.mp hc
      subst c
      rcases (Dstar 0).support_nonempty with ⟨d, hd⟩
      have hd0 : d = 0 := Set.mem_singleton_iff.mp (hsupp_sub hd)
      simpa [hd0] using hd
    have hdecode : Dstar 0 0 = 1 :=
      (PMF.apply_eq_one_iff (Dstar 0) 0).2 hsupp_eq
    have hE0 : qary_noise_expectation 0 f = f 0 := by
      unfold qary_noise_expectation
      rw [Finset.sum_eq_single 0]
      · simp
      · intro z hz hz0
        have hcoord : ∃ i, z i ≠ 0 := by
          by_contra h
          push Not at h
          apply hz0
          funext i
          exact h i
        rcases hcoord with ⟨i, hi⟩
        apply mul_eq_zero_of_left
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hi]
      · simp
    have hpoly :=
      sharp_threshold_decoder_success_polynomial C Dstar hML
        (show (0 : ℝ) ≤ 0 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)
    apply (ENNReal.toReal_eq_one_iff _).1
    rw [← hpoly, hE0]
    simp [f, qary_decoding_region_indicator, hdecode]
  have hreal :
      sharp_threshold_lower_bound (Fintype.card 𝔽)
          (linear_code_minimum_distance C) L p δ ≤ g p₀ := by
    rcases hp₀.eq_or_lt with hp₀eq | hp₀pos
    · have hg0 : g p₀ = 1 := by
        dsimp [g]
        rw [← hp₀eq, hzero_success]
        exact ENNReal.toReal_one
      rw [hg0]
      exact hbound_le_one
    · have hgdiff : DifferentiableOn ℝ g (Set.Icc p₀ p₁) := by
        intro t ht
        have htpos : 0 < t := hp₀pos.trans_le ht.1
        have htlt : t < 1 := ht.2.trans_lt hp₁lt
        exact
          (maximum_likelihood_success_derivative C Dstar hML hdist
            htpos htlt).1.differentiableWithinAt
      have hderiv (t : ℝ) (ht : t ∈ Set.Icc p₀ p₁) :
          deriv g t ≤ -κ * g t * (1 - g t) := by
        have htpos : 0 < t := hp₀pos.trans_le ht.1
        have htlt : t < 1 := ht.2.trans_lt hp₁lt
        have hd :=
          (maximum_likelihood_success_derivative C Dstar hML hdist
            htpos htlt).2
        have hprod : 0 ≤ g t * (1 - g t) := by
          have hb := hg_bounds t ht
          exact mul_nonneg hb.1 (sub_nonneg.mpr hb.2)
        have hcoeff : κ ≤ (1 - t) / 4 * A := by
          dsimp [κ]
          have ht_p : t ≤ p := by
            calc
              t ≤ p₁ := ht.2
              _ ≤ p := by
                dsimp [p₁]
                linarith
          exact mul_le_mul_of_nonneg_right (by linarith) hA
        calc
          deriv g t ≤ -((1 - t) / 4) * A * g t * (1 - g t) := by
            simpa [g, A] using hd
          _ ≤ -κ * g t * (1 - g t) := by nlinarith
      have hanti : AntitoneOn g (Set.Icc p₀ p₁) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc p₀ p₁)
          hgdiff.continuousOn (hgdiff.mono interior_subset)
        intro t ht
        have htI : t ∈ Set.Icc p₀ p₁ := interior_subset ht
        have hp := (hg_bounds t htI)
        have hprod : 0 ≤ g t * (1 - g t) :=
          mul_nonneg hp.1 (sub_nonneg.mpr hp.2)
        exact (hderiv t htI).trans (by nlinarith)
      by_cases hone : ∃ t ∈ Set.Icc p₀ p₁, g t = 1
      · rcases hone with ⟨t, ht, htone⟩
        have hge : 1 ≤ g p₀ := by
          rw [← htone]
          exact hanti ⟨le_rfl, hp₀₁.le⟩ ht ht.1
        have hle := (hg_bounds p₀ ⟨le_rfl, hp₀₁.le⟩).2
        have hg0 : g p₀ = 1 := le_antisymm hle hge
        rw [hg0]
        exact hbound_le_one
      · have hgpos : ∀ t ∈ Set.Icc p₀ p₁, 0 < g t := by
          intro t ht
          exact hbase_pos.trans_le
            (hanti ht ⟨hp₀₁.le, le_rfl⟩ ht.2)
        have hglt : ∀ t ∈ Set.Icc p₀ p₁, g t < 1 := by
          intro t ht
          exact lt_of_le_of_ne (hg_bounds t ht).2 (fun h => hone ⟨t, ht, h⟩)
        have hlogistic :=
          logistic_threshold_integration g hp₀₁.le hκ hgdiff hgpos hglt hderiv
        have hgap_nonneg : 0 ≤ 1 - g p₀ :=
          sub_nonneg.mpr (hg_bounds p₀ ⟨le_rfl, hp₀₁.le⟩).2
        have hscaled :
            (1 / (2 * (L : ℝ))) * (1 - g p₀) ≤
              Real.exp (-κ * (p₁ - p₀)) := by
          exact (mul_le_mul_of_nonneg_right hbase_real hgap_nonneg).trans hlogistic
        have hscaled_target :
            (1 / (2 * (L : ℝ))) * (1 - g p₀) ≤
              Real.exp (-((1 - p) / 4) *
                (Real.sqrt (linear_code_minimum_distance C : ℝ) /
                  Real.rpow (Fintype.card 𝔽 : ℝ) (3 / 2 : ℝ)) * δ) := by
          simpa [κ, A, p₀, p₁, mul_assoc] using hscaled
        have htwoL : 0 < 2 * (L : ℝ) := by positivity
        have hdiv :
            (1 - g p₀) / (2 * (L : ℝ)) ≤
              Real.exp (-((1 - p) / 4) *
                (Real.sqrt (linear_code_minimum_distance C : ℝ) /
                  Real.rpow (Fintype.card 𝔽 : ℝ) (3 / 2 : ℝ)) * δ) := by
          simpa [div_eq_mul_inv, mul_comm] using hscaled_target
        have hgap_le :=
          (div_le_iff₀ htwoL).1 hdiv
        unfold sharp_threshold_lower_bound
        nlinarith
  intro c
  rw [hML.1.2 (p - sampling_slack n - δ) c 0]
  apply ENNReal.ofReal_le_of_le_toReal
  change sharp_threshold_lower_bound (Fintype.card 𝔽)
      (linear_code_minimum_distance C) L p δ ≤ g p₀
  exact hreal

@[blueprint "lem:quantitative-list-decoding-to-qsc"
  (statement := /-- Let $\mathbb F$ be a finite field of cardinality $q$, let $n\geq1$, and let $C\leq\mathbb F^n$ be a linear $(p,L)$-list-decodable code with $L\geq1$ and $d_{\min}(C)\geq4q$.  Let $\delta>0$ and suppose that $n^{-1/4}\leq p<1$, $0\leq p-n^{-1/4}-\delta$, and $p-n^{-1/4}\leq1-1/q$.  Then there exists a randomized decoder $D^*$ satisfying, for every $c\in C$,
  \[
    \Pr_{z\sim\mathrm{qSC}_{p-n^{-1/4}-\delta}}
      [D^*(c+z)=c]
    \geq1-2L\exp\!\left(-\frac{1-p}{4}
      \frac{\sqrt{d_{\min}(C)}}{q^{3/2}}\delta\right).
  \] -/)
  (proof := /-- By \cref{lem:random-list-decoder-baseline}, the random-list decoder has success probability at least $1/(2L)$ at parameter $p-n^{-1/4}$.  The nonnegativity hypotheses imply $0\leq p-n^{-1/4}$, and the assumed upper bound places this parameter in the nearest-neighbor maximum-likelihood regime.  Thus \cref{lem:sharp-threshold-maximum-likelihood-baseline} replaces the random-list decoder by a deterministic, translation-symmetric nearest-neighbor decoder with a downward-monotone zero decoding region, without decreasing its success probability.  The remaining minimum-distance and channel hypotheses permit \cref{lem:sharp-threshold-amplification}, which gives the displayed success probability at parameter $p-n^{-1/4}-\delta$. -/)
  (title := /-- A list-decodable code communicates reliably below its list-decoding radius -/)
  (latexEnv := "lemma")]
lemma quantitative_list_decoding_to_qsc
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (hn : 0 < n) (C : qary_linear_code 𝔽 n)
    {p δ : ℝ} {L : ℕ}
    (hslack : sampling_slack n ≤ p) (hnoise : 0 ≤ p - sampling_slack n - δ)
    (hMLrange : p - sampling_slack n ≤
      1 - 1 / (Fintype.card 𝔽 : ℝ))
    (hp : p < 1) (hδ : 0 < δ) (hL : 0 < L)
    (hlist : list_decodable C p L)
    (hdist : 4 * Fintype.card 𝔽 ≤ linear_code_minimum_distance C) :
    ∃ Dstar : qary_decoder C, ∀ c : C,
      ENNReal.ofReal
        (sharp_threshold_lower_bound (Fintype.card 𝔽)
          (linear_code_minimum_distance C) L p δ) ≤
        qsc_success_probability C Dstar (p - sampling_slack n - δ) c := by
  obtain ⟨D, hD⟩ := random_list_decoder_baseline hn C hslack hL hlist
  have hr₀ : 0 ≤ p - sampling_slack n := sub_nonneg.mpr hslack
  have hslack_nonneg : 0 ≤ sampling_slack n := by
    unfold sampling_slack
    exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hr₁ : p - sampling_slack n < 1 := by linarith
  obtain ⟨Dstar, hsharp, hbase⟩ :=
    sharp_threshold_maximum_likelihood_baseline C hr₀ hr₁ hMLrange D hD
  exact ⟨Dstar,
    sharp_threshold_amplification C Dstar hnoise hp hδ hL hdist hsharp hbase⟩

@[blueprint "lem:capacity-bridge-asymptotic-passage"
  (statement := /-- Let $p\in(0,1)$ and let $(C_n)_{n\geq0}$ be a family of linear codes over a finite field of cardinality $q$.  If the family achieves list-decoding capacity at corruption fraction $p$ and
  \[
    d_{\min}(C_n)=\omega\!\left(\frac{q^3}{(1-p)^2}\right),
  \]
  then the family achieves capacity on $\mathrm{qSC}_p$. -/)
  (proof := /-- Write $q=|\mathbb F|$ and $\rho=1-1/q$.  The positivity of $q^3/(1-p)^2$ and \cref{def:minimum-distance-growth} imply that $d_{\min}(C_n)\to\infty$.  First suppose that $p\leq\rho$, and put $a=(1-p)/(8q^{3/2})$.  For each $k\geq1$, the distance divergence eventually gives both $d_{\min}(C_n)\geq4q$ and
  \[
    2k\exp\!\left(-a\frac{\sqrt{d_{\min}(C_n)}}k\right)\leq\frac1k.
  \]
  Let $K_n$ be the largest $k\leq n$ satisfying these two inequalities, with $k=0$ admitted unconditionally.  The preceding eventual assertion for every fixed $k$ shows that $K_n\to\infty$.  Apply \cref{def:achieves-list-decoding-capacity} to $L_n=K_n$, obtaining $\eta_n\to0$ and eventual list decodability at radius $p-\eta_n$.  Since $|\eta_n|\geq\eta_n$, \cref{def:list-decodable} also gives list decodability at the smaller radius $p-|\eta_n|$.

  Define
  \[
    \varepsilon_n=|\eta_n|+n^{-1/4}+K_n^{-1}.
  \]
  By \cref{def:sampling-slack}, this sequence is nonnegative and tends to zero.  Eventually it is at most $p$, the parameter $p-|\eta_n|-n^{-1/4}$ lies in $[0,\rho]$, and all hypotheses of \cref{lem:quantitative-list-decoding-to-qsc} hold with base radius $p-|\eta_n|$, list size $K_n$, and additional slack $K_n^{-1}$.  Its exponential error is at most the displayed bound, hence at most $K_n^{-1}\leq\varepsilon_n$.  Choosing the resulting decoders gives the reliability clause of \cref{def:achieves-qsc-capacity}; its rate clause is exactly the rate clause already supplied by \cref{def:achieves-list-decoding-capacity}.

  Finally, suppose $p>\rho$.  Applying $\log t\leq t-1$, strictly to $(1/q)/(1-p)$, proves directly from \cref{def:qary-entropy} that $1-h_q(p)>0$.  The rate clause in \cref{def:achieves-list-decoding-capacity} then implies $|C_n|\to\infty$.  Set $L_n=\lfloor\sqrt{|C_n|}\rfloor$; then $L_n\to\infty$, so the list-decoding clause supplies $\eta_n\to0$.  For all sufficiently large $n$, the resulting code is list-decodable at the smaller radius
  \[
    r_n=\rho+n^{-1/4}.
  \]
  By \cref{lem:random-list-decoder-baseline-good-error-mass}, the Hamming ball of radius $r_n n$ has mass at least $1/2$ under $\mathrm{qSC}_\rho$.  The definition \cref{def:qsc-error-mass} makes this channel uniform on $\mathbb F^n$, so this ball contains at least $q^n/2$ words.  Translation preserves its cardinality.  Double-counting the pairs $(y,c)$ with $d(y,c)\leq r_n n$, and using \cref{def:list-decodable} for the upper bound at each center $y$, yields
  \[
    |C_n|\,|B_n|\leq q^nL_n,\qquad |B_n|\geq q^n/2,
  \]
  and hence $|C_n|\leq2L_n$.  This contradicts $L_n=\lfloor\sqrt{|C_n|}\rfloor$ once $|C_n|\geq9$.  Therefore $p\leq\rho$, and the first case proves the result. -/)
  (title := /-- Asymptotic passage from the quantitative estimate to capacity -/)
  (latexEnv := "lemma")]
lemma capacity_bridge_asymptotic_passage
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (C : qary_code_family 𝔽) (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1)
    (hlist : achieves_list_decoding_capacity C p)
    (hdist : minimum_distance_growth C p) :
    achieves_qsc_capacity C p := by
  have hA : 0 < (Fintype.card 𝔽 : ℝ) ^ 3 / (1 - p) ^ 2 := by
    positivity
  have hdtop : Filter.Tendsto
      (fun n => (linear_code_minimum_distance (C n) : ℝ))
      Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    let M := max b 1
    have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right b 1)
    have he := (Asymptotics.isLittleO_iff.mp hdist) (div_pos hA hM)
    filter_upwards [he] with n hn
    rw [Real.norm_eq_abs, abs_of_pos hA, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ (linear_code_minimum_distance (C n) : ℝ) by positivity)] at hn
    have hmul :
        ((Fintype.card 𝔽 : ℝ) ^ 3 / (1 - p) ^ 2) * M ≤
          ((Fintype.card 𝔽 : ℝ) ^ 3 / (1 - p) ^ 2) *
            (linear_code_minimum_distance (C n) : ℝ) := by
      calc
        _ ≤ (((Fintype.card 𝔽 : ℝ) ^ 3 / (1 - p) ^ 2 / M) *
              (linear_code_minimum_distance (C n) : ℝ)) * M :=
          mul_le_mul_of_nonneg_right hn (le_of_lt hM)
        _ = _ := by field_simp
    have hMd : M ≤ (linear_code_minimum_distance (C n) : ℝ) := by
      nlinarith
    exact le_trans (le_max_left b 1) hMd
  unfold achieves_qsc_capacity
  refine ⟨hlist.1, ?_⟩
  by_cases hpq : p ≤ 1 - 1 / (Fintype.card 𝔽 : ℝ)
  · let a : ℝ := (1 - p) / 8 /
        Real.rpow (Fintype.card 𝔽 : ℝ) (3 / 2 : ℝ)
    have ha : 0 < a := by
      dsimp [a]
      positivity
    let Good : ℕ → ℕ → Prop := fun k n =>
      k = 0 ∨
        0 < k ∧
          4 * Fintype.card 𝔽 ≤ linear_code_minimum_distance (C n) ∧
            2 * (k : ℝ) *
                Real.exp (-a * Real.sqrt
                  (linear_code_minimum_distance (C n) : ℝ) / (k : ℝ)) ≤
              1 / (k : ℝ)
    have hgood : ∀ k, ∀ᶠ n in Filter.atTop, Good k n := by
      intro k
      by_cases hk : k = 0
      · exact Filter.Eventually.of_forall fun _ => Or.inl hk
      · have hkpos : 0 < (k : ℝ) := by positivity
        have hsqrt : Filter.Tendsto
            (fun n => Real.sqrt (linear_code_minimum_distance (C n) : ℝ))
            Filter.atTop Filter.atTop :=
          Real.tendsto_sqrt_atTop.comp hdtop
        have hscaled : Filter.Tendsto
            (fun n => a / (k : ℝ) *
              Real.sqrt (linear_code_minimum_distance (C n) : ℝ))
            Filter.atTop Filter.atTop :=
          hsqrt.const_mul_atTop (div_pos ha hkpos)
        have hnegative : Filter.Tendsto
            (fun n => -(a / (k : ℝ) *
              Real.sqrt (linear_code_minimum_distance (C n) : ℝ)))
            Filter.atTop Filter.atBot :=
          Filter.tendsto_neg_atTop_atBot.comp hscaled
        have hexp : Filter.Tendsto
            (fun n => Real.exp (-(a / (k : ℝ) *
              Real.sqrt (linear_code_minimum_distance (C n) : ℝ))))
            Filter.atTop (nhds 0) :=
          Real.tendsto_exp_atBot.comp hnegative
        have herr : Filter.Tendsto
            (fun n => 2 * (k : ℝ) *
              Real.exp (-a * Real.sqrt
                (linear_code_minimum_distance (C n) : ℝ) / (k : ℝ)))
            Filter.atTop (nhds 0) := by
          convert (tendsto_const_nhds.mul hexp) using 1
          · funext n
            congr 2
            field_simp
          · simp
        have herrsmall : ∀ᶠ n in Filter.atTop,
            2 * (k : ℝ) *
                Real.exp (-a * Real.sqrt
                  (linear_code_minimum_distance (C n) : ℝ) / (k : ℝ)) ≤
              1 / (k : ℝ) := by
          filter_upwards [herr.eventually_lt tendsto_const_nhds
            (show (0 : ℝ) < 1 / (k : ℝ) by positivity)] with n hn
          exact le_of_lt hn
        have hlarge : ∀ᶠ n in Filter.atTop,
            4 * Fintype.card 𝔽 ≤ linear_code_minimum_distance (C n) := by
          have hlarge' := (Filter.tendsto_atTop.1 hdtop
            (4 * Fintype.card 𝔽 : ℝ))
          filter_upwards [hlarge'] with n hn
          exact_mod_cast hn
        filter_upwards [herrsmall, hlarge] with n hnerr hnd
        exact Or.inr ⟨Nat.pos_of_ne_zero hk, hnd, hnerr⟩
    let K : ℕ → ℕ := fun n => Nat.findGreatest (fun k => Good k n) n
    have hKgood : ∀ n, Good (K n) n := by
      intro n
      exact Nat.findGreatest_spec (P := fun k => Good k n)
        (Nat.zero_le n) (show Good 0 n from Or.inl rfl)
    have hKtop : Filter.Tendsto K Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop]
      intro k
      filter_upwards [hgood k, Filter.eventually_ge_atTop k] with n hkn hle
      exact Nat.le_findGreatest hle hkn
    have hKpos : ∀ᶠ n in Filter.atTop, 0 < K n :=
      hKtop.eventually_gt_atTop 0
    obtain ⟨ε₀, hε₀, hlist₀⟩ := hlist.2 K hKtop
    have hlistabs : ∀ᶠ n in Filter.atTop,
        list_decodable (C n) (p - |ε₀ n|) (K n) := by
      filter_upwards [hlist₀] with n hn
      unfold list_decodable at hn ⊢
      intro y
      refine le_trans (Finset.card_le_card ?_) (hn y)
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      refine le_trans hc (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg n))
      linarith [le_abs_self (ε₀ n)]
    have hKinv : Filter.Tendsto (fun n => (K n : ℝ)⁻¹)
        Filter.atTop (nhds 0) :=
      (tendsto_natCast_atTop_iff.mpr hKtop).inv_tendsto_atTop
    have hsamp : Filter.Tendsto sampling_slack Filter.atTop (nhds 0) := by
      unfold sampling_slack
      exact (tendsto_rpow_neg_atTop
        (show (0 : ℝ) < 1 / 4 by norm_num)).comp
          tendsto_natCast_atTop_atTop
    let ε : ℕ → ℝ := fun n =>
      |ε₀ n| + sampling_slack n + (K n : ℝ)⁻¹
    have hε : Filter.Tendsto ε Filter.atTop (nhds 0) := by
      dsimp [ε]
      simpa using (hε₀.abs.add hsamp).add hKinv
    have hεle : ∀ᶠ n in Filter.atTop, ε n ≤ p := by
      filter_upwards [hε.eventually_lt tendsto_const_nhds hp₀] with n hn
      exact le_of_lt hn
    have hε₀small : ∀ᶠ n in Filter.atTop, |ε₀ n| ≤ (1 - p) / 2 := by
      have hpos : 0 < (1 - p) / 2 := by linarith
      have habspos : |(0 : ℝ)| < (1 - p) / 2 := by simpa using hpos
      filter_upwards [hε₀.abs.eventually_lt tendsto_const_nhds habspos] with n hn
      exact le_of_lt hn
    let Q : (n : ℕ) → qary_decoder (C n) → Prop := fun n D =>
      ∀ c : C n, ENNReal.ofReal (1 - ε n) ≤
        qsc_success_probability (C n) D (p - ε n) c
    have hQ : ∀ᶠ n in Filter.atTop, ∃ D, Q n D := by
      filter_upwards [hKpos, hlistabs, hεle, hε₀small,
        Filter.eventually_gt_atTop (0 : ℕ)] with n hkn hln hsn hεnsmall hn
      have hgn := hKgood n
      rcases hgn with hkzero | ⟨_, hdn, herrn⟩
      · exact (Nat.ne_of_gt hkn hkzero).elim
      have hsampnonneg : 0 ≤ sampling_slack n := by
        unfold sampling_slack
        exact Real.rpow_nonneg (Nat.cast_nonneg n) _
      have hinvpos : 0 < (K n : ℝ)⁻¹ := by positivity
      have hnoise : 0 ≤ (p - |ε₀ n|) - sampling_slack n - (K n : ℝ)⁻¹ := by
        dsimp [ε] at hsn
        linarith
      have hslack : sampling_slack n ≤ p - |ε₀ n| := by
        linarith
      have hML : p - |ε₀ n| - sampling_slack n ≤
          1 - 1 / (Fintype.card 𝔽 : ℝ) := by
        linarith [abs_nonneg (ε₀ n)]
      have hpbase : p - |ε₀ n| < 1 := by
        linarith [abs_nonneg (ε₀ n)]
      obtain ⟨D, hD⟩ := quantitative_list_decoding_to_qsc
        hn (C n) hslack hnoise hML hpbase hinvpos hkn hln hdn
      refine ⟨D, ?_⟩
      intro c
      have hqpow : 0 <
          Real.rpow (Fintype.card 𝔽 : ℝ) (3 / 2 : ℝ) := by
        exact Real.rpow_pos_of_pos (by positivity) _
      have hcoef : a ≤
          (1 - (p - |ε₀ n|)) / 4 /
            Real.rpow (Fintype.card 𝔽 : ℝ) (3 / 2 : ℝ) := by
        dsimp [a]
        apply div_le_div_of_nonneg_right _ (le_of_lt hqpow)
        linarith [abs_nonneg (ε₀ n)]
      have hsqrtnonneg : 0 ≤
          Real.sqrt (linear_code_minimum_distance (C n) : ℝ) :=
        Real.sqrt_nonneg _
      have hexponent :
          -((1 - (p - |ε₀ n|)) / 4) *
                (Real.sqrt (linear_code_minimum_distance (C n) : ℝ) /
                  Real.rpow (Fintype.card 𝔽 : ℝ) (3 / 2 : ℝ)) *
                (K n : ℝ)⁻¹ ≤
            -a * Real.sqrt (linear_code_minimum_distance (C n) : ℝ) /
              (K n : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef hsqrtnonneg)
          (le_of_lt hinvpos)
        simpa only [div_eq_mul_inv, neg_mul, mul_assoc, mul_left_comm, mul_comm]
          using neg_le_neg hmul
      have herrcompare :
          2 * (K n : ℝ) *
              Real.exp
                (-((1 - (p - |ε₀ n|)) / 4) *
                  (Real.sqrt (linear_code_minimum_distance (C n) : ℝ) /
                    Real.rpow (Fintype.card 𝔽 : ℝ) (3 / 2 : ℝ)) *
                  (K n : ℝ)⁻¹) ≤
            2 * (K n : ℝ) *
              Real.exp (-a *
                Real.sqrt (linear_code_minimum_distance (C n) : ℝ) /
                (K n : ℝ)) := by
        gcongr
      have hreal : 1 - ε n ≤
          sharp_threshold_lower_bound (Fintype.card 𝔽)
            (linear_code_minimum_distance (C n)) (K n)
            (p - |ε₀ n|) (K n : ℝ)⁻¹ := by
        unfold sharp_threshold_lower_bound
        dsimp [ε]
        have herrn' :
            2 * (K n : ℝ) *
                Real.exp (-a * Real.sqrt
                  (linear_code_minimum_distance (C n) : ℝ) / (K n : ℝ)) ≤
              (K n : ℝ)⁻¹ := by
          simpa only [one_div] using herrn
        apply sub_le_sub_left
        exact (herrcompare.trans herrn').trans (by
          nlinarith [abs_nonneg (ε₀ n), hsampnonneg, le_of_lt hinvpos])
      refine le_trans (ENNReal.ofReal_le_ofReal hreal) ?_
      have hchannel :
          p - ε n = p - |ε₀ n| - sampling_slack n - (K n : ℝ)⁻¹ := by
        dsimp [ε]
        ring
      rw [hchannel]
      exact hD c
    rw [Filter.eventually_atTop] at hQ
    obtain ⟨N, hN⟩ := hQ
    let D : (n : ℕ) → qary_decoder (C n) := fun n =>
      if hn : N ≤ n then Classical.choose (hN n hn)
      else fun _ => ⟨fun c => if c = 0 then 1 else 0, hasSum_ite_eq _ _⟩
    refine ⟨ε, D, hε, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop N, hεle, hKpos] with n hn hsn hkn
    have hQn : Q n (D n) := by
      dsimp [D]
      rw [dif_pos hn]
      exact Classical.choose_spec (hN n hn)
    refine ⟨?_, hsn, hQn⟩
    dsimp [ε]
    exact add_nonneg
      (add_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      (inv_nonneg.mpr (Nat.cast_nonneg _))
  · push Not at hpq
    exfalso
    let q : ℝ := Fintype.card 𝔽
    have hq : 1 < q := by
      dsimp [q]
      exact_mod_cast Fintype.one_lt_card (α := 𝔽)
    have hqpos : 0 < q := lt_trans zero_lt_one hq
    have hqm1 : 0 < q - 1 := by linarith
    have hp : 0 < p := hp₀
    have h1p : 0 < 1 - p := by linarith
    let x : ℝ := (1 / q) / (1 - p)
    let y : ℝ := ((q - 1) / q) / p
    have hx : 0 < x := by
      dsimp [x]
      positivity
    have hy : 0 < y := by
      dsimp [y]
      positivity
    have hxne : x ≠ 1 := by
      intro heq
      have hpEq : p = 1 - 1 / q := by
        dsimp [x] at heq
        field_simp [ne_of_gt hqpos, ne_of_gt h1p] at heq ⊢
        nlinarith
      rw [hpEq] at hpq
      exact lt_irrefl _ hpq
    have hxlog := Real.log_lt_sub_one_of_pos hx hxne
    have hylog := Real.log_le_sub_one_of_pos hy
    have hkl : 0 < -(1 - p) * Real.log x - p * Real.log y := by
      have hxmul := mul_lt_mul_of_pos_left hxlog h1p
      have hymul := mul_le_mul_of_nonneg_left hylog (le_of_lt hp)
      have hsum : -(1 - p) * (x - 1) - p * (y - 1) = 0 := by
        dsimp [x, y]
        field_simp [ne_of_gt hqpos, ne_of_gt hp, ne_of_gt h1p]
        ring
      rw [← hsum]
      nlinarith
    have hcardsub : ((Fintype.card 𝔽 - 1 : ℕ) : ℝ) = q - 1 := by
      rw [Nat.cast_sub (le_of_lt (Fintype.one_lt_card (α := 𝔽)))]
      dsimp [q]
      norm_num
    have hidentity : -(1 - p) * Real.log x - p * Real.log y =
        Real.log q * (1 - qary_entropy (Fintype.card 𝔽) p) := by
      dsimp [x, y]
      unfold qary_entropy Real.logb
      rw [hcardsub]
      rw [Real.log_div (div_ne_zero one_ne_zero (ne_of_gt hqpos))
          (ne_of_gt h1p),
        Real.log_div one_ne_zero (ne_of_gt hqpos),
        Real.log_div (div_ne_zero (ne_of_gt hqm1) (ne_of_gt hqpos))
          (ne_of_gt hp),
        Real.log_div (ne_of_gt hqm1) (ne_of_gt hqpos),
        Real.log_div one_ne_zero (ne_of_gt h1p),
        Real.log_div (ne_of_gt hqm1) (ne_of_gt hp),
        Real.log_one]
      have hlogcard : 0 < Real.log (Fintype.card 𝔽 : ℝ) := by
        simpa [q] using Real.log_pos hq
      dsimp [q]
      field_simp [ne_of_gt hlogcard, ne_of_gt hqpos,
        ne_of_gt hqm1, ne_of_gt hp, ne_of_gt h1p]
      ring
    have hrate : 0 < 1 - qary_entropy (Fintype.card 𝔽) p := by
      rw [hidentity] at hkl
      nlinarith [Real.log_pos hq]
    let M : ℕ → ℕ := fun n => Nat.card (C n)
    have hMpos (n : ℕ) : 0 < M n := by
      dsimp [M]
      exact Nat.card_pos
    have hMtop : Filter.Tendsto M Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop]
      intro B
      have hrateevent : ∀ᶠ n in Filter.atTop,
          (1 - qary_entropy (Fintype.card 𝔽) p) / 2 <
            linear_code_rate (C n) :=
        tendsto_const_nhds.eventually_lt hlist.1 (by linarith)
      have hgrow : Filter.Tendsto
          (fun n : ℕ =>
            ((1 - qary_entropy (Fintype.card 𝔽) p) / 2) * (n : ℝ))
          Filter.atTop Filter.atTop :=
        tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
      have hBevent : ∀ᶠ n : ℕ in Filter.atTop,
          Real.logb q (B : ℝ) <
            ((1 - qary_entropy (Fintype.card 𝔽) p) / 2) * (n : ℝ) :=
        hgrow.eventually_gt_atTop _
      filter_upwards [hrateevent, hBevent,
        Filter.eventually_gt_atTop (0 : ℕ)] with n hrn hBn hn
      by_contra hBM
      have hMB : M n < B := Nat.lt_of_not_ge hBM
      have hMreal : (0 : ℝ) < (M n : ℝ) := by exact_mod_cast hMpos n
      have hBreal : (M n : ℝ) < (B : ℝ) := by exact_mod_cast hMB
      have hlog : Real.log (M n : ℝ) < Real.log (B : ℝ) :=
        Real.strictMonoOn_log hMreal (lt_trans hMreal hBreal) hBreal
      have hlogb : Real.logb q (M n : ℝ) < Real.logb q (B : ℝ) := by
        unfold Real.logb
        exact (div_lt_div_iff_of_pos_right (Real.log_pos hq)).mpr hlog
      have hrndef : linear_code_rate (C n) =
          Real.logb q (M n : ℝ) / (n : ℝ) := by
        letI : Fintype (C n) := Fintype.ofFinite (C n)
        unfold linear_code_rate
        dsimp [q, M]
        rw [Nat.card_eq_fintype_card]
      rw [hrndef] at hrn
      have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hrmul :
          ((1 - qary_entropy (Fintype.card 𝔽) p) / 2) * (n : ℝ) <
            Real.logb q (M n : ℝ) :=
        (lt_div_iff₀ hnreal).mp hrn
      linarith
    let L : ℕ → ℕ := fun n => Nat.sqrt (M n)
    have hLtop : Filter.Tendsto L Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop]
      intro b
      have hb := Filter.tendsto_atTop.1 hMtop (b * b)
      filter_upwards [hb] with n hn
      exact Nat.le_sqrt.mpr hn
    obtain ⟨ε₀, hε₀, hlist₀⟩ := hlist.2 L hLtop
    have hsamp' : Filter.Tendsto sampling_slack Filter.atTop (nhds 0) := by
      unfold sampling_slack
      exact (tendsto_rpow_neg_atTop
        (show (0 : ℝ) < 1 / 4 by norm_num)).comp
          tendsto_natCast_atTop_atTop
    have hsumzero : Filter.Tendsto (fun n => ε₀ n + sampling_slack n)
        Filter.atTop (nhds 0) := by
      simpa using hε₀.add hsamp'
    have hgap : 0 < p - (1 - 1 / q) := by
      linarith
    have hradius : ∀ᶠ n in Filter.atTop,
        1 - 1 / q + sampling_slack n ≤ p - ε₀ n := by
      filter_upwards [hsumzero.eventually_lt tendsto_const_nhds
        (show (0 : ℝ) < p - (1 - 1 / q) by exact hgap)] with n hn
      linarith
    have hlistR : ∀ᶠ n in Filter.atTop,
        list_decodable (C n) (1 - 1 / q + sampling_slack n) (L n) := by
      filter_upwards [hlist₀, hradius] with n hln hrn
      unfold list_decodable at hln ⊢
      intro w
      refine le_trans (Finset.card_le_card ?_) (hln w)
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact le_trans hc (mul_le_mul_of_nonneg_right hrn (Nat.cast_nonneg n))
    have hMlarge : ∀ᶠ n in Filter.atTop, 9 ≤ M n :=
      Filter.tendsto_atTop.1 hMtop 9
    have hevent : ∀ᶠ n in Filter.atTop,
        list_decodable (C n) (1 - 1 / q + sampling_slack n) (L n) ∧
          9 ≤ M n ∧ 0 < n :=
      hlistR.and (hMlarge.and (Filter.eventually_gt_atTop (0 : ℕ)))
    rw [Filter.eventually_atTop] at hevent
    obtain ⟨N, hN⟩ := hevent
    have ⟨hln, hmn, hn⟩ := hN N le_rfl
    letI : Fintype (C N) := Fintype.ofFinite (C N)
    let r : ℝ := 1 - 1 / q + sampling_slack N
    let Ball : Finset (Fin N → 𝔽) :=
      Finset.univ.filter fun z =>
        (hammingDist z 0 : ℝ) ≤ r * (N : ℝ)
    have hrslack : sampling_slack N ≤ r := by
      dsimp [r]
      have : 0 ≤ 1 - 1 / q := by
        have : 1 / q < 1 := (div_lt_one hqpos).mpr hq
        linarith
      linarith
    have hmass := random_list_decoder_baseline_good_error_mass
      (𝔽 := 𝔽) hn hrslack
    have hchannel : r - sampling_slack N = 1 - 1 / q := by
      dsimp [r]
      ring
    rw [hchannel] at hmass
    have huniform (z : Fin N → 𝔽) :
        qsc_error_mass (1 - 1 / q) z =
          (ENNReal.ofReal (1 / q)) ^ N := by
      unfold qsc_error_mass
      calc
        (∏ i : Fin N, if z i = 0 then ENNReal.ofReal (1 - (1 - 1 / q))
            else ENNReal.ofReal ((1 - 1 / q) /
              ((Fintype.card 𝔽 : ℝ) - 1))) =
            ∏ _i : Fin N, ENNReal.ofReal (1 / q) := by
          apply Finset.prod_congr rfl
          intro i hi
          split_ifs
          · congr 1
            ring
          · congr 1
            dsimp [q]
            have hcardpos : (0 : ℝ) < Fintype.card 𝔽 := by positivity
            have hcardm1 : (0 : ℝ) < (Fintype.card 𝔽 : ℝ) - 1 := by
              simpa [q] using hqm1
            field_simp [ne_of_gt hcardpos, ne_of_gt hcardm1]
        _ = _ := by simp
    have hmass' :
        ENNReal.ofReal (1 / 2) ≤
          (Ball.card : ENNReal) * (ENNReal.ofReal (1 / q)) ^ N := by
      simp_rw [huniform] at hmass
      rw [← Finset.sum_filter] at hmass
      simpa only [Ball, Finset.sum_const, nsmul_eq_mul] using hmass
    have hmassreal : (1 / 2 : ℝ) ≤
        (Ball.card : ℝ) * (1 / q) ^ N := by
      have ht := ENNReal.toReal_mono (by finiteness) hmass'
      simpa [ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal, le_of_lt hqpos] using ht
    have hqpowpos : 0 < q ^ N := pow_pos hqpos _
    have hballlarge : q ^ N / 2 ≤ (Ball.card : ℝ) := by
      have heq : (Ball.card : ℝ) * (1 / q) ^ N =
          (Ball.card : ℝ) / q ^ N := by
        rw [one_div, inv_pow, div_eq_mul_inv]
      rw [heq] at hmassreal
      have hh := (le_div_iff₀ hqpowpos).mp hmassreal
      nlinarith
    have htranslate (c : C N) :
        (∑ w : Fin N → 𝔽,
          if (hammingDist w (c : Fin N → 𝔽) : ℝ) ≤ r * (N : ℝ)
          then (1 : ℕ) else 0) = Ball.card := by
      calc
        _ = ∑ z : Fin N → 𝔽,
            if (hammingDist ((c : Fin N → 𝔽) + z)
                (c : Fin N → 𝔽) : ℝ) ≤ r * (N : ℝ)
            then (1 : ℕ) else 0 := by
          symm
          exact Equiv.sum_comp (Equiv.addLeft (c : Fin N → 𝔽))
            (fun w => if (hammingDist w (c : Fin N → 𝔽) : ℝ) ≤
              r * (N : ℝ) then (1 : ℕ) else 0)
        _ = ∑ z : Fin N → 𝔽,
            if (hammingDist z 0 : ℝ) ≤ r * (N : ℝ)
            then (1 : ℕ) else 0 := by
          apply Finset.sum_congr rfl
          intro z hz
          simp [hammingDist]
        _ = Ball.card := by
          rw [← Finset.sum_filter]
          simp [Ball]
    have hpairs : M N * Ball.card ≤
        (Fintype.card 𝔽) ^ N * L N := by
      change list_decodable (C N) r (L N) at hln
      unfold list_decodable at hln
      calc
        M N * Ball.card = ∑ c : C N, Ball.card := by
          simp [M, Nat.card_eq_fintype_card]
        _ = ∑ c : C N, ∑ w : Fin N → 𝔽,
              if (hammingDist w (c : Fin N → 𝔽) : ℝ) ≤ r * (N : ℝ)
              then (1 : ℕ) else 0 := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [htranslate c]
        _ = ∑ w : Fin N → 𝔽, ∑ c : C N,
              if (hammingDist w (c : Fin N → 𝔽) : ℝ) ≤ r * (N : ℝ)
              then (1 : ℕ) else 0 := Finset.sum_comm
        _ = ∑ w : Fin N → 𝔽,
              (Finset.univ.filter fun c : C N =>
                (hammingDist w (c : Fin N → 𝔽) : ℝ) ≤
                  r * (N : ℝ)).card := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [← Finset.sum_filter]
          simp
        _ ≤ ∑ _w : Fin N → 𝔽, L N := by
          apply Finset.sum_le_sum
          intro w hw
          exact hln w
        _ = (Fintype.card 𝔽) ^ N * L N := by
          simp [Fintype.card_fun]
    have hpairsR : (M N : ℝ) * (Ball.card : ℝ) ≤
        q ^ N * (L N : ℝ) := by
      dsimp [q]
      exact_mod_cast hpairs
    have hmul := mul_le_mul_of_nonneg_left hballlarge
      (show (0 : ℝ) ≤ M N by positivity)
    have hchain := hmul.trans hpairsR
    have hMLreal : (M N : ℝ) / 2 ≤ (L N : ℝ) := by
      nlinarith [hchain, hqpowpos]
    have hs3 : 3 ≤ L N := by
      dsimp [L]
      rw [Nat.le_sqrt]
      nlinarith
    have hsquare : L N * L N ≤ M N := by
      dsimp [L]
      exact Nat.sqrt_le _
    have htwice : 2 * L N < M N := by
      nlinarith
    have hnot : (M N : ℝ) ≤ 2 * (L N : ℝ) := by
      nlinarith
    exact (not_lt_of_ge hnot) (by exact_mod_cast htwice)

@[blueprint "thm:capacity-bridge"
  (statement := /-- Let $p\in(0,1)$ and let $(C_n)_{n\geq0}$ be a family of linear codes over a finite field of cardinality $q$.  Suppose that $(C_n)$ achieves list-decoding capacity on the adversarial channel introducing a $p$-fraction of corruptions and that
  \[
    d_{\min}(C_n)=\omega\!\left(\frac{q^3}{(1-p)^2}\right).
  \]
  Then $(C_n)$ achieves capacity on the $q$-ary symmetric channel $\mathrm{qSC}_p$. -/)
  (proof := /-- This is exactly \cref{lem:capacity-bridge-asymptotic-passage} applied to the given code family, list-decoding-capacity hypothesis, minimum-distance growth hypothesis, and the inequalities $0<p<1$. -/)
  (title := /-- List-decoding capacity implies capacity on the $q$-ary symmetric channel -/)
  (latexEnv := "theorem")]
theorem capacity_bridge
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (C : qary_code_family 𝔽) (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1)
    (hlist : achieves_list_decoding_capacity C p)
    (hdist : minimum_distance_growth C p) :
    achieves_qsc_capacity C p := by
  exact capacity_bridge_asymptotic_passage C p hp₀ hp₁ hlist hdist

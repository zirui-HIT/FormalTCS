import Architect
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory

@[blueprint "def:averaged-two-bin"
  (statement := /-- Let $T$ be a positive integer and let $\vreport = (r_t)_{t \in \{0,\dots,T-1\}}$ and
  $\vpred = (p_t)_{t \in \{0,\dots,T-1\}}$ be two families of real numbers indexed by $\mathrm{Fin}\,T$.
  The \emph{averaged two-bin calibration error} of $\vreport$ against $\vpred$ is
  \[
    \atb(\vreport,\vpred) \;=\; \int_{0}^{1} \frac{1}{T^2}\left(
      \Big(\sum_{t : r_t < q}(r_t - p_t)\Big)^2 +
      \Big(\sum_{t : r_t \ge q}(r_t - p_t)\Big)^2 \right)\,\mathrm dq ,
  \]
  where the integral is taken with respect to Lebesgue measure on $[0,1]$ (equivalently, the expectation
  over $q \sim \mathrm{Unif}([0,1])$) and, for each threshold $q$, the two sums range over the indices $t$
  with $r_t < q$ and with $r_t \ge q$ respectively. -/)
  (title := /-- Averaged two-bin calibration error (ATB) -/)
  (latexEnv := "definition")]
noncomputable def averaged_two_bin {T : ℕ} (r p : Fin T → ℝ) : ℝ :=
  ∫ q in (0 : ℝ)..1,
    (1 / (T : ℝ) ^ 2) *
      ((∑ t ∈ Finset.univ.filter (fun t => r t < q), (r t - p t)) ^ 2 +
       (∑ t ∈ Finset.univ.filter (fun t => q ≤ r t), (r t - p t)) ^ 2)

@[blueprint "def:state-bernoulli"
  (statement := /-- For a real parameter $p$, the \emph{single-coordinate Bernoulli state law} $\mathrm{Ber}(p)$
  is the Borel measure on $\mathbb R$ given by
  \[
    \mathrm{Ber}(p) \;=\; p\,\delta_{1} + (1-p)\,\delta_{0},
  \]
  where $\delta_a$ denotes the Dirac measure at $a \in \mathbb R$ and the coefficients are interpreted as
  extended-nonnegative reals via $x \mapsto \max(x,0)$. When $p \in [0,1]$ this is the distribution of a
  Bernoulli random variable with mean $p$, viewed as taking the real values $1$ and $0$. -/)
  (title := /-- Single-coordinate Bernoulli state law -/)
  (latexEnv := "definition")]
noncomputable def state_bernoulli (p : ℝ) : Measure ℝ :=
  ENNReal.ofReal p • Measure.dirac 1 + ENNReal.ofReal (1 - p) • Measure.dirac 0

@[blueprint "def:state-measure"
  (statement := /-- Let $T$ be a positive integer and let $\vpred = (p_t)_{t \in \mathrm{Fin}\,T}$ be a family of
  real numbers. The \emph{joint state law} $\mathbb P_{\vpred}$ associated with $\vpred$ is the product measure
  \[
    \mathbb P_{\vpred} \;=\; \bigotimes_{t \in \mathrm{Fin}\,T} \mathrm{Ber}(p_t)
  \]
  on $\mathbb R^{\mathrm{Fin}\,T}$, so that under $\mathbb P_{\vpred}$ the coordinates $y_t$ are independent and
  each $y_t$ has law $\mathrm{Ber}(p_t)$ (\cref{def:state-bernoulli}). Writing $\vstate \sim \vpred$ means that
  $\vstate$ is distributed according to $\mathbb P_{\vpred}$. -/)
  (title := /-- Joint state law of independent Bernoulli coordinates -/)
  (latexEnv := "definition")]
noncomputable def state_measure {T : ℕ} (p : Fin T → ℝ) : Measure (Fin T → ℝ) :=
  Measure.pi (fun t => state_bernoulli (p t))

@[blueprint "lem:atb-nonneg"
  (statement := /-- For every natural number $T$ and all families $\vreport,\vpred : \mathrm{Fin}\,T \to \mathbb R$,
  the averaged two-bin calibration error of \cref{def:averaged-two-bin} is nonnegative:
  \[
    \atb(\vreport,\vpred) \;\ge\; 0 .
  \]
  No range restriction is imposed on the entries of $\vreport$ and $\vpred$: they are arbitrary real numbers. -/)
  (proof := /-- Since $0 \le 1$, it suffices, by nonnegativity of the interval integral of a pointwise
  nonnegative integrand, to show that the integrand is nonnegative at every $q \in [0,1]$. So fix
  $q \in [0,1]$. The integrand of \cref{def:averaged-two-bin} equals
  $\tfrac{1}{T^2}\big(A(q)^2 + B(q)^2\big)$, where $A(q) = \sum_{t : r_t < q}(r_t - p_t)$ and
  $B(q) = \sum_{t : r_t \ge q}(r_t - p_t)$. Both $A(q)^2 \ge 0$ and $B(q)^2 \ge 0$, being squares of real
  numbers, so $A(q)^2 + B(q)^2 \ge 0$; moreover $\tfrac{1}{T^2} \ge 0$, since it is the reciprocal of the
  square of the real number $T$ (this also covers the degenerate case $T = 0$, where the factor is $0$).
  Hence the product $\tfrac{1}{T^2}\big(A(q)^2 + B(q)^2\big)$ is nonnegative, and therefore
  $\atb(\vreport,\vpred) \ge 0$. -/)
  (title := /-- Nonnegativity of ATB -/)
  (latexEnv := "lemma")]
lemma atb_nonneg {T : ℕ} (r p : Fin T → ℝ) : 0 ≤ averaged_two_bin r p := by
  refine intervalIntegral.integral_nonneg zero_le_one fun q _ => ?_
  positivity

@[blueprint "lem:atb-self-zero"
  (statement := /-- For every natural number $T$ and every family $\vpred = (p_t)_{t \in \mathrm{Fin}\,T}$ of real
  numbers, the averaged two-bin calibration error of \cref{def:averaged-two-bin} of $\vpred$ against itself
  vanishes:
  \[
    \atb(\vpred,\vpred) \;=\; 0 .
  \] -/)
  (proof := /-- Substitute $\vreport = \vpred$ into \cref{def:averaged-two-bin}. For every threshold $q$ and
  every index $t$, the summand $p_t - p_t = 0$, so both bin sums $\sum_{t : p_t < q}(p_t - p_t)$ and
  $\sum_{t : p_t \ge q}(p_t - p_t)$ are $0$. Therefore the integrand equals
  $\tfrac{1}{T^2}\,(0^2 + 0^2) = 0$ for every $q$, and the integral of the zero function over $[0,1]$ is $0$. -/)
  (title := /-- ATB vanishes on the ground truth -/)
  (latexEnv := "lemma")]
lemma atb_self_zero {T : ℕ} (p : Fin T → ℝ) : averaged_two_bin p p = 0 := by
  simp only [averaged_two_bin, sub_self, Finset.sum_const_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, mul_zero,
    intervalIntegral.integral_zero]

@[blueprint "lem:atb-bool-prod-sum"
  (statement := /-- Let $T$ be a natural number, let $M$ be a commutative semiring, and let
  $u,v : \mathrm{Fin}\,T \to M$. Then, summing over all sign patterns $b : \mathrm{Fin}\,T \to \{\top,\bot\}$,
  \[
    \sum_{b} \prod_{i \in \mathrm{Fin}\,T} \big(u_i\ \text{if}\ b_i,\ v_i\ \text{otherwise}\big)
      \;=\; \prod_{i \in \mathrm{Fin}\,T} (u_i + v_i).
  \] -/)
  (proof := /-- Expanding each factor, $u_i + v_i = \sum_{c \in \{\top,\bot\}} (u_i$ if $c$, $v_i$ otherwise$)$,
  because the two-element type $\{\top,\bot\}$ has exactly the summands $c = \top$ and $c = \bot$. Substituting
  this expansion into the right-hand side and distributing the product over the sums, the generalised
  distributivity law for a product of finite sums rewrites $\prod_i \sum_{c} (\cdots)$ as a sum indexed by the
  finitely supported choice functions assigning to each $i \in \mathrm{Fin}\,T$ one index $c \in \{\top,\bot\}$,
  the summand attached to a choice function being the product of the selected factors. That index set is
  precisely the set of maps $b : \mathrm{Fin}\,T \to \{\top,\bot\}$, and under this identification the summand
  attached to $b$ is $\prod_i (u_i$ if $b_i$, $v_i$ otherwise$)$. Matching the two sums term by term along this
  bijection gives the claimed identity. -/)
  (title := /-- Product of binary sums as a sum over sign patterns -/)
  (latexEnv := "lemma")]
lemma atb_bool_prod_sum {T : ℕ} {M : Type*} [CommSemiring M] (u v : Fin T → M) :
    ∑ b : Fin T → Bool, ∏ i, (if b i then u i else v i) = ∏ i, (u i + v i) := by
  have h : ∀ i, u i + v i = ∑ c : Bool, (if c then u i else v i) := by
    intro i
    simp [Fintype.sum_bool]
  simp only [h]
  rw [Finset.prod_univ_sum]
  apply Finset.sum_nbij' (fun x => (x : Fin T → Bool)) (fun b => b) <;> simp

@[blueprint "lem:atb-state-measure-eq-dirac-sum"
  (statement := /-- Let $T$ be a natural number and let $\vpred : \mathrm{Fin}\,T \to \mathbb R$. Then the joint
  state law $\mathbb P_{\vpred}$ of \cref{def:state-measure} is the finite combination of Dirac measures
  \[
    \mathbb P_{\vpred} \;=\; \sum_{b : \mathrm{Fin}\,T \to \{\top,\bot\}}
      \Big(\prod_{i} w_i(b_i)\Big)\,\delta_{y(b)},
  \]
  where $w_i(\top) = (p_i)_+$ and $w_i(\bot) = (1 - p_i)_+$ are the extended-nonnegative coefficients
  $x \mapsto \max(x,0)$ of \cref{def:state-bernoulli}, and $y(b) \in \mathbb R^{\mathrm{Fin}\,T}$ is the binary
  configuration with $y(b)_i = 1$ if $b_i$ holds and $y(b)_i = 0$ otherwise. -/)
  (proof := /-- Both sides are measures on $\mathbb R^{\mathrm{Fin}\,T}$, and the left-hand side is by
  definition the product measure $\bigotimes_i \mathrm{Ber}(p_i)$ of \cref{def:state-measure}. Each factor
  $\mathrm{Ber}(p_i) = (p_i)_+\,\delta_1 + (1 - p_i)_+\,\delta_0$ of \cref{def:state-bernoulli} is a finite
  measure, since its total mass is $(p_i)_+ + (1-p_i)_+ < \infty$; in particular each factor is $\sigma$-finite,
  so the product measure is characterised by its values on measurable rectangles. It therefore suffices to fix
  measurable sets $s_i \subseteq \mathbb R$ and to verify that the right-hand side assigns to the rectangle
  $\prod_i s_i$ the value $\prod_i \mathrm{Ber}(p_i)(s_i)$.

  For the individual factors, evaluating $\mathrm{Ber}(p_i)$ on a measurable set $s_i$ gives
  $\mathrm{Ber}(p_i)(s_i) = \mathbf 1[1 \in s_i]\,(p_i)_+ + \mathbf 1[0 \in s_i]\,(1 - p_i)_+$, because
  $\delta_a(s_i) = \mathbf 1[a \in s_i]$ for measurable $s_i$. Hence
  $\prod_i \mathrm{Ber}(p_i)(s_i) = \prod_i \big(\mathbf 1[1 \in s_i](p_i)_+ + \mathbf 1[0 \in s_i](1-p_i)_+\big)$,
  and \cref{lem:atb-bool-prod-sum}, applied with $u_i = \mathbf 1[1 \in s_i](p_i)_+$ and
  $v_i = \mathbf 1[0 \in s_i](1-p_i)_+$ in the semiring of extended nonnegative reals, rewrites this product as
  $\sum_b \prod_i (u_i$ if $b_i$, $v_i$ otherwise$)$.

  It remains to compare this sum term by term with the right-hand side evaluated on $\prod_i s_i$. Fix $b$. The
  $b$-th term of the right-hand side is $\big(\prod_i w_i(b_i)\big)\,\mathbf 1[y(b) \in \prod_i s_i]$. If
  $y(b)_i \in s_i$ for every $i$, the indicator is $1$ and the two $b$-th terms agree factorwise: for each $i$,
  distinguishing the cases $b_i = \top$ and $b_i = \bot$, membership of $y(b)_i$ in $s_i$ turns the indicator
  $\mathbf 1[y(b)_i \in s_i]$ into $1$ and leaves $w_i(b_i)$. Otherwise there is an index $i$ with
  $y(b)_i \notin s_i$; then the right-hand term vanishes because its indicator is $0$, and the corresponding
  product vanishes as well because its $i$-th factor is $\mathbf 1[y(b)_i \in s_i]\,w_i(b_i) = 0$. -/)
  (title := /-- The joint state law as a finite combination of Dirac measures -/)
  (latexEnv := "lemma")]
lemma atb_state_measure_eq_dirac_sum {T : ℕ} (p : Fin T → ℝ) :
    state_measure p = ∑ b : Fin T → Bool,
      (∏ i, (if b i then ENNReal.ofReal (p i) else ENNReal.ofReal (1 - p i))) •
        Measure.dirac (fun i => if b i then (1 : ℝ) else 0) := by
  classical
  haveI : ∀ a : ℝ, IsFiniteMeasure (state_bernoulli a) := by
    intro a
    constructor
    simp [state_bernoulli, Measure.add_apply, Measure.smul_apply]
  have hb : ∀ (a : ℝ) (u : Set ℝ), MeasurableSet u →
      state_bernoulli a u = (if (1 : ℝ) ∈ u then ENNReal.ofReal a else 0)
        + (if (0 : ℝ) ∈ u then ENNReal.ofReal (1 - a) else 0) := by
    intro a u hum
    simp only [state_bernoulli, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hum, Set.indicator_apply]
    split_ifs <;> simp
  rw [state_measure]
  refine Measure.pi_eq ?_
  intro s hs
  have hprod : ∏ i, state_bernoulli (p i) (s i)
      = ∏ i, ((if (1 : ℝ) ∈ s i then ENNReal.ofReal (p i) else 0)
        + (if (0 : ℝ) ∈ s i then ENNReal.ofReal (1 - p i) else 0)) :=
    Finset.prod_congr rfl fun i _ => hb (p i) (s i) (hs i)
  rw [Measure.finset_sum_apply, hprod,
    ← atb_bool_prod_sum (fun i => if (1 : ℝ) ∈ s i then ENNReal.ofReal (p i) else 0)
      (fun i => if (0 : ℝ) ∈ s i then ENNReal.ofReal (1 - p i) else 0)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ (MeasurableSet.univ_pi hs), smul_eq_mul,
    Set.indicator_apply]
  by_cases hmem : ∀ i, (if b i then (1 : ℝ) else 0) ∈ s i
  · have hmem' : (fun i => if b i then (1 : ℝ) else 0) ∈ Set.univ.pi s :=
      fun i _ => hmem i
    rw [if_pos hmem', Pi.one_apply, mul_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi := hmem i
    cases hbi : b i <;> simp_all
  · have hmem' : (fun i => if b i then (1 : ℝ) else 0) ∉ Set.univ.pi s := by
      intro hcon
      exact hmem fun i => hcon i (Set.mem_univ i)
    rw [if_neg hmem', mul_zero]
    obtain ⟨i, hi⟩ := not_forall.1 hmem
    symm
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    cases hbi : b i <;> simp_all

@[blueprint "lem:atb-state-measure-integral-eq-sum"
  (statement := /-- Let $T$ be a natural number, let $\vpred : \mathrm{Fin}\,T \to \mathbb R$ satisfy
  $p_i \in [0,1]$ for every $i \in \mathrm{Fin}\,T$, and let $f : \mathbb R^{\mathrm{Fin}\,T} \to \mathbb R$ be an
  arbitrary function. Then $f$ has a Bochner integral against the joint state law $\mathbb P_{\vpred}$ of
  \cref{def:state-measure}, given by the finite sum
  \[
    \int f \,\mathrm d\mathbb P_{\vpred}
      \;=\; \sum_{b : \mathrm{Fin}\,T \to \{\top,\bot\}}
        \Big(\prod_{i} \big(p_i\ \text{if}\ b_i,\ 1 - p_i\ \text{otherwise}\big)\Big)\, f(y(b)),
  \]
  where $y(b)_i = 1$ if $b_i$ holds and $y(b)_i = 0$ otherwise. -/)
  (proof := /-- By \cref{lem:atb-state-measure-eq-dirac-sum}, $\mathbb P_{\vpred}$ is the finite sum of the
  measures $c_b\,\delta_{y(b)}$ with $c_b = \prod_i w_i(b_i)$, where $w_i(\top) = (p_i)_+$ and
  $w_i(\bot) = (1 - p_i)_+$. Every real-valued function is integrable against a Dirac measure on
  $\mathbb R^{\mathrm{Fin}\,T}$, since singletons are measurable there and the integral of the norm reduces to
  the finite value $\lVert f(y(b))\rVert$; rescaling by the finite constant $c_b$ preserves integrability, so $f$
  is integrable against each summand $c_b\,\delta_{y(b)}$. Consequently the integral against a finite sum of
  measures is the sum of the integrals, and
  $\int f\,\mathrm d(c_b\,\delta_{y(b)}) = c_b\,\int f\,\mathrm d\delta_{y(b)} = c_b\, f(y(b))$, the last step
  being the defining property of the Dirac measure.

  Finally the coefficients are identified. Since $p_i \in [0,1]$, both $p_i \ge 0$ and $1 - p_i \ge 0$, so
  $(p_i)_+ = p_i$ and $(1 - p_i)_+ = 1 - p_i$ as real numbers; as each factor is finite, the real number
  attached to $c_b$ is the product $\prod_i (p_i$ if $b_i$, $1 - p_i$ otherwise$)$. Substituting this into the
  sum over $b$ gives the stated formula. -/)
  (title := /-- Expectation under the joint state law as a finite sum over binary configurations -/)
  (latexEnv := "lemma")]
lemma atb_state_measure_integral_eq_sum {T : ℕ} (p : Fin T → ℝ)
    (hp : ∀ t, p t ∈ Set.Icc (0 : ℝ) 1) (f : (Fin T → ℝ) → ℝ) :
    ∫ y, f y ∂(state_measure p) =
      ∑ b : Fin T → Bool, (∏ i, (if b i then p i else 1 - p i)) *
        f (fun i => if b i then (1 : ℝ) else 0) := by
  classical
  have hfin : ∀ b : Fin T → Bool,
      (∏ i, (if b i then ENNReal.ofReal (p i) else ENNReal.ofReal (1 - p i))) ≠ ⊤ := by
    intro b
    refine ne_of_lt (ENNReal.prod_lt_top ?_)
    intro i _
    split_ifs <;> exact ENNReal.ofReal_lt_top
  have hint : ∀ b : Fin T → Bool,
      Integrable f ((∏ i, (if b i then ENNReal.ofReal (p i) else ENNReal.ofReal (1 - p i))) •
        Measure.dirac (fun i => if b i then (1 : ℝ) else 0)) := by
    intro b
    exact (integrable_dirac (by simp)).smul_measure (hfin b)
  rw [atb_state_measure_eq_dirac_sum p, integral_finset_sum_measure fun b _ => hint b]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_smul_measure, integral_dirac, smul_eq_mul, ENNReal.toReal_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  cases hbi : b i
  · exact ENNReal.toReal_ofReal (by linarith [(hp i).2])
  · exact ENNReal.toReal_ofReal (hp i).1

@[blueprint "lem:atb-bernoulli-cross-moment"
  (statement := /-- Let $T$ be a natural number, let $\vreport,\vpred : \mathrm{Fin}\,T \to \mathbb R$, and let
  $s,t \in \mathrm{Fin}\,T$. Weighting each binary configuration $y(b)$, with $y(b)_i = 1$ if $b_i$ holds and
  $y(b)_i = 0$ otherwise, by $\prod_i (p_i$ if $b_i$, $1 - p_i$ otherwise$)$, one has
  \[
    \sum_{b : \mathrm{Fin}\,T \to \{\top,\bot\}} \Big(\prod_{i} \big(p_i\ \text{if}\ b_i,\ 1 - p_i\
      \text{otherwise}\big)\Big)\,(r_s - y(b)_s)(r_t - y(b)_t)
      \;=\; (r_s - p_s)(r_t - p_t) + \mathbf 1[s = t]\,p_s(1 - p_s).
  \] -/)
  (proof := /-- Both cases are instances of \cref{lem:atb-bool-prod-sum}, applied after writing the summand as a
  single product over $i \in \mathrm{Fin}\,T$ of a factor depending only on $b_i$.

  Suppose first $s = t$. Define $u_i = p_i(r_s - 1)^2$ and $v_i = (1 - p_i)r_s^2$ for $i = s$, and $u_i = p_i$,
  $v_i = 1 - p_i$ for $i \neq s$. For every $b$, the factor of index $i$ in $\prod_i (u_i$ if $b_i$, $v_i$
  otherwise$)$ equals the $i$-th weight $(p_i$ if $b_i$, $1 - p_i$ otherwise$)$ times $(r_s - y(b)_s)^2$ when
  $i = s$ and times $1$ otherwise, because $r_s - y(b)_s$ equals $r_s - 1$ if $b_s$ holds and $r_s$ otherwise.
  Hence the summand equals $\prod_i (u_i$ if $b_i$, $v_i$ otherwise$)$, and
  \cref{lem:atb-bool-prod-sum} evaluates the sum as $\prod_i (u_i + v_i)$. All factors with $i \neq s$ equal
  $p_i + (1 - p_i) = 1$, so the product reduces to its $s$-th factor
  $p_s(r_s - 1)^2 + (1 - p_s)r_s^2 = r_s^2 - 2p_sr_s + p_s = (r_s - p_s)^2 + p_s(1 - p_s)$, which is the claim
  since $\mathbf 1[s = t] = 1$.

  Suppose now $s \neq t$. Define $u_i = p_i(r_s - 1)$, $v_i = (1 - p_i)r_s$ for $i = s$; $u_i = p_i(r_t - 1)$,
  $v_i = (1 - p_i)r_t$ for $i = t$; and $u_i = p_i$, $v_i = 1 - p_i$ for all other $i$. As before the summand
  equals $\prod_i (u_i$ if $b_i$, $v_i$ otherwise$)$, the two distinguished indices contributing the factors
  $r_s - y(b)_s$ and $r_t - y(b)_t$ respectively. By \cref{lem:atb-bool-prod-sum} the sum equals
  $\prod_i (u_i + v_i)$; all factors with $i \notin \{s,t\}$ equal $1$, so the product reduces to
  $\big(p_s(r_s - 1) + (1 - p_s)r_s\big)\big(p_t(r_t - 1) + (1 - p_t)r_t\big) = (r_s - p_s)(r_t - p_t)$, which is
  the claim since $\mathbf 1[s = t] = 0$. -/)
  (title := /-- Second moments of the centred binary states -/)
  (latexEnv := "lemma")]
lemma atb_bernoulli_cross_moment {T : ℕ} (r p : Fin T → ℝ) (s t : Fin T) :
    ∑ b : Fin T → Bool, (∏ i, (if b i then p i else 1 - p i)) *
        ((r s - (if b s then (1 : ℝ) else 0)) * (r t - (if b t then (1 : ℝ) else 0))) =
      (r s - p s) * (r t - p t) + (if s = t then p s * (1 - p s) else 0) := by
  classical
  have key1 : ∀ (w : Fin T → ℝ) (c : ℝ) (a : Fin T),
      ∏ i, (w i * (if i = a then c else 1)) = (∏ i, w i) * c := by
    intro w c a
    rw [Finset.prod_mul_distrib,
      Fintype.prod_eq_single a (f := fun i => if i = a then c else 1) (fun x hx => if_neg hx),
      if_pos rfl]
  have key2 : ∀ (w : Fin T → ℝ) (c d : ℝ) (a e : Fin T), a ≠ e →
      ∏ i, (w i * (if i = a then c else if i = e then d else 1)) = (∏ i, w i) * (c * d) := by
    intro w c d a e hae
    rw [Finset.prod_mul_distrib,
      Fintype.prod_eq_mul a e hae (f := fun i => if i = a then c else if i = e then d else 1)
        (fun x hx => by rw [if_neg hx.1, if_neg hx.2]),
      if_pos rfl, if_neg (Ne.symm hae), if_pos rfl]
  by_cases hst : s = t
  · subst hst
    have hsum : ∀ b : Fin T → Bool, (∏ i, (if b i then p i else 1 - p i)) *
        ((r s - (if b s then (1 : ℝ) else 0)) * (r s - (if b s then (1 : ℝ) else 0)))
        = ∏ i, (if b i then (if i = s then p i * ((r s - 1) * (r s - 1)) else p i)
            else (if i = s then (1 - p i) * (r s * r s) else 1 - p i)) := by
      intro b
      rw [Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) =>
        show (if b i then (if i = s then p i * ((r s - 1) * (r s - 1)) else p i)
            else (if i = s then (1 - p i) * (r s * r s) else 1 - p i))
          = (if b i then p i else 1 - p i) *
            (if i = s then (r s - (if b s then (1 : ℝ) else 0)) *
              (r s - (if b s then (1 : ℝ) else 0)) else 1) from by
          by_cases hi : i = s
          · subst hi
            cases hbi : b i <;> simp [hbi] <;> ring
          · rw [if_neg hi, if_neg hi, if_neg hi, mul_one]),
        key1 (fun i => if b i then p i else 1 - p i)]
    rw [Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => hsum b),
      atb_bool_prod_sum (fun i => if i = s then p i * ((r s - 1) * (r s - 1)) else p i)
        (fun i => if i = s then (1 - p i) * (r s * r s) else 1 - p i),
      Fintype.prod_eq_single s
        (f := fun i => (if i = s then p i * ((r s - 1) * (r s - 1)) else p i)
          + (if i = s then (1 - p i) * (r s * r s) else 1 - p i))
        (fun x hx => by rw [if_neg hx, if_neg hx]; ring),
      if_pos rfl, if_pos rfl, if_pos rfl]
    ring
  · have hsum : ∀ b : Fin T → Bool, (∏ i, (if b i then p i else 1 - p i)) *
        ((r s - (if b s then (1 : ℝ) else 0)) * (r t - (if b t then (1 : ℝ) else 0)))
        = ∏ i, (if b i then (if i = s then p i * (r s - 1) else if i = t then p i * (r t - 1) else p i)
            else (if i = s then (1 - p i) * r s else if i = t then (1 - p i) * r t else 1 - p i)) := by
      intro b
      rw [Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) =>
        show (if b i then (if i = s then p i * (r s - 1) else if i = t then p i * (r t - 1) else p i)
            else (if i = s then (1 - p i) * r s else if i = t then (1 - p i) * r t else 1 - p i))
          = (if b i then p i else 1 - p i) *
            (if i = s then r s - (if b s then (1 : ℝ) else 0)
              else if i = t then r t - (if b t then (1 : ℝ) else 0) else 1) from by
          by_cases hi : i = s
          · subst hi
            cases hbi : b i <;> simp [hbi] <;> ring
          · by_cases hi' : i = t
            · subst hi'
              cases hbi : b i <;> simp [hi, hbi] <;> ring
            · rw [if_neg hi, if_neg hi', if_neg hi, if_neg hi', if_neg hi, if_neg hi', mul_one]),
        key2 (fun i => if b i then p i else 1 - p i) _ _ s t hst]
    rw [Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => hsum b),
      atb_bool_prod_sum
        (fun i => if i = s then p i * (r s - 1) else if i = t then p i * (r t - 1) else p i)
        (fun i => if i = s then (1 - p i) * r s else if i = t then (1 - p i) * r t else 1 - p i),
      Fintype.prod_eq_mul s t hst
        (f := fun i => (if i = s then p i * (r s - 1) else if i = t then p i * (r t - 1) else p i)
          + (if i = s then (1 - p i) * r s else if i = t then (1 - p i) * r t else 1 - p i))
        (fun x hx => by rw [if_neg hx.1, if_neg hx.2, if_neg hx.1, if_neg hx.2]; ring),
      if_pos rfl, if_pos rfl, if_neg (Ne.symm hst), if_neg (Ne.symm hst), if_pos rfl, if_pos rfl,
      if_neg hst]
    ring

@[blueprint "lem:atb-bin-sum-sq-expand"
  (statement := /-- Let $T$ be a natural number, let $\vreport : \mathrm{Fin}\,T \to \mathbb R$, let
  $q \in \mathbb R$, and let $d : \mathrm{Fin}\,T \to \mathbb R$. Writing $\mathbf 1[\cdot]$ for the indicator
  taking the value $1$ when its condition holds and $0$ otherwise,
  \[
    \Big(\sum_{t : r_t < q} d_t\Big)^2 + \Big(\sum_{t : q \le r_t} d_t\Big)^2
      \;=\; \sum_{s}\sum_{t} \big(\mathbf 1[r_s < q]\,\mathbf 1[r_t < q]
        + \mathbf 1[q \le r_s]\,\mathbf 1[q \le r_t]\big)\, d_s d_t ,
  \]
  both inner sums on the left ranging over the indices of $\mathrm{Fin}\,T$ satisfying the displayed condition
  and both sums on the right ranging over all of $\mathrm{Fin}\,T$. -/)
  (proof := /-- Rewriting each restricted sum as a sum over all of $\mathrm{Fin}\,T$ with the corresponding
  indicator factor gives $\sum_{t : r_t < q} d_t = \sum_t \mathbf 1[r_t < q]\,d_t$ and
  $\sum_{t : q \le r_t} d_t = \sum_t \mathbf 1[q \le r_t]\,d_t$. Expanding each square as the product of the sum
  with itself and distributing the product of two finite sums, the left-hand side becomes
  \[
    \sum_{s}\sum_{t} \mathbf 1[r_s < q]\,d_s\,\mathbf 1[r_t < q]\,d_t
      + \sum_{s}\sum_{t} \mathbf 1[q \le r_s]\,d_s\,\mathbf 1[q \le r_t]\,d_t ,
  \]
  and combining the two double sums into one leaves a single double sum whose $(s,t)$ term is
  $\mathbf 1[r_s < q]\,d_s\,\mathbf 1[r_t < q]\,d_t + \mathbf 1[q \le r_s]\,d_s\,\mathbf 1[q \le r_t]\,d_t$.
  For each fixed pair $(s,t)$ this term equals
  $\big(\mathbf 1[r_s < q]\mathbf 1[r_t < q] + \mathbf 1[q \le r_s]\mathbf 1[q \le r_t]\big)d_sd_t$: resolving
  the four indicator cases, each side is a sum of the same monomials in $d_s d_t$, so the identity follows by
  commutative ring algebra. -/)
  (title := /-- Bilinear expansion of the two-bin square sum -/)
  (latexEnv := "lemma")]
lemma atb_bin_sum_sq_expand {T : ℕ} (r : Fin T → ℝ) (q : ℝ) (d : Fin T → ℝ) :
    (∑ t ∈ Finset.univ.filter (fun t => r t < q), d t) ^ 2 +
        (∑ t ∈ Finset.univ.filter (fun t => q ≤ r t), d t) ^ 2 =
      ∑ s, ∑ t, ((if r s < q then (1 : ℝ) else 0) * (if r t < q then (1 : ℝ) else 0) +
        (if q ≤ r s then (1 : ℝ) else 0) * (if q ≤ r t then (1 : ℝ) else 0)) * (d s * d t) := by
  simp only [Finset.sum_filter, sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> ring

@[blueprint "lem:atb-integrand-interval-integrable"
  (statement := /-- Let $T$ be a natural number and let $\vreport, \vstate : \mathrm{Fin}\,T \to \mathbb R$.
  Then the integrand of \cref{def:averaged-two-bin}, namely
  \[
    q \;\longmapsto\; \frac{1}{T^2}\left(\Big(\sum_{t : r_t < q}(r_t - y_t)\Big)^2
      + \Big(\sum_{t : q \le r_t}(r_t - y_t)\Big)^2\right),
  \]
  is interval integrable with respect to Lebesgue measure on the interval from $0$ to $1$. -/)
  (proof := /-- By \cref{lem:atb-bin-sum-sq-expand} applied with $d_t = r_t - y_t$, for every $q$ the integrand
  equals
  \[
    \frac{1}{T^2}\sum_{s}\sum_{t}\big(\mathbf 1[r_s < q]\mathbf 1[r_t < q]
      + \mathbf 1[q \le r_s]\mathbf 1[q \le r_t]\big)(r_s - y_s)(r_t - y_t),
  \]
  a finite real-linear combination, with coefficients independent of $q$, of the functions
  $q \mapsto \mathbf 1[r_s < q]\mathbf 1[r_t < q]$ and $q \mapsto \mathbf 1[q \le r_s]\mathbf 1[q \le r_t]$.
  The first of these is monotone: each factor is nondecreasing in $q$ with values in $\{0,1\}$, so their product
  is nondecreasing. The second is antitone by the same argument applied to the nonincreasing factors
  $\mathbf 1[q \le r_s]$ and $\mathbf 1[q \le r_t]$. Monotone and antitone real functions are interval
  integrable on any interval, hence so is their sum, so is each product with a constant, and so is the finite
  double sum of these terms together with the outer constant factor $1/T^2$. Since interval integrability only
  depends on the function, it transfers back to the original integrand. -/)
  (title := /-- Interval integrability of the two-bin integrand -/)
  (latexEnv := "lemma")]
lemma atb_integrand_interval_integrable {T : ℕ} (r y : Fin T → ℝ) :
    IntervalIntegrable (fun q => (1 / (T : ℝ) ^ 2) *
        ((∑ t ∈ Finset.univ.filter (fun t => r t < q), (r t - y t)) ^ 2 +
         (∑ t ∈ Finset.univ.filter (fun t => q ≤ r t), (r t - y t)) ^ 2)) volume 0 1 := by
  have hfun : (fun q => (1 / (T : ℝ) ^ 2) *
      ((∑ t ∈ Finset.univ.filter (fun t => r t < q), (r t - y t)) ^ 2 +
       (∑ t ∈ Finset.univ.filter (fun t => q ≤ r t), (r t - y t)) ^ 2))
      = fun q => (1 / (T : ℝ) ^ 2) * ∑ s, ∑ t,
          ((if r s < q then (1 : ℝ) else 0) * (if r t < q then (1 : ℝ) else 0) +
            (if q ≤ r s then (1 : ℝ) else 0) * (if q ≤ r t then (1 : ℝ) else 0)) *
            ((r s - y s) * (r t - y t)) := by
    funext q
    rw [atb_bin_sum_sq_expand r q (fun t => r t - y t)]
  rw [hfun]
  refine IntervalIntegrable.const_mul ?_ _
  have hsum : (fun q => ∑ s, ∑ t,
      ((if r s < q then (1 : ℝ) else 0) * (if r t < q then (1 : ℝ) else 0) +
        (if q ≤ r s then (1 : ℝ) else 0) * (if q ≤ r t then (1 : ℝ) else 0)) *
        ((r s - y s) * (r t - y t)))
      = ∑ s : Fin T, ∑ t : Fin T, (fun q : ℝ =>
        ((if r s < q then (1 : ℝ) else 0) * (if r t < q then (1 : ℝ) else 0) +
          (if q ≤ r s then (1 : ℝ) else 0) * (if q ≤ r t then (1 : ℝ) else 0)) *
          ((r s - y s) * (r t - y t))) := by
    funext q
    simp [Finset.sum_apply]
  rw [hsum]
  refine IntervalIntegrable.sum _ fun s _ => IntervalIntegrable.sum _ fun t _ => ?_
  refine IntervalIntegrable.mul_const ?_ _
  refine IntervalIntegrable.add ?_ ?_
  · refine Monotone.intervalIntegrable ?_
    intro a c hac
    dsimp only
    split_ifs <;> norm_num <;> linarith
  · refine Antitone.intervalIntegrable ?_
    intro a c hac
    dsimp only
    split_ifs <;> norm_num <;> linarith

@[blueprint "lem:atb-pointwise-decomposition"
  (statement := /-- Let $T$ be a natural number, let $\vreport,\vpred : \mathrm{Fin}\,T \to \mathbb R$, and let
  $q \in \mathbb R$. Averaging the two-bin square sum at threshold $q$ over the binary configurations $y(b)$,
  weighted by $\prod_i (p_i$ if $b_i$, $1 - p_i$ otherwise$)$, gives
  \[
    \sum_{b} \Big(\prod_{i} \big(p_i\ \text{if}\ b_i,\ 1 - p_i\ \text{otherwise}\big)\Big)
      \left(\Big(\sum_{t : r_t < q}(r_t - y(b)_t)\Big)^2 + \Big(\sum_{t : q \le r_t}(r_t - y(b)_t)\Big)^2\right)
  \]
  \[
    =\; \Big(\sum_{t : r_t < q}(r_t - p_t)\Big)^2 + \Big(\sum_{t : q \le r_t}(r_t - p_t)\Big)^2
      \;+\; \sum_{t \in \mathrm{Fin}\,T} p_t\,(1 - p_t),
  \]
  where $y(b)_t = 1$ if $b_t$ holds and $y(b)_t = 0$ otherwise, and the restricted sums range over the indices
  of $\mathrm{Fin}\,T$ satisfying the displayed condition. -/)
  (proof := /-- Write $K_{s,t} = \mathbf 1[r_s < q]\mathbf 1[r_t < q] + \mathbf 1[q \le r_s]\mathbf 1[q \le r_t]$
  for the kernel of the threshold $q$; note that $K_{s,t}$ does not depend on the configuration.
  By \cref{lem:atb-bin-sum-sq-expand}, applied for each fixed $b$ with $d_t = r_t - y(b)_t$, the bracket
  attached to $b$ equals $\sum_s \sum_t K_{s,t}\,(r_s - y(b)_s)(r_t - y(b)_t)$. Multiplying by the weight of $b$
  and summing over $b$, the left-hand side becomes
  $\sum_b \sum_s \sum_t K_{s,t}(r_s - y(b)_s)(r_t - y(b)_t)\prod_i(p_i$ if $b_i$, $1-p_i$ otherwise$)$.

  All sums are finite, so the order of summation may be exchanged, bringing the sum over $b$ innermost. For
  fixed $s$ and $t$ the inner sum is $K_{s,t}$ times
  $\sum_b \big(\prod_i (p_i$ if $b_i$, $1-p_i$ otherwise$)\big)(r_s - y(b)_s)(r_t - y(b)_t)$, which by
  \cref{lem:atb-bernoulli-cross-moment} equals $K_{s,t}\big((r_s - p_s)(r_t - p_t) + \mathbf 1[s = t]p_s(1-p_s)\big)$.
  Hence the left-hand side equals
  $\sum_s \sum_t K_{s,t}(r_s - p_s)(r_t - p_t) + \sum_s \sum_t K_{s,t}\,\mathbf 1[s = t]\,p_s(1 - p_s)$.

  The first double sum is, by \cref{lem:atb-bin-sum-sq-expand} applied with $d_t = r_t - p_t$, exactly
  $\big(\sum_{t : r_t < q}(r_t - p_t)\big)^2 + \big(\sum_{t : q \le r_t}(r_t - p_t)\big)^2$. In the second double
  sum only the diagonal term $t = s$ survives, leaving $\sum_s K_{s,s}\,p_s(1 - p_s)$; and $K_{s,s} = 1$ for
  every $s$, because exactly one of $r_s < q$ and $q \le r_s$ holds, so one of the two products
  $\mathbf 1[r_s<q]^2$ and $\mathbf 1[q \le r_s]^2$ equals $1$ and the other equals $0$. The second double sum is
  therefore $\sum_s p_s(1 - p_s)$, which gives the stated identity. -/)
  (title := /-- Pointwise error decomposition at a fixed threshold -/)
  (latexEnv := "lemma")]
lemma atb_pointwise_decomposition {T : ℕ} (r p : Fin T → ℝ) (q : ℝ) :
    ∑ b : Fin T → Bool, (∏ i, (if b i then p i else 1 - p i)) *
        ((∑ t ∈ Finset.univ.filter (fun t => r t < q), (r t - (if b t then (1 : ℝ) else 0))) ^ 2 +
         (∑ t ∈ Finset.univ.filter (fun t => q ≤ r t), (r t - (if b t then (1 : ℝ) else 0))) ^ 2) =
      ((∑ t ∈ Finset.univ.filter (fun t => r t < q), (r t - p t)) ^ 2 +
        (∑ t ∈ Finset.univ.filter (fun t => q ≤ r t), (r t - p t)) ^ 2) + ∑ t, p t * (1 - p t) := by
  classical
  set K : Fin T → Fin T → ℝ := fun s t =>
    (if r s < q then (1 : ℝ) else 0) * (if r t < q then (1 : ℝ) else 0) +
      (if q ≤ r s then (1 : ℝ) else 0) * (if q ≤ r t then (1 : ℝ) else 0) with hK
  have hexpand : ∀ b : Fin T → Bool, (∏ i, (if b i then p i else 1 - p i)) *
      ((∑ t ∈ Finset.univ.filter (fun t => r t < q), (r t - (if b t then (1 : ℝ) else 0))) ^ 2 +
       (∑ t ∈ Finset.univ.filter (fun t => q ≤ r t), (r t - (if b t then (1 : ℝ) else 0))) ^ 2)
      = ∑ s, ∑ t, K s t *
        ((r s - (if b s then (1 : ℝ) else 0)) * (r t - (if b t then (1 : ℝ) else 0))) *
        (∏ i, (if b i then p i else 1 - p i)) := by
    intro b
    rw [atb_bin_sum_sq_expand r q (fun t => r t - (if b t then (1 : ℝ) else 0)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hK]
    ring
  have hswap : ∑ b : Fin T → Bool, ∑ s, ∑ t, K s t *
        ((r s - (if b s then (1 : ℝ) else 0)) * (r t - (if b t then (1 : ℝ) else 0))) *
        (∏ i, (if b i then p i else 1 - p i))
      = ∑ s, ∑ t, K s t *
        ((r s - p s) * (r t - p t) + (if s = t then p s * (1 - p s) else 0)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← atb_bernoulli_cross_moment r p s t, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hsplit : ∑ s, ∑ t, K s t *
        ((r s - p s) * (r t - p t) + (if s = t then p s * (1 - p s) else 0))
      = (∑ s, ∑ t, K s t * ((r s - p s) * (r t - p t)))
        + ∑ s, ∑ t, K s t * (if s = t then p s * (1 - p s) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  have hdiag : ∑ s, ∑ t, K s t * (if s = t then p s * (1 - p s) else 0)
      = ∑ t, p t * (1 - p t) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_eq_single s (fun t _ hts => by simp [Ne.symm hts]) (by simp), if_pos rfl, hK]
    by_cases hq : r s < q
    · simp [hq, not_le.2 hq]
    · simp [hq, not_lt.1 hq]
  rw [Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => hexpand b), hswap, hsplit, hdiag,
    ← atb_bin_sum_sq_expand r q (fun t => r t - p t)]

@[blueprint "thm:atb-error-decomposition"
  (statement := /-- Let $T$ be a natural number, let $\vreport : \mathrm{Fin}\,T \to \mathbb R$ be an arbitrary
  family, and let $\vpred : \mathrm{Fin}\,T \to \mathbb R$ be a family satisfying $p_t \in [0,1]$ for every
  $t \in \mathrm{Fin}\,T$, so that each coordinate law $\mathrm{Ber}(p_t)$ of \cref{def:state-bernoulli} is a
  genuine Bernoulli probability measure with mean $p_t$ and variance $p_t(1 - p_t)$. Let $\vstate \sim \vpred$
  be distributed according to the joint state law $\mathbb P_{\vpred}$ of \cref{def:state-measure}. Then the
  expected averaged two-bin error (\cref{def:averaged-two-bin}) of the fixed report $\vreport$ against the
  random states admits the decomposition
  \[
    \mathbb E_{\vstate \sim \vpred}\big[\atb(\vreport,\vstate)\big]
      \;=\; \atb(\vreport,\vpred) \;+\; \frac{1}{T^2}\sum_{t \in \mathrm{Fin}\,T} p_t\,(1 - p_t) ,
  \]
  the expectation on the left being the Bochner integral of $\vstate \mapsto \atb(\vreport,\vstate)$ over
  $\mathbb R^{\mathrm{Fin}\,T}$ with respect to $\mathbb P_{\vpred}$. Here the coefficient $1/T^2$ is read with
  the convention $1/0^2 = 0$, so that for $T = 0$ the identity holds with both sides equal to $0$. -/)
  (proof := /-- Since $p_i \in [0,1]$ for every $i$, \cref{lem:atb-state-measure-integral-eq-sum} applies to the
  function $\vstate \mapsto \atb(\vreport,\vstate)$ and turns the expectation on the left into the finite sum
  \[
    \mathbb E_{\vstate \sim \vpred}\big[\atb(\vreport,\vstate)\big]
      = \sum_{b} \Big(\prod_{i} \big(p_i\ \text{if}\ b_i,\ 1 - p_i\ \text{otherwise}\big)\Big)\,
        \atb(\vreport, y(b)),
  \]
  indexed by the sign patterns $b : \mathrm{Fin}\,T \to \{\top,\bot\}$, where $y(b)_i = 1$ if $b_i$ holds and
  $y(b)_i = 0$ otherwise.

  Unfolding \cref{def:averaged-two-bin}, each $\atb(\vreport, y(b))$ is an integral in the threshold variable
  $q$ over $[0,1]$, and the constant weight of $b$ may be moved inside that integral by linearity of the
  interval integral in the integrand. Each of the finitely many resulting integrands is interval integrable by
  \cref{lem:atb-integrand-interval-integrable}, applied with the state family $y(b)$, and remains so after
  multiplication by the constant weight; hence the finite sum of the integrals is the integral of the finite sum,
  and the whole left-hand side is a single interval integral over $q \in [0,1]$ of
  $\sum_b \big(\prod_i(\cdots)\big)\,\tfrac{1}{T^2}\big(\cdots\big)$.

  The resulting integrand is evaluated for each fixed $q$. Pulling the constant $1/T^2$ out of the sum over $b$
  and applying \cref{lem:atb-pointwise-decomposition} shows that it equals
  \[
    \frac{1}{T^2}\left(\Big(\sum_{t : r_t < q}(r_t - p_t)\Big)^2 + \Big(\sum_{t : q \le r_t}(r_t - p_t)\Big)^2\right)
      + \frac{1}{T^2}\sum_{t} p_t(1 - p_t),
  \]
  for every $q$, so the two integrands agree on the interval and the integrals coincide. The first summand is
  interval integrable by \cref{lem:atb-integrand-interval-integrable} applied with the state family $\vpred$,
  and the second summand is a constant, hence interval integrable; therefore the integral splits as the sum of
  the two integrals. The first integral is exactly $\atb(\vreport,\vpred)$ by
  \cref{def:averaged-two-bin}, and the integral of the constant over the interval from $0$ to $1$ is that
  constant times the length $1 - 0 = 1$, namely $\tfrac{1}{T^2}\sum_t p_t(1 - p_t)$. This gives the claimed
  decomposition. -/)
  (title := /-- Error decomposition for ATB -/)
  (latexEnv := "theorem")]
theorem atb_error_decomposition {T : ℕ} (r p : Fin T → ℝ)
    (hp : ∀ t, p t ∈ Set.Icc (0 : ℝ) 1) :
    ∫ y, averaged_two_bin r y ∂(state_measure p) =
      averaged_two_bin r p + (1 / (T : ℝ) ^ 2) * ∑ t, p t * (1 - p t) := by
  classical
  have hptw : ∀ q : ℝ, ∑ b : Fin T → Bool, (∏ i, (if b i then p i else 1 - p i)) *
      ((1 / (T : ℝ) ^ 2) *
        ((∑ t ∈ Finset.univ.filter (fun t => r t < q), (r t - (if b t then (1 : ℝ) else 0))) ^ 2 +
         (∑ t ∈ Finset.univ.filter (fun t => q ≤ r t), (r t - (if b t then (1 : ℝ) else 0))) ^ 2))
      = (1 / (T : ℝ) ^ 2) *
          ((∑ t ∈ Finset.univ.filter (fun t => r t < q), (r t - p t)) ^ 2 +
           (∑ t ∈ Finset.univ.filter (fun t => q ≤ r t), (r t - p t)) ^ 2)
        + (1 / (T : ℝ) ^ 2) * ∑ t, p t * (1 - p t) := by
    intro q
    have hfac : ∀ b : Fin T → Bool, (∏ i, (if b i then p i else 1 - p i)) *
        ((1 / (T : ℝ) ^ 2) *
          ((∑ t ∈ Finset.univ.filter (fun t => r t < q), (r t - (if b t then (1 : ℝ) else 0))) ^ 2 +
           (∑ t ∈ Finset.univ.filter (fun t => q ≤ r t), (r t - (if b t then (1 : ℝ) else 0))) ^ 2))
        = (1 / (T : ℝ) ^ 2) * ((∏ i, (if b i then p i else 1 - p i)) *
          ((∑ t ∈ Finset.univ.filter (fun t => r t < q), (r t - (if b t then (1 : ℝ) else 0))) ^ 2 +
           (∑ t ∈ Finset.univ.filter (fun t => q ≤ r t), (r t - (if b t then (1 : ℝ) else 0))) ^ 2)) := by
      intro b
      ring
    rw [Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => hfac b), ← Finset.mul_sum,
      atb_pointwise_decomposition r p q]
    ring
  rw [atb_state_measure_integral_eq_sum p hp (fun y => averaged_two_bin r y)]
  simp only [averaged_two_bin]
  rw [Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) =>
      (intervalIntegral.integral_const_mul (∏ i, (if b i then p i else 1 - p i))
        (fun q => (1 / (T : ℝ) ^ 2) *
          ((∑ t ∈ Finset.univ.filter (fun t => r t < q),
              (r t - (if b t then (1 : ℝ) else 0))) ^ 2 +
           (∑ t ∈ Finset.univ.filter (fun t => q ≤ r t),
              (r t - (if b t then (1 : ℝ) else 0))) ^ 2))).symm),
    ← intervalIntegral.integral_finset_sum (fun b _ =>
      (atb_integrand_interval_integrable r (fun i => if b i then (1 : ℝ) else 0)).const_mul _),
    intervalIntegral.integral_congr (g := fun q => (1 / (T : ℝ) ^ 2) *
        ((∑ t ∈ Finset.univ.filter (fun t => r t < q), (r t - p t)) ^ 2 +
         (∑ t ∈ Finset.univ.filter (fun t => q ≤ r t), (r t - p t)) ^ 2)
      + (1 / (T : ℝ) ^ 2) * ∑ t, p t * (1 - p t)) (fun q _ => hptw q),
    intervalIntegral.integral_add
      (atb_integrand_interval_integrable r p) intervalIntegrable_const,
    intervalIntegral.integral_const]
  simp

@[blueprint "thm:atb-interim-truthful"
  (statement := /-- Let $T$ be a positive integer and let $\vpred : \mathrm{Fin}\,T \to \mathbb R$ be a ground-truth
  family satisfying $p_t \in [0,1]$ for every $t \in \mathrm{Fin}\,T$, so that each coordinate law
  $\mathrm{Ber}(p_t)$ of \cref{def:state-bernoulli} is a genuine Bernoulli probability measure with mean $p_t$,
  and let $\vstate \sim \vpred$ be the associated joint state law (\cref{def:state-measure}). Then the averaged
  two-bin calibration error is \emph{interim truthful}: for every report $\vreport : \mathrm{Fin}\,T \to \mathbb R$
  satisfying $r_t \in [0,1]$ for every $t \in \mathrm{Fin}\,T$,
  \[
    \mathbb E_{\vstate \sim \vpred}\big[\atb(\vpred,\vstate)\big]
      \;\le\; \mathbb E_{\vstate \sim \vpred}\big[\atb(\vreport,\vstate)\big].
  \] -/)
  (proof := /-- Both sides are expectations under the joint state law of the ground-truth family $\vpred$, whose
  coordinates satisfy $p_t \in [0,1]$ for every $t$, so the error decomposition of
  \cref{thm:atb-error-decomposition} applies verbatim to each side. On the left, taking $\vreport = \vpred$ gives
  $\mathbb E_{\vstate \sim \vpred}[\atb(\vpred,\vstate)] = \atb(\vpred,\vpred) + \tfrac{1}{T^2}\sum_t p_t(1-p_t)$,
  and $\atb(\vpred,\vpred) = 0$ by \cref{lem:atb-self-zero}, so the left-hand side equals
  $\tfrac{1}{T^2}\sum_t p_t(1-p_t)$. On the right,
  $\mathbb E_{\vstate \sim \vpred}[\atb(\vreport,\vstate)] = \atb(\vreport,\vpred) + \tfrac{1}{T^2}\sum_t p_t(1-p_t)$,
  and $\atb(\vreport,\vpred) \ge 0$ by \cref{lem:atb-nonneg}. Subtracting the common variance term
  $\tfrac{1}{T^2}\sum_t p_t(1-p_t)$ from both sides reduces the claim to $0 \le \atb(\vreport,\vpred)$, which holds. -/)
  (title := /-- Interim truthfulness of ATB -/)
  (latexEnv := "theorem")]
theorem atb_interim_truthful {T : ℕ} (hT : 0 < T) (r p : Fin T → ℝ)
    (hr : ∀ t, r t ∈ Set.Icc (0 : ℝ) 1) (hp : ∀ t, p t ∈ Set.Icc (0 : ℝ) 1) :
    ∫ y, averaged_two_bin p y ∂(state_measure p) ≤
      ∫ y, averaged_two_bin r y ∂(state_measure p) := by
  rw [atb_error_decomposition p p hp, atb_error_decomposition r p hp, atb_self_zero]
  simpa [add_comm] using add_le_add_right (atb_nonneg r p)
    ((1 / (T : ℝ) ^ 2) * ∑ t, p t * (1 - p t))

@[blueprint "def:ex-ante-atb-error"
  (statement := /-- Let $T$ be a positive integer, let $X$ be a measurable space, and let $D$ be a distribution of
  pairs $(x,y) \in X \times \mathbb R$. For a predictor $r : X \to \mathbb R$, the \emph{expected ex-ante ATB error}
  of $r$ under $D$ is
  \[
    \mathrm{ExAnteATB}_D(r) \;=\;
      \mathbb E_{S \sim D^{\otimes T}}\Big[\atb\big((r(x_t))_{t},\,(y_t)_{t}\big)\Big],
  \]
  where $S = ((x_t,y_t))_{t \in \mathrm{Fin}\,T}$ is a sample of $T$ i.i.d.\ draws from $D$ (distributed according
  to the product measure $D^{\otimes T}$), the report sequence is $(r(x_t))_t$, and the state sequence is
  $(y_t)_t$; here $\atb$ is the averaged two-bin error of \cref{def:averaged-two-bin}. This coincides with the
  expected error $\mathbb E_S[\CAL_{D_S}(r)]$ of the ATB metric evaluated on the empirical distribution $D_S$. -/)
  (title := /-- Expected ex-ante ATB error of a predictor -/)
  (latexEnv := "definition")]
noncomputable def ex_ante_atb_error {X : Type*} [MeasurableSpace X] (T : ℕ)
    (D : Measure (X × ℝ)) (r : X → ℝ) : ℝ :=
  ∫ s : Fin T → X × ℝ,
      averaged_two_bin (fun t => r (s t).1) (fun t => (s t).2)
    ∂(Measure.pi fun _ => D)

@[blueprint "def:is-ground-truth"
  (statement := /-- Let $X$ be a measurable space and let $D$ be a distribution of pairs $(x,y) \in X \times \mathbb R$.
  A predictor $p : X \to \mathbb R$ is a \emph{ground-truth predictor} for $D$ if, as a function on $X \times \mathbb R$,
  $(x,y) \mapsto p(x)$ agrees $D$-almost everywhere with the conditional expectation
  $\mathbb E_D[\,y \mid x\,]$, that is, with the conditional expectation of the label $(x,y) \mapsto y$ given the
  $\sigma$-algebra generated by the first coordinate $x$. Equivalently, $p(x) = \mathbb E[y \mid x]$ almost surely. -/)
  (title := /-- Ground-truth predictor as a conditional expectation -/)
  (latexEnv := "definition")]
def is_ground_truth {X : Type*} [MeasurableSpace X]
    (D : Measure (X × ℝ)) (p : X → ℝ) : Prop :=
  (fun z : X × ℝ => p z.1) =ᵐ[D]
    condExp (MeasurableSpace.comap Prod.fst inferInstance) D (fun z => z.2)

@[blueprint "lem:atb-integral-prod-mul"
  (statement := /-- Let $\mu$ and $\nu$ be probability measures and let $f$ and $g$ be bounded measurable real-valued functions. Then the integral of $(x,y) \mapsto f(x)g(y)$ under $\mu \otimes \nu$ factors as the product of the two marginal integrals. -/)
  (proof := /-- Decompose each function into its positive and negative parts. For each of the four resulting nonnegative product terms, the factorization follows from Tonelli's theorem for lower Lebesgue integrals. Convert back to Bochner integrals and use linearity. -/)
  (title := /-- Factorization of a bounded product integral -/)
  (latexEnv := "lemma")]
lemma atb_integral_prod_mul {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : A → ℝ) (g : B → ℝ) (Cf Cg : ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ x, |f x| ≤ Cf) (hgb : ∀ y, |g y| ≤ Cg) :
    ∫ z, f z.1 * g z.2 ∂(μ.prod ν) = (∫ x, f x ∂μ) * ∫ y, g y ∂ν := by
  have hnonneg (a : A → ℝ) (b : B → ℝ) (Ca Cb : ℝ)
      (ha : Measurable a) (hb : Measurable b)
      (hai : Integrable a μ) (hbi : Integrable b ν)
      (han : ∀ x, 0 ≤ a x) (hbn : ∀ y, 0 ≤ b y)
      (hab : ∀ x, a x ≤ Ca) (hbb : ∀ y, b y ≤ Cb) :
      ∫ z, a z.1 * b z.2 ∂(μ.prod ν) = (∫ x, a x ∂μ) * ∫ y, b y ∂ν := by
    have hpmeas : AEStronglyMeasurable (fun z : A × B => a z.1 * b z.2) (μ.prod ν) :=
      ((ha.comp measurable_fst).mul (hb.comp measurable_snd)).aestronglyMeasurable
    have hpint : Integrable (fun z : A × B => a z.1 * b z.2) (μ.prod ν) := by
      exact (integrable_const (|Ca| * |Cb|)).mono' hpmeas
        (Filter.Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (han z.1) (hbn z.2))]
          exact mul_le_mul (le_trans (hab z.1) (le_abs_self Ca))
            (le_trans (hbb z.2) (le_abs_self Cb)) (hbn z.2) (abs_nonneg Ca))
    have hpnonneg : 0 ≤ ∫ z : A × B, a z.1 * b z.2 ∂(μ.prod ν) :=
      integral_nonneg (fun z => mul_nonneg (han z.1) (hbn z.2))
    have hanint : 0 ≤ ∫ x, a x ∂μ := integral_nonneg han
    have hbnint : 0 ≤ ∫ y, b y ∂ν := integral_nonneg hbn
    refine (ENNReal.ofReal_eq_ofReal_iff hpnonneg (mul_nonneg hanint hbnint)).mp ?_
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hpint
      (Filter.Eventually.of_forall fun z => mul_nonneg (han z.1) (hbn z.2))]
    rw [ENNReal.ofReal_mul hanint]
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hai
      (Filter.Eventually.of_forall han)]
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hbi
      (Filter.Eventually.of_forall hbn)]
    calc
      (∫⁻ z : A × B, ENNReal.ofReal (a z.1 * b z.2) ∂(μ.prod ν))
          = ∫⁻ z : A × B, ENNReal.ofReal (a z.1) * ENNReal.ofReal (b z.2) ∂(μ.prod ν) := by
              apply MeasureTheory.lintegral_congr
              intro z
              rw [ENNReal.ofReal_mul (han z.1)]
      _ = (∫⁻ x, ENNReal.ofReal (a x) ∂μ) * ∫⁻ y, ENNReal.ofReal (b y) ∂ν :=
        MeasureTheory.lintegral_prod_mul ha.ennreal_ofReal.aemeasurable
          hb.ennreal_ofReal.aemeasurable
  let fp : A → ℝ := fun x => max (f x) 0
  let fn : A → ℝ := fun x => max (-f x) 0
  let gp : B → ℝ := fun y => max (g y) 0
  let gn : B → ℝ := fun y => max (-g y) 0
  have hfp : Measurable fp := hf.max measurable_const
  have hfn : Measurable fn := hf.neg.max measurable_const
  have hgp : Measurable gp := hg.max measurable_const
  have hgn : Measurable gn := hg.neg.max measurable_const
  have hfpn : ∀ x, 0 ≤ fp x := fun x => le_max_right _ _
  have hfnn : ∀ x, 0 ≤ fn x := fun x => le_max_right _ _
  have hgpn : ∀ y, 0 ≤ gp y := fun y => le_max_right _ _
  have hgnn : ∀ y, 0 ≤ gn y := fun y => le_max_right _ _
  have hfpb : ∀ x, fp x ≤ |Cf| := fun x => max_le
    (le_trans (le_trans (le_abs_self (f x)) (hfb x)) (le_abs_self Cf)) (abs_nonneg Cf)
  have hfnb : ∀ x, fn x ≤ |Cf| := fun x => max_le
    (le_trans (le_trans (neg_le_abs (f x)) (hfb x)) (le_abs_self Cf)) (abs_nonneg Cf)
  have hgpb : ∀ y, gp y ≤ |Cg| := fun y => max_le
    (le_trans (le_trans (le_abs_self (g y)) (hgb y)) (le_abs_self Cg)) (abs_nonneg Cg)
  have hgnb : ∀ y, gn y ≤ |Cg| := fun y => max_le
    (le_trans (le_trans (neg_le_abs (g y)) (hgb y)) (le_abs_self Cg)) (abs_nonneg Cg)
  have hfpi : Integrable fp μ := (integrable_const |Cf|).mono'
    hfp.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hfpn x)]
      exact hfpb x)
  have hfni : Integrable fn μ := (integrable_const |Cf|).mono'
    hfn.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hfnn x)]
      exact hfnb x)
  have hgpi : Integrable gp ν := (integrable_const |Cg|).mono'
    hgp.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hgpn y)]
      exact hgpb y)
  have hgni : Integrable gn ν := (integrable_const |Cg|).mono'
    hgn.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hgnn y)]
      exact hgnb y)
  have hprodint (a : A → ℝ) (b : B → ℝ) (ha : Measurable a) (hb : Measurable b)
      (han : ∀ x, 0 ≤ a x) (hbn : ∀ y, 0 ≤ b y)
      (hab : ∀ x, a x ≤ |Cf|) (hbb : ∀ y, b y ≤ |Cg|) :
      Integrable (fun z : A × B => a z.1 * b z.2) (μ.prod ν) := by
    exact (integrable_const (|Cf| * |Cg|)).mono'
      ((ha.comp measurable_fst).mul (hb.comp measurable_snd)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (han z.1) (hbn z.2))]
        exact mul_le_mul (hab z.1) (hbb z.2) (hbn z.2) (abs_nonneg Cf))
  have hfpgp := hprodint fp gp hfp hgp hfpn hgpn hfpb hgpb
  have hfpgn := hprodint fp gn hfp hgn hfpn hgnn hfpb hgnb
  have hfngp := hprodint fn gp hfn hgp hfnn hgpn hfnb hgpb
  have hfngn := hprodint fn gn hfn hgn hfnn hgnn hfnb hgnb
  have hfdec : ∀ x, f x = fp x - fn x := by
    intro x
    dsimp [fp, fn]
    rcases le_total 0 (f x) with hx | hx
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
      ring
    · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
      ring
  have hgdec : ∀ y, g y = gp y - gn y := by
    intro y
    dsimp [gp, gn]
    rcases le_total 0 (g y) with hy | hy
    · rw [max_eq_left hy, max_eq_right (neg_nonpos.mpr hy)]
      ring
    · rw [max_eq_right hy, max_eq_left (neg_nonneg.mpr hy)]
      ring
  have hinter :
      (∫ z, f z.1 * g z.2 ∂(μ.prod ν)) =
        (∫ z, fp z.1 * gp z.2 ∂(μ.prod ν))
          - (∫ z, fp z.1 * gn z.2 ∂(μ.prod ν))
          - (∫ z, fn z.1 * gp z.2 ∂(μ.prod ν))
          + ∫ z, fn z.1 * gn z.2 ∂(μ.prod ν) := by
    calc
      (∫ z, f z.1 * g z.2 ∂(μ.prod ν)) =
          ∫ z, fp z.1 * gp z.2 - fp z.1 * gn z.2 - fn z.1 * gp z.2
            + fn z.1 * gn z.2 ∂(μ.prod ν) := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun z => by
                change f z.1 * g z.2 = _
                rw [hfdec z.1, hgdec z.2]
                ring
      _ = (∫ z, fp z.1 * gp z.2 ∂(μ.prod ν))
          - (∫ z, fp z.1 * gn z.2 ∂(μ.prod ν))
          - (∫ z, fn z.1 * gp z.2 ∂(μ.prod ν))
          + ∫ z, fn z.1 * gn z.2 ∂(μ.prod ν) := by
            calc
              (∫ z, fp z.1 * gp z.2 - fp z.1 * gn z.2 - fn z.1 * gp z.2
                  + fn z.1 * gn z.2 ∂(μ.prod ν)) =
                  (∫ z, fp z.1 * gp z.2 - fp z.1 * gn z.2 - fn z.1 * gp z.2
                    ∂(μ.prod ν)) + ∫ z, fn z.1 * gn z.2 ∂(μ.prod ν) := by
                    simpa only [Pi.add_apply, Pi.sub_apply] using
                      integral_add ((hfpgp.sub hfpgn).sub hfngp) hfngn
              _ = ((∫ z, fp z.1 * gp z.2 - fp z.1 * gn z.2 ∂(μ.prod ν))
                    - ∫ z, fn z.1 * gp z.2 ∂(μ.prod ν))
                    + ∫ z, fn z.1 * gn z.2 ∂(μ.prod ν) := by
                    simpa only [Pi.sub_apply] using congrArg
                      (fun x => x + ∫ z, fn z.1 * gn z.2 ∂(μ.prod ν))
                      (integral_sub (hfpgp.sub hfpgn) hfngp)
              _ = (∫ z, fp z.1 * gp z.2 ∂(μ.prod ν))
                    - (∫ z, fp z.1 * gn z.2 ∂(μ.prod ν))
                    - (∫ z, fn z.1 * gp z.2 ∂(μ.prod ν))
                    + ∫ z, fn z.1 * gn z.2 ∂(μ.prod ν) := by
                    simpa only [Pi.sub_apply] using congrArg
                      (fun x => x - (∫ z, fn z.1 * gp z.2 ∂(μ.prod ν))
                        + ∫ z, fn z.1 * gn z.2 ∂(μ.prod ν))
                      (integral_sub hfpgp hfpgn)
  have hfintdec : (∫ x, f x ∂μ) = (∫ x, fp x ∂μ) - ∫ x, fn x ∂μ := by
    calc
      (∫ x, f x ∂μ) = ∫ x, fp x - fn x ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall hfdec)
      _ = (∫ x, fp x ∂μ) - ∫ x, fn x ∂μ := integral_sub hfpi hfni
  have hgintdec : (∫ y, g y ∂ν) = (∫ y, gp y ∂ν) - ∫ y, gn y ∂ν := by
    calc
      (∫ y, g y ∂ν) = ∫ y, gp y - gn y ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall hgdec)
      _ = (∫ y, gp y ∂ν) - ∫ y, gn y ∂ν := integral_sub hgpi hgni
  rw [hinter, hfintdec, hgintdec,
    hnonneg fp gp |Cf| |Cg| hfp hgp hfpi hgpi hfpn hgpn hfpb hgpb,
    hnonneg fp gn |Cf| |Cg| hfp hgn hfpi hgni hfpn hgnn hfpb hgnb,
    hnonneg fn gp |Cf| |Cg| hfn hgp hfni hgpi hfnn hgpn hfnb hgpb,
    hnonneg fn gn |Cf| |Cg| hfn hgn hfni hgni hfnn hgnn hfnb hgnb]
  ring

@[blueprint "lem:atb-pair-integral-pi"
  (statement := /-- Let $T$ be a nonnegative integer, let $D$ be a probability measure on $X\times\mathbb R$, and let $f:X\times\mathbb R\to\mathbb R$ be measurable with $|f|\le C$. For an i.i.d. sample $S=(S_t)_{t\in\mathrm{Fin}\,T}$ with law $D^{\otimes T}$,
  \[
    \int \Big(\sum_t f(S_t)\Big)^2\,dD^{\otimes T}
      =T\int f^2\,dD+T(T-1)\Big(\int f\,dD\Big)^2.
  \] -/)
  (proof := /-- Expand the square as a double finite sum. Every diagonal term is $\int f^2\,dD$ by the measure-preserving coordinate projection. For two distinct coordinates, split the product measure by the measure-preserving equivalence that removes one coordinate and apply the bounded product-factorization lemma \cref{lem:atb-integral-prod-mul}; the term is then $(\int f\,dD)^2$. There are $T$ diagonal terms and $T(T-1)$ ordered off-diagonal terms, which gives the stated identity. -/)
  (title := /-- Second moment of a coordinate sum -/)
  (latexEnv := "lemma")]
lemma atb_pair_integral_pi {X : Type*} [MeasurableSpace X] (T : ℕ)
    (D : Measure (X × ℝ)) [IsProbabilityMeasure D] (f : X × ℝ → ℝ) (C : ℝ)
    (hf : Measurable f) (hb : ∀ z, |f z| ≤ C) :
    ∫ s : Fin T → X × ℝ, (∑ t, f (s t)) ^ 2 ∂(Measure.pi fun _ => D)
      = (T : ℝ) * (∫ z, f z ^ 2 ∂D)
        + (T : ℝ) * ((T : ℝ) - 1) * (∫ z, f z ∂D) ^ 2 := by
  classical
  cases T with
  | zero => simp
  | succ n =>
    have hcross (t u : Fin (n + 1)) (htu : t ≠ u) :
        ∫ s : Fin (n + 1) → X × ℝ, f (s t) * f (s u)
          ∂(Measure.pi fun _ => D) = (∫ z, f z ∂D) ^ 2 := by
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq htu.symm
      have hsecond : Measurable (fun s : Fin n → X × ℝ => f (s j)) :=
        hf.comp (measurable_pi_apply j)
      have hsecondb : ∀ s : Fin n → X × ℝ, |f (s j)| ≤ C := fun s => hb (s j)
      have hfactor := atb_integral_prod_mul D (Measure.pi fun _ : Fin n => D)
        f (fun s : Fin n → X × ℝ => f (s j)) C C hf hsecond hb hsecondb
      have heval :
          (∫ s : Fin n → X × ℝ, f (s j) ∂(Measure.pi fun _ => D)) = ∫ z, f z ∂D := by
        let mp := MeasureTheory.measurePreserving_eval (fun _ : Fin n => D) j
        have hm : AEStronglyMeasurable f (Measure.map (Function.eval j)
            (Measure.pi fun _ : Fin n => D)) := by
          rw [mp.map_eq]
          exact hf.aestronglyMeasurable
        calc
          (∫ s : Fin n → X × ℝ, f (s j) ∂(Measure.pi fun _ => D)) =
              ∫ z, f z ∂(Measure.map (Function.eval j) (Measure.pi fun _ : Fin n => D)) :=
                (MeasureTheory.integral_map mp.measurable.aemeasurable hm).symm
          _ = ∫ z, f z ∂D := by rw [mp.map_eq]
      rw [heval] at hfactor
      rw [← sq] at hfactor
      have hmap := (MeasureTheory.measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => D) t).integral_comp'
        (fun z => f z.1 * f (z.2 j))
      rw [hfactor] at hmap
      simpa [MeasurableEquiv.piFinSuccAbove_apply, Fin.removeNth_apply, hj] using hmap
    have hdiag (t : Fin (n + 1)) :
        ∫ s : Fin (n + 1) → X × ℝ, f (s t) * f (s t)
          ∂(Measure.pi fun _ => D) = ∫ z, f z * f z ∂D := by
      let mp := MeasureTheory.measurePreserving_eval (fun _ : Fin (n + 1) => D) t
      have hm : AEStronglyMeasurable (fun z => f z * f z)
          (Measure.map (Function.eval t) (Measure.pi fun _ : Fin (n + 1) => D)) := by
        rw [mp.map_eq]
        exact (hf.mul hf).aestronglyMeasurable
      calc
        (∫ s : Fin (n + 1) → X × ℝ, f (s t) * f (s t)
            ∂(Measure.pi fun _ => D)) =
            ∫ z, f z * f z
              ∂(Measure.map (Function.eval t) (Measure.pi fun _ : Fin (n + 1) => D)) :=
                (MeasureTheory.integral_map mp.measurable.aemeasurable hm).symm
        _ = ∫ z, f z * f z ∂D := by rw [mp.map_eq]
    have hint (t u : Fin (n + 1)) :
        Integrable (fun s : Fin (n + 1) → X × ℝ => f (s t) * f (s u))
          (Measure.pi fun _ => D) := by
      exact (integrable_const (|C| * |C|)).mono'
        ((hf.comp (measurable_pi_apply t)).mul
          (hf.comp (measurable_pi_apply u))).aestronglyMeasurable
        (Filter.Eventually.of_forall fun s => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul
            (le_trans (hb (s t)) (le_abs_self C))
            (le_trans (hb (s u)) (le_abs_self C))
            (abs_nonneg _) (abs_nonneg C))
    simp_rw [sq, Finset.sum_mul_sum]
    have hinnerint (t : Fin (n + 1)) :
        (∫ s : Fin (n + 1) → X × ℝ, ∑ u, f (s t) * f (s u)
            ∂(Measure.pi fun _ => D)) =
          ∑ u, ∫ s : Fin (n + 1) → X × ℝ, f (s t) * f (s u)
            ∂(Measure.pi fun _ => D) := by
      rw [integral_finset_sum]
      exact fun u _ => hint t u
    rw [integral_finset_sum]
    · simp_rw [hinnerint]
      have hterm (t u : Fin (n + 1)) :
          (∫ s : Fin (n + 1) → X × ℝ, f (s t) * f (s u)
              ∂(Measure.pi fun _ => D)) =
            if t = u then (∫ z, f z * f z ∂D) else (∫ z, f z ∂D) ^ 2 := by
        by_cases htu : t = u
        · subst u
          simpa using hdiag t
        · simpa [htu] using hcross t u htu
      simp_rw [hterm]
      have hsum (t : Fin (n + 1)) :
          (∑ u : Fin (n + 1), if t = u then (∫ z, f z * f z ∂D)
            else (∫ z, f z ∂D) ^ 2) =
            (∫ z, f z * f z ∂D) + n * (∫ z, f z ∂D) ^ 2 := by
        calc
          (∑ u : Fin (n + 1), if t = u then (∫ z, f z * f z ∂D)
              else (∫ z, f z ∂D) ^ 2) =
              (if t = t then (∫ z, f z * f z ∂D) else (∫ z, f z ∂D) ^ 2)
                + ∑ u ∈ Finset.univ.erase t,
                    (if t = u then (∫ z, f z * f z ∂D) else (∫ z, f z ∂D) ^ 2) :=
              (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ t)).symm
          _ = (∫ z, f z * f z ∂D)
                + ∑ u ∈ Finset.univ.erase t, (∫ z, f z ∂D) ^ 2 := by
              congr 1
              · simp
              · apply Finset.sum_congr rfl
                intro u hu
                simp only [Finset.mem_erase] at hu
                simp [hu.1.symm]
          _ = (∫ z, f z * f z ∂D) + n * (∫ z, f z ∂D) ^ 2 := by
              simp
      simp_rw [hsum]
      simp
      ring
    · exact fun t _ => integrable_finset_sum _ fun u _ => hint t u

@[blueprint "lem:atb-integral-swap-nonnegative"
  (statement := /-- Let $\mu$ and $\nu$ be finite measures. If $F$ is a bounded, measurable, nonnegative real-valued function on the product space, then its two iterated integrals agree. -/)
  (proof := /-- Convert both iterated Bochner integrals to lower Lebesgue integrals using nonnegativity and integrability from the uniform bound. Tonelli's theorem identifies both orders with the lower Lebesgue integral on the product measure. -/)
  (title := /-- Tonelli swap for bounded nonnegative functions -/)
  (latexEnv := "lemma")]
lemma atb_integral_swap_nonnegative {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (F : A × B → ℝ) (C : ℝ) (hF : Measurable F)
    (h0 : ∀ z, 0 ≤ F z) (hC : ∀ z, F z ≤ C) :
    (∫ x, ∫ y, F (x, y) ∂ν ∂μ) = ∫ y, ∫ x, F (x, y) ∂μ ∂ν := by
  have hsection_left (x : A) : Integrable (fun y => F (x, y)) ν := by
    exact (integrable_const |C|).mono'
      (hF.comp measurable_prodMk_left).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 (x, y))]
        exact le_trans (hC (x, y)) (le_abs_self C))
  have hsection_right (y : B) : Integrable (fun x => F (x, y)) μ := by
    exact (integrable_const |C|).mono'
      (hF.comp measurable_prodMk_right).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 (x, y))]
        exact le_trans (hC (x, y)) (le_abs_self C))
  have hlinleft : Measurable (fun x => ∫⁻ y, ENNReal.ofReal (F (x, y)) ∂ν) :=
    hF.ennreal_ofReal.lintegral_prod_right
  have hlinright : Measurable (fun y => ∫⁻ x, ENNReal.ofReal (F (x, y)) ∂μ) :=
    hF.ennreal_ofReal.lintegral_prod_left
  have hleft_nonneg : ∀ x, 0 ≤ ∫ y, F (x, y) ∂ν :=
    fun x => integral_nonneg (fun y => h0 (x, y))
  have hright_nonneg : ∀ y, 0 ≤ ∫ x, F (x, y) ∂μ :=
    fun y => integral_nonneg (fun x => h0 (x, y))
  have hleft_eq (x : A) :
      (∫ y, F (x, y) ∂ν) = ENNReal.toReal (∫⁻ y, ENNReal.ofReal (F (x, y)) ∂ν) := by
    calc
      (∫ y, F (x, y) ∂ν) = ENNReal.toReal (ENNReal.ofReal (∫ y, F (x, y) ∂ν)) :=
        (ENNReal.toReal_ofReal (hleft_nonneg x)).symm
      _ = ENNReal.toReal (∫⁻ y, ENNReal.ofReal (F (x, y)) ∂ν) := congrArg _
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hsection_left x)
          (Filter.Eventually.of_forall fun y => h0 (x, y)))
  have hright_eq (y : B) :
      (∫ x, F (x, y) ∂μ) = ENNReal.toReal (∫⁻ x, ENNReal.ofReal (F (x, y)) ∂μ) := by
    calc
      (∫ x, F (x, y) ∂μ) = ENNReal.toReal (ENNReal.ofReal (∫ x, F (x, y) ∂μ)) :=
        (ENNReal.toReal_ofReal (hright_nonneg y)).symm
      _ = ENNReal.toReal (∫⁻ x, ENNReal.ofReal (F (x, y)) ∂μ) := congrArg _
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hsection_right y)
          (Filter.Eventually.of_forall fun x => h0 (x, y)))
  have hleft_meas : Measurable (fun x => ∫ y, F (x, y) ∂ν) := by
    rw [show (fun x => ∫ y, F (x, y) ∂ν) =
      (fun x => ENNReal.toReal (∫⁻ y, ENNReal.ofReal (F (x, y)) ∂ν)) from funext hleft_eq]
    exact ENNReal.measurable_toReal.comp hlinleft
  have hright_meas : Measurable (fun y => ∫ x, F (x, y) ∂μ) := by
    rw [show (fun y => ∫ x, F (x, y) ∂μ) =
      (fun y => ENNReal.toReal (∫⁻ x, ENNReal.ofReal (F (x, y)) ∂μ)) from funext hright_eq]
    exact ENNReal.measurable_toReal.comp hlinright
  have hleft_bound : ∀ x, ‖∫ y, F (x, y) ∂ν‖ ≤ |C| * ν.real Set.univ := by
    intro x
    exact MeasureTheory.norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 (x, y))]
        exact le_trans (hC (x, y)) (le_abs_self C))
  have hright_bound : ∀ y, ‖∫ x, F (x, y) ∂μ‖ ≤ |C| * μ.real Set.univ := by
    intro y
    exact MeasureTheory.norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 (x, y))]
        exact le_trans (hC (x, y)) (le_abs_self C))
  have houter_left : Integrable (fun x => ∫ y, F (x, y) ∂ν) μ := by
    exact (integrable_const (|C| * ν.real Set.univ)).mono'
      hleft_meas.aestronglyMeasurable (Filter.Eventually.of_forall hleft_bound)
  have houter_right : Integrable (fun y => ∫ x, F (x, y) ∂μ) ν := by
    exact (integrable_const (|C| * μ.real Set.univ)).mono'
      hright_meas.aestronglyMeasurable (Filter.Eventually.of_forall hright_bound)
  have hlin_swap :
      (∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x, y)) ∂ν ∂μ) =
        ∫⁻ y, ∫⁻ x, ENNReal.ofReal (F (x, y)) ∂μ ∂ν :=
    (MeasureTheory.lintegral_prod _ hF.ennreal_ofReal.aemeasurable).symm.trans
      (MeasureTheory.lintegral_prod_symm _ hF.ennreal_ofReal.aemeasurable)
  calc
    (∫ x, ∫ y, F (x, y) ∂ν ∂μ) =
        ENNReal.toReal (ENNReal.ofReal (∫ x, ∫ y, F (x, y) ∂ν ∂μ)) :=
      (ENNReal.toReal_ofReal (integral_nonneg hleft_nonneg)).symm
    _ = ENNReal.toReal
        (∫⁻ x, ENNReal.ofReal (∫ y, F (x, y) ∂ν) ∂μ) := congrArg _
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal houter_left
        (Filter.Eventually.of_forall hleft_nonneg))
    _ = ENNReal.toReal
        (∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x, y)) ∂ν ∂μ) := by
      congr 1
      apply lintegral_congr
      intro x
      exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hsection_left x)
        (Filter.Eventually.of_forall fun y => h0 (x, y))
    _ = ENNReal.toReal
        (∫⁻ y, ∫⁻ x, ENNReal.ofReal (F (x, y)) ∂μ ∂ν) := congrArg _ hlin_swap
    _ = ENNReal.toReal
        (∫⁻ y, ENNReal.ofReal (∫ x, F (x, y) ∂μ) ∂ν) := by
      congr 1
      apply lintegral_congr
      intro y
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hsection_right y)
        (Filter.Eventually.of_forall fun x => h0 (x, y))).symm
    _ = ENNReal.toReal (ENNReal.ofReal (∫ y, ∫ x, F (x, y) ∂μ ∂ν)) := congrArg _
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal houter_right
        (Filter.Eventually.of_forall hright_nonneg)).symm
    _ = ∫ y, ∫ x, F (x, y) ∂μ ∂ν :=
      ENNReal.toReal_ofReal (integral_nonneg hright_nonneg)

@[blueprint "lem:atb-ex-ante-formula"
  (statement := /-- Let $T>0$, let $D$ be a probability measure on $X\times\mathbb R$, and let $\rho:X\times\mathbb R\to\mathbb R$ be measurable with $|\rho(x,y)-y|\le1$. Then the expected averaged two-bin error equals
  \[
  \frac1T\int(\rho-y)^2\,dD+\frac{T-1}{T}\int_0^1\left[
    \left(\int \mathbf 1_{\{\rho<q\}}(\rho-y)\,dD\right)^2+
    \left(\int \mathbf 1_{\{q\le\rho\}}(\rho-y)\,dD\right)^2\right]dq.
  \] -/)
  (proof := /-- For each threshold $q$, write the two bin sums as coordinate sums of the bounded measurable functions $\mathbf 1_{\{\rho<q\}}(\rho-y)$ and $\mathbf 1_{\{q\le\rho\}}(\rho-y)$. Their squared sum is a bounded nonnegative jointly measurable function of the sample and $q$, so \cref{lem:atb-integral-swap-nonnegative} exchanges the sample and threshold integrals. Apply \cref{lem:atb-pair-integral-pi} to each bin. The two diagonal terms add to $\int(\rho-y)^2\,dD$, since the bins partition the sample space, while the off-diagonal terms are the two squared bin means. Finally, the factor $T^{-2}$ in the averaged two-bin definition changes the diagonal coefficient to $1/T$ and the off-diagonal coefficient to $(T-1)/T$. -/)
  (title := /-- Bias-variance formula for the expected ex-ante ATB error -/)
  (latexEnv := "lemma")]
lemma atb_ex_ante_formula {X : Type*} [MeasurableSpace X] (T : ℕ) (hT : 0 < T)
    (D : Measure (X × ℝ)) [IsProbabilityMeasure D] (ρ : X × ℝ → ℝ)
    (hρ : Measurable ρ) (hb : ∀ z, |ρ z - z.2| ≤ 1) :
    ∫ s : Fin T → X × ℝ, averaged_two_bin (fun t => ρ (s t)) (fun t => (s t).2)
        ∂(Measure.pi fun _ => D)
      = 1 / (T : ℝ) * (∫ z, (ρ z - z.2) ^ 2 ∂D)
        + ((T : ℝ) - 1) / (T : ℝ) * ∫ q in (0 : ℝ)..1,
            ((∫ z, (if ρ z < q then ρ z - z.2 else 0) ∂D) ^ 2
              + (∫ z, (if q ≤ ρ z then ρ z - z.2 else 0) ∂D) ^ 2) := by
  classical
  let a : ℝ → X × ℝ → ℝ := fun q z => if ρ z < q then ρ z - z.2 else 0
  let b : ℝ → X × ℝ → ℝ := fun q z => if q ≤ ρ z then ρ z - z.2 else 0
  let H : (Fin T → X × ℝ) × ℝ → ℝ := fun z =>
    (∑ t, a z.2 (z.1 t)) ^ 2 + (∑ t, b z.2 (z.1 t)) ^ 2
  have ha (q : ℝ) : Measurable (a q) := by
    dsimp [a]
    exact Measurable.ite (measurableSet_lt hρ measurable_const)
      (hρ.sub measurable_snd) measurable_const
  have hbmeas (q : ℝ) : Measurable (b q) := by
    dsimp [b]
    exact Measurable.ite (measurableSet_le measurable_const hρ)
      (hρ.sub measurable_snd) measurable_const
  have hab (q : ℝ) (z : X × ℝ) : |a q z| ≤ 1 := by
    dsimp [a]
    split_ifs
    · exact hb z
    · simp
  have hbb (q : ℝ) (z : X × ℝ) : |b q z| ≤ 1 := by
    dsimp [b]
    split_ifs
    · exact hb z
    · simp
  have hsum_a (s : Fin T → X × ℝ) (q : ℝ) : |∑ t, a q (s t)| ≤ (T : ℝ) := by
    calc
      |∑ t, a q (s t)| ≤ ∑ t, |a q (s t)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t : Fin T, (1 : ℝ) := Finset.sum_le_sum fun t _ => hab q (s t)
      _ = (T : ℝ) := by simp
  have hsum_b (s : Fin T → X × ℝ) (q : ℝ) : |∑ t, b q (s t)| ≤ (T : ℝ) := by
    calc
      |∑ t, b q (s t)| ≤ ∑ t, |b q (s t)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t : Fin T, (1 : ℝ) := Finset.sum_le_sum fun t _ => hbb q (s t)
      _ = (T : ℝ) := by simp
  have hHmeas : Measurable H := by
    have ha_joint (t : Fin T) : Measurable (fun z : (Fin T → X × ℝ) × ℝ =>
        if ρ (z.1 t) < z.2 then ρ (z.1 t) - (z.1 t).2 else 0) := by
      have heval : Measurable (fun z : (Fin T → X × ℝ) × ℝ => z.1 t) :=
        (measurable_pi_apply t).comp measurable_fst
      exact Measurable.ite (measurableSet_lt (hρ.comp heval) measurable_snd)
        ((hρ.comp heval).sub (measurable_snd.comp heval)) measurable_const
    have hb_joint (t : Fin T) : Measurable (fun z : (Fin T → X × ℝ) × ℝ =>
        if z.2 ≤ ρ (z.1 t) then ρ (z.1 t) - (z.1 t).2 else 0) := by
      have heval : Measurable (fun z : (Fin T → X × ℝ) × ℝ => z.1 t) :=
        (measurable_pi_apply t).comp measurable_fst
      exact Measurable.ite (measurableSet_le measurable_snd (hρ.comp heval))
        ((hρ.comp heval).sub (measurable_snd.comp heval)) measurable_const
    exact ((Finset.measurable_sum Finset.univ fun t _ => ha_joint t).pow_const 2).add
      ((Finset.measurable_sum Finset.univ fun t _ => hb_joint t).pow_const 2)
  have hH0 : ∀ z, 0 ≤ H z := fun z => by
    dsimp [H]
    positivity
  have hHC : ∀ z, H z ≤ 2 * (T : ℝ) ^ 2 := by
    intro z
    have ha_bounds := (abs_le.mp (hsum_a z.1 z.2))
    have hb_bounds := (abs_le.mp (hsum_b z.1 z.2))
    have ha_sq : (∑ t, a z.2 (z.1 t)) ^ 2 ≤ (T : ℝ) ^ 2 :=
      sq_le_sq' ha_bounds.1 ha_bounds.2
    have hb_sq : (∑ t, b z.2 (z.1 t)) ^ 2 ≤ (T : ℝ) ^ 2 :=
      sq_le_sq' hb_bounds.1 hb_bounds.2
    dsimp [H]
    linarith
  have hswap := atb_integral_swap_nonnegative
    (Measure.pi fun _ : Fin T => D) (volume.restrict (Set.Ioc (0 : ℝ) 1))
    H (2 * (T : ℝ) ^ 2) hHmeas hH0 hHC
  have hpair (q : ℝ) :
      (∫ s : Fin T → X × ℝ, H (s, q) ∂(Measure.pi fun _ => D)) =
        (T : ℝ) * (∫ z, (ρ z - z.2) ^ 2 ∂D)
          + (T : ℝ) * ((T : ℝ) - 1) *
            ((∫ z, a q z ∂D) ^ 2 + (∫ z, b q z ∂D) ^ 2) := by
    have hsum_a_meas : Measurable (fun s : Fin T → X × ℝ => ∑ t, a q (s t)) :=
      Finset.measurable_sum Finset.univ fun t _ => (ha q).comp (measurable_pi_apply t)
    have hsum_b_meas : Measurable (fun s : Fin T → X × ℝ => ∑ t, b q (s t)) :=
      Finset.measurable_sum Finset.univ fun t _ => (hbmeas q).comp (measurable_pi_apply t)
    have hsq_a : Integrable (fun s : Fin T → X × ℝ => (∑ t, a q (s t)) ^ 2)
        (Measure.pi fun _ => D) := by
      exact (integrable_const ((T : ℝ) ^ 2)).mono'
        (hsum_a_meas.pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun s => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact sq_le_sq' (abs_le.mp (hsum_a s q)).1 (abs_le.mp (hsum_a s q)).2)
    have hsq_b : Integrable (fun s : Fin T → X × ℝ => (∑ t, b q (s t)) ^ 2)
        (Measure.pi fun _ => D) := by
      exact (integrable_const ((T : ℝ) ^ 2)).mono'
        (hsum_b_meas.pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun s => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact sq_le_sq' (abs_le.mp (hsum_b s q)).1 (abs_le.mp (hsum_b s q)).2)
    have ha2int : Integrable (fun z => (a q z) ^ 2) D := by
      exact (integrable_const (1 : ℝ)).mono' ((ha q).pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          simpa using sq_le_sq' (abs_le.mp (hab q z)).1 (abs_le.mp (hab q z)).2)
    have hb2int : Integrable (fun z => (b q z) ^ 2) D := by
      exact (integrable_const (1 : ℝ)).mono' ((hbmeas q).pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          simpa using sq_le_sq' (abs_le.mp (hbb q z)).1 (abs_le.mp (hbb q z)).2)
    have hdiag : (∫ z, (a q z) ^ 2 ∂D) + (∫ z, (b q z) ^ 2 ∂D) =
        ∫ z, (ρ z - z.2) ^ 2 ∂D := by
      rw [← integral_add ha2int hb2int]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        by_cases hz : ρ z < q
        · simp [a, b, hz, not_le.mpr hz]
        · simp [a, b, hz, le_of_not_gt hz]
    have hpa := atb_pair_integral_pi T D (a q) 1 (ha q) (hab q)
    have hpb := atb_pair_integral_pi T D (b q) 1 (hbmeas q) (hbb q)
    dsimp [H]
    rw [integral_add hsq_a hsq_b, hpa, hpb]
    rw [← hdiag]
    ring
  have havg (s : Fin T → X × ℝ) :
      averaged_two_bin (fun t => ρ (s t)) (fun t => (s t).2) =
        (1 / (T : ℝ) ^ 2) * ∫ q in (0 : ℝ)..1, H (s, q) := by
    rw [averaged_two_bin, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro q _
    simp only [H, a, b, Finset.sum_filter]
  let K : ℝ → ℝ := fun q =>
    ∫ s : Fin T → X × ℝ, H (s, q) ∂(Measure.pi fun _ => D)
  have hHsection (q : ℝ) : Integrable (fun s : Fin T → X × ℝ => H (s, q))
      (Measure.pi fun _ => D) := by
    exact (integrable_const (2 * (T : ℝ) ^ 2)).mono'
      (hHmeas.comp measurable_prodMk_right).aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hH0 (s, q))]
        exact hHC (s, q))
  have hKnonneg (q : ℝ) : 0 ≤ K q := by
    dsimp [K]
    exact integral_nonneg fun s => hH0 (s, q)
  have hK_eq (q : ℝ) : K q = ENNReal.toReal
      (∫⁻ s : Fin T → X × ℝ, ENNReal.ofReal (H (s, q)) ∂(Measure.pi fun _ => D)) := by
    calc
      K q = ENNReal.toReal (ENNReal.ofReal (K q)) :=
        (ENNReal.toReal_ofReal (hKnonneg q)).symm
      _ = ENNReal.toReal
          (∫⁻ s : Fin T → X × ℝ, ENNReal.ofReal (H (s, q))
            ∂(Measure.pi fun _ => D)) := congrArg _
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hHsection q)
          (Filter.Eventually.of_forall fun s => hH0 (s, q)))
  have hKmeas : Measurable K := by
    rw [show K = (fun q => ENNReal.toReal
      (∫⁻ s : Fin T → X × ℝ, ENNReal.ofReal (H (s, q))
        ∂(Measure.pi fun _ => D))) from funext hK_eq]
    exact ENNReal.measurable_toReal.comp hHmeas.ennreal_ofReal.lintegral_prod_left
  have hKbound : ∀ q, ‖K q‖ ≤
      (2 * (T : ℝ) ^ 2) * (Measure.pi fun _ : Fin T => D).real Set.univ := by
    intro q
    dsimp [K]
    exact MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := Measure.pi fun _ : Fin T => D)
      (Filter.Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hH0 (s, q))]
        exact hHC (s, q))
  have hKint : Integrable K (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    exact (integrable_const
      ((2 * (T : ℝ) ^ 2) * (Measure.pi fun _ : Fin T => D).real Set.univ)).mono'
      hKmeas.aestronglyMeasurable (Filter.Eventually.of_forall hKbound)
  have hKdecomp :
      (∫ q in Set.Ioc (0 : ℝ) 1, K q) =
        (T : ℝ) * (∫ z, (ρ z - z.2) ^ 2 ∂D)
          + (T : ℝ) * ((T : ℝ) - 1) * ∫ q in Set.Ioc (0 : ℝ) 1,
            ((∫ z, a q z ∂D) ^ 2 + (∫ z, b q z ∂D) ^ 2) := by
    let c : ℝ := (T : ℝ) * (∫ z, (ρ z - z.2) ^ 2 ∂D)
    have hcint : Integrable (fun _q : ℝ => c) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      integrable_const c
    have hremint : Integrable (fun q => K q - c)
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) := hKint.sub hcint
    calc
      (∫ q in Set.Ioc (0 : ℝ) 1, K q) =
          ∫ q in Set.Ioc (0 : ℝ) 1, c + (K q - c) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun q => by ring
      _ = (∫ _q in Set.Ioc (0 : ℝ) 1, c) +
          ∫ q in Set.Ioc (0 : ℝ) 1, K q - c := integral_add hcint hremint
      _ = c + ∫ q in Set.Ioc (0 : ℝ) 1, K q - c := by
        congr 1
        simp [c]
      _ = c + ∫ q in Set.Ioc (0 : ℝ) 1,
          (T : ℝ) * ((T : ℝ) - 1) *
            ((∫ z, a q z ∂D) ^ 2 + (∫ z, b q z ∂D) ^ 2) := by
              congr 1
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun q => by
                dsimp [K, c]
                rw [hpair q]
                ring
      _ = c + (T : ℝ) * ((T : ℝ) - 1) * ∫ q in Set.Ioc (0 : ℝ) 1,
          ((∫ z, a q z ∂D) ^ 2 + (∫ z, b q z ∂D) ^ 2) := by
            rw [integral_const_mul]
      _ = (T : ℝ) * (∫ z, (ρ z - z.2) ^ 2 ∂D)
          + (T : ℝ) * ((T : ℝ) - 1) * ∫ q in Set.Ioc (0 : ℝ) 1,
            ((∫ z, a q z ∂D) ^ 2 + (∫ z, b q z ∂D) ^ 2) := by
              rfl
  have hTne : (T : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hT
  calc
    (∫ s : Fin T → X × ℝ, averaged_two_bin (fun t => ρ (s t)) (fun t => (s t).2)
        ∂(Measure.pi fun _ => D)) =
        (1 / (T : ℝ) ^ 2) *
          (∫ s : Fin T → X × ℝ, (∫ q in Set.Ioc (0 : ℝ) 1, H (s, q))
            ∂(Measure.pi fun _ => D)) := by
              simp_rw [havg, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
              rw [integral_const_mul]
    _ = (1 / (T : ℝ) ^ 2) * ∫ q in Set.Ioc (0 : ℝ) 1, K q := by
      rw [hswap]
    _ = (1 / (T : ℝ) ^ 2) *
        ((T : ℝ) * (∫ z, (ρ z - z.2) ^ 2 ∂D)
          + (T : ℝ) * ((T : ℝ) - 1) * ∫ q in Set.Ioc (0 : ℝ) 1,
            ((∫ z, a q z ∂D) ^ 2 + (∫ z, b q z ∂D) ^ 2)) := by
              rw [hKdecomp]
    _ = 1 / (T : ℝ) * (∫ z, (ρ z - z.2) ^ 2 ∂D)
        + ((T : ℝ) - 1) / (T : ℝ) * ∫ q in (0 : ℝ)..1,
            ((∫ z, (if ρ z < q then ρ z - z.2 else 0) ∂D) ^ 2
              + (∫ z, (if q ≤ ρ z then ρ z - z.2 else 0) ∂D) ^ 2) := by
                rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
                dsimp [a, b]
                field_simp [hTne]

@[blueprint "lem:atb-condexp-weighted-integral-zero"
  (statement := /-- Let $Y(x,y)=y$ be integrable and let $W:X\times\mathbb R\to[0,1]$ be measurable with respect to the $\sigma$-algebra generated by the first coordinate. Assume that $0\le Y\le1$ and $0\le\mathbb E[Y\mid x]\le1$ almost everywhere. Then
  \[
    \int W\bigl(\mathbb E[Y\mid x]-Y\bigr)\,dD=0.
  \] -/)
  (proof := /-- Replace $Y$ and its conditional expectation by measurable pointwise $[0,1]$-valued truncations, which agree with them almost everywhere. For either truncation $V$, the layer-cake identity gives $W V=\int_0^1\mathbf 1_{\{q\le W\}}V\,dq$. The integrands are bounded, measurable, and nonnegative, so \cref{lem:atb-integral-swap-nonnegative} exchanges the $D$-integral and the threshold integral. For every $q$, the set $\{q\le W\}$ belongs to the conditioning $\sigma$-algebra; the defining set-integral identity for conditional expectation therefore equates the two inner integrals. Integrating in $q$ and subtracting proves the claim. -/)
  (title := /-- Orthogonality of the conditional-expectation residual -/)
  (latexEnv := "lemma")]
lemma atb_condexp_weighted_integral_zero {X : Type*} [MeasurableSpace X]
    (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (hy : Integrable (fun z : X × ℝ => z.2) D) (w : X × ℝ → ℝ)
    (hw : Measurable[MeasurableSpace.comap Prod.fst inferInstance] w)
    (hwm : ∀ z, w z ∈ Set.Icc (0 : ℝ) 1)
    (hy0 : ∀ᵐ z ∂D, 0 ≤ z.2) (hy1 : ∀ᵐ z ∂D, z.2 ≤ 1)
    (hce0 : ∀ᵐ z ∂D, 0 ≤ condExp (MeasurableSpace.comap Prod.fst inferInstance)
      D (fun z => z.2) z)
    (hce1 : ∀ᵐ z ∂D, condExp (MeasurableSpace.comap Prod.fst inferInstance)
      D (fun z => z.2) z ≤ 1) :
    ∫ z, w z *
        (condExp (MeasurableSpace.comap Prod.fst inferInstance) D (fun z => z.2) z - z.2) ∂D
      = 0 := by
  let m : MeasurableSpace (X × ℝ) :=
    MeasurableSpace.comap (Prod.fst : X × ℝ → X)
      (inferInstance : MeasurableSpace X)
  let m0 : MeasurableSpace (X × ℝ) :=
    @Prod.instMeasurableSpace X ℝ (inferInstance : MeasurableSpace X)
      (inferInstance : MeasurableSpace ℝ)
  let mp : MeasurableSpace ((X × ℝ) × ℝ) :=
    @Prod.instMeasurableSpace (X × ℝ) ℝ m0 (inferInstance : MeasurableSpace ℝ)
  have hm : m ≤ m0 := by
    dsimp [m]
    exact (@measurable_fst X ℝ (inferInstance : MeasurableSpace X)
      (inferInstance : MeasurableSpace ℝ)).comap_le
  change ∀ᵐ z ∂D, 0 ≤ condExp m D (fun z : X × ℝ => z.2) z at hce0
  change ∀ᵐ z ∂D, condExp m D (fun z : X × ℝ => z.2) z ≤ 1 at hce1
  let yhat : X × ℝ → ℝ := fun z => max 0 (min 1 z.2)
  let chat : X × ℝ → ℝ := fun z =>
    max 0 (min 1 (condExp m D (fun z : X × ℝ => z.2) z))
  have hyhat_meas : Measurable[m0] yhat := by
    exact measurable_const.max (measurable_const.min measurable_snd)
  have hchat_meas : Measurable[m0] chat := by
    have hcem : Measurable[m0]
        (condExp m D (fun z : X × ℝ => z.2)) :=
      (MeasureTheory.stronglyMeasurable_condExp.mono hm).measurable
    exact measurable_const.max (measurable_const.min hcem)
  have hyhat_mem : ∀ z, yhat z ∈ Set.Icc (0 : ℝ) 1 := by
    intro z
    dsimp [yhat]
    constructor <;> simp
  have hchat_mem : ∀ z, chat z ∈ Set.Icc (0 : ℝ) 1 := by
    intro z
    dsimp [chat]
    constructor <;> simp
  have hyhat_eq : yhat =ᵐ[D] fun z : X × ℝ => z.2 := by
    filter_upwards [hy0, hy1] with z hz0 hz1
    simp [yhat, max_eq_right hz0, min_eq_right hz1]
  have hchat_eq : chat =ᵐ[D] condExp m D (fun z : X × ℝ => z.2) := by
    filter_upwards [hce0, hce1] with z hz0 hz1
    simp [chat, max_eq_right hz0, min_eq_right hz1]
  let Fc : (X × ℝ) × ℝ → ℝ := fun z => if z.2 ≤ w z.1 then chat z.1 else 0
  let Fy : (X × ℝ) × ℝ → ℝ := fun z => if z.2 ≤ w z.1 then yhat z.1 else 0
  have hwm_ambient : Measurable[m0] w := hw.mono hm le_rfl
  have hfst : Measurable[mp, m0] (Prod.fst : (X × ℝ) × ℝ → X × ℝ) :=
    @measurable_fst (X × ℝ) ℝ m0 (inferInstance : MeasurableSpace ℝ)
  have hsnd : Measurable[mp] (Prod.snd : (X × ℝ) × ℝ → ℝ) :=
    @measurable_snd (X × ℝ) ℝ m0 (inferInstance : MeasurableSpace ℝ)
  have hFcmeas : Measurable[mp] Fc := by
    exact Measurable.ite (measurableSet_le hsnd (hwm_ambient.comp hfst))
      (hchat_meas.comp hfst) measurable_const
  have hFymeas : Measurable[mp] Fy := by
    exact Measurable.ite (measurableSet_le hsnd (hwm_ambient.comp hfst))
      (hyhat_meas.comp hfst) measurable_const
  have hFc0 : ∀ z, 0 ≤ Fc z := fun z => by
    dsimp [Fc]
    split_ifs
    · exact (hchat_mem z.1).1
    · norm_num
  have hFy0 : ∀ z, 0 ≤ Fy z := fun z => by
    dsimp [Fy]
    split_ifs
    · exact (hyhat_mem z.1).1
    · norm_num
  have hFc1 : ∀ z, Fc z ≤ 1 := fun z => by
    dsimp [Fc]
    split_ifs
    · exact (hchat_mem z.1).2
    · norm_num
  have hFy1 : ∀ z, Fy z ≤ 1 := fun z => by
    dsimp [Fy]
    split_ifs
    · exact (hyhat_mem z.1).2
    · norm_num
  have hswapc := atb_integral_swap_nonnegative D
    (volume.restrict (Set.Ioc (0 : ℝ) 1)) Fc 1 hFcmeas hFc0 hFc1
  have hswapy := atb_integral_swap_nonnegative D
    (volume.restrict (Set.Ioc (0 : ℝ) 1)) Fy 1 hFymeas hFy0 hFy1
  have hlayer (v : X × ℝ → ℝ) (z : X × ℝ) :
      (∫ q in (0 : ℝ)..1, (if q ≤ w z then v z else 0)) = w z * v z := by
    have hwz := hwm z
    rw [show (fun q : ℝ => if q ≤ w z then v z else 0) =
      Set.indicator {q | q ≤ w z} (fun _ => v z) from by
        funext q
        by_cases hq : q ≤ w z <;> simp [Set.indicator, hq]]
    rw [intervalIntegral.integral_indicator hwz]
    simp
  have hinner (q : ℝ) : (∫ z, Fc (z, q) ∂D) = ∫ z, Fy (z, q) ∂D := by
    let s : Set (X × ℝ) := {z | q ≤ w z}
    have hs : MeasurableSet[m] s := measurableSet_le measurable_const hw
    calc
      (∫ z, Fc (z, q) ∂D) = ∫ z in s, chat z ∂D := by
        rw [← MeasureTheory.integral_indicator (hm s hs)]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by
          by_cases hz : z ∈ s
          · have hz' : q ≤ w z := hz
            simp [Fc, s, Set.indicator, hz, hz']
          · have hz' : ¬q ≤ w z := by simpa [s] using hz
            simp [Fc, s, Set.indicator, hz, hz']
      _ = ∫ z in s, condExp m D (fun z : X × ℝ => z.2) z ∂D :=
        setIntegral_congr_ae (hm s hs) (hchat_eq.mono fun z hz _ => hz)
      _ = ∫ z in s, z.2 ∂D := MeasureTheory.setIntegral_condExp hm hy hs
      _ = ∫ z in s, yhat z ∂D :=
        setIntegral_congr_ae (hm s hs) (hyhat_eq.symm.mono fun z hz _ => hz)
      _ = ∫ z, Fy (z, q) ∂D := by
        rw [← MeasureTheory.integral_indicator (hm s hs)]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by
          by_cases hz : z ∈ s
          · have hz' : q ≤ w z := hz
            simp [Fy, s, Set.indicator, hz, hz']
          · have hz' : ¬q ≤ w z := by simpa [s] using hz
            simp [Fy, s, Set.indicator, hz, hz']
  change (∫ z, w z * (condExp m D (fun z : X × ℝ => z.2) z - z.2) ∂D) = 0
  calc
    (∫ z, w z * (condExp m D (fun z : X × ℝ => z.2) z - z.2) ∂D) =
        ∫ z, w z * (chat z - yhat z) ∂D := by
          apply integral_congr_ae
          filter_upwards [hchat_eq, hyhat_eq] with z hcz hyz
          rw [hcz, hyz]
    _ = (∫ z, w z * chat z ∂D) - ∫ z, w z * yhat z ∂D := by
      rw [← integral_sub]
      · apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by ring
      · exact (integrable_const 1).mono'
          (hwm_ambient.mul hchat_meas).aestronglyMeasurable
          (Filter.Eventually.of_forall fun z => by
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hwm z).1 (hchat_mem z).1)]
            exact mul_le_one₀ (hwm z).2 (hchat_mem z).1 (hchat_mem z).2)
      · exact (integrable_const 1).mono'
          (hwm_ambient.mul hyhat_meas).aestronglyMeasurable
          (Filter.Eventually.of_forall fun z => by
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hwm z).1 (hyhat_mem z).1)]
            exact mul_le_one₀ (hwm z).2 (hyhat_mem z).1 (hyhat_mem z).2)
    _ = (∫ z, (∫ q in Set.Ioc (0 : ℝ) 1, Fc (z, q)) ∂D) -
        ∫ z, (∫ q in Set.Ioc (0 : ℝ) 1, Fy (z, q)) ∂D := by
          congr 1
          · apply integral_congr_ae
            exact Filter.Eventually.of_forall fun z => by
              calc
                w z * chat z = ∫ q in (0 : ℝ)..1, Fc (z, q) := by
                  simpa [Fc] using (hlayer chat z).symm
                _ = ∫ q in Set.Ioc (0 : ℝ) 1, Fc (z, q) :=
                  intervalIntegral.integral_of_le (by norm_num)
          · apply integral_congr_ae
            exact Filter.Eventually.of_forall fun z => by
              calc
                w z * yhat z = ∫ q in (0 : ℝ)..1, Fy (z, q) := by
                  simpa [Fy] using (hlayer yhat z).symm
                _ = ∫ q in Set.Ioc (0 : ℝ) 1, Fy (z, q) :=
                  intervalIntegral.integral_of_le (by norm_num)
    _ = (∫ q in Set.Ioc (0 : ℝ) 1, ∫ z, Fc (z, q) ∂D) -
        ∫ q in Set.Ioc (0 : ℝ) 1, ∫ z, Fy (z, q) ∂D := by rw [hswapc, hswapy]
    _ = 0 := by
      apply sub_eq_zero.mpr
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hinner

@[blueprint "lem:atb-brier-gap"
  (statement := /-- Let $Y(x,y)=y$ be integrable, let $r:X\to[0,1]$ be measurable, and assume that $0\le Y\le1$ and $0\le\mathbb E[Y\mid x]\le1$ almost everywhere. Then
  \[
    \int(r(x)-Y)^2\,dD
      =\int(r(x)-\mathbb E[Y\mid x])^2\,dD
       +\int(\mathbb E[Y\mid x]-Y)^2\,dD.
  \] -/)
  (proof := /-- Apply \cref{lem:atb-condexp-weighted-integral-zero} first with weight $r(x)$ and then with a pointwise $[0,1]$-valued truncation of $\mathbb E[Y\mid x]$. Since the truncation agrees almost everywhere with the conditional expectation, subtraction gives
  \[
    \int(r-\mathbb E[Y\mid x])(\mathbb E[Y\mid x]-Y)\,dD=0.
  \]
  All terms are integrable by the stated bounds. Expanding $r-Y=(r-\mathbb E[Y\mid x])+(\mathbb E[Y\mid x]-Y)$, integrating the square, and using the vanishing cross term yields the identity. -/)
  (title := /-- Pythagoras identity for the squared label error -/)
  (latexEnv := "lemma")]
lemma atb_brier_gap {X : Type*} [MeasurableSpace X]
    (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (hy : Integrable (fun z : X × ℝ => z.2) D) (r : X → ℝ) (hrm : Measurable r)
    (hr : ∀ x, r x ∈ Set.Icc (0 : ℝ) 1)
    (hy0 : ∀ᵐ z ∂D, 0 ≤ z.2) (hy1 : ∀ᵐ z ∂D, z.2 ≤ 1)
    (hce0 : ∀ᵐ z ∂D, 0 ≤ condExp (MeasurableSpace.comap Prod.fst inferInstance)
      D (fun z => z.2) z)
    (hce1 : ∀ᵐ z ∂D, condExp (MeasurableSpace.comap Prod.fst inferInstance)
      D (fun z => z.2) z ≤ 1) :
    ∫ z, (r z.1 - z.2) ^ 2 ∂D
      = (∫ z, (r z.1 -
            condExp (MeasurableSpace.comap Prod.fst inferInstance) D (fun z => z.2) z) ^ 2 ∂D)
        + ∫ z, (condExp (MeasurableSpace.comap Prod.fst inferInstance) D (fun z => z.2) z
            - z.2) ^ 2 ∂D := by
  let m : MeasurableSpace (X × ℝ) :=
    MeasurableSpace.comap (Prod.fst : X × ℝ → X)
      (inferInstance : MeasurableSpace X)
  let m0 : MeasurableSpace (X × ℝ) :=
    @Prod.instMeasurableSpace X ℝ (inferInstance : MeasurableSpace X)
      (inferInstance : MeasurableSpace ℝ)
  have hm : m ≤ m0 := by
    dsimp [m]
    exact (@measurable_fst X ℝ (inferInstance : MeasurableSpace X)
      (inferInstance : MeasurableSpace ℝ)).comap_le
  change ∀ᵐ z ∂D, 0 ≤ condExp m D (fun z : X × ℝ => z.2) z at hce0
  change ∀ᵐ z ∂D, condExp m D (fun z : X × ℝ => z.2) z ≤ 1 at hce1
  have hrw : Measurable[m] (fun z : X × ℝ => r z.1) :=
    hrm.comp (comap_measurable (Prod.fst : X × ℝ → X))
  have hrmem : ∀ z : X × ℝ, r z.1 ∈ Set.Icc (0 : ℝ) 1 := fun z => hr z.1
  have hcross_r := atb_condexp_weighted_integral_zero D hy (fun z => r z.1)
    hrw hrmem hy0 hy1 hce0 hce1
  let chat : X × ℝ → ℝ := fun z =>
    max 0 (min 1 (condExp m D (fun z : X × ℝ => z.2) z))
  have hchatm : Measurable[m] chat := by
    have hcem : Measurable[m] (condExp m D (fun z : X × ℝ => z.2)) :=
      MeasureTheory.stronglyMeasurable_condExp.measurable
    exact measurable_const.max (measurable_const.min hcem)
  have hchatmem : ∀ z, chat z ∈ Set.Icc (0 : ℝ) 1 := by
    intro z
    dsimp [chat]
    constructor <;> simp
  have hchat_eq : chat =ᵐ[D] condExp m D (fun z : X × ℝ => z.2) := by
    filter_upwards [hce0, hce1] with z hz0 hz1
    simp [chat, max_eq_right hz0, min_eq_right hz1]
  have hcross_chat := atb_condexp_weighted_integral_zero D hy chat hchatm hchatmem
    hy0 hy1 hce0 hce1
  have hcross_ce :
      (∫ z, condExp m D (fun z : X × ℝ => z.2) z *
        (condExp m D (fun z : X × ℝ => z.2) z - z.2) ∂D) = 0 := by
    rw [← hcross_chat]
    apply integral_congr_ae
    filter_upwards [hchat_eq] with z hz
    rw [hz]
  have hceint : Integrable (condExp m D (fun z : X × ℝ => z.2)) D :=
    MeasureTheory.integrable_condExp
  have hrint : Integrable (fun z : X × ℝ => r z.1) D := by
    exact (integrable_const (1 : ℝ)).mono'
      ((hrm.comp measurable_fst).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hr z.1).1]
        exact (hr z.1).2)
  have hfr : Integrable (fun z : X × ℝ => r z.1 - condExp m D (fun z => z.2) z) D :=
    hrint.sub hceint
  have hgy : Integrable (fun z : X × ℝ => condExp m D (fun z => z.2) z - z.2) D :=
    hceint.sub hy
  have hfrb : ∀ᵐ z ∂D, ‖r z.1 - condExp m D (fun z => z.2) z‖ ≤ 1 := by
    filter_upwards [hce0, hce1] with z hz0 hz1
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(hr z.1).1, (hr z.1).2]
  have hgyb : ∀ᵐ z ∂D, ‖condExp m D (fun z => z.2) z - z.2‖ ≤ 1 := by
    filter_upwards [hce0, hce1, hy0, hy1] with z hc0 hc1 hz0 hz1
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hfrsq : Integrable
      (fun z : X × ℝ => (r z.1 - condExp m D (fun z => z.2) z) ^ 2) D := by
    simpa [pow_two] using hfr.bdd_mul hfr.aestronglyMeasurable hfrb
  have hgysq : Integrable
      (fun z : X × ℝ => (condExp m D (fun z => z.2) z - z.2) ^ 2) D := by
    simpa [pow_two] using hgy.bdd_mul hgy.aestronglyMeasurable hgyb
  have hcrossint : Integrable (fun z : X × ℝ =>
      (r z.1 - condExp m D (fun z => z.2) z) *
        (condExp m D (fun z => z.2) z - z.2)) D :=
    hgy.bdd_mul hfr.aestronglyMeasurable hfrb
  have hcross : (∫ z, (r z.1 - condExp m D (fun z => z.2) z) *
      (condExp m D (fun z => z.2) z - z.2) ∂D) = 0 := by
    have hrgy : Integrable (fun z : X × ℝ =>
        r z.1 * (condExp m D (fun z => z.2) z - z.2)) D :=
      hgy.bdd_mul hrint.aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hr z.1).1]
          exact (hr z.1).2)
    have hceb : ∀ᵐ z ∂D, ‖condExp m D (fun z : X × ℝ => z.2) z‖ ≤ 1 := by
      filter_upwards [hce0, hce1] with z hz0 hz1
      rw [Real.norm_eq_abs, abs_of_nonneg hz0]
      exact hz1
    have hcegy : Integrable (fun z : X × ℝ =>
        condExp m D (fun z => z.2) z * (condExp m D (fun z => z.2) z - z.2)) D :=
      hgy.bdd_mul hceint.aestronglyMeasurable hceb
    calc
      (∫ z, (r z.1 - condExp m D (fun z => z.2) z) *
          (condExp m D (fun z => z.2) z - z.2) ∂D) =
          (∫ z, r z.1 * (condExp m D (fun z => z.2) z - z.2) ∂D) -
            ∫ z, condExp m D (fun z => z.2) z *
              (condExp m D (fun z => z.2) z - z.2) ∂D := by
                rw [← integral_sub hrgy hcegy]
                apply integral_congr_ae
                exact Filter.Eventually.of_forall fun z => by ring
      _ = 0 := by rw [hcross_r, hcross_ce, sub_zero]
  change (∫ z, (r z.1 - z.2) ^ 2 ∂D) =
    (∫ z, (r z.1 - condExp m D (fun z : X × ℝ => z.2) z) ^ 2 ∂D) +
      ∫ z, (condExp m D (fun z : X × ℝ => z.2) z - z.2) ^ 2 ∂D
  calc
    (∫ z, (r z.1 - z.2) ^ 2 ∂D) = ∫ z,
        (r z.1 - condExp m D (fun z => z.2) z) ^ 2
          + (condExp m D (fun z => z.2) z - z.2) ^ 2
          + 2 * ((r z.1 - condExp m D (fun z => z.2) z) *
            (condExp m D (fun z => z.2) z - z.2)) ∂D := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun z => by ring
    _ = (∫ z, (r z.1 - condExp m D (fun z => z.2) z) ^ 2
          + (condExp m D (fun z => z.2) z - z.2) ^ 2 ∂D)
        + ∫ z, 2 * ((r z.1 - condExp m D (fun z => z.2) z) *
          (condExp m D (fun z => z.2) z - z.2)) ∂D :=
            integral_add (hfrsq.add hgysq) (hcrossint.const_mul 2)
    _ = (∫ z, (r z.1 - condExp m D (fun z => z.2) z) ^ 2 ∂D)
        + (∫ z, (condExp m D (fun z => z.2) z - z.2) ^ 2 ∂D)
        + 2 * ∫ z, (r z.1 - condExp m D (fun z => z.2) z) *
          (condExp m D (fun z => z.2) z - z.2) ∂D := by
            rw [integral_add hfrsq hgysq, integral_const_mul]
    _ = (∫ z, (r z.1 - condExp m D (fun z => z.2) z) ^ 2 ∂D)
        + ∫ z, (condExp m D (fun z => z.2) z - z.2) ^ 2 ∂D := by
          rw [hcross]
          ring

@[blueprint "thm:atb-strictly-ex-ante-truthful"
  (statement := /-- Let $T$ be a positive integer, let $X$ be a measurable space, and let $D$ be a probability
  distribution of pairs $(x,y) \in X \times \mathbb R$ whose label is binary, in the sense that
  $y \in \{0,1\}$ for $D$-almost every pair $(x,y)$. Let $r : X \to \mathbb R$ be a measurable predictor and let
  $p : X \to \mathbb R$ be a ground-truth predictor for $D$ in the sense of \cref{def:is-ground-truth}, so that
  $(x,y) \mapsto p(x)$ agrees $D$-almost everywhere with $\mathbb E_D[\,y \mid x\,]$; assume moreover that
  $r(x) \in [0,1]$ and $p(x) \in [0,1]$ for every $x \in X$. If the expected ex-ante ATB errors of
  \cref{def:ex-ante-atb-error} satisfy
  \[
    \mathrm{ExAnteATB}_D(r) \;\le\; \mathrm{ExAnteATB}_D(p),
  \]
  then $(x,y) \mapsto r(x)$ agrees $D$-almost everywhere with $(x,y) \mapsto p(x)$. Thus, up to
  $D$-almost-everywhere equality, the ground-truth predictor is the unique minimizer of the expected ex-ante ATB
  error among measurable predictors with values in $[0,1]$: the averaged two-bin calibration error of
  \cref{def:averaged-two-bin} is strictly ex-ante truthful. -/)
  (proof := /-- Let $c=\mathbb E_D[Y\mid x]$. Binary labels are integrable and lie in $[0,1]$ almost everywhere; since $p=c$ almost everywhere, the same bounds hold for $c$. Replace $r(x)$ and $c$ outside the binary-label event by the observed label, and truncate $c$ pointwise to $[0,1]$. These representatives are measurable, have pointwise residual bounded by one, and are almost everywhere equal to the original reports. Coordinatewise almost-everywhere equality lifts to the product sample law, so the expected errors are unchanged.

  Apply \cref{lem:atb-ex-ante-formula} to both representatives. For the ground-truth representative, each threshold-bin mean vanishes by \cref{lem:atb-condexp-weighted-integral-zero}, applied to the corresponding $\{0,1\}$-valued threshold indicator. The threshold contribution for $r$ is nonnegative. By \cref{lem:atb-brier-gap},
  \[
    \int(r-Y)^2\,dD=\int(r-c)^2\,dD+\int(c-Y)^2\,dD.
  \]
  Consequently the assumed error inequality implies $T^{-1}\int(r-c)^2\,dD\le0$. The integrand and $T^{-1}$ are nonnegative, hence this integral is zero. Therefore $(r-c)^2=0$ almost everywhere, so $r=c=p$ almost everywhere. -/)
  (title := /-- Strict ex-ante truthfulness of ATB -/)
  (latexEnv := "theorem")]
theorem atb_strictly_ex_ante_truthful {X : Type*} [MeasurableSpace X] (T : ℕ) (hT : 0 < T)
    (D : Measure (X × ℝ)) [IsProbabilityMeasure D] (r p : X → ℝ)
    (hy : ∀ᵐ z ∂D, z.2 = 0 ∨ z.2 = 1) (hrm : Measurable r)
    (hp : is_ground_truth D p)
    (hr : ∀ x, r x ∈ Set.Icc (0 : ℝ) 1) (hpmem : ∀ x, p x ∈ Set.Icc (0 : ℝ) 1)
    (hle : ex_ante_atb_error T D r ≤ ex_ante_atb_error T D p) :
    (fun z : X × ℝ => r z.1) =ᵐ[D] (fun z : X × ℝ => p z.1) := by
  classical
  let m : MeasurableSpace (X × ℝ) :=
    MeasurableSpace.comap (Prod.fst : X × ℝ → X)
      (inferInstance : MeasurableSpace X)
  let m0 : MeasurableSpace (X × ℝ) :=
    @Prod.instMeasurableSpace X ℝ (inferInstance : MeasurableSpace X)
      (inferInstance : MeasurableSpace ℝ)
  have hm : m ≤ m0 := by
    dsimp [m]
    exact (@measurable_fst X ℝ (inferInstance : MeasurableSpace X)
      (inferInstance : MeasurableSpace ℝ)).comap_le
  change (fun z : X × ℝ => p z.1) =ᵐ[D] condExp m D (fun z => z.2) at hp
  have hy0 : ∀ᵐ z ∂D, 0 ≤ z.2 := by
    filter_upwards [hy] with z hz
    rcases hz with hz | hz <;> simp [hz]
  have hy1 : ∀ᵐ z ∂D, z.2 ≤ 1 := by
    filter_upwards [hy] with z hz
    rcases hz with hz | hz <;> simp [hz]
  have hyint : Integrable (fun z : X × ℝ => z.2) D := by
    exact (integrable_const (1 : ℝ)).mono' measurable_snd.aestronglyMeasurable
      (by
        filter_upwards [hy0, hy1] with z hz0 hz1
        rw [Real.norm_eq_abs, abs_of_nonneg hz0]
        exact hz1)
  have hce0 : ∀ᵐ z ∂D, 0 ≤ condExp m D (fun z : X × ℝ => z.2) z := by
    filter_upwards [hp] with z hz
    rw [← hz]
    exact (hpmem z.1).1
  have hce1 : ∀ᵐ z ∂D, condExp m D (fun z : X × ℝ => z.2) z ≤ 1 := by
    filter_upwards [hp] with z hz
    rw [← hz]
    exact (hpmem z.1).2
  let chat : X × ℝ → ℝ := fun z =>
    max 0 (min 1 (condExp m D (fun z : X × ℝ => z.2) z))
  have hchatm : Measurable[m] chat := by
    have hcem : Measurable[m] (condExp m D (fun z : X × ℝ => z.2)) :=
      MeasureTheory.stronglyMeasurable_condExp.measurable
    exact measurable_const.max (measurable_const.min hcem)
  have hchatm0 : Measurable[m0] chat := hchatm.mono hm le_rfl
  have hchatmem : ∀ z, chat z ∈ Set.Icc (0 : ℝ) 1 := by
    intro z
    dsimp [chat]
    constructor <;> simp
  have hchat_eq : chat =ᵐ[D] condExp m D (fun z : X × ℝ => z.2) := by
    filter_upwards [hce0, hce1] with z hz0 hz1
    simp [chat, max_eq_right hz0, min_eq_right hz1]
  let good : Set (X × ℝ) := {z | z.2 = 0 ∨ z.2 = 1}
  have hgood : MeasurableSet[m0] good := by
    dsimp [good]
    exact (measurableSet_eq_fun measurable_snd measurable_const).union
      (measurableSet_eq_fun measurable_snd measurable_const)
  let ρr : X × ℝ → ℝ := fun z => if z ∈ good then r z.1 else z.2
  let ρp : X × ℝ → ℝ := fun z => if z ∈ good then chat z else z.2
  have hρr : Measurable[m0] ρr :=
    Measurable.ite hgood (hrm.comp measurable_fst) measurable_snd
  have hρp : Measurable[m0] ρp :=
    Measurable.ite hgood hchatm0 measurable_snd
  have hρrb : ∀ z, |ρr z - z.2| ≤ 1 := by
    intro z
    by_cases hz : z ∈ good
    · rcases hz with hz | hz
      · simp [ρr, good, hz]
        exact abs_le.2 ⟨by linarith [(hr z.1).1], by linarith [(hr z.1).2]⟩
      · simp [ρr, good, hz]
        exact abs_le.2 ⟨by linarith [(hr z.1).1], by linarith [(hr z.1).2]⟩
    · simp [ρr, hz]
  have hρpb : ∀ z, |ρp z - z.2| ≤ 1 := by
    intro z
    by_cases hz : z ∈ good
    · rcases hz with hz | hz
      · simp [ρp, good, hz]
        exact abs_le.2 ⟨by linarith [(hchatmem z).1], by linarith [(hchatmem z).2]⟩
      · simp [ρp, good, hz]
        exact abs_le.2 ⟨by linarith [(hchatmem z).1], by linarith [(hchatmem z).2]⟩
    · simp [ρp, hz]
  have hρr_eq : ρr =ᵐ[D] fun z : X × ℝ => r z.1 := by
    filter_upwards [hy] with z hz
    simp [ρr, good, hz]
  have hρp_ce : ρp =ᵐ[D] condExp m D (fun z : X × ℝ => z.2) := by
    filter_upwards [hy, hchat_eq] with z hz hcz
    simp [ρp, good, hz, hcz]
  have hρp_eq : ρp =ᵐ[D] fun z : X × ℝ => p z.1 := hρp_ce.trans hp.symm
  have hlift_avg (f g : X × ℝ → ℝ) (hfg : f =ᵐ[D] g) :
      (fun s : Fin T → X × ℝ => averaged_two_bin (fun t => f (s t)) (fun t => (s t).2)) =ᵐ[
        Measure.pi fun _ : Fin T => D]
      fun s => averaged_two_bin (fun t => g (s t)) (fun t => (s t).2) := by
    have ht (t : Fin T) : (fun s : Fin T → X × ℝ => f (s t)) =ᵐ[
        Measure.pi fun _ : Fin T => D] fun s => g (s t) := by
      change f ∘ Function.eval t =ᵐ[Measure.pi fun _ : Fin T => D] g ∘ Function.eval t
      exact (MeasureTheory.measurePreserving_eval
        (fun _ : Fin T => D) t).quasiMeasurePreserving.ae_eq_comp hfg
    have hall : ∀ᵐ s ∂(Measure.pi fun _ : Fin T => D), ∀ t, f (s t) = g (s t) :=
      MeasureTheory.ae_all_iff.mpr ht
    filter_upwards [hall] with s hs
    congr 1
    funext t
    exact hs t
  have herr_r : ex_ante_atb_error T D r =
      ∫ s : Fin T → X × ℝ, averaged_two_bin (fun t => ρr (s t)) (fun t => (s t).2)
        ∂(Measure.pi fun _ => D) := by
    rw [ex_ante_atb_error]
    exact integral_congr_ae (hlift_avg ρr (fun z => r z.1) hρr_eq).symm
  have herr_p : ex_ante_atb_error T D p =
      ∫ s : Fin T → X × ℝ, averaged_two_bin (fun t => ρp (s t)) (fun t => (s t).2)
        ∂(Measure.pi fun _ => D) := by
    rw [ex_ante_atb_error]
    exact integral_congr_ae (hlift_avg ρp (fun z => p z.1) hρp_eq).symm
  have hform_r := atb_ex_ante_formula T hT D ρr hρr hρrb
  have hform_p := atb_ex_ante_formula T hT D ρp hρp hρpb
  have hbias_lt (q : ℝ) :
      (∫ z, (if ρp z < q then ρp z - z.2 else 0) ∂D) = 0 := by
    let wq : X × ℝ → ℝ := fun z => if chat z < q then 1 else 0
    have hwq : Measurable[m] wq :=
      Measurable.ite (measurableSet_lt hchatm measurable_const) measurable_const measurable_const
    have hwqmem : ∀ z, wq z ∈ Set.Icc (0 : ℝ) 1 := by
      intro z
      dsimp [wq]
      split_ifs <;> norm_num
    have hz := atb_condexp_weighted_integral_zero D hyint wq hwq hwqmem
      hy0 hy1 hce0 hce1
    calc
      (∫ z, (if ρp z < q then ρp z - z.2 else 0) ∂D) =
          ∫ z, wq z * (condExp m D (fun z : X × ℝ => z.2) z - z.2) ∂D := by
            apply integral_congr_ae
            filter_upwards [hρp_ce, hchat_eq] with z hpz hcz
            rw [hpz, ← hcz]
            dsimp [wq]
            split_ifs <;> ring
      _ = 0 := hz
  have hbias_ge (q : ℝ) :
      (∫ z, (if q ≤ ρp z then ρp z - z.2 else 0) ∂D) = 0 := by
    let wq : X × ℝ → ℝ := fun z => if q ≤ chat z then 1 else 0
    have hwq : Measurable[m] wq :=
      Measurable.ite (measurableSet_le measurable_const hchatm) measurable_const measurable_const
    have hwqmem : ∀ z, wq z ∈ Set.Icc (0 : ℝ) 1 := by
      intro z
      dsimp [wq]
      split_ifs <;> norm_num
    have hz := atb_condexp_weighted_integral_zero D hyint wq hwq hwqmem
      hy0 hy1 hce0 hce1
    calc
      (∫ z, (if q ≤ ρp z then ρp z - z.2 else 0) ∂D) =
          ∫ z, wq z * (condExp m D (fun z : X × ℝ => z.2) z - z.2) ∂D := by
            apply integral_congr_ae
            filter_upwards [hρp_ce, hchat_eq] with z hpz hcz
            rw [hpz, ← hcz]
            dsimp [wq]
            split_ifs <;> ring
      _ = 0 := hz
  have hρr_brier : (∫ z, (ρr z - z.2) ^ 2 ∂D) =
      ∫ z, (r z.1 - z.2) ^ 2 ∂D := by
    apply integral_congr_ae
    filter_upwards [hρr_eq] with z hz
    rw [hz]
  have hρp_brier : (∫ z, (ρp z - z.2) ^ 2 ∂D) =
      ∫ z, (condExp m D (fun z : X × ℝ => z.2) z - z.2) ^ 2 ∂D := by
    apply integral_congr_ae
    filter_upwards [hρp_ce] with z hz
    rw [hz]
  let B : ℝ := ∫ q in (0 : ℝ)..1,
    ((∫ z, (if ρr z < q then ρr z - z.2 else 0) ∂D) ^ 2
      + (∫ z, (if q ≤ ρr z then ρr z - z.2 else 0) ∂D) ^ 2)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact intervalIntegral.integral_nonneg_of_forall (by norm_num) fun q => by positivity
  have hcoef0 : 0 ≤ ((T : ℝ) - 1) / (T : ℝ) := by
    apply div_nonneg
    · have hTone : (1 : ℕ) ≤ T := hT
      apply sub_nonneg.mpr
      exact_mod_cast hTone
    · positivity
  have hle' :
      1 / (T : ℝ) * (∫ z, (ρr z - z.2) ^ 2 ∂D)
          + ((T : ℝ) - 1) / (T : ℝ) * B
        ≤ 1 / (T : ℝ) * (∫ z, (ρp z - z.2) ^ 2 ∂D) := by
    calc
      1 / (T : ℝ) * (∫ z, (ρr z - z.2) ^ 2 ∂D)
          + ((T : ℝ) - 1) / (T : ℝ) * B =
          ∫ s : Fin T → X × ℝ,
            averaged_two_bin (fun t => ρr (s t)) (fun t => (s t).2)
              ∂(Measure.pi fun _ => D) := by
                rw [hform_r]
      _ = ex_ante_atb_error T D r := herr_r.symm
      _ ≤ ex_ante_atb_error T D p := hle
      _ = ∫ s : Fin T → X × ℝ,
            averaged_two_bin (fun t => ρp (s t)) (fun t => (s t).2)
              ∂(Measure.pi fun _ => D) := herr_p
      _ = 1 / (T : ℝ) * (∫ z, (ρp z - z.2) ^ 2 ∂D) := by
        rw [hform_p]
        simp_rw [hbias_lt, hbias_ge]
        simp
  have hbrier := atb_brier_gap D hyint r hrm hr hy0 hy1 hce0 hce1
  rw [hρr_brier, hρp_brier, hbrier] at hle'
  let G : ℝ := ∫ z, (r z.1 - condExp m D (fun z : X × ℝ => z.2) z) ^ 2 ∂D
  have hceint : Integrable (condExp m D (fun z : X × ℝ => z.2)) D :=
    MeasureTheory.integrable_condExp
  have hrint : Integrable (fun z : X × ℝ => r z.1) D := by
    exact (integrable_const (1 : ℝ)).mono' (hrm.comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hr z.1).1]
        exact (hr z.1).2)
  have hfr : Integrable
      (fun z : X × ℝ => r z.1 - condExp m D (fun z => z.2) z) D := hrint.sub hceint
  have hfrb : ∀ᵐ z ∂D, ‖r z.1 - condExp m D (fun z => z.2) z‖ ≤ 1 := by
    filter_upwards [hce0, hce1] with z hz0 hz1
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(hr z.1).1, (hr z.1).2]
  have hGint : Integrable
      (fun z : X × ℝ => (r z.1 - condExp m D (fun z => z.2) z) ^ 2) D := by
    simpa [pow_two] using hfr.bdd_mul hfr.aestronglyMeasurable hfrb
  have hG0 : 0 ≤ G := by
    dsimp [G]
    exact integral_nonneg fun z => sq_nonneg _
  have hinvpos : 0 < 1 / (T : ℝ) := one_div_pos.mpr (by positivity)
  have htail0 : 0 ≤ ((T : ℝ) - 1) / (T : ℝ) * B := mul_nonneg hcoef0 hB0
  have hGle : G ≤ 0 := by
    dsimp [G]
    nlinarith
  have hGeq : G = 0 := le_antisymm hGle hG0
  have hzsq : (fun z : X × ℝ =>
      (r z.1 - condExp m D (fun z => z.2) z) ^ 2) =ᵐ[D] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg _) hGint).mp hGeq
  have hrce : (fun z : X × ℝ => r z.1) =ᵐ[D]
      condExp m D (fun z : X × ℝ => z.2) := by
    filter_upwards [hzsq] with z hz
    change (r z.1 - condExp m D (fun z : X × ℝ => z.2) z) ^ 2 = 0 at hz
    nlinarith [sq_nonneg (r z.1 - condExp m D (fun z : X × ℝ => z.2) z)]
  exact hrce.trans hp.symm

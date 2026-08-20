import Architect
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory
open scoped BigOperators

@[blueprint "def:boolean-distinguishing-family"
  (statement := /-- A Boolean distinguishing family on a measurable space $\mathcal X$ is a countable collection $\mathcal F$ of measurable maps $f:\mathcal X\to\{0,1\}$ that is closed under pointwise complementation.  Countability ensures that the suprema over $\mathcal F$ appearing below are measurable random variables; since all constituent functions are Boolean-valued, those random variables are also uniformly bounded and hence integrable under every probability measure. -/)
  (title := /-- Boolean distinguishing families -/)
  (latexEnv := "definition")]
structure boolean_distinguishing_family (X : Type*) [MeasurableSpace X] where
  carrier : Set (X → Bool)
  carrier_countable : carrier.Countable
  measurable : ∀ f ∈ carrier, Measurable f
  complement_mem : ∀ f ∈ carrier, (fun x => ! (f x)) ∈ carrier

@[blueprint "def:boolean-value"
  (statement := /-- For $b\in\{0,1\}$, let $[b]\in\mathbb R$ denote $1$ when $b=1$ and $0$ when $b=0$. -/)
  (title := /-- Real value of a Boolean -/)
  (latexEnv := "definition")]
def boolean_value (b : Bool) : ℝ :=
  if b then 1 else 0

@[blueprint "def:rademacher-sign"
  (statement := /-- For $b\in\{0,1\}$, define the associated Rademacher sign by $\operatorname{sgn}_{\mathrm{Rad}}(b)=1$ when $b=1$ and $\operatorname{sgn}_{\mathrm{Rad}}(b)=-1$ when $b=0$. -/)
  (title := /-- Rademacher sign -/)
  (latexEnv := "definition")]
def rademacher_sign (b : Bool) : ℝ :=
  if b then 1 else -1

@[blueprint "def:fooling-distance"
  (statement := /-- Let $\mathcal F$ be a Boolean distinguishing family and let $P,Q$ be probability measures on $\mathcal X$.  Their fooling distance is
  \[
    d_{\mathcal F}(P,Q)
      =\sup_{f\in\mathcal F}\left|\mathbb E_P[f]-\mathbb E_Q[f]\right|.
  \]
  The supremum of the empty family is understood to be $0$. -/)
  (title := /-- Fooling distance -/)
  (latexEnv := "definition")]
noncomputable def fooling_distance {X : Type*} [MeasurableSpace X]
    (F : boolean_distinguishing_family X) (P Q : ProbabilityMeasure X) : ℝ :=
  sSup ((fun f : X → Bool =>
    |(∫ x, boolean_value (f x) ∂P.toMeasure) -
      (∫ x, boolean_value (f x) ∂Q.toMeasure)|) '' F.carrier)

@[blueprint "def:empirical-rademacher-complexity"
  (statement := /-- For a sample $S=(x_i)_{i=1}^m$ and a Boolean distinguishing family $\mathcal F$, define
  \[
  \widehat{\mathcal R}(\mathcal F,S)
   =\mathbb E_{\sigma\sim\{\pm1\}^m}
     \left[\sup_{f\in\mathcal F}
       \left|\frac1m\sum_{i=1}^m \sigma_i(2f(x_i)-1)\right|\right].
  \]
  Finite expectations are represented by normalized sums, and the conventions of $\mathbb R$ apply when $m=0$. -/)
  (title := /-- Empirical Rademacher complexity -/)
  (latexEnv := "definition")]
noncomputable def empirical_rademacher_complexity {X : Type*} [MeasurableSpace X]
    (F : boolean_distinguishing_family X) {m : ℕ} (S : Fin m → X) : ℝ :=
  ((2 : ℝ) ^ m)⁻¹ *
    ∑ σ : Fin m → Bool,
      sSup ((fun f : X → Bool =>
        |(m : ℝ)⁻¹ *
          ∑ i : Fin m,
            rademacher_sign (σ i) * (2 * boolean_value (f (S i)) - 1)|) '' F.carrier)

@[blueprint "def:distributional-rademacher-complexity"
  (statement := /-- For a probability measure $P$ on $\mathcal X$, define the distributional Rademacher complexity at sample size $m$ by the Bochner integral
  \[
    \mathcal R_m(\mathcal F,P)
      =\int_{\mathcal X^m}\widehat{\mathcal R}(\mathcal F,S)\,dP^m(S).
  \]
  The countability and Boolean boundedness in \cref{def:boolean-distinguishing-family} make the empirical-complexity sample functional measurable and integrable under $P^m$.  Thus this integral is the genuine expectation
  $\mathbb E_{S\sim P^m}[\widehat{\mathcal R}(\mathcal F,S)]$. -/)
  (title := /-- Distributional Rademacher complexity -/)
  (latexEnv := "definition")]
noncomputable def distributional_rademacher_complexity {X : Type*} [MeasurableSpace X]
    (F : boolean_distinguishing_family X) (m : ℕ) (P : ProbabilityMeasure X) : ℝ :=
  ∫ S, empirical_rademacher_complexity F S
    ∂(ProbabilityMeasure.pi (fun _ : Fin m => P)).toMeasure

@[blueprint "def:rademacher-complexity-promise"
  (statement := /-- Let $\mathcal F$ be a Boolean distinguishing family, let $P$ be a probability measure on $\mathcal X$, let $m\in\mathbb N$, and let $\rho\in\mathbb R$.  The Rademacher-complexity promise at threshold $\rho$ is the inequality
  $\mathcal R_m(\mathcal F,P)\leq\rho$.  By \cref{def:boolean-distinguishing-family, def:distributional-rademacher-complexity}, the quantity on the left is already a genuine expectation, so no separate integrability guard is required. -/)
  (title := /-- Rademacher-complexity promise -/)
  (latexEnv := "definition")]
def rademacher_complexity_promise {X : Type*} [MeasurableSpace X]
    (F : boolean_distinguishing_family X) (m : ℕ)
    (P : ProbabilityMeasure X) (ρ : ℝ) : Prop :=
  distributional_rademacher_complexity F m P ≤ ρ

@[blueprint "def:sample-event-probability"
  (statement := /-- If $S\sim P^n$ and $E\subseteq\mathcal X^n$ is an event, define $\Pr_{S\sim P^n}[E]$ to be the real-valued mass of $E$ under the finite product measure. -/)
  (title := /-- Probability of a sample event -/)
  (latexEnv := "definition")]
noncomputable def sample_event_probability {X : Type*} [MeasurableSpace X]
    (P : ProbabilityMeasure X) (n : ℕ) (E : Set (Fin n → X)) : ℝ :=
  (ProbabilityMeasure.pi (fun _ : Fin n => P)).toMeasure.real E

@[blueprint "def:empirical-probability-measure"
  (statement := /-- Given $P$ and a sample $S=(x_i)_{i=1}^n$, let $\widehat P_S$ be the uniform probability measure on the entries of $S$.  At the degenerate sample size $n=0$, set $\widehat P_S=P$. -/)
  (title := /-- Empirical probability measure -/)
  (latexEnv := "definition")]
noncomputable def empirical_probability_measure {X : Type*} [MeasurableSpace X]
    (P : ProbabilityMeasure X) {n : ℕ} (S : Fin n → X) : ProbabilityMeasure X :=
  if h : n = 0 then P
  else
    letI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero h⟩⟩
    ⟨((PMF.uniformOfFintype (Fin n)).map S).toMeasure, inferInstance⟩

@[blueprint "def:sample-complexity-bound"
  (statement := /-- For $C>0$, define the explicit representative
  \[
    B_C(m,\epsilon,\delta)
      =m+\left\lceil
        \frac{C(1+\log(1/\delta))}{\epsilon^2}
      \right\rceil.
  \]
  On $0<\delta<1$, this has the asymptotic form
  $m+O(\log(1/\delta)/\epsilon^2)$ as $\delta\downarrow0$. -/)
  (title := /-- Sample-complexity bound -/)
  (latexEnv := "definition")]
noncomputable def sample_complexity_bound (C : ℝ) (m : ℕ) (ε δ : ℝ) : ℕ :=
  m + Nat.ceil (C * (1 + Real.log (1 / δ)) / ε ^ 2)

@[blueprint "def:testable-distribution-learner"
  (statement := /-- A testable distribution learner with $n$ samples is a rule that, from a sample in $\mathcal X^n$, either rejects or returns a probability measure on $\mathcal X$. -/)
  (title := /-- Testable distribution learners -/)
  (latexEnv := "definition")]
structure testable_distribution_learner (X : Type*) [MeasurableSpace X] where
  sampleCount : ℕ
  run : (Fin sampleCount → X) → Option (ProbabilityMeasure X)

@[blueprint "def:learner-good-run"
  (statement := /-- A run of a learner is good at parameters $(m,\eta,\rho)$ if it returns an $\eta$-accurate distribution, or if it rejects and the Rademacher-complexity promise of
  \cref{def:rademacher-complexity-promise} fails for the input distribution at threshold $\rho$.  Thus every good run under that promise returns an $\eta$-accurate distribution. -/)
  (title := /-- Good runs of a testable learner -/)
  (latexEnv := "definition")]
def learner_good_run {X : Type*} [MeasurableSpace X]
    (L : testable_distribution_learner X) (F : boolean_distinguishing_family X)
    (P : ProbabilityMeasure X) (m : ℕ) (η ρ : ℝ)
    (S : Fin L.sampleCount → X) : Prop :=
  match L.run S with
  | none => ¬ rademacher_complexity_promise F m P ρ
  | some P_hat => fooling_distance F P P_hat ≤ η

@[blueprint "def:is-rademacher-testable-distribution-learner"
  (statement := /-- A learner $L$ is an $(m,\eta,\rho,\delta)$-Rademacher testable distribution learner against $\mathcal F$ if, for every input distribution $P$, a sample from $P^{n}$, where $n$ is the sample count of $L$, yields a good run with probability at least $1-\delta$. -/)
  (title := /-- Rademacher-testable distribution learning guarantee -/)
  (latexEnv := "definition")]
def is_rademacher_testable_distribution_learner {X : Type*} [MeasurableSpace X]
    (L : testable_distribution_learner X) (F : boolean_distinguishing_family X)
    (m : ℕ) (η ρ δ : ℝ) : Prop :=
  ∀ P : ProbabilityMeasure X,
    sample_event_probability P L.sampleCount
      {S | learner_good_run L F P m η ρ S} ≥ 1 - δ

@[blueprint "def:identity-tester"
  (statement := /-- An identity tester using $n$ samples is a measurable Boolean decision rule on $\mathcal X^n\times\mathcal X^n$.  Its first input is a sample from the unknown distribution, and its second input is an independent sample generated from the explicit reference distribution.  The sample complexity counts the samples requested from the unknown distribution; the reference samples are internally available from the explicit law. -/)
  (title := /-- Identity testers -/)
  (latexEnv := "definition")]
structure identity_tester (X : Type*) [MeasurableSpace X] where
  sampleCount : ℕ
  decide : ((Fin sampleCount → X) × (Fin sampleCount → X)) → Bool
  measurable_decide : Measurable decide

@[blueprint "def:equivalence-tester"
  (statement := /-- An equivalence tester using $n$ samples per input oracle is a measurable Boolean decision rule on the product measurable space $\mathcal X^n\times\mathcal X^n$.  Its sample complexity is counted per input distribution. -/)
  (title := /-- Equivalence testers -/)
  (latexEnv := "definition")]
structure equivalence_tester (X : Type*) [MeasurableSpace X] where
  sampleCount : ℕ
  decide : ((Fin sampleCount → X) × (Fin sampleCount → X)) → Bool
  measurable_decide : Measurable decide

@[blueprint "def:measurable-decision-event"
  (statement := /-- If $d:\Omega\to\{\mathtt{false},\mathtt{true}\}$ is measurable and $b$ is a Boolean outcome, then $d^{-1}(\{b\})$, equipped with the preimage measurability proof, is the measurable event on which $d$ returns $b$. -/)
  (title := /-- Measurable event of a Boolean decision -/)
  (latexEnv := "definition")]
def measurable_decision_event {Ω : Type*} [MeasurableSpace Ω]
    (d : Ω → Bool) (hd : Measurable d) (b : Bool) :
    {E : Set Ω // MeasurableSet E} :=
  ⟨d ⁻¹' {b}, hd (measurableSet_singleton b)⟩

@[blueprint "def:identity-acceptance-probability"
  (statement := /-- Let $T$ be an identity tester, let $P$ be the unknown distribution, and let $P_{\mathrm{ref}}$ be the explicit reference distribution.  The acceptance event is the measurable event from \cref{def:measurable-decision-event} associated with the outcome $\mathtt{true}$.  The acceptance probability is its mass under the product law $P^n\times P_{\mathrm{ref}}^n$, so the two samples are independent. -/)
  (title := /-- Identity-test acceptance probability -/)
  (latexEnv := "definition")]
noncomputable def identity_acceptance_probability {X : Type*} [MeasurableSpace X]
    (T : identity_tester X) (P P_ref : ProbabilityMeasure X) : ℝ :=
  ((ProbabilityMeasure.pi (fun _ : Fin T.sampleCount => P)).toMeasure.prod
    (ProbabilityMeasure.pi (fun _ : Fin T.sampleCount => P_ref)).toMeasure).real
      (measurable_decision_event T.decide T.measurable_decide true)

@[blueprint "def:identity-rejection-probability"
  (statement := /-- Let $T$ be an identity tester, let $P$ be the unknown distribution, and let $P_{\mathrm{ref}}$ be the explicit reference distribution.  The rejection event is the measurable event from \cref{def:measurable-decision-event} associated with the outcome $\mathtt{false}$.  The rejection probability is its mass under the product law $P^n\times P_{\mathrm{ref}}^n$, so the two samples are independent. -/)
  (title := /-- Identity-test rejection probability -/)
  (latexEnv := "definition")]
noncomputable def identity_rejection_probability {X : Type*} [MeasurableSpace X]
    (T : identity_tester X) (P P_ref : ProbabilityMeasure X) : ℝ :=
  ((ProbabilityMeasure.pi (fun _ : Fin T.sampleCount => P)).toMeasure.prod
    (ProbabilityMeasure.pi (fun _ : Fin T.sampleCount => P_ref)).toMeasure).real
      (measurable_decision_event T.decide T.measurable_decide false)

@[blueprint "def:equivalence-acceptance-probability"
  (statement := /-- The acceptance event of a two-sample tester $T$ on $(P,Q)$ is the measurable event from \cref{def:measurable-decision-event} associated with the outcome $\mathtt{true}$.  Its probability is the mass of this event under $P^n\times Q^n$. -/)
  (title := /-- Equivalence-test acceptance probability -/)
  (latexEnv := "definition")]
noncomputable def equivalence_acceptance_probability {X : Type*} [MeasurableSpace X]
    (T : equivalence_tester X) (P Q : ProbabilityMeasure X) : ℝ :=
  ((ProbabilityMeasure.pi (fun _ : Fin T.sampleCount => P)).toMeasure.prod
    (ProbabilityMeasure.pi (fun _ : Fin T.sampleCount => Q)).toMeasure).real
      (measurable_decision_event T.decide T.measurable_decide true)

@[blueprint "def:equivalence-rejection-probability"
  (statement := /-- The rejection event of a two-sample tester $T$ on $(P,Q)$ is the measurable event from \cref{def:measurable-decision-event} associated with the outcome $\mathtt{false}$.  Its probability is the mass of this event under $P^n\times Q^n$. -/)
  (title := /-- Equivalence-test rejection probability -/)
  (latexEnv := "definition")]
noncomputable def equivalence_rejection_probability {X : Type*} [MeasurableSpace X]
    (T : equivalence_tester X) (P Q : ProbabilityMeasure X) : ℝ :=
  ((ProbabilityMeasure.pi (fun _ : Fin T.sampleCount => P)).toMeasure.prod
    (ProbabilityMeasure.pi (fun _ : Fin T.sampleCount => Q)).toMeasure).real
      (measurable_decision_event T.decide T.measurable_decide false)

@[blueprint "def:is-identity-tester"
  (statement := /-- Let $P_{\mathrm{ref}}$ be an explicit distribution from which the tester can generate independent reference samples.  A measurable tester $T$ is an $(\epsilon,\delta)$-identity tester to $P_{\mathrm{ref}}$ against $\mathcal F$ if, under the product law of an unknown sample and an independent reference sample, it accepts every input equal to $P_{\mathrm{ref}}$ with probability at least $1-\delta$, and rejects every input at fooling distance greater than $\epsilon$ from $P_{\mathrm{ref}}$ with probability at least $1-\delta$. -/)
  (title := /-- Correctness of an identity tester -/)
  (latexEnv := "definition")]
def is_identity_tester {X : Type*} [MeasurableSpace X]
    (T : identity_tester X) (F : boolean_distinguishing_family X)
    (P_ref : ProbabilityMeasure X) (ε δ : ℝ) : Prop :=
  (∀ P : ProbabilityMeasure X, P = P_ref →
      identity_acceptance_probability T P P_ref ≥ 1 - δ) ∧
  (∀ P : ProbabilityMeasure X, fooling_distance F P P_ref > ε →
      identity_rejection_probability T P P_ref ≥ 1 - δ)

@[blueprint "def:is-equivalence-tester-under-rademacher-promise"
  (statement := /-- A measurable tester $T$ is an $(\epsilon,\delta)$-equivalence tester under the Rademacher promise at sample size $m$ if, whenever
  the numerical bound in \cref{def:rademacher-complexity-promise} holds for $P$ or for $Q$ at threshold $\epsilon/16$, it accepts $P=Q$ and rejects
  $d_{\mathcal F}(P,Q)>\epsilon$, in each case with probability at least
  $1-\delta$.  The measurability field of $T$ ensures that its acceptance and rejection quantities are probabilities of measurable events. -/)
  (title := /-- Correctness under the Rademacher promise -/)
  (latexEnv := "definition")]
def is_equivalence_tester_under_rademacher_promise
    {X : Type*} [MeasurableSpace X]
    (T : equivalence_tester X) (F : boolean_distinguishing_family X)
    (m : ℕ) (ε δ : ℝ) : Prop :=
  ∀ P Q : ProbabilityMeasure X,
    (rademacher_complexity_promise F m P (ε / 16) ∨
      rademacher_complexity_promise F m Q (ε / 16)) →
    (P = Q → equivalence_acceptance_probability T P Q ≥ 1 - δ) ∧
    (fooling_distance F P Q > ε →
      equivalence_rejection_probability T P Q ≥ 1 - δ)

@[blueprint "def:learner-equivalence-decision"
  (statement := /-- Given a testable learner $L$, run it on each component of a pair of samples.  Reject if either execution rejects; otherwise, with outputs $\widehat P,\widehat Q$, accept exactly when
  $d_{\mathcal F}(\widehat P,\widehat Q)\leq\epsilon/2$. -/)
  (title := /-- Learner-based equivalence decision rule -/)
  (latexEnv := "definition")]
noncomputable def learner_equivalence_decision
    {X : Type*} [MeasurableSpace X]
    (L : testable_distribution_learner X)
    (F : boolean_distinguishing_family X) (ε : ℝ) :
    ((Fin L.sampleCount → X) × (Fin L.sampleCount → X)) → Bool :=
  fun S =>
    match L.run S.1, L.run S.2 with
    | some P_hat, some Q_hat =>
        if fooling_distance F P_hat Q_hat ≤ ε / 2 then true else false
    | _, _ => false

@[blueprint "def:equivalence-tester-from-learner"
  (statement := /-- Let $L$ be a testable learner and suppose that the paired-sample decision rule of \cref{def:learner-equivalence-decision} is measurable.  The corresponding equivalence tester has the same sample count as $L$ and uses that measurable rule. -/)
  (title := /-- Equivalence tester obtained from a learner -/)
  (latexEnv := "definition")]
noncomputable def equivalence_tester_from_learner
    {X : Type*} [MeasurableSpace X]
    (L : testable_distribution_learner X)
    (F : boolean_distinguishing_family X) (ε : ℝ)
    (h_decide : Measurable (learner_equivalence_decision L F ε)) :
    equivalence_tester X where
  sampleCount := L.sampleCount
  decide := learner_equivalence_decision L F ε
  measurable_decide := h_decide

@[blueprint "lem:empirical-rademacher-measurable-bounded-local"
  (statement := /-- Let $\mathcal X$ be a measurable space, let $\mathcal F$ be a countable family of measurable Boolean maps on $\mathcal X$ closed under pointwise complementation, and let $n\geq1$.  Then the map $S\mapsto\widehat{\mathcal R}(\mathcal F,S)$ is measurable and takes values in $[0,1]$. -/)
  (proof := /-- For a fixed sign vector and a fixed $f\in\mathcal F$, the normalized signed sum in \cref{def:empirical-rademacher-complexity} is measurable by the measurability clause in \cref{def:boolean-distinguishing-family}.  Its absolute value is at most $1$, since every summand has absolute value $1$.  The supremum over $f$ is measurable because $\mathcal F$ is countable, remains in $[0,1]$, and the finite normalized average over sign vectors preserves measurability and these bounds. -/)
  (title := /-- Measurability and boundedness of empirical Rademacher complexity -/)
  (latexEnv := "lemma")]
lemma empirical_rademacher_measurable_bounded_local
    {X : Type*} [MeasurableSpace X]
    (F : boolean_distinguishing_family X) {n : ℕ} (hn : 0 < n) :
    Measurable (fun S : Fin n → X => empirical_rademacher_complexity F S) ∧
      ∀ S : Fin n → X, 0 ≤ empirical_rademacher_complexity F S ∧
        empirical_rademacher_complexity F S ≤ 1 := by
  classical
  have hscore_meas :
      ∀ (σ : Fin n → Bool) (f : X → Bool), f ∈ F.carrier →
        Measurable (fun S : Fin n → X =>
          |(n : ℝ)⁻¹ * ∑ i : Fin n,
            rademacher_sign (σ i) *
              (2 * boolean_value (f (S i)) - 1)|) := by
    intro σ f hf
    apply Measurable.abs
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    apply Measurable.const_mul
    apply Measurable.sub_const
    apply Measurable.const_mul
    exact (measurable_of_finite boolean_value).comp
      ((F.measurable f hf).comp (measurable_pi_apply i))
  have hscore_bound :
      ∀ (S : Fin n → X) (σ : Fin n → Bool) (f : X → Bool),
        |(n : ℝ)⁻¹ * ∑ i : Fin n,
          rademacher_sign (σ i) *
            (2 * boolean_value (f (S i)) - 1)| ≤ 1 := by
    intro S σ f
    have hterm :
        ∀ i : Fin n,
          |rademacher_sign (σ i) *
              (2 * boolean_value (f (S i)) - 1)| = 1 := by
      intro i
      cases hσ : σ i <;> cases hf : f (S i) <;>
        norm_num [rademacher_sign, boolean_value, hσ, hf]
    calc
      |(n : ℝ)⁻¹ * ∑ i : Fin n,
          rademacher_sign (σ i) *
            (2 * boolean_value (f (S i)) - 1)| =
          (n : ℝ)⁻¹ *
            |∑ i : Fin n,
              rademacher_sign (σ i) *
                (2 * boolean_value (f (S i)) - 1)| := by
        rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
      _ ≤ (n : ℝ)⁻¹ *
          ∑ i : Fin n,
            |rademacher_sign (σ i) *
              (2 * boolean_value (f (S i)) - 1)| := by
        exact mul_le_mul_of_nonneg_left
          (Finset.abs_sum_le_sum_abs
            (fun i : Fin n =>
              rademacher_sign (σ i) *
                (2 * boolean_value (f (S i)) - 1)) Finset.univ)
          (inv_nonneg.mpr (Nat.cast_nonneg n))
      _ = 1 := by
        simp_rw [hterm]
        simp [hn.ne']
  have hsup_meas :
      ∀ σ : Fin n → Bool,
        Measurable (fun S : Fin n → X =>
          sSup ((fun f : X → Bool =>
            |(n : ℝ)⁻¹ * ∑ i : Fin n,
              rademacher_sign (σ i) *
                (2 * boolean_value (f (S i)) - 1)|) '' F.carrier)) := by
    intro σ
    exact Measurable.sSup F.carrier_countable (hscore_meas σ)
  have hsup_bounds :
      ∀ (S : Fin n → X) (σ : Fin n → Bool),
        0 ≤ sSup ((fun f : X → Bool =>
          |(n : ℝ)⁻¹ * ∑ i : Fin n,
            rademacher_sign (σ i) *
              (2 * boolean_value (f (S i)) - 1)|) '' F.carrier) ∧
        sSup ((fun f : X → Bool =>
          |(n : ℝ)⁻¹ * ∑ i : Fin n,
            rademacher_sign (σ i) *
              (2 * boolean_value (f (S i)) - 1)|) '' F.carrier) ≤ 1 := by
    intro S σ
    constructor
    · exact Real.sSup_nonneg (fun x hx => by
        rcases hx with ⟨f, hf, rfl⟩
        exact abs_nonneg _)
    · by_cases hF : F.carrier = ∅
      · simp [hF]
      · apply csSup_le (Set.nonempty_iff_ne_empty.mpr hF |>.image _)
        rintro _ ⟨f, hf, rfl⟩
        exact hscore_bound S σ f
  constructor
  · unfold empirical_rademacher_complexity
    fun_prop
  · intro S
    unfold empirical_rademacher_complexity
    constructor
    · exact mul_nonneg (inv_nonneg.mpr (by positivity))
        (Finset.sum_nonneg (fun σ hσ => (hsup_bounds S σ).1))
    · calc
        ((2 : ℝ) ^ n)⁻¹ *
            ∑ σ : Fin n → Bool,
              sSup ((fun f : X → Bool =>
                |(n : ℝ)⁻¹ * ∑ i : Fin n,
                  rademacher_sign (σ i) *
                    (2 * boolean_value (f (S i)) - 1)|) '' F.carrier) ≤
            ((2 : ℝ) ^ n)⁻¹ * ∑ _σ : Fin n → Bool, (1 : ℝ) := by
          apply mul_le_mul_of_nonneg_left
          · exact Finset.sum_le_sum (fun σ hσ => (hsup_bounds S σ).2)
          · positivity
        _ = 1 := by simp

@[blueprint "lem:empirical-rademacher-bounded-differences-local"
  (statement := /-- Let $\mathcal X$ be a measurable space, let $\mathcal F$ be a Boolean distinguishing family on $\mathcal X$, and let $n\geq1$.  If two samples in $\mathcal X^n$ differ in one coordinate, then their empirical Rademacher complexities differ by at most $2/n$. -/)
  (proof := /-- Fix a sign vector.  Replacing one sample coordinate changes each normalized signed sum in \cref{def:empirical-rademacher-complexity} by at most $2/n$.  The reverse triangle inequality transfers this estimate through the absolute value, taking the supremum over $f\in\mathcal F$ preserves it, and the normalized finite average over sign vectors preserves it once more. -/)
  (title := /-- Bounded differences for empirical Rademacher complexity -/)
  (latexEnv := "lemma")]
lemma empirical_rademacher_bounded_differences_local
    {X : Type*} [MeasurableSpace X]
    (F : boolean_distinguishing_family X) {n : ℕ} (hn : 0 < n) :
    ∀ (S : Fin n → X) (k : Fin n) (z' : X),
      |empirical_rademacher_complexity F S -
        empirical_rademacher_complexity F (Function.update S k z')| ≤
          2 / (n : ℝ) := by
  classical
  have hterm_abs :
      ∀ (S : Fin n → X) (σ : Fin n → Bool) (f : X → Bool) (i : Fin n),
        |rademacher_sign (σ i) *
          (2 * boolean_value (f (S i)) - 1)| = 1 := by
    intro S σ f i
    cases hσ : σ i <;> cases hf : f (S i) <;>
      norm_num [rademacher_sign, boolean_value, hσ, hf]
  have hscore_bound :
      ∀ (S : Fin n → X) (σ : Fin n → Bool) (f : X → Bool),
        |(n : ℝ)⁻¹ * ∑ i : Fin n,
          rademacher_sign (σ i) *
            (2 * boolean_value (f (S i)) - 1)| ≤ 1 := by
    intro S σ f
    calc
      |(n : ℝ)⁻¹ * ∑ i : Fin n,
          rademacher_sign (σ i) *
            (2 * boolean_value (f (S i)) - 1)| =
          (n : ℝ)⁻¹ *
            |∑ i : Fin n,
              rademacher_sign (σ i) *
                (2 * boolean_value (f (S i)) - 1)| := by
        rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
      _ ≤ (n : ℝ)⁻¹ *
          ∑ i : Fin n,
            |rademacher_sign (σ i) *
              (2 * boolean_value (f (S i)) - 1)| := by
        exact mul_le_mul_of_nonneg_left
          (Finset.abs_sum_le_sum_abs _ Finset.univ)
          (inv_nonneg.mpr (Nat.cast_nonneg n))
      _ = 1 := by
        simp_rw [hterm_abs S σ f]
        simp [hn.ne']
  have hscore_update :
      ∀ (S : Fin n → X) (σ : Fin n → Bool) (f : X → Bool)
        (k : Fin n) (z' : X),
        abs (abs ((n : ℝ)⁻¹ * ∑ i : Fin n,
            rademacher_sign (σ i) *
              (2 * boolean_value (f (S i)) - 1)) -
          abs ((n : ℝ)⁻¹ * ∑ i : Fin n,
            rademacher_sign (σ i) *
              (2 * boolean_value (f ((Function.update S k z') i)) - 1))) ≤
            2 / (n : ℝ) := by
    intro S σ f k z'
    have hsum :
        (∑ i : Fin n,
            rademacher_sign (σ i) *
              (2 * boolean_value (f (S i)) - 1)) -
          (∑ i : Fin n,
            rademacher_sign (σ i) *
              (2 * boolean_value (f ((Function.update S k z') i)) - 1)) =
        rademacher_sign (σ k) *
            (2 * boolean_value (f (S k)) - 1) -
          rademacher_sign (σ k) *
            (2 * boolean_value (f z') - 1) := by
      rw [← Finset.sum_sub_distrib]
      calc
        (∑ i : Fin n,
            (rademacher_sign (σ i) *
                (2 * boolean_value (f (S i)) - 1) -
              rademacher_sign (σ i) *
                (2 * boolean_value
                  (f ((Function.update S k z') i)) - 1))) =
            rademacher_sign (σ k) *
                (2 * boolean_value (f (S k)) - 1) -
              rademacher_sign (σ k) *
                (2 * boolean_value
                  (f ((Function.update S k z') k)) - 1) := by
          apply Finset.sum_eq_single k
          · intro i hi hik
            rw [Function.update_of_ne hik]
            ring
          · simp
        _ = _ := by rw [Function.update_self]
    have hk :
        |rademacher_sign (σ k) *
              (2 * boolean_value (f (S k)) - 1) -
            rademacher_sign (σ k) *
              (2 * boolean_value (f z') - 1)| ≤ 2 := by
      calc
        _ ≤ |rademacher_sign (σ k) *
              (2 * boolean_value (f (S k)) - 1)| +
            |rademacher_sign (σ k) *
              (2 * boolean_value (f z') - 1)| := abs_sub _ _
        _ = 2 := by
          rw [hterm_abs S σ f k]
          cases hσ : σ k <;> cases hf : f z' <;>
            norm_num [rademacher_sign, boolean_value, hσ, hf]
    calc
      _ ≤ |(n : ℝ)⁻¹ *
            (∑ i : Fin n,
                rademacher_sign (σ i) *
                  (2 * boolean_value (f (S i)) - 1)) -
          (n : ℝ)⁻¹ *
            (∑ i : Fin n,
              rademacher_sign (σ i) *
                (2 * boolean_value
                  (f ((Function.update S k z') i)) - 1))| :=
        abs_abs_sub_abs_le_abs_sub _ _
      _ = (n : ℝ)⁻¹ *
          |rademacher_sign (σ k) *
              (2 * boolean_value (f (S k)) - 1) -
            rademacher_sign (σ k) *
              (2 * boolean_value (f z') - 1)| := by
        rw [← mul_sub, hsum, abs_mul,
          abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
      _ ≤ (n : ℝ)⁻¹ * 2 :=
        mul_le_mul_of_nonneg_left hk
          (inv_nonneg.mpr (Nat.cast_nonneg n))
      _ = 2 / (n : ℝ) := by ring
  intro S k z'
  by_cases hF : F.carrier = ∅
  · simp [empirical_rademacher_complexity, hF]
    positivity
  have hFne : F.carrier.Nonempty := Set.nonempty_iff_ne_empty.mpr hF
  have hsup_update :
      ∀ σ : Fin n → Bool,
        |sSup ((fun f : X → Bool =>
            |(n : ℝ)⁻¹ * ∑ i : Fin n,
              rademacher_sign (σ i) *
                (2 * boolean_value (f (S i)) - 1)|) '' F.carrier) -
          sSup ((fun f : X → Bool =>
            |(n : ℝ)⁻¹ * ∑ i : Fin n,
              rademacher_sign (σ i) *
                (2 * boolean_value
                  (f ((Function.update S k z') i)) - 1)|) '' F.carrier)| ≤
            2 / (n : ℝ) := by
    intro σ
    have hbddS : BddAbove ((fun f : X → Bool =>
        |(n : ℝ)⁻¹ * ∑ i : Fin n,
          rademacher_sign (σ i) *
            (2 * boolean_value (f (S i)) - 1)|) '' F.carrier) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨f, hf, rfl⟩
      exact hscore_bound S σ f
    have hbddU : BddAbove ((fun f : X → Bool =>
        |(n : ℝ)⁻¹ * ∑ i : Fin n,
          rademacher_sign (σ i) *
            (2 * boolean_value
              (f ((Function.update S k z') i)) - 1)|) '' F.carrier) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨f, hf, rfl⟩
      exact hscore_bound (Function.update S k z') σ f
    rw [abs_le]
    constructor
    · have hle :
          sSup ((fun f : X → Bool =>
              |(n : ℝ)⁻¹ * ∑ i : Fin n,
                rademacher_sign (σ i) *
                  (2 * boolean_value
                    (f ((Function.update S k z') i)) - 1)|) '' F.carrier) ≤
            sSup ((fun f : X → Bool =>
              |(n : ℝ)⁻¹ * ∑ i : Fin n,
                rademacher_sign (σ i) *
                  (2 * boolean_value (f (S i)) - 1)|) '' F.carrier) +
              2 / (n : ℝ) := by
          apply csSup_le (hFne.image _)
          rintro _ ⟨f, hf, rfl⟩
          have hs := le_csSup hbddS ⟨f, hf, rfl⟩
          have hu := (abs_le.mp (hscore_update S σ f k z')).1
          linarith
      linarith
    · have hle :
          sSup ((fun f : X → Bool =>
              |(n : ℝ)⁻¹ * ∑ i : Fin n,
                rademacher_sign (σ i) *
                  (2 * boolean_value (f (S i)) - 1)|) '' F.carrier) ≤
            sSup ((fun f : X → Bool =>
              |(n : ℝ)⁻¹ * ∑ i : Fin n,
                rademacher_sign (σ i) *
                  (2 * boolean_value
                    (f ((Function.update S k z') i)) - 1)|) '' F.carrier) +
              2 / (n : ℝ) := by
          apply csSup_le (hFne.image _)
          rintro _ ⟨f, hf, rfl⟩
          have hu := le_csSup hbddU ⟨f, hf, rfl⟩
          have hs := (abs_le.mp (hscore_update S σ f k z')).2
          linarith
      linarith
  unfold empirical_rademacher_complexity
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (by positivity))]
  calc
    ((2 : ℝ) ^ n)⁻¹ *
        |∑ σ : Fin n → Bool,
          (sSup ((fun f : X → Bool =>
              |(n : ℝ)⁻¹ * ∑ i : Fin n,
                rademacher_sign (σ i) *
                  (2 * boolean_value (f (S i)) - 1)|) '' F.carrier) -
            sSup ((fun f : X → Bool =>
              |(n : ℝ)⁻¹ * ∑ i : Fin n,
                rademacher_sign (σ i) *
                  (2 * boolean_value
                    (f ((Function.update S k z') i)) - 1)|) '' F.carrier))| ≤
        ((2 : ℝ) ^ n)⁻¹ *
          ∑ σ : Fin n → Bool,
            |sSup ((fun f : X → Bool =>
                |(n : ℝ)⁻¹ * ∑ i : Fin n,
                  rademacher_sign (σ i) *
                    (2 * boolean_value (f (S i)) - 1)|) '' F.carrier) -
              sSup ((fun f : X → Bool =>
                |(n : ℝ)⁻¹ * ∑ i : Fin n,
                  rademacher_sign (σ i) *
                    (2 * boolean_value
                      (f ((Function.update S k z') i)) - 1)|) '' F.carrier)| := by
      exact mul_le_mul_of_nonneg_left
        (Finset.abs_sum_le_sum_abs _ Finset.univ)
        (inv_nonneg.mpr (by positivity))
    _ ≤ ((2 : ℝ) ^ n)⁻¹ *
          ∑ _σ : Fin n → Bool, (2 / (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum (fun σ hσ => hsup_update σ)
      · positivity
    _ = 2 / (n : ℝ) := by simp

@[blueprint "lem:finite-product-bounded-differences-subgaussian-local"
  (statement := /-- Let $P$ be a probability measure on a nonempty measurable space, let $a\geq0$, and let $G:\mathcal X^q\to[0,1]$ be measurable.  If changing one coordinate changes $G$ by at most $a$, then $G-\mathbb E G$ has a sub-Gaussian moment-generating function with variance proxy $qa^2$. -/)
  (proof := /-- Induct on $q$.  Split a nonempty sample into its first coordinate and its tail by the measure-preserving head--tail equivalence for finite product measures.  For each fixed head, the induction hypothesis controls the centered tail slice.  Its tail expectation, viewed as a function of the head, lies in an interval of length at most $2a$, so Hoeffding's lemma gives variance proxy $a^2$.  Fubini's theorem factors the exponential moment into these two centered contributions, whose variance proxies add.  The case $q=0$ is constant. -/)
  (title := /-- Bounded differences are sub-Gaussian on finite products -/)
  (latexEnv := "lemma")]
lemma finite_product_bounded_differences_subgaussian_local
    {X : Type*} [MeasurableSpace X] [Nonempty X]
    (P : ProbabilityMeasure X) (a : NNReal) :
    ∀ (q : ℕ) (G : (Fin q → X) → ℝ),
      Measurable G →
      (∀ S, 0 ≤ G S ∧ G S ≤ 1) →
      (∀ S k z', |G S - G (Function.update S k z')| ≤ (a : ℝ)) →
      ProbabilityTheory.HasSubgaussianMGF
        (fun S => G S - ∫ T, G T
          ∂(ProbabilityMeasure.pi (fun _ : Fin q => P)).toMeasure)
        ((q : NNReal) * a ^ 2)
        (ProbabilityMeasure.pi (fun _ : Fin q => P)).toMeasure := by
  classical
  intro q
  induction q with
  | zero =>
      intro G hG hGb hGu
      let S0 : Fin 0 → X := fun i => Fin.elim0 i
      have hconst : G = fun _ => G S0 := by
        funext S
        congr 1
        exact Subsingleton.elim S S0
      rw [hconst]
      simpa using
        (ProbabilityTheory.HasSubgaussianMGF.zero
          (μ := (ProbabilityMeasure.pi (fun _ : Fin 0 => P)).toMeasure))
  | succ q ih =>
      intro G hG hGb hGu
      let μq := (ProbabilityMeasure.pi (fun _ : Fin q => P)).toMeasure
      let μs := (ProbabilityMeasure.pi (fun _ : Fin (q + 1) => P)).toMeasure
      let H : X × (Fin q → X) → ℝ := fun p => G (Fin.cons p.1 p.2)
      let g : X → ℝ := fun x => ∫ T, H (x, T) ∂μq
      have hH : Measurable H := by
        apply hG.comp
        refine measurable_pi_iff.mpr (Fin.cases ?_ ?_)
        · exact measurable_fst
        · intro i
          exact (measurable_pi_apply i).comp measurable_snd
      have hHb : ∀ p, 0 ≤ H p ∧ H p ≤ 1 := fun p => hGb _
      have hHI : Integrable H (P.toMeasure.prod μq) := by
        refine ⟨hH.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := 1) ?_⟩
        exact Filter.Eventually.of_forall (fun p => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hHb p).1]
          exact (hHb p).2)
      have hgM : Measurable g := by
        exact hH.stronglyMeasurable.integral_prod_right'.measurable
      have hgb : ∀ x, 0 ≤ g x ∧ g x ≤ 1 := by
        intro x
        have hxM : Measurable (fun T => H (x, T)) :=
          hH.comp (measurable_const.prodMk measurable_id)
        have hxI : Integrable (fun T => H (x, T)) μq := by
          refine ⟨hxM.aestronglyMeasurable,
            HasFiniteIntegral.of_bounded (C := 1) ?_⟩
          exact Filter.Eventually.of_forall (fun T => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hHb (x, T)).1]
            exact (hHb (x, T)).2)
        constructor
        · exact integral_nonneg (fun T => (hHb (x, T)).1)
        · change (∫ T, H (x, T) ∂μq) ≤ 1
          calc
            (∫ T, H (x, T) ∂μq) ≤ ∫ _T, (1 : ℝ) ∂μq :=
              integral_mono hxI (integrable_const 1)
                (fun T => (hHb (x, T)).2)
            _ = 1 := by simp [μq]
      have htail : ∀ x,
          ProbabilityTheory.HasSubgaussianMGF
            (fun T => H (x, T) - ∫ U, H (x, U) ∂μq)
            ((q : NNReal) * a ^ 2) μq := by
        intro x
        apply ih (fun T => H (x, T))
        · exact hH.comp (measurable_const.prodMk measurable_id)
        · exact fun T => hHb (x, T)
        · intro T k z'
          simpa [H] using hGu (Fin.cons x T) k.succ z'
      let x0 : X := Classical.arbitrary X
      have hgdiff : ∀ x, |g x - g x0| ≤ (a : ℝ) := by
        intro x
        have hxM : Measurable (fun T => H (x, T)) :=
          hH.comp (measurable_const.prodMk measurable_id)
        have hx0M : Measurable (fun T => H (x0, T)) :=
          hH.comp (measurable_const.prodMk measurable_id)
        have hxI : Integrable (fun T => H (x, T)) μq := by
          refine ⟨hxM.aestronglyMeasurable,
            HasFiniteIntegral.of_bounded (C := 1) ?_⟩
          exact Filter.Eventually.of_forall (fun T => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hHb (x, T)).1]
            exact (hHb (x, T)).2)
        have hx0I : Integrable (fun T => H (x0, T)) μq := by
          refine ⟨hx0M.aestronglyMeasurable,
            HasFiniteIntegral.of_bounded (C := 1) ?_⟩
          exact Filter.Eventually.of_forall (fun T => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hHb (x0, T)).1]
            exact (hHb (x0, T)).2)
        rw [← integral_sub]
        · calc
            |∫ T, H (x, T) - H (x0, T) ∂μq| ≤
                ∫ T, |H (x, T) - H (x0, T)| ∂μq :=
              by simpa [Real.norm_eq_abs] using
                (norm_integral_le_integral_norm
                  (μ := μq) (f := fun T => H (x, T) - H (x0, T)))
            _ ≤ ∫ _T, (a : ℝ) ∂μq := integral_mono
                (by simpa [Real.norm_eq_abs] using (hxI.sub hx0I).norm)
                (integrable_const _) (fun T => by
                  simpa [H, Real.norm_eq_abs] using hGu (Fin.cons x T) 0 x0)
            _ = (a : ℝ) := by simp [μq]
        · exact hxI
        · exact hx0I
      have hgsub : ProbabilityTheory.HasSubgaussianMGF
          (fun x => g x - ∫ y, g y ∂P.toMeasure) (a ^ 2) P.toMeasure := by
        have h := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
          (μ := P.toMeasure)
          (a := g x0 - (a : ℝ)) (b := g x0 + (a : ℝ)) hgM.aemeasurable
          (Filter.Eventually.of_forall (fun x => by
            rw [Set.mem_Icc]
            have h := abs_le.mp (hgdiff x)
            constructor <;> linarith))
        convert h using 1
        ext
        rw [show g x0 + (a : ℝ) - (g x0 - (a : ℝ)) = (a : ℝ) + a by ring]
        simp [Real.nnnorm_of_nonneg (add_nonneg a.coe_nonneg a.coe_nonneg)]
      have hmean : ∫ p, H p ∂(P.toMeasure.prod μq) = ∫ x, g x ∂P.toMeasure := by
        simpa [g] using (MeasureTheory.integral_prod H hHI)
      have hgI : Integrable g P.toMeasure := by
        refine ⟨hgM.aestronglyMeasurable,
          HasFiniteIntegral.of_bounded (C := 1) ?_⟩
        exact Filter.Eventually.of_forall (fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hgb x).1]
          exact (hgb x).2)
      have hmean_bounds :
          0 ≤ ∫ r, H r ∂(P.toMeasure.prod μq) ∧
            ∫ r, H r ∂(P.toMeasure.prod μq) ≤ 1 := by
        rw [hmean]
        constructor
        · exact integral_nonneg (fun x => (hgb x).1)
        · calc
            (∫ x, g x ∂P.toMeasure) ≤ ∫ _x, (1 : ℝ) ∂P.toMeasure :=
              integral_mono hgI (integrable_const 1) (fun x => (hgb x).2)
            _ = 1 := by simp
      have hprod : ProbabilityTheory.HasSubgaussianMGF
          (fun p => H p - ∫ r, H r ∂(P.toMeasure.prod μq))
          (((q + 1 : ℕ) : NNReal) * a ^ 2) (P.toMeasure.prod μq) := by
        have hexpI : ∀ t : ℝ, Integrable
            (fun p => Real.exp
              (t * (H p - ∫ r, H r ∂(P.toMeasure.prod μq))))
            (P.toMeasure.prod μq) := by
          intro t
          refine ⟨(((hH.sub measurable_const).const_mul t).exp).aestronglyMeasurable,
            HasFiniteIntegral.of_bounded (C := Real.exp |t|) ?_⟩
          exact Filter.Eventually.of_forall (fun p => by
            rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
            apply Real.exp_le_exp.mpr
            have hd : |H p - ∫ r, H r ∂(P.toMeasure.prod μq)| ≤ 1 := by
              rw [abs_le]
              constructor <;> linarith [(hHb p).1, (hHb p).2,
                hmean_bounds.1, hmean_bounds.2]
            calc
              t * (H p - ∫ r, H r ∂(P.toMeasure.prod μq)) ≤
                  |t * (H p - ∫ r, H r ∂(P.toMeasure.prod μq))| :=
                le_abs_self _
              _ = |t| * |H p - ∫ r, H r ∂(P.toMeasure.prod μq)| := abs_mul _ _
              _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left hd (abs_nonneg t)
              _ = |t| := mul_one _)
        refine ⟨hexpI, ?_⟩
        intro t
        have houterI : Integrable
            (fun x => ∫ T, Real.exp
              (t * (H (x, T) - ∫ r, H r ∂(P.toMeasure.prod μq))) ∂μq)
            P.toMeasure := (hexpI t).integral_prod_left
        have hfactor :
            (fun x => ∫ T, Real.exp
              (t * (H (x, T) - ∫ r, H r ∂(P.toMeasure.prod μq))) ∂μq) =
            (fun x => Real.exp (t * (g x - ∫ y, g y ∂P.toMeasure)) *
              (∫ T, Real.exp (t * (H (x, T) - g x)) ∂μq)) := by
          funext x
          rw [hmean, ← MeasureTheory.integral_const_mul]
          congr 1
          funext T
          rw [← Real.exp_add]
          congr 1
          ring
        have hleftI : Integrable
            (fun x => Real.exp (t * (g x - ∫ y, g y ∂P.toMeasure)) *
              (∫ T, Real.exp (t * (H (x, T) - g x)) ∂μq)) P.toMeasure := by
          rw [← hfactor]
          exact houterI
        have hrightI : Integrable
            (fun x => Real.exp (t * (g x - ∫ y, g y ∂P.toMeasure)) *
              Real.exp (((q : NNReal) * a ^ 2 : ℝ) * t ^ 2 / 2)) P.toMeasure :=
          (hgsub.integrable_exp_mul t).mul_const _
        simp only [ProbabilityTheory.mgf]
        rw [MeasureTheory.integral_prod _ (hexpI t)]
        simp_rw [hmean]
        calc
            (∫ x, ∫ T, Real.exp (t * (H (x, T) - ∫ y, g y ∂P.toMeasure)) ∂μq ∂P.toMeasure) =
                ∫ x, Real.exp (t * (g x - ∫ y, g y ∂P.toMeasure)) *
                  (∫ T, Real.exp (t * (H (x, T) - g x)) ∂μq) ∂P.toMeasure := by
              congr 1
              funext x
              rw [← MeasureTheory.integral_const_mul]
              congr 1
              funext T
              rw [← Real.exp_add]
              congr 1
              ring
            _ ≤ ∫ x, Real.exp (t * (g x - ∫ y, g y ∂P.toMeasure)) *
                Real.exp (((q : NNReal) * a ^ 2 : ℝ) * t ^ 2 / 2) ∂P.toMeasure := by
              apply integral_mono hleftI hrightI
              intro x
              exact mul_le_mul_of_nonneg_left
                (by simpa [ProbabilityTheory.mgf] using (htail x).mgf_le t)
                (Real.exp_nonneg _)
            _ = (∫ x, Real.exp (t * (g x - ∫ y, g y ∂P.toMeasure)) ∂P.toMeasure) *
                Real.exp (((q : NNReal) * a ^ 2 : ℝ) * t ^ 2 / 2) := by
              rw [MeasureTheory.integral_mul_const]
            _ ≤ Real.exp ((a ^ 2 : ℝ) * t ^ 2 / 2) *
                Real.exp (((q : NNReal) * a ^ 2 : ℝ) * t ^ 2 / 2) := by
              gcongr
              exact hgsub.mgf_le t
            _ = Real.exp (((((q + 1 : ℕ) : NNReal) * a ^ 2 : ℝ) * t ^ 2 / 2)) := by
              rw [← Real.exp_add]
              congr 1
              push_cast
              ring
      have hp := MeasureTheory.measurePreserving_piFinSuccAbove
        (fun _ : Fin (q + 1) => P.toMeasure) 0
      have hGint :
          (∫ p, H p ∂(P.toMeasure.prod μq)) = ∫ S, G S ∂μs := by
        simp only [μq, μs, ProbabilityMeasure.toMeasure_pi]
        rw [← hp.map_eq, MeasureTheory.integral_map hp.aemeasurable]
        · simp [H]
        · rw [hp.map_eq]
          exact hH.aestronglyMeasurable
      rw [hGint] at hprod
      have hmap : μs.map (MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (q + 1) => X) 0) = P.toMeasure.prod μq := by
        simpa [μs, μq] using hp.map_eq
      rw [← hmap] at hprod
      simpa [H, μs, μq, Function.comp_def] using
        hprod.of_map hp.aemeasurable

@[blueprint "lem:empirical-rademacher-concentration"
  (statement := /-- There is a universal constant $C>0$ such that, for every measurable space $\mathcal X$, every countable family $\mathcal F$ of measurable maps $\mathcal X\to\{0,1\}$ that is closed under pointwise complementation, every probability measure $P$ on $\mathcal X$, every $n\geq1$, and every $\delta\in(0,1)$, the map $S\mapsto\widehat{\mathcal R}(\mathcal F,S)$ is integrable under $P^n$, the displayed deviation set is measurable, and
  \[
  \Pr_{S\sim P^n}\left[
    \left|\widehat{\mathcal R}(\mathcal F,S)
      -\mathcal R_n(\mathcal F,P)\right|
    \leq C\sqrt{\frac{1+\log(1/\delta)}{n}}
  \right]\geq1-\delta.
  \] -/)
  (proof := /-- Put
  $G(S)=\widehat{\mathcal R}(\mathcal F,S)$.  By
  \cref{lem:empirical-rademacher-measurable-bounded-local}, $G$ is measurable
  and takes values in $[0,1]$, hence it is integrable under $P^n$.  Its
  integral is $\mathcal R_n(\mathcal F,P)$ by
  \cref{def:distributional-rademacher-complexity}.  Moreover,
  \cref{lem:empirical-rademacher-bounded-differences-local} shows that
  replacing one coordinate changes $G$ by at most $2/n$.

  Apply
  \cref{lem:finite-product-bounded-differences-subgaussian-local} with
  $a=2/n$.  The centered variable
  $G-\mathcal R_n(\mathcal F,P)$ is sub-Gaussian with variance proxy
  $n(2/n)^2=4/n$.  Consequently, for every $t\geq0$, each of its two tails is
  at most $\exp(-nt^2/8)$, and their union is at most
  $2\exp(-nt^2/8)$.

  Take $C=4$, set $A=1+\log(1/\delta)$, and set
  $t=4\sqrt{A/n}$.  Since $0<\delta<1$, one has $A>0$ and
  \[
    -\frac{nt^2}{8}=-2A\leq\log(\delta/2).
  \]
  Indeed, the last inequality is equivalent to
  $\log\delta+\log2\leq2$, which follows from
  $\log\delta<0$ and $\log2\leq1$.  Thus each tail has probability at most
  $\delta/2$, so the complement of the displayed deviation event has
  probability at most $\delta$.  The event is measurable because $G$ is
  measurable; complementing its probability gives the claimed lower bound in
  the notation of \cref{def:sample-event-probability}. -/)
  (title := /-- Concentration of empirical Rademacher complexity -/)
  (latexEnv := "lemma")]
lemma empirical_rademacher_concentration :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type*} [MeasurableSpace X]
        (F : boolean_distinguishing_family X) (P : ProbabilityMeasure X)
        (n : ℕ) (δ : ℝ), 0 < n → 0 < δ → δ < 1 →
        Integrable (fun S : Fin n → X => empirical_rademacher_complexity F S)
          (ProbabilityMeasure.pi (fun _ : Fin n => P)).toMeasure ∧
        MeasurableSet
          {S : Fin n → X | |empirical_rademacher_complexity F S -
            distributional_rademacher_complexity F n P| ≤
            C * Real.sqrt ((1 + Real.log (1 / δ)) / n)} ∧
        sample_event_probability P n
          {S : Fin n → X | |empirical_rademacher_complexity F S -
            distributional_rademacher_complexity F n P| ≤
            C * Real.sqrt ((1 + Real.log (1 / δ)) / n)} ≥ 1 - δ := by
  refine ⟨4, by norm_num, ?_⟩
  intro X inst F P n δ hn hδ hδ1
  letI : Nonempty X := P.nonempty
  let μ := (ProbabilityMeasure.pi (fun _ : Fin n => P)).toMeasure
  let G : (Fin n → X) → ℝ := fun S => empirical_rademacher_complexity F S
  have hMB := empirical_rademacher_measurable_bounded_local F hn
  have hM : Measurable G := by simpa [G] using hMB.1
  have hB : ∀ S, 0 ≤ G S ∧ G S ≤ 1 := by simpa [G] using hMB.2
  have hI : Integrable G μ := by
    refine ⟨hM.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := 1) ?_⟩
    exact Filter.Eventually.of_forall (fun S => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hB S).1]
      exact (hB S).2)
  let a : NNReal := ⟨2 / (n : ℝ), by positivity⟩
  have ha : (a : ℝ) = 2 / (n : ℝ) := rfl
  have hsg : ProbabilityTheory.HasSubgaussianMGF
      (fun S => G S - ∫ T, G T ∂μ) ((n : NNReal) * a ^ 2) μ := by
    apply finite_product_bounded_differences_subgaussian_local P a n G hM hB
    intro S k z'
    simpa [G, ha] using
      empirical_rademacher_bounded_differences_local F hn S k z'
  have hcenter :
      (∫ T, G T ∂μ) = distributional_rademacher_complexity F n P := by
    rfl
  rw [hcenter] at hsg
  let A : ℝ := 1 + Real.log (1 / δ)
  let t : ℝ := 4 * Real.sqrt (A / n)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hratio : 1 < 1 / δ := by
    exact (lt_div_iff₀ hδ).2 (by linarith)
  have hA : 0 < A := by
    dsimp [A]
    have h := Real.log_pos hratio
    linarith
  have harg : 0 ≤ A / (n : ℝ) := le_of_lt (div_pos hA hnR)
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have htsq : t ^ 2 = 16 * A / (n : ℝ) := by
    dsimp [t]
    rw [mul_pow, Real.sq_sqrt harg]
    ring
  have hc : (((n : NNReal) * a ^ 2 : NNReal) : ℝ) = 4 / (n : ℝ) := by
    push_cast
    rw [ha]
    field_simp
    ring
  have hlogδ : Real.log δ < 0 := Real.log_neg hδ hδ1
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hexponent :
      -t ^ 2 / (2 * (((n : NNReal) * a ^ 2 : NNReal) : ℝ)) ≤
        Real.log (δ / 2) := by
    rw [hc, htsq]
    dsimp [A]
    rw [Real.log_div hδ.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    rw [show Real.log (1 / δ) = -Real.log δ by
      rw [one_div, Real.log_inv]]
    field_simp
    nlinarith
  have htail :
      Real.exp (-t ^ 2 /
        (2 * (((n : NNReal) * a ^ 2 : NNReal) : ℝ))) ≤ δ / 2 := by
    calc
      _ ≤ Real.exp (Real.log (δ / 2)) := Real.exp_le_exp.mpr hexponent
      _ = δ / 2 := Real.exp_log (by positivity)
  have hgood_meas : MeasurableSet
      {S : Fin n → X | |G S - distributional_rademacher_complexity F n P| ≤
        4 * Real.sqrt ((1 + Real.log (1 / δ)) / n)} := by
    exact measurableSet_le
      (Measurable.abs (hM.sub measurable_const)) measurable_const
  refine ⟨?_, ?_, ?_⟩
  · simpa [G, μ] using hI
  · change MeasurableSet {S : Fin n → X |
      |G S - distributional_rademacher_complexity F n P| ≤
        4 * Real.sqrt ((1 + Real.log (1 / δ)) / n)}
    assumption
  · have hpos :
        μ.real {S : Fin n → X |
          t ≤ G S - distributional_rademacher_complexity F n P} ≤ δ / 2 := by
      calc
        _ ≤ Real.exp (-t ^ 2 /
            (2 * (((n : NNReal) * a ^ 2 : NNReal) : ℝ))) :=
          hsg.measure_ge_le ht
        _ ≤ δ / 2 := htail
    have hneg :
        μ.real {S : Fin n → X |
          t ≤ -(G S - distributional_rademacher_complexity F n P)} ≤ δ / 2 := by
      calc
        _ ≤ Real.exp (-t ^ 2 /
            (2 * (((n : NNReal) * a ^ 2 : NNReal) : ℝ))) :=
          hsg.neg.measure_ge_le ht
        _ ≤ δ / 2 := htail
    let good : Set (Fin n → X) :=
      {S | |G S - distributional_rademacher_complexity F n P| ≤ t}
    have hgood_t : MeasurableSet good := by
      dsimp [good]
      exact measurableSet_le
        (Measurable.abs (hM.sub measurable_const)) measurable_const
    have hbad_subset :
        goodᶜ ⊆
          {S : Fin n → X |
            t ≤ G S - distributional_rademacher_complexity F n P} ∪
          {S : Fin n → X |
            t ≤ -(G S - distributional_rademacher_complexity F n P)} := by
      intro S hS
      simp only [good, Set.mem_compl_iff, Set.mem_setOf_eq, not_le,
        Set.mem_union] at hS ⊢
      by_cases hz : 0 ≤ G S - distributional_rademacher_complexity F n P
      · left
        rw [abs_of_nonneg hz] at hS
        exact le_of_lt hS
      · right
        rw [abs_of_neg (lt_of_not_ge hz)] at hS
        exact le_of_lt hS
    have hbad : μ.real goodᶜ ≤ δ := by
      calc
        μ.real goodᶜ ≤ μ.real
            ({S : Fin n → X |
              t ≤ G S - distributional_rademacher_complexity F n P} ∪
            {S : Fin n → X |
              t ≤ -(G S - distributional_rademacher_complexity F n P)}) :=
          measureReal_mono hbad_subset
        _ ≤ μ.real {S : Fin n → X |
              t ≤ G S - distributional_rademacher_complexity F n P} +
            μ.real {S : Fin n → X |
              t ≤ -(G S - distributional_rademacher_complexity F n P)} :=
          measureReal_union_le _ _
        _ ≤ δ / 2 + δ / 2 := add_le_add hpos hneg
        _ = δ := by ring
    have hcomp := MeasureTheory.probReal_compl_eq_one_sub
      (μ := μ) hgood_t
    change μ.real good ≥ 1 - δ
    linarith

@[blueprint "lem:empirical-probability-measure-integral-local-rademacher-generalization"
  (statement := /-- Let $P$ be a probability measure on a measurable space, let $n\geq1$, and let $S\in\mathcal X^n$.  The integral of a measurable real-valued function against the empirical measure $\widehat P_S$ is its sample average. -/)
  (proof := /-- Unfold \cref{def:empirical-probability-measure}.  Since $n$ is positive, the empirical measure is the pushforward of the uniform probability mass function on $\operatorname{Fin}(n)$ by $S$.  The change-of-variables formula followed by the finite-sum formula for integration against a probability mass function gives the asserted normalized sum. -/)
  (title := /-- Integration against an empirical measure -/)
  (latexEnv := "lemma")]
lemma empirical_probability_measure_integral_local_rademacher_generalization
    {X : Type*} [MeasurableSpace X] (P : ProbabilityMeasure X)
    {n : ℕ} (hn : 0 < n) (S : Fin n → X) (g : X → ℝ)
    (hg : Measurable g) :
    (∫ x, g x ∂(empirical_probability_measure P S).toMeasure) =
      (n : ℝ)⁻¹ * ∑ i : Fin n, g (S i) := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold empirical_probability_measure
  rw [dif_neg hn.ne']
  dsimp
  rw [← PMF.toMeasure_map S (PMF.uniformOfFintype (Fin n))
    (measurable_of_finite S)]
  rw [MeasureTheory.integral_map (measurable_of_finite S).aemeasurable
    hg.aestronglyMeasurable]
  rw [MeasureTheory.integral_fintype .of_finite]
  calc
    ∑ i : Fin n, (PMF.uniformOfFintype (Fin n)).toMeasure.real {i} • g (S i) =
        ∑ i : Fin n, (n : ℝ)⁻¹ * g (S i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [smul_eq_mul]
      congr 1
      rw [measureReal_def,
        PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton i)]
      simp [PMF.uniformOfFintype_apply]
    _ = (n : ℝ)⁻¹ * ∑ i : Fin n, g (S i) := by
      rw [Finset.mul_sum]

@[blueprint "lem:empirical-fooling-distance-measurable-bounded-local-rademacher-generalization"
  (statement := /-- Let $\mathcal F$ be a countable complemented family of measurable Boolean functions, let $P$ be a probability measure, and let $n\geq1$.  The map $S\mapsto d_{\mathcal F}(P,\widehat P_S)$ is measurable, takes values in $[0,1]$, and changes by at most $1/n$ when one sample coordinate is replaced. -/)
  (proof := /-- By \cref{lem:empirical-probability-measure-integral-local-rademacher-generalization}, each empirical expectation is a finite sample average and is therefore measurable as a function of the sample.  Countability of $\mathcal F$ makes the supremum measurable.  Every Boolean expectation lies in $[0,1]$, so every absolute difference, and hence its supremum, lies in $[0,1]$.  Replacing one coordinate changes each sample average by at most $1/n$; the reverse triangle inequality and the elementary comparison of two bounded suprema preserve this bound. -/)
  (title := /-- Measurability and bounded differences of empirical fooling distance -/)
  (latexEnv := "lemma")]
lemma empirical_fooling_distance_measurable_bounded_local_rademacher_generalization
    {X : Type*} [MeasurableSpace X]
    (F : boolean_distinguishing_family X) (P : ProbabilityMeasure X)
    {n : ℕ} (hn : 0 < n) :
    let D : (Fin n → X) → ℝ :=
      fun S => fooling_distance F P (empirical_probability_measure P S)
    Measurable D ∧
      (∀ S, 0 ≤ D S ∧ D S ≤ 1) ∧
      ∀ (S : Fin n → X) (k : Fin n) (z' : X),
        |D S - D (Function.update S k z')| ≤ 1 / (n : ℝ) := by
  classical
  dsimp
  have hvalue_meas :
      ∀ f : X → Bool, f ∈ F.carrier →
        Measurable (fun x => boolean_value (f x)) := by
    intro f hf
    exact (measurable_of_finite boolean_value).comp (F.measurable f hf)
  have hmean_bounds :
      ∀ (Q : ProbabilityMeasure X) (f : X → Bool), f ∈ F.carrier →
        0 ≤ (∫ x, boolean_value (f x) ∂Q.toMeasure) ∧
          (∫ x, boolean_value (f x) ∂Q.toMeasure) ≤ 1 := by
    intro Q f hf
    have hM := hvalue_meas f hf
    have hI : Integrable (fun x => boolean_value (f x)) Q.toMeasure := by
      refine ⟨hM.aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := 1) ?_⟩
      exact Filter.Eventually.of_forall (fun x => by
        cases hfx : f x <;> simp [boolean_value, hfx])
    constructor
    · exact integral_nonneg (fun x => by
        cases hfx : f x <;> simp [boolean_value, hfx])
    · calc
        (∫ x, boolean_value (f x) ∂Q.toMeasure) ≤
            ∫ _x, (1 : ℝ) ∂Q.toMeasure :=
          integral_mono hI (integrable_const 1) (fun x => by
            cases hfx : f x <;> simp [boolean_value, hfx])
        _ = 1 := by simp
  have hscore_meas :
      ∀ f : X → Bool, f ∈ F.carrier →
        Measurable (fun S : Fin n → X =>
          |(∫ x, boolean_value (f x) ∂P.toMeasure) -
            (∫ x, boolean_value (f x)
              ∂(empirical_probability_measure P S).toMeasure)|) := by
    intro f hf
    have hM := hvalue_meas f hf
    have heq :
        (fun S : Fin n → X =>
          |(∫ x, boolean_value (f x) ∂P.toMeasure) -
            (∫ x, boolean_value (f x)
              ∂(empirical_probability_measure P S).toMeasure)|) =
        fun S => |(∫ x, boolean_value (f x) ∂P.toMeasure) -
          (n : ℝ)⁻¹ * ∑ i : Fin n, boolean_value (f (S i))| := by
      funext S
      rw [empirical_probability_measure_integral_local_rademacher_generalization
        P hn S _ hM]
    rw [heq]
    apply Measurable.abs
    apply measurable_const.sub
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    exact hM.comp (measurable_pi_apply i)
  have hscore_bound :
      ∀ (S : Fin n → X) (f : X → Bool), f ∈ F.carrier →
        |(∫ x, boolean_value (f x) ∂P.toMeasure) -
          (∫ x, boolean_value (f x)
            ∂(empirical_probability_measure P S).toMeasure)| ≤ 1 := by
    intro S f hf
    have hP := hmean_bounds P f hf
    have hS := hmean_bounds (empirical_probability_measure P S) f hf
    rw [abs_le]
    constructor <;> linarith
  have hM : Measurable (fun S : Fin n → X =>
      fooling_distance F P (empirical_probability_measure P S)) := by
    unfold fooling_distance
    exact Measurable.sSup F.carrier_countable hscore_meas
  have hB : ∀ S : Fin n → X,
      0 ≤ fooling_distance F P (empirical_probability_measure P S) ∧
        fooling_distance F P (empirical_probability_measure P S) ≤ 1 := by
    intro S
    unfold fooling_distance
    constructor
    · exact Real.sSup_nonneg (fun y hy => by
        rcases hy with ⟨f, hf, rfl⟩
        exact abs_nonneg _)
    · by_cases hF : F.carrier = ∅
      · simp [hF]
      · apply csSup_le (Set.nonempty_iff_ne_empty.mpr hF |>.image _)
        rintro _ ⟨f, hf, rfl⟩
        exact hscore_bound S f hf
  have hscore_update :
      ∀ (S : Fin n → X) (f : X → Bool), f ∈ F.carrier →
        ∀ (k : Fin n) (z' : X),
        abs
          (|(∫ x, boolean_value (f x) ∂P.toMeasure) -
              (∫ x, boolean_value (f x)
                ∂(empirical_probability_measure P S).toMeasure)| -
            |(∫ x, boolean_value (f x) ∂P.toMeasure) -
              (∫ x, boolean_value (f x)
                ∂(empirical_probability_measure P
                  (Function.update S k z')).toMeasure)|) ≤
          1 / (n : ℝ) := by
    intro S f hf k z'
    have hMf := hvalue_meas f hf
    rw [empirical_probability_measure_integral_local_rademacher_generalization
      P hn S _ hMf]
    rw [empirical_probability_measure_integral_local_rademacher_generalization
      P hn (Function.update S k z') _ hMf]
    have hsum :
        (∑ i : Fin n, boolean_value (f (S i))) -
          (∑ i : Fin n,
            boolean_value (f ((Function.update S k z') i))) =
          boolean_value (f (S k)) - boolean_value (f z') := by
      rw [← Finset.sum_sub_distrib]
      calc
        (∑ i : Fin n,
            (boolean_value (f (S i)) -
              boolean_value (f ((Function.update S k z') i)))) =
            boolean_value (f (S k)) -
              boolean_value (f ((Function.update S k z') k)) := by
          apply Finset.sum_eq_single k
          · intro i hi hik
            rw [Function.update_of_ne hik]
            ring
          · simp
        _ = _ := by rw [Function.update_self]
    have hk :
        |boolean_value (f (S k)) - boolean_value (f z')| ≤ 1 := by
      cases h1 : f (S k) <;> cases h2 : f z' <;>
        norm_num [boolean_value, h1, h2]
    calc
      _ ≤ |((∫ x, boolean_value (f x) ∂P.toMeasure) -
              (n : ℝ)⁻¹ * ∑ i : Fin n, boolean_value (f (S i))) -
            ((∫ x, boolean_value (f x) ∂P.toMeasure) -
              (n : ℝ)⁻¹ * ∑ i : Fin n,
                boolean_value (f ((Function.update S k z') i)))| :=
        abs_abs_sub_abs_le_abs_sub _ _
      _ = (n : ℝ)⁻¹ *
          |boolean_value (f (S k)) - boolean_value (f z')| := by
        rw [show
          ((∫ x, boolean_value (f x) ∂P.toMeasure) -
              (n : ℝ)⁻¹ * ∑ i : Fin n, boolean_value (f (S i))) -
            ((∫ x, boolean_value (f x) ∂P.toMeasure) -
              (n : ℝ)⁻¹ * ∑ i : Fin n,
                boolean_value (f ((Function.update S k z') i))) =
            -(n : ℝ)⁻¹ *
              ((∑ i : Fin n, boolean_value (f (S i))) -
                ∑ i : Fin n,
                  boolean_value (f ((Function.update S k z') i))) by ring]
        rw [hsum, abs_mul, abs_neg,
          abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
      _ ≤ (n : ℝ)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hk
          (inv_nonneg.mpr (Nat.cast_nonneg n))
      _ = 1 / (n : ℝ) := by ring
  refine ⟨hM, hB, ?_⟩
  intro S k z'
  by_cases hF : F.carrier = ∅
  · simp [fooling_distance, hF]
  have hFne : F.carrier.Nonempty := Set.nonempty_iff_ne_empty.mpr hF
  have hbddS : BddAbove ((fun f : X → Bool =>
      |(∫ x, boolean_value (f x) ∂P.toMeasure) -
        (∫ x, boolean_value (f x)
          ∂(empirical_probability_measure P S).toMeasure)|) '' F.carrier) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨f, hf, rfl⟩
    exact hscore_bound S f hf
  have hbddU : BddAbove ((fun f : X → Bool =>
      |(∫ x, boolean_value (f x) ∂P.toMeasure) -
        (∫ x, boolean_value (f x)
          ∂(empirical_probability_measure P
            (Function.update S k z')).toMeasure)|) '' F.carrier) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨f, hf, rfl⟩
    exact hscore_bound (Function.update S k z') f hf
  unfold fooling_distance
  rw [abs_le]
  constructor
  · have hle :
        sSup ((fun f : X → Bool =>
          |(∫ x, boolean_value (f x) ∂P.toMeasure) -
            (∫ x, boolean_value (f x)
              ∂(empirical_probability_measure P
                (Function.update S k z')).toMeasure)|) '' F.carrier) ≤
          sSup ((fun f : X → Bool =>
            |(∫ x, boolean_value (f x) ∂P.toMeasure) -
              (∫ x, boolean_value (f x)
                ∂(empirical_probability_measure P S).toMeasure)|) '' F.carrier) +
            1 / (n : ℝ) := by
        apply csSup_le (hFne.image _)
        rintro _ ⟨f, hf, rfl⟩
        have hs := le_csSup hbddS ⟨f, hf, rfl⟩
        have hu := (abs_le.mp (hscore_update S f hf k z')).1
        linarith
    linarith
  · have hle :
        sSup ((fun f : X → Bool =>
          |(∫ x, boolean_value (f x) ∂P.toMeasure) -
            (∫ x, boolean_value (f x)
              ∂(empirical_probability_measure P S).toMeasure)|) '' F.carrier) ≤
          sSup ((fun f : X → Bool =>
            |(∫ x, boolean_value (f x) ∂P.toMeasure) -
              (∫ x, boolean_value (f x)
                ∂(empirical_probability_measure P
                  (Function.update S k z')).toMeasure)|) '' F.carrier) +
            1 / (n : ℝ) := by
        apply csSup_le (hFne.image _)
        rintro _ ⟨f, hf, rfl⟩
        have hu := le_csSup hbddU ⟨f, hf, rfl⟩
        have hs := (abs_le.mp (hscore_update S f hf k z')).2
        linarith
    linarith

@[blueprint "lem:empirical-fooling-distance-ghost-bound-local-rademacher-generalization"
  (statement := /-- Let $P$ be a probability measure, let $n\geq1$, and let $S,S'$ be independent samples from $P^n$.  The expectation of $d_{\mathcal F}(P,\widehat P_S)$ is at most the expectation of $d_{\mathcal F}(\widehat P_S,\widehat P_{S'})$. -/)
  (proof := /-- For every $f\in\mathcal F$, \cref{lem:empirical-probability-measure-integral-local-rademacher-generalization} identifies the expectation of its ghost-sample average with its expectation under $P$.  The norm-of-integral inequality therefore bounds the deviation of $f$ on a fixed sample by the ghost-sample expectation of the corresponding two-sample deviation.  Taking the supremum over the countable class and integrating the resulting pointwise inequality proves the claim.  Measurability and boundedness use the same countable-supremum argument as \cref{lem:empirical-fooling-distance-measurable-bounded-local-rademacher-generalization}. -/)
  (title := /-- Ghost-sample bound for empirical fooling distance -/)
  (latexEnv := "lemma")]
lemma empirical_fooling_distance_ghost_bound_local_rademacher_generalization
    {X : Type*} [MeasurableSpace X]
    (F : boolean_distinguishing_family X) (P : ProbabilityMeasure X)
    {n : ℕ} (hn : 0 < n) :
    let μ := (ProbabilityMeasure.pi (fun _ : Fin n => P)).toMeasure
    (∫ S, fooling_distance F P (empirical_probability_measure P S) ∂μ) ≤
      ∫ p : (Fin n → X) × (Fin n → X),
        fooling_distance F (empirical_probability_measure P p.1)
          (empirical_probability_measure P p.2) ∂(μ.prod μ) := by
  classical
  dsimp
  let μ := (ProbabilityMeasure.pi (fun _ : Fin n => P)).toMeasure
  let D : (Fin n → X) → ℝ :=
    fun S => fooling_distance F P (empirical_probability_measure P S)
  let gap : ((Fin n → X) × (Fin n → X)) → ℝ :=
    fun p => fooling_distance F (empirical_probability_measure P p.1)
      (empirical_probability_measure P p.2)
  by_cases hF : F.carrier = ∅
  · simp [D, gap, fooling_distance, hF]
  have hFne : F.carrier.Nonempty := Set.nonempty_iff_ne_empty.mpr hF
  have hvalue_meas :
      ∀ f : X → Bool, f ∈ F.carrier →
        Measurable (fun x => boolean_value (f x)) := by
    intro f hf
    exact (measurable_of_finite boolean_value).comp (F.measurable f hf)
  have hmean_bounds :
      ∀ (Q : ProbabilityMeasure X) (f : X → Bool), f ∈ F.carrier →
        0 ≤ (∫ x, boolean_value (f x) ∂Q.toMeasure) ∧
          (∫ x, boolean_value (f x) ∂Q.toMeasure) ≤ 1 := by
    intro Q f hf
    have hM := hvalue_meas f hf
    have hI : Integrable (fun x => boolean_value (f x)) Q.toMeasure := by
      refine ⟨hM.aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := 1) ?_⟩
      exact Filter.Eventually.of_forall (fun x => by
        cases hfx : f x <;> simp [boolean_value, hfx])
    constructor
    · exact integral_nonneg (fun x => by
        cases hfx : f x <;> simp [boolean_value, hfx])
    · calc
        (∫ x, boolean_value (f x) ∂Q.toMeasure) ≤
            ∫ _x, (1 : ℝ) ∂Q.toMeasure :=
          integral_mono hI (integrable_const 1) (fun x => by
            cases hfx : f x <;> simp [boolean_value, hfx])
        _ = 1 := by simp
  have hgap_score_meas :
      ∀ f : X → Bool, f ∈ F.carrier →
        Measurable (fun p : (Fin n → X) × (Fin n → X) =>
          |(∫ x, boolean_value (f x)
              ∂(empirical_probability_measure P p.1).toMeasure) -
            (∫ x, boolean_value (f x)
              ∂(empirical_probability_measure P p.2).toMeasure)|) := by
    intro f hf
    have hMf := hvalue_meas f hf
    have heq :
        (fun p : (Fin n → X) × (Fin n → X) =>
          |(∫ x, boolean_value (f x)
              ∂(empirical_probability_measure P p.1).toMeasure) -
            (∫ x, boolean_value (f x)
              ∂(empirical_probability_measure P p.2).toMeasure)|) =
        fun p => |(n : ℝ)⁻¹ *
              ∑ i : Fin n, boolean_value (f (p.1 i)) -
            (n : ℝ)⁻¹ *
              ∑ i : Fin n, boolean_value (f (p.2 i))| := by
      funext p
      rw [empirical_probability_measure_integral_local_rademacher_generalization
        P hn p.1 _ hMf]
      rw [empirical_probability_measure_integral_local_rademacher_generalization
        P hn p.2 _ hMf]
    rw [heq]
    apply Measurable.abs
    apply Measurable.sub
    · apply Measurable.const_mul
      apply Finset.measurable_sum
      intro i hi
      exact hMf.comp ((measurable_pi_apply i).comp measurable_fst)
    · apply Measurable.const_mul
      apply Finset.measurable_sum
      intro i hi
      exact hMf.comp ((measurable_pi_apply i).comp measurable_snd)
  have hgapM : Measurable gap := by
    dsimp [gap]
    unfold fooling_distance
    exact Measurable.sSup F.carrier_countable hgap_score_meas
  have hgapB : ∀ p, 0 ≤ gap p ∧ gap p ≤ 1 := by
    intro p
    dsimp [gap]
    unfold fooling_distance
    constructor
    · exact Real.sSup_nonneg (fun y hy => by
        rcases hy with ⟨f, hf, rfl⟩
        exact abs_nonneg _)
    · apply csSup_le (hFne.image _)
      rintro _ ⟨f, hf, rfl⟩
      have h1 := hmean_bounds (empirical_probability_measure P p.1) f hf
      have h2 := hmean_bounds (empirical_probability_measure P p.2) f hf
      rw [abs_le]
      constructor <;> linarith
  have hgapI : Integrable gap (μ.prod μ) := by
    refine ⟨hgapM.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := 1) ?_⟩
    exact Filter.Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hgapB p).1]
      exact (hgapB p).2)
  have hDB :=
    empirical_fooling_distance_measurable_bounded_local_rademacher_generalization
      F P hn
  have hDM : Measurable D := by simpa [D] using hDB.1
  have hDBounds : ∀ S, 0 ≤ D S ∧ D S ≤ 1 := by
    simpa [D] using hDB.2.1
  have hDI : Integrable D μ := by
    refine ⟨hDM.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := 1) ?_⟩
    exact Filter.Eventually.of_forall (fun S => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hDBounds S).1]
      exact (hDBounds S).2)
  have hsample_mean :
      ∀ f : X → Bool, f ∈ F.carrier →
        (∫ T : Fin n → X,
          (n : ℝ)⁻¹ * ∑ i : Fin n, boolean_value (f (T i)) ∂μ) =
          ∫ x, boolean_value (f x) ∂P.toMeasure := by
    intro f hf
    have hMf := hvalue_meas f hf
    have hcoordI : ∀ i : Fin n,
        Integrable (fun T : Fin n → X => boolean_value (f (T i))) μ := by
      intro i
      have hM : Measurable (fun T : Fin n → X =>
          boolean_value (f (T i))) :=
        hMf.comp (measurable_pi_apply i)
      refine ⟨hM.aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := 1) ?_⟩
      exact Filter.Eventually.of_forall (fun T => by
        cases hft : f (T i) <;> simp [boolean_value, hft])
    have hcoord_mean : ∀ i : Fin n,
        (∫ T : Fin n → X, boolean_value (f (T i)) ∂μ) =
          ∫ x, boolean_value (f x) ∂P.toMeasure := by
      intro i
      have hmap :
          μ.map (Function.eval i) = P.toMeasure := by
        dsimp [μ]
        simpa [MeasureTheory.Measure.pi_map_eval] using
          (MeasureTheory.Measure.pi_map_eval
            (μ := fun _ : Fin n => P.toMeasure) i)
      calc
        (∫ T : Fin n → X, boolean_value (f (T i)) ∂μ) =
            ∫ x, boolean_value (f x)
              ∂(μ.map (Function.eval i)) := by
          symm
          exact MeasureTheory.integral_map
            (measurable_pi_apply i).aemeasurable
            hMf.aestronglyMeasurable
        _ = _ := by rw [hmap]
    calc
      (∫ T : Fin n → X,
          (n : ℝ)⁻¹ * ∑ i : Fin n, boolean_value (f (T i)) ∂μ) =
          (n : ℝ)⁻¹ * ∑ i : Fin n,
            (∫ T : Fin n → X, boolean_value (f (T i)) ∂μ) := by
        rw [MeasureTheory.integral_const_mul]
        congr 1
        simpa using MeasureTheory.integral_finsetSum Finset.univ
          (fun i hi => hcoordI i)
      _ = (n : ℝ)⁻¹ * ∑ _i : Fin n,
          (∫ x, boolean_value (f x) ∂P.toMeasure) := by
        congr 1
        exact Finset.sum_congr rfl (fun i hi => hcoord_mean i)
      _ = ∫ x, boolean_value (f x) ∂P.toMeasure := by
        simp [hn.ne']
  have hpoint : ∀ S, D S ≤ ∫ T, gap (S, T) ∂μ := by
    intro S
    dsimp [D]
    unfold fooling_distance
    apply csSup_le (hFne.image _)
    rintro _ ⟨f, hf, rfl⟩
    have hMf := hvalue_meas f hf
    let A : (Fin n → X) → ℝ :=
      fun T => (n : ℝ)⁻¹ * ∑ i : Fin n, boolean_value (f (T i))
    have hAM : Measurable A := by
      dsimp [A]
      apply Measurable.const_mul
      apply Finset.measurable_sum
      intro i hi
      exact hMf.comp (measurable_pi_apply i)
    have hAI : Integrable A μ := by
      refine ⟨hAM.aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := 1) ?_⟩
      exact Filter.Eventually.of_forall (fun T => by
        have hnonneg : 0 ≤ A T := by
          dsimp [A]
          exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
            (Finset.sum_nonneg (fun i hi => by
              cases hfi : f (T i) <;> simp [boolean_value, hfi]))
        rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
        dsimp [A]
        calc
          (n : ℝ)⁻¹ * ∑ i : Fin n, boolean_value (f (T i)) ≤
              (n : ℝ)⁻¹ * ∑ _i : Fin n, (1 : ℝ) := by
            apply mul_le_mul_of_nonneg_left
            · apply Finset.sum_le_sum
              intro i hi
              cases hfi : f (T i) <;> simp [boolean_value, hfi]
            · positivity
          _ = 1 := by simp [hn.ne'])
    have hgapSliceI : Integrable (fun T => gap (S, T)) μ := by
      have hpairM : Measurable
          (fun T : Fin n → X => (S, T)) :=
        measurable_const.prodMk measurable_id
      have hM := hgapM.comp hpairM
      refine ⟨hM.aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := 1) ?_⟩
      exact Filter.Eventually.of_forall (fun T => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hgapB (S, T)).1]
        exact (hgapB (S, T)).2)
    change |(∫ x, boolean_value (f x) ∂P.toMeasure) -
      (∫ x, boolean_value (f x)
        ∂(empirical_probability_measure P S).toMeasure)| ≤ _
    rw [empirical_probability_measure_integral_local_rademacher_generalization
      P hn S _ hMf]
    change |(∫ x, boolean_value (f x) ∂P.toMeasure) - A S| ≤ _
    rw [← hsample_mean f hf]
    calc
      |(∫ T, A T ∂μ) - A S| =
          |∫ T, A T - A S ∂μ| := by
        rw [integral_sub hAI (integrable_const _)]
        simp [μ]
      _ ≤ ∫ T, |A T - A S| ∂μ := by
        simpa [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm
            (μ := μ) (f := fun T => A T - A S))
      _ ≤ ∫ T, gap (S, T) ∂μ := by
        apply integral_mono
        · exact (hAI.sub (integrable_const _)).norm
        · exact hgapSliceI
        · intro T
          dsimp [gap]
          unfold fooling_distance
          have hbdd : BddAbove ((fun g : X → Bool =>
              |(∫ x, boolean_value (g x)
                  ∂(empirical_probability_measure P S).toMeasure) -
                (∫ x, boolean_value (g x)
                  ∂(empirical_probability_measure P T).toMeasure)|) ''
                F.carrier) := by
            refine ⟨1, ?_⟩
            rintro _ ⟨g, hg, rfl⟩
            have h1 := hmean_bounds (empirical_probability_measure P S) g hg
            have h2 := hmean_bounds (empirical_probability_measure P T) g hg
            rw [abs_le]
            constructor <;> linarith
          have hs := le_csSup hbdd ⟨f, hf, rfl⟩
          change |(∫ x, boolean_value (f x)
              ∂(empirical_probability_measure P S).toMeasure) -
            (∫ x, boolean_value (f x)
              ∂(empirical_probability_measure P T).toMeasure)| ≤ _ at hs
          rw [empirical_probability_measure_integral_local_rademacher_generalization
            P hn S _ hMf] at hs
          rw [empirical_probability_measure_integral_local_rademacher_generalization
            P hn T _ hMf] at hs
          simpa [A, abs_sub_comm] using hs
  have houterI : Integrable (fun S => ∫ T, gap (S, T) ∂μ) μ := by
    simpa using hgapI.integral_prod_left
  calc
    (∫ S, fooling_distance F P (empirical_probability_measure P S) ∂μ) =
        ∫ S, D S ∂μ := rfl
    _ ≤ ∫ S, (∫ T, gap (S, T) ∂μ) ∂μ :=
      integral_mono hDI houterI hpoint
    _ = ∫ p : (Fin n → X) × (Fin n → X), gap p ∂(μ.prod μ) := by
      simpa using (MeasureTheory.integral_prod gap hgapI).symm
    _ = _ := rfl

@[blueprint "lem:empirical-pair-fooling-distance-measurable-bounded-local-rademacher-generalization"
  (statement := /-- For positive sample size, the fooling distance between two empirical measures is a measurable function of the pair of samples and takes values in $[0,1]$. -/)
  (proof := /-- Apply \cref{lem:empirical-probability-measure-integral-local-rademacher-generalization} to rewrite every Boolean expectation as a finite average.  Each resulting absolute difference is measurable, their countable supremum is measurable, and the fact that Boolean averages lie in $[0,1]$ bounds the supremum by $1$. -/)
  (title := /-- Measurability of two-sample empirical fooling distance -/)
  (latexEnv := "lemma")]
lemma empirical_pair_fooling_distance_measurable_bounded_local_rademacher_generalization
    {X : Type*} [MeasurableSpace X]
    (F : boolean_distinguishing_family X) (P : ProbabilityMeasure X)
    {n : ℕ} (hn : 0 < n) :
    let gap : ((Fin n → X) × (Fin n → X)) → ℝ :=
      fun p => fooling_distance F (empirical_probability_measure P p.1)
        (empirical_probability_measure P p.2)
    Measurable gap ∧ ∀ p, 0 ≤ gap p ∧ gap p ≤ 1 := by
  classical
  dsimp
  have hvalue_meas :
      ∀ f : X → Bool, f ∈ F.carrier →
        Measurable (fun x => boolean_value (f x)) := by
    intro f hf
    exact (measurable_of_finite boolean_value).comp (F.measurable f hf)
  have hscore_meas :
      ∀ f : X → Bool, f ∈ F.carrier →
        Measurable (fun p : (Fin n → X) × (Fin n → X) =>
          |(∫ x, boolean_value (f x)
              ∂(empirical_probability_measure P p.1).toMeasure) -
            (∫ x, boolean_value (f x)
              ∂(empirical_probability_measure P p.2).toMeasure)|) := by
    intro f hf
    have hMf := hvalue_meas f hf
    have heq :
        (fun p : (Fin n → X) × (Fin n → X) =>
          |(∫ x, boolean_value (f x)
              ∂(empirical_probability_measure P p.1).toMeasure) -
            (∫ x, boolean_value (f x)
              ∂(empirical_probability_measure P p.2).toMeasure)|) =
        fun p => |(n : ℝ)⁻¹ *
              ∑ i : Fin n, boolean_value (f (p.1 i)) -
            (n : ℝ)⁻¹ *
              ∑ i : Fin n, boolean_value (f (p.2 i))| := by
      funext p
      rw [empirical_probability_measure_integral_local_rademacher_generalization
        P hn p.1 _ hMf]
      rw [empirical_probability_measure_integral_local_rademacher_generalization
        P hn p.2 _ hMf]
    rw [heq]
    apply Measurable.abs
    apply Measurable.sub
    · apply Measurable.const_mul
      apply Finset.measurable_sum
      intro i hi
      exact hMf.comp ((measurable_pi_apply i).comp measurable_fst)
    · apply Measurable.const_mul
      apply Finset.measurable_sum
      intro i hi
      exact hMf.comp ((measurable_pi_apply i).comp measurable_snd)
  have hM : Measurable (fun p : (Fin n → X) × (Fin n → X) =>
      fooling_distance F (empirical_probability_measure P p.1)
        (empirical_probability_measure P p.2)) := by
    unfold fooling_distance
    exact Measurable.sSup F.carrier_countable hscore_meas
  refine ⟨hM, ?_⟩
  intro p
  unfold fooling_distance
  constructor
  · exact Real.sSup_nonneg (fun y hy => by
      rcases hy with ⟨f, hf, rfl⟩
      exact abs_nonneg _)
  · by_cases hF : F.carrier = ∅
    · simp [hF]
    · apply csSup_le (Set.nonempty_iff_ne_empty.mpr hF |>.image _)
      rintro _ ⟨f, hf, rfl⟩
      have hmean_bounds (Q : ProbabilityMeasure X) :
          0 ≤ (∫ x, boolean_value (f x) ∂Q.toMeasure) ∧
            (∫ x, boolean_value (f x) ∂Q.toMeasure) ≤ 1 := by
        have hMf := hvalue_meas f hf
        have hI : Integrable (fun x => boolean_value (f x)) Q.toMeasure := by
          refine ⟨hMf.aestronglyMeasurable,
            HasFiniteIntegral.of_bounded (C := 1) ?_⟩
          exact Filter.Eventually.of_forall (fun x => by
            cases hfx : f x <;> simp [boolean_value, hfx])
        constructor
        · exact integral_nonneg (fun x => by
            cases hfx : f x <;> simp [boolean_value, hfx])
        · calc
            (∫ x, boolean_value (f x) ∂Q.toMeasure) ≤
                ∫ _x, (1 : ℝ) ∂Q.toMeasure :=
              integral_mono hI (integrable_const 1) (fun x => by
                cases hfx : f x <;> simp [boolean_value, hfx])
            _ = 1 := by simp
      have h1 := hmean_bounds (empirical_probability_measure P p.1)
      have h2 := hmean_bounds (empirical_probability_measure P p.2)
      rw [abs_le]
      constructor <;> linarith

@[blueprint "lem:empirical-pair-fooling-distance-symmetrization-local-rademacher-generalization"
  (statement := /-- For two independent samples $S,S'\sim P^n$ with $n\geq1$, the expected fooling distance between their empirical measures is at most $\mathcal R_n(\mathcal F,P)$. -/)
  (proof := /-- Average over all coordinatewise swaps of the two samples.  Each swap preserves the product law.  By \cref{lem:empirical-probability-measure-integral-local-rademacher-generalization}, after a fixed swap the difference of empirical Boolean averages is one half of the corresponding signed difference of the centered Boolean values.  The triangle inequality bounds its supremum by one half of the two signed suprema.  Averaging over signs gives one half of the two empirical Rademacher complexities, and integrating the two samples gives $\mathcal R_n(\mathcal F,P)$.  Integrability follows from \cref{lem:empirical-pair-fooling-distance-measurable-bounded-local-rademacher-generalization, lem:empirical-rademacher-measurable-bounded-local}. -/)
  (title := /-- Symmetrization of two-sample fooling distance -/)
  (latexEnv := "lemma")]
lemma empirical_pair_fooling_distance_symmetrization_local_rademacher_generalization
    {X : Type*} [MeasurableSpace X]
    (F : boolean_distinguishing_family X) (P : ProbabilityMeasure X)
    {n : ℕ} (hn : 0 < n) :
    let μ := (ProbabilityMeasure.pi (fun _ : Fin n => P)).toMeasure
    (∫ p : (Fin n → X) × (Fin n → X),
        fooling_distance F (empirical_probability_measure P p.1)
          (empirical_probability_measure P p.2) ∂(μ.prod μ)) ≤
      distributional_rademacher_complexity F n P := by
  classical
  dsimp
  let μ := (ProbabilityMeasure.pi (fun _ : Fin n => P)).toMeasure
  let gap : ((Fin n → X) × (Fin n → X)) → ℝ :=
    fun p => fooling_distance F (empirical_probability_measure P p.1)
      (empirical_probability_measure P p.2)
  let swapBy : (Fin n → Bool) →
      ((Fin n → X) × (Fin n → X)) →
        ((Fin n → X) × (Fin n → X)) :=
    fun σ p =>
      (fun i => if σ i = true then p.1 i else p.2 i,
       fun i => if σ i = true then p.2 i else p.1 i)
  by_cases hF : F.carrier = ∅
  · simp [gap, fooling_distance, distributional_rademacher_complexity,
      empirical_rademacher_complexity, hF]
  have hFne : F.carrier.Nonempty := Set.nonempty_iff_ne_empty.mpr hF
  have hpair :=
    empirical_pair_fooling_distance_measurable_bounded_local_rademacher_generalization
      F P hn
  have hgapM : Measurable gap := by simpa [gap] using hpair.1
  have hgapB : ∀ p, 0 ≤ gap p ∧ gap p ≤ 1 := by
    simpa [gap] using hpair.2
  have hgapI : Integrable gap (μ.prod μ) := by
    refine ⟨hgapM.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := 1) ?_⟩
    exact Filter.Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hgapB p).1]
      exact (hgapB p).2)
  have hswap_involutive :
      ∀ (σ : Fin n → Bool) (p : (Fin n → X) × (Fin n → X)),
        swapBy σ (swapBy σ p) = p := by
    intro σ p
    apply Prod.ext
    · funext i
      dsimp [swapBy]
      by_cases hi : σ i = true <;> simp [hi]
    · funext i
      dsimp [swapBy]
      by_cases hi : σ i = true <;> simp [hi]
  have hswapM : ∀ σ : Fin n → Bool, Measurable (swapBy σ) := by
    intro σ
    apply Measurable.prodMk
    · apply measurable_pi_iff.mpr
      intro i
      cases hσ : σ i
      · simp [swapBy, hσ]
        fun_prop
      · simp [swapBy, hσ]
        fun_prop
    · apply measurable_pi_iff.mpr
      intro i
      cases hσ : σ i
      · simp [swapBy, hσ]
        fun_prop
      · simp [swapBy, hσ]
        fun_prop
  have hswapMP : ∀ σ : Fin n → Bool,
      MeasurePreserving (swapBy σ) (μ.prod μ) (μ.prod μ) := by
    intro σ
    let coordSwap : (Fin n → X × X) → (Fin n → X × X) :=
      fun p i => if σ i = true then p i else (p i).swap
    have hcoord : MeasurePreserving coordSwap
        (Measure.pi (fun _ : Fin n => P.toMeasure.prod P.toMeasure))
        (Measure.pi (fun _ : Fin n => P.toMeasure.prod P.toMeasure)) := by
      change MeasurePreserving
        (fun p i => if σ i = true then p i else (p i).swap)
        (Measure.pi (fun _ : Fin n => P.toMeasure.prod P.toMeasure))
        (Measure.pi (fun _ : Fin n => P.toMeasure.prod P.toMeasure))
      apply MeasureTheory.measurePreserving_pi
        (fun _ : Fin n => P.toMeasure.prod P.toMeasure)
        (fun _ : Fin n => P.toMeasure.prod P.toMeasure)
        (f := fun i q => if σ i = true then q else q.swap)
      intro i
      by_cases hi : σ i = true
      · convert (MeasurePreserving.id
            (μ := P.toMeasure.prod P.toMeasure)) using 1
        funext q
        simp [hi]
      · simpa [coordSwap, hi] using
          (MeasureTheory.Measure.measurePreserving_swap
            (μ := P.toMeasure) (ν := P.toMeasure))
    have harrow :=
      MeasureTheory.measurePreserving_arrowProdEquivProdArrow
        X X (Fin n) (fun _ => P.toMeasure) (fun _ => P.toMeasure)
    have harrow_symm : MeasurePreserving
        ((MeasurableEquiv.arrowProdEquivProdArrow X X (Fin n)).symm)
        (μ.prod μ)
        (Measure.pi (fun _ : Fin n => P.toMeasure.prod P.toMeasure)) := by
      have h := harrow.symm
        (e := MeasurableEquiv.arrowProdEquivProdArrow X X (Fin n))
      simpa [μ] using h
    have harrow_fwd : MeasurePreserving
        (MeasurableEquiv.arrowProdEquivProdArrow X X (Fin n))
        (Measure.pi (fun _ : Fin n => P.toMeasure.prod P.toMeasure))
        (μ.prod μ) := by
      simpa [μ] using harrow
    have hcomp := harrow_fwd.comp (hcoord.comp harrow_symm)
    have heq :
        swapBy σ =
          (MeasurableEquiv.arrowProdEquivProdArrow X X (Fin n)) ∘
            coordSwap ∘
              (MeasurableEquiv.arrowProdEquivProdArrow X X (Fin n)).symm := by
      funext p
      apply Prod.ext <;> funext i
      · dsimp [swapBy, coordSwap]
        by_cases hi : σ i = true <;>
          simp [hi, MeasurableEquiv.arrowProdEquivProdArrow,
            Equiv.arrowProdEquivProdArrow]
      · dsimp [swapBy, coordSwap]
        by_cases hi : σ i = true <;>
          simp [hi, MeasurableEquiv.arrowProdEquivProdArrow,
            Equiv.arrowProdEquivProdArrow]
    rw [heq]
    exact hcomp
  have hinvariant : ∀ σ : Fin n → Bool,
      (∫ p, gap p ∂(μ.prod μ)) =
        ∫ p, gap (swapBy σ p) ∂(μ.prod μ) := by
    intro σ
    let e : ((Fin n → X) × (Fin n → X)) ≃ᵐ
        ((Fin n → X) × (Fin n → X)) := {
      toFun := swapBy σ
      invFun := swapBy σ
      left_inv := hswap_involutive σ
      right_inv := hswap_involutive σ
      measurable_toFun := hswapM σ
      measurable_invFun := hswapM σ }
    exact ((hswapMP σ).integral_comp e.measurableEmbedding gap).symm
  let radScore : (Fin n → Bool) → (Fin n → X) → ℝ :=
    fun σ S =>
      sSup ((fun f : X → Bool =>
        |(n : ℝ)⁻¹ * ∑ i : Fin n,
          rademacher_sign (σ i) *
            (2 * boolean_value (f (S i)) - 1)|) '' F.carrier)
  have hrad_bound : ∀ (σ : Fin n → Bool) (S : Fin n → X),
      BddAbove ((fun f : X → Bool =>
        |(n : ℝ)⁻¹ * ∑ i : Fin n,
          rademacher_sign (σ i) *
            (2 * boolean_value (f (S i)) - 1)|) '' F.carrier) := by
    intro σ S
    refine ⟨1, ?_⟩
    rintro _ ⟨f, hf, rfl⟩
    calc
      |(n : ℝ)⁻¹ * ∑ i : Fin n,
          rademacher_sign (σ i) *
            (2 * boolean_value (f (S i)) - 1)| =
          (n : ℝ)⁻¹ *
            |∑ i : Fin n, rademacher_sign (σ i) *
              (2 * boolean_value (f (S i)) - 1)| := by
        rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
      _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, (1 : ℝ) := by
        apply mul_le_mul_of_nonneg_left
        · calc
            |∑ i : Fin n, rademacher_sign (σ i) *
                (2 * boolean_value (f (S i)) - 1)| ≤
                ∑ i : Fin n, |rademacher_sign (σ i) *
                  (2 * boolean_value (f (S i)) - 1)| :=
              Finset.abs_sum_le_sum_abs _ _
            _ = ∑ _i : Fin n, (1 : ℝ) := by
              apply Finset.sum_congr rfl
              intro i hi
              cases hσ : σ i <;> cases hfS : f (S i) <;>
                norm_num [rademacher_sign, boolean_value, hσ, hfS]
        · positivity
      _ = 1 := by simp [hn.ne']
  have hsingle : ∀ (σ : Fin n → Bool)
      (p : (Fin n → X) × (Fin n → X)),
      gap (swapBy σ p) ≤
        (1 / 2 : ℝ) * (radScore σ p.1 + radScore σ p.2) := by
    intro σ p
    dsimp [gap]
    unfold fooling_distance
    apply csSup_le (hFne.image _)
    rintro _ ⟨f, hf, rfl⟩
    have hMf : Measurable (fun x => boolean_value (f x)) :=
      (measurable_of_finite boolean_value).comp (F.measurable f hf)
    change |(∫ x, boolean_value (f x)
        ∂(empirical_probability_measure P (swapBy σ p).1).toMeasure) -
      (∫ x, boolean_value (f x)
        ∂(empirical_probability_measure P (swapBy σ p).2).toMeasure)| ≤ _
    rw [empirical_probability_measure_integral_local_rademacher_generalization
      P hn (swapBy σ p).1 _ hMf]
    rw [empirical_probability_measure_integral_local_rademacher_generalization
      P hn (swapBy σ p).2 _ hMf]
    have hsum :
        (∑ i : Fin n, boolean_value (f ((swapBy σ p).1 i))) -
          (∑ i : Fin n, boolean_value (f ((swapBy σ p).2 i))) =
        (1 / 2 : ℝ) * ∑ i : Fin n,
          rademacher_sign (σ i) *
            ((2 * boolean_value (f (p.1 i)) - 1) -
              (2 * boolean_value (f (p.2 i)) - 1)) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [swapBy]
      cases hσ : σ i <;>
        cases h1 : f (p.1 i) <;> cases h2 : f (p.2 i) <;>
          norm_num [rademacher_sign, boolean_value, hσ, h1, h2]
    have hrewrite :
        (n : ℝ)⁻¹ *
            (∑ i : Fin n, boolean_value (f ((swapBy σ p).1 i))) -
          (n : ℝ)⁻¹ *
            (∑ i : Fin n, boolean_value (f ((swapBy σ p).2 i))) =
        (1 / 2 : ℝ) * ((n : ℝ)⁻¹ * ∑ i : Fin n,
          rademacher_sign (σ i) *
            ((2 * boolean_value (f (p.1 i)) - 1) -
              (2 * boolean_value (f (p.2 i)) - 1))) := by
      rw [← mul_sub, hsum]
      ring
    rw [hrewrite, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have h1 := le_csSup (hrad_bound σ p.1) ⟨f, hf, rfl⟩
    have h2 := le_csSup (hrad_bound σ p.2) ⟨f, hf, rfl⟩
    dsimp [radScore]
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    calc
      |(n : ℝ)⁻¹ * ∑ i : Fin n,
          rademacher_sign (σ i) *
            ((2 * boolean_value (f (p.1 i)) - 1) -
              (2 * boolean_value (f (p.2 i)) - 1))| =
          |(n : ℝ)⁻¹ * ∑ i : Fin n,
              rademacher_sign (σ i) *
                (2 * boolean_value (f (p.1 i)) - 1) -
            (n : ℝ)⁻¹ * ∑ i : Fin n,
              rademacher_sign (σ i) *
                (2 * boolean_value (f (p.2 i)) - 1)| := by
        congr 1
        rw [← mul_sub, ← Finset.sum_sub_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ |(n : ℝ)⁻¹ * ∑ i : Fin n,
              rademacher_sign (σ i) *
                (2 * boolean_value (f (p.1 i)) - 1)| +
            |(n : ℝ)⁻¹ * ∑ i : Fin n,
              rademacher_sign (σ i) *
                (2 * boolean_value (f (p.2 i)) - 1)| := abs_sub _ _
      _ ≤ radScore σ p.1 + radScore σ p.2 := add_le_add h1 h2
  have hpoint : ∀ p : (Fin n → X) × (Fin n → X),
      ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, gap (swapBy σ p) ≤
        (1 / 2 : ℝ) *
          (empirical_rademacher_complexity F p.1 +
            empirical_rademacher_complexity F p.2) := by
    intro p
    calc
      ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, gap (swapBy σ p) ≤
          ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
            (1 / 2 : ℝ) * (radScore σ p.1 + radScore σ p.2) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum (fun σ hσ => hsingle σ p)
        · positivity
      _ = (1 / 2 : ℝ) *
          (empirical_rademacher_complexity F p.1 +
            empirical_rademacher_complexity F p.2) := by
        unfold empirical_rademacher_complexity
        dsimp [radScore]
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        ring
  have hR := empirical_rademacher_measurable_bounded_local F hn
  let Rhat : (Fin n → X) → ℝ :=
    fun S => empirical_rademacher_complexity F S
  have hRM : Measurable Rhat := by simpa [Rhat] using hR.1
  have hRB : ∀ S, 0 ≤ Rhat S ∧ Rhat S ≤ 1 := by
    simpa [Rhat] using hR.2
  have hleftI : Integrable
      (fun p : (Fin n → X) × (Fin n → X) =>
        ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, gap (swapBy σ p))
      (μ.prod μ) := by
    apply Integrable.const_mul
    apply MeasureTheory.integrable_finsetSum Finset.univ
    intro σ hσ
    have hM := hgapM.comp (hswapM σ)
    refine ⟨hM.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := 1) ?_⟩
    exact Filter.Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hgapB (swapBy σ p)).1]
      exact (hgapB (swapBy σ p)).2)
  have hrightI : Integrable
      (fun p : (Fin n → X) × (Fin n → X) =>
        (1 / 2 : ℝ) * (Rhat p.1 + Rhat p.2)) (μ.prod μ) := by
    have hM : Measurable
        (fun p : (Fin n → X) × (Fin n → X) =>
          (1 / 2 : ℝ) * (Rhat p.1 + Rhat p.2)) := by
      fun_prop
    refine ⟨hM.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := 1) ?_⟩
    exact Filter.Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · nlinarith [(hRB p.1).1, (hRB p.1).2, (hRB p.2).1, (hRB p.2).2]
      · nlinarith [(hRB p.1).1, (hRB p.2).1])
  have hRfstI : Integrable
      (fun p : (Fin n → X) × (Fin n → X) => Rhat p.1) (μ.prod μ) := by
    have hM : Measurable
        (fun p : (Fin n → X) × (Fin n → X) => Rhat p.1) :=
      hRM.comp measurable_fst
    refine ⟨hM.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := 1) ?_⟩
    exact Filter.Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hRB p.1).1]
      exact (hRB p.1).2)
  have hRsndI : Integrable
      (fun p : (Fin n → X) × (Fin n → X) => Rhat p.2) (μ.prod μ) := by
    have hM : Measurable
        (fun p : (Fin n → X) × (Fin n → X) => Rhat p.2) :=
      hRM.comp measurable_snd
    refine ⟨hM.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := 1) ?_⟩
    exact Filter.Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hRB p.2).1]
      exact (hRB p.2).2)
  calc
    (∫ p, gap p ∂(μ.prod μ)) =
        ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
          (∫ p, gap (swapBy σ p) ∂(μ.prod μ)) := by
      simp_rw [← hinvariant]
      simp
    _ = ∫ p, ((2 : ℝ) ^ n)⁻¹ *
          ∑ σ : Fin n → Bool, gap (swapBy σ p) ∂(μ.prod μ) := by
      rw [MeasureTheory.integral_const_mul]
      congr 1
      symm
      apply MeasureTheory.integral_finsetSum Finset.univ
      intro σ hσ
      have hM := hgapM.comp (hswapM σ)
      refine ⟨hM.aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := 1) ?_⟩
      exact Filter.Eventually.of_forall (fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hgapB (swapBy σ p)).1]
        exact (hgapB (swapBy σ p)).2)
    _ ≤ ∫ p, (1 / 2 : ℝ) * (Rhat p.1 + Rhat p.2) ∂(μ.prod μ) :=
      integral_mono hleftI hrightI hpoint
    _ = (1 / 2 : ℝ) *
        ((∫ p, Rhat p.1 ∂(μ.prod μ)) +
          (∫ p, Rhat p.2 ∂(μ.prod μ))) := by
      rw [MeasureTheory.integral_const_mul]
      congr 1
      exact integral_add hRfstI hRsndI
    _ = (1 / 2 : ℝ) *
        ((∫ S, Rhat S ∂μ) + (∫ S, Rhat S ∂μ)) := by
      congr 2
      · rw [MeasureTheory.integral_prod _ hRfstI]
        simp [μ]
      · rw [MeasureTheory.integral_prod _ hRsndI]
        simp [μ]
    _ = distributional_rademacher_complexity F n P := by
      change (1 / 2 : ℝ) *
        (distributional_rademacher_complexity F n P +
          distributional_rademacher_complexity F n P) =
        distributional_rademacher_complexity F n P
      ring

@[blueprint "lem:rademacher-generalization"
  (statement := /-- There is a universal constant $C>0$ such that, for every standard Borel measurable space $\mathcal X$, every countable family $\mathcal F$ of measurable Boolean functions on $\mathcal X$ that is closed under pointwise complementation, every probability measure $P$ on $\mathcal X$, every $n\geq1$, and every $\delta\in(0,1)$, the map $S\mapsto\widehat{\mathcal R}(\mathcal F,S)$ is integrable under $P^n$, the displayed good-sample set is measurable, and
  \[
  \Pr_{S\sim P^n}\left[
    d_{\mathcal F}(P,\widehat P_S)
    \leq \mathcal R_n(\mathcal F,P)
      +C\sqrt{\frac{1+\log(1/\delta)}{n}}
  \right]\geq1-\delta.
  \] -/)
  (proof := /-- Put
  $D(S)=d_{\mathcal F}(P,\widehat P_S)$.  By
  \cref{lem:empirical-fooling-distance-measurable-bounded-local-rademacher-generalization},
  the function $D$ is measurable, takes values in $[0,1]$, and changes by at
  most $1/n$ when one coordinate of $S$ is replaced.  In particular, $D$ is
  integrable.  The empirical Rademacher functional is likewise measurable,
  bounded by $1$, and integrable by
  \cref{lem:empirical-rademacher-measurable-bounded-local}.

  Let $S'$ be an independent sample with law $P^n$.  The ghost-sample
  inequality
  \cref{lem:empirical-fooling-distance-ghost-bound-local-rademacher-generalization}
  and the coordinate-swap symmetrization inequality
  \cref{lem:empirical-pair-fooling-distance-symmetrization-local-rademacher-generalization}
  give
  \[
    \mathbb E_{S\sim P^n}D(S)
      \leq \mathbb E_{S,S'\sim P^n}
        d_{\mathcal F}(\widehat P_S,\widehat P_{S'})
      \leq \mathcal R_n(\mathcal F,P).
  \]

  Apply
  \cref{lem:finite-product-bounded-differences-subgaussian-local} to $D$ with
  coordinate bound $a=1/n$.  The centered random variable
  $D-\mathbb E D$ is sub-Gaussian with variance proxy $na^2=1/n$.
  Consequently, for every $t\geq0$,
  \[
    \Pr[D-\mathbb E D\geq t]\leq \exp(-nt^2/2).
  \]
  Set $A=1+\log(1/\delta)$ and $t=2\sqrt{A/n}$.  Since
  $0<\delta<1$, one has $A>0$ and
  \[
    -nt^2/2=-2A=-2+2\log\delta\leq\log\delta.
  \]
  Thus the preceding tail probability is at most $\delta$.  The expectation
  bound shows that the complement of
  \[
    \left\{S:D(S)\leq
      \mathcal R_n(\mathcal F,P)+
        2\sqrt{(1+\log(1/\delta))/n}\right\}
  \]
  is contained in this upper-tail event.  The good set is measurable because
  $D$ is measurable.  Taking its complement and using
  \cref{def:sample-event-probability} proves the result with the universal
  constant $C=2$. -/)
  (title := /-- Rademacher generalization bound -/)
  (latexEnv := "lemma")]
lemma rademacher_generalization :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
        (F : boolean_distinguishing_family X) (P : ProbabilityMeasure X)
        (n : ℕ) (δ : ℝ), 0 < n → 0 < δ → δ < 1 →
        Integrable (fun S : Fin n → X => empirical_rademacher_complexity F S)
          (ProbabilityMeasure.pi (fun _ : Fin n => P)).toMeasure ∧
        MeasurableSet
          {S : Fin n → X |
            fooling_distance F P (empirical_probability_measure P S) ≤
              distributional_rademacher_complexity F n P +
                C * Real.sqrt ((1 + Real.log (1 / δ)) / n)} ∧
        sample_event_probability P n
          {S : Fin n → X |
            fooling_distance F P (empirical_probability_measure P S) ≤
              distributional_rademacher_complexity F n P +
                C * Real.sqrt ((1 + Real.log (1 / δ)) / n)} ≥ 1 - δ := by
  refine ⟨2, by norm_num, ?_⟩
  intro X inst1 inst2 F P n δ hn hδ hδ1
  letI : Nonempty X := P.nonempty
  let μ := (ProbabilityMeasure.pi (fun _ : Fin n => P)).toMeasure
  let D : (Fin n → X) → ℝ :=
    fun S => fooling_distance F P (empirical_probability_measure P S)
  have hR := empirical_rademacher_measurable_bounded_local F hn
  have hRI : Integrable
      (fun S : Fin n → X => empirical_rademacher_complexity F S) μ := by
    refine ⟨hR.1.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := 1) ?_⟩
    exact Filter.Eventually.of_forall (fun S => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hR.2 S).1]
      exact (hR.2 S).2)
  have hDB :=
    empirical_fooling_distance_measurable_bounded_local_rademacher_generalization
      F P hn
  have hDM : Measurable D := by simpa [D] using hDB.1
  have hDBounds : ∀ S, 0 ≤ D S ∧ D S ≤ 1 := by
    simpa [D] using hDB.2.1
  have hDupdate : ∀ (S : Fin n → X) (k : Fin n) (z' : X),
      |D S - D (Function.update S k z')| ≤ 1 / (n : ℝ) := by
    simpa [D] using hDB.2.2
  have hDI : Integrable D μ := by
    refine ⟨hDM.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := 1) ?_⟩
    exact Filter.Eventually.of_forall (fun S => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hDBounds S).1]
      exact (hDBounds S).2)
  have hmean :
      (∫ S, D S ∂μ) ≤ distributional_rademacher_complexity F n P := by
    have hghost :=
      empirical_fooling_distance_ghost_bound_local_rademacher_generalization
        F P hn
    have hsymm :=
      empirical_pair_fooling_distance_symmetrization_local_rademacher_generalization
        F P hn
    have hg :
        (∫ S, D S ∂μ) ≤
          ∫ p : (Fin n → X) × (Fin n → X),
            fooling_distance F (empirical_probability_measure P p.1)
              (empirical_probability_measure P p.2) ∂(μ.prod μ) := by
      simpa [D, μ] using hghost
    have hs :
        (∫ p : (Fin n → X) × (Fin n → X),
            fooling_distance F (empirical_probability_measure P p.1)
              (empirical_probability_measure P p.2) ∂(μ.prod μ)) ≤
          distributional_rademacher_complexity F n P := by
      simpa [μ] using hsymm
    exact hg.trans hs
  let a : NNReal := ⟨1 / (n : ℝ), by positivity⟩
  have ha : (a : ℝ) = 1 / (n : ℝ) := rfl
  have hsg : ProbabilityTheory.HasSubgaussianMGF
      (fun S => D S - ∫ T, D T ∂μ) ((n : NNReal) * a ^ 2) μ := by
    apply finite_product_bounded_differences_subgaussian_local
      P a n D hDM hDBounds
    intro S k z'
    simpa [ha] using hDupdate S k z'
  let A : ℝ := 1 + Real.log (1 / δ)
  let t : ℝ := 2 * Real.sqrt (A / n)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hratio : 1 < 1 / δ := by
    exact (lt_div_iff₀ hδ).2 (by linarith)
  have hA : 0 < A := by
    dsimp [A]
    have h := Real.log_pos hratio
    linarith
  have harg : 0 ≤ A / (n : ℝ) := le_of_lt (div_pos hA hnR)
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have htsq : t ^ 2 = 4 * A / (n : ℝ) := by
    dsimp [t]
    rw [mul_pow, Real.sq_sqrt harg]
    ring
  have hc : (((n : NNReal) * a ^ 2 : NNReal) : ℝ) =
      1 / (n : ℝ) := by
    push_cast
    rw [ha]
    field_simp
  have hlogδ : Real.log δ < 0 := Real.log_neg hδ hδ1
  have hexponent :
      -t ^ 2 / (2 * (((n : NNReal) * a ^ 2 : NNReal) : ℝ)) ≤
        Real.log δ := by
    rw [hc, htsq]
    dsimp [A]
    rw [show Real.log (1 / δ) = -Real.log δ by
      rw [one_div, Real.log_inv]]
    field_simp
    nlinarith
  have htail :
      Real.exp (-t ^ 2 /
        (2 * (((n : NNReal) * a ^ 2 : NNReal) : ℝ))) ≤ δ := by
    calc
      _ ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr hexponent
      _ = δ := Real.exp_log hδ
  let good : Set (Fin n → X) :=
    {S | D S ≤ distributional_rademacher_complexity F n P + t}
  have hgoodM : MeasurableSet good := by
    dsimp [good]
    exact measurableSet_le hDM measurable_const
  refine ⟨?_, ?_, ?_⟩
  · simpa [μ] using hRI
  · change MeasurableSet {S : Fin n → X |
      D S ≤ distributional_rademacher_complexity F n P +
        2 * Real.sqrt ((1 + Real.log (1 / δ)) / n)}
    simpa [good, t, A] using hgoodM
  · have hbad_subset :
        goodᶜ ⊆ {S : Fin n → X | t ≤ D S - ∫ T, D T ∂μ} := by
      intro S hS
      simp only [good, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hS ⊢
      linarith
    have hbad : μ.real goodᶜ ≤ δ := by
      calc
        μ.real goodᶜ ≤
            μ.real {S : Fin n → X | t ≤ D S - ∫ T, D T ∂μ} :=
          measureReal_mono hbad_subset
        _ ≤ Real.exp (-t ^ 2 /
            (2 * (((n : NNReal) * a ^ 2 : NNReal) : ℝ))) :=
          hsg.measure_ge_le ht
        _ ≤ δ := htail
    have hcomp := MeasureTheory.probReal_compl_eq_one_sub
      (μ := μ) hgoodM
    change μ.real good ≥ 1 - δ
    linarith

@[blueprint "lem:distributional-rademacher-monotone-sample-size"
  (statement := /-- Let $\mathcal X$ be a measurable space, let $P$ be a probability measure on $\mathcal X$, and let $\mathcal F$ be a countable family of measurable Boolean functions on $\mathcal X$ that is closed under pointwise complementation.  For all natural numbers $m,s$ with $1\leq m\leq s$, the empirical-complexity functionals on $\mathcal X^m$ and $\mathcal X^s$ are integrable under $P^m$ and $P^s$, respectively, and
  $\mathcal R_s(\mathcal F,P)\leq\mathcal R_m(\mathcal F,P)$. -/)
  (proof := /-- By \cref{lem:empirical-rademacher-concentration}, the empirical-complexity functional of \cref{def:empirical-rademacher-complexity} is integrable under $P^q$ for every positive integer $q$; in particular, it is integrable at $q=m$ and $q=s$.

  We first prove the adjacent-sample inequality.  Fix $n\geq1$, a sample $S=(x_i)_{i=1}^{n+1}$, a sign vector $\sigma$, and $f\in\mathcal F$.  Double counting the sums obtained by deleting one coordinate gives
  \[
    \frac1{n+1}\sum_{i=1}^{n+1}\sigma_i(2f(x_i)-1)
      =\frac1{n+1}\sum_{j=1}^{n+1}
        \frac1n\sum_{i\ne j}\sigma_i(2f(x_i)-1).
  \]
  The triangle inequality, followed by taking the supremum over $f$, bounds the absolute value on the left by the average of the $n$-sample suprema on the right.  Averaging over $\sigma$ preserves this inequality.  For each fixed deleted coordinate $j$, restriction of sign vectors from $n+1$ coordinates to the remaining $n$ coordinates is two-to-one, since the deleted sign has two possible values.  Consequently,
  \[
    \widehat{\mathcal R}(\mathcal F,S)
      \leq \frac1{n+1}\sum_{j=1}^{n+1}
        \widehat{\mathcal R}(\mathcal F,S^{\setminus j}).
  \]

  Under the product measure $P^{n+1}$, every coordinate-deletion map is measure-preserving onto $P^n$.  Integrating the preceding inequality, using the established integrability to interchange each finite sum and integral, and applying \cref{def:distributional-rademacher-complexity}, yields
  $\mathcal R_{n+1}(\mathcal F,P)\leq\mathcal R_n(\mathcal F,P)$.  Induction from $m$ to $s$ now gives
  $\mathcal R_s(\mathcal F,P)\leq\mathcal R_m(\mathcal F,P)$. -/)
  (title := /-- Monotonicity in the sample size -/)
  (latexEnv := "lemma")]
lemma distributional_rademacher_monotone_sample_size
    {X : Type*} [MeasurableSpace X]
    (F : boolean_distinguishing_family X) (P : ProbabilityMeasure X)
    {m s : ℕ} (hm : 0 < m) (hms : m ≤ s) :
    Integrable (fun S : Fin s → X => empirical_rademacher_complexity F S)
      (ProbabilityMeasure.pi (fun _ : Fin s => P)).toMeasure ∧
    Integrable (fun S : Fin m → X => empirical_rademacher_complexity F S)
      (ProbabilityMeasure.pi (fun _ : Fin m => P)).toMeasure ∧
    distributional_rademacher_complexity F s P ≤
      distributional_rademacher_complexity F m P := by
  have hscore_bound :
      ∀ {q : ℕ}, 0 < q →
        ∀ (T : Fin q → X) (σ : Fin q → Bool) (f : X → Bool),
          |(q : ℝ)⁻¹ *
              ∑ i : Fin q,
                rademacher_sign (σ i) *
                  (2 * boolean_value (f (T i)) - 1)| ≤ 1 := by
    intro q hq T σ f
    have hterm :
        ∀ i : Fin q,
          |rademacher_sign (σ i) *
              (2 * boolean_value (f (T i)) - 1)| = 1 := by
      intro i
      cases hσ : σ i <;> cases hf : f (T i) <;>
        norm_num [rademacher_sign, boolean_value, hσ, hf]
    calc
      |(q : ℝ)⁻¹ *
          ∑ i : Fin q,
            rademacher_sign (σ i) *
              (2 * boolean_value (f (T i)) - 1)| =
          (q : ℝ)⁻¹ *
            |∑ i : Fin q,
              rademacher_sign (σ i) *
                (2 * boolean_value (f (T i)) - 1)| := by
        rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg q))]
      _ ≤ (q : ℝ)⁻¹ *
          ∑ i : Fin q,
            |rademacher_sign (σ i) *
              (2 * boolean_value (f (T i)) - 1)| := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.abs_sum_le_sum_abs
            (fun i : Fin q =>
              rademacher_sign (σ i) *
                (2 * boolean_value (f (T i)) - 1)) Finset.univ
        · exact inv_nonneg.mpr (Nat.cast_nonneg q)
      _ = 1 := by
        simp_rw [hterm]
        simp [hq.ne']
  have hmean :
      ∀ {n : ℕ}, 0 < n →
        ∀ a : Fin (n + 1) → ℝ,
          ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i, a i =
            ((n + 1 : ℕ) : ℝ)⁻¹ *
              ∑ j : Fin (n + 1),
                (n : ℝ)⁻¹ * ∑ i : Fin n, a (j.succAbove i) := by
    intro n hn a
    have hdel :
        ∀ j : Fin (n + 1),
          ∑ i : Fin n, a (j.succAbove i) =
            (∑ i : Fin (n + 1), a i) - a j := by
      intro j
      have h := Fin.sum_univ_succAbove a j
      linarith
    simp_rw [hdel]
    field_simp
    rw [← Finset.sum_div]
    field_simp [hn.ne']
    rw [Finset.sum_sub_distrib]
    simp
    ring
  have hsign :
      ∀ {n : ℕ} (j : Fin (n + 1)) (b : (Fin n → Bool) → ℝ),
        (∑ σ : Fin (n + 1) → Bool,
          b (fun i : Fin n => σ (j.succAbove i))) =
            2 * (∑ τ : Fin n → Bool, b τ) := by
    intro n j b
    rw [←
      (Fin.insertNthEquiv (fun _ : Fin (n + 1) => Bool) j).sum_comp]
    rw [Fintype.sum_prod_type]
    simp
  have halgebra :
      ∀ {n : ℕ} (B : Fin (n + 1) → (Fin n → Bool) → ℝ),
        ((2 : ℝ) ^ (n + 1))⁻¹ *
            (∑ σ : Fin (n + 1) → Bool,
              ((n + 1 : ℕ) : ℝ)⁻¹ *
                (∑ j : Fin (n + 1),
                  B j (fun i : Fin n => σ (j.succAbove i)))) =
          ((n + 1 : ℕ) : ℝ)⁻¹ *
            (∑ j : Fin (n + 1),
              ((2 : ℝ) ^ n)⁻¹ *
                (∑ τ : Fin n → Bool, B j τ)) := by
    intro n B
    calc
      _ = ((2 : ℝ) ^ (n + 1))⁻¹ *
          ((n + 1 : ℕ) : ℝ)⁻¹ *
            (∑ σ : Fin (n + 1) → Bool,
              ∑ j : Fin (n + 1),
                B j (fun i : Fin n => σ (j.succAbove i))) := by
        rw [← Finset.mul_sum]
        ring
      _ = ((2 : ℝ) ^ (n + 1))⁻¹ *
          ((n + 1 : ℕ) : ℝ)⁻¹ *
            (∑ j : Fin (n + 1),
              2 * (∑ τ : Fin n → Bool, B j τ)) := by
        rw [Finset.sum_comm]
        simp_rw [hsign]
      _ = _ := by
        simp_rw [← Finset.mul_sum]
        rw [pow_succ]
        ring
  have hpoint :
      ∀ {n : ℕ}, 0 < n →
        ∀ S : Fin (n + 1) → X,
          empirical_rademacher_complexity F S ≤
            ((n + 1 : ℕ) : ℝ)⁻¹ *
              ∑ j : Fin (n + 1),
                empirical_rademacher_complexity F
                  (fun i : Fin n => S (j.succAbove i)) := by
    intro n hn S
    by_cases hF : F.carrier = ∅
    · simp [empirical_rademacher_complexity, hF]
    have hFne : F.carrier.Nonempty := Set.nonempty_iff_ne_empty.mpr hF
    have hsup :
        ∀ σ : Fin (n + 1) → Bool,
          sSup ((fun f : X → Bool =>
            |((n + 1 : ℕ) : ℝ)⁻¹ *
              ∑ i : Fin (n + 1),
                rademacher_sign (σ i) *
                  (2 * boolean_value (f (S i)) - 1)|) '' F.carrier) ≤
            ((n + 1 : ℕ) : ℝ)⁻¹ *
              ∑ j : Fin (n + 1),
                sSup ((fun f : X → Bool =>
                  |(n : ℝ)⁻¹ *
                    ∑ i : Fin n,
                      rademacher_sign (σ (j.succAbove i)) *
                        (2 * boolean_value (f (S (j.succAbove i))) - 1)|) ''
                    F.carrier) := by
      intro σ
      apply csSup_le (hFne.image _)
      rintro _ ⟨f, hf, rfl⟩
      change
        |((n + 1 : ℕ) : ℝ)⁻¹ *
          ∑ i : Fin (n + 1),
            rademacher_sign (σ i) *
              (2 * boolean_value (f (S i)) - 1)| ≤ _
      conv_lhs => rw [hmean hn]
      calc
        |((n + 1 : ℕ) : ℝ)⁻¹ *
            ∑ j : Fin (n + 1),
              (n : ℝ)⁻¹ *
                ∑ i : Fin n,
                  rademacher_sign (σ (j.succAbove i)) *
                    (2 * boolean_value (f (S (j.succAbove i))) - 1)| ≤
            ((n + 1 : ℕ) : ℝ)⁻¹ *
              ∑ j : Fin (n + 1),
                |(n : ℝ)⁻¹ *
                  ∑ i : Fin n,
                    rademacher_sign (σ (j.succAbove i)) *
                      (2 * boolean_value (f (S (j.succAbove i))) - 1)| := by
          rw [abs_mul,
            abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg (n + 1)))]
          apply mul_le_mul_of_nonneg_left
          · exact Finset.abs_sum_le_sum_abs _ Finset.univ
          · exact inv_nonneg.mpr (Nat.cast_nonneg (n + 1))
        _ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ *
            ∑ j : Fin (n + 1),
              sSup ((fun g : X → Bool =>
                |(n : ℝ)⁻¹ *
                  ∑ i : Fin n,
                    rademacher_sign (σ (j.succAbove i)) *
                      (2 * boolean_value (g (S (j.succAbove i))) - 1)|) ''
                F.carrier) := by
          apply mul_le_mul_of_nonneg_left
          · apply Finset.sum_le_sum
            intro j hj
            apply le_csSup
            · refine ⟨1, ?_⟩
              rintro _ ⟨g, hg, rfl⟩
              exact hscore_bound hn
                (fun i : Fin n => S (j.succAbove i))
                (fun i : Fin n => σ (j.succAbove i)) g
            · exact ⟨f, hf, rfl⟩
          · exact inv_nonneg.mpr (Nat.cast_nonneg (n + 1))
    unfold empirical_rademacher_complexity
    calc
      ((2 : ℝ) ^ (n + 1))⁻¹ *
          ∑ σ : Fin (n + 1) → Bool,
            sSup ((fun f : X → Bool =>
              |((n + 1 : ℕ) : ℝ)⁻¹ *
                ∑ i : Fin (n + 1),
                  rademacher_sign (σ i) *
                    (2 * boolean_value (f (S i)) - 1)|) '' F.carrier) ≤
          ((2 : ℝ) ^ (n + 1))⁻¹ *
            ∑ σ : Fin (n + 1) → Bool,
              ((n + 1 : ℕ) : ℝ)⁻¹ *
                ∑ j : Fin (n + 1),
                  sSup ((fun f : X → Bool =>
                    |(n : ℝ)⁻¹ *
                      ∑ i : Fin n,
                        rademacher_sign (σ (j.succAbove i)) *
                          (2 * boolean_value
                            (f (S (j.succAbove i))) - 1)|) '' F.carrier) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum (fun σ hσ => hsup σ)
        · positivity
      _ = _ := by
        exact halgebra (fun j τ =>
          sSup ((fun f : X → Bool =>
            |(n : ℝ)⁻¹ *
              ∑ i : Fin n,
                rademacher_sign (τ i) *
                  (2 * boolean_value (f (S (j.succAbove i))) - 1)|) ''
            F.carrier))
  rcases empirical_rademacher_concentration with ⟨C, hC, h_integrable⟩
  have hspos : 0 < s := hm.trans_le hms
  have hs_integrable :=
    (h_integrable F P s (1 / 2) hspos (by norm_num) (by norm_num)).1
  have hm_integrable :=
    (h_integrable F P m (1 / 2) hm (by norm_num) (by norm_num)).1
  refine ⟨hs_integrable, hm_integrable, ?_⟩
  have hpres :
      ∀ {n : ℕ} (j : Fin (n + 1)),
        MeasurePreserving
          (fun S : Fin (n + 1) → X =>
            fun i : Fin n => S (j.succAbove i))
          (ProbabilityMeasure.pi
            (fun _ : Fin (n + 1) => P)).toMeasure
          (ProbabilityMeasure.pi (fun _ : Fin n => P)).toMeasure := by
    intro n j
    exact MeasureTheory.measurePreserving_snd.comp
      (MeasureTheory.measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => P.toMeasure) j)
  have hdelete :
      ∀ {n : ℕ}, 0 < n →
        ∀ j : Fin (n + 1),
          (∫ S : Fin (n + 1) → X,
              empirical_rademacher_complexity F
                (fun i : Fin n => S (j.succAbove i))
            ∂(ProbabilityMeasure.pi
              (fun _ : Fin (n + 1) => P)).toMeasure) =
            distributional_rademacher_complexity F n P := by
    intro n hn j
    have hnI :=
      (h_integrable F P n (1 / 2) hn
        (by norm_num) (by norm_num)).1
    have hp := hpres j
    change _ =
      ∫ T, empirical_rademacher_complexity F T
        ∂(ProbabilityMeasure.pi (fun _ : Fin n => P)).toMeasure
    rw [← hp.map_eq, MeasureTheory.integral_map hp.aemeasurable]
    exact hp.map_eq.symm ▸ hnI.aestronglyMeasurable
  have hstep :
      ∀ {n : ℕ}, 0 < n →
        distributional_rademacher_complexity F (n + 1) P ≤
          distributional_rademacher_complexity F n P := by
    intro n hn
    have hnI :=
      (h_integrable F P n (1 / 2) hn
        (by norm_num) (by norm_num)).1
    have hn1I :=
      (h_integrable F P (n + 1) (1 / 2)
        (by omega) (by norm_num) (by norm_num)).1
    have hdelI :
        ∀ j : Fin (n + 1),
          Integrable
            (fun S : Fin (n + 1) → X =>
              empirical_rademacher_complexity F
                (fun i : Fin n => S (j.succAbove i)))
            (ProbabilityMeasure.pi
              (fun _ : Fin (n + 1) => P)).toMeasure := by
      intro j
      simpa [Function.comp_def] using
        (hpres j).integrable_comp_of_integrable hnI
    have hsumI :
        Integrable
          (fun S : Fin (n + 1) → X =>
            ∑ j : Fin (n + 1),
              empirical_rademacher_complexity F
                (fun i : Fin n => S (j.succAbove i)))
          (ProbabilityMeasure.pi
            (fun _ : Fin (n + 1) => P)).toMeasure := by
      simpa using MeasureTheory.integrable_finsetSum Finset.univ
        (fun j hj => hdelI j)
    have havgI :
        Integrable
          (fun S : Fin (n + 1) → X =>
            ((n + 1 : ℕ) : ℝ)⁻¹ *
              ∑ j : Fin (n + 1),
                empirical_rademacher_complexity F
                  (fun i : Fin n => S (j.succAbove i)))
          (ProbabilityMeasure.pi
            (fun _ : Fin (n + 1) => P)).toMeasure :=
      hsumI.const_mul _
    calc
      distributional_rademacher_complexity F (n + 1) P ≤
          ∫ S : Fin (n + 1) → X,
            ((n + 1 : ℕ) : ℝ)⁻¹ *
              ∑ j : Fin (n + 1),
                empirical_rademacher_complexity F
                  (fun i : Fin n => S (j.succAbove i))
            ∂(ProbabilityMeasure.pi
              (fun _ : Fin (n + 1) => P)).toMeasure := by
        exact MeasureTheory.integral_mono hn1I havgI (hpoint hn)
      _ = ((n + 1 : ℕ) : ℝ)⁻¹ *
          ∑ j : Fin (n + 1),
            (∫ S : Fin (n + 1) → X,
              empirical_rademacher_complexity F
                (fun i : Fin n => S (j.succAbove i))
              ∂(ProbabilityMeasure.pi
                (fun _ : Fin (n + 1) => P)).toMeasure) := by
        rw [MeasureTheory.integral_const_mul]
        congr 1
        simpa using MeasureTheory.integral_finsetSum Finset.univ
          (fun j hj => hdelI j)
      _ = distributional_rademacher_complexity F n P := by
        simp_rw [hdelete hn]
        simp
        field_simp
  exact Nat.le_induction le_rfl
    (fun n hmn ih => (hstep (hm.trans_le hmn)).trans ih) s hms

@[blueprint "lem:sample-complexity-sqrt-control-local-testable-distribution-learning"
  (statement := /-- Let $K>0$, let $m$ be a positive integer, and let $\eta,\delta\in(0,1)$.  If
  $n=B_{K^2}(m,\eta,\delta)$, then $n>0$ and
  \[
    K\sqrt{\frac{1+\log(1/\delta)}{n}}\leq\eta.
  \] -/)
  (proof := /-- By \cref{def:sample-complexity-bound}, positivity of $m$ gives $n>0$, while the natural ceiling gives
  \[
    \frac{K^2(1+\log(1/\delta))}{\eta^2}\leq n.
  \]
  Since $0<\delta<1$, the logarithmic factor is positive.  Multiplication by the positive quantities $\eta^2$ and $n$, followed by taking nonnegative square roots, yields the claimed inequality. -/)
  (title := /-- Square-root control from the sample bound -/)
  (latexEnv := "lemma")]
lemma sample_complexity_sqrt_control_local_testable_distribution_learning
    (K : ℝ) (hK : 0 < K) (m : ℕ) (hm : 0 < m)
    (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let n := sample_complexity_bound (K ^ 2) m η δ
    0 < n ∧
      K * Real.sqrt ((1 + Real.log (1 / δ)) / n) ≤ η := by
  dsimp
  have hn : 0 < sample_complexity_bound (K ^ 2) m η δ := by
    unfold sample_complexity_bound
    omega
  refine ⟨hn, ?_⟩
  have hratio : 1 < 1 / δ := by
    exact (lt_div_iff₀ hδ).2 (by linarith)
  have hA : 0 < 1 + Real.log (1 / δ) := by
    have := Real.log_pos hratio
    linarith
  have hηsq : 0 < η ^ 2 := sq_pos_of_pos hη
  have hnR : (0 : ℝ) < sample_complexity_bound (K ^ 2) m η δ := by
    exact_mod_cast hn
  have hbase :
      K ^ 2 * (1 + Real.log (1 / δ)) / η ^ 2 ≤
        (sample_complexity_bound (K ^ 2) m η δ : ℝ) := by
    unfold sample_complexity_bound
    calc
      K ^ 2 * (1 + Real.log (1 / δ)) / η ^ 2 ≤
          (Nat.ceil (K ^ 2 * (1 + Real.log (1 / δ)) / η ^ 2) : ℝ) :=
        Nat.le_ceil _
      _ ≤ (m : ℝ) +
          Nat.ceil (K ^ 2 * (1 + Real.log (1 / δ)) / η ^ 2) := by
        have hmR : (0 : ℝ) ≤ m := by positivity
        linarith
      _ = ((m + Nat.ceil
          (K ^ 2 * (1 + Real.log (1 / δ)) / η ^ 2) : ℕ) : ℝ) := by
        norm_num
  have hmul :
      K ^ 2 * (1 + Real.log (1 / δ)) ≤
        η ^ 2 * sample_complexity_bound (K ^ 2) m η δ := by
    have := (div_le_iff₀ hηsq).1 hbase
    nlinarith
  have hq :
      0 ≤ (1 + Real.log (1 / δ)) /
        (sample_complexity_bound (K ^ 2) m η δ : ℝ) := by
    positivity
  have hsqrt_sq := Real.sq_sqrt hq
  have hsq :
      (K * Real.sqrt ((1 + Real.log (1 / δ)) /
        (sample_complexity_bound (K ^ 2) m η δ : ℝ))) ^ 2 ≤ η ^ 2 := by
    rw [mul_pow, hsqrt_sq]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hnR).2
    nlinarith
  have hsqrt_nonneg :
      0 ≤ K * Real.sqrt ((1 + Real.log (1 / δ)) /
        (sample_complexity_bound (K ^ 2) m η δ : ℝ)) := by
    positivity
  nlinarith

@[blueprint "lem:testable-distribution-learning"
  (statement := /-- There is a universal constant $C>0$ such that, for every standard Borel measurable space $\mathcal X$, every positive integer $m$, every $\eta,\delta\in(0,1)$, and every countable complemented measurable Boolean family $\mathcal F$ on $\mathcal X$, there exists an $(m,\eta,\eta/4,\delta)$-Rademacher testable distribution learner $L$ with the following additional properties.  For every probability measure $P$ on $\mathcal X$, the set of samples on which $L$ has a good run is measurable.  Moreover, the paired-sample decision rule obtained from $L$ at threshold $4\eta$ is measurable, and $L$ uses at most $B_C(m,\eta,\delta)$ samples. -/)
  (proof := /-- Let $C_{\mathrm c}>0$ and $C_{\mathrm g}>0$ be the universal
  constants supplied respectively by
  \cref{lem:empirical-rademacher-concentration} and
  \cref{lem:rademacher-generalization}.  Set
  $K=12C_{\mathrm c}+6C_{\mathrm g}$, $C=K^2$, and
  $s=B_C(m,\eta,\delta)$.  By
  \cref{lem:sample-complexity-sqrt-control-local-testable-distribution-learning},
  $s>0$ and
  [
    K\sqrt{\frac{1+\log(1/\delta)}s}\leq\eta.
  ]
  The identity
  $\log(1/(\delta/2))=\log2+\log(1/\delta)$ and the inequality
  $\log2\leq1$ imply
  [
    C_{\mathrm c}\sqrt{\frac{1+\log(1/(\delta/2))}s}\leq\frac\eta6,
    \qquad
    C_{\mathrm g}\sqrt{\frac{1+\log(1/(\delta/2))}s}\leq\frac\eta3.
  ]

  Define the learner using the interfaces in
  \cref{def:testable-distribution-learner, def:learner-good-run,
  def:is-rademacher-testable-distribution-learner}: on a sample $S$ of
  size $s$, reject when
  $\widehat{\mathcal R}(\mathcal F,S)>\eta/2$, and otherwise return the
  uniform empirical probability measure $\widehat P_S$.  Positivity of
  $s$ makes this empirical measure independent of the auxiliary law used
  in its definition.

  Fix a probability measure $P$.  Apply
  \cref{lem:empirical-rademacher-concentration} and
  \cref{lem:rademacher-generalization} with failure probability
  $\delta/2$, and denote their good events by $E_{mathrm c}$ and
  $E_{mathrm g}$.  If
  $\mathcal R_m(\mathcal F,P)\leq\eta/4$, then $m\leq s$ and
  \cref{lem:distributional-rademacher-monotone-sample-size} gives
  $\mathcal R_s(\mathcal F,P)\leq\eta/4$.  On $E_{mathrm c}$,
  [
    \widehat{\mathcal R}(\mathcal F,S)
      \leq\mathcal R_s(\mathcal F,P)+\eta/6<\eta/2,
  ]
  so the learner does not reject; on $E_{mathrm g}$,
  $d_{\mathcal F}(P,\widehat P_S)\leq\eta/4+\eta/3\leq\eta$.
  The complement of $E_{mathrm c}\cap E_{mathrm g}$ is contained in
  $E_{mathrm c}^{\mathrm c}\cup E_{mathrm g}^{\mathrm c}$, whose
  probability is at most $\delta$ by the union bound.  Hence a good run
  occurs with probability at least $1-\delta$ under the promise.

  Suppose now that the promise fails.  If
  $\mathcal R_s(\mathcal F,P)>2\eta/3$, then on $E_{mathrm c}$,
  [
    \widehat{\mathcal R}(\mathcal F,S)
      \geq\mathcal R_s(\mathcal F,P)-\eta/6>\eta/2,
  ]
  so the learner rejects, which is a good run off the promise.  If instead
  $\mathcal R_s(\mathcal F,P)\leq2\eta/3$, then on
  $E_{mathrm g}$ the returned empirical measure, whenever the learner
  does not reject, satisfies
  $d_{\mathcal F}(P,\widehat P_S)\leq2\eta/3+\eta/3=\eta$.
  Each of these events has probability at least
  $1-\delta/2\geq1-\delta$, proving the required guarantee for every
  $P$.

  Finally, \cref{lem:empirical-rademacher-measurable-bounded-local} and
  \cref{lem:empirical-fooling-distance-measurable-bounded-local-rademacher-generalization}
  show that every good-run event is a measurable union and intersection
  of the rejection and accuracy events.  For paired samples,
  \cref{lem:empirical-pair-fooling-distance-measurable-bounded-local-rademacher-generalization}
  makes the empirical-output distance measurable, so the Boolean rule in
  \cref{def:learner-equivalence-decision} at threshold $4\eta$ is
  measurable as well.  By construction the sample count is exactly
  $B_C(m,\eta,\delta)$. -/)
  (title := /-- Testable learning of bounded-Rademacher distributions -/)
  (latexEnv := "lemma")]
lemma testable_distribution_learning :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
        (F : boolean_distinguishing_family X)
        (m : ℕ) (η δ : ℝ),
        0 < m → 0 < η → η < 1 → 0 < δ → δ < 1 →
        ∃ L : testable_distribution_learner X,
          is_rademacher_testable_distribution_learner
            L F m η (η / 4) δ ∧
          (∀ P : ProbabilityMeasure X,
            MeasurableSet
              {S : Fin L.sampleCount → X |
                learner_good_run L F P m η (η / 4) S}) ∧
          Measurable (learner_equivalence_decision L F (4 * η)) ∧
          L.sampleCount ≤ sample_complexity_bound C m η δ := by
  obtain ⟨Cc, hCc, hconc⟩ := empirical_rademacher_concentration
  obtain ⟨Cg, hCg, hgen⟩ := rademacher_generalization
  let K := 12 * Cc + 6 * Cg
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨K ^ 2, sq_pos_of_pos hK, ?_⟩
  intro X inst1 inst2 F m η δ hm hη hη1 hδ hδ1
  let s := sample_complexity_bound (K ^ 2) m η δ
  have hsqrt := sample_complexity_sqrt_control_local_testable_distribution_learning K hK m hm η δ hη hδ hδ1
  change 0 < s ∧ K * Real.sqrt ((1 + Real.log (1 / δ)) / s) ≤ η at hsqrt
  have hs : 0 < s := hsqrt.1
  letI : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  let Q : (Fin s → X) → ProbabilityMeasure X :=
    fun S => ⟨((PMF.uniformOfFintype (Fin s)).map S).toMeasure, inferInstance⟩
  let L : testable_distribution_learner X :=
    { sampleCount := s
      run := fun S =>
        if empirical_rademacher_complexity F S > η / 2 then none else some (Q S) }
  have hδ2 : 0 < δ / 2 := by positivity
  have hδ2one : δ / 2 < 1 := by linarith
  have hsqrt_rescale :
      Real.sqrt ((1 + Real.log (1 / (δ / 2))) / s) ≤
        2 * Real.sqrt ((1 + Real.log (1 / δ)) / s) := by
    have hδne : δ ≠ 0 := ne_of_gt hδ
    have hlogδ : 0 ≤ Real.log (1 / δ) := by
      apply Real.log_nonneg
      exact (le_div_iff₀ hδ).2 (by linarith)
    have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    have hlog :
        Real.log (1 / (δ / 2)) = Real.log 2 + Real.log (1 / δ) := by
      calc
        Real.log (1 / (δ / 2)) = Real.log (2 / δ) := by
          congr 1
          field_simp
        _ = Real.log 2 - Real.log δ := Real.log_div (by norm_num) hδne
        _ = Real.log 2 + Real.log (1 / δ) := by
          rw [Real.log_div (by norm_num) hδne, Real.log_one]
          ring
    rw [hlog]
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · have hsR : (0 : ℝ) < s := by exact_mod_cast hs
      have hq : 0 ≤ (1 + Real.log (1 / δ)) / (s : ℝ) := by positivity
      rw [mul_pow, Real.sq_sqrt hq]
      apply (div_le_iff₀ hsR).2
      field_simp
      nlinarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hconc_error :
      Cc * Real.sqrt ((1 + Real.log (1 / (δ / 2))) / s) ≤ η / 6 := by
    calc
      Cc * Real.sqrt ((1 + Real.log (1 / (δ / 2))) / s) ≤
          Cc * (2 * Real.sqrt ((1 + Real.log (1 / δ)) / s)) := by
        gcongr
      _ ≤ η / 6 := by
        have hq := Real.sqrt_nonneg ((1 + Real.log (1 / δ)) / (s : ℝ))
        dsimp [K] at hsqrt
        nlinarith
  have hgen_error :
      Cg * Real.sqrt ((1 + Real.log (1 / (δ / 2))) / s) ≤ η / 3 := by
    calc
      Cg * Real.sqrt ((1 + Real.log (1 / (δ / 2))) / s) ≤
          Cg * (2 * Real.sqrt ((1 + Real.log (1 / δ)) / s)) := by
        gcongr
      _ ≤ η / 3 := by
        have hq := Real.sqrt_nonneg ((1 + Real.log (1 / δ)) / (s : ℝ))
        dsimp [K] at hsqrt
        nlinarith
  have hQeq (P : ProbabilityMeasure X) (S : Fin s → X) :
      Q S = empirical_probability_measure P S := by
    simp [Q, empirical_probability_measure, ne_of_gt hs]
  have hms : m ≤ s := by
    dsimp [s, sample_complexity_bound]
    omega
  refine ⟨L, ?_, ?_, ?_, by simp [L, s]⟩
  · intro P
    change sample_event_probability P s
      {S : Fin s → X | learner_good_run L F P m η (η / 4) S} ≥ 1 - δ
    let Ec : Set (Fin s → X) :=
      {S | |empirical_rademacher_complexity F S -
        distributional_rademacher_complexity F s P| ≤
          Cc * Real.sqrt ((1 + Real.log (1 / (δ / 2))) / s)}
    let Eg : Set (Fin s → X) :=
      {S | fooling_distance F P (empirical_probability_measure P S) ≤
        distributional_rademacher_complexity F s P +
          Cg * Real.sqrt ((1 + Real.log (1 / (δ / 2))) / s)}
    have hc := hconc F P s (δ / 2) hs hδ2 hδ2one
    have hg := hgen F P s (δ / 2) hs hδ2 hδ2one
    have hEcM : MeasurableSet Ec := by simpa [Ec] using hc.2.1
    have hEgM : MeasurableSet Eg := by simpa [Eg] using hg.2.1
    have hEcProb : sample_event_probability P s Ec ≥ 1 - δ / 2 := by
      simpa [Ec] using hc.2.2
    have hEgProb : sample_event_probability P s Eg ≥ 1 - δ / 2 := by
      simpa [Eg] using hg.2.2
    by_cases hP : rademacher_complexity_promise F m P (η / 4)
    · have hmono := distributional_rademacher_monotone_sample_size F P hm hms
      have hRs : distributional_rademacher_complexity F s P ≤ η / 4 :=
        hmono.2.2.trans hP
      have hsub : Ec ∩ Eg ⊆
          {S : Fin s → X | learner_good_run L F P m η (η / 4) S} := by
        intro S hS
        have hcS0 : |empirical_rademacher_complexity F S -
            distributional_rademacher_complexity F s P| ≤
              Cc * Real.sqrt ((1 + Real.log (1 / (δ / 2))) / s) := by
          simpa [Ec] using hS.1
        have hcS : |empirical_rademacher_complexity F S -
            distributional_rademacher_complexity F s P| ≤ η / 6 :=
          hcS0.trans hconc_error
        have hgS0 : fooling_distance F P (empirical_probability_measure P S) ≤
            distributional_rademacher_complexity F s P +
              Cg * Real.sqrt ((1 + Real.log (1 / (δ / 2))) / s) := by
          simpa [Eg] using hS.2
        have hgS : fooling_distance F P (empirical_probability_measure P S) ≤
            distributional_rademacher_complexity F s P + η / 3 :=
          le_trans hgS0 (by nlinarith [hgen_error])
        have hrad :
            empirical_rademacher_complexity F S ≤ η / 2 := by
          have hupper := le_trans
            (le_abs_self (empirical_rademacher_complexity F S -
              distributional_rademacher_complexity F s P)) hcS
          nlinarith
        have hnot : ¬ empirical_rademacher_complexity F S > η / 2 :=
          not_lt_of_ge hrad
        simp [learner_good_run, L, hnot, hQeq P S]
        nlinarith
      let μ := (ProbabilityMeasure.pi (fun _ : Fin s => P)).toMeasure
      have hEcBad : μ.real Ecᶜ ≤ δ / 2 := by
        have hcomp := MeasureTheory.probReal_compl_eq_one_sub
          (μ := μ) hEcM
        change μ.real Ec ≥ 1 - δ / 2 at hEcProb
        linarith
      have hEgBad : μ.real Egᶜ ≤ δ / 2 := by
        have hcomp := MeasureTheory.probReal_compl_eq_one_sub
          (μ := μ) hEgM
        change μ.real Eg ≥ 1 - δ / 2 at hEgProb
        linarith
      have hbad : μ.real ((Ec ∩ Eg)ᶜ) ≤ δ := by
        rw [Set.compl_inter]
        calc
          μ.real (Ecᶜ ∪ Egᶜ) ≤ μ.real Ecᶜ + μ.real Egᶜ :=
            measureReal_union_le _ _
          _ ≤ δ / 2 + δ / 2 := add_le_add hEcBad hEgBad
          _ = δ := by ring
      have hinter : μ.real (Ec ∩ Eg) ≥ 1 - δ := by
        have hcomp := MeasureTheory.probReal_compl_eq_one_sub
          (μ := μ) (hEcM.inter hEgM)
        linarith
      calc
        sample_event_probability P s
            {S : Fin s → X | learner_good_run L F P m η (η / 4) S} ≥
            μ.real (Ec ∩ Eg) := by
          exact measureReal_mono hsub
        _ ≥ 1 - δ := hinter
    · by_cases hhigh :
          2 * η / 3 < distributional_rademacher_complexity F s P
      · have hsub : Ec ⊆
            {S : Fin s → X | learner_good_run L F P m η (η / 4) S} := by
          intro S hS
          have hcS0 : |empirical_rademacher_complexity F S -
              distributional_rademacher_complexity F s P| ≤
                Cc * Real.sqrt ((1 + Real.log (1 / (δ / 2))) / s) := by
            simpa [Ec] using hS
          have hcS : |empirical_rademacher_complexity F S -
              distributional_rademacher_complexity F s P| ≤ η / 6 :=
            hcS0.trans hconc_error
          have hlower := neg_le_of_abs_le hcS
          have hrej : empirical_rademacher_complexity F S > η / 2 := by
            nlinarith
          simp [learner_good_run, L, hrej, hP]
        calc
          sample_event_probability P s
              {S : Fin s → X | learner_good_run L F P m η (η / 4) S} ≥
              sample_event_probability P s Ec := measureReal_mono hsub
          _ ≥ 1 - δ / 2 := hEcProb
          _ ≥ 1 - δ := by linarith
      · have hRs : distributional_rademacher_complexity F s P ≤ 2 * η / 3 :=
          le_of_not_gt hhigh
        have hsub : Eg ⊆
            {S : Fin s → X | learner_good_run L F P m η (η / 4) S} := by
          intro S hS
          have hgS0 : fooling_distance F P (empirical_probability_measure P S) ≤
              distributional_rademacher_complexity F s P +
                Cg * Real.sqrt ((1 + Real.log (1 / (δ / 2))) / s) := by
            simpa [Eg] using hS
          have hgS : fooling_distance F P (empirical_probability_measure P S) ≤
              distributional_rademacher_complexity F s P + η / 3 :=
            le_trans hgS0 (by nlinarith [hgen_error])
          by_cases hrej : empirical_rademacher_complexity F S > η / 2
          · simp [learner_good_run, L, hrej, hP]
          · simp [learner_good_run, L, hrej, hQeq P S]
            nlinarith
        calc
          sample_event_probability P s
              {S : Fin s → X | learner_good_run L F P m η (η / 4) S} ≥
              sample_event_probability P s Eg := measureReal_mono hsub
          _ ≥ 1 - δ / 2 := hEgProb
          _ ≥ 1 - δ := by linarith
  · intro P
    change MeasurableSet
      {S : Fin s → X | learner_good_run L F P m η (η / 4) S}
    have hR : Measurable
        (fun S : Fin s → X => empirical_rademacher_complexity F S) :=
      (empirical_rademacher_measurable_bounded_local F hs).1
    have hD0 : Measurable (fun S : Fin s → X =>
        fooling_distance F P (empirical_probability_measure P S)) :=
      (empirical_fooling_distance_measurable_bounded_local_rademacher_generalization
        F P hs).1
    have hD : Measurable (fun S : Fin s → X => fooling_distance F P (Q S)) := by
      convert hD0 using 1
      funext S
      rw [hQeq P S]
    have hrej : MeasurableSet
        {S : Fin s → X | empirical_rademacher_complexity F S > η / 2} :=
      measurableSet_lt measurable_const hR
    have hacc : MeasurableSet
        {S : Fin s → X | empirical_rademacher_complexity F S ≤ η / 2} :=
      measurableSet_le hR measurable_const
    have hgood : MeasurableSet
        {S : Fin s → X | fooling_distance F P (Q S) ≤ η} :=
      measurableSet_le hD measurable_const
    by_cases hP : rademacher_complexity_promise F m P (η / 4)
    · convert hacc.inter hgood using 1
      ext S
      by_cases hS : empirical_rademacher_complexity F S > η / 2
      · simp [learner_good_run, L, hP, hS, not_le_of_gt hS]
      · have hS' : empirical_rademacher_complexity F S ≤ η / 2 :=
          le_of_not_gt hS
        simp [learner_good_run, L, hP, hS, hS']
    · convert hrej.union (hacc.inter hgood) using 1
      ext S
      by_cases hS : empirical_rademacher_complexity F S > η / 2
      · simp [learner_good_run, L, hP, hS, not_le_of_gt hS]
      · have hS' : empirical_rademacher_complexity F S ≤ η / 2 :=
          le_of_not_gt hS
        simp [learner_good_run, L, hP, hS, hS']
  · classical
    by_cases hX : Nonempty X
    · let x0 : X := Classical.choice hX
      let P0 : ProbabilityMeasure X := Q (fun _ => x0)
      have hR : Measurable
          (fun S : Fin s → X => empirical_rademacher_complexity F S) :=
        (empirical_rademacher_measurable_bounded_local F hs).1
      have hG0 : Measurable (fun p : (Fin s → X) × (Fin s → X) =>
          fooling_distance F (empirical_probability_measure P0 p.1)
            (empirical_probability_measure P0 p.2)) :=
        (empirical_pair_fooling_distance_measurable_bounded_local_rademacher_generalization
          F P0 hs).1
      have hG : Measurable (fun p : (Fin s → X) × (Fin s → X) =>
          fooling_distance F (Q p.1) (Q p.2)) := by
        convert hG0 using 1
        funext p
        rw [hQeq P0 p.1, hQeq P0 p.2]
      have hrej1 : MeasurableSet
          {p : (Fin s → X) × (Fin s → X) |
            empirical_rademacher_complexity F p.1 > η / 2} :=
        measurableSet_lt measurable_const (hR.comp measurable_fst)
      have hrej2 : MeasurableSet
          {p : (Fin s → X) × (Fin s → X) |
            empirical_rademacher_complexity F p.2 > η / 2} :=
        measurableSet_lt measurable_const (hR.comp measurable_snd)
      have hclose : MeasurableSet
          {p : (Fin s → X) × (Fin s → X) |
            fooling_distance F (Q p.1) (Q p.2) ≤ (4 * η) / 2} :=
        measurableSet_le hG measurable_const
      have hdec : Measurable (fun p : (Fin s → X) × (Fin s → X) =>
          if empirical_rademacher_complexity F p.1 > η / 2 then false
          else if empirical_rademacher_complexity F p.2 > η / 2 then false
          else if fooling_distance F (Q p.1) (Q p.2) ≤ (4 * η) / 2
            then true else false) :=
        Measurable.ite hrej1 measurable_const
          (Measurable.ite hrej2 measurable_const
            (Measurable.ite hclose measurable_const measurable_const))
      have heq : learner_equivalence_decision L F (4 * η) =
          (fun p : (Fin s → X) × (Fin s → X) =>
            if empirical_rademacher_complexity F p.1 > η / 2 then false
            else if empirical_rademacher_complexity F p.2 > η / 2 then false
            else if fooling_distance F (Q p.1) (Q p.2) ≤ (4 * η) / 2
              then true else false) := by
        funext p
        by_cases h1 : empirical_rademacher_complexity F p.1 > η / 2
        · simp [learner_equivalence_decision, L, h1]
        · by_cases h2 : empirical_rademacher_complexity F p.2 > η / 2
          · simp [learner_equivalence_decision, L, h1, h2]
          · simp [learner_equivalence_decision, L, h1, h2]
      rw [heq]
      exact hdec
    · letI : IsEmpty X := ⟨fun x => hX ⟨x⟩⟩
      change Measurable (fun p : (Fin s → X) × (Fin s → X) =>
        learner_equivalence_decision L F (4 * η) p)
      exact measurable_of_empty _

@[blueprint "lem:fooling-distance-triangle"
  (statement := /-- Let $\mathcal X$ be a measurable space, let $\mathcal F$ be a family of measurable functions $\mathcal X\to\{0,1\}$ closed under pointwise complementation, and let $P,Q,R$ be probability measures on $\mathcal X$.  Then
  \[
    d_{\mathcal F}(P,R)
      \leq d_{\mathcal F}(P,Q)+d_{\mathcal F}(Q,R).
  \] -/)
  (proof := /-- By \cref{def:fooling-distance}, the distance is the supremum of the absolute differences of Boolean expectations.  For every $f\in\mathcal F$ and every probability measure $S$, measurability of $f$ and the pointwise bounds $0\leq f\leq 1$ imply that $f$ is integrable and that $0\leq\mathbb E_S f\leq 1$.  Hence each set whose supremum defines a fooling distance is bounded above by $1$.  If $\mathcal F$ is empty, all three defining sets are empty and their stipulated suprema are $0$.  Otherwise, fix $f\in\mathcal F$.  The triangle inequality in $\mathbb R$ gives
  \[
  |\mathbb E_P f-\mathbb E_R f|
   \leq |\mathbb E_P f-\mathbb E_Q f|
      +|\mathbb E_Q f-\mathbb E_R f|.
  \]
  Boundedness and the defining property of the supremum bound the two terms on the right by $d_{\mathcal F}(P,Q)$ and $d_{\mathcal F}(Q,R)$, respectively.  Thus every element of the set defining $d_{\mathcal F}(P,R)$ is at most their sum; the defining property of the supremum yields the asserted inequality. -/)
  (title := /-- Triangle inequality for fooling distance -/)
  (latexEnv := "lemma")]
lemma fooling_distance_triangle
    {X : Type*} [MeasurableSpace X]
    (F : boolean_distinguishing_family X)
    (P Q R : ProbabilityMeasure X) :
    fooling_distance F P R ≤
      fooling_distance F P Q + fooling_distance F Q R := by
  have h_integrable (S : ProbabilityMeasure X) {f : X → Bool}
      (hf : f ∈ F.carrier) :
      Integrable (fun x => boolean_value (f x)) S.toMeasure := by
    refine Integrable.of_bound ?_ 1 ?_
    · exact ((measurable_of_finite boolean_value).comp
        (F.measurable f hf)).aestronglyMeasurable
    · filter_upwards with x
      cases f x <;> norm_num [boolean_value]
  have h_integral_bounds (S : ProbabilityMeasure X) {f : X → Bool}
      (hf : f ∈ F.carrier) :
      (∫ x, boolean_value (f x) ∂S.toMeasure) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact integral_nonneg (fun x => by
        cases f x <;> norm_num [boolean_value])
    · calc
        (∫ x, boolean_value (f x) ∂S.toMeasure) ≤
            ∫ _x, (1 : ℝ) ∂S.toMeasure :=
          integral_mono (h_integrable S hf) (integrable_const 1)
            (fun x => by cases f x <;> norm_num [boolean_value])
        _ = 1 := by simp
  have h_abs_le_one (S T : ProbabilityMeasure X) {f : X → Bool}
      (hf : f ∈ F.carrier) :
      |(∫ x, boolean_value (f x) ∂S.toMeasure) -
        (∫ x, boolean_value (f x) ∂T.toMeasure)| ≤ 1 := by
    rcases h_integral_bounds S hf with ⟨hS0, hS1⟩
    rcases h_integral_bounds T hf with ⟨hT0, hT1⟩
    rw [abs_le]
    constructor <;> linarith
  have h_bdd (S T : ProbabilityMeasure X) :
      BddAbove ((fun f : X → Bool =>
        |(∫ x, boolean_value (f x) ∂S.toMeasure) -
          (∫ x, boolean_value (f x) ∂T.toMeasure)|) '' F.carrier) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨f, hf, rfl⟩
    exact h_abs_le_one S T hf
  by_cases hF : F.carrier.Nonempty
  · unfold fooling_distance
    obtain ⟨f₀, hf₀⟩ := hF
    apply csSup_le
    · exact ⟨_, ⟨f₀, hf₀, rfl⟩⟩
    · rintro _ ⟨f, hf, rfl⟩
      calc
        |(∫ x, boolean_value (f x) ∂P.toMeasure) -
            (∫ x, boolean_value (f x) ∂R.toMeasure)| ≤
            |(∫ x, boolean_value (f x) ∂P.toMeasure) -
              (∫ x, boolean_value (f x) ∂Q.toMeasure)| +
            |(∫ x, boolean_value (f x) ∂Q.toMeasure) -
              (∫ x, boolean_value (f x) ∂R.toMeasure)| :=
          abs_sub_le _ _ _
        _ ≤ sSup ((fun f : X → Bool =>
              |(∫ x, boolean_value (f x) ∂P.toMeasure) -
                (∫ x, boolean_value (f x) ∂Q.toMeasure)|) '' F.carrier) +
            sSup ((fun f : X → Bool =>
              |(∫ x, boolean_value (f x) ∂Q.toMeasure) -
                (∫ x, boolean_value (f x) ∂R.toMeasure)|) '' F.carrier) :=
          add_le_add
            (le_csSup (h_bdd P Q) ⟨f, hf, rfl⟩)
            (le_csSup (h_bdd Q R) ⟨f, hf, rfl⟩)
  · have h_empty : F.carrier = ∅ := Set.not_nonempty_iff_eq_empty.mp hF
    simp [fooling_distance, h_empty]

@[blueprint "lem:fooling-distance-reverse-triangle"
  (statement := /-- Let $\mathcal X$ be a measurable space, let $\mathcal F$ be a family of measurable Boolean functions on $\mathcal X$ closed under pointwise complementation, and let $P,Q,\widehat P,\widehat Q$ be probability measures on $\mathcal X$.  Then
  \[
  d_{\mathcal F}(P,Q)
    -d_{\mathcal F}(P,\widehat P)
    -d_{\mathcal F}(Q,\widehat Q)
    \leq d_{\mathcal F}(\widehat P,\widehat Q).
  \] -/)
  (proof := /-- Use the distance of \cref{def:fooling-distance}.  Apply \cref{lem:fooling-distance-triangle} first through $\widehat P$ and then through $\widehat Q$ to obtain
  \[
    d_{\mathcal F}(P,Q)
      \leq d_{\mathcal F}(P,\widehat P)
       +d_{\mathcal F}(\widehat P,\widehat Q)
       +d_{\mathcal F}(\widehat Q,Q).
  \]
  Symmetry of the absolute difference in the definition of $d_{\mathcal F}$ identifies the last term with
  $d_{\mathcal F}(Q,\widehat Q)$.  Rearrangement yields the result. -/)
  (title := /-- Reverse triangle inequality for fooling distance -/)
  (latexEnv := "lemma")]
lemma fooling_distance_reverse_triangle
    {X : Type*} [MeasurableSpace X]
    (F : boolean_distinguishing_family X)
    (P Q P_hat Q_hat : ProbabilityMeasure X) :
    fooling_distance F P Q -
        fooling_distance F P P_hat -
        fooling_distance F Q Q_hat ≤
      fooling_distance F P_hat Q_hat := by
  have h_first := fooling_distance_triangle F P P_hat Q
  have h_second := fooling_distance_triangle F P_hat Q_hat Q
  have h_symm :
      fooling_distance F Q_hat Q = fooling_distance F Q Q_hat := by
    simp only [fooling_distance, abs_sub_comm]
  rw [h_symm] at h_second
  linarith

@[blueprint "lem:learner-equivalence-completeness"
  (statement := /-- Let $\mathcal X$ be a measurable space, let $\mathcal F$ be a Boolean distinguishing family on $\mathcal X$, let $L$ be a testable distribution learner, let $m\in\mathbb N$, and let $\epsilon,\delta\in\mathbb R$.  Suppose that $L$ is an
  $(m,\epsilon/4,\epsilon/16,\delta/2)$-Rademacher testable distribution learner against $\mathcal F$ and that its paired-sample decision rule is measurable.  For all probability measures $P,Q$ on $\mathcal X$, if
  $\mathcal R_m(\mathcal F,P)\leq\epsilon/16$ or
  $\mathcal R_m(\mathcal F,Q)\leq\epsilon/16$, and if $P=Q$, then the measurable tester constructed from $L$ accepts $(P,Q)$ with probability at least $1-\delta$. -/)
  (proof := /-- Assume $P=Q$ and replace $Q$ by $P$.  The disjunctive hypothesis of
  \cref{def:rademacher-complexity-promise} then yields
  $\mathcal R_m(\mathcal F,P)\leq\epsilon/16$.  Let $\mu=P^{L.\mathrm{sampleCount}}$, let $G$ be the set of good samples from
  \cref{def:learner-good-run}, and let $A$ be the measurable acceptance event from
  \cref{def:measurable-decision-event}.  By
  \cref{def:is-rademacher-testable-distribution-learner, def:sample-event-probability},
  the real value $g$ of $\mu(G)$ satisfies
  $g\geq1-\delta/2$.

  If $S,T\in G$, the Rademacher promise rules out rejection in either good run.  Hence $L(S)=\widehat P$ and $L(T)=\widehat Q$ for probability measures satisfying
  $d_{\mathcal F}(P,\widehat P)\leq\epsilon/4$ and
  $d_{\mathcal F}(P,\widehat Q)\leq\epsilon/4$.  Symmetry from
  \cref{def:fooling-distance} and \cref{lem:fooling-distance-triangle} give
  \[
    d_{\mathcal F}(\widehat P,\widehat Q)
      \leq d_{\mathcal F}(\widehat P,P)
        +d_{\mathcal F}(P,\widehat Q)
      \leq\epsilon/2.
  \]
  Thus \cref{def:learner-equivalence-decision} returns true, so $G\times G\subseteq A$.

  The set $G$ is not assumed measurable, so we use measurable sections rather than a union bound.  For $S$ let $A_S=\{T:(S,T)\in A\}$ and set
  $H=\{S:\mu(G)\leq\mu(A_S)\}$.  Measurability of $A$ makes $H$ measurable.  The inclusion $G\times G\subseteq A$ implies $G\subseteq H$, whence
  $\mu(G)\leq\mu(H)$.  The product-measure section formula and monotonicity therefore give
  \[
    (\mu\times\mu)(A)
      =\int\mu(A_S)\,d\mu(S)
      \geq\int_H\mu(G)\,d\mu(S)
      =\mu(G)\mu(H)
      \geq\mu(G)^2.
  \]
  By \cref{def:equivalence-tester-from-learner, def:equivalence-acceptance-probability}, the left-hand side is the acceptance probability.  If $\delta\geq1$, its nonnegativity proves the claim.  If $\delta<1$, then $g\geq1-\delta/2\geq0$, and hence
  $g^2\geq(1-\delta/2)^2\geq1-\delta$.  This proves the required bound. -/)
  (title := /-- Completeness of the learner-based equivalence tester -/)
  (latexEnv := "lemma")]
lemma learner_equivalence_completeness
    {X : Type*} [MeasurableSpace X]
    (F : boolean_distinguishing_family X)
    (L : testable_distribution_learner X)
    (m : ℕ) (ε δ : ℝ)
    (hL : is_rademacher_testable_distribution_learner
      L F m (ε / 4) (ε / 16) (δ / 2))
    (h_decide : Measurable (learner_equivalence_decision L F ε)) :
    ∀ P Q : ProbabilityMeasure X,
      (rademacher_complexity_promise F m P (ε / 16) ∨
        rademacher_complexity_promise F m Q (ε / 16)) →
      P = Q →
      equivalence_acceptance_probability
        (equivalence_tester_from_learner L F ε h_decide) P Q ≥ 1 - δ := by
  intro P Q hpromise hPQ
  subst Q
  have hP : rademacher_complexity_promise F m P (ε / 16) :=
    hpromise.elim id id
  let μ :=
    (ProbabilityMeasure.pi (fun _ : Fin L.sampleCount => P)).toMeasure
  let G : Set (Fin L.sampleCount → X) :=
    {S | learner_good_run L F P m (ε / 4) (ε / 16) S}
  let A : Set ((Fin L.sampleCount → X) × (Fin L.sampleCount → X)) :=
    measurable_decision_event (learner_equivalence_decision L F ε)
      h_decide true
  have hA : MeasurableSet A :=
    (measurable_decision_event (learner_equivalence_decision L F ε)
      h_decide true).property
  have hgood : (μ G).toReal ≥ 1 - δ / 2 := by
    have h := hL P
    change (μ G).toReal ≥ 1 - δ / 2 at h
    exact h
  have h_pair_good : G ×ˢ G ⊆ A := by
    rintro ⟨S, T⟩ ⟨hS, hT⟩
    rcases hLS : L.run S with _ | P_hat
    · exfalso
      simpa [G, learner_good_run, hLS, hP] using hS
    rcases hLT : L.run T with _ | Q_hat
    · exfalso
      simpa [G, learner_good_run, hLT, hP] using hT
    have hSP : fooling_distance F P P_hat ≤ ε / 4 := by
      simpa [G, learner_good_run, hLS] using hS
    have hTQ : fooling_distance F P Q_hat ≤ ε / 4 := by
      simpa [G, learner_good_run, hLT] using hT
    have hSP' : fooling_distance F P_hat P ≤ ε / 4 := by
      simpa [fooling_distance, abs_sub_comm] using hSP
    have hdist : fooling_distance F P_hat Q_hat ≤ ε / 2 := by
      calc
        fooling_distance F P_hat Q_hat ≤
            fooling_distance F P_hat P + fooling_distance F P Q_hat :=
          fooling_distance_triangle F P_hat P Q_hat
        _ ≤ ε / 2 := by linarith
    change learner_equivalence_decision L F ε (S, T) = true
    simp [learner_equivalence_decision, hLS, hLT, hdist]
  let H : Set (Fin L.sampleCount → X) :=
    {S | μ G ≤ μ (Prod.mk S ⁻¹' A)}
  have hH : MeasurableSet H := by
    exact measurableSet_le measurable_const
      (measurable_measure_prodMk_left hA)
  have hGH : μ G ≤ μ H := by
    apply measure_mono
    intro S hS
    change μ G ≤ μ (Prod.mk S ⁻¹' A)
    apply measure_mono
    intro T hT
    exact h_pair_good ⟨hS, hT⟩
  have hprod : μ G * μ G ≤ μ.prod μ A := by
    rw [MeasureTheory.Measure.prod_apply hA]
    calc
      μ G * μ G ≤ μ G * μ H := by gcongr
      _ = ∫⁻ S, H.indicator (fun _ => μ G) S ∂μ := by
        symm
        exact MeasureTheory.lintegral_indicator_const hH (μ G)
      _ ≤ ∫⁻ S, μ (Prod.mk S ⁻¹' A) ∂μ := by
        apply MeasureTheory.lintegral_mono
        intro S
        by_cases hS : S ∈ H
        · have hmem := hS
          change μ G ≤ μ (Prod.mk S ⁻¹' A) at hS
          simpa [hmem] using hS
        · simp [hS]
  have hμG : μ G ≠ ⊤ := measure_ne_top μ G
  have hμprod : μ.prod μ A ≠ ⊤ := measure_ne_top (μ.prod μ) A
  have hprod_real :
      (μ G).toReal * (μ G).toReal ≤ (μ.prod μ A).toReal := by
    rw [← ENNReal.toReal_mul]
    exact (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top hμG hμG) hμprod).2 hprod
  change (μ.prod μ).real A ≥ 1 - δ
  by_cases hδ : 1 ≤ δ
  · have hnonneg : 0 ≤ (μ.prod μ A).toReal := ENNReal.toReal_nonneg
    simpa [Measure.real] using (show (μ.prod μ A).toReal ≥ 1 - δ by linarith)
  · have hbase : 0 ≤ 1 - δ / 2 := by linarith
    have hμG_nonneg : 0 ≤ (μ G).toReal := ENNReal.toReal_nonneg
    have hmul :
        0 ≤ ((μ G).toReal - (1 - δ / 2)) *
          ((μ G).toReal + (1 - δ / 2)) :=
      mul_nonneg (sub_nonneg.mpr hgood) (add_nonneg hμG_nonneg hbase)
    have hbound : 1 - δ ≤ (μ.prod μ A).toReal := by
      nlinarith [sq_nonneg δ]
    simpa [Measure.real] using hbound

@[blueprint "lem:learner-equivalence-soundness"
  (statement := /-- Let $\mathcal X$ be a measurable space, let $\mathcal F$ be a Boolean distinguishing family on $\mathcal X$, let $L$ be a testable distribution learner, let $m\in\mathbb N$, and let $\epsilon,\delta\in\mathbb R$.  Suppose that $L$ is an
  $(m,\epsilon/4,\epsilon/16,\delta/2)$-Rademacher testable distribution learner against $\mathcal F$ and that its paired-sample decision rule is measurable.  Then, for all probability measures $P,Q$ on $\mathcal X$, if $d_{\mathcal F}(P,Q)>\epsilon$, the equivalence tester constructed from $L$ rejects $(P,Q)$ with probability at least $1-\delta$. -/)
  (proof := /-- Let $\mu$ and $\nu$ be the product sample laws induced by $P$ and $Q$, and let $G_P$ and $G_Q$ be their respective good-run sets from \cref{def:learner-good-run}.  The guarantee in \cref{def:is-rademacher-testable-distribution-learner} gives
  $\mu(G_P),\nu(G_Q)\geq 1-\delta/2$.  Let $A$ be the measurable false-decision event supplied by \cref{def:measurable-decision-event} for the rule in \cref{def:learner-equivalence-decision}.  We claim that $G_P\times G_Q\subseteq A$.  If either learner execution returns no measure, the rule returns false.  Otherwise, for its returned measures $\widehat P,\widehat Q$, the definition of the good-run sets gives
  $d_{\mathcal F}(P,\widehat P),d_{\mathcal F}(Q,\widehat Q)\leq\epsilon/4$, and \cref{lem:fooling-distance-reverse-triangle} gives
  \[
  d_{\mathcal F}(\widehat P,\widehat Q)
    \geq d_{\mathcal F}(P,Q)
       -d_{\mathcal F}(P,\widehat P)
       -d_{\mathcal F}(Q,\widehat Q)
    >\epsilon/2.
  \]
  Hence \cref{def:learner-equivalence-decision} again returns false, proving the claimed inclusion.

  For each first sample $S$, write $A_S=\{T:(S,T)\in A\}$ and set
  $K=\{S:\nu(G_Q)\leq\nu(A_S)\}$.  Measurability of $A$ makes $K$ measurable, while the inclusion above gives $G_P\subseteq K$.  The product-measure formula and monotonicity therefore yield
  \[
    \mu(G_P)\nu(G_Q)
      \leq \int_K \nu(G_Q)\,d\mu
      \leq \int \nu(A_S)\,d\mu
      =(\mu\times\nu)(A).
  \]
  All these measures are finite, so the same inequality holds for their real values.  If $\delta\geq1$, nonnegativity of $(\mu\times\nu)(A)$ proves the desired bound.  If $\delta<1$, then $1-\delta/2\geq0$, and the two learner bounds imply
  $(\mu\times\nu)(A)\geq(1-\delta/2)^2\geq1-\delta$.  By \cref{def:equivalence-tester-from-learner, def:equivalence-rejection-probability}, $(\mu\times\nu)(A)$ is the required rejection probability. -/)
  (title := /-- Soundness of the learner-based equivalence tester -/)
  (latexEnv := "lemma")]
lemma learner_equivalence_soundness
    {X : Type*} [MeasurableSpace X]
    (F : boolean_distinguishing_family X)
    (L : testable_distribution_learner X)
    (m : ℕ) (ε δ : ℝ)
    (hL : is_rademacher_testable_distribution_learner
      L F m (ε / 4) (ε / 16) (δ / 2))
    (h_decide : Measurable (learner_equivalence_decision L F ε)) :
    ∀ P Q : ProbabilityMeasure X,
      fooling_distance F P Q > ε →
      equivalence_rejection_probability
        (equivalence_tester_from_learner L F ε h_decide) P Q ≥ 1 - δ := by
  intro P Q hPQ
  let μ :=
    (ProbabilityMeasure.pi (fun _ : Fin L.sampleCount => P)).toMeasure
  let ν :=
    (ProbabilityMeasure.pi (fun _ : Fin L.sampleCount => Q)).toMeasure
  let G : Set (Fin L.sampleCount → X) :=
    {S | learner_good_run L F P m (ε / 4) (ε / 16) S}
  let H : Set (Fin L.sampleCount → X) :=
    {S | learner_good_run L F Q m (ε / 4) (ε / 16) S}
  let A : Set ((Fin L.sampleCount → X) × (Fin L.sampleCount → X)) :=
    measurable_decision_event (learner_equivalence_decision L F ε)
      h_decide false
  have hA : MeasurableSet A :=
    (measurable_decision_event (learner_equivalence_decision L F ε)
      h_decide false).property
  have hgoodP : (μ G).toReal ≥ 1 - δ / 2 := by
    have h := hL P
    change (μ G).toReal ≥ 1 - δ / 2 at h
    exact h
  have hgoodQ : (ν H).toReal ≥ 1 - δ / 2 := by
    have h := hL Q
    change (ν H).toReal ≥ 1 - δ / 2 at h
    exact h
  have h_pair_good : G ×ˢ H ⊆ A := by
    rintro ⟨S, T⟩ ⟨hS, hT⟩
    rcases hLS : L.run S with _ | P_hat
    · change learner_equivalence_decision L F ε (S, T) = false
      simp [learner_equivalence_decision, hLS]
    rcases hLT : L.run T with _ | Q_hat
    · change learner_equivalence_decision L F ε (S, T) = false
      simp [learner_equivalence_decision, hLS, hLT]
    have hSP : fooling_distance F P P_hat ≤ ε / 4 := by
      simpa [G, learner_good_run, hLS] using hS
    have hTQ : fooling_distance F Q Q_hat ≤ ε / 4 := by
      simpa [H, learner_good_run, hLT] using hT
    have hdist : fooling_distance F P_hat Q_hat > ε / 2 := by
      have hreverse := fooling_distance_reverse_triangle F P Q P_hat Q_hat
      linarith
    change learner_equivalence_decision L F ε (S, T) = false
    simp [learner_equivalence_decision, hLS, hLT, not_le.mpr hdist]
  let K : Set (Fin L.sampleCount → X) :=
    {S | ν H ≤ ν (Prod.mk S ⁻¹' A)}
  have hK : MeasurableSet K := by
    exact measurableSet_le measurable_const
      (measurable_measure_prodMk_left hA)
  have hGK : μ G ≤ μ K := by
    apply measure_mono
    intro S hS
    change ν H ≤ ν (Prod.mk S ⁻¹' A)
    apply measure_mono
    intro T hT
    exact h_pair_good ⟨hS, hT⟩
  have hprod : μ G * ν H ≤ μ.prod ν A := by
    rw [MeasureTheory.Measure.prod_apply hA]
    calc
      μ G * ν H ≤ μ K * ν H := by gcongr
      _ = ∫⁻ S, K.indicator (fun _ => ν H) S ∂μ := by
        symm
        simpa [mul_comm] using
          (MeasureTheory.lintegral_indicator_const hK (ν H))
      _ ≤ ∫⁻ S, ν (Prod.mk S ⁻¹' A) ∂μ := by
        apply MeasureTheory.lintegral_mono
        intro S
        by_cases hS : S ∈ K
        · have hmem := hS
          change ν H ≤ ν (Prod.mk S ⁻¹' A) at hS
          simpa [hmem] using hS
        · simp [hS]
  have hμG : μ G ≠ ⊤ := measure_ne_top μ G
  have hνH : ν H ≠ ⊤ := measure_ne_top ν H
  have hμprod : μ.prod ν A ≠ ⊤ := measure_ne_top (μ.prod ν) A
  have hprod_real :
      (μ G).toReal * (ν H).toReal ≤ (μ.prod ν A).toReal := by
    rw [← ENNReal.toReal_mul]
    exact (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top hμG hνH) hμprod).2 hprod
  change (μ.prod ν).real A ≥ 1 - δ
  by_cases hδ : 1 ≤ δ
  · have hnonneg : 0 ≤ (μ.prod ν A).toReal := ENNReal.toReal_nonneg
    simpa [Measure.real] using (show (μ.prod ν A).toReal ≥ 1 - δ by linarith)
  · have hbase : 0 ≤ 1 - δ / 2 := by linarith
    have hmul :
        0 ≤ ((μ G).toReal - (1 - δ / 2)) *
          ((ν H).toReal - (1 - δ / 2)) :=
      mul_nonneg (sub_nonneg.mpr hgoodP) (sub_nonneg.mpr hgoodQ)
    have hbound : 1 - δ ≤ (μ.prod ν A).toReal := by
      nlinarith [sq_nonneg δ]
    simpa [Measure.real] using hbound

@[blueprint "lem:sample-complexity-rescaling"
  (statement := /-- For every $C>0$ there is $C'>0$ such that, uniformly for $m\in\mathbb N$ and $\epsilon,\delta\in(0,1)$,
  \[
    B_C(m,\epsilon/4,\delta/2)
      \leq B_{C'}(m,\epsilon,\delta).
  \] -/)
  (proof := /-- In \cref{def:sample-complexity-bound}, take
  $C'=16C(1+\log 2)$, which is positive.  For $0<\delta<1$, one has
  $\log(1/\delta)\geq0$ and
  $\log(1/(\delta/2))=\log 2+\log(1/\delta)$.  Hence
  \[
    16C\bigl(1+\log 2+\log(1/\delta)\bigr)
    \leq 16C(1+\log 2)(1+\log(1/\delta)).
  \]
  Division by the positive number $\epsilon^2$ preserves this inequality,
  and monotonicity of the natural ceiling yields the result. -/)
  (title := /-- Rescaling the sample-complexity parameters -/)
  (latexEnv := "lemma")]
lemma sample_complexity_rescaling (C : ℝ) (hC : 0 < C) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ (m : ℕ) (ε δ : ℝ),
        0 < ε → ε < 1 → 0 < δ → δ < 1 →
        sample_complexity_bound C m (ε / 4) (δ / 2) ≤
          sample_complexity_bound C' m ε δ := by
  refine ⟨16 * C * (1 + Real.log 2), ?_, ?_⟩
  · have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    positivity
  · intro m ε δ hε _ hδ hδ1
    unfold sample_complexity_bound
    apply Nat.add_le_add_left
    apply Nat.ceil_le_ceil
    have hεne : ε ≠ 0 := ne_of_gt hε
    have hδne : δ ≠ 0 := ne_of_gt hδ
    have hlogδ : 0 ≤ Real.log (1 / δ) := by
      apply Real.log_nonneg
      exact (le_div_iff₀ hδ).2 (by linarith)
    have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    have hlog_rescale :
        Real.log (1 / (δ / 2)) = Real.log 2 + Real.log (1 / δ) := by
      calc
        Real.log (1 / (δ / 2)) = Real.log (2 / δ) := by
          congr 1
          field_simp
        _ = Real.log 2 - Real.log δ := Real.log_div (by norm_num) hδne
        _ = Real.log 2 + Real.log (1 / δ) := by
          rw [Real.log_div (by norm_num) hδne, Real.log_one]
          ring
    rw [hlog_rescale]
    have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
    calc
      C * (1 + (Real.log 2 + Real.log (1 / δ))) / (ε / 4) ^ 2 =
          (16 * C * (1 + Real.log 2 + Real.log (1 / δ))) / ε ^ 2 := by
            field_simp [hεne]
            <;> ring
      _ ≤ (16 * C * (1 + Real.log 2) * (1 + Real.log (1 / δ))) / ε ^ 2 := by
        apply (div_le_div_iff_of_pos_right hεsq).2
        have hprod : 0 ≤ 16 * C * Real.log 2 * Real.log (1 / δ) := by
          positivity
        nlinarith

@[blueprint "lem:identity-testing-from-equivalence-testing"
  (statement := /-- Let $\mathcal X$ be a measurable space, let $\mathcal F$ be a Boolean distinguishing family on $\mathcal X$, let $T$ be an equivalence tester on $\mathcal X$, let $P_{\mathrm{ref}}$ be a probability measure on $\mathcal X$, let $m\in\mathbb N$, and let $\epsilon,\delta\in\mathbb R$.  Suppose that $T$ is an $(\epsilon,\delta)$-equivalence tester under the Rademacher promise at sample size $m$ and that
  $\mathcal R_m(\mathcal F,P_{\mathrm{ref}})\leq\epsilon/16$.  Then there exists a measurable $(\epsilon,\delta)$-identity tester $I$ to $P_{\mathrm{ref}}$ against $\mathcal F$ whose sample count is at most that of $T$. -/)
  (proof := /-- By \cref{def:identity-tester, def:equivalence-tester}, define $I$ to have the same sample count, decision rule, and measurability proof as $T$.  Fix an unknown probability measure $P$.  The assumed bound on $P_{\mathrm{ref}}$ is the second disjunct of the promise in \cref{def:rademacher-complexity-promise}, so apply the correctness hypothesis for $T$ to $(P,P_{\mathrm{ref}})$ using \cref{def:is-equivalence-tester-under-rademacher-promise}.  The definitions \cref{def:identity-acceptance-probability, def:identity-rejection-probability, def:equivalence-acceptance-probability, def:equivalence-rejection-probability} identify the acceptance and rejection probabilities of $I$ with those of $T$, since both use the product law $P^n\times P_{\mathrm{ref}}^n$ and the same rule.  Hence the completeness conclusion for $P=P_{\mathrm{ref}}$ and the soundness conclusion for $d_{\mathcal F}(P,P_{\mathrm{ref}})>\epsilon$ establish \cref{def:is-identity-tester}.  Finally, the two sample counts are equal, and therefore the required inequality holds. -/)
  (title := /-- Reduction from identity to equivalence testing -/)
  (latexEnv := "lemma")]
lemma identity_testing_from_equivalence_testing
    {X : Type*} [MeasurableSpace X]
    (F : boolean_distinguishing_family X)
    (T : equivalence_tester X) (P_ref : ProbabilityMeasure X)
    (m : ℕ) (ε δ : ℝ)
    (hT : is_equivalence_tester_under_rademacher_promise T F m ε δ)
    (hP : rademacher_complexity_promise F m P_ref (ε / 16)) :
    ∃ I : identity_tester X,
      is_identity_tester I F P_ref ε δ ∧ I.sampleCount ≤ T.sampleCount := by
  let I : identity_tester X :=
    { sampleCount := T.sampleCount
      decide := T.decide
      measurable_decide := T.measurable_decide }
  refine ⟨I, ?_, le_rfl⟩
  constructor
  · intro P hEq
    exact (hT P P_ref (Or.inr hP)).1 hEq
  · intro P hFar
    exact (hT P P_ref (Or.inr hP)).2 hFar

@[blueprint "thm:restricted-testing-upper-bounds-equivalence"
  (statement := /-- There is a universal constant $C>0$ with the following property.  Let $\mathcal X$ be a standard Borel measurable space, let $\mathcal F$ be a countable complemented family of measurable Boolean distinguishers, let $m$ be a positive integer, and let $\epsilon,\delta\in(0,1)$.  There exists a measurable $(\epsilon,\delta)$-equivalence tester for unknown distributions $P,Q$ under the promise
  \[
    \mathcal R_m(\mathcal F,P)\leq\epsilon/16
  \]
  or the analogous condition with $Q$ in place of $P$, using at most $B_C(m,\epsilon,\delta)$ samples from each input distribution. -/)
  (proof := /-- Choose the learner supplied by
  \cref{lem:testable-distribution-learning} with the positive sample parameter $m$, accuracy $\eta=\epsilon/4$, and failure probability $\delta/2$.  Its measurable paired-sample decision rule defines an equivalence tester.  The completeness conclusion is \cref{lem:learner-equivalence-completeness}, and the soundness conclusion is \cref{lem:learner-equivalence-soundness}.  The tester uses the learner's sample count from each input distribution.  Finally, \cref{lem:sample-complexity-rescaling} absorbs the substitutions $\epsilon\mapsto\epsilon/4$ and $\delta\mapsto\delta/2$ into a universal positive constant. -/)
  (title := /-- Restricted-interface upper bound for equivalence testing -/)
  (latexEnv := "theorem")]
theorem restricted_testing_upper_bounds_equivalence :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
        (F : boolean_distinguishing_family X)
        (m : ℕ) (ε δ : ℝ),
        0 < m → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        ∃ T : equivalence_tester X,
          is_equivalence_tester_under_rademacher_promise T F m ε δ ∧
          T.sampleCount ≤ sample_complexity_bound C m ε δ := by
  obtain ⟨C, hC, hlearner⟩ := testable_distribution_learning
  obtain ⟨C', hC', hrescale⟩ := sample_complexity_rescaling C hC
  refine ⟨C', hC', ?_⟩
  intro X inst1 inst2 F m ε δ hm hε hε1 hδ hδ1
  have hε4 : 0 < ε / 4 := by positivity
  have hε4_lt : ε / 4 < 1 := by linarith
  have hδ2 : 0 < δ / 2 := by positivity
  have hδ2_lt : δ / 2 < 1 := by linarith
  obtain ⟨L, hL, _, hdecide, hcount⟩ :=
    hlearner F m (ε / 4) (δ / 2) hm hε4 hε4_lt hδ2 hδ2_lt
  have hL' : is_rademacher_testable_distribution_learner
      L F m (ε / 4) (ε / 16) (δ / 2) := by
    convert hL using 1 <;> ring
  have hdecide' : Measurable (learner_equivalence_decision L F ε) := by
    simpa only [show (4 : ℝ) * (ε / 4) = ε by ring] using hdecide
  refine ⟨equivalence_tester_from_learner L F ε hdecide', ?_, ?_⟩
  · intro P Q hpromise
    exact ⟨learner_equivalence_completeness F L m ε δ hL' hdecide' P Q hpromise,
      learner_equivalence_soundness F L m ε δ hL' hdecide' P Q⟩
  · exact hcount.trans (hrescale m ε δ hε hε1 hδ hδ1)

@[blueprint "thm:restricted-testing-upper-bounds-identity"
  (statement := /-- There is a universal constant $C>0$ with the following property.  Let $\mathcal X$ be a standard Borel measurable space, let $\mathcal F$ be a countable complemented family of measurable Boolean distinguishers, let $m$ be a positive integer, let $\epsilon,\delta\in(0,1)$, and let $P_{\mathrm{ref}}$ be an explicit probability distribution.  If
  $\mathcal R_m(\mathcal F,P_{\mathrm{ref}})\leq\epsilon/16$, then there exists a measurable $(\epsilon,\delta)$-identity tester to $P_{\mathrm{ref}}$ against $\mathcal F$ using at most $B_C(m,\epsilon,\delta)$ samples from the unknown distribution. -/)
  (proof := /-- Apply \cref{thm:restricted-testing-upper-bounds-equivalence} with the same positive sample parameter $m$.  The assumed Rademacher bound for $P_{\mathrm{ref}}$ supplies the second disjunct of the equivalence promise for every unknown input distribution.  The reduction \cref{lem:identity-testing-from-equivalence-testing} uses an independent sample from $P_{\mathrm{ref}}$, preserves the number of unknown samples, and converts equivalence completeness and soundness into the corresponding identity-testing conclusions. -/)
  (title := /-- Restricted-interface upper bound for identity testing -/)
  (latexEnv := "theorem")]
theorem restricted_testing_upper_bounds_identity :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
        (F : boolean_distinguishing_family X)
        (P_ref : ProbabilityMeasure X)
        (m : ℕ) (ε δ : ℝ),
        0 < m → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        rademacher_complexity_promise F m P_ref (ε / 16) →
        ∃ T : identity_tester X,
          is_identity_tester T F P_ref ε δ ∧
          T.sampleCount ≤ sample_complexity_bound C m ε δ := by
  obtain ⟨C, hC, hEq⟩ := restricted_testing_upper_bounds_equivalence
  refine ⟨C, hC, ?_⟩
  intro X inst1 inst2 F P_ref m ε δ hm hε hε1 hδ hδ1 hP
  obtain ⟨T, hT, hcount⟩ := hEq F m ε δ hm hε hε1 hδ hδ1
  obtain ⟨I, hI, hIcount⟩ :=
    identity_testing_from_equivalence_testing F T P_ref m ε δ hT hP
  refine ⟨I, hI, Nat.le_trans hIcount hcount⟩

@[blueprint "def:unrestricted-upper-expectation"
  (statement := /-- Let $P$ be a probability measure on a measurable space $\mathcal X$, and let $g:\mathcal X\to\mathbb R$ admit an integrable measurable majorant.  Its upper expectation is
  \[
    \mathbb E_P^*[g]
      =\inf\left\{\int h\,dP:
        h\text{ is measurable and integrable, and }g\leq h\right\}.
  \]
  Every bounded real-valued function admits such a majorant.  If $g$ is measurable and integrable, this quantity agrees with its ordinary expectation; for a nonmeasurable indicator it is the outer probability of its support.  Thus nonmeasurable bounded functions are not assigned expectation zero. -/)
  (title := /-- Upper expectation of a bounded function -/)
  (latexEnv := "definition")]
noncomputable def unrestricted_upper_expectation
    {X : Type*} [MeasurableSpace X] (P : ProbabilityMeasure X)
    (g : X → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ h : X → ℝ,
    Measurable h ∧ Integrable h P.toMeasure ∧
      (∀ x, g x ≤ h x) ∧ (∫ x, h x ∂P.toMeasure) = r}

@[blueprint "def:unrestricted-fooling-distance"
  (statement := /-- Let $\mathcal X$ be a measurable space, let $\mathcal F\subseteq\{0,1\}^{\mathcal X}$ be an arbitrary family of Boolean functions, and let $P,Q$ be probability measures on $\mathcal X$.  With upper expectation as in \cref{def:unrestricted-upper-expectation}, the unrestricted fooling distance is
  \[
    d_{\mathcal F}(P,Q)
      =\sup_{f\in\mathcal F}\left|\mathbb E_P^*[f]-\mathbb E_Q^*[f]\right|.
  \]
  No countability or measurability hypothesis is imposed on $\mathcal F$; in particular, a nonmeasurable distinguisher contributes its outer expectation rather than zero. -/)
  (title := /-- Fooling distance for an unrestricted Boolean family -/)
  (latexEnv := "definition")]
noncomputable def unrestricted_fooling_distance
    {X : Type*} [MeasurableSpace X] (F : Set (X → Bool))
    (P Q : ProbabilityMeasure X) : ℝ :=
  sSup ((fun f : X → Bool =>
    |unrestricted_upper_expectation P (fun x => boolean_value (f x)) -
      unrestricted_upper_expectation Q (fun x => boolean_value (f x))|) '' F)

@[blueprint "def:unrestricted-empirical-rademacher-complexity"
  (statement := /-- Let $S=(x_i)_{i=1}^m$ be a sample in $\mathcal X$ and let $\mathcal F\subseteq\{0,1\}^{\mathcal X}$ be arbitrary.  Define
  \[
    \widehat{\mathcal R}(\mathcal F,S)
      =\mathbb E_{\sigma\sim\{\pm1\}^m}
        \left[\sup_{f\in\mathcal F}
          \left|\frac1m\sum_{i=1}^m\sigma_i(2f(x_i)-1)\right|\right].
  \]
  The expectation over signs is the normalized finite sum, with the usual real-number conventions when $m=0$. -/)
  (title := /-- Empirical Rademacher complexity for an unrestricted family -/)
  (latexEnv := "definition")]
noncomputable def unrestricted_empirical_rademacher_complexity
    {X : Type*} (F : Set (X → Bool)) {m : ℕ} (S : Fin m → X) : ℝ :=
  ((2 : ℝ) ^ m)⁻¹ *
    ∑ σ : Fin m → Bool,
      sSup ((fun f : X → Bool =>
        |(m : ℝ)⁻¹ *
          ∑ i : Fin m,
            rademacher_sign (σ i) * (2 * boolean_value (f (S i)) - 1)|) '' F)

@[blueprint "def:unrestricted-distributional-rademacher-complexity"
  (statement := /-- Let $P$ be a probability measure on $\mathcal X$, let $m\in\mathbb N$, and let $\mathcal F\subseteq\{0,1\}^{\mathcal X}$ be arbitrary.  Its distributional Rademacher complexity is the upper expectation
  \[
    \mathcal R_m^*(\mathcal F,P)
      =\mathbb E_{S\sim P^m}^*\!\left[\widehat{\mathcal R}(\mathcal F,S)\right]
  \]
  defined by \cref{def:unrestricted-upper-expectation}.  The empirical functional is bounded, so this upper expectation is finite even when the supremum over $\mathcal F$ is not measurable. -/)
  (title := /-- Distributional Rademacher complexity for an unrestricted family -/)
  (latexEnv := "definition")]
noncomputable def unrestricted_distributional_rademacher_complexity
    {X : Type*} [MeasurableSpace X] (F : Set (X → Bool))
    (m : ℕ) (P : ProbabilityMeasure X) : ℝ :=
  unrestricted_upper_expectation
    (ProbabilityMeasure.pi (fun _ : Fin m => P))
    (fun S => unrestricted_empirical_rademacher_complexity F S)

@[blueprint "def:unrestricted-rademacher-complexity-promise"
  (statement := /-- For an arbitrary Boolean family $\mathcal F\subseteq\{0,1\}^{\mathcal X}$, a probability measure $P$, a sample parameter $m$, and a threshold $\rho$, the unrestricted Rademacher-complexity promise is the upper-expectation inequality
  $\mathcal R_m^*(\mathcal F,P)\leq\rho$, where $\mathcal R_m^*$ is defined in \cref{def:unrestricted-distributional-rademacher-complexity}. -/)
  (title := /-- Rademacher promise for an unrestricted family -/)
  (latexEnv := "definition")]
def unrestricted_rademacher_complexity_promise
    {X : Type*} [MeasurableSpace X] (F : Set (X → Bool))
    (m : ℕ) (P : ProbabilityMeasure X) (ρ : ℝ) : Prop :=
  unrestricted_distributional_rademacher_complexity F m P ≤ ρ

@[blueprint "def:unrestricted-learner-good-run"
  (statement := /-- Let $L$ be a testable distribution learner and let $\mathcal F\subseteq\{0,1\}^{\mathcal X}$ be arbitrary.  A run on a sample $S$ is good at parameters $(m,\eta,\rho)$ if it returns a distribution within upper-expectation fooling distance $\eta$ of the input distribution, or if it rejects and the upper-expectation Rademacher promise at threshold $\rho$ is false.  The distance and promise are those of \cref{def:unrestricted-fooling-distance, def:unrestricted-rademacher-complexity-promise}. -/)
  (title := /-- Good learner runs for an unrestricted family -/)
  (latexEnv := "definition")]
def unrestricted_learner_good_run
    {X : Type*} [MeasurableSpace X] (L : testable_distribution_learner X)
    (F : Set (X → Bool)) (P : ProbabilityMeasure X)
    (m : ℕ) (η ρ : ℝ) (S : Fin L.sampleCount → X) : Prop :=
  match L.run S with
  | none => ¬ unrestricted_rademacher_complexity_promise F m P ρ
  | some P_hat => unrestricted_fooling_distance F P P_hat ≤ η

@[blueprint "def:is-unrestricted-rademacher-testable-distribution-learner"
  (statement := /-- A learner $L$ is an $(m,\eta,\rho,\delta)$-Rademacher testable distribution learner for an arbitrary Boolean family $\mathcal F$ if, for every input distribution $P$, the outer probability of the set of samples on which the good-run condition of \cref{def:unrestricted-learner-good-run} fails is at most $\delta$.  Equivalently, the good-run event has inner probability at least $1-\delta$; the outer-probability formulation remains meaningful when the learner, the family, or its empirical supremum is nonmeasurable. -/)
  (title := /-- Testable learning for an unrestricted family -/)
  (latexEnv := "definition")]
def is_unrestricted_rademacher_testable_distribution_learner
    {X : Type*} [MeasurableSpace X] (L : testable_distribution_learner X)
    (F : Set (X → Bool)) (m : ℕ) (η ρ δ : ℝ) : Prop :=
  ∀ P : ProbabilityMeasure X,
    sample_event_probability P L.sampleCount
      {S | ¬ unrestricted_learner_good_run L F P m η ρ S} ≤ δ

@[blueprint "def:unrestricted-tester"
  (statement := /-- An unrestricted tester using $n$ samples from each of two input distributions is a Boolean decision rule on pairs of samples in $\mathcal X^n$.  Its sample complexity is counted per input distribution.  In accordance with the source theorem's abstract algorithmic model, no measurability hypothesis is imposed on the rule. -/)
  (title := /-- Testers in the unrestricted algorithmic model -/)
  (latexEnv := "definition")]
structure unrestricted_tester (X : Type*) where
  sampleCount : ℕ
  decide : ((Fin sampleCount → X) × (Fin sampleCount → X)) → Bool

@[blueprint "def:unrestricted-acceptance-probability"
  (statement := /-- Let $T$ be an unrestricted tester with sample count $n$, and let $P,Q$ be probability measures on $\mathcal X$.  Its acceptance probability on $(P,Q)$ is the inner probability of its acceptance event, defined by
  \[
    1-(P^n\times Q^n)^*\{(S_P,S_Q):T(S_P,S_Q)=\mathtt{false}\},
  \]
  where the superscript $*$ denotes outer probability.  Thus a lower bound on this quantity is a genuine high-probability guarantee even when the decision rule is not measurable. -/)
  (title := /-- Inner acceptance probability of an unrestricted tester -/)
  (latexEnv := "definition")]
noncomputable def unrestricted_acceptance_probability
    {X : Type*} [MeasurableSpace X] (T : unrestricted_tester X)
    (P Q : ProbabilityMeasure X) : ℝ :=
  1 - ((ProbabilityMeasure.pi (fun _ : Fin T.sampleCount => P)).toMeasure.prod
    (ProbabilityMeasure.pi (fun _ : Fin T.sampleCount => Q)).toMeasure).real
      {S | T.decide S = false}

@[blueprint "def:unrestricted-rejection-probability"
  (statement := /-- Let $T$ be an unrestricted tester with sample count $n$, and let $P,Q$ be probability measures on $\mathcal X$.  Its rejection probability on $(P,Q)$ is the inner probability of its rejection event, defined by
  \[
    1-(P^n\times Q^n)^*\{(S_P,S_Q):T(S_P,S_Q)=\mathtt{true}\}.
  \]
  Consequently, a lower bound on this quantity controls the outer probability of every failure to reject, without requiring the decision rule to be measurable. -/)
  (title := /-- Inner rejection probability of an unrestricted tester -/)
  (latexEnv := "definition")]
noncomputable def unrestricted_rejection_probability
    {X : Type*} [MeasurableSpace X] (T : unrestricted_tester X)
    (P Q : ProbabilityMeasure X) : ℝ :=
  1 - ((ProbabilityMeasure.pi (fun _ : Fin T.sampleCount => P)).toMeasure.prod
    (ProbabilityMeasure.pi (fun _ : Fin T.sampleCount => Q)).toMeasure).real
      {S | T.decide S = true}

@[blueprint "def:is-unrestricted-identity-tester"
  (statement := /-- Let $\mathcal F\subseteq\{0,1\}^{\mathcal X}$ be arbitrary and let $P_{\mathrm{ref}}$ be an explicit reference distribution.  An unrestricted tester $T$ is an $(\epsilon,\delta)$-identity tester against $\mathcal F$ if its inner acceptance probability is at least $1-\delta$ whenever the unknown distribution equals $P_{\mathrm{ref}}$, and its inner rejection probability is at least $1-\delta$ whenever the unrestricted fooling distance from $P_{\mathrm{ref}}$ exceeds $\epsilon$.  Equivalently, the outer probability of the relevant erroneous decision is at most $\delta$ in each case.  The second sample is drawn independently from the explicit reference distribution. -/)
  (title := /-- Identity testing for an unrestricted family -/)
  (latexEnv := "definition")]
def is_unrestricted_identity_tester
    {X : Type*} [MeasurableSpace X] (T : unrestricted_tester X)
    (F : Set (X → Bool)) (P_ref : ProbabilityMeasure X)
    (ε δ : ℝ) : Prop :=
  (∀ P : ProbabilityMeasure X, P = P_ref →
      unrestricted_acceptance_probability T P P_ref ≥ 1 - δ) ∧
  (∀ P : ProbabilityMeasure X,
      unrestricted_fooling_distance F P P_ref > ε →
      unrestricted_rejection_probability T P P_ref ≥ 1 - δ)

@[blueprint "def:is-unrestricted-equivalence-tester-under-rademacher-promise"
  (statement := /-- Let $\mathcal F\subseteq\{0,1\}^{\mathcal X}$ be arbitrary.  An unrestricted tester $T$ is an $(\epsilon,\delta)$-equivalence tester under the upper-expectation Rademacher promise at sample size $m$ if, whenever $\mathcal R_m^*(\mathcal F,P)\leq\epsilon/16$ or $\mathcal R_m^*(\mathcal F,Q)\leq\epsilon/16$, its inner acceptance probability is at least $1-\delta$ when $P=Q$, and its inner rejection probability is at least $1-\delta$ when the upper-expectation fooling distance $d_{\mathcal F}(P,Q)$ exceeds $\epsilon$.  Equivalently, in either case the outer probability of the corresponding erroneous decision is at most $\delta$. -/)
  (title := /-- Equivalence testing for an unrestricted family -/)
  (latexEnv := "definition")]
def is_unrestricted_equivalence_tester_under_rademacher_promise
    {X : Type*} [MeasurableSpace X] (T : unrestricted_tester X)
    (F : Set (X → Bool)) (m : ℕ) (ε δ : ℝ) : Prop :=
  ∀ P Q : ProbabilityMeasure X,
    (unrestricted_rademacher_complexity_promise F m P (ε / 16) ∨
      unrestricted_rademacher_complexity_promise F m Q (ε / 16)) →
    (P = Q → unrestricted_acceptance_probability T P Q ≥ 1 - δ) ∧
    (unrestricted_fooling_distance F P Q > ε →
      unrestricted_rejection_probability T P Q ≥ 1 - δ)

@[blueprint "def:unrestricted-learner-equivalence-decision"
  (statement := /-- Given a learner $L$ and an arbitrary Boolean family $\mathcal F$, run $L$ on both samples.  Reject if either run rejects; otherwise accept precisely when the two returned distributions have unrestricted fooling distance at most $\epsilon/2$. -/)
  (title := /-- Learner-based decision for an unrestricted family -/)
  (latexEnv := "definition")]
noncomputable def unrestricted_learner_equivalence_decision
    {X : Type*} [MeasurableSpace X] (L : testable_distribution_learner X)
    (F : Set (X → Bool)) (ε : ℝ) :
    ((Fin L.sampleCount → X) × (Fin L.sampleCount → X)) → Bool :=
  fun S =>
    match L.run S.1, L.run S.2 with
    | some P_hat, some Q_hat =>
        if unrestricted_fooling_distance F P_hat Q_hat ≤ ε / 2 then true else false
    | _, _ => false

@[blueprint "def:unrestricted-equivalence-tester-from-learner"
  (statement := /-- The paired-sample rule of \cref{def:unrestricted-learner-equivalence-decision} defines an unrestricted tester with the same sample count as the learner. -/)
  (title := /-- Equivalence tester from an unrestricted learner -/)
  (latexEnv := "definition")]
noncomputable def unrestricted_equivalence_tester_from_learner
    {X : Type*} [MeasurableSpace X] (L : testable_distribution_learner X)
    (F : Set (X → Bool)) (ε : ℝ) : unrestricted_tester X where
  sampleCount := L.sampleCount
  decide := unrestricted_learner_equivalence_decision L F ε

@[blueprint "lem:unrestricted-testable-distribution-learning"
  (statement := /-- There exists a universal constant $C>0$ with the following property.  Let $\mathcal X$ be a standard Borel measurable space, let $\mathcal F$ be a countable family of measurable Boolean distinguishers closed under pointwise complementation, let $m$ be a positive integer, and let $\eta,\delta\in(0,1)$.  There is an $(m,\eta,\eta/4,\delta)$-Rademacher testable distribution learner $L$ against $\mathcal F$.  For every input probability measure $P$, the learner's good-run event is measurable; the paired-sample decision rule at threshold $4\eta$ is measurable; and the sample count of $L$ is at most $B_C(m,\eta,\delta)$. -/)
  (proof := /-- Apply \cref{lem:testable-distribution-learning} to the standard Borel space $\mathcal X$, the countable complemented family of measurable Boolean distinguishers $\mathcal F$, the positive integer $m$, and the parameters $\eta,\delta\in(0,1)$.  Its conclusion supplies the asserted learner, the measurable good-run events for every input probability measure, the measurable paired-sample decision rule, and the bound $B_C(m,\eta,\delta)$ with one universal positive constant $C$. -/)
  (title := /-- Testable learning for a measurable distinguishing family -/)
  (latexEnv := "lemma")]
lemma unrestricted_testable_distribution_learning :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
        (F : boolean_distinguishing_family X)
        (m : ℕ) (η δ : ℝ),
        0 < m → 0 < η → η < 1 → 0 < δ → δ < 1 →
        ∃ L : testable_distribution_learner X,
          is_rademacher_testable_distribution_learner
            L F m η (η / 4) δ ∧
          (∀ P : ProbabilityMeasure X,
            MeasurableSet
              {S : Fin L.sampleCount → X |
                learner_good_run L F P m η (η / 4) S}) ∧
          Measurable (learner_equivalence_decision L F (4 * η)) ∧
          L.sampleCount ≤ sample_complexity_bound C m η δ := by
  exact testable_distribution_learning

@[blueprint "thm:testing-upper-bounds-equivalence"
  (statement := /-- There exists a universal constant $C>0$ with the following property.  Let $\mathcal X$ be a standard Borel measurable space, let $\mathcal F$ be a countable family of measurable Boolean distinguishers closed under pointwise complementation, let $m$ be a positive integer, and let $\epsilon,\delta\in(0,1)$.  There exists a measurable $(\epsilon,\delta)$-equivalence tester for unknown probability measures $P,Q$ under the promise
  \[
    \mathcal R_m(\mathcal F,P)\leq\epsilon/16
  \]
  or the analogous condition with $Q$ in place of $P$.  The tester accepts with probability at least $1-\delta$ when $P=Q$, rejects with probability at least $1-\delta$ when $d_{\mathcal F}(P,Q)>\epsilon$, and uses at most $B_C(m,\epsilon,\delta)$ samples from each input distribution. -/)
  (proof := /-- Choose the learner supplied by
  \cref{lem:unrestricted-testable-distribution-learning} with the positive sample parameter $m$, accuracy $\eta=\epsilon/4$, and failure probability $\delta/2$.  Use the paired-sample rule in \cref{def:equivalence-tester-from-learner}: run the learner independently on samples from $P$ and $Q$, reject if either run rejects, and otherwise accept exactly when the fooling distance between the returned distributions is at most $\epsilon/2$.

  Suppose first that $P=Q$ and that the Rademacher promise holds for one input.  It then holds for both.  By \cref{lem:learner-equivalence-completeness}, the two good-run guarantees and the union bound imply that, with probability at least $1-\delta$, both runs return distributions $\widehat P$ and $\widehat Q$ satisfying
  \[
    d_{\mathcal F}(P,\widehat P)\leq\epsilon/4,
    \qquad
    d_{\mathcal F}(P,\widehat Q)\leq\epsilon/4.
  \]
  The triangle inequality gives $d_{\mathcal F}(\widehat P,\widehat Q)\leq\epsilon/2$, so the tester accepts on this event.

  Now suppose that $d_{\mathcal F}(P,Q)>\epsilon$.  By \cref{lem:learner-equivalence-soundness}, with probability at least $1-\delta$, either one learner run rejects, in which case the tester rejects, or both runs return distributions with
  $d_{\mathcal F}(P,\widehat P)\leq\epsilon/4$ and
  $d_{\mathcal F}(Q,\widehat Q)\leq\epsilon/4$.  In the latter case the reverse triangle inequality yields
  \[
    d_{\mathcal F}(\widehat P,\widehat Q)
      \geq d_{\mathcal F}(P,Q)
        -d_{\mathcal F}(P,\widehat P)
        -d_{\mathcal F}(Q,\widehat Q)
      >\epsilon/2,
  \]
  so the tester again rejects.  The tester uses the learner's sample count from each input.  Finally,
  \cref{lem:sample-complexity-rescaling} absorbs the replacements
  $\epsilon\mapsto\epsilon/4$ and $\delta\mapsto\delta/2$ into a universal constant, giving the stated bound. -/)
  (title := /-- Upper bound for equivalence testing -/)
  (latexEnv := "theorem")]
theorem testing_upper_bounds_equivalence :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
        (F : boolean_distinguishing_family X)
        (m : ℕ) (ε δ : ℝ),
        0 < m → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        ∃ T : equivalence_tester X,
          is_equivalence_tester_under_rademacher_promise
            T F m ε δ ∧
          T.sampleCount ≤ sample_complexity_bound C m ε δ := by
  obtain ⟨C, hC, hlearn⟩ := unrestricted_testable_distribution_learning
  obtain ⟨C', hC', hrescale⟩ := sample_complexity_rescaling C hC
  refine ⟨C', hC', ?_⟩
  intro X instM instB F m ε δ hm hε hε1 hδ hδ1
  obtain ⟨L, hL, _, hdec, hcount⟩ :=
    hlearn F m (ε / 4) (δ / 2) hm (by positivity) (by linarith)
      (by positivity) (by linarith)
  have hrho : (ε / 4) / 4 = ε / 16 := by ring
  rw [hrho] at hL
  have hthreshold : 4 * (ε / 4) = ε := by ring
  rw [hthreshold] at hdec
  refine ⟨equivalence_tester_from_learner L F ε hdec, ?_⟩
  constructor
  · intro P Q hpromise
    exact
      ⟨learner_equivalence_completeness F L m ε δ hL hdec P Q hpromise,
        learner_equivalence_soundness F L m ε δ hL hdec P Q⟩
  · change L.sampleCount ≤ sample_complexity_bound C' m ε δ
    exact le_trans hcount (hrescale m ε δ hε hε1 hδ hδ1)

@[blueprint "thm:testing-upper-bounds-identity"
  (statement := /-- There exists a universal constant $C>0$ with the following property.  Let $\mathcal X$ be a standard Borel measurable space, let $\mathcal F$ be a countable family of measurable Boolean distinguishers closed under pointwise complementation, let $m$ be a positive integer, let $\epsilon,\delta\in(0,1)$, and let $P_{\mathrm{ref}}$ be an explicit probability distribution.  If
  $\mathcal R_m(\mathcal F,P_{\mathrm{ref}})\leq\epsilon/16$, then there exists a measurable $(\epsilon,\delta)$-identity tester to $P_{\mathrm{ref}}$ against $\mathcal F$ with correctness probability at least $1-\delta$ and sample count at most $B_C(m,\epsilon,\delta)$. -/)
  (proof := /-- Apply \cref{thm:testing-upper-bounds-equivalence} with the same positive sample parameter $m$.  For every unknown probability measure $P$, the assumed Rademacher bound for the explicit reference measure $P_{\mathrm{ref}}$ supplies the second disjunct of the equivalence promise.  The reduction \cref{lem:identity-testing-from-equivalence-testing} uses $P_{\mathrm{ref}}$ as the second input, preserves the number of samples drawn from the unknown distribution, and converts equivalence completeness and soundness into the acceptance and rejection clauses of the identity tester.  Combining its sample-count inequality with the equivalence tester's bound proves the assertion. -/)
  (title := /-- Upper bound for identity testing -/)
  (latexEnv := "theorem")]
theorem testing_upper_bounds_identity :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
        (F : boolean_distinguishing_family X)
        (P_ref : ProbabilityMeasure X)
        (m : ℕ) (ε δ : ℝ),
        0 < m → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        rademacher_complexity_promise F m P_ref (ε / 16) →
        ∃ T : identity_tester X,
          is_identity_tester T F P_ref ε δ ∧
          T.sampleCount ≤ sample_complexity_bound C m ε δ := by
  obtain ⟨C, hC, hEq⟩ := testing_upper_bounds_equivalence
  refine ⟨C, hC, ?_⟩
  intro X instM instB F P_ref m ε δ hm hε hε1 hδ hδ1 hP
  obtain ⟨T, hT, hcount⟩ := hEq F m ε δ hm hε hε1 hδ hδ1
  obtain ⟨I, hI, hIcount⟩ :=
    identity_testing_from_equivalence_testing F T P_ref m ε δ hT hP
  exact ⟨I, hI, Nat.le_trans hIcount hcount⟩

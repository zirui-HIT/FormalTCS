import Architect
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Process.Adapted

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:is-submodular-set-function"
  (statement := /-- A real-valued set function $f$ is submodular in diminishing-returns form if,
  whenever $S\subseteq T$ and $i\notin T$, one has
  $f(S\cup\{i\})-f(S)\geq f(T\cup\{i\})-f(T)$. -/)
  (title := /-- Submodular set function -/)
  (latexEnv := "definition")]
def is_submodular_set_function {α : Type*} (f : Set α → ℝ) : Prop :=
  ∀ ⦃S T : Set α⦄, S ⊆ T → ∀ ⦃i : α⦄, i ∉ T →
    f (insert i S) - f S ≥ f (insert i T) - f T

@[blueprint "def:multilinear-extension"
  (statement := /-- Let $U$ be finite and let $f\colon 2^U\to\mathbb R$.  For
  $x\in\mathbb R^U$, the multilinear extension is
  \[
    F(x)=\sum_{S\subseteq U} f(S)\prod_{i\in S}x_i
      \prod_{i\in U\setminus S}(1-x_i).
  \] -/)
  (title := /-- Multilinear extension -/)
  (latexEnv := "definition")]
noncomputable def multilinear_extension {α : Type*} [Fintype α] [DecidableEq α]
    (f : Set α → ℝ) (x : α → ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset α).powerset,
    f (↑S : Set α) * (∏ i ∈ S, x i) *
      ∏ i ∈ (Finset.univ : Finset α) \ S, (1 - x i)

@[blueprint "def:scaled-indicator"
  (statement := /-- For a finite set $A\subseteq U$ and $t\in\mathbb R$, the scaled
  indicator $t\mathbf 1_A\in\mathbb R^U$ has coordinate $t$ on $A$ and coordinate
  $0$ on $U\setminus A$. -/)
  (title := /-- Scaled indicator vector -/)
  (latexEnv := "definition")]
def scaled_indicator {α : Type*} [DecidableEq α] (t : ℝ) (A : Finset α) : α → ℝ :=
  fun i ↦ if i ∈ A then t else 0

@[blueprint "def:multilinear-marginal"
  (statement := /-- For the multilinear extension $F$ from
  \cref{def:multilinear-extension}, the $i$th multilinear marginal at $x$ is
  $F(x[i\leftarrow 1])-F(x[i\leftarrow 0])$.  Multilinearity identifies this
  quantity with the coordinate derivative $\nabla_iF(x)$. -/)
  (title := /-- Coordinate marginal of the multilinear extension -/)
  (latexEnv := "definition")]
noncomputable def multilinear_marginal {α : Type*} [Fintype α] [DecidableEq α]
    (f : Set α → ℝ) (x : α → ℝ) (i : α) : ℝ :=
  multilinear_extension f (Function.update x i 1) -
    multilinear_extension f (Function.update x i 0)

@[blueprint "def:is-gradient-maximizing-base"
  (statement := /-- Let $M$ be a matroid on a finite ground type, let $A$ be a finite
  set, and let $t\in\mathbb R$.  A finite set $Z$ is a gradient-maximizing base at
  $(t,A)$ if $Z$ is a base of $M$ and its sum of multilinear marginals at
  $t\mathbf 1_A$ is at least the corresponding sum over every finite base. -/)
  (title := /-- Gradient-maximizing base -/)
  (latexEnv := "definition")]
def is_gradient_maximizing_base {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matroid α) (f : Set α → ℝ) (t : ℝ) (A Z : Finset α) : Prop :=
  M.IsBase (↑Z : Set α) ∧
    ∀ B : Finset α, M.IsBase (↑B : Set α) →
      (∑ i ∈ B, multilinear_marginal f (scaled_indicator t A) i) ≤
        ∑ i ∈ Z, multilinear_marginal f (scaled_indicator t A) i

@[blueprint "def:base-exchange-bijection"
  (statement := /-- Let $A$ and $Z$ be finite sets in a matroid $M$.  A base-exchange
  bijection is a bijection $h\colon A\to Z$ such that
  $A-i+h(i)$ is a base of $M$ for every $i\in A$. -/)
  (title := /-- Base-exchange bijection -/)
  (latexEnv := "definition")]
structure base_exchange_bijection {α : Type*} [DecidableEq α]
    (M : Matroid α) (A Z : Finset α) where
  equiv : A ≃ Z
  valid : ∀ i : A,
    M.IsBase (↑(insert (equiv i).1 (A.erase i.1)) : Set α)

@[blueprint "def:expected-set-value"
  (statement := /-- If $p$ is a probability mass function on the finite subsets of
  $U$, then the expected value of $f$ under $p$ is
  $\sum_A p(A)f(A)$, with the extended-nonnegative mass converted to a real number. -/)
  (title := /-- Expected value of a random finite set -/)
  (latexEnv := "definition")]
noncomputable def expected_set_value {α : Type*} [Fintype α]
    (f : Set α → ℝ) (p : PMF (Finset α)) : ℝ :=
  ∑ A : Finset α, (p A).toReal * f (↑A : Set α)

@[blueprint "def:gs-poisson-dynamics"
  (statement := /-- Fix a finite matroid $M$, a set function $f$, and a starting
  time $\varepsilon$.  GS--Poisson dynamics consist of an initial base $A_0$,
  whose cardinality $k=|A_0|$ is the rank of $M$, the rate
  $\lambda(t)=k/t$ on $[\varepsilon,1]$, a
  gradient-maximizing base $Z(t,A)$ for every admissible time and current base,
  a base-exchange bijection from $A$ to $Z(t,A)$, and the uniform law on $A$ used
  to select the element exchanged at an event. -/)
  (title := /-- Event dynamics of GS--Poisson -/)
  (latexEnv := "definition")]
structure gs_poisson_dynamics {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matroid α) (f : Set α → ℝ) (ε : ℝ) where
  initial : Finset α
  initial_isBase : M.IsBase (↑initial : Set α)
  rate : ℝ → ℝ
  rate_spec : ∀ ⦃t : ℝ⦄, ε ≤ t → t ≤ 1 →
    rate t = (initial.card : ℝ) / t
  greedyBase : ℝ → Finset α → Finset α
  greedy_base_spec : ∀ ⦃t : ℝ⦄ ⦃A : Finset α⦄,
    ε ≤ t → t ≤ 1 → M.IsBase (↑A : Set α) →
      is_gradient_maximizing_base M f t A (greedyBase t A)
  exchange : ∀ (t : ℝ) (A : Finset α), ε ≤ t → t ≤ 1 →
    M.IsBase (↑A : Set α) →
      base_exchange_bijection M A (greedyBase t A)
  uniformSwapLaw : ∀ (t : ℝ) (A : Finset α), A.Nonempty → PMF α
  uniform_swap_law_spec : ∀ (t : ℝ) (A : Finset α) (hA : A.Nonempty),
    uniformSwapLaw t A hA = PMF.uniformOfFinset A hA

@[blueprint "def:gs-poisson-swap-law"
  (statement := /-- Let $D$ be GS--Poisson dynamics.  At an admissible event time
  $t$ with current nonempty base $A$, the one-event law chooses $i\in A$
  uniformly and returns $A-i+h_{t,A}(i)$, where $h_{t,A}$ is the recorded
  exchange bijection.  Outside the admissible regime the law leaves $A$
  unchanged; this totalization is immaterial for valid event schedules. -/)
  (title := /-- One-event GS--Poisson transition law -/)
  (latexEnv := "definition")]
noncomputable def gs_poisson_swap_law {α : Type*} [Fintype α] [DecidableEq α]
    {M : Matroid α} {f : Set α → ℝ} {ε : ℝ}
    (D : gs_poisson_dynamics M f ε) (t : ℝ) (A : Finset α) :
    PMF (Finset α) :=
  if ht : ε ≤ t ∧ t ≤ 1 then
    letI : Decidable (M.IsBase (↑A : Set α)) := Classical.propDecidable _
    if hAbase : M.IsBase (↑A : Set α) then
      if hA : A.Nonempty then
        PMF.map
          (fun i ↦ if hi : i ∈ A then
            insert ((D.exchange t A ht.1 ht.2 hAbase).equiv ⟨i, hi⟩).1
              (A.erase i)
          else A)
          (D.uniformSwapLaw t A hA)
      else PMF.pure A
    else PMF.pure A
  else PMF.pure A

@[blueprint "def:gs-poisson-run-law"
  (statement := /-- For GS--Poisson dynamics $D$ and a chronologically ordered
  finite list $(t_1,\ldots,t_N)$ of event times, the conditional terminal law is
  obtained from the point mass at the initial base by successively applying the
  one-event transition laws at $t_1,\ldots,t_N$. -/)
  (title := /-- Conditional terminal law along an event schedule -/)
  (latexEnv := "definition")]
noncomputable def gs_poisson_run_law {α : Type*} [Fintype α] [DecidableEq α]
    {M : Matroid α} {f : Set α → ℝ} {ε : ℝ}
    (D : gs_poisson_dynamics M f ε) (times : List ℝ) : PMF (Finset α) :=
  times.foldl
    (fun stateLaw t ↦ stateLaw.bind (gs_poisson_swap_law D t))
    (PMF.pure D.initial)

@[blueprint "def:gs-poisson-expected-potential"
  (statement := /-- Let $D$ be GS--Poisson dynamics, let $t\in\mathbb R$, and
  let $q$ be a probability mass function on finite sets.  The expected
  multilinear potential of $q$ at time $t$ is
  \[
    \sum_A q(A)F(t\mathbf 1_A),
  \]
  where $F$ is \cref{def:multilinear-extension}. -/)
  (title := /-- Expected multilinear potential -/)
  (latexEnv := "definition")]
noncomputable def gs_poisson_expected_potential {α : Type*} [Fintype α]
    [DecidableEq α] {M : Matroid α} {f : Set α → ℝ} {ε : ℝ}
    (D : gs_poisson_dynamics M f ε) (t : ℝ) (q : PMF (Finset α)) : ℝ :=
  ∑ A : Finset α, (q A).toReal *
    multilinear_extension f (scaled_indicator t A)

@[blueprint "def:gs-poisson-expected-drift"
  (statement := /-- Let $D$ be GS--Poisson dynamics, let $t\in\mathbb R$, and
  let $q$ be the pre-jump law of the current base.  Its expected instantaneous
  potential drift is the $q$-average of
  \[
    \sum_{i\in A}\nabla_iF(t\mathbf 1_A)
    +\lambda(t)\,
      \mathbb E_{B\sim K_{t,A}}
        \bigl[F(t\mathbf 1_B)-F(t\mathbf 1_A)\bigr],
  \]
  where $K_{t,A}$ is the one-event transition law from
  \cref{def:gs-poisson-swap-law}.  The first term is the derivative between
  events and the second is the marked-jump compensator. -/)
  (title := /-- Expected instantaneous GS--Poisson drift -/)
  (latexEnv := "definition")]
noncomputable def gs_poisson_expected_drift {α : Type*} [Fintype α]
    [DecidableEq α] {M : Matroid α} {f : Set α → ℝ} {ε : ℝ}
    (D : gs_poisson_dynamics M f ε) (t : ℝ) (q : PMF (Finset α)) : ℝ :=
  ∑ A : Finset α, (q A).toReal *
    ((∑ i ∈ A, multilinear_marginal f (scaled_indicator t A) i) +
      D.rate t * ∑ B : Finset α, ((gs_poisson_swap_law D t A) B).toReal *
        (multilinear_extension f (scaled_indicator t B) -
          multilinear_extension f (scaled_indicator t A)))

@[blueprint "def:gs-poisson-process"
  (statement := /-- Fix a finite matroid $M$, a set function $f$, and
  $0<\varepsilon\leq 1$.  A GS--Poisson process consists of
  \cref{def:gs-poisson-dynamics} together with a probability law on finite,
  strictly chronologically ordered event schedules in $(\varepsilon,1]$.
  The number of events in every interval $(a,b]\subseteq(\varepsilon,1]$ has
  the Poisson law with mean $k\log(b/a)$, where $k$ is the cardinality of the
  recorded initial base and hence the rank of $M$; moreover, the count random
  variables associated with every finite family of pairwise disjoint such
  intervals are jointly independent.  The schedule space carries a filtration
  $(\mathcal F_t)_{t\in\mathbb R}$ to which both the count up to time $t$ and
  every coordinate of the conditional state law obtained from events up to
  time $t$ are adapted.  For $\varepsilon\leq s\leq t\leq1$, the count on
  $(s,t]$ is independent of $\mathcal F_s$.  Every coordinate of the
  schedule-dependent terminal law in \cref{def:gs-poisson-run-law} is
  measurable.  The time-and-schedule kernels for the expected potential
  \cref{def:gs-poisson-expected-potential} and the pre-jump drift
  \cref{def:gs-poisson-expected-drift} are jointly measurable, and the latter
  is adapted to $(\mathcal F_t)_{t\in\mathbb R}$.  On every subinterval
  $[s,t]\subseteq[\varepsilon,1]$, their expectations satisfy the exact Dynkin
  identity: the change of expected potential equals the time integral of the
  expected pre-jump drift.  Finally, the field
  \texttt{output} is required pointwise to be the integral of the measurable
  terminal probability kernel.  Thus the compensator is tied to the same
  Poisson events, greedy bases, exchange bijections, and uniform swaps that
  induce the terminal law. -/)
  (title := /-- GS--Poisson process and its induced terminal law -/)
  (latexEnv := "definition")]
structure gs_poisson_process {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matroid α) (f : Set α → ℝ) (ε : ℝ) where
  dynamics : gs_poisson_dynamics M f ε
  eventScheduleLaw : MeasureTheory.Measure (ℕ × (ℕ → ℝ))
  event_schedule_is_probability :
    MeasureTheory.IsProbabilityMeasure eventScheduleLaw
  event_schedule_spec : ∀ᵐ schedule ∂eventScheduleLaw,
    (∀ i : ℕ, i < schedule.1 →
      ε < schedule.2 i ∧ schedule.2 i ≤ 1) ∧
    (∀ i j : ℕ, i < j → j < schedule.1 →
      schedule.2 i < schedule.2 j)
  intervalCountLaw : ℝ → ℝ → PMF ℕ
  interval_count_law_spec : ∀ ⦃a b : ℝ⦄, ε ≤ a → a ≤ b → b ≤ 1 →
    ∀ n : ℕ, (intervalCountLaw a b n).toReal =
      Real.exp (-((dynamics.initial.card : ℝ) * Real.log (b / a))) *
        ((dynamics.initial.card : ℝ) * Real.log (b / a)) ^ n / n.factorial
  event_schedule_count_spec : ∀ ⦃a b : ℝ⦄, ε ≤ a → a ≤ b → b ≤ 1 →
    ∀ n : ℕ,
      eventScheduleLaw {schedule |
        ((Finset.range schedule.1).filter
          (fun i ↦ a < schedule.2 i ∧ schedule.2 i ≤ b)).card = n} =
        intervalCountLaw a b n
  independent_increments_spec :
    ∀ (n : ℕ) (a b : Fin n → ℝ),
      (∀ i, ε ≤ a i ∧ a i ≤ b i ∧ b i ≤ 1) →
      (∀ i j, i ≠ j →
        Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a j) (b j))) →
      ProbabilityTheory.iIndepFun
        (fun i schedule ↦
          ((Finset.range schedule.1).filter
            (fun j ↦ a i < schedule.2 j ∧ schedule.2 j ≤ b i)).card)
        eventScheduleLaw
  eventFiltration :
    MeasureTheory.Filtration ℝ
      (inferInstance : MeasurableSpace (ℕ × (ℕ → ℝ)))
  event_count_adapted :
    MeasureTheory.Adapted eventFiltration
      (fun t schedule ↦
        ((Finset.range schedule.1).filter
          (fun i ↦ ε < schedule.2 i ∧ schedule.2 i ≤ t)).card)
  run_law_adapted : ∀ A : Finset α,
    MeasureTheory.Adapted eventFiltration
      (fun t schedule ↦
        gs_poisson_run_law dynamics
          ((List.ofFn (fun i : Fin schedule.1 ↦ schedule.2 i)).filter
            (fun s ↦ s ≤ t)) A)
  future_increment_independent :
    ∀ ⦃s t : ℝ⦄, ε ≤ s → s ≤ t → t ≤ 1 →
      ProbabilityTheory.Indep (eventFiltration s)
        (MeasurableSpace.comap
          (fun schedule : ℕ × (ℕ → ℝ) ↦
            ((Finset.range schedule.1).filter
              (fun i ↦ s < schedule.2 i ∧ schedule.2 i ≤ t)).card)
          (inferInstance : MeasurableSpace ℕ))
        eventScheduleLaw
  terminal_run_measurable : ∀ A : Finset α,
    Measurable (fun schedule : ℕ × (ℕ → ℝ) ↦
      gs_poisson_run_law dynamics
        (List.ofFn (fun i : Fin schedule.1 ↦ schedule.2 i)) A)
  potential_jointly_measurable :
    Measurable (fun z : ℝ × (ℕ × (ℕ → ℝ)) ↦
      gs_poisson_expected_potential dynamics z.1
        (gs_poisson_run_law dynamics
          ((List.ofFn (fun i : Fin z.2.1 ↦ z.2.2 i)).filter
            (fun u ↦ u ≤ z.1))))
  prejump_drift_jointly_measurable :
    Measurable (fun z : ℝ × (ℕ × (ℕ → ℝ)) ↦
      gs_poisson_expected_drift dynamics z.1
        (gs_poisson_run_law dynamics
          ((List.ofFn (fun i : Fin z.2.1 ↦ z.2.2 i)).filter
            (fun u ↦ u < z.1))))
  prejump_drift_adapted :
    MeasureTheory.Adapted eventFiltration
      (fun t schedule ↦
        gs_poisson_expected_drift dynamics t
          (gs_poisson_run_law dynamics
            ((List.ofFn (fun i : Fin schedule.1 ↦ schedule.2 i)).filter
              (fun u ↦ u < t))))
  potential_compensator_identity :
    ∀ ⦃s t : ℝ⦄, ε ≤ s → s ≤ t → t ≤ 1 →
      (∫ schedule,
          gs_poisson_expected_potential dynamics t
            (gs_poisson_run_law dynamics
              ((List.ofFn (fun i : Fin schedule.1 ↦ schedule.2 i)).filter
                (fun u ↦ u ≤ t)))
        ∂eventScheduleLaw) -
        (∫ schedule,
          gs_poisson_expected_potential dynamics s
            (gs_poisson_run_law dynamics
              ((List.ofFn (fun i : Fin schedule.1 ↦ schedule.2 i)).filter
                (fun u ↦ u ≤ s)))
        ∂eventScheduleLaw) =
        ∫ u in s..t,
          ∫ schedule,
            gs_poisson_expected_drift dynamics u
              (gs_poisson_run_law dynamics
                ((List.ofFn (fun i : Fin schedule.1 ↦ schedule.2 i)).filter
                  (fun r ↦ r < u)))
          ∂eventScheduleLaw
  output : PMF (Finset α)
  output_is_terminal_law : ∀ A : Finset α,
    output A = ∫⁻ schedule,
      gs_poisson_run_law dynamics
        (List.ofFn (fun i : Fin schedule.1 ↦ schedule.2 i)) A
      ∂eventScheduleLaw
  output_isBase : ∀ A : Finset α, A ∈ output.support →
    M.IsBase (↑A : Set α)

@[blueprint "lem:gs-poisson-output-independent"
  (statement := /-- Let $P$ be a GS--Poisson process for a finite matroid $M$.
  Every finite set in the support of the terminal output law of $P$ is independent
  in $M$. -/)
  (proof := /-- Let $A$ belong to the support of the terminal law.  By the terminal
  support condition in \cref{def:gs-poisson-process}, $A$ is a base of $M$.
  Every base of a matroid is independent, and hence $A$ is independent. -/)
  (title := /-- Terminal outputs are independent -/)
  (latexEnv := "lemma")]
lemma gs_poisson_output_independent {α : Type*} [Fintype α] [DecidableEq α]
    {M : Matroid α} {f : Set α → ℝ} {ε : ℝ}
    (P : gs_poisson_process M f ε) :
    ∀ A : Finset α, A ∈ P.output.support → M.Indep (↑A : Set α) := by
  intro A hA
  exact (P.output_isBase A hA).indep

@[blueprint "lem:gs-poisson-terminal-potential-eq"
  (statement := /-- For every finite set $A$ and set function $f$, the multilinear
  extension at the indicator of $A$ equals $f(A)$. -/)
  (proof := /-- Expand the multilinear extension from
  \cref{def:multilinear-extension}.  At the indicator of $A$, the summand indexed
  by $A$ is $f(A)$, while every other summand contains a zero factor. -/)
  (title := /-- Multilinear extension at an indicator -/)
  (latexEnv := "lemma")]
lemma gs_poisson_terminal_potential_eq {α : Type*} [Fintype α] [DecidableEq α]
    (f : Set α → ℝ) (A : Finset α) :
    multilinear_extension f (scaled_indicator 1 A) = f (↑A : Set α) := by
  classical
  rw [multilinear_extension, Finset.sum_eq_single A]
  · have hone : ∏ i ∈ A, scaled_indicator 1 A i = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      simp [scaled_indicator, hi]
    have hzero : ∏ i ∈ (Finset.univ : Finset α) \ A,
        (1 - scaled_indicator 1 A i) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      simp [scaled_indicator, Finset.mem_sdiff.mp hi]
    simp [hone, hzero]
  · intro B hB hBA
    by_cases hsub : B ⊆ A
    · obtain ⟨i, hiA, hiB⟩ : ∃ i, i ∈ A ∧ i ∉ B := by
        by_contra h
        push Not at h
        exact hBA (Finset.Subset.antisymm hsub h)
      have hiuniv : i ∈ (Finset.univ : Finset α) \ B := by simp [hiB]
      have hz : ∏ j ∈ (Finset.univ : Finset α) \ B,
          (1 - scaled_indicator 1 A j) = 0 := by
        apply Finset.prod_eq_zero hiuniv
        simp [scaled_indicator, hiA]
      simp [hz]
    · obtain ⟨i, hiB, hiA⟩ : ∃ i, i ∈ B ∧ i ∉ A := by
        simpa [Finset.not_subset] using hsub
      have hz : ∏ j ∈ B, scaled_indicator 1 A j = 0 := by
        apply Finset.prod_eq_zero hiB
        simp [scaled_indicator, hiA]
      simp [hz]
  · simp

@[blueprint "lem:gs-poisson-multilinear-nonnegative-on-cube"
  (statement := /-- If $f$ is nonnegative and every coordinate of $x$ lies in
  $[0,1]$, then the multilinear extension of $f$ at $x$ is nonnegative. -/)
  (proof := /-- Expand \cref{def:multilinear-extension}.  Every coordinate and
  complementary-coordinate factor is nonnegative, as is the value of $f$ in
  each summand. -/)
  (title := /-- Nonnegativity of the multilinear extension on the cube -/)
  (latexEnv := "lemma")]
lemma gs_poisson_multilinear_nonnegative_on_cube {α : Type*} [Fintype α]
    [DecidableEq α] {f : Set α → ℝ} (hf : ∀ S : Set α, 0 ≤ f S)
    {x : α → ℝ} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    0 ≤ multilinear_extension f x := by
  classical
  unfold multilinear_extension
  apply Finset.sum_nonneg
  intro S hS
  exact mul_nonneg (mul_nonneg (hf _) (Finset.prod_nonneg fun i hi ↦ (hx i).1))
    (Finset.prod_nonneg fun i hi ↦ sub_nonneg.mpr (hx i).2)

@[blueprint "lem:gs-poisson-multilinear-nonnegative"
  (statement := /-- If $f$ is nonnegative and $0\leq t\leq1$, then its
  multilinear extension is nonnegative at every scaled indicator
  $t\mathbf 1_A$. -/)
  (proof := /-- Every coordinate of the scaled indicator lies in $[0,1]$;
  apply \cref{lem:gs-poisson-multilinear-nonnegative-on-cube}. -/)
  (title := /-- Nonnegativity of the scaled multilinear extension -/)
  (latexEnv := "lemma")]
lemma gs_poisson_multilinear_nonnegative {α : Type*} [Fintype α] [DecidableEq α]
    {f : Set α → ℝ} (hf : ∀ S : Set α, 0 ≤ f S)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (A : Finset α) :
    0 ≤ multilinear_extension f (scaled_indicator t A) := by
  apply gs_poisson_multilinear_nonnegative_on_cube hf
  intro i
  simp only [scaled_indicator]
  split <;> constructor <;> linarith

@[blueprint "lem:gs-poisson-expected-potential-nonnegative"
  (statement := /-- If $f$ is nonnegative and $0\leq t\leq1$, then the expected
  multilinear potential of every probability mass function is nonnegative. -/)
  (proof := /-- Expand \cref{def:gs-poisson-expected-potential}.  Each probability
  weight is nonnegative, and each scaled multilinear value is nonnegative by
  \cref{lem:gs-poisson-multilinear-nonnegative}; hence their finite sum is
  nonnegative. -/)
  (title := /-- Nonnegativity of expected potential -/)
  (latexEnv := "lemma")]
lemma gs_poisson_expected_potential_nonnegative {α : Type*} [Fintype α]
    [DecidableEq α] {M : Matroid α} {f : Set α → ℝ} {ε : ℝ}
    (D : gs_poisson_dynamics M f ε) (hf : ∀ S : Set α, 0 ≤ f S)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (q : PMF (Finset α)) :
    0 ≤ gs_poisson_expected_potential D t q := by
  classical
  unfold gs_poisson_expected_potential
  apply Finset.sum_nonneg
  intro A hA
  exact mul_nonneg ENNReal.toReal_nonneg
    (gs_poisson_multilinear_nonnegative hf ht0 ht1 A)

@[blueprint "lem:gs-poisson-discrete-gradient-bound"
  (statement := /-- For a monotone submodular set function $f$ and finite sets
  $S,O$, the gain $f(O)-f(S)$ is at most the sum, over $i\in O$, of the
  marginal gains $f(S+i)-f(S)$. -/)
  (proof := /-- Monotonicity first bounds $f(O)$ by $f(S\cup O)$.  Insert the
  elements of $O$ one at a time.  At each insertion, diminishing returns from
  \cref{def:is-submodular-set-function} bounds the new marginal by its marginal
  at the original set $S$; elements already in $S$ contribute zero.  Summing
  these inequalities gives the claim. -/)
  (title := /-- Discrete gradient bound for a submodular function -/)
  (latexEnv := "lemma")]
lemma gs_poisson_discrete_gradient_bound {α : Type*} [DecidableEq α]
    {f : Set α → ℝ} (hfmono : Monotone f)
    (hfsubmod : is_submodular_set_function f) (S O : Finset α) :
    f (↑O : Set α) - f (↑S : Set α) ≤
      ∑ i ∈ O, (f (insert i (↑S : Set α)) - f (↑S : Set α)) := by
  classical
  have hunion : f (↑(S ∪ O) : Set α) - f (↑S : Set α) ≤
      ∑ i ∈ O, (f (insert i (↑S : Set α)) - f (↑S : Set α)) := by
    induction O using Finset.induction_on with
    | empty => simp
    | @insert a O ha ih =>
        by_cases haS : a ∈ S
        · convert ih using 1 <;> simp [ha, haS] <;> ring
        · have hsub : (↑S : Set α) ⊆ (↑(S ∪ O) : Set α) := by
            intro x hx
            simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
            exact Or.inl hx
          have haU : a ∉ (↑(S ∪ O) : Set α) := by simp [ha, haS]
          have hm := hfsubmod hsub haU
          calc
            f (↑(S ∪ insert a O) : Set α) - f (↑S : Set α) =
                (f (insert a (↑(S ∪ O) : Set α)) - f (↑(S ∪ O) : Set α)) +
                  (f (↑(S ∪ O) : Set α) - f (↑S : Set α)) := by
              simp only [Finset.union_insert, Finset.coe_insert, Finset.coe_union]
              ring
            _ ≤ (f (insert a (↑S : Set α)) - f (↑S : Set α)) +
                  ∑ i ∈ O, (f (insert i (↑S : Set α)) - f (↑S : Set α)) :=
              add_le_add hm ih
            _ = ∑ i ∈ insert a O,
                  (f (insert i (↑S : Set α)) - f (↑S : Set α)) := by
              rw [Finset.sum_insert ha]
  calc
    f (↑O : Set α) - f (↑S : Set α) ≤
        f (↑(S ∪ O) : Set α) - f (↑S : Set α) := by
      gcongr
      apply hfmono
      intro x hx
      simp [hx]
    _ ≤ _ := hunion

@[blueprint "lem:gs-poisson-exponential-chord"
  (statement := /-- For every $0\leq\varepsilon\leq1$,
  $(1-\varepsilon)(1-e^{-1})\leq1-e^{-(1-\varepsilon)}$. -/)
  (proof := /-- Apply convexity of the exponential function on the segment from
  $0$ to $-1$, with coefficients $\varepsilon$ and $1-\varepsilon$, and
  rearrange the resulting inequality. -/)
  (title := /-- Exponential chord inequality -/)
  (latexEnv := "lemma")]
lemma gs_poisson_exponential_chord {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (1 - ε) * (1 - 1 / Real.exp 1) ≤ 1 - Real.exp (-(1 - ε)) := by
  have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ))
    (Set.mem_univ (-1 : ℝ)) hε0 (sub_nonneg.mpr hε1) (by ring)
  norm_num [smul_eq_mul, Real.exp_neg] at hconv
  have heq : ε - 1 = -(1 - ε) := by ring
  rw [heq] at hconv
  simp only [one_div]
  nlinarith

@[blueprint "lem:gs-poisson-swap-preserves-base"
  (statement := /-- At an admissible time, one GS--Poisson transition from a
  base is supported on bases. -/)
  (proof := /-- Unfold the transition law from
  \cref{def:gs-poisson-swap-law}.  For a nonempty base, every point in the
  support is the image of an element of the uniform law and is a base by the
  recorded exchange bijection.  For the empty base, the transition is the
  point mass at that base. -/)
  (title := /-- A GS--Poisson swap preserves bases -/)
  (latexEnv := "lemma")]
lemma gs_poisson_swap_preserves_base {α : Type*} [Fintype α] [DecidableEq α]
    {M : Matroid α} {f : Set α → ℝ} {ε t : ℝ}
    (D : gs_poisson_dynamics M f ε) (ht0 : ε ≤ t) (ht1 : t ≤ 1)
    (A : Finset α) (hA : M.IsBase (↑A : Set α)) :
    ∀ B : Finset α, B ∈ (gs_poisson_swap_law D t A).support →
      M.IsBase (↑B : Set α) := by
  intro B hB
  by_cases hne : A.Nonempty
  · rw [gs_poisson_swap_law, dif_pos ⟨ht0, ht1⟩, dif_pos hA,
      dif_pos hne, PMF.mem_support_map_iff] at hB
    obtain ⟨i, hi, rfl⟩ := hB
    have hiA : i ∈ A := by
      simpa [D.uniform_swap_law_spec t A hne] using hi
    simp only [dif_pos hiA]
    exact (D.exchange t A ht0 ht1 hA).valid ⟨i, hiA⟩
  · rw [gs_poisson_swap_law, dif_pos ⟨ht0, ht1⟩, dif_pos hA,
      dif_neg hne, PMF.mem_support_pure_iff] at hB
    simpa [hB] using hA

@[blueprint "lem:gs-poisson-run-preserves-base"
  (statement := /-- If all event times in a finite schedule lie in
  $[\varepsilon,1]$, the conditional GS--Poisson terminal law is supported on
  bases. -/)
  (proof := /-- Induct on the schedule from the right.  The empty schedule is
  the point mass at the initial base from \cref{def:gs-poisson-dynamics}.  At
  the induction step, the support formula for a bind and
  \cref{lem:gs-poisson-swap-preserves-base} show that one further admissible
  transition preserves the base invariant. -/)
  (title := /-- GS--Poisson runs remain on bases -/)
  (latexEnv := "lemma")]
lemma gs_poisson_run_preserves_base {α : Type*} [Fintype α] [DecidableEq α]
    {M : Matroid α} {f : Set α → ℝ} {ε : ℝ}
    (D : gs_poisson_dynamics M f ε) (times : List ℝ)
    (htimes : ∀ t ∈ times, ε ≤ t ∧ t ≤ 1) :
    ∀ B : Finset α, B ∈ (gs_poisson_run_law D times).support →
      M.IsBase (↑B : Set α) := by
  induction times using List.reverseRecOn with
  | nil =>
      intro B hB
      have h : B = D.initial := by
        simpa [gs_poisson_run_law, PMF.mem_support_pure_iff] using hB
      simpa [h] using D.initial_isBase
  | append_singleton times t ih =>
      intro B hB
      simp only [gs_poisson_run_law, List.foldl_append, List.foldl_cons,
        List.foldl_nil] at hB
      rw [PMF.mem_support_bind_iff] at hB
      obtain ⟨A, hA, hAB⟩ := hB
      have hAtimes : ∀ u ∈ times, ε ≤ u ∧ u ≤ 1 := by
        intro u hu
        exact htimes u (List.mem_append_left [t] hu)
      have ht := htimes t (by simp)
      exact gs_poisson_swap_preserves_base D ht.1 ht.2 A (ih hAtimes A hA) B hAB

@[blueprint "lem:gs-poisson-product-update-outside"
  (statement := /-- Updating a function at an index outside a finite product
  does not change that product. -/)
  (proof := /-- Compare the factors pointwise.  Every index in the product is
  distinct from the updated index, so function update leaves its value fixed. -/)
  (title := /-- Products are unchanged by an outside update -/)
  (latexEnv := "lemma")]
lemma gs_poisson_product_update_outside {α : Type*} [DecidableEq α]
    (x : α → ℝ) (i : α) (z : ℝ) (S : Finset α) (hi : i ∉ S) :
    ∏ j ∈ S, Function.update x i z j = ∏ j ∈ S, x j := by
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := by
    intro h
    subst j
    exact hi hj
  simp [Function.update, hji]

@[blueprint "lem:gs-poisson-product-update-inside"
  (statement := /-- Updating a function at an index inside a finite product
  replaces exactly that factor. -/)
  (proof := /-- Separate the distinguished factor with the product-erasure
  identity and apply \cref{lem:gs-poisson-product-update-outside} to the
  remaining factors. -/)
  (title := /-- Products under an inside update -/)
  (latexEnv := "lemma")]
lemma gs_poisson_product_update_inside {α : Type*} [DecidableEq α]
    (x : α → ℝ) (i : α) (z : ℝ) (S : Finset α) (hi : i ∈ S) :
    ∏ j ∈ S, Function.update x i z j = z * ∏ j ∈ S.erase i, x j := by
  rw [← Finset.prod_erase_mul _ _ hi]
  rw [gs_poisson_product_update_outside x i z (S.erase i) (Finset.notMem_erase i S)]
  simp [Function.update]
  ring

@[blueprint "lem:gs-poisson-multilinear-update"
  (statement := /-- The multilinear extension is affine in each coordinate:
  replacing coordinate $i$ by $r$ gives $rF(x[i\leftarrow1])+
  (1-r)F(x[i\leftarrow0])$. -/)
  (proof := /-- Expand \cref{def:multilinear-extension} and split its finite
  sum according as the indexing subset contains $i$.  In the first case the
  first coordinate product contributes $r$; in the second case the
  complementary-coordinate product contributes $1-r$.  The product
  calculations use \cref{lem:gs-poisson-product-update-outside,
  lem:gs-poisson-product-update-inside}. -/)
  (title := /-- Coordinate affinity of the multilinear extension -/)
  (latexEnv := "lemma")]
lemma gs_poisson_multilinear_update {α : Type*} [Fintype α] [DecidableEq α]
    (f : Set α → ℝ) (x : α → ℝ) (i : α) (r : ℝ) :
    multilinear_extension f (Function.update x i r) =
      r * multilinear_extension f (Function.update x i 1) +
        (1 - r) * multilinear_extension f (Function.update x i 0) := by
  classical
  unfold multilinear_extension
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hiS : i ∈ S
  · have hcomp : i ∉ (Finset.univ : Finset α) \ S := by simp [hiS]
    have hp (z : ℝ) : ∏ j ∈ S, Function.update x i z j =
        z * ∏ j ∈ S.erase i, x j := by
      exact gs_poisson_product_update_inside x i z S hiS
    have hc (z : ℝ) : ∏ j ∈ (Finset.univ : Finset α) \ S,
        (1 - Function.update x i z j) =
          ∏ j ∈ (Finset.univ : Finset α) \ S, (1 - x j) := by
      calc
        _ = ∏ j ∈ (Finset.univ : Finset α) \ S,
            Function.update (fun k ↦ 1 - x k) i (1 - z) j := by
          apply Finset.prod_congr rfl
          intro j hj
          by_cases hji : j = i <;> simp [Function.update, hji]
        _ = _ := gs_poisson_product_update_outside
          (fun k ↦ 1 - x k) i (1 - z) _ hcomp
    rw [hp r, hp 1, hp 0, hc r, hc 1, hc 0]
    ring
  · have hicomp : i ∈ (Finset.univ : Finset α) \ S := by simp [hiS]
    have hp (z : ℝ) : ∏ j ∈ S, Function.update x i z j = ∏ j ∈ S, x j := by
      exact gs_poisson_product_update_outside x i z S hiS
    have hc (z : ℝ) : ∏ j ∈ (Finset.univ : Finset α) \ S,
        (1 - Function.update x i z j) =
          (1 - z) * ∏ j ∈ ((Finset.univ : Finset α) \ S).erase i,
            (1 - x j) := by
      calc
        _ = ∏ j ∈ (Finset.univ : Finset α) \ S,
            Function.update (fun k ↦ 1 - x k) i (1 - z) j := by
          apply Finset.prod_congr rfl
          intro j hj
          by_cases hji : j = i <;> simp [Function.update, hji]
        _ = _ := gs_poisson_product_update_inside
          (fun k ↦ 1 - x k) i (1 - z) _ hicomp
    rw [hp r, hp 1, hp 0, hc r, hc 1, hc 0]
    ring

@[blueprint "lem:gs-poisson-multilinear-coordinate-difference"
  (statement := /-- Changing one coordinate of the multilinear extension from
  $r$ to $s$ changes its value by $(s-r)$ times the corresponding multilinear
  marginal. -/)
  (proof := /-- Apply the coordinate-affinity identity
  \cref{lem:gs-poisson-multilinear-update} at $r$ and $s$, subtract the two
  equalities, and use \cref{def:multilinear-marginal}. -/)
  (title := /-- Coordinate difference formula for the multilinear extension -/)
  (latexEnv := "lemma")]
lemma gs_poisson_multilinear_coordinate_difference {α : Type*} [Fintype α]
    [DecidableEq α] (f : Set α → ℝ) (x : α → ℝ) (i : α) (r s : ℝ) :
    multilinear_extension f (Function.update x i s) -
        multilinear_extension f (Function.update x i r) =
      (s - r) * multilinear_marginal f x i := by
  calc
    multilinear_extension f (Function.update x i s) -
        multilinear_extension f (Function.update x i r) =
        (s * multilinear_extension f (Function.update x i 1) +
          (1 - s) * multilinear_extension f (Function.update x i 0)) -
        (r * multilinear_extension f (Function.update x i 1) +
          (1 - r) * multilinear_extension f (Function.update x i 0)) := by
      rw [gs_poisson_multilinear_update f x i s,
        gs_poisson_multilinear_update f x i r]
    _ = (s - r) * multilinear_marginal f x i := by
      unfold multilinear_marginal
      ring

@[blueprint "lem:gs-poisson-marginal-as-extension"
  (statement := /-- A multilinear marginal is the multilinear extension of the
  corresponding discrete marginal set function, after fixing that coordinate
  to zero. -/)
  (proof := /-- Expand both sides using
  \cref{def:multilinear-extension} and
  \cref{def:multilinear-marginal}, split the power set according as it contains
  the distinguished coordinate, and evaluate the coordinate factors using
  \cref{lem:gs-poisson-product-update-outside,
  lem:gs-poisson-product-update-inside}. -/)
  (title := /-- Multilinear marginals as multilinear extensions -/)
  (latexEnv := "lemma")]
lemma gs_poisson_marginal_as_extension {α : Type*} [Fintype α] [DecidableEq α]
    (f : Set α → ℝ) (x : α → ℝ) (i : α) :
    multilinear_marginal f x i =
      multilinear_extension (fun S ↦ f (insert i S) - f S)
        (Function.update x i 0) := by
  classical
  let U : Finset α := Finset.univ.erase i
  have hiU : i ∉ U := Finset.notMem_erase i _
  have huniv : (Finset.univ : Finset α) = insert i U := by simp [U]
  unfold multilinear_marginal multilinear_extension
  rw [huniv]
  simp only [Finset.sum_powerset_insert hiU]
  have hA1 : ∑ T ∈ U.powerset,
      (f (↑T : Set α) * ∏ j ∈ T, Function.update x i 1 j) *
        ∏ j ∈ insert i U \ T, (1 - Function.update x i 1 j) = 0 := by
    apply Finset.sum_eq_zero
    intro T hT
    have hiT : i ∉ T := by
      intro hit
      exact hiU ((Finset.mem_powerset.mp hT) hit)
    have hic : i ∈ insert i U \ T := by simp [hiT]
    have hz : ∏ j ∈ insert i U \ T, (1 - Function.update x i 1 j) = 0 := by
      apply Finset.prod_eq_zero hic
      simp [Function.update]
    simp [hz]
  have hB0 : ∑ T ∈ U.powerset,
      (f (↑(insert i T) : Set α) *
          ∏ j ∈ insert i T, Function.update x i 0 j) *
        ∏ j ∈ insert i U \ insert i T, (1 - Function.update x i 0 j) = 0 := by
    apply Finset.sum_eq_zero
    intro T hT
    have hiins : i ∈ insert i T := Finset.mem_insert_self i T
    have hz : ∏ j ∈ insert i T, Function.update x i 0 j = 0 := by
      apply Finset.prod_eq_zero hiins
      simp [Function.update]
    simp [hz]
  have hC1 : ∑ T ∈ U.powerset,
      (((f (insert i (↑(insert i T) : Set α)) - f (↑(insert i T) : Set α)) *
          ∏ j ∈ insert i T, Function.update x i 0 j) *
        ∏ j ∈ insert i U \ insert i T, (1 - Function.update x i 0 j)) = 0 := by
    apply Finset.sum_eq_zero
    intro T hT
    have hiins : i ∈ insert i T := Finset.mem_insert_self i T
    have hz : ∏ j ∈ insert i T, Function.update x i 0 j = 0 := by
      apply Finset.prod_eq_zero hiins
      simp [Function.update]
    simp [hz]
  rw [hA1, hB0, hC1]
  simp only [zero_add, add_zero, zero_sub]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  have hiT : i ∉ T := by
    intro hit
    exact hiU ((Finset.mem_powerset.mp hT) hit)
  have hp1 : ∏ j ∈ insert i T, Function.update x i 1 j = ∏ j ∈ T, x j := by
    rw [gs_poisson_product_update_inside x i 1 _ (Finset.mem_insert_self i T)]
    simp [hiT]
  have hp0 : ∏ j ∈ T, Function.update x i 0 j = ∏ j ∈ T, x j :=
    gs_poisson_product_update_outside x i 0 T hiT
  have hcset : insert i U \ insert i T = U \ T := by
    ext j
    simp [U]
  have hc1 : ∏ j ∈ insert i U \ insert i T,
      (1 - Function.update x i 1 j) = ∏ j ∈ U \ T, (1 - x j) := by
    rw [hcset]
    have hi : i ∉ U \ T := by simp [hiU]
    calc
      _ = ∏ j ∈ U \ T, Function.update (fun k ↦ 1 - x k) i 0 j := by
        apply Finset.prod_congr rfl
        intro j hj
        by_cases hji : j = i <;> simp [Function.update, hji]
      _ = _ := gs_poisson_product_update_outside (fun k ↦ 1 - x k) i 0 _ hi
  have hc0 : ∏ j ∈ insert i U \ T,
      (1 - Function.update x i 0 j) = ∏ j ∈ U \ T, (1 - x j) := by
    have hic : i ∈ insert i U \ T := by simp [hiT]
    calc
      _ = ∏ j ∈ insert i U \ T,
          Function.update (fun k ↦ 1 - x k) i 1 j := by
        apply Finset.prod_congr rfl
        intro j hj
        by_cases hji : j = i <;> simp [Function.update, hji]
      _ = _ := by
        rw [gs_poisson_product_update_inside (fun k ↦ 1 - x k) i 1 _ hic]
        have herase : (insert i U \ T).erase i = U \ T := by
          ext j
          simp [U]
        rw [herase]
        simp
  rw [hp1, hp0, hc1, hc0]
  simp only [Finset.coe_insert]
  ring

@[blueprint "lem:gs-poisson-marginal-nonnegative"
  (statement := /-- Every multilinear marginal of a monotone set function is
  nonnegative at a point of the unit cube. -/)
  (proof := /-- By \cref{lem:gs-poisson-marginal-as-extension}, the marginal is
  the multilinear extension of the discrete marginal function.  Monotonicity
  makes that function nonnegative, and
  \cref{lem:gs-poisson-multilinear-nonnegative-on-cube} applies after the
  distinguished coordinate is set to zero. -/)
  (title := /-- Nonnegative multilinear marginals -/)
  (latexEnv := "lemma")]
lemma gs_poisson_marginal_nonnegative {α : Type*} [Fintype α] [DecidableEq α]
    {f : Set α → ℝ} (hfmono : Monotone f) {x : α → ℝ}
    (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1) (i : α) :
    0 ≤ multilinear_marginal f x i := by
  rw [gs_poisson_marginal_as_extension]
  apply gs_poisson_multilinear_nonnegative_on_cube
  · intro S
    exact sub_nonneg.mpr (hfmono (Set.subset_insert i S))
  · intro j
    by_cases hji : j = i
    · subst j
      simp [Function.update]
    · simpa [Function.update, hji] using hx j

@[blueprint "lem:gs-poisson-multilinear-update-monotone"
  (statement := /-- For a monotone set function, increasing one coordinate of
  a point in the unit cube cannot decrease its multilinear extension. -/)
  (proof := /-- The coordinate difference formula
  \cref{lem:gs-poisson-multilinear-coordinate-difference} expresses the change
  as the product of the nonnegative coordinate increment and the nonnegative
  marginal supplied by \cref{lem:gs-poisson-marginal-nonnegative}. -/)
  (title := /-- Coordinatewise monotonicity of the multilinear extension -/)
  (latexEnv := "lemma")]
lemma gs_poisson_multilinear_update_monotone {α : Type*} [Fintype α]
    [DecidableEq α] {f : Set α → ℝ} (hfmono : Monotone f)
    {x : α → ℝ} (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1)
    (i : α) {r s : ℝ} (hrs : r ≤ s) :
    multilinear_extension f (Function.update x i r) ≤
      multilinear_extension f (Function.update x i s) := by
  have hd := gs_poisson_multilinear_coordinate_difference f x i r s
  have hm := gs_poisson_marginal_nonnegative hfmono hx i
  nlinarith [mul_nonneg (sub_nonneg.mpr hrs) hm]

@[blueprint "lem:gs-poisson-multilinear-monotone"
  (statement := /-- On the unit cube, the multilinear extension of a monotone
  set function is monotone in the coordinatewise order. -/)
  (proof := /-- Replace the coordinates one at a time.  Each replacement is
  nondecreasing by \cref{lem:gs-poisson-multilinear-update-monotone}; induction
  over the finite ground set then gives the result. -/)
  (title := /-- Monotonicity of the multilinear extension -/)
  (latexEnv := "lemma")]
lemma gs_poisson_multilinear_monotone {α : Type*} [Fintype α] [DecidableEq α]
    {f : Set α → ℝ} (hfmono : Monotone f) {x y : α → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1)
    (hxy : ∀ i, x i ≤ y i) :
    multilinear_extension f x ≤ multilinear_extension f y := by
  classical
  let z : Finset α → α → ℝ := fun S i ↦ if i ∈ S then y i else x i
  have hz (S : Finset α) : ∀ i, 0 ≤ z S i ∧ z S i ≤ 1 := by
    intro i
    simp only [z]
    split
    · exact hy i
    · exact hx i
  have hind : ∀ S : Finset α,
      multilinear_extension f x ≤ multilinear_extension f (z S) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [z]
    | @insert a S ha ih =>
        apply ih.trans
        have hstep := gs_poisson_multilinear_update_monotone hfmono (hz S) a (hxy a)
        have hleft : Function.update (z S) a (x a) = z S := by
          funext j
          by_cases hja : j = a
          · subst j
            simp [z, ha, Function.update]
          · simp [z, hja]
        have hright : Function.update (z S) a (y a) = z (insert a S) := by
          funext j
          by_cases hja : j = a
          · subst j
            simp [z, Function.update]
          · simp [z, hja]
        simpa [hleft, hright] using hstep
  simpa [z] using hind (Finset.univ : Finset α)

@[blueprint "lem:gs-poisson-multilinear-neg"
  (statement := /-- The multilinear extension of the pointwise negation of a
  set function is the negation of its multilinear extension. -/)
  (proof := /-- Expand \cref{def:multilinear-extension}, distribute negation
  through the finite sum, and rearrange each summand. -/)
  (title := /-- Multilinear extension commutes with negation -/)
  (latexEnv := "lemma")]
lemma gs_poisson_multilinear_neg {α : Type*} [Fintype α] [DecidableEq α]
    (f : Set α → ℝ) (x : α → ℝ) :
    multilinear_extension (fun S ↦ -f S) x = -multilinear_extension f x := by
  classical
  unfold multilinear_extension
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  ring

@[blueprint "lem:gs-poisson-marginal-antitone"
  (statement := /-- For a monotone submodular set function, each multilinear
  marginal is antitone on the unit cube in the coordinatewise order. -/)
  (proof := /-- By \cref{lem:gs-poisson-marginal-as-extension}, the marginal
  is the multilinear extension of the corresponding discrete marginal.  The
  diminishing-returns hypothesis makes the negative of that discrete marginal
  monotone (with the case in which the distinguished element is already
  present following from monotonicity).  Apply
  \cref{lem:gs-poisson-multilinear-monotone} to the negated function and use
  \cref{lem:gs-poisson-multilinear-neg}. -/)
  (title := /-- Antitonicity of multilinear marginals -/)
  (latexEnv := "lemma")]
lemma gs_poisson_marginal_antitone {α : Type*} [Fintype α] [DecidableEq α]
    {f : Set α → ℝ} (hfmono : Monotone f)
    (hfsubmod : is_submodular_set_function f) {x y : α → ℝ}
    (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1) (hy : ∀ j, 0 ≤ y j ∧ y j ≤ 1)
    (hxy : ∀ j, x j ≤ y j) (i : α) :
    multilinear_marginal f y i ≤ multilinear_marginal f x i := by
  let g : Set α → ℝ := fun S ↦ f (insert i S) - f S
  have hg : Monotone (fun S ↦ -g S) := by
    intro S T hST
    simp only [g]
    by_cases hiT : i ∈ T
    · have hi : insert i T = T := Set.insert_eq_of_mem hiT
      rw [hi]
      have hnonneg : 0 ≤ f (insert i S) - f S :=
        sub_nonneg.mpr (hfmono (Set.subset_insert i S))
      linarith
    · have hsub := hfsubmod hST hiT
      linarith
  rw [gs_poisson_marginal_as_extension, gs_poisson_marginal_as_extension]
  have hx0 : ∀ j, 0 ≤ Function.update x i 0 j ∧
      Function.update x i 0 j ≤ 1 := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [Function.update]
    · simpa [Function.update, hji] using hx j
  have hy0 : ∀ j, 0 ≤ Function.update y i 0 j ∧
      Function.update y i 0 j ≤ 1 := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [Function.update]
    · simpa [Function.update, hji] using hy j
  have hxy0 : ∀ j, Function.update x i 0 j ≤ Function.update y i 0 j := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [Function.update]
    · simpa [Function.update, hji] using hxy j
  have h := gs_poisson_multilinear_monotone hg hx0 hy0 hxy0
  rw [gs_poisson_multilinear_neg, gs_poisson_multilinear_neg] at h
  linarith

@[blueprint "lem:gs-poisson-discrete-marginal-extension-le"
  (statement := /-- On the unit cube, the multilinear extension of the
  discrete $i$th marginal is at most the $i$th multilinear marginal. -/)
  (proof := /-- Let $g(S)=f(S+i)-f(S)$.  Monotonicity makes $g$ nonnegative.
  The coordinate-affinity identity \cref{lem:gs-poisson-multilinear-update}
  writes $F_g(x)$ as $(1-x_i)F_g(x[i\leftarrow0])$, because the term with
  coordinate $i$ fixed to one vanishes.  The latter value is the marginal by
  \cref{lem:gs-poisson-marginal-as-extension}, and it is nonnegative by
  \cref{lem:gs-poisson-multilinear-nonnegative-on-cube}. -/)
  (title := /-- Expected discrete marginal is bounded by multilinear marginal -/)
  (latexEnv := "lemma")]
lemma gs_poisson_discrete_marginal_extension_le {α : Type*} [Fintype α]
    [DecidableEq α] {f : Set α → ℝ} (hfmono : Monotone f)
    {x : α → ℝ} (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1) (i : α) :
    multilinear_extension (fun S ↦ f (insert i S) - f S) x ≤
      multilinear_marginal f x i := by
  classical
  let g : Set α → ℝ := fun S ↦ f (insert i S) - f S
  have hg : ∀ S : Set α, 0 ≤ g S := by
    intro S
    exact sub_nonneg.mpr (hfmono (Set.subset_insert i S))
  have hx0 : ∀ j, 0 ≤ Function.update x i 0 j ∧
      Function.update x i 0 j ≤ 1 := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [Function.update]
    · simpa [Function.update, hji] using hx j
  have hzero : multilinear_extension g (Function.update x i 1) = 0 := by
    unfold multilinear_extension
    apply Finset.sum_eq_zero
    intro S hS
    by_cases hiS : i ∈ S
    · have hgi : g (↑S : Set α) = 0 := by
        simp [g, Set.insert_eq_of_mem hiS]
      simp [hgi]
    · have hic : i ∈ (Finset.univ : Finset α) \ S := by simp [hiS]
      have hz : ∏ j ∈ (Finset.univ : Finset α) \ S,
          (1 - Function.update x i 1 j) = 0 := by
        apply Finset.prod_eq_zero hic
        simp [Function.update]
      simp [hz]
  have hself : Function.update x i (x i) = x := by
    funext j
    by_cases hji : j = i <;> simp [Function.update, hji]
  have haff := gs_poisson_multilinear_update g x i (x i)
  rw [hself, hzero] at haff
  have hm : 0 ≤ multilinear_extension g (Function.update x i 0) :=
    gs_poisson_multilinear_nonnegative_on_cube hg hx0
  rw [gs_poisson_marginal_as_extension]
  change multilinear_extension g x ≤ multilinear_extension g (Function.update x i 0)
  nlinarith [mul_nonneg (hx i).1 hm]

@[blueprint "lem:gs-poisson-multilinear-monotone-function"
  (statement := /-- On the unit cube, pointwise order of set functions is
  preserved by their multilinear extensions. -/)
  (proof := /-- Expand \cref{def:multilinear-extension}.  Every product weight
  is nonnegative, so pointwise comparison of the set-function values compares
  each summand. -/)
  (title := /-- Monotonicity of multilinear extension in the set function -/)
  (latexEnv := "lemma")]
lemma gs_poisson_multilinear_monotone_function {α : Type*} [Fintype α]
    [DecidableEq α] {f g : Set α → ℝ} (hfg : ∀ S, f S ≤ g S)
    {x : α → ℝ} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    multilinear_extension f x ≤ multilinear_extension g x := by
  classical
  unfold multilinear_extension
  apply Finset.sum_le_sum
  intro S hS
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul_of_nonneg_right (hfg _) (Finset.prod_nonneg fun i hi ↦ (hx i).1)
  · exact Finset.prod_nonneg fun i hi ↦ sub_nonneg.mpr (hx i).2

@[blueprint "lem:gs-poisson-multilinear-sum"
  (statement := /-- Multilinear extension commutes with a finite sum of set
  functions. -/)
  (proof := /-- Expand \cref{def:multilinear-extension}, distribute the finite
  sums through multiplication, and interchange their order. -/)
  (title := /-- Multilinear extension of a finite sum -/)
  (latexEnv := "lemma")]
lemma gs_poisson_multilinear_sum {α ι : Type*} [Fintype α] [DecidableEq α]
    (I : Finset ι) (g : ι → Set α → ℝ) (x : α → ℝ) :
    multilinear_extension (fun S ↦ ∑ i ∈ I, g i S) x =
      ∑ i ∈ I, multilinear_extension (g i) x := by
  classical
  unfold multilinear_extension
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

@[blueprint "lem:gs-poisson-multilinear-one"
  (statement := /-- The multilinear extension of the constant-one set function
  equals one throughout the unit cube. -/)
  (proof := /-- Coordinatewise monotonicity
  \cref{lem:gs-poisson-multilinear-monotone} sandwiches the value between its
  values at the zero and one vectors.  Both endpoint values are one by
  \cref{lem:gs-poisson-terminal-potential-eq}. -/)
  (title := /-- Multilinear extension of the constant one function -/)
  (latexEnv := "lemma")]
lemma gs_poisson_multilinear_one {α : Type*} [Fintype α] [DecidableEq α]
    {x : α → ℝ} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    multilinear_extension (fun _ : Set α ↦ (1 : ℝ)) x = 1 := by
  let z : α → ℝ := fun _ ↦ 0
  let o : α → ℝ := fun _ ↦ 1
  have hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1 := by intro i; simp [z]
  have ho : ∀ i, 0 ≤ o i ∧ o i ≤ 1 := by intro i; simp [o]
  have hzx : ∀ i, z i ≤ x i := fun i ↦ (hx i).1
  have hxo : ∀ i, x i ≤ o i := fun i ↦ (hx i).2
  have hl := gs_poisson_multilinear_monotone (f := fun _ : Set α ↦ (1 : ℝ))
    (fun _ _ _ ↦ le_rfl) hz hx hzx
  have hr := gs_poisson_multilinear_monotone (f := fun _ : Set α ↦ (1 : ℝ))
    (fun _ _ _ ↦ le_rfl) hx ho hxo
  have hzval : multilinear_extension (fun _ : Set α ↦ (1 : ℝ)) z = 1 := by
    rw [show z = scaled_indicator 1 (∅ : Finset α) by
      funext i
      simp [z, scaled_indicator]]
    exact gs_poisson_terminal_potential_eq (fun _ : Set α ↦ (1 : ℝ)) ∅
  have hoval : multilinear_extension (fun _ : Set α ↦ (1 : ℝ)) o = 1 := by
    rw [show o = scaled_indicator 1 (Finset.univ : Finset α) by
      funext i
      simp [o, scaled_indicator]]
    exact gs_poisson_terminal_potential_eq (fun _ : Set α ↦ (1 : ℝ)) Finset.univ
  linarith

@[blueprint "lem:gs-poisson-multilinear-constant-sub"
  (statement := /-- On the unit cube, the multilinear extension of
  $S\mapsto c-f(S)$ equals $c-F_f(x)$. -/)
  (proof := /-- Expand \cref{def:multilinear-extension}, distribute the finite
  sum, and use \cref{lem:gs-poisson-multilinear-one} to identify the sum of
  the multilinear weights with one. -/)
  (title := /-- Multilinear extension of a constant difference -/)
  (latexEnv := "lemma")]
lemma gs_poisson_multilinear_constant_sub {α : Type*} [Fintype α]
    [DecidableEq α] (f : Set α → ℝ) (c : ℝ) {x : α → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    multilinear_extension (fun S ↦ c - f S) x = c - multilinear_extension f x := by
  classical
  have hone := gs_poisson_multilinear_one (α := α) hx
  unfold multilinear_extension at hone ⊢
  calc
    ∑ S ∈ (Finset.univ : Finset α).powerset,
        ((fun S ↦ c - f S) (↑S : Set α) * ∏ i ∈ S, x i) *
          ∏ i ∈ Finset.univ \ S, (1 - x i) =
        ∑ S ∈ (Finset.univ : Finset α).powerset,
          ((c * ∏ i ∈ S, x i) * ∏ i ∈ Finset.univ \ S, (1 - x i) -
            (f (↑S : Set α) * ∏ i ∈ S, x i) *
              ∏ i ∈ Finset.univ \ S, (1 - x i)) := by
      apply Finset.sum_congr rfl
      intro S hS
      ring
    _ = (∑ S ∈ (Finset.univ : Finset α).powerset,
          (c * ∏ i ∈ S, x i) * ∏ i ∈ Finset.univ \ S, (1 - x i)) -
        ∑ S ∈ (Finset.univ : Finset α).powerset,
          (f (↑S : Set α) * ∏ i ∈ S, x i) *
            ∏ i ∈ Finset.univ \ S, (1 - x i) := by
      rw [Finset.sum_sub_distrib]
    _ = c - ∑ S ∈ (Finset.univ : Finset α).powerset,
          (f (↑S : Set α) * ∏ i ∈ S, x i) *
            ∏ i ∈ Finset.univ \ S, (1 - x i) := by
      have hc : ∑ S ∈ (Finset.univ : Finset α).powerset,
          (c * ∏ i ∈ S, x i) * ∏ i ∈ Finset.univ \ S, (1 - x i) = c := by
        calc
          _ = c * ∑ S ∈ (Finset.univ : Finset α).powerset,
              ((1 : ℝ) * ∏ i ∈ S, x i) *
                ∏ i ∈ Finset.univ \ S, (1 - x i) := by
            simp only [one_mul, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro S hS
            ring
          _ = c := by rw [hone]; ring
      rw [hc]

@[blueprint "lem:gs-poisson-multilinear-gradient-bound"
  (statement := /-- For a monotone submodular set function, every point $x$ of
  the unit cube and finite set $O$ satisfy
  $f(O)-F(x)\leq\sum_{i\in O}\nabla_iF(x)$. -/)
  (proof := /-- Apply \cref{lem:gs-poisson-discrete-gradient-bound} to every
  finite subset of the ground set.  Monotonicity of multilinear extension in
  its set-function argument from
  \cref{lem:gs-poisson-multilinear-monotone-function}, together with
  \cref{lem:gs-poisson-multilinear-constant-sub} and linearity from
  \cref{lem:gs-poisson-multilinear-sum}, turns the pointwise inequality into an
  inequality of extensions.  Finally bound each extended discrete marginal by
  \cref{lem:gs-poisson-discrete-marginal-extension-le}. -/)
  (title := /-- Gradient lower bound for the multilinear extension -/)
  (latexEnv := "lemma")]
lemma gs_poisson_multilinear_gradient_bound {α : Type*} [Fintype α]
    [DecidableEq α] {f : Set α → ℝ} (hfmono : Monotone f)
    (hfsubmod : is_submodular_set_function f) {x : α → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (O : Finset α) :
    f (↑O : Set α) - multilinear_extension f x ≤
      ∑ i ∈ O, multilinear_marginal f x i := by
  classical
  let g : α → Set α → ℝ := fun i S ↦ f (insert i S) - f S
  have hpoint : ∀ S : Set α, f (↑O : Set α) - f S ≤ ∑ i ∈ O, g i S := by
    intro S
    let T : Finset α := Finset.univ.filter (fun i ↦ i ∈ S)
    have hTS : (↑T : Set α) = S := by
      ext i
      simp [T]
    simpa [g, hTS] using gs_poisson_discrete_gradient_bound hfmono hfsubmod T O
  have hmono := gs_poisson_multilinear_monotone_function hpoint hx
  rw [gs_poisson_multilinear_constant_sub f (f (↑O : Set α)) hx,
    gs_poisson_multilinear_sum O g x] at hmono
  apply hmono.trans
  apply Finset.sum_le_sum
  intro i hi
  exact gs_poisson_discrete_marginal_extension_le hfmono hx i

@[blueprint "lem:gs-poisson-exchange-potential-bound"
  (statement := /-- Let $A$ be a finite set, let $i\in A$, and put
  $B=A-i+j$.  For $0\leq t\leq1$, the potential increment from $A$ to $B$ is
  at least $t(\nabla_jF(t\mathbf1_A)-\nabla_iF(t\mathbf1_A))$. -/)
  (proof := /-- First set coordinate $i$ to zero and then coordinate $j$ to
  $t$.  The coordinate difference formula
  \cref{lem:gs-poisson-multilinear-coordinate-difference} identifies both
  changes.  Removing coordinate $i$ can only increase the $j$th marginal by
  \cref{lem:gs-poisson-marginal-antitone}; the $i$th marginal is independent
  of its own coordinate. -/)
  (title := /-- Potential gain under one exchange -/)
  (latexEnv := "lemma")]
lemma gs_poisson_exchange_potential_bound {α : Type*} [Fintype α]
    [DecidableEq α] {M : Matroid α} {f : Set α → ℝ} (hfmono : Monotone f)
    (hfsubmod : is_submodular_set_function f) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (A : Finset α) (i : α) (hi : i ∈ A)
    (j : α) (hA : M.IsBase (↑A : Set α))
    (hB : M.IsBase (↑(insert j (A.erase i)) : Set α)) :
    t * (multilinear_marginal f (scaled_indicator t A) j -
        multilinear_marginal f (scaled_indicator t A) i) ≤
      multilinear_extension f (scaled_indicator t (insert j (A.erase i))) -
        multilinear_extension f (scaled_indicator t A) := by
  let x := scaled_indicator t A
  let x0 := Function.update x i 0
  have hx : ∀ k, 0 ≤ x k ∧ x k ≤ 1 := by
    intro k
    simp only [x, scaled_indicator]
    split <;> constructor <;> linarith
  have hx0 : ∀ k, 0 ≤ x0 k ∧ x0 k ≤ 1 := by
    intro k
    by_cases hki : k = i
    · subst k
      simp [x0, Function.update]
    · simpa [x0, Function.update, hki] using hx k
  have hx0x : ∀ k, x0 k ≤ x k := by
    intro k
    by_cases hki : k = i
    · subst k
      simp [x0, Function.update, x, scaled_indicator, hi, ht0]
    · simp [x0, Function.update, hki]
  have hremove : scaled_indicator t (A.erase i) = x0 := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [x0, x, scaled_indicator]
    · simp [x0, x, scaled_indicator, hki]
  have horiginal : Function.update x0 i t = x := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [x0, x, Function.update, scaled_indicator, hi]
    · simp [x0, Function.update, hki]
  have hfinal : Function.update x0 j t =
      scaled_indicator t (insert j (A.erase i)) := by
    funext k
    by_cases hkj : k = j
    · subst k
      simp [x0, x, Function.update, scaled_indicator]
    · by_cases hki : k = i
      · subst k
        simp [x0, x, Function.update, scaled_indicator, hkj]
      · simp [x0, x, Function.update, scaled_indicator, hkj, hki]
  by_cases hji : j = i
  · subst j
    simp [Finset.insert_erase hi]
  · have hjnot : j ∉ A.erase i := by
      intro hjmem
      have hBerase : M.IsBase (↑(A.erase i) : Set α) := by
        simpa [Finset.insert_eq_of_mem hjmem] using hB
      have heqset : (↑(A.erase i) : Set α) = (↑A : Set α) :=
        hBerase.eq_of_subset_isBase hA (by intro k hk; simp_all)
      have heqfin : A.erase i = A := by exact_mod_cast heqset
      have : i ∉ A := by rw [← heqfin]; simp
      exact this hi
    have hjA : j ∉ A := by
      simpa [Finset.mem_erase, hji] using hjnot
    have hjzero : Function.update x0 j 0 = x0 := by
      funext k
      by_cases hkj : k = j
      · subst k
        simp [x0, x, Function.update, scaled_indicator, hjA]
      · simp [Function.update, hkj]
    have hjmono := gs_poisson_marginal_antitone hfmono hfsubmod hx0 hx hx0x j
    have hmi : multilinear_marginal f x0 i = multilinear_marginal f x i := by
      unfold multilinear_marginal x0
      simp [Function.update]
    have hi0 : Function.update x0 i 0 = x0 := by
      funext k
      by_cases hki : k = i <;> simp [x0, Function.update, hki]
    have hadd := gs_poisson_multilinear_coordinate_difference f x0 j 0 t
    rw [hjzero] at hadd
    have hdel := gs_poisson_multilinear_coordinate_difference f x0 i t 0
    rw [horiginal, hi0] at hdel
    rw [hfinal] at hadd
    change t * (multilinear_marginal f x j - multilinear_marginal f x i) ≤
      multilinear_extension f (scaled_indicator t (insert j (A.erase i))) -
        multilinear_extension f x
    rw [hmi] at hdel
    nlinarith

@[blueprint "lem:gs-poisson-pmf-map-expectation"
  (statement := /-- On finite types, expectation under the pushforward of a
  probability mass function equals expectation after composition with the
  pushing map. -/)
  (proof := /-- Expand the pushed-forward masses as finite sums over fibers,
  commute the two finite sums, and retain the unique term indexed by the image
  of each source point. -/)
  (title := /-- Expectation under a pushed-forward PMF -/)
  (latexEnv := "lemma")]
lemma gs_poisson_pmf_map_expectation {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (g : α → β) (h : β → ℝ) :
    ∑ b, ((p.map g) b).toReal * h b = ∑ a, (p a).toReal * h (g a) := by
  classical
  simp only [PMF.map_apply, tsum_fintype]
  have hreal (b : β) : (∑ a, if b = g a then p a else 0).toReal =
      ∑ a, (if b = g a then p a else 0).toReal := by
    apply ENNReal.toReal_sum
    intro a ha
    split
    · exact PMF.apply_ne_top p a
    · simp
  simp_rw [hreal]
  simp only [ENNReal.toReal_zero, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_eq_single (g a)]
  · simp
  · intro b hb hne
    simp [hne]
  · simp

@[blueprint "lem:gs-poisson-uniform-expectation"
  (statement := /-- The expectation of a real-valued function under the uniform
  probability mass function on a nonempty finite set $A$ is its sum over $A$
  divided by $|A|$. -/)
  (proof := /-- Expand the uniform mass function: its value is $|A|^{-1}$ on
  $A$ and zero off $A$.  Split the ambient finite sum into these two parts and
  factor out the constant weight. -/)
  (title := /-- Expectation under a finite uniform law -/)
  (latexEnv := "lemma")]
lemma gs_poisson_uniform_expectation {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset α) (hA : A.Nonempty) (g : α → ℝ) :
    ∑ i, ((PMF.uniformOfFinset A hA) i).toReal * g i =
      (1 / (A.card : ℝ)) * ∑ i ∈ A, g i := by
  simp only [PMF.uniformOfFinset_apply]
  have hc : ((↑A.card)⁻¹ : ENNReal).toReal = 1 / (A.card : ℝ) := by
    rw [ENNReal.toReal_inv]
    simp
  rw [Finset.mul_sum, ← hc]
  trans ∑ i, if i ∈ A then ((↑A.card)⁻¹ : ENNReal).toReal * g i else 0
  · apply Finset.sum_congr rfl
    intro i hi
    by_cases hiA : i ∈ A <;> simp [hiA]
  · rw [← Finset.sum_filter]
    simp

@[blueprint "lem:gs-poisson-base-drift-bound"
  (statement := /-- At every admissible positive time and current base $A$, the
  instantaneous GS--Poisson drift is at least $f(O)-F(t\mathbf1_A)$. -/)
  (proof := /-- The greedy base has total marginal at least that of $O$, which
  is at least $f(O)-F(t\mathbf1_A)$ by
  \cref{lem:gs-poisson-multilinear-gradient-bound}.  Reindex its marginal sum
  through the exchange bijection.  The one-step estimate
  \cref{lem:gs-poisson-exchange-potential-bound}, averaged using
  \cref{lem:gs-poisson-pmf-map-expectation,
  lem:gs-poisson-uniform-expectation}, shows that the jump term cancels the
  current-base marginal sum after multiplication by the rate $|A|/t$. -/)
  (title := /-- Conditional drift bound at a base -/)
  (latexEnv := "lemma")]
lemma gs_poisson_base_drift_bound {α : Type*} [Fintype α] [DecidableEq α]
    {M : Matroid α} {f : Set α → ℝ} {ε t : ℝ}
    (D : gs_poisson_dynamics M f ε) (hεpos : 0 < ε)
    (hfmono : Monotone f) (hfsubmod : is_submodular_set_function f)
    (O A : Finset α) (hObase : M.IsBase (↑O : Set α))
    (hA : M.IsBase (↑A : Set α)) (ht0 : ε ≤ t) (ht1 : t ≤ 1) :
    f (↑O : Set α) - multilinear_extension f (scaled_indicator t A) ≤
      (∑ i ∈ A, multilinear_marginal f (scaled_indicator t A) i) +
        D.rate t * ∑ B : Finset α, ((gs_poisson_swap_law D t A) B).toReal *
          (multilinear_extension f (scaled_indicator t B) -
            multilinear_extension f (scaled_indicator t A)) := by
  have htpos : 0 < t := lt_of_lt_of_le hεpos ht0
  have htunit : ∀ i, 0 ≤ scaled_indicator t A i ∧ scaled_indicator t A i ≤ 1 := by
    intro i
    simp only [scaled_indicator]
    split <;> constructor <;> linarith
  let Z := D.greedyBase t A
  have hZ := (D.greedy_base_spec ht0 ht1 hA).1
  have hgreedy := (D.greedy_base_spec ht0 ht1 hA).2 O hObase
  have hgrad := gs_poisson_multilinear_gradient_bound hfmono hfsubmod htunit O
  by_cases hAempty : A = ∅
  · subst A
    have hOempty : O = ∅ := by
      have heq := hA.eq_of_subset_isBase hObase (by simp)
      exact_mod_cast heq.symm
    subst O
    have hsum : ∑ B : Finset α,
        ((gs_poisson_swap_law D t ∅) B).toReal *
          (multilinear_extension f (scaled_indicator t B) -
            multilinear_extension f (scaled_indicator t ∅)) = 0 := by
      apply Finset.sum_eq_zero
      intro B hB
      by_cases hBe : B = ∅
      · subst B
        simp
      · simp [gs_poisson_swap_law, ht0, ht1, hA, PMF.pure_apply, hBe]
    rw [hsum, mul_zero, add_zero]
    simpa using hgrad
  · have hAne : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hAempty
    let e := D.exchange t A ht0 ht1 hA
    let swap : α → Finset α := fun i ↦ if hi : i ∈ A then
      insert ((e.equiv ⟨i, hi⟩).1) (A.erase i) else A
    have hswap : gs_poisson_swap_law D t A =
        PMF.map swap (PMF.uniformOfFinset A hAne) := by
      simp [gs_poisson_swap_law, ht0, ht1, hA, hAne, swap, e,
        D.uniform_swap_law_spec]
    let H : Finset α → ℝ := fun B ↦
      multilinear_extension f (scaled_indicator t B) -
        multilinear_extension f (scaled_indicator t A)
    have hexpect : ∑ B : Finset α, ((gs_poisson_swap_law D t A) B).toReal * H B =
        (1 / (A.card : ℝ)) * ∑ i ∈ A, H (swap i) := by
      rw [hswap, gs_poisson_pmf_map_expectation,
        gs_poisson_uniform_expectation]
    have hgain : t * (∑ i ∈ Z, multilinear_marginal f (scaled_indicator t A) i -
        ∑ i ∈ A, multilinear_marginal f (scaled_indicator t A) i) ≤
        ∑ i ∈ A, H (swap i) := by
      let m : α → ℝ := fun i ↦ multilinear_marginal f (scaled_indicator t A) i
      have hZsum : ∑ i ∈ Z, m i = ∑ z : Z, m z.1 :=
        Finset.sum_subtype Z (fun _ ↦ Iff.rfl) m
      have hAsum : ∑ i ∈ A, m i = ∑ a : A, m a.1 :=
        Finset.sum_subtype A (fun _ ↦ Iff.rfl) m
      have hequiv : ∑ a : A, m (e.equiv a).1 = ∑ z : Z, m z.1 :=
        e.equiv.sum_comp (fun z : Z ↦ m z.1)
      have hrhs : ∑ i ∈ A, H (swap i) =
          ∑ a : A, H (insert (e.equiv a).1 (A.erase a.1)) := by
        rw [Finset.sum_subtype A (fun _ ↦ Iff.rfl) (fun i ↦ H (swap i))]
        apply Finset.sum_congr rfl
        intro a ha
        simp [swap, a.property]
      calc
        t * (∑ i ∈ Z, multilinear_marginal f (scaled_indicator t A) i -
            ∑ i ∈ A, multilinear_marginal f (scaled_indicator t A) i) =
            ∑ a : A, t * (m (e.equiv a).1 - m a.1) := by
          rw [hZsum, hAsum, ← hequiv]
          simp only [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
        _ ≤ ∑ a : A, H (insert (e.equiv a).1 (A.erase a.1)) := by
          apply Finset.sum_le_sum
          intro a ha
          simpa [H, m] using
            gs_poisson_exchange_potential_bound hfmono hfsubmod
              (le_of_lt htpos) ht1 A a.1 a.property (e.equiv a).1 hA
              (e.valid a)
        _ = ∑ i ∈ A, H (swap i) := hrhs.symm
    have hcard : D.initial.card = A.card := by
      have heq := D.initial_isBase.encard_eq_encard_of_isBase hA
      exact_mod_cast heq
    have hcardpos : 0 < (A.card : ℝ) := by exact_mod_cast hAne.card_pos
    rw [D.rate_spec ht0 ht1, hcard, hexpect]
    have hscaled := mul_le_mul_of_nonneg_left hgain (le_of_lt (one_div_pos.mpr htpos))
    have hfactor (u : ℝ) : ((A.card : ℝ) / t) * (1 / (A.card : ℝ) * u) =
        (1 / t) * u := by
      field_simp
    rw [hfactor]
    have hscaled' :
        (∑ i ∈ Z, multilinear_marginal f (scaled_indicator t A) i -
          ∑ i ∈ A, multilinear_marginal f (scaled_indicator t A) i) ≤
            (1 / t) * ∑ i ∈ A, H (swap i) := by
      calc
        _ = (1 / t) * (t *
            (∑ i ∈ Z, multilinear_marginal f (scaled_indicator t A) i -
              ∑ i ∈ A, multilinear_marginal f (scaled_indicator t A) i)) := by
          field_simp
        _ ≤ _ := hscaled
    linarith

@[blueprint "lem:gs-poisson-pmf-real-masses-sum"
  (statement := /-- On a finite sample space, the real values of the masses of
  a probability mass function sum to one. -/)
  (proof := /-- Convert the defining extended-nonnegative summation identity
  for a probability mass function to the reals; every individual mass is
  finite. -/)
  (title := /-- Sum of real PMF masses -/)
  (latexEnv := "lemma")]
lemma gs_poisson_pmf_real_masses_sum {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_one, ← PMF.tsum_coe p, tsum_fintype]
  rw [ENNReal.toReal_sum]
  intro a ha
  exact PMF.apply_ne_top p a

@[blueprint "lem:gs-poisson-expected-drift-bound"
  (statement := /-- At every admissible time, if a probability mass function is
  supported on bases, its expected GS--Poisson drift is at least the optimal
  value minus its expected potential. -/)
  (proof := /-- Apply \cref{lem:gs-poisson-base-drift-bound} at each base in the
  support, multiply by its nonnegative probability, and sum.  Terms outside
  the support have zero mass.  Expanding
  \cref{def:gs-poisson-expected-potential,
  def:gs-poisson-expected-drift} and using
  \cref{lem:gs-poisson-pmf-real-masses-sum} identifies the resulting sums. -/)
  (title := /-- Expected GS--Poisson drift bound -/)
  (latexEnv := "lemma")]
lemma gs_poisson_expected_drift_bound {α : Type*} [Fintype α] [DecidableEq α]
    {M : Matroid α} {f : Set α → ℝ} {ε t : ℝ}
    (D : gs_poisson_dynamics M f ε) (hεpos : 0 < ε)
    (hfmono : Monotone f) (hfsubmod : is_submodular_set_function f)
    (O : Finset α) (hObase : M.IsBase (↑O : Set α))
    (q : PMF (Finset α))
    (hq : ∀ A : Finset α, A ∈ q.support → M.IsBase (↑A : Set α))
    (ht0 : ε ≤ t) (ht1 : t ≤ 1) :
    f (↑O : Set α) - gs_poisson_expected_potential D t q ≤
      gs_poisson_expected_drift D t q := by
  classical
  have hmass := gs_poisson_pmf_real_masses_sum q
  have hsum : ∑ A : Finset α, (q A).toReal *
      (f (↑O : Set α) - multilinear_extension f (scaled_indicator t A)) ≤
      ∑ A : Finset α, (q A).toReal *
        ((∑ i ∈ A, multilinear_marginal f (scaled_indicator t A) i) +
          D.rate t * ∑ B : Finset α, ((gs_poisson_swap_law D t A) B).toReal *
            (multilinear_extension f (scaled_indicator t B) -
              multilinear_extension f (scaled_indicator t A))) := by
    apply Finset.sum_le_sum
    intro A hAuniv
    by_cases hmassA : q A = 0
    · simp [hmassA]
    · apply mul_le_mul_of_nonneg_left
      · exact gs_poisson_base_drift_bound D hεpos hfmono hfsubmod O A hObase
          (hq A (by simpa [PMF.mem_support_iff] using hmassA)) ht0 ht1
      · positivity
  unfold gs_poisson_expected_potential gs_poisson_expected_drift
  have hleft : ∑ A : Finset α, (q A).toReal *
      (f (↑O : Set α) - multilinear_extension f (scaled_indicator t A)) =
      f (↑O : Set α) - ∑ A : Finset α, (q A).toReal *
        multilinear_extension f (scaled_indicator t A) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    have : ∑ A : Finset α, (q A).toReal * f (↑O : Set α) = f (↑O : Set α) := by
      rw [← Finset.sum_mul, hmass, one_mul]
    rw [this]
  rw [← hleft]
  exact hsum

@[blueprint "lem:gs-poisson-multilinear-absolute-bound"
  (statement := /-- If every coordinate of a vector lies in $[0,1]$, then the
  absolute value of the multilinear extension at that vector is at most the
  sum of the absolute values of the set-function values. -/)
  (proof := /-- Expand \\cref{def:multilinear-extension} and apply the triangle
  inequality.  Every coordinate factor and complementary-coordinate factor
  lies in $[0,1]$, so the absolute value of each product weight is at most
  one. -/)
  (title := /-- Uniform absolute bound for the multilinear extension -/)
  (latexEnv := "lemma")]
lemma gs_poisson_multilinear_absolute_bound {α : Type*} [Fintype α]
    [DecidableEq α] (f : Set α → ℝ) {x : α → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    |multilinear_extension f x| ≤
      ∑ S ∈ (Finset.univ : Finset α).powerset, |f (↑S : Set α)| := by
  classical
  unfold multilinear_extension
  calc
    |∑ S ∈ (Finset.univ : Finset α).powerset,
        f (↑S : Set α) * (∏ i ∈ S, x i) *
          ∏ i ∈ (Finset.univ : Finset α) \ S, (1 - x i)| ≤
        ∑ S ∈ (Finset.univ : Finset α).powerset,
          |f (↑S : Set α) * (∏ i ∈ S, x i) *
            ∏ i ∈ (Finset.univ : Finset α) \ S, (1 - x i)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ S ∈ (Finset.univ : Finset α).powerset, |f (↑S : Set α)| := by
      apply Finset.sum_le_sum
      intro S hS
      rw [abs_mul, abs_mul]
      have hprod : |∏ i ∈ S, x i| ≤ 1 := by
        rw [abs_of_nonneg (Finset.prod_nonneg fun i hi ↦ (hx i).1)]
        apply Finset.prod_le_one
        · intro i hi
          exact (hx i).1
        · intro i hi
          exact (hx i).2
      have hcompl : |∏ i ∈ (Finset.univ : Finset α) \ S, (1 - x i)| ≤ 1 := by
        rw [abs_of_nonneg (Finset.prod_nonneg fun i hi ↦
          sub_nonneg.mpr (hx i).2)]
        apply Finset.prod_le_one
        · intro i hi
          exact sub_nonneg.mpr (hx i).2
        · intro i hi
          linarith [(hx i).1]
      calc
        |f (↑S : Set α)| * |∏ i ∈ S, x i| *
            |∏ i ∈ (Finset.univ : Finset α) \ S, (1 - x i)| ≤
            |f (↑S : Set α)| * 1 * 1 := by
          gcongr
        _ = |f (↑S : Set α)| := by ring

@[blueprint "lem:gs-poisson-expected-potential-absolute-bound"
  (statement := /-- On the unit time interval, the absolute value of every
  expected multilinear potential is at most the sum of the absolute values of
  the set-function values. -/)
  (proof := /-- Expand \\cref{def:gs-poisson-expected-potential}, apply the
  triangle inequality and
  \\cref{lem:gs-poisson-multilinear-absolute-bound} termwise, and use
  \\cref{lem:gs-poisson-pmf-real-masses-sum} for the probability weights. -/)
  (title := /-- Uniform absolute bound for expected potential -/)
  (latexEnv := "lemma")]
lemma gs_poisson_expected_potential_absolute_bound {α : Type*} [Fintype α]
    [DecidableEq α] {M : Matroid α} {f : Set α → ℝ} {ε t : ℝ}
    (D : gs_poisson_dynamics M f ε) (q : PMF (Finset α))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |gs_poisson_expected_potential D t q| ≤
      ∑ S ∈ (Finset.univ : Finset α).powerset, |f (↑S : Set α)| := by
  classical
  have hcube (A : Finset α) :
      ∀ i, 0 ≤ scaled_indicator t A i ∧ scaled_indicator t A i ≤ 1 := by
    intro i
    simp only [scaled_indicator]
    split <;> constructor <;> linarith
  unfold gs_poisson_expected_potential
  calc
    |∑ A : Finset α, (q A).toReal *
        multilinear_extension f (scaled_indicator t A)| ≤
        ∑ A : Finset α, |(q A).toReal *
          multilinear_extension f (scaled_indicator t A)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ A : Finset α, (q A).toReal *
        (∑ S ∈ (Finset.univ : Finset α).powerset, |f (↑S : Set α)|) := by
      apply Finset.sum_le_sum
      intro A hA
      rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      gcongr
      exact gs_poisson_multilinear_absolute_bound f (hcube A)
    _ = ∑ S ∈ (Finset.univ : Finset α).powerset, |f (↑S : Set α)| := by
      rw [← Finset.sum_mul, gs_poisson_pmf_real_masses_sum, one_mul]

@[blueprint "lem:gs-poisson-expected-drift-absolute-bound"
  (statement := /-- For fixed positive starting time, the absolute value of the
  expected GS--Poisson drift is bounded uniformly over all admissible times
  and all probability mass functions on finite sets. -/)
  (proof := /-- Put $K=\sum_{S\subseteq U}|f(S)|$.  By
  \\cref{lem:gs-poisson-multilinear-absolute-bound}, every potential on the
  cube has absolute value at most $K$, and hence every marginal and every
  potential difference has absolute value at most $2K$.  The two probability
  averages have total mass one by
  \\cref{lem:gs-poisson-pmf-real-masses-sum}.  Finally, the rate is at most
  $|U|/\varepsilon$ on the admissible interval. -/)
  (title := /-- Uniform absolute bound for expected GS--Poisson drift -/)
  (latexEnv := "lemma")]
lemma gs_poisson_expected_drift_absolute_bound {α : Type*} [Fintype α]
    [DecidableEq α] {M : Matroid α} {f : Set α → ℝ} {ε : ℝ}
    (D : gs_poisson_dynamics M f ε) (hεpos : 0 < ε) :
    ∃ C : ℝ, ∀ (t : ℝ) (q : PMF (Finset α)), ε ≤ t → t ≤ 1 →
      |gs_poisson_expected_drift D t q| ≤ C := by
  classical
  let K : ℝ := ∑ S ∈ (Finset.univ : Finset α).powerset, |f (↑S : Set α)|
  let n : ℝ := Fintype.card α
  refine ⟨n * (2 * K) + (n / ε) * (2 * K), ?_⟩
  intro t q ht0 ht1
  have htpos : 0 < t := lt_of_lt_of_le hεpos ht0
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hn : 0 ≤ n := by
    dsimp [n]
    positivity
  have hcube (A : Finset α) :
      ∀ i, 0 ≤ scaled_indicator t A i ∧ scaled_indicator t A i ≤ 1 := by
    intro i
    simp only [scaled_indicator]
    split <;> constructor <;> linarith
  have hF (A : Finset α) :
      |multilinear_extension f (scaled_indicator t A)| ≤ K := by
    simpa [K] using gs_poisson_multilinear_absolute_bound f (hcube A)
  have hmarg (A : Finset α) (i : α) :
      |multilinear_marginal f (scaled_indicator t A) i| ≤ 2 * K := by
    have hzero : ∀ j, 0 ≤ Function.update (scaled_indicator t A) i 0 j ∧
        Function.update (scaled_indicator t A) i 0 j ≤ 1 := by
      intro j
      by_cases hji : j = i
      · subst j
        simp
      · simpa [Function.update, hji] using hcube A j
    have hone : ∀ j, 0 ≤ Function.update (scaled_indicator t A) i 1 j ∧
        Function.update (scaled_indicator t A) i 1 j ≤ 1 := by
      intro j
      by_cases hji : j = i
      · subst j
        simp
      · simpa [Function.update, hji] using hcube A j
    have h0 := gs_poisson_multilinear_absolute_bound f hzero
    have h1 := gs_poisson_multilinear_absolute_bound f hone
    unfold multilinear_marginal
    calc
      |multilinear_extension f (Function.update (scaled_indicator t A) i 1) -
          multilinear_extension f (Function.update (scaled_indicator t A) i 0)| ≤
          |multilinear_extension f
            (Function.update (scaled_indicator t A) i 1)| +
          |multilinear_extension f
            (Function.update (scaled_indicator t A) i 0)| := abs_sub _ _
      _ ≤ 2 * K := by simpa [K, two_mul] using add_le_add h1 h0
  have hrate : |D.rate t| ≤ n / ε := by
    rw [D.rate_spec ht0 ht1,
      abs_of_nonneg (div_nonneg (by positivity) (le_of_lt htpos))]
    dsimp [n]
    have hcard : (D.initial.card : ℝ) ≤ Fintype.card α := by
      exact_mod_cast D.initial.card_le_univ
    apply (div_le_div_iff₀ htpos hεpos).2
    nlinarith [show (0 : ℝ) ≤ D.initial.card by positivity]
  have hcomponent (A : Finset α) :
      |(∑ i ∈ A, multilinear_marginal f (scaled_indicator t A) i) +
        D.rate t * ∑ B : Finset α, ((gs_poisson_swap_law D t A) B).toReal *
          (multilinear_extension f (scaled_indicator t B) -
            multilinear_extension f (scaled_indicator t A))| ≤
        n * (2 * K) + (n / ε) * (2 * K) := by
    have hmargs :
        |∑ i ∈ A, multilinear_marginal f (scaled_indicator t A) i| ≤
          n * (2 * K) := by
      calc
        |∑ i ∈ A, multilinear_marginal f (scaled_indicator t A) i| ≤
            ∑ i ∈ A, |multilinear_marginal f (scaled_indicator t A) i| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ A, 2 * K := by
          apply Finset.sum_le_sum
          intro i hi
          exact hmarg A i
        _ = (A.card : ℝ) * (2 * K) := by simp
        _ ≤ n * (2 * K) := by
          gcongr
          dsimp [n]
          exact_mod_cast A.card_le_univ
    have hjump :
        |∑ B : Finset α, ((gs_poisson_swap_law D t A) B).toReal *
          (multilinear_extension f (scaled_indicator t B) -
            multilinear_extension f (scaled_indicator t A))| ≤ 2 * K := by
      calc
        |∑ B : Finset α, ((gs_poisson_swap_law D t A) B).toReal *
            (multilinear_extension f (scaled_indicator t B) -
              multilinear_extension f (scaled_indicator t A))| ≤
            ∑ B : Finset α, |((gs_poisson_swap_law D t A) B).toReal *
              (multilinear_extension f (scaled_indicator t B) -
                multilinear_extension f (scaled_indicator t A))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ B : Finset α, ((gs_poisson_swap_law D t A) B).toReal *
            (2 * K) := by
          apply Finset.sum_le_sum
          intro B hB
          rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
          gcongr
          exact (abs_sub _ _).trans (by
            simpa [two_mul] using add_le_add (hF B) (hF A))
        _ = 2 * K := by
          rw [← Finset.sum_mul, gs_poisson_pmf_real_masses_sum, one_mul]
    calc
      |(∑ i ∈ A, multilinear_marginal f (scaled_indicator t A) i) +
          D.rate t * ∑ B : Finset α, ((gs_poisson_swap_law D t A) B).toReal *
            (multilinear_extension f (scaled_indicator t B) -
              multilinear_extension f (scaled_indicator t A))| ≤
          |∑ i ∈ A, multilinear_marginal f (scaled_indicator t A) i| +
            |D.rate t| * |∑ B : Finset α,
              ((gs_poisson_swap_law D t A) B).toReal *
                (multilinear_extension f (scaled_indicator t B) -
                  multilinear_extension f (scaled_indicator t A))| := by
            simpa [abs_mul] using
              (abs_add_le
                (∑ i ∈ A, multilinear_marginal f (scaled_indicator t A) i)
                (D.rate t * ∑ B : Finset α,
                  ((gs_poisson_swap_law D t A) B).toReal *
                    (multilinear_extension f (scaled_indicator t B) -
                      multilinear_extension f (scaled_indicator t A))))
      _ ≤ n * (2 * K) + (n / ε) * (2 * K) := by
        gcongr
  unfold gs_poisson_expected_drift
  calc
    |∑ A : Finset α, (q A).toReal *
        ((∑ i ∈ A, multilinear_marginal f (scaled_indicator t A) i) +
          D.rate t * ∑ B : Finset α, ((gs_poisson_swap_law D t A) B).toReal *
            (multilinear_extension f (scaled_indicator t B) -
              multilinear_extension f (scaled_indicator t A)))| ≤
        ∑ A : Finset α, |(q A).toReal *
          ((∑ i ∈ A, multilinear_marginal f (scaled_indicator t A) i) +
            D.rate t * ∑ B : Finset α, ((gs_poisson_swap_law D t A) B).toReal *
              (multilinear_extension f (scaled_indicator t B) -
                multilinear_extension f (scaled_indicator t A)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ A : Finset α, (q A).toReal *
        (n * (2 * K) + (n / ε) * (2 * K)) := by
      apply Finset.sum_le_sum
      intro A hA
      rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      gcongr
      exact hcomponent A
    _ = n * (2 * K) + (n / ε) * (2 * K) := by
      rw [← Finset.sum_mul, gs_poisson_pmf_real_masses_sum, one_mul]

@[blueprint "lem:gs-poisson-expected-potential-le-optimum"
  (statement := /-- If a probability mass function is supported on bases and
  $O$ is optimal among independent sets, then at every time in $[0,1]$ its
  expected multilinear potential is at most $f(O)$. -/)
  (proof := /-- Coordinatewise monotonicity from
  \\cref{lem:gs-poisson-multilinear-monotone} compares each scaled indicator
  with the terminal indicator.  The terminal identity
  \\cref{lem:gs-poisson-terminal-potential-eq} and optimality of $O$ bound
  every positive-mass term by $f(O)$.  Sum the inequalities and use
  \\cref{lem:gs-poisson-pmf-real-masses-sum}. -/)
  (title := /-- Expected potential is bounded by the optimum -/)
  (latexEnv := "lemma")]
lemma gs_poisson_expected_potential_le_optimum {α : Type*} [Fintype α]
    [DecidableEq α] {M : Matroid α} {f : Set α → ℝ} {ε t : ℝ}
    (D : gs_poisson_dynamics M f ε) (hfmono : Monotone f)
    (O : Finset α)
    (hOoptimal : ∀ B : Finset α, M.Indep (↑B : Set α) →
      f (↑B : Set α) ≤ f (↑O : Set α))
    (q : PMF (Finset α))
    (hq : ∀ A : Finset α, A ∈ q.support → M.IsBase (↑A : Set α))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    gs_poisson_expected_potential D t q ≤ f (↑O : Set α) := by
  classical
  unfold gs_poisson_expected_potential
  calc
    ∑ A : Finset α, (q A).toReal *
        multilinear_extension f (scaled_indicator t A) ≤
        ∑ A : Finset α, (q A).toReal * f (↑O : Set α) := by
      apply Finset.sum_le_sum
      intro A hA
      by_cases hmass : q A = 0
      · simp [hmass]
      · apply mul_le_mul_of_nonneg_left
        · calc
            multilinear_extension f (scaled_indicator t A) ≤
                multilinear_extension f (scaled_indicator 1 A) := by
              apply gs_poisson_multilinear_monotone hfmono
              · intro i
                simp only [scaled_indicator]
                split <;> constructor <;> linarith
              · intro i
                simp only [scaled_indicator]
                split <;> simp
              · intro i
                simp only [scaled_indicator]
                split <;> linarith
            _ = f (↑A : Set α) := gs_poisson_terminal_potential_eq f A
            _ ≤ f (↑O : Set α) :=
              hOoptimal A (hq A (by simpa [PMF.mem_support_iff] using hmass)).indep
        · positivity
    _ = f (↑O : Set α) := by
      rw [← Finset.sum_mul, gs_poisson_pmf_real_masses_sum, one_mul]

@[blueprint "lem:gs-poisson-integral-comparison"
  (statement := /-- Let $0<\varepsilon\leq1$ and $c\geq0$.  Suppose that
  $y,d\colon\mathbb R\to\mathbb R$, that $d$ is integrable on
  $[\varepsilon,1]$, that $0\leq y\leq c$ there, that increments of $y$ are
  interval integrals of $d$, and that $d(t)\geq c-y(t)$.  Then
  $y(1)\geq(1-\varepsilon)(1-e^{-1})c$. -/)
  (proof := /-- The chord inequality
  \\cref{lem:gs-poisson-exponential-chord} handles the degenerate
  zero-length interval.  Otherwise, the drift bound and $y\leq c$ first imply that $y$ is
  nondecreasing.  Divide $[\varepsilon,1]$ into $n$ equal pieces.  On each
  piece, monotonicity gives
  $(1+\delta)(c-y(t_{j+1}))\leq c-y(t_j)$, where
  $\delta=(1-\varepsilon)/n$.  Iteration yields
  $(1+\delta)^n(c-y(1))\leq c$.  Letting $n$ tend to infinity and using the
  Strict convexity of the exponential leaves positive slack between the
  desired chord and the exact exponential curve because
  $\varepsilon>0$.  A sufficiently fine finite partition, together with
  $e^x\leq(1-x)^{-1}$ for $0\leq x<1$, absorbs this slack and gives the
  claimed chord bound. -/)
  (title := /-- Integral comparison with exponential decay -/)
  (latexEnv := "lemma")]
lemma gs_poisson_integral_comparison {ε c : ℝ} (hεpos : 0 < ε)
    (hεone : ε ≤ 1) (hc : 0 ≤ c) (y d : ℝ → ℝ)
    (hdint : IntervalIntegrable d MeasureTheory.volume ε 1)
    (hy0 : ∀ t, ε ≤ t → t ≤ 1 → 0 ≤ y t)
    (hyc : ∀ t, ε ≤ t → t ≤ 1 → y t ≤ c)
    (hevol : ∀ s t, ε ≤ s → s ≤ t → t ≤ 1 →
      y t - y s = ∫ u in s..t, d u)
    (hdrift : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Icc ε 1),
      c - y t ≤ d t) :
    (1 - ε) * (1 - 1 / Real.exp 1) * c ≤ y 1 := by
  have hmono : MonotoneOn y (Set.Icc ε 1) := by
    intro s hs t ht hst
    rw [← sub_nonneg, hevol s t hs.1 hst ht.2]
    apply intervalIntegral.integral_nonneg_of_ae_restrict hst
    have hdrift' :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset
        (Set.Icc_subset_Icc hs.1 ht.2) hdrift
    filter_upwards [hdrift', MeasureTheory.ae_restrict_mem measurableSet_Icc]
      with u hudrift hu
    have hu' : u ∈ Set.Icc ε 1 :=
      ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩
    exact (sub_nonneg.mpr (hyc u hu'.1 hu'.2)).trans
      hudrift
  have hstep {s t : ℝ} (hs : s ∈ Set.Icc ε 1)
      (ht : t ∈ Set.Icc ε 1) (hst : s ≤ t) :
      (1 + (t - s)) * (c - y t) ≤ c - y s := by
    have hdint' : IntervalIntegrable d MeasureTheory.volume s t := by
      apply hdint.mono_set
      rw [Set.uIcc_of_le hst, Set.uIcc_of_le hεone]
      exact Set.Icc_subset_Icc hs.1 ht.2
    have hint : (t - s) * (c - y t) ≤ ∫ u in s..t, d u := by
      calc
        (t - s) * (c - y t) = ∫ _ in s..t, c - y t := by
          simp
          ring
        _ ≤ ∫ u in s..t, d u := by
          apply intervalIntegral.integral_mono_ae_restrict
            (f := fun _ ↦ c - y t) (g := d)
            hst intervalIntegrable_const hdint'
          have hdrift' :=
            MeasureTheory.ae_restrict_of_ae_restrict_of_subset
              (Set.Icc_subset_Icc hs.1 ht.2) hdrift
          filter_upwards [hdrift', MeasureTheory.ae_restrict_mem measurableSet_Icc]
            with u hudrift hu
          have hu' : u ∈ Set.Icc ε 1 :=
            ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩
          exact (sub_le_sub_left (hmono hu' ht hu.2) c).trans
            hudrift
    rw [← hevol s t hs.1 hst ht.2] at hint
    linarith
  let a : ℝ := 1 - ε
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hEuler : ∀ n : ℕ, 0 < n →
      (1 + a / (n : ℝ)) ^ n * (c - y 1) ≤ c := by
    intro n hn
    let δ : ℝ := a / (n : ℝ)
    let T : ℕ → ℝ := fun j ↦ ε + (j : ℝ) * δ
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hδ : 0 ≤ δ := div_nonneg ha (le_of_lt hnreal)
    have hTmem : ∀ j : ℕ, j ≤ n → T j ∈ Set.Icc ε 1 := by
      intro j hj
      have hjreal : (j : ℝ) ≤ n := by exact_mod_cast hj
      constructor
      · dsimp [T]
        exact le_add_of_nonneg_right (mul_nonneg (by positivity) hδ)
      · dsimp [T, δ, a]
        have hratio : (j : ℝ) / (n : ℝ) ≤ 1 :=
          (div_le_one hnreal).2 hjreal
        calc
          ε + (j : ℝ) * ((1 - ε) / (n : ℝ)) =
              ε + (1 - ε) * ((j : ℝ) / (n : ℝ)) := by ring
          _ ≤ ε + (1 - ε) * 1 := by gcongr
          _ = 1 := by ring
    have hTzero : T 0 = ε := by simp [T]
    have hTn : T n = 1 := by
      dsimp [T, δ, a]
      field_simp
      ring
    have hind : ∀ j : ℕ, j ≤ n →
        (1 + δ) ^ j * (c - y (T j)) ≤ c := by
      intro j hj
      induction j with
      | zero =>
          simp only [pow_zero, one_mul, hTzero]
          linarith [hy0 ε (le_refl ε) hεone]
      | succ j ih =>
          have hjn : j ≤ n := Nat.le_trans (Nat.le_succ j) hj
          have hnext : T (j + 1) - T j = δ := by
            dsimp [T]
            push_cast
            ring
          have hrel := hstep (hTmem j hjn) (hTmem (j + 1) hj)
            (by
              rw [← sub_nonneg, hnext]
              exact hδ)
          rw [hnext] at hrel
          rw [pow_succ]
          calc
            (1 + δ) ^ j * (1 + δ) * (c - y (T (j + 1))) =
                (1 + δ) ^ j * ((1 + δ) * (c - y (T (j + 1)))) := by ring
            _ ≤ (1 + δ) ^ j * (c - y (T j)) := by
              exact mul_le_mul_of_nonneg_left hrel
                (pow_nonneg (by linarith) j)
            _ ≤ c := ih hjn
    simpa [δ, hTn] using hind n (le_refl n)
  have hchord :=
    gs_poisson_exponential_chord (le_of_lt hεpos) hεone
  by_cases ha0 : a = 0
  · have : ε = 1 := by dsimp [a] at ha0; linarith
    have hchordc := mul_le_mul_of_nonneg_right hchord hc
    have hzero :
        (1 - ε) * (1 - 1 / Real.exp 1) * c ≤ 0 := by
      simpa [this] using hchordc
    exact hzero.trans (hy0 1 hεone (le_refl 1))
  have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have haone : a < 1 := by dsimp [a]; linarith
  have hstrict :
      a * (1 - 1 / Real.exp 1) < 1 - Real.exp (-a) := by
    have hconv := strictConvexOn_exp.2 (Set.mem_univ (0 : ℝ))
      (Set.mem_univ (-1 : ℝ)) (by norm_num) hεpos hapos (by
        dsimp [a]
        ring)
    norm_num [smul_eq_mul, Real.exp_neg] at hconv
    rw [Real.exp_neg]
    dsimp [a] at hconv ⊢
    simp only [one_div]
    calc
      (1 - ε) * (1 - (Real.exp 1)⁻¹) =
          1 - (ε + (1 - ε) * (Real.exp 1)⁻¹) := by ring
      _ < 1 - (Real.exp (1 - ε))⁻¹ := sub_lt_sub_left hconv 1
  have hxlim :
      Filter.Tendsto
        (fun n : ℕ ↦ a * ((n : ℝ) / ((n : ℝ) + a)))
        Filter.atTop (nhds a) := by
    simpa using Filter.Tendsto.const_mul a
      (tendsto_natCast_div_add_atTop (𝕜 := ℝ) a)
  have hqlim :
      Filter.Tendsto
        (fun n : ℕ ↦ 1 - Real.exp (-(a * ((n : ℝ) / ((n : ℝ) + a)))))
        Filter.atTop (nhds (1 - Real.exp (-a))) := by
    exact (continuous_const.sub (Real.continuous_exp.comp
      (continuous_neg.comp continuous_id))).continuousAt.tendsto.comp hxlim
  have hevent :
      ∀ᶠ n : ℕ in Filter.atTop,
        a * (1 - 1 / Real.exp 1) ≤
          1 - Real.exp (-(a * ((n : ℝ) / ((n : ℝ) + a)))) :=
    hqlim.eventually_const_le hstrict
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨N, hN⟩ := hevent
  let n : ℕ := max N 1
  have hcoef := hN n (le_max_left N 1)
  have hn : 1 ≤ n := le_max_right N 1
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  let δ : ℝ := a / (n : ℝ)
  have hδ : 0 ≤ δ := div_nonneg ha (le_of_lt hnreal)
  have hfrac0 : 0 ≤ δ / (1 + δ) :=
    div_nonneg hδ (by linarith)
  have hfrac1 : δ / (1 + δ) < 1 :=
    (div_lt_one (by linarith)).2 (by linarith)
  have hfactor : Real.exp (δ / (1 + δ)) ≤ 1 + δ := by
    have h := Real.exp_bound_div_one_sub_of_interval hfrac0 hfrac1
    convert h using 1 <;> field_simp <;> ring
  have hbase :
      Real.exp (a * ((n : ℝ) / ((n : ℝ) + a))) ≤
        (1 + a / (n : ℝ)) ^ n := by
    calc
      Real.exp (a * ((n : ℝ) / ((n : ℝ) + a))) =
          Real.exp (δ / (1 + δ)) ^ n := by
        rw [← Real.exp_nat_mul]
        congr 1
        dsimp [δ]
        field_simp
      _ ≤ (1 + δ) ^ n := by gcongr
      _ = (1 + a / (n : ℝ)) ^ n := by rfl
  have hgap0 : 0 ≤ c - y 1 := sub_nonneg.mpr
    (hyc 1 hεone (le_refl 1))
  have hweighted :
      Real.exp (a * ((n : ℝ) / ((n : ℝ) + a))) * (c - y 1) ≤ c :=
    (mul_le_mul_of_nonneg_right hbase hgap0).trans (hEuler n hnpos)
  have hgap :
      c - y 1 ≤
        Real.exp (-(a * ((n : ℝ) / ((n : ℝ) + a)))) * c := by
    let x := a * ((n : ℝ) / ((n : ℝ) + a))
    calc
      c - y 1 = Real.exp (-x) * (Real.exp x * (c - y 1)) := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
      _ ≤ Real.exp (-x) * c :=
        mul_le_mul_of_nonneg_left hweighted (le_of_lt (Real.exp_pos _))
  have hcoefc :
      a * (1 - 1 / Real.exp 1) * c ≤
        (1 - Real.exp (-(a * ((n : ℝ) / ((n : ℝ) + a))))) * c :=
    mul_le_mul_of_nonneg_right hcoef hc
  simpa [a] using hcoefc.trans (by linarith [hgap])

@[blueprint "lem:gs-poisson-terminal-expectation-eq"
  (statement := /-- For a GS--Poisson process $P$, its expected terminal set
  value equals the expectation over event schedules of the multilinear potential
  at time $1$. -/)
  (proof := /-- Expand the expectation from \cref{def:expected-set-value} and the
  expected potential from \cref{def:gs-poisson-expected-potential}.  Interchange
  the finite sum and integral, use the terminal-mixture identity in
  \cref{def:gs-poisson-process}, and apply
  \cref{lem:gs-poisson-terminal-potential-eq} to every terminal set. -/)
  (title := /-- Terminal expectation as terminal potential -/)
  (latexEnv := "lemma")]
lemma gs_poisson_terminal_expectation_eq {α : Type*} [Fintype α] [DecidableEq α]
    {M : Matroid α} {f : Set α → ℝ} {ε : ℝ}
    (P : gs_poisson_process M f ε) :
    expected_set_value f P.output =
      ∫ schedule, gs_poisson_expected_potential P.dynamics 1
        (gs_poisson_run_law P.dynamics
          (List.ofFn (fun i : Fin schedule.1 ↦ schedule.2 i)))
        ∂P.eventScheduleLaw := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure P.eventScheduleLaw :=
    P.event_schedule_is_probability
  simp only [expected_set_value, gs_poisson_expected_potential]
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro A hA
    rw [gs_poisson_terminal_potential_eq]
    rw [MeasureTheory.integral_mul_const]
    congr 1
    rw [P.output_is_terminal_law A]
    rw [MeasureTheory.integral_toReal]
    · exact P.terminal_run_measurable A |>.aemeasurable
    · filter_upwards
      exact fun schedule ↦ lt_top_iff_ne_top.mpr
        (PMF.apply_ne_top (gs_poisson_run_law P.dynamics
          (List.ofFn (fun i : Fin schedule.1 ↦ schedule.2 i))) A)
  · intro A hA
    rw [gs_poisson_terminal_potential_eq]
    apply MeasureTheory.Integrable.of_bound
      ((P.terminal_run_measurable A).ennreal_toReal.mul_const _).aestronglyMeasurable
      |f (↑A : Set α)|
    filter_upwards with schedule
    have hp : (gs_poisson_run_law P.dynamics
        (List.ofFn (fun i : Fin schedule.1 ↦ schedule.2 i)) A).toReal ≤ 1 := by
      rw [← ENNReal.toReal_one]
      exact ENNReal.toReal_mono (by simp) (PMF.coe_le_one _ _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_of_le_one_left (abs_nonneg _) hp

@[blueprint "lem:gs-poisson-expected-value-bound"
  (statement := /-- Let $M$ be a finite matroid, let
  $f\colon 2^U\to\mathbb R$ be nonnegative, monotone, and submodular, and let
  $0<\varepsilon\leq 1$.  If $O$ is a base whose value is at least that of every
  independent set and $P$ is the GS--Poisson process started at $\varepsilon$, then
  \[
    \mathbb E_{A\sim P}[f(A)]\geq
      (1-\varepsilon)(1-e^{-1})f(O).
  \] -/)
  (proof := /-- For a time $t$ and an event schedule, let $q_t^-$ be the run
  law using event times strictly below $t$, and let $q_t$ use event times at
  most $t$.  Each schedule contains only finitely many event times, so
  $q_t^-=q_t$ for almost every $t$.  On every schedule satisfying the process
  specification, \\cref{lem:gs-poisson-run-preserves-base} shows that both
  laws are supported on bases.

  Let
  [
    y(t)=\mathbb E_{\mathrm{schedule}}
      [\Phi(t,q_t)],\qquad
    d(t)=\mathbb E_{\mathrm{schedule}}[\operatorname{drift}(t,q_t^-)].
  ]
  The uniform estimates
  \\cref{lem:gs-poisson-expected-potential-absolute-bound,
  lem:gs-poisson-expected-drift-absolute-bound} and the joint measurability in
  \\cref{def:gs-poisson-process} make all of these integrals well defined and
  make $d$ interval integrable.  Nonnegativity follows from
  \\cref{lem:gs-poisson-expected-potential-nonnegative}, while
  \\cref{lem:gs-poisson-expected-potential-le-optimum} gives
  $y(t)\leq f(O)$ on $[\varepsilon,1]$.

  For almost every time the pre-jump and at-time laws agree.  Applying
  \\cref{lem:gs-poisson-expected-drift-bound} schedule by schedule and then
  integrating yields
  [
    d(t)\geq f(O)-y(t)
  ]
  for almost every $t\in[\varepsilon,1]$.  The compensator identity in
  \\cref{def:gs-poisson-process} gives
  $y(t)-y(s)=\int_s^t d(u)\,du$.  Hence
  \\cref{lem:gs-poisson-integral-comparison} yields
  [
    y(1)\geq(1-\varepsilon)(1-e^{-1})f(O).
  ]
  Finally, all scheduled event times are at most $1$, and
  \\cref{lem:gs-poisson-terminal-expectation-eq} identifies $y(1)$ with the
  expected value of the terminal output. -/)
  (title := /-- GS--Poisson expected-value estimate -/)
  (latexEnv := "lemma")]
lemma gs_poisson_expected_value_bound {α : Type*} [Fintype α] [DecidableEq α]
    {M : Matroid α} {f : Set α → ℝ} {ε : ℝ}
    (hεpos : 0 < ε) (hεone : ε ≤ 1)
    (hfnonneg : ∀ S : Set α, 0 ≤ f S)
    (hfmono : Monotone f)
    (hfsubmod : is_submodular_set_function f)
    (O : Finset α) (hObase : M.IsBase (↑O : Set α))
    (hOoptimal : ∀ B : Finset α, M.Indep (↑B : Set α) →
      f (↑B : Set α) ≤ f (↑O : Set α))
    (P : gs_poisson_process M f ε) :
    (1 - ε) * (1 - 1 / Real.exp 1) * f (↑O : Set α) ≤
      expected_set_value f P.output := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure P.eventScheduleLaw :=
    P.event_schedule_is_probability
  let pre : ℝ → (ℕ × (ℕ → ℝ)) → PMF (Finset α) := fun t schedule ↦
    gs_poisson_run_law P.dynamics
      ((List.ofFn (fun i : Fin schedule.1 ↦ schedule.2 i)).filter
        (fun u ↦ u < t))
  let cur : ℝ → (ℕ × (ℕ → ℝ)) → PMF (Finset α) := fun t schedule ↦
    gs_poisson_run_law P.dynamics
      ((List.ofFn (fun i : Fin schedule.1 ↦ schedule.2 i)).filter
        (fun u ↦ u ≤ t))
  let pot : ℝ → (ℕ × (ℕ → ℝ)) → ℝ := fun t schedule ↦
    gs_poisson_expected_potential P.dynamics t (cur t schedule)
  let drift : ℝ → (ℕ × (ℕ → ℝ)) → ℝ := fun t schedule ↦
    gs_poisson_expected_drift P.dynamics t (pre t schedule)
  let y : ℝ → ℝ := fun t ↦ ∫ schedule, pot t schedule ∂P.eventScheduleLaw
  let d : ℝ → ℝ := fun t ↦ ∫ schedule, drift t schedule ∂P.eventScheduleLaw
  obtain ⟨C, hC⟩ :=
    gs_poisson_expected_drift_absolute_bound P.dynamics hεpos
  have hCnonneg : 0 ≤ C := by
    have h := hC ε (PMF.pure P.dynamics.initial) (le_refl ε) hεone
    exact (abs_nonneg _).trans h
  have hdstrong : MeasureTheory.StronglyMeasurable d := by
    dsimp [d, drift, pre]
    simp only [MeasureTheory.integral_eq_setToFun]
    apply MeasureTheory.StronglyMeasurable.setToFun_prod_right _
      (fun s hs ↦ ?_) P.prejump_drift_jointly_measurable.stronglyMeasurable
    refine (Measurable.ennreal_toReal ?_).stronglyMeasurable.smul_const _
    exact measurable_measure_prodMk_left hs
  have hdbound (t : ℝ) (ht0 : ε ≤ t) (ht1 : t ≤ 1) : |d t| ≤ C := by
    dsimp [d]
    have hbound :
        ∀ᵐ schedule ∂P.eventScheduleLaw, ‖drift t schedule‖ ≤ C := by
      apply Filter.Eventually.of_forall
      intro schedule
      simpa [Real.norm_eq_abs, drift] using hC t (pre t schedule) ht0 ht1
    simpa [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_of_norm_le_const hbound)
  have hdint : IntervalIntegrable d MeasureTheory.volume ε 1 := by
    rw [intervalIntegrable_iff' (by finiteness)]
    apply MeasureTheory.IntegrableOn.of_bound (by
      rw [Set.uIcc_of_le hεone]
      exact measure_Icc_lt_top)
      hdstrong.aestronglyMeasurable.restrict C
    apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIcc
    intro t ht
    rw [Set.uIcc_of_le hεone] at ht
    simpa [Real.norm_eq_abs] using hdbound t ht.1 ht.2
  have hnoevent :
      ∀ᵐ t ∂MeasureTheory.volume, ∀ᵐ schedule ∂P.eventScheduleLaw,
        pre t schedule = cur t schedule := by
    let good : (ℕ × (ℕ → ℝ)) → ℝ → Prop := fun schedule t ↦
      ∀ i : ℕ, i < schedule.1 → t ≠ schedule.2 i
    have hgood_meas :
        MeasurableSet {z : (ℕ × (ℕ → ℝ)) × ℝ | good z.1 z.2} := by
      dsimp [good]
      measurability
    have hgood :
        ∀ᵐ schedule ∂P.eventScheduleLaw,
          ∀ᵐ t ∂MeasureTheory.volume, good schedule t := by
      apply Filter.Eventually.of_forall
      intro schedule
      have hzero :
          MeasureTheory.volume
            ((Finset.range schedule.1).image schedule.2 : Set ℝ) = 0 :=
        Finset.measure_zero _ _
      rw [MeasureTheory.ae_iff]
      apply le_antisymm
      · calc
          MeasureTheory.volume {t | ¬good schedule t} ≤
              MeasureTheory.volume
                ((Finset.range schedule.1).image schedule.2 : Set ℝ) := by
            apply MeasureTheory.measure_mono
            intro t ht
            simp only [good, not_forall, not_not] at ht
            obtain ⟨i, hi, hit⟩ := ht
            simp only [Finset.coe_image, Finset.coe_range, Set.mem_image,
              Set.mem_setOf_eq]
            exact ⟨i, hi, hit.symm⟩
          _ = 0 := hzero
      · exact bot_le
    have hgood' :
        ∀ᵐ t ∂MeasureTheory.volume,
          ∀ᵐ schedule ∂P.eventScheduleLaw, good schedule t :=
      (P.eventScheduleLaw.ae_ae_comm hgood_meas).mp hgood
    filter_upwards [hgood'] with t ht
    filter_upwards [ht] with schedule hschedule
    dsimp [pre, cur]
    congr 1
    apply List.filter_congr
    intro u hu
    by_cases hut : u < t
    · simp [hut, le_of_lt hut]
    · have hne : u ≠ t := by
        intro hut'
        subst u
        simp only [List.mem_ofFn] at hu
        obtain ⟨i, hi⟩ := hu
        exact hschedule i.1 i.2 hi.symm
      have hnle : ¬u ≤ t := fun hle ↦ hne (le_antisymm hle (le_of_not_gt hut))
      simp [hut, hnle]
  have hschedule_times (schedule : ℕ × (ℕ → ℝ))
      (hspec : (∀ i : ℕ, i < schedule.1 →
        ε < schedule.2 i ∧ schedule.2 i ≤ 1) ∧
        (∀ i j : ℕ, i < j → j < schedule.1 →
          schedule.2 i < schedule.2 j)) :
      ∀ u ∈ List.ofFn (fun i : Fin schedule.1 ↦ schedule.2 i),
        ε ≤ u ∧ u ≤ 1 := by
    intro u hu
    simp only [List.mem_ofFn] at hu
    obtain ⟨i, hi⟩ := hu
    subst u
    exact ⟨le_of_lt (hspec.1 i.1 i.2).1, (hspec.1 i.1 i.2).2⟩
  have hprebase (t : ℝ) (schedule : ℕ × (ℕ → ℝ))
      (hspec : (∀ i : ℕ, i < schedule.1 →
        ε < schedule.2 i ∧ schedule.2 i ≤ 1) ∧
        (∀ i j : ℕ, i < j → j < schedule.1 →
          schedule.2 i < schedule.2 j)) :
      ∀ A : Finset α, A ∈ (pre t schedule).support →
        M.IsBase (↑A : Set α) := by
    apply gs_poisson_run_preserves_base
    intro u hu
    exact hschedule_times schedule hspec u (List.mem_of_mem_filter hu)
  have hcurbase (t : ℝ) (schedule : ℕ × (ℕ → ℝ))
      (hspec : (∀ i : ℕ, i < schedule.1 →
        ε < schedule.2 i ∧ schedule.2 i ≤ 1) ∧
        (∀ i j : ℕ, i < j → j < schedule.1 →
          schedule.2 i < schedule.2 j)) :
      ∀ A : Finset α, A ∈ (cur t schedule).support →
        M.IsBase (↑A : Set α) := by
    apply gs_poisson_run_preserves_base
    intro u hu
    exact hschedule_times schedule hspec u (List.mem_of_mem_filter hu)
  let K : ℝ := ∑ S ∈ (Finset.univ : Finset α).powerset, |f (↑S : Set α)|
  have hpotint (t : ℝ) (ht0 : ε ≤ t) (ht1 : t ≤ 1) :
      MeasureTheory.Integrable (pot t) P.eventScheduleLaw := by
    apply MeasureTheory.Integrable.of_bound
      ((P.potential_jointly_measurable.comp
        measurable_prodMk_left).aestronglyMeasurable) K
    apply Filter.Eventually.of_forall
    intro schedule
    simpa [Real.norm_eq_abs, pot, K] using
      gs_poisson_expected_potential_absolute_bound P.dynamics
        (cur t schedule) (le_trans (le_of_lt hεpos) ht0) ht1
  have hdriftint (t : ℝ) (ht0 : ε ≤ t) (ht1 : t ≤ 1) :
      MeasureTheory.Integrable (drift t) P.eventScheduleLaw := by
    apply MeasureTheory.Integrable.of_bound
      ((P.prejump_drift_jointly_measurable.comp
        measurable_prodMk_left).aestronglyMeasurable) C
    apply Filter.Eventually.of_forall
    intro schedule
    simpa [Real.norm_eq_abs, drift] using hC t (pre t schedule) ht0 ht1
  have hy0 : ∀ t, ε ≤ t → t ≤ 1 → 0 ≤ y t := by
    intro t ht0 ht1
    dsimp [y]
    apply MeasureTheory.integral_nonneg_of_ae
    apply Filter.Eventually.of_forall
    intro schedule
    exact gs_poisson_expected_potential_nonnegative P.dynamics hfnonneg
      (le_trans (le_of_lt hεpos) ht0) ht1 (cur t schedule)
  have hyc : ∀ t, ε ≤ t → t ≤ 1 → y t ≤ f (↑O : Set α) := by
    intro t ht0 ht1
    have hle :
        ∀ᵐ schedule ∂P.eventScheduleLaw,
          pot t schedule ≤ f (↑O : Set α) := by
      filter_upwards [P.event_schedule_spec] with schedule hspec
      exact gs_poisson_expected_potential_le_optimum P.dynamics hfmono O
        hOoptimal (cur t schedule) (hcurbase t schedule hspec)
        (le_trans (le_of_lt hεpos) ht0) ht1
    have hint := MeasureTheory.integral_mono_ae (hpotint t ht0 ht1)
      (MeasureTheory.integrable_const (f (↑O : Set α))) hle
    simpa [y] using hint
  have hevol : ∀ s t, ε ≤ s → s ≤ t → t ≤ 1 →
      y t - y s = ∫ u in s..t, d u := by
    intro s t hs hst ht
    simpa [y, d, pot, drift, cur, pre] using
      P.potential_compensator_identity hs hst ht
  have hdrift :
      ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Icc ε 1),
        f (↑O : Set α) - y t ≤ d t := by
    filter_upwards [MeasureTheory.ae_restrict_of_ae hnoevent,
      MeasureTheory.ae_restrict_mem measurableSet_Icc] with t hprecur ht
    have hsched :
        ∀ᵐ schedule ∂P.eventScheduleLaw,
          f (↑O : Set α) - pot t schedule ≤ drift t schedule := by
      filter_upwards [P.event_schedule_spec, hprecur] with schedule hspec heq
      have hbound := gs_poisson_expected_drift_bound P.dynamics hεpos
        hfmono hfsubmod O hObase (pre t schedule)
        (hprebase t schedule hspec) ht.1 ht.2
      simpa [pot, drift, heq] using hbound
    have hint := MeasureTheory.integral_mono_ae
      ((MeasureTheory.integrable_const (f (↑O : Set α))).sub
        (hpotint t ht.1 ht.2))
      (hdriftint t ht.1 ht.2) hsched
    calc
      f (↑O : Set α) - y t =
          ∫ schedule, f (↑O : Set α) - pot t schedule
            ∂P.eventScheduleLaw := by
        rw [MeasureTheory.integral_sub
          (MeasureTheory.integrable_const (f (↑O : Set α)))
          (hpotint t ht.1 ht.2)]
        simp [y]
      _ ≤ ∫ schedule, drift t schedule ∂P.eventScheduleLaw := by
        simpa only [Pi.sub_apply] using hint
      _ = d t := by rfl
  have hcompare := gs_poisson_integral_comparison hεpos hεone
    (hfnonneg (↑O : Set α)) y d hdint hy0 hyc hevol hdrift
  have hyterminal : y 1 = expected_set_value f P.output := by
    rw [gs_poisson_terminal_expectation_eq P]
    dsimp [y, pot, cur]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [P.event_schedule_spec] with schedule hspec
    congr 2
    apply List.filter_eq_self.mpr
    intro u hu
    simpa using (hschedule_times schedule hspec u hu).2
  rw [hyterminal] at hcompare
  exact hcompare

@[blueprint "thm:matroid"
  (statement := /-- Let $M=(U,\mathcal I)$ be a matroid on a finite ground set,
  let $f\colon 2^U\to\mathbb R$ be nonnegative, monotone, and submodular, and let
  $0<\varepsilon\leq 1$.  Suppose that $O$ is a base of $M$ such that
  $f(B)\leq f(O)$ for every independent set $B$, and let $P$ be a GS--Poisson
  process for $(M,f,\varepsilon)$.  Then every set in the support of the terminal
  output law of $P$ is independent, and
  \[
    \mathbb E_{A\sim P}[f(A)]\geq
      (1-\varepsilon)(1-e^{-1})f(O).
  \] -/)
  (proof := /-- By \cref{lem:gs-poisson-output-independent}, every set in the
  support of the terminal output law is independent.  By
  \cref{lem:gs-poisson-expected-value-bound}, the expectation under that law is
  at least $(1-\varepsilon)(1-e^{-1})f(O)$.  These two conclusions give the
  required conjunction. -/)
  (title := /-- Approximation guarantee for GS--Poisson under a matroid constraint -/)
  (latexEnv := "theorem")]
theorem matroid {α : Type*} [Fintype α] [DecidableEq α]
    {M : Matroid α} {f : Set α → ℝ} {ε : ℝ}
    (hεpos : 0 < ε) (hεone : ε ≤ 1)
    (hfnonneg : ∀ S : Set α, 0 ≤ f S)
    (hfmono : Monotone f)
    (hfsubmod : is_submodular_set_function f)
    (O : Finset α) (hObase : M.IsBase (↑O : Set α))
    (hOoptimal : ∀ B : Finset α, M.Indep (↑B : Set α) →
      f (↑B : Set α) ≤ f (↑O : Set α))
    (P : gs_poisson_process M f ε) :
    (∀ A : Finset α, A ∈ P.output.support → M.Indep (↑A : Set α)) ∧
      (1 - ε) * (1 - 1 / Real.exp 1) * f (↑O : Set α) ≤
        expected_set_value f P.output := by
  exact ⟨gs_poisson_output_independent P,
    gs_poisson_expected_value_bound hεpos hεone hfnonneg hfmono hfsubmod O hObase
      hOoptimal P⟩

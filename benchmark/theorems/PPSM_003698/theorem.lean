import Mathlib.Analysis.Complex.Exponential
import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Independence.Basic

set_option linter.all false

def is_submodular_set_function {α : Type*} (f : Set α → ℝ) : Prop :=
  ∀ ⦃S T : Set α⦄, S ⊆ T → ∀ ⦃i : α⦄, i ∉ T →
    f (insert i S) - f S ≥ f (insert i T) - f T

noncomputable def multilinear_extension {α : Type*} [Fintype α] [DecidableEq α]
    (f : Set α → ℝ) (x : α → ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset α).powerset,
    f (↑S : Set α) * (∏ i ∈ S, x i) *
      ∏ i ∈ (Finset.univ : Finset α) \ S, (1 - x i)

def scaled_indicator {α : Type*} [DecidableEq α] (t : ℝ) (A : Finset α) : α → ℝ :=
  fun i ↦ if i ∈ A then t else 0

noncomputable def multilinear_marginal {α : Type*} [Fintype α] [DecidableEq α]
    (f : Set α → ℝ) (x : α → ℝ) (i : α) : ℝ :=
  multilinear_extension f (Function.update x i 1) -
    multilinear_extension f (Function.update x i 0)

def is_gradient_maximizing_base {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matroid α) (f : Set α → ℝ) (t : ℝ) (A Z : Finset α) : Prop :=
  M.IsBase (↑Z : Set α) ∧
    ∀ B : Finset α, M.IsBase (↑B : Set α) →
      (∑ i ∈ B, multilinear_marginal f (scaled_indicator t A) i) ≤
        ∑ i ∈ Z, multilinear_marginal f (scaled_indicator t A) i

structure base_exchange_bijection {α : Type*} [DecidableEq α]
    (M : Matroid α) (A Z : Finset α) where
  equiv : A ≃ Z
  valid : ∀ i : A,
    M.IsBase (↑(insert (equiv i).1 (A.erase i.1)) : Set α)

noncomputable def expected_set_value {α : Type*} [Fintype α]
    (f : Set α → ℝ) (p : PMF (Finset α)) : ℝ :=
  ∑ A : Finset α, (p A).toReal * f (↑A : Set α)

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

noncomputable def gs_poisson_run_law {α : Type*} [Fintype α] [DecidableEq α]
    {M : Matroid α} {f : Set α → ℝ} {ε : ℝ}
    (D : gs_poisson_dynamics M f ε) (times : List ℝ) : PMF (Finset α) :=
  times.foldl
    (fun stateLaw t ↦ stateLaw.bind (gs_poisson_swap_law D t))
    (PMF.pure D.initial)

noncomputable def gs_poisson_expected_potential {α : Type*} [Fintype α]
    [DecidableEq α] {M : Matroid α} {f : Set α → ℝ} {ε : ℝ}
    (D : gs_poisson_dynamics M f ε) (t : ℝ) (q : PMF (Finset α)) : ℝ :=
  ∑ A : Finset α, (q A).toReal *
    multilinear_extension f (scaled_indicator t A)

noncomputable def gs_poisson_expected_drift {α : Type*} [Fintype α]
    [DecidableEq α] {M : Matroid α} {f : Set α → ℝ} {ε : ℝ}
    (D : gs_poisson_dynamics M f ε) (t : ℝ) (q : PMF (Finset α)) : ℝ :=
  ∑ A : Finset α, (q A).toReal *
    ((∑ i ∈ A, multilinear_marginal f (scaled_indicator t A) i) +
      D.rate t * ∑ B : Finset α, ((gs_poisson_swap_law D t A) B).toReal *
        (multilinear_extension f (scaled_indicator t B) -
          multilinear_extension f (scaled_indicator t A)))

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
        expected_set_value f P.output := by sorry

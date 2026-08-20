import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory

structure biased_source_mean_problem (K M : ℕ) [NeZero K] [NeZero M] where
  targetGroup : PMF (Fin K)
  sourceGroup : Fin M → PMF (Fin K)
  cost : Fin M → ℝ
  meanRadius : ℝ
  varianceBound : ℝ
  cost_pos : ∀ m, 0 < cost m
  meanRadius_nonneg : 0 ≤ meanRadius
  varianceBound_nonneg : 0 ≤ varianceBound
  source_covers : ∀ z, ∃ m, 0 < (sourceGroup m z).toReal

abbrev sampling_plan (M : ℕ) := Fin M → ℕ

def plan_total_samples {M : ℕ} (n : sampling_plan M) : ℕ :=
  ∑ m, n m

def plan_cost {M : ℕ} (c : Fin M → ℝ) (n : sampling_plan M) : ℝ :=
  ∑ m, c m * n m

noncomputable def average_plan_cost {M : ℕ} (c : Fin M → ℝ) (n : sampling_plan M) : ℝ :=
  if plan_total_samples n = 0 then 0 else plan_cost c n / plan_total_samples n

def pmf_real_mass {α : Type*} (q : PMF α) (a : α) : ℝ :=
  (q a).toReal

noncomputable def source_mixture_mass {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M) (z : Fin K) : ℝ :=
  if plan_total_samples n = 0 then 0
  else (∑ m, n m * pmf_real_mass (p.sourceGroup m) z) / plan_total_samples n

def target_supported_by_plan {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (q : Fin K → ℝ) : Prop :=
  ∀ z, 0 < q z → 0 < source_mixture_mass p n z

noncomputable def plan_discrepancy {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (q : Fin K → ℝ) : ℝ :=
  ∑ z, if q z = 0 then 0 else (q z) ^ 2 / source_mixture_mass p n z

noncomputable def effective_sample_size {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (q : Fin K → ℝ) : ℝ := by
  classical
  exact if plan_total_samples n = 0 ∨ ¬ target_supported_by_plan p n q then 0
    else plan_total_samples n / plan_discrepancy p n q

def budget_feasible_plan {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (B : ℝ) (n : sampling_plan M) : Prop :=
  plan_cost p.cost n ≤ B

def optimal_sampling_plan {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (q : Fin K → ℝ)
    (B : ℝ) (n : sampling_plan M) : Prop :=
  budget_feasible_plan p B n ∧
    ∀ n', budget_feasible_plan p B n' →
      effective_sample_size p n' q ≤ effective_sample_size p n q

noncomputable def uniform_group_mass (K : ℕ) [NeZero K] (_z : Fin K) : ℝ :=
  1 / K

abbrev conditional_outcome_model (K : ℕ) := Fin K → MeasureTheory.ProbabilityMeasure ℝ

noncomputable def conditional_group_mean {K : ℕ}
    (P : conditional_outcome_model K) (z : Fin K) : ℝ :=
  ∫ y, y ∂(P z : Measure ℝ)

def bounded_conditional_mean_class {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (P : conditional_outcome_model K) : Prop :=
  ∀ z, MeasureTheory.MemLp id 2 (P z : Measure ℝ) ∧
    |conditional_group_mean P z| ≤ p.meanRadius ∧
    ProbabilityTheory.variance id (P z : Measure ℝ) ≤ p.varianceBound

abbrev sampled_dataset (K M : ℕ) (n : sampling_plan M) :=
  (m : Fin M) → Fin (n m) → Fin K × ℝ

noncomputable def source_observation_law {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (P : conditional_outcome_model K)
    (m : Fin M) : Measure (Fin K × ℝ) :=
  Measure.map
    (fun x : Fin K × (Fin K → ℝ) => (x.1, x.2 x.1))
    ((p.sourceGroup m).toMeasure.prod
      (Measure.pi fun z => (P z : Measure ℝ)))

noncomputable def sampling_law {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (P : conditional_outcome_model K) : Measure (sampled_dataset K M n) :=
  Measure.pi fun m => Measure.pi fun _i : Fin (n m) => source_observation_law p P m

def observed_group_count {K M : ℕ} {n : sampling_plan M}
    (D : sampled_dataset K M n) (z : Fin K) : ℕ :=
  ∑ m, ∑ i, if (D m i).1 = z then 1 else 0

def observed_group_sum {K M : ℕ} {n : sampling_plan M}
    (D : sampled_dataset K M n) (z : Fin K) : ℝ :=
  ∑ m, ∑ i, if (D m i).1 = z then (D m i).2 else 0

noncomputable def observed_group_mean {K M : ℕ} {n : sampling_plan M}
    (D : sampled_dataset K M n) (z : Fin K) : ℝ :=
  if observed_group_count D z = 0 then 0
  else observed_group_sum D z / observed_group_count D z

noncomputable def post_stratified_estimator {K M : ℕ} {n : sampling_plan M}
    (qT : PMF (Fin K)) (D : sampled_dataset K M n) : ℝ :=
  ∑ z, pmf_real_mass qT z * observed_group_mean D z

noncomputable def vector_of_means_estimator {K M : ℕ} {n : sampling_plan M}
    (D : sampled_dataset K M n) : Fin K → ℝ :=
  fun z => observed_group_mean D z

noncomputable def target_population_mean {K : ℕ}
    (qT : PMF (Fin K)) (P : conditional_outcome_model K) : ℝ :=
  ∑ z, pmf_real_mass qT z * conditional_group_mean P z

noncomputable def population_mean_risk {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (estimator : sampled_dataset K M n → ℝ) (P : conditional_outcome_model K) : ℝ :=
  ∫ D, (estimator D - target_population_mean p.targetGroup P) ^ 2 ∂sampling_law p n P

noncomputable def group_means_risk {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (estimator : sampled_dataset K M n → (Fin K → ℝ))
    (P : conditional_outcome_model K) : ℝ :=
  ∫ D, (∑ z, (estimator D z - conditional_group_mean P z) ^ 2) ∂sampling_law p n P

noncomputable def population_worst_case_risk {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (estimator : sampled_dataset K M n → ℝ)
    (hrisk : BddAbove {r : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
      r = population_mean_risk p n estimator P}) : ℝ :=
  sSup {r : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
    r = population_mean_risk p n estimator P}

noncomputable def group_worst_case_risk {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (estimator : sampled_dataset K M n → (Fin K → ℝ))
    (hrisk : BddAbove {r : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
      r = group_means_risk p n estimator P}) : ℝ :=
  sSup {r : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
    r = group_means_risk p n estimator P}

noncomputable def population_minimax_risk {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (B : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ n : sampling_plan M, budget_feasible_plan p B n ∧
    ∃ estimator : sampled_dataset K M n → ℝ, Measurable estimator ∧
      ∃ hrisk : BddAbove {s : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
        s = population_mean_risk p n estimator P},
        r = population_worst_case_risk p n estimator hrisk}

noncomputable def group_minimax_risk {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (B : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ n : sampling_plan M, budget_feasible_plan p B n ∧
    ∃ estimator : sampled_dataset K M n → (Fin K → ℝ), Measurable estimator ∧
      ∃ hrisk : BddAbove {s : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
        s = group_means_risk p n estimator P},
        r = group_worst_case_risk p n estimator hrisk}

noncomputable def population_leading_risk {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M) (B : ℝ) : ℝ :=
  p.varianceBound * average_plan_cost p.cost n *
    plan_discrepancy p n (fun z => pmf_real_mass p.targetGroup z) / B

noncomputable def group_leading_risk {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M) (B : ℝ) : ℝ :=
  (K : ℝ) ^ 2 * p.varianceBound * average_plan_cost p.cost n *
    plan_discrepancy p n (uniform_group_mass K) / B

noncomputable def inverse_budget_rate (B : ℝ) : ℝ :=
  1 / B

theorem minimax_optimal_data_collection_under_budget {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (hmean : 0 < p.meanRadius) :
    ∃ targetPlans uniformPlans : ℝ → sampling_plan M,
      (∀ B, 0 < B →
        optimal_sampling_plan p (fun z => pmf_real_mass p.targetGroup z) B (targetPlans B)) ∧
      (∀ B, 0 < B →
        optimal_sampling_plan p (uniform_group_mass K) B (uniformPlans B)) ∧
      (∀ B, Measurable
        (post_stratified_estimator p.targetGroup : sampled_dataset K M (targetPlans B) → ℝ)) ∧
      (∀ B, Measurable
        (vector_of_means_estimator : sampled_dataset K M (uniformPlans B) → (Fin K → ℝ))) ∧
      (∀ P, bounded_conditional_mean_class p P →
        ∃ remainder : ℝ → ℝ,
          Asymptotics.IsLittleO Filter.atTop remainder inverse_budget_rate ∧
          ∀ B, 0 < B →
            population_mean_risk p (targetPlans B)
                (post_stratified_estimator p.targetGroup) P ≤
              population_leading_risk p (targetPlans B) B + remainder B) ∧
      Asymptotics.IsLittleO Filter.atTop
        (fun B => population_minimax_risk p B -
          population_leading_risk p (targetPlans B) B)
        inverse_budget_rate ∧
      (∀ P, bounded_conditional_mean_class p P →
        ∃ remainder : ℝ → ℝ,
          Asymptotics.IsLittleO Filter.atTop remainder inverse_budget_rate ∧
          ∀ B, 0 < B →
            group_means_risk p (uniformPlans B) vector_of_means_estimator P ≤
              group_leading_risk p (uniformPlans B) B + remainder B) ∧
      Asymptotics.IsLittleO Filter.atTop
        (fun B => group_minimax_risk p B - group_leading_risk p (uniformPlans B) B)
        inverse_budget_rate := by sorry

import Mathlib.Algebra.Notation.Indicator
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.all false
set_option maxHeartbeats 500000

abbrev rate_vector (Job : Type*) := Job → ℝ

structure polytope_scheduling_problem (Job : Type*) where
  feasible_rates : Set (rate_vector Job)
  convex_feasible_rates : Convex ℝ feasible_rates
  compact_feasible_rates : IsCompact feasible_rates
  zero_mem_feasible_rates : (0 : rate_vector Job) ∈ feasible_rates
  feasible_rates_nonnegative :
    ∀ ⦃z : rate_vector Job⦄, z ∈ feasible_rates → ∀ j, 0 ≤ z j
  downward_closed :
    ∀ ⦃z y : rate_vector Job⦄, z ∈ feasible_rates →
      (∀ j, 0 ≤ y j) → (∀ j, y j ≤ z j) → y ∈ feasible_rates

structure weighted_job_instance (Job : Type*) where
  release : Job → ℝ
  processing : Job → ℝ
  weight : Job → ℝ
  release_nonnegative : ∀ j, 0 ≤ release j
  processing_positive : ∀ j, 0 < processing j
  weight_positive : ∀ j, 0 < weight j

structure speed_schedule {Job : Type*} (P : polytope_scheduling_problem Job)
    (I : weighted_job_instance Job) (speed : ℝ) where
  rate : ℝ → rate_vector Job
  completion : Job → ℝ
  rate_interval_integrable :
    ∀ j a b, IntervalIntegrable (fun t => rate t j) volume a b
  rate_feasible :
    ∀ t, 0 ≤ t →
      ∃ z ∈ P.feasible_rates, rate t = fun j => speed * z j
  no_processing_before_release :
    ∀ j t, t < I.release j → rate t j = 0
  no_processing_after_completion :
    ∀ j t, completion j < t → rate t j = 0
  completion_after_release : ∀ j, I.release j ≤ completion j
  processing_exact :
    ∀ j, (∫ t in I.release j..completion j, rate t j) = I.processing j
  processing_incomplete_before_completion :
    ∀ j t, I.release j ≤ t → t < completion j →
      (∫ u in I.release j..t, rate u j) < I.processing j

def weighted_integral_flow_time {Job : Type*} [Fintype Job]
    {P : polytope_scheduling_problem Job} {I : weighted_job_instance Job} {speed : ℝ}
    (S : speed_schedule P I speed) : ℝ :=
  ∑ j, I.weight j * (S.completion j - I.release j)

noncomputable def remaining_job_size {Job : Type*}
    {P : polytope_scheduling_problem Job} {I : weighted_job_instance Job} {speed : ℝ}
    (S : speed_schedule P I speed) (t : ℝ) : rate_vector Job :=
  fun j =>
    if I.release j ≤ t ∧ t < S.completion j then
      max 0 (I.processing j - ∫ u in I.release j..t, S.rate u j)
    else
      0

noncomputable def offline_integral_optimum {Job : Type*} [Fintype Job]
    (P : polytope_scheduling_problem Job) (I : weighted_job_instance Job) : ℝ :=
  sInf {c : ℝ | ∃ S : speed_schedule P I 1, c = weighted_integral_flow_time S}

def job_instances_agree_until {Job : Type*}
    (I K : weighted_job_instance Job) (t : ℝ) : Prop :=
  ∀ j, I.release j ≤ t ∨ K.release j ≤ t →
    I.release j = K.release j ∧
    I.processing j = K.processing j ∧
    I.weight j = K.weight j

structure online_scheduling_algorithm {Job : Type*}
    (P : polytope_scheduling_problem Job) where
  run :
    ∀ (speed : ℝ), 0 < speed → (I : weighted_job_instance Job) →
      speed_schedule P I speed
  causal :
    ∀ (speed : ℝ) (hspeed : 0 < speed)
      (I K : weighted_job_instance Job) (t : ℝ),
      job_instances_agree_until I K t →
      ∀ u, 0 ≤ u → u ≤ t →
        (run speed hspeed I).rate u = (run speed hspeed K).rate u

structure residual_schedule {Job : Type*} (P : polytope_scheduling_problem Job)
    (x : rate_vector Job) where
  rate : ℝ → rate_vector Job
  completion : Job → ℝ
  size_nonnegative : ∀ j, 0 ≤ x j
  rate_interval_integrable :
    ∀ j a b, IntervalIntegrable (fun t => rate t j) volume a b
  rate_feasible : ∀ t, 0 ≤ t → rate t ∈ P.feasible_rates
  completion_nonnegative : ∀ j, 0 ≤ completion j
  processing_exact : ∀ j, (∫ t in (0 : ℝ)..completion j, rate t j) = x j
  processing_incomplete_before_completion :
    ∀ j t, 0 ≤ t → t < completion j →
      (∫ u in (0 : ℝ)..t, rate u j) < x j
  no_processing_after_completion :
    ∀ j t, completion j < t → rate t j = 0

def residual_weighted_completion {Job : Type*} [Fintype Job]
    {P : polytope_scheduling_problem Job} {x : rate_vector Job}
    (w : rate_vector Job) (R : residual_schedule P x) : ℝ :=
  ∑ j, w j * R.completion j

noncomputable def residual_integral_optimum {Job : Type*} [Fintype Job]
    (P : polytope_scheduling_problem Job) (w x : rate_vector Job) : ℝ :=
  sInf {c : ℝ | ∃ R : residual_schedule P x, c = residual_weighted_completion w R}

noncomputable def discrete_supermodular {Job : Type*}
    (g : rate_vector Job → ℝ) : Prop :=
  ∀ x : rate_vector Job, (∀ j, 0 ≤ x j) →
    ∀ U V : Set Job,
      g (U.indicator x) + g (V.indicator x) ≤
        g ((U ∩ V).indicator x) + g ((U ∪ V).indicator x)

def residual_directional_derivative {Job : Type*}
    (f : rate_vector Job → ℝ) (x y : rate_vector Job) (d : ℝ) : Prop :=
  Filter.Tendsto
    (fun δ : ℝ => (f (fun j => x j - δ * y j) - f x) / δ)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds d)

def active_feasible_rates {Job : Type*}
    (P : polytope_scheduling_problem Job) (x : rate_vector Job) : Set (rate_vector Job) :=
  {y | y ∈ P.feasible_rates ∧ ∀ j, x j = 0 → y j = 0}

structure gradient_descent_algorithm {Job : Type*} [Fintype Job]
    (P : polytope_scheduling_problem Job) where
  to_online : online_scheduling_algorithm P
  minimizes_residual_derivative :
    ∀ (speed : ℝ) (hspeed : 0 < speed)
      (I : weighted_job_instance Job) (t : ℝ), 0 ≤ t →
      let S := to_online.run speed hspeed I
      let x := remaining_job_size S t
      let z : rate_vector Job := fun j => S.rate t j / speed
      z ∈ active_feasible_rates P x ∧
        ∃ D : rate_vector Job → ℝ,
          (∀ y ∈ active_feasible_rates P x,
            residual_directional_derivative
              (residual_integral_optimum P I.weight) x y (D y)) ∧
          ∀ y ∈ active_feasible_rates P x, D z ≤ D y

def integral_speed_competitive {Job : Type*} [Fintype Job]
    (P : polytope_scheduling_problem Job) (A : online_scheduling_algorithm P)
    (speed ratio : ℝ) : Prop :=
  ∀ hspeed : 0 < speed, ∀ I : weighted_job_instance Job,
    weighted_integral_flow_time (A.run speed hspeed I) ≤
      ratio * offline_integral_optimum P I

theorem gradient_descent_desiderata_for_integral_objective
    : ∃ C : ℝ, 0 < C ∧
      ∀ (Job : Type) [Fintype Job]
        (P : polytope_scheduling_problem Job) (GD : gradient_descent_algorithm P),
        (∀ w : rate_vector Job, (∀ j, 0 < w j) →
          discrete_supermodular (residual_integral_optimum P w)) →
        ∀ ε : ℝ, 0 < ε →
          integral_speed_competitive P GD.to_online (1 + ε) (C / ε) := by sorry

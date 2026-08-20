import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Logic.Relation

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators

structure warm_start_oracle (Instance Solution : Type*) [MetricSpace Solution] where
  solution : Instance → Solution
  runtime : Instance → Solution → ℝ
  runtime_nonnegative : ∀ I P, 0 ≤ runtime I P
  runtime_le_dist : ∀ I P, runtime I P ≤ dist (solution I) P

class unit_separated_metric (Solution : Type*) [MetricSpace Solution] : Prop where
  one_le_dist : ∀ {x y : Solution}, x ≠ y → 1 ≤ dist x y

structure online_ball_search_input (Instance Solution : Type*) (T : ℕ) where
  instanceAt : Fin T → Instance
  origin : Solution

structure trajectory_family (Solution : Type*) (T k : ℕ) where
  owner : Fin T → Fin k
  prediction : Fin T → Solution
  previousDay : Fin T → Option (Fin T)
  previousDay_lt : ∀ {t s}, previousDay t = some s → s < t
  previousDay_owner : ∀ {t s}, previousDay t = some s → owner s = owner t
  previousDay_maximal :
    ∀ {t s u}, previousDay t = some s → u < t → owner u = owner t → u ≤ s
  no_previousDay : ∀ {t}, previousDay t = none → ∀ u, u < t → owner u ≠ owner t

def trajectory_previous_prediction {Solution : Type*} {T k : ℕ}
    (origin : Solution) (family : trajectory_family Solution T k) (t : Fin T) : Solution :=
  match family.previousDay t with
  | none => origin
  | some s => family.prediction s

def trajectory_previous_solution {Solution : Type*} {T k : ℕ}
    (origin : Solution) (solution : Fin T → Solution)
    (family : trajectory_family Solution T k) (t : Fin T) : Solution :=
  match family.previousDay t with
  | none => origin
  | some s => solution s

noncomputable def trajectory_hit_cost {Solution : Type*} [MetricSpace Solution] {T k : ℕ}
    (solution : Fin T → Solution) (family : trajectory_family Solution T k) : ℝ :=
  ∑ t, dist (family.prediction t) (solution t)

noncomputable def trajectory_movement_cost {Solution : Type*} [MetricSpace Solution] {T k : ℕ}
    (origin : Solution) (family : trajectory_family Solution T k) : ℝ :=
  ∑ t, dist (trajectory_previous_prediction origin family t) (family.prediction t)

noncomputable def trajectory_family_cost {Solution : Type*} [MetricSpace Solution] {T k : ℕ}
    (origin : Solution) (solution : Fin T → Solution)
    (family : trajectory_family Solution T k) : ℝ :=
  trajectory_hit_cost solution family + trajectory_movement_cost origin family

noncomputable def predict_yesterday_step_cost {Solution : Type*} [MetricSpace Solution]
    {T k : ℕ} (origin : Solution) (solution : Fin T → Solution)
    (family : trajectory_family Solution T k) (t : Fin T) : ℝ :=
  dist (trajectory_previous_solution origin solution family t) (solution t)

noncomputable def collapse_owner_charge {Solution : Type*} [MetricSpace Solution]
    {T k : ℕ} (origin : Solution) (solution : Fin T → Solution)
    (family : trajectory_family Solution T k) (t : Fin T) (q : Fin k) : ℝ :=
  by
    classical
    exact ∑ s, if
        family.owner s = q ∧
          (match family.previousDay t with
           | none => True
           | some p => p < s) ∧ s < t
      then predict_yesterday_step_cost origin solution family s
      else 0

structure quadratic_decay_run (Solution : Type*) (T : ℕ) where
  output : Fin T → Solution
  dayVirtualRadius : Fin T → ℝ
  daySearchedRadius : Fin T → ℝ
  dayRuntime : Fin T → ℝ
  dayVirtualRadius_nonnegative : ∀ t, 0 ≤ dayVirtualRadius t
  daySearchedRadius_nonnegative : ∀ t, 0 ≤ daySearchedRadius t
  dayRuntime_nonnegative : ∀ t, 0 ≤ dayRuntime t

structure online_ball_search_algorithm (Instance Solution : Type*) [MetricSpace Solution] where
  run : {T : ℕ} → warm_start_oracle Instance Solution →
    online_ball_search_input Instance Solution T → quadratic_decay_run Solution T
  run_nonanticipating : ∀ {T : ℕ}
    (oracle : warm_start_oracle Instance Solution)
    (input input' : online_ball_search_input Instance Solution T) (t : Fin T),
    input.origin = input'.origin →
    (∀ s : Fin T, s ≤ t → input.instanceAt s = input'.instanceAt s) →
      (run oracle input).output t = (run oracle input').output t ∧
      (run oracle input).dayVirtualRadius t =
        (run oracle input').dayVirtualRadius t ∧
      (run oracle input).daySearchedRadius t =
        (run oracle input').daySearchedRadius t ∧
      (run oracle input).dayRuntime t = (run oracle input').dayRuntime t

noncomputable def quadratic_decay_rate (rank : ℕ) : ℝ :=
  if rank = 0 then 1
  else 1 / (((rank + 1 : ℕ) : ℝ) ^ 2 * (Real.log ((rank + 1 : ℕ) : ℝ)) ^ 2)

structure quadratic_decay_thread_execution (Solution : Type*) (threadCount : ℕ) where
  center : Solution
  rankedVirtualTime : Fin threadCount → ℝ
  rankedVirtualTime_nonnegative : ∀ r, 0 ≤ rankedVirtualTime r
  searchedRadius : ℝ
  searchedRadius_eq_schedule :
    searchedRadius = ∑ r, quadratic_decay_rate r.val * rankedVirtualTime r
  warmStartWork : ℝ
  warmStartWork_eq_searchedRadius : warmStartWork = searchedRadius
  overheadRuntime : ℝ
  overheadRuntime_nonnegative : 0 ≤ overheadRuntime
  overheadRuntime_le_schedule :
    overheadRuntime ≤
      ∑ r, (((r.val + 1 : ℕ) : ℝ) * quadratic_decay_rate r.val) *
        rankedVirtualTime r
  subsumedBy : Option (Fin threadCount)
  radiusAtSubsumption : ℝ
  subsumingRadiusAtSubsumption : ℝ
  rankAtSubsumption : Fin threadCount
  subsumingRankAtSubsumption : Fin threadCount

structure quadratic_decay_day_execution
    {Instance Solution : Type*} [MetricSpace Solution] {T : ℕ}
    (oracle : warm_start_oracle Instance Solution)
    (input : online_ball_search_input Instance Solution T)
    (run : quadratic_decay_run Solution T) (t : Fin T) where
  thread :
    Fin (t.val + 1) → quadratic_decay_thread_execution Solution (t.val + 1)
  source : Fin (t.val + 1) → Option (Fin T)
  source_before : ∀ i s, source i = some s → s < t
  center_eq_source : ∀ i, (thread i).center =
    match source i with
    | none => input.origin
    | some s => run.output s
  origin_source_unique : ∃! i, source i = none
  previous_source_unique : ∀ s, s < t → ∃! i, source i = some s
  stopVirtualTime : ℝ
  stopVirtualTime_nonnegative : 0 ≤ stopVirtualTime
  stopVirtualTime_eq_dayVirtualRadius :
    stopVirtualTime = run.dayVirtualRadius t
  rankedVirtualTimeAt :
    Fin (t.val + 1) → Fin (t.val + 1) → ℝ → ℝ
  rankedVirtualTimeAt_zero : ∀ i r, rankedVirtualTimeAt i r 0 = 0
  rankedVirtualTimeAt_nonnegative : ∀ i r τ,
    0 ≤ τ → τ ≤ stopVirtualTime → 0 ≤ rankedVirtualTimeAt i r τ
  rankedVirtualTimeAt_monotone : ∀ i r τ υ,
    0 ≤ τ → τ ≤ υ → υ ≤ stopVirtualTime →
      rankedVirtualTimeAt i r τ ≤ rankedVirtualTimeAt i r υ
  rankedVirtualTimeAt_stop : ∀ i r,
    rankedVirtualTimeAt i r stopVirtualTime =
      (thread i).rankedVirtualTime r
  searchedRadiusAt : Fin (t.val + 1) → ℝ → ℝ
  searchedRadiusAt_eq_schedule : ∀ i τ,
    0 ≤ τ → τ ≤ stopVirtualTime →
      searchedRadiusAt i τ =
        ∑ r, quadratic_decay_rate r.val * rankedVirtualTimeAt i r τ
  searchedRadiusAt_stop : ∀ i,
    searchedRadiusAt i stopVirtualTime = (thread i).searchedRadius
  rank_time_at_le_clock : ∀ τ,
    0 ≤ τ → τ ≤ stopVirtualTime → ∀ r : Fin (t.val + 1),
      (∑ i, rankedVirtualTimeAt i r τ) ≤ τ
  fastest_rank_fills_clock : ∀ τ,
    0 ≤ τ → τ ≤ stopVirtualTime →
      (∑ i, rankedVirtualTimeAt i
        (⟨0, Nat.zero_lt_succ t.val⟩ : Fin (t.val + 1)) τ) = τ
  rank_time_at_antitone : ∀ τ,
    0 ≤ τ → τ ≤ stopVirtualTime → ∀ r s : Fin (t.val + 1), r ≤ s →
      (∑ i, rankedVirtualTimeAt i s τ) ≤
        ∑ i, rankedVirtualTimeAt i r τ
  rank_time_le_virtual_radius : ∀ r : Fin (t.val + 1),
    (∑ i, (thread i).rankedVirtualTime r) ≤ run.dayVirtualRadius t
  fastest_rank_fills_virtual_radius :
    (∑ i, (thread i).rankedVirtualTime
      (⟨0, Nat.zero_lt_succ t.val⟩ : Fin (t.val + 1))) = run.dayVirtualRadius t
  unsubsumedCount : ℕ
  unsubsumedCount_eq :
    unsubsumedCount =
      (Finset.univ.filter fun i => (thread i).subsumedBy = none).card
  persistent_rank_fills_virtual_radius : ∀ r : Fin (t.val + 1),
    r.val < unsubsumedCount →
      (∑ i, (thread i).rankedVirtualTime r) = run.dayVirtualRadius t
  rank_time_antitone : ∀ r s : Fin (t.val + 1), r ≤ s →
    (∑ i, (thread i).rankedVirtualTime s) ≤
      ∑ i, (thread i).rankedVirtualTime r
  valid_subsumption : ∀ i j, (thread i).subsumedBy = some j →
    i ≠ j ∧
    (thread i).subsumingRankAtSubsumption <
      (thread i).rankAtSubsumption ∧
    0 ≤ (thread i).radiusAtSubsumption ∧
    (thread i).radiusAtSubsumption = (thread i).searchedRadius ∧
    (thread i).subsumingRadiusAtSubsumption ≤ (thread j).searchedRadius ∧
    dist (thread j).center (thread i).center ≤
      (thread i).subsumingRadiusAtSubsumption -
        (thread i).radiusAtSubsumption
  subsumptionVirtualTime : Fin (t.val + 1) → ℝ
  activeAt : Fin (t.val + 1) → ℝ → Prop
  activeCountAt : ℝ → ℕ
  activeCountAt_positive : ∀ τ,
    0 ≤ τ → τ ≤ stopVirtualTime → 0 < activeCountAt τ
  activeCountAt_le_threadCount : ∀ τ,
    0 ≤ τ → τ ≤ stopVirtualTime → activeCountAt τ ≤ t.val + 1
  rankAt : Fin (t.val + 1) → ℝ → Fin (t.val + 1)
  initial_rank_eq_source : ∀ i,
    (rankAt i 0).val =
      match source i with
      | none => t.val
      | some s => t.val - (s.val + 1)
  activeAt_iff_rank_lt_activeCount : ∀ i τ,
    0 ≤ τ → τ ≤ stopVirtualTime →
      (activeAt i τ ↔ (rankAt i τ).val < activeCountAt τ)
  active_rank_exhaustive : ∀ τ,
    0 ≤ τ → τ ≤ stopVirtualTime → ∀ r : Fin (t.val + 1),
      r.val < activeCountAt τ →
        ∃! i, activeAt i τ ∧ rankAt i τ = r
  active_rank_order_preserved : ∀ i j τ υ,
    0 ≤ τ → τ ≤ υ → υ ≤ stopVirtualTime →
      activeAt i τ → activeAt j τ → activeAt i υ → activeAt j υ →
      rankAt i τ < rankAt j τ → rankAt i υ < rankAt j υ
  rankedVirtualTimeAt_strict_growth : ∀ i r τ υ,
    0 ≤ τ → τ < υ → υ ≤ stopVirtualTime →
      rankedVirtualTimeAt i r τ < rankedVirtualTimeAt i r υ →
        ∃ ξ, τ ≤ ξ ∧ ξ ≤ υ ∧ activeAt i ξ ∧ rankAt i ξ = r
  assigned_rank_accumulates : ∀ i r τ υ,
    0 ≤ τ → τ ≤ υ → υ ≤ stopVirtualTime →
      (∀ ξ, τ ≤ ξ → ξ ≤ υ → activeAt i ξ ∧ rankAt i ξ = r) →
        rankedVirtualTimeAt i r υ =
          rankedVirtualTimeAt i r τ + (υ - τ)
  ordered_active_radius_separation : ∀ i j τ υ δ,
    0 ≤ τ → τ ≤ υ → υ ≤ stopVirtualTime →
      (∀ ξ, τ ≤ ξ → ξ ≤ υ →
        activeAt i ξ ∧ activeAt j ξ ∧ rankAt i ξ < rankAt j ξ ∧
          δ ≤ quadratic_decay_rate (rankAt i ξ).val -
            quadratic_decay_rate (rankAt j ξ).val) →
      searchedRadiusAt i τ - searchedRadiusAt j τ + δ * (υ - τ) ≤
        searchedRadiusAt i υ - searchedRadiusAt j υ
  bounded_rank_lineage_progress : ∀ {k : ℕ} (hk : 2 ≤ k)
      (i : Fin (t.val + 1)) (point : Solution) (τ υ : ℝ),
    0 ≤ τ → τ ≤ υ → υ ≤ stopVirtualTime →
      activeAt i τ → (rankAt i τ).val < k →
      ∃ j : Fin (t.val + 1),
        Relation.ReflTransGen
            (fun a b => (thread a).subsumedBy = some b) i j ∧
        activeAt j υ ∧ (rankAt j υ).val < k ∧
        searchedRadiusAt i τ - dist (thread i).center point +
              (υ - τ) /
                ((k : ℝ) ^ 2 * (Real.log (k : ℝ)) ^ 2) ≤
            searchedRadiusAt j υ - dist (thread j).center point
  activeAt_iff : ∀ i τ,
    0 ≤ τ → τ ≤ stopVirtualTime →
      (activeAt i τ ↔
        match (thread i).subsumedBy with
        | none => True
        | some _ => τ ≤ subsumptionVirtualTime i)
  valid_subsumption_time : ∀ i j, (thread i).subsumedBy = some j →
    0 ≤ subsumptionVirtualTime i ∧
    subsumptionVirtualTime i ≤ stopVirtualTime ∧
    activeAt i (subsumptionVirtualTime i) ∧
    activeAt j (subsumptionVirtualTime i) ∧
    rankAt j (subsumptionVirtualTime i) <
      rankAt i (subsumptionVirtualTime i) ∧
    searchedRadiusAt i (subsumptionVirtualTime i) =
      (thread i).radiusAtSubsumption ∧
    searchedRadiusAt j (subsumptionVirtualTime i) =
      (thread i).subsumingRadiusAtSubsumption
  containment_forces_subsumption : ∀ i j τ,
    0 ≤ τ → τ < stopVirtualTime →
      activeAt i τ → activeAt j τ → rankAt j τ < rankAt i τ →
      dist (thread j).center (thread i).center ≤
        searchedRadiusAt j τ - searchedRadiusAt i τ →
      ∃ j', (thread i).subsumedBy = some j' ∧
        subsumptionVirtualTime i ≤ τ
  subsumed_call_incomplete : ∀ i j, (thread i).subsumedBy = some j →
    (thread i).radiusAtSubsumption <
      oracle.runtime (input.instanceAt t) (thread i).center
  subsumed_thread_stops : ∀ i j τ, (thread i).subsumedBy = some j →
    subsumptionVirtualTime i ≤ τ → τ ≤ stopVirtualTime →
      searchedRadiusAt i τ = (thread i).radiusAtSubsumption
  no_active_call_completes_before_stop : ∀ i τ,
    0 ≤ τ → τ < stopVirtualTime → activeAt i τ →
      searchedRadiusAt i τ <
        oracle.runtime (input.instanceAt t) (thread i).center
  ownerCollapseCheckpointTime : ∀ {k : ℕ}
    (family : trajectory_family Solution T k) (hk : 2 ≤ k),
      Fin (k + 1) → ℝ
  ownerCollapseLeader : ∀ {k : ℕ}
    (family : trajectory_family Solution T k) (hk : 2 ≤ k),
      Fin (k + 1) → Fin (t.val + 1)
  ownerCollapseCheckpointTime_monotone : ∀ {k : ℕ}
    (family : trajectory_family Solution T k) (hk : 2 ≤ k)
    (n m : Fin (k + 1)), n ≤ m →
      ownerCollapseCheckpointTime family hk n ≤
        ownerCollapseCheckpointTime family hk m
  ownerCollapseInvariant : ∀ {k : ℕ}
    (family : trajectory_family Solution T k) (hk : 2 ≤ k)
    (n : Fin (k + 1)),
      let τ := ownerCollapseCheckpointTime family hk n
      let leader := ownerCollapseLeader family hk n
      let budget :=
        (k : ℝ) ^ 3 * (Real.log (k : ℝ)) ^ 2 *
          ∑ q, if q.val < n.val then
            collapse_owner_charge input.origin
              (fun s => oracle.solution (input.instanceAt s)) family t q
          else 0
      stopVirtualTime ≤ budget ∨
        (0 ≤ τ ∧ τ ≤ stopVirtualTime ∧ τ ≤ budget ∧
          activeAt leader τ ∧
          dist (thread leader).center
              (trajectory_previous_solution input.origin
                (fun s => oracle.solution (input.instanceAt s)) family t) ≤
            searchedRadiusAt leader τ ∧
          (∀ i, activeAt i τ → rankAt i τ < rankAt leader τ →
            ∃ s, source i = some s) ∧
          (∀ i s, activeAt i τ → rankAt i τ < rankAt leader τ →
            source i = some s → family.owner s ≠ family.owner t) ∧
          ∀ (q : Fin k) i j s u, q.val < n.val →
            activeAt i τ → rankAt i τ < rankAt leader τ →
            source i = some s → family.owner s = q →
            activeAt j τ → rankAt j τ < rankAt leader τ →
            source j = some u → family.owner u = q → i = j)
  thread_does_not_overrun : ∀ i,
    (thread i).searchedRadius ≤
      oracle.runtime (input.instanceAt t) (thread i).center
  winner : Fin (t.val + 1)
  winner_not_subsumed : (thread winner).subsumedBy = none
  winner_completes :
    (thread winner).searchedRadius =
      oracle.runtime (input.instanceAt t) (thread winner).center
  output_from_completed_call :
    run.output t = oracle.solution (input.instanceAt t)
  searched_radius_accounting :
    run.daySearchedRadius t = ∑ i, (thread i).searchedRadius
  runtime_accounting :
    run.dayRuntime t =
      ∑ i, ((thread i).warmStartWork + (thread i).overheadRuntime)

def quadratic_decay_algorithm_specification
    {Instance Solution : Type*} [MetricSpace Solution]
    (algorithm : online_ball_search_algorithm Instance Solution) : Prop :=
  ∀ {T : ℕ} (oracle : warm_start_oracle Instance Solution)
    (input : online_ball_search_input Instance Solution T) (t : Fin T),
    Nonempty
      (quadratic_decay_day_execution oracle input (algorithm.run oracle input) t)

class quadratic_decay_event_scheduler
    (Instance Solution : Type*) [MetricSpace Solution] where
  algorithm : online_ball_search_algorithm Instance Solution
  dayExecution : ∀ {T : ℕ} (oracle : warm_start_oracle Instance Solution)
    (input : online_ball_search_input Instance Solution T) (t : Fin T),
    quadratic_decay_day_execution oracle input (algorithm.run oracle input) t

noncomputable def quadratic_decay_algorithm
    (Instance Solution : Type*) [MetricSpace Solution]
    [quadratic_decay_event_scheduler Instance Solution] :
    online_ball_search_algorithm Instance Solution :=
  quadratic_decay_event_scheduler.algorithm

noncomputable def total_searched_radius {Solution : Type*} {T : ℕ}
    (run : quadratic_decay_run Solution T) : ℝ :=
  ∑ t, run.daySearchedRadius t

noncomputable def total_runtime {Solution : Type*} {T : ℕ}
    (run : quadratic_decay_run Solution T) : ℝ :=
  ∑ t, run.dayRuntime t

noncomputable def quadratic_log_scale (k : ℕ) : ℝ :=
  (k : ℝ) ^ 4 * (Real.log (k : ℝ)) ^ 2

theorem online_competitive_with_runtime :
    ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ,
    ∃ C_runtime : ℝ, 0 < C_runtime ∧
    ∀ (Instance Solution : Type*) [MetricSpace Solution]
      [unit_separated_metric Solution]
      [quadratic_decay_event_scheduler Instance Solution],
    quadratic_decay_algorithm_specification
      (quadratic_decay_algorithm Instance Solution) ∧
    (∀ (T : ℕ) (oracle : warm_start_oracle Instance Solution)
      (input : online_ball_search_input Instance Solution T) (t : Fin T),
      ((quadratic_decay_algorithm Instance Solution).run oracle input).output t =
        oracle.solution (input.instanceAt t)) ∧
    (∀ (k : ℕ), k₀ ≤ k → ∀ (T : ℕ)
      (oracle : warm_start_oracle Instance Solution)
      (input : online_ball_search_input Instance Solution T)
      (family : trajectory_family Solution T k),
      total_searched_radius
          ((quadratic_decay_algorithm Instance Solution).run oracle input) ≤
        C * quadratic_log_scale k *
          trajectory_family_cost input.origin
            (fun s => oracle.solution (input.instanceAt s)) family) ∧
    (∀ (T : ℕ)
      (oracle : warm_start_oracle Instance Solution)
      (input : online_ball_search_input Instance Solution T),
      total_runtime
          ((quadratic_decay_algorithm Instance Solution).run oracle input) ≤
        C_runtime * total_searched_radius
          ((quadratic_decay_algorithm Instance Solution).run oracle input)) := by sorry

import Architect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Defs

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators

@[blueprint "def:warm-start-oracle"
  (statement := /-- Let $\mathcal I$ be an instance space and let $S$ be a metric solution space.  A warm-start oracle specifies the true solution $s(I)$ of every instance $I$, together with a nonnegative runtime $\tau(I,P)$ for every prediction $P\in S$, and satisfies $\tau(I,P)\leq d(s(I),P)$. -/)
  (title := /-- Warm-start oracle -/)
  (latexEnv := "definition")]
structure warm_start_oracle (Instance Solution : Type*) [MetricSpace Solution] where
  solution : Instance → Solution
  runtime : Instance → Solution → ℝ
  runtime_nonnegative : ∀ I P, 0 ≤ runtime I P
  runtime_le_dist : ∀ I P, runtime I P ≤ dist (solution I) P

@[blueprint "def:unit-separated-metric"
  (statement := /-- A metric space is unit-separated if every pair of distinct points has distance at least $1$.  This records the normalization that the minimum nonzero distance in the solution space is $1$. -/)
  (title := /-- Unit-separated metric space -/)
  (latexEnv := "definition")]
class unit_separated_metric (Solution : Type*) [MetricSpace Solution] : Prop where
  one_le_dist : ∀ {x y : Solution}, x ≠ y → 1 ≤ dist x y

@[blueprint "def:online-ball-search-input"
  (statement := /-- An online ball-search input of length $T$ is a sequence of instances $I_t$, indexed by $t\in\operatorname{Fin}(T)$, together with the distinguished initial point $0_S$ from which every benchmark trajectory starts. -/)
  (title := /-- Online ball-search input -/)
  (latexEnv := "definition")]
structure online_ball_search_input (Instance Solution : Type*) (T : ℕ) where
  instanceAt : Fin T → Instance
  origin : Solution

@[blueprint "def:trajectory-family"
  (statement := /-- Fix $T,k\in\mathbb N$.  A family of $k$ trajectories assigns every day $t$ to an owner $a(t)\in\operatorname{Fin}(k)$ and a prediction $P_t$.  It also records the closest earlier day on the same trajectory, or records that no such day exists.  The accompanying conditions assert strict precedence, equality of owners, maximality among earlier days of that owner, and the correctness of the no-predecessor case. -/)
  (title := /-- A certified family of trajectories -/)
  (latexEnv := "definition")]
structure trajectory_family (Solution : Type*) (T k : ℕ) where
  owner : Fin T → Fin k
  prediction : Fin T → Solution
  previousDay : Fin T → Option (Fin T)
  previousDay_lt : ∀ {t s}, previousDay t = some s → s < t
  previousDay_owner : ∀ {t s}, previousDay t = some s → owner s = owner t
  previousDay_maximal :
    ∀ {t s u}, previousDay t = some s → u < t → owner u = owner t → u ≤ s
  no_previousDay : ∀ {t}, previousDay t = none → ∀ u, u < t → owner u ≠ owner t

@[blueprint "def:trajectory-previous-prediction"
  (statement := /-- For a day $t$, the preceding prediction on its trajectory is $P_s$ when the certified predecessor is $s$, and is the common origin $0_S$ when $t$ is the first day of that trajectory. -/)
  (title := /-- Previous prediction on a trajectory -/)
  (latexEnv := "definition")]
def trajectory_previous_prediction {Solution : Type*} {T k : ℕ}
    (origin : Solution) (family : trajectory_family Solution T k) (t : Fin T) : Solution :=
  match family.previousDay t with
  | none => origin
  | some s => family.prediction s

@[blueprint "def:trajectory-previous-solution"
  (statement := /-- For a solution sequence $(S_t)$, the preceding solution associated with day $t$ is $S_s$ when $s$ is the certified predecessor on the same trajectory, and is the common origin when no predecessor exists. -/)
  (title := /-- Previous solution on a trajectory -/)
  (latexEnv := "definition")]
def trajectory_previous_solution {Solution : Type*} {T k : ℕ}
    (origin : Solution) (solution : Fin T → Solution)
    (family : trajectory_family Solution T k) (t : Fin T) : Solution :=
  match family.previousDay t with
  | none => origin
  | some s => solution s

@[blueprint "def:trajectory-hit-cost"
  (statement := /-- The hit cost of a trajectory family against solutions $(S_t)$ is $\sum_t d(P_t,S_t)$. -/)
  (title := /-- Hit cost of a trajectory family -/)
  (latexEnv := "definition")]
noncomputable def trajectory_hit_cost {Solution : Type*} [MetricSpace Solution] {T k : ℕ}
    (solution : Fin T → Solution) (family : trajectory_family Solution T k) : ℝ :=
  ∑ t, dist (family.prediction t) (solution t)

@[blueprint "def:trajectory-movement-cost"
  (statement := /-- The movement cost of a trajectory family is the sum, over all days $t$, of the distance from the preceding prediction on the same trajectory to $P_t$; the common origin is used on the first day of each trajectory. -/)
  (title := /-- Movement cost of a trajectory family -/)
  (latexEnv := "definition")]
noncomputable def trajectory_movement_cost {Solution : Type*} [MetricSpace Solution] {T k : ℕ}
    (origin : Solution) (family : trajectory_family Solution T k) : ℝ :=
  ∑ t, dist (trajectory_previous_prediction origin family t) (family.prediction t)

@[blueprint "def:trajectory-family-cost"
  (statement := /-- The cost of a family of trajectories is the sum of its hit cost and its movement cost. -/)
  (title := /-- Total cost of a trajectory family -/)
  (latexEnv := "definition")]
noncomputable def trajectory_family_cost {Solution : Type*} [MetricSpace Solution] {T k : ℕ}
    (origin : Solution) (solution : Fin T → Solution)
    (family : trajectory_family Solution T k) : ℝ :=
  trajectory_hit_cost solution family + trajectory_movement_cost origin family

@[blueprint "def:predict-yesterday-step-cost"
  (statement := /-- On day $t$, the cost of predicting the preceding solution on the same benchmark trajectory is $d(S_{\operatorname{prev}(t)},S_t)$, with the common origin substituted when $t$ has no predecessor. -/)
  (title := /-- One-step predict-yesterday cost -/)
  (latexEnv := "definition")]
noncomputable def predict_yesterday_step_cost {Solution : Type*} [MetricSpace Solution]
    {T k : ℕ} (origin : Solution) (solution : Fin T → Solution)
    (family : trajectory_family Solution T k) (t : Fin T) : ℝ :=
  dist (trajectory_previous_solution origin solution family t) (solution t)

@[blueprint "def:predict-yesterday-cost"
  (statement := /-- The total predict-yesterday cost of a trajectory family is $\sum_t d(S_{\operatorname{prev}(t)},S_t)$, using the common origin on first visits. -/)
  (title := /-- Total predict-yesterday cost -/)
  (latexEnv := "definition")]
noncomputable def predict_yesterday_cost {Solution : Type*} [MetricSpace Solution] {T k : ℕ}
    (origin : Solution) (solution : Fin T → Solution)
    (family : trajectory_family Solution T k) : ℝ :=
  ∑ t, predict_yesterday_step_cost origin solution family t

@[blueprint "def:collapse-interval-charge"
  (statement := /-- For a day $t$, the collapse-interval charge is the sum of predict-yesterday step costs on days strictly before $t$ and strictly after the preceding day on $t$'s trajectory; if $t$ has no predecessor, every earlier day is included. -/)
  (title := /-- Charge in the interval preceding a benchmark day -/)
  (latexEnv := "definition")]
noncomputable def collapse_interval_charge {Solution : Type*} [MetricSpace Solution]
    {T k : ℕ} (origin : Solution) (solution : Fin T → Solution)
    (family : trajectory_family Solution T k) (t : Fin T) : ℝ :=
  by
    classical
    exact ∑ s, if
        (match family.previousDay t with
         | none => True
         | some p => p < s) ∧ s < t
      then predict_yesterday_step_cost origin solution family s
      else 0

@[blueprint "def:collapse-owner-charge"
  (statement := /-- Fix a metric space $S$, an origin, a sequence of $T$ solutions, a certified family of $k$ trajectories, a day $t$, and an owner $q\in\operatorname{Fin}(k)$.  The $q$-component of the collapse-interval charge at $t$ is the sum of the predict-yesterday step costs of precisely those days $s$ that lie strictly after the predecessor of $t$ (when it exists), strictly before $t$, and are owned by $q$. -/)
  (title := /-- Owner component of a collapse-interval charge -/)
  (latexEnv := "definition")]
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

@[blueprint "lem:collapse-owner-charge-partition"
  (statement := /-- Let $T,k\in\mathbb N$, let $S$ be a metric space, fix an origin $o\in S$ and a sequence $(S_s)_{s\in\operatorname{Fin}(T)}$ in $S$, and let a certified family of $k$ trajectories own the days.  For every $t\in\operatorname{Fin}(T)$, the collapse-interval charge determined by $o$, $(S_s)$, and the family is the sum, over all $q\in\operatorname{Fin}(k)$, of its $q$-components. -/)
  (proof := /-- Expand the scalar charge using \cref{def:collapse-interval-charge} and every owner component using \cref{def:collapse-owner-charge}.  Interchange the two finite sums.  For each day $s$ in the collapse interval, the certified owner $\operatorname{owner}(s)\in\operatorname{Fin}(k)$ contributes its predict-yesterday step cost to exactly one inner summand, while every other owner contributes zero.  Thus the inner sum equals the scalar summand at $s$, and summing over $s$ proves the identity. -/)
  (title := /-- Collapse charge is partitioned by owners -/)
  (latexEnv := "lemma")]
lemma collapse_owner_charge_partition {Solution : Type*} [MetricSpace Solution]
    {T k : ℕ} (origin : Solution) (solution : Fin T → Solution)
    (family : trajectory_family Solution T k) (t : Fin T) :
    collapse_interval_charge origin solution family t =
      ∑ q, collapse_owner_charge origin solution family t q := by
  classical
  unfold collapse_interval_charge collapse_owner_charge
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h :
      (match family.previousDay t with
       | none => True
       | some p => p < s) ∧ s < t <;>
    simp [h]

@[blueprint "def:quadratic-decay-run"
  (statement := /-- A run over $T$ days records the solution output on every day together with that day's virtual radius, total searched radius, and runtime.  Each of the three cost quantities is nonnegative. -/)
  (title := /-- Output and cost trace of an online search run -/)
  (latexEnv := "definition")]
structure quadratic_decay_run (Solution : Type*) (T : ℕ) where
  output : Fin T → Solution
  dayVirtualRadius : Fin T → ℝ
  daySearchedRadius : Fin T → ℝ
  dayRuntime : Fin T → ℝ
  dayVirtualRadius_nonnegative : ∀ t, 0 ≤ dayVirtualRadius t
  daySearchedRadius_nonnegative : ∀ t, 0 ≤ daySearchedRadius t
  dayRuntime_nonnegative : ∀ t, 0 ≤ dayRuntime t

@[blueprint "def:online-ball-search-algorithm"
  (statement := /-- Fix an instance type and a metric solution space.  An online ball-search algorithm assigns to every finite horizon, warm-start oracle, and input sequence a run containing its daily outputs and cost trace.  This assignment is nonanticipating: if two inputs have the same origin and their instances agree through a day $t$, then the output, virtual radius, searched radius, and runtime recorded on day $t$ are equal for the two runs. -/)
  (title := /-- Online ball-search algorithm -/)
  (latexEnv := "definition")]
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

@[blueprint "def:quadratic-decay-rate"
  (statement := /-- The thread occupying rank $r$ in the quadratic-decay schedule runs at rate $1$ when $r=0$, and at rate
  \[
    \frac{1}{(r+1)^2\log^2(r+1)}
  \]
  when $r\geq 1$.  Thus rank zero is the fastest rank, and the remaining rates are the prescribed summable quadratic-decay schedule. -/)
  (title := /-- Quadratic-decay thread rate -/)
  (latexEnv := "definition")]
noncomputable def quadratic_decay_rate (rank : ℕ) : ℝ :=
  if rank = 0 then 1
  else 1 / (((rank + 1 : ℕ) : ℝ) ^ 2 * (Real.log ((rank + 1 : ℕ) : ℝ)) ^ 2)

@[blueprint "def:quadratic-decay-thread-execution"
  (statement := /-- Fix a finite collection of threads.  The execution record of one thread consists of its prediction center, the nonnegative amount of virtual time for which it occupies each rate rank, the resulting searched radius, the warm-start work performed, and the nonnegative scheduling and pruning overhead charged to it.  The searched radius is the rank-rate-weighted virtual time, the warm-start work equals that radius, and the overhead is at most the corresponding rank-weighted work, with rank $r$ charged at most $r+1$ accounting units per unit of searched work.  If the thread is pruned, the record also identifies the subsuming thread and records both radii and both rate ranks at the moment of subsumption. -/)
  (title := /-- Accounted execution of one quadratic-decay thread -/)
  (latexEnv := "definition")]
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

@[blueprint "def:quadratic-decay-day-execution"
  (statement := /-- Fix a day $t$ of an online input and a proposed run trace.  A quadratic-decay execution certificate has exactly one thread for the origin and one for every earlier returned solution.  It records, at every virtual time from zero to a distinguished stopping time, each thread's cumulative occupancy of every rate rank and its consequent searched radius.  These histories start at zero, are nonnegative and nondecreasing, agree with the final thread records at the stopping time, and distribute virtual time among the ranks according to \cref{def:quadratic-decay-rate}.

  Initially, the threads are ordered by recency: the thread sourced from an earlier day $s<t$ has rank $t-s-1$, while the origin thread has rank $t$.  Thus the most recently returned solution is fastest and every older source is slower.  A thread is active through its recorded subsumption time and inactive thereafter; an unsubsumed thread remains active through the stopping time.  At every virtual time, the active threads are assigned bijectively to the initial segment of rate ranks: each active thread has one rank, and every rank below the active-thread count has exactly one owner.  The strict rank order of two threads is preserved for as long as both remain active, so removing a thread merely compacts the surviving ranks.  Rank-time can increase only on an interval containing a time at which the thread is active at that rank, and it increases by the interval length whenever that assignment persists throughout the interval.  More generally, let two threads remain active on a closed virtual-time interval, with the first strictly faster throughout.  If their instantaneous rate difference is bounded below by a real number $\delta$ throughout that interval, then their faster-minus-slower searched-radius difference increases by at least $\delta$ times the length of the interval.  This separation law remains valid when other threads are removed and the two ranks compact during the interval.

  The certificate also records global progress along every subsumption lineage.  Fix an integer $k\geq2$, virtual times $0\leq\tau\leq\upsilon$ not exceeding the stopping time, a point $P$, and a thread that is active at time $\tau$ with rank strictly below $k$.  At time $\upsilon$ there is an active thread, still of rank strictly below $k$, that is obtained from the original thread by zero or more successive subsumptions.  Along this lineage the containment potential with respect to $P$, defined as the searched radius minus the distance from the thread center to $P$, increases by at least
  \[
    \frac{\upsilon-\tau}{k^2\log^2 k}.
  \]
  In particular, containment potential is preserved across the inclusive time of every subsumption event, while service before and after that event contributes to the same lower bound.

  A subsumption event occurs no later than the stopping time, while both the subsumed thread and its strictly faster subsumer are active, and the two radii in its containment certificate are their radii at that event.  Conversely, at every virtual time strictly before the stopping time, whenever the searched ball of a faster active thread contains that of a slower active thread, the slower thread is subsumed no later than that virtual time.  The subsumed warm-start call must still be incomplete then and receives no further work.  Before the stopping time, every active warm-start call is incomplete.  At the stopping time the designated active winner completes, so it is a genuinely first completed call, with simultaneous completions permitted; if containment first occurs at that same time, completion takes precedence.

  Every thread performs precisely its final searched radius of warm-start work and never runs past completion.  For every certified family of $k\geq2$ benchmark trajectories, the certificate also records $k+1$ owner-indexed collapse checkpoints.  At stage $n$, either the day has already stopped within the cumulative budget of the first $n$ owners, or there is an active leading thread whose searched ball contains the benchmark predecessor, every faster thread has a benchmark owner, the current day's owner supplies no faster thread, and each of the first $n$ owners supplies at most one faster thread.  The checkpoint times are nondecreasing, and the stage-$n$ time is bounded by $k^3(\log k)^2$ times the sum of the corresponding owner components from \cref{def:collapse-owner-charge}.  Hence each owner is charged at most once even when pruning changes the leading thread.

  Finally, the certificate identifies the returned solution with the output of the winner's completed call and identifies the trace's searched radius and runtime with, respectively, the sum of the final thread radii and the sum, over all threads, of warm-start work plus scheduling and pruning overhead.  The rank-weighted overhead bound in \cref{def:quadratic-decay-thread-execution} makes this accounting uniform over the number of threads. -/)
  (title := /-- Certified daily execution of quadratic decay -/)
  (latexEnv := "definition")]
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

@[blueprint "def:quadratic-decay-algorithm-specification"
  (statement := /-- A nonanticipating online ball-search algorithm is the quadratic-decay algorithm if, for every finite horizon, every warm-start oracle, every online input, and every day, its observable run admits the certificate of \cref{def:quadratic-decay-day-execution}.  Thus the origin and earlier outputs receive their prescribed initial ranks, active threads uniquely occupy the initial segment of rate ranks, rank-time follows those assignments, searched-ball containment forces pruning, the owner-indexed collapse checkpoints preserve cumulative charge disjointness for every benchmark family, execution stops at the first completed call, and scheduling and pruning overhead obey the uniform rank-weighted bound. -/)
  (title := /-- Operational specification of quadratic decay -/)
  (latexEnv := "definition")]
def quadratic_decay_algorithm_specification
    {Instance Solution : Type*} [MetricSpace Solution]
    (algorithm : online_ball_search_algorithm Instance Solution) : Prop :=
  ∀ {T : ℕ} (oracle : warm_start_oracle Instance Solution)
    (input : online_ball_search_input Instance Solution T) (t : Fin T),
    Nonempty
      (quadratic_decay_day_execution oracle input (algorithm.run oracle input) t)

@[blueprint "def:quadratic-decay-event-scheduler"
  (statement := /-- Fix an instance type and a metric solution space.  A certified quadratic-decay event scheduler supplies a nonanticipating online ball-search algorithm together with a concrete execution record on every day, for every finite horizon, warm-start oracle, and online input.  The algorithm field supplies the prefix-invariance law, while each daily record supplies the first-event choices, deterministic resolution of simultaneous events, finite pruning history, spliced rank-time histories, owner-indexed cumulative collapse checkpoints, first-completion rule, and runtime accounting required by \cref{def:quadratic-decay-day-execution}.  This structure is the explicit formal implementation interface for the event scheduler analyzed in the source algorithm. -/)
  (title := /-- Certified event scheduler for quadratic decay -/)
  (latexEnv := "definition")]
class quadratic_decay_event_scheduler
    (Instance Solution : Type*) [MetricSpace Solution] where
  algorithm : online_ball_search_algorithm Instance Solution
  dayExecution : ∀ {T : ℕ} (oracle : warm_start_oracle Instance Solution)
    (input : online_ball_search_input Instance Solution T) (t : Fin T),
    quadratic_decay_day_execution oracle input (algorithm.run oracle input) t

@[blueprint "lem:quadratic-decay-algorithm-exists"
  (statement := /-- For every instance type and metric solution space equipped with a certified event scheduler as in \cref{def:quadratic-decay-event-scheduler}, there exists a nonanticipating online ball-search algorithm satisfying the operational quadratic-decay specification of \cref{def:quadratic-decay-algorithm-specification}. -/)
  (proof := /-- Let a certified scheduler be given.  Take the online algorithm stored in \cref{def:quadratic-decay-event-scheduler}; its algorithm field already includes the required prefix-invariance law.  For an arbitrary horizon, warm-start oracle, online input, and day, the scheduler's daily field supplies a concrete record of the form \cref{def:quadratic-decay-day-execution}.  Placing that record in its nonempty wrapper proves the operational specification in \cref{def:quadratic-decay-algorithm-specification}, and the stored algorithm is the required witness. -/)
  (title := /-- A certified scheduler yields the quadratic-decay algorithm -/)
  (latexEnv := "lemma")]
lemma quadratic_decay_algorithm_exists
    (Instance Solution : Type*) [MetricSpace Solution]
    [quadratic_decay_event_scheduler Instance Solution] :
    ∃ algorithm : online_ball_search_algorithm Instance Solution,
      quadratic_decay_algorithm_specification algorithm := by
  refine ⟨quadratic_decay_event_scheduler.algorithm, ?_⟩
  intro T oracle input t
  exact ⟨quadratic_decay_event_scheduler.dayExecution oracle input t⟩

@[blueprint "def:quadratic-decay-algorithm"
  (statement := /-- Given a certified event scheduler, the quadratic-decay online ball-search algorithm is the nonanticipating, trajectory-count-oblivious, first-completion procedure selected by \cref{lem:quadratic-decay-algorithm-exists}.  On day $t$, the output from each earlier day $s<t$ initially has recency rank $t-s-1$, and the origin has rank $t$. -/)
  (title := /-- Quadratic-decay online algorithm -/)
  (latexEnv := "definition")]
noncomputable def quadratic_decay_algorithm
    (Instance Solution : Type*) [MetricSpace Solution]
    [quadratic_decay_event_scheduler Instance Solution] :
    online_ball_search_algorithm Instance Solution :=
  Classical.choose (quadratic_decay_algorithm_exists Instance Solution)

@[blueprint "lem:quadratic-decay-algorithm-satisfies-specification"
  (statement := /-- For every instance type and metric solution space equipped with a certified event scheduler, the distinguished quadratic-decay algorithm is nonanticipating and satisfies the prescribed-initial-rank, time-respecting, first-completion specification of \cref{def:quadratic-decay-algorithm-specification}. -/)
  (proof := /-- The existence result \cref{lem:quadratic-decay-algorithm-exists}, applied to the supplied scheduler, gives a nonanticipating algorithm together with daily certificates whose source threads have their prescribed initial ranks and whose execution histories stop at the first unpruned completion.  The distinguished algorithm of \cref{def:quadratic-decay-algorithm} is chosen from that certified pair and therefore retains the full specification. -/)
  (title := /-- The distinguished algorithm has certified executions -/)
  (latexEnv := "lemma")]
lemma quadratic_decay_algorithm_satisfies_specification
    (Instance Solution : Type*) [MetricSpace Solution]
    [quadratic_decay_event_scheduler Instance Solution] :
    quadratic_decay_algorithm_specification
      (quadratic_decay_algorithm Instance Solution) := by
  exact Classical.choose_spec (quadratic_decay_algorithm_exists Instance Solution)

@[blueprint "lem:quadratic-decay-correct"
  (statement := /-- Let the instance and solution types be arbitrary, let the solution type be a metric space, and assume a certified quadratic-decay event scheduler.  For every horizon $T\in\mathbb{N}$, warm-start oracle, online input of horizon $T$, and day $t\in\operatorname{Fin}(T)$, the output of the distinguished quadratic-decay procedure on day $t$ is the oracle-designated solution of the instance arriving on day $t$. -/)
  (proof := /-- Apply \cref{lem:quadratic-decay-algorithm-satisfies-specification} to the given oracle, input, and day, and choose the resulting nonempty certificate from \cref{def:quadratic-decay-day-execution}.  The certificate's output-from-completed-call field is exactly the asserted equality between the recorded output and the oracle-designated solution. -/)
  (title := /-- Quadratic decay solves every online instance -/)
  (latexEnv := "lemma")]
lemma quadratic_decay_correct
    {Instance Solution : Type*} [MetricSpace Solution]
    [quadratic_decay_event_scheduler Instance Solution] {T : ℕ}
    (oracle : warm_start_oracle Instance Solution)
    (input : online_ball_search_input Instance Solution T) (t : Fin T) :
    ((quadratic_decay_algorithm Instance Solution).run oracle input).output t =
      oracle.solution (input.instanceAt t) := by
  exact (Classical.choice
    (quadratic_decay_algorithm_satisfies_specification
      Instance Solution oracle input t)).output_from_completed_call

@[blueprint "def:total-virtual-radius"
  (statement := /-- The total virtual radius of a run is the sum of its virtual radii over all days. -/)
  (title := /-- Total virtual radius -/)
  (latexEnv := "definition")]
noncomputable def total_virtual_radius {Solution : Type*} {T : ℕ}
    (run : quadratic_decay_run Solution T) : ℝ :=
  ∑ t, run.dayVirtualRadius t

@[blueprint "def:total-searched-radius"
  (statement := /-- The total searched radius of a run is the sum of the radii searched over all days. -/)
  (title := /-- Total searched radius -/)
  (latexEnv := "definition")]
noncomputable def total_searched_radius {Solution : Type*} {T : ℕ}
    (run : quadratic_decay_run Solution T) : ℝ :=
  ∑ t, run.daySearchedRadius t

@[blueprint "def:total-runtime"
  (statement := /-- The total runtime of a run is the sum of its runtimes over all days. -/)
  (title := /-- Total runtime -/)
  (latexEnv := "definition")]
noncomputable def total_runtime {Solution : Type*} {T : ℕ}
    (run : quadratic_decay_run Solution T) : ℝ :=
  ∑ t, run.dayRuntime t

@[blueprint "def:quadratic-log-scale"
  (statement := /-- The asymptotic competitive scale at trajectory count $k$ is $k^4(\log k)^2$, interpreted over the real numbers. -/)
  (title := /-- Quartic logarithmic competitive scale -/)
  (latexEnv := "definition")]
noncomputable def quadratic_log_scale (k : ℕ) : ℝ :=
  (k : ℝ) ^ 4 * (Real.log (k : ℝ)) ^ 2

@[blueprint "lem:predict-yesterday-cost-bound"
  (statement := /-- Let $T,k\in\mathbb N$, let $\mathcal S$ be a metric space, fix an origin $o\in\mathcal S$, and let $(S_t)_{t\in\operatorname{Fin}(T)}$ be a sequence in $\mathcal S$.  For every certified family $P$ of $k$ trajectories on these $T$ indices, the sum of the distances from the preceding solution on the same trajectory to $S_t$ is at most twice the hit-plus-movement cost of $P$.  On the first index of each trajectory, the origin $o$ is used in place of both the preceding solution and the preceding prediction. -/)
  (proof := /-- First consider the days that have a predecessor.  The predecessor map is injective on these days: if two distinct days had the same predecessor, order the days with the earlier one first.  The ownership and maximality clauses of \cref{def:trajectory-family} would place the earlier day at or before their common predecessor, contradicting the strict-precedence clause.  The first days contribute zero to the distance between the preceding solution and preceding prediction by \cref{def:trajectory-previous-solution, def:trajectory-previous-prediction}.  Reindexing the remaining sum along the injective predecessor map, using symmetry of the metric, and enlarging its image to all days therefore bounds it by the hit cost in \cref{def:trajectory-hit-cost}.  For each day, the triangle inequality applied through the preceding prediction and then the current prediction bounds the step cost from \cref{def:predict-yesterday-step-cost} by the preceding hit term, the current movement term, and the current hit term.  Summing this inequality and invoking \cref{def:predict-yesterday-cost, def:trajectory-movement-cost, def:trajectory-family-cost} gives at most twice the hit cost plus the movement cost.  The movement cost is nonnegative, so this is at most twice the hit-plus-movement cost. -/)
  (title := /-- Predicting yesterday is controlled by one trajectory family -/)
  (latexEnv := "lemma")]
lemma predict_yesterday_cost_bound {Solution : Type*} [MetricSpace Solution] {T k : ℕ}
    (origin : Solution) (solution : Fin T → Solution)
    (family : trajectory_family Solution T k) :
    predict_yesterday_cost origin solution family ≤
      2 * trajectory_family_cost origin solution family := by
  classical
  let active : Finset (Fin T) :=
    Finset.univ.filter fun t => family.previousDay t ≠ none
  let used : Finset (Fin T) :=
    Finset.univ.filter fun s => ∃ t, family.previousDay t = some s
  have previousDay_injective :
      ∀ {t u s : Fin T}, family.previousDay t = some s →
        family.previousDay u = some s → t = u := by
    intro t u s ht hu
    rcases lt_trichotomy t u with htu | htu | htu
    · have howner : family.owner t = family.owner u := by
        rw [← family.previousDay_owner ht, ← family.previousDay_owner hu]
      have hle := family.previousDay_maximal hu htu howner
      exact False.elim ((not_lt_of_ge hle) (family.previousDay_lt ht))
    · exact htu
    · have howner : family.owner u = family.owner t := by
        rw [← family.previousDay_owner hu, ← family.previousDay_owner ht]
      have hle := family.previousDay_maximal ht htu howner
      exact False.elim ((not_lt_of_ge hle) (family.previousDay_lt hu))
  have remove_first_days :
      (∑ t ∈ active,
          dist (trajectory_previous_solution origin solution family t)
            (trajectory_previous_prediction origin family t)) =
        ∑ t, dist (trajectory_previous_solution origin solution family t)
          (trajectory_previous_prediction origin family t) := by
    apply Finset.sum_subset
    · simpa [active] using
        (Finset.filter_subset Finset.univ
          (fun t => family.previousDay t ≠ none))
    · intro t ht ht_not_active
      cases hprev : family.previousDay t with
      | none =>
          simp [trajectory_previous_solution, trajectory_previous_prediction, hprev]
      | some s =>
          exact False.elim (ht_not_active (by simp [active, hprev]))
  have reindex_previous_hits :
      (∑ t ∈ active,
          dist (trajectory_previous_solution origin solution family t)
            (trajectory_previous_prediction origin family t)) =
        ∑ s ∈ used, dist (family.prediction s) (solution s) := by
    apply Finset.sum_bij (fun t _ => (family.previousDay t).getD t)
    · intro t ht
      have htne : family.previousDay t ≠ none := by
        simpa [active] using ht
      obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp htne
      simp only [used, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨t, by simpa [hs] using hs⟩
    · intro t ht u hu heq
      have htne : family.previousDay t ≠ none := by
        simpa [active] using ht
      have hune : family.previousDay u ≠ none := by
        simpa [active] using hu
      obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp htne
      obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hune
      simp [hs, hr] at heq
      subst r
      exact previousDay_injective hs hr
    · intro s hs
      have hex : ∃ t, family.previousDay t = some s := by
        simpa [used] using hs
      obtain ⟨t, ht⟩ := hex
      refine ⟨t, ?_, ?_⟩
      · simp [active, ht]
      · simp [ht]
    · intro t ht
      have htne : family.previousDay t ≠ none := by
        simpa [active] using ht
      obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp htne
      simp [trajectory_previous_solution, trajectory_previous_prediction, hs,
        dist_comm]
  have previous_hits_le_hit_cost :
      (∑ t, dist (trajectory_previous_solution origin solution family t)
          (trajectory_previous_prediction origin family t)) ≤
        ∑ t, dist (family.prediction t) (solution t) := by
    calc
      _ = ∑ t ∈ active,
          dist (trajectory_previous_solution origin solution family t)
            (trajectory_previous_prediction origin family t) := remove_first_days.symm
      _ = ∑ s ∈ used, dist (family.prediction s) (solution s) :=
        reindex_previous_hits
      _ ≤ ∑ s, dist (family.prediction s) (solution s) :=
        Finset.sum_le_univ_sum_of_nonneg (fun _ => dist_nonneg)
  unfold predict_yesterday_cost predict_yesterday_step_cost trajectory_family_cost
    trajectory_hit_cost trajectory_movement_cost
  calc
    (∑ t, dist (trajectory_previous_solution origin solution family t) (solution t)) ≤
        ∑ t, (dist (trajectory_previous_solution origin solution family t)
              (trajectory_previous_prediction origin family t) +
            dist (trajectory_previous_prediction origin family t)
              (family.prediction t) +
            dist (family.prediction t) (solution t)) := by
      exact Finset.sum_le_sum fun t _ => dist_triangle4 _ _ _ _
    _ = (∑ t, dist (trajectory_previous_solution origin solution family t)
          (trajectory_previous_prediction origin family t)) +
        (∑ t, dist (trajectory_previous_prediction origin family t)
          (family.prediction t)) +
        ∑ t, dist (family.prediction t) (solution t) := by
      simp only [Finset.sum_add_distrib]
    _ ≤ (∑ t, dist (family.prediction t) (solution t)) +
        (∑ t, dist (trajectory_previous_prediction origin family t)
          (family.prediction t)) +
        ∑ t, dist (family.prediction t) (solution t) := by
      linarith [previous_hits_le_hit_cost]
    _ ≤ 2 * ((∑ t, dist (family.prediction t) (solution t)) +
        ∑ t, dist (trajectory_previous_prediction origin family t)
          (family.prediction t)) := by
      have movement_nonnegative :
          0 ≤ ∑ t, dist (trajectory_previous_prediction origin family t)
            (family.prediction t) :=
        Finset.sum_nonneg fun _ _ => dist_nonneg
      linarith

@[blueprint "lem:collapse-interval-charging-bound"
  (statement := /-- Let $T,k\in\mathbb N$, let $S$ be a metric space, fix an origin in $S$ and a sequence of $T$ solutions, and let a certified family of $k$ trajectories own these days.  For every $q\in\operatorname{Fin}(k)$, the sum of the collapse-interval charges over the days owned by $q$ is at most the total predict-yesterday cost of the entire trajectory family. -/)
  (proof := /-- Expand the charges using \cref{def:collapse-interval-charge} and interchange the two finite sums.  Fix a day $s$, and consider two days $a<b$, both owned by $q$, whose preceding intervals contain $s$.  If $b$ has no preceding day, the no-predecessor condition in \cref{def:trajectory-family} contradicts the fact that the earlier day $a$ has the same owner.  Otherwise, if $p$ is the preceding day of $b$, predecessor maximality in \cref{def:trajectory-family} gives $a\leq p$, whereas membership of $s$ in the two intervals gives $p<s<a$, again a contradiction.  Consequently, at most one summand charges the predict-yesterday step at $s$.  This step cost is nonnegative because it is a metric distance by \cref{def:predict-yesterday-step-cost}; hence its total coefficient is at most one.  Summing this pointwise estimate over $s$ and applying \cref{def:predict-yesterday-cost} proves the inequality. -/)
  (title := /-- Disjoint charging of collapse intervals -/)
  (latexEnv := "lemma")]
lemma collapse_interval_charging_bound {Solution : Type*} [MetricSpace Solution]
    {T k : ℕ} (origin : Solution) (solution : Fin T → Solution)
    (family : trajectory_family Solution T k) (q : Fin k) :
    (∑ t, if family.owner t = q then
      collapse_interval_charge origin solution family t else 0) ≤
      predict_yesterday_cost origin solution family := by
  classical
  unfold collapse_interval_charge predict_yesterday_cost
  calc
    (∑ t, if family.owner t = q then
        ∑ s, if
            (match family.previousDay t with
             | none => True
             | some p => p < s) ∧ s < t
          then predict_yesterday_step_cost origin solution family s
          else 0
      else 0) =
        ∑ t, ∑ s, if family.owner t = q ∧
            ((match family.previousDay t with
              | none => True
              | some p => p < s) ∧ s < t)
          then predict_yesterday_step_cost origin solution family s
          else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      by_cases hq : family.owner t = q <;> simp [hq]
    _ = ∑ s, ∑ t, if family.owner t = q ∧
            ((match family.previousDay t with
              | none => True
              | some p => p < s) ∧ s < t)
          then predict_yesterday_step_cost origin solution family s
          else 0 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ s, predict_yesterday_step_cost origin solution family s := by
      apply Finset.sum_le_sum
      intro s hs
      let A : Finset (Fin T) := Finset.univ.filter fun t =>
        family.owner t = q ∧
          ((match family.previousDay t with
            | none => True
            | some p => p < s) ∧ s < t)
      have no_two {a b : Fin T} (ha : a ∈ A) (hb : b ∈ A)
          (hab : a < b) : False := by
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        rcases ha with ⟨haq, ha_previous, hsa⟩
        rcases hb with ⟨hbq, hb_previous, hsb⟩
        have hab_owner : family.owner a = family.owner b := haq.trans hbq.symm
        cases hpb : family.previousDay b with
        | none =>
            exact (family.no_previousDay hpb a hab) hab_owner
        | some p =>
            have hap : a ≤ p :=
              family.previousDay_maximal hpb hab hab_owner
            have hps : p < s := by
              simpa [hpb] using hb_previous
            exact (not_lt_of_ge hap) (lt_trans hps hsa)
      have hA : A.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        exact le_antisymm
          (le_of_not_gt fun hba => no_two hb ha hba)
          (le_of_not_gt fun hab => no_two ha hb hab)
      rw [← Finset.sum_filter]
      change (∑ t ∈ A, predict_yesterday_step_cost origin solution family s) ≤
        predict_yesterday_step_cost origin solution family s
      rw [Finset.sum_const]
      have hA_real : (A.card : ℝ) ≤ 1 := by
        exact_mod_cast hA
      have hs_nonnegative :
          0 ≤ predict_yesterday_step_cost origin solution family s := by
        unfold predict_yesterday_step_cost
        exact dist_nonneg
      simpa [nsmul_eq_mul] using
        mul_le_mul_of_nonneg_right hA_real hs_nonnegative

@[blueprint "lem:quadratic-decay-day-virtual-radius-bound"
  (statement := /-- Let the instance and solution types be arbitrary, equip the solution type with a metric, and assume a certified quadratic-decay event scheduler.  For every horizon $T\in\mathbb N$, trajectory count $k\in\mathbb N$ with $k\geq2$, warm-start oracle, online ball-search input of horizon $T$, certified family of $k$ trajectories, and day $t\in\operatorname{Fin}(T)$, the day-$t$ virtual radius of the distinguished quadratic-decay run is at most
  \[
    k^3(\log k)^2 C_t+k^2(\log k)^2 d(S_{\operatorname{prev}(t)},S_t),
  \]
  where $S_s$ is the oracle-designated solution of the instance on day $s$, $S_{\operatorname{prev}(t)}$ is the solution on the preceding day owned by the same trajectory, with the input origin used when no such day exists, and $C_t$ is the sum of these predecessor-to-current solution distances over the days strictly after $\operatorname{prev}(t)$ and strictly before $t$. -/)
  (proof := /-- Obtain the certified execution of day $t$ from \cref{lem:quadratic-decay-algorithm-satisfies-specification}.  Apply its owner-collapse invariant at the final checkpoint $n=k$.  The cumulative budget there includes every owner exactly once.  By \cref{lem:collapse-owner-charge-partition}, its sum of owner components is exactly $C_t$, so the checkpoint budget is the first displayed term.

  If the early-completion alternative of the invariant holds, the stopping virtual radius is already bounded by this first term, and the asserted inequality follows because the predict-yesterday step cost and its coefficient are nonnegative.  Otherwise, the invariant supplies a checkpoint within that budget and an active leading thread whose searched ball contains the preceding benchmark solution.  Suppose that the leader's rank were at least $k$.  Since active ranks form an initial segment by \cref{def:quadratic-decay-day-execution}, choose an active thread at each rank $q<k$ and send $q$ to the benchmark owner of that thread.  The owner-collapse invariant makes this self-map of $\operatorname{Fin}(k)$ injective, hence surjective, whereas its exclusion of the current day's owner shows that this owner is not in the image.  This contradiction proves that the leader's rank is strictly less than $k$.

  Put $B=k^2\log^2 k$ and let $D$ be the predict-yesterday step cost on day $t$.  Both are nonnegative, and $B$ is positive because $k\geq2$.  Suppose, toward a contradiction, that the stopping time is larger than the collapse budget plus $BD$.  Since the checkpoint time $\tau$ is at most the collapse budget, the time $\upsilon=\tau+BD$ is then strictly before the stopping time.  Apply the bounded-rank lineage-progress law in \cref{def:quadratic-decay-day-execution} to the leader, with the preceding benchmark solution as the fixed point.  The initial containment potential is nonnegative, so at time $\upsilon$ the law produces an active subsumption successor of rank below $k$ whose containment potential is at least $(\upsilon-\tau)/B=D$.  The triangle inequality therefore shows that this successor's searched radius is at least its distance from the current solution.  The warm-start runtime bound then says that its call has completed by time $\upsilon$, contradicting the clause of \cref{def:quadratic-decay-day-execution} that no active call completes strictly before the stopping time.  Consequently the stopping time is at most the collapse budget plus $BD$; its equality with the day virtual radius gives the stated estimate. -/)
  (title := /-- Per-day virtual-radius estimate from trajectory collapse -/)
  (latexEnv := "lemma")]
lemma quadratic_decay_day_virtual_radius_bound
    {Instance Solution : Type*} [MetricSpace Solution]
    [quadratic_decay_event_scheduler Instance Solution] {T k : ℕ}
    (oracle : warm_start_oracle Instance Solution)
    (input : online_ball_search_input Instance Solution T)
    (family : trajectory_family Solution T k) (hk : 2 ≤ k) (t : Fin T) :
    ((quadratic_decay_algorithm Instance Solution).run oracle input).dayVirtualRadius t ≤
      (k : ℝ) ^ 3 * (Real.log (k : ℝ)) ^ 2 *
          collapse_interval_charge input.origin
            (fun s => oracle.solution (input.instanceAt s)) family t +
        (k : ℝ) ^ 2 * (Real.log (k : ℝ)) ^ 2 *
          predict_yesterday_step_cost input.origin
            (fun s => oracle.solution (input.instanceAt s)) family t := by
  classical
  obtain ⟨execution⟩ :=
    quadratic_decay_algorithm_satisfies_specification
      Instance Solution oracle input t
  let n : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  have hcheckpoint := execution.ownerCollapseInvariant family hk n
  simp [n] at hcheckpoint
  rw [← collapse_owner_charge_partition input.origin
    (fun s => oracle.solution (input.instanceAt s)) family t] at hcheckpoint
  rcases hcheckpoint with hstop | hcheckpoint
  · rw [← execution.stopVirtualTime_eq_dayVirtualRadius]
    exact hstop.trans (le_add_of_nonneg_right (by
      unfold predict_yesterday_step_cost
      positivity))
  · rcases hcheckpoint with
      ⟨hτ0, hτstop, hτbudget, hactive, hcontains,
        hsourced, hnotowner, hunique⟩
    let τ := execution.ownerCollapseCheckpointTime family hk n
    let leader := execution.ownerCollapseLeader family hk n
    change 0 ≤ τ at hτ0
    change τ ≤ execution.stopVirtualTime at hτstop
    change τ ≤
      (k : ℝ) ^ 3 * (Real.log (k : ℝ)) ^ 2 *
        collapse_interval_charge input.origin
          (fun s => oracle.solution (input.instanceAt s)) family t at hτbudget
    change execution.activeAt leader τ at hactive
    change dist (execution.thread leader).center
        (trajectory_previous_solution input.origin
          (fun s => oracle.solution (input.instanceAt s)) family t) ≤
      execution.searchedRadiusAt leader τ at hcontains
    change ∀ i, execution.activeAt i τ →
      execution.rankAt i τ < execution.rankAt leader τ →
      ∃ s, execution.source i = some s at hsourced
    change ∀ i s, execution.activeAt i τ →
      execution.rankAt i τ < execution.rankAt leader τ →
      execution.source i = some s →
      family.owner s ≠ family.owner t at hnotowner
    change ∀ (q : Fin k) i j s u,
      execution.activeAt i τ →
      execution.rankAt i τ < execution.rankAt leader τ →
      execution.source i = some s → family.owner s = q →
      execution.activeAt j τ →
      execution.rankAt j τ < execution.rankAt leader τ →
      execution.source j = some u → family.owner u = q → i = j at hunique
    have hrank : (execution.rankAt leader τ).val < k := by
      by_contra h
      have hk_le_rank :
          k ≤ (execution.rankAt leader τ).val :=
        Nat.le_of_not_gt h
      have hleader_count :
          (execution.rankAt leader τ).val <
            execution.activeCountAt τ :=
        (execution.activeAt_iff_rank_lt_activeCount
          leader τ hτ0 hτstop).mp hactive
      have hq_rank (q : Fin k) :
          q.val < (execution.rankAt leader τ).val :=
        lt_of_lt_of_le q.isLt hk_le_rank
      have hthread_exists (q : Fin k) :
          ∃! i, execution.activeAt i τ ∧
            execution.rankAt i τ =
              (⟨q.val, lt_trans (hq_rank q)
                (execution.rankAt leader τ).isLt⟩ :
                  Fin (t.val + 1)) :=
        execution.active_rank_exhaustive τ hτ0 hτstop
          _ (lt_trans (hq_rank q) hleader_count)
      let fasterThread (q : Fin k) : Fin (t.val + 1) :=
        Classical.choose (hthread_exists q).exists
      have hfasterThread (q : Fin k) :
          execution.activeAt (fasterThread q) τ ∧
            execution.rankAt (fasterThread q) τ =
              (⟨q.val, lt_trans (hq_rank q)
                (execution.rankAt leader τ).isLt⟩ :
                  Fin (t.val + 1)) :=
        Classical.choose_spec (hthread_exists q).exists
      have hfasterRank (q : Fin k) :
          execution.rankAt (fasterThread q) τ <
            execution.rankAt leader τ := by
        rw [(hfasterThread q).2]
        exact Fin.mk_lt_mk.mpr (hq_rank q)
      let fasterSource (q : Fin k) : Fin T :=
        Classical.choose
          (hsourced (fasterThread q) (hfasterThread q).1 (hfasterRank q))
      have hfasterSource (q : Fin k) :
          execution.source (fasterThread q) = some (fasterSource q) :=
        Classical.choose_spec
          (hsourced (fasterThread q) (hfasterThread q).1 (hfasterRank q))
      let ownerMap (q : Fin k) : Fin k :=
        family.owner (fasterSource q)
      have hownerInjective : Function.Injective ownerMap := by
        intro q r hqr
        have hthreads : fasterThread q = fasterThread r :=
          hunique (ownerMap q) (fasterThread q) (fasterThread r)
            (fasterSource q) (fasterSource r)
            (hfasterThread q).1 (hfasterRank q) (hfasterSource q)
            (by rfl) (hfasterThread r).1 (hfasterRank r)
            (hfasterSource r) (by
              change ownerMap r = ownerMap q
              exact hqr.symm)
        apply Fin.ext
        have hranks := congrArg
          (fun i => (execution.rankAt i τ).val) hthreads
        simpa [hfasterThread] using hranks
      obtain ⟨q, hq⟩ :=
        (Finite.surjective_of_injective hownerInjective) (family.owner t)
      exact
        (hnotowner (fasterThread q) (fasterSource q)
          (hfasterThread q).1 (hfasterRank q) (hfasterSource q))
          (by
            change ownerMap q = family.owner t
            exact hq)
    let A :=
      (k : ℝ) ^ 3 * (Real.log (k : ℝ)) ^ 2 *
        collapse_interval_charge input.origin
          (fun s => oracle.solution (input.instanceAt s)) family t
    let B := (k : ℝ) ^ 2 * (Real.log (k : ℝ)) ^ 2
    let D :=
      predict_yesterday_step_cost input.origin
        (fun s => oracle.solution (input.instanceAt s)) family t
    change τ ≤ A at hτbudget
    have hk_real : (1 : ℝ) < (k : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hk)
    have hlog : 0 < Real.log (k : ℝ) := Real.log_pos hk_real
    have hBpos : 0 < B := by
      dsimp [B]
      positivity
    have hDnonneg : 0 ≤ D := by
      dsimp [D, predict_yesterday_step_cost]
      exact dist_nonneg
    rw [← execution.stopVirtualTime_eq_dayVirtualRadius]
    change execution.stopVirtualTime ≤ A + B * D
    by_contra hbound
    have hstrict : A + B * D < execution.stopVirtualTime :=
      lt_of_not_ge hbound
    let υ := τ + B * D
    have hτleυ : τ ≤ υ := by
      dsimp [υ]
      nlinarith [mul_nonneg hBpos.le hDnonneg]
    have hυ0 : 0 ≤ υ := hτ0.trans hτleυ
    have hυstrict : υ < execution.stopVirtualTime := by
      dsimp [υ]
      linarith
    have hυstop : υ ≤ execution.stopVirtualTime := hυstrict.le
    obtain ⟨j, _, hjactive, _, hprogress⟩ :=
      execution.bounded_rank_lineage_progress hk leader
        (trajectory_previous_solution input.origin
          (fun s => oracle.solution (input.instanceAt s)) family t)
        τ υ hτ0 hτleυ hυstop hactive hrank
    have hquotient : (υ - τ) / B = D := by
      dsimp [υ]
      field_simp [ne_of_gt hBpos]
      ring
    rw [hquotient] at hprogress
    have hpotential :
        D ≤ execution.searchedRadiusAt j υ -
          dist (execution.thread j).center
            (trajectory_previous_solution input.origin
              (fun s => oracle.solution (input.instanceAt s)) family t) := by
      linarith
    have hdistance :
        dist (execution.thread j).center
            (oracle.solution (input.instanceAt t)) ≤
          execution.searchedRadiusAt j υ := by
      have htriangle :=
        dist_triangle (execution.thread j).center
          (trajectory_previous_solution input.origin
            (fun s => oracle.solution (input.instanceAt s)) family t)
          (oracle.solution (input.instanceAt t))
      dsimp [D, predict_yesterday_step_cost] at hpotential
      linarith
    have hruntime :
        oracle.runtime (input.instanceAt t) (execution.thread j).center ≤
          execution.searchedRadiusAt j υ := by
      calc
        oracle.runtime (input.instanceAt t) (execution.thread j).center ≤
            dist (oracle.solution (input.instanceAt t))
              (execution.thread j).center :=
          oracle.runtime_le_dist _ _
        _ = dist (execution.thread j).center
              (oracle.solution (input.instanceAt t)) := dist_comm _ _
        _ ≤ execution.searchedRadiusAt j υ := hdistance
    have hincomplete :=
      execution.no_active_call_completes_before_stop
        j υ hυ0 hυstrict hjactive
    linarith

@[blueprint "lem:one-trajectory-virtual-radius-bound"
  (statement := /-- Let the instance and solution types be arbitrary, equip the solution type with a metric, and assume a certified quadratic-decay event scheduler.  Fix a horizon $T\in\mathbb N$, a trajectory count $k\in\mathbb N$ with $k\geq2$, a warm-start oracle, an online ball-search input of horizon $T$, a certified family of $k$ trajectories, and an owner $q\in\operatorname{Fin}(k)$.  Write $S_t$ for the oracle-designated solution on day $t$ and $S_{\operatorname{prev}(t)}$ for the solution on the preceding day with the same owner, using the input origin when no such day exists.  Then the virtual radius of the distinguished quadratic-decay run on the days owned by $q$ satisfies
  \[
    \sum_{\substack{t\in\operatorname{Fin}(T)\\\operatorname{owner}(t)=q}} R_t
    \leq 2k^3(\log k)^2
      \sum_{t\in\operatorname{Fin}(T)} d(S_{\operatorname{prev}(t)},S_t),
  \]
  where $R_t$ is the day-$t$ virtual radius. -/)
  (proof := /-- Apply \cref{lem:quadratic-decay-day-virtual-radius-bound} on every day owned by $q$ and sum.  The first family of terms is bounded by the total predict-yesterday cost through \cref{lem:collapse-interval-charging-bound}.  The second family is a sub-sum of the same nonnegative total.  Since $k\geq2$, its coefficient $k^2(\log k)^2$ is at most $k^3(\log k)^2$.  Adding the two estimates gives the claimed factor two. -/)
  (title := /-- Virtual-radius bound on one benchmark trajectory -/)
  (latexEnv := "lemma")]
lemma one_trajectory_virtual_radius_bound
    {Instance Solution : Type*} [MetricSpace Solution]
    [quadratic_decay_event_scheduler Instance Solution] {T k : ℕ}
    (oracle : warm_start_oracle Instance Solution)
    (input : online_ball_search_input Instance Solution T)
    (family : trajectory_family Solution T k) (hk : 2 ≤ k) (q : Fin k) :
    (∑ t, if family.owner t = q then
      ((quadratic_decay_algorithm Instance Solution).run oracle input).dayVirtualRadius t
        else 0) ≤
      2 * (k : ℝ) ^ 3 * (Real.log (k : ℝ)) ^ 2 *
        predict_yesterday_cost input.origin
          (fun s => oracle.solution (input.instanceAt s)) family := by
  classical
  have hsum :
      (∑ t, if family.owner t = q then
        ((quadratic_decay_algorithm Instance Solution).run oracle input).dayVirtualRadius t
          else 0) ≤
        ∑ t, if family.owner t = q then
          (k : ℝ) ^ 3 * (Real.log (k : ℝ)) ^ 2 *
              collapse_interval_charge input.origin
                (fun s => oracle.solution (input.instanceAt s)) family t +
            (k : ℝ) ^ 2 * (Real.log (k : ℝ)) ^ 2 *
              predict_yesterday_step_cost input.origin
                (fun s => oracle.solution (input.instanceAt s)) family t
          else 0 := by
    apply Finset.sum_le_sum
    intro t ht
    by_cases howner : family.owner t = q
    · simp only [howner, if_true]
      exact quadratic_decay_day_virtual_radius_bound oracle input family hk t
    · simp [howner]
  have hsplit :
      (∑ t, if family.owner t = q then
        (k : ℝ) ^ 3 * (Real.log (k : ℝ)) ^ 2 *
              collapse_interval_charge input.origin
                (fun s => oracle.solution (input.instanceAt s)) family t +
            (k : ℝ) ^ 2 * (Real.log (k : ℝ)) ^ 2 *
              predict_yesterday_step_cost input.origin
                (fun s => oracle.solution (input.instanceAt s)) family t
          else 0) =
        ((k : ℝ) ^ 3 * (Real.log (k : ℝ)) ^ 2) *
            (∑ t, if family.owner t = q then
              collapse_interval_charge input.origin
                (fun s => oracle.solution (input.instanceAt s)) family t else 0) +
          ((k : ℝ) ^ 2 * (Real.log (k : ℝ)) ^ 2) *
            (∑ t, if family.owner t = q then
              predict_yesterday_step_cost input.origin
                (fun s => oracle.solution (input.instanceAt s)) family t else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    by_cases howner : family.owner t = q <;> simp [howner]
  have hcollapse := collapse_interval_charging_bound input.origin
    (fun s => oracle.solution (input.instanceAt s)) family q
  have hstep :
      (∑ t, if family.owner t = q then
        predict_yesterday_step_cost input.origin
          (fun s => oracle.solution (input.instanceAt s)) family t else 0) ≤
        predict_yesterday_cost input.origin
          (fun s => oracle.solution (input.instanceAt s)) family := by
    unfold predict_yesterday_cost
    apply Finset.sum_le_sum
    intro t ht
    by_cases howner : family.owner t = q
    · simp [howner]
    · simp only [howner, if_false]
      unfold predict_yesterday_step_cost
      exact dist_nonneg
  have hcost :
      0 ≤ predict_yesterday_cost input.origin
        (fun s => oracle.solution (input.instanceAt s)) family := by
    unfold predict_yesterday_cost
    apply Finset.sum_nonneg
    intro t ht
    unfold predict_yesterday_step_cost
    exact dist_nonneg
  have hA : 0 ≤ (k : ℝ) ^ 3 * (Real.log (k : ℝ)) ^ 2 := by
    positivity
  have hB : 0 ≤ (k : ℝ) ^ 2 * (Real.log (k : ℝ)) ^ 2 := by
    positivity
  have hweighted :
      ((k : ℝ) ^ 3 * (Real.log (k : ℝ)) ^ 2) *
            (∑ t, if family.owner t = q then
              collapse_interval_charge input.origin
                (fun s => oracle.solution (input.instanceAt s)) family t else 0) +
          ((k : ℝ) ^ 2 * (Real.log (k : ℝ)) ^ 2) *
            (∑ t, if family.owner t = q then
              predict_yesterday_step_cost input.origin
                (fun s => oracle.solution (input.instanceAt s)) family t else 0) ≤
        ((k : ℝ) ^ 3 * (Real.log (k : ℝ)) ^ 2) *
            predict_yesterday_cost input.origin
              (fun s => oracle.solution (input.instanceAt s)) family +
          ((k : ℝ) ^ 2 * (Real.log (k : ℝ)) ^ 2) *
            predict_yesterday_cost input.origin
              (fun s => oracle.solution (input.instanceAt s)) family :=
    add_le_add (mul_le_mul_of_nonneg_left hcollapse hA)
      (mul_le_mul_of_nonneg_left hstep hB)
  have hkone : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast (le_trans (by decide : 1 ≤ 2) hk)
  have hkpow : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := by
    calc
      (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 * (k : ℝ) := by
        simpa using mul_le_mul_of_nonneg_left hkone (sq_nonneg (k : ℝ))
      _ = (k : ℝ) ^ 3 := by ring
  have hBA :
      (k : ℝ) ^ 2 * (Real.log (k : ℝ)) ^ 2 ≤
        (k : ℝ) ^ 3 * (Real.log (k : ℝ)) ^ 2 :=
    mul_le_mul_of_nonneg_right hkpow (sq_nonneg (Real.log (k : ℝ)))
  have hfinal :
      ((k : ℝ) ^ 3 * (Real.log (k : ℝ)) ^ 2) *
            predict_yesterday_cost input.origin
              (fun s => oracle.solution (input.instanceAt s)) family +
          ((k : ℝ) ^ 2 * (Real.log (k : ℝ)) ^ 2) *
            predict_yesterday_cost input.origin
              (fun s => oracle.solution (input.instanceAt s)) family ≤
        2 * (k : ℝ) ^ 3 * (Real.log (k : ℝ)) ^ 2 *
          predict_yesterday_cost input.origin
            (fun s => oracle.solution (input.instanceAt s)) family := by
    have := mul_le_mul_of_nonneg_right hBA hcost
    nlinarith
  exact hsum.trans (hsplit ▸ hweighted.trans hfinal)

@[blueprint "lem:all-trajectories-virtual-radius-bound"
  (statement := /-- Let the instance and solution types be arbitrary, equip the solution type with a metric, and assume a certified quadratic-decay event scheduler.  Fix a horizon $T\in\mathbb N$, a trajectory count $k\in\mathbb N$ with $k\geq2$, a warm-start oracle, an online ball-search input of horizon $T$, and a certified family of $k$ trajectories.  Write $S_t$ for the oracle-designated solution on day $t$ and $S_{\operatorname{prev}(t)}$ for the solution on the preceding day with the same owner, using the input origin when no such day exists.  Then the total virtual radius of the distinguished quadratic-decay run is at most
  \[
    2k^4(\log k)^2\sum_t d(S_{\operatorname{prev}(t)},S_t)
  \]. -/)
  (proof := /-- Expand the total virtual radius and the quartic logarithmic scale using \cref{def:total-virtual-radius, def:quadratic-log-scale}.  Interchange the two finite sums over days and owners.  For each day, exactly the summand indexed by its owner from \cref{def:trajectory-family} remains, so the resulting double sum equals the total virtual radius.  Apply \cref{lem:one-trajectory-virtual-radius-bound} to every owner and sum the inequalities.  Since $\operatorname{Fin}(k)$ has cardinality $k$, the right-hand side is $k$ copies of the one-owner bound; normalizing the product changes $k^3$ to $k^4$ and yields the claimed estimate. -/)
  (title := /-- Total virtual radius against all trajectories -/)
  (latexEnv := "lemma")]
lemma all_trajectories_virtual_radius_bound
    {Instance Solution : Type*} [MetricSpace Solution]
    [quadratic_decay_event_scheduler Instance Solution] {T k : ℕ}
    (oracle : warm_start_oracle Instance Solution)
    (input : online_ball_search_input Instance Solution T)
    (family : trajectory_family Solution T k) (hk : 2 ≤ k) :
    total_virtual_radius
        ((quadratic_decay_algorithm Instance Solution).run oracle input) ≤
      2 * quadratic_log_scale k *
        predict_yesterday_cost input.origin
          (fun s => oracle.solution (input.instanceAt s)) family := by
  classical
  rw [total_virtual_radius, quadratic_log_scale]
  calc
    (∑ t,
        ((quadratic_decay_algorithm Instance Solution).run oracle input).dayVirtualRadius t) =
        ∑ q : Fin k, ∑ t, if family.owner t = q then
          ((quadratic_decay_algorithm Instance Solution).run oracle input).dayVirtualRadius t
          else 0 := by
      rw [Finset.sum_comm]
      simp
    _ ≤ ∑ q : Fin k,
        2 * (k : ℝ) ^ 3 * (Real.log (k : ℝ)) ^ 2 *
          predict_yesterday_cost input.origin
            (fun s => oracle.solution (input.instanceAt s)) family :=
      Finset.sum_le_sum fun q _ =>
        one_trajectory_virtual_radius_bound oracle input family hk q
    _ = 2 * ((k : ℝ) ^ 4 * (Real.log (k : ℝ)) ^ 2) *
        predict_yesterday_cost input.origin
          (fun s => oracle.solution (input.instanceAt s)) family := by
      simp
      ring

@[blueprint "lem:quadratic-decay-rate-le-telescoping-majorant"
  (statement := /-- For every rank $r$, the quadratic-decay rate at rank $r$ is at most
  \[
    2\left(1+\frac{1}{(\log 2)^2}\right)
      \left(\frac{1}{r+1}-\frac{1}{r+2}\right).
  \] -/)
  (proof := /-- At rank zero the inequality follows directly from \cref{def:quadratic-decay-rate} and positivity of $\log 2$.  For $r\geq1$, monotonicity of the logarithm gives $\log(r+1)\geq\log 2>0$, so the rate is at most $((\log 2)^2(r+1)^2)^{-1}$.  The inequality $(r+2)\leq2(r+1)$ bounds $(r+1)^{-2}$ by twice the displayed telescoping difference.  Enlarging the nonnegative coefficient $(\log 2)^{-2}$ to $1+(\log 2)^{-2}$ proves the claim. -/)
  (title := /-- A telescoping majorant for the quadratic-decay rate -/)
  (latexEnv := "lemma")]
lemma quadratic_decay_rate_le_telescoping_majorant (rank : ℕ) :
    quadratic_decay_rate rank ≤
      (2 * (1 + 1 / (Real.log 2) ^ 2)) *
        (1 / (((rank + 1 : ℕ) : ℝ)) -
          1 / (((rank + 2 : ℕ) : ℝ))) := by
  by_cases h : rank = 0
  · subst rank
    have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    norm_num [quadratic_decay_rate]
    have hinv : 0 ≤ (Real.log 2 ^ 2)⁻¹ := by
      positivity
    nlinarith
  · have hr : 1 ≤ rank := Nat.one_le_iff_ne_zero.mpr h
    have hcast : (2 : ℝ) ≤ ((rank + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ hr
    have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog : Real.log 2 ≤ Real.log (((rank + 1 : ℕ) : ℝ)) :=
      Real.log_le_log (by norm_num) hcast
    have ha : 0 < (((rank + 1 : ℕ) : ℝ)) := by
      positivity
    have halog : 0 < Real.log (((rank + 1 : ℕ) : ℝ)) := by
      exact hlogtwo.trans_le hlog
    have hsq :
        (Real.log 2) ^ 2 ≤
          (Real.log (((rank + 1 : ℕ) : ℝ))) ^ 2 := by
      nlinarith
    have hgeom :
        1 / (((rank + 1 : ℕ) : ℝ)) ^ 2 ≤
          2 * (1 / (((rank + 1 : ℕ) : ℝ)) -
            1 / (((rank + 2 : ℕ) : ℝ))) := by
      field_simp
      norm_num at *
      nlinarith
    have hcoefficient : 0 ≤ 1 / (Real.log 2) ^ 2 := by
      positivity
    rw [quadratic_decay_rate, if_neg h]
    calc
      1 / ((((rank + 1 : ℕ) : ℝ)) ^ 2 *
          (Real.log (((rank + 1 : ℕ) : ℝ))) ^ 2) ≤
          1 / ((((rank + 1 : ℕ) : ℝ)) ^ 2 *
            (Real.log 2) ^ 2) := by
        apply (one_div_le_one_div
          (mul_pos (sq_pos_of_pos ha) (sq_pos_of_pos halog))
          (mul_pos (sq_pos_of_pos ha) (sq_pos_of_pos hlogtwo))).2
        exact mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = (1 / (Real.log 2) ^ 2) *
          (1 / (((rank + 1 : ℕ) : ℝ)) ^ 2) := by
        ring
      _ ≤ (1 / (Real.log 2) ^ 2) *
          (2 * (1 / (((rank + 1 : ℕ) : ℝ)) -
            1 / (((rank + 2 : ℕ) : ℝ)))) := by
        exact mul_le_mul_of_nonneg_left hgeom hcoefficient
      _ ≤ (1 + 1 / (Real.log 2) ^ 2) *
          (2 * (1 / (((rank + 1 : ℕ) : ℝ)) -
            1 / (((rank + 2 : ℕ) : ℝ)))) := by
        have hdiff : 0 ≤
            1 / (((rank + 1 : ℕ) : ℝ)) -
              1 / (((rank + 2 : ℕ) : ℝ)) := by
          have hab :
              (((rank + 1 : ℕ) : ℝ)) ≤
                (((rank + 2 : ℕ) : ℝ)) := by
            norm_num
          have hrecip :
              1 / (((rank + 2 : ℕ) : ℝ)) ≤
                1 / (((rank + 1 : ℕ) : ℝ)) := by
            apply (one_div_le_one_div (by positivity) (by positivity)).2
            exact hab
          linarith
        apply mul_le_mul_of_nonneg_right
        · linarith
        · exact mul_nonneg (by norm_num) hdiff
      _ = (2 * (1 + 1 / (Real.log 2) ^ 2)) *
          (1 / (((rank + 1 : ℕ) : ℝ)) -
            1 / (((rank + 2 : ℕ) : ℝ))) := by
        ring

@[blueprint "lem:finite-quadratic-decay-rate-sum-bound"
  (statement := /-- For every $n\in\mathbb{N}$, the sum of the quadratic-decay rates over the first $n$ ranks is at most
  \[
    2\left(1+\frac{1}{(\log 2)^2}\right).
  \] -/)
  (proof := /-- Apply the pointwise estimate of \cref{lem:quadratic-decay-rate-le-telescoping-majorant} and sum over the ranks.  The resulting differences telescope to $1-(n+1)^{-1}\leq1$.  Multiplication by the nonnegative coefficient $2(1+(\log 2)^{-2})$ preserves this inequality. -/)
  (title := /-- Uniform bound for finite quadratic-decay rate sums -/)
  (latexEnv := "lemma")]
lemma finite_quadratic_decay_rate_sum_bound (n : ℕ) :
    (∑ r : Fin n, quadratic_decay_rate r.val) ≤
      2 * (1 + 1 / (Real.log 2) ^ 2) := by
  let A : ℝ := 2 * (1 + 1 / (Real.log 2) ^ 2)
  have htel :
      (∑ r : Fin n,
        (1 / (((r.val + 1 : ℕ) : ℝ)) -
          1 / (((r.val + 2 : ℕ) : ℝ)))) =
        1 - 1 / (((n + 1 : ℕ) : ℝ)) := by
    let f : ℕ → ℝ := fun j =>
      1 / (((j + 1 : ℕ) : ℝ))
    calc
      (∑ r : Fin n,
          (1 / (((r.val + 1 : ℕ) : ℝ)) -
            1 / (((r.val + 2 : ℕ) : ℝ)))) =
          ∑ j ∈ Finset.range n, (f j - f (j + 1)) := by
        exact Fin.sum_univ_eq_sum_range
          (fun j => f j - f (j + 1)) n
      _ = f 0 - f n := by
        exact Finset.sum_range_sub' f n
      _ = 1 - 1 / (((n + 1 : ℕ) : ℝ)) := by
        simp [f]
  calc
    (∑ r : Fin n, quadratic_decay_rate r.val) ≤
        ∑ r : Fin n,
          A * (1 / (((r.val + 1 : ℕ) : ℝ)) -
            1 / (((r.val + 2 : ℕ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro r _
      exact quadratic_decay_rate_le_telescoping_majorant r.val
    _ = A * (∑ r : Fin n,
          (1 / (((r.val + 1 : ℕ) : ℝ)) -
            1 / (((r.val + 2 : ℕ) : ℝ)))) := by
      rw [Finset.mul_sum]
    _ = A * (1 - 1 / (((n + 1 : ℕ) : ℝ))) := by
      rw [htel]
    _ ≤ A := by
      have hA : 0 ≤ A := by
        dsimp [A]
        positivity
      have hrec : 0 ≤ 1 / (((n + 1 : ℕ) : ℝ)) := by
        positivity
      nlinarith [mul_nonneg hA hrec]
    _ = 2 * (1 + 1 / (Real.log 2) ^ 2) := by
      rfl

@[blueprint "lem:quadratic-decay-day-searched-radius-bound"
  (statement := /-- Fix instance and solution types, a metric on the solution type, and a certified quadratic-decay event scheduler.  On every day of every finite run, the searched radius of the distinguished quadratic-decay algorithm is at most
  \[
    2\left(1+\frac{1}{(\log 2)^2}\right)
  \]
  times that day's virtual radius. -/)
  (proof := /-- Obtain the day's certified execution from \cref{lem:quadratic-decay-algorithm-satisfies-specification}.  The searched-radius identities in \cref{def:quadratic-decay-thread-execution, def:quadratic-decay-day-execution} rewrite the daily searched radius as the sum over ranks of the rate at that rank times its total assigned virtual time.  Each such total is at most the daily virtual radius, and every rate is nonnegative.  The finite rate-sum estimate \cref{lem:finite-quadratic-decay-rate-sum-bound} then gives the stated bound; nonnegativity of the daily virtual radius is part of \cref{def:quadratic-decay-run}. -/)
  (title := /-- Daily searched radius is controlled by virtual radius -/)
  (latexEnv := "lemma")]
lemma quadratic_decay_day_searched_radius_bound
    {Instance Solution : Type*} [MetricSpace Solution]
    [quadratic_decay_event_scheduler Instance Solution] {T : ℕ}
    (oracle : warm_start_oracle Instance Solution)
    (input : online_ball_search_input Instance Solution T) (t : Fin T) :
    ((quadratic_decay_algorithm Instance Solution).run oracle input).daySearchedRadius t ≤
      (2 * (1 + 1 / (Real.log 2) ^ 2)) *
        ((quadratic_decay_algorithm Instance Solution).run oracle input).dayVirtualRadius t := by
  let run :=
    (quadratic_decay_algorithm Instance Solution).run oracle input
  obtain ⟨execution⟩ :=
    quadratic_decay_algorithm_satisfies_specification
      Instance Solution oracle input t
  have hrate : ∀ rank : ℕ, 0 ≤ quadratic_decay_rate rank := by
    intro rank
    rw [quadratic_decay_rate]
    split_ifs
    · norm_num
    · positivity
  rw [execution.searched_radius_accounting]
  calc
    (∑ i, (execution.thread i).searchedRadius) =
        ∑ i, ∑ r,
          quadratic_decay_rate r.val *
            (execution.thread i).rankedVirtualTime r := by
      apply Finset.sum_congr rfl
      intro i _
      exact (execution.thread i).searchedRadius_eq_schedule
    _ = ∑ r, ∑ i,
          quadratic_decay_rate r.val *
            (execution.thread i).rankedVirtualTime r := by
      rw [Finset.sum_comm]
    _ = ∑ r, quadratic_decay_rate r.val *
          (∑ i, (execution.thread i).rankedVirtualTime r) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
    _ ≤ ∑ r : Fin (t.val + 1), quadratic_decay_rate r.val *
          run.dayVirtualRadius t := by
      apply Finset.sum_le_sum
      intro r _
      exact mul_le_mul_of_nonneg_left
        (execution.rank_time_le_virtual_radius r) (hrate r.val)
    _ = (∑ r : Fin (t.val + 1), quadratic_decay_rate r.val) *
          run.dayVirtualRadius t := by
      rw [Finset.sum_mul]
    _ ≤ (2 * (1 + 1 / (Real.log 2) ^ 2)) *
          run.dayVirtualRadius t := by
      exact mul_le_mul_of_nonneg_right
        (finite_quadratic_decay_rate_sum_bound (t.val + 1))
        (run.dayVirtualRadius_nonnegative t)

@[blueprint "lem:quadratic-virtual-radius-bounds-total-radius"
  (statement := /-- There is a positive real constant $C_{\mathrm{rad}}$, chosen independently of the instance type, the solution type, the metric-space structure, and the certified event scheduler, such that, for every such choice, every finite horizon, every warm-start oracle, and every online input, the total radius searched by the quadratic-decay procedure is at most $C_{\mathrm{rad}}$ times its total virtual radius. -/)
  (proof := /-- Choose
  \[
    C=2\left(1+\frac{1}{(\log 2)^2}\right).
  \]
  Since $\log 2>0$, this constant is positive and is fixed before all quantified types, structures, and runtime data.  For arbitrary instance and solution types, metric-space structure, certified scheduler, horizon, warm-start oracle, and input, apply \cref{lem:quadratic-decay-day-searched-radius-bound} on every day and sum the resulting inequalities.  Distributivity of multiplication over the finite sum, together with \cref{def:total-virtual-radius, def:total-searched-radius}, gives the claimed total-radius inequality with this uniform constant. -/)
  (title := /-- Total searched radius is controlled by virtual radius -/)
  (latexEnv := "lemma")]
lemma quadratic_virtual_radius_bounds_total_radius :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Instance Solution : Type*) [MetricSpace Solution]
      [quadratic_decay_event_scheduler Instance Solution] (T : ℕ)
      (oracle : warm_start_oracle Instance Solution)
      (input : online_ball_search_input Instance Solution T),
      total_searched_radius
          ((quadratic_decay_algorithm Instance Solution).run oracle input) ≤
        C * total_virtual_radius
          ((quadratic_decay_algorithm Instance Solution).run oracle input) := by
  let C : ℝ := 2 * (1 + 1 / (Real.log 2) ^ 2)
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro Instance Solution metric scheduler T oracle input
    rw [total_searched_radius, total_virtual_radius]
    calc
      (∑ t,
          ((quadratic_decay_algorithm Instance Solution).run oracle input).daySearchedRadius t) ≤
          ∑ t, C *
            ((quadratic_decay_algorithm Instance Solution).run oracle input).dayVirtualRadius t := by
        apply Finset.sum_le_sum
        intro t _
        exact quadratic_decay_day_searched_radius_bound oracle input t
      _ = C * (∑ t,
          ((quadratic_decay_algorithm Instance Solution).run oracle input).dayVirtualRadius t) := by
        rw [Finset.mul_sum]

@[blueprint "lem:quadratic-runtime-weights-bounded"
  (statement := /-- For every finite number of ranks, the sum of the runtime weights
  \[
    \sum_{r<N}(r+1)\rho_r
  \]
  of the quadratic-decay schedule is at most $1+4/\log 2$, where $\rho_r$ is the rate at rank $r$. -/)
  (proof := /-- For $n\geq2$, the elementary logarithmic inequality
  $1-1/x\leq\log x$, applied to $x=(n+1)/n$, gives
  $1/(n+1)\leq\log(n+1)-\log n$.  Moreover,
  $n+1\leq2n$ and $\log(n+1)\leq2\log n$.  Clearing the positive
  denominators yields
  \[
    \frac{1}{n\log^2 n}\leq
      4\left(\frac1{\log n}-\frac1{\log(n+1)}\right).
  \]
  By \cref{def:quadratic-decay-rate}, the rank-zero weight is $1$, while
  the weight at rank $r\geq1$ is the left-hand side with $n=r+1$.
  Summing the displayed inequalities telescopes; the remaining terminal
  reciprocal logarithm is nonnegative, giving the asserted bound. -/)
  (title := /-- Uniform bound for the quadratic runtime weights -/)
  (latexEnv := "lemma")]
lemma quadratic_runtime_weights_bounded (N : ℕ) :
    (∑ r ∈ Finset.range N,
      (((r + 1 : ℕ) : ℝ) * quadratic_decay_rate r)) ≤
      1 + 4 * (Real.log 2)⁻¹ := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hpointwise (n : ℕ) (hn : 2 ≤ n) :
      ((n : ℝ)⁻¹ / (Real.log (n : ℝ)) ^ 2) ≤
        4 * ((Real.log (n : ℝ))⁻¹ -
          (Real.log ((n + 1 : ℕ) : ℝ))⁻¹) := by
    have hn_real : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn_pos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hn_real
    have hn_one_pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hlogn : 0 < Real.log (n : ℝ) :=
      Real.log_pos (lt_of_lt_of_le (by norm_num) hn_real)
    have hlogn_one : 0 < Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n + 1 by omega))
    have hratio_pos :
        0 < (((n + 1 : ℕ) : ℝ) / (n : ℝ)) :=
      div_pos hn_one_pos hn_pos
    have hincrement :
        1 / ((n + 1 : ℕ) : ℝ) ≤
          Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
      have h := Real.one_sub_inv_le_log_of_pos hratio_pos
      rw [Real.log_div (ne_of_gt hn_one_pos) (ne_of_gt hn_pos)] at h
      convert h using 1 <;> norm_num [Nat.cast_add] <;> field_simp <;> ring
    have hn_one_le_twice : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
      exact_mod_cast (show n + 1 ≤ 2 * n by omega)
    have hn_one_le_square : ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) * (n : ℝ) := by
      exact_mod_cast (show n + 1 ≤ n * n by nlinarith)
    have hlog_le :
        Real.log ((n + 1 : ℕ) : ℝ) ≤ 2 * Real.log (n : ℝ) := by
      have h :=
        (Real.log_le_log_iff hn_one_pos (mul_pos hn_pos hn_pos)).2
          hn_one_le_square
      rw [Real.log_mul (ne_of_gt hn_pos) (ne_of_gt hn_pos)] at h
      linarith
    have hdiff_nonnegative :
        0 ≤ Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) :=
      le_trans (by positivity) hincrement
    have hunit :
        1 ≤ ((n + 1 : ℕ) : ℝ) *
          (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) := by
      simpa [mul_comm] using (div_le_iff₀ hn_one_pos).mp hincrement
    have htwice :
        1 ≤ 2 * (n : ℝ) *
          (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) :=
      le_trans hunit
        (mul_le_mul_of_nonneg_right hn_one_le_twice hdiff_nonnegative)
    have hscaled :
        2 * Real.log (n : ℝ) ≤
          4 * (n : ℝ) * Real.log (n : ℝ) *
            (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) := by
      calc
        _ = (2 * Real.log (n : ℝ)) * 1 := by ring
        _ ≤ (2 * Real.log (n : ℝ)) *
              (2 * (n : ℝ) *
                (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))) :=
          mul_le_mul_of_nonneg_left htwice (by positivity)
        _ = _ := by ring
    have hcross :
        Real.log (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) ≤
          (4 * (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))) *
            ((n : ℝ) * (Real.log (n : ℝ)) ^ 2) := by
      calc
        _ ≤ Real.log (n : ℝ) * (2 * Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog_le (le_of_lt hlogn)
        _ ≤ Real.log (n : ℝ) *
              (4 * (n : ℝ) * Real.log (n : ℝ) *
                (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hscaled (le_of_lt hlogn)
        _ = _ := by ring
    have hleft :
        (n : ℝ)⁻¹ / (Real.log (n : ℝ)) ^ 2 =
          1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2) := by
      field_simp
    have hright :
        (Real.log (n : ℝ))⁻¹ -
            (Real.log ((n + 1 : ℕ) : ℝ))⁻¹ =
          (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) /
            (Real.log (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)) := by
      field_simp
      <;> ring
    rw [hleft, hright]
    rw [show 4 *
        ((Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) /
          (Real.log (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ))) =
        (4 * (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))) /
          (Real.log (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)) by ring]
    apply (div_le_div_iff₀
      (mul_pos hn_pos (sq_pos_of_pos hlogn))
      (mul_pos hlogn hlogn_one)).2
    simpa using hcross
  have hweight (r : ℕ) (hr : 1 ≤ r) :
      (((r + 1 : ℕ) : ℝ) * quadratic_decay_rate r) ≤
        4 * ((Real.log ((r + 1 : ℕ) : ℝ))⁻¹ -
          (Real.log ((r + 2 : ℕ) : ℝ))⁻¹) := by
    rw [quadratic_decay_rate, if_neg (by omega)]
    have hlog : Real.log ((r + 1 : ℕ) : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < r + 1 by omega)))
    convert hpointwise (r + 1) (by omega) using 1 <;>
      field_simp <;> ring
  have hpartial :
      ∀ M : ℕ, 1 ≤ M →
        (∑ r ∈ Finset.range M,
          (((r + 1 : ℕ) : ℝ) * quadratic_decay_rate r)) ≤
          1 + 4 * ((Real.log 2)⁻¹ -
            (Real.log ((M + 1 : ℕ) : ℝ))⁻¹) := by
    intro M
    induction M with
    | zero =>
        intro hM
        omega
    | succ M ih =>
        intro hM
        by_cases hM0 : M = 0
        · subst M
          simp [quadratic_decay_rate]
        · have hMpos : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM0
          rw [Finset.sum_range_succ]
          calc
            _ ≤
                (1 + 4 * ((Real.log 2)⁻¹ -
                  (Real.log ((M + 1 : ℕ) : ℝ))⁻¹)) +
                (((M + 1 : ℕ) : ℝ) * quadratic_decay_rate M) :=
              add_le_add (ih hMpos) (le_refl _)
            _ ≤
                (1 + 4 * ((Real.log 2)⁻¹ -
                  (Real.log ((M + 1 : ℕ) : ℝ))⁻¹)) +
                4 * ((Real.log ((M + 1 : ℕ) : ℝ))⁻¹ -
                  (Real.log ((M + 2 : ℕ) : ℝ))⁻¹) :=
              add_le_add (le_refl _) (hweight M hMpos)
            _ = 1 + 4 * ((Real.log 2)⁻¹ -
                  (Real.log (((M + 1) + 1 : ℕ) : ℝ))⁻¹) := by
              ring
  cases N with
  | zero =>
      simp
      positivity
  | succ N =>
      have h := hpartial (N + 1) (by omega)
      have hterminal :
          0 ≤ (Real.log (((N + 1) + 1 : ℕ) : ℝ))⁻¹ := by
        positivity
      nlinarith

@[blueprint "lem:quadratic-day-runtime-bounds-searched-radius"
  (statement := /-- Fix instance and solution types, a metric on the solution type,
  and a certified quadratic-decay scheduler.  For every horizon, warm-start
  oracle, online input, and day, the daily runtime is at most
  $\left(2+4/\log 2\right)$ times the daily searched radius. -/)
  (proof := /-- Obtain the certified daily execution from
  \cref{lem:quadratic-decay-algorithm-satisfies-specification}.  The runtime
  accounting in \cref{def:quadratic-decay-day-execution} and the warm-start
  identity in \cref{def:quadratic-decay-thread-execution} split the daily
  runtime into the daily searched radius and the total overhead.  For each
  rank, its nonnegative runtime weight multiplies at most the daily virtual
  radius.  Interchanging the two finite sums and applying
  \cref{lem:quadratic-runtime-weights-bounded} therefore bounds the overhead
  by $\left(1+4/\log 2\right)$ times the daily virtual radius.

  The rank-zero rate in \cref{def:quadratic-decay-rate} is $1$, all other
  searched-radius summands are nonnegative, and the certified rank-zero
  occupancy equals the daily virtual radius.  Hence the daily virtual radius
  is at most the daily searched radius.  Substitution into the overhead
  estimate and addition of the warm-start work prove the stated factor. -/)
  (title := /-- Daily runtime is controlled by daily searched radius -/)
  (latexEnv := "lemma")]
lemma quadratic_day_runtime_bounds_searched_radius
    {Instance Solution : Type*} [MetricSpace Solution]
    [quadratic_decay_event_scheduler Instance Solution] {T : ℕ}
    (oracle : warm_start_oracle Instance Solution)
    (input : online_ball_search_input Instance Solution T) (t : Fin T) :
    ((quadratic_decay_algorithm Instance Solution).run oracle input).dayRuntime t ≤
      (2 + 4 * (Real.log 2)⁻¹) *
        ((quadratic_decay_algorithm Instance Solution).run oracle input).daySearchedRadius t := by
  rcases quadratic_decay_algorithm_satisfies_specification
      Instance Solution oracle input t with ⟨execution⟩
  let run := (quadratic_decay_algorithm Instance Solution).run oracle input
  have hrate_nonnegative (r : ℕ) : 0 ≤ quadratic_decay_rate r := by
    unfold quadratic_decay_rate
    by_cases hr : r = 0
    · simp [hr]
    · simp [hr]
      positivity
  have hweight_nonnegative (r : ℕ) :
      0 ≤ (((r + 1 : ℕ) : ℝ) * quadratic_decay_rate r) :=
    mul_nonneg (by positivity) (hrate_nonnegative r)
  have hvirtual_le_searched :
      run.dayVirtualRadius t ≤ run.daySearchedRadius t := by
    calc
      run.dayVirtualRadius t =
          ∑ i, (execution.thread i).rankedVirtualTime
            (⟨0, Nat.zero_lt_succ t.val⟩ : Fin (t.val + 1)) :=
        execution.fastest_rank_fills_virtual_radius.symm
      _ ≤ ∑ i, (execution.thread i).searchedRadius := by
        apply Finset.sum_le_sum
        intro i hi
        rw [(execution.thread i).searchedRadius_eq_schedule]
        have hsingle :=
          Finset.single_le_sum
            (fun r _ =>
              mul_nonneg (hrate_nonnegative r.val)
                ((execution.thread i).rankedVirtualTime_nonnegative r))
            (Finset.mem_univ
              (⟨0, Nat.zero_lt_succ t.val⟩ : Fin (t.val + 1)))
        simpa [quadratic_decay_rate] using hsingle
      _ = run.daySearchedRadius t := execution.searched_radius_accounting.symm
  have hfinite_weights :
      (∑ r : Fin (t.val + 1),
        (((r.val + 1 : ℕ) : ℝ) * quadratic_decay_rate r.val)) ≤
        1 + 4 * (Real.log 2)⁻¹ := by
    change (∑ r : Fin (t.val + 1),
      (fun s : ℕ =>
        (((s + 1 : ℕ) : ℝ) * quadratic_decay_rate s)) r) ≤
        1 + 4 * (Real.log 2)⁻¹
    exact (Fin.sum_univ_eq_sum_range
      (fun s : ℕ =>
        (((s + 1 : ℕ) : ℝ) * quadratic_decay_rate s))
      (t.val + 1)).trans_le
        (quadratic_runtime_weights_bounded (t.val + 1))
  have hoverhead :
      (∑ i, (execution.thread i).overheadRuntime) ≤
        (1 + 4 * (Real.log 2)⁻¹) * run.dayVirtualRadius t := by
    calc
      _ ≤ ∑ i, ∑ r,
          ((((r.val + 1 : ℕ) : ℝ) * quadratic_decay_rate r.val) *
            (execution.thread i).rankedVirtualTime r) :=
        Finset.sum_le_sum fun i _ =>
          (execution.thread i).overheadRuntime_le_schedule
      _ = ∑ r : Fin (t.val + 1),
          ((((r.val + 1 : ℕ) : ℝ) * quadratic_decay_rate r.val) *
            ∑ i : Fin (t.val + 1),
              (execution.thread i).rankedVirtualTime r) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.mul_sum]
      _ ≤ ∑ r : Fin (t.val + 1),
          ((((r.val + 1 : ℕ) : ℝ) * quadratic_decay_rate r.val) *
            run.dayVirtualRadius t) := by
        apply Finset.sum_le_sum
        intro r hr
        exact mul_le_mul_of_nonneg_left
          (execution.rank_time_le_virtual_radius r)
          (hweight_nonnegative r.val)
      _ = (∑ r : Fin (t.val + 1),
          (((r.val + 1 : ℕ) : ℝ) * quadratic_decay_rate r.val)) *
            run.dayVirtualRadius t := by
        rw [Finset.sum_mul]
      _ ≤ (1 + 4 * (Real.log 2)⁻¹) * run.dayVirtualRadius t :=
        mul_le_mul_of_nonneg_right hfinite_weights
          (run.dayVirtualRadius_nonnegative t)
  have hfactor_nonnegative : 0 ≤ 1 + 4 * (Real.log 2)⁻¹ := by
    have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity
  change run.dayRuntime t ≤
    (2 + 4 * (Real.log 2)⁻¹) * run.daySearchedRadius t
  calc
    run.dayRuntime t =
        ∑ i, ((execution.thread i).warmStartWork +
          (execution.thread i).overheadRuntime) :=
      execution.runtime_accounting
    _ = (∑ i, (execution.thread i).searchedRadius) +
        ∑ i, (execution.thread i).overheadRuntime := by
      rw [Finset.sum_add_distrib]
      apply congrArg₂ (· + ·) ?_ rfl
      apply Finset.sum_congr rfl
      intro i hi
      exact (execution.thread i).warmStartWork_eq_searchedRadius
    _ = run.daySearchedRadius t +
        ∑ i, (execution.thread i).overheadRuntime := by
      rw [execution.searched_radius_accounting]
    _ ≤ run.daySearchedRadius t +
        (1 + 4 * (Real.log 2)⁻¹) * run.dayVirtualRadius t :=
      add_le_add (le_refl _) hoverhead
    _ ≤ run.daySearchedRadius t +
        (1 + 4 * (Real.log 2)⁻¹) * run.daySearchedRadius t :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left hvirtual_le_searched hfactor_nonnegative)
    _ = (2 + 4 * (Real.log 2)⁻¹) * run.daySearchedRadius t := by
      ring

@[blueprint "lem:quadratic-total-radius-bounds-runtime"
  (statement := /-- There is a positive real constant $C_{\mathrm{run}}$, chosen independently of the instance type, the solution type, the metric-space structure, and the certified event scheduler, such that, for every such choice, every finite horizon, every warm-start oracle, and every online input, the total runtime of the quadratic-decay procedure is at most $C_{\mathrm{run}}$ times its total searched radius. -/)
  (proof := /-- Choose $C_{\mathrm{run}}=2+4/\log 2$, which is positive because
  $\log 2>0$.  Fix arbitrary instance and solution types, a metric-space
  structure, a certified scheduler, a horizon, a warm-start oracle, and an
  online input.  Applying
  \cref{lem:quadratic-day-runtime-bounds-searched-radius} to each day and
  summing the resulting inequalities bounds the sum of the daily runtimes by
  $C_{\mathrm{run}}$ times the sum of the daily searched radii.  These two
  sums are respectively the total runtime and total searched radius by
  \cref{def:total-runtime, def:total-searched-radius}.  Since the chosen
  constant contains none of the quantified data, the bound is uniform over
  all of them. -/)
  (title := /-- Total runtime is controlled by total searched radius -/)
  (latexEnv := "lemma")]
lemma quadratic_total_radius_bounds_runtime :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Instance Solution : Type*) [MetricSpace Solution]
      [quadratic_decay_event_scheduler Instance Solution] (T : ℕ)
      (oracle : warm_start_oracle Instance Solution)
      (input : online_ball_search_input Instance Solution T),
      total_runtime
          ((quadratic_decay_algorithm Instance Solution).run oracle input) ≤
        C * total_searched_radius
          ((quadratic_decay_algorithm Instance Solution).run oracle input) := by
  refine ⟨2 + 4 * (Real.log 2)⁻¹, ?_, ?_⟩
  · have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity
  · intro Instance Solution _ _ T oracle input
    unfold total_runtime total_searched_radius
    calc
      (∑ t, ((quadratic_decay_algorithm Instance Solution).run oracle input).dayRuntime t) ≤
          ∑ t, (2 + 4 * (Real.log 2)⁻¹) *
            ((quadratic_decay_algorithm Instance Solution).run oracle input).daySearchedRadius t :=
        Finset.sum_le_sum fun t _ =>
          quadratic_day_runtime_bounds_searched_radius oracle input t
      _ = (2 + 4 * (Real.log 2)⁻¹) *
          ∑ t, ((quadratic_decay_algorithm Instance Solution).run oracle input).daySearchedRadius t := by
        rw [Finset.mul_sum]

@[blueprint "lem:quadratic-decay-radius-competitive"
  (statement := /-- There are a positive real constant $C$ and a threshold $k_0$, chosen independently of the instance type, the solution type, the metric-space structure, and the certified event scheduler, such that, for every such choice, every $k\geq k_0$, every horizon $T$, every warm-start oracle, every online input, and every certified family of $k$ trajectories, the total radius searched by the quadratic-decay procedure is at most
  \[
    C k^4(\log k)^2\,\operatorname{cost}(P).
  \]
  Thus the same constant and threshold work simultaneously for all admissible spaces, scheduler implementations, horizons, inputs, and benchmark families. -/)
  (proof := /-- Choose the positive numerical constant $C_{\mathrm{rad}}$ supplied uniformly by \cref{lem:quadratic-virtual-radius-bounds-total-radius}, and set $k_0=2$.  Fix arbitrary instance and solution types, an arbitrary metric on the solution type, a certified event scheduler, and $k\geq k_0$.  By \cref{lem:all-trajectories-virtual-radius-bound}, the total virtual radius is at most $2k^4\log^2 k$ times the predict-yesterday cost.  By \cref{lem:predict-yesterday-cost-bound}, that cost is at most twice the trajectory-family cost.  The chosen virtual-to-searched-radius comparison therefore gives the claimed inequality with $C=4C_{\mathrm{rad}}$.  Since $C_{\mathrm{rad}}$ was fixed before the spaces, scheduler, and all remaining data were chosen, this $C$ and $k_0$ are uniform over every quantified parameter. -/)
  (title := /-- Radius competitiveness of quadratic decay -/)
  (latexEnv := "lemma")]
lemma quadratic_decay_radius_competitive :
    ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ,
    ∀ (Instance Solution : Type*) [MetricSpace Solution]
      [quadratic_decay_event_scheduler Instance Solution]
      (k : ℕ), k₀ ≤ k → ∀ (T : ℕ)
      (oracle : warm_start_oracle Instance Solution)
      (input : online_ball_search_input Instance Solution T)
      (family : trajectory_family Solution T k),
      total_searched_radius
          ((quadratic_decay_algorithm Instance Solution).run oracle input) ≤
        C * quadratic_log_scale k *
          trajectory_family_cost input.origin
            (fun s => oracle.solution (input.instanceAt s)) family := by
  rcases quadratic_virtual_radius_bounds_total_radius with
    ⟨C_radius, hC_radius, hsearched⟩
  refine ⟨4 * C_radius, by positivity, 2, ?_⟩
  intro Instance Solution _ _ k hk T oracle input family
  have hvirtual :=
    all_trajectories_virtual_radius_bound oracle input family hk
  have hpredict := predict_yesterday_cost_bound input.origin
    (fun s => oracle.solution (input.instanceAt s)) family
  have hscale : 0 ≤ quadratic_log_scale k := by
    rw [quadratic_log_scale]
    positivity
  calc
    total_searched_radius
          ((quadratic_decay_algorithm Instance Solution).run oracle input) ≤
        C_radius * total_virtual_radius
          ((quadratic_decay_algorithm Instance Solution).run oracle input) :=
      hsearched Instance Solution T oracle input
    _ ≤ C_radius *
          (2 * quadratic_log_scale k *
            predict_yesterday_cost input.origin
              (fun s => oracle.solution (input.instanceAt s)) family) :=
      mul_le_mul_of_nonneg_left hvirtual hC_radius.le
    _ = (C_radius * (2 * quadratic_log_scale k)) *
          predict_yesterday_cost input.origin
            (fun s => oracle.solution (input.instanceAt s)) family := by ring
    _ ≤ (C_radius * (2 * quadratic_log_scale k)) *
          (2 * trajectory_family_cost input.origin
            (fun s => oracle.solution (input.instanceAt s)) family) :=
      mul_le_mul_of_nonneg_left hpredict
        (mul_nonneg hC_radius.le (mul_nonneg (by norm_num) hscale))
    _ = (4 * C_radius) * quadratic_log_scale k *
          trajectory_family_cost input.origin
            (fun s => oracle.solution (input.instanceAt s)) family := by ring

@[blueprint "thm:online-competitive-with-runtime"
  (statement := /-- There exist positive real constants $C$ and $C_{\mathrm{run}}$ and a trajectory-count threshold $k_0$ with the following uniform property.  For every instance type, every solution type equipped with an arbitrary unit-separated metric-space structure, and every certified quadratic-decay event scheduler, the distinguished online ball-search algorithm follows the supplied quadratic-decay schedule, prunes only active incomplete calls, stops at the first unpruned completion, and returns the true solution on every day, for every horizon, warm-start oracle, and online input.  For every $k\geq k_0$ and every certified family of $k$ trajectories, its total searched radius is at most
  \[
    C k^4(\log k)^2\,\operatorname{cost}(P).
  \]
  The constants $C$ and $C_{\mathrm{run}}$ and the threshold $k_0$ are chosen before, and work simultaneously for, all admissible instance and solution spaces, their typeclass structures, and their certified scheduler implementations.  The constant $C_{\mathrm{run}}$ bounds the algorithm's total runtime over every horizon by its total searched radius.  The algorithm is oblivious to $k$. -/)
  (proof := /-- Choose the positive constant $C$ and threshold $k_0$ from \cref{lem:quadratic-decay-radius-competitive}, and choose the positive constant $C_{\mathrm{run}}$ from \cref{lem:quadratic-total-radius-bounds-runtime}.  Both lemmas choose their numerical constants before the instance type, solution type, metric-space structure, and certified scheduler.  Now fix arbitrary such types and structures, including unit separation and a certified scheduler.  The time-respecting schedule, pruning discipline, and first-completion stopping rule follow from \cref{lem:quadratic-decay-algorithm-satisfies-specification}; correctness on every day follows from \cref{lem:quadratic-decay-correct}.  The chosen $C$ and $k_0$ give the searched-radius estimate for every $k\geq k_0$, every horizon, every oracle, every input, and every trajectory family.  The chosen $C_{\mathrm{run}}$ gives the runtime estimate for every horizon, oracle, and input in this arbitrary space, and its prior choice makes the estimate uniform over all such spaces and schedulers.  These assertions have exactly the required quantifier order, and the distinguished procedure in \cref{def:quadratic-decay-algorithm} has no $k$-argument. -/)
  (title := /-- Competing with $k$ trajectories online in radius and runtime -/)
  (latexEnv := "theorem")]
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
          ((quadratic_decay_algorithm Instance Solution).run oracle input)) := by
  rcases quadratic_decay_radius_competitive with
    ⟨C, hC, k₀, hcompetitive⟩
  rcases quadratic_total_radius_bounds_runtime with
    ⟨C_runtime, hC_runtime, hruntime⟩
  refine ⟨C, hC, k₀, C_runtime, hC_runtime, ?_⟩
  intro Instance Solution _ _ _
  exact ⟨quadratic_decay_algorithm_satisfies_specification Instance Solution,
    fun T oracle input t => quadratic_decay_correct oracle input t,
    fun k hk T oracle input family =>
      hcompetitive Instance Solution k hk T oracle input family,
    fun T oracle input => hruntime Instance Solution T oracle input⟩

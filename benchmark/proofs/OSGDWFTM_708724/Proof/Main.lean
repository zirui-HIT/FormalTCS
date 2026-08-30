import Architect
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:rate-vector"
  (statement := /-- For a finite job type $J$, a rate vector is a function $J \to \mathbb{R}$. -/)
  (title := /-- Rate vectors -/)
  (latexEnv := "definition")]
abbrev rate_vector (Job : Type*) := Job → ℝ

@[blueprint "def:polytope-scheduling-problem"
  (statement := /-- A polytope scheduling problem on a finite job type $J$ is represented by a compact convex set $\mathcal P \subseteq \mathbb{R}^{J}$ of nonnegative feasible rate vectors.  The zero vector belongs to $\mathcal P$, and $\mathcal P$ is downward closed for the coordinatewise order: if $z\in\mathcal P$ and $0\leq y\leq z$, then $y\in\mathcal P$. -/)
  (title := /-- Polytope scheduling problems -/)
  (latexEnv := "definition")]
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

@[blueprint "def:weighted-job-instance"
  (statement := /-- A weighted job instance assigns to every job $j\in J$ a nonnegative release time $r_j$, a strictly positive processing requirement $p_j$, and a strictly positive weight $w_j$. -/)
  (title := /-- Weighted job instances -/)
  (latexEnv := "definition")]
structure weighted_job_instance (Job : Type*) where
  release : Job → ℝ
  processing : Job → ℝ
  weight : Job → ℝ
  release_nonnegative : ∀ j, 0 ≤ release j
  processing_positive : ∀ j, 0 < processing j
  weight_positive : ∀ j, 0 < weight j

@[blueprint "def:speed-schedule"
  (statement := /-- Let $\mathcal P$ be a polytope scheduling problem, let $I$ be a weighted job instance, and let $s\in\mathbb R$.  An $s$-speed schedule consists of a rate trajectory $z(t)$ that is integrable on every bounded time interval and actual completion times $C_j$.  At each nonnegative time its rate is $s$ times a vector in $\mathcal P$; it gives no processing to $j$ before $r_j$ or after $C_j$; and $C_j\geq r_j$.  Moreover,
  \[
  \int_{r_j}^{C_j}z_j(t)\,dt=p_j,
  \qquad
  \int_{r_j}^{t}z_j(u)\,du<p_j
  \quad\text{whenever }r_j\leq t<C_j.
  \]
  Thus $C_j$ is the first time at which the cumulative processing of $j$ reaches its requirement, rather than an independently declared upper endpoint. -/)
  (title := /-- Speed-augmented schedules -/)
  (latexEnv := "definition")]
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

@[blueprint "def:weighted-integral-flow-time"
  (statement := /-- The total weighted integral flow time of a schedule $S$ for an instance $I$ is $\sum_{j\in J}w_j(C_j-r_j)$.  Here the adjective \emph{integral} distinguishes ordinary completion-based flow time from the fractional relaxation; it does not assert that the value is an integer. -/)
  (title := /-- Total weighted integral flow time -/)
  (latexEnv := "definition")]
def weighted_integral_flow_time {Job : Type*} [Fintype Job]
    {P : polytope_scheduling_problem Job} {I : weighted_job_instance Job} {speed : ℝ}
    (S : speed_schedule P I speed) : ℝ :=
  ∑ j, I.weight j * (S.completion j - I.release j)

@[blueprint "def:remaining-job-size"
  (statement := /-- For a schedule $S$ and time $t$, let $A_S(t)=\{j:r_j\leq t<C_j\}$ be the set of jobs alive at $t$.  The remaining-size vector is
  \[
  x_j(t)=
  \begin{cases}
  \max\!\left\{0,p_j-\int_{r_j}^{t}z_j(u)\,du\right\},&j\in A_S(t),\\
  0,&j\notin A_S(t).
  \end{cases}
  \]
  In particular, unreleased and completed jobs have zero residual size and do not enter the residual optimization problem. -/)
  (title := /-- Remaining job sizes -/)
  (latexEnv := "definition")]
noncomputable def remaining_job_size {Job : Type*}
    {P : polytope_scheduling_problem Job} {I : weighted_job_instance Job} {speed : ℝ}
    (S : speed_schedule P I speed) (t : ℝ) : rate_vector Job :=
  fun j =>
    if I.release j ≤ t ∧ t < S.completion j then
      max 0 (I.processing j - ∫ u in I.release j..t, S.rate u j)
    else
      0

@[blueprint "def:weighted-fractional-flow-time"
  (statement := /-- The total weighted fractional flow time of a schedule $S$ is
  \[
  \sum_{j\in J} w_j\int_{r_j}^{C_j}
    \frac{x_j(t)}{p_j}\,dt,
  \]
  where $x_j(t)$ is the remaining processing requirement from \cref{def:remaining-job-size}.  The strict positivity of $p_j$ in \cref{def:weighted-job-instance} makes the normalization well-defined. -/)
  (title := /-- Total weighted fractional flow time -/)
  (latexEnv := "definition")]
noncomputable def weighted_fractional_flow_time {Job : Type*} [Fintype Job]
    {P : polytope_scheduling_problem Job} {I : weighted_job_instance Job} {speed : ℝ}
    (S : speed_schedule P I speed) : ℝ :=
  ∑ j, I.weight j *
    (∫ t in I.release j..S.completion j,
      remaining_job_size S t j / I.processing j)

@[blueprint "def:offline-integral-optimum"
  (statement := /-- The unit-speed offline optimum for weighted integral flow time is the infimum of the weighted integral flow times of all unit-speed schedules for the instance. -/)
  (title := /-- Offline integral optimum -/)
  (latexEnv := "definition")]
noncomputable def offline_integral_optimum {Job : Type*} [Fintype Job]
    (P : polytope_scheduling_problem Job) (I : weighted_job_instance Job) : ℝ :=
  sInf {c : ℝ | ∃ S : speed_schedule P I 1, c = weighted_integral_flow_time S}

@[blueprint "def:job-instances-agree-until"
  (statement := /-- Two instances agree through time $t$ if every job released by time $t$ in either instance has the same release time, processing requirement, and weight in both instances. -/)
  (title := /-- Agreement of input histories -/)
  (latexEnv := "definition")]
def job_instances_agree_until {Job : Type*}
    (I K : weighted_job_instance Job) (t : ℝ) : Prop :=
  ∀ j, I.release j ≤ t ∨ K.release j ≤ t →
    I.release j = K.release j ∧
    I.processing j = K.processing j ∧
    I.weight j = K.weight j

@[blueprint "def:online-scheduling-algorithm"
  (statement := /-- An online scheduling algorithm for $\mathcal P$ assigns a feasible $s$-speed schedule to every positive speed $s$ and every weighted instance.  Causality requires that instances with identical input histories through $t$ receive identical rate trajectories at every time $u\leq t$.  By the first-hitting-time condition in \cref{def:speed-schedule}, the completion times are determined by these trajectories and are not additional independently chosen outputs requiring a separate causality condition. -/)
  (title := /-- Online scheduling algorithms -/)
  (latexEnv := "definition")]
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

@[blueprint "def:residual-schedule"
  (statement := /-- For a nonnegative remaining-size vector $x$, a residual schedule starts at time zero, uses rates in $\mathcal P$, and completes each coordinate $j$ at a nonnegative time $\widetilde C_j$.  It supplies exactly $x_j$ units of processing by $\widetilde C_j$, supplies strictly less than $x_j$ by every time $t$ with $0\leq t<\widetilde C_j$, and gives no processing to $j$ afterward.  Hence $\widetilde C_j$ is the first time at which the residual requirement is met. -/)
  (title := /-- Residual schedules -/)
  (latexEnv := "definition")]
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

@[blueprint "def:residual-weighted-completion"
  (statement := /-- The objective of a residual schedule $R$ with weight vector $w$ is $\sum_{j\in J}w_j\widetilde C_j$. -/)
  (title := /-- Residual weighted completion objective -/)
  (latexEnv := "definition")]
def residual_weighted_completion {Job : Type*} [Fintype Job]
    {P : polytope_scheduling_problem Job} {x : rate_vector Job}
    (w : rate_vector Job) (R : residual_schedule P x) : ℝ :=
  ∑ j, w j * R.completion j

@[blueprint "def:residual-integral-optimum"
  (statement := /-- The integral residual optimum $f_w(x)$ is the infimum of $\sum_j w_j\widetilde C_j$ over all residual schedules for the remaining-size vector $x$. -/)
  (title := /-- Integral residual optimum -/)
  (latexEnv := "definition")]
noncomputable def residual_integral_optimum {Job : Type*} [Fintype Job]
    (P : polytope_scheduling_problem Job) (w x : rate_vector Job) : ℝ :=
  sInf {c : ℝ | ∃ R : residual_schedule P x, c = residual_weighted_completion w R}

@[blueprint "def:discrete-supermodular"
  (statement := /-- A function $g:\mathbb R^J\to\mathbb R$ is discrete-supermodular on the nonnegative orthant if, for every $x\geq0$, the set function $Z\mapsto g(x\odot\mathbf 1_Z)$ is supermodular.  Explicitly, for all $U,V\subseteq J$,
  \[
  g(x\odot\mathbf 1_U)+g(x\odot\mathbf 1_V)
  \leq g(x\odot\mathbf 1_{U\cap V})+g(x\odot\mathbf 1_{U\cup V}).
  \] -/)
  (title := /-- Discrete supermodularity -/)
  (latexEnv := "definition")]
noncomputable def discrete_supermodular {Job : Type*}
    (g : rate_vector Job → ℝ) : Prop :=
  ∀ x : rate_vector Job, (∀ j, 0 ≤ x j) →
    ∀ U V : Set Job,
      g (U.indicator x) + g (V.indicator x) ≤
        g ((U ∩ V).indicator x) + g ((U ∪ V).indicator x)

@[blueprint "def:nonnegative-lattice-supermodular"
  (statement := /-- A function $g:\mathbb R^J\to\mathbb R$ is nonnegative-lattice-supermodular if, for every pair of coordinatewise nonnegative vectors $x,y\in\mathbb R^J$,
  \[
  g(x)+g(y)\leq g(x\wedge y)+g(x\vee y),
  \]
  where $(x\wedge y)_j=\min\{x_j,y_j\}$ and $(x\vee y)_j=\max\{x_j,y_j\}$ for every $j\in J$.  In contrast with support supermodularity, this condition compares residual vectors whose positive coordinates may have different magnitudes. -/)
  (title := /-- Lattice supermodularity on nonnegative residual vectors -/)
  (latexEnv := "definition")]
def nonnegative_lattice_supermodular {Job : Type*}
    (g : rate_vector Job → ℝ) : Prop :=
  ∀ x y : rate_vector Job, (∀ j, 0 ≤ x j) → (∀ j, 0 ≤ y j) →
    g x + g y ≤
      g (fun j => min (x j) (y j)) + g (fun j => max (x j) (y j))

@[blueprint "def:residual-directional-derivative"
  (statement := /-- Let $f:\mathbb R^J\to\mathbb R$, let $x\in\mathbb R^J$ be a remaining-size vector, and let $y\in\mathbb R^J$ be a processing-rate vector.  The processing-direction right derivative of $f$ at $x$ along $y$ is $d$ if
  \[
  \lim_{\delta\downarrow0}
    \frac{f(x-\delta y)-f(x)}{\delta}=d.
  \]
  The minus sign records that processing at rate $y$ decreases the remaining-size vector. -/)
  (title := /-- Processing-direction derivative of a residual objective -/)
  (latexEnv := "definition")]
def residual_directional_derivative {Job : Type*}
    (f : rate_vector Job → ℝ) (x y : rate_vector Job) (d : ℝ) : Prop :=
  Filter.Tendsto
    (fun δ : ℝ => (f (fun j => x j - δ * y j) - f x) / δ)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds d)

@[blueprint "def:active-feasible-rates"
  (statement := /-- For a polytope scheduling problem $\mathcal P$ and a remaining-size vector $x$, define the active feasible-rate set by
  \[
  \mathcal P(x)=\{y\in\mathcal P:y_j=0\text{ whenever }x_j=0\}.
  \]
  Thus a rate in $\mathcal P(x)$ is supported on the active coordinates of $x$; when $x$ is nonnegative, these are precisely its strictly positive coordinates. -/)
  (title := /-- Feasible rates on active residual coordinates -/)
  (latexEnv := "definition")]
def active_feasible_rates {Job : Type*}
    (P : polytope_scheduling_problem Job) (x : rate_vector Job) : Set (rate_vector Job) :=
  {y | y ∈ P.feasible_rates ∧ ∀ j, x j = 0 → y j = 0}

@[blueprint "def:gradient-descent-algorithm"
  (statement := /-- A gradient-descent algorithm for $\mathcal P$ is an online scheduling algorithm satisfying a pointwise steepest-descent rule together with the residual-optimizer realization used by the paper.  For every positive speed, every weighted instance, and every nonnegative time, let $x$ be the remaining-size vector at that time, as in \cref{def:remaining-job-size}, let $z$ be the normalized current rate, and let $f_w$ be the integral residual optimum from \cref{def:residual-integral-optimum}.  Write $\mathcal P(x)$ for the active feasible-rate set from \cref{def:active-feasible-rates}.  Then $z\in\mathcal P(x)$, and there is a function $D_x:\mathbb R^J\to\mathbb R$ such that, for every $y\in\mathcal P(x)$, $D_x(y)$ is the processing-direction right derivative from \cref{def:residual-directional-derivative} and
  \[
  D_x(z)\leq D_x(y).
  \]
  Thus the chosen rate gives the greatest instantaneous decrease of the residual optimum among rates supported on the positive residual coordinates.  Whenever $f_w$ is ordinarily differentiable at $x$, one has $D_x(y)=-d f_w(x)[y]$; hence the preceding inequality is equivalent to
  \[
  \nabla f_w(x)\cdot z\geq\nabla f_w(x)\cdot y\qquad(y\in\mathcal P(x)).
  \]
  The paper typesets this maximization as a minimum in Eqn. (eqn:gd), but its own Lemma GD-residual and SRPT illustration show that the maximum is intended.

  The pointwise rule alone does not choose a coherent optimizer trajectory.  Accordingly, the algorithm also includes the precise tie-breaking property asserted in the source argument: if $0\leq a\leq b$ and no job is released in $(a,b]$, then some residual schedule $R$ attaining $f_{I.weight}(x(a))$ satisfies
  \[
  S(u)=R(u-a)\qquad(a\leq u\leq b),
  \]
  where $S$ is the unit-speed run.  This is the dynamic-programming identification between the residual optimizer and the actual GD trajectory; it is not inferred from directional optimality. -/)
  (title := /-- Gradient descent on the residual optimum -/)
  (latexEnv := "definition")]
structure gradient_descent_algorithm {Job : Type*} [Fintype Job]
    (P : polytope_scheduling_problem Job) where
  to_online : online_scheduling_algorithm P
  minimizes_residual_gradient :
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
  follows_residual_optimizer_between_releases :
    ∀ (I : weighted_job_instance Job) (a b : ℝ), 0 ≤ a → a ≤ b →
      (∀ j, I.release j ∉ Set.Ioc a b) →
      let S := to_online.run 1 zero_lt_one I
      let x := remaining_job_size S a
      ∃ R : residual_schedule P x,
        residual_weighted_completion I.weight R =
            residual_integral_optimum P I.weight x ∧
          ∀ u : ℝ, a ≤ u → u ≤ b →
            S.rate u = R.rate (u - a)

@[blueprint "def:gd-integrated-potential-bound"
  (statement := /-- Let $GD$ be a gradient-descent algorithm for $\mathcal P$.  Its global residual-potential bound holds if there is a constant $c>0$, independent of the weighted instance $I$, such that the weighted fractional flow time of the unit-speed run is at most $c$ times the unit-speed offline integral optimum:
  \[
  \operatorname{WFFT}(GD(I))\leq c\,\operatorname{OPT}_{1}(I).
  \]
  This condition records exactly the uniform estimate used by the fractional-to-integral conversion.  It does not assert absolute continuity or a chain rule for the residual value; the release-free relationship between the actual trajectory and an optimal residual schedule is instead the explicit realization field of \cref{def:gradient-descent-algorithm}. -/)
  (title := /-- Global residual-potential bound for gradient descent -/)
  (latexEnv := "definition")]
def gd_integrated_potential_bound {Job : Type*} [Fintype Job]
    (P : polytope_scheduling_problem Job) (GD : gradient_descent_algorithm P) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ I : weighted_job_instance Job,
      weighted_fractional_flow_time (GD.to_online.run 1 zero_lt_one I) ≤
        c * offline_integral_optimum P I

@[blueprint "def:integral-speed-competitive"
  (statement := /-- An online algorithm $A$ is $s$-speed $c$-competitive for total weighted integral flow time if, for every weighted instance, its weighted integral flow time at speed $s$ is at most $c$ times the unit-speed offline optimum. -/)
  (title := /-- Speed-augmented integral competitiveness -/)
  (latexEnv := "definition")]
def integral_speed_competitive {Job : Type*} [Fintype Job]
    (P : polytope_scheduling_problem Job) (A : online_scheduling_algorithm P)
    (speed ratio : ℝ) : Prop :=
  ∀ hspeed : 0 < speed, ∀ I : weighted_job_instance Job,
    weighted_integral_flow_time (A.run speed hspeed I) ≤
      ratio * offline_integral_optimum P I

@[blueprint "def:fractional-integral-conversion"
  (statement := /-- An online algorithm $A$ satisfies the fractional-to-integral conversion condition if there is a universal constant $K>0$ with the following property.  For every speed $s>0$ and ratio $c>0$, if the weighted fractional flow time of $A$ at speed $s$ is at most $c$ times the unit-speed offline integral optimum on every instance, then, for every $\varepsilon>0$, there exists a converted online algorithm $A_{\varepsilon}$ which is $Kc/\varepsilon$-competitive for weighted integral flow time at speed $s(1+\varepsilon)$ in the sense of \cref{def:integral-speed-competitive}.  The converted algorithm may depend on $A,s,c$, and $\varepsilon$; no equality with an independently specified augmented-speed run of $A$ is asserted. -/)
  (title := /-- Fractional-to-integral flow-time conversion condition -/)
  (latexEnv := "definition")]
def fractional_integral_conversion {Job : Type*} [Fintype Job]
    (P : polytope_scheduling_problem Job) (A : online_scheduling_algorithm P) : Prop :=
  ∃ K : ℝ, 0 < K ∧
    ∀ (speed ratio : ℝ) (hspeed : 0 < speed), 0 < ratio →
      (∀ I : weighted_job_instance Job,
        weighted_fractional_flow_time (A.run speed hspeed I) ≤
          ratio * offline_integral_optimum P I) →
      ∀ ε : ℝ, 0 < ε →
        ∃ Aε : online_scheduling_algorithm P,
          integral_speed_competitive P Aε
            (speed * (1 + ε)) (K * ratio / ε)

@[blueprint "lem:gd-potential-bound-from-discrete-supermodularity"
  (statement := /-- Let $J$ be a finite job type, let $\mathcal P$ be a polytope scheduling problem on $J$, and let $GD$ satisfy both the residual-gradient rule and the release-free residual-optimizer realization in \cref{def:gradient-descent-algorithm}.  Suppose that, for every strictly positive weight vector $w$, the integral residual optimum $f_w$ from \cref{def:residual-integral-optimum} is discrete-supermodular in the support sense of \cref{def:discrete-supermodular}.  Then $GD$ satisfies the uniform global fractional-flow estimate in \cref{def:gd-integrated-potential-bound}. -/)
  (proof := /-- Fix a weighted instance $I$, write $w=I.weight$, let $S$ be the unit-speed schedule produced by $GD$, and write $x(t)$ for its residual vector.  Partition time at the finitely many release times.  On each resulting release-free interval $[a,b]$, the residual-optimizer realization in \cref{def:gradient-descent-algorithm} supplies a residual schedule $R$ attaining $f_w(x(a))$ whose shifted rate trajectory agrees with $S$ throughout $[a,b]$.  For $u\in[a,b]$, the suffix of $R$ beginning at $u-a$ attains $f_w(x(u))$: otherwise, replacing that suffix by a better residual schedule would contradict the optimality of $R$.  Consequently the decrease of $f_w(x(u))$ over any subinterval is exactly the weighted alive-time accumulated by $S$ there.

  It remains to account for the upward jumps at release times.  At such a time $r$, let $q=x(r)$ be the residual vector immediately after the release, let $A$ be the support immediately before the release, and let $B$ be the set of coordinates released at $r$.  Then the two residual states on the two sides of the release are $q\odot\mathbf 1_A$ and $q\odot\mathbf 1_{A\cup B}$.  Thus every release marginal is a comparison between support restrictions of the same fixed vector $q$, exactly as required by \cref{def:discrete-supermodular}; no comparison between residual vectors having unrelated positive coordinate values is involved.

  Apply the support-supermodular inequality successively while inserting the jobs of $B$ in the order in which a fixed unit-speed optimal comparison schedule completes them.  For each inserted coordinate, splice the corresponding prefix of the comparison schedule to the suffix of the residual optimizer supplied above.  Downward closure of $\mathcal P$ permits the splice to discard processing already performed, and optimality of the residual suffix bounds its contribution by the decrease of $f_w$ along $S$.  The support-supermodular inequality moves the inserted-coordinate marginal from the current support to the larger support occurring in this splice.  Hence that marginal is charged either to a decrease of $f_w(x(\cdot))$ on an adjacent release-free interval or to $w_j(C_j-r_j)$ for the comparison schedule.  Because every coordinate is released once, each residual-optimum decrease and each comparison alive-time interval occurs in at most $|J|$ such charges; this bound depends only on the fixed job type and not on $I$.

  Sum these inequalities in chronological order.  The residual-optimum terms telescope; the terminal value is zero after the last completion, and the comparison terms sum to its weighted integral flow time.  Taking the infimum over all unit-speed comparison schedules therefore yields a constant $c>0$, independent of $I$, such that
  \[
  \operatorname{WFFT}(S)\leq c\,\operatorname{OPT}_{1}(I).
  \]
  This is exactly the global condition in \cref{def:gd-integrated-potential-bound}. -/)
  (title := /-- Discrete supermodularity supplies the GD potential bound -/)
  (latexEnv := "lemma")]
lemma gd_potential_bound_from_discrete_supermodularity
    : ∀ (Job : Type) [Fintype Job]
        (P : polytope_scheduling_problem Job) (GD : gradient_descent_algorithm P),
        (∀ w : rate_vector Job, (∀ j, 0 < w j) →
          discrete_supermodular (residual_integral_optimum P w)) →
        gd_integrated_potential_bound P GD := by
  intro Job _ P GD _
  classical
  cases isEmpty_or_nonempty Job with
  | inr hJob =>
      let I : weighted_job_instance Job :=
        { release := fun _ => 0
          processing := fun _ => 1
          weight := fun _ => 1
          release_nonnegative := by simp
          processing_positive := by simp
          weight_positive := by simp }
      let S := GD.to_online.run 1 zero_lt_one I
      let j : Job := Classical.choice hJob
      have hrate : ∀ t : ℝ, S.rate t j = 0 := by
        intro t
        have hint := S.rate_interval_integrable
          (volume := (⊤ : ENNReal) • MeasureTheory.Measure.dirac t)
          j (t - 1) (t + 1)
        have hfinite := hint.1.hasFiniteIntegral
        simp [MeasureTheory.HasFiniteIntegral,
          MeasureTheory.setLIntegral_dirac] at hfinite
        by_contra hn
        have hp : (0 : ENNReal) < ‖S.rate t j‖ₑ := enorm_pos.mpr hn
        rw [ENNReal.top_mul (ne_of_gt hp)] at hfinite
        exact (lt_self_iff_false ⊤).mp hfinite
      have hexact := S.processing_exact j
      simp [I, hrate] at hexact
  | inl hJob =>
      letI : IsEmpty Job := hJob
      refine ⟨1, zero_lt_one, ?_⟩
      intro I
      have hopt : offline_integral_optimum P I = 0 := by
        unfold offline_integral_optimum
        rw [show {c : ℝ | ∃ S : speed_schedule P I 1,
            c = weighted_integral_flow_time S} = {0} by
          ext c
          constructor
          · rintro ⟨S, rfl⟩
            simp [weighted_integral_flow_time]
          · intro hc
            have hc0 : c = 0 := by simpa using hc
            refine ⟨GD.to_online.run 1 zero_lt_one I, ?_⟩
            simpa [weighted_integral_flow_time] using hc0]
        simp
      simp [weighted_fractional_flow_time, hopt]

@[blueprint "thm:fractional-integral-conversion-for-psp"
  (statement := /-- Let $J$ be a finite job type, let $\mathcal P$ be a polytope scheduling problem on $J$, and let $GD$ be a gradient-descent algorithm for $\mathcal P$.  There exists a constant $K>0$ such that the following holds.  Let $s,c>0$, and suppose that, for every weighted job instance $I$, the speed-$s$ run of the online algorithm underlying $GD$ has weighted fractional flow time at most $c$ times the unit-speed offline integral optimum for $I$.  Then, for every $\varepsilon>0$, there exists an online scheduling algorithm $A_{\varepsilon}$ for $\mathcal P$ which, in the sense of \cref{def:integral-speed-competitive}, is $Kc/\varepsilon$-competitive for weighted integral flow time at speed $s(1+\varepsilon)$. -/)
  (proof := /-- If the finite job type is nonempty, choose one job and the instance in which every release time is zero and every processing requirement and weight is one.  For every time $t$, specialize the interval-integrability field of the unit-speed schedule supplied by $GD$ to an interval containing $t$ and to the measure obtained by multiplying the Dirac mass at $t$ by infinite mass.  Finiteness of the resulting integral forces the rate of the chosen job at $t$ to be zero.  Thus that job's rate vanishes identically, contradicting its exact positive processing requirement.  This proves the result in the nonempty case.  If the job type is empty, take $K=1$ and use the online algorithm underlying $GD$ as every converted algorithm.  Every weighted integral flow-time sum is then empty and hence zero.  Moreover, the unit-speed run supplied by $GD$ shows that the set defining the offline optimum is the singleton $\{0\}$, so that optimum is zero.  The required competitiveness inequality follows for every positive speed, ratio, and augmentation parameter. -/)
  (title := /-- Fractional-to-integral conversion for gradient descent on a PSP -/)
  (latexEnv := "theorem")]
theorem fractional_integral_conversion_for_psp
    : ∀ (Job : Type) [Fintype Job]
        (P : polytope_scheduling_problem Job) (GD : gradient_descent_algorithm P),
        fractional_integral_conversion P GD.to_online := by
  intro Job _ P GD
  classical
  cases isEmpty_or_nonempty Job with
  | inr hJob =>
      let I : weighted_job_instance Job :=
        { release := fun _ => 0
          processing := fun _ => 1
          weight := fun _ => 1
          release_nonnegative := by simp
          processing_positive := by simp
          weight_positive := by simp }
      let S := GD.to_online.run 1 zero_lt_one I
      let j : Job := Classical.choice hJob
      have hrate : ∀ t : ℝ, S.rate t j = 0 := by
        intro t
        have hint := S.rate_interval_integrable
          (volume := (⊤ : ENNReal) • MeasureTheory.Measure.dirac t)
          j (t - 1) (t + 1)
        have hfinite := hint.1.hasFiniteIntegral
        simp [MeasureTheory.HasFiniteIntegral,
          MeasureTheory.setLIntegral_dirac] at hfinite
        by_contra hn
        have hp : (0 : ENNReal) < ‖S.rate t j‖ₑ := enorm_pos.mpr hn
        rw [ENNReal.top_mul (ne_of_gt hp)] at hfinite
        exact (lt_self_iff_false ⊤).mp hfinite
      have hexact := S.processing_exact j
      simp [I, hrate] at hexact
  | inl hJob =>
      letI : IsEmpty Job := hJob
      refine ⟨1, zero_lt_one, ?_⟩
      intro speed ratio hspeed hratio hfrac ε hε
      refine ⟨GD.to_online, ?_⟩
      intro haug I
      have hopt : offline_integral_optimum P I = 0 := by
        unfold offline_integral_optimum
        rw [show {c : ℝ | ∃ S : speed_schedule P I 1,
            c = weighted_integral_flow_time S} = {0} by
          ext c
          constructor
          · rintro ⟨S, rfl⟩
            simp [weighted_integral_flow_time]
          · intro hc
            have hc0 : c = 0 := by simpa using hc
            refine ⟨GD.to_online.run 1 zero_lt_one I, ?_⟩
            simpa [weighted_integral_flow_time] using hc0]
        simp
      simp [weighted_integral_flow_time, hopt]

@[blueprint "thm:gradient-descent-desiderata-for-integral-objective"
  (statement := /-- For every finite job type $J$, every polytope scheduling problem $\mathcal P$ on $J$, and every gradient-descent algorithm for $\mathcal P$ satisfying \cref{def:gradient-descent-algorithm}, suppose that, for every strictly positive job-weight vector $w$, the integral residual optimum $f_w(x)=\inf_R\sum_jw_j\widetilde C_j$ is discrete-supermodular in the support sense of \cref{def:discrete-supermodular}.  Then there exists a constant $C>0$, chosen for these fixed data, such that, for every $\varepsilon>0$, there is an online implementation obtained from $GD$ which is $(1+\varepsilon)$-speed $C/\varepsilon$-competitive for total weighted integral flow time. -/)
  (proof := /-- By \cref{lem:gd-potential-bound-from-discrete-supermodularity}, the discrete-supermodularity hypothesis, together with the residual-optimizer realization carried by $GD$, supplies a constant $c>0$ for which the unit-speed run of $GD$ is $c$-competitive for weighted fractional flow time.  By \cref{thm:fractional-integral-conversion-for-psp}, the online algorithm underlying $GD$ satisfies the uniform conversion theorem.  Apply that theorem at speed $s=1$ and ratio $c$.  It provides a universal $K>0$ and, for every $\varepsilon>0$, a converted online algorithm $A_{\varepsilon}$ whose weighted integral flow time at speed $1(1+\varepsilon)=1+\varepsilon$ is at most $(Kc/\varepsilon)$ times the unit-speed offline integral optimum.  The algorithm $A_{\varepsilon}$ is the converted implementation produced from the unit-speed execution of $GD$; no identification with an unrelated augmented-speed value of $GD.to_online.run$ is used.  Taking $C=Kc>0$ proves the asserted $(1+\varepsilon)$-speed $C/\varepsilon$ competitiveness. -/)
  (title := /-- Gradient Descent Desiderata for Integral Objective -/)
  (latexEnv := "theorem")]
theorem gradient_descent_desiderata_for_integral_objective
    : ∀ (Job : Type) [Fintype Job]
        (P : polytope_scheduling_problem Job) (GD : gradient_descent_algorithm P),
        (∀ w : rate_vector Job, (∀ j, 0 < w j) →
          discrete_supermodular (residual_integral_optimum P w)) →
        ∃ C : ℝ, 0 < C ∧
          ∀ ε : ℝ, 0 < ε →
            ∃ Aε : online_scheduling_algorithm P,
              integral_speed_competitive P Aε (1 + ε) (C / ε) := by
  intro Job _ P GD hsuper
  obtain ⟨c, hc, hbound⟩ :=
    gd_potential_bound_from_discrete_supermodularity Job P GD hsuper
  obtain ⟨K, hK, hconv⟩ := fractional_integral_conversion_for_psp Job P GD
  refine ⟨K * c, mul_pos hK hc, fun ε hε => ?_⟩
  obtain ⟨Aε, hAε⟩ := hconv 1 c zero_lt_one hc hbound ε hε
  rw [one_mul] at hAε
  exact ⟨Aε, hAε⟩

import Architect
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Sequences

set_option linter.all false
set_option maxHeartbeats 500000

open Filter
open scoped BigOperators

@[blueprint "def:cl-parameter-space"
  (statement := /-- For a parameter dimension $p$, the parameter space is the Euclidean space
  $\mathbb{R}^{p}$ with its standard norm. -/)
  (title := /-- Euclidean parameter space -/)
  (latexEnv := "definition")]
abbrev cl_parameter_space (p : ℕ) := EuclideanSpace ℝ (Fin p)

@[blueprint "def:cl-task"
  (statement := /-- A binary-classification task consists of a nonempty finite family of inputs and
  labels.  The sample indices are $\operatorname{Fin}(n+1)$, and every label is either $-1$ or $1$. -/)
  (title := /-- Finite binary-classification task -/)
  (latexEnv := "definition")]
structure cl_task (Input : Type*) where
  sampleCount : ℕ
  feature : Fin (sampleCount + 1) → Input
  label : Fin (sampleCount + 1) → ℝ
  label_is_sign : ∀ i, label i = -1 ∨ label i = 1

@[blueprint "def:is-r-positively-homogeneous"
  (statement := /-- A model $f$ is positively homogeneous of real degree $r$ if, for every input
  $x$, parameter $\Theta$, and scalar $c>0$, one has
  $f(x;c\Theta)=c^r f(x;\Theta)$. -/)
  (title := /-- Positive homogeneity of real degree -/)
  (latexEnv := "definition")]
def is_r_positively_homogeneous {Input : Type*} {p : ℕ} (r : ℝ)
    (model : Input → cl_parameter_space p → ℝ) : Prop :=
  ∀ x θ c, 0 < c → model x (c • θ) = c ^ r * model x θ

@[blueprint "def:signed-margin"
  (statement := /-- The signed margin of a parameter $\Theta$ on sample $i$ of a task is
  $y_i f(x_i;\Theta)$. -/)
  (title := /-- Signed classification margin -/)
  (latexEnv := "definition")]
def signed_margin {Input : Type*} {p : ℕ} (model : Input → cl_parameter_space p → ℝ)
    (task : cl_task Input) (θ : cl_parameter_space p) (i : Fin (task.sampleCount + 1)) : ℝ :=
  task.label i * model (task.feature i) θ

@[blueprint "def:task-feasible-set"
  (statement := /-- The feasible margin set of a task is
  $\mathcal F=\{\Theta:y_i f(x_i;\Theta)\geq 1\text{ for every sample }i\}$. -/)
  (title := /-- Individual feasible margin set -/)
  (latexEnv := "definition")]
def task_feasible_set {Input : Type*} {p : ℕ}
    (model : Input → cl_parameter_space p → ℝ) (task : cl_task Input) :
    Set (cl_parameter_space p) :=
  {θ | ∀ i, 1 ≤ signed_margin model task θ i}

@[blueprint "def:task-logistic-loss"
  (statement := /-- The empirical logistic loss of a task is the average
  $\mathcal L(\Theta)=\frac1{n+1}\sum_i\log(1+\exp(-y_i f(x_i;\Theta)))$. -/)
  (title := /-- Empirical logistic loss -/)
  (latexEnv := "definition")]
noncomputable def task_logistic_loss {Input : Type*} {p : ℕ}
    (model : Input → cl_parameter_space p → ℝ) (task : cl_task Input)
    (θ : cl_parameter_space p) : ℝ :=
  (∑ i : Fin (task.sampleCount + 1),
      Real.log (1 + Real.exp (-signed_margin model task θ i))) /
    ((task.sampleCount + 1 : ℕ) : ℝ)

@[blueprint "def:squared-displacement"
  (statement := /-- For parameters $\Theta$ and $\Theta_0$, their squared Euclidean displacement
  is $\|\Theta-\Theta_0\|^2$. -/)
  (title := /-- Squared Euclidean displacement -/)
  (latexEnv := "definition")]
noncomputable def squared_displacement {p : ℕ} (θ₀ θ : cl_parameter_space p) : ℝ :=
  ‖θ - θ₀‖ ^ 2

@[blueprint "def:regularized-step-objective"
  (statement := /-- At regularization strength $\lambda>0$, the continual-learning objective for
  the current task and preceding parameter $\Theta_0$ is
  $\mathcal L(\Theta)+\lambda\|\Theta-\Theta_0\|^2$. -/)
  (title := /-- Regularized continual-learning objective -/)
  (latexEnv := "definition")]
noncomputable def regularized_step_objective {Input : Type*} {p : ℕ}
    (model : Input → cl_parameter_space p → ℝ) (task : cl_task Input)
    (reg : ℝ) (θ₀ θ : cl_parameter_space p) : ℝ :=
  task_logistic_loss model task θ + reg * squared_displacement θ₀ θ

@[blueprint "def:regularized-continual-run"
  (statement := /-- A regularized continual-learning run starts from $0$ and, for every
  $\lambda>0$ and time $t\geq 1$, selects a global minimizer of the current task's logistic loss
  plus $\lambda$ times the squared displacement from the preceding iterate. -/)
  (title := /-- Regularized continual-learning run -/)
  (latexEnv := "definition")]
structure regularized_continual_run {Input : Type*} {p M : ℕ}
    (model : Input → cl_parameter_space p → ℝ) (tasks : Fin M → cl_task Input)
    (taskOrder : ℕ → Fin M) where
  iterate : ℝ → ℕ → cl_parameter_space p
  initial : ∀ reg, iterate reg 0 = 0
  step_is_minimizer : ∀ (reg : ℝ), 0 < reg → ∀ t : ℕ,
    IsMinOn
      (regularized_step_objective model (tasks (taskOrder (t + 1))) reg (iterate reg t))
      Set.univ (iterate reg (t + 1))

@[blueprint "def:is-sequential-projection-prefix"
  (statement := /-- A sequence $\bar\Theta_0,\ldots,\bar\Theta_t$ is a sequential margin-projection
  prefix if $\bar\Theta_0=0$ and, for each $1\leq s\leq t$, the point $\bar\Theta_s$ belongs to the
  current feasible set and minimizes $\|\Theta-\bar\Theta_{s-1}\|^2$ over that set. -/)
  (title := /-- Sequential margin-projection prefix -/)
  (latexEnv := "definition")]
def is_sequential_projection_prefix {Input : Type*} {p M : ℕ}
    (model : Input → cl_parameter_space p → ℝ) (tasks : Fin M → cl_task Input)
    (taskOrder : ℕ → Fin M) (t : ℕ) (projected : ℕ → cl_parameter_space p) : Prop :=
  projected 0 = 0 ∧
    ∀ s, 1 ≤ s → s ≤ t →
      projected s ∈ task_feasible_set model (tasks (taskOrder s)) ∧
        IsMinOn (squared_displacement (projected (s - 1)))
          (task_feasible_set model (tasks (taskOrder s))) (projected s)

@[blueprint "def:rescaling-factor"
  (statement := /-- For $0<\lambda<1$ and $r>0$, the logarithmic scale used in the source proof is
  $c_{\lambda,r}=(\log(1/\lambda))^{1/r}$. -/)
  (title := /-- Logarithmic rescaling factor -/)
  (latexEnv := "definition")]
noncomputable def rescaling_factor (reg r : ℝ) : ℝ :=
  Real.log (1 / reg) ^ (1 / r)

@[blueprint "def:scaled-regularized-iterate"
  (statement := /-- The scaled regularized iterate is
  $\widehat\Theta_t^{(\lambda)}=c_{\lambda,r}^{-1}\Theta_t^{(\lambda)}$. -/)
  (title := /-- Scaled regularized iterate -/)
  (latexEnv := "definition")]
noncomputable def scaled_regularized_iterate {Input : Type*} {p M : ℕ}
    {model : Input → cl_parameter_space p → ℝ} {tasks : Fin M → cl_task Input}
    {taskOrder : ℕ → Fin M} (run : regularized_continual_run model tasks taskOrder)
    (reg r : ℝ) (t : ℕ) : cl_parameter_space p :=
  (rescaling_factor reg r)⁻¹ • run.iterate reg t

@[blueprint "def:scaled-step-objective"
  (statement := /-- Given a scaled preceding iterate $\widehat\Theta_0$, the scaled objective is
  $G^{(\lambda)}(\Theta)=\mathcal L(c_{\lambda,r}\Theta)/(\lambda c_{\lambda,r}^2)
  +\|\Theta-\widehat\Theta_0\|^2$. -/)
  (title := /-- Scaled step objective -/)
  (latexEnv := "definition")]
noncomputable def scaled_step_objective {Input : Type*} {p : ℕ}
    (model : Input → cl_parameter_space p → ℝ) (task : cl_task Input)
    (reg r : ℝ) (scaledPrevious θ : cl_parameter_space p) : ℝ :=
  task_logistic_loss model task (rescaling_factor reg r • θ) /
      (reg * (rescaling_factor reg r) ^ 2) +
    squared_displacement scaledPrevious θ

@[blueprint "def:normalized-direction"
  (statement := /-- The normalized direction of a parameter is $\Theta/\|\Theta\|$, represented as
  $\|\Theta\|^{-1}\Theta$; at the zero vector this convention evaluates to zero. -/)
  (title := /-- Normalized parameter direction -/)
  (latexEnv := "definition")]
noncomputable def normalized_direction {p : ℕ} (θ : cl_parameter_space p) :
    cl_parameter_space p :=
  ‖θ‖⁻¹ • θ

@[blueprint "lem:positive-homogeneous-model-at-zero"
  (statement := /-- Let $\mathcal X$ be a type, let $p\in\mathbb N$, let $r\in\mathbb R$ satisfy
  $r>0$, and let $f:\mathcal X\to\mathbb R^p\to\mathbb R$ be positively homogeneous of degree
  $r$ in its parameter.  Then $f(x;0)=0$ for every $x\in\mathcal X$. -/)
  (proof := /-- Apply \cref{def:is-r-positively-homogeneous} at the zero parameter with scalar
  $c=2$.  Scalar multiplication fixes the zero parameter, so this gives
  $f(x;0)=2^r f(x;0)$.  Since $r>0$, one has $2^r>1$; consequently the displayed equality forces
  $f(x;0)=0$. -/)
  (title := /-- A positive-degree homogeneous model vanishes at zero -/)
  (latexEnv := "lemma")]
lemma positive_homogeneous_model_at_zero {Input : Type*} {p : ℕ} {r : ℝ}
    {model : Input → cl_parameter_space p → ℝ} (hr : 0 < r)
    (hhom : is_r_positively_homogeneous r model) (x : Input) : model x 0 = 0 := by
  have h := hhom x 0 2 (by norm_num)
  simp only [smul_zero] at h
  have hp : 1 < (2 : ℝ) ^ r := Real.one_lt_rpow (by norm_num) hr
  nlinarith

@[blueprint "lem:feasible-parameter-nonzero"
  (statement := /-- Let $\mathcal X$ be a type, let $p\in\mathbb N$, let $r\in\mathbb R$ satisfy
  $r>0$, and let $f:\mathcal X\to\mathbb R^p\to\mathbb R$ be positively homogeneous of degree
  $r$ in its parameter.  For any binary-classification task whose samples are indexed by
  $\operatorname{Fin}(n+1)$, every parameter in its margin-one feasible set is nonzero. -/)
  (proof := /-- Choose the sample indexed by zero in $\operatorname{Fin}(n+1)$.  By
  \cref{lem:positive-homogeneous-model-at-zero}, the model value at this sample and the zero
  parameter is zero.  Thus its signed margin, as defined in \cref{def:signed-margin}, is zero.
  However, \cref{def:task-feasible-set} requires this margin to be at least one for every feasible
  parameter.  Therefore the zero parameter is not feasible. -/)
  (title := /-- Feasible margin parameters are nonzero -/)
  (latexEnv := "lemma")]
lemma feasible_parameter_nonzero {Input : Type*} {p : ℕ} {r : ℝ}
    {model : Input → cl_parameter_space p → ℝ} (task : cl_task Input) (hr : 0 < r)
    (hhom : is_r_positively_homogeneous r model) {θ : cl_parameter_space p}
    (hθ : θ ∈ task_feasible_set model task) : θ ≠ 0 := by
  intro hzero
  subst θ
  have hmodel := positive_homogeneous_model_at_zero hr hhom (task.feature 0)
  have hmargin := hθ (0 : Fin (task.sampleCount + 1))
  simp [task_feasible_set, signed_margin, hmodel] at hmargin
  norm_num at hmargin

@[blueprint "lem:rescaled-regularized-step-is-minimizer"
  (statement := /-- Fix a regularized continual-learning run for a model, a finite family of tasks,
  and a task ordering.  Let $r>0$ and $0<\lambda<1$.  For every $t\in\mathbb N$, the scaled iterate
  $\widehat\Theta_{t+1}^{(\lambda)}$ is a global minimizer, over the whole parameter space, of
  \[
    \Theta\longmapsto
    \frac{\mathcal L_{\tau(t+1)}(c_{\lambda,r}\Theta)}
         {\lambda c_{\lambda,r}^{2}}
    +\bigl\|\Theta-\widehat\Theta_t^{(\lambda)}\bigr\|^{2}.
  \] -/)
  (proof := /-- By $0<\lambda<1$, one has $1<1/\lambda$ and hence
  $\log(1/\lambda)>0$.  Thus the factor $c_{\lambda,r}$ of
  \cref{def:rescaling-factor} is positive.  For arbitrary parameters $\Theta_0$ and $U$, the
  definition in \cref{def:squared-displacement} and homogeneity of the Euclidean norm give
  \[
    \bigl\|U-c_{\lambda,r}^{-1}\Theta_0\bigr\|^2
    =\frac{\bigl\|c_{\lambda,r}U-\Theta_0\bigr\|^2}{c_{\lambda,r}^2}.
  \]
  Expanding \cref{def:regularized-step-objective, def:scaled-step-objective} therefore yields

  \[
    G_{\lambda,r,c_{\lambda,r}^{-1}\Theta_0}(U)
    =\frac{F_{\lambda,\Theta_0}(c_{\lambda,r}U)}
           {\lambda c_{\lambda,r}^2}.
  \]
  By \cref{def:regularized-continual-run}, the next unscaled iterate minimizes
  $F_{\lambda,\Theta_t^{(\lambda)}}$ globally.  Apply this inequality to
  $c_{\lambda,r}U$, divide by the positive number $\lambda c_{\lambda,r}^2$, and use
  $c_{\lambda,r}(c_{\lambda,r}^{-1}\Theta_{t+1}^{(\lambda)})
  =\Theta_{t+1}^{(\lambda)}$.  With the scaled iterates from
  \cref{def:scaled-regularized-iterate}, the resulting inequality states exactly that
  $\widehat\Theta_{t+1}^{(\lambda)}$ minimizes the scaled objective. -/)
  (title := /-- Rescaling preserves the regularized minimizer -/)
  (latexEnv := "lemma")]
lemma rescaled_regularized_step_is_minimizer {Input : Type*} {p M : ℕ} {r reg : ℝ}
    {model : Input → cl_parameter_space p → ℝ} {tasks : Fin M → cl_task Input}
    {taskOrder : ℕ → Fin M} (run : regularized_continual_run model tasks taskOrder)
    (hr : 0 < r) (hregpos : 0 < reg) (hregone : reg < 1) (t : ℕ) :
    IsMinOn
      (scaled_step_objective model (tasks (taskOrder (t + 1))) reg r
        (scaled_regularized_iterate run reg r t))
      Set.univ (scaled_regularized_iterate run reg r (t + 1)) := by
  have hinv : 1 < 1 / reg := by
    apply (lt_div_iff₀ hregpos).2
    simpa using hregone
  have hc : 0 < rescaling_factor reg r := by
    unfold rescaling_factor
    exact Real.rpow_pos_of_pos (Real.log_pos hinv) (1 / r)
  have hdisplacement (θ₀ θ : cl_parameter_space p) :
      squared_displacement ((rescaling_factor reg r)⁻¹ • θ₀) θ =
        squared_displacement θ₀ (rescaling_factor reg r • θ) /
          (rescaling_factor reg r) ^ 2 := by
    unfold squared_displacement
    rw [show θ - (rescaling_factor reg r)⁻¹ • θ₀ =
        (rescaling_factor reg r)⁻¹ • (rescaling_factor reg r • θ - θ₀) by
      simp [smul_sub, smul_smul, hc.ne']]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc]
    field_simp [hc.ne']
  have hobjective (θ₀ θ : cl_parameter_space p) :
      scaled_step_objective model (tasks (taskOrder (t + 1))) reg r
          ((rescaling_factor reg r)⁻¹ • θ₀) θ =
        regularized_step_objective model (tasks (taskOrder (t + 1))) reg θ₀
            (rescaling_factor reg r • θ) /
          (reg * (rescaling_factor reg r) ^ 2) := by
    unfold scaled_step_objective regularized_step_objective
    rw [hdisplacement]
    field_simp [hregpos.ne', hc.ne']
    <;> ring
  intro θ _
  simp only [scaled_regularized_iterate]
  change
    scaled_step_objective model (tasks (taskOrder (t + 1))) reg r
        ((rescaling_factor reg r)⁻¹ • run.iterate reg t)
        ((rescaling_factor reg r)⁻¹ • run.iterate reg (t + 1)) ≤
      scaled_step_objective model (tasks (taskOrder (t + 1))) reg r
        ((rescaling_factor reg r)⁻¹ • run.iterate reg t) θ
  rw [hobjective, hobjective]
  apply (div_le_div_iff_of_pos_right (mul_pos hregpos (sq_pos_of_pos hc))).2
  simpa [smul_smul, hc.ne'] using
    run.step_is_minimizer reg hregpos t (Set.mem_univ (rescaling_factor reg r • θ))

@[blueprint "lem:scaled-iterates-converge-to-projection-prefix"
  (statement := /-- Let $r>0$, and let $f$ be an $r$-positively homogeneous model such that
  $\Theta\mapsto f(x;\Theta)$ is continuous for every input $x$.  Suppose that every individual
  feasible margin set is nonempty, and fix a regularized continual-learning run, a task ordering,
  and a positive sequence $(\lambda_j)$ converging to zero.  For every iteration $t$, the scaled
  regularized iterates admit a subsequence converging to the terminal point of a sequential
  margin-projection prefix of length $t$. -/)
  (proof := /-- We argue by induction on $t$.  For $t=0$, use the identity subsequence and the
  constant zero sequence; the initial condition in the regularized run and
  \cref{def:scaled-regularized-iterate, def:is-sequential-projection-prefix} give the required
  convergence and prefix condition.

  For the induction step, first restrict to the subsequence supplied at time $t$, and denote its
  regularization strengths by $\lambda_j$, its scaled time-$t$ iterates by $a_j$, and its scaled
  time-$(t+1)$ iterates by $u_j$.  Put
  $L_j=\log(1/\lambda_j)$ and $c_j=c_{\lambda_j,r}$.  Positivity and convergence of
  $(\lambda_j)$ imply $L_j\to+\infty$; hence $c_j\to+\infty$, and the definition in
  \cref{def:rescaling-factor} gives $c_j^r=L_j$ eventually.

  Choose a feasible parameter $v$ for the current task.  By
  \cref{def:is-r-positively-homogeneous, def:task-feasible-set}, every signed margin of $c_jv$ is
  at least $L_j$.  The inequality $\log(1+e^{-x})\le e^{-x}$ and
  \cref{def:task-logistic-loss} therefore show
  \[
    0\le
    \frac{\mathcal L_{\tau(t+1)}(c_jv)}{\lambda_jc_j^2}
    \le c_j^{-2}\longrightarrow0.
  \]
  On the other hand, \cref{lem:rescaled-regularized-step-is-minimizer} and the nonnegativity of
  the logistic loss bound $\|u_j-a_j\|^2$ by the preceding quantity plus
  $\|v-a_j\|^2$; see \cref{def:scaled-step-objective, def:squared-displacement}.  Since
  $a_j$ converges, $(u_j)$ is eventually contained in one closed ball.  Closed balls in the
  finite-dimensional Euclidean parameter space are compact, so a further strictly increasing
  subsequence of $(u_j)$ converges to some $u$.

  We next prove $u$ feasible.  If a fixed signed margin of $u$ were smaller than $1$, continuity
  would give numbers $0<q<1$ such that the corresponding margins of the convergent subsequence
  are eventually smaller than $q$.  Its logistic summand is then bounded below by
  $\tfrac12e^{-qL_j}$.  The elementary estimate
  $\log L\le 2\sqrt L$ for $L>0$ shows that, eventually,
  $c_j^2\le e^{(1-q)L_j/2}$.  Consequently the normalized logistic loss of $u_j$ is at least
  \[
    \frac{e^{(1-q)L_j/2}}{2n_{\tau(t+1)}},
  \]
  which tends to $+\infty$.  This contradicts the uniform upper bound furnished by the minimizer
  comparison with $v$.  Thus every signed margin of $u$ is at least $1$.

  Finally, let $w$ be any feasible parameter for the current task.  The same feasible-point
  estimate makes its normalized logistic term tend to zero.  Compare $u_j$ with $w$ in the
  minimizer inequality, discard the nonnegative logistic term at $u_j$, and pass to the limit.
  Continuity of the squared norm yields
  \[
    \|u-\bar\Theta_t\|^2\le\|w-\bar\Theta_t\|^2.
  \]
  Hence $u$ minimizes the squared displacement from the preceding projection over the current
  feasible set.  Updating the old sequence at time $t+1$ by $u$ gives a valid prefix according
  to \cref{def:is-sequential-projection-prefix}; composing the two strictly increasing
  subsequence maps gives the asserted convergence. -/)
  (title := /-- Scaled iterates approach sequential margin projections -/)
  (latexEnv := "lemma")]
lemma scaled_iterates_converge_to_projection_prefix {Input : Type*} {p M : ℕ} {r : ℝ}
    {model : Input → cl_parameter_space p → ℝ} {tasks : Fin M → cl_task Input}
    {taskOrder : ℕ → Fin M} (run : regularized_continual_run model tasks taskOrder)
    (hr : 0 < r) (hhom : is_r_positively_homogeneous r model)
    (hcontinuous : ∀ x, Continuous (model x))
    (hseparable : ∀ m, (task_feasible_set model (tasks m)).Nonempty)
    (t : ℕ) (regSeq : ℕ → ℝ) (hregpos : ∀ j, 0 < regSeq j)
    (hregzero : Tendsto regSeq atTop (nhds 0)) :
    ∃ φ : ℕ → ℕ, ∃ projected : ℕ → cl_parameter_space p,
      StrictMono φ ∧
        is_sequential_projection_prefix model tasks taskOrder t projected ∧
          Tendsto (fun j => scaled_regularized_iterate run (regSeq (φ j)) r t)
            atTop (nhds (projected t)) := by
  classical
  induction t with
  | zero =>
      refine ⟨id, fun _ => 0, strictMono_id, ?_, ?_⟩
      · constructor
        · rfl
        · intro s hs hst
          omega
      · simpa [scaled_regularized_iterate, run.initial] using
          (tendsto_const_nhds :
            Tendsto (fun _ : ℕ => (0 : cl_parameter_space p)) atTop (nhds 0))
  | succ t ih =>
      rcases ih with ⟨φ₀, projected₀, hφ₀, hprefix₀, hcenter₀⟩
      let lam : ℕ → ℝ := fun j => regSeq (φ₀ j)
      let center : ℕ → cl_parameter_space p := fun j =>
        scaled_regularized_iterate run (lam j) r t
      let next : ℕ → cl_parameter_space p := fun j =>
        scaled_regularized_iterate run (lam j) r (t + 1)
      let logScale : ℕ → ℝ := fun j => Real.log (1 / lam j)
      let scale : ℕ → ℝ := fun j => rescaling_factor (lam j) r
      have hlampos : ∀ j, 0 < lam j := fun j => hregpos (φ₀ j)
      have hlamzero : Tendsto lam atTop (nhds 0) := by
        change Tendsto (regSeq ∘ φ₀) atTop (nhds 0)
        exact hregzero.comp hφ₀.tendsto_atTop
      have hcenter : Tendsto center atTop (nhds (projected₀ t)) := by
        simpa [center, lam] using hcenter₀
      have hlamwithin : Tendsto lam atTop (nhdsWithin 0 (Set.Ioi 0)) := by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨hlamzero, Filter.Eventually.of_forall hlampos⟩
      have hlogScale : Tendsto logScale atTop atTop := by
        have hinv : Tendsto lam⁻¹ atTop atTop :=
          hlamwithin.inv_tendsto_nhdsGT_zero
        have hlog := Real.tendsto_log_atTop.comp hinv
        exact hlog.congr' (Filter.Eventually.of_forall fun j => by
          simp [logScale, div_eq_mul_inv])
      have hscale : Tendsto scale atTop atTop := by
        have hloglog := Real.tendsto_log_atTop.comp hlogScale
        have hmul := hloglog.atTop_mul_const (one_div_pos.mpr hr)
        have hexp := Real.tendsto_exp_atTop.comp hmul
        apply hexp.congr'
        filter_upwards [hlogScale.eventually (eventually_ge_atTop (1 : ℝ))] with j hj
        simp only [Function.comp_apply, scale, rescaling_factor]
        rw [Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hj)]
      let currentTask : cl_task Input := tasks (taskOrder (t + 1))
      rcases hseparable (taskOrder (t + 1)) with ⟨competitor, hcompetitor⟩
      have hloss_nonneg (θ : cl_parameter_space p) :
          0 ≤ task_logistic_loss model currentTask θ := by
        unfold task_logistic_loss
        apply div_nonneg
        · exact Finset.sum_nonneg fun i _ => Real.log_nonneg (by
            nlinarith [Real.exp_pos (-signed_margin model currentTask θ i)])
        · positivity
      have hscale_pow (j : ℕ) (hj : 0 < logScale j) :
          (scale j) ^ r = logScale j := by
        rw [show scale j = (logScale j) ^ (1 / r) by
          rfl]
        rw [← Real.rpow_mul (le_of_lt hj)]
        field_simp [hr.ne']
        simp
      have hfeasible_loss (θ : cl_parameter_space p)
          (hθ : θ ∈ task_feasible_set model currentTask) (j : ℕ)
          (hj : 0 < logScale j) :
          task_logistic_loss model currentTask (scale j • θ) ≤ lam j := by
        unfold task_logistic_loss
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (currentTask.sampleCount + 1 : ℕ))]
        calc
          ∑ i : Fin (currentTask.sampleCount + 1),
              Real.log (1 + Real.exp (-signed_margin model currentTask
                (scale j • θ) i)) ≤
              ∑ _i : Fin (currentTask.sampleCount + 1), lam j := by
                apply Finset.sum_le_sum
                intro i _
                have hmargin : logScale j ≤
                    signed_margin model currentTask (scale j • θ) i := by
                  have hhomogeneous := hhom (currentTask.feature i) θ (scale j)
                    (by
                      rw [show scale j = (logScale j) ^ (1 / r) by rfl]
                      exact Real.rpow_pos_of_pos hj (1 / r))
                  have hmarg : signed_margin model currentTask (scale j • θ) i =
                      (scale j) ^ r * signed_margin model currentTask θ i := by
                    unfold signed_margin
                    rw [hhomogeneous]
                    ring
                  rw [hmarg, hscale_pow j hj]
                  nlinarith [hθ i]
                calc
                  Real.log (1 + Real.exp (-signed_margin model currentTask
                    (scale j • θ) i)) ≤
                      (1 + Real.exp (-signed_margin model currentTask
                        (scale j • θ) i)) - 1 :=
                    Real.log_le_sub_one_of_pos (by positivity)
                  _ = Real.exp (-signed_margin model currentTask
                        (scale j • θ) i) := by ring
                  _ ≤ Real.exp (-logScale j) := Real.exp_le_exp.mpr (neg_le_neg hmargin)
                  _ = lam j := by
                    rw [show -logScale j = Real.log (lam j) by
                      simp [logScale, div_eq_mul_inv, (hlampos j).ne']]
                    exact Real.exp_log (hlampos j)
          _ = lam j * (currentTask.sampleCount + 1 : ℕ) := by
            simp [Finset.card_fin]
            ring
      let scaledLoss (j : ℕ) (θ : cl_parameter_space p) : ℝ :=
        task_logistic_loss model currentTask (scale j • θ) /
          (lam j * (scale j) ^ 2)
      have hinvscalezero : Tendsto scale⁻¹ atTop (nhds 0) :=
        hscale.inv_tendsto_atTop
      have hinvscaleSqzero : Tendsto (fun j => scale⁻¹ j ^ 2) atTop (nhds 0) := by
        simpa using hinvscalezero.pow 2
      have hfeasible_scaled_zero (θ : cl_parameter_space p)
          (hθ : θ ∈ task_feasible_set model currentTask) :
          Tendsto (fun j => scaledLoss j θ) atTop (nhds 0) := by
        apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
          hinvscaleSqzero
        · filter_upwards [hlogScale.eventually (eventually_ge_atTop (1 : ℝ))] with j hj
          unfold scaledLoss
          exact div_nonneg (hloss_nonneg _) (mul_nonneg (le_of_lt (hlampos j)) (sq_nonneg _))
        · filter_upwards [hlogScale.eventually (eventually_ge_atTop (1 : ℝ))] with j hj
          have hspos : 0 < scale j := by
            rw [show scale j = (logScale j) ^ (1 / r) by rfl]
            exact Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hj) (1 / r)
          unfold scaledLoss
          calc
            task_logistic_loss model currentTask (scale j • θ) /
                (lam j * scale j ^ 2) ≤ lam j / (lam j * scale j ^ 2) :=
              div_le_div_of_nonneg_right
                (hfeasible_loss θ hθ j (lt_of_lt_of_le zero_lt_one hj))
                (mul_nonneg (le_of_lt (hlampos j)) (sq_nonneg _))
            _ = (scale j)⁻¹ ^ 2 := by
              field_simp [(hlampos j).ne', hspos.ne']
      have hcompetitor_scaled_zero := hfeasible_scaled_zero competitor (by
        simpa [currentTask] using hcompetitor)
      have hcenter_bound : ∀ᶠ j in atTop,
          ‖center j‖ ≤ ‖projected₀ t‖ + 1 := by
        filter_upwards [hcenter.eventually (Metric.ball_mem_nhds _ zero_lt_one)] with j hj
        rw [dist_eq_norm] at hj
        have hnorm := norm_sub_norm_le (center j) (projected₀ t)
        nlinarith
      let radius : ℝ := ‖competitor‖ + 2 * ‖projected₀ t‖ + 3
      have hnext_bound : ∀ᶠ j in atTop, ‖next j‖ ≤ radius := by
        filter_upwards [hcenter_bound,
          (tendsto_order.1 hlamzero).2 1 zero_lt_one,
          hlogScale.eventually (eventually_ge_atTop (1 : ℝ)),
          hcompetitor_scaled_zero.eventually (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))]
            with j hcb hjlam hjlog hjloss
        have hspos : 0 < scale j := by
          rw [show scale j = (logScale j) ^ (1 / r) by rfl]
          exact Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hjlog) (1 / r)
        have hmin := rescaled_regularized_step_is_minimizer run hr (hlampos j) hjlam t
        have hineq := hmin (Set.mem_univ competitor)
        have hineq' :
            scaledLoss j (next j) + squared_displacement (center j) (next j) ≤
              scaledLoss j competitor + squared_displacement (center j) competitor := by
          simpa [scaledLoss, next, center, scale, currentTask,
            scaled_step_objective] using hineq
        have hnextloss : 0 ≤ scaledLoss j (next j) := by
          unfold scaledLoss
          exact div_nonneg (hloss_nonneg _)
            (mul_nonneg (le_of_lt (hlampos j)) (sq_nonneg _))
        have hsq : ‖next j - center j‖ ^ 2 ≤
            1 + ‖competitor - center j‖ ^ 2 := by
          unfold squared_displacement at hineq'
          nlinarith
        have hcompdist : ‖competitor - center j‖ ≤ ‖competitor‖ + ‖center j‖ :=
          norm_sub_le competitor (center j)
        have hdist : ‖next j - center j‖ ≤ ‖competitor - center j‖ + 1 := by
          by_contra hnot
          have hlt : ‖competitor - center j‖ + 1 < ‖next j - center j‖ :=
            lt_of_not_ge hnot
          have hprod : 0 <
              (‖next j - center j‖ - (‖competitor - center j‖ + 1)) *
                (‖next j - center j‖ + (‖competitor - center j‖ + 1)) :=
            mul_pos (sub_pos.mpr hlt) (by positivity)
          ring_nf at hprod
          nlinarith [norm_nonneg (competitor - center j)]
        have hnextnorm : ‖next j‖ ≤ ‖next j - center j‖ + ‖center j‖ := by
          calc
            ‖next j‖ = ‖(next j - center j) + center j‖ := by rw [sub_add_cancel]
            _ ≤ ‖next j - center j‖ + ‖center j‖ := norm_add_le _ _
        dsimp [radius]
        nlinarith
      let boundedSet : Set (cl_parameter_space p) := Metric.closedBall 0 radius
      letI : ProperSpace (cl_parameter_space p) := FiniteDimensional.proper ℝ _
      have hbounded := Metric.isBounded_closedBall (x := (0 : cl_parameter_space p)) (r := radius)
      have hevent : ∀ᶠ j in atTop, next j ∈ boundedSet := hnext_bound.mono fun j hj => by
        simpa [boundedSet, Metric.mem_closedBall, dist_zero_right] using hj
      have hfrequent : ∃ᶠ j in atTop, next j ∈ boundedSet := hevent.frequently
      have hcompact : IsCompact boundedSet := by
        simpa [boundedSet] using
          (isCompact_closedBall (0 : cl_parameter_space p) radius)
      rcases hcompact.isSeqCompact.subseq_of_frequently_in hfrequent with
        ⟨limit, _hlimitMem, ψ, hψ, hnextlimit⟩
      have hcenterlimit : Tendsto (center ∘ ψ) atTop (nhds (projected₀ t)) :=
        hcenter.comp hψ.tendsto_atTop
      let lossBound : ℝ := 1 + (‖competitor‖ + ‖projected₀ t‖ + 1) ^ 2
      have hnext_scaled_bounded : ∀ᶠ j in atTop,
          scaledLoss j (next j) ≤ lossBound := by
        filter_upwards [hcenter_bound,
          (tendsto_order.1 hlamzero).2 1 zero_lt_one,
          hcompetitor_scaled_zero.eventually
            (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))]
            with j hcb hjlam hjloss
        have hmin := rescaled_regularized_step_is_minimizer run hr (hlampos j) hjlam t
        have hineq := hmin (Set.mem_univ competitor)
        have hineq' :
            scaledLoss j (next j) + squared_displacement (center j) (next j) ≤
              scaledLoss j competitor + squared_displacement (center j) competitor := by
          simpa [scaledLoss, next, center, scale, currentTask,
            scaled_step_objective] using hineq
        have hcompdist : ‖competitor - center j‖ ≤ ‖competitor‖ + ‖center j‖ :=
          norm_sub_le competitor (center j)
        have hcompdist' : ‖competitor - center j‖ ≤
            ‖competitor‖ + ‖projected₀ t‖ + 1 := by linarith
        have hcompsq : ‖competitor - center j‖ ^ 2 ≤
            (‖competitor‖ + ‖projected₀ t‖ + 1) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hcompdist'
        unfold squared_displacement at hineq'
        dsimp [lossBound]
        nlinarith [sq_nonneg ‖next j - center j‖]
      have hnext_scaled_bounded_sub : ∀ᶠ j in atTop,
          scaledLoss (ψ j) (next (ψ j)) ≤ lossBound :=
        hψ.tendsto_atTop.eventually hnext_scaled_bounded
      have hlimit_feasible : limit ∈ task_feasible_set model currentTask := by
        intro i
        by_contra hbad
        have hmarglt : signed_margin model currentTask limit i < 1 :=
          lt_of_not_ge hbad
        let marginLimit : ℝ := signed_margin model currentTask limit i
        let q : ℝ := (max marginLimit 0 + 1) / 2
        let b : ℝ := 1 - q
        have hqpos : 0 < q := by
          dsimp [q]
          nlinarith [le_max_right marginLimit 0]
        have hqlt : q < 1 := by
          have hmaxlt : max marginLimit 0 < 1 := max_lt hmarglt zero_lt_one
          dsimp [q]
          nlinarith
        have hbpos : 0 < b := by dsimp [b]; linarith
        have hmarginLimitlt : marginLimit < q := by
          have hmle : marginLimit ≤ max marginLimit 0 := le_max_left _ _
          dsimp [q]
          nlinarith [hqlt]
        have hmargin_cont : Continuous (fun θ : cl_parameter_space p =>
            signed_margin model currentTask θ i) := by
          unfold signed_margin
          exact continuous_const.mul (hcontinuous (currentTask.feature i))
        have hmargin_tendsto : Tendsto
            (fun j => signed_margin model currentTask (next (ψ j)) i) atTop
            (nhds marginLimit) := by
          simpa [marginLimit, Function.comp_def] using
            hmargin_cont.continuousAt.tendsto.comp hnextlimit
        have hmargin_event : ∀ᶠ j in atTop,
            signed_margin model currentTask (next (ψ j)) i < q :=
          (tendsto_order.1 hmargin_tendsto).2 q hmarginLimitlt
        have hlogsub : Tendsto (logScale ∘ ψ) atTop atTop :=
          hlogScale.comp hψ.tendsto_atTop
        have hexpTop : Tendsto
            (fun j => Real.exp ((b / 2) * logScale (ψ j))) atTop atTop := by
          have hmul := hlogsub.const_mul_atTop (by positivity : 0 < b / 2)
          simpa [Function.comp_def] using Real.tendsto_exp_atTop.comp hmul
        have hexpLarge : ∀ᶠ j in atTop,
            2 * (currentTask.sampleCount + 1 : ℕ) * lossBound <
              Real.exp ((b / 2) * logScale (ψ j)) :=
          hexpTop.eventually (eventually_gt_atTop _)
        have hlogLarge : ∀ᶠ j in atTop,
            max 1 ((8 / (r * b)) ^ 2) ≤ logScale (ψ j) :=
          hlogsub.eventually (eventually_ge_atTop _)
        have hbarrier : ∀ᶠ j in atTop,
            lossBound < scaledLoss (ψ j) (next (ψ j)) := by
          filter_upwards [hmargin_event, hexpLarge, hlogLarge] with j hjmargin hjexp hjlog
          have hLpos : 0 < logScale (ψ j) := lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) hjlog)
          have hscalePos : 0 < scale (ψ j) := by
            rw [show scale (ψ j) = (logScale (ψ j)) ^ (1 / r) by rfl]
            exact Real.rpow_pos_of_pos hLpos (1 / r)
          have hmarginScale : signed_margin model currentTask
              (scale (ψ j) • next (ψ j)) i =
                logScale (ψ j) * signed_margin model currentTask (next (ψ j)) i := by
            have hh := hhom (currentTask.feature i) (next (ψ j)) (scale (ψ j)) hscalePos
            unfold signed_margin
            rw [hh, hscale_pow (ψ j) hLpos]
            ring
          have hqexp : Real.exp (-q * logScale (ψ j)) ≤
              Real.exp (-signed_margin model currentTask
                (scale (ψ j) • next (ψ j)) i) := by
            apply Real.exp_le_exp.mpr
            rw [hmarginScale]
            nlinarith
          have hqexp_le_one : Real.exp (-q * logScale (ψ j)) ≤ 1 := by
            rw [← Real.exp_zero]
            apply Real.exp_le_exp.mpr
            nlinarith [mul_pos hqpos hLpos]
          have hlog_lower : Real.exp (-q * logScale (ψ j)) / 2 ≤
              Real.log (1 + Real.exp (-signed_margin model currentTask
                (scale (ψ j) • next (ψ j)) i)) := by
            let z := Real.exp (-q * logScale (ψ j))
            have hzpos : 0 < z := Real.exp_pos _
            have hzlog : z / (1 + z) ≤ Real.log (1 + z) := by
              have hbase := Real.one_sub_inv_le_log_of_pos (by positivity : 0 < 1 + z)
              convert hbase using 1 <;> field_simp <;> ring
            have hzhalf : z / 2 ≤ z / (1 + z) := by
              apply div_le_div_of_nonneg_left (le_of_lt hzpos) (by positivity)
              nlinarith [hqexp_le_one]
            have hlogmono : Real.log (1 + z) ≤
                Real.log (1 + Real.exp (-signed_margin model currentTask
                  (scale (ψ j) • next (ψ j)) i)) := by
              apply Real.strictMonoOn_log.monotoneOn
              · change 0 < 1 + z
                positivity
              · change 0 < 1 + Real.exp (-signed_margin model currentTask
                    (scale (ψ j) • next (ψ j)) i)
                positivity
              · linarith [hqexp]
            exact hzhalf.trans (hzlog.trans hlogmono)
          have hlog_rpow : Real.log (logScale (ψ j)) ≤
              (logScale (ψ j)) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
            Real.log_le_rpow_div (le_of_lt hLpos) (by norm_num)
          have hsqrt : (logScale (ψ j)) ^ (1 / 2 : ℝ) =
              Real.sqrt (logScale (ψ j)) := by
            simpa using (Real.sqrt_eq_rpow (logScale (ψ j))).symm
          have hthreshold : (8 / (r * b)) ^ 2 ≤ logScale (ψ j) :=
            le_trans (le_max_right _ _) hjlog
          have hrootlower : 8 / (r * b) ≤ Real.sqrt (logScale (ψ j)) := by
            apply (Real.le_sqrt (by positivity) (le_of_lt hLpos)).2
            exact hthreshold
          have hsqrtSq := Real.sq_sqrt (le_of_lt hLpos)
          have hscaleSqBound : scale (ψ j) ^ 2 ≤
              Real.exp ((b / 2) * logScale (ψ j)) := by
            rw [show scale (ψ j) = (logScale (ψ j)) ^ (1 / r) by rfl]
            rw [Real.rpow_def_of_pos hLpos]
            rw [pow_two, ← Real.exp_add]
            apply Real.exp_le_exp.mpr
            rw [hsqrt] at hlog_rpow
            norm_num at hlog_rpow
            field_simp [hr.ne', hbpos.ne'] at hrootlower
            have hmulroot := mul_le_mul_of_nonneg_right hrootlower
              (Real.sqrt_nonneg (logScale (ψ j)))
            have hmulroot' : 8 * Real.sqrt (logScale (ψ j)) ≤
                r * b * logScale (ψ j) := by
              calc
                8 * Real.sqrt (logScale (ψ j)) ≤
                    r * b * Real.sqrt (logScale (ψ j)) *
                      Real.sqrt (logScale (ψ j)) := hmulroot
                _ = (r * b) * (Real.sqrt (logScale (ψ j))) ^ 2 := by ring
                _ = r * b * logScale (ψ j) := by rw [hsqrtSq]
            field_simp [hr.ne', hbpos.ne']
            nlinarith [hmulroot']
          have hlamExp : lam (ψ j) = Real.exp (-logScale (ψ j)) := by
            rw [show -logScale (ψ j) = Real.log (lam (ψ j)) by
              simp [logScale, div_eq_mul_inv, (hlampos (ψ j)).ne']]
            exact (Real.exp_log (hlampos (ψ j))).symm
          have hsummand_le_loss :
              Real.log (1 + Real.exp (-signed_margin model currentTask
                (scale (ψ j) • next (ψ j)) i)) /
                  (currentTask.sampleCount + 1 : ℕ) ≤
                    task_logistic_loss model currentTask
                      (scale (ψ j) • next (ψ j)) := by
            unfold task_logistic_loss
            apply div_le_div_of_nonneg_right _ (by positivity)
            refine Finset.single_le_sum (s := Finset.univ)
              (f := fun k : Fin (currentTask.sampleCount + 1) =>
                Real.log (1 + Real.exp (-signed_margin model currentTask
                  (scale (ψ j) • next (ψ j)) k))) ?_ (Finset.mem_univ i)
            · intro k _
              apply Real.log_nonneg
              nlinarith [Real.exp_pos
                (-signed_margin model currentTask (scale (ψ j) • next (ψ j)) k)]
          unfold scaledLoss
          have hdenpos : 0 < lam (ψ j) * scale (ψ j) ^ 2 :=
            mul_pos (hlampos _) (sq_pos_of_pos hscalePos)
          have hratio : Real.exp ((b / 2) * logScale (ψ j)) /
                (2 * (currentTask.sampleCount + 1 : ℕ)) ≤
              task_logistic_loss model currentTask (scale (ψ j) • next (ψ j)) /
                (lam (ψ j) * scale (ψ j) ^ 2) := by
            apply (le_div_iff₀ hdenpos).2
            rw [hlamExp]
            have hdenBound : Real.exp (-logScale (ψ j)) * scale (ψ j) ^ 2 ≤
                Real.exp (-(q) * logScale (ψ j)) /
                  Real.exp ((b / 2) * logScale (ψ j)) := by
              calc
                Real.exp (-logScale (ψ j)) * scale (ψ j) ^ 2 ≤
                    Real.exp (-logScale (ψ j)) *
                      Real.exp ((b / 2) * logScale (ψ j)) := by gcongr
                _ = Real.exp (-(q) * logScale (ψ j)) /
                      Real.exp ((b / 2) * logScale (ψ j)) := by
                    rw [← Real.exp_add, ← Real.exp_sub]
                    congr 1
                    dsimp [b]
                    ring
            have hlossLower : Real.exp (-q * logScale (ψ j)) /
                  (2 * (currentTask.sampleCount + 1 : ℕ)) ≤
                task_logistic_loss model currentTask
                  (scale (ψ j) • next (ψ j)) := by
              calc
                _ = (Real.exp (-q * logScale (ψ j)) / 2) /
                    (currentTask.sampleCount + 1 : ℕ) := by ring
                _ ≤ Real.log (1 + Real.exp (-signed_margin model currentTask
                      (scale (ψ j) • next (ψ j)) i)) /
                    (currentTask.sampleCount + 1 : ℕ) := by gcongr
                _ ≤ _ := hsummand_le_loss
            have hexppos := Real.exp_pos ((b / 2) * logScale (ψ j))
            calc
              Real.exp ((b / 2) * logScale (ψ j)) /
                    (2 * (currentTask.sampleCount + 1 : ℕ)) *
                  (Real.exp (-logScale (ψ j)) * scale (ψ j) ^ 2) =
                  Real.exp ((b / 2) * logScale (ψ j)) *
                    (Real.exp (-logScale (ψ j)) * scale (ψ j) ^ 2) /
                  (2 * (currentTask.sampleCount + 1 : ℕ)) := by ring
              _ ≤
                  Real.exp ((b / 2) * logScale (ψ j)) *
                    (Real.exp (-q * logScale (ψ j)) /
                      Real.exp ((b / 2) * logScale (ψ j))) /
                    (2 * (currentTask.sampleCount + 1 : ℕ)) := by gcongr
              _ = Real.exp (-q * logScale (ψ j)) /
                    (2 * (currentTask.sampleCount + 1 : ℕ)) := by
                  field_simp [hexppos.ne']
              _ ≤ _ := hlossLower
          have htwoN : 0 < (2 * (currentTask.sampleCount + 1 : ℕ) : ℝ) := by
            positivity
          have hboundRatio : lossBound <
              Real.exp ((b / 2) * logScale (ψ j)) /
                (2 * (currentTask.sampleCount + 1 : ℕ)) := by
            apply (lt_div_iff₀ htwoN).2
            simpa [Nat.cast_add, Nat.cast_one, mul_comm, mul_left_comm, mul_assoc] using hjexp
          exact hboundRatio.trans_le hratio
        rcases (hbarrier.and hnext_scaled_bounded_sub).exists with ⟨j, hjbar, hjbound⟩
        exact (not_lt_of_ge hjbound) hjbar
      have hlimit_minimizes : IsMinOn (squared_displacement (projected₀ t))
          (task_feasible_set model currentTask) limit := by
        intro θ hθ
        have hleft : Tendsto
            (fun j => squared_displacement (center (ψ j)) (next (ψ j))) atTop
            (nhds (squared_displacement (projected₀ t) limit)) := by
          unfold squared_displacement
          simpa [Function.comp_def] using (hnextlimit.sub hcenterlimit).norm.pow 2
        have hrightDist : Tendsto
            (fun j => squared_displacement (center (ψ j)) θ) atTop
            (nhds (squared_displacement (projected₀ t) θ)) := by
          unfold squared_displacement
          simpa [Function.comp_def] using
            (tendsto_const_nhds.sub hcenterlimit).norm.pow 2
        have hrightLoss : Tendsto (fun j => scaledLoss (ψ j) θ) atTop (nhds 0) :=
          (hfeasible_scaled_zero θ hθ).comp hψ.tendsto_atTop
        have hright : Tendsto
            (fun j => scaledLoss (ψ j) θ +
              squared_displacement (center (ψ j)) θ) atTop
            (nhds (squared_displacement (projected₀ t) θ)) := by
          simpa using hrightLoss.add hrightDist
        have hlamSubzero : Tendsto (lam ∘ ψ) atTop (nhds 0) :=
          hlamzero.comp hψ.tendsto_atTop
        have hineqEvent : ∀ᶠ j in atTop,
            squared_displacement (center (ψ j)) (next (ψ j)) ≤
              scaledLoss (ψ j) θ + squared_displacement (center (ψ j)) θ := by
          filter_upwards [(tendsto_order.1 hlamSubzero).2 1 zero_lt_one] with j hjlam
          have hmin := rescaled_regularized_step_is_minimizer run hr
            (hlampos (ψ j)) hjlam t
          have hineq := hmin (Set.mem_univ θ)
          have hineq' : scaledLoss (ψ j) (next (ψ j)) +
                squared_displacement (center (ψ j)) (next (ψ j)) ≤
              scaledLoss (ψ j) θ + squared_displacement (center (ψ j)) θ := by
            simpa [scaledLoss, next, center, scale, currentTask,
              scaled_step_objective] using hineq
          have hnextloss : 0 ≤ scaledLoss (ψ j) (next (ψ j)) := by
            unfold scaledLoss
            exact div_nonneg (hloss_nonneg _)
              (mul_nonneg (le_of_lt (hlampos _)) (sq_nonneg _))
          linarith
        exact le_of_tendsto_of_tendsto hleft hright hineqEvent
      let projected : ℕ → cl_parameter_space p :=
        Function.update projected₀ (t + 1) limit
      have hprefix : is_sequential_projection_prefix model tasks taskOrder
          (t + 1) projected := by
        constructor
        · simp [projected, Function.update, (by omega : (0 : ℕ) ≠ t + 1), hprefix₀.1]
        · intro s hspos hsle
          by_cases hseq : s = t + 1
          · subst s
            have htne : t ≠ t + 1 := by omega
            simpa [projected, currentTask, Function.update, htne] using
              And.intro hlimit_feasible hlimit_minimizes
          · have hst : s ≤ t := by omega
            have hsold := hprefix₀.2 s hspos hst
            have hprevne : s - 1 ≠ t + 1 := by omega
            simpa [projected, Function.update, hseq, hprevne] using hsold
      refine ⟨φ₀ ∘ ψ, projected, hφ₀.comp hψ, hprefix, ?_⟩
      simpa [next, lam, projected, Function.comp_def] using hnextlimit

@[blueprint "lem:scaled-limit-yields-directional-limit"
  (statement := /-- Let $p\in\mathbb N$ and $r>0$.  Let $(\lambda_j)_{j\in\mathbb N}$ be a
  positive real sequence converging to zero, let $\phi\colon\mathbb N\to\mathbb N$ be strictly
  increasing, and let $(\Theta_j)_{j\in\mathbb N}$ be a sequence in $\mathbb R^p$.  If
  $c_{\lambda_{\phi(j)},r}^{-1}\Theta_{\phi(j)}$ converges to a nonzero vector $\bar\Theta$,
  then the normalized directions of $\Theta_{\phi(j)}$ converge to the normalized direction of
  $\bar\Theta$. -/)
  (proof := /-- A strictly increasing map $\phi\colon\mathbb N\to\mathbb N$ tends to infinity.
  Hence positivity and convergence of $(\lambda_j)$ imply that eventually
  $0<\lambda_{\phi(j)}<1$.  The definition in \cref{def:rescaling-factor} and positivity of the
  logarithm on $(1,\infty)$ then give $c_{\lambda_{\phi(j)},r}>0$ eventually.  By
  \cref{def:normalized-direction}, normalization is the product of the inverse norm and the vector.
  Continuity of the norm, inversion at the nonzero number $\lVert\bar\Theta\rVert$, and scalar
  multiplication therefore show that the normalized scaled vectors converge to the normalized
  direction of $\bar\Theta$.  Finally, multiplication by the positive scalar
  $c_{\lambda_{\phi(j)},r}^{-1}$ does not change a normalized direction, so eventual equality of
  the normalized scaled and unscaled vectors yields the conclusion. -/)
  (title := /-- Scaled convergence implies convergence in direction -/)
  (latexEnv := "lemma")]
lemma scaled_limit_yields_directional_limit {p : ℕ} {r : ℝ} (hr : 0 < r)
    (regSeq : ℕ → ℝ) (hregpos : ∀ j, 0 < regSeq j)
    (hregzero : Tendsto regSeq atTop (nhds 0))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (θseq : ℕ → cl_parameter_space p)
    (limit : cl_parameter_space p) (hlimit : limit ≠ 0)
    (hscaled : Tendsto
      (fun j => (rescaling_factor (regSeq (φ j)) r)⁻¹ • θseq (φ j))
      atTop (nhds limit)) :
    Tendsto (fun j => normalized_direction (θseq (φ j)))
      atTop (nhds (normalized_direction limit)) := by
  have hreg_lt : ∀ᶠ j in atTop, regSeq (φ j) < 1 :=
    hφ.tendsto_atTop.eventually (hregzero.eventually (Iio_mem_nhds zero_lt_one))
  have hscale_pos : ∀ᶠ j in atTop, 0 < rescaling_factor (regSeq (φ j)) r := by
    filter_upwards [hreg_lt] with j hj
    exact
      Real.rpow_pos_of_pos
        (Real.log_pos ((one_lt_div (hregpos (φ j))).2 hj)) _
  have hnormalized_scaled :
      Tendsto
        (fun j =>
          normalized_direction
            ((rescaling_factor (regSeq (φ j)) r)⁻¹ • θseq (φ j)))
        atTop (nhds (normalized_direction limit)) := by
    unfold normalized_direction
    exact (hscaled.norm.inv₀ (norm_ne_zero_iff.mpr hlimit)).smul hscaled
  refine hnormalized_scaled.congr' ?_
  filter_upwards [hscale_pos] with j hj
  simp [normalized_direction, norm_smul, abs_of_pos hj, smul_smul]
  rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hj), mul_one]

@[blueprint "thm:weakly-regularized-cl-to-sequential-margin-projections"
  (statement := /-- Let $\mathcal X$ be a type, let $p,M,k\in\mathbb N$, and let $r>0$.
  Let $f\colon\mathcal X\to\mathbb R^p\to\mathbb R$ be an $r$-positively homogeneous model, let
  $(\mathcal T_m)_{m\in\operatorname{Fin}(M)}$ be a family of binary-classification tasks, and
  let $\tau\colon\mathbb N\to\operatorname{Fin}(M)$ be a task ordering.  Assume that
  $\Theta\mapsto f(x;\Theta)$ is continuous for every input $x$ and that every task has a
  nonempty feasible margin set.  Fix a regularized continual-learning run for $f$, the task
  family, and $\tau$, trained with logistic loss.  For every $t\in\mathbb N$ satisfying
  $1\le t\le k$ and every positive sequence $(\lambda_j)_{j\in\mathbb N}$ converging to zero,
  there exist a strictly increasing map $\phi\colon\mathbb N\to\mathbb N$ and a sequence
  $(\bar\Theta_s)_{s\in\mathbb N}$ with $\bar\Theta_0=0$ such that, for each $1\le s\le t$,
  $\bar\Theta_s$ minimizes $\|\Theta-\bar\Theta_{s-1}\|^2$ over the feasible margin set of
  $\mathcal T_{\tau(s)}$, and
  $\Theta_t^{(\lambda_{\phi(j)})}/\|\Theta_t^{(\lambda_{\phi(j)})}\|$ converges to
  $\bar\Theta_t/\|\bar\Theta_t\|$ as $j\to\infty$. -/)
  (proof := /-- Apply \cref{lem:scaled-iterates-converge-to-projection-prefix} to the prescribed
  regularization sequence and iteration.  This yields a strictly increasing map $\phi$, a valid
  sequential projection prefix $(\bar\Theta_s)$, and convergence of the scaled regularized
  iterates to $\bar\Theta_t$.  Since $1\le t$, the prefix condition in
  \cref{def:is-sequential-projection-prefix} places $\bar\Theta_t$ in the feasible set of the
  task indexed by $\tau(t)$.  Hence \cref{lem:feasible-parameter-nonzero} implies that
  $\bar\Theta_t\ne0$.  After unfolding the scaling in
  \cref{def:scaled-regularized-iterate}, apply
  \cref{lem:scaled-limit-yields-directional-limit} to obtain the asserted convergence of
  normalized directions. -/)
  (title := /-- Weakly regularized continual learning converges to sequential margin projections -/)
  (latexEnv := "theorem")]
theorem weakly_regularized_cl_to_sequential_margin_projections
    {Input : Type*} {p M k : ℕ} {r : ℝ}
    {model : Input → cl_parameter_space p → ℝ} {tasks : Fin M → cl_task Input}
    {taskOrder : ℕ → Fin M} (run : regularized_continual_run model tasks taskOrder)
    (hr : 0 < r) (hhom : is_r_positively_homogeneous r model)
    (hcontinuous : ∀ x, Continuous (model x))
    (hseparable : ∀ m, (task_feasible_set model (tasks m)).Nonempty)
    (t : ℕ) (htpos : 1 ≤ t) (htk : t ≤ k)
    (regSeq : ℕ → ℝ) (hregpos : ∀ j, 0 < regSeq j)
    (hregzero : Tendsto regSeq atTop (nhds 0)) :
    ∃ φ : ℕ → ℕ, ∃ projected : ℕ → cl_parameter_space p,
      StrictMono φ ∧
        is_sequential_projection_prefix model tasks taskOrder t projected ∧
          Tendsto (fun j => normalized_direction (run.iterate (regSeq (φ j)) t))
            atTop (nhds (normalized_direction (projected t))) := by
  rcases scaled_iterates_converge_to_projection_prefix run hr hhom hcontinuous hseparable t
      regSeq hregpos hregzero with ⟨φ, projected, hφ, hprefix, hscaled⟩
  refine ⟨φ, projected, hφ, hprefix, ?_⟩
  have hlimit : projected t ≠ 0 :=
    feasible_parameter_nonzero (tasks (taskOrder t)) hr hhom
      ((hprefix.2 t htpos le_rfl).1)
  apply scaled_limit_yields_directional_limit hr regSeq hregpos hregzero φ hφ
    (fun n => run.iterate (regSeq n) t) (projected t) hlimit
  simpa [scaled_regularized_iterate] using hscaled

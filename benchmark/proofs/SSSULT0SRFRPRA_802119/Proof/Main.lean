import Architect
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators

@[blueprint "def:td-vector"
  (statement := /-- For $d\in\mathbb{N}$, the parameter space is the real coordinate space $\mathbb{R}^d$, represented as functions on $\operatorname{Fin}(d)$. -/)
  (title := /-- TD parameter vectors -/)
  (latexEnv := "definition")]
abbrev td_vector (d : ℕ) := Fin d → ℝ

@[blueprint "def:td-euclidean-norm"
  (statement := /-- For $v\in\mathbb{R}^d$, define its Euclidean norm by $\|v\|_2=(\sum_{i=1}^d v_i^2)^{1/2}$. -/)
  (title := /-- Euclidean norm -/)
  (latexEnv := "definition")]
noncomputable def td_euclidean_norm {d : ℕ} (v : td_vector d) : ℝ :=
  Real.sqrt (∑ i, (v i) ^ 2)

@[blueprint "def:td-model"
  (statement := /-- A finite linear TD model consists of a transition probability mass function $P(s,\cdot)$, a stationary probability mass function $\pi$, a reward $r(s,s')$, a feature vector $\phi(s)\in\mathbb{R}^d$, and a discount $\gamma\in[0,1)$.  The real transition matrix is primitive, which is the finite-state formulation of irreducibility and aperiodicity; $\pi$ is stationary; and the feature map has full column rank. -/)
  (title := /-- Finite ergodic linear TD model -/)
  (latexEnv := "definition")]
structure td_model (n d : ℕ) where
  transition : Fin n → PMF (Fin n)
  stationary : PMF (Fin n)
  reward : Fin n → Fin n → ℝ
  feature : Fin n → td_vector d
  discount : ℝ
  discount_nonneg : 0 ≤ discount
  discount_lt_one : discount < 1
  transition_primitive :
    Matrix.IsPrimitive (fun i j : Fin n => (transition i j).toReal)
  stationary_eq : ∀ j, ∑ i, (stationary i).toReal * (transition i j).toReal =
    (stationary j).toReal
  feature_full_rank :
    Function.Injective (fun θ : td_vector d => fun s => (feature s) ⬝ᵥ θ)

@[blueprint "def:td-prefix-kernel"
  (statement := /-- At time $t$, the next-state kernel reads the last state of a trajectory prefix $(s_0,\ldots,s_t)$ and returns the transition law $P(s_t,\cdot)$. -/)
  (title := /-- Markov next-state prefix kernel -/)
  (latexEnv := "definition")]
noncomputable def td_prefix_kernel {n d : ℕ} (M : td_model n d) (t : ℕ) :
    ProbabilityTheory.Kernel ((i : Finset.Iic t) → Fin n) (Fin n) :=
  ProbabilityTheory.Kernel.ofFunOfCountable fun x =>
    (M.transition (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure

@[blueprint "def:td-prefix-kernel-is-markov"
  (statement := /-- Every next-state prefix kernel in \cref{def:td-prefix-kernel} is a Markov kernel because each transition law is a probability mass function. -/)
  (title := /-- The prefix kernel is Markov -/)
  (latexEnv := "definition")]
instance td_prefix_kernel_is_markov {n d : ℕ} (M : td_model n d) (t : ℕ) :
    ProbabilityTheory.IsMarkovKernel (td_prefix_kernel M t) := by
  constructor
  intro x
  change MeasureTheory.IsProbabilityMeasure
    ((M.transition (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure)
  infer_instance

@[blueprint "def:td-markov-path-measure"
  (statement := /-- For an initial state $s_0$, the canonical path law is the Ionescu--Tulcea trajectory measure obtained from the point mass at $s_0$ and the prefix kernels in \cref{def:td-prefix-kernel}. -/)
  (title := /-- Canonical Markov path measure -/)
  (latexEnv := "definition")]
noncomputable def td_markov_path_measure {n d : ℕ} (M : td_model n d) (s0 : Fin n) :
    MeasureTheory.Measure (ℕ → Fin n) :=
  ProbabilityTheory.Kernel.trajMeasure (MeasureTheory.Measure.dirac s0)
    (fun t => td_prefix_kernel M t)

@[blueprint "def:td-transition-matrix"
  (statement := /-- The real transition matrix associated with a TD model is $P_{ss'}=P(s,\{s'\})$. -/)
  (title := /-- Real transition matrix -/)
  (latexEnv := "definition")]
noncomputable def td_transition_matrix {n d : ℕ} (M : td_model n d) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (M.transition i j).toReal

@[blueprint "def:td-sample-matrix"
  (statement := /-- For a transition $z=(s,s')$, define $A_z=\phi(s)(\phi(s)-\gamma\phi(s'))^\top$. -/)
  (title := /-- Sample TD matrix -/)
  (latexEnv := "definition")]
def td_sample_matrix {n d : ℕ} (M : td_model n d) (s s' : Fin n) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => M.feature s i * (M.feature s j - M.discount * M.feature s' j)

@[blueprint "def:td-sample-vector"
  (statement := /-- For a transition $z=(s,s')$, define $b_z=r(s,s')\phi(s)$. -/)
  (title := /-- Sample TD vector -/)
  (latexEnv := "definition")]
def td_sample_vector {n d : ℕ} (M : td_model n d) (s s' : Fin n) : td_vector d :=
  M.reward s s' • M.feature s

@[blueprint "def:td-update"
  (statement := /-- The TD increment at parameter $\theta$ and transition $(s,s')$ is $g(\theta,(s,s'))=b_{(s,s')}-A_{(s,s')}\theta$. -/)
  (title := /-- Sample TD increment -/)
  (latexEnv := "definition")]
def td_update {n d : ℕ} (M : td_model n d) (θ : td_vector d) (s s' : Fin n) :
    td_vector d :=
  td_sample_vector M s s' - Matrix.mulVec (td_sample_matrix M s s') θ

@[blueprint "def:td-population-matrix"
  (statement := /-- The population TD matrix is $A=\mathbb{E}_{s\sim\pi,\,s'\sim P(s,\cdot)}[A_{(s,s')}]$. -/)
  (title := /-- Population TD matrix -/)
  (latexEnv := "definition")]
noncomputable def td_population_matrix {n d : ℕ} (M : td_model n d) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ∑ s, ∑ s',
    (M.stationary s).toReal * (M.transition s s').toReal * td_sample_matrix M s s' i j

@[blueprint "def:td-population-vector"
  (statement := /-- The population TD vector is $b=\mathbb{E}_{s\sim\pi,\,s'\sim P(s,\cdot)}[b_{(s,s')}]$. -/)
  (title := /-- Population TD vector -/)
  (latexEnv := "definition")]
noncomputable def td_population_vector {n d : ℕ} (M : td_model n d) : td_vector d :=
  fun i => ∑ s, ∑ s',
    (M.stationary s).toReal * (M.transition s s').toReal * td_sample_vector M s s' i

@[blueprint "def:td-mean-update"
  (statement := /-- The stationary mean TD increment is $\bar g(\theta)=b-A\theta$. -/)
  (title := /-- Mean TD increment -/)
  (latexEnv := "definition")]
noncomputable def td_mean_update {n d : ℕ} (M : td_model n d) (θ : td_vector d) :
    td_vector d :=
  td_population_vector M - Matrix.mulVec (td_population_matrix M) θ

@[blueprint "def:td-fixed-point"
  (statement := /-- A vector $\theta^*$ is the TD fixed point when $A\theta^*=b$, equivalently $\bar g(\theta^*)=0$. -/)
  (title := /-- TD fixed point -/)
  (latexEnv := "definition")]
def td_fixed_point {n d : ℕ} (M : td_model n d) (θstar : td_vector d) : Prop :=
  Matrix.mulVec (td_population_matrix M) θstar = td_population_vector M

@[blueprint "def:td-iterates"
  (statement := /-- Given positive stepsizes $(\eta_t)$, an initial parameter $\theta_0$, and a state path $(s_t)$, define the unprojected TD iterates by $\theta_{t+1}=\theta_t+\eta_t g(\theta_t,(s_t,s_{t+1}))$. -/)
  (title := /-- Unprojected TD recursion -/)
  (latexEnv := "definition")]
noncomputable def td_iterates {n d : ℕ} (M : td_model n d) (η : ℕ → ℝ)
    (θ0 : td_vector d) : ℕ → (ℕ → Fin n) → td_vector d
  | 0, _ => θ0
  | t + 1, path =>
      td_iterates M η θ0 t path +
        η t • td_update M (td_iterates M η θ0 t path) (path t) (path (t + 1))

@[blueprint "def:td-stopped-iterates"
  (statement := /-- Fix a radius $R\in\mathbb R$.  Given a stepsize sequence $(\eta_t)$, an initial vector $\theta_0$, and a state path $(s_t)$, define the stopped TD recursion by $\widetilde\theta_0=\theta_0$ and
  \[
  \widetilde\theta_{t+1}=
  \begin{cases}
  \widetilde\theta_t+\eta_tg(\widetilde\theta_t,(s_t,s_{t+1})),&
    \|\widetilde\theta_t\|_2\leq R,\\
  \widetilde\theta_t,&\|\widetilde\theta_t\|_2>R.
  \end{cases}
  \]
  Thus the recursion is frozen from the first time at which its current iterate lies outside the closed ball of radius $R$. -/)
  (title := /-- Stopped TD recursion -/)
  (latexEnv := "definition")]
noncomputable def td_stopped_iterates {n d : ℕ} (M : td_model n d) (η : ℕ → ℝ)
    (θ0 : td_vector d) (R : ℝ) : ℕ → (ℕ → Fin n) → td_vector d
  | 0, _ => θ0
  | t + 1, path =>
      if td_euclidean_norm (td_stopped_iterates M η θ0 R t path) ≤ R then
        td_stopped_iterates M η θ0 R t path +
          η t • td_update M (td_stopped_iterates M η θ0 R t path)
            (path t) (path (t + 1))
      else
        td_stopped_iterates M η θ0 R t path

@[blueprint "def:td-stopped-stepsize"
  (statement := /-- For the stopped recursion in \cref{def:td-stopped-iterates}, define
  \[
  \widetilde\eta_t=
  \begin{cases}
  \eta_t,&\|\widetilde\theta_t\|_2\leq R,\\
  0,&\|\widetilde\theta_t\|_2>R.
  \end{cases}
  \]
  The stopped recursion consequently satisfies
  $\widetilde\theta_{t+1}=\widetilde\theta_t+widetilde\eta_t
  g(\widetilde\theta_t,(s_t,s_{t+1}))$. -/)
  (title := /-- Stopped TD stepsizes -/)
  (latexEnv := "definition")]
noncomputable def td_stopped_stepsize {n d : ℕ} (M : td_model n d) (η : ℕ → ℝ)
    (θ0 : td_vector d) (R : ℝ) (path : ℕ → Fin n) (t : ℕ) : ℝ :=
  if td_euclidean_norm (td_stopped_iterates M η θ0 R t path) ≤ R then η t else 0

@[blueprint "def:pr-step-mass"
  (statement := /-- For $T\geq 0$, set $S_T=\sum_{t=0}^{T-1}\eta_t$. -/)
  (title := /-- Cumulative stepsize -/)
  (latexEnv := "definition")]
def pr_step_mass (η : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, η t

@[blueprint "def:pr-average"
  (statement := /-- The Polyak--Ruppert average is $\bar\theta_T=S_T^{-1}\sum_{t=0}^{T-1}\eta_t\theta_t$. -/)
  (title := /-- Polyak--Ruppert average -/)
  (latexEnv := "definition")]
noncomputable def pr_average {d : ℕ} (η : ℕ → ℝ)
    (θ : ℕ → td_vector d) (T : ℕ) : td_vector d :=
  (pr_step_mass η T)⁻¹ • ∑ t ∈ Finset.range T, η t • θ t

@[blueprint "def:td-value"
  (statement := /-- The approximate value represented by $\theta$ is $V_\theta(s)=\phi(s)^\top\theta$. -/)
  (title := /-- Linear value approximation -/)
  (latexEnv := "definition")]
def td_value {n d : ℕ} (M : td_model n d) (θ : td_vector d) : Fin n → ℝ :=
  fun s => M.feature s ⬝ᵥ θ

@[blueprint "def:td-weighted-square"
  (statement := /-- For a state function $v$, define $\|v\|_D^2=\sum_s\pi(s)v(s)^2$. -/)
  (title := /-- Stationary weighted square norm -/)
  (latexEnv := "definition")]
noncomputable def td_weighted_square {n d : ℕ} (M : td_model n d) (v : Fin n → ℝ) : ℝ :=
  ∑ s, (M.stationary s).toReal * (v s) ^ 2

@[blueprint "def:td-dirichlet-energy"
  (statement := /-- For a state function $v$, define its Dirichlet energy by $\|v\|_{\mathrm{Dir}}^2=\frac12\sum_{s,s'}\pi(s)P(s,s')(v(s)-v(s'))^2$. -/)
  (title := /-- Dirichlet energy -/)
  (latexEnv := "definition")]
noncomputable def td_dirichlet_energy {n d : ℕ} (M : td_model n d)
    (v : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ s, ∑ s',
    (M.stationary s).toReal * (M.transition s s').toReal * (v s - v s') ^ 2

@[blueprint "def:td-potential"
  (statement := /-- Relative to the TD fixed point $\theta^*$, define $f(\theta)=(1-\gamma)\|V_\theta-V_{\theta^*}\|_D^2+\gamma\|V_\theta-V_{\theta^*}\|_{\mathrm{Dir}}^2$. -/)
  (title := /-- TD Dirichlet potential -/)
  (latexEnv := "definition")]
noncomputable def td_potential {n d : ℕ} (M : td_model n d)
    (θstar θ : td_vector d) : ℝ :=
  (1 - M.discount) * td_weighted_square M (td_value M θ - td_value M θstar) +
    M.discount * td_dirichlet_energy M (td_value M θ - td_value M θstar)

@[blueprint "def:td-uniform-bounds"
  (statement := /-- The constants $\phi_\infty>0$ and $r_\infty\geq0$ uniformly bound the Euclidean feature norms and absolute rewards. -/)
  (title := /-- Feature and reward bounds -/)
  (latexEnv := "definition")]
def td_uniform_bounds {n d : ℕ} (M : td_model n d) (φinf rinf : ℝ) : Prop :=
  0 < φinf ∧ 0 ≤ rinf ∧
    (∀ s, td_euclidean_norm (M.feature s) ≤ φinf) ∧
    (∀ s s', |M.reward s s'| ≤ rinf)

@[blueprint "def:td-geometric-mixing"
  (statement := /-- The mixing constant $\tau\geq1$ satisfies the finite-state total-variation estimate $\sum_j|(P^k)_{ij}-\pi_j|\leq 8\,2^{-k/\tau}$ for every state $i$ and every $k\geq0$. -/)
  (title := /-- Geometric mixing bound -/)
  (latexEnv := "definition")]
noncomputable def td_geometric_mixing {n d : ℕ} (M : td_model n d) (τ : ℝ) : Prop :=
  1 ≤ τ ∧ ∀ (k : ℕ) (i : Fin n),
    (∑ j, |(td_transition_matrix M ^ k) i j - (M.stationary j).toReal|) ≤
      8 * Real.rpow 2 (-((k : ℝ) / τ))

@[blueprint "def:td-curvature"
  (statement := /-- The curvature constant $\omega>0$ satisfies $f(\theta)-f(\theta^*)\geq\omega\|\theta-\theta^*\|_2^2$ for every $\theta$. -/)
  (title := /-- Quantitative TD curvature -/)
  (latexEnv := "definition")]
noncomputable def td_curvature {n d : ℕ} (M : td_model n d)
    (θstar : td_vector d) (ω : ℝ) : Prop :=
  0 < ω ∧ ∀ θ,
    ω * (td_euclidean_norm (θ - θstar)) ^ 2 ≤
      td_potential M θstar θ - td_potential M θstar θstar

@[blueprint "def:admissible-stepsize-shape"
  (statement := /-- A stepsize shape $(a_t)$ is admissible if it is positive, non-increasing, satisfies $a_0\leq1$, and has finite square sum. -/)
  (title := /-- Admissible anytime stepsize shape -/)
  (latexEnv := "definition")]
def admissible_stepsize_shape (a : ℕ → ℝ) : Prop :=
  (∀ t, 0 < a t) ∧ Antitone a ∧ a 0 ≤ 1 ∧ Summable (fun t => (a t) ^ 2)

@[blueprint "def:pr-eta-base"
  (statement := /-- Define the base stepsize by $\eta_{\mathrm{base}}=(c\tau\phi_\infty^2)^{-1}$. -/)
  (title := /-- Base stepsize -/)
  (latexEnv := "definition")]
noncomputable def pr_eta_base (c τ φinf : ℝ) : ℝ :=
  1 / (c * τ * φinf ^ 2)

@[blueprint "def:pr-square-mass"
  (statement := /-- Define $H=\sum_{t=0}^\infty\eta_t^2$. -/)
  (title := /-- Infinite squared-stepsize mass -/)
  (latexEnv := "definition")]
noncomputable def pr_square_mass (η : ℕ → ℝ) : ℝ :=
  ∑' t, (η t) ^ 2

@[blueprint "def:pr-a-one"
  (statement := /-- For $\delta\in(0,1)$, define $A_1(\delta)=1536(\sum_ta_t^2)^{1/2}(2\log(8/\delta))^{1/2}+2304$. -/)
  (title := /-- First bootstrap coefficient -/)
  (latexEnv := "definition")]
noncomputable def pr_a_one (a : ℕ → ℝ) (δ : ℝ) : ℝ :=
  1536 * Real.sqrt (∑' t, (a t) ^ 2) * Real.sqrt (2 * Real.log (8 / δ)) + 2304

@[blueprint "def:pr-a-two"
  (statement := /-- Define $A_2=2706\sum_ta_t^2$. -/)
  (title := /-- Second bootstrap coefficient -/)
  (latexEnv := "definition")]
noncomputable def pr_a_two (a : ℕ → ℝ) : ℝ :=
  2706 * (∑' t, (a t) ^ 2)

@[blueprint "def:pr-c-min"
  (statement := /-- Define $c_{\min}(\delta)=\frac12(A_1(\delta)+(A_1(\delta)^2+4A_2)^{1/2})$. -/)
  (title := /-- Minimal bootstrap constant -/)
  (latexEnv := "definition")]
noncomputable def pr_c_min (a : ℕ → ℝ) (δ : ℝ) : ℝ :=
  (pr_a_one a δ + Real.sqrt ((pr_a_one a δ) ^ 2 + 4 * pr_a_two a)) / 2

@[blueprint "def:pr-rho"
  (statement := /-- Define $\rho=2c/(c^2-A_1(\delta)c-A_2)^{1/2}$. -/)
  (title := /-- Bootstrap radius multiplier -/)
  (latexEnv := "definition")]
noncomputable def pr_rho (a : ℕ → ℝ) (δ c : ℝ) : ℝ :=
  2 * c / Real.sqrt (c ^ 2 - pr_a_one a δ * c - pr_a_two a)

@[blueprint "def:pr-base-radius"
  (statement := /-- Define $R_{\mathrm{base}}=\max\{\|\theta_0-\theta^*\|_2,\|\theta^*\|_2,r_\infty/\phi_\infty\}$. -/)
  (title := /-- Base TD radius -/)
  (latexEnv := "definition")]
noncomputable def pr_base_radius {d : ℕ} (θ0 θstar : td_vector d)
    (rinf φinf : ℝ) : ℝ :=
  max (td_euclidean_norm (θ0 - θstar))
    (max (td_euclidean_norm θstar) (rinf / φinf))

@[blueprint "def:pr-fast-constant"
  (statement := /-- Define $C_{\mathrm{fast}}=\rho R_{\mathrm{base}}[2+2\tau\phi_\infty^2(264\eta_0+176\sqrt{H}\sqrt{2\log(8/\delta)})+192\tau\phi_\infty^4H]$. -/)
  (title := /-- Fast-rate constant -/)
  (latexEnv := "definition")]
noncomputable def pr_fast_constant {d : ℕ} (a η : ℕ → ℝ) (δ c τ φinf rinf : ℝ)
    (θ0 θstar : td_vector d) : ℝ :=
  pr_rho a δ c * pr_base_radius θ0 θstar rinf φinf *
    (2 + 2 * τ * φinf ^ 2 *
      (264 * η 0 + 176 * Real.sqrt (pr_square_mass η) * Real.sqrt (2 * Real.log (8 / δ))) +
      192 * τ * φinf ^ 4 * pr_square_mass η)

@[blueprint "def:pr-robust-constant"
  (statement := /-- Define $C_{\mathrm{robust}}=\rho^2R_{\mathrm{base}}^2[\frac12+2\tau\phi_\infty^2(288\eta_0+192\sqrt{H}\sqrt{2\log(8/\delta)})+(672\tau+\frac92)\phi_\infty^4H]$. -/)
  (title := /-- Robust-rate constant -/)
  (latexEnv := "definition")]
noncomputable def pr_robust_constant {d : ℕ} (a η : ℕ → ℝ) (δ c τ φinf rinf : ℝ)
    (θ0 θstar : td_vector d) : ℝ :=
  (pr_rho a δ c) ^ 2 * (pr_base_radius θ0 θstar rinf φinf) ^ 2 *
    ((1 / 2 : ℝ) + 2 * τ * φinf ^ 2 *
      (288 * η 0 + 192 * Real.sqrt (pr_square_mass η) * Real.sqrt (2 * Real.log (8 / δ))) +
      (672 * τ + 9 / 2) * φinf ^ 4 * pr_square_mass η)

@[blueprint "def:td-i-one"
  (statement := /-- Define $I_{1,T}=S_T^{-1}(\theta_0-\theta_T)$. -/)
  (title := /-- Telescoping term -/)
  (latexEnv := "definition")]
noncomputable def td_i_one {n d : ℕ} (M : td_model n d) (η : ℕ → ℝ)
    (θ0 : td_vector d) (path : ℕ → Fin n) (T : ℕ) : td_vector d :=
  (pr_step_mass η T)⁻¹ • (θ0 - td_iterates M η θ0 T path)

@[blueprint "def:td-i-two"
  (statement := /-- Define $I_{2,T}=S_T^{-1}\sum_{t<T}\eta_t\xi_{Z_t}$, where $\xi_{(s,s')}=b_{(s,s')}-A_{(s,s')}\theta^*$. -/)
  (title := /-- Fixed-point noise term -/)
  (latexEnv := "definition")]
noncomputable def td_i_two {n d : ℕ} (M : td_model n d) (η : ℕ → ℝ)
    (θstar : td_vector d) (path : ℕ → Fin n) (T : ℕ) : td_vector d :=
  (pr_step_mass η T)⁻¹ • ∑ t ∈ Finset.range T, η t •
    (td_sample_vector M (path t) (path (t + 1)) -
      Matrix.mulVec (td_sample_matrix M (path t) (path (t + 1))) θstar)

@[blueprint "def:td-i-three"
  (statement := /-- Define $I_{3,T}=S_T^{-1}\sum_{t<T}\eta_t(A-A_{Z_t})(\theta_t-\theta^*)$. -/)
  (title := /-- Multiplicative Markov-noise term -/)
  (latexEnv := "definition")]
noncomputable def td_i_three {n d : ℕ} (M : td_model n d) (η : ℕ → ℝ)
    (θ0 θstar : td_vector d) (path : ℕ → Fin n) (T : ℕ) : td_vector d :=
  (pr_step_mass η T)⁻¹ • ∑ t ∈ Finset.range T, η t •
    (Matrix.mulVec
      (td_population_matrix M - td_sample_matrix M (path t) (path (t + 1)))
      (td_iterates M η θ0 t path - θstar))

@[blueprint "def:td-recursion-remainder"
  (statement := /-- Define $B_T$ as the residual in the exact squared-error expansion of the TD recursion after subtracting the initial error, the squared-increment sum, and twice the stationary mean-drift sum. -/)
  (title := /-- Squared-error recursion remainder -/)
  (latexEnv := "definition")]
noncomputable def td_recursion_remainder {n d : ℕ} (M : td_model n d) (η : ℕ → ℝ)
    (θ0 θstar : td_vector d) (path : ℕ → Fin n) (T : ℕ) : ℝ :=
  (td_euclidean_norm (td_iterates M η θ0 T path - θstar)) ^ 2 -
    (td_euclidean_norm (θ0 - θstar)) ^ 2 -
    (∑ t ∈ Finset.range T, (η t) ^ 2 *
      (td_euclidean_norm (td_update M (td_iterates M η θ0 t path)
        (path t) (path (t + 1)))) ^ 2) -
    2 * ∑ t ∈ Finset.range T, η t *
      (td_mean_update M (td_iterates M η θ0 t path) ⬝ᵥ
        (td_iterates M η θ0 t path - θstar))

@[blueprint "def:td-stopped-recursion-remainder"
  (statement := /-- Fix a radius $R\in\mathbb R$.  For the stopped iterates and stopped stepsizes from \cref{def:td-stopped-iterates,def:td-stopped-stepsize}, define $\widetilde B_T$ to be the residual in their exact squared-error expansion:
  \[
  \begin{aligned}
  \widetilde B_T={}&\|\widetilde\theta_T-\theta^*\|_2^2
  -\|\theta_0-\theta^*\|_2^2
  -\sum_{t<T}\widetilde\eta_t^2
    \|g(\widetilde\theta_t,(s_t,s_{t+1}))\|_2^2\\
  &-2\sum_{t<T}\widetilde\eta_t
    \langle\bar g(\widetilde\theta_t),
    \widetilde\theta_t-\theta^*\rangle.
  \end{aligned}
  \] -/)
  (title := /-- Stopped squared-error recursion remainder -/)
  (latexEnv := "definition")]
noncomputable def td_stopped_recursion_remainder {n d : ℕ} (M : td_model n d)
    (η : ℕ → ℝ) (θ0 θstar : td_vector d) (R : ℝ)
    (path : ℕ → Fin n) (T : ℕ) : ℝ :=
  (td_euclidean_norm (td_stopped_iterates M η θ0 R T path - θstar)) ^ 2 -
    (td_euclidean_norm (θ0 - θstar)) ^ 2 -
    (∑ t ∈ Finset.range T,
      (td_stopped_stepsize M η θ0 R path t) ^ 2 *
        (td_euclidean_norm
          (td_update M (td_stopped_iterates M η θ0 R t path)
            (path t) (path (t + 1)))) ^ 2) -
    2 * ∑ t ∈ Finset.range T, td_stopped_stepsize M η θ0 R path t *
      (td_mean_update M (td_stopped_iterates M η θ0 R t path) ⬝ᵥ
        (td_stopped_iterates M η θ0 R t path - θstar))

@[blueprint "def:bounded-iterates-event"
  (statement := /-- The radius event $\mathcal E_R$ consists of paths for which $\sup_t\|\theta_t\|_2\leq\rho R_{\mathrm{base}}$. -/)
  (title := /-- Uniform bounded-iterate event -/)
  (latexEnv := "definition")]
noncomputable def bounded_iterates_event {n d : ℕ} (M : td_model n d) (a η : ℕ → ℝ)
    (δ c φinf rinf : ℝ) (θ0 θstar : td_vector d) : Set (ℕ → Fin n) :=
  {path | ∀ t, td_euclidean_norm (td_iterates M η θ0 t path) ≤
    pr_rho a δ c * pr_base_radius θ0 θstar rinf φinf}

@[blueprint "def:i-two-control-event"
  (statement := /-- The event $\mathcal E_2$ is the simultaneous fixed-point-noise estimate used in the source proof, with confidence parameter $\delta/4$. -/)
  (title := /-- Fixed-point-noise control event -/)
  (latexEnv := "definition")]
noncomputable def i_two_control_event {n d : ℕ} (M : td_model n d) (η : ℕ → ℝ)
    (δ τ φinf rinf : ℝ) (θstar : td_vector d) : Set (ℕ → Fin n) :=
  {path | ∀ T, 1 ≤ T →
    td_euclidean_norm (td_i_two M η θstar path T) ≤
      2 / pr_step_mass η T *
        (2 * Real.sqrt (pr_square_mass η) * Real.sqrt (2 * Real.log (8 / δ)) + 3 * η 0) *
        8 * τ * (rinf * φinf + 2 * φinf ^ 2 * td_euclidean_norm θstar)}

@[blueprint "def:i-three-control-event"
  (statement := /-- The event $\mathcal E_3$ asserts that, whenever the radius event holds, the multiplicative Markov-noise term obeys the simultaneous localized estimate from the source. -/)
  (title := /-- Multiplicative-noise control event -/)
  (latexEnv := "definition")]
noncomputable def i_three_control_event {n d : ℕ} (M : td_model n d) (a η : ℕ → ℝ)
    (δ c τ φinf rinf : ℝ) (θ0 θstar : td_vector d) : Set (ℕ → Fin n) :=
  {path | path ∈ bounded_iterates_event M a η δ c φinf rinf θ0 θstar →
    ∀ T, 1 ≤ T →
      td_euclidean_norm (td_i_three M η θ0 θstar path T) ≤
        2 / pr_step_mass η T *
          (128 * τ * φinf ^ 2 *
              (pr_rho a δ c * pr_base_radius θ0 θstar rinf φinf) *
              Real.sqrt (pr_square_mass η) * Real.sqrt (2 * Real.log (8 / δ)) +
            192 * η 0 * τ * φinf ^ 2 *
              (pr_rho a δ c * pr_base_radius θ0 θstar rinf φinf)) +
        2 / pr_step_mass η T *
          (96 * τ * φinf ^ 4 *
            (pr_rho a δ c * pr_base_radius θ0 θstar rinf φinf) * pr_square_mass η)}

@[blueprint "def:energy-control-event"
  (statement := /-- The event $\mathcal E_4$ asserts that, on the radius event, the squared-increment sum plus $B_T$ satisfies the simultaneous bound obtained from the bootstrap proof. -/)
  (title := /-- Robust energy-control event -/)
  (latexEnv := "definition")]
noncomputable def energy_control_event {n d : ℕ} (M : td_model n d) (a η : ℕ → ℝ)
    (δ c τ φinf rinf : ℝ) (θ0 θstar : td_vector d) : Set (ℕ → Fin n) :=
  {path | path ∈ bounded_iterates_event M a η δ c φinf rinf θ0 θstar →
    ∀ T, 1 ≤ T →
      (∑ t ∈ Finset.range T, (η t) ^ 2 *
          (td_euclidean_norm (td_update M (td_iterates M η θ0 t path)
            (path t) (path (t + 1)))) ^ 2) +
          td_recursion_remainder M η θ0 θstar path T ≤
        768 * τ * φinf ^ 2 *
            (pr_rho a δ c * pr_base_radius θ0 θstar rinf φinf) ^ 2 *
            Real.sqrt (pr_square_mass η) * Real.sqrt (2 * Real.log (8 / δ)) +
        1152 * η 0 * τ * φinf ^ 2 *
            (pr_rho a δ c * pr_base_radius θ0 θstar rinf φinf) ^ 2 +
        1344 * τ * φinf ^ 4 *
            (pr_rho a δ c * pr_base_radius θ0 θstar rinf φinf) ^ 2 * pr_square_mass η +
        9 * φinf ^ 4 *
            (pr_rho a δ c * pr_base_radius θ0 θstar rinf φinf) ^ 2 * pr_square_mass η}

@[blueprint "def:stopped-energy-control-event"
  (statement := /-- Let $M$ be a finite TD model, let $(a_t)$ and $(\eta_t)$ be real sequences, let $\delta,c,\tau,\phi_\infty,r_\infty\in\mathbb R$, and let $\theta_0,\theta^*\in\mathbb R^d$.  Put
  \[
  R_{\max}=\rho(a,\delta,c)R_{\mathrm{base}}
  \quad\text{and}\quad H=\sum_{t=0}^{\infty}\eta_t^2.
  \]
  The stopped energy-control event consists of the paths for which, simultaneously for every $T\geq1$, the stopped squared-increment sum plus the stopped remainder from \cref{def:td-stopped-recursion-remainder} is at most
  \[
  \begin{aligned}
  &768\tau\phi_\infty^2R_{\max}^2\sqrt H
    \sqrt{2\log(8/\delta)}
  +1152\eta_0\tau\phi_\infty^2R_{\max}^2\\
  &\qquad +1344\tau\phi_\infty^4R_{\max}^2H
  +9\phi_\infty^4R_{\max}^2H.
  \end{aligned}
  \] -/)
  (title := /-- Simultaneous energy control for the stopped recursion -/)
  (latexEnv := "definition")]
noncomputable def stopped_energy_control_event {n d : ℕ} (M : td_model n d)
    (a η : ℕ → ℝ) (δ c τ φinf rinf : ℝ)
    (θ0 θstar : td_vector d) : Set (ℕ → Fin n) :=
  {path | ∀ T, 1 ≤ T →
    let R := pr_rho a δ c * pr_base_radius θ0 θstar rinf φinf
    (∑ t ∈ Finset.range T,
        (td_stopped_stepsize M η θ0 R path t) ^ 2 *
          (td_euclidean_norm
            (td_update M (td_stopped_iterates M η θ0 R t path)
              (path t) (path (t + 1)))) ^ 2) +
        td_stopped_recursion_remainder M η θ0 θstar R path T ≤
      768 * τ * φinf ^ 2 * R ^ 2 * Real.sqrt (pr_square_mass η) *
          Real.sqrt (2 * Real.log (8 / δ)) +
        1152 * η 0 * τ * φinf ^ 2 * R ^ 2 +
        1344 * τ * φinf ^ 4 * R ^ 2 * pr_square_mass η +
        9 * φinf ^ 4 * R ^ 2 * pr_square_mass η}

@[blueprint "def:analysis-event"
  (statement := /-- Define the common event $\mathcal E=\mathcal E_R\cap\mathcal E_2\cap\mathcal E_3\cap\mathcal E_4$. -/)
  (title := /-- Common high-probability analysis event -/)
  (latexEnv := "definition")]
noncomputable def analysis_event {n d : ℕ} (M : td_model n d) (a η : ℕ → ℝ)
    (δ c τ φinf rinf : ℝ) (θ0 θstar : td_vector d) : Set (ℕ → Fin n) :=
  bounded_iterates_event M a η δ c φinf rinf θ0 θstar ∩
    i_two_control_event M η δ τ φinf rinf θstar ∩
    i_three_control_event M a η δ c τ φinf rinf θ0 θstar ∩
    energy_control_event M a η δ c τ φinf rinf θ0 θstar

@[blueprint "def:pr-rate-event"
  (statement := /-- The target rate event consists of paths for which, for every $T\geq1$, the potential error of the PR average is at most the minimum of the explicit fast and robust bounds. -/)
  (title := /-- Simultaneous PR-rate event -/)
  (latexEnv := "definition")]
noncomputable def pr_rate_event {n d : ℕ} (M : td_model n d) (a η : ℕ → ℝ)
    (δ c τ φinf rinf ω : ℝ) (θ0 θstar : td_vector d) : Set (ℕ → Fin n) :=
  {path | ∀ T, 1 ≤ T →
    td_potential M θstar
        (pr_average η (fun t => td_iterates M η θ0 t path) T) -
        td_potential M θstar θstar ≤
      min
        ((pr_fast_constant a η δ c τ φinf rinf θ0 θstar) ^ 2 /
          (ω * (pr_step_mass η T) ^ 2))
        (pr_robust_constant a η δ c τ φinf rinf θ0 θstar /
          pr_step_mass η T)}

@[blueprint "lem:rho-bootstrap-inequality"
  (statement := /-- Let $a_t>0$ be non-increasing with $a_0\leq1$ and $\sum_ta_t^2<\infty$, let $\delta\in(0,1)$, and suppose $c>c_{\min}(\delta)$.  With $\rho$ as in \cref{def:pr-rho}, one has $\rho>2$ and
  \[
  4+1536\frac{\rho^2}{c}\Bigl(\sum_ta_t^2\Bigr)^{1/2}\Bigl(2\log\frac8\delta\Bigr)^{1/2}
  +2304\frac{\rho^2}{c}+2706\Bigl(\sum_ta_t^2\Bigr)\frac{\rho^2}{c^2}\leq\rho^2.
  \] -/)
  (proof := /-- Set $S=\sum_t a_t^2$, $A_1=A_1(\delta)$, $A_2=2706S$, and $D=c^2-A_1c-A_2$.  By \cref{def:pr-a-one,def:pr-a-two}, one has $A_1>0$ and $A_2\geq0$.  The hypothesis and \cref{def:pr-c-min} imply
  \[
  \sqrt{A_1^2+4A_2}<2c-A_1
  \]
  and $c>0$.  Squaring this strict inequality and using $(\sqrt{A_1^2+4A_2})^2=A_1^2+4A_2$ gives $D>0$.  If $r=\sqrt D$, then $r>0$, $r^2=D$, and $r<c$, since $A_1c+A_2>0$.  Hence \cref{def:pr-rho} yields $\rho=2c/r>2$.  Finally, the left-hand side of the asserted inequality is
  \[
  4+\frac{4cA_1}{r^2}+\frac{4A_2}{r^2}
  =\frac{4(r^2+cA_1+A_2)}{r^2}
  =\frac{4c^2}{r^2}=\rho^2,
  \]
  which proves the inequality, in fact with equality. -/)
  (title := /-- Bootstrap inequality for the explicit radius -/)
  (latexEnv := "lemma")]
lemma rho_bootstrap_inequality (a : ℕ → ℝ) (δ c : ℝ)
    (ha : admissible_stepsize_shape a) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hc : pr_c_min a δ < c) :
    2 < pr_rho a δ c ∧
      4 + 1536 * (pr_rho a δ c) ^ 2 / c * Real.sqrt (∑' t, (a t) ^ 2) *
          Real.sqrt (2 * Real.log (8 / δ)) +
        2304 * (pr_rho a δ c) ^ 2 / c +
        2706 * (∑' t, (a t) ^ 2) * (pr_rho a δ c) ^ 2 / c ^ 2 ≤
          (pr_rho a δ c) ^ 2 := by
  have hsum : 0 ≤ ∑' t, (a t) ^ 2 := tsum_nonneg (fun t => sq_nonneg (a t))
  have hA : 0 < pr_a_one a δ := by
    rw [pr_a_one]
    positivity
  have hB : 0 ≤ pr_a_two a := by
    rw [pr_a_two]
    positivity
  have hdisc : 0 ≤ (pr_a_one a δ) ^ 2 + 4 * pr_a_two a := by positivity
  have hsdisc := Real.sq_sqrt hdisc
  have hsnonneg := Real.sqrt_nonneg ((pr_a_one a δ) ^ 2 + 4 * pr_a_two a)
  have hc' :
      (pr_a_one a δ + Real.sqrt ((pr_a_one a δ) ^ 2 + 4 * pr_a_two a)) / 2 < c := by
    simpa [pr_c_min] using hc
  have hcpos : 0 < c := by nlinarith
  have hrootlt :
      Real.sqrt ((pr_a_one a δ) ^ 2 + 4 * pr_a_two a) <
        2 * c - pr_a_one a δ := by
    nlinarith
  have hsqlt :
      (Real.sqrt ((pr_a_one a δ) ^ 2 + 4 * pr_a_two a)) ^ 2 <
        (2 * c - pr_a_one a δ) ^ 2 := by
    nlinarith
  have hq : 0 < c ^ 2 - pr_a_one a δ * c - pr_a_two a := by
    nlinarith
  set r := Real.sqrt (c ^ 2 - pr_a_one a δ * c - pr_a_two a) with hr
  have hrpos : 0 < r := by
    rw [hr]
    exact Real.sqrt_pos.2 hq
  have hrsq : r ^ 2 = c ^ 2 - pr_a_one a δ * c - pr_a_two a := by
    rw [hr]
    exact Real.sq_sqrt (le_of_lt hq)
  have hrlt : r < c := by
    nlinarith
  constructor
  · rw [pr_rho, ← hr, lt_div_iff₀ hrpos]
    nlinarith
  · rw [pr_rho, ← hr]
    field_simp [ne_of_gt hrpos, ne_of_gt hcpos]
    rw [pr_a_one, pr_a_two] at *
    nlinarith [hrsq]

@[blueprint "lem:averaged-td-decomposition"
  (statement := /-- For every $n,d\in\mathbb N$, every TD model $M$ with $n$ states and
  $d$-dimensional parameter vectors, every stepsize sequence
  $\eta\colon\mathbb N\to\mathbb R$ satisfying $\eta_t>0$ for all $t$, every
  $\theta_0,\theta^*\in\mathbb R^d$, every path
  $s\colon\mathbb N\to\operatorname{Fin}(n)$, and every $T\in\mathbb N$ with
  $T\geq1$, if $\theta^*$ is a TD fixed point for $M$, then
  \[
  A(\bar\theta_T-\theta^*)=I_{1,T}+I_{2,T}+I_{3,T}.
  \] -/)
  (proof := /-- By positivity of the stepsizes and $T\geq1$, the cumulative
  stepsize $S_T$ from \cref{def:pr-step-mass} is strictly positive.  Summing
  the recursion in \cref{def:td-iterates,def:td-update} from $t=0$ through
  $T-1$ gives
  \[
  \sum_{t<T}\eta_t g(\theta_t,(s_t,s_{t+1}))=\theta_T-\theta_0.
  \]
  For each $t$, linearity of matrix--vector multiplication, the fixed-point
  identity in \cref{def:td-fixed-point}, and the sample and population
  quantities in
  \cref{def:td-sample-matrix,def:td-sample-vector,def:td-population-matrix}
  yield
  \[
  A(\theta_t-\theta^*)=-g(\theta_t,(s_t,s_{t+1}))
    +(b_{(s_t,s_{t+1})}-A_{(s_t,s_{t+1})}\theta^*)
    +(A-A_{(s_t,s_{t+1})})(\theta_t-\theta^*).
  \]
  Multiply this identity by $\eta_t$, sum over $t<T$, and use the telescoping
  equality.  Since $S_T\neq0$, \cref{def:pr-average} identifies the normalized
  sum on the left with $A(\bar\theta_T-\theta^*)$; the three normalized sums
  on the right are respectively the terms of
  \cref{def:td-i-one,def:td-i-two,def:td-i-three}. -/)
  (title := /-- Exact averaged TD decomposition -/)
  (latexEnv := "lemma")]
lemma averaged_td_decomposition {n d : ℕ} (M : td_model n d) (η : ℕ → ℝ)
    (θ0 θstar : td_vector d) (path : ℕ → Fin n) (T : ℕ)
    (hfixed : td_fixed_point M θstar) (hη : ∀ t, 0 < η t) (hT : 1 ≤ T) :
    Matrix.mulVec (td_population_matrix M)
        (pr_average η (fun t => td_iterates M η θ0 t path) T - θstar) =
      td_i_one M η θ0 path T + td_i_two M η θstar path T +
        td_i_three M η θ0 θstar path T := by
  have hSpos : 0 < pr_step_mass η T := by
    unfold pr_step_mass
    apply Finset.sum_pos
    · intro i hi
      exact hη i
    · exact Finset.nonempty_range_iff.mpr (by omega)
  have htel :
      (∑ t ∈ Finset.range T,
          η t • td_update M (td_iterates M η θ0 t path) (path t) (path (t + 1))) =
        td_iterates M η θ0 T path - θ0 := by
    calc
      _ = ∑ t ∈ Finset.range T,
          (td_iterates M η θ0 (t + 1) path - td_iterates M η θ0 t path) := by
        apply Finset.sum_congr rfl
        intro t ht
        simp [td_iterates]
      _ = _ := by
        simpa [td_iterates] using
          Finset.sum_range_sub (fun t => td_iterates M η θ0 t path) T
  have hsplit (t : ℕ) :
      Matrix.mulVec (td_population_matrix M)
          (td_iterates M η θ0 t path - θstar) =
        -td_update M (td_iterates M η θ0 t path) (path t) (path (t + 1)) +
          (td_sample_vector M (path t) (path (t + 1)) -
            Matrix.mulVec (td_sample_matrix M (path t) (path (t + 1))) θstar) +
          Matrix.mulVec
            (td_population_matrix M - td_sample_matrix M (path t) (path (t + 1)))
            (td_iterates M η θ0 t path - θstar) := by
    simp only [td_update, Matrix.mulVec_sub, Matrix.sub_mulVec]
    rw [hfixed]
    abel
  have havg :
      pr_average η (fun t => td_iterates M η θ0 t path) T - θstar =
        (pr_step_mass η T)⁻¹ • ∑ t ∈ Finset.range T,
          η t • (td_iterates M η θ0 t path - θstar) := by
    unfold pr_average
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
    change
      (pr_step_mass η T)⁻¹ •
            (∑ t ∈ Finset.range T, η t • td_iterates M η θ0 t path) -
          θstar =
        (pr_step_mass η T)⁻¹ •
          ((∑ t ∈ Finset.range T, η t • td_iterates M η θ0 t path) -
            pr_step_mass η T • θstar)
    ext i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp [hSpos.ne']
  have hsmul (c : ℝ) (v : td_vector d) :
      Matrix.mulVec (td_population_matrix M) (c • v) =
        c • Matrix.mulVec (td_population_matrix M) v := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [havg, hsmul, Matrix.mulVec_sum]
  simp_rw [hsmul, hsplit]
  rw [td_i_one, td_i_two, td_i_three]
  simp_rw [smul_add, smul_neg]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_neg_distrib, htel]
  simp only [neg_sub, smul_add]

@[blueprint "lem:pinelis-cosh-le-exp-half-sq"
  (statement := /-- For every $z\in\mathbb R$,
  \[
  \cosh z\leq \exp\!\left(\frac{z^2}{2}\right).
  \] -/)
  (proof := /-- Expand the hyperbolic cosine into its even power series.  For every $n\in\mathbb N$, the factorial estimate
  $2^n n!\leq(2n)!$ shows that
  \[
  \frac{z^{2n}}{(2n)!}\leq
  \frac{(z^2/2)^n}{n!}.
  \]
  Summing these nonnegative termwise inequalities and using the exponential power series proves the claim. -/)
  (title := /-- Gaussian majorant for the hyperbolic cosine -/)
  (latexEnv := "lemma")]
lemma pinelis_cosh_le_exp_half_sq (z : ℝ) :
    Real.cosh z ≤ Real.exp (z ^ 2 / 2) := by
  have hcau_tendsto (f : CauSeq ℂ norm) :
      Filter.Tendsto f Filter.atTop (nhds f.lim) := by
    refine tendsto_nhds.mpr ?_
    intro s hos hmem
    suffices ∃ a : ℕ, ∀ c : ℕ, c ≥ a → f c ∈ s by simpa using this
    rcases Metric.isOpen_iff.1 hos _ hmem with ⟨ε, hε, hball⟩
    obtain ⟨N, hN⟩ := Setoid.symm (CauSeq.equiv_lim f) _ hε
    exact ⟨N, fun c hc => hball (by
      dsimp [Metric.ball]
      rw [dist_comm, dist_eq_norm]
      exact hN c hc)⟩
  have hcomplex_exp : Complex.exp = NormedSpace.exp := by
    funext w
    rw [Complex.exp, NormedSpace.exp_eq_tsum_div]
    exact tendsto_nhds_unique (hcau_tendsto w.exp')
      (NormedSpace.expSeries_div_summable w).hasSum.tendsto_sum_nat
  have hreal_exp : Real.exp = NormedSpace.exp := by
    ext w
    exact mod_cast congr_fun hcomplex_exp w
  have hcosh_full :
      HasSum
        (fun n => (z ^ n / (n.factorial : ℝ) +
          (-z) ^ n / (n.factorial : ℝ)) / 2)
        (Real.cosh z) := by
    have hp : HasSum (fun n => z ^ n / (n.factorial : ℝ)) (Real.exp z) := by
      simpa only [hreal_exp] using
        (NormedSpace.expSeries_div_hasSum_exp z)
    have hm : HasSum (fun n => (-z) ^ n / (n.factorial : ℝ)) (Real.exp (-z)) := by
      simpa only [hreal_exp] using
        (NormedSpace.expSeries_div_hasSum_exp (-z))
    rw [Real.cosh_eq]
    exact (hp.add hm).div_const 2
  let a : ℕ → ℝ := fun n =>
    (z ^ n / (n.factorial : ℝ) + (-z) ^ n / (n.factorial : ℝ)) / 2
  have ha : HasSum a (Real.cosh z) := by
    simpa [a] using hcosh_full
  have heven_summable : Summable (fun n => a (2 * n)) :=
    ha.summable.comp_injective (by
      intro m n h
      omega)
  have heven := heven_summable.hasSum
  have hodd : HasSum (fun n => a (2 * n + 1)) 0 := by
    have hz : (fun n => a (2 * n + 1)) = 0 := by
      funext n
      dsimp [a]
      rw [Odd.neg_pow (odd_two_mul_add_one n)]
      ring
    rw [hz]
    exact hasSum_zero
  have hvalue : (∑' n, a (2 * n)) = Real.cosh z :=
    by simpa using (heven.even_add_odd hodd).unique ha
  have hcosh_even :
      HasSum (fun n => z ^ (2 * n) / ((2 * n).factorial : ℝ))
        (Real.cosh z) := by
    rw [← hvalue]
    have heq :
        (fun n => z ^ (2 * n) / ((2 * n).factorial : ℝ)) =
          fun n => a (2 * n) := by
      funext n
      dsimp [a]
      rw [Even.neg_pow (even_two_mul n)]
      ring
    rw [heq]
    exact heven
  have hexp :
      HasSum (fun n => (z ^ 2 / 2) ^ n / (n.factorial : ℝ))
        (Real.exp (z ^ 2 / 2)) := by
    simpa only [hreal_exp] using
      (NormedSpace.expSeries_div_hasSum_exp (z ^ 2 / 2))
  rw [← hcosh_even.tsum_eq, ← hexp.tsum_eq]
  apply hcosh_even.summable.tsum_le_tsum
  · intro n
    simp only [div_pow, pow_mul, inv_mul_eq_div, div_div]
    gcongr
    norm_cast
    exact Nat.two_pow_mul_factorial_le_factorial_two_mul n
  · exact hexp.summable

@[blueprint "lem:pinelis-cosh-norm-add-le"
  (statement := /-- Let $x,y\in\mathbb R^d$, let $b\geq0$, and suppose that $\lVert y\rVert_2\leq b$.  Then, for every $\lambda\in\mathbb R$,
  \[
  \cosh\!\left(\lambda\lVert x+y\rVert_2\right)
  \leq
  \cosh\!\left(\lambda\lVert x\rVert_2\right)\cosh(\lambda b)
  +
  \frac{\sinh(\lambda\lVert x\rVert_2)\sinh(\lambda b)}
       {\lVert x\rVert_2 b}\,\langle x,y\rangle,
  \]
  where the quotient is interpreted as zero when its denominator is zero. -/)
  (proof := /-- Put $r=\lVert x\rVert_2$ and
  $p=(rb+\langle x,y\rangle)/(2rb)$ when $rb>0$.
  Cauchy--Schwarz and $\lVert y\rVert_2\leq b$ give $0\leq p\leq1$, while expansion of the squared norm gives
  \[
  \lVert x+y\rVert_2^2
  \leq (1-p)(r-b)^2+p(r+b)^2.
  \]
  For every $n\in\mathbb N$, convexity of $u\mapsto u^n$ on $[0,\infty)$ bounds the $2n$-th term in the power series of the left-hand hyperbolic cosine by the corresponding convex combination of the series at $\lambda(r-b)$ and $\lambda(r+b)$.  Summing and applying the addition and subtraction identities for the hyperbolic cosine yields the displayed affine bound.  If $r=0$ or $b=0$, the quotient and inner-product term vanish, and the result follows directly from monotonicity and evenness of the hyperbolic cosine. -/)
  (title := /-- Affine conditional-cosh bound in Euclidean space -/)
  (latexEnv := "lemma")]
lemma pinelis_cosh_norm_add_le {d : ℕ}
    (x y : EuclideanSpace ℝ (Fin d)) (b lam : ℝ)
    (hb : 0 ≤ b) (hy : ‖y‖ ≤ b) :
    Real.cosh (lam * ‖x + y‖) ≤
      Real.cosh (lam * ‖x‖) * Real.cosh (lam * b) +
        (Real.sinh (lam * ‖x‖) * Real.sinh (lam * b) / (‖x‖ * b)) *
          inner ℝ x y := by
  have hsinh_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ Real.sinh z := by
    rw [Real.sinh_eq]
    have he : Real.exp (-z) ≤ Real.exp z := Real.exp_le_exp.mpr (by linarith)
    positivity
  have hcosh_mono {a c : ℝ} (hac : |a| ≤ |c|) :
      Real.cosh a ≤ Real.cosh c := by
    rw [← Real.cosh_abs (x := a), ← Real.cosh_abs (x := c)]
    let u := (|c| + |a|) / 2
    let v := (|c| - |a|) / 2
    have hu : 0 ≤ u := by dsimp [u]; positivity
    have hv : 0 ≤ v := by dsimp [v]; linarith
    have ha : |a| = u - v := by dsimp [u, v]; ring
    have hc : |c| = u + v := by dsimp [u, v]; ring
    rw [ha, hc, Real.cosh_sub, Real.cosh_add]
    nlinarith [mul_nonneg (hsinh_nonneg hu) (hsinh_nonneg hv)]
  have hcau_tendsto (f : CauSeq ℂ norm) :
      Filter.Tendsto f Filter.atTop (nhds f.lim) := by
    refine tendsto_nhds.mpr ?_
    intro s hos hmem
    suffices ∃ a : ℕ, ∀ c : ℕ, c ≥ a → f c ∈ s by simpa using this
    rcases Metric.isOpen_iff.1 hos _ hmem with ⟨ε, hε, hball⟩
    obtain ⟨N, hN⟩ := Setoid.symm (CauSeq.equiv_lim f) _ hε
    exact ⟨N, fun c hc => hball (by
      dsimp [Metric.ball]
      rw [dist_comm, dist_eq_norm]
      exact hN c hc)⟩
  have hcomplex_exp : Complex.exp = NormedSpace.exp := by
    funext z
    rw [Complex.exp, NormedSpace.exp_eq_tsum_div]
    exact tendsto_nhds_unique (hcau_tendsto z.exp')
      (NormedSpace.expSeries_div_summable z).hasSum.tendsto_sum_nat
  have hreal_exp : Real.exp = NormedSpace.exp := by
    ext z
    exact mod_cast congr_fun hcomplex_exp z
  have hcosh_series (z : ℝ) :
      HasSum
        (fun n => (z ^ n / (n.factorial : ℝ) +
          (-z) ^ n / (n.factorial : ℝ)) / 2)
        (Real.cosh z) := by
    have hp : HasSum (fun n => z ^ n / (n.factorial : ℝ)) (Real.exp z) := by
      simpa only [hreal_exp] using
        (NormedSpace.expSeries_div_hasSum_exp z)
    have hm : HasSum (fun n => (-z) ^ n / (n.factorial : ℝ)) (Real.exp (-z)) := by
      simpa only [hreal_exp] using
        (NormedSpace.expSeries_div_hasSum_exp (-z))
    rw [Real.cosh_eq]
    exact (hp.add hm).div_const 2
  by_cases hb0 : b = 0
  · subst b
    have hy0 : ‖y‖ = 0 := le_antisymm (by simpa using hy) (norm_nonneg y)
    have hyeq : y = 0 := norm_eq_zero.mp hy0
    subst y
    simp
  by_cases hx0 : ‖x‖ = 0
  · have hxeq : x = 0 := norm_eq_zero.mp hx0
    subst x
    simp only [norm_zero, zero_add, inner_zero_left, mul_zero, div_zero, zero_mul,
      add_zero, Real.cosh_zero, one_mul]
    apply hcosh_mono
    simpa only [abs_mul, abs_norm, abs_of_nonneg hb] using
      mul_le_mul_of_nonneg_left hy (abs_nonneg lam)
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx0)
  let p : ℝ := (‖x‖ * b + inner ℝ x y) / (2 * ‖x‖ * b)
  have hinner :
      |inner ℝ x y| ≤ ‖x‖ * b := by
    exact (abs_real_inner_le_norm x y).trans
      (mul_le_mul_of_nonneg_left hy (norm_nonneg x))
  have hp0 : 0 ≤ p := by
    dsimp [p]
    apply div_nonneg
    · nlinarith [neg_le_of_abs_le hinner]
    · positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    rw [div_le_one (by positivity : 0 < 2 * ‖x‖ * b)]
    nlinarith [le_of_abs_le hinner]
  have hysq : ‖y‖ ^ 2 ≤ b ^ 2 := by
    have hprod :=
      mul_nonneg (sub_nonneg.mpr hy) (add_nonneg hb (norm_nonneg y))
    nlinarith
  have hcombo :
      (1 - p) * (‖x‖ - b) ^ 2 + p * (‖x‖ + b) ^ 2 =
        ‖x‖ ^ 2 + b ^ 2 + 2 * inner ℝ x y := by
    dsimp [p]
    field_simp [hx0, hb0]
    ring
  have hnormsq :
      ‖x + y‖ ^ 2 ≤
        (1 - p) * (‖x‖ - b) ^ 2 + p * (‖x‖ + b) ^ 2 := by
    rw [hcombo, norm_add_sq_real]
    nlinarith
  have hterm (n : ℕ) :
      (lam * ‖x + y‖) ^ (2 * n) / ((2 * n).factorial : ℝ) ≤
        (1 - p) * ((lam * (‖x‖ - b)) ^ (2 * n) / ((2 * n).factorial : ℝ)) +
          p * ((lam * (‖x‖ + b)) ^ (2 * n) / ((2 * n).factorial : ℝ)) := by
    have hpow :
        (‖x + y‖ ^ 2) ^ n ≤
          (1 - p) * ((‖x‖ - b) ^ 2) ^ n +
            p * ((‖x‖ + b) ^ 2) ^ n := by
      calc
        (‖x + y‖ ^ 2) ^ n ≤
            ((1 - p) * (‖x‖ - b) ^ 2 + p * (‖x‖ + b) ^ 2) ^ n := by
              gcongr
        _ ≤ (1 - p) * ((‖x‖ - b) ^ 2) ^ n +
              p * ((‖x‖ + b) ^ 2) ^ n := by
              have hc := (convexOn_pow n).2
                (sq_nonneg (‖x‖ - b)) (sq_nonneg (‖x‖ + b))
                (sub_nonneg.mpr hp1) hp0 (by ring)
              simpa only [smul_eq_mul] using hc
    calc
      (lam * ‖x + y‖) ^ (2 * n) / ((2 * n).factorial : ℝ) =
          lam ^ (2 * n) * (‖x + y‖ ^ 2) ^ n /
            ((2 * n).factorial : ℝ) := by
              have hn :
                  ‖x + y‖ ^ (2 * n) = (‖x + y‖ ^ 2) ^ n := by
                rw [pow_mul]
              rw [mul_pow, hn]
      _ ≤ lam ^ (2 * n) *
            ((1 - p) * ((‖x‖ - b) ^ 2) ^ n +
              p * ((‖x‖ + b) ^ 2) ^ n) /
            ((2 * n).factorial : ℝ) := by
              apply div_le_div_of_nonneg_right
              · exact mul_le_mul_of_nonneg_left hpow
                  ((even_two_mul n).pow_nonneg lam)
              · positivity
      _ = (1 - p) * ((lam * (‖x‖ - b)) ^ (2 * n) /
              ((2 * n).factorial : ℝ)) +
            p * ((lam * (‖x‖ + b)) ^ (2 * n) /
              ((2 * n).factorial : ℝ)) := by
              have hm :
                  (‖x‖ - b) ^ (2 * n) = ((‖x‖ - b) ^ 2) ^ n := by
                rw [pow_mul]
              have hp :
                  (‖x‖ + b) ^ (2 * n) = ((‖x‖ + b) ^ 2) ^ n := by
                rw [pow_mul]
              rw [mul_pow, mul_pow, hm, hp]
              ring
  have hseries :
      Real.cosh (lam * ‖x + y‖) ≤
        (1 - p) * Real.cosh (lam * (‖x‖ - b)) +
          p * Real.cosh (lam * (‖x‖ + b)) := by
    have hleft := hcosh_series (lam * ‖x + y‖)
    have hright :=
      ((hcosh_series (lam * (‖x‖ - b))).mul_left (1 - p)).add
        ((hcosh_series (lam * (‖x‖ + b))).mul_left p)
    rw [← hleft.tsum_eq, ← hright.tsum_eq]
    apply hleft.summable.tsum_le_tsum
    · intro n
      by_cases hn : Even n
      · obtain ⟨k, rfl⟩ := hn
        simpa [two_mul, Even.neg_pow (even_two_mul k)] using hterm k
      · have hnodd : Odd n := Nat.not_even_iff_odd.mp hn
        simp only [hnodd.neg_pow]
        ring_nf
        norm_num
    · exact hright.summable
  calc
    Real.cosh (lam * ‖x + y‖) ≤
        (1 - p) * Real.cosh (lam * (‖x‖ - b)) +
          p * Real.cosh (lam * (‖x‖ + b)) := hseries
    _ = Real.cosh (lam * ‖x‖) * Real.cosh (lam * b) +
        (Real.sinh (lam * ‖x‖) * Real.sinh (lam * b) / (‖x‖ * b)) *
          inner ℝ x y := by
      rw [show lam * (‖x‖ - b) = lam * ‖x‖ - lam * b by ring,
        show lam * (‖x‖ + b) = lam * ‖x‖ + lam * b by ring,
        Real.cosh_sub, Real.cosh_add]
      dsimp [p]
      field_simp [hx0, hb0]
      ring

@[blueprint "lem:pinelis-conditional-cosh"
  (statement := /-- Let $(\Omega,\mathcal F,\mu)$ be a probability space, let $(\mathcal F_t)_{t\geq0}$ be a filtration, and let $X_t:\Omega\to\mathbb R^d$ be such that $M_T=\sum_{t<T}X_t$ is an $\mathbb R^d$-valued martingale.  Suppose that $\lVert X_t\rVert_2\leq b_t$ almost surely for every $t$, where $b_t\geq0$.  For every $\lambda>0$, put
  \[
  V_T=\sum_{t<T}b_t^2,
  \qquad
  Y_T=\exp\!\left(-\frac{\lambda^2V_T}{2}\right)
      \cosh\!\left(\lambda\lVert M_T\rVert_2\right).
  \]
  Then $(Y_T)_{T\geq0}$ is a real-valued supermartingale with respect to $(\mathcal F_T)_{T\geq0}$, one has $Y_T(\omega)\geq0$ for every $T\in\mathbb N$ and every $\omega\in\Omega$, and $Y_0=1$ holds $\mu$-almost surely. -/)
  (proof := /-- The martingale hypothesis implies that $X_t$ has conditional mean zero given $\mathcal F_t$.  Apply \cref{lem:pinelis-cosh-norm-add-le} with $x=M_t$, $y=X_t$, and $b=b_t$.  The coefficient of its inner-product term is $\mathcal F_t$-measurable, so conditional expectation removes that term and gives
  \[
  \mathbb E\!\left[
    \cosh\!\left(\lambda\lVert M_t+X_t\rVert_2\right)
    \mathrel{\middle|}\mathcal F_t\right]
  \leq
  \cosh(\lambda b_t)
  \cosh\!\left(\lambda\lVert M_t\rVert_2\right).
  \]
  By \cref{lem:pinelis-cosh-le-exp-half-sq},
  $\cosh(\lambda b_t)\leq\exp(\lambda^2b_t^2/2)$, and therefore
  \[
  \mathbb E\!\left[
    \cosh\!\left(\lambda\lVert M_t+X_t\rVert_2\right)
    \mathrel{\middle|}\mathcal F_t\right]
  \leq
  \exp\!\left(\frac{\lambda^2b_t^2}{2}\right)
  \cosh\!\left(\lambda\lVert M_t\rVert_2\right).
  \]
  Multiplication by $\exp(-\lambda^2V_{t+1}/2)$ and the identity $V_{t+1}=V_t+b_t^2$ yield
  $\mathbb E[Y_{t+1}\mid\mathcal F_t]\leq Y_t$.  The same increment bound gives integrability at every finite time, while adaptedness follows from that of the martingale.  Thus $Y$ is a supermartingale.  Finally, $M_0=0$ and $V_0=0$, so $Y_0=1$; nonnegativity follows from positivity of the exponential and of the hyperbolic cosine. -/)
  (title := /-- Conditional-cosh supermartingale for Euclidean martingales -/)
  (latexEnv := "lemma")]
lemma pinelis_conditional_cosh {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (ℱ : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›)
    (X : ℕ → Ω → td_vector d) (b : ℕ → ℝ) (lam : ℝ)
    (hmart : MeasureTheory.Martingale
      (fun T ω => ∑ t ∈ Finset.range T, X t ω) ℱ μ)
    (hbnonneg : ∀ t, 0 ≤ b t)
    (hbound : ∀ t, ∀ᵐ ω ∂μ, td_euclidean_norm (X t ω) ≤ b t)
    (hlam : 0 < lam) :
    MeasureTheory.Supermartingale
        (fun T ω =>
          Real.exp
              (-(lam ^ 2 / 2) * (∑ t ∈ Finset.range T, (b t) ^ 2)) *
            Real.cosh
              (lam * td_euclidean_norm (∑ t ∈ Finset.range T, X t ω)))
        ℱ μ ∧
      (∀ T ω,
        0 ≤
          Real.exp
              (-(lam ^ 2 / 2) * (∑ t ∈ Finset.range T, (b t) ^ 2)) *
            Real.cosh
              (lam * td_euclidean_norm (∑ t ∈ Finset.range T, X t ω))) ∧
      ∀ᵐ ω ∂μ,
        Real.exp
              (-(lam ^ 2 / 2) * (∑ t ∈ Finset.range 0, (b t) ^ 2)) *
            Real.cosh
              (lam * td_euclidean_norm (∑ t ∈ Finset.range 0, X t ω)) =
          1 := by
  let S : ℕ → Ω → td_vector d :=
    fun T ω => ∑ t ∈ Finset.range T, X t ω
  let L : td_vector d →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have hnorm (v : td_vector d) :
      td_euclidean_norm v = ‖L v‖ := by
    rw [td_euclidean_norm, EuclideanSpace.norm_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp [L, Real.norm_eq_abs, sq_abs]
  change MeasureTheory.Martingale S ℱ μ at hmart
  have hmartL :
      MeasureTheory.Martingale (fun T ω => L (S T ω)) ℱ μ := by
    refine ⟨fun T => L.cont.comp_stronglyMeasurable (hmart.1 T), ?_⟩
    intro i j hij
    filter_upwards [hmart.2 i j hij,
      L.comp_condExp_comm (m := ℱ i) (hmart.integrable j)] with ω hcond hcomm
    exact hcomm.symm.trans (congrArg L hcond)
  have hsum_nonneg (T : ℕ) :
      0 ≤ ∑ t ∈ Finset.range T, b t :=
    Finset.sum_nonneg fun t ht => hbnonneg t
  have hM_bound (T : ℕ) :
      ∀ᵐ ω ∂μ, ‖L (S T ω)‖ ≤ ∑ t ∈ Finset.range T, b t := by
    have hall :
        ∀ᵐ ω ∂μ, ∀ t ∈ Finset.range T,
          td_euclidean_norm (X t ω) ≤ b t := by
      rw [Filter.eventually_all_finset]
      intro t ht
      exact hbound t
    filter_upwards [hall] with ω hω
    have hLS :
        L (S T ω) = ∑ t ∈ Finset.range T, L (X t ω) := by
      ext i
      simp [S, L]
    rw [hLS]
    calc
      ‖∑ t ∈ Finset.range T, L (X t ω)‖ ≤
          ∑ t ∈ Finset.range T, ‖L (X t ω)‖ := norm_sum_le _ _
      _ = ∑ t ∈ Finset.range T, td_euclidean_norm (X t ω) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact (hnorm (X t ω)).symm
      _ ≤ ∑ t ∈ Finset.range T, b t :=
        Finset.sum_le_sum fun t ht => hω t ht
  have hC_strong (T : ℕ) :
      @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ T)
        (fun ω => Real.cosh (lam * ‖L (S T ω)‖)) := by
    exact Real.continuous_cosh.comp_stronglyMeasurable
      ((hmartL.1 T).norm.const_mul lam)
  have hC_integrable (T : ℕ) :
      MeasureTheory.Integrable
        (fun ω => Real.cosh (lam * ‖L (S T ω)‖)) μ := by
    apply MeasureTheory.Integrable.of_bound
      ((hC_strong T).mono (ℱ.le T)).aestronglyMeasurable
      (Real.cosh (lam * ∑ t ∈ Finset.range T, b t))
    filter_upwards [hM_bound T] with ω hω
    have hc := pinelis_cosh_norm_add_le
      (0 : EuclideanSpace ℝ (Fin d)) (L (S T ω))
      (∑ t ∈ Finset.range T, b t) lam (hsum_nonneg T) hω
    have hc' :
        Real.cosh (lam * ‖L (S T ω)‖) ≤
          Real.cosh (lam * ∑ t ∈ Finset.range T, b t) := by
      simpa using hc
    rw [Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]
    exact hc'
  have hY_strong :
      MeasureTheory.StronglyAdapted ℱ
        (fun T ω =>
          Real.exp
              (-(lam ^ 2 / 2) * (∑ t ∈ Finset.range T, (b t) ^ 2)) *
            Real.cosh
              (lam * td_euclidean_norm (∑ t ∈ Finset.range T, X t ω))) := by
    intro T
    simpa only [S, hnorm] using
      (hC_strong T).const_mul
        (Real.exp
          (-(lam ^ 2 / 2) * (∑ t ∈ Finset.range T, (b t) ^ 2)))
  have hY_integrable (T : ℕ) :
      MeasureTheory.Integrable
        (fun ω =>
          Real.exp
              (-(lam ^ 2 / 2) * (∑ t ∈ Finset.range T, (b t) ^ 2)) *
            Real.cosh
              (lam * td_euclidean_norm (∑ t ∈ Finset.range T, X t ω))) μ := by
    simpa only [S, hnorm] using
      (hC_integrable T).const_mul
        (Real.exp
          (-(lam ^ 2 / 2) * (∑ t ∈ Finset.range T, (b t) ^ 2)))
  refine ⟨?_, ?_, ?_⟩
  · apply MeasureTheory.supermartingale_nat hY_strong hY_integrable
    intro i
    let mi : Ω → EuclideanSpace ℝ (Fin d) := fun ω => L (S i ω)
    let zi : Ω → EuclideanSpace ℝ (Fin d) := fun ω => L (X i ω)
    let kappa : Ω → ℝ := fun ω =>
      Real.sinh (lam * ‖mi ω‖) * Real.sinh (lam * b i) /
        (‖mi ω‖ * b i)
    let g : Ω → EuclideanSpace ℝ (Fin d) := fun ω => kappa ω • mi ω
    let cnext : Ω → ℝ := fun ω =>
      Real.cosh (lam * ‖L (S (i + 1) ω)‖)
    let cbase : Ω → ℝ := fun ω =>
      Real.cosh (lam * ‖mi ω‖) * Real.cosh (lam * b i)
    let cross : Ω → ℝ := fun ω => (innerSL ℝ) (g ω) (zi ω)
    have hstepM (ω : Ω) :
        L (S (i + 1) ω) = mi ω + zi ω := by
      simp [mi, zi, S, Finset.sum_range_succ]
    have hZeq :
        zi = fun ω => L (S (i + 1) ω) - L (S i ω) := by
      funext ω
      rw [hstepM]
      simp [mi]
    have hZ_integrable : MeasureTheory.Integrable zi μ := by
      rw [hZeq]
      exact (hmartL.integrable (i + 1)).sub (hmartL.integrable i)
    have hZ_cond :
        MeasureTheory.condExp (m := ℱ i) μ zi =ᵐ[μ] 0 := by
      rw [hZeq]
      change MeasureTheory.condExp (m := ℱ i) μ
        ((fun ω => L (S (i + 1) ω)) - fun ω => L (S i ω)) =ᵐ[μ] 0
      have hself :=
        MeasureTheory.condExp_of_stronglyMeasurable
          (ℱ.le i) (hmartL.1 i) (hmartL.integrable i)
      filter_upwards [
        MeasureTheory.condExp_sub (hmartL.integrable (i + 1))
          (hmartL.integrable i) (ℱ i),
        hmartL.2 i (i + 1) (Nat.le_succ i)] with ω hsub hnext
      rw [hsub, Pi.sub_apply, hnext, congrFun hself ω, sub_self]
      rfl
    have hMi_strong :
        @MeasureTheory.StronglyMeasurable Ω (EuclideanSpace ℝ (Fin d)) _
          (ℱ i) mi := by
      exact hmartL.1 i
    have hK_strong :
          @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ i) kappa := by
      have hs :
          @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ i)
            (fun ω => Real.sinh (lam * ‖mi ω‖)) :=
        Real.continuous_sinh.comp_stronglyMeasurable
          (hMi_strong.norm.const_mul lam)
      have hn := hs.const_mul (Real.sinh (lam * b i))
      have hd := hMi_strong.norm.const_mul (b i)
      convert hn.div hd using 1
      funext ω
      simp [kappa]
      ring
    have hG_strong :
        @MeasureTheory.StronglyMeasurable Ω (EuclideanSpace ℝ (Fin d)) _
          (ℱ i) g := by
      exact hK_strong.smul hMi_strong
    have hZi_bound :
        ∀ᵐ ω ∂μ, ‖zi ω‖ ≤ b i := by
      filter_upwards [hbound i] with ω hω
      simpa [zi, hnorm] using hω
    have hCross_ae :
        MeasureTheory.AEStronglyMeasurable cross μ := by
      exact
        (innerSL ℝ (E := EuclideanSpace ℝ (Fin d))).continuous₂
          |>.comp_aestronglyMeasurable₂
            ((hG_strong.mono (ℱ.le i)).aestronglyMeasurable)
            hZ_integrable.aestronglyMeasurable
    have hCbase_integrable : MeasureTheory.Integrable cbase μ := by
      dsimp [cbase, mi]
      exact (hC_integrable i).mul_const (Real.cosh (lam * b i))
    have hCross_integrable : MeasureTheory.Integrable cross μ := by
      apply hCbase_integrable.mono' hCross_ae
      filter_upwards [hZi_bound] with ω hZi
      have hp := pinelis_cosh_norm_add_le
        (mi ω) (zi ω) (b i) lam (hbnonneg i) hZi
      have hm := pinelis_cosh_norm_add_le
        (mi ω) (-zi ω) (b i) lam (hbnonneg i) (by simpa using hZi)
      have hcross :
          kappa ω * inner ℝ (mi ω) (zi ω) = cross ω := by
        dsimp [cross, g]
        exact (real_inner_smul_left (mi ω) (zi ω) (kappa ω)).symm
      have hneg :
          -cbase ω ≤ cross ω := by
        rw [← hcross]
        have hcpos : 0 ≤ Real.cosh (lam * ‖mi ω + zi ω‖) :=
          (Real.cosh_pos _).le
        simpa [cbase, kappa] using
          (show -cbase ω ≤ kappa ω * inner ℝ (mi ω) (zi ω) by
            dsimp [cbase]
            nlinarith [hp])
      have hpos :
          cross ω ≤ cbase ω := by
        rw [← hcross]
        have hcpos : 0 ≤ Real.cosh (lam * ‖mi ω - zi ω‖) :=
          (Real.cosh_pos _).le
        have hm' :
            Real.cosh (lam * ‖mi ω - zi ω‖) ≤
              cbase ω - kappa ω * inner ℝ (mi ω) (zi ω) := by
          simpa [cbase, kappa, sub_eq_add_neg] using hm
        nlinarith
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨hneg, hpos⟩
    have hCross_cond :
        MeasureTheory.condExp (m := ℱ i) μ cross =ᵐ[μ] fun ω =>
          inner ℝ (g ω) ((MeasureTheory.condExp (m := ℱ i) μ zi) ω) := by
      exact
        MeasureTheory.condExp_bilin_of_stronglyMeasurable_left
          (B := innerSL ℝ) hG_strong hCross_integrable hZ_integrable
    have hCross_zero :
        MeasureTheory.condExp (m := ℱ i) μ cross =ᵐ[μ] 0 := by
      filter_upwards [hCross_cond, hZ_cond] with ω hcross hzero
      rw [hcross, hzero]
      simp
    have hpoint : cnext ≤ᵐ[μ] cbase + cross := by
      filter_upwards [hZi_bound] with ω hZi
      have hp := pinelis_cosh_norm_add_le
        (mi ω) (zi ω) (b i) lam (hbnonneg i) hZi
      have hcross :
          kappa ω * inner ℝ (mi ω) (zi ω) = cross ω := by
        dsimp [cross, g]
        exact (real_inner_smul_left (mi ω) (zi ω) (kappa ω)).symm
      change cnext ω ≤ cbase ω + cross ω
      rw [← hcross]
      simpa [cnext, cbase, kappa, hstepM] using hp
    have hCnext_integrable : MeasureTheory.Integrable cnext μ := by
      simpa [cnext] using hC_integrable (i + 1)
    have hsum_integrable :
        MeasureTheory.Integrable (cbase + cross) μ :=
      hCbase_integrable.add hCross_integrable
    have hmono :=
      MeasureTheory.condExp_mono (m := ℱ i)
        hCnext_integrable hsum_integrable hpoint
    have hadd :=
      MeasureTheory.condExp_add hCbase_integrable hCross_integrable (ℱ i)
    have hbase_self :
        MeasureTheory.condExp (m := ℱ i) μ cbase =ᵐ[μ] cbase := by
      have hcbase_strong :
          @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ i) cbase := by
        dsimp [cbase]
        exact (Real.continuous_cosh.comp_stronglyMeasurable
          (hMi_strong.norm.const_mul lam)).mul
            MeasureTheory.stronglyMeasurable_const
      have heq := MeasureTheory.condExp_of_stronglyMeasurable
        (ℱ.le i) hcbase_strong hCbase_integrable
      exact Filter.Eventually.of_forall fun ω => congrFun heq ω
    have hC_cond :
        MeasureTheory.condExp (m := ℱ i) μ cnext ≤ᵐ[μ] cbase := by
      filter_upwards [hmono, hadd, hbase_self, hCross_zero] with
        ω hle ha hb hz
      rw [ha, Pi.add_apply, hb, hz, Pi.zero_apply, add_zero] at hle
      exact hle
    let an : ℝ :=
      Real.exp
        (-(lam ^ 2 / 2) * (∑ t ∈ Finset.range (i + 1), (b t) ^ 2))
    let ai : ℝ :=
      Real.exp
        (-(lam ^ 2 / 2) * (∑ t ∈ Finset.range i, (b t) ^ 2))
    have hnext_eq :
        (fun ω =>
          Real.exp
              (-(lam ^ 2 / 2) *
                (∑ t ∈ Finset.range (i + 1), (b t) ^ 2)) *
            Real.cosh
              (lam *
                td_euclidean_norm
                  (∑ t ∈ Finset.range (i + 1), X t ω))) =
          fun ω => an * cnext ω := by
      funext ω
      simp only [an, cnext, S, hnorm]
    have hnow_eq :
        (fun ω =>
          Real.exp
              (-(lam ^ 2 / 2) * (∑ t ∈ Finset.range i, (b t) ^ 2)) *
            Real.cosh
              (lam * td_euclidean_norm
                (∑ t ∈ Finset.range i, X t ω))) =
          fun ω => ai * Real.cosh (lam * ‖mi ω‖) := by
      funext ω
      simp only [ai, mi, S, hnorm]
    rw [hnext_eq, hnow_eq]
    have hscale :
        MeasureTheory.condExp (m := ℱ i) μ (fun ω => an * cnext ω)
          =ᵐ[μ] fun ω =>
            an * (MeasureTheory.condExp (m := ℱ i) μ cnext) ω := by
      have hf : (fun ω => an * cnext ω) = an • cnext := by
        funext ω
        simp [smul_eq_mul]
      have hg :
          (fun ω => an *
            (MeasureTheory.condExp (m := ℱ i) μ cnext) ω) =
            an • MeasureTheory.condExp (m := ℱ i) μ cnext := by
        funext ω
        simp [smul_eq_mul]
      rw [hf, hg]
      exact MeasureTheory.condExp_smul (μ := μ) an cnext (ℱ i)
    have hexp_id :
        an * Real.exp ((lam * b i) ^ 2 / 2) = ai := by
      dsimp [an, ai]
      rw [Finset.sum_range_succ]
      rw [show
        -(lam ^ 2 / 2) *
            ((∑ t ∈ Finset.range i, b t ^ 2) + b i ^ 2) =
          (-(lam ^ 2 / 2) * (∑ t ∈ Finset.range i, b t ^ 2)) +
            (-(lam ^ 2 / 2) * b i ^ 2) by ring,
        Real.exp_add, mul_assoc, ← Real.exp_add]
      ring_nf
      simp
    filter_upwards [hscale, hC_cond] with ω hscaleω hcondω
    rw [hscaleω]
    calc
      an * (MeasureTheory.condExp (m := ℱ i) μ cnext) ω ≤
          an * cbase ω :=
        mul_le_mul_of_nonneg_left hcondω (Real.exp_pos _).le
      _ = (an * Real.cosh (lam * b i)) *
          Real.cosh (lam * ‖mi ω‖) := by
        dsimp [cbase]
        ring
      _ ≤ (an * Real.exp ((lam * b i) ^ 2 / 2)) *
          Real.cosh (lam * ‖mi ω‖) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (pinelis_cosh_le_exp_half_sq (lam * b i))
            (Real.exp_pos _).le)
          (Real.cosh_pos _).le
      _ = ai * Real.cosh (lam * ‖mi ω‖) := by rw [hexp_id]
  · intro T ω
    positivity
  · simp [td_euclidean_norm]

@[blueprint "lem:pinelis-anytime-maximal"
  (statement := /-- Let $(\Omega,\mathcal F,\mu)$ be a probability space, let $(\mathcal F_t)_{t\geq0}$ be a filtration, and let $(Y_t)_{t\geq0}$ be a nonnegative real-valued supermartingale with $Y_0=1$ almost surely.  Then, for every $q>0$,
  \[
  \mu\!\left\{\omega:\text{ there exists }t\geq0\text{ with }Y_t(\omega)\geq q\right\}
  \leq \frac1q.
  \]
  The event is the countable-time crossing event, not a finite-horizon surrogate. -/)
  (proof := /-- For $N\in\mathbb N$, stop $Y$ at the first time $t\leq N$ for which $Y_t\geq q$, using $N$ itself if no crossing occurs.  Optional stopping for the nonnegative supermartingale gives expectation at most $\mathbb E[Y_0]=1$.  On the crossing event the stopped value is at least $q$, and it is nonnegative on the complement; hence
  \[
  q\,\mu\{\exists t\leq N:Y_t\geq q\}\leq1.
  \]
  These finite-horizon crossing events increase with $N$, and their union is the countable-time crossing event.  Continuity of probability from below and $q>0$ therefore give the asserted bound. -/)
  (title := /-- Countable-time maximal inequality for nonnegative supermartingales -/)
  (latexEnv := "lemma")]
lemma pinelis_anytime_maximal {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (ℱ : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›)
    (Y : ℕ → Ω → ℝ) (q : ℝ)
    (hsuper : MeasureTheory.Supermartingale Y ℱ μ)
    (hnonneg : ∀ T ω, 0 ≤ Y T ω)
    (hinitial : ∀ᵐ ω ∂μ, Y 0 ω = 1) (hq : 0 < q) :
    μ.real {ω | ∃ T : ℕ, q ≤ Y T ω} ≤ 1 / q := by
  classical
  let E : ℕ → Set Ω := fun n => {ω | ∃ k ≤ n, q ≤ Y k ω}
  have hE_mono : Monotone E := by
    intro n m hnm ω hω
    rcases hω with ⟨k, hkn, hk⟩
    exact ⟨k, hkn.trans hnm, hk⟩
  have hE_union : (⋃ n : ℕ, E n) = {ω | ∃ T : ℕ, q ≤ Y T ω} := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨n, k, _hkn, hk⟩
      exact ⟨k, hk⟩
    · rintro ⟨k, hk⟩
      exact Set.mem_iUnion.mpr ⟨k, k, le_rfl, hk⟩
  have hfinite : ∀ n, q * μ.real (E n) ≤ 1 := by
    intro n
    set τ : Ω → ℕ∞ := fun ω =>
      ((MeasureTheory.hittingBtwn Y (Set.Ici q) 0 n ω : ℕ) : ℕ∞) with hτ_def
    set evt : Set Ω := {ω |
      q ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        fun k => Y k ω} with hevt
    have hadapted : MeasureTheory.Adapted ℱ Y :=
      hsuper.stronglyAdapted.adapted
    have hτ_stop : MeasureTheory.IsStoppingTime ℱ τ := by
      rw [hτ_def]
      exact hadapted.isStoppingTime_hittingBtwn measurableSet_Ici
    have hτ_le : ∀ ω, τ ω ≤ (n : ℕ∞) := by
      intro ω
      have hle : MeasureTheory.hittingBtwn Y (Set.Ici q) 0 n ω ≤ n :=
        MeasureTheory.hittingBtwn_le ω
      simp only [hτ_def]
      exact_mod_cast hle
    have hint : ∀ i, MeasureTheory.Integrable (Y i) μ :=
      hsuper.integrable
    have hsv_int : MeasureTheory.Integrable
        (MeasureTheory.stoppedValue Y τ) μ :=
      MeasureTheory.integrable_stoppedValue ℕ hτ_stop hint hτ_le
    have hsv_nonneg : 0 ≤ MeasureTheory.stoppedValue Y τ :=
      fun ω => hnonneg _ ω
    have hmeas_evt : MeasurableSet evt :=
      measurableSet_le measurable_const
        (Finset.measurable_range_sup'' fun k _ =>
          (hsuper.stronglyMeasurable k).measurable.le (ℱ.le k))
    have hstep : ∀ ω ∈ evt,
        q ≤ MeasureTheory.stoppedValue Y τ ω := by
      intro ω hω
      rw [hevt, Set.mem_setOf_eq, Finset.le_sup'_iff] at hω
      have hmem : MeasureTheory.stoppedValue Y τ ω ∈ Set.Ici q := by
        rw [hτ_def]
        refine MeasureTheory.stoppedValue_hittingBtwn_mem ?_
        obtain ⟨k, hk_mem, hk_le⟩ := hω
        rw [Finset.mem_range, Nat.lt_succ_iff] at hk_mem
        exact ⟨k, ⟨Nat.zero_le _, hk_mem⟩, hk_le⟩
      exact hmem
    have hB : q * μ.real evt ≤
        ∫ ω in evt, MeasureTheory.stoppedValue Y τ ω ∂μ :=
      MeasureTheory.setIntegral_ge_of_const_le_real hmeas_evt
        (MeasureTheory.measure_ne_top _ _) hstep hsv_int.integrableOn
    have hC : (∫ ω in evt, MeasureTheory.stoppedValue Y τ ω ∂μ) ≤
        ∫ ω, MeasureTheory.stoppedValue Y τ ω ∂μ :=
      MeasureTheory.setIntegral_le_integral hsv_int
        (Filter.Eventually.of_forall hsv_nonneg)
    have hD : (∫ ω, MeasureTheory.stoppedValue Y τ ω ∂μ) ≤
        ∫ ω, Y 0 ω ∂μ := by
      have hsub : MeasureTheory.Submartingale (-Y) ℱ μ := hsuper.neg
      have hmono := hsub.expected_stoppedValue_mono
        (MeasureTheory.isStoppingTime_const ℱ 0) hτ_stop
        (fun _ => bot_le) hτ_le
      have key : ∀ σ : Ω → ℕ∞,
          (∫ ω, MeasureTheory.stoppedValue (-Y) σ ω ∂μ) =
            -(∫ ω, MeasureTheory.stoppedValue Y σ ω ∂μ) := by
        intro σ
        have hfun : (fun ω => MeasureTheory.stoppedValue (-Y) σ ω) =
            fun ω => -(MeasureTheory.stoppedValue Y σ ω) := by
          funext ω
          simp only [MeasureTheory.stoppedValue, Pi.neg_apply]
        rw [hfun, MeasureTheory.integral_neg]
      simp only [key] at hmono
      rw [MeasureTheory.stoppedValue_const] at hmono
      linarith
    have hmax : q * μ.real evt ≤ ∫ ω, Y 0 ω ∂μ :=
      hB.trans (hC.trans hD)
    have hinit : (∫ ω, Y 0 ω ∂μ) = 1 := by
      rw [MeasureTheory.integral_congr_ae hinitial]
      simp
    rw [hinit] at hmax
    simpa only [E, hevt, Finset.le_sup'_iff, Finset.mem_range,
      Nat.lt_succ_iff] using hmax
  have hmeasure_le : μ (⋃ n : ℕ, E n) ≤ ENNReal.ofReal (1 / q) := by
    rw [hE_mono.measure_iUnion]
    refine iSup_le ?_
    intro n
    have hdiv : μ.real (E n) ≤ 1 / q := by
      rw [le_div_iff₀ hq]
      simpa [mul_comm] using hfinite n
    rw [← MeasureTheory.ofReal_measureReal (μ := μ) (s := E n)]
    exact ENNReal.ofReal_le_ofReal hdiv
  have hreal_le : μ.real (⋃ n : ℕ, E n) ≤ 1 / q := by
    have hnonneg_div : 0 ≤ 1 / q := one_div_nonneg.mpr hq.le
    have htop : ENNReal.ofReal (1 / q) ≠ ⊤ := ENNReal.ofReal_ne_top
    change (μ (⋃ n : ℕ, E n)).toReal ≤ 1 / q
    calc
      (μ (⋃ n : ℕ, E n)).toReal ≤ (ENNReal.ofReal (1 / q)).toReal :=
        ENNReal.toReal_mono htop hmeasure_le
      _ = 1 / q := ENNReal.toReal_ofReal hnonneg_div
  rw [hE_union] at hreal_le
  exact hreal_le

@[blueprint "lem:pinelis-anytime-td"
  (statement := /-- Let $(\Omega,\mathcal F,\mu)$ be a probability space, let $(\mathcal F_t)_{t\geq0}$ be a filtration, and let $X_t:\Omega\to\mathbb R^d$ be such that $M_T=\sum_{t<T}X_t$ is an $\mathbb R^d$-valued martingale.  Suppose that $\|X_t\|_2\leq b_t$ almost surely, where $b_t\geq0$ and $\sum_{t=0}^{\infty}b_t^2<\infty$.  For every $\delta\in(0,1)$, with probability at least $1-\delta$ one has, simultaneously for all $T\geq0$,
  \[
  \|M_T\|_2\leq
  \left(\sum_{t=0}^{\infty}b_t^2\right)^{1/2}
  \left(2\log\frac{2}{\delta}\right)^{1/2}.
  \]
  Here the juxtaposition of the two square-root factors denotes multiplication. -/)
  (proof := /-- Put
  \[
  M_T=\sum_{t<T}X_t,qquad
  B^2=\sum_{t=0}^{\infty}b_t^2,qquad
  A=2\log\frac{2}{\delta},qquad
  R=\sqrt{B^2}\sqrt A.
  \]
  The summands defining $B^2$ are nonnegative.  If $B^2=0$, comparison of each $b_t^2$ with the full sum gives $b_t=0$ for every $t$.  The increment bound and the Euclidean norm of \cref{def:td-euclidean-norm} then imply $X_t=0$ almost surely for each $t$.  Since the index set is countable, these equalities hold simultaneously on one event of probability one.  On that event $M_T=0$ for every $T$, and hence the asserted inequalities hold simultaneously.

  Suppose that $B^2>0$.  The assumptions $0<\delta<1$ imply $A>0$, so
  \[
  \lambda=\frac{\sqrt A}{\sqrt{B^2}}
  \]
  is positive.  By \cref{lem:pinelis-conditional-cosh},
  \[
  Y_T=\exp\!\left(-\frac{\lambda^2}{2}
      \sum_{t<T}b_t^2\right)
      \cosh\!\left(\lambda\lVert M_T\rVert_2\right)
  \]
  is a nonnegative supermartingale and $Y_0=1$ almost surely.  Summability and nonnegativity give
  $\sum_{t<T}b_t^2\leq B^2$ for every $T$.  Moreover,
  $\cosh x\geq e^x/2$, while the definitions give
  $\lambda R=A$ and $\lambda^2B^2=A$.  Consequently, if
  $\lVert M_T\rVert_2>R$ for some $T$, then
  \[
  Y_T\geq
  \frac12\exp\!\left(\lambda R-\frac{\lambda^2B^2}{2}\right)
  =\frac12\exp\!\left(\log\frac2\delta\right)
  =\frac1\delta.
  \]
  Thus the event on which the desired bound fails is contained in the countable-time event
  $\{\omega:\exists T,\ Y_T(\omega)\geq1/\delta\}$.  Applying
  \cref{lem:pinelis-anytime-maximal} with $q=1/\delta$ shows that this crossing event has probability at most $\delta$.  Its measurable complement therefore has probability at least $1-\delta$ and is contained in the event on which $\lVert M_T\rVert_2\leq R$ for every $T$, which proves the claim. -/)
  (title := /-- Anytime Pinelis inequality for finite-dimensional TD martingales -/)
  (latexEnv := "lemma")]
lemma pinelis_anytime_td {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (ℱ : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›)
    (X : ℕ → Ω → td_vector d) (b : ℕ → ℝ) (δ : ℝ)
    (hmart : MeasureTheory.Martingale
      (fun T ω => ∑ t ∈ Finset.range T, X t ω) ℱ μ)
    (hbnonneg : ∀ t, 0 ≤ b t)
    (hbound : ∀ t, ∀ᵐ ω ∂μ, td_euclidean_norm (X t ω) ≤ b t)
    (hbsum : Summable (fun t => (b t) ^ 2))
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    μ.real
        {ω | ∀ T,
          td_euclidean_norm (∑ t ∈ Finset.range T, X t ω) ≤
            Real.sqrt (∑' t, (b t) ^ 2) *
              Real.sqrt (2 * Real.log (2 / δ))} ≥
      1 - δ := by
  classical
  let S : ℕ → Ω → td_vector d :=
    fun T ω => ∑ t ∈ Finset.range T, X t ω
  let B2 : ℝ := ∑' t, (b t) ^ 2
  let A : ℝ := 2 * Real.log (2 / δ)
  let R : ℝ := Real.sqrt B2 * Real.sqrt A
  let L : td_vector d ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have hnorm (v : td_vector d) :
      td_euclidean_norm v = ‖L v‖ := by
    rw [td_euclidean_norm, EuclideanSpace.norm_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp [L, Real.norm_eq_abs, sq_abs]
  have hB2_nonneg : 0 ≤ B2 := by
    exact tsum_nonneg fun t => sq_nonneg (b t)
  change 1 - δ ≤ μ.real {ω | ∀ T, td_euclidean_norm (S T ω) ≤ R}
  by_cases hB2zero : B2 = 0
  · have hbzero (t : ℕ) : b t = 0 := by
      have hle : (b t) ^ 2 ≤ B2 := by
        dsimp [B2]
        exact hbsum.le_tsum t (fun i hi => sq_nonneg (b i))
      nlinarith [sq_nonneg (b t)]
    have hXzero (t : ℕ) : ∀ᵐ ω ∂μ, X t ω = 0 := by
      filter_upwards [hbound t] with ω hω
      have hnorm_zero : ‖L (X t ω)‖ = 0 := by
        apply le_antisymm
        · rw [← hnorm]
          simpa [hbzero t] using hω
        · exact norm_nonneg _
      apply L.injective
      exact norm_eq_zero.mp hnorm_zero
    have hXzero_all : ∀ᵐ ω ∂μ, ∀ t, X t ω = 0 :=
      MeasureTheory.ae_all_iff.mpr hXzero
    have hgood_ae :
        {ω | ∀ T, td_euclidean_norm (S T ω) ≤ R} =ᵐ[μ] Set.univ := by
      filter_upwards [hXzero_all] with ω hω
      change (∀ T, td_euclidean_norm (S T ω) ≤ R) = True
      apply propext
      rw [iff_true]
      intro T
      simp [S, hω, R, B2, hB2zero, td_euclidean_norm]
    have hmeasure :
        μ {ω | ∀ T, td_euclidean_norm (S T ω) ≤ R} = μ Set.univ :=
      MeasureTheory.measure_congr hgood_ae
    calc
      1 - δ ≤ 1 := by linarith
      _ = μ.real {ω | ∀ T, td_euclidean_norm (S T ω) ≤ R} := by
        rw [MeasureTheory.Measure.real, hmeasure]
        simp
  · have hB2pos : 0 < B2 :=
      lt_of_le_of_ne hB2_nonneg (Ne.symm hB2zero)
    have hratio : 1 < 2 / δ := by
      rw [lt_div_iff₀ hδ0]
      linarith
    have hlogpos : 0 < Real.log (2 / δ) := Real.log_pos hratio
    have hApos : 0 < A := by
      dsimp [A]
      positivity
    have hsqrtB2pos : 0 < Real.sqrt B2 := Real.sqrt_pos.2 hB2pos
    have hsqrtApos : 0 < Real.sqrt A := Real.sqrt_pos.2 hApos
    let lam : ℝ := Real.sqrt A / Real.sqrt B2
    have hlam : 0 < lam := by
      dsimp [lam]
      positivity
    let Y : ℕ → Ω → ℝ :=
      fun T ω =>
        Real.exp
            (-(lam ^ 2 / 2) * (∑ t ∈ Finset.range T, (b t) ^ 2)) *
          Real.cosh (lam * td_euclidean_norm (S T ω))
    have hpinelis :=
      pinelis_conditional_cosh (μ := μ) (ℱ := ℱ) (X := X) (b := b)
        (lam := lam) hmart hbnonneg hbound hlam
    have hsuper : MeasureTheory.Supermartingale Y ℱ μ := by
      simpa only [Y, S] using hpinelis.1
    have hnonneg : ∀ T ω, 0 ≤ Y T ω := by
      simpa only [Y, S] using hpinelis.2.1
    have hinitial : ∀ᵐ ω ∂μ, Y 0 ω = 1 := by
      simpa only [Y, S] using hpinelis.2.2
    let C : Set Ω := {ω | ∃ T : ℕ, 1 / δ ≤ Y T ω}
    have hcross : μ.real C ≤ δ := by
      have hmax :=
        pinelis_anytime_maximal (μ := μ) (ℱ := ℱ) (Y := Y)
          (q := 1 / δ) hsuper hnonneg hinitial (one_div_pos.mpr hδ0)
      simpa only [C, one_div_div, div_one] using hmax
    have hCmeas : MeasurableSet C := by
      rw [show C = ⋃ T : ℕ, {ω | 1 / δ ≤ Y T ω} by
        ext ω
        simp [C]]
      refine MeasurableSet.iUnion ?_
      intro T
      exact measurableSet_le measurable_const
        (((hsuper.1 T).mono (ℱ.le T)).measurable)
    have hV (T : ℕ) :
        (∑ t ∈ Finset.range T, (b t) ^ 2) ≤ B2 := by
      dsimp [B2]
      exact hbsum.sum_le_tsum (Finset.range T)
        (fun t ht => sq_nonneg (b t))
    have hlamR : lam * R = A := by
      calc
        lam * R =
            (Real.sqrt A / Real.sqrt B2) *
              (Real.sqrt B2 * Real.sqrt A) := by
                rfl
        _ = Real.sqrt A * Real.sqrt A := by
          field_simp [ne_of_gt hsqrtB2pos]
        _ = A := by
          nlinarith [Real.sq_sqrt hApos.le]
    have hlam_sq_B2 : lam ^ 2 * B2 = A := by
      dsimp [lam]
      field_simp [ne_of_gt hsqrtB2pos]
      nlinarith [Real.sq_sqrt hB2_nonneg, Real.sq_sqrt hApos.le]
    have hexponent :
        lam * R - (lam ^ 2 / 2) * B2 = Real.log (2 / δ) := by
      rw [hlamR]
      have hhalf : (lam ^ 2 / 2) * B2 = A / 2 := by
        rw [div_mul_eq_mul_div, hlam_sq_B2]
      rw [hhalf]
      dsimp [A]
      ring
    have hexpbase :
        Real.exp (lam * R - (lam ^ 2 / 2) * B2) / 2 = 1 / δ := by
      rw [hexponent, Real.exp_log (div_pos (by norm_num) hδ0)]
      field_simp [hδ0.ne']
    have hbad_cross :
        {ω | ∃ T, R < td_euclidean_norm (S T ω)} ⊆ C := by
      rintro ω ⟨T, hT⟩
      refine ⟨T, ?_⟩
      have hcosh :
          Real.exp (lam * td_euclidean_norm (S T ω)) / 2 ≤
            Real.cosh (lam * td_euclidean_norm (S T ω)) := by
        rw [Real.cosh_eq]
        nlinarith [Real.exp_pos (-(lam * td_euclidean_norm (S T ω)))]
      have htime :
          lam * R ≤ lam * td_euclidean_norm (S T ω) := by
        have hmul :=
          mul_pos hlam
            (sub_pos.mpr hT)
        nlinarith
      have hcoef : 0 ≤ lam ^ 2 / 2 := by positivity
      have hvar :
          -(lam ^ 2 / 2) * B2 ≤
            -(lam ^ 2 / 2) * (∑ t ∈ Finset.range T, (b t) ^ 2) :=
        mul_le_mul_of_nonpos_left (hV T) (neg_nonpos.mpr hcoef)
      have harg :
          lam * R - (lam ^ 2 / 2) * B2 ≤
            lam * td_euclidean_norm (S T ω) -
              (lam ^ 2 / 2) * (∑ t ∈ Finset.range T, (b t) ^ 2) := by
        linarith
      calc
        1 / δ =
            Real.exp (lam * R - (lam ^ 2 / 2) * B2) / 2 :=
          hexpbase.symm
        _ ≤
            Real.exp
                (lam * td_euclidean_norm (S T ω) -
                  (lam ^ 2 / 2) *
                    (∑ t ∈ Finset.range T, (b t) ^ 2)) / 2 := by
          exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr harg)
            (by norm_num)
        _ =
            Real.exp
                (-(lam ^ 2 / 2) *
                  (∑ t ∈ Finset.range T, (b t) ^ 2)) *
              (Real.exp (lam * td_euclidean_norm (S T ω)) / 2) := by
          calc
            Real.exp
                  (lam * td_euclidean_norm (S T ω) -
                    (lam ^ 2 / 2) *
                      (∑ t ∈ Finset.range T, (b t) ^ 2)) / 2 =
                Real.exp
                    (-(lam ^ 2 / 2) *
                        (∑ t ∈ Finset.range T, (b t) ^ 2) +
                      lam * td_euclidean_norm (S T ω)) / 2 := by
              congr 2
              ring
            _ =
                (Real.exp
                      (-(lam ^ 2 / 2) *
                        (∑ t ∈ Finset.range T, (b t) ^ 2)) *
                    Real.exp (lam * td_euclidean_norm (S T ω))) / 2 := by
              rw [Real.exp_add]
            _ =
                Real.exp
                    (-(lam ^ 2 / 2) *
                      (∑ t ∈ Finset.range T, (b t) ^ 2)) *
                  (Real.exp (lam * td_euclidean_norm (S T ω)) / 2) := by
              ring
        _ ≤
            Real.exp
                (-(lam ^ 2 / 2) *
                  (∑ t ∈ Finset.range T, (b t) ^ 2)) *
              Real.cosh (lam * td_euclidean_norm (S T ω)) :=
          mul_le_mul_of_nonneg_left hcosh (Real.exp_pos _).le
        _ = Y T ω := rfl
    have hCcomp_sub :
        Cᶜ ⊆ {ω | ∀ T, td_euclidean_norm (S T ω) ≤ R} := by
      intro ω hω T
      by_contra hnot
      have hbad : R < td_euclidean_norm (S T ω) :=
        lt_of_not_ge hnot
      exact hω (hbad_cross ⟨T, hbad⟩)
    have hCcomp_lower : 1 - δ ≤ μ.real Cᶜ := by
      rw [MeasureTheory.probReal_compl_eq_one_sub hCmeas]
      linarith
    exact hCcomp_lower.trans (MeasureTheory.measureReal_mono hCcomp_sub)

@[blueprint "lem:energy-abel-remainder-bound"
  (statement := /-- Let $(\eta_t)_{t\in\mathbb N}$, $(u_t)_{t\in\mathbb N}$,
  $(v_t)_{t\in\mathbb N}$, and $(w_t)_{t\in\mathbb N}$ be real sequences.  Let
  $\tau,\phi_\infty,R\geq0$, and fix $T\in\mathbb N$ with $T\geq1$.  Suppose
  $\eta_t>0$ for every $t\in\mathbb N$, the sequence $(\eta_t)$ is non-increasing, and
  \[
  |\eta_0u_0|+|\eta_Tu_T|\leq384\eta_0\tau\phi_\infty^2R^2,\qquad
  |v_t|\leq192\tau\phi_\infty^2R^2,
  \]
  and $|w_t|\leq672\eta_t\tau\phi_\infty^4R^2$ for every $t<T$.  Then the Abel remainder
  \[
  \eta_0u_0-\eta_Tu_T-\sum_{t<T}(\eta_t-\eta_{t+1})v_t
  -\sum_{t<T}\eta_{t+1}w_t
  \]
  has absolute value at most
  \[
  576\eta_0\tau\phi_\infty^2R^2+
  672\tau\phi_\infty^4R^2\sum_{t<T}\eta_t^2.
  \] -/)
  (proof := /-- The endpoint terms contribute at most $384\eta_0\tau\phi_\infty^2R^2$.  Since $\eta$ is non-increasing and nonnegative,
  \[
  \sum_{t<T}(\eta_t-\eta_{t+1})=\eta_0-\eta_T\leq\eta_0;
  \]
  hence the variation term contributes at most
  $192\eta_0\tau\phi_\infty^2R^2$.  Finally,
  $\eta_{t+1}\leq\eta_t$ and the bound on $w_t$ show that the last sum is at most
  $672\tau\phi_\infty^4R^2\sum_{t<T}\eta_t^2$.  The triangle inequality gives the claim. -/)
  (title := /-- Deterministic Abel bound for the localized energy remainder -/)
  (latexEnv := "lemma")]
lemma energy_abel_remainder_bound (η u v w : ℕ → ℝ) (τ φinf R : ℝ) (T : ℕ)
    (hT : 1 ≤ T) (hηpos : ∀ t, 0 < η t) (hηanti : Antitone η)
    (hτ : 0 ≤ τ) (hφ : 0 ≤ φinf) (hR : 0 ≤ R)
    (hend : |η 0 * u 0| + |η T * u T| ≤
      384 * η 0 * τ * φinf ^ 2 * R ^ 2)
    (hvar : ∀ t ∈ Finset.range T,
      |v t| ≤ 192 * τ * φinf ^ 2 * R ^ 2)
    (hlip : ∀ t ∈ Finset.range T,
      |w t| ≤ 672 * η t * τ * φinf ^ 4 * R ^ 2) :
    |η 0 * u 0 - η T * u T -
        (∑ t ∈ Finset.range T, (η t - η (t + 1)) * v t) -
        (∑ t ∈ Finset.range T, η (t + 1) * w t)| ≤
      576 * η 0 * τ * φinf ^ 2 * R ^ 2 +
        672 * τ * φinf ^ 4 * R ^ 2 *
          (∑ t ∈ Finset.range T, (η t) ^ 2) := by
  have hηnonneg (t : ℕ) : 0 ≤ η t := (hηpos t).le
  have hstep (t : ℕ) : η (t + 1) ≤ η t := hηanti (Nat.le_succ t)
  have hdiff (t : ℕ) : 0 ≤ η t - η (t + 1) := sub_nonneg.mpr (hstep t)
  have hvar_sum :
      |∑ t ∈ Finset.range T, (η t - η (t + 1)) * v t| ≤
        192 * η 0 * τ * φinf ^ 2 * R ^ 2 := by
    calc
      |∑ t ∈ Finset.range T, (η t - η (t + 1)) * v t| ≤
          ∑ t ∈ Finset.range T, |(η t - η (t + 1)) * v t| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ Finset.range T,
          (η t - η (t + 1)) * (192 * τ * φinf ^ 2 * R ^ 2) := by
        apply Finset.sum_le_sum
        intro t ht
        rw [abs_mul, abs_of_nonneg (hdiff t)]
        exact mul_le_mul_of_nonneg_left (hvar t ht) (hdiff t)
      _ = (η 0 - η T) * (192 * τ * φinf ^ 2 * R ^ 2) := by
        rw [← Finset.sum_mul, Finset.sum_range_sub']
      _ ≤ η 0 * (192 * τ * φinf ^ 2 * R ^ 2) := by
        apply mul_le_mul_of_nonneg_right (sub_le_self (η 0) (hηnonneg T))
        positivity
      _ = 192 * η 0 * τ * φinf ^ 2 * R ^ 2 := by ring
  have hlip_sum :
      |∑ t ∈ Finset.range T, η (t + 1) * w t| ≤
        672 * τ * φinf ^ 4 * R ^ 2 *
          (∑ t ∈ Finset.range T, (η t) ^ 2) := by
    calc
      |∑ t ∈ Finset.range T, η (t + 1) * w t| ≤
          ∑ t ∈ Finset.range T, |η (t + 1) * w t| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ Finset.range T,
          672 * τ * φinf ^ 4 * R ^ 2 * (η t) ^ 2 := by
        apply Finset.sum_le_sum
        intro t ht
        rw [abs_mul, abs_of_nonneg (hηnonneg (t + 1))]
        calc
          η (t + 1) * |w t| ≤
              η (t + 1) * (672 * η t * τ * φinf ^ 4 * R ^ 2) :=
            mul_le_mul_of_nonneg_left (hlip t ht) (hηnonneg (t + 1))
          _ ≤ η t * (672 * η t * τ * φinf ^ 4 * R ^ 2) := by
            apply mul_le_mul_of_nonneg_right (hstep t)
            have hηt : 0 ≤ η t := hηnonneg t
            positivity
          _ = 672 * τ * φinf ^ 4 * R ^ 2 * (η t) ^ 2 := by ring
      _ = 672 * τ * φinf ^ 4 * R ^ 2 *
          (∑ t ∈ Finset.range T, (η t) ^ 2) := by
        rw [Finset.mul_sum]
  calc
    |η 0 * u 0 - η T * u T -
        (∑ t ∈ Finset.range T, (η t - η (t + 1)) * v t) -
        (∑ t ∈ Finset.range T, η (t + 1) * w t)| ≤
      (|η 0 * u 0| + |η T * u T|) +
        |∑ t ∈ Finset.range T, (η t - η (t + 1)) * v t| +
        |∑ t ∈ Finset.range T, η (t + 1) * w t| := by
      calc
        |η 0 * u 0 - η T * u T -
            (∑ t ∈ Finset.range T, (η t - η (t + 1)) * v t) -
            (∑ t ∈ Finset.range T, η (t + 1) * w t)| ≤
          |η 0 * u 0 - η T * u T -
            (∑ t ∈ Finset.range T, (η t - η (t + 1)) * v t)| +
            |∑ t ∈ Finset.range T, η (t + 1) * w t| := abs_sub _ _
        _ ≤ (|η 0 * u 0 - η T * u T| +
              |∑ t ∈ Finset.range T, (η t - η (t + 1)) * v t|) +
            |∑ t ∈ Finset.range T, η (t + 1) * w t| :=
          by
            have habs := abs_sub
              (η 0 * u 0 - η T * u T)
              (∑ t ∈ Finset.range T, (η t - η (t + 1)) * v t)
            linarith
        _ ≤ (|η 0 * u 0| + |η T * u T|) +
              |∑ t ∈ Finset.range T, (η t - η (t + 1)) * v t| +
            |∑ t ∈ Finset.range T, η (t + 1) * w t| :=
          by
            have habs := abs_sub (η 0 * u 0) (η T * u T)
            linarith
    _ ≤ 576 * η 0 * τ * φinf ^ 2 * R ^ 2 +
        672 * τ * φinf ^ 4 * R ^ 2 *
          (∑ t ∈ Finset.range T, (η t) ^ 2) := by
      linarith

@[blueprint "lem:energy-td-euclidean-norm-bridge"
  (statement := /-- For every $d\in\mathbb N$ and $v\in\mathbb R^d$, the TD Euclidean norm from \cref{def:td-euclidean-norm} is the norm obtained by transporting $v$ to Mathlib's Euclidean space through the canonical $\ell^2$ equivalence. -/)
  (proof := /-- Expand the two norm definitions.  The canonical $\ell^2$ equivalence preserves every coordinate, so both squared norms are the same finite sum. -/)
  (title := /-- Canonical Euclidean-space realization of the TD norm -/)
  (latexEnv := "lemma")]
lemma energy_td_euclidean_norm_bridge {d : ℕ} (v : td_vector d) :
    td_euclidean_norm v =
      ‖(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm v‖ := by
  rw [td_euclidean_norm, EuclideanSpace.norm_eq]
  congr 1
  simp

@[blueprint "lem:energy-td-euclidean-norm-add"
  (statement := /-- For every $x,y\in\mathbb R^d$, the TD Euclidean norm satisfies $\lVert x+y\rVert_2\leq\lVert x\rVert_2+\lVert y\rVert_2$. -/)
  (proof := /-- Transport the three vectors through the canonical isometry of \cref{lem:energy-td-euclidean-norm-bridge}, use linearity of that equivalence, and apply the norm triangle inequality in Euclidean space. -/)
  (title := /-- Triangle inequality for the TD Euclidean norm -/)
  (latexEnv := "lemma")]
lemma energy_td_euclidean_norm_add {d : ℕ} (x y : td_vector d) :
    td_euclidean_norm (x + y) ≤ td_euclidean_norm x + td_euclidean_norm y := by
  let L : td_vector d ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  rw [energy_td_euclidean_norm_bridge, energy_td_euclidean_norm_bridge,
    energy_td_euclidean_norm_bridge]
  change ‖L (x + y)‖ ≤ ‖L x‖ + ‖L y‖
  rw [map_add]
  exact norm_add_le _ _

@[blueprint "lem:energy-td-euclidean-norm-smul"
  (statement := /-- For every $r\in\mathbb R$ and $x\in\mathbb R^d$, one has $\lVert rx\rVert_2=|r|\lVert x\rVert_2$. -/)
  (proof := /-- Transport the vectors by \cref{lem:energy-td-euclidean-norm-bridge}; linearity and the norm formula for scalar multiplication give the identity. -/)
  (title := /-- Homogeneity of the TD Euclidean norm -/)
  (latexEnv := "lemma")]
lemma energy_td_euclidean_norm_smul {d : ℕ} (r : ℝ) (x : td_vector d) :
    td_euclidean_norm (r • x) = |r| * td_euclidean_norm x := by
  let L : td_vector d ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  rw [energy_td_euclidean_norm_bridge, energy_td_euclidean_norm_bridge]
  change ‖L (r • x)‖ = |r| * ‖L x‖
  rw [map_smul, norm_smul, Real.norm_eq_abs]

@[blueprint "lem:energy-td-euclidean-norm-sub"
  (statement := /-- For every $x,y\in\mathbb R^d$, the TD Euclidean norm satisfies $\lVert x-y\rVert_2\leq\lVert x\rVert_2+\lVert y\rVert_2$. -/)
  (proof := /-- Write subtraction as addition of $-y$, apply \cref{lem:energy-td-euclidean-norm-add}, and use the homogeneity identity \cref{lem:energy-td-euclidean-norm-smul} with scalar $-1$. -/)
  (title := /-- Difference triangle inequality for the TD Euclidean norm -/)
  (latexEnv := "lemma")]
lemma energy_td_euclidean_norm_sub {d : ℕ} (x y : td_vector d) :
    td_euclidean_norm (x - y) ≤ td_euclidean_norm x + td_euclidean_norm y := by
  rw [sub_eq_add_neg]
  refine (energy_td_euclidean_norm_add x (-y)).trans_eq ?_
  rw [show -y = (-1 : ℝ) • y by ext i; simp,
    energy_td_euclidean_norm_smul]
  norm_num

@[blueprint "lem:energy-td-dot-product-bound"
  (statement := /-- For every $x,y\in\mathbb R^d$, their coordinate dot product satisfies $|x\mathbin{\boldsymbol\cdot}y|\leq\lVert x\rVert_2\lVert y\rVert_2$. -/)
  (proof := /-- Under \cref{lem:energy-td-euclidean-norm-bridge}, the coordinate dot product is the real inner product with the arguments reversed.  The result is therefore the Cauchy--Schwarz inequality in Euclidean space. -/)
  (title := /-- Cauchy--Schwarz bound for TD vectors -/)
  (latexEnv := "lemma")]
lemma energy_td_dot_product_bound {d : ℕ} (x y : td_vector d) :
    |x ⬝ᵥ y| ≤ td_euclidean_norm x * td_euclidean_norm y := by
  let L : td_vector d ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have h := abs_real_inner_le_norm (L y) (L x)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simp only [RCLike.star_def, starRingEnd_apply, star_id_of_comm] at h
  change |x ⬝ᵥ y| ≤ ‖L y‖ * ‖L x‖ at h
  simpa only [energy_td_euclidean_norm_bridge, mul_comm] using h

@[blueprint "def:energy-centered-scalar"
  (statement := /-- For a TD parameter $\theta$ and transition $(s,s')$, define the centered scalar energy increment by
  \[
  h_\theta(s,s')=\langle g(\theta,(s,s'))-\bar g(\theta),\theta-\theta^*\rangle.
  \] -/)
  (title := /-- Centered scalar TD energy increment -/)
  (latexEnv := "definition")]
noncomputable def energy_centered_scalar {n d : ℕ} (M : td_model n d)
    (θstar θ : td_vector d) (s s' : Fin n) : ℝ :=
  (td_update M θ s s' - td_mean_update M θ) ⬝ᵥ (θ - θstar)

@[blueprint "def:energy-state-center"
  (statement := /-- Average the centered scalar increment of \cref{def:energy-centered-scalar} over one transition from $s$:
  \[
  f_\theta(s)=\sum_{s'}P(s,s')h_\theta(s,s').
  \] -/)
  (title := /-- One-step state average of the centered energy -/)
  (latexEnv := "definition")]
noncomputable def energy_state_center {n d : ℕ} (M : td_model n d)
    (θstar θ : td_vector d) (s : Fin n) : ℝ :=
  ∑ s', (M.transition s s').toReal * energy_centered_scalar M θstar θ s s'

@[blueprint "def:energy-poisson-solution"
  (statement := /-- Define the canonical centered Poisson series
  \[
  u_\theta(s)=\sum_{k=0}^{\infty}\sum_j
  \bigl((P^k)_{sj}-\pi_j\bigr)f_\theta(j),
  \]
  where $f_\theta$ is from \cref{def:energy-state-center}. -/)
  (title := /-- Poisson series for the centered TD energy -/)
  (latexEnv := "definition")]
noncomputable def energy_poisson_solution {n d : ℕ} (M : td_model n d)
    (θstar θ : td_vector d) (s : Fin n) : ℝ :=
  ∑' k, ∑ j,
    ((td_transition_matrix M ^ k) s j - (M.stationary j).toReal) *
      energy_state_center M θstar θ j

@[blueprint "lem:energy-state-center-stationary"
  (statement := /-- For every $\theta^*,\theta\in\mathbb R^d$, the stationary mean of $f_\theta$ vanishes:
  \[
  \sum_s\pi(s)f_\theta(s)=0.
  \] -/)
  (proof := /-- Expand \cref{def:energy-state-center,def:energy-centered-scalar}.  The stationary average of the sample update is the population update by \cref{def:td-population-matrix,def:td-population-vector,def:td-mean-update}; hence centering makes every coordinate average zero.  Distributing the dot product over the finite sums proves the identity. -/)
  (title := /-- Stationary centering identity for the energy observable -/)
  (latexEnv := "lemma")]
lemma energy_state_center_stationary {n d : ℕ} (M : td_model n d)
    (θstar θ : td_vector d) :
    (∑ s, (M.stationary s).toReal * energy_state_center M θstar θ s) = 0 := by
  classical
  have hb :
      (∑ s, (M.stationary s).toReal •
        ∑ s', (M.transition s s').toReal • td_sample_vector M s s') =
        td_population_vector M := by
    ext i
    simp only [td_sample_vector, td_population_vector, Pi.smul_apply,
      Finset.sum_apply, Finset.smul_sum, smul_eq_mul]
    ring
  have hA :
      (∑ s, (M.stationary s).toReal •
        ∑ s', (M.transition s s').toReal •
          Matrix.mulVec (td_sample_matrix M s s') θ) =
        Matrix.mulVec (td_population_matrix M) θ := by
    ext i
    simp only [td_sample_matrix, td_population_matrix, Matrix.mulVec,
      Pi.smul_apply, Finset.sum_apply, Finset.smul_sum, smul_eq_mul,
      dotProduct, Finset.mul_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro s' hs'
    ring
  have hmean :
      (∑ s, (M.stationary s).toReal •
        ∑ s', (M.transition s s').toReal • td_update M θ s s') =
        td_mean_update M θ := by
    rw [td_mean_update, ← hb, ← hA]
    ext i
    simp only [td_update, Pi.smul_apply, Pi.sub_apply, Finset.sum_apply,
      Finset.smul_sum, smul_eq_mul]
    simp_rw [mul_sub, Finset.sum_sub_distrib]
  have hpmf (p : PMF (Fin n)) : ∑ s, (p s).toReal = 1 := by
    have hpenn : ∑ s, p s = 1 := by
      have hfin : HasSum (fun s : Fin n => p s) (∑ s, p s) :=
        hasSum_fintype (fun s : Fin n => p s)
      exact ((PMF.hasSum_coe_one p).unique hfin).symm
    rw [← ENNReal.toReal_sum]
    · rw [hpenn]
      norm_num
    · exact fun s hs => p.apply_ne_top s
  have hconst (v : td_vector d) :
      (∑ s, (M.stationary s).toReal •
        ∑ s', (M.transition s s').toReal • v) = v := by
    simp_rw [← Finset.sum_smul, hpmf]
    rw [← Finset.sum_smul, hpmf]
    simp
  have hcenter :
      (∑ s, (M.stationary s).toReal •
        ∑ s', (M.transition s s').toReal •
          (td_update M θ s s' - td_mean_update M θ)) = 0 := by
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [hmean, hconst]
    simp
  simp only [energy_state_center, energy_centered_scalar]
  calc
    (∑ s, (M.stationary s).toReal *
        ∑ s', (M.transition s s').toReal *
          ((td_update M θ s s' - td_mean_update M θ) ⬝ᵥ (θ - θstar))) =
        ((∑ s, (M.stationary s).toReal •
          ∑ s', (M.transition s s').toReal •
            (td_update M θ s s' - td_mean_update M θ)) ⬝ᵥ
              (θ - θstar)) := by
          simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul]
    _ = 0 := by
      rw [hcenter]
      simp

@[blueprint "lem:energy-geometric-envelope"
  (statement := /-- For every $\tau\geq1$, the geometric mixing envelope is summable and satisfies
  \[
  \sum_{k=0}^{\infty}2^{-k/\tau}\leq3\tau.
  \] -/)
  (proof := /-- Put $x=(\log2)/\tau$ and $q=e^{-x}=2^{-1/\tau}$.  Then $0<q<1$, so the series equals $(1-q)^{-1}$.  The inequality $1+x\leq e^x$ gives $q\leq(1+x)^{-1}$ and hence $(1-q)^{-1}\leq(1+x)/x$.  Applying $\log y\leq y-1$ to $y=1/2$ gives $\log2\geq1/2$; together with $\tau\geq1$, this implies $(1+x)/x\leq3\tau$. -/)
  (title := /-- Total mass of the geometric mixing envelope -/)
  (latexEnv := "lemma")]
lemma energy_geometric_envelope (τ : ℝ) (hτ : 1 ≤ τ) :
    Summable (fun k : ℕ => Real.rpow 2 (-((k : ℝ) / τ))) ∧
      (∑' k : ℕ, Real.rpow 2 (-((k : ℝ) / τ))) ≤ 3 * τ := by
  let x : ℝ := Real.log 2 / τ
  let q : ℝ := Real.rpow 2 (-(1 / τ))
  have hτpos : 0 < τ := lt_of_lt_of_le zero_lt_one hτ
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hxpos : 0 < x := div_pos hlogpos hτpos
  have hqexp : q = Real.exp (-x) := by
    dsimp [q]
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    dsimp [x]
    ring
  have hqpos : 0 < q := by rw [hqexp]; positivity
  have hqone : q < 1 := by
    rw [hqexp, Real.exp_lt_one_iff]
    linarith
  have hterm (k : ℕ) : Real.rpow 2 (-((k : ℝ) / τ)) = q ^ k := by
    dsimp [q]
    rw [show -((k : ℝ) / τ) = (-(1 / τ)) * (k : ℝ) by ring,
      Real.rpow_mul_natCast (by norm_num)]
  have hsumq : Summable (fun k : ℕ => q ^ k) :=
    summable_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs, abs_of_pos hqpos] using hqone)
  constructor
  · simpa only [hterm] using hsumq
  · rw [show (∑' k : ℕ, Real.rpow 2 (-((k : ℝ) / τ))) = ∑' k : ℕ, q ^ k by
      congr 1
      funext k
      exact hterm k]
    rw [tsum_geometric_of_lt_one hqpos.le hqone]
    have hexp : 1 + x ≤ Real.exp x := by
      simpa [add_comm] using Real.add_one_le_exp x
    have hexppos : 0 < Real.exp x := Real.exp_pos x
    have honexpos : 0 < 1 + x := by linarith
    have hqinv : q = (Real.exp x)⁻¹ := by
      rw [hqexp, Real.exp_neg]
    have hqinvl : q ≤ (1 + x)⁻¹ := by
      rw [hqinv]
      exact (inv_le_inv₀ hexppos honexpos).2 hexp
    have hden : x / (1 + x) ≤ 1 - q := by
      have hxfrac : x / (1 + x) = 1 - (1 + x)⁻¹ := by
        field_simp
        ring
      rw [hxfrac]
      linarith
    have hdenpos : 0 < 1 - q := sub_pos.mpr hqone
    have hfracpos : 0 < x / (1 + x) := div_pos hxpos honexpos
    have hinv : (1 - q)⁻¹ ≤ (x / (1 + x))⁻¹ :=
      (inv_le_inv₀ hdenpos hfracpos).2 hden
    have hloglower : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv] at h
      norm_num at h ⊢
      linarith
    have hlast : (x / (1 + x))⁻¹ ≤ 3 * τ := by
      rw [inv_div]
      dsimp [x]
      field_simp [ne_of_gt hτpos, ne_of_gt hlogpos]
      nlinarith
    exact hinv.trans hlast

@[blueprint "lem:energy-poisson-series"
  (statement := /-- Let $f\colon\operatorname{Fin}(n)\to\mathbb R$ have stationary mean zero and satisfy $|f(s)|\leq C$, where $C\geq0$.  Under the geometric-mixing bound with $\tau\geq1$, the series
  \[
  u(s)=\sum_{k=0}^{\infty}\sum_j((P^k)_{sj}-\pi_j)f(j)
  \]
  converges, satisfies $|u(s)|\leq24C\tau$, and solves $u-Pu=f$. -/)
  (proof := /-- The mixing hypothesis bounds the absolute value of the $k$th summand by $8C2^{-k/\tau}$.  Comparison with \cref{lem:energy-geometric-envelope} proves convergence and the bound $24C\tau$.  Multiplication by $P$ shifts the summand from $k$ to $k+1$, using that every transition row has mass one.  Subtracting the shifted series leaves its zeroth term, which equals $f$ because the stationary mean of $f$ is zero. -/)
  (title := /-- Bounded finite-state Poisson solution under geometric mixing -/)
  (latexEnv := "lemma")]
lemma energy_poisson_series {n d : ℕ} (M : td_model n d) (τ C : ℝ)
    (f : Fin n → ℝ) (hmix : td_geometric_mixing M τ)
    (hC : 0 ≤ C) (hf : ∀ s, |f s| ≤ C)
    (hzero : ∑ s, (M.stationary s).toReal * f s = 0) :
    (∀ s, Summable (fun k : ℕ =>
      ∑ j, ((td_transition_matrix M ^ k) s j - (M.stationary j).toReal) * f j)) ∧
    (∀ s, |∑' k : ℕ,
      ∑ j, ((td_transition_matrix M ^ k) s j - (M.stationary j).toReal) * f j| ≤
        24 * C * τ) ∧
    (∀ s,
      (∑' k : ℕ,
        ∑ j, ((td_transition_matrix M ^ k) s j - (M.stationary j).toReal) * f j) -
        ∑ j, (M.transition s j).toReal *
          (∑' k : ℕ,
            ∑ l, ((td_transition_matrix M ^ k) j l -
              (M.stationary l).toReal) * f l) = f s) := by
  classical
  have hτ : 1 ≤ τ := hmix.1
  have hgeom := energy_geometric_envelope τ hτ
  have hterm (k : ℕ) (s : Fin n) :
      |∑ j, ((td_transition_matrix M ^ k) s j -
          (M.stationary j).toReal) * f j| ≤
        8 * C * Real.rpow 2 (-((k : ℝ) / τ)) := by
    calc
      |∑ j, ((td_transition_matrix M ^ k) s j -
          (M.stationary j).toReal) * f j| ≤
          ∑ j, |((td_transition_matrix M ^ k) s j -
            (M.stationary j).toReal) * f j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |(td_transition_matrix M ^ k) s j -
            (M.stationary j).toReal| * C := by
          apply Finset.sum_le_sum
          intro j hj
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hf j) (abs_nonneg _)
      _ = C * ∑ j, |(td_transition_matrix M ^ k) s j -
            (M.stationary j).toReal| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
      _ ≤ C * (8 * Real.rpow 2 (-((k : ℝ) / τ))) :=
          mul_le_mul_of_nonneg_left (hmix.2 k s) hC
      _ = 8 * C * Real.rpow 2 (-((k : ℝ) / τ)) := by ring
  have hsummable (s : Fin n) : Summable (fun k : ℕ =>
      ∑ j, ((td_transition_matrix M ^ k) s j -
        (M.stationary j).toReal) * f j) := by
    apply Summable.of_norm_bounded (hgeom.1.mul_left (8 * C))
    intro k
    rw [Real.norm_eq_abs]
    exact hterm k s
  have hbound (s : Fin n) :
      |∑' k : ℕ, ∑ j, ((td_transition_matrix M ^ k) s j -
          (M.stationary j).toReal) * f j| ≤ 24 * C * τ := by
    calc
      |∑' k : ℕ, ∑ j, ((td_transition_matrix M ^ k) s j -
          (M.stationary j).toReal) * f j| ≤
          ∑' k : ℕ, |∑ j, ((td_transition_matrix M ^ k) s j -
            (M.stationary j).toReal) * f j| := by
              simpa only [Real.norm_eq_abs] using
                norm_tsum_le_tsum_norm (f := fun k : ℕ =>
                  ∑ j, ((td_transition_matrix M ^ k) s j -
                    (M.stationary j).toReal) * f j) ((hsummable s).norm)
      _ ≤ ∑' k : ℕ, 8 * C * Real.rpow 2 (-((k : ℝ) / τ)) := by
          exact Summable.tsum_le_tsum (fun k => hterm k s) (hsummable s).norm
            (hgeom.1.mul_left (8 * C))
      _ = 8 * C * (∑' k : ℕ, Real.rpow 2 (-((k : ℝ) / τ))) := by
          rw [tsum_mul_left]
      _ ≤ 24 * C * τ := by
          have := hgeom.2
          nlinarith
  refine ⟨hsummable, hbound, ?_⟩
  intro s
  let g : ℕ → Fin n → ℝ := fun k i =>
    ∑ j, ((td_transition_matrix M ^ k) i j -
      (M.stationary j).toReal) * f j
  have hrow (i : Fin n) : ∑ j, (M.transition i j).toReal = 1 := by
    have hpenn : ∑ j, M.transition i j = 1 := by
      have hfin : HasSum (fun j : Fin n => M.transition i j)
          (∑ j, M.transition i j) := hasSum_fintype _
      exact ((PMF.hasSum_coe_one (M.transition i)).unique hfin).symm
    rw [← ENNReal.toReal_sum]
    · rw [hpenn]
      norm_num
    · exact fun j hj => (M.transition i).apply_ne_top j
  have hstep (k : ℕ) (i : Fin n) :
      ∑ j, (M.transition i j).toReal * g k j = g (k + 1) i := by
    change ∑ j, td_transition_matrix M i j * g k j = g (k + 1) i
    dsimp only [g]
    rw [pow_succ']
    simp only [Matrix.mul_apply]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    change ∑ x, (M.transition i x).toReal *
        (((td_transition_matrix M ^ k) x l - (M.stationary l).toReal) * f l) =
      (∑ j, (M.transition i j).toReal * (td_transition_matrix M ^ k) j l -
        (M.stationary l).toReal) * f l
    have hinner :
        ∑ x, (M.transition i x).toReal *
            ((td_transition_matrix M ^ k) x l - (M.stationary l).toReal) =
          ∑ j, (M.transition i j).toReal * (td_transition_matrix M ^ k) j l -
            (M.stationary l).toReal := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      rw [← Finset.sum_mul, hrow]
      ring
    calc
      _ = (∑ x, (M.transition i x).toReal *
          ((td_transition_matrix M ^ k) x l - (M.stationary l).toReal)) * f l := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = _ := by rw [hinner]
  have hshift :
      ∑ j, (M.transition s j).toReal * (∑' k : ℕ, g k j) =
        ∑' k : ℕ, g (k + 1) s := by
    have hinter :
        (∑' k : ℕ, ∑ j, (M.transition s j).toReal * g k j) =
          ∑ j, (M.transition s j).toReal * (∑' k : ℕ, g k j) := by
      simpa only [tsum_mul_left] using Summable.tsum_finsetSum
        (s := Finset.univ)
        (f := fun j : Fin n => fun k : ℕ => (M.transition s j).toReal * g k j)
        (fun j hj => (hsummable j).mul_left ((M.transition s j).toReal))
    rw [← hinter]
    apply tsum_congr
    intro k
    exact hstep k s
  change (∑' k : ℕ, g k s) - ∑ j, (M.transition s j).toReal *
      (∑' k : ℕ, g k j) = f s
  rw [hshift]
  have hsplit : g 0 s + (∑' k : ℕ, g (k + 1) s) = ∑' k : ℕ, g k s := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.zero_add]
      using (hsummable s).sum_add_tsum_nat_add 1
  rw [← hsplit]
  have hgzero : g 0 s = f s := by
    dsimp only [g]
    simp only [pow_zero]
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    rw [hzero]
    simp only [sub_zero]
    change (∑ x, (if s = x then 1 else 0) * f x) = f s
    simp
  rw [hgzero]
  ring

@[blueprint "lem:energy-sample-update-bound"
  (statement := /-- Let $M$ satisfy the uniform bounds with constants $\phi_infty,r_infty$.  If $r_infty\leq\phi_infty B$, $2B\leq R$, and $\lVert\theta\rVert_2\leq R$, then every sample update satisfies
  \[
  \lVert g(\theta,(s,s'))\rVert_2\leq\frac52\phi_infty^2R.
  \] -/)
  (proof := /-- The reward vector has norm at most $r_\infty\phi_\infty\leq\frac12\phi_\infty^2R$.  The sample matrix is the outer product $\phi(s)(\phi(s)-\gamma\phi(s'))^\top$; Cauchy--Schwarz, $0\leq\gamma<1$, the scalar-multiplication identity \cref{lem:energy-td-euclidean-norm-smul}, and the dot-product bound \cref{lem:energy-td-dot-product-bound} bound its action on $\theta$ by $2\phi_\infty^2R$.  The difference triangle inequality \cref{lem:energy-td-euclidean-norm-sub} gives the result. -/)
  (title := /-- Uniform sample-update bound inside the stopping radius -/)
  (latexEnv := "lemma")]
lemma energy_sample_update_bound {n d : ℕ} (M : td_model n d)
    (φinf rinf B R : ℝ) (θ : td_vector d) (s s' : Fin n)
    (hbounds : td_uniform_bounds M φinf rinf)
    (hrB : rinf ≤ φinf * B) (hBR : 2 * B ≤ R)
    (hθ : td_euclidean_norm θ ≤ R) :
    td_euclidean_norm (td_update M θ s s') ≤ (5 / 2 : ℝ) * φinf ^ 2 * R := by
  have hφpos : 0 < φinf := hbounds.1
  have hrnonneg : 0 ≤ rinf := hbounds.2.1
  have hφs := hbounds.2.2.1 s
  have hφs' := hbounds.2.2.1 s'
  have hr := hbounds.2.2.2 s s'
  have hB : 0 ≤ B := by nlinarith
  have hR : 0 ≤ R := by nlinarith
  have hθnonneg : 0 ≤ td_euclidean_norm θ := Real.sqrt_nonneg _
  have hγabs : |M.discount| ≤ 1 := by
    rw [abs_of_nonneg M.discount_nonneg]
    exact M.discount_lt_one.le
  have hφsnonneg : 0 ≤ td_euclidean_norm (M.feature s) := Real.sqrt_nonneg _
  have hφs'nonneg : 0 ≤ td_euclidean_norm (M.feature s') := Real.sqrt_nonneg _
  have hdiff :
      td_euclidean_norm (M.feature s - M.discount • M.feature s') ≤ 2 * φinf := by
    calc
      td_euclidean_norm (M.feature s - M.discount • M.feature s') ≤
          td_euclidean_norm (M.feature s) +
            td_euclidean_norm (M.discount • M.feature s') :=
        energy_td_euclidean_norm_sub _ _
      _ = td_euclidean_norm (M.feature s) +
          |M.discount| * td_euclidean_norm (M.feature s') := by
            rw [energy_td_euclidean_norm_smul]
      _ ≤ φinf + 1 * φinf := by
        have hm := mul_le_mul hγabs hφs' hφs'nonneg (by norm_num)
        nlinarith
      _ = 2 * φinf := by ring
  have hmat : Matrix.mulVec (td_sample_matrix M s s') θ =
      ((M.feature s - M.discount • M.feature s') ⬝ᵥ θ) • M.feature s := by
    ext i
    simp only [td_sample_matrix, Matrix.mulVec, dotProduct, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hmatnorm :
      td_euclidean_norm (Matrix.mulVec (td_sample_matrix M s s') θ) ≤
        2 * φinf ^ 2 * R := by
    rw [hmat, energy_td_euclidean_norm_smul]
    have hdot := energy_td_dot_product_bound
      (M.feature s - M.discount • M.feature s') θ
    have habsdot :
        |(M.feature s - M.discount • M.feature s') ⬝ᵥ θ| ≤
          2 * φinf * R := hdot.trans (mul_le_mul hdiff hθ
            (Real.sqrt_nonneg _) (by positivity))
    have hp := mul_le_mul habsdot hφs hφsnonneg
      (mul_nonneg (mul_nonneg (by positivity) hφpos.le) hR)
    nlinarith
  have hbvec :
      td_euclidean_norm (td_sample_vector M s s') ≤
        (1 / 2 : ℝ) * φinf ^ 2 * R := by
    rw [td_sample_vector, energy_td_euclidean_norm_smul]
    have habsr : |M.reward s s'| ≤ rinf := hr
    have hp := mul_le_mul habsr hφs hφsnonneg hrnonneg
    nlinarith [mul_nonneg hφpos.le hB, sq_nonneg φinf]
  rw [td_update]
  exact (energy_td_euclidean_norm_sub _ _).trans (by nlinarith)

@[blueprint "lem:energy-mean-update-average"
  (statement := /-- For every finite TD model and parameter $\theta$, the population mean update is the stationary transition average of the sample update:
  \[
  \bar g(\theta)=\sum_{s,s'}\pi(s)P(s,s')g(\theta,(s,s')).
  \] -/)
  (proof := /-- Expand \cref{def:td-update,def:td-mean-update}.  The reward-vector terms sum to \cref{def:td-population-vector}; distributing matrix--vector multiplication through the finite sums shows that the sample-matrix terms sum to \cref{def:td-population-matrix} applied to $\theta$. -/)
  (title := /-- Stationary representation of the population TD update -/)
  (latexEnv := "lemma")]
lemma energy_mean_update_average {n d : ℕ} (M : td_model n d) (θ : td_vector d) :
    td_mean_update M θ =
      ∑ s, (M.stationary s).toReal •
        ∑ s', (M.transition s s').toReal • td_update M θ s s' := by
  classical
  have hb :
      (∑ s, (M.stationary s).toReal •
        ∑ s', (M.transition s s').toReal • td_sample_vector M s s') =
        td_population_vector M := by
    ext i
    simp only [td_sample_vector, td_population_vector, Pi.smul_apply,
      Finset.sum_apply, Finset.smul_sum, smul_eq_mul]
    ring
  have hA :
      (∑ s, (M.stationary s).toReal •
        ∑ s', (M.transition s s').toReal •
          Matrix.mulVec (td_sample_matrix M s s') θ) =
        Matrix.mulVec (td_population_matrix M) θ := by
    ext i
    simp only [td_sample_matrix, td_population_matrix, Matrix.mulVec,
      Pi.smul_apply, Finset.sum_apply, Finset.smul_sum, smul_eq_mul,
      dotProduct, Finset.mul_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro s' hs'
    ring
  rw [td_mean_update, ← hb, ← hA]
  ext i
  simp only [td_update, Pi.smul_apply, Pi.sub_apply, Finset.sum_apply,
    Finset.smul_sum, smul_eq_mul]
  simp_rw [mul_sub, Finset.sum_sub_distrib]

@[blueprint "lem:energy-mean-update-bound"
  (statement := /-- Under the hypotheses of \cref{lem:energy-sample-update-bound}, the population mean update obeys the same estimate:
  \[
  \lVert\bar g(\theta)\rVert_2\leq\frac52\phi_\infty^2R.
  \] -/)
  (proof := /-- Use the stationary-average identity \cref{lem:energy-mean-update-average}.  Apply the triangle inequality from \cref{lem:energy-td-euclidean-norm-bridge} to both finite convex sums, use \cref{lem:energy-sample-update-bound} for every summand, and use that the stationary law and every transition row have total mass one. -/)
  (title := /-- Uniform population-update bound inside the stopping radius -/)
  (latexEnv := "lemma")]
lemma energy_mean_update_bound {n d : ℕ} (M : td_model n d)
    (φinf rinf B R : ℝ) (θ : td_vector d)
    (hbounds : td_uniform_bounds M φinf rinf)
    (hrB : rinf ≤ φinf * B) (hBR : 2 * B ≤ R)
    (hθ : td_euclidean_norm θ ≤ R) :
    td_euclidean_norm (td_mean_update M θ) ≤ (5 / 2 : ℝ) * φinf ^ 2 * R := by
  classical
  have hsum (w : Fin n → ℝ) (v : Fin n → td_vector d) :
      td_euclidean_norm (∑ i, w i • v i) ≤
        ∑ i, |w i| * td_euclidean_norm (v i) := by
    let L : td_vector d ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
    rw [energy_td_euclidean_norm_bridge]
    change ‖L (∑ i, w i • v i)‖ ≤ ∑ i, |w i| * td_euclidean_norm (v i)
    rw [map_sum]
    calc
      ‖∑ i, L (w i • v i)‖ ≤ ∑ i, ‖L (w i • v i)‖ := norm_sum_le _ _
      _ = ∑ i, |w i| * td_euclidean_norm (v i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_smul, norm_smul, Real.norm_eq_abs,
          energy_td_euclidean_norm_bridge]
  have hpmf (p : PMF (Fin n)) : ∑ s, (p s).toReal = 1 := by
    have hpenn : ∑ s, p s = 1 := by
      have hfin : HasSum (fun s : Fin n => p s) (∑ s, p s) :=
        hasSum_fintype (fun s : Fin n => p s)
      exact ((PMF.hasSum_coe_one p).unique hfin).symm
    rw [← ENNReal.toReal_sum]
    · rw [hpenn]
      norm_num
    · exact fun s hs => p.apply_ne_top s
  rw [energy_mean_update_average]
  have hinner (s : Fin n) :
      td_euclidean_norm
          (∑ s', (M.transition s s').toReal • td_update M θ s s') ≤
        ∑ s', (M.transition s s').toReal * ((5 / 2 : ℝ) * φinf ^ 2 * R) := by
    refine (hsum _ _).trans ?_
    apply Finset.sum_le_sum
    intro s' hs'
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul_of_nonneg_left
      (energy_sample_update_bound M φinf rinf B R θ s s' hbounds hrB hBR hθ)
      ENNReal.toReal_nonneg
  calc
    td_euclidean_norm
        (∑ s, (M.stationary s).toReal •
          ∑ s', (M.transition s s').toReal • td_update M θ s s') ≤
      ∑ s, |(M.stationary s).toReal| *
        td_euclidean_norm
          (∑ s', (M.transition s s').toReal • td_update M θ s s') := hsum _ _
    _ ≤ ∑ s, (M.stationary s).toReal *
        (∑ s', (M.transition s s').toReal *
          ((5 / 2 : ℝ) * φinf ^ 2 * R)) := by
      apply Finset.sum_le_sum
      intro s hs
      rw [abs_of_nonneg ENNReal.toReal_nonneg]
      gcongr
      exact hinner s
    _ = (5 / 2 : ℝ) * φinf ^ 2 * R := by
      simp_rw [← Finset.sum_mul, hpmf]
      rw [← Finset.sum_mul, hpmf]
      ring

@[blueprint "lem:energy-centered-observable-bound"
  (statement := /-- Suppose $\lVert\theta^*\rVert_2\leq B$, $r_\infty\leq\phi_\infty B$, $2B\leq R$, and $\lVert\theta\rVert_2\leq R$.  Under the uniform and mixing bounds, the centered energy observable, its one-step state average, and its Poisson solution satisfy
  \[
  |h_\theta(s,s')|\leq\frac{15}{2}\phi_\infty^2R^2,
  \quad |f_\theta(s)|\leq\frac{15}{2}\phi_\infty^2R^2,
  \quad |u_\theta(s)|\leq180\tau\phi_\infty^2R^2,
  \]
  and $u_\theta-Pu_\theta=f_\theta$. -/)
  (proof := /-- By \cref{lem:energy-sample-update-bound,lem:energy-mean-update-bound}, the centered update has norm at most $5\phi_\infty^2R$.  The error vector has norm at most $R+B\leq3R/2$ by \cref{lem:energy-td-euclidean-norm-sub}; Cauchy--Schwarz from \cref{lem:energy-td-dot-product-bound} yields the bound on $h_\theta$.  Averaging against a transition probability gives the same bound on $f_\theta$.  Its stationary mean is zero by \cref{lem:energy-state-center-stationary}, so \cref{lem:energy-poisson-series} gives the Poisson identity and the bound $24(15/2)=180$. -/)
  (title := /-- Bounds and Poisson identity for the stopped energy observable -/)
  (latexEnv := "lemma")]
lemma energy_centered_observable_bound {n d : ℕ} (M : td_model n d)
    (τ φinf rinf B R : ℝ) (θstar θ : td_vector d)
    (hbounds : td_uniform_bounds M φinf rinf)
    (hmix : td_geometric_mixing M τ)
    (hstar : td_euclidean_norm θstar ≤ B)
    (hrB : rinf ≤ φinf * B) (hBR : 2 * B ≤ R)
    (hθ : td_euclidean_norm θ ≤ R) :
    (∀ s s', |energy_centered_scalar M θstar θ s s'| ≤
      (15 / 2 : ℝ) * φinf ^ 2 * R ^ 2) ∧
    (∀ s, |energy_state_center M θstar θ s| ≤
      (15 / 2 : ℝ) * φinf ^ 2 * R ^ 2) ∧
    (∀ s, |energy_poisson_solution M θstar θ s| ≤
      180 * τ * φinf ^ 2 * R ^ 2) ∧
    (∀ s, energy_poisson_solution M θstar θ s -
      ∑ j, (M.transition s j).toReal * energy_poisson_solution M θstar θ j =
        energy_state_center M θstar θ s) := by
  classical
  have hφpos : 0 < φinf := hbounds.1
  have hB : 0 ≤ B := by
    exact (Real.sqrt_nonneg _).trans hstar
  have hR : 0 ≤ R := by nlinarith
  have herr : td_euclidean_norm (θ - θstar) ≤ (3 / 2 : ℝ) * R := by
    refine (energy_td_euclidean_norm_sub θ θstar).trans ?_
    nlinarith
  have hsample (s s' : Fin n) :
      td_euclidean_norm (td_update M θ s s') ≤ (5 / 2 : ℝ) * φinf ^ 2 * R :=
    energy_sample_update_bound M φinf rinf B R θ s s' hbounds hrB hBR hθ
  have hmean : td_euclidean_norm (td_mean_update M θ) ≤
      (5 / 2 : ℝ) * φinf ^ 2 * R :=
    energy_mean_update_bound M φinf rinf B R θ hbounds hrB hBR hθ
  have hh (s s' : Fin n) : |energy_centered_scalar M θstar θ s s'| ≤
      (15 / 2 : ℝ) * φinf ^ 2 * R ^ 2 := by
    rw [energy_centered_scalar]
    refine (energy_td_dot_product_bound _ _).trans ?_
    have hcent := energy_td_euclidean_norm_sub
      (td_update M θ s s') (td_mean_update M θ)
    have hcent' : td_euclidean_norm (td_update M θ s s' - td_mean_update M θ) ≤
        5 * φinf ^ 2 * R := by
      exact hcent.trans (by nlinarith [hsample s s'])
    nlinarith [mul_le_mul hcent' herr (Real.sqrt_nonneg _)
      (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg φinf)) hR)]
  have hpmf (p : PMF (Fin n)) : ∑ s, (p s).toReal = 1 := by
    have hpenn : ∑ s, p s = 1 := by
      have hfin : HasSum (fun s : Fin n => p s) (∑ s, p s) :=
        hasSum_fintype (fun s : Fin n => p s)
      exact ((PMF.hasSum_coe_one p).unique hfin).symm
    rw [← ENNReal.toReal_sum]
    · rw [hpenn]
      norm_num
    · exact fun s hs => p.apply_ne_top s
  have hf (s : Fin n) : |energy_state_center M θstar θ s| ≤
      (15 / 2 : ℝ) * φinf ^ 2 * R ^ 2 := by
    rw [energy_state_center]
    calc
      |∑ s', (M.transition s s').toReal * energy_centered_scalar M θstar θ s s'| ≤
          ∑ s', |(M.transition s s').toReal *
            energy_centered_scalar M θstar θ s s'| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s', (M.transition s s').toReal *
          ((15 / 2 : ℝ) * φinf ^ 2 * R ^ 2) := by
        apply Finset.sum_le_sum
        intro s' hs'
        rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
        exact mul_le_mul_of_nonneg_left (hh s s') ENNReal.toReal_nonneg
      _ = (15 / 2 : ℝ) * φinf ^ 2 * R ^ 2 := by
        rw [← Finset.sum_mul, hpmf]
        ring
  have hC : 0 ≤ (15 / 2 : ℝ) * φinf ^ 2 * R ^ 2 := by positivity
  have hp := energy_poisson_series M τ
    ((15 / 2 : ℝ) * φinf ^ 2 * R ^ 2)
    (energy_state_center M θstar θ) hmix hC hf
    (energy_state_center_stationary M θstar θ)
  refine ⟨hh, hf, ?_, ?_⟩
  · intro s
    change |∑' k : ℕ, ∑ j, ((td_transition_matrix M ^ k) s j -
      (M.stationary j).toReal) * energy_state_center M θstar θ j| ≤ _
    have := hp.2.1 s
    nlinarith
  · intro s
    exact hp.2.2 s

@[blueprint "lem:energy-update-difference-bound"
  (statement := /-- Under the uniform feature bound, for every $\theta,\theta'\in\mathbb R^d$ and transition $(s,s')$,
  \[
  \lVert g(\theta,(s,s'))-g(\theta',(s,s'))\rVert_2
  \leq2\phi_\infty^2\lVert\theta-\theta'\rVert_2,
  \]
  and the same bound holds for $\lVert\bar g(\theta)-\bar g(\theta')\rVert_2$. -/)
  (proof := /-- The sample-update difference is the sample matrix applied to $\theta-\theta'$.  Its outer-product form, Cauchy--Schwarz from \cref{lem:energy-td-dot-product-bound}, and the norm identities \cref{lem:energy-td-euclidean-norm-sub,lem:energy-td-euclidean-norm-smul} give the first estimate.  Average this estimate using \cref{lem:energy-mean-update-average,lem:energy-td-euclidean-norm-bridge} and the unit masses of the transition and stationary laws to obtain the population estimate. -/)
  (title := /-- Lipschitz bounds for sample and population TD updates -/)
  (latexEnv := "lemma")]
lemma energy_update_difference_bound {n d : ℕ} (M : td_model n d)
    (φinf rinf : ℝ) (θ θ' : td_vector d)
    (hbounds : td_uniform_bounds M φinf rinf) :
    (∀ s s', td_euclidean_norm (td_update M θ s s' - td_update M θ' s s') ≤
      2 * φinf ^ 2 * td_euclidean_norm (θ - θ')) ∧
    td_euclidean_norm (td_mean_update M θ - td_mean_update M θ') ≤
      2 * φinf ^ 2 * td_euclidean_norm (θ - θ') := by
  classical
  have hφpos : 0 < φinf := hbounds.1
  have hmatrix (v : td_vector d) (s s' : Fin n) :
      td_euclidean_norm (Matrix.mulVec (td_sample_matrix M s s') v) ≤
        2 * φinf ^ 2 * td_euclidean_norm v := by
    have hφs := hbounds.2.2.1 s
    have hφs' := hbounds.2.2.1 s'
    have hγabs : |M.discount| ≤ 1 := by
      rw [abs_of_nonneg M.discount_nonneg]
      exact M.discount_lt_one.le
    have hdiff :
        td_euclidean_norm (M.feature s - M.discount • M.feature s') ≤ 2 * φinf := by
      calc
        td_euclidean_norm (M.feature s - M.discount • M.feature s') ≤
            td_euclidean_norm (M.feature s) +
              td_euclidean_norm (M.discount • M.feature s') :=
          energy_td_euclidean_norm_sub _ _
        _ = td_euclidean_norm (M.feature s) +
            |M.discount| * td_euclidean_norm (M.feature s') := by
              rw [energy_td_euclidean_norm_smul]
        _ ≤ φinf + φinf := by
          have hm := mul_le_mul hγabs hφs' (Real.sqrt_nonneg _) (by norm_num)
          nlinarith
        _ = 2 * φinf := by ring
    have hmat : Matrix.mulVec (td_sample_matrix M s s') v =
        ((M.feature s - M.discount • M.feature s') ⬝ᵥ v) • M.feature s := by
      ext i
      simp only [td_sample_matrix, Matrix.mulVec, dotProduct, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hmat, energy_td_euclidean_norm_smul]
    have hdot := energy_td_dot_product_bound
      (M.feature s - M.discount • M.feature s') v
    have habsdot : |(M.feature s - M.discount • M.feature s') ⬝ᵥ v| ≤
        2 * φinf * td_euclidean_norm v :=
      hdot.trans (mul_le_mul hdiff le_rfl (Real.sqrt_nonneg _) (by positivity))
    have hp := mul_le_mul habsdot hφs (Real.sqrt_nonneg _)
      (mul_nonneg (mul_nonneg (by positivity) hφpos.le) (Real.sqrt_nonneg _))
    nlinarith
  have hsample (s s' : Fin n) :
      td_euclidean_norm (td_update M θ s s' - td_update M θ' s s') ≤
        2 * φinf ^ 2 * td_euclidean_norm (θ - θ') := by
    have heq : td_update M θ s s' - td_update M θ' s s' =
        -(Matrix.mulVec (td_sample_matrix M s s') (θ - θ')) := by
      ext i
      simp only [td_update, Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.neg_apply]
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      ring
    rw [heq, show -(Matrix.mulVec (td_sample_matrix M s s') (θ - θ')) =
      (-1 : ℝ) • Matrix.mulVec (td_sample_matrix M s s') (θ - θ') by ext i; simp,
      energy_td_euclidean_norm_smul]
    norm_num
    exact hmatrix _ s s'
  have hsum (w : Fin n → ℝ) (v : Fin n → td_vector d) :
      td_euclidean_norm (∑ i, w i • v i) ≤
        ∑ i, |w i| * td_euclidean_norm (v i) := by
    let L : td_vector d ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
    rw [energy_td_euclidean_norm_bridge]
    change ‖L (∑ i, w i • v i)‖ ≤ ∑ i, |w i| * td_euclidean_norm (v i)
    rw [map_sum]
    calc
      ‖∑ i, L (w i • v i)‖ ≤ ∑ i, ‖L (w i • v i)‖ := norm_sum_le _ _
      _ = ∑ i, |w i| * td_euclidean_norm (v i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_smul, norm_smul, Real.norm_eq_abs,
          energy_td_euclidean_norm_bridge]
  have hpmf (p : PMF (Fin n)) : ∑ s, (p s).toReal = 1 := by
    have hpenn : ∑ s, p s = 1 := by
      have hfin : HasSum (fun s : Fin n => p s) (∑ s, p s) :=
        hasSum_fintype (fun s : Fin n => p s)
      exact ((PMF.hasSum_coe_one p).unique hfin).symm
    rw [← ENNReal.toReal_sum]
    · rw [hpenn]
      norm_num
    · exact fun s hs => p.apply_ne_top s
  have hmean_eq : td_mean_update M θ - td_mean_update M θ' =
      ∑ s, (M.stationary s).toReal •
        ∑ s', (M.transition s s').toReal •
          (td_update M θ s s' - td_update M θ' s s') := by
    rw [energy_mean_update_average, energy_mean_update_average]
    ext i
    simp only [Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, Finset.smul_sum,
      smul_eq_mul]
    simp_rw [mul_sub, Finset.sum_sub_distrib]
  constructor
  · exact hsample
  · rw [hmean_eq]
    refine (hsum _ _).trans ?_
    calc
      (∑ s, |(M.stationary s).toReal| *
          td_euclidean_norm
            (∑ s', (M.transition s s').toReal •
              (td_update M θ s s' - td_update M θ' s s'))) ≤
          ∑ s, (M.stationary s).toReal *
            (∑ s', (M.transition s s').toReal *
              (2 * φinf ^ 2 * td_euclidean_norm (θ - θ'))) := by
        apply Finset.sum_le_sum
        intro s hs
        rw [abs_of_nonneg ENNReal.toReal_nonneg]
        gcongr
        refine (hsum _ _).trans ?_
        apply Finset.sum_le_sum
        intro s' hs'
        rw [abs_of_nonneg ENNReal.toReal_nonneg]
        exact mul_le_mul_of_nonneg_left (hsample s s') ENNReal.toReal_nonneg
      _ = 2 * φinf ^ 2 * td_euclidean_norm (θ - θ') := by
        simp_rw [← Finset.sum_mul, hpmf]
        rw [← Finset.sum_mul, hpmf]
        ring

@[blueprint "lem:energy-poisson-lipschitz"
  (statement := /-- Under the uniform and mixing bounds, suppose $\lVert\theta^*\rVert_2\leq B$, $r_\infty\leq\phi_\infty B$, $2B\leq R$, and both $\theta$ and $\theta'$ lie in the radius-$R$ ball.  Then
  \[
  |u_\theta(s)-u_{\theta'}(s)|
  \leq264\tau\phi_\infty^2R\lVert\theta-\theta'\rVert_2.
  \] -/)
  (proof := /-- Expand the difference of the two centered scalar observables.  The update-difference estimates in \cref{lem:energy-update-difference-bound} contribute $4\phi_\infty^2\lVert\theta-\theta'\rVert_2$, while the difference triangle inequality \cref{lem:energy-td-euclidean-norm-sub} bounds each error vector by $3R/2$; the remaining centered update is bounded using \cref{lem:energy-sample-update-bound,lem:energy-mean-update-bound}.  Cauchy--Schwarz from \cref{lem:energy-td-dot-product-bound} gives
  $|f_\theta-f_{\theta'}|\leq11\phi_\infty^2R\lVert\theta-\theta'\rVert_2$.  The difference has stationary mean zero by \cref{lem:energy-state-center-stationary}; applying \cref{lem:energy-poisson-series} gives the factor $24\cdot11=264$.  The individual Poisson series are summable by the observable bounds in \cref{lem:energy-centered-observable-bound}, so their difference is the Poisson series of $f_\theta-f_{\theta'}$. -/)
  (title := /-- Lipschitz continuity of the energy Poisson solution -/)
  (latexEnv := "lemma")]
lemma energy_poisson_lipschitz {n d : ℕ} (M : td_model n d)
    (τ φinf rinf B R : ℝ) (θstar θ θ' : td_vector d)
    (hbounds : td_uniform_bounds M φinf rinf)
    (hmix : td_geometric_mixing M τ)
    (hstar : td_euclidean_norm θstar ≤ B)
    (hrB : rinf ≤ φinf * B) (hBR : 2 * B ≤ R)
    (hθ : td_euclidean_norm θ ≤ R) (hθ' : td_euclidean_norm θ' ≤ R) :
    ∀ s, |energy_poisson_solution M θstar θ s -
      energy_poisson_solution M θstar θ' s| ≤
        264 * τ * φinf ^ 2 * R * td_euclidean_norm (θ - θ') := by
  classical
  have hφpos : 0 < φinf := hbounds.1
  have hB : 0 ≤ B := (Real.sqrt_nonneg _).trans hstar
  have hR : 0 ≤ R := by nlinarith
  have hδnorm : 0 ≤ td_euclidean_norm (θ - θ') := Real.sqrt_nonneg _
  have herr (v : td_vector d) (hv : td_euclidean_norm v ≤ R) :
      td_euclidean_norm (v - θstar) ≤ (3 / 2 : ℝ) * R := by
    refine (energy_td_euclidean_norm_sub v θstar).trans ?_
    nlinarith
  have hdiff := energy_update_difference_bound M φinf rinf θ θ' hbounds
  have hcentdiff (s s' : Fin n) :
      td_euclidean_norm
        ((td_update M θ s s' - td_mean_update M θ) -
          (td_update M θ' s s' - td_mean_update M θ')) ≤
        4 * φinf ^ 2 * td_euclidean_norm (θ - θ') := by
    have hs := hdiff.1 s s'
    have hm := hdiff.2
    have heq :
        (td_update M θ s s' - td_mean_update M θ) -
          (td_update M θ' s s' - td_mean_update M θ') =
        (td_update M θ s s' - td_update M θ' s s') -
          (td_mean_update M θ - td_mean_update M θ') := by
      abel
    rw [heq]
    exact (energy_td_euclidean_norm_sub _ _).trans (by nlinarith)
  have hcenter' (s s' : Fin n) :
      td_euclidean_norm (td_update M θ' s s' - td_mean_update M θ') ≤
        5 * φinf ^ 2 * R := by
    refine (energy_td_euclidean_norm_sub _ _).trans ?_
    have hs := energy_sample_update_bound M φinf rinf B R θ' s s'
      hbounds hrB hBR hθ'
    have hm := energy_mean_update_bound M φinf rinf B R θ'
      hbounds hrB hBR hθ'
    nlinarith
  have hh (s s' : Fin n) :
      |energy_centered_scalar M θstar θ s s' -
        energy_centered_scalar M θstar θ' s s'| ≤
        11 * φinf ^ 2 * R * td_euclidean_norm (θ - θ') := by
    have heq :
        energy_centered_scalar M θstar θ s s' -
          energy_centered_scalar M θstar θ' s s' =
        (((td_update M θ s s' - td_mean_update M θ) -
            (td_update M θ' s s' - td_mean_update M θ')) ⬝ᵥ (θ - θstar)) +
          ((td_update M θ' s s' - td_mean_update M θ') ⬝ᵥ (θ - θ')) := by
      simp only [energy_centered_scalar, dotProduct, Pi.sub_apply]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [heq]
    refine (abs_add_le _ _).trans ?_
    have hfirst := energy_td_dot_product_bound
      ((td_update M θ s s' - td_mean_update M θ) -
        (td_update M θ' s s' - td_mean_update M θ')) (θ - θstar)
    have hsecond := energy_td_dot_product_bound
      (td_update M θ' s s' - td_mean_update M θ') (θ - θ')
    have hfirst' := hfirst.trans (mul_le_mul (hcentdiff s s') (herr θ hθ)
      (Real.sqrt_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg φinf)) hδnorm))
    have hsecond' := hsecond.trans (mul_le_mul (hcenter' s s') le_rfl
      hδnorm (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg φinf)) hR))
    nlinarith [sq_nonneg φinf]
  have hpmf (p : PMF (Fin n)) : ∑ s, (p s).toReal = 1 := by
    have hpenn : ∑ s, p s = 1 := by
      have hfin : HasSum (fun s : Fin n => p s) (∑ s, p s) :=
        hasSum_fintype (fun s : Fin n => p s)
      exact ((PMF.hasSum_coe_one p).unique hfin).symm
    rw [← ENNReal.toReal_sum]
    · rw [hpenn]
      norm_num
    · exact fun s hs => p.apply_ne_top s
  have hf (s : Fin n) :
      |energy_state_center M θstar θ s - energy_state_center M θstar θ' s| ≤
        11 * φinf ^ 2 * R * td_euclidean_norm (θ - θ') := by
    rw [energy_state_center, energy_state_center]
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    calc
      |∑ s', (M.transition s s').toReal *
          (energy_centered_scalar M θstar θ s s' -
            energy_centered_scalar M θstar θ' s s')| ≤
        ∑ s', |(M.transition s s').toReal *
          (energy_centered_scalar M θstar θ s s' -
            energy_centered_scalar M θstar θ' s s')| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s', (M.transition s s').toReal *
          (11 * φinf ^ 2 * R * td_euclidean_norm (θ - θ')) := by
        apply Finset.sum_le_sum
        intro s' hs'
        rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
        exact mul_le_mul_of_nonneg_left (hh s s') ENNReal.toReal_nonneg
      _ = _ := by rw [← Finset.sum_mul, hpmf]; ring
  let C : ℝ := 11 * φinf ^ 2 * R * td_euclidean_norm (θ - θ')
  let fd : Fin n → ℝ := fun s =>
    energy_state_center M θstar θ s - energy_state_center M θstar θ' s
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hzero : ∑ s, (M.stationary s).toReal * fd s = 0 := by
    dsimp [fd]
    simp_rw [mul_sub, Finset.sum_sub_distrib,
      energy_state_center_stationary M θstar]
    ring
  have hpd := energy_poisson_series M τ C fd hmix hC hf hzero
  have C0 : 0 ≤ (15 / 2 : ℝ) * φinf ^ 2 * R ^ 2 := by positivity
  have hbθ := energy_centered_observable_bound M τ φinf rinf B R θstar θ
    hbounds hmix hstar hrB hBR hθ
  have hbθ' := energy_centered_observable_bound M τ φinf rinf B R θstar θ'
    hbounds hmix hstar hrB hBR hθ'
  have hpθ := energy_poisson_series M τ
    ((15 / 2 : ℝ) * φinf ^ 2 * R ^ 2) (energy_state_center M θstar θ)
    hmix C0 hbθ.2.1 (energy_state_center_stationary M θstar θ)
  have hpθ' := energy_poisson_series M τ
    ((15 / 2 : ℝ) * φinf ^ 2 * R ^ 2) (energy_state_center M θstar θ')
    hmix C0 hbθ'.2.1 (energy_state_center_stationary M θstar θ')
  intro s
  rw [energy_poisson_solution, energy_poisson_solution]
  have htsum :
      (∑' k : ℕ, ∑ j, ((td_transition_matrix M ^ k) s j -
          (M.stationary j).toReal) * energy_state_center M θstar θ j) -
        (∑' k : ℕ, ∑ j, ((td_transition_matrix M ^ k) s j -
          (M.stationary j).toReal) * energy_state_center M θstar θ' j) =
        ∑' k : ℕ, ∑ j, ((td_transition_matrix M ^ k) s j -
          (M.stationary j).toReal) * fd j := by
    rw [← (hpθ.1 s).tsum_sub (hpθ'.1 s)]
    apply tsum_congr
    intro k
    dsimp [fd]
    simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [htsum]
  have := hpd.2.1 s
  dsimp [C] at this
  nlinarith

@[blueprint "def:energy-prefix-extension"
  (statement := /-- Extend a finite state prefix $(s_0,\ldots,s_t)$ to an infinite path by keeping its last state after time $t$. -/)
  (title := /-- Constant-tail extension of a finite trajectory prefix -/)
  (latexEnv := "definition")]
def energy_prefix_extension {n : ℕ} (t : ℕ) (x : (i : Finset.Iic t) → Fin n) :
    ℕ → Fin n := fun k =>
  if h : k ≤ t then x ⟨k, Finset.mem_Iic.mpr h⟩
  else x ⟨t, Finset.mem_Iic.mpr le_rfl⟩

@[blueprint "lem:energy-stopped-iterate-prefix"
  (statement := /-- If $x$ is the restriction of a path to times at most $t$, then for every $k\leq t$ the stopped iterate computed from the constant-tail extension of $x$ equals the stopped iterate computed from the original path. -/)
  (proof := /-- Induct on $k$.  The initial iterates agree.  At the successor step, the induction hypothesis identifies the current stopped iterates, while \cref{def:energy-prefix-extension} identifies the two state coordinates at $k$ and $k+1$ because both are at most $t$; the two branches of the stopped recursion are therefore identical. -/)
  (title := /-- Stopped iterates depend only on the observed prefix -/)
  (latexEnv := "lemma")]
lemma energy_stopped_iterate_prefix {n d : ℕ} (M : td_model n d)
    (η : ℕ → ℝ) (θ0 : td_vector d) (R : ℝ) (path : ℕ → Fin n)
    (t k : ℕ) (hk : k ≤ t) :
    td_stopped_iterates M η θ0 R k
        (energy_prefix_extension t (Preorder.frestrictLe t path)) =
      td_stopped_iterates M η θ0 R k path := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hkt : k ≤ t := le_trans (Nat.le_succ k) hk
      have hk1t : k + 1 ≤ t := hk
      rw [td_stopped_iterates, td_stopped_iterates, ih hkt]
      have hs : energy_prefix_extension t
          (Preorder.frestrictLe t path) k = path k := by
        simp [energy_prefix_extension, hkt, Preorder.frestrictLe_apply]
      have hs' : energy_prefix_extension t
          (Preorder.frestrictLe t path) (k + 1) = path (k + 1) := by
        simp [energy_prefix_extension, hk1t, Preorder.frestrictLe_apply]
      rw [hs, hs']

@[blueprint "lem:energy-markov-anytime-scalar"
  (statement := /-- Let $F_t$ assign a real increment to each state prefix $(s_0,\ldots,s_t)$ and next state.  Suppose its transition-law mean is zero, $|F_t|\leq b_t$, $b_t\geq0$, and $\sum_tb_t^2<\infty$.  Under the canonical Markov path law, for every $\varepsilon\in(0,1)$, with probability at least $1-\varepsilon$ one has simultaneously for all $T$,
  \[
  \left|\sum_{t<T}F_t((s_i)_{i\leq t},s_{t+1})\right|
  \leq\sqrt{\sum_tb_t^2}\sqrt{2\log(2/\varepsilon)}.
  \] -/)
  (proof := /-- Use the canonical product filtration.  Every increment is measurable one step after its prefix because the prefix space is finite.  The conditional-distribution identity for the trajectory law identifies the next-state conditional law with the model transition kernel; the assumed transition mean therefore makes the partial sums a martingale.  Embed the scalar increments in $\mathbb R^1$ and apply \cref{lem:pinelis-anytime-td}; the TD Euclidean norm on $\mathbb R^1$ is absolute value. -/)
  (title := /-- Anytime scalar martingale bound on the canonical Markov path -/)
  (latexEnv := "lemma")]
lemma energy_markov_anytime_scalar {n d : ℕ} (M : td_model n d) (s0 : Fin n)
    (F : (t : ℕ) → ((i : Finset.Iic t) → Fin n) → Fin n → ℝ)
    (b : ℕ → ℝ) (ε : ℝ)
    (hcenter : ∀ t x, ∑ j, (M.transition
      (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩) j).toReal * F t x j = 0)
    (hbnonneg : ∀ t, 0 ≤ b t)
    (hbound : ∀ t x j, |F t x j| ≤ b t)
    (hbsum : Summable (fun t => (b t) ^ 2))
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    (td_markov_path_measure M s0).real
      {path | ∀ T,
        |∑ t ∈ Finset.range T,
          F t (Preorder.frestrictLe t path) (path (t + 1))| ≤
          Real.sqrt (∑' t, (b t) ^ 2) *
            Real.sqrt (2 * Real.log (2 / ε))} ≥ 1 - ε := by
  classical
  letI : Nonempty (Fin n) := ⟨s0⟩
  let μ := td_markov_path_measure M s0
  letI : MeasureTheory.IsProbabilityMeasure μ := by
    dsimp [μ, td_markov_path_measure]
    infer_instance
  let ℱ : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Fin n)) :=
    MeasureTheory.Filtration.piLE
  let Y : ℕ → (ℕ → Fin n) → ℝ := fun t path =>
    F t (Preorder.frestrictLe t path) (path (t + 1))
  let X : ℕ → (ℕ → Fin n) → td_vector 1 := fun t path _ => Y t path
  let S : ℕ → (ℕ → Fin n) → td_vector 1 := fun T path =>
    ∑ t ∈ Finset.range T, X t path
  have hYmeas (t : ℕ) :
      @Measurable (ℕ → Fin n) ℝ (ℱ (t + 1)) inferInstance (Y t) := by
    let G : ((i : Finset.Iic (t + 1)) → Fin n) → ℝ := fun z =>
      F t (Preorder.frestrictLe₂ (π := fun _ : ℕ => Fin n) (Nat.le_succ t) z)
        (z ⟨t + 1, Finset.mem_Iic.mpr le_rfl⟩)
    rw [MeasureTheory.Filtration.piLE_eq_comap_frestrictLe]
    have hG : Measurable G := measurable_of_countable G
    have hc : @Measurable (ℕ → Fin n) ((i : Finset.Iic (t + 1)) → Fin n)
        (MeasurableSpace.comap (Preorder.frestrictLe (t + 1)) inferInstance)
        inferInstance (Preorder.frestrictLe (t + 1)) := comap_measurable _
    have hcomp := hG.comp hc
    change @Measurable (ℕ → Fin n) ℝ
      (MeasurableSpace.comap (Preorder.frestrictLe (t + 1)) inferInstance)
      inferInstance (Y t)
    have heq : Y t = G ∘ Preorder.frestrictLe (t + 1) := by
      funext path
      dsimp [Y, G, Function.comp_apply]
      congr 2
    rw [heq]
    exact hcomp
  have hXmeas (t : ℕ) :
      @Measurable (ℕ → Fin n) (td_vector 1) (ℱ (t + 1)) inferInstance (X t) := by
    exact @measurable_pi_lambda (ℕ → Fin n) (Fin 1) (fun _ => ℝ)
      (ℱ (t + 1)) (fun _ => inferInstance) (X t) (fun _ => hYmeas t)
  have hadapt : MeasureTheory.StronglyAdapted ℱ S := by
    apply MeasureTheory.Adapted.stronglyAdapted
    intro T
    dsimp [S]
    apply Finset.measurable_sum
    intro t ht
    have hlt : t < T := Finset.mem_range.mp ht
    exact (hXmeas t).mono (ℱ.mono (Nat.succ_le_iff.mpr hlt)) le_rfl
  have hXint (t : ℕ) : MeasureTheory.Integrable (X t) μ := by
    have hm : Measurable (X t) := (hXmeas t).mono (ℱ.le' _) le_rfl
    apply MeasureTheory.Integrable.of_bound hm.aestronglyMeasurable (b t)
    filter_upwards
    intro path
    change ‖fun _ : Fin 1 => Y t path‖ ≤ b t
    simpa [Pi.norm_def, Y] using hbound t (Preorder.frestrictLe t path) (path (t + 1))
  have hSint (T : ℕ) : MeasureTheory.Integrable (S T) μ := by
    dsimp [S]
    exact MeasureTheory.integrable_finsetSum _ (fun t ht => hXint t)
  have hcond (t : ℕ) :
      MeasureTheory.condExp (m := ℱ t) μ (fun path => X t path) =ᵐ[μ] 0 := by
    let Pfx : (ℕ → Fin n) → ((i : Finset.Iic t) → Fin n) := Preorder.frestrictLe t
    let Nxt : (ℕ → Fin n) → Fin n := fun path => path (t + 1)
    let Q : (((i : Finset.Iic t) → Fin n) × Fin n) → td_vector 1 :=
      fun z _ => F t z.1 z.2
    have hPfx : Measurable Pfx := by
      simpa [Pfx] using Preorder.measurable_frestrictLe t
    have hNxt : Measurable Nxt := measurable_pi_apply _
    have hQ : MeasureTheory.StronglyMeasurable Q :=
      (measurable_of_countable Q).stronglyMeasurable
    have hQI : MeasureTheory.Integrable (fun path => Q (Pfx path, Nxt path)) μ := by
      simpa [Q, Pfx, Nxt, X, Y] using hXint t
    have hce := ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib
      hPfx hNxt.aemeasurable hQ hQI
    have hk := ProbabilityTheory.Kernel.condDistrib_trajMeasure
      (X := fun _ : ℕ => Fin n) (μ₀ := MeasureTheory.Measure.dirac s0)
      (κ := fun t => td_prefix_kernel M t)
      (a := t)
    have hkp := (hPfx.quasiMeasurePreserving μ).ae_eq_comp hk
    rw [MeasureTheory.Filtration.piLE_eq_comap_frestrictLe]
    refine hce.trans ?_
    filter_upwards [hkp] with path hpath
    change (∫ j, (fun _ : Fin 1 => F t (Pfx path) j)
      ∂ProbabilityTheory.condDistrib Nxt Pfx μ (Pfx path)) = 0
    dsimp [Nxt, Pfx, μ, td_markov_path_measure] at hpath ⊢
    rw [hpath]
    change (∫ j, (fun _ : Fin 1 => F t (Pfx path) j)
      ∂(M.transition ((Pfx path) ⟨t, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure) = 0
    rw [MeasureTheory.integral_fintype]
    · simp_rw [MeasureTheory.measureReal_def,
        PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
      ext i
      simpa [smul_eq_mul] using hcenter t (Pfx path)
    · exact MeasureTheory.Integrable.of_finite
  have hmart : MeasureTheory.Martingale S ℱ μ := by
    apply MeasureTheory.martingale_of_condExp_sub_eq_zero_nat hadapt hSint
    intro t
    have hinc : S (t + 1) - S t = X t := by
      funext path i
      simp [S, Finset.sum_range_succ]
    rw [hinc]
    exact hcond t
  have hp := pinelis_anytime_td μ ℱ X b ε hmart hbnonneg ?_ hbsum hε0 hε1
  · simpa [μ, X, Y, td_euclidean_norm, Real.sqrt_sq_eq_abs] using hp
  · intro t
    filter_upwards
    intro path
    change td_euclidean_norm (fun _ : Fin 1 => Y t path) ≤ b t
    simpa [td_euclidean_norm, Y, Real.sqrt_sq_eq_abs] using hbound t
      (Preorder.frestrictLe t path) (path (t + 1))

@[blueprint "lem:energy-stopped-stepsize-antitone"
  (statement := /-- If the original stepsizes are nonnegative and non-increasing, then the stopped stepsizes are also nonnegative and non-increasing along every path. -/)
  (proof := /-- Nonnegativity follows directly from \cref{def:td-stopped-stepsize}.  For consecutive indices, if the current stopped iterate is inside the ball, the next stopped stepsize is either the next original stepsize or zero, and both are at most the current original stepsize.  If the current iterate is outside the ball, \cref{def:td-stopped-iterates} freezes it, so both consecutive stopped stepsizes are zero.  The consecutive inequalities imply antitonicity on the natural numbers. -/)
  (title := /-- Antitonicity of the stopped stepsizes -/)
  (latexEnv := "lemma")]
lemma energy_stopped_stepsize_antitone {n d : ℕ} (M : td_model n d)
    (η : ℕ → ℝ) (θ0 : td_vector d) (R : ℝ) (path : ℕ → Fin n)
    (hηnonneg : ∀ t, 0 ≤ η t) (hηanti : Antitone η) :
    (∀ t, 0 ≤ td_stopped_stepsize M η θ0 R path t) ∧
      Antitone (td_stopped_stepsize M η θ0 R path) := by
  have hnonneg (t : ℕ) :
      0 ≤ td_stopped_stepsize M η θ0 R path t := by
    rw [td_stopped_stepsize]
    split_ifs
    · exact hηnonneg t
    · exact le_rfl
  have hsucc (t : ℕ) :
      td_stopped_stepsize M η θ0 R path (t + 1) ≤
        td_stopped_stepsize M η θ0 R path t := by
    by_cases ht : td_euclidean_norm
        (td_stopped_iterates M η θ0 R t path) ≤ R
    · rw [td_stopped_stepsize]
      rw [td_stopped_stepsize]
      split_ifs
      · exact hηanti (Nat.le_succ t)
      · exact hηnonneg t
    · have hfreeze :
          td_stopped_iterates M η θ0 R (t + 1) path =
            td_stopped_iterates M η θ0 R t path := by
        rw [td_stopped_iterates, if_neg ht]
      rw [td_stopped_stepsize, td_stopped_stepsize, hfreeze]
      simp [ht]
  exact ⟨hnonneg, antitone_nat_of_succ_le hsucc⟩

@[blueprint "lem:energy-abel-remainder-bound-nonnegative"
  (statement := /-- The Abel remainder estimate of \cref{lem:energy-abel-remainder-bound} remains valid when the stepsizes are merely nonnegative rather than strictly positive. -/)
  (proof := /-- If every stepsize is positive, apply \cref{lem:energy-abel-remainder-bound}.  Otherwise, repeat its deterministic estimate: antitonicity makes each difference $\eta_t-\eta_{t+1}$ nonnegative and telescoping bounds its total mass by $\eta_0$; also $\eta_{t+1}\leq\eta_t$ bounds the Lipschitz sum by the squared-stepsize mass.  The triangle inequality then gives the same constants. -/)
  (title := /-- Nonnegative Abel remainder bound -/)
  (latexEnv := "lemma")]
lemma energy_abel_remainder_bound_nonnegative
    (η u v w : ℕ → ℝ) (τ φinf R : ℝ) (T : ℕ)
    (hT : 1 ≤ T) (hηnonneg : ∀ t, 0 ≤ η t) (hηanti : Antitone η)
    (hτ : 0 ≤ τ) (hφ : 0 ≤ φinf) (hR : 0 ≤ R)
    (hend : |η 0 * u 0| + |η T * u T| ≤
      384 * η 0 * τ * φinf ^ 2 * R ^ 2)
    (hvar : ∀ t ∈ Finset.range T,
      |v t| ≤ 192 * τ * φinf ^ 2 * R ^ 2)
    (hlip : ∀ t ∈ Finset.range T,
      |w t| ≤ 672 * η t * τ * φinf ^ 4 * R ^ 2) :
    |η 0 * u 0 - η T * u T -
        (∑ t ∈ Finset.range T, (η t - η (t + 1)) * v t) -
        (∑ t ∈ Finset.range T, η (t + 1) * w t)| ≤
      576 * η 0 * τ * φinf ^ 2 * R ^ 2 +
        672 * τ * φinf ^ 4 * R ^ 2 *
          (∑ t ∈ Finset.range T, (η t) ^ 2) := by
  by_cases hηpos : ∀ t, 0 < η t
  · exact energy_abel_remainder_bound η u v w τ φinf R T hT hηpos hηanti
      hτ hφ hR hend hvar hlip
  · have hstep (t : ℕ) : η (t + 1) ≤ η t := hηanti (Nat.le_succ t)
    have hdiff (t : ℕ) : 0 ≤ η t - η (t + 1) := sub_nonneg.mpr (hstep t)
    have hvar_sum :
        |∑ t ∈ Finset.range T, (η t - η (t + 1)) * v t| ≤
          192 * η 0 * τ * φinf ^ 2 * R ^ 2 := by
      calc
        _ ≤ ∑ t ∈ Finset.range T, |(η t - η (t + 1)) * v t| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ t ∈ Finset.range T,
            (η t - η (t + 1)) * (192 * τ * φinf ^ 2 * R ^ 2) := by
          apply Finset.sum_le_sum
          intro t ht
          rw [abs_mul, abs_of_nonneg (hdiff t)]
          exact mul_le_mul_of_nonneg_left (hvar t ht) (hdiff t)
        _ = (η 0 - η T) * (192 * τ * φinf ^ 2 * R ^ 2) := by
          rw [← Finset.sum_mul, Finset.sum_range_sub']
        _ ≤ η 0 * (192 * τ * φinf ^ 2 * R ^ 2) := by
          apply mul_le_mul_of_nonneg_right
            (sub_le_self (η 0) (hηnonneg T))
          positivity
        _ = _ := by ring
    have hlip_sum :
        |∑ t ∈ Finset.range T, η (t + 1) * w t| ≤
          672 * τ * φinf ^ 4 * R ^ 2 *
            (∑ t ∈ Finset.range T, (η t) ^ 2) := by
      calc
        _ ≤ ∑ t ∈ Finset.range T, |η (t + 1) * w t| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ t ∈ Finset.range T,
            672 * τ * φinf ^ 4 * R ^ 2 * (η t) ^ 2 := by
          apply Finset.sum_le_sum
          intro t ht
          rw [abs_mul, abs_of_nonneg (hηnonneg (t + 1))]
          calc
            η (t + 1) * |w t| ≤
                η (t + 1) * (672 * η t * τ * φinf ^ 4 * R ^ 2) :=
              mul_le_mul_of_nonneg_left (hlip t ht) (hηnonneg (t + 1))
            _ ≤ η t * (672 * η t * τ * φinf ^ 4 * R ^ 2) := by
              apply mul_le_mul_of_nonneg_right (hstep t)
              have h₁ : 0 ≤ 672 * η t := mul_nonneg (by norm_num) (hηnonneg t)
              have h₂ : 0 ≤ 672 * η t * τ := mul_nonneg h₁ hτ
              have h₃ : 0 ≤ 672 * η t * τ * φinf ^ 4 :=
                mul_nonneg h₂ (by positivity)
              exact mul_nonneg h₃ (by positivity)
            _ = _ := by ring
        _ = _ := by rw [Finset.mul_sum]
    calc
      _ ≤ (|η 0 * u 0| + |η T * u T|) +
          |∑ t ∈ Finset.range T, (η t - η (t + 1)) * v t| +
          |∑ t ∈ Finset.range T, η (t + 1) * w t| := by
        calc
          _ ≤ |η 0 * u 0 - η T * u T -
                (∑ t ∈ Finset.range T, (η t - η (t + 1)) * v t)| +
              |∑ t ∈ Finset.range T, η (t + 1) * w t| := abs_sub _ _
          _ ≤ (|η 0 * u 0 - η T * u T| +
                |∑ t ∈ Finset.range T, (η t - η (t + 1)) * v t|) +
              |∑ t ∈ Finset.range T, η (t + 1) * w t| := by
            gcongr
            exact abs_sub _ _
          _ ≤ _ := by
            gcongr
            exact abs_sub _ _
      _ ≤ _ := by linarith

@[blueprint "lem:energy-stopped-remainder-identity"
  (statement := /-- For every stopped TD path and horizon $T$, the stopped recursion remainder is exactly
  \[
  \widetilde B_T=2\sum_{t<T}\widetilde\eta_t
  h_{\widetilde\theta_t}(s_t,s_{t+1}).
  \] -/)
  (proof := /-- The stopped recursion satisfies $\widetilde\theta_{t+1}=\widetilde\theta_t+\widetilde\eta_tg(\widetilde\theta_t,(s_t,s_{t+1}))$ in both branches of \cref{def:td-stopped-iterates,def:td-stopped-stepsize}.  Expand the Euclidean square at each step, sum the resulting telescoping identity, and compare with \cref{def:td-stopped-recursion-remainder,def:energy-centered-scalar}. -/)
  (title := /-- Exact centered-sum representation of the stopped remainder -/)
  (latexEnv := "lemma")]
lemma energy_stopped_remainder_identity {n d : ℕ} (M : td_model n d)
    (η : ℕ → ℝ) (θ0 θstar : td_vector d) (R : ℝ)
    (path : ℕ → Fin n) (T : ℕ) :
    td_stopped_recursion_remainder M η θ0 θstar R path T =
      2 * ∑ t ∈ Finset.range T,
        td_stopped_stepsize M η θ0 R path t *
          energy_centered_scalar M θstar
            (td_stopped_iterates M η θ0 R t path) (path t) (path (t + 1)) := by
  classical
  have hsq (v : td_vector d) : (td_euclidean_norm v) ^ 2 = ∑ i, (v i) ^ 2 := by
    rw [td_euclidean_norm]
    exact Real.sq_sqrt (Finset.sum_nonneg (fun i hi => sq_nonneg (v i)))
  have hrec (t : ℕ) :
      td_stopped_iterates M η θ0 R (t + 1) path - θstar =
        (td_stopped_iterates M η θ0 R t path - θstar) +
          td_stopped_stepsize M η θ0 R path t •
            td_update M (td_stopped_iterates M η θ0 R t path)
              (path t) (path (t + 1)) := by
    rw [td_stopped_stepsize, td_stopped_iterates]
    split_ifs with h
    · ext i
      simp
      ring
    · ext i
      simp
  have hstep (t : ℕ) :
      td_euclidean_norm
            (td_stopped_iterates M η θ0 R (t + 1) path - θstar) ^ 2 -
          td_euclidean_norm
            (td_stopped_iterates M η θ0 R t path - θstar) ^ 2 -
          td_stopped_stepsize M η θ0 R path t ^ 2 *
            td_euclidean_norm
              (td_update M (td_stopped_iterates M η θ0 R t path)
                (path t) (path (t + 1))) ^ 2 -
          2 * td_stopped_stepsize M η θ0 R path t *
            (td_mean_update M (td_stopped_iterates M η θ0 R t path) ⬝ᵥ
              (td_stopped_iterates M η θ0 R t path - θstar)) =
        2 * td_stopped_stepsize M η θ0 R path t *
          energy_centered_scalar M θstar
            (td_stopped_iterates M η θ0 R t path) (path t) (path (t + 1)) := by
    let e : td_vector d := td_stopped_iterates M η θ0 R t path - θstar
    let q : td_vector d := td_update M
      (td_stopped_iterates M η θ0 R t path) (path t) (path (t + 1))
    let m : td_vector d := td_mean_update M
      (td_stopped_iterates M η θ0 R t path)
    let α : ℝ := td_stopped_stepsize M η θ0 R path t
    have hnext :
        td_stopped_iterates M η θ0 R (t + 1) path - θstar = e + α • q := by
      simpa [e, q, α] using hrec t
    have hexpand :
        ∑ i, (e i + α * q i) ^ 2 =
          (∑ i, (e i) ^ 2) + α ^ 2 * (∑ i, (q i) ^ 2) +
            2 * α * (∑ i, q i * e i) := by
      calc
        _ = ∑ i, ((e i) ^ 2 + α ^ 2 * (q i) ^ 2 +
            2 * α * (q i * e i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = _ := by
          simp_rw [Finset.sum_add_distrib]
          rw [Finset.mul_sum, Finset.mul_sum]
    have hdifference :
        (∑ i, (q i - m i) * e i) =
          (∑ i, q i * e i) - ∑ i, m i * e i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hnext, hsq (e + α • q), hsq e, hsq q]
    change (∑ i, (e i + α * q i) ^ 2) - (∑ i, (e i) ^ 2) -
        α ^ 2 * (∑ i, (q i) ^ 2) -
        2 * α * (∑ i, m i * e i) =
      2 * α * ∑ i, (q i - m i) * e i
    rw [hexpand, hdifference]
    ring
  induction T with
  | zero => simp [td_stopped_recursion_remainder, td_stopped_iterates]
  | succ T ih =>
      calc
        td_stopped_recursion_remainder M η θ0 θstar R path (T + 1) =
            td_stopped_recursion_remainder M η θ0 θstar R path T +
              (td_euclidean_norm
                    (td_stopped_iterates M η θ0 R (T + 1) path - θstar) ^ 2 -
                td_euclidean_norm
                    (td_stopped_iterates M η θ0 R T path - θstar) ^ 2 -
                td_stopped_stepsize M η θ0 R path T ^ 2 *
                  td_euclidean_norm
                    (td_update M (td_stopped_iterates M η θ0 R T path)
                      (path T) (path (T + 1))) ^ 2 -
                2 * td_stopped_stepsize M η θ0 R path T *
                  (td_mean_update M (td_stopped_iterates M η θ0 R T path) ⬝ᵥ
                    (td_stopped_iterates M η θ0 R T path - θstar))) := by
              rw [td_stopped_recursion_remainder, Finset.sum_range_succ,
                Finset.sum_range_succ]
              rw [td_stopped_recursion_remainder]
              ring
        _ = 2 * ∑ t ∈ Finset.range T,
              td_stopped_stepsize M η θ0 R path t *
                energy_centered_scalar M θstar
                  (td_stopped_iterates M η θ0 R t path) (path t) (path (t + 1)) +
            2 * td_stopped_stepsize M η θ0 R path T *
              energy_centered_scalar M θstar
                (td_stopped_iterates M η θ0 R T path) (path T) (path (T + 1)) := by
              rw [ih, hstep T]
        _ = 2 * ∑ t ∈ Finset.range (T + 1),
              td_stopped_stepsize M η θ0 R path t *
                energy_centered_scalar M θstar
                  (td_stopped_iterates M η θ0 R t path) (path t) (path (t + 1)) := by
              rw [Finset.sum_range_succ]
              ring

@[blueprint "lem:energy-stopped-martingale-control"
  (statement := /-- Let $M$ be a finite TD model, let $\theta^*$ be a TD fixed point, and let $\phi_\infty>0$, $r_\infty\geq0$, and $\tau\geq1$ satisfy the uniform boundedness and geometric-mixing hypotheses.  Let $a_t>0$ be non-increasing, with $a_0\leq1$ and $\sum_ta_t^2<\infty$, set $\eta_t=(c\tau\phi_\infty^2)^{-1}a_t$, fix $\delta\in(0,1)$, and suppose $c>c_{\min}(\delta)$.  For every initial vector $\theta_0$ and initial state $s_0$, the stopped energy-control event has probability at least $1-\delta/4$ under the canonical path law started at $s_0$.  Equivalently, with that probability, simultaneously for every $T\geq1$,
  \[
  \sum_{t<T}\widetilde\eta_t^2
  \|g(\widetilde\theta_t,Z_t)\|_2^2+\widetilde B_T
  \leq768\tau\phi_\infty^2R_{\max}^2\sqrt H
  \sqrt{2\log\frac8\delta}
  +1152\eta_0\tau\phi_\infty^2R_{\max}^2
  +(1344\tau+9)\phi_\infty^4R_{\max}^2H,
  \]
  where $R_{\max}=\rho R_{\mathrm{base}}$, $H=\sum_t\eta_t^2$, and the stopped quantities are those of \cref{def:td-stopped-iterates,def:td-stopped-stepsize,def:td-stopped-recursion-remainder}.  Juxtaposed square-root factors in the display are multiplied. -/)
  (proof := /-- Put $B=R_{\mathrm{base}}$ and $R=\rho B$.  The bootstrap estimate \cref{lem:rho-bootstrap-inequality} gives $\rho>2$; the definition of $B$ and the triangle inequality \cref{lem:energy-td-euclidean-norm-add} then give
  $\|\theta^*\|_2\leq B$, $r_\infty\leq\phi_\infty B$, $2B\leq R$, and $\|\theta_0\|_2\leq R$.  The prescribed stepsizes are positive, non-increasing, and square-summable.

  For a prefix $(s_0,\ldots,s_t)$, evaluate the stopped iterate on its constant-tail extension.  By \cref{lem:energy-stopped-iterate-prefix}, this agrees with the stopped iterate of every extending path through time $t$.  Define the scalar increment to be the stopped stepsize times
  \[
  h_{\widetilde\theta_t}(s_t,s_{t+1})
  -f_{\widetilde\theta_t}(s_t)
  +u_{\widetilde\theta_t}(s_{t+1})
  -P u_{\widetilde\theta_t}(s_t).
  \]
  Its conditional transition mean is zero by the definition of $f$.  On an active step, \cref{lem:energy-centered-observable-bound} bounds the two centered-observable terms by $(15/2)\phi_\infty^2R^2$ and each Poisson term by $180\tau\phi_\infty^2R^2$; on an inactive step the multiplier is zero.  Hence the increment is bounded by $384\eta_t\tau\phi_\infty^2R^2$.  Applying \cref{lem:energy-markov-anytime-scalar} with error probability $\delta/4$ yields, simultaneously for every $T$,
  \[
  |M_T|\leq384\tau\phi_\infty^2R^2
  \sqrt H\sqrt{2\log(8/\delta)}.
  \]

  Along a fixed path, replace every Poisson value after deactivation by zero.  The stopped stepsizes are nonnegative and antitone by \cref{lem:energy-stopped-stepsize-antitone}.  The endpoint and transition-variation terms are bounded by the preceding Poisson estimate.  When the next step remains active, \cref{lem:energy-poisson-lipschitz} and the recursion identity give
  \[
  |u_{\widetilde\theta_t}(s_{t+1})
    -u_{\widetilde\theta_{t+1}}(s_{t+1})|
  \leq264\tau\phi_\infty^2R
    \|\widetilde\theta_t-\widetilde\theta_{t+1}\|_2.
  \]
  The sample-update estimate \cref{lem:energy-sample-update-bound}, together with the scalar-multiplication norm identity \cref{lem:energy-td-euclidean-norm-smul}, bounds the right-hand side by
  $660\widetilde\eta_t\tau\phi_\infty^4R^2$, hence by the required coefficient $672$.  The nonnegative Abel estimate \cref{lem:energy-abel-remainder-bound-nonnegative} therefore bounds the Poisson remainder by
  \[
  576\eta_0\tau\phi_\infty^2R^2+
  672\tau\phi_\infty^4R^2H.
  \]
  The Poisson identity and the exact recursion formula \cref{lem:energy-stopped-remainder-identity} show that $\widetilde B_T$ is twice the sum of the martingale and Abel terms.  This gives the coefficients $768$, $1152$, and $1344$.

  Finally, on every active step \cref{lem:energy-sample-update-bound} gives
  $\|g(\widetilde\theta_t,Z_t)\|_2\leq(5/2)\phi_\infty^2R$; inactive steps contribute zero.  Square-summability thus bounds the stopped squared-update sum by
  $(25/4)\phi_\infty^4R^2H\leq9\phi_\infty^4R^2H$.  Adding this deterministic term proves the asserted event inclusion, and monotonicity of the path measure gives the stated probability. -/)
  (title := /-- High-probability energy control for the stopped recursion -/)
  (latexEnv := "lemma")]
lemma energy_stopped_martingale_control {n d : ℕ} (M : td_model n d)
    (a η : ℕ → ℝ) (δ c τ φinf rinf : ℝ)
    (θ0 θstar : td_vector d) (s0 : Fin n)
    (ha : admissible_stepsize_shape a)
    (hη : ∀ t, η t = pr_eta_base c τ φinf * a t)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hc : pr_c_min a δ < c)
    (hbounds : td_uniform_bounds M φinf rinf)
    (hmix : td_geometric_mixing M τ) (hfixed : td_fixed_point M θstar) :
    (td_markov_path_measure M s0).real
        (stopped_energy_control_event M a η δ c τ φinf rinf θ0 θstar) ≥
      1 - δ / 4 := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure (td_markov_path_measure M s0) := by
    dsimp [td_markov_path_measure]
    infer_instance
  let B := pr_base_radius θ0 θstar rinf φinf
  let R := pr_rho a δ c * B
  have hρ : 2 < pr_rho a δ c :=
    (rho_bootstrap_inequality a δ c ha hδ0 hδ1 hc).1
  have hφpos : 0 < φinf := hbounds.1
  have hτ : 1 ≤ τ := hmix.1
  have hτpos : 0 < τ := lt_of_lt_of_le zero_lt_one hτ
  have hτ0 : 0 ≤ τ := hτpos.le
  have hB : 0 ≤ B := by
    dsimp [B, pr_base_radius]
    exact (Real.sqrt_nonneg _).trans (le_max_left _ _)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hstar : td_euclidean_norm θstar ≤ B := by
    dsimp [B, pr_base_radius]
    exact le_max_of_le_right (le_max_left _ _)
  have hdiff0 : td_euclidean_norm (θ0 - θstar) ≤ B := by
    dsimp [B, pr_base_radius]
    exact le_max_left _ _
  have hrdiv : rinf / φinf ≤ B := by
    dsimp [B, pr_base_radius]
    exact le_max_of_le_right (le_max_right _ _)
  have hrB : rinf ≤ φinf * B := by
    calc
      rinf = φinf * (rinf / φinf) := by field_simp
      _ ≤ φinf * B := mul_le_mul_of_nonneg_left hrdiv hφpos.le
  have hBR : 2 * B ≤ R := by
    dsimp [R]
    nlinarith
  have hθ0 : td_euclidean_norm θ0 ≤ R := by
    have hadd := energy_td_euclidean_norm_add (θ0 - θstar) θstar
    have heq : (θ0 - θstar) + θstar = θ0 := by abel
    rw [heq] at hadd
    nlinarith
  have hA : 0 < pr_a_one a δ := by
    rw [pr_a_one]
    positivity
  have hcpos : 0 < c := by
    have hcmin : 0 < pr_c_min a δ := by
      rw [pr_c_min]
      positivity
    linarith
  have hηpos (t : ℕ) : 0 < η t := by
    rw [hη t, pr_eta_base]
    exact mul_pos (one_div_pos.mpr
      (mul_pos (mul_pos hcpos hτpos) (sq_pos_of_pos hφpos))) (ha.1 t)
  have hηnonneg (t : ℕ) : 0 ≤ η t := (hηpos t).le
  have hηanti : Antitone η := by
    intro i j hij
    rw [hη i, hη j]
    apply mul_le_mul_of_nonneg_left (ha.2.1 hij)
    rw [pr_eta_base]
    positivity
  have hηsum : Summable (fun t => (η t) ^ 2) := by
    have hs := ha.2.2.2.mul_left ((pr_eta_base c τ φinf) ^ 2)
    simpa only [hη, mul_pow] using hs
  have hH : 0 ≤ pr_square_mass η := by
    rw [pr_square_mass]
    exact tsum_nonneg (fun t => sq_nonneg (η t))
  let Θ : (t : ℕ) → ((i : Finset.Iic t) → Fin n) → td_vector d :=
    fun t x => td_stopped_iterates M η θ0 R t (energy_prefix_extension t x)
  let A : (t : ℕ) → ((i : Finset.Iic t) → Fin n) → ℝ :=
    fun t x => td_stopped_stepsize M η θ0 R
      (energy_prefix_extension t x) t
  let F : (t : ℕ) → ((i : Finset.Iic t) → Fin n) → Fin n → ℝ :=
    fun t x j =>
      A t x *
        (energy_centered_scalar M θstar (Θ t x)
            (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩) j -
          energy_state_center M θstar (Θ t x)
            (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩) +
          energy_poisson_solution M θstar (Θ t x) j -
          ∑ k, (M.transition (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩) k).toReal *
            energy_poisson_solution M θstar (Θ t x) k)
  let b : ℕ → ℝ := fun t => 384 * η t * τ * φinf ^ 2 * R ^ 2
  have hpmf (p : PMF (Fin n)) : ∑ j, (p j).toReal = 1 := by
    have hpenn : ∑ j, p j = 1 := by
      have hs : HasSum (fun j : Fin n => p j) (∑ j, p j) :=
        hasSum_fintype (fun j : Fin n => p j)
      exact ((PMF.hasSum_coe_one p).unique hs).symm
    rw [← ENNReal.toReal_sum]
    · rw [hpenn]
      norm_num
    · exact fun j hj => p.apply_ne_top j
  have hcenter (t : ℕ) (x : (i : Finset.Iic t) → Fin n) :
      ∑ j, (M.transition (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩) j).toReal *
        F t x j = 0 := by
    let s := x ⟨t, Finset.mem_Iic.mpr le_rfl⟩
    have hone := hpmf (M.transition (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩))
    have hinner :
        (∑ j, (M.transition s j).toReal *
          (energy_centered_scalar M θstar (Θ t x) s j -
              energy_state_center M θstar (Θ t x) s +
            energy_poisson_solution M θstar (Θ t x) j -
            ∑ k, (M.transition s k).toReal *
              energy_poisson_solution M θstar (Θ t x) k)) = 0 := by
      dsimp [energy_state_center]
      ring_nf
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      rw [hone]
      ring
    dsimp [F]
    calc
      _ = A t x * ∑ j, (M.transition s j).toReal *
          (energy_centered_scalar M θstar (Θ t x) s j -
              energy_state_center M θstar (Θ t x) s +
            energy_poisson_solution M θstar (Θ t x) j -
            ∑ k, (M.transition s k).toReal *
              energy_poisson_solution M θstar (Θ t x) k) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            dsimp [s]
            ring
      _ = 0 := by rw [hinner, mul_zero]
  have hbnonneg (t : ℕ) : 0 ≤ b t := by
    dsimp [b]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hηnonneg t)) hτ0)
        (sq_nonneg φinf)) (sq_nonneg R)
  have hbound (t : ℕ) (x : (i : Finset.Iic t) → Fin n) (j : Fin n) :
      |F t x j| ≤ b t := by
    let s := x ⟨t, Finset.mem_Iic.mpr le_rfl⟩
    by_cases hactive : td_euclidean_norm (Θ t x) ≤ R
    · have hobs := energy_centered_observable_bound M τ φinf rinf B R
        θstar (Θ t x) hbounds hmix hstar hrB hBR hactive
      have hpu :
          |∑ k, (M.transition s k).toReal *
              energy_poisson_solution M θstar (Θ t x) k| ≤
            180 * τ * φinf ^ 2 * R ^ 2 := by
        calc
          _ ≤ ∑ k, |(M.transition s k).toReal *
              energy_poisson_solution M θstar (Θ t x) k| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k, (M.transition s k).toReal *
              (180 * τ * φinf ^ 2 * R ^ 2) := by
            apply Finset.sum_le_sum
            intro k hk
            rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
            exact mul_le_mul_of_nonneg_left (hobs.2.2.1 k)
              ENNReal.toReal_nonneg
          _ = _ := by rw [← Finset.sum_mul, hpmf]; ring
      have hexpr :
          |energy_centered_scalar M θstar (Θ t x) s j -
              energy_state_center M θstar (Θ t x) s +
              energy_poisson_solution M θstar (Θ t x) j -
              ∑ k, (M.transition s k).toReal *
                energy_poisson_solution M θstar (Θ t x) k| ≤
            375 * τ * φinf ^ 2 * R ^ 2 := by
        have htri := abs_add_le
          (energy_centered_scalar M θstar (Θ t x) s j -
            energy_state_center M θstar (Θ t x) s)
          (energy_poisson_solution M θstar (Θ t x) j -
            ∑ k, (M.transition s k).toReal *
              energy_poisson_solution M θstar (Θ t x) k)
        have htri₁ := abs_sub
          (energy_centered_scalar M θstar (Θ t x) s j)
          (energy_state_center M θstar (Θ t x) s)
        have htri₂ := abs_sub
          (energy_poisson_solution M θstar (Θ t x) j)
          (∑ k, (M.transition s k).toReal *
            energy_poisson_solution M θstar (Θ t x) k)
        have hD : 0 ≤ φinf ^ 2 * R ^ 2 :=
          mul_nonneg (sq_nonneg φinf) (sq_nonneg R)
        have hτD : φinf ^ 2 * R ^ 2 ≤ τ * φinf ^ 2 * R ^ 2 := by
          nlinarith
        have heq :
            energy_centered_scalar M θstar (Θ t x) s j -
                energy_state_center M θstar (Θ t x) s +
                energy_poisson_solution M θstar (Θ t x) j -
                ∑ k, (M.transition s k).toReal *
                  energy_poisson_solution M θstar (Θ t x) k =
              (energy_centered_scalar M θstar (Θ t x) s j -
                energy_state_center M θstar (Θ t x) s) +
              (energy_poisson_solution M θstar (Θ t x) j -
                ∑ k, (M.transition s k).toReal *
                  energy_poisson_solution M θstar (Θ t x) k) := by ring
        rw [heq]
        calc
          _ ≤ |energy_centered_scalar M θstar (Θ t x) s j -
                energy_state_center M θstar (Θ t x) s| +
              |energy_poisson_solution M θstar (Θ t x) j -
                ∑ k, (M.transition s k).toReal *
                  energy_poisson_solution M θstar (Θ t x) k| := htri
          _ ≤ (|energy_centered_scalar M θstar (Θ t x) s j| +
                |energy_state_center M θstar (Θ t x) s|) +
              (|energy_poisson_solution M θstar (Θ t x) j| +
                |∑ k, (M.transition s k).toReal *
                  energy_poisson_solution M θstar (Θ t x) k|) :=
            add_le_add htri₁ htri₂
          _ ≤ ((15 / 2 : ℝ) * φinf ^ 2 * R ^ 2 +
                (15 / 2 : ℝ) * φinf ^ 2 * R ^ 2) +
              (180 * τ * φinf ^ 2 * R ^ 2 +
                180 * τ * φinf ^ 2 * R ^ 2) := by
            gcongr
            · exact hobs.1 s j
            · exact hobs.2.1 s
            · exact hobs.2.2.1 j
          _ ≤ 375 * τ * φinf ^ 2 * R ^ 2 := by nlinarith
      have hAeq : A t x = η t := by
        dsimp [A, Θ]
        rw [td_stopped_stepsize, if_pos hactive]
      dsimp [F, b]
      rw [hAeq]
      rw [abs_mul, abs_of_pos (hηpos t)]
      exact (mul_le_mul_of_nonneg_left hexpr (hηnonneg t)).trans (by
        have hC : 0 ≤ η t * τ * φinf ^ 2 * R ^ 2 :=
          mul_nonneg
            (mul_nonneg (mul_nonneg (hηnonneg t) hτ0) (sq_nonneg φinf))
            (sq_nonneg R)
        nlinarith)
    · have hAzero : A t x = 0 := by
        dsimp [A, Θ]
        rw [td_stopped_stepsize, if_neg hactive]
      simp [F, hAzero, hbnonneg t]
  have hbsum : Summable (fun t => (b t) ^ 2) := by
    have hs := hηsum.mul_left ((384 * τ * φinf ^ 2 * R ^ 2) ^ 2)
    apply hs.congr
    intro t
    dsimp [b]
    ring
  have hε0 : 0 < δ / 4 := by positivity
  have hε1 : δ / 4 < 1 := by linarith
  let E : Set (ℕ → Fin n) :=
    {path | ∀ T,
      |∑ t ∈ Finset.range T,
        F t (Preorder.frestrictLe t path) (path (t + 1))| ≤
        Real.sqrt (∑' t, (b t) ^ 2) *
          Real.sqrt (2 * Real.log (2 / (δ / 4)))}
  have hprob :
      (td_markov_path_measure M s0).real E ≥ 1 - δ / 4 := by
    exact energy_markov_anytime_scalar M s0 F b (δ / 4) hcenter hbnonneg
      hbound hbsum hε0 hε1
  have hbmass :
      Real.sqrt (∑' t, (b t) ^ 2) =
        384 * τ * φinf ^ 2 * R ^ 2 * Real.sqrt (pr_square_mass η) := by
    have htsum :
        (∑' t, (b t) ^ 2) =
          (384 * τ * φinf ^ 2 * R ^ 2) ^ 2 * pr_square_mass η := by
      rw [pr_square_mass]
      rw [← tsum_mul_left]
      apply tsum_congr
      intro t
      dsimp [b]
      ring
    rw [htsum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
      abs_of_nonneg]
    positivity
  have hsubset :
      E ⊆ stopped_energy_control_event M a η δ c τ φinf rinf θ0 θstar := by
    intro path hpath
    intro T hT
    let θ : ℕ → td_vector d := fun t =>
      td_stopped_iterates M η θ0 R t path
    let α : ℕ → ℝ := fun t =>
      td_stopped_stepsize M η θ0 R path t
    let active : ℕ → Prop := fun t => td_euclidean_norm (θ t) ≤ R
    let u : ℕ → ℝ := fun t =>
      if active t then energy_poisson_solution M θstar (θ t) (path t) else 0
    let v : ℕ → ℝ := fun t =>
      if active t then energy_poisson_solution M θstar (θ t) (path (t + 1)) else 0
    let w : ℕ → ℝ := fun t =>
      if active (t + 1) then v t - u (t + 1) else 0
    have hα := energy_stopped_stepsize_antitone M η θ0 R path hηnonneg hηanti
    have hprefix (t : ℕ) :
        Θ t (Preorder.frestrictLe t path) = θ t := by
      exact energy_stopped_iterate_prefix M η θ0 R path t t le_rfl
    have hstate (t : ℕ) :
        energy_prefix_extension t (Preorder.frestrictLe t path) t = path t := by
      simp [energy_prefix_extension, Preorder.frestrictLe_apply]
    have hFeq (t : ℕ) :
        F t (Preorder.frestrictLe t path) (path (t + 1)) =
          α t * (energy_centered_scalar M θstar (θ t) (path t) (path (t + 1)) -
            energy_state_center M θstar (θ t) (path t) +
            energy_poisson_solution M θstar (θ t) (path (t + 1)) -
            ∑ k, (M.transition (path t) k).toReal *
              energy_poisson_solution M θstar (θ t) k) := by
      dsimp [F, A, Θ, α, θ]
      rw [td_stopped_stepsize, td_stopped_stepsize,
        energy_stopped_iterate_prefix M η θ0 R path t t le_rfl]
    have hdecomp (t : ℕ) :
        α t * energy_centered_scalar M θstar (θ t) (path t) (path (t + 1)) =
          F t (Preorder.frestrictLe t path) (path (t + 1)) +
            α t * (u t - v t) := by
      by_cases ht : active t
      · have hobs := energy_centered_observable_bound M τ φinf rinf B R
          θstar (θ t) hbounds hmix hstar hrB hBR ht
        rw [hFeq]
        dsimp [u, v]
        rw [if_pos ht, if_pos ht]
        have hp := hobs.2.2.2 (path t)
        rw [← hp]
        ring
      · have hzero : α t = 0 := by
          dsimp [α, active, θ] at ht ⊢
          rw [td_stopped_stepsize, if_neg ht]
        rw [hFeq, hzero]
        simp
    have hwend (t : ℕ) :
        α (t + 1) * w t = α (t + 1) * (v t - u (t + 1)) := by
      by_cases ht : active (t + 1)
      · simp [w, ht]
      · have hz : α (t + 1) = 0 := by
          dsimp [α, active, θ] at ht ⊢
          rw [td_stopped_stepsize, if_neg ht]
        simp [w, ht, hz]
    have hend :
        |α 0 * u 0| + |α T * u T| ≤
          384 * α 0 * τ * φinf ^ 2 * R ^ 2 := by
      have hprod (t : ℕ) :
          |α t * u t| ≤ 180 * α t * τ * φinf ^ 2 * R ^ 2 := by
        by_cases ht : active t
        · have hu := (energy_centered_observable_bound M τ φinf rinf B R
            θstar (θ t) hbounds hmix hstar hrB hBR ht).2.2.1 (path t)
          have hat : 0 ≤ α t := hα.1 t
          simp only [u, ht, if_true, abs_mul, abs_of_nonneg hat]
          calc
            α t * |energy_poisson_solution M θstar (θ t) (path t)| ≤
                α t * (180 * τ * φinf ^ 2 * R ^ 2) :=
              mul_le_mul_of_nonneg_left hu hat
            _ = _ := by ring
        · simp [u, ht]
          exact mul_nonneg
            (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hα.1 t)) hτ0)
              (sq_nonneg φinf)) (sq_nonneg R)
      have hαT := hα.2 (Nat.zero_le T)
      have hC : 0 ≤ τ * φinf ^ 2 * R ^ 2 := by positivity
      calc
        _ ≤ 180 * α 0 * τ * φinf ^ 2 * R ^ 2 +
            180 * α T * τ * φinf ^ 2 * R ^ 2 :=
          add_le_add (hprod 0) (hprod T)
        _ ≤ 180 * α 0 * τ * φinf ^ 2 * R ^ 2 +
            180 * α 0 * τ * φinf ^ 2 * R ^ 2 := by
          gcongr
        _ ≤ _ := by
          have hα0 : 0 ≤ α 0 := hα.1 0
          nlinarith [mul_nonneg hα0 hC]
    have hvar : ∀ t ∈ Finset.range T,
        |v t| ≤ 192 * τ * φinf ^ 2 * R ^ 2 := by
      intro t ht
      by_cases ha' : active t
      · have hv := (energy_centered_observable_bound M τ φinf rinf B R
            θstar (θ t) hbounds hmix hstar hrB hBR ha').2.2.1 (path (t + 1))
        simp only [v, ha', if_true]
        have hC : 0 ≤ τ * φinf ^ 2 * R ^ 2 := by positivity
        nlinarith
      · simp [v, ha']
        positivity
    have hlip : ∀ t ∈ Finset.range T,
        |w t| ≤ 672 * α t * τ * φinf ^ 4 * R ^ 2 := by
      intro t ht
      by_cases hn : active (t + 1)
      · have hαnext : α (t + 1) = η (t + 1) := by
          dsimp [α, active, θ] at hn ⊢
          rw [td_stopped_stepsize, if_pos hn]
        have hαnextpos : 0 < α (t + 1) := by
          rw [hαnext]
          exact hηpos (t + 1)
        have hαtpos : 0 < α t :=
          lt_of_lt_of_le hαnextpos (hα.2 (Nat.le_succ t))
        have hc : active t := by
          by_contra hnc
          have hz : α t = 0 := by
            dsimp [α, active, θ] at hnc ⊢
            rw [td_stopped_stepsize, if_neg hnc]
          linarith
        have hαeq : α t = η t := by
          dsimp [α, active, θ] at hc ⊢
          rw [td_stopped_stepsize, if_pos hc]
        have hrec :
            θ (t + 1) = θ t + α t •
              td_update M (θ t) (path t) (path (t + 1)) := by
          dsimp [θ, α]
          rw [td_stopped_iterates, td_stopped_stepsize]
          split_ifs <;> ext i <;> simp <;> ring
        have hg := energy_sample_update_bound M φinf rinf B R (θ t)
          (path t) (path (t + 1)) hbounds hrB hBR hc
        have hdist :
            td_euclidean_norm (θ t - θ (t + 1)) ≤
              (5 / 2 : ℝ) * α t * φinf ^ 2 * R := by
          rw [hrec]
          have heq : θ t - (θ t + α t •
              td_update M (θ t) (path t) (path (t + 1))) =
              (-α t) • td_update M (θ t) (path t) (path (t + 1)) := by
            ext i
            simp
          rw [heq, energy_td_euclidean_norm_smul, abs_neg,
            abs_of_pos hαtpos]
          calc
            α t * td_euclidean_norm
                (td_update M (θ t) (path t) (path (t + 1))) ≤
                α t * ((5 / 2 : ℝ) * φinf ^ 2 * R) :=
              mul_le_mul_of_nonneg_left hg hαtpos.le
            _ = _ := by ring
        have hpo := energy_poisson_lipschitz M τ φinf rinf B R
          θstar (θ t) (θ (t + 1)) hbounds hmix hstar hrB hBR hc hn
          (path (t + 1))
        simp only [w, hn, if_true, v, hc, u]
        have hK : 0 ≤ 264 * τ * φinf ^ 2 * R :=
          mul_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) hτ0) (sq_nonneg φinf)) hR
        have hp := mul_le_mul_of_nonneg_left hdist hK
        exact hpo.trans (hp.trans (by
          have hC : 0 ≤ α t * τ * φinf ^ 4 * R ^ 2 := by
            exact mul_nonneg
              (mul_nonneg (mul_nonneg hαtpos.le hτ0) (by positivity))
              (by positivity)
          nlinarith))
      · rw [show w t = 0 by simp [w, hn]]
        have hK : 0 ≤ 672 * α t * τ * φinf ^ 4 * R ^ 2 := by
          exact mul_nonneg
            (mul_nonneg
              (mul_nonneg (mul_nonneg (by norm_num) (hα.1 t)) hτ0)
              (by positivity)) (by positivity)
        simpa only [abs_zero] using hK
    have habel := energy_abel_remainder_bound_nonnegative α u v w τ φinf R T
      hT hα.1 hα.2 hτ0 hφpos.le hR hend hvar hlip
    have habelid :
        ∑ t ∈ Finset.range T, α t * (u t - v t) =
          α 0 * u 0 - α T * u T -
            (∑ t ∈ Finset.range T, (α t - α (t + 1)) * v t) -
            (∑ t ∈ Finset.range T, α (t + 1) * w t) := by
      have hw :
          (∑ t ∈ Finset.range T, α (t + 1) * w t) =
            ∑ t ∈ Finset.range T, α (t + 1) * (v t - u (t + 1)) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact hwend t
      rw [hw]
      simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib]
      have htel := Finset.sum_range_sub' (f := fun t => α t * u t) T
      have hsum :
          (∑ t ∈ Finset.range T, α t * u t) -
              (∑ t ∈ Finset.range T, α (t + 1) * u (t + 1)) =
            ∑ t ∈ Finset.range T,
              (α t * u t - α (t + 1) * u (t + 1)) :=
        (Finset.sum_sub_distrib
          (fun t => α t * u t)
          (fun t => α (t + 1) * u (t + 1))).symm
      linear_combination hsum + htel
    have hrem :
        td_stopped_recursion_remainder M η θ0 θstar R path T ≤
          768 * τ * φinf ^ 2 * R ^ 2 * Real.sqrt (pr_square_mass η) *
              Real.sqrt (2 * Real.log (8 / δ)) +
            1152 * η 0 * τ * φinf ^ 2 * R ^ 2 +
            1344 * τ * φinf ^ 4 * R ^ 2 * pr_square_mass η := by
      have hm := hpath T
      rw [hbmass] at hm
      have hlog : 2 / (δ / 4) = 8 / δ := by field_simp; ring
      rw [hlog] at hm
      have hsumdec :
          ∑ t ∈ Finset.range T,
              α t * energy_centered_scalar M θstar (θ t)
                (path t) (path (t + 1)) =
            (∑ t ∈ Finset.range T,
              F t (Preorder.frestrictLe t path) (path (t + 1))) +
              ∑ t ∈ Finset.range T, α t * (u t - v t) := by
        simp_rw [hdecomp, Finset.sum_add_distrib]
      have hfinite :
          (∑ t ∈ Finset.range T, (α t) ^ 2) ≤ pr_square_mass η := by
        calc
          _ ≤ ∑ t ∈ Finset.range T, (η t) ^ 2 := by
            apply Finset.sum_le_sum
            intro t ht
            have haη : α t ≤ η t := by
              dsimp [α]
              rw [td_stopped_stepsize]
              split_ifs
              · exact le_rfl
              · exact hηnonneg t
            nlinarith [hα.1 t, hηnonneg t]
          _ ≤ _ := hηsum.sum_le_tsum (Finset.range T)
            (fun t ht => sq_nonneg (η t))
      rw [energy_stopped_remainder_identity, hsumdec, habelid]
      have habs := abs_add_le
        (∑ t ∈ Finset.range T,
          F t (Preorder.frestrictLe t path) (path (t + 1)))
        (α 0 * u 0 - α T * u T -
          (∑ t ∈ Finset.range T, (α t - α (t + 1)) * v t) -
          (∑ t ∈ Finset.range T, α (t + 1) * w t))
      have hα0 : α 0 = η 0 := by
        dsimp [α, θ, R] at hθ0 ⊢
        rw [td_stopped_stepsize, td_stopped_iterates, if_pos hθ0]
      have hC : 0 ≤ 672 * τ * φinf ^ 4 * R ^ 2 := by positivity
      have habelfin :
          576 * α 0 * τ * φinf ^ 2 * R ^ 2 +
              672 * τ * φinf ^ 4 * R ^ 2 *
                (∑ t ∈ Finset.range T, (α t) ^ 2) ≤
            576 * α 0 * τ * φinf ^ 2 * R ^ 2 +
              672 * τ * φinf ^ 4 * R ^ 2 * pr_square_mass η := by
        have hmulf := mul_le_mul_of_nonneg_left hfinite hC
        linarith
      have habel' := habel.trans habelfin
      have htotal :
          (∑ t ∈ Finset.range T,
              F t (Preorder.frestrictLe t path) (path (t + 1))) +
              (α 0 * u 0 - α T * u T -
                (∑ t ∈ Finset.range T, (α t - α (t + 1)) * v t) -
                (∑ t ∈ Finset.range T, α (t + 1) * w t)) ≤
            384 * τ * φinf ^ 2 * R ^ 2 * Real.sqrt (pr_square_mass η) *
                Real.sqrt (2 * Real.log (8 / δ)) +
              (576 * α 0 * τ * φinf ^ 2 * R ^ 2 +
                672 * τ * φinf ^ 4 * R ^ 2 * pr_square_mass η) := by
        calc
          _ ≤ |(∑ t ∈ Finset.range T,
                F t (Preorder.frestrictLe t path) (path (t + 1))) +
              (α 0 * u 0 - α T * u T -
                (∑ t ∈ Finset.range T, (α t - α (t + 1)) * v t) -
                (∑ t ∈ Finset.range T, α (t + 1) * w t))| := le_abs_self _
          _ ≤ _ := habs.trans (add_le_add hm habel')
      rw [hα0] at htotal
      rw [hα0]
      linarith
    have henergy :
        ∑ t ∈ Finset.range T, (α t) ^ 2 *
            td_euclidean_norm
              (td_update M (θ t) (path t) (path (t + 1))) ^ 2 ≤
          9 * φinf ^ 4 * R ^ 2 * pr_square_mass η := by
      calc
        _ ≤ ∑ t ∈ Finset.range T,
            9 * φinf ^ 4 * R ^ 2 * (η t) ^ 2 := by
          apply Finset.sum_le_sum
          intro t ht
          by_cases ha' : active t
          · have hαeq : α t = η t := by
              dsimp [α, active, θ] at ha' ⊢
              rw [td_stopped_stepsize, if_pos ha']
            have hg := energy_sample_update_bound M φinf rinf B R (θ t)
              (path t) (path (t + 1)) hbounds hrB hBR ha'
            rw [hαeq]
            have hηsq : 0 ≤ (η t) ^ 2 := sq_nonneg _
            have hgsq : td_euclidean_norm
                (td_update M (θ t) (path t) (path (t + 1))) ^ 2 ≤
                ((5 / 2 : ℝ) * φinf ^ 2 * R) ^ 2 :=
              (sq_le_sq₀ (Real.sqrt_nonneg _)
                (by positivity : 0 ≤ (5 / 2 : ℝ) * φinf ^ 2 * R)).2 hg
            have hmul := mul_le_mul_of_nonneg_left hgsq hηsq
            nlinarith
          · have hz : α t = 0 := by
              dsimp [α, active, θ] at ha' ⊢
              rw [td_stopped_stepsize, if_neg ha']
            rw [hz]
            norm_num
            positivity
        _ = 9 * φinf ^ 4 * R ^ 2 *
            (∑ t ∈ Finset.range T, (η t) ^ 2) := by
          rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (hηsum.sum_le_tsum (Finset.range T)
            (fun t ht => sq_nonneg (η t))) (by positivity)
    change (∑ t ∈ Finset.range T, (α t) ^ 2 *
        td_euclidean_norm
          (td_update M (θ t) (path t) (path (t + 1))) ^ 2) +
      td_stopped_recursion_remainder M η θ0 θstar R path T ≤ _
    nlinarith
  calc
    1 - δ / 4 ≤ (td_markov_path_measure M s0).real E := hprob
    _ ≤ (td_markov_path_measure M s0).real
        (stopped_energy_control_event M a η δ c τ φinf rinf θ0 θstar) :=
      MeasureTheory.measureReal_mono hsubset

@[blueprint "lem:stopped-bootstrap-stationary-quadratic-identity"
  (statement := /-- Let $\pi\colon\operatorname{Fin}(n)\to\mathbb R$ and $P\colon\operatorname{Fin}(n)^2\to\mathbb R$ satisfy $\sum_{s'}P(s,s')=1$ and $\sum_s\pi(s)P(s,s')=\pi(s')$.  Then, for every $\gamma\in\mathbb R$ and $x\colon\operatorname{Fin}(n)\to\mathbb R$,
  \[
  \sum_{s,s'}\pi(s)P(s,s')x(s)(x(s)-\gamma x(s'))
  =(1-\gamma)\sum_s\pi(s)x(s)^2
  +\frac{\gamma}{2}\sum_{s,s'}\pi(s)P(s,s')(x(s)-x(s'))^2.
  \] -/)
  (proof := /-- Expand the square in the second term.  The row-mass identity rewrites the contribution containing $x(s)^2$ as $\sum_s\pi(s)x(s)^2$, and stationarity rewrites the contribution containing $x(s')^2$ as the same sum.  The remaining cross term is $-\gamma\sum_{s,s'}\pi(s)P(s,s')x(s)x(s')$ on both sides. -/)
  (title := /-- Stationary quadratic identity for the stopped bootstrap -/)
  (latexEnv := "lemma")]
lemma stopped_bootstrap_stationary_quadratic_identity {n : ℕ}
    (π : Fin n → ℝ) (P : Fin n → Fin n → ℝ) (γ : ℝ) (x : Fin n → ℝ)
    (hrow : ∀ s, ∑ s', P s s' = 1)
    (hstat : ∀ s', ∑ s, π s * P s s' = π s') :
    (∑ s, ∑ s', π s * P s s' * x s * (x s - γ * x s')) =
      (1 - γ) * ∑ s, π s * (x s) ^ 2 +
        γ * (1 / 2 : ℝ) * ∑ s, ∑ s', π s * P s s' * (x s - x s') ^ 2 := by
  have hleft :
      (∑ s, ∑ s', π s * P s s' * (x s) ^ 2) = ∑ s, π s * (x s) ^ 2 := by
    apply Finset.sum_congr rfl
    intro s hs
    calc
      (∑ s', π s * P s s' * (x s) ^ 2) =
          (π s * (x s) ^ 2) * ∑ s', P s s' := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro s' hs'
            ring
      _ = π s * (x s) ^ 2 := by rw [hrow s, mul_one]
  have hright :
      (∑ s, ∑ s', π s * P s s' * (x s') ^ 2) = ∑ s, π s * (x s) ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s' hs'
    calc
      (∑ s, π s * P s s' * (x s') ^ 2) =
          (∑ s, π s * P s s') * (x s') ^ 2 := by rw [Finset.sum_mul]
      _ = π s' * (x s') ^ 2 := by rw [hstat s']
  have hcross :
      (∑ s, ∑ s', π s * P s s' * x s * (γ * x s')) =
        γ * ∑ s, ∑ s', π s * P s s' * x s * x s' := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s' hs'
    ring
  have hmain :
      (∑ s, ∑ s', π s * P s s' * x s * (x s - γ * x s')) =
        (∑ s, π s * (x s) ^ 2) -
          γ * ∑ s, ∑ s', π s * P s s' * x s * x s' := by
    calc
      _ = (∑ s, ∑ s', π s * P s s' * (x s) ^ 2) -
          γ * ∑ s, ∑ s', π s * P s s' * x s * x s' := by
            simp_rw [mul_sub, Finset.sum_sub_distrib]
            rw [hcross]
            congr 1
            apply Finset.sum_congr rfl
            intro s hs
            apply Finset.sum_congr rfl
            intro s' hs'
            ring
      _ = _ := by rw [hleft]
  rw [hmain]
  have hmiddle :
      (∑ s, ∑ s', π s * P s s' * (2 * x s * x s')) =
        2 * ∑ s, ∑ s', π s * P s s' * x s * x s' := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s' hs'
    ring
  simp_rw [sub_sq, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  rw [hleft, hright, hmiddle]
  ring

@[blueprint "lem:stopped-bootstrap-fixed-point-drift-identity"
  (statement := /-- Let $M$ be a finite TD model and let $\theta^*$ be a TD fixed point.  For every $\theta\in\mathbb R^d$,
  \[
  \langle\bar g(\theta),\theta^*-\theta\rangle
  =f(\theta)-f(\theta^*).
  \] -/)
  (proof := /-- By \cref{def:td-fixed-point,def:td-mean-update}, the left-hand side is the population quadratic form in $\theta^*-\theta$.  Expanding the population matrix using \cref{def:td-population-matrix,def:td-sample-matrix} expresses it as the stationary transition average of $x(s)(x(s)-\gamma x(s'))$, where $x(s)=\phi(s)^\top(\theta^*-\theta)$.  The transition rows have unit mass, and the stationary distribution satisfies the identity in \cref{def:td-model}.  Therefore \cref{lem:stopped-bootstrap-stationary-quadratic-identity} identifies this quadratic form with the weighted-square and Dirichlet terms in \cref{def:td-potential}. -/)
  (title := /-- Fixed-point drift identity for the stopped bootstrap -/)
  (latexEnv := "lemma")]
lemma stopped_bootstrap_fixed_point_drift_identity {n d : ℕ} (M : td_model n d)
    (θstar θ : td_vector d) (hfixed : td_fixed_point M θstar) :
    td_mean_update M θ ⬝ᵥ (θstar - θ) =
      td_potential M θstar θ - td_potential M θstar θstar := by
  let y : td_vector d := θstar - θ
  let x : Fin n → ℝ := fun s => M.feature s ⬝ᵥ y
  have hrow (s : Fin n) : ∑ s', ((M.transition s) s').toReal = 1 := by
    rw [← ENNReal.toReal_sum]
    · have hmass : ∑ s', (M.transition s) s' = 1 := by
        simpa only [tsum_fintype] using (PMF.hasSum_coe_one (M.transition s)).tsum_eq
      rw [hmass]
      norm_num
    · intro s' hs'
      exact PMF.apply_ne_top (M.transition s) s'
  have hmean : td_mean_update M θ = Matrix.mulVec (td_population_matrix M) y := by
    unfold td_mean_update
    rw [← hfixed]
    dsimp [y]
    rw [Matrix.mulVec_sub]
  have hmul (i : Fin d) :
      Matrix.mulVec (td_population_matrix M) y i =
        ∑ s, ∑ s', (M.stationary s).toReal * ((M.transition s) s').toReal *
          M.feature s i * (x s - M.discount * x s') := by
    unfold td_population_matrix td_sample_matrix Matrix.mulVec
    calc
      (∑ j, (∑ s, ∑ s', (M.stationary s).toReal *
          ((M.transition s) s').toReal *
          (M.feature s i * (M.feature s j - M.discount * M.feature s' j))) * y j) =
          ∑ j, ∑ s, ∑ s', (M.stationary s).toReal *
            ((M.transition s) s').toReal *
            (M.feature s i * (M.feature s j - M.discount * M.feature s' j)) * y j := by
              simp_rw [Finset.sum_mul]
      _ = ∑ s, ∑ s', ∑ j, (M.stationary s).toReal *
          ((M.transition s) s').toReal *
          (M.feature s i * (M.feature s j - M.discount * M.feature s' j)) * y j := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro s hs
            rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s hs
        apply Finset.sum_congr rfl
        intro s' hs'
        dsimp [x]
        unfold dotProduct
        rw [mul_sub]
        simp_rw [Finset.mul_sum]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hlhs :
      td_mean_update M θ ⬝ᵥ (θstar - θ) =
        ∑ s, ∑ s', (M.stationary s).toReal * ((M.transition s) s').toReal *
          x s * (x s - M.discount * x s') := by
    rw [hmean]
    change Matrix.mulVec (td_population_matrix M) y ⬝ᵥ y = _
    unfold dotProduct
    simp_rw [hmul]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s' hs'
    dsimp [x]
    unfold dotProduct
    calc
      (∑ i, (M.stationary s).toReal * ((M.transition s) s').toReal *
          M.feature s i *
          (∑ j, M.feature s j * y j - M.discount * ∑ j, M.feature s' j * y j) * y i) =
          ∑ i, ((M.stationary s).toReal * ((M.transition s) s').toReal *
            (∑ j, M.feature s j * y j - M.discount * ∑ j, M.feature s' j * y j)) *
            (M.feature s i * y i) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = ((M.stationary s).toReal * ((M.transition s) s').toReal *
            (∑ j, M.feature s j * y j - M.discount * ∑ j, M.feature s' j * y j)) *
          ∑ i, M.feature s i * y i := by rw [← Finset.mul_sum]
      _ = _ := by ring
  have hvalue (s : Fin n) :
      td_value M θ s - td_value M θstar s = -x s := by
    unfold td_value
    dsimp [x, y]
    unfold dotProduct
    simp_rw [Pi.sub_apply, mul_sub]
    rw [Finset.sum_sub_distrib]
    ring
  have hquad := stopped_bootstrap_stationary_quadratic_identity
    (fun s => (M.stationary s).toReal)
    (fun s s' => ((M.transition s) s').toReal) M.discount x hrow M.stationary_eq
  calc
    td_mean_update M θ ⬝ᵥ (θstar - θ) =
        ∑ s, ∑ s', (M.stationary s).toReal * ((M.transition s) s').toReal *
          x s * (x s - M.discount * x s') := hlhs
    _ = (1 - M.discount) * ∑ s, (M.stationary s).toReal * (x s) ^ 2 +
        M.discount * (1 / 2 : ℝ) *
          ∑ s, ∑ s', (M.stationary s).toReal * ((M.transition s) s').toReal *
            (x s - x s') ^ 2 := hquad
    _ = td_potential M θstar θ - td_potential M θstar θstar := by
      unfold td_potential td_weighted_square td_dirichlet_energy
      simp only [Pi.sub_apply]
      simp_rw [hvalue]
      simp
      ring_nf

@[blueprint "lem:stopped-bootstrap-drift-nonpositive"
  (statement := /-- Let $M$ be a finite TD model and let $\theta^*$ be a TD fixed point.  Then for every $\theta\in\mathbb R^d$,
  \[
  \langle\bar g(\theta),\theta-\theta^*\rangle\leq0.
  \] -/)
  (proof := /-- By \cref{lem:stopped-bootstrap-fixed-point-drift-identity}, the same inner product with $\theta^*-\theta$ equals $f(\theta)-f(\theta^*)$.  The definition \cref{def:td-potential}, the bounds $0\leq\gamma<1$, and nonnegativity of the stationary and transition weights show that this difference is nonnegative.  Reversing the second argument of the inner product changes its sign and proves the claim. -/)
  (title := /-- Nonpositivity of the stopped-bootstrap drift -/)
  (latexEnv := "lemma")]
lemma stopped_bootstrap_drift_nonpositive {n d : ℕ} (M : td_model n d)
    (θstar θ : td_vector d) (hfixed : td_fixed_point M θstar) :
    td_mean_update M θ ⬝ᵥ (θ - θstar) ≤ 0 := by
  have hid := stopped_bootstrap_fixed_point_drift_identity M θstar θ hfixed
  have hzero : td_potential M θstar θstar = 0 := by
    simp [td_potential, td_weighted_square, td_dirichlet_energy]
  have hpotential : 0 ≤ td_potential M θstar θ := by
    unfold td_potential td_weighted_square td_dirichlet_energy
    have hγ : 0 ≤ M.discount := M.discount_nonneg
    have hγ' : 0 ≤ 1 - M.discount := by linarith [M.discount_lt_one]
    positivity
  have hsign :
      td_mean_update M θ ⬝ᵥ (θ - θstar) =
        -(td_mean_update M θ ⬝ᵥ (θstar - θ)) := by
    unfold dotProduct
    simp_rw [Pi.sub_apply]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsign, hid, hzero]
  linarith

@[blueprint "lem:stopped-bootstrap-implies-radius"
  (statement := /-- Let $M$ be a finite TD model, let $\theta^*$ be a TD fixed point, and let $\phi_\infty>0$, $r_\infty\geq0$, and $\tau\geq1$ satisfy the uniform boundedness and geometric-mixing hypotheses.  Let $(a_t)$ be positive and non-increasing, with $a_0\leq1$ and $\sum_ta_t^2<\infty$, put $\eta_t=(c\tau\phi_\infty^2)^{-1}a_t$, fix $\delta\in(0,1)$, and suppose $c>c_{\min}(\delta)$.  For every initial vector $\theta_0$, every path in the stopped energy-control event belongs to the uniform bounded-iterate event. -/)
  (proof := /-- Put $R_{\mathrm{base}}=\max\{\|\theta_0-\theta^*\|_2,\|\theta^*\|_2,r_\infty/\phi_\infty\}$ and $R_{\max}=\rho R_{\mathrm{base}}$ as in \cref{def:pr-base-radius,def:pr-rho}.  The hypotheses imply $c>0$, $\tau\geq1$, and $\phi_\infty>0$.  Hence the schedule in \cref{def:pr-eta-base} is positive and, with $S=\sum_ta_t^2$ and $H$ as in \cref{def:pr-square-mass},
  \[
  H=(c\tau\phi_\infty^2)^{-2}S,
  \qquad
  \sqrt H=(c\tau\phi_\infty^2)^{-1}\sqrt S.
  \]
  For every $T\geq1$, expanding \cref{def:td-stopped-recursion-remainder} gives
  \[
  \|\widetilde\theta_T-\theta^*\|_2^2
  =\|\theta_0-\theta^*\|_2^2
  +\sum_{t<T}\widetilde\eta_t^2
    \|g(\widetilde\theta_t,Z_t)\|_2^2
  +2\sum_{t<T}\widetilde\eta_t
    \langle\bar g(\widetilde\theta_t),
      \widetilde\theta_t-\theta^*\rangle
  +\widetilde B_T.
  \]
  Every stopped stepsize is nonnegative, and \cref{lem:stopped-bootstrap-drift-nonpositive} makes every summand in the inner-product sum nonpositive.  The defining estimate of \cref{def:stopped-energy-control-event} therefore bounds the stopped squared error by the initial squared error plus its displayed energy bound $E$.  The coordinatewise inequality $(x+y)^2\leq2x^2+2y^2$ and the definition of $R_{\mathrm{base}}$ yield
  \[
  \|\widetilde\theta_T\|_2^2\leq4R_{\mathrm{base}}^2+2E.
  \]
  Substituting the preceding identities for $H$ and $\sqrt H$, using $a_0\leq1$ and $\tau\geq1$, and collecting the four terms in $E$ gives
  \[
  \|\widetilde\theta_T\|_2^2
  \leq R_{\mathrm{base}}^2
  \left(4+1536\frac{\rho^2}{c}\sqrt{\sum_ta_t^2}
  \sqrt{2\log\frac8\delta}+2304\frac{\rho^2}{c}
  +2706\frac{\rho^2}{c^2}\sum_ta_t^2\right).
  \]
  By \cref{lem:rho-bootstrap-inequality}, the parenthesized expression is at most $\rho^2$, and $\rho>2$.  The same coordinatewise estimate gives $\|\theta_0\|_2\leq2R_{\mathrm{base}}\leq R_{\max}$, so the bound holds also at $T=0$.  Thus $\|\widetilde\theta_T\|_2\leq R_{\max}$ for every $T$.  The recursion in \cref{def:td-stopped-iterates,def:td-stopped-stepsize} consequently always selects the original stepsize; induction using \cref{def:td-iterates} gives $\widetilde\theta_T=\theta_T$ for every $T$.  Hence the original path belongs to the uniform bounded-iterate event \cref{def:bounded-iterates-event}. -/)
  (title := /-- The stopped bootstrap prevents exit -/)
  (latexEnv := "lemma")]
lemma stopped_bootstrap_implies_radius {n d : ℕ} (M : td_model n d)
    (a η : ℕ → ℝ) (δ c τ φinf rinf : ℝ) (θ0 θstar : td_vector d)
    (ha : admissible_stepsize_shape a)
    (hη : ∀ t, η t = pr_eta_base c τ φinf * a t)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hc : pr_c_min a δ < c)
    (hbounds : td_uniform_bounds M φinf rinf)
    (hmix : td_geometric_mixing M τ) (hfixed : td_fixed_point M θstar) :
    stopped_energy_control_event M a η δ c τ φinf rinf θ0 θstar ⊆
      bounded_iterates_event M a η δ c φinf rinf θ0 θstar := by
  intro path hpath
  have hφpos : 0 < φinf := hbounds.1
  have hrnonneg : 0 ≤ rinf := hbounds.2.1
  have hτ : 1 ≤ τ := hmix.1
  have hA : 0 < pr_a_one a δ := by
    rw [pr_a_one]
    positivity
  have hBtwo : 0 ≤ pr_a_two a := by
    rw [pr_a_two]
    positivity
  have hcpos : 0 < c := by
    have hsqrt := Real.sqrt_nonneg ((pr_a_one a δ) ^ 2 + 4 * pr_a_two a)
    rw [pr_c_min] at hc
    nlinarith
  have hbasepos : 0 < pr_eta_base c τ φinf := by
    unfold pr_eta_base
    positivity
  have hηpos : ∀ t, 0 < η t := by
    intro t
    rw [hη t]
    exact mul_pos hbasepos (ha.1 t)
  have hsum : 0 ≤ ∑' t, (a t) ^ 2 := tsum_nonneg (fun t => sq_nonneg (a t))
  have hmass :
      pr_square_mass η =
        (pr_eta_base c τ φinf) ^ 2 * ∑' t, (a t) ^ 2 := by
    unfold pr_square_mass
    simp_rw [hη, mul_pow]
    rw [tsum_mul_left]
  have hsqrtmass :
      Real.sqrt (pr_square_mass η) =
        pr_eta_base c τ φinf * Real.sqrt (∑' t, (a t) ^ 2) := by
    rw [hmass, Real.sqrt_mul (sq_nonneg (pr_eta_base c τ φinf))]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hbasepos]
  obtain ⟨hρ, hbootstrap⟩ :=
    rho_bootstrap_inequality a δ c ha hδ0 hδ1 hc
  let ρ := pr_rho a δ c
  let B := pr_base_radius θ0 θstar rinf φinf
  let R := ρ * B
  have hB : 0 ≤ B := by
    dsimp [B, pr_base_radius]
    positivity
  have herr0 : td_euclidean_norm (θ0 - θstar) ≤ B := by
    dsimp [B, pr_base_radius]
    exact le_max_left _ _
  have hstar : td_euclidean_norm θstar ≤ B := by
    dsimp [B, pr_base_radius]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hR : 0 ≤ R := mul_nonneg (by dsimp [ρ]; linarith) hB
  have hnorm_nonneg (v : td_vector d) : 0 ≤ td_euclidean_norm v := by
    unfold td_euclidean_norm
    positivity
  have hnorm_sq (v : td_vector d) :
      (td_euclidean_norm v) ^ 2 = ∑ i, (v i) ^ 2 := by
    unfold td_euclidean_norm
    rw [Real.sq_sqrt]
    exact Finset.sum_nonneg fun i hi => sq_nonneg (v i)
  have hshift_sq (v : td_vector d) :
      (td_euclidean_norm v) ^ 2 ≤
        2 * (td_euclidean_norm (v - θstar)) ^ 2 +
          2 * (td_euclidean_norm θstar) ^ 2 := by
    rw [hnorm_sq, hnorm_sq, hnorm_sq]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    simp only [Pi.sub_apply]
    nlinarith [sq_nonneg (v i - 2 * θstar i)]
  have hstop : ∀ T, td_euclidean_norm
      (td_stopped_iterates M η θ0 R T path) ≤ R := by
    intro T
    cases T with
    | zero =>
        simp only [td_stopped_iterates]
        have hsquare := hshift_sq θ0
        have herr0_nonneg := hnorm_nonneg (θ0 - θstar)
        have hstar_nonneg := hnorm_nonneg θstar
        have hθ0_nonneg := hnorm_nonneg θ0
        have htwo : 2 * B ≤ R := by
          dsimp [R, ρ]
          nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_lt hρ)) hB]
        nlinarith [sq_nonneg (B - td_euclidean_norm (θ0 - θstar)),
          sq_nonneg (B - td_euclidean_norm θstar)]
    | succ T =>
        have hTpos : 1 ≤ T + 1 := Nat.succ_le_succ (Nat.zero_le T)
        have henergy := hpath (T + 1) hTpos
        dsimp only at henergy
        let E :=
          768 * τ * φinf ^ 2 * R ^ 2 * Real.sqrt (pr_square_mass η) *
              Real.sqrt (2 * Real.log (8 / δ)) +
            1152 * η 0 * τ * φinf ^ 2 * R ^ 2 +
            1344 * τ * φinf ^ 4 * R ^ 2 * pr_square_mass η +
            9 * φinf ^ 4 * R ^ 2 * pr_square_mass η
        have henergy' :
            (∑ t ∈ Finset.range (T + 1),
                (td_stopped_stepsize M η θ0 R path t) ^ 2 *
                  (td_euclidean_norm
                    (td_update M (td_stopped_iterates M η θ0 R t path)
                      (path t) (path (t + 1)))) ^ 2) +
                td_stopped_recursion_remainder M η θ0 θstar R path (T + 1) ≤ E := by
          simpa [E, R, ρ, B] using henergy
        have hstoppedη (t : ℕ) :
            0 ≤ td_stopped_stepsize M η θ0 R path t := by
          unfold td_stopped_stepsize
          split_ifs
          · exact le_of_lt (hηpos t)
          · exact le_rfl
        have hdrift :
            (∑ t ∈ Finset.range (T + 1),
              td_stopped_stepsize M η θ0 R path t *
                (td_mean_update M (td_stopped_iterates M η θ0 R t path) ⬝ᵥ
                  (td_stopped_iterates M η θ0 R t path - θstar))) ≤ 0 := by
          apply Finset.sum_nonpos
          intro t ht
          exact mul_nonpos_of_nonneg_of_nonpos (hstoppedη t)
            (stopped_bootstrap_drift_nonpositive M θstar
              (td_stopped_iterates M η θ0 R t path) hfixed)
        have herr_energy :
            (td_euclidean_norm
              (td_stopped_iterates M η θ0 R (T + 1) path - θstar)) ^ 2 ≤
                (td_euclidean_norm (θ0 - θstar)) ^ 2 + E := by
          unfold td_stopped_recursion_remainder at henergy'
          nlinarith
        have hsquare :=
          hshift_sq (td_stopped_iterates M η θ0 R (T + 1) path)
        have hτpos : 0 < τ := lt_of_lt_of_le zero_lt_one hτ
        have heta_coefficient : η 0 * τ * φinf ^ 2 ≤ 1 / c := by
          rw [hη 0]
          unfold pr_eta_base
          calc
            (1 / (c * τ * φinf ^ 2) * a 0) * τ * φinf ^ 2 = a 0 / c := by
              field_simp [ne_of_gt hcpos, ne_of_gt hτpos, ne_of_gt hφpos]
              <;> ring
            _ ≤ 1 / c := (div_le_div_iff_of_pos_right hcpos).2 ha.2.2.1
        have hfirst :
            2 * (768 * τ * φinf ^ 2 * R ^ 2 * Real.sqrt (pr_square_mass η) *
              Real.sqrt (2 * Real.log (8 / δ))) =
              B ^ 2 * (1536 * ρ ^ 2 / c * Real.sqrt (∑' t, (a t) ^ 2) *
                Real.sqrt (2 * Real.log (8 / δ))) := by
          rw [hsqrtmass]
          dsimp [R, ρ]
          unfold pr_eta_base
          field_simp [ne_of_gt hcpos, ne_of_gt hτpos, ne_of_gt hφpos]
          <;> ring
        have hsecond :
            2 * (1152 * η 0 * τ * φinf ^ 2 * R ^ 2) ≤
              B ^ 2 * (2304 * ρ ^ 2 / c) := by
          calc
            2 * (1152 * η 0 * τ * φinf ^ 2 * R ^ 2) =
                2304 * (η 0 * τ * φinf ^ 2) * R ^ 2 := by ring
            _ ≤ 2304 * (1 / c) * R ^ 2 := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left heta_coefficient (by norm_num))
                (sq_nonneg R)
            _ = B ^ 2 * (2304 * ρ ^ 2 / c) := by
              dsimp [R]
              ring
        have hτsq : 1 ≤ τ ^ 2 := by nlinarith
        have h2688 : 2688 / τ ≤ (2688 : ℝ) := by
          apply (div_le_iff₀ hτpos).2
          nlinarith
        have h18 : 18 / τ ^ 2 ≤ (18 : ℝ) := by
          apply (div_le_iff₀ (sq_pos_of_pos hτpos)).2
          nlinarith
        have hcoefficient : 2688 / τ + 18 / τ ^ 2 ≤ (2706 : ℝ) := by
          linarith
        have hthird :
            2 * (1344 * τ * φinf ^ 4 * R ^ 2 * pr_square_mass η +
              9 * φinf ^ 4 * R ^ 2 * pr_square_mass η) ≤
              B ^ 2 * (2706 * (∑' t, (a t) ^ 2) * ρ ^ 2 / c ^ 2) := by
          calc
            2 * (1344 * τ * φinf ^ 4 * R ^ 2 * pr_square_mass η +
                9 * φinf ^ 4 * R ^ 2 * pr_square_mass η) =
                (R ^ 2 * (∑' t, (a t) ^ 2) / c ^ 2) *
                  (2688 / τ + 18 / τ ^ 2) := by
                    rw [hmass]
                    unfold pr_eta_base
                    field_simp [ne_of_gt hcpos, ne_of_gt hτpos, ne_of_gt hφpos]
                    <;> ring
            _ ≤ (R ^ 2 * (∑' t, (a t) ^ 2) / c ^ 2) * 2706 := by
              exact mul_le_mul_of_nonneg_left hcoefficient (by positivity)
            _ = B ^ 2 * (2706 * (∑' t, (a t) ^ 2) * ρ ^ 2 / c ^ 2) := by
              dsimp [R]
              ring
        have hE :
            2 * E ≤ B ^ 2 *
              (1536 * ρ ^ 2 / c * Real.sqrt (∑' t, (a t) ^ 2) *
                  Real.sqrt (2 * Real.log (8 / δ)) +
                2304 * ρ ^ 2 / c +
                2706 * (∑' t, (a t) ^ 2) * ρ ^ 2 / c ^ 2) := by
          calc
            2 * E =
                2 * (768 * τ * φinf ^ 2 * R ^ 2 * Real.sqrt (pr_square_mass η) *
                  Real.sqrt (2 * Real.log (8 / δ))) +
                2 * (1152 * η 0 * τ * φinf ^ 2 * R ^ 2) +
                2 * (1344 * τ * φinf ^ 4 * R ^ 2 * pr_square_mass η +
                  9 * φinf ^ 4 * R ^ 2 * pr_square_mass η) := by
                    dsimp [E]
                    ring
            _ ≤
                B ^ 2 * (1536 * ρ ^ 2 / c * Real.sqrt (∑' t, (a t) ^ 2) *
                  Real.sqrt (2 * Real.log (8 / δ))) +
                B ^ 2 * (2304 * ρ ^ 2 / c) +
                B ^ 2 * (2706 * (∑' t, (a t) ^ 2) * ρ ^ 2 / c ^ 2) :=
                  add_le_add (add_le_add (le_of_eq hfirst) hsecond) hthird
            _ = B ^ 2 *
                (1536 * ρ ^ 2 / c * Real.sqrt (∑' t, (a t) ^ 2) *
                    Real.sqrt (2 * Real.log (8 / δ)) +
                  2304 * ρ ^ 2 / c +
                  2706 * (∑' t, (a t) ^ 2) * ρ ^ 2 / c ^ 2) := by ring
        have herr0_sq :
            (td_euclidean_norm (θ0 - θstar)) ^ 2 ≤ B ^ 2 :=
          (sq_le_sq₀ (hnorm_nonneg (θ0 - θstar)) hB).2 herr0
        have hstar_sq : (td_euclidean_norm θstar) ^ 2 ≤ B ^ 2 :=
          (sq_le_sq₀ (hnorm_nonneg θstar) hB).2 hstar
        have hbootstrap' :
            4 +
                (1536 * ρ ^ 2 / c * Real.sqrt (∑' t, (a t) ^ 2) *
                    Real.sqrt (2 * Real.log (8 / δ)) +
                  2304 * ρ ^ 2 / c +
                  2706 * (∑' t, (a t) ^ 2) * ρ ^ 2 / c ^ 2) ≤
              ρ ^ 2 := by
          simpa [ρ, add_assoc] using hbootstrap
        have hstopped_square :
            (td_euclidean_norm
              (td_stopped_iterates M η θ0 R (T + 1) path)) ^ 2 ≤ R ^ 2 := by
          calc
            (td_euclidean_norm
                (td_stopped_iterates M η θ0 R (T + 1) path)) ^ 2 ≤
                2 * (td_euclidean_norm
                  (td_stopped_iterates M η θ0 R (T + 1) path - θstar)) ^ 2 +
                  2 * (td_euclidean_norm θstar) ^ 2 := hsquare
            _ ≤ 2 * ((td_euclidean_norm (θ0 - θstar)) ^ 2 + E) +
                  2 * (td_euclidean_norm θstar) ^ 2 := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left herr_energy (by norm_num)) le_rfl
            _ ≤ 2 * (B ^ 2 + E) + 2 * B ^ 2 := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left
                  (by
                    simpa [add_comm] using add_le_add_right herr0_sq E)
                  (by norm_num))
                (mul_le_mul_of_nonneg_left hstar_sq (by norm_num))
            _ = 4 * B ^ 2 + 2 * E := by ring
            _ ≤ B ^ 2 *
                (4 +
                  (1536 * ρ ^ 2 / c * Real.sqrt (∑' t, (a t) ^ 2) *
                      Real.sqrt (2 * Real.log (8 / δ)) +
                    2304 * ρ ^ 2 / c +
                    2706 * (∑' t, (a t) ^ 2) * ρ ^ 2 / c ^ 2)) := by
              calc
                4 * B ^ 2 + 2 * E ≤
                    4 * B ^ 2 + B ^ 2 *
                      (1536 * ρ ^ 2 / c * Real.sqrt (∑' t, (a t) ^ 2) *
                          Real.sqrt (2 * Real.log (8 / δ)) +
                        2304 * ρ ^ 2 / c +
                        2706 * (∑' t, (a t) ^ 2) * ρ ^ 2 / c ^ 2) :=
                          (by
                            simpa [add_comm] using
                              add_le_add_left hE (4 * B ^ 2))
                _ = _ := by ring
            _ ≤ B ^ 2 * ρ ^ 2 :=
              mul_le_mul_of_nonneg_left hbootstrap' (sq_nonneg B)
            _ = R ^ 2 := by
              dsimp [R]
              ring
        change td_euclidean_norm
            (td_stopped_iterates M η θ0 R (T + 1) path) ≤ R
        exact (sq_le_sq₀
          (hnorm_nonneg (td_stopped_iterates M η θ0 R (T + 1) path)) hR).1
            hstopped_square
  have heq : ∀ T, td_stopped_iterates M η θ0 R T path =
      td_iterates M η θ0 T path := by
    intro T
    induction T with
    | zero => rfl
    | succ T ih =>
        rw [td_stopped_iterates, if_pos (hstop T), td_iterates, ih]
  change ∀ T, td_euclidean_norm (td_iterates M η θ0 T path) ≤
    pr_rho a δ c * pr_base_radius θ0 θstar rinf φinf
  intro T
  rw [← heq T]
  simpa [R, ρ, B] using hstop T

@[blueprint "lem:bounded-iterates-probability"
  (statement := /-- Let $M$ be a finite TD model, let $\theta^*$ be a TD fixed point, and let $\phi_\infty>0$, $r_\infty\geq0$, and $\tau\geq1$ satisfy the uniform boundedness and geometric-mixing hypotheses.  Let $(a_t)$ be positive and non-increasing, with $a_0\leq1$ and $\sum_ta_t^2<\infty$, set $\eta_t=(c\tau\phi_\infty^2)^{-1}a_t$, fix $\delta\in(0,1)$, and suppose $c>c_{\min}(\delta)$.  For every initial vector $\theta_0$ and initial state $s_0$, the event
  \[
  \mathcal E_R=\left\{\sup_{t\geq0}\|\theta_t\|_2
  \leq\rho R_{\mathrm{base}}\right\}
  \]
  has probability at least $1-\delta/4$ under the canonical Markov path law started at $s_0$. -/)
  (proof := /-- Under the canonical probability measure of \cref{def:td-markov-path-measure}, \cref{lem:energy-stopped-martingale-control} gives the stopped energy-control event probability at least $1-\delta/4$.  By \cref{lem:stopped-bootstrap-implies-radius}, this event is contained in $\mathcal E_R$.  Monotonicity of the real-valued measure under this inclusion gives the claimed probability bound. -/)
  (title := /-- High-probability uniform boundedness -/)
  (latexEnv := "lemma")]
lemma bounded_iterates_probability {n d : ℕ} (M : td_model n d) (a η : ℕ → ℝ)
    (δ c τ φinf rinf : ℝ) (θ0 θstar : td_vector d) (s0 : Fin n)
    (ha : admissible_stepsize_shape a) (hη : ∀ t, η t = pr_eta_base c τ φinf * a t)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hc : pr_c_min a δ < c)
    (hbounds : td_uniform_bounds M φinf rinf)
    (hmix : td_geometric_mixing M τ) (hfixed : td_fixed_point M θstar) :
    (td_markov_path_measure M s0).real
        (bounded_iterates_event M a η δ c φinf rinf θ0 θstar) ≥ 1 - δ / 4 := by
  letI : MeasureTheory.IsProbabilityMeasure (td_markov_path_measure M s0) := by
    dsimp [td_markov_path_measure]
    infer_instance
  calc
    1 - δ / 4 ≤ (td_markov_path_measure M s0).real
        (stopped_energy_control_event M a η δ c τ φinf rinf θ0 θstar) :=
      energy_stopped_martingale_control M a η δ c τ φinf rinf θ0 θstar s0
        ha hη hδ0 hδ1 hc hbounds hmix hfixed
    _ ≤ _ := MeasureTheory.measureReal_mono
      (stopped_bootstrap_implies_radius M a η δ c τ φinf rinf θ0 θstar
        ha hη hδ0 hδ1 hc hbounds hmix hfixed) (MeasureTheory.measure_ne_top _ _)

@[blueprint "lem:td-edge-geometric-tail"
  (statement := /-- For every real number $\tau\geq1$, the geometric tail is summable and satisfies
  \[
  \sum_{m=1}^{\infty}2^{-m/\tau}\leq\frac74\tau.
  \] -/)
  (proof := /-- Put $x=(\log 2)/\tau$ and $q=e^{-x}=2^{-1/\tau}$.  Since $x>0$, one has $0<q<1$, so the tail is the convergent geometric series $q/(1-q)$.  The inequality $1+x\leq e^x$ implies $xq\leq1-q$, hence $q/(1-q)\leq1/x=\tau/\log2$.  Finally, the explicit lower bound $\log2>4/7$ yields $\tau/\log2\leq(7/4)\tau$. -/)
  (title := /-- Quantitative geometric-tail bound -/)
  (latexEnv := "lemma")]
lemma td_edge_geometric_tail (τ : ℝ) (hτ : 1 ≤ τ) :
    Summable (fun k : ℕ => Real.rpow 2 (-(((k + 1 : ℕ) : ℝ) / τ))) ∧
      (∑' k : ℕ, Real.rpow 2 (-(((k + 1 : ℕ) : ℝ) / τ))) ≤
        (7 / 4 : ℝ) * τ := by
  let x : ℝ := Real.log 2 / τ
  let q : ℝ := Real.rpow 2 (-(1 / τ))
  have hτpos : 0 < τ := lt_of_lt_of_le zero_lt_one hτ
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hxpos : 0 < x := div_pos hlogpos hτpos
  have hqexp : q = Real.exp (-x) := by
    dsimp [q]
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    dsimp [x]
    ring
  have hqpos : 0 < q := by rw [hqexp]; positivity
  have hqone : q < 1 := by
    rw [hqexp, Real.exp_lt_one_iff]
    linarith
  have hterm (k : ℕ) :
      Real.rpow 2 (-(((k + 1 : ℕ) : ℝ) / τ)) = q ^ (k + 1) := by
    dsimp [q]
    rw [show -(((k + 1 : ℕ) : ℝ) / τ) =
        (-(1 / τ)) * ((k + 1 : ℕ) : ℝ) by ring,
      Real.rpow_mul_natCast (by norm_num)]
  have hsumq : Summable (fun k : ℕ => q ^ k) :=
    summable_geometric_of_norm_lt_one
      (by simpa [Real.norm_eq_abs, abs_of_pos hqpos] using hqone)
  have htailq : Summable (fun k : ℕ => q ^ (k + 1)) := by
    simpa [pow_succ, mul_comm] using hsumq.mul_left q
  constructor
  · simpa only [hterm] using htailq
  · rw [show (∑' k : ℕ, Real.rpow 2 (-(((k + 1 : ℕ) : ℝ) / τ))) =
        ∑' k : ℕ, q ^ (k + 1) by
      congr 1
      funext k
      exact hterm k]
    have htailvalue : (∑' k : ℕ, q ^ (k + 1)) = q * (1 - q)⁻¹ := by
      rw [show (∑' k : ℕ, q ^ (k + 1)) = ∑' k : ℕ, q * q ^ k by
        congr 1
        funext k
        rw [pow_succ, mul_comm]]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hqpos.le hqone]
    rw [htailvalue]
    have hexp : 1 + x ≤ Real.exp x := by
      simpa [add_comm] using Real.add_one_le_exp x
    have hqmul : q * (1 + x) ≤ 1 := by
      rw [hqexp]
      calc
        Real.exp (-x) * (1 + x) ≤ Real.exp (-x) * Real.exp x :=
          mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    have hdenpos : 0 < 1 - q := sub_pos.mpr hqone
    have hxq : x * q ≤ 1 - q := by nlinarith [hqmul]
    have htailbound : q * (1 - q)⁻¹ ≤ 1 / x := by
      rw [← div_eq_mul_inv]
      apply (div_le_iff₀ hdenpos).2
      have hdiv : q ≤ (1 - q) / x := (le_div_iff₀ hxpos).2 (by
        nlinarith [hxq])
      simpa [div_eq_mul_inv, mul_comm] using hdiv
    calc
      q * (1 - q)⁻¹ ≤ 1 / x := htailbound
      _ = τ / Real.log 2 := by
        dsimp [x]
        field_simp [ne_of_gt hτpos, ne_of_gt hlogpos]
      _ ≤ (7 / 4 : ℝ) * τ := by
        have hlog43 : (1 / 4 : ℝ) ≤ Real.log (4 / 3) := by
          have h := Real.log_le_sub_one_of_pos
            (show (0 : ℝ) < 3 / 4 by norm_num)
          rw [show (3 / 4 : ℝ) = (4 / 3 : ℝ)⁻¹ by norm_num,
            Real.log_inv] at h
          norm_num at h ⊢
          linarith
        have hlog32 : (1 / 3 : ℝ) ≤ Real.log (3 / 2) := by
          have h := Real.log_le_sub_one_of_pos
            (show (0 : ℝ) < 2 / 3 by norm_num)
          rw [show (2 / 3 : ℝ) = (3 / 2 : ℝ)⁻¹ by norm_num,
            Real.log_inv] at h
          norm_num at h ⊢
          linarith
        have hlogsplit : Real.log 2 = Real.log (4 / 3) + Real.log (3 / 2) := by
          calc
            Real.log 2 = Real.log ((4 / 3 : ℝ) * (3 / 2 : ℝ)) := by norm_num
            _ = Real.log (4 / 3) + Real.log (3 / 2) :=
              Real.log_mul (by norm_num) (by norm_num)
        have hloglower : (4 / 7 : ℝ) < Real.log 2 := by
          rw [hlogsplit]
          nlinarith
        rw [div_le_iff₀ hlogpos]
        nlinarith

@[blueprint "lem:td-edge-vector-poisson"
  (statement := /-- Let $g\colon\operatorname{Fin}(n)\to\mathbb R^d$ have stationary mean zero and satisfy $\|g(s)\|_2\leq C$ for every state, where $C\geq0$.  If $M$ satisfies the geometric-mixing estimate with constant $\tau$, then there exists $v\colon\operatorname{Fin}(n)\to\mathbb R^d$ such that
  \[
  v(s)-\sum_jP(s,j)v(j)=g(s),\qquad
  \|v(s)\|_2\leq15\tau C
  \]
  for every state $s$. -/)
  (proof := /-- Transport the observable to Mathlib's Euclidean space by \cref{lem:energy-td-euclidean-norm-bridge} and form the centered series
  \[
  w(s)=\sum_{k=0}^{\infty}\sum_j((P^k)_{sj}-\pi_j)g(j).
  \]
  The mixing estimate and \cref{lem:energy-geometric-envelope} prove summability.  Stationary centering identifies the zeroth term with $g(s)$, while \cref{lem:td-edge-geometric-tail} bounds the remaining terms by $14\tau C$; hence $\|w(s)\|_2\leq C+14\tau C\leq15\tau C$.  Multiplication by $P$ shifts the series by one index, because each transition row has total mass one, so subtraction leaves the zeroth term and gives $w-Pw=g$.  Transporting back to $\mathbb R^d$ yields the asserted function. -/)
  (title := /-- Vector-valued state Poisson solution -/)
  (latexEnv := "lemma")]
lemma td_edge_vector_poisson {n d : ℕ} (M : td_model n d) (τ C : ℝ)
    (g : Fin n → td_vector d) (hmix : td_geometric_mixing M τ)
    (hC : 0 ≤ C)
    (hcenter : ∑ s, (M.stationary s).toReal • g s = 0)
    (hbound : ∀ s, td_euclidean_norm (g s) ≤ C) :
    ∃ v : Fin n → td_vector d,
      (∀ s, v s - ∑ j, (M.transition s j).toReal • v j = g s) ∧
      ∀ s, td_euclidean_norm (v s) ≤ 15 * τ * C := by
  classical
  let L : td_vector d ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  let f : Fin n → EuclideanSpace ℝ (Fin d) := fun s => L (g s)
  let a : ℕ → Fin n → EuclideanSpace ℝ (Fin d) := fun k s =>
    ∑ j, ((td_transition_matrix M ^ k) s j -
      (M.stationary j).toReal) • f j
  let w : Fin n → EuclideanSpace ℝ (Fin d) := fun s => ∑' k, a k s
  have hτ : 1 ≤ τ := hmix.1
  have hf (s : Fin n) : ‖f s‖ ≤ C := by
    change ‖L (g s)‖ ≤ C
    rw [← energy_td_euclidean_norm_bridge]
    exact hbound s
  have hfzero : ∑ s, (M.stationary s).toReal • f s = 0 := by
    have hmap := congrArg L hcenter
    simpa only [map_sum, map_smul, map_zero] using hmap
  have hterm (k : ℕ) (s : Fin n) :
      ‖a k s‖ ≤ 8 * C * Real.rpow 2 (-((k : ℝ) / τ)) := by
    dsimp only [a]
    calc
      ‖∑ j, ((td_transition_matrix M ^ k) s j -
          (M.stationary j).toReal) • f j‖ ≤
          ∑ j, ‖((td_transition_matrix M ^ k) s j -
            (M.stationary j).toReal) • f j‖ := norm_sum_le _ _
      _ ≤ ∑ j, |(td_transition_matrix M ^ k) s j -
            (M.stationary j).toReal| * C := by
          apply Finset.sum_le_sum
          intro j hj
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hf j) (abs_nonneg _)
      _ = C * ∑ j, |(td_transition_matrix M ^ k) s j -
            (M.stationary j).toReal| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
      _ ≤ C * (8 * Real.rpow 2 (-((k : ℝ) / τ))) :=
          mul_le_mul_of_nonneg_left (hmix.2 k s) hC
      _ = 8 * C * Real.rpow 2 (-((k : ℝ) / τ)) := by ring
  have hgeom := energy_geometric_envelope τ hτ
  have hsummable (s : Fin n) : Summable (fun k : ℕ => a k s) := by
    apply Summable.of_norm_bounded (hgeom.1.mul_left (8 * C))
    intro k
    exact hterm k s
  have htailgeom := td_edge_geometric_tail τ hτ
  have htailsummable (s : Fin n) : Summable (fun k : ℕ => a (k + 1) s) := by
    apply Summable.of_norm_bounded (htailgeom.1.mul_left (8 * C))
    intro k
    exact hterm (k + 1) s
  have htailbound (s : Fin n) :
      ‖∑' k : ℕ, a (k + 1) s‖ ≤ 14 * τ * C := by
    calc
      ‖∑' k : ℕ, a (k + 1) s‖ ≤ ∑' k : ℕ, ‖a (k + 1) s‖ :=
        norm_tsum_le_tsum_norm (htailsummable s).norm
      _ ≤ ∑' k : ℕ,
          8 * C * Real.rpow 2 (-(((k + 1 : ℕ) : ℝ) / τ)) :=
        Summable.tsum_le_tsum (fun k => hterm (k + 1) s)
          (htailsummable s).norm (htailgeom.1.mul_left (8 * C))
      _ = 8 * C *
          (∑' k : ℕ, Real.rpow 2 (-(((k + 1 : ℕ) : ℝ) / τ))) := by
        rw [tsum_mul_left]
      _ ≤ 14 * τ * C := by
        have := htailgeom.2
        nlinarith
  have ha0 (s : Fin n) : a 0 s = f s := by
    dsimp only [a]
    simp only [pow_zero]
    simp_rw [sub_smul, Finset.sum_sub_distrib]
    rw [hfzero]
    simp only [sub_zero]
    change (∑ x, (if s = x then 1 else 0) • f x) = f s
    simp
  have hwbound (s : Fin n) : ‖w s‖ ≤ 15 * τ * C := by
    have hsplit : a 0 s + (∑' k : ℕ, a (k + 1) s) = ∑' k : ℕ, a k s := by
      simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        Nat.zero_add] using (hsummable s).sum_add_tsum_nat_add 1
    dsimp only [w]
    rw [← hsplit]
    calc
      ‖a 0 s + ∑' k : ℕ, a (k + 1) s‖ ≤
          ‖a 0 s‖ + ‖∑' k : ℕ, a (k + 1) s‖ := norm_add_le _ _
      _ ≤ C + 14 * τ * C := add_le_add (by rw [ha0]; exact hf s) (htailbound s)
      _ ≤ 15 * τ * C := by nlinarith
  have hrow (i : Fin n) : ∑ j, (M.transition i j).toReal = 1 := by
    have hpenn : ∑ j, M.transition i j = 1 := by
      have hfin : HasSum (fun j : Fin n => M.transition i j)
          (∑ j, M.transition i j) := hasSum_fintype _
      exact ((PMF.hasSum_coe_one (M.transition i)).unique hfin).symm
    rw [← ENNReal.toReal_sum]
    · rw [hpenn]
      norm_num
    · exact fun j hj => (M.transition i).apply_ne_top j
  have hstep (k : ℕ) (i : Fin n) :
      ∑ j, (M.transition i j).toReal • a k j = a (k + 1) i := by
    change ∑ j, td_transition_matrix M i j • a k j = a (k + 1) i
    dsimp only [a]
    rw [pow_succ']
    simp only [Matrix.mul_apply]
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    have hinner :
        ∑ x, td_transition_matrix M i x *
            ((td_transition_matrix M ^ k) x l - (M.stationary l).toReal) =
          ∑ j, td_transition_matrix M i j *
              (td_transition_matrix M ^ k) j l -
            (M.stationary l).toReal := by
      change
        (∑ x, (M.transition i x).toReal *
          ((td_transition_matrix M ^ k) x l - (M.stationary l).toReal)) =
        ∑ j, (M.transition i j).toReal *
            (td_transition_matrix M ^ k) j l - (M.stationary l).toReal
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      rw [← Finset.sum_mul, hrow]
      ring
    simp_rw [smul_smul]
    rw [← Finset.sum_smul, hinner]
  have hshift (s : Fin n) :
      ∑ j, (M.transition s j).toReal • (∑' k : ℕ, a k j) =
        ∑' k : ℕ, a (k + 1) s := by
    calc
      ∑ j, (M.transition s j).toReal • (∑' k : ℕ, a k j) =
          ∑ j, ∑' k : ℕ, (M.transition s j).toReal • a k j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [(hsummable j).tsum_const_smul]
      _ = ∑' k : ℕ, ∑ j, (M.transition s j).toReal • a k j := by
        symm
        exact Summable.tsum_finsetSum
          (fun j hj => (hsummable j).const_smul ((M.transition s j).toReal))
      _ = ∑' k : ℕ, a (k + 1) s := by
        apply tsum_congr
        intro k
        exact hstep k s
  have hwpoisson (s : Fin n) :
      w s - ∑ j, (M.transition s j).toReal • w j = f s := by
    dsimp only [w]
    rw [hshift]
    have hsplit : a 0 s + (∑' k : ℕ, a (k + 1) s) = ∑' k : ℕ, a k s := by
      simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        Nat.zero_add] using (hsummable s).sum_add_tsum_nat_add 1
    rw [← hsplit, ha0]
    abel
  refine ⟨fun s => L.symm (w s), ?_, ?_⟩
  · intro s
    apply L.injective
    simp only [map_sub, map_sum, map_smul, L.apply_symm_apply]
    exact hwpoisson s
  · intro s
    rw [energy_td_euclidean_norm_bridge]
    change ‖L (L.symm (w s))‖ ≤ 15 * τ * C
    rw [L.apply_symm_apply]
    exact hwbound s

@[blueprint "lem:td-edge-poisson-solution"
  (statement := /-- Let $M$ be a finite TD model on the state space $\operatorname{Fin}(n)$, and let $\tau,C\in\mathbb R$.  Assume that $M$ satisfies the geometric-mixing estimate with constant $\tau$ and that $C\geq0$.  Let $h\colon\operatorname{Fin}(n)\times\operatorname{Fin}(n)\to\mathbb R^d$ satisfy
  \[
  \sum_s\pi(s)\sum_{s'}P(s,s')h(s,s')=0,
  \]
  and $\|h(s,s')\|_2\leq C$ for every ordered pair $(s,s')$.  Then there exists a function $u\colon\operatorname{Fin}(n)\times\operatorname{Fin}(n)\to\mathbb R^d$ such that, for every $s,s'\in\operatorname{Fin}(n)$,
  \[
  u(s,s')-\sum_jP(s',j)u(s',j)=h(s,s')
  \]
  and $\|u(s,s')\|_2\leq16\tau C$. -/)
  (proof := /-- Define $g(s)=\sum_jP(s,j)h(s,j)$.  The stationary-centering hypothesis gives $\sum_s\pi(s)g(s)=0$.  Since each transition row is a probability distribution, the triangle inequality transported through \cref{lem:energy-td-euclidean-norm-bridge} gives $\|g(s)\|_2\leq C$.  Apply \cref{lem:td-edge-vector-poisson} to obtain $v$ satisfying
  \[
  v(s)-\sum_jP(s,j)v(j)=g(s),\qquad
  \|v(s)\|_2\leq15\tau C.
  \]
  Set $u(s,s')=h(s,s')+v(s')$.  Expanding the transition average of $u$ and substituting the displayed state Poisson identity leaves exactly $h(s,s')$.  Finally, \cref{lem:energy-td-euclidean-norm-add}, the bounds on $h$ and $v$, and $\tau\geq1$ from \cref{def:td-geometric-mixing} give
  \[
  \|u(s,s')\|_2\leq C+15\tau C\leq16\tau C.
  \] -/)
  (title := /-- Quantitative Poisson solution on the transition-edge chain -/)
  (latexEnv := "lemma")]
lemma td_edge_poisson_solution {n d : ℕ} (M : td_model n d) (τ C : ℝ)
    (h : Fin n → Fin n → td_vector d)
    (hmix : td_geometric_mixing M τ) (hC : 0 ≤ C)
    (hcenter : (∑ s, (M.stationary s).toReal •
      (∑ s', (M.transition s s').toReal • h s s')) = 0)
    (hbound : ∀ s s', td_euclidean_norm (h s s') ≤ C) :
    ∃ u : Fin n → Fin n → td_vector d,
      (∀ s s', u s s' -
          ∑ j, (M.transition s' j).toReal • u s' j = h s s') ∧
      ∀ s s', td_euclidean_norm (u s s') ≤ 16 * τ * C := by
  classical
  let L : td_vector d ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  let g : Fin n → td_vector d := fun s =>
    ∑ j, (M.transition s j).toReal • h s j
  have hrow (s : Fin n) : ∑ j, (M.transition s j).toReal = 1 := by
    have hpenn : ∑ j, M.transition s j = 1 := by
      have hfin : HasSum (fun j : Fin n => M.transition s j)
          (∑ j, M.transition s j) := hasSum_fintype _
      exact ((PMF.hasSum_coe_one (M.transition s)).unique hfin).symm
    rw [← ENNReal.toReal_sum]
    · rw [hpenn]
      norm_num
    · exact fun j hj => (M.transition s).apply_ne_top j
  have hgcenter : ∑ s, (M.stationary s).toReal • g s = 0 := by
    simpa only [g] using hcenter
  have hgbound (s : Fin n) : td_euclidean_norm (g s) ≤ C := by
    rw [energy_td_euclidean_norm_bridge]
    change ‖L (g s)‖ ≤ C
    dsimp only [g]
    rw [map_sum]
    simp_rw [map_smul]
    calc
      ‖∑ j, (M.transition s j).toReal • L (h s j)‖ ≤
          ∑ j, ‖(M.transition s j).toReal • L (h s j)‖ := norm_sum_le _ _
      _ ≤ ∑ j, (M.transition s j).toReal * C := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg ENNReal.toReal_nonneg]
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        rw [← energy_td_euclidean_norm_bridge]
        exact hbound s j
      _ = C := by
        rw [← Finset.sum_mul, hrow]
        ring
  obtain ⟨v, hv, hvbound⟩ :=
    td_edge_vector_poisson M τ C g hmix hC hgcenter hgbound
  refine ⟨fun s s' => h s s' + v s', ?_, ?_⟩
  · intro s s'
    simp_rw [smul_add, Finset.sum_add_distrib]
    change h s s' + v s' -
      (g s' + ∑ j, (M.transition s' j).toReal • v j) = h s s'
    rw [← hv s']
    abel
  · intro s s'
    calc
      td_euclidean_norm (h s s' + v s') ≤
          td_euclidean_norm (h s s') + td_euclidean_norm (v s') :=
        energy_td_euclidean_norm_add _ _
      _ ≤ C + 15 * τ * C := add_le_add (hbound s s') (hvbound s')
      _ ≤ 16 * τ * C := by
        have hτ : 1 ≤ τ := hmix.1
        nlinarith

@[blueprint "lem:td-edge-poisson-solution-lipschitz"
  (statement := /-- Let $n,d\in\mathbb N$, let $M$ be a finite TD model on $\operatorname{Fin}(n)$ with transition matrix $P$, stationary distribution $\pi$, and geometric-mixing constant $\tau$, and fix $\theta^*\in\mathbb R^d$.  Let
  $h_\theta(s,s')\in\mathbb R^d$ be indexed by $\theta\in\mathbb R^d$ and
  $s,s'\in\operatorname{Fin}(n)$, and suppose that, for every $\theta$,
  \[
  \sum_s\pi(s)\sum_{s'}P(s,s')h_\theta(s,s')=0.
  \]
  If $C,L\geq0$ and, for all $\theta,\theta'\in\mathbb R^d$ and all
  $s,s'\in\operatorname{Fin}(n)$,
  \[
  \|h_\theta(s,s')\|_2\leq C\|\theta-\theta^*\|_2
  \quad\text{and}\quad
  \|h_\theta(s,s')-h_{\theta'}(s,s')\|_2
  \leq L\|\theta-\theta'\|_2
  \]
  then there exists a family
  $u_\theta(s,s')\in\mathbb R^d$, indexed by the same parameters and edges,
  such that, for all $\theta,s,s'$,
  \[
  u_\theta(s,s')-\sum_jP(s',j)u_\theta(s',j)=h_\theta(s,s'),
  \]
  and, for all $\theta,\theta'\in\mathbb R^d$ and
  $s,s'\in\operatorname{Fin}(n)$,
  \[
  \|u_\theta(s,s')\|_2\leq16\tau C\|\theta-\theta^*\|_2,
  \qquad
  \|u_\theta(s,s')-u_{\theta'}(s,s')\|_2
  \leq16\tau L\|\theta-\theta'\|_2.
  \] -/)
  (proof := /-- Let $E\colon\mathbb R^d\to\ell_2^d$ be the canonical continuous linear equivalence from \cref{lem:energy-td-euclidean-norm-bridge}.  For a state observable $q\colon\operatorname{Fin}(n)\to\mathbb R^d$, define
  \[
  a_k^q(s)=\sum_j\bigl((P^k)_{sj}-\pi(j)\bigr)E(q(j)),
  \qquad w_q(s)=\sum_{k=0}^{\infty}a_k^q(s),
  \]
  where $P$ is the matrix of \cref{def:td-transition-matrix}.  Suppose that
  $\sum_s\pi(s)q(s)=0$ and $\lVert q(s)\rVert_2\leq D$ for every $s$, with
  $D\geq0$.  The mixing estimate in \cref{def:td-geometric-mixing} and
  \cref{lem:energy-td-euclidean-norm-bridge} give
  \[
  \lVert a_k^q(s)\rVert_2\leq8D,2^{-k/\tau}.
  \]
  Hence \cref{lem:energy-geometric-envelope} proves summability.  Stationary
  centering gives $a_0^q(s)=E(q(s))$, while
  \cref{lem:td-edge-geometric-tail} bounds the norm of the remaining series by
  $14\tau D$.  Thus $\lVert w_q(s)\rVert_2\leq15\tau D$.  Every transition row
  has total mass one, and the identity $P^{k+1}=P P^k$ therefore yields
  \[
  \sum_jP(s,j)a_k^q(j)=a_{k+1}^q(s).
  \]
  Absolute summability permits interchange of the finite transition sum and
  the series, so telescoping proves
  $w_q(s)-\sum_jP(s,j)w_q(j)=E(q(s))$.

  For each parameter, set $g_\theta(s)=\sum_jP(s,j)h_\theta(s,j)$.  The assumed
  edge centering gives $\sum_s\pi(s)g_\theta(s)=0$.  The triangle inequality,
  the unit mass of each transition row, and
  \cref{lem:energy-td-euclidean-norm-bridge} show
  \[
  \lVert g_\theta(s)\rVert_2\leq
  C\lVert\theta-\theta^*\rVert_2,
  \quad
  \lVert g_\theta(s)-g_{\theta'}(s)\rVert_2\leq
  L\lVert\theta-\theta'\rVert_2.
  \]
  Apply the preceding construction to $g_\theta$ and to
  $g_\theta-g_{\theta'}$.  Termwise linearity, justified by the established
  summability, gives
  $w_{g_\theta}-w_{g_{\theta'}}=w_{g_\theta-g_{\theta'}}$.  Define
  $v_\theta(s)=E^{-1}(w_{g_\theta}(s))$ and
  $u_\theta(s,s')=h_\theta(s,s')+v_\theta(s')$.  The state Poisson identity
  for $v_\theta$ expands to the required edge identity.  Finally,
  \cref{lem:energy-td-euclidean-norm-add}, the bounds for $h$ and $v$, and
  $\tau\geq1$ from \cref{def:td-geometric-mixing} give respectively
  \[
  \lVert u_\theta(s,s')\rVert_2\leq16\tau C
  \lVert\theta-\theta^*\rVert_2,
  \qquad
  \lVert u_\theta(s,s')-u_{\theta'}(s,s')\rVert_2
  \leq16\tau L\lVert\theta-\theta'\rVert_2.
  \] -/)
  (title := /-- Lipschitz family of transition-edge Poisson solutions -/)
  (latexEnv := "lemma")]
lemma td_edge_poisson_solution_lipschitz {n d : ℕ} (M : td_model n d)
    (τ C L : ℝ) (θstar : td_vector d)
    (h : td_vector d → Fin n → Fin n → td_vector d)
    (hmix : td_geometric_mixing M τ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hcenter : ∀ θ, (∑ s, (M.stationary s).toReal •
      (∑ s', (M.transition s s').toReal • h θ s s')) = 0)
    (hbound : ∀ θ s s',
      td_euclidean_norm (h θ s s') ≤ C * td_euclidean_norm (θ - θstar))
    (hlip : ∀ θ θ' s s',
      td_euclidean_norm (h θ s s' - h θ' s s') ≤
        L * td_euclidean_norm (θ - θ')) :
    ∃ u : td_vector d → Fin n → Fin n → td_vector d,
      (∀ θ s s', u θ s s' -
          ∑ j, (M.transition s' j).toReal • u θ s' j = h θ s s') ∧
      (∀ θ s s', td_euclidean_norm (u θ s s') ≤
        16 * τ * C * td_euclidean_norm (θ - θstar)) ∧
      ∀ θ θ' s s', td_euclidean_norm (u θ s s' - u θ' s s') ≤
        16 * τ * L * td_euclidean_norm (θ - θ') := by
  classical
  let E : td_vector d ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  let a : (Fin n → td_vector d) → ℕ → Fin n → EuclideanSpace ℝ (Fin d) :=
    fun q k s => ∑ j, ((td_transition_matrix M ^ k) s j -
      (M.stationary j).toReal) • E (q j)
  let w : (Fin n → td_vector d) → Fin n → EuclideanSpace ℝ (Fin d) :=
    fun q s => ∑' k, a q k s
  have hτ : 1 ≤ τ := hmix.1
  have hrow (i : Fin n) : ∑ j, (M.transition i j).toReal = 1 := by
    have hpenn : ∑ j, M.transition i j = 1 := by
      have hfin : HasSum (fun j : Fin n => M.transition i j)
          (∑ j, M.transition i j) := hasSum_fintype _
      exact ((PMF.hasSum_coe_one (M.transition i)).unique hfin).symm
    rw [← ENNReal.toReal_sum]
    · rw [hpenn]
      norm_num
    · exact fun j hj => (M.transition i).apply_ne_top j
  have hstate (q : Fin n → td_vector d) (D : ℝ) (hD : 0 ≤ D)
      (hqcenter : ∑ s, (M.stationary s).toReal • q s = 0)
      (hqbound : ∀ s, td_euclidean_norm (q s) ≤ D) :
      (∀ s, Summable (fun k : ℕ => a q k s)) ∧
      (∀ s, w q s - ∑ j, (M.transition s j).toReal • w q j = E (q s)) ∧
      ∀ s, ‖w q s‖ ≤ 15 * τ * D := by
    have hfbound (s : Fin n) : ‖E (q s)‖ ≤ D := by
      rw [← energy_td_euclidean_norm_bridge]
      exact hqbound s
    have hfzero : ∑ s, (M.stationary s).toReal • E (q s) = 0 := by
      have hmap := congrArg E hqcenter
      simpa only [map_sum, map_smul, map_zero] using hmap
    have hterm (k : ℕ) (s : Fin n) :
        ‖a q k s‖ ≤ 8 * D * Real.rpow 2 (-((k : ℝ) / τ)) := by
      dsimp only [a]
      calc
        ‖∑ j, ((td_transition_matrix M ^ k) s j -
            (M.stationary j).toReal) • E (q j)‖ ≤
            ∑ j, ‖((td_transition_matrix M ^ k) s j -
              (M.stationary j).toReal) • E (q j)‖ := norm_sum_le _ _
        _ ≤ ∑ j, |(td_transition_matrix M ^ k) s j -
              (M.stationary j).toReal| * D := by
            apply Finset.sum_le_sum
            intro j hj
            rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (hfbound j) (abs_nonneg _)
        _ = D * ∑ j, |(td_transition_matrix M ^ k) s j -
              (M.stationary j).toReal| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
        _ ≤ D * (8 * Real.rpow 2 (-((k : ℝ) / τ))) :=
            mul_le_mul_of_nonneg_left (hmix.2 k s) hD
        _ = 8 * D * Real.rpow 2 (-((k : ℝ) / τ)) := by ring
    have hgeom := energy_geometric_envelope τ hτ
    have hsummable (s : Fin n) : Summable (fun k : ℕ => a q k s) := by
      apply Summable.of_norm_bounded (hgeom.1.mul_left (8 * D))
      intro k
      exact hterm k s
    have htailgeom := td_edge_geometric_tail τ hτ
    have htailsummable (s : Fin n) : Summable (fun k : ℕ => a q (k + 1) s) := by
      apply Summable.of_norm_bounded (htailgeom.1.mul_left (8 * D))
      intro k
      exact hterm (k + 1) s
    have htailbound (s : Fin n) :
        ‖∑' k : ℕ, a q (k + 1) s‖ ≤ 14 * τ * D := by
      calc
        ‖∑' k : ℕ, a q (k + 1) s‖ ≤ ∑' k : ℕ, ‖a q (k + 1) s‖ :=
          norm_tsum_le_tsum_norm (htailsummable s).norm
        _ ≤ ∑' k : ℕ,
            8 * D * Real.rpow 2 (-(((k + 1 : ℕ) : ℝ) / τ)) :=
          Summable.tsum_le_tsum (fun k => hterm (k + 1) s)
            (htailsummable s).norm (htailgeom.1.mul_left (8 * D))
        _ = 8 * D *
            (∑' k : ℕ, Real.rpow 2 (-(((k + 1 : ℕ) : ℝ) / τ))) := by
          rw [tsum_mul_left]
        _ ≤ 14 * τ * D := by
          have := htailgeom.2
          nlinarith
    have ha0 (s : Fin n) : a q 0 s = E (q s) := by
      dsimp only [a]
      simp only [pow_zero]
      simp_rw [sub_smul, Finset.sum_sub_distrib]
      rw [hfzero]
      simp only [sub_zero]
      change (∑ x, (if s = x then 1 else 0) • E (q x)) = E (q s)
      simp
    have hwbound (s : Fin n) : ‖w q s‖ ≤ 15 * τ * D := by
      have hsplit : a q 0 s + (∑' k : ℕ, a q (k + 1) s) =
          ∑' k : ℕ, a q k s := by
        simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
          Nat.zero_add] using (hsummable s).sum_add_tsum_nat_add 1
      dsimp only [w]
      rw [← hsplit]
      calc
        ‖a q 0 s + ∑' k : ℕ, a q (k + 1) s‖ ≤
            ‖a q 0 s‖ + ‖∑' k : ℕ, a q (k + 1) s‖ := norm_add_le _ _
        _ ≤ D + 14 * τ * D :=
          add_le_add (by rw [ha0]; exact hfbound s) (htailbound s)
        _ ≤ 15 * τ * D := by nlinarith
    have hstep (k : ℕ) (i : Fin n) :
        ∑ j, (M.transition i j).toReal • a q k j = a q (k + 1) i := by
      change ∑ j, td_transition_matrix M i j • a q k j = a q (k + 1) i
      dsimp only [a]
      rw [pow_succ']
      simp only [Matrix.mul_apply]
      simp_rw [Finset.smul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l hl
      have hinner :
          ∑ x, td_transition_matrix M i x *
              ((td_transition_matrix M ^ k) x l - (M.stationary l).toReal) =
            ∑ j, td_transition_matrix M i j *
                (td_transition_matrix M ^ k) j l -
              (M.stationary l).toReal := by
        change
          (∑ x, (M.transition i x).toReal *
            ((td_transition_matrix M ^ k) x l - (M.stationary l).toReal)) =
          ∑ j, (M.transition i j).toReal *
              (td_transition_matrix M ^ k) j l - (M.stationary l).toReal
        simp_rw [mul_sub, Finset.sum_sub_distrib]
        rw [← Finset.sum_mul, hrow]
        ring
      simp_rw [smul_smul]
      rw [← Finset.sum_smul, hinner]
    have hshift (s : Fin n) :
        ∑ j, (M.transition s j).toReal • w q j =
          ∑' k : ℕ, a q (k + 1) s := by
      calc
        ∑ j, (M.transition s j).toReal • w q j =
            ∑ j, ∑' k : ℕ, (M.transition s j).toReal • a q k j := by
          apply Finset.sum_congr rfl
          intro j hj
          dsimp only [w]
          rw [(hsummable j).tsum_const_smul]
        _ = ∑' k : ℕ, ∑ j, (M.transition s j).toReal • a q k j := by
          symm
          exact Summable.tsum_finsetSum
            (fun j hj => (hsummable j).const_smul ((M.transition s j).toReal))
        _ = ∑' k : ℕ, a q (k + 1) s := by
          apply tsum_congr
          intro k
          exact hstep k s
    have hwpoisson (s : Fin n) :
        w q s - ∑ j, (M.transition s j).toReal • w q j = E (q s) := by
      rw [hshift]
      have hsplit : a q 0 s + (∑' k : ℕ, a q (k + 1) s) =
          ∑' k : ℕ, a q k s := by
        simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
          Nat.zero_add] using (hsummable s).sum_add_tsum_nat_add 1
      dsimp only [w]
      rw [← hsplit, ha0]
      abel
    exact ⟨hsummable, hwpoisson, hwbound⟩
  let g : td_vector d → Fin n → td_vector d := fun θ s =>
    ∑ j, (M.transition s j).toReal • h θ s j
  have hgcenter (θ : td_vector d) :
      ∑ s, (M.stationary s).toReal • g θ s = 0 := by
    simpa only [g] using hcenter θ
  have hgbound (θ : td_vector d) (s : Fin n) :
      td_euclidean_norm (g θ s) ≤
        C * td_euclidean_norm (θ - θstar) := by
    rw [energy_td_euclidean_norm_bridge]
    change ‖E (g θ s)‖ ≤ C * td_euclidean_norm (θ - θstar)
    dsimp only [g]
    rw [map_sum]
    simp_rw [map_smul]
    calc
      ‖∑ j, (M.transition s j).toReal • E (h θ s j)‖ ≤
          ∑ j, ‖(M.transition s j).toReal • E (h θ s j)‖ := norm_sum_le _ _
      _ ≤ ∑ j, (M.transition s j).toReal *
          (C * td_euclidean_norm (θ - θstar)) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg ENNReal.toReal_nonneg]
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        rw [← energy_td_euclidean_norm_bridge]
        exact hbound θ s j
      _ = C * td_euclidean_norm (θ - θstar) := by
        rw [← Finset.sum_mul, hrow]
        ring
  have hgdiffcenter (θ θ' : td_vector d) :
      ∑ s, (M.stationary s).toReal • (g θ s - g θ' s) = 0 := by
    simp_rw [smul_sub, Finset.sum_sub_distrib]
    rw [hgcenter θ, hgcenter θ', sub_self]
  have hgdiffbound (θ θ' : td_vector d) (s : Fin n) :
      td_euclidean_norm (g θ s - g θ' s) ≤
        L * td_euclidean_norm (θ - θ') := by
    rw [energy_td_euclidean_norm_bridge]
    change ‖E (g θ s - g θ' s)‖ ≤ L * td_euclidean_norm (θ - θ')
    dsimp only [g]
    rw [map_sub, map_sum, map_sum, ← Finset.sum_sub_distrib]
    simp_rw [map_smul, ← smul_sub, ← map_sub]
    calc
      ‖∑ j, (M.transition s j).toReal • E (h θ s j - h θ' s j)‖ ≤
          ∑ j, ‖(M.transition s j).toReal • E (h θ s j - h θ' s j)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j, (M.transition s j).toReal *
          (L * td_euclidean_norm (θ - θ')) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg ENNReal.toReal_nonneg]
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        rw [← energy_td_euclidean_norm_bridge]
        exact hlip θ θ' s j
      _ = L * td_euclidean_norm (θ - θ') := by
        rw [← Finset.sum_mul, hrow]
        ring
  have hgdata (θ : td_vector d) := hstate (g θ)
    (C * td_euclidean_norm (θ - θstar))
    (mul_nonneg hC (Real.sqrt_nonneg _)) (hgcenter θ) (hgbound θ)
  have hgdiffdata (θ θ' : td_vector d) := hstate
    (fun s => g θ s - g θ' s) (L * td_euclidean_norm (θ - θ'))
    (mul_nonneg hL (Real.sqrt_nonneg _)) (hgdiffcenter θ θ') (hgdiffbound θ θ')
  have hwsub (θ θ' : td_vector d) (s : Fin n) :
      w (g θ) s - w (g θ') s = w (fun x => g θ x - g θ' x) s := by
    dsimp only [w]
    rw [← ((hgdata θ).1 s).tsum_sub ((hgdata θ').1 s)]
    apply tsum_congr
    intro k
    dsimp only [a]
    simp_rw [map_sub, smul_sub, Finset.sum_sub_distrib]
  let v : td_vector d → Fin n → td_vector d := fun θ s => E.symm (w (g θ) s)
  have hvpoisson (θ : td_vector d) (s : Fin n) :
      v θ s - ∑ j, (M.transition s j).toReal • v θ j = g θ s := by
    apply E.injective
    simp only [v, map_sub, map_sum, map_smul, E.apply_symm_apply]
    exact (hgdata θ).2.1 s
  have hvbound (θ : td_vector d) (s : Fin n) :
      td_euclidean_norm (v θ s) ≤
        15 * τ * C * td_euclidean_norm (θ - θstar) := by
    rw [energy_td_euclidean_norm_bridge]
    change ‖E (E.symm (w (g θ) s))‖ ≤ _
    rw [E.apply_symm_apply]
    simpa [mul_assoc] using (hgdata θ).2.2 s
  have hvdiffbound (θ θ' : td_vector d) (s : Fin n) :
      td_euclidean_norm (v θ s - v θ' s) ≤
        15 * τ * L * td_euclidean_norm (θ - θ') := by
    rw [energy_td_euclidean_norm_bridge]
    change ‖E (E.symm (w (g θ) s) - E.symm (w (g θ') s))‖ ≤ _
    rw [map_sub, E.apply_symm_apply, E.apply_symm_apply, hwsub]
    simpa [mul_assoc] using (hgdiffdata θ θ').2.2 s
  refine ⟨fun θ s s' => h θ s s' + v θ s', ?_, ?_, ?_⟩
  · intro θ s s'
    simp_rw [smul_add, Finset.sum_add_distrib]
    change h θ s s' + v θ s' -
      (g θ s' + ∑ j, (M.transition s' j).toReal • v θ j) = h θ s s'
    rw [← hvpoisson θ s']
    abel
  · intro θ s s'
    calc
      td_euclidean_norm (h θ s s' + v θ s') ≤
          td_euclidean_norm (h θ s s') + td_euclidean_norm (v θ s') :=
        energy_td_euclidean_norm_add _ _
      _ ≤ C * td_euclidean_norm (θ - θstar) +
          15 * τ * C * td_euclidean_norm (θ - θstar) :=
        add_le_add (hbound θ s s') (hvbound θ s')
      _ = (1 + 15 * τ) * (C * td_euclidean_norm (θ - θstar)) := by ring
      _ ≤ (16 * τ) * (C * td_euclidean_norm (θ - θstar)) :=
        mul_le_mul_of_nonneg_right (by linarith)
          (mul_nonneg hC (Real.sqrt_nonneg _))
      _ = 16 * τ * C * td_euclidean_norm (θ - θstar) := by ring
  · intro θ θ' s s'
    have heq :
        (h θ s s' + v θ s') - (h θ' s s' + v θ' s') =
          (h θ s s' - h θ' s s') + (v θ s' - v θ' s') := by abel
    rw [heq]
    calc
      td_euclidean_norm
          ((h θ s s' - h θ' s s') + (v θ s' - v θ' s')) ≤
          td_euclidean_norm (h θ s s' - h θ' s s') +
            td_euclidean_norm (v θ s' - v θ' s') :=
        energy_td_euclidean_norm_add _ _
      _ ≤ L * td_euclidean_norm (θ - θ') +
          15 * τ * L * td_euclidean_norm (θ - θ') :=
        add_le_add (hlip θ θ' s s') (hvdiffbound θ θ' s')
      _ = (1 + 15 * τ) * (L * td_euclidean_norm (θ - θ')) := by ring
      _ ≤ (16 * τ) * (L * td_euclidean_norm (θ - θ')) :=
        mul_le_mul_of_nonneg_right (by linarith)
          (mul_nonneg hL (Real.sqrt_nonneg _))
      _ = 16 * τ * L * td_euclidean_norm (θ - θ') := by ring

@[blueprint "lem:td-markov-anytime-vector"
  (statement := /-- Let $M$ be a finite-state TD model on $\operatorname{Fin}(n)$, fix an initial state $s_0$, and let $(S_t)_{t\geq0}$ have the canonical path law of $M$ started from $s_0$.  For every $t\in\mathbb N$, let $F_t(x,j)\in\mathbb R^d$ be indexed by a prefix $x=(x_i)_{0\leq i\leq t}$ and a state $j\in\operatorname{Fin}(n)$.  Let $(b_t)_{t\geq0}$ be nonnegative and satisfy $\sum_{t=0}^{\infty}b_t^2<\infty$.  Suppose that, for every $t$, every prefix $x$, and every state $j$,
  \[
  \sum_{k\in\operatorname{Fin}(n)}P(x_t,k)F_t(x,k)=0,
  \qquad \|F_t(x,j)\|_2\leq b_t,
  \]
  where $P$ is the transition matrix of $M$.  Then, for every $\varepsilon\in(0,1)$, with probability at least $1-\varepsilon$ one has, simultaneously for every $T\in\mathbb N$,
  \[
  \left\|\sum_{t<T}F_t((S_i)_{0\leq i\leq t},S_{t+1})\right\|_2
  \leq\sqrt{\sum_{t=0}^{\infty}b_t^2}\sqrt{2\log(2/\varepsilon)}.
  \] -/)
  (proof := /-- Use the coordinate filtration on the canonical trajectory measure from \cref{def:td-markov-path-measure}.  Since the state space is finite, each increment is measurable one step after its prefix.  Its Euclidean bound, together with the canonical continuous linear equivalence between $\mathbb R^d$ and Euclidean space and the bounded inverse of that equivalence, makes every increment integrable.  The conditional-distribution formula for the trajectory measure and the prefix kernel in \cref{def:td-prefix-kernel} identify the conditional law of $S_{t+1}$ given $(S_i)_{i\leq t}$ with $P(S_t,\cdot)$.  The centering hypothesis therefore shows that each conditional expected increment vanishes, so the adapted integrable partial sums form a martingale.  Apply \cref{lem:pinelis-anytime-td} with the bounds $b_t$ and confidence parameter $\varepsilon$; its conclusion is exactly the asserted simultaneous estimate. -/)
  (title := /-- Anytime vector martingale bound on the canonical Markov path -/)
  (latexEnv := "lemma")]
lemma td_markov_anytime_vector {n d : ℕ} (M : td_model n d) (s0 : Fin n)
    (F : (t : ℕ) → ((i : Finset.Iic t) → Fin n) → Fin n → td_vector d)
    (b : ℕ → ℝ) (ε : ℝ)
    (hcenter : ∀ t x, ∑ j, (M.transition
      (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩) j).toReal • F t x j = 0)
    (hbnonneg : ∀ t, 0 ≤ b t)
    (hbound : ∀ t x j, td_euclidean_norm (F t x j) ≤ b t)
    (hbsum : Summable (fun t => (b t) ^ 2))
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    (td_markov_path_measure M s0).real
      {path | ∀ T,
        td_euclidean_norm (∑ t ∈ Finset.range T,
          F t (Preorder.frestrictLe t path) (path (t + 1))) ≤
          Real.sqrt (∑' t, (b t) ^ 2) *
            Real.sqrt (2 * Real.log (2 / ε))} ≥ 1 - ε := by
  classical
  letI : Nonempty (Fin n) := ⟨s0⟩
  let μ := td_markov_path_measure M s0
  letI : MeasureTheory.IsProbabilityMeasure μ := by
    dsimp [μ, td_markov_path_measure]
    infer_instance
  let ℱ : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Fin n)) :=
    MeasureTheory.Filtration.piLE
  let X : ℕ → (ℕ → Fin n) → td_vector d := fun t path =>
    F t (Preorder.frestrictLe t path) (path (t + 1))
  let S : ℕ → (ℕ → Fin n) → td_vector d := fun T path =>
    ∑ t ∈ Finset.range T, X t path
  let L : td_vector d ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  let K : EuclideanSpace ℝ (Fin d) →L[ℝ] td_vector d := L.symm
  have hnorm (v : td_vector d) : td_euclidean_norm v = ‖L v‖ := by
    rw [td_euclidean_norm, EuclideanSpace.norm_eq]
    congr 1
    simp [L]
  have hXmeas (t : ℕ) :
      @Measurable (ℕ → Fin n) (td_vector d) (ℱ (t + 1)) inferInstance (X t) := by
    let G : ((i : Finset.Iic (t + 1)) → Fin n) → td_vector d := fun z =>
      F t (Preorder.frestrictLe₂ (π := fun _ : ℕ => Fin n) (Nat.le_succ t) z)
        (z ⟨t + 1, Finset.mem_Iic.mpr le_rfl⟩)
    rw [MeasureTheory.Filtration.piLE_eq_comap_frestrictLe]
    have hG : Measurable G := measurable_of_countable G
    have hc : @Measurable (ℕ → Fin n) ((i : Finset.Iic (t + 1)) → Fin n)
        (MeasurableSpace.comap (Preorder.frestrictLe (t + 1)) inferInstance)
        inferInstance (Preorder.frestrictLe (t + 1)) := comap_measurable _
    have hcomp := hG.comp hc
    change @Measurable (ℕ → Fin n) (td_vector d)
      (MeasurableSpace.comap (Preorder.frestrictLe (t + 1)) inferInstance)
      inferInstance (X t)
    have heq : X t = G ∘ Preorder.frestrictLe (t + 1) := by
      funext path
      dsimp [X, G, Function.comp_apply]
      congr 2
    rw [heq]
    exact hcomp
  have hadapt : MeasureTheory.StronglyAdapted ℱ S := by
    apply MeasureTheory.Adapted.stronglyAdapted
    intro T
    dsimp [S]
    apply Finset.measurable_sum
    intro t ht
    have hlt : t < T := Finset.mem_range.mp ht
    exact (hXmeas t).mono (ℱ.mono (Nat.succ_le_iff.mpr hlt)) le_rfl
  have hXint (t : ℕ) : MeasureTheory.Integrable (X t) μ := by
    have hm : Measurable (X t) := (hXmeas t).mono (ℱ.le' _) le_rfl
    apply MeasureTheory.Integrable.of_bound hm.aestronglyMeasurable (‖K‖ * b t)
    filter_upwards
    intro path
    calc
      ‖X t path‖ = ‖K (L (X t path))‖ := by simp [K]
      _ ≤ ‖K‖ * ‖L (X t path)‖ := K.le_opNorm _
      _ = ‖K‖ * td_euclidean_norm (X t path) := by rw [hnorm]
      _ ≤ ‖K‖ * b t := mul_le_mul_of_nonneg_left
        (hbound t (Preorder.frestrictLe t path) (path (t + 1))) (norm_nonneg _)
  have hSint (T : ℕ) : MeasureTheory.Integrable (S T) μ := by
    dsimp [S]
    exact MeasureTheory.integrable_finsetSum _ (fun t ht => hXint t)
  have hcond (t : ℕ) :
      MeasureTheory.condExp (m := ℱ t) μ (fun path => X t path) =ᵐ[μ] 0 := by
    let Pfx : (ℕ → Fin n) → ((i : Finset.Iic t) → Fin n) := Preorder.frestrictLe t
    let Nxt : (ℕ → Fin n) → Fin n := fun path => path (t + 1)
    let Q : (((i : Finset.Iic t) → Fin n) × Fin n) → td_vector d :=
      fun z => F t z.1 z.2
    have hPfx : Measurable Pfx := by
      simpa [Pfx] using Preorder.measurable_frestrictLe t
    have hNxt : Measurable Nxt := measurable_pi_apply _
    have hQ : MeasureTheory.StronglyMeasurable Q :=
      (measurable_of_countable Q).stronglyMeasurable
    have hQI : MeasureTheory.Integrable (fun path => Q (Pfx path, Nxt path)) μ := by
      simpa [Q, Pfx, Nxt, X] using hXint t
    have hce := ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib
      hPfx hNxt.aemeasurable hQ hQI
    have hk := ProbabilityTheory.Kernel.condDistrib_trajMeasure
      (X := fun _ : ℕ => Fin n) (μ₀ := MeasureTheory.Measure.dirac s0)
      (κ := fun t => td_prefix_kernel M t)
      (a := t)
    have hkp := (hPfx.quasiMeasurePreserving μ).ae_eq_comp hk
    rw [MeasureTheory.Filtration.piLE_eq_comap_frestrictLe]
    refine hce.trans ?_
    filter_upwards [hkp] with path hpath
    change (∫ j, F t (Pfx path) j
      ∂ProbabilityTheory.condDistrib Nxt Pfx μ (Pfx path)) = 0
    dsimp [Nxt, Pfx, μ, td_markov_path_measure] at hpath ⊢
    rw [hpath]
    change (∫ j, F t (Pfx path) j
      ∂(M.transition ((Pfx path) ⟨t, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure) = 0
    rw [MeasureTheory.integral_fintype]
    · simp_rw [MeasureTheory.measureReal_def,
        PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
      exact hcenter t (Pfx path)
    · exact MeasureTheory.Integrable.of_finite
  have hmart : MeasureTheory.Martingale S ℱ μ := by
    apply MeasureTheory.martingale_of_condExp_sub_eq_zero_nat hadapt hSint
    intro t
    have hinc : S (t + 1) - S t = X t := by
      funext path i
      simp [S, Finset.sum_range_succ]
    rw [hinc]
    exact hcond t
  have hp := pinelis_anytime_td μ ℱ X b ε hmart hbnonneg ?_ hbsum hε0 hε1
  · simpa [μ, X] using hp
  · intro t
    filter_upwards
    intro path
    exact hbound t (Preorder.frestrictLe t path) (path (t + 1))

@[blueprint "lem:i-two-fixed-point-noise-poisson"
  (statement := /-- Let $M$ be a finite-state TD model satisfying the uniform bounds with constants $\phi_\infty,r_\infty$ and the geometric-mixing estimate with constant $\tau$, and let $\theta^*$ be a TD fixed point.  Put
  \[
  C=r_\infty\phi_\infty+2\phi_\infty^2\lVert\theta^*\rVert_2.
  \]
  Then there exists $u\colon\operatorname{Fin}(n)^2\to\mathbb R^d$ such that
  \[
  u(s,s')-\sum_jP(s',j)u(s',j)=g(\theta^*,(s,s'))
  \]
  and $\lVert u(s,s')\rVert_2\leq16\tau C$ for every $s,s'$. -/)
  (proof := /-- The stationary transition average of the fixed-point update is zero by \cref{lem:energy-mean-update-average} and the fixed-point identity.  The reward part has norm at most $r_\infty\phi_\infty$.  The sample-matrix part has norm at most $2\phi_\infty^2\lVert\theta^*\rVert_2$ by \cref{lem:energy-td-dot-product-bound,lem:energy-td-euclidean-norm-smul}; hence \cref{lem:energy-td-euclidean-norm-sub} gives the bound $C$.  Applying \cref{lem:td-edge-poisson-solution} to this centered observable yields the asserted function and estimate. -/)
  (title := /-- Poisson solution for the fixed-point transition noise -/)
  (latexEnv := "lemma")]
lemma i_two_fixed_point_noise_poisson {n d : ℕ} (M : td_model n d)
    (τ φinf rinf : ℝ) (θstar : td_vector d)
    (hbounds : td_uniform_bounds M φinf rinf)
    (hmix : td_geometric_mixing M τ) (hfixed : td_fixed_point M θstar) :
    ∃ u : Fin n → Fin n → td_vector d,
      (∀ s s', u s s' -
          ∑ j, (M.transition s' j).toReal • u s' j = td_update M θstar s s') ∧
      ∀ s s', td_euclidean_norm (u s s') ≤
        16 * τ * (rinf * φinf + 2 * φinf ^ 2 * td_euclidean_norm θstar) := by
  classical
  let C := rinf * φinf + 2 * φinf ^ 2 * td_euclidean_norm θstar
  have hφpos : 0 < φinf := hbounds.1
  have hrnonneg : 0 ≤ rinf := hbounds.2.1
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (mul_nonneg hrnonneg hφpos.le)
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg φinf))
        (Real.sqrt_nonneg _))
  have hcenter :
      (∑ s, (M.stationary s).toReal •
        ∑ s', (M.transition s s').toReal • td_update M θstar s s') = 0 := by
    rw [← energy_mean_update_average, td_mean_update, hfixed, sub_self]
  have hbound (s s' : Fin n) : td_euclidean_norm (td_update M θstar s s') ≤ C := by
    have hφs := hbounds.2.2.1 s
    have hφs' := hbounds.2.2.1 s'
    have hr := hbounds.2.2.2 s s'
    have hγabs : |M.discount| ≤ 1 := by
      rw [abs_of_nonneg M.discount_nonneg]
      exact M.discount_lt_one.le
    have hdiff :
        td_euclidean_norm (M.feature s - M.discount • M.feature s') ≤ 2 * φinf := by
      calc
        td_euclidean_norm (M.feature s - M.discount • M.feature s') ≤
            td_euclidean_norm (M.feature s) +
              td_euclidean_norm (M.discount • M.feature s') :=
          energy_td_euclidean_norm_sub _ _
        _ = td_euclidean_norm (M.feature s) +
            |M.discount| * td_euclidean_norm (M.feature s') := by
              rw [energy_td_euclidean_norm_smul]
        _ ≤ φinf + 1 * φinf := by
          have hm := mul_le_mul hγabs hφs' (Real.sqrt_nonneg _) (by norm_num)
          nlinarith
        _ = 2 * φinf := by ring
    have hmat : Matrix.mulVec (td_sample_matrix M s s') θstar =
        ((M.feature s - M.discount • M.feature s') ⬝ᵥ θstar) • M.feature s := by
      ext i
      simp only [td_sample_matrix, Matrix.mulVec, dotProduct, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have hmatnorm :
        td_euclidean_norm (Matrix.mulVec (td_sample_matrix M s s') θstar) ≤
          2 * φinf ^ 2 * td_euclidean_norm θstar := by
      rw [hmat, energy_td_euclidean_norm_smul]
      have hdot := energy_td_dot_product_bound
        (M.feature s - M.discount • M.feature s') θstar
      have habsdot :
          |(M.feature s - M.discount • M.feature s') ⬝ᵥ θstar| ≤
            2 * φinf * td_euclidean_norm θstar :=
        hdot.trans (mul_le_mul hdiff le_rfl (Real.sqrt_nonneg _) (by positivity))
      have hp := mul_le_mul habsdot hφs (Real.sqrt_nonneg _)
        (mul_nonneg (mul_nonneg (by positivity) hφpos.le) (Real.sqrt_nonneg _))
      nlinarith
    have hbvec : td_euclidean_norm (td_sample_vector M s s') ≤ rinf * φinf := by
      rw [td_sample_vector, energy_td_euclidean_norm_smul]
      exact mul_le_mul hr hφs (Real.sqrt_nonneg _) hrnonneg
    rw [td_update]
    exact (energy_td_euclidean_norm_sub _ _).trans (by
      dsimp [C]
      linarith)
  simpa only [C] using
    td_edge_poisson_solution M τ C (td_update M θstar) hmix hC hcenter hbound

@[blueprint "lem:i-two-weighted-coboundary-bound"
  (statement := /-- Let $(\eta_t)_{t\geq0}$ be a positive non-increasing sequence and let $(q_t)_{t\geq0}$ be a sequence in $\mathbb R^d$ satisfying $\lVert q_t\rVert_2\leq U$, where $U\geq0$.  Then, for every $T\in\mathbb N$,
  \[
  \left\lVert\sum_{t<T}\eta_t(q_t-q_{t+1})\right\rVert_2
  \leq3\eta_0U.
  \] -/)
  (proof := /-- Abel summation writes the displayed sum as
  \[
  \eta_0q_0-\eta_Tq_T-
  \sum_{t<T}(\eta_t-\eta_{t+1})q_{t+1}.
  \]
  By antitonicity, all coefficients in the last sum are nonnegative and their sum is $\eta_0-\eta_T$.  The endpoint terms have norm at most $(\eta_0+\eta_T)U$, while the variation term has norm at most $(\eta_0-\eta_T)U$.  The triangle inequality from \cref{lem:energy-td-euclidean-norm-sub}, together with the homogeneity identity \cref{lem:energy-td-euclidean-norm-smul} and the canonical norm realization \cref{lem:energy-td-euclidean-norm-bridge}, gives the stated bound. -/)
  (title := /-- Vector Abel bound for a weighted coboundary -/)
  (latexEnv := "lemma")]
lemma i_two_weighted_coboundary_bound {d : ℕ} (η : ℕ → ℝ)
    (q : ℕ → td_vector d) (U : ℝ) (T : ℕ)
    (hηpos : ∀ t, 0 < η t) (hηanti : Antitone η) (hU : 0 ≤ U)
    (hq : ∀ t, td_euclidean_norm (q t) ≤ U) :
    td_euclidean_norm (∑ t ∈ Finset.range T, η t • (q t - q (t + 1))) ≤
      3 * η 0 * U := by
  have hηnonneg (t : ℕ) : 0 ≤ η t := (hηpos t).le
  have hdiff (t : ℕ) : 0 ≤ η t - η (t + 1) :=
    sub_nonneg.mpr (hηanti (Nat.le_succ t))
  have habel :
      (∑ t ∈ Finset.range T, η t • (q t - q (t + 1))) =
        η 0 • q 0 - η T • q T -
          ∑ t ∈ Finset.range T, (η t - η (t + 1)) • q (t + 1) := by
    induction T with
    | zero => simp
    | succ T ih =>
        rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
        ext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
  have hvariation :
      td_euclidean_norm
          (∑ t ∈ Finset.range T, (η t - η (t + 1)) • q (t + 1)) ≤
        η 0 * U := by
    let L : td_vector d ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
    calc
      td_euclidean_norm
          (∑ t ∈ Finset.range T, (η t - η (t + 1)) • q (t + 1)) =
          ‖L (∑ t ∈ Finset.range T,
            (η t - η (t + 1)) • q (t + 1))‖ :=
        energy_td_euclidean_norm_bridge _
      _ ≤ ∑ t ∈ Finset.range T,
          ‖L ((η t - η (t + 1)) • q (t + 1))‖ := by
        rw [map_sum]
        exact norm_sum_le _ _
      _ ≤ ∑ t ∈ Finset.range T, (η t - η (t + 1)) * U := by
        apply Finset.sum_le_sum
        intro t ht
        rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hdiff t)]
        apply mul_le_mul_of_nonneg_left _ (hdiff t)
        rw [← energy_td_euclidean_norm_bridge]
        exact hq (t + 1)
      _ = (η 0 - η T) * U := by
        rw [← Finset.sum_mul, Finset.sum_range_sub']
      _ ≤ η 0 * U :=
        mul_le_mul_of_nonneg_right (sub_le_self (η 0) (hηnonneg T)) hU
  have hendpoint :
      td_euclidean_norm (η 0 • q 0 - η T • q T) ≤ 2 * η 0 * U := by
    calc
      td_euclidean_norm (η 0 • q 0 - η T • q T) ≤
          td_euclidean_norm (η 0 • q 0) + td_euclidean_norm (η T • q T) :=
        energy_td_euclidean_norm_sub _ _
      _ = η 0 * td_euclidean_norm (q 0) + η T * td_euclidean_norm (q T) := by
        rw [energy_td_euclidean_norm_smul, energy_td_euclidean_norm_smul,
          abs_of_pos (hηpos 0), abs_of_pos (hηpos T)]
      _ ≤ η 0 * U + η T * U :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hq 0) (hηnonneg 0))
          (mul_le_mul_of_nonneg_left (hq T) (hηnonneg T))
      _ ≤ 2 * η 0 * U := by
        have hT : η T ≤ η 0 := hηanti (Nat.zero_le T)
        have hm := mul_le_mul_of_nonneg_right hT hU
        linarith
  rw [habel]
  exact (energy_td_euclidean_norm_sub _ _).trans (by linarith)

@[blueprint "lem:i-two-poisson-martingale-control"
  (statement := /-- Let $n,d\in\mathbb N$, let $M$ be a finite-state TD model on $\operatorname{Fin}(n)$ with parameter space $\mathbb R^d$, let $\eta\colon\mathbb N\to\mathbb R$, and fix $\delta,\tau,\phi_\infty,r_\infty\in\mathbb R$, a vector $\theta^*\in\mathbb R^d$, and an initial state $s_0\in\operatorname{Fin}(n)$.  Assume that $\eta_t>0$ for every $t$, that $\eta$ is non-increasing, and that $\sum_{t=0}^{\infty}\eta_t^2<\infty$; assume also that $0<\delta<1$, that $M$ satisfies the uniform feature and reward bounds with constants $\phi_\infty,r_\infty$ and the geometric-mixing bound with constant $\tau$, and that $\theta^*$ is a TD fixed point.  Then the canonical Markov path law of $M$ started from $s_0$ assigns probability at least $1-\delta/4$ to the simultaneous fixed-point-noise event $\mathcal E_2$ of \cref{def:i-two-control-event}. -/)
  (proof := /-- Put
  \[
  C=r_\infty\phi_\infty+2\phi_\infty^2\lVert\theta^*\rVert_2.
  \]
  By \cref{lem:i-two-fixed-point-noise-poisson}, there is a function $u$ satisfying
  \[
  u(s,s')-\sum_jP(s',j)u(s',j)=g(\theta^*,(s,s')),
  \qquad \lVert u(s,s')\rVert_2\leq16\tau C.
  \]
  Set $q(s)=\sum_jP(s,j)u(s,j)$.  The transition weights are nonnegative and sum to one, so the canonical norm realization in \cref{lem:energy-td-euclidean-norm-bridge} gives $\lVert q(s)\rVert_2\leq16\tau C$.

  For a path prefix $x=(x_0,\ldots,x_t)$ and a state $j$, define
  \[
  F_t(x,j)=\eta_t\bigl(u(x_t,j)-q(x_t)\bigr),
  \qquad b_t=32\tau C\eta_t.
  \]
  Every transition-weighted mean of $F_t$ is zero.  The difference triangle inequality and homogeneity from \cref{lem:energy-td-euclidean-norm-sub,lem:energy-td-euclidean-norm-smul} give $\lVert F_t(x,j)\rVert_2\leq b_t$, and square-summability of $\eta$ gives square-summability of $b$.  Applying \cref{lem:td-markov-anytime-vector} with confidence parameter $\delta/4$ therefore produces an event of probability at least $1-\delta/4$ on which, simultaneously for every $T$,
  \[
  \left\lVert\sum_{t<T}\eta_t
  \bigl(u(S_t,S_{t+1})-q(S_t)\bigr)\right\rVert_2
  \leq32\tau C\sqrt{H}\sqrt{2\log(8/\delta)},
  \qquad H=\sum_{t=0}^{\infty}\eta_t^2.
  \]

  By \cref{lem:i-two-weighted-coboundary-bound},
  \[
  \left\lVert\sum_{t<T}\eta_t\bigl(q(S_t)-q(S_{t+1})\bigr)\right\rVert_2
  \leq48\tau C\eta_0.
  \]
  The Poisson identity expresses the unnormalized numerator in \cref{def:td-i-two} as the sum of these martingale and coboundary terms.  The triangle inequality \cref{lem:energy-td-euclidean-norm-add} bounds its norm by
  \[
  16\tau C\left(2\sqrt H\sqrt{2\log(8/\delta)}+3\eta_0\right).
  \]
  For every $T\geq1$, positivity of the stepsizes makes the mass in \cref{def:pr-step-mass} positive.  Dividing the preceding estimate by this mass and using the homogeneity identity from \cref{lem:energy-td-euclidean-norm-smul}, together with \cref{def:pr-square-mass}, gives exactly the simultaneous inequalities defining the event in \cref{def:i-two-control-event}.  This martingale event is therefore contained in $\mathcal E_2$, and monotonicity of the canonical path measure proves the claimed probability bound. -/)
  (title := /-- Poisson and martingale control of the fixed-point noise -/)
  (latexEnv := "lemma")]
lemma i_two_poisson_martingale_control {n d : ℕ} (M : td_model n d)
    (η : ℕ → ℝ) (δ τ φinf rinf : ℝ) (θstar : td_vector d) (s0 : Fin n)
    (hηpos : ∀ t, 0 < η t) (hηanti : Antitone η)
    (hηsum : Summable (fun t => (η t) ^ 2))
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hbounds : td_uniform_bounds M φinf rinf)
    (hmix : td_geometric_mixing M τ) (hfixed : td_fixed_point M θstar) :
    (td_markov_path_measure M s0).real
        (i_two_control_event M η δ τ φinf rinf θstar) ≥ 1 - δ / 4 := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure (td_markov_path_measure M s0) := by
    dsimp [td_markov_path_measure]
    infer_instance
  let C := rinf * φinf + 2 * φinf ^ 2 * td_euclidean_norm θstar
  have hτ : 0 ≤ τ := hmix.1.trans' (by norm_num)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (mul_nonneg hbounds.2.1 hbounds.1.le)
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg φinf))
        (Real.sqrt_nonneg _))
  obtain ⟨u, hupoisson, hubound⟩ :=
    i_two_fixed_point_noise_poisson M τ φinf rinf θstar hbounds hmix hfixed
  have hrow (s : Fin n) : ∑ j, (M.transition s j).toReal = 1 := by
    have hpenn : ∑ j, M.transition s j = 1 := by
      have hfin : HasSum (fun j : Fin n => M.transition s j)
          (∑ j, M.transition s j) := hasSum_fintype _
      exact ((PMF.hasSum_coe_one (M.transition s)).unique hfin).symm
    rw [← ENNReal.toReal_sum]
    · rw [hpenn]
      norm_num
    · exact fun j hj => (M.transition s).apply_ne_top j
  let q : Fin n → td_vector d := fun s =>
    ∑ j, (M.transition s j).toReal • u s j
  have hqbound (s : Fin n) :
      td_euclidean_norm (q s) ≤ 16 * τ * C := by
    let L : td_vector d ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
    calc
      td_euclidean_norm (q s) = ‖L (q s)‖ :=
        energy_td_euclidean_norm_bridge _
      _ ≤ ∑ j, ‖L ((M.transition s j).toReal • u s j)‖ := by
        dsimp [q]
        rw [map_sum]
        exact norm_sum_le _ _
      _ ≤ ∑ j, (M.transition s j).toReal * (16 * τ * C) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [map_smul, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg ENNReal.toReal_nonneg]
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        rw [← energy_td_euclidean_norm_bridge]
        simpa only [C] using hubound s j
      _ = 16 * τ * C := by
        rw [← Finset.sum_mul, hrow]
        ring
  let F : (t : ℕ) → ((i : Finset.Iic t) → Fin n) → Fin n → td_vector d :=
    fun t x j => η t •
      (u (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩) j -
        q (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩))
  let b : ℕ → ℝ := fun t => 32 * τ * C * η t
  have hFcenter : ∀ t x, ∑ j, (M.transition
      (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩) j).toReal • F t x j = 0 := by
    intro t x
    let s := x ⟨t, Finset.mem_Iic.mpr le_rfl⟩
    change ∑ j, (M.transition s j).toReal •
      (η t • (u s j - q s)) = 0
    calc
      (∑ j, (M.transition s j).toReal • (η t • (u s j - q s))) =
          η t • ∑ j, (M.transition s j).toReal • (u s j - q s) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [smul_smul]
        rw [mul_comm]
      _ = η t • ((∑ j, (M.transition s j).toReal • u s j) -
          ∑ j, (M.transition s j).toReal • q s) := by
        simp_rw [smul_sub]
        rw [Finset.sum_sub_distrib]
        rw [smul_sub]
      _ = η t • (q s - (∑ j, (M.transition s j).toReal) • q s) := by
        rw [← Finset.sum_smul]
      _ = 0 := by rw [hrow]; simp
  have hbnonneg : ∀ t, 0 ≤ b t := by
    intro t
    dsimp [b]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hτ) hC)
      (hηpos t).le
  have hFbound : ∀ t x j, td_euclidean_norm (F t x j) ≤ b t := by
    intro t x j
    let s := x ⟨t, Finset.mem_Iic.mpr le_rfl⟩
    change td_euclidean_norm (η t • (u s j - q s)) ≤ b t
    rw [energy_td_euclidean_norm_smul, abs_of_pos (hηpos t)]
    have hdiff := energy_td_euclidean_norm_sub (u s j) (q s)
    have hsum : td_euclidean_norm (u s j) + td_euclidean_norm (q s) ≤
        16 * τ * C + 16 * τ * C :=
      add_le_add (by simpa only [C] using hubound s j) (hqbound s)
    have hm := mul_le_mul_of_nonneg_left (hdiff.trans hsum) (hηpos t).le
    dsimp [b]
    nlinarith
  have hbsum : Summable (fun t => (b t) ^ 2) := by
    have hs := hηsum.mul_left ((32 * τ * C) ^ 2)
    apply hs.congr
    intro t
    dsimp [b]
    ring
  have hε0 : 0 < δ / 4 := by positivity
  have hε1 : δ / 4 < 1 := by linarith
  let E : Set (ℕ → Fin n) :=
    {path | ∀ T,
      td_euclidean_norm (∑ t ∈ Finset.range T,
        F t (Preorder.frestrictLe t path) (path (t + 1))) ≤
        Real.sqrt (∑' t, (b t) ^ 2) *
          Real.sqrt (2 * Real.log (2 / (δ / 4)))}
  have hprob : (td_markov_path_measure M s0).real E ≥ 1 - δ / 4 := by
    exact td_markov_anytime_vector M s0 F b (δ / 4) hFcenter hbnonneg
      hFbound hbsum hε0 hε1
  have hbmass :
      Real.sqrt (∑' t, (b t) ^ 2) =
        32 * τ * C * Real.sqrt (pr_square_mass η) := by
    have htsum :
        (∑' t, (b t) ^ 2) = (32 * τ * C) ^ 2 * pr_square_mass η := by
      rw [pr_square_mass, ← tsum_mul_left]
      apply tsum_congr
      intro t
      dsimp [b]
      ring
    rw [htsum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
      abs_of_nonneg]
    positivity
  have hlog : 2 / (δ / 4) = 8 / δ := by
    field_simp [ne_of_gt hδ0]
    norm_num
  have hsubset : E ⊆ i_two_control_event M η δ τ φinf rinf θstar := by
    intro path hpath
    intro T hT
    have hSpos : 0 < pr_step_mass η T := by
      unfold pr_step_mass
      apply Finset.sum_pos
      · intro i hi
        exact hηpos i
      · exact Finset.nonempty_range_iff.mpr (by omega)
    have hmart :
        td_euclidean_norm (∑ t ∈ Finset.range T,
          η t • (u (path t) (path (t + 1)) - q (path t))) ≤
          32 * τ * C * Real.sqrt (pr_square_mass η) *
            Real.sqrt (2 * Real.log (8 / δ)) := by
      have hp := hpath T
      rw [hbmass, hlog] at hp
      simpa [F, Preorder.frestrictLe_apply] using hp
    let qp : ℕ → td_vector d := fun t => q (path t)
    have hcob :
        td_euclidean_norm (∑ t ∈ Finset.range T,
          η t • (q (path t) - q (path (t + 1)))) ≤
          3 * η 0 * (16 * τ * C) := by
      simpa only [qp] using i_two_weighted_coboundary_bound η qp
        (16 * τ * C) T hηpos hηanti (by positivity)
        (fun t => hqbound (path t))
    have hrawid :
        (∑ t ∈ Finset.range T, η t •
          td_update M θstar (path t) (path (t + 1))) =
          (∑ t ∈ Finset.range T,
            η t • (u (path t) (path (t + 1)) - q (path t))) +
          ∑ t ∈ Finset.range T,
            η t • (q (path t) - q (path (t + 1))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      dsimp [q]
      rw [← hupoisson (path t) (path (t + 1))]
      module
    have hraw :
        td_euclidean_norm (∑ t ∈ Finset.range T, η t •
          td_update M θstar (path t) (path (t + 1))) ≤
          16 * τ * C *
            (2 * Real.sqrt (pr_square_mass η) *
              Real.sqrt (2 * Real.log (8 / δ)) + 3 * η 0) := by
      rw [hrawid]
      exact (energy_td_euclidean_norm_add _ _).trans (by
        have hs := add_le_add hmart hcob
        nlinarith)
    rw [td_i_two, energy_td_euclidean_norm_smul,
      abs_of_pos (inv_pos.mpr hSpos)]
    calc
      (pr_step_mass η T)⁻¹ *
          td_euclidean_norm (∑ t ∈ Finset.range T, η t •
            (td_sample_vector M (path t) (path (t + 1)) -
              Matrix.mulVec (td_sample_matrix M (path t) (path (t + 1))) θstar)) ≤
          (pr_step_mass η T)⁻¹ *
            (16 * τ * C *
              (2 * Real.sqrt (pr_square_mass η) *
                Real.sqrt (2 * Real.log (8 / δ)) + 3 * η 0)) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hSpos.le)
        simpa only [td_update] using hraw
      _ = 2 / pr_step_mass η T *
          (2 * Real.sqrt (pr_square_mass η) * Real.sqrt (2 * Real.log (8 / δ)) +
            3 * η 0) * 8 * τ *
          (rinf * φinf + 2 * φinf ^ 2 * td_euclidean_norm θstar) := by
        dsimp [C]
        rw [div_eq_mul_inv]
        ring
  calc
    1 - δ / 4 ≤ (td_markov_path_measure M s0).real E := hprob
    _ ≤ (td_markov_path_measure M s0).real
        (i_two_control_event M η δ τ φinf rinf θstar) :=
      MeasureTheory.measureReal_mono hsubset (MeasureTheory.measure_ne_top _ _)

@[blueprint "lem:i-three-nonnegative-weighted-coboundary-bound"
  (statement := /-- Let $(\alpha_t)_{t\geq0}$ be a nonnegative non-increasing sequence, let $(q_t)_{t\geq0}$ be a sequence in $\mathbb R^d$, and let $U\geq0$.  If $\lVert q_t\rVert_2\leq U$ for every $t$, then, for every $T\in\mathbb N$,
  \[
  \left\lVert\sum_{t<T}\alpha_t(q_t-q_{t+1})\right\rVert_2
  \leq3\alpha_0U.
  \] -/)
  (proof := /-- Abel summation writes the weighted coboundary as the difference of the two endpoint terms and the sum with coefficients $\alpha_t-\alpha_{t+1}$.  Nonnegativity and monotonicity make these coefficients nonnegative and bound their total mass by $\alpha_0$.  The triangle inequality and homogeneity identities from \cref{lem:energy-td-euclidean-norm-sub,lem:energy-td-euclidean-norm-smul}, together with the canonical norm realization in \cref{lem:energy-td-euclidean-norm-bridge}, bound the two endpoints by $2\alpha_0U$ and the variation term by $\alpha_0U$. -/)
  (title := /-- Nonnegative vector Abel bound for a weighted coboundary -/)
  (latexEnv := "lemma")]
lemma i_three_nonnegative_weighted_coboundary_bound {d : ℕ} (α : ℕ → ℝ)
    (q : ℕ → td_vector d) (U : ℝ) (T : ℕ)
    (hαnonneg : ∀ t, 0 ≤ α t) (hαanti : Antitone α) (hU : 0 ≤ U)
    (hq : ∀ t, td_euclidean_norm (q t) ≤ U) :
    td_euclidean_norm (∑ t ∈ Finset.range T, α t • (q t - q (t + 1))) ≤
      3 * α 0 * U := by
  have hdiff (t : ℕ) : 0 ≤ α t - α (t + 1) :=
    sub_nonneg.mpr (hαanti (Nat.le_succ t))
  have habel :
      (∑ t ∈ Finset.range T, α t • (q t - q (t + 1))) =
        α 0 • q 0 - α T • q T -
          ∑ t ∈ Finset.range T, (α t - α (t + 1)) • q (t + 1) := by
    induction T with
    | zero => simp
    | succ T ih =>
        rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
        ext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
  have hvariation :
      td_euclidean_norm
          (∑ t ∈ Finset.range T, (α t - α (t + 1)) • q (t + 1)) ≤
        α 0 * U := by
    let L : td_vector d ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
    calc
      td_euclidean_norm
          (∑ t ∈ Finset.range T, (α t - α (t + 1)) • q (t + 1)) =
          ‖L (∑ t ∈ Finset.range T,
            (α t - α (t + 1)) • q (t + 1))‖ :=
        energy_td_euclidean_norm_bridge _
      _ ≤ ∑ t ∈ Finset.range T,
          ‖L ((α t - α (t + 1)) • q (t + 1))‖ := by
        rw [map_sum]
        exact norm_sum_le _ _
      _ ≤ ∑ t ∈ Finset.range T, (α t - α (t + 1)) * U := by
        apply Finset.sum_le_sum
        intro t ht
        rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hdiff t)]
        apply mul_le_mul_of_nonneg_left _ (hdiff t)
        rw [← energy_td_euclidean_norm_bridge]
        exact hq (t + 1)
      _ = (α 0 - α T) * U := by
        rw [← Finset.sum_mul, Finset.sum_range_sub']
      _ ≤ α 0 * U :=
        mul_le_mul_of_nonneg_right (sub_le_self (α 0) (hαnonneg T)) hU
  have hendpoint :
      td_euclidean_norm (α 0 • q 0 - α T • q T) ≤ 2 * α 0 * U := by
    calc
      td_euclidean_norm (α 0 • q 0 - α T • q T) ≤
          td_euclidean_norm (α 0 • q 0) + td_euclidean_norm (α T • q T) :=
        energy_td_euclidean_norm_sub _ _
      _ = α 0 * td_euclidean_norm (q 0) + α T * td_euclidean_norm (q T) := by
        rw [energy_td_euclidean_norm_smul, energy_td_euclidean_norm_smul,
          abs_of_nonneg (hαnonneg 0), abs_of_nonneg (hαnonneg T)]
      _ ≤ α 0 * U + α T * U :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hq 0) (hαnonneg 0))
          (mul_le_mul_of_nonneg_left (hq T) (hαnonneg T))
      _ ≤ 2 * α 0 * U := by
        have hT : α T ≤ α 0 := hαanti (Nat.zero_le T)
        have hm := mul_le_mul_of_nonneg_right hT hU
        linarith
  rw [habel]
  exact (energy_td_euclidean_norm_sub _ _).trans (by linarith)

@[blueprint "lem:i-three-multiplicative-poisson-family"
  (statement := /-- Let $M$ satisfy the uniform feature bound with constant $\phi_\infty$ and the geometric-mixing estimate with constant $\tau$, and fix $\theta^*\in\mathbb R^d$.  There exists a family $u_\theta(s,s')\in\mathbb R^d$ such that
  \[
  u_\theta(s,s')-\sum_jP(s',j)u_\theta(s',j)
  =(A-A_{(s,s')})(\theta-\theta^*),
  \]
  with $\lVert u_\theta(s,s')\rVert_2\leq64\tau\phi_\infty^2\lVert\theta-\theta^*\rVert_2$ and $\lVert u_\theta(s,s')-u_{\theta'}(s,s')\rVert_2\leq64\tau\phi_\infty^2\lVert\theta-\theta'\rVert_2$. -/)
  (proof := /-- Express $(A-A_{(s,s')})(\theta-\theta^*)$ as the sample-update difference $g(\theta,(s,s'))-g(\theta^*,(s,s'))$ minus the corresponding mean-update difference.  The stationary average vanishes by \cref{lem:energy-mean-update-average}.  The sample and mean Lipschitz estimates in \cref{lem:energy-update-difference-bound}, followed by the difference triangle inequality in \cref{lem:energy-td-euclidean-norm-sub}, give both the growth and parameter-Lipschitz bounds with constant $4\phi_\infty^2$.  Apply \cref{lem:td-edge-poisson-solution-lipschitz}; its factor $16$ gives the asserted constant $64$. -/)
  (title := /-- Lipschitz edge-Poisson family for multiplicative TD noise -/)
  (latexEnv := "lemma")]
lemma i_three_multiplicative_poisson_family {n d : ℕ} (M : td_model n d)
    (τ φinf rinf : ℝ) (θstar : td_vector d)
    (hbounds : td_uniform_bounds M φinf rinf)
    (hmix : td_geometric_mixing M τ) :
    ∃ u : td_vector d → Fin n → Fin n → td_vector d,
      (∀ θ s s', u θ s s' -
          ∑ j, (M.transition s' j).toReal • u θ s' j =
            Matrix.mulVec (td_population_matrix M - td_sample_matrix M s s')
              (θ - θstar)) ∧
      (∀ θ s s', td_euclidean_norm (u θ s s') ≤
        64 * τ * φinf ^ 2 * td_euclidean_norm (θ - θstar)) ∧
      ∀ θ θ' s s', td_euclidean_norm (u θ s s' - u θ' s s') ≤
        64 * τ * φinf ^ 2 * td_euclidean_norm (θ - θ') := by
  classical
  let h : td_vector d → Fin n → Fin n → td_vector d := fun θ s s' =>
    (td_update M θ s s' - td_update M θstar s s') -
      (td_mean_update M θ - td_mean_update M θstar)
  have hh (θ : td_vector d) (s s' : Fin n) :
      h θ s s' = Matrix.mulVec
        (td_population_matrix M - td_sample_matrix M s s') (θ - θstar) := by
    ext i
    simp only [h, td_update, td_mean_update, Matrix.mulVec, dotProduct,
      Matrix.sub_apply, Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  have hpmf (p : PMF (Fin n)) : ∑ s, (p s).toReal = 1 := by
    have hpenn : ∑ s, p s = 1 := by
      have hfin : HasSum (fun s : Fin n => p s) (∑ s, p s) := hasSum_fintype _
      exact ((PMF.hasSum_coe_one p).unique hfin).symm
    rw [← ENNReal.toReal_sum]
    · rw [hpenn]
      norm_num
    · exact fun s hs => p.apply_ne_top s
  have hmeanavg (v : td_vector d) :
      (∑ s, (M.stationary s).toReal •
        ∑ s', (M.transition s s').toReal • v) = v := by
    have hinner (s : Fin n) :
        (∑ s', (M.transition s s').toReal • v) = v := by
      rw [← Finset.sum_smul, hpmf]
      simp
    simp_rw [hinner]
    rw [← Finset.sum_smul, hpmf]
    simp
  have hcenter : ∀ θ, (∑ s, (M.stationary s).toReal •
      (∑ s', (M.transition s s').toReal • h θ s s')) = 0 := by
    intro θ
    dsimp [h]
    simp_rw [smul_sub, Finset.sum_sub_distrib]
    simp only [smul_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    rw [← energy_mean_update_average M θ,
      ← energy_mean_update_average M θstar,
      Finset.sum_sub_distrib,
      hmeanavg (td_mean_update M θ), hmeanavg (td_mean_update M θstar)]
    abel
  have hbound : ∀ θ s s',
      td_euclidean_norm (h θ s s') ≤
        4 * φinf ^ 2 * td_euclidean_norm (θ - θstar) := by
    intro θ s s'
    have hd := energy_update_difference_bound M φinf rinf θ θstar hbounds
    exact (energy_td_euclidean_norm_sub _ _).trans (by
      have hs := hd.1 s s'
      have hm := hd.2
      nlinarith)
  have hlip : ∀ θ θ' s s',
      td_euclidean_norm (h θ s s' - h θ' s s') ≤
        4 * φinf ^ 2 * td_euclidean_norm (θ - θ') := by
    intro θ θ' s s'
    have heq : h θ s s' - h θ' s s' =
        (td_update M θ s s' - td_update M θ' s s') -
          (td_mean_update M θ - td_mean_update M θ') := by
      dsimp [h]
      abel
    rw [heq]
    have hd := energy_update_difference_bound M φinf rinf θ θ' hbounds
    exact (energy_td_euclidean_norm_sub _ _).trans (by
      have hs := hd.1 s s'
      have hm := hd.2
      nlinarith)
  obtain ⟨u, hpoisson, hubound, hulip⟩ :=
    td_edge_poisson_solution_lipschitz M τ (4 * φinf ^ 2) (4 * φinf ^ 2)
      θstar h hmix (by positivity) (by positivity) hcenter hbound hlip
  refine ⟨u, ?_, ?_, ?_⟩
  · intro θ s s'
    rw [← hh]
    exact hpoisson θ s s'
  · intro θ s s'
    have hb := hubound θ s s'
    nlinarith
  · intro θ θ' s s'
    have hl := hulip θ θ' s s'
    nlinarith

@[blueprint "lem:i-three-stopped-poisson-control"
  (statement := /-- Let $n,d\in\mathbb N$, let $M$ be a finite TD model on $\operatorname{Fin}(n)$ with parameter space $\mathbb R^d$, let $a,\eta\colon\mathbb N\to\mathbb R$, and let $\delta,c,\tau,\phi_\infty,r_\infty\in\mathbb R$.  Fix $\theta_0,\theta^*\in\mathbb R^d$ and $s_0\in\operatorname{Fin}(n)$.  Assume that $a$ is positive and non-increasing, $a_0\leq1$, and $\sum_{t=0}^\infty a_t^2<\infty$; that $\eta_t=\eta_{\mathrm{base}}a_t$ for every $t$, where $\eta_{\mathrm{base}}=(c\tau\phi_\infty^2)^{-1}$; that $0<\delta<1$ and $c>c_{\min}(a,\delta)$; that $M$ satisfies the uniform bounds with constants $\phi_\infty,r_\infty$ and the geometric-mixing condition with constant $\tau$; and that $\theta^*$ is a TD fixed point of $M$.  Then the canonical path law of $M$ started from $s_0$ assigns probability at least $1-\delta/4$ to the localized multiplicative-noise event $\mathcal E_3$ of \cref{def:i-three-control-event}. -/)
  (proof := /-- Put $B=R_{\mathrm{base}}$ and $R=\rho B$.  The definition of $B$ gives $\lVert\theta^*\rVert_2\leq B$ and $r_\infty\leq\phi_\infty B$, while \cref{lem:rho-bootstrap-inequality} gives $2B\leq R$.  By \cref{lem:i-three-multiplicative-poisson-family}, choose $u_\theta(s,s')$ satisfying
  \[
  u_\theta(s,s')-\sum_jP(s',j)u_\theta(s',j)
  =(A-A_{(s,s')})(\theta-\theta^*)
  \]
  together with the growth and Lipschitz bounds having constant $64\tau\phi_\infty^2$.  Set $q_\theta(s)=\sum_jP(s,j)u_\theta(s,j)$.  The canonical norm realization in \cref{lem:energy-td-euclidean-norm-bridge} and the unit transition masses give
  $\lVert q_\theta(s)\rVert_2\leq128\tau\phi_\infty^2R$ whenever $\lVert\theta-\theta^*\rVert_2\leq2R$, and preserve the same Lipschitz constant for $q_\theta$.

  For every finite prefix through time $t$, evaluate $u$ at the stopped iterate determined by its constant-tail extension and multiply the centered edge difference $u_{\widetilde\theta_t}(S_t,j)-q_{\widetilde\theta_t}(S_t)$ by the stopped stepsize.  The prefix identity in \cref{lem:energy-stopped-iterate-prefix} identifies this construction with the stopped process on every full path.  When the stopped stepsize is nonzero, the current iterate lies in the radius-$R$ ball; hence the difference triangle inequality and homogeneity from \cref{lem:energy-td-euclidean-norm-sub,lem:energy-td-euclidean-norm-smul} bound the increment by $256\tau\phi_\infty^2R\eta_t$.  Its transition mean is zero, and its squared bound is summable.  Applying \cref{lem:td-markov-anytime-vector} with confidence $\delta/4$ produces an event of probability at least $1-\delta/4$ on which the corresponding martingale sums are bounded simultaneously for all horizons by
  \[
  256\tau\phi_\infty^2R\sqrt{\sum_t\eta_t^2}
  \sqrt{2\log(8/\delta)}.
  \]

  Along a fixed path, \cref{lem:energy-stopped-stepsize-antitone} makes the stopped stepsizes nonnegative and non-increasing.  Insert an auxiliary sequence which equals $q_{\widetilde\theta_t}(S_t)$ while stopping remains active, and at the first inactive time uses the preceding active parameter.  Its norm is at most $128\tau\phi_\infty^2R$, so \cref{lem:i-three-nonnegative-weighted-coboundary-bound} bounds its weighted coboundary by $384\eta_0\tau\phi_\infty^2R$.  The remaining parameter-change term is controlled by the Lipschitz bound for $q$, the stopped recursion, and the sample-update estimate \cref{lem:energy-sample-update-bound}; its $t$th norm is at most $192\tau\phi_\infty^4R\eta_t^2$.  Summing these estimates uses \cref{lem:energy-td-euclidean-norm-bridge}, and combining the martingale and coboundary parts uses \cref{lem:energy-td-euclidean-norm-add}.

  Finally, on the radius event, induction in the stopped recursion identifies every stopped iterate and stepsize with its unstopped counterpart.  For $T\geq1$, positivity of the stepsizes gives $S_T>0$; the homogeneity identity in \cref{lem:energy-td-euclidean-norm-smul} therefore permits division by $S_T$.  The resulting inequality has exactly the three constants $128$, $192$, and $96$ in the event of \cref{def:i-three-control-event}.  Thus the martingale event is contained in $\mathcal E_3$, and monotonicity of the canonical path measure proves the result. -/)
  (title := /-- Stopped Poisson and martingale control of multiplicative noise -/)
  (latexEnv := "lemma")]
lemma i_three_stopped_poisson_control {n d : ℕ} (M : td_model n d)
    (a η : ℕ → ℝ) (δ c τ φinf rinf : ℝ)
    (θ0 θstar : td_vector d) (s0 : Fin n)
    (ha : admissible_stepsize_shape a)
    (hη : ∀ t, η t = pr_eta_base c τ φinf * a t)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hc : pr_c_min a δ < c)
    (hbounds : td_uniform_bounds M φinf rinf)
    (hmix : td_geometric_mixing M τ) (hfixed : td_fixed_point M θstar) :
    (td_markov_path_measure M s0).real
        (i_three_control_event M a η δ c τ φinf rinf θ0 θstar) ≥ 1 - δ / 4 := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure (td_markov_path_measure M s0) := by
    dsimp [td_markov_path_measure]
    infer_instance
  have hφ : 0 < φinf := hbounds.1
  have hτ : 1 ≤ τ := hmix.1
  have hcpos : 0 < c := by
    have hA : 0 < pr_a_one a δ := by rw [pr_a_one]; positivity
    have hA2 : 0 ≤ pr_a_two a := by rw [pr_a_two]; positivity
    have hs := Real.sqrt_nonneg ((pr_a_one a δ) ^ 2 + 4 * pr_a_two a)
    rw [pr_c_min] at hc
    nlinarith
  have hbase : 0 < pr_eta_base c τ φinf := by
    rw [pr_eta_base]
    positivity
  have hηpos (t : ℕ) : 0 < η t := by rw [hη t]; exact mul_pos hbase (ha.1 t)
  have hηanti : Antitone η := by
    intro i j hij
    rw [hη i, hη j]
    exact mul_le_mul_of_nonneg_left (ha.2.1 hij) hbase.le
  have hηsum : Summable (fun t => (η t) ^ 2) := by
    have hs := ha.2.2.2.mul_left ((pr_eta_base c τ φinf) ^ 2)
    apply hs.congr
    intro t
    rw [hη t]
    ring
  obtain ⟨hρ, _⟩ := rho_bootstrap_inequality a δ c ha hδ0 hδ1 hc
  let B := pr_base_radius θ0 θstar rinf φinf
  let R := pr_rho a δ c * B
  have hB : 0 ≤ B := by
    dsimp [B, pr_base_radius]
    exact (Real.sqrt_nonneg _).trans (le_max_left _ _)
  have hR : 0 ≤ R := by
    exact mul_nonneg (le_of_lt (lt_trans (by norm_num) hρ)) hB
  have hstar : td_euclidean_norm θstar ≤ B := by
    dsimp [B, pr_base_radius]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have herr0 : td_euclidean_norm (θ0 - θstar) ≤ B := by
    dsimp [B, pr_base_radius]
    exact le_max_left _ _
  have hBR : 2 * B ≤ R := by
    dsimp [R]
    nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_lt hρ)) hB]
  have hrB : rinf ≤ φinf * B := by
    have hr : rinf / φinf ≤ B := by
      dsimp [B, pr_base_radius]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    simpa [mul_comm] using (div_le_iff₀ hφ).mp hr
  obtain ⟨u, hupoisson, hubound, hulip⟩ :=
    i_three_multiplicative_poisson_family M τ φinf rinf θstar
      hbounds hmix
  have hrow (s : Fin n) : ∑ j, (M.transition s j).toReal = 1 := by
    have hpenn : ∑ j, M.transition s j = 1 := by
      have hfin : HasSum (fun j : Fin n => M.transition s j)
          (∑ j, M.transition s j) := hasSum_fintype _
      exact ((PMF.hasSum_coe_one (M.transition s)).unique hfin).symm
    rw [← ENNReal.toReal_sum]
    · rw [hpenn]
      norm_num
    · exact fun j hj => (M.transition s).apply_ne_top j
  let q : td_vector d → Fin n → td_vector d := fun θ s =>
    ∑ j, (M.transition s j).toReal • u θ s j
  have hqbound (θ : td_vector d)
      (hθ : td_euclidean_norm (θ - θstar) ≤ 2 * R) (s : Fin n) :
      td_euclidean_norm (q θ s) ≤ 128 * τ * φinf ^ 2 * R := by
    let L : td_vector d ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
    calc
      td_euclidean_norm (q θ s) = ‖L (q θ s)‖ := energy_td_euclidean_norm_bridge _
      _ ≤ ∑ j, ‖L ((M.transition s j).toReal • u θ s j)‖ := by
        dsimp [q]
        rw [map_sum]
        exact norm_sum_le _ _
      _ ≤ ∑ j, (M.transition s j).toReal *
          (64 * τ * φinf ^ 2 * td_euclidean_norm (θ - θstar)) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [map_smul, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg ENNReal.toReal_nonneg]
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        rw [← energy_td_euclidean_norm_bridge]
        exact hubound θ s j
      _ = 64 * τ * φinf ^ 2 * td_euclidean_norm (θ - θstar) := by
        rw [← Finset.sum_mul, hrow]
        ring
      _ ≤ 128 * τ * φinf ^ 2 * R := by
        have hn : 0 ≤ 64 * τ * φinf ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hθ hn]
  have hqlip (θ θ' : td_vector d) (s : Fin n) :
      td_euclidean_norm (q θ s - q θ' s) ≤
        64 * τ * φinf ^ 2 * td_euclidean_norm (θ - θ') := by
    let L : td_vector d ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
    calc
      td_euclidean_norm (q θ s - q θ' s) = ‖L (q θ s - q θ' s)‖ :=
        energy_td_euclidean_norm_bridge _
      _ ≤ ∑ j, ‖L ((M.transition s j).toReal •
          (u θ s j - u θ' s j))‖ := by
        have heq : q θ s - q θ' s =
            ∑ j, (M.transition s j).toReal • (u θ s j - u θ' s j) := by
          dsimp [q]
          simp_rw [smul_sub, Finset.sum_sub_distrib]
        rw [heq, map_sum]
        exact norm_sum_le _ _
      _ ≤ ∑ j, (M.transition s j).toReal *
          (64 * τ * φinf ^ 2 * td_euclidean_norm (θ - θ')) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [map_smul, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg ENNReal.toReal_nonneg]
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        rw [← energy_td_euclidean_norm_bridge]
        exact hulip θ θ' s j
      _ = _ := by rw [← Finset.sum_mul, hrow, one_mul]
  let θx : (t : ℕ) → ((i : Finset.Iic t) → Fin n) → td_vector d := fun t x =>
    td_stopped_iterates M η θ0 R t (energy_prefix_extension t x)
  let αx : (t : ℕ) → ((i : Finset.Iic t) → Fin n) → ℝ := fun t x =>
    td_stopped_stepsize M η θ0 R (energy_prefix_extension t x) t
  let F : (t : ℕ) → ((i : Finset.Iic t) → Fin n) → Fin n → td_vector d :=
    fun t x j => αx t x •
      (u (θx t x) (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩) j -
        q (θx t x) (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩))
  let b : ℕ → ℝ := fun t => 256 * τ * φinf ^ 2 * R * η t
  have hFcenter : ∀ t x, ∑ j, (M.transition
      (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩) j).toReal • F t x j = 0 := by
    intro t x
    let s := x ⟨t, Finset.mem_Iic.mpr le_rfl⟩
    change ∑ j, (M.transition s j).toReal •
      (αx t x • (u (θx t x) s j - q (θx t x) s)) = 0
    calc
      _ = αx t x • ∑ j, (M.transition s j).toReal •
          (u (θx t x) s j - q (θx t x) s) := by
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            simp only [smul_smul]
            rw [mul_comm]
      _ = αx t x • ((∑ j, (M.transition s j).toReal • u (θx t x) s j) -
          ∑ j, (M.transition s j).toReal • q (θx t x) s) := by
            simp_rw [smul_sub]
            rw [Finset.sum_sub_distrib, smul_sub]
      _ = αx t x • (q (θx t x) s -
          (∑ j, (M.transition s j).toReal) • q (θx t x) s) := by
            rw [← Finset.sum_smul]
      _ = 0 := by rw [hrow]; simp [q]
  have hbnonneg : ∀ t, 0 ≤ b t := by
    intro t
    dsimp [b]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        (le_trans (by norm_num) hτ)) (sq_nonneg φinf)) hR)
      (hηpos t).le
  have hFbound : ∀ t x j, td_euclidean_norm (F t x j) ≤ b t := by
    intro t x j
    by_cases hx : td_euclidean_norm (θx t x) ≤ R
    · have hdiff : td_euclidean_norm (θx t x - θstar) ≤ 2 * R := by
        exact (energy_td_euclidean_norm_sub _ _).trans (by nlinarith [hstar, hBR])
      have hu := hubound (θx t x) (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩) j
      have hq := hqbound (θx t x) hdiff (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩)
      have haeq : αx t x = η t := by simp [αx, td_stopped_stepsize, θx, hx]
      change td_euclidean_norm (αx t x •
        (u (θx t x) (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩) j -
          q (θx t x) (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩))) ≤ b t
      rw [haeq, energy_td_euclidean_norm_smul, abs_of_pos (hηpos t)]
      have hs := energy_td_euclidean_norm_sub
        (u (θx t x) (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩) j)
        (q (θx t x) (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩))
      dsimp [b]
      have hu' : td_euclidean_norm
          (u (θx t x) (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩) j) ≤
          128 * τ * φinf ^ 2 * R := by
        calc
          _ ≤ 64 * τ * φinf ^ 2 * td_euclidean_norm (θx t x - θstar) := hu
          _ ≤ 64 * τ * φinf ^ 2 * (2 * R) :=
            mul_le_mul_of_nonneg_left hdiff (by positivity)
          _ = _ := by ring
      have hd : td_euclidean_norm
          (u (θx t x) (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩) j -
            q (θx t x) (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩)) ≤
          256 * τ * φinf ^ 2 * R := hs.trans (by linarith)
      have hm := mul_le_mul_of_nonneg_left hd (hηpos t).le
      nlinarith
    · have haeq : αx t x = 0 := by simp [αx, td_stopped_stepsize, θx, hx]
      change td_euclidean_norm (αx t x •
        (u (θx t x) (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩) j -
          q (θx t x) (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩))) ≤ b t
      rw [haeq, zero_smul]
      simpa [td_euclidean_norm] using hbnonneg t
  have hbsum : Summable (fun t => (b t) ^ 2) := by
    have hs := hηsum.mul_left ((256 * τ * φinf ^ 2 * R) ^ 2)
    apply hs.congr
    intro t
    dsimp [b]
    ring
  have hε0 : 0 < δ / 4 := by positivity
  have hε1 : δ / 4 < 1 := by linarith
  let E : Set (ℕ → Fin n) := {path | ∀ T,
    td_euclidean_norm (∑ t ∈ Finset.range T,
      F t (Preorder.frestrictLe t path) (path (t + 1))) ≤
      Real.sqrt (∑' t, (b t) ^ 2) * Real.sqrt (2 * Real.log (2 / (δ / 4)))}
  have hprob : (td_markov_path_measure M s0).real E ≥ 1 - δ / 4 :=
    td_markov_anytime_vector M s0 F b (δ / 4) hFcenter hbnonneg hFbound
      hbsum hε0 hε1
  have hbmass : Real.sqrt (∑' t, (b t) ^ 2) =
      256 * τ * φinf ^ 2 * R * Real.sqrt (pr_square_mass η) := by
    have ht : (∑' t, (b t) ^ 2) =
        (256 * τ * φinf ^ 2 * R) ^ 2 * pr_square_mass η := by
      rw [pr_square_mass, ← tsum_mul_left]
      apply tsum_congr
      intro t
      dsimp [b]
      ring
    rw [ht, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
      abs_of_nonneg]
    positivity
  have hlog : 2 / (δ / 4) = 8 / δ := by
    field_simp [ne_of_gt hδ0]
    norm_num
  have hsubset : E ⊆ i_three_control_event M a η δ c τ φinf rinf θ0 θstar := by
    intro path hpath hradius T hT
    let θs : ℕ → td_vector d := fun t => td_stopped_iterates M η θ0 R t path
    let α : ℕ → ℝ := fun t => td_stopped_stepsize M η θ0 R path t
    have hαprops := energy_stopped_stepsize_antitone M η θ0 R path
      (fun t => (hηpos t).le) hηanti
    have hαnonneg := hαprops.1
    have hαanti := hαprops.2
    have hαle (t : ℕ) : α t ≤ η t := by
      dsimp [α, td_stopped_stepsize]
      split_ifs
      · exact le_rfl
      · exact (hηpos t).le
    have hactive (t : ℕ) (ht : α t ≠ 0) : td_euclidean_norm (θs t) ≤ R := by
      dsimp [α, θs, td_stopped_stepsize] at ht ⊢
      split_ifs at ht with h
      · exact h
      · contradiction
    have hactivediff (t : ℕ) (ht : α t ≠ 0) :
        td_euclidean_norm (θs t - θstar) ≤ 2 * R :=
      (energy_td_euclidean_norm_sub _ _).trans
        (by nlinarith [hactive t ht, hstar, hBR])
    have hmart : td_euclidean_norm (∑ t ∈ Finset.range T,
        α t • (u (θs t) (path t) (path (t + 1)) - q (θs t) (path t))) ≤
        256 * τ * φinf ^ 2 * R * Real.sqrt (pr_square_mass η) *
          Real.sqrt (2 * Real.log (8 / δ)) := by
      have hp := hpath T
      rw [hbmass, hlog] at hp
      have hαprefix (t : ℕ) :
          td_stopped_stepsize M η θ0 R
              (energy_prefix_extension t (Preorder.frestrictLe t path)) t =
            td_stopped_stepsize M η θ0 R path t := by
        unfold td_stopped_stepsize
        rw [energy_stopped_iterate_prefix M η θ0 R path t t le_rfl]
      simpa [F, θx, αx, θs, α, hαprefix, energy_stopped_iterate_prefix,
        Preorder.frestrictLe_apply] using hp
    let v : ℕ → td_vector d := fun t => match t with
      | 0 => q θ0 (path 0)
      | k + 1 => if α k = 0 then q θ0 (path (k + 1))
          else if α (k + 1) = 0 then q (θs k) (path (k + 1))
          else q (θs (k + 1)) (path (k + 1))
    have hvbound (t : ℕ) : td_euclidean_norm (v t) ≤
        128 * τ * φinf ^ 2 * R := by
      cases t with
      | zero =>
          simp only [v]
          exact hqbound θ0 (herr0.trans (by nlinarith [hBR])) (path 0)
      | succ k =>
          by_cases hk : α k = 0
          · simp [v, hk]
            exact hqbound θ0 (herr0.trans (by nlinarith [hBR])) (path (k + 1))
          · by_cases hk1 : α (k + 1) = 0
            · simp [v, hk, hk1]
              exact hqbound (θs k) (hactivediff k hk) (path (k + 1))
            · simp [v, hk, hk1]
              exact hqbound (θs (k + 1)) (hactivediff (k + 1) hk1) (path (k + 1))
    have hcob := i_three_nonnegative_weighted_coboundary_bound α v
      (128 * τ * φinf ^ 2 * R) T hαnonneg hαanti (by positivity) hvbound
    have hcob' : td_euclidean_norm (∑ t ∈ Finset.range T,
        α t • (v t - v (t + 1))) ≤ 384 * η 0 * τ * φinf ^ 2 * R := by
      exact hcob.trans (by
        have hz := hαle 0
        have hn : 0 ≤ 128 * τ * φinf ^ 2 * R := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hz hn])
    have hstep (t : ℕ) : θs (t + 1) - θs t =
        α t • td_update M (θs t) (path t) (path (t + 1)) := by
      dsimp [θs, α, td_stopped_stepsize]
      rw [td_stopped_iterates]
      split_ifs <;> simp_all
    have hremterm (t : ℕ) : td_euclidean_norm
        (if α (t + 1) = 0 then 0 else
          α t • (q (θs (t + 1)) (path (t + 1)) - q (θs t) (path (t + 1)))) ≤
        192 * τ * φinf ^ 4 * R * (η t) ^ 2 := by
      by_cases ht1 : α (t + 1) = 0
      · rw [if_pos ht1]
        rw [show td_euclidean_norm (0 : td_vector d) = 0 by
          simp [td_euclidean_norm]]
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
            (le_trans (by norm_num) hτ)) (by positivity)) hR)
          (sq_nonneg (η t))
      · have ht : α t ≠ 0 := by
          intro hz
          have := hαanti (Nat.le_succ t)
          change α (t + 1) ≤ α t at this
          rw [hz] at this
          exact ht1 (le_antisymm this (hαnonneg (t + 1)))
        rw [if_neg ht1, energy_td_euclidean_norm_smul,
          abs_of_nonneg (hαnonneg t)]
        have hu := energy_sample_update_bound M φinf rinf B R (θs t)
          (path t) (path (t + 1)) hbounds hrB hBR (hactive t ht)
        have hs : td_euclidean_norm (θs (t + 1) - θs t) ≤
            α t * ((5 / 2 : ℝ) * φinf ^ 2 * R) := by
          rw [hstep, energy_td_euclidean_norm_smul,
            abs_of_nonneg (hαnonneg t)]
          exact mul_le_mul_of_nonneg_left hu (hαnonneg t)
        have hq := hqlip (θs (t + 1)) (θs t) (path (t + 1))
        have ha0 : 0 ≤ α t := hαnonneg t
        have he0 : 0 ≤ η t := (hηpos t).le
        have hal := hαle t
        calc
          α t * td_euclidean_norm
              (q (θs (t + 1)) (path (t + 1)) - q (θs t) (path (t + 1))) ≤
              α t * (64 * τ * φinf ^ 2 *
                td_euclidean_norm (θs (t + 1) - θs t)) :=
            mul_le_mul_of_nonneg_left hq ha0
          _ ≤ α t * (64 * τ * φinf ^ 2 *
                (α t * ((5 / 2 : ℝ) * φinf ^ 2 * R))) := by
            gcongr
          _ = 160 * τ * φinf ^ 4 * R * (α t) ^ 2 := by ring
          _ ≤ 192 * τ * φinf ^ 4 * R * (η t) ^ 2 := by
            have hsq : (α t) ^ 2 ≤ (η t) ^ 2 := (sq_le_sq₀ ha0 he0).2 hal
            have hk : 0 ≤ τ * φinf ^ 4 * R := by positivity
            nlinarith [mul_le_mul_of_nonneg_left hsq hk]
    have hrem : td_euclidean_norm (∑ t ∈ Finset.range T,
        if α (t + 1) = 0 then 0 else
          α t • (q (θs (t + 1)) (path (t + 1)) - q (θs t) (path (t + 1)))) ≤
        192 * τ * φinf ^ 4 * R * pr_square_mass η := by
      let L : td_vector d ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
      calc
        td_euclidean_norm (∑ t ∈ Finset.range T,
            if α (t + 1) = 0 then 0 else α t •
              (q (θs (t + 1)) (path (t + 1)) - q (θs t) (path (t + 1)))) ≤
            ∑ t ∈ Finset.range T, 192 * τ * φinf ^ 4 * R * (η t) ^ 2 := by
              rw [energy_td_euclidean_norm_bridge, map_sum]
              calc
                _ ≤ ∑ t ∈ Finset.range T, ‖L (if α (t + 1) = 0 then 0 else α t •
                    (q (θs (t + 1)) (path (t + 1)) - q (θs t) (path (t + 1))))‖ :=
                  norm_sum_le _ _
                _ ≤ _ := by
                  apply Finset.sum_le_sum
                  intro t ht
                  rw [← energy_td_euclidean_norm_bridge]
                  exact hremterm t
        _ ≤ 192 * τ * φinf ^ 4 * R * pr_square_mass η := by
          rw [pr_square_mass]
          have hfin := Summable.sum_le_tsum (Finset.range T)
            (fun t ht => mul_nonneg (by positivity) (sq_nonneg (η t)))
            ((hηsum.mul_left (192 * τ * φinf ^ 4 * R)))
          rw [← tsum_mul_left]
          exact hfin
    have hsplit : (∑ t ∈ Finset.range T,
        α t • (q (θs t) (path t) - q (θs t) (path (t + 1)))) =
        (∑ t ∈ Finset.range T, α t • (v t - v (t + 1))) +
        ∑ t ∈ Finset.range T, if α (t + 1) = 0 then 0 else
          α t • (q (θs (t + 1)) (path (t + 1)) - q (θs t) (path (t + 1))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      by_cases hαt : α t = 0
      · have hle := hαanti (Nat.le_succ t)
        change α (t + 1) ≤ α t at hle
        rw [hαt] at hle
        have hαt1 : α (t + 1) = 0 := le_antisymm hle (hαnonneg _)
        simp [hαt, hαt1]
      · have hprev : ∀ k, t = k + 1 → α k ≠ 0 := by
          intro k hk hz
          subst t
          have hh := hαanti (Nat.le_succ k)
          change α (k + 1) ≤ α k at hh
          rw [hz] at hh
          exact hαt (le_antisymm hh (hαnonneg _))
        cases t with
        | zero =>
            by_cases h1 : α 1 = 0 <;>
              simp [v, θs, td_stopped_iterates, hαt, h1] <;> module
        | succ k =>
            have hk : α k ≠ 0 := hprev k rfl
            by_cases hk1 : α (k + 1 + 1) = 0 <;>
              simp [v, hk, hαt, hk1] <;> module
    have hcoball : td_euclidean_norm (∑ t ∈ Finset.range T,
        α t • (q (θs t) (path t) - q (θs t) (path (t + 1)))) ≤
        384 * η 0 * τ * φinf ^ 2 * R +
          192 * τ * φinf ^ 4 * R * pr_square_mass η := by
      rw [hsplit]
      exact (energy_td_euclidean_norm_add _ _).trans (add_le_add hcob' hrem)
    have hrawid : (∑ t ∈ Finset.range T, α t •
        Matrix.mulVec (td_population_matrix M - td_sample_matrix M (path t) (path (t + 1)))
          (θs t - θstar)) =
        (∑ t ∈ Finset.range T,
          α t • (u (θs t) (path t) (path (t + 1)) - q (θs t) (path t))) +
        ∑ t ∈ Finset.range T,
          α t • (q (θs t) (path t) - q (θs t) (path (t + 1))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      rw [← hupoisson (θs t) (path t) (path (t + 1))]
      dsimp [q]
      module
    have hraw : td_euclidean_norm (∑ t ∈ Finset.range T, α t •
        Matrix.mulVec (td_population_matrix M - td_sample_matrix M (path t) (path (t + 1)))
          (θs t - θstar)) ≤
        256 * τ * φinf ^ 2 * R * Real.sqrt (pr_square_mass η) *
            Real.sqrt (2 * Real.log (8 / δ)) +
          384 * η 0 * τ * φinf ^ 2 * R +
          192 * τ * φinf ^ 4 * R * pr_square_mass η := by
      rw [hrawid]
      exact (energy_td_euclidean_norm_add _ _).trans (by linarith [hmart, hcoball])
    have heqiter : ∀ t, θs t = td_iterates M η θ0 t path := by
      intro t
      induction t with
      | zero => rfl
      | succ t ih =>
          dsimp [θs] at ih ⊢
          rw [td_stopped_iterates, if_pos]
          · rw [td_iterates, ih]
          · rw [ih]
            exact hradius t
    have heqα : ∀ t, α t = η t := by
      intro t
      dsimp [α, td_stopped_stepsize]
      have heqt : td_stopped_iterates M η θ0 R t path =
          td_iterates M η θ0 t path := by simpa [θs] using heqiter t
      rw [heqt, if_pos (hradius t)]
    have hSpos : 0 < pr_step_mass η T := by
      unfold pr_step_mass
      apply Finset.sum_pos
      · intro i hi
        exact hηpos i
      · exact Finset.nonempty_range_iff.mpr (by omega)
    rw [td_i_three, energy_td_euclidean_norm_smul,
      abs_of_pos (inv_pos.mpr hSpos)]
    have hraw' : td_euclidean_norm (∑ t ∈ Finset.range T, η t •
        Matrix.mulVec (td_population_matrix M - td_sample_matrix M (path t) (path (t + 1)))
          (td_iterates M η θ0 t path - θstar)) ≤
        256 * τ * φinf ^ 2 * R * Real.sqrt (pr_square_mass η) *
            Real.sqrt (2 * Real.log (8 / δ)) +
          384 * η 0 * τ * φinf ^ 2 * R +
          192 * τ * φinf ^ 4 * R * pr_square_mass η := by
      simpa only [heqα, heqiter] using hraw
    calc
      (pr_step_mass η T)⁻¹ * td_euclidean_norm (∑ t ∈ Finset.range T, η t •
          Matrix.mulVec (td_population_matrix M - td_sample_matrix M (path t) (path (t + 1)))
            (td_iterates M η θ0 t path - θstar)) ≤
          (pr_step_mass η T)⁻¹ *
            (256 * τ * φinf ^ 2 * R * Real.sqrt (pr_square_mass η) *
                Real.sqrt (2 * Real.log (8 / δ)) +
              384 * η 0 * τ * φinf ^ 2 * R +
              192 * τ * φinf ^ 4 * R * pr_square_mass η) :=
        mul_le_mul_of_nonneg_left hraw' (inv_nonneg.mpr hSpos.le)
      _ = 2 / pr_step_mass η T *
            (128 * τ * φinf ^ 2 * R * Real.sqrt (pr_square_mass η) *
                Real.sqrt (2 * Real.log (8 / δ)) +
              192 * η 0 * τ * φinf ^ 2 * R) +
          2 / pr_step_mass η T *
            (96 * τ * φinf ^ 4 * R * pr_square_mass η) := by
        rw [div_eq_mul_inv]
        ring
  calc
    1 - δ / 4 ≤ (td_markov_path_measure M s0).real E := hprob
    _ ≤ (td_markov_path_measure M s0).real
        (i_three_control_event M a η δ c τ φinf rinf θ0 θstar) :=
      MeasureTheory.measureReal_mono hsubset (MeasureTheory.measure_ne_top _ _)

@[blueprint "lem:i-two-control-probability"
  (statement := /-- Let $n,d\in\mathbb N$, let $M$ be a finite TD model on $n$ states with parameter space $\mathbb R^d$, let $\eta\colon\mathbb N\to\mathbb R$, let $\delta,\tau,\phi_\infty,r_\infty\in\mathbb R$, let $\theta^*\in\mathbb R^d$, and let $s_0$ be an initial state.  Assume that $\eta_t>0$ for every $t$, that $\eta$ is non-increasing, and that $\sum_{t=0}^{\infty}\eta_t^2<\infty$; that $0<\delta<1$; that $M$ satisfies the uniform feature and reward bounds with constants $\phi_\infty,r_\infty$ and the geometric-mixing condition with constant $\tau$; and that $\theta^*$ is a TD fixed point.  Then the event $\mathcal E_2$ of \cref{def:i-two-control-event} has probability at least $1-\delta/4$ under the canonical Markov path law of $M$ started at $s_0$. -/)
  (proof := /-- Apply \cref{lem:i-two-poisson-martingale-control}, whose conclusion is exactly the asserted lower bound for the event $\mathcal E_2$. -/)
  (title := /-- High-probability fixed-point-noise estimate -/)
  (latexEnv := "lemma")]
lemma i_two_control_probability {n d : ℕ} (M : td_model n d) (η : ℕ → ℝ)
    (δ τ φinf rinf : ℝ) (θstar : td_vector d) (s0 : Fin n)
    (hηpos : ∀ t, 0 < η t) (hηanti : Antitone η)
    (hηsum : Summable (fun t => (η t) ^ 2))
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hbounds : td_uniform_bounds M φinf rinf)
    (hmix : td_geometric_mixing M τ) (hfixed : td_fixed_point M θstar) :
    (td_markov_path_measure M s0).real
        (i_two_control_event M η δ τ φinf rinf θstar) ≥ 1 - δ / 4 := by
  exact i_two_poisson_martingale_control M η δ τ φinf rinf θstar s0
    hηpos hηanti hηsum hδ0 hδ1 hbounds hmix hfixed

@[blueprint "lem:i-three-control-probability"
  (statement := /-- Let $M$ be a finite TD model, let $\theta^*$ be a TD fixed point, and let $\phi_\infty>0$, $r_\infty\geq0$, and $\tau\geq1$ satisfy the uniform boundedness and geometric-mixing hypotheses.  Let $a_t>0$ be non-increasing, with $a_0\leq1$ and $\sum_ta_t^2<\infty$, set $\eta_t=(c\tau\phi_\infty^2)^{-1}a_t$, fix $\delta\in(0,1)$, and suppose $c>c_{\min}(\delta)$.  For every initial vector $\theta_0$ and initial state $s_0$, the localized event $\mathcal E_3$ has probability at least $1-\delta/4$ under the canonical Markov path law started at $s_0$. -/)
  (proof := /-- Apply \cref{lem:i-three-stopped-poisson-control}, which supplies the stopped Poisson decomposition, the canonical-trajectory martingale estimate, the Abel remainder bounds, and the identification with the original recursion on $\mathcal E_R$.  Its conclusion is exactly the required probability estimate for \cref{def:i-three-control-event}. -/)
  (title := /-- High-probability multiplicative-noise estimate -/)
  (latexEnv := "lemma")]
lemma i_three_control_probability {n d : ℕ} (M : td_model n d) (a η : ℕ → ℝ)
    (δ c τ φinf rinf : ℝ) (θ0 θstar : td_vector d) (s0 : Fin n)
    (ha : admissible_stepsize_shape a) (hη : ∀ t, η t = pr_eta_base c τ φinf * a t)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hc : pr_c_min a δ < c)
    (hbounds : td_uniform_bounds M φinf rinf)
    (hmix : td_geometric_mixing M τ) (hfixed : td_fixed_point M θstar) :
    (td_markov_path_measure M s0).real
        (i_three_control_event M a η δ c τ φinf rinf θ0 θstar) ≥ 1 - δ / 4 := by
  exact i_three_stopped_poisson_control M a η δ c τ φinf rinf θ0 θstar s0
    ha hη hδ0 hδ1 hc hbounds hmix hfixed

@[blueprint "lem:energy-control-probability"
  (statement := /-- Let $n,d\in\mathbb N$, let $M$ be a finite TD model on $n$ states with parameter space $\mathbb R^d$, let $a,\eta\colon\mathbb N\to\mathbb R$, let $\delta,c,\tau,\phi_\infty,r_\infty\in\mathbb R$, let $\theta_0,\theta^*\in\mathbb R^d$, and let $s_0$ be an initial state.  Assume that $a$ is positive and non-increasing, $a_0\leq1$, and $\sum_ta_t^2<\infty$; that $\eta_t=(c\tau\phi_\infty^2)^{-1}a_t$ for every $t$; that $0<\delta<1$ and $c>c_{\min}(a,\delta)$; that $M$ satisfies the uniform feature and reward bounds with constants $\phi_\infty,r_\infty$ and the geometric-mixing bound with constant $\tau$; and that $\theta^*$ is a TD fixed point.  Then the localized energy-control event $\mathcal E_4$ of \cref{def:energy-control-event} has probability at least $1-\delta/4$ under the canonical Markov path law of $M$ started at $s_0$. -/)
  (proof := /-- By \cref{lem:energy-stopped-martingale-control}, the stopped energy-control event of \cref{def:stopped-energy-control-event} has probability at least $1-\delta/4$.  We prove that this event is contained in the localized event of \cref{def:energy-control-event}.  Fix a path in the stopped event and assume that it belongs to the radius event of \cref{def:bounded-iterates-event}, as required by the antecedent in the definition of the localized event.  Put $R=\rho R_{\mathrm{base}}$.  Induction on $t$, using \cref{def:td-stopped-iterates,def:td-iterates}, shows that $\widetilde\theta_t=\theta_t$: after the induction hypothesis, the radius assumption forces the active branch of the stopped recursion.  It then follows from \cref{def:td-stopped-stepsize} that $\widetilde\eta_t=\eta_t$ for every $t$.  Substitution of these identities into \cref{def:td-stopped-recursion-remainder,def:td-recursion-remainder} gives $\widetilde B_T=B_T$ and turns the stopped energy inequality into the required localized inequality for every $T\geq1$.  Hence the desired event contains the stopped event, and monotonicity of the canonical path measure proves the asserted bound. -/)
  (title := /-- High-probability robust energy estimate -/)
  (latexEnv := "lemma")]
lemma energy_control_probability {n d : ℕ} (M : td_model n d) (a η : ℕ → ℝ)
    (δ c τ φinf rinf : ℝ) (θ0 θstar : td_vector d) (s0 : Fin n)
    (ha : admissible_stepsize_shape a) (hη : ∀ t, η t = pr_eta_base c τ φinf * a t)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hc : pr_c_min a δ < c)
    (hbounds : td_uniform_bounds M φinf rinf)
    (hmix : td_geometric_mixing M τ) (hfixed : td_fixed_point M θstar) :
    (td_markov_path_measure M s0).real
        (energy_control_event M a η δ c τ φinf rinf θ0 θstar) ≥ 1 - δ / 4 := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure (td_markov_path_measure M s0) := by
    dsimp [td_markov_path_measure]
    infer_instance
  have hsubset :
      stopped_energy_control_event M a η δ c τ φinf rinf θ0 θstar ⊆
        energy_control_event M a η δ c τ φinf rinf θ0 θstar := by
    intro path hstop
    intro hbounded
    intro T hT
    let R := pr_rho a δ c * pr_base_radius θ0 θstar rinf φinf
    have heq : ∀ t, td_stopped_iterates M η θ0 R t path =
        td_iterates M η θ0 t path := by
      intro t
      induction t with
      | zero => rfl
      | succ t ih =>
          rw [td_stopped_iterates, if_pos, td_iterates, ih]
          simpa only [ih, R] using hbounded t
    have hstep : ∀ t, td_stopped_stepsize M η θ0 R path t = η t := by
      intro t
      rw [td_stopped_stepsize, if_pos]
      simpa only [heq t, R] using hbounded t
    have hcontrol := hstop T hT
    dsimp only at hcontrol
    simpa only [R, td_stopped_recursion_remainder, td_recursion_remainder, heq, hstep]
      using hcontrol
  calc
    1 - δ / 4 ≤ (td_markov_path_measure M s0).real
        (stopped_energy_control_event M a η δ c τ φinf rinf θ0 θstar) :=
      energy_stopped_martingale_control M a η δ c τ φinf rinf θ0 θstar s0
        ha hη hδ0 hδ1 hc hbounds hmix hfixed
    _ ≤ (td_markov_path_measure M s0).real
        (energy_control_event M a η δ c τ φinf rinf θ0 θstar) :=
      MeasureTheory.measureReal_mono hsubset

@[blueprint "lem:analysis-event-probability"
  (statement := /-- Let $n,d\in\mathbb N$, let $M$ be a TD model on the state space
  $\operatorname{Fin}(n)$ with parameter vectors in $\mathbb R^d$, let
  $a,\eta\colon\mathbb N\to\mathbb R$, let
  $\delta,c,\tau,\phi_\infty,r_\infty\in\mathbb R$, let
  $\theta_0,\theta^*\in\mathbb R^d$, and let $s_0\in\operatorname{Fin}(n)$.
  Assume that $a$ has the admissible stepsize shape of
  \cref{def:admissible-stepsize-shape}, that
  $\eta_t=(c\tau\phi_\infty^2)^{-1}a_t$ for every $t\in\mathbb N$, that
  $0<\delta<1$, and that $c>c_{\min}(a,\delta)$.  Assume also that $M$
  satisfies the uniform-boundedness condition with constants
  $\phi_\infty,r_\infty$ and the geometric-mixing condition with constant
  $\tau$, and that $\theta^*$ is a TD fixed point of $M$.  Then, under the
  canonical Markov path law started at $s_0$, the common event
  $\mathcal E=\mathcal E_R\cap\mathcal E_2\cap\mathcal E_3\cap\mathcal E_4$
  of \cref{def:analysis-event} has probability at least $1-\delta$. -/)
  (proof := /-- The schedule assumptions imply that $\eta_t>0$ for every
  $t$, that $\eta$ is non-increasing, and that $\sum_t\eta_t^2<\infty$.
  Hence \cref{lem:bounded-iterates-probability,lem:i-two-control-probability,lem:i-three-control-probability,lem:energy-control-probability}
  give probability at least $1-\delta/4$ to each of
  $\mathcal E_R,\mathcal E_2,\mathcal E_3,\mathcal E_4$, respectively.
  Each event is measurable: the iterate at a fixed time is a measurable
  function of finitely many path coordinates, as are the fixed-time noise and
  energy expressions, and the simultaneous events are countable
  intersections of their measurable fixed-time inequalities.  Consequently,
  the complement of each event has probability at most $\delta/4$.
  Subadditivity bounds the union of the four complements by $\delta$; taking
  the complement identifies the remaining event with
  $\mathcal E_R\cap\mathcal E_2\cap\mathcal E_3\cap\mathcal E_4$ and proves the
  claimed lower bound. -/)
  (title := /-- Probability of the common analysis event -/)
  (latexEnv := "lemma")]
lemma analysis_event_probability {n d : ℕ} (M : td_model n d) (a η : ℕ → ℝ)
    (δ c τ φinf rinf : ℝ) (θ0 θstar : td_vector d) (s0 : Fin n)
    (ha : admissible_stepsize_shape a) (hη : ∀ t, η t = pr_eta_base c τ φinf * a t)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hc : pr_c_min a δ < c)
    (hbounds : td_uniform_bounds M φinf rinf)
    (hmix : td_geometric_mixing M τ) (hfixed : td_fixed_point M θstar) :
    (td_markov_path_measure M s0).real
        (analysis_event M a η δ c τ φinf rinf θ0 θstar) ≥ 1 - δ := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure (td_markov_path_measure M s0) := by
    dsimp [td_markov_path_measure]
    infer_instance
  have hit : ∀ t, Measurable (fun path => td_iterates M η θ0 t path) := by
    intro t
    induction t with
    | zero => exact measurable_const
    | succ t ih =>
        simp only [td_iterates]
        apply measurable_pi_lambda
        intro i
        simp [td_update, td_sample_vector, td_sample_matrix, Matrix.mulVec]
        measurability
  have hi2 : ∀ T, Measurable (fun path => td_i_two M η θstar path T) := by
    intro T
    apply measurable_pi_lambda
    intro i
    simp [td_i_two, td_sample_vector, td_sample_matrix, Matrix.mulVec]
    measurability
  have hi3 : ∀ T, Measurable (fun path => td_i_three M η θ0 θstar path T) := by
    intro T
    apply measurable_pi_lambda
    intro i
    simp [td_i_three, td_sample_matrix, Matrix.mulVec]
    measurability
  have hrem : ∀ T,
      Measurable (fun path => td_recursion_remainder M η θ0 θstar path T) := by
    intro T
    unfold td_recursion_remainder td_euclidean_norm td_update td_sample_vector
      td_sample_matrix td_mean_update Matrix.mulVec
    measurability
  have hR : MeasurableSet
      (bounded_iterates_event M a η δ c φinf rinf θ0 θstar) := by
    rw [bounded_iterates_event, ← Set.iInter_setOf]
    apply MeasurableSet.iInter
    intro t
    apply measurableSet_le _ measurable_const
    unfold td_euclidean_norm
    measurability
  have h2 : MeasurableSet (i_two_control_event M η δ τ φinf rinf θstar) := by
    rw [i_two_control_event, ← Set.iInter_setOf]
    apply MeasurableSet.iInter
    intro T
    by_cases hT : 1 ≤ T
    · simp only [hT, true_implies]
      apply measurableSet_le _ measurable_const
      unfold td_euclidean_norm
      measurability
    · simp [hT]
  have h3 : MeasurableSet
      (i_three_control_event M a η δ c τ φinf rinf θ0 θstar) := by
    unfold i_three_control_event
    apply hR.imp
    rw [← Set.iInter_setOf]
    apply MeasurableSet.iInter
    intro T
    by_cases hT : 1 ≤ T
    · simp only [hT, true_implies]
      apply measurableSet_le _ measurable_const
      unfold td_euclidean_norm
      measurability
    · simp [hT]
  have henergy : ∀ T, Measurable (fun path =>
      (∑ t ∈ Finset.range T, (η t) ^ 2 *
          (td_euclidean_norm (td_update M (td_iterates M η θ0 t path)
            (path t) (path (t + 1)))) ^ 2) +
        td_recursion_remainder M η θ0 θstar path T) := by
    intro T
    apply Measurable.add _ (hrem T)
    apply Finset.measurable_sum
    intro t ht
    unfold td_euclidean_norm td_update td_sample_vector td_sample_matrix Matrix.mulVec
    measurability
  have h4 : MeasurableSet
      (energy_control_event M a η δ c τ φinf rinf θ0 θstar) := by
    unfold energy_control_event
    apply hR.imp
    rw [← Set.iInter_setOf]
    apply MeasurableSet.iInter
    intro T
    by_cases hT : 1 ≤ T
    · simp only [hT, true_implies]
      exact measurableSet_le (henergy T) measurable_const
    · simp [hT]
  have hφ : 0 < φinf := hbounds.1
  have hτ : 1 ≤ τ := hmix.1
  have hcpos : 0 < c := by
    have hA : 0 < pr_a_one a δ := by rw [pr_a_one]; positivity
    have hA2 : 0 ≤ pr_a_two a := by rw [pr_a_two]; positivity
    have hs := Real.sqrt_nonneg ((pr_a_one a δ) ^ 2 + 4 * pr_a_two a)
    rw [pr_c_min] at hc
    nlinarith
  have hbase : 0 < pr_eta_base c τ φinf := by
    rw [pr_eta_base]
    positivity
  have hηpos : ∀ t, 0 < η t := by
    intro t
    rw [hη t]
    exact mul_pos hbase (ha.1 t)
  have hηanti : Antitone η := by
    intro i j hij
    rw [hη i, hη j]
    exact mul_le_mul_of_nonneg_left (ha.2.1 hij) hbase.le
  have hηsum : Summable (fun t => (η t) ^ 2) := by
    have hs := ha.2.2.2.mul_left ((pr_eta_base c τ φinf) ^ 2)
    apply hs.congr
    intro t
    rw [hη t]
    ring
  have hpR := bounded_iterates_probability M a η δ c τ φinf rinf θ0 θstar s0
    ha hη hδ0 hδ1 hc hbounds hmix hfixed
  have hp2 := i_two_control_probability M η δ τ φinf rinf θstar s0
    hηpos hηanti hηsum hδ0 hδ1 hbounds hmix hfixed
  have hp3 := i_three_control_probability M a η δ c τ φinf rinf θ0 θstar s0
    ha hη hδ0 hδ1 hc hbounds hmix hfixed
  have hp4 := energy_control_probability M a η δ c τ φinf rinf θ0 θstar s0
    ha hη hδ0 hδ1 hc hbounds hmix hfixed
  have hcR : (td_markov_path_measure M s0).real
      (bounded_iterates_event M a η δ c φinf rinf θ0 θstar)ᶜ ≤ δ / 4 := by
    have hcomp := MeasureTheory.probReal_add_probReal_compl
      (μ := td_markov_path_measure M s0) hR
    linarith
  have hc2 : (td_markov_path_measure M s0).real
      (i_two_control_event M η δ τ φinf rinf θstar)ᶜ ≤ δ / 4 := by
    have hcomp := MeasureTheory.probReal_add_probReal_compl
      (μ := td_markov_path_measure M s0) h2
    linarith
  have hc3 : (td_markov_path_measure M s0).real
      (i_three_control_event M a η δ c τ φinf rinf θ0 θstar)ᶜ ≤ δ / 4 := by
    have hcomp := MeasureTheory.probReal_add_probReal_compl
      (μ := td_markov_path_measure M s0) h3
    linarith
  have hc4 : (td_markov_path_measure M s0).real
      (energy_control_event M a η δ c τ φinf rinf θ0 θstar)ᶜ ≤ δ / 4 := by
    have hcomp := MeasureTheory.probReal_add_probReal_compl
      (μ := td_markov_path_measure M s0) h4
    linarith
  have hbad : (td_markov_path_measure M s0).real
      ((bounded_iterates_event M a η δ c φinf rinf θ0 θstar)ᶜ ∪
        (i_two_control_event M η δ τ φinf rinf θstar)ᶜ ∪
        (i_three_control_event M a η δ c τ φinf rinf θ0 θstar)ᶜ ∪
        (energy_control_event M a η δ c τ φinf rinf θ0 θstar)ᶜ) ≤ δ := by
    calc
      _ ≤ (td_markov_path_measure M s0).real
            ((bounded_iterates_event M a η δ c φinf rinf θ0 θstar)ᶜ ∪
              (i_two_control_event M η δ τ φinf rinf θstar)ᶜ ∪
              (i_three_control_event M a η δ c τ φinf rinf θ0 θstar)ᶜ) +
            (td_markov_path_measure M s0).real
              (energy_control_event M a η δ c τ φinf rinf θ0 θstar)ᶜ :=
        MeasureTheory.measureReal_union_le _ _
      _ ≤ ((td_markov_path_measure M s0).real
              ((bounded_iterates_event M a η δ c φinf rinf θ0 θstar)ᶜ ∪
                (i_two_control_event M η δ τ φinf rinf θstar)ᶜ) +
            (td_markov_path_measure M s0).real
              (i_three_control_event M a η δ c τ φinf rinf θ0 θstar)ᶜ) +
            (td_markov_path_measure M s0).real
              (energy_control_event M a η δ c τ φinf rinf θ0 θstar)ᶜ := by
        gcongr
        exact MeasureTheory.measureReal_union_le _ _
      _ ≤ (((td_markov_path_measure M s0).real
              (bounded_iterates_event M a η δ c φinf rinf θ0 θstar)ᶜ +
            (td_markov_path_measure M s0).real
              (i_two_control_event M η δ τ φinf rinf θstar)ᶜ) +
            (td_markov_path_measure M s0).real
              (i_three_control_event M a η δ c τ φinf rinf θ0 θstar)ᶜ) +
            (td_markov_path_measure M s0).real
              (energy_control_event M a η δ c τ φinf rinf θ0 θstar)ᶜ := by
        gcongr
        exact MeasureTheory.measureReal_union_le _ _
      _ ≤ δ := by linarith
  have hE : MeasurableSet
      (analysis_event M a η δ c τ φinf rinf θ0 θstar) := by
    exact ((hR.inter h2).inter h3).inter h4
  have hcomp := MeasureTheory.probReal_add_probReal_compl
    (μ := td_markov_path_measure M s0) hE
  have hcompl :
      (analysis_event M a η δ c τ φinf rinf θ0 θstar)ᶜ =
        (bounded_iterates_event M a η δ c φinf rinf θ0 θstar)ᶜ ∪
          (i_two_control_event M η δ τ φinf rinf θstar)ᶜ ∪
          (i_three_control_event M a η δ c τ φinf rinf θ0 θstar)ᶜ ∪
          (energy_control_event M a η δ c τ φinf rinf θ0 θstar)ᶜ := by
    simp only [analysis_event, Set.compl_inter]
  rw [hcompl] at hcomp
  linarith

@[blueprint "lem:fast-constant-collection"
  (statement := /-- For every $d\in\mathbb N$, sequences $a,\eta:\mathbb N\to\mathbb R$, parameters $\delta,c,\tau,\phi_\infty,r_\infty\in\mathbb R$, and vectors $\theta_0,\theta^*\in\mathbb R^d$, write $H=\operatorname{tsum}_{t\in\mathbb N}\eta_t^2$, $\rho=\rho(a,\delta,c)$, $R_{\mathrm{base}}=\max\{\lVert\theta_0-\theta^*\rVert_2,\lVert\theta^*\rVert_2,r_\infty/\phi_\infty\}$, and $R_{\max}=\rho R_{\mathrm{base}}$.  Then
  \[
  \begin{aligned}
  &2R_{\max}+(2\sqrt H\sqrt{2\log(8/\delta)}+3\eta_0)48\tau\phi_\infty^2R_{\max}
    +256\tau\phi_\infty^2R_{\max}\sqrt H\sqrt{2\log(8/\delta)}\\
  &\qquad +384\eta_0\tau\phi_\infty^2R_{\max}
    +192\tau\phi_\infty^4R_{\max}H
   =R_{\max}\bigl[2+2\tau\phi_\infty^2(264\eta_0+176\sqrt H\sqrt{2\log(8/\delta)})+192\tau\phi_\infty^4H\bigr].
  \end{aligned}
  \] -/)
  (proof := /-- Unfold $C_{\mathrm{fast}}$ according to \cref{def:pr-fast-constant} and distribute every product.  The coefficient of $\eta_0\tau\phi_\infty^2R_{\max}$ is $3\cdot48+384=528=2\cdot264$, while the coefficient of $\sqrt H\sqrt{2\log(8/\delta)}\tau\phi_\infty^2R_{\max}$ is $2\cdot48+256=352=2\cdot176$.  The constant coefficient $2$ and the coefficient $192$ of $\tau\phi_\infty^4R_{\max}H$ already coincide, so commutativity and distributivity give the asserted identity. -/)
  (title := /-- Collection of the fast-rate constants -/)
  (latexEnv := "lemma")]
lemma fast_constant_collection {d : ℕ} (a η : ℕ → ℝ) (δ c τ φinf rinf : ℝ)
    (θ0 θstar : td_vector d) :
    2 * (pr_rho a δ c * pr_base_radius θ0 θstar rinf φinf) +
      (2 * Real.sqrt (pr_square_mass η) * Real.sqrt (2 * Real.log (8 / δ)) + 3 * η 0) *
        48 * τ * φinf ^ 2 *
          (pr_rho a δ c * pr_base_radius θ0 θstar rinf φinf) +
      256 * τ * φinf ^ 2 *
        (pr_rho a δ c * pr_base_radius θ0 θstar rinf φinf) *
        Real.sqrt (pr_square_mass η) * Real.sqrt (2 * Real.log (8 / δ)) +
      384 * η 0 * τ * φinf ^ 2 *
        (pr_rho a δ c * pr_base_radius θ0 θstar rinf φinf) +
      192 * τ * φinf ^ 4 *
        (pr_rho a δ c * pr_base_radius θ0 θstar rinf φinf) * pr_square_mass η =
      pr_fast_constant a η δ c τ φinf rinf θ0 θstar := by
  unfold pr_fast_constant
  ring

@[blueprint "lem:fast-rate-on-analysis-event"
  (statement := /-- Let $n,d\in\mathbb N$, let $M$ be a TD model with $n$
  states and $d$-dimensional parameter vectors, and let
  $a,\eta\colon\mathbb N\to\mathbb R$.  Fix
  $\delta,c,\tau,\phi_\infty,r_\infty,\omega\in\mathbb R$, vectors
  $\theta_0,\theta^*\in\mathbb R^d$, and a path
  $s\colon\mathbb N\to\operatorname{Fin}(n)$.  Suppose that $\eta_t>0$ for
  every $t$, that $\theta^*$ is a TD fixed point for $M$, and that
  $\omega>0$ satisfies
  \[
  \omega\lVert\theta-\theta^*\rVert_2^2
    \leq f(\theta)-f(\theta^*)
  \qquad\text{for every }\theta\in\mathbb R^d.
  \]
  If $s$ belongs to the common event $\mathcal E$ of
  \cref{def:analysis-event}, then, for every $T\in\mathbb N$ with $T\geq1$,
  \[
  f(\bar\theta_T)-f(\theta^*)
    \leq\frac{C_{\mathrm{fast}}^2}{\omega S_T^2},
  \]
  where $S_T$ and $C_{\mathrm{fast}}$ are defined in
  \cref{def:pr-step-mass,def:pr-fast-constant}. -/)
  (proof := /-- Write $A$ for the population matrix of
  \cref{def:td-population-matrix}.  Expanding the sample matrix, exchanging the
  finite sums, and using both the unit row sums of the transition kernel and
  stationarity shows that, for every $\theta$,
  \[
  f(\theta)-f(\theta^*)=(\theta-\theta^*)^\top A(\theta-\theta^*).
  \]
  This is exactly the quadratic form obtained by expanding the weighted square
  and Dirichlet terms in \cref{def:td-potential}.

  Put $R=\rho R_{\mathrm{base}}$.  First suppose that $R=0$.  The radius part
  of \cref{def:analysis-event}, together with nonnegativity of the Euclidean
  norm, forces every iterate to vanish.  The recursion and positivity of every
  $\eta_t$ then force every sample update to vanish as well.  The fixed-point
  equation identifies the mean drift at the zero vector with
  $-(f(0)-f(\theta^*))$.  Consequently, the exact remainder in
  \cref{def:td-recursion-remainder} equals
  $2S_T(f(0)-f(\theta^*))$.  The energy part of the event has zero right-hand
  side in this case, so this remainder is nonpositive.  Since $S_T>0$, one has
  $f(0)-f(\theta^*)\leq0$.  The average is zero and the constant in
  \cref{def:pr-fast-constant} is also zero, which proves the claim.

  Now suppose that $R>0$.  The definition of $\rho$ in \cref{def:pr-rho}
  implies $\rho>2$; hence $R_{\mathrm{base}}\leq R$.  The definition in
  \cref{def:pr-base-radius} then bounds both $\lVert\theta^*\rVert_2$ and
  $r_\infty/\phi_\infty$ by $R$, giving
  $r_\infty\phi_\infty+2\phi_\infty^2\lVert\theta^*\rVert_2
  \leq3\phi_\infty^2R$.  The three components of
  \cref{def:analysis-event} therefore give the stated bounds for $I_{2,T}$ and
  $I_{3,T}$, while the radius bound and the triangle inequality give
  $\lVert I_{1,T}\rVert_2\leq2R/S_T$.  Applying
  \cref{lem:averaged-td-decomposition}, the triangle inequality, and then
  \cref{lem:fast-constant-collection} yields
  \[
  \lVert A(\bar\theta_T-\theta^*)\rVert_2
    \leq C_{\mathrm{fast}}/S_T.
  \]

  Finally set $e=\bar\theta_T-\theta^*$ and
  $p=f(\bar\theta_T)-f(\theta^*)$.  The quadratic identity and
  Cauchy--Schwarz give $p\leq\lVert e\rVert_2\lVert Ae\rVert_2$, whereas the
  curvature hypothesis gives $\omega\lVert e\rVert_2^2\leq p$.  If
  $\lVert e\rVert_2=0$, the desired bridge is immediate.  Otherwise, cancellation
  of the positive factor $\lVert e\rVert_2$ gives
  $\omega\lVert e\rVert_2\leq\lVert Ae\rVert_2$, and hence
  $p\leq\lVert Ae\rVert_2^2/\omega$.  Substitution of the preceding matrix
  bound, using $S_T>0$, $\omega>0$, and the nonnegativity of
  $C_{\mathrm{fast}}$, proves the displayed inequality. -/)
  (title := /-- Fast rate on the common event -/)
  (latexEnv := "lemma")]
lemma fast_rate_on_analysis_event {n d : ℕ} (M : td_model n d) (a η : ℕ → ℝ)
    (δ c τ φinf rinf ω : ℝ) (θ0 θstar : td_vector d) (path : ℕ → Fin n)
    (hηpos : ∀ t, 0 < η t) (hfixed : td_fixed_point M θstar)
    (hcurv : td_curvature M θstar ω)
    (hpath : path ∈ analysis_event M a η δ c τ φinf rinf θ0 θstar) :
    ∀ T, 1 ≤ T →
      td_potential M θstar (pr_average η (fun t => td_iterates M η θ0 t path) T) -
          td_potential M θstar θstar ≤
        (pr_fast_constant a η δ c τ φinf rinf θ0 θstar) ^ 2 /
          (ω * (pr_step_mass η T) ^ 2) := by
  intro T hT
  rcases hcurv with ⟨hω, hcurv⟩
  have hSpos : 0 < pr_step_mass η T := by
    unfold pr_step_mass
    apply Finset.sum_pos
    · intro i hi
      exact hηpos i
    · exact Finset.nonempty_range_iff.mpr (by omega)
  have hnorm_nonneg (x : td_vector d) : 0 ≤ td_euclidean_norm x :=
    Real.sqrt_nonneg _
  have hnorm_sq (x : td_vector d) :
      td_euclidean_norm x ^ 2 = ∑ i, (x i) ^ 2 := by
    unfold td_euclidean_norm
    rw [Real.sq_sqrt]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hnormzero : td_euclidean_norm (0 : td_vector d) = 0 := by
    unfold td_euclidean_norm
    simp
  have hnorm_eq_zero {x : td_vector d} (hx : td_euclidean_norm x = 0) : x = 0 := by
    funext i
    have hi : (x i) ^ 2 ≤ ∑ j, (x j) ^ 2 := by
      exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [← hnorm_sq x, hx] at hi
    simp only [Pi.zero_apply]
    nlinarith
  have hdot (x y : td_vector d) :
      x ⬝ᵥ y ≤ td_euclidean_norm x * td_euclidean_norm y := by
    simpa only [dotProduct, td_euclidean_norm] using
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ x y
  have htri (x y : td_vector d) :
      td_euclidean_norm (x + y) ≤ td_euclidean_norm x + td_euclidean_norm y := by
    have hsquare :
        td_euclidean_norm (x + y) ^ 2 ≤
          (td_euclidean_norm x + td_euclidean_norm y) ^ 2 := by
      rw [hnorm_sq]
      simp only [Pi.add_apply]
      calc
        ∑ i, (x i + y i) ^ 2 =
            (∑ i, (x i) ^ 2) + 2 * (x ⬝ᵥ y) + ∑ i, (y i) ^ 2 := by
              simp_rw [add_pow_two]
              simp only [dotProduct, Finset.sum_add_distrib, Finset.mul_sum,
                Finset.sum_mul]
              ring
        _ ≤ (∑ i, (x i) ^ 2) +
            2 * (td_euclidean_norm x * td_euclidean_norm y) +
            ∑ i, (y i) ^ 2 := by nlinarith [hdot x y]
        _ = _ := by rw [← hnorm_sq x, ← hnorm_sq y]; ring
    nlinarith [hnorm_nonneg (x + y), hnorm_nonneg x, hnorm_nonneg y]
  have hnorm_smul (r : ℝ) (x : td_vector d) :
      td_euclidean_norm (r • x) = |r| * td_euclidean_norm x := by
    unfold td_euclidean_norm
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (∑ i, (r * x i) ^ 2) = r ^ 2 * ∑ i, (x i) ^ 2 by
      simp_rw [mul_pow]
      rw [Finset.mul_sum]]
    rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs]
  have hnorm_neg (x : td_vector d) :
      td_euclidean_norm (-x) = td_euclidean_norm x := by
    simpa using hnorm_smul (-1 : ℝ) x
  have hsub (x y : td_vector d) :
      td_euclidean_norm (x - y) ≤ td_euclidean_norm x + td_euclidean_norm y := by
    rw [sub_eq_add_neg]
    simpa only [hnorm_neg] using htri x (-y)
  have hsum4 (f : Fin d → Fin d → Fin n → Fin n → ℝ) :
      (∑ i, ∑ j, ∑ s, ∑ s', f i j s s') =
        ∑ s, ∑ s', ∑ i, ∑ j, f i j s s' := by
    calc
      _ = ∑ i, ∑ s, ∑ j, ∑ s', f i j s s' := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
      _ = ∑ s, ∑ i, ∑ j, ∑ s', f i j s s' := by rw [Finset.sum_comm]
      _ = ∑ s, ∑ i, ∑ s', ∑ j, f i j s s' := by
        apply Finset.sum_congr rfl
        intro s hs
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
      _ = ∑ s, ∑ s', ∑ i, ∑ j, f i j s s' := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.sum_comm]
  have hpot (θ : td_vector d) :
      td_potential M θstar θ - td_potential M θstar θstar =
        (θ - θstar) ⬝ᵥ
          Matrix.mulVec (td_population_matrix M) (θ - θstar) := by
    have hp (s : Fin n) : (∑ s', M.transition s s') = 1 := by
      simpa using PMF.tsum_coe (M.transition s)
    have hrow (s : Fin n) : (∑ s', (M.transition s s').toReal) = 1 := by
      rw [← ENNReal.toReal_sum (fun i _ => (M.transition s).apply_ne_top i)]
      rw [hp]
      exact ENNReal.toReal_one
    have hdir (v : Fin n → ℝ) :
        td_dirichlet_energy M v = td_weighted_square M v -
          ∑ s, ∑ s', (M.stationary s).toReal * (M.transition s s').toReal *
            v s * v s' := by
      have hfirst :
          (∑ s, ∑ s', (M.stationary s).toReal * (M.transition s s').toReal *
              (v s) ^ 2) = ∑ s, (M.stationary s).toReal * (v s) ^ 2 := by
        apply Finset.sum_congr rfl
        intro s hs
        calc
          _ = ((M.stationary s).toReal * (v s) ^ 2) *
                ∑ s', (M.transition s s').toReal := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro s' hs'
              ring
          _ = _ := by rw [hrow]; ring
      have hsecond :
          (∑ s, ∑ s', (M.stationary s).toReal * (M.transition s s').toReal *
              (v s') ^ 2) = ∑ s, (M.stationary s).toReal * (v s) ^ 2 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro s' hs'
        calc
          _ = (v s') ^ 2 *
                ∑ s, (M.stationary s).toReal * (M.transition s s').toReal := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro s hs
              ring
          _ = _ := by rw [M.stationary_eq]; ring
      unfold td_dirichlet_energy td_weighted_square
      rw [show (∑ s, ∑ s', (M.stationary s).toReal *
          (M.transition s s').toReal * (v s - v s') ^ 2) =
          (∑ s, ∑ s', (M.stationary s).toReal *
            (M.transition s s').toReal * (v s) ^ 2) +
          (∑ s, ∑ s', (M.stationary s).toReal *
            (M.transition s s').toReal * (v s') ^ 2) -
          2 * (∑ s, ∑ s', (M.stationary s).toReal *
            (M.transition s s').toReal * v s * v s') by
        calc
          _ = ∑ s, ∑ s',
              ((M.stationary s).toReal * (M.transition s s').toReal * (v s) ^ 2 +
                (M.stationary s).toReal * (M.transition s s').toReal * (v s') ^ 2 -
                2 * ((M.stationary s).toReal * (M.transition s s').toReal *
                  v s * v s')) := by
              apply Finset.sum_congr rfl
              intro s hs
              apply Finset.sum_congr rfl
              intro s' hs'
              ring
          _ = _ := by
              simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                Finset.mul_sum, Finset.sum_mul]
      ]
      rw [hfirst, hsecond]
      ring
    have hsample (s s' : Fin n) :
        (θ - θstar) ⬝ᵥ Matrix.mulVec (td_sample_matrix M s s') (θ - θstar) =
          (td_value M θ - td_value M θstar) s *
            ((td_value M θ - td_value M θstar) s -
              M.discount * (td_value M θ - td_value M θstar) s') := by
      simp [td_sample_matrix, Matrix.mulVec, dotProduct, td_value]
      have hvalue (r : Fin n) :
          (∑ i, (θ i - θstar i) * M.feature r i) =
            (∑ i, M.feature r i * θ i) -
              ∑ i, M.feature r i * θstar i := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      have hsecond :
          (∑ i, (M.feature s i - M.discount * M.feature s' i) *
              (θ i - θstar i)) =
            (∑ i, (θ i - θstar i) * M.feature s i) -
              M.discount * ∑ i, (θ i - θstar i) * M.feature s' i := by
        calc
          _ = ∑ i, ((θ i - θstar i) * M.feature s i -
                M.discount * ((θ i - θstar i) * M.feature s' i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
          _ = _ := by rw [Finset.sum_sub_distrib, Finset.mul_sum]
      calc
        _ = (∑ i, (θ i - θstar i) * M.feature s i) *
              ∑ j, (M.feature s j - M.discount * M.feature s' j) *
                (θ j - θstar j) := by
            rw [Finset.sum_mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
        _ = _ := by rw [hsecond, hvalue s, hvalue s']
    have hpopulation :
        (θ - θstar) ⬝ᵥ Matrix.mulVec (td_population_matrix M) (θ - θstar) =
          td_weighted_square M (td_value M θ - td_value M θstar) -
            M.discount *
              ∑ s, ∑ s', (M.stationary s).toReal * (M.transition s s').toReal *
                (td_value M θ - td_value M θstar) s *
                (td_value M θ - td_value M θstar) s' := by
      calc
        _ = ∑ s, ∑ s', (M.stationary s).toReal * (M.transition s s').toReal *
              ((θ - θstar) ⬝ᵥ
                Matrix.mulVec (td_sample_matrix M s s') (θ - θstar)) := by
            simp [td_population_matrix, Matrix.mulVec, dotProduct]
            simp only [Finset.mul_sum, Finset.sum_mul]
            rw [hsum4]
            apply Finset.sum_congr rfl
            intro s hs
            apply Finset.sum_congr rfl
            intro s' hs'
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            ring
        _ = _ := by
          simp_rw [hsample]
          unfold td_weighted_square
          have hfirst :
              (∑ s, ∑ s', (M.stationary s).toReal *
                  (M.transition s s').toReal *
                    ((td_value M θ - td_value M θstar) s) ^ 2) =
                ∑ s, (M.stationary s).toReal *
                  ((td_value M θ - td_value M θstar) s) ^ 2 := by
            apply Finset.sum_congr rfl
            intro s hs
            calc
              _ = ((M.stationary s).toReal *
                    ((td_value M θ - td_value M θstar) s) ^ 2) *
                    ∑ s', (M.transition s s').toReal := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro s' hs'
                  ring
              _ = _ := by rw [hrow]; ring
          calc
            _ = (∑ s, ∑ s', (M.stationary s).toReal *
                    (M.transition s s').toReal *
                      ((td_value M θ - td_value M θstar) s) ^ 2) -
                  M.discount *
                    ∑ s, ∑ s', (M.stationary s).toReal *
                      (M.transition s s').toReal *
                        (td_value M θ - td_value M θstar) s *
                        (td_value M θ - td_value M θstar) s' := by
                simp only [Finset.mul_sum, Finset.sum_mul,
                  Finset.sum_sub_distrib]
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro s hs
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro s' hs'
                ring
            _ = _ := by rw [hfirst]
    rw [hpopulation]
    unfold td_potential
    rw [hdir]
    simp [td_weighted_square, td_dirichlet_energy, td_value]
    ring
  simp only [analysis_event, Set.mem_inter_iff] at hpath
  rcases hpath with ⟨⟨⟨hR, htwo⟩, hthree⟩, henergy⟩
  change ∀ t, td_euclidean_norm (td_iterates M η θ0 t path) ≤
    pr_rho a δ c * pr_base_radius θ0 θstar rinf φinf at hR
  change ∀ U, 1 ≤ U →
    td_euclidean_norm (td_i_two M η θstar path U) ≤ _ at htwo
  change (path ∈ bounded_iterates_event M a η δ c φinf rinf θ0 θstar →
    ∀ U, 1 ≤ U → td_euclidean_norm (td_i_three M η θ0 θstar path U) ≤ _) at hthree
  change (path ∈ bounded_iterates_event M a η δ c φinf rinf θ0 θstar →
    ∀ U, 1 ≤ U → _ ≤ _) at henergy
  have hbounded : path ∈ bounded_iterates_event M a η δ c φinf rinf θ0 θstar := by
    exact hR
  have hthreeT := hthree hbounded T hT
  have henergyT := henergy hbounded T hT
  have htwoT := htwo T hT
  have hdecomp := averaged_td_decomposition M η θ0 θstar path T hfixed hηpos hT
  set R := pr_rho a δ c * pr_base_radius θ0 θstar rinf φinf
  set B := pr_base_radius θ0 θstar rinf φinf
  change ∀ t, td_euclidean_norm (td_iterates M η θ0 t path) ≤ R at hR
  change td_euclidean_norm (td_i_three M η θ0 θstar path T) ≤
    2 / pr_step_mass η T *
        (128 * τ * φinf ^ 2 * R * Real.sqrt (pr_square_mass η) *
            Real.sqrt (2 * Real.log (8 / δ)) + 192 * η 0 * τ * φinf ^ 2 * R) +
      2 / pr_step_mass η T * (96 * τ * φinf ^ 4 * R * pr_square_mass η) at hthreeT
  change (∑ t ∈ Finset.range T, (η t) ^ 2 *
      (td_euclidean_norm (td_update M (td_iterates M η θ0 t path)
        (path t) (path (t + 1)))) ^ 2) +
      td_recursion_remainder M η θ0 θstar path T ≤
    768 * τ * φinf ^ 2 * R ^ 2 * Real.sqrt (pr_square_mass η) *
        Real.sqrt (2 * Real.log (8 / δ)) +
      1152 * η 0 * τ * φinf ^ 2 * R ^ 2 +
      1344 * τ * φinf ^ 4 * R ^ 2 * pr_square_mass η +
      9 * φinf ^ 4 * R ^ 2 * pr_square_mass η at henergyT
  have hRnonneg : 0 ≤ R := by
    exact le_trans (hnorm_nonneg _) (hR 0)
  by_cases hRzero : R = 0
  · rw [hRzero] at hR hthreeT henergyT
    have hzeroiter (t : ℕ) : td_iterates M η θ0 t path = 0 := by
      apply hnorm_eq_zero
      exact le_antisymm (hR t) (hnorm_nonneg _)
    have hθ0zero : θ0 = 0 := by
      simpa [td_iterates] using hzeroiter 0
    have havgzero : pr_average η (fun t => td_iterates M η θ0 t path) T = 0 := by
      unfold pr_average
      simp_rw [hzeroiter]
      simp
    have hscaledzero (t : ℕ) :
        η t • td_update M (td_iterates M η θ0 t path) (path t) (path (t + 1)) = 0 := by
      calc
        _ = td_iterates M η θ0 (t + 1) path - td_iterates M η θ0 t path := by
          simp [td_iterates]
        _ = 0 := by rw [hzeroiter, hzeroiter]; simp
    have hupdatezero (t : ℕ) :
        td_update M (td_iterates M η θ0 t path) (path t) (path (t + 1)) = 0 := by
      funext i
      have hi := congrFun (hscaledzero t) i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
      exact (mul_eq_zero.mp hi).resolve_left (ne_of_gt (hηpos t))
    have hmean :
        td_mean_update M (0 : td_vector d) ⬝ᵥ ((0 : td_vector d) - θstar) =
          -(td_potential M θstar (0 : td_vector d) -
            td_potential M θstar θstar) := by
      rw [hpot]
      have hmeanvector :
          td_mean_update M (0 : td_vector d) =
            Matrix.mulVec (td_population_matrix M) θstar := by
        funext i
        simp only [td_mean_update, Pi.sub_apply, Matrix.mulVec, dotProduct, Pi.zero_apply,
          mul_zero, Finset.sum_const_zero, sub_zero]
        exact (congrFun hfixed i).symm
      rw [hmeanvector]
      simp only [dotProduct, Matrix.mulVec, Pi.zero_apply, zero_sub, Pi.neg_apply]
      have hinner (i : Fin d) :
          (∑ j, td_population_matrix M i j * -θstar j) =
            -(∑ j, td_population_matrix M i j * θstar j) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hinner i]
      ring
    have hrem : td_recursion_remainder M η θ0 θstar path T =
        2 * pr_step_mass η T *
          (td_potential M θstar (0 : td_vector d) - td_potential M θstar θstar) := by
      unfold td_recursion_remainder
      simp_rw [hupdatezero, hzeroiter]
      rw [hθ0zero]
      simp_rw [hmean]
      simp only [zero_sub, Pi.zero_apply, zero_pow, OfNat.ofNat_ne_zero, mul_zero,
        Finset.sum_const_zero, sub_zero, zero_mul, hnormzero]
      unfold pr_step_mass
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum,
        Finset.sum_mul, Finset.sum_neg_distrib]
      simp only [pow_two, mul_zero, sub_self, Finset.sum_const_zero, neg_zero,
        zero_sub]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    have hremnonpos : td_recursion_remainder M η θ0 θstar path T ≤ 0 := by
      simpa [hupdatezero, hnormzero] using henergyT
    have hpnonpos :
        td_potential M θstar (0 : td_vector d) - td_potential M θstar θstar ≤ 0 := by
      rw [hrem] at hremnonpos
      nlinarith
    have hfastzero : pr_fast_constant a η δ c τ φinf rinf θ0 θstar = 0 := by
      unfold pr_fast_constant
      change R * _ = 0
      rw [hRzero]
      ring
    rw [havgzero, hfastzero]
    simpa [hω.ne', hSpos.ne'] using hpnonpos
  · have hRpos : 0 < R := lt_of_le_of_ne hRnonneg (Ne.symm hRzero)
    have hBnonneg : 0 ≤ B := by
      dsimp [B, pr_base_radius]
      exact le_trans (hnorm_nonneg (θ0 - θstar)) (le_max_left _ _)
    have hrhopos : 0 < pr_rho a δ c := by
      by_contra hnrho
      have hrhononpos : pr_rho a δ c ≤ 0 := le_of_not_gt hnrho
      have : R ≤ 0 := by
        rw [show R = pr_rho a δ c * B by rfl]
        exact mul_nonpos_of_nonpos_of_nonneg hrhononpos hBnonneg
      linarith
    have ha2nonneg : 0 ≤ pr_a_two a := by
      unfold pr_a_two
      positivity
    have ha1pos : 0 < pr_a_one a δ := by
      unfold pr_a_one
      positivity
    have hsqrtdenpos :
        0 < Real.sqrt (c ^ 2 - pr_a_one a δ * c - pr_a_two a) := by
      have hsqrtnonneg := Real.sqrt_nonneg (c ^ 2 - pr_a_one a δ * c - pr_a_two a)
      by_contra hn
      have hz : Real.sqrt (c ^ 2 - pr_a_one a δ * c - pr_a_two a) = 0 :=
        le_antisymm (le_of_not_gt hn) hsqrtnonneg
      rw [pr_rho, hz, div_zero] at hrhopos
      linarith
    have hcpos : 0 < c := by
      rw [pr_rho] at hrhopos
      have hdiv := (div_pos_iff.mp hrhopos)
      rcases hdiv with hdiv | hdiv
      · nlinarith [hdiv.1]
      · nlinarith [hdiv.2, Real.sqrt_nonneg
          (c ^ 2 - pr_a_one a δ * c - pr_a_two a)]
    have hdenpos : 0 < c ^ 2 - pr_a_one a δ * c - pr_a_two a :=
      Real.sqrt_pos.mp hsqrtdenpos
    have hsqrtlt : Real.sqrt (c ^ 2 - pr_a_one a δ * c - pr_a_two a) < c := by
      have hsqsqrt := Real.sq_sqrt (le_of_lt hdenpos)
      nlinarith
    have hrhotwo : 2 < pr_rho a δ c := by
      rw [pr_rho, lt_div_iff₀ hsqrtdenpos]
      nlinarith
    have hBleR : B ≤ R := by
      calc
        B = 1 * B := by ring
        _ ≤ pr_rho a δ c * B :=
          mul_le_mul_of_nonneg_right (le_of_lt (lt_trans (by norm_num) hrhotwo)) hBnonneg
        _ = R := by rfl
    have hBtheta : td_euclidean_norm θstar ≤ B := by
      dsimp [B, pr_base_radius]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hBratio : rinf / φinf ≤ B := by
      dsimp [B, pr_base_radius]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hrphi : rinf * φinf = φinf ^ 2 * (rinf / φinf) := by
      by_cases hφ : φinf = 0
      · simp [hφ]
      · field_simp
    have hraw :
        rinf * φinf + 2 * φinf ^ 2 * td_euclidean_norm θstar ≤
          3 * φinf ^ 2 * R := by
      rw [hrphi]
      have hsum : rinf / φinf + 2 * td_euclidean_norm θstar ≤ 3 * B := by
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left hsum (sq_nonneg φinf)
      have hBRmul := mul_le_mul_of_nonneg_left hBleR (sq_nonneg φinf)
      nlinarith
    have hmassnonneg : 0 ≤ pr_square_mass η := by
      unfold pr_square_mass
      exact tsum_nonneg fun _ => sq_nonneg _
    have hsqrtmassnonneg : 0 ≤ Real.sqrt (pr_square_mass η) := Real.sqrt_nonneg _
    have hsqrtlognonneg : 0 ≤ Real.sqrt (2 * Real.log (8 / δ)) := Real.sqrt_nonneg _
    have htwo_bound :
        td_euclidean_norm (td_i_two M η θstar path T) ≤
          (2 * Real.sqrt (pr_square_mass η) * Real.sqrt (2 * Real.log (8 / δ)) +
              3 * η 0) * 48 * τ * φinf ^ 2 * R / pr_step_mass η T := by
      by_cases hφ : φinf = 0
      · simpa [hφ] using htwoT
      · have hφsqpos : 0 < φinf ^ 2 := sq_pos_of_ne_zero hφ
        have hη0pos := hηpos 0
        have hcoefpos : 0 <
            2 / pr_step_mass η T *
              (128 * φinf ^ 2 * R * Real.sqrt (pr_square_mass η) *
                  Real.sqrt (2 * Real.log (8 / δ)) +
                192 * η 0 * φinf ^ 2 * R) +
              2 / pr_step_mass η T *
                (96 * φinf ^ 4 * R * pr_square_mass η) := by
          have hfirst : 0 <
              128 * φinf ^ 2 * R * Real.sqrt (pr_square_mass η) *
                    Real.sqrt (2 * Real.log (8 / δ)) +
                192 * η 0 * φinf ^ 2 * R := by
            positivity
          have hsecond : 0 ≤ 96 * φinf ^ 4 * R * pr_square_mass η := by
            positivity
          have hdivpos : 0 < 2 / pr_step_mass η T := div_pos (by norm_num) hSpos
          positivity
        have hfactor :
            2 / pr_step_mass η T *
                (128 * τ * φinf ^ 2 * R * Real.sqrt (pr_square_mass η) *
                    Real.sqrt (2 * Real.log (8 / δ)) +
                  192 * η 0 * τ * φinf ^ 2 * R) +
              2 / pr_step_mass η T *
                (96 * τ * φinf ^ 4 * R * pr_square_mass η) =
              τ * (2 / pr_step_mass η T *
                (128 * φinf ^ 2 * R * Real.sqrt (pr_square_mass η) *
                    Real.sqrt (2 * Real.log (8 / δ)) +
                  192 * η 0 * φinf ^ 2 * R) +
                2 / pr_step_mass η T *
                  (96 * φinf ^ 4 * R * pr_square_mass η)) := by ring
        rw [hfactor] at hthreeT
        have hthree_nonneg := hnorm_nonneg (td_i_three M η θ0 θstar path T)
        have htaunonneg : 0 ≤ τ := by nlinarith
        have hnoise_nonneg :
            0 ≤ 2 * Real.sqrt (pr_square_mass η) * Real.sqrt (2 * Real.log (8 / δ)) +
              3 * η 0 := by positivity
        have hcoefnonneg : 0 ≤
            2 / pr_step_mass η T *
              (2 * Real.sqrt (pr_square_mass η) * Real.sqrt (2 * Real.log (8 / δ)) +
                3 * η 0) * 8 * τ := by positivity
        calc
          _ ≤ 2 / pr_step_mass η T *
              (2 * Real.sqrt (pr_square_mass η) * Real.sqrt (2 * Real.log (8 / δ)) +
                3 * η 0) * 8 * τ *
                  (rinf * φinf + 2 * φinf ^ 2 * td_euclidean_norm θstar) := htwoT
          _ ≤ 2 / pr_step_mass η T *
              (2 * Real.sqrt (pr_square_mass η) * Real.sqrt (2 * Real.log (8 / δ)) +
                3 * η 0) * 8 * τ * (3 * φinf ^ 2 * R) :=
            mul_le_mul_of_nonneg_left hraw hcoefnonneg
          _ = _ := by ring
    have hthree_bound :
        td_euclidean_norm (td_i_three M η θ0 θstar path T) ≤
          (256 * τ * φinf ^ 2 * R * Real.sqrt (pr_square_mass η) *
              Real.sqrt (2 * Real.log (8 / δ)) +
            384 * η 0 * τ * φinf ^ 2 * R +
            192 * τ * φinf ^ 4 * R * pr_square_mass η) /
              pr_step_mass η T := by
      calc
        _ ≤ 2 / pr_step_mass η T *
              (128 * τ * φinf ^ 2 * R * Real.sqrt (pr_square_mass η) *
                  Real.sqrt (2 * Real.log (8 / δ)) +
                192 * η 0 * τ * φinf ^ 2 * R) +
            2 / pr_step_mass η T *
              (96 * τ * φinf ^ 4 * R * pr_square_mass η) := hthreeT
        _ = _ := by ring
    have hR0 : td_euclidean_norm θ0 ≤ R := by
      simpa [td_iterates] using hR 0
    have hRT := hR T
    have hione_bound : td_euclidean_norm (td_i_one M η θ0 path T) ≤ 2 * R /
        pr_step_mass η T := by
      have hinvnonneg : 0 ≤ (pr_step_mass η T)⁻¹ := le_of_lt (inv_pos.mpr hSpos)
      calc
        _ = |(pr_step_mass η T)⁻¹| *
              td_euclidean_norm (θ0 - td_iterates M η θ0 T path) := by
            unfold td_i_one
            rw [hnorm_smul]
        _ = (pr_step_mass η T)⁻¹ *
              td_euclidean_norm (θ0 - td_iterates M η θ0 T path) := by
            rw [abs_of_nonneg hinvnonneg]
        _ ≤ (pr_step_mass η T)⁻¹ *
              (td_euclidean_norm θ0 + td_euclidean_norm (td_iterates M η θ0 T path)) :=
            mul_le_mul_of_nonneg_left (hsub _ _) hinvnonneg
        _ ≤ (pr_step_mass η T)⁻¹ * (2 * R) := by
            gcongr
            linarith
        _ = _ := by field_simp
    have hmatrix_bound : td_euclidean_norm
          (Matrix.mulVec (td_population_matrix M)
            (pr_average η (fun t => td_iterates M η θ0 t path) T - θstar)) ≤
        pr_fast_constant a η δ c τ φinf rinf θ0 θstar /
          pr_step_mass η T := by
      rw [hdecomp]
      calc
        _ ≤ td_euclidean_norm (td_i_one M η θ0 path T +
              td_i_two M η θstar path T) +
            td_euclidean_norm (td_i_three M η θ0 θstar path T) := htri _ _
        _ ≤ td_euclidean_norm (td_i_one M η θ0 path T) +
              td_euclidean_norm (td_i_two M η θstar path T) +
            td_euclidean_norm (td_i_three M η θ0 θstar path T) := by
              gcongr
              exact htri _ _
        _ ≤ 2 * R / pr_step_mass η T +
              ((2 * Real.sqrt (pr_square_mass η) *
                  Real.sqrt (2 * Real.log (8 / δ)) + 3 * η 0) *
                48 * τ * φinf ^ 2 * R) / pr_step_mass η T +
              (256 * τ * φinf ^ 2 * R * Real.sqrt (pr_square_mass η) *
                  Real.sqrt (2 * Real.log (8 / δ)) +
                384 * η 0 * τ * φinf ^ 2 * R +
                192 * τ * φinf ^ 4 * R * pr_square_mass η) /
                  pr_step_mass η T := by gcongr
        _ = _ := by
          rw [show R = pr_rho a δ c * pr_base_radius θ0 θstar rinf φinf by rfl]
          rw [← add_div, ← add_div]
          congr 1
          simpa only [mul_assoc, add_assoc] using
            fast_constant_collection a η δ c τ φinf rinf θ0 θstar
    have hfast_nonneg : 0 ≤ pr_fast_constant a η δ c τ φinf rinf θ0 θstar := by
      have hmatrix_nonneg := hnorm_nonneg
        (Matrix.mulVec (td_population_matrix M)
          (pr_average η (fun t => td_iterates M η θ0 t path) T - θstar))
      have := mul_le_mul_of_nonneg_right hmatrix_bound (le_of_lt hSpos)
      field_simp at this
      nlinarith
    let e := pr_average η (fun t => td_iterates M η θ0 t path) T - θstar
    let z := Matrix.mulVec (td_population_matrix M) e
    let p := td_potential M θstar
        (pr_average η (fun t => td_iterates M η θ0 t path) T) -
      td_potential M θstar θstar
    have hpidentity : p = e ⬝ᵥ z := by
      dsimp [p, e, z]
      exact hpot _
    have hpupper : p ≤ td_euclidean_norm e * td_euclidean_norm z := by
      rw [hpidentity]
      exact hdot _ _
    have hplower : ω * td_euclidean_norm e ^ 2 ≤ p := by
      dsimp [p, e]
      exact hcurv _
    have hzbound : td_euclidean_norm z ≤
        pr_fast_constant a η δ c τ φinf rinf θ0 θstar / pr_step_mass η T := by
      exact hmatrix_bound
    have hbridge : p ≤ td_euclidean_norm z ^ 2 / ω := by
      by_cases hezero : td_euclidean_norm e = 0
      · rw [hezero] at hpupper
        have hright : 0 ≤ td_euclidean_norm z ^ 2 / ω :=
          div_nonneg (sq_nonneg _) (le_of_lt hω)
        linarith
      · have hepos : 0 < td_euclidean_norm e :=
          lt_of_le_of_ne (hnorm_nonneg e) (Ne.symm hezero)
        have hωe : ω * td_euclidean_norm e ≤ td_euclidean_norm z := by
          apply le_of_mul_le_mul_left _ hepos
          calc
            td_euclidean_norm e * (ω * td_euclidean_norm e) =
                ω * td_euclidean_norm e ^ 2 := by ring
            _ ≤ p := hplower
            _ ≤ td_euclidean_norm e * td_euclidean_norm z := hpupper
        apply (le_div_iff₀ hω).mpr
        calc
          p * ω ≤ (td_euclidean_norm e * td_euclidean_norm z) * ω :=
            mul_le_mul_of_nonneg_right hpupper (le_of_lt hω)
          _ = (ω * td_euclidean_norm e) * td_euclidean_norm z := by ring
          _ ≤ td_euclidean_norm z * td_euclidean_norm z :=
            mul_le_mul_of_nonneg_right hωe (hnorm_nonneg z)
          _ = td_euclidean_norm z ^ 2 := by ring
    change p ≤ _
    calc
      _ ≤ td_euclidean_norm z ^ 2 / ω := hbridge
      _ ≤ (pr_fast_constant a η δ c τ φinf rinf θ0 θstar /
          pr_step_mass η T) ^ 2 / ω := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hω)
        simpa only [pow_two] using mul_self_le_mul_self (hnorm_nonneg z) hzbound
      _ = _ := by field_simp

@[blueprint "lem:weighted-square-average-bound"
  (statement := /-- Let $\eta,x\colon\mathbb N\to\mathbb R$ and $T\in\mathbb N$.  If $\eta_t\geq0$ for every $t$, then
  \[
  \left(\sum_{t<T}\eta_tx_t\right)^2
  \leq S_T\sum_{t<T}\eta_tx_t^2.
  \] -/)
  (proof := /-- By \cref{def:pr-step-mass}, $S_T=\sum_{t<T}\eta_t$.  Apply the finite Cauchy--Schwarz inequality to the three sequences $r_t=\eta_tx_t$, $f_t=\eta_t$, and $g_t=\eta_tx_t^2$.  The hypotheses give $f_t,g_t\geq0$, and $r_t^2=f_tg_t$ for every $t<T$, which yields the asserted inequality. -/)
  (title := /-- Weighted square of a finite average -/)
  (latexEnv := "lemma")]
lemma weighted_square_average_bound (η x : ℕ → ℝ) (T : ℕ)
    (hη : ∀ t, 0 ≤ η t) :
    (∑ t ∈ Finset.range T, η t * x t) ^ 2 ≤
      pr_step_mass η T * ∑ t ∈ Finset.range T, η t * (x t) ^ 2 := by
  unfold pr_step_mass
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i hi
    exact hη i
  · intro i hi
    exact mul_nonneg (hη i) (sq_nonneg (x i))
  · intro i hi
    ring_nf
    exact le_rfl

@[blueprint "lem:stationary-dirichlet-quadratic-identity"
  (statement := /-- Let $\pi\colon\operatorname{Fin}(n)\to\mathbb R$ and $P\colon\operatorname{Fin}(n)^2\to\mathbb R$ satisfy $\sum_{s'}P(s,s')=1$ and $\sum_s\pi(s)P(s,s')=\pi(s')$.  Then, for every $\gamma\in\mathbb R$ and $x\colon\operatorname{Fin}(n)\to\mathbb R$,
  \[
  \sum_{s,s'}\pi(s)P(s,s')x(s)(x(s)-\gamma x(s'))
  =(1-\gamma)\sum_s\pi(s)x(s)^2
  +\frac{\gamma}{2}\sum_{s,s'}\pi(s)P(s,s')(x(s)-x(s'))^2.
  \] -/)
  (proof := /-- Expand the square in the Dirichlet term.  The row-mass identity changes the coefficient of $x(s)^2$ into $\pi(s)$, while stationarity changes the coefficient of $x(s')^2$ into $\pi(s')$.  After these two substitutions, both sides consist of the same diagonal term minus the same $\gamma$-weighted cross term. -/)
  (title := /-- Stationary quadratic and Dirichlet identity -/)
  (latexEnv := "lemma")]
lemma stationary_dirichlet_quadratic_identity {n : ℕ}
    (π : Fin n → ℝ) (P : Fin n → Fin n → ℝ) (γ : ℝ) (x : Fin n → ℝ)
    (hrow : ∀ s, ∑ s', P s s' = 1)
    (hstat : ∀ s', ∑ s, π s * P s s' = π s') :
    (∑ s, ∑ s', π s * P s s' * x s * (x s - γ * x s')) =
      (1 - γ) * ∑ s, π s * (x s) ^ 2 +
        γ * (1 / 2 : ℝ) * ∑ s, ∑ s', π s * P s s' * (x s - x s') ^ 2 := by
  have hleft :
      (∑ s, ∑ s', π s * P s s' * (x s) ^ 2) = ∑ s, π s * (x s) ^ 2 := by
    apply Finset.sum_congr rfl
    intro s hs
    calc
      (∑ s', π s * P s s' * (x s) ^ 2) =
          (π s * (x s) ^ 2) * ∑ s', P s s' := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro s' hs'
            ring
      _ = π s * (x s) ^ 2 := by rw [hrow s, mul_one]
  have hright :
      (∑ s, ∑ s', π s * P s s' * (x s') ^ 2) = ∑ s, π s * (x s) ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s' hs'
    calc
      (∑ s, π s * P s s' * (x s') ^ 2) =
          (∑ s, π s * P s s') * (x s') ^ 2 := by rw [Finset.sum_mul]
      _ = π s' * (x s') ^ 2 := by rw [hstat s']
  have hcross :
      (∑ s, ∑ s', π s * P s s' * x s * (γ * x s')) =
        γ * ∑ s, ∑ s', π s * P s s' * x s * x s' := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s' hs'
    ring
  have hmain :
      (∑ s, ∑ s', π s * P s s' * x s * (x s - γ * x s')) =
        (∑ s, π s * (x s) ^ 2) -
          γ * ∑ s, ∑ s', π s * P s s' * x s * x s' := by
    calc
      _ = (∑ s, ∑ s', π s * P s s' * (x s) ^ 2) -
          γ * ∑ s, ∑ s', π s * P s s' * x s * x s' := by
            simp_rw [mul_sub, Finset.sum_sub_distrib]
            rw [hcross]
            congr 1
            apply Finset.sum_congr rfl
            intro s hs
            apply Finset.sum_congr rfl
            intro s' hs'
            ring
      _ = _ := by rw [hleft]
  rw [hmain]
  have hmiddle :
      (∑ s, ∑ s', π s * P s s' * (2 * x s * x s')) =
        2 * ∑ s, ∑ s', π s * P s s' * x s * x s' := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s' hs'
    ring
  simp_rw [sub_sq, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  rw [hleft, hright, hmiddle]
  ring

@[blueprint "lem:fixed-point-drift-potential-identity"
  (statement := /-- Let $M$ be a finite TD model and let $\theta^*$ be a TD fixed point.  For every $\theta\in\mathbb R^d$,
  \[
  \langle\bar g(\theta),\theta^*-\theta\rangle
  =f(\theta)-f(\theta^*).
  \] -/)
  (proof := /-- By \cref{def:td-fixed-point,def:td-mean-update}, the left-hand side is the population quadratic form $(\theta-\theta^*)^\top A(\theta-\theta^*)$.  Expanding $A$ via \cref{def:td-sample-matrix,def:td-population-matrix} expresses this form as the stationary transition average of $x(s)(x(s)-\gamma x(s'))$, where $x(s)=\phi(s)^\top(\theta^*-\theta)$.  Every transition row has mass one and the stationary distribution satisfies the stationarity identity in \cref{def:td-model}; hence \cref{lem:stationary-dirichlet-quadratic-identity} identifies this average with the weighted-square and Dirichlet terms in \cref{def:td-potential}. -/)
  (title := /-- Fixed-point drift equals the TD potential -/)
  (latexEnv := "lemma")]
lemma fixed_point_drift_potential_identity {n d : ℕ} (M : td_model n d)
    (θstar θ : td_vector d) (hfixed : td_fixed_point M θstar) :
    td_mean_update M θ ⬝ᵥ (θstar - θ) =
      td_potential M θstar θ - td_potential M θstar θstar := by
  let y : td_vector d := θstar - θ
  let x : Fin n → ℝ := fun s => M.feature s ⬝ᵥ y
  have hrow (s : Fin n) : ∑ s', ((M.transition s) s').toReal = 1 := by
    rw [← ENNReal.toReal_sum]
    · have hmass : ∑ s', (M.transition s) s' = 1 := by
        simpa only [tsum_fintype] using (PMF.hasSum_coe_one (M.transition s)).tsum_eq
      rw [hmass]
      norm_num
    · intro s' hs'
      exact PMF.apply_ne_top (M.transition s) s'
  have hmean : td_mean_update M θ = Matrix.mulVec (td_population_matrix M) y := by
    unfold td_mean_update
    rw [← hfixed]
    dsimp [y]
    rw [Matrix.mulVec_sub]
  have hmul (i : Fin d) :
      Matrix.mulVec (td_population_matrix M) y i =
        ∑ s, ∑ s', (M.stationary s).toReal * ((M.transition s) s').toReal *
          M.feature s i * (x s - M.discount * x s') := by
    unfold td_population_matrix td_sample_matrix Matrix.mulVec
    calc
      (∑ j, (∑ s, ∑ s', (M.stationary s).toReal *
          ((M.transition s) s').toReal *
          (M.feature s i * (M.feature s j - M.discount * M.feature s' j))) * y j) =
          ∑ j, ∑ s, ∑ s', (M.stationary s).toReal *
            ((M.transition s) s').toReal *
            (M.feature s i * (M.feature s j - M.discount * M.feature s' j)) * y j := by
              simp_rw [Finset.sum_mul]
      _ = ∑ s, ∑ s', ∑ j, (M.stationary s).toReal *
          ((M.transition s) s').toReal *
          (M.feature s i * (M.feature s j - M.discount * M.feature s' j)) * y j := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro s hs
            rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s hs
        apply Finset.sum_congr rfl
        intro s' hs'
        dsimp [x]
        unfold dotProduct
        rw [mul_sub]
        simp_rw [Finset.mul_sum]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hlhs :
      td_mean_update M θ ⬝ᵥ (θstar - θ) =
        ∑ s, ∑ s', (M.stationary s).toReal * ((M.transition s) s').toReal *
          x s * (x s - M.discount * x s') := by
    rw [hmean]
    change Matrix.mulVec (td_population_matrix M) y ⬝ᵥ y = _
    unfold dotProduct
    simp_rw [hmul]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s' hs'
    dsimp [x]
    unfold dotProduct
    calc
      (∑ i, (M.stationary s).toReal * ((M.transition s) s').toReal *
          M.feature s i *
          (∑ j, M.feature s j * y j - M.discount * ∑ j, M.feature s' j * y j) * y i) =
          ∑ i, ((M.stationary s).toReal * ((M.transition s) s').toReal *
            (∑ j, M.feature s j * y j - M.discount * ∑ j, M.feature s' j * y j)) *
            (M.feature s i * y i) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = ((M.stationary s).toReal * ((M.transition s) s').toReal *
            (∑ j, M.feature s j * y j - M.discount * ∑ j, M.feature s' j * y j)) *
          ∑ i, M.feature s i * y i := by rw [← Finset.mul_sum]
      _ = _ := by ring
  have hvalue (s : Fin n) :
      td_value M θ s - td_value M θstar s = -x s := by
    unfold td_value
    dsimp [x, y]
    unfold dotProduct
    simp_rw [Pi.sub_apply, mul_sub]
    rw [Finset.sum_sub_distrib]
    ring
  have hquad := stationary_dirichlet_quadratic_identity
    (fun s => (M.stationary s).toReal)
    (fun s s' => ((M.transition s) s').toReal) M.discount x hrow M.stationary_eq
  calc
    td_mean_update M θ ⬝ᵥ (θstar - θ) =
        ∑ s, ∑ s', (M.stationary s).toReal * ((M.transition s) s').toReal *
          x s * (x s - M.discount * x s') := hlhs
    _ = (1 - M.discount) * ∑ s, (M.stationary s).toReal * (x s) ^ 2 +
        M.discount * (1 / 2 : ℝ) *
          ∑ s, ∑ s', (M.stationary s).toReal * ((M.transition s) s').toReal *
            (x s - x s') ^ 2 := hquad
    _ = td_potential M θstar θ - td_potential M θstar θstar := by
      unfold td_potential td_weighted_square td_dirichlet_energy
      simp only [Pi.sub_apply]
      simp_rw [hvalue]
      simp
      ring_nf

@[blueprint "lem:td-potential-weighted-average-bound"
  (statement := /-- Let $M$ be a finite TD model, let $\theta^*\in\mathbb R^d$, let $\eta_t>0$ for every $t$, and let $(\theta_t)_{t\geq0}$ be any sequence in $\mathbb R^d$.  For every $T\geq1$,
  \[
  S_T\bigl(f(\bar\theta_T)-f(\theta^*)\bigr)
  \leq\sum_{t<T}\eta_t\bigl(f(\theta_t)-f(\theta^*)\bigr).
  \] -/)
  (proof := /-- Positivity of the weights and $T\geq1$ give $S_T>0$ by \cref{def:pr-step-mass}.  For every state coordinate and every state-pair difference, \cref{lem:weighted-square-average-bound} bounds the square at the weighted average by the corresponding weighted sum of squares.  Multiply these inequalities by the nonnegative stationary, transition, and discount coefficients and sum them according to \cref{def:td-potential,def:td-value,def:td-weighted-square,def:td-dirichlet-energy}.  The definition of the average in \cref{def:pr-average} then gives the displayed inequality. -/)
  (title := /-- TD potential at a weighted average -/)
  (latexEnv := "lemma")]
lemma td_potential_weighted_average_bound {n d : ℕ} (M : td_model n d)
    (η : ℕ → ℝ) (θ : ℕ → td_vector d) (θstar : td_vector d) (T : ℕ)
    (hη : ∀ t, 0 < η t) (hT : 1 ≤ T) :
    pr_step_mass η T *
        (td_potential M θstar (pr_average η θ T) - td_potential M θstar θstar) ≤
      ∑ t ∈ Finset.range T,
        η t * (td_potential M θstar (θ t) - td_potential M θstar θstar) := by
  have hSpos : 0 < pr_step_mass η T := by
    unfold pr_step_mass
    apply Finset.sum_pos
    · intro i hi
      exact hη i
    · exact Finset.nonempty_range_iff.mpr (by omega)
  have hηnonneg : ∀ t, 0 ≤ η t := fun t => (hη t).le
  have hscalar (z : ℕ → ℝ) :
      pr_step_mass η T *
          ((pr_step_mass η T)⁻¹ * ∑ t ∈ Finset.range T, η t * z t) ^ 2 ≤
        ∑ t ∈ Finset.range T, η t * (z t) ^ 2 := by
    have hcauchy := weighted_square_average_bound η z T hηnonneg
    calc
      pr_step_mass η T *
          ((pr_step_mass η T)⁻¹ * ∑ t ∈ Finset.range T, η t * z t) ^ 2 =
          (∑ t ∈ Finset.range T, η t * z t) ^ 2 / pr_step_mass η T := by
            field_simp [hSpos.ne']
      _ ≤ ∑ t ∈ Finset.range T, η t * (z t) ^ 2 := by
        apply (div_le_iff₀ hSpos).2
        simpa [mul_comm] using hcauchy
  have havg :
      pr_average η θ T - θstar =
        (pr_step_mass η T)⁻¹ • ∑ t ∈ Finset.range T,
          η t • (θ t - θstar) := by
    unfold pr_average
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
    change
      (pr_step_mass η T)⁻¹ • (∑ t ∈ Finset.range T, η t • θ t) - θstar =
        (pr_step_mass η T)⁻¹ •
          ((∑ t ∈ Finset.range T, η t • θ t) - pr_step_mass η T • θstar)
    ext i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp [hSpos.ne']
  have hvalue (s : Fin n) :
      td_value M (pr_average η θ T) s - td_value M θstar s =
        (pr_step_mass η T)⁻¹ * ∑ t ∈ Finset.range T,
          η t * (td_value M (θ t) s - td_value M θstar s) := by
    unfold td_value
    rw [← dotProduct_sub]
    rw [havg]
    simp only [dotProduct_smul, dotProduct_sum, smul_eq_mul, dotProduct_sub]
  have hstate (s : Fin n) :
      pr_step_mass η T *
          (td_value M (pr_average η θ T) s - td_value M θstar s) ^ 2 ≤
        ∑ t ∈ Finset.range T,
          η t * (td_value M (θ t) s - td_value M θstar s) ^ 2 := by
    rw [hvalue]
    exact hscalar (fun t => td_value M (θ t) s - td_value M θstar s)
  have hpair (s s' : Fin n) :
      pr_step_mass η T *
          ((td_value M (pr_average η θ T) s - td_value M θstar s) -
            (td_value M (pr_average η θ T) s' - td_value M θstar s')) ^ 2 ≤
        ∑ t ∈ Finset.range T, η t *
          ((td_value M (θ t) s - td_value M θstar s) -
            (td_value M (θ t) s' - td_value M θstar s')) ^ 2 := by
    rw [hvalue s, hvalue s']
    have hsums :
        (∑ t ∈ Finset.range T, η t * (td_value M (θ t) s - td_value M θstar s)) -
            ∑ t ∈ Finset.range T, η t * (td_value M (θ t) s' - td_value M θstar s') =
          ∑ t ∈ Finset.range T, η t *
            ((td_value M (θ t) s - td_value M θstar s) -
              (td_value M (θ t) s' - td_value M θstar s')) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    rw [← mul_sub, hsums]
    exact hscalar (fun t =>
      (td_value M (θ t) s - td_value M θstar s) -
        (td_value M (θ t) s' - td_value M θstar s'))
  have hQ :
      pr_step_mass η T *
          ∑ s, (M.stationary s).toReal *
            (td_value M (pr_average η θ T) s - td_value M θstar s) ^ 2 ≤
        ∑ t ∈ Finset.range T, η t *
          ∑ s, (M.stationary s).toReal *
            (td_value M (θ t) s - td_value M θstar s) ^ 2 := by
    calc
      pr_step_mass η T *
          ∑ s, (M.stationary s).toReal *
            (td_value M (pr_average η θ T) s - td_value M θstar s) ^ 2 =
          ∑ s, (M.stationary s).toReal *
            (pr_step_mass η T *
              (td_value M (pr_average η θ T) s - td_value M θstar s) ^ 2) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro s hs
                ring
      _ ≤ ∑ s, (M.stationary s).toReal *
          (∑ t ∈ Finset.range T,
            η t * (td_value M (θ t) s - td_value M θstar s) ^ 2) := by
              gcongr with s
              exact hstate s
      _ = ∑ t ∈ Finset.range T, η t *
          ∑ s, (M.stationary s).toReal *
            (td_value M (θ t) s - td_value M θstar s) ^ 2 := by
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro t ht
              apply Finset.sum_congr rfl
              intro s hs
              ring
  have hD :
      pr_step_mass η T *
          ∑ s, ∑ s', (M.stationary s).toReal * ((M.transition s) s').toReal *
            ((td_value M (pr_average η θ T) s - td_value M θstar s) -
              (td_value M (pr_average η θ T) s' - td_value M θstar s')) ^ 2 ≤
        ∑ t ∈ Finset.range T, η t *
          ∑ s, ∑ s', (M.stationary s).toReal * ((M.transition s) s').toReal *
            ((td_value M (θ t) s - td_value M θstar s) -
              (td_value M (θ t) s' - td_value M θstar s')) ^ 2 := by
    calc
      pr_step_mass η T *
          ∑ s, ∑ s', (M.stationary s).toReal * ((M.transition s) s').toReal *
            ((td_value M (pr_average η θ T) s - td_value M θstar s) -
              (td_value M (pr_average η θ T) s' - td_value M θstar s')) ^ 2 =
          ∑ s, ∑ s', (M.stationary s).toReal * ((M.transition s) s').toReal *
            (pr_step_mass η T *
              ((td_value M (pr_average η θ T) s - td_value M θstar s) -
                (td_value M (pr_average η θ T) s' - td_value M θstar s')) ^ 2) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro s hs
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro s' hs'
                  ring
      _ ≤ ∑ s, ∑ s', (M.stationary s).toReal * ((M.transition s) s').toReal *
          (∑ t ∈ Finset.range T, η t *
            ((td_value M (θ t) s - td_value M θstar s) -
              (td_value M (θ t) s' - td_value M θstar s')) ^ 2) := by
              gcongr with s s'
              exact hpair s s'
      _ = ∑ t ∈ Finset.range T, η t *
          ∑ s, ∑ s', (M.stationary s).toReal * ((M.transition s) s').toReal *
            ((td_value M (θ t) s - td_value M θstar s) -
              (td_value M (θ t) s' - td_value M θstar s')) ^ 2 := by
                simp_rw [Finset.mul_sum]
                calc
                  _ = ∑ s, ∑ t ∈ Finset.range T, ∑ s',
                      (M.stationary s).toReal * ((M.transition s) s').toReal *
                        (η t *
                          ((td_value M (θ t) s - td_value M θstar s) -
                            (td_value M (θ t) s' - td_value M θstar s')) ^ 2) := by
                            apply Finset.sum_congr rfl
                            intro s hs
                            rw [Finset.sum_comm]
                  _ = ∑ t ∈ Finset.range T, ∑ s, ∑ s',
                      (M.stationary s).toReal * ((M.transition s) s').toReal *
                        (η t *
                          ((td_value M (θ t) s - td_value M θstar s) -
                            (td_value M (θ t) s' - td_value M θstar s')) ^ 2) := by
                            rw [Finset.sum_comm]
                  _ = _ := by
                    apply Finset.sum_congr rfl
                    intro t ht
                    apply Finset.sum_congr rfl
                    intro s hs
                    apply Finset.sum_congr rfl
                    intro s' hs'
                    ring
  have hQscaled := mul_le_mul_of_nonneg_left hQ (sub_nonneg.mpr M.discount_lt_one.le)
  have hDscaled := mul_le_mul_of_nonneg_left hD
    (mul_nonneg M.discount_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2))
  unfold td_potential td_weighted_square td_dirichlet_energy
  simp only [Pi.sub_apply, sub_self, zero_pow, mul_zero, Finset.sum_const_zero,
    add_zero, sub_zero]
  norm_num
  calc
    pr_step_mass η T *
        ((1 - M.discount) *
            ∑ s, (M.stationary s).toReal *
              (td_value M (pr_average η θ T) s - td_value M θstar s) ^ 2 +
          M.discount * ((1 / 2 : ℝ) *
            ∑ s, ∑ s', (M.stationary s).toReal * ((M.transition s) s').toReal *
              ((td_value M (pr_average η θ T) s - td_value M θstar s) -
                (td_value M (pr_average η θ T) s' - td_value M θstar s')) ^ 2)) =
        (1 - M.discount) * (pr_step_mass η T *
            ∑ s, (M.stationary s).toReal *
              (td_value M (pr_average η θ T) s - td_value M θstar s) ^ 2) +
          (M.discount * (1 / 2 : ℝ)) * (pr_step_mass η T *
            ∑ s, ∑ s', (M.stationary s).toReal * ((M.transition s) s').toReal *
              ((td_value M (pr_average η θ T) s - td_value M θstar s) -
                (td_value M (pr_average η θ T) s' - td_value M θstar s')) ^ 2) := by ring
    _ ≤ (1 - M.discount) *
          (∑ t ∈ Finset.range T, η t *
            ∑ s, (M.stationary s).toReal *
              (td_value M (θ t) s - td_value M θstar s) ^ 2) +
        (M.discount * (1 / 2 : ℝ)) *
          (∑ t ∈ Finset.range T, η t *
            ∑ s, ∑ s', (M.stationary s).toReal * ((M.transition s) s').toReal *
              ((td_value M (θ t) s - td_value M θstar s) -
                (td_value M (θ t) s' - td_value M θstar s')) ^ 2) :=
      add_le_add hQscaled hDscaled
    _ = ∑ t ∈ Finset.range T, η t *
        ((1 - M.discount) *
            ∑ s, (M.stationary s).toReal *
              (td_value M (θ t) s - td_value M θstar s) ^ 2 +
          M.discount * ((1 / 2 : ℝ) *
            ∑ s, ∑ s', (M.stationary s).toReal * ((M.transition s) s').toReal *
              ((td_value M (θ t) s - td_value M θstar s) -
                (td_value M (θ t) s' - td_value M θstar s')) ^ 2)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      ring

@[blueprint "lem:pr-rho-square-ge-one-or-nonpositive"
  (statement := /-- For every sequence $a\colon\mathbb N\to\mathbb R$ and every $\delta,c\in\mathbb R$, the multiplier $\rho$ from \cref{def:pr-rho} satisfies $\rho^2\geq1$ or $\rho\leq0$. -/)
  (proof := /-- The coefficients $A_1$ and $A_2$ from \cref{def:pr-a-one,def:pr-a-two} are nonnegative.  Write $D=c^2-A_1c-A_2$.  If $D\leq0$, then $\sqrt D=0$ and hence $\rho=0$.  If $D>0$ and $c\leq0$, then $\rho\leq0$.  Finally, if $D>0$ and $c>0$, nonnegativity of $A_1c+A_2$ gives $\sqrt D\leq c$, so \cref{def:pr-rho} yields $\rho=2c/\sqrt D\geq2$ and therefore $\rho^2\geq1$. -/)
  (title := /-- Unconditional dichotomy for the bootstrap multiplier -/)
  (latexEnv := "lemma")]
lemma pr_rho_square_ge_one_or_nonpositive (a : ℕ → ℝ) (δ c : ℝ) :
    1 ≤ (pr_rho a δ c) ^ 2 ∨ pr_rho a δ c ≤ 0 := by
  have hA1 : 0 ≤ pr_a_one a δ := by
    unfold pr_a_one
    positivity
  have hA2 : 0 ≤ pr_a_two a := by
    unfold pr_a_two
    positivity
  let D := c ^ 2 - pr_a_one a δ * c - pr_a_two a
  by_cases hD : 0 < D
  · have hsqrt : 0 < Real.sqrt D := Real.sqrt_pos.2 hD
    by_cases hc : 0 < c
    · left
      have hDle : D ≤ c ^ 2 := by
        dsimp [D]
        nlinarith [mul_nonneg hA1 hc.le]
      have hsqrtle : Real.sqrt D ≤ c := by
        have hsqrt_sq := Real.sq_sqrt hD.le
        nlinarith [Real.sqrt_nonneg D]
      change 1 ≤ (2 * c / Real.sqrt D) ^ 2
      have hrho : 2 ≤ 2 * c / Real.sqrt D := by
        apply (le_div_iff₀ hsqrt).2
        nlinarith
      nlinarith [sq_nonneg (2 * c / Real.sqrt D)]
    · right
      have hc_nonpos : c ≤ 0 := le_of_not_gt hc
      change 2 * c / Real.sqrt D ≤ 0
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (Real.sqrt_nonneg D)
  · right
    have hD_nonpos : D ≤ 0 := le_of_not_gt hD
    change 2 * c / Real.sqrt D ≤ 0
    rw [Real.sqrt_eq_zero_of_nonpos hD_nonpos, div_zero]

@[blueprint "lem:td-euclidean-norm-eq-zero"
  (statement := /-- If $v\in\mathbb R^d$ satisfies $\lVert v\rVert_2=0$ for the Euclidean norm of \cref{def:td-euclidean-norm}, then $v=0$. -/)
  (proof := /-- The squared coordinates are nonnegative and their sum is nonnegative.  The vanishing square root therefore forces that sum to be zero, so every squared coordinate and hence every coordinate is zero. -/)
  (title := /-- Vanishing TD Euclidean norm -/)
  (latexEnv := "lemma")]
lemma td_euclidean_norm_eq_zero {d : ℕ} (v : td_vector d)
    (h : td_euclidean_norm v = 0) : v = 0 := by
  unfold td_euclidean_norm at h
  have hsum_nonneg : 0 ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg fun i hi => sq_nonneg (v i)
  have hsum : ∑ i, (v i) ^ 2 = 0 := by
    have := (Real.sqrt_eq_zero').mp h
    linarith
  ext i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j hj => sq_nonneg (v j))).mp hsum i (Finset.mem_univ i)
  change v i = 0
  nlinarith

@[blueprint "lem:robust-rate-on-analysis-event"
  (statement := /-- Let $n,d\in\mathbb N$, let $M$ be a finite TD model on $n$ states with parameter space $\mathbb R^d$, let $a,\eta\colon\mathbb N\to\mathbb R$, and let $\delta,c,\tau,\phi_\infty,r_\infty\in\mathbb R$.  Fix $\theta_0,\theta^*\in\mathbb R^d$ and a path $(s_t)_{t\geq0}$ in $\operatorname{Fin}(n)$.  Suppose that $\eta_t>0$ for every $t$, that $\theta^*$ is a TD fixed point of $M$, and that the path belongs to the common event $\mathcal E(M,a,\eta,\delta,c,\tau,\phi_\infty,r_\infty,\theta_0,\theta^*)$.  Then, for every $T\geq1$,
  \[
  f(\bar\theta_T)-f(\theta^*)\leq\frac{C_{\mathrm{robust}}}{S_T}.
  \] -/)
  (proof := /-- Positivity of the stepsizes and $T\geq1$ imply $S_T>0$ by \cref{def:pr-step-mass}.  Membership in \cref{def:analysis-event} supplies the bounded-iterate condition and the energy estimate.  By \cref{lem:fixed-point-drift-potential-identity}, expanding \cref{def:td-recursion-remainder} gives
  \[
  2\sum_{t<T}\eta_t
  \bigl(f(\theta_t)-f(\theta^*)\bigr)
  =\|\theta_0-\theta^*\|_2^2-\|\theta_T-\theta^*\|_2^2
  +\sum_{t<T}\eta_t^2\|g(\theta_t,Z_t)\|_2^2+B_T.
  \]
  It remains to control the difference of the endpoint squared norms without assuming $c>c_{\min}$.  By \cref{lem:pr-rho-square-ge-one-or-nonpositive}, either $\rho^2\geq1$ or $\rho\leq0$.  In the first case, \cref{def:pr-base-radius} and nonnegativity of the terminal squared norm give
  $\|\theta_0-\theta^*\|_2^2-\|\theta_T-\theta^*\|_2^2\leq\rho^2R_{\mathrm{base}}^2$.
  In the second case, the bounded-iterate condition forces $\rho R_{\mathrm{base}}=0$.  If $\rho<0$, then $R_{\mathrm{base}}=0$ and the same bound follows.  If $\rho=0$, every iterate has zero Euclidean norm and therefore vanishes by \cref{lem:td-euclidean-norm-eq-zero}; the two endpoint squared norms are then equal.  Thus the endpoint bound holds in every case.

  Adding the energy estimate and collecting coefficients according to \cref{def:pr-robust-constant} shows
  $\sum_{t<T}\eta_t(f(\theta_t)-f(\theta^*))\leq C_{\mathrm{robust}}$.
  Finally, \cref{lem:td-potential-weighted-average-bound} and \cref{def:pr-average} give
  $S_T(f(\bar\theta_T)-f(\theta^*))\leq\sum_{t<T}\eta_t(f(\theta_t)-f(\theta^*))$.
  Division by the positive number $S_T$ proves the displayed inequality. -/)
  (title := /-- Robust rate on the common event -/)
  (latexEnv := "lemma")]
lemma robust_rate_on_analysis_event {n d : ℕ} (M : td_model n d) (a η : ℕ → ℝ)
    (δ c τ φinf rinf : ℝ) (θ0 θstar : td_vector d) (path : ℕ → Fin n)
    (hηpos : ∀ t, 0 < η t) (hfixed : td_fixed_point M θstar)
    (hpath : path ∈ analysis_event M a η δ c τ φinf rinf θ0 θstar) :
    ∀ T, 1 ≤ T →
      td_potential M θstar (pr_average η (fun t => td_iterates M η θ0 t path) T) -
          td_potential M θstar θstar ≤
        pr_robust_constant a η δ c τ φinf rinf θ0 θstar /
          pr_step_mass η T := by
  intro T hT
  have hSpos : 0 < pr_step_mass η T := by
    unfold pr_step_mass
    apply Finset.sum_pos
    · intro i hi
      exact hηpos i
    · exact Finset.nonempty_range_iff.mpr (by omega)
  let ρ := pr_rho a δ c
  let R := pr_base_radius θ0 θstar rinf φinf
  let Ebound :=
    768 * τ * φinf ^ 2 * (ρ * R) ^ 2 *
        Real.sqrt (pr_square_mass η) * Real.sqrt (2 * Real.log (8 / δ)) +
      1152 * η 0 * τ * φinf ^ 2 * (ρ * R) ^ 2 +
      1344 * τ * φinf ^ 4 * (ρ * R) ^ 2 * pr_square_mass η +
      9 * φinf ^ 4 * (ρ * R) ^ 2 * pr_square_mass η
  have henergy := hpath.2 hpath.1.1.1 T hT
  change
    (∑ t ∈ Finset.range T, (η t) ^ 2 *
        (td_euclidean_norm (td_update M (td_iterates M η θ0 t path)
          (path t) (path (t + 1)))) ^ 2) +
      td_recursion_remainder M η θ0 θstar path T ≤ Ebound at henergy
  have hdrift (t : ℕ) :
      td_mean_update M (td_iterates M η θ0 t path) ⬝ᵥ
          (td_iterates M η θ0 t path - θstar) =
        -(td_potential M θstar (td_iterates M η θ0 t path) -
          td_potential M θstar θstar) := by
    rw [show td_iterates M η θ0 t path - θstar =
      -(θstar - td_iterates M η θ0 t path) by abel]
    simp only [dotProduct_neg, neg_inj]
    exact fixed_point_drift_potential_identity M θstar
      (td_iterates M η θ0 t path) hfixed
  have hsum :
      (∑ t ∈ Finset.range T,
          η t * -(td_potential M θstar (td_iterates M η θ0 t path) -
            td_potential M θstar θstar)) =
        -(∑ t ∈ Finset.range T, η t *
          (td_potential M θstar (td_iterates M η θ0 t path) -
            td_potential M θstar θstar)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  have hrec :
      2 * ∑ t ∈ Finset.range T, η t *
          (td_potential M θstar (td_iterates M η θ0 t path) -
            td_potential M θstar θstar) =
        (td_euclidean_norm (θ0 - θstar)) ^ 2 -
          (td_euclidean_norm (td_iterates M η θ0 T path - θstar)) ^ 2 +
          ((∑ t ∈ Finset.range T, (η t) ^ 2 *
              (td_euclidean_norm (td_update M (td_iterates M η θ0 t path)
                (path t) (path (t + 1)))) ^ 2) +
            td_recursion_remainder M η θ0 θstar path T) := by
    unfold td_recursion_remainder
    simp_rw [hdrift]
    rw [hsum]
    ring
  have hC :
      ρ ^ 2 * R ^ 2 + Ebound =
        2 * pr_robust_constant a η δ c τ φinf rinf θ0 θstar := by
    dsimp [ρ, R, Ebound]
    unfold pr_robust_constant
    ring
  have hnorm (v : td_vector d) : 0 ≤ td_euclidean_norm v := by
    unfold td_euclidean_norm
    exact Real.sqrt_nonneg _
  have hRnonneg : 0 ≤ R := by
    dsimp [R, pr_base_radius]
    exact le_trans (hnorm (θ0 - θstar)) (le_max_left _ _)
  have hbase : td_euclidean_norm (θ0 - θstar) ≤ R := by
    dsimp [R, pr_base_radius]
    exact le_max_left _ _
  have hρcases := pr_rho_square_ge_one_or_nonpositive a δ c
  change 1 ≤ ρ ^ 2 ∨ ρ ≤ 0 at hρcases
  have hinitial_terminal :
      (td_euclidean_norm (θ0 - θstar)) ^ 2 -
          (td_euclidean_norm (td_iterates M η θ0 T path - θstar)) ^ 2 ≤
        ρ ^ 2 * R ^ 2 := by
    rcases hρcases with hρsq | hρnonpos
    · have he0sq : (td_euclidean_norm (θ0 - θstar)) ^ 2 ≤ R ^ 2 := by
        nlinarith [hnorm (θ0 - θstar), sq_nonneg (R - td_euclidean_norm (θ0 - θstar))]
      have hRsq : R ^ 2 ≤ ρ ^ 2 * R ^ 2 := by
        simpa using mul_le_mul_of_nonneg_right hρsq (sq_nonneg R)
      calc
        (td_euclidean_norm (θ0 - θstar)) ^ 2 -
            (td_euclidean_norm (td_iterates M η θ0 T path - θstar)) ^ 2 ≤
          (td_euclidean_norm (θ0 - θstar)) ^ 2 :=
            sub_le_self _ (sq_nonneg _)
        _ ≤ R ^ 2 := he0sq
        _ ≤ ρ ^ 2 * R ^ 2 := hRsq
    · have hbounded0 := hpath.1.1.1 0
      change td_euclidean_norm θ0 ≤ ρ * R at hbounded0
      have hprod_nonpos : ρ * R ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hρnonpos hRnonneg
      have hprod : ρ * R = 0 := by
        nlinarith [hnorm θ0]
      by_cases hρzero : ρ = 0
      · have hiter_norm (t : ℕ) : td_euclidean_norm (td_iterates M η θ0 t path) = 0 := by
          have hb := hpath.1.1.1 t
          change td_euclidean_norm (td_iterates M η θ0 t path) ≤ ρ * R at hb
          rw [hprod] at hb
          nlinarith [hnorm (td_iterates M η θ0 t path)]
        have hiter_zero (t : ℕ) : td_iterates M η θ0 t path = 0 :=
          td_euclidean_norm_eq_zero _ (hiter_norm t)
        have hθ0 : θ0 = 0 := by simpa [td_iterates] using hiter_zero 0
        rw [hiter_zero T, hθ0, hρzero]
        simp
      · have hRzero : R = 0 := (mul_eq_zero.mp hprod).resolve_left hρzero
        have he0zero : td_euclidean_norm (θ0 - θstar) = 0 := by
          rw [hRzero] at hbase
          nlinarith [hnorm (θ0 - θstar)]
        rw [hRzero, he0zero]
        simp only [pow_two, mul_zero, zero_mul, zero_sub]
        exact neg_nonpos.mpr (mul_self_nonneg _)
  have hpotential_sum :
      ∑ t ∈ Finset.range T, η t *
          (td_potential M θstar (td_iterates M η θ0 t path) -
            td_potential M θstar θstar) ≤
        pr_robust_constant a η δ c τ φinf rinf θ0 θstar := by
    nlinarith [hrec, henergy, hinitial_terminal, hC]
  have havg := td_potential_weighted_average_bound M η
    (fun t => td_iterates M η θ0 t path) θstar T hηpos hT
  apply (le_div_iff₀ hSpos).2
  exact le_trans (by simpa [mul_comm] using havg) hpotential_sum

@[blueprint "thm:pr-main"
  (statement := /-- Let $n,d\in\mathbb N$, let $M$ be a finite TD model on
  $\operatorname{Fin}(n)$ with parameter space $\mathbb R^d$ as in
  \cref{def:td-model}, and let $a,\eta\colon\mathbb N\to\mathbb R$.  Fix
  $\delta,c,\tau,\phi_\infty,r_\infty,\omega\in\mathbb R$, vectors
  $\theta_0,\theta^*\in\mathbb R^d$, and an initial state
  $s_0\in\operatorname{Fin}(n)$.  Assume that $a$ satisfies
  \cref{def:admissible-stepsize-shape}, that
  $\eta_t=(c\tau\phi_\infty^2)^{-1}a_t$ for every $t\in\mathbb N$, that
  $0<\delta<1$, and that $c>c_{\min}(a,\delta)$.  Assume also that $M$
  satisfies \cref{def:td-uniform-bounds,def:td-geometric-mixing} with the
  displayed constants, that $\theta^*$ is the unique TD fixed point of $M$,
  and that \cref{def:td-curvature} holds with constant $\omega$.  Then the
  canonical Markov path measure started at $s_0$ assigns probability at least
  $1-\delta$ to the event on which, simultaneously for every
  $T\in\mathbb N$ with $T\geq1$,
  \[
  f(\bar\theta_T)-f(\theta^*)\leq
  \min\left\{\frac{C_{\mathrm{fast}}^2}{\omega S_T^2},
  \frac{C_{\mathrm{robust}}}{S_T}\right\},
  \]
  where $S_T$, $\bar\theta_T$, $c_{\min}$, $C_{\mathrm{fast}}$, and
  $C_{\mathrm{robust}}$ are those of
  \cref{def:pr-step-mass,def:pr-average,def:pr-c-min,def:pr-fast-constant,def:pr-robust-constant}. -/)
  (proof := /-- The hypotheses in \cref{def:admissible-stepsize-shape,def:pr-eta-base,def:td-uniform-bounds,def:td-geometric-mixing}, together with $c>c_{\min}(\delta)$, imply $\eta_t>0$ for every $t$.  By \cref{lem:analysis-event-probability}, the common event $\mathcal E$ has probability at least $1-\delta$.  On $\mathcal E$, \cref{lem:fast-rate-on-analysis-event} supplies the fast inequality for every $T\geq1$, while \cref{lem:robust-rate-on-analysis-event} supplies the robust inequality for every such $T$, using the positivity just established.  Hence $\mathcal E$ is contained in the target rate event, and monotonicity of the path measure proves the claim. -/)
  (title := /-- High-probability rate for Polyak--Ruppert averaging -/)
  (latexEnv := "theorem")]
theorem pr_main {n d : ℕ} (M : td_model n d) (a η : ℕ → ℝ)
    (δ c τ φinf rinf ω : ℝ) (θ0 θstar : td_vector d) (s0 : Fin n)
    (ha : admissible_stepsize_shape a)
    (hη : ∀ t, η t = pr_eta_base c τ φinf * a t)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hc : pr_c_min a δ < c)
    (hbounds : td_uniform_bounds M φinf rinf)
    (hmix : td_geometric_mixing M τ)
    (hfixed : td_fixed_point M θstar)
    (hfixed_unique : ∀ θ, td_fixed_point M θ → θ = θstar)
    (hcurv : td_curvature M θstar ω) :
    (td_markov_path_measure M s0).real
        (pr_rate_event M a η δ c τ φinf rinf ω θ0 θstar) ≥ 1 - δ := by
  letI : MeasureTheory.IsProbabilityMeasure (td_markov_path_measure M s0) := by
    dsimp [td_markov_path_measure]
    infer_instance
  have hφ : 0 < φinf := hbounds.1
  have hτ : 1 ≤ τ := hmix.1
  have hcpos : 0 < c := by
    have hA : 0 < pr_a_one a δ := by rw [pr_a_one]; positivity
    have hA2 : 0 ≤ pr_a_two a := by rw [pr_a_two]; positivity
    have hs := Real.sqrt_nonneg ((pr_a_one a δ) ^ 2 + 4 * pr_a_two a)
    rw [pr_c_min] at hc
    nlinarith
  have hbase : 0 < pr_eta_base c τ φinf := by
    rw [pr_eta_base]
    positivity
  have hηpos : ∀ t, 0 < η t := by
    intro t
    rw [hη t]
    exact mul_pos hbase (ha.1 t)
  have hsubset :
      analysis_event M a η δ c τ φinf rinf θ0 θstar ⊆
        pr_rate_event M a η δ c τ φinf rinf ω θ0 θstar := by
    intro path hpath T hT
    exact le_min
      (fast_rate_on_analysis_event M a η δ c τ φinf rinf ω θ0 θstar path
        hηpos hfixed hcurv hpath T hT)
      (robust_rate_on_analysis_event M a η δ c τ φinf rinf θ0 θstar path
        hηpos hfixed hpath T hT)
  calc
    1 - δ ≤ (td_markov_path_measure M s0).real
        (analysis_event M a η δ c τ φinf rinf θ0 θstar) :=
      analysis_event_probability M a η δ c τ φinf rinf θ0 θstar s0
        ha hη hδ0 hδ1 hc hbounds hmix hfixed
    _ ≤ (td_markov_path_measure M s0).real
        (pr_rate_event M a η δ c τ φinf rinf ω θ0 θstar) :=
      MeasureTheory.measureReal_mono hsubset

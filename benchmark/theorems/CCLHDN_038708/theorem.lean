import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Sequences

set_option linter.all false
set_option maxHeartbeats 500000

open Filter
open scoped BigOperators

abbrev cl_parameter_space (p : ℕ) := EuclideanSpace ℝ (Fin p)

structure cl_task (Input : Type*) where
  sampleCount : ℕ
  feature : Fin (sampleCount + 1) → Input
  label : Fin (sampleCount + 1) → ℝ
  label_is_sign : ∀ i, label i = -1 ∨ label i = 1

def is_r_positively_homogeneous {Input : Type*} {p : ℕ} (r : ℝ)
    (model : Input → cl_parameter_space p → ℝ) : Prop :=
  ∀ x θ c, 0 < c → model x (c • θ) = c ^ r * model x θ

def signed_margin {Input : Type*} {p : ℕ} (model : Input → cl_parameter_space p → ℝ)
    (task : cl_task Input) (θ : cl_parameter_space p) (i : Fin (task.sampleCount + 1)) : ℝ :=
  task.label i * model (task.feature i) θ

def task_feasible_set {Input : Type*} {p : ℕ}
    (model : Input → cl_parameter_space p → ℝ) (task : cl_task Input) :
    Set (cl_parameter_space p) :=
  {θ | ∀ i, 1 ≤ signed_margin model task θ i}

noncomputable def task_logistic_loss {Input : Type*} {p : ℕ}
    (model : Input → cl_parameter_space p → ℝ) (task : cl_task Input)
    (θ : cl_parameter_space p) : ℝ :=
  (∑ i : Fin (task.sampleCount + 1),
      Real.log (1 + Real.exp (-signed_margin model task θ i))) /
    ((task.sampleCount + 1 : ℕ) : ℝ)

noncomputable def squared_displacement {p : ℕ} (θ₀ θ : cl_parameter_space p) : ℝ :=
  ‖θ - θ₀‖ ^ 2

noncomputable def regularized_step_objective {Input : Type*} {p : ℕ}
    (model : Input → cl_parameter_space p → ℝ) (task : cl_task Input)
    (reg : ℝ) (θ₀ θ : cl_parameter_space p) : ℝ :=
  task_logistic_loss model task θ + reg * squared_displacement θ₀ θ

structure regularized_continual_run {Input : Type*} {p M : ℕ}
    (model : Input → cl_parameter_space p → ℝ) (tasks : Fin M → cl_task Input)
    (taskOrder : ℕ → Fin M) where
  iterate : ℝ → ℕ → cl_parameter_space p
  initial : ∀ reg, iterate reg 0 = 0
  step_is_minimizer : ∀ (reg : ℝ), 0 < reg → ∀ t : ℕ,
    IsMinOn
      (regularized_step_objective model (tasks (taskOrder (t + 1))) reg (iterate reg t))
      Set.univ (iterate reg (t + 1))

def is_sequential_projection_prefix {Input : Type*} {p M : ℕ}
    (model : Input → cl_parameter_space p → ℝ) (tasks : Fin M → cl_task Input)
    (taskOrder : ℕ → Fin M) (t : ℕ) (projected : ℕ → cl_parameter_space p) : Prop :=
  projected 0 = 0 ∧
    ∀ s, 1 ≤ s → s ≤ t →
      projected s ∈ task_feasible_set model (tasks (taskOrder s)) ∧
        IsMinOn (squared_displacement (projected (s - 1)))
          (task_feasible_set model (tasks (taskOrder s))) (projected s)

noncomputable def normalized_direction {p : ℕ} (θ : cl_parameter_space p) :
    cl_parameter_space p :=
  ‖θ‖⁻¹ • θ

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
            atTop (nhds (normalized_direction (projected t))) := by sorry

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open scoped BigOperators

abbrev td_vector (d : ℕ) := Fin d → ℝ

noncomputable def td_euclidean_norm {d : ℕ} (v : td_vector d) : ℝ :=
  Real.sqrt (∑ i, (v i) ^ 2)

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

noncomputable def td_prefix_kernel {n d : ℕ} (M : td_model n d) (t : ℕ) :
    ProbabilityTheory.Kernel ((i : Finset.Iic t) → Fin n) (Fin n) :=
  ProbabilityTheory.Kernel.ofFunOfCountable fun x =>
    (M.transition (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure

instance td_prefix_kernel_is_markov {n d : ℕ} (M : td_model n d) (t : ℕ) :
    ProbabilityTheory.IsMarkovKernel (td_prefix_kernel M t) := by
  constructor
  intro x
  change MeasureTheory.IsProbabilityMeasure
    ((M.transition (x ⟨t, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure)
  infer_instance

noncomputable def td_markov_path_measure {n d : ℕ} (M : td_model n d) (s0 : Fin n) :
    MeasureTheory.Measure (ℕ → Fin n) :=
  ProbabilityTheory.Kernel.trajMeasure (MeasureTheory.Measure.dirac s0)
    (fun t => td_prefix_kernel M t)

noncomputable def td_transition_matrix {n d : ℕ} (M : td_model n d) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (M.transition i j).toReal

def td_sample_matrix {n d : ℕ} (M : td_model n d) (s s' : Fin n) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => M.feature s i * (M.feature s j - M.discount * M.feature s' j)

def td_sample_vector {n d : ℕ} (M : td_model n d) (s s' : Fin n) : td_vector d :=
  M.reward s s' • M.feature s

def td_update {n d : ℕ} (M : td_model n d) (θ : td_vector d) (s s' : Fin n) :
    td_vector d :=
  td_sample_vector M s s' - Matrix.mulVec (td_sample_matrix M s s') θ

noncomputable def td_population_matrix {n d : ℕ} (M : td_model n d) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ∑ s, ∑ s',
    (M.stationary s).toReal * (M.transition s s').toReal * td_sample_matrix M s s' i j

noncomputable def td_population_vector {n d : ℕ} (M : td_model n d) : td_vector d :=
  fun i => ∑ s, ∑ s',
    (M.stationary s).toReal * (M.transition s s').toReal * td_sample_vector M s s' i

def td_fixed_point {n d : ℕ} (M : td_model n d) (θstar : td_vector d) : Prop :=
  Matrix.mulVec (td_population_matrix M) θstar = td_population_vector M

noncomputable def td_iterates {n d : ℕ} (M : td_model n d) (η : ℕ → ℝ)
    (θ0 : td_vector d) : ℕ → (ℕ → Fin n) → td_vector d
  | 0, _ => θ0
  | t + 1, path =>
      td_iterates M η θ0 t path +
        η t • td_update M (td_iterates M η θ0 t path) (path t) (path (t + 1))

def pr_step_mass (η : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, η t

noncomputable def pr_average {d : ℕ} (η : ℕ → ℝ)
    (θ : ℕ → td_vector d) (T : ℕ) : td_vector d :=
  (pr_step_mass η T)⁻¹ • ∑ t ∈ Finset.range T, η t • θ t

def td_value {n d : ℕ} (M : td_model n d) (θ : td_vector d) : Fin n → ℝ :=
  fun s => M.feature s ⬝ᵥ θ

noncomputable def td_weighted_square {n d : ℕ} (M : td_model n d) (v : Fin n → ℝ) : ℝ :=
  ∑ s, (M.stationary s).toReal * (v s) ^ 2

noncomputable def td_dirichlet_energy {n d : ℕ} (M : td_model n d)
    (v : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ s, ∑ s',
    (M.stationary s).toReal * (M.transition s s').toReal * (v s - v s') ^ 2

noncomputable def td_potential {n d : ℕ} (M : td_model n d)
    (θstar θ : td_vector d) : ℝ :=
  (1 - M.discount) * td_weighted_square M (td_value M θ - td_value M θstar) +
    M.discount * td_dirichlet_energy M (td_value M θ - td_value M θstar)

def td_uniform_bounds {n d : ℕ} (M : td_model n d) (φinf rinf : ℝ) : Prop :=
  0 < φinf ∧ 0 ≤ rinf ∧
    (∀ s, td_euclidean_norm (M.feature s) ≤ φinf) ∧
    (∀ s s', |M.reward s s'| ≤ rinf)

noncomputable def td_geometric_mixing {n d : ℕ} (M : td_model n d) (τ : ℝ) : Prop :=
  1 ≤ τ ∧ ∀ (k : ℕ) (i : Fin n),
    (∑ j, |(td_transition_matrix M ^ k) i j - (M.stationary j).toReal|) ≤
      8 * Real.rpow 2 (-((k : ℝ) / τ))

noncomputable def td_curvature {n d : ℕ} (M : td_model n d)
    (θstar : td_vector d) (ω : ℝ) : Prop :=
  0 < ω ∧ ∀ θ,
    ω * (td_euclidean_norm (θ - θstar)) ^ 2 ≤
      td_potential M θstar θ - td_potential M θstar θstar

def admissible_stepsize_shape (a : ℕ → ℝ) : Prop :=
  (∀ t, 0 < a t) ∧ Antitone a ∧ a 0 ≤ 1 ∧ Summable (fun t => (a t) ^ 2)

noncomputable def pr_eta_base (c τ φinf : ℝ) : ℝ :=
  1 / (c * τ * φinf ^ 2)

noncomputable def pr_square_mass (η : ℕ → ℝ) : ℝ :=
  ∑' t, (η t) ^ 2

noncomputable def pr_a_one (a : ℕ → ℝ) (δ : ℝ) : ℝ :=
  1536 * Real.sqrt (∑' t, (a t) ^ 2) * Real.sqrt (2 * Real.log (8 / δ)) + 2304

noncomputable def pr_a_two (a : ℕ → ℝ) : ℝ :=
  2706 * (∑' t, (a t) ^ 2)

noncomputable def pr_c_min (a : ℕ → ℝ) (δ : ℝ) : ℝ :=
  (pr_a_one a δ + Real.sqrt ((pr_a_one a δ) ^ 2 + 4 * pr_a_two a)) / 2

noncomputable def pr_rho (a : ℕ → ℝ) (δ c : ℝ) : ℝ :=
  2 * c / Real.sqrt (c ^ 2 - pr_a_one a δ * c - pr_a_two a)

noncomputable def pr_base_radius {d : ℕ} (θ0 θstar : td_vector d)
    (rinf φinf : ℝ) : ℝ :=
  max (td_euclidean_norm (θ0 - θstar))
    (max (td_euclidean_norm θstar) (rinf / φinf))

noncomputable def pr_fast_constant {d : ℕ} (a η : ℕ → ℝ) (δ c τ φinf rinf : ℝ)
    (θ0 θstar : td_vector d) : ℝ :=
  pr_rho a δ c * pr_base_radius θ0 θstar rinf φinf *
    (2 + 2 * τ * φinf ^ 2 *
      (264 * η 0 + 176 * Real.sqrt (pr_square_mass η) * Real.sqrt (2 * Real.log (8 / δ))) +
      192 * τ * φinf ^ 4 * pr_square_mass η)

noncomputable def pr_robust_constant {d : ℕ} (a η : ℕ → ℝ) (δ c τ φinf rinf : ℝ)
    (θ0 θstar : td_vector d) : ℝ :=
  (pr_rho a δ c) ^ 2 * (pr_base_radius θ0 θstar rinf φinf) ^ 2 *
    ((1 / 2 : ℝ) + 2 * τ * φinf ^ 2 *
      (288 * η 0 + 192 * Real.sqrt (pr_square_mass η) * Real.sqrt (2 * Real.log (8 / δ))) +
      (672 * τ + 9 / 2) * φinf ^ 4 * pr_square_mass η)

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

theorem pr_main {n d : ℕ} (M : td_model n d) (a η : ℕ → ℝ)
    (δ c τ φinf rinf ω : ℝ) (θ0 θstar : td_vector d) (s0 : Fin n)
    (ha : admissible_stepsize_shape a)
    (hη : ∀ t, η t = pr_eta_base c τ φinf * a t)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hc : pr_c_min a δ < c)
    (hbounds : td_uniform_bounds M φinf rinf)
    (hmix : td_geometric_mixing M τ)
    (hfixed : td_fixed_point M θstar)
    (hcurv : td_curvature M θstar ω) :
    (td_markov_path_measure M s0).real
        (pr_rate_event M a η δ c τ φinf rinf ω θ0 θstar) ≥ 1 - δ := by sorry

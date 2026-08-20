import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian

set_option maxHeartbeats 500000

open MeasureTheory

abbrev input_space (d : ℕ) := EuclideanSpace ℝ (Fin d)

abbrev weight_rows (m d : ℕ) := Fin m → input_space d

abbrev gradient_matrix (m d : ℕ) := EuclideanSpace ℝ (Fin m × Fin d)

def row_space {m d : ℕ} (W : weight_rows m d) : Submodule ℝ (input_space d) :=
  Submodule.span ℝ (Set.range W)

noncomputable def row_projector {m d : ℕ} (W : weight_rows m d) :
    input_space d →L[ℝ] input_space d :=
  (row_space W).starProjection

noncomputable def row_alignment {m p d : ℕ}
    (W : weight_rows m d) (U : weight_rows p d) : ℝ :=
  ‖(row_projector W).comp (row_projector U)‖

def first_layer_sgd_update {m d : ℕ} (W : weight_rows m d)
    (g : EuclideanSpace ℝ (Fin m)) (x : input_space d) (η : ℝ) : weight_rows m d :=
  fun i ↦ W i - (η * g i) • x

structure sgd_model (Ω Θ : Type*) [MeasurableSpace Ω] (m d : ℕ) where
  inputs : Ω → ℕ → input_space d
  trajectory : Ω → ℕ → Θ
  firstLayerRows : Θ → weight_rows m d
  sampleActivationGradient : Θ → input_space d → EuclideanSpace ℝ (Fin m)
  populationFirstLayerGradient : Θ → gradient_matrix m d
  filtration : ℕ → MeasurableSpace Ω

noncomputable def sample_first_layer_gradient
    {Ω Θ : Type*} [MeasurableSpace Ω] {m d : ℕ}
    (M : sgd_model Ω Θ m d) (θ : Θ) (x : input_space d) :
    gradient_matrix m d :=
  WithLp.toLp 2 (fun ij : Fin m × Fin d ↦
    (M.sampleActivationGradient θ x ij.1) * x ij.2)

def filtration_assumption {Ω Θ : Type*} [MeasurableSpace Ω] {m d : ℕ}
    (M : sgd_model Ω Θ m d) : Prop :=
  (∀ t, M.filtration t ≤ ‹MeasurableSpace Ω›) ∧
    ∀ ⦃s t : ℕ⦄, s ≤ t → M.filtration s ≤ M.filtration t

noncomputable def sgd_semantic_coherence
    {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ] {m d : ℕ}
    (μ : Measure Ω) (M : sgd_model Ω Θ m d) : Prop :=
  filtration_assumption M ∧
    (∀ t, MeasurableSpace.comap (fun ω ↦ M.trajectory ω t)
      ‹MeasurableSpace Θ› ≤ M.filtration t) ∧
    (∀ t, 1 ≤ t →
      ProbabilityTheory.Indep (M.filtration (t - 1))
        (MeasurableSpace.comap (fun ω ↦ M.inputs ω t)
          (borel (input_space d))) μ) ∧
    Measurable M.firstLayerRows ∧
    Measurable (Function.uncurry M.sampleActivationGradient) ∧
    (∀ θ t, MeasureTheory.Integrable
      (fun ω ↦ sample_first_layer_gradient M θ (M.inputs ω t)) μ) ∧
    ∀ θ t, M.populationFirstLayerGradient θ =
      ∫ ω, sample_first_layer_gradient M θ (M.inputs ω t) ∂μ

def sub_gaussian_input_assumptions {Ω Θ : Type*} [MeasurableSpace Ω]
    {m d : ℕ} (μ : Measure Ω) (M : sgd_model Ω Θ m d)
    (K₁ K₂ α₂ : ℝ) : Prop :=
  ProbabilityTheory.iIndepFun (fun t ω ↦ M.inputs ω t) μ ∧
    (∀ s t, ProbabilityTheory.IdentDistrib
      (fun ω ↦ M.inputs ω s) (fun ω ↦ M.inputs ω t) μ μ) ∧
    (∀ t (v : input_space d), ‖v‖ = 1 →
      ProbabilityTheory.HasSubgaussianMGF
        (fun ω ↦ inner ℝ v (M.inputs ω t)) ⟨K₁ ^ 2, sq_nonneg K₁⟩ μ) ∧
    ∀ t (r : ℝ), 0 ≤ r →
      μ {ω | |‖M.inputs ω t‖ ^ 2 - α₂ * (d : ℝ)| ≥ r} ≤
        ENNReal.ofReal (2 * Real.exp (-(r ^ 2) / (K₂ ^ 2 * (d : ℝ))))

def standard_initialization_assumption {Ω Θ : Type*} [MeasurableSpace Ω]
    {m d : ℕ} (μ : Measure Ω) (M : sgd_model Ω Θ m d) (K₃ : ℝ) : Prop :=
  let Z : Fin m × Fin d → Ω → ℝ :=
    fun ij ω ↦ (M.firstLayerRows (M.trajectory ω 0) ij.1) ij.2
  ProbabilityTheory.iIndepFun Z μ ∧
    (∀ i j, ProbabilityTheory.IdentDistrib (Z i) (Z j) μ μ) ∧
    (∀ i, ∫ ω, Z i ω ∂μ = 0) ∧
    (∀ i, ∫ ω, (Z i ω) ^ 2 ∂μ = 1 / (d : ℝ)) ∧
    ∀ i, ProbabilityTheory.HasSubgaussianMGF
      (Z i) ⟨K₃ ^ 2, sq_nonneg K₃⟩ μ

def bounded_activation_gradients {Ω Θ : Type*} [MeasurableSpace Ω]
    {m d : ℕ} (μ : Measure Ω) (M : sgd_model Ω Θ m d) (G : ℝ) : Prop :=
  ∀ (θ : Θ) (t : ℕ), ∀ᵐ ω ∂μ,
    ‖M.sampleActivationGradient θ (M.inputs ω t)‖ ≤ G

noncomputable def population_gradient_controlled {Ω Θ : Type*} [MeasurableSpace Ω]
    {m p d : ℕ} (M : sgd_model Ω Θ m d) (U : weight_rows p d)
    (ψ : ℝ → ℝ) : Prop :=
  MonotoneOn ψ (Set.Icc (0 : ℝ) 1) ∧
    (∀ r ∈ Set.Icc (0 : ℝ) 1, 0 ≤ ψ r) ∧
    ∀ θ, ‖M.populationFirstLayerGradient θ‖ ≤
      ψ (row_alignment (M.firstLayerRows θ) U)

def follows_first_layer_sgd {Ω Θ : Type*} [MeasurableSpace Ω]
    {m d : ℕ} (M : sgd_model Ω Θ m d) (η : ℝ) : Prop :=
  ∀ (ω : Ω) (t : ℕ), 1 ≤ t →
    M.firstLayerRows (M.trajectory ω t) =
      first_layer_sgd_update
        (M.firstLayerRows (M.trajectory ω (t - 1)))
        (M.sampleActivationGradient (M.trajectory ω (t - 1)) (M.inputs ω t))
        (M.inputs ω t) η

noncomputable def conditional_second_moment {Ω Θ : Type*} [MeasurableSpace Ω]
    {m d : ℕ} (μ : Measure Ω) (M : sgd_model Ω Θ m d)
    (t : ℕ) (v : EuclideanSpace ℝ (Fin m)) (ω : Ω) : ℝ :=
  MeasureTheory.condExp (m := M.filtration (t - 1)) μ
    (fun ω' ↦
      inner ℝ v (M.sampleActivationGradient
        (M.trajectory ω' (t - 1)) (M.inputs ω' t)) ^ 2) ω

noncomputable def gradient_condition_number {Ω Θ : Type*} [MeasurableSpace Ω]
    {m d : ℕ} (μ : Measure Ω) (M : sgd_model Ω Θ m d)
    (G : ℝ) (T : ℕ) (ω : Ω) : ℝ :=
  G ^ 2 / sInf {q : ℝ | ∃ (v : EuclideanSpace ℝ (Fin m)) (t : ℕ),
    ‖v‖ = 1 ∧ t ∈ Finset.Icc 1 T ∧
      q = conditional_second_moment μ M t v ω}

noncomputable def log_scale (T d p : ℕ) (δ : ℝ) : ℝ :=
  Real.log (((T : ℝ) * (d : ℝ) * (p : ℝ)) / δ)

noncomputable def alignment_threshold (C κbar : ℝ) (m p d T : ℕ) (δ : ℝ) : ℝ :=
  C * Real.sqrt
    (κbar * (m : ℝ) * (p : ℝ) * log_scale T d p δ / (d : ℝ))

noncomputable def admissible_sgd_regime (C c c' κbar η : ℝ)
    (m p d T : ℕ) (δ : ℝ) (ψ : ℝ → ℝ) : Prop :=
  (d : ℝ) ≥ c * κbar ^ 2 * (m : ℝ) ^ 2 * (log_scale T d p δ) ^ 2 ∧
    η ≤ c' /
      (κbar ^ 2 * Real.sqrt
        ((m : ℝ) * (d : ℝ) * log_scale T d p δ)) ∧
    alignment_threshold C κbar m p d T δ ∈ Set.Icc (0 : ℝ) 1 ∧
    (T : ℝ) ≤ 1 / (ψ (alignment_threshold C κbar m p d T δ)) ^ 2

noncomputable def condition_number_event {Ω Θ : Type*} [MeasurableSpace Ω]
    {m d : ℕ} (μ : Measure Ω) (M : sgd_model Ω Θ m d)
    (G κbar : ℝ) (T : ℕ) : Set Ω :=
  {ω | gradient_condition_number μ M G T ω ≤ κbar}

noncomputable def uniform_small_alignment_event {Ω Θ : Type*} [MeasurableSpace Ω]
    {m p d : ℕ} (M : sgd_model Ω Θ m d) (U : weight_rows p d)
    (C κbar : ℝ) (T : ℕ) (δ : ℝ) : Set Ω :=
  {ω | ∀ t ∈ Finset.Icc 1 T,
    row_alignment (M.firstLayerRows (M.trajectory ω t)) U ≤
      alignment_threshold C κbar m p d T δ}

theorem main
    (K₁ K₂ K₃ α₂ G : ℝ)
    (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hK₃ : 0 < K₃)
    (hα₂ : 0 < α₂) (hG : 0 < G) :
    ∃ C c c' : ℝ, 0 < C ∧ 0 < c ∧ 0 < c' ∧
      ∀ {m d p T : ℕ} {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
        (μ : Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
        (M : sgd_model Ω Θ m d) (U : weight_rows p d)
        (ψ : ℝ → ℝ) (δ κbar η : ℝ),
        0 < m → 0 < d → 0 < p → 0 < T →
        0 < δ → 1 ≤ κbar → 0 ≤ η →
        sgd_semantic_coherence μ M →
        sub_gaussian_input_assumptions μ M K₁ K₂ α₂ →
        standard_initialization_assumption μ M K₃ →
        bounded_activation_gradients μ M G →
        population_gradient_controlled M U ψ →
        follows_first_layer_sgd M η →
        admissible_sgd_regime C c c' κbar η m p d T δ ψ →
        MeasurableSet (condition_number_event μ M G κbar T) →
        MeasurableSet (uniform_small_alignment_event M U C κbar T δ) →
        0 < μ (condition_number_event μ M G κbar T) →
        (ProbabilityTheory.cond μ
          (condition_number_event μ M G κbar T))
            (uniform_small_alignment_event M U C κbar T δ) ≥
          ENNReal.ofReal (1 - δ) := by sorry

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

set_option linter.all false
set_option maxHeartbeats 500000

open scoped ENNReal
open MeasureTheory

abbrev euclidean_domain (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable instance euclidean_domain_measurable_space (d : ℕ) :
    MeasurableSpace (euclidean_domain d) :=
  borel (euclidean_domain d)

structure optimization_objective (d : ℕ) where
  value : euclidean_domain d → ℝ
  minimizerSet : Set (euclidean_domain d)
  minimizerSet_nonempty : minimizerSet.Nonempty
  minimizerSet_closed : IsClosed minimizerSet
  minimizerSet_convex : Convex ℝ minimizerSet
  projection : euclidean_domain d → euclidean_domain d
  projection_mem : ∀ x, projection x ∈ minimizerSet
  projection_nearest :
    ∀ x y, y ∈ minimizerSet → ‖x - projection x‖ ≤ ‖x - y‖
  mem_minimizerSet_iff :
    ∀ x, x ∈ minimizerSet ↔ ∀ y, value x ≤ value y

def optimal_value {d : ℕ} (f : optimization_objective d) : ℝ :=
  f.value (f.projection 0)

def is_l_smooth {d : ℕ} (L : ℝ) (f : optimization_objective d) : Prop :=
  Differentiable ℝ f.value ∧
    ∀ x y, ‖gradient f.value x - gradient f.value y‖ ≤ L * ‖x - y‖

def is_tau_quasar_convex {d : ℕ} (τ : ℝ) (f : optimization_objective d) : Prop :=
  ∀ x, f.value x - optimal_value f ≤
    (1 / τ) * inner ℝ (gradient f.value x) (x - f.projection x)

def has_mu_quadratic_growth {d : ℕ} (μ : ℝ) (f : optimization_objective d) : Prop :=
  ∀ x, (μ / 2) * ‖x - f.projection x‖ ^ 2 ≤ f.value x - optimal_value f

def admissible_objective_class (d : ℕ) (μ L τ : ℝ) :
    Set (optimization_objective d) :=
  {f | is_l_smooth L f ∧ is_tau_quasar_convex τ f ∧ has_mu_quadratic_growth μ f}

abbrev algorithm_history (d : ℕ) :=
  ℕ × (ℕ → euclidean_domain d × euclidean_domain d)

structure first_order_algorithm (d : ℕ) where
  query : algorithm_history d → euclidean_domain d
  output : algorithm_history d → euclidean_domain d
  query_measurable : Measurable query
  output_measurable : Measurable output

structure stochastic_first_order_oracle
    (d : ℕ) (𝓕 : Set (optimization_objective d)) (σ : ℝ) where
  SampleSpace : Type
  [sampleMeasurableSpace : MeasurableSpace SampleSpace]
  probabilityMeasure : Measure SampleSpace
  [probabilityMeasure_isProbability : IsProbabilityMeasure probabilityMeasure]
  response :
    ℕ → {f : optimization_objective d // f ∈ 𝓕} →
      euclidean_domain d → SampleSpace → euclidean_domain d
  response_jointly_measurable :
    ∀ n f, Measurable fun z : euclidean_domain d × SampleSpace =>
      response n f z.1 z.2
  response_integrable :
    ∀ n f x, Integrable (response n f x) probabilityMeasure
  noise_square_integrable :
    ∀ n f x, Integrable
      (fun ω => ‖response n f x ω - gradient f.1.value x‖ ^ 2)
      probabilityMeasure
  unbiased :
    ∀ n f x, (∫ ω, response n f x ω ∂probabilityMeasure) =
      gradient f.1.value x
  variance_bound :
    ∀ n f x, (∫ ω, ‖response n f x ω - gradient f.1.value x‖ ^ 2
      ∂probabilityMeasure) ≤ σ ^ 2

def oracle_transcript {d : ℕ} {𝓕 : Set (optimization_objective d)} {σ : ℝ}
    (algorithm : first_order_algorithm d)
    (oracle : stochastic_first_order_oracle d 𝓕 σ)
    (f : {f : optimization_objective d // f ∈ 𝓕})
    (ω : oracle.SampleSpace) :
    ℕ → algorithm_history d
  | 0 => (0, fun _ => (0, 0))
  | n + 1 =>
      let history := oracle_transcript algorithm oracle f ω n
      let x := algorithm.query history
      (n + 1, Function.update history.2 n (x, oracle.response n f x ω))

noncomputable def expected_optimization_error
    {d : ℕ} {𝓕 : Set (optimization_objective d)} {σ : ℝ}
    (T : ℕ) (algorithm : first_order_algorithm d)
    (oracle : stochastic_first_order_oracle d 𝓕 σ)
    (f : {f : optimization_objective d // f ∈ 𝓕}) : ℝ≥0∞ :=
  letI := oracle.sampleMeasurableSpace
  ∫⁻ ω, ENNReal.ofReal
    (f.1.value (algorithm.output (oracle_transcript algorithm oracle f ω T)) -
      optimal_value f.1) ∂oracle.probabilityMeasure

noncomputable def minimax_optimization_error
    {d : ℕ} {𝓕 : Set (optimization_objective d)} {σ : ℝ}
    (T : ℕ) (oracle : stochastic_first_order_oracle d 𝓕 σ) : ℝ≥0∞ :=
  ⨅ algorithm : first_order_algorithm d,
    ⨆ f : {f : optimization_objective d // f ∈ 𝓕},
      expected_optimization_error T algorithm oracle f

noncomputable def worst_oracle_minimax_error
    (d T : ℕ) (μ L τ σ : ℝ) : ℝ≥0∞ :=
  ⨆ oracle : stochastic_first_order_oracle d
      (admissible_objective_class d μ L τ) σ,
    minimax_optimization_error T oracle

theorem new_lower_bound_nonconvex_stochastic_optimization :
    ∃ c : ℝ, 0 < c ∧
      ∀ (μ L τ σ : ℝ) (d T : ℕ),
        0 < μ →
        0 < L →
        0 < τ →
        τ ≤ 1 →
        0 < T →
        3 * Real.logb (5 / 4 : ℝ) (2 / τ) ≤ (d : ℝ) →
        202 ≤ L / μ →
        ENNReal.ofReal
            (c * σ ^ 2 / (μ * τ ^ 2 * Real.log (2 / τ) * (T : ℝ))) ≤
          worst_oracle_minimax_error d T μ L τ σ := by sorry

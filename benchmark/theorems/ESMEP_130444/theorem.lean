import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

set_option linter.all false
set_option maxHeartbeats 500000

def soft_big_o (f g : ℕ → ℝ) : Prop :=
  ∃ k : ℕ,
    Asymptotics.IsBigO Filter.atTop f
      (fun n => (Real.log ((n : ℝ) + 2)) ^ k * g n)

def high_probability_soft_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → MeasureTheory.Measure Ω) (Q : ℕ → Ω → ℝ)
    (B : ℝ → ℕ → Ω → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∃ k : ℕ, ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∀ᶠ T in Filter.atTop,
        ∃ E : Set Ω, MeasurableSet E ∧
          1 - δ ≤ (μ T).real E ∧
            ∀ ω ∈ E, Q T ω ≤
              C * (Real.log ((T : ℝ) + 2)) ^ k * B δ T ω

structure identified_property (Y : Type*) [MeasurableSpace Y] where
  property : MeasureTheory.Measure Y → Set.Icc (0 : ℝ) 1
  identification : Set.Icc (0 : ℝ) 1 → Y → ℝ

noncomputable def elicitable_property {Y : Type*} [MeasurableSpace Y]
    (Γ : identified_property Y) : Prop :=
  ∃ loss : Set.Icc (0 : ℝ) 1 → Y → ℝ,
    ∀ (ν : MeasureTheory.Measure Y), ν Set.univ = 1 →
      ∀ γ : Set.Icc (0 : ℝ) 1,
        MeasureTheory.Integrable (fun y => loss (Γ.property ν) y) ν →
        MeasureTheory.Integrable (fun y => loss γ y) ν →
          MeasureTheory.integral ν (fun y => loss (Γ.property ν) y) ≤
              MeasureTheory.integral ν (fun y => loss γ y) ∧
            (MeasureTheory.integral ν (fun y => loss (Γ.property ν) y) =
                MeasureTheory.integral ν (fun y => loss γ y) ↔
              γ = Γ.property ν)

noncomputable def is_identification_function {Y : Type*} [MeasurableSpace Y]
    (Γ : identified_property Y) : Prop :=
  ∀ (ν : MeasureTheory.Measure Y), ν Set.univ = 1 →
    ∀ γ : Set.Icc (0 : ℝ) 1,
      MeasureTheory.Integrable (fun y => Γ.identification γ y) ν →
        (MeasureTheory.integral ν (fun y => Γ.identification γ y) = 0 ↔
          γ = Γ.property ν)

def lipschitz_identification {Y : Type*} [MeasurableSpace Y]
    (Γ : identified_property Y) (ρ : ℝ) : Prop :=
  0 ≤ ρ ∧
    ∀ p q y,
      |Γ.identification p y - Γ.identification q y| ≤
        ρ * |(p : ℝ) - (q : ℝ)|

structure online_agnostic_learner (X : Type*) where
  predict :
    (n : ℕ) → (Fin n → X) → (Fin n → ℝ) → Fin n → X → ℝ
  regret : ℕ → ℝ

noncomputable def online_agnostic_regret {X : Type*}
    (A : online_agnostic_learner X) (F : Set (X → ℝ)) : Prop :=
  ∀ (n : ℕ) (x : Fin n → X) (κ : Fin n → ℝ),
    sSup {a : ℝ | ∃ f ∈ F, a = ∑ t, f (x t) * κ t} ≤
      (∑ t, A.predict n x κ t (x t) * κ t) + A.regret n

structure forecasting_process (X Y Ω : Type*) [MeasurableSpace Ω] where
  measure : ℕ → MeasureTheory.Measure Ω
  context : (T : ℕ) → Ω → Fin T → X
  label : (T : ℕ) → Ω → Fin T → Y
  prediction : (T : ℕ) → Ω → Fin T → Set.Icc (0 : ℝ) 1
  gridSize : ℕ → ℕ
  gridSize_pos : ∀ T, 0 < gridSize T
  probability : ∀ T, measure T Set.univ = 1

noncomputable def grid_point (N : ℕ) (i : Fin N) : ℝ :=
  ((i.1 + 1 : ℕ) : ℝ) / (N : ℝ)

noncomputable def prediction_bucket {X Y Ω : Type*} [MeasurableSpace Ω]
    (P : forecasting_process X Y Ω) (T : ℕ) (ω : Ω)
    (i : Fin (P.gridSize T)) : Finset (Fin T) := by
  classical
  exact Finset.univ.filter
    (fun t => (P.prediction T ω t : ℝ) = grid_point (P.gridSize T) i)

def uses_prediction_grid {X Y Ω : Type*} [MeasurableSpace Ω]
    (P : forecasting_process X Y Ω) : Prop :=
  ∀ (T : ℕ) (ω : Ω) (t : Fin T),
    ∃ i : Fin (P.gridSize T),
      (P.prediction T ω t : ℝ) = grid_point (P.gridSize T) i

noncomputable def bucket_count {X Y Ω : Type*} [MeasurableSpace Ω]
    (P : forecasting_process X Y Ω) (T : ℕ) (ω : Ω)
    (i : Fin (P.gridSize T)) : ℕ :=
  (prediction_bucket P T ω i).card

noncomputable def bucket_correlation {X Y Ω : Type*} [MeasurableSpace Ω]
    (P : forecasting_process X Y Ω) (F : Set (X → ℝ))
    (V : Set.Icc (0 : ℝ) 1 → Y → ℝ) (T : ℕ) (ω : Ω)
    (i : Fin (P.gridSize T)) : ℝ :=
  if bucket_count P T ω i = 0 then 0
  else
    ((bucket_count P T ω i : ℕ) : ℝ)⁻¹ *
      sSup {a : ℝ | ∃ f ∈ F,
        a =
          |∑ t ∈ prediction_bucket P T ω i,
            f (P.context T ω t) *
              V (P.prediction T ω t) (P.label T ω t)|}

noncomputable def swap_multicalibration_error
    {X Y Ω : Type*} [MeasurableSpace Ω]
    (P : forecasting_process X Y Ω) (F : Set (X → ℝ))
    (V : Set.Icc (0 : ℝ) 1 → Y → ℝ)
    (r : ℝ) (T : ℕ) (ω : Ω) : ℝ :=
  ∑ i : Fin (P.gridSize T),
    (bucket_count P T ω i : ℝ) *
      (bucket_correlation P F V T ω i) ^ r

noncomputable def tuned_grid_size (q : ℝ) (T : ℕ) : ℕ :=
  max 1 (Nat.ceil ((T : ℝ) ^ (1 / (q + 1))))

noncomputable def regret_contribution {X Y Ω : Type*} [MeasurableSpace Ω]
    (P : forecasting_process X Y Ω) (A : online_agnostic_learner X)
    (q : ℝ) (T : ℕ) (ω : Ω) : ℝ :=
  ∑ i : Fin (P.gridSize T),
    (bucket_count P T ω i : ℝ) *
      (A.regret (bucket_count P T ω i) /
        (bucket_count P T ω i : ℝ)) ^ q

noncomputable def discretization_contribution
    {X Y Ω : Type*} [MeasurableSpace Ω]
    (P : forecasting_process X Y Ω) (q ρ δ : ℝ) (T : ℕ) : ℝ :=
  ρ ^ q * (T : ℝ) / (P.gridSize T : ℝ) ^ q +
    (P.gridSize T : ℝ) *
      (Real.log ((P.gridSize T : ℝ) / δ)) ^ (q / 2)

noncomputable def preoptimized_rate {X Y Ω : Type*} [MeasurableSpace Ω]
    (P : forecasting_process X Y Ω) (A : online_agnostic_learner X)
    (q ρ δ : ℝ) (T : ℕ) (ω : Ω) : ℝ :=
  discretization_contribution P q ρ δ T +
    regret_contribution P A q T ω

def oracle_efficient_execution
    {X Y Ω : Type*} [MeasurableSpace Ω]
    (P : forecasting_process X Y Ω) (A : online_agnostic_learner X)
    (F : Set (X → ℝ)) (V : Set.Icc (0 : ℝ) 1 → Y → ℝ)
    (q ρ : ℝ) : Prop :=
  high_probability_soft_bound P.measure
    (swap_multicalibration_error P F V q)
    (fun δ => preoptimized_rate P A q ρ δ)

noncomputable def large_exponent_rate
    (q ρ α complexity δ : ℝ) (T : ℕ) : ℝ :=
  ρ ^ q * (T : ℝ) ^ (1 / (q + 1)) +
    (T : ℝ) ^ (1 / (q + 1)) *
      (Real.log (1 / δ)) ^ (q / 2) +
    (T : ℝ) ^
        (1 - q + q / (q + 1) + α * q ^ 2 / (q + 1)) *
      complexity ^ q +
    (T : ℝ) ^ (1 / (q + 1)) * complexity ^ q

noncomputable def small_exponent_rate
    (r ρ α complexity δ : ℝ) (T : ℕ) : ℝ :=
  ρ ^ r * (T : ℝ) ^ (1 - r / 3) +
    (T : ℝ) ^ (1 - r / 3) *
      (Real.log (1 / δ)) ^ (r / 2) +
    (T : ℝ) ^ (1 + 2 * r * (α - 1) / 3) *
      complexity ^ r +
    (T : ℝ) ^ (1 - r / 3) * complexity ^ r

theorem smcal_general_result
    {X Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]
    (Γ : identified_property Y)
    (P : forecasting_process X Y Ω) (A : online_agnostic_learner X)
    (F : Set (X → ℝ)) (r ρ α complexity : ℝ)
    (hr : 1 ≤ r)
    (hαzero : 0 ≤ α) (hαone : α < 1)
    (hcomplexity : 0 < complexity)
    (helicitable : elicitable_property Γ)
    (hidentify : is_identification_function Γ)
    (hlip : lipschitz_identification Γ ρ)
    (hbounded : ∀ f ∈ F, ∀ x, |f x| ≤ 1)
    (hF : F.Nonempty)
    (honline : online_agnostic_regret A F)
    (hregret_nonneg : ∀ n, 0 ≤ A.regret n)
    (hregret :
      soft_big_o A.regret
        (fun n => (n : ℝ) ^ α * complexity))
    (hgrid : uses_prediction_grid P)
    (hsize :
      ∀ T, P.gridSize T = tuned_grid_size (max r 2) T)
    (hAlgorithm :
      oracle_efficient_execution P A F Γ.identification (max r 2) ρ) :
    (2 ≤ r →
      high_probability_soft_bound P.measure
        (swap_multicalibration_error P F Γ.identification r)
        (fun δ T _ => large_exponent_rate r ρ α complexity δ T)) ∧
    ((1 ≤ r ∧ r < 2) →
      high_probability_soft_bound P.measure
        (swap_multicalibration_error P F Γ.identification r)
        (fun δ T _ => small_exponent_rate r ρ α complexity δ T)) := by sorry

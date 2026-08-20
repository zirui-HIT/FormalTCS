import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic

open MeasureTheory
open scoped BigOperators

structure boolean_distinguishing_family (X : Type*) [MeasurableSpace X] where
  carrier : Set (X → Bool)
  carrier_countable : carrier.Countable
  measurable : ∀ f ∈ carrier, Measurable f
  complement_mem : ∀ f ∈ carrier, (fun x => ! (f x)) ∈ carrier

def boolean_value (b : Bool) : ℝ :=
  if b then 1 else 0

def rademacher_sign (b : Bool) : ℝ :=
  if b then 1 else -1

noncomputable def fooling_distance {X : Type*} [MeasurableSpace X]
    (F : boolean_distinguishing_family X) (P Q : ProbabilityMeasure X) : ℝ :=
  sSup ((fun f : X → Bool =>
    |(∫ x, boolean_value (f x) ∂P.toMeasure) -
      (∫ x, boolean_value (f x) ∂Q.toMeasure)|) '' F.carrier)

noncomputable def empirical_rademacher_complexity {X : Type*} [MeasurableSpace X]
    (F : boolean_distinguishing_family X) {m : ℕ} (S : Fin m → X) : ℝ :=
  ((2 : ℝ) ^ m)⁻¹ *
    ∑ σ : Fin m → Bool,
      sSup ((fun f : X → Bool =>
        |(m : ℝ)⁻¹ *
          ∑ i : Fin m,
            rademacher_sign (σ i) * (2 * boolean_value (f (S i)) - 1)|) '' F.carrier)

noncomputable def distributional_rademacher_complexity {X : Type*} [MeasurableSpace X]
    (F : boolean_distinguishing_family X) (m : ℕ) (P : ProbabilityMeasure X) : ℝ :=
  ∫ S, empirical_rademacher_complexity F S
    ∂(ProbabilityMeasure.pi (fun _ : Fin m => P)).toMeasure

def rademacher_complexity_promise {X : Type*} [MeasurableSpace X]
    (F : boolean_distinguishing_family X) (m : ℕ)
    (P : ProbabilityMeasure X) (ρ : ℝ) : Prop :=
  distributional_rademacher_complexity F m P ≤ ρ

structure identity_tester (X : Type*) [MeasurableSpace X] where
  sampleCount : ℕ
  decide : ((Fin sampleCount → X) × (Fin sampleCount → X)) → Bool
  measurable_decide : Measurable decide

def measurable_decision_event {Ω : Type*} [MeasurableSpace Ω]
    (d : Ω → Bool) (hd : Measurable d) (b : Bool) :
    {E : Set Ω // MeasurableSet E} :=
  ⟨d ⁻¹' {b}, hd (measurableSet_singleton b)⟩

noncomputable def identity_acceptance_probability {X : Type*} [MeasurableSpace X]
    (T : identity_tester X) (P P_ref : ProbabilityMeasure X) : ℝ :=
  ((ProbabilityMeasure.pi (fun _ : Fin T.sampleCount => P)).toMeasure.prod
    (ProbabilityMeasure.pi (fun _ : Fin T.sampleCount => P_ref)).toMeasure).real
      (measurable_decision_event T.decide T.measurable_decide true)

noncomputable def identity_rejection_probability {X : Type*} [MeasurableSpace X]
    (T : identity_tester X) (P P_ref : ProbabilityMeasure X) : ℝ :=
  ((ProbabilityMeasure.pi (fun _ : Fin T.sampleCount => P)).toMeasure.prod
    (ProbabilityMeasure.pi (fun _ : Fin T.sampleCount => P_ref)).toMeasure).real
      (measurable_decision_event T.decide T.measurable_decide false)

def is_identity_tester {X : Type*} [MeasurableSpace X]
    (T : identity_tester X) (F : boolean_distinguishing_family X)
    (P_ref : ProbabilityMeasure X) (ε δ : ℝ) : Prop :=
  (∀ P : ProbabilityMeasure X, P = P_ref →
      identity_acceptance_probability T P P_ref ≥ 1 - δ) ∧
  (∀ P : ProbabilityMeasure X, fooling_distance F P P_ref > ε →
      identity_rejection_probability T P P_ref ≥ 1 - δ)

noncomputable def sample_complexity_bound (C : ℝ) (m : ℕ) (ε δ : ℝ) : ℕ :=
  m + Nat.ceil (C * (1 + Real.log (1 / δ)) / ε ^ 2)

theorem testing_upper_bounds_identity :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
        (F : boolean_distinguishing_family X)
        (P_ref : ProbabilityMeasure X)
        (m : ℕ) (ε δ : ℝ),
        0 < m → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        rademacher_complexity_promise F m P_ref (ε / 16) →
        ∃ T : identity_tester X,
          is_identity_tester T F P_ref ε δ ∧
          T.sampleCount ≤ sample_complexity_bound C m ε δ := by sorry

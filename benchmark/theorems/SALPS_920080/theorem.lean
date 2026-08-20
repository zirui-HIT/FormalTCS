import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory

abbrev boolean_concept_class (X : Type*) :=
  Set (X → Bool)

def set_shatters {X : Type*} (H : boolean_concept_class X) (W : Set X) : Prop :=
  ∀ W' ⊆ W, ∃ h ∈ H, h ⁻¹' {true} ∩ W = W'

def positive_region {X : Type*} (h : X → Bool) : Set X :=
  {x | h x = true}

def generalized_smoothness {X : Type*} [MeasurableSpace X]
    (Dtrue Dref : Measure X) (sigma q : ℝ) : Prop :=
  ∀ S : Set X, MeasurableSet S →
    (Dtrue S).toReal ≤ sigma⁻¹ * Real.rpow (Dref S).toReal (1 / q)

def positive_conditional_law {X : Type*} [MeasurableSpace X]
    (Ptrue Dtrue : Measure X) (hstar : X → Bool) : Prop :=
  Measurable hstar ∧
    Dtrue (positive_region hstar) ≠ 0 ∧
    ∀ S : Set X, MeasurableSet S →
      Ptrue S =
        Dtrue (S ∩ positive_region hstar) / Dtrue (positive_region hstar)

def numerical_vc_dimension {X : Type*} (H : boolean_concept_class X) (d : ℕ) : Prop :=
  (∀ W : Finset X, set_shatters H (W : Set X) → W.card ≤ d) ∧
    ∃ W : Finset X, W.card = d ∧ set_shatters H (W : Set X)

abbrev positive_reference_learner (X : Type*) (n : ℕ) :=
  (Fin n → X) → (Fin n → X) → (X → Bool)

noncomputable def misclassification_error {X : Type*} [MeasurableSpace X]
    (Dtrue : Measure X) (h hstar : X → Bool) : ℝ :=
  (Dtrue {x | h x ≠ hstar x}).toReal

def positive_reference_success_event {X : Type*} [MeasurableSpace X] {n : ℕ}
    (Dtrue : Measure X) (hstar : X → Bool) (epsilon : ℝ)
    (A : positive_reference_learner X n) :
    Set ((Fin n → X) × (Fin n → X)) :=
  {samples |
    misclassification_error Dtrue (A samples.1 samples.2) hstar ≤ epsilon}

def positive_reference_learning_guarantee {X : Type*} [MeasurableSpace X] {n : ℕ}
    (Ptrue Dref Dtrue : Measure X) (hstar : X → Bool)
    (epsilon delta : ℝ) (A : positive_reference_learner X n) : Prop :=
  (∀ positiveSamples referenceSamples, Measurable (A positiveSamples referenceSamples)) ∧
    MeasurableSet (positive_reference_success_event Dtrue hstar epsilon A) ∧
    1 - delta ≤
      (((Measure.pi (fun _ : Fin n => Ptrue)).prod
          (Measure.pi (fun _ : Fin n => Dref)))
        (positive_reference_success_event Dtrue hstar epsilon A)).toReal

noncomputable def sample_complexity_scale
    (d : ℕ) (epsilon delta sigma q : ℝ) : ℝ :=
  ((d : ℝ) + Real.log (1 / delta)) /
    Real.rpow (epsilon * sigma) (2 * q)

def polylog_sample_bound (n : ℕ) (scale C : ℝ) (k : ℕ) : Prop :=
  0 ≤ scale ∧ 0 < C ∧
    (n : ℝ) ≤ C * scale * (Real.log (Real.exp 1 + scale)) ^ k

def admits_measurable_erm_selection {X : Type*} [MeasurableSpace X]
    (H : boolean_concept_class X) : Prop :=
  H.Nonempty →
    ∀ n : ℕ,
      ∃ select : (Fin n → X) → (Fin n → Bool) → (X → Bool),
        (∀ sample labels,
            select sample labels ∈ H ∧
              ∀ h ∈ H,
                (Finset.univ.filter
                    (fun i => select sample labels (sample i) ≠ labels i)).card ≤
                  (Finset.univ.filter
                    (fun i => h (sample i) ≠ labels i)).card) ∧
          Measurable
            (fun data : ((Fin n → X) × (Fin n → Bool)) × X =>
              select data.1.1 data.1.2 data.2)

theorem sample_complexity {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (H : boolean_concept_class X) (d : ℕ) (sigma q : ℝ)
    (hHmeasurable : ∀ h ∈ H, Measurable h)
    (hHselection : admits_measurable_erm_selection H)
    (hvc : numerical_vc_dimension H d)
    (hsigmaPos : 0 < sigma) (hsigmaUpper : sigma ≤ 1) (hq : 1 ≤ q) :
    ∃ C : ℝ, ∃ k : ℕ, 0 < C ∧
      ∀ epsilon delta : ℝ,
        0 < epsilon → epsilon < 1 / 2 →
        0 < delta → delta < 1 / 2 →
        ∃ n : ℕ, ∃ A : positive_reference_learner X n,
          polylog_sample_bound n
              (sample_complexity_scale d epsilon delta sigma q) C k ∧
            ∀ (Dtrue Ptrue Dref : Measure X) (hstar : X → Bool),
              IsProbabilityMeasure Dtrue →
              IsProbabilityMeasure Ptrue →
              IsProbabilityMeasure Dref →
              hstar ∈ H →
              positive_conditional_law Ptrue Dtrue hstar →
              generalized_smoothness Dtrue Dref sigma q →
            positive_reference_learning_guarantee
              Ptrue Dref Dtrue hstar epsilon delta A := by sorry

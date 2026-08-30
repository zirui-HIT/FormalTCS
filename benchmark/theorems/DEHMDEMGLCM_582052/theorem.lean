import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.Basic

set_option linter.all false
set_option maxHeartbeats 500000

structure hellinger_density (Ω : Type*) [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) where
  toProbabilityMeasure : MeasureTheory.ProbabilityMeasure Ω
  val : Ω → ℝ
  nonnegative : ∀ x, 0 ≤ val x
  measurable_val : Measurable val
  measure_eq_withDensity :
    (toProbabilityMeasure : MeasureTheory.Measure Ω) =
      μ.withDensity (fun x => ENNReal.ofReal (val x))

noncomputable def squared_hellinger {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} (p q : hellinger_density Ω μ) : ℝ :=
  (2 : ℝ)⁻¹ *
    MeasureTheory.integral μ
      (fun x => (Real.sqrt (p.val x) - Real.sqrt (q.val x)) ^ (2 : ℕ))

abbrev concept_class (Ω : Type*) :=
  Set (Ω → Bool)

def set_shatters {Ω : Type*} (H : concept_class Ω) (W : Set Ω) : Prop :=
  ∀ W' ⊆ W, ∃ h ∈ H, h ⁻¹' {true} ∩ W = W'

def concept_event {Ω : Type*} (h : Ω → Bool) : Set Ω :=
  {x | h x = true}

def ratio_concept_class {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} (F : Set (hellinger_density Ω μ)) :
    concept_class Ω :=
  {h | ∃ p ∈ F, ∃ q ∈ F, ∃ τ : ℝ,
    h = fun x => decide (τ * q.val x ≤ p.val x)}

noncomputable def modified_hellinger_distance {Ω : Type*} [MeasurableSpace Ω]
    (H : concept_class Ω)
    (P Q : MeasureTheory.Measure Ω) : ℝ :=
  sSup {r : ℝ | ∃ h ∈ H,
    r = (2 : ℝ)⁻¹ *
      (Real.sqrt (P.real (concept_event h)) -
        Real.sqrt (Q.real (concept_event h))) ^ (2 : ℕ)}

noncomputable def empirical_measure {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (x : Fin n → Ω) : MeasureTheory.Measure Ω :=
  (n : ENNReal)⁻¹ • (∑ i : Fin n, MeasureTheory.Measure.dirac (x i))

def is_approximate_minimum_distance_estimator {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} (n : ℕ)
    (H : concept_class Ω)
    (F : Set (hellinger_density Ω μ))
    (ε : ℝ) (hat : (Fin n → Ω) → hellinger_density Ω μ) : Prop :=
  0 ≤ ε ∧ ∀ x, hat x ∈ F ∧ ∀ g ∈ F,
    modified_hellinger_distance H (empirical_measure n x)
        (hat x).toProbabilityMeasure ≤
      modified_hellinger_distance H (empirical_measure n x)
        g.toProbabilityMeasure + ε

def shattered_cardinalities {Ω : Type*}
    (H : concept_class Ω) : Set ℕ :=
  {m | ∃ W : Finset Ω, W.card = m ∧
    set_shatters H (W : Set Ω)}

def has_vc_dimension {Ω : Type*}
    (H : concept_class Ω) (d : ℕ) : Prop :=
  BddAbove (shattered_cardinalities H) ∧
    sSup (shattered_cardinalities H) = d

noncomputable def binary_logarithm (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

noncomputable def hellinger_log_penalty (x : ℝ) : ℝ :=
  x * binary_logarithm (2 / x)

noncomputable def best_approximation_penalty {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} (f : hellinger_density Ω μ)
    (F : Set (hellinger_density Ω μ)) : ℝ :=
  sInf {r : ℝ | ∃ g ∈ F,
    r = hellinger_log_penalty (squared_hellinger f g)}

noncomputable def vc_complexity_term (n d : ℕ) (δ : ℝ) : ℝ :=
  (((d : ℝ) * binary_logarithm n + binary_logarithm (2 / δ)) *
    binary_logarithm n) / (n : ℝ)

noncomputable def iid_sample_law {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {n : ℕ} (f : hellinger_density Ω μ) :
    MeasureTheory.Measure (Fin n → Ω) :=
  (MeasureTheory.ProbabilityMeasure.pi
    (fun _ : Fin n => f.toProbabilityMeasure)).toMeasure

def is_atomless_measure {Ω : Type*} [MeasurableSpace Ω]
    (ν : MeasureTheory.Measure Ω) : Prop :=
  ∀ s : Set Ω, MeasurableSet s → 0 < ν s →
    ∃ t : Set Ω, t ⊆ s ∧ MeasurableSet t ∧ 0 < ν t ∧ ν t < ν s

theorem hellinger_minimum_distance_estimator :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
        (n d : ℕ) (δ : ℝ) (f : hellinger_density Ω μ)
        (F : Set (hellinger_density Ω μ)),
        2 ≤ n → 1 ≤ d → 0 < δ → δ < 1 → F.Nonempty →
        ∀ (ε : ℝ), ε ≤ (n : ℝ)⁻¹ →
        ∀ (hat : (Fin n → Ω) → hellinger_density Ω μ),
          is_atomless_measure
            (f.toProbabilityMeasure : MeasureTheory.Measure Ω) →
          (ratio_concept_class F).Countable →
          has_vc_dimension (ratio_concept_class F) d →
          is_approximate_minimum_distance_estimator n
            (ratio_concept_class F) F ε hat →
          Measurable (fun x => squared_hellinger f (hat x)) →
          iid_sample_law (n := n) f
              {x | squared_hellinger f (hat x) ≤
                C * (best_approximation_penalty f F +
                  vc_complexity_term n d δ)} ≥
            ENNReal.ofReal (1 - δ) := by sorry

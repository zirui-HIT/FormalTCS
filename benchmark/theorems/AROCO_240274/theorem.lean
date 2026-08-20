import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity

open scoped BigOperators
open MeasureTheory

abbrev oco_point (d : ℕ) := Fin d → ℝ

noncomputable def continuous_hedge_learning_rate (d T : ℕ) : ℝ :=
  min 1
    (Real.rpow (T : ℝ) (-(1 : ℝ) / 3) *
      Real.rpow ((d : ℝ) * Real.log (T : ℝ)) ((1 : ℝ) / 3))

noncomputable def continuous_hedge_weight_measure {d : ℕ}
    (X : Set (oco_point d)) (loss : ℕ → oco_point d → ℝ) (η : ℝ) (t : ℕ) :
    Measure (oco_point d) :=
  ((MeasureTheory.Measure.euclideanHausdorffMeasure
      (Module.finrank ℝ (affineSpan ℝ X).direction)).restrict X).withDensity fun y =>
    ENNReal.ofReal (Real.exp (-η * ∑ s ∈ Finset.range t, loss s y))

noncomputable def continuous_hedge_distribution {d : ℕ}
    (X : Set (oco_point d)) (loss : ℕ → oco_point d → ℝ) (η : ℝ) (t : ℕ) :
    Measure (oco_point d) :=
  letI : Decidable X.Nonempty := Classical.propDecidable _
  let μ := continuous_hedge_weight_measure X loss η t
  if hX : X.Nonempty then
    if μ Set.univ ≠ 0 ∧ μ Set.univ ≠ ⊤ then
      (μ Set.univ)⁻¹ • μ
    else
      Measure.dirac hX.choose
  else
    0

def is_continuous_hedge {d : ℕ} (T : ℕ) (X : Set (oco_point d))
    (loss : ℕ → oco_point d → ℝ) (η : ℝ)
    (p : ℕ → Measure (oco_point d)) (x : ℕ → oco_point d) : Prop :=
  ∀ t, t ≤ T →
    p t = continuous_hedge_distribution X loss η t ∧
      IsProbabilityMeasure (p t) ∧
      p t (Xᶜ) = 0 ∧
      Integrable (fun y => y) (p t) ∧
      x t = integral (p t) (fun y => y) ∧
      x t ∈ X

def comparator_alternating_regret {d : ℕ} (T : ℕ)
    (loss : ℕ → oco_point d → ℝ) (x : ℕ → oco_point d) (u : oco_point d) : ℝ :=
  ∑ t ∈ Finset.range T, (loss t (x t) + loss t (x (t + 1)) - 2 * loss t u)

noncomputable def alternating_regret {d : ℕ} (T : ℕ) (X : Set (oco_point d))
    (loss : ℕ → oco_point d → ℝ) (x : ℕ → oco_point d) : ℝ :=
  sSup (comparator_alternating_regret T loss x '' X)

noncomputable def continuous_hedge_rate (d T : ℕ) : ℝ :=
  Real.rpow (d : ℝ) ((2 : ℝ) / 3) *
    Real.rpow (T : ℝ) ((1 : ℝ) / 3) *
      Real.rpow (Real.log (T : ℝ)) ((2 : ℝ) / 3)

theorem hedge_cont :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ,
      ∀ (d T : ℕ) (X : Set (oco_point d)) (loss : ℕ → oco_point d → ℝ),
        T₀ ≤ T →
        0 < d →
        X.Nonempty →
        Convex ℝ X →
        (∀ t, t < T → ConvexOn ℝ X (loss t)) →
        (∀ t, t < T → ∀ y ∈ X, |loss t y| ≤ 1) →
        (∀ t, t ≤ T →
          (continuous_hedge_weight_measure X loss
              (continuous_hedge_learning_rate d T) t) Set.univ ≠ 0 ∧
          (continuous_hedge_weight_measure X loss
              (continuous_hedge_learning_rate d T) t) Set.univ ≠ ⊤) →
        ∃ (p : ℕ → Measure (oco_point d)) (x : ℕ → oco_point d),
          is_continuous_hedge T X loss (continuous_hedge_learning_rate d T) p x ∧
          alternating_regret T X loss x ≤ C * continuous_hedge_rate d T := by sorry

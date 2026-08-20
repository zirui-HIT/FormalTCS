import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

noncomputable def averaged_two_bin {T : ℕ} (r p : Fin T → ℝ) : ℝ :=
  ∫ q in (0 : ℝ)..1,
    (1 / (T : ℝ) ^ 2) *
      ((∑ t ∈ Finset.univ.filter (fun t => r t < q), (r t - p t)) ^ 2 +
       (∑ t ∈ Finset.univ.filter (fun t => q ≤ r t), (r t - p t)) ^ 2)

noncomputable def ex_ante_atb_error {X : Type*} [MeasurableSpace X] (T : ℕ)
    (D : Measure (X × ℝ)) (r : X → ℝ) : ℝ :=
  ∫ s : Fin T → X × ℝ,
      averaged_two_bin (fun t => r (s t).1) (fun t => (s t).2)
    ∂(Measure.pi fun _ => D)

def is_ground_truth {X : Type*} [MeasurableSpace X]
    (D : Measure (X × ℝ)) (p : X → ℝ) : Prop :=
  (fun z : X × ℝ => p z.1) =ᵐ[D]
    condExp (MeasurableSpace.comap Prod.fst inferInstance) D (fun z => z.2)

theorem atb_strictly_ex_ante_truthful {X : Type*} [MeasurableSpace X] (T : ℕ) (hT : 0 < T)
    (D : Measure (X × ℝ)) [IsProbabilityMeasure D] (r p : X → ℝ)
    (hy : ∀ᵐ z ∂D, z.2 = 0 ∨ z.2 = 1) (hrm : Measurable r)
    (hp : is_ground_truth D p)
    (hr : ∀ x, r x ∈ Set.Icc (0 : ℝ) 1) (hpmem : ∀ x, p x ∈ Set.Icc (0 : ℝ) 1)
    (hle : ex_ante_atb_error T D r ≤ ex_ante_atb_error T D p) :
    (fun z : X × ℝ => r z.1) =ᵐ[D] (fun z : X × ℝ => p z.1) := by sorry

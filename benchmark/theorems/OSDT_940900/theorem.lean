import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

set_option linter.all false
set_option maxHeartbeats 500000

noncomputable def domain_supremum {E : Type} (Ω : Set E) (f : E → ℝ) : ℝ :=
  sSup (f '' Ω)

noncomputable def domain_infimum {E : Type} (Ω : Set E) (g : E → ℝ) : ℝ :=
  sInf (g '' Ω)

noncomputable def transport_upper_deviation
    {I E : Type} [Fintype I] [Nonempty I]
    (σ : E → I → ℝ) (s : E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (σ s) - 1

noncomputable def transport_lower_deviation
    {I E : Type} [Fintype I] [Nonempty I]
    (σ : E → I → ℝ) (s : E) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (σ s) - 1

noncomputable def transport_conditions
    {d : ℕ} [NeZero d]
    (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (μ ν : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))
    (eigenbasis :
      EuclideanSpace ℝ (Fin d) →
        OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (σ : EuclideanSpace ℝ (Fin d) → Fin d → ℝ) : Prop :=
  Ω.Nonempty ∧
    IsCompact Ω ∧
    Convex ℝ Ω ∧
    ContDiffOn ℝ 1 T Ω ∧
    (∀ s ∈ Ω, ∀ i,
      fderivWithin ℝ T Ω s (eigenbasis s i) =
        (σ s i) • eigenbasis s i) ∧
    (∀ s ∈ Ω, ∀ i, 0 < σ s i) ∧
    MeasureTheory.IsProbabilityMeasure μ ∧
    MeasureTheory.IsProbabilityMeasure ν ∧
    MeasureTheory.Measure.AbsolutelyContinuous μ
      MeasureTheory.MeasureSpace.volume ∧
    MeasureTheory.Measure.AbsolutelyContinuous ν
      MeasureTheory.MeasureSpace.volume ∧
    μ Ωᶜ = 0 ∧
    ν Ωᶜ = 0 ∧
    MeasureTheory.Measure.map T μ = ν ∧
    ∃ s ∈ Ω, ∃ i, σ s i ≠ 1

noncomputable def is_unit_schedule (τ : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 1 τ (Set.Icc 0 1) ∧
    MonotoneOn τ (Set.Icc 0 1) ∧
    Set.MapsTo τ (Set.Icc 0 1) (Set.Icc 0 1) ∧
    τ 0 = 0 ∧
    τ 1 = 1

noncomputable def l_inf_speed {E : Type}
    (Ω : Set E) (f g : E → ℝ) (x : ℝ) : ℝ :=
  max
    (sSup ((fun s => |f s / (1 + x * f s)|) '' Ω))
    (sSup ((fun s => |g s / (1 + x * g s)|) '' Ω))

noncomputable def solves_l_inf_ode {E : Type}
    (Ω : Set E) (f g : E → ℝ) (τ : ℝ → ℝ) : Prop :=
  is_unit_schedule τ ∧
    ∃ Z : ℝ, 0 < Z ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt τ (Z⁻¹ * (l_inf_speed Ω f g (τ t))⁻¹) t

noncomputable def transition_time (fStar gStar : ℝ) : ℝ :=
  Real.log ((1 / 2) * (1 - fStar / gStar)) /
    (Real.log ((1 / 4) * (2 - fStar / gStar - gStar / fStar)) -
      Real.log (gStar + 1))

abbrev transition_time_defined (fStar gStar : ℝ) : Prop :=
  gStar < 0 ∧
    0 < fStar ∧
    Real.log ((1 / 4) * (2 - fStar / gStar - gStar / fStar)) -
        Real.log (gStar + 1) ≠ 0

noncomputable def transition_value (fStar gStar : ℝ) : ℝ :=
  -(1 / 2) * (1 / fStar + 1 / gStar)

noncomputable def transition_left_formula (fStar gStar t : ℝ) : ℝ :=
  (1 / fStar) *
      (((1 / (4 * (gStar + 1))) *
        (2 - fStar / gStar - gStar / fStar)) ^ t) -
    1 / fStar

noncomputable def transition_right_formula (fStar gStar t : ℝ) : ℝ :=
  (1 / 2) * (1 / gStar - 1 / fStar) *
      ((2 * (gStar + 1) / (1 - gStar / fStar)) ^ t) *
      (((1 / 2) * (1 - fStar / gStar)) ^ (1 - t)) -
    1 / gStar

noncomputable def expanding_formula (fStar t : ℝ) : ℝ :=
  ((fStar + 1) ^ t - 1) / fStar

noncomputable def contracting_formula (gStar t : ℝ) : ℝ :=
  ((gStar + 1) ^ t - 1) / gStar

noncomputable def has_transition_formula
    (τ : ℝ → ℝ) (fStar gStar : ℝ) : Prop :=
  let t₀ := transition_time fStar gStar
  τ t₀ = transition_value fStar gStar ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (t ≤ t₀ → τ t = transition_left_formula fStar gStar t) ∧
      (t₀ ≤ t → τ t = transition_right_formula fStar gStar t)

noncomputable def has_expanding_formula (τ : ℝ → ℝ) (fStar : ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1, τ t = expanding_formula fStar t

noncomputable def has_contracting_formula (τ : ℝ → ℝ) (gStar : ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1, τ t = contracting_formula gStar t

theorem solution_of_l_inf_ode
    {d : ℕ} [NeZero d]
    (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (μ ν : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))
    (eigenbasis :
      EuclideanSpace ℝ (Fin d) →
        OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (σ : EuclideanSpace ℝ (Fin d) → Fin d → ℝ)
    (τ : ℝ → ℝ)
    (htransport :
      transport_conditions Ω T μ ν eigenbasis σ)
    (hode :
      solves_l_inf_ode Ω
        (transport_upper_deviation σ)
        (transport_lower_deviation σ) τ) :
    (let f := transport_upper_deviation σ
      let g := transport_lower_deviation σ
      let fStar := domain_supremum Ω f
      let gStar := domain_infimum Ω g
      let t₀ := transition_time fStar gStar
      if transition_time_defined fStar gStar ∧
          t₀ ∈ Set.Icc (0 : ℝ) 1 then
        has_transition_formula τ fStar gStar
      else if -gStar ≤ fStar then
        has_expanding_formula τ fStar
      else
        has_contracting_formula τ gStar) := by
  sorry

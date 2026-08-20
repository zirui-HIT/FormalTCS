import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

open MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable def marginal_moment {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d)) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (|⟪u, X ω⟫| ^ p) ∂μ

noncomputable def aggregated_moment {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → EuclideanSpace ℝ (Fin d))
    (P₀ : Measure (EuclideanSpace ℝ (Fin d))) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, marginal_moment μ X u p ∂P₀

noncomputable def nu_measure {d : ℕ} (nrm : Seminorm ℝ (EuclideanSpace ℝ (Fin d)))
    (P₀ : Measure (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  ⨆ x ∈ frontier {y : EuclideanSpace ℝ (Fin d) | nrm y ≤ 1},
    1 / P₀ {u : EuclideanSpace ℝ (Fin d) | 1 ≤ |⟪u, x⟫|}

noncomputable def tail_bound_value {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (nrm : Seminorm ℝ (EuclideanSpace ℝ (Fin d)))
    (X : Ω → EuclideanSpace ℝ (Fin d)) (t : ℝ) : ℝ≥0∞ :=
  ⨅ P₀ ∈ {ν : Measure (EuclideanSpace ℝ (Fin d)) |
      IsProbabilityMeasure ν ∧ nu_measure nrm ν ≠ ⊤},
    ⨅ p ∈ Set.Ici (1 : ℝ),
      ENNReal.ofReal (Real.exp (t / p))
        * aggregated_moment μ X P₀ p ^ (1 / p)
        * nu_measure nrm P₀ ^ (1 / p)

theorem tail_bound {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (nrm : Seminorm ℝ (EuclideanSpace ℝ (Fin d)))
    (X : Ω → EuclideanSpace ℝ (Fin d)) (hX : Measurable X)
    (t : ℝ) (ht : 0 ≤ t) :
    1 - ENNReal.ofReal (Real.exp (-t))
      ≤ μ {ω | ENNReal.ofReal (nrm (X ω)) ≤ tail_bound_value μ nrm X t} := by
  sorry

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option linter.all false
set_option maxHeartbeats 500000

open scoped Matrix
open MeasureTheory ProbabilityTheory

section

local instance matrix_measurable_space {n : ℕ} :
    MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin n → ℝ))

structure stochastic_contraction_process (n : ℕ) (Ω : Type) [MeasurableSpace Ω]
    (μ : Measure Ω) where
  M : ℕ → Ω → Matrix (Fin n) (Fin n) ℝ
  Δ : ℕ → Ω → (Fin n → ℝ)
  Mbar : Matrix (Fin n) (Fin n) ℝ
  indep : iIndepFun M μ
  fresh : ∀ (t : ℕ), IndepFun (M t) (Δ t) μ
  psd : ∀ (t : ℕ) (ω : Ω), (M t ω).PosSemidef
  contraction : ∀ (t : ℕ) (ω : Ω), (1 - M t ω).PosSemidef
  mean : ∀ (t : ℕ) (i j : Fin n), ∫ ω, M t ω i j ∂μ = Mbar i j
  recurrence : ∀ (t : ℕ) (ω : Ω), Δ (t + 1) ω = (1 - M t ω) *ᵥ Δ t ω
  M_meas : ∀ (t : ℕ), Measurable (M t)
  Δ_meas : ∀ (t : ℕ), Measurable (Δ t)

theorem last_iterate_convergence :
    ∃ C : ℝ, 0 < C ∧ ∃ θ : ℝ, (0.001 : ℝ) ≤ θ ∧
      ∀ (n : ℕ) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (P : stochastic_contraction_process n Ω μ) (t : ℕ), 1 ≤ t →
        (∫⁻ ω, ENNReal.ofReal (P.Δ t ω ⬝ᵥ (P.Mbar *ᵥ P.Δ t ω)) ∂μ)
          ≤ ENNReal.ofReal C *
              (∫⁻ ω, ENNReal.ofReal (P.Δ 0 ω ⬝ᵥ P.Δ 0 ω) ∂μ) /
                ENNReal.ofReal ((t : ℝ) ^ ((3 : ℝ) / 4 + θ)) := by sorry

end

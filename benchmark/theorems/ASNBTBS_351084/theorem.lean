import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Algebra.InfiniteSum.Defs

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

structure betting_null_model {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (m : ℝ) (X : ℕ → Ω → ℝ) : Prop where
  independent : iIndepFun X μ
  commonLaw : ∀ n, IdentDistrib (X n) id μ P
  support : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1
  mean : ∫ x, x ∂P = m
  nondegenerate : P ≠ Measure.dirac m

def betting_history {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (n : ℕ) : MeasurableSpace Ω :=
  ⨆ k : Fin n, MeasurableSpace.comap (X (k : ℕ)) inferInstance

def is_predictable_bet {Ω : Type*} [MeasurableSpace Ω]
    (X lam : ℕ → Ω → ℝ) : Prop :=
  ∀ n, @Measurable Ω ℝ (betting_history X n) inferInstance (lam n)

def is_admissible_bet {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (m : ℝ) (lam : ℕ → Ω → ℝ) : Prop :=
  is_predictable_bet X lam ∧
    ∀ n ω, -(1 / (1 - m)) ≤ lam n ω ∧ lam n ω ≤ 1 / m

def betting_wealth {Ω : Type*} (m : ℝ)
    (X lam : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∏ k ∈ Finset.range n, (1 + lam k ω * (X k ω - m))

theorem sum_of_squares_criterion {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (m : ℝ) (X lam : ℕ → Ω → ℝ)
    (hmodel : betting_null_model μ P m X)
    (hbet : is_admissible_bet X m lam) :
    ∃ Wlim : Ω → ℝ,
      (∀ᵐ ω ∂μ,
        Tendsto (fun n => betting_wealth m X lam n ω) atTop (𝓝 (Wlim ω))) ∧
      (∀ᵐ ω ∂μ,
        Wlim ω = 0 ↔
          ¬Summable (fun n => (lam n ω) ^ 2) ∨
            ∃ n, lam n ω * (X n ω - m) = -1) ∧
      (∀ᵐ ω ∂μ,
        0 < Wlim ω ↔
          Summable (fun n => (lam n ω) ^ 2) ∧
            ∀ n, -1 < lam n ω * (X n ω - m)) := by sorry

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open scoped BigOperators ENNReal

structure probability_vector (d : ℕ) where
  coordinate : Fin d → ℝ
  nonnegative : ∀ i, 0 ≤ coordinate i
  sum_eq_one : ∑ i, coordinate i = 1

structure prediction_grid (d m : ℕ) where
  point : Fin m → probability_vector d
  injective : Function.Injective point

abbrev nonanticipating_adversary (d m T : ℕ) :=
  ∀ t : Fin T, (Fin t.val → Fin m) → (Fin t.val → Fin d) → Fin d

structure randomized_forecasting_strategy (d m T : ℕ) where
  seedCount : ℕ
  seedCount_pos : 0 < seedCount
  seedLaw : PMF (Fin seedCount)
  forecast :
    ∀ t : Fin T, Fin seedCount → (Fin t.val → Fin m) → (Fin t.val → Fin d) → Fin m
  predictionPath : nonanticipating_adversary d m T → Fin seedCount → Fin T → Fin m
  outcomePath : nonanticipating_adversary d m T → Fin seedCount → Fin T → Fin d
  forecast_consistent : ∀ adversary seed t,
    predictionPath adversary seed t =
      forecast t seed
        (fun s => predictionPath adversary seed ⟨s.val, lt_trans s.isLt t.isLt⟩)
        (fun s => outcomePath adversary seed ⟨s.val, lt_trans s.isLt t.isLt⟩)
  outcome_consistent : ∀ adversary seed t,
    outcomePath adversary seed t =
      adversary t
        (fun s => predictionPath adversary seed ⟨s.val, lt_trans s.isLt t.isLt⟩)
        (fun s => outcomePath adversary seed ⟨s.val, lt_trans s.isLt t.isLt⟩)

def one_hot_coordinate {d : ℕ} (x i : Fin d) : ℝ :=
  if i = x then 1 else 0

def calibration_error {d m T : ℕ} (grid : prediction_grid d m)
    (predictions : Fin T → Fin m) (outcomes : Fin T → Fin d) : ℝ :=
  ∑ j, ∑ i, |∑ t, if predictions t = j then
    (grid.point j).coordinate i - one_hot_coordinate (outcomes t) i else 0|

def expected_calibration_error {d m T : ℕ} (grid : prediction_grid d m)
    (strategy : randomized_forecasting_strategy d m T)
    (adversary : nonanticipating_adversary d m T) : ℝ :=
  ∑ seed, (strategy.seedLaw seed).toReal *
    calibration_error grid (strategy.predictionPath adversary seed)
      (strategy.outcomePath adversary seed)

def polynomial_polylog_horizon_bound (C : ℝ) (k : ℕ) (ε : ℝ) (d T : ℕ) : Prop :=
  T ≤ d ^ ⌈(C * (1 + ε⁻¹ ^ 2)) *
    (Real.log (d + 1) + Real.log (1 + ε⁻¹)) ^ k⌉₊

theorem calibration_algo :
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ (ε : ℝ), 0 < ε → ∀ (d : ℕ), 0 < d →
        ∃ (m T : ℕ) (grid : prediction_grid d m)
          (strategy : randomized_forecasting_strategy d m T),
          0 < m ∧ 0 < T ∧ polynomial_polylog_horizon_bound C k ε d T ∧
          ∀ adversary : nonanticipating_adversary d m T,
            expected_calibration_error grid strategy adversary ≤ ε * T := by sorry

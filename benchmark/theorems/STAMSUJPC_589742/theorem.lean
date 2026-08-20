import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Filter
import Mathlib.Order.Filter.AtTopBot.Defs

set_option linter.all false
set_option maxHeartbeats 500000

structure precedence_instance (n : ℕ) where
  precedence : Fin n → Fin n → Prop
  decidablePrecedence : DecidableRel precedence
  strictOrder : IsStrictOrder (Fin n) precedence

structure unit_job_schedule (n m : ℕ) where
  makespan : ℕ
  slot : Fin n → Fin makespan
  capacity : ∀ t : Fin makespan,
    (Finset.univ.filter fun j : Fin n => slot j = t).card ≤ m

def unit_job_schedule_respects_precedence {n m : ℕ}
    (I : precedence_instance n) (S : unit_job_schedule n m) : Prop :=
  ∀ ⦃i j : Fin n⦄, I.precedence i j → S.slot i < S.slot j

def unit_job_schedule_is_optimal {n m : ℕ}
    (I : precedence_instance n) (S : unit_job_schedule n m) : Prop :=
  unit_job_schedule_respects_precedence I S ∧
    ∀ T : unit_job_schedule n m,
      unit_job_schedule_respects_precedence I T → S.makespan ≤ T.makespan

structure makespan_scheduling_algorithm (m : ℕ) where
  schedule : ∀ n : ℕ, precedence_instance n → unit_job_schedule n m
  runningTime : ∀ n : ℕ, precedence_instance n → ℕ
  optimal : ∀ (n : ℕ) (I : precedence_instance n),
    unit_job_schedule_is_optimal I (schedule n I)

noncomputable def has_subexponential_running_time {m : ℕ}
    (A : makespan_scheduling_algorithm m) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ I : precedence_instance n,
        (A.runningTime n I : ℝ) ≤
          Real.rpow (1 + (n : ℝ) / (m : ℝ))
            (C * Real.sqrt ((n : ℝ) * (m : ℝ)))

theorem mainthm (m : ℕ) (hm : 0 < m) :
    ∃ A : makespan_scheduling_algorithm m, has_subexponential_running_time A := by sorry

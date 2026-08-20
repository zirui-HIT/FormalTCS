import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Order.ConditionallyCompleteLattice.Basic

set_option linter.all false
set_option maxHeartbeats 500000

structure ocp_interval where
  lo : ℝ
  hi : ℝ

def ocp_vol (I : ocp_interval) : ℝ := I.hi - I.lo

def ocp_covers (I : ocp_interval) (y : ℝ) : Prop := I.lo ≤ y ∧ y ≤ I.hi

noncomputable def ocp_opt_vol (T : ℕ) (S : Fin T → ℝ) (α : ℝ) : ℝ :=
  sInf { v : ℝ | ∃ I : ocp_interval, ocp_vol I = v ∧
    (1 - α) * (T : ℝ) ≤ (({i : Fin T | ocp_covers I (S i)}.ncard : ℝ)) }

noncomputable def ocp_error_rate (α : ℝ) (T : ℕ) (t : ℕ) : ℝ :=
  if t = 0 then 1 else α * (T : ℝ) / (t : ℝ)

noncomputable def ocp_mistakes_upto (T : ℕ) (S : Fin T → ℝ) (I : ocp_interval)
    (t : ℕ) : ℕ :=
  {i : Fin T | (i : ℕ) < t ∧ ¬ ocp_covers I (S i)}.ncard

def ocp_feasible (α : ℝ) (T : ℕ) (S : Fin T → ℝ) (I : ocp_interval) (t : ℕ) : Prop :=
  (ocp_mistakes_upto T S I t : ℝ) ≤ ocp_error_rate α T t * (t : ℝ)

noncomputable def ocp_total_mistakes (T : ℕ) (S : Fin T → ℝ)
    (play : Fin T → ocp_interval) : ℕ :=
  {t : Fin T | ¬ ocp_covers (play t) (S t)}.ncard

structure ocp_meta_alg_guarantee (minwidth μ α : ℝ) (T : ℕ) (S : Fin T → ℝ) where
  play : Fin T → ocp_interval
  metaConst : ℝ
  metaConst_nonneg : 0 ≤ metaConst
  volume_bound : ∀ t : Fin T, ocp_vol (play t) ≤ μ * max (ocp_opt_vol T S α) minwidth
  mistakes_bound :
    (∀ (I₁ I₂ : ocp_interval) (t₁ t₂ : ℕ),
        2 * α * (T : ℝ) + 1 < (t₁ : ℝ) → t₁ < t₂ → t₂ ≤ T →
        ocp_feasible α T S I₁ t₁ → ocp_feasible α T S I₂ t₂ →
        ∃ i : Fin T, ((i : ℕ) : ℝ) < 2 * α * (T : ℝ) + 1 ∧
          ocp_covers I₁ (S i) ∧ ocp_covers I₂ (S i)) →
      (ocp_total_mistakes T S play : ℝ) ≤
        (2 * α * (T : ℝ) + 1) +
          metaConst * (Real.log (1 / minwidth) / Real.log μ) * (α * (T : ℝ) + 1)

theorem ocp_optimal_algorithm_for_arbitrary_order
    (minwidth μ α : ℝ) (T : ℕ) (S : Fin T → ℝ)
    (hminwidth : 0 < minwidth) (hμ : 3 < μ) (hα : 0 ≤ α)
    (hlog : 1 ≤ Real.log (1 / minwidth) / Real.log μ)
    (G : ocp_meta_alg_guarantee minwidth μ α T S) :
    (∀ t : Fin T, ocp_vol (G.play t) ≤ μ * max (ocp_opt_vol T S α) minwidth) ∧
      (ocp_total_mistakes T S G.play : ℝ) ≤
        (G.metaConst + 2) * (Real.log (1 / minwidth) / Real.log μ) * (α * (T : ℝ) + 1) := by sorry

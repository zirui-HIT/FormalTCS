import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

inductive dynamic_update_mode where
  | incremental
  | decremental

structure fine_grained_complexity_model where
  Algorithm : Type
  totalTime : Algorithm → ℕ → ℕ
  computesMinimumWeightFourClique : Algorithm → Prop
  computesDynamicSTSP : dynamic_update_mode → Algorithm → Prop
  dynamicSTSPSubquarticReduction :
    ∀ (mode : dynamic_update_mode) (A : Algorithm) (ε : ℝ),
      computesDynamicSTSP mode A → 0 < ε →
      Asymptotics.IsBigO Filter.atTop
        (fun n : ℕ => (totalTime A n : ℝ))
        (fun n : ℕ => Real.rpow (n : ℝ) (4 - ε)) →
      ∃ B : Algorithm, ∃ δ : ℝ,
        computesMinimumWeightFourClique B ∧ 0 < δ ∧
          Asymptotics.IsBigO Filter.atTop
            (fun n : ℕ => (totalTime B n : ℝ))
            (fun n : ℕ => Real.rpow (n : ℝ) (4 - δ))

def runs_in_exponent_time (M : fine_grained_complexity_model)
    (A : M.Algorithm) (c : ℝ) : Prop :=
  Asymptotics.IsBigO Filter.atTop
    (fun n : ℕ => (M.totalTime A n : ℝ))
    (fun n : ℕ => Real.rpow (n : ℝ) c)

def requires_near_quartic_total_time (M : fine_grained_complexity_model)
    (P : M.Algorithm → Prop) : Prop :=
  ∀ A, P A → ∀ ε : ℝ, 0 < ε → ¬ runs_in_exponent_time M A (4 - ε)

def minimum_weight_four_clique_hypothesis
    (M : fine_grained_complexity_model) : Prop :=
  requires_near_quartic_total_time M M.computesMinimumWeightFourClique

def dynamic_stsp_near_quartic_lower_bound
    (M : fine_grained_complexity_model) (mode : dynamic_update_mode) : Prop :=
  requires_near_quartic_total_time M (M.computesDynamicSTSP mode)

theorem st_sp_lb (M : fine_grained_complexity_model)
    (hClique : minimum_weight_four_clique_hypothesis M) :
    ∀ mode : dynamic_update_mode,
      dynamic_stsp_near_quartic_lower_bound M mode := by sorry

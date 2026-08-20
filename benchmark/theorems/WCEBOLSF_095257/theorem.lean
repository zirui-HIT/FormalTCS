import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.all false

def online_learner := List (ℝ × ℝ) → ℝ → ℝ

noncomputable def online_loss_from (p : ℝ) (A : online_learner) (f : ℝ → ℝ) :
    List (ℝ × ℝ) → List ℝ → ENNReal
  | _, [] => 0
  | history, x :: xs =>
      ENNReal.ofReal (|A history x - f x| ^ p) +
        online_loss_from p A f (history ++ [(x, f x)]) xs

noncomputable def online_loss (p : ℝ) (A : online_learner) (f : ℝ → ℝ)
    (queries : List ℝ) : ENNReal :=
  match queries with
  | [] => 0
  | x :: xs => online_loss_from p A f [(x, f x)] xs

noncomputable def worst_case_loss (p : ℝ) (A : online_learner)
    (F : Set (ℝ → ℝ)) : ENNReal :=
  ⨆ f : {f : ℝ → ℝ // f ∈ F},
    ⨆ queries : {queries : List ℝ // ∀ x ∈ queries, x ∈ Set.Icc (0 : ℝ) 1},
      online_loss p A f.1 queries.1

noncomputable def optimal_loss (p : ℝ) (F : Set (ℝ → ℝ)) : ENNReal :=
  ⨅ A : online_learner, worst_case_loss p A F

def smooth_function_class (q : ℝ) : Set (ℝ → ℝ) :=
  {f | AbsolutelyContinuousOnInterval f 0 1 ∧
    IntervalIntegrable (fun x => |deriv f x| ^ q) MeasureTheory.volume 0 1 ∧
    (∫ x in (0 : ℝ)..1, |deriv f x| ^ q) ≤ 1}

def positive_parameter_filter : Filter ℝ :=
  nhdsWithin 0 (Set.Ioo 0 1)

def positive_parameter_pair_filter : Filter (ℝ × ℝ) :=
  Filter.comap (fun z : ℝ × ℝ => min z.1 z.2) positive_parameter_filter ⊓
    Filter.principal (Set.prod (Set.Ioo 0 1) (Set.Ioo 0 1))

def ennreal_is_big_o_upper {α : Type*} (l : Filter α)
    (f g : α → ENNReal) : Prop :=
  ∃ C : NNReal, ∀ᶠ x in l, f x ≤ (C : ENNReal) * g x

noncomputable def inverse_parameter_scale (x : ℝ) : ENNReal :=
  ENNReal.ofReal x⁻¹

theorem finitebound :
    ennreal_is_big_o_upper positive_parameter_pair_filter
      (fun z : ℝ × ℝ =>
        optimal_loss (1 + z.1) (smooth_function_class (1 + z.2)))
      (fun z : ℝ × ℝ => inverse_parameter_scale (min z.1 z.2)) := by sorry

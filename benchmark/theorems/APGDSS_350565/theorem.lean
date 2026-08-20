import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Extr
import Mathlib.NumberTheory.Padics.PadicVal.Basic

noncomputable def silver_ratio : ℝ :=
  1 + Real.sqrt 2

def silver_horizon (k : ℕ) : ℕ :=
  2 ^ k - 1

noncomputable def silver_stepsize (M : ℝ) (t : ℕ) : ℝ :=
  (Real.rpow silver_ratio ((padicValNat 2 (t + 1) : ℝ) - 1) + 1) / M

def composite_objective {E : Type*} (f h : E → ℝ) (x : E) : ℝ :=
  f x + h x

def is_m_smooth_convex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (M : ℝ) (f : E → ℝ) (g : E → E) : Prop :=
  0 < M ∧
    ConvexOn ℝ Set.univ f ∧
    (∀ x : E, HasGradientAt f (g x) x) ∧
    ∀ x y : E, ‖g x - g y‖ ≤ M * ‖x - y‖

def is_proximal_point {E : Type*} [NormedAddCommGroup E]
    (h : E → ℝ) (α : ℝ) (y z : E) : Prop :=
  0 < α ∧
    IsMinOn (fun w : E => h w + ‖w - y‖ ^ 2 / (2 * α)) Set.univ z

def is_silver_proximal_gradient_trajectory {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : ℝ) (h : E → ℝ) (g : E → E) (k : ℕ) (x : ℕ → E) : Prop :=
  ∀ t : ℕ, t < silver_horizon k →
    is_proximal_point h (silver_stepsize M t)
      (x t - silver_stepsize M t • g (x t)) (x (t + 1))

theorem silver_proximal_gradient_rate {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (M : ℝ) (f h : E → ℝ) (g : E → E) (k : ℕ) (hk : 0 < k)
    (x : ℕ → E) (xStar : E)
    (hf : is_m_smooth_convex M f g)
    (hh : ConvexOn ℝ Set.univ h)
    (hxStar : IsMinOn (composite_objective f h) Set.univ xStar)
    (hx : is_silver_proximal_gradient_trajectory M h g k x) :
    composite_objective f h (x (silver_horizon k)) -
        composite_objective f h xStar ≤
      silver_ratio /
          (4 * Real.sqrt 2 *
            Real.rpow (silver_horizon k : ℝ) (Real.logb 2 silver_ratio)) *
        M * ‖x 0 - xStar‖ ^ 2 := by sorry

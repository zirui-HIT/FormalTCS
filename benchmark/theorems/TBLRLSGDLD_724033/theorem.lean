import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Lattice.Nat

open scoped BigOperators

abbrev logistic_parameter_space := EuclideanSpace ℝ (Fin 2)

noncomputable def logistic_loss (z : ℝ) : ℝ :=
  Real.log (1 + Real.exp (-z))

noncomputable def empirical_logistic_loss {n : ℕ}
    (x : Fin n → logistic_parameter_space) (w : logistic_parameter_space) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, logistic_loss (inner ℝ w (x i))

def is_admissible_logistic_dataset {n : ℕ}
    (x : Fin n → logistic_parameter_space) (γ : ℝ) : Prop :=
  0 < n ∧
    0 < γ ∧
    γ < 1 ∧
    (∀ i, ‖x i‖ ≤ 1) ∧
    ∃ wStar : logistic_parameter_space,
      ‖wStar‖ = 1 ∧
        (∀ i, γ ≤ inner ℝ wStar (x i)) ∧
        ∀ w : logistic_parameter_space, ‖w‖ = 1 →
          ∃ i, inner ℝ w (x i) ≤ γ

noncomputable def large_stepsize_threshold (n : ℕ) (γ : ℝ) : ℝ :=
  max (n : ℝ) ((32 / γ ^ 2) * Real.log (256 / γ ^ 2))

noncomputable def is_logistic_gradient_descent_orbit {n : ℕ}
    (x : Fin n → logistic_parameter_space) (η : ℝ)
    (w : ℕ → logistic_parameter_space) : Prop :=
  w 0 = 0 ∧
    ∀ t : ℕ,
      w (t + 1) =
        w t + (η / (n : ℝ)) •
          (∑ i : Fin n,
            (1 / (Real.exp (inner ℝ (w t) (x i)) + 1)) • x i)

noncomputable def logistic_transition_time {n : ℕ}
    (x : Fin n → logistic_parameter_space) (η : ℝ)
    (w : ℕ → logistic_parameter_space) : ℕ :=
  sInf {t : ℕ | empirical_logistic_loss x (w t) ≤ 1 / (8 * η)}

theorem upper_bound :
    ∃ CTransition CLoss : ℝ,
      0 < CTransition ∧
      0 < CLoss ∧
      ∀ (n : ℕ) (x : Fin n → logistic_parameter_space) (γ η : ℝ)
        (w : ℕ → logistic_parameter_space),
        is_admissible_logistic_dataset x γ →
        large_stepsize_threshold n γ ≤ η →
        is_logistic_gradient_descent_orbit x η w →
        empirical_logistic_loss x
            (w (logistic_transition_time x η w)) ≤ 1 / (8 * η) ∧
          (logistic_transition_time x η w : ℝ) ≤
              CTransition *
                ((n : ℝ) / γ + Real.log (1 / γ) / γ ^ 2) ∧
            ∀ t : ℕ, logistic_transition_time x η w < t →
              empirical_logistic_loss x (w t) ≤
                CLoss /
                  (η * γ ^ 2 *
                    ((t - logistic_transition_time x η w : ℕ) : ℝ)) := by sorry

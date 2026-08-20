import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt

open scoped BigOperators

abbrev hamiltonian_point (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

def hamiltonian_objective {d : ℕ}
    (f : hamiltonian_point d → ℝ)
    (g : hamiltonian_point d → hamiltonian_point d)
    (L : ℝ) (xStar : hamiltonian_point d) : Prop :=
  0 < L ∧
    (∀ x, HasGradientAt f (g x) x) ∧
    (∀ x x', f x + inner ℝ (g x) (x' - x) ≤ f x') ∧
    (∀ x x',
      f x' ≤ f x + inner ℝ (g x) (x' - x) + (L / 2) * ‖x' - x‖ ^ 2) ∧
    (∀ x, f xStar ≤ f x) ∧
    (∀ x, f x = f xStar → x = xStar)

def extragradient_trajectory {d : ℕ}
    (g : hamiltonian_point d → hamiltonian_point d) (η : ℝ)
    (x₀ y₀ : hamiltonian_point d) : ℕ → hamiltonian_point d × hamiltonian_point d
  | 0 => (x₀, y₀)
  | n + 1 =>
      let previous := extragradient_trajectory g η x₀ y₀ n
      let xHalf := previous.1 + η • previous.2
      let xNext := xHalf - (η ^ 2) • g xHalf
      let yNext := previous.2 - η • g xNext
      (xNext, yNext)

noncomputable def weighted_extragradient_average {d : ℕ}
    (g : hamiltonian_point d → hamiltonian_point d) (η : ℝ)
    (x : hamiltonian_point d) (N : ℕ) : hamiltonian_point d :=
  (2 / ((N : ℝ) * ((N + 1 : ℕ) : ℝ))) •
    ∑ i ∈ Finset.range N,
      (((N - i : ℕ) : ℝ) • (extragradient_trajectory g η x 0 (i + 1)).1)

noncomputable def mixed_extragradient_point {d : ℕ}
    (g : hamiltonian_point d → hamiltonian_point d) (η lam : ℝ)
    (x : hamiltonian_point d) (N : ℕ) : hamiltonian_point d :=
  (lam / (lam + 1)) • (extragradient_trajectory g η x 0 N).1 +
    (1 / (lam + 1)) • weighted_extragradient_average g η x N

noncomputable def accelerated_outer_iterate {d : ℕ}
    (g : hamiltonian_point d → hamiltonian_point d) (η lam : ℝ)
    (N : ℕ → ℕ) (x₀ : hamiltonian_point d) : ℕ → hamiltonian_point d
  | 0 => x₀
  | k + 1 =>
      mixed_extragradient_point g η lam
        (accelerated_outer_iterate g η lam N x₀ k) (N (k + 1))

def inner_step_mass (N : ℕ) : ℝ := (N : ℝ) * ((N + 1 : ℕ) : ℝ)

noncomputable def mixing_parameter : ℝ := (Real.sqrt 3 + 1) / 2

def admissible_inner_schedule (N : ℕ → ℕ) (K : ℕ) : Prop :=
  N 0 = 4 ∧
    ∀ k, k < K →
      (3 / (Real.sqrt 3 + 1)) * inner_step_mass (N k) ≤
        inner_step_mass (N (k + 1))

theorem hf_extg_cvx {d : ℕ}
    (f : hamiltonian_point d → ℝ)
    (g : hamiltonian_point d → hamiltonian_point d)
    (L η : ℝ) (xStar x₀ : hamiltonian_point d)
    (N : ℕ → ℕ) (K : ℕ)
    (hObjective : hamiltonian_objective f g L xStar)
    (hηpos : 0 < η) (hηmax : η ≤ 1 / Real.sqrt L)
    (hSchedule : admissible_inner_schedule N K) :
    f (accelerated_outer_iterate g η mixing_parameter N x₀ K) - f xStar
      ≤
    ((Real.sqrt 3 + 1) / 3) ^ K *
      (f x₀ - f xStar +
        ((Real.sqrt 3 - 1) / (60 * η ^ 2)) * ‖x₀ - xStar‖ ^ 2) := by sorry

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Int.Interval

noncomputable def rnn_eigenvalue (α : ℝ) (K : ℕ) (s : ℤ) : ℂ :=
  Complex.exp (((-α / K : ℝ) : ℂ) + ((Real.pi * s / K : ℝ) : ℂ) * Complex.I)

noncomputable def rnn_coefficient_scale (α : ℝ) (K : ℕ) : ℝ :=
  Real.exp (-α) * (Real.exp (2 * α) - Real.exp (-(2 * α))) / (2 * K)

noncomputable def rnn_coefficient (α : ℝ) (K : ℕ) (s : ℤ) : ℂ :=
  ((rnn_coefficient_scale α K : ℝ) : ℂ) * (-1 : ℂ) ^ s

noncomputable def rnn_filter (α : ℝ) (T K : ℕ) (k : ℕ) : ℂ :=
  ∑ s ∈ Finset.Icc (-(T : ℤ)) (T : ℤ), rnn_coefficient α K s * rnn_eigenvalue α K s ^ k

noncomputable def shift_filter (K : ℕ) (k : ℕ) : ℂ :=
  if k = K then 1 else 0

noncomputable def white_noise_time_loss (c d : ℕ → ℂ) : ℝ :=
  ∑' k : ℕ, ‖c k - d k‖ ^ 2

theorem upper_bound_of_the_error (α : ℝ) (hα : 0 < α) (T K : ℕ → ℕ)
    (hK1 : ∀ n, 1 ≤ K n)
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop)
    (hK : Filter.Tendsto K Filter.atTop Filter.atTop)
    (hSK : Filter.Tendsto (fun n => (2 * (T n : ℝ) + 1) / (K n : ℝ)) Filter.atTop (nhds 0)) :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n => white_noise_time_loss (rnn_filter α (T n) (K n)) (shift_filter (K n)) - 1)
      (fun n => -(Real.exp (-(2 * α)) * (Real.exp (2 * α) - Real.exp (-(2 * α))) / 2)
                  * ((2 * (T n : ℝ) + 1) / (K n : ℝ))) := by sorry

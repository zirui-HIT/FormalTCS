import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators

abbrev optimization_point (d : ℕ) :=
  EuclideanSpace ℝ (Fin d)

noncomputable def objective_hessian {d : ℕ}
    (f : optimization_point d → ℝ) (x : optimization_point d) :
    optimization_point d →L[ℝ] optimization_point d :=
  fderiv ℝ (gradient f) x

def has_lipschitz_gradient {d : ℕ}
    (f : optimization_point d → ℝ) (L1 : ℝ) : Prop :=
  ∀ x y, ‖gradient f x - gradient f y‖ ≤ L1 * ‖x - y‖

def has_lipschitz_hessian {d : ℕ}
    (f : optimization_point d → ℝ) (L2 : ℝ) : Prop :=
  ∀ x y, ‖objective_hessian f x - objective_hessian f y‖ ≤ L2 * ‖x - y‖

structure conversion_run (d K T : ℕ) (D eta delta : ℝ) where
  iterate : ℕ → optimization_point d
  displacement : ℕ → optimization_point d
  iterate_succ : ∀ n, iterate (n + 1) = iterate n + displacement n
  displacement_norm_le : ∀ n, ‖displacement n‖ ≤ D

noncomputable def conversion_midpoint {d K T : ℕ} {D eta delta : ℝ}
    (run : conversion_run d K T D eta delta) (n : ℕ) : optimization_point d :=
  (2 : ℝ)⁻¹ • (run.iterate n + run.iterate (n + 1))

noncomputable def episode_average {d K T : ℕ} {D eta delta : ℝ}
    (run : conversion_run d K T D eta delta) (k : ℕ) : optimization_point d :=
  (T : ℝ)⁻¹ •
    ∑ n ∈ Finset.range T, conversion_midpoint run (k * T + n)

noncomputable def episode_gradient_sum {d K T : ℕ} {D eta delta : ℝ}
    (f : optimization_point d → ℝ)
    (run : conversion_run d K T D eta delta) (k : ℕ) : optimization_point d :=
  ∑ n ∈ Finset.range T, gradient f (conversion_midpoint run (k * T + n))

noncomputable def episode_comparator {d K T : ℕ} {D eta delta : ℝ}
    (f : optimization_point d → ℝ)
    (run : conversion_run d K T D eta delta) (k : ℕ) : optimization_point d :=
  (-D / ‖episode_gradient_sum f run k‖) • episode_gradient_sum f run k

noncomputable def conversion_regret {d K T : ℕ} {D eta delta : ℝ}
    (f : optimization_point d → ℝ)
    (run : conversion_run d K T D eta delta)
    (u : ℕ → optimization_point d) : ℝ :=
  ∑ k ∈ Finset.range K, ∑ n ∈ Finset.range T,
    inner ℝ (gradient f (conversion_midpoint run (k * T + n)))
      (run.displacement (k * T + n) - u k)

def conversion_algorithm_execution
    {d K T : ℕ} {D eta delta L1 L2 : ℝ}
    (f : optimization_point d → ℝ)
    (run : conversion_run d K T D eta delta) : Prop :=
  ∃ model : ℕ → (optimization_point d →L[ℝ] optimization_point d),
    (∀ n < K * T, ‖model n‖ ≤ 2 * L1) ∧
    (∀ n < K * T, ∀ u, ‖u‖ ≤ D →
      inner ℝ (gradient f (conversion_midpoint run n)) (run.displacement n) +
          (2 : ℝ)⁻¹ * inner ℝ (run.displacement n) (model n (run.displacement n)) ≤
        inner ℝ (gradient f (conversion_midpoint run n)) u +
          (2 : ℝ)⁻¹ * inner ℝ u (model n u) + delta) ∧
    (∀ n < K * T, ∀ u, ‖u‖ ≤ D →
      -delta * ‖u - run.displacement n‖ ≤
        inner ℝ
          (gradient f (conversion_midpoint run n) + model n (run.displacement n))
          (u - run.displacement n)) ∧
    conversion_regret f run (episode_comparator f run) ≤
      D ^ 2 / (2 * eta) +
        eta / 2 *
          ∑ n ∈ Finset.range (K * T),
            ‖gradient f (conversion_midpoint run n) -
              model n (run.displacement n)‖ ^ 2 +
        delta * (K * T : ℕ) ∧
    D ^ 2 / (2 * eta) +
          eta / 2 *
            ∑ n ∈ Finset.range (K * T),
              ‖gradient f (conversion_midpoint run n) -
                model n (run.displacement n)‖ ^ 2 +
          delta * (K * T : ℕ) +
          D * (K * T : ℕ) * (L2 / 2 * (T : ℝ) ^ 2 * D ^ 2) ≤
      D * (K * T : ℕ) *
        (Real.rpow L2 ((8 : ℝ) / 5) * Real.rpow D ((13 : ℝ) / 5) /
            (8 * Real.rpow (d : ℝ) ((3 : ℝ) / 5) *
              Real.rpow L1 ((3 : ℝ) / 5)) +
          7 * Real.rpow 52 ((3 : ℝ) / 13) *
              Real.rpow (d : ℝ) ((2 : ℝ) / 5) *
              Real.rpow L1 ((7 : ℝ) / 5) * Real.rpow D ((3 : ℝ) / 5) /
            (Real.rpow L2 ((2 : ℝ) / 5) * (K * T : ℕ)))

def prescribed_parameters
    (d K T M : ℕ) (L1 L2 gap D eta delta : ℝ) : Prop :=
  0 < d ∧ 0 < K ∧ 0 < T ∧ 0 < M ∧
    0 < L1 ∧ 0 < L2 ∧ 0 < gap ∧ 0 < D ∧ 0 < eta ∧ 0 < delta ∧
    D =
      Real.rpow
        (gap /
          (52 * Real.rpow (d : ℝ) ((2 : ℝ) / 5) *
            Real.rpow L1 ((2 : ℝ) / 5) * Real.rpow L2 ((3 : ℝ) / 5) * (M : ℝ)))
        ((5 : ℝ) / 13) ∧
    eta =
      Real.rpow
        (1 /
          (24 * (d : ℝ) * L1 * Real.rpow L2 ((2 : ℝ) / 3) *
            Real.rpow D ((2 : ℝ) / 3)))
        ((3 : ℝ) / 5) ∧
    (T : ℝ) = 3 / Real.rpow (D * L2 * eta) ((1 : ℝ) / 3) ∧
    delta = D / (eta * (T : ℝ)) ∧
    K * T = M

noncomputable def convergence_rate_bound
    (d M : ℕ) (L1 L2 gap : ℝ) : ℝ :=
  2 * Real.rpow gap ((8 : ℝ) / 13) *
      Real.rpow
        (52 * Real.rpow L1 ((2 : ℝ) / 5) * Real.rpow L2 ((3 : ℝ) / 5))
        ((5 : ℝ) / 13) *
      Real.rpow (d : ℝ) ((2 : ℝ) / 13) /
      Real.rpow (M : ℝ) ((8 : ℝ) / 13) +
    L2 * gap / (416 * (d : ℝ) * L1 * (M : ℝ)) +
    7 * Real.rpow L1 ((17 : ℝ) / 13) * Real.rpow gap ((3 : ℝ) / 13) /
        Real.rpow L2 ((7 : ℝ) / 13) *
        Real.rpow (d : ℝ) ((4 : ℝ) / 13) /
        Real.rpow (M : ℝ) ((16 : ℝ) / 13) +
    Real.rpow L2 ((7 : ℝ) / 13) / 48 *
      Real.rpow
        (gap /
          (52 * Real.rpow (d : ℝ) ((2 : ℝ) / 5) *
            Real.rpow L1 ((2 : ℝ) / 5) * (M : ℝ)))
        ((10 : ℝ) / 13)

theorem convergence_rate_formal
    {d K T M : ℕ} {D eta delta L1 L2 fStar : ℝ}
    (f : optimization_point d → ℝ)
    (run : conversion_run d K T D eta delta)
    (h_smooth : ContDiff ℝ 2 f)
    (h_gradient : has_lipschitz_gradient f L1)
    (h_hessian : has_lipschitz_hessian f L2)
    (h_optimal : IsGLB (Set.range f) fStar)
    (h_execution : conversion_algorithm_execution (L1 := L1) (L2 := L2) f run)
    (h_parameters :
      prescribed_parameters d K T M L1 L2
        (f (run.iterate 0) - fStar) D eta delta) :
    (K : ℝ)⁻¹ *
        ∑ k ∈ Finset.range K, ‖gradient f (episode_average run k)‖ ≤
      convergence_rate_bound d M L1 L2 (f (run.iterate 0) - fStar) := by sorry

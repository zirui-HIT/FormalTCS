import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.ENNReal.Holder

set_option linter.all false
set_option maxHeartbeats 500000

open scoped Gradient

noncomputable def finite_lp_norm (p : ENNReal) {d : ℕ}
    (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ‖WithLp.toLp p (WithLp.ofLp z)‖

def l_smooth_with_respect_to_lp {d : ℕ} (p q : ENNReal) (L : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ x y,
    finite_lp_norm q (gradient f y - gradient f x) ≤
      L * finite_lp_norm p (y - x)

structure hasd_data (d : ℕ) where
  x : ℕ → EuclideanSpace ℝ (Fin d)
  y : ℕ → EuclideanSpace ℝ (Fin d)
  v : ℕ → EuclideanSpace ℝ (Fin d)
  A : ℕ → ℝ
  a : ℕ → ℝ
  rho : ℕ → ℝ
  psi : ℕ → EuclideanSpace ℝ (Fin d) → ℝ

def is_hasd_run {d : ℕ} (run : hasd_data d)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ) (p q : ENNReal)
    (T : ℕ) (x0 : EuclideanSpace ℝ (Fin d)) : Prop :=
  run.x 0 = x0 ∧
  run.A 0 = 0 ∧
  (∀ z, run.psi 0 z = (1 / 2 : ℝ) * ‖z - x0‖ ^ 2) ∧
  (∀ t, t ≤ T → IsMinOn (run.psi t) Set.univ (run.v t)) ∧
  ∀ t, t < T →
    0 < run.a (t + 1) ∧
    0 < run.rho t ∧
    run.A (t + 1) = run.A t + run.a (t + 1) ∧
    run.a (t + 1) ^ 2 =
      (run.A t + run.A (t + 1)) / (18 * L * run.rho t) ∧
    run.y t =
      (1 - run.a (t + 1) / run.A (t + 1)) • run.x t +
        (run.a (t + 1) / run.A (t + 1)) • run.v t ∧
    IsMinOn
      (fun z => inner ℝ (gradient f (run.y t)) (z - run.y t) +
        L * finite_lp_norm p (z - run.y t) ^ 2)
      Set.univ (run.x (t + 1)) ∧
    (1 / 2 : ℝ) *
        (‖gradient f (run.x (t + 1))‖ ^ 2 /
          finite_lp_norm q (gradient f (run.x (t + 1))) ^ 2) ≤ run.rho t ∧
    run.rho t ≤ 2 *
        (‖gradient f (run.x (t + 1))‖ ^ 2 /
          finite_lp_norm q (gradient f (run.x (t + 1))) ^ 2) ∧
    ∀ z,
      run.psi (t + 1) z = run.psi t z + run.a (t + 1) *
        (f (run.x (t + 1)) +
          inner ℝ (gradient f (run.x (t + 1))) (z - run.x (t + 1)))

noncomputable def average_gradient_ratio {d : ℕ} (run : hasd_data d)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (q : ENNReal) (T : ℕ) : ℝ :=
  (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
    finite_lp_norm q (gradient f (run.x (t + 1))) /
      ‖gradient f (run.x (t + 1))‖

theorem main {d T : ℕ} (hT : 0 < T) {p q : ENNReal}
    [hpq : ENNReal.HolderConjugate p q] (hp : (2 : ℝ) ≤ p.toReal)
    {L : ℝ} (hL : 0 < L) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hconv : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (hsmooth : l_smooth_with_respect_to_lp p q L f)
    (run : hasd_data d) (x0 xstar : EuclideanSpace ℝ (Fin d))
    (hrun : is_hasd_run run f L p q T x0) (hmin : ∀ z, f xstar ≤ f z) :
    f (run.x T) - f xstar ≤
      324 * L * ‖x0 - xstar‖ ^ 2 /
        (average_gradient_ratio run f q T ^ 2 * (T : ℝ) ^ 2) := by
  sorry

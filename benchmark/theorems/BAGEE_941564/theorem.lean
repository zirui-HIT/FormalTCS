import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option maxHeartbeats 500000

abbrev ba_vector (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def vector_average {d T : ℕ} (z : Fin T → ba_vector d) : ba_vector d :=
  (T : ℝ)⁻¹ • ∑ t, z t

def polar_target {d : ℕ} (S : Set (ba_vector d)) : Set (ba_vector d) :=
  {u | ∀ ⦃s⦄, s ∈ S → inner ℝ u s ≤ 0}

noncomputable def source_offset {d : ℕ}
    (p x θ : ba_vector d) : ba_vector d :=
  (2 * ‖p‖ / ‖x - θ‖) • (x - θ)

structure blackwell_problem (d : ℕ) (A B : Type) where
  payoff : A → B → ba_vector d
  target : Set (ba_vector d)
  bound : ℝ
  bound_nonnegative : 0 ≤ bound
  payoff_bounded : ∀ a b, ‖payoff a b‖ ≤ bound
  target_nonempty : target.Nonempty
  target_closed : IsClosed target
  target_convex : Convex ℝ target
  target_zero : (0 : ba_vector d) ∈ target
  target_add : ∀ ⦃x y⦄, x ∈ target → y ∈ target → x + y ∈ target
  target_smul : ∀ (c : ℝ), 0 ≤ c → ∀ ⦃x⦄, x ∈ target → c • x ∈ target
  halfspace_oracle : ba_vector d → A
  halfspace_condition : ∀ ⦃u⦄, u ∈ polar_target target →
    ∀ b, inner ℝ u (payoff (halfspace_oracle u) b) ≤ 0

structure geq_to_ba_execution {d : ℕ} {A B : Type}
    (P : blackwell_problem d A B)
    (error : ℝ → ℝ → ℕ → ℝ) (T : ℕ)
    (x : Fin T → ba_vector d) (a : Fin T → A) (b : Fin T → B)
    (barG : Fin T → ba_vector d → ba_vector d) where
  projected : Fin T → ba_vector d
  projected_mem : ∀ t, projected t ∈ polar_target P.target
  projection_inequality : ∀ t ⦃z⦄, z ∈ polar_target P.target →
    inner ℝ (x t - projected t) (z - projected t) ≤ 0
  action_eq : ∀ t, a t = P.halfspace_oracle (projected t)
  field_eq : ∀ t, barG t (x t) =
    P.payoff (a t) (b t) - source_offset (P.payoff (a t) (b t)) (x t) (projected t)
  geq_bound : ‖vector_average (fun t => barG t (x t))‖ ≤
    error (3 * P.bound) 0 T / (T : ℝ)

theorem geq_to_ba {d T : ℕ} {A B : Type}
    (P : blackwell_problem d A B) (error : ℝ → ℝ → ℕ → ℝ)
    (hT : 1 ≤ T) (x : Fin T → ba_vector d) (a : Fin T → A)
    (b : Fin T → B) (barG : Fin T → ba_vector d → ba_vector d)
    (run : geq_to_ba_execution P error T x a b barG) :
    Metric.infDist (vector_average (fun t => P.payoff (a t) (b t))) P.target ≤
        ‖vector_average (fun t => barG t (x t))‖ ∧
      ‖vector_average (fun t => barG t (x t))‖ ≤
        error (3 * P.bound) 0 T / (T : ℝ) := by
  sorry

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Nat.Choose.Basic

variable {X : Type*} [MetricSpace X] {Y : Type*}

def is_gamma_cover (γ : ℝ) (Z : Finset X) (φ : X → X) : Prop :=
  ∀ x : X, φ x ∈ Z ∧ φ x ∈ Metric.closedBall x γ

noncomputable def perturbed_loss (γ : ℝ) (h : X → Y) (x : X) (y : Y) : ℝ := by
  classical
  exact if ∀ z ∈ Metric.closedBall x γ, h z = y then 0 else 1

noncomputable def perturbed_opt (γ : ℝ) (H : Set (X → Y)) (T : ℕ)
    (xs : Fin T → X) (ys : Fin T → Y) : ℝ :=
  ⨅ h ∈ H, ∑ t, perturbed_loss γ h (xs t) (ys t)

noncomputable def projected_empirical_opt (H : Set (X → Y)) (φ : X → X) (T : ℕ)
    (xs : Fin T → X) (ys : Fin T → Y) : ℝ := by
  classical
  exact ⨅ h ∈ H, ∑ t, if h (φ (xs t)) = ys t then (0 : ℝ) else 1

theorem input_margin_upperbnd {γ : ℝ} (hγ : 0 < γ) {Z : Finset X} {φ : X → X}
    (hcover : is_gamma_cover γ Z φ) (H : Set (X → Y)) (T : ℕ)
    (xs : Fin T → X) (ys : Fin T → Y) (d : ℕ) (hd : 0 < d) (hdn : d ≤ Z.card)
    (m : ℕ) (hcount : m ≤ ∑ k ∈ Finset.range (d + 1), (Z.card).choose k)
    (expectedMistakes : ℝ)
    (hMW : ∀ η : ℝ, 0 < η →
      expectedMistakes ≤ (η / (1 - Real.exp (-η))) * projected_empirical_opt H φ T xs ys
        + (1 / (1 - Real.exp (-η))) * Real.log (m : ℝ)) :
    expectedMistakes - perturbed_opt γ H T xs ys
      ≤ Real.sqrt (2 * (T : ℝ) * ((d : ℝ) * Real.log (Real.exp 1 * (Z.card : ℝ) / (d : ℝ))))
        + (d : ℝ) * Real.log (Real.exp 1 * (Z.card : ℝ) / (d : ℝ)) := by sorry

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.InnerProductSpace.Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def beta_smooth_on (gradR : E → E) (K : Set E) (β : ℝ) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, ‖gradR x - gradR y‖ ≤ β * ‖x - y‖

noncomputable def bregman_div (R : E → ℝ) (gradR : E → E) (w w' : E) : ℝ :=
  R w - R w' - inner ℝ (gradR w') (w - w')

noncomputable def omd_objective (R : E → ℝ) (gradR : E → E) (η : ℝ) (ℓ wt w : E) : ℝ :=
  η * inner ℝ ℓ w + bregman_div R gradR w wt

def approx_omd_trajectory (R : E → ℝ) (gradR : E → E) (K : Set E) (η : ℝ)
    (ℓ w : ℕ → E) (T : ℕ) (ε : ℝ) : Prop :=
  ∀ t, 1 ≤ t → t ≤ T →
    w (t + 1) ∈ K ∧
      ∀ u ∈ K, omd_objective R gradR η (ℓ t) (w t) (w (t + 1))
        ≤ omd_objective R gradR η (ℓ t) (w t) u + ε

noncomputable def regret (ℓ w : ℕ → E) (u : E) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.Icc 1 T, inner ℝ (ℓ t) (w t))
    - (∑ t ∈ Finset.Icc 1 T, inner ℝ (ℓ t) u)

theorem ub_smooth :
    ∃ C : ℝ, 0 < C ∧
      ∀ (K : Set E) (R : E → ℝ) (gradR : E → E) (β D η ε : ℝ) (T : ℕ)
        (ℓ w : ℕ → E) (u : E),
        Convex ℝ K →
        (∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D) →
        0 < η → 0 < β →
        beta_smooth_on gradR K β →
        (∀ x ∈ K, HasGradientAt R (gradR x) x) →
        StrongConvexOn K 1 R →
        (∀ t, 1 ≤ t → t ≤ T → ‖ℓ t‖ ≤ 1) →
        approx_omd_trajectory R gradR K η ℓ w T ε →
        w 1 ∈ K → u ∈ K →
        0 ≤ ε → ε ≤ D ^ 2 / 2 →
        regret ℓ w u T ≤
          C * (η⁻¹ * bregman_div R gradR u (w 1) + (T : ℝ) * η
            + ((T : ℝ) * D * Real.sqrt (β * ε)) / η) := by
  sorry

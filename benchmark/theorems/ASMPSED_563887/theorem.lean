import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

set_option linter.all false
set_option maxHeartbeats 500000

open Matrix MeasureTheory
open scoped BigOperators

def matrix_quad_form {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) : ℝ :=
  ∑ i, v i * (M *ᵥ v) i

noncomputable def lambda_max {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  sSup (spectrum ℝ A)

def cumulative_step (η : ℕ → ℝ) (s : ℕ) : ℝ :=
  ∑ u ∈ Finset.range s, η u

noncomputable def memory_weighted_step (η : ℕ → ℝ) (r : ℝ) (t : ℕ) : ℝ :=
  ∑ s ∈ Finset.range t,
    Real.exp (-(r * (cumulative_step η t - cumulative_step η s)) / 4) * (η s) ^ 2

def psgd_iterate {d n : ℕ} {Z : Type*}
    (x0 : Fin d → ℝ) (η : ℕ → ℝ) (P : Matrix (Fin d) (Fin d) ℝ)
    (g : (Fin d → ℝ) → Z → (Fin d → ℝ)) (S : Fin n → Z) :
    (t : ℕ) → (Fin t → Fin n) → (Fin d → ℝ)
  | 0, _ => x0
  | t + 1, idx =>
      let prev := psgd_iterate x0 η P g S t (fun s => idx s.castSucc)
      prev - η t • (P *ᵥ g prev (S (idx (Fin.last t))))

def smooth_wrt_H {d : ℕ} {Z : Type*} (X : Set (Fin d → ℝ))
    (H : Matrix (Fin d) (Fin d) ℝ) (β : ℝ)
    (g : (Fin d → ℝ) → Z → (Fin d → ℝ)) : Prop :=
  ∀ (x : Fin d → ℝ), x ∈ X → ∀ (y : Fin d → ℝ), y ∈ X → ∀ (z : Z),
    matrix_quad_form H⁻¹ (g x z - g y z) ≤ β ^ 2 * matrix_quad_form H (x - y)

def contractivity_property {d : ℕ} {Z : Type*}
    (X : Set (Fin d → ℝ)) (P M : Matrix (Fin d) (Fin d) ℝ)
    (g : (Fin d → ℝ) → Z → (Fin d → ℝ)) (ηbar r : ℝ) : Prop :=
  ∀ (x : Fin d → ℝ), x ∈ X → ∀ (y : Fin d → ℝ), y ∈ X →
    ∀ (z : Z) (a : ℝ), 0 ≤ a → a ≤ ηbar →
    matrix_quad_form M ((x - a • (P *ᵥ g x z)) - (y - a • (P *ᵥ g y z)))
      ≤ (1 - a * r) * matrix_quad_form M (x - y)

noncomputable def gradient_covariance {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (Q : Measure Z) (g : (Fin d → ℝ) → Z → (Fin d → ℝ)) (x : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun j k =>
    ∫ z, (g x z j - ∫ z', g x z' j ∂Q) * (g x z k - ∫ z', g x z' k ∂Q) ∂Q

def gradient_covariance_bound {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (X : Set (Fin d → ℝ)) (Q : Measure Z)
    (g : (Fin d → ℝ) → Z → (Fin d → ℝ))
    (Sig : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (∀ x, x ∈ X → MemLp (fun z => g x z) 2 Q) ∧
    ∀ x, x ∈ X → (Sig - gradient_covariance Q g x).PosSemidef

noncomputable def on_average_parameter_stability_sq
    {d n : ℕ} {Z : Type*} [MeasurableSpace Z]
    (Q : Measure Z) (i : Fin n) (x0 : Fin d → ℝ) (η : ℕ → ℝ)
    (P M : Matrix (Fin d) (Fin d) ℝ)
    (g : (Fin d → ℝ) → Z → (Fin d → ℝ)) (t : ℕ) : ℝ :=
  ∫ S, (∫ z',
      ((n : ℝ) ^ t)⁻¹ *
        ∑ idx : Fin t → Fin n,
          matrix_quad_form M
            (psgd_iterate x0 η P g S t idx -
              psgd_iterate x0 η P g (Function.update S i z') t idx)
      ∂Q) ∂(Measure.pi fun _ : Fin n => Q)

noncomputable def psgd_stability_bound {d : ℕ}
    (n : ℕ) (η : ℕ → ℝ) (r : ℝ) (t : ℕ)
    (P M Sig : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  64 * (memory_weighted_step η r t / (8 * (n : ℝ)) +
      (1 - Real.exp (-(cumulative_step η t) * r / 4)) / ((n : ℝ) ^ 2 * r ^ 2)) *
    (P * M * P * Sig).trace

theorem psgd_gen_stab {d n t : ℕ} {Z : Type*} [MeasurableSpace Z]
    (Q : Measure Z) [IsProbabilityMeasure Q]
    (i : Fin n) (X : Set (Fin d → ℝ)) (x0 : Fin d → ℝ) (η : ℕ → ℝ)
    (H P M Sig : Matrix (Fin d) (Fin d) ℝ)
    (g : (Fin d → ℝ) → Z → (Fin d → ℝ))
    (β ηbar r : ℝ)
    (hx0 : x0 ∈ X)
    (hβ : 0 < β) (hηbar : 0 < ηbar) (hr : 0 < r)
    (hHpd : H.PosDef) (hPpd : P.PosDef) (hMpd : M.PosDef)
    (hHmax : lambda_max H = 1)
    (hsmooth : smooth_wrt_H X H β g)
    (hcontractive : contractivity_property X P M g ηbar r)
    (hcov : gradient_covariance_bound X Q g Sig)
    (hgMeasurable : Measurable (Function.uncurry g))
    (hiterate :
      ∀ (S : Fin n → Z) (s : ℕ), s ≤ t →
        ∀ idx : Fin s → Fin n, psgd_iterate x0 η P g S s idx ∈ X)
    (hinnerIntegrable :
      ∀ S : Fin n → Z,
        Integrable
          (fun z' =>
            ((n : ℝ) ^ t)⁻¹ *
              ∑ idx : Fin t → Fin n,
                matrix_quad_form M
                  (psgd_iterate x0 η P g S t idx -
                    psgd_iterate x0 η P g (Function.update S i z') t idx))
          Q)
    (houterIntegrable :
      Integrable
        (fun S =>
          ∫ z',
            ((n : ℝ) ^ t)⁻¹ *
              ∑ idx : Fin t → Fin n,
                matrix_quad_form M
                  (psgd_iterate x0 η P g S t idx -
                    psgd_iterate x0 η P g (Function.update S i z') t idx)
          ∂Q)
        (Measure.pi fun _ : Fin n => Q))
    (hstepNonneg : ∀ s, 0 ≤ η s)
    (hstepCap : ∀ s, η s ≤ min ηbar r⁻¹)
    (hsample :
      8 * β * Real.sqrt (lambda_max (H * P * M * P)) *
          Real.sqrt (lambda_max (M⁻¹ * H)) / r ≤ (n : ℝ)) :
    on_average_parameter_stability_sq Q i x0 η P M g t ≤
      psgd_stability_bound n η r t P M Sig := by sorry

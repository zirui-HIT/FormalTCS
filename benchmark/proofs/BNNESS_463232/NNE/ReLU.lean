/-
Copyright (c) 2026 Anthony Chang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Chang
-/

import Mathlib

/-!
# ReLU activation

This file defines the ReLU activation function.

We define the scalar activation `relu x = max x 0` and its componentwise lift
`reluV` on finite vectors `Fin n → ℝ`.
-/

namespace NNE

/-- Scalar ReLU activation, `relu x = max x 0`. -/
def relu (x : ℝ) : ℝ := max x 0

/-- Componentwise ReLU on a finite vector. -/
def reluV {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

@[simp] lemma relu_apply (x : ℝ) : relu x = max x 0 := rfl

@[simp] lemma reluV_apply {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    reluV x i = relu (x i) := rfl

/-- ReLU is nonnegative. -/
lemma relu_nonneg (x : ℝ) : 0 ≤ relu x := le_max_right x 0

/-- ReLU is the identity on nonnegative inputs. -/
lemma relu_of_nonneg {x : ℝ} (hx : 0 ≤ x) : relu x = x := max_eq_left hx

/-- ReLU vanishes on nonpositive inputs. -/
lemma relu_of_nonpos {x : ℝ} (hx : x ≤ 0) : relu x = 0 := max_eq_right hx

@[simp] lemma relu_zero : relu 0 = 0 := by simp [relu]

/-- The input never exceeds its ReLU. -/
lemma le_relu (x : ℝ) : x ≤ relu x := le_max_left x 0

/-- ReLU is monotone. -/
lemma monotone_relu : Monotone relu := fun _ _ h => max_le_max h le_rfl

/-- The decomposition of the identity through two ReLUs: `x = relu x - relu (-x)`. -/
lemma relu_sub_relu_neg (x : ℝ) : relu x - relu (-x) = x := by
  rcases le_total 0 x with hx | hx
  · rw [relu_of_nonneg hx, relu_of_nonpos (neg_nonpos.mpr hx), sub_zero]
  · rw [relu_of_nonpos hx, relu_of_nonneg (neg_nonneg.mpr hx), zero_sub, neg_neg]

/-- ReLU of a nonpositive-scaled input, useful as the companion of `relu_sub_relu_neg`. -/
lemma relu_neg_sub_relu (x : ℝ) : relu (-x) - relu x = -x := by
  have := relu_sub_relu_neg x; linarith

/-- The two ReLUs of `±t` sum to the absolute value: `relu t + relu (-t) = |t|`. -/
lemma relu_add_relu_neg (t : ℝ) : relu t + relu (-t) = |t| := by
  rcases le_total 0 t with h | h
  · rw [relu_of_nonneg h, relu_of_nonpos (by linarith), abs_of_nonneg h]
    ring
  · rw [relu_of_nonpos h, relu_of_nonneg (by linarith), abs_of_nonpos h]
    ring

/-- The ReLU gadget computing a binary maximum with a single hidden layer:
`relu (a - b) + relu b - relu (-b) = a ⊔ b`. -/
lemma relu_max_gadget (a b : ℝ) : relu (a - b) + relu b - relu (-b) = a ⊔ b := by
  rcases le_total a b with h | h
  · rw [relu_of_nonpos (by linarith : a - b ≤ 0), sup_eq_right.mpr h]
    have := relu_sub_relu_neg b
    linarith
  · rw [relu_of_nonneg (by linarith : (0 : ℝ) ≤ a - b), sup_eq_left.mpr h]
    have := relu_sub_relu_neg b
    linarith

/-- Symmetric second differences of ReLU vanish away from the kink. -/
lemma relu_second_diff_of_abs_le {c d : ℝ} (h : |d| ≤ |c|) :
    relu (c + d) + relu (c - d) - 2 * relu c = 0 := by
  rcases le_total 0 c with hc | hc
  · rw [abs_of_nonneg hc] at h
    have hd := abs_le.mp h
    rw [relu_of_nonneg (by linarith), relu_of_nonneg (by linarith), relu_of_nonneg hc]
    ring
  · rw [abs_of_nonpos hc] at h
    have hd := abs_le.mp h
    rw [relu_of_nonpos (by linarith), relu_of_nonpos (by linarith), relu_of_nonpos hc]
    ring

/-- `reluV` commutes with `Fin.append`. -/
lemma reluV_append {m₁ m₂ : ℕ} (u : Fin m₁ → ℝ) (v : Fin m₂ → ℝ) :
    reluV (Fin.append u v) = Fin.append (reluV u) (reluV v) := by
  funext k
  induction k using Fin.addCases with
  | left i => simp
  | right j => simp

/-- ReLU is continuous. -/
@[fun_prop]
lemma continuous_relu : Continuous relu := continuous_id.max continuous_const

/-- The componentwise ReLU is continuous. -/
@[fun_prop]
lemma continuous_reluV {n : ℕ} : Continuous (reluV (n := n)) :=
  continuous_pi fun i => continuous_relu.comp (continuous_apply i)

end NNE

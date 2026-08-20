import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

set_option maxHeartbeats 500000

open scoped Matrix

attribute [local instance] Matrix.instPartialOrder Matrix.instStarOrderedRing
  Matrix.instNonnegSpectrumClass Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable def matrix_inner_product {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  (Aᵀ * B).trace

noncomputable def bregman_divergence {m n : ℕ}
    (f : Matrix (Fin m) (Fin n) ℝ → ℝ)
    (grad : Matrix (Fin m) (Fin n) ℝ → Matrix (Fin m) (Fin n) ℝ)
    (U V : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  f U - f V - matrix_inner_product (grad V) (U - V)

noncomputable def cumulative_gradient {m n : ℕ}
    (G : ℕ → Matrix (Fin m) (Fin n) ℝ) (t : ℕ) : Matrix (Fin m) (Fin n) ℝ :=
  ∑ s ∈ Finset.Icc 1 t, G s

noncomputable def gradient_covariance {m n : ℕ}
    (G : ℕ → Matrix (Fin m) (Fin n) ℝ) (t : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  ∑ s ∈ Finset.Icc 1 t, G s * (G s)ᵀ

noncomputable def preconditioner {m n : ℕ} (Gconst : ℝ)
    (G : ℕ → Matrix (Fin m) (Fin n) ℝ) (t : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  CFC.sqrt (Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) + gradient_covariance G t)

noncomputable def learning_rate (alpha beta : ℝ) : ℝ :=
  Real.sqrt (alpha / beta)

structure admissible_smoothing (m n : ℕ) where
  opNorm : Matrix (Fin m) (Fin n) ℝ → ℝ
  nucNorm : Matrix (Fin m) (Fin n) ℝ → ℝ
  pot : Matrix (Fin m) (Fin n) ℝ → Matrix (Fin m) (Fin m) ℝ → ℝ
  gradPot : Matrix (Fin m) (Fin n) ℝ → Matrix (Fin m) (Fin m) ℝ → Matrix (Fin m) (Fin n) ℝ
  alpha : ℝ
  beta : ℝ
  alpha_pos : 0 < alpha
  beta_pos : 0 < beta
  gradPot_is_gradient : ∀ (X : Matrix (Fin m) (Fin n) ℝ) (L : Matrix (Fin m) (Fin m) ℝ),
    L.PosDef →
      DifferentiableAt ℝ (fun Z => pot Z L) X ∧
        ∀ H, fderiv ℝ (fun Z => pot Z L) X H = matrix_inner_product (gradPot X L) H
  feasibility : ∀ (X : Matrix (Fin m) (Fin n) ℝ) (L : Matrix (Fin m) (Fin m) ℝ),
    L.PosSemidef → opNorm (gradPot X L) ≤ 1
  dominance_ge : ∀ (X : Matrix (Fin m) (Fin n) ℝ) (L : Matrix (Fin m) (Fin m) ℝ),
    L.PosSemidef → nucNorm X ≤ pot X L
  dominance_zero : ∀ (X : Matrix (Fin m) (Fin n) ℝ), pot X 0 = nucNorm X
  upper_stability : ∀ (X : Matrix (Fin m) (Fin n) ℝ) (L₁ L₂ : Matrix (Fin m) (Fin m) ℝ),
    L₁.PosSemidef → (L₂ - L₁).PosSemidef →
      pot X L₂ - pot X L₁ ≤ alpha * (L₂.trace - L₁.trace)
  smoothness : ∀ (X Y : Matrix (Fin m) (Fin n) ℝ) (L : Matrix (Fin m) (Fin m) ℝ),
    L.PosDef →
      bregman_divergence (fun Z => pot Z L) (fun Z => gradPot Z L) Y X
        ≤ (beta / 2) * ((X - Y)ᵀ * L⁻¹ * (X - Y)).trace
  nucNorm_dual : ∀ (A : Matrix (Fin m) (Fin n) ℝ) (D : ℝ), 0 ≤ D →
    sInf ((fun Y => matrix_inner_product A Y) ''
        {Y : Matrix (Fin m) (Fin n) ℝ | opNorm Y ≤ D})
      = -D * nucNorm A
  nucNorm_normalization : ∀ (A : Matrix (Fin m) (Fin n) ℝ),
    nucNorm A = (CFC.sqrt (Aᵀ * A)).trace
  opNorm_normalization : ∀ (A : Matrix (Fin m) (Fin n) ℝ) (c : ℝ),
    opNorm A ≤ c → (c ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) - A * Aᵀ).PosSemidef

structure gbpa_run {m n : ℕ} (S : admissible_smoothing m n) where
  G : ℕ → Matrix (Fin m) (Fin n) ℝ
  X : ℕ → Matrix (Fin m) (Fin n) ℝ
  D : ℝ
  D_pos : 0 < D
  Gconst : ℝ
  Gconst_nonneg : 0 ≤ Gconst
  T : ℕ
  T_pos : 1 ≤ T
  grad_bound : ∀ t, 1 ≤ t → t ≤ T → S.opNorm (G t) ≤ Gconst
  init : X 1 = 0
  update : ∀ t, 1 ≤ t → t < T →
    X (t + 1) =
      (-D) • S.gradPot (cumulative_gradient G t)
        ((learning_rate S.alpha S.beta)⁻¹ • preconditioner Gconst G t)

noncomputable def regret {m n : ℕ} (opNorm : Matrix (Fin m) (Fin n) ℝ → ℝ)
    (G X : ℕ → Matrix (Fin m) (Fin n) ℝ) (D : ℝ) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.Icc 1 T, matrix_inner_product (G t) (X t))
    - sInf ((fun Y => ∑ t ∈ Finset.Icc 1 T, matrix_inner_product (G t) Y) ''
        {Y : Matrix (Fin m) (Fin n) ℝ | opNorm Y ≤ D})

theorem main {m n : ℕ} (S : admissible_smoothing m n) (run : gbpa_run S) :
    regret S.opNorm run.G run.X run.D run.T ≤
      2 * Real.sqrt (S.alpha * S.beta) * run.D
          * (preconditioner run.Gconst run.G run.T).trace
      + (1 - Real.sqrt (S.alpha * S.beta)) * run.D * S.nucNorm (run.G 1) := by sorry

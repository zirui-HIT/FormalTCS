import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Algebra.Order.Star.Real

open Matrix BigOperators
open scoped Matrix.Norms.L2Operator

namespace ThresholdRank

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def topThresholdRank
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (τ : ℝ) : ℕ :=
  Fintype.card { i : n // τ ≤ hA.eigenvalues i }

noncomputable def bottomThresholdRank
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (μ : ℝ) : ℕ :=
  Fintype.card { i : n // hA.eigenvalues i ≤ -μ }

theorem small_top_rank_implies_small_bottom_rank
    [Nonempty n] (A : Matrix n n ℝ)
    (hHerm : A.IsHermitian)
    (hNonneg : ∀ i j, 0 ≤ A i j)
    (hOp : ‖A‖ ≤ (1 : ℝ))
    {τ : ℝ} (hτ : 0 ≤ τ) {s : ℕ}
    (htop : topThresholdRank A hHerm τ ≤ s)
    {σ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) :
    (bottomThresholdRank A hHerm (Real.sqrt (σ + τ * (1 - σ))) : ℝ)
      ≤ s / (σ^2) := by sorry

end ThresholdRank

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

/-!
  # Large bottom rank implies large top rank (BHSV25 Theorem 4.1)

  Common definitions and basic lemmas used by the later sections.
-/

namespace ThresholdRank

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
private lemma real_matrix_map_starRingEnd_eq (A : Matrix n n ℝ) :
    A.map (starRingEnd ℝ) = A := by
  ext i j
  simp

/-- Top threshold rank: number of eigenvalues `≥ τ`. -/
noncomputable def topThresholdRank
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (τ : ℝ) : ℕ :=
  Fintype.card { i : n // τ ≤ hA.eigenvalues i }

/-- Bottom threshold rank: number of eigenvalues `≤ -μ`. -/
noncomputable def bottomThresholdRank
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (μ : ℝ) : ℕ :=
  Fintype.card { i : n // hA.eigenvalues i ≤ -μ }

@[simp]
lemma topThresholdRank_nonneg (A : Matrix n n ℝ) (hA : A.IsHermitian) (τ : ℝ) :
    0 ≤ topThresholdRank A hA τ := Nat.zero_le _

@[simp]
lemma bottomThresholdRank_nonneg (A : Matrix n n ℝ) (hA : A.IsHermitian) (μ : ℝ) :
    0 ≤ bottomThresholdRank A hA μ := Nat.zero_le _

/-! ### Monotonicity -/

lemma topThresholdRank_antitone
    (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    Antitone (fun τ => topThresholdRank A hA τ) := by
  classical
  intro τ₁ τ₂ hτ
  simpa only [topThresholdRank] using
    (Fintype.card_subtype_mono
      (p := fun i => τ₂ ≤ hA.eigenvalues i)
      (q := fun i => τ₁ ≤ hA.eigenvalues i)
      (fun _ hi => hτ.trans hi))

lemma topThresholdRank_mono
    (A : Matrix n n ℝ) (hA : A.IsHermitian)
    {τ₁ τ₂ : ℝ} (hτ : τ₁ ≤ τ₂) :
    topThresholdRank A hA τ₂ ≤ topThresholdRank A hA τ₁ :=
  topThresholdRank_antitone A hA hτ

lemma bottomThresholdRank_antitone
    (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    Antitone (fun μ : ℝ => bottomThresholdRank A hA μ) := by
  classical
  intro μ₁ μ₂ hμ
  simpa only [bottomThresholdRank] using
    (Fintype.card_subtype_mono
      (p := fun i => hA.eigenvalues i ≤ -μ₂)
      (q := fun i => hA.eigenvalues i ≤ -μ₁)
      (fun _ hi => hi.trans (neg_le_neg hμ)))

lemma bottomThresholdRank_mono
    (A : Matrix n n ℝ) (hA : A.IsHermitian)
    {μ₁ μ₂ : ℝ} (hμ : μ₁ ≤ μ₂) :
    bottomThresholdRank A hA μ₂ ≤ bottomThresholdRank A hA μ₁ :=
  bottomThresholdRank_antitone A hA hμ

/-! ### Trivial bounds -/

lemma topThresholdRank_le_card
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (τ : ℝ) :
    topThresholdRank A hA τ ≤ Fintype.card n := by
  classical
  simpa only [topThresholdRank] using
    (Fintype.card_subtype_le (p := fun i : n => τ ≤ hA.eigenvalues i))

lemma bottomThresholdRank_le_card
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (μ : ℝ) :
    bottomThresholdRank A hA μ ≤ Fintype.card n := by
  classical
  simpa only [bottomThresholdRank] using
    (Fintype.card_subtype_le (p := fun i : n => hA.eigenvalues i ≤ -μ))

/-! ### Frobenius / Hilbert–Schmidt structures -/

noncomputable def frobeniusSq {n : Type*} [Fintype n] (M : Matrix n n ℝ) : ℝ :=
  ∑ i, ∑ j, (M i j)^2

noncomputable def frobeniusInner {n : Type*} [Fintype n]
    (A B : Matrix n n ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * B i j

lemma frobeniusInner_trace {n : Type*} [Fintype n] (A B : Matrix n n ℝ) :
    frobeniusInner A B = Matrix.trace (Matrix.transpose A * B) := by
  classical
  have htrace :
      Matrix.trace (Matrix.transpose A * B) = ∑ i, ∑ j, A j i * B j i := by
    simp only [trace, transpose, diag_apply, mul_apply, of_apply]
  have hswap :
      frobeniusInner A B = ∑ i, ∑ j, A j i * B j i := by
    simpa only [frobeniusInner] using
      (Finset.sum_comm (s := (Finset.univ : Finset n)) (t := Finset.univ)
        (f := fun   i j => A i j * B i j))
  calc
    frobeniusInner A B = _ := hswap
    _ = Matrix.trace (Matrix.transpose A * B) := htrace.symm

lemma frobeniusSq_trace {n : Type*} [Fintype n] (M : Matrix n n ℝ) :
    frobeniusSq M = Matrix.trace (Matrix.transpose M * M) := by
  classical
  simpa only [frobeniusSq, pow_two, frobeniusInner] using
    (frobeniusInner_trace (A := M) (B := M))

lemma frobeniusInner_diagonalization
    (U : Matrix n n ℝ) (hU : U ∈ Matrix.unitaryGroup n ℝ)
    (d : n → ℝ) (A M : Matrix n n ℝ)
    (hA : A = U * Matrix.diagonal d * Uᴴ) (hHerm : A.IsHermitian) :
    frobeniusInner A M = ∑ i, d i * (Uᴴ * M * U) i i := by
  classical
  have _ := hU
  let M' := Uᴴ * M * U
  have hA_symm : Aᵀ = A := by
    simpa [conjTranspose, real_matrix_map_starRingEnd_eq] using hHerm.eq
  have hcycle := Matrix.trace_mul_cycle (A := U) (B := Matrix.diagonal d) (C := Uᴴ * M)
  have hcomm := Matrix.trace_mul_comm (A := M') (B := Matrix.diagonal d)
  calc
    frobeniusInner A M = Matrix.trace (Aᵀ * M) := frobeniusInner_trace _ _
    _ = Matrix.trace (U * Matrix.diagonal d * Uᴴ * M) := by
          simp only [hA, conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc, transpose_mul,
            transpose_transpose, diagonal_transpose]
    _ = Matrix.trace (M' * Matrix.diagonal d) := by
          simpa only [conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc, M'] using hcycle
    _ = Matrix.trace (Matrix.diagonal d * M') := by
          simpa only [conjTranspose_eq_transpose_of_trivial, M'] using hcomm
    _ = ∑ i, d i * (Uᴴ * M * U) i i := by
      simp only [trace, conjTranspose_eq_transpose_of_trivial, diag_apply, mul_apply,
        diagonal_apply, transpose_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        ↓reduceIte, M']

lemma trace_conjUnitary
    (U : Matrix n n ℝ) (hU : U ∈ Matrix.unitaryGroup n ℝ) (A : Matrix n n ℝ) :
    Matrix.trace (Matrix.conjTranspose U * A * U) = Matrix.trace A := by
  classical
  have hU_mul_left : U * Uᴴ = (1 : Matrix n n ℝ) :=
    (Matrix.mem_unitaryGroup_iff).mp hU
  have hU_mul_transpose : U * Uᵀ = (1 : Matrix n n ℝ) := by
    simpa [conjTranspose, real_matrix_map_starRingEnd_eq] using hU_mul_left
  calc
    Matrix.trace (Uᴴ * A * U)
        = Matrix.trace (A * U * Uᴴ) := by
            simpa only [conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using
              (Matrix.trace_mul_cycle (A := A) (B := U) (C := Uᴴ)).symm
    _ = Matrix.trace (A * 1) := by
          simp only [conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc, hU_mul_transpose,
            mul_one]
    _ = Matrix.trace A := by simp only [mul_one]

lemma frobeniusSq_conjUnitary
    (U : Matrix n n ℝ) (hU : U ∈ Matrix.unitaryGroup n ℝ) (M : Matrix n n ℝ) :
    frobeniusSq (Uᴴ * M * U) = frobeniusSq M := by
  classical
  have hU_mul_left : U * Uᴴ = (1 : Matrix n n ℝ) :=
    (Matrix.mem_unitaryGroup_iff).mp hU
  have hU_mul_right : Uᴴ * U = (1 : Matrix n n ℝ) :=
    (Matrix.mem_unitaryGroup_iff').mp hU
  calc
    frobeniusSq (Uᴴ * M * U)
        = Matrix.trace ((Uᴴ * M * U)ᵀ * (Uᴴ * M * U)) := frobeniusSq_trace _
    _ = Matrix.trace (Uᴴ * Mᵀ * U * Uᴴ * M * U) := by
          simp only [conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc, transpose_mul,
            transpose_transpose]
    _ = Matrix.trace (Mᵀ * U * Uᴴ * M * U * Uᴴ) := by
          simpa only [conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using
            (Matrix.trace_mul_comm (A := Uᴴ) (B := Mᵀ * U * Uᴴ * M * U))
    _ = Matrix.trace (Mᵀ * (U * Uᴴ) * M * (U * Uᴴ)) := by
          simp only [conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc]
    _ = Matrix.trace (Mᵀ * M) := by
          have hUUtrans : U * Uᵀ = (1 : Matrix n n ℝ) := by
            simpa [conjTranspose, real_matrix_map_starRingEnd_eq] using hU_mul_left
          have hUtransU : Uᵀ * U = (1 : Matrix n n ℝ) := by
            simpa [conjTranspose, real_matrix_map_starRingEnd_eq] using hU_mul_right
          simp only [conjTranspose_eq_transpose_of_trivial, hUUtrans, mul_one]
    _ = frobeniusSq M := by symm; exact frobeniusSq_trace M

lemma posSemidef_diag_nonneg {n : Type*} [Fintype n]
    {M : Matrix n n ℝ} (hM : Matrix.PosSemidef M) (i : n) :
    0 ≤ M i i := by
  exact hM.diag_nonneg

lemma frobeniusSq_nonneg {n : Type*} [Fintype n] (M : Matrix n n ℝ) :
    0 ≤ frobeniusSq M := by
  classical
  unfold frobeniusSq
  positivity

/-! ### Eigenvalue bounds -/

def eigenvaluesBounded (A : Matrix n n ℝ) (hA : A.IsHermitian) : Prop :=
  ∀ i, |hA.eigenvalues i| ≤ 1

/-! ### Eigenvalues bounded by operator norm

We need that `‖A‖ ≤ 1` (ℓ²-operator norm) implies all eigenvalues are in `[-1,1]`. -/

section EigenvalueBound

variable (A : Matrix n n ℝ)

/-- Helper: eigenvalues of a Hermitian real matrix belong to its real spectrum. -/
lemma eigenvalue_mem_spectrum_real
    (hA : A.IsHermitian) (i : n) :
    hA.eigenvalues i ∈ spectrum ℝ A := by
  classical
  -- Use the library lemma.
  simpa only using (Matrix.IsHermitian.eigenvalues_mem_spectrum_real (A := A) hA i)

/-- If `A` is Hermitian and `‖A‖ ≤ 1` for the ℓ²-operator norm, then all eigenvalues
lie in `[-1,1]`. -/
theorem eigenvaluesBounded_of_opNorm_le_one [Nonempty n]
    (hA : A.IsHermitian) (hOp : ‖A‖ ≤ (1 : ℝ)) :
    eigenvaluesBounded A hA := by
  classical
  intro i
  -- Each eigenvalue belongs to the (real) spectrum of `A`.
  have hmem : hA.eigenvalues i ∈ spectrum ℝ A :=
    eigenvalue_mem_spectrum_real (A := A) hA i
  -- Points in the spectrum lie in the closed ball of radius ‖A‖.
  have hball := (spectrum.subset_closedBall_norm (a := A)) hmem
  have hnorm : ‖hA.eigenvalues i‖ ≤ ‖A‖ := by
    simpa only [Real.norm_eq_abs, Metric.mem_closedBall, dist_eq_norm, sub_zero] using hball
  have hnorm' : ‖hA.eigenvalues i‖ ≤ 1 := hnorm.trans hOp
  -- Switch to absolute value for real numbers.
  simpa only [ge_iff_le, Real.norm_eq_abs] using hnorm'

end EigenvalueBound

end ThresholdRank

import Colorexpanders.Base
import Colorexpanders.Lemma4_3

open Matrix BigOperators
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

namespace ThresholdRank

variable {n : Type*} [Fintype n] [DecidableEq n]

section Lemma4_4_new

variable (A : Matrix n n ℝ) (hHerm : A.IsHermitian)

/-- Indices of eigenvalues `≤ -μ`, packaged as a finite type. -/
@[simp] abbrev negEigSubtype (μ : ℝ) :=
  { i : n // hHerm.eigenvalues i ≤ -μ }

/-- First `t` indices among the negative eigenvalues. -/
noncomputable def negEigIdx {μ : ℝ} {t : ℕ}
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    Fin t → n := fun s =>
  let hcard :
      t ≤ Fintype.card (negEigSubtype (A := A) (hHerm := hHerm) (μ := μ)) := by
        simpa only [negEigSubtype, bottomThresholdRank, ge_iff_le] using hBottom
  ((Fintype.equivFin (negEigSubtype (A := A) (hHerm := hHerm) (μ := μ))).symm
      (Fin.castLE hcard s)).1

/-- Matrix whose columns are the chosen eigenvectors, scaled by `1/√t`. -/
noncomputable def negEigenMatrixScaled {μ : ℝ} {t : ℕ} (_ : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    Matrix n (Fin t) ℝ :=
  let U : Matrix n n ℝ := hHerm.eigenvectorUnitary
  fun i s => (1 / Real.sqrt (t : ℝ)) *
    U i (negEigIdx (A := A) (hHerm := hHerm) hBottom s)

/-- Rows `wᵢ` of the scaled eigenvector matrix. -/
noncomputable def negRowVec {μ : ℝ} {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i : n) :
    Fin t → ℝ :=
  fun s => negEigenMatrixScaled (A := A) (hHerm := hHerm) ht hBottom i s

/-- `‖wᵢ‖₂`. -/
noncomputable def negRowNorm {μ : ℝ} {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i : n) : ℝ :=
  Real.sqrt (∑ s, (negRowVec (A := A) (hHerm := hHerm) ht hBottom i s)^2)

/-- Tensor-square vector `(wᵢ ⊗ wᵢ) / ‖wᵢ‖` flattened to `Fin t × Fin t → ℝ`. -/
noncomputable def negTensorVec {μ : ℝ} {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i : n) :
    Fin t × Fin t → ℝ :=
  fun p =>
    let r := negRowNorm (A := A) (hHerm := hHerm) ht hBottom i
    if _ : r = 0 then 0
    else (negRowVec (A := A) (hHerm := hHerm) ht hBottom i p.1 *
          negRowVec (A := A) (hHerm := hHerm) ht hBottom i p.2) / r

/-- Matrix `V` with columns `vᵢ`. -/
noncomputable def negVmatrix {μ : ℝ} {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    Matrix (Fin t × Fin t) n ℝ :=
  fun p i => negTensorVec (A := A) (hHerm := hHerm) ht hBottom i p

/-- Corresponding eigenvalues. -/
noncomputable def negEigValues {μ : ℝ} {t : ℕ}
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    Fin t → ℝ :=
  fun s => hHerm.eigenvalues
    (negEigIdx (A := A) (hHerm := hHerm) hBottom s)

/-- Scaled block and its projector. -/
noncomputable def UsMatrix {μ : ℝ} {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    Matrix n (Fin t) ℝ :=
  negEigenMatrixScaled (A := A) (hHerm := hHerm) ht hBottom

@[simp] lemma UsMatrix_eq_negEigenMatrixScaled {μ : ℝ} {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    UsMatrix (A := A) (hHerm := hHerm) ht hBottom =
      negEigenMatrixScaled (A := A) (hHerm := hHerm) ht hBottom := rfl

noncomputable def Pproj {μ : ℝ} {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    Matrix n n ℝ :=
  UsMatrix (A := A) (hHerm := hHerm) ht hBottom *
    (UsMatrix (A := A) (hHerm := hHerm) ht hBottom)ᵀ

/-- Witness matrix `M := Vᵀ * V`. -/
noncomputable def negWitnessM {μ : ℝ} {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    Matrix n n ℝ :=
  (negVmatrix (A := A) (hHerm := hHerm) ht hBottom)ᵀ *
    (negVmatrix (A := A) (hHerm := hHerm) ht hBottom)

/-- Gram matrices are PSD. -/
lemma negWitnessM_posSemidef {μ : ℝ} {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    Matrix.PosSemidef (negWitnessM (A := A) (hHerm := hHerm) ht hBottom) := by
  classical
  let V := negVmatrix (A := A) (hHerm := hHerm) ht hBottom
  simpa only [negWitnessM, conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self (A := V)

/-- The selection map `negEigIdx` is injective. -/
lemma negEigIdx_injective {μ : ℝ} {t : ℕ}
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    Function.Injective (negEigIdx (A := A) (hHerm := hHerm) hBottom) := by
  classical
  have hcard :
      t ≤ Fintype.card (negEigSubtype (A := A) (hHerm := hHerm) (μ := μ)) := by
    simpa only [negEigSubtype, bottomThresholdRank, ge_iff_le] using hBottom
  intro a b hab
  exact Fin.castLE_injective hcard <|
    (Fintype.equivFin (negEigSubtype (A := A) (hHerm := hHerm) (μ := μ))).symm.injective
      (Subtype.ext hab)

/-- Orthonormal columns (up to the scaling `1/√t`). -/
lemma negEigenMatrixScaled_orthonormal {μ : ℝ} {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    (negEigenMatrixScaled (A := A) (hHerm := hHerm) ht hBottom)ᵀ *
      negEigenMatrixScaled (A := A) (hHerm := hHerm) ht hBottom =
      (1 / (t : ℝ)) • (1 : Matrix (Fin t) (Fin t) ℝ) := by
  classical
  let U : Matrix n n ℝ := hHerm.eigenvectorUnitary
  have hU_mul : Uᵀ * U = (1 : Matrix n n ℝ) :=
    (Matrix.mem_unitaryGroup_iff').mp hHerm.eigenvectorUnitary.2
  let Us := negEigenMatrixScaled (A := A) (hHerm := hHerm) ht hBottom
  have ht_nonneg : 0 ≤ (t : ℝ) := by exact_mod_cast (Nat.zero_le t)
  ext s r
  have hscalar : (1 / Real.sqrt (t : ℝ)) * (1 / Real.sqrt (t : ℝ)) = 1 / (t : ℝ) := by
    have hsqrt' : Real.sqrt (t : ℝ) * Real.sqrt (t : ℝ) = t := by
      simp only [Nat.cast_nonneg, Real.mul_self_sqrt]
    calc
      (1 / Real.sqrt (t : ℝ)) * (1 / Real.sqrt (t : ℝ))
          = 1 / (Real.sqrt (t : ℝ) * Real.sqrt (t : ℝ)) := by ring
      _ = 1 / (t : ℝ) := by simp only [hsqrt', one_div]
  have hscalar' : (Real.sqrt (t : ℝ))⁻¹ * (Real.sqrt (t : ℝ))⁻¹ = (t : ℝ)⁻¹ := by
    simpa only [one_div] using hscalar
  have hsum :
      ∑ i, Us i s * Us i r =
        (1 / (t : ℝ)) *
          (Uᵀ * U)
            (negEigIdx (A := A) (hHerm := hHerm) hBottom s)
            (negEigIdx (A := A) (hHerm := hHerm) hBottom r) := by
    calc
      ∑ i, Us i s * Us i r
          = (Real.sqrt (t : ℝ))⁻¹ *
              ((Real.sqrt (t : ℝ))⁻¹ *
                ∑ i,
                  U i (negEigIdx (A := A) (hHerm := hHerm) hBottom s) *
                    U i (negEigIdx (A := A) (hHerm := hHerm) hBottom r)) := by
            simp only [negEigenMatrixScaled, one_div, IsHermitian.eigenvectorUnitary_apply,
              mul_left_comm, mul_assoc, Finset.mul_sum, Us, U]
      _ = (1 / (t : ℝ)) *
              ∑ i,
                U i (negEigIdx (A := A) (hHerm := hHerm) hBottom s) *
                  U i (negEigIdx (A := A) (hHerm := hHerm) hBottom r) := by
            have h := hscalar'
            have hassoc :
                (Real.sqrt (t : ℝ))⁻¹ *
                    ((Real.sqrt (t : ℝ))⁻¹ * ∑ i, U i (negEigIdx (A := A) (hHerm := hHerm)
                       hBottom s) * U i
                        (negEigIdx (A := A) (hHerm := hHerm) hBottom r))
                  = (Real.sqrt (t : ℝ))⁻¹ * (Real.sqrt (t : ℝ))⁻¹ *
                      ∑ i, U i (negEigIdx (A := A) (hHerm := hHerm) hBottom s) *
                        U i (negEigIdx (A := A) (hHerm := hHerm) hBottom r) := by
              ring
            calc
              (Real.sqrt (t : ℝ))⁻¹ *
                  ((Real.sqrt (t : ℝ))⁻¹ *
                    ∑ i, U i (negEigIdx (A := A) (hHerm := hHerm) hBottom s) *
                      U i (negEigIdx (A := A) (hHerm := hHerm) hBottom r))
                  = (Real.sqrt (t : ℝ))⁻¹ * (Real.sqrt (t : ℝ))⁻¹ *
                      ∑ i, U i (negEigIdx (A := A) (hHerm := hHerm) hBottom s) *
                        U i (negEigIdx (A := A) (hHerm := hHerm)
                           hBottom r) := hassoc
              _ = (1 / (t : ℝ)) *
                      ∑ i, U i (negEigIdx (A := A) (hHerm := hHerm) hBottom s) *
                        U i (negEigIdx (A := A) (hHerm := hHerm) hBottom r) := by
                    simp only [h, one_div]
      _ = (1 / (t : ℝ)) *
            (Uᵀ * U)
              (negEigIdx (A := A) (hHerm := hHerm) hBottom s)
              (negEigIdx (A := A) (hHerm := hHerm) hBottom r) := by
            simp only [one_div, IsHermitian.eigenvectorUnitary_apply, mul_apply, transpose_apply, U]
  have hdelta :
      (Uᵀ * U)
          (negEigIdx (A := A) (hHerm := hHerm) hBottom s)
          (negEigIdx (A := A) (hHerm := hHerm) hBottom r)
        = if negEigIdx (A := A) (hHerm := hHerm) hBottom s =
            negEigIdx (A := A) (hHerm := hHerm) hBottom r
          then 1 else 0 := by
    have := congrArg (fun M =>
        M (negEigIdx (A := A) (hHerm := hHerm) hBottom s)
          (negEigIdx (A := A) (hHerm := hHerm) hBottom r)) hU_mul
    simpa only [one_apply] using this
  have hinj := negEigIdx_injective (A := A) (hHerm := hHerm) hBottom
  have hsr :
      (negEigIdx (A := A) (hHerm := hHerm) hBottom s =
        negEigIdx (A := A) (hHerm := hHerm) hBottom r) ↔ s = r :=
    hinj.eq_iff
  calc
    ((Usᵀ * Us) s r) =
        ∑ i, Us i s * Us i r := by simp only [mul_apply, transpose_apply, Us]
    _ = (1 / (t : ℝ)) *
        (Uᵀ * U)
          (negEigIdx (A := A) (hHerm := hHerm) hBottom s)
          (negEigIdx (A := A) (hHerm := hHerm) hBottom r) := by
          exact hsum
    _ = (1 / (t : ℝ)) * (if s = r then 1 else 0) := by
          simpa only [one_div, mul_ite, mul_one, mul_zero, hsr] using
            congrArg (fun x => (1 / (t : ℝ)) * x) hdelta
    _ = ((1 / (t : ℝ)) • (1 : Matrix (Fin t) (Fin t) ℝ)) s r := by
          simp only [Matrix.smul_apply, smul_eq_mul, one_apply]

/-- Tensor-square identity: the Frobenius norm of `w ⊗ w` is `‖w‖^4`. -/
lemma tensorSquare_sum_sq {t : ℕ} (u : Fin t → ℝ) :
    ∑ p : Fin t × Fin t, (u p.1 * u p.2)^2 = (∑ s : Fin t, (u s)^2)^2 := by
  classical
  calc
    ∑ p : Fin t × Fin t, (u p.1 * u p.2)^2
        = ∑ i, ∑ j, (u i * u j)^2 := by
            simpa only [Finset.univ_product_univ] using
              (Finset.sum_product (s := Finset.univ) (t := Finset.univ) (f :=
                fun p : Fin t × Fin t => (u p.1 * u p.2) ^ 2))
    _ = ∑ i, ∑ j, (u i)^2 * (u j)^2 := by
            refine Finset.sum_congr rfl ?_ ; intro i _;
              refine Finset.sum_congr rfl ?_; intro j _; ring
    _ = (∑ i, (u i)^2) * ∑ j, (u j)^2 := by
            simp only [Finset.mul_sum, mul_comm]
    _ = (∑ s : Fin t, (u s)^2) ^ 2 := by ring

/-- Mixed tensor-square identity. -/
lemma tensorSquare_sum_mul {t : ℕ} (u v : Fin t → ℝ) :
    ∑ p : Fin t × Fin t, (u p.1 * u p.2) * (v p.1 * v p.2) =
      (∑ s : Fin t, u s * v s) ^ 2 := by
  classical
  calc
    ∑ p : Fin t × Fin t, (u p.1 * u p.2) * (v p.1 * v p.2)
        = ∑ i, ∑ j, (u i * u j) * (v i * v j) := by
            simpa only [Finset.univ_product_univ] using
              (Finset.sum_product (s := Finset.univ) (t := Finset.univ) (f :=
                fun p : Fin t × Fin t => (u p.1 * u p.2) * (v p.1 * v p.2)))
    _ = ∑ i, (u i * v i) * (∑ j, u j * v j) := by
            refine Finset.sum_congr rfl ?_ ; intro i _;
              simp only [mul_left_comm, mul_comm, Finset.mul_sum]
    _ = (∑ j, u j * v j) * ∑ i, (u i * v i) := by
            simp only [mul_assoc, Finset.sum_mul]
    _ = (∑ s : Fin t, u s * v s) ^ 2 := by ring

/-- Row norms as sums of squares. -/
lemma negRowNorm_sq {μ : ℝ} {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i : n) :
    (negRowNorm (A := A) (hHerm := hHerm) ht hBottom i)^2 =
      ∑ s, (negRowVec (A := A) (hHerm := hHerm) ht hBottom i s)^2 := by
  have hnonneg :
      0 ≤ ∑ s, (negRowVec (A := A) (hHerm := hHerm) ht hBottom i s)^2 :=
    by positivity
  have h := Real.sq_sqrt hnonneg
  simpa only [negRowNorm, pow_two] using h

/-- Trace of `Us * Usᵀ` is 1. -/
lemma negUs_trace_one {μ : ℝ} {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    Matrix.trace
      (negEigenMatrixScaled (A := A) (hHerm := hHerm) ht hBottom *
        (negEigenMatrixScaled (A := A) (hHerm := hHerm) ht hBottom)ᵀ) = 1 := by
  classical
  let Us := negEigenMatrixScaled (A := A) (hHerm := hHerm) ht hBottom
  have horth :=
    negEigenMatrixScaled_orthonormal (A := A) (hHerm := hHerm) ht hBottom
  have hswap := Matrix.trace_mul_comm (A := Us) (B := Usᵀ)
  calc
    Matrix.trace (Us * Usᵀ) = Matrix.trace (Usᵀ * Us) := hswap
    _ = Matrix.trace ((1 / (t : ℝ)) • (1 : Matrix (Fin t) (Fin t) ℝ)) := by
          simpa only [one_div, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul] using
            congrArg Matrix.trace horth
    _ = (1 / (t : ℝ)) * (t : ℝ) := by
          simp only [one_div, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]
    _ = 1 := by
          have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt ht
          field_simp [ht0]

/-- Sum of squared row norms equals 1. -/
lemma sum_negRowNorm_sq {μ : ℝ} {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    ∑ i, (negRowNorm (A := A) (hHerm := hHerm) ht hBottom i)^2 = 1 := by
  classical
  let Us := negEigenMatrixScaled (A := A) (hHerm := hHerm) ht hBottom
  have htrace := negUs_trace_one (A := A) (hHerm := hHerm) ht hBottom
  have hrows :
      Matrix.trace (Us * Usᵀ) = ∑ i, ∑ s, (Us i s)^2 := by
    simp only [trace, diag_apply, mul_apply, transpose_apply, pow_two]
  calc
    ∑ i, (negRowNorm (A := A) (hHerm := hHerm) ht hBottom i)^2
        = ∑ i, ∑ s, (Us i s)^2 := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simp only [negRowNorm_sq (A := A) (hHerm := hHerm) ht hBottom,
              negRowVec, Us]
    _ = Matrix.trace (Us * Usᵀ) := hrows.symm
    _ = 1 := htrace

/-- Norm of each tensorized column. -/
lemma negTensorVec_norm_sq {μ : ℝ} {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i : n) :
    ∑ p : Fin t × Fin t,
        (negTensorVec (A := A) (hHerm := hHerm) ht hBottom i p)^2 =
      (negRowNorm (A := A) (hHerm := hHerm) ht hBottom i)^2 := by
  classical
  let w : Fin t → ℝ := negRowVec (A := A) (hHerm := hHerm) ht hBottom i
  let r : ℝ := negRowNorm (A := A) (hHerm := hHerm) ht hBottom i
  have hsq : r ^ 2 = ∑ s, (w s)^2 := by
    have hnonneg : 0 ≤ ∑ s, (w s)^2 := by positivity
    dsimp only [negRowNorm, w, r] at *
    simpa only [pow_two] using (Real.sq_sqrt hnonneg)
  by_cases hr : r = 0
  · have hsum_zero : ∑ s, (w s)^2 = 0 := by simpa only [hr, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow] using hsq.symm
    calc
      ∑ p : Fin t × Fin t,
          (negTensorVec (A := A) (hHerm := hHerm) ht hBottom i p)^2 = 0 := by
            simp only [negTensorVec, hr, ↓reduceDIte, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
              zero_pow, Finset.sum_const_zero, r]
      _ = ∑ s, (w s)^2 := by simp only [hsum_zero]
      _ = r^2 := by simp only [hsq]
  · have hr2_ne : r ^ 2 ≠ 0 := pow_ne_zero _ hr
    calc
      ∑ p : Fin t × Fin t,
          (negTensorVec (A := A) (hHerm := hHerm) ht hBottom i p)^2
          = ∑ p : Fin t × Fin t, ((w p.1 * w p.2) / r) ^ 2 := by
              simp only [negTensorVec, hr, ↓reduceDIte, w, r]
      _ = ∑ p : Fin t × Fin t, (w p.1 * w p.2) ^ 2 * (r ^ 2)⁻¹ := by
              refine Finset.sum_congr rfl ?_
              intro p _
              field_simp [pow_two]
      _ = (∑ p : Fin t × Fin t, (w p.1 * w p.2) ^ 2) * (r ^ 2)⁻¹ := by
              simpa only using
                (Finset.sum_mul (s := (Finset.univ : Finset (Fin t × Fin t))) (f :=
                    fun p : Fin t × Fin t => (w p.1 * w p.2) ^ 2) (a := (r ^ 2)⁻¹)).symm
      _ = ((∑ s, (w s) ^ 2) ^ 2) * (r ^ 2)⁻¹ := by simp only [tensorSquare_sum_sq (t := t) w]
      _ = r ^ 2 := by
              calc
                ((∑ s, (w s)^2) ^ 2) * (r ^ 2)⁻¹
                    = (r ^ 2 * r ^ 2) * (r ^ 2)⁻¹ := by simp only [pow_two, hsq, mul_assoc]
                _ = r ^ 2 := by field_simp [hr2_ne]

/-- Trace of the Gram witness is 1. -/
lemma negWitnessM_trace_one {μ : ℝ} {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    Matrix.trace (negWitnessM (A := A) (hHerm := hHerm) ht hBottom) = 1 := by
  classical
  let V := negVmatrix (A := A) (hHerm := hHerm) ht hBottom
  have htrace :
      Matrix.trace (Vᵀ * V) =
        ∑ i, ∑ p : Fin t × Fin t, (V p i)^2 := by
    simp only [trace, diag_apply, mul_apply, transpose_apply, pow_two]
  have hcols :
      ∀ i, ∑ p : Fin t × Fin t, (V p i)^2 =
        (negRowNorm (A := A) (hHerm := hHerm) ht hBottom i)^2 := by
    intro i
    simpa only [V, negVmatrix] using
      (negTensorVec_norm_sq (A := A) (hHerm := hHerm) (ht := ht) hBottom i)
  calc
    Matrix.trace (negWitnessM (A := A) (hHerm := hHerm) ht hBottom)
        = ∑ i, ∑ p, (V p i)^2 := by simpa only [negWitnessM, V] using htrace
    _ = ∑ i, (negRowNorm (A := A) (hHerm := hHerm) ht hBottom i)^2 := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simpa only using hcols i
    _ = 1 := sum_negRowNorm_sq (A := A) (hHerm := hHerm) ht hBottom

/-- Frobenius norm bound: `‖M‖_F^2 ≤ 1/t`. -/
lemma negWitnessM_frobeniusSq {μ : ℝ} {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    frobeniusSq (negWitnessM (A := A) (hHerm := hHerm)
      ht hBottom) ≤ 1 / (t : ℝ) := by
  classical
  let Us := negEigenMatrixScaled (A := A) (hHerm := hHerm) ht hBottom
  let P : Matrix n n ℝ := Us * Usᵀ
  have hP_diag :
      ∀ i, P i i =
        (negRowNorm (A := A) (hHerm := hHerm) ht hBottom i)^2 := by
    intro i
    have hsum :
        P i i = ∑ s, (Us i s)^2 := by
      simp only [mul_apply, transpose_apply, pow_two, P]
    have hnorm :=
      negRowNorm_sq (A := A) (hHerm := hHerm) ht hBottom i
    have hnorm' : (negRowNorm (A := A) (hHerm := hHerm) ht hBottom i)^2 =
        ∑ s, (Us i s)^2 := by
      simpa only [pow_two, negRowVec] using hnorm
    linarith
  have hP_cs : ∀ i j, (P i j)^2 ≤ P i i * P j j := by
    intro i j
    have hcs :
        (∑ s, Us i s * Us j s) ^ 2 ≤
          (∑ s, (Us i s)^2) * ∑ s, (Us j s)^2 :=
      Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset (Fin t)))
        (f := fun s => Us i s) (g := fun s => Us j s)
    have hPij :
        P i j = ∑ s, Us i s * Us j s := by
      simp only [mul_apply, transpose_apply, P]
    have hPii :
        P i i = ∑ s, (Us i s)^2 := by
      simp only [mul_apply, transpose_apply, pow_two, P]
    have hPjj :
        P j j = ∑ s, (Us j s)^2 := by
      simp only [mul_apply, transpose_apply, pow_two, P]
    have hcs' : (P i j)^2 ≤ P i i * P j j := by
      calc
        (P i j)^2 = (∑ s, Us i s * Us j s) ^ 2 := by simp only [hPij]
        _ ≤ (∑ s, (Us i s)^2) * ∑ s, (Us j s)^2 := hcs
        _ = P i i * P j j := by simp only [hPii, hPjj]
    exact hcs'
  have hentry :
      ∀ i j,
        ((negWitnessM (A := A) (hHerm := hHerm) ht hBottom) i j)^2 ≤
          (P i j)^2 := by
    intro i j
    classical
    set wi : Fin t → ℝ := negRowVec (A := A) (hHerm := hHerm) ht hBottom i
    set wj : Fin t → ℝ := negRowVec (A := A) (hHerm := hHerm) ht hBottom j
    set ri : ℝ := negRowNorm (A := A) (hHerm := hHerm) ht hBottom i
    set rj : ℝ := negRowNorm (A := A) (hHerm := hHerm) ht hBottom j
    have hPij : P i j = ∑ s, wi s * wj s := by
      simp only [mul_apply, transpose_apply, negRowVec, P, Us, wi, wj]
    have hPii : P i i = ri ^ 2 := by
      simpa only using hP_diag i
    have hPjj : P j j = rj ^ 2 := by
      simpa only using hP_diag j
    by_cases hri : ri = 0
    · have hcol_zero : ∀ p, negTensorVec (A := A) (hHerm := hHerm) (μ := μ)
        (t := t) ht hBottom i p = 0 := by
        intro p; simp only [negTensorVec, hri, ↓reduceDIte, ri]
      have hcol_zeroV : ∀ p, negVmatrix (A := A) (hHerm := hHerm) (μ := μ)
        (t := t) ht hBottom p i = 0 := by
        intro p; simp only [negVmatrix, hcol_zero]
      have hMij :
          (negWitnessM (A := A) (hHerm := hHerm) ht hBottom) i j =
            ∑ p, negVmatrix (A := A) (hHerm := hHerm)
              ht hBottom p i *
              negVmatrix (A := A) (hHerm := hHerm) ht hBottom p j := by
        simp only [negWitnessM, mul_apply, transpose_apply]
      have hMij_zero : (negWitnessM (A := A) (hHerm := hHerm) (μ := μ)
        (t := t) ht hBottom) i j = 0 := by
        simp only [hMij, hcol_zeroV, zero_mul, Finset.sum_const_zero]
      have hnonneg : 0 ≤ (P i j)^2 := by positivity
      simpa only [hMij_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        ge_iff_le] using hnonneg
    · by_cases hrj : rj = 0
      · have hcol_zero : ∀ p, negTensorVec (A := A) (hHerm := hHerm) (μ := μ)
          (t := t) ht hBottom j p = 0 := by
          intro p; simp only [negTensorVec, hrj, ↓reduceDIte, rj]
        have hcol_zeroV : ∀ p, negVmatrix (A := A) (hHerm := hHerm) (μ := μ)
          (t := t) ht hBottom p j = 0 := by
          intro p; simp only [negVmatrix, hcol_zero]
        have hMij :
            (negWitnessM (A := A) (hHerm := hHerm) ht hBottom) i j =
              ∑ p, negVmatrix (A := A) (hHerm := hHerm) ht hBottom p i *
                negVmatrix (A := A) (hHerm := hHerm) ht hBottom p j := by
          simp only [negWitnessM, mul_apply, transpose_apply]
        have hMij_zero :
            (negWitnessM (A := A) (hHerm := hHerm) ht hBottom) i j = 0 := by
          simp only [hMij, hcol_zeroV, mul_zero, Finset.sum_const_zero]
        have hnonneg : 0 ≤ (P i j)^2 := by positivity
        simpa only [hMij_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          ge_iff_le] using hnonneg
      · -- nonzero norms
        have hPij_sq_le : (P i j)^2 ≤ (ri * rj) ^ 2 := by
          have h := hP_cs i j
          calc
            (P i j)^2 ≤ P i i * P j j := h
            _ = ri ^ 2 * rj ^ 2 := by simp only [hPii, hPjj]
            _ = (ri * rj) ^ 2 := by ring
        have hMij :
            (negWitnessM (A := A) (hHerm := hHerm) ht hBottom) i j =
              (P i j)^2 / (ri * rj) := by
          have hts := tensorSquare_sum_mul (u := wi) (v := wj)
          calc
            (negWitnessM (A := A) (hHerm := hHerm) ht hBottom) i j
                = ∑ p, negVmatrix (A := A) (hHerm := hHerm) ht hBottom p i *
                    negVmatrix (A := A) (hHerm := hHerm) ht hBottom p j := by
                    simp only [negWitnessM, mul_apply, transpose_apply]
            _ = ∑ p, negTensorVec (A := A) (hHerm := hHerm) ht hBottom i p *
                    negTensorVec (A := A) (hHerm := hHerm) ht hBottom j p := by
                    simp only [negVmatrix]
            _ = (ri * rj)⁻¹ *
                  ∑ p : Fin t × Fin t, (wi p.1 * wi p.2) * (wj p.1 * wj p.2) := by
                    simp only [negTensorVec, hri, ↓reduceDIte, div_eq_mul_inv, mul_comm, hrj,
                      mul_left_comm, mul_assoc, _root_.mul_inv_rev, Finset.mul_sum, ri, rj, wi, wj]
            _ = (ri * rj)⁻¹ * (∑ s, wi s * wj s) ^ 2 := by simp only [_root_.mul_inv_rev,
              tensorSquare_sum_mul (u := wi)]
            _ = (∑ s, wi s * wj s) ^ 2 / (ri * rj) := by ring
            _ = (P i j)^2 / (ri * rj) := by simp only [hPij]
        have hri_pos : 0 < ri := by
          have hnonneg : 0 ≤ ri := by
            have hsqrt := Real.sqrt_nonneg (∑ s, (negRowVec (A := A) (hHerm := hHerm)
               ht hBottom i s) ^ 2)
            simpa only [ri, negRowNorm] using hsqrt
          have hne : 0 ≠ ri := by exact fun h => hri h.symm
          exact lt_of_le_of_ne hnonneg hne
        have hrj_pos : 0 < rj := by
          have hnonneg : 0 ≤ rj := by
            have hsqrt := Real.sqrt_nonneg (∑ s, (negRowVec (A := A) (hHerm := hHerm)
               ht hBottom j s) ^ 2)
            simpa only [rj, negRowNorm] using hsqrt
          have hne : 0 ≠ rj := by exact fun h => hrj h.symm
          exact lt_of_le_of_ne hnonneg hne
        have hden_pos : 0 < ri * rj := mul_pos hri_pos hrj_pos
        have hM_sq :
            ((negWitnessM (A := A) (hHerm := hHerm) ht hBottom) i j)^2 =
              ((P i j)^2 / (ri * rj))^2 := by simp only [hMij]
        have hratio :
            (P i j)^2 / (ri * rj) ^ 2 ≤ 1 := by
          have hnonneg : 0 ≤ (ri * rj) ^ 2 := sq_nonneg (ri * rj)
          have hdiv :=
            div_le_div_of_nonneg_right hPij_sq_le hnonneg
          have hsq_ne : (ri * rj) ^ 2 ≠ 0 :=
            pow_ne_zero 2 (mul_ne_zero (ne_of_gt hri_pos) (ne_of_gt hrj_pos))
          have hself : (ri * rj) ^ 2 / (ri * rj) ^ 2 = (1 : ℝ) := by
            field_simp [hsq_ne]
          simpa only [ge_iff_le, hself] using hdiv
        have hbound :
            ((P i j)^2 / (ri * rj))^2 ≤ (P i j)^2 := by
          have hmul := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ (P i j)^2)
          have hrewrite :
              (P i j)^2 * ((P i j)^2 / (ri * rj) ^ 2) =
                ((P i j)^2 / (ri * rj))^2 := by ring
          have hrewrite' : (P i j)^2 * (1 : ℝ) = (P i j)^2 := by ring
          simpa only [ge_iff_le, hrewrite, hrewrite'] using hmul
        simpa only [hM_sq, ge_iff_le] using hbound
  have hP_sq : frobeniusSq P = 1 / (t : ℝ) := by
    have hproj :
        P * P = (1 / (t : ℝ)) • P := by
      have horth :=
        negEigenMatrixScaled_orthonormal (A := A) (hHerm := hHerm) ht hBottom
      calc
        P * P = Us * Usᵀ * (Us * Usᵀ) := by simp only [P]
        _ = Us * (Usᵀ * Us) * Usᵀ := by simp only [Matrix.mul_assoc]
        _ = Us * ((1 / (t : ℝ)) • (1 : Matrix (Fin t) (Fin t) ℝ)) * Usᵀ := by
              simpa only [one_div, Matrix.mul_smul, Matrix.mul_one, smul_mul, Us] using
                congrArg (fun M => Us * M * Usᵀ) horth
        _ = (1 / (t : ℝ)) • P := by
              simp only [one_div, Matrix.mul_smul, Matrix.mul_one, smul_mul, Us, P]
    have htraceP : Matrix.trace P = 1 := by
      simpa only using negUs_trace_one (A := A) (hHerm := hHerm) ht hBottom
    calc
      frobeniusSq P = Matrix.trace (Pᵀ * P) := frobeniusSq_trace _
      _ = Matrix.trace (P * P) := by simp only [transpose_mul, transpose_transpose, P]
      _ = Matrix.trace ((1 / (t : ℝ)) • P) := by simp only [hproj, one_div, trace_smul,
        smul_eq_mul]
      _ = (1 / (t : ℝ)) * Matrix.trace P := by simp only [one_div, trace_smul, smul_eq_mul]
      _ = 1 / (t : ℝ) := by simp only [one_div, htraceP, mul_one]
  have hsum :
      ∑ i, ∑ j,
          ((negWitnessM (A := A) (hHerm := hHerm) ht hBottom) i j)^2 ≤
        ∑ i, ∑ j, (P i j)^2 := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine Finset.sum_le_sum (fun j _ => hentry i j)
  have hM_le_P :
      frobeniusSq (negWitnessM (A := A) (hHerm := hHerm) ht hBottom) ≤
        frobeniusSq P := by
    simpa only [frobeniusSq] using hsum
  linarith [hM_le_P, hP_sq]

/-- Condition 1: the Gram witness has `frobeniusInner A M ≥ μ^2`. -/
lemma negWitnessM_inner_bound
    (hNonneg : ∀ i j, 0 ≤ A i j) (hOp : ‖A‖ ≤ (1 : ℝ))
    {μ : ℝ} (hμ : 0 ≤ μ) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    frobeniusInner A
      (negWitnessM (A := A) (hHerm := hHerm) ht hBottom) ≥ μ^2 := by
  classical
  let M := negWitnessM (A := A) (hHerm := hHerm) ht hBottom
  let Us := UsMatrix (A := A) (hHerm := hHerm) ht hBottom
  let P : Matrix n n ℝ := Us * Usᵀ
  let r : n → ℝ :=
    fun i => negRowNorm (A := A) (hHerm := hHerm) ht hBottom i
  let vals := negEigValues (A := A) (hHerm := hHerm) hBottom

  have hA_Us :
      A * Us = Us * Matrix.diagonal vals := by
    ext i s
    classical
    let U : Matrix n n ℝ := hHerm.eigenvectorUnitary
    have hcol :
        ∑ j, A i j * U j (negEigIdx (A := A) (hHerm := hHerm) hBottom s) =
          vals s *
            U i (negEigIdx (A := A) (hHerm := hHerm) hBottom s) := by
      have h := hHerm.mulVec_eigenvectorBasis
        (j := negEigIdx (A := A) (hHerm := hHerm) hBottom s)
      simpa only [U, vals, negEigValues, IsHermitian.eigenvectorUnitary_apply, mulVec, dotProduct,
        Pi.smul_apply, smul_eq_mul] using congrArg (fun v => v i) h
    calc
      (A * Us) i s = ∑ j, A i j * Us j s := by simp only [UsMatrix_eq_negEigenMatrixScaled,
        mul_apply, Us]
      _ = (Real.sqrt (t : ℝ))⁻¹ *
            ∑ j, A i j *
              U j
                (negEigIdx (A := A) (hHerm := hHerm) hBottom s) := by
            simp only [UsMatrix_eq_negEigenMatrixScaled, negEigenMatrixScaled, one_div,
              IsHermitian.eigenvectorUnitary_apply, Finset.mul_sum, mul_left_comm, Us, U]
      _ = (Real.sqrt (t : ℝ))⁻¹ *
            (vals s *
              U i
                (negEigIdx (A := A) (hHerm := hHerm) hBottom s)) := by
            simp only [hcol]
      _ = vals s * ((Real.sqrt (t : ℝ))⁻¹ *
            U i (negEigIdx (A := A) (hHerm := hHerm) hBottom s)) := by ring
      _ = (vals s) * Us i s := by
            have hUs :
                Us i s =
                  (Real.sqrt (t : ℝ))⁻¹ *
                    U i (negEigIdx (A := A) (hHerm := hHerm) hBottom s) := by
              simp only [UsMatrix_eq_negEigenMatrixScaled, negEigenMatrixScaled, one_div,
                IsHermitian.eigenvectorUnitary_apply, Us, U]
            simp only [mul_left_comm, hUs]
      _ = (Us * Matrix.diagonal vals) i s := by
            simp only [UsMatrix_eq_negEigenMatrixScaled, mul_diagonal, mul_comm, vals, Us]

  have hA_symm : Matrix.transpose A = A := by
    have h := hHerm.eq
    simpa only [conjTranspose_eq_transpose_of_trivial] using h
  have hinner_P :
      frobeniusInner A P =
        (1 / (t : ℝ)) * ∑ s, vals s := by
    have htrace_cycle := Matrix.trace_mul_cycle (A := A) (B := Us) (C := Usᵀ)
    have horth :=
      negEigenMatrixScaled_orthonormal (A := A) (hHerm := hHerm) ht hBottom
    calc
      frobeniusInner A P
          = Matrix.trace (Matrix.transpose A * P) := frobeniusInner_trace _ _
      _ = Matrix.trace (A * P) := by simp only [hA_symm]
      _ = Matrix.trace (Usᵀ * A * Us) := by
            simpa only [Matrix.mul_assoc, P] using htrace_cycle
      _ = Matrix.trace (Usᵀ * (Us * Matrix.diagonal vals)) := by
            simp only [Matrix.mul_assoc, hA_Us]
      _ = Matrix.trace ((Usᵀ * Us) * Matrix.diagonal vals) := by
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace (((1 / (t : ℝ)) • (1 : Matrix (Fin t) (Fin t) ℝ)) *
            Matrix.diagonal vals) := by
            simpa only [Us, UsMatrix_eq_negEigenMatrixScaled, one_div, Algebra.smul_mul_assoc,
              one_mul, trace_smul, trace_diagonal, smul_eq_mul] using
              congrArg (fun M => Matrix.trace (M * Matrix.diagonal vals)) horth
      _ = Matrix.trace ((1 / (t : ℝ)) • Matrix.diagonal vals) := by
            simp only [one_div, Algebra.smul_mul_assoc, one_mul, trace_smul, trace_diagonal,
              smul_eq_mul]
      _ = (1 / (t : ℝ)) * Matrix.trace (Matrix.diagonal vals) := by
            simp only [one_div, trace_smul, trace_diagonal, smul_eq_mul]
      _ = (1 / (t : ℝ)) * ∑ s, vals s := by
            simp only [one_div, trace, diag_apply, diagonal_apply_eq]

  have hvals_le : ∀ s, vals s ≤ -μ := by
    intro s
    classical
    set hcard :
        t ≤ Fintype.card (negEigSubtype (A := A) (hHerm := hHerm) (μ := μ)) := by
      simpa only [negEigSubtype, bottomThresholdRank, ge_iff_le] using hBottom
    have hsub :
        hHerm.eigenvalues
            ((Fintype.equivFin (negEigSubtype (A := A) (hHerm := hHerm) (μ := μ))).symm
              (Fin.castLE hcard s)).1 ≤ -μ :=
      ((Fintype.equivFin (negEigSubtype (A := A) (hHerm := hHerm) (μ := μ))).symm
        (Fin.castLE hcard s)).2
    simpa only [vals, negEigValues, negEigIdx, negEigSubtype, ge_iff_le] using hsub

  have hinnerP_le : frobeniusInner A P ≤ -μ := by
    have hsum_le :
        ∑ s, vals s ≤ ∑ _ : Fin t, (-μ) := by
      refine Finset.sum_le_sum ?_ ; intro s _; simpa only using hvals_le s
    have hsum_const :
        ∑ _ : Fin t, (-μ : ℝ) = (t : ℝ) * (-μ) := by simp only [Finset.sum_neg_distrib,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_neg]
    have hsum_le' : ∑ s, vals s ≤ (t : ℝ) * (-μ) := by
      have := hsum_le
      simpa only [mul_neg, ge_iff_le, hsum_const] using this
    have hpos : 0 ≤ (1 / (t : ℝ)) := by
      have htpos : 0 < (t : ℝ) := by exact_mod_cast ht
      have hpos' : 0 < (1 / (t : ℝ)) := by
        have := one_div_pos.mpr htpos
        simpa only [one_div, inv_pos, Nat.cast_pos, gt_iff_lt] using this
      exact le_of_lt hpos'
    have hmul : (1 / (t : ℝ)) * ((t : ℝ) * (-μ)) = -μ := by
      have htne : (t : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt ht
      field_simp [htne]
    calc
      frobeniusInner A P = (1 / (t : ℝ)) * ∑ s, vals s := hinner_P
      _ ≤ (1 / (t : ℝ)) * ((t : ℝ) * (-μ)) := by
            have := mul_le_mul_of_nonneg_left hsum_le' hpos
            simpa only [one_div, mul_neg, ge_iff_le] using this
      _ = -μ := hmul

  have hinnerP_sq : μ^2 ≤ (frobeniusInner A P)^2 := by
    have hμ_nonneg : 0 ≤ μ := hμ
    have hneg : frobeniusInner A P ≤ 0 := by
      have hle : -μ ≤ (0 : ℝ) := by linarith
      exact le_trans hinnerP_le hle
    have hμ_le_abs : μ ≤ |frobeniusInner A P| := by
      have hle : -frobeniusInner A P ≥ μ := by linarith [hinnerP_le]
      have habs_frob : |frobeniusInner A P| = -frobeniusInner A P := abs_of_nonpos hneg
      simpa only [habs_frob, ge_iff_le] using hle
    have hmul :
        μ * μ ≤ |frobeniusInner A P| * |frobeniusInner A P| :=
      mul_le_mul hμ_le_abs hμ_le_abs hμ_nonneg (abs_nonneg _)
    have habs_sq :
        |frobeniusInner A P| * |frobeniusInner A P| = (frobeniusInner A P)^2 := by
      have h := sq_abs (frobeniusInner A P)
      calc
        |frobeniusInner A P| * |frobeniusInner A P|
            = (|frobeniusInner A P|)^2 := by ring
        _ = (frobeniusInner A P)^2 := by simp only [h, pow_two]
    have hmu_sq : μ * μ = μ^2 := by ring
    simpa only [ge_iff_le, hmu_sq, habs_sq] using hmul

  have hP_zero_of_r_zero :
      ∀ i j, r i = 0 ∨ r j = 0 → P i j = 0 := by
    intro i j hzero
    rcases hzero with hri | hrj
    · have hnorm :=
        negRowNorm_sq (A := A) (hHerm := hHerm) ht hBottom i
      have hri_sq : (r i)^2 = 0 := by simp only [hri, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, r]
      have hsum_zero :
          ∑ s,
              (negRowVec (A := A) (hHerm := hHerm) ht hBottom i s)^2 = 0 :=
        by
          have hnorm' :
              (r i)^2 =
                ∑ s,
                  (negRowVec (A := A) (hHerm := hHerm) ht hBottom i s)^2 :=
            by simpa only using hnorm
          simpa only [hri, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using
            hnorm'.symm
      have hrow_zero :
          ∀ s,
            negRowVec (A := A) (hHerm := hHerm) ht hBottom i s = 0 := by
        have hzero :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).1 hsum_zero
        intro s
        have hs := hzero s (by simp only [Finset.mem_univ])
        exact sq_eq_zero_iff.mp hs
      have hPij :
          P i j =
            ∑ s,
              negRowVec (A := A) (hHerm := hHerm) ht hBottom i s *
                negRowVec (A := A) (hHerm := hHerm) ht hBottom j s := by
        simp only [UsMatrix_eq_negEigenMatrixScaled, mul_apply, transpose_apply, negRowVec, P, Us]
      calc
        P i j =
            ∑ s,
              negRowVec (A := A) (hHerm := hHerm) ht hBottom i s *
                negRowVec (A := A) (hHerm := hHerm) ht hBottom j s := hPij
        _ = 0 := by
          have hsum :
              ∑ s : Fin t,
                  negRowVec (A := A) (hHerm := hHerm) ht hBottom i s *
                    negRowVec (A := A) (hHerm := hHerm) ht hBottom j s =
                ∑ s : Fin t, (0 : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro s hs; simp only [hrow_zero s, zero_mul]
          simp only [hsum, Finset.sum_const_zero]
    · have hnorm :=
        negRowNorm_sq (A := A) (hHerm := hHerm) ht hBottom j
      have hrj_sq : (r j)^2 = 0 := by simp only [hrj, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, r]
      have hsum_zero :
          ∑ s,
              (negRowVec (A := A) (hHerm := hHerm) ht hBottom j s)^2 = 0 :=
        by
          have hnorm' :
              (r j)^2 =
                ∑ s,
                  (negRowVec (A := A) (hHerm := hHerm) ht hBottom j s)^2 :=
            by simpa only using hnorm
          simpa only [hrj, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using
            hnorm'.symm
      have hrow_zero :
          ∀ s,
            negRowVec (A := A) (hHerm := hHerm) ht hBottom j s = 0 := by
        have hzero :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).1 hsum_zero
        intro s
        have hs := hzero s (by simp only [Finset.mem_univ])
        exact sq_eq_zero_iff.mp hs
      have hPij :
          P i j =
            ∑ s,
              negRowVec (A := A) (hHerm := hHerm) ht hBottom i s *
                negRowVec (A := A) (hHerm := hHerm) ht hBottom j s := by
        simp only [UsMatrix_eq_negEigenMatrixScaled, mul_apply, transpose_apply, negRowVec, P, Us]
      calc
        P i j =
            ∑ s,
              negRowVec (A := A) (hHerm := hHerm) ht hBottom i s *
                negRowVec (A := A) (hHerm := hHerm) ht hBottom j s := hPij
        _ = 0 := by
          have hsum :
              ∑ s : Fin t,
                  negRowVec (A := A) (hHerm := hHerm) ht hBottom i s *
                    negRowVec (A := A) (hHerm := hHerm) ht hBottom j s =
                ∑ s : Fin t, (0 : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro s hs; simp only [hrow_zero s, mul_zero]
          simp only [hsum, Finset.sum_const_zero]

  have hM_entry :
      ∀ i j,
        M i j = (P i j)^2 / (r i * r j) := by
    intro i j
    classical
    set wi : Fin t → ℝ := negRowVec (A := A) (hHerm := hHerm) ht hBottom i
    set wj : Fin t → ℝ := negRowVec (A := A) (hHerm := hHerm) ht hBottom j
    have hPij : P i j = ∑ s, wi s * wj s := by
      simp only [UsMatrix_eq_negEigenMatrixScaled, mul_apply, transpose_apply, negRowVec, P, Us,
        wi, wj]
    by_cases hri : r i = 0
    · -- Column `i` vanishes.
      have hcol_zero : ∀ p, negTensorVec (A := A) (hHerm := hHerm) (μ := μ)
          (t := t) ht hBottom i p = 0 := by
        intro p; simp only [negTensorVec, hri, ↓reduceDIte, r]
      have hcol_zeroV : ∀ p, negVmatrix (A := A) (hHerm := hHerm) (μ := μ)
          (t := t) ht hBottom p i = 0 := by
        intro p; simp only [negVmatrix, hcol_zero]
      have hMij :
          M i j =
            ∑ p, negVmatrix (A := A) (hHerm := hHerm) ht hBottom p i *
              negVmatrix (A := A) (hHerm := hHerm) ht hBottom p j := by
        simp only [negWitnessM, mul_apply, transpose_apply, M]
      have hsum_zero : ∑ s, (wi s)^2 = 0 := by
        have hnorm :=
          negRowNorm_sq (A := A) (hHerm := hHerm) ht hBottom i
        have hri_sq : (r i)^2 = 0 := by simp only [hri, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, zero_pow, r]
        have hnorm' : (r i)^2 = ∑ s, (wi s)^2 := by simpa only using hnorm
        simpa only [hri, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using hnorm'.symm
      have hrow_zero : ∀ s, wi s = 0 := by
        have hzero :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).1 hsum_zero
        intro s
        have hs := hzero s (by simp only [Finset.mem_univ])
        exact sq_eq_zero_iff.mp hs
      have hP_zero : P i j = 0 := by
        have hsum_zero' : ∑ s, wi s * wj s = 0 := by
          calc
            ∑ s, wi s * wj s = ∑ s, 0 := by
              refine Finset.sum_congr rfl ?_; intro s hs; simp only [hrow_zero s, zero_mul]
            _ = 0 := by simp only [Finset.sum_const_zero]
        calc
          P i j = ∑ s, wi s * wj s := hPij
          _ = 0 := hsum_zero'
      simp only [hMij, hcol_zeroV, zero_mul, Finset.sum_const_zero, hP_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, hri, div_zero, r]
    · by_cases hrj : r j = 0
      · -- Column `j` vanishes.
        have hcol_zero : ∀ p, negTensorVec (A := A) (hHerm := hHerm) (μ := μ)
            (t := t) ht hBottom j p = 0 := by
          intro p; simp only [negTensorVec, hrj, ↓reduceDIte, r]
        have hcol_zeroV : ∀ p, negVmatrix (A := A) (hHerm := hHerm) (μ := μ)
            (t := t) ht hBottom p j = 0 := by
          intro p; simp only [negVmatrix, hcol_zero]
        have hMij :
            M i j =
              ∑ p, negVmatrix (A := A) (hHerm := hHerm) ht hBottom p i *
                negVmatrix (A := A) (hHerm := hHerm) ht hBottom p j := by
          simp only [negWitnessM, mul_apply, transpose_apply, M]
        have hP_zero : P i j = 0 := by
          have hsum_zero : ∑ s, (wj s)^2 = 0 := by
            have hnorm :=
              negRowNorm_sq (A := A) (hHerm := hHerm) ht hBottom j
            have hrj_sq : (r j)^2 = 0 := by simp only [hrj, ne_eq, OfNat.ofNat_ne_zero,
              not_false_eq_true, zero_pow, r]
            have hnorm' : (r j)^2 = ∑ s, (wj s)^2 := by simpa only using hnorm
            simpa only [hrj, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using
              hnorm'.symm
          have hrow_zero : ∀ s, wj s = 0 := by
            have hzero :=
              (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).1 hsum_zero
            intro s
            have hs := hzero s (by simp only [Finset.mem_univ])
            exact sq_eq_zero_iff.mp hs
          have hsum_zero' : ∑ s, wi s * wj s = 0 := by
            calc
              ∑ s, wi s * wj s = ∑ s, wi s * 0 := by
                refine Finset.sum_congr rfl ?_; intro s hs; simp only [hrow_zero s, mul_zero]
              _ = 0 := by simp only [mul_zero, Finset.sum_const_zero]
          calc
            P i j = ∑ s, wi s * wj s := hPij
            _ = 0 := hsum_zero'
        simp only [hMij, hcol_zeroV, mul_zero, Finset.sum_const_zero, hP_zero, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, hrj, div_zero, r]
      · -- Both norms are nonzero: exact formula via tensor identity.
        have hMij :
            M i j =
              (r i * r j)⁻¹ *
                ∑ p : Fin t × Fin t,
                  (wi p.1 * wi p.2) * (wj p.1 * wj p.2) := by
          calc
            M i j
                = ∑ p, negVmatrix (A := A) (hHerm := hHerm) ht hBottom p i *
                    negVmatrix (A := A) (hHerm := hHerm) ht hBottom p j := by
                    simp only [negWitnessM, mul_apply, transpose_apply, M]
            _ = ∑ p, negTensorVec (A := A) (hHerm := hHerm) ht hBottom i p *
                    negTensorVec (A := A) (hHerm := hHerm) ht hBottom j p := by
                    simp only [negVmatrix]
            _ = (r i * r j)⁻¹ *
                  ∑ p : Fin t × Fin t, (wi p.1 * wi p.2) * (wj p.1 * wj p.2) := by
                    simp only [negTensorVec, hri, ↓reduceDIte, div_eq_mul_inv, mul_comm, hrj,
                      mul_left_comm, mul_assoc, _root_.mul_inv_rev, Finset.mul_sum, r, wi, wj]
        have hsum :
            ∑ p : Fin t × Fin t, (wi p.1 * wi p.2) * (wj p.1 * wj p.2) = (P i j)^2 := by
          simpa only [hPij] using tensorSquare_sum_mul (u := wi) (v := wj)
        have hri_ne : r i ≠ 0 := hri
        have hrj_ne : r j ≠ 0 := hrj
        have hMij' :
            M i j = (P i j)^2 / (r i * r j) := by
          calc
            M i j = (r i * r j)⁻¹ * (P i j)^2 := by
              simpa only [_root_.mul_inv_rev, hsum] using hMij
            _ = (P i j)^2 / (r i * r j) := by ring
        simp only [hMij']

  have hinner_M :
      frobeniusInner A M = ∑ i, ∑ j, A i j * (P i j)^2 / (r i * r j) := by
    classical
    simp only [frobeniusInner, hM_entry, mul_div_assoc, M, r]
  have hinner_P_def : frobeniusInner A P = ∑ i, ∑ j, A i j * P i j := rfl

  have hr_nonneg : ∀ i j, 0 ≤ r i * r j := by
    intro i j
    have hri : 0 ≤ r i := by
      dsimp only [negRowNorm, r]
      exact Real.sqrt_nonneg _
    have hrj : 0 ≤ r j := by
      dsimp only [negRowNorm, r]
      exact Real.sqrt_nonneg _
    exact mul_nonneg hri hrj
  have hcs :=
    Finset.sum_mul_sq_le_sq_mul_sq
      (s := (Finset.univ : Finset (n × n)))
      (f := fun p : n × n =>
        Real.sqrt (A p.1 p.2) * P p.1 p.2 / Real.sqrt (r p.1 * r p.2))
      (g := fun p : n × n =>
        Real.sqrt (A p.1 p.2) * Real.sqrt (r p.1 * r p.2))
  have hfg :
      (∑ p : n × n,
          (Real.sqrt (A p.1 p.2) * P p.1 p.2 / Real.sqrt (r p.1 * r p.2)) *
            (Real.sqrt (A p.1 p.2) * Real.sqrt (r p.1 * r p.2))) =
        frobeniusInner A P := by
    classical
    have hterm :
        ∀ p : n × n,
          (Real.sqrt (A p.1 p.2) * P p.1 p.2 / Real.sqrt (r p.1 * r p.2)) *
              (Real.sqrt (A p.1 p.2) * Real.sqrt (r p.1 * r p.2)) =
            A p.1 p.2 * P p.1 p.2 := by
      intro p
      set rp := r p.1 * r p.2
      have hr_nonneg' : 0 ≤ rp := hr_nonneg _ _
      by_cases hrp_zero : rp = 0
      · -- One of the norms vanishes, so the whole term is zero.
        have hzero : r p.1 = 0 ∨ r p.2 = 0 := mul_eq_zero.mp hrp_zero
        have hP0 : P p.1 p.2 = 0 := hP_zero_of_r_zero _ _ hzero
        simp only [hP0, hrp_zero, Real.sqrt_zero, div_zero, rp, mul_zero]
      · -- Product is positive, cancel the square root.
        have hr_pos : 0 < rp := lt_of_le_of_ne' hr_nonneg' hrp_zero
        have hsqrt_ne : Real.sqrt rp ≠ 0 := by
          have hsqrt_pos : 0 < Real.sqrt rp := Real.sqrt_pos.mpr hr_pos
          exact ne_of_gt hsqrt_pos
        have hA_nonneg : 0 ≤ A p.1 p.2 := hNonneg _ _
        have hA_sqrt :
            Real.sqrt (A p.1 p.2) * Real.sqrt (A p.1 p.2) = A p.1 p.2 :=
          Real.mul_self_sqrt hA_nonneg
        have hcancel : Real.sqrt rp / Real.sqrt rp = (1 : ℝ) := by
          field_simp [hsqrt_ne]
        calc
          (Real.sqrt (A p.1 p.2) * P p.1 p.2 / Real.sqrt rp) *
              (Real.sqrt (A p.1 p.2) * Real.sqrt rp)
              = ((Real.sqrt (A p.1 p.2))^2 * P p.1 p.2) *
                  (Real.sqrt rp / Real.sqrt rp) := by ring
          _ = ((Real.sqrt (A p.1 p.2))^2 * P p.1 p.2) * 1 := by
                simp only [hcancel, mul_one]
          _ = ((Real.sqrt (A p.1 p.2))^2) * P p.1 p.2 := by ring
          _ = A p.1 p.2 * P p.1 p.2 := by
                simp only [pow_two, hA_sqrt]
    have hsum_prod :
        (∑ p : n × n,
            (Real.sqrt (A p.1 p.2) * P p.1 p.2 / Real.sqrt (r p.1 * r p.2)) *
              (Real.sqrt (A p.1 p.2) * Real.sqrt (r p.1 * r p.2))) =
          ∑ i, ∑ j,
            (Real.sqrt (A i j) * P i j / Real.sqrt (r i * r j)) *
              (Real.sqrt (A i j) * Real.sqrt (r i * r j)) := by
      classical
      simpa only [Finset.univ_product_univ] using
        (Finset.sum_product (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset n)) (f :=
          fun p : n × n =>
          (Real.sqrt (A p.1 p.2) * P p.1 p.2 / Real.sqrt (r p.1 * r p.2)) *
            (Real.sqrt (A p.1 p.2) * Real.sqrt (r p.1 * r p.2))))
    have hsum :
        ∑ i, ∑ j,
            (Real.sqrt (A i j) * P i j / Real.sqrt (r i * r j)) *
              (Real.sqrt (A i j) * Real.sqrt (r i * r j))
          = ∑ i, ∑ j, A i j * P i j := by
      refine Finset.sum_congr rfl ?_; intro i hi
      refine Finset.sum_congr rfl ?_; intro j hj
      simpa only using hterm (i, j)
    have htotal := hsum_prod.trans hsum
    simpa only [mul_left_comm, mul_comm, hinner_P_def] using htotal
  have hf_sq :
      (∑ p : n × n,
          (Real.sqrt (A p.1 p.2) * P p.1 p.2 / Real.sqrt (r p.1 * r p.2))^2) =
        frobeniusInner A M := by
    classical
    have hterm :
        ∀ p : n × n,
          (Real.sqrt (A p.1 p.2) * P p.1 p.2 / Real.sqrt (r p.1 * r p.2))^2 =
            A p.1 p.2 * (P p.1 p.2)^2 / (r p.1 * r p.2) := by
      intro p
      have hA_nonneg : 0 ≤ A p.1 p.2 := hNonneg _ _
      have hr_nonneg' : 0 ≤ r p.1 * r p.2 := hr_nonneg _ _
      have hA_sqrt : (Real.sqrt (A p.1 p.2))^2 = A p.1 p.2 := by
        simpa only [pow_two] using Real.mul_self_sqrt hA_nonneg
      have hr_sqrt : (Real.sqrt (r p.1 * r p.2))^2 = r p.1 * r p.2 := by
        simpa only [pow_two] using Real.mul_self_sqrt hr_nonneg'
      calc
        (Real.sqrt (A p.1 p.2) * P p.1 p.2 / Real.sqrt (r p.1 * r p.2))^2
            = (Real.sqrt (A p.1 p.2))^2 * (P p.1 p.2)^2 /
                (Real.sqrt (r p.1 * r p.2))^2 := by
              ring
        _ = A p.1 p.2 * (P p.1 p.2)^2 / (r p.1 * r p.2) := by
              simp only [hA_sqrt, hr_sqrt]
    have hsum :
        (∑ p : n × n,
            (Real.sqrt (A p.1 p.2) * P p.1 p.2 / Real.sqrt (r p.1 * r p.2))^2) =
          ∑ i, ∑ j, A i j * (P i j)^2 / (r i * r j) := by
      classical
      have hprod :
          (∑ p : n × n,
              (Real.sqrt (A p.1 p.2) * P p.1 p.2 / Real.sqrt (r p.1 * r p.2))^2) =
            ∑ i, ∑ j,
              (Real.sqrt (A i j) * P i j / Real.sqrt (r i * r j))^2 := by
        simpa only [Finset.univ_product_univ] using
          (Finset.sum_product (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset n))
            (f := fun p : n × n =>
            (Real.sqrt (A p.1 p.2) * P p.1 p.2 / Real.sqrt (r p.1 * r p.2)) ^ 2))
      have hpoint :
          ∑ i, ∑ j, (Real.sqrt (A i j) * P i j / Real.sqrt (r i * r j))^2 =
            ∑ i, ∑ j, A i j * (P i j)^2 / (r i * r j) := by
        refine Finset.sum_congr rfl ?_; intro i hi
        refine Finset.sum_congr rfl ?_; intro j hj
        simpa only using hterm (i, j)
      exact hprod.trans hpoint
    simpa only [hinner_M] using hsum
  have hg_sq :
      (∑ p : n × n,
          (Real.sqrt (A p.1 p.2) * Real.sqrt (r p.1 * r p.2))^2) =
        ∑ i, ∑ j, A i j * r i * r j := by
    classical
    have hterm :
        ∀ p : n × n,
          (Real.sqrt (A p.1 p.2) * Real.sqrt (r p.1 * r p.2))^2 =
            A p.1 p.2 * r p.1 * r p.2 := by
      intro p
      have hA_nonneg : 0 ≤ A p.1 p.2 := hNonneg _ _
      have hr_nonneg' : 0 ≤ r p.1 * r p.2 := hr_nonneg _ _
      have hA_sqrt : (Real.sqrt (A p.1 p.2))^2 = A p.1 p.2 := by
        simpa only [pow_two] using Real.mul_self_sqrt hA_nonneg
      have hr_sqrt : (Real.sqrt (r p.1 * r p.2))^2 = r p.1 * r p.2 := by
        simpa only [pow_two] using Real.mul_self_sqrt hr_nonneg'
      calc
        (Real.sqrt (A p.1 p.2) * Real.sqrt (r p.1 * r p.2))^2
            = (Real.sqrt (A p.1 p.2))^2 * (Real.sqrt (r p.1 * r p.2))^2 := by
              ring
        _ = A p.1 p.2 * r p.1 * r p.2 := by
              simp only [hA_sqrt, hr_sqrt, mul_assoc]
    have hsum :
        (∑ p : n × n,
            (Real.sqrt (A p.1 p.2) * Real.sqrt (r p.1 * r p.2))^2) =
          ∑ i, ∑ j, A i j * r i * r j := by
      classical
      have hprod :
          (∑ p : n × n,
              (Real.sqrt (A p.1 p.2) * Real.sqrt (r p.1 * r p.2))^2) =
            ∑ i, ∑ j, (Real.sqrt (A i j) * Real.sqrt (r i * r j))^2 := by
        simpa only [Finset.univ_product_univ] using
          (Finset.sum_product (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset n)) (f :=
            fun p : n × n => (Real.sqrt (A p.1 p.2) * Real.sqrt (r p.1 * r p.2)) ^ 2))
      have hpoint :
          ∑ i, ∑ j, (Real.sqrt (A i j) * Real.sqrt (r i * r j))^2 =
            ∑ i, ∑ j, A i j * r i * r j := by
        refine Finset.sum_congr rfl ?_; intro i hi
        refine Finset.sum_congr rfl ?_; intro j hj
        simpa only using hterm (i, j)
      exact hprod.trans hpoint
    simpa only using hsum
  have hcs_rewrite :
      (frobeniusInner A P)^2 ≤
        frobeniusInner A M * (∑ i, ∑ j, A i j * r i * r j) := by
    simpa only [hfg, hf_sq, hg_sq] using hcs

  have hden_nonneg :
      0 ≤ ∑ i, ∑ j, A i j * r i * r j := by
    classical
    refine Finset.sum_nonneg ?_; intro i _
    exact Finset.sum_nonneg (fun j _ => by
      have hAij := hNonneg i j
      have hri : 0 ≤ r i := by
        dsimp only [negRowNorm, r]
        exact Real.sqrt_nonneg _
      have hrj : 0 ≤ r j := by
        dsimp only [negRowNorm, r]
        exact Real.sqrt_nonneg _
      have hprod : 0 ≤ r i * r j := mul_nonneg hri hrj
      have hterm : 0 ≤ A i j * (r i * r j) := mul_nonneg hAij hprod
      simpa only [mul_assoc, ge_iff_le] using hterm)
  let rE : EuclideanSpace ℝ n := (EuclideanSpace.equiv n ℝ).symm r
  have hnorm_r : ‖rE‖ = 1 := by
    have hsq :=
      sum_negRowNorm_sq (A := A) (hHerm := hHerm) ht hBottom
    have hnorm_sq : ‖rE‖ ^ 2 = 1 := by
      have := hsq
      have habs :
          ∑ i, ‖rE i‖ ^ 2 = 1 := by
        simpa only [rE, r, PiLp.continuousLinearEquiv_symm_apply, negRowNorm, Real.norm_eq_abs,
          sq_abs] using hsq
      simpa only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs] using habs
    nlinarith [hnorm_sq, norm_nonneg rE]
  have hden_le_one :
      ∑ i, ∑ j, A i j * r i * r j ≤ 1 := by
    classical
    let mulVecE : EuclideanSpace ℝ n :=
      (EuclideanSpace.equiv n ℝ).symm (A *ᵥ r)
    have hinner_dot :
        inner (𝕜 := ℝ) rE mulVecE = dotProduct rE mulVecE := by
      classical
      have h :=
        (EuclideanSpace.inner_eq_star_dotProduct (x := rE) (y := mulVecE) :
          _ = dotProduct mulVecE rE)
      simpa only [star_trivial, dotProduct_comm] using h
    have hdot :
        ∑ i, ∑ j, A i j * r i * r j = inner (𝕜 := ℝ) rE mulVecE := by
      have hrewrite :
          ∑ i, ∑ j, A i j * r i * r j =
            ∑ i, r i * (∑ j, A i j * r j) := by
        simp only [mul_assoc, Finset.mul_sum, mul_left_comm]
      have hdot' :
          ∑ i, ∑ j, A i j * r i * r j = dotProduct rE mulVecE := by
        calc
          ∑ i, ∑ j, A i j * r i * r j = ∑ i, r i * (∑ j, A i j * r j) := hrewrite
          _ = dotProduct rE mulVecE := by
            simp only [dotProduct, PiLp.continuousLinearEquiv_symm_apply, mulVec, rE, mulVecE]
      calc
        ∑ i, ∑ j, A i j * r i * r j = dotProduct rE mulVecE := hdot'
        _ = inner (𝕜 := ℝ) rE mulVecE := hinner_dot.symm
    have hinner_nonneg : 0 ≤ inner (𝕜 := ℝ) rE mulVecE := by
      have := hden_nonneg
      simpa only [ge_iff_le, hdot] using this
    have hinner_le :
        inner (𝕜 := ℝ) rE mulVecE ≤ ‖rE‖ * ‖mulVecE‖ := by
      have hpos : |inner (𝕜 := ℝ) rE mulVecE| = inner (𝕜 := ℝ) rE mulVecE :=
        abs_of_nonneg hinner_nonneg
      have habs : |inner (𝕜 := ℝ) rE mulVecE| ≤ ‖rE‖ * ‖mulVecE‖ :=
        abs_real_inner_le_norm rE mulVecE
      simpa only [ge_iff_le, hpos] using habs
    have hmul_le :
        ‖mulVecE‖ ≤ ‖A‖ * ‖rE‖ := by
      simpa only [mulVecE, rE, PiLp.continuousLinearEquiv_symm_apply] using
        Matrix.l2_opNorm_mulVec (A := A) (x := rE)
    have hA_le : ‖A‖ ≤ 1 := hOp
    have hnorm_rvec : ‖rE‖ = 1 := hnorm_r
    have hmul_le' : ‖mulVecE‖ ≤ ‖rE‖ := by
      have hrE_nonneg : 0 ≤ ‖rE‖ := norm_nonneg _
      have hprod_le : ‖A‖ * ‖rE‖ ≤ 1 * ‖rE‖ :=
        mul_le_mul_of_nonneg_right hA_le hrE_nonneg
      exact le_trans hmul_le (by simpa only [one_mul] using hprod_le)
    have hinner_le_one :
        inner (𝕜 := ℝ) rE mulVecE ≤ 1 := by
      have hprod_le : ‖rE‖ * ‖mulVecE‖ ≤ ‖rE‖ * ‖rE‖ :=
        mul_le_mul_of_nonneg_left hmul_le' (norm_nonneg _)
      have hinner_le' :
          inner (𝕜 := ℝ) rE mulVecE ≤ ‖rE‖ * ‖rE‖ :=
        le_trans hinner_le hprod_le
      simpa only [ge_iff_le, hnorm_rvec, mul_one] using hinner_le'
    have hsum_le_one :
        ∑ i, ∑ j, A i j * r i * r j ≤ 1 := by
      linarith [hdot, hinner_le_one]
    exact hsum_le_one

  have hcs' :
      (frobeniusInner A P)^2 ≤ frobeniusInner A M := by
    have hnonnegM : 0 ≤ frobeniusInner A M := by
      have hterms_nonneg :
          ∀ i j, 0 ≤ A i j * (P i j)^2 / (r i * r j) := by
        intro i j
        have hAij := hNonneg i j
        have hsq : 0 ≤ (P i j)^2 := by positivity
        have hnum : 0 ≤ A i j * (P i j)^2 := mul_nonneg hAij hsq
        have hden_nonneg : 0 ≤ r i * r j := by
          have hi : 0 ≤ r i := by
            dsimp only [negRowNorm, r]
            exact Real.sqrt_nonneg _
          have hj : 0 ≤ r j := by
            dsimp only [negRowNorm, r]
            exact Real.sqrt_nonneg _
          exact mul_nonneg hi hj
        exact div_nonneg hnum hden_nonneg
      have hsum_nonneg :
          0 ≤ ∑ i, ∑ j, A i j * (P i j)^2 / (r i * r j) :=
        Finset.sum_nonneg (fun i _ =>
          Finset.sum_nonneg (fun j _ => hterms_nonneg i j))
      simpa only [hinner_M, ge_iff_le] using hsum_nonneg
    have hmul_le : frobeniusInner A M * (∑ i, ∑ j, A i j * r i * r j) ≤
        frobeniusInner A M * 1 :=
      mul_le_mul_of_nonneg_left hden_le_one hnonnegM
    have hden_le :
        frobeniusInner A M * (∑ i, ∑ j, A i j * r i * r j) ≤ frobeniusInner A M := by
      simpa only [mul_one] using hmul_le
    exact le_trans hcs_rewrite hden_le

  exact le_trans hinnerP_sq hcs'

theorem lemma4_4
    (hNonneg : ∀ i j, 0 ≤ A i j) (hOp : ‖A‖ ≤ (1 : ℝ))
    {μ : ℝ} (hμ : 0 ≤ μ) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    ∃ M : Matrix n n ℝ,
      Matrix.PosSemidef M ∧
      Matrix.trace M = 1 ∧
      frobeniusSq M ≤ 1 / (t : ℝ) ∧
      frobeniusInner A M ≥ μ^2 := by
  classical
  let M := negWitnessM (A := A) (hHerm := hHerm) ht hBottom
  refine ⟨M,
    negWitnessM_posSemidef (A := A) (hHerm := hHerm) ht hBottom,
    ?trace, ?frob, ?inner⟩
  · simpa only using (negWitnessM_trace_one (A := A) (hHerm := hHerm) ht hBottom)
  · simpa only [one_div] using
    (negWitnessM_frobeniusSq (A := A) (hHerm := hHerm) ht hBottom)
  · simpa only [ge_iff_le] using
    (negWitnessM_inner_bound (A := A) (hHerm := hHerm) (hNonneg := hNonneg)
      (hOp := hOp) (hμ := hμ) (ht := ht) hBottom)

end Lemma4_4_new

end ThresholdRank

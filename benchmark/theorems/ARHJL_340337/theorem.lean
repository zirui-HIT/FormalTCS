import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real

open scoped BigOperators
open MeasureTheory

abbrev cool_matrix (m n : ℕ) := Fin n → Fin m → ℝ

noncomputable def cool_gaussian_column_measure (m : ℕ) : Measure (Fin m → ℝ) :=
  Measure.pi fun _ => ProbabilityTheory.gaussianReal 0 1

noncomputable def cool_gaussian_matrix_measure (m n : ℕ) : Measure (cool_matrix m n) :=
  Measure.pi fun _ => cool_gaussian_column_measure m

def cool_initial_block_length (n m B K : ℕ) : ℕ :=
  n - K * m * Nat.log2 B

def cool_temperature (n m B K : ℕ) (j : Fin n) : ℕ :=
  if j.1 < cool_initial_block_length n m B K then
    B
  else
    B / 2 ^ (1 + (j.1 - cool_initial_block_length n m B K) / (K * m))

noncomputable def cool_column {m n : ℕ} (A : cool_matrix m n) (j : Fin n) :
    EuclideanSpace ℝ (Fin m) :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm (A j)

noncomputable def cool_state (n m B K : ℕ) (A : cool_matrix m n) :
    ℕ → EuclideanSpace ℝ (Fin m)
  | 0 => 0
  | t + 1 =>
      if ht : t < n then
        let j : Fin n := ⟨t, ht⟩
        let y := cool_state n m B K A t
        let a := cool_column A j
        let b : ℝ := cool_temperature n m B K j
        if ‖y - b • a‖ ≤ ‖y + b • a‖ then y - b • a else y + b • a
      else
        cool_state n m B K A t

noncomputable def cool_output (n m B K : ℕ) (A : cool_matrix m n) (j : Fin n) : ℝ :=
  let y := cool_state n m B K A j.1
  let a := cool_column A j
  let b : ℝ := cool_temperature n m B K j
  if ‖y - b • a‖ ≤ ‖y + b • a‖ then -b else b

noncomputable def cool_matrix_vector {m n : ℕ} (A : cool_matrix m n) (x : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin m) :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm fun i => ∑ j, A j i * x j

noncomputable def cool_contraction_ratio {m n : ℕ} (A : cool_matrix m n) (x : Fin n → ℝ) : ℝ :=
  ‖cool_matrix_vector A x‖ /
    ‖(EuclideanSpace.equiv (Fin n) ℝ).symm x‖

noncomputable def cool_bad_event (n m B K : ℕ) (C : ℝ) : Set (cool_matrix m n) :=
  {A | cool_contraction_ratio A (cool_output n m B K A) >
    C * (m : ℝ) / ((B : ℝ) * Real.sqrt (n : ℝ))}

theorem cool_online_algorithm_guarantee :
    ∃ K₀ : ℕ, ∃ C_ratio C_fail c : ℝ,
      0 < C_ratio ∧ 0 < C_fail ∧ 0 < c ∧
      ∀ (m n B K : ℕ),
        m < n → Nat.isPowerOfTwo B → 2 ≤ B → K₀ ≤ K →
        2 * K * m * Nat.log2 B ≤ n →
        (cool_gaussian_matrix_measure m n).real
          (cool_bad_event n m B K C_ratio) ≤
          C_fail * (Nat.log2 B : ℝ) * Real.exp (-c * (m : ℝ)) := by sorry

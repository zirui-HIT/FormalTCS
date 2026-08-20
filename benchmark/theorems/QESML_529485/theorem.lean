import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Matrix.Mul
import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option linter.all false
set_option maxHeartbeats 500000

abbrev qesml_real_vector (n : ℕ) := Fin n → ℝ

abbrev qesml_real_matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

inductive qesml_matvec_side where
  | forward
  | transpose

inductive qesml_matvec_program (n : ℕ) (α : Type) where
  | pure (value : α)
  | query (side : qesml_matvec_side) (input : qesml_real_vector n)
      (next : qesml_real_vector n → qesml_matvec_program n α)

def qesml_matvec_response {n : ℕ} (A : qesml_real_matrix n)
    (side : qesml_matvec_side) (x : qesml_real_vector n) : qesml_real_vector n :=
  match side with
  | .forward => Matrix.mulVec A x
  | .transpose => Matrix.mulVec A.transpose x

def qesml_execute_matvec_program {n : ℕ} {α : Type} (A : qesml_real_matrix n) :
    qesml_matvec_program n α → α
  | .pure value => value
  | .query side input next =>
      qesml_execute_matvec_program A (next (qesml_matvec_response A side input))

def qesml_matvec_query_count {n : ℕ} {α : Type} (A : qesml_real_matrix n) :
    qesml_matvec_program n α → ℕ
  | .pure _ => 0
  | .query side input next =>
      1 + qesml_matvec_query_count A (next (qesml_matvec_response A side input))

structure qesml_randomized_matvec_algorithm (n : ℕ) where
  Seed : Type
  seedDistribution : Finset (qesml_real_matrix n) → ℝ → ℝ → PMF Seed
  program : Finset (qesml_real_matrix n) → ℝ → ℝ → Seed →
    qesml_matvec_program n (qesml_real_matrix n)

noncomputable def qesml_algorithm_output {n : ℕ}
    (algorithm : qesml_randomized_matvec_algorithm n) (A : qesml_real_matrix n)
    (family : Finset (qesml_real_matrix n)) (ε δ : ℝ) : PMF (qesml_real_matrix n) :=
  PMF.map
    (fun seed => qesml_execute_matvec_program A (algorithm.program family ε δ seed))
    (algorithm.seedDistribution family ε δ)

noncomputable def qesml_frobenius_norm {n : ℕ} (A : qesml_real_matrix n) : ℝ :=
  Real.sqrt (∑ i, ∑ j, (A i j) ^ 2)

noncomputable def qesml_frobenius_distance {n : ℕ}
    (A B : qesml_real_matrix n) : ℝ :=
  qesml_frobenius_norm (A - B)

noncomputable def qesml_best_family_error {n : ℕ} (A : qesml_real_matrix n)
    (family : Finset (qesml_real_matrix n)) (hFamily : family.Nonempty) : ℝ :=
  family.inf' hFamily (fun B => qesml_frobenius_distance A B)

def qesml_successful_approximation {n : ℕ} (A : qesml_real_matrix n)
    (family : Finset (qesml_real_matrix n)) (hFamily : family.Nonempty)
    (ε : ℝ) (B : qesml_real_matrix n) : Prop :=
  B ∈ family ∧
    qesml_frobenius_distance A B ≤
      (3 + ε) * qesml_best_family_error A family hFamily

noncomputable def qesml_query_envelope (familySize : ℕ) (ε δ : ℝ)
    (inputPower failurePower : ℕ) : ℝ :=
  (Real.sqrt (Real.log (familySize : ℝ)) / ε ^ 2) *
    (Real.log (2 + (familySize : ℝ)) + Real.log (2 + ε⁻¹)) ^ inputPower *
    (Real.log (2 + δ⁻¹)) ^ failurePower

def qesml_has_soft_query_bound
    (algorithm : (n : ℕ) → qesml_randomized_matvec_algorithm n) : Prop :=
  ∃ (C : ℝ) (inputPower failurePower : ℕ),
    0 < C ∧
      ∀ (n : ℕ) (family : Finset (qesml_real_matrix n)) (hFamily : family.Nonempty)
        (ε δ : ℝ) (A : qesml_real_matrix n) (seed : (algorithm n).Seed),
        0 < ε → ε < 1 → 0 < δ → δ < 1 →
        seed ∈ ((algorithm n).seedDistribution family ε δ).support →
        (qesml_matvec_query_count A ((algorithm n).program family ε δ seed) : ℝ) ≤
          C * qesml_query_envelope family.card ε δ inputPower failurePower

def qesml_has_high_probability_guarantee {n : ℕ}
    (algorithm : qesml_randomized_matvec_algorithm n) : Prop :=
  ∀ (family : Finset (qesml_real_matrix n)) (hFamily : family.Nonempty)
    (ε δ : ℝ) (A : qesml_real_matrix n),
    0 < ε → ε < 1 → 0 < δ → δ < 1 →
    ENNReal.ofReal (1 - δ) ≤
      (qesml_algorithm_output algorithm A family ε δ).toOuterMeasure
        {B | qesml_successful_approximation A family hFamily ε B}

def qesml_solves_finite_family_approximation
    (algorithm : (n : ℕ) → qesml_randomized_matvec_algorithm n) : Prop :=
  qesml_has_soft_query_bound algorithm ∧
    ∀ n : ℕ, qesml_has_high_probability_guarantee (algorithm n)

theorem finite_family_approximation :
    ∃ algorithm : (n : ℕ) → qesml_randomized_matvec_algorithm n,
      qesml_solves_finite_family_approximation algorithm := by sorry

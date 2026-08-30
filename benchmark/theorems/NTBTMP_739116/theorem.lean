import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Matrix.Basic

abbrev metric_matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def clean_matrix {n : ℕ} (M : metric_matrix n) : Prop :=
  (∀ i, M i i = 0) ∧
    (∀ i j, i ≠ j → 0 < M i j) ∧
      ∀ i j, M i j = M j i

def metric_matrix_property {n : ℕ} (M : metric_matrix n) : Prop :=
  clean_matrix M ∧ ∀ i j k, M i k ≤ M i j + M j k

noncomputable def matrix_hamming_distance {n : ℕ} (M N : metric_matrix n) : ℕ := by
  classical
  exact ((Finset.univ.product Finset.univ).filter fun p => M p.1 p.2 ≠ N p.1 p.2).card

def epsilon_far_from_metric {n : ℕ} (ε : ℝ) (M : metric_matrix n) : Prop :=
  ∀ N : metric_matrix n,
    metric_matrix_property N →
      ε * (n : ℝ) ^ (2 : ℕ) ≤ (matrix_hamming_distance M N : ℝ)

structure nonadaptive_matrix_tester (n : ℕ) where
  Seed : Type
  coins : PMF Seed
  queries : Seed → Finset (Fin n × Fin n)
  output : Seed → metric_matrix n → Bool
  output_eq_of_query_eq :
    ∀ seed M N,
      (∀ p ∈ queries seed, M p.1 p.2 = N p.1 p.2) →
        output seed M = output seed N

noncomputable def tester_acceptance_probability {n : ℕ} (A : nonadaptive_matrix_tester n)
    (M : metric_matrix n) : ENNReal :=
  (A.coins.map fun seed => A.output seed M) true

noncomputable def tester_rejection_probability {n : ℕ} (A : nonadaptive_matrix_tester n)
    (M : metric_matrix n) : ENNReal :=
  (A.coins.map fun seed => A.output seed M) false

def tester_uses_at_most {n : ℕ} (A : nonadaptive_matrix_tester n) (q : ℝ) : Prop :=
  ∀ seed, ((A.queries seed).card : ℝ) ≤ q

def metric_tester_guarantee {n : ℕ} (A : nonadaptive_matrix_tester n) (ε : ℝ) : Prop :=
  (∀ M : metric_matrix n,
      metric_matrix_property M → tester_acceptance_probability A M = 1) ∧
    ∀ M : metric_matrix n,
      epsilon_far_from_metric ε M →
        (2 : ENNReal) / 3 ≤ tester_rejection_probability A M

noncomputable def metric_testing_query_scale (n : ℕ) (ε : ℝ) : ℝ :=
  (n : ℝ) ^ (2 / 3 : ℝ) / ε ^ (4 / 3 : ℝ)

theorem testing_metrics_upper_bound :
    ∃ n₀ : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∃ A : nonadaptive_matrix_tester n,
          tester_uses_at_most A (C * metric_testing_query_scale n ε) ∧
            metric_tester_guarantee A ε := by sorry

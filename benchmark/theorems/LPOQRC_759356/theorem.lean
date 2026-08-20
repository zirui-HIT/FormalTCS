import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite

abbrev same_set_query (U : Type) := U × U

abbrev same_set_oracle (U : Type) := same_set_query U → Bool

def same_set_oracle_represents {U : Type} (P : Setoid U)
    (oracle : same_set_oracle U) : Prop :=
  ∀ x y : U, oracle (x, y) = true ↔ P.r x y

inductive deterministic_pair_query_algorithm (U : Type) : ℕ → Type where
  | output (learnedPartition : Setoid U) : deterministic_pair_query_algorithm U 0
  | query {remainingRounds : ℕ} (batch : List (same_set_query U))
      (next : (Fin batch.length → Bool) →
        deterministic_pair_query_algorithm U remainingRounds) :
      deterministic_pair_query_algorithm U (remainingRounds + 1)

def run_pair_query_algorithm {U : Type} :
    {rounds : ℕ} → deterministic_pair_query_algorithm U rounds →
      same_set_oracle U → Setoid U
  | 0, .output learnedPartition, _ => learnedPartition
  | _ + 1, .query batch next, oracle =>
      run_pair_query_algorithm (next (fun i => oracle (batch.get i))) oracle

def pair_query_count {U : Type} :
    {rounds : ℕ} → deterministic_pair_query_algorithm U rounds →
      same_set_oracle U → ℕ
  | 0, .output _, _ => 0
  | _ + 1, .query batch next, oracle =>
      batch.length + pair_query_count (next (fun i => oracle (batch.get i))) oracle

def pair_query_algorithm_learns {U : Type} {rounds : ℕ}
    (algorithm : deterministic_pair_query_algorithm U rounds) (P : Setoid U) : Prop :=
  ∀ oracle : same_set_oracle U,
    same_set_oracle_represents P oracle → run_pair_query_algorithm algorithm oracle = P

def partition_has_at_most_classes {U : Type} (P : Setoid U) (k : ℕ) : Prop :=
  Nat.card (Quotient P) ≤ k

noncomputable def pair_query_budget (n k r : ℕ) : ℝ :=
  8 * Real.rpow (n : ℝ) (1 + 1 / ((2 : ℝ) ^ r - 1)) *
    Real.rpow (k : ℝ) (1 - 1 / ((2 : ℝ) ^ r - 1))

def learns_k_partitions_with_budget {U : Type} [Fintype U] {rounds : ℕ}
    (algorithm : deterministic_pair_query_algorithm U rounds) (k : ℕ) (budget : ℝ) : Prop :=
  ∀ P : Setoid U, partition_has_at_most_classes P k →
    pair_query_algorithm_learns algorithm P ∧
      ∀ oracle : same_set_oracle U, same_set_oracle_represents P oracle →
        (pair_query_count algorithm oracle : ℝ) ≤ budget

theorem pair_query_upper_bound (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k)
    (U : Type) [Fintype U] :
    ∃ algorithm : deterministic_pair_query_algorithm U r,
      learns_k_partitions_with_budget algorithm k
        (pair_query_budget (Fintype.card U) k r) := by sorry

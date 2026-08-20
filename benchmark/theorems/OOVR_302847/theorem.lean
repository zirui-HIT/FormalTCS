import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Sum

set_option linter.all false

abbrev online_ov_vector (d : ℕ) := Fin d → Bool

def online_ov_dot_product_on {d : ℕ} (C : Finset (Fin d))
    (x q : online_ov_vector d) : ℕ :=
  ∑ j ∈ C, (x j).toNat * (q j).toNat

def online_ov_orthogonal {d : ℕ} (x q : online_ov_vector d) : Prop :=
  online_ov_dot_product_on Finset.univ x q = 0

structure deterministic_online_ov_algorithms (n d : ℕ) where
  State : Type
  encodeState : State → List Bool
  encodeState_injective : Function.Injective encodeState
  preprocess : (Fin n → online_ov_vector d) → State × ℕ
  query : State → online_ov_vector d → Bool × ℕ

def solves_online_ov {n d : ℕ} (A : deterministic_online_ov_algorithms n d) : Prop :=
  ∀ (X : Fin n → online_ov_vector d) (q : online_ov_vector d),
    (A.query (A.preprocess X).1 q).1 = true ↔
      ∃ j : Fin n, online_ov_orthogonal (X j) q

def partial_binomial_sum (d t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (t + 1), Nat.choose d j

noncomputable def online_ov_query_bound (n d i : ℕ) : ℝ :=
  2 * (i : ℝ) * (d : ℝ) * (n : ℝ) ^ (1 - 1 / (i : ℝ))

noncomputable def online_ov_space_bound (n d i : ℕ) : ℝ :=
  (partial_binomial_sum d (d / i) : ℝ) * (i : ℝ) * (d : ℝ) *
    (n : ℝ) ^ (1 - 1 / (i : ℝ))

def online_ov_preprocessing_bound (n d i : ℕ) : ℝ :=
  (partial_binomial_sum d (d / i) : ℝ) * (i : ℝ) * (d : ℝ) * (n : ℝ)

def bounded_online_ov_data_structure
    (n d i : ℕ) (A : deterministic_online_ov_algorithms n d) : Prop :=
  solves_online_ov A ∧
    (∀ (X : Fin n → online_ov_vector d) (q : online_ov_vector d),
      ((A.query (A.preprocess X).1 q).2 : ℝ) ≤ online_ov_query_bound n d i) ∧
    (∀ X : Fin n → online_ov_vector d,
      ((A.encodeState (A.preprocess X).1).length : ℝ) ≤ online_ov_space_bound n d i) ∧
    (∀ X : Fin n → online_ov_vector d,
      ((A.preprocess X).2 : ℝ) ≤ online_ov_preprocessing_bound n d i)

theorem worst_case_algorithm_parameterized :
    ∃ OV : (n d i : ℕ) → deterministic_online_ov_algorithms n d,
      ∀ (n d i : ℕ) (hn : 1 ≤ n) (hi : 1 ≤ i) (hid : i ≤ d),
        bounded_online_ov_data_structure n d i (OV n d i) := by sorry

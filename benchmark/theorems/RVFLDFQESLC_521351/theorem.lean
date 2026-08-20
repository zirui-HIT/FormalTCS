import Mathlib.Algebra.Field.ZMod
import Mathlib.InformationTheory.Hamming
import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option maxHeartbeats 500000

noncomputable section

abbrev binary_word (n : ℕ) := Fin n → ZMod 2

structure binary_linear_code (k n : ℕ) where
  encode : binary_word k →ₗ[ZMod 2] binary_word n
  injective : Function.Injective encode

inductive binary_oracle_tree (n : ℕ) (A : Type) where
  | output : A → binary_oracle_tree n A
  | query : Fin n → binary_oracle_tree n A → binary_oracle_tree n A →
      binary_oracle_tree n A

def binary_oracle_tree_eval {n : ℕ} {A : Type} (y : binary_word n) :
    binary_oracle_tree n A → A
  | .output a => a
  | .query i zeroBranch oneBranch =>
      if y i = 0 then
        binary_oracle_tree_eval y zeroBranch
      else
        binary_oracle_tree_eval y oneBranch

def binary_oracle_tree_depth {n : ℕ} {A : Type} : binary_oracle_tree n A → ℕ
  | .output _ => 0
  | .query _ zeroBranch oneBranch =>
      1 + max (binary_oracle_tree_depth zeroBranch) (binary_oracle_tree_depth oneBranch)

abbrev randomized_adaptive_decoder (n m : ℕ) (A : Type) :=
  Fin m → PMF (binary_oracle_tree n A)

def randomized_adaptive_decoder_output {n m : ℕ} {A : Type}
    (D : randomized_adaptive_decoder n m A) (y : binary_word n) (i : Fin m) : PMF A :=
  PMF.map (binary_oracle_tree_eval y) (D i)

def decoder_uses_at_most_queries {n m q : ℕ} {A : Type}
    (D : randomized_adaptive_decoder n m A) : Prop :=
  ∀ i tree, tree ∈ (D i).support → binary_oracle_tree_depth tree ≤ q

def binary_decoding_error (p : PMF (ZMod 2)) (a : ZMod 2) : ENNReal :=
  ∑' z, if z = a then 0 else p z

def binary_relaxed_decoding_error (p : PMF (Option (ZMod 2))) (a : ZMod 2) : ENNReal :=
  ∑' z, if z = some a ∨ z = none then 0 else p z

def within_relative_hamming_radius {k n : ℕ} (C : binary_linear_code k n)
    (δ : ℝ) (b : binary_word k) (y : binary_word n) : Prop :=
  (hammingDist y (C.encode b) : ℝ) ≤ δ * (n : ℝ)

def is_binary_rlcc {k n : ℕ} (C : binary_linear_code k n)
    (q : ℕ) (δ c s : ℝ) : Prop :=
  ∃ D : randomized_adaptive_decoder n n (Option (ZMod 2)),
    decoder_uses_at_most_queries (q := q) D ∧
      (∀ b u,
        randomized_adaptive_decoder_output D (C.encode b) u (some (C.encode b u)) ≥
          ENNReal.ofReal c) ∧
      (∀ b u y,
        within_relative_hamming_radius C δ b y →
          binary_relaxed_decoding_error
              (randomized_adaptive_decoder_output D y u) (C.encode b u) ≤ ENNReal.ofReal s)

def is_binary_lcc {k n : ℕ} (C : binary_linear_code k n)
    (q : ℕ) (δ c s : ℝ) : Prop :=
  ∃ D : randomized_adaptive_decoder n n (ZMod 2),
    decoder_uses_at_most_queries (q := q) D ∧
      (∀ b u,
        randomized_adaptive_decoder_output D (C.encode b) u (C.encode b u) ≥
          ENNReal.ofReal c) ∧
      (∀ b u y,
        within_relative_hamming_radius C δ b y →
          binary_decoding_error (randomized_adaptive_decoder_output D y u) (C.encode b u) ≤
            ENNReal.ofReal s)

def binary_soundness_threshold (q : ℕ) : ℝ :=
  ((2 : ℝ) ^ (q / 2))⁻¹

theorem rlcc_soundness_threshold {k n q : ℕ} {δ s α : ℝ}
    (C : binary_linear_code k n)
    (hδ_nonnegative : 0 ≤ δ) (hδ_at_most_one : δ ≤ 1)
    (hs_nonnegative : 0 ≤ s) (hs_at_most_one : s ≤ 1)
    (hα_nonnegative : 0 ≤ α) (hα_at_most_one : α ≤ 1)
    (hRLCC : is_binary_rlcc C q δ 1 s)
    (hthreshold : s ≤ (1 - α) * binary_soundness_threshold q)
    (ε : ℝ) (hε : 0 < ε) :
    is_binary_lcc C q (α * δ * ε / (q : ℝ)) 1 ε := by sorry

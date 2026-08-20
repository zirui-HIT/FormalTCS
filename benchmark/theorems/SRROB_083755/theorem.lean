import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.BitVec
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.ProductMeasure

set_option linter.all false
set_option maxHeartbeats 500000

abbrev random_tape : Type := ℕ → Bool

noncomputable def fair_bit_measure : MeasureTheory.Measure Bool :=
  ProbabilityTheory.bernoulliMeasure false true
    ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩

noncomputable def fair_random_tape_measure : MeasureTheory.Measure random_tape :=
  MeasureTheory.Measure.infinitePi (fun _ : ℕ => fair_bit_measure)

structure static_retrieval_instance (U n V : ℕ) where
  keySet : Finset (Fin U)
  keySet_card : keySet.card = n
  value : Fin U → Fin V

inductive retrieval_probe_tree (m w V : ℕ) where
  | answer : Fin V → retrieval_probe_tree m w V
  | probe : Fin m → (BitVec w → retrieval_probe_tree m w V) →
      retrieval_probe_tree m w V

def execute_retrieval_probe_tree {m w V : ℕ}
    (memory : Fin m → BitVec w) : retrieval_probe_tree m w V → Fin V
  | .answer output => output
  | .probe address next =>
      execute_retrieval_probe_tree memory (next (memory address))

def count_retrieval_probes {m w V : ℕ}
    (memory : Fin m → BitVec w) : retrieval_probe_tree m w V → ℕ
  | .answer _ => 0
  | .probe address next =>
      1 + count_retrieval_probes memory (next (memory address))

structure randomized_static_retrieval_scheme (U n V w m : ℕ) where
  encode :
    static_retrieval_instance U n V → random_tape → Fin m → BitVec w
  query : Fin U → random_tape → retrieval_probe_tree m w V
  correct :
    ∀ (input : static_retrieval_instance U n V) (x : Fin U),
      x ∈ input.keySet →
      ∀ tape : random_tape,
        execute_retrieval_probe_tree (encode input tape) (query x tape) =
          input.value x

noncomputable def expected_retrieval_query_cost {U n V w m : ℕ}
    (scheme : randomized_static_retrieval_scheme U n V w m)
    (input : static_retrieval_instance U n V) (x : Fin U) : ℝ :=
  ∫ tape : random_tape,
    (count_retrieval_probes (scheme.encode input tape)
      (scheme.query x tape) : ℝ) ∂fair_random_tape_measure

def has_expected_query_cost {U n V w m : ℕ}
    (scheme : randomized_static_retrieval_scheme U n V w m) (t : ℕ) : Prop :=
  ∀ (input : static_retrieval_instance U n V) (x : Fin U),
    x ∈ input.keySet →
      MeasureTheory.Integrable
          (fun tape : random_tape =>
            (count_retrieval_probes (scheme.encode input tape)
              (scheme.query x tape) : ℝ))
          fair_random_tape_measure ∧
        expected_retrieval_query_cost scheme input x ≤ (t : ℝ)

def polynomial_retrieval_parameters
    (n U V w a b : ℕ) : Prop :=
  2 * n ≤ U ∧ U ≤ n ^ a ∧ V ≤ n ^ b ∧ 1 < V ∧
    Real.logb 2 (V : ℝ) ≤ (w : ℝ)

noncomputable def retrieval_space_threshold
    (C : ℝ) (n V w t : ℕ) : ℝ :=
  (n : ℝ) * Real.logb 2 (V : ℝ) +
    (Nat.floor
      ((n : ℝ) * Real.exp
        (-C * (((w : ℝ) * (t : ℝ)) / Real.logb 2 (V : ℝ)))) : ℝ)

theorem randomized_static_retrieval_space_lower_bound :
    ∀ (a b : ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (n U V w t m : ℕ)
        (scheme : randomized_static_retrieval_scheme U n V w m),
        polynomial_retrieval_parameters n U V w a b →
        has_expected_query_cost scheme t →
        retrieval_space_threshold C n V w t ≤ (m : ℝ) * (w : ℝ) := by sorry

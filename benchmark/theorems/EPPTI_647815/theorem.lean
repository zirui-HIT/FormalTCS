import Mathlib.InformationTheory.Hamming
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

set_option linter.all false

abbrev boolean_domain (n : ℕ) := Fin n → Bool

abbrev boolean_function (n : ℕ) := boolean_domain n → Bool

abbrev boolean_property (n : ℕ) := Set (boolean_function n)

noncomputable def boolean_function_distance {n : ℕ}
    (f g : boolean_function n) : ℝ :=
  (hammingDist f g : ℝ) / (Fintype.card (boolean_domain n) : ℝ)

def property_neighborhood {n : ℕ} (P : boolean_property n) (ε : ℝ) :
    boolean_property n :=
  {f | ∃ g ∈ P, boolean_function_distance f g ≤ ε}

inductive boolean_circuit_source (ι : Type)
  | input (index : ι)
  | gate (index : ℕ)

inductive boolean_circuit_gate (ι : Type)
  | constant (value : Bool)
  | neg (source : boolean_circuit_source ι)
  | conj (left right : boolean_circuit_source ι)
  | disj (left right : boolean_circuit_source ι)
  | xor (left right : boolean_circuit_source ι)

structure boolean_circuit (ι : Type) (outputWidth : ℕ) where
  gates : List (boolean_circuit_gate ι)
  outputs : Fin outputWidth → boolean_circuit_source ι

def boolean_circuit_source_value {ι : Type} (assignment : ι → Bool)
    (values : Array Bool) : boolean_circuit_source ι → Bool
  | .input index => assignment index
  | .gate index => values.getD index false

def boolean_circuit_gate_value {ι : Type} (assignment : ι → Bool)
    (values : Array Bool) : boolean_circuit_gate ι → Bool
  | .constant value => value
  | .neg source => !(boolean_circuit_source_value assignment values source)
  | .conj left right =>
      boolean_circuit_source_value assignment values left &&
        boolean_circuit_source_value assignment values right
  | .disj left right =>
      boolean_circuit_source_value assignment values left ||
        boolean_circuit_source_value assignment values right
  | .xor left right =>
      xor (boolean_circuit_source_value assignment values left)
        (boolean_circuit_source_value assignment values right)

def boolean_circuit_gate_values {ι : Type} {outputWidth : ℕ}
    (circuit : boolean_circuit ι outputWidth) (assignment : ι → Bool) :
    Array Bool :=
  circuit.gates.foldl
    (fun values gate => values.push (boolean_circuit_gate_value assignment values gate)) #[]

def boolean_circuit_eval {ι : Type} {outputWidth : ℕ}
    (circuit : boolean_circuit ι outputWidth) (assignment : ι → Bool) :
    Fin outputWidth → Bool :=
  fun output => boolean_circuit_source_value assignment
    (boolean_circuit_gate_values circuit assignment) (circuit.outputs output)

def boolean_circuit_size {ι : Type} {outputWidth : ℕ}
    (circuit : boolean_circuit ι outputWidth) : ℕ :=
  circuit.gates.length + outputWidth

inductive sample_tester_input (n m randomBits : ℕ)
  | point (sample : Fin m) (coordinate : Fin n)
  | label (sample : Fin m)
  | random (bit : Fin randomBits)

structure sample_tester (n m : ℕ) where
  randomBits : ℕ
  circuit : boolean_circuit (sample_tester_input n m randomBits) 1

def sample_tester_assignment {n m randomBits : ℕ}
    (samples : Fin m → boolean_domain n) (f : boolean_function n)
    (coins : Fin randomBits → Bool) : sample_tester_input n m randomBits → Bool
  | .point sample coordinate => samples sample coordinate
  | .label sample => f (samples sample)
  | .random bit => coins bit

def sample_tester_accepts {n m : ℕ} (tester : sample_tester n m)
    (f : boolean_function n) (samples : Fin m → boolean_domain n)
    (coins : Fin tester.randomBits → Bool) : Bool :=
  boolean_circuit_eval tester.circuit
    (sample_tester_assignment samples f coins) 0

def sample_tester_acceptance_count {n m : ℕ} (tester : sample_tester n m)
    (f : boolean_function n) : ℕ :=
  ((Finset.univ : Finset
      ((Fin m → boolean_domain n) × (Fin tester.randomBits → Bool))).filter
    (fun world => sample_tester_accepts tester f world.1 world.2 = true)).card

def sample_tester_world_count {n m : ℕ} (tester : sample_tester n m) : ℕ :=
  Fintype.card ((Fin m → boolean_domain n) × (Fin tester.randomBits → Bool))

def sample_testable {n : ℕ} (P : boolean_property n) (ε : ℝ) (m s : ℕ) : Prop :=
  ∃ tester : sample_tester n m,
    boolean_circuit_size tester.circuit ≤ s ∧
      (∀ f ∈ P, 2 * sample_tester_world_count tester ≤
        3 * sample_tester_acceptance_count tester f) ∧
      (∀ f ∉ property_neighborhood P ε,
        3 * sample_tester_acceptance_count tester f ≤
          sample_tester_world_count tester)

def permutation_preserves_parts {n k : ℕ}
    (part : boolean_domain n → Fin k) (σ : Equiv.Perm (boolean_domain n)) : Prop :=
  ∀ x, part (σ x) = part x

def property_part_symmetric {n k : ℕ} (Q : boolean_property n)
    (part : boolean_domain n → Fin k) : Prop :=
  ∀ (σ : Equiv.Perm (boolean_domain n)), permutation_preserves_parts part σ →
    ∀ f : boolean_function n, f ∈ Q ↔ (fun x => f (σ x)) ∈ Q

def partition_has_circuit_complexity {n k : ℕ}
    (part : boolean_domain n → Fin k) (bound : ℕ) : Prop :=
  ∃ (width : ℕ) (encoding : Fin k → (Fin width → Bool)),
    Function.Injective encoding ∧
      ∃ circuit : boolean_circuit (Fin n) width,
        boolean_circuit_size circuit ≤ bound ∧
          ∀ x : boolean_domain n,
            boolean_circuit_eval circuit x = encoding (part x)

def structured_symmetric_property {n : ℕ} (Q : boolean_property n)
    (k bound : ℕ) : Prop :=
  ∃ part : boolean_domain n → Fin k,
    property_part_symmetric Q part ∧
      partition_has_circuit_complexity part bound

def double_exponential_bound (constant m k : ℕ) : Prop :=
  k ≤ 2 ^ (2 ^ (constant * (m + 1)))

def exponential_times_bound (constant m s bound : ℕ) : Prop :=
  bound ≤ 2 ^ (constant * (m + 1)) * s

theorem main_hard :
    ∃ partConstant partitionConstant : ℕ,
      ∀ (n m s : ℕ) (ε : ℝ) (P : boolean_property n),
        0 ≤ ε →
          sample_testable P ε m s →
            ∃ (k : ℕ) (Q : boolean_property n) (partitionBound : ℕ),
              P ⊆ Q ∧
                Q ⊆ property_neighborhood P ε ∧
                structured_symmetric_property Q k partitionBound ∧
                double_exponential_bound partConstant m k ∧
                exponential_times_bound partitionConstant m s partitionBound := by sorry

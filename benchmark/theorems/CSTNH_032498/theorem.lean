import Mathlib.Data.Nat.Log
import Mathlib.Computability.PartrecCode
import Mathlib.InformationTheory.Hamming
import Mathlib.Logic.Encodable.Pi

open scoped BigOperators

abbrev binary_string (n : ℕ) := Fin n → Bool

noncomputable instance binary_string_encodable (n : ℕ) : Encodable (binary_string n) :=
  Encodable.ofEquiv (Fin (Fintype.card (binary_string n)))
    (Fintype.equivFin (binary_string n))

def finite_type_code {α : Type*} [Encodable α] (x : α) : ℕ :=
  Encodable.encode x

abbrev language_family := ∀ n : ℕ, binary_string n → Prop

abbrev boolean_concept_class (α : Type*) := Set (α → Bool)

def set_shatters {α : Type*} (C : boolean_concept_class α) (W : Set α) : Prop :=
  ∀ W' ⊆ W, ∃ c ∈ C, c ⁻¹' {true} ∩ W = W'

noncomputable def vc_dimension {α : Type*} (C : boolean_concept_class α) : ℕ :=
  sSup {n : ℕ | ∃ W : Finset α, W.card = n ∧ set_shatters C (↑W)}

inductive register_machine_instruction where
  | halt
  | increment (register next : ℕ)
  | decrement (register positive zero : ℕ)
  | loadLiteral (value register next : ℕ)
  | indirectRead (addressRegister outputRegister next : ℕ)
  | indirectWrite (sourceRegister addressRegister next : ℕ)
  | pair (leftRegister rightRegister outputRegister next : ℕ)
  | pairLeft (sourceRegister outputRegister next : ℕ)
  | pairRight (sourceRegister outputRegister next : ℕ)
  | branchEqual (leftRegister rightRegister equalNext unequalNext : ℕ)
  | oracleQuery (lengthRegister inputRegister outputRegister next : ℕ)
  | sampleQuery (indexRegister pointOutputRegister labelOutputRegister next : ℕ)
  | sampleQueryIndirect
      (indexRegister pointOutputAddressRegister labelOutputRegister next : ℕ)
  deriving DecidableEq

abbrev machine_program := List register_machine_instruction

def register_machine_instruction_code : register_machine_instruction → ℕ
  | .halt => 0
  | .increment register next => Nat.pair 1 (Nat.pair register next)
  | .decrement register positive zero =>
      Nat.pair 2 (Nat.pair register (Nat.pair positive zero))
  | .loadLiteral value register next =>
      Nat.pair 11 (Nat.pair value (Nat.pair register next))
  | .indirectRead addressRegister outputRegister next =>
      Nat.pair 3 (Nat.pair addressRegister (Nat.pair outputRegister next))
  | .indirectWrite sourceRegister addressRegister next =>
      Nat.pair 4 (Nat.pair sourceRegister (Nat.pair addressRegister next))
  | .pair leftRegister rightRegister outputRegister next =>
      Nat.pair 12 (Nat.pair leftRegister
        (Nat.pair rightRegister (Nat.pair outputRegister next)))
  | .oracleQuery lengthRegister inputRegister outputRegister next =>
      Nat.pair 5 (Nat.pair lengthRegister
        (Nat.pair inputRegister (Nat.pair outputRegister next)))
  | .sampleQuery indexRegister pointOutputRegister labelOutputRegister next =>
      Nat.pair 6 (Nat.pair indexRegister
        (Nat.pair pointOutputRegister (Nat.pair labelOutputRegister next)))
  | .sampleQueryIndirect indexRegister pointOutputAddressRegister labelOutputRegister next =>
      Nat.pair 7 (Nat.pair indexRegister
        (Nat.pair pointOutputAddressRegister (Nat.pair labelOutputRegister next)))
  | .pairLeft sourceRegister outputRegister next =>
      Nat.pair 8 (Nat.pair sourceRegister (Nat.pair outputRegister next))
  | .pairRight sourceRegister outputRegister next =>
      Nat.pair 9 (Nat.pair sourceRegister (Nat.pair outputRegister next))
  | .branchEqual leftRegister rightRegister equalNext unequalNext =>
      Nat.pair 10 (Nat.pair leftRegister
        (Nat.pair rightRegister (Nat.pair equalNext unequalNext)))

def machine_word_list_code : List ℕ → ℕ
  | [] => 0
  | word :: words => Nat.pair (word + 1) (machine_word_list_code words)

def machine_program_code (program : machine_program) : ℕ :=
  machine_word_list_code (program.map register_machine_instruction_code)

structure machine_configuration where
  programCounter : ℕ
  registers : ℕ → ℕ

def machine_initial_configuration (input : ℕ) : machine_configuration where
  programCounter := 0
  registers := fun register => if register = 1 then input else 0

def machine_step (program : machine_program)
    (configuration : machine_configuration) : Option machine_configuration :=
  match program[configuration.programCounter]? with
  | none => none
  | some .halt => none
  | some (.increment register next) =>
      some {
        programCounter := next
        registers := Function.update configuration.registers register
          (configuration.registers register + 1) }
  | some (.decrement register positive zero) =>
      if configuration.registers register = 0 then
        some { programCounter := zero, registers := configuration.registers }
      else
        some {
          programCounter := positive
          registers := Function.update configuration.registers register
            (configuration.registers register - 1) }
  | some (.loadLiteral value register next) =>
      some {
        programCounter := next
        registers := Function.update configuration.registers register value }
  | some (.indirectRead addressRegister outputRegister next) =>
      some {
        programCounter := next
        registers := Function.update configuration.registers outputRegister
          (configuration.registers (configuration.registers addressRegister)) }
  | some (.indirectWrite sourceRegister addressRegister next) =>
      some {
        programCounter := next
        registers := Function.update configuration.registers
          (configuration.registers addressRegister)
          (configuration.registers sourceRegister) }
  | some (.pair leftRegister rightRegister outputRegister next) =>
      some {
        programCounter := next
        registers := Function.update configuration.registers outputRegister
          (Nat.pair (configuration.registers leftRegister)
            (configuration.registers rightRegister)) }
  | some (.pairLeft sourceRegister outputRegister next) =>
      some {
        programCounter := next
        registers := Function.update configuration.registers outputRegister
          (Nat.unpair (configuration.registers sourceRegister)).1 }
  | some (.pairRight sourceRegister outputRegister next) =>
      some {
        programCounter := next
        registers := Function.update configuration.registers outputRegister
          (Nat.unpair (configuration.registers sourceRegister)).2 }
  | some (.branchEqual leftRegister rightRegister equalNext unequalNext) =>
      some {
        programCounter := if configuration.registers leftRegister =
            configuration.registers rightRegister then equalNext else unequalNext
        registers := configuration.registers }
  | some (.oracleQuery _ _ _ _) => none
  | some (.sampleQuery _ _ _ _) => none
  | some (.sampleQueryIndirect _ _ _ _) => none

def machine_reaches_within (program : machine_program) :
    ℕ → machine_configuration → machine_configuration → Prop
  | 0, initial, final => initial = final
  | steps + 1, initial, final =>
      initial = final ∨ ∃ next,
        machine_step program initial = some next ∧
          machine_reaches_within program steps next final

def machine_computes_in_time (program : machine_program)
    (input output steps : ℕ) : Prop :=
  ∃ final,
    machine_reaches_within program steps (machine_initial_configuration input) final ∧
      machine_step program final = none ∧ final.registers 0 = output

def oracle_accepts_code (oracle : language_family) (length queryCode : ℕ) : Prop :=
  ∃ query : binary_string length,
    finite_type_code query = queryCode ∧ oracle length query

def oracle_machine_step (oracle : language_family) (program : machine_program)
    (initial final : machine_configuration) : Prop :=
  match program[initial.programCounter]? with
  | some (.oracleQuery lengthRegister inputRegister outputRegister next) =>
      (oracle_accepts_code oracle (initial.registers lengthRegister)
          (initial.registers inputRegister) ∧
        final = {
          programCounter := next
          registers := Function.update initial.registers outputRegister 1 }) ∨
      (¬ oracle_accepts_code oracle (initial.registers lengthRegister)
          (initial.registers inputRegister) ∧
        final = {
          programCounter := next
          registers := Function.update initial.registers outputRegister 0 })
  | _ => machine_step program initial = some final

def oracle_machine_reaches_within (oracle : language_family) (program : machine_program) :
    ℕ → machine_configuration → machine_configuration → Prop
  | 0, initial, final => initial = final
  | steps + 1, initial, final =>
      initial = final ∨ ∃ next,
        oracle_machine_step oracle program initial next ∧
          oracle_machine_reaches_within oracle program steps next final

def oracle_machine_computes_in_time (oracle : language_family) (program : machine_program)
    (input output steps : ℕ) : Prop :=
  ∃ final,
    oracle_machine_reaches_within oracle program steps
      (machine_initial_configuration input) final ∧
      (¬ ∃ next, oracle_machine_step oracle program final next) ∧
      final.registers 0 = output

structure quantitative_verifier where
  program : machine_program
  accepts : ∀ {n k : ℕ}, binary_string n → binary_string k → Bool
  cost : ℕ → ℕ → ℕ
  runsWithinCost : ∀ {n k : ℕ} (x : binary_string n) (w : binary_string k),
    machine_computes_in_time program
      (Nat.pair n (Nat.pair k (Nat.pair (finite_type_code x) (finite_type_code w))))
      (Encodable.encode (accepts x w)) (cost n k)

def verifier_decides_with_bounds (L : language_family) (V : quantitative_verifier)
    (t p : ℕ → ℕ) : Prop :=
  (∀ n x, L n x ↔ ∃ w : binary_string (p n), V.accepts x w = true) ∧
    ∃ K : ℕ, 0 < K ∧ ∀ n, V.cost n (p n) ≤ K * (t n + 1)

def nondeterministic_time_class (t p : ℕ → ℕ) : Set language_family :=
  {L | ∃ V : quantitative_verifier, verifier_decides_with_bounds L V t p}

structure quantitative_randomized_algorithm where
  program : machine_program
  randomBits : ℕ → ℕ
  accepts : ∀ {n : ℕ}, binary_string n → binary_string (randomBits n) → Bool
  cost : ℕ → ℕ
  runsWithinCost : ∀ {n : ℕ} (x : binary_string n)
      (randomness : binary_string (randomBits n)),
    machine_computes_in_time program
      (Nat.pair n (Nat.pair (finite_type_code x) (finite_type_code randomness)))
      (Encodable.encode (accepts x randomness)) (cost n)

noncomputable def randomized_acceptance_probability
    (A : quantitative_randomized_algorithm) {n : ℕ} (x : binary_string n) : ℝ :=
  ((Finset.univ.filter (fun r : binary_string (A.randomBits n) => A.accepts x r = true)).card : ℝ) /
    (2 : ℝ) ^ A.randomBits n

def randomized_time_class (t : ℕ → ℕ) : Set language_family :=
  {L | ∃ A : quantitative_randomized_algorithm,
    (∀ n x, L n x → (2 : ℝ) / 3 ≤ randomized_acceptance_probability A x) ∧
    (∀ n x, ¬ L n x → randomized_acceptance_probability A x = 0) ∧
    (∀ n, A.randomBits n ≤ t n) ∧
    ∀ n, A.cost n ≤ t n}

structure quantitative_natural_algorithm where
  program : machine_program
  output : ℕ → ℕ
  cost : ℕ → ℕ
  runsWithinCost : ∀ n,
    machine_computes_in_time program n (output n) (cost n)

def time_constructible (p : ℕ → ℕ) : Prop :=
  ∃ (A : quantitative_natural_algorithm) (K : ℕ),
    0 < K ∧ (∀ n, A.output n = p n) ∧ ∀ n, A.cost n ≤ K * (p n + 1)

def growth_function (p : ℕ → ℕ) : Prop := Monotone p ∧ ∀ n, n ≤ p n

def polynomially_bounded (f p : ℕ → ℕ) : Prop :=
  ∃ K d : ℕ, ∀ n, f n ≤ K * (p n + 1) ^ d

def polynomial_padding_stable (q p : ℕ → ℕ) : Prop :=
  ∀ N : ℕ → ℕ, polynomially_bounded N p →
    ∃ d : ℕ, ∀ n, q (N n) ≤ q n * (p n + 1) ^ d

def p_log_p (p : ℕ → ℕ) (n : ℕ) : ℕ := p n * (Nat.log 2 (p n + 1) + 1)

def tradeoff_runtime (p m t : ℕ → ℕ) (K d n : ℕ) : ℕ :=
  2 ^ (K * m n) * t n * (Nat.log 2 (t n + 1) + 1) * (p n + 1) ^ d

def few_sample_randomized_containment (p m t : ℕ → ℕ) : Prop :=
  ∀ L ∈ nondeterministic_time_class p p,
    ∃ K d : ℕ, L ∈ randomized_time_class (tradeoff_runtime p m t K d)

structure efficient_binary_code where
  expansion : ℕ
  one_lt_expansion : 1 < expansion
  epsilonStar : ℝ
  epsilonStar_pos : 0 < epsilonStar
  epsilonStar_lt_one : epsilonStar < 1
  encode : ∀ k : ℕ, binary_string k → binary_string (expansion * k)
  decode : ∀ k : ℕ, binary_string (expansion * k) → binary_string k
  codeword_nonzero : ∀ k (hk : 0 < k) (x : binary_string k),
    ∃ i : Fin (expansion * k), encode k x i = true
  encoderProgram : machine_program
  decoderProgram : machine_program
  coordinateProgram : machine_program
  encodingCost : ℕ → ℕ
  decodingCost : ℕ → ℕ
  coordinateCost : ℕ → ℕ
  encodingCost_poly : polynomially_bounded encodingCost id
  decodingCost_poly : polynomially_bounded decodingCost id
  coordinateCost_poly : polynomially_bounded coordinateCost id
  encoderRunsWithinCost : ∀ k (x : binary_string k),
    machine_computes_in_time encoderProgram (Encodable.encode (k, x))
      (Encodable.encode (encode k x)) (encodingCost k)
  decoderRunsWithinCost : ∀ k (y : binary_string (expansion * k)),
    machine_computes_in_time decoderProgram (Encodable.encode (k, y))
      (Encodable.encode (decode k y)) (decodingCost k)
  coordinateRunsWithinCost : ∀ k (x : binary_string k)
      (i : Fin (expansion * k)),
    machine_computes_in_time coordinateProgram (Encodable.encode (k, x, i))
      (Encodable.encode (encode k x i)) (coordinateCost k)
  corrects : ∀ k (x : binary_string k) (y : binary_string (expansion * k)),
    (hammingDist y (encode k x) : ℝ) ≤ epsilonStar * (expansion * k) → decode k y = x

inductive indexed_decision_tree (n k : ℕ) where
  | leaf : Bool → indexed_decision_tree n k
  | bitNode : Fin n → indexed_decision_tree n k → indexed_decision_tree n k →
      indexed_decision_tree n k
  | indexNode : (Fin k → indexed_decision_tree n k) → indexed_decision_tree n k

def indexed_decision_tree_eval {n k : ℕ} :
    indexed_decision_tree n k → (binary_string n × Fin k) → Bool
  | .leaf b, _ => b
  | .bitNode i left right, x =>
      if x.1 i then indexed_decision_tree_eval right x else indexed_decision_tree_eval left x
  | .indexNode branch, x => indexed_decision_tree_eval (branch x.2) x

def indexed_decision_tree_size {n k : ℕ} : indexed_decision_tree n k → ℕ
  | .leaf _ => 1
  | .bitNode _ left right =>
      1 + indexed_decision_tree_size left + indexed_decision_tree_size right
  | .indexNode branch => 1 + ∑ i, indexed_decision_tree_size (branch i)

noncomputable def indexed_decision_tree_code {n k : ℕ}
    (tree : indexed_decision_tree n k) : ℕ :=
  let rec serialize : indexed_decision_tree n k → List Bool
    | .leaf false => [false, false]
    | .leaf true => [false, true]
    | .bitNode i left right =>
        [true, false] ++ List.replicate i.1 true ++ [false] ++
          serialize left ++ serialize right
    | .indexNode branch =>
        [true, true] ++ List.flatten (List.ofFn (fun i => serialize (branch i)))
  (serialize tree).foldr (fun bit code => 2 * code + if bit then 1 else 0) 1

inductive indexed_boolean_circuit (n k : ℕ) where
  | bitInput : Fin n → indexed_boolean_circuit n k
  | indexEq : Fin k → indexed_boolean_circuit n k
  | const : Bool → indexed_boolean_circuit n k
  | neg : indexed_boolean_circuit n k → indexed_boolean_circuit n k
  | conj : indexed_boolean_circuit n k → indexed_boolean_circuit n k →
      indexed_boolean_circuit n k
  | disj : indexed_boolean_circuit n k → indexed_boolean_circuit n k →
      indexed_boolean_circuit n k

def indexed_boolean_circuit_eval {n k : ℕ} :
    indexed_boolean_circuit n k → (binary_string n × Fin k) → Bool
  | .bitInput i, x => x.1 i
  | .indexEq i, x => decide (x.2 = i)
  | .const b, _ => b
  | .neg C, x => !(indexed_boolean_circuit_eval C x)
  | .conj C D, x => indexed_boolean_circuit_eval C x && indexed_boolean_circuit_eval D x
  | .disj C D, x => indexed_boolean_circuit_eval C x || indexed_boolean_circuit_eval D x

def indexed_boolean_circuit_size {n k : ℕ} : indexed_boolean_circuit n k → ℕ
  | .bitInput _ => 1
  | .indexEq _ => 1
  | .const _ => 1
  | .neg C => 1 + indexed_boolean_circuit_size C
  | .conj C D => 1 + indexed_boolean_circuit_size C + indexed_boolean_circuit_size D
  | .disj C D => 1 + indexed_boolean_circuit_size C + indexed_boolean_circuit_size D

structure finite_distribution (α : Type*) [Fintype α] where
  mass : α → ℝ
  mass_nonneg : ∀ x, 0 ≤ mass x
  total_mass : ∑ x, mass x = 1

noncomputable def finite_prediction_error {α : Type*} [Fintype α]
    (D : finite_distribution α) (f h : α → Bool) : ℝ :=
  ∑ x, if f x = h x then 0 else D.mass x

def finite_sample_mass {α : Type*} [Fintype α] {m : ℕ}
    (D : finite_distribution α) (sample : Fin m → α) : ℝ :=
  ∏ i, D.mass (sample i)

abbrev finite_labeled_sample (α : Type*) (m : ℕ) := Fin m → (α × Bool)

def sample_machine_step {α : Type*} [Encodable α] {m : ℕ}
    (sample : finite_labeled_sample α m) (program : machine_program)
    (initial final : machine_configuration) : Prop :=
  match program[initial.programCounter]? with
  | some (.sampleQuery indexRegister pointOutputRegister labelOutputRegister next) =>
      if h : initial.registers indexRegister < m then
        final = {
          programCounter := next
          registers := Function.update
            (Function.update initial.registers pointOutputRegister
              (finite_type_code (sample ⟨initial.registers indexRegister, h⟩).1))
            labelOutputRegister
            (finite_type_code (sample ⟨initial.registers indexRegister, h⟩).2) }
      else
        final = {
          programCounter := next
          registers := Function.update
            (Function.update initial.registers pointOutputRegister 0)
            labelOutputRegister 0 }
  | some (.sampleQueryIndirect indexRegister pointOutputAddressRegister
      labelOutputRegister next) =>
      if h : initial.registers indexRegister < m then
        final = {
          programCounter := next
          registers := Function.update
            (Function.update initial.registers
              (initial.registers pointOutputAddressRegister)
              (finite_type_code (sample ⟨initial.registers indexRegister, h⟩).1))
            labelOutputRegister
            (finite_type_code (sample ⟨initial.registers indexRegister, h⟩).2) }
      else
        final = {
          programCounter := next
          registers := Function.update
            (Function.update initial.registers
              (initial.registers pointOutputAddressRegister) 0)
            labelOutputRegister 0 }
  | _ => machine_step program initial = some final

def sample_machine_reaches_within {α : Type*} [Encodable α] {m : ℕ}
    (sample : finite_labeled_sample α m) (program : machine_program) :
    ℕ → ℕ → machine_configuration → machine_configuration → Prop
  | 0, _, initial, final => initial = final
  | steps + 1, sampleQueries, initial, final =>
      initial = final ∨ ∃ next,
        sample_machine_step sample program initial next ∧
          match program[initial.programCounter]? with
          | some (.sampleQuery _ _ _ _) | some (.sampleQueryIndirect _ _ _ _) =>
              ∃ remainingQueries, sampleQueries = remainingQueries + 1 ∧
                sample_machine_reaches_within sample program steps remainingQueries next final
          | _ =>
              sample_machine_reaches_within sample program steps sampleQueries next final

def sample_machine_computes_in_time {α : Type*} [Encodable α] {m : ℕ}
    (sample : finite_labeled_sample α m) (program : machine_program)
    (input output : ℕ) (retainedWords : List ℕ) (sampleQueries steps : ℕ) : Prop :=
  ∃ final,
    sample_machine_reaches_within sample program steps sampleQueries
      (machine_initial_configuration input) final ∧
      (¬ ∃ next, sample_machine_step sample program final next) ∧
      final.registers 0 = output ∧
      ∀ i : Fin retainedWords.length, final.registers (i.1 + 1) = retainedWords.get i

def machine_word_bit_length (word : ℕ) : ℕ := Nat.log 2 (word + 1) + 1

def machine_word_list_bit_length (words : List ℕ) : ℕ :=
  words.length + (words.map machine_word_bit_length).sum

def deterministically_labeled_sample {α : Type*} {m : ℕ} (f : α → Bool)
    (sample : Fin m → α) : finite_labeled_sample α m :=
  fun i => (sample i, f (sample i))

structure computable_boolean_hypothesis (α : Type*) [Encodable α] where
  program : machine_program
  retainedWords : List ℕ
  predict : α → Bool
  runtime : α → ℕ
  computes : ∀ x, sample_machine_computes_in_time
    (fun i : Fin retainedWords.length => (retainedWords.get i, false)) program
    (Encodable.encode x) (Encodable.encode (predict x)) []
    retainedWords.length (runtime x)

structure finite_learner (α : Type*) [Encodable α] (m : ℕ) where
  randomBits : ℕ
  run : finite_labeled_sample α m → binary_string randomBits →
    computable_boolean_hypothesis α

noncomputable def pac_failure_mass {α : Type*} [Fintype α] [Encodable α] {m : ℕ}
    (D : finite_distribution α) (f : α → Bool) (A : finite_learner α m) (ε : ℝ) : ℝ :=
  ∑ sample : Fin m → α,
    ∑ randomness : binary_string A.randomBits,
      if ε < finite_prediction_error D f
          ((A.run (deterministically_labeled_sample f sample) randomness).predict)
      then finite_sample_mass D sample / (2 : ℝ) ^ A.randomBits else 0

def pac_learns_concept_class {α : Type*} [Fintype α] [Encodable α] {m : ℕ}
    (C : boolean_concept_class α)
    (A : finite_learner α m) (ε : ℝ) : Prop :=
  ∀ (f : α → Bool), f ∈ C → ∀ D : finite_distribution α,
    pac_failure_mass D f A ε ≤ (1 : ℝ) / 3

abbrev certificate_point (p : ℕ → ℕ) (code : efficient_binary_code) (n : ℕ) :=
  binary_string n × Fin (code.expansion * p n)

abbrev indexed_concept_family (p : ℕ → ℕ) (code : efficient_binary_code) :=
  ∀ n : ℕ, boolean_concept_class (certificate_point p code n)

abbrev accuracy_parameter := Set.Ioi (0 : ℝ)

structure uniform_pac_learner (p : ℕ → ℕ) (code : efficient_binary_code)
    (C : indexed_concept_family p code) where
  program : machine_program
  sampleProcessingFactor : ℕ
  sampleCount : ℕ → accuracy_parameter → ℕ
  run : ∀ n ε, finite_learner (certificate_point p code n) (sampleCount n ε)
  runtime : ℕ → accuracy_parameter → ℕ
  runsWithinRuntime : ∀ n ε
      (sample : finite_labeled_sample (certificate_point p code n) (sampleCount n ε))
      (randomness : binary_string (run n ε).randomBits),
    sample_machine_computes_in_time sample program
      (Nat.pair n (Nat.pair (sampleCount n ε) (finite_type_code randomness)))
      (machine_program_code ((run n ε).run sample randomness).program)
      ((run n ε).run sample randomness).retainedWords
      (sampleCount n ε)
      (sampleProcessingFactor * sampleCount n ε + runtime n ε)
  hypothesisRunsWithinRuntime : ∀ n ε
      (sample : finite_labeled_sample (certificate_point p code n) (sampleCount n ε))
      (randomness : binary_string (run n ε).randomBits)
      (x : certificate_point p code n),
    ((run n ε).run sample randomness).runtime x ≤ runtime n ε
  learns : ∀ n ε, pac_learns_concept_class (C n) (run n ε) ε.1

def inverse_accuracy_sample_bound {p : ℕ → ℕ} {code : efficient_binary_code}
    {C : indexed_concept_family p code} (A : uniform_pac_learner p code C) : Prop :=
  ∃ K : ℕ, ∀ n ε, A.sampleCount n ε ≤ Nat.ceil ((K : ℝ) / ε.1)

def exponential_p_runtime_bound {p : ℕ → ℕ} {code : efficient_binary_code}
    {C : indexed_concept_family p code} (A : uniform_pac_learner p code C) : Prop :=
  ∃ B K : ℕ, ∀ n ε, A.runtime n ε ≤ B * 2 ^ (K * p n)

def linear_p_over_accuracy_bound {p : ℕ → ℕ} {code : efficient_binary_code}
    {C : indexed_concept_family p code} (A : uniform_pac_learner p code C) : Prop :=
  ∃ B K : ℕ, ∀ n ε,
    A.sampleCount n ε ≤ B + Nat.ceil ((K : ℝ) * p n / ε.1) ∧
    A.runtime n ε ≤ B + Nat.ceil ((K : ℝ) * p n / ε.1)

def family_has_small_decision_trees {p : ℕ → ℕ} {code : efficient_binary_code}
    (C : indexed_concept_family p code) : Prop :=
  ∃ K : ℕ, ∀ n (f : certificate_point p code n → Bool), f ∈ C n →
    ∃ T : indexed_decision_tree n (code.expansion * p n),
      indexed_decision_tree_eval T = f ∧ indexed_decision_tree_size T ≤ K * (p n + 1)

def family_has_small_circuits {p : ℕ → ℕ} {code : efficient_binary_code}
    (C : indexed_concept_family p code) : Prop :=
  ∃ K : ℕ, ∀ n (f : certificate_point p code n → Bool), f ∈ C n →
    ∃ circuit : indexed_boolean_circuit n (code.expansion * p n),
      indexed_boolean_circuit_eval circuit = f ∧
        indexed_boolean_circuit_size circuit ≤ K * (p n + 1)

structure oracle_enumerator (p : ℕ → ℕ) (code : efficient_binary_code)
    (C : indexed_concept_family p code) where
  oracle : language_family
  oracle_mem : oracle ∈ nondeterministic_time_class (p_log_p p) p
  seedLength : ℕ → ℕ
  seedLength_poly : polynomially_bounded seedLength p
  enumerate : ∀ n, binary_string (seedLength n) →
    indexed_decision_tree n (code.expansion * p n)
  program : machine_program
  runtime : ℕ → ℕ
  runtime_poly : polynomially_bounded runtime p
  runsWithinRuntime : ∀ n (seed : binary_string (seedLength n)),
    oracle_machine_computes_in_time oracle program (Encodable.encode (n, seed))
      (indexed_decision_tree_code (enumerate n seed)) (runtime n)
  sound : ∀ n seed, indexed_decision_tree_eval (enumerate n seed) ∈ C n
  complete : ∀ n (f : certificate_point p code n → Bool), f ∈ C n →
    ∃ seed, indexed_decision_tree_eval (enumerate n seed) = f

def ntime_enumerable {p : ℕ → ℕ} {code : efficient_binary_code}
    (C : indexed_concept_family p code) : Prop :=
  Nonempty (oracle_enumerator p code C)

def am_protocol_runtime (p t : ℕ → ℕ) (K d n : ℕ) : ℕ :=
  K * t n * (Nat.log 2 (t n + 1) + 1) * (p n + 1) ^ d

def am_simulation_runtime (m q : ℕ → ℕ) (n : ℕ) : ℕ :=
  2 ^ (m n + 1) * (q n + m n + n + 1)

structure fixed_accuracy_pac_learner (p : ℕ → ℕ) (code : efficient_binary_code)
    (C : indexed_concept_family p code) (m t : ℕ → ℕ) (ε : ℝ) where
  program : machine_program
  sampleCountProgram : machine_program
  run : ∀ n, finite_learner (certificate_point p code n) (m n)
  runtime : ℕ → ℕ
  runtime_le : ∀ n, runtime n ≤ t n
  sampleCount_le_runtime : ∀ n, m n ≤ runtime n
  sampleCountRunsWithinRuntime : ∀ n,
    machine_computes_in_time sampleCountProgram n (m n) (runtime n)
  randomBits_le : ∀ n, (run n).randomBits ≤ runtime n
  runsWithinRuntime : ∀ n
      (sample : finite_labeled_sample (certificate_point p code n) (m n))
      (randomness : binary_string (run n).randomBits),
    sample_machine_computes_in_time sample program
      (Nat.pair n (Nat.pair (m n) (finite_type_code randomness)))
      (machine_program_code ((run n).run sample randomness).program)
      ((run n).run sample randomness).retainedWords (m n) (runtime n)
  hypothesisRunsWithinRuntime : ∀ n
      (sample : finite_labeled_sample (certificate_point p code n) (m n))
      (randomness : binary_string (run n).randomBits)
      (x : certificate_point p code n),
    ((run n).run sample randomness).runtime x ≤ runtime n
  returnedProgramSize_le : ∀ n
      (sample : finite_labeled_sample (certificate_point p code n) (m n))
      (randomness : binary_string (run n).randomBits),
    machine_word_bit_length
      (machine_program_code ((run n).run sample randomness).program) ≤ runtime n
  retainedWordsSize_le : ∀ n
      (sample : finite_labeled_sample (certificate_point p code n) (m n))
      (randomness : binary_string (run n).randomBits),
    machine_word_list_bit_length
      ((run n).run sample randomness).retainedWords ≤ runtime n
  learns : ∀ n, pac_learns_concept_class (C n) (run n) ε

def certificate_family_item_one {p : ℕ → ℕ} {code : efficient_binary_code}
    (C : indexed_concept_family p code) : Prop :=
  (∀ n, 0 < n → vc_dimension (C n) = 1) ∧
  ntime_enumerable C ∧
  ∃ A : uniform_pac_learner p code C,
    inverse_accuracy_sample_bound A ∧ exponential_p_runtime_bound A

def certificate_family_few_sample_property {p : ℕ → ℕ} {code : efficient_binary_code}
    (C : indexed_concept_family p code) : Prop :=
  ∀ m t : ℕ → ℕ,
    Nonempty (fixed_accuracy_pac_learner p code C m t code.epsilonStar) →
      (∀ K d : ℕ, polynomial_padding_stable
        (am_simulation_runtime (fun n => 2 * m n) (am_protocol_runtime p t K d)) p) →
      few_sample_randomized_containment p m t

def certificate_family_many_sample_property {p : ℕ → ℕ} {code : efficient_binary_code}
    (C : indexed_concept_family p code) : Prop :=
  ∃ A : uniform_pac_learner p code C, linear_p_over_accuracy_bound A

structure computational_statistical_tradeoff_properties (p : ℕ → ℕ)
    (code : efficient_binary_code) (C : indexed_concept_family p code) : Prop where
  itemOne : certificate_family_item_one C
  fewSamples : certificate_family_few_sample_property C
  manySamples : certificate_family_many_sample_property C
  decisionTrees : family_has_small_decision_trees C
  circuits : family_has_small_circuits C

theorem computational_statistical_tradeoffs_from_np_hardness
    (p : ℕ → ℕ) (hp : growth_function p) (htc : time_constructible p)
    (hcode : Nonempty efficient_binary_code) :
    ∃ code : efficient_binary_code,
      ∃ C : indexed_concept_family p code,
        computational_statistical_tradeoff_properties p code C := by sorry

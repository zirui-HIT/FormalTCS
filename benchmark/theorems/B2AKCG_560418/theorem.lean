import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.ENNReal.Basic

set_option linter.all false
set_option maxHeartbeats 500000

noncomputable def k_center_covering_radius {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C : Finset V) : ℕ∞ :=
  Finset.univ.sup fun v : V => C.inf fun c => G.edist v c

noncomputable def k_center_radius {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) : ℕ∞ :=
  (Finset.univ.filter fun C : Finset V => C.card = k).inf
    fun C => k_center_covering_radius G C

def k_center_mixed_approximation {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) (C : Finset V) : Prop :=
  C.card = k ∧
    k_center_radius G k ≤ k_center_covering_radius G C ∧
    (((2 * k - 1 : ℕ) : ℕ∞) * k_center_covering_radius G C) ≤
      (((4 * k - 3 : ℕ) : ℕ∞) * k_center_radius G k +
        ((2 * k - 2 : ℕ) : ℕ∞))

structure word_ram_graph (n : ℕ) where
  graph : SimpleGraph (Fin n)
  adjacency : Fin n → Fin n → Bool
  adjacency_correct :
    ∀ u v, adjacency u v = true ↔ graph.Adj u v

inductive word_ram_instruction where
  | loadConstant (destination value : ℕ)
  | copy (destination source : ℕ)
  | add (destination left right : ℕ)
  | subtract (destination left right : ℕ)
  | readInput (destination addressRegister : ℕ)
  | readMemory (destination addressRegister : ℕ)
  | writeMemory (addressRegister source : ℕ)
  | readRandomBit (destination : ℕ)
  | jump (target : ℕ)
  | branchZero (test target : ℕ)
  | halt (outputStart outputLength : ℕ)

structure word_ram_program where
  registerCount : ℕ
  code : List word_ram_instruction

def word_ram_memory_write (memory : List ℕ) (address value : ℕ) : List ℕ :=
  (memory ++ List.replicate (address + 1 - memory.length) 0).set address value

structure word_ram_configuration where
  programCounter : ℕ
  registers : List ℕ
  memory : List ℕ
  randomHead : ℕ

def word_ram_next_configuration
    (program : word_ram_program) (input : List ℕ) (randomTape : List Bool)
    (state : word_ram_configuration) : Option word_ram_configuration :=
  match program.code[state.programCounter]? with
  | some (.loadConstant destination value) =>
      some
        { programCounter := state.programCounter + 1
          registers := state.registers.set destination value
          memory := state.memory
          randomHead := state.randomHead }
  | some (.copy destination source) =>
      some
        { programCounter := state.programCounter + 1
          registers := state.registers.set destination
            (state.registers.getD source 0)
          memory := state.memory
          randomHead := state.randomHead }
  | some (.add destination left right) =>
      some
        { programCounter := state.programCounter + 1
          registers := state.registers.set destination
            (state.registers.getD left 0 + state.registers.getD right 0)
          memory := state.memory
          randomHead := state.randomHead }
  | some (.subtract destination left right) =>
      some
        { programCounter := state.programCounter + 1
          registers := state.registers.set destination
            (state.registers.getD left 0 - state.registers.getD right 0)
          memory := state.memory
          randomHead := state.randomHead }
  | some (.readInput destination addressRegister) =>
      some
        { programCounter := state.programCounter + 1
          registers := state.registers.set destination
            (input.getD (state.registers.getD addressRegister 0) 0)
          memory := state.memory
          randomHead := state.randomHead }
  | some (.readMemory destination addressRegister) =>
      some
        { programCounter := state.programCounter + 1
          registers := state.registers.set destination
            (state.memory.getD (state.registers.getD addressRegister 0) 0)
          memory := state.memory
          randomHead := state.randomHead }
  | some (.writeMemory addressRegister source) =>
      some
        { programCounter := state.programCounter + 1
          registers := state.registers
          memory := word_ram_memory_write state.memory
            (state.registers.getD addressRegister 0)
            (state.registers.getD source 0)
          randomHead := state.randomHead }
  | some (.readRandomBit destination) =>
      some
        { programCounter := state.programCounter + 1
          registers := state.registers.set destination
            (if randomTape.getD state.randomHead false then 1 else 0)
          memory := state.memory
          randomHead := state.randomHead + 1 }
  | some (.jump target) =>
      some
        { programCounter := target
          registers := state.registers
          memory := state.memory
          randomHead := state.randomHead }
  | some (.branchZero test target) =>
      some
        { programCounter :=
            if state.registers.getD test 0 = 0 then target
            else state.programCounter + 1
          registers := state.registers
          memory := state.memory
          randomHead := state.randomHead }
  | some (.halt _ _) => none
  | none => none

def word_ram_halt_output
    (program : word_ram_program) (state : word_ram_configuration) :
    Option (List ℕ) :=
  match program.code[state.programCounter]? with
  | some (.halt outputStart outputLength) =>
      some ((List.range outputLength).map fun i =>
        state.registers.getD (outputStart + i) 0)
  | _ => none

def word_ram_instruction_words : word_ram_instruction → List ℕ
  | .loadConstant destination value => [destination, value]
  | .copy destination source => [destination, source]
  | .add destination left right => [destination, left, right]
  | .subtract destination left right => [destination, left, right]
  | .readInput destination addressRegister => [destination, addressRegister]
  | .readMemory destination addressRegister => [destination, addressRegister]
  | .writeMemory addressRegister source => [addressRegister, source]
  | .readRandomBit destination => [destination]
  | .jump target => [target]
  | .branchZero test target => [test, target]
  | .halt outputStart outputLength => [outputStart, outputLength]

def word_ram_bit_width (words : List ℕ) : ℕ :=
  (words.map Nat.size).foldl Nat.max 0

structure randomized_word_ram_computation where
  program : word_ram_program
  input : List ℕ
  randomTape : List Bool
  initialState : word_ram_configuration
  finalState : word_ram_configuration
  trace : List word_ram_configuration
  output : List ℕ
  initialState_eq :
    initialState =
      { programCounter := 0
        registers := List.replicate program.registerCount 0
        memory := []
        randomHead := 0 }
  trace_starts : trace.head? = some initialState
  trace_ends : trace.getLast? = some finalState
  trace_valid :
    List.IsChain
      (fun current next =>
        word_ram_next_configuration program input randomTape current = some next)
      trace
  halted : word_ram_halt_output program finalState = some output
  operationCount : ℕ
  operationCount_eq : operationCount = trace.length - 1
  wordBits : ℕ
  wordBits_eq :
    wordBits = word_ram_bit_width
      (program.code.flatMap word_ram_instruction_words ++ input ++
        trace.flatMap fun state =>
          [state.programCounter, state.randomHead] ++ state.registers ++ state.memory)

def word_ram_random_tape (bits : ℕ) (seed : Fin (2 ^ bits)) : List Bool :=
  List.ofFn fun i : Fin bits => Nat.testBit seed.val i.val

def word_ram_graph_input {n : ℕ}
    (G : word_ram_graph n) (k : ℕ) (radius : Option ℕ) : List ℕ :=
  n :: k :: radius.getD 0 ::
    (List.ofFn fun u : Fin n =>
      List.ofFn fun v : Fin n =>
        if G.adjacency u v then 1 else 0).flatten

noncomputable def word_ram_decode_centers (n : ℕ) (output : List ℕ) :
    Finset (Fin n) :=
  (output.filterMap fun v =>
    if hv : v < n then some (⟨v, hv⟩ : Fin n) else none).toFinset

structure randomized_k_center_algorithm where
  program : word_ram_program
  randomBits : ℕ → ℕ → ℕ → ℕ
  run : {n : ℕ} → (G : word_ram_graph n) → (k : ℕ) →
    Fin (2 ^ randomBits k n G.graph.edgeSet.ncard) →
      randomized_word_ram_computation
  run_program :
    ∀ {n : ℕ} (G : word_ram_graph n) (k : ℕ)
      (seed : Fin (2 ^ randomBits k n G.graph.edgeSet.ncard)),
      (run G k seed).program = program
  run_input :
    ∀ {n : ℕ} (G : word_ram_graph n) (k : ℕ)
      (seed : Fin (2 ^ randomBits k n G.graph.edgeSet.ncard)),
      (run G k seed).input = word_ram_graph_input G k none
  run_random_tape :
    ∀ {n : ℕ} (G : word_ram_graph n) (k : ℕ)
      (seed : Fin (2 ^ randomBits k n G.graph.edgeSet.ncard)),
      (run G k seed).randomTape =
        word_ram_random_tape (randomBits k n G.graph.edgeSet.ncard) seed
  steps : ℕ → ℕ → ℕ → ℕ
  wordBits : ℕ → ℕ → ℕ
  operationCount_le_steps :
    ∀ {n : ℕ} (G : word_ram_graph n) (k : ℕ)
      (seed : Fin (2 ^ randomBits k n G.graph.edgeSet.ncard)),
      (run G k seed).operationCount ≤ steps k n G.graph.edgeSet.ncard
  wordBits_le_wordBits :
    ∀ {n : ℕ} (G : word_ram_graph n) (k : ℕ)
      (seed : Fin (2 ^ randomBits k n G.graph.edgeSet.ncard)),
      (run G k seed).wordBits ≤ wordBits k n

def target_soft_o_running_time (steps : ℕ → ℕ → ℕ → ℕ) (k : ℕ) : Prop :=
  ∃ d : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ n : ℕ in Filter.atTop, ∀ m : ℕ, m ≤ n.choose 2 →
      (steps k n m : ℝ) ≤
        C * (((m : ℝ) * (n : ℝ) +
          Real.rpow (n : ℝ) ((k : ℝ) / 2 + 1)) *
        Real.log ((n : ℝ) + 2) ^ d)

def logarithmic_word_bound (wordBits : ℕ → ℕ) : Prop :=
  Asymptotics.IsBigO Filter.atTop
    (fun n : ℕ => (wordBits n : ℝ))
    (fun n : ℕ => Real.log ((n : ℝ) + 2))

noncomputable def high_probability_mixed_approximation
    (A : randomized_k_center_algorithm) (k : ℕ) : Prop :=
  ∃ c : ℕ, 0 < c ∧ ∃ N : ℕ,
    ∀ (n : ℕ) (G : word_ram_graph n), N ≤ n →
      1 - 1 / ((n : ENNReal) ^ c) ≤
        (Nat.card
          {seed : Fin (2 ^ A.randomBits k n G.graph.edgeSet.ncard) //
            k_center_mixed_approximation G.graph k
              (word_ram_decode_centers n (A.run G k seed).output)} : ENNReal) /
          ((2 ^ A.randomBits k n G.graph.edgeSet.ncard : ℕ) : ENNReal)

theorem beyond_two_approximation_for_k_center (k : ℕ) (hk : 2 ≤ k) :
    ∃ A : randomized_k_center_algorithm,
      logarithmic_word_bound (A.wordBits k) ∧
      target_soft_o_running_time A.steps k ∧
      high_probability_mixed_approximation A k := by sorry

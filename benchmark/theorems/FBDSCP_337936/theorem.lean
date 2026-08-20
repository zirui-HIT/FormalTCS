import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Data.Finset.Filter
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option linter.all false
set_option maxHeartbeats 500000

structure communication_resources where
  alice_bits : ℕ
  bob_bits : ℕ
  carol_bits : ℕ
  merlin_bits : ℕ
  alice_time : ℕ
  bob_time : ℕ
  carol_time : ℕ

inductive communication_tree
    (X Y Advice PublicCoin PrivateCoin : Type) where
  | output (value : Bool)
  | alice (bits time : ℕ)
      (message : PMF X → X → Fin (2 ^ bits))
      (next : Fin (2 ^ bits) →
        communication_tree X Y Advice PublicCoin PrivateCoin)
  | bob (bits time : ℕ)
      (message : Y → Fin (2 ^ bits))
      (next : Fin (2 ^ bits) →
        communication_tree X Y Advice PublicCoin PrivateCoin)
  | merlin (bits : ℕ)
      (message : Advice → Fin (2 ^ bits))
      (next : Fin (2 ^ bits) →
        communication_tree X Y Advice PublicCoin PrivateCoin)
  | carol (bits time : ℕ)
      (message : PMF X → PublicCoin → PrivateCoin → Fin (2 ^ bits))
      (next : Fin (2 ^ bits) →
        communication_tree X Y Advice PublicCoin PrivateCoin)

def communication_tree_run
    {X Y Advice PublicCoin PrivateCoin : Type} :
    communication_tree X Y Advice PublicCoin PrivateCoin →
      PMF X → X → Y → Advice → PublicCoin → PrivateCoin → Bool
  | .output value, _, _, _, _, _, _ => value
  | .alice _ _ message next, distribution, x, y, advice, publicCoin, privateCoin =>
      communication_tree_run (next (message distribution x))
        distribution x y advice publicCoin privateCoin
  | .bob _ _ message next, distribution, x, y, advice, publicCoin, privateCoin =>
      communication_tree_run (next (message y))
        distribution x y advice publicCoin privateCoin
  | .merlin _ message next, distribution, x, y, advice, publicCoin, privateCoin =>
      communication_tree_run (next (message advice))
        distribution x y advice publicCoin privateCoin
  | .carol _ _ message next, distribution, x, y, advice, publicCoin, privateCoin =>
      communication_tree_run (next (message distribution publicCoin privateCoin))
        distribution x y advice publicCoin privateCoin

def communication_tree_resources
    {X Y Advice PublicCoin PrivateCoin : Type} :
    communication_tree X Y Advice PublicCoin PrivateCoin →
      PMF X → X → Y → Advice → PublicCoin → PrivateCoin →
        communication_resources
  | .output _, _, _, _, _, _, _ =>
      ⟨0, 0, 0, 0, 0, 0, 0⟩
  | .alice bits time message next,
      distribution, x, y, advice, publicCoin, privateCoin =>
      let tail := communication_tree_resources (next (message distribution x))
        distribution x y advice publicCoin privateCoin
      { tail with
        alice_bits := bits + tail.alice_bits
        alice_time := (time + 1) + tail.alice_time }
  | .bob bits time message next,
      distribution, x, y, advice, publicCoin, privateCoin =>
      let tail := communication_tree_resources (next (message y))
        distribution x y advice publicCoin privateCoin
      { tail with
        bob_bits := bits + tail.bob_bits
        bob_time := (time + 1) + tail.bob_time }
  | .merlin bits message next,
      distribution, x, y, advice, publicCoin, privateCoin =>
      let tail := communication_tree_resources (next (message advice))
        distribution x y advice publicCoin privateCoin
      { tail with merlin_bits := bits + tail.merlin_bits }
  | .carol bits time message next,
      distribution, x, y, advice, publicCoin, privateCoin =>
      let tail := communication_tree_resources
        (next (message distribution publicCoin privateCoin))
        distribution x y advice publicCoin privateCoin
      { tail with
        carol_bits := bits + tail.carol_bits
        carol_time := (time + 1) + tail.carol_time }

structure specialized_protocol (X Y : Type) where
  advice : Type
  public_coin : Type
  private_coin : Type
  tree : communication_tree X Y advice public_coin private_coin
  public_coin_distribution : PMF public_coin
  private_coin_distribution : PMF private_coin
  special_advice : PMF X → X → Y → public_coin → advice

def protocol_has_cost_time
    {X Y : Type} (protocol : specialized_protocol X Y)
    (c_a c_b c_c c_m t_a t_b t_c : ℕ) : Prop :=
  ∀ (distribution : PMF X) (x : X) (y : Y)
      (advice : protocol.advice)
      (publicCoin : protocol.public_coin)
      (privateCoin : protocol.private_coin),
    let used := communication_tree_resources protocol.tree
      distribution x y advice publicCoin privateCoin
    used.alice_bits ≤ c_a ∧
      used.bob_bits ≤ c_b ∧
      used.carol_bits ≤ c_c ∧
      used.merlin_bits ≤ c_m ∧
      used.alice_time ≤ t_a ∧
      used.bob_time ≤ t_b ∧
      used.carol_time ≤ t_c

noncomputable def protocol_false_positive_probability
    {X Y : Type} (protocol : specialized_protocol X Y)
    (f : X → Y → Bool) (distribution : PMF X) (y : Y) : ℝ :=
  ∑' x, (distribution x).toReal *
    ∑' publicCoin, (protocol.public_coin_distribution publicCoin).toReal *
      ∑' privateCoin, (protocol.private_coin_distribution privateCoin).toReal *
        if f x y = false ∧
            communication_tree_run protocol.tree distribution x y
              (protocol.special_advice distribution x y publicCoin)
              publicCoin privateCoin = true
        then 1
        else 0

def protocol_has_false_positive_error
    {X Y : Type} (protocol : specialized_protocol X Y)
    (f : X → Y → Bool) (ε : ℝ) : Prop :=
  0 ≤ ε ∧
    ∀ (distribution : PMF X) (y : Y),
      protocol_false_positive_probability protocol f distribution y ≤ ε

def protocol_has_type_one_error
    {X Y : Type} (protocol : specialized_protocol X Y)
    (f : X → Y → Bool) : Prop :=
  ∀ (distribution : PMF X) (x : X) (y : Y)
      (publicCoin : protocol.public_coin)
      (privateCoin : protocol.private_coin),
    distribution x ≠ 0 → f x y = true →
      communication_tree_run protocol.tree distribution x y
        (protocol.special_advice distribution x y publicCoin)
        publicCoin privateCoin = true

noncomputable def protocol_unsound_acceptance_probability
    {X Y : Type} (protocol : specialized_protocol X Y)
    (distribution : PMF X) (x : X) (y : Y)
    (advice : protocol.advice) (publicCoin : protocol.public_coin) : ℝ :=
  ∑' privateCoin, (protocol.private_coin_distribution privateCoin).toReal *
    if communication_tree_run protocol.tree distribution x y advice
        publicCoin privateCoin = true
    then 1
    else 0

def protocol_has_soundness
    {X Y : Type} (protocol : specialized_protocol X Y) (δ : ℝ) : Prop :=
  0 ≤ δ ∧
    ∀ (distribution : PMF X) (x : X) (y : Y)
      (advice : protocol.advice) (publicCoin : protocol.public_coin),
      distribution x ≠ 0 →
        advice ≠ protocol.special_advice distribution x y publicCoin →
        protocol_unsound_acceptance_probability protocol distribution
          x y advice publicCoin ≤ δ

inductive reporting_cell (X Y : Type) where
  | storedPoint (value : X)
  | query (value : Y)
  | reportPoint (value : X)
  | bit (value : Bool)
  | index (value : ℕ)

noncomputable def preprocessing_input_cells {X Y : Type} (dataset : Finset X) :
    List (reporting_cell X Y) :=
  dataset.1.toList.map reporting_cell.storedPoint

def query_input_cells {X Y : Type} (storedState : List (reporting_cell X Y))
    (y : Y) : List (reporting_cell X Y) :=
  reporting_cell.query y :: storedState

noncomputable def reported_points {X Y : Type}
    (memory : List (reporting_cell X Y)) : Finset X :=
  letI := Classical.decEq X
  (memory.filterMap fun
    | .reportPoint value => some value
    | _ => none).toFinset

abbrev elementary_resource_instruction (C Label Control : Type) :=
  Turing.TM2.Stmt (fun _ : Unit => C) Label Control

abbrev resource_state (C Label Control : Type) :=
  Turing.TM2.Cfg (fun _ : Unit => C) Label Control

structure resource_algorithm (C : Type) where
  label : Type
  control : Type
  [label_finite : Fintype label]
  start : label
  initial : control
  program : label → elementary_resource_instruction C label control

def resource_statement_cost {C Label Control : Type} :
    elementary_resource_instruction C Label Control →
      Control → (Unit → List C) → ℕ
  | .push stack value next, state, memory =>
      1 + resource_statement_cost next state
        (Function.update memory stack (value state :: memory stack))
  | .peek stack update next, state, memory =>
      1 + resource_statement_cost next
        (update state (memory stack).head?) memory
  | .pop stack update next, state, memory =>
      1 + resource_statement_cost next
        (update state (memory stack).head?)
        (Function.update memory stack (memory stack).tail)
  | .load update next, state, memory =>
      1 + resource_statement_cost next (update state) memory
  | .branch predicate ifTrue ifFalse, state, memory =>
      1 + if predicate state then
        resource_statement_cost ifTrue state memory
      else
        resource_statement_cost ifFalse state memory
  | .goto _, _, _ => 1
  | .halt, _, _ => 1

def resource_step_cost {C : Type} (algorithm : resource_algorithm C) :
    resource_state C algorithm.label algorithm.control → ℕ
  | ⟨none, _, _⟩ => 0
  | ⟨some label, state, memory⟩ =>
      resource_statement_cost (algorithm.program label) state memory

def resource_initial_state {C : Type} (algorithm : resource_algorithm C)
    (initialMemory : List C) :
    resource_state C algorithm.label algorithm.control :=
  ⟨some algorithm.start, algorithm.initial, fun _ => initialMemory⟩

def transition_trace {C : Type} (step : C → C → Prop) : List C → Prop
  | [] => True
  | [_] => True
  | first :: second :: remainder =>
      step first second ∧ transition_trace step (second :: remainder)

structure resource_execution
    {C : Type} (algorithm : resource_algorithm C) (initialMemory : List C) where
  trace : List (resource_state C algorithm.label algorithm.control)
  trace_nonempty : trace ≠ []
  begins_at_input : trace.head? = some (resource_initial_state algorithm initialMemory)
  follows_transition : transition_trace
    (fun current next => Turing.TM2.step algorithm.program current = some next) trace
  final_configuration : resource_state C algorithm.label algorithm.control
  ends_at_result : trace.reverse.head? = some final_configuration
  halted : final_configuration.l = none
  final_memory : List C
  final_memory_eq : final_configuration.stk () = final_memory

def resource_configuration_space {C Label Control : Type}
    (configuration : resource_state C Label Control) : ℕ :=
  (configuration.stk ()).length

def execution_trace_space {C Label Control : Type} :
    List (resource_state C Label Control) → ℕ
  | [] => 0
  | configuration :: remainder =>
      max (resource_configuration_space configuration)
        (execution_trace_space remainder)

def execution_time {C : Type} {algorithm : resource_algorithm C}
    {initialMemory : List C}
    (execution : resource_execution algorithm initialMemory) : ℕ :=
  (execution.trace.map (resource_step_cost algorithm)).sum

def execution_space {C : Type} {algorithm : resource_algorithm C}
    {initialMemory : List C}
    (execution : resource_execution algorithm initialMemory) : ℕ :=
  execution_trace_space execution.trace

structure reporting_data_structure (X Y : Type) where
  seed : Type
  seed_distribution : PMF seed
  preprocess_algorithm : seed → resource_algorithm (reporting_cell X Y)
  preprocess : ∀ dataset randomSeed,
    resource_execution (preprocess_algorithm randomSeed)
      (preprocessing_input_cells dataset)
  query_algorithm : resource_algorithm (reporting_cell X Y)
  query : ∀ storedState y,
    resource_execution query_algorithm (query_input_cells storedState y)

def matching_report
    {X Y : Type} (f : X → Y → Bool) (dataset : Finset X) (y : Y) :
    Finset X :=
  dataset.filter (fun x => f x y = true)

def report_count
    {X Y : Type} (f : X → Y → Bool) (dataset : Finset X) (y : Y) : ℕ :=
  (matching_report f dataset y).card

noncomputable def expected_query_time
    {X Y : Type} (dataStructure : reporting_data_structure X Y)
    (dataset : Finset X) (y : Y) : ℝ :=
  ∑' randomSeed, (dataStructure.seed_distribution randomSeed).toReal *
    (execution_time (dataStructure.query
      (dataStructure.preprocess dataset randomSeed).final_memory y) : ℝ)

def reports_exactly
    {X Y : Type} (dataStructure : reporting_data_structure X Y)
    (f : X → Y → Bool) : Prop :=
  ∀ (dataset : Finset X) (randomSeed : dataStructure.seed) (y : Y),
    reported_points ((dataStructure.query
      (dataStructure.preprocess dataset randomSeed).final_memory y).final_memory) =
      matching_report f dataset y

structure reduction_constants where
  space_exponent : ℕ
  preprocessing_exponent : ℕ
  query_exponent : ℕ
  soundness_exponent : ℕ
  false_positive_factor : ℕ
  output_factor : ℕ
  space_exponent_pos : 0 < space_exponent
  preprocessing_exponent_pos : 0 < preprocessing_exponent
  query_exponent_pos : 0 < query_exponent
  soundness_exponent_pos : 0 < soundness_exponent
  false_positive_factor_pos : 0 < false_positive_factor
  output_factor_pos : 0 < output_factor

def exponential_overhead (constant cost : ℕ) : ℕ :=
  2 ^ (constant * cost)

def has_space_bound
    {X Y : Type} (dataStructure : reporting_data_structure X Y)
    (constants : reduction_constants) (c_a c_b c_c c_m : ℕ) : Prop :=
  ∀ (dataset : Finset X) (randomSeed : dataStructure.seed),
    execution_space (dataStructure.preprocess dataset randomSeed) ≤
      exponential_overhead constants.space_exponent (c_a + c_b + c_m) *
        (dataset.card + c_c)

def has_preprocessing_bound
    {X Y : Type} (dataStructure : reporting_data_structure X Y)
    (constants : reduction_constants)
    (c_a c_b c_m t_a t_b t_c : ℕ) : Prop :=
  ∀ (dataset : Finset X) (randomSeed : dataStructure.seed),
    execution_time (dataStructure.preprocess dataset randomSeed) ≤
      exponential_overhead constants.preprocessing_exponent
          (c_a + c_b + c_m) *
        dataset.card * (t_a + t_b + t_c) + 2

def query_upper_bound
    (constants : reduction_constants)
    (c_a c_b c_c c_m t_b n n_y : ℕ) (ε δ : ℝ) : ℝ :=
  (exponential_overhead constants.query_exponent (c_a + c_m) : ℝ) *
      (↑(c_a + c_b + c_m + c_c + t_b) : ℝ) +
    (constants.false_positive_factor : ℝ) * ε * (n : ℝ) +
    (exponential_overhead constants.soundness_exponent c_m : ℝ) *
      δ * (n : ℝ) +
    (constants.output_factor : ℝ) * (n_y : ℝ) + 2

def has_expected_query_bound
    {X Y : Type} (dataStructure : reporting_data_structure X Y)
    (f : X → Y → Bool) (constants : reduction_constants)
    (c_a c_b c_c c_m t_b : ℕ) (ε δ : ℝ) : Prop :=
  ∀ (dataset : Finset X) (y : Y),
    expected_query_time dataStructure dataset y ≤
      query_upper_bound constants c_a c_b c_c c_m t_b
        dataset.card (report_count f dataset y) ε δ

def satisfies_reduction_guarantees
    {X Y : Type} (dataStructure : reporting_data_structure X Y)
    (f : X → Y → Bool) (constants : reduction_constants)
    (c_a c_b c_c c_m t_a t_b t_c : ℕ) (ε δ : ℝ) : Prop :=
  reports_exactly dataStructure f ∧
    has_space_bound dataStructure constants c_a c_b c_c c_m ∧
    has_preprocessing_bound dataStructure constants
      c_a c_b c_m t_a t_b t_c ∧
    has_expected_query_bound dataStructure f constants
      c_a c_b c_c c_m t_b ε δ

theorem reduction_communication_protocols_data_structures :
    ∃ constants : reduction_constants,
      ∀ {X Y : Type} (f : X → Y → Bool)
        (protocol : specialized_protocol X Y)
        (c_a c_b c_c c_m t_a t_b t_c : ℕ) (ε δ : ℝ),
        protocol_has_cost_time protocol
            c_a c_b c_c c_m t_a t_b t_c →
          protocol_has_false_positive_error protocol f ε →
          protocol_has_type_one_error protocol f →
          protocol_has_soundness protocol δ →
          ∃ dataStructure : reporting_data_structure X Y,
            satisfies_reduction_guarantees dataStructure f constants
              c_a c_b c_c c_m t_a t_b t_c ε δ := by sorry

import Architect
import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Data.Finset.Filter
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:communication-resources"
  (statement := /-- The resource use of one complete execution consists of the numbers of bits sent by Alice, Bob, Carol, and Merlin, together with the times used by Alice, Bob, and Carol to construct their messages. -/)
  (title := /-- Communication resources of an execution -/)
  (latexEnv := "definition")]
structure communication_resources where
  alice_bits : ℕ
  bob_bits : ℕ
  carol_bits : ℕ
  merlin_bits : ℕ
  alice_time : ℕ
  bob_time : ℕ
  carol_time : ℕ

@[blueprint "def:communication-tree"
  (statement := /-- A communication tree is a finite protocol tree.  At an Alice node the outgoing message may depend only on the input distribution and Alice's input; at a Bob node it may depend only on Bob's input; at a Merlin node it may depend only on Merlin's advice; and at a Carol node it may depend only on the input distribution and Carol's public and private coins.  Dependence on the preceding transcript is represented by the current node.  Each message belongs to an alphabet of size $2^b$, where $b$ is the declared bit cost of that node. -/)
  (title := /-- Finite specialized communication tree -/)
  (latexEnv := "definition")]
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

@[blueprint "def:communication-tree-run"
  (statement := /-- Given a distribution $\lambda$, inputs $x$ and $y$, advice $m$, and public and private coins, evaluate the communication tree by following the message selected at each successive node. -/)
  (title := /-- Evaluation of a communication tree -/)
  (latexEnv := "definition")]
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

@[blueprint "def:communication-tree-resources"
  (statement := /-- For fixed inputs, advice, and coins, the resources of a communication-tree execution are obtained along the unique executed root-to-leaf path.  The declared bit costs are summed, while every executed Alice, Bob, or Carol node contributes its declared message-construction time plus one mandatory primitive unit.  In particular, every node that constructs a message has strictly positive certified construction cost. -/)
  (title := /-- Resources used along an executed path -/)
  (latexEnv := "definition")]
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

@[blueprint "def:specialized-protocol"
  (statement := /-- A specialized product-distributional protocol consists of a finite communication tree, distributions for Carol's public and private coins, and a distinguished advice $m^*(\lambda,x,y,R_{\mathrm{pub}})$ for every distribution, pair of inputs, and public coin. -/)
  (title := /-- Specialized product-distributional protocol -/)
  (latexEnv := "definition")]
structure specialized_protocol (X Y : Type) where
  advice : Type
  public_coin : Type
  private_coin : Type
  tree : communication_tree X Y advice public_coin private_coin
  public_coin_distribution : PMF public_coin
  private_coin_distribution : PMF private_coin
  special_advice : PMF X → X → Y → public_coin → advice

@[blueprint "def:protocol-has-cost-time"
  (statement := /-- The protocol has $(c_a,c_b,c_c,c_m)$-cost and $(t_a,t_b,t_c)$-time if, for every distribution, inputs, advice, and realization of Carol's coins, the corresponding execution uses at most these seven bounds.  Each Alice, Bob, and Carol message node is charged its declared construction time together with the mandatory positive unit in \cref{def:communication-tree-resources}; hence the three time bounds also bound the respective numbers of executed message nodes. -/)
  (title := /-- Communication-cost and message-construction-time bounds -/)
  (latexEnv := "definition")]
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

@[blueprint "def:protocol-false-positive-probability"
  (statement := /-- For a distribution $\lambda$ and query $y$, the false-positive probability under the distinguished advice is the probability, over $x\sim\lambda$ and Carol's public and private coins, that $f(x,y)=0$ while the protocol outputs $1$. -/)
  (title := /-- False-positive probability under distinguished advice -/)
  (latexEnv := "definition")]
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

@[blueprint "def:protocol-has-false-positive-error"
  (statement := /-- The protocol has false-positive error at most $\epsilon$ under its distinguished advice if $\epsilon\geq 0$ and the preceding false-positive probability is at most $\epsilon$ for every input distribution and every query. -/)
  (title := /-- Uniform false-positive error bound -/)
  (latexEnv := "definition")]
def protocol_has_false_positive_error
    {X Y : Type} (protocol : specialized_protocol X Y)
    (f : X → Y → Bool) (ε : ℝ) : Prop :=
  0 ≤ ε ∧
    ∀ (distribution : PMF X) (y : Y),
      protocol_false_positive_probability protocol f distribution y ≤ ε

@[blueprint "def:protocol-has-type-one-error"
  (statement := /-- The error under distinguished advice is of type I if a positive target value is never rejected on the sampled-input support: for every distribution $\lambda$, every $x$ in the support of $\lambda$, every query $y$, and every realization of Carol's coins, $f(x,y)=1$ forces the execution under $m^*$ to output $1$. -/)
  (title := /-- Type-I error under distinguished advice -/)
  (latexEnv := "definition")]
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

@[blueprint "def:protocol-unsound-acceptance-probability"
  (statement := /-- For fixed $\lambda,x,y,m,R_{\mathrm{pub}}$, the unsound-acceptance probability is the probability over Carol's private coin that the protocol outputs $1$ with advice $m$. -/)
  (title := /-- Acceptance probability of fixed advice -/)
  (latexEnv := "definition")]
noncomputable def protocol_unsound_acceptance_probability
    {X Y : Type} (protocol : specialized_protocol X Y)
    (distribution : PMF X) (x : X) (y : Y)
    (advice : protocol.advice) (publicCoin : protocol.public_coin) : ℝ :=
  ∑' privateCoin, (protocol.private_coin_distribution privateCoin).toReal *
    if communication_tree_run protocol.tree distribution x y advice
        publicCoin privateCoin = true
    then 1
    else 0

@[blueprint "def:protocol-has-soundness"
  (statement := /-- The protocol has soundness at most $\delta$ if $\delta\geq 0$ and, for every fixed distribution $\lambda$, every input $x$ in the support of $\lambda$, every query $y$, every public coin, and every advice distinct from the distinguished advice, the probability of output $1$ over the private coin is at most $\delta$. -/)
  (title := /-- Soundness against non-distinguished advice -/)
  (latexEnv := "definition")]
def protocol_has_soundness
    {X Y : Type} (protocol : specialized_protocol X Y) (δ : ℝ) : Prop :=
  0 ≤ δ ∧
    ∀ (distribution : PMF X) (x : X) (y : Y)
      (advice : protocol.advice) (publicCoin : protocol.public_coin),
      distribution x ≠ 0 →
        advice ≠ protocol.special_advice distribution x y publicCoin →
        protocol_unsound_acceptance_probability protocol distribution
          x y advice publicCoin ≤ δ

@[blueprint "def:reporting-cell"
  (statement := /-- A storage cell for a reporting data structure contains one stored point of $X$, one query value of $Y$, one point marked for the output report, one Boolean control value, or one natural-number word.  In particular, an entire dataset, transcript tree, query, or report is not itself a single cell. -/)
  (title := /-- Atomic cells for reporting data structures -/)
  (latexEnv := "definition")]
inductive reporting_cell (X Y : Type) where
  | storedPoint (value : X)
  | query (value : Y)
  | reportPoint (value : X)
  | bit (value : Bool)
  | index (value : ℕ)

@[blueprint "def:preprocessing-input-cells"
  (statement := /-- The machine representation of a finite preprocessing dataset is the list obtained from the underlying finite multiset, with every element tagged as a stored point.  This representation introduces no transcript tree or precomputed query answer. -/)
  (title := /-- Cell representation of preprocessing input -/)
  (latexEnv := "definition")]
noncomputable def preprocessing_input_cells {X Y : Type} (dataset : Finset X) :
    List (reporting_cell X Y) :=
  dataset.1.toList.map reporting_cell.storedPoint

@[blueprint "def:query-input-cells"
  (statement := /-- The machine representation of a query places one query cell at the head of the persistent cell list returned by preprocessing.  Thus the query is the top stack cell and can be inspected before any persistent cell; no report cell is inserted at the input boundary. -/)
  (title := /-- Cell representation of query input -/)
  (latexEnv := "definition")]
def query_input_cells {X Y : Type} (storedState : List (reporting_cell X Y))
    (y : Y) : List (reporting_cell X Y) :=
  reporting_cell.query y :: storedState

@[blueprint "def:reported-points"
  (statement := /-- The report represented by a final machine memory is the finite set of values occurring in cells explicitly tagged as report points.  Stored points, query cells, control bits, and index words do not contribute to the returned report. -/)
  (title := /-- Structural decoding of report cells -/)
  (latexEnv := "definition")]
noncomputable def reported_points {X Y : Type}
    (memory : List (reporting_cell X Y)) : Finset X :=
  letI := Classical.decEq X
  (memory.filterMap fun
    | .reportPoint value => some value
    | _ => none).toFinset

@[blueprint "def:elementary-resource-instruction"
  (statement := /-- For an atomic cell alphabet $C$, program labels $\Lambda$, and a control-state type $S$, a resource statement is a finite Mathlib stack-machine instruction tree.  Its primitive constructors push, peek at, or pop one cell, update the control state, choose one branch, jump, or halt.  The control type may carry values of $C$: a peek or pop may retain an inspected cell in the control state, and a later push may construct a cell from that retained value.  A single Mathlib machine step evaluates the successive primitive constructors in the selected path of this tree through its terminal jump or halt. -/)
  (title := /-- Stack-machine resource statements -/)
  (latexEnv := "definition")]
abbrev elementary_resource_instruction (C Label Control : Type) :=
  Turing.TM2.Stmt (fun _ : Unit => C) Label Control

@[blueprint "def:resource-state"
  (statement := /-- A resource state is a configuration of the one-stack machine over atomic cells: it consists of the current optional program label, a possibly data-bearing control state, and the complete resident stack. -/)
  (title := /-- Resource-machine configurations -/)
  (latexEnv := "definition")]
abbrev resource_state (C Label Control : Type) :=
  Turing.TM2.Cfg (fun _ : Unit => C) Label Control

@[blueprint "def:resource-algorithm"
  (statement := /-- A resource-accounted algorithm over atomic cells $C$ is a finite-program stack machine.  It has a finite label type, an unrestricted control-state type that may retain inspected values of $C$, a distinguished initial label and state, and a finite instruction tree for each label.  Its operational semantics is the fixed one-step function of Mathlib's stack-machine model, rather than an arbitrary relation supplied by the algorithm.  Allowing data-bearing control is essential: after a peek or pop records an arbitrary cell in the control state, subsequent instructions may preserve it, combine it with other retained input such as a query, and push a transformed cell. -/)
  (title := /-- Finite-program resource algorithm with data-bearing control -/)
  (latexEnv := "definition")]
structure resource_algorithm (C : Type) where
  label : Type
  control : Type
  [label_finite : Fintype label]
  start : label
  initial : control
  program : label → elementary_resource_instruction C label control

@[blueprint "def:resource-statement-cost"
  (statement := /-- Let $C$ be an atomic cell alphabet, let $\Lambda$ be a label type, and let $S$ be a control-state type.  The cost of executing a resource statement from a control state and one-stack memory is the number of primitive constructors on the path actually evaluated by Mathlib's statement semantics.  A push first updates the stack seen by the continuation; a peek, pop, or load first updates the continuation's control state and, for a pop, its stack; a branch charges its test and follows only the selected continuation; and a jump or halt has unit cost. -/)
  (title := /-- Primitive cost of an executed resource statement -/)
  (latexEnv := "definition")]
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

@[blueprint "def:resource-step-cost"
  (statement := /-- Let $A$ be a resource algorithm.  The primitive cost charged at a nonhalting configuration is the path-sensitive cost of the statement stored at its current program label, evaluated from its current control state and stack.  A halting configuration has cost zero because no further Mathlib machine step is taken from it. -/)
  (title := /-- Primitive cost of one Mathlib machine step -/)
  (latexEnv := "definition")]
def resource_step_cost {C : Type} (algorithm : resource_algorithm C) :
    resource_state C algorithm.label algorithm.control → ℕ
  | ⟨none, _, _⟩ => 0
  | ⟨some label, state, memory⟩ =>
      resource_statement_cost (algorithm.program label) state memory

@[blueprint "def:resource-initial-state"
  (statement := /-- The initial configuration of a resource algorithm places the supplied list of atomic input cells, and only that list, on its unique stack and starts at the distinguished program label and control state. -/)
  (title := /-- Initial resource-machine configuration -/)
  (latexEnv := "definition")]
def resource_initial_state {C : Type} (algorithm : resource_algorithm C)
    (initialMemory : List C) :
    resource_state C algorithm.label algorithm.control :=
  ⟨some algorithm.start, algorithm.initial, fun _ => initialMemory⟩

@[blueprint "def:transition-trace"
  (statement := /-- A finite list of configurations follows a transition relation if every two successive configurations in the list are related by one transition. -/)
  (title := /-- Valid finite transition trace -/)
  (latexEnv := "definition")]
def transition_trace {C : Type} (step : C → C → Prop) : List C → Prop
  | [] => True
  | [_] => True
  | first :: second :: remainder =>
      step first second ∧ transition_trace step (second :: remainder)

@[blueprint "def:resource-execution"
  (statement := /-- A certified execution from an explicit initial cell list is a nonempty finite trace beginning at the corresponding initial configuration, following one complete Mathlib stack-machine statement evaluation at each configuration transition, and ending at a halting configuration.  Primitive operations executed within each such transition are charged separately by \cref{def:resource-step-cost}.  The final memory is required to be the actual content of the unique machine stack in that final configuration. -/)
  (title := /-- Certified execution of a resource-accounted algorithm -/)
  (latexEnv := "definition")]
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

@[blueprint "def:resource-configuration-space"
  (statement := /-- The resident space of a one-stack resource-machine configuration is the number of atomic cells on its explicit stack. -/)
  (title := /-- Resident space of one configuration -/)
  (latexEnv := "definition")]
def resource_configuration_space {C Label Control : Type}
    (configuration : resource_state C Label Control) : ℕ :=
  (configuration.stk ()).length

@[blueprint "def:execution-trace-space"
  (statement := /-- The space used along a finite machine trace is the maximum number of atomic cells on the explicit stack of any configuration in that trace. -/)
  (title := /-- Maximum resident space along a trace -/)
  (latexEnv := "definition")]
def execution_trace_space {C Label Control : Type} :
    List (resource_state C Label Control) → ℕ
  | [] => 0
  | configuration :: remainder =>
      max (resource_configuration_space configuration)
        (execution_trace_space remainder)

@[blueprint "def:execution-time"
  (statement := /-- The running time certified by an execution is the sum, over its configuration trace, of the path-sensitive primitive cost in \cref{def:resource-step-cost}.  Every push, peek, pop, control update, selected branch, jump, and halt executed inside a Mathlib machine step contributes one unit; the final halting configuration contributes zero because it initiates no step. -/)
  (title := /-- Time of a certified execution -/)
  (latexEnv := "definition")]
def execution_time {C : Type} {algorithm : resource_algorithm C}
    {initialMemory : List C}
    (execution : resource_execution algorithm initialMemory) : ℕ :=
  (execution.trace.map (resource_step_cost algorithm)).sum

@[blueprint "def:execution-space"
  (statement := /-- The space certified by an execution is the maximum number of resident storage cells among the configurations of its valid operational trace. -/)
  (title := /-- Space of a certified execution -/)
  (latexEnv := "definition")]
def execution_space {C : Type} {algorithm : resource_algorithm C}
    {initialMemory : List C}
    (execution : resource_execution algorithm initialMemory) : ℕ :=
  execution_trace_space execution.trace

@[blueprint "def:reporting-data-structure"
  (statement := /-- A randomized reporting data structure on $X$ and $Y$ consists of a preprocessing-seed distribution, one finite-program preprocessing machine for each seed, and a finite-program query machine, all over the atomic cells of \cref{def:reporting-cell}.  Their unrestricted control types may retain inspected points and queries, while every executed primitive stack or control operation is charged by \cref{def:resource-statement-cost}.  Preprocessing starts from exactly the stored-point representation of its dataset.  Its final stack is the persistent state.  Querying starts from exactly one query cell followed by that persistent stack, so the query occupies the top stack cell, and the report is structurally determined by the report-point cells in the final stack. -/)
  (title := /-- Randomized reporting data structure with certified costs -/)
  (latexEnv := "definition")]
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

@[blueprint "def:matching-report"
  (statement := /-- For a dataset $\mathcal D$ and query $y$, the correct report is the finite subset of all $x\in\mathcal D$ for which $f(x,y)=1$. -/)
  (title := /-- Correct report for a dataset and query -/)
  (latexEnv := "definition")]
def matching_report
    {X Y : Type} (f : X → Y → Bool) (dataset : Finset X) (y : Y) :
    Finset X :=
  dataset.filter (fun x => f x y = true)

@[blueprint "def:report-count"
  (statement := /-- The output size $n_y$ is the cardinality of the correct report for $y$. -/)
  (title := /-- Number of reported matches -/)
  (latexEnv := "definition")]
def report_count
    {X Y : Type} (f : X → Y → Bool) (dataset : Finset X) (y : Y) : ℕ :=
  (matching_report f dataset y).card

@[blueprint "def:expected-query-time"
  (statement := /-- The expected query time on $\mathcal D$ and $y$ is the discrete expectation, with respect to the preprocessing-seed distribution, of the primitive-instruction cost in \cref{def:execution-time} of the certified execution obtained by querying the final stack returned by preprocessing. -/)
  (title := /-- Expected query time -/)
  (latexEnv := "definition")]
noncomputable def expected_query_time
    {X Y : Type} (dataStructure : reporting_data_structure X Y)
    (dataset : Finset X) (y : Y) : ℝ :=
  ∑' randomSeed, (dataStructure.seed_distribution randomSeed).toReal *
    (execution_time (dataStructure.query
      (dataStructure.preprocess dataset randomSeed).final_memory y) : ℝ)

@[blueprint "def:reports-exactly"
  (statement := /-- A reporting data structure is correct for $f$ if, for every finite dataset, preprocessing seed, and query, the finite set structurally extracted from the final report-point cells of the query execution is exactly the set of matching elements of the dataset. -/)
  (title := /-- Exact reporting correctness -/)
  (latexEnv := "definition")]
def reports_exactly
    {X Y : Type} (dataStructure : reporting_data_structure X Y)
    (f : X → Y → Bool) : Prop :=
  ∀ (dataset : Finset X) (randomSeed : dataStructure.seed) (y : Y),
    reported_points ((dataStructure.query
      (dataStructure.preprocess dataset randomSeed).final_memory y).final_memory) =
      matching_report f dataset y

@[blueprint "def:reduction-constants"
  (statement := /-- The absolute constants hidden in the reduction bounds consist of four exponent multipliers $K_s,K_p,K_q,K_\delta$, two linear multipliers $K_\epsilon,K_o$, and one additive slack $K_c$.  All seven constants are positive; in the reduction theorem one common record is chosen before the input domains, target function, protocol, resource bounds, and error parameters, and hence is independent of all instance data.  In particular the additive slack $K_c$, which absorbs the fixed instruction sequence that every machine executes irrespective of its input, is an absolute constant and not a numeral fixed in advance. -/)
  (title := /-- Explicit constants for the asymptotic reduction bounds -/)
  (latexEnv := "definition")]
structure reduction_constants where
  space_exponent : ℕ
  preprocessing_exponent : ℕ
  query_exponent : ℕ
  soundness_exponent : ℕ
  false_positive_factor : ℕ
  output_factor : ℕ
  additive_slack : ℕ
  space_exponent_pos : 0 < space_exponent
  preprocessing_exponent_pos : 0 < preprocessing_exponent
  query_exponent_pos : 0 < query_exponent
  soundness_exponent_pos : 0 < soundness_exponent
  false_positive_factor_pos : 0 < false_positive_factor
  output_factor_pos : 0 < output_factor
  additive_slack_pos : 0 < additive_slack

@[blueprint "def:exponential-overhead"
  (statement := /-- For an explicit constant $K$ and a cost $c$, the expression $2^{Kc}$ represents a factor of size $2^{O(c)}$. -/)
  (title := /-- Explicit exponential overhead -/)
  (latexEnv := "definition")]
def exponential_overhead (constant cost : ℕ) : ℕ :=
  2 ^ (constant * cost)

@[blueprint "def:has-space-bound"
  (statement := /-- The data structure satisfies the reduction's space bound if, for every finite dataset $\mathcal D$ and preprocessing seed, every configuration in the certified preprocessing execution has at most $2^{K_s(c_a+c_b+c_m)}(|\mathcal D|+c_c)$ resident storage cells. -/)
  (title := /-- Space guarantee of the reduction -/)
  (latexEnv := "definition")]
def has_space_bound
    {X Y : Type} (dataStructure : reporting_data_structure X Y)
    (constants : reduction_constants) (c_a c_b c_c c_m : ℕ) : Prop :=
  ∀ (dataset : Finset X) (randomSeed : dataStructure.seed),
    execution_space (dataStructure.preprocess dataset randomSeed) ≤
      exponential_overhead constants.space_exponent (c_a + c_b + c_m) *
        (dataset.card + c_c)

@[blueprint "def:has-preprocessing-bound"
  (statement := /-- The data structure satisfies the reduction's preprocessing bound if, for every finite dataset $\mathcal D$ and seed, the primitive-instruction cost of the certified preprocessing execution is at most
  \[
  2^{K_p(c_a+c_b+c_m)}|\mathcal D|(t_a+t_b+t_c)+K_c.
  \]
  Each push, peek, pop, control update, selected branch, jump, and halt executed inside a Mathlib machine step is charged separately, and the additive slack $K_c$ of \cref{def:reduction-constants} covers the fixed initialization and halting sequence, which is independent of the dataset and of all cost and time parameters. -/)
  (title := /-- Preprocessing-time guarantee of the reduction -/)
  (latexEnv := "definition")]
def has_preprocessing_bound
    {X Y : Type} (dataStructure : reporting_data_structure X Y)
    (constants : reduction_constants)
    (c_a c_b c_m t_a t_b t_c : ℕ) : Prop :=
  ∀ (dataset : Finset X) (randomSeed : dataStructure.seed),
    execution_time (dataStructure.preprocess dataset randomSeed) ≤
      exponential_overhead constants.preprocessing_exponent
          (c_a + c_b + c_m) *
        dataset.card * (t_a + t_b + t_c) + constants.additive_slack

@[blueprint "def:query-upper-bound"
  (statement := /-- With explicit constants, the claimed expected-query bound is
  \[
  2^{K_q(c_a+c_m)}(c_a+c_b+c_m+c_c+t_b)
  +K_\epsilon\epsilon n
  +2^{K_\delta c_m}\delta n
  +K_o n_y+K_c.
  \]
  Every unit of this quantity bounds one executed primitive stack-machine instruction, including instructions evaluated inside the same Mathlib machine step, and the additive slack $K_c$ of \cref{def:reduction-constants} covers the fixed initialization, input-inspection, and halting sequence, which is independent of $n$, of $n_y$, and of all cost, time, and error parameters. -/)
  (title := /-- Explicit expected-query upper bound -/)
  (latexEnv := "definition")]
def query_upper_bound
    (constants : reduction_constants)
    (c_a c_b c_c c_m t_b n n_y : ℕ) (ε δ : ℝ) : ℝ :=
  (exponential_overhead constants.query_exponent (c_a + c_m) : ℝ) *
      (↑(c_a + c_b + c_m + c_c + t_b) : ℝ) +
    (constants.false_positive_factor : ℝ) * ε * (n : ℝ) +
    (exponential_overhead constants.soundness_exponent c_m : ℝ) *
      δ * (n : ℝ) +
    (constants.output_factor : ℝ) * (n_y : ℝ) + (constants.additive_slack : ℝ)

@[blueprint "def:has-expected-query-bound"
  (statement := /-- The data structure satisfies the expected-query guarantee if, for every finite dataset and query, the expected number of executed primitive stack-machine instructions in the certified query execution is bounded by the explicit expression with $n=|\mathcal D|$ and $n_y$ equal to the number of matches, including the absolute additive slack $K_c$ of \cref{def:reduction-constants} for initialization, input inspection, and halting. -/)
  (title := /-- Expected-query-time guarantee of the reduction -/)
  (latexEnv := "definition")]
def has_expected_query_bound
    {X Y : Type} (dataStructure : reporting_data_structure X Y)
    (f : X → Y → Bool) (constants : reduction_constants)
    (c_a c_b c_c c_m t_b : ℕ) (ε δ : ℝ) : Prop :=
  ∀ (dataset : Finset X) (y : Y),
    expected_query_time dataStructure dataset y ≤
      query_upper_bound constants c_a c_b c_c c_m t_b
        dataset.card (report_count f dataset y) ε δ

@[blueprint "def:satisfies-reduction-guarantees"
  (statement := /-- A data structure satisfies the complete conclusion of the reduction when its finite-program, data-bearing-control stack-machine implementations report exactly and their certified traces obey the stated maximum-resident-space, preprocessing primitive-instruction, and expected-query primitive-instruction bounds with one common record of absolute constants. -/)
  (title := /-- Complete data-structure guarantees -/)
  (latexEnv := "definition")]
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

@[blueprint "def:protocol-reduction-witness"
  (statement := /-- For a fixed record of absolute constants, a witness to one instance of the protocol reduction consists of a reporting data structure implemented by Mathlib's stack-machine semantics, equipped with the path-sensitive primitive cost of \cref{def:resource-statement-cost}, and satisfying exactness and all three certified resource bounds for the prescribed costs, times, and error parameters. -/)
  (title := /-- Witness for the communication-to-data-structure reduction -/)
  (latexEnv := "definition")]
structure protocol_reduction_witness
    (constants : reduction_constants) {X Y : Type} (f : X → Y → Bool)
    (c_a c_b c_c c_m t_a t_b t_c : ℕ) (ε δ : ℝ) where
  data_structure : reporting_data_structure X Y
  guarantees : satisfies_reduction_guarantees data_structure f constants
    c_a c_b c_c c_m t_a t_b t_c ε δ

@[blueprint "lem:matching-report-membership"
  (statement := /-- Let $X$ and $Y$ be types, let $f\colon X\times Y\to\{0,1\}$,
  let $\mathcal D\subseteq X$ be finite, and let $y\in Y$ and $x\in X$.  Then
  \[
  x\in\operatorname{matchingReport}_f(\mathcal D,y)
  \quad\Longleftrightarrow\quad
  x\in\mathcal D\ \text{and}\ f(x,y)=1.
  \] -/)
  (proof := /-- By \cref{def:matching-report}, the correct report is obtained by filtering $\mathcal D$ with the predicate $f(x,y)=1$.  The membership characterization of \texttt{Finset.filter} therefore gives the displayed equivalence, including both membership in the original dataset and satisfaction of the predicate. -/)
  (title := /-- Membership in the correct report -/)
  (latexEnv := "lemma")]
lemma matching_report_membership
    {X Y : Type} (f : X → Y → Bool)
    (dataset : Finset X) (y : Y) (x : X) :
    x ∈ matching_report f dataset y ↔
      x ∈ dataset ∧ f x y = true := by
  unfold matching_report
  exact Finset.mem_filter

@[blueprint "lem:expected-query-time-formula"
  (statement := /-- For every randomized reporting data structure, finite dataset $\mathcal D$, and query $y$, the expected query time equals the sum over preprocessing seeds of the seed probability times the primitive-instruction cost of the certified execution that queries the final stack returned by preprocessing. -/)
  (proof := /-- Unfolding \cref{def:expected-query-time} yields exactly the asserted PMF-weighted sum.  Each summand is the probability mass of the seed multiplied by the certified path-sensitive primitive-instruction cost, cast to $\mathbb R$, of the corresponding query execution. -/)
  (title := /-- Discrete formula for expected query time -/)
  (latexEnv := "lemma")]
lemma expected_query_time_formula
    {X Y : Type} (dataStructure : reporting_data_structure X Y)
    (dataset : Finset X) (y : Y) :
    expected_query_time dataStructure dataset y =
      ∑' randomSeed, (dataStructure.seed_distribution randomSeed).toReal *
        (execution_time (dataStructure.query
          (dataStructure.preprocess dataset randomSeed).final_memory y) : ℝ) := by
  rfl

@[blueprint "lem:transcript-tree-reduction"
  (statement := /-- There is a single record of positive natural-number constants
  $K_s,K_p,K_q,K_\delta,K_\epsilon,K_o,K_c$ with the following uniform property.
  Let $X,Y$ be types, let $f\colon X\times Y\to\{0,1\}$, let $\pi$ be a
  specialized protocol, let
  $c_a,c_b,c_c,c_m,t_a,t_b,t_c\in\mathbb N$, and let
  $\epsilon,\delta\in\mathbb R$.  Assume that every execution of $\pi$
  satisfies the indicated communication and message-construction bounds; that
  $\epsilon\geq 0$ and, for every input distribution and query, the
  false-positive probability under the distinguished advice is at most
  $\epsilon$; that every positive input in the support of the input
  distribution is accepted under the distinguished advice for every
  realization of Carol's coins; and that $\delta\geq 0$ and every
  non-distinguished advice has acceptance probability at most $\delta$ over
  Carol's private coin, for every supported input, query, and public coin.

  Then the type of witnesses consisting of a randomized reporting data
  structure implemented by finite-program stack machines whose control states
  may retain inspected data, together with proofs of the following guarantees,
  is nonempty.
  For every finite dataset $\mathcal D$, every preprocessing seed, and every
  query $y$, the certified query returns exactly
  $\{x\in\mathcal D:f(x,y)=1\}$.  Every certified preprocessing execution
  has resident space at most
  \[
  2^{K_s(c_a+c_b+c_m)}\bigl(|\mathcal D|+c_c\bigr)
  \]
  and primitive-instruction cost at most
  \[
  2^{K_p(c_a+c_b+c_m)}|\mathcal D|(t_a+t_b+t_c)+K_c.
  \]
  Moreover, writing $n_y$ for the number of reported points, the expected
  certified query primitive-instruction cost, over the preprocessing-seed distribution,
  is at most
  \[
  2^{K_q(c_a+c_m)}(c_a+c_b+c_m+c_c+t_b)
  +K_\epsilon\epsilon|\mathcal D|
  +2^{K_\delta c_m}\delta|\mathcal D|
  +K_o n_y+K_c.
  \]
  The same record of constants is used for all the quantified types,
  functions, protocols, resource bounds, and error parameters. -/)
  (proof := /-- Fix the absolute constants large enough to absorb the fixed
  stack-machine instruction sequences used below; in particular choose the
  additive slack $K_c$ of \cref{def:reduction-constants} to be an upper bound,
  valid for every instance, for the number of primitive instructions spent on
  initialization, on inspecting the topmost input cell, and on halting.  Such a
  bound exists because those instruction sequences are fixed by the two
  machines and depend neither on the dataset nor on the cost, time, and error
  parameters.  The empty dataset is
  handled by machines that initialize and halt without emitting a report
  point, so assume that $\mathcal D$ is nonempty.  Let $\lambda$ be the
  uniform probability mass function on $\mathcal D$, and sample Carol's
  public and private coins according to the distributions in the protocol.
  These coins form the preprocessing seed.

  Preprocessing constructs the protocol transcript tree recursively.  At an
  Alice node it creates one child for each possible Alice message; at a Bob
  node it creates one child for each possible Bob message; at a Merlin node it
  creates one child for each possible Merlin message; and at a Carol node it
  stores the unique message determined by $\lambda$, the sampled coins, and
  the preceding transcript.  At a $1$-leaf with transcript $\tau$, it stores
  precisely those $x\in\mathcal D$ for which Alice's messages on input $x$
  agree with $\tau$ when Bob and Merlin send the messages recorded by
  $\tau$.  The construction is implemented by the finite-program machine of
  \cref{def:resource-algorithm}: each tree-cell read, write, push, pop, branch,
  or control transfer is one primitive constructor in the statement language
  of \cref{def:elementary-resource-instruction}, and
  \cref{def:resource-statement-cost} charges every constructor on the path
  selected by the current control state and stack.  The only initial cells are
  those in \cref{def:preprocessing-input-cells}.  The preprocessing control
  type contains states carrying an inspected dataset point.  A peek or pop
  can therefore retain any $x\in X$, and a subsequent push can copy that
  point into every appropriate leaf, with no finite-range restriction on
  $X$.  Thus no semantic tree or report is inserted at a boundary.

  To answer $y$, the query machine starts from the single query cell of
  \cref{def:query-input-cells} followed by the stored transcript-tree cells.
  Because this query cell is at the head of the stack, the machine first
  inspects it and records $y$ in its data-bearing control state, before it
  traverses any persistent cell.  While a leaf list
  is scanned, a peek or pop records the current stored point $x$ in a second
  control component without discarding $y$; a branch tests $f(x,y)$; and, if
  that test succeeds, a push computes \texttt{reportPoint}~$x$ from the
  retained point.  Hence the primitive instruction sequence both preserves
  the query and constructs the required report cell for arbitrary $X$ and
  $Y$.
  For each of the at most $2^{c_m}$ Merlin messages, it traverses the tree as
  follows: it explores every Alice child, follows the unique Bob child
  selected by $y$ and the current transcript, follows the child selected by
  the fixed Merlin message, and reads the unique stored Carol message.  On
  reaching a visited $1$-leaf it scans that leaf's list and emits a report
  cell exactly when the corresponding point satisfies $f(x,y)=1$.  The
  returned set is the structural extraction of
  \cref{def:reported-points}; hence, by the membership equivalence in
  \cref{lem:matching-report-membership}, every emitted element belongs to
  $\mathcal D$ and satisfies $f(x,y)=1$.

  Conversely, suppose $x\in\mathcal D$ and $f(x,y)=1$.  For every public
  coin, choose the distinguished Merlin advice.  The type-I hypothesis says
  that the resulting protocol execution accepts for every private coin.
  Its root-to-leaf transcript is therefore visited by the query traversal,
  and the preprocessing rule placed $x$ in the corresponding $1$-leaf.
  The query consequently emits $x$.  This proves exact reporting.

  The protocol-cost hypothesis bounds the branching contributed by Alice,
  Bob, and Merlin by an exponential in $c_a+c_b+c_m$, while every stored
  Carol message has length at most $c_c$.  Summing over the $|\mathcal D|$
  input points gives resident space at most
  $2^{K_s(c_a+c_b+c_m)}(|\mathcal D|+c_c)$.  Constructing Alice's, Bob's, and
  Carol's messages for every relevant point and transcript costs at most
  $2^{K_p(c_a+c_b+c_m)}|\mathcal D|(t_a+t_b+t_c)+K_c$ primitive machine
  instructions, since the first summand dominates all dataset-dependent work
  and, by the choice of $K_c$ above, the residual initialization and halting
  sequence costs at most $K_c$.  Indeed, by
  \cref{def:communication-tree-resources, def:protocol-has-cost-time}, every
  executed Alice, Bob, or Carol node contributes its declared construction
  time plus one mandatory primitive unit.  The protocol time bounds therefore
  dominate both the declared construction costs and the number of executed
  message nodes on every path; in particular, no message construction can be
  traversed at zero certified cost.

  For the query bound, the deterministic traversal overhead for one query is
  at most
  $2^{K_q(c_a+c_m)}(c_a+c_b+c_m+c_c+t_b)$.  Under the distinguished advice,
  the expected number of false-positive stored points is at most
  $\epsilon|\mathcal D|$.  For every other advice and every fixed public
  coin, soundness bounds the private-coin acceptance probability of each
  point by $\delta$; summing over at most $2^{c_m}$ advice messages and over
  the dataset contributes at most
  $2^{K_\delta c_m}\delta|\mathcal D|$.  Emitting the $n_y$ genuine answers
  costs at most $K_o n_y$, and, by the choice of $K_c$ above, initialization,
  inspection of the topmost query cell, and halting cost at most $K_c$ further
  primitive instructions.  Linearity of the seed expectation, written in the
  discrete form of \cref{lem:expected-query-time-formula}, yields the asserted
  expected-query inequality.  Together with exactness and the space and
  preprocessing estimates, these bounds give the witness of
  \cref{def:protocol-reduction-witness}. -/)
  (title := /-- Transcript-tree reporting construction -/)
  (latexEnv := "lemma")]
lemma transcript_tree_reduction :
    ∃ constants : reduction_constants,
      ∀ {X Y : Type} (f : X → Y → Bool)
        (protocol : specialized_protocol X Y)
        (c_a c_b c_c c_m t_a t_b t_c : ℕ) (ε δ : ℝ),
        protocol_has_cost_time protocol
            c_a c_b c_c c_m t_a t_b t_c →
          protocol_has_false_positive_error protocol f ε →
          protocol_has_type_one_error protocol f →
          protocol_has_soundness protocol δ →
          Nonempty (protocol_reduction_witness constants f
            c_a c_b c_c c_m t_a t_b t_c ε δ) := by
  classical
  obtain ⟨constants, hs1, hs2, hs3, hs4⟩ : ∃ constants : reduction_constants,
      12 ≤ constants.additive_slack ∧ 1 ≤ constants.space_exponent ∧
        4 ≤ constants.false_positive_factor ∧ 10 ≤ constants.output_factor :=
    ⟨⟨1, 1, 1, 1, 4, 10, 12, Nat.one_pos, Nat.one_pos, Nat.one_pos, Nat.one_pos,
      by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num, by norm_num,
      by norm_num⟩
  refine ⟨constants, ?_⟩
  intro X Y f protocol c_a c_b c_c c_m t_a t_b t_c ε δ hcost hfp htype hsound
  obtain ⟨geoPMF, hgeoval⟩ : ∃ p : PMF ℕ, ∀ k : ℕ, p k = (2⁻¹ : ENNReal) ^ (k + 1) := by
    refine ⟨⟨fun k => (2⁻¹ : ENNReal) ^ (k+1), ?_⟩, fun k => rfl⟩
    have h : ∑' k : ℕ, (2⁻¹ : ENNReal) ^ (k+1) = 1 := by
      rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two]
      rw [inv_inv]
      exact ENNReal.inv_mul_cancel two_ne_zero (by exact_mod_cast ENNReal.ofNat_ne_top)
    exact h ▸ ENNReal.summable.hasSum

  let trivAlg (C : Type) : resource_algorithm C :=
    { label := Unit, control := Unit, label_finite := inferInstance,
      start := (), initial := (), program := fun _ => .halt }

  let scanStmt (f : X → Y → Bool) :
      Turing.TM2.Stmt (fun _ : Unit => reporting_cell X Y) Unit
        (ℕ × Bool × Option Y × List (reporting_cell X Y)) :=
    .branch (fun v => 0 < v.1)
      (.load (fun v => (v.1 - 1, v.2)) (.goto (fun _ => ())))
      (.branch (fun v => v.2.1)
        (.branch (fun v => v.2.2.2.isEmpty)
          .halt
          (.push () (fun v => (v.2.2.2.head?).getD (.bit true))
            (.load (fun v => (v.1, v.2.1, v.2.2.1, v.2.2.2.tail)) (.goto (fun _ => ())))))
        (.pop () (fun v c => match c with
            | none => (v.1, true, v.2.2.1, v.2.2.2)
            | some (.query y) => (v.1, false, some y, v.2.2.2)
            | some (.index k) => (2 ^ (k+1), false, v.2.2.1, v.2.2.2)
            | some (.storedPoint x) => (v.1, false, v.2.2.1,
                (match v.2.2.1 with
                 | none => v.2.2.2
                 | some y => if f x y then .reportPoint x :: v.2.2.2 else v.2.2.2))
            | some _ => v)
          (.goto (fun _ => ()))))

  let scanAlg (f : X → Y → Bool) : resource_algorithm (reporting_cell X Y) :=
    { label := Unit, control := ℕ × Bool × Option Y × List (reporting_cell X Y),
      label_finite := inferInstance, start := (), initial := (0, false, none, []),
      program := fun _ => scanStmt f }

  have hupd {C : Type} (a b : List C) :
      Function.update (fun _ : Unit => a) () b = fun _ => b := by
    funext u; cases u; simp

  have stepBurn (f : X → Y → Bool) (n : ℕ) (r : Bool × Option Y × List (reporting_cell X Y))
      (mem : List (reporting_cell X Y)) :
      Turing.TM2.step (fun _ => scanStmt f) ⟨some (), (n+1, r), fun _ => mem⟩ =
        some ⟨some (), (n, r), fun _ => mem⟩ := by
    simp [scanStmt]

  have costBurn (f : X → Y → Bool) (n : ℕ) (r : Bool × Option Y × List (reporting_cell X Y))
      (mem : List (reporting_cell X Y)) :
      resource_step_cost (scanAlg f) ⟨some (), (n+1, r), fun _ => mem⟩ = 3 := by
    simp [scanAlg, resource_step_cost, scanStmt, resource_statement_cost]

  have stepEmitHalt (f : X → Y → Bool) (q : Option Y) (mem : List (reporting_cell X Y)) :
      Turing.TM2.step (fun _ => scanStmt f) ⟨some (), (0, true, q, []), fun _ => mem⟩ =
        some ⟨none, (0, true, q, []), fun _ => mem⟩ := by
    simp [scanStmt]

  have costEmitHalt (f : X → Y → Bool) (q : Option Y) (mem : List (reporting_cell X Y)) :
      resource_step_cost (scanAlg f) ⟨some (), (0, true, q, []), fun _ => mem⟩ = 4 := by
    simp [scanAlg, resource_step_cost, scanStmt, resource_statement_cost]

  have stepEmitPush (f : X → Y → Bool) (q : Option Y) (c : reporting_cell X Y)
      (pen mem : List (reporting_cell X Y)) :
      Turing.TM2.step (fun _ => scanStmt f) ⟨some (), (0, true, q, c :: pen), fun _ => mem⟩ =
        some ⟨some (), (0, true, q, pen), fun _ => c :: mem⟩ := by
    simp [scanStmt, hupd]

  have costEmitPush (f : X → Y → Bool) (q : Option Y) (c : reporting_cell X Y)
      (pen mem : List (reporting_cell X Y)) :
      resource_step_cost (scanAlg f) ⟨some (), (0, true, q, c :: pen), fun _ => mem⟩ = 6 := by
    simp [scanAlg, resource_step_cost, scanStmt, resource_statement_cost]

  have stepScanNil (f : X → Y → Bool) (q : Option Y) (pen : List (reporting_cell X Y)) :
      Turing.TM2.step (fun _ => scanStmt f) ⟨some (), (0, false, q, pen), fun _ => []⟩ =
        some ⟨some (), (0, true, q, pen), fun _ => []⟩ := by
    simp [scanStmt, hupd]

  have costScan (f : X → Y → Bool) (q : Option Y) (pen mem : List (reporting_cell X Y)) :
      resource_step_cost (scanAlg f) ⟨some (), (0, false, q, pen), fun _ => mem⟩ = 4 := by
    simp [scanAlg, resource_step_cost, scanStmt, resource_statement_cost]

  have stepScanQuery (f : X → Y → Bool) (y : Y) (q : Option Y) (pen mem : List (reporting_cell X Y)) :
      Turing.TM2.step (fun _ => scanStmt f)
          ⟨some (), (0, false, q, pen), fun _ => reporting_cell.query y :: mem⟩ =
        some ⟨some (), (0, false, some y, pen), fun _ => mem⟩ := by
    simp [scanStmt, hupd]

  have stepScanIndex (f : X → Y → Bool) (k : ℕ) (q : Option Y) (pen mem : List (reporting_cell X Y)) :
      Turing.TM2.step (fun _ => scanStmt f)
          ⟨some (), (0, false, q, pen), fun _ => reporting_cell.index k :: mem⟩ =
        some ⟨some (), (2 ^ (k+1), false, q, pen), fun _ => mem⟩ := by
    simp [scanStmt, hupd]

  have stepScanPoint (f : X → Y → Bool) (x : X) (y : Y) (pen mem : List (reporting_cell X Y)) :
      Turing.TM2.step (fun _ => scanStmt f)
          ⟨some (), (0, false, some y, pen), fun _ => reporting_cell.storedPoint x :: mem⟩ =
        some ⟨some (), (0, false, some y,
          (if f x y then reporting_cell.reportPoint x :: pen else pen)), fun _ => mem⟩ := by
    simp [scanStmt, hupd]

  let pushAlg (C : Type) (c : C) : resource_algorithm C :=
    { label := Unit, control := Bool, label_finite := inferInstance,
      start := (), initial := false,
      program := fun _ => .peek () (fun _ o => o.isSome)
        (.branch (fun v => v) (.push () (fun _ => c) .halt) .halt) }

  have emitTrace (f : X → Y → Bool) (q : Option Y) (pen mem : List (reporting_cell X Y)) :
      ∃ tl : List (resource_state (reporting_cell X Y) (scanAlg f).label (scanAlg f).control),
        transition_trace
            (fun c n => Turing.TM2.step (scanAlg f).program c = some n)
            (⟨some (), (0, true, q, pen), fun _ => mem⟩ :: tl) ∧
          (⟨some (), (0, true, q, pen), fun _ => mem⟩ :: tl).getLast? =
            some ⟨none, (0, true, q, []), fun _ => pen.reverse ++ mem⟩ ∧
          ((⟨some (), (0, true, q, pen), fun _ => mem⟩ :: tl).map
              (resource_step_cost (scanAlg f))).sum = 6 * pen.length + 4 := by
    induction pen generalizing mem with
    | nil =>
        refine ⟨[⟨none, (0, true, q, []), fun _ => mem⟩], ⟨?_, trivial⟩, ?_, ?_⟩
        · exact stepEmitHalt f q mem
        · simp
        · have h2 : resource_step_cost (scanAlg f)
              (⟨none, (0, true, q, []), fun _ => mem⟩ :
                resource_state (reporting_cell X Y) (scanAlg f).label (scanAlg f).control) = 0 := rfl
          rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
            costEmitHalt f q mem, h2]
          simp
    | cons c pen ih =>
        obtain ⟨tl, htr, hlast, hcost⟩ := ih (c :: mem)
        refine ⟨⟨some (), (0, true, q, pen), fun _ => c :: mem⟩ :: tl, ⟨?_, htr⟩, ?_, ?_⟩
        · exact stepEmitPush f q c pen mem
        · rw [List.getLast?_cons_cons, hlast]
          simp
        · rw [List.map_cons, List.sum_cons, hcost, costEmitPush f q c pen mem]
          simp
          ring
  have scanPointsTrace (f : X → Y → Bool) (y : Y) (l : List X) (pen : List (reporting_cell X Y)) :
      ∃ tl : List (resource_state (reporting_cell X Y) (scanAlg f).label (scanAlg f).control),
        transition_trace
            (fun c n => Turing.TM2.step (scanAlg f).program c = some n)
            (⟨some (), (0, false, some y, pen),
              fun _ => l.map reporting_cell.storedPoint⟩ :: tl) ∧
          (⟨some (), (0, false, some y, pen),
              fun _ => l.map reporting_cell.storedPoint⟩ :: tl).getLast? =
            some ⟨none, (0, true, some y, []), fun _ => pen.reverse ++
              ((l.filter (fun x => f x y)).map reporting_cell.reportPoint)⟩ ∧
          ((⟨some (), (0, false, some y, pen),
              fun _ => l.map reporting_cell.storedPoint⟩ :: tl).map
              (resource_step_cost (scanAlg f))).sum =
            4 * l.length + 6 * (l.filter (fun x => f x y)).length + 6 * pen.length + 8 := by
    induction l generalizing pen with
    | nil =>
        obtain ⟨tl, htr, hlast, hcost⟩ := emitTrace f (some y) pen []
        refine ⟨⟨some (), (0, true, some y, pen), fun _ => []⟩ :: tl, ⟨?_, ?_⟩, ?_, ?_⟩
        · exact stepScanNil f (some y) pen
        · exact htr
        · rw [List.getLast?_cons_cons]
          simpa using hlast
        · rw [List.map_cons, List.sum_cons]
          rw [show (resource_step_cost (scanAlg f)
                (⟨some (), (0, false, some y, pen), fun _ => List.map reporting_cell.storedPoint
                  (([] : List X))⟩ :
                  resource_state (reporting_cell X Y) (scanAlg f).label (scanAlg f).control)) = 4 from
                costScan f (some y) pen _]
          rw [hcost]
          simp only [List.length_nil, List.filter_nil, Nat.mul_zero]
          omega
    | cons x l ih =>
        obtain ⟨tl, htr, hlast, hcost⟩ :=
          ih (if f x y then reporting_cell.reportPoint x :: pen else pen)
        refine ⟨⟨some (), (0, false, some y,
            (if f x y then reporting_cell.reportPoint x :: pen else pen)),
            fun _ => l.map reporting_cell.storedPoint⟩ :: tl, ⟨?_, htr⟩, ?_, ?_⟩
        · exact stepScanPoint f x y pen (l.map reporting_cell.storedPoint)
        · rw [List.getLast?_cons_cons, hlast]
          by_cases hx : f x y = true <;> simp [hx]
        · rw [List.map_cons, List.sum_cons, hcost]
          rw [show (resource_step_cost (scanAlg f)
                (⟨some (), (0, false, some y, pen), fun _ => List.map reporting_cell.storedPoint
                  (x :: l)⟩ :
                  resource_state (reporting_cell X Y) (scanAlg f).label (scanAlg f).control)) = 4 from
                costScan f (some y) pen _]
          by_cases hx : f x y = true <;> simp [hx] <;> ring

  have mkExec {C : Type} (alg : resource_algorithm C) (mem : List C)
      (tl : List (resource_state C alg.label alg.control))
      (fin : resource_state C alg.label alg.control)
      (htr : transition_trace (fun c n => Turing.TM2.step alg.program c = some n)
        (resource_initial_state alg mem :: tl))
      (hlast : (resource_initial_state alg mem :: tl).getLast? = some fin)
      (hhalt : fin.l = none) :
      ∃ e : resource_execution alg mem,
        e.trace = resource_initial_state alg mem :: tl ∧ e.final_memory = fin.stk () := by
    refine ⟨{ trace := resource_initial_state alg mem :: tl,
              trace_nonempty := by simp,
              begins_at_input := by simp,
              follows_transition := htr,
              final_configuration := fin,
              ends_at_result := ?_,
              halted := hhalt,
              final_memory := fin.stk (),
              final_memory_eq := rfl }, rfl, rfl⟩
    rw [List.head?_reverse]
    exact hlast

  have execUnique {C : Type} (alg : resource_algorithm C) (mem : List C)
      (e1 e2 : resource_execution alg mem) : e1.trace = e2.trace := by
    have key : ∀ (t1 : List (resource_state C alg.label alg.control))
        (c : resource_state C alg.label alg.control)
        (t2 : List (resource_state C alg.label alg.control)),
        transition_trace (fun a b => Turing.TM2.step alg.program a = some b) (c :: t1) →
        transition_trace (fun a b => Turing.TM2.step alg.program a = some b) (c :: t2) →
        (∀ fin, (c :: t1).getLast? = some fin → fin.l = none) →
        (∀ fin, (c :: t2).getLast? = some fin → fin.l = none) → t1 = t2 := by
      intro t1
      induction t1 with
      | nil =>
          intro c t2 _ h2 hh1 _
          have hc : c.l = none := hh1 c (by simp)
          have hstep : Turing.TM2.step alg.program c = none := by
            obtain ⟨cl, cv, cs⟩ := c
            simp at hc
            subst hc
            rfl
          cases t2 with
          | nil => rfl
          | cons d t2' =>
              exact absurd (h2.1.symm.trans hstep) (by simp)
      | cons a t1' ih =>
          intro c t2 h1 h2 hh1 hh2
          cases t2 with
          | nil =>
              have hc : c.l = none := hh2 c (by simp)
              have hstep : Turing.TM2.step alg.program c = none := by
                obtain ⟨cl, cv, cs⟩ := c
                simp at hc
                subst hc
                rfl
              exact absurd (h1.1.symm.trans hstep) (by simp)
          | cons b t2' =>
              have hab : a = b := by
                have := h1.1.symm.trans h2.1
                exact Option.some.inj this
              subst hab
              have := ih a t2' h1.2 h2.2
                (by intro fin hfin; exact hh1 fin (by rw [List.getLast?_cons_cons]; exact hfin))
                (by intro fin hfin; exact hh2 fin (by rw [List.getLast?_cons_cons]; exact hfin))
              rw [this]
    obtain ⟨t1, c1, ht1⟩ : ∃ (t : List (resource_state C alg.label alg.control))
        (c : resource_state C alg.label alg.control), e1.trace = c :: t := by
      cases h : e1.trace with
      | nil => exact absurd h e1.trace_nonempty
      | cons a t => exact ⟨t, a, rfl⟩
    obtain ⟨t2, c2, ht2⟩ : ∃ (t : List (resource_state C alg.label alg.control))
        (c : resource_state C alg.label alg.control), e2.trace = c :: t := by
      cases h : e2.trace with
      | nil => exact absurd h e2.trace_nonempty
      | cons a t => exact ⟨t, a, rfl⟩
    have hc : c1 = c2 := by
      have h1 := e1.begins_at_input
      have h2 := e2.begins_at_input
      rw [ht1] at h1
      rw [ht2] at h2
      simp at h1 h2
      rw [h1, h2]
    subst hc
    rw [ht1, ht2]
    have hlast : ∀ (e : resource_execution alg mem) (t : List (resource_state C alg.label alg.control))
        (c : resource_state C alg.label alg.control), e.trace = c :: t →
        ∀ fin, (c :: t).getLast? = some fin → fin.l = none := by
      intro e t c ht fin hfin
      have h := e.ends_at_result
      rw [ht, List.head?_reverse] at h
      rw [hfin] at h
      have : fin = e.final_configuration := by
        exact Option.some.inj h
      rw [this]
      exact e.halted
    have := key t1 c1 t2 (by rw [← ht1]; exact e1.follows_transition)
      (by rw [← ht2]; exact e2.follows_transition)
      (hlast e1 t1 c1 ht1) (hlast e2 t2 c1 ht2)
    rw [this]

  have execFinalEq {C : Type} (alg : resource_algorithm C) (mem : List C)
      (e1 e2 : resource_execution alg mem) :
      e1.final_memory = e2.final_memory ∧ execution_time e1 = execution_time e2 := by
    have ht := execUnique alg mem e1 e2
    have h1 := e1.ends_at_result
    have h2 := e2.ends_at_result
    rw [ht] at h1
    have hfc : e1.final_configuration = e2.final_configuration :=
      Option.some.inj (h1.symm.trans h2)
    refine ⟨?_, ?_⟩
    · rw [← e1.final_memory_eq, ← e2.final_memory_eq, hfc]
    · unfold execution_time
      rw [ht]

  have burnScanTrace (f : X → Y → Bool) (y : Y) (l : List X) (pen : List (reporting_cell X Y)) (m : ℕ) :
      ∃ tl : List (resource_state (reporting_cell X Y) (scanAlg f).label (scanAlg f).control),
        transition_trace
            (fun c n => Turing.TM2.step (scanAlg f).program c = some n)
            (⟨some (), (m, false, some y, pen),
              fun _ => l.map reporting_cell.storedPoint⟩ :: tl) ∧
          (⟨some (), (m, false, some y, pen),
              fun _ => l.map reporting_cell.storedPoint⟩ :: tl).getLast? =
            some ⟨none, (0, true, some y, []), fun _ => pen.reverse ++
              ((l.filter (fun x => f x y)).map reporting_cell.reportPoint)⟩ ∧
          ((⟨some (), (m, false, some y, pen),
              fun _ => l.map reporting_cell.storedPoint⟩ :: tl).map
              (resource_step_cost (scanAlg f))).sum =
            3 * m + (4 * l.length + 6 * (l.filter (fun x => f x y)).length
              + 6 * pen.length + 8) := by
    induction m with
    | zero =>
        obtain ⟨tl, htr, hlast, hcost⟩ := scanPointsTrace f y l pen
        exact ⟨tl, htr, hlast, by rw [hcost]; omega⟩
    | succ m ih =>
        obtain ⟨tl, htr, hlast, hcost⟩ := ih
        refine ⟨⟨some (), (m, false, some y, pen),
            fun _ => l.map reporting_cell.storedPoint⟩ :: tl, ⟨?_, htr⟩, ?_, ?_⟩
        · exact stepBurn f m (false, some y, pen) (l.map reporting_cell.storedPoint)
        · rw [List.getLast?_cons_cons]
          exact hlast
        · rw [List.map_cons, List.sum_cons, hcost]
          rw [show (resource_step_cost (scanAlg f)
                (⟨some (), (m + 1, false, some y, pen),
                  fun _ => l.map reporting_cell.storedPoint⟩ :
                  resource_state (reporting_cell X Y) (scanAlg f).label (scanAlg f).control)) = 3 from
                costBurn f m (false, some y, pen) _]
          omega

  have stepScanCons (f : X → Y → Bool) (c : reporting_cell X Y) (q : Option Y)
      (pen mem : List (reporting_cell X Y)) :
      ∃ (m' : ℕ) (q' : Option Y) (pen' : List (reporting_cell X Y)),
        Turing.TM2.step (fun _ => scanStmt f)
            ⟨some (), (0, false, q, pen), fun _ => c :: mem⟩ =
          some ⟨some (), (m', false, q', pen'), fun _ => mem⟩ := by
    cases c with
    | storedPoint x =>
        cases q with
        | none => exact ⟨0, none, pen, by simp [scanStmt, hupd]⟩
        | some y =>
            exact ⟨0, some y, (if f x y then reporting_cell.reportPoint x :: pen else pen),
              by simpa [hupd] using stepScanPoint f x y pen mem⟩
    | query y => exact ⟨0, some y, pen, by simp [scanStmt, hupd]⟩
    | reportPoint x => exact ⟨0, q, pen, by simp [scanStmt, hupd]⟩
    | bit b => exact ⟨0, q, pen, by simp [scanStmt, hupd]⟩
    | index k => exact ⟨2 ^ (k+1), q, pen, by simp [scanStmt, hupd]⟩

  have haltsGeneral (f : X → Y → Bool) (mem : List (reporting_cell X Y)) : ∀ (m : ℕ) (q : Option Y)
      (pen : List (reporting_cell X Y)),
      ∃ (tl : List (resource_state (reporting_cell X Y) (scanAlg f).label (scanAlg f).control))
        (fin : resource_state (reporting_cell X Y) (scanAlg f).label (scanAlg f).control),
        transition_trace
            (fun c n => Turing.TM2.step (scanAlg f).program c = some n)
            (⟨some (), (m, false, q, pen), fun _ => mem⟩ :: tl) ∧
          (⟨some (), (m, false, q, pen), fun _ => mem⟩ :: tl).getLast? = some fin ∧
          fin.l = none := by
    induction mem with
    | nil =>
        intro m q pen
        induction m with
        | zero =>
            obtain ⟨tl, htr, hlast, _⟩ := emitTrace f q pen ([] : List (reporting_cell X Y))
            exact ⟨⟨some (), (0, true, q, pen), fun _ => []⟩ :: tl, _,
              ⟨stepScanNil f q pen, htr⟩, by rw [List.getLast?_cons_cons]; exact hlast, rfl⟩
        | succ m ihm =>
            obtain ⟨tl, fin, htr, hlast, hhalt⟩ := ihm
            exact ⟨⟨some (), (m, false, q, pen), fun _ => []⟩ :: tl, fin,
              ⟨stepBurn f m (false, q, pen) [], htr⟩,
              by rw [List.getLast?_cons_cons]; exact hlast, hhalt⟩
    | cons c mem ih =>
        intro m q pen
        induction m with
        | zero =>
            obtain ⟨m', q', pen', hstep⟩ := stepScanCons f c q pen mem
            obtain ⟨tl, fin, htr, hlast, hhalt⟩ := ih m' q' pen'
            exact ⟨⟨some (), (m', false, q', pen'), fun _ => mem⟩ :: tl, fin,
              ⟨hstep, htr⟩, by rw [List.getLast?_cons_cons]; exact hlast, hhalt⟩
        | succ m ihm =>
            obtain ⟨tl, fin, htr, hlast, hhalt⟩ := ihm
            exact ⟨⟨some (), (m, false, q, pen), fun _ => c :: mem⟩ :: tl, fin,
              ⟨stepBurn f m (false, q, pen) (c :: mem), htr⟩,
              by rw [List.getLast?_cons_cons]; exact hlast, hhalt⟩

  have queryExecAny (f : X → Y → Bool) (st : List (reporting_cell X Y)) (y : Y) :
      Nonempty (resource_execution (scanAlg f) (query_input_cells st y)) := by
    obtain ⟨tl, fin, htr, hlast, hhalt⟩ := haltsGeneral f (query_input_cells st y) 0 none []
    obtain ⟨e, _, _⟩ := mkExec (scanAlg f) (query_input_cells st y) tl fin htr hlast hhalt
    exact ⟨e⟩

  have queryExecIndex (f : X → Y → Bool) (y : Y) (k : ℕ) (l : List X) :
      ∃ e : resource_execution (scanAlg f)
          (query_input_cells (reporting_cell.index k :: l.map reporting_cell.storedPoint) y),
        e.final_memory = (l.filter (fun x => f x y)).map reporting_cell.reportPoint ∧
        execution_time e = 8 + 3 * 2 ^ (k+1) +
          (4 * l.length + 6 * (l.filter (fun x => f x y)).length + 8) := by
    obtain ⟨tl, htr, hlast, hcost⟩ := burnScanTrace f y l [] (2 ^ (k+1))
    obtain ⟨e, hetr, hemem⟩ := mkExec (scanAlg f)
      (query_input_cells (reporting_cell.index k :: l.map reporting_cell.storedPoint) y)
      (⟨some (), (0, false, some y, []),
          fun _ => reporting_cell.index k :: l.map reporting_cell.storedPoint⟩ ::
        ⟨some (), (2 ^ (k+1), false, some y, []),
          fun _ => l.map reporting_cell.storedPoint⟩ :: tl)
      ⟨none, (0, true, some y, []),
        fun _ => ([] : List (reporting_cell X Y)).reverse ++
          ((l.filter (fun x => f x y)).map reporting_cell.reportPoint)⟩
      ⟨stepScanQuery f y none [] (reporting_cell.index k :: l.map reporting_cell.storedPoint),
        stepScanIndex f k (some y) [] (l.map reporting_cell.storedPoint), htr⟩
      (by rw [List.getLast?_cons_cons, List.getLast?_cons_cons]; exact hlast) rfl
    refine ⟨e, ?_, ?_⟩
    · rw [hemem]; simp
    · rw [execution_time, hetr, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, hcost]
      rw [show (resource_step_cost (scanAlg f)
            (resource_initial_state (scanAlg f)
              (query_input_cells (reporting_cell.index k :: l.map reporting_cell.storedPoint) y))) = 4
          from costScan f none [] _]
      rw [show (resource_step_cost (scanAlg f)
            (⟨some (), (0, false, some y, []),
              fun _ => reporting_cell.index k :: l.map reporting_cell.storedPoint⟩ :
              resource_state (reporting_cell X Y) (scanAlg f).label (scanAlg f).control)) = 4
          from costScan f (some y) [] _]
      simp only [List.length_nil, Nat.mul_zero]
      omega

  have queryExecPlain (f : X → Y → Bool) (y : Y) (l : List X) :
      ∃ e : resource_execution (scanAlg f)
          (query_input_cells (l.map reporting_cell.storedPoint) y),
        e.final_memory = (l.filter (fun x => f x y)).map reporting_cell.reportPoint ∧
        execution_time e = 4 +
          (4 * l.length + 6 * (l.filter (fun x => f x y)).length + 8) := by
    obtain ⟨tl, htr, hlast, hcost⟩ := scanPointsTrace f y l []
    obtain ⟨e, hetr, hemem⟩ := mkExec (scanAlg f)
      (query_input_cells (l.map reporting_cell.storedPoint) y)
      (⟨some (), (0, false, some y, []), fun _ => l.map reporting_cell.storedPoint⟩ :: tl)
      ⟨none, (0, true, some y, []),
        fun _ => ([] : List (reporting_cell X Y)).reverse ++
          ((l.filter (fun x => f x y)).map reporting_cell.reportPoint)⟩
      ⟨stepScanQuery f y none [] (l.map reporting_cell.storedPoint), htr⟩
      (by rw [List.getLast?_cons_cons]; exact hlast) rfl
    refine ⟨e, ?_, ?_⟩
    · rw [hemem]; simp
    · rw [execution_time, hetr, List.map_cons, List.sum_cons, hcost]
      rw [show (resource_step_cost (scanAlg f)
            (resource_initial_state (scanAlg f)
              (query_input_cells (l.map reporting_cell.storedPoint) y))) = 4
          from costScan f none [] _]
      simp

  have trivExec (C : Type) (mem : List C) :
      ∃ e : resource_execution (trivAlg C) mem,
        e.final_memory = mem ∧ execution_time e = 1 ∧ execution_space e = mem.length := by
    obtain ⟨e, hetr, hemem⟩ := mkExec (trivAlg C) mem
      [⟨none, (), fun _ => mem⟩] ⟨none, (), fun _ => mem⟩ ⟨rfl, trivial⟩ rfl rfl
    refine ⟨e, hemem, ?_, ?_⟩
    · rw [execution_time, hetr]
      simp [resource_step_cost, resource_statement_cost, trivAlg, resource_initial_state]
    · rw [execution_space, hetr]
      simp [execution_trace_space, resource_configuration_space, resource_initial_state]

  have pushExecNil (C : Type) (c : C) :
      ∃ e : resource_execution (pushAlg C c) [],
        e.final_memory = [] ∧ execution_time e = 3 ∧ execution_space e = 0 := by
    obtain ⟨e, hetr, hemem⟩ := mkExec (pushAlg C c) []
      [⟨none, false, fun _ => []⟩] ⟨none, false, fun _ => []⟩
      ⟨by simp [pushAlg, resource_initial_state], trivial⟩ rfl rfl
    refine ⟨e, hemem, ?_, ?_⟩
    · rw [execution_time, hetr]
      simp [resource_step_cost, resource_statement_cost, pushAlg, resource_initial_state]
    · rw [execution_space, hetr]
      simp [execution_trace_space, resource_configuration_space, resource_initial_state]

  have pushExecCons (C : Type) (c a : C) (mem : List C) :
      ∃ e : resource_execution (pushAlg C c) (a :: mem),
        e.final_memory = c :: a :: mem ∧ execution_time e = 4 ∧
          execution_space e = mem.length + 2 := by
    obtain ⟨e, hetr, hemem⟩ := mkExec (pushAlg C c) (a :: mem)
      [⟨none, true, fun _ => c :: a :: mem⟩] ⟨none, true, fun _ => c :: a :: mem⟩
      ⟨by simp [pushAlg, resource_initial_state, hupd], trivial⟩ rfl rfl
    refine ⟨e, hemem, ?_, ?_⟩
    · rw [execution_time, hetr]
      simp [resource_step_cost, resource_statement_cost, pushAlg, resource_initial_state]
    · rw [execution_space, hetr]
      simp [execution_trace_space, resource_configuration_space, resource_initial_state]

  have reportedFilter (f : X → Y → Bool) (D : Finset X) (y : Y) :
      reported_points ((D.1.toList.filter (fun x => f x y)).map
          (reporting_cell.reportPoint : X → reporting_cell X Y)) =
        matching_report f D y := by
    classical
    have h1 : ((D.1.toList.filter (fun x => f x y)).map
        (reporting_cell.reportPoint : X → reporting_cell X Y)).filterMap
        (fun c => match c with
          | reporting_cell.reportPoint value => some value
          | _ => none) = D.1.toList.filter (fun x => f x y) := by
      induction D.1.toList with
      | nil => simp
      | cons a l ih =>
          by_cases ha : f a y = true
          · simp [ha, ih]
          · simp [ha, ih]
    refine Finset.ext (fun x => ?_)
    rw [reported_points]
    rw [h1]
    rw [List.mem_toFinset, List.mem_filter, matching_report, Finset.mem_filter,
      Multiset.mem_toList, ← Finset.mem_def]

  have reportedNone (D : Finset X) (y : Y) :
      reported_points (reporting_cell.query y :: D.1.toList.map
        (reporting_cell.storedPoint : X → reporting_cell X Y)) = (∅ : Finset X) := by
    have h1 : (reporting_cell.query y :: D.1.toList.map
        (reporting_cell.storedPoint : X → reporting_cell X Y)).filterMap
        (fun c => match c with
          | reporting_cell.reportPoint value => some value
          | _ => none) = [] := by
      simp only [List.filterMap_cons]
      induction D.1.toList with
      | nil => simp
      | cons a l ih => simpa using ih
    rw [reported_points, h1]
    simp

  have inputCellsLength (D : Finset X) :
      (preprocessing_input_cells D : List (reporting_cell X Y)).length = D.card := by
    rw [preprocessing_input_cells, List.length_map, Multiset.length_toList]
    rfl

  have pmfTsumToReal {S : Type} (p : PMF S) : ∑' s, (p s).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun a => PMF.apply_ne_top _ _)]
    simp [PMF.tsum_coe]

  have tsumPMFconst {S : Type} (p : PMF S) (c : ℝ) : ∑' s, (p s).toReal * c = c := by
    rw [tsum_mul_right, pmfTsumToReal, one_mul]

  have tsumPure {X : Type} (x : X) (p : PMF X) (h1 : p x = 1)
      (h0 : ∀ x', x' ≠ x → p x' = 0) (g : X → ℝ) :
      ∑' x', (p x').toReal * g x' = g x := by
    rw [tsum_eq_single x (fun b hb => by simp [h0 b hb])]
    simp [h1]

  have pureExists {X : Type} (x : X) :
      ∃ p : PMF X, p x = 1 ∧ ∀ x', x' ≠ x → p x' = 0 := by
    classical
    refine ⟨⟨fun x' => if x' = x then 1 else 0, ?_⟩, ?_, ?_⟩
    · have h : ∑' x' : X, (if x' = x then (1 : ENNReal) else 0) = 1 := tsum_ite_eq x 1
      have h2 := ENNReal.summable.hasSum (f := fun x' : X => if x' = x then (1 : ENNReal) else 0)
      rwa [h] at h2
    · show (if x = x then (1 : ENNReal) else 0) = 1
      simp
    · intro x' hx'
      show (if x' = x then (1 : ENNReal) else 0) = 0
      simp [hx']

  have caseBKey (f : X → Y → Bool) (protocol : specialized_protocol X Y) (ε : ℝ)
      (hrun : ∀ (d : PMF X) (x : X) (y : Y) (m : protocol.advice) (R : protocol.public_coin)
        (r : protocol.private_coin), communication_tree_run protocol.tree d x y m R r = true)
      (hfp : protocol_has_false_positive_error protocol f ε) :
      (∀ x y, f x y = true) ∨ 1 ≤ ε := by
    by_cases hall : ∀ x y, f x y = true
    · exact Or.inl hall
    · right
      obtain ⟨x, hx⟩ := not_forall.mp hall
      obtain ⟨y, hxy⟩ := not_forall.mp hx
      have hxy' : f x y = false := by
        cases hf : f x y with
        | false => rfl
        | true => exact absurd hf hxy
      obtain ⟨p, hp1, hp0⟩ := pureExists x
      have h := hfp.2 p y
      have hcalc : protocol_false_positive_probability protocol f p y = 1 := by
        unfold protocol_false_positive_probability
        simp only [hrun, and_true]
        rw [tsumPure x p hp1 hp0 (fun x' => ∑' publicCoin, (protocol.public_coin_distribution publicCoin).toReal *
          ∑' privateCoin, (protocol.private_coin_distribution privateCoin).toReal *
            if f x' y = false then (1 : ℝ) else 0)]
        rw [tsumPMFconst, tsumPMFconst, hxy']
        simp
      rw [hcalc] at h
      exact h

  have treeConst {A P Q : Type} :
      ∀ (t : communication_tree X Y A P Q),
        (∀ (d : PMF X) (x : X) (y : Y) (m : A) (R : P) (r : Q),
          (communication_tree_resources t d x y m R r).alice_bits = 0 ∧
          (communication_tree_resources t d x y m R r).bob_bits = 0 ∧
          (communication_tree_resources t d x y m R r).carol_bits = 0 ∧
          (communication_tree_resources t d x y m R r).merlin_bits = 0) →
        ∀ (d₁ : PMF X) (x₁ : X) (y₁ : Y) (m₁ : A) (R₁ : P) (r₁ : Q)
          (d₂ : PMF X) (x₂ : X) (y₂ : Y) (m₂ : A) (R₂ : P) (r₂ : Q),
          communication_tree_run t d₁ x₁ y₁ m₁ R₁ r₁ =
            communication_tree_run t d₂ x₂ y₂ m₂ R₂ r₂ := by
    intro t
    induction t with
    | output v => intro _ _ _ _ _ _ _ _ _ _ _ _ _; rfl
    | alice bits time msg next ih =>
        intro h d₁ x₁ y₁ m₁ R₁ r₁ d₂ x₂ y₂ m₂ R₂ r₂
        have hb : bits = 0 := by
          have h1 := (h d₁ x₁ y₁ m₁ R₁ r₁).1
          have h2 : (communication_tree_resources
              (communication_tree.alice bits time msg next) d₁ x₁ y₁ m₁ R₁ r₁).alice_bits =
              bits + (communication_tree_resources (next (msg d₁ x₁))
                d₁ x₁ y₁ m₁ R₁ r₁).alice_bits := rfl
          omega
        subst hb
        haveI : Subsingleton (Fin (2 ^ 0)) := by simp; infer_instance
        have hsub : ∀ (d : PMF X) (x : X), next (msg d x) = next (msg d₁ x₁) := by
          intro d x
          rw [Subsingleton.elim (msg d x) (msg d₁ x₁)]
        have hrun : ∀ (d : PMF X) (x : X) (y : Y) (m : A) (R : P) (r : Q),
            communication_tree_run (communication_tree.alice 0 time msg next) d x y m R r =
              communication_tree_run (next (msg d x)) d x y m R r := fun _ _ _ _ _ _ => rfl
        rw [hrun, hrun, hsub d₁ x₁, hsub d₂ x₂]
        refine ih (msg d₁ x₁) ?_ d₁ x₁ y₁ m₁ R₁ r₁ d₂ x₂ y₂ m₂ R₂ r₂
        intro d x y m R r
        have h4 := h d x y m R r
        have e1 : (communication_tree_resources
            (communication_tree.alice 0 time msg next) d x y m R r).alice_bits =
            0 + (communication_tree_resources (next (msg d x)) d x y m R r).alice_bits := rfl
        have e2 : (communication_tree_resources
            (communication_tree.alice 0 time msg next) d x y m R r).bob_bits =
            (communication_tree_resources (next (msg d x)) d x y m R r).bob_bits := rfl
        have e3 : (communication_tree_resources
            (communication_tree.alice 0 time msg next) d x y m R r).carol_bits =
            (communication_tree_resources (next (msg d x)) d x y m R r).carol_bits := rfl
        have e4 : (communication_tree_resources
            (communication_tree.alice 0 time msg next) d x y m R r).merlin_bits =
            (communication_tree_resources (next (msg d x)) d x y m R r).merlin_bits := rfl
        rw [e1, e2, e3, e4, hsub d x] at h4
        omega
    | bob bits time msg next ih =>
        intro h d₁ x₁ y₁ m₁ R₁ r₁ d₂ x₂ y₂ m₂ R₂ r₂
        have hb : bits = 0 := by
          have h1 := (h d₁ x₁ y₁ m₁ R₁ r₁).2.1
          have h2 : (communication_tree_resources
              (communication_tree.bob bits time msg next) d₁ x₁ y₁ m₁ R₁ r₁).bob_bits =
              bits + (communication_tree_resources (next (msg y₁))
                d₁ x₁ y₁ m₁ R₁ r₁).bob_bits := rfl
          omega
        subst hb
        haveI : Subsingleton (Fin (2 ^ 0)) := by simp; infer_instance
        have hsub : ∀ (y : Y), next (msg y) = next (msg y₁) := by
          intro y
          rw [Subsingleton.elim (msg y) (msg y₁)]
        have hrun : ∀ (d : PMF X) (x : X) (y : Y) (m : A) (R : P) (r : Q),
            communication_tree_run (communication_tree.bob 0 time msg next) d x y m R r =
              communication_tree_run (next (msg y)) d x y m R r := fun _ _ _ _ _ _ => rfl
        rw [hrun, hrun, hsub y₁, hsub y₂]
        refine ih (msg y₁) ?_ d₁ x₁ y₁ m₁ R₁ r₁ d₂ x₂ y₂ m₂ R₂ r₂
        intro d x y m R r
        have h4 := h d x y m R r
        have e1 : (communication_tree_resources
            (communication_tree.bob 0 time msg next) d x y m R r).alice_bits =
            (communication_tree_resources (next (msg y)) d x y m R r).alice_bits := rfl
        have e2 : (communication_tree_resources
            (communication_tree.bob 0 time msg next) d x y m R r).bob_bits =
            0 + (communication_tree_resources (next (msg y)) d x y m R r).bob_bits := rfl
        have e3 : (communication_tree_resources
            (communication_tree.bob 0 time msg next) d x y m R r).carol_bits =
            (communication_tree_resources (next (msg y)) d x y m R r).carol_bits := rfl
        have e4 : (communication_tree_resources
            (communication_tree.bob 0 time msg next) d x y m R r).merlin_bits =
            (communication_tree_resources (next (msg y)) d x y m R r).merlin_bits := rfl
        rw [e1, e2, e3, e4, hsub y] at h4
        omega
    | merlin bits msg next ih =>
        intro h d₁ x₁ y₁ m₁ R₁ r₁ d₂ x₂ y₂ m₂ R₂ r₂
        have hb : bits = 0 := by
          have h1 := (h d₁ x₁ y₁ m₁ R₁ r₁).2.2.2
          have h2 : (communication_tree_resources
              (communication_tree.merlin bits msg next) d₁ x₁ y₁ m₁ R₁ r₁).merlin_bits =
              bits + (communication_tree_resources (next (msg m₁))
                d₁ x₁ y₁ m₁ R₁ r₁).merlin_bits := rfl
          omega
        subst hb
        haveI : Subsingleton (Fin (2 ^ 0)) := by simp; infer_instance
        have hsub : ∀ (m : A), next (msg m) = next (msg m₁) := by
          intro m
          rw [Subsingleton.elim (msg m) (msg m₁)]
        have hrun : ∀ (d : PMF X) (x : X) (y : Y) (m : A) (R : P) (r : Q),
            communication_tree_run (communication_tree.merlin 0 msg next) d x y m R r =
              communication_tree_run (next (msg m)) d x y m R r := fun _ _ _ _ _ _ => rfl
        rw [hrun, hrun, hsub m₁, hsub m₂]
        refine ih (msg m₁) ?_ d₁ x₁ y₁ m₁ R₁ r₁ d₂ x₂ y₂ m₂ R₂ r₂
        intro d x y m R r
        have h4 := h d x y m R r
        have e1 : (communication_tree_resources
            (communication_tree.merlin 0 msg next) d x y m R r).alice_bits =
            (communication_tree_resources (next (msg m)) d x y m R r).alice_bits := rfl
        have e2 : (communication_tree_resources
            (communication_tree.merlin 0 msg next) d x y m R r).bob_bits =
            (communication_tree_resources (next (msg m)) d x y m R r).bob_bits := rfl
        have e3 : (communication_tree_resources
            (communication_tree.merlin 0 msg next) d x y m R r).carol_bits =
            (communication_tree_resources (next (msg m)) d x y m R r).carol_bits := rfl
        have e4 : (communication_tree_resources
            (communication_tree.merlin 0 msg next) d x y m R r).merlin_bits =
            0 + (communication_tree_resources (next (msg m)) d x y m R r).merlin_bits := rfl
        rw [e1, e2, e3, e4, hsub m] at h4
        omega
    | carol bits time msg next ih =>
        intro h d₁ x₁ y₁ m₁ R₁ r₁ d₂ x₂ y₂ m₂ R₂ r₂
        have hb : bits = 0 := by
          have h1 := (h d₁ x₁ y₁ m₁ R₁ r₁).2.2.1
          have h2 : (communication_tree_resources
              (communication_tree.carol bits time msg next) d₁ x₁ y₁ m₁ R₁ r₁).carol_bits =
              bits + (communication_tree_resources (next (msg d₁ R₁ r₁))
                d₁ x₁ y₁ m₁ R₁ r₁).carol_bits := rfl
          omega
        subst hb
        haveI : Subsingleton (Fin (2 ^ 0)) := by simp; infer_instance
        have hsub : ∀ (d : PMF X) (R : P) (r : Q), next (msg d R r) = next (msg d₁ R₁ r₁) := by
          intro d R r
          rw [Subsingleton.elim (msg d R r) (msg d₁ R₁ r₁)]
        have hrun : ∀ (d : PMF X) (x : X) (y : Y) (m : A) (R : P) (r : Q),
            communication_tree_run (communication_tree.carol 0 time msg next) d x y m R r =
              communication_tree_run (next (msg d R r)) d x y m R r := fun _ _ _ _ _ _ => rfl
        rw [hrun, hrun, hsub d₁ R₁ r₁, hsub d₂ R₂ r₂]
        refine ih (msg d₁ R₁ r₁) ?_ d₁ x₁ y₁ m₁ R₁ r₁ d₂ x₂ y₂ m₂ R₂ r₂
        intro d x y m R r
        have h4 := h d x y m R r
        have e1 : (communication_tree_resources
            (communication_tree.carol 0 time msg next) d x y m R r).alice_bits =
            (communication_tree_resources (next (msg d R r)) d x y m R r).alice_bits := rfl
        have e2 : (communication_tree_resources
            (communication_tree.carol 0 time msg next) d x y m R r).bob_bits =
            (communication_tree_resources (next (msg d R r)) d x y m R r).bob_bits := rfl
        have e3 : (communication_tree_resources
            (communication_tree.carol 0 time msg next) d x y m R r).carol_bits =
            0 + (communication_tree_resources (next (msg d R r)) d x y m R r).carol_bits := rfl
        have e4 : (communication_tree_resources
            (communication_tree.carol 0 time msg next) d x y m R r).merlin_bits =
            (communication_tree_resources (next (msg d R r)) d x y m R r).merlin_bits := rfl
        rw [e1, e2, e3, e4, hsub d R r] at h4
        omega

  have filterLenCard (f : X → Y → Bool) (D : Finset X) (y : Y) :
      (D.1.toList.filter (fun x => f x y)).length = report_count f D y := by
    classical
    rw [report_count, matching_report, Finset.card, Finset.filter_val]
    conv_rhs => rw [← Multiset.coe_toList D.1]
    rw [← Multiset.countP_eq_card_filter, Multiset.coe_countP, List.countP_eq_length_filter]
    simp

  have mainCase1 (constants : reduction_constants)
      (c_a c_b c_c c_m t_a t_b t_c : ℕ) (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
      (hslack : 12 ≤ constants.additive_slack)
      (hfalse : ∀ x y, f x y = false) :
      Nonempty (protocol_reduction_witness constants f c_a c_b c_c c_m t_a t_b t_c ε δ) := by
    classical
    obtain ⟨sp, hsp1, hsp0⟩ := pureExists (0 : ℕ)
    have hpre : ∀ (D : Finset X) (k : ℕ),
        ∃ e : resource_execution (trivAlg (reporting_cell X Y)) (preprocessing_input_cells D),
          e.final_memory = preprocessing_input_cells D ∧ execution_time e = 1 ∧
            execution_space e = D.card := by
      intro D k
      obtain ⟨e, h1, h2, h3⟩ := trivExec (reporting_cell X Y) (preprocessing_input_cells D)
      exact ⟨e, h1, h2, by rw [h3, inputCellsLength]⟩
    choose pre hmem htime hspace using hpre
    have hq : ∀ (st : List (reporting_cell X Y)) (y : Y),
        ∃ e : resource_execution (trivAlg (reporting_cell X Y)) (query_input_cells st y),
          e.final_memory = query_input_cells st y ∧ execution_time e = 1 := by
      intro st y
      obtain ⟨e, h1, h2, _⟩ := trivExec (reporting_cell X Y) (query_input_cells st y)
      exact ⟨e, h1, h2⟩
    choose qf hqmem hqtime using hq
    refine ⟨{ data_structure :=
      { seed := ℕ, seed_distribution := sp,
        preprocess_algorithm := fun _ => trivAlg (reporting_cell X Y),
        preprocess := pre,
        query_algorithm := trivAlg (reporting_cell X Y),
        query := qf }, guarantees := ⟨?_, ?_, ?_, ?_⟩ }⟩
    · intro D k y
      dsimp only
      rw [hqmem, hmem]
      rw [query_input_cells, preprocessing_input_cells]
      rw [reportedNone]
      rw [matching_report]
      refine (Finset.filter_eq_empty_iff.mpr ?_).symm
      intro x _
      rw [hfalse x y]
      exact Bool.false_ne_true
    · intro D k
      dsimp only
      rw [hspace]
      have hp : 0 < exponential_overhead constants.space_exponent (c_a + c_b + c_m) := by
        rw [exponential_overhead]; positivity
      calc D.card ≤ D.card + c_c := Nat.le_add_right _ _
        _ ≤ exponential_overhead constants.space_exponent (c_a + c_b + c_m) * (D.card + c_c) := by
            exact Nat.le_mul_of_pos_left _ hp
    · intro D k
      dsimp only
      rw [htime]
      omega
    · intro D y
      have hexp : expected_query_time
          { seed := ℕ, seed_distribution := sp,
            preprocess_algorithm := fun _ => trivAlg (reporting_cell X Y),
            preprocess := pre,
            query_algorithm := trivAlg (reporting_cell X Y),
            query := qf : reporting_data_structure X Y } D y = 1 := by
        rw [expected_query_time]
        dsimp only
        rw [tsum_congr (fun k => by rw [hqtime ((pre D k).final_memory) y]; norm_num :
          ∀ k, (sp k).toReal * ((execution_time (qf ((pre D k).final_memory) y) : ℕ) : ℝ)
            = (sp k).toReal * 1)]
        rw [tsumPMFconst]
      rw [hexp, query_upper_bound]
      have h1 : (0 : ℝ) ≤ (exponential_overhead constants.query_exponent (c_a + c_m) : ℝ) *
          (↑(c_a + c_b + c_m + c_c + t_b) : ℝ) := by positivity
      have h2 : (0 : ℝ) ≤ (constants.false_positive_factor : ℝ) * ε * (D.card : ℝ) := by positivity
      have h3 : (0 : ℝ) ≤ (exponential_overhead constants.soundness_exponent c_m : ℝ) * δ *
          (D.card : ℝ) := by positivity
      have h4 : (0 : ℝ) ≤ (constants.output_factor : ℝ) * ((report_count f D y : ℕ) : ℝ) := by
        positivity
      have h5 : (12 : ℝ) ≤ (constants.additive_slack : ℝ) := by exact_mod_cast hslack
      linarith

  have mainCase2a (constants : reduction_constants)
      (c_a c_b c_c c_m t_a t_b t_c : ℕ) (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
      (hslack : 12 ≤ constants.additive_slack)
      (hKs : 1 ≤ constants.space_exponent)
      (hc : 1 ≤ c_a + c_b + c_c + c_m) :
      Nonempty (protocol_reduction_witness constants f c_a c_b c_c c_m t_a t_b t_c ε δ) := by
    classical
    let qtot : ∀ (st : List (reporting_cell X Y)) (y : Y),
        resource_execution (scanAlg f) (query_input_cells st y) :=
      fun st y => (queryExecAny f st y).some
    have hplain : ∀ (l : List X) (m : List (reporting_cell X Y)) (y : Y),
        m = l.map reporting_cell.storedPoint →
        (qtot m y).final_memory = (l.filter (fun x => f x y)).map reporting_cell.reportPoint ∧
        execution_time (qtot m y) =
          4 + (4 * l.length + 6 * (l.filter (fun x => f x y)).length + 8) := by
      intro l m y hml
      subst hml
      obtain ⟨e0, hm0, ht0⟩ := queryExecPlain f y l
      obtain ⟨hfm, htm⟩ := execFinalEq (scanAlg f)
        (query_input_cells (l.map reporting_cell.storedPoint) y)
        (qtot (l.map reporting_cell.storedPoint) y) e0
      exact ⟨by rw [hfm, hm0], by rw [htm, ht0]⟩
    have hindex : ∀ (l : List X) (k : ℕ) (m : List (reporting_cell X Y)) (y : Y),
        m = reporting_cell.index k :: l.map reporting_cell.storedPoint →
        (qtot m y).final_memory = (l.filter (fun x => f x y)).map reporting_cell.reportPoint ∧
        execution_time (qtot m y) = 8 + 3 * 2 ^ (k + 1) +
          (4 * l.length + 6 * (l.filter (fun x => f x y)).length + 8) := by
      intro l k m y hml
      subst hml
      obtain ⟨e0, hm0, ht0⟩ := queryExecIndex f y k l
      obtain ⟨hfm, htm⟩ := execFinalEq (scanAlg f)
        (query_input_cells (reporting_cell.index k :: l.map reporting_cell.storedPoint) y)
        (qtot (reporting_cell.index k :: l.map reporting_cell.storedPoint) y) e0
      exact ⟨by rw [hfm, hm0], by rw [htm, ht0]⟩
    have key : ∀ (D : Finset X) (k : ℕ),
        ∃ e : resource_execution (pushAlg (reporting_cell X Y) (reporting_cell.index k))
            (preprocessing_input_cells D),
          execution_time e ≤ 4 ∧
          execution_space e ≤ exponential_overhead constants.space_exponent (c_a + c_b + c_m) *
            (D.card + c_c) ∧
          ∀ y : Y,
            (qtot e.final_memory y).final_memory =
              (D.1.toList.filter (fun x => f x y)).map reporting_cell.reportPoint ∧
            (D.card = 0 → execution_time (qtot e.final_memory y) = 12) ∧
            (D.card ≠ 0 → 3 * 2 ^ (k + 1) ≤ execution_time (qtot e.final_memory y)) := by
      intro D k
      rcases hL : D.1.toList with _ | ⟨a, L⟩
      · have hn : D.card = 0 := by
          rw [show D.card = D.1.toList.length from (Multiset.length_toList D.1).symm, hL]; rfl
        rw [preprocessing_input_cells, hL, hn]
        simp only [List.map_nil]
        obtain ⟨e, hm, ht, hs⟩ := pushExecNil (reporting_cell X Y) (reporting_cell.index k)
        refine ⟨e, by omega, by rw [hs]; exact Nat.zero_le _, ?_⟩
        intro y
        rw [hm]
        obtain ⟨hfm, htm⟩ := hplain [] [] y rfl
        refine ⟨by rw [hfm], ?_, ?_⟩
        · intro _; rw [htm]; simp
        · intro h; exact absurd rfl h
      · have hn : D.card = L.length + 1 := by
          rw [show D.card = D.1.toList.length from (Multiset.length_toList D.1).symm, hL]; rfl
        rw [preprocessing_input_cells, hL, hn]
        simp only [List.map_cons]
        obtain ⟨e, hm, ht, hs⟩ := pushExecCons (reporting_cell X Y) (reporting_cell.index k)
          (reporting_cell.storedPoint a) (L.map reporting_cell.storedPoint)
        refine ⟨e, by omega, ?_, ?_⟩
        · rw [hs, List.length_map]
          rcases Nat.eq_zero_or_pos c_c with hcc | hcc
          · subst hcc
            have h1 : 0 < c_a + c_b + c_m := by omega
            have h2 : 2 ≤ exponential_overhead constants.space_exponent (c_a + c_b + c_m) := by
              rw [exponential_overhead]
              calc (2 : ℕ) = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ (constants.space_exponent * (c_a + c_b + c_m)) :=
                    Nat.pow_le_pow_right (by norm_num) (Nat.mul_pos hKs h1)
            calc L.length + 2 ≤ 2 * (L.length + 1 + 0) := by omega
              _ ≤ exponential_overhead constants.space_exponent (c_a + c_b + c_m) *
                  (L.length + 1 + 0) := Nat.mul_le_mul_right _ h2
          · have h1 : 1 ≤ exponential_overhead constants.space_exponent (c_a + c_b + c_m) := by
              rw [exponential_overhead]; exact Nat.one_le_two_pow
            calc L.length + 2 ≤ 1 * (L.length + 1 + c_c) := by omega
              _ ≤ exponential_overhead constants.space_exponent (c_a + c_b + c_m) *
                  (L.length + 1 + c_c) := Nat.mul_le_mul_right _ h1
        · intro y
          rw [hm]
          obtain ⟨hfm, htm⟩ := hindex (a :: L) k
            (reporting_cell.index k :: reporting_cell.storedPoint a ::
              L.map reporting_cell.storedPoint) y rfl
          refine ⟨by rw [hfm], ?_, ?_⟩
          · intro h; exact absurd h (by omega)
          · intro _; rw [htm]; omega
    choose pre hptime hpspace hqall using key
    let DS : reporting_data_structure X Y :=
      { seed := ℕ, seed_distribution := geoPMF,
        preprocess_algorithm := fun k => pushAlg (reporting_cell X Y) (reporting_cell.index k),
        preprocess := pre,
        query_algorithm := scanAlg f,
        query := qtot }
    refine ⟨{ data_structure := DS, guarantees := ⟨?_, ?_, ?_, ?_⟩ }⟩
    · intro D k y
      show reported_points ((qtot (pre D k).final_memory y).final_memory) = matching_report f D y
      rw [(hqall D k y).1]
      exact reportedFilter f D y
    · intro D k
      exact hpspace D k
    · intro D k
      exact le_trans (hptime D k) (le_trans (by omega) (Nat.le_add_left _ _))
    · intro D y
      have hgeo : ∀ k : ℕ, (geoPMF k).toReal = ((2 : ℝ)⁻¹) ^ (k + 1) := by
        intro k
        have h0 : (geoPMF k) = (2⁻¹ : ENNReal) ^ (k + 1) := hgeoval k
        rw [h0, ENNReal.toReal_pow]
        norm_num
      have h1 : (0 : ℝ) ≤ (exponential_overhead constants.query_exponent (c_a + c_m) : ℝ) *
          (↑(c_a + c_b + c_m + c_c + t_b) : ℝ) := by positivity
      have h2 : (0 : ℝ) ≤ (constants.false_positive_factor : ℝ) * ε * (D.card : ℝ) := by positivity
      have h3 : (0 : ℝ) ≤ (exponential_overhead constants.soundness_exponent c_m : ℝ) * δ *
          (D.card : ℝ) := by positivity
      have h4 : (0 : ℝ) ≤ (constants.output_factor : ℝ) * ((report_count f D y : ℕ) : ℝ) := by
        positivity
      have h5 : (12 : ℝ) ≤ (constants.additive_slack : ℝ) := by exact_mod_cast hslack
      by_cases hD : D.card = 0
      · have hny : report_count f D y = 0 := by
          have hle := Finset.card_filter_le D (fun x => f x y = true)
          rw [report_count, matching_report]
          omega
        show (∑' k : ℕ, (geoPMF k).toReal *
          (execution_time (qtot (pre D k).final_memory y) : ℝ)) ≤
            query_upper_bound constants c_a c_b c_c c_m t_b D.card (report_count f D y) ε δ
        rw [tsum_congr (fun k : ℕ => by rw [(hqall D k y).2.1 hD] :
          ∀ k : ℕ, (geoPMF k).toReal * (execution_time (qtot (pre D k).final_memory y) : ℝ)
            = (geoPMF k).toReal * ((12 : ℕ) : ℝ))]
        rw [tsumPMFconst, query_upper_bound, hny, hD]
        push_cast at h1 ⊢
        linarith
      · have hterm : ∀ k : ℕ, (3 : ℝ) ≤ (geoPMF k).toReal *
            (execution_time (qtot (pre D k).final_memory y) : ℝ) := by
          intro k
          have hb := (hqall D k y).2.2 hD
          have hb' : ((3 * 2 ^ (k + 1) : ℕ) : ℝ) ≤
              ((execution_time (qtot (pre D k).final_memory y) : ℕ) : ℝ) := Nat.cast_le.mpr hb
          push_cast at hb'
          rw [hgeo k]
          have hp : (0 : ℝ) < ((2 : ℝ)⁻¹) ^ (k + 1) := by positivity
          have hcalc : ((2 : ℝ)⁻¹) ^ (k + 1) * (3 * 2 ^ (k + 1)) = 3 := by
            rw [inv_pow]; field_simp
          calc (3 : ℝ) = ((2 : ℝ)⁻¹) ^ (k + 1) * (3 * 2 ^ (k + 1)) := hcalc.symm
            _ ≤ ((2 : ℝ)⁻¹) ^ (k + 1) *
                (execution_time (qtot (pre D k).final_memory y) : ℝ) :=
                mul_le_mul_of_nonneg_left hb' hp.le
        have hns : ¬ Summable (fun k : ℕ => (geoPMF k).toReal *
            (execution_time (qtot (pre D k).final_memory y) : ℝ)) := by
          intro hs
          have hlim := hs.tendsto_atTop_zero
          have hge := ge_of_tendsto hlim (Filter.Eventually.of_forall hterm)
          linarith
        show (∑' k : ℕ, (geoPMF k).toReal *
          (execution_time (qtot (pre D k).final_memory y) : ℝ)) ≤
            query_upper_bound constants c_a c_b c_c c_m t_b D.card (report_count f D y) ε δ
        rw [tsum_eq_zero_of_not_summable hns, query_upper_bound]
        linarith

  have mainCase2b (constants : reduction_constants)
      (c_a c_b c_c c_m t_a t_b t_c : ℕ) (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
      (hslack : 12 ≤ constants.additive_slack)
      (hKe : 4 ≤ constants.false_positive_factor)
      (hKo : 10 ≤ constants.output_factor)
      (hkey : (∀ x y, f x y = true) ∨ 1 ≤ ε) :
      Nonempty (protocol_reduction_witness constants f c_a c_b c_c c_m t_a t_b t_c ε δ) := by
    classical
    let qtot : ∀ (st : List (reporting_cell X Y)) (y : Y),
        resource_execution (scanAlg f) (query_input_cells st y) :=
      fun st y => (queryExecAny f st y).some
    have hplain : ∀ (l : List X) (m : List (reporting_cell X Y)) (y : Y),
        m = l.map reporting_cell.storedPoint →
        (qtot m y).final_memory = (l.filter (fun x => f x y)).map reporting_cell.reportPoint ∧
        execution_time (qtot m y) =
          4 + (4 * l.length + 6 * (l.filter (fun x => f x y)).length + 8) := by
      intro l m y hml
      subst hml
      obtain ⟨e0, hm0, ht0⟩ := queryExecPlain f y l
      obtain ⟨hfm, htm⟩ := execFinalEq (scanAlg f)
        (query_input_cells (l.map reporting_cell.storedPoint) y)
        (qtot (l.map reporting_cell.storedPoint) y) e0
      exact ⟨by rw [hfm, hm0], by rw [htm, ht0]⟩
    have key : ∀ (D : Finset X) (k : ℕ),
        ∃ e : resource_execution (trivAlg (reporting_cell X Y)) (preprocessing_input_cells D),
          execution_time e = 1 ∧ execution_space e = D.card ∧
            e.final_memory = preprocessing_input_cells D := by
      intro D k
      obtain ⟨e, h1, h2, h3⟩ := trivExec (reporting_cell X Y) (preprocessing_input_cells D)
      exact ⟨e, h2, by rw [h3, inputCellsLength], h1⟩
    choose pre hptime hpspace hpmem using key
    have hqfacts : ∀ (D : Finset X) (y : Y),
        (qtot (preprocessing_input_cells D) y).final_memory =
          (D.1.toList.filter (fun x => f x y)).map reporting_cell.reportPoint ∧
        execution_time (qtot (preprocessing_input_cells D) y) =
          4 * D.card + 6 * report_count f D y + 12 := by
      intro D y
      obtain ⟨hfm, htm⟩ := hplain D.1.toList (preprocessing_input_cells D) y rfl
      refine ⟨hfm, ?_⟩
      rw [htm, ← filterLenCard f D y]
      have hcard : D.card = D.1.toList.length := (Multiset.length_toList D.1).symm
      omega
    let DS : reporting_data_structure X Y :=
      { seed := ℕ, seed_distribution := geoPMF,
        preprocess_algorithm := fun _ => trivAlg (reporting_cell X Y),
        preprocess := pre,
        query_algorithm := scanAlg f,
        query := qtot }
    refine ⟨{ data_structure := DS, guarantees := ⟨?_, ?_, ?_, ?_⟩ }⟩
    · intro D k y
      show reported_points ((qtot (pre D k).final_memory y).final_memory) = matching_report f D y
      rw [hpmem D k, (hqfacts D y).1]
      exact reportedFilter f D y
    · intro D k
      show execution_space (pre D k) ≤
        exponential_overhead constants.space_exponent (c_a + c_b + c_m) * (D.card + c_c)
      rw [hpspace D k]
      have h1 : 1 ≤ exponential_overhead constants.space_exponent (c_a + c_b + c_m) := by
        rw [exponential_overhead]; exact Nat.one_le_two_pow
      calc D.card ≤ 1 * (D.card + c_c) := by omega
        _ ≤ exponential_overhead constants.space_exponent (c_a + c_b + c_m) * (D.card + c_c) :=
            Nat.mul_le_mul_right _ h1
    · intro D k
      exact le_trans (le_of_eq (hptime D k)) (le_trans (by omega) (Nat.le_add_left _ _))
    · intro D y
      have hn0 : (0 : ℝ) ≤ (D.card : ℝ) := Nat.cast_nonneg _
      have hny0 : (0 : ℝ) ≤ ((report_count f D y : ℕ) : ℝ) := Nat.cast_nonneg _
      have hexp : (∑' k : ℕ, (geoPMF k).toReal *
          (execution_time (qtot (pre D k).final_memory y) : ℝ)) =
          4 * (D.card : ℝ) + 6 * ((report_count f D y : ℕ) : ℝ) + 12 := by
        rw [tsum_congr (fun k : ℕ => by rw [hpmem D k, (hqfacts D y).2] :
          ∀ k : ℕ, (geoPMF k).toReal * (execution_time (qtot (pre D k).final_memory y) : ℝ)
            = (geoPMF k).toReal * ((4 * D.card + 6 * report_count f D y + 12 : ℕ) : ℝ))]
        rw [tsumPMFconst]
        push_cast
        ring
      show (∑' k : ℕ, (geoPMF k).toReal *
        (execution_time (qtot (pre D k).final_memory y) : ℝ)) ≤
          query_upper_bound constants c_a c_b c_c c_m t_b D.card (report_count f D y) ε δ
      rw [hexp, query_upper_bound]
      have h1 : (0 : ℝ) ≤ (exponential_overhead constants.query_exponent (c_a + c_m) : ℝ) *
          (↑(c_a + c_b + c_m + c_c + t_b) : ℝ) := by positivity
      have h3 : (0 : ℝ) ≤ (exponential_overhead constants.soundness_exponent c_m : ℝ) * δ *
          (D.card : ℝ) := by positivity
      have hKc : (12 : ℝ) ≤ (constants.additive_slack : ℝ) := by exact_mod_cast hslack
      have hKo' : (10 : ℝ) ≤ (constants.output_factor : ℝ) := by exact_mod_cast hKo
      rcases hkey with hall | hone
      · have hny : report_count f D y = D.card := by
          rw [report_count, matching_report, Finset.filter_true_of_mem (fun x _ => hall x y)]
        have h2 : (0 : ℝ) ≤ (constants.false_positive_factor : ℝ) * ε * (D.card : ℝ) := by positivity
        rw [hny]
        have h7 : 10 * (D.card : ℝ) ≤ (constants.output_factor : ℝ) * (D.card : ℝ) :=
          mul_le_mul_of_nonneg_right hKo' hn0
        linarith
      · have hKe' : (4 : ℝ) ≤ (constants.false_positive_factor : ℝ) := by exact_mod_cast hKe
        have h4 : (4 : ℝ) ≤ (constants.false_positive_factor : ℝ) * ε := by nlinarith
        have h2 : (4 : ℝ) * (D.card : ℝ) ≤
            (constants.false_positive_factor : ℝ) * ε * (D.card : ℝ) :=
          mul_le_mul_of_nonneg_right h4 hn0
        have h6 : 6 * ((report_count f D y : ℕ) : ℝ) ≤
            (constants.output_factor : ℝ) * ((report_count f D y : ℕ) : ℝ) := by
          have h8 : (6 : ℝ) ≤ (constants.output_factor : ℝ) := by linarith
          exact mul_le_mul_of_nonneg_right h8 hny0
        linarith

  by_cases hfalse : ∀ x y, f x y = false
  · exact mainCase1 constants c_a c_b c_c c_m t_a t_b t_c ε δ hfp.1 hsound.1 hs1 hfalse
  · by_cases hc : 1 ≤ c_a + c_b + c_c + c_m
    · exact mainCase2a constants c_a c_b c_c c_m t_a t_b t_c ε δ hfp.1 hsound.1
        hs1 hs2 hc
    · have hza : c_a = 0 := by omega
      have hzb : c_b = 0 := by omega
      have hzc : c_c = 0 := by omega
      have hzm : c_m = 0 := by omega
      have hres : ∀ (d : PMF X) (x : X) (y : Y) (m : protocol.advice)
          (R : protocol.public_coin) (r : protocol.private_coin),
          (communication_tree_resources protocol.tree d x y m R r).alice_bits = 0 ∧
          (communication_tree_resources protocol.tree d x y m R r).bob_bits = 0 ∧
          (communication_tree_resources protocol.tree d x y m R r).carol_bits = 0 ∧
          (communication_tree_resources protocol.tree d x y m R r).merlin_bits = 0 := by
        intro d x y m R r
        obtain ⟨ha, hb, hcc, hm, -, -, -⟩ := hcost d x y m R r
        omega
      have htc := treeConst protocol.tree hres
      obtain ⟨x0, hx0⟩ := not_forall.mp hfalse
      obtain ⟨y0, hxy0⟩ := not_forall.mp hx0
      have hx0y0 : f x0 y0 = true := by
        cases hf : f x0 y0 with
        | true => rfl
        | false => exact absurd hf hxy0
      obtain ⟨R0, hR0⟩ := protocol.public_coin_distribution.support_nonempty
      obtain ⟨r0, hr0⟩ := protocol.private_coin_distribution.support_nonempty
      obtain ⟨p0, hp1, hp0⟩ := pureExists x0
      have hinst := htype p0 x0 y0 R0 r0 (by rw [hp1]; exact one_ne_zero) hx0y0
      have hrun : ∀ (d : PMF X) (x : X) (y : Y) (m : protocol.advice)
          (R : protocol.public_coin) (r : protocol.private_coin),
          communication_tree_run protocol.tree d x y m R r = true := by
        intro d x y m R r
        rw [htc d x y m R r p0 x0 y0 (protocol.special_advice p0 x0 y0 R0) R0 r0]
        exact hinst
      exact mainCase2b constants c_a c_b c_c c_m t_a t_b t_c ε δ hfp.1 hsound.1
        hs1 hs3 hs4 (caseBKey f protocol ε hrun hfp)

@[blueprint "thm:reduction-communication-protocols-data-structures"
  (statement := /-- There is one record of positive absolute constants, chosen independently of all input domains, functions, protocols, resource bounds, and error parameters, with the following property.  Let $f:X\times Y\to\{0,1\}$.  If there exists a protocol $\pi$ in the specialized product-distributional communication model with soundness $\delta$, type-I false-positive error $\epsilon$ under its unique distinguished Merlin advice, $(c_a,c_b,c_c,c_m)$-cost, and $(t_a,t_b,t_c)$-time, then there is a randomized data structure whose persistent state is a finite list of atomic point and control cells and whose preprocessing and query algorithms are finite-program stack machines with data-bearing control states.  The control may retain an inspected stored point and the query value, and hence may construct the corresponding report-point cell without restricting the input domains to finite types.  Every executed push, peek, pop, control update, selected branch, jump, and halt is charged separately, including operations evaluated inside one Mathlib machine step; preprocessing starts from exactly the dataset's point cells, querying starts from exactly one topmost query cell followed by the persistent state, and the returned report is exactly the set of explicitly emitted report-point cells.  Its preprocessing execution on every finite dataset $\mathcal D\subset X$ has certified resident space
  \[
  2^{O(c_a+c_b+c_m)}\bigl(|\mathcal D|+c_c\bigr)
  \]
  and certified preprocessing primitive-instruction cost
  \[
  2^{O(c_a+c_b+c_m)}|\mathcal D|(t_a+t_b+t_c)+O(1),
  \]
  where the final summand is one absolute constant, independent of the dataset and of all cost, time, and error parameters, charging machine initialization and halting.
  Given $y\in Y$, its query execution outputs exactly the $x\in\mathcal D$ satisfying $f(x,y)=1$, and its expected certified primitive-instruction cost is
  \[
  2^{O(c_a+c_m)}(c_a+c_b+c_m+c_c+t_b)
  +O(\epsilon|\mathcal D|)
  +2^{O(c_m)}\delta|\mathcal D|
  +O(n_y)+O(1),
  \]
  where $n_y$ is the number of reported points and the final summand is the same absolute constant, charging initialization, inspection of the topmost query cell, and halting of the corresponding stack machine. -/)
  (proof := /-- Apply \cref{lem:transcript-tree-reduction}.  First take the single positive record of constants supplied there.  For arbitrary input domains, target function, specialized protocol, resource bounds, and error parameters satisfying the four stated hypotheses, apply the uniform property of that record.  The resulting nonempty reduction-witness type contains a randomized reporting data structure implemented by the instrumented stack-machine semantics; its guarantee field gives exact reporting and the stated space, preprocessing-time, and expected-query-time inequalities.  Taking its data-structure field supplies the required existential witness without making the previously chosen constants depend on the instance. -/)
  (title := /-- Reduction from communication protocols to data structures -/)
  (latexEnv := "theorem")]
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
              c_a c_b c_c c_m t_a t_b t_c ε δ := by
  obtain ⟨constants, hconstants⟩ := transcript_tree_reduction
  refine ⟨constants, ?_⟩
  intro X Y f protocol c_a c_b c_c c_m t_a t_b t_c ε δ hcost hfalse htype hsound
  obtain ⟨witness⟩ :=
    hconstants f protocol c_a c_b c_c c_m t_a t_b t_c ε δ hcost hfalse htype hsound
  exact ⟨witness.data_structure, witness.guarantees⟩

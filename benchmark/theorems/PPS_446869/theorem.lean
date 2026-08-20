import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Computability.TuringMachine.PostTuringMachine

set_option linter.all false
set_option maxHeartbeats 500000

universe u v

structure encoded_graph_path_decomposition where
  bags : List (List ℕ)
  width : ℕ

def encoded_graph_path_decomposition_valid (n : ℕ) (R : ℕ → ℕ → Prop)
    (D : encoded_graph_path_decomposition) : Prop :=
  D.bags.length ≤ (n + 1) ^ 4 ∧
  (∀ B ∈ D.bags, B.Nodup ∧ ∀ v ∈ B, v < n) ∧
  (∀ v, v < n → ∃ i : Fin D.bags.length, v ∈ D.bags.get i) ∧
  (∀ v w, v < n → w < n → R v w →
    ∃ i : Fin D.bags.length, v ∈ D.bags.get i ∧ w ∈ D.bags.get i) ∧
  (∀ v (i j k : Fin D.bags.length), i ≤ j → j ≤ k →
    v ∈ D.bags.get i → v ∈ D.bags.get k → v ∈ D.bags.get j) ∧
  ∀ i : Fin D.bags.length, (D.bags.get i).toFinset.card ≤ D.width + 1

structure encoded_list_coloring_input where
  vertexCount : ℕ
  colorCount : ℕ
  edges : List (ℕ × ℕ)
  allowed : List (List ℕ)

def encoded_list_coloring_input_valid (X : encoded_list_coloring_input) : Prop :=
  X.allowed.length = X.vertexCount ∧
  X.colorCount ≤ X.vertexCount ^ 2 ∧ X.edges.Nodup ∧
  (∀ e ∈ X.edges, e.1 < X.vertexCount ∧ e.2 < X.vertexCount) ∧
  ∀ L ∈ X.allowed,
    L.Nodup ∧ L.length ≤ X.vertexCount ∧ ∀ c ∈ L, c < X.colorCount

def encoded_list_coloring_is_colorable (X : encoded_list_coloring_input) : Prop :=
  ∃ coloring : ℕ → ℕ,
    (∀ v, v < X.vertexCount →
      coloring v < X.colorCount ∧ coloring v ∈ X.allowed.getD v []) ∧
    ∀ e ∈ X.edges, coloring e.1 ≠ coloring e.2

def encoded_list_coloring_adjacency (X : encoded_list_coloring_input)
    (v w : ℕ) : Prop :=
  v ≠ w ∧ ((v, w) ∈ X.edges ∨ (w, v) ∈ X.edges)

structure encoded_decomposed_list_coloring_input where
  problem : encoded_list_coloring_input
  decomposition : encoded_graph_path_decomposition

def encoded_decomposed_list_coloring_input_valid
    (X : encoded_decomposed_list_coloring_input) : Prop :=
  encoded_list_coloring_input_valid X.problem ∧
    encoded_graph_path_decomposition_valid X.problem.vertexCount
      (encoded_list_coloring_adjacency X.problem) X.decomposition

structure encoded_three_cnf_input where
  variableCount : ℕ
  clauses : List (List (ℕ × Bool))

def encoded_three_cnf_input_valid (X : encoded_three_cnf_input) : Prop :=
  X.clauses.Nodup ∧ ∀ c ∈ X.clauses,
    c.Nodup ∧ c.length ≤ 3 ∧ ∀ l ∈ c, l.1 < X.variableCount

def encoded_three_cnf_is_satisfiable (X : encoded_three_cnf_input) : Prop :=
  ∃ assignment : ℕ → Bool, ∀ c ∈ X.clauses,
    ∃ l ∈ c, assignment l.1 = l.2

def encoded_three_cnf_adjacency (X : encoded_three_cnf_input) (v w : ℕ) : Prop :=
  v ≠ w ∧ ∃ c ∈ X.clauses,
    (∃ sv, (v, sv) ∈ c) ∧ ∃ sw, (w, sw) ∈ c

structure encoded_decomposed_three_cnf_input where
  formula : encoded_three_cnf_input
  decomposition : encoded_graph_path_decomposition

def encoded_decomposed_three_cnf_input_valid
    (X : encoded_decomposed_three_cnf_input) : Prop :=
  encoded_three_cnf_input_valid X.formula ∧
    encoded_graph_path_decomposition_valid X.formula.variableCount
      (encoded_three_cnf_adjacency X.formula) X.decomposition

def fixed_binary_encoding (n : ℕ) : List Bool :=
  List.replicate n true ++ [false]

def fixed_list_encoding {X : Type u} (encode : X → List Bool)
    (xs : List X) : List Bool :=
  fixed_binary_encoding xs.length ++
    xs.flatMap fun x => fixed_binary_encoding (encode x).length ++ encode x

def encoded_graph_path_decomposition_binary_encoding
    (D : encoded_graph_path_decomposition) : List Bool :=
  fixed_list_encoding (fixed_list_encoding fixed_binary_encoding) D.bags ++
    fixed_binary_encoding D.width

def encoded_list_coloring_input_binary_encoding
    (X : encoded_list_coloring_input) : List Bool :=
  fixed_binary_encoding X.vertexCount ++ fixed_binary_encoding X.colorCount ++
    fixed_list_encoding
      (fun e : ℕ × ℕ =>
        fixed_binary_encoding e.1 ++ fixed_binary_encoding e.2) X.edges ++
    fixed_list_encoding (fixed_list_encoding fixed_binary_encoding) X.allowed

def encoded_decomposed_list_coloring_input_binary_encoding
    (X : encoded_decomposed_list_coloring_input) : List Bool :=
  encoded_list_coloring_input_binary_encoding X.problem ++
    encoded_graph_path_decomposition_binary_encoding X.decomposition

def encoded_three_cnf_input_binary_encoding
    (X : encoded_three_cnf_input) : List Bool :=
  fixed_binary_encoding X.variableCount ++
    fixed_list_encoding
      (fixed_list_encoding fun l : ℕ × Bool =>
        fixed_binary_encoding l.1 ++ [l.2]) X.clauses

def encoded_decomposed_three_cnf_input_binary_encoding
    (X : encoded_decomposed_three_cnf_input) : List Bool :=
  encoded_three_cnf_input_binary_encoding X.formula ++
    encoded_graph_path_decomposition_binary_encoding X.decomposition

structure timed_decision_procedure where
  stateCount : ℕ
  machine :
    Turing.TM0.Machine (Option Bool) (Fin (stateCount + 1))

def timed_decision_procedure_configuration_after
    (A : timed_decision_procedure) (input : List Bool) :
    ℕ → Option (Turing.TM0.Cfg (Option Bool) (Fin (A.stateCount + 1)))
  | 0 => some (Turing.TM0.init (input.map some))
  | k + 1 => (timed_decision_procedure_configuration_after A input k).bind
      (Turing.TM0.step A.machine)

def timed_decision_procedure_halts_with_in (A : timed_decision_procedure)
    (input : List Bool) (answer : Bool) (steps : ℕ) : Prop :=
  ∃ cfg, timed_decision_procedure_configuration_after A input steps = some cfg ∧
    Turing.TM0.step A.machine cfg = none ∧ cfg.Tape.head = some answer

def decision_procedure_solves_on {X : Type u} (A : timed_decision_procedure)
    (encoding : X → List Bool) (P eligible : X → Prop) : Prop :=
  ∀ x, eligible x → ∃ steps answer,
    timed_decision_procedure_halts_with_in A (encoding x)
      answer steps ∧ (answer = true ↔ P x)

def decision_procedure_runs_in_time_on {X : Type u}
    (A : timed_decision_procedure) (encoding : X → List Bool)
    (size : X → ℕ) (eligible : X → Prop) (bound : X → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ x,
    eligible x → n₀ ≤ size x → ∃ steps answer,
      timed_decision_procedure_halts_with_in A (encoding x)
        answer steps ∧ (steps : ℝ) ≤ C * bound x

def primal_pathwidth_seth : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 2 → ∀ c : ℕ,
    ∀ A : timed_decision_procedure,
      ¬(decision_procedure_solves_on A
          encoded_decomposed_three_cnf_input_binary_encoding
          (fun X => encoded_three_cnf_is_satisfiable X.formula)
          encoded_decomposed_three_cnf_input_valid ∧
        decision_procedure_runs_in_time_on A
          encoded_decomposed_three_cnf_input_binary_encoding
          (fun X => X.formula.variableCount)
          encoded_decomposed_three_cnf_input_valid
          (fun X =>
            Real.rpow (2 - ε) (X.decomposition.width : ℝ) *
              (X.formula.variableCount : ℝ) ^ c))

def fixed_width_list_coloring_speedup : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ p : ℕ, 4 < p ∧
    ∃ A : timed_decision_procedure,
      decision_procedure_solves_on A
        encoded_decomposed_list_coloring_input_binary_encoding
        (fun X => encoded_list_coloring_is_colorable X.problem)
        (fun X => encoded_decomposed_list_coloring_input_valid X ∧
          X.decomposition.width = p) ∧
      decision_procedure_runs_in_time_on A
        encoded_decomposed_list_coloring_input_binary_encoding
        (fun X => X.problem.vertexCount)
        (fun X => encoded_decomposed_list_coloring_input_valid X ∧
          X.decomposition.width = p)
        (fun X =>
          Real.rpow (X.problem.vertexCount : ℝ)
            ((p : ℝ) - 4 - ε))

def uniform_pathwidth_list_coloring_speedup : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ p₀ : ℕ, 0 < p₀ ∧
    ∃ A : timed_decision_procedure,
      decision_procedure_solves_on A
        encoded_decomposed_list_coloring_input_binary_encoding
        (fun X => encoded_list_coloring_is_colorable X.problem)
        encoded_decomposed_list_coloring_input_valid ∧
      ∀ p : ℕ, p₀ < p →
        decision_procedure_runs_in_time_on A
          encoded_decomposed_list_coloring_input_binary_encoding
          (fun X => X.problem.vertexCount)
          (fun X => encoded_decomposed_list_coloring_input_valid X ∧
            X.decomposition.width = p)
          (fun X =>
            Real.rpow (X.problem.vertexCount : ℝ)
              ((1 - ε) * p))

theorem lc :
    ((¬ primal_pathwidth_seth) ↔ fixed_width_list_coloring_speedup) ∧
      (fixed_width_list_coloring_speedup ↔
        uniform_pathwidth_list_coloring_speedup) := by sorry

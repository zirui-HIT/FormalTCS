import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Computability.TuringMachine.Computable

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators

inductive advice_csp_kind where
  | maxCut
  | max2Lin

structure unweighted_two_lin_instance where
  kind : advice_csp_kind
  numVariables : ℕ
  numConstraints : ℕ
  variables_pos : 0 < numVariables
  leftEndpoint : Fin numConstraints → Fin numVariables
  rightEndpoint : Fin numConstraints → Fin numVariables
  endpoints_ne : ∀ e, leftEndpoint e ≠ rightEndpoint e
  parity : Fin numConstraints → Bool
  constraints_unique :
    ∀ (e f : Fin numConstraints), parity e = parity f →
      ((leftEndpoint e = leftEndpoint f ∧ rightEndpoint e = rightEndpoint f) ∨
        (leftEndpoint e = rightEndpoint f ∧ rightEndpoint e = leftEndpoint f)) →
      e = f
  maxCutParity : kind = advice_csp_kind.maxCut → ∀ e, parity e = true

def unweighted_two_lin_constraint_satisfied
    (I : unweighted_two_lin_instance)
    (x : Fin I.numVariables → Bool)
    (e : Fin I.numConstraints) : Prop :=
  (x (I.leftEndpoint e) = x (I.rightEndpoint e)) ↔ I.parity e = false

noncomputable def unweighted_two_lin_value
    (I : unweighted_two_lin_instance)
    (x : Fin I.numVariables → Bool) : ℕ := by
  classical
  exact
    (Finset.univ.filter fun e => unweighted_two_lin_constraint_satisfied I x e).card

noncomputable def unweighted_two_lin_optimal_value (I : unweighted_two_lin_instance) : ℕ :=
  Finset.sup Finset.univ (unweighted_two_lin_value I)

noncomputable def unweighted_two_lin_optimal_value_real
    (I : unweighted_two_lin_instance) : ℝ :=
  (unweighted_two_lin_optimal_value I : ℝ)

def unweighted_two_lin_is_optimal
    (I : unweighted_two_lin_instance)
    (xStar : Fin I.numVariables → Bool) : Prop :=
  unweighted_two_lin_value I xStar = unweighted_two_lin_optimal_value I

noncomputable def unweighted_two_lin_average_degree
    (I : unweighted_two_lin_instance) : ℝ :=
  (2 * (I.numConstraints : ℝ)) / (I.numVariables : ℝ)

noncomputable def label_advice_coordinate_weight
    (epsilon : ℝ) (truth advised : Bool) : ℝ :=
  if advised = truth then (1 + epsilon) / 2 else (1 - epsilon) / 2

noncomputable def label_advice_vector_weight
    (I : unweighted_two_lin_instance)
    (xStar advised : Fin I.numVariables → Bool)
    (epsilon : ℝ) : ℝ :=
  ∏ i, label_advice_coordinate_weight epsilon (xStar i) (advised i)

structure label_advice_input where
  cspInstance : unweighted_two_lin_instance
  advised : Fin cspInstance.numVariables → Bool

def label_advice_encode_nat (r : ℕ) : List Bool :=
  List.replicate r false ++ [true]

def label_advice_instance_encoding (I : unweighted_two_lin_instance) : List Bool :=
  (match I.kind with
    | advice_csp_kind.maxCut => [false]
    | advice_csp_kind.max2Lin => [true]) ++
  label_advice_encode_nat I.numVariables ++
  label_advice_encode_nat I.numConstraints ++
  (List.ofFn fun e : Fin I.numConstraints =>
    label_advice_encode_nat (I.leftEndpoint e).val ++
    label_advice_encode_nat (I.rightEndpoint e).val ++
    [I.parity e]).flatten

def label_advice_input_encoding (input : label_advice_input) : List Bool :=
  label_advice_instance_encoding input.cspInstance ++ List.ofFn input.advised

def label_advice_output_encoding (output : List Bool) : List Bool :=
  output

structure label_advice_algorithm where
  solve : label_advice_input → List Bool

def label_advice_execution (A : label_advice_algorithm) :=
  Turing.TM2ComputableInPolyTime
    label_advice_input_encoding label_advice_output_encoding A.solve

def label_advice_polynomial_time (A : label_advice_algorithm) : Prop :=
  Nonempty (label_advice_execution A)

def label_advice_output_assignment
    (I : unweighted_two_lin_instance) (output : List Bool) :
    Fin I.numVariables → Bool :=
  fun i => output.getD i.val false

noncomputable def label_advice_expected_value
    (A : label_advice_algorithm)
    (I : unweighted_two_lin_instance)
    (xStar : Fin I.numVariables → Bool)
    (epsilon : ℝ) : ℝ :=
  ∑ advised : Fin I.numVariables → Bool,
    label_advice_vector_weight I xStar advised epsilon *
      (unweighted_two_lin_value I
        (label_advice_output_assignment I (A.solve ⟨I, advised⟩)) : ℝ)

def unweighted_max_qp_solver_contract
    (maxQPSolver : ℝ → label_advice_algorithm) : Prop :=
  ∃ (K : ℝ), 0 ≤ K ∧
    ∀ (epsilon : ℝ), 0 < epsilon → epsilon ≤ 1 →
      label_advice_polynomial_time (maxQPSolver epsilon) ∧
      ∀ (I : unweighted_two_lin_instance)
        (xStar : Fin I.numVariables → Bool),
        unweighted_two_lin_is_optimal I xStar →
        label_advice_expected_value (maxQPSolver epsilon) I xStar epsilon ≥
          unweighted_two_lin_optimal_value_real I -
            (K / epsilon) *
              Real.sqrt ((I.numVariables : ℝ) * (I.numConstraints : ℝ))

theorem max_two_lin_unweighted_label_advice
    (maxQPSolver : ℝ → label_advice_algorithm)
    (hMaxQP : unweighted_max_qp_solver_contract maxQPSolver)
    : ∃ (C : ℝ), 0 ≤ C ∧
      ∀ (epsilon : ℝ), 0 < epsilon → epsilon ≤ 1 →
        ∃ A : label_advice_algorithm,
          label_advice_polynomial_time A ∧
          ∀ (I : unweighted_two_lin_instance)
            (xStar : Fin I.numVariables → Bool),
            unweighted_two_lin_is_optimal I xStar →
            label_advice_expected_value A I xStar epsilon ≥
              (1 - C /
                (epsilon * Real.sqrt (unweighted_two_lin_average_degree I))) *
                  unweighted_two_lin_optimal_value_real I := by sorry

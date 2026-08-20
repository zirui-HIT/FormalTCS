import Architect
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Computability.TuringMachine.Computable

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators

@[blueprint "def:advice-csp-kind"
  (statement := /-- The two problem classes under consideration are Max Cut and Boolean Max \(2\)-Lin. -/)
  (title := /-- Problem Kind -/)
  (latexEnv := "definition")]
inductive advice_csp_kind where
  | maxCut
  | max2Lin

@[blueprint "def:unweighted-two-lin-instance"
  (statement := /-- An unweighted Boolean Max \(2\)-Lin instance consists of \(n>0\) variables, \(m\) loopless binary constraints, and a prescribed parity for each constraint. A constraint of parity \(\mathsf{false}\) requires equal endpoint labels, whereas one of parity \(\mathsf{true}\) requires unequal endpoint labels. The constraint set is simple as a signed undirected graph: two constraints having the same parity and the same unordered pair of endpoints have the same index. An instance declared to be Max Cut has parity \(\mathsf{true}\) on every constraint. -/)
  (title := /-- Unweighted Max Cut and Max \(2\)-Lin Instances -/)
  (latexEnv := "definition")]
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

@[blueprint "def:unweighted-two-lin-constraint-satisfied"
  (statement := /-- For an instance \(I\), an assignment \(x\), and a constraint \(e\), the predicate \(\operatorname{Sat}_I(x,e)\) holds precisely when the endpoint labels are equal if and only if the prescribed parity is \(\mathsf{false}\). -/)
  (title := /-- Satisfaction of a Binary Constraint -/)
  (latexEnv := "definition")]
def unweighted_two_lin_constraint_satisfied
    (I : unweighted_two_lin_instance)
    (x : Fin I.numVariables → Bool)
    (e : Fin I.numConstraints) : Prop :=
  (x (I.leftEndpoint e) = x (I.rightEndpoint e)) ↔ I.parity e = false

@[blueprint "def:unweighted-two-lin-value"
  (statement := /-- The value \(\operatorname{val}_I(x)\) of an assignment is the number of constraints of \(I\) that it satisfies. -/)
  (title := /-- Value of an Assignment -/)
  (latexEnv := "definition")]
noncomputable def unweighted_two_lin_value
    (I : unweighted_two_lin_instance)
    (x : Fin I.numVariables → Bool) : ℕ := by
  classical
  exact
    (Finset.univ.filter fun e => unweighted_two_lin_constraint_satisfied I x e).card

@[blueprint "def:unweighted-two-lin-optimal-value"
  (statement := /-- The optimum \(\operatorname{OPT}(I)\) is the maximum, over all Boolean assignments, of the number of satisfied constraints. -/)
  (title := /-- Optimal Value -/)
  (latexEnv := "definition")]
noncomputable def unweighted_two_lin_optimal_value (I : unweighted_two_lin_instance) : ℕ :=
  Finset.sup Finset.univ (unweighted_two_lin_value I)

@[blueprint "def:unweighted-two-lin-optimal-value-real"
  (statement := /-- The real-valued optimum \(\operatorname{OPT}_{\mathbb R}(I)\) is the natural optimum regarded as a real number. -/)
  (title := /-- Real-Valued Optimal Value -/)
  (latexEnv := "definition")]
noncomputable def unweighted_two_lin_optimal_value_real
    (I : unweighted_two_lin_instance) : ℝ :=
  (unweighted_two_lin_optimal_value I : ℝ)

@[blueprint "def:unweighted-two-lin-is-optimal"
  (statement := /-- An assignment \(x^\ast\) is optimal for \(I\) when its value equals \(\operatorname{OPT}(I)\). -/)
  (title := /-- Optimal Assignments -/)
  (latexEnv := "definition")]
def unweighted_two_lin_is_optimal
    (I : unweighted_two_lin_instance)
    (xStar : Fin I.numVariables → Bool) : Prop :=
  unweighted_two_lin_value I xStar = unweighted_two_lin_optimal_value I

@[blueprint "def:unweighted-two-lin-average-degree"
  (statement := /-- For an unweighted instance with \(n\) variables and \(m\) constraints, its average degree is \(\Delta(I)=2m/n\). -/)
  (title := /-- Average Degree -/)
  (latexEnv := "definition")]
noncomputable def unweighted_two_lin_average_degree
    (I : unweighted_two_lin_instance) : ℝ :=
  (2 * (I.numConstraints : ℝ)) / (I.numVariables : ℝ)

@[blueprint "def:label-advice-coordinate-weight"
  (statement := /-- Given \(0<\varepsilon\leq 1\), an optimal label \(x_i^\ast\), and an advised label \(\widetilde x_i\), the coordinate weight is \((1+\varepsilon)/2\) when the labels agree and \((1-\varepsilon)/2\) when they disagree. -/)
  (title := /-- Coordinate Law of Label Advice -/)
  (latexEnv := "definition")]
noncomputable def label_advice_coordinate_weight
    (epsilon : ℝ) (truth advised : Bool) : ℝ :=
  if advised = truth then (1 + epsilon) / 2 else (1 - epsilon) / 2

@[blueprint "def:label-advice-vector-weight"
  (statement := /-- The probability weight of an advice vector \(\widetilde x\) is the product of its coordinate weights. Thus the coordinates are independent, and each agrees with \(x^\ast\) with probability \((1+\varepsilon)/2\). -/)
  (title := /-- Product Law of Label Advice -/)
  (latexEnv := "definition")]
noncomputable def label_advice_vector_weight
    (I : unweighted_two_lin_instance)
    (xStar advised : Fin I.numVariables → Bool)
    (epsilon : ℝ) : ℝ :=
  ∏ i, label_advice_coordinate_weight epsilon (xStar i) (advised i)

@[blueprint "def:label-advice-input"
  (statement := /-- A Label Advice input is a pair \((I,\widetilde x)\), where \(I\) is an unweighted Max Cut or Max \(2\)-Lin instance and \(\widetilde x\) assigns one advised Boolean label to each variable of \(I\). -/)
  (title := /-- Inputs to a Label Advice Algorithm -/)
  (latexEnv := "definition")]
structure label_advice_input where
  cspInstance : unweighted_two_lin_instance
  advised : Fin cspInstance.numVariables → Bool

@[blueprint "def:label-advice-encode-nat"
  (statement := /-- The self-delimiting unary encoding of a natural number \(r\) is the word consisting of \(r\) false bits followed by one true bit. -/)
  (title := /-- Unary Encoding of Natural Numbers -/)
  (latexEnv := "definition")]
def label_advice_encode_nat (r : ℕ) : List Bool :=
  List.replicate r false ++ [true]

@[blueprint "def:label-advice-instance-encoding"
  (statement := /-- The encoding of an unweighted instance records its problem kind, numbers of variables and constraints, and, for every constraint in index order, the unary encodings of its two endpoints followed by its parity bit. This is a finite binary word determined by all computational data of the instance. -/)
  (title := /-- Encoding of Unweighted Instances -/)
  (latexEnv := "definition")]
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

@[blueprint "def:label-advice-input-encoding"
  (statement := /-- The binary encoding of a Label Advice input concatenates the encoding of its instance with the advised labels in variable-index order. -/)
  (title := /-- Encoding of Label Advice Inputs -/)
  (latexEnv := "definition")]
def label_advice_input_encoding (input : label_advice_input) : List Bool :=
  label_advice_instance_encoding input.cspInstance ++ List.ofFn input.advised

@[blueprint "def:label-advice-output-encoding"
  (statement := /-- A solver output is already a binary word, and its machine encoding is therefore the identity encoding. -/)
  (title := /-- Encoding of Solver Outputs -/)
  (latexEnv := "definition")]
def label_advice_output_encoding (output : List Bool) : List Bool :=
  output

@[blueprint "def:label-advice-algorithm"
  (statement := /-- A Label Advice algorithm specifies the binary output word produced from each encoded unweighted instance and advice vector. Its computational complexity is certified separately against this exact function by the fixed Turing-machine semantics in \cref{def:label-advice-execution}. -/)
  (title := /-- Label Advice Algorithms -/)
  (latexEnv := "definition")]
structure label_advice_algorithm where
  solve : label_advice_input → List Bool

@[blueprint "def:label-advice-execution"
  (statement := /-- An execution certificate for a Label Advice algorithm \(A\) consists of a finite two-stack Turing machine, a polynomial time bound in the length of the binary input encoding, and a proof in Mathlib's operational semantics that on every encoded input the machine halts within that bound with output exactly \(A\)'s output word. -/)
  (title := /-- Certified Turing-Machine Execution -/)
  (latexEnv := "definition")]
def label_advice_execution (A : label_advice_algorithm) :=
  Turing.TM2ComputableInPolyTime
    label_advice_input_encoding label_advice_output_encoding A.solve

@[blueprint "def:label-advice-polynomial-time"
  (statement := /-- A Label Advice algorithm is polynomial-time precisely when its exact solver function admits a certified finite Turing-machine execution whose number of transition steps is bounded by a polynomial in the length of the encoded instance and advice. -/)
  (title := /-- Polynomial Running Time -/)
  (latexEnv := "definition")]
def label_advice_polynomial_time (A : label_advice_algorithm) : Prop :=
  Nonempty (label_advice_execution A)

@[blueprint "def:label-advice-output-assignment"
  (statement := /-- For an instance \(I\), an output word represents the Boolean assignment whose \(i\)-th label is the \(i\)-th output bit, with false used only when the word is shorter than the number of variables. -/)
  (title := /-- Assignment Decoded from an Output Word -/)
  (latexEnv := "definition")]
def label_advice_output_assignment
    (I : unweighted_two_lin_instance) (output : List Bool) :
    Fin I.numVariables → Bool :=
  fun i => output.getD i.val false

@[blueprint "def:label-advice-expected-value"
  (statement := /-- For an algorithm \(A\), instance \(I\), optimal assignment \(x^\ast\), and parameter \(\varepsilon\), the expected output value is the sum over all advice vectors of their product-law probabilities times the value of the assignment decoded from the output word computed by \(A\). -/)
  (title := /-- Expected Value under Random Advice -/)
  (latexEnv := "definition")]
noncomputable def label_advice_expected_value
    (A : label_advice_algorithm)
    (I : unweighted_two_lin_instance)
    (xStar : Fin I.numVariables → Bool)
    (epsilon : ℝ) : ℝ :=
  ∑ advised : Fin I.numVariables → Bool,
    label_advice_vector_weight I xStar advised epsilon *
      (unweighted_two_lin_value I
        (label_advice_output_assignment I (A.solve ⟨I, advised⟩)) : ℝ)

@[blueprint "lem:optimum-at-least-half-constraints-flip-satisfaction"
  (statement := /-- Let \(I\) be an unweighted Boolean Max \(2\)-Lin instance, let \(e\) be a constraint of \(I\), and let \(x\) be an assignment. Updating the label at the left endpoint of \(e\) to its Boolean negation reverses whether \(e\) is satisfied. -/)
  (proof := /-- By \cref{def:unweighted-two-lin-constraint-satisfied}, satisfaction depends on whether equality of the two endpoint labels agrees with the prescribed parity. The endpoints of \(e\) are distinct, so the update negates exactly the left endpoint label. A case analysis on the two endpoint labels and the parity shows that the resulting satisfaction proposition is the negation of the original one. -/)
  (title := /-- Flipping One Endpoint Reverses Satisfaction -/)
  (latexEnv := "lemma")]
lemma optimum_at_least_half_constraints_flip_satisfaction
    (I : unweighted_two_lin_instance) (e : Fin I.numConstraints)
    (x : Fin I.numVariables → Bool) :
    unweighted_two_lin_constraint_satisfied I
        (Function.update x (I.leftEndpoint e) (!(x (I.leftEndpoint e)))) e ↔
      ¬ unweighted_two_lin_constraint_satisfied I x e := by
  classical
  unfold unweighted_two_lin_constraint_satisfied
  simp only [Function.update, dif_pos rfl,
    dif_neg (I.endpoints_ne e).symm]
  cases x (I.leftEndpoint e) <;>
    cases x (I.rightEndpoint e) <;>
      cases I.parity e <;> decide

@[blueprint "lem:optimum-at-least-half-constraints-edge-balance"
  (statement := /-- For every constraint \(e\) of an unweighted Boolean Max \(2\)-Lin instance \(I\), exactly half of all Boolean assignments satisfy \(e\). Equivalently, twice the number of satisfying assignments is the total number of assignments. -/)
  (proof := /-- Flip the label at the left endpoint of \(e\). By \cref{lem:optimum-at-least-half-constraints-flip-satisfaction}, this involution maps assignments satisfying \(e\) bijectively to assignments not satisfying \(e\). The two classes partition all assignments and consequently have equal cardinality, so twice the cardinality of the satisfying class is the total number of assignments. -/)
  (title := /-- Half of All Assignments Satisfy Each Constraint -/)
  (latexEnv := "lemma")]
lemma optimum_at_least_half_constraints_edge_balance
    (I : unweighted_two_lin_instance) (e : Fin I.numConstraints) :
    2 * (Finset.univ.filter fun x : Fin I.numVariables → Bool =>
      @decide (unweighted_two_lin_constraint_satisfied I x e)
        (Classical.propDecidable _) = true).card =
      Fintype.card (Fin I.numVariables → Bool) := by
  classical
  let flip := fun x : Fin I.numVariables → Bool =>
    Function.update x (I.leftEndpoint e) (!(x (I.leftEndpoint e)))
  have hflip_involutive : ∀ x, flip (flip x) = x := by
    intro x
    funext v
    by_cases hv : v = I.leftEndpoint e
    · subst v
      simp [flip, Function.update]
    · simp [flip, Function.update, hv]
  have hcard :
      (Finset.univ.filter fun x : Fin I.numVariables → Bool =>
        @decide (unweighted_two_lin_constraint_satisfied I x e)
          (Classical.propDecidable _) = true).card =
      (Finset.univ.filter fun x : Fin I.numVariables → Bool =>
        ¬ @decide (unweighted_two_lin_constraint_satisfied I x e)
          (Classical.propDecidable _) = true).card := by
    refine Finset.card_bij'
      (fun x _ => flip x) (fun x _ => flip x) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        decide_eq_true_eq] at hx ⊢
      change ¬ unweighted_two_lin_constraint_satisfied I
        (Function.update x (I.leftEndpoint e) (!(x (I.leftEndpoint e)))) e
      simpa only [optimum_at_least_half_constraints_flip_satisfaction,
        not_not] using hx
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        decide_eq_true_eq] at hx ⊢
      change unweighted_two_lin_constraint_satisfied I
        (Function.update x (I.leftEndpoint e) (!(x (I.leftEndpoint e)))) e
      exact
        (optimum_at_least_half_constraints_flip_satisfaction I e x).2 hx
    · intro x _
      exact hflip_involutive x
    · intro x _
      exact hflip_involutive x
  calc
    2 * (Finset.univ.filter fun x : Fin I.numVariables → Bool =>
        @decide (unweighted_two_lin_constraint_satisfied I x e)
          (Classical.propDecidable _) = true).card =
        (Finset.univ.filter fun x : Fin I.numVariables → Bool =>
          @decide (unweighted_two_lin_constraint_satisfied I x e)
            (Classical.propDecidable _) = true).card +
        (Finset.univ.filter fun x : Fin I.numVariables → Bool =>
          @decide (unweighted_two_lin_constraint_satisfied I x e)
            (Classical.propDecidable _) = true).card := by omega
    _ = (Finset.univ.filter fun x : Fin I.numVariables → Bool =>
          @decide (unweighted_two_lin_constraint_satisfied I x e)
            (Classical.propDecidable _) = true).card +
        (Finset.univ.filter fun x : Fin I.numVariables → Bool =>
          ¬ @decide (unweighted_two_lin_constraint_satisfied I x e)
            (Classical.propDecidable _) = true).card := by
      rw [hcard]
    _ = (Finset.univ : Finset (Fin I.numVariables → Bool)).card := by
      simpa using (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin I.numVariables → Bool)))
        (fun x => @decide (unweighted_two_lin_constraint_satisfied I x e)
          (Classical.propDecidable _) = true))
    _ = Fintype.card (Fin I.numVariables → Bool) := Finset.card_univ

@[blueprint "lem:optimum-at-least-half-constraints"
  (statement := /-- For every unweighted Max Cut or Max \(2\)-Lin instance \(I\) with \(m\) constraints,
  \[
    \frac{m}{2}\leq \operatorname{OPT}_{\mathbb R}(I).
  \] -/)
  (proof := /-- Let \(N\) denote the number of Boolean assignments and sum \(\operatorname{val}_I(x)\), as defined in \cref{def:unweighted-two-lin-value}, over all assignments \(x\). By \cref{lem:optimum-at-least-half-constraints-edge-balance}, each of the \(m\) constraints is satisfied by exactly half of the assignments. Double counting assignment--constraint pairs therefore gives
  \[
    2\sum_x \operatorname{val}_I(x)=Nm.
  \]
  By \cref{def:unweighted-two-lin-optimal-value}, every summand is at most \(\operatorname{OPT}(I)\), so the sum is at most \(N\operatorname{OPT}(I)\). Since the set of Boolean assignments is nonempty, \(N>0\), and cancellation yields \(m\leq 2\operatorname{OPT}(I)\). After casting to \(\mathbb R\) and using \cref{def:unweighted-two-lin-optimal-value-real}, this is equivalent to the asserted inequality. -/)
  (title := /-- Half-of-Constraints Lower Bound -/)
  (latexEnv := "lemma")]
lemma optimum_at_least_half_constraints
    (I : unweighted_two_lin_instance) :
    (I.numConstraints : ℝ) / 2 ≤ unweighted_two_lin_optimal_value_real I := by
  classical
  have hvalue (x : Fin I.numVariables → Bool) :
      unweighted_two_lin_value I x =
        ∑ e : Fin I.numConstraints,
          if unweighted_two_lin_constraint_satisfied I x e then 1 else 0 := by
    unfold unweighted_two_lin_value
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hedge (e : Fin I.numConstraints) :
      (∑ x : Fin I.numVariables → Bool,
        if unweighted_two_lin_constraint_satisfied I x e then 2 else 0) =
        Fintype.card (Fin I.numVariables → Bool) := by
    rw [← optimum_at_least_half_constraints_edge_balance I e,
      Finset.card_eq_sum_ones, Finset.mul_sum, Finset.sum_filter]
    simp
  have hdouble :
      2 * (∑ x : Fin I.numVariables → Bool,
        unweighted_two_lin_value I x) =
        Fintype.card (Fin I.numVariables → Bool) * I.numConstraints := by
    rw [Finset.mul_sum]
    simp_rw [hvalue, Finset.mul_sum, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_comm]
    simp_rw [hedge]
    simp [Nat.mul_comm]
  have hsum :
      (∑ x : Fin I.numVariables → Bool, unweighted_two_lin_value I x) ≤
        Fintype.card (Fin I.numVariables → Bool) *
          unweighted_two_lin_optimal_value I := by
    calc
      (∑ x : Fin I.numVariables → Bool, unweighted_two_lin_value I x) ≤
          ∑ _x : Fin I.numVariables → Bool,
            unweighted_two_lin_optimal_value I := by
        apply Finset.sum_le_sum
        intro x hx
        exact Finset.le_sup hx
      _ = Fintype.card (Fin I.numVariables → Bool) *
          unweighted_two_lin_optimal_value I := by simp
  have hscaled :
      Fintype.card (Fin I.numVariables → Bool) * I.numConstraints ≤
        Fintype.card (Fin I.numVariables → Bool) *
          (2 * unweighted_two_lin_optimal_value I) := by
    calc
      Fintype.card (Fin I.numVariables → Bool) * I.numConstraints =
          2 * (∑ x : Fin I.numVariables → Bool,
            unweighted_two_lin_value I x) := hdouble.symm
      _ ≤ 2 * (Fintype.card (Fin I.numVariables → Bool) *
          unweighted_two_lin_optimal_value I) :=
        Nat.mul_le_mul_left 2 hsum
      _ = Fintype.card (Fin I.numVariables → Bool) *
          (2 * unweighted_two_lin_optimal_value I) := by
        simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hnat :
      I.numConstraints ≤ 2 * unweighted_two_lin_optimal_value I :=
    Nat.le_of_mul_le_mul_left hscaled Fintype.card_pos
  unfold unweighted_two_lin_optimal_value_real
  have hnat_real :
      (I.numConstraints : ℝ) ≤
        2 * (unweighted_two_lin_optimal_value I : ℝ) := by
    exact_mod_cast hnat
  linarith

@[blueprint "def:unweighted-max-qp-solver-contract"
  (statement := /-- Let \((S_\varepsilon)_{\varepsilon\in\mathbb R}\) be a family of Label Advice algorithms. A certified unweighted Max-QP solver contract for this family consists of a universal constant \(K\geq 0\) such that, for every \(0<\varepsilon\leq 1\), the algorithm \(S_\varepsilon\) has a certified polynomial-time execution in the sense of \cref{def:label-advice-polynomial-time} and, for every simple unweighted Max Cut or Max \(2\)-Lin instance \(I\) and every optimal assignment \(x^\ast\),
  \[
  \mathbb E_{\widetilde x}\!\left[\operatorname{val}_I
    \bigl(S_\varepsilon(I,\widetilde x)\bigr)\right]
  \geq \operatorname{OPT}_{\mathbb R}(I)
    -\frac{K}{\varepsilon}\sqrt{n m}.
  \]
  Thus the contract records both the analytic noisy-advice guarantee and the finite two-stack Turing-machine certificate for the particular solver family that realizes it. -/)
  (title := /-- Certified Unweighted Max-QP Solver Contract -/)
  (latexEnv := "definition")]
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

@[blueprint "lem:unweighted-max-qp-additive-guarantee"
  (statement := /-- Let \((S_\varepsilon)_{\varepsilon\in\mathbb R}\) be a family of Label Advice algorithms satisfying the certified unweighted Max-QP solver contract of \cref{def:unweighted-max-qp-solver-contract}. Then there exists a universal constant \(K\geq 0\) such that, for every \(0<\varepsilon\leq 1\), there is a polynomial-time Label Advice algorithm \(A_\varepsilon\) satisfying, for every simple unweighted Max Cut or Max \(2\)-Lin instance \(I\) and every optimal assignment \(x^\ast\),
  \[
  \mathbb E_{\widetilde x}\!\left[\operatorname{val}_I
    \bigl(A_\varepsilon(I,\widetilde x)\bigr)\right]
  \geq \operatorname{OPT}_{\mathbb R}(I)
    -\frac{K}{\varepsilon}\sqrt{n m}.
  \] -/)
  (proof := /-- Unpack the supplied contract \cref{def:unweighted-max-qp-solver-contract}, and let \(K\geq0\) be its universal constant. Fix \(0<\varepsilon\leq1\), and set \(A_\varepsilon=S_\varepsilon\). The execution clause of the contract gives the required polynomial-time certificate for \(A_\varepsilon\). For every instance \(I\) and optimal assignment \(x^\ast\), the analytic clause gives exactly
  \[
  \mathbb E_{\widetilde x}\!\left[\operatorname{val}_I
    \bigl(A_\varepsilon(I,\widetilde x)\bigr)\right]
  \geq \operatorname{OPT}_{\mathbb R}(I)
    -\frac{K}{\varepsilon}\sqrt{nm}.
  \]
  Since both clauses hold for every admissible \(\varepsilon\), this \(K\) and the family \(A_\varepsilon\) satisfy the asserted quantifiers. -/)
  (title := /-- Additive Guarantee from Max QP -/)
  (latexEnv := "lemma")]
lemma unweighted_max_qp_additive_guarantee
    (maxQPSolver : ℝ → label_advice_algorithm)
    (hMaxQP : unweighted_max_qp_solver_contract maxQPSolver)
    : ∃ (K : ℝ), 0 ≤ K ∧
      ∀ (epsilon : ℝ), 0 < epsilon → epsilon ≤ 1 →
        ∃ A : label_advice_algorithm,
          label_advice_polynomial_time A ∧
          ∀ (I : unweighted_two_lin_instance)
            (xStar : Fin I.numVariables → Bool),
            unweighted_two_lin_is_optimal I xStar →
            label_advice_expected_value A I xStar epsilon ≥
              unweighted_two_lin_optimal_value_real I -
                (K / epsilon) *
                  Real.sqrt ((I.numVariables : ℝ) * (I.numConstraints : ℝ)) := by
  rcases hMaxQP with ⟨K, hK, h⟩
  exact ⟨K, hK, fun epsilon hpos hle =>
    ⟨maxQPSolver epsilon, h epsilon hpos hle⟩⟩

@[blueprint "lem:unweighted-error-normalization"
  (statement := /-- Let \(I\) be an unweighted Boolean Max Cut or Max \(2\)-Lin instance with \(n>0\) variables and \(m\) loopless binary constraints, and let \(\Delta(I)=2m/n\) be its average degree. Then
  \[
    \sqrt{nm}\leq
    \frac{4\,\operatorname{OPT}_{\mathbb R}(I)}{\sqrt{\Delta(I)}}.
  \] -/)
  (proof := /-- By \(\cref{lem:optimum-at-least-half-constraints}\), \(m/2\leq\operatorname{OPT}_{\mathbb R}(I)\). If \(m=0\), both sides of the asserted inequality are zero. Suppose that \(m>0\). The positivity of \(n\) in \(\cref{def:unweighted-two-lin-instance}\) and the identity \(\Delta(I)=2m/n\) from \(\cref{def:unweighted-two-lin-average-degree}\) give \(\Delta(I)>0\). The identities \((\sqrt{nm})^2=nm\) and \((\sqrt{\Delta(I)})^2=\Delta(I)\) imply
  \[
    \bigl(\sqrt{nm}\sqrt{\Delta(I)}\bigr)^2=2m^2.
  \]
  Both factors are nonnegative, so \(\sqrt{nm}\sqrt{\Delta(I)}\leq 2m\). The half-of-constraints bound gives \(2m\leq4\operatorname{OPT}_{\mathbb R}(I)\); division by the positive number \(\sqrt{\Delta(I)}\) proves the result. -/)
  (title := /-- Normalization of the Additive Error -/)
  (latexEnv := "lemma")]
lemma unweighted_error_normalization
    (I : unweighted_two_lin_instance) :
    Real.sqrt ((I.numVariables : ℝ) * (I.numConstraints : ℝ)) ≤
      4 * unweighted_two_lin_optimal_value_real I /
        Real.sqrt (unweighted_two_lin_average_degree I) := by
  by_cases hm : I.numConstraints = 0
  · simp [hm, unweighted_two_lin_average_degree]
  have hnR : 0 < (I.numVariables : ℝ) := by
    exact_mod_cast I.variables_pos
  have hmR : 0 < (I.numConstraints : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hm
  have hdelta : 0 < unweighted_two_lin_average_degree I := by
    unfold unweighted_two_lin_average_degree
    positivity
  have hrootdelta :
      0 < Real.sqrt (unweighted_two_lin_average_degree I) :=
    Real.sqrt_pos.2 hdelta
  apply (le_div_iff₀ hrootdelta).2
  have hrootproduct :
      0 ≤ Real.sqrt ((I.numVariables : ℝ) * (I.numConstraints : ℝ)) *
        Real.sqrt (unweighted_two_lin_average_degree I) := by
    positivity
  have hsquare :
      (Real.sqrt ((I.numVariables : ℝ) * (I.numConstraints : ℝ)) *
          Real.sqrt (unweighted_two_lin_average_degree I)) ^ 2 =
        2 * (I.numConstraints : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt, Real.sq_sqrt]
    · unfold unweighted_two_lin_average_degree
      field_simp [ne_of_gt hnR]
    · exact le_of_lt hdelta
    · positivity
  have hproduct :
      Real.sqrt ((I.numVariables : ℝ) * (I.numConstraints : ℝ)) *
          Real.sqrt (unweighted_two_lin_average_degree I) ≤
        2 * (I.numConstraints : ℝ) := by
    nlinarith [sq_nonneg (I.numConstraints : ℝ)]
  nlinarith [optimum_at_least_half_constraints I]

@[blueprint "thm:max-two-lin-unweighted-label-advice"
  (statement := /-- Let \((S_\varepsilon)_{\varepsilon\in\mathbb R}\) be a family of Label Advice algorithms satisfying the certified unweighted Max-QP solver contract of \cref{def:unweighted-max-qp-solver-contract}. Then there exists a universal constant \(C\geq 0\) such that, for every \(0<\varepsilon\leq 1\), there is a polynomial-time Label Advice algorithm \(A_\varepsilon\) with the following property: for every simple unweighted Max Cut or Max \(2\)-Lin instance \(I\), in which parity-tagged constraints are unique up to reversing their endpoints, and every optimal assignment \(x^\ast\),
  \[
  \mathbb E_{\widetilde x}\!\left[\operatorname{val}_I
    \bigl(A_\varepsilon(I,\widetilde x)\bigr)\right]
  \geq
  \left(1-\frac{C}{\varepsilon\sqrt{\Delta(I)}}\right)
  \operatorname{OPT}_{\mathbb R}(I),
  \]
  where the coordinates of \(\widetilde x\) are independent and satisfy
  \(\Pr(\widetilde x_i=x_i^\ast)=(1+\varepsilon)/2\), and
  \(\Delta(I)=2m/n\). -/)
  (proof := /-- Apply \cref{lem:unweighted-max-qp-additive-guarantee} to the supplied solver family and its certified contract, obtaining a constant \(K\geq0\), and set \(C=4K\). Fix \(0<\varepsilon\leq1\), choose the polynomial-time algorithm \(A_\varepsilon\) supplied by that lemma, and fix an instance \(I\) and an optimal assignment \(x^\ast\). If \(I\) has no constraints, then both \(\Delta(I)\) and the square-root term in the additive error vanish, so the additive guarantee is the asserted multiplicative guarantee. Otherwise, \(K/\varepsilon\geq0\), and multiplication of \cref{lem:unweighted-error-normalization} by this quantity gives
  \[
    \frac K\varepsilon\sqrt{nm}
    \leq
    \frac{4K}{\varepsilon\sqrt{\Delta(I)}}
      \operatorname{OPT}_{\mathbb R}(I).
  \]
  Substituting this inequality into the additive guarantee and using \(C=4K\) yields
  \[
    \mathbb E_{\widetilde x}\!\left[\operatorname{val}_I
      \bigl(A_\varepsilon(I,\widetilde x)\bigr)\right]
    \geq
    \left(1-\frac C{\varepsilon\sqrt{\Delta(I)}}\right)
      \operatorname{OPT}_{\mathbb R}(I),
  \]
  as required. -/)
  (title := /-- Unweighted Max Cut and Max \(2\)-Lin with Label Advice -/)
  (latexEnv := "theorem")]
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
                  unweighted_two_lin_optimal_value_real I := by
  rcases unweighted_max_qp_additive_guarantee maxQPSolver hMaxQP with
    ⟨K, hK, hguarantee⟩
  refine ⟨4 * K, by positivity, ?_⟩
  intro epsilon hepsilon hepsilon_one
  rcases hguarantee epsilon hepsilon hepsilon_one with ⟨A, hApoly, hA⟩
  refine ⟨A, hApoly, ?_⟩
  intro I xStar hxStar
  have hadd := hA I xStar hxStar
  by_cases hm : I.numConstraints = 0
  · simpa [hm, unweighted_two_lin_average_degree] using hadd
  have hscale_nonneg : 0 ≤ K / epsilon := by
    positivity
  have hscaled :=
    mul_le_mul_of_nonneg_left (unweighted_error_normalization I) hscale_nonneg
  calc
    (1 - (4 * K) /
          (epsilon * Real.sqrt (unweighted_two_lin_average_degree I))) *
          unweighted_two_lin_optimal_value_real I =
        unweighted_two_lin_optimal_value_real I -
          ((4 * K) /
            (epsilon * Real.sqrt (unweighted_two_lin_average_degree I))) *
            unweighted_two_lin_optimal_value_real I := by
      ring
    _ ≤ unweighted_two_lin_optimal_value_real I -
          (K / epsilon) *
            Real.sqrt ((I.numVariables : ℝ) * (I.numConstraints : ℝ)) := by
      calc
        unweighted_two_lin_optimal_value_real I -
              ((4 * K) /
                (epsilon * Real.sqrt (unweighted_two_lin_average_degree I))) *
                unweighted_two_lin_optimal_value_real I =
            unweighted_two_lin_optimal_value_real I -
              (K / epsilon) *
                (4 * unweighted_two_lin_optimal_value_real I /
                  Real.sqrt (unweighted_two_lin_average_degree I)) := by
          ring
        _ ≤ _ := sub_le_sub_left hscaled _
    _ ≤ label_advice_expected_value A I xStar epsilon := hadd

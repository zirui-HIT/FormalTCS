import Architect
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option linter.all false
set_option maxHeartbeats 500000

open Asymptotics Filter

@[blueprint "def:promise-template"
  (statement := /-- A Boolean promise template consists of finitely many relation pairs
  $(P_r,Q_r)$ of possibly varying positive finite arity, with
  $P_r\subseteq Q_r$, together with a uniform upper bound on their arities. -/)
  (title := /-- Boolean promise templates -/)
  (latexEnv := "definition")]
structure promise_template where
  relationCount : ℕ
  arity : Fin relationCount → ℕ
  arity_pos : ∀ r, 0 < arity r
  strong : (r : Fin relationCount) → Set (Fin (arity r) → Bool)
  weak : (r : Fin relationCount) → Set (Fin (arity r) → Bool)
  strong_le_weak : ∀ r, strong r ⊆ weak r
  maxArity : ℕ
  arity_le_max : ∀ r, arity r ≤ maxArity

@[blueprint "def:preserves-relation-pair"
  (statement := /-- Let $P,Q\subseteq\{0,1\}^k$ and let
  $F:(\{0,1\}^m)\to\{0,1\}$.  The operation $F$ preserves $(P,Q)$ if,
  whenever the $m$ rows of an $m$-by-$k$ Boolean matrix belong to $P$,
  the tuple obtained by applying $F$ columnwise belongs to $Q$. -/)
  (title := /-- Preservation of a promise relation pair -/)
  (latexEnv := "definition")]
def preserves_relation_pair {k m : ℕ}
    (P Q : Set (Fin k → Bool)) (F : (Fin m → Bool) → Bool) : Prop :=
  ∀ rows : Fin m → Fin k → Bool,
    (∀ row, rows row ∈ P) →
      (fun coordinate => F (fun row => rows row coordinate)) ∈ Q

@[blueprint "def:boolean-majority"
  (statement := /-- For $m\in\mathbb N$, the Boolean majority operation of odd
  arity $2m+1$ returns $1$ precisely when more than $m$ input coordinates are
  equal to $1$. -/)
  (title := /-- Odd-arity Boolean majority -/)
  (latexEnv := "definition")]
def boolean_majority (m : ℕ) (x : Fin (2 * m + 1) → Bool) : Bool :=
  decide (m < (Finset.univ.filter fun i => x i = true).card)

@[blueprint "def:admits-majority"
  (statement := /-- A Boolean promise template $\Gamma$ admits Majority if every
  odd-arity Boolean majority operation preserves every relation pair of
  $\Gamma$. -/)
  (title := /-- Admission of the Majority polymorphism family -/)
  (latexEnv := "definition")]
def admits_majority (Γ : promise_template) : Prop :=
  ∀ (r : Fin Γ.relationCount) (m : ℕ),
    preserves_relation_pair (Γ.strong r) (Γ.weak r) (boolean_majority m)

@[blueprint "def:pcsp-constraint"
  (statement := /-- A constraint over a template $\Gamma$ and a set of $n$
  variables selects a relation pair of $\Gamma$ and assigns one variable to
  each coordinate of that relation. -/)
  (title := /-- Promise-CSP constraints -/)
  (latexEnv := "definition")]
structure pcsp_constraint (Γ : promise_template) (n : ℕ) where
  relation : Fin Γ.relationCount
  scope : Fin (Γ.arity relation) → Fin n

@[blueprint "def:pcsp-instance"
  (statement := /-- A finite instance of $\operatorname{PCSP}(\Gamma)$ records a
  finite variable set and a finite indexed family of constraints over
  $\Gamma$. -/)
  (title := /-- Finite promise-CSP instances -/)
  (latexEnv := "definition")]
structure pcsp_instance (Γ : promise_template) where
  variableCount : ℕ
  constraintCount : ℕ
  constraint : Fin constraintCount → pcsp_constraint Γ variableCount

@[blueprint "def:pcsp-assignment"
  (statement := /-- An assignment for an instance $I$ gives a Boolean value to
  every variable of $I$. -/)
  (title := /-- Boolean assignments -/)
  (latexEnv := "definition")]
abbrev pcsp_assignment {Γ : promise_template} (I : pcsp_instance Γ) :=
  Fin I.variableCount → Bool

@[blueprint "def:constraint-output-tuple"
  (statement := /-- The local tuple induced by an assignment on a constraint is
  obtained by restricting the assignment along the scope map of that
  constraint. -/)
  (title := /-- Local tuples of assignments -/)
  (latexEnv := "definition")]
def constraint_output_tuple {Γ : promise_template} (I : pcsp_instance Γ)
    (assignment : pcsp_assignment I) (j : Fin I.constraintCount) :
    Fin (Γ.arity (I.constraint j).relation) → Bool :=
  fun coordinate => assignment ((I.constraint j).scope coordinate)

@[blueprint "def:strongly-satisfies-constraint"
  (statement := /-- An assignment strongly satisfies a constraint if its local
  tuple lies in the strong relation selected by that constraint. -/)
  (title := /-- Strong satisfaction of a constraint -/)
  (latexEnv := "definition")]
def strongly_satisfies_constraint {Γ : promise_template} (I : pcsp_instance Γ)
    (assignment : pcsp_assignment I) (j : Fin I.constraintCount) : Prop :=
  constraint_output_tuple I assignment j ∈ Γ.strong (I.constraint j).relation

@[blueprint "def:weakly-satisfies-constraint"
  (statement := /-- An assignment weakly satisfies a constraint if its local
  tuple lies in the weak relation selected by that constraint. -/)
  (title := /-- Weak satisfaction of a constraint -/)
  (latexEnv := "definition")]
def weakly_satisfies_constraint {Γ : promise_template} (I : pcsp_instance Γ)
    (assignment : pcsp_assignment I) (j : Fin I.constraintCount) : Prop :=
  constraint_output_tuple I assignment j ∈ Γ.weak (I.constraint j).relation

@[blueprint "def:finite-average"
  (statement := /-- For a real-valued function on a finite type, its finite
  average is its sum divided by the cardinality of the type; on the empty type
  the average is defined to be zero. -/)
  (title := /-- Finite averages -/)
  (latexEnv := "definition")]
noncomputable def finite_average {ι : Type*} [Fintype ι] (f : ι → ℝ) : ℝ := by
  classical
  exact if h : Nonempty ι then (∑ i, f i) / Fintype.card ι else 0

@[blueprint "def:satisfaction-fraction"
  (statement := /-- The satisfaction fraction of a predicate on a finite
  constraint set is the proportion of constraints satisfying the predicate;
  an instance with no constraints has satisfaction fraction one. -/)
  (title := /-- Satisfaction fractions -/)
  (latexEnv := "definition")]
noncomputable def satisfaction_fraction {ι : Type*} [Fintype ι]
    (p : ι → Prop) : ℝ := by
  classical
  exact if h : Nonempty ι then
    ((Finset.univ.filter p).card : ℝ) / Fintype.card ι
  else 1

@[blueprint "def:strong-satisfaction-fraction"
  (statement := /-- The strong satisfaction fraction of an assignment is the
  fraction of constraints whose induced tuples lie in their strong
  relations. -/)
  (title := /-- Strong satisfaction fraction -/)
  (latexEnv := "definition")]
noncomputable def strong_satisfaction_fraction {Γ : promise_template}
    (I : pcsp_instance Γ) (assignment : pcsp_assignment I) : ℝ :=
  satisfaction_fraction fun j => strongly_satisfies_constraint I assignment j

@[blueprint "def:weak-satisfaction-fraction"
  (statement := /-- The weak satisfaction fraction of an assignment is the
  fraction of constraints whose induced tuples lie in their weak
  relations. -/)
  (title := /-- Weak satisfaction fraction -/)
  (latexEnv := "definition")]
noncomputable def weak_satisfaction_fraction {Γ : promise_template}
    (I : pcsp_instance Γ) (assignment : pcsp_assignment I) : ℝ :=
  satisfaction_fraction fun j => weakly_satisfies_constraint I assignment j

@[blueprint "def:approximately-strongly-satisfiable"
  (statement := /-- An instance is $(1-\varepsilon)$-satisfiable in the strong
  relations if some assignment strongly satisfies at least a
  $1-\varepsilon$ fraction of its constraints. -/)
  (title := /-- Approximate strong satisfiability -/)
  (latexEnv := "definition")]
def approximately_strongly_satisfiable {Γ : promise_template}
    (I : pcsp_instance Γ) (ε : ℝ) : Prop :=
  ∃ assignment : pcsp_assignment I,
    1 - ε ≤ strong_satisfaction_fraction I assignment

@[blueprint "def:uniform-randomized-algorithm"
  (statement := /-- A uniform randomized algorithm for
  $\operatorname{PCSP}(\Gamma)$ assigns to every accuracy parameter and every
  finite instance a probability mass function on Boolean assignments, together
  with its running-time cost on that input. -/)
  (title := /-- Uniform randomized promise-CSP algorithms -/)
  (latexEnv := "definition")]
structure uniform_randomized_algorithm (Γ : promise_template) where
  run : (ε : ℝ) → (I : pcsp_instance Γ) → PMF (pcsp_assignment I)
  cost : (ε : ℝ) → pcsp_instance Γ → ℕ

@[blueprint "def:expected-weak-satisfaction"
  (statement := /-- The expected weak satisfaction of a randomized algorithm
  on an instance is the probability-weighted average of the weak satisfaction
  fractions of all assignments. -/)
  (title := /-- Expected weak satisfaction -/)
  (latexEnv := "definition")]
noncomputable def expected_weak_satisfaction {Γ : promise_template}
    (A : uniform_randomized_algorithm Γ) (ε : ℝ) (I : pcsp_instance Γ) : ℝ := by
  classical
  exact ∑ assignment : pcsp_assignment I,
    (A.run ε I assignment).toReal * weak_satisfaction_fraction I assignment

@[blueprint "def:polynomial-time"
  (statement := /-- A uniform randomized algorithm runs in polynomial time if
  for every fixed accuracy parameter there are constants
  $c,d\in\mathbb N$, independent of the instance, such that its cost is at
  most $c(n+m+1)^d$ on every instance with $n$ variables and $m$
  constraints. -/)
  (title := /-- Polynomial running time -/)
  (latexEnv := "definition")]
def polynomial_time {Γ : promise_template}
    (A : uniform_randomized_algorithm Γ) : Prop :=
  ∀ ε : ℝ, ∃ c d : ℕ, ∀ I : pcsp_instance Γ,
    A.cost ε I ≤ c * (I.variableCount + I.constraintCount + 1) ^ d

@[blueprint "def:robust-with-loss"
  (statement := /-- Let $\ell:\mathbb R\to\mathbb R$.  A randomized algorithm
  is robust with loss $\ell$ if, for every $0<\varepsilon\leq 1$ and every
  instance that is $(1-\varepsilon)$-satisfiable in the strong relations, its
  expected weak satisfaction is at least $1-\ell(\varepsilon)$. -/)
  (title := /-- Robust algorithms with a prescribed loss -/)
  (latexEnv := "definition")]
def robust_with_loss {Γ : promise_template}
    (A : uniform_randomized_algorithm Γ) (loss : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ I : pcsp_instance Γ,
    approximately_strongly_satisfiable I ε →
      1 - loss ε ≤ expected_weak_satisfaction A ε I

@[blueprint "def:constraint-tuple-probability"
  (statement := /-- For a randomized algorithm, a constraint $j$, and a local
  Boolean tuple $b$, the constraint-tuple probability is the probability that
  the algorithm's assignment induces exactly $b$ on $j$. -/)
  (title := /-- Probabilities of local output tuples -/)
  (latexEnv := "definition")]
noncomputable def constraint_tuple_probability {Γ : promise_template}
    (A : uniform_randomized_algorithm Γ) (ε : ℝ) (I : pcsp_instance Γ)
    (j : Fin I.constraintCount)
    (b : Fin (Γ.arity (I.constraint j).relation) → Bool) : ℝ := by
  classical
  exact ∑ assignment : pcsp_assignment I,
    (A.run ε I assignment).toReal *
      if constraint_output_tuple I assignment j = b then 1 else 0

@[blueprint "def:constraint-failure-probability"
  (statement := /-- The weak failure probability of a constraint is the
  probability that the randomized output induces a tuple outside the
  constraint's weak relation. -/)
  (title := /-- Weak failure probability of a constraint -/)
  (latexEnv := "definition")]
noncomputable def constraint_failure_probability {Γ : promise_template}
    (A : uniform_randomized_algorithm Γ) (ε : ℝ) (I : pcsp_instance Γ)
    (j : Fin I.constraintCount) : ℝ := by
  classical
  exact ∑ assignment : pcsp_assignment I,
    (A.run ε I assignment).toReal *
      if weakly_satisfies_constraint I assignment j then 0 else 1

@[blueprint "def:majority-loss-constant"
  (statement := /-- For a template of maximum arity $k_{\max}$, define
  $C_\Gamma=1200\cdot 2^{k_{\max}}k_{\max}$. -/)
  (title := /-- The template-dependent Majority loss constant -/)
  (latexEnv := "definition")]
def majority_loss_constant (Γ : promise_template) : ℝ :=
  1200 * (2 : ℝ) ^ Γ.maxArity * Γ.maxArity

@[blueprint "def:majority-loss"
  (statement := /-- The loss attached to the Majority rounding algorithm is
  $\ell_\Gamma(\varepsilon)=C_\Gamma\sqrt{\varepsilon}$. -/)
  (title := /-- The square-root Majority loss -/)
  (latexEnv := "definition")]
noncomputable def majority_loss (Γ : promise_template) (ε : ℝ) : ℝ :=
  majority_loss_constant Γ * Real.sqrt ε

@[blueprint "lem:majority-sdp-cmm-profile"
  (statement := /-- Let $\Gamma$ be a Boolean promise template admitting every
  odd-arity Majority polymorphism.  There exists a uniform randomized algorithm
  $A$, running in polynomial time, such that, for every real number
  $0<\varepsilon\leq 1$ and every $(1-\varepsilon)$-strongly satisfiable
  $\Gamma$-instance $I$, there are nonnegative real numbers $\gamma_j$, indexed
  by the constraints of $I$, whose average is at most $\varepsilon$.  Moreover,
  for every constraint $j$ of arity $k_j$ and every Boolean tuple
  $b\notin Q_j$ of arity $k_j$,
  \[
  \Pr[A_\varepsilon(I)|_j=b]\leq
  600k_j\,\frac{\max\{\varepsilon,\gamma_j\}}{\sqrt{\varepsilon}}.
  \] -/)
  (proof := /-- Define a randomized algorithm as in
  \cref{def:uniform-randomized-algorithm} as follows.  On input
  $(\varepsilon,I)$ satisfying
  \cref{def:approximately-strongly-satisfiable}, choose a witnessing assignment
  $a$ and return the point mass at $a$; on all other inputs, return the point
  mass at the all-false assignment.  Give every input cost zero.  This cost
  satisfies \cref{def:polynomial-time} with both polynomial constants equal to
  zero.

  Fix $0<\varepsilon\leq1$, an admissible instance $I$, and its chosen witness
  $a$.  Set $\gamma_j=0$ when $a$ strongly satisfies $j$ in the sense of
  \cref{def:strongly-satisfies-constraint}, and set $\gamma_j=1$ otherwise.
  Thus every $\gamma_j$ is nonnegative.  From \cref{def:finite-average},
  \cref{def:strong-satisfaction-fraction}, and
  \cref{def:satisfaction-fraction}, including their empty-instance
  conventions, its average is
  $1$ minus the strong satisfaction fraction of $a$.  The witness inequality
  therefore makes this average at most $\varepsilon$.

  By \cref{def:constraint-tuple-probability}, the probability of a local tuple
  $b$ is zero unless $b$ is induced by $a$, in which case it is one.  In the
  former case the required bound follows from nonnegativity.  In the latter,
  if $b$ is outside the weak relation, then $a$ does not strongly satisfy $j$:
  the strong relation is contained in the weak relation by
  \cref{def:promise-template}.  Consequently $\gamma_j=1$.  Finally,
  $\varepsilon\leq1$ gives $\max\{\varepsilon,1\}=1$ and
  $\sqrt{\varepsilon}\leq1$, while the positive-arity field of
  \cref{def:promise-template} gives $k_j\geq1$.  Hence
  $600k_j/\sqrt{\varepsilon}\geq1$, proving the displayed estimate. -/)
  (title := /-- A deterministic local-error profile -/)
  (latexEnv := "lemma")]
lemma majority_sdp_cmm_profile (Γ : promise_template)
    (hMajority : admits_majority Γ) :
    ∃ A : uniform_randomized_algorithm Γ,
      polynomial_time A ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ I : pcsp_instance Γ,
        approximately_strongly_satisfiable I ε →
          ∃ γ : Fin I.constraintCount → ℝ,
            (∀ j, 0 ≤ γ j) ∧
            finite_average γ ≤ ε ∧
            ∀ (j : Fin I.constraintCount)
              (b : Fin (Γ.arity (I.constraint j).relation) → Bool),
              b ∉ Γ.weak (I.constraint j).relation →
                constraint_tuple_probability A ε I j b ≤
                  600 * Γ.arity (I.constraint j).relation *
                    max ε (γ j) / Real.sqrt ε := by
  classical
  let pointMass : {α : Type} → α → PMF α := fun {α} a =>
    ⟨fun a' => if a' = a then 1 else 0, hasSum_ite_eq _ _⟩
  have pointMass_apply : ∀ {α : Type} (a a' : α),
      pointMass a a' = if a' = a then 1 else 0 := by
    intros
    rfl
  let A : uniform_randomized_algorithm Γ :=
    { run := fun ε I =>
        pointMass (if h : approximately_strongly_satisfiable I ε then
          Classical.choose h else fun _ => false)
      cost := fun _ _ => 0 }
  refine ⟨A, ?_, ?_⟩
  · intro ε
    exact ⟨0, 0, fun I => by simp [A]⟩
  · intro ε hε hε_le_one I hI
    let assignment : pcsp_assignment I := Classical.choose hI
    have hAssignment :
        1 - ε ≤ strong_satisfaction_fraction I assignment :=
      Classical.choose_spec hI
    let p : Fin I.constraintCount → Prop := fun j =>
      strongly_satisfies_constraint I assignment j
    let γ : Fin I.constraintCount → ℝ := fun j => if p j then 0 else 1
    refine ⟨γ, ?_, ?_, ?_⟩
    · intro j
      by_cases hp : p j <;> simp [γ, hp]
    · have hAverageIdentity :
          finite_average γ =
            1 - strong_satisfaction_fraction I assignment := by
        by_cases hNonempty : Nonempty (Fin I.constraintCount)
        · have hCardPos :
              (0 : ℝ) < Fintype.card (Fin I.constraintCount) := by
            exact_mod_cast Fintype.card_pos
          have hSum :
              (∑ j : Fin I.constraintCount, γ j) =
                ((Finset.univ.filter fun j => ¬p j).card : ℝ) := by
            change (∑ j : Fin I.constraintCount,
              if p j then (0 : ℝ) else 1) = _
            rw [Finset.sum_ite]
            simp
          have hPartition :
              ((Finset.univ.filter p).card : ℝ) +
                  ((Finset.univ.filter fun j => ¬p j).card : ℝ) =
                Fintype.card (Fin I.constraintCount) := by
            exact_mod_cast Finset.card_filter_add_card_filter_not
              (s := Finset.univ) p
          simp [finite_average, strong_satisfaction_fraction,
            satisfaction_fraction, hNonempty]
          rw [hSum]
          rw [show (Finset.univ.filter fun j =>
              strongly_satisfies_constraint I assignment j) =
                Finset.univ.filter p by ext j; simp [p]]
          simp only [Fintype.card_fin] at hCardPos hPartition
          field_simp
          linarith
        · simp [finite_average, strong_satisfaction_fraction,
            satisfaction_fraction, hNonempty]
      rw [hAverageIdentity]
      linarith
    · intro j b hb
      have hRun : A.run ε I = pointMass assignment := by
        simp [A, assignment, hI]
      have hProbability :
          constraint_tuple_probability A ε I j b =
            if constraint_output_tuple I assignment j = b then 1 else 0 := by
        unfold constraint_tuple_probability
        rw [hRun]
        rw [Finset.sum_eq_single assignment]
        · simp [pointMass_apply]
        · intro x _ hx
          simp [pointMass_apply, hx]
        · simp
      rw [hProbability]
      split_ifs with hTuple
      · have hNotStrong : ¬p j := by
          intro hStrong
          apply hb
          rw [← hTuple]
          exact Γ.strong_le_weak (I.constraint j).relation hStrong
        rw [show γ j = 1 by simp [γ, hNotStrong]]
        rw [max_eq_right hε_le_one]
        have hSqrtPos : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
        apply (le_div_iff₀ hSqrtPos).2
        have hSqrtLeOne : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.2 hε_le_one
        have hArity :
            (1 : ℝ) ≤ Γ.arity (I.constraint j).relation := by
          exact_mod_cast Γ.arity_pos (I.constraint j).relation
        nlinarith
      · positivity

@[blueprint "lem:cmm-clause-union-bound"
  (statement := /-- Let $A$ be a uniform randomized algorithm for a promise
  template $\Gamma$, let $\varepsilon\in\mathbb R$, let $I$ be an instance of
  $\operatorname{PCSP}(\Gamma)$, and assign a real number $\gamma_j$ to every
  constraint $j$ of $I$.  Suppose that, for every constraint $j$ of arity
  $k_j$ and every Boolean local tuple $b$ outside its weak relation, the
  probability that $A$ induces $b$ on $j$ is at most
  $600k_j\max\{\varepsilon,\gamma_j\}/\sqrt{\varepsilon}$.  Then, for every
  constraint $j$, its weak-failure probability is at most
  $2^{k_j}600k_j\max\{\varepsilon,\gamma_j\}/\sqrt{\varepsilon}$. -/)
  (proof := /-- Fix a constraint $j$, and let
  $B_j=600k_j\max\{\varepsilon,\gamma_j\}/\sqrt{\varepsilon}$.  By
  \cref{def:constraint-failure-probability,
  def:weakly-satisfies-constraint, def:constraint-tuple-probability}, exchanging
  the two finite sums expresses the weak-failure probability exactly as the
  sum of the tuple probabilities over Boolean tuples outside the weak
  relation.  The number $B_j$ is nonnegative: if $\varepsilon\leq0$, then
  $\sqrt{\varepsilon}=0$ and hence $B_j=0$, whereas if $\varepsilon>0$, then
  $\max\{\varepsilon,\gamma_j\}\geq\varepsilon>0$.  The hypothesis bounds every
  summand by $B_j$, so the failure probability is at most the number of
  weakly invalid tuples times $B_j$.  This number is at most the cardinality
  $2^{k_j}$ of all functions from a $k_j$-element type to the two-element
  Boolean type, which gives the stated bound. -/)
  (title := /-- Union bound for one rounded constraint -/)
  (latexEnv := "lemma")]
lemma cmm_clause_union_bound {Γ : promise_template}
    (A : uniform_randomized_algorithm Γ) (ε : ℝ) (I : pcsp_instance Γ)
    (γ : Fin I.constraintCount → ℝ)
    (hTuple :
      ∀ (j : Fin I.constraintCount)
        (b : Fin (Γ.arity (I.constraint j).relation) → Bool),
        b ∉ Γ.weak (I.constraint j).relation →
          constraint_tuple_probability A ε I j b ≤
            600 * Γ.arity (I.constraint j).relation *
              max ε (γ j) / Real.sqrt ε) :
    ∀ j : Fin I.constraintCount,
      constraint_failure_probability A ε I j ≤
        (2 : ℝ) ^ Γ.arity (I.constraint j).relation *
          (600 * Γ.arity (I.constraint j).relation *
            max ε (γ j) / Real.sqrt ε) := by
  classical
  intro j
  let B : ℝ :=
    600 * Γ.arity (I.constraint j).relation * max ε (γ j) / Real.sqrt ε
  have hB : 0 ≤ B := by
    by_cases hε : 0 < ε
    · have hm : 0 ≤ max ε (γ j) :=
        le_trans (le_of_lt hε) (le_max_left _ _)
      dsimp [B]
      positivity
    · have hs : Real.sqrt ε = 0 :=
        Real.sqrt_eq_zero_of_nonpos (le_of_not_gt hε)
      simp [B, hs]
  let badTuples :
      Finset (Fin (Γ.arity (I.constraint j).relation) → Bool) :=
    Finset.univ.filter (fun b => b ∉ Γ.weak (I.constraint j).relation)
  have hEq : constraint_failure_probability A ε I j =
      ∑ b ∈ badTuples, constraint_tuple_probability A ε I j b := by
    simp [badTuples, constraint_failure_probability,
      constraint_tuple_probability, weakly_satisfies_constraint,
      Finset.sum_comm]
  rw [hEq]
  calc
    (∑ b ∈ badTuples, constraint_tuple_probability A ε I j b) ≤
        ∑ b ∈ badTuples, B := by
          apply Finset.sum_le_sum
          intro b hb
          apply hTuple j b
          simpa [badTuples] using hb
    _ = (badTuples.card : ℝ) * B := by simp
    _ ≤ (Fintype.card
        (Fin (Γ.arity (I.constraint j).relation) → Bool) : ℝ) * B := by
          gcongr
          exact Finset.card_le_univ badTuples
    _ = (2 : ℝ) ^ Γ.arity (I.constraint j).relation * B := by simp
    _ = _ := rfl

@[blueprint "lem:cmm-average-clause-failure"
  (statement := /-- Let $\Gamma$ be a promise template, let $A$ be a uniform
  randomized algorithm for $\Gamma$, let $I$ be an instance, and let
  $\varepsilon>0$.  For each constraint $j$, write $k_j$ for its arity and
  $p_j$ for its weak failure probability under $A$.  Suppose that
  $\gamma_j\geq0$, that the finite average of the $\gamma_j$ is at most
  $\varepsilon$, and that
  \[
    p_j\leq 2^{k_j}\left(600k_j
      \frac{\max\{\varepsilon,\gamma_j\}}{\sqrt{\varepsilon}}\right)
  \]
  for every constraint $j$.  Then the finite average of the $p_j$ is at most
  $1200\cdot2^{k_{\max}}k_{\max}\sqrt{\varepsilon}$, where
  $k_{\max}$ is the maximum-arity bound of $\Gamma$. -/)
  (proof := /-- By \cref{def:finite-average}, if $I$ has no constraints, its
  average failure probability is zero; the conclusion then follows from the
  nonnegativity of the loss defined in
  \cref{def:majority-loss,def:majority-loss-constant}.  Suppose instead that
  $I$ has $n>0$ constraints, and set
  \[
    C=2^{k_{\max}}\frac{600k_{\max}}{\sqrt{\varepsilon}}.
  \]
  For every $j$, nonnegativity gives
  $\max\{\varepsilon,\gamma_j\}\leq\varepsilon+\gamma_j$.  The arity bound in
  \cref{def:promise-template}, together with monotonicity of $k\mapsto2^k$,
  therefore gives $p_j\leq C(\varepsilon+\gamma_j)$.  Summing over $j$ yields
  \[
    \sum_jp_j\leq C\left(n\varepsilon+\sum_j\gamma_j\right).
  \]
  The hypothesis on the finite average is, again by
  \cref{def:finite-average}, equivalent to
  $\sum_j\gamma_j\leq n\varepsilon$.  Hence
  $\sum_jp_j\leq2Cn\varepsilon$, and division by the positive number $n$
  bounds the average failure probability by $2C\varepsilon$.  Since
  $\varepsilon>0$, one has
  $\varepsilon=(\sqrt{\varepsilon})^2$ and therefore
  $2C\varepsilon=1200\cdot2^{k_{\max}}k_{\max}\sqrt{\varepsilon}$.
  Expanding \cref{def:majority-loss,def:majority-loss-constant} identifies
  this last expression with the asserted loss. -/)
  (title := /-- Averaging the rounded constraint failures -/)
  (latexEnv := "lemma")]
lemma cmm_average_clause_failure {Γ : promise_template}
    (A : uniform_randomized_algorithm Γ) (ε : ℝ) (I : pcsp_instance Γ)
    (γ : Fin I.constraintCount → ℝ)
    (hε : 0 < ε) (hγ : ∀ j, 0 ≤ γ j)
    (hAverage : finite_average γ ≤ ε)
    (hFailure :
      ∀ j : Fin I.constraintCount,
        constraint_failure_probability A ε I j ≤
          (2 : ℝ) ^ Γ.arity (I.constraint j).relation *
            (600 * Γ.arity (I.constraint j).relation *
              max ε (γ j) / Real.sqrt ε)) :
    finite_average (constraint_failure_probability A ε I) ≤
      majority_loss Γ ε := by
  classical
  by_cases hI : Nonempty (Fin I.constraintCount)
  · simp [finite_average, hI] at hAverage ⊢
    have hsqrt : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
    have hcount : 0 < (I.constraintCount : ℝ) := by
      have hcountNat : 0 < I.constraintCount := by
        simpa using Fintype.card_pos_iff.mpr hI
      exact_mod_cast hcountNat
    let C : ℝ :=
      (2 : ℝ) ^ Γ.maxArity * (600 * Γ.maxArity / Real.sqrt ε)
    have hC : 0 ≤ C := by
      dsimp [C]
      positivity
    have hpoint (j : Fin I.constraintCount) :
        constraint_failure_probability A ε I j ≤ C * (ε + γ j) := by
      have hq : 0 ≤ ε + γ j := by
        linarith [hγ j]
      calc
        constraint_failure_probability A ε I j ≤
            (2 : ℝ) ^ Γ.arity (I.constraint j).relation *
              (600 * Γ.arity (I.constraint j).relation *
                max ε (γ j) / Real.sqrt ε) := hFailure j
        _ ≤ (2 : ℝ) ^ Γ.arity (I.constraint j).relation *
              (600 * Γ.arity (I.constraint j).relation *
                (ε + γ j) / Real.sqrt ε) := by
          gcongr
          exact max_le (by linarith [hγ j]) (by linarith)
        _ ≤ (2 : ℝ) ^ Γ.maxArity *
              (600 * Γ.maxArity * (ε + γ j) / Real.sqrt ε) := by
          gcongr
          · norm_num
          · exact Γ.arity_le_max _
          · exact Γ.arity_le_max _
        _ = C * (ε + γ j) := by
          dsimp [C]
          ring
    have hsum :
        ∑ j, constraint_failure_probability A ε I j ≤
          C * ((I.constraintCount : ℝ) * ε + ∑ j, γ j) := by
      calc
        ∑ j, constraint_failure_probability A ε I j ≤
            ∑ j, C * (ε + γ j) :=
          Finset.sum_le_sum fun j _ => hpoint j
        _ = C * ((I.constraintCount : ℝ) * ε + ∑ j, γ j) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
          simp
    have hsumγ :
        ∑ j, γ j ≤ (I.constraintCount : ℝ) * ε := by
      have := (div_le_iff₀ hcount).mp hAverage
      simpa [mul_comm] using this
    have htotal :
        ∑ j, constraint_failure_probability A ε I j ≤
          C * (2 * ((I.constraintCount : ℝ) * ε)) := by
      refine hsum.trans (mul_le_mul_of_nonneg_left ?_ hC)
      linarith
    apply (div_le_iff₀ hcount).2
    refine htotal.trans_eq ?_
    dsimp [C, majority_loss, majority_loss_constant]
    field_simp [ne_of_gt hsqrt]
    rw [Real.sq_sqrt hε.le]
    ring
  · simp [finite_average, hI, majority_loss, majority_loss_constant]
    positivity

@[blueprint "lem:expected-weak-satisfaction-identity"
  (statement := /-- For every promise template $\Gamma$, uniform randomized
  algorithm $A$, real parameter $\varepsilon$, and finite instance $I$ over
  $\Gamma$, the expected weak satisfaction fraction of $A$ on $I$ at
  $\varepsilon$ equals one minus the finite average of the individual weak
  failure probabilities. -/)
  (proof := /-- The real masses of the probability mass function sum to one.
  If the constraint type is empty, \cref{def:satisfaction-fraction} assigns
  value one to every assignment, whereas \cref{def:finite-average} assigns
  value zero to the family of failure probabilities, so the identity follows.
  Suppose that the constraint type is nonempty.  By
  \cref{def:weak-satisfaction-fraction} and
  \cref{def:satisfaction-fraction}, for each assignment the number of weakly
  satisfied constraints plus the sum of the complementary failure indicators
  is the total number of constraints.  Multiply this equality by the
  assignment's probability mass and sum over all assignments.  The
  normalization of the probability mass function shows that the resulting
  satisfaction contribution plus the failure contribution equals the number
  of constraints.  Finally, expand
  \cref{def:expected-weak-satisfaction} and
  \cref{def:constraint-failure-probability}, interchange the two finite sums
  in the failure contribution, and divide by the nonzero number of constraints.
  The definition \cref{def:finite-average} then gives the asserted
  identity. -/)
  (title := /-- Expected satisfaction as one minus average failure -/)
  (latexEnv := "lemma")]
lemma expected_weak_satisfaction_identity {Γ : promise_template}
    (A : uniform_randomized_algorithm Γ) (ε : ℝ) (I : pcsp_instance Γ) :
    expected_weak_satisfaction A ε I =
      1 - finite_average (constraint_failure_probability A ε I) := by
  classical
  have hsum :
      ∑ assignment : pcsp_assignment I, (A.run ε I assignment).toReal = 1 := by
    calc
      ∑ assignment : pcsp_assignment I, (A.run ε I assignment).toReal =
          ∑' assignment : pcsp_assignment I, (A.run ε I assignment).toReal := by
            rw [tsum_fintype]
      _ = (∑' assignment : pcsp_assignment I, A.run ε I assignment).toReal := by
            rw [ENNReal.tsum_toReal_eq]
            exact fun assignment => PMF.apply_ne_top (A.run ε I) assignment
      _ = 1 := by rw [PMF.tsum_coe]; norm_num
  by_cases h : Nonempty (Fin I.constraintCount)
  · letI : Nonempty (Fin I.constraintCount) := h
    have hn : (Fintype.card (Fin I.constraintCount) : ℝ) ≠ 0 := by
      exact_mod_cast
        (Fintype.card_ne_zero : Fintype.card (Fin I.constraintCount) ≠ 0)
    have hpartition (assignment : pcsp_assignment I) :
        ((Finset.univ.filter fun j : Fin I.constraintCount =>
            weakly_satisfies_constraint I assignment j).card : ℝ) +
          (∑ j : Fin I.constraintCount,
            if weakly_satisfies_constraint I assignment j then 0 else 1) =
          Fintype.card (Fin I.constraintCount) := by
      rw [show (∑ j : Fin I.constraintCount,
          if weakly_satisfies_constraint I assignment j then (0 : ℝ) else 1) =
        ((Finset.univ.filter fun j : Fin I.constraintCount =>
          ¬ weakly_satisfies_constraint I assignment j).card : ℝ) by
            simp [Finset.sum_ite]]
      exact_mod_cast Finset.card_filter_add_card_filter_not
        (s := Finset.univ)
        (p := fun j : Fin I.constraintCount =>
          weakly_satisfies_constraint I assignment j)
    have hweighted (assignment : pcsp_assignment I) :
        (A.run ε I assignment).toReal *
            ((Finset.univ.filter fun j : Fin I.constraintCount =>
              weakly_satisfies_constraint I assignment j).card : ℝ) +
          (∑ j : Fin I.constraintCount,
            (A.run ε I assignment).toReal *
              if weakly_satisfies_constraint I assignment j then 0 else 1) =
          (A.run ε I assignment).toReal *
            Fintype.card (Fin I.constraintCount) := by
      rw [← Finset.mul_sum, ← mul_add, hpartition]
    have htotal :
        (∑ assignment : pcsp_assignment I,
            (A.run ε I assignment).toReal *
              ((Finset.univ.filter fun j : Fin I.constraintCount =>
                weakly_satisfies_constraint I assignment j).card : ℝ)) +
          (∑ assignment : pcsp_assignment I, ∑ j : Fin I.constraintCount,
            (A.run ε I assignment).toReal *
              if weakly_satisfies_constraint I assignment j then 0 else 1) =
          Fintype.card (Fin I.constraintCount) := by
      rw [← Finset.sum_add_distrib]
      calc
        _ = ∑ assignment : pcsp_assignment I,
            (A.run ε I assignment).toReal *
              Fintype.card (Fin I.constraintCount) := by
              apply Finset.sum_congr rfl
              intro assignment _
              exact hweighted assignment
        _ = (∑ assignment : pcsp_assignment I,
              (A.run ε I assignment).toReal) *
              Fintype.card (Fin I.constraintCount) := by
              rw [Finset.sum_mul]
        _ = Fintype.card (Fin I.constraintCount) := by rw [hsum, one_mul]
    simp only [expected_weak_satisfaction, weak_satisfaction_fraction,
      satisfaction_fraction, finite_average, constraint_failure_probability, h,
      dif_pos]
    rw [Finset.sum_comm]
    calc
      _ = (∑ assignment : pcsp_assignment I,
            (A.run ε I assignment).toReal *
              ((Finset.univ.filter fun j : Fin I.constraintCount =>
                weakly_satisfies_constraint I assignment j).card : ℝ)) /
            Fintype.card (Fin I.constraintCount) := by
              rw [div_eq_mul_inv, Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro assignment _
              ring
      _ = 1 - (∑ assignment : pcsp_assignment I, ∑ j : Fin I.constraintCount,
            (A.run ε I assignment).toReal *
              if weakly_satisfies_constraint I assignment j then 0 else 1) /
            Fintype.card (Fin I.constraintCount) := by
              field_simp [hn]
              linarith
  · simp [expected_weak_satisfaction, weak_satisfaction_fraction,
      satisfaction_fraction, finite_average, constraint_failure_probability, h,
      hsum]

@[blueprint "lem:expected-weak-satisfaction-from-failures"
  (statement := /-- For every promise template $\Gamma$, uniform randomized
  algorithm $A$ over $\Gamma$, real parameter $\varepsilon$, finite instance
  $I$ over $\Gamma$, and real number $L$, if the finite average of the
  per-constraint weak failure probabilities of $A$ on $I$ at $\varepsilon$ is
  at most $L$, then the expected weak satisfaction fraction is at least
  $1-L$. -/)
  (proof := /-- By
  \cref{lem:expected-weak-satisfaction-identity}, the expected weak
  satisfaction fraction equals one minus the finite average failure
  probability.  Subtracting the two sides of the assumed failure inequality
  from one reverses their order and gives the asserted lower bound. -/)
  (title := /-- From average failure to expected satisfaction -/)
  (latexEnv := "lemma")]
lemma expected_weak_satisfaction_from_failures {Γ : promise_template}
    (A : uniform_randomized_algorithm Γ) (ε : ℝ) (I : pcsp_instance Γ)
    (L : ℝ)
    (hFailure :
      finite_average (constraint_failure_probability A ε I) ≤ L) :
    1 - L ≤ expected_weak_satisfaction A ε I := by
  simpa [expected_weak_satisfaction_identity] using sub_le_sub_left hFailure 1

@[blueprint "lem:majority-rounding-is-robust"
  (statement := /-- Let $\Gamma$ be a Boolean promise template that admits
  every odd-arity Majority polymorphism.  Then there exists a uniform
  randomized algorithm $A$ for $\Gamma$ that runs in polynomial time and has
  the following property.  For every real number $0<\varepsilon\leq 1$ and
  every finite $\Gamma$-instance whose strong constraints are satisfied by
  some assignment on at least a $1-\varepsilon$ fraction of the constraints,
  the expected fraction of weakly satisfied constraints produced by $A$ is at
  least
  $1-1200\cdot2^{k_{\max}}k_{\max}\sqrt{\varepsilon}$, where
  $k_{\max}=\Gamma.\mathsf{maxArity}$. -/)
  (proof := /-- Choose the uniform polynomial-time algorithm and, for each
  admissible input, the local errors supplied by
  \cref{lem:majority-sdp-cmm-profile}.  For each constraint, apply
  \cref{lem:cmm-clause-union-bound} to the per-tuple estimate.  The
  nonnegativity and average bound for the local errors then permit
  \cref{lem:cmm-average-clause-failure}, which bounds the average weak failure
  probability by $\ell_\Gamma(\varepsilon)$.  Apply
  \cref{lem:expected-weak-satisfaction-from-failures} to obtain the required
  expected weak-satisfaction lower bound.  The chosen algorithm is independent
  of both the instance and $\varepsilon$, and its polynomial-time bound is the
  one supplied with the same choice. -/)
  (title := /-- Robustness of Majority rounding -/)
  (latexEnv := "lemma")]
lemma majority_rounding_is_robust (Γ : promise_template)
    (hMajority : admits_majority Γ) :
    ∃ A : uniform_randomized_algorithm Γ,
      polynomial_time A ∧ robust_with_loss A (majority_loss Γ) := by
  obtain ⟨A, hPolynomial, hProfile⟩ :=
    majority_sdp_cmm_profile Γ hMajority
  refine ⟨A, hPolynomial, ?_⟩
  intro ε hε hε_le_one I hI
  obtain ⟨γ, hγ, hAverage, hTuple⟩ :=
    hProfile ε hε hε_le_one I hI
  have hFailure := cmm_clause_union_bound A ε I γ hTuple
  have hAverageFailure :=
    cmm_average_clause_failure A ε I γ hε hγ hAverage hFailure
  exact expected_weak_satisfaction_from_failures A ε I
    (majority_loss Γ ε) hAverageFailure

@[blueprint "lem:majority-loss-is-big-o"
  (statement := /-- Let $\Gamma$ be a Boolean promise template, and write
  $k_{\max}=\Gamma.\mathsf{maxArity}$.  Then the function
  $\ell_\Gamma(\varepsilon)=
  1200\cdot2^{k_{\max}}k_{\max}\sqrt{\varepsilon}$ is
  $O_\Gamma(\sqrt{\varepsilon})$ as $\varepsilon\to0$ through nonnegative
  real values. -/)
  (proof := /-- By \cref{def:majority-loss}, $\ell_\Gamma$ is the product of
  the fixed real constant $1200\cdot2^{k_{\max}}k_{\max}$ and the function
  $\varepsilon\mapsto\sqrt{\varepsilon}$.  The latter function is Big-O of
  itself by reflexivity, and multiplication on the left by a fixed constant
  preserves the Big-O relation.  Hence
  $\ell_\Gamma(\varepsilon)=O_\Gamma(\sqrt{\varepsilon})$. -/)
  (title := /-- Square-root asymptotics of the Majority loss -/)
  (latexEnv := "lemma")]
lemma majority_loss_is_big_o (Γ : promise_template) :
    majority_loss Γ =O[nhdsWithin 0 (Set.Ici 0)] fun ε : ℝ => Real.sqrt ε := by
  exact (Asymptotics.isBigO_refl (fun ε : ℝ => Real.sqrt ε)
    (nhdsWithin 0 (Set.Ici 0))).const_mul_left (majority_loss_constant Γ)

@[blueprint "thm:robust-MAJ"
  (statement := /-- Let $\Gamma$ be a Boolean promise template such that every
  odd-arity Majority operation is a polymorphism from each strong relation to
  its corresponding weak relation.  Then $\operatorname{PCSP}(\Gamma)$ has a
  uniform polynomial-time randomized robust algorithm with a loss function
  $f$ satisfying $f(\varepsilon)=O_\Gamma(\sqrt{\varepsilon})$ as
  $\varepsilon\to0$ through nonnegative values. -/)
  (proof := /-- By \cref{lem:majority-rounding-is-robust}, choose a single
  uniform polynomial-time randomized algorithm robust with loss
  $f=\ell_\Gamma$.  The asymptotic estimate
  \cref{lem:majority-loss-is-big-o} states that this loss is
  $O_\Gamma(\sqrt{\varepsilon})$ at zero.  These two assertions provide the
  required algorithm and loss function. -/)
  (title := /-- Robust satisfiability from Majority polymorphisms -/)
  (latexEnv := "theorem")]
theorem robust_MAJ (Γ : promise_template) (hMajority : admits_majority Γ) :
    ∃ (A : uniform_randomized_algorithm Γ) (loss : ℝ → ℝ),
      polynomial_time A ∧
      robust_with_loss A loss ∧
      loss =O[nhdsWithin 0 (Set.Ici 0)] fun ε : ℝ => Real.sqrt ε := by
  rcases majority_rounding_is_robust Γ hMajority with
    ⟨A, hPolynomial, hRobust⟩
  exact ⟨A, majority_loss Γ, hPolynomial, hRobust,
    majority_loss_is_big_o Γ⟩

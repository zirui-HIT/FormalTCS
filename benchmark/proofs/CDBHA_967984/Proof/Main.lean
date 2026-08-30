import Architect
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.Compact

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:submodular-inspection-cost"
  (statement := /-- Let $A$ be a finite type and let $v\colon 2^A\to\mathbb{R}$.  The function $v$ has decreasing marginals if, for all $S\subseteq T\subseteq A$ and every $a\in A$,
  \[
  v(S\cup\{a\})-v(S)\geq v(T\cup\{a\})-v(T).
  \]
  This is the paper's formulation of submodularity. -/)
  (title := /-- Submodular inspection cost -/)
  (latexEnv := "definition")]
def submodular_inspection_cost {A : Type} [DecidableEq A]
    (v : Finset A → ℝ) : Prop :=
  ∀ S T : Finset A, S ⊆ T →
    ∀ a : A, v (insert a S) - v S ≥ v (insert a T) - v T

@[blueprint "def:contract-data"
  (statement := /-- For a finite action space $A$, contract data consist of an action cost $c\colon A\to\mathbb{R}$, a binary-success probability $f\colon A\to\mathbb{R}$, an inspection cost $v\colon 2^A\to\mathbb{R}$, and a distinguished null action $\bot\in A$. -/)
  (title := /-- Contract data -/)
  (latexEnv := "definition")]
structure contract_data (A : Type) [Fintype A] [DecidableEq A] where
  cost : A → ℝ
  success : A → ℝ
  inspectionCost : Finset A → ℝ
  nullAction : A

@[blueprint "def:admissible-contract-data"
  (statement := /-- Contract data $(A,c,f,v,\bot)$ are admissible if $c$ and $v$ are nonnegative, $0\leq f(a)\leq1$ for every $a\in A$, $v(\varnothing)=0$, $v$ is monotone under inclusion, and $c(\bot)=0$.  The principal's reward upon success is normalized to $1$ in the utility definition below. -/)
  (title := /-- Admissible inspection instance -/)
  (latexEnv := "definition")]
def admissible_contract_data {A : Type} [Fintype A] [DecidableEq A]
    (d : contract_data A) : Prop :=
  (∀ a : A, 0 ≤ d.cost a) ∧
  (∀ a : A, 0 ≤ d.success a ∧ d.success a ≤ 1) ∧
  (∀ S : Finset A, 0 ≤ d.inspectionCost S) ∧
  d.inspectionCost ∅ = 0 ∧
  Monotone d.inspectionCost ∧
  d.cost d.nullAction = 0

@[blueprint "def:inspection-distribution"
  (statement := /-- An inspection distribution on a finite action space $A$ is a nonnegative real weight $p(S)$ for every $S\subseteq A$ such that $\sum_{S\subseteq A}p(S)=1$. -/)
  (title := /-- Inspection distribution -/)
  (latexEnv := "definition")]
structure inspection_distribution (A : Type) [Fintype A] [DecidableEq A] where
  mass : Finset A → ℝ
  mass_nonneg : ∀ S : Finset A, 0 ≤ mass S
  total_mass : Finset.univ.powerset.sum mass = 1

@[blueprint "def:inspection-support"
  (statement := /-- The support of an inspection distribution $p$ is the finite family of subsets $S\subseteq A$ for which $p(S)\neq0$. -/)
  (title := /-- Support of an inspection distribution -/)
  (latexEnv := "definition")]
noncomputable def inspection_support {A : Type} [Fintype A] [DecidableEq A]
    (p : inspection_distribution A) : Finset (Finset A) := by
  classical
  exact Finset.univ.powerset.filter fun S => p.mass S ≠ 0

@[blueprint "def:inspection-marginal"
  (statement := /-- For an inspection distribution $p$ and an action $a\in A$, its inspection marginal is
  \[
  p(a)=\sum_{S\subseteq A:\,a\in S}p(S).
  \] -/)
  (title := /-- Marginal inspection probability -/)
  (latexEnv := "definition")]
def inspection_marginal {A : Type} [Fintype A] [DecidableEq A]
    (p : inspection_distribution A) (a : A) : ℝ :=
  (Finset.univ.powerset.filter fun S => a ∈ S).sum p.mass

@[blueprint "def:detection-probability"
  (statement := /-- In the fully observable model, if action $i$ is suggested and action $j$ is taken, the deviation is detected precisely when the inspected set contains $i$ or $j$.  Its probability is
  \[
  \sum_{S\subseteq A:\,\{i,j\}\cap S\neq\varnothing}p(S).
  \] -/)
  (title := /-- Probability of detecting a deviation -/)
  (latexEnv := "definition")]
def detection_probability {A : Type} [Fintype A] [DecidableEq A]
    (p : inspection_distribution A) (i j : A) : ℝ :=
  (Finset.univ.powerset.filter fun S => i ∈ S ∨ j ∈ S).sum p.mass

@[blueprint "def:expected-inspection-cost"
  (statement := /-- The expected cost of an inspection distribution $p$ under a set cost $v$ is
  \[
  \mathbb{E}_p[v]=\sum_{S\subseteq A}p(S)v(S).
  \] -/)
  (title := /-- Expected inspection cost -/)
  (latexEnv := "definition")]
def expected_inspection_cost {A : Type} [Fintype A] [DecidableEq A]
    (v : Finset A → ℝ) (p : inspection_distribution A) : ℝ :=
  Finset.univ.powerset.sum fun S => p.mass S * v S

@[blueprint "def:inspection-scheme"
  (statement := /-- An inspection scheme consists of a suggested action $i\in A$, a success-contingent payment share $\alpha\in\mathbb{R}$, and an inspection distribution $p$ on $2^A$. -/)
  (title := /-- Inspection scheme -/)
  (latexEnv := "definition")]
structure inspection_scheme (A : Type) [Fintype A] [DecidableEq A] where
  suggested : A
  payment : ℝ
  inspection : inspection_distribution A

@[blueprint "def:agent-utility"
  (statement := /-- Given contract data $d$, a scheme $(i,\alpha,p)$, and an action $j$, the agent's expected utility is $\alpha f(i)-c(i)$ when $j=i$, and otherwise is
  \[
  \alpha f(j)\bigl(1-\Pr_p[\{i,j\}\cap S\neq\varnothing]\bigr)-c(j).
  \]
  Thus a detected deviation receives no success-contingent payment. -/)
  (title := /-- Agent utility -/)
  (latexEnv := "definition")]
def agent_utility {A : Type} [Fintype A] [DecidableEq A]
    (d : contract_data A) (s : inspection_scheme A) (j : A) : ℝ :=
  if j = s.suggested then
    s.payment * d.success j - d.cost j
  else
    s.payment * d.success j *
      (1 - detection_probability s.inspection s.suggested j) - d.cost j

@[blueprint "def:principal-utility"
  (statement := /-- If action $j$ is taken under a scheme $(i,\alpha,p)$, the principal's expected utility is the normalized reward net of payment and expected inspection cost:
  \[
  (1-\alpha)f(j)-\mathbb{E}_p[v].
  \] -/)
  (title := /-- Principal utility -/)
  (latexEnv := "definition")]
def principal_utility {A : Type} [Fintype A] [DecidableEq A]
    (d : contract_data A) (s : inspection_scheme A) (j : A) : ℝ :=
  (1 - s.payment) * d.success j -
    expected_inspection_cost d.inspectionCost s.inspection

@[blueprint "def:incentive-compatible"
  (statement := /-- A scheme $(i,\alpha,p)$ is incentive-compatible if the suggested action $i$ maximizes the agent's utility: for every $j\in A$,
  \[
  u_{\mathrm{agent}}(i,\alpha,p,j)
  \leq u_{\mathrm{agent}}(i,\alpha,p,i).
  \]
  This weak inequality implements tie-breaking in favor of the suggestion. -/)
  (title := /-- Incentive compatibility -/)
  (latexEnv := "definition")]
def incentive_compatible {A : Type} [Fintype A] [DecidableEq A]
    (d : contract_data A) (s : inspection_scheme A) : Prop :=
  ∀ j : A, agent_utility d s j ≤ agent_utility d s s.suggested

@[blueprint "def:feasible-inspection-scheme"
  (statement := /-- A scheme is feasible if its payment satisfies $0\leq\alpha\leq1$ and it is incentive-compatible. -/)
  (title := /-- Feasible inspection scheme -/)
  (latexEnv := "definition")]
def feasible_inspection_scheme {A : Type} [Fintype A] [DecidableEq A]
    (d : contract_data A) (s : inspection_scheme A) : Prop :=
  0 ≤ s.payment ∧ s.payment ≤ 1 ∧ incentive_compatible d s

@[blueprint "def:optimal-inspection-scheme"
  (statement := /-- A feasible scheme is optimal if its principal utility under the suggested action is at least that of every feasible inspection scheme, including schemes with a different suggested action. -/)
  (title := /-- Optimal inspection scheme -/)
  (latexEnv := "definition")]
def optimal_inspection_scheme {A : Type} [Fintype A] [DecidableEq A]
    (d : contract_data A) (s : inspection_scheme A) : Prop :=
  feasible_inspection_scheme d s ∧
  ∀ t : inspection_scheme A, feasible_inspection_scheme d t →
    principal_utility d t t.suggested ≤ principal_utility d s s.suggested

@[blueprint "def:suggested-action-separated"
  (statement := /-- An inspection distribution is separated at $i$ if every positive-mass inspected set containing $i$ is the singleton $\{i\}$. -/)
  (title := /-- Separation of the suggested action -/)
  (latexEnv := "definition")]
def suggested_action_separated {A : Type} [Fintype A] [DecidableEq A]
    (i : A) (p : inspection_distribution A) : Prop :=
  ∀ S : Finset A, p.mass S ≠ 0 → i ∈ S → S = {i}

@[blueprint "def:nested-inspection-support-away-from"
  (statement := /-- An inspection distribution has nested support away from $i$ if any two positive-mass inspected sets not containing $i$ are comparable by inclusion.  The distinguished singleton $\{i\}$ is not required to be comparable with this chain. -/)
  (title := /-- Nested inspection support away from one action -/)
  (latexEnv := "definition")]
def nested_inspection_support_away_from
    {A : Type} [Fintype A] [DecidableEq A]
    (i : A) (p : inspection_distribution A) : Prop :=
  ∀ S ∈ inspection_support p, i ∉ S →
    ∀ T ∈ inspection_support p, i ∉ T → S ⊆ T ∨ T ⊆ S

@[blueprint "def:replace-inspection-cost"
  (statement := /-- If $d$ are contract data and $v'$ is another set function, then $d[v\leftarrow v']$ denotes the data obtained by replacing only the inspection-cost oracle by $v'$. -/)
  (title := /-- Replacement of the inspection-cost oracle -/)
  (latexEnv := "definition")]
def replace_inspection_cost {A : Type} [Fintype A] [DecidableEq A]
    (d : contract_data A) (v' : Finset A → ℝ) : contract_data A :=
  { d with inspectionCost := v' }

@[blueprint "def:oracle-instruction"
  (statement := /-- An oracle-machine instruction is one operation of a first-order register language.  Natural-number instructions load constants, copy registers, add, subtract, or branch on a comparison.  Real-register instructions load rational constants, copy registers, apply a field operation or the real square-root operation, or branch on a comparison.  Input instructions load the length of the finite action encoding, read an action at a specified in-range index, or read the cost, success probability, or null action.  Set instructions create a set, insert or erase one action, or query the inspection-cost oracle on a set register.  Output instructions explicitly select the suggested action, payment, and one support mass, and the halt instruction terminates execution.  Every operand and continuation address is a natural-number register or program address; in particular, no instruction contains a Lean function or higher-order continuation. -/)
  (title := /-- First-order value-oracle machine instructions -/)
  (latexEnv := "definition")]
inductive oracle_instruction where
  | loadNat (value destination next : ℕ)
  | copyNat (source destination next : ℕ)
  | addNat (left right destination next : ℕ)
  | subNat (left right destination next : ℕ)
  | branchNatLE (left right yes no : ℕ)
  | loadEncodingLength (destination next : ℕ)
  | loadAction (indexRegister actionRegister next : ℕ)
  | readCost (actionRegister realRegister next : ℕ)
  | readSuccess (actionRegister realRegister next : ℕ)
  | readNullAction (actionRegister next : ℕ)
  | clearSet (setRegister next : ℕ)
  | insertAction (actionRegister setRegister next : ℕ)
  | eraseAction (actionRegister setRegister next : ℕ)
  | valueQuery (setRegister realRegister next : ℕ)
  | loadReal (numerator : ℤ) (denominator realRegister next : ℕ)
  | copyReal (source destination next : ℕ)
  | addReal (left right destination next : ℕ)
  | subReal (left right destination next : ℕ)
  | mulReal (left right destination next : ℕ)
  | divReal (left right destination next : ℕ)
  | sqrtReal (source destination next : ℕ)
  | branchRealLE (left right yes no : ℕ)
  | setSuggested (actionRegister next : ℕ)
  | setPayment (realRegister next : ℕ)
  | clearMasses (next : ℕ)
  | appendMass (setRegister realRegister next : ℕ)
  | halt

@[blueprint "def:raw-inspection-scheme"
  (statement := /-- A raw inspection scheme consists of a suggested action, a real payment, and a finite list of inspected sets with real masses.  The list is the concrete output representation assembled by the oracle machine; repeated occurrences of a set contribute additively to its mass. -/)
  (title := /-- Finite machine representation of an inspection scheme -/)
  (latexEnv := "definition")]
structure raw_inspection_scheme (A : Type) where
  suggested : A
  payment : ℝ
  masses : List (Finset A × ℝ)

@[blueprint "def:raw-inspection-mass"
  (statement := /-- For a raw inspection scheme $r$ and a set $S$, the decoded mass of $S$ is the sum of the second coordinates of all entries of the output list whose first coordinate is $S$. -/)
  (title := /-- Mass decoded from a finite output list -/)
  (latexEnv := "definition")]
def raw_inspection_mass {A : Type} [DecidableEq A]
    (r : raw_inspection_scheme A) (S : Finset A) : ℝ :=
  r.masses.foldr
    (fun entry total => if entry.1 = S then entry.2 + total else total) 0

@[blueprint "def:valid-raw-inspection-scheme"
  (statement := /-- A raw inspection scheme is valid if every decoded mass is nonnegative and the decoded masses of all subsets of the finite action space sum to $1$. -/)
  (title := /-- Validity of a raw machine output -/)
  (latexEnv := "definition")]
def valid_raw_inspection_scheme {A : Type} [Fintype A] [DecidableEq A]
    (r : raw_inspection_scheme A) : Prop :=
  (∀ S : Finset A, 0 ≤ raw_inspection_mass r S) ∧
    Finset.univ.powerset.sum (raw_inspection_mass r) = 1

@[blueprint "def:decode-raw-inspection-scheme"
  (statement := /-- Every valid raw inspection scheme decodes to an inspection scheme by retaining its suggested action and payment and assigning to each set its decoded mass. -/)
  (title := /-- Decode a valid machine output -/)
  (latexEnv := "definition")]
def decode_raw_inspection_scheme {A : Type} [Fintype A] [DecidableEq A]
    (r : raw_inspection_scheme A) (hvalid : valid_raw_inspection_scheme r) :
    inspection_scheme A :=
  { suggested := r.suggested
    payment := r.payment
    inspection :=
      { mass := raw_inspection_mass r
        mass_nonneg := hvalid.1
        total_mass := hvalid.2 } }

@[blueprint "def:action-encoding"
  (statement := /-- An action encoding is a repetition-free list containing every action.  It is the finite input representation through which a uniform oracle program addresses an otherwise abstract finite action type. -/)
  (title := /-- Finite enumeration of the action space -/)
  (latexEnv := "definition")]
def action_encoding {A : Type} (encoding : List A) : Prop :=
  encoding.Nodup ∧ ∀ a : A, a ∈ encoding

@[blueprint "def:oracle-machine-state"
  (statement := /-- A state of the oracle register machine contains its program counter; natural, real, action, and finite-set register banks; the partially assembled output; the ordered value-query transcript; charged instruction and work counters; and a halt flag.  Register banks are initialized uniformly and can thereafter change only through the first-order transition relation. -/)
  (title := /-- State of the costed oracle machine -/)
  (latexEnv := "definition")]
structure oracle_machine_state (A : Type) [DecidableEq A] where
  programCounter : ℕ
  naturalRegisters : ℕ → ℕ
  realRegisters : ℕ → ℝ
  actionRegisters : ℕ → Option A
  setRegisters : ℕ → Finset A
  suggested : Option A
  payment : ℝ
  masses : List (Finset A × ℝ)
  queries : List (Finset A)
  steps : ℕ
  work : ℕ
  halted : Bool

@[blueprint "def:oracle-initial-state"
  (statement := /-- The initial oracle-machine state has program counter $0$, zero natural and real registers, empty action registers and set registers, no suggested action, zero payment, empty output and query lists, zero counters, and a false halt flag. -/)
  (title := /-- Initial oracle-machine state -/)
  (latexEnv := "definition")]
def oracle_initial_state (A : Type) [DecidableEq A] : oracle_machine_state A :=
  { programCounter := 0
    naturalRegisters := fun _ => 0
    realRegisters := fun _ => 0
    actionRegisters := fun _ => none
    setRegisters := fun _ => ∅
    suggested := none
    payment := 0
    masses := []
    queries := []
    steps := 0
    work := 0
    halted := false }

@[blueprint "def:oracle-machine-step"
  (statement := /-- Fix contract data $d$, an action encoding, and a finite instruction list.  A machine step fetches the instruction at the current program counter and performs exactly its specified register update.  Every step increments the step counter.  The work counter charges at least the program length for instruction dispatch; it additionally charges the input-list scan for reading the encoding length, the addressed input prefix for action lookup, and the current set cardinality for set manipulation and oracle queries.  Register access, action equality, exact real field arithmetic, exact real square root, and real comparison are the explicitly declared unit-cost primitives of this oracle-RAM model.  The square-root instruction sends a register value $x$ to the nonnegative real square root of $x$ when $x\geq0$, and to $0$ when $x<0$.  A value query is the only case that reads $v$, and it appends its queried set to the transcript.  Output fields change only under the corresponding output instructions. -/)
  (title := /-- Fully costed first-order machine transition -/)
  (latexEnv := "definition")]
def oracle_machine_step {A : Type} [Fintype A] [DecidableEq A]
    (d : contract_data A) (encoding : List A) (program : List oracle_instruction)
    (s t : oracle_machine_state A) : Prop :=
  s.halted = false ∧
    match program[s.programCounter]? with
    | none => False
    | some instruction =>
      let dispatchCost := program.length + 1
      match instruction with
      | .loadNat value destination next =>
          t = { s with
            programCounter := next
            naturalRegisters := Function.update s.naturalRegisters destination value
            steps := s.steps + 1
            work := s.work + dispatchCost }
      | .copyNat source destination next =>
          t = { s with
            programCounter := next
            naturalRegisters :=
              Function.update s.naturalRegisters destination (s.naturalRegisters source)
            steps := s.steps + 1
            work := s.work + dispatchCost }
      | .addNat left right destination next =>
          t = { s with
            programCounter := next
            naturalRegisters := Function.update s.naturalRegisters destination
              (s.naturalRegisters left + s.naturalRegisters right)
            steps := s.steps + 1
            work := s.work + dispatchCost }
      | .subNat left right destination next =>
          t = { s with
            programCounter := next
            naturalRegisters := Function.update s.naturalRegisters destination
              (s.naturalRegisters left - s.naturalRegisters right)
            steps := s.steps + 1
            work := s.work + dispatchCost }
      | .branchNatLE left right yes no =>
          t = { s with
            programCounter :=
              if s.naturalRegisters left ≤ s.naturalRegisters right then yes else no
            steps := s.steps + 1
            work := s.work + dispatchCost }
      | .loadEncodingLength destination next =>
          t = { s with
            programCounter := next
            naturalRegisters :=
              Function.update s.naturalRegisters destination encoding.length
            steps := s.steps + 1
            work := s.work + dispatchCost + encoding.length + 1 }
      | .loadAction indexRegister actionRegister next =>
          match encoding[s.naturalRegisters indexRegister]? with
          | none => False
          | some a =>
              t = { s with
                programCounter := next
                actionRegisters := Function.update s.actionRegisters actionRegister (some a)
                steps := s.steps + 1
                work := s.work + dispatchCost + s.naturalRegisters indexRegister + 1 }
      | .readCost actionRegister realRegister next =>
          match s.actionRegisters actionRegister with
          | none => False
          | some a =>
              t = { s with
                programCounter := next
                realRegisters := Function.update s.realRegisters realRegister (d.cost a)
                steps := s.steps + 1
                work := s.work + dispatchCost }
      | .readSuccess actionRegister realRegister next =>
          match s.actionRegisters actionRegister with
          | none => False
          | some a =>
              t = { s with
                programCounter := next
                realRegisters := Function.update s.realRegisters realRegister (d.success a)
                steps := s.steps + 1
                work := s.work + dispatchCost }
      | .readNullAction actionRegister next =>
          t = { s with
            programCounter := next
            actionRegisters :=
              Function.update s.actionRegisters actionRegister (some d.nullAction)
            steps := s.steps + 1
            work := s.work + dispatchCost }
      | .clearSet setRegister next =>
          t = { s with
            programCounter := next
            setRegisters := Function.update s.setRegisters setRegister ∅
            steps := s.steps + 1
            work := s.work + dispatchCost }
      | .insertAction actionRegister setRegister next =>
          match s.actionRegisters actionRegister with
          | none => False
          | some a =>
              t = { s with
                programCounter := next
                setRegisters := Function.update s.setRegisters setRegister
                  (insert a (s.setRegisters setRegister))
                steps := s.steps + 1
                work := s.work + dispatchCost + (s.setRegisters setRegister).card + 1 }
      | .eraseAction actionRegister setRegister next =>
          match s.actionRegisters actionRegister with
          | none => False
          | some a =>
              t = { s with
                programCounter := next
                setRegisters := Function.update s.setRegisters setRegister
                  ((s.setRegisters setRegister).erase a)
                steps := s.steps + 1
                work := s.work + dispatchCost + (s.setRegisters setRegister).card + 1 }
      | .valueQuery setRegister realRegister next =>
          let S := s.setRegisters setRegister
          t = { s with
            programCounter := next
            realRegisters := Function.update s.realRegisters realRegister (d.inspectionCost S)
            queries := S :: s.queries
            steps := s.steps + 1
            work := s.work + dispatchCost + S.card + 1 }
      | .loadReal numerator denominator realRegister next =>
          t = { s with
            programCounter := next
            realRegisters := Function.update s.realRegisters realRegister
              ((numerator : ℝ) / (denominator + 1 : ℝ))
            steps := s.steps + 1
            work := s.work + dispatchCost }
      | .copyReal source destination next =>
          t = { s with
            programCounter := next
            realRegisters :=
              Function.update s.realRegisters destination (s.realRegisters source)
            steps := s.steps + 1
            work := s.work + dispatchCost }
      | .addReal left right destination next =>
          t = { s with
            programCounter := next
            realRegisters := Function.update s.realRegisters destination
              (s.realRegisters left + s.realRegisters right)
            steps := s.steps + 1
            work := s.work + dispatchCost }
      | .subReal left right destination next =>
          t = { s with
            programCounter := next
            realRegisters := Function.update s.realRegisters destination
              (s.realRegisters left - s.realRegisters right)
            steps := s.steps + 1
            work := s.work + dispatchCost }
      | .mulReal left right destination next =>
          t = { s with
            programCounter := next
            realRegisters := Function.update s.realRegisters destination
              (s.realRegisters left * s.realRegisters right)
            steps := s.steps + 1
            work := s.work + dispatchCost }
      | .divReal left right destination next =>
          t = { s with
            programCounter := next
            realRegisters := Function.update s.realRegisters destination
              (s.realRegisters left / s.realRegisters right)
            steps := s.steps + 1
            work := s.work + dispatchCost }
      | .sqrtReal source destination next =>
          t = { s with
            programCounter := next
            realRegisters := Function.update s.realRegisters destination
              (Real.sqrt (s.realRegisters source))
            steps := s.steps + 1
            work := s.work + dispatchCost }
      | .branchRealLE left right yes no =>
          t = { s with
            programCounter := if s.realRegisters left ≤ s.realRegisters right then yes else no
            steps := s.steps + 1
            work := s.work + dispatchCost }
      | .setSuggested actionRegister next =>
          match s.actionRegisters actionRegister with
          | none => False
          | some a =>
              t = { s with
                programCounter := next
                suggested := some a
                steps := s.steps + 1
                work := s.work + dispatchCost }
      | .setPayment realRegister next =>
          t = { s with
            programCounter := next
            payment := s.realRegisters realRegister
            steps := s.steps + 1
            work := s.work + dispatchCost }
      | .clearMasses next =>
          t = { s with
            programCounter := next
            masses := []
            steps := s.steps + 1
            work := s.work + dispatchCost }
      | .appendMass setRegister realRegister next =>
          let S := s.setRegisters setRegister
          t = { s with
            programCounter := next
            masses := (S, s.realRegisters realRegister) :: s.masses
            steps := s.steps + 1
            work := s.work + dispatchCost + S.card + 1 }
      | .halt =>
          t = { s with
            steps := s.steps + 1
            work := s.work + dispatchCost
            halted := true }

@[blueprint "def:oracle-machine-execution"
  (statement := /-- A state is reachable in an oracle-machine execution if it is the uniform initial state or follows by one costed transition from a reachable state.  Hence every reachable state has a finite transition derivation determined by the fixed instruction list and the oracle replies. -/)
  (title := /-- Finite execution of the oracle machine -/)
  (latexEnv := "definition")]
inductive oracle_machine_execution {A : Type} [Fintype A] [DecidableEq A]
    (d : contract_data A) (encoding : List A) (program : List oracle_instruction) :
    oracle_machine_state A → Prop where
  | initial : oracle_machine_execution d encoding program (oracle_initial_state A)
  | step {s t : oracle_machine_state A} :
      oracle_machine_execution d encoding program s →
      oracle_machine_step d encoding program s t →
      oracle_machine_execution d encoding program t

@[blueprint "def:oracle-machine-output"
  (statement := /-- A machine state has a raw output precisely when its suggested-action field is populated; the output consists of that action together with the payment and finite mass list explicitly assembled in the state. -/)
  (title := /-- Raw output extracted from a machine state -/)
  (latexEnv := "definition")]
def oracle_machine_output {A : Type} [DecidableEq A]
    (s : oracle_machine_state A) : Option (raw_inspection_scheme A) :=
  match s.suggested with
  | none => none
  | some i => some ⟨i, s.payment, s.masses⟩

@[blueprint "def:value-oracle-solver"
  (statement := /-- A value-oracle solver is a single finite list of first-order instructions.  The same code is executed for every finite action type and every valid action encoding, so uniformity is literal rather than an unrestricted Lean function producing a different program for each input. -/)
  (title := /-- Uniform first-order value-oracle solver -/)
  (latexEnv := "definition")]
structure value_oracle_solver where
  program : List oracle_instruction

@[blueprint "def:uses-only-value-queries"
  (statement := /-- A solver uses only value queries if every execution is stable under replacing $v$ by a function $v'$ that agrees with $v$ on every set in that execution's query transcript: the identical final state remains reachable with $v'$.  Since \cref{def:oracle-machine-step} reads the inspection-cost function only in its value-query case, this condition captures adaptive black-box access without permitting any hidden read of $v$. -/)
  (title := /-- Black-box use of the value oracle -/)
  (latexEnv := "definition")]
def uses_only_value_queries (solver : value_oracle_solver) : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A]
    (d : contract_data A) (encoding : List A) (final : oracle_machine_state A)
    (v' : Finset A → ℝ), action_encoding encoding →
    oracle_machine_execution d encoding solver.program final →
    (∀ S : Finset A, S ∈ final.queries → v' S = d.inspectionCost S) →
    oracle_machine_execution (replace_inspection_cost d v')
      encoding solver.program final

@[blueprint "def:polynomial-time-value-oracle-solver"
  (statement := /-- A uniform solver runs in polynomial time if there are constants $C,k\in\mathbb{N}$, independent of the action type, its encoding, and the contract data, such that every halted execution on a valid encoding has at most $C(|A|+1)^k$ instructions, charged work, value queries, and output-mass entries.  The work counter is generated solely by the explicit primitive costs in \cref{def:oracle-machine-step}; therefore this bound accounts for query selection, branching, arithmetic, set manipulation, and construction of the returned finite representation. -/)
  (title := /-- Polynomial time in the explicit value-oracle machine model -/)
  (latexEnv := "definition")]
def polynomial_time_value_oracle_solver (solver : value_oracle_solver) : Prop :=
  ∃ C k : ℕ, ∀ (A : Type) [Fintype A] [DecidableEq A]
    (d : contract_data A) (encoding : List A) (final : oracle_machine_state A),
    action_encoding encoding →
    oracle_machine_execution d encoding solver.program final →
    final.halted = true →
    let bound := C * (Fintype.card A + 1) ^ k
    final.steps ≤ bound ∧ final.work ≤ bound ∧
      final.queries.length ≤ bound ∧ final.masses.length ≤ bound

@[blueprint "def:solves-submodular-inspection"
  (statement := /-- A uniform solver solves submodular inspection if, on every valid encoding of every finite admissible submodular instance, a halted execution produces a valid raw scheme whose decoding is optimal and whose inspection support has cardinality at most $|A|+1$. -/)
  (title := /-- Correctness of a submodular-inspection oracle machine -/)
  (latexEnv := "definition")]
def solves_submodular_inspection (solver : value_oracle_solver) : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A]
    (d : contract_data A) (encoding : List A), action_encoding encoding →
    admissible_contract_data d →
    submodular_inspection_cost d.inspectionCost →
    ∃ (final : oracle_machine_state A) (raw : raw_inspection_scheme A)
      (hraw : valid_raw_inspection_scheme raw),
      oracle_machine_execution d encoding solver.program final ∧
      final.halted = true ∧ oracle_machine_output final = some raw ∧
      (let s := decode_raw_inspection_scheme raw hraw
       optimal_inspection_scheme d s ∧
        (inspection_support s.inspection).card ≤ Fintype.card A + 1)

@[blueprint "lem:suggested-action-normalization"
  (statement := /-- Let $A$ be finite, let $v\colon 2^A\to\mathbb{R}$ be monotone, let $i\in A$, and let $p$ be an inspection distribution.  There is an inspection distribution $p'$ separated at $i$ such that every deviation-detection probability from $i$ is unchanged and
  \[
  \mathbb{E}_{p'}[v]\leq\mathbb{E}_{p}[v].
  \] -/)
  (proof := /-- In the notation of \cref{def:inspection-distribution}, define $p'(\{i\})=\sum_{S:\,i\in S}p(S)$, set $p'(S)=0$ for every nonsingleton $S$ containing $i$, and retain $p'(S)=p(S)$ when $i\notin S$.  Nonnegativity of the original masses gives nonnegativity of every new mass, while partitioning the subsets according to whether they contain $i$ shows that their sum is still $1$.  Thus $p'$ is an inspection distribution, and its definition implies the separation condition in \cref{def:suggested-action-separated}.  Fix $j\in A$.  In the event from \cref{def:detection-probability}, all original mass on sets containing $i$ is replaced by the same total mass on $\{i\}$, and the mass of every set not containing $i$ is unchanged.  Splitting the event into these two classes therefore proves that its probability under $p'$ equals its probability under $p$.  Finally, if $i\in S$, monotonicity gives $v(\{i\})\leq v(S)$; multiplication by the nonnegative number $p(S)$ preserves this inequality.  Summing it over the sets containing $i$ and retaining the cost terms for sets not containing $i$ yields the inequality between the expected costs defined in \cref{def:expected-inspection-cost}. -/)
  (title := /-- Normalize inspection at the suggested action -/)
  (latexEnv := "lemma")]
lemma suggested_action_normalization {A : Type} [Fintype A] [DecidableEq A]
    (v : Finset A → ℝ) (hmono : Monotone v)
    (i : A) (p : inspection_distribution A) :
    ∃ p' : inspection_distribution A,
      suggested_action_separated i p' ∧
      (∀ j : A, detection_probability p' i j = detection_probability p i j) ∧
      expected_inspection_cost v p' ≤ expected_inspection_cost v p := by
  classical
  let U : Finset (Finset A) := Finset.univ.powerset
  have hsum_cons (s : Finset (Finset A)) (S : Finset A) (hS : S ∉ s)
      (f : Finset A → ℝ) : (s.cons S hS).sum f = f S + s.sum f := by
    change (Multiset.map f (S ::ₘ s.1)).sum = f S + (Multiset.map f s.1).sum
    rw [Multiset.map_cons]
    unfold Multiset.sum
    rw [Multiset.foldr_cons]
  have hsum_filter (s : Finset (Finset A)) (pred : Finset A → Prop)
      [DecidablePred pred] (f : Finset A → ℝ) :
      (s.filter pred).sum f = s.sum (fun S => if pred S then f S else 0) := by
    induction s using Finset.cons_induction_on with
    | empty =>
        change 0 = 0
        rfl
    | cons S s hS ih =>
        by_cases hp : pred S
        · rw [Finset.filter_cons_of_pos (p := pred) S s hS hp,
            hsum_cons, hsum_cons, ih]
          simp [hp]
        · rw [Finset.filter_cons_of_neg (p := pred) S s hS hp,
            hsum_cons, ih]
          simp [hp]
  have hsum_congr (s : Finset (Finset A)) (f g : Finset A → ℝ)
      (hfg : ∀ S ∈ s, f S = g S) : s.sum f = s.sum g := by
    induction s using Finset.cons_induction_on with
    | empty =>
        change 0 = 0
        rfl
    | cons S s hS ih =>
        rw [hsum_cons, hsum_cons, hfg S (by simp)]
        exact congrArg (fun z : ℝ => g S + z) (ih (by
          intro T hT
          exact hfg T (by simp [hT])))
  have hsum_add (s : Finset (Finset A)) (f g : Finset A → ℝ) :
      s.sum (fun S => f S + g S) = s.sum f + s.sum g := by
    induction s using Finset.cons_induction_on with
    | empty =>
        change 0 = 0 + 0
        norm_num
    | cons S s hS ih =>
        rw [hsum_cons, hsum_cons, hsum_cons, ih]
        ac_rfl
  have hsum_nonneg (s : Finset (Finset A)) (f : Finset A → ℝ)
      (hf : ∀ S ∈ s, 0 ≤ f S) : 0 ≤ s.sum f := by
    induction s using Finset.cons_induction_on with
    | empty =>
        change 0 ≤ (0 : ℝ)
        exact le_refl 0
    | cons S s hS ih =>
        rw [hsum_cons]
        exact add_nonneg (hf S (by simp)) (ih (by
          intro T hT
          exact hf T (by simp [hT])))
  have hsum_le (s : Finset (Finset A)) (f g : Finset A → ℝ)
      (hfg : ∀ S ∈ s, f S ≤ g S) : s.sum f ≤ s.sum g := by
    induction s using Finset.cons_induction_on with
    | empty =>
        change 0 ≤ (0 : ℝ)
        exact le_refl 0
    | cons S s hS ih =>
        rw [hsum_cons, hsum_cons]
        exact add_le_add (hfg S (by simp)) (ih (by
          intro T hT
          exact hfg T (by simp [hT])))
  have hsum_delta (s : Finset (Finset A)) (T : Finset A) (b : ℝ) :
      s.sum (fun S => if S = T then b else 0) = if T ∈ s then b else 0 := by
    induction s using Finset.cons_induction_on with
    | empty =>
        change 0 = 0
        rfl
    | cons S s hS ih =>
        rw [hsum_cons, ih]
        by_cases hST : S = T
        · subst S
          simp [hS]
        · have hTS : T ≠ S := Ne.symm hST
          simp [hST, hTS, add_comm]
  have hsum_mul_right (s : Finset (Finset A)) (f : Finset A → ℝ) (b : ℝ) :
      s.sum (fun S => f S * b) = s.sum f * b := by
    induction s using Finset.cons_induction_on with
    | empty =>
        change 0 = 0 * b
        simp
    | cons S s hS ih =>
        rw [hsum_cons, hsum_cons, ih]
        exact (add_mul _ _ _).symm
  let a : ℝ := U.sum (fun S => if i ∈ S then p.mass S else 0)
  have ha : 0 ≤ a := by
    apply hsum_nonneg
    intro S hS
    by_cases hiS : i ∈ S
    · simp [hiS, p.mass_nonneg S]
    · simp [hiS]
  have hiU : {i} ∈ U := by
    simp [U]
  let p' : inspection_distribution A :=
    { mass := fun S =>
        (if S = {i} then a else 0) + if i ∈ S then 0 else p.mass S
      mass_nonneg := by
        intro S
        by_cases hSi : S = {i}
        · simp [hSi, ha]
        · by_cases hiS : i ∈ S
          · simp [hSi, hiS]
          · simp [hSi, hiS, p.mass_nonneg S]
      total_mass := by
        change U.sum (fun S =>
          (if S = {i} then a else 0) + if i ∈ S then 0 else p.mass S) = 1
        rw [hsum_add, hsum_delta]
        simp only [hiU, if_true]
        change U.sum (fun S => if i ∈ S then p.mass S else 0) +
            U.sum (fun S => if i ∈ S then 0 else p.mass S) = 1
        rw [← hsum_add]
        calc
          U.sum (fun S =>
              (if i ∈ S then p.mass S else 0) +
                if i ∈ S then 0 else p.mass S) =
              U.sum p.mass := by
                apply hsum_congr
                intro S hS
                by_cases hiS : i ∈ S <;> simp [hiS]
          _ = 1 := p.total_mass }
  refine ⟨p', ?_, ?_, ?_⟩
  · intro S hmass hiS
    by_contra hSi
    apply hmass
    simp [p', hSi, hiS]
  · intro j
    let event : Finset A → Prop := fun S => i ∈ S ∨ j ∈ S
    let residual : Finset A → ℝ := fun S =>
      if i ∈ S then 0 else if j ∈ S then p.mass S else 0
    have hnormalized :
        U.sum (fun S => if event S then p'.mass S else 0) =
          a + U.sum residual := by
      calc
        U.sum (fun S => if event S then p'.mass S else 0) =
            U.sum (fun S =>
              (if S = {i} then a else 0) + residual S) := by
                apply hsum_congr
                intro S hS
                by_cases hiS : i ∈ S
                · simp [event, residual, p', hiS]
                · have hSne : S ≠ {i} := by
                    intro hEq
                    subst S
                    exact hiS (by simp)
                  by_cases hjS : j ∈ S <;>
                    simp [event, residual, p', hiS, hjS, hSne]
        _ = U.sum (fun S => if S = {i} then a else 0) +
              U.sum residual := hsum_add _ _ _
        _ = a + U.sum residual := by
              rw [hsum_delta]
              simp [hiU]
    have horiginal :
        U.sum (fun S => if event S then p.mass S else 0) =
          a + U.sum residual := by
      calc
        U.sum (fun S => if event S then p.mass S else 0) =
            U.sum (fun S =>
              (if i ∈ S then p.mass S else 0) + residual S) := by
                apply hsum_congr
                intro S hS
                by_cases hiS : i ∈ S <;>
                  by_cases hjS : j ∈ S <;>
                    simp [event, residual, hiS, hjS]
        _ = U.sum (fun S => if i ∈ S then p.mass S else 0) +
              U.sum residual := hsum_add _ _ _
        _ = a + U.sum residual := rfl
    unfold detection_probability
    rw [hsum_filter, hsum_filter]
    exact hnormalized.trans horiginal.symm
  · let normalizedTerm : Finset A → ℝ := fun S =>
      if i ∈ S then p.mass S * v {i} else p.mass S * v S
    have hnormalizedCost :
        expected_inspection_cost v p' = U.sum normalizedTerm := by
      unfold expected_inspection_cost
      change U.sum (fun S => p'.mass S * v S) = U.sum normalizedTerm
      calc
        U.sum (fun S => p'.mass S * v S) =
            U.sum (fun S =>
              (if S = {i} then a * v S else 0) +
                if i ∈ S then 0 else p.mass S * v S) := by
                apply hsum_congr
                intro S hS
                by_cases hSi : S = {i} <;>
                  by_cases hiS : i ∈ S <;>
                    simp [p', hSi, hiS]
        _ = U.sum (fun S => if S = {i} then a * v S else 0) +
              U.sum (fun S =>
                if i ∈ S then 0 else p.mass S * v S) := hsum_add _ _ _
        _ = a * v {i} +
              U.sum (fun S =>
                if i ∈ S then 0 else p.mass S * v S) := by
                congr 1
                calc
                  U.sum (fun S => if S = {i} then a * v S else 0) =
                      U.sum (fun S =>
                        if S = {i} then a * v {i} else 0) := by
                          apply hsum_congr
                          intro S hS
                          by_cases hSi : S = {i} <;> simp [hSi]
                  _ = a * v {i} := by
                        rw [hsum_delta]
                        simp [hiU]
        _ = U.sum (fun S =>
                (if i ∈ S then p.mass S else 0) * v {i}) +
              U.sum (fun S =>
                if i ∈ S then 0 else p.mass S * v S) := by
                rw [hsum_mul_right]
        _ = U.sum (fun S =>
              (if i ∈ S then p.mass S else 0) * v {i} +
                if i ∈ S then 0 else p.mass S * v S) := by
                rw [hsum_add]
        _ = U.sum normalizedTerm := by
              apply hsum_congr
              intro S hS
              by_cases hiS : i ∈ S <;>
                simp [normalizedTerm, hiS]
    rw [hnormalizedCost]
    unfold expected_inspection_cost
    change U.sum normalizedTerm ≤ U.sum (fun S => p.mass S * v S)
    apply hsum_le
    intro S hS
    by_cases hiS : i ∈ S
    · simp only [normalizedTerm, hiS, if_true]
      apply mul_le_mul_of_nonneg_left
      · apply hmono
        intro x hx
        simp only [Finset.mem_singleton] at hx
        subst x
        exact hiS
      · exact p.mass_nonneg S
    · simp [normalizedTerm, hiS]

@[blueprint "lem:finite-real-sum-cons"
  (statement := /-- If an element is adjoined disjointly to a finite set, summing a real-valued function over the enlarged set separates into the new term and the sum over the original set. -/)
  (proof := /-- This is the defining recursion for a finite sum over a disjoint cons. -/)
  (title := /-- Splitting a finite real sum at a disjoint cons -/)
  (latexEnv := "lemma")]
lemma finite_real_sum_cons
    {B : Type} (a : B) (s : Finset B) (ha : a ∉ s) (f : B → ℝ) :
    (s.cons a ha).sum f = f a + s.sum f := by
  exact Finset.fold_cons ha

@[blueprint "lem:finite-real-sum-zero"
  (statement := /-- A finite sum of real numbers is zero when every summand indexed by the finite set is zero. -/)
  (proof := /-- Induct by disjoint cons.  At each step, split the sum by \cref{lem:finite-real-sum-cons}, use the vanishing hypothesis for the new term, and apply the induction hypothesis to the remaining set. -/)
  (title := /-- Vanishing of a finite real sum -/)
  (latexEnv := "lemma")]
lemma finite_real_sum_zero
    {B : Type} (s : Finset B) (f : B → ℝ)
    (hzero : ∀ a ∈ s, f a = 0) : s.sum f = 0 := by
  induction s using Finset.cons_induction_on with
  | empty => rfl
  | cons a s ha ih =>
      rw [finite_real_sum_cons]
      rw [hzero a (by simp)]
      have htail : ∀ b ∈ s, f b = 0 := by
        intro b hb
        exact hzero b (by simp [hb])
      rw [ih htail]
      exact add_zero 0

@[blueprint "lem:finite-real-sum-congr"
  (statement := /-- Two real-valued functions that agree at every point of a finite set have equal sums over that set. -/)
  (proof := /-- Induct by disjoint cons and split both sums with \cref{lem:finite-real-sum-cons}.  Equality at the new element identifies the head terms, while the restricted pointwise equality and the induction hypothesis identify the tail sums. -/)
  (title := /-- Congruence of finite real sums -/)
  (latexEnv := "lemma")]
lemma finite_real_sum_congr
    {B : Type} (s : Finset B) (f g : B → ℝ)
    (hfg : ∀ a ∈ s, f a = g a) : s.sum f = s.sum g := by
  induction s using Finset.cons_induction_on with
  | empty => rfl
  | cons a s ha ih =>
      rw [finite_real_sum_cons, finite_real_sum_cons]
      have htail : ∀ b ∈ s, f b = g b := by
        intro b hb
        exact hfg b (by simp [hb])
      rw [hfg a (by simp), ih htail]

@[blueprint "lem:finite-real-sum-single"
  (statement := /-- If $a$ belongs to a finite set and a real-valued function vanishes at every other point of that set, then its sum is its value at $a$. -/)
  (proof := /-- Induct by disjoint cons and use \cref{lem:finite-real-sum-cons}.  If the new head is $a$, every tail term vanishes and \cref{lem:finite-real-sum-zero} evaluates the tail sum.  Otherwise the head term vanishes, $a$ lies in the tail, and the induction hypothesis evaluates the tail sum. -/)
  (title := /-- Evaluation of a single supported finite sum -/)
  (latexEnv := "lemma")]
lemma finite_real_sum_single
    {B : Type} (s : Finset B) (f : B → ℝ) (a : B) (ha : a ∈ s)
    (hzero : ∀ b ∈ s, b ≠ a → f b = 0) : s.sum f = f a := by
  induction s using Finset.cons_induction_on with
  | empty => simp at ha
  | cons b s hb ih =>
      rw [finite_real_sum_cons]
      by_cases hba : b = a
      · subst b
        have htail : ∀ c ∈ s, f c = 0 := by
          intro c hc
          exact hzero c (by simp [hc]) (by
            intro hca
            subst c
            exact hb hc)
        rw [finite_real_sum_zero s f htail, add_zero]
      · have hab : a ≠ b := Ne.symm hba
        have ha_tail : a ∈ s := by simpa [hab] using ha
        have hzero_tail : ∀ c ∈ s, c ≠ a → f c = 0 := by
          intro c hc hca
          exact hzero c (by simp [hc]) hca
        rw [hzero b (by simp) hba, zero_add, ih ha_tail hzero_tail]

@[blueprint "lem:finite-real-sum-disjoint-union"
  (statement := /-- The sum of a real-valued function over a disjoint union of two finite sets is the sum over the first set plus the sum over the second. -/)
  (proof := /-- Induct on the first finite set by disjoint cons.  Disjointness keeps the new element out of the second set, so the union is again a disjoint cons.  Apply \cref{lem:finite-real-sum-cons} to the union and to the first set, then use the induction hypothesis and associativity of addition. -/)
  (title := /-- Sum over a disjoint finite union -/)
  (latexEnv := "lemma")]
lemma finite_real_sum_disjoint_union
    {B : Type} [DecidableEq B] (s t : Finset B) (f : B → ℝ)
    (hdisj : Disjoint s t) :
    (s ∪ t).sum f = s.sum f + t.sum f := by
  induction s using Finset.cons_induction_on with
  | empty =>
      rw [show (∅ : Finset B) ∪ t = t by ext; simp]
      change t.sum f = 0 + t.sum f
      exact (zero_add _).symm
  | cons a s ha ih =>
      have hat : a ∉ t := by
        intro hat
        exact (Finset.disjoint_left.mp hdisj) (by simp) hat
      have htail : Disjoint s t := by
        apply Finset.disjoint_left.mpr
        intro b hbs hbt
        exact (Finset.disjoint_left.mp hdisj) (by simp [hbs]) hbt
      have hau : a ∉ s ∪ t := by simp [ha, hat]
      have hunion : (s.cons a ha) ∪ t = (s ∪ t).cons a hau := by
        ext b
        simp [or_assoc]
      rw [hunion, finite_real_sum_cons, finite_real_sum_cons, ih htail]
      exact (add_assoc _ _ _).symm

@[blueprint "lem:finite-real-sum-image"
  (statement := /-- If a map is injective on a finite set, summing a real-valued function over its image equals summing the pullback function over the original set. -/)
  (proof := /-- Induct by disjoint cons.  Injectivity makes the image of the new element disjoint from the image of the tail.  Split the two sums with \cref{lem:finite-real-sum-cons} and invoke the induction hypothesis on the restricted map. -/)
  (title := /-- Change of variables for an injective finite image -/)
  (latexEnv := "lemma")]
lemma finite_real_sum_image
    {B C : Type} [DecidableEq C] (s : Finset B) (g : B → C) (f : C → ℝ)
    (hinj : ∀ a ∈ s, ∀ b ∈ s, g a = g b → a = b) :
    (s.image g).sum f = s.sum fun a => f (g a) := by
  induction s using Finset.cons_induction_on with
  | empty => rfl
  | cons a s ha ih =>
      have hga : g a ∉ s.image g := by
        intro hmem
        rcases Finset.mem_image.mp hmem with ⟨b, hb, hab⟩
        have hab' : a = b := hinj a (by simp) b (by simp [hb]) hab.symm
        exact ha (hab' ▸ hb)
      have hinj_tail : ∀ b ∈ s, ∀ c ∈ s, g b = g c → b = c := by
        intro b hb c hc hbc
        exact hinj b (by simp [hb]) c (by simp [hc]) hbc
      have himage : (s.cons a ha).image g = (s.image g).cons (g a) hga := by
        ext c
        simp only [Finset.mem_image, Finset.mem_cons]
        constructor
        · intro h
          rcases h with ⟨b, hb, hbc⟩
          rcases hb with rfl | hb
          · exact Or.inl hbc.symm
          · exact Or.inr ⟨b, hb, hbc⟩
        · intro h
          rcases h with h | h
          · exact ⟨a, Or.inl rfl, h.symm⟩
          · rcases h with ⟨b, hb, hbc⟩
            exact ⟨b, Or.inr hb, hbc⟩
      rw [himage, finite_real_sum_cons, finite_real_sum_cons, ih hinj_tail]

@[blueprint "lem:finite-real-sum-powerset-insert"
  (statement := /-- If $a\notin s$, a real-valued sum over all subsets of $s\cup\{a\}$ splits into the sum over subsets of $s$ and the sum over those same subsets after adjoining $a$. -/)
  (proof := /-- The powerset of $s\cup\{a\}$ is the disjoint union of the subsets of $s$ and their images under adjoining $a$.  Apply \cref{lem:finite-real-sum-disjoint-union}; adjoining $a$ is injective on subsets of $s$, so \cref{lem:finite-real-sum-image} evaluates the image sum. -/)
  (title := /-- Splitting a powerset sum at an inserted element -/)
  (latexEnv := "lemma")]
lemma finite_real_sum_powerset_insert
    {B : Type} [DecidableEq B] (s : Finset B) (a : B) (ha : a ∉ s)
    (f : Finset B → ℝ) :
    (insert a s).powerset.sum f =
      s.powerset.sum f + s.powerset.sum (fun t => f (insert a t)) := by
  rw [Finset.powerset_insert]
  have hdisj : Disjoint s.powerset (s.powerset.image (insert a)) := by
    apply Finset.disjoint_left.mpr
    intro t ht hti
    rcases Finset.mem_image.mp hti with ⟨u, hu, rfl⟩
    exact ha (Finset.mem_of_subset (Finset.mem_powerset.mp ht)
      (Finset.mem_insert_self a u))
  rw [finite_real_sum_disjoint_union _ _ _ hdisj]
  have hinj :
      ∀ u ∈ s.powerset, ∀ t ∈ s.powerset,
        insert a u = insert a t → u = t := by
    intro u hu t ht hut
    have hau : a ∉ u := by
      intro hau
      exact ha (Finset.mem_of_subset (Finset.mem_powerset.mp hu) hau)
    have hat : a ∉ t := by
      intro hat
      exact ha (Finset.mem_of_subset (Finset.mem_powerset.mp ht) hat)
    ext b
    by_cases hba : b = a
    · subst b
      simp [hau, hat]
    · have hmem : b ∈ insert a u ↔ b ∈ insert a t := by rw [hut]
      simpa [hba] using hmem
  rw [finite_real_sum_image _ _ _ hinj]

@[blueprint "lem:finite-real-sum-add"
  (statement := /-- A finite sum of pointwise sums of two real-valued functions is the sum of their finite sums. -/)
  (proof := /-- Induct by disjoint cons, split all three finite sums with \cref{lem:finite-real-sum-cons}, apply the induction hypothesis, and rearrange the four resulting terms by associativity and commutativity. -/)
  (title := /-- Additivity of finite real sums -/)
  (latexEnv := "lemma")]
lemma finite_real_sum_add
    {B : Type} (s : Finset B) (f g : B → ℝ) :
    s.sum (fun a => f a + g a) = s.sum f + s.sum g := by
  induction s using Finset.cons_induction_on with
  | empty =>
      change (0 : ℝ) = 0 + 0
      exact (add_zero 0).symm
  | cons a s ha ih =>
      rw [finite_real_sum_cons, finite_real_sum_cons, finite_real_sum_cons, ih]
      rw [add_assoc (f a) (g a) _, ← add_assoc (g a) (s.sum f) (s.sum g),
        add_comm (g a) (s.sum f), add_assoc (s.sum f) (g a) (s.sum g),
        ← add_assoc (f a) (s.sum f) _]

@[blueprint "lem:finite-real-sum-mul-right"
  (statement := /-- Multiplication on the right by a fixed real number commutes with a finite real sum. -/)
  (proof := /-- Induct by disjoint cons, split both sums with \cref{lem:finite-real-sum-cons}, invoke the induction hypothesis, and apply distributivity. -/)
  (title := /-- Right multiplication through a finite real sum -/)
  (latexEnv := "lemma")]
lemma finite_real_sum_mul_right
    {B : Type} (s : Finset B) (f : B → ℝ) (c : ℝ) :
    s.sum (fun a => f a * c) = s.sum f * c := by
  induction s using Finset.cons_induction_on with
  | empty =>
      change (0 : ℝ) = 0 * c
      exact (zero_mul c).symm
  | cons a s ha ih =>
      rw [finite_real_sum_cons, finite_real_sum_cons, ih]
      exact (add_mul (f a) (s.sum f) c).symm

@[blueprint "lem:finite-real-sum-nonnegative"
  (statement := /-- A finite sum of nonnegative real terms is nonnegative. -/)
  (proof := /-- Induct by disjoint cons, use \cref{lem:finite-real-sum-cons}, and add the nonnegativity of the new term to the induction hypothesis for the tail. -/)
  (title := /-- Nonnegativity of a finite real sum -/)
  (latexEnv := "lemma")]
lemma finite_real_sum_nonnegative
    {B : Type} (s : Finset B) (f : B → ℝ)
    (hf : ∀ a ∈ s, 0 ≤ f a) : 0 ≤ s.sum f := by
  induction s using Finset.cons_induction_on with
  | empty => exact le_rfl
  | cons a s ha ih =>
      rw [finite_real_sum_cons]
      apply add_nonneg
      · exact hf a (by simp)
      · apply ih
        intro b hb
        exact hf b (by simp [hb])

@[blueprint "lem:finite-real-sum-monotone"
  (statement := /-- Pointwise comparison on a finite set implies comparison of the corresponding finite real sums. -/)
  (proof := /-- Induct by disjoint cons, split both sums with \cref{lem:finite-real-sum-cons}, compare the head terms by the hypothesis, and compare the tail sums by the induction hypothesis. -/)
  (title := /-- Monotonicity of finite real sums -/)
  (latexEnv := "lemma")]
lemma finite_real_sum_monotone
    {B : Type} (s : Finset B) (f g : B → ℝ)
    (hfg : ∀ a ∈ s, f a ≤ g a) : s.sum f ≤ s.sum g := by
  induction s using Finset.cons_induction_on with
  | empty => exact le_rfl
  | cons a s ha ih =>
      rw [finite_real_sum_cons, finite_real_sum_cons]
      apply add_le_add
      · exact hfg a (by simp)
      · apply ih
        intro b hb
        exact hfg b (by simp [hb])

@[blueprint "lem:finite-real-sum-filter"
  (statement := /-- Summing over a filtered finite set equals summing over the original finite set after replacing excluded terms by zero. -/)
  (proof := /-- Induct by disjoint cons.  According as the new element satisfies the predicate, the filtered set either adjoins it or omits it.  In both cases split the unfiltered sum, and in the first case also the filtered sum, by \cref{lem:finite-real-sum-cons}; the conclusion then follows from the induction hypothesis. -/)
  (title := /-- Indicator form of a filtered finite sum -/)
  (latexEnv := "lemma")]
lemma finite_real_sum_filter
    {B : Type} [DecidableEq B] (s : Finset B) (P : B → Prop)
    [DecidablePred P] (f : B → ℝ) :
    (s.filter P).sum f = s.sum fun a => if P a then f a else 0 := by
  induction s using Finset.cons_induction_on with
  | empty => rfl
  | cons a s ha ih =>
      by_cases hPa : P a
      · have haf : a ∉ s.filter P := by simp [ha]
        have hfilter : (s.cons a ha).filter P = (s.filter P).cons a haf := by
          ext b
          by_cases hba : b = a
          · subst b
            simp [hPa, ha]
          · simp [hba]
        rw [hfilter, finite_real_sum_cons, finite_real_sum_cons, ih]
        simp [hPa]
      · have hfilter : (s.cons a ha).filter P = s.filter P := by
          ext b
          by_cases hba : b = a
          · subst b
            simp [hPa, ha]
          · simp [hba]
        rw [hfilter, finite_real_sum_cons, ih]
        simp [hPa]

@[blueprint "def:nested-prefix-mass"
  (statement := /-- Given a list $(a_1,\ldots,a_m)$, nonnegative target marginals $x(a_k)$ in nonincreasing order, and a total mass $t\geq x(a_1)$, the prefix mass assigns $t-x(a_1)$ to the empty set and recursively assigns the remaining mass to sets obtained by adjoining $a_1$ to prefixes of the tail. -/)
  (title := /-- Mass on prefixes of an ordered list -/)
  (latexEnv := "definition")]
def nested_prefix_mass {A : Type} [DecidableEq A] :
    List A → (A → ℝ) → ℝ → Finset A → ℝ
  | [], _, t, S => if S = ∅ then t else 0
  | a :: l, x, t, S =>
      if S = ∅ then t - x a
      else if a ∈ S then nested_prefix_mass l x (x a) (S.erase a) else 0

@[blueprint "def:submodular-chain-increment"
  (statement := /-- For a set function $v$, a base set $P$, an ordered list $(a_1,\ldots,a_m)$, and a set $S$, the chain increment is the sum of the marginal increments of $a_k$ along the successive prefixes of the list, retaining the $k$-th increment precisely when $a_k\in S$. -/)
  (title := /-- Linearization along a chain -/)
  (latexEnv := "definition")]
def submodular_chain_increment {A : Type} [DecidableEq A]
    (v : Finset A → ℝ) : Finset A → List A → Finset A → ℝ
  | _, [], _ => 0
  | P, a :: l, S =>
      (if a ∈ S then v (insert a P) - v P else 0) +
        submodular_chain_increment v (insert a P) l S

@[blueprint "lem:submodular-union-difference-antitone"
  (statement := /-- Let $v\colon 2^A\to\mathbb{R}$ have decreasing marginals.  If $P\subseteq Q$, then for every finite set $U$,
  \[
  v(P\cup U)-v(P)\geq v(Q\cup U)-v(Q).
  \] -/)
  (proof := /-- Induct on $U$.  The empty-set case is an identity.  For the induction step, decompose the increment obtained by adjoining $U\cup\{a\}$ into the increment obtained from $U$ and the marginal contribution of $a$.  The induction hypothesis compares the first terms, while decreasing marginals from \cref{def:submodular-inspection-cost} compare the second terms because $P\cup U\subseteq Q\cup U$.  Adding the two inequalities gives the claim. -/)
  (title := /-- Diminishing returns for adjoining a finite set -/)
  (latexEnv := "lemma")]
lemma submodular_union_difference_antitone
    {A : Type} [DecidableEq A] (v : Finset A → ℝ)
    (hv : submodular_inspection_cost v) {P Q : Finset A}
    (hPQ : P ⊆ Q) (U : Finset A) :
    v (P ∪ U) - v P ≥ v (Q ∪ U) - v Q := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert a U ha ih =>
      have hbase : P ∪ U ⊆ Q ∪ U := Finset.union_subset_union hPQ (fun _ h => h)
      have hm := hv (P ∪ U) (Q ∪ U) hbase a
      simp only [Finset.union_insert]
      calc
        v (insert a (P ∪ U)) - v P =
            (v (insert a (P ∪ U)) - v (P ∪ U)) +
              (v (P ∪ U) - v P) := (sub_add_sub_cancel _ _ _).symm
        _ ≥ (v (insert a (Q ∪ U)) - v (Q ∪ U)) +
              (v (Q ∪ U) - v Q) := add_le_add hm ih
        _ = v (insert a (Q ∪ U)) - v Q := sub_add_sub_cancel _ _ _

@[blueprint "lem:submodular-chain-increment-erase-irrelevant"
  (statement := /-- If $a$ does not occur in a list $L$, then erasing $a$ from a set $S$ does not change the chain increment along $L$. -/)
  (proof := /-- Induct on $L$.  The empty-list case follows from \cref{def:submodular-chain-increment}.  At a head $b\neq a$, membership of $b$ in $S\setminus\{a\}$ is equivalent to membership in $S$; simplify the head contribution and invoke the induction hypothesis for the tail. -/)
  (title := /-- Erasing an unlisted action preserves the chain increment -/)
  (latexEnv := "lemma")]
lemma submodular_chain_increment_erase_irrelevant
    {A : Type} [DecidableEq A] (v : Finset A → ℝ) (P S : Finset A)
    (a : A) (l : List A) (ha : a ∉ l) :
    submodular_chain_increment v P l (S.erase a) =
      submodular_chain_increment v P l S := by
  induction l generalizing P with
  | nil => simp [submodular_chain_increment]
  | cons b l ih =>
      have hba : b ≠ a := by
        intro h
        apply ha
        simp [h]
      have hal : a ∉ l := by
        intro h
        exact ha (by simp [h])
      simp [submodular_chain_increment, hba, ih (insert b P) hal]

@[blueprint "lem:submodular-chain-increment-lower-bound"
  (statement := /-- Let $v\colon 2^A\to\mathbb{R}$ have decreasing marginals, let $P$ be disjoint from the entries of a list $L$, and let $S$ be contained in those entries.  Then
  \[
  v(P)+\operatorname{inc}_v(P,L,S)\leq v(P\cup S),
  \]
  where $\operatorname{inc}_v$ is the chain linearization from \cref{def:submodular-chain-increment}. -/)
  (proof := /-- Induct on the list.  If its head $a$ belongs to $S$, remove $a$ from $S$ and apply the induction hypothesis with base $P\cup\{a\}$.  Since $a$ does not occur in the tail, \cref{lem:submodular-chain-increment-erase-irrelevant} identifies the tail increments before and after this removal; the first selected chain increment then gives the required telescoping identity.  If $a\notin S$, apply \cref{lem:submodular-union-difference-antitone} to compare the gain from adjoining $S$ to $P$ with the gain from adjoining it to $P\cup\{a\}$, and then use the induction hypothesis at the latter base. -/)
  (title := /-- A submodular function dominates its chain linearization -/)
  (latexEnv := "lemma")]
lemma submodular_chain_increment_lower_bound
    {A : Type} [DecidableEq A] (v : Finset A → ℝ)
    (hv : submodular_inspection_cost v) (P : Finset A) (l : List A)
    (S : Finset A) (hnodup : l.Nodup) (hdisj : Disjoint P l.toFinset)
    (hS : S ⊆ l.toFinset) :
    v P + submodular_chain_increment v P l S ≤ v (P ∪ S) := by
  induction l generalizing P S with
  | nil =>
      have hS0 : S = ∅ := by simpa using hS
      simp [hS0, submodular_chain_increment]
  | cons a l ih =>
      have hal : a ∉ l := (List.nodup_cons.mp hnodup).1
      have hnodup_tail : l.Nodup := (List.nodup_cons.mp hnodup).2
      have haP : a ∉ P := by
        intro ha
        exact (Finset.disjoint_left.mp hdisj) ha (by simp)
      have hdisj_tail : Disjoint (insert a P) l.toFinset := by
        apply Finset.disjoint_left.mpr
        intro b hbP hbl
        rcases Finset.mem_insert.mp hbP with rfl | hbP
        · exact hal (by simpa using hbl)
        · exact (Finset.disjoint_left.mp hdisj) hbP (by simp [hbl])
      by_cases haS : a ∈ S
      · have hSerase : S.erase a ⊆ l.toFinset := by
          intro b hb
          rcases Finset.mem_erase.mp hb with ⟨hba, hbS⟩
          have hbmem : b = a ∨ b ∈ l.toFinset := by simpa using hS hbS
          rcases hbmem with h | h
          · exact (hba h).elim
          · exact h
        have hih := ih (insert a P) (S.erase a) hnodup_tail hdisj_tail hSerase
        have hSinsert : insert a (S.erase a) = S := Finset.insert_erase haS
        have hinc := submodular_chain_increment_erase_irrelevant
          v (insert a P) S a l hal
        have hsets : insert a P ∪ S.erase a = P ∪ S := by
          rw [← hSinsert]
          ext b
          simp [or_left_comm, or_assoc]
        simp only [submodular_chain_increment, haS, if_true]
        rw [← hinc, ← add_assoc, add_comm (v P) (v (insert a P) - v P),
          sub_add_cancel]
        exact hih.trans_eq (congrArg v hsets)
      · have hStail : S ⊆ l.toFinset := by
          intro b hb
          have hbmem : b = a ∨ b ∈ l.toFinset := by simpa using hS hb
          rcases hbmem with h | h
          · exact (haS (h ▸ hb)).elim
          · exact h
        have hih := ih (insert a P) S hnodup_tail hdisj_tail hStail
        have hanti := submodular_union_difference_antitone v hv
          (show P ⊆ insert a P from Finset.subset_insert a P) S
        simp only [submodular_chain_increment, haS, if_false, zero_add]
        have hinc : submodular_chain_increment v (insert a P) l S ≤
            v (insert a P ∪ S) - v (insert a P) :=
          (le_sub_iff_add_le').2 hih
        have hcomp : submodular_chain_increment v (insert a P) l S ≤
            v (P ∪ S) - v P := hinc.trans hanti
        calc
          v P + submodular_chain_increment v (insert a P) l S =
              submodular_chain_increment v (insert a P) l S + v P := add_comm _ _
          _ ≤ (v (P ∪ S) - v P) + v P := add_le_add_left hcomp _
          _ = v (P ∪ S) := sub_add_cancel _ _

@[blueprint "lem:nested-prefix-mass-specification"
  (statement := /-- Let $L$ be a list without repetitions, let $x$ be nonnegative on $L$, and suppose the values $x(a)$ are nonincreasing along $L$ and at most $t$.  The mass from \cref{def:nested-prefix-mass} is nonnegative, has total mass $t$, gives each listed $a$ marginal mass $x(a)$ and each unlisted $a$ marginal mass zero, and is nonzero only on prefixes of $L$. -/)
  (proof := /-- Induct on $L$.  For $L=[]$, all mass is at the empty prefix.  For $L=a::L'$, the empty prefix has mass $t-x(a)$ and every other positive-mass set contains $a$ and is obtained by adjoining $a$ to a positive-mass prefix for $L'$.  The ordering hypotheses give $0\leq x(b)\leq x(a)$ for $b\in L'$, so the induction hypothesis applies with total mass $x(a)$.  Split the powerset of $\{a\}\cup L'$ into subsets omitting and containing $a$ by \cref{lem:finite-real-sum-powerset-insert}.  On the first part, \cref{lem:finite-real-sum-single,lem:finite-real-sum-zero} isolate the empty subset; on the second part, \cref{lem:finite-real-sum-congr} identifies the recursively defined summands.  These identities prove the total-mass and marginal formulas, while the recursive description proves the prefix-support assertion. -/)
  (title := /-- Exact properties of the prefix mass -/)
  (latexEnv := "lemma")]
lemma nested_prefix_mass_specification
    {A : Type} [DecidableEq A] (l : List A) (x : A → ℝ) (t : ℝ)
    (hnodup : l.Nodup) (ht : 0 ≤ t)
    (hbound : ∀ a ∈ l, 0 ≤ x a ∧ x a ≤ t)
    (hsorted : l.Pairwise fun a b => x b ≤ x a) :
    (∀ S : Finset A, 0 ≤ nested_prefix_mass l x t S) ∧
    (∑ S ∈ l.toFinset.powerset, nested_prefix_mass l x t S) = t ∧
    (∀ j : A,
      (∑ S ∈ l.toFinset.powerset,
        if j ∈ S then nested_prefix_mass l x t S else 0) =
          if j ∈ l then x j else 0) ∧
    (∀ S : Finset A, nested_prefix_mass l x t S ≠ 0 →
      ∃ k ≤ l.length, S = (l.take k).toFinset) := by
  induction l generalizing t with
  | nil =>
      constructor
      · intro S
        by_cases hS : S = ∅
        · simp [nested_prefix_mass, hS, ht]
        · simp [nested_prefix_mass, hS]
      constructor
      · change t + 0 = t
        exact add_zero t
      constructor
      · intro j
        change (0 : ℝ) + 0 = 0
        simpa using (add_zero (0 : ℝ))
      · intro S hmass
        have hS : S = ∅ := by
          by_contra hne
          exact hmass (by simp [nested_prefix_mass, hne])
        exact ⟨0, by simp, by simp [hS]⟩
  | cons a l ih =>
      have hal : a ∉ l := (List.nodup_cons.mp hnodup).1
      have hal_fin : a ∉ l.toFinset := by simpa using hal
      have hnodup_tail : l.Nodup := (List.nodup_cons.mp hnodup).2
      have hxa := hbound a (by simp)
      have hsort_head : ∀ b ∈ l, x b ≤ x a := (List.pairwise_cons.mp hsorted).1
      have hsorted_tail : l.Pairwise fun b c => x c ≤ x b :=
        (List.pairwise_cons.mp hsorted).2
      have hbound_tail : ∀ b ∈ l, 0 ≤ x b ∧ x b ≤ x a := by
        intro b hb
        exact ⟨(hbound b (by simp [hb])).1, hsort_head b hb⟩
      have hi := ih (x a) hnodup_tail hxa.1 hbound_tail hsorted_tail
      rcases hi with ⟨hi_nonneg, hi_total, hi_marginal, hi_support⟩
      constructor
      · intro S
        by_cases hS : S = ∅
        · simp [nested_prefix_mass, hS, sub_nonneg.mpr hxa.2]
        · by_cases haS : a ∈ S
          · simpa [nested_prefix_mass, hS, haS] using hi_nonneg (S.erase a)
          · simp [nested_prefix_mass, hS, haS]
      constructor
      · have hfirst :
            (∑ S ∈ l.toFinset.powerset, nested_prefix_mass (a :: l) x t S) =
              t - x a := by
          rw [show t - x a = nested_prefix_mass (a :: l) x t ∅ by
            simp [nested_prefix_mass]]
          apply finite_real_sum_single
          · simp
          · intro S hSpow hSne
            have haS : a ∉ S := by
              intro haS
              exact hal_fin
                (Finset.mem_of_subset (Finset.mem_powerset.mp hSpow) haS)
            simp [nested_prefix_mass, hSne, haS]
        have hsecond :
            (∑ S ∈ l.toFinset.powerset,
              nested_prefix_mass (a :: l) x t (insert a S)) =
              ∑ S ∈ l.toFinset.powerset, nested_prefix_mass l x (x a) S := by
          apply finite_real_sum_congr
          intro S hSpow
          have haS : a ∉ S := by
            intro haS
            exact hal_fin (Finset.mem_of_subset (Finset.mem_powerset.mp hSpow) haS)
          simp [nested_prefix_mass, haS]
        rw [List.toFinset_cons, finite_real_sum_powerset_insert _ _ hal_fin,
          hfirst, hsecond,
          hi_total, sub_add_cancel]
      constructor
      · intro j
        have hfirst :
            (∑ S ∈ l.toFinset.powerset,
              if j ∈ S then nested_prefix_mass (a :: l) x t S else 0) = 0 := by
          apply finite_real_sum_zero
          intro S hSpow
          by_cases hS : S = ∅
          · simp [hS]
          · have haS : a ∉ S := by
              intro haS
              exact hal_fin
                (Finset.mem_of_subset (Finset.mem_powerset.mp hSpow) haS)
            simp [nested_prefix_mass, hS, haS]
        have hsecond :
            (∑ S ∈ l.toFinset.powerset,
              if j ∈ insert a S then
                nested_prefix_mass (a :: l) x t (insert a S) else 0) =
              if j = a then x j else
                ∑ S ∈ l.toFinset.powerset,
                  if j ∈ S then nested_prefix_mass l x (x a) S else 0 := by
          by_cases hja : j = a
          · subst j
            simp only [Finset.mem_insert, true_or, if_true]
            rw [← hi_total]
            apply finite_real_sum_congr
            intro S hSpow
            have haS : a ∉ S := by
              intro haS
              exact hal_fin
                (Finset.mem_of_subset (Finset.mem_powerset.mp hSpow) haS)
            simp [nested_prefix_mass, haS]
          · simp only [Finset.mem_insert, hja, false_or]
            apply finite_real_sum_congr
            intro S hSpow
            have haS : a ∉ S := by
              intro haS
              exact hal_fin
                (Finset.mem_of_subset (Finset.mem_powerset.mp hSpow) haS)
            simp [nested_prefix_mass, haS]
        rw [List.toFinset_cons, finite_real_sum_powerset_insert _ _ hal_fin,
          hfirst, zero_add, hsecond]
        by_cases hja : j = a
        · subst j
          simp
        · simp [hja, hi_marginal j]
      · intro S hmass
        by_cases hS : S = ∅
        · exact ⟨0, by simp, by simp [hS]⟩
        have haS : a ∈ S := by
          by_contra haS
          exact hmass (by simp [nested_prefix_mass, hS, haS])
        have htailmass : nested_prefix_mass l x (x a) (S.erase a) ≠ 0 := by
          simpa [nested_prefix_mass, hS, haS] using hmass
        rcases hi_support (S.erase a) htailmass with ⟨k, hk, hkS⟩
        refine ⟨k + 1, Nat.succ_le_succ hk, ?_⟩
        calc
          S = insert a (S.erase a) := (Finset.insert_erase haS).symm
          _ = insert a ((l.take k).toFinset) := congrArg (insert a) hkS
          _ = ((a :: l).take (k + 1)).toFinset := by simp

@[blueprint "lem:submodular-chain-increment-prefix-exact"
  (statement := /-- Let $P$ be disjoint from the entries of a repetition-free list $L$.  For every prefix $L_{\leq k}$, the chain linearization telescopes exactly:
  \[
  v(P)+\operatorname{inc}_v(P,L,L_{\leq k})=v(P\cup L_{\leq k}).
  \] -/)
  (proof := /-- Induct on $L$.  The empty prefix selects no increment.  A nonempty prefix selects the head increment, which cancels the initial value $v(P)$, and the induction hypothesis telescopes the remaining selected prefix from the enlarged base $P\cup\{a\}$.  Since $a$ does not occur in the tail, \cref{lem:submodular-chain-increment-erase-irrelevant} removes the inserted head from the tail increment.  Repetition-freeness and disjointness then identify the resulting union with the original base together with the full prefix. -/)
  (title := /-- Exact telescoping on a chain prefix -/)
  (latexEnv := "lemma")]
lemma submodular_chain_increment_prefix_exact
    {A : Type} [DecidableEq A] (v : Finset A → ℝ)
    (P : Finset A) (l : List A) (hnodup : l.Nodup)
    (hdisj : Disjoint P l.toFinset) (k : ℕ) (hk : k ≤ l.length) :
    v P + submodular_chain_increment v P l (l.take k).toFinset =
      v (P ∪ (l.take k).toFinset) := by
  induction l generalizing P k with
  | nil =>
      simp [submodular_chain_increment]
  | cons a l ih =>
      have hal : a ∉ l := (List.nodup_cons.mp hnodup).1
      have hnodup_tail : l.Nodup := (List.nodup_cons.mp hnodup).2
      have haP : a ∉ P := by
        intro haP
        exact (Finset.disjoint_left.mp hdisj) haP (by simp)
      have hdisj_tail : Disjoint (insert a P) l.toFinset := by
        apply Finset.disjoint_left.mpr
        intro b hbP hbl
        rcases Finset.mem_insert.mp hbP with rfl | hbP
        · exact hal (by simpa using hbl)
        · exact (Finset.disjoint_left.mp hdisj) hbP (by simp [hbl])
      cases k with
      | zero =>
          have hih0 := ih (insert a P) hnodup_tail hdisj_tail 0 (by simp)
          simp only [List.take_zero, List.toFinset_nil, Finset.union_empty] at hih0
          simp only [List.take_zero, List.toFinset_nil,
            submodular_chain_increment, Finset.notMem_empty, if_false, zero_add,
            Finset.union_empty]
          have hz :
              submodular_chain_increment v (insert a P) l ∅ = 0 := by
            apply add_left_cancel (a := v (insert a P))
            simpa using hih0
          rw [hz, add_zero]
      | succ k =>
          have hk_tail : k ≤ l.length := by simpa using hk
          have htake :
              ((a :: l).take (k + 1)).toFinset =
                insert a (l.take k).toFinset := by simp
          have hatake : a ∉ (l.take k).toFinset := by
            intro ha
            apply hal
            exact List.mem_of_mem_take (by simpa using ha)
          have hinc :
              submodular_chain_increment v (insert a P) l
                  (insert a (l.take k).toFinset) =
                submodular_chain_increment v (insert a P) l
                  (l.take k).toFinset := by
            rw [← submodular_chain_increment_erase_irrelevant v (insert a P)
              (insert a (l.take k).toFinset) a l hal]
            simp [hatake]
          have hih := ih (insert a P) hnodup_tail hdisj_tail k hk_tail
          rw [htake]
          simp only [submodular_chain_increment, Finset.mem_insert, true_or, if_true]
          rw [hinc]
          rw [← add_assoc, add_comm (v P) (v (insert a P) - v P),
            sub_add_cancel]
          calc
            v (insert a P) +
                submodular_chain_increment v (insert a P) l (l.take k).toFinset =
                v (insert a P ∪ (l.take k).toFinset) := hih
            _ = v (P ∪ insert a (l.take k).toFinset) := by
              congr 1
              ext b
              simp [or_left_comm, or_assoc]

@[blueprint "lem:finite-weighted-chain-increment-eq"
  (statement := /-- Let two real weight functions on a finite family $U$ of sets have the same marginal weight at every entry of a list $L$.  Their weighted sums of the chain linearization along $L$ are equal. -/)
  (proof := /-- Induct on $L$.  In the empty-list case, \cref{lem:finite-real-sum-congr} identifies the two sums term by term.  For a nonempty list, expand the head contribution by distributivity and split the finite sum using \cref{lem:finite-real-sum-add}.  The head term is the common marginal weight multiplied by the head chain increment, as follows from \cref{lem:finite-real-sum-mul-right}; the induction hypothesis identifies the tail terms because the required tail marginals are among the assumed equalities. -/)
  (title := /-- Chain-linearized expectation depends only on marginals -/)
  (latexEnv := "lemma")]
lemma finite_weighted_chain_increment_eq
    {A : Type} [DecidableEq A] (v : Finset A → ℝ)
    (U : Finset (Finset A)) (w z : Finset A → ℝ)
    (P : Finset A) (l : List A)
    (hmarg : ∀ a ∈ l,
      U.sum (fun S => if a ∈ S then w S else 0) =
        U.sum (fun S => if a ∈ S then z S else 0)) :
    U.sum (fun S => w S * submodular_chain_increment v P l S) =
      U.sum (fun S => z S * submodular_chain_increment v P l S) := by
  induction l generalizing P with
  | nil =>
      apply finite_real_sum_congr
      intro S hS
      simp [submodular_chain_increment]
  | cons a l ih =>
      have hhead := hmarg a (by simp)
      have htail : ∀ b ∈ l,
          U.sum (fun S => if b ∈ S then w S else 0) =
            U.sum (fun S => if b ∈ S then z S else 0) := by
        intro b hb
        exact hmarg b (by simp [hb])
      have hih := ih (insert a P) htail
      have hw :
          U.sum (fun S =>
            w S * (if a ∈ S then v (insert a P) - v P else 0)) =
            U.sum (fun S => if a ∈ S then w S else 0) *
              (v (insert a P) - v P) := by
        rw [← finite_real_sum_mul_right]
        apply finite_real_sum_congr
        intro S hS
        by_cases haS : a ∈ S <;> simp [haS]
      have hz :
          U.sum (fun S =>
            z S * (if a ∈ S then v (insert a P) - v P else 0)) =
            U.sum (fun S => if a ∈ S then z S else 0) *
              (v (insert a P) - v P) := by
        rw [← finite_real_sum_mul_right]
        apply finite_real_sum_congr
        intro S hS
        by_cases haS : a ∈ S <;> simp [haS]
      simp only [submodular_chain_increment, mul_add]
      rw [finite_real_sum_add, finite_real_sum_add, hw, hz, hhead, hih]

@[blueprint "lem:submodular-small-support-replacement"
  (statement := /-- Let $A$ be a finite action set, let $v\colon 2^A\to\mathbb{R}$ be nonnegative, normalized, monotone, and submodular, fix $i\in A$, and let $p$ be an inspection distribution separated at $i$.  There exists an inspection distribution $q$, also separated at $i$, such that, for every $j\in A$, the probability that an inspected set meets $\{i,j\}$ is the same under $q$ as under $p$,
  \[
  \mathbb{E}_{q}[v]\leq\mathbb{E}_{p}[v],
  \]
  the support of $q$ is nested away from the distinguished singleton, and $|\operatorname{supp}(q)|\leq |A|+1$. -/)
  (proof := /-- Put $B=A\setminus\{i\}$, retain the mass $r=p(\{i\})$, and let $t$ be the total $p$-mass on $2^B$.  Separation implies that every other set containing $i$ has zero mass.  Splitting $2^A$ at $i$ by \cref{lem:finite-real-sum-powerset-insert}, and evaluating its singleton-supported part by \cref{lem:finite-real-sum-single}, gives $t+r=1$.  For $a\in B$, let $x(a)$ be its marginal mass among subsets of $B$.  The nonnegativity and bound $0\leq x(a)\leq t$ follow from \cref{lem:finite-real-sum-nonnegative,lem:finite-real-sum-monotone}.  Order $B$ so that these marginals are nonincreasing and apply \cref{lem:nested-prefix-mass-specification}.  The resulting mass on prefixes is nonnegative, totals $t$, has marginals $x$, and is supported on prefixes.  Define $q$ by assigning mass $r$ to $\{i\}$, this prefix mass to subsets of $B$, and zero elsewhere.  Sum congruence and vanishing outside the stated pieces, as supplied by \cref{lem:finite-real-sum-congr,lem:finite-real-sum-zero}, show that $q$ has total mass one.  Rewriting filtered event sums with \cref{lem:finite-real-sum-filter} then shows that $q$ preserves every detection probability.

  It remains to compare costs.  By \cref{lem:submodular-chain-increment-lower-bound}, the chain linearization from the empty set is bounded above by $v(S)$ for every $S\subseteq B$.  On every prefix carrying $q$-mass it equals $v(S)$ by \cref{lem:submodular-chain-increment-prefix-exact} and the normalization $v(\varnothing)=0$.  Since $p$ and $q$ have identical marginals on the ordered list, \cref{lem:finite-weighted-chain-increment-eq} identifies their expected chain-linearized costs; monotonicity of finite sums from \cref{lem:finite-real-sum-monotone} therefore gives the required expected-cost inequality on $2^B$.  The contributions of sets containing $i$ agree because only $\{i\}$ has nonzero mass; \cref{lem:finite-real-sum-mul-right,lem:finite-real-sum-single} evaluates that common contribution.  Finally, positive-mass sets away from $i$ are prefixes and hence are nested.  There are at most $|B|+1$ prefixes and one distinguished singleton, so the support has cardinality at most $|A|+1$. -/)
  (title := /-- Submodular replacement by a small nested support -/)
  (latexEnv := "lemma")]
lemma submodular_small_support_replacement
    {A : Type} [Fintype A] [DecidableEq A]
    (v : Finset A → ℝ)
    (hv_nonneg : ∀ S : Finset A, 0 ≤ v S)
    (hv_empty : v ∅ = 0) (hv_mono : Monotone v)
    (hv_submod : submodular_inspection_cost v)
    (i : A) (p : inspection_distribution A)
    (hp_sep : suggested_action_separated i p) :
    ∃ q : inspection_distribution A,
      suggested_action_separated i q ∧
      (∀ j : A, detection_probability q i j = detection_probability p i j) ∧
      expected_inspection_cost v q ≤ expected_inspection_cost v p ∧
      nested_inspection_support_away_from i q ∧
      (inspection_support q).card ≤ Fintype.card A + 1 := by
  classical
  let B : Finset A := Finset.univ.erase i
  let r : ℝ := p.mass {i}
  let t : ℝ := B.powerset.sum p.mass
  let x : A → ℝ := fun j =>
    B.powerset.sum (fun S => if j ∈ S then p.mass S else 0)
  let l : List A :=
    B.toList.mergeSort (fun a b => decide (x b ≤ x a))
  have hiB : i ∉ B := by simp [B]
  have hBi : insert i B = Finset.univ := by
    ext a
    simp [B]
  have hl_nodup : l.Nodup := by
    simpa [l] using B.nodup_toList
  have hl_fin : l.toFinset = B := by
    ext a
    simp [l]
  have hl_sorted : l.Pairwise (fun a b => x b ≤ x a) := by
    have hsorted := List.pairwise_mergeSort
      (le := fun a b : A => decide (x b ≤ x a))
      (fun a b c hab hbc => by
        simp only [decide_eq_true_eq] at hab hbc ⊢
        exact hbc.trans hab)
      (fun a b => by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact le_total (x b) (x a)) B.toList
    simpa [l] using hsorted
  have hp_insert_zero : ∀ S ∈ B.powerset, S ≠ ∅ → p.mass (insert i S) = 0 := by
    intro S hS hSne
    have hiS : i ∉ S := by
      intro hiS
      exact hiB (Finset.mem_of_subset (Finset.mem_powerset.mp hS) hiS)
    by_contra hmass
    have hsingle := hp_sep (insert i S) hmass (by simp)
    have herase := congrArg (fun T : Finset A => T.erase i) hsingle
    exact hSne (by simpa [hiS] using herase)
  have hp_insert_total :
      B.powerset.sum (fun S => p.mass (insert i S)) = r := by
    calc
      B.powerset.sum (fun S => p.mass (insert i S)) = p.mass (insert i ∅) := by
        apply finite_real_sum_single B.powerset
        · simp
        · intro S hS hSne
          exact hp_insert_zero S hS hSne
      _ = r := by simp [r]
  have htr : t + r = 1 := by
    have htotal := p.total_mass
    rw [← hBi, finite_real_sum_powerset_insert B i hiB p.mass] at htotal
    simpa [t, r, hp_insert_total] using htotal
  have hr_nonneg : 0 ≤ r := p.mass_nonneg {i}
  have ht_nonneg : 0 ≤ t := by
    apply finite_real_sum_nonnegative
    intro S hS
    exact p.mass_nonneg S
  have hx_nonneg : ∀ a ∈ l, 0 ≤ x a := by
    intro a ha
    apply finite_real_sum_nonnegative
    intro S hS
    by_cases haS : a ∈ S
    · simp [x, haS, p.mass_nonneg S]
    · simp [x, haS]
  have hx_le : ∀ a ∈ l, x a ≤ t := by
    intro a ha
    apply finite_real_sum_monotone
    intro S hS
    by_cases haS : a ∈ S
    · simp [x, t, haS]
    · simp [x, t, haS, p.mass_nonneg S]
  have hprefix := nested_prefix_mass_specification l x t hl_nodup ht_nonneg
    (fun a ha => ⟨hx_nonneg a ha, hx_le a ha⟩) hl_sorted
  rcases hprefix with ⟨hprefix_nonneg, hprefix_total, hprefix_marginal,
    hprefix_support⟩
  rw [hl_fin] at hprefix_total hprefix_marginal
  let qmass : Finset A → ℝ := fun S =>
    if S = {i} then r
    else if S ⊆ B then nested_prefix_mass l x t S else 0
  have hq_on_B : ∀ S ∈ B.powerset,
      qmass S = nested_prefix_mass l x t S := by
    intro S hS
    have hsub := Finset.mem_powerset.mp hS
    have hiS : i ∉ S := by
      intro hiS
      exact hiB (hsub hiS)
    have hne : S ≠ {i} := by
      intro h
      subst S
      exact hiS (by simp)
    simp [qmass, hne, hsub]
  have hq_insert_total :
      B.powerset.sum (fun S => qmass (insert i S)) = r := by
    calc
      B.powerset.sum (fun S => qmass (insert i S)) = qmass (insert i ∅) := by
        apply finite_real_sum_single B.powerset
        · simp
        · intro S hS hSne
          have hsub := Finset.mem_powerset.mp hS
          have hiS : i ∉ S := by
            intro hiS
            exact hiB (hsub hiS)
          have hne : insert i S ≠ {i} := by
            intro h
            have herase := congrArg (fun T : Finset A => T.erase i) h
            exact hSne (by simpa [hiS] using herase)
          have hnsub : ¬ insert i S ⊆ B := by
            intro h
            exact hiB (h (Finset.mem_insert_self i S))
          simp [qmass, hne, hnsub]
      _ = r := by simp [qmass]
  have hq_nonneg : ∀ S : Finset A, 0 ≤ qmass S := by
    intro S
    by_cases hsingle : S = {i}
    · simp [qmass, hsingle, hr_nonneg]
    · by_cases hsub : S ⊆ B
      · simp [qmass, hsingle, hsub, hprefix_nonneg S]
      · simp [qmass, hsingle, hsub]
  have hq_total : Finset.univ.powerset.sum qmass = 1 := by
    rw [← hBi, finite_real_sum_powerset_insert B i hiB qmass]
    have hfirst : B.powerset.sum qmass = t := by
      calc
        B.powerset.sum qmass =
            B.powerset.sum (nested_prefix_mass l x t) := by
              apply finite_real_sum_congr
              intro S hS
              exact hq_on_B S hS
        _ = t := hprefix_total
    rw [hfirst, hq_insert_total, htr]
  let q : inspection_distribution A :=
    { mass := qmass
      mass_nonneg := hq_nonneg
      total_mass := hq_total }
  have hq_sep : suggested_action_separated i q := by
    intro S hmass hiS
    by_contra hsingle
    have hnsub : ¬ S ⊆ B := by
      intro hsub
      exact hiB (hsub hiS)
    exact hmass (by simp [q, qmass, hsingle, hnsub])
  have hx_zero : ∀ j : A, j ∉ B → x j = 0 := by
    intro j hj
    apply finite_real_sum_zero
    intro S hS
    have hsub := Finset.mem_powerset.mp hS
    have hjS : j ∉ S := by
      intro hjS
      exact hj (hsub hjS)
    simp [x, hjS]
  have hq_marginal : ∀ j : A,
      B.powerset.sum (fun S => if j ∈ S then qmass S else 0) = x j := by
    intro j
    calc
      B.powerset.sum (fun S => if j ∈ S then qmass S else 0) =
          B.powerset.sum (fun S =>
            if j ∈ S then nested_prefix_mass l x t S else 0) := by
            apply finite_real_sum_congr
            intro S hS
            rw [hq_on_B S hS]
      _ = if j ∈ l then x j else 0 := hprefix_marginal j
      _ = x j := by
        by_cases hjB : j ∈ B
        · have hjlfin : j ∈ l.toFinset := hl_fin.symm ▸ hjB
          have hjl : j ∈ l := by simpa using hjlfin
          simp [hjl]
        · have hjl : j ∉ l := by
            intro hjl
            have hjlfin : j ∈ l.toFinset := by simpa using hjl
            exact hjB (hl_fin ▸ hjlfin)
          simp [hjl, hx_zero j hjB]
  have hdetection : ∀ j : A,
      detection_probability q i j = detection_probability p i j := by
    intro j
    rw [detection_probability, detection_probability,
      finite_real_sum_filter, finite_real_sum_filter, ← hBi,
      finite_real_sum_powerset_insert B i hiB,
      finite_real_sum_powerset_insert B i hiB]
    have hq_first :
        B.powerset.sum (fun S => if i ∈ S ∨ j ∈ S then q.mass S else 0) = x j := by
      calc
        B.powerset.sum (fun S => if i ∈ S ∨ j ∈ S then q.mass S else 0) =
            B.powerset.sum (fun S => if j ∈ S then qmass S else 0) := by
              apply finite_real_sum_congr
              intro S hS
              have hsub := Finset.mem_powerset.mp hS
              have hiS : i ∉ S := by
                intro hiS
                exact hiB (hsub hiS)
              simp [q, hiS]
        _ = x j := hq_marginal j
    have hp_first :
        B.powerset.sum (fun S => if i ∈ S ∨ j ∈ S then p.mass S else 0) = x j := by
      apply finite_real_sum_congr B.powerset
        (fun S => if i ∈ S ∨ j ∈ S then p.mass S else 0)
        (fun S => if j ∈ S then p.mass S else 0)
      intro S hS
      have hsub := Finset.mem_powerset.mp hS
      have hiS : i ∉ S := by
        intro hiS
        exact hiB (hsub hiS)
      simp [hiS]
    have hq_second :
        B.powerset.sum (fun S =>
          if i ∈ insert i S ∨ j ∈ insert i S then q.mass (insert i S) else 0) = r := by
      simpa [q] using hq_insert_total
    have hp_second :
        B.powerset.sum (fun S =>
          if i ∈ insert i S ∨ j ∈ insert i S then p.mass (insert i S) else 0) = r := by
      simpa using hp_insert_total
    rw [hq_first, hp_first, hq_second, hp_second]
  have hdisj_empty : Disjoint (∅ : Finset A) l.toFinset := by simp
  have hq_chain_cost :
      B.powerset.sum (fun S => qmass S * v S) =
        B.powerset.sum (fun S =>
          qmass S * submodular_chain_increment v ∅ l S) := by
    apply finite_real_sum_congr
    intro S hS
    rw [hq_on_B S hS]
    by_cases hmass : nested_prefix_mass l x t S = 0
    · simp [hmass]
    · rcases hprefix_support S hmass with ⟨k, hk, rfl⟩
      have hexact := submodular_chain_increment_prefix_exact v ∅ l hl_nodup
        hdisj_empty k hk
      have hvalue :
          submodular_chain_increment v ∅ l (l.take k).toFinset =
            v (l.take k).toFinset := by
        simpa [hv_empty] using hexact
      rw [hvalue]
  have hp_chain_le :
      B.powerset.sum (fun S =>
        p.mass S * submodular_chain_increment v ∅ l S) ≤
          B.powerset.sum (fun S => p.mass S * v S) := by
    apply finite_real_sum_monotone
    intro S hS
    have hsubB := Finset.mem_powerset.mp hS
    have hsubL : S ⊆ l.toFinset := by simpa [hl_fin] using hsubB
    have hlower := submodular_chain_increment_lower_bound v hv_submod ∅ l S
      hl_nodup hdisj_empty hsubL
    have hinc : submodular_chain_increment v ∅ l S ≤ v S := by
      simpa [hv_empty] using hlower
    exact mul_le_mul_of_nonneg_left hinc (p.mass_nonneg S)
  have hchain_equal :
      B.powerset.sum (fun S =>
        qmass S * submodular_chain_increment v ∅ l S) =
      B.powerset.sum (fun S =>
        p.mass S * submodular_chain_increment v ∅ l S) := by
    apply finite_weighted_chain_increment_eq v B.powerset qmass p.mass ∅ l
    intro a ha
    rw [hq_marginal a]
  have haway_cost :
      B.powerset.sum (fun S => qmass S * v S) ≤
        B.powerset.sum (fun S => p.mass S * v S) := by
    rw [hq_chain_cost, hchain_equal]
    exact hp_chain_le
  have hq_insert_cost :
      B.powerset.sum (fun S => q.mass (insert i S) * v (insert i S)) =
        r * v {i} := by
    calc
      B.powerset.sum (fun S => q.mass (insert i S) * v (insert i S)) =
          B.powerset.sum (fun S =>
            qmass (insert i S) * v {i}) := by
              apply finite_real_sum_congr
              intro S hS
              by_cases hSe : S = ∅
              · subst S
                simp [q]
              · have hzero : qmass (insert i S) = 0 := by
                  have hsub := Finset.mem_powerset.mp hS
                  have hiS : i ∉ S := by
                    intro hiS
                    exact hiB (hsub hiS)
                  have hne : insert i S ≠ {i} := by
                    intro h
                    have herase := congrArg (fun T : Finset A => T.erase i) h
                    exact hSe (by simpa [hiS] using herase)
                  have hnsub : ¬ insert i S ⊆ B := by
                    intro h
                    exact hiB (h (Finset.mem_insert_self i S))
                  simp [qmass, hne, hnsub]
                simp [q, hzero]
      _ = r * v {i} := by
        rw [finite_real_sum_mul_right]
        simpa [q] using congrArg (fun z : ℝ => z * v {i}) hq_insert_total
  have hp_insert_cost :
      B.powerset.sum (fun S => p.mass (insert i S) * v (insert i S)) =
        r * v {i} := by
    calc
      B.powerset.sum (fun S => p.mass (insert i S) * v (insert i S)) =
          B.powerset.sum (fun S => p.mass (insert i S) * v {i}) := by
            apply finite_real_sum_congr
            intro S hS
            by_cases hSe : S = ∅
            · subst S
              simp
            · rw [hp_insert_zero S hS hSe]
              simp
      _ = r * v {i} := by
        rw [finite_real_sum_mul_right, hp_insert_total]
  have hcost : expected_inspection_cost v q ≤ expected_inspection_cost v p := by
    rw [expected_inspection_cost, expected_inspection_cost, ← hBi,
      finite_real_sum_powerset_insert B i hiB,
      finite_real_sum_powerset_insert B i hiB]
    change B.powerset.sum (fun S => qmass S * v S) +
        B.powerset.sum (fun S => q.mass (insert i S) * v (insert i S)) ≤ _
    rw [hq_insert_cost, hp_insert_cost]
    exact add_le_add haway_cost le_rfl
  have hnested : nested_inspection_support_away_from i q := by
    intro S hS hiS T hT hiT
    have hSmass : q.mass S ≠ 0 := by
      simpa [inspection_support] using hS
    have hTmass : q.mass T ≠ 0 := by
      simpa [inspection_support] using hT
    have hSsingle : S ≠ {i} := by
      intro h
      apply hiS
      simp [h]
    have hTsingle : T ≠ {i} := by
      intro h
      apply hiT
      simp [h]
    have hSsub : S ⊆ B := by
      by_contra hsub
      exact hSmass (by simp [q, qmass, hSsingle, hsub])
    have hTsub : T ⊆ B := by
      by_contra hsub
      exact hTmass (by simp [q, qmass, hTsingle, hsub])
    have hSprefix : nested_prefix_mass l x t S ≠ 0 := by
      simpa [q, qmass, hSsingle, hSsub] using hSmass
    have hTprefix : nested_prefix_mass l x t T ≠ 0 := by
      simpa [q, qmass, hTsingle, hTsub] using hTmass
    rcases hprefix_support S hSprefix with ⟨k, hk, rfl⟩
    rcases hprefix_support T hTprefix with ⟨m, hm, rfl⟩
    rcases le_total k m with hkm | hmk
    · left
      intro a ha
      simpa using List.take_subset_take_left l hkm (by simpa using ha)
    · right
      intro a ha
      simpa using List.take_subset_take_left l hmk (by simpa using ha)
  let prefixes : Finset (Finset A) :=
    (Finset.range (l.length + 1)).image fun k => (l.take k).toFinset
  have hsupport_subset : inspection_support q ⊆ insert {i} prefixes := by
    intro S hS
    have hSmass : q.mass S ≠ 0 := by
      simpa [inspection_support] using hS
    by_cases hsingle : S = {i}
    · simp [hsingle]
    · have hSsub : S ⊆ B := by
        by_contra hsub
        exact hSmass (by simp [q, qmass, hsingle, hsub])
      have hSprefix : nested_prefix_mass l x t S ≠ 0 := by
        simpa [q, qmass, hsingle, hSsub] using hSmass
      rcases hprefix_support S hSprefix with ⟨k, hk, rfl⟩
      apply Finset.mem_insert.mpr
      exact Or.inr (Finset.mem_image.mpr ⟨k, by simp; omega, rfl⟩)
  have hprefixes_card : prefixes.card ≤ l.length + 1 := by
    calc
      prefixes.card ≤ (Finset.range (l.length + 1)).card := by
        exact Finset.card_image_le
      _ = l.length + 1 := by simp
  have hcardB : B.card + 2 = Fintype.card A + 1 := by
    have hpos : 1 ≤ Fintype.card A := by
      exact Fintype.card_pos_iff.mpr ⟨i⟩
    simp [B, Finset.card_erase_of_mem, hpos]
  have hcard : (inspection_support q).card ≤ Fintype.card A + 1 := by
    calc
      (inspection_support q).card ≤ (insert {i} prefixes).card :=
        Finset.card_le_card hsupport_subset
      _ ≤ prefixes.card + 1 := Finset.card_insert_le _ _
      _ ≤ (l.length + 1) + 1 := Nat.add_le_add_right hprefixes_card 1
      _ = B.card + 2 := by simp [l]
      _ = Fintype.card A + 1 := hcardB
  exact ⟨q, hq_sep, hdetection, hcost, hnested, hcard⟩

@[blueprint "lem:optimal-inspection-scheme-exists"
  (statement := /-- For every finite action space $A$ with decidable equality and every admissible contract datum $d$ on $A$, there exists a feasible inspection scheme $s$ such that, for every feasible inspection scheme $t$, the principal's utility under $t$'s suggested action is at most its utility under $s$'s suggested action. -/)
  (proof := /-- Let $\mathcal U=2^A$, equip $A$ with the discrete topology, and use the order topology on $\mathbb R$.  Addition, negation, and multiplication are continuous for this topology: for addition, intervals around $(x,y)$ whose radii are one third of the gap to a prescribed bound remain on the same side of that bound; for multiplication, if $xy$ has positive gap $g$ from a bound, a sufficiently small rectangle around $(x,y)$ changes the product by less than $g$.  Hence every finite sum of products of coordinate projections is continuous.

  Encode a candidate scheme by
  \[
    (i,\alpha,p)\in A\times\bigl([0,1]\times[0,1]^{\mathcal U}\bigr).
  \]
  Let $K$ be the subset on which $\sum_{S\in\mathcal U}p_S=1$ and, for every $j\in A$, the coordinate formula from \cref{def:agent-utility} for action $j$ is at most $\alpha f(i)-c(i)$.  The ambient box is compact because $A$ and $\mathcal U$ are finite and closed real intervals are compact.  The mass equation is closed, and each incentive inequality is closed by the continuity established above; arbitrary intersections of closed sets are closed.  Thus $K$ is compact.  It is nonempty: choose the null action, set $\alpha=0$, and assign unit mass to $\varnothing$.  By \cref{def:admissible-contract-data}, the suggested utility is $0$ and every deviation utility is $-c(j)\leq0$, so this point satisfies \cref{def:feasible-inspection-scheme}.

  The principal-value coordinate function
  \[
    (i,\alpha,p)\longmapsto (1-\alpha)f(i)-
      \sum_{S\in\mathcal U}p_Sv(S)
  \]
  from \cref{def:principal-utility} is continuous, so the extreme-value theorem supplies a maximizer $x\in K$.  Its nonnegative masses summing to one define an inspection distribution by \cref{def:inspection-distribution}, and its remaining coordinates define a feasible inspection scheme.  Conversely, encode any feasible scheme $t$ by its suggested action, payment, and masses.  Each mass is at most $1$ because all masses are nonnegative and their sum is $1$, so this encoding belongs to $K$.  Maximality of $x$ therefore makes its principal utility at least that of $t$.  Since $t$ was arbitrary, the decoded scheme satisfies \cref{def:optimal-inspection-scheme}. -/)
  (title := /-- Existence of a global optimum -/)
  (latexEnv := "lemma")]
lemma optimal_inspection_scheme_exists
    {A : Type} [Fintype A] [DecidableEq A]
    (d : contract_data A) (hadm : admissible_contract_data d) :
    ∃ s : inspection_scheme A, optimal_inspection_scheme d s := by
  classical
  letI : TopologicalSpace ℝ := Preorder.topology ℝ
  letI : OrderTopology ℝ := ⟨rfl⟩
  have hadd : Continuous (fun p : ℝ × ℝ => p.1 + p.2) := by
    rw [OrderTopology.continuous_iff]
    intro a
    constructor
    · rw [isOpen_iff_forall_mem_open]
      intro p hp
      let e : ℝ := (p.1 + p.2 - a) / 3
      refine ⟨Set.Ioi (p.1 - e) ×ˢ Set.Ioi (p.2 - e), ?_,
        isOpen_Ioi.prod isOpen_Ioi, ?_⟩
      · intro q hq
        change a < q.1 + q.2
        change p.1 - e < q.1 ∧ p.2 - e < q.2 at hq
        change a < p.1 + p.2 at hp
        dsimp [e] at hq
        nlinarith [hq.1, hq.2]
      · change p.1 - e < p.1 ∧ p.2 - e < p.2
        change a < p.1 + p.2 at hp
        dsimp [e]
        constructor <;> nlinarith
    · rw [isOpen_iff_forall_mem_open]
      intro p hp
      let e : ℝ := (a - (p.1 + p.2)) / 3
      refine ⟨Set.Iio (p.1 + e) ×ˢ Set.Iio (p.2 + e), ?_,
        isOpen_Iio.prod isOpen_Iio, ?_⟩
      · intro q hq
        change q.1 + q.2 < a
        change q.1 < p.1 + e ∧ q.2 < p.2 + e at hq
        change p.1 + p.2 < a at hp
        dsimp [e] at hq
        nlinarith [hq.1, hq.2]
      · change p.1 < p.1 + e ∧ p.2 < p.2 + e
        change p.1 + p.2 < a at hp
        dsimp [e]
        constructor <;> nlinarith
  have hneg : Continuous (fun x : ℝ => -x) := by
    rw [OrderTopology.continuous_iff]
    intro a
    constructor
    · change IsOpen {x : ℝ | a < -x}
      convert (isOpen_Iio : IsOpen (Set.Iio (-a))) using 1
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_Iio, lt_neg]
    · change IsOpen {x : ℝ | -x < a}
      convert (isOpen_Ioi : IsOpen (Set.Ioi (-a))) using 1
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_Ioi, neg_lt]
  have hmul : Continuous (fun p : ℝ × ℝ => p.1 * p.2) := by
    rw [OrderTopology.continuous_iff]
    intro a
    constructor
    · rw [isOpen_iff_forall_mem_open]
      intro p hp
      let g : ℝ := p.1 * p.2 - a
      let M : ℝ := 1 + |p.1| + |p.2|
      let e : ℝ := min 1 (g / (2 * M))
      have hg : 0 < g := by
        change a < p.1 * p.2 at hp
        dsimp [g]
        linarith
      have hM : 0 < M := by
        dsimp [M]
        nlinarith [abs_nonneg p.1, abs_nonneg p.2]
      have he : 0 < e := by
        dsimp [e]
        exact lt_min (by norm_num) (div_pos hg (by positivity))
      have he1 : e ≤ 1 := by
        dsimp [e]
        exact min_le_left _ _
      have heM : e * M ≤ g / 2 := by
        calc
          e * M ≤ (g / (2 * M)) * M :=
            mul_le_mul_of_nonneg_right (by
              dsimp [e]
              exact min_le_right _ _) (le_of_lt hM)
          _ = g / 2 := by field_simp
      refine ⟨Set.Ioo (p.1 - e) (p.1 + e) ×ˢ
          Set.Ioo (p.2 - e) (p.2 + e), ?_,
        isOpen_Ioo.prod isOpen_Ioo, ?_⟩
      · intro q hq
        rcases hq with ⟨⟨hq1l, hq1u⟩, ⟨hq2l, hq2u⟩⟩
        have hd1 : |q.1 - p.1| < e := (abs_lt).2 ⟨by linarith, by linarith⟩
        have hd2 : |q.2 - p.2| < e := (abs_lt).2 ⟨by linarith, by linarith⟩
        have hprod : |q.1 - p.1| * |q.2 - p.2| < e * e := by
          nlinarith [
            mul_nonneg (sub_nonneg.mpr (le_of_lt hd1)) (abs_nonneg (q.2 - p.2)),
            mul_pos he (sub_pos.mpr hd2)]
        have hp1 : |p.1| * |q.2 - p.2| ≤ |p.1| * e :=
          mul_le_mul_of_nonneg_left (le_of_lt hd2) (abs_nonneg _)
        have hp2 : |p.2| * |q.1 - p.1| ≤ |p.2| * e :=
          mul_le_mul_of_nonneg_left (le_of_lt hd1) (abs_nonneg _)
        have habs : |q.1 * q.2 - p.1 * p.2| < g := by
          calc
            |q.1 * q.2 - p.1 * p.2| =
                |(q.1 - p.1) * (q.2 - p.2) + p.1 * (q.2 - p.2) +
                  p.2 * (q.1 - p.1)| := by congr 1 <;> ring
            _ ≤ |(q.1 - p.1) * (q.2 - p.2) + p.1 * (q.2 - p.2)| +
                  |p.2 * (q.1 - p.1)| := abs_add_le _ _
            _ ≤ (|(q.1 - p.1) * (q.2 - p.2)| +
                  |p.1 * (q.2 - p.2)|) + |p.2 * (q.1 - p.1)| :=
              add_le_add (abs_add_le _ _) (le_refl _)
            _ = |q.1 - p.1| * |q.2 - p.2| + |p.1| * |q.2 - p.2| +
                  |p.2| * |q.1 - p.1| := by rw [abs_mul, abs_mul, abs_mul]
            _ < e * e + |p.1| * e + |p.2| * e := by linarith
            _ ≤ e * M := by
              dsimp [M]
              nlinarith [mul_nonneg (le_of_lt he) (sub_nonneg.mpr he1)]
            _ ≤ g / 2 := heM
            _ < g := by nlinarith
        change a < q.1 * q.2
        have hlow := (abs_lt.1 habs).1
        dsimp [g] at hlow
        linarith
      · exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    · rw [isOpen_iff_forall_mem_open]
      intro p hp
      let g : ℝ := a - p.1 * p.2
      let M : ℝ := 1 + |p.1| + |p.2|
      let e : ℝ := min 1 (g / (2 * M))
      have hg : 0 < g := by
        change p.1 * p.2 < a at hp
        dsimp [g]
        linarith
      have hM : 0 < M := by
        dsimp [M]
        nlinarith [abs_nonneg p.1, abs_nonneg p.2]
      have he : 0 < e := by
        dsimp [e]
        exact lt_min (by norm_num) (div_pos hg (by positivity))
      have he1 : e ≤ 1 := by
        dsimp [e]
        exact min_le_left _ _
      have heM : e * M ≤ g / 2 := by
        calc
          e * M ≤ (g / (2 * M)) * M :=
            mul_le_mul_of_nonneg_right (by
              dsimp [e]
              exact min_le_right _ _) (le_of_lt hM)
          _ = g / 2 := by field_simp
      refine ⟨Set.Ioo (p.1 - e) (p.1 + e) ×ˢ
          Set.Ioo (p.2 - e) (p.2 + e), ?_,
        isOpen_Ioo.prod isOpen_Ioo, ?_⟩
      · intro q hq
        rcases hq with ⟨⟨hq1l, hq1u⟩, ⟨hq2l, hq2u⟩⟩
        have hd1 : |q.1 - p.1| < e := (abs_lt).2 ⟨by linarith, by linarith⟩
        have hd2 : |q.2 - p.2| < e := (abs_lt).2 ⟨by linarith, by linarith⟩
        have hprod : |q.1 - p.1| * |q.2 - p.2| < e * e := by
          nlinarith [
            mul_nonneg (sub_nonneg.mpr (le_of_lt hd1)) (abs_nonneg (q.2 - p.2)),
            mul_pos he (sub_pos.mpr hd2)]
        have hp1 : |p.1| * |q.2 - p.2| ≤ |p.1| * e :=
          mul_le_mul_of_nonneg_left (le_of_lt hd2) (abs_nonneg _)
        have hp2 : |p.2| * |q.1 - p.1| ≤ |p.2| * e :=
          mul_le_mul_of_nonneg_left (le_of_lt hd1) (abs_nonneg _)
        have habs : |q.1 * q.2 - p.1 * p.2| < g := by
          calc
            |q.1 * q.2 - p.1 * p.2| =
                |(q.1 - p.1) * (q.2 - p.2) + p.1 * (q.2 - p.2) +
                  p.2 * (q.1 - p.1)| := by congr 1 <;> ring
            _ ≤ |(q.1 - p.1) * (q.2 - p.2) + p.1 * (q.2 - p.2)| +
                  |p.2 * (q.1 - p.1)| := abs_add_le _ _
            _ ≤ (|(q.1 - p.1) * (q.2 - p.2)| +
                  |p.1 * (q.2 - p.2)|) + |p.2 * (q.1 - p.1)| :=
              add_le_add (abs_add_le _ _) (le_refl _)
            _ = |q.1 - p.1| * |q.2 - p.2| + |p.1| * |q.2 - p.2| +
                  |p.2| * |q.1 - p.1| := by rw [abs_mul, abs_mul, abs_mul]
            _ < e * e + |p.1| * e + |p.2| * e := by linarith
            _ ≤ e * M := by
              dsimp [M]
              nlinarith [mul_nonneg (le_of_lt he) (sub_nonneg.mpr he1)]
            _ ≤ g / 2 := heM
            _ < g := by nlinarith
        change q.1 * q.2 < a
        have hupp := (abs_lt.1 habs).2
        dsimp [g] at hupp
        linarith
      · exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  letI : ContinuousAdd ℝ := ⟨hadd⟩
  letI : ContinuousNeg ℝ := ⟨hneg⟩
  letI : ContinuousSub ℝ := ⟨by
    change Continuous (fun p : ℝ × ℝ => p.1 + -p.2)
    fun_prop⟩
  letI : ContinuousMul ℝ := ⟨hmul⟩
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  let U : Finset (Finset A) := Finset.univ.powerset
  let X := A × (ℝ × (Finset A → ℝ))
  letI : TopologicalSpace X :=
    inferInstanceAs (TopologicalSpace (A × (ℝ × (Finset A → ℝ))))
  let same (i j : A) : ℝ := if j = i then 1 else 0
  let seen (i j : A) (S : Finset A) : ℝ :=
    if i ∈ S ∨ j ∈ S then 1 else 0
  let detect (x : X) (j : A) : ℝ :=
    U.sum fun S => seen x.1 j S * x.2.2 S
  let agentValue (x : X) (j : A) : ℝ :=
    same x.1 j * (x.2.1 * d.success j - d.cost j) +
      (1 - same x.1 j) *
        (x.2.1 * d.success j * (1 - detect x j) - d.cost j)
  let suggestedValue (x : X) : ℝ :=
    x.2.1 * d.success x.1 - d.cost x.1
  let principalValue (x : X) : ℝ :=
    (1 - x.2.1) * d.success x.1 -
      U.sum fun S => x.2.2 S * d.inspectionCost S
  let box : Set X :=
    Set.univ ×ˢ Set.Icc ((0 : ℝ), fun _ => (0 : ℝ)) (1, fun _ => 1)
  let total (x : X) : ℝ := U.sum x.2.2
  let K : Set X :=
    box ∩ {x | total x = 1} ∩
      {x | ∀ j : A, agentValue x j ≤ suggestedValue x}
  have hmass (S : Finset A) : Continuous (fun x : X => x.2.2 S) := by
    fun_prop
  have hsame (j : A) : Continuous (fun x : X => same x.1 j) :=
    (continuous_of_discreteTopology :
      Continuous (fun i : A => same i j)).comp continuous_fst
  have hseen (j : A) (S : Finset A) :
      Continuous (fun x : X => seen x.1 j S) :=
    (continuous_of_discreteTopology :
      Continuous (fun i : A => seen i j S)).comp continuous_fst
  have hsuccess : Continuous (fun x : X => d.success x.1) :=
    (continuous_of_discreteTopology :
      Continuous d.success).comp continuous_fst
  have hcost : Continuous (fun x : X => d.cost x.1) :=
    (continuous_of_discreteTopology :
      Continuous d.cost).comp continuous_fst
  have hdetect (j : A) : Continuous (fun x : X => detect x j) := by
    dsimp [detect]
    apply continuous_finset_sum
    intro S hS
    exact (hseen j S).mul (hmass S)
  have hau (j : A) : Continuous (fun x : X => agentValue x j) := by
    dsimp [agentValue]
    exact
      (hsame j).mul ((by fun_prop : Continuous (fun x : X => x.2.1)).mul
        continuous_const |>.sub continuous_const) |>.add
      ((continuous_const.sub (hsame j)).mul
        (((by fun_prop : Continuous (fun x : X => x.2.1)).mul
          continuous_const).mul (continuous_const.sub (hdetect j)) |>.sub
          continuous_const))
  have hsuggested : Continuous suggestedValue := by
    dsimp [suggestedValue]
    fun_prop (disch := aesop)
  have hprincipal : Continuous principalValue := by
    dsimp [principalValue]
    fun_prop (disch := aesop)
  have htotal : Continuous total := by
    dsimp [total]
    fun_prop
  have hbox : IsCompact box := by
    dsimp [box]
    exact Set.finite_univ.isCompact.prod isCompact_Icc
  have htotalClosed : IsClosed {x : X | total x = 1} :=
    isClosed_eq htotal continuous_const
  have hicClosed :
      IsClosed {x : X | ∀ j : A, agentValue x j ≤ suggestedValue x} := by
    rw [show {x : X | ∀ j : A, agentValue x j ≤ suggestedValue x} =
        ⋂ j : A, {x : X | agentValue x j ≤ suggestedValue x} by
      ext x
      simp]
    exact isClosed_iInter fun j => isClosed_le (hau j) hsuggested
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact (hbox.inter_right htotalClosed).inter_right hicClosed
  let x0 : X :=
    (d.nullAction, (0, fun S : Finset A => if S = ∅ then 1 else 0))
  have hx0box : x0 ∈ box := by
    dsimp [x0, box]
    refine ⟨Set.mem_univ _, ?_⟩
    constructor
    · refine ⟨le_rfl, ?_⟩
      intro S
      change 0 ≤ if S = ∅ then 1 else 0
      split_ifs <;> norm_num
    · refine ⟨by norm_num, ?_⟩
      intro S
      change (if S = ∅ then 1 else 0) ≤ 1
      split_ifs <;> norm_num
  have hx0total : total x0 = 1 := by
    simp [total, x0, U]
  have hx0ic : ∀ j : A, agentValue x0 j ≤ suggestedValue x0 := by
    intro j
    dsimp [agentValue, suggestedValue, x0, same]
    split_ifs <;> simp_all [hadm.1 j, hadm.2.2.2.2.2]
  have hx0K : x0 ∈ K := ⟨⟨hx0box, hx0total⟩, hx0ic⟩
  obtain ⟨x, hxK, hxmax⟩ :=
    hKcompact.exists_isMaxOn ⟨x0, hx0K⟩ hprincipal.continuousOn
  let p : inspection_distribution A :=
    { mass := x.2.2
      mass_nonneg := fun S => hxK.1.1.2.1.2 S
      total_mass := by simpa [total, U] using hxK.1.2 }
  let s : inspection_scheme A :=
    { suggested := x.1
      payment := x.2.1
      inspection := p }
  have hdetectScheme (j : A) :
      detection_probability p x.1 j = detect x j := by
    simp [detection_probability, detect, seen, p, U, Finset.sum_filter]
  have hagentScheme (j : A) :
      agent_utility d s j = agentValue x j := by
    by_cases hji : j = x.1
    · simp [agent_utility, agentValue, same, s, hji]
    · simp [agent_utility, agentValue, same, s, hji, hdetectScheme]
  have hsuggestedScheme :
      agent_utility d s s.suggested = suggestedValue x := by
    simp [agent_utility, suggestedValue, s]
  have hsFeasible : feasible_inspection_scheme d s := by
    refine ⟨hxK.1.1.2.1.1, hxK.1.1.2.2.1, ?_⟩
    intro j
    rw [hagentScheme, hsuggestedScheme]
    exact hxK.2 j
  have hprincipalScheme :
      principal_utility d s s.suggested = principalValue x := by
    simp [principal_utility, principalValue, expected_inspection_cost, s, p, U]
  refine ⟨s, hsFeasible, ?_⟩
  intro t ht
  let y : X := (t.suggested, (t.payment, t.inspection.mass))
  have hmassUpper (S : Finset A) : t.inspection.mass S ≤ 1 := by
    calc
      t.inspection.mass S ≤ U.sum t.inspection.mass := by
        apply Finset.single_le_sum
        · intro T hT
          exact t.inspection.mass_nonneg T
        · simp [U]
      _ = 1 := by simpa [U] using t.inspection.total_mass
  have hybox : y ∈ box := by
    refine ⟨Set.mem_univ _, ?_⟩
    constructor
    · exact ⟨ht.1, t.inspection.mass_nonneg⟩
    · exact ⟨ht.2.1, hmassUpper⟩
  have hytotal : total y = 1 := by
    simpa [total, y, U] using t.inspection.total_mass
  have hdetectT (j : A) :
      detection_probability t.inspection t.suggested j = detect y j := by
    simp [detection_probability, detect, seen, y, U, Finset.sum_filter]
  have hagentT (j : A) :
      agent_utility d t j = agentValue y j := by
    by_cases hji : j = t.suggested
    · simp [agent_utility, agentValue, same, y, hji]
    · simp [agent_utility, agentValue, same, y, hji, hdetectT]
  have hsuggestedT :
      agent_utility d t t.suggested = suggestedValue y := by
    simp [agent_utility, suggestedValue, y]
  have hyic : ∀ j : A, agentValue y j ≤ suggestedValue y := by
    intro j
    rw [← hagentT, ← hsuggestedT]
    exact ht.2.2 j
  have hyK : y ∈ K := ⟨⟨hybox, hytotal⟩, hyic⟩
  have hprincipalT :
      principal_utility d t t.suggested = principalValue y := by
    simp [principal_utility, principalValue, expected_inspection_cost, y, U]
  calc
    principal_utility d t t.suggested = principalValue y := hprincipalT
    _ ≤ principalValue x := hxmax hyK
    _ = principal_utility d s s.suggested := hprincipalScheme.symm

@[blueprint "lem:small-support-optimal-inspection-scheme"
  (statement := /-- Let $A$ be a finite action set, and let $d$ be admissible contract data on $A$ whose inspection-cost function is submodular.  Then there exists an optimal feasible, and hence incentive-compatible, inspection scheme for $d$ whose inspection distribution is supported on at most $|A|+1$ subsets of $A$. -/)
  (proof := /-- Choose a globally optimal scheme $s$ by \cref{lem:optimal-inspection-scheme-exists}.  Apply \cref{lem:suggested-action-normalization} at the action suggested by $s$, and let $s_1$ retain the suggested action and payment of $s$ while using the resulting separated distribution.  The preserved detection probabilities and \cref{def:agent-utility} show that every action has the same agent utility under $s_1$ as under $s$.  Hence $s_1$ is feasible by \cref{def:feasible-inspection-scheme}.  Its weakly lower expected inspection cost gives it weakly greater principal utility by \cref{def:principal-utility}; the optimality of $s$ therefore implies that $s_1$ is optimal according to \cref{def:optimal-inspection-scheme}.

  The hypotheses in \cref{def:admissible-contract-data}, together with the assumed submodularity, permit the application of \cref{lem:submodular-small-support-replacement} to the inspection distribution of $s_1$.  Let $s_2$ retain the suggested action and payment of $s_1$ and use the replacement distribution.  Preservation of all detection probabilities again preserves every agent utility and therefore feasibility, while the expected-cost inequality weakly increases principal utility.  Thus the optimality of $s_1$ implies that $s_2$ is optimal.  The support-cardinality conclusion of the replacement lemma gives $|\operatorname{supp}(s_2)|\leq |A|+1$, as required. -/)
  (title := /-- An optimal scheme with small support -/)
  (latexEnv := "lemma")]
lemma small_support_optimal_inspection_scheme
    {A : Type} [Fintype A] [DecidableEq A]
    (d : contract_data A) (hadm : admissible_contract_data d)
    (hsubmod : submodular_inspection_cost d.inspectionCost) :
    ∃ s : inspection_scheme A,
      optimal_inspection_scheme d s ∧
      (inspection_support s.inspection).card ≤ Fintype.card A + 1 := by
  rcases optimal_inspection_scheme_exists d hadm with ⟨s, hs⟩
  obtain ⟨p, hpsep, hpdetect, hpcost⟩ :=
    suggested_action_normalization d.inspectionCost hadm.2.2.2.2.1
      s.suggested s.inspection
  let s₁ : inspection_scheme A := { s with inspection := p }
  have hagent₁ (j : A) : agent_utility d s₁ j = agent_utility d s j := by
    by_cases hj : j = s.suggested
    · simp [agent_utility, s₁, hj]
    · simp [agent_utility, s₁, hj, hpdetect j]
  have hs₁feas : feasible_inspection_scheme d s₁ := by
    refine ⟨by simpa [s₁] using hs.1.1, by simpa [s₁] using hs.1.2.1, ?_⟩
    intro j
    calc
      agent_utility d s₁ j = agent_utility d s j := hagent₁ j
      _ ≤ agent_utility d s s.suggested := hs.1.2.2 j
      _ = agent_utility d s₁ s₁.suggested := by
        simpa [s₁] using (hagent₁ s.suggested).symm
  have hprincipal₁ :
      principal_utility d s s.suggested ≤
        principal_utility d s₁ s₁.suggested := by
    simpa [principal_utility, s₁] using
      (sub_le_sub_left hpcost ((1 - s.payment) * d.success s.suggested))
  have hs₁ : optimal_inspection_scheme d s₁ :=
    ⟨hs₁feas, fun t ht => (hs.2 t ht).trans hprincipal₁⟩
  obtain ⟨q, hqsep, hqdetect, hqcost, hqnested, hqcard⟩ :=
    submodular_small_support_replacement d.inspectionCost hadm.2.2.1
      hadm.2.2.2.1 hadm.2.2.2.2.1 hsubmod s.suggested p hpsep
  let s₂ : inspection_scheme A := { s₁ with inspection := q }
  have hagent₂ (j : A) : agent_utility d s₂ j = agent_utility d s₁ j := by
    by_cases hj : j = s.suggested
    · simp [agent_utility, s₁, s₂, hj]
    · simp [agent_utility, s₁, s₂, hj, hqdetect j]
  have hs₂feas : feasible_inspection_scheme d s₂ := by
    refine ⟨by simpa [s₂] using hs₁.1.1, by simpa [s₂] using hs₁.1.2.1, ?_⟩
    intro j
    calc
      agent_utility d s₂ j = agent_utility d s₁ j := hagent₂ j
      _ ≤ agent_utility d s₁ s₁.suggested := hs₁.1.2.2 j
      _ = agent_utility d s₂ s₂.suggested := by
        simpa [s₁, s₂] using (hagent₂ s.suggested).symm
  have hprincipal₂ :
      principal_utility d s₁ s₁.suggested ≤
        principal_utility d s₂ s₂.suggested := by
    simpa [principal_utility, s₁, s₂] using
      (sub_le_sub_left hqcost ((1 - s.payment) * d.success s.suggested))
  refine ⟨s₂, ⟨hs₂feas, fun t ht => (hs₁.2 t ht).trans hprincipal₂⟩, ?_⟩
  simpa [s₂] using hqcard

@[blueprint "def:abstract-submodular-value-oracle-solver"
  (statement := /-- An abstract submodular value-oracle solver consists of three uniform maps.  For every finite action type, contract datum, and action encoding, they specify an inspection scheme, the finite adaptive transcript of inspected sets queried from the cost oracle, and the charged amount of work.  If a replacement cost oracle agrees with the original oracle on the transcript, then the replacement run has the same transcript, work, and output.  There are constants $C,k\in\mathbb{N}$, independent of the action type and instance, for which both the work and the number of queries are at most $C(|A|+1)^k$ on every valid encoding.  Finally, on every admissible instance with submodular inspection cost, the output is globally optimal and its inspection distribution has support of cardinality at most $|A|+1$. -/)
  (title := /-- Abstract polynomial-time submodular value-oracle solver -/)
  (latexEnv := "definition")]
structure abstract_submodular_value_oracle_solver where
  solve : ∀ (A : Type) [Fintype A] [DecidableEq A],
    contract_data A → List A → inspection_scheme A
  queries : ∀ (A : Type) [Fintype A] [DecidableEq A],
    contract_data A → List A → List (Finset A)
  work : ∀ (A : Type) [Fintype A] [DecidableEq A],
    contract_data A → List A → ℕ
  transcript_stable :
    ∀ (A : Type) [Fintype A] [DecidableEq A]
      (d : contract_data A) (encoding : List A) (v' : Finset A → ℝ),
      action_encoding encoding →
      (∀ S : Finset A,
        S ∈ queries A d encoding → v' S = d.inspectionCost S) →
      queries A (replace_inspection_cost d v') encoding = queries A d encoding ∧
      work A (replace_inspection_cost d v') encoding = work A d encoding ∧
      solve A (replace_inspection_cost d v') encoding = solve A d encoding
  polynomial_resources :
    ∃ C k : ℕ, ∀ (A : Type) [Fintype A] [DecidableEq A]
      (d : contract_data A) (encoding : List A), action_encoding encoding →
      let bound := C * (Fintype.card A + 1) ^ k
      work A d encoding ≤ bound ∧ (queries A d encoding).length ≤ bound
  correctness :
    ∀ (A : Type) [Fintype A] [DecidableEq A]
      (d : contract_data A) (encoding : List A), action_encoding encoding →
      admissible_contract_data d →
      submodular_inspection_cost d.inspectionCost →
      optimal_inspection_scheme d (solve A d encoding) ∧
      (inspection_support (solve A d encoding).inspection).card ≤
        Fintype.card A + 1

@[blueprint "lem:polynomial-time-submodular-oracle-solver"
  (statement := /-- There exists a uniform abstract submodular value-oracle solver in the sense of \cref{def:abstract-submodular-value-oracle-solver}.  Thus, for every finite action space and every encoding of its actions, the solver has an oracle-stable finite query transcript and a uniformly polynomial bound on its work and number of value queries, and on every admissible instance with submodular inspection cost it returns a globally optimal inspection scheme supported on at most $|A|+1$ sets.  In addition, for every finite action space $A$ and every admissible contract datum $d$ on $A$ with submodular inspection cost, there exists an optimal incentive-compatible inspection scheme whose inspection distribution has support of cardinality at most $|A|+1$. -/)
  (proof := /-- Apply the polynomial-time value-oracle construction for submodular inspection costs.  For each finite action space, admissible datum, and action encoding, take its output scheme, its ordered list of oracle queries, and its charged work as the three maps in \cref{def:abstract-submodular-value-oracle-solver}.  If a replacement inspection-cost oracle agrees with the original oracle on that adaptive query transcript, induction over the successive oracle calls shows that every answer, subsequent query, charged operation, and ultimately the output scheme is unchanged.  The uniform polynomial bounds proved for the construction furnish constants $C,k\in\mathbb{N}$ bounding both the charged work and the transcript length by $C(|A|+1)^k$.  Its correctness theorem gives global optimality, and its submodular chain construction uses at most $|A|+1$ sets, so these data form an abstract submodular value-oracle solver.

  For the additional per-instance assertion, fix a finite action space $A$ and admissible contract data $d$ with submodular inspection cost.  Applying \cref{lem:small-support-optimal-inspection-scheme} gives an optimal inspection scheme whose inspection distribution is supported on at most $|A|+1$ sets. -/)
  (title := /-- Uniform polynomial-time value-oracle solution for submodular inspection -/)
  (latexEnv := "lemma")]
lemma polynomial_time_submodular_oracle_solver
    : Nonempty abstract_submodular_value_oracle_solver ∧
      ∀ (A : Type) [Fintype A] [DecidableEq A]
        (d : contract_data A), admissible_contract_data d →
        submodular_inspection_cost d.inspectionCost →
        ∃ s : inspection_scheme A,
          optimal_inspection_scheme d s ∧
          (inspection_support s.inspection).card ≤ Fintype.card A + 1 := by
  classical
  refine ⟨?_, fun A _ _ d hadm hsub =>
    small_support_optimal_inspection_scheme d hadm hsub⟩
  have chainmono : ∀ (A : Type) [DecidableEq A] (v : Finset A → ℝ),
        Monotone v → ∀ (U : Finset (Finset A)) (w z : Finset A → ℝ)
        (P : Finset A) (l : List A),
        (∀ a ∈ l, U.sum (fun S => if a ∈ S then w S else 0) ≤
          U.sum (fun S => if a ∈ S then z S else 0)) →
        U.sum (fun S => w S * submodular_chain_increment v P l S) ≤
          U.sum (fun S => z S * submodular_chain_increment v P l S) := by
    intro A _ v hmono U w z P l
    induction l generalizing P with
    | nil =>
        intro _
        apply le_of_eq
        apply finite_real_sum_congr
        intro S hS
        simp [submodular_chain_increment]
    | cons a l ih =>
        intro hmarg
        have hhead := hmarg a (by simp)
        have htail : ∀ b ∈ l, U.sum (fun S => if b ∈ S then w S else 0) ≤
            U.sum (fun S => if b ∈ S then z S else 0) := by
          intro b hb
          exact hmarg b (by simp [hb])
        have hih := ih (insert a P) htail
        have hw :
            U.sum (fun S =>
              w S * (if a ∈ S then v (insert a P) - v P else 0)) =
              U.sum (fun S => if a ∈ S then w S else 0) *
                (v (insert a P) - v P) := by
          rw [← finite_real_sum_mul_right]
          apply finite_real_sum_congr
          intro S hS
          by_cases haS : a ∈ S <;> simp [haS]
        have hz :
            U.sum (fun S =>
              z S * (if a ∈ S then v (insert a P) - v P else 0)) =
              U.sum (fun S => if a ∈ S then z S else 0) *
                (v (insert a P) - v P) := by
          rw [← finite_real_sum_mul_right]
          apply finite_real_sum_congr
          intro S hS
          by_cases haS : a ∈ S <;> simp [haS]
        have hincnn : 0 ≤ v (insert a P) - v P :=
          sub_nonneg.mpr (hmono (Finset.subset_insert a P))
        simp only [submodular_chain_increment, mul_add]
        rw [finite_real_sum_add, finite_real_sum_add, hw, hz]
        exact add_le_add (mul_le_mul_of_nonneg_right hhead hincnn) hih
  have rep : ∀ (R : Finset ℝ) (K : ℝ),
        ∃ K' ∈ R ∪ insert 0 ((R.image fun ρ => ρ - 1) ∪ (R.image fun ρ => ρ + 1) ∪
            ((R ×ˢ R).image fun z => (z.1 + z.2) / 2)),
          ∀ ρ ∈ R, (K ≤ ρ ↔ K' ≤ ρ) ∧ (ρ ≤ K ↔ ρ ≤ K') := by
    classical
    intro R K
    by_cases hK : K ∈ R
    · exact ⟨K, Finset.mem_union_left _ hK, fun ρ _ => ⟨Iff.rfl, Iff.rfl⟩⟩
    · have hsplit : ∀ ρ ∈ R, ρ < K ∨ K < ρ := by
        intro ρ hρ
        rcases lt_trichotomy ρ K with h | h | h
        · exact Or.inl h
        · exact absurd (h ▸ hρ) hK
        · exact Or.inr h
      by_cases hlo : (R.filter fun ρ => ρ < K).Nonempty
      · by_cases hhi : (R.filter fun ρ => K < ρ).Nonempty
        · obtain ⟨ρ₁, hρ₁mem, hρ₁max⟩ :
              ∃ ρ₁ ∈ R.filter fun ρ => ρ < K,
                ∀ ρ ∈ R.filter fun ρ => ρ < K, ρ ≤ ρ₁ :=
            ⟨(R.filter fun ρ => ρ < K).max' hlo,
              (R.filter fun ρ => ρ < K).max'_mem hlo,
              fun ρ hρ => (R.filter fun ρ => ρ < K).le_max' ρ hρ⟩
          obtain ⟨ρ₂, hρ₂mem, hρ₂min⟩ :
              ∃ ρ₂ ∈ R.filter fun ρ => K < ρ,
                ∀ ρ ∈ R.filter fun ρ => K < ρ, ρ₂ ≤ ρ :=
            ⟨(R.filter fun ρ => K < ρ).min' hhi,
              (R.filter fun ρ => K < ρ).min'_mem hhi,
              fun ρ hρ => (R.filter fun ρ => K < ρ).min'_le ρ hρ⟩
          have hρ₁R : ρ₁ ∈ R := (Finset.mem_filter.mp hρ₁mem).1
          have hρ₁K : ρ₁ < K := (Finset.mem_filter.mp hρ₁mem).2
          have hρ₂R : ρ₂ ∈ R := (Finset.mem_filter.mp hρ₂mem).1
          have hKρ₂ : K < ρ₂ := (Finset.mem_filter.mp hρ₂mem).2
          refine ⟨(ρ₁ + ρ₂) / 2, ?_, ?_⟩
          · refine Finset.mem_union_right _ (Finset.mem_insert_of_mem ?_)
            refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(ρ₁, ρ₂), ?_, rfl⟩)
            exact Finset.mem_product.mpr ⟨hρ₁R, hρ₂R⟩
          · have h1 : ρ₁ < (ρ₁ + ρ₂) / 2 := by
              have : ρ₁ < ρ₂ := hρ₁K.trans hKρ₂
              linarith
            have h2 : (ρ₁ + ρ₂) / 2 < ρ₂ := by
              have : ρ₁ < ρ₂ := hρ₁K.trans hKρ₂
              linarith
            intro ρ hρ
            rcases hsplit ρ hρ with h | h
            · have hle : ρ ≤ ρ₁ :=
                hρ₁max ρ (Finset.mem_filter.mpr ⟨hρ, h⟩)
              constructor
              · constructor
                · intro hc; exact absurd (lt_of_le_of_lt hc h) (lt_irrefl K)
                · intro hc
                  exact absurd (lt_of_le_of_lt hc (lt_of_le_of_lt hle h1))
                    (lt_irrefl _)
              · exact ⟨fun _ => by linarith, fun _ => le_of_lt h⟩
            · have hge : ρ₂ ≤ ρ := hρ₂min ρ (Finset.mem_filter.mpr ⟨hρ, h⟩)
              constructor
              · exact ⟨fun _ => by linarith, fun _ => le_of_lt h⟩
              · constructor
                · intro hc; exact absurd (lt_of_lt_of_le h hc) (lt_irrefl _)
                · intro hc
                  exact absurd (lt_of_lt_of_le (lt_of_lt_of_le h2 hge) hc)
                    (lt_irrefl _)
        · obtain ⟨ρ₁, hρ₁mem, hρ₁max⟩ :
              ∃ ρ₁ ∈ R.filter fun ρ => ρ < K,
                ∀ ρ ∈ R.filter fun ρ => ρ < K, ρ ≤ ρ₁ :=
            ⟨(R.filter fun ρ => ρ < K).max' hlo,
              (R.filter fun ρ => ρ < K).max'_mem hlo,
              fun ρ hρ => (R.filter fun ρ => ρ < K).le_max' ρ hρ⟩
          have hρ₁R : ρ₁ ∈ R := (Finset.mem_filter.mp hρ₁mem).1
          refine ⟨ρ₁ + 1, ?_, ?_⟩
          · refine Finset.mem_union_right _ (Finset.mem_insert_of_mem ?_)
            exact Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨ρ₁, hρ₁R, rfl⟩))
          · intro ρ hρ
            have h : ρ < K := by
              rcases hsplit ρ hρ with h | h
              · exact h
              · exact absurd ⟨ρ, Finset.mem_filter.mpr ⟨hρ, h⟩⟩ hhi
            have hle : ρ ≤ ρ₁ := hρ₁max ρ (Finset.mem_filter.mpr ⟨hρ, h⟩)
            constructor
            · constructor
              · intro hc; exact absurd (lt_of_le_of_lt hc h) (lt_irrefl K)
              · intro hc; linarith
            · exact ⟨fun _ => by linarith, fun _ => le_of_lt h⟩
      · by_cases hhi : (R.filter fun ρ => K < ρ).Nonempty
        · obtain ⟨ρ₂, hρ₂mem, hρ₂min⟩ :
              ∃ ρ₂ ∈ R.filter fun ρ => K < ρ,
                ∀ ρ ∈ R.filter fun ρ => K < ρ, ρ₂ ≤ ρ :=
            ⟨(R.filter fun ρ => K < ρ).min' hhi,
              (R.filter fun ρ => K < ρ).min'_mem hhi,
              fun ρ hρ => (R.filter fun ρ => K < ρ).min'_le ρ hρ⟩
          have hρ₂R : ρ₂ ∈ R := (Finset.mem_filter.mp hρ₂mem).1
          refine ⟨ρ₂ - 1, ?_, ?_⟩
          · refine Finset.mem_union_right _ (Finset.mem_insert_of_mem ?_)
            exact Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ρ₂, hρ₂R, rfl⟩))
          · intro ρ hρ
            have h : K < ρ := by
              rcases hsplit ρ hρ with h | h
              · exact absurd ⟨ρ, Finset.mem_filter.mpr ⟨hρ, h⟩⟩ hlo
              · exact h
            have hge : ρ₂ ≤ ρ := hρ₂min ρ (Finset.mem_filter.mpr ⟨hρ, h⟩)
            constructor
            · exact ⟨fun _ => by linarith, fun _ => le_of_lt h⟩
            · constructor
              · intro hc; exact absurd (lt_of_lt_of_le h hc) (lt_irrefl _)
              · intro hc; linarith
        · refine ⟨0, ?_, ?_⟩
          · exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
          · intro ρ hρ
            rcases hsplit ρ hρ with h | h
            · exact absurd ⟨ρ, Finset.mem_filter.mpr ⟨hρ, h⟩⟩ hlo
            · exact absurd ⟨ρ, Finset.mem_filter.mpr ⟨hρ, h⟩⟩ hhi
  have cmpeq : ∀ (A : Type) [Fintype A] [DecidableEq A] (c f : A → ℝ)
        (key : ℝ → A → ℝ),
        (∀ (K : ℝ) (j : A), key K j =
          if 0 < f j then (c j + K) / f j else 1 + ∑ a : A, |(c a + K) / f a|) →
        ∀ K K' : ℝ,
          (∀ a b : A, (K * (f b - f a) ≤ c b * f a - c a * f b ↔
            K' * (f b - f a) ≤ c b * f a - c a * f b)) →
          (fun a b : A => decide (key K a ≤ key K b)) =
            (fun a b : A => decide (key K' a ≤ key K' b)) := by
    classical
    intro A _ _ c f key hkey K K' hsign
    have hbig : ∀ (L : ℝ) (a : A), 0 < f a →
        (c a + L) / f a < 1 + ∑ x : A, |(c x + L) / f x| := by
      intro L a _
      have h1 : (c a + L) / f a ≤ |(c a + L) / f a| := le_abs_self _
      have h2 : |(c a + L) / f a| ≤ ∑ x : A, |(c x + L) / f x| := by
        apply Finset.single_le_sum (f := fun x : A => |(c x + L) / f x|)
        · intro x _
          exact abs_nonneg _
        · exact Finset.mem_univ a
      linarith
    funext a b
    apply decide_eq_decide.mpr
    by_cases hfa : 0 < f a
    · by_cases hfb : 0 < f b
      · rw [hkey, hkey, hkey, hkey]
        simp only [hfa, hfb, if_true]
        rw [div_le_div_iff₀ hfa hfb, div_le_div_iff₀ hfa hfb]
        constructor
        · intro h
          have := (hsign a b).mp (by nlinarith)
          nlinarith
        · intro h
          have := (hsign a b).mpr (by nlinarith)
          nlinarith
      · rw [hkey, hkey, hkey, hkey]
        simp only [hfa, hfb, if_true, if_false]
        exact ⟨fun _ => le_of_lt (hbig K' a hfa), fun _ => le_of_lt (hbig K a hfa)⟩
    · by_cases hfb : 0 < f b
      · rw [hkey, hkey, hkey, hkey]
        simp only [hfa, hfb, if_true, if_false]
        constructor
        · intro h
          exact absurd (lt_of_le_of_lt h (hbig K b hfb)) (lt_irrefl _)
        · intro h
          exact absurd (lt_of_le_of_lt h (hbig K' b hfb)) (lt_irrefl _)
      · rw [hkey, hkey, hkey, hkey]
        simp only [hfa, hfb, if_false]
        exact ⟨fun _ => le_refl _, fun _ => le_refl _⟩
  have core : ∀ (A : Type) [Fintype A] [DecidableEq A]
        (chainmono : ∀ (v : Finset A → ℝ), Monotone v →
          ∀ (U : Finset (Finset A)) (w z : Finset A → ℝ) (P : Finset A) (l : List A),
            (∀ a ∈ l, U.sum (fun S => if a ∈ S then w S else 0) ≤
              U.sum (fun S => if a ∈ S then z S else 0)) →
            U.sum (fun S => w S * submodular_chain_increment v P l S) ≤
              U.sum (fun S => z S * submodular_chain_increment v P l S))
        (d : contract_data A) (key : ℝ → A → ℝ)
        (hkey : ∀ (K : ℝ) (j : A), key K j =
          if 0 < d.success j then (d.cost j + K) / d.success j
          else 1 + ∑ a : A, |(d.cost a + K) / d.success a|)
        (Lam : Finset ℝ)
        (hLamrep : ∀ K : ℝ, ∃ K' ∈ Lam,
          (fun a b : A => decide (key K a ≤ key K b)) =
            (fun a b : A => decide (key K' a ≤ key K' b)))
        (QQ : Finset (Finset A))
        (hQ1 : ∀ i : A, ({i} : Finset A) ∈ QQ)
        (hQ2 : ∀ (i : A) (K' : ℝ), K' ∈ Lam → ∀ k : ℕ, k ≤ Fintype.card A →
          ((((Finset.univ.erase i).toList.mergeSort
            (fun a b => decide (key K' a ≤ key K' b))).take k).toFinset) ∈ QQ),
        admissible_contract_data d →
        submodular_inspection_cost d.inspectionCost →
        ∃ s : inspection_scheme A, optimal_inspection_scheme d s ∧
          inspection_support s.inspection ⊆ QQ ∧
          (inspection_support s.inspection).card ≤ Fintype.card A + 1 := by
    classical
    intro A _ _ chainmono d key hkey Lam hLamrep QQ hQ1 hQ2 hadm hsubmod
    obtain ⟨hc_nonneg, hf_bounds, hv_nonneg, hv_empty, hv_mono, hc_null⟩ := hadm
    have hadm' : admissible_contract_data d :=
      ⟨hc_nonneg, hf_bounds, hv_nonneg, hv_empty, hv_mono, hc_null⟩
    rcases optimal_inspection_scheme_exists d hadm' with ⟨s, hs⟩
    obtain ⟨p, hpsep, hpdetect, hpcost⟩ :=
      suggested_action_normalization d.inspectionCost hv_mono s.suggested
        s.inspection
    let s₁ : inspection_scheme A := { s with inspection := p }
    have hagent₁ : ∀ j : A, agent_utility d s₁ j = agent_utility d s j := by
      intro j
      by_cases hj : j = s.suggested
      · simp [agent_utility, s₁, hj]
      · simp [agent_utility, s₁, hj, hpdetect j]
    have hs₁feas : feasible_inspection_scheme d s₁ := by
      refine ⟨by simpa [s₁] using hs.1.1, by simpa [s₁] using hs.1.2.1, ?_⟩
      intro j
      calc
        agent_utility d s₁ j = agent_utility d s j := hagent₁ j
        _ ≤ agent_utility d s s.suggested := hs.1.2.2 j
        _ = agent_utility d s₁ s₁.suggested := by
          simpa [s₁] using (hagent₁ s.suggested).symm
    have hprincipal₁ :
        principal_utility d s s.suggested ≤
          principal_utility d s₁ s₁.suggested := by
      simpa [principal_utility, s₁] using
        (sub_le_sub_left hpcost ((1 - s.payment) * d.success s.suggested))
    have hs₁ : optimal_inspection_scheme d s₁ :=
      ⟨hs₁feas, fun u hu => (hs.2 u hu).trans hprincipal₁⟩
    set i : A := s.suggested with hi
    set α : ℝ := s.payment with hα
    set v : Finset A → ℝ := d.inspectionCost with hv
    set c : A → ℝ := d.cost with hcdef
    set f : A → ℝ := d.success with hfdef
    have hα0 : 0 ≤ α := hs₁.1.1
    have hf_nonneg : ∀ j : A, 0 ≤ f j := fun j => (hf_bounds j).1
    let B : Finset A := Finset.univ.erase i
    let r : ℝ := p.mass {i}
    let t : ℝ := B.powerset.sum p.mass
    let x : A → ℝ := fun j =>
      B.powerset.sum (fun S => if j ∈ S then p.mass S else 0)
    set K : ℝ := α * f i - c i with hK
    let y : A → ℝ := fun j =>
      if 0 < α * f j then
        max 0 ((α * f j * (1 - r) - c j - K) / (α * f j))
      else 0
    let l : List A := B.toList.mergeSort (fun a b => decide (key K a ≤ key K b))
    have hiB : i ∉ B := by simp [B]
    have hBi : insert i B = Finset.univ := by
      ext a
      simp [B]
    have hl_nodup : l.Nodup := by
      simpa [l] using B.nodup_toList
    have hl_fin : l.toFinset = B := by
      ext a
      simp [l]
    have hl_keysorted : l.Pairwise fun a b => key K a ≤ key K b := by
      have hsorted := List.pairwise_mergeSort
        (le := fun a b : A => decide (key K a ≤ key K b))
        (fun a b e hab hbc => by
          simp only [decide_eq_true_eq] at hab hbc ⊢
          exact hab.trans hbc)
        (fun a b => by
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          exact le_total (key K a) (key K b)) B.toList
      have := hsorted
      simp only [decide_eq_true_eq] at this
      simpa [l] using this
    have hbig : ∀ (L : ℝ) (a : A), 0 < f a →
        (c a + L) / f a < 1 + ∑ z : A, |(c z + L) / f z| := by
      intro L a _
      have h1 : (c a + L) / f a ≤ |(c a + L) / f a| := le_abs_self _
      have h2 : |(c a + L) / f a| ≤ ∑ z : A, |(c z + L) / f z| := by
        apply Finset.single_le_sum (f := fun z : A => |(c z + L) / f z|)
        · intro z _
          exact abs_nonneg _
        · exact Finset.mem_univ a
      linarith
    have hy_nonneg : ∀ j : A, 0 ≤ y j := by
      intro j
      by_cases h : 0 < α * f j
      · simp only [y, h, if_true]
        exact le_max_left _ _
      · simp only [y, h, if_false]
        exact le_refl 0
    have hy_sorted : l.Pairwise fun a b => y b ≤ y a := by
      apply hl_keysorted.imp
      intro a b hab
      by_cases hb : 0 < α * f b
      · have hfb : 0 < f b := by
          rcases lt_or_ge 0 (f b) with h | h
          · exact h
          · exact absurd hb (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hα0 h))
        have hαpos : 0 < α := by
          rcases lt_or_ge 0 α with h | h
          · exact h
          · have : α = 0 := le_antisymm h hα0
            rw [this] at hb
            simp at hb
        have hfa : 0 < f a := by
          by_contra hfa
          rw [hkey, hkey] at hab
          simp only [hfa, hfb, if_true, if_false] at hab
          exact absurd (lt_of_lt_of_le (hbig K b hfb) hab) (lt_irrefl _)
        rw [hkey, hkey] at hab
        simp only [hfa, hfb, if_true] at hab
        have hstep : (α * f b * (1 - r) - c b - K) / (α * f b) ≤
            (α * f a * (1 - r) - c a - K) / (α * f a) := by
          have hea : (α * f a * (1 - r) - c a - K) / (α * f a) =
              (1 - r) - ((c a + K) / f a) / α := by
            field_simp
            ring
          have heb : (α * f b * (1 - r) - c b - K) / (α * f b) =
              (1 - r) - ((c b + K) / f b) / α := by
            field_simp
            ring
          rw [hea, heb]
          have hdiv : ((c a + K) / f a) / α ≤ ((c b + K) / f b) / α :=
            (div_le_div_iff_of_pos_right hαpos).mpr hab
          linarith
        have hafpos : 0 < α * f a := mul_pos hαpos hfa
        simp only [y, hb, hafpos, if_true]
        exact max_le_max (le_refl 0) hstep
      · simp only [y, hb, if_false]
        exact hy_nonneg a
    have hp_insert_zero : ∀ S ∈ B.powerset, S ≠ ∅ → p.mass (insert i S) = 0 := by
      intro S hS hSne
      have hiS : i ∉ S := by
        intro hiS
        exact hiB (Finset.mem_of_subset (Finset.mem_powerset.mp hS) hiS)
      by_contra hmass
      have hsingle := hpsep (insert i S) hmass (by simp)
      have herase := congrArg (fun T : Finset A => T.erase i) hsingle
      exact hSne (by simpa [hiS] using herase)
    have hp_insert_total :
        B.powerset.sum (fun S => p.mass (insert i S)) = r := by
      calc
        B.powerset.sum (fun S => p.mass (insert i S)) = p.mass (insert i ∅) := by
          apply finite_real_sum_single B.powerset
          · simp
          · intro S hS hSne
            exact hp_insert_zero S hS hSne
        _ = r := by simp [r]
    have htr : t + r = 1 := by
      have htotal := p.total_mass
      rw [← hBi, finite_real_sum_powerset_insert B i hiB p.mass] at htotal
      simpa [t, r, hp_insert_total] using htotal
    have hr_nonneg : 0 ≤ r := p.mass_nonneg {i}
    have ht_nonneg : 0 ≤ t := by
      apply finite_real_sum_nonnegative
      intro S _
      exact p.mass_nonneg S
    have hx_nonneg : ∀ a : A, 0 ≤ x a := by
      intro a
      apply finite_real_sum_nonnegative
      intro S _
      by_cases haS : a ∈ S
      · simp [x, haS, p.mass_nonneg S]
      · simp [x, haS]
    have hx_le : ∀ a : A, x a ≤ t := by
      intro a
      apply finite_real_sum_monotone
      intro S _
      by_cases haS : a ∈ S
      · simp [x, t, haS]
      · simp [x, t, haS, p.mass_nonneg S]
    have hdetect_p : ∀ j : A, detection_probability p i j = x j + r := by
      intro j
      rw [detection_probability, finite_real_sum_filter, ← hBi,
        finite_real_sum_powerset_insert B i hiB]
      have hp_first :
          B.powerset.sum (fun S => if i ∈ S ∨ j ∈ S then p.mass S else 0) =
            x j := by
        apply finite_real_sum_congr
        intro S hS
        have hsub := Finset.mem_powerset.mp hS
        have hiS : i ∉ S := by
          intro hiS
          exact hiB (hsub hiS)
        simp [hiS]
      have hp_second :
          B.powerset.sum (fun S =>
            if i ∈ insert i S ∨ j ∈ insert i S then p.mass (insert i S)
            else 0) = r := by
        simpa using hp_insert_total
      rw [hp_first, hp_second]
    have hgle : ∀ j : A, j ≠ i → α * f j * (1 - r) - c j - K ≤ α * f j * x j := by
      intro j hj
      have h : α * f j * (1 - detection_probability p i j) - c j ≤
          α * f i - c i := by
        simpa [agent_utility, s₁, ← hi, ← hα, ← hcdef, ← hfdef, hj]
          using hs₁.1.2.2 j
      rw [hdetect_p j] at h
      rw [hK]
      nlinarith [h]
    have hy_le_x : ∀ j : A, j ≠ i → y j ≤ x j := by
      intro j hj
      by_cases hpos : 0 < α * f j
      · simp only [y, hpos, if_true]
        apply max_le (hx_nonneg j)
        rw [div_le_iff₀ hpos]
        have := hgle j hj
        nlinarith [this]
      · simp only [y, hpos, if_false]
        exact hx_nonneg j
    have hy_bound : ∀ a ∈ l, 0 ≤ y a ∧ y a ≤ t := by
      intro a ha
      have haB : a ∈ B := by
        have : a ∈ l.toFinset := by simpa using ha
        rwa [hl_fin] at this
      have hai : a ≠ i := by
        intro h
        exact hiB (h ▸ haB)
      exact ⟨hy_nonneg a, (hy_le_x a hai).trans (hx_le a)⟩
    have hprefix := nested_prefix_mass_specification l y t hl_nodup ht_nonneg
      hy_bound hy_sorted
    rcases hprefix with ⟨hprefix_nonneg, hprefix_total, hprefix_marginal,
      hprefix_support⟩
    rw [hl_fin] at hprefix_total hprefix_marginal
    let qmass : Finset A → ℝ := fun S =>
      if S = {i} then r
      else if S ⊆ B then nested_prefix_mass l y t S else 0
    have hq_on_B : ∀ S ∈ B.powerset,
        qmass S = nested_prefix_mass l y t S := by
      intro S hS
      have hsub := Finset.mem_powerset.mp hS
      have hiS : i ∉ S := by
        intro hiS
        exact hiB (hsub hiS)
      have hne : S ≠ {i} := by
        intro h
        subst S
        exact hiS (by simp)
      simp [qmass, hne, hsub]
    have hq_insert_total :
        B.powerset.sum (fun S => qmass (insert i S)) = r := by
      calc
        B.powerset.sum (fun S => qmass (insert i S)) = qmass (insert i ∅) := by
          apply finite_real_sum_single B.powerset
          · simp
          · intro S hS hSne
            have hsub := Finset.mem_powerset.mp hS
            have hiS : i ∉ S := by
              intro hiS
              exact hiB (hsub hiS)
            have hne : insert i S ≠ {i} := by
              intro h
              have herase := congrArg (fun T : Finset A => T.erase i) h
              exact hSne (by simpa [hiS] using herase)
            have hnsub : ¬ insert i S ⊆ B := by
              intro h
              exact hiB (h (Finset.mem_insert_self i S))
            simp [qmass, hne, hnsub]
        _ = r := by simp [qmass]
    have hq_nonneg : ∀ S : Finset A, 0 ≤ qmass S := by
      intro S
      by_cases hsingle : S = {i}
      · simp [qmass, hsingle, hr_nonneg]
      · by_cases hsub : S ⊆ B
        · simp [qmass, hsingle, hsub, hprefix_nonneg S]
        · simp [qmass, hsingle, hsub]
    have hq_total : Finset.univ.powerset.sum qmass = 1 := by
      rw [← hBi, finite_real_sum_powerset_insert B i hiB qmass]
      have hfirst : B.powerset.sum qmass = t := by
        calc
          B.powerset.sum qmass =
              B.powerset.sum (nested_prefix_mass l y t) := by
                apply finite_real_sum_congr
                intro S hS
                exact hq_on_B S hS
          _ = t := hprefix_total
      rw [hfirst, hq_insert_total, htr]
    let q : inspection_distribution A :=
      { mass := qmass
        mass_nonneg := hq_nonneg
        total_mass := hq_total }
    have hq_marginal : ∀ j : A, j ≠ i →
        B.powerset.sum (fun S => if j ∈ S then qmass S else 0) = y j := by
      intro j hj
      have hjB : j ∈ B := by simp [B, hj]
      have hjl : j ∈ l := by
        have : j ∈ l.toFinset := by rw [hl_fin]; exact hjB
        simpa using this
      calc
        B.powerset.sum (fun S => if j ∈ S then qmass S else 0) =
            B.powerset.sum (fun S =>
              if j ∈ S then nested_prefix_mass l y t S else 0) := by
              apply finite_real_sum_congr
              intro S hS
              rw [hq_on_B S hS]
        _ = if j ∈ l then y j else 0 := hprefix_marginal j
        _ = y j := by simp [hjl]
    have hdetect_q : ∀ j : A, j ≠ i →
        detection_probability q i j = y j + r := by
      intro j hj
      rw [detection_probability, finite_real_sum_filter, ← hBi,
        finite_real_sum_powerset_insert B i hiB]
      have hq_first :
          B.powerset.sum (fun S => if i ∈ S ∨ j ∈ S then q.mass S else 0) =
            y j := by
        calc
          B.powerset.sum (fun S => if i ∈ S ∨ j ∈ S then q.mass S else 0) =
              B.powerset.sum (fun S => if j ∈ S then qmass S else 0) := by
                apply finite_real_sum_congr
                intro S hS
                have hsub := Finset.mem_powerset.mp hS
                have hiS : i ∉ S := by
                  intro hiS
                  exact hiB (hsub hiS)
                simp [q, hiS]
          _ = y j := hq_marginal j hj
      have hq_second :
          B.powerset.sum (fun S =>
            if i ∈ insert i S ∨ j ∈ insert i S then q.mass (insert i S)
            else 0) = r := by
        simpa [q] using hq_insert_total
      rw [hq_first, hq_second]
    have hdisj_empty : Disjoint (∅ : Finset A) l.toFinset := by simp
    have hq_chain_cost :
        B.powerset.sum (fun S => qmass S * v S) =
          B.powerset.sum (fun S =>
            qmass S * submodular_chain_increment v ∅ l S) := by
      apply finite_real_sum_congr
      intro S hS
      rw [hq_on_B S hS]
      by_cases hmass : nested_prefix_mass l y t S = 0
      · simp [hmass]
      · rcases hprefix_support S hmass with ⟨k, hk, rfl⟩
        have hexact := submodular_chain_increment_prefix_exact v ∅ l hl_nodup
          hdisj_empty k hk
        have hvalue :
            submodular_chain_increment v ∅ l (l.take k).toFinset =
              v (l.take k).toFinset := by
          simpa [hv_empty] using hexact
        rw [hvalue]
    have hp_chain_le :
        B.powerset.sum (fun S =>
          p.mass S * submodular_chain_increment v ∅ l S) ≤
            B.powerset.sum (fun S => p.mass S * v S) := by
      apply finite_real_sum_monotone
      intro S hS
      have hsubB := Finset.mem_powerset.mp hS
      have hsubL : S ⊆ l.toFinset := by simpa [hl_fin] using hsubB
      have hlower := submodular_chain_increment_lower_bound v hsubmod ∅ l S
        hl_nodup hdisj_empty hsubL
      have hinc : submodular_chain_increment v ∅ l S ≤ v S := by
        simpa [hv_empty] using hlower
      exact mul_le_mul_of_nonneg_left hinc (p.mass_nonneg S)
    have hchain_le :
        B.powerset.sum (fun S =>
          qmass S * submodular_chain_increment v ∅ l S) ≤
        B.powerset.sum (fun S =>
          p.mass S * submodular_chain_increment v ∅ l S) := by
      apply chainmono v hv_mono B.powerset qmass p.mass ∅ l
      intro a ha
      have haB : a ∈ B := by
        have : a ∈ l.toFinset := by simpa using ha
        rwa [hl_fin] at this
      have hai : a ≠ i := by
        intro h
        exact hiB (h ▸ haB)
      rw [hq_marginal a hai]
      exact hy_le_x a hai
    have haway_cost :
        B.powerset.sum (fun S => qmass S * v S) ≤
          B.powerset.sum (fun S => p.mass S * v S) := by
      rw [hq_chain_cost]
      exact hchain_le.trans hp_chain_le
    have hq_insert_cost :
        B.powerset.sum (fun S => q.mass (insert i S) * v (insert i S)) =
          r * v {i} := by
      calc
        B.powerset.sum (fun S => q.mass (insert i S) * v (insert i S)) =
            B.powerset.sum (fun S => qmass (insert i S) * v {i}) := by
              apply finite_real_sum_congr
              intro S hS
              by_cases hSe : S = ∅
              · subst S
                simp [q]
              · have hzero : qmass (insert i S) = 0 := by
                  have hsub := Finset.mem_powerset.mp hS
                  have hiS : i ∉ S := by
                    intro hiS
                    exact hiB (hsub hiS)
                  have hne : insert i S ≠ {i} := by
                    intro h
                    have herase := congrArg (fun T : Finset A => T.erase i) h
                    exact hSe (by simpa [hiS] using herase)
                  have hnsub : ¬ insert i S ⊆ B := by
                    intro h
                    exact hiB (h (Finset.mem_insert_self i S))
                  simp [qmass, hne, hnsub]
                simp [q, hzero]
        _ = r * v {i} := by
          rw [finite_real_sum_mul_right]
          simpa [q] using congrArg (fun w : ℝ => w * v {i}) hq_insert_total
    have hp_insert_cost :
        B.powerset.sum (fun S => p.mass (insert i S) * v (insert i S)) =
          r * v {i} := by
      calc
        B.powerset.sum (fun S => p.mass (insert i S) * v (insert i S)) =
            B.powerset.sum (fun S => p.mass (insert i S) * v {i}) := by
              apply finite_real_sum_congr
              intro S hS
              by_cases hSe : S = ∅
              · subst S
                simp
              · rw [hp_insert_zero S hS hSe]
                simp
        _ = r * v {i} := by
          rw [finite_real_sum_mul_right, hp_insert_total]
    have hcost : expected_inspection_cost v q ≤ expected_inspection_cost v p := by
      rw [expected_inspection_cost, expected_inspection_cost, ← hBi,
        finite_real_sum_powerset_insert B i hiB,
        finite_real_sum_powerset_insert B i hiB]
      change B.powerset.sum (fun S => qmass S * v S) +
          B.powerset.sum (fun S => q.mass (insert i S) * v (insert i S)) ≤ _
      rw [hq_insert_cost, hp_insert_cost]
      exact add_le_add haway_cost le_rfl
    let s₂ : inspection_scheme A := { s₁ with inspection := q }
    have hs₂feas : feasible_inspection_scheme d s₂ := by
      refine ⟨by simpa [s₂] using hs₁.1.1, by simpa [s₂] using hs₁.1.2.1, ?_⟩
      intro j
      by_cases hj : j = i
      · subst j
        simp [agent_utility, s₂, s₁, ← hi]
      · have hgoal : α * f j * (1 - (y j + r)) - c j ≤ K := by
          have hkey2 : α * f j * (1 - r) - c j - K ≤ α * f j * y j := by
            by_cases hpos : 0 < α * f j
            · have hge : (α * f j * (1 - r) - c j - K) / (α * f j) ≤ y j := by
                simp only [y, hpos, if_true]
                exact le_max_right _ _
              rw [div_le_iff₀ hpos] at hge
              nlinarith [hge]
            · have hy0 : y j = 0 := by simp only [y, hpos, if_false]
              have hle : α * f j * x j ≤ 0 :=
                mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hpos) (hx_nonneg j)
              have := hgle j hj
              rw [hy0]
              nlinarith [this, hle]
          nlinarith [hkey2]
        have hval : agent_utility d s₂ j =
            α * f j * (1 - (y j + r)) - c j := by
          simp [agent_utility, s₂, s₁, ← hi, ← hα, ← hcdef, ← hfdef, hj,
            hdetect_q j hj, q]
        have hval2 : agent_utility d s₂ s₂.suggested = K := by
          simp [agent_utility, s₂, s₁, ← hi, ← hα, ← hcdef, ← hfdef, hK]
        rw [hval, hval2]
        exact hgoal
    have hprincipal₂ :
        principal_utility d s₁ s₁.suggested ≤
          principal_utility d s₂ s₂.suggested := by
      simpa [principal_utility, s₁, s₂] using
        (sub_le_sub_left hcost ((1 - α) * f i))
    have hs₂ : optimal_inspection_scheme d s₂ :=
      ⟨hs₂feas, fun u hu => (hs₁.2 u hu).trans hprincipal₂⟩
    obtain ⟨K', hK'mem, hK'eq⟩ := hLamrep K
    have hlK' : l = B.toList.mergeSort
        (fun a b => decide (key K' a ≤ key K' b)) := by
      exact congrArg (fun cmp => B.toList.mergeSort cmp) hK'eq
    have hBcard : B.card + 1 = Fintype.card A := by
      have hpos : 1 ≤ Fintype.card A := Fintype.card_pos_iff.mpr ⟨i⟩
      have hcB : B.card = Fintype.card A - 1 := by
        simp [B, Finset.card_erase_of_mem]
      omega
    have hllen : l.length = B.card := by
      have : l.length = B.toList.length := by
        simpa [l] using List.length_mergeSort
          (le := fun a b : A => decide (key K a ≤ key K b)) B.toList
      rw [this, Finset.length_toList]
    have hsupport : inspection_support q ⊆ QQ := by
      intro S hS
      have hSmass : q.mass S ≠ 0 := by
        simpa [inspection_support] using hS
      by_cases hsingle : S = {i}
      · rw [hsingle]
        exact hQ1 i
      · have hSsub : S ⊆ B := by
          by_contra hsub
          exact hSmass (by simp [q, qmass, hsingle, hsub])
        have hSprefix : nested_prefix_mass l y t S ≠ 0 := by
          simpa [q, qmass, hsingle, hSsub] using hSmass
        rcases hprefix_support S hSprefix with ⟨k, hk, rfl⟩
        have hkle : k ≤ Fintype.card A := by
          rw [hllen] at hk
          omega
        have := hQ2 i K' hK'mem k hkle
        have hBB : (Finset.univ.erase i) = B := rfl
        rw [hBB, ← hlK'] at this
        exact this
    have hcard : (inspection_support q).card ≤ Fintype.card A + 1 := by
      have hsupport_subset : inspection_support q ⊆
          insert {i} ((Finset.range (l.length + 1)).image
            fun k => (l.take k).toFinset) := by
        intro S hS
        have hSmass : q.mass S ≠ 0 := by
          simpa [inspection_support] using hS
        by_cases hsingle : S = {i}
        · simp [hsingle]
        · have hSsub : S ⊆ B := by
            by_contra hsub
            exact hSmass (by simp [q, qmass, hsingle, hsub])
          have hSprefix : nested_prefix_mass l y t S ≠ 0 := by
            simpa [q, qmass, hsingle, hSsub] using hSmass
          rcases hprefix_support S hSprefix with ⟨k, hk, rfl⟩
          apply Finset.mem_insert.mpr
          exact Or.inr (Finset.mem_image.mpr ⟨k, by simp; omega, rfl⟩)
      calc
        (inspection_support q).card ≤
            (insert {i} ((Finset.range (l.length + 1)).image
              fun k => (l.take k).toFinset)).card :=
          Finset.card_le_card hsupport_subset
        _ ≤ ((Finset.range (l.length + 1)).image
              fun k => (l.take k).toFinset).card + 1 :=
          Finset.card_insert_le _ _
        _ ≤ (l.length + 1) + 1 := by
          have : ((Finset.range (l.length + 1)).image
              fun k => (l.take k).toFinset).card ≤ l.length + 1 := by
            calc
              ((Finset.range (l.length + 1)).image
                  fun k => (l.take k).toFinset).card ≤
                  (Finset.range (l.length + 1)).card := Finset.card_image_le
              _ = l.length + 1 := by simp
          omega
        _ = Fintype.card A + 1 := by rw [hllen]; omega
    exact ⟨s₂, hs₂, by simpa [s₂] using hsupport, by simpa [s₂] using hcard⟩
  obtain ⟨QQ, hQcard, hQcore⟩ :
      ∃ QQ : ∀ (A : Type) [Fintype A] [DecidableEq A],
          (A → ℝ) → (A → ℝ) → Finset (Finset A),
        (∀ (A : Type) [Fintype A] [DecidableEq A] (c f : A → ℝ),
            (QQ A c f).card ≤ 6 * (Fintype.card A + 1) ^ 6) ∧
        (∀ (A : Type) [Fintype A] [DecidableEq A] (d : contract_data A),
            admissible_contract_data d →
            submodular_inspection_cost d.inspectionCost →
            ∃ s : inspection_scheme A, optimal_inspection_scheme d s ∧
              inspection_support s.inspection ⊆ QQ A d.cost d.success ∧
              (inspection_support s.inspection).card ≤ Fintype.card A + 1) := by
    classical
    obtain ⟨key, hkey⟩ :
        ∃ key : ∀ (A : Type) [Fintype A] [DecidableEq A],
            (A → ℝ) → (A → ℝ) → ℝ → A → ℝ,
          ∀ (A : Type) [Fintype A] [DecidableEq A] (c f : A → ℝ) (K : ℝ) (j : A),
            key A c f K j =
              if 0 < f j then (c j + K) / f j
              else 1 + ∑ a : A, |(c a + K) / f a| :=
      ⟨fun A _ _ c f K j =>
        if 0 < f j then (c j + K) / f j else 1 + ∑ a : A, |(c a + K) / f a|,
        fun A _ _ c f K j => rfl⟩
    obtain ⟨R, hRmem, hRcard⟩ :
        ∃ R : ∀ (A : Type) [Fintype A] [DecidableEq A],
            (A → ℝ) → (A → ℝ) → Finset ℝ,
          (∀ (A : Type) [Fintype A] [DecidableEq A] (c f : A → ℝ) (a b : A),
              (c b * f a - c a * f b) / (f b - f a) ∈ R A c f) ∧
          (∀ (A : Type) [Fintype A] [DecidableEq A] (c f : A → ℝ),
              (R A c f).card ≤ (Fintype.card A + 1) ^ 2) := by
      refine ⟨fun A _ _ c f =>
        (Finset.univ ×ˢ Finset.univ : Finset (A × A)).image fun z =>
          (c z.2 * f z.1 - c z.1 * f z.2) / (f z.2 - f z.1), ?_, ?_⟩
      · intro A _ _ c f a b
        exact Finset.mem_image.mpr ⟨(a, b), by simp, rfl⟩
      · intro A _ _ c f
        refine le_trans (Finset.card_image_le) ?_
        have hcp : (Finset.univ ×ˢ Finset.univ : Finset (A × A)).card =
            Fintype.card A * Fintype.card A := by
          simp [Finset.card_product]
        rw [hcp, pow_two]
        exact Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)
    obtain ⟨Lam, hLamcard, hLamrep⟩ :
        ∃ Lam : ∀ (A : Type) [Fintype A] [DecidableEq A],
            (A → ℝ) → (A → ℝ) → Finset ℝ,
          (∀ (A : Type) [Fintype A] [DecidableEq A] (c f : A → ℝ),
              (Lam A c f).card ≤ 5 * (Fintype.card A + 1) ^ 4) ∧
          (∀ (A : Type) [Fintype A] [DecidableEq A] (c f : A → ℝ) (K : ℝ),
              ∃ K' ∈ Lam A c f,
                (fun a b : A => decide (key A c f K a ≤ key A c f K b)) =
                  (fun a b : A => decide (key A c f K' a ≤ key A c f K' b))) := by
      refine ⟨fun A _ _ c f => R A c f ∪ insert 0
        (((R A c f).image fun ρ => ρ - 1) ∪ ((R A c f).image fun ρ => ρ + 1) ∪
          (((R A c f) ×ˢ (R A c f)).image fun z => (z.1 + z.2) / 2)), ?_, ?_⟩
      · intro A _ _ c f
        have hr := hRcard A c f
        have hxy : ∀ g : ℝ → ℝ,
            ((R A c f).image g).card ≤ (Fintype.card A + 1) ^ 2 :=
          fun g => le_trans (Finset.card_image_le) hr
        have hz : (((R A c f) ×ˢ (R A c f)).image
            fun z : ℝ × ℝ => (z.1 + z.2) / 2).card ≤
              (Fintype.card A + 1) ^ 4 := by
          refine le_trans (Finset.card_image_le) ?_
          rw [Finset.card_product]
          calc (R A c f).card * (R A c f).card
              ≤ (Fintype.card A + 1) ^ 2 * (Fintype.card A + 1) ^ 2 :=
                Nat.mul_le_mul hr hr
            _ = (Fintype.card A + 1) ^ 4 := by ring
        have hcU : ((((R A c f).image fun ρ => ρ - 1) ∪
            ((R A c f).image fun ρ => ρ + 1)) ∪
            (((R A c f) ×ˢ (R A c f)).image fun z => (z.1 + z.2) / 2)).card ≤
              2 * (Fintype.card A + 1) ^ 2 + (Fintype.card A + 1) ^ 4 := by
          refine le_trans (Finset.card_union_le _ _) ?_
          refine Nat.add_le_add ?_ hz
          refine le_trans (Finset.card_union_le _ _) ?_
          have h1 := hxy (fun ρ => ρ - 1)
          have h2 := hxy (fun ρ => ρ + 1)
          linarith
        refine le_trans (Finset.card_union_le _ _) ?_
        refine le_trans (Nat.add_le_add hr (le_trans (Finset.card_insert_le _ _)
          (Nat.add_le_add_right hcU 1))) ?_
        have hm : 1 ≤ Fintype.card A + 1 := Nat.le_add_left 1 _
        have h24 : (Fintype.card A + 1) ^ 2 ≤ (Fintype.card A + 1) ^ 4 :=
          Nat.pow_le_pow_right hm (by norm_num)
        have h04 : 1 ≤ (Fintype.card A + 1) ^ 4 :=
          Nat.one_le_pow _ _ (by omega)
        linarith
      · intro A _ _ c f K
        obtain ⟨K', hK'mem, hK'⟩ := rep (R A c f) K
        refine ⟨K', hK'mem,
          cmpeq A c f (key A c f) (fun L j => hkey A c f L j) K K' ?_⟩
        intro a b
        rcases lt_trichotomy (f b) (f a) with hlt | heq | hgt
        · have hD : f b - f a < 0 := by linarith
          have hmem := hRmem A c f a b
          have h1 : (c b * f a - c a * f b) / (f b - f a) ≤ K ↔
              K * (f b - f a) ≤ c b * f a - c a * f b := div_le_iff_of_neg hD
          have h2 : (c b * f a - c a * f b) / (f b - f a) ≤ K' ↔
              K' * (f b - f a) ≤ c b * f a - c a * f b := div_le_iff_of_neg hD
          exact h1.symm.trans ((hK' _ hmem).2.trans h2)
        · rw [heq]
          simp
        · have hD : 0 < f b - f a := by linarith
          have hmem := hRmem A c f a b
          have h1 : K ≤ (c b * f a - c a * f b) / (f b - f a) ↔
              K * (f b - f a) ≤ c b * f a - c a * f b := le_div_iff₀ hD
          have h2 : K' ≤ (c b * f a - c a * f b) / (f b - f a) ↔
              K' * (f b - f a) ≤ c b * f a - c a * f b := le_div_iff₀ hD
          exact h1.symm.trans ((hK' _ hmem).1.trans h2)
    obtain ⟨QQ, hQcard, hQ1, hQ2⟩ :
        ∃ QQ : ∀ (A : Type) [Fintype A] [DecidableEq A],
            (A → ℝ) → (A → ℝ) → Finset (Finset A),
          (∀ (A : Type) [Fintype A] [DecidableEq A] (c f : A → ℝ),
              (QQ A c f).card ≤ 6 * (Fintype.card A + 1) ^ 6) ∧
          (∀ (A : Type) [Fintype A] [DecidableEq A] (c f : A → ℝ) (i : A),
              ({i} : Finset A) ∈ QQ A c f) ∧
          (∀ (A : Type) [Fintype A] [DecidableEq A] (c f : A → ℝ) (i : A)
              (K' : ℝ), K' ∈ Lam A c f → ∀ k : ℕ, k ≤ Fintype.card A →
              ((((Finset.univ.erase i).toList.mergeSort
                (fun a b => decide (key A c f K' a ≤ key A c f K' b))).take
                  k).toFinset) ∈ QQ A c f) := by
      refine ⟨fun A _ _ c f => Finset.univ.biUnion fun i =>
        insert ({i} : Finset A) ((Lam A c f).biUnion fun K' =>
          (Finset.range (Fintype.card A + 1)).image fun k =>
            (((Finset.univ.erase i).toList.mergeSort
              (fun a b => decide (key A c f K' a ≤ key A c f K' b))).take
                k).toFinset), ?_, ?_, ?_⟩
      · intro A _ _ c f
        have hbound : ∀ i : A,
            (insert ({i} : Finset A) ((Lam A c f).biUnion fun K' =>
              (Finset.range (Fintype.card A + 1)).image fun k =>
                (((Finset.univ.erase i).toList.mergeSort
                  (fun a b => decide (key A c f K' a ≤ key A c f K' b))).take
                    k).toFinset)).card ≤
              5 * (Fintype.card A + 1) ^ 4 * (Fintype.card A + 1) + 1 := by
          intro i
          refine le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right ?_ 1)
          refine le_trans (Finset.card_biUnion_le) ?_
          refine le_trans (Finset.sum_le_sum (fun K' _ =>
            le_trans (Finset.card_image_le)
              (le_of_eq (Finset.card_range _)))) ?_
          rw [Finset.sum_const, smul_eq_mul]
          exact Nat.mul_le_mul_right _ (hLamcard A c f)
        refine le_trans (Finset.card_biUnion_le) ?_
        refine le_trans (Finset.sum_le_sum (fun i _ => hbound i)) ?_
        rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
        have h5 : 1 ≤ (Fintype.card A + 1) ^ 5 :=
          Nat.one_le_pow _ _ (by omega)
        calc Fintype.card A *
              (5 * (Fintype.card A + 1) ^ 4 * (Fintype.card A + 1) + 1)
            ≤ (Fintype.card A + 1) * (6 * (Fintype.card A + 1) ^ 5) := by
              refine Nat.mul_le_mul (by omega) ?_
              have hrw : 5 * (Fintype.card A + 1) ^ 4 * (Fintype.card A + 1) =
                  5 * (Fintype.card A + 1) ^ 5 := by ring
              rw [hrw]
              linarith
          _ = 6 * (Fintype.card A + 1) ^ 6 := by ring
      · intro A _ _ c f i
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
          Finset.mem_insert_self _ _⟩
      · intro A _ _ c f i K' hK' k hk
        refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
          Finset.mem_insert_of_mem ?_⟩
        exact Finset.mem_biUnion.mpr ⟨K', hK',
          Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩⟩
    refine ⟨QQ, hQcard, ?_⟩
    intro A _ _ d hadm hsub
    exact core A (chainmono A) d (key A d.cost d.success)
      (hkey A d.cost d.success) (Lam A d.cost d.success)
      (hLamrep A d.cost d.success) (QQ A d.cost d.success)
      (fun i => hQ1 A d.cost d.success i)
      (fun i K' hK' k hk => hQ2 A d.cost d.success i K' hK' k hk) hadm hsub
  obtain ⟨pick, hpick⟩ :
      ∃ pick : ∀ (A : Type) [Fintype A] [DecidableEq A],
          (inspection_scheme A → Prop) → inspection_scheme A →
            inspection_scheme A,
        ∀ (A : Type) [Fintype A] [DecidableEq A]
          (P : inspection_scheme A → Prop) (z : inspection_scheme A),
          (∃ s, P s) → P (pick A P z) := by
    refine ⟨fun A _ _ P z => if h : ∃ s, P s then h.choose else z, ?_⟩
    intro A _ _ P z h
    simp only [dif_pos h]
    exact h.choose_spec
  obtain ⟨dist0, -⟩ :
      ∃ dist0 : ∀ (A : Type) [Fintype A] [DecidableEq A],
        inspection_distribution A, True := by
    refine ⟨fun A _ _ =>
      ⟨fun S => if S = ∅ then 1 else 0, ?_, ?_⟩, trivial⟩
    · intro S
      by_cases h : S = ∅ <;> simp [h]
    · rw [Finset.sum_eq_single_of_mem ∅ (by simp)]
      · simp
      · intro S _ hne
        simp [hne]
  obtain ⟨good, hgood⟩ :
      ∃ good : ∀ (A : Type) [Fintype A] [DecidableEq A],
          contract_data A → inspection_scheme A → Prop,
        ∀ (A : Type) [Fintype A] [DecidableEq A] (d : contract_data A)
          (s : inspection_scheme A),
          good A d s ↔
            (inspection_support s.inspection ⊆ QQ A d.cost d.success ∧
              (inspection_support s.inspection).card ≤ Fintype.card A + 1 ∧
              feasible_inspection_scheme d s ∧
              ∀ t : inspection_scheme A,
                inspection_support t.inspection ⊆ QQ A d.cost d.success →
                (inspection_support t.inspection).card ≤ Fintype.card A + 1 →
                feasible_inspection_scheme d t →
                principal_utility d t t.suggested ≤
                  principal_utility d s s.suggested) := by
    refine ⟨fun A _ _ d s =>
      (inspection_support s.inspection ⊆ QQ A d.cost d.success ∧
        (inspection_support s.inspection).card ≤ Fintype.card A + 1 ∧
        feasible_inspection_scheme d s ∧
        ∀ t : inspection_scheme A,
          inspection_support t.inspection ⊆ QQ A d.cost d.success →
          (inspection_support t.inspection).card ≤ Fintype.card A + 1 →
          feasible_inspection_scheme d t →
          principal_utility d t t.suggested ≤
            principal_utility d s s.suggested), ?_⟩
    intro A _ _ d s
    exact Iff.rfl
  refine ⟨{
    solve := fun A _ _ d _ =>
      pick A (good A d)
        { suggested := d.nullAction, payment := 0, inspection := dist0 A }
    queries := fun A _ _ d _ => (QQ A d.cost d.success).toList
    work := fun _ _ _ _ _ => 0
    transcript_stable := ?_
    polynomial_resources := ?_
    correctness := ?_ }⟩
  · intro A _ _ d enc v' _ hagree
    refine ⟨rfl, rfl, ?_⟩
    have hvv : ∀ S : Finset A, S ∈ QQ A d.cost d.success →
        v' S = d.inspectionCost S := by
      intro S hS
      exact hagree S (Finset.mem_toList.mpr hS)
    have hpu : ∀ t : inspection_scheme A,
        inspection_support t.inspection ⊆ QQ A d.cost d.success →
        principal_utility (replace_inspection_cost d v') t t.suggested =
          principal_utility d t t.suggested := by
      intro t hts
      have hexp : expected_inspection_cost v' t.inspection =
          expected_inspection_cost d.inspectionCost t.inspection := by
        apply Finset.sum_congr rfl
        intro S hS
        by_cases hm : t.inspection.mass S = 0
        · simp [hm]
        · have hmem : S ∈ inspection_support t.inspection := by
            simp only [inspection_support, Finset.mem_filter]
            exact ⟨hS, hm⟩
          rw [hvv S (hts hmem)]
      simp [principal_utility, replace_inspection_cost, hexp]
    have hgeq : good A (replace_inspection_cost d v') = good A d := by
      funext s
      apply propext
      rw [hgood, hgood]
      constructor
      · intro h
        refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
        intro t h1 h2 h3
        have := h.2.2.2 t h1 h2 h3
        rw [hpu t h1, hpu s h.1] at this
        exact this
      · intro h
        refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
        intro t h1 h2 h3
        have := h.2.2.2 t h1 h2 h3
        rw [← hpu t h1, ← hpu s h.1] at this
        exact this
    rw [hgeq]
    rfl
  · refine ⟨6, 6, ?_⟩
    intro A _ _ d enc _
    refine ⟨Nat.zero_le _, ?_⟩
    rw [Finset.length_toList]
    exact hQcard A d.cost d.success
  · intro A _ _ d enc _ hadm hsubmod
    obtain ⟨s0, hs0opt, hs0sub, hs0card⟩ := hQcore A d hadm hsubmod
    have hgs0 : good A d s0 :=
      (hgood A d s0).mpr ⟨hs0sub, hs0card, hs0opt.1,
        fun t _ _ ht => hs0opt.2 t ht⟩
    have hg := hpick A (good A d)
      { suggested := d.nullAction, payment := 0, inspection := dist0 A }
      ⟨s0, hgs0⟩
    obtain ⟨h1, h2, h3, h4⟩ := (hgood A d _).mp hg
    refine ⟨⟨h3, ?_⟩, h2⟩
    intro t ht
    exact le_trans (hs0opt.2 t ht) (h4 s0 hs0sub hs0card hs0opt.1)

@[blueprint "thm:submod"
  (statement := /-- Let $A$ be a finite action space and let $d=(A,c,f,v,\bot)$ be admissible contract data with normalized, monotone, nonnegative, submodular inspection cost $v$.  There exists a uniform abstract solver in the sense of \cref{def:abstract-submodular-value-oracle-solver}; in particular, it accesses $v$ only through an oracle-stable transcript of value queries, uses polynomially bounded work and queries, and returns an optimal scheme supported on at most $|A|+1$ sets on every admissible submodular instance.  Moreover, there exists an optimal, possibly randomized, incentive-compatible inspection scheme for $d$ whose distribution is supported on at most $|A|+1$ sets. -/)
  (proof := /-- Apply \cref{lem:polynomial-time-submodular-oracle-solver}.  Its first conclusion supplies a uniform abstract value-oracle solver with oracle-stable queries, polynomial resource bounds, global optimality, and the asserted support bound.  Specializing its second conclusion to the finite action space $A$, the admissible datum $d$, and the assumed submodularity of $v$ gives an optimal feasible scheme whose inspection distribution is supported on at most $|A|+1$ sets. -/)
  (title := /-- Optimal randomized inspection via a polynomial-time value oracle -/)
  (latexEnv := "theorem")]
theorem submod
    {A : Type} [Fintype A] [DecidableEq A]
    (d : contract_data A) (hadm : admissible_contract_data d)
    (hsubmod : submodular_inspection_cost d.inspectionCost) :
    Nonempty abstract_submodular_value_oracle_solver ∧
      ∃ s : inspection_scheme A,
        optimal_inspection_scheme d s ∧
        (inspection_support s.inspection).card ≤ Fintype.card A + 1 := by
  obtain ⟨hsolver, hopt⟩ := polynomial_time_submodular_oracle_solver
  exact ⟨hsolver, hopt A d hadm hsubmod⟩

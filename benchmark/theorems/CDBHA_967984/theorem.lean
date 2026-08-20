import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic

open Classical

def submodular_inspection_cost {A : Type} [DecidableEq A]
    (v : Finset A → ℝ) : Prop :=
  ∀ S T : Finset A, S ⊆ T →
    ∀ a : A, v (insert a S) - v S ≥ v (insert a T) - v T

structure contract_data (A : Type) [Fintype A] [DecidableEq A] where
  cost : A → ℝ
  success : A → ℝ
  inspectionCost : Finset A → ℝ
  nullAction : A

def admissible_contract_data {A : Type} [Fintype A] [DecidableEq A]
    (d : contract_data A) : Prop :=
  (∀ a : A, 0 ≤ d.cost a) ∧
  (∀ a : A, 0 ≤ d.success a ∧ d.success a ≤ 1) ∧
  (∀ S : Finset A, 0 ≤ d.inspectionCost S) ∧
  d.inspectionCost ∅ = 0 ∧
  Monotone d.inspectionCost ∧
  d.cost d.nullAction = 0

structure inspection_distribution (A : Type) [Fintype A] [DecidableEq A] where
  mass : Finset A → ℝ
  mass_nonneg : ∀ S : Finset A, 0 ≤ mass S
  total_mass : Finset.univ.powerset.sum mass = 1

noncomputable def inspection_support {A : Type} [Fintype A] [DecidableEq A]
    (p : inspection_distribution A) : Finset (Finset A) := by
  classical
  exact Finset.univ.powerset.filter fun S => p.mass S ≠ 0

def detection_probability {A : Type} [Fintype A] [DecidableEq A]
    (p : inspection_distribution A) (i j : A) : ℝ :=
  (Finset.univ.powerset.filter fun S => i ∈ S ∨ j ∈ S).sum p.mass

def expected_inspection_cost {A : Type} [Fintype A] [DecidableEq A]
    (v : Finset A → ℝ) (p : inspection_distribution A) : ℝ :=
  Finset.univ.powerset.sum fun S => p.mass S * v S

structure inspection_scheme (A : Type) [Fintype A] [DecidableEq A] where
  suggested : A
  payment : ℝ
  inspection : inspection_distribution A

def agent_utility {A : Type} [Fintype A] [DecidableEq A]
    (d : contract_data A) (s : inspection_scheme A) (j : A) : ℝ :=
  if j = s.suggested then
    s.payment * d.success j - d.cost j
  else
    s.payment * d.success j *
      (1 - detection_probability s.inspection s.suggested j) - d.cost j

def principal_utility {A : Type} [Fintype A] [DecidableEq A]
    (d : contract_data A) (s : inspection_scheme A) (j : A) : ℝ :=
  (1 - s.payment) * d.success j -
    expected_inspection_cost d.inspectionCost s.inspection

def incentive_compatible {A : Type} [Fintype A] [DecidableEq A]
    (d : contract_data A) (s : inspection_scheme A) : Prop :=
  ∀ j : A, agent_utility d s j ≤ agent_utility d s s.suggested

def feasible_inspection_scheme {A : Type} [Fintype A] [DecidableEq A]
    (d : contract_data A) (s : inspection_scheme A) : Prop :=
  0 ≤ s.payment ∧ s.payment ≤ 1 ∧ incentive_compatible d s

def optimal_inspection_scheme {A : Type} [Fintype A] [DecidableEq A]
    (d : contract_data A) (s : inspection_scheme A) : Prop :=
  feasible_inspection_scheme d s ∧
  ∀ t : inspection_scheme A, feasible_inspection_scheme d t →
    principal_utility d t t.suggested ≤ principal_utility d s s.suggested

def replace_inspection_cost {A : Type} [Fintype A] [DecidableEq A]
    (d : contract_data A) (v' : Finset A → ℝ) : contract_data A :=
  { d with inspectionCost := v' }

def action_encoding {A : Type} (encoding : List A) : Prop :=
  encoding.Nodup ∧ ∀ a : A, a ∈ encoding

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

theorem submod
    {A : Type} [Fintype A] [DecidableEq A]
    (d : contract_data A) (hadm : admissible_contract_data d)
    (hsubmod : submodular_inspection_cost d.inspectionCost) :
    (∃ s : inspection_scheme A,
      optimal_inspection_scheme d s ∧
      (inspection_support s.inspection).card ≤ Fintype.card A + 1) ∧
    Nonempty abstract_submodular_value_oracle_solver := by sorry

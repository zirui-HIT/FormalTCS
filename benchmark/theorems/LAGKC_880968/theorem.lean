import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Topology.MetricSpace.Defs

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators

noncomputable def single_center_cost {V : Type*} [MetricSpace V]
    (q : ℕ) (points : Finset V) (center : V) : ℝ :=
  ∑ point ∈ points, dist point center ^ q

noncomputable def trimmed_single_center_cost {V : Type*} [MetricSpace V]
    [DecidableEq V] (q : ℕ) (alpha : ℝ) (points : Finset V) (center : V) : ℝ :=
  sInf {value : ℝ | ∃ core : Finset V,
    core ⊆ points ∧
      (1 - alpha) * (points.card : ℝ) ≤ (core.card : ℝ) ∧
      value = single_center_cost q core center}

noncomputable def distance_to_centers {V : Type*} [MetricSpace V]
    (q : ℕ) (centers : Finset V) (point : V) : ℝ :=
  sInf ((fun center : V => dist point center ^ q) '' (centers : Set V))

noncomputable def clustering_cost {V : Type*} [MetricSpace V]
    (q : ℕ) (points centers : Finset V) : ℝ :=
  ∑ point ∈ points, distance_to_centers q centers point

noncomputable def optimal_clustering_cost {V : Type*} [MetricSpace V]
    (q k : ℕ) (points : Finset V) : ℝ :=
  sInf {value : ℝ | ∃ centers : Finset V,
    centers.card = k ∧ value = clustering_cost q points centers}

noncomputable def predictor_label_error {V : Type*} [MetricSpace V] [Fintype V]
    [DecidableEq V] (points : Finset V) (k q : ℕ) (alpha lambda : ℝ)
    (predictor referenceLabel : V → Fin k) (referenceCenter : Fin k → V) : Prop :=
  0 ≤ lambda ∧ lambda ≤ alpha ∧ Function.Injective referenceCenter ∧
    (∀ point ∈ points,
      ∀ label : Fin k,
        dist point (referenceCenter (referenceLabel point)) ≤
          dist point (referenceCenter label)) ∧
    (∑ label : Fin k,
      single_center_cost q (points.filter fun point => referenceLabel point = label)
        (referenceCenter label)) ≤
      (1 + alpha) * optimal_clustering_cost q k points ∧
    ∀ label : Fin k,
      ((points.filter fun point =>
          referenceLabel point = label ∧ predictor point ≠ label).card : ℝ) ≤
        lambda * ((points.filter fun point => referenceLabel point = label).card : ℝ) ∧
      ((points.filter fun point =>
          predictor point = label ∧ referenceLabel point ≠ label).card : ℝ) ≤
        lambda * ((points.filter fun point => predictor point = label).card : ℝ)

structure costed_computation (A : Type*) where
  output : A
  steps : ℕ

def costed_then {A B : Type*} (first : costed_computation A)
    (next : A → costed_computation B) : costed_computation B :=
  let second := next first.output
  ⟨second.output, first.steps + second.steps + 1⟩

def costed_list_fold {A B : Type*} (items : List B) (initial : A)
    (step : A → B → costed_computation A) : costed_computation A :=
  items.foldl (fun computation item =>
    let successor := step computation.output item
    ⟨successor.output, computation.steps + successor.steps + 1⟩) ⟨initial, 0⟩

noncomputable def get_center {V : Type*} [MetricSpace V] [Fintype V]
    [DecidableEq V] (points : Finset V) (q : ℕ) (alpha : ℝ) :
    costed_computation (Option V) :=
  costed_list_fold (Finset.univ.toList : List V) (none : Option V)
    (fun current candidate =>
      let score := fun center : V =>
        if q = 2 then trimmed_single_center_cost q alpha points center
        else single_center_cost q points center
      let next := match current with
        | none => some candidate
        | some incumbent =>
            if score candidate < score incumbent then some candidate else some incumbent
      ⟨next, 2 * points.card ^ 2 + 2 * points.card + 1⟩)

structure learning_augmented_k_clustering_algorithm where
  run : {V : Type} → [MetricSpace V] → [Fintype V] → [DecidableEq V] →
    Finset V → (k q : ℕ) → ℝ → (V → Fin k) → costed_computation (Finset V)

noncomputable def algorithm_one : learning_augmented_k_clustering_algorithm where
  run := fun {V} _ _ _ points k q alpha predictor =>
    let selected := costed_list_fold (Finset.univ.toList : List (Fin k)) ∅
      (fun centers label =>
        let predictedClass := points.filter fun point => predictor point = label
        let best := get_center predictedClass q alpha
        ⟨match best.output with
          | none => centers
          | some center => insert center centers,
          best.steps⟩)
    costed_then selected fun centers =>
      costed_list_fold (Finset.univ.toList : List V) centers
        (fun padded point =>
          ⟨if padded.card < k then insert point padded else padded, 1⟩)

def algorithm_runs_in_polynomial_time
    (algorithm : learning_augmented_k_clustering_algorithm) : Prop :=
  ∃ coefficient degree : ℕ, 0 < coefficient ∧
    ∀ {V : Type} [MetricSpace V] [Fintype V] [DecidableEq V]
      (points : Finset V) (k q : ℕ) (alpha : ℝ) (predictor : V → Fin k),
      (algorithm.run points k q alpha predictor).steps ≤
        coefficient * (Fintype.card V + k + 1) ^ degree

theorem learning_augmented_k_clustering_approximation :
    algorithm_runs_in_polynomial_time algorithm_one ∧
      ∃ approximationError : ℕ → ℝ → ℝ,
        (∀ q : ℕ, q = 1 ∨ q = 2 →
          Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioo 0 ((1 : ℝ) / 2)))
            (approximationError q)
            (fun alpha : ℝ => Real.rpow alpha ((q : ℝ)⁻¹))) ∧
        ∀ {V : Type} [MetricSpace V] [Fintype V] [DecidableEq V]
          (points : Finset V) (k q : ℕ),
          0 < k → k ≤ Fintype.card V → q = 1 ∨ q = 2 →
          ∀ (alpha lambda : ℝ) (predictor referenceLabel : V → Fin k)
            (referenceCenter : Fin k → V),
            0 < alpha → alpha < (1 : ℝ) / 2 →
            predictor_label_error points k q alpha lambda predictor referenceLabel
              referenceCenter →
            (algorithm_one.run points k q alpha predictor).output.card = k ∧
            clustering_cost q points
                (algorithm_one.run points k q alpha predictor).output ≤
              (1 + approximationError q alpha) *
                optimal_clustering_cost q k points := by sorry

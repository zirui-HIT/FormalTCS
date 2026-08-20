import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Compactness.Compact

open MeasureTheory

variable {IStep Step : Type*}
  [MeasurableSpace IStep]
  [Inhabited Step] [TopologicalSpace Step] [MeasurableSpace Step]
  [BorelSpace Step] [SecondCountableTopology Step] [CompactSpace Step]
  [TopologicalSpace.MetrizableSpace Step]

def input_prefix_eq (T t : ℕ) (x x' : Fin T → IStep) : Prop :=
  ∀ i : Fin T, (i : ℕ) < t → x i = x' i

def action_prefix (T t : ℕ) (y : Fin T → Step) : Fin T → Step :=
  fun i => if (i : ℕ) < t then y i else default

def is_online_algorithm (T : ℕ) (feasible : (Fin T → IStep) → Set (Fin T → Step))
    (ν : (Fin T → IStep) → ProbabilityMeasure (Fin T → Step)) : Prop :=
  (∀ x, (ν x : Measure (Fin T → Step)) (feasible x) = 1) ∧
    (∀ (t : ℕ) (x x' : Fin T → IStep), input_prefix_eq T t x x' →
      Measure.map (action_prefix T t) (ν x : Measure (Fin T → Step)) =
        Measure.map (action_prefix T t) (ν x' : Measure (Fin T → Step)))

noncomputable def expected_cost {α : Type*} [MeasurableSpace α] (μ : ProbabilityMeasure α)
    (c : α → ℝ) : ℝ :=
  ∫ a, c a ∂(μ : Measure α)

def is_finitely_supported {ι : Type*} [MeasurableSpace ι] (D : ProbabilityMeasure ι) : Prop :=
  ∃ s : Finset ι, (D : Measure ι) ((↑s : Set ι)ᶜ) = 0

theorem online_minimax_full [MeasurableSingletonClass IStep] (T : ℕ) (α β : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (feasible : (Fin T → IStep) → Set (Fin T → Step))
    (cost : (Fin T → IStep) → (Fin T → Step) → ℝ) (opt : (Fin T → IStep) → ℝ)
    (hcost : ∀ x, Continuous (cost x)) (hfeasible : ∀ x, IsCompact (feasible x))
    (hbayes : ∀ D : ProbabilityMeasure (Fin T → IStep), is_finitely_supported D →
      ∃ ν, is_online_algorithm T feasible ν ∧
        (∫ x, expected_cost (ν x) (cost x) ∂(D : Measure (Fin T → IStep)))
          ≤ α * (∫ x, opt x ∂(D : Measure (Fin T → IStep))) + β) :
    ∃ ν, is_online_algorithm T feasible ν ∧
      ∀ x, expected_cost (ν x) (cost x) ≤ α * opt x + β := by sorry

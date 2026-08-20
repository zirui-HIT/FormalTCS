import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Finset.Union
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Partition.Finpartition

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators

def indexed_union {κ ι : Type*} [DecidableEq ι]
    (I : κ → Finset ι) (Δ : Finset κ) : Finset ι :=
  Δ.biUnion I

noncomputable def mixed_moment_x_factor {ι : Type*} (x : ℝ) (S : Finset ι) : ℝ :=
  ∏ k ∈ Finset.range (S.card - 1),
    (1 - (((k + 1 : ℕ) : ℝ) * x))⁻¹

def mixed_moment_y_factor {ι : Type*} (y : ℝ) (S : Finset ι) : ℝ :=
  ∏ k ∈ Finset.range (S.card - 1),
    (1 - (((k + 1 : ℕ) : ℝ) * y))

noncomputable def mixed_moment_right_hand_side {ι : Type*} [DecidableEq ι]
    {ℓ q r : ℕ} (I : Fin ℓ → Finset ι) (A : Fin q → Finset ι)
    (B : Fin r → Finset ι) (η x₀ y₀ : ℝ) (Δ : Finset (Fin ℓ)) : ℝ :=
  η ^ (indexed_union I Δ).card *
    (∏ j : Fin q, mixed_moment_x_factor x₀ (indexed_union I Δ ∩ A j)) *
    ∏ i : Fin r, mixed_moment_y_factor y₀ (indexed_union I Δ ∩ B i)

def has_general_mixed_moments {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {ℓ q r : ℕ} (μ : MeasureTheory.Measure Ω) (Z : Fin ℓ → Ω → ℝ)
    (I : Fin ℓ → Finset ι) (A : Fin q → Finset ι) (B : Fin r → Finset ι)
    (η x₀ y₀ : ℝ) : Prop :=
  ∀ Δ : Finset (Fin ℓ),
    MeasureTheory.Integrable (fun ω ↦ ∏ t ∈ Δ, Z t ω) μ ∧
      (∫ ω, ∏ t ∈ Δ, Z t ω ∂μ) =
        mixed_moment_right_hand_side I A B η x₀ y₀ Δ

def total_index_count {ι : Type*} [DecidableEq ι] {ℓ : ℕ}
    (I : Fin ℓ → Finset ι) : ℕ :=
  (indexed_union I Finset.univ).card

noncomputable def joint_cumulant {Ω : Type*} [MeasurableSpace Ω] {ℓ : ℕ}
    (μ : MeasureTheory.Measure Ω) (Z : Fin ℓ → Ω → ℝ) : ℝ :=
  ∑ π : Finpartition (Finset.univ : Finset (Fin ℓ)),
    ((-1 : ℝ) ^ (π.parts.card - 1)) *
      (Nat.factorial (π.parts.card - 1) : ℝ) *
      ∏ C ∈ π.parts, (∫ ω, ∏ t ∈ C, Z t ω ∂μ)

def b_intersection_graph {ι : Type*} [DecidableEq ι] {ℓ r : ℕ}
    (I : Fin ℓ → Finset ι) (B : Fin r → Finset ι) : SimpleGraph (Fin ℓ) :=
  SimpleGraph.fromRel fun t t' ↦
    ∃ i : Fin r, (I t ∩ B i).Nonempty ∧ (I t' ∩ B i).Nonempty

noncomputable def intersection_component_count {ι : Type*} [DecidableEq ι]
    {ℓ r : ℕ} (I : Fin ℓ → Finset ι) (B : Fin r → Finset ι) : ℕ :=
  Nat.card (b_intersection_graph I B).ConnectedComponent

theorem upper_bound_general_cumulant
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {ℓ q r : ℕ} (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (Z : Fin ℓ → Ω → ℝ) (I : Fin ℓ → Finset ι)
    (A : Fin q → Finset ι) (B : Fin r → Finset ι) (η x₀ y₀ : ℝ)
    (hℓ : 0 < ℓ) (hη : 0 ≤ η) (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀)
    (hI_disjoint : (Set.univ : Set (Fin ℓ)).PairwiseDisjoint I)
    (hA_disjoint : (Set.univ : Set (Fin q)).PairwiseDisjoint A)
    (hB_disjoint : (Set.univ : Set (Fin r)).PairwiseDisjoint B)
    (hmom : has_general_mixed_moments μ Z I A B η x₀ y₀) :
    (1 ≤ r →
      0 < y₀ →
      2 * (total_index_count I : ℝ) ^ 2 * y₀ ≤ 1 →
      2 * x₀ ≤ y₀ →
      |joint_cumulant μ Z| ≤
        4 * (ℓ : ℝ) ^ (2 * ℓ) * η ^ total_index_count I *
          ((total_index_count I : ℝ) ^ 2 * y₀) ^ (ℓ - 1) *
          (x₀ / y₀) ^ (intersection_component_count I B - 1)) ∧
    (r = 0 →
      2 * (total_index_count I : ℝ) ^ 2 * x₀ ≤ 1 →
      |joint_cumulant μ Z| ≤
        2 * (ℓ : ℝ) ^ (2 * ℓ) * η ^ total_index_count I *
          ((total_index_count I : ℝ) ^ 2 * x₀) ^ (ℓ - 1)) := by sorry

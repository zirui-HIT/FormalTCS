import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Probability.ProbabilityMassFunction.Basic

universe u v

inductive pool_query_tree (α : Type u) (β : Type v) : Type (max u v)
  | output (value : β) : pool_query_tree α β
  | query (point : α) (next : Bool → pool_query_tree α β) : pool_query_tree α β

def pool_query_tree_run {α : Type u} {β : Type v} :
    pool_query_tree α β → (α → Bool) → β
  | .output value, _ => value
  | .query point next, oracle => pool_query_tree_run (next (oracle point)) oracle

def pool_query_tree_cost {α : Type u} {β : Type v} :
    pool_query_tree α β → (α → Bool) → ℕ
  | .output _, _ => 0
  | .query point next, oracle =>
      1 + pool_query_tree_cost (next (oracle point)) oracle

def directional_halfspace_class {d : ℕ}
    (X : Finset (EuclideanSpace ℝ (Fin d)))
    (V : Finset (EuclideanSpace ℝ (Fin d))) : Set (↥X → Bool) :=
  {f | ∃ u ∈ V, ∃ t : ℝ, ∀ x : ↥X,
    f x = decide (t < inner ℝ u (x : EuclideanSpace ℝ (Fin d)))}

def unit_direction_set {d : ℕ}
    (V : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ u ∈ V, ‖u‖ = 1

noncomputable def normalized_hamming_error {α : Type u} [Fintype α]
    (f g : α → Bool) : ℝ :=
  ((Finset.univ.filter fun x => f x ≠ g x).card : ℝ) / Fintype.card α

noncomputable def proper_active_pac_learnable_within {α : Type u}
    [Fintype α] (C targets : Set (α → Bool)) (ε δ B : ℝ) : Prop :=
  ∃ learner : PMF (pool_query_tree α (α → Bool)),
    ∀ f ∈ targets,
      (∀ T ∈ learner.support,
          pool_query_tree_run T f ∈ C ∧
            (pool_query_tree_cost T f : ℝ) ≤ B) ∧
        learner.toOuterMeasure
            {T | normalized_hamming_error f (pool_query_tree_run T f) > ε} ≤
          ENNReal.ofReal δ

noncomputable def tolerant_targets {α : Type u} [Fintype α]
    (C : Set (α → Bool)) (c ε : ℝ) : Set (α → Bool) :=
  {f | ∃ g ∈ C, normalized_hamming_error f g ≤ c * ε}

noncomputable def clipped_binary_log (m : ℕ) : ℝ :=
  (Nat.log 2 (max 2 m) : ℝ)

noncomputable def inverse_accuracy_log (ε : ℝ) : ℝ :=
  Real.log (1 / ε)

noncomputable def tolerant_query_scale (D : ℕ) (ε : ℝ) : ℝ :=
  min ((D : ℝ) + inverse_accuracy_log ε) (1 / ε) * clipped_binary_log D

theorem d_directional_halfspace_tolerant_pac_learning :
    ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ < 1 ∧
      ∀ c : ℝ, 0 < c → c ≤ c₀ →
        ∀ δ : ℝ, 0 < δ → δ < 1 →
          ∃ K : ℝ, 0 < K ∧
            ∀ (d : ℕ)
              (X : Finset (EuclideanSpace ℝ (Fin d)))
              (V : Finset (EuclideanSpace ℝ (Fin d))),
              unit_direction_set V →
                ∀ ε : ℝ, 0 < ε → ε < 1 →
                  proper_active_pac_learnable_within
                    (directional_halfspace_class X V)
                    (tolerant_targets (directional_halfspace_class X V) c ε)
                    ε δ (K * tolerant_query_scale V.card ε) := by sorry

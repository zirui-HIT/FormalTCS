import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

set_option linter.all false
set_option maxHeartbeats 500000

def is_replacement_path {V : Type*} (G : SimpleGraph V) (f : ℕ) {u v : V}
    (π : G.Walk u v) : Prop :=
  ∃ F : Finset (Sym2 V),
    (↑F ⊆ G.edgeSet) ∧ F.card ≤ f ∧ (∀ e ∈ π.edges, e ∉ F) ∧
      π.length = (G.deleteEdges ↑F).dist u v

inductive is_consecutive_partition {V : Type*} (G : SimpleGraph V)
    (P : (a b : V) → G.Walk a b → Prop) :
    (n : ℕ) → (u v : V) → G.Walk u v → Prop
  | nil (u : V) : is_consecutive_partition G P 0 u u SimpleGraph.Walk.nil
  | cons {u w v : V} {n : ℕ} (p : G.Walk u w) (hp : P u w p)
      {q : G.Walk w v} (hq : is_consecutive_partition G P n w v q) :
      is_consecutive_partition G P (n + 1) u v (p.append q)

theorem intromain (k f : ℕ) (hk : 0 < k) (hf : 0 < f) (hkf : k ≤ f) :
    (∀ (V : Type) (G : SimpleGraph V) (u v : V) (π : G.Walk u v),
        is_replacement_path G f π →
          ∃ n ≤ 8 * k + 1,
            is_consecutive_partition G
              (fun _ _ p => is_replacement_path G (f / k) p) n u v π)
    ∧
    (2 ≤ f / k →
      ∃ (V : Type) (G : SimpleGraph V) (u v : V) (π : G.Walk u v),
        is_replacement_path G f π ∧
          ¬ ∃ n ≤ 2 * k,
            is_consecutive_partition G
              (fun _ _ p =>
                is_replacement_path G (f / k - 2) p) n u v π) := by sorry

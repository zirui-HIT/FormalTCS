import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Log

set_option linter.all false

noncomputable def edge_weight {d : ℕ} (a : Fin (d + 1) → ℝ)
    (x : Fin d → ℝ) : ℝ :=
  (∑ i : Fin d, a i.castSucc * x i) + a (Fin.last d)

structure parametric_dag (d : ℕ) where
  n : ℕ
  weight : Fin n → Fin n → Option (Fin (d + 1) → ℝ)
  acyclic : ∀ v : Fin n,
    ¬Relation.TransGen (fun u w => (weight u w).isSome = true) v v
  s : Fin n
  t : Fin n

def st_path {d : ℕ} (G : parametric_dag d)
    (p : List (Fin G.n)) : Prop :=
  p.head? = some G.s ∧ p.getLast? = some G.t ∧
    p.IsChain (fun u v => (G.weight u v).isSome = true)

noncomputable def path_weight {d : ℕ} (G : parametric_dag d)
    (p : List (Fin G.n)) (x : Fin d → ℝ) : ℝ :=
  ((p.zip p.tail).map fun uv =>
      (G.weight uv.1 uv.2).elim 0 (fun a => edge_weight a x)).foldr (· + ·) 0

def shortest_path_at {d : ℕ} (G : parametric_dag d)
    (p : List (Fin G.n)) (x : Fin d → ℝ) : Prop :=
  st_path G p ∧ ∀ q : List (Fin G.n),
    st_path G q → path_weight G p x ≤ path_weight G q x

def shortest_path_cover {d : ℕ} (G : parametric_dag d)
    (S : Set (List (Fin G.n))) : Prop :=
  (∀ p ∈ S, st_path G p) ∧
    ∀ x : Fin d → ℝ, ∃ p ∈ S, shortest_path_at G p x

noncomputable def mspc_size {d : ℕ} (G : parametric_dag d) : ℕ :=
  sInf {k : ℕ | ∃ S : Set (List (Fin G.n)),
    shortest_path_cover G S ∧ S.ncard = k}

theorem linear_upper_bound :
    ∃ C : ℕ, 0 < C ∧ ∀ (d : ℕ) (G : parametric_dag d),
      mspc_size G ≤ G.n ^ (C * d * Nat.log 2 G.n) := by sorry

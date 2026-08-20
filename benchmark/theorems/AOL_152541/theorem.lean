import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat

abbrev learner (X Y : Type*) := List (X × Y) → X → Set Y

def compat_set {X Y : Type*} (h : X → Set Y) (n : ℕ) : Set (List (X × Y)) :=
  {xy | xy.length = n ∧ ∀ p ∈ xy, p.2 ∈ h p.1}

def mistake_set {X Y : Type*} (A : learner X Y) (h : X → Set Y)
    (xy : List (X × Y)) : Set ℕ :=
  {k | ∃ p : X × Y, xy[k]? = some p ∧
    (p.2 ∉ A (xy.take k) p.1 ∨ ¬ A (xy.take k) p.1 ⊆ h p.1)}

noncomputable def mistake_bound_hyp {X Y : Type*} (A : learner X Y) (h : X → Set Y) (N : ℕ) : ℕ :=
  sSup ((fun xy => (mistake_set A h xy).ncard) '' compat_set h N)

noncomputable def mistake_bound_class {X Y : Type*} (H : Set (X → Set Y)) (A : learner X Y)
    (N : ℕ) : ℕ :=
  sSup ((fun h => mistake_bound_hyp A h N) '' H)

noncomputable def minimax_mistake_bound {X Y : Type*} (H : Set (X → Set Y)) (N : ℕ) : ℕ :=
  sInf (Set.range fun A : learner X Y => mistake_bound_class H A N)

structure ambiguous_tree {X Y : Type*} (H : Set (X → Set Y)) where
  verts : Set (List Y)
  inst : List Y → X
  hyp : List Y → (X → Set Y)
  defaults : Set (List Y)
  root_mem : ([] : List Y) ∈ verts
  prefix_closed : ∀ u ∈ verts, ∀ w : List Y, w <+: u → w ∈ verts
  verts_finite : verts.Finite
  default_child : ∀ u ∈ verts, (∃ y : Y, u ++ [y] ∈ verts) →
    ∃! y : Y, u ++ [y] ∈ verts ∧ u ++ [y] ∈ defaults
  leaf_hyp_mem : ∀ u ∈ verts, (¬ ∃ y : Y, u ++ [y] ∈ verts) → hyp u ∈ H
  leaf_hyp_compat : ∀ u ∈ verts, (¬ ∃ y : Y, u ++ [y] ∈ verts) →
    ∀ (k : ℕ) (y : Y), u[k]? = some y → y ∈ hyp u (inst (u.take k))

noncomputable def tree_depth {X Y : Type*} {H : Set (X → Set Y)} (T : ambiguous_tree H) : ℕ :=
  sSup ((fun u : List Y => u.length) '' T.verts)

def tree_leaves {X Y : Type*} {H : Set (X → Set Y)} (T : ambiguous_tree H) : Set (List Y) :=
  {u | u ∈ T.verts ∧ ¬ ∃ y : Y, u ++ [y] ∈ T.verts}

def relevant_edges {X Y : Type*} {H : Set (X → Set Y)} (T : ambiguous_tree H)
    (u : List Y) : Set ℕ :=
  {k | k < u.length ∧
    (u.take (k + 1) ∉ T.defaults ∨
      ∃ z : Y, u.take k ++ [z] ∈ T.verts ∧ z ∉ T.hyp u (T.inst (u.take k)))}

noncomputable def tree_rank_weighted {X Y : Type*} {H : Set (X → Set Y)} (T : ambiguous_tree H)
    (w : (X → Set Y) → ℕ) : ℕ :=
  sInf ((fun u => (relevant_edges T u).ncard + w (T.hyp u)) '' tree_leaves T)

noncomputable def al_dim_weighted {X Y : Type*} (H : Set (X → Set Y)) (w : (X → Set Y) → ℕ)
    (n : ℕ) : ℕ :=
  sSup {r : ℕ | ∃ T : ambiguous_tree H, tree_depth T ≤ n ∧ tree_rank_weighted T w = r}

noncomputable def al_dim {X Y : Type*} (H : Set (X → Set Y)) (n : ℕ) : ℕ :=
  al_dim_weighted H (fun _ => 0) n

theorem minimax_eq_al {X Y : Type*} [Fintype Y] {H : Set (X → Set Y)} (hH : H.Nonempty)
    (hne : ∀ h ∈ H, ∃ x : X, (h x).Nonempty) (N : ℕ) :
    minimax_mistake_bound H N = al_dim H N := by sorry

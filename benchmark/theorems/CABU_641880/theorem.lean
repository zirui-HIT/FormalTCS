import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Sym.Sym2
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sym

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def cross_cluster_ind (C : Finset V) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => |(if u ∈ C then (1 : ℝ) else 0) - (if v ∈ C then (1 : ℝ) else 0)|,
    fun u v => abs_sub_comm _ _⟩

noncomputable def cross_partition_ind (P : Finpartition (Finset.univ : Finset V)) : Sym2 V → ℝ :=
  fun e => if ∃ C ∈ P.parts, cross_cluster_ind C e = 1 then (1 : ℝ) else 0

noncomputable def cross_union_ind (w₁ w₂ : Sym2 V → ℝ) : Sym2 V → ℝ :=
  fun e => if w₁ e = 1 ∨ w₂ e = 1 then (1 : ℝ) else 0

def deg_weighted (c : Sym2 V → ℝ) (w : Sym2 V → ℝ) (v : V) : ℝ :=
  ∑ e : Sym2 V, if v ∈ e then w e * c e else 0

def delta_cut (c : Sym2 V → ℝ) (C : Finset V) : ℝ :=
  ∑ e : Sym2 V, cross_cluster_ind C e * c e

def restrict_to (S : Finset V) (d : V → ℝ) : V → ℝ :=
  fun v => if v ∈ S then d v else 0

def is_flow (f : V → V → ℝ) : Prop :=
  ∀ u v, f u v = - f v u

def has_congestion (c : Sym2 V → ℝ) (α : ℝ) (f : V → V → ℝ) : Prop :=
  ∀ u v, |f u v| ≤ α * c s(u, v)

def is_demand (b : V → ℝ) : Prop :=
  ∑ v, b v = 0

def routes (f : V → V → ℝ) (b : V → ℝ) : Prop :=
  ∀ v, ∑ u, f u v = b v

def mixes_simultaneously (c : Sym2 V → ℝ) (α : ℝ) {ι : Type*} (d : ι → V → ℝ)
    (s : Finset ι) : Prop :=
  ∀ b : ι → V → ℝ, (∀ i ∈ s, is_demand (b i)) → (∀ i ∈ s, ∀ v, |b i v| ≤ d i v) →
    ∃ f, is_flow f ∧ has_congestion c α f ∧ routes f (fun v => ∑ i ∈ s, b i v)

def is_congestion_approx (c : Sym2 V → ℝ) (𝒞 : Finset (Finset V)) (q : ℝ) : Prop :=
  ∀ b : V → ℝ, is_demand b → (∀ C ∈ 𝒞, |∑ v ∈ C, b v| ≤ delta_cut c C) →
    ∃ f, is_flow f ∧ has_congestion c q f ∧ routes f b

def refinement (P : ℕ → Finpartition (Finset.univ : Finset V)) (i L : ℕ) :
    Finpartition (Finset.univ : Finset V) :=
  (Finset.Icc i L).inf (fun j => P j)

def cut_collection (P : ℕ → Finpartition (Finset.univ : Finset V)) (L : ℕ) : Finset (Finset V) :=
  (Finset.Icc 1 L).biUnion (fun i => (refinement P i L).parts)

def valid_hierarchy (P : ℕ → Finpartition (Finset.univ : Finset V)) (L : ℕ) : Prop :=
  P 1 = ⊥ ∧ P L = ⊤

def mixing_hypothesis (c : Sym2 V → ℝ) (α : ℝ)
    (P : ℕ → Finpartition (Finset.univ : Finset V)) (L : ℕ) : Prop :=
  ∀ i ∈ Finset.Icc 1 (L - 1),
    mixes_simultaneously c α
      (fun C : Finset V =>
        restrict_to C
          (deg_weighted c (cross_union_ind (cross_partition_ind (P i)) (cross_cluster_ind C))))
      (P (i + 1)).parts

structure directed_path (V : Type*) where
  length : ℕ
  vertex : Fin (length + 1) → V

def directed_path_edge_count (p : directed_path V) (u v : V) : ℕ :=
  ∑ k : Fin p.length,
    if p.vertex (Fin.castSucc k) = u ∧ p.vertex (Fin.succ k) = v then 1 else 0

structure path_transport (V : Type*) where
  cardinality : ℕ
  path : Fin cardinality → directed_path V
  weight : Fin cardinality → ℝ
  weight_nonnegative : ∀ k, 0 ≤ weight k

def path_source_mass (T : path_transport V) (v : V) : ℝ :=
  ∑ k : Fin T.cardinality,
    if (T.path k).vertex ⟨0, Nat.zero_lt_succ _⟩ = v then T.weight k else 0

def path_receipt_mass (T : path_transport V) (v : V) : ℝ :=
  ∑ k : Fin T.cardinality,
    if (T.path k).vertex (Fin.last (T.path k).length) = v then T.weight k else 0

def path_edge_load (T : path_transport V) (u v : V) : ℝ :=
  ∑ k : Fin T.cardinality,
    T.weight k * ((directed_path_edge_count (T.path k) u v : ℝ) +
      (directed_path_edge_count (T.path k) v u : ℝ))

def transport_endpoint_coverage (c : Sym2 V → ℝ)
    (P : ℕ → Finpartition (Finset.univ : Finset V)) (L i : ℕ)
    (T : path_transport V) : Prop :=
  ∀ (a a' : V → ℝ) (q : Finset V → V → ℝ)
    (scale : ℕ → Fin T.cardinality → Fin 8 → ℝ)
    (cutoff : (j : ℕ) → (k : Fin T.cardinality) → Fin 8 →
      Fin ((T.path k).length + 1))
    (forward : ℕ → Fin T.cardinality → Fin 8 → Bool),
    is_demand a →
    (∀ v, |a v| ≤ deg_weighted c (cross_partition_ind (P i)) v) →
    is_demand a' →
    (∀ v, |a' v| ≤
      deg_weighted c (cross_partition_ind (P (i + 1))) v) →
    (∀ j ∈ Finset.Icc (i + 1) L, ∀ k, ∀ s : Fin 8,
      0 ≤ scale j k s ∧ scale j k s ≤ 1) →
    (∀ k, (∑ j ∈ Finset.Icc (i + 1) L, ∑ s : Fin 8, scale j k s) ≤
      8 * (L : ℝ)) →
    (∀ C ∈ (P (i + 1)).parts,
      is_demand (q C) ∧ (∀ v, v ∉ C → q C v = 0)) →
    (∀ v, a v - a' v - ∑ C ∈ (P (i + 1)).parts, q C v =
      ∑ j ∈ Finset.Icc (i + 1) L,
        ∑ k : Fin T.cardinality, ∑ s : Fin 8,
          scale j k s * T.weight k *
            ((if (T.path k).vertex (cutoff j k s) = v then (1 : ℝ) else 0) -
              if (if forward j k s = true then
                  (T.path k).vertex ⟨0, Nat.zero_lt_succ (T.path k).length⟩
                else (T.path k).vertex (Fin.last (T.path k).length)) = v
              then (1 : ℝ) else 0)) →
    ∀ C ∈ (P (i + 1)).parts, ∀ v,
      |q C v| ≤
        restrict_to C
          (fun w =>
            deg_weighted c (cross_partition_ind (P i)) w +
            deg_weighted c (cross_cluster_ind C) w) v

def flow_hypothesis (c : Sym2 V → ℝ) (β : ℝ)
    (P : ℕ → Finpartition (Finset.univ : Finset V)) (L : ℕ) : Prop :=
  ∀ i ∈ Finset.Icc 1 (L - 1),
    ∃ T : path_transport V,
      (∀ k, 0 < T.weight k →
        (T.path k).vertex ⟨0, Nat.zero_lt_succ (T.path k).length⟩ ≠
          (T.path k).vertex (Fin.last (T.path k).length)) ∧
      (∀ v, path_source_mass T v =
        deg_weighted c (cross_partition_ind (P (i + 1))) v) ∧
      (∀ v, 0 ≤ path_receipt_mass T v ∧
        path_receipt_mass T v ≤
          (1 / 2) * deg_weighted c (cross_partition_ind (P i)) v) ∧
      (∀ u v, path_edge_load T u v ≤ β * c s(u, v)) ∧
      transport_endpoint_coverage c P L i T

theorem cut_approx (c : Sym2 V → ℝ) (W α β : ℝ)
    (P : ℕ → Finpartition (Finset.univ : Finset V)) (L : ℕ)
    (hW : 1 ≤ W) (hc : ∀ e, c e = 0 ∨ (1 ≤ c e ∧ c e ≤ W))
    (hα : 1 ≤ α) (hβ : 1 ≤ β) (hL : 1 ≤ L)
    (hhier : valid_hierarchy P L)
    (hmix : mixing_hypothesis c α P L) (hflow : flow_hypothesis c β P L) :
    is_congestion_approx c (cut_collection P L) (16 * (L : ℝ) ^ 2 * α * β) := by sorry

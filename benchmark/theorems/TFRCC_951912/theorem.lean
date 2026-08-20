import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Sym
import Mathlib.InformationTheory.Hamming

set_option linter.all false
set_option maxHeartbeats 500000

universe u

structure rb_clustering (α : Type u) where
  sameBlock : α → α → Bool
  sameBlock_refl : ∀ x, sameBlock x x = true
  sameBlock_symm : ∀ x y, sameBlock x y = sameBlock y x
  sameBlock_trans : ∀ {x y z}, sameBlock x y = true →
    sameBlock y z = true → sameBlock x z = true

def same_block_on_pair {α : Type u} (C : rb_clustering α) : Sym2 α → Bool :=
  Sym2.lift ⟨C.sameBlock, C.sameBlock_symm⟩

def disagreement_distance {α : Type u} [Fintype α]
    (C D : rb_clustering α) : ℕ :=
  hammingDist (same_block_on_pair C) (same_block_on_pair D)

def colored_cluster_count {α : Type u} [Fintype α] (color : α → Bool)
    (C : rb_clustering α) (x : α) (b : Bool) : ℕ :=
  (Finset.univ.filter fun y => C.sameBlock x y = true ∧ color y = b).card

def population_ratio {α : Type u} [Fintype α] (color : α → Bool)
    (p q : ℕ) : Prop :=
  0 < Fintype.card α ∧
    q * (Finset.univ.filter fun x => color x = true).card =
      p * (Finset.univ.filter fun x => color x = false).card

def ratio_fair {α : Type u} [Fintype α] (color : α → Bool)
    (p q : ℕ) (C : rb_clustering α) : Prop :=
  ∀ x, q * colored_cluster_count color C x true =
    p * colored_cluster_count color C x false

noncomputable def consensus_objective {α : Type u} [Fintype α] {m : ℕ}
    (ell : ℝ) (inputs : Fin m → rb_clustering α) (F : rb_clustering α) : ℝ :=
  Real.rpow
    (∑ i, Real.rpow (disagreement_distance (inputs i) F : ℝ) ell)
    (1 / ell)

structure fair_consensus_algorithm where
  run : {α : Type u} → [Fintype α] → (color : α → Bool) → (m : ℕ) →
    (Fin m → rb_clustering α) → rb_clustering α
  cost : {α : Type u} → [Fintype α] → (color : α → Bool) → (m : ℕ) →
    (Fin m → rb_clustering α) → ℕ

def factor_approximate_consensus (A : fair_consensus_algorithm.{u})
    (ell factor : ℝ) (p q : ℕ) : Prop :=
  ∀ {α : Type u} [Fintype α] (color : α → Bool) (m : ℕ)
    (inputs : Fin m → rb_clustering α),
    population_ratio color p q →
      (Finset.univ.filter fun x => color x = false).card ≤
        (Finset.univ.filter fun x => color x = true).card →
      ratio_fair color p q (A.run color m inputs) ∧
      ∀ F : rb_clustering α, ratio_fair color p q F →
        consensus_objective ell inputs (A.run color m inputs) ≤
          factor * consensus_objective ell inputs F

def quadratic_consensus_time (A : fair_consensus_algorithm.{u}) : Prop :=
  ∃ K : ℕ, ∀ {α : Type u} [Fintype α] (color : α → Bool) (m : ℕ)
    (inputs : Fin m → rb_clustering α),
    A.cost color m inputs ≤ K * m ^ 2 * Fintype.card α ^ 2

def has_fair_consensus_algorithm (ell factor : ℝ) (p q : ℕ) : Prop :=
  ∃ A : fair_consensus_algorithm.{u},
    factor_approximate_consensus A ell factor p q ∧ quadratic_consensus_time A

theorem consensus_p_q_fair (ell : ℝ) (p q : ℕ)
    (hEll : 1 ≤ ell) (hp : 1 < p) (hq : 1 < q)
    (hpq : Nat.Coprime p q) :
    has_fair_consensus_algorithm ell 35 p q := by sorry

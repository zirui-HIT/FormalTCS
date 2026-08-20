import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Monotone.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

def is_submodular {S : Type*} [DecidableEq S] (φ : Finset S → ℝ) : Prop :=
  ∀ X Y : Finset S, φ (X ∩ Y) + φ (X ∪ Y) ≤ φ X + φ Y

def is_polymatroid {S : Type*} [DecidableEq S] (φ : Finset S → ℝ) : Prop :=
  Monotone φ ∧ is_submodular φ ∧ φ ∅ = 0

def is_k_polymatroid {S : Type*} [DecidableEq S] (k : ℝ) (φ : Finset S → ℝ) : Prop :=
  is_polymatroid φ ∧ ∀ X : Finset S, φ X ≤ k * (X.card : ℝ)

def is_integer_valued {S : Type*} (φ : Finset S → ℝ) : Prop :=
  ∀ X : Finset S, ∃ n : ℤ, φ X = (n : ℝ)

def is_coupling {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    (φ₁ : Finset S₁ → ℝ) (φ₂ : Finset S₂ → ℝ) (φ : Finset (S₁ × S₂) → ℝ) : Prop :=
  (∀ X₁ : Finset S₁,
      φ (X₁ ×ˢ (Finset.univ : Finset S₂)) = φ₁ X₁ * φ₂ (Finset.univ : Finset S₂)) ∧
  (∀ X₂ : Finset S₂,
      φ ((Finset.univ : Finset S₁) ×ˢ X₂) = φ₁ (Finset.univ : Finset S₁) * φ₂ X₂)

theorem poly {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    [DecidableEq S₁] [DecidableEq S₂]
    (k₁ k₂ : ℝ) (φ₁ : Finset S₁ → ℝ) (φ₂ : Finset S₂ → ℝ)
    (h₁ : is_k_polymatroid k₁ φ₁) (h₂ : is_k_polymatroid k₂ φ₂) :
    ∃ φ : Finset (S₁ × S₂) → ℝ,
      is_k_polymatroid (k₁ * k₂) φ ∧ is_coupling φ₁ φ₂ φ ∧
      (is_integer_valued φ₁ → is_integer_valued φ₂ → is_integer_valued φ) := by sorry

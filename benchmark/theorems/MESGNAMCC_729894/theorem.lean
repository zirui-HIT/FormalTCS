import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators

universe u v w

def indicator_function_one {A : Type*} (u : A → ℝ) : Prop :=
  ∀ a, u a = 0 ∨ u a = 1

def indicator_function_two {A B : Type*} (u : A → B → ℝ) : Prop :=
  ∀ a b, u a b = 0 ∨ u a b = 1

def cylinder_intersection {X Y Z : Type*} (f : X → Y → ℝ) (g : X → Z → ℝ)
    (h : Y → Z → ℝ) : X → Y → Z → ℝ :=
  fun x y z ↦ f x y * g x z * h y z

noncomputable def product_uniform_density {X Y Z : Type*} [Fintype X] [Fintype Y]
    [Fintype Z] (q : X → Y → Z → ℝ) : ℝ :=
  (∑ x, ∑ y, ∑ z, q x y z) /
    ((Fintype.card X : ℝ) * (Fintype.card Y : ℝ) * (Fintype.card Z : ℝ))

def slice_function {X Y Z : Type*} (s : X → Y → Z → ℝ) : Prop :=
  (∃ a : X → Y → ℝ, ∃ b : Z → ℝ,
      indicator_function_two a ∧ indicator_function_one b ∧
        ∀ x y z, s x y z = a x y * b z) ∨
  (∃ a : X → ℝ, ∃ b : Y → Z → ℝ,
      indicator_function_one a ∧ indicator_function_two b ∧
        ∀ x y z, s x y z = a x * b y z) ∨
  (∃ a : X → Z → ℝ, ∃ b : Y → ℝ,
      indicator_function_two a ∧ indicator_function_one b ∧
        ∀ x y z, s x y z = a x z * b y)

def slice_cover_sum {X Y Z : Type*} {R : ℕ} (s : Fin R → X → Y → Z → ℝ) :
    X → Y → Z → ℝ :=
  fun x y z ↦ ∑ i, s i x y z

theorem slice_function_removal_lemma :
    ∃ (decayConstant sliceConstant countConstant : ℝ) (threshold : ℕ),
      0 < decayConstant ∧ 0 < sliceConstant ∧ 0 < countConstant ∧
      ∀ (X : Type u) (Y : Type v) (Z : Type w) [Fintype X] [Fintype Y] [Fintype Z]
        [Nonempty X] [Nonempty Y] [Nonempty Z]
        (f : X → Y → ℝ) (g : X → Z → ℝ) (h : Y → Z → ℝ) (d : ℕ),
        threshold ≤ d →
        indicator_function_two f →
        indicator_function_two g →
        indicator_function_two h →
        product_uniform_density (cylinder_intersection f g h) ≤
            Real.rpow 2 (-(d : ℝ)) →
        ∃ (R : ℕ) (s : Fin R → X → Y → Z → ℝ),
          (∀ i, slice_function (s i)) ∧
          (∀ x y z,
            cylinder_intersection f g h x y z ≤ slice_cover_sum s x y z) ∧
          product_uniform_density (slice_cover_sum s) ≤
            Real.rpow 2 (-decayConstant * Real.sqrt (d : ℝ)) *
              Real.log (((Fintype.card X * Fintype.card Y * Fintype.card Z : ℕ) : ℝ)) ∧
          (∀ i, Real.rpow 2 (-sliceConstant * (d : ℝ)) ≤
            product_uniform_density (s i)) ∧
          (R : ℝ) ≤ Real.rpow 2 (countConstant * (d : ℝ)) *
    Real.log (((Fintype.card X * Fintype.card Y * Fintype.card Z : ℕ) : ℝ)) := by sorry

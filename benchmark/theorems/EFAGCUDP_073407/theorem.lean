import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Lattice.Fold

open scoped BigOperators

structure fair_goods_instance (Group ItemType : Type*) where
  groupSize : Group → ℕ
  valuation : Group → ItemType → ℝ
  copies : ItemType → ℕ
  smallestGroup : Group
  largestGroup : Group
  someType : ItemType

def number_of_groups {Group ItemType : Type*} [Fintype Group]
    (I : fair_goods_instance Group ItemType) : ℕ :=
  Fintype.card Group

def number_of_types {Group ItemType : Type*} [Fintype ItemType]
    (I : fair_goods_instance Group ItemType) : ℕ :=
  Fintype.card ItemType

def number_of_agents {Group ItemType : Type*} [Fintype Group]
    (I : fair_goods_instance Group ItemType) : ℕ :=
  ∑ i, I.groupSize i

def group_size_gcd {Group ItemType : Type*} [Fintype Group]
    (I : fair_goods_instance Group ItemType) : ℕ :=
  Finset.univ.gcd I.groupSize

def frobenius_threshold {Group ItemType : Type*} [Fintype Group]
    (I : fair_goods_instance Group ItemType) : ℕ :=
  group_size_gcd I * (I.groupSize I.smallestGroup / group_size_gcd I - 1) *
    (I.groupSize I.largestGroup / group_size_gcd I - 1)

def goods_profile_assumptions {Group ItemType : Type*} [Fintype ItemType]
    (I : fair_goods_instance Group ItemType) : Prop :=
  (∀ i, 0 < I.groupSize i) ∧
    (∀ i, I.groupSize I.smallestGroup ≤ I.groupSize i) ∧
    (∀ i, I.groupSize i ≤ I.groupSize I.largestGroup) ∧
    (∀ i z, 0 ≤ I.valuation i z) ∧
    (∀ i, 0 < Real.sqrt (∑ z, (I.valuation i z) ^ 2)) ∧
    (∃ i i' : Group, i ≠ i') ∧
    (∀ i i', i ≠ i' →
      0 < ∑ z,
        (I.valuation i z / Real.sqrt (∑ w, (I.valuation i w) ^ 2) -
          I.valuation i' z / Real.sqrt (∑ w, (I.valuation i' w) ^ 2)) ^ 2)

noncomputable def unit_valuation_norm {Group ItemType : Type*} [Fintype ItemType]
    (I : fair_goods_instance Group ItemType) (i : Group) : ℝ :=
  Real.sqrt (∑ z, (I.valuation i z) ^ 2)

noncomputable def unit_normalized_value {Group ItemType : Type*} [Fintype ItemType]
    (I : fair_goods_instance Group ItemType) (i : Group) (z : ItemType) : ℝ :=
  I.valuation i z / unit_valuation_norm I i

noncomputable def unit_separation_squared {Group ItemType : Type*} [Fintype ItemType]
    (I : fair_goods_instance Group ItemType) (i i' : Group) : ℝ :=
  ∑ z, (unit_normalized_value I i z - unit_normalized_value I i' z) ^ 2

noncomputable def minimum_unit_separation_squared {Group ItemType : Type*}
    [Fintype Group] [Fintype ItemType] (I : fair_goods_instance Group ItemType) : ℝ := by
  classical
  let pairs : Finset (Group × Group) :=
    (Finset.univ.product Finset.univ).filter (fun p => p.1 ≠ p.2)
  exact if h : pairs.Nonempty then
    pairs.inf' h (fun p => unit_separation_squared I p.1 p.2)
  else 0

def advertised_copy_complexity {Group ItemType : Type*} [Fintype Group] [Fintype ItemType]
    (I : fair_goods_instance Group ItemType) : ℕ :=
  number_of_groups I ^ 2 +
    number_of_types I * (frobenius_threshold I + number_of_agents I +
      I.groupSize I.largestGroup - number_of_groups I - 1)

noncomputable def advertised_copy_lower_bound {Group ItemType : Type*}
    [Fintype Group] [Fintype ItemType] (I : fair_goods_instance Group ItemType) : ℝ :=
  ((4 * number_of_agents I * advertised_copy_complexity I : ℕ) : ℝ) /
    minimum_unit_separation_squared I

def allocation (Group ItemType : Type*) :=
  Group → ItemType → ℕ

def bundle_value {Group ItemType : Type*} [Fintype ItemType]
    (I : fair_goods_instance Group ItemType) (A : allocation Group ItemType)
    (i i' : Group) : ℝ :=
  ∑ z, I.valuation i z * (A i' z : ℝ)

def complete_allocation {Group ItemType : Type*} [Fintype Group]
    (I : fair_goods_instance Group ItemType) (A : allocation Group ItemType) : Prop :=
  ∀ z, ∑ i, I.groupSize i * A i z = I.copies z

def envy_free_allocation {Group ItemType : Type*} [Fintype ItemType]
    (I : fair_goods_instance Group ItemType) (A : allocation Group ItemType) : Prop :=
  ∀ i i', bundle_value I A i i' ≤ bundle_value I A i i

def admits_envy_free_allocation {Group ItemType : Type*} [Fintype Group] [Fintype ItemType]
    (I : fair_goods_instance Group ItemType) : Prop :=
  ∃ A : allocation Group ItemType, complete_allocation I A ∧ envy_free_allocation I A

theorem existence_of_envy_free_goods_allocation {Group ItemType : Type*}
    [Fintype Group] [Fintype ItemType] (I : fair_goods_instance Group ItemType)
    (hprofile : goods_profile_assumptions I)
    (hpositive : ∀ z, 0 < I.copies z)
    (hbound : ∀ z, advertised_copy_lower_bound I ≤ (I.copies z : ℝ))
    (hdiv : ∀ z, group_size_gcd I ∣ I.copies z) :
    admits_envy_free_allocation I := by sorry

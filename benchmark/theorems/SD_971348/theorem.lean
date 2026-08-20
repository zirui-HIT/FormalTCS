import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Topology.Homeomorph.Defs

abbrev binary_concept_class (X : Type*) := Set (X → Bool)

def indexed_shatters {X I : Type*} [Fintype I]
    (H : binary_concept_class X) (points : I → X) : Prop :=
  ∀ labels : I → Bool, ∃ h ∈ H, ∀ i, h (points i) = labels i

def vc_dimension_at_most {X : Type*} (H : binary_concept_class X) (a : ℤ) : Prop :=
  ∀ (I : Type) [Fintype I] (points : I → X),
    Function.Injective points →
    indexed_shatters H points →
    (Fintype.card I : ℤ) ≤ a

def indexed_dual_antipodally_shatters {X I : Type*} [Fintype I]
    (H : binary_concept_class X) (concepts : I → X → Bool) : Prop :=
  (∀ i, concepts i ∈ H) ∧
    ∀ labels : I → Bool,
      ∃ x : X,
        (∀ i, concepts i x = labels i) ∨
          (∀ i, concepts i x = !(labels i))

def dual_antipodal_vc_dimension_at_most {X : Type*}
    (H : binary_concept_class X) (b : ℤ) : Prop :=
  ∀ (I : Type) [Fintype I] (concepts : I → X → Bool),
    Function.Injective concepts →
    indexed_dual_antipodally_shatters H concepts →
    (Fintype.card I : ℤ) ≤ b

structure PreAbstractSimplicialComplex (V : Type*) where
  faces : Set (Finset V)
  nonempty_of_mem : ∀ ⦃s⦄, s ∈ faces → s.Nonempty
  down_closed : ∀ ⦃s⦄, s ∈ faces → ∀ ⦃t⦄, t ⊆ s → t.Nonempty → t ∈ faces

noncomputable def simplicial_geometric_realization {V : Type*}
    [Fintype V] [DecidableEq V] (K : PreAbstractSimplicialComplex V) : Type _ := by
  classical
  exact
    { weights : V → ℝ //
      (∀ v, 0 ≤ weights v) ∧
        (∑ v, weights v) = 1 ∧
          (Finset.univ.filter fun v => weights v ≠ 0) ∈ K.faces }

noncomputable instance simplicial_geometric_realization_topological_space
    {V : Type*} [Fintype V] [DecidableEq V]
    (K : PreAbstractSimplicialComplex V) :
    TopologicalSpace (simplicial_geometric_realization K) := by
  classical
  unfold simplicial_geometric_realization
  infer_instance

structure antipodal_simplicial_sphere (n : ℕ) where
  Vertex : Type
  [vertexFintype : Fintype Vertex]
  [vertexDecidableEq : DecidableEq Vertex]
  complex : PreAbstractSimplicialComplex Vertex
  antipode : Vertex ≃ Vertex
  antipode_involutive : ∀ v, antipode (antipode v) = v
  antipode_fixed_point_free : ∀ v, antipode v ≠ v
  antipode_preserves_faces :
    ∀ s : Finset Vertex, s ∈ complex.faces ↔ s.image antipode ∈ complex.faces
  realizationAntipode :
    simplicial_geometric_realization complex ≃ₜ
      simplicial_geometric_realization complex
  realizationAntipode_coordinates :
    ∀ w v, (realizationAntipode w).1 (antipode v) = w.1 v
  toStandardSphere :
    simplicial_geometric_realization complex ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1
  toStandardSphere_equivariant :
    ∀ w,
      (toStandardSphere (realizationAntipode w)).1 =
        -(toStandardSphere w).1

def labeled_antipode {X : Type*} (z : X × Bool) : X × Bool :=
  (z.1, !z.2)

def mapped_face_antipodally_realizable {X V : Type*} [DecidableEq V]
    (H : binary_concept_class X) (f : V → X × Bool) (s : Finset V) : Prop :=
  (∃ h ∈ H, ∀ v ∈ s, (f v).2 = h (f v).1) ∧
    (∃ h ∈ H, ∀ v ∈ s, !(f v).2 = h (f v).1)

def admits_simplicial_sphere {X : Type*}
    (H : binary_concept_class X) (n : ℕ) : Prop :=
  ∃ S : antipodal_simplicial_sphere n,
    ∃ f : S.Vertex → X × Bool,
      (∀ s : Finset S.Vertex, s ∈ S.complex.faces →
        @mapped_face_antipodally_realizable X S.Vertex
          S.vertexDecidableEq H f s) ∧
      (∀ v, f (S.antipode v) = labeled_antipode (f v))

def simplicial_spherical_dimension_at_least {X : Type*}
    (H : binary_concept_class X) (n : ℤ) : Prop :=
  n ≤ -1 ∨ ∃ m : ℕ, n ≤ (m : ℤ) ∧ admits_simplicial_sphere H m

abbrev integer_unit_sphere (n : ℤ) :=
  Metric.sphere
    (0 : EuclideanSpace ℝ (Fin (n + 1).toNat))
    1

noncomputable def margin_partial_classifier {n : ℤ} (ε : ℝ)
    (u v : integer_unit_sphere n) : Option Bool :=
  if InnerProductGeometry.angle u.1 v.1 ≤ ε then
    some true
  else if InnerProductGeometry.angle (-u.1) v.1 ≤ ε then
    some false
  else
    none

noncomputable def margin_linear_partial_class (n : ℤ) (ε : ℝ) :
    Set (integer_unit_sphere n → Option Bool) :=
  Set.range (margin_partial_classifier (n := n) ε)

def disambiguates {X : Type*} (H : binary_concept_class X)
    (P : Set (X → Option Bool)) : Prop :=
  ∀ p ∈ P, ∃ h ∈ H, ∀ x y, p x = some y → h x = y

def has_bounded_spherical_class (a b n : ℤ) : Prop :=
  ∃ (X : Type) (H : binary_concept_class X),
    vc_dimension_at_most H a ∧
      dual_antipodal_vc_dimension_at_most H b ∧
        simplicial_spherical_dimension_at_least H n

noncomputable def has_margin_disambiguation (a b n : ℤ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ε < Real.pi / 2 ∧
    ∃ H : binary_concept_class (integer_unit_sphere n),
      disambiguates H (margin_linear_partial_class n ε) ∧
        vc_dimension_at_most H a ∧
          dual_antipodal_vc_dimension_at_most H b

theorem rough_equivalence_between_disambiguations_and_spherical_dimension
    (a b n : ℤ) :
    has_bounded_spherical_class a b n ↔
      has_margin_disambiguation a b n := by sorry

import Architect
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Topology.Homeomorph.Defs

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:binary-concept-class"
  (statement := /-- For a type \(X\), a binary concept class on \(X\) is a set of functions from \(X\) to the two labels \(\{0,1\}\). -/)
  (title := /-- Binary concept classes -/)
  (latexEnv := "definition")]
abbrev binary_concept_class (X : Type*) := Set (X → Bool)

@[blueprint "def:indexed-shatters"
  (statement := /-- Let \(H\) be a binary concept class on \(X\), let \(I\) be a finite type, and let \(x:I\to X\).  The class \(H\) shatters the indexed family \(x\) if, for every labeling \(\ell:I\to\{0,1\}\), there is \(h\in H\) such that \(h(x_i)=\ell_i\) for every \(i\in I\). -/)
  (title := /-- Indexed shattering -/)
  (latexEnv := "definition")]
def indexed_shatters {X I : Type*} [Fintype I]
    (H : binary_concept_class X) (points : I → X) : Prop :=
  ∀ labels : I → Bool, ∃ h ∈ H, ∀ i, h (points i) = labels i

@[blueprint "def:vc-dimension-at-most"
  (statement := /-- Let \(H\) be a binary concept class on \(X\) and let \(a\in\mathbb{Z}\).  The VC dimension of \(H\) is at most \(a\) if every injectively indexed finite family shattered by \(H\) has cardinality at most \(a\). -/)
  (title := /-- An integer upper bound on VC dimension -/)
  (latexEnv := "definition")]
def vc_dimension_at_most {X : Type*} (H : binary_concept_class X) (a : ℤ) : Prop :=
  ∀ (I : Type) [Fintype I] (points : I → X),
    Function.Injective points →
    indexed_shatters H points →
    (Fintype.card I : ℤ) ≤ a

@[blueprint "def:indexed-dual-antipodally-shatters"
  (statement := /-- Let \(H\) be a binary concept class on \(X\), and let \((h_i)_{i\in I}\) be a finite family of members of \(H\).  This family is dually antipodally shattered if, for every labeling \(\ell:I\to\{0,1\}\), there is \(x\in X\) for which either \(h_i(x)=\ell_i\) for all \(i\), or \(h_i(x)=1-\ell_i\) for all \(i\). -/)
  (title := /-- Indexed dual antipodal shattering -/)
  (latexEnv := "definition")]
def indexed_dual_antipodally_shatters {X I : Type*} [Fintype I]
    (H : binary_concept_class X) (concepts : I → X → Bool) : Prop :=
  (∀ i, concepts i ∈ H) ∧
    ∀ labels : I → Bool,
      ∃ x : X,
        (∀ i, concepts i x = labels i) ∨
          (∀ i, concepts i x = !(labels i))

@[blueprint "def:dual-antipodal-vc-dimension-at-most"
  (statement := /-- Let \(H\) be a binary concept class on \(X\) and let \(b\in\mathbb{Z}\).  Its dual antipodal VC dimension is at most \(b\) if every injectively indexed finite subfamily which is dually antipodally shattered has cardinality at most \(b\). -/)
  (title := /-- An integer upper bound on dual antipodal VC dimension -/)
  (latexEnv := "definition")]
def dual_antipodal_vc_dimension_at_most {X : Type*}
    (H : binary_concept_class X) (b : ℤ) : Prop :=
  ∀ (I : Type) [Fintype I] (concepts : I → X → Bool),
    Function.Injective concepts →
    indexed_dual_antipodally_shatters H concepts →
    (Fintype.card I : ℤ) ≤ b

@[blueprint "def:simplicial-geometric-realization"
  (statement := /-- Let \(K\) be a finite abstract simplicial complex with vertex set \(V\).  Its geometric realization is the space of nonnegative functions \(w:V\to\mathbb{R}\) whose coordinates sum to \(1\) and whose nonzero support is a face of \(K\). -/)
  (title := /-- Barycentric geometric realization -/)
  (latexEnv := "definition")]
noncomputable def simplicial_geometric_realization {V : Type*}
    [Fintype V] [DecidableEq V] (K : PreAbstractSimplicialComplex V) : Type _ := by
  classical
  exact
    { weights : V → ℝ //
      (∀ v, 0 ≤ weights v) ∧
        (∑ v, weights v) = 1 ∧
          (Finset.univ.filter fun v => weights v ≠ 0) ∈ K.faces }

@[blueprint "def:simplicial-geometric-realization-topological-space"
  (statement := /-- The geometric realization \(|K|\) carries the subspace topology inherited from the finite-dimensional coordinate space \(\mathbb{R}^V\). -/)
  (title := /-- Topology on a simplicial realization -/)
  (latexEnv := "definition")]
noncomputable instance simplicial_geometric_realization_topological_space
    {V : Type*} [Fintype V] [DecidableEq V]
    (K : PreAbstractSimplicialComplex V) :
    TopologicalSpace (simplicial_geometric_realization K) := by
  classical
  unfold simplicial_geometric_realization
  infer_instance

@[blueprint "def:antipodal-simplicial-sphere"
  (statement := /-- An antipodal simplicial \(n\)-sphere consists of a finite simplicial complex \(K\), a fixed-point-free involutive simplicial permutation \(\tau\) of its vertices, the induced coordinate-permuting involution of \(|K|\), and a homeomorphism \(|K|\to S^n\) which intertwines that involution with \(z\mapsto-z\). -/)
  (title := /-- Antipodal simplicial spheres -/)
  (latexEnv := "definition")]
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

@[blueprint "def:labeled-antipode"
  (statement := /-- The antipode of a labeled point \((x,y)\) is the point \((x,1-y)\) obtained by reversing its binary label. -/)
  (title := /-- Antipodality on labeled points -/)
  (latexEnv := "definition")]
def labeled_antipode {X : Type*} (z : X × Bool) : X × Bool :=
  (z.1, !z.2)

@[blueprint "def:mapped-face-antipodally-realizable"
  (statement := /-- Let \(H\) be a binary concept class on \(X\), let \(s\) be a finite set of vertices, and map each vertex \(v\) to a labeled point \(f(v)\).  The mapped face is antipodally realizable by \(H\) if one member of \(H\) realizes all labels \(f(v)\), \(v\in s\), and another member realizes all reversed labels. -/)
  (title := /-- Antipodally realizable labeled faces -/)
  (latexEnv := "definition")]
def mapped_face_antipodally_realizable {X V : Type*} [DecidableEq V]
    (H : binary_concept_class X) (f : V → X × Bool) (s : Finset V) : Prop :=
  (∃ h ∈ H, ∀ v ∈ s, (f v).2 = h (f v).1) ∧
    (∃ h ∈ H, ∀ v ∈ s, !(f v).2 = h (f v).1)

@[blueprint "def:admits-simplicial-sphere"
  (statement := /-- A binary concept class \(H\) admits a simplicial \(n\)-sphere if there are an antipodal simplicial \(n\)-sphere \(K\) and a vertex map from \(K\) to labeled points such that every face maps to an antipodally realizable face and the vertex map commutes with antipodality. -/)
  (title := /-- Admission of a simplicial sphere -/)
  (latexEnv := "definition")]
def admits_simplicial_sphere {X : Type*}
    (H : binary_concept_class X) (n : ℕ) : Prop :=
  ∃ S : antipodal_simplicial_sphere n,
    ∃ f : S.Vertex → X × Bool,
      (∀ s : Finset S.Vertex, s ∈ S.complex.faces →
        @mapped_face_antipodally_realizable X S.Vertex
          S.vertexDecidableEq H f s) ∧
      (∀ v, f (S.antipode v) = labeled_antipode (f v))

@[blueprint "def:simplicial-spherical-dimension-at-least"
  (statement := /-- Let \(H\) be a binary concept class and let \(n\in\mathbb{Z}\).  Its simplicial spherical dimension is at least \(n\) if \(n\leq-1\), or if \(H\) admits a simplicial \(m\)-sphere for some nonnegative integer \(m\geq n\).  This incorporates the convention that the least possible spherical dimension is \(-1\). -/)
  (title := /-- A lower bound on simplicial spherical dimension -/)
  (latexEnv := "definition")]
def simplicial_spherical_dimension_at_least {X : Type*}
    (H : binary_concept_class X) (n : ℤ) : Prop :=
  n ≤ -1 ∨ ∃ m : ℕ, n ≤ (m : ℤ) ∧ admits_simplicial_sphere H m

@[blueprint "def:integer-unit-sphere"
  (statement := /-- For \(n\in\mathbb{Z}\), the standard \(n\)-sphere is the unit sphere in \(\mathbb{R}^{(n+1)_{\geq0}}\).  Thus this agrees with the usual \(n\)-sphere when \(n\geq0\), and is empty when \(n\leq-1\). -/)
  (title := /-- Integer-indexed unit spheres -/)
  (latexEnv := "definition")]
abbrev integer_unit_sphere (n : ℤ) :=
  Metric.sphere
    (0 : EuclideanSpace ℝ (Fin (n + 1).toNat))
    1

@[blueprint "def:margin-partial-classifier"
  (statement := /-- Let \(u\) be a point of the \(n\)-sphere and let \(\varepsilon\in\mathbb{R}\).  The associated partial margin classifier labels \(v\) positively when the angular distance from \(u\) to \(v\) is at most \(\varepsilon\), labels it negatively when the angular distance from \(-u\) to \(v\) is at most \(\varepsilon\), and is undefined otherwise.  The positive clause has priority if both inequalities hold, exactly as in this displayed case definition. -/)
  (title := /-- Partial linear classifiers with angular margin -/)
  (latexEnv := "definition")]
noncomputable def margin_partial_classifier {n : ℤ} (ε : ℝ)
    (u v : integer_unit_sphere n) : Option Bool :=
  if InnerProductGeometry.angle u.1 v.1 ≤ ε then
    some true
  else if InnerProductGeometry.angle (-u.1) v.1 ≤ ε then
    some false
  else
    none

@[blueprint "def:margin-linear-partial-class"
  (statement := /-- The partial class \(\mathcal L_{n,\varepsilon}\) consists of all partial margin classifiers on the \(n\)-sphere whose normal vector \(u\) ranges over that sphere. -/)
  (title := /-- The class of partial margin classifiers -/)
  (latexEnv := "definition")]
noncomputable def margin_linear_partial_class (n : ℤ) (ε : ℝ) :
    Set (integer_unit_sphere n → Option Bool) :=
  Set.range (margin_partial_classifier (n := n) ε)

@[blueprint "def:disambiguates"
  (statement := /-- A total binary concept class \(H\) disambiguates a partial class \(P\) if every \(p\in P\) has an extension \(h\in H\): for every point \(x\) and label \(y\), the equality \(p(x)=y\) implies \(h(x)=y\). -/)
  (title := /-- Disambiguation by total concepts -/)
  (latexEnv := "definition")]
def disambiguates {X : Type*} (H : binary_concept_class X)
    (P : Set (X → Option Bool)) : Prop :=
  ∀ p ∈ P, ∃ h ∈ H, ∀ x y, p x = some y → h x = y

@[blueprint "def:has-bounded-spherical-class"
  (statement := /-- For integers \(a,b,n\), this proposition asserts the existence of a domain \(X\) and a binary concept class \(H\) on \(X\) whose VC dimension is at most \(a\), whose dual antipodal VC dimension is at most \(b\), and whose simplicial spherical dimension is at least \(n\). -/)
  (title := /-- The spherical-dimension side of the equivalence -/)
  (latexEnv := "definition")]
def has_bounded_spherical_class (a b n : ℤ) : Prop :=
  ∃ (X : Type) (H : binary_concept_class X),
    vc_dimension_at_most H a ∧
      dual_antipodal_vc_dimension_at_most H b ∧
        simplicial_spherical_dimension_at_least H n

@[blueprint "def:has-margin-disambiguation"
  (statement := /-- For integers \(a,b,n\), this proposition asserts that for some angular radius \(\varepsilon\) satisfying \(0<\varepsilon<\pi/2\), the partial class \(\mathcal L_{n,\varepsilon}\) has a disambiguating total class whose VC dimension is at most \(a\) and whose dual antipodal VC dimension is at most \(b\).  Equivalently, its cosine margin \(\cos\varepsilon\) is strictly positive. -/)
  (title := /-- The margin-disambiguation side of the equivalence -/)
  (latexEnv := "definition")]
noncomputable def has_margin_disambiguation (a b n : ℤ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ε < Real.pi / 2 ∧
    ∃ H : binary_concept_class (integer_unit_sphere n),
      disambiguates H (margin_linear_partial_class n ε) ∧
        vc_dimension_at_most H a ∧
          dual_antipodal_vc_dimension_at_most H b

@[blueprint "def:standard-sphere-antipode-for-margin-disambiguation"
  (statement := /-- For every natural number \(m\), negation defines an involutive equivalence of the standard unit \(m\)-sphere. -/)
  (title := /-- Antipodality on the standard sphere -/)
  (latexEnv := "definition")]
noncomputable def standard_sphere_antipode_for_margin_disambiguation (m : ℕ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 where
  toFun u := ⟨-u.1, by simpa [Metric.mem_sphere, dist_eq_norm] using u.2⟩
  invFun u := ⟨-u.1, by simpa [Metric.mem_sphere, dist_eq_norm] using u.2⟩
  left_inv u := by ext; simp
  right_inv u := by ext; simp

@[blueprint "lem:antipodal-simplicial-sphere-has-margin-selector"
  (statement := /-- For every antipodal simplicial \(m\)-sphere, there are a radius \(0<\varepsilon<\pi/2\) and an antipodality-compatible vertex selector on the standard \(m\)-sphere such that the vertices selected throughout each angular \(\varepsilon\)-cap lie in a single face. -/)
  (proof := /-- Transport the standard sphere to the geometric realization by \cref{def:antipodal-simplicial-sphere}.  At every point choose a vertex whose barycentric coordinate is at least the reciprocal of the number of vertices, and make these choices on antipodal pairs so that they commute with \cref{def:standard-sphere-antipode-for-margin-disambiguation}.  Uniform continuity of the inverse homeomorphism supplies a positive angular radius on which barycentric coordinates move by less than half this reciprocal.  Hence every vertex selected in the cap about a point has positive coordinate at that point, so all selected vertices belong to its support face in \cref{def:simplicial-geometric-realization}. -/)
  (title := /-- An equivariant face-local vertex selector -/)
  (latexEnv := "lemma")]
lemma antipodal_simplicial_sphere_has_margin_selector
    (m : ℕ) (S : antipodal_simplicial_sphere m) :
    ∃ ε : ℝ, 0 < ε ∧ ε < Real.pi / 2 ∧
      ∃ q : Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 → S.Vertex,
        (∀ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
          ∃ s : Finset S.Vertex, s ∈ S.complex.faces ∧
          ∀ v, InnerProductGeometry.angle u.1 v.1 ≤ ε → q v ∈ s) ∧
        ∀ u, q (standard_sphere_antipode_for_margin_disambiguation m u) =
          S.antipode (q u) := by
  classical
  letI : Fintype S.Vertex := S.vertexFintype
  letI : DecidableEq S.Vertex := S.vertexDecidableEq
  let Y := Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1
  let A : Y ≃ Y := standard_sphere_antipode_for_margin_disambiguation m
  let F : Y → simplicial_geometric_realization S.complex := S.toStandardSphere.symm
  have hsphere_nonempty :
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by positivity)
  let u₀ : Y := ⟨Classical.choose hsphere_nonempty, Classical.choose_spec hsphere_nonempty⟩
  have hvertex_nonempty : Nonempty S.Vertex := by
    by_contra h
    haveI : IsEmpty S.Vertex := not_nonempty_iff.mp h
    have hsum := (F u₀).property.2.1
    simpa using hsum
  have hcard : 0 < Fintype.card S.Vertex :=
    Fintype.card_pos_iff.mpr hvertex_nonempty
  let c : ℝ := 1 / (Fintype.card S.Vertex : ℝ)
  have hc : 0 < c := one_div_pos.mpr (by exact_mod_cast hcard)
  have hlarge : ∀ u : Y, ∃ i : S.Vertex, c ≤ (F u).1 i := by
    intro u
    by_contra h
    simp only [not_exists, not_le] at h
    let i₀ : S.Vertex := Classical.choice hvertex_nonempty
    have hlt : (∑ i, (F u).1 i) < ∑ _i : S.Vertex, c := by
      apply Finset.sum_lt_sum
      · intro i hi
        exact (h i).le
      · exact ⟨i₀, Finset.mem_univ i₀, h i₀⟩
    have hsumc : (∑ _i : S.Vertex, c) = 1 := by
      simp [c]
    rw [(F u).property.2.1, hsumc] at hlt
    exact (lt_irrefl 1 hlt)
  let pick : Y → S.Vertex := fun u => Classical.choose (hlarge u)
  have hpick : ∀ u : Y, c ≤ (F u).1 (pick u) := fun u =>
    Classical.choose_spec (hlarge u)
  have hAA : ∀ u : Y, A (A u) = u := by
    intro u
    ext
    simp [A, standard_sphere_antipode_for_margin_disambiguation]
  have hAne : ∀ u : Y, A u ≠ u := by
    intro u hu
    have hval : -u.1 = u.1 := congrArg Subtype.val hu
    have huzero : u.1 = 0 := by
      ext i
      have hi := congrArg (fun z : EuclideanSpace ℝ (Fin (m + 1)) => z i) hval
      simp only [PiLp.neg_apply, PiLp.zero_apply] at hi ⊢
      linarith
    have humem := u.2
    rw [Metric.mem_sphere, huzero, dist_self] at humem
    norm_num at humem
  have hFneg : ∀ u : Y, F (A u) = S.realizationAntipode (F u) := by
    intro u
    dsimp only [F]
    apply S.toStandardSphere.injective
    simp only [Homeomorph.apply_symm_apply]
    apply Subtype.ext
    change -u.1 = (S.toStandardSphere (S.realizationAntipode (S.toStandardSphere.symm u))).1
    rw [S.toStandardSphere_equivariant]
    simp
  let orbit : Y → Set Y := fun u => {u, A u}
  have horbit : ∀ u : Y, orbit (A u) = orbit u := by
    intro u
    ext z
    simp [orbit, hAA, or_comm]
  let repOf : Set Y → Y := fun B =>
    if hB : B.Nonempty then Classical.choose hB else u₀
  have hrep_mem : ∀ u : Y, repOf (orbit u) ∈ orbit u := by
    intro u
    simp only [repOf]
    split
    · exact Classical.choose_spec ‹(orbit u).Nonempty›
    · exfalso
      apply ‹¬(orbit u).Nonempty›
      exact ⟨u, by simp [orbit]⟩
  have hrep_neg : ∀ u : Y, repOf (orbit (A u)) = repOf (orbit u) := by
    intro u
    rw [horbit]
  have hrep_cases : ∀ u : Y, repOf (orbit u) = u ∨ repOf (orbit u) = A u := by
    intro u
    simpa [orbit] using hrep_mem u
  let q : Y → S.Vertex := fun u =>
    if u = repOf (orbit u) then pick u else S.antipode (pick (A u))
  have hqneg : ∀ u : Y, q (A u) = S.antipode (q u) := by
    intro u
    by_cases hu : u = repOf (orbit u)
    · have hne : A u ≠ repOf (orbit (A u)) := by
        rw [hrep_neg, ← hu]
        exact hAne u
      dsimp only [q]
      rw [if_neg hne, if_pos hu, hAA]
    · have hrep : repOf (orbit u) = A u :=
        (hrep_cases u).resolve_left (fun h => hu h.symm)
      have heq : A u = repOf (orbit (A u)) := by
        rw [hrep_neg, hrep]
      dsimp only [q]
      rw [if_pos heq, if_neg hu, S.antipode_involutive]
  have hqlarge : ∀ u : Y, c ≤ (F u).1 (q u) := by
    intro u
    by_cases hu : u = repOf (orbit u)
    · dsimp only [q]
      rw [if_pos hu]
      exact hpick u
    · have hcoord := S.realizationAntipode_coordinates (F u) (S.antipode (pick (A u)))
      rw [← hFneg u, S.antipode_involutive] at hcoord
      dsimp only [q]
      rw [if_neg hu, ← hcoord]
      exact hpick (A u)
  let W : Y → EuclideanSpace ℝ S.Vertex := fun u => WithLp.toLp 2 (F u).1
  have hWuniform : UniformContinuous W :=
    CompactSpace.uniformContinuous_of_continuous
      ((PiLp.continuous_toLp 2 (fun _ : S.Vertex => ℝ)).comp
        (continuous_subtype_val.comp S.toStandardSphere.symm.continuous))
  rcases (Metric.uniformContinuous_iff.mp hWuniform) (c / 2) (by positivity) with
    ⟨δ, hδ, hWδ⟩
  rcases (Metric.continuousAt_iff.mp Real.continuous_cos.continuousAt)
      (δ ^ 2 / 4) (by positivity) with ⟨η, hη, hcosη⟩
  let ε : ℝ := min (η / 2) (Real.pi / 4)
  have hεpos : 0 < ε := by simp [ε, hη, Real.pi_pos]
  have hεpi : ε < Real.pi / 2 := by
    have := Real.pi_pos
    simp only [ε]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine ⟨ε, hεpos, hεpi, q, ?_, hqneg⟩
  intro u
  let s : Finset S.Vertex := Finset.univ.filter fun i => (F u).1 i ≠ 0
  refine ⟨s, (F u).property.2.2, ?_⟩
  intro v huv
  have hunorm : ‖u.1‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using u.2
  have hvnorm : ‖v.1‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using v.2
  have hcos := InnerProductGeometry.cos_angle u.1 v.1
  rw [hunorm, hvnorm] at hcos
  norm_num at hcos
  have hnormsq := norm_sub_sq_real u.1 v.1
  rw [hunorm, hvnorm] at hnormsq
  have hangleη : dist (InnerProductGeometry.angle u.1 v.1) 0 < η := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (InnerProductGeometry.angle_nonneg _ _)]
    have hεη : ε ≤ η / 2 := min_le_left _ _
    nlinarith
  have hcosclose := hcosη hangleη
  rw [Real.cos_zero, Real.dist_eq] at hcosclose
  have hsq : ‖u.1 - v.1‖ ^ 2 < δ ^ 2 := by
    rw [hcos] at hcosclose
    nlinarith [neg_abs_le (inner ℝ u.1 v.1 - 1)]
  have huvδ : dist u v < δ := by
    change ‖u.1 - v.1‖ < δ
    exact (sq_lt_sq₀ (norm_nonneg _) hδ.le).mp hsq
  have hclose : dist (W u) (W v) < c / 2 := hWδ huvδ
  have hcoordinate : dist ((F v).1 (q v)) ((F u).1 (q v)) < c / 2 :=
    lt_of_le_of_lt (PiLp.dist_apply_le (W v) (W u) (q v))
      (by simpa [dist_comm] using hclose)
  have hdiff : (F v).1 (q v) - (F u).1 (q v) < c / 2 := by
    exact lt_of_le_of_lt (le_abs_self _) (by simpa [Real.dist_eq] using hcoordinate)
  have hpositive : 0 < (F u).1 (q v) := by nlinarith [hqlarge v]
  simp [s, hpositive.ne']

@[blueprint "lem:antipodal-simplicial-sphere-has-lower-margin-selector"
  (statement := /-- Let \(d\) be positive and satisfy \(d\leq m+1\).  Every antipodal simplicial \(m\)-sphere admits a positive-radius, antipodality-compatible face-local vertex selector on the unit sphere in \(\mathbb R^d\). -/)
  (proof := /-- Embed \(\mathbb R^d\) isometrically as the first factor of \(\mathbb R^d\times\mathbb R^{m+1-d}\), identify this product with \(\mathbb R^{m+1}\), and restrict the selector from \cref{lem:antipodal-simplicial-sphere-has-margin-selector}.  Linear isometries preserve both norms and angles and commute with negation, so face locality and antipodal equivariance pass to the restricted selector. -/)
  (title := /-- Restriction of a margin selector to an equator -/)
  (latexEnv := "lemma")]
lemma antipodal_simplicial_sphere_has_lower_margin_selector
    (d m : ℕ) (hd : 0 < d) (hdm : d ≤ m + 1)
    (S : antipodal_simplicial_sphere m) :
    ∃ ε : ℝ, 0 < ε ∧ ε < Real.pi / 2 ∧
      ∃ q : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → S.Vertex,
        (∀ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
          ∃ s : Finset S.Vertex, s ∈ S.complex.faces ∧
            ∀ v, InnerProductGeometry.angle u.1 v.1 ≤ ε → q v ∈ s) ∧
        ∀ u, q (⟨-u.1, by simpa [Metric.mem_sphere, dist_eq_norm] using u.2⟩) =
          S.antipode (q u) := by
  classical
  let k := m + 1 - d
  have hdk : d + k = m + 1 := by omega
  let E₁ : EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin k) :=
    LinearIsometry.inl ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin k))
  let E₁₂ : EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (d + k)) :=
    { toLinearMap :=
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d) (m := k)).symm.toLinearMap.comp
          E₁.toLinearMap
      norm_map' := fun x => by
        change ‖(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d) (m := k)).symm
          (x, 0)‖ = ‖x‖
        simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd] }
  let E₃ : EuclideanSpace ℝ (Fin (d + k)) →ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (m + 1)) :=
    LinearIsometryEquiv.toLinearIsometry
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr hdk))
  let E : EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
    E₃.comp E₁₂
  let eSphere : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 := fun u =>
    ⟨E u.1, by
      have hu : ‖u.1‖ = 1 := by
        simpa [Metric.mem_sphere, dist_eq_norm] using u.2
      simpa [Metric.mem_sphere, dist_eq_norm, hu]⟩
  have eneg : ∀ u, eSphere
      (⟨-u.1, by simpa [Metric.mem_sphere, dist_eq_norm] using u.2⟩) =
      standard_sphere_antipode_for_margin_disambiguation m (eSphere u) := by
    intro u
    apply Subtype.ext
    change E (-u.1) = -E u.1
    exact E.map_neg u.1
  rcases antipodal_simplicial_sphere_has_margin_selector m S with
    ⟨ε, hε, hεπ, q, hface, hq⟩
  refine ⟨ε, hε, hεπ, fun u => q (eSphere u), ?_, ?_⟩
  · intro u
    rcases hface (eSphere u) with ⟨s, hs, hlocal⟩
    refine ⟨s, hs, ?_⟩
    intro v huv
    apply hlocal (eSphere v)
    simpa [eSphere] using E.angle_map u.1 v.1 ▸ huv
  · intro u
    change q (eSphere
      (⟨-u.1, by simpa [Metric.mem_sphere, dist_eq_norm] using u.2⟩)) =
        S.antipode (q (eSphere u))
    rw [eneg, hq]

@[blueprint "lem:face-local-selector-gives-margin-disambiguator"
  (statement := /-- An equivariant vertex selector whose selected vertices on every angular cap lie in one realizable face induces a disambiguation of the corresponding margin classifiers.  Pullback through the selected labeled points does not increase either the VC dimension or the dual antipodal VC dimension. -/)
  (proof := /-- For each member \(h\) of the original class, define a concept that is positive at \(v\) exactly when \(h\) realizes the label attached to the selected vertex \(q(v)\).  Face realizability from \cref{def:mapped-face-antipodally-realizable} makes this concept positive on the cap about a center; equivariance of the selector and labeling makes it negative on the antipodal cap, which proves \cref{def:disambiguates}.  A shattered indexed family maps to a shattered family of selected domain points, and shattering forces this feature map to be injective.  A dually antipodally shattered family lifts to an injective family of original concepts; the selected label introduces only one simultaneous reversal.  The bounds therefore follow from \cref{def:vc-dimension-at-most, def:dual-antipodal-vc-dimension-at-most}. -/)
  (title := /-- From a face-local selector to a bounded disambiguator -/)
  (latexEnv := "lemma")]
lemma face_local_selector_gives_margin_disambiguator
    {X : Type} (H : binary_concept_class X) (a b n : ℤ) (m : ℕ)
    (S : antipodal_simplicial_sphere m) (f : S.Vertex → X × Bool)
    (hfaces : ∀ s : Finset S.Vertex, s ∈ S.complex.faces →
      @mapped_face_antipodally_realizable X S.Vertex S.vertexDecidableEq H f s)
    (fequiv : ∀ v, f (S.antipode v) = labeled_antipode (f v))
    (hvc : vc_dimension_at_most H a)
    (hdual : dual_antipodal_vc_dimension_at_most H b)
    (ε : ℝ) (q : integer_unit_sphere n → S.Vertex)
    (hlocal : ∀ u : integer_unit_sphere n,
      ∃ s : Finset S.Vertex, s ∈ S.complex.faces ∧
      ∀ v, InnerProductGeometry.angle u.1 v.1 ≤ ε → q v ∈ s)
    (qequiv : ∀ u, q (⟨-u.1,
      by simpa [Metric.mem_sphere, dist_eq_norm] using u.2⟩) = S.antipode (q u)) :
    ∃ G : binary_concept_class (integer_unit_sphere n),
      disambiguates G (margin_linear_partial_class n ε) ∧
        vc_dimension_at_most G a ∧ dual_antipodal_vc_dimension_at_most G b := by
  classical
  let g : (X → Bool) → integer_unit_sphere n → Bool := fun h v =>
    decide (h (f (q v)).1 = (f (q v)).2)
  let G : binary_concept_class (integer_unit_sphere n) := g '' H
  refine ⟨G, ?_, ?_, ?_⟩
  · rintro p ⟨u, rfl⟩
    rcases hlocal u with ⟨s, hs, hcap⟩
    rcases hfaces s hs with ⟨⟨h, hh, hreal⟩, hreverse⟩
    refine ⟨g h, ⟨h, hh, rfl⟩, ?_⟩
    intro v y hv
    unfold margin_partial_classifier at hv
    split at hv
    · have hvpos : q v ∈ s := hcap v (by assumption)
      have hhv : h (f (q v)).1 = (f (q v)).2 := (hreal (q v) hvpos).symm
      simp only [Option.some.injEq] at hv
      subst y
      simp [g, hhv]
    · split at hv
      · let av : integer_unit_sphere n :=
          ⟨-v.1, by simpa [Metric.mem_sphere, dist_eq_norm] using v.2⟩
        have hang : InnerProductGeometry.angle u.1 av.1 ≤ ε := by
          have heq : InnerProductGeometry.angle u.1 (-v.1) =
              InnerProductGeometry.angle (-u.1) v.1 := by
            simpa using InnerProductGeometry.angle_neg_neg (-u.1) v.1
          rw [show av.1 = -v.1 by rfl, heq]
          exact ‹InnerProductGeometry.angle (-u.1) v.1 ≤ ε›
        have havmem : q av ∈ s := hcap av hang
        have hqa : q av = S.antipode (q v) := by simpa [av] using qequiv v
        have hfv : f (q av) = labeled_antipode (f (q v)) := by
          rw [hqa, fequiv]
        have hhav : h (f (q av)).1 = (f (q av)).2 := (hreal (q av) havmem).symm
        have hnot : h (f (q v)).1 = !(f (q v)).2 := by
          simpa [hfv, labeled_antipode] using hhav
        simp only [Option.some.injEq] at hv
        subst y
        cases hlabel : (f (q v)).2 <;> simp [g, hlabel] at hnot ⊢ <;> assumption
      · contradiction
  · intro I _ points hpoints hshatters
    let x : I → X := fun i => (f (q (points i))).1
    let r : I → Bool := fun i => (f (q (points i))).2
    have hxinj : Function.Injective x := by
      intro i j hx
      by_contra hij
      let labels : I → Bool := fun k =>
        if k = i then true else if k = j then decide (r i ≠ r j) else false
      rcases hshatters labels with ⟨gh, ⟨h, hh, hgh⟩, hvals⟩
      subst gh
      have hi := hvals i
      have hj := hvals j
      have hji : j ≠ i := fun hji => hij hji.symm
      cases hri : r i <;> cases hrj : r j <;>
        simp [g, labels, x, r, hij, hji, hri, hrj, hx] at hi hj <;> simp_all
    apply hvc I x hxinj
    intro labels
    let labels' : I → Bool := fun i => decide (labels i = r i)
    rcases hshatters labels' with ⟨gh, ⟨h, hh, hgh⟩, hvals⟩
    subst gh
    refine ⟨h, hh, ?_⟩
    intro i
    have hi := hvals i
    cases hli : labels i <;> cases hri : r i <;>
      simp [g, labels', x, r, hli, hri] at hi ⊢ <;> assumption
  · intro I _ concepts hconcepts hshatters
    have hpre : ∀ i, ∃ h ∈ H, g h = concepts i := by
      intro i
      simpa [G] using hshatters.1 i
    let source : I → X → Bool := fun i => Classical.choose (hpre i)
    have hsource_mem : ∀ i, source i ∈ H := fun i => Classical.choose_spec (hpre i) |>.1
    have hsource_eq : ∀ i, g (source i) = concepts i := fun i =>
      Classical.choose_spec (hpre i) |>.2
    have hsource_inj : Function.Injective source := by
      intro i j hij
      apply hconcepts
      rw [← hsource_eq i, ← hsource_eq j, hij]
    apply hdual I source hsource_inj
    refine ⟨hsource_mem, ?_⟩
    intro labels
    rcases hshatters.2 labels with ⟨v, hv | hv⟩
    · refine ⟨(f (q v)).1, ?_⟩
      by_cases hr : (f (q v)).2 = true
      · left
        intro i
        have hi := hv i
        rw [← hsource_eq i] at hi
        simpa [g, hr] using hi
      · right
        intro i
        have hi := hv i
        rw [← hsource_eq i] at hi
        cases hli : labels i <;> cases hri : (f (q v)).2 <;>
          simp [g, hri, hli] at hr hi ⊢ <;> assumption
    · refine ⟨(f (q v)).1, ?_⟩
      by_cases hr : (f (q v)).2 = true
      · right
        intro i
        have hi := hv i
        rw [← hsource_eq i] at hi
        cases hli : labels i <;> simp [g, hr, hli] at hi ⊢ <;> assumption
      · left
        intro i
        have hi := hv i
        rw [← hsource_eq i] at hi
        cases hli : labels i <;> cases hri : (f (q v)).2 <;>
          simp [g, hri, hli] at hr hi ⊢ <;> assumption

@[blueprint "lem:spherical-class-gives-margin-disambiguation"
  (statement := /-- For all integers \(a,b,n\), if there exists a class with VC dimension at most \(a\), dual antipodal VC dimension at most \(b\), and simplicial spherical dimension at least \(n\), then, for some angular radius \(\varepsilon\) with \(0<\varepsilon<\pi/2\), the partial linear classifiers on the \(n\)-sphere have a disambiguation satisfying the same two upper bounds. -/)
  (proof := /-- Assume \cref{def:has-bounded-spherical-class}, witnessed by a domain \(X\), a class \(H\), the two stated dimension bounds, and the spherical-dimension lower bound.  If \(n\leq-1\), then \((n+1)_{\geq0}=0\), so \cref{def:integer-unit-sphere} is empty.  Take \(\varepsilon=\pi/4\) and the empty total class.  The partial margin class has no centers, hence the empty class satisfies \cref{def:disambiguates}; neither shattering predicate can hold, so both dimension bounds are vacuous.

  Suppose \(n\geq0\).  By \cref{def:simplicial-spherical-dimension-at-least, def:admits-simplicial-sphere}, choose \(m\in\mathbb N\) with \(n\leq m\), an antipodal simplicial \(m\)-sphere \(S\), and an equivariant vertex labeling whose every face is antipodally realizable by \(H\).  Put \(d=(n+1)_{\geq0}\).  Then \(0<d\leq m+1\).  Apply \cref{lem:antipodal-simplicial-sphere-has-lower-margin-selector} to obtain \(0<\varepsilon<\pi/2\) and an equivariant selector from the unit sphere in \(\mathbb R^d\) to the vertices of \(S\), with all vertices selected on each angular \(\varepsilon\)-cap contained in one face.  The hypotheses of \cref{lem:face-local-selector-gives-margin-disambiguator} now hold for \(H\), the chosen labeling, and this selector.  That lemma supplies a class disambiguating \cref{def:margin-linear-partial-class} with the original VC and dual antipodal VC upper bounds.  Together with the inequalities for \(\varepsilon\), this is exactly \cref{def:has-margin-disambiguation}. -/)
  (title := /-- From simplicial spherical dimension to a margin disambiguation -/)
  (latexEnv := "lemma")]
lemma spherical_class_gives_margin_disambiguation (a b n : ℤ) :
    has_bounded_spherical_class a b n →
      has_margin_disambiguation a b n := by
  classical
  rintro ⟨X, H, hvc, hdual, hsphere⟩
  by_cases hn : n ≤ -1
  · refine ⟨Real.pi / 4, by positivity, by nlinarith [Real.pi_pos], ∅, ?_, ?_, ?_⟩
    · rintro p ⟨u, rfl⟩
      have hfin : (n + 1).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
      have hu : u.1 = 0 := by
        ext i
        exact Fin.elim0 (Fin.cast hfin i)
      have hfalse : False := by
        have humem := u.2
        simp only [Metric.mem_sphere, hu, dist_self] at humem
        norm_num at humem
      exact hfalse.elim
    · intro I _ points hinjective hshatters
      rcases hshatters (fun _ => false) with ⟨h, hh, _⟩
      exact hh.elim
    · intro I _ concepts hinjective hshatters
      rcases hshatters.2 (fun _ => false) with ⟨u, hu⟩
      have hfin : (n + 1).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
      have huzero : u.1 = 0 := by
        ext i
        exact Fin.elim0 (Fin.cast hfin i)
      have humem := u.2
      simp only [Metric.mem_sphere, huzero, dist_self] at humem
      norm_num at humem
  · have hn0 : 0 ≤ n := by omega
    rcases hsphere with hsphere | ⟨m, hnm, hadmit⟩
    · omega
    · rcases hadmit with ⟨S, f, hfaces, fequiv⟩
      let d := (n + 1).toNat
      have hd : 0 < d := by
        dsimp only [d]
        exact Int.pos_iff_toNat_pos.mp (by omega)
      have hdm : d ≤ m + 1 := by
        dsimp only [d]
        omega
      rcases antipodal_simplicial_sphere_has_lower_margin_selector d m hd hdm S with
        ⟨ε, hε, hεπ, q, hlocal, qequiv⟩
      refine ⟨ε, hε, hεπ, ?_⟩
      exact face_local_selector_gives_margin_disambiguator H a b n m S f
        hfaces fequiv hvc hdual ε q hlocal qequiv

@[blueprint "def:is-finite-barycentric-subdivision"
  (statement := /-- Let \(K\) and \(L\) be finite abstract simplicial complexes on vertex sets \(V\) and \(W\), respectively, and let \(\phi\) be a bijection from \(W\) to the set of faces of \(K\).  The complex \(L\) is the barycentric subdivision of \(K\), relative to \(\phi\), if its faces are precisely the nonempty finite sets \(t\subseteq W\) for which \(\phi(v)\) and \(\phi(w)\) are comparable under inclusion for every \(v,w\in t\). -/)
  (title := /-- Finite barycentric subdivision -/)
  (latexEnv := "definition")]
def is_finite_barycentric_subdivision
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W)
    (vertexFace : W ≃ {s : Finset V // s ∈ K.faces}) : Prop :=
  ∀ t : Finset W,
    t ∈ L.faces ↔
      t.Nonempty ∧
        ∀ v ∈ t, ∀ w ∈ t,
          (vertexFace v).1 ⊆ (vertexFace w).1 ∨
            (vertexFace w).1 ⊆ (vertexFace v).1

@[blueprint "lem:finite-barycentric-subdivision-exists"
  (statement := /-- Let \(V\) be a type with decidable equality, and let \(K\) be a pre-abstract simplicial complex on \(V\). There exists a pre-abstract simplicial complex on the type of faces of \(K\) which, under the identity equivalence of that type, is a finite barycentric subdivision of \(K\) in the sense of \cref{def:is-finite-barycentric-subdivision}. -/)
  (proof := /-- Take the faces of the new complex to be the nonempty finite chains in the face poset of \(K\).  Every member of such a chain is a nonempty face of \(K\), and every nonempty subset of a finite chain is again a finite chain.  Thus these chains satisfy the nonemptiness and downward-closure axioms for an abstract simplicial complex.  Under the identity bijection from the new vertex set to the faces of \(K\), the resulting face condition is exactly \cref{def:is-finite-barycentric-subdivision}. -/)
  (title := /-- Existence of finite barycentric subdivisions -/)
  (latexEnv := "lemma")]
lemma finite_barycentric_subdivision_exists
    {V : Type*} [DecidableEq V]
    (K : PreAbstractSimplicialComplex V) :
    ∃ L : PreAbstractSimplicialComplex {s : Finset V // s ∈ K.faces},
      is_finite_barycentric_subdivision K L (Equiv.refl _) := by
  let L : PreAbstractSimplicialComplex {s : Finset V // s ∈ K.faces} :=
    ⟨{t | t.Nonempty ∧ ∀ v ∈ t, ∀ w ∈ t, v.1 ⊆ w.1 ∨ w.1 ⊆ v.1}, by
      simp only [IsRelLowerSet]
      aesop⟩
  refine ⟨L, ?_⟩
  intro t
  rfl

@[blueprint "lem:barycentric-subdivision-realization-homeomorphism"
  (statement := /-- Let \(K\) and \(L\) be finite abstract simplicial complexes on vertex sets \(V\) and \(W\), respectively, and let \(\phi:W\to\{A:A\in K\}\) be a bijection for which \(L\) is the barycentric subdivision of \(K\) in the sense of \cref{def:is-finite-barycentric-subdivision}.  There exists a homeomorphism \(F:|L|\to |K|\) equal to the affine extension of the face-barycenter map.  Explicitly, for every \(x\in |L|\) and \(v\in V\),
  \[
  F(x)_v=\sum_{w\in W:\,v\in\phi(w)}\frac{x_w}{|\phi(w)|}.
  \] -/)
  (proof := /-- For each vertex \(w\) of \(L\), write \(A_w\) for its corresponding nonempty face of \(K\), and define the affine barycenter map by
  \[
  B(a)_v=\sum_{w:\,v\in A_w}\frac{a_w}{|A_w|}.
  \]
  Its coordinates are nonnegative, and interchanging the two finite sums shows that their sum is \(\sum_w a_w\).  If the support of \(a\) is a face of \(L\), then \cref{def:is-finite-barycentric-subdivision} makes the faces \(A_w\) in that support a finite chain.  Choose its largest member \(A_{w_{\max}}\).  Every nonzero coordinate of \(B(a)\) lies in \(A_{w_{\max}}\), while the positive coefficient of \(w_{\max}\) makes every coordinate on \(A_{w_{\max}}\) nonzero.  Thus the support of \(B(a)\) is exactly \(A_{w_{\max}}\), so \(B\) takes values in the realization from \cref{def:simplicial-geometric-realization}.

  We next prove uniqueness of chain coordinates.  For a nonnegative coefficient vector \(a\) with chain support and largest face \(A_{w_{\max}}\), every coordinate of \(B(a)\) on \(A_{w_{\max}}\) is at least \(a_{w_{\max}}/|A_{w_{\max}}|\).  If there are smaller supporting faces, choose the largest of them and then a vertex of \(A_{w_{\max}}\) outside that proper subface; if there are none, choose any vertex of \(A_{w_{\max}}\).  At this vertex equality holds.  Consequently
  \[
  a_{w_{\max}}=|A_{w_{\max}}|
    \min_{v\in A_{w_{\max}}}B(a)_v.
  \]
  Equal images therefore have the same largest face and the same coefficient there.  Removing this coefficient and inducting on the total support cardinality proves injectivity.

  For surjectivity, let \(y\) be a point of the realization of \(K\), let \(A\) be its support, and let \(m=\min_{v\in A}y_v>0\).  Subtract \(m\) from every coordinate on \(A\), leaving zero outside \(A\).  The resulting nonnegative vector has support a proper subface of \(A\).  Induction on \(|A|\) represents it by a chain of faces contained in that proper subface.  Adjoining the face \(A\) with coefficient \(|A|m\) preserves the chain condition and reconstructs \(y\).  The preceding mass identity shows that these coefficients sum to \(1\), giving a point of the realization of \(L\).

  Each coordinate of \(B\) is a finite sum of constant multiples of coordinate projections, hence \(B\) is continuous.  Finally, the realization of \(L\) is the finite union, over its faces, of the closed simplices cut out inside the compact cube \([0,1]^W\); it is therefore compact.  The realization of \(K\), as a subspace of \(\mathbb{R}^V\), is Hausdorff.  Thus the continuous bijection \(B\) from the compact source to the Hausdorff target is a homeomorphism, and its defining formula is the asserted coordinate identity. -/)
  (title := /-- Realizations are preserved by barycentric subdivision -/)
  (latexEnv := "lemma")]
lemma barycentric_subdivision_realization_homeomorphism
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W)
    (vertexFace : W ≃ {s : Finset V // s ∈ K.faces})
    (hsubdivision : is_finite_barycentric_subdivision K L vertexFace) :
    ∃ realizationMap :
        simplicial_geometric_realization L ≃ₜ
          simplicial_geometric_realization K,
      ∀ x v, (realizationMap x).1 v =
        ∑ w : W, if v ∈ (vertexFace w).1 then
          x.1 w / ((vertexFace w).1.card : ℝ) else 0 := by
  classical
  let bw : (W → ℝ) → V → ℝ :=
    fun a v => ∑ w : W, if v ∈ (vertexFace w).1 then
      a w / ((vertexFace w).1.card : ℝ) else 0
  have hcard (w : W) : 0 < ((vertexFace w).1.card : ℝ) := by
    exact_mod_cast (K.isRelLowerSet_faces (vertexFace w).property).1.card_pos
  have hbnonneg (a : W → ℝ) (ha : ∀ w, 0 ≤ a w) :
      ∀ v, 0 ≤ bw a v := by
    intro v
    dsimp [bw]
    apply Finset.sum_nonneg
    intro w hw
    split_ifs
    · exact div_nonneg (ha w) (le_of_lt (hcard w))
    · exact le_rfl
  have hmass (a : W → ℝ) : (∑ v, bw a v) = ∑ w, a w := by
    calc
      (∑ v, bw a v) =
          ∑ v, ∑ w : W, if v ∈ (vertexFace w).1 then
            a w / ((vertexFace w).1.card : ℝ) else 0 := by rfl
      _ = ∑ w : W, ∑ v, if v ∈ (vertexFace w).1 then
            a w / ((vertexFace w).1.card : ℝ) else 0 := Finset.sum_comm
      _ = ∑ w : W, a w := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [← Finset.sum_filter]
        simp only [Finset.filter_mem_eq_inter]
        rw [Finset.univ_inter]
        rw [Finset.sum_const, nsmul_eq_mul]
        field_simp [ne_of_gt (hcard w)]
  have hmax (a : W → ℝ) (ha : ∀ w, 0 ≤ a w)
      (hane : (Finset.univ.filter fun w => a w ≠ 0).Nonempty)
      (hachain : ∀ v ∈ Finset.univ.filter (fun w => a w ≠ 0),
        ∀ w ∈ Finset.univ.filter (fun u => a u ≠ 0),
          (vertexFace v).1 ⊆ (vertexFace w).1 ∨
            (vertexFace w).1 ⊆ (vertexFace v).1) :
      ∃ wm ∈ Finset.univ.filter (fun w => a w ≠ 0),
        (∀ w ∈ Finset.univ.filter (fun u => a u ≠ 0),
          (vertexFace w).1 ⊆ (vertexFace wm).1) ∧
        (Finset.univ.filter fun v => bw a v ≠ 0) =
          (vertexFace wm).1 := by
    let sa := Finset.univ.filter fun w => a w ≠ 0
    obtain ⟨wm, hwm⟩ :=
      sa.exists_maximalFor (fun w => (vertexFace w).1) hane
    have hgreat : ∀ w ∈ sa,
        (vertexFace w).1 ⊆ (vertexFace wm).1 := by
      intro w hw
      rcases hachain w hw wm hwm.1 with h | h
      · exact h
      · exact hwm.2 hw h
    refine ⟨wm, hwm.1, hgreat, Finset.Subset.antisymm ?_ ?_⟩
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      by_contra hvmax
      apply hv
      dsimp [bw]
      apply Finset.sum_eq_zero
      intro w hw
      by_cases haw : a w = 0
      · simp [haw]
      · have hwmem : w ∈ sa := by simp [sa, haw]
        have hvw : v ∉ (vertexFace w).1 := fun hvw =>
          hvmax (hgreat w hwmem hvw)
        simp [hvw]
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hapos : 0 < a wm :=
        lt_of_le_of_ne (ha wm) (Ne.symm (by simpa [sa] using hwm.1))
      have hterm : 0 < a wm / ((vertexFace wm).1.card : ℝ) :=
        div_pos hapos (hcard wm)
      have hle : a wm / ((vertexFace wm).1.card : ℝ) ≤ bw a v := by
        let term : W → ℝ := fun w =>
          if v ∈ (vertexFace w).1 then
            a w / ((vertexFace w).1.card : ℝ) else 0
        have ht : ∀ w ∈ Finset.univ, 0 ≤ term w := by
          intro w hw
          dsimp [term]
          split_ifs
          · exact div_nonneg (ha w) (le_of_lt (hcard w))
          · exact le_rfl
        have hh := Finset.single_le_sum ht (Finset.mem_univ wm)
        simpa [bw, term, hv] using hh
      exact ne_of_gt (lt_of_lt_of_le hterm hle)
  have hcoefficient (a : W → ℝ) (ha : ∀ w, 0 ≤ a w)
      (hachain : ∀ v ∈ Finset.univ.filter (fun w => a w ≠ 0),
        ∀ w ∈ Finset.univ.filter (fun u => a u ≠ 0),
          (vertexFace v).1 ⊆ (vertexFace w).1 ∨
            (vertexFace w).1 ⊆ (vertexFace v).1)
      (wm : W) (hwm : wm ∈ Finset.univ.filter (fun w => a w ≠ 0))
      (hgreat : ∀ w ∈ Finset.univ.filter (fun u => a u ≠ 0),
        (vertexFace w).1 ⊆ (vertexFace wm).1) :
      a wm = ((vertexFace wm).1.card : ℝ) *
        (((vertexFace wm).1.image (bw a)).min'
          ((K.isRelLowerSet_faces (vertexFace wm).property).1.image (bw a))) := by
    let sa := Finset.univ.filter fun w => a w ≠ 0
    let A := (vertexFace wm).1
    have hA : A.Nonempty :=
      (K.isRelLowerSet_faces (vertexFace wm).property).1
    let c := a wm / (A.card : ℝ)
    have hc_le (v : V) (hv : v ∈ A) : c ≤ bw a v := by
      let term : W → ℝ := fun w =>
        if v ∈ (vertexFace w).1 then
          a w / ((vertexFace w).1.card : ℝ) else 0
      have ht : ∀ w ∈ Finset.univ, 0 ≤ term w := by
        intro w hw
        dsimp [term]
        split_ifs
        · exact div_nonneg (ha w) (le_of_lt (hcard w))
        · exact le_rfl
      have hh := Finset.single_le_sum ht (Finset.mem_univ wm)
      simpa [bw, term, c, A, hv] using hh
    have hcmin : c ≤ (A.image (bw a)).min' (hA.image (bw a)) := by
      apply Finset.le_min'
      intro z hz
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
      exact hc_le v hv
    have hspecial : ∃ v ∈ A, bw a v = c := by
      by_cases he : (sa.erase wm).Nonempty
      · obtain ⟨w₂, hw₂⟩ :=
          (sa.erase wm).exists_maximalFor
            (fun w => (vertexFace w).1) he
        have hgreat₂ : ∀ w ∈ sa.erase wm,
            (vertexFace w).1 ⊆ (vertexFace w₂).1 := by
          intro w hw
          have hwsa : w ∈ sa := Finset.mem_of_mem_erase hw
          have hw₂sa : w₂ ∈ sa := Finset.mem_of_mem_erase hw₂.1
          rcases hachain w hwsa w₂ hw₂sa with h | h
          · exact h
          · exact hw₂.2 hw h
        have hw₂sub : (vertexFace w₂).1 ⊆ A :=
          hgreat w₂ (Finset.mem_of_mem_erase hw₂.1)
        have hw₂ne : (vertexFace w₂).1 ≠ A := by
          intro h
          have : w₂ = wm := vertexFace.injective (Subtype.ext h)
          exact (Finset.ne_of_mem_erase hw₂.1) this
        obtain ⟨v, hvA, hv₂⟩ :=
          Finset.exists_of_ssubset
            (Finset.ssubset_iff_subset_ne.mpr ⟨hw₂sub, hw₂ne⟩)
        refine ⟨v, hvA, ?_⟩
        dsimp [bw]
        rw [Finset.sum_eq_single wm]
        · simp [hvA, c, A]
        · intro w hw hne
          by_cases haw : a w = 0
          · simp [haw]
          · have hwsa : w ∈ sa := by simp [sa, haw]
            have hwerase : w ∈ sa.erase wm :=
              Finset.mem_erase.mpr ⟨hne, hwsa⟩
            have hvw : v ∉ (vertexFace w).1 := fun hvw =>
              hv₂ (hgreat₂ w hwerase hvw)
            simp [hvw]
        · intro h
          exact (h (Finset.mem_univ wm)).elim
      · rw [Finset.not_nonempty_iff_eq_empty] at he
        obtain ⟨v, hvA⟩ := hA
        refine ⟨v, hvA, ?_⟩
        dsimp [bw]
        rw [Finset.sum_eq_single wm]
        · simp [hvA, c, A]
        · intro w hw hne
          have haw : a w = 0 := by
            by_contra haw
            have hwsa : w ∈ sa := by simp [sa, haw]
            have : w ∈ sa.erase wm :=
              Finset.mem_erase.mpr ⟨hne, hwsa⟩
            rw [he] at this
            simpa using this
          simp [haw]
        · intro h
          exact (h (Finset.mem_univ wm)).elim
    obtain ⟨v, hvA, hv⟩ := hspecial
    have hminc : (A.image (bw a)).min' (hA.image (bw a)) ≤ c := by
      rw [← hv]
      apply Finset.min'_le
      exact Finset.mem_image.mpr ⟨v, hvA, rfl⟩
    have hc : c = (A.image (bw a)).min' (hA.image (bw a)) :=
      le_antisymm hcmin hminc
    rw [← hc]
    dsimp [c, A]
    field_simp [ne_of_gt (hcard wm)]
  have hbremove (a : W → ℝ) (wm : W) (v : V) :
      bw (fun w => if w = wm then 0 else a w) v =
        bw a v - (if v ∈ (vertexFace wm).1 then
          a wm / ((vertexFace wm).1.card : ℝ) else 0) := by
    let f : W → ℝ := fun w => if v ∈ (vertexFace w).1 then
      a w / ((vertexFace w).1.card : ℝ) else 0
    let g : W → ℝ := fun w => if v ∈ (vertexFace w).1 then
      (if w = wm then 0 else a w) /
        ((vertexFace w).1.card : ℝ) else 0
    change (∑ w : W, g w) = (∑ w : W, f w) - f wm
    calc
      (∑ w, g w) = ∑ w ∈ Finset.univ.erase wm, g w := by
        rw [← Finset.sum_erase_add Finset.univ g (Finset.mem_univ wm)]
        simp [g]
      _ = ∑ w ∈ Finset.univ.erase wm, f w := by
        apply Finset.sum_congr rfl
        intro w hw
        have hne : w ≠ wm := (Finset.mem_erase.mp hw).1
        simp [f, g, hne]
      _ = (∑ w, f w) - f wm :=
        Finset.sum_erase_eq_sub (f := f) (Finset.mem_univ wm)
  have hbinjective (a b : W → ℝ)
      (ha : ∀ w, 0 ≤ a w) (hb : ∀ w, 0 ≤ b w)
      (hca : ∀ v ∈ Finset.univ.filter (fun w => a w ≠ 0),
        ∀ w ∈ Finset.univ.filter (fun u => a u ≠ 0),
          (vertexFace v).1 ⊆ (vertexFace w).1 ∨
            (vertexFace w).1 ⊆ (vertexFace v).1)
      (hcb : ∀ v ∈ Finset.univ.filter (fun w => b w ≠ 0),
        ∀ w ∈ Finset.univ.filter (fun u => b u ≠ 0),
          (vertexFace v).1 ⊆ (vertexFace w).1 ∨
            (vertexFace w).1 ⊆ (vertexFace v).1)
      (hab : bw a = bw b) : a = b := by
    let sa := Finset.univ.filter fun w => a w ≠ 0
    let sb := Finset.univ.filter fun w => b w ≠ 0
    generalize hN : sa.card + sb.card = N
    induction N using Nat.strong_induction_on generalizing a b with
    | h N ih =>
      by_cases hane : sa.Nonempty
      · by_cases hbne : sb.Nonempty
        · obtain ⟨wa, hwa, hagreat, hasupp⟩ :=
            hmax a ha hane hca
          obtain ⟨wb, hwb, hbgreat, hbsupp⟩ :=
            hmax b hb hbne hcb
          have hsuppEq :
              (Finset.univ.filter fun v => bw a v ≠ 0) =
                Finset.univ.filter (fun v => bw b v ≠ 0) := by
            simp [hab]
          have hfaces : (vertexFace wa).1 = (vertexFace wb).1 :=
            hasupp.symm.trans (hsuppEq.trans hbsupp)
          have hwab : wa = wb :=
            vertexFace.injective (Subtype.ext hfaces)
          subst wb
          have hcoeff : a wa = b wa := by
            rw [hcoefficient a ha hca wa hwa hagreat]
            rw [hcoefficient b hb hcb wa hwb hbgreat]
            rw [hab]
          let a' : W → ℝ := fun w => if w = wa then 0 else a w
          let b' : W → ℝ := fun w => if w = wa then 0 else b w
          have ha' : ∀ w, 0 ≤ a' w := by
            intro w
            simp only [a']
            split_ifs
            · exact le_rfl
            · exact ha w
          have hb' : ∀ w, 0 ≤ b' w := by
            intro w
            simp only [b']
            split_ifs
            · exact le_rfl
            · exact hb w
          have hsa' :
              (Finset.univ.filter fun w => a' w ≠ 0) = sa.erase wa := by
            ext w
            simp [a', sa]
          have hsb' :
              (Finset.univ.filter fun w => b' w ≠ 0) = sb.erase wa := by
            ext w
            simp [b', sb]
          have hca' : ∀ v ∈ Finset.univ.filter (fun w => a' w ≠ 0),
              ∀ w ∈ Finset.univ.filter (fun u => a' u ≠ 0),
                (vertexFace v).1 ⊆ (vertexFace w).1 ∨
                  (vertexFace w).1 ⊆ (vertexFace v).1 := by
            intro v hv w hw
            apply hca v
            · rw [hsa'] at hv
              exact Finset.mem_of_mem_erase hv
            · rw [hsa'] at hw
              exact Finset.mem_of_mem_erase hw
          have hcb' : ∀ v ∈ Finset.univ.filter (fun w => b' w ≠ 0),
              ∀ w ∈ Finset.univ.filter (fun u => b' u ≠ 0),
                (vertexFace v).1 ⊆ (vertexFace w).1 ∨
                  (vertexFace w).1 ⊆ (vertexFace v).1 := by
            intro v hv w hw
            apply hcb v
            · rw [hsb'] at hv
              exact Finset.mem_of_mem_erase hv
            · rw [hsb'] at hw
              exact Finset.mem_of_mem_erase hw
          have hab' : bw a' = bw b' := by
            funext v
            rw [show a' = (fun w => if w = wa then 0 else a w) from rfl]
            rw [show b' = (fun w => if w = wa then 0 else b w) from rfl]
            rw [hbremove, hbremove, hab, hcoeff]
          have hlt :
              (Finset.univ.filter fun w => a' w ≠ 0).card +
                (Finset.univ.filter fun w => b' w ≠ 0).card < N := by
            have hwa_sa : wa ∈ sa := hwa
            have hwb_sb : wa ∈ sb := hwb
            calc
              (Finset.univ.filter fun w => a' w ≠ 0).card +
                    (Finset.univ.filter fun w => b' w ≠ 0).card =
                  (sa.erase wa).card + (sb.erase wa).card := by
                    rw [hsa', hsb']
              _ < sa.card + sb.card := Nat.add_lt_add
                    (Finset.card_erase_lt_of_mem hwa_sa)
                    (Finset.card_erase_lt_of_mem hwb_sb)
              _ = N := hN
          have habfun : a' = b' :=
            ih _ hlt a' b' ha' hb' hca' hcb' hab' rfl
          funext w
          by_cases hwaeq : w = wa
          · simpa [hwaeq] using hcoeff
          · have := congrFun habfun w
            simpa [a', b', hwaeq] using this
        · rw [Finset.not_nonempty_iff_eq_empty] at hbne
          have hbzero : ∀ w, b w = 0 := by
            intro w
            have : w ∉ sb := by rw [hbne]; simp
            simpa [sb] using this
          have hbmap : bw b = 0 := by
            funext v
            simp [bw, hbzero]
          obtain ⟨wa, hwa, hagreat, hasupp⟩ :=
            hmax a ha hane hca
          have : (Finset.univ.filter fun v => bw a v ≠ 0).Nonempty := by
            rw [hasupp]
            exact (K.isRelLowerSet_faces (vertexFace wa).property).1
          rw [hab, hbmap] at this
          simpa using this
      · rw [Finset.not_nonempty_iff_eq_empty] at hane
        have hazero : ∀ w, a w = 0 := by
          intro w
          have : w ∉ sa := by rw [hane]; simp
          simpa [sa] using this
        have hamap : bw a = 0 := by
          funext v
          simp [bw, hazero]
        by_cases hbne : sb.Nonempty
        · obtain ⟨wb, hwb, hbgreat, hbsupp⟩ :=
            hmax b hb hbne hcb
          have : (Finset.univ.filter fun v => bw b v ≠ 0).Nonempty := by
            rw [hbsupp]
            exact (K.isRelLowerSet_faces (vertexFace wb).property).1
          rw [← hab, hamap] at this
          simpa using this
        · rw [Finset.not_nonempty_iff_eq_empty] at hbne
          have hbzero : ∀ w, b w = 0 := by
            intro w
            have : w ∉ sb := by rw [hbne]; simp
            simpa [sb] using this
          funext w
          rw [hazero w, hbzero w]
  have hbadd (a b : W → ℝ) :
      bw (fun w => a w + b w) = fun v => bw a v + bw b v := by
    funext v
    dsimp [bw]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    split_ifs <;> ring
  have hbbasis (q : ℝ) (wm : W) (v : V) :
      bw (fun w => if w = wm then q else 0) v =
        if v ∈ (vertexFace wm).1 then
          q / ((vertexFace wm).1.card : ℝ) else 0 := by
    dsimp [bw]
    rw [Finset.sum_eq_single wm]
    · simp
    · intro w hw hne
      simp [hne]
    · intro h
      exact (h (Finset.mem_univ wm)).elim
  have hrepresent (y : V → ℝ) (hy : ∀ v, 0 ≤ y v)
      (hyface : (Finset.univ.filter fun v => y v ≠ 0) ∈ K.faces) :
      ∃ a : W → ℝ,
        (∀ w, 0 ≤ a w) ∧
        (∀ v ∈ Finset.univ.filter (fun w => a w ≠ 0),
          ∀ w ∈ Finset.univ.filter (fun u => a u ≠ 0),
            (vertexFace v).1 ⊆ (vertexFace w).1 ∨
              (vertexFace w).1 ⊆ (vertexFace v).1) ∧
        bw a = y ∧
        ∀ w ∈ Finset.univ.filter (fun u => a u ≠ 0),
          (vertexFace w).1 ⊆
            Finset.univ.filter (fun v => y v ≠ 0) := by
    let A := Finset.univ.filter fun v => y v ≠ 0
    generalize hN : A.card = N
    induction N using Nat.strong_induction_on generalizing y with
    | h N ih =>
      have hA : A.Nonempty := (K.isRelLowerSet_faces hyface).1
      let values := A.image y
      have hvalues : values.Nonempty := hA.image y
      let m := values.min' hvalues
      obtain ⟨vmin, hvminA, hvmin⟩ :=
        Finset.mem_image.mp (Finset.min'_mem values hvalues)
      have hmpos : 0 < m := by
        have hvne : y vmin ≠ 0 := by
          simpa [A] using hvminA
        change 0 < values.min' hvalues
        rw [← hvmin]
        exact lt_of_le_of_ne (hy vmin) (Ne.symm hvne)
      have hmle (v : V) (hv : v ∈ A) : m ≤ y v := by
        apply Finset.min'_le
        exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
      let y' : V → ℝ := fun v => if v ∈ A then y v - m else 0
      have hy' : ∀ v, 0 ≤ y' v := by
        intro v
        dsimp [y']
        split_ifs with hv
        · linarith [hmle v hv]
        · exact le_rfl
      let A' := Finset.univ.filter fun v => y' v ≠ 0
      have hA'sub : A' ⊆ A := by
        intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, A'] at hv
        by_contra hvA
        exact hv (by simp [y', hvA])
      have hvmin_not : vmin ∉ A' := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, A']
        simp [y', hvminA, hvmin, m]
      have hA'ne : A' ≠ A := by
        intro heq
        exact hvmin_not (heq ▸ hvminA)
      have hA'lt : A'.card < A.card :=
        Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.mpr ⟨hA'sub, hA'ne⟩)
      obtain ⟨a', ha', hchain', hmap', hinv'⟩ :
          ∃ a' : W → ℝ,
            (∀ w, 0 ≤ a' w) ∧
            (∀ v ∈ Finset.univ.filter (fun w => a' w ≠ 0),
              ∀ w ∈ Finset.univ.filter (fun u => a' u ≠ 0),
                (vertexFace v).1 ⊆ (vertexFace w).1 ∨
                  (vertexFace w).1 ⊆ (vertexFace v).1) ∧
            bw a' = y' ∧
            ∀ w ∈ Finset.univ.filter (fun u => a' u ≠ 0),
              (vertexFace w).1 ⊆ A' := by
        by_cases hA'nonempty : A'.Nonempty
        · have hA'face : A' ∈ K.faces :=
            (K.isRelLowerSet_faces hyface).2 hA'sub hA'nonempty
          exact ih A'.card (by omega) y' hy' hA'face rfl
        · rw [Finset.not_nonempty_iff_eq_empty] at hA'nonempty
          refine ⟨fun _ => 0, by simp, ?_, ?_, ?_⟩
          · simp
          · funext v
            have : y' v = 0 := by
              by_contra hv
              have : v ∈ A' := by simp [A', hv]
              rw [hA'nonempty] at this
              simpa using this
            simp [bw, this]
          · simp
      let wA : W := vertexFace.symm ⟨A, hyface⟩
      have hfacewA : (vertexFace wA).1 = A := by
        simp [wA]
      have ha'wA : a' wA = 0 := by
        by_contra hne
        have hwmem :
            wA ∈ Finset.univ.filter (fun u => a' u ≠ 0) := by
          simp [hne]
        have hAsub : A ⊆ A' := by
          rw [← hfacewA]
          exact hinv' wA hwmem
        exact hA'ne (Finset.Subset.antisymm hA'sub hAsub)
      let q : ℝ := (A.card : ℝ) * m
      have hqpos : 0 < q :=
        mul_pos (by exact_mod_cast hA.card_pos) hmpos
      let basis : W → ℝ := fun w => if w = wA then q else 0
      let a : W → ℝ := fun w => a' w + basis w
      have ha : ∀ w, 0 ≤ a w := by
        intro w
        exact add_nonneg (ha' w) (by
          dsimp [basis]
          split_ifs
          · exact le_of_lt hqpos
          · exact le_rfl)
      have hsupp :
          (Finset.univ.filter fun w => a w ≠ 0) =
            insert wA (Finset.univ.filter fun w => a' w ≠ 0) := by
        ext w
        by_cases hw : w = wA
        · subst w
          simp [a, basis, ha'wA, ne_of_gt hqpos]
        · simp [a, basis, hw, ha' w]
      have hchain : ∀ v ∈ Finset.univ.filter (fun w => a w ≠ 0),
          ∀ w ∈ Finset.univ.filter (fun u => a u ≠ 0),
            (vertexFace v).1 ⊆ (vertexFace w).1 ∨
              (vertexFace w).1 ⊆ (vertexFace v).1 := by
        intro v hv w hw
        rw [hsupp] at hv hw
        rcases Finset.mem_insert.mp hv with rfl | hv
        · right
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact Finset.Subset.rfl
          · rw [hfacewA]
            exact hA'sub.trans' (hinv' w hw)
        · rcases Finset.mem_insert.mp hw with rfl | hw
          · left
            rw [hfacewA]
            exact hA'sub.trans' (hinv' v hv)
          · exact hchain' v hv w hw
      have hmap : bw a = y := by
        rw [show a = (fun w => a' w + basis w) from rfl, hbadd]
        funext v
        rw [hmap']
        change y' v + bw basis v = y v
        rw [show basis = (fun w => if w = wA then q else 0) from rfl]
        rw [hbbasis]
        by_cases hvA : v ∈ A
        · simp [y', hvA, hfacewA, q]
          have hAcard : (A.card : ℝ) ≠ 0 := by
            exact_mod_cast hA.card_ne_zero
          field_simp [hAcard]
          ring
        · have hyv : y v = 0 := by
            by_contra hne
            exact hvA (by simp [A, hne])
          simp [y', hvA, hfacewA, hyv]
      refine ⟨a, ha, hchain, hmap, ?_⟩
      intro w hw
      rw [hsupp] at hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rw [hfacewA]
      · exact (hinv' w hw).trans hA'sub
  have hFface (x : simplicial_geometric_realization L) :
      (Finset.univ.filter fun v => bw x.1 v ≠ 0) ∈ K.faces := by
    have hx := (hsubdivision
      (Finset.univ.filter fun w => x.1 w ≠ 0)).mp x.property.2.2
    obtain ⟨wm, hwm, hgreat, hsupp⟩ :=
      hmax x.1 x.property.1 hx.1 hx.2
    rw [hsupp]
    exact (vertexFace wm).property
  let F : simplicial_geometric_realization L →
      simplicial_geometric_realization K := fun x =>
    ⟨bw x.1, hbnonneg x.1 x.property.1,
      (hmass x.1).trans x.property.2.1, hFface x⟩
  have hFinjective : Function.Injective F := by
    intro x z hxz
    apply Subtype.ext
    have hcx := (hsubdivision
      (Finset.univ.filter fun w => x.1 w ≠ 0)).mp x.property.2.2
    have hcz := (hsubdivision
      (Finset.univ.filter fun w => z.1 w ≠ 0)).mp z.property.2.2
    apply hbinjective x.1 z.1 x.property.1 z.property.1 hcx.2 hcz.2
    exact congrArg Subtype.val hxz
  have hFsurjective : Function.Surjective F := by
    intro y
    obtain ⟨a, ha, hchain, hmap, hinv⟩ :=
      hrepresent y.1 y.property.1 y.property.2.2
    have hasum : (∑ w, a w) = 1 := by
      rw [← hmass a, hmap]
      exact y.property.2.1
    have hane :
        (Finset.univ.filter fun w => a w ≠ 0).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      have hazero : ∀ w, a w = 0 := by
        intro w
        have : w ∉ Finset.univ.filter (fun u => a u ≠ 0) := by
          rw [h]
          simp
        simpa using this
      have : (∑ w, a w) = 0 := by simp [hazero]
      linarith
    have haface :
        (Finset.univ.filter fun w => a w ≠ 0) ∈ L.faces :=
      (hsubdivision _).mpr ⟨hane, hchain⟩
    let x : simplicial_geometric_realization L :=
      ⟨a, ha, hasum, haface⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hmap
  have hFcontinuous : Continuous F := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro v
    dsimp [F, bw]
    apply continuous_finset_sum
    intro w hw
    split_ifs
    · exact ((continuous_apply w).comp continuous_subtype_val).div_const _
    · exact continuous_const
  let cube : Set (W → ℝ) :=
    Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1)
  let C (s : Finset W) : Set (W → ℝ) :=
    cube ∩ ({a | (∑ w, a w) = 1} ∩
      {a | ∀ w ∈ Finset.univ \ s, a w = 0})
  have hcube : IsCompact cube := by
    exact isCompact_Icc
  have hsumclosed : IsClosed {a : W → ℝ | (∑ w, a w) = 1} := by
    apply isClosed_eq
    · apply continuous_finset_sum
      intro w hw
      exact continuous_apply w
    · exact continuous_const
  have hzeroClosed (t : Finset W) :
      IsClosed {a : W → ℝ | ∀ w ∈ t, a w = 0} := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert w t hwt ih =>
        simpa only [Finset.forall_mem_insert, Set.setOf_and] using
          (isClosed_eq (continuous_apply w) continuous_const).inter ih
  have hCcompact (s : Finset W) : IsCompact (C s) := by
    exact hcube.inter_right (hsumclosed.inter (hzeroClosed _))
  let faceFinset : Finset (Finset W) :=
    Finset.univ.filter fun s => s ∈ L.faces
  let R : Set (W → ℝ) :=
    {a | (∀ w, 0 ≤ a w) ∧ (∑ w, a w) = 1 ∧
      (Finset.univ.filter fun w => a w ≠ 0) ∈ L.faces}
  have hRunion : R = ⋃ s ∈ faceFinset, C s := by
    ext a
    constructor
    · intro haR
      have ha := haR
      change (∀ w, 0 ≤ a w) ∧ (∑ w, a w) = 1 ∧
        (Finset.univ.filter fun w => a w ≠ 0) ∈ L.faces at ha
      let s := Finset.univ.filter fun w => a w ≠ 0
      apply Set.mem_iUnion.2
      refine ⟨s, Set.mem_iUnion.2 ?_⟩
      refine ⟨by simp [faceFinset, s, ha.2.2], ?_⟩
      change a ∈ cube ∩ ({a | (∑ w, a w) = 1} ∩
        {a | ∀ w ∈ Finset.univ \ s, a w = 0})
      refine ⟨?_, ha.2.1, ?_⟩
      · constructor
        · exact ha.1
        · intro w
          have hle := Finset.single_le_sum
            (fun u (_ : u ∈ Finset.univ) => ha.1 u)
            (Finset.mem_univ w)
          rw [ha.2.1] at hle
          exact hle
      · intro w hw
        have hwnot : w ∉ s := (Finset.mem_sdiff.mp hw).2
        by_contra haw
        exact hwnot (by simp [s, haw])
    · intro haU
      obtain ⟨s, hs⟩ := Set.mem_iUnion.1 haU
      obtain ⟨hsface, haC⟩ := Set.mem_iUnion.1 hs
      have hsL : s ∈ L.faces := by
        simpa [faceFinset] using hsface
      change a ∈ cube ∩ ({a | (∑ w, a w) = 1} ∩
        {a | ∀ w ∈ Finset.univ \ s, a w = 0}) at haC
      change (∀ w, 0 ≤ a w) ∧ (∑ w, a w) = 1 ∧
        (Finset.univ.filter fun w => a w ≠ 0) ∈ L.faces
      refine ⟨haC.1.1, haC.2.1, ?_⟩
      have hsub :
          (Finset.univ.filter fun w => a w ≠ 0) ⊆ s := by
        intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
        by_contra hws
        exact hw (haC.2.2 w (Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ w, hws⟩))
      have hne :
          (Finset.univ.filter fun w => a w ≠ 0).Nonempty := by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty] at h
        have hz : ∀ w, a w = 0 := by
          intro w
          have : w ∉ Finset.univ.filter (fun u => a u ≠ 0) := by
            rw [h]
            simp
          simpa using this
        have : (∑ w, a w) = 0 := by simp [hz]
        rw [haC.2.1] at this
        norm_num at this
      exact (L.isRelLowerSet_faces hsL).2 hsub hne
  have hRcompact : IsCompact R := by
    rw [hRunion]
    apply faceFinset.isCompact_biUnion
    intro s hs
    exact hCcompact s
  letI : CompactSpace (simplicial_geometric_realization L) := by
    unfold simplicial_geometric_realization
    apply isCompact_iff_compactSpace.mp
    exact hRcompact
  letI : T2Space (simplicial_geometric_realization K) := by
    exact T2Space.of_injective_continuous Subtype.val_injective
      continuous_subtype_val
  have hhome : IsHomeomorph F :=
    isHomeomorph_iff_continuous_bijective.mpr
      ⟨hFcontinuous, hFinjective, hFsurjective⟩
  let e : simplicial_geometric_realization L ≃ₜ
      simplicial_geometric_realization K :=
    IsHomeomorph.homeomorph F hhome
  refine ⟨e, ?_⟩
  intro x v
  rfl

@[blueprint "lem:barycentric-subdivision-preserves-antipodality"
  (statement := /-- Let \(m\in\mathbb{N}\), and let \(S\) be an antipodal simplicial \(m\)-sphere.  There exist an antipodal simplicial \(m\)-sphere \(T\), a bijection \(\phi\) from the vertices of \(T\) to the faces of \(S\), and a homeomorphism \(F:|T|\to |S|\) with the following properties.  The complex of \(T\) is the finite barycentric subdivision of the complex of \(S\) relative to \(\phi\).  For every vertex \(v\) of \(T\),
  \[
  \phi(\tau_T(v))=\{\tau_S(u):u\in\phi(v)\},
  \]
  where \(\tau_T\) and \(\tau_S\) are the respective vertex antipodes.  If \(\widehat\tau_T\) and \(\widehat\tau_S\) denote the coordinate-permuting antipodes on the two geometric realizations, then, for every \(x\in|T|\),
  \[
  F(\widehat\tau_T(x))=\widehat\tau_S(F(x)).
  \] -/)
  (proof := /-- Apply \cref{lem:finite-barycentric-subdivision-exists} to the complex of \(S\), and denote the resulting chain complex on the faces of \(S\) by \(L\).  If \(\tau\) is the vertex antipode of \(S\), define an involution on these faces by \(A\mapsto\tau[A]\).  This is well defined by the face-preservation axiom in \cref{def:antipodal-simplicial-sphere}, and its square is the identity because \(\tau^2\) is the identity.  Imaging by \(\tau\) preserves inclusions, so it sends finite chains to finite chains.  Hence \cref{def:is-finite-barycentric-subdivision} shows that it is a simplicial involution of \(L\).

  This involution fixes no face.  Indeed, if \(\tau[A]=A\), assign weight \(1/|A|\) to each vertex in \(A\) and weight zero to every other vertex.  The face \(A\) is nonempty, so these weights define its barycenter in the realization from \cref{def:simplicial-geometric-realization}.  The coordinate axiom in \cref{def:antipodal-simplicial-sphere} and the equality \(\tau[A]=A\) make this barycenter fixed by the realization antipode of \(S\).  Its image under the equivariant homeomorphism to the standard unit sphere would therefore equal its own negative.  This forces that image to be zero, contradicting that its norm is one.

  On the realization of \(L\), define \(\widehat\tau_L\) by \((\widehat\tau_Lx)_A=x_{\tau[A]}\).  Its coordinates are nonnegative, their sum remains one by reindexing, and its support is the image under the face involution of the support of \(x\), hence is again a face of \(L\).  Applying the coordinate permutation twice gives the identity, and each of its coordinates is a continuous coordinate projection.  Thus \(\widehat\tau_L\) is an involutive homeomorphism satisfying the required coordinate formula.

  Apply \cref{lem:barycentric-subdivision-realization-homeomorphism} to obtain the affine barycenter homeomorphism \(F:|L|\to|S|\).  In its coordinate formula, reindex the sum by the face involution.  Imaging a face by \(\tau\) preserves its cardinality, and \(\tau(v)\in\tau[A]\) holds exactly when \(v\in A\).  The reindexed formula is therefore \(F(\widehat\tau_Lx)=\widehat\tau_S(F(x))\).  Equip \(L\) with the preceding vertex and realization involutions, and compose \(F\) with the standard-sphere homeomorphism of \(S\).  The established equivariance and that of \(S\) give all the fields of the required antipodal simplicial \(m\)-sphere \(T\), as well as the asserted vertex-face and realization identities. -/)
  (title := /-- Antipodality survives barycentric subdivision -/)
  (latexEnv := "lemma")]
lemma barycentric_subdivision_preserves_antipodality
    (m : ℕ) (S : antipodal_simplicial_sphere m) :
    ∃ (T : antipodal_simplicial_sphere m)
      (vertexFace :
        T.Vertex ≃ {s : Finset S.Vertex // s ∈ S.complex.faces})
      (realizationMap :
        @simplicial_geometric_realization T.Vertex
            T.vertexFintype T.vertexDecidableEq T.complex ≃ₜ
          @simplicial_geometric_realization S.Vertex
            S.vertexFintype S.vertexDecidableEq S.complex),
      @is_finite_barycentric_subdivision S.Vertex T.Vertex
          S.vertexDecidableEq T.vertexDecidableEq
          S.complex T.complex vertexFace ∧
        (∀ v,
          (vertexFace (T.antipode v)).1 =
            @Finset.image S.Vertex S.Vertex S.vertexDecidableEq
              S.antipode (vertexFace v).1) ∧
        ∀ w,
          realizationMap (T.realizationAntipode w) =
            S.realizationAntipode (realizationMap w) := by
  classical
  letI : Fintype S.Vertex := S.vertexFintype
  letI : DecidableEq S.Vertex := S.vertexDecidableEq
  let Face := {s : Finset S.Vertex // s ∈ S.complex.faces}
  let faceAntipodeMap : Face → Face := fun A =>
    ⟨A.1.image S.antipode,
      (S.antipode_preserves_faces A.1).mp A.2⟩
  have hScomp :
      (S.antipode : S.Vertex → S.Vertex) ∘ S.antipode = id := by
    funext v
    exact S.antipode_involutive v
  have hfaceAntipodeMap (A : Face) :
      faceAntipodeMap (faceAntipodeMap A) = A := by
    apply Subtype.ext
    change (A.1.image S.antipode).image S.antipode = A.1
    rw [Finset.image_image, hScomp, Finset.image_id]
  let faceAntipode : Face ≃ Face :=
    { toFun := faceAntipodeMap
      invFun := faceAntipodeMap
      left_inv := hfaceAntipodeMap
      right_inv := hfaceAntipodeMap }
  have hfaceAntipode (A : Face) :
      faceAntipode (faceAntipode A) = A := hfaceAntipodeMap A
  have hfaceAntipode_ne (A : Face) : faceAntipode A ≠ A := by
    intro hA
    have himage : A.1.image S.antipode = A.1 := by
      exact congrArg Subtype.val hA
    have hcard : (A.1.card : ℝ) ≠ 0 := by
      exact_mod_cast
        (S.complex.isRelLowerSet_faces A.property).1.card_ne_zero
    let b : simplicial_geometric_realization S.complex :=
      ⟨fun v => if v ∈ A.1 then (A.1.card : ℝ)⁻¹ else 0, by
        refine ⟨?_, ?_, ?_⟩
        · intro v
          by_cases hv : v ∈ A.1 <;> simp [hv]
        · simp [hcard]
        · simpa [hcard] using A.property⟩
    have hmem (v : S.Vertex) :
        S.antipode v ∈ A.1 ↔ v ∈ A.1 := by
      constructor
      · intro hv
        have hv' : S.antipode (S.antipode v) ∈
            A.1.image S.antipode :=
          Finset.mem_image.mpr ⟨S.antipode v, hv, rfl⟩
        rw [S.antipode_involutive, himage] at hv'
        exact hv'
      · intro hv
        rw [← himage]
        exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    have hb : S.realizationAntipode b = b := by
      apply Subtype.ext
      funext v
      have hcoord :=
        S.realizationAntipode_coordinates b (S.antipode v)
      rw [S.antipode_involutive] at hcoord
      rw [hcoord]
      simp [b, hmem v]
    have heq := S.toStandardSphere_equivariant b
    rw [hb] at heq
    have hzero : (S.toStandardSphere b).1 = 0 := by
      ext i
      have hi := congrArg
        (fun z : EuclideanSpace ℝ (Fin (m + 1)) => z i) heq
      simp only [PiLp.neg_apply, PiLp.zero_apply] at hi ⊢
      linarith
    have hunit := (S.toStandardSphere b).property
    rw [Metric.mem_sphere, hzero, dist_self] at hunit
    norm_num at hunit
  obtain ⟨L, hL⟩ :=
    finite_barycentric_subdivision_exists S.complex
  have hface_map (s : Finset Face) (hs : s ∈ L.faces) :
      s.image faceAntipode ∈ L.faces := by
    rw [hL] at hs ⊢
    simp only [Equiv.refl_apply] at hs ⊢
    refine ⟨hs.1.image faceAntipode, ?_⟩
    intro A hA B hB
    rw [Finset.mem_image] at hA hB
    obtain ⟨A', hA', rfl⟩ := hA
    obtain ⟨B', hB', rfl⟩ := hB
    rcases hs.2 A' hA' B' hB' with hAB | hBA
    · left
      change A'.1.image S.antipode ⊆ B'.1.image S.antipode
      exact Finset.image_subset_image hAB
    · right
      change B'.1.image S.antipode ⊆ A'.1.image S.antipode
      exact Finset.image_subset_image hBA
  have hfaces (s : Finset Face) :
      s ∈ L.faces ↔ s.image faceAntipode ∈ L.faces := by
    constructor
    · exact hface_map s
    · intro hs
      have hss := hface_map (s.image faceAntipode) hs
      have hcomp : (faceAntipode : Face → Face) ∘ faceAntipode = id := by
        funext A
        exact hfaceAntipode A
      simpa only [Finset.image_image, hcomp, Finset.image_id] using hss
  let realizationAntipodeMap :
      simplicial_geometric_realization L →
        simplicial_geometric_realization L := fun w =>
    ⟨fun A => w.1 (faceAntipode A), by
      refine ⟨fun A => w.property.1 (faceAntipode A), ?_, ?_⟩
      · calc
          ∑ A, w.1 (faceAntipode A) = ∑ A, w.1 A :=
            faceAntipode.sum_comp w.1
          _ = 1 := w.property.2.1
      · have hsupp :
            Finset.univ.filter (fun A => w.1 (faceAntipode A) ≠ 0) =
              (Finset.univ.filter fun A => w.1 A ≠ 0).image
                faceAntipode := by
          ext A
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_image]
          constructor
          · intro hA
            exact ⟨faceAntipode A, hA, hfaceAntipode A⟩
          · rintro ⟨B, hB, hBA⟩
            have hEq : B = faceAntipode A := by
              calc
                B = faceAntipode (faceAntipode B) :=
                  (hfaceAntipode B).symm
                _ = faceAntipode A := congrArg faceAntipode hBA
            simpa only [← hEq] using hB
        rw [hsupp]
        exact hface_map _ w.property.2.2⟩
  let realizationAntipode :
      simplicial_geometric_realization L ≃ₜ
        simplicial_geometric_realization L :=
    { toEquiv :=
        { toFun := realizationAntipodeMap
          invFun := realizationAntipodeMap
          left_inv := by
            intro w
            apply Subtype.ext
            funext A
            exact congrArg w.1 (hfaceAntipode A)
          right_inv := by
            intro w
            apply Subtype.ext
            funext A
            exact congrArg w.1 (hfaceAntipode A) }
      continuous_toFun := by
        dsimp [realizationAntipodeMap]
        apply Continuous.subtype_mk
        apply continuous_pi
        intro A
        exact (continuous_apply (faceAntipode A)).comp
          continuous_subtype_val
      continuous_invFun := by
        dsimp [realizationAntipodeMap]
        apply Continuous.subtype_mk
        apply continuous_pi
        intro A
        exact (continuous_apply (faceAntipode A)).comp
          continuous_subtype_val }
  obtain ⟨realizationMap, hrealizationMap⟩ :=
    barycentric_subdivision_realization_homeomorphism
      S.complex L (Equiv.refl Face) hL
  have hmap (w : simplicial_geometric_realization L) :
      realizationMap (realizationAntipode w) =
        S.realizationAntipode (realizationMap w) := by
    apply Subtype.ext
    funext v
    have hcoord := S.realizationAntipode_coordinates
      (realizationMap w) (S.antipode v)
    rw [S.antipode_involutive] at hcoord
    rw [hrealizationMap, hcoord, hrealizationMap]
    change
      (∑ A : Face, if v ∈ A.1 then
        w.1 (faceAntipode A) / (A.1.card : ℝ) else 0) =
      ∑ A : Face, if S.antipode v ∈ A.1 then
        w.1 A / (A.1.card : ℝ) else 0
    have hsum := faceAntipode.sum_comp
      (fun A : Face =>
        if S.antipode v ∈ A.1 then
          w.1 A / (A.1.card : ℝ) else 0)
    have hcardimage (A : Face) :
        (A.1.image S.antipode).card = A.1.card :=
      Finset.card_image_of_injective A.1 S.antipode.injective
    simpa [realizationAntipode, realizationAntipodeMap,
      faceAntipode, faceAntipodeMap, hcardimage] using hsum
  let T : antipodal_simplicial_sphere m :=
    { Vertex := Face
      complex := L
      antipode := faceAntipode
      antipode_involutive := hfaceAntipode
      antipode_fixed_point_free := hfaceAntipode_ne
      antipode_preserves_faces := hfaces
      realizationAntipode := realizationAntipode
      realizationAntipode_coordinates := by
        intro w A
        change w.1 (faceAntipode (faceAntipode A)) = w.1 A
        rw [hfaceAntipode]
      toStandardSphere := realizationMap.trans S.toStandardSphere
      toStandardSphere_equivariant := by
        intro w
        change
          (S.toStandardSphere
            (realizationMap (realizationAntipode w))).1 =
            -(S.toStandardSphere (realizationMap w)).1
        rw [hmap, S.toStandardSphere_equivariant] }
  refine ⟨T, Equiv.refl Face, realizationMap, ?_, ?_, ?_⟩
  · simpa [T] using hL
  · intro A
    rfl
  · intro w
    exact hmap w

@[blueprint "lem:barycentric-subdivision-preserves-antipodality-with-coordinates"
  (statement := /-- Let \(m\in\mathbb{N}\), and let \(S\) be an antipodal simplicial \(m\)-sphere.  There exist an antipodal simplicial \(m\)-sphere \(T\), a bijection \(\phi\) from the vertices of \(T\) to the faces of \(S\), and a homeomorphism \(F:|T|\to|S|\) such that \(T\) is the barycentric subdivision of \(S\) relative to \(\phi\), \(\phi(\tau_T(v))=\tau_S[\phi(v)]\) for every vertex \(v\), \(F\) is the affine barycenter map, and \(F\) intertwines the realization antipodes. -/)
  (proof := /-- Apply \cref{lem:barycentric-subdivision-preserves-antipodality} to obtain \(T\), \(\phi\), and the subdivision and vertex-antipode identities.  Apply \cref{lem:barycentric-subdivision-realization-homeomorphism} to this subdivision and retain its affine coordinate formula.  For a point \(x\in|T|\), reindex each coordinate sum by the involution \(v\mapsto\tau_T(v)\).  The vertex-antipode identity identifies membership in \(\phi(\tau_T(v))\) with membership of the antipodal old vertex in \(\phi(v)\), and preserves the face cardinality.  The realization-antipode coordinate identities for \(S\) and \(T\) then show coordinatewise that \(F(\widehat\tau_T(x))=\widehat\tau_S(F(x))\). -/)
  (title := /-- Equivariant affine barycentric subdivision -/)
  (latexEnv := "lemma")]
lemma barycentric_subdivision_preserves_antipodality_with_coordinates
    (m : ℕ) (S : antipodal_simplicial_sphere m) :
    ∃ (T : antipodal_simplicial_sphere m)
      (vertexFace :
        T.Vertex ≃ {s : Finset S.Vertex // s ∈ S.complex.faces})
      (realizationMap :
        @simplicial_geometric_realization T.Vertex
            T.vertexFintype T.vertexDecidableEq T.complex ≃ₜ
          @simplicial_geometric_realization S.Vertex
            S.vertexFintype S.vertexDecidableEq S.complex),
      @is_finite_barycentric_subdivision S.Vertex T.Vertex
          S.vertexDecidableEq T.vertexDecidableEq
          S.complex T.complex vertexFace ∧
        (∀ v,
          (vertexFace (T.antipode v)).1 =
            @Finset.image S.Vertex S.Vertex S.vertexDecidableEq
              S.antipode (vertexFace v).1) ∧
        (letI := T.vertexFintype
         letI := S.vertexDecidableEq
         ∀ x v, (realizationMap x).1 v =
           ∑ w : T.Vertex, if v ∈ (vertexFace w).1 then
             x.1 w / ((vertexFace w).1.card : ℝ) else 0) ∧
        ∀ w,
          realizationMap (T.realizationAntipode w) =
            S.realizationAntipode (realizationMap w) := by
  classical
  letI : Fintype S.Vertex := S.vertexFintype
  letI : DecidableEq S.Vertex := S.vertexDecidableEq
  obtain ⟨T, vertexFace, _, hsubdivision, hvertex, _⟩ :=
    barycentric_subdivision_preserves_antipodality m S
  letI : Fintype T.Vertex := T.vertexFintype
  letI : DecidableEq T.Vertex := T.vertexDecidableEq
  obtain ⟨realizationMap, hcoordinates⟩ :=
    barycentric_subdivision_realization_homeomorphism
      S.complex T.complex vertexFace hsubdivision
  refine ⟨T, vertexFace, realizationMap, hsubdivision, hvertex,
    hcoordinates, ?_⟩
  intro x
  apply Subtype.ext
  funext u
  have hsource (w : T.Vertex) :
      (T.realizationAntipode x).1 w = x.1 (T.antipode w) := by
    calc
      (T.realizationAntipode x).1 w =
          (T.realizationAntipode x).1
            (T.antipode (T.antipode w)) := by
              rw [T.antipode_involutive]
      _ = x.1 (T.antipode w) :=
        T.realizationAntipode_coordinates x (T.antipode w)
  have htarget :
      (S.realizationAntipode (realizationMap x)).1 u =
        (realizationMap x).1 (S.antipode u) := by
    calc
      (S.realizationAntipode (realizationMap x)).1 u =
          (S.realizationAntipode (realizationMap x)).1
            (S.antipode (S.antipode u)) := by
              rw [S.antipode_involutive]
      _ = (realizationMap x).1 (S.antipode u) :=
        S.realizationAntipode_coordinates
          (realizationMap x) (S.antipode u)
  rw [hcoordinates, htarget, hcoordinates]
  simp_rw [hsource]
  rw [← T.antipode.sum_comp]
  apply Finset.sum_congr rfl
  intro w hw
  rw [T.antipode_involutive, hvertex]
  have hmem :
      (∃ a ∈ (vertexFace w).1, S.antipode a = u) ↔
        S.antipode u ∈ (vertexFace w).1 := by
    constructor
    · rintro ⟨a, ha, hau⟩
      have hua : S.antipode u = a := by
        rw [← hau, S.antipode_involutive]
      simpa [hua] using ha
    · intro hu
      exact ⟨S.antipode u, hu, S.antipode_involutive u⟩
  have hmem' :
      u ∈ Finset.image S.antipode (vertexFace w).1 ↔
        S.antipode u ∈ (vertexFace w).1 := by
    rw [Finset.mem_image]
    exact hmem
  by_cases hu : S.antipode u ∈ (vertexFace w).1
  · rw [if_pos (hmem'.mpr hu), if_pos hu,
      Finset.card_image_of_injective _ S.antipode.injective]
  · rw [if_neg (fun h => hu (hmem'.mp h)), if_neg hu]

@[blueprint "def:equivariant-barycentric-mesh-stage"
  (statement := /-- Fix an antipodal simplicial \(m\)-sphere \(S\), a natural number \(D\), and a nonnegative mesh parameter \(M\).  An equivariant barycentric mesh stage consists of an antipodal simplicial \(m\)-sphere \(T\), an equivariant homeomorphism \(F:|T|\to|S|\), canonical realized points corresponding to the vertices of \(T\), a bound \(D\) on the cardinality of every face of \(T\), an affine coordinate formula for \(F\), and the assertion that the images under \(F\) of two vertices in a common face differ by at most \(M\) in every coordinate of \(|S|\). -/)
  (title := /-- Quantitative stages of equivariant subdivision -/)
  (latexEnv := "definition")]
structure equivariant_barycentric_mesh_stage
    (m : ℕ) (S : antipodal_simplicial_sphere m) (D : ℕ) (M : ℝ) where
  T : antipodal_simplicial_sphere m
  realizationMap :
    @simplicial_geometric_realization T.Vertex
        T.vertexFintype T.vertexDecidableEq T.complex ≃ₜ
      @simplicial_geometric_realization S.Vertex
        S.vertexFintype S.vertexDecidableEq S.complex
  realizationMap_equivariant :
    ∀ w, realizationMap (T.realizationAntipode w) =
      S.realizationAntipode (realizationMap w)
  vertexPoint :
    T.Vertex →
      @simplicial_geometric_realization T.Vertex
        T.vertexFintype T.vertexDecidableEq T.complex
  vertexPoint_coordinates :
    letI := T.vertexDecidableEq
    ∀ v w, (vertexPoint v).1 w = if w = v then 1 else 0
  face_card_le : ∀ s : Finset T.Vertex, s ∈ T.complex.faces → s.card ≤ D
  realizationMap_affine :
    letI := T.vertexFintype
    ∀ x u, (realizationMap x).1 u =
      ∑ v : T.Vertex, x.1 v * (realizationMap (vertexPoint v)).1 u
  coordinate_mesh_le :
    ∀ s : Finset T.Vertex, s ∈ T.complex.faces →
      ∀ v ∈ s, ∀ w ∈ s, ∀ u,
        |(realizationMap (vertexPoint v)).1 u -
          (realizationMap (vertexPoint w)).1 u| ≤ M

@[blueprint "lem:barycentric-subdivision-preserves-face-cardinality-bound"
  (statement := /-- Let \(K\) and \(L\) be finite abstract simplicial complexes, and suppose that \(L\) is a barycentric subdivision of \(K\).  If every face of \(K\) has cardinality at most \(D\), then every face of \(L\) has cardinality at most \(D\). -/)
  (proof := /-- Let \(t\) be a face of \(L\).  Its vertices correspond to a nonempty finite chain of faces of \(K\).  Choose a maximal face \(A\) in this chain.  Every other member is contained in \(A\).  Distinct members of the chain have distinct positive cardinalities, so the map sending a member of the chain to one less than its cardinality injects the vertices of \(t\) into \(\{0,\ldots,|A|-1\}\).  Hence \(|t|\leq |A|\leq D\). -/)
  (title := /-- Barycentric subdivision preserves face-size bounds -/)
  (latexEnv := "lemma")]
lemma barycentric_subdivision_preserves_face_cardinality_bound
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W)
    (vertexFace : W ≃ {s : Finset V // s ∈ K.faces})
    (hsubdivision : is_finite_barycentric_subdivision K L vertexFace)
    (D : ℕ) (hcard : ∀ s : Finset V, s ∈ K.faces → s.card ≤ D) :
    ∀ t : Finset W, t ∈ L.faces → t.card ≤ D := by
  intro t ht
  obtain ⟨htne, hchain⟩ := (hsubdivision t).mp ht
  obtain ⟨wm, hwm⟩ :=
    t.exists_maximalFor (fun w => (vertexFace w).1) htne
  have hgreat : ∀ w ∈ t, (vertexFace w).1 ⊆ (vertexFace wm).1 := by
    intro w hw
    rcases hchain w hw wm hwm.1 with h | h
    · exact h
    · exact hwm.2 hw h
  let rank : W → ℕ := fun w => (vertexFace w).1.card - 1
  have hrank_maps :
      Set.MapsTo rank (t : Set W)
        (Finset.range (vertexFace wm).1.card : Set ℕ) := by
    intro w hw
    have hwpos :
        0 < (vertexFace w).1.card :=
      (K.isRelLowerSet_faces (vertexFace w).property).1.card_pos
    have hwle :
        (vertexFace w).1.card ≤ (vertexFace wm).1.card :=
      Finset.card_le_card (hgreat w hw)
    simp only [Finset.coe_range, Set.mem_Iio, rank]
    omega
  have hrank_inj : (t : Set W).InjOn rank := by
    intro v hv w hw heq
    have hvpos :
        0 < (vertexFace v).1.card :=
      (K.isRelLowerSet_faces (vertexFace v).property).1.card_pos
    have hwpos :
        0 < (vertexFace w).1.card :=
      (K.isRelLowerSet_faces (vertexFace w).property).1.card_pos
    have hcardeq :
        (vertexFace v).1.card = (vertexFace w).1.card := by
      dsimp only [rank] at heq
      omega
    apply vertexFace.injective
    apply Subtype.ext
    rcases hchain v hv w hw with hvw | hwv
    · exact Finset.eq_of_subset_of_card_le hvw hcardeq.ge
    · exact (Finset.eq_of_subset_of_card_le hwv hcardeq.le).symm
  have hle :
      t.card ≤ (Finset.range (vertexFace wm).1.card).card :=
    Finset.card_le_card_of_injOn rank hrank_maps hrank_inj
  have hle' : t.card ≤ (vertexFace wm).1.card := by
    simpa using hle
  exact hle'.trans (hcard (vertexFace wm).1 (vertexFace wm).property)

@[blueprint "lem:nested-face-averages-contract"
  (statement := /-- Let \(A\subseteq B\) be nonempty finite sets with \(|B|\leq D\), where \(D>0\).  Suppose that a real-valued function differs by at most \(M\geq0\) on pairs of points of \(B\).  Then the difference between its averages on \(A\) and \(B\) is at most \((1-1/D)M\). -/)
  (proof := /-- Fix \(a\in A\).  Express \(f(a)-\operatorname{avg}_B f\) as the average over \(b\in B\) of \(f(a)-f(b)\).  The summand with \(b=a\) is zero, while each of the remaining \(|B|-1\) summands has absolute value at most \(M\).  Thus its absolute value is at most \((1-1/|B|)M\), which is at most \((1-1/D)M\) because \(|B|\leq D\).  Finally, the difference of the averages on \(A\) and \(B\) is the average over \(a\in A\) of these differences, so the triangle inequality gives the same bound. -/)
  (title := /-- Contraction of averages on nested faces -/)
  (latexEnv := "lemma")]
lemma nested_face_averages_contract
    {V : Type*} [DecidableEq V]
    (D : ℕ) (hD : 0 < D)
    (A B : Finset V) (hA : A.Nonempty) (hAB : A ⊆ B)
    (hBD : B.card ≤ D)
    (f : V → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hdiam : ∀ v ∈ B, ∀ w ∈ B, |f v - f w| ≤ M) :
    |(∑ v ∈ A, f v) / (A.card : ℝ) -
        (∑ v ∈ B, f v) / (B.card : ℝ)| ≤
      (1 - 1 / (D : ℝ)) * M := by
  have hAposNat : 0 < A.card := hA.card_pos
  have hB : B.Nonempty := hA.mono hAB
  have hBposNat : 0 < B.card := hB.card_pos
  have hApos : 0 < (A.card : ℝ) := by exact_mod_cast hAposNat
  have hBpos : 0 < (B.card : ℝ) := by exact_mod_cast hBposNat
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast hD
  have hBDreal : (B.card : ℝ) ≤ (D : ℝ) := by exact_mod_cast hBD
  have hratio :
      1 - 1 / (B.card : ℝ) ≤ 1 - 1 / (D : ℝ) := by
    have hinv :
        1 / (D : ℝ) ≤ 1 / (B.card : ℝ) :=
      (one_div_le_one_div hDpos hBpos).2 hBDreal
    linarith
  have hpoint : ∀ a ∈ A,
      |f a - (∑ b ∈ B, f b) / (B.card : ℝ)| ≤
        (1 - 1 / (D : ℝ)) * M := by
    intro a ha
    have haB : a ∈ B := hAB ha
    have hid :
        f a - (∑ b ∈ B, f b) / (B.card : ℝ) =
          (∑ b ∈ B, (f a - f b)) / (B.card : ℝ) := by
      field_simp [ne_of_gt hBpos]
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    rw [hid, abs_div, abs_of_pos hBpos]
    have hsum :
        |∑ b ∈ B, (f a - f b)| ≤
          ((B.card - 1 : ℕ) : ℝ) * M := by
      calc
        |∑ b ∈ B, (f a - f b)| ≤
            ∑ b ∈ B, |f a - f b| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ b ∈ B.erase a, |f a - f b| := by
          rw [← Finset.sum_erase_add _ _ haB]
          simp
        _ ≤ ∑ _b ∈ B.erase a, M := by
          apply Finset.sum_le_sum
          intro b hb
          exact hdiam a haB b (Finset.mem_of_mem_erase hb)
        _ = ((B.card - 1 : ℕ) : ℝ) * M := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem haB]
    calc
      |∑ b ∈ B, (f a - f b)| / (B.card : ℝ) ≤
          (((B.card - 1 : ℕ) : ℝ) * M) /
            (B.card : ℝ) :=
        div_le_div_of_nonneg_right hsum hBpos.le
      _ = (1 - 1 / (B.card : ℝ)) * M := by
        rw [Nat.cast_sub hBposNat]
        norm_num
        field_simp [ne_of_gt hBpos]
      _ ≤ (1 - 1 / (D : ℝ)) * M :=
        mul_le_mul_of_nonneg_right hratio hM
  have hid :
      (∑ v ∈ A, f v) / (A.card : ℝ) -
          (∑ v ∈ B, f v) / (B.card : ℝ) =
        (∑ a ∈ A,
          (f a - (∑ v ∈ B, f v) / (B.card : ℝ))) /
            (A.card : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    field_simp [ne_of_gt hApos, ne_of_gt hBpos]
  rw [hid, abs_div, abs_of_pos hApos]
  apply (div_le_iff₀ hApos).2
  calc
    |∑ a ∈ A, (f a - (∑ v ∈ B, f v) / (B.card : ℝ))| ≤
        ∑ a ∈ A,
          |f a - (∑ v ∈ B, f v) / (B.card : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ A, (1 - 1 / (D : ℝ)) * M := by
      apply Finset.sum_le_sum
      intro a ha
      exact hpoint a ha
    _ = (1 - 1 / (D : ℝ)) * M * (A.card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

@[blueprint "lem:initial-equivariant-barycentric-mesh-stage"
  (statement := /-- Every antipodal simplicial \(m\)-sphere \(S\) has an equivariant barycentric mesh stage whose face-cardinality bound is the number of vertices of \(S\) and whose coordinate mesh bound is \(1\). -/)
  (proof := /-- Apply \cref{lem:barycentric-subdivision-preserves-antipodality-with-coordinates} once.  The canonical point of a new vertex is the corresponding coordinate basis vector; the subdivision condition shows that its singleton support is a face.  The affine coordinate formula identifies its image with the barycenter of the corresponding old face and proves the required affine expansion.  Apply \cref{lem:barycentric-subdivision-preserves-face-cardinality-bound} to the trivial bound by the total number of old vertices.  Finally, every coordinate of every realization point lies in \([0,1]\), so the coordinate difference between any two realized vertices is at most \(1\). -/)
  (title := /-- The initial quantitative subdivision stage -/)
  (latexEnv := "lemma")]
lemma initial_equivariant_barycentric_mesh_stage
    (m : ℕ) (S : antipodal_simplicial_sphere m) :
    Nonempty (equivariant_barycentric_mesh_stage m S
      (@Fintype.card S.Vertex S.vertexFintype) 1) := by
  classical
  letI : Fintype S.Vertex := S.vertexFintype
  letI : DecidableEq S.Vertex := S.vertexDecidableEq
  obtain ⟨T, vertexFace, realizationMap, hsubdivision, _,
      hcoordinates, hequivariant⟩ :=
    barycentric_subdivision_preserves_antipodality_with_coordinates m S
  letI : Fintype T.Vertex := T.vertexFintype
  letI : DecidableEq T.Vertex := T.vertexDecidableEq
  let vertexPoint :
      T.Vertex → simplicial_geometric_realization T.complex := fun v =>
    ⟨fun w => if w = v then 1 else 0, by
      refine ⟨?_, ?_, ?_⟩
      · intro w
        positivity
      · simp
      · have hsingleton : ({v} : Finset T.Vertex) ∈ T.complex.faces := by
          apply (hsubdivision {v}).2
          simp
        have heq :
            (Finset.univ.filter fun w =>
              (if w = v then (1 : ℝ) else 0) ≠ 0) = {v} := by
          ext w
          simp
        rw [heq]
        exact hsingleton⟩
  constructor
  refine
    { T := T
      realizationMap := realizationMap
      realizationMap_equivariant := hequivariant
      vertexPoint := vertexPoint
      vertexPoint_coordinates := ?_
      face_card_le := ?_
      realizationMap_affine := ?_
      coordinate_mesh_le := ?_ }
  · intro v w
    rfl
  · apply barycentric_subdivision_preserves_face_cardinality_bound
      S.complex T.complex vertexFace hsubdivision
    intro s hs
    exact Finset.card_le_card (Finset.subset_univ s)
  · intro x u
    have hverteximage (v : T.Vertex) :
        (realizationMap (vertexPoint v)).1 u =
          if u ∈ (vertexFace v).1 then
            1 / ((vertexFace v).1.card : ℝ) else 0 := by
      rw [hcoordinates]
      rw [Finset.sum_eq_single v]
      · simp [vertexPoint]
      · intro b hb hne
        simp [vertexPoint, hne]
      · simp
    rw [hcoordinates]
    apply Finset.sum_congr rfl
    intro v hv
    rw [hverteximage]
    by_cases hu : u ∈ (vertexFace v).1
    · simp [hu, div_eq_mul_inv]
    · simp [hu]
  · intro s hs v hv w hw u
    have hv0 : 0 ≤ (realizationMap (vertexPoint v)).1 u :=
      (realizationMap (vertexPoint v)).property.1 u
    have hw0 : 0 ≤ (realizationMap (vertexPoint w)).1 u :=
      (realizationMap (vertexPoint w)).property.1 u
    have hv1 : (realizationMap (vertexPoint v)).1 u ≤ 1 := by
      calc
        (realizationMap (vertexPoint v)).1 u ≤
            ∑ z, (realizationMap (vertexPoint v)).1 z :=
          Finset.single_le_sum
            (fun z _ => (realizationMap (vertexPoint v)).property.1 z)
            (Finset.mem_univ u)
        _ = 1 := (realizationMap (vertexPoint v)).property.2.1
    have hw1 : (realizationMap (vertexPoint w)).1 u ≤ 1 := by
      calc
        (realizationMap (vertexPoint w)).1 u ≤
            ∑ z, (realizationMap (vertexPoint w)).1 z :=
          Finset.single_le_sum
            (fun z _ => (realizationMap (vertexPoint w)).property.1 z)
            (Finset.mem_univ u)
        _ = 1 := (realizationMap (vertexPoint w)).property.2.1
    rw [abs_le]
    constructor <;> linarith

@[blueprint "lem:next-equivariant-barycentric-mesh-stage"
  (statement := /-- Let \(D>0\) and \(M\geq0\).  From an equivariant barycentric mesh stage with face-size bound \(D\) and coordinate mesh bound \(M\), one further barycentric subdivision produces a stage with the same face-size bound and coordinate mesh bound \((1-1/D)M\). -/)
  (proof := /-- Apply \cref{lem:barycentric-subdivision-preserves-antipodality-with-coordinates} to the current stage and compose its affine equivariant homeomorphism with the stage homeomorphism.  Canonical new vertices map to averages of the old vertex images over their corresponding old faces; this follows by substituting the coordinate formula into the stage's affine expansion and interchanging the finite sums.  The face-size bound persists by \cref{lem:barycentric-subdivision-preserves-face-cardinality-bound}.  Vertices of a new face correspond to nested nonempty old faces.  Apply \cref{lem:nested-face-averages-contract} coordinatewise to their old vertex images, using the old coordinate mesh bound on the larger face, to obtain the factor \(1-1/D\). -/)
  (title := /-- One quantitative equivariant subdivision step -/)
  (latexEnv := "lemma")]
lemma next_equivariant_barycentric_mesh_stage
    (m : ℕ) (S : antipodal_simplicial_sphere m)
    (D : ℕ) (hD : 0 < D) (M : ℝ) (hM : 0 ≤ M)
    (stage : equivariant_barycentric_mesh_stage m S D M) :
    Nonempty (equivariant_barycentric_mesh_stage m S D
      ((1 - 1 / (D : ℝ)) * M)) := by
  classical
  let A := stage.T
  letI : Fintype S.Vertex := S.vertexFintype
  letI : DecidableEq S.Vertex := S.vertexDecidableEq
  letI : Fintype A.Vertex := A.vertexFintype
  letI : DecidableEq A.Vertex := A.vertexDecidableEq
  obtain ⟨T, vertexFace, stepMap, hsubdivision, _,
      hstepCoordinates, hstepEquivariant⟩ :=
    barycentric_subdivision_preserves_antipodality_with_coordinates m A
  letI : Fintype T.Vertex := T.vertexFintype
  letI : DecidableEq T.Vertex := T.vertexDecidableEq
  let realizationMap := stepMap.trans stage.realizationMap
  let vertexPoint :
      T.Vertex → simplicial_geometric_realization T.complex := fun v =>
    ⟨fun w => if w = v then 1 else 0, by
      refine ⟨?_, ?_, ?_⟩
      · intro w
        positivity
      · simp
      · have hsingleton : ({v} : Finset T.Vertex) ∈ T.complex.faces := by
          apply (hsubdivision {v}).2
          simp
        have heq :
            (Finset.univ.filter fun w =>
              (if w = v then (1 : ℝ) else 0) ≠ 0) = {v} := by
          ext w
          simp
        rw [heq]
        exact hsingleton⟩
  have hstepVertex (v : T.Vertex) (a : A.Vertex) :
      (stepMap (vertexPoint v)).1 a =
        if a ∈ (vertexFace v).1 then
          1 / ((vertexFace v).1.card : ℝ) else 0 := by
    rw [hstepCoordinates]
    rw [Finset.sum_eq_single v]
    · simp [vertexPoint]
    · intro b hb hne
      simp [vertexPoint, hne]
    · simp
  have hnewImage (v : T.Vertex) (u : S.Vertex) :
      (realizationMap (vertexPoint v)).1 u =
        (∑ a ∈ (vertexFace v).1,
          (stage.realizationMap (stage.vertexPoint a)).1 u) /
            ((vertexFace v).1.card : ℝ) := by
    change
      (stage.realizationMap (stepMap (vertexPoint v))).1 u = _
    rw [stage.realizationMap_affine]
    simp_rw [hstepVertex]
    rw [Finset.sum_div]
    simp_rw [ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    apply Finset.sum_congr rfl
    intro a ha
    rw [div_eq_mul_inv]
    ring
  constructor
  refine
    { T := T
      realizationMap := realizationMap
      realizationMap_equivariant := ?_
      vertexPoint := vertexPoint
      vertexPoint_coordinates := ?_
      face_card_le := ?_
      realizationMap_affine := ?_
      coordinate_mesh_le := ?_ }
  · intro x
    change
      stage.realizationMap
          (stepMap (T.realizationAntipode x)) =
        S.realizationAntipode
          (stage.realizationMap (stepMap x))
    rw [hstepEquivariant, stage.realizationMap_equivariant]
  · intro v w
    rfl
  · apply barycentric_subdivision_preserves_face_cardinality_bound
      A.complex T.complex vertexFace hsubdivision D
    exact stage.face_card_le
  · intro x u
    change
      (stage.realizationMap (stepMap x)).1 u =
        ∑ v : T.Vertex, x.1 v *
          (stage.realizationMap (stepMap (vertexPoint v))).1 u
    rw [stage.realizationMap_affine]
    simp_rw [hstepCoordinates]
    calc
      (∑ a : A.Vertex,
          (∑ v : T.Vertex,
            if a ∈ (vertexFace v).1 then
              x.1 v / ((vertexFace v).1.card : ℝ) else 0) *
            (stage.realizationMap (stage.vertexPoint a)).1 u) =
          ∑ a : A.Vertex, ∑ v : T.Vertex,
            (if a ∈ (vertexFace v).1 then
              x.1 v / ((vertexFace v).1.card : ℝ) else 0) *
              (stage.realizationMap (stage.vertexPoint a)).1 u := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.sum_mul]
      _ = ∑ v : T.Vertex, ∑ a : A.Vertex,
            (if a ∈ (vertexFace v).1 then
              x.1 v / ((vertexFace v).1.card : ℝ) else 0) *
              (stage.realizationMap (stage.vertexPoint a)).1 u :=
        Finset.sum_comm
      _ = ∑ v : T.Vertex, x.1 v *
          ((∑ a ∈ (vertexFace v).1,
            (stage.realizationMap (stage.vertexPoint a)).1 u) /
              ((vertexFace v).1.card : ℝ)) := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [Finset.sum_div, Finset.mul_sum]
            simp_rw [ite_mul, zero_mul]
            rw [← Finset.sum_filter]
            rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
            apply Finset.sum_congr rfl
            intro a ha
            rw [div_eq_mul_inv]
            ring
      _ = ∑ v : T.Vertex, x.1 v *
          (stage.realizationMap (stepMap (vertexPoint v))).1 u := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [← hnewImage]
            rfl
  · intro s hs v hv w hw u
    have hsdata := (hsubdivision s).mp hs
    rcases hsdata.2 v hv w hw with hvw | hwv
    · rw [hnewImage, hnewImage]
      apply nested_face_averages_contract D hD
        (vertexFace v).1 (vertexFace w).1
      · exact (A.complex.isRelLowerSet_faces
          (vertexFace v).property).1
      · exact hvw
      · exact stage.face_card_le
          (vertexFace w).1 (vertexFace w).property
      · exact hM
      · intro a ha b hb
        exact stage.coordinate_mesh_le
          (vertexFace w).1 (vertexFace w).property a ha b hb u
    · rw [hnewImage, hnewImage, abs_sub_comm]
      apply nested_face_averages_contract D hD
        (vertexFace w).1 (vertexFace v).1
      · exact (A.complex.isRelLowerSet_faces
          (vertexFace w).property).1
      · exact hwv
      · exact stage.face_card_le
          (vertexFace v).1 (vertexFace v).property
      · exact hM
      · intro a ha b hb
        exact stage.coordinate_mesh_le
          (vertexFace v).1 (vertexFace v).property a ha b hb u

@[blueprint "lem:iterated-equivariant-barycentric-mesh-stage"
  (statement := /-- Let \(S\) be an antipodal simplicial \(m\)-sphere, let \(D\) be the number of vertices of \(S\), and set \(q=1-1/D\).  For every \(r\in\mathbb{N}\), there is an equivariant barycentric mesh stage with face-size bound \(D\) and coordinate mesh bound \(q^r\). -/)
  (proof := /-- The standard sphere is nonempty, and its homeomorphic realization has weights summing to one, so \(S\) has at least one vertex and hence \(D>0\).  The case \(r=0\) is \cref{lem:initial-equivariant-barycentric-mesh-stage}, since \(q^0=1\).  If a stage has mesh bound \(q^r\), this bound is nonnegative and \cref{lem:next-equivariant-barycentric-mesh-stage} produces a stage with bound \(q\,q^r=q^{r+1}\).  Induction on \(r\) proves the assertion. -/)
  (title := /-- Geometric coordinate decay under iteration -/)
  (latexEnv := "lemma")]
lemma iterated_equivariant_barycentric_mesh_stage
    (m : ℕ) (S : antipodal_simplicial_sphere m) :
    let D := @Fintype.card S.Vertex S.vertexFintype
    let q := 1 - 1 / (D : ℝ)
    ∀ r : ℕ,
      Nonempty (equivariant_barycentric_mesh_stage m S D (q ^ r)) := by
  dsimp only
  classical
  letI : Fintype S.Vertex := S.vertexFintype
  letI : DecidableEq S.Vertex := S.vertexDecidableEq
  let Y := Metric.sphere
    (0 : EuclideanSpace ℝ (Fin (m + 1))) 1
  have hY : Y.Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by positivity)
  let y : Y := ⟨Classical.choose hY, Classical.choose_spec hY⟩
  have hvertex : Nonempty S.Vertex := by
    by_contra h
    haveI : IsEmpty S.Vertex := not_nonempty_iff.mp h
    have hsum := (S.toStandardSphere.symm y).property.2.1
    simpa using hsum
  have hD : 0 < Fintype.card S.Vertex :=
    Fintype.card_pos_iff.mpr hvertex
  have hDreal : 0 < (Fintype.card S.Vertex : ℝ) := by
    exact_mod_cast hD
  have hq : 0 ≤ 1 - 1 / (Fintype.card S.Vertex : ℝ) := by
    have hDone : (1 : ℝ) ≤ (Fintype.card S.Vertex : ℝ) := by
      exact_mod_cast hD
    have : 1 / (Fintype.card S.Vertex : ℝ) ≤ 1 := by
      exact (div_le_one hDreal).2 hDone
    linarith
  intro r
  induction r with
  | zero =>
      simpa using initial_equivariant_barycentric_mesh_stage m S
  | succ r ihr =>
      rcases ihr with ⟨stage⟩
      have hpow :
          0 ≤ (1 - 1 / (Fintype.card S.Vertex : ℝ)) ^ r :=
        pow_nonneg hq r
      rcases next_equivariant_barycentric_mesh_stage
          m S (Fintype.card S.Vertex) hD
          ((1 - 1 / (Fintype.card S.Vertex : ℝ)) ^ r)
          hpow stage with ⟨next⟩
      refine ⟨?_⟩
      simpa [pow_succ, mul_comm] using next

@[blueprint "lem:antipodal-sphere-realization-has-uniform-angular-threshold"
  (statement := /-- Let \(S\) be an antipodal simplicial \(m\)-sphere and let \(\varepsilon>0\).  There exists \(\delta>0\) such that whenever two points of \(|S|\) have coordinate-function distance less than \(\delta\), the angle between their images under the homeomorphism from \(|S|\) to the standard unit sphere is less than \(\varepsilon\). -/)
  (proof := /-- On the product of two standard unit spheres, the angle function is continuous because neither vector is zero.  Compactness makes it uniformly continuous, and comparison with a diagonal pair gives a positive sphere-distance threshold for angular distance less than \(\varepsilon\).  Equip \(|S|\), viewed as the subtype of its finite coordinate space, with its inherited metric.  It is compact because it is homeomorphic to the standard sphere, so the sphere homeomorphism is uniformly continuous.  A second positive threshold in \(|S|\), chosen for the preceding sphere-distance threshold, has the required property. -/)
  (title := /-- Uniform angular continuity on a simplicial sphere -/)
  (latexEnv := "lemma")]
lemma antipodal_sphere_realization_has_uniform_angular_threshold
    (m : ℕ) (S : antipodal_simplicial_sphere m)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x y :
        @simplicial_geometric_realization S.Vertex
          S.vertexFintype S.vertexDecidableEq S.complex,
        (∀ u, |x.1 u - y.1 u| < δ) →
          InnerProductGeometry.angle
            (S.toStandardSphere x).1 (S.toStandardSphere y).1 < ε := by
  classical
  letI : Fintype S.Vertex := S.vertexFintype
  let Y := Metric.sphere
    (0 : EuclideanSpace ℝ (Fin (m + 1))) 1
  have hYnonzero : ∀ y : Y, y.1 ≠ 0 := by
    intro y hy
    have hymem := y.2
    rw [Metric.mem_sphere, hy, dist_self] at hymem
    norm_num at hymem
  let angleMap : Y × Y → ℝ := fun z =>
    InnerProductGeometry.angle z.1.1 z.2.1
  have hangleContinuous : Continuous angleMap := by
    dsimp only [angleMap]
    unfold InnerProductGeometry.angle
    fun_prop (disch := simp [hYnonzero])
  have hangleUniform : UniformContinuous angleMap :=
    CompactSpace.uniformContinuous_of_continuous hangleContinuous
  rcases (Metric.uniformContinuous_iff.mp hangleUniform) ε hε with
    ⟨η, hη, hangleη⟩
  have hangleClose : ∀ u v : Y, dist u v < η →
      InnerProductGeometry.angle u.1 v.1 < ε := by
    intro u v huv
    have hpdist : dist (u, v) (u, u) < η := by
      simpa [Prod.dist_eq, dist_comm] using huv
    have hout := hangleη hpdist
    change dist
      (InnerProductGeometry.angle u.1 v.1)
      (InnerProductGeometry.angle u.1 u.1) < ε at hout
    rw [InnerProductGeometry.angle_self (hYnonzero u)] at hout
    simpa [Real.dist_eq, abs_of_nonneg
      (InnerProductGeometry.angle_nonneg u.1 v.1)] using hout
  letI : MetricSpace
      (@simplicial_geometric_realization S.Vertex
        S.vertexFintype S.vertexDecidableEq S.complex) := by
    let mX : MetricSpace
        (@simplicial_geometric_realization S.Vertex
          S.vertexFintype S.vertexDecidableEq S.complex) := by
      dsimp only [simplicial_geometric_realization]
      infer_instance
    exact mX.replaceTopology (by rfl)
  letI : CompactSpace
      (@simplicial_geometric_realization S.Vertex
        S.vertexFintype S.vertexDecidableEq S.complex) :=
    S.toStandardSphere.symm.compactSpace
  have hsphereUniform : UniformContinuous S.toStandardSphere :=
    CompactSpace.uniformContinuous_of_continuous
      S.toStandardSphere.continuous
  rcases (Metric.uniformContinuous_iff.mp hsphereUniform) η hη with
    ⟨δ, hδ, hsphereδ⟩
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  apply hangleClose
  apply hsphereδ
  change dist x.1 y.1 < δ
  rw [dist_pi_lt_iff hδ]
  intro u
  rw [Real.dist_eq]
  exact hxy u

@[blueprint "lem:iterated-barycentric-subdivision-mesh-convergence"
  (statement := /-- Let \(m\in\mathbb{N}\), let \(S\) be an antipodal simplicial \(m\)-sphere, and let \(\varepsilon\in\mathbb{R}\) satisfy \(\varepsilon>0\).  There exist an antipodal simplicial \(m\)-sphere \(T\), a homeomorphism \(F:|T|\to|S|\), and a map \(\iota\) from the vertices of \(T\) to the standard unit sphere in \(\mathbb{R}^{m+1}\) such that \(F(\widehat\tau_T(w))=\widehat\tau_S(F(w))\) for every \(w\in|T|\), \(\iota(\tau_T(v))=-\iota(v)\) for every vertex \(v\) of \(T\), and the angle between \(\iota(v)\) and \(\iota(w)\) is strictly less than \(\varepsilon\) whenever \(v\) and \(w\) belong to a common face of \(T\). -/)
  (proof := /-- Apply \cref{lem:antipodal-sphere-realization-has-uniform-angular-threshold} to obtain \(\delta>0\) such that two points of \(|S|\) whose corresponding coordinates differ by less than \(\delta\) have standard-sphere images at angle less than \(\varepsilon\).  Let \(D\) be the number of vertices of \(S\), and set \(q=1-1/D\).  The realization of \(S\) is nonempty because it is homeomorphic to the standard sphere; since every realization point has coordinates summing to one, \(D>0\).  Hence \(0\leq q<1\), so choose \(r\in\mathbb{N}\) with \(q^r<\delta\).

  By \cref{lem:iterated-equivariant-barycentric-mesh-stage}, there are an antipodal simplicial \(m\)-sphere \(T\), an equivariant homeomorphism \(F:|T|\to|S|\), and a canonical realization point \(p_v\in|T|\) for every vertex \(v\) of \(T\), such that
  \[
  |F(p_v)_u-F(p_w)_u|\leq q^r
  \]
  for every coordinate \(u\) whenever \(v\) and \(w\) lie in a common face.  Define \(\iota(v)\) to be the image of \(F(p_v)\) under the fixed homeomorphism from \(|S|\) to the standard sphere.  The coordinate formula for \(p_v\) and the coordinate-permuting realization antipode give \(p_{\tau_T(v)}=\widehat\tau_T(p_v)\); equivariance of \(F\) and of the sphere homeomorphism therefore gives \(\iota(\tau_T(v))=-\iota(v)\).  Finally, vertices in a common face have every \(F(p_v)\)-coordinate differing by at most \(q^r<\delta\), so the choice of \(\delta\) yields the asserted strict angular bound. -/)
  (title := /-- Mesh convergence for equivariant barycentric subdivision -/)
  (latexEnv := "lemma")]
lemma iterated_barycentric_subdivision_mesh_convergence
    (m : ℕ) (S : antipodal_simplicial_sphere m)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (T : antipodal_simplicial_sphere m)
      (realizationMap :
        @simplicial_geometric_realization T.Vertex
            T.vertexFintype T.vertexDecidableEq T.complex ≃ₜ
          @simplicial_geometric_realization S.Vertex
            S.vertexFintype S.vertexDecidableEq S.complex)
      (ι : T.Vertex →
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1),
      (∀ w,
        realizationMap (T.realizationAntipode w) =
          S.realizationAntipode (realizationMap w)) ∧
      (∀ v, ι (T.antipode v) =
        standard_sphere_antipode_for_margin_disambiguation m (ι v)) ∧
      ∀ s : Finset T.Vertex, s ∈ T.complex.faces →
        ∀ v ∈ s, ∀ w ∈ s,
          InnerProductGeometry.angle (ι v).1 (ι w).1 < ε := by
  classical
  letI : Fintype S.Vertex := S.vertexFintype
  letI : DecidableEq S.Vertex := S.vertexDecidableEq
  let Y := Metric.sphere
    (0 : EuclideanSpace ℝ (Fin (m + 1))) 1
  obtain ⟨δ, hδ, hangular⟩ :=
    antipodal_sphere_realization_has_uniform_angular_threshold m S ε hε
  have hY : Y.Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by positivity)
  let y : Y := ⟨Classical.choose hY, Classical.choose_spec hY⟩
  have hvertex : Nonempty S.Vertex := by
    by_contra h
    haveI : IsEmpty S.Vertex := not_nonempty_iff.mp h
    have hsum := (S.toStandardSphere.symm y).property.2.1
    simpa using hsum
  let D := Fintype.card S.Vertex
  let q : ℝ := 1 - 1 / (D : ℝ)
  have hD : 0 < D := Fintype.card_pos_iff.mpr hvertex
  have hDreal : 0 < (D : ℝ) := by exact_mod_cast hD
  have hDone : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hqnonneg : 0 ≤ q := by
    have hinv : 1 / (D : ℝ) ≤ 1 := (div_le_one hDreal).2 hDone
    dsimp only [q]
    linarith
  have hqlt : q < 1 := by
    have hinv : 0 < 1 / (D : ℝ) := one_div_pos.mpr hDreal
    dsimp only [q]
    linarith
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hδ hqlt
  have hstage :
      Nonempty (equivariant_barycentric_mesh_stage m S D (q ^ r)) := by
    simpa [D, q] using
      (iterated_equivariant_barycentric_mesh_stage m S r)
  rcases hstage with ⟨stage⟩
  letI : Fintype stage.T.Vertex := stage.T.vertexFintype
  letI : DecidableEq stage.T.Vertex := stage.T.vertexDecidableEq
  let ι : stage.T.Vertex → Y := fun v =>
    S.toStandardSphere
      (stage.realizationMap (stage.vertexPoint v))
  have hvertexAntipode : ∀ v,
      stage.vertexPoint (stage.T.antipode v) =
        stage.T.realizationAntipode (stage.vertexPoint v) := by
    intro v
    apply Subtype.ext
    funext w
    rw [stage.vertexPoint_coordinates]
    have hrhs :
        (stage.T.realizationAntipode (stage.vertexPoint v)).1 w =
          (stage.vertexPoint v).1 (stage.T.antipode w) := by
      calc
        (stage.T.realizationAntipode (stage.vertexPoint v)).1 w =
            (stage.T.realizationAntipode (stage.vertexPoint v)).1
              (stage.T.antipode (stage.T.antipode w)) := by
                rw [stage.T.antipode_involutive]
        _ = (stage.vertexPoint v).1 (stage.T.antipode w) :=
          stage.T.realizationAntipode_coordinates
            (stage.vertexPoint v) (stage.T.antipode w)
    rw [hrhs, stage.vertexPoint_coordinates]
    have heq :
        w = stage.T.antipode v ↔ stage.T.antipode w = v := by
      constructor
      · intro hw
        rw [hw, stage.T.antipode_involutive]
      · intro hw
        have := congrArg stage.T.antipode hw
        simpa [stage.T.antipode_involutive] using this
    by_cases hw : w = stage.T.antipode v
    · rw [if_pos hw, if_pos (heq.mp hw)]
    · rw [if_neg hw, if_neg (fun h => hw (heq.mpr h))]
  have hiota : ∀ v, ι (stage.T.antipode v) =
      standard_sphere_antipode_for_margin_disambiguation m (ι v) := by
    intro v
    apply Subtype.ext
    change
      (S.toStandardSphere
        (stage.realizationMap
          (stage.vertexPoint (stage.T.antipode v)))).1 =
        -(S.toStandardSphere
          (stage.realizationMap (stage.vertexPoint v))).1
    rw [hvertexAntipode, stage.realizationMap_equivariant,
      S.toStandardSphere_equivariant]
  refine ⟨stage.T, stage.realizationMap, ι,
    stage.realizationMap_equivariant, hiota, ?_⟩
  intro s hs v hv w hw
  apply hangular
  intro u
  exact (stage.coordinate_mesh_le s hs v hv w hw u).trans_lt hr

@[blueprint "lem:cross-polytope-antipodal-simplicial-sphere"
  (statement := /-- For every natural number \(m\), there exists an antipodal simplicial \(m\)-sphere: a finite simplicial complex equipped with a fixed-point-free involutive simplicial permutation of its vertices, the induced coordinate-permuting involution of its geometric realization, and an equivariant homeomorphism from that realization to the standard unit \(m\)-sphere. -/)
  (proof := /-- Let the vertex set be \(V=\{0,\ldots,m\}\times\{-,+\}\), and let \(\tau(i,\sigma)=(i,-\sigma)\).  Declare a nonempty finite subset of \(V\) to be a face when it contains no pair \(v,\tau(v)\).  Every nonempty subset of such a face again has this property, and \(\tau\) is a fixed-point-free involution preserving the resulting face set.

  For a point \(w\) of the realization in \cref{def:simplicial-geometric-realization}, define the signed coordinate vector \(x(w)\in\mathbb{R}^{m+1}\) by
  \[
  x(w)_i=w(i,+)-w(i,-).
  \]
  Since the support of \(w\) is a face, at most one of the two summands is nonzero.  Consequently \(x(w)\neq0\), \(\sum_i|x(w)_i|=1\), and the two weights over \(i\) are recovered as \(\max\{x(w)_i,0\}\) and \(\max\{-x(w)_i,0\}\).  Thus \(w\mapsto x(w)/\lVert x(w)\rVert_2\) maps the realization continuously and injectively to the Euclidean unit sphere.

  Conversely, for a unit vector \(u\), put \(L(u)=\sum_i|u_i|>0\), and assign the weights \(\max\{u_i,0\}/L(u)\) and \(\max\{-u_i,0\}/L(u)\) to the two vertices over \(i\).  These weights are nonnegative, sum to one, and have no antipodal pair in their support, so they define a point of the realization.  The identities
  \[
  \max\{t,0\}-\max\{-t,0\}=t,
  \qquad
  \max\{t,0\}+\max\{-t,0\}=|t|
  \]
  show that this map and radial normalization are inverse.  Their coordinate formulas, whose denominators are everywhere positive on their respective domains, also prove continuity of both maps.

  Finally, permuting barycentric coordinates by \(\tau\) defines an involutive homeomorphism of the realization and sends \(x(w)\) to \(-x(w)\).  Radial normalization commutes with negation, so the homeomorphism to the unit sphere is equivariant.  These data satisfy every field of \cref{def:antipodal-simplicial-sphere}. -/)
  (title := /-- The cross-polytope as an antipodal simplicial sphere -/)
  (latexEnv := "lemma")]
lemma cross_polytope_antipodal_simplicial_sphere (m : ℕ) :
    Nonempty (antipodal_simplicial_sphere m) := by
  classical
  let V := Fin (m + 1) × Bool
  let τ : V ≃ V :=
    { toFun := fun v => (v.1, !v.2)
      invFun := fun v => (v.1, !v.2)
      left_inv := by
        rintro ⟨i, b⟩
        cases b <;> rfl
      right_inv := by
        rintro ⟨i, b⟩
        cases b <;> rfl }
  have hττ : ∀ v : V, τ (τ v) = v := by
    rintro ⟨i, b⟩
    cases b <;> rfl
  let K : PreAbstractSimplicialComplex V :=
    { faces := {s | s.Nonempty ∧ ∀ v ∈ s, τ v ∉ s}
      isRelLowerSet_faces := by
        intro s hs
        refine ⟨hs.1, ?_⟩
        intro t hts ht
        refine ⟨ht, ?_⟩
        intro v hv hτv
        exact hs.2 v (hts hv) (hts hτv) }
  let realizationAntipodeMap :
      simplicial_geometric_realization K → simplicial_geometric_realization K :=
    fun w =>
      ⟨fun v => w.1 (τ v), by
        refine ⟨fun v => w.property.1 (τ v), ?_, ?_⟩
        · calc
            ∑ v, w.1 (τ v) = ∑ v, w.1 v := τ.sum_comp w.1
            _ = 1 := w.property.2.1
        · change
            (Finset.univ.filter fun v => w.1 (τ v) ≠ 0).Nonempty ∧
              ∀ v ∈ Finset.univ.filter (fun v => w.1 (τ v) ≠ 0),
                τ v ∉ Finset.univ.filter (fun v => w.1 (τ v) ≠ 0)
          have hwface := w.property.2.2
          change
            (Finset.univ.filter fun v => w.1 v ≠ 0).Nonempty ∧
              ∀ v ∈ Finset.univ.filter (fun v => w.1 v ≠ 0),
                τ v ∉ Finset.univ.filter (fun v => w.1 v ≠ 0) at hwface
          constructor
          · obtain ⟨v, hv⟩ := hwface.1
            refine ⟨τ v, by simpa only [Finset.mem_filter, Finset.mem_univ,
              true_and, hττ] using hv⟩
          · intro v hv hτv
            have hv' : v ∈ Finset.univ.filter (fun u => w.1 u ≠ 0) := by
              simpa only [Finset.mem_filter, Finset.mem_univ, true_and, hττ] using hτv
            have hτv' : τ v ∈ Finset.univ.filter (fun u => w.1 u ≠ 0) := by
              simpa using hv
            exact hwface.2 v hv' hτv' ⟩
  let realizationAntipode :
      simplicial_geometric_realization K ≃ₜ simplicial_geometric_realization K :=
    { toEquiv :=
        { toFun := realizationAntipodeMap
          invFun := realizationAntipodeMap
          left_inv := by
            intro w
            apply Subtype.ext
            funext v
            exact congrArg w.1 (by
              rcases v with ⟨i, b⟩
              cases b <;> rfl)
          right_inv := by
            intro w
            apply Subtype.ext
            funext v
            exact congrArg w.1 (by
              rcases v with ⟨i, b⟩
              cases b <;> rfl) }
      continuous_toFun := by
        dsimp [realizationAntipodeMap]
        apply Continuous.subtype_mk
        apply continuous_pi
        intro v
        exact (continuous_apply (τ v)).comp continuous_subtype_val
      continuous_invFun := by
        dsimp [realizationAntipodeMap]
        apply Continuous.subtype_mk
        apply continuous_pi
        intro v
        exact (continuous_apply (τ v)).comp continuous_subtype_val }
  let signedVector (w : simplicial_geometric_realization K) :
      EuclideanSpace ℝ (Fin (m + 1)) :=
    WithLp.toLp 2 fun i => w.1 (i, false) - w.1 (i, true)
  have signedVector_ne_zero (w : simplicial_geometric_realization K) :
      signedVector w ≠ 0 := by
    have hwface := w.property.2.2
    change
      (Finset.univ.filter fun v => w.1 v ≠ 0).Nonempty ∧
        ∀ v ∈ Finset.univ.filter (fun v => w.1 v ≠ 0),
          τ v ∉ Finset.univ.filter (fun v => w.1 v ≠ 0) at hwface
    obtain ⟨⟨i, b⟩, hv⟩ := hwface.1
    have hvne : w.1 (i, b) ≠ 0 := by simpa using hv
    have hopp : w.1 (τ (i, b)) = 0 := by
      by_contra h
      exact hwface.2 (i, b) hv (by simpa using h)
    intro hzero
    have hi := congrArg (fun x : EuclideanSpace ℝ (Fin (m + 1)) => x i) hzero
    change w.1 (i, false) - w.1 (i, true) = 0 at hi
    rw [sub_eq_zero] at hi
    cases b
    · have hopp' : w.1 (i, true) = 0 := by simpa [τ] using hopp
      exact hvne (hi.trans hopp')
    · have hopp' : w.1 (i, false) = 0 := by simpa [τ] using hopp
      exact hvne (hi.symm.trans hopp')
  let toSphereMap (w : simplicial_geometric_realization K) :
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
    ⟨NormedSpace.normalize (signedVector w), by
      simpa using NormedSpace.norm_normalize (signedVector_ne_zero w)⟩
  let l1Norm (u : EuclideanSpace ℝ (Fin (m + 1))) : ℝ :=
    ∑ i, |u i|
  have sphere_l1Norm_pos
      (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
      0 < l1Norm u.1 := by
    have hunorm : ‖u.1‖ = 1 := by simpa using u.property
    have hune : u.1 ≠ 0 := by
      intro h
      simp [h] at hunorm
    have hex : ∃ i, u.1 i ≠ 0 := by
      by_contra h
      push Not at h
      apply hune
      ext i
      exact h i
    obtain ⟨i, hi⟩ := hex
    apply Finset.sum_pos'
    · intro j hj
      exact abs_nonneg _
    · exact ⟨i, Finset.mem_univ i, abs_pos.mpr hi⟩
  let inverseWeight
      (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) (v : V) : ℝ :=
    if v.2 then max (-u.1 v.1) 0 / l1Norm u.1
    else max (u.1 v.1) 0 / l1Norm u.1
  let fromSphereMap
      (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
      simplicial_geometric_realization K :=
    ⟨inverseWeight u, by
      have hLpos := sphere_l1Norm_pos u
      have hLne : l1Norm u.1 ≠ 0 := ne_of_gt hLpos
      have hsum : ∑ v, inverseWeight u v = 1 := by
        calc
          ∑ v, inverseWeight u v =
              ∑ i, (inverseWeight u (i, true) + inverseWeight u (i, false)) := by
                rw [Fintype.sum_prod_type]
                simp_rw [Fintype.sum_bool]
          _ = ∑ i, |u.1 i| / l1Norm u.1 := by
                apply Finset.sum_congr rfl
                intro i hi
                dsimp [inverseWeight]
                rw [← add_div]
                congr 1
                simpa only [add_comm] using
                  max_zero_add_max_neg_zero_eq_abs_self (u.1 i)
          _ = l1Norm u.1 / l1Norm u.1 := by
                rw [Finset.sum_div]
          _ = 1 := div_self hLne
      refine ⟨?_, hsum, ?_⟩
      · intro v
        dsimp [inverseWeight]
        split <;> positivity
      · change
          (Finset.univ.filter fun v => inverseWeight u v ≠ 0).Nonempty ∧
            ∀ v ∈ Finset.univ.filter (fun v => inverseWeight u v ≠ 0),
              τ v ∉ Finset.univ.filter (fun v => inverseWeight u v ≠ 0)
        constructor
        · by_contra h
          rw [Finset.not_nonempty_iff_eq_empty] at h
          have hz : ∀ v, inverseWeight u v = 0 := by
            intro v
            have hv : v ∉ Finset.univ.filter (fun q => inverseWeight u q ≠ 0) := by
              rw [h]
              simp
            simpa using hv
          have : (∑ v, inverseWeight u v) = 0 := by simp [hz]
          linarith
        · rintro ⟨i, b⟩ hv hτv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv hτv
          by_cases hi : 0 ≤ u.1 i
          · cases b <;> simp [inverseWeight, τ, hi] at hv hτv
          · have hi' : u.1 i ≤ 0 := le_of_lt (lt_of_not_ge hi)
            cases b <;> simp [inverseWeight, τ, hi'] at hv hτv ⟩
  have signedVector_fromSphere
      (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
      signedVector (fromSphereMap u) = (l1Norm u.1)⁻¹ • u.1 := by
    ext i
    change inverseWeight u (i, false) - inverseWeight u (i, true) =
      (l1Norm u.1)⁻¹ * u.1 i
    dsimp [inverseWeight]
    rw [← sub_div, max_zero_sub_max_neg_zero_eq_self]
    rw [div_eq_mul_inv, mul_comm]
  have recover_false (w : simplicial_geometric_realization K) (i : Fin (m + 1)) :
      max ((signedVector w) i) 0 = w.1 (i, false) := by
    by_cases hf : w.1 (i, false) = 0
    · have hn := w.property.1 (i, true)
      simp [signedVector, hf, max_eq_right (neg_nonpos.mpr hn)]
    · have hwface := w.property.2.2
      change
        (Finset.univ.filter fun v => w.1 v ≠ 0).Nonempty ∧
          ∀ v ∈ Finset.univ.filter (fun v => w.1 v ≠ 0),
            τ v ∉ Finset.univ.filter (fun v => w.1 v ≠ 0) at hwface
      have ht : w.1 (i, true) = 0 := by
        by_contra ht
        exact hwface.2 (i, false) (by simpa using hf) (by simpa [τ] using ht)
      have hn := w.property.1 (i, false)
      simp [signedVector, ht, max_eq_left hn]
  have recover_true (w : simplicial_geometric_realization K) (i : Fin (m + 1)) :
      max (-((signedVector w) i)) 0 = w.1 (i, true) := by
    by_cases ht : w.1 (i, true) = 0
    · have hn := w.property.1 (i, false)
      simp [signedVector, ht, max_eq_right (neg_nonpos.mpr hn)]
    · have hwface := w.property.2.2
      change
        (Finset.univ.filter fun v => w.1 v ≠ 0).Nonempty ∧
          ∀ v ∈ Finset.univ.filter (fun v => w.1 v ≠ 0),
            τ v ∉ Finset.univ.filter (fun v => w.1 v ≠ 0) at hwface
      have hf : w.1 (i, false) = 0 := by
        by_contra hf
        exact hwface.2 (i, true) (by simpa using ht) (by simpa [τ] using hf)
      have hn := w.property.1 (i, true)
      simp [signedVector, hf, max_eq_left hn]
  have signedVector_injective : Function.Injective signedVector := by
    intro w z h
    apply Subtype.ext
    funext v
    rcases v with ⟨i, b⟩
    cases b
    · rw [← recover_false w i, ← recover_false z i, h]
    · rw [← recover_true w i, ← recover_true z i, h]
  have l1Norm_signedVector (w : simplicial_geometric_realization K) :
      l1Norm (signedVector w) = 1 := by
    dsimp [l1Norm]
    calc
      ∑ i, |(signedVector w) i| =
          ∑ i, (max ((signedVector w) i) 0 + max (-((signedVector w) i)) 0) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact (max_zero_add_max_neg_zero_eq_abs_self ((signedVector w) i)).symm
      _ = ∑ i, (w.1 (i, false) + w.1 (i, true)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [recover_false, recover_true]
      _ = ∑ v, w.1 v := by
            rw [Fintype.sum_prod_type]
            simp_rw [Fintype.sum_bool]
            apply Finset.sum_congr rfl
            intro i hi
            rw [add_comm]
      _ = 1 := w.property.2.1
  have l1Norm_normalize_signedVector (w : simplicial_geometric_realization K) :
      l1Norm (NormedSpace.normalize (signedVector w)) = ‖signedVector w‖⁻¹ := by
    have hn : 0 < ‖signedVector w‖ := norm_pos_iff.mpr (signedVector_ne_zero w)
    change (∑ i, |‖signedVector w‖⁻¹ * (signedVector w) i|) =
      ‖signedVector w‖⁻¹
    calc
      ∑ i, |‖signedVector w‖⁻¹ * (signedVector w) i| =
          ∑ i, ‖signedVector w‖⁻¹ * |(signedVector w) i| := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [abs_mul, abs_of_pos (inv_pos.mpr hn)]
      _ = ‖signedVector w‖⁻¹ * ∑ i, |(signedVector w) i| := by
            rw [Finset.mul_sum]
      _ = ‖signedVector w‖⁻¹ := by
            have hL := l1Norm_signedVector w
            change (∑ i, |(signedVector w) i|) = 1 at hL
            rw [hL, mul_one]
  have fromSphere_toSphere (u : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
      toSphereMap (fromSphereMap u) = u := by
    apply Subtype.ext
    change NormedSpace.normalize (signedVector (fromSphereMap u)) = u.1
    rw [signedVector_fromSphere]
    rw [NormedSpace.normalize_smul_of_pos (inv_pos.mpr (sphere_l1Norm_pos u))]
    apply NormedSpace.normalize_eq_self_of_norm_eq_one
    simpa using u.property
  have toSphere_fromSphere (w : simplicial_geometric_realization K) :
      fromSphereMap (toSphereMap w) = w := by
    apply signedVector_injective
    rw [signedVector_fromSphere]
    change
      (l1Norm (NormedSpace.normalize (signedVector w)))⁻¹ •
          NormedSpace.normalize (signedVector w) = signedVector w
    rw [l1Norm_normalize_signedVector]
    rw [inv_inv]
    exact NormedSpace.norm_smul_normalize (signedVector w)
  have continuous_signedVector : Continuous signedVector := by
    dsimp [signedVector]
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (m + 1) => ℝ)).comp
    apply continuous_pi
    intro i
    exact ((continuous_apply (i, false)).comp continuous_subtype_val).sub
      ((continuous_apply (i, true)).comp continuous_subtype_val)
  have continuous_l1Norm : Continuous l1Norm := by
    dsimp [l1Norm]
    fun_prop
  let sphereHomeomorph :
      simplicial_geometric_realization K ≃ₜ
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
    { toEquiv :=
        { toFun := toSphereMap
          invFun := fromSphereMap
          left_inv := toSphere_fromSphere
          right_inv := fromSphere_toSphere }
      continuous_toFun := by
        dsimp [toSphereMap]
        apply Continuous.subtype_mk
        dsimp [NormedSpace.normalize]
        exact ((continuous_norm.comp continuous_signedVector).inv₀
          (fun w => norm_ne_zero_iff.mpr (signedVector_ne_zero w))).smul
            continuous_signedVector
      continuous_invFun := by
        dsimp [fromSphereMap]
        apply Continuous.subtype_mk
        apply continuous_pi
        rintro ⟨i, b⟩
        have hc : Continuous (fun u : Metric.sphere
            (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 => u.1 i) :=
          ((continuous_apply i).comp
            (PiLp.continuous_ofLp 2 (fun _ : Fin (m + 1) => ℝ))).comp
              continuous_subtype_val
        have hL : Continuous (fun u : Metric.sphere
            (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 => l1Norm u.1) :=
          continuous_l1Norm.comp continuous_subtype_val
        have hLne : ∀ u : Metric.sphere
            (0 : EuclideanSpace ℝ (Fin (m + 1))) 1, l1Norm u.1 ≠ 0 :=
          fun u => ne_of_gt (sphere_l1Norm_pos u)
        cases b
        · dsimp [inverseWeight]
          exact (hc.max continuous_const).div hL hLne
        · dsimp [inverseWeight]
          exact (hc.neg.max continuous_const).div hL hLne }
  have signedVector_realizationAntipode
      (w : simplicial_geometric_realization K) :
      signedVector (realizationAntipode w) = -signedVector w := by
    ext i
    change w.1 (τ (i, false)) - w.1 (τ (i, true)) =
      -(w.1 (i, false) - w.1 (i, true))
    change w.1 (i, true) - w.1 (i, false) =
      -(w.1 (i, false) - w.1 (i, true))
    ring
  have hface_map (s : Finset V) (hs : s ∈ K.faces) :
      s.image τ ∈ K.faces := by
    change s.Nonempty ∧ ∀ v ∈ s, τ v ∉ s at hs
    change (s.image τ).Nonempty ∧ ∀ v ∈ s.image τ, τ v ∉ s.image τ
    constructor
    · exact hs.1.image τ
    · intro v hv hτv
      rw [Finset.mem_image] at hv hτv
      obtain ⟨u, hu, rfl⟩ := hv
      obtain ⟨q, hq, hqeq⟩ := hτv
      apply hs.2 u hu
      have hqu : q = τ u := by
        apply τ.injective
        simpa only [hττ] using hqeq
      simpa only [hqu] using hq
  refine ⟨{
    Vertex := V
    complex := K
    antipode := τ
    antipode_involutive := by
      exact hττ
    antipode_fixed_point_free := by
      rintro ⟨i, b⟩ h
      have : !b = b := by simpa [τ] using congrArg Prod.snd h
      cases b <;> simp at this
    antipode_preserves_faces := by
      intro s
      constructor
      · exact hface_map s
      · intro hs
        have := hface_map (s.image τ) hs
        have hcomp : (τ : V → V) ∘ τ = id := by
          funext v
          exact hττ v
        simpa only [Finset.image_image, hcomp, Finset.image_id] using this
    realizationAntipode := realizationAntipode
    realizationAntipode_coordinates := by
      intro w v
      change w.1 (τ (τ v)) = w.1 v
      congr 1
      rcases v with ⟨i, b⟩
      cases b <;> rfl
    toStandardSphere := sphereHomeomorph
    toStandardSphere_equivariant := by
      intro w
      change NormedSpace.normalize (signedVector (realizationAntipode w)) =
        -NormedSpace.normalize (signedVector w)
      rw [signedVector_realizationAntipode, NormedSpace.normalize_neg] }⟩

@[blueprint "lem:standard-sphere-has-fine-antipodal-triangulation"
  (statement := /-- For every natural number \(m\) and every real number \(\varepsilon>0\), there exist an antipodal simplicial \(m\)-sphere \(S\) and a map \(\iota\) from its vertices to the standard unit \(m\)-sphere such that \(\iota\) intertwines the two antipodalities and the angular distance between the images of any two vertices of a common face is strictly less than \(\varepsilon\). -/)
  (proof := /-- Choose the antipodal simplicial \(m\)-sphere furnished by \cref{lem:cross-polytope-antipodal-simplicial-sphere}.  Apply \cref{lem:iterated-barycentric-subdivision-mesh-convergence} to this sphere and the positive number \(\varepsilon\).  The resulting iterated subdivision and vertex placement are equivariant, and the angular diameter of the image of each face is strictly less than \(\varepsilon\).  Discarding the auxiliary realization homeomorphism leaves exactly the asserted sphere and vertex map. -/)
  (title := /-- Fine antipodal triangulations of the standard sphere -/)
  (latexEnv := "lemma")]
lemma standard_sphere_has_fine_antipodal_triangulation
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (S : antipodal_simplicial_sphere m)
      (ι : S.Vertex →
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1),
      (∀ v, ι (S.antipode v) =
        standard_sphere_antipode_for_margin_disambiguation m (ι v)) ∧
      ∀ s : Finset S.Vertex, s ∈ S.complex.faces →
        ∀ v ∈ s, ∀ w ∈ s,
          InnerProductGeometry.angle (ι v).1 (ι w).1 < ε := by
  obtain ⟨S⟩ := cross_polytope_antipodal_simplicial_sphere m
  obtain ⟨T, _, ι, _, hiota, hmesh⟩ :=
    iterated_barycentric_subdivision_mesh_convergence m S ε hε
  exact ⟨T, ι, hiota, hmesh⟩

@[blueprint "lem:margin-disambiguation-gives-spherical-class"
  (statement := /-- For all integers \(a,b,n\), suppose that there exist a real number \(\varepsilon\) with \(0<\varepsilon<\pi/2\) and a binary concept class on the integer-indexed standard \(n\)-sphere which disambiguates the partial angular-margin linear classifiers of radius \(\varepsilon\), has VC dimension at most \(a\), and has dual antipodal VC dimension at most \(b\).  Then there exist a type \(X\) and a binary concept class on \(X\) with VC dimension at most \(a\), dual antipodal VC dimension at most \(b\), and simplicial spherical dimension at least \(n\). -/)
  (proof := /-- Assume \cref{def:has-margin-disambiguation}, and choose \(0<\varepsilon<\pi/2\) and a class \(H\) disambiguating \(\mathcal L_{n,\varepsilon}\) with the asserted two dimension bounds.  If \(n\leq-1\), take this \(H\); the final condition in \cref{def:has-bounded-spherical-class} is the first alternative in \cref{def:simplicial-spherical-dimension-at-least}.

  Suppose that \(n\geq0\), and put \(m=n\), regarded as a natural number.  Apply \cref{lem:standard-sphere-has-fine-antipodal-triangulation} with \(m\) and \(\varepsilon\).  This gives an antipodal simplicial \(m\)-sphere \(S\), an equivariant vertex placement \(\iota\) on the standard sphere, and an angular diameter less than \(\varepsilon\) for the image of every face.

  The fixed-point-free involution on the finite vertex set partitions that set into two-element orbits.  Choose one representative in every orbit.  For a vertex \(v\), let \(r(v)\) be its chosen representative and let \(\sigma(v)\in\{0,1\}\) record whether \(v\) is the representative or its antipode.  Choose the convention \(\sigma(v)=1\) for the representative and \(\sigma(v)=0\) for its antipode, and define
  \[
    f(v)=(\iota(r(v)),\sigma(v)).
  \]
  Then \(r\) is constant on antipodal pairs and \(\sigma\) changes under the involution, so \(f\) commutes with the labeled antipodality in \cref{def:labeled-antipode}.

  Let \(s\) be a nonempty face and choose \(w\in s\).  Center the partial classifier of \cref{def:margin-partial-classifier} at \(\iota(w)\).  If \(\sigma(v)=1\), then \(r(v)=v\), and the mesh bound gives
  \(\angle(\iota(w),\iota(r(v)))<\varepsilon\).  If \(\sigma(v)=0\), equivariance gives \(\iota(r(v))=-\iota(v)\), whence
  \[
    \angle(-\iota(w),\iota(r(v)))
      =\angle(\iota(w),\iota(v))<\varepsilon.
  \]
  Moreover, in the latter case
  \(\angle(\iota(w),\iota(r(v)))=\pi-\angle(\iota(w),\iota(v))>\varepsilon\), because \(\varepsilon<\pi/2\).  Thus the positive clause in the definition has the required priority, and the classifier takes precisely the labels \(f(v)\) on \(s\).  The classifier centered at \(-\iota(w)\) takes all reversed labels.  By \cref{def:disambiguates, def:margin-linear-partial-class}, members of \(H\) extend these two partial classifiers.

  For the empty face, choose any point of the nonempty standard \(m\)-sphere.  Disambiguation of its margin classifier supplies a member of \(H\), which vacuously realizes either labeling of the empty face.  Hence every face is antipodally realizable in the sense of \cref{def:mapped-face-antipodally-realizable}, while the construction of \(f\) gives the equivariance required by \cref{def:admits-simplicial-sphere}.  Therefore \(H\) admits an \(m\)-sphere.  Since \(m=n\), \cref{def:simplicial-spherical-dimension-at-least} and the two inherited dimension bounds yield \cref{def:has-bounded-spherical-class}. -/)
  (title := /-- From a margin disambiguation to simplicial spherical dimension -/)
  (latexEnv := "lemma")]
lemma margin_disambiguation_gives_spherical_class (a b n : ℤ) :
    has_margin_disambiguation a b n →
      has_bounded_spherical_class a b n := by
  classical
  intro hmargin
  rcases hmargin with ⟨ε, hε, hεpi, H, hdis, hvc, hdual⟩
  cases n with
  | negSucc k =>
      exact ⟨integer_unit_sphere (.negSucc k), H, hvc, hdual, Or.inl (by omega)⟩
  | ofNat m =>
      obtain ⟨S, ι, hiota, hmesh⟩ :=
        standard_sphere_has_fine_antipodal_triangulation m ε hε
      letI : Fintype S.Vertex := S.vertexFintype
      letI : DecidableEq S.Vertex := S.vertexDecidableEq
      let e := Fintype.equivFin S.Vertex
      let f : S.Vertex → integer_unit_sphere (.ofNat m) × Bool := fun v =>
        if e v < e (S.antipode v) then (ι v, true)
        else (ι (S.antipode v), false)
      have hiota_val : ∀ v, (ι (S.antipode v)).1 = -(ι v).1 := by
        intro v
        simpa [standard_sphere_antipode_for_margin_disambiguation] using
          congrArg Subtype.val (hiota v)
      have hH : ∃ h, h ∈ H := by
        have hsphere :
            (Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1).Nonempty :=
          NormedSpace.sphere_nonempty.mpr (by norm_num)
        rcases hsphere with ⟨u, hu⟩
        let u' : integer_unit_sphere (.ofNat m) := ⟨u, hu⟩
        rcases hdis (margin_partial_classifier ε u') ⟨u', rfl⟩ with
          ⟨h, hh, _⟩
        exact ⟨h, hh⟩
      refine ⟨integer_unit_sphere (.ofNat m), H, hvc, hdual,
        Or.inr ⟨m, by simp, ?_⟩⟩
      refine ⟨S, f, ?_, ?_⟩
      · intro s hs
        by_cases hsne : s.Nonempty
        · rcases hsne with ⟨w, hw⟩
          let u : integer_unit_sphere (.ofNat m) := ι w
          let au : integer_unit_sphere (.ofNat m) :=
            standard_sphere_antipode_for_margin_disambiguation m (ι w)
          have hu : u = ι w := rfl
          have hau : au.1 = -u.1 := rfl
          rcases hdis (margin_partial_classifier ε u) ⟨u, rfl⟩ with
            ⟨hp, hpH, hpext⟩
          rcases hdis (margin_partial_classifier ε au) ⟨au, rfl⟩ with
            ⟨hr, hrH, hrext⟩
          constructor
          · refine ⟨hp, hpH, ?_⟩
            intro v hv
            have hnear :
                InnerProductGeometry.angle (ι w).1 (ι v).1 < ε :=
              hmesh s hs w hw v hv
            have hpclass :
                margin_partial_classifier ε u (f v).1 = some (f v).2 := by
              by_cases hvorder : e v < e (S.antipode v)
              · have hnear' : InnerProductGeometry.angle u.1 (f v).1 ≤ ε := by
                  have hf : (f v).1 = ι v := by simp [f, hvorder]
                  rw [hu, hf]
                  exact hnear.le
                simp only [margin_partial_classifier]
                rw [if_pos hnear']
                simp [f, hvorder]
              · have hfar : ε < InnerProductGeometry.angle
                    (ι w).1 (ι (S.antipode v)).1 := by
                  rw [hiota_val v, InnerProductGeometry.angle_neg_right]
                  linarith
                have hnegnear : InnerProductGeometry.angle
                    (-(ι w).1) (ι (S.antipode v)).1 ≤ ε := by
                  rw [hiota_val v]
                  simpa using hnear.le
                have hfar' : ε <
                    InnerProductGeometry.angle u.1 (f v).1 := by
                  have hf : (f v).1 = ι (S.antipode v) := by
                    simp [f, hvorder]
                  rw [hu, hf]
                  exact hfar
                have hnegnear' :
                    InnerProductGeometry.angle (-u.1) (f v).1 ≤ ε := by
                  have hf : (f v).1 = ι (S.antipode v) := by
                    simp [f, hvorder]
                  rw [hu, hf]
                  exact hnegnear
                simp only [margin_partial_classifier]
                rw [if_neg (not_le_of_gt hfar'), if_pos hnegnear']
                simp [f, hvorder]
            exact (hpext (f v).1 (f v).2 hpclass).symm
          · refine ⟨hr, hrH, ?_⟩
            intro v hv
            have hnear :
                InnerProductGeometry.angle (ι w).1 (ι v).1 < ε :=
              hmesh s hs w hw v hv
            have hrclass :
                margin_partial_classifier ε au (f v).1 = some (!(f v).2) := by
              by_cases hvorder : e v < e (S.antipode v)
              · have hnear' :
                    InnerProductGeometry.angle u.1 (f v).1 < ε := by
                  have hf : (f v).1 = ι v := by simp [f, hvorder]
                  rw [hu, hf]
                  exact hnear
                have hfar : ε <
                    InnerProductGeometry.angle au.1 (f v).1 := by
                  rw [hau]
                  rw [InnerProductGeometry.angle_neg_left]
                  linarith
                have hnegnear :
                    InnerProductGeometry.angle (-au.1) (f v).1 ≤ ε := by
                  rw [hau]
                  simpa only [neg_neg] using hnear'.le
                simp only [margin_partial_classifier]
                rw [if_neg (not_le_of_gt hfar), if_pos hnegnear]
                simp [f, hvorder]
              · have hnegbase : InnerProductGeometry.angle
                    (-(ι w).1) (ι (S.antipode v)).1 < ε := by
                  rw [hiota_val v]
                  simpa only [InnerProductGeometry.angle_neg_neg] using hnear
                have hnegnear :
                    InnerProductGeometry.angle (-u.1) (f v).1 < ε := by
                  have hf : (f v).1 = ι (S.antipode v) := by
                    simp [f, hvorder]
                  rw [hu, hf]
                  exact hnegbase
                have hposnear :
                    InnerProductGeometry.angle au.1 (f v).1 ≤ ε := by
                  rw [hau]
                  exact hnegnear.le
                simp only [margin_partial_classifier]
                rw [if_pos hposnear]
                simp [f, hvorder]
            have hreq := hrext (f v).1 (!(f v).2) hrclass
            cases hfv : (f v).2 <;> simp [hfv] at hreq ⊢ <;> assumption
        · rcases hH with ⟨h, hh⟩
          constructor
          · refine ⟨h, hh, ?_⟩
            intro v hv
            exact (hsne ⟨v, hv⟩).elim
          · refine ⟨h, hh, ?_⟩
            intro v hv
            exact (hsne ⟨v, hv⟩).elim
      · intro v
        by_cases hv : e v < e (S.antipode v)
        · have hav : ¬e (S.antipode v) < e v :=
            not_lt_of_ge (le_of_lt hv)
          simp [f, hv, hav, S.antipode_involutive, labeled_antipode]
        · have hav : e (S.antipode v) < e v :=
            lt_of_le_of_ne (le_of_not_gt hv)
              (e.injective.ne (S.antipode_fixed_point_free v))
          simp [f, hv, hav, S.antipode_involutive, labeled_antipode]

@[blueprint "thm:rough-equivalence-between-disambiguations-and-spherical-dimension"
  (statement := /-- For all integers \(a,b,n\), there exists a binary concept class with VC dimension at most \(a\), dual antipodal VC dimension at most \(b\), and simplicial spherical dimension at least \(n\) if and only if, for some angular radius \(\varepsilon\) satisfying \(0<\varepsilon<\pi/2\), the partial linear classifiers of the \(n\)-dimensional unit sphere admit a disambiguation satisfying the same two dimension bounds.  The corresponding cosine margin is therefore strictly positive. -/)
  (proof := /-- The forward implication is \cref{lem:spherical-class-gives-margin-disambiguation}, and the reverse implication is \cref{lem:margin-disambiguation-gives-spherical-class}.  Together they give the asserted equivalence. -/)
  (title := /-- Rough equivalence between disambiguations and spherical dimension -/)
  (latexEnv := "theorem")]
theorem rough_equivalence_between_disambiguations_and_spherical_dimension
    (a b n : ℤ) :
    has_bounded_spherical_class a b n ↔
      has_margin_disambiguation a b n := by
  constructor
  · exact spherical_class_gives_margin_disambiguation a b n
  · exact margin_disambiguation_gives_spherical_class a b n

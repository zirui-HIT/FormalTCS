import Architect
import Mathlib

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:election"
  (statement := /-- Let \(V\) be a type of voters and \(C\) a type of candidates. An election on
  \((V,C)\) consists of a strict preference relation \(\succ_v\) on \(C\) for every voter
  \(v\in V\), with each \(\succ_v\) a strict total order. -/)
  (title := /-- Election -/)
  (latexEnv := "definition")]
structure election (V C : Type*) where
  prefers : V → C → C → Prop
  preference_is_strict_total : ∀ v, IsStrictTotalOrder C (prefers v)

@[blueprint "def:committee"
  (statement := /-- For a candidate type \(C\), a committee is a finite set of candidates. Its
  permitted cardinality will be imposed separately. -/)
  (title := /-- Committee -/)
  (latexEnv := "definition")]
abbrev committee (C : Type*) := Finset C

@[blueprint "def:prefers-over-committee"
  (statement := /-- Let \(\mathcal E\) be an election, let \(v\) be a voter, let \(a\) be a
  candidate, and let \(S\) be a committee. The voter \(v\) prefers \(a\) to \(S\) if
  \(a\succ_v b\) for every \(b\in S\). -/)
  (title := /-- Preference over a committee -/)
  (latexEnv := "definition")]
def prefers_over_committee {V C : Type*} (E : election V C) (v : V) (a : C)
    (S : committee C) : Prop :=
  ∀ b ∈ S, E.prefers v a b

@[blueprint "def:voter-fraction"
  (statement := /-- Suppose that \(V\) is finite. For an election \(\mathcal E\), a candidate
  \(a\), and a committee \(S\), define
  \[
    q_{\mathcal E}(a,S)
      =\frac{|\{v\in V:a\succ_v S\}|}{|V|}.
  \]
  In particular, this value is \(0\) when \(V\) is empty, according to the division convention
  in \(\mathbb R\). -/)
  (title := /-- Fraction of voters preferring a candidate to a committee -/)
  (latexEnv := "definition")]
noncomputable def voter_fraction {V C : Type*} [Fintype V] (E : election V C) (a : C)
    (S : committee C) : ℝ := by
  classical
  exact
    ((Finset.univ.filter (fun v => prefers_over_committee E v a S)).card : ℝ) /
      (Fintype.card V : ℝ)

@[blueprint "def:alpha-undominated"
  (statement := /-- Let \(\alpha\in\mathbb R\) and \(k\in\mathbb N\). A committee \(S\) is
  \(\alpha\)-undominated with size bound \(k\) if \(|S|\leq k\) and
  \(q_{\mathcal E}(a,S)<\alpha\) for every candidate \(a\). -/)
  (title := /-- Undominated committee -/)
  (latexEnv := "definition")]
def alpha_undominated {V C : Type*} [Fintype V] (E : election V C) (α : ℝ) (k : ℕ)
    (S : committee C) : Prop :=
  S.card ≤ k ∧ ∀ a : C, voter_fraction E a S < α

@[blueprint "def:integral-criterion-admissible"
  (statement := /-- Let \(k\geq 1\). A function \(g:\mathbb R\to\mathbb R\) is admissible for the
  integral criterion if it is nonnegative, nonconstant, and nondecreasing on \([0,1]\), is
  continuous at \(1\), and the function \(x\mapsto g(x^k)\) is convex on \([0,1]\). -/)
  (title := /-- Admissibility for the integral criterion -/)
  (latexEnv := "definition")]
def integral_criterion_admissible (g : ℝ → ℝ) (k : ℕ) : Prop :=
  (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ g x) ∧
    (∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ Set.Icc (0 : ℝ) 1, g x ≠ g y) ∧
      MonotoneOn g (Set.Icc (0 : ℝ) 1) ∧
        ContinuousAt g 1 ∧
          ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun x : ℝ => g (x ^ k))

@[blueprint "def:finite-simplex-triangulation"
  (statement := /-- Let \(C\) be a nonempty finite set. A finite triangulation of the
  standard simplex \(\Delta(C)\) is a finite geometric simplicial complex whose vertices
  lie in \(\Delta(C)\), whose realization is exactly \(\Delta(C)\), whose simplices meet
  face-to-face, and which is pure of dimension \(|C|-1\). -/)
  (title := /-- Finite triangulations of a standard simplex -/)
  (latexEnv := "definition")]
structure finite_simplex_triangulation (C : Type*) [Fintype C] [Nonempty C] where
  cells : Set (Set (C → ℝ))
  finite_cells : cells.Finite
  finite_vertices : ∀ σ ∈ cells, σ.Finite
  nonempty_cells : ∀ σ ∈ cells, σ.Nonempty
  affine_independent : ∀ σ ∈ cells, AffineIndependent ℝ ((↑) : σ → (C → ℝ))
  closed_under_nonempty_faces :
    ∀ σ ∈ cells, ∀ τ : Set (C → ℝ), τ.Nonempty → τ ⊆ σ → τ ∈ cells
  vertices_mem_standard_simplex :
    ∀ σ ∈ cells, ∀ x ∈ σ, x ∈ stdSimplex ℝ C
  cover :
    stdSimplex ℝ C = ⋃ σ ∈ cells, convexHull ℝ σ
  face_to_face :
    ∀ σ ∈ cells, ∀ τ ∈ cells,
      convexHull ℝ σ ∩ convexHull ℝ τ = convexHull ℝ (σ ∩ τ)
  pure :
    ∀ σ ∈ cells, ∃ τ ∈ cells,
      σ ⊆ τ ∧ Set.ncard τ = Fintype.card C

@[blueprint "def:sperner-labeling"
  (statement := /-- Let \(K\) be a finite triangulation of \(\Delta(C)\). A Sperner
  labeling of \(K\) assigns to every point \(x\in\mathbb R^C\) a label in \(C\), and at
  each vertex of \(K\) the coordinate selected by its label is nonzero. Equivalently, the
  label of a vertex belongs to the unique smallest face of \(\Delta(C)\) containing that
  vertex. -/)
  (title := /-- Sperner labelings on a triangulated standard simplex -/)
  (latexEnv := "definition")]
def sperner_labeling {C : Type*} [Fintype C] [Nonempty C]
    (K : finite_simplex_triangulation C) (label : (C → ℝ) → C) : Prop :=
  ∀ x ∈ ⋃₀ K.cells, x (label x) ≠ 0

@[blueprint "lem:standard-simplex-canonical-triangulation"
  (statement := /-- Let \(C\) be a nonempty finite set. The standard simplex
  \(\Delta(C)\) admits a finite triangulation all of whose simplices have diameter at
  most \(1\) in the supremum norm. -/)
  (proof := /-- For each \(a\in C\), let \(e_a\in\mathbb R^C\) be the coordinate
  vector with value \(1\) at \(a\) and \(0\) elsewhere, and let
  \(V=\{e_a:a\in C\}\). Define the cells to be all nonempty subsets of \(V\).
  The set \(V\), and hence its family of subsets, is finite. The vectors \(e_a\)
  are linearly independent, so \(V\) and each of its subsets are affinely
  independent. Every \(e_a\) belongs to \(\Delta(C)\), and the convex hull of
  \(V\) is \(\Delta(C)\). Since \(V\) itself is a cell, while the convex hull of
  every cell is contained in the convex hull of \(V\), the cells cover
  \(\Delta(C)\). For two cells, their union is affinely independent, so the
  intersection of their convex hulls is the convex hull of their intersection.
  Finally, every cell is contained in the cell \(V\), which has cardinality
  \(|C|\). These observations verify all fields of
  \cref{def:finite-simplex-triangulation}.

  If \(e_a,e_b\in V\), then at every coordinate the absolute difference between
  \(e_a\) and \(e_b\) is at most \(1\). The supremum-product metric therefore
  gives \(d(e_a,e_b)\leq 1\). Thus every pair of vertices in every cell has
  distance at most \(1\), and the diameter of each cell is at most \(1\). -/)
  (title := /-- The canonical triangulation of a finite standard simplex -/)
  (latexEnv := "lemma")]
lemma standard_simplex_canonical_triangulation {C : Type*} [Fintype C] [Nonempty C] :
    ∃ K : finite_simplex_triangulation C,
      ∀ σ ∈ K.cells, Metric.diam σ ≤ 1 := by
  classical
  let e : C → C → ℝ := fun i => Pi.single i 1
  let V : Set (C → ℝ) := Set.range e
  have he_linear : LinearIndependent ℝ e := by
    simpa [e] using Pi.linearIndependent_single_one C ℝ
  have he_injective : Function.Injective e := he_linear.injective
  have hV_finite : V.Finite := Set.finite_range e
  have hV_nonempty : V.Nonempty := Set.range_nonempty e
  have hV_affine : AffineIndependent ℝ ((↑) : V → (C → ℝ)) :=
    he_linear.affineIndependent.range
  let K : finite_simplex_triangulation C :=
    { cells := {σ | σ.Nonempty ∧ σ ⊆ V}
      finite_cells := hV_finite.finite_subsets.subset (fun _ hσ => hσ.2)
      finite_vertices := fun _ hσ => hV_finite.subset hσ.2
      nonempty_cells := fun _ hσ => hσ.1
      affine_independent := fun _ hσ => hV_affine.mono hσ.2
      closed_under_nonempty_faces := fun _ hσ τ hτ hτσ => ⟨hτ, hτσ.trans hσ.2⟩
      vertices_mem_standard_simplex := by
        rintro σ hσ x hx
        obtain ⟨i, rfl⟩ := hσ.2 hx
        exact single_mem_stdSimplex ℝ i
      cover := by
        rw [← convexHull_rangle_single_eq_stdSimplex ℝ C]
        change convexHull ℝ V = ⋃ σ ∈ {σ | σ.Nonempty ∧ σ ⊆ V}, convexHull ℝ σ
        apply Set.Subset.antisymm
        · intro x hx
          exact Set.mem_iUnion_of_mem V (Set.mem_iUnion_of_mem ⟨hV_nonempty, Set.Subset.rfl⟩ hx)
        · apply Set.iUnion_subset
          intro σ
          apply Set.iUnion_subset
          intro hσ
          exact convexHull_mono hσ.2
      face_to_face := by
        intro σ hσ τ hτ
        let σf := (hV_finite.subset hσ.2).toFinset
        let τf := (hV_finite.subset hτ.2).toFinset
        have hσf : (σf : Set (C → ℝ)) ⊆ V := by
          simpa [σf] using hσ.2
        have hτf : (τf : Set (C → ℝ)) ⊆ V := by
          simpa [τf] using hτ.2
        have h_union :
            AffineIndependent ℝ ((↑) : ↥(σf ∪ τf) → (C → ℝ)) := by
          apply hV_affine.mono
          intro x hx
          rcases Finset.mem_union.mp hx with hx | hx
          · exact hσf hx
          · exact hτf hx
        simpa [σf, τf] using
          h_union.convexHull_inter'.symm
      pure := by
        intro σ hσ
        refine ⟨V, ⟨hV_nonempty, Set.Subset.rfl⟩, hσ.2, ?_⟩
        simpa [V, Nat.card_eq_fintype_card] using
          Set.ncard_range_of_injective he_injective }
  refine ⟨K, ?_⟩
  intro σ hσ
  apply Metric.diam_le_of_forall_dist_le zero_le_one
  intro x hx y hy
  obtain ⟨i, rfl⟩ := hσ.2 hx
  obtain ⟨j, rfl⟩ := hσ.2 hy
  rw [dist_pi_le_iff zero_le_one]
  intro c
  by_cases hic : i = c <;> by_cases hjc : j = c <;>
    simp [e, Pi.single_apply, hic, hjc]

@[blueprint "def:barycentric-face-chain-cell"
  (statement := /-- Let \(K\) be a finite triangulation of the standard simplex.
  A barycentric face-chain cell of \(K\) is the set of centroids of a nonempty
  finite chain \(\mathcal F\) of nonempty faces of one cell \(\sigma\) of \(K\).
  The chain is ordered by inclusion. -/)
  (title := /-- Cells determined by chains of face barycentres -/)
  (latexEnv := "definition")]
noncomputable def barycentric_face_chain_cell {C : Type*}
    [Fintype C] [Nonempty C] (K : finite_simplex_triangulation C)
    (τ : Set (C → ℝ)) : Prop :=
  ∃ σ ∈ K.cells, ∃ ℱ : Finset (Finset (C → ℝ)),
    ℱ.Nonempty ∧
      (∀ F ∈ ℱ, F.Nonempty ∧ (F : Set (C → ℝ)) ⊆ σ) ∧
        (∀ F ∈ ℱ, ∀ G ∈ ℱ, F ⊆ G ∨ G ⊆ F) ∧
          τ = {x | ∃ F ∈ ℱ, x = F.centroid ℝ id}

@[blueprint "lem:barycentric-face-chain-affine-independent"
  (statement := /-- Let \(C\) be a nonempty finite type and let \(K\) be a finite
  triangulation of \(\Delta(C)\). The family of barycentric face-chain cells of \(K\)
  is finite. Every member of this family is a nonempty finite affinely independent
  set contained in \(\Delta(C)\), and every nonempty subset of such a member is again
  a barycentric face-chain cell of \(K\). -/)
  (proof := /-- Use \cref{def:barycentric-face-chain-cell}. There are finitely many
  cells \(\sigma\) of \(K\), each \(\sigma\) is finite, and hence each \(\sigma\) has
  only finitely many chains of nonempty faces. This proves finiteness of the family
  and of every face-chain cell; nonemptiness follows from the nonemptiness of the
  indexing chain.

  We first record the separation property used for affine independence. If
  \(G\subsetneq F\subseteq\sigma\) and \(F\neq\varnothing\), then the centroid of
  \(F\) does not belong to \(\operatorname{aff}(G)\). Indeed, choose
  \(v\in F\setminus G\). Regard \(F\) as a subfamily of the affinely independent
  family \(\sigma\). If its centroid belonged to \(\operatorname{aff}(G)\), uniqueness
  of affine coordinates would force the coefficient of \(v\) in the centroid to
  vanish, whereas that coefficient is \(1/|F|\neq0\).

  We now prove affine independence of the centroids in a chain by strong induction on
  the number of faces. Choose a face \(F\) of maximal cardinality. If it is the only
  face, the assertion is immediate. Otherwise choose a face \(G\) of maximal
  cardinality among the remaining faces. Comparability and maximality imply that every
  remaining face \(H\) satisfies \(H\subseteq G\subsetneq F\). Hence the centroid of
  every such \(H\) lies in
  \(\operatorname{conv}(H)\subseteq\operatorname{aff}(G)\), while the separation
  property places the centroid of \(F\) outside \(\operatorname{aff}(G)\). The
  induction hypothesis makes the remaining centroids affinely independent, so
  adjoining the centroid of \(F\) preserves affine independence.

  For every face \(F\) in the chain, its centroid lies in
  \(\operatorname{conv}(F)\). Since \(F\subseteq\sigma\), all vertices of \(\sigma\)
  lie in the convex set \(\Delta(C)\), and therefore every centroid lies in
  \(\Delta(C)\). Finally, if \(\rho\) is a nonempty subset of the centroid set, filter
  the indexing chain to those faces whose centroids belong to \(\rho\). The filtered
  chain is nonempty, retains nonempty faces, containment in \(\sigma\), and
  comparability, and its centroid set is exactly \(\rho\). Thus it again satisfies
  \cref{def:barycentric-face-chain-cell}. -/)
  (title := /-- Basic axioms for barycentric face-chain cells -/)
  (latexEnv := "lemma")]
lemma barycentric_face_chain_affine_independent {C : Type*}
    [Fintype C] [Nonempty C] (K : finite_simplex_triangulation C) :
    Set.Finite
        {τ : Set (C → ℝ) | barycentric_face_chain_cell K τ} ∧
      (∀ τ, barycentric_face_chain_cell K τ →
        τ.Finite ∧ τ.Nonempty ∧
          AffineIndependent ℝ ((↑) : τ → (C → ℝ)) ∧
            ∀ x ∈ τ, x ∈ stdSimplex ℝ C) ∧
        ∀ τ, barycentric_face_chain_cell K τ →
          ∀ ρ : Set (C → ℝ), ρ.Nonempty → ρ ⊆ τ →
            barycentric_face_chain_cell K ρ := by
  classical
  let P := C → ℝ
  have centroid_not_mem_affineSpan
      {σ : Set P} (hσ : AffineIndependent ℝ ((↑) : σ → P))
      {F G : Finset P} (hF : F.Nonempty) (hFσ : (F : Set P) ⊆ σ)
      (hGF : G ⊂ F) :
      F.centroid ℝ id ∉ affineSpan ℝ (G : Set P) := by
    intro hmem
    have hGFset : (G : Set P) ⊂ (F : Set P) := by
      simpa using hGF
    obtain ⟨x, hxF, hxG⟩ := Set.exists_of_ssubset hGFset
    let i : F := ⟨x, hxF⟩
    let p : F → P := fun y => y
    have hp : AffineIndependent ℝ p := by
      exact hσ.comp_embedding
        (⟨fun y : F => ⟨(y : P), hFσ y.property⟩,
            fun _ _ h =>
              Subtype.ext (congrArg (fun z : σ => (z : P)) h)⟩ : F ↪ σ)
    let t : Set F := {y | (y : P) ∈ G}
    have hGt : p '' t = (G : Set P) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        exact ⟨⟨y, hGF.le hy⟩, hy, rfl⟩
    have hmem' :
        (Finset.univ : Finset F).affineCombination ℝ p
            ((Finset.univ : Finset F).centroidWeightsIndicator ℝ) ∈
          affineSpan ℝ (p '' t) := by
      rw [hGt, ← Finset.centroid_eq_affineCombination_fintype,
        Finset.centroid_univ]
      exact hmem
    have huniv : (Finset.univ : Finset F).Nonempty := by
      exact ⟨i, Finset.mem_univ i⟩
    have hw :
        ∑ y, (Finset.univ : Finset F).centroidWeightsIndicator ℝ y = 1 :=
      (Finset.univ : Finset F).sum_centroidWeightsIndicator_eq_one_of_nonempty
        ℝ huniv
    have hi_not : i ∉ t := hxG
    have hz :=
      hp.eq_zero_of_affineCombination_mem_affineSpan hw hmem'
        (Finset.mem_univ i) hi_not
    letI : Nonempty F := ⟨i⟩
    have hFempty : F = ∅ := by
      simpa [Finset.centroidWeightsIndicator, Finset.centroidWeights] using hz
    exact hF.ne_empty hFempty
  have chain_centroids_affineIndependent :
      ∀ (σ : Set P) (ℱ : Finset (Finset P)),
        AffineIndependent ℝ ((↑) : σ → P) →
        (∀ F ∈ ℱ, F.Nonempty ∧ (F : Set P) ⊆ σ) →
        (∀ F ∈ ℱ, ∀ G ∈ ℱ, F ⊆ G ∨ G ⊆ F) →
        AffineIndependent ℝ (fun F : ℱ => F.1.centroid ℝ id) := by
    intro σ ℱ hσ hfaces hchain
    have by_card :
        ∀ n : ℕ, ∀ ℒ : Finset (Finset P), ℒ.card = n →
          (∀ F ∈ ℒ, F.Nonempty ∧ (F : Set P) ⊆ σ) →
          (∀ F ∈ ℒ, ∀ G ∈ ℒ, F ⊆ G ∨ G ⊆ F) →
          AffineIndependent ℝ (fun F : ℒ => F.1.centroid ℝ id) := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
          intro ℒ hcard hfacesℒ hchainℒ
          by_cases hℒ : ℒ = ∅
          · subst ℒ
            exact affineIndependent_of_subsingleton (k := ℝ) _
          obtain ⟨F, hFℒ, hFmax⟩ :=
            ℒ.exists_max_image Finset.card (Finset.nonempty_iff_ne_empty.mpr hℒ)
          let ℛ := ℒ.erase F
          have hnpos : 0 < n := by
            rw [← hcard]
            exact Finset.card_pos.mpr ⟨F, hFℒ⟩
          have hℛcard : ℛ.card < n := by
            dsimp [ℛ]
            rw [Finset.card_erase_of_mem hFℒ, hcard]
            omega
          have hℛfaces :
              ∀ G ∈ ℛ, G.Nonempty ∧ (G : Set P) ⊆ σ := by
            intro G hG
            exact hfacesℒ G (Finset.mem_of_mem_erase hG)
          have hℛchain :
              ∀ G ∈ ℛ, ∀ H ∈ ℛ, G ⊆ H ∨ H ⊆ G := by
            intro G hG H hH
            exact hchainℒ G (Finset.mem_of_mem_erase hG)
              H (Finset.mem_of_mem_erase hH)
          have hℛai :
              AffineIndependent ℝ (fun G : ℛ => G.1.centroid ℝ id) :=
            ih ℛ.card hℛcard ℛ rfl hℛfaces hℛchain
          by_cases hℛ : ℛ = ∅
          · letI : Subsingleton ℒ :=
              ⟨fun A B => by
                apply Subtype.ext
                have hAF : A.1 = F := by
                  by_contra hne
                  have : A.1 ∈ ℛ := by
                    exact Finset.mem_erase.mpr ⟨hne, A.2⟩
                  simpa [hℛ] using this
                have hBF : B.1 = F := by
                  by_contra hne
                  have : B.1 ∈ ℛ := by
                    exact Finset.mem_erase.mpr ⟨hne, B.2⟩
                  simpa [hℛ] using this
                exact hAF.trans hBF.symm⟩
            exact affineIndependent_of_subsingleton (k := ℝ) _
          obtain ⟨G, hGℛ, hGmax⟩ :=
            ℛ.exists_max_image Finset.card (Finset.nonempty_iff_ne_empty.mpr hℛ)
          have hGℒ : G ∈ ℒ := Finset.mem_of_mem_erase hGℛ
          have hGFne : G ≠ F := (Finset.mem_erase.mp hGℛ).1
          have hGF : G ⊂ F := by
            rcases hchainℒ G hGℒ F hFℒ with hsub | hsup
            · exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hGFne⟩
            · exact False.elim
                (hGFne
                  (Finset.eq_of_subset_of_card_le (s := F) (t := G)
                    hsup (hFmax G hGℒ)).symm)
          have hHG : ∀ H ∈ ℛ, H ⊆ G := by
            intro H hH
            rcases hℛchain H hH G hGℛ with hsub | hsup
            · exact hsub
            · have heq :=
                Finset.eq_of_subset_of_card_le (s := G) (t := H)
                  hsup (hGmax H hH)
              simpa [heq]
          let i : ℒ := ⟨F, hFℒ⟩
          let p : ℒ → P := fun H => H.1.centroid ℝ id
          have hother :
              AffineIndependent ℝ (fun H : {H : ℒ // H ≠ i} => p H) := by
            let e : {H : ℒ // H ≠ i} ≃ ℛ :=
              { toFun := fun H =>
                  ⟨H.1.1, Finset.mem_erase.mpr
                    ⟨by
                      intro heq
                      apply H.2
                      apply Subtype.ext
                      exact heq,
                      H.1.2⟩⟩
                invFun := fun H =>
                  ⟨⟨H.1, Finset.mem_of_mem_erase H.2⟩, by
                    intro heq
                    have : H.1 = F :=
                      congrArg (fun z : ℒ => z.1) heq
                    exact (Finset.mem_erase.mp H.2).1 this⟩
                left_inv := by
                  intro H
                  apply Subtype.ext
                  apply Subtype.ext
                  rfl
                right_inv := by
                  intro H
                  apply Subtype.ext
                  rfl }
            exact (affineIndependent_equiv (k := ℝ) e).2 hℛai
          have hrange :
              p '' {H | H ≠ i} ⊆ affineSpan ℝ (G : Set P) := by
            rintro y ⟨H, hHi, rfl⟩
            have hHℛ : H.1 ∈ ℛ := by
              exact Finset.mem_erase.mpr
                ⟨by
                  intro heq
                  apply hHi
                  apply Subtype.ext
                  exact heq,
                  H.2⟩
            have hHG' := hHG H.1 hHℛ
            have hcentroid :
                H.1.centroid ℝ id ∈ convexHull ℝ (H.1 : Set P) :=
              Finset.centroid_mem_convexHull (R := ℝ) H.1
                (hℛfaces H.1 hHℛ).1
            exact
              (convexHull_min
                (fun x hx => subset_affineSpan ℝ (G : Set P) (hHG' hx))
                (affineSpan ℝ (G : Set P)).convex) hcentroid
          have hnot :
              p i ∉ affineSpan ℝ (p '' {H | H ≠ i}) := by
            intro hi
            exact
              (centroid_not_mem_affineSpan hσ (hfacesℒ F hFℒ).1
                (hfacesℒ F hFℒ).2 hGF)
                ((affineSpan_le_of_subset_coe (k := ℝ) hrange) hi)
          exact hother.affineIndependent_of_notMem_span hnot
    exact by_card ℱ.card ℱ rfl hfaces hchain
  let faceFamilies (σ : Set P) : Set (Finset (Finset P)) :=
    {ℱ | ∀ F ∈ ℱ, (F : Set P) ⊆ σ}
  let centroidSet (ℱ : Finset (Finset P)) : Set P :=
    {x | ∃ F ∈ ℱ, x = F.centroid ℝ id}
  have faceFamilies_finite :
      ∀ σ : Set P, σ.Finite → (faceFamilies σ).Finite := by
    intro σ hσ
    have hfaces : {F : Finset P | (F : Set P) ⊆ σ}.Finite := by
      simpa using
        hσ.finite_subsets.preimage_embedding Finset.coeEmb.toEmbedding
    convert
      hfaces.finite_subsets.preimage_embedding
        Finset.coeEmb.toEmbedding using 1
    ext ℱ
    simp [faceFamilies, Set.subset_def]
    rfl
  have hfinite :
      Set.Finite {τ : Set P | barycentric_face_chain_cell K τ} := by
    have hcandidate :
        Set.Finite
          (⋃ σ ∈ K.cells, centroidSet '' faceFamilies σ) :=
      K.finite_cells.biUnion fun σ hσ =>
        (faceFamilies_finite σ (K.finite_vertices σ hσ)).image centroidSet
    refine hcandidate.subset ?_
    intro τ hτ
    rcases hτ with ⟨σ, hσ, ℱ, hℱ, hfaces, hchain, rfl⟩
    apply Set.mem_iUnion.2
    refine ⟨σ, Set.mem_iUnion.2 ⟨hσ, ?_⟩⟩
    exact ⟨ℱ, by
      intro F hF
      exact (hfaces F hF).2, rfl⟩
  refine ⟨hfinite, ?_, ?_⟩
  · intro τ hτ
    rcases hτ with ⟨σ, hσ, ℱ, hℱ, hfaces, hchain, hτ⟩
    have hτrange :
        τ = Set.range (fun F : ℱ => F.1.centroid ℝ id) := by
      rw [hτ]
      ext x
      simp [eq_comm]
    have hτfinite : τ.Finite := by
      rw [hτrange]
      exact Set.finite_range _
    have hτnonempty : τ.Nonempty := by
      obtain ⟨F, hF⟩ := hℱ
      rw [hτ]
      exact ⟨F.centroid ℝ id, F, hF, rfl⟩
    have hτai : AffineIndependent ℝ ((↑) : τ → P) := by
      rw [hτrange]
      exact
        (chain_centroids_affineIndependent σ ℱ
          (K.affine_independent σ hσ) hfaces hchain).range
    refine ⟨hτfinite, hτnonempty, hτai, ?_⟩
    intro x hx
    rw [hτ] at hx
    rcases hx with ⟨F, hF, rfl⟩
    have hcentroid :
        F.centroid ℝ id ∈ convexHull ℝ (F : Set P) :=
      Finset.centroid_mem_convexHull (R := ℝ) F (hfaces F hF).1
    exact
      ((convex_stdSimplex ℝ C).convexHull_subset_iff.2
        (fun y hy =>
          K.vertices_mem_standard_simplex σ hσ y ((hfaces F hF).2 hy)))
        hcentroid
  · intro τ hτ ρ hρ hρτ
    rcases hτ with ⟨σ, hσ, ℱ, hℱ, hfaces, hchain, hτ⟩
    let 𝒢 := ℱ.filter (fun F => F.centroid ℝ id ∈ ρ)
    refine ⟨σ, hσ, 𝒢, ?_, ?_, ?_, ?_⟩
    · obtain ⟨x, hxρ⟩ := hρ
      have hxτ := hρτ hxρ
      rw [hτ] at hxτ
      rcases hxτ with ⟨F, hF, rfl⟩
      exact ⟨F, Finset.mem_filter.mpr ⟨hF, hxρ⟩⟩
    · intro F hF
      exact hfaces F (Finset.mem_filter.mp hF).1
    · intro F hF G hG
      exact hchain F (Finset.mem_filter.mp hF).1
        G (Finset.mem_filter.mp hG).1
    · ext x
      constructor
      · intro hx
        have hxτ := hρτ hx
        rw [hτ] at hxτ
        rcases hxτ with ⟨F, hF, rfl⟩
        exact ⟨F, Finset.mem_filter.mpr ⟨hF, hx⟩, rfl⟩
      · rintro ⟨F, hF, rfl⟩
        exact (Finset.mem_filter.mp hF).2

@[blueprint "lem:finite-convex-hull-barycentric-chain-cover"
  (statement := /-- Let \(C\) be a type, let \(s\) be a nonempty finite subset of
  \(\mathbb R^C\), and let \(x\in\operatorname{conv}(s)\). There is a nonempty finite
  inclusion-chain \(\mathcal F\) of nonempty subsets of \(s\) such that \(x\) belongs
  to the convex hull of the centroids of the members of \(\mathcal F\). -/)
  (proof := /-- Write \(x=\sum_{y\in s}w_y y\), where \(w_y\geq0\) and
  \(\sum_{y\in s}w_y=1\), and argue by strong induction on \(|s|\). Choose
  \(a\in s\) minimizing \(w_y\), put \(m=w_a\), and set \(q=1-|s|m\). Then
  \(m,q\geq0\).

  If \(q=0\), the nonnegative numbers \(w_y-m\) sum to zero. Hence
  \(w_y=m=|s|^{-1}\) for every \(y\in s\), so \(x\) is the centroid of \(s\) and
  the singleton chain \(\{s\}\) suffices. If \(q>0\), then
  \(t=s\setminus\{a\}\) is nonempty and
  \[
    w'_y=\frac{w_y-m}{q}\qquad(y\in t)
  \]
  are nonnegative coefficients summing to one. Set
  \(x'=\sum_{y\in t}w'_y y\). The induction hypothesis supplies the required
  chain for \(x'\) inside \(t\). The identity
  \[
    x=|s|m\,\operatorname{centroid}(s)+q x'
  \]
  expresses \(x\) as a convex combination because \(|s|m+q=1\). Adjoining \(s\)
  to the chain for \(x'\) therefore gives the required chain for \(x\). -/)
  (title := /-- Finite convex hulls are covered by barycentric chain simplices -/)
  (latexEnv := "lemma")]
lemma finite_convex_hull_barycentric_chain_cover {C : Type*} :
    ∀ s : Finset (C → ℝ), s.Nonempty → ∀ x : C → ℝ,
      x ∈ convexHull ℝ (s : Set (C → ℝ)) →
        ∃ ℱ : Finset (Finset (C → ℝ)),
          ℱ.Nonempty ∧
            (∀ F ∈ ℱ, F.Nonempty ∧ F ⊆ s) ∧
              (∀ F ∈ ℱ, ∀ G ∈ ℱ, F ⊆ G ∨ G ⊆ F) ∧
                x ∈ convexHull ℝ
                  {y | ∃ F ∈ ℱ, y = F.centroid ℝ id} := by
  classical
  refine Finset.strongInduction (p := fun s => s.Nonempty → ∀ x : C → ℝ,
    x ∈ convexHull ℝ (s : Set (C → ℝ)) →
      ∃ ℱ : Finset (Finset (C → ℝ)),
        ℱ.Nonempty ∧
          (∀ F ∈ ℱ, F.Nonempty ∧ F ⊆ s) ∧
            (∀ F ∈ ℱ, ∀ G ∈ ℱ, F ⊆ G ∨ G ⊆ F) ∧
              x ∈ convexHull ℝ
                {y | ∃ F ∈ ℱ, y = F.centroid ℝ id}) ?_
  intro s ih hs x hx
  rw [Finset.mem_convexHull'] at hx
  obtain ⟨w, hw_nonneg, hw_sum, hw_repr⟩ := hx
  obtain ⟨a, ha, hmin⟩ := s.exists_min_image w hs
  let m : ℝ := w a
  let q : ℝ := 1 - (s.card : ℝ) * m
  have hm_nonneg : 0 ≤ m := hw_nonneg a ha
  have hcardm_le : (s.card : ℝ) * m ≤ 1 := by
    calc
      (s.card : ℝ) * m = ∑ y ∈ s, m := by
        simp [nsmul_eq_mul]
      _ ≤ ∑ y ∈ s, w y := by
        exact Finset.sum_le_sum fun y hy => hmin y hy
      _ = 1 := hw_sum
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    linarith
  by_cases hq : q = 0
  · have hdiff_nonneg : ∀ y ∈ s, 0 ≤ w y - m := by
      intro y hy
      exact sub_nonneg.mpr (hmin y hy)
    have hdiff_sum : ∑ y ∈ s, (w y - m) = 0 := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hw_sum]
      dsimp [q] at hq
      nlinarith
    have hweq : ∀ y ∈ s, w y = m := by
      intro y hy
      have hyzero :=
        (Finset.sum_eq_zero_iff_of_nonneg hdiff_nonneg).mp hdiff_sum y hy
      linarith
    have hcard_ne : (s.card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr hs
    have hm : m = (s.card : ℝ)⁻¹ := by
      field_simp
      dsimp [q] at hq
      nlinarith
    have hcentroid : s.centroid ℝ id = x := by
      rw [Finset.centroid_def,
        Finset.affineCombination_eq_linear_combination _ _ _
          (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs)]
      simp only [Finset.centroidWeights_apply, id_eq]
      calc
        ∑ y ∈ s, (s.card : ℝ)⁻¹ • y = ∑ y ∈ s, w y • y := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [hweq y hy, hm]
        _ = x := hw_repr
    refine ⟨{s}, Finset.singleton_nonempty s, ?_, ?_, ?_⟩
    · intro F hF
      rw [Finset.mem_singleton.mp hF]
      exact ⟨hs, Finset.Subset.rfl⟩
    · intro F hF G hG
      rw [Finset.mem_singleton.mp hF, Finset.mem_singleton.mp hG]
      exact Or.inl Finset.Subset.rfl
    · rw [← hcentroid]
      apply subset_convexHull ℝ
      exact ⟨s, Finset.mem_singleton_self s, rfl⟩
  · have hq_pos : 0 < q := lt_of_le_of_ne hq_nonneg (Ne.symm hq)
    let t : Finset (C → ℝ) := s.erase a
    have ht_ssubset : t ⊂ s := by
      exact Finset.erase_ssubset ha
    have ht : t.Nonempty := by
      by_contra ht_empty
      have ht_eq : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht_empty
      have hs_cases : s = ∅ ∨ s = {a} := by
        exact (Finset.erase_eq_empty_iff s a).mp ht_eq
      have hs_single : s = {a} := hs_cases.resolve_left
        (Finset.nonempty_iff_ne_empty.mp hs)
      have hwa : w a = 1 := by
        simpa [hs_single] using hw_sum
      apply hq
      simp [q, m, hs_single, hwa]
    let w' : (C → ℝ) → ℝ := fun y => (w y - m) / q
    have hw'_nonneg : ∀ y ∈ t, 0 ≤ w' y := by
      intro y hy
      have hys : y ∈ s := (Finset.erase_subset a s) hy
      exact div_nonneg (sub_nonneg.mpr (hmin y hys)) (le_of_lt hq_pos)
    have hsum_erase : ∑ y ∈ t, w y = 1 - m := by
      have herase := Finset.sum_erase_add s w ha
      dsimp [t]
      dsimp [m]
      linarith
    have hcard_t : (t.card : ℝ) = (s.card : ℝ) - 1 := by
      have hcard_nat : t.card = s.card - 1 := by
        simpa [t] using Finset.card_erase_of_mem ha
      rw [hcard_nat]
      rw [Nat.cast_sub (Finset.one_le_card.mpr hs)]
      norm_num
    have hnum : ∑ y ∈ t, (w y - m) = q := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hsum_erase, hcard_t]
      dsimp [q]
      ring
    have hw'_sum : ∑ y ∈ t, w' y = 1 := by
      calc
        ∑ y ∈ t, w' y = (∑ y ∈ t, (w y - m)) / q := by
          dsimp [w']
          exact (Finset.sum_div t (fun y => w y - m) q).symm
        _ = q / q := by rw [hnum]
        _ = 1 := div_self (ne_of_gt hq_pos)
    let x' : C → ℝ := ∑ y ∈ t, w' y • y
    have hx' : x' ∈ convexHull ℝ (t : Set (C → ℝ)) := by
      rw [Finset.mem_convexHull']
      exact ⟨w', hw'_nonneg, hw'_sum, rfl⟩
    obtain ⟨ℱ, hℱ_nonempty, hℱ_faces, hℱ_chain, hx'_chain⟩ :=
      ih t ht_ssubset ht x' hx'
    let ℱ' : Finset (Finset (C → ℝ)) := insert s ℱ
    have hℱ'_nonempty : ℱ'.Nonempty := by
      exact ⟨s, Finset.mem_insert_self s ℱ⟩
    have hℱ'_faces : ∀ F ∈ ℱ', F.Nonempty ∧ F ⊆ s := by
      intro F hF
      rcases Finset.mem_insert.mp hF with rfl | hF
      · exact ⟨hs, Finset.Subset.rfl⟩
      · exact ⟨(hℱ_faces F hF).1,
          (hℱ_faces F hF).2.trans (Finset.erase_subset a s)⟩
    have hℱ'_chain : ∀ F ∈ ℱ', ∀ G ∈ ℱ', F ⊆ G ∨ G ⊆ F := by
      intro F hF G hG
      rcases Finset.mem_insert.mp hF with rfl | hF
      · exact Or.inr (hℱ'_faces G hG).2
      · rcases Finset.mem_insert.mp hG with rfl | hG
        · exact Or.inl (hℱ'_faces F hF).2
        · exact hℱ_chain F hF G hG
    have hx'_big :
        x' ∈ convexHull ℝ {y | ∃ F ∈ ℱ', y = F.centroid ℝ id} := by
      apply (convexHull_mono _ ) hx'_chain
      intro y hy
      obtain ⟨F, hF, rfl⟩ := hy
      exact ⟨F, Finset.mem_insert_of_mem hF, rfl⟩
    have hcentroid_mem :
        s.centroid ℝ id ∈ {y | ∃ F ∈ ℱ', y = F.centroid ℝ id} :=
      ⟨s, Finset.mem_insert_self s ℱ, rfl⟩
    have hcentroid_hull :
        s.centroid ℝ id ∈
          convexHull ℝ {y | ∃ F ∈ ℱ', y = F.centroid ℝ id} :=
      (show {y | ∃ F ∈ ℱ', y = F.centroid ℝ id} ⊆
          convexHull ℝ {y | ∃ F ∈ ℱ', y = F.centroid ℝ id} from
        subset_convexHull ℝ {y | ∃ F ∈ ℱ', y = F.centroid ℝ id})
          hcentroid_mem
    have hcard_ne : (s.card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr hs
    have hcentroid_scaled :
        ((s.card : ℝ) * m) • s.centroid ℝ id =
          ∑ y ∈ s, m • y := by
      rw [Finset.centroid_def,
        Finset.affineCombination_eq_linear_combination _ _ _
          (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs)]
      simp only [Finset.centroidWeights_apply, id_eq, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      rw [smul_smul]
      congr 1
      field_simp
    have hx'_scaled : q • x' = ∑ y ∈ t, (w y - m) • y := by
      dsimp [x']
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      rw [smul_smul]
      congr 1
      dsimp [w']
      field_simp
    have hsum_vectors :
        (∑ y ∈ s, m • y) + (∑ y ∈ t, (w y - m) • y) =
          ∑ y ∈ s, w y • y := by
      have hm_split := Finset.sum_erase_add s (fun y => m • y) ha
      have hw_split := Finset.sum_erase_add s (fun y => w y • y) ha
      dsimp [t] at *
      rw [← hw_split]
      calc
        (∑ y ∈ s, m • y) + ∑ y ∈ s.erase a, (w y - m) • y =
            ((∑ y ∈ s.erase a, m • y) +
              ∑ y ∈ s.erase a, (w y - m) • y) + m • a := by
          rw [← hm_split]
          abel
        _ = (∑ y ∈ s.erase a, w y • y) + w a • a := by
          congr 1
          · rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro y hy
            rw [sub_smul]
            abel
    have hx_decomp :
        x = ((s.card : ℝ) * m) • s.centroid ℝ id + q • x' := by
      rw [hcentroid_scaled, hx'_scaled, hsum_vectors, hw_repr]
    refine ⟨ℱ', hℱ'_nonempty, hℱ'_faces, hℱ'_chain, ?_⟩
    rw [hx_decomp]
    exact (convex_convexHull ℝ _)
      hcentroid_hull hx'_big (mul_nonneg (Nat.cast_nonneg _) hm_nonneg)
        hq_nonneg (by dsimp [q]; ring)

@[blueprint "lem:barycentric-face-chain-cover"
  (statement := /-- Let \(C\) be a nonempty finite type and let \(K\) be a finite
  triangulation of \(\Delta(C)\). The convex hulls of all barycentric face-chain
  cells of \(K\) cover \(\Delta(C)\). -/)
  (proof := /-- For each cell \(\sigma\) of \(K\), apply
  \cref{lem:finite-convex-hull-barycentric-chain-cover} to its finite nonempty vertex
  set. Every point of \(\operatorname{conv}(\sigma)\) then lies in the convex hull of
  the centroids of a nonempty inclusion-chain of nonempty faces of \(\sigma\). These
  centroid sets are barycentric face-chain cells by
  \cref{def:barycentric-face-chain-cell}. The cover axiom in
  \cref{def:finite-simplex-triangulation} therefore shows that the standard simplex
  is contained in the stated union.

  Conversely, every centroid in a barycentric face-chain cell lies in the convex hull
  of its face, hence in the convex hull of its supporting cell and therefore in the
  standard simplex by \cref{def:finite-simplex-triangulation}. Convexity of the
  standard simplex places the convex hull of every barycentric face-chain cell inside
  it, proving the reverse containment. -/)
  (title := /-- Barycentric face-chain cells cover the simplex -/)
  (latexEnv := "lemma")]
lemma barycentric_face_chain_cover {C : Type*}
    [Fintype C] [Nonempty C] (K : finite_simplex_triangulation C) :
    stdSimplex ℝ C =
      ⋃ τ ∈ {τ : Set (C → ℝ) | barycentric_face_chain_cell K τ},
        convexHull ℝ τ := by
  classical
  apply Set.Subset.antisymm
  · rw [K.cover]
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨σ, hx⟩
    rcases Set.mem_iUnion.1 hx with ⟨hσ, hxσ⟩
    let s : Finset (C → ℝ) := (K.finite_vertices σ hσ).toFinset
    have hs_coe : (s : Set (C → ℝ)) = σ := by
      exact (K.finite_vertices σ hσ).coe_toFinset
    have hs : s.Nonempty := by
      simpa [s] using K.nonempty_cells σ hσ
    have hx_s : x ∈ convexHull ℝ (s : Set (C → ℝ)) := by
      simpa [hs_coe] using hxσ
    obtain ⟨ℱ, hℱ_nonempty, hℱ_faces, hℱ_chain, hx_chain⟩ :=
      finite_convex_hull_barycentric_chain_cover s hs x hx_s
    let τ : Set (C → ℝ) := {y | ∃ F ∈ ℱ, y = F.centroid ℝ id}
    have hτ : barycentric_face_chain_cell K τ := by
      refine ⟨σ, hσ, ℱ, hℱ_nonempty, ?_, hℱ_chain, rfl⟩
      intro F hF
      refine ⟨(hℱ_faces F hF).1, ?_⟩
      intro z hz
      rw [← hs_coe]
      exact (hℱ_faces F hF).2 hz
    apply Set.mem_iUnion.2
    refine ⟨τ, Set.mem_iUnion.2 ⟨hτ, ?_⟩⟩
    exact hx_chain
  · intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨τ, hx⟩
    rcases Set.mem_iUnion.1 hx with ⟨hτ, hxτ⟩
    apply (convexHull_min _ (convex_stdSimplex ℝ C)) hxτ
    intro y hy
    obtain ⟨σ, hσ, ℱ, hℱ_nonempty, hℱ_faces, hℱ_chain, rfl⟩ := hτ
    obtain ⟨F, hF, rfl⟩ := hy
    apply (convexHull_min _ (convex_stdSimplex ℝ C))
      ((convexHull_mono (hℱ_faces F hF).2)
        (Finset.centroid_mem_convexHull F (hℱ_faces F hF).1))
    intro z hz
    exact K.vertices_mem_standard_simplex σ hσ z hz

@[blueprint "lem:barycentric-centroid-injective-of-affine-independent"
  (statement := /-- Let \(C\) be a finite nonempty type, let \(\sigma\) be an affinely
  independent finite set in \(\mathbb R^C\), and let \(F,G\) be nonempty subsets of
  \(\sigma\). If \(F\) and \(G\) have the same centroid, then \(F=G\). -/)
  (proof := /-- Express both centroids in the affine coordinates of \(\sigma\). The
  coefficient of a vertex is \(1/|F|\) on \(F\) and zero off \(F\), and similarly for
  \(G\). Affine independence makes these coordinate functions equal. Their supports
  are therefore equal, which gives \(F=G\). -/)
  (title := /-- Centroids distinguish nonempty faces of a simplex -/)
  (latexEnv := "lemma")]
lemma barycentric_centroid_injective_of_affine_independent {C : Type*}
    [Fintype C] [Nonempty C] (σ F G : Finset (C → ℝ))
    (hσ : AffineIndependent ℝ ((↑) : σ → (C → ℝ)))
    (hF : F.Nonempty) (hFσ : F ⊆ σ) (hG : G.Nonempty) (hGσ : G ⊆ σ)
    (hcentroid : F.centroid ℝ id = G.centroid ℝ id) : F = G := by
  classical
  let wF : (C → ℝ) → ℝ := fun v => if v ∈ F then (F.card : ℝ)⁻¹ else 0
  let wG : (C → ℝ) → ℝ := fun v => if v ∈ G then (G.card : ℝ)⁻¹ else 0
  have hFcard : (F.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hF
  have hGcard : (G.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hG
  have hsumF : ∑ v ∈ σ, wF v = 1 := by
    rw [← Finset.sum_subset hFσ]
    · simp [wF, hFcard]
    · intro v hvσ hvF
      simp [wF, hvF]
  have hsumG : ∑ v ∈ σ, wG v = 1 := by
    rw [← Finset.sum_subset hGσ]
    · simp [wG, hGcard]
    · intro v hvσ hvG
      simp [wG, hvG]
  have hlinearF : ∑ v ∈ σ, wF v • v = F.centroid ℝ id := by
    rw [← Finset.sum_subset hFσ]
    · rw [Finset.centroid_def,
        Finset.affineCombination_eq_linear_combination _ _ _
          (F.sum_centroidWeights_eq_one_of_nonempty ℝ hF)]
      simp [wF]
    · intro v hvσ hvF
      simp [wF, hvF]
  have hlinearG : ∑ v ∈ σ, wG v • v = G.centroid ℝ id := by
    rw [← Finset.sum_subset hGσ]
    · rw [Finset.centroid_def,
        Finset.affineCombination_eq_linear_combination _ _ _
          (G.sum_centroidWeights_eq_one_of_nonempty ℝ hG)]
      simp [wG]
    · intro v hvσ hvG
      simp [wG, hvG]
  apply Finset.Subset.antisymm
  · intro v hvF
    have hvσ := hFσ hvF
    have hw := hσ.eq_of_sum_eq_sum_subtype (hsumF.trans hsumG.symm)
      (hlinearF.trans (hcentroid.trans hlinearG.symm)) v hvσ
    by_contra hvG
    simp [wF, wG, hvF, hvG, hFcard] at hw
  · intro v hvG
    have hvσ := hGσ hvG
    have hw := hσ.eq_of_sum_eq_sum_subtype (hsumF.trans hsumG.symm)
      (hlinearF.trans (hcentroid.trans hlinearG.symm)) v hvσ
    by_contra hvF
    simp [wF, wG, hvF, hvG, hGcard] at hw
    exact hGcard hw.symm

@[blueprint "lem:barycentric-positive-face-recovery"
  (statement := /-- Let \(\mathcal F\) and \(\mathcal G\) be nonempty finite chains of
  nonempty subsets of a finite set \(S\). Give the members of each chain nonnegative
  weights, and suppose the resulting weighted sums of normalized indicator functions
  agree on \(S\). Every member of \(\mathcal F\) having positive weight then belongs to
  \(\mathcal G\). -/)
  (proof := /-- A positively weighted \(F\in\mathcal F\) creates a strict coordinate
  gap: every coordinate indexed by \(F\) is larger than every coordinate outside
  \(F\). An incomparable member of \(\mathcal G\) would reverse this inequality, so all
  members of \(\mathcal G\) are comparable with \(F\). Choose a largest member below
  \(F\). If \(F=S\), a point outside that member has positive first coordinate and
  zero second coordinate. Otherwise choose a smallest member above \(F\); points in
  the two successive set differences have equal second coordinates, contradicting
  the strict gap. Hence \(F\in\mathcal G\). -/)
  (title := /-- Positive coefficients recover faces in a barycentric chain -/)
  (latexEnv := "lemma")]
lemma barycentric_positive_face_recovery {E : Type*} [DecidableEq E]
    (S : Finset E) (ℱ 𝒢 : Finset (Finset E)) (a b : Finset E → ℝ)
    (hℱ_nonempty : ℱ.Nonempty) (h𝒢_nonempty : 𝒢.Nonempty)
    (hℱ_faces : ∀ F ∈ ℱ, F.Nonempty ∧ F ⊆ S)
    (h𝒢_faces : ∀ G ∈ 𝒢, G.Nonempty ∧ G ⊆ S)
    (hℱ_chain : ∀ F ∈ ℱ, ∀ G ∈ ℱ, F ⊆ G ∨ G ⊆ F)
    (h𝒢_chain : ∀ F ∈ 𝒢, ∀ G ∈ 𝒢, F ⊆ G ∨ G ⊆ F)
    (ha : ∀ F ∈ ℱ, 0 ≤ a F) (hb : ∀ G ∈ 𝒢, 0 ≤ b G)
    (hcoord : ∀ v ∈ S,
      (∑ F ∈ ℱ, a F * if v ∈ F then (F.card : ℝ)⁻¹ else 0) =
        ∑ G ∈ 𝒢, b G * if v ∈ G then (G.card : ℝ)⁻¹ else 0)
    {F : Finset E} (hFℱ : F ∈ ℱ) (haF : 0 < a F) : F ∈ 𝒢 := by
  classical
  have hF_nonempty := (hℱ_faces F hFℱ).1
  have hFS := (hℱ_faces F hFℱ).2
  have hFcard : 0 < (F.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hF_nonempty
  have hsep : ∀ p ∈ F, ∀ q ∈ S, q ∉ F →
      (∑ H ∈ ℱ, a H * if q ∈ H then (H.card : ℝ)⁻¹ else 0) <
        ∑ H ∈ ℱ, a H * if p ∈ H then (H.card : ℝ)⁻¹ else 0 := by
    intro p hpF q hqS hqF
    apply Finset.sum_lt_sum
    · intro H hHℱ
      by_cases hqH : q ∈ H
      · have hpH : p ∈ H := by
          rcases hℱ_chain F hFℱ H hHℱ with hFH | hHF
          · exact hFH hpF
          · exact False.elim (hqF (hHF hqH))
        simp [hqH, hpH]
      · by_cases hpH : p ∈ H
        · simp only [hqH, hpH, if_false, if_true, mul_zero]
          exact mul_nonneg (ha H hHℱ) (inv_nonneg.mpr (Nat.cast_nonneg _))
        · simp [hqH, hpH]
    · refine ⟨F, hFℱ, ?_⟩
      simp only [hqF, hpF, if_false, if_true, mul_zero]
      exact mul_pos haF (inv_pos.mpr hFcard)
  by_contra hF𝒢
  have hcomparable : ∀ G ∈ 𝒢, G ⊆ F ∨ F ⊆ G := by
    intro G hG𝒢
    by_contra hcomp
    push Not at hcomp
    obtain ⟨p, hpF, hpG⟩ := Finset.not_subset.mp hcomp.2
    obtain ⟨q, hqG, hqF⟩ := Finset.not_subset.mp hcomp.1
    have hpS := hFS hpF
    have hqS := (h𝒢_faces G hG𝒢).2 hqG
    have hmono :
        (∑ H ∈ 𝒢, b H * if p ∈ H then (H.card : ℝ)⁻¹ else 0) ≤
          ∑ H ∈ 𝒢, b H * if q ∈ H then (H.card : ℝ)⁻¹ else 0 := by
      apply Finset.sum_le_sum
      intro H hH𝒢
      by_cases hpH : p ∈ H
      · have hqH : q ∈ H := by
          rcases h𝒢_chain G hG𝒢 H hH𝒢 with hGH | hHG
          · exact hGH hqG
          · exact False.elim (hpG (hHG hpH))
        simp [hpH, hqH]
      · simp only [hpH, if_false, mul_zero]
        by_cases hqH : q ∈ H
        · simp only [hqH, if_true]
          exact mul_nonneg (hb H hH𝒢) (inv_nonneg.mpr (Nat.cast_nonneg _))
        · simp [hqH]
    have hstrict := hsep p hpF q hqS hqF
    rw [hcoord p hpS, hcoord q hqS] at hstrict
    exact (not_lt_of_ge hmono) hstrict
  let below := 𝒢.filter fun G => G ⊆ F
  obtain ⟨B, hBF, hBmax, hBsource⟩ :
      ∃ B : Finset E, B ⊆ F ∧
        (∀ G ∈ 𝒢, G ⊆ F → G ⊆ B) ∧ (B = ∅ ∨ B ∈ 𝒢) := by
    by_cases hbelow : below.Nonempty
    · obtain ⟨B, hBbelow, hBcard⟩ := Finset.exists_max_image below Finset.card hbelow
      refine ⟨B, (Finset.mem_filter.mp hBbelow).2, ?_, Or.inr (Finset.mem_filter.mp hBbelow).1⟩
      intro G hG𝒢 hGF
      have hGbelow : G ∈ below := Finset.mem_filter.mpr ⟨hG𝒢, hGF⟩
      rcases h𝒢_chain B (Finset.mem_filter.mp hBbelow).1 G hG𝒢 with hBG | hGB
      · have hcard := hBcard G hGbelow
        exact (Finset.eq_of_subset_of_card_le hBG hcard).ge
      · exact hGB
    · refine ⟨∅, Finset.empty_subset _, ?_, Or.inl rfl⟩
      intro G hG𝒢 hGF
      exact False.elim (hbelow ⟨G, Finset.mem_filter.mpr ⟨hG𝒢, hGF⟩⟩)
  have hBF_ne : B ≠ F := by
    intro hBF_eq
    rcases hBsource with hBempty | hB𝒢
    · exact hF_nonempty.ne_empty (hBF_eq.symm.trans hBempty)
    · exact hF𝒢 (hBF_eq ▸ hB𝒢)
  obtain ⟨p, hpF, hpB⟩ := Finset.not_subset.mp fun hFB => hBF_ne (Finset.Subset.antisymm hBF hFB)
  have hpS := hFS hpF
  by_cases hFS_eq : F = S
  · have hright_zero :
        (∑ G ∈ 𝒢, b G * if p ∈ G then (G.card : ℝ)⁻¹ else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro G hG𝒢
      have hGF : G ⊆ F := hFS_eq ▸ (h𝒢_faces G hG𝒢).2
      have hGB := hBmax G hG𝒢 hGF
      simp [show p ∉ G by exact fun hpG => hpB (hGB hpG)]
    have hleft_pos : 0 <
        ∑ H ∈ ℱ, a H * if p ∈ H then (H.card : ℝ)⁻¹ else 0 := by
      apply Finset.sum_pos'
      · intro H hHℱ
        by_cases hpH : p ∈ H
        · simp only [hpH, if_true]
          exact mul_nonneg (ha H hHℱ) (inv_nonneg.mpr (Nat.cast_nonneg _))
        · simp [hpH]
      · refine ⟨F, hFℱ, ?_⟩
        simp only [hpF, if_true]
        exact mul_pos haF (inv_pos.mpr hFcard)
    rw [hcoord p hpS, hright_zero] at hleft_pos
    exact (lt_irrefl 0) hleft_pos
  · obtain ⟨q₀, hq₀S, hq₀F⟩ := Finset.not_subset.mp fun hSF => hFS_eq (Finset.Subset.antisymm hFS hSF)
    have hright_nonneg : 0 ≤
        ∑ G ∈ 𝒢, b G * if q₀ ∈ G then (G.card : ℝ)⁻¹ else 0 := by
      apply Finset.sum_nonneg
      intro G hG𝒢
      by_cases hqG : q₀ ∈ G
      · simp only [hqG, if_true]
        exact mul_nonneg (hb G hG𝒢) (inv_nonneg.mpr (Nat.cast_nonneg _))
      · simp [hqG]
    have hp_positive : 0 <
        ∑ G ∈ 𝒢, b G * if p ∈ G then (G.card : ℝ)⁻¹ else 0 := by
      have hs := hsep p hpF q₀ hq₀S hq₀F
      rw [hcoord p hpS, hcoord q₀ hq₀S] at hs
      exact lt_of_le_of_lt hright_nonneg hs
    have habove_nonempty : (𝒢.filter fun G => F ⊆ G).Nonempty := by
      have hterms : ∀ G ∈ 𝒢,
          0 ≤ b G * if p ∈ G then (G.card : ℝ)⁻¹ else 0 := by
        intro G hG𝒢
        by_cases hpG : p ∈ G
        · simp only [hpG, if_true]
          exact mul_nonneg (hb G hG𝒢) (inv_nonneg.mpr (Nat.cast_nonneg _))
        · simp [hpG]
      obtain ⟨G, hG𝒢, hGpos⟩ := (Finset.sum_pos_iff_of_nonneg hterms).mp hp_positive
      have hpG : p ∈ G := by
        by_contra hpG
        simp [hpG] at hGpos
      rcases hcomparable G hG𝒢 with hGF | hFG
      · exact False.elim (hpB (hBmax G hG𝒢 hGF hpG))
      · exact ⟨G, Finset.mem_filter.mpr ⟨hG𝒢, hFG⟩⟩
    obtain ⟨A, hAabove, hAcard⟩ :=
      Finset.exists_min_image (𝒢.filter fun G => F ⊆ G) Finset.card habove_nonempty
    have hA𝒢 := (Finset.mem_filter.mp hAabove).1
    have hFA := (Finset.mem_filter.mp hAabove).2
    have hAmin : ∀ G ∈ 𝒢, F ⊆ G → A ⊆ G := by
      intro G hG𝒢 hFG
      have hGabove : G ∈ 𝒢.filter fun H => F ⊆ H := Finset.mem_filter.mpr ⟨hG𝒢, hFG⟩
      rcases h𝒢_chain A hA𝒢 G hG𝒢 with hAG | hGA
      · exact hAG
      · have hcard := hAcard G hGabove
        exact (Finset.eq_of_subset_of_card_le hGA hcard).symm.le
    have hFA_ne : F ≠ A := fun h => hF𝒢 (h ▸ hA𝒢)
    obtain ⟨q, hqA, hqF⟩ := Finset.not_subset.mp fun hAF => hFA_ne (Finset.Subset.antisymm hFA hAF)
    have hqS := (h𝒢_faces A hA𝒢).2 hqA
    have hmem_iff : ∀ G ∈ 𝒢, p ∈ G ↔ q ∈ G := by
      intro G hG𝒢
      rcases hcomparable G hG𝒢 with hGF | hFG
      · have hGB := hBmax G hG𝒢 hGF
        constructor
        · intro hpG
          exact False.elim (hpB (hGB hpG))
        · intro hqG
          exact False.elim (hqF (hGF hqG))
      · have hAG := hAmin G hG𝒢 hFG
        exact ⟨fun _ => hAG hqA, fun _ => hFG hpF⟩
    have heq :
        (∑ G ∈ 𝒢, b G * if p ∈ G then (G.card : ℝ)⁻¹ else 0) =
          ∑ G ∈ 𝒢, b G * if q ∈ G then (G.card : ℝ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro G hG𝒢
      rw [if_congr (hmem_iff G hG𝒢) rfl rfl]
    have hs := hsep p hpF q hqS hqF
    rw [hcoord p hpS, hcoord q hqS, heq] at hs
    exact (lt_irrefl _) hs

@[blueprint "lem:barycentric-weighted-centroid-expansion"
  (statement := /-- Let \(\mathcal F\) be a finite family of nonempty subsets of a
  finite set \(\sigma\subseteq\mathbb R^C\), and attach a real weight \(a_F\) to every
  \(F\in\mathcal F\). The weighted sum of the centroids of the \(F\)'s equals the
  linear combination of the vertices of \(\sigma\) whose coefficient at \(v\) is
  \(\sum_{F\ni v}a_F/|F|\). -/)
  (proof := /-- Expand each centroid as the average of the vertices of its nonempty
  face. Distribute its outer weight through this sum, extend each face sum to
  \(\sigma\) by zero, and interchange the two finite sums. -/)
  (title := /-- Vertex expansion of weighted face centroids -/)
  (latexEnv := "lemma")]
lemma barycentric_weighted_centroid_expansion {C : Type*}
    [Fintype C] [Nonempty C] (σ : Finset (C → ℝ))
    (ℱ : Finset (Finset (C → ℝ))) (a : Finset (C → ℝ) → ℝ)
    (hfaces : ∀ F ∈ ℱ, F.Nonempty ∧ F ⊆ σ) :
    (∑ F ∈ ℱ, a F • F.centroid ℝ id) =
      ∑ v ∈ σ, (∑ F ∈ ℱ,
        a F * if v ∈ F then (F.card : ℝ)⁻¹ else 0) • v := by
  classical
  calc
    (∑ F ∈ ℱ, a F • F.centroid ℝ id) =
        ∑ F ∈ ℱ, ∑ v ∈ F, (a F * (F.card : ℝ)⁻¹) • v := by
      apply Finset.sum_congr rfl
      intro F hFℱ
      rw [Finset.centroid_def,
        Finset.affineCombination_eq_linear_combination _ _ _
          (F.sum_centroidWeights_eq_one_of_nonempty ℝ (hfaces F hFℱ).1)]
      simp_rw [Finset.smul_sum, smul_smul]
      simp
    _ = ∑ F ∈ ℱ, ∑ v ∈ σ,
        (a F * if v ∈ F then (F.card : ℝ)⁻¹ else 0) • v := by
      apply Finset.sum_congr rfl
      intro F hFℱ
      rw [← Finset.sum_subset (hfaces F hFℱ).2]
      · apply Finset.sum_congr rfl
        intro v hvF
        simp [hvF]
      · intro v hvσ hvF
        simp [hvF]
    _ = ∑ v ∈ σ, (∑ F ∈ ℱ,
        a F * if v ∈ F then (F.card : ℝ)⁻¹ else 0) • v := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v hvσ
      rw [Finset.sum_smul]

@[blueprint "lem:barycentric-chain-coordinate-sum"
  (statement := /-- In the setting of
  \cref{lem:barycentric-weighted-centroid-expansion}, if the face weights sum to
  one, then the induced coefficients on the vertices of \(\sigma\) also sum to one. -/)
  (proof := /-- Interchange the finite sums. For each nonempty face \(F\), its
  normalized indicator has sum \(|F|/|F|=1\). The resulting sum is therefore the
  original sum of the face weights. -/)
  (title := /-- Normalization of induced vertex coordinates -/)
  (latexEnv := "lemma")]
lemma barycentric_chain_coordinate_sum {C : Type*}
    [Fintype C] [Nonempty C] (σ : Finset (C → ℝ))
    (ℱ : Finset (Finset (C → ℝ))) (a : Finset (C → ℝ) → ℝ)
    (hfaces : ∀ F ∈ ℱ, F.Nonempty ∧ F ⊆ σ)
    (hsum : ∑ F ∈ ℱ, a F = 1) :
    (∑ v ∈ σ, ∑ F ∈ ℱ,
      a F * if v ∈ F then (F.card : ℝ)⁻¹ else 0) = 1 := by
  classical
  calc
    (∑ v ∈ σ, ∑ F ∈ ℱ,
        a F * if v ∈ F then (F.card : ℝ)⁻¹ else 0) =
        ∑ F ∈ ℱ, ∑ v ∈ σ,
          a F * if v ∈ F then (F.card : ℝ)⁻¹ else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ F ∈ ℱ, a F := by
      apply Finset.sum_congr rfl
      intro F hFℱ
      rw [← Finset.mul_sum]
      rw [← Finset.sum_subset (hfaces F hFℱ).2]
      · have hcard : (F.card : ℝ) ≠ 0 := by
          exact_mod_cast Finset.card_ne_zero.mpr (hfaces F hFℱ).1
        simp [hcard]
      · intro v hvσ hvF
        simp [hvF]
    _ = 1 := hsum

@[blueprint "lem:barycentric-chains-in-one-simplex-intersection"
  (statement := /-- Let \(\sigma\subseteq\mathbb R^C\) be a finite affinely independent
  set, and let \(\mathcal F,\mathcal G\) be nonempty chains of nonempty faces of
  \(\sigma\). The convex hulls of their respective face centroids meet in the convex
  hull of the centroids common to the two chains. -/)
  (proof := /-- By
  \cref{lem:barycentric-centroid-injective-of-affine-independent}, distinct faces
  have distinct centroids. Take convex coefficients for a point in the two hulls and
  use \cref{lem:barycentric-weighted-centroid-expansion} together with
  \cref{lem:barycentric-chain-coordinate-sum} to express both combinations in the
  unique affine coordinates of \(\sigma\). The coordinate functions agree. Applying
  \cref{lem:barycentric-positive-face-recovery} in both directions shows that
  every centroid with positive coefficient belongs to both chains. Removing the
  zero coefficients leaves a convex combination of precisely the common centroids.
  The reverse inclusion follows from monotonicity of the convex hull. -/)
  (title := /-- Intersection of barycentric chain simplices in one simplex -/)
  (latexEnv := "lemma")]
lemma barycentric_chains_in_one_simplex_intersection {C : Type*}
    [Fintype C] [Nonempty C] (σ : Finset (C → ℝ))
    (hσ : AffineIndependent ℝ ((↑) : σ → (C → ℝ)))
    (ℱ 𝒢 : Finset (Finset (C → ℝ)))
    (hℱ_nonempty : ℱ.Nonempty) (h𝒢_nonempty : 𝒢.Nonempty)
    (hℱ_faces : ∀ F ∈ ℱ, F.Nonempty ∧ F ⊆ σ)
    (h𝒢_faces : ∀ G ∈ 𝒢, G.Nonempty ∧ G ⊆ σ)
    (hℱ_chain : ∀ F ∈ ℱ, ∀ G ∈ ℱ, F ⊆ G ∨ G ⊆ F)
    (h𝒢_chain : ∀ F ∈ 𝒢, ∀ G ∈ 𝒢, F ⊆ G ∨ G ⊆ F) :
    convexHull ℝ (↑(ℱ.image fun F => F.centroid ℝ id) : Set (C → ℝ)) ∩
        convexHull ℝ (↑(𝒢.image fun G => G.centroid ℝ id) : Set (C → ℝ)) =
      convexHull ℝ
        ((↑(ℱ.image fun F => F.centroid ℝ id) : Set (C → ℝ)) ∩
          (↑(𝒢.image fun G => G.centroid ℝ id) : Set (C → ℝ))) := by
  classical
  let c : Finset (C → ℝ) → (C → ℝ) := fun F => F.centroid ℝ id
  let T := ℱ.image c
  let U := 𝒢.image c
  change convexHull ℝ (T : Set (C → ℝ)) ∩ convexHull ℝ (U : Set (C → ℝ)) =
    convexHull ℝ ((T : Set (C → ℝ)) ∩ (U : Set (C → ℝ)))
  have hcℱ : Set.InjOn c (ℱ : Set (Finset (C → ℝ))) := by
    intro F hFℱ G hGℱ hFG
    exact barycentric_centroid_injective_of_affine_independent σ F G hσ
      (hℱ_faces F hFℱ).1 (hℱ_faces F hFℱ).2
      (hℱ_faces G hGℱ).1 (hℱ_faces G hGℱ).2 hFG
  have hc𝒢 : Set.InjOn c (𝒢 : Set (Finset (C → ℝ))) := by
    intro F hF𝒢 G hG𝒢 hFG
    exact barycentric_centroid_injective_of_affine_independent σ F G hσ
      (h𝒢_faces F hF𝒢).1 (h𝒢_faces F hF𝒢).2
      (h𝒢_faces G hG𝒢).1 (h𝒢_faces G hG𝒢).2 hFG
  apply Set.Subset.antisymm
  · intro x hx
    rcases (Finset.mem_convexHull').mp hx.1 with ⟨w, hw, hsumw, hxw⟩
    rcases (Finset.mem_convexHull').mp hx.2 with ⟨z, hz, hsumz, hxz⟩
    let a : Finset (C → ℝ) → ℝ := fun F => w (c F)
    let b : Finset (C → ℝ) → ℝ := fun G => z (c G)
    have ha : ∀ F ∈ ℱ, 0 ≤ a F := by
      intro F hFℱ
      exact hw (c F) (by exact Finset.mem_image.mpr ⟨F, hFℱ, rfl⟩)
    have hb : ∀ G ∈ 𝒢, 0 ≤ b G := by
      intro G hG𝒢
      exact hz (c G) (by exact Finset.mem_image.mpr ⟨G, hG𝒢, rfl⟩)
    have hsuma : ∑ F ∈ ℱ, a F = 1 := by
      change ∑ F ∈ ℱ, w (c F) = 1
      rw [← Finset.sum_image hcℱ]
      exact hsumw
    have hsumb : ∑ G ∈ 𝒢, b G = 1 := by
      change ∑ G ∈ 𝒢, z (c G) = 1
      rw [← Finset.sum_image hc𝒢]
      exact hsumz
    have hfacea : ∑ F ∈ ℱ, a F • F.centroid ℝ id = x := by
      change ∑ F ∈ ℱ, w (c F) • c F = x
      exact (Finset.sum_image (f := fun y => w y • y) hcℱ).symm.trans hxw
    have hfaceb : ∑ G ∈ 𝒢, b G • G.centroid ℝ id = x := by
      change ∑ G ∈ 𝒢, z (c G) • c G = x
      exact (Finset.sum_image (f := fun y => z y • y) hc𝒢).symm.trans hxz
    have hvertexa :
        (∑ v ∈ σ, (∑ F ∈ ℱ,
          a F * if v ∈ F then (F.card : ℝ)⁻¹ else 0) • v) = x :=
      (barycentric_weighted_centroid_expansion σ ℱ a hℱ_faces).symm.trans hfacea
    have hvertexb :
        (∑ v ∈ σ, (∑ G ∈ 𝒢,
          b G * if v ∈ G then (G.card : ℝ)⁻¹ else 0) • v) = x :=
      (barycentric_weighted_centroid_expansion σ 𝒢 b h𝒢_faces).symm.trans hfaceb
    have hcoordsuma :
        (∑ v ∈ σ, ∑ F ∈ ℱ,
          a F * if v ∈ F then (F.card : ℝ)⁻¹ else 0) = 1 :=
      barycentric_chain_coordinate_sum σ ℱ a hℱ_faces hsuma
    have hcoordsumb :
        (∑ v ∈ σ, ∑ G ∈ 𝒢,
          b G * if v ∈ G then (G.card : ℝ)⁻¹ else 0) = 1 :=
      barycentric_chain_coordinate_sum σ 𝒢 b h𝒢_faces hsumb
    have hcoord : ∀ v ∈ σ,
        (∑ F ∈ ℱ, a F * if v ∈ F then (F.card : ℝ)⁻¹ else 0) =
          ∑ G ∈ 𝒢, b G * if v ∈ G then (G.card : ℝ)⁻¹ else 0 :=
      hσ.eq_of_sum_eq_sum_subtype (hcoordsuma.trans hcoordsumb.symm)
        (hvertexa.trans hvertexb.symm)
    have hrecover : ∀ F ∈ ℱ, 0 < a F → F ∈ 𝒢 := by
      intro F hFℱ haF
      exact barycentric_positive_face_recovery σ ℱ 𝒢 a b hℱ_nonempty h𝒢_nonempty
        hℱ_faces h𝒢_faces hℱ_chain h𝒢_chain ha hb hcoord hFℱ haF
    rw [← Finset.coe_inter]
    apply (Finset.mem_convexHull').mpr
    refine ⟨w, ?_, ?_, ?_⟩
    · intro y hy
      exact hw y (Finset.inter_subset_left hy)
    · rw [Finset.sum_subset Finset.inter_subset_left]
      · exact hsumw
      · intro y hyT hyTU
        obtain ⟨F, hFℱ, rfl⟩ := Finset.mem_image.mp hyT
        have hw_nonneg := hw (c F) (by simpa [T] using hyT)
        have hw_not_pos : ¬0 < w (c F) := by
          intro hw_pos
          have hF𝒢 := hrecover F hFℱ hw_pos
          apply hyTU
          exact Finset.mem_inter.mpr
            ⟨hyT, Finset.mem_image.mpr ⟨F, hF𝒢, rfl⟩⟩
        exact le_antisymm (not_lt.mp hw_not_pos) hw_nonneg
    · rw [Finset.sum_subset Finset.inter_subset_left]
      · exact hxw
      · intro y hyT hyTU
        obtain ⟨F, hFℱ, rfl⟩ := Finset.mem_image.mp hyT
        have hw_nonneg := hw (c F) (by simpa [T] using hyT)
        have hw_not_pos : ¬0 < w (c F) := by
          intro hw_pos
          have hF𝒢 := hrecover F hFℱ hw_pos
          apply hyTU
          exact Finset.mem_inter.mpr
            ⟨hyT, Finset.mem_image.mpr ⟨F, hF𝒢, rfl⟩⟩
        have hw_zero := le_antisymm (not_lt.mp hw_not_pos) hw_nonneg
        simp [hw_zero]
  · exact Set.subset_inter (convexHull_mono Set.inter_subset_left)
      (convexHull_mono Set.inter_subset_right)

@[blueprint "lem:barycentric-chain-restrict-to-face"
  (statement := /-- Let \(q\subseteq\sigma\subseteq\mathbb R^C\), where \(\sigma\) is
  finite and affinely independent, and let \(\mathcal F\) be a finite family of
  nonempty faces of \(\sigma\). If a point belongs both to the convex hull of the
  centroids indexed by \(\mathcal F\) and to \(\operatorname{conv}(q)\), then it belongs
  to the convex hull of those centroids whose indexing faces are contained in \(q\). -/)
  (proof := /-- Use
  \cref{lem:barycentric-centroid-injective-of-affine-independent} to index convex
  coefficients by faces. Expand them into vertex coordinates using
  \cref{lem:barycentric-weighted-centroid-expansion}, normalized by
  \cref{lem:barycentric-chain-coordinate-sum}. Compare these coordinates with a
  convex representation supported on \(q\). Affine independence of \(\sigma\) forces
  every coordinate outside \(q\) to vanish. Hence a face with positive coefficient
  is contained in \(q\); deleting the remaining zero coefficients gives the claimed
  restricted convex combination. -/)
  (title := /-- Restricting a barycentric chain combination to a face -/)
  (latexEnv := "lemma")]
lemma barycentric_chain_restrict_to_face {C : Type*}
    [Fintype C] [Nonempty C] (σ q : Finset (C → ℝ))
    (hσ : AffineIndependent ℝ ((↑) : σ → (C → ℝ))) (hqσ : q ⊆ σ)
    (ℱ : Finset (Finset (C → ℝ)))
    (hℱ_faces : ∀ F ∈ ℱ, F.Nonempty ∧ F ⊆ σ) (x : C → ℝ)
    (hxℱ : x ∈ convexHull ℝ
      (↑(ℱ.image fun F => F.centroid ℝ id) : Set (C → ℝ)))
    (hxq : x ∈ convexHull ℝ (q : Set (C → ℝ))) :
    x ∈ convexHull ℝ
      (↑((ℱ.filter fun F => F ⊆ q).image fun F => F.centroid ℝ id) :
        Set (C → ℝ)) := by
  classical
  let c : Finset (C → ℝ) → (C → ℝ) := fun F => F.centroid ℝ id
  let T := ℱ.image c
  let ℱq := ℱ.filter fun F => F ⊆ q
  let R := ℱq.image c
  have hcℱ : Set.InjOn c (ℱ : Set (Finset (C → ℝ))) := by
    intro F hFℱ G hGℱ hFG
    exact barycentric_centroid_injective_of_affine_independent σ F G hσ
      (hℱ_faces F hFℱ).1 (hℱ_faces F hFℱ).2
      (hℱ_faces G hGℱ).1 (hℱ_faces G hGℱ).2 hFG
  change x ∈ convexHull ℝ (R : Set (C → ℝ))
  change x ∈ convexHull ℝ (T : Set (C → ℝ)) at hxℱ
  rcases (Finset.mem_convexHull').mp hxℱ with ⟨w, hw, hsumw, hxw⟩
  rcases (Finset.mem_convexHull').mp hxq with ⟨d, hd, hsumd, hxd⟩
  let a : Finset (C → ℝ) → ℝ := fun F => w (c F)
  let e : (C → ℝ) → ℝ := fun v => if v ∈ q then d v else 0
  have ha : ∀ F ∈ ℱ, 0 ≤ a F := by
    intro F hFℱ
    exact hw (c F) (Finset.mem_image.mpr ⟨F, hFℱ, rfl⟩)
  have hsuma : ∑ F ∈ ℱ, a F = 1 := by
    change ∑ F ∈ ℱ, w (c F) = 1
    rw [← Finset.sum_image hcℱ]
    exact hsumw
  have hfacea : ∑ F ∈ ℱ, a F • F.centroid ℝ id = x := by
    change ∑ F ∈ ℱ, w (c F) • c F = x
    exact (Finset.sum_image (f := fun y => w y • y) hcℱ).symm.trans hxw
  have hvertexa :
      (∑ v ∈ σ, (∑ F ∈ ℱ,
        a F * if v ∈ F then (F.card : ℝ)⁻¹ else 0) • v) = x :=
    (barycentric_weighted_centroid_expansion σ ℱ a hℱ_faces).symm.trans hfacea
  have hcoordsuma :
      (∑ v ∈ σ, ∑ F ∈ ℱ,
        a F * if v ∈ F then (F.card : ℝ)⁻¹ else 0) = 1 :=
    barycentric_chain_coordinate_sum σ ℱ a hℱ_faces hsuma
  have hsume : ∑ v ∈ σ, e v = 1 := by
    rw [← Finset.sum_subset hqσ]
    · simpa [e] using hsumd
    · intro v hvσ hvq
      simp [e, hvq]
  have hlineare : ∑ v ∈ σ, e v • v = x := by
    rw [← Finset.sum_subset hqσ]
    · simpa [e] using hxd
    · intro v hvσ hvq
      simp [e, hvq]
  have hcoord : ∀ v ∈ σ,
      (∑ F ∈ ℱ, a F * if v ∈ F then (F.card : ℝ)⁻¹ else 0) = e v :=
    hσ.eq_of_sum_eq_sum_subtype (hcoordsuma.trans hsume.symm)
      (hvertexa.trans hlineare.symm)
  have hsupport : ∀ F ∈ ℱ, 0 < a F → F ⊆ q := by
    intro F hFℱ haF v hvF
    have hvσ := (hℱ_faces F hFℱ).2 hvF
    by_contra hvq
    have hpositive : 0 <
        ∑ G ∈ ℱ, a G * if v ∈ G then (G.card : ℝ)⁻¹ else 0 := by
      apply Finset.sum_pos'
      · intro G hGℱ
        by_cases hvG : v ∈ G
        · simp only [hvG, if_true]
          exact mul_nonneg (ha G hGℱ) (inv_nonneg.mpr (Nat.cast_nonneg _))
        · simp [hvG]
      · refine ⟨F, hFℱ, ?_⟩
        have hFcard : 0 < (F.card : ℝ) := by
          exact_mod_cast Finset.card_pos.mpr (hℱ_faces F hFℱ).1
        simp only [hvF, if_true]
        exact mul_pos haF (inv_pos.mpr hFcard)
    rw [hcoord v hvσ] at hpositive
    simp [e, hvq] at hpositive
  have hRT : R ⊆ T := by
    intro y hyR
    obtain ⟨F, hFℱq, rfl⟩ := Finset.mem_image.mp hyR
    exact Finset.mem_image.mpr ⟨F, (Finset.mem_filter.mp hFℱq).1, rfl⟩
  apply (Finset.mem_convexHull').mpr
  refine ⟨w, ?_, ?_, ?_⟩
  · intro y hyR
    exact hw y (hRT hyR)
  · rw [Finset.sum_subset hRT]
    · exact hsumw
    · intro y hyT hyR
      obtain ⟨F, hFℱ, rfl⟩ := Finset.mem_image.mp hyT
      have hw_nonneg := hw (c F) hyT
      have hw_not_pos : ¬0 < w (c F) := by
        intro hw_pos
        apply hyR
        exact Finset.mem_image.mpr
          ⟨F, Finset.mem_filter.mpr ⟨hFℱ, hsupport F hFℱ hw_pos⟩, rfl⟩
      exact le_antisymm (not_lt.mp hw_not_pos) hw_nonneg
  · rw [Finset.sum_subset hRT]
    · exact hxw
    · intro y hyT hyR
      obtain ⟨F, hFℱ, rfl⟩ := Finset.mem_image.mp hyT
      have hw_nonneg := hw (c F) hyT
      have hw_not_pos : ¬0 < w (c F) := by
        intro hw_pos
        apply hyR
        exact Finset.mem_image.mpr
          ⟨F, Finset.mem_filter.mpr ⟨hFℱ, hsupport F hFℱ hw_pos⟩, rfl⟩
      have hw_zero := le_antisymm (not_lt.mp hw_not_pos) hw_nonneg
      simp [hw_zero]

@[blueprint "lem:barycentric-face-chain-intersection"
  (statement := /-- Let \(C\) be a nonempty finite type, let \(K\) be a finite
  triangulation of \(\Delta(C)\), and let \(\tau\) and \(\rho\) be barycentric
  face-chain cells of \(K\). Then their convex hulls meet in the convex hull of their
  common vertices. -/)
  (proof := /-- Choose supporting cells \(\sigma,\sigma'\) and face chains for
  \(\tau,\rho\) as in \cref{def:barycentric-face-chain-cell}. Every chain centroid
  belongs to the convex hull of its indexing face, so a point in both chain simplices
  belongs to \(\operatorname{conv}(\sigma)\cap
  \operatorname{conv}(\sigma')\). The face-to-face axiom of
  \cref{def:finite-simplex-triangulation} identifies this intersection with
  \(\operatorname{conv}(\sigma\cap\sigma')\).

  Apply \cref{lem:barycentric-chain-restrict-to-face} to each convex representation.
  It deletes precisely the zero-coefficient centroids whose indexing faces are not
  contained in \(\sigma\cap\sigma'\). The two remaining nonempty chains are chains of
  faces of the same affinely independent set \(\sigma\cap\sigma'\). Hence
  \cref{lem:barycentric-chains-in-one-simplex-intersection} places the point in the
  convex hull of the centroids common to both restricted chains, which is contained
  in \(\operatorname{conv}(\tau\cap\rho)\). Conversely,
  \(\tau\cap\rho\subseteq\tau\) and \(\tau\cap\rho\subseteq\rho\), so monotonicity of
  the convex hull gives the reverse inclusion. -/)
  (title := /-- Face-to-face intersection for barycentric chain cells -/)
  (latexEnv := "lemma")]
lemma barycentric_face_chain_intersection {C : Type*}
    [Fintype C] [Nonempty C] (K : finite_simplex_triangulation C)
    (τ ρ : Set (C → ℝ))
    (hτ : barycentric_face_chain_cell K τ)
    (hρ : barycentric_face_chain_cell K ρ) :
    convexHull ℝ τ ∩ convexHull ℝ ρ = convexHull ℝ (τ ∩ ρ) := by
  classical
  rcases hτ with ⟨σ, hσK, ℱ, hℱ_nonempty, hℱ_faces, hℱ_chain, hτeq⟩
  rcases hρ with ⟨σ', hσ'K, 𝒢, h𝒢_nonempty, h𝒢_faces, h𝒢_chain, hρeq⟩
  let c : Finset (C → ℝ) → (C → ℝ) := fun F => F.centroid ℝ id
  let T := ℱ.image c
  let U := 𝒢.image c
  let s := (K.finite_vertices σ hσK).toFinset
  let t := (K.finite_vertices σ' hσ'K).toFinset
  let q := s ∩ t
  have hscoe : (s : Set (C → ℝ)) = σ := by
    exact (K.finite_vertices σ hσK).coe_toFinset
  have htcoe : (t : Set (C → ℝ)) = σ' := by
    exact (K.finite_vertices σ' hσ'K).coe_toFinset
  have hsmem : ∀ v : C → ℝ, v ∈ s ↔ v ∈ σ := by
    intro v
    change v ∈ (s : Set (C → ℝ)) ↔ v ∈ σ
    rw [hscoe]
  have htmem : ∀ v : C → ℝ, v ∈ t ↔ v ∈ σ' := by
    intro v
    change v ∈ (t : Set (C → ℝ)) ↔ v ∈ σ'
    rw [htcoe]
  have hτT : τ = (T : Set (C → ℝ)) := by
    rw [hτeq]
    ext y
    simp [T, c, eq_comm]
  have hρU : ρ = (U : Set (C → ℝ)) := by
    rw [hρeq]
    ext y
    simp [U, c, eq_comm]
  rw [hτT, hρU]
  have hsAI : AffineIndependent ℝ ((↑) : s → (C → ℝ)) := by
    let e : s ↪ σ :=
      ⟨fun v => ⟨v.1, (hsmem v.1).1 v.2⟩,
        fun v w h => Subtype.ext
          (congrArg (fun z : σ => (z : C → ℝ)) h)⟩
    have he : ((↑) : σ → (C → ℝ)) ∘ e = ((↑) : s → (C → ℝ)) := by
      funext v
      rfl
    rw [← he]
    exact (K.affine_independent σ hσK).comp_embedding e
  have htAI : AffineIndependent ℝ ((↑) : t → (C → ℝ)) := by
    let e : t ↪ σ' :=
      ⟨fun v => ⟨v.1, (htmem v.1).1 v.2⟩,
        fun v w h => Subtype.ext
          (congrArg (fun z : σ' => (z : C → ℝ)) h)⟩
    have he : ((↑) : σ' → (C → ℝ)) ∘ e = ((↑) : t → (C → ℝ)) := by
      funext v
      rfl
    rw [← he]
    exact (K.affine_independent σ' hσ'K).comp_embedding e
  have hqAI : AffineIndependent ℝ ((↑) : q → (C → ℝ)) :=
    hsAI.mono (by
      intro v hv
      exact Finset.inter_subset_left hv)
  have hℱ_faces_s : ∀ F ∈ ℱ, F.Nonempty ∧ F ⊆ s := by
    intro F hFℱ
    refine ⟨(hℱ_faces F hFℱ).1, ?_⟩
    intro v hvF
    have : v ∈ σ := (hℱ_faces F hFℱ).2 hvF
    exact (hsmem v).2 this
  have h𝒢_faces_t : ∀ G ∈ 𝒢, G.Nonempty ∧ G ⊆ t := by
    intro G hG𝒢
    refine ⟨(h𝒢_faces G hG𝒢).1, ?_⟩
    intro v hvG
    have : v ∈ σ' := (h𝒢_faces G hG𝒢).2 hvG
    exact (htmem v).2 this
  have hTσ : (T : Set (C → ℝ)) ⊆ convexHull ℝ σ := by
    intro y hyT
    obtain ⟨F, hFℱ, rfl⟩ := Finset.mem_image.mp hyT
    exact convexHull_mono (hℱ_faces F hFℱ).2
      (Finset.centroid_mem_convexHull F (hℱ_faces F hFℱ).1)
  have hUσ' : (U : Set (C → ℝ)) ⊆ convexHull ℝ σ' := by
    intro y hyU
    obtain ⟨G, hG𝒢, rfl⟩ := Finset.mem_image.mp hyU
    exact convexHull_mono (h𝒢_faces G hG𝒢).2
      (Finset.centroid_mem_convexHull G (h𝒢_faces G hG𝒢).1)
  have hconvTσ : convexHull ℝ (T : Set (C → ℝ)) ⊆ convexHull ℝ σ :=
    convexHull_min hTσ (convex_convexHull ℝ σ)
  have hconvUσ' : convexHull ℝ (U : Set (C → ℝ)) ⊆ convexHull ℝ σ' :=
    convexHull_min hUσ' (convex_convexHull ℝ σ')
  apply Set.Subset.antisymm
  · intro x hx
    have hxcommon : x ∈ convexHull ℝ (σ ∩ σ') := by
      rw [← K.face_to_face σ hσK σ' hσ'K]
      exact ⟨hconvTσ hx.1, hconvUσ' hx.2⟩
    have hxq : x ∈ convexHull ℝ (q : Set (C → ℝ)) := by
      rw [show (q : Set (C → ℝ)) = σ ∩ σ' by
        ext v
        simp [q, hscoe, htcoe]]
      exact hxcommon
    let ℱq := ℱ.filter fun F => F ⊆ q
    let 𝒢q := 𝒢.filter fun G => G ⊆ q
    let Tq := ℱq.image c
    let Uq := 𝒢q.image c
    have hxTq : x ∈ convexHull ℝ (Tq : Set (C → ℝ)) := by
      exact barycentric_chain_restrict_to_face s q hsAI Finset.inter_subset_left
        ℱ hℱ_faces_s x hx.1 hxq
    have hxUq : x ∈ convexHull ℝ (Uq : Set (C → ℝ)) := by
      exact barycentric_chain_restrict_to_face t q htAI Finset.inter_subset_right
        𝒢 h𝒢_faces_t x hx.2 hxq
    have hℱq_nonempty : ℱq.Nonempty := by
      by_contra hne
      have hempty : ℱq = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hTqempty : Tq = ∅ := by simp [Tq, hempty]
      rw [hTqempty] at hxTq
      simpa using hxTq
    have h𝒢q_nonempty : 𝒢q.Nonempty := by
      by_contra hne
      have hempty : 𝒢q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hUqempty : Uq = ∅ := by simp [Uq, hempty]
      rw [hUqempty] at hxUq
      simpa using hxUq
    have hℱq_faces : ∀ F ∈ ℱq, F.Nonempty ∧ F ⊆ q := by
      intro F hFℱq
      have h := Finset.mem_filter.mp hFℱq
      exact ⟨(hℱ_faces F h.1).1, h.2⟩
    have h𝒢q_faces : ∀ G ∈ 𝒢q, G.Nonempty ∧ G ⊆ q := by
      intro G hG𝒢q
      have h := Finset.mem_filter.mp hG𝒢q
      exact ⟨(h𝒢_faces G h.1).1, h.2⟩
    have hℱq_chain : ∀ F ∈ ℱq, ∀ G ∈ ℱq, F ⊆ G ∨ G ⊆ F := by
      intro F hF G hG
      exact hℱ_chain F (Finset.mem_filter.mp hF).1 G (Finset.mem_filter.mp hG).1
    have h𝒢q_chain : ∀ F ∈ 𝒢q, ∀ G ∈ 𝒢q, F ⊆ G ∨ G ⊆ F := by
      intro F hF G hG
      exact h𝒢_chain F (Finset.mem_filter.mp hF).1 G (Finset.mem_filter.mp hG).1
    have hsame := barycentric_chains_in_one_simplex_intersection q hqAI ℱq 𝒢q
      hℱq_nonempty h𝒢q_nonempty hℱq_faces h𝒢q_faces hℱq_chain h𝒢q_chain
    have hxrestricted : x ∈ convexHull ℝ
        ((Tq : Set (C → ℝ)) ∩ (Uq : Set (C → ℝ))) := by
      rw [← hsame]
      exact ⟨hxTq, hxUq⟩
    apply convexHull_mono _ hxrestricted
    intro y hy
    rcases hy with ⟨hyTq, hyUq⟩
    constructor
    · obtain ⟨F, hFℱq, rfl⟩ := Finset.mem_image.mp hyTq
      exact Finset.mem_image.mpr
        ⟨F, (Finset.mem_filter.mp hFℱq).1, rfl⟩
    · obtain ⟨G, hG𝒢q, rfl⟩ := Finset.mem_image.mp hyUq
      exact Finset.mem_image.mpr
        ⟨G, (Finset.mem_filter.mp hG𝒢q).1, rfl⟩
  · exact Set.subset_inter (convexHull_mono Set.inter_subset_left)
      (convexHull_mono Set.inter_subset_right)

@[blueprint "lem:finite-nonempty-finset-chain-extension"
  (statement := /-- Let \(S\) be a finite set and let \(\mathcal F\) be a finite
  inclusion-chain of nonempty subsets of \(S\). There is an inclusion-chain
  \(\mathcal G\) of nonempty subsets of \(S\) which contains \(\mathcal F\) and has
  exactly \(|S|\) members. -/)
  (proof := /-- Put \(x\preceq y\) if \(x=y\), or if some member of
  \(\mathcal F\) contains \(x\) but not \(y\). Comparability of the members of
  \(\mathcal F\) makes this a partial order. Extend it to a linear order. For each
  \(x\in S\), take the initial segment of \(S\) ending at \(x\). These initial
  segments form a chain of \(|S|\) nonempty subsets, since distinct endpoints give
  distinct initial segments. If \(F\in\mathcal F\), choose its greatest element in
  the linear extension. Every element of \(F\) precedes this greatest element, and
  every element outside \(F\) follows it by the definition of \(\preceq\). Thus
  \(F\) is the corresponding initial segment, so the new chain contains
  \(\mathcal F\). -/)
  (title := /-- Extension of a finite set-chain through every positive rank -/)
  (latexEnv := "lemma")]
lemma finite_nonempty_finset_chain_extension {α : Type*}
    (S : Finset α) (ℱ : Finset (Finset α))
    (hfaces : ∀ F ∈ ℱ, F.Nonempty ∧ F ⊆ S)
    (hchain : ∀ F ∈ ℱ, ∀ G ∈ ℱ, F ⊆ G ∨ G ⊆ F) :
    ∃ 𝒢 : Finset (Finset α), ℱ ⊆ 𝒢 ∧
      (∀ F ∈ 𝒢, F.Nonempty ∧ F ⊆ S) ∧
        (∀ F ∈ 𝒢, ∀ G ∈ 𝒢, F ⊆ G ∨ G ⊆ F) ∧
          𝒢.card = S.card := by
  classical
  let r : α → α → Prop := fun x y =>
    x = y ∨ ∃ F ∈ ℱ, x ∈ F ∧ y ∉ F
  have hr_refl : ∀ x, r x x := fun x => Or.inl rfl
  have hr_trans : ∀ x y z, r x y → r y z → r x z := by
    intro x y z hxy hyz
    rcases hxy with rfl | ⟨F, hF, hxF, hyF⟩
    · exact hyz
    rcases hyz with rfl | ⟨G, hG, hyG, hzG⟩
    · exact Or.inr ⟨F, hF, hxF, hyF⟩
    rcases hchain F hF G hG with hFG | hGF
    · exact Or.inr ⟨G, hG, hFG hxF, hzG⟩
    · exact False.elim (hyF (hGF hyG))
  have hr_antisymm : ∀ x y, r x y → r y x → x = y := by
    intro x y hxy hyx
    rcases hxy with hxy | ⟨F, hF, hxF, hyF⟩
    · exact hxy
    rcases hyx with hyx | ⟨G, hG, hyG, hxG⟩
    · exact hyx.symm
    rcases hchain F hF G hG with hFG | hGF
    · exact False.elim (hxG (hFG hxF))
    · exact False.elim (hyF (hGF hyG))
  letI chainOrder : PartialOrder α :=
    { le := r
      le_refl := hr_refl
      le_trans := hr_trans
      le_antisymm := hr_antisymm }
  let initial : α → Finset α := fun x =>
    S.filter fun y => toLinearExtension y ≤ toLinearExtension x
  let 𝒢 : Finset (Finset α) := S.image initial
  have hinitial : Set.InjOn initial (S : Set α) := by
    intro x hx y hy hxy
    change x ∈ S at hx
    change y ∈ S at hy
    have hxx : x ∈ initial x := by
      simp [initial, hx]
    have hyy : y ∈ initial y := by
      simp [initial, hy]
    have hxy' : toLinearExtension x ≤ toLinearExtension y := by
      have : x ∈ initial y := by
        rw [← hxy]
        exact hxx
      exact (Finset.mem_filter.mp this).2
    have hyx' : toLinearExtension y ≤ toLinearExtension x := by
      have : y ∈ initial x := by
        rw [hxy]
        exact hyy
      exact (Finset.mem_filter.mp this).2
    have hxy_eq : toLinearExtension x = toLinearExtension y :=
      le_antisymm hxy' hyx'
    change x = y at hxy_eq
    exact hxy_eq
  have h𝒢card : 𝒢.card = S.card := by
    exact Finset.card_image_iff.mpr hinitial
  have h𝒢faces : ∀ F ∈ 𝒢, F.Nonempty ∧ F ⊆ S := by
    intro F hF
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hF
    constructor
    · exact ⟨x, by simp [initial, hxS]⟩
    · intro y hy
      exact (Finset.mem_filter.mp hy).1
  have h𝒢chain : ∀ F ∈ 𝒢, ∀ G ∈ 𝒢, F ⊆ G ∨ G ⊆ F := by
    intro F hF G hG
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hF
    obtain ⟨y, hyS, rfl⟩ := Finset.mem_image.mp hG
    rcases le_total (toLinearExtension x) (toLinearExtension y) with hxy | hyx
    · left
      intro z hz
      have hz' := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hz'.1, hz'.2.trans hxy⟩
    · right
      intro z hz
      have hz' := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hz'.1, hz'.2.trans hyx⟩
  have hℱ𝒢 : ℱ ⊆ 𝒢 := by
    intro F hF
    obtain ⟨x, hxF, hxmax⟩ :=
      F.exists_max_image (fun y => toLinearExtension y) (hfaces F hF).1
    have hxS : x ∈ S := (hfaces F hF).2 hxF
    have hFinitial : F = initial x := by
      apply Finset.Subset.antisymm
      · intro y hyF
        exact Finset.mem_filter.mpr ⟨(hfaces F hF).2 hyF, hxmax y hyF⟩
      · intro y hy
        have hy' := Finset.mem_filter.mp hy
        by_contra hyF
        have hxy_base : x ≤ y := by
          change r x y
          exact Or.inr ⟨F, hF, hxF, hyF⟩
        have hxy_ext : toLinearExtension x ≤ toLinearExtension y :=
          toLinearExtension.monotone hxy_base
        have hyx_ext : toLinearExtension y ≤ toLinearExtension x := hy'.2
        have hyx_ext_eq : toLinearExtension y = toLinearExtension x :=
          le_antisymm hyx_ext hxy_ext
        change y = x at hyx_ext_eq
        have hyx : y = x := hyx_ext_eq
        exact hyF (hyx.symm ▸ hxF)
    rw [hFinitial]
    exact Finset.mem_image.mpr ⟨x, hxS, rfl⟩
  exact ⟨𝒢, hℱ𝒢, h𝒢faces, h𝒢chain, h𝒢card⟩

@[blueprint "lem:barycentric-face-chain-centroid-injective"
  (statement := /-- Let \(\sigma\) be a cell of a finite triangulation of a standard
  simplex, and let \(\mathcal F\) be an inclusion-chain of nonempty finite subsets of
  \(\sigma\). Then distinct members of \(\mathcal F\) have distinct centroids. -/)
  (proof := /-- By \cref{def:finite-simplex-triangulation}, the vertices of
  \(\sigma\) are affinely independent. First suppose that
  \(G\subsetneq F\subseteq\sigma\). Choose \(v\in F\setminus G\). If the centroid of
  \(F\) lay in \(\operatorname{aff}(G)\), uniqueness of affine coordinates in the
  affinely independent family \(F\) would force its coefficient at \(v\) to vanish.
  That coefficient is \(1/|F|\), which is nonzero because \(F\) is nonempty, a
  contradiction. Thus the centroid of \(F\) is not in
  \(\operatorname{aff}(G)\), whereas the centroid of \(G\) is in
  \(\operatorname{conv}(G)\subseteq\operatorname{aff}(G)\). Any two members of
  \(\mathcal F\) are comparable, so equality of their centroids rules out strict
  containment in either direction and hence forces equality. -/)
  (title := /-- Injectivity of centroids along a face chain -/)
  (latexEnv := "lemma")]
lemma barycentric_face_chain_centroid_injective {C : Type*}
    [Fintype C] [Nonempty C] (K : finite_simplex_triangulation C)
    (σ : Set (C → ℝ)) (hσ : σ ∈ K.cells)
    (ℱ : Finset (Finset (C → ℝ)))
    (hfaces : ∀ F ∈ ℱ, F.Nonempty ∧ (F : Set (C → ℝ)) ⊆ σ)
    (hchain : ∀ F ∈ ℱ, ∀ G ∈ ℱ, F ⊆ G ∨ G ⊆ F) :
    Function.Injective (fun F : ℱ => F.1.centroid ℝ id) := by
  classical
  let P := C → ℝ
  have centroid_not_mem_affineSpan
      {F G : Finset P} (hF : F.Nonempty) (hFσ : (F : Set P) ⊆ σ)
      (hGF : G ⊂ F) :
      F.centroid ℝ id ∉ affineSpan ℝ (G : Set P) := by
    intro hmem
    have hGFset : (G : Set P) ⊂ (F : Set P) := by
      simpa using hGF
    obtain ⟨x, hxF, hxG⟩ := Set.exists_of_ssubset hGFset
    let i : F := ⟨x, hxF⟩
    let p : F → P := fun y => y
    have hp : AffineIndependent ℝ p := by
      exact (K.affine_independent σ hσ).comp_embedding
        (⟨fun y : F => ⟨(y : P), hFσ y.property⟩,
            fun _ _ h =>
              Subtype.ext (congrArg (fun z : σ => (z : P)) h)⟩ : F ↪ σ)
    let t : Set F := {y | (y : P) ∈ G}
    have hGt : p '' t = (G : Set P) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        exact ⟨⟨y, hGF.le hy⟩, hy, rfl⟩
    have hmem' :
        (Finset.univ : Finset F).affineCombination ℝ p
            ((Finset.univ : Finset F).centroidWeightsIndicator ℝ) ∈
          affineSpan ℝ (p '' t) := by
      rw [hGt, ← Finset.centroid_eq_affineCombination_fintype,
        Finset.centroid_univ]
      exact hmem
    have huniv : (Finset.univ : Finset F).Nonempty := by
      exact ⟨i, Finset.mem_univ i⟩
    have hw :
        ∑ y, (Finset.univ : Finset F).centroidWeightsIndicator ℝ y = 1 :=
      (Finset.univ : Finset F).sum_centroidWeightsIndicator_eq_one_of_nonempty
        ℝ huniv
    have hi_not : i ∉ t := hxG
    have hz :=
      hp.eq_zero_of_affineCombination_mem_affineSpan hw hmem'
        (Finset.mem_univ i) hi_not
    letI : Nonempty F := ⟨i⟩
    have hFempty : F = ∅ := by
      simpa [Finset.centroidWeightsIndicator, Finset.centroidWeights] using hz
    exact hF.ne_empty hFempty
  intro A B hABcentroid
  change A.1.centroid ℝ id = B.1.centroid ℝ id at hABcentroid
  apply Subtype.ext
  rcases hchain A.1 A.2 B.1 B.2 with hAB | hBA
  · by_contra hne
    have hstrict : A.1 ⊂ B.1 :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hAB, hne⟩
    have hnot := centroid_not_mem_affineSpan
      (hfaces B.1 B.2).1 (hfaces B.1 B.2).2 hstrict
    apply hnot
    rw [← hABcentroid]
    exact (convexHull_subset_affineSpan (𝕜 := ℝ) (A.1 : Set P))
      (Finset.centroid_mem_convexHull (R := ℝ) A.1 (hfaces A.1 A.2).1)
  · by_contra hne
    have hstrict : B.1 ⊂ A.1 :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hBA, fun h => hne h.symm⟩
    have hnot := centroid_not_mem_affineSpan
      (hfaces A.1 A.2).1 (hfaces A.1 A.2).2 hstrict
    apply hnot
    rw [hABcentroid]
    exact (convexHull_subset_affineSpan (𝕜 := ℝ) (B.1 : Set P))
      (Finset.centroid_mem_convexHull (R := ℝ) B.1 (hfaces B.1 B.2).1)

@[blueprint "lem:barycentric-face-chain-maximal-extension"
  (statement := /-- Let \(C\) be a nonempty finite type, let \(K\) be a pure finite
  triangulation of \(\Delta(C)\), and let \(\tau\) be a barycentric face-chain cell of
  \(K\). Then \(\tau\) is contained in a barycentric face-chain cell having exactly
  \(|C|\) vertices. -/)
  (proof := /-- Choose a cell \(\sigma\) and a chain \(\mathcal F\) of its nonempty
  faces representing \(\tau\), as in \cref{def:barycentric-face-chain-cell}.
  Purity in \cref{def:finite-simplex-triangulation} supplies a cell
  \(\widehat\sigma\) containing \(\sigma\) and having \(|C|\) vertices. Apply
  \cref{lem:finite-nonempty-finset-chain-extension} to extend \(\mathcal F\) inside
  \(\widehat\sigma\) to an inclusion-chain \(\mathcal G\) of exactly \(|C|\)
  nonempty faces. The centroid set of \(\mathcal G\) is therefore a barycentric
  face-chain cell containing \(\tau\). By
  \cref{lem:barycentric-face-chain-centroid-injective}, its centroid map is
  injective, so this centroid set also has exactly \(|C|\) members. -/)
  (title := /-- Extension of face chains to maximal chains -/)
  (latexEnv := "lemma")]
lemma barycentric_face_chain_maximal_extension {C : Type*}
    [Fintype C] [Nonempty C] (K : finite_simplex_triangulation C)
    (τ : Set (C → ℝ)) (hτ : barycentric_face_chain_cell K τ) :
    ∃ ρ : Set (C → ℝ), barycentric_face_chain_cell K ρ ∧
      τ ⊆ ρ ∧ Set.ncard ρ = Fintype.card C := by
  classical
  let P := C → ℝ
  rcases hτ with ⟨σ, hσ, ℱ, hℱ, hfaces, hchain, hτ⟩
  obtain ⟨σhat, hσhat, hσσhat, hσhatcard⟩ := K.pure σ hσ
  let S : Finset P := (K.finite_vertices σhat hσhat).toFinset
  have hS_nonempty : S.Nonempty := by
    simpa [S] using K.nonempty_cells σhat hσhat
  have hfacesS : ∀ F ∈ ℱ, F.Nonempty ∧ F ⊆ S := by
    intro F hF
    refine ⟨(hfaces F hF).1, ?_⟩
    intro x hx
    simp only [S, Set.Finite.mem_toFinset]
    exact hσσhat ((hfaces F hF).2 hx)
  obtain ⟨𝒢, hℱ𝒢, h𝒢facesS, h𝒢chain, h𝒢card⟩ :=
    finite_nonempty_finset_chain_extension S ℱ hfacesS hchain
  have h𝒢_nonempty : 𝒢.Nonempty := by
    apply Finset.card_pos.mp
    rw [h𝒢card]
    exact Finset.card_pos.mpr hS_nonempty
  have h𝒢faces :
      ∀ F ∈ 𝒢, F.Nonempty ∧ (F : Set P) ⊆ σhat := by
    intro F hF
    refine ⟨(h𝒢facesS F hF).1, ?_⟩
    intro x hx
    have hxS := (h𝒢facesS F hF).2 hx
    simpa only [S, Set.Finite.mem_toFinset] using hxS
  let ρ : Set P := {x | ∃ F ∈ 𝒢, x = F.centroid ℝ id}
  have hρcell : barycentric_face_chain_cell K ρ := by
    exact ⟨σhat, hσhat, 𝒢, h𝒢_nonempty, h𝒢faces, h𝒢chain, rfl⟩
  have hτρ : τ ⊆ ρ := by
    intro x hx
    rw [hτ] at hx
    rcases hx with ⟨F, hF, rfl⟩
    exact ⟨F, hℱ𝒢 hF, rfl⟩
  have hρrange :
      ρ = Set.range (fun F : 𝒢 => F.1.centroid ℝ id) := by
    ext x
    simp [ρ, eq_comm]
  have hcentroid_injective :
      Function.Injective (fun F : 𝒢 => F.1.centroid ℝ id) :=
    barycentric_face_chain_centroid_injective K σhat hσhat 𝒢
      h𝒢faces h𝒢chain
  refine ⟨ρ, hρcell, hτρ, ?_⟩
  rw [hρrange, Set.ncard_range_of_injective hcentroid_injective]
  rw [Nat.card_eq_finsetCard]
  change 𝒢.card = Fintype.card C
  rw [h𝒢card]
  change (K.finite_vertices σhat hσhat).toFinset.card = Fintype.card C
  rw [← Set.ncard_eq_toFinset_card σhat
    (K.finite_vertices σhat hσhat)]
  exact hσhatcard

@[blueprint "lem:barycentric-face-chain-diameter"
  (statement := /-- Let \(C\) be a nonempty finite type and put
  \(q_C=(|C|-1)/|C|\). Then \(0\leq q_C<1\). For every finite triangulation \(K\) of
  \(\Delta(C)\) and every barycentric face-chain cell \(\tau\) of \(K\), there exists
  a cell \(\sigma\in K\) such that
  \(\operatorname{conv}(\tau)\subseteq\operatorname{conv}(\sigma)\) and
  \(\operatorname{diam}(\tau)\leq q_C\operatorname{diam}(\sigma)\). -/)
  (proof := /-- Since \(C\) is nonempty, \(|C|\geq1\), so
  \(q_C=(|C|-1)/|C|\) lies in \([0,1)\). By
  \cref{def:barycentric-face-chain-cell}, choose a cell \(\sigma\) of \(K\) and a
  nonempty chain of nonempty faces of \(\sigma\) whose centroids form \(\tau\).
  The centroid of each face belongs to its convex hull and hence to
  \(\operatorname{conv}(\sigma)\). Convexity therefore gives
  \(\operatorname{conv}(\tau)\subseteq\operatorname{conv}(\sigma)\).

  Consider two faces \(F\subseteq G\) in the chain. If \(F=G\), their centroids
  coincide. Otherwise, put \(H=G\setminus F\), which is nonempty. Writing \(b_S\)
  for the centroid of a nonempty finite set \(S\), expansion of the three
  centroids as uniform averages and the disjoint decomposition \(G=F\sqcup H\)
  give
  \[
    b_F-b_G=\frac{|H|}{|G|}(b_F-b_H).
  \]
  Both \(b_F\) and \(b_H\) lie in \(\operatorname{conv}(\sigma)\), whose diameter
  equals that of \(\sigma\). Hence
  \[
    d(b_F,b_G)\leq\frac{|H|}{|G|}\operatorname{diam}(\sigma).
  \]
  The purity axiom in \cref{def:finite-simplex-triangulation} extends \(\sigma\) to
  a cell with \(|C|\) vertices, so \(|G|\leq|C|\). Since \(|F|\geq1\) and
  \(|H|+|F|=|G|\), elementary arithmetic yields
  \[
    \frac{|H|}{|G|}\leq\frac{|C|-1}{|C|}=q_C.
  \]
  The chain condition compares either orientation of every pair of faces.
  Applying the resulting distance bound to every pair of vertices of \(\tau\)
  proves the asserted diameter estimate. -/)
  (title := /-- Diameter bound for barycentric face-chain cells -/)
  (latexEnv := "lemma")]
lemma barycentric_face_chain_diameter {C : Type*}
    [Fintype C] [Nonempty C] :
    0 ≤ (((Fintype.card C - 1 : ℕ) : ℝ) / (Fintype.card C : ℝ)) ∧
      (((Fintype.card C - 1 : ℕ) : ℝ) / (Fintype.card C : ℝ)) < 1 ∧
        ∀ K : finite_simplex_triangulation C,
          ∀ τ : Set (C → ℝ), barycentric_face_chain_cell K τ →
            ∃ σ ∈ K.cells,
              convexHull ℝ τ ⊆ convexHull ℝ σ ∧
                Metric.diam τ ≤
                  (((Fintype.card C - 1 : ℕ) : ℝ) /
                    (Fintype.card C : ℝ)) * Metric.diam σ := by
  classical
  have hn : 0 < Fintype.card C := Fintype.card_pos
  refine ⟨by positivity, by norm_num [div_lt_one, hn], ?_⟩
  intro K τ hτ
  rcases hτ with ⟨σ, hσ, ℱ, hℱ, hfaces, hchain, rfl⟩
  refine ⟨σ, hσ, ?_, ?_⟩
  · refine convexHull_min ?_ (convex_convexHull ℝ σ)
    intro x hx
    rcases hx with ⟨F, hF, rfl⟩
    exact convexHull_mono (hfaces F hF).2
      (Finset.centroid_mem_convexHull F (hfaces F hF).1)
  · apply Metric.diam_le_of_forall_dist_le
    · positivity
    intro x hx y hy
    rcases hx with ⟨F, hF, rfl⟩
    rcases hy with ⟨G, hG, rfl⟩
    have hbound (F G : Finset (C → ℝ)) (hF : F ∈ ℱ) (hG : G ∈ ℱ)
        (hFG : F ⊆ G) :
        dist (F.centroid ℝ id) (G.centroid ℝ id) ≤
          ((Fintype.card C - 1 : ℕ) : ℝ) / (Fintype.card C : ℝ) *
            Metric.diam σ := by
      have hcentroid (S : Finset (C → ℝ)) (hS : S.Nonempty) :
      S.centroid ℝ id = (S.card : ℝ)⁻¹ • ∑ z ∈ S, z := by
        have hScard : (S.card : ℝ) ≠ 0 := by
          exact_mod_cast hS.card_ne_zero
        rw [Finset.centroid_eq_centerMass S hS]
        simp [Finset.centerMass, hScard, Finset.smul_sum]
      by_cases hEq : F = G
      · subst G
        simp
        positivity
      have hcard : F.card < G.card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hFG, hEq⟩)
      have hdiff : (G \ F).Nonempty :=
        Finset.sdiff_nonempty_of_card_lt_card hcard
      have hcardF : (F.card : ℝ) ≠ 0 := by
        exact_mod_cast (hfaces F hF).1.card_ne_zero
      have hcardG : (G.card : ℝ) ≠ 0 := by
        exact_mod_cast (hfaces G hG).1.card_ne_zero
      have hcardDiff : ((G \ F).card : ℝ) ≠ 0 := by
        exact_mod_cast hdiff.card_ne_zero
      have hcardEq : ((G \ F).card : ℝ) + (F.card : ℝ) = (G.card : ℝ) := by
        exact_mod_cast Finset.card_sdiff_add_card_eq_card hFG
      have hdecomp :
          F.centroid ℝ id - G.centroid ℝ id =
            (((G \ F).card : ℝ) / (G.card : ℝ)) •
              (F.centroid ℝ id - (G \ F).centroid ℝ id) := by
        rw [hcentroid F (hfaces F hF).1, hcentroid G (hfaces G hG).1,
          hcentroid (G \ F) hdiff]
        rw [← Finset.sum_sdiff hFG]
        ext c
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, Finset.sum_apply,
          smul_eq_mul]
        rw [← hcardEq]
        field_simp
        ring
      have hFmem : F.centroid ℝ id ∈ convexHull ℝ σ :=
        convexHull_mono (hfaces F hF).2
          (Finset.centroid_mem_convexHull F (hfaces F hF).1)
      have hdiffSub : ((G \ F : Finset (C → ℝ)) : Set (C → ℝ)) ⊆ σ := by
        intro z hz
        exact (hfaces G hG).2 (Finset.sdiff_subset hz)
      have hdiffMem : (G \ F).centroid ℝ id ∈ convexHull ℝ σ :=
        convexHull_mono hdiffSub
          (Finset.centroid_mem_convexHull (G \ F) hdiff)
      have hdist :
          dist (F.centroid ℝ id) ((G \ F).centroid ℝ id) ≤ Metric.diam σ := by
        simpa using Metric.dist_le_diam_of_mem
          (isBounded_convexHull.mpr (K.finite_vertices σ hσ).isBounded)
          hFmem hdiffMem
      obtain ⟨ρ, hρ, hσρ, hρcard⟩ := K.pure σ hσ
      have hGρ : ((G : Finset (C → ℝ)) : Set (C → ℝ)) ⊆ ρ :=
        (hfaces G hG).2.trans hσρ
      have hGcard : G.card ≤ Fintype.card C := by
        rw [← hρcard]
        simpa using Set.ncard_le_ncard hGρ (K.finite_vertices ρ hρ)
      have hcoeff :
          ((G \ F).card : ℝ) / (G.card : ℝ) ≤
            ((Fintype.card C - 1 : ℕ) : ℝ) / (Fintype.card C : ℝ) := by
        have hnR : (0 : ℝ) < Fintype.card C := by exact_mod_cast hn
        have hFR : (0 : ℝ) < F.card := by
          exact_mod_cast (hfaces F hF).1.card_pos
        have hGR : (0 : ℝ) < G.card := by
          exact_mod_cast (by omega : 0 < G.card)
        have hGleR : (G.card : ℝ) ≤ Fintype.card C := by exact_mod_cast hGcard
        have hFone : (1 : ℝ) ≤ F.card := by
          exact_mod_cast (hfaces F hF).1.card_pos
        have hGleMul : (G.card : ℝ) ≤
            (F.card : ℝ) * (Fintype.card C : ℝ) :=
          hGleR.trans (by nlinarith)
        have hsubCast : ((Fintype.card C - 1 : ℕ) : ℝ) =
            (Fintype.card C : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card C)]
          norm_num
        rw [div_le_div_iff₀ hGR hnR, hsubCast]
        nlinarith [hcardEq, hGleMul]
      calc
        dist (F.centroid ℝ id) (G.centroid ℝ id) =
            ((G \ F).card : ℝ) / (G.card : ℝ) *
              dist (F.centroid ℝ id) ((G \ F).centroid ℝ id) := by
          rw [dist_eq_norm, hdecomp, norm_smul, Real.norm_of_nonneg (by positivity),
            ← dist_eq_norm]
        _ ≤ ((G \ F).card : ℝ) / (G.card : ℝ) * Metric.diam σ :=
          mul_le_mul_of_nonneg_left hdist (by positivity)
        _ ≤ ((Fintype.card C - 1 : ℕ) : ℝ) / (Fintype.card C : ℝ) *
            Metric.diam σ :=
          mul_le_mul_of_nonneg_right hcoeff Metric.diam_nonneg
    rcases hchain F hF G hG with hFG | hGF
    · exact hbound F G hF hG hFG
    · rw [dist_comm]
      exact hbound G F hG hF hGF

@[blueprint "lem:barycentric-subdivision-realization"
  (statement := /-- Let \(C\) be a nonempty finite type and let \(K\) be a finite
  triangulation of \(\Delta(C)\). There is a finite triangulation \(K'\) whose cells
  are exactly the barycentric face-chain cells of \(K\). -/)
  (proof := /-- Define the cells of \(K'\) by
  \cref{def:barycentric-face-chain-cell}. Finiteness, nonemptiness, affine
  independence, containment of the vertices in \(\Delta(C)\), and closure under
  nonempty faces are supplied by
  \cref{lem:barycentric-face-chain-affine-independent}. The cover axiom is
  \cref{lem:barycentric-face-chain-cover}, and the face-to-face axiom is
  \cref{lem:barycentric-face-chain-intersection}. Finally,
  \cref{lem:barycentric-face-chain-maximal-extension} gives purity of dimension
  \(|C|-1\). These are precisely the fields of
  \cref{def:finite-simplex-triangulation}, so they define the required \(K'\), with
  the asserted cell equality by construction. -/)
  (title := /-- Realization of the barycentric subdivision -/)
  (latexEnv := "lemma")]
lemma barycentric_subdivision_realization {C : Type*}
    [Fintype C] [Nonempty C] (K : finite_simplex_triangulation C) :
    ∃ K' : finite_simplex_triangulation C,
      K'.cells =
        {τ : Set (C → ℝ) | barycentric_face_chain_cell K τ} := by
  rcases barycentric_face_chain_affine_independent K with
    ⟨hfinite, hbasic, hfaces⟩
  let K' : finite_simplex_triangulation C :=
    { cells := {τ | barycentric_face_chain_cell K τ}
      finite_cells := hfinite
      finite_vertices := fun σ hσ => (hbasic σ hσ).1
      nonempty_cells := fun σ hσ => (hbasic σ hσ).2.1
      affine_independent := fun σ hσ => (hbasic σ hσ).2.2.1
      closed_under_nonempty_faces := fun σ hσ τ hτ hτσ =>
        hfaces σ hσ τ hτ hτσ
      vertices_mem_standard_simplex := fun σ hσ x hx =>
        (hbasic σ hσ).2.2.2 x hx
      cover := barycentric_face_chain_cover K
      face_to_face := fun σ hσ τ hτ =>
        barycentric_face_chain_intersection K σ τ hσ hτ
      pure := fun σ hσ =>
        barycentric_face_chain_maximal_extension K σ hσ }
  exact ⟨K', rfl⟩

@[blueprint "lem:barycentric-subdivision-contraction"
  (statement := /-- Let \(C\) be a nonempty finite set. There is a constant
  \(q_C\in[0,1)\) such that, for every finite triangulation \(K\) of \(\Delta(C)\),
  there is a finite triangulation \(K'\) of \(\Delta(C)\) with the following property:
  for every cell \(\tau\) of \(K'\), there is a cell \(\sigma\) of \(K\) such that
  \(\operatorname{conv}(\tau)\subseteq\operatorname{conv}(\sigma)\) and
  \(\operatorname{diam}(\tau)\leq q_C\operatorname{diam}(\sigma)\). -/)
  (proof := /-- Put \(q_C=(|C|-1)/|C|\). By
  \cref{lem:barycentric-face-chain-diameter}, \(0\leq q_C<1\), and every
  barycentric face-chain cell has diameter at most \(q_C\) times the diameter of a
  containing old cell. For a given triangulation \(K\), choose the triangulation
  \(K'\) supplied by \cref{lem:barycentric-subdivision-realization}. Its cells are
  exactly the barycentric face-chain cells of \(K\). Applying the containment and
  diameter conclusions of \cref{lem:barycentric-face-chain-diameter} to each cell of
  \(K'\) gives the required refinement and contraction estimates. -/)
  (title := /-- Barycentric subdivision contracts every simplex uniformly -/)
  (latexEnv := "lemma")]
lemma barycentric_subdivision_contraction {C : Type*} [Fintype C] [Nonempty C] :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧
      ∀ K : finite_simplex_triangulation C,
        ∃ K' : finite_simplex_triangulation C,
          ∀ τ ∈ K'.cells, ∃ σ ∈ K.cells,
            convexHull ℝ τ ⊆ convexHull ℝ σ ∧
              Metric.diam τ ≤ q * Metric.diam σ := by
  rcases barycentric_face_chain_diameter (C := C) with ⟨hq0, hq1, hdiam⟩
  refine ⟨_, hq0, hq1, ?_⟩
  intro K
  rcases barycentric_subdivision_realization K with ⟨K', hK'⟩
  refine ⟨K', ?_⟩
  intro τ hτ
  rw [hK'] at hτ
  exact hdiam K τ hτ

@[blueprint "lem:iterated-barycentric-subdivision-contraction"
  (statement := /-- Let \(C\) be a nonempty finite set. There is \(q_C\in[0,1)\) such
  that, for every \(n\in\mathbb N\) and every finite triangulation \(K\) of
  \(\Delta(C)\), there is a finite triangulation \(K'\) of \(\Delta(C)\) such that, for
  each cell \(\tau\) of \(K'\), there is a cell \(\sigma\) of \(K\) whose convex hull
  contains the convex hull of \(\tau\), and
  \(\operatorname{diam}(\tau)\leq q_C^n\operatorname{diam}(\sigma)\). -/)
  (proof := /-- Choose \(q_C\) from
  \cref{lem:barycentric-subdivision-contraction}. We argue by induction on \(n\).
  For \(n=0\), take the original triangulation and use \(q_C^0=1\). Suppose the result
  has been proved for \(n\), and barycentrically subdivide the resulting triangulation
  once more. By \cref{lem:barycentric-subdivision-contraction}, every cell \(\tau\) of
  the new triangulation lies in a cell \(\rho\) from the \(n\)-fold subdivision and
  satisfies
  \(\operatorname{diam}(\tau)\le q_C\operatorname{diam}(\rho)\). The induction
  hypothesis supplies an original cell \(\sigma\) containing \(\rho\) with
  \(\operatorname{diam}(\rho)\le q_C^n\operatorname{diam}(\sigma)\). Since
  \(q_C\geq0\), multiplication preserves the inequality; transitivity of containment
  and \(q_Cq_C^n=q_C^{n+1}\) give the assertion for \(n+1\). -/)
  (title := /-- Iterated barycentric subdivision has geometrically decaying mesh -/)
  (latexEnv := "lemma")]
lemma iterated_barycentric_subdivision_contraction {C : Type*}
    [Fintype C] [Nonempty C] :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧
      ∀ n : ℕ, ∀ K : finite_simplex_triangulation C,
        ∃ K' : finite_simplex_triangulation C,
          ∀ τ ∈ K'.cells, ∃ σ ∈ K.cells,
            convexHull ℝ τ ⊆ convexHull ℝ σ ∧
              Metric.diam τ ≤ q ^ n * Metric.diam σ := by
  rcases barycentric_subdivision_contraction (C := C) with ⟨q, hq0, hq1, hstep⟩
  refine ⟨q, hq0, hq1, ?_⟩
  intro n
  induction n with
  | zero =>
      intro K
      refine ⟨K, ?_⟩
      intro τ hτ
      exact ⟨τ, hτ, fun _ hx => hx, by simp⟩
  | succ n ih =>
      intro K
      rcases ih K with ⟨Kₙ, hKₙ⟩
      rcases hstep Kₙ with ⟨Kₙ₁, hKₙ₁⟩
      refine ⟨Kₙ₁, ?_⟩
      intro τ hτ
      rcases hKₙ₁ τ hτ with ⟨ρ, hρ, hτρ, hdτρ⟩
      rcases hKₙ ρ hρ with ⟨σ, hσ, hρσ, hdρσ⟩
      refine ⟨σ, hσ, hτρ.trans hρσ, ?_⟩
      calc
        Metric.diam τ ≤ q * Metric.diam ρ := hdτρ
        _ ≤ q * (q ^ n * Metric.diam σ) :=
          mul_le_mul_of_nonneg_left hdρσ hq0
        _ = q ^ (n + 1) * Metric.diam σ := by ring

@[blueprint "lem:barycentric-subdivision-mesh"
  (statement := /-- Let \(C\) be a nonempty finite set. For every
  \(\varepsilon>0\), the standard simplex \(\Delta(C)\) admits a finite triangulation
  every simplex of which has diameter strictly less than \(\varepsilon\). -/)
  (proof := /-- Choose a canonical triangulation \(K_0\) from
  \cref{lem:standard-simplex-canonical-triangulation}; every cell of \(K_0\) has
  diameter at most \(1\). Choose \(q_C\in[0,1)\) and its iterated refinements from
  \cref{lem:iterated-barycentric-subdivision-contraction}. Since \(q_C^n\) tends to
  zero, there is \(n\) with \(q_C^n<\varepsilon\). Let \(K_n\) be the corresponding
  \(n\)-fold subdivision. For every cell \(\tau\) of \(K_n\), the cited refinement
  lemma supplies a cell \(\sigma\) of \(K_0\) such that
  \[
    \operatorname{diam}(\tau)
      \leq q_C^n\operatorname{diam}(\sigma)
      \leq q_C^n<\varepsilon.
  \]
  Thus \(K_n\) has the required mesh. -/)
  (title := /-- Arbitrarily fine barycentric subdivisions of a finite simplex -/)
  (latexEnv := "lemma")]
lemma barycentric_subdivision_mesh {C : Type*} [Fintype C] [Nonempty C]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : finite_simplex_triangulation C,
      ∀ σ ∈ K.cells, Metric.diam σ < ε := by
  rcases standard_simplex_canonical_triangulation (C := C) with ⟨K₀, hK₀⟩
  rcases iterated_barycentric_subdivision_contraction (C := C) with
    ⟨q, hq0, hq1, hq⟩
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hq1
  rcases hq n K₀ with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro τ hτ
  rcases hK τ hτ with ⟨σ, hσ, _, hτσ⟩
  calc
    Metric.diam τ ≤ q ^ n * Metric.diam σ := hτσ
    _ ≤ q ^ n * 1 := mul_le_mul_of_nonneg_left (hK₀ σ hσ) (pow_nonneg hq0 n)
    _ = q ^ n := mul_one _
    _ < ε := hn

@[blueprint "lem:finite-simplex-triangulation-coordinate-face-restriction"
  (statement := /-- Let \(K\) be a finite triangulation of \(\Delta(C)\), and fix
  \(b\in C\). If \(C\setminus\{b\}\) is nonempty, the cells of \(K\) contained in the
  coordinate face \(x(b)=0\), after deleting their zero \(b\)-coordinate, form a finite
  triangulation of \(\Delta(C\setminus\{b\})\). -/)
  (proof := /-- Put \(D=C\setminus\{b\}\), and let
  \(\iota:\mathbb R^D\to\mathbb R^C\) insert the coordinate \(0\) at \(b\). This is an
  injective linear map, its range is \(\{x:x(b)=0\}\), and
  \(y\in\Delta(D)\) if and only if \(\iota(y)\in\Delta(C)\). Define the restricted
  cells to be the sets \(\tau\) for which \(\iota(\tau)\) is a cell of \(K\).

  Injectivity of \(\iota\) transports finiteness, nonemptiness, affine independence,
  closure under nonempty faces, and the face-to-face identity in
  \cref{def:finite-simplex-triangulation}. If \(\sigma\) is a cell of \(K\), all of its
  \(b\)-coordinates are nonnegative. Writing a point of
  \(\operatorname{conv}(\sigma)\) as a finite convex combination shows that coordinate
  \(b\) vanishes exactly after all positive weight has been restricted to vertices
  with zero \(b\)-coordinate. Consequently
  \[
    \operatorname{conv}(\sigma)\cap\{x:x(b)=0\}
      =\operatorname{conv}\{x\in\sigma:x(b)=0\}.
  \]
  Applying this identity to the covering axiom of \(K\), and then pulling back by
  \(\iota\), proves that the restricted cells cover \(\Delta(D)\).

  It remains to prove purity. Extend any restricted cell to a maximal restricted cell
  \(\tau\), which exists because the cell family is finite, and let \(p\) be the
  centroid of \(\tau\). If \(p\) belongs to the convex hull of another restricted cell
  \(\upsilon\), the face-to-face identity puts \(p\) in
  \(\operatorname{conv}(\tau\cap\upsilon)\). Uniqueness of barycentric coordinates for
  the affinely independent vertices of \(\tau\), whose centroid weights are all
  nonzero, gives \(\tau\subseteq\upsilon\); maximality then gives
  \(\upsilon=\tau\). The union of the convex hulls of all other cells is a finite union
  of closed sets not containing \(p\). Hence a sufficiently short initial segment from
  \(p\) toward any \(z\in\Delta(D)\) meets no other cell. The covering axiom puts that
  segment in \(\operatorname{conv}(\tau)\), and extrapolating its affine line shows
  \(z\in\operatorname{aff}(\tau)\). Thus \(\Delta(D)\subseteq\operatorname{aff}(\tau)\).

  The \(|D|\) standard coordinate vectors are affinely independent and lie in
  \(\Delta(D)\), so the preceding affine-span inclusion gives
  \(|D|\leq|\tau|\). Conversely, every vertex of \(\tau\) lies in the convex hull of
  those coordinate vectors, and affine independence gives \(|\tau|\leq|D|\).
  Therefore \(|\tau|=|D|\), proving purity and all remaining axioms of
  \cref{def:finite-simplex-triangulation}. The defining cell equality is immediate
  from the construction. -/)
  (title := /-- Restriction of a simplex triangulation to a coordinate face -/)
  (latexEnv := "lemma")]
lemma finite_simplex_triangulation_coordinate_face_restriction
    {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    (K : finite_simplex_triangulation C) (b : C)
    [Nonempty {a : C // a ≠ b}] :
    ∃ Kb : finite_simplex_triangulation {a : C // a ≠ b},
      ∀ τ : Set ({a : C // a ≠ b} → ℝ),
        τ ∈ Kb.cells ↔
          (fun y : ({a : C // a ≠ b} → ℝ) => fun a : C =>
            if h : a = b then 0 else y ⟨a, h⟩) '' τ ∈ K.cells := by
  classical
  let e : ({a : C // a ≠ b} → ℝ) →ₗ[ℝ] (C → ℝ) :=
    { toFun := fun y a => if h : a = b then 0 else y ⟨a, h⟩
      map_add' := by
        intro x y
        funext a
        simp only [Pi.add_apply]
        split <;> simp_all
      map_smul' := by
        intro r x
        funext a
        simp only [Pi.smul_apply, smul_eq_mul]
        split <;> simp_all }
  have he : Function.Injective e := by
    intro x y hxy
    funext a
    have h := congrFun hxy a.1
    simpa [e, a.2] using h
  have hrange : Set.range e = {x : C → ℝ | x b = 0} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      simp [e]
    · intro hx
      let y : {a : C // a ≠ b} → ℝ := fun a => x a.1
      refine ⟨y, ?_⟩
      funext a
      change (if h : a = b then 0 else x a) = x a
      split
      · subst a
        exact hx.symm
      · rfl
  have hface (σ : Set (C → ℝ)) (hfin : σ.Finite)
      (hnonneg : ∀ x ∈ σ, 0 ≤ x b) :
      convexHull ℝ σ ∩ {x : C → ℝ | x b = 0} =
        convexHull ℝ (σ ∩ {x : C → ℝ | x b = 0}) := by
    let s := hfin.toFinset
    ext x
    constructor
    · rintro ⟨hxconv, hxb⟩
      change x b = 0 at hxb
      have hxconv' : x ∈ convexHull ℝ (s : Set (C → ℝ)) := by
        simpa [s] using hxconv
      rw [Finset.mem_convexHull'] at hxconv'
      rcases hxconv' with ⟨w, hw, hwsum, hwx⟩
      have hterm_nonneg : ∀ y ∈ s, 0 ≤ w y * y b := by
        intro y hy
        exact mul_nonneg (hw y hy) (hnonneg y (by simpa [s] using hy))
      have hterm_sum : ∑ y ∈ s, w y * y b = 0 := by
        have h := congrFun hwx b
        simpa [Finset.sum_apply, smul_eq_mul, hxb] using h
      have hterm_zero : ∀ y ∈ s, w y * y b = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hterm_sum
      have hwzero : ∀ y ∈ s, y b ≠ 0 → w y = 0 := by
        intro y hy hyb
        exact (mul_eq_zero.mp (hterm_zero y hy)).resolve_right hyb
      have hsum_filter : ∑ y ∈ s.filter (fun y => y b = 0), w y = 1 := by
        rw [← hwsum]
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro y hy hyf
        have hyb : y b ≠ 0 := by
          simp [Finset.mem_filter, hy] at hyf
          exact hyf
        exact hwzero y hy hyb
      have hweighted_filter :
          ∑ y ∈ s.filter (fun y => y b = 0), w y • y = x := by
        rw [← hwx]
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro y hy hyf
        have hyb : y b ≠ 0 := by
          simp [Finset.mem_filter, hy] at hyf
          exact hyf
        simp [hwzero y hy hyb]
      have hxfilter :
          x ∈ convexHull ℝ ((s.filter (fun y => y b = 0) : Finset (C → ℝ)) :
            Set (C → ℝ)) := by
        rw [Finset.mem_convexHull']
        exact ⟨w, fun y hy => hw y (Finset.mem_filter.mp hy).1,
          hsum_filter, hweighted_filter⟩
      have hsset :
          ((s.filter (fun y => y b = 0) : Finset (C → ℝ)) : Set (C → ℝ)) =
            σ ∩ {y : C → ℝ | y b = 0} := by
        ext z
        simp [s]
      rw [← hsset]
      exact hxfilter
    · intro hx
      refine ⟨convexHull_mono Set.inter_subset_left hx, ?_⟩
      exact convexHull_min Set.inter_subset_right
        (convex_hyperplane (LinearMap.proj b).isLinear 0) hx
  have hstd (y : {a : C // a ≠ b} → ℝ) :
      y ∈ stdSimplex ℝ {a : C // a ≠ b} ↔ e y ∈ stdSimplex ℝ C := by
    change
      ((∀ a, 0 ≤ y a) ∧ ∑ a, y a = 1) ↔
        ((∀ a, 0 ≤ (e y) a) ∧ ∑ a, (e y) a = 1)
    constructor
    · rintro ⟨hy0, hysum⟩
      constructor
      · intro a
        by_cases hab : a = b
        · simp [e, hab]
        · simpa [e, hab] using hy0 ⟨a, hab⟩
      · rw [Fintype.sum_eq_add_sum_subtype_ne]
        change
          (if h : b = b then 0 else y ⟨b, h⟩) +
              ∑ a : {a : C // a ≠ b},
                (if h : a.1 = b then 0 else y ⟨a.1, h⟩) = 1
        have hbterm : (if h : b = b then 0 else y ⟨b, h⟩) = 0 := dif_pos rfl
        rw [hbterm, zero_add]
        rw [← hysum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [dif_neg a.2]
    · rintro ⟨hy0, hysum⟩
      constructor
      · intro a
        simpa [e, a.2] using hy0 a.1
      · rw [Fintype.sum_eq_add_sum_subtype_ne] at hysum
        change
          (if h : b = b then 0 else y ⟨b, h⟩) +
              ∑ a : {a : C // a ≠ b},
                (if h : a.1 = b then 0 else y ⟨a.1, h⟩) = 1 at hysum
        have hbterm : (if h : b = b then 0 else y ⟨b, h⟩) = 0 := dif_pos rfl
        rw [hbterm, zero_add] at hysum
        have hsums :
            (∑ a : {a : C // a ≠ b},
                (if h : a.1 = b then 0 else y ⟨a.1, h⟩)) =
              ∑ a : {a : C // a ≠ b}, y a := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [dif_neg a.2]
        rw [hsums] at hysum
        exact hysum
  have hAI (σ : Set ({a : C // a ≠ b} → ℝ)) (hσ : e '' σ ∈ K.cells) :
      AffineIndependent ℝ ((↑) : σ → ({a : C // a ≠ b} → ℝ)) := by
    apply AffineIndependent.of_comp e.toAffineMap
    let f : σ ↪ (e '' σ) :=
      ⟨fun x => ⟨e x, ⟨x, x.2, rfl⟩⟩, fun x y h => Subtype.ext (he (congrArg Subtype.val h))⟩
    have h := (K.affine_independent _ hσ).comp_embedding f
    simpa [f, Function.comp_def] using h
  have hFTF (σ τ : Set ({a : C // a ≠ b} → ℝ))
      (hσ : e '' σ ∈ K.cells) (hτ : e '' τ ∈ K.cells) :
      convexHull ℝ σ ∩ convexHull ℝ τ = convexHull ℝ (σ ∩ τ) := by
    apply he.image_injective
    rw [Set.image_inter he, e.image_convexHull, e.image_convexHull,
      e.image_convexHull, Set.image_inter he, K.face_to_face _ hσ _ hτ]
  refine ⟨{
    cells := {τ | e '' τ ∈ K.cells}
    finite_cells := by
      exact K.finite_cells.preimage (Set.injOn_of_injective he.image_injective)
    finite_vertices := by
      intro σ hσ
      rw [← Set.finite_image_iff (Set.injOn_of_injective he)]
      exact K.finite_vertices _ hσ
    nonempty_cells := by
      intro σ hσ
      exact Set.image_nonempty.mp (K.nonempty_cells _ hσ)
    affine_independent := by
      intro σ hσ
      exact hAI σ hσ
    closed_under_nonempty_faces := by
      intro σ hσ τ hτ hτσ
      exact K.closed_under_nonempty_faces _ hσ _ (hτ.image e) (Set.image_mono hτσ)
    vertices_mem_standard_simplex := by
      intro σ hσ x hx
      exact (hstd x).2 (K.vertices_mem_standard_simplex _ hσ (e x) ⟨x, hx, rfl⟩)
    cover := by
      ext y
      constructor
      · intro hy
        have hey : e y ∈ stdSimplex ℝ C := (hstd y).1 hy
        rw [K.cover] at hey
        simp only [Set.mem_iUnion] at hey
        rcases hey with ⟨σ, hσ, heyσ⟩
        let ρ : Set ({a : C // a ≠ b} → ℝ) := e ⁻¹' σ
        have himage : e '' ρ = σ ∩ {x : C → ℝ | x b = 0} := by
          rw [← hrange]
          exact Set.image_preimage_eq_inter_range
        have heyface : e y ∈ convexHull ℝ (σ ∩ {x : C → ℝ | x b = 0}) := by
          rw [← hface σ (K.finite_vertices σ hσ)
            (fun x hx => (K.vertices_mem_standard_simplex σ hσ x hx).1 b)]
          exact ⟨heyσ, by simp [e]⟩
        have hρnonempty : (e '' ρ).Nonempty := by
          rw [himage]
          by_contra h
          rw [Set.not_nonempty_iff_eq_empty.mp h, convexHull_empty] at heyface
          exact heyface
        have hρcell : e '' ρ ∈ K.cells :=
          K.closed_under_nonempty_faces σ hσ _ hρnonempty
            (himage.symm ▸ Set.inter_subset_left)
        have heyimage : e y ∈ e '' convexHull ℝ ρ := by
          rw [e.image_convexHull, himage]
          exact heyface
        rcases heyimage with ⟨z, hz, hzy⟩
        have hzy' : z = y := he hzy
        subst z
        exact Set.mem_iUnion_of_mem ρ (Set.mem_iUnion_of_mem hρcell hz)
      · intro hy
        simp only [Set.mem_iUnion] at hy
        rcases hy with ⟨σ, hσ, hyσ⟩
        apply convexHull_min _ (convex_stdSimplex ℝ {a : C // a ≠ b}) hyσ
        intro x hx
        exact (hstd x).2
          (K.vertices_mem_standard_simplex _ hσ (e x) ⟨x, hx, rfl⟩)
    face_to_face := by
      intro σ hσ τ hτ
      exact hFTF σ τ hσ hτ
    pure := by
      intro σ hσ
      have hcells : {τ : Set ({a : C // a ≠ b} → ℝ) | e '' τ ∈ K.cells}.Finite :=
        K.finite_cells.preimage (Set.injOn_of_injective he.image_injective)
      rcases hcells.exists_le_maximal hσ with ⟨τ, hστ, hτmax⟩
      refine ⟨τ, hτmax.1, hστ, ?_⟩
      have hτfin : τ.Finite := by
        rw [← Set.finite_image_iff (Set.injOn_of_injective he)]
        exact K.finite_vertices _ hτmax.1
      let t := hτfin.toFinset
      have htne : t.Nonempty := by
        simpa [t] using Set.image_nonempty.mp (K.nonempty_cells _ hτmax.1)
      have htai : AffineIndependent ℝ ((↑) : t → ({a : C // a ≠ b} → ℝ)) := by
        let et : t ≃ τ :=
          { toFun := fun x => ⟨x, hτfin.mem_toFinset.mp (by simpa [t] using x.2)⟩
            invFun := fun x => ⟨x, by
              change x.1 ∈ hτfin.toFinset
              exact hτfin.mem_toFinset.mpr x.2⟩
            left_inv := by intro x; rfl
            right_inv := by intro x; rfl }
        have h := (hAI τ hτmax.1).comp_embedding et.toEmbedding
        simpa [et, Function.comp_def] using h
      let q : {a : C // a ≠ b} → ({a : C // a ≠ b} → ℝ) :=
        fun a c => if a = c then 1 else 0
      have hqli : LinearIndependent ℝ q := by
        have hq :
            q = fun a : {a : C // a ≠ b} => Pi.single a (1 : ℝ) := by
          funext a c
          simp [q, Pi.single_apply, eq_comm]
        rw [hq]
        exact Pi.linearIndependent_single_one {a : C // a ≠ b} ℝ
      have hqinj : Function.Injective q := hqli.injective
      let B : Finset ({a : C // a ≠ b} → ℝ) := Finset.univ.image q
      have hBset : (B : Set ({a : C // a ≠ b} → ℝ)) = Set.range q := by
        ext x
        simp [B]
      have hBcard : B.card = Fintype.card {a : C // a ≠ b} := by
        change (Finset.univ.image q).card = Fintype.card {a : C // a ≠ b}
        rw [Finset.card_image_of_injective _ hqinj]
        exact Finset.card_univ
      have hBai : AffineIndependent ℝ ((↑) : B → ({a : C // a ≠ b} → ℝ)) := by
        have h := hqli.affineIndependent.range
        rw [← hBset] at h
        exact h
      have hcentroid_support {u : Set ({a : C // a ≠ b} → ℝ)}
          (hu : u ⊆ (t : Set ({a : C // a ≠ b} → ℝ)))
          (hc : t.centroid ℝ id ∈ convexHull ℝ u) :
          (t : Set ({a : C // a ≠ b} → ℝ)) ⊆ u := by
        let uf := t.filter (fun x => x ∈ u)
        have hufset : (uf : Set ({a : C // a ≠ b} → ℝ)) = u := by
          ext x
          constructor
          · intro hx
            exact (Finset.mem_filter.mp hx).2
          · intro hx
            exact Finset.mem_filter.mpr ⟨hu hx, hx⟩
        rw [← hufset, Finset.mem_convexHull'] at hc
        rcases hc with ⟨w, hw, hwsum, hwx⟩
        let v : ({a : C // a ≠ b} → ℝ) → ℝ :=
          fun x => if x ∈ u then w x else 0
        have hvsum : ∑ x ∈ t, v x = 1 := by
          change (∑ x ∈ t, if x ∈ u then w x else 0) = 1
          rw [← Finset.sum_filter]
          simpa [uf] using hwsum
        have hvx : ∑ x ∈ t, v x • x = t.centroid ℝ id := by
          change (∑ x ∈ t, (if x ∈ u then w x else 0) • x) = t.centroid ℝ id
          simp_rw [ite_smul, zero_smul]
          rw [← Finset.sum_filter]
          simpa [uf] using hwx
        have hcentroid_sum :
            ∑ x ∈ t, t.centroidWeights ℝ x = 1 :=
          t.sum_centroidWeights_eq_one_of_nonempty ℝ htne
        have hcentroid_vec :
            ∑ x ∈ t, t.centroidWeights ℝ x • x = t.centroid ℝ id := by
          rw [t.centroid_eq_centerMass htne]
          rw [Finset.centerMass_eq_of_sum_1 _ _ hcentroid_sum]
          rfl
        have heq := htai.eq_of_sum_eq_sum_subtype
          (hcentroid_sum.trans hvsum.symm) (hcentroid_vec.trans hvx.symm)
        intro x hx
        by_contra hxu
        have hxweight := heq x hx
        have hcard : (t.card : ℝ) ≠ 0 := by
          exact_mod_cast Finset.card_ne_zero.mpr htne
        have hinv : (t.card : ℝ)⁻¹ ≠ 0 := inv_ne_zero hcard
        apply hinv
        simpa [v, hxu] using hxweight
      have hspan :
          stdSimplex ℝ {a : C // a ≠ b} ⊆ affineSpan ℝ (t : Set ({a : C // a ≠ b} → ℝ)) := by
        let x₀ := t.centroid ℝ id
        have hx₀conv : x₀ ∈ convexHull ℝ (t : Set ({a : C // a ≠ b} → ℝ)) := by
          exact t.centroid_mem_convexHull htne
        have hx₀std : x₀ ∈ stdSimplex ℝ {a : C // a ≠ b} := by
          apply convexHull_min _ (convex_stdSimplex ℝ {a : C // a ≠ b}) hx₀conv
          intro x hx
          exact (hstd x).2
            (K.vertices_mem_standard_simplex _ hτmax.1 (e x)
              ⟨x, by simpa [t] using hx, rfl⟩)
        have hx₀_forces (υ : Set ({a : C // a ≠ b} → ℝ))
            (hυ : e '' υ ∈ K.cells) (hxυ : x₀ ∈ convexHull ℝ υ) : τ ⊆ υ := by
          have hxinter :
              x₀ ∈ convexHull ℝ ((t : Set ({a : C // a ≠ b} → ℝ)) ∩ υ) := by
            rw [← hFTF (t : Set ({a : C // a ≠ b} → ℝ)) υ]
            · exact ⟨hx₀conv, hxυ⟩
            · simpa [t] using hτmax.1
            · exact hυ
          have hsub := hcentroid_support Set.inter_subset_left hxinter
          intro x hx
          exact (hsub (by simpa [t] using hx)).2
        let others : Set (Set ({a : C // a ≠ b} → ℝ)) :=
          {υ | e '' υ ∈ K.cells ∧ υ ≠ τ}
        have hothersfin : others.Finite := by
          apply hcells.subset
          intro υ hυ
          exact hυ.1
        let bad : Set ({a : C // a ≠ b} → ℝ) :=
          ⋃ υ ∈ others, convexHull ℝ υ
        have hbadclosed : IsClosed bad := by
          apply hothersfin.isClosed_biUnion
          intro υ hυ
          have hυfin : υ.Finite := by
            rw [← Set.finite_image_iff (Set.injOn_of_injective he)]
            exact K.finite_vertices _ hυ.1
          exact hυfin.isClosed_convexHull (𝕜 := ℝ)
        have hx₀not : x₀ ∉ bad := by
          intro hx
          simp only [bad, Set.mem_iUnion] at hx
          rcases hx with ⟨υ, hυ, hxυ⟩
          have hτυ : τ ⊆ υ := hx₀_forces υ hυ.1 hxυ
          have hυτ : υ ⊆ τ := hτmax.2 hυ.1 hτυ
          exact hυ.2 (Set.Subset.antisymm hυτ hτυ)
        intro z hz
        let f : ℝ → ({a : C // a ≠ b} → ℝ) :=
          fun r => (1 - r) • x₀ + r • z
        have hfcont : Continuous f := by
          fun_prop
        have hopen : IsOpen badᶜ := hbadclosed.isOpen_compl
        have hx₀compl : x₀ ∈ badᶜ := hx₀not
        have hnhds : f ⁻¹' badᶜ ∈ nhds 0 := by
          apply hfcont.continuousAt
          apply hopen.mem_nhds
          simpa [f] using hx₀compl
        rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hε, hball⟩
        let r : ℝ := min (ε / 2) (1 / 2)
        have hrpos : 0 < r := by
          exact lt_min (half_pos hε) (by norm_num)
        have hrlt : r < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
        have hfrcompl : f r ∈ badᶜ := by
          apply hball
          change dist r 0 < ε
          rw [Real.dist_eq, sub_zero, abs_of_pos hrpos]
          exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
        have hfrstd : f r ∈ stdSimplex ℝ {a : C // a ≠ b} := by
          apply (convex_stdSimplex ℝ {a : C // a ≠ b}) hx₀std hz
          · exact sub_nonneg.mpr (le_of_lt hrlt)
          · exact le_of_lt hrpos
          · ring
        have hefr : e (f r) ∈ stdSimplex ℝ C := (hstd (f r)).1 hfrstd
        rw [K.cover] at hefr
        simp only [Set.mem_iUnion] at hefr
        rcases hefr with ⟨υC, hυC, hefrυC⟩
        let υ : Set ({a : C // a ≠ b} → ℝ) := e ⁻¹' υC
        have hυimage : e '' υ = υC ∩ {x : C → ℝ | x b = 0} := by
          rw [← hrange]
          exact Set.image_preimage_eq_inter_range
        have hefrface :
            e (f r) ∈ convexHull ℝ (υC ∩ {x : C → ℝ | x b = 0}) := by
          rw [← hface υC (K.finite_vertices υC hυC)
            (fun x hx => (K.vertices_mem_standard_simplex υC hυC x hx).1 b)]
          exact ⟨hefrυC, by simp [e]⟩
        have hυnonempty : (e '' υ).Nonempty := by
          rw [hυimage]
          by_contra h
          rw [Set.not_nonempty_iff_eq_empty.mp h, convexHull_empty] at hefrface
          exact hefrface
        have hυcell : e '' υ ∈ K.cells :=
          K.closed_under_nonempty_faces υC hυC _ hυnonempty
            (hυimage.symm ▸ Set.inter_subset_left)
        have hefrimage : e (f r) ∈ e '' convexHull ℝ υ := by
          rw [e.image_convexHull, hυimage]
          exact hefrface
        rcases hefrimage with ⟨w, hwυ, hw⟩
        have hwfr : w = f r := he hw
        subst w
        have hυeq : υ = τ := by
          by_contra hne
          have hbad : f r ∈ bad := by
            exact Set.mem_iUnion_of_mem υ
              (Set.mem_iUnion_of_mem ⟨hυcell, hne⟩ hwυ)
          exact hfrcompl hbad
        rw [hυeq] at hwυ
        have hx₀span :
            x₀ ∈ affineSpan ℝ (t : Set ({a : C // a ≠ b} → ℝ)) :=
          convexHull_subset_affineSpan (t : Set ({a : C // a ≠ b} → ℝ)) hx₀conv
        have hfrspan :
            f r ∈ affineSpan ℝ (t : Set ({a : C // a ≠ b} → ℝ)) := by
          apply convexHull_subset_affineSpan (t : Set ({a : C // a ≠ b} → ℝ))
          simpa [t] using hwυ
        have hline := AffineMap.lineMap_mem r⁻¹ hx₀span hfrspan
        have hrne : r ≠ 0 := ne_of_gt hrpos
        have hlineeq : AffineMap.lineMap x₀ (f r) r⁻¹ = z := by
          funext a
          simp [AffineMap.lineMap_apply, f, hrne]
          field_simp
          ring
        rw [hlineeq] at hline
        exact hline
      have hupper :
          (t : Set ({a : C // a ≠ b} → ℝ)) ⊆
            affineSpan ℝ (B : Set ({a : C // a ≠ b} → ℝ)) := by
        intro x hx
        apply convexHull_subset_affineSpan (B : Set ({a : C // a ≠ b} → ℝ))
        rw [hBset, convexHull_basis_eq_stdSimplex]
        exact (hstd x).2
          (K.vertices_mem_standard_simplex _ hτmax.1 (e x)
            ⟨x, by simpa [t] using hx, rfl⟩)
      have hlower :
          (B : Set ({a : C // a ≠ b} → ℝ)) ⊆
            affineSpan ℝ (t : Set ({a : C // a ≠ b} → ℝ)) := by
        intro x hx
        apply hspan
        rw [← convexHull_basis_eq_stdSimplex, ← hBset]
        exact (subset_convexHull (𝕜 := ℝ)
          (s := (B : Set ({a : C // a ≠ b} → ℝ)))) hx
      have hle₁ : t.card ≤ B.card :=
        htai.card_le_card_of_subset_affineSpan hupper
      have hle₂ : B.card ≤ t.card :=
        hBai.card_le_card_of_subset_affineSpan hlower
      calc
        τ.ncard = hτfin.toFinset.card := Set.ncard_eq_toFinset_card τ hτfin
        _ = t.card := rfl
        _ = B.card := Nat.le_antisymm hle₁ hle₂
        _ = Fintype.card {a : C // a ≠ b} := hBcard }, by
      intro τ
      rfl⟩

@[blueprint "lem:triangulation-top-cell-is-basis"
  (statement := /-- Let \(K\) be a finite triangulation of \(\Delta(C)\), and let
  \(\sigma\) be a cell of \(K\) with \(|\sigma|=|C|\). Then the vertices of
  \(\sigma\), regarded as vectors in \(\mathbb R^C\), form a basis. -/)
  (proof := /-- Every vertex has coordinate sum \(1\) by
  \cref{def:finite-simplex-triangulation}. Consequently, any linear relation among
  the vertices has coefficients summing to zero. Affine independence of the cell
  then makes every coefficient zero, so the vertices are linearly independent.
  Their number equals \(\dim(\mathbb R^C)=|C|\), and hence they form a basis. -/)
  (title := /-- The vertices of a top-dimensional cell form a vector-space basis -/)
  (latexEnv := "lemma")]
lemma triangulation_top_cell_is_basis {C : Type*} [Fintype C] [Nonempty C]
    (K : finite_simplex_triangulation C) (σ : Set (C → ℝ))
    (hσ : σ ∈ K.cells) (hcardσ : Set.ncard σ = Fintype.card C) :
    ∃ b : Module.Basis σ ℝ (C → ℝ), ⇑b = ((↑) : σ → (C → ℝ)) := by
  classical
  letI : Fintype σ := (K.finite_vertices σ hσ).fintype
  letI : Nonempty σ :=
    ⟨⟨(K.nonempty_cells σ hσ).choose, (K.nonempty_cells σ hσ).choose_spec⟩⟩
  have hlin : LinearIndependent ℝ ((↑) : σ → (C → ℝ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hvsum (j : σ) : ∑ a, (j : C → ℝ) a = 1 :=
      (K.vertices_mem_standard_simplex σ hσ j j.property).2
    have hsum : ∑ j, g j = 0 := by
      have h := congrArg (fun z : C → ℝ => ∑ a, z a) hg
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        Finset.sum_const_zero] at h
      rw [Finset.sum_comm] at h
      simpa only [← Finset.mul_sum, hvsum, mul_one] using h
    exact (K.affine_independent σ hσ).eq_zero_of_sum_eq_zero
      (s := Finset.univ) (by simpa using hsum) (by simpa using hg) i (Finset.mem_univ i)
  have hdim : Fintype.card σ = Module.finrank ℝ (C → ℝ) := by
    simpa using hcardσ
  let b : Module.Basis σ ℝ (C → ℝ) :=
    basisOfLinearIndependentOfCardEqFinrank hlin hdim
  exact ⟨b, coe_basisOfLinearIndependentOfCardEqFinrank hlin hdim⟩

@[blueprint "lem:triangulation-cell-positive-centroid"
  (statement := /-- Let \(\tau\) be a cell of a finite triangulation of
  \(\Delta(C)\). If \(\operatorname{conv}(\tau)\) contains a point with every
  coordinate positive, then \(\tau\) has a centroid \(y\) with every coordinate
  positive. Moreover, no proper subset of \(\tau\) has convex hull containing
  \(y\), and every cell whose convex hull contains \(y\) contains \(\tau\). -/)
  (proof := /-- Write the given positive point as a convex combination of the
  vertices of \(\tau\). For each coordinate, positivity of that combination and
  nonnegativity of all vertices supplied by
  \cref{def:finite-simplex-triangulation} show that some vertex has that
  coordinate positive. Averaging all vertices therefore gives a centroid \(y\)
  with every coordinate positive.

  The centroid assigns the same strictly positive weight to every vertex of
  \(\tau\). Uniqueness of affine coordinates for the affinely independent cell
  \(\tau\) therefore shows that any subset of \(\tau\) whose convex hull contains
  \(y\) must equal \(\tau\). If \(y\) also lies in the convex hull of a cell
  \(\rho\), the face-to-face axiom in
  \cref{def:finite-simplex-triangulation} puts \(y\) in
  \(\operatorname{conv}(\tau\cap\rho)\), so the preceding conclusion gives
  \(\tau\subseteq\rho\). -/)
  (title := /-- A positive facet centroid detects all incident cells -/)
  (latexEnv := "lemma")]
lemma triangulation_cell_positive_centroid {C : Type*}
    [Fintype C] [Nonempty C] (K : finite_simplex_triangulation C)
    (τ : Set (C → ℝ)) (hτ : τ ∈ K.cells)
    (hinterior : ∃ x ∈ convexHull ℝ τ, ∀ a : C, 0 < x a) :
    ∃ y : C → ℝ,
      (∀ a : C, 0 < y a) ∧ y ∈ convexHull ℝ τ ∧
        (∀ u ⊆ τ, y ∈ convexHull ℝ u → τ ⊆ u) ∧
          ∀ ρ ∈ K.cells, y ∈ convexHull ℝ ρ → τ ⊆ ρ := by
  classical
  let s : Finset (C → ℝ) := (K.finite_vertices τ hτ).toFinset
  have hsτ : (s : Set (C → ℝ)) = τ := by
    simp [s]
  have hsne : s.Nonempty := by
    simpa [s] using K.nonempty_cells τ hτ
  let y : C → ℝ := s.centroid ℝ id
  have hsumweights : ∑ z ∈ s, s.centroidWeights ℝ z = 1 :=
    s.sum_centroidWeights_eq_one_of_nonempty ℝ hsne
  have hyformula :
      y = ∑ z ∈ s, ((s.card : ℝ)⁻¹) • z := by
    change s.affineCombination ℝ id (s.centroidWeights ℝ) =
      ∑ z ∈ s, ((s.card : ℝ)⁻¹) • z
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hsumweights]
    simp
  obtain ⟨x, hxτ, hxpos⟩ := hinterior
  have hxτ' : x ∈ convexHull ℝ (s : Set (C → ℝ)) := by
    simpa [hsτ] using hxτ
  obtain ⟨w, hw_nonneg, hw_sum, hw_eq⟩ :=
    (Finset.mem_convexHull' (R := ℝ)).mp hxτ'
  have hypos : ∀ a : C, 0 < y a := by
    intro a
    have hxsum : ∑ z ∈ s, w z * z a = x a := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
        congrArg (fun q : C → ℝ => q a) hw_eq
    have hterm_nonneg : ∀ z ∈ s, 0 ≤ w z * z a := by
      intro z hz
      exact mul_nonneg (hw_nonneg z hz)
        ((K.vertices_mem_standard_simplex τ hτ z (hsτ ▸ hz)).1 a)
    have hsumpos : 0 < ∑ z ∈ s, w z * z a := by
      rw [hxsum]
      exact hxpos a
    obtain ⟨z, hzs, hzterm⟩ :=
      (Finset.sum_pos_iff_of_nonneg hterm_nonneg).mp hsumpos
    have hza : 0 < z a := by
      have hwz := hw_nonneg z hzs
      nlinarith
    rw [hyformula]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have havg_nonneg :
        ∀ u ∈ s, 0 ≤ (s.card : ℝ)⁻¹ * u a := by
      intro u hu
      exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        ((K.vertices_mem_standard_simplex τ hτ u (hsτ ▸ hu)).1 a)
    apply (Finset.sum_pos_iff_of_nonneg havg_nonneg).2
    refine ⟨z, hzs, mul_pos ?_ hza⟩
    exact inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr hsne))
  have hyτ : y ∈ convexHull ℝ τ := by
    rw [← hsτ]
    exact s.centroid_mem_convexHull hsne
  have hminimal : ∀ u ⊆ τ, y ∈ convexHull ℝ u → τ ⊆ u := by
    intro u hu hyu
    let r : Finset (C → ℝ) := s.filter (· ∈ u)
    have hr : (r : Set (C → ℝ)) = u := by
      rw [← Set.inter_eq_right.mpr hu, ← hsτ]
      ext z
      simp [r]
    have hyu' : y ∈ convexHull ℝ (r : Set (C → ℝ)) := by
      simpa [hr] using hyu
    obtain ⟨v, hv_nonneg, hv_sum, hv_eq⟩ :=
      (Finset.mem_convexHull' (R := ℝ)).mp hyu'
    let v' : (C → ℝ) → ℝ := fun z => if z ∈ r then v z else 0
    have hv'_sum : ∑ z ∈ s, v' z = 1 := by
      calc
        ∑ z ∈ s, v' z = ∑ z ∈ r, v' z := (Finset.sum_subset
          (Finset.filter_subset _ _) (by
            intro z hzs hzr
            change z ∉ r at hzr
            simp [v', hzr])).symm
        _ = ∑ z ∈ r, v z := by
          apply Finset.sum_congr rfl
          intro z hzr
          simp [v', hzr]
        _ = 1 := hv_sum
    have hv'_eq : ∑ z ∈ s, v' z • z = y := by
      calc
        ∑ z ∈ s, v' z • z = ∑ z ∈ r, v' z • z := (Finset.sum_subset
          (Finset.filter_subset _ _) (by
            intro z hzs hzr
            change z ∉ r at hzr
            simp [v', hzr])).symm
        _ = ∑ z ∈ r, v z • z := by
          apply Finset.sum_congr rfl
          intro z hzr
          simp [v', hzr]
        _ = y := hv_eq
    have hai_s :
        AffineIndependent ℝ ((↑) : ↥(s : Set (C → ℝ)) → (C → ℝ)) := by
      rw [hsτ]
      exact K.affine_independent τ hτ
    have hcentroid_eq :
        ∀ z ∈ s, (s.card : ℝ)⁻¹ = v' z := by
      apply hai_s.eq_of_sum_eq_sum_subtype (s := s)
      · rw [hv'_sum]
        simpa using hsumweights
      · rw [hv'_eq, ← hyformula]
    intro z hzτ
    have hzs : z ∈ s := by
      rw [← hsτ] at hzτ
      exact hzτ
    have hzrin : z ∈ r := by
      by_contra hzr
      have hzcoord := hcentroid_eq z hzs
      change (s.card : ℝ)⁻¹ = (if z ∈ r then v z else 0) at hzcoord
      rw [if_neg hzr] at hzcoord
      have : 0 < (s.card : ℝ)⁻¹ :=
        inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr hsne))
      exact (ne_of_gt this) hzcoord
    rw [← hr]
    exact hzrin
  refine ⟨y, hypos, hyτ, hminimal, ?_⟩
  intro ρ hρ hyρ
  have hτinter : τ ⊆ τ ∩ ρ := hminimal (τ ∩ ρ) Set.inter_subset_left (by
    rw [← K.face_to_face τ hτ ρ hρ]
    exact ⟨hyτ, hyρ⟩)
  exact hτinter.trans Set.inter_subset_right

@[blueprint "lem:exists-positive-parameter-in-open-preimage"
  (statement := /-- Let \(U\) be an open subset of a topological space and let
  \(f:\mathbb R\to U'\) be continuous. If \(f(0)\in U\), then
  \(f(t)\in U\) for some \(t>0\). -/)
  (proof := /-- The point \(0\) belongs to the closure of the positive half-line
  \((0,\infty)\). The inverse image \(f^{-1}(U)\) is an open neighbourhood of
  \(0\), so the defining property of closure gives a point
  \(t\in f^{-1}(U)\cap(0,\infty)\). -/)
  (title := /-- A continuous path remains in an open set at a positive time -/)
  (latexEnv := "lemma")]
lemma exists_positive_parameter_in_open_preimage {E : Type*} [TopologicalSpace E]
    (U : Set E) (hU : IsOpen U) (f : ℝ → E) (hf : Continuous f)
    (h0 : f 0 ∈ U) :
    ∃ t : ℝ, 0 < t ∧ f t ∈ U := by
  have hclosure : (0 : ℝ) ∈ closure (Set.Ioi 0) := by
    simp
  obtain ⟨t, htf, htpos⟩ :=
    (mem_closure_iff.mp hclosure) (f ⁻¹' U) (hU.preimage hf) h0
  exact ⟨t, htpos, htf⟩

@[blueprint "lem:triangulation-interior-facet-two-cofaces"
  (statement := /-- Let \(C\) be a nonempty finite type, let \(K\) be a finite
  triangulation of \(\Delta(C)\), and let \(\tau\) be a cell of \(K\) such that
  \(|\tau|+1=|C|\). Suppose that there is a point \(x\in\operatorname{conv}(\tau)\)
  such that \(x(a)>0\) for every \(a\in C\). Then exactly two cells \(\sigma\) of
  \(K\) contain \(\tau\) and satisfy \(|\sigma|=|C|\). -/)
  (proof := /-- By \cref{lem:triangulation-cell-positive-centroid}, choose a point
  \(y\in\operatorname{conv}(\tau)\) with every ambient coordinate positive, with the
  additional property that every cell whose convex hull contains \(y\) contains
  \(\tau\). Purity in \cref{def:finite-simplex-triangulation} gives a top-dimensional
  coface \(\sigma_0=\tau\cup\{v_0\}\). By
  \cref{lem:triangulation-top-cell-is-basis}, its vertices form a basis \(b\) of
  \(\mathbb R^C\). Let \(i_0\) denote the basis vector \(v_0\). The \(i_0\)-coordinate
  vanishes on \(\operatorname{conv}(\tau)\), while every other basis coordinate of
  \(y\) is strictly positive.

  Every top-dimensional coface has the form \(\tau\cup\{v\}\), and affine
  independence implies that the \(i_0\)-coordinate of \(v\) is nonzero. We first show
  that two such cofaces whose extra vertices have coordinates of the same sign are
  equal. For sufficiently small \(t>0\), the point
  \(p=(1-t)y+tv\) has positive residual affine coefficients with respect to both
  cofaces. The required positive parameter is supplied by
  \cref{lem:exists-positive-parameter-in-open-preimage}. Thus \(p\) lies in both
  convex hulls. The face-to-face axiom identifies their intersection with the convex
  hull of their common vertices; if the cofaces were distinct, their common vertex
  set would be exactly \(\tau\), forcing the nonzero \(i_0\)-coordinate of \(p\) to
  vanish. Hence the two cofaces coincide.

  It remains to produce a coface on the opposite side. The union of the convex hulls
  of cells not containing \(\tau\) is closed, because the triangulation is finite.
  Its complement, intersected with the region where every ambient coordinate is
  positive, is an open neighbourhood of \(y\). Apply
  \cref{lem:exists-positive-parameter-in-open-preimage} to
  \(p_t=(1+t)y-tv_0\) and choose \(t>0\) in this neighbourhood. The covering axiom
  places \(p_t\) in a cell, which necessarily contains \(\tau\); purity extends that
  cell to a top-dimensional coface \(\sigma_-\). Since the \(i_0\)-coordinate of
  \(p_t\) is \(-t\), this coface differs from \(\sigma_0\), and its extra vertex has
  negative \(i_0\)-coordinate. Finally, every top-dimensional coface has a nonzero
  extra-vertex coordinate. The same-sign result identifies it with \(\sigma_0\) in
  the positive case and with \(\sigma_-\) in the negative case. These two distinct
  cofaces therefore exhaust the set being counted, whose cardinality is two. -/)
  (title := /-- An interior facet has exactly two top-dimensional cofaces -/)
  (latexEnv := "lemma")]
lemma triangulation_interior_facet_two_cofaces {C : Type*}
    [Fintype C] [Nonempty C] (K : finite_simplex_triangulation C)
    (τ : Set (C → ℝ)) (hτ : τ ∈ K.cells)
    (hcard : Set.ncard τ + 1 = Fintype.card C)
    (hinterior : ∃ x ∈ convexHull ℝ τ, ∀ a : C, 0 < x a) :
    Set.ncard
        {σ : Set (C → ℝ) |
          σ ∈ K.cells ∧ τ ⊆ σ ∧ Set.ncard σ = Fintype.card C} = 2 := by
  classical
  obtain ⟨y, hypos, hyτ, hyminimal, hycells⟩ :=
    triangulation_cell_positive_centroid K τ hτ hinterior
  obtain ⟨σ₀, hσ₀, hτσ₀, hcardσ₀⟩ := K.pure τ hτ
  have hτfinite := K.finite_vertices τ hτ
  obtain ⟨v₀, hv₀τ, hinsert₀⟩ :=
    (Set.exists_eq_insert_iff_ncard hτfinite).2
      ⟨hτσ₀, by omega⟩
  have hv₀σ₀ : v₀ ∈ σ₀ := by
    rw [← hinsert₀]
    exact Set.mem_insert v₀ τ
  let i₀ : σ₀ := ⟨v₀, hv₀σ₀⟩
  letI : Fintype σ₀ := (K.finite_vertices σ₀ hσ₀).fintype
  letI : Nonempty σ₀ :=
    ⟨⟨(K.nonempty_cells σ₀ hσ₀).choose,
      (K.nonempty_cells σ₀ hσ₀).choose_spec⟩⟩
  obtain ⟨b, hb⟩ :=
    triangulation_top_cell_is_basis K σ₀ hσ₀ hcardσ₀
  have hrange : Set.range b = σ₀ := by
    rw [hb]
    ext z
    simp
  have hb_sum (i : σ₀) : ∑ a, (b i) a = 1 := by
    rw [hb]
    exact (K.vertices_mem_standard_simplex σ₀ hσ₀ i i.property).2
  have hrepr_sum (p : C → ℝ) (hp : p ∈ stdSimplex ℝ C) :
      ∑ i, b.repr p i = 1 := by
    have h := congrArg (fun z : C → ℝ => ∑ a, z a) (b.sum_repr p)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [Finset.sum_comm] at h
    simpa only [← Finset.mul_sum, hb_sum, mul_one, hp.2] using h
  have hmem_iff (p : C → ℝ) (hp : p ∈ stdSimplex ℝ C) :
      p ∈ convexHull ℝ σ₀ ↔ ∀ i : σ₀, 0 ≤ b.repr p i := by
    constructor
    · intro hconv
      have hconv' : p ∈ convexHull ℝ (Set.range b) := by
        rw [hrange]
        exact hconv
      rw [convexHull_range_eq_exists_affineCombination] at hconv'
      obtain ⟨s, w, hw_nonneg, hw_sum, hw_eq⟩ := hconv'
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hw_sum] at hw_eq
      let c : σ₀ → ℝ := fun i => if i ∈ s then w i else 0
      have hw_eq' : ∑ i, c i • b i = p := by
        rw [← hw_eq]
        simp [c]
      intro i
      by_cases his : i ∈ s
      · have hi := congrArg (fun q => q i) (b.repr_sum_self c)
        rw [hw_eq'] at hi
        change b.repr p i = c i at hi
        rw [hi]
        simpa [c, his] using hw_nonneg i his
      · have hi := congrArg (fun q => q i) (b.repr_sum_self c)
        rw [hw_eq'] at hi
        change b.repr p i = c i at hi
        rw [hi]
        simp [c, his]
    · intro hnonneg
      rw [← hrange]
      rw [convexHull_range_eq_exists_affineCombination]
      have hsum : ∑ i, b.repr p i = 1 := hrepr_sum p hp
      refine ⟨Finset.univ, fun i => b.repr p i, ?_, by simpa using hsum, ?_⟩
      · intro i hi
        exact hnonneg i
      · rw [Finset.affineCombination_eq_linear_combination _ _ _ (by
          simpa using hsum)]
        exact b.sum_repr p
  have hconv_support (p : C → ℝ) (hp : p ∈ stdSimplex ℝ C)
      (S : Finset σ₀) (hnonneg : ∀ i : σ₀, 0 ≤ b.repr p i)
      (hzero : ∀ i ∉ S, b.repr p i = 0) :
      p ∈ convexHull ℝ (b '' (S : Set σ₀)) := by
    have hrangeS :
        Set.range (fun i : S => b i.1) = b '' (S : Set σ₀) := by
      ext z
      simp
    rw [← hrangeS, convexHull_range_eq_exists_affineCombination]
    have hsumS : ∑ i : S, b.repr p i.1 = 1 := by
      calc
        ∑ i : S, b.repr p i.1 = ∑ i ∈ S, b.repr p i := by
          rw [Finset.sum_coe_sort_eq_attach, Finset.sum_attach]
        _ = ∑ i, b.repr p i := Finset.sum_subset
          (Finset.subset_univ S) (by
            intro i hi hiS
            exact hzero i hiS)
        _ = 1 := hrepr_sum p hp
    refine ⟨Finset.univ, fun i : S => b.repr p i.1, ?_,
      by simpa using hsumS, ?_⟩
    · intro i hi
      exact hnonneg i.1
    · rw [Finset.affineCombination_eq_linear_combination _ _ _ (by
          simpa using hsumS)]
      change ∑ i : S, b.repr p i.1 • b i.1 = p
      calc
        ∑ i : S, b.repr p i.1 • b i.1 =
            ∑ i ∈ S, b.repr p i • b i := by
              rw [Finset.sum_coe_sort_eq_attach]
              exact Finset.sum_attach S (fun i => b.repr p i • b i)
        _ = ∑ i, b.repr p i • b i := Finset.sum_subset
          (Finset.subset_univ S) (by
            intro i hi hiS
            rw [hzero i hiS, zero_smul])
        _ = p := b.sum_repr p
  let Sτ : Finset σ₀ := Finset.univ.erase i₀
  have hindex_mem_τ {i : σ₀} (hi : i ≠ i₀) : b i ∈ τ := by
    have hiσ : (i : C → ℝ) ∈ insert v₀ τ := hinsert₀.symm ▸ i.property
    rcases hiσ with hiv | hiτ
    · exfalso
      apply hi
      apply Subtype.ext
      exact hiv
    · rw [hb]
      exact hiτ
  have himageSτ : b '' (Sτ : Set σ₀) = τ := by
    ext z
    constructor
    · rintro ⟨i, hiS, rfl⟩
      apply hindex_mem_τ
      simpa [Sτ] using hiS
    · intro hzτ
      let i : σ₀ := ⟨z, hτσ₀ hzτ⟩
      have hi : i ≠ i₀ := by
        intro hii
        have hzv : z = v₀ := congrArg Subtype.val hii
        exact hv₀τ (hzv ▸ hzτ)
      refine ⟨i, ?_, ?_⟩
      · simp [Sτ, hi]
      · rw [hb]
  have hcoord_i₀_of_mem_τ (p : C → ℝ) (hp : p ∈ convexHull ℝ τ) :
      b.repr p i₀ = 0 := by
    have hpspan :
        p ∈ Submodule.span ℝ (b '' (Sτ : Set σ₀)) := by
      rw [himageSτ]
      exact convexHull_min Submodule.subset_span (Submodule.convex _) hp
    have hsupp :
        ((b.repr p).support : Set σ₀) ⊆ (Sτ : Set σ₀) :=
      b.mem_span_image.mp hpspan
    by_contra hne
    have hiSupp : i₀ ∈ (b.repr p).support := Finsupp.mem_support_iff.mpr hne
    have := hsupp hiSupp
    simpa [Sτ] using this
  have hyStd : y ∈ stdSimplex ℝ C := by
    exact convexHull_min
      (fun z hz => K.vertices_mem_standard_simplex τ hτ z hz)
      (convex_stdSimplex ℝ C) hyτ
  have hy_nonneg : ∀ i : σ₀, 0 ≤ b.repr y i :=
    (hmem_iff y hyStd).mp (convexHull_mono hτσ₀ hyτ)
  have hy_i₀ : b.repr y i₀ = 0 := hcoord_i₀_of_mem_τ y hyτ
  have hy_strict : ∀ i : σ₀, i ≠ i₀ → 0 < b.repr y i := by
    intro i hi
    have hii : b i ∈ τ := hindex_mem_τ hi
    have hnonzero : b.repr y i ≠ 0 := by
      intro hzeroi
      let S : Finset σ₀ := Sτ.erase i
      have hzero_out : ∀ j ∉ S, b.repr y j = 0 := by
        intro j hj
        by_cases hji : j = i
        · subst j
          exact hzeroi
        · have hjSτ : j ∉ Sτ := by
            intro hjmem
            exact hj (by simp [S, hji, hjmem])
          have hji₀ : j = i₀ := by
            simpa [Sτ] using hjSτ
          subst j
          exact hy_i₀
      have hyS := hconv_support y hyStd S hy_nonneg hzero_out
      have himageS : b '' (S : Set σ₀) = τ \ {b i} := by
        ext z
        constructor
        · rintro ⟨j, hjS, rfl⟩
          have hjSτ : j ∈ Sτ := (Finset.mem_erase.mp hjS).2
          have hbjτ : b j ∈ τ := by
            rw [← himageSτ]
            exact ⟨j, hjSτ, rfl⟩
          refine ⟨hbjτ, ?_⟩
          intro hbeq
          exact (Finset.mem_erase.mp hjS).1 (b.injective hbeq)
        · rintro ⟨hzτ, hzneq⟩
          rw [← himageSτ] at hzτ
          obtain ⟨j, hjSτ, hbj⟩ := hzτ
          have hji : j ≠ i := by
            intro hji
            apply hzneq
            simpa [hji] using hbj.symm
          exact ⟨j, Finset.mem_erase.mpr ⟨hji, hjSτ⟩, hbj⟩
      have hyproper : y ∈ convexHull ℝ (τ \ {b i}) := by
        rw [← himageS]
        exact hyS
      have hsub := hyminimal (τ \ {b i}) Set.diff_subset hyproper
      exact (hsub hii).2 (by rfl)
    exact lt_of_le_of_ne (hy_nonneg i) (Ne.symm hnonzero)
  have hcoface_coord_ne (σ : Set (C → ℝ)) (hσ : σ ∈ K.cells)
      (hτσ : τ ⊆ σ) (hcardσ : Set.ncard σ = Fintype.card C)
      (v : C → ℝ) (hvτ : v ∉ τ) (hinsert : insert v τ = σ) :
      b.repr v i₀ ≠ 0 := by
    intro hcoord
    have hvspan : v ∈ Submodule.span ℝ (b '' (Sτ : Set σ₀)) := by
      apply b.mem_span_image.mpr
      intro j hj
      have hjne : j ≠ i₀ := by
        intro hji
        subst j
        exact Finsupp.notMem_support_iff.mpr hcoord hj
      simpa [Sτ] using hjne
    rw [himageSτ] at hvspan
    letI : Fintype σ := (K.finite_vertices σ hσ).fintype
    letI : Nonempty σ :=
      ⟨⟨(K.nonempty_cells σ hσ).choose,
        (K.nonempty_cells σ hσ).choose_spec⟩⟩
    obtain ⟨c, hc⟩ :=
      triangulation_top_cell_is_basis K σ hσ hcardσ
    have hvσ : v ∈ σ := by
      rw [← hinsert]
      exact Set.mem_insert v τ
    let iv : σ := ⟨v, hvσ⟩
    have himage :
        c '' ({iv}ᶜ : Set σ) = τ := by
      ext z
      constructor
      · rintro ⟨j, hj, rfl⟩
        have hjσ : (j : C → ℝ) ∈ insert v τ := hinsert.symm ▸ j.property
        rcases hjσ with hjv | hjτ
        · exfalso
          apply hj
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          apply Subtype.ext
          exact hjv
        · rw [hc]
          exact hjτ
      · intro hzτ
        let j : σ := ⟨z, hτσ hzτ⟩
        have hjne : j ≠ iv := by
          intro hji
          have hzv : z = v := congrArg Subtype.val hji
          exact hvτ (hzv ▸ hzτ)
        refine ⟨j, ?_, ?_⟩
        · simpa using hjne
        · rw [hc]
    have hvnot :
        c iv ∉ Submodule.span ℝ (c '' ({iv}ᶜ : Set σ)) :=
      c.linearIndependent.notMem_span iv
    have himage' : Subtype.val '' ({iv}ᶜ : Set σ) = τ := by
      rw [← hc]
      exact himage
    rw [hc, himage'] at hvnot
    exact hvnot hvspan
  have hsum_Sτ (f : σ₀ → ℝ) :
      ∑ i : Sτ, f i.1 = (∑ i, f i) - f i₀ := by
    rw [Finset.sum_coe_sort_eq_attach, Finset.sum_attach]
    simp [Sτ]
  have hsum_Sτ_smul (f : σ₀ → ℝ) :
      ∑ i : Sτ, f i.1 • b i.1 =
        (∑ i, f i • b i) - f i₀ • b i₀ := by
    rw [Finset.sum_coe_sort_eq_attach]
    rw [Finset.sum_attach Sτ (fun i => f i • b i)]
    simp [Sτ]
  have hmem_coface_of_coeff (ρ : Set (C → ℝ)) (w : C → ℝ)
      (hwτ : w ∉ τ) (hinsertw : insert w τ = ρ)
      (p : C → ℝ) (hp : p ∈ stdSimplex ℝ C)
      (hwStd : w ∈ stdSimplex ℝ C)
      (hα : b.repr w i₀ ≠ 0)
      (hlam_nonneg : 0 ≤ b.repr p i₀ / b.repr w i₀)
      (hrest : ∀ i : σ₀, i ≠ i₀ →
        0 ≤ b.repr p i -
          (b.repr p i₀ / b.repr w i₀) * b.repr w i) :
      p ∈ convexHull ℝ ρ := by
    let q : Option Sτ → (C → ℝ)
      | none => w
      | some i => b i.1
    have hqrange : Set.range q = ρ := by
      ext z
      constructor
      · rintro ⟨j, rfl⟩
        cases j with
        | none =>
            rw [← hinsertw]
            exact Set.mem_insert w τ
        | some j =>
            rw [← hinsertw]
            right
            rw [← himageSτ]
            exact ⟨j.1, j.2, rfl⟩
      · intro hz
        rw [← hinsertw] at hz
        rcases hz with rfl | hzτ
        · exact ⟨none, rfl⟩
        · rw [← himageSτ] at hzτ
          obtain ⟨j, hjS, hbj⟩ := hzτ
          exact ⟨some ⟨j, hjS⟩, hbj⟩
    rw [← hqrange, convexHull_range_eq_exists_affineCombination]
    let lam : ℝ := b.repr p i₀ / b.repr w i₀
    let r : Option Sτ → ℝ
      | none => lam
      | some i => b.repr p i.1 - lam * b.repr w i.1
    have hlam : lam * b.repr w i₀ = b.repr p i₀ := by
      dsimp [lam]
      field_simp
    have hrsum : ∑ j, r j = 1 := by
      simp only [Fintype.sum_option, r]
      change lam + ∑ x : Sτ,
        (fun i : σ₀ => b.repr p i - lam * b.repr w i) x.1 = 1
      rw [hsum_Sτ (fun i : σ₀ =>
        b.repr p i - lam * b.repr w i)]
      simp only [Finset.sum_sub_distrib, Finset.sum_mul]
      rw [hrepr_sum p hp, ← Finset.mul_sum, hrepr_sum w hwStd, hlam]
      ring
    refine ⟨Finset.univ, r, ?_, by simpa using hrsum, ?_⟩
    · intro j hj
      cases j with
      | none => exact hlam_nonneg
      | some j =>
          exact hrest j.1 (Finset.mem_erase.mp j.2).1
    · rw [Finset.affineCombination_eq_linear_combination _ _ _ (by
          simpa using hrsum)]
      simp only [Fintype.sum_option, q, r]
      change lam • w + ∑ x : Sτ,
        (fun i : σ₀ => b.repr p i - lam * b.repr w i) x.1 • b x.1 = p
      rw [hsum_Sτ_smul (fun i : σ₀ =>
        b.repr p i - lam * b.repr w i)]
      simp only [sub_smul, Finset.sum_sub_distrib, b.sum_repr]
      have hfactor :
          ∑ x, (lam * b.repr w x) • b x = lam • w := by
        simp_rw [mul_smul]
        rw [← Finset.smul_sum, b.sum_repr]
      rw [hfactor]
      have hsmul :
          (lam * b.repr w i₀) • b i₀ = b.repr p i₀ • b i₀ :=
        congrArg (fun a : ℝ => a • b i₀) hlam
      rw [hsmul]
      module
  have hsame_sign (σ ρ : Set (C → ℝ))
      (hσ : σ ∈ K.cells) (hρ : ρ ∈ K.cells)
      (hτσ : τ ⊆ σ) (hτρ : τ ⊆ ρ)
      (hcardσ : Set.ncard σ = Fintype.card C)
      (hcardρ : Set.ncard ρ = Fintype.card C)
      (v w : C → ℝ) (hvτ : v ∉ τ) (hwτ : w ∉ τ)
      (hinsertv : insert v τ = σ) (hinsertw : insert w τ = ρ)
      (hsign : 0 < b.repr v i₀ * b.repr w i₀) :
      σ = ρ := by
    have hvStd : v ∈ stdSimplex ℝ C :=
      K.vertices_mem_standard_simplex σ hσ v
        (hinsertv ▸ Set.mem_insert v τ)
    have hwStd : w ∈ stdSimplex ℝ C :=
      K.vertices_mem_standard_simplex ρ hρ w
        (hinsertw ▸ Set.mem_insert w τ)
    have hαv := hcoface_coord_ne σ hσ hτσ hcardσ v hvτ hinsertv
    have hαw := hcoface_coord_ne ρ hρ hτρ hcardρ w hwτ hinsertw
    let path : ℝ → (C → ℝ) :=
      fun t => (1 - t) • y + t • v
    let good : Set ℝ :=
      {t | t < 1 ∧ ∀ i : σ₀, i ≠ i₀ →
        0 < ((1 - t) * b.repr y i + t * b.repr v i) -
          (((1 - t) * b.repr y i₀ + t * b.repr v i₀) /
            b.repr w i₀) * b.repr w i}
    have hgood_open : IsOpen good := by
      have hleft : IsOpen {t : ℝ | t < 1} :=
        isOpen_lt continuous_id continuous_const
      have hright : IsOpen {t : ℝ | ∀ i : σ₀, i ≠ i₀ →
          0 < ((1 - t) * b.repr y i + t * b.repr v i) -
            (((1 - t) * b.repr y i₀ + t * b.repr v i₀) /
              b.repr w i₀) * b.repr w i} := by
        simp only [Set.setOf_forall]
        apply isOpen_iInter_of_finite
        intro i
        apply isOpen_iInter_of_finite
        intro hi
        apply isOpen_lt continuous_const
        fun_prop
      exact hleft.inter hright
    have hzero_good : (0 : ℝ) ∈ good := by
      constructor
      · norm_num
      · intro i hi
        simpa [path, hy_i₀] using hy_strict i hi
    obtain ⟨t, htpos, htgood⟩ :=
      exists_positive_parameter_in_open_preimage good hgood_open id
        continuous_id hzero_good
    have ht1 : t < 1 := htgood.1
    let p : C → ℝ := path t
    have hpStd : p ∈ stdSimplex ℝ C :=
      (convex_stdSimplex ℝ C) hyStd hvStd
        (sub_nonneg.mpr (le_of_lt ht1)) (le_of_lt htpos) (by ring)
    have hpcoord : b.repr p i₀ = t * b.repr v i₀ := by
      simp [p, path, hy_i₀]
    have hpσ : p ∈ convexHull ℝ σ := by
      apply hmem_coface_of_coeff σ v hvτ hinsertv p hpStd hvStd hαv
      · rw [hpcoord]
        field_simp
        exact le_of_lt htpos
      · intro i hi
        have hpi :
            b.repr p i = (1 - t) * b.repr y i + t * b.repr v i := by
          simp [p, path]
        rw [hpi, hpcoord]
        have hratio :
            t * b.repr v i₀ / b.repr v i₀ = t := by
          field_simp
        rw [hratio]
        nlinarith [hy_strict i hi]
    have hpρ : p ∈ convexHull ℝ ρ := by
      apply hmem_coface_of_coeff ρ w hwτ hinsertw p hpStd hwStd hαw
      · rw [hpcoord]
        apply le_of_lt
        apply (div_pos_iff).2
        rcases (mul_pos_iff.mp hsign) with ⟨hvi, hwi⟩ | ⟨hvi, hwi⟩
        · exact Or.inl ⟨mul_pos htpos hvi, hwi⟩
        · exact Or.inr ⟨mul_neg_of_pos_of_neg htpos hvi, hwi⟩
      · intro i hi
        simpa [p, path] using le_of_lt (htgood.2 i hi)
    by_contra hne
    have hvw : v ≠ w := by
      intro hvw
      apply hne
      rw [← hinsertv, ← hinsertw, hvw]
    have hinter : σ ∩ ρ = τ := by
      rw [← hinsertv, ← hinsertw]
      ext z
      simp only [Set.mem_inter_iff, Set.mem_insert_iff]
      constructor
      · rintro ⟨hv | hz, hw | hz'⟩
        · exact (hvw (hv.symm.trans hw)).elim
        · exact (hvτ (hv ▸ hz')).elim
        · exact hz
        · exact hz
      · intro hz
        exact ⟨Or.inr hz, Or.inr hz⟩
    have hpface : p ∈ convexHull ℝ (σ ∩ ρ) := by
      rw [← K.face_to_face σ hσ ρ hρ]
      exact ⟨hpσ, hpρ⟩
    rw [hinter] at hpface
    have hpzero := hcoord_i₀_of_mem_τ p hpface
    rw [hpcoord] at hpzero
    exact (mul_ne_zero (ne_of_gt htpos) hαv) hpzero
  have hb_i₀ : b i₀ = v₀ := by
    rw [hb]
  have hv₀coord : b.repr v₀ i₀ = 1 := by
    rw [← hb_i₀]
    simp
  let badCells : Set (Set (C → ℝ)) :=
    {ρ | ρ ∈ K.cells ∧ ¬ τ ⊆ ρ}
  have hbadCells : badCells.Finite := by
    apply K.finite_cells.subset
    intro ρ hρ
    exact hρ.1
  have hbadClosed : IsClosed (⋃ ρ ∈ badCells, convexHull ℝ ρ) := by
    apply hbadCells.isClosed_biUnion
    intro ρ hρ
    exact Set.Finite.isClosed_convexHull (𝕜 := ℝ)
      (K.finite_vertices ρ hρ.1)
  let good : Set (C → ℝ) :=
    {p | (∀ a : C, 0 < p a) ∧
      ∀ ρ ∈ K.cells, ¬ τ ⊆ ρ → p ∉ convexHull ℝ ρ}
  have hpositive_open : IsOpen {p : C → ℝ | ∀ a : C, 0 < p a} := by
    simp only [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro a
    exact isOpen_lt continuous_const (continuous_apply a)
  have hgood_eq : good =
      {p : C → ℝ | ∀ a : C, 0 < p a} ∩
        (⋃ ρ ∈ badCells, convexHull ℝ ρ)ᶜ := by
    ext p
    simp [good, badCells]
  have hgood_open : IsOpen good := by
    rw [hgood_eq]
    exact hpositive_open.inter hbadClosed.isOpen_compl
  have hygood : y ∈ good := by
    refine ⟨hypos, ?_⟩
    intro ρ hρ hnot hyρ
    exact hnot (hycells ρ hρ hyρ)
  let opposite : ℝ → (C → ℝ) :=
    fun t => (1 + t) • y - t • v₀
  have hopposite_cont : Continuous opposite := by
    dsimp [opposite]
    fun_prop
  have hzero_opposite : opposite 0 ∈ good := by
    simpa [opposite] using hygood
  obtain ⟨t, htpos, htgood⟩ :=
    exists_positive_parameter_in_open_preimage good hgood_open opposite
      hopposite_cont hzero_opposite
  let p : C → ℝ := opposite t
  have hv₀Std : v₀ ∈ stdSimplex ℝ C :=
    K.vertices_mem_standard_simplex σ₀ hσ₀ v₀ hv₀σ₀
  have hpStd : p ∈ stdSimplex ℝ C := by
    constructor
    · intro a
      exact le_of_lt (htgood.1 a)
    · change ∑ a, ((1 + t) * y a - t * v₀ a) = 1
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        hyStd.2, hv₀Std.2]
      ring
  have hpcoord : b.repr p i₀ = -t := by
    simp [p, opposite, hy_i₀, hv₀coord]
  have hpnotσ₀ : p ∉ convexHull ℝ σ₀ := by
    intro hpσ₀
    have hnonneg := (hmem_iff p hpStd).mp hpσ₀ i₀
    rw [hpcoord] at hnonneg
    linarith
  have hpcover := hpStd
  rw [K.cover] at hpcover
  simp only [Set.mem_iUnion] at hpcover
  obtain ⟨ρ, hρ, hpρ⟩ := hpcover
  have hτρ : τ ⊆ ρ := by
    by_contra hnot
    exact htgood.2 ρ hρ hnot hpρ
  obtain ⟨σm, hσm, hρσm, hcardσm⟩ := K.pure ρ hρ
  have hτσm : τ ⊆ σm := hτρ.trans hρσm
  have hpσm : p ∈ convexHull ℝ σm := convexHull_mono hρσm hpρ
  have hσmne : σm ≠ σ₀ := by
    intro heq
    apply hpnotσ₀
    rwa [← heq]
  obtain ⟨w, hwτ, hinsertw⟩ :=
    (Set.exists_eq_insert_iff_ncard hτfinite).2
      ⟨hτσm, by omega⟩
  have hwcoord_ne : b.repr w i₀ ≠ 0 :=
    hcoface_coord_ne σm hσm hτσm hcardσm w hwτ hinsertw
  have hwcoord_neg : b.repr w i₀ < 0 := by
    rcases lt_trichotomy (b.repr w i₀) 0 with hneg | hzero | hpos
    · exact hneg
    · exact (hwcoord_ne hzero).elim
    · exfalso
      apply hσmne
      exact hsame_sign σm σ₀ hσm hσ₀ hτσm hτσ₀ hcardσm hcardσ₀
        w v₀ hwτ hv₀τ hinsertw hinsert₀ (by
          rw [hv₀coord, mul_one]
          exact hpos)
  have hclassify (σ : Set (C → ℝ))
      (hσ : σ ∈ K.cells ∧ τ ⊆ σ ∧
        Set.ncard σ = Fintype.card C) :
      σ = σ₀ ∨ σ = σm := by
    obtain ⟨hσcell, hτσ, hcardσ⟩ := hσ
    obtain ⟨v, hvτ, hinsertv⟩ :=
      (Set.exists_eq_insert_iff_ncard hτfinite).2
        ⟨hτσ, by omega⟩
    have hvcoord_ne : b.repr v i₀ ≠ 0 :=
      hcoface_coord_ne σ hσcell hτσ hcardσ v hvτ hinsertv
    rcases lt_trichotomy (b.repr v i₀) 0 with hneg | hzero | hpos
    · right
      exact hsame_sign σ σm hσcell hσm hτσ hτσm hcardσ hcardσm
        v w hvτ hwτ hinsertv hinsertw
          (mul_pos_of_neg_of_neg hneg hwcoord_neg)
    · exact (hvcoord_ne hzero).elim
    · left
      exact hsame_sign σ σ₀ hσcell hσ₀ hτσ hτσ₀ hcardσ hcardσ₀
        v v₀ hvτ hv₀τ hinsertv hinsert₀ (by
          rw [hv₀coord, mul_one]
          exact hpos)
  have hcofaces :
      {σ : Set (C → ℝ) |
        σ ∈ K.cells ∧ τ ⊆ σ ∧ Set.ncard σ = Fintype.card C} =
      {σ₀, σm} := by
    ext σ
    constructor
    · intro hσ
      rcases hclassify σ hσ with hσ₀ | hσm'
      · exact Set.mem_insert_iff.mpr (Or.inl hσ₀)
      · exact Set.mem_insert_iff.mpr
          (Or.inr (Set.mem_singleton_iff.mpr hσm'))
    · intro hσ
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
      rcases hσ with rfl | rfl
      · exact ⟨hσ₀, hτσ₀, hcardσ₀⟩
      · exact ⟨hσm, hτσm, hcardσm⟩
  rw [hcofaces]
  exact Set.ncard_eq_two.mpr ⟨σ₀, σm, hσmne.symm, rfl⟩

@[blueprint "lem:sperner-incidence-parity"
  (statement := /-- Let \(C\) be a finite set with at least two elements, let \(K\) be
  a finite triangulation of \(\Delta(C)\), and let \(\ell\) be a Sperner labeling. For
  every \(b\in C\), the parity of the fully labeled top-dimensional cells equals the
  parity of the facets in \(x(b)=0\) labeled by \(C\setminus\{b\}\). -/)
  (proof := /-- We first determine the number of top-dimensional cofaces of every
  facet \(\tau\) carrying all labels in \(C\setminus\{b\}\). Suppose initially that
  every vertex of \(\tau\) has zero \(b\)-coordinate. Purity in
  \cref{def:finite-simplex-triangulation} supplies a top-dimensional coface
  \(\sigma_0=\tau\cup\{v_0\}\). Its extra vertex has strictly positive
  \(b\)-coordinate: nonnegativity follows from membership in the standard simplex, and
  vanishing would contradict
  \cref{lem:triangulation-top-cell-is-basis}, since then every vector in a basis of
  \(\mathbb R^C\) would have zero \(b\)-coordinate.

  This coface is unique. Indeed, if
  \(\rho=\tau\cup\{w\}\) were another top-dimensional coface, then \(w(b)>0\) as well.
  Use \cref{lem:triangulation-top-cell-is-basis} for \(\rho\), and let \(y\) be the
  centroid of the basis vectors belonging to \(\tau\). All their coefficients in
  \(y\) are strictly positive. The coefficient of \(v_0\) in the \(w\)-direction is
  also positive, because evaluation at \(b\) expresses
  \(v_0(b)\) as that coefficient times \(w(b)\). Consequently all coefficients,
  except possibly the \(w\)-coefficient, remain positive along
  \(p_t=(1-t)y+tv_0\) for every sufficiently small \(t>0\); the existence of such a
  parameter follows from
  \cref{lem:exists-positive-parameter-in-open-preimage}. The \(w\)-coefficient is
  positive for every \(t>0\). Thus \(p_t\) belongs to both
  \(\operatorname{conv}(\sigma_0)\) and \(\operatorname{conv}(\rho)\). The
  face-to-face axiom in \cref{def:finite-simplex-triangulation} places it in
  \(\operatorname{conv}(\tau)\), where the \(b\)-coordinate is zero, whereas
  \(p_t(b)=t v_0(b)>0\), a contradiction. Hence a facet in \(x(b)=0\) has exactly one
  top-dimensional coface.

  For an arbitrary facet under consideration, the Sperner condition in
  \cref{def:sperner-labeling} ensures that, for every \(a\neq b\), some vertex has
  strictly positive \(a\)-coordinate. If some vertex also has positive
  \(b\)-coordinate, the centroid of \(\tau\) has every coordinate strictly positive,
  so \cref{lem:triangulation-interior-facet-two-cofaces} gives exactly two
  top-dimensional cofaces. Otherwise \(\tau\subseteq\{x:x(b)=0\}\), and the preceding
  argument gives exactly one. The coface count is therefore odd precisely for the
  facets on the right-hand side.

  We next compute the incidence count over a fixed top-dimensional cell \(\sigma\).
  Its facets correspond bijectively to vertices \(v\in\sigma\), by deleting \(v\).
  If \(\sigma\setminus\{v\}\) carries all labels in \(C\setminus\{b\}\), then its
  \(|C|-1\) vertices map bijectively to those \(|C|-1\) labels. If
  \(\ell(v)=b\), the cell is fully labeled and this is the unique qualifying
  deletion. If \(\ell(v)\neq b\), precisely one other vertex has label \(\ell(v)\);
  deleting either of these two vertices qualifies, and no other deletion does. If no
  deletion qualifies, the cell is not fully labeled. Thus a top-dimensional cell has
  an odd number of qualifying facets exactly when it is fully labeled. Moreover, any
  fully labeled cell is automatically top-dimensional: surjectivity gives at least
  \(|C|\) vertices, while purity gives a containing cell with exactly \(|C|\)
  vertices.

  Finally, count the finite incidence relation
  \(\{(\sigma,\tau):\tau\subseteq\sigma\}\), restricting \(\sigma\) to
  top-dimensional cells and \(\tau\) to facets carrying \(C\setminus\{b\}\).
  Summing the fiber cardinalities first over cells and then over facets gives the same
  total. Reducing the two sums modulo \(2\) and applying the two fiber computations
  above yields the asserted equality. -/)
  (title := /-- The Sperner incidence count modulo two -/)
  (latexEnv := "lemma")]
lemma sperner_incidence_parity {C : Type*} [Fintype C] [Nonempty C]
    (K : finite_simplex_triangulation C) (label : (C → ℝ) → C)
    (hlabel : sperner_labeling K label) (b : C)
    (hC : 1 < Fintype.card C) :
    Set.ncard
        {σ : Set (C → ℝ) |
          σ ∈ K.cells ∧ Set.SurjOn label σ Set.univ} % 2 =
      Set.ncard
        {τ : Set (C → ℝ) |
          τ ∈ K.cells ∧
            Set.ncard τ + 1 = Fintype.card C ∧
              Set.SurjOn label τ {a : C | a ≠ b} ∧
                ∀ x ∈ τ, x b = 0} % 2 := by
  classical
  have boundary_unique (τ : Set (C → ℝ)) (hτ : τ ∈ K.cells)
      (hcardτ : Set.ncard τ + 1 = Fintype.card C)
      (hzero : ∀ x ∈ τ, x b = 0) :
      Set.ncard
          {σ : Set (C → ℝ) |
            σ ∈ K.cells ∧ τ ⊆ σ ∧
              Set.ncard σ = Fintype.card C} = 1 := by
    have hτfinite := K.finite_vertices τ hτ
    obtain ⟨σ₀, hσ₀, hτσ₀, hcardσ₀⟩ := K.pure τ hτ
    obtain ⟨v₀, hv₀τ, hinsert₀⟩ :=
      (Set.exists_eq_insert_iff_ncard hτfinite).2
        ⟨hτσ₀, by omega⟩
    have hv₀σ₀ : v₀ ∈ σ₀ := by
      rw [← hinsert₀]
      exact Set.mem_insert v₀ τ
    have hextra_pos (σ : Set (C → ℝ)) (hσ : σ ∈ K.cells)
        (hτσ : τ ⊆ σ) (hcardσ : Set.ncard σ = Fintype.card C)
        (v : C → ℝ) (hvτ : v ∉ τ) (hinsert : insert v τ = σ) :
        0 < v b := by
      have hvStd : v ∈ stdSimplex ℝ C :=
        K.vertices_mem_standard_simplex σ hσ v
          (hinsert ▸ Set.mem_insert v τ)
      have hvne : v b ≠ 0 := by
        intro hvzero
        letI : Fintype σ := (K.finite_vertices σ hσ).fintype
        letI : Nonempty σ :=
          ⟨⟨(K.nonempty_cells σ hσ).choose,
            (K.nonempty_cells σ hσ).choose_spec⟩⟩
        obtain ⟨c, hc⟩ :=
          triangulation_top_cell_is_basis K σ hσ hcardσ
        have hall (i : σ) : (c i) b = 0 := by
          rw [hc]
          have hi : (i : C → ℝ) ∈ insert v τ :=
            hinsert.symm ▸ i.property
          rcases hi with hiv | hiτ
          · simpa [hiv] using hvzero
          · exact hzero i hiτ
        let q : C → ℝ := Pi.single b 1
        have hq := congrArg (fun z : C → ℝ => z b) (c.sum_repr q)
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hq
        have hsumzero :
            ∑ i, c.repr q i * c i b = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          rw [hall i, mul_zero]
        rw [hsumzero] at hq
        have hqb : q b = 1 := by simp [q]
        linarith
      exact lt_of_le_of_ne (hvStd.1 b) (Ne.symm hvne)
    have hv₀pos :=
      hextra_pos σ₀ hσ₀ hτσ₀ hcardσ₀ v₀ hv₀τ hinsert₀
    have hclassify (ρ : Set (C → ℝ))
        (hρmem : ρ ∈
          {σ : Set (C → ℝ) |
            σ ∈ K.cells ∧ τ ⊆ σ ∧
              Set.ncard σ = Fintype.card C}) :
        ρ = σ₀ := by
      obtain ⟨hρ, hτρ, hcardρ⟩ := hρmem
      obtain ⟨w, hwτ, hinsertw⟩ :=
        (Set.exists_eq_insert_iff_ncard hτfinite).2
          ⟨hτρ, by omega⟩
      have hwρ : w ∈ ρ := by
        rw [← hinsertw]
        exact Set.mem_insert w τ
      have hwpos :=
        hextra_pos ρ hρ hτρ hcardρ w hwτ hinsertw
      by_contra hρne
      have hwv₀ : w ≠ v₀ := by
        intro hwv
        apply hρne
        rw [← hinsertw, ← hinsert₀, hwv]
      letI : Fintype ρ := (K.finite_vertices ρ hρ).fintype
      letI : Nonempty ρ :=
        ⟨⟨(K.nonempty_cells ρ hρ).choose,
          (K.nonempty_cells ρ hρ).choose_spec⟩⟩
      obtain ⟨c, hc⟩ :=
        triangulation_top_cell_is_basis K ρ hρ hcardρ
      let iw : ρ := ⟨w, hwρ⟩
      let Sτ : Finset ρ := Finset.univ.erase iw
      have hc_iw : c iw = w := by rw [hc]
      have hindex_mem_τ {i : ρ} (hi : i ≠ iw) : c i ∈ τ := by
        rw [hc]
        have hiρ : (i : C → ℝ) ∈ insert w τ :=
          hinsertw.symm ▸ i.property
        rcases hiρ with hiw | hiτ
        · exfalso
          apply hi
          apply Subtype.ext
          exact hiw
        · exact hiτ
      have himageSτ : c '' (Sτ : Set ρ) = τ := by
        ext z
        constructor
        · rintro ⟨i, hiS, rfl⟩
          apply hindex_mem_τ
          simpa [Sτ] using hiS
        · intro hzτ
          let i : ρ := ⟨z, hτρ hzτ⟩
          have hi : i ≠ iw := by
            intro hii
            have hzw : z = w := congrArg Subtype.val hii
            exact hwτ (hzw ▸ hzτ)
          refine ⟨i, ?_, ?_⟩
          · simp [Sτ, hi]
          · rw [hc]
      have hτnonempty := K.nonempty_cells τ hτ
      have hSτnonempty : Sτ.Nonempty := by
        obtain ⟨z, hzτ⟩ := hτnonempty
        rw [← himageSτ] at hzτ
        obtain ⟨i, hiS, hci⟩ := hzτ
        exact ⟨i, hiS⟩
      let d : ℝ := (Sτ.card : ℝ)
      have hdpos : 0 < d := by
        dsimp [d]
        exact_mod_cast (Finset.card_pos.mpr hSτnonempty)
      let y : C → ℝ :=
        ∑ i : Sτ, d⁻¹ • c i.1
      have hyconv : y ∈ convexHull ℝ τ := by
        rw [← himageSτ]
        have hrangeS :
            Set.range (fun i : Sτ => c i.1) =
              c '' (Sτ : Set ρ) := by
          ext z
          simp
        rw [← hrangeS, convexHull_range_eq_exists_affineCombination]
        have hweights : ∑ _ : Sτ, d⁻¹ = 1 := by
          simp only [Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul]
          change (Fintype.card Sτ : ℝ) * d⁻¹ = 1
          have hcardS : (Fintype.card Sτ : ℝ) = d := by
            simp [d]
          rw [hcardS]
          exact mul_inv_cancel₀ (ne_of_gt hdpos)
        refine ⟨Finset.univ, fun _ : Sτ => d⁻¹, ?_, hweights, ?_⟩
        · intro i hi
          exact le_of_lt (inv_pos.mpr hdpos)
        · rw [Finset.affineCombination_eq_linear_combination _ _ _
            hweights]
      have hyStd : y ∈ stdSimplex ℝ C :=
        convexHull_min
          (fun z hz => K.vertices_mem_standard_simplex τ hτ z hz)
          (convex_stdSimplex ℝ C) hyconv
      have hyrepr (i : ρ) :
          c.repr y i = if i ∈ Sτ then d⁻¹ else 0 := by
        simp only [y, map_sum, map_smul, Module.Basis.repr_self,
          Finsupp.coe_finset_sum, Finset.sum_apply,
          Finsupp.single_apply]
        by_cases hi : i ∈ Sτ
        · rw [if_pos hi]
          rw [Finset.sum_eq_single ⟨i, hi⟩]
          · simp
          · intro j hj hji
            have hval : j.1 ≠ i := by
              intro hval
              apply hji
              exact Subtype.ext hval
            simp [hval]
          · simp
        · rw [if_neg hi]
          apply Finset.sum_eq_zero
          intro j hj
          have hji : j.1 ≠ i := by
            intro hji
            apply hi
            simpa [hji] using j.2
          simp [hji]
      have hrepr_sum (p : C → ℝ) (hp : p ∈ stdSimplex ℝ C) :
          ∑ i, c.repr p i = 1 := by
        have h := congrArg (fun z : C → ℝ => ∑ a, z a) (c.sum_repr p)
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
        rw [Finset.sum_comm] at h
        have hcsum (i : ρ) : ∑ a, (c i) a = 1 := by
          rw [hc]
          exact (K.vertices_mem_standard_simplex ρ hρ i i.property).2
        simpa only [← Finset.mul_sum, hcsum, mul_one, hp.2] using h
      have hcoord_repr (z : C → ℝ) :
          z b = c.repr z iw * w b := by
        have h := congrArg (fun q : C → ℝ => q b) (c.sum_repr z)
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
        have hsum :
            ∑ i, c.repr z i * c i b =
              c.repr z iw * w b := by
          rw [Finset.sum_eq_single iw]
          · rw [hc_iw]
          · intro i hi hne
            have hci := hzero (c i) (hindex_mem_τ hne)
            rw [hci, mul_zero]
          · intro hi
            exact (hi (Finset.mem_univ iw)).elim
        rw [hsum] at h
        exact h.symm
      have hvreprpos : 0 < c.repr v₀ iw := by
        have hprod : 0 < c.repr v₀ iw * w b := by
          rw [← hcoord_repr]
          exact hv₀pos
        nlinarith
      let path : ℝ → (C → ℝ) :=
        fun t => (1 - t) • y + t • v₀
      let good : Set ℝ :=
        {t | t < 1 ∧ ∀ i : ρ, i ≠ iw →
          0 < (1 - t) * c.repr y i + t * c.repr v₀ i}
      have hgood_open : IsOpen good := by
        have hleft : IsOpen {t : ℝ | t < 1} :=
          isOpen_lt continuous_id continuous_const
        have hright : IsOpen {t : ℝ | ∀ i : ρ, i ≠ iw →
            0 < (1 - t) * c.repr y i + t * c.repr v₀ i} := by
          simp only [Set.setOf_forall]
          apply isOpen_iInter_of_finite
          intro i
          apply isOpen_iInter_of_finite
          intro hi
          apply isOpen_lt continuous_const
          fun_prop
        exact hleft.inter hright
      have hzero_good : (0 : ℝ) ∈ good := by
        constructor
        · norm_num
        · intro i hi
          have hiS : i ∈ Sτ := by simp [Sτ, hi]
          simpa [hyrepr i, hiS] using inv_pos.mpr hdpos
      obtain ⟨t, htpos, htgood⟩ :=
        exists_positive_parameter_in_open_preimage good hgood_open id
          continuous_id hzero_good
      have ht1 : t < 1 := htgood.1
      let p : C → ℝ := path t
      have hpStd : p ∈ stdSimplex ℝ C :=
        (convex_stdSimplex ℝ C) hyStd
          (K.vertices_mem_standard_simplex σ₀ hσ₀ v₀ hv₀σ₀)
          (sub_nonneg.mpr (le_of_lt ht1)) (le_of_lt htpos)
          (by ring)
      have hpρ : p ∈ convexHull ℝ ρ := by
        have hrange : Set.range c = ρ := by
          rw [hc]
          ext z
          simp
        rw [← hrange, convexHull_range_eq_exists_affineCombination]
        refine ⟨Finset.univ, fun i => c.repr p i, ?_,
          by simpa using hrepr_sum p hpStd, ?_⟩
        · intro i hi
          by_cases hii : i = iw
          · subst i
            have hyiw : c.repr y iw = 0 := by
              rw [hyrepr]
              simp [Sτ]
            simp [p, path, hyiw]
            exact le_of_lt (mul_pos htpos hvreprpos)
          · have hi := htgood.2 i hii
            simpa [p, path] using le_of_lt hi
        · rw [Finset.affineCombination_eq_linear_combination _ _ _
              (by simpa using hrepr_sum p hpStd)]
          exact c.sum_repr p
      have hpσ₀ : p ∈ convexHull ℝ σ₀ := by
        apply (convex_convexHull ℝ σ₀)
          (convexHull_mono hτσ₀ hyconv)
          (subset_convexHull ℝ σ₀ hv₀σ₀)
          (sub_nonneg.mpr (le_of_lt ht1)) (le_of_lt htpos)
        ring
      have hinter : ρ ∩ σ₀ = τ := by
        rw [← hinsertw, ← hinsert₀]
        ext z
        simp only [Set.mem_inter_iff, Set.mem_insert_iff]
        constructor
        · rintro ⟨hw | hz, hv | hz'⟩
          · exact (hwv₀ (hw.symm.trans hv)).elim
          · exact (hwτ (hw ▸ hz')).elim
          · exact hz
          · exact hz
        · intro hz
          exact ⟨Or.inr hz, Or.inr hz⟩
      have hpface : p ∈ convexHull ℝ τ := by
        rw [← hinter, ← K.face_to_face ρ hρ σ₀ hσ₀]
        exact ⟨hpρ, hpσ₀⟩
      have hconvzero : Convex ℝ {z : C → ℝ | z b = 0} := by
        intro x hx y hy a d ha hd had
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        simp [hx, hy]
      have hpzero : p b = 0 := by
        exact convexHull_min
          (fun z hz => hzero z hz) hconvzero hpface
      have hppos : 0 < p b := by
        have hyzero : y b = 0 :=
          convexHull_min
            (fun z hz => hzero z hz)
            hconvzero
            hyconv
        simp [p, path, hyzero]
        exact mul_pos htpos hv₀pos
      linarith
    have hcofaces :
        {σ : Set (C → ℝ) |
          σ ∈ K.cells ∧ τ ⊆ σ ∧
            Set.ncard σ = Fintype.card C} = {σ₀} := by
      ext ρ
      constructor
      · intro hρ
        exact Set.mem_singleton_iff.mpr (hclassify ρ hρ)
      · intro hρ
        rw [Set.mem_singleton_iff] at hρ
        subst ρ
        exact ⟨hσ₀, hτσ₀, hcardσ₀⟩
    rw [hcofaces, Set.ncard_singleton]
  have facet_coface_parity (τ : Set (C → ℝ)) (hτ : τ ∈ K.cells)
      (hcardτ : Set.ncard τ + 1 = Fintype.card C)
      (hsurj : Set.SurjOn label τ {a : C | a ≠ b}) :
      Set.ncard
          {σ : Set (C → ℝ) |
            σ ∈ K.cells ∧ τ ⊆ σ ∧
              Set.ncard σ = Fintype.card C} % 2 =
        if ∀ x ∈ τ, x b = 0 then 1 else 0 := by
    by_cases hzero : ∀ x ∈ τ, x b = 0
    · rw [if_pos hzero, boundary_unique τ hτ hcardτ hzero]
    · rw [if_neg hzero]
      have hτfinite := K.finite_vertices τ hτ
      let sτ : Finset (C → ℝ) := hτfinite.toFinset
      have hsτnonempty : sτ.Nonempty := by
        simpa [sτ] using K.nonempty_cells τ hτ
      let y : C → ℝ := sτ.centroid ℝ id
      have hyconv : y ∈ convexHull ℝ τ := by
        have hy :=
          Finset.centroid_mem_convexHull (R := ℝ) sτ hsτnonempty
        simpa [y, sτ] using hy
      have hsτcardpos : (0 : ℝ) < sτ.card := by
        exact_mod_cast Finset.card_pos.mpr hsτnonempty
      have hsτcardne : (sτ.card : ℝ) ≠ 0 :=
        ne_of_gt hsτcardpos
      have hyformula :
          y = (sτ.card : ℝ)⁻¹ • ∑ x ∈ sτ, x := by
        change sτ.centroid ℝ id =
          (sτ.card : ℝ)⁻¹ • ∑ x ∈ sτ, x
        rw [Finset.centroid_eq_centerMass sτ hsτnonempty]
        simp [Finset.centerMass, Finset.centroidWeights,
          Finset.smul_sum, hsτcardne, smul_smul]
      have hypos (a : C) : 0 < y a := by
        have hnonneg : ∀ x ∈ sτ, 0 ≤ x a := by
          intro x hx
          have hxτ : x ∈ τ := by simpa [sτ] using hx
          exact (K.vertices_mem_standard_simplex τ hτ x hxτ).1 a
        have hex : ∃ x ∈ sτ, 0 < x a := by
          by_cases hab : a = b
          · subst a
            push Not at hzero
            obtain ⟨x, hxτ, hxb⟩ := hzero
            refine ⟨x, by simpa [sτ] using hxτ, ?_⟩
            exact lt_of_le_of_ne
              ((K.vertices_mem_standard_simplex τ hτ x hxτ).1 b)
              (Ne.symm hxb)
          · obtain ⟨x, hxτ, hlabelx⟩ := hsurj hab
            refine ⟨x, by simpa [sτ] using hxτ, ?_⟩
            have hxnonzero := hlabel x
              (Set.mem_sUnion_of_mem hxτ hτ)
            rw [hlabelx] at hxnonzero
            exact lt_of_le_of_ne
              ((K.vertices_mem_standard_simplex τ hτ x hxτ).1 a)
              (Ne.symm hxnonzero)
        have hsumpos : 0 < ∑ x ∈ sτ, x a :=
          (Finset.sum_pos_iff_of_nonneg hnonneg).2 hex
        rw [hyformula]
        simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
        exact mul_pos (inv_pos.mpr hsτcardpos) hsumpos
      have hinterior : ∃ x ∈ convexHull ℝ τ, ∀ a : C, 0 < x a :=
        ⟨y, hyconv, hypos⟩
      rw [triangulation_interior_facet_two_cofaces K τ hτ hcardτ
        hinterior]
  have top_facet_parity (σ : Set (C → ℝ)) (hσ : σ ∈ K.cells)
      (hcardσ : Set.ncard σ = Fintype.card C) :
      Set.ncard
          {τ : Set (C → ℝ) |
            τ ∈ K.cells ∧ τ ⊆ σ ∧
              Set.ncard τ + 1 = Fintype.card C ∧
                Set.SurjOn label τ {a : C | a ≠ b}} % 2 =
        if Set.SurjOn label σ Set.univ then 1 else 0 := by
    let Vgood : Set (C → ℝ) :=
      {v | v ∈ σ ∧
        Set.SurjOn label (σ \ {v}) {a : C | a ≠ b}}
    let faces : Set (Set (C → ℝ)) :=
      {τ | τ ∈ K.cells ∧ τ ⊆ σ ∧
        Set.ncard τ + 1 = Fintype.card C ∧
          Set.SurjOn label τ {a : C | a ≠ b}}
    change Set.ncard faces % 2 =
      if Set.SurjOn label σ Set.univ then 1 else 0
    have hfaces :
        faces = (fun v : C → ℝ => σ \ {v}) '' Vgood := by
      ext τ
      constructor
      · intro hτ
        obtain ⟨hτcell, hτσ, hcardτ, hsurjτ⟩ := hτ
        have hτfinite := K.finite_vertices τ hτcell
        obtain ⟨v, hvτ, hinsert⟩ :=
          (Set.exists_eq_insert_iff_ncard hτfinite).2
            ⟨hτσ, by omega⟩
        have hvσ : v ∈ σ := by
          rw [← hinsert]
          exact Set.mem_insert v τ
        have hdiff : σ \ {v} = τ := by
          rw [← hinsert]
          simp [hvτ]
        exact ⟨v, ⟨hvσ, hdiff.symm ▸ hsurjτ⟩, hdiff⟩
      · rintro ⟨v, hv, rfl⟩
        obtain ⟨hvσ, hsurjv⟩ := hv
        have hdiffcard :
            Set.ncard (σ \ {v}) + 1 = Fintype.card C := by
          rw [Set.ncard_sdiff_singleton_of_mem hvσ, hcardσ]
          omega
        have hdiffnonempty : (σ \ {v}).Nonempty := by
          apply (Set.ncard_pos
            ((K.finite_vertices σ hσ).sdiff (t := {v}))).mp
          rw [Set.ncard_sdiff_singleton_of_mem hvσ, hcardσ]
          omega
        exact ⟨K.closed_under_nonempty_faces σ hσ (σ \ {v})
            hdiffnonempty Set.diff_subset,
          Set.diff_subset, hdiffcard, hsurjv⟩
    have hdelinj :
        Set.InjOn (fun v : C → ℝ => σ \ {v}) Vgood := by
      intro v hv w hw heq
      have hvσ : v ∈ σ := hv.1
      have hwσ : w ∈ σ := hw.1
      by_contra hvw
      have hwmem : w ∈ σ \ {v} := by
        exact ⟨hwσ, by simpa [Set.mem_singleton_iff] using Ne.symm hvw⟩
      change σ \ {v} = σ \ {w} at heq
      rw [heq] at hwmem
      exact hwmem.2 (Set.mem_singleton_iff.mpr rfl)
    have hfacecard : Set.ncard faces = Set.ncard Vgood := by
      rw [hfaces]
      exact hdelinj.ncard_image
    have hVfinite : Vgood.Finite := by
      apply (K.finite_vertices σ hσ).subset
      intro v hv
      exact hv.1
    by_cases hV : Vgood.Nonempty
    · obtain ⟨v, hvV⟩ := hV
      have hvσ : v ∈ σ := hvV.1
      have hvgood := hvV.2
      let A := {x : C → ℝ // x ∈ σ \ {v}}
      let D := {a : C // a ≠ b}
      letI : Fintype A :=
        ((K.finite_vertices σ hσ).sdiff (t := {v})).fintype
      let pick (a : D) : C → ℝ :=
        Classical.choose (hvgood a.property)
      have hpickspec (a : D) :
          pick a ∈ σ \ {v} ∧ label (pick a) = a.1 :=
        Classical.choose_spec (hvgood a.property)
      let g : D → A := fun a => ⟨pick a, (hpickspec a).1⟩
      have hglabel (a : D) : label (g a).1 = a.1 :=
        (hpickspec a).2
      have hginj : Function.Injective g := by
        intro a d had
        apply Subtype.ext
        have := congrArg (fun x : A => label x.1) had
        simpa [hglabel] using this
      have hcardA :
          Fintype.card A = Fintype.card C - 1 := by
        change Fintype.card ↥(σ \ {v}) = Fintype.card C - 1
        rw [Set.fintypeCard_eq_ncard]
        rw [Set.ncard_sdiff_singleton_of_mem hvσ, hcardσ]
      have hcardD :
          Fintype.card D = Fintype.card C - 1 := by
        change Fintype.card {a : C // ¬a = b} =
          Fintype.card C - 1
        rw [Fintype.card_subtype_compl (fun a : C => a = b),
          Fintype.card_subtype_eq]
      have hgbij : Function.Bijective g :=
        (Fintype.bijective_iff_injective_and_card g).2
          ⟨hginj, hcardD.trans hcardA.symm⟩
      have hAlabel_ne (x : A) : label x.1 ≠ b := by
        obtain ⟨a, rfl⟩ := hgbij.2 x
        rw [hglabel]
        exact a.property
      have hAinjective :
          Function.Injective (fun x : A => label x.1) := by
        intro x y hxy
        obtain ⟨a, rfl⟩ := hgbij.2 x
        obtain ⟨d, rfl⟩ := hgbij.2 y
        apply congrArg g
        apply Subtype.ext
        simpa [hglabel] using hxy
      have hfull_iff :
          Set.SurjOn label σ Set.univ ↔ label v = b := by
        constructor
        · intro hfull
          obtain ⟨x, hxσ, hxl⟩ := hfull (Set.mem_univ b)
          have hxv : x = v := by
            by_contra hxv
            let xA : A := ⟨x, hxσ, by simpa using hxv⟩
            exact hAlabel_ne xA hxl
          simpa [hxv] using hxl
        · intro hvlabel
          intro a ha
          by_cases hab : a = b
          · subst a
            exact ⟨v, hvσ, hvlabel⟩
          · obtain ⟨x, hx, hxl⟩ := hvgood hab
            exact ⟨x, hx.1, hxl⟩
      have hgood_other_label (w : C → ℝ) (hwV : w ∈ Vgood)
          (hwv : w ≠ v) : label w = label v := by
        let wA : A := ⟨w, hwV.1, by simpa using hwv⟩
        have hwlabelne : label w ≠ b := hAlabel_ne wA
        obtain ⟨x, hx, hxl⟩ := hwV.2 hwlabelne
        by_cases hxv : x = v
        · simpa [hxv] using hxl.symm
        · let xA : A := ⟨x, hx.1, by simpa using hxv⟩
          have hxAwA : xA = wA := hAinjective (by
            change label x = label w
            exact hxl)
          have hxw : x = w := congrArg Subtype.val hxAwA
          exact (hx.2 (by simpa [hxw])).elim
      by_cases hvlabel : label v = b
      · have hVeq : Vgood = {v} := by
          ext w
          constructor
          · intro hwV
            by_cases hwv : w = v
            · simpa [hwv]
            · have hwlabel := hgood_other_label w hwV hwv
              let wA : A := ⟨w, hwV.1, by simpa using hwv⟩
              exact (hAlabel_ne wA (hwlabel.trans hvlabel)).elim
          · intro hw
            simp only [Set.mem_singleton_iff] at hw
            simpa [hw] using hvV
        rw [show (if Set.SurjOn label σ Set.univ then 1 else 0) = 1
          by simp [hfull_iff, hvlabel]]
        rw [hfacecard, hVeq, Set.ncard_singleton]
      · obtain ⟨w, hwA, hwlabel⟩ := hvgood hvlabel
        have hwv : w ≠ v := by
          exact fun hwv => hwA.2 (by simpa [hwv])
        have hwV : w ∈ Vgood := by
          refine ⟨hwA.1, ?_⟩
          intro a ha
          by_cases halabel : a = label v
          · exact ⟨v, ⟨hvσ, by simpa using Ne.symm hwv⟩,
              by simpa [halabel]⟩
          · obtain ⟨x, hx, hxl⟩ := hvgood ha
            have hxw : x ≠ w := by
              intro hxw
              apply halabel
              rw [← hxl, hxw, hwlabel]
            exact ⟨x, ⟨hx.1, by simpa using hxw⟩, hxl⟩
        have hVeq : Vgood = {v, w} := by
          ext u
          constructor
          · intro huV
            by_cases huv : u = v
            · simp [huv]
            · have hulabel := hgood_other_label u huV huv
              let uA : A := ⟨u, huV.1, by simpa using huv⟩
              let wA : A := ⟨w, hwA⟩
              have huAwA : uA = wA := hAinjective (by
                change label u = label w
                exact hulabel.trans hwlabel.symm)
              have huw : u = w := congrArg Subtype.val huAwA
              simp [huw]
          · intro hu
            rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
            rcases hu with rfl | rfl
            · exact hvV
            · exact hwV
        rw [show (if Set.SurjOn label σ Set.univ then 1 else 0) = 0
          by simp [hfull_iff, hvlabel]]
        rw [hfacecard, hVeq]
        have hvw : v ≠ w := Ne.symm hwv
        rw [Set.ncard_pair hvw]
    · have hVempty : Vgood = ∅ := Set.not_nonempty_iff_eq_empty.mp hV
      have hnotfull : ¬ Set.SurjOn label σ Set.univ := by
        intro hfull
        obtain ⟨v, hvσ, hvlabel⟩ := hfull (Set.mem_univ b)
        have hvgood :
            Set.SurjOn label (σ \ {v})
              {a : C | a ≠ b} := by
          intro a hab
          obtain ⟨x, hxσ, hxl⟩ := hfull (Set.mem_univ a)
          have hxv : x ≠ v := by
            intro hxv
            apply hab
            rw [← hxl, hxv, hvlabel]
          exact ⟨x, ⟨hxσ, by simpa using hxv⟩, hxl⟩
        have hvV : v ∈ Vgood :=
          ⟨hvσ, hvgood⟩
        rw [hVempty] at hvV
        exact hvV
      rw [show (if Set.SurjOn label σ Set.univ then 1 else 0) = 0
        by simp [hnotfull]]
      rw [hfacecard, hVempty, Set.ncard_empty]
  have hfull_top (σ : Set (C → ℝ)) (hσ : σ ∈ K.cells)
      (hfull : Set.SurjOn label σ Set.univ) :
      Set.ncard σ = Fintype.card C := by
    have himage : label '' σ = Set.univ := by
      ext a
      simp only [Set.mem_image, Set.mem_univ, iff_true]
      exact hfull (Set.mem_univ a)
    have hlower : Fintype.card C ≤ Set.ncard σ := by
      have hle := Set.ncard_image_le (f := label) (s := σ)
        (K.finite_vertices σ hσ)
      rw [himage] at hle
      simpa using hle
    obtain ⟨ρ, hρ, hσρ, hcardρ⟩ := K.pure σ hσ
    have hupper : Set.ncard σ ≤ Fintype.card C := by
      rw [← hcardρ]
      exact Set.ncard_le_ncard hσρ (K.finite_vertices ρ hρ)
    omega
  let topCells : Finset (Set (C → ℝ)) :=
    K.finite_cells.toFinset.filter
      (fun σ => Set.ncard σ = Fintype.card C)
  let facetCells : Finset (Set (C → ℝ)) :=
    K.finite_cells.toFinset.filter
      (fun τ => Set.ncard τ + 1 = Fintype.card C ∧
        Set.SurjOn label τ {a : C | a ≠ b})
  let rel : Set (C → ℝ) → Set (C → ℝ) → Prop :=
    fun σ τ => τ ⊆ σ
  have hdouble :
      (∑ σ ∈ topCells,
          (facetCells.bipartiteAbove rel σ).card) =
        ∑ τ ∈ facetCells,
          (topCells.bipartiteBelow rel τ).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := topCells) (t := facetCells) (r := rel)
  let fullCells : Set (Set (C → ℝ)) :=
    {σ | σ ∈ K.cells ∧ Set.SurjOn label σ Set.univ}
  have hfullfinite : fullCells.Finite := by
    apply K.finite_cells.subset
    intro σ hσ
    exact hσ.1
  have htop_indicator :
      (∑ σ ∈ topCells,
          if Set.SurjOn label σ Set.univ then 1 else 0) =
        Set.ncard fullCells := by
    calc
      (∑ σ ∈ topCells,
          if Set.SurjOn label σ Set.univ then 1 else 0) =
          (topCells.filter
            (fun σ => Set.SurjOn label σ Set.univ)).card := by
            simp
      _ = hfullfinite.toFinset.card := by
        congr 1
        ext σ
        constructor
        · intro hσ
          simp only [Finset.mem_filter] at hσ
          obtain ⟨hσtop, hσfull⟩ := hσ
          have hσparts :
              σ ∈ K.cells ∧ Set.ncard σ = Fintype.card C := by
            simpa [topCells] using hσtop
          have hσcell : σ ∈ K.cells := hσparts.1
          simpa [fullCells, hσcell, hσfull]
        · intro hσ
          have hσ' : σ ∈ fullCells := by
            simpa using hσ
          obtain ⟨hσcell, hσfull⟩ := hσ'
          simp only [Finset.mem_filter]
          refine ⟨?_, hσfull⟩
          simp [topCells, hσcell,
            hfull_top σ hσcell hσfull]
      _ = Set.ncard fullCells :=
        (Set.ncard_eq_toFinset_card fullCells hfullfinite).symm
  have htopsum :
      (∑ σ ∈ topCells,
          (facetCells.bipartiteAbove rel σ).card) % 2 =
        Set.ncard fullCells % 2 := by
    have hcongr :
        (∑ σ ∈ topCells,
            (facetCells.bipartiteAbove rel σ).card) ≡
          (∑ σ ∈ topCells,
            if Set.SurjOn label σ Set.univ then 1 else 0) [MOD 2] := by
      apply Nat.ModEq.sum
      intro σ hσtop
      have hσparts :
          σ ∈ K.cells ∧ Set.ncard σ = Fintype.card C := by
        simpa [topCells] using hσtop
      let Fσ : Set (Set (C → ℝ)) :=
        {τ | τ ∈ K.cells ∧ τ ⊆ σ ∧
          Set.ncard τ + 1 = Fintype.card C ∧
            Set.SurjOn label τ {a : C | a ≠ b}}
      have hFσfinite : Fσ.Finite := by
        apply K.finite_cells.subset
        intro τ hτ
        exact hτ.1
      have hfiber :
          facetCells.bipartiteAbove rel σ =
            hFσfinite.toFinset := by
        ext τ
        simp [facetCells, rel, Fσ] <;> aesop
      change (facetCells.bipartiteAbove rel σ).card % 2 =
        (if Set.SurjOn label σ Set.univ then 1 else 0) % 2
      rw [hfiber, ← Set.ncard_eq_toFinset_card Fσ hFσfinite]
      rw [show
        (if Set.SurjOn label σ Set.univ then 1 else 0) % 2 =
          if Set.SurjOn label σ Set.univ then 1 else 0 by
            split <;> norm_num]
      simpa [Fσ] using
        top_facet_parity σ hσparts.1 hσparts.2
    rw [← htop_indicator]
    exact hcongr
  let boundaryFacets : Set (Set (C → ℝ)) :=
    {τ | τ ∈ K.cells ∧
      Set.ncard τ + 1 = Fintype.card C ∧
        Set.SurjOn label τ {a : C | a ≠ b} ∧
          ∀ x ∈ τ, x b = 0}
  have hboundaryfinite : boundaryFacets.Finite := by
    apply K.finite_cells.subset
    intro τ hτ
    exact hτ.1
  have hfacet_indicator :
      (∑ τ ∈ facetCells,
          if ∀ x ∈ τ, x b = 0 then 1 else 0) =
        Set.ncard boundaryFacets := by
    calc
      (∑ τ ∈ facetCells,
          if ∀ x ∈ τ, x b = 0 then 1 else 0) =
          (facetCells.filter (fun τ => ∀ x ∈ τ, x b = 0)).card := by
            simp
      _ = hboundaryfinite.toFinset.card := by
        congr 1
        ext τ
        simp [facetCells, boundaryFacets] <;> aesop
      _ = Set.ncard boundaryFacets :=
        (Set.ncard_eq_toFinset_card boundaryFacets
          hboundaryfinite).symm
  have hfacetsum :
      (∑ τ ∈ facetCells,
          (topCells.bipartiteBelow rel τ).card) % 2 =
        Set.ncard boundaryFacets % 2 := by
    have hcongr :
        (∑ τ ∈ facetCells,
            (topCells.bipartiteBelow rel τ).card) ≡
          (∑ τ ∈ facetCells,
            if ∀ x ∈ τ, x b = 0 then 1 else 0) [MOD 2] := by
      apply Nat.ModEq.sum
      intro τ hτfacet
      have hτparts :
          τ ∈ K.cells ∧
            Set.ncard τ + 1 = Fintype.card C ∧
              Set.SurjOn label τ {a : C | a ≠ b} := by
        simpa [facetCells, and_assoc] using hτfacet
      let Gτ : Set (Set (C → ℝ)) :=
        {σ | σ ∈ K.cells ∧ τ ⊆ σ ∧
          Set.ncard σ = Fintype.card C}
      have hGτfinite : Gτ.Finite := by
        apply K.finite_cells.subset
        intro σ hσ
        exact hσ.1
      have hfiber :
          topCells.bipartiteBelow rel τ =
            hGτfinite.toFinset := by
        ext σ
        simp [topCells, rel, Gτ] <;> aesop
      change (topCells.bipartiteBelow rel τ).card % 2 =
        (if ∀ x ∈ τ, x b = 0 then 1 else 0) % 2
      rw [hfiber, ← Set.ncard_eq_toFinset_card Gτ hGτfinite]
      rw [show
        (if ∀ x ∈ τ, x b = 0 then 1 else 0) % 2 =
          if ∀ x ∈ τ, x b = 0 then 1 else 0 by
            split <;> norm_num]
      simpa [Gτ] using facet_coface_parity τ hτparts.1
        hτparts.2.1 hτparts.2.2
    rw [← hfacet_indicator]
    exact hcongr
  change Set.ncard fullCells % 2 =
    Set.ncard boundaryFacets % 2
  rw [← htopsum, ← hfacetsum, hdouble]

@[blueprint "lem:sperner-coordinate-boundary-parity"
  (statement := /-- Let \(C\) be a finite set with at least two elements, let \(K\) be
  a finite triangulation of \(\Delta(C)\), and let \(\ell\) be a Sperner labeling. For
  every \(b\in C\), the number of facets in the coordinate face \(x(b)=0\) whose labels
  are exactly \(C\setminus\{b\}\) is odd. -/)
  (proof := /-- We use strong induction on \(|C|\). Fix \(b\in C\). Since \(|C|>1\),
  the type \(C_b=\{a:C\mid a\neq b\}\) is nonempty. Apply
  \cref{lem:finite-simplex-triangulation-coordinate-face-restriction} to obtain the
  restricted triangulation \(K_b\) of \(\Delta(C_b)\). Let \(\iota(y)\) extend
  \(y\) by a zero \(b\)-coordinate, and fix \(d_0\in C_b\). Define
  \(\ell_b(y)\) to be \(\ell(\iota(y))\), regarded as an element of \(C_b\), when
  this label is not \(b\), and to be \(d_0\) otherwise. If \(y\) is a vertex of
  \(K_b\), then the Sperner condition in \cref{def:sperner-labeling} gives
  \(\iota(y)(\ell(\iota(y)))\neq0\). Since the \(b\)-coordinate of \(\iota(y)\)
  is zero, \(\ell(\iota(y))\neq b\); hence \(\ell_b(y)=\ell(\iota(y))\) on every
  vertex, and \(\ell_b\) is a Sperner labeling of \(K_b\).

  If \(|C_b|=1\), then \(\Delta(C_b)\) is a singleton. The covering and
  nonempty-face axioms force its unique point to be the unique fully labeled cell of
  \(K_b\), so the number of fully labeled cells is one. Suppose now that
  \(|C_b|>1\), and choose \(c\in C_b\). Since \(|C_b|<|C|\), the strong-induction
  hypothesis applied to \(K_b\), \(\ell_b\), and \(c\) says that the number of facets
  of \(K_b\) in the coordinate face \(y(c)=0\), labeled by
  \(C_b\setminus\{c\}\), is odd. Apply
  \cref{lem:sperner-incidence-parity} to \(K_b\), \(\ell_b\), and \(c\). Its
  incidence equality identifies the parity of that boundary-facet count with the
  parity of the fully labeled cells of \(K_b\). The latter count is therefore odd.

  Finally, the injective map \(\iota\) sends a fully labeled cell of \(K_b\) to a
  cell of \(K\) in \(x(b)=0\). Surjectivity of its labels and purity of \(K_b\)
  show that such a cell has \(|C_b|=|C|-1\) vertices. Conversely, restricting the
  coordinates of any cell counted in the statement gives a fully labeled cell of
  \(K_b\); the zero \(b\)-coordinate shows that extending it again recovers the
  original cell. Thus the cell correspondence in
  \cref{lem:finite-simplex-triangulation-coordinate-face-restriction} is a bijection
  between the fully labeled cells of \(K_b\) and the cells counted in the statement.
  Their cardinalities are equal, so the latter cardinality is odd. -/)
  (title := /-- Odd parity on each coordinate boundary face -/)
  (latexEnv := "lemma")]
lemma sperner_coordinate_boundary_parity {C : Type*}
    [Fintype C] [Nonempty C] (K : finite_simplex_triangulation C)
    (label : (C → ℝ) → C) (hlabel : sperner_labeling K label)
    (b : C) (hC : 1 < Fintype.card C) :
    Set.ncard
        {τ : Set (C → ℝ) |
          τ ∈ K.cells ∧
            Set.ncard τ + 1 = Fintype.card C ∧
              Set.SurjOn label τ {a : C | a ≠ b} ∧
                ∀ x ∈ τ, x b = 0} % 2 = 1 := by
  classical
  induction hcard : Fintype.card C using Nat.strong_induction_on generalizing C with
  | h n ih =>
    obtain ⟨d, hd⟩ := Fintype.exists_ne_of_one_lt_card hC b
    letI : Nonempty {a : C // a ≠ b} := ⟨⟨d, hd⟩⟩
    let e : ({a : C // a ≠ b} → ℝ) → (C → ℝ) :=
      fun y a => if ha : a = b then 0 else y ⟨a, ha⟩
    have he : Function.Injective e := by
      intro y z hyz
      funext a
      have ha := congrFun hyz a.1
      simpa [e, a.2] using ha
    obtain ⟨Kb, hKb⟩ :=
      finite_simplex_triangulation_coordinate_face_restriction K b
    let d₀ : {a : C // a ≠ b} := Classical.choice inferInstance
    let labelb : ({a : C // a ≠ b} → ℝ) → {a : C // a ≠ b} :=
      fun y => if hy : label (e y) = b then d₀ else ⟨label (e y), hy⟩
    have hlabelb_eq (y : {a : C // a ≠ b} → ℝ)
        (hy : y ∈ ⋃₀ Kb.cells) : (labelb y).1 = label (e y) := by
      have hey : e y ∈ ⋃₀ K.cells := by
        rcases Set.mem_sUnion.mp hy with ⟨σ, hσ, hyσ⟩
        exact Set.mem_sUnion.mpr ⟨e '' σ, (hKb σ).mp hσ, ⟨y, hyσ, rfl⟩⟩
      have hne : label (e y) ≠ b := by
        intro h
        have hnz := hlabel (e y) hey
        rw [h] at hnz
        exact hnz (by simp [e])
      simp [labelb, hne]
    have hlabelb : sperner_labeling Kb labelb := by
      intro y hy
      have hey : e y ∈ ⋃₀ K.cells := by
        rcases Set.mem_sUnion.mp hy with ⟨σ, hσ, hyσ⟩
        exact Set.mem_sUnion.mpr ⟨e '' σ, (hKb σ).mp hσ, ⟨y, hyσ, rfl⟩⟩
      have hnz := hlabel (e y) hey
      have heq := hlabelb_eq y hy
      rw [← heq] at hnz
      simpa [e, (labelb y).2] using hnz
    let fullb : Set (Set ({a : C // a ≠ b} → ℝ)) :=
      {σ | σ ∈ Kb.cells ∧ Set.SurjOn labelb σ Set.univ}
    let boundary : Set (Set (C → ℝ)) :=
      {τ | τ ∈ K.cells ∧
        Set.ncard τ + 1 = Fintype.card C ∧
          Set.SurjOn label τ {a : C | a ≠ b} ∧ ∀ x ∈ τ, x b = 0}
    have hcardD : Fintype.card {a : C // a ≠ b} + 1 = Fintype.card C := by
      have hc := Fintype.card_subtype_compl (fun a : C => a = b)
      rw [Fintype.card_subtype_eq b] at hc
      change Fintype.card {a : C // ¬a = b} + 1 = Fintype.card C
      rw [hc]
      omega
    have hcorrespond : Set.ncard fullb = Set.ncard boundary := by
      apply Set.ncard_congr (fun σ _ => e '' σ)
      · intro σ hσ
        rcases hσ with ⟨hσcell, hσsurj⟩
        have hlabels : labelb '' σ = Set.univ :=
          Set.Subset.antisymm (Set.subset_univ _) hσsurj
        have hlower : Fintype.card {a : C // a ≠ b} ≤ Set.ncard σ := by
          have hi := Set.ncard_image_le (f := labelb)
            (Kb.finite_vertices σ hσcell)
          simpa [hlabels] using hi
        obtain ⟨ρ, hρ, hσρ, hcardρ⟩ := Kb.pure σ hσcell
        have hupper : Set.ncard σ ≤ Fintype.card {a : C // a ≠ b} := by
          rw [← hcardρ]
          exact Set.ncard_le_ncard hσρ (Kb.finite_vertices ρ hρ)
        have hcardσ : Set.ncard σ = Fintype.card {a : C // a ≠ b} :=
          Nat.le_antisymm hupper hlower
        refine ⟨(hKb σ).mp hσcell, ?_, ?_, ?_⟩
        · rw [Set.ncard_image_of_injective σ he, hcardσ]
          exact hcardD
        · intro a ha
          rcases hσsurj (Set.mem_univ ⟨a, ha⟩) with ⟨y, hy, hya⟩
          refine ⟨e y, ⟨y, hy, rfl⟩, ?_⟩
          have hyall : y ∈ ⋃₀ Kb.cells :=
            Set.mem_sUnion.mpr ⟨σ, hσcell, hy⟩
          calc
            label (e y) = (labelb y).1 := (hlabelb_eq y hyall).symm
            _ = a := congrArg Subtype.val hya
        · intro x hx
          rcases hx with ⟨y, hy, rfl⟩
          simp [e]
      · intro σ τ hσ hτ heq
        exact he.image_injective heq
      · intro τ hτ
        rcases hτ with ⟨hτcell, hτcard, hτsurj, hτzero⟩
        let r : (C → ℝ) → ({a : C // a ≠ b} → ℝ) := fun x a => x a.1
        let σ : Set ({a : C // a ≠ b} → ℝ) := e ⁻¹' τ
        have her (x : C → ℝ) (hx : x b = 0) : e (r x) = x := by
          funext a
          by_cases ha : a = b
          · subst a
            simp [e, hx]
          · simp [e, r, ha]
        have heimage : e '' σ = τ := by
          ext x
          constructor
          · rintro ⟨y, hy, rfl⟩
            exact hy
          · intro hx
            refine ⟨r x, ?_, her x (hτzero x hx)⟩
            change e (r x) ∈ τ
            rw [her x (hτzero x hx)]
            exact hx
        have hσcell : σ ∈ Kb.cells := by
          apply (hKb σ).mpr
          rw [heimage]
          exact hτcell
        have hσsurj : Set.SurjOn labelb σ Set.univ := by
          intro a ha
          rcases hτsurj a.2 with ⟨x, hx, hxa⟩
          have hxzero := hτzero x hx
          have hrx : r x ∈ σ := by
            change e (r x) ∈ τ
            rw [her x hxzero]
            exact hx
          refine ⟨r x, hrx, ?_⟩
          apply Subtype.ext
          have hrall : r x ∈ ⋃₀ Kb.cells :=
            Set.mem_sUnion.mpr ⟨σ, hσcell, hrx⟩
          calc
            (labelb (r x)).1 = label (e (r x)) := hlabelb_eq (r x) hrall
            _ = label x := by rw [her x hxzero]
            _ = a.1 := hxa
        exact ⟨σ, ⟨hσcell, hσsurj⟩, heimage⟩
    have hfull : Set.ncard fullb % 2 = 1 := by
      by_cases hDcard : Fintype.card {a : C // a ≠ b} = 1
      · letI : Subsingleton {a : C // a ≠ b} :=
          Fintype.card_le_one_iff_subsingleton.mp (by omega)
        let p : {a : C // a ≠ b} → ℝ := fun _ => 1
        have hcell_eq (σ : Set ({a : C // a ≠ b} → ℝ))
            (hσ : σ ∈ Kb.cells) : σ = {p} := by
          rcases Kb.nonempty_cells σ hσ with ⟨x, hx⟩
          have hxp : x = p := by
            have hxstd := Kb.vertices_mem_standard_simplex σ hσ x hx
            rw [stdSimplex_unique] at hxstd
            simpa [p] using hxstd
          subst x
          apply Set.eq_singleton_iff_unique_mem.mpr
          refine ⟨hx, ?_⟩
          intro x hxσ
          have hxstd := Kb.vertices_mem_standard_simplex σ hσ x hxσ
          rw [stdSimplex_unique] at hxstd
          simpa [p] using hxstd
        have hpcell : ({p} : Set ({a : C // a ≠ b} → ℝ)) ∈ Kb.cells := by
          have hpstd : p ∈ stdSimplex ℝ {a : C // a ≠ b} := by
            rw [stdSimplex_unique]
            simp [p]
          rw [Kb.cover] at hpstd
          rcases Set.mem_iUnion.mp hpstd with ⟨σ, hpstd⟩
          rcases Set.mem_iUnion.mp hpstd with ⟨hσ, hpstd⟩
          rw [hcell_eq σ hσ] at hσ
          exact hσ
        have hfull_eq : fullb = {{p}} := by
          ext σ
          constructor
          · rintro ⟨hσ, hsurj⟩
            simpa [hcell_eq σ hσ]
          · intro hσ
            have hσeq : σ = {p} := by simpa using hσ
            subst σ
            refine ⟨hpcell, ?_⟩
            intro a ha
            refine ⟨p, Set.mem_singleton p, ?_⟩
            exact Subsingleton.elim _ _
        rw [hfull_eq]
        norm_num
      · have hDgt : 1 < Fintype.card {a : C // a ≠ b} := by
          have hpos : 0 < Fintype.card {a : C // a ≠ b} := Fintype.card_pos
          omega
        let c : {a : C // a ≠ b} := Classical.choice inferInstance
        have hlt : Fintype.card {a : C // a ≠ b} < n := by
          rw [← hcard]
          omega
        have hrec := ih (Fintype.card {a : C // a ≠ b}) hlt Kb labelb
          hlabelb c hDgt rfl
        have hinc := sperner_incidence_parity Kb labelb hlabelb c hDgt
        calc
          Set.ncard fullb % 2 =
              Set.ncard
                {τ : Set ({a : C // a ≠ b} → ℝ) |
                  τ ∈ Kb.cells ∧
                    Set.ncard τ + 1 = Fintype.card {a : C // a ≠ b} ∧
                      Set.SurjOn labelb τ {a | a ≠ c} ∧
                        ∀ x ∈ τ, x c = 0} % 2 := by
                          simpa [fullb] using hinc
          _ = 1 := hrec
    rw [← hcard]
    change Set.ncard boundary % 2 = 1
    rw [← hcorrespond]
    exact hfull

@[blueprint "lem:sperner-parity"
  (statement := /-- Let \(C\) be a nonempty finite set, let \(K\) be a finite
  triangulation of \(\Delta(C)\), and let \(\ell\) be a Sperner labeling of its
  vertices. The number of simplices of \(K\) on which \(\ell\) assumes every value of
  \(C\) is odd. In particular, \(K\) contains a fully labeled simplex. -/)
  (proof := /-- If \(|C|=1\), the covering and nonempty-face axioms in
  \cref{def:finite-simplex-triangulation} force the unique point of \(\Delta(C)\) to be
  a cell of \(K\); its label is the unique element of \(C\), so exactly one cell is
  fully labeled.

  Suppose \(|C|>1\), and choose \(b\in C\). By
  \cref{lem:sperner-incidence-parity}, the number of fully labeled cells has the same
  parity as the number of facets contained in \(x(b)=0\) and labeled by
  \(C\setminus\{b\}\). By \cref{lem:sperner-coordinate-boundary-parity}, the latter
  number is odd. Therefore the number of fully labeled cells is odd, as required. -/)
  (title := /-- Parity form of Sperner's lemma -/)
  (latexEnv := "lemma")]
lemma sperner_parity {C : Type*} [Fintype C] [Nonempty C]
    (K : finite_simplex_triangulation C) (label : (C → ℝ) → C)
    (hlabel : sperner_labeling K label) :
    Set.ncard
        {σ : Set (C → ℝ) |
          σ ∈ K.cells ∧ Set.SurjOn label σ Set.univ} % 2 = 1 := by
  classical
  by_cases hcard : Fintype.card C = 1
  · letI : Subsingleton C :=
      Fintype.card_le_one_iff_subsingleton.mp (by omega)
    let p : C → ℝ := fun _ => 1
    have hcell_eq (σ : Set (C → ℝ)) (hσ : σ ∈ K.cells) : σ = {p} := by
      rcases K.nonempty_cells σ hσ with ⟨x, hx⟩
      have hxp : x = p := by
        have hxstd := K.vertices_mem_standard_simplex σ hσ x hx
        rw [stdSimplex_unique] at hxstd
        simpa [p] using hxstd
      subst x
      apply Set.eq_singleton_iff_unique_mem.mpr
      refine ⟨hx, ?_⟩
      intro x hxσ
      have hxstd := K.vertices_mem_standard_simplex σ hσ x hxσ
      rw [stdSimplex_unique] at hxstd
      simpa [p] using hxstd
    have hpcell : ({p} : Set (C → ℝ)) ∈ K.cells := by
      have hpstd : p ∈ stdSimplex ℝ C := by
        rw [stdSimplex_unique]
        simp [p]
      rw [K.cover] at hpstd
      rcases Set.mem_iUnion.mp hpstd with ⟨σ, hpstd⟩
      rcases Set.mem_iUnion.mp hpstd with ⟨hσ, hpstd⟩
      rw [hcell_eq σ hσ] at hσ
      exact hσ
    have hfull_eq :
        {σ : Set (C → ℝ) |
            σ ∈ K.cells ∧ Set.SurjOn label σ Set.univ} = {{p}} := by
      ext σ
      constructor
      · rintro ⟨hσ, hsurj⟩
        simpa [hcell_eq σ hσ]
      · intro hσ
        have hσeq : σ = {p} := by simpa using hσ
        subst σ
        refine ⟨hpcell, ?_⟩
        intro a ha
        refine ⟨p, Set.mem_singleton p, ?_⟩
        exact Subsingleton.elim _ _
    rw [hfull_eq]
    norm_num
  · have hC : 1 < Fintype.card C := by
      have hpos : 0 < Fintype.card C := Fintype.card_pos
      omega
    let b : C := Classical.choice inferInstance
    calc
      Set.ncard
            {σ : Set (C → ℝ) |
              σ ∈ K.cells ∧ Set.SurjOn label σ Set.univ} % 2 =
          Set.ncard
            {τ : Set (C → ℝ) |
              τ ∈ K.cells ∧
                Set.ncard τ + 1 = Fintype.card C ∧
                  Set.SurjOn label τ {a : C | a ≠ b} ∧
                    ∀ x ∈ τ, x b = 0} % 2 :=
        sperner_incidence_parity K label hlabel b hC
      _ = 1 := sperner_coordinate_boundary_parity K label hlabel b hC

@[blueprint "lem:finite-simplex-approximate-fixed-point"
  (statement := /-- Let \(C\) be a nonempty finite set, let
  \(T:\mathbb R^C\to\mathbb R^C\) be continuous, and suppose that
  \(T(\Delta(C))\subseteq\Delta(C)\). For every \(\varepsilon>0\), there exists
  \(p\in\Delta(C)\) such that \(\|T(p)-p\|_\infty<\varepsilon\). -/)
  (proof := /-- If \(|C|=1\), then \(\Delta(C)\) is a singleton, so the assumption
  \(T(\Delta(C))\subseteq\Delta(C)\) forces its unique point to be fixed. Assume
  henceforth that \(|C|>1\), and put
  \(\eta=\varepsilon/(4|C|)\). Compactness of \(\Delta(C)\) and continuity of \(T\)
  give \(\delta_0>0\) such that points of \(\Delta(C)\) at distance less than
  \(\delta_0\) have images at distance less than \(\eta\). Set
  \(\delta=\min\{\delta_0,\eta\}\). By
  \cref{lem:barycentric-subdivision-mesh}, choose a triangulation \(K\) whose cells
  have diameter less than \(\delta\).

  If a vertex \(x\) of \(K\) satisfies \(T(x)=x\), use it. Otherwise, for each vertex
  \(x\), choose a coordinate \(\ell(x)\) such that
  \(T(x)(\ell(x))<x(\ell(x))\). Such a coordinate exists: if
  \(x(a)\leq T(x)(a)\) for every \(a\), equality of the two coordinate sums forces
  equality in every coordinate, contrary to \(T(x)\neq x\). Since every coordinate
  of \(T(x)\) is nonnegative, \(x(\ell(x))\neq0\); extending \(\ell\) arbitrarily
  away from the vertices therefore gives a Sperner labeling in the sense of
  \cref{def:sperner-labeling}. By \cref{lem:sperner-parity}, there is a cell
  \(\sigma\) having, for each \(a\in C\), a vertex \(v_a\) labeled \(a\).

  Choose a vertex \(p\) of \(\sigma\), and write
  \(d_a=T(p)(a)-p(a)\). The mesh bound gives
  \(\|p-v_a\|_\infty<\delta\), while uniform continuity gives
  \(\|T(p)-T(v_a)\|_\infty<\eta\). Since
  \(T(v_a)(a)<v_a(a)\), the triangle inequality on this coordinate yields
  \(d_a<2\eta\). Both \(p\) and \(T(p)\) have coordinate sum \(1\), so
  \(\sum_a d_a=0\). For each fixed \(a\), it follows that
  \[
    -d_a=\sum_{b\neq a}d_b
      \leq |C|\,2\eta=\frac{\varepsilon}{2}.
  \]
  Thus \(-\varepsilon<d_a<2\eta<\varepsilon\) for every \(a\), whence
  \(\|T(p)-p\|_\infty<\varepsilon\). -/)
  (title := /-- Approximate fixed points on a finite standard simplex -/)
  (latexEnv := "lemma")]
lemma finite_simplex_approximate_fixed_point {C : Type*} [Fintype C] [Nonempty C]
    (T : (C → ℝ) → (C → ℝ)) (hT : Continuous T)
    (hTΔ : Set.MapsTo T (stdSimplex ℝ C) (stdSimplex ℝ C))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p ∈ stdSimplex ℝ C, dist (T p) p < ε := by
  classical
  by_cases hcard : Fintype.card C = 1
  · letI : Subsingleton C :=
      Fintype.card_le_one_iff_subsingleton.mp (by omega)
    let p : C → ℝ := fun _ => 1
    have hp : p ∈ stdSimplex ℝ C := by
      rw [stdSimplex_unique]
      simp [p]
    have hTp := hTΔ hp
    have hfix : T p = p := by
      rw [stdSimplex_unique] at hTp
      simpa [p] using hTp
    exact ⟨p, hp, by simpa [hfix] using hε⟩
  have hcard_gt : 1 < Fintype.card C := by
    have hcard_pos : 0 < Fintype.card C := Fintype.card_pos
    omega
  let η : ℝ := ε / (4 * (Fintype.card C : ℝ))
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have huc : UniformContinuousOn T (stdSimplex ℝ C) :=
    (isCompact_stdSimplex (𝕜 := ℝ) (ι := C)).uniformContinuousOn_of_continuous
      hT.continuousOn
  rcases (Metric.uniformContinuousOn_iff.mp huc) η hη with
    ⟨δ₀, hδ₀, hcontrol⟩
  let δ : ℝ := min δ₀ η
  have hδ : 0 < δ := by
    exact lt_min hδ₀ hη
  rcases barycentric_subdivision_mesh (C := C) δ hδ with ⟨K, hmesh⟩
  by_cases hfixed : ∃ x ∈ ⋃₀ K.cells, T x = x
  · rcases hfixed with ⟨x, hx, hTx⟩
    rcases hx with ⟨σ, hσ, hxσ⟩
    have hxΔ : x ∈ stdSimplex ℝ C :=
      K.vertices_mem_standard_simplex σ hσ x hxσ
    exact ⟨x, hxΔ, by simpa [hTx] using hε⟩
  push Not at hfixed
  have exists_decreasing (x : C → ℝ) (hxΔ : x ∈ stdSimplex ℝ C)
      (hne : T x ≠ x) : ∃ a : C, T x a < x a := by
    have hTxΔ := hTΔ hxΔ
    by_contra h
    push Not at h
    have hsum : (∑ a, x a) = ∑ a, T x a := by
      calc
        (∑ a, x a) = 1 := hxΔ.2
        _ = ∑ a, T x a := hTxΔ.2.symm
    have hcoord : ∀ a ∈ (Finset.univ : Finset C), x a = T x a :=
      (Finset.sum_eq_sum_iff_of_le
        (s := Finset.univ) (f := x) (g := T x)
        (by
          intro a ha
          exact h a)).mp hsum
    apply hne
    funext a
    exact (hcoord a (Finset.mem_univ a)).symm
  let label : (C → ℝ) → C := fun x =>
    if h : ∃ a : C, T x a < x a then Classical.choose h
    else Classical.choice inferInstance
  have label_decreases (x : C → ℝ) (hx : ∃ a : C, T x a < x a) :
      T x (label x) < x (label x) := by
    simpa [label, hx] using Classical.choose_spec hx
  have hlabel : sperner_labeling K label := by
    rw [sperner_labeling]
    intro x hx
    rcases hx with ⟨σ, hσ, hxσ⟩
    have hxΔ : x ∈ stdSimplex ℝ C :=
      K.vertices_mem_standard_simplex σ hσ x hxσ
    have hdec := exists_decreasing x hxΔ (hfixed x ⟨σ, hσ, hxσ⟩)
    have hlt := label_decreases x hdec
    have hnonneg := (hTΔ hxΔ).1 (label x)
    linarith
  have hparity := sperner_parity K label hlabel
  have hfull_finite :
      {σ : Set (C → ℝ) |
        σ ∈ K.cells ∧ Set.SurjOn label σ Set.univ}.Finite :=
    K.finite_cells.subset (by
      intro σ hσ
      exact hσ.1)
  have hfull_pos :
      0 < Set.ncard
        {σ : Set (C → ℝ) |
          σ ∈ K.cells ∧ Set.SurjOn label σ Set.univ} := by
    omega
  have hfull_nonempty :
      {σ : Set (C → ℝ) |
        σ ∈ K.cells ∧ Set.SurjOn label σ Set.univ}.Nonempty :=
    (Set.ncard_pos hfull_finite).mp hfull_pos
  rcases hfull_nonempty with ⟨σ, hσ, hsurj⟩
  rcases K.nonempty_cells σ hσ with ⟨p, hpσ⟩
  have hpΔ : p ∈ stdSimplex ℝ C :=
    K.vertices_mem_standard_simplex σ hσ p hpσ
  have hupper (a : C) : T p a - p a < 2 * η := by
    rcases hsurj (a := a) (Set.mem_univ a) with ⟨v, hvσ, hvlabel⟩
    have hvΔ : v ∈ stdSimplex ℝ C :=
      K.vertices_mem_standard_simplex σ hσ v hvσ
    have hvdec := exists_decreasing v hvΔ (hfixed v ⟨σ, hσ, hvσ⟩)
    have hvlt : T v a < v a := by
      simpa [hvlabel] using label_decreases v hvdec
    have hpv : dist p v < δ :=
      lt_of_le_of_lt
        (Metric.dist_le_diam_of_mem
          (K.finite_vertices σ hσ).isBounded hpσ hvσ)
        (hmesh σ hσ)
    have hpvδ₀ : dist p v < δ₀ :=
      lt_of_lt_of_le hpv (min_le_left δ₀ η)
    have hpvη : dist p v < η :=
      lt_of_lt_of_le hpv (min_le_right δ₀ η)
    have hTpv : dist (T p) (T v) < η :=
      hcontrol p hpΔ v hvΔ hpvδ₀
    have hTcoord : dist (T p a) (T v a) < η :=
      (dist_pi_lt_iff hη).mp hTpv a
    have hpcoord : dist (p a) (v a) < η :=
      (dist_pi_lt_iff hη).mp hpvη a
    rw [Real.dist_eq] at hTcoord hpcoord
    rw [abs_lt] at hTcoord hpcoord
    linarith
  have hsum : ∑ a, (T p a - p a) = 0 := by
    calc
      ∑ a, (T p a - p a) = (∑ a, T p a) - ∑ a, p a :=
        by
          simpa using
            (Finset.sum_sub_distrib (s := Finset.univ)
              (fun a => T p a) (fun a => p a))
      _ = 0 := by rw [(hTΔ hpΔ).2, hpΔ.2]; ring
  have hη_card : (Fintype.card C : ℝ) * (2 * η) = ε / 2 := by
    have hcard_ne : (Fintype.card C : ℝ) ≠ 0 := by positivity
    dsimp [η]
    field_simp [hcard_ne] <;> ring
  have hη_lt : 2 * η < ε := by
    have hone : (1 : ℝ) ≤ Fintype.card C := by
      exact_mod_cast (show 1 ≤ Fintype.card C by omega)
    calc
      2 * η = 1 * (2 * η) := by ring
      _ ≤ (Fintype.card C : ℝ) * (2 * η) :=
        mul_le_mul_of_nonneg_right hone (by positivity)
      _ = ε / 2 := hη_card
      _ < ε := by linarith
  have herase_bound (a : C) :
      ∑ b ∈ Finset.univ.erase a, (T p b - p b) ≤ ε / 2 := by
    calc
      ∑ b ∈ Finset.univ.erase a, (T p b - p b) ≤
          ∑ _b ∈ Finset.univ.erase a, (2 * η) := by
            apply Finset.sum_le_sum
            intro b hb
            exact (hupper b).le
      _ = ((Finset.univ.erase a).card : ℝ) * (2 * η) := by simp
      _ ≤ (Fintype.card C : ℝ) * (2 * η) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast Finset.card_le_card (Finset.erase_subset a Finset.univ)
        · positivity
      _ = ε / 2 := hη_card
  have hsum_erase (a : C) :
      (∑ b ∈ Finset.univ.erase a, (T p b - p b)) + (T p a - p a) = 0 := by
    calc
      (∑ b ∈ Finset.univ.erase a, (T p b - p b)) + (T p a - p a) =
          ∑ b ∈ Finset.univ, (T p b - p b) :=
        Finset.sum_erase_add Finset.univ (fun b => T p b - p b)
          (Finset.mem_univ a)
      _ = 0 := hsum
  refine ⟨p, hpΔ, (dist_pi_lt_iff hε).2 ?_⟩
  intro a
  rw [Real.dist_eq, abs_lt]
  constructor
  · have hb := herase_bound a
    have hs := hsum_erase a
    linarith
  · exact (hupper a).trans hη_lt

@[blueprint "lem:finite-simplex-brouwer"
  (statement := /-- Let \(C\) be a nonempty finite set, and write
  \[
    \Delta(C)=\left\{p\in\mathbb R^C:p(a)\geq0\ \text{for every }a\in C,\quad
      \sum_{a\in C}p(a)=1\right\}.
  If \(T:\mathbb R^C\to\mathbb R^C\) is continuous and
  \(T(\Delta(C))\subseteq\Delta(C)\), then there exists \(p\in\Delta(C)\) such that
  \(T(p)=p\). -/)
  (proof := /-- Define \(f(p)=\operatorname{dist}(T(p),p)\). Since \(T\) is continuous,
  so is \(f\). The finite-dimensional standard simplex is nonempty and compact, hence
  \(f\) attains its minimum there at some \(p\in\Delta(C)\). If \(f(p)>0\), then
  \cref{lem:finite-simplex-approximate-fixed-point}, applied with
  \(\varepsilon=f(p)\), gives \(q\in\Delta(C)\) such that \(f(q)<f(p)\), contradicting
  minimality. Thus \(f(p)=0\), and therefore \(T(p)=p\). -/)
  (title := /-- Brouwer's fixed-point theorem on a finite standard simplex -/)
  (latexEnv := "lemma")]
lemma finite_simplex_brouwer {C : Type*} [Fintype C] [Nonempty C]
    (T : (C → ℝ) → (C → ℝ)) (hT : Continuous T)
    (hTΔ : Set.MapsTo T (stdSimplex ℝ C) (stdSimplex ℝ C)) :
    ∃ p ∈ stdSimplex ℝ C, T p = p := by
  classical
  let f : (C → ℝ) → ℝ := fun p => dist (T p) p
  have hf : Continuous f := hT.dist continuous_id
  have hΔne : (stdSimplex ℝ C).Nonempty := by
    let p : stdSimplex ℝ C := Classical.arbitrary _
    exact ⟨p, p.property⟩
  rcases (isCompact_stdSimplex (𝕜 := ℝ) (ι := C)).exists_isMinOn hΔne hf.continuousOn with
    ⟨p, hp, hpmin⟩
  refine ⟨p, hp, ?_⟩
  apply dist_eq_zero.mp
  by_contra hne
  have hpos : 0 < dist (T p) p := lt_of_le_of_ne dist_nonneg (Ne.symm hne)
  rcases finite_simplex_approximate_fixed_point T hT hTΔ _ hpos with ⟨q, hq, hq_lt⟩
  have hpq : dist (T p) p ≤ dist (T q) q := hpmin hq
  exact (not_lt_of_ge hpq) hq_lt

@[blueprint "lem:finite-simplex-response-fixed-point"
  (statement := /-- Let \(C\) be a nonempty finite set, let \(k\in\mathbb N\), and let
  \(r:C^k\to C\). There is a probability vector \(p\) on \(C\) which is stationary for the
  polynomial response map induced by \(r\): for every \(a\in C\),
  \[
    p(a)=\sum_{\mathbf b\in C^k:\,r(\mathbf b)=a}
      \prod_{i=1}^k p(b_i).
  \] -/)
  (proof := /-- Let
  \[
    \Delta(C)=\left\{p\in\mathbb R^C:p(a)\geq0\ \text{for every }a\in C,\quad
      \sum_{a\in C}p(a)=1\right\}.
  \]
  Since \(C\) is nonempty and finite, \(\Delta(C)\) is a nonempty compact convex subset of
  the finite-dimensional real vector space \(\mathbb R^C\). Define \(T:\Delta(C)\to
  \mathbb R^C\) by
  \[
    T(p)(a)=\sum_{\mathbf b\in C^k:\,r(\mathbf b)=a}
      \prod_{i=1}^k p(b_i).
  \]
  Every coordinate of \(T\) is a finite polynomial in the coordinates of \(p\), hence
  \(T\) is continuous. Its coordinates are nonnegative. Moreover, summing first over
  \(a\) and then over \(\mathbf b\) gives
  \[
    \sum_{a\in C}T(p)(a)
      =\sum_{\mathbf b\in C^k}\prod_{i=1}^k p(b_i)
      =\left(\sum_{a\in C}p(a)\right)^k=1.
  \]
  Thus \(T\) is a continuous self-map of \(\Delta(C)\). Applying
  \cref{lem:finite-simplex-brouwer} supplies \(p\in\Delta(C)\) with \(T(p)=p\). Expanding
  this equality coordinatewise gives all the asserted properties. -/)
  (title := /-- Stationary distribution for a finite polynomial response map -/)
  (latexEnv := "lemma")]
lemma finite_simplex_response_fixed_point {C : Type*} [Fintype C] [DecidableEq C]
    [Nonempty C] (k : ℕ) (r : (Fin k → C) → C) :
    ∃ p : C → ℝ,
      (∀ a : C, 0 ≤ p a) ∧
        (∑ a : C, p a) = 1 ∧
          ∀ a : C,
            p a =
              ∑ b : Fin k → C, if r b = a then ∏ i : Fin k, p (b i) else 0 := by
  let T : (C → ℝ) → (C → ℝ) := fun p a =>
    ∑ b : Fin k → C, if r b = a then ∏ i : Fin k, p (b i) else 0
  have hT : Continuous T := by
    apply continuous_pi
    intro a
    apply continuous_finsetSum
    intro b hb
    by_cases hba : r b = a
    · simp only [hba, if_true]
      apply continuous_finsetProd
      intro i hi
      exact continuous_apply (b i)
    · simpa [hba] using
        (continuous_const : Continuous (fun _ : C → ℝ => (0 : ℝ)))
  have hTΔ : Set.MapsTo T (stdSimplex ℝ C) (stdSimplex ℝ C) := by
    intro p hp
    constructor
    · intro a
      apply Finset.sum_nonneg
      intro b hb
      by_cases hba : r b = a
      · simp only [hba, if_true]
        exact Finset.prod_nonneg fun i hi => hp.1 (b i)
      · simp [hba]
    · calc
        ∑ a : C, T p a =
            ∑ b : Fin k → C, ∑ a : C,
              if r b = a then ∏ i : Fin k, p (b i) else 0 := by
                simp only [T]
                rw [Finset.sum_comm]
        _ = ∑ b : Fin k → C, ∏ i : Fin k, p (b i) := by
          apply Finset.sum_congr rfl
          intro b hb
          simp
        _ = ∏ i : Fin k, ∑ a : C, p a :=
          (Fintype.prod_sum (fun (_ : Fin k) (a : C) => p a)).symm
        _ = 1 := by simp [hp.2]
  rcases finite_simplex_brouwer T hT hTΔ with ⟨p, hp, hfixed⟩
  refine ⟨p, hp.1, hp.2, ?_⟩
  intro a
  simpa only [T] using (congrFun hfixed a).symm

@[blueprint "lem:strict-quantile-finite-rank"
  (statement := /-- Let \(C\) be finite and let \(\succ\) be a strict total order on \(C\).
  There is a natural-valued rank bounded by \(|C|\) such that \(a\succ b\) implies that
  the rank of \(b\) is strictly smaller than the rank of \(a\). -/)
  (proof := /-- Reverse the given strict total order and use the induced linear order on
  \(C\).  The increasing order isomorphism from \(\operatorname{Fin}(|C|)\) to \(C\)
  then supplies the required rank through its inverse. -/)
  (title := /-- Natural ranks for a finite strict preference order -/)
  (latexEnv := "lemma")]
lemma strict_quantile_finite_rank {C : Type*} [Fintype C]
    (pref : C → C → Prop) (hpref : IsStrictTotalOrder C pref) :
    ∃ ρ : C → ℕ,
      (∀ a : C, ρ a < Fintype.card C) ∧
        ∀ a b : C, pref a b → ρ b < ρ a := by
  classical
  letI : IsStrictTotalOrder C (fun a b => pref b a) := hpref.swap
  letI : LinearOrder C := linearOrderOfSTO (fun a b => pref b a)
  let e : Fin (Fintype.card C) ≃o C :=
    (Finset.orderIsoOfFin Finset.univ Finset.card_univ).trans
      ((OrderIso.setCongr (↑(Finset.univ : Finset C) : Set C) Set.univ (by simp)).trans
        OrderIso.Set.univ)
  refine ⟨fun a => (e.symm a).val, fun a => (e.symm a).isLt, ?_⟩
  intro a b hab
  exact e.symm.lt_iff_lt.mpr hab

@[blueprint "lem:strict-quantile-fractional-rank-cut"
  (statement := /-- Let \(p\) be a probability vector on a finite set \(C\), and let
  \(\rho:C\to\mathbb N\) take values below \(|C|\).  For every \(t\in[0,1]\) there is a
  function \(q:C\to[0,1]\) of \(p\)-mean \(t\) such that, whenever
  \(\rho(b)<\rho(a)\) and \(q(a)>0\), one has \(q(b)=1\). -/)
  (proof := /-- For a real parameter \(s\), put
  \(q_s(a)=\max\{0,\min\{1,s-\rho(a)\}\}\).  Its \(p\)-mean is continuous in \(s\),
  equals \(0\) at \(s=0\), and equals \(1\) at \(s=|C|\).  The intermediate value
  theorem gives a parameter with mean \(t\).  Consecutive natural ranks differ by at
  least one, which gives the asserted saturation property. -/)
  (title := /-- A fractional cut of prescribed probability mass -/)
  (latexEnv := "lemma")]
lemma strict_quantile_fractional_rank_cut {C : Type*} [Fintype C]
    (p : C → ℝ) (hpnonneg : ∀ a : C, 0 ≤ p a) (hpsum : (∑ a : C, p a) = 1)
    (ρ : C → ℕ) (hρ : ∀ a : C, ρ a < Fintype.card C)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ q : C → ℝ,
      (∀ a : C, 0 ≤ q a ∧ q a ≤ 1) ∧
        (∑ a : C, p a * q a) = t ∧
          ∀ a b : C, ρ b < ρ a → 0 < q a → q b = 1 := by
  classical
  let qcut : ℝ → C → ℝ :=
    fun s a => max 0 (min 1 (s - (ρ a : ℝ)))
  let mass : ℝ → ℝ := fun s => ∑ a : C, p a * qcut s a
  have hmass_cont : Continuous mass := by
    dsimp [mass, qcut]
    fun_prop
  have hmass_zero : mass 0 = 0 := by
    simp only [mass, qcut]
    apply Finset.sum_eq_zero
    intro a ha
    have hcast : 0 ≤ (ρ a : ℝ) := by positivity
    rw [max_eq_left]
    · ring
    · exact min_le_of_right_le (sub_nonpos.mpr hcast)
  have hmass_card : mass (Fintype.card C : ℝ) = 1 := by
    rw [show mass (Fintype.card C : ℝ) = ∑ a : C, p a by
      apply Finset.sum_congr rfl
      intro a ha
      have hstep : (1 : ℝ) ≤ (Fintype.card C : ℝ) - (ρ a : ℝ) := by
        have hn : ρ a + 1 ≤ Fintype.card C := Nat.succ_le_iff.mpr (hρ a)
        have hn' : ((ρ a + 1 : ℕ) : ℝ) ≤ (Fintype.card C : ℝ) :=
          Nat.cast_le.mpr hn
        norm_num at hn'
        linarith
      simp [mass, qcut, min_eq_left hstep]]
    exact hpsum
  have htmem : t ∈ Set.Icc (mass 0) (mass (Fintype.card C : ℝ)) := by
    simpa [hmass_zero, hmass_card] using And.intro ht0 ht1
  rcases intermediate_value_Icc (show (0 : ℝ) ≤ Fintype.card C by positivity)
      hmass_cont.continuousOn htmem with ⟨s, hs, hst⟩
  refine ⟨qcut s, ?_, ?_, ?_⟩
  · intro a
    constructor
    · exact le_max_left _ _
    · exact max_le zero_le_one (min_le_left _ _)
  · simpa [mass] using hst
  · intro a b hba hqa
    have hsa : (ρ a : ℝ) < s := by
      by_contra h
      have hle : s - (ρ a : ℝ) ≤ 0 := sub_nonpos.mpr (le_of_not_gt h)
      have hmin : min 1 (s - (ρ a : ℝ)) ≤ 0 :=
        le_trans (min_le_right _ _) hle
      have : qcut s a = 0 := by
        simp [qcut, max_eq_left hmin]
      linarith
    have hrank : (ρ b : ℝ) + 1 ≤ (ρ a : ℝ) := by
      exact_mod_cast hba
    have hone : (1 : ℝ) ≤ s - (ρ b : ℝ) := by
      linarith
    simp [qcut, min_eq_left hone]

@[blueprint "lem:strict-quantile-response-bound"
  (statement := /-- Under the response and stationarity hypotheses of the strict quantile
  argument, for every \(t\in[0,1]\) one has
  \[
    \alpha\leq 1-t+t^k.
  \] -/)
  (proof := /-- For each voter, use \cref{lem:strict-quantile-finite-rank} to rank the
  candidates and \cref{lem:strict-quantile-fractional-rank-cut} to choose a fractional
  lower set \(q\) of \(p\)-mass \(t\).  If the response to a tuple is preferred to every
  entry, then either the response lies above the cut, contributing at most \(1-t\), or
  every entry lies below it, contributing \(t^k\).  Multiply this pointwise alternative
  by the product weights and sum.  Stationarity makes the response contribution equal
  to \(1-t\), independence gives \(t^k\), and averaging the response hypothesis over
  voters yields the displayed bound. -/)
  (title := /-- Polynomial cut bound for a stationary response -/)
  (latexEnv := "lemma")]
lemma strict_quantile_response_bound {V C : Type*} [Fintype V] [Fintype C]
    [DecidableEq C] (E : election V C) (α : ℝ) (k : ℕ) (hαpos : 0 < α)
    (r : (Fin k → C) → C)
    (hr :
      ∀ b : Fin k → C,
        α ≤ voter_fraction E (r b) (Finset.univ.image b))
    (p : C → ℝ) (hpnonneg : ∀ a : C, 0 ≤ p a) (hpsum : (∑ a : C, p a) = 1)
    (hstationary :
      ∀ a : C,
        p a =
          ∑ b : Fin k → C, if r b = a then ∏ i : Fin k, p (b i) else 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, α ≤ 1 - t + t ^ k := by
  classical
  haveI : Nonempty C := by
    by_contra h
    haveI : IsEmpty C := not_nonempty_iff.mp h
    simpa using hpsum
  haveI : Nonempty V := by
    by_contra h
    haveI : IsEmpty V := not_nonempty_iff.mp h
    have h := hr (fun _ => Classical.choice inferInstance)
    simp [voter_fraction] at h
    linarith
  intro t ht
  choose ρ hρ hρpref using
    fun v => strict_quantile_finite_rank (E.prefers v) (E.preference_is_strict_total v)
  choose q hqbound hqmass hqsaturated using
    fun v => strict_quantile_fractional_rank_cut p hpnonneg hpsum (ρ v) (hρ v)
      t ht.1 ht.2
  let w : (Fin k → C) → ℝ := fun b => ∏ i : Fin k, p (b i)
  have hw : ∀ b : Fin k → C, 0 ≤ w b := by
    intro b
    exact Finset.prod_nonneg fun i hi => hpnonneg (b i)
  have hwsum : (∑ b : Fin k → C, w b) = 1 := by
    simpa [w, hpsum] using (Fintype.sum_pow p k).symm
  have hevent (v : V) (b : Fin k → C) :
      (if prefers_over_committee E v (r b) (Finset.univ.image b) then (1 : ℝ) else 0) ≤
        (1 - q v (r b)) + ∏ i : Fin k, q v (b i) := by
    by_cases hgood : prefers_over_committee E v (r b) (Finset.univ.image b)
    · rw [if_pos hgood]
      by_cases hqpos : 0 < q v (r b)
      · have hall : ∀ i : Fin k, q v (b i) = 1 := by
          intro i
          apply hqsaturated v (r b) (b i)
          · apply hρpref v
            exact hgood (b i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
          · exact hqpos
        simp [hall]
        exact hqbound v (r b) |>.2
      · have hqzero : q v (r b) = 0 :=
          le_antisymm (le_of_not_gt hqpos) (hqbound v (r b)).1
        rw [hqzero]
        have hprod : 0 ≤ ∏ i : Fin k, q v (b i) :=
          Finset.prod_nonneg fun i hi => (hqbound v (b i)).1
        linarith
    · rw [if_neg hgood]
      have hprod : 0 ≤ ∏ i : Fin k, q v (b i) :=
        Finset.prod_nonneg fun i hi => (hqbound v (b i)).1
      linarith [(hqbound v (r b)).2]
  have hpush (v : V) :
      (∑ b : Fin k → C, w b * q v (r b)) = t := by
    calc
      (∑ b : Fin k → C, w b * q v (r b)) =
          ∑ a : C, (∑ b : Fin k → C, if r b = a then w b else 0) * q v a := by
            symm
            simp_rw [Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro b hb
            simp [eq_comm]
      _ = ∑ a : C, p a * q v a := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [← hstationary a]
      _ = t := hqmass v
  have hproduct (v : V) :
      (∑ b : Fin k → C, w b * ∏ i : Fin k, q v (b i)) = t ^ k := by
    calc
      (∑ b : Fin k → C, w b * ∏ i : Fin k, q v (b i)) =
          ∑ b : Fin k → C, ∏ i : Fin k, (p (b i) * q v (b i)) := by
            apply Finset.sum_congr rfl
            intro b hb
            simp [w, Finset.prod_mul_distrib]
      _ = (∑ a : C, p a * q v a) ^ k := (Fintype.sum_pow (fun a => p a * q v a) k).symm
      _ = t ^ k := by rw [hqmass v]
  have hper_voter (v : V) :
      (∑ b : Fin k → C,
          w b *
            (if prefers_over_committee E v (r b) (Finset.univ.image b)
              then (1 : ℝ) else 0)) ≤
        1 - t + t ^ k := by
    calc
      _ ≤ ∑ b : Fin k → C,
          w b * ((1 - q v (r b)) + ∏ i : Fin k, q v (b i)) := by
            apply Finset.sum_le_sum
            intro b hb
            exact mul_le_mul_of_nonneg_left (hevent v b) (hw b)
      _ = (∑ b : Fin k → C, w b * (1 - q v (r b))) +
          ∑ b : Fin k → C, w b * ∏ i : Fin k, q v (b i) := by
            simp_rw [mul_add]
            exact Finset.sum_add_distrib
      _ = 1 - t + t ^ k := by
            rw [hproduct v]
            simp_rw [mul_sub, mul_one]
            rw [Finset.sum_sub_distrib, hwsum, hpush v]
  have hlower :
      α ≤ ∑ b : Fin k → C,
        w b * voter_fraction E (r b) (Finset.univ.image b) := by
    calc
      α = ∑ b : Fin k → C, w b * α := by
        rw [← Finset.sum_mul, hwsum, one_mul]
      _ ≤ ∑ b : Fin k → C,
          w b * voter_fraction E (r b) (Finset.univ.image b) := by
        apply Finset.sum_le_sum
        intro b hb
        exact mul_le_mul_of_nonneg_left (hr b) (hw b)
  have hcard (b : Fin k → C) :
      (((Finset.univ.filter
          (fun v => prefers_over_committee E v (r b) (Finset.univ.image b))).card : ℕ) : ℝ) =
        ∑ v : V,
          if prefers_over_committee E v (r b) (Finset.univ.image b) then (1 : ℝ) else 0 := by
    simp
  have hvf :
      (∑ b : Fin k → C,
          w b * voter_fraction E (r b) (Finset.univ.image b)) =
        (∑ v : V, ∑ b : Fin k → C,
            w b *
              (if prefers_over_committee E v (r b) (Finset.univ.image b)
                then (1 : ℝ) else 0)) / (Fintype.card V : ℝ) := by
    simp_rw [voter_fraction, hcard]
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
    congr 1
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  have hcardV : (0 : ℝ) < Fintype.card V := by positivity
  calc
    α ≤ ∑ b : Fin k → C,
        w b * voter_fraction E (r b) (Finset.univ.image b) := hlower
    _ = (∑ v : V, ∑ b : Fin k → C,
          w b *
            (if prefers_over_committee E v (r b) (Finset.univ.image b)
              then (1 : ℝ) else 0)) / (Fintype.card V : ℝ) := hvf
    _ ≤ (∑ v : V, (1 - t + t ^ k)) / (Fintype.card V : ℝ) := by
      exact (div_le_div_iff_of_pos_right hcardV).2 (Finset.sum_le_sum fun v hv => hper_voter v)
    _ = 1 - t + t ^ k := by
      rw [div_eq_iff (ne_of_gt hcardV)]
      simp [nsmul_eq_mul]
      ring

@[blueprint "lem:strict-quantile-threshold-below-one"
  (statement := /-- Under the stationary response hypotheses, if
  \(0<\alpha\leq1\) and \(k\geq1\), then in fact \(\alpha<1\). -/)
  (proof := /-- The bounds from \cref{lem:strict-quantile-response-bound}, evaluated at
  \(t=1/2\), give \(\alpha<1\) when \(k\geq2\).  When \(k=1\), suppose
  \(\alpha=1\).  Fix a voter and use \cref{lem:strict-quantile-finite-rank}.
  Every response to a positive-weight input must then be unanimously preferred to that
  input, hence must have strictly larger rank.  Summing these strict inequalities gives
  a strict increase of expected rank, whereas stationarity identifies the input and
  response rank expectations.  This contradiction proves the claim. -/)
  (title := /-- A stationary strict response has threshold below one -/)
  (latexEnv := "lemma")]
lemma strict_quantile_threshold_below_one {V C : Type*} [Fintype V] [Fintype C]
    [DecidableEq C] (E : election V C) (α : ℝ) (k : ℕ)
    (hαpos : 0 < α) (hαone : α ≤ 1) (hk : 0 < k)
    (r : (Fin k → C) → C)
    (hr :
      ∀ b : Fin k → C,
        α ≤ voter_fraction E (r b) (Finset.univ.image b))
    (p : C → ℝ) (hpnonneg : ∀ a : C, 0 ≤ p a) (hpsum : (∑ a : C, p a) = 1)
    (hstationary :
      ∀ a : C,
        p a =
          ∑ b : Fin k → C, if r b = a then ∏ i : Fin k, p (b i) else 0) :
    α < 1 := by
  classical
  haveI : Nonempty C := by
    by_contra h
    haveI : IsEmpty C := not_nonempty_iff.mp h
    simpa using hpsum
  haveI : Nonempty V := by
    by_contra h
    haveI : IsEmpty V := not_nonempty_iff.mp h
    have h := hr (fun _ => Classical.choice inferInstance)
    simp [voter_fraction] at h
    linarith
  have hcut := strict_quantile_response_bound E α k hαpos r hr p hpnonneg hpsum hstationary
  rcases k with _ | k
  · omega
  rcases k with _ | k
  · by_contra hαnot
    have hαeq : α = 1 := le_antisymm hαone (le_of_not_gt hαnot)
    let v : V := Classical.choice inferInstance
    rcases strict_quantile_finite_rank (E.prefers v) (E.preference_is_strict_total v) with
      ⟨ρ, hρ, hρpref⟩
    have hcardV : (0 : ℝ) < Fintype.card V := by positivity
    have hallgood (b : Fin 1 → C) (v' : V) :
        prefers_over_committee E v' (r b) (Finset.univ.image b) := by
      have hb := hr b
      rw [hαeq] at hb
      have hcard_real :
          (Fintype.card V : ℝ) ≤
            ((Finset.univ.filter
              (fun v' => prefers_over_committee E v' (r b) (Finset.univ.image b))).card : ℝ) := by
        have hb' : (1 : ℝ) ≤
            ((Finset.univ.filter
              (fun v' => prefers_over_committee E v' (r b) (Finset.univ.image b))).card : ℝ) /
              (Fintype.card V : ℝ) := by
          simpa [voter_fraction] using hb
        have hmul := (le_div_iff₀ hcardV).mp hb'
        simpa using hmul
      have hcard_nat :
          Fintype.card V ≤
            (Finset.univ.filter
              (fun v' => prefers_over_committee E v' (r b) (Finset.univ.image b))).card := by
        exact_mod_cast hcard_real
      have hcard_eq :
          (Finset.univ.filter
              (fun v' => prefers_over_committee E v' (r b) (Finset.univ.image b))).card =
            Fintype.card V :=
        Nat.le_antisymm (Finset.card_le_univ _) hcard_nat
      have hfilter :
          Finset.univ.filter
              (fun v' => prefers_over_committee E v' (r b) (Finset.univ.image b)) =
            Finset.univ :=
        Finset.eq_univ_of_card _ hcard_eq
      have hv' :
          v' ∈ Finset.univ.filter
            (fun v' => prefers_over_committee E v' (r b) (Finset.univ.image b)) := by
        rw [hfilter]
        exact Finset.mem_univ v'
      exact (Finset.mem_filter.mp hv').2
    have hresp_expect :
        (∑ b : Fin 1 → C, p (b 0) * (ρ (r b) : ℝ)) =
          ∑ a : C, p a * (ρ a : ℝ) := by
      calc
        (∑ b : Fin 1 → C, p (b 0) * (ρ (r b) : ℝ)) =
            ∑ a : C,
              (∑ b : Fin 1 → C, if r b = a then p (b 0) else 0) * (ρ a : ℝ) := by
                symm
                simp_rw [Finset.sum_mul]
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro b hb
                simp [eq_comm]
        _ = ∑ a : C, p a * (ρ a : ℝ) := by
              apply Finset.sum_congr rfl
              intro a ha
              have hs := hstationary a
              change p a = ∑ b : Fin 1 → C, if r b = a then ∏ i : Fin 1, p (b i) else 0 at hs
              have hs' : p a = ∑ b : Fin 1 → C, if r b = a then p (b 0) else 0 := by
                simpa only [Fin.prod_univ_one] using hs
              rw [← hs']
    have hinput_expect :
        (∑ b : Fin 1 → C, p (b 0) * (ρ (b 0) : ℝ)) =
          ∑ a : C, p a * (ρ a : ℝ) := by
      refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) C)
        (fun b : Fin 1 → C => p (b 0) * (ρ (b 0) : ℝ))
        (fun a : C => p a * (ρ a : ℝ)) ?_
      intro b
      simp
    have hpositive : ∃ a : C, 0 < p a := by
      by_contra h
      have hnonpos : ∀ a : C, p a ≤ 0 := fun a => le_of_not_gt (fun ha => h ⟨a, ha⟩)
      have hs : (∑ a : C, p a) ≤ 0 :=
        Finset.sum_nonpos fun a ha => hnonpos a
      linarith
    rcases hpositive with ⟨a, ha⟩
    let ba : Fin 1 → C := fun _ => a
    have hsumlt :
        (∑ b : Fin 1 → C, p (b 0) * (ρ (b 0) : ℝ)) <
          ∑ b : Fin 1 → C, p (b 0) * (ρ (r b) : ℝ) := by
      apply Finset.sum_lt_sum
      · intro b hb
        have hpref :
            E.prefers v (r b) (b 0) :=
          hallgood b v (b 0) (Finset.mem_image.mpr ⟨0, Finset.mem_univ 0, rfl⟩)
        exact mul_le_mul_of_nonneg_left
          (by exact_mod_cast (hρpref (r b) (b 0) hpref).le) (hpnonneg (b 0))
      · refine ⟨ba, Finset.mem_univ ba, ?_⟩
        have hpref :
            E.prefers v (r ba) (ba 0) :=
          hallgood ba v (ba 0) (Finset.mem_image.mpr ⟨0, Finset.mem_univ 0, rfl⟩)
        have hrank : (ρ (ba 0) : ℝ) < ρ (r ba) := by
          exact_mod_cast hρpref (r ba) (ba 0) hpref
        have hpba : 0 < p (ba 0) := by simpa [ba] using ha
        exact mul_lt_mul_of_pos_left hrank hpba
    rw [hinput_expect, hresp_expect] at hsumlt
    exact (lt_irrefl _ hsumlt).elim
  · have hb := hcut (1 / 2 : ℝ) (by constructor <;> norm_num)
    have hpow : (1 / 2 : ℝ) ^ (Nat.succ (Nat.succ k)) ≤ (1 / 2 : ℝ) ^ 2 :=
      pow_right_anti₀ (by norm_num) (by norm_num) (by omega)
    norm_num at hpow
    linarith

@[blueprint "lem:strict-quantile-integral-from-cut-bound"
  (statement := /-- Let \(0<\alpha<1\), let \(k\geq1\), and let \(g\) be admissible.
  If
  \[
    \alpha\leq1-t+t^k\qquad(0\leq t\leq1),
  \]
  then
  \[
    \int_0^\alpha g(x)\,dx<
    \int_{1-\alpha}^1g(x^k)\,dx.
  \] -/)
  (proof := /-- Put \(h(x)=g(x^k)\).  The cut bound, applied to
  \(t=1-\alpha+u\), gives \(u\leq(1-\alpha+u)^k\), so monotonicity of \(g\)
  gives the pointwise comparison after translating the right integral to
  \([0,\alpha]\).  Nonconstancy and monotonicity give \(h(0)<h(1)\).
  Continuity at \(1\) and convexity make \(h\) strictly increasing on a
  terminal interval.  Choosing an interior translated point above both that
  interval and the \(k\)-th root of \(\alpha\) produces a strict comparison
  on a neighborhood of positive measure.  Strict monotonicity of the
  interval integral and translation of variables yield the claim. -/)
  (title := /-- Strict integral comparison from polynomial cut bounds -/)
  (latexEnv := "lemma")]
lemma strict_quantile_integral_from_cut_bound (g : ℝ → ℝ) (α : ℝ) (k : ℕ)
    (hαpos : 0 < α) (hαlt : α < 1) (hk : 0 < k)
    (hg : integral_criterion_admissible g k)
    (hcut : ∀ t ∈ Set.Icc (0 : ℝ) 1, α ≤ 1 - t + t ^ k) :
    (∫ x in (0 : ℝ)..α, g x) < ∫ x in (1 - α)..1, g (x ^ k) := by
  rcases hg with ⟨hgnonneg, hgnonconst, hgmono, hgcont, hhconv⟩
  let h : ℝ → ℝ := fun x => g (x ^ k)
  let root : ℝ → ℝ := fun x => x ^ ((k : ℝ)⁻¹)
  have hhconv' : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) h := by
    simpa [h] using hhconv
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  have hkinvpos : (0 : ℝ) < (k : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hk)
  have hhmono : MonotoneOn h (Set.Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    apply hgmono
    · exact ⟨pow_nonneg hx.1 k, pow_le_one₀ hx.1 hx.2⟩
    · exact ⟨pow_nonneg hy.1 k, pow_le_one₀ hy.1 hy.2⟩
    · exact pow_le_pow_left₀ hx.1 hxy k
  have hg01 : g 0 < g 1 := by
    rcases hgnonconst with ⟨x, hx, y, hy, hxy⟩
    have h0x := hgmono (by simp) hx hx.1
    have hx1 := hgmono hx (by simp) hx.2
    have h0y := hgmono (by simp) hy hy.1
    have hy1 := hgmono hy (by simp) hy.2
    have hle : g 0 ≤ g 1 := le_trans h0x hx1
    exact lt_of_le_of_ne hle fun heq => by
      have hx0 : g x = g 0 := le_antisymm (heq ▸ hx1) h0x
      have hy0 : g y = g 0 := le_antisymm (heq ▸ hy1) h0y
      exact hxy (hx0.trans hy0.symm)
  have hh01 : h 0 < h 1 := by
    simpa [h, zero_pow hk0, one_pow] using hg01
  have hhcont : ContinuousAt h 1 := by
    have hpcont : ContinuousAt (fun x : ℝ => x ^ k) 1 := by fun_prop
    have hgcont' : ContinuousAt g ((fun x : ℝ => x ^ k) 1) := by
      simpa using hgcont
    have hc : ContinuousAt (fun x : ℝ => g (x ^ k)) 1 :=
      Filter.Tendsto.comp hgcont' hpcont
    simpa [h] using hc
  have hnear : ∀ᶠ x in nhds (1 : ℝ), h 0 < h x :=
    continuousAt_const.eventually_lt hhcont hh01
  rcases Metric.mem_nhds_iff.mp hnear with ⟨ε, hε, hεsub⟩
  let δ : ℝ := min (ε / 2) (1 / 2)
  let y : ℝ := 1 - δ
  have hδpos : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hypos : 0 < y := by dsimp [y]; linarith
  have hylt : y < 1 := by dsimp [y]; linarith
  have hyball : y ∈ Metric.ball (1 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [y, δ]
    have hδle : min (ε / 2) (1 / 2) ≤ ε / 2 := min_le_left _ _
    rw [abs_of_nonpos]
    · linarith
    · linarith
  have hh0y : h 0 < h y := hεsub hyball
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hypos.le, hylt.le⟩
  have hhstrict : StrictMonoOn h (Set.Icc (0 : ℝ) 1 ∩ Set.Ici y) :=
    hhconv'.strictMonoOn (by simp) hypos hh0y
  let z : ℝ := root α
  have hzpos : 0 < z := Real.rpow_pos_of_pos hαpos _
  have hzlt : z < 1 := Real.rpow_lt_one hαpos.le hαlt hkinvpos
  have hzpow : z ^ k = α := by
    simpa [z, root] using Real.rpow_inv_natCast_pow hαpos.le hk0
  let M : ℝ := max y (max z (1 - α))
  let s : ℝ := (M + 1) / 2
  have hMlt : M < 1 := by
    dsimp [M]
    exact max_lt hylt (max_lt hzlt (by linarith))
  have hMleS : M < s := by dsimp [s]; linarith
  have hslt : s < 1 := by dsimp [s]; linarith
  have hys : y < s := lt_of_le_of_lt (le_max_left _ _) hMleS
  have hzs : z < s := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hMleS
  have hshift : 1 - α < s :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hMleS
  have hspos : 0 < s := lt_trans hypos hys
  have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hspos.le, hslt.le⟩
  let u : ℝ := s - (1 - α)
  have hupos : 0 < u := by dsimp [u]; linarith
  have hult : u < α := by dsimp [u]; linarith
  let ru : ℝ := root u
  have hrupos : 0 < ru := Real.rpow_pos_of_pos hupos _
  have hrupow : ru ^ k = u := by
    simpa [ru, root] using Real.rpow_inv_natCast_pow hupos.le hk0
  have hpowzs : α < s ^ k := by
    rw [← hzpow]
    exact pow_lt_pow_left₀ hzs hzpos.le hk0
  have hrus : ru < s := by
    have hurpow :
        root u < root (s ^ k) :=
      Real.rpow_lt_rpow hupos.le (by linarith [hpowzs]) hkinvpos
    simpa [ru, root, Real.pow_rpow_inv_natCast hspos.le hk0] using hurpow
  have hruIcc : ru ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hrupos.le, (lt_trans hrus hslt).le⟩
  have hhrus : h ru < h s := by
    by_cases hruy : ru < y
    · exact lt_of_le_of_lt (hhmono hruIcc hyIcc hruy.le)
        (hhstrict ⟨hyIcc, by simp⟩ ⟨hsIcc, hys.le⟩ hys)
    · exact hhstrict ⟨hruIcc, le_of_not_gt hruy⟩ ⟨hsIcc, hys.le⟩ hrus
  have hstrict_at : g u < g ((1 - α + u) ^ k) := by
    have hsu : 1 - α + u = s := by dsimp [u]; ring
    simpa [h, hrupow, hsu] using hhrus
  let upper : ℝ → ℝ := fun x => g ((1 - α + x) ^ k)
  have hgmono_small : MonotoneOn g (Set.uIcc (0 : ℝ) α) := by
    rw [Set.uIcc_of_le hαpos.le]
    exact hgmono.mono fun x hx => ⟨hx.1, hx.2.trans hαlt.le⟩
  have hupper_mono : MonotoneOn upper (Set.uIcc (0 : ℝ) α) := by
    rw [Set.uIcc_of_le hαpos.le]
    intro x hx x' hx' hxx'
    apply hgmono
    · constructor
      · exact pow_nonneg (by linarith [hx.1]) k
      · exact pow_le_one₀ (by linarith [hx.1]) (by linarith [hx.2])
    · constructor
      · exact pow_nonneg (by linarith [hx'.1]) k
      · exact pow_le_one₀ (by linarith [hx'.1]) (by linarith [hx'.2])
    · exact pow_le_pow_left₀ (by linarith [hx.1]) (by linarith) k
  have hpointwise : ∀ x ∈ Set.Ioc (0 : ℝ) α, g x ≤ upper x := by
    intro x hx
    have hshiftIcc : 1 - α + x ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · linarith [hx.1, hαlt]
      · linarith [hx.2]
    apply hgmono ⟨hx.1.le, hx.2.trans hαlt.le⟩
      ⟨pow_nonneg hshiftIcc.1 k, pow_le_one₀ hshiftIcc.1 hshiftIcc.2⟩
    have := hcut (1 - α + x) hshiftIcc
    linarith
  let u₂ : ℝ := (u + α) / 2
  have huu₂ : u < u₂ := by dsimp [u₂]; linarith
  have hu₂α : u₂ < α := by dsimp [u₂]; linarith
  have hstrict_interval :
      Set.Ioo u u₂ ⊆ {x : ℝ | g x < upper x} := by
    intro x hx
    let rx : ℝ := root x
    have hxpos : 0 < x := lt_trans hupos hx.1
    have hrxpos : 0 < rx := Real.rpow_pos_of_pos hxpos _
    have hrxpow : rx ^ k = x := by
      simpa [rx, root] using Real.rpow_inv_natCast_pow hxpos.le hk0
    have hrxs : rx < s := by
      have hrpow : root x < root (s ^ k) :=
        Real.rpow_lt_rpow hxpos.le (by linarith [hx.2, hu₂α, hpowzs]) hkinvpos
      simpa [rx, root, Real.pow_rpow_inv_natCast hspos.le hk0] using hrpow
    have hrxIcc : rx ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hrxpos.le, (lt_trans hrxs hslt).le⟩
    have hhrxs : h rx < h s := by
      by_cases hrxy : rx < y
      · exact lt_of_le_of_lt (hhmono hrxIcc hyIcc hrxy.le)
          (hhstrict ⟨hyIcc, by simp⟩ ⟨hsIcc, hys.le⟩ hys)
      · exact hhstrict ⟨hrxIcc, le_of_not_gt hrxy⟩ ⟨hsIcc, hys.le⟩ hrxs
    have hshiftx : s ≤ 1 - α + x := by
      dsimp [u] at hx
      linarith [hx.1]
    have hshiftxIcc : 1 - α + x ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · linarith [hshiftx, hspos]
      · linarith [hx.2, hu₂α]
    have hhupper : h s ≤ h (1 - α + x) :=
      hhmono hsIcc hshiftxIcc hshiftx
    have := lt_of_lt_of_le hhrxs hhupper
    simpa [h, upper, hrxpow] using this
  let c : ℝ := (u + u₂) / 2
  have huc : u < c := by dsimp [c]; linarith
  have hcu₂ : c < u₂ := by dsimp [c]; linarith
  have hset_nhds :
      ({x : ℝ | g x < upper x} ∩ Set.Ioc (0 : ℝ) α) ∈ nhds c := by
    apply Filter.mem_of_superset (Ioo_mem_nhds huc hcu₂)
    intro x hx
    exact ⟨hstrict_interval hx, ⟨lt_trans hupos hx.1, (lt_trans hx.2 hu₂α).le⟩⟩
  have hstrict_measure :
      (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioc (0 : ℝ) α)
          {x : ℝ | g x < upper x} ≠ 0 := by
    rw [MeasureTheory.Measure.restrict_apply' measurableSet_Ioc]
    exact ne_of_gt (MeasureTheory.Measure.measure_pos_of_mem_nhds
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) hset_nhds)
  have hlt :
      (∫ x in (0 : ℝ)..α, g x) < ∫ x in (0 : ℝ)..α, upper x := by
    apply intervalIntegral.integral_lt_integral_of_ae_le_of_measure_setOf_lt_ne_zero
      hαpos.le hgmono_small.intervalIntegrable hupper_mono.intervalIntegrable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
      exact hpointwise x hx
    · exact hstrict_measure
  calc
    (∫ x in (0 : ℝ)..α, g x) < ∫ x in (0 : ℝ)..α, upper x := hlt
    _ = ∫ x in (1 - α)..1, g (x ^ k) := by
      simpa [upper] using
        (intervalIntegral.integral_comp_add_left
          (f := fun x : ℝ => g (x ^ k)) (a := (0 : ℝ)) (b := α) (1 - α))

@[blueprint "lem:strict-quantile-rearrangement"
  (statement := /-- Let \(V\) and \(C\) be finite, let \(\mathcal E\) be an election, let
  \(0<\alpha\leq1\), and let \(k\geq1\). Let \(g:\mathbb R\to\mathbb R\) be admissible for
  the integral criterion. Suppose \(r:C^k\to C\) assigns to each tuple \(\mathbf b\) a
  candidate preferred to every entry of \(\mathbf b\) by at least an
  \(\alpha\)-fraction of the voters. If a probability vector \(p\) on \(C\) is stationary
  for the polynomial response map induced by \(r\), then
  \[
    \int_0^\alpha g(x)\,dx
      <\int_{1-\alpha}^1 g(x^k)\,dx.
  \] -/)
  (proof := /-- By \cref{lem:strict-quantile-response-bound}, stationarity and the
  response inequalities imply
  \[
    \alpha\leq1-t+t^k\qquad(0\leq t\leq1).
  \]
  The same hypotheses, together with \(0<\alpha\leq1\) and \(k>0\), imply
  \(\alpha<1\) by \cref{lem:strict-quantile-threshold-below-one}.  Applying
  \cref{lem:strict-quantile-integral-from-cut-bound} to these polynomial cut bounds and
  the admissibility of \(g\) gives
  \[
    \int_0^\alpha g(x)\,dx<
    \int_{1-\alpha}^1g(x^k)\,dx,
  \]
  as required. -/)
  (title := /-- Strict quantile comparison for a stationary response coupling -/)
  (latexEnv := "lemma")]
lemma strict_quantile_rearrangement {V C : Type*} [Fintype V] [Fintype C]
    [DecidableEq C] (E : election V C) (g : ℝ → ℝ) (α : ℝ) (k : ℕ)
    (hαpos : 0 < α) (hαone : α ≤ 1) (hk : 0 < k)
    (hg : integral_criterion_admissible g k) (r : (Fin k → C) → C)
    (hr :
      ∀ b : Fin k → C,
        α ≤ voter_fraction E (r b) (Finset.univ.image b))
    (p : C → ℝ) (hpnonneg : ∀ a : C, 0 ≤ p a) (hpsum : (∑ a : C, p a) = 1)
    (hstationary :
      ∀ a : C,
        p a =
          ∑ b : Fin k → C, if r b = a then ∏ i : Fin k, p (b i) else 0) :
    (∫ x in (0 : ℝ)..α, g x) < ∫ x in (1 - α)..1, g (x ^ k) := by
  have hcut :=
    strict_quantile_response_bound E α k hαpos r hr p hpnonneg hpsum hstationary
  have hαlt :=
    strict_quantile_threshold_below_one E α k hαpos hαone hk r hr p hpnonneg hpsum
      hstationary
  exact strict_quantile_integral_from_cut_bound g α k hαpos hαlt hk hg hcut

@[blueprint "lem:integral-gap-of-no-undominated"
  (statement := /-- Let \(V\) and \(C\) be finite, let \(\mathcal E\) be an election, let
  \(0<\alpha\leq1\), and let \(k\geq1\). Let \(g:\mathbb R\to\mathbb R\) be admissible
  for the integral criterion. If every committee \(S\) with \(|S|\leq k\) is dominated by
  some candidate on at least an \(\alpha\)-fraction of the voters, then
  \[
    \int_0^\alpha g(x)\,dx
      < \int_{1-\alpha}^1 g(x^k)\,dx .
  \] -/)
  (proof := /-- For each ordered tuple \(\mathbf b\in C^k\), let \(S_{\mathbf b}\) be
  the set of its entries. Since \(|S_{\mathbf b}|\leq k\), choose \(r(\mathbf b)\in C\)
  such that
  \[
    q_{\mathcal E}(r(\mathbf b),S_{\mathbf b})\geq\alpha.
  \]
  Applying the hypothesis to the empty committee also shows that \(C\) is nonempty.
  Hence \cref{lem:finite-simplex-response-fixed-point} supplies a probability vector
  \(p\) on \(C\) satisfying
  \[
    p(a)=\sum_{\mathbf b\in C^k:\,r(\mathbf b)=a}
      \prod_{i=1}^k p(b_i)
    \qquad(a\in C).
  \]
  The response inequalities, the stationarity identity, the assumptions
  \(0<\alpha\leq1\) and \(k>0\), and the admissibility of \(g\) are exactly the hypotheses
  of \cref{lem:strict-quantile-rearrangement}. That lemma therefore gives
  \[
    \int_0^\alpha g(x)\,dx
      <\int_{1-\alpha}^1 g(x^k)\,dx,
  \]
  as required. -/)
  (title := /-- Failure of undominance forces the strict integral gap -/)
  (latexEnv := "lemma")]
lemma integral_gap_of_no_undominated {V C : Type*} [Fintype V] [Fintype C]
    (E : election V C) (g : ℝ → ℝ) (α : ℝ) (k : ℕ) (hαpos : 0 < α) (hαone : α ≤ 1)
    (hk : 0 < k) (hg : integral_criterion_admissible g k)
    (hno :
      ∀ S : committee C, S.card ≤ k →
        ∃ a : C, α ≤ voter_fraction E a S) :
    (∫ x in (0 : ℝ)..α, g x) < ∫ x in (1 - α)..1, g (x ^ k) := by
  classical
  letI : Nonempty C :=
    ⟨Classical.choose (hno ∅ (by simp))⟩
  have hcard (b : Fin k → C) : (Finset.univ.image b).card ≤ k := by
    simpa using
      (Finset.card_image_le (s := (Finset.univ : Finset (Fin k))) (f := b))
  let r : (Fin k → C) → C := fun b =>
    Classical.choose (hno (Finset.univ.image b) (hcard b))
  have hr :
      ∀ b : Fin k → C,
        α ≤ voter_fraction E (r b) (Finset.univ.image b) := by
    intro b
    simpa [r] using
      (Classical.choose_spec (hno (Finset.univ.image b) (hcard b)))
  obtain ⟨p, hpnonneg, hpsum, hstationary⟩ :=
    finite_simplex_response_fixed_point k r
  exact
    strict_quantile_rearrangement E g α k hαpos hαone hk hg r hr p hpnonneg hpsum
      hstationary

@[blueprint "lem:integral-criterion-yields-undominated"
  (statement := /-- Let \(V\) and \(C\) be finite, let \(\mathcal E\) be an election, let
  \(0<\alpha\leq 1\), and let \(k\geq 1\). Suppose that \(g:\mathbb R\to\mathbb R\) is admissible
  for the integral criterion and that
  \[
    \int_0^\alpha g(x)\,dx\ \geq\
    \int_{1-\alpha}^1 g(x^k)\,dx.
  \]
  Then \(\mathcal E\) has an \(\alpha\)-undominated committee containing at most \(k\)
  candidates. -/)
  (proof := /-- Suppose to the contrary that no \(\alpha\)-undominated committee containing
  at most \(k\) candidates exists. Then for every committee \(S\) with \(|S|\leq k\), the
  negation of the defining strict inequalities supplies a candidate \(a\) such that
  \(q_{\mathcal E}(a,S)\geq\alpha\). By
  \cref{lem:integral-gap-of-no-undominated}, this implies
  \[
    \int_0^\alpha g(x)\,dx
      <\int_{1-\alpha}^1 g(x^k)\,dx,
  \]
  contradicting the assumed weak reverse inequality. Hence such an
  \(\alpha\)-undominated committee exists. -/)
  (title := /-- The integral criterion implies existence of an undominated committee -/)
  (latexEnv := "lemma")]
lemma integral_criterion_yields_undominated {V C : Type*} [Fintype V] [Fintype C]
    (E : election V C) (g : ℝ → ℝ) (α : ℝ) (k : ℕ) (hαpos : 0 < α) (hαone : α ≤ 1)
    (hk : 0 < k) (hg : integral_criterion_admissible g k)
    (hintegral :
      (∫ x in (0 : ℝ)..α, g x) ≥ ∫ x in (1 - α)..1, g (x ^ k)) :
    ∃ S : committee C, alpha_undominated E α k S := by
  classical
  contrapose! hintegral
  apply integral_gap_of_no_undominated E g α k hαpos hαone hk hg
  simpa only [alpha_undominated, not_exists, not_and, not_forall, not_lt] using hintegral

@[blueprint "lem:main-hypothesis-rearrangement"
  (statement := /-- Let \(\alpha\in\mathbb R\) and \(k\in\mathbb N\) satisfy
  \(0<\alpha\leq 1\) and \(k>0\). If
  \[
    \frac{\alpha}{1-\ln\alpha}\geq\frac{2}{k+1},
  \]
  then
  \[
    \frac{k}{k+1}\left(1+\frac{\ln\alpha}{k}\right)
      \geq 1-\frac{\alpha}{2}.
  \] -/)
  (proof := /-- Since \(0<\alpha\leq 1\), one has \(\ln\alpha\leq 0\), and hence
  \(1-\ln\alpha>0\). Since \(k>0\), both \(k\) and \(k+1\) are positive. Cross-multiplying the
  assumed inequality therefore gives
  \[
    2(1-\ln\alpha)\leq \alpha(k+1),
  \]
  or equivalently \(2-\alpha\leq 2(k+\ln\alpha)/(k+1)\). Finally,
  \((k+\ln\alpha)/(k+1)=k(1+(\ln\alpha)/k)/(k+1)\), which proves the claimed inequality. -/)
  (title := /-- Rearrangement of the numerical hypothesis -/)
  (latexEnv := "lemma")]
lemma main_hypothesis_rearrangement (α : ℝ) (k : ℕ) (hαpos : 0 < α) (hαone : α ≤ 1)
    (hk : 0 < k)
    (hnumeric : α / (1 - Real.log α) ≥ 2 / ((k : ℝ) + 1)) :
    ((k : ℝ) / ((k : ℝ) + 1)) * (1 + Real.log α / (k : ℝ)) ≥ 1 - α / 2 := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hk1 : 0 < (k : ℝ) + 1 := by positivity
  have hlog := Real.log_nonpos hαpos.le hαone
  have hden : 0 < 1 - Real.log α := by linarith
  have hcross := (div_le_div_iff₀ hk1 hden).mp hnumeric
  field_simp
  nlinarith [hcross]

@[blueprint "lem:fractional-power-bound"
  (statement := /-- Let \(\alpha\in\mathbb R\) and \(k\in\mathbb N\) satisfy
  \(0<\alpha\leq 1\) and \(k>0\). If
  \[
    \frac{\alpha}{1-\ln\alpha}\geq\frac{2}{k+1},
  \]
  then
  \[
    \frac{k}{k+1}\alpha^{1/k}\geq 1-\frac{\alpha}{2}.
  \] -/)
  (proof := /-- By \cref{lem:main-hypothesis-rearrangement},
  \[
    \frac{k}{k+1}\left(1+\frac{\ln\alpha}{k}\right)
      \geq 1-\frac{\alpha}{2}.
  \]
  Positivity of \(\alpha\) gives
  \(\alpha^{1/k}=\exp((\ln\alpha)/k)\). The inequality
  \(1+t\leq\exp(t)\), applied to \(t=(\ln\alpha)/k\), and multiplication by the nonnegative
  factor \(k/(k+1)\) prove the claim. -/)
  (title := /-- Lower bound for the fractional power -/)
  (latexEnv := "lemma")]
lemma fractional_power_bound (α : ℝ) (k : ℕ) (hαpos : 0 < α) (hαone : α ≤ 1)
    (hk : 0 < k)
    (hnumeric : α / (1 - Real.log α) ≥ 2 / ((k : ℝ) + 1)) :
    ((k : ℝ) / ((k : ℝ) + 1)) * α ^ ((k : ℝ)⁻¹) ≥ 1 - α / 2 := by
  calc
    1 - α / 2 ≤ ((k : ℝ) / ((k : ℝ) + 1)) * (1 + Real.log α / (k : ℝ)) :=
      main_hypothesis_rearrangement α k hαpos hαone hk hnumeric
    _ ≤ ((k : ℝ) / ((k : ℝ) + 1)) * α ^ ((k : ℝ)⁻¹) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [Real.rpow_def_of_pos hαpos, div_eq_mul_inv, add_comm] using
          (Real.add_one_le_exp (Real.log α / (k : ℝ)))
      · positivity

@[blueprint "lem:scaled-fractional-power-bound"
  (statement := /-- Let \(\alpha\in\mathbb R\) and \(k\in\mathbb N\) satisfy
  \(0<\alpha\leq 1\) and \(k>0\). If
  \[
    \frac{\alpha}{1-\ln\alpha}\geq\frac{2}{k+1},
  \]
  then
  \[
    \frac{k}{k+1}\alpha^{1+1/k}
      \geq \frac12\bigl(1-(1-\alpha)^2\bigr).
  \] -/)
  (proof := /-- Multiply the inequality in \cref{lem:fractional-power-bound} by the positive
  number \(\alpha\). For \(\alpha>0\), the real-power addition law gives
  \(\alpha\alpha^{1/k}=\alpha^{1+1/k}\). Finally,
  \(\alpha(1-\alpha/2)=\tfrac12(1-(1-\alpha)^2)\), which yields the stated inequality. -/)
  (title := /-- Scaled fractional-power inequality -/)
  (latexEnv := "lemma")]
lemma scaled_fractional_power_bound (α : ℝ) (k : ℕ) (hαpos : 0 < α) (hαone : α ≤ 1)
    (hk : 0 < k)
    (hnumeric : α / (1 - Real.log α) ≥ 2 / ((k : ℝ) + 1)) :
    ((k : ℝ) / ((k : ℝ) + 1)) * α ^ (1 + (k : ℝ)⁻¹) ≥
      (1 / 2 : ℝ) * (1 - (1 - α) ^ 2) := by
  rw [Real.rpow_add hαpos, Real.rpow_one]
  have hscaled := mul_le_mul_of_nonneg_left
    (fractional_power_bound α k hαpos hαone hk hnumeric) (le_of_lt hαpos)
  nlinarith [hscaled]

@[blueprint "lem:fractional-power-integral"
  (statement := /-- Let \(\alpha>0\) and \(k\geq 1\). Then
  \[
    \int_0^\alpha x^{1/k}\,dx
      =\frac{k}{k+1}\alpha^{1+1/k}.
  \] -/)
  (proof := /-- Cast the inequality \(k>0\) to the reals. Its reciprocal is positive and
  hence greater than \(-1\), so the interval-integral formula for the real power \(x^{1/k}\)
  applies. The exponent \(1+1/k\) is nonzero, so its real power at the lower endpoint is
  \(0\). Clearing the nonzero denominators and normalizing the resulting field identity gives
  the stated coefficient \(k/(k+1)\). -/)
  (title := /-- Integral of the fractional power -/)
  (latexEnv := "lemma")]
lemma fractional_power_integral (α : ℝ) (k : ℕ) (hαpos : 0 < α) (hk : 0 < k) :
    (∫ x in (0 : ℝ)..α, x ^ ((k : ℝ)⁻¹)) =
      ((k : ℝ) / ((k : ℝ) + 1)) * α ^ (1 + (k : ℝ)⁻¹) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast hk
  have hr : 0 < (k : ℝ)⁻¹ := inv_pos.mpr hkR
  rw [integral_rpow (Or.inl (by linarith))]
  rw [Real.zero_rpow (ne_of_gt (by positivity))]
  field_simp [hkR.ne']
  ring_nf

@[blueprint "lem:identity-integral"
  (statement := /-- For every \(\alpha\in\mathbb R\),
  \[
    \int_{1-\alpha}^1 x\,dx
      =\frac12\bigl(1-(1-\alpha)^2\bigr).
  \] -/)
  (proof := /-- The interval-integral formula for the identity function gives
  \[
    \int_{1-\alpha}^1 x\,dx
      =\frac{1^2-(1-\alpha)^2}{2}.
  \]
  Since \(1^2=1\) and division by \(2\) is multiplication by \(1/2\) in
  \(\mathbb R\), the ring identity
  \[
    \frac{1^2-(1-\alpha)^2}{2}
      =\frac12\bigl(1-(1-\alpha)^2\bigr)
  \]
  gives the asserted equality. -/)
  (title := /-- Integral of the identity function -/)
  (latexEnv := "lemma")]
lemma identity_integral (α : ℝ) :
    (∫ x in (1 - α)..1, x) = (1 / 2 : ℝ) * (1 - (1 - α) ^ 2) := by
  rw [integral_id]
  ring

@[blueprint "lem:fractional-power-of-natural-power"
  (statement := /-- Let \(k\) be a positive natural number. For every real number \(x\in[0,1]\),
  \[
    (x^k)^{1/k}=x.
  \] -/)
  (proof := /-- Fix \(x\in[0,1]\). Then \(x\geq 0\). Since \(k\) is positive, one has
  \(k\neq 0\). The real-power identity
  \((x^k)^{(k:\mathbb R)^{-1}}=x\) for a nonnegative real number \(x\) and a nonzero natural
  number \(k\) gives the required equality. -/)
  (title := /-- A fractional power cancels a natural power -/)
  (latexEnv := "lemma")]
lemma fractional_power_of_natural_power (k : ℕ) (hk : 0 < k) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, (x ^ k) ^ ((k : ℝ)⁻¹) = x := by
  intro x hx
  exact Real.pow_rpow_inv_natCast hx.1 (Nat.ne_of_gt hk)

@[blueprint "lem:composed-fractional-power-integral"
  (statement := /-- Let \(\alpha\in\mathbb R\) and \(k\in\mathbb N\) satisfy
  \(0<\alpha\leq 1\) and \(0<k\). Then
  \[
    \int_{1-\alpha}^1 (x^k)^{1/k}\,dx
      =\int_{1-\alpha}^1 x\,dx.
  \] -/)
  (proof := /-- The inequalities \(0<\alpha\leq 1\) imply
  \([1-\alpha,1]\subseteq[0,1]\). Hence
  \cref{lem:fractional-power-of-natural-power} gives
  \((x^k)^{1/k}=x\) at every point of the interval of integration. Congruence of interval
  integrals under pointwise equality gives the result. -/)
  (title := /-- Integral of the composed fractional power -/)
  (latexEnv := "lemma")]
lemma composed_fractional_power_integral (α : ℝ) (k : ℕ) (hαpos : 0 < α)
    (hαone : α ≤ 1) (hk : 0 < k) :
    (∫ x in (1 - α)..1, (x ^ k) ^ ((k : ℝ)⁻¹)) = ∫ x in (1 - α)..1, x := by
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le (by linarith : 1 - α ≤ 1)] at hx
  exact fractional_power_of_natural_power k hk x ⟨by linarith [hx.1], hx.2⟩

@[blueprint "lem:fractional-power-integral-criterion"
  (statement := /-- Let \(\alpha\in\mathbb R\) and \(k\in\mathbb N\) satisfy
  \(0<\alpha\leq 1\) and \(k\geq 1\). If
  \[
    \frac{\alpha}{1-\ln\alpha}\geq\frac{2}{k+1},
  \]
  then the function \(g:\mathbb R\to\mathbb R\) defined by \(g(x)=x^{1/k}\) satisfies the
  integral inequality
  \[
    \int_0^\alpha g(x)\,dx
      \geq \int_{1-\alpha}^1 g(x^k)\,dx.
  \] -/)
  (proof := /-- By \cref{lem:scaled-fractional-power-bound}, the expression
  \(\frac{k}{k+1}\alpha^{1+1/k}\) is at least
  \(\frac12(1-(1-\alpha)^2)\). The left expression is the first integral by
  \cref{lem:fractional-power-integral}, while the right expression is the identity integral by
  \cref{lem:identity-integral}. Finally,
  \cref{lem:composed-fractional-power-integral} identifies that identity integral with the
  integral of \(g(x^k)=(x^k)^{1/k}\). Combining these equalities with the inequality proves the
  assertion. -/)
  (title := /-- Verification of the fractional-power integral criterion -/)
  (latexEnv := "lemma")]
lemma fractional_power_integral_criterion (α : ℝ) (k : ℕ) (hαpos : 0 < α)
    (hαone : α ≤ 1) (hk : 0 < k)
    (hnumeric : α / (1 - Real.log α) ≥ 2 / ((k : ℝ) + 1)) :
    (∫ x in (0 : ℝ)..α, x ^ ((k : ℝ)⁻¹)) ≥
      ∫ x in (1 - α)..1, (x ^ k) ^ ((k : ℝ)⁻¹) := by
  rw [fractional_power_integral α k hαpos hk,
    composed_fractional_power_integral α k hαpos hαone hk, identity_integral α]
  exact scaled_fractional_power_bound α k hαpos hαone hk hnumeric

@[blueprint "lem:fractional-power-admissible"
  (statement := /-- For every positive integer \(k\), define \(g:\mathbb R\to\mathbb R\) by
  \(g(x)=x^{1/k}\). The function \(g\) is nonnegative, nonconstant, and nondecreasing on
  \([0,1]\), is continuous at \(1\), and the function \(x\mapsto g(x^k)\) is convex on
  \([0,1]\). Hence \(g\) is admissible for the integral criterion with parameter \(k\). -/)
  (proof := /-- Set \(r=1/k\). Since \(k\) is positive, both \(k\) and \(r\) are nonzero and
  \(r>0\). For every \(x\in[0,1]\), nonnegativity of \(x\) implies \(x^r\geq0\). Moreover,
  \(g(0)=0\) and \(g(1)=1\), so \(g\) is nonconstant on \([0,1]\). If
  \(0\leq x\leq y\leq1\), monotonicity of real exponentiation with nonnegative exponent gives
  \(x^r\leq y^r\). The real power function with the fixed positive exponent \(r\) is
  continuous at \(1\). Finally, \cref{lem:fractional-power-of-natural-power} gives
  \((x^k)^{1/k}=x\) for every \(x\in[0,1]\). Thus \(x\mapsto g(x^k)\) agrees on \([0,1]\)
  with the identity function, which is convex on this convex interval. These five properties
  are exactly the conditions in \cref{def:integral-criterion-admissible}. -/)
  (title := /-- Admissibility of the fractional-power function -/)
  (latexEnv := "lemma")]
lemma fractional_power_admissible (k : ℕ) (hk : 0 < k) :
    integral_criterion_admissible (fun x : ℝ => x ^ ((k : ℝ)⁻¹)) k := by
  unfold integral_criterion_admissible
  have hkR : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast hk
  have hr : 0 < (k : ℝ)⁻¹ := inv_pos.mpr hkR
  refine ⟨fun x hx => Real.rpow_nonneg hx.1 _, ?_, ?_, ?_, ?_⟩
  · refine ⟨0, ⟨le_rfl, zero_le_one⟩, 1, ⟨zero_le_one, le_rfl⟩, ?_⟩
    simp [Real.zero_rpow hr.ne']
  · exact
      (Real.monotoneOn_rpow_Ici_of_exponent_nonneg hr.le).mono Set.Icc_subset_Ici_self
  · exact Real.continuousAt_rpow_const 1 _ (Or.inl one_ne_zero)
  · refine (convexOn_id (convex_Icc (0 : ℝ) 1)).congr ?_
    intro x hx
    exact (fractional_power_of_natural_power k hk x hx).symm

@[blueprint "thm:main"
  (statement := /-- Let \(V\) and \(C\) be finite types, let \(\mathcal E\) be an election on
  \((V,C)\), let \(\alpha\in\mathbb R\) satisfy \(0<\alpha\leq 1\), and let
  \(k\in\mathbb N\) satisfy \(k\geq 1\). If
  \[
    \frac{\alpha}{1-\ln\alpha}\geq\frac{2}{k+1},
  \]
  then there exists an \(\alpha\)-undominated committee containing at most \(k\) candidates. -/)
  (proof := /-- Define \(g(x)=x^{1/k}\). By
  \cref{lem:fractional-power-admissible}, this function is admissible for the integral
  criterion. By \cref{lem:fractional-power-integral-criterion}, the numerical hypothesis
  implies
  \[
    \int_0^\alpha g(x)\,dx
      \geq\int_{1-\alpha}^1 g(x^k)\,dx.
  \]
  Applying \cref{lem:integral-criterion-yields-undominated} to this admissible function and
  the displayed integral inequality produces a committee \(S\) with \(|S|\leq k\) and
  \(q_{\mathcal E}(a,S)<\alpha\) for every candidate \(a\). This is precisely an
  \(\alpha\)-undominated committee of cardinality at most \(k\). -/)
  (title := /-- Six candidates suffice to win a voter majority -/)
  (latexEnv := "theorem")]
theorem main {V C : Type*} [Fintype V] [Fintype C] (E : election V C) (α : ℝ) (k : ℕ)
    (hαpos : 0 < α) (hαone : α ≤ 1) (hk : 0 < k)
    (hnumeric : α / (1 - Real.log α) ≥ 2 / ((k : ℝ) + 1)) :
    ∃ S : committee C, alpha_undominated E α k S := by
  apply integral_criterion_yields_undominated E (fun x : ℝ => x ^ ((k : ℝ)⁻¹)) α k hαpos hαone hk
  · exact fractional_power_admissible k hk
  · exact fractional_power_integral_criterion α k hαpos hαone hk hnumeric

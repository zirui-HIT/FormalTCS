import Architect
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option linter.all false
set_option maxHeartbeats 4000000

@[blueprint "def:metric-matrix"
  (statement := /-- For $n\in\mathbb N$, an $n\times n$ real matrix is a function on $[n]\times[n]$. -/)
  (title := /-- Real Matrices on a Finite Ground Set -/)
  (latexEnv := "definition")]
abbrev metric_matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

@[blueprint "def:clean-matrix"
  (statement := /-- A matrix $M$ is clean if it is symmetric, vanishes on the diagonal, and is strictly positive away from the diagonal. -/)
  (title := /-- Clean Matrix -/)
  (latexEnv := "definition")]
def clean_matrix {n : ℕ} (M : metric_matrix n) : Prop :=
  (∀ i, M i i = 0) ∧
    (∀ i j, i ≠ j → 0 < M i j) ∧
      ∀ i j, M i j = M j i

@[blueprint "def:metric-matrix-property"
  (statement := /-- A real matrix $M$ defines a metric on $[n]$ if it is clean and satisfies $M(i,k)\leq M(i,j)+M(j,k)$ for every $i,j,k\in[n]$. -/)
  (title := /-- The Metric-Matrix Property -/)
  (latexEnv := "definition")]
def metric_matrix_property {n : ℕ} (M : metric_matrix n) : Prop :=
  clean_matrix M ∧ ∀ i j k, M i k ≤ M i j + M j k

@[blueprint "def:matrix-hamming-distance"
  (statement := /-- The entrywise Hamming distance between two $n\times n$ matrices is the number of ordered pairs $(i,j)$ on which their entries differ. -/)
  (title := /-- Entrywise Hamming Distance -/)
  (latexEnv := "definition")]
noncomputable def matrix_hamming_distance {n : ℕ} (M N : metric_matrix n) : ℕ := by
  classical
  exact ((Finset.univ.product Finset.univ).filter fun p => M p.1 p.2 ≠ N p.1 p.2).card

@[blueprint "def:epsilon-far-from-metric"
  (statement := /-- For $\varepsilon\in\mathbb R$, a matrix $M$ is $\varepsilon$-far from the metric property if every metric matrix differs from $M$ in at least $\varepsilon n^2$ ordered entries. -/)
  (title := /-- Farness from the Metric Property -/)
  (latexEnv := "definition")]
def epsilon_far_from_metric {n : ℕ} (ε : ℝ) (M : metric_matrix n) : Prop :=
  ∀ N : metric_matrix n,
    metric_matrix_property N →
      ε * (n : ℝ) ^ (2 : ℕ) ≤ (matrix_hamming_distance M N : ℝ)

@[blueprint "def:violating-triangle"
  (statement := /-- A three-element subset $t\subseteq[n]$ is a violating triangle of $M$ if some ordering $i,j,k$ of its three distinct vertices satisfies $M(i,k)>M(i,j)+M(j,k)$. -/)
  (title := /-- Violating Triangle -/)
  (latexEnv := "definition")]
def violating_triangle {n : ℕ} (M : metric_matrix n) (t : Finset (Fin n)) : Prop :=
  t.card = 3 ∧
    ∃ i ∈ t, ∃ j ∈ t, ∃ k ∈ t,
      i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ M i k > M i j + M j k

@[blueprint "def:violating-triangles"
  (statement := /-- The finite set $T(M)$ consists of all violating triangles of $M$. -/)
  (title := /-- Set of Violating Triangles -/)
  (latexEnv := "definition")]
noncomputable def violating_triangles {n : ℕ} (M : metric_matrix n) : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter (violating_triangle M)

@[blueprint "def:vertex-triangle-degree"
  (statement := /-- For a family $T$ of triangles, the vertex--triangle degree $d_T(i)$ is the number of members of $T$ containing $i$. -/)
  (title := /-- Vertex--Triangle Degree -/)
  (latexEnv := "definition")]
noncomputable def vertex_triangle_degree {n : ℕ} (T : Finset (Finset (Fin n)))
    (i : Fin n) : ℕ := by
  classical
  exact (T.filter fun t => i ∈ t).card

@[blueprint "def:pair-triangle-degree"
  (statement := /-- For a family $T$ of triangles, the pair--triangle degree $d_T(i,j)$ is the number of members of $T$ containing both $i$ and $j$. -/)
  (title := /-- Pair--Triangle Degree -/)
  (latexEnv := "definition")]
noncomputable def pair_triangle_degree {n : ℕ} (T : Finset (Finset (Fin n)))
    (i j : Fin n) : ℕ := by
  classical
  exact (T.filter fun t => i ∈ t ∧ j ∈ t).card

@[blueprint "def:sampled-triangle-count"
  (statement := /-- If $s$ vertices are sampled with replacement, $X_T$ is the number of triangles in $T$ whose three vertices all occur among the samples. -/)
  (title := /-- Sampled Violating-Triangle Count -/)
  (latexEnv := "definition")]
noncomputable def sampled_triangle_count {n s : ℕ} (T : Finset (Finset (Fin n)))
    (sample : Fin s → Fin n) : ℕ := by
  classical
  exact (T.filter fun t => ∀ i ∈ t, i ∈ Finset.univ.image sample).card

@[blueprint "def:sampled-triangle-mean"
  (statement := /-- The mean of $X_T$ is its average over the uniform distribution on all functions $[s]\to[n]$. -/)
  (title := /-- Mean Sampled Triangle Count -/)
  (latexEnv := "definition")]
noncomputable def sampled_triangle_mean {n : ℕ} (T : Finset (Finset (Fin n))) (s : ℕ) : ℝ :=
  (∑ sample : Fin s → Fin n, (sampled_triangle_count T sample : ℝ)) /
    (Fintype.card (Fin s → Fin n) : ℝ)

@[blueprint "def:sampled-triangle-variance"
  (statement := /-- The variance of $X_T$ is the uniform average of $(X_T-\mathbb E X_T)^2$ over all samples $[s]\to[n]$. -/)
  (title := /-- Variance of the Sampled Triangle Count -/)
  (latexEnv := "definition")]
noncomputable def sampled_triangle_variance {n : ℕ} (T : Finset (Finset (Fin n)))
    (s : ℕ) : ℝ :=
  (∑ sample : Fin s → Fin n,
      ((sampled_triangle_count T sample : ℝ) - sampled_triangle_mean T s) ^ (2 : ℕ)) /
    (Fintype.card (Fin s → Fin n) : ℝ)

@[blueprint "def:nonadaptive-matrix-tester"
  (statement := /-- A non-adaptive randomized tester consists of a probability mass function on random seeds, a finite set of queried entries determined only by the seed, and a Boolean output determined by the values of those queried entries. -/)
  (title := /-- Non-Adaptive Randomized Matrix Tester -/)
  (latexEnv := "definition")]
structure nonadaptive_matrix_tester (n : ℕ) where
  Seed : Type
  coins : PMF Seed
  queries : Seed → Finset (Fin n × Fin n)
  output : Seed → metric_matrix n → Bool
  output_eq_of_query_eq :
    ∀ seed M N,
      (∀ p ∈ queries seed, M p.1 p.2 = N p.1 p.2) →
        output seed M = output seed N

@[blueprint "def:tester-acceptance-probability"
  (statement := /-- The acceptance probability of a tester on $M$ is the probability mass assigned to the Boolean value $\mathtt{true}$ after pushing its seed distribution through its output map. -/)
  (title := /-- Acceptance Probability -/)
  (latexEnv := "definition")]
noncomputable def tester_acceptance_probability {n : ℕ} (A : nonadaptive_matrix_tester n)
    (M : metric_matrix n) : ENNReal :=
  (A.coins.map fun seed => A.output seed M) true

@[blueprint "def:tester-rejection-probability"
  (statement := /-- The rejection probability of a tester on $M$ is the probability mass assigned to the Boolean value $\mathtt{false}$ after pushing its seed distribution through its output map. -/)
  (title := /-- Rejection Probability -/)
  (latexEnv := "definition")]
noncomputable def tester_rejection_probability {n : ℕ} (A : nonadaptive_matrix_tester n)
    (M : metric_matrix n) : ENNReal :=
  (A.coins.map fun seed => A.output seed M) false

@[blueprint "def:tester-uses-at-most"
  (statement := /-- A tester uses at most $q$ queries if every random seed produces a query set of cardinality at most $q$. -/)
  (title := /-- Worst-Case Query Bound -/)
  (latexEnv := "definition")]
def tester_uses_at_most {n : ℕ} (A : nonadaptive_matrix_tester n) (q : ℝ) : Prop :=
  ∀ seed, ((A.queries seed).card : ℝ) ≤ q

@[blueprint "def:metric-tester-guarantee"
  (statement := /-- A tester has the metric-testing guarantee at proximity $\varepsilon$ if it accepts every metric matrix with probability one and rejects every $\varepsilon$-far matrix with probability at least $2/3$. -/)
  (title := /-- One-Sided Metric-Testing Guarantee -/)
  (latexEnv := "definition")]
def metric_tester_guarantee {n : ℕ} (A : nonadaptive_matrix_tester n) (ε : ℝ) : Prop :=
  (∀ M : metric_matrix n,
      metric_matrix_property M → tester_acceptance_probability A M = 1) ∧
    ∀ M : metric_matrix n,
      epsilon_far_from_metric ε M →
        (2 : ENNReal) / 3 ≤ tester_rejection_probability A M

@[blueprint "def:clean-metric-tester-guarantee"
  (statement := /-- The clean-input guarantee has the same perfect completeness as metric testing, but requires soundness only for $\varepsilon$-far matrices that are already symmetric, positive off the diagonal, and zero on the diagonal. -/)
  (title := /-- Metric-Testing Guarantee on Clean Inputs -/)
  (latexEnv := "definition")]
def clean_metric_tester_guarantee {n : ℕ} (A : nonadaptive_matrix_tester n)
    (ε : ℝ) : Prop :=
  (∀ M : metric_matrix n,
      metric_matrix_property M → tester_acceptance_probability A M = 1) ∧
    ∀ M : metric_matrix n,
      clean_matrix M → epsilon_far_from_metric ε M →
        (2 : ENNReal) / 3 ≤ tester_rejection_probability A M

@[blueprint "def:metric-testing-query-scale"
  (statement := /-- The target query scale is $Q(n,\varepsilon)=n^{2/3}/\varepsilon^{4/3}$, with real exponentiation. -/)
  (title := /-- Metric-Testing Query Scale -/)
  (latexEnv := "definition")]
noncomputable def metric_testing_query_scale (n : ℕ) (ε : ℝ) : ℝ :=
  (n : ℝ) ^ (2 / 3 : ℝ) / ε ^ (4 / 3 : ℝ)

@[blueprint "lem:metric-repair-cover-for-many-violating-triangles"
  (statement := /-- Let $M$ be a clean real matrix. There is a metric matrix $N$ such that every ordered entry on which $M$ and $N$ differ is an ordered pair of distinct vertices contained in a violating triangle of $M$. -/)
  (proof := /-- Let $T(M)$ be the family from \cref{def:violating-triangles}. Assign a large auxiliary length to every ordered pair in the off-diagonal of a member of $T(M)$, and retain the original length on every other pair. The path pseudometric generated by these lengths is a genuine metric: positivity follows from the positive off-diagonal entries in \cref{def:clean-matrix} and finiteness, while symmetry and the triangle inequality are inherited from the path construction. If an uncovered pair were shortened, a chain of smaller total length would contain a first segment producing a strict triangle violation; one of that chain's edges would then lie in the off-diagonal of a member of $T(M)$ and have the large auxiliary length, a contradiction. Hence the resulting matrix satisfies \cref{def:metric-matrix-property} and changes only pairs covered by violating triangles. -/)
  (title := /-- Metric Repair Supported on Violating Triangles -/)
  (latexEnv := "lemma")]
lemma metric_repair_cover_for_many_violating_triangles {n : ℕ} {M : metric_matrix n}
    (hclean : clean_matrix M) :
    ∃ N : metric_matrix n,
      metric_matrix_property N ∧
        ((Finset.univ.product Finset.univ).filter fun p => M p.1 p.2 ≠ N p.1 p.2) ⊆
          (violating_triangles M).biUnion Finset.offDiag := by
  classical
  rcases hclean with ⟨hdiag, hpos, hsymm⟩
  let bad : Fin n → Fin n → Prop := fun i j =>
    (i, j) ∈ (violating_triangles M).biUnion Finset.offDiag
  let w : Fin n → Fin n → NNReal := fun i j => Real.toNNReal (M i j)
  have hMnonneg : ∀ i j, 0 ≤ M i j := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [hdiag]
    · exact (hpos i j hij).le
  have hw_coe : ∀ i j, (w i j : ℝ) = M i j := by
    intro i j
    simp [w, hMnonneg]
  have hw_self : ∀ i, w i i = 0 := by
    intro i
    exact NNReal.coe_injective (by simp [hw_coe, hdiag])
  have hw_comm : ∀ i j, w i j = w j i := by
    intro i j
    exact NNReal.coe_injective (by simp [hw_coe, hsymm])
  have hw_pos : ∀ i j, i ≠ j → 0 < w i j := by
    intro i j hij
    exact NNReal.coe_pos.mp (by simpa [hw_coe] using hpos i j hij)
  have hbad_comm : ∀ i j, bad i j ↔ bad j i := by
    intro i j
    simp only [bad, Finset.mem_biUnion, Finset.mem_offDiag]
    constructor
    · rintro ⟨t, ht, hi, hj, hij⟩
      exact ⟨t, ht, hj, hi, hij.symm⟩
    · rintro ⟨t, ht, hj, hi, hji⟩
      exact ⟨t, ht, hi, hj, hji.symm⟩
  let D : NNReal := 1 + ∑ i : Fin n, ∑ j : Fin n, w i j
  have hw_lt_D : ∀ i j, w i j < D := by
    intro i j
    have h₁ : w i j ≤ ∑ j : Fin n, w i j := by
      exact Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ j)
    have h₂ : (∑ j : Fin n, w i j) ≤ ∑ i : Fin n, ∑ j : Fin n, w i j := by
      exact Finset.single_le_sum
        (s := Finset.univ) (f := fun i' : Fin n => ∑ j : Fin n, w i' j)
        (fun _ _ => (show (0 : NNReal) ≤ _ from zero_le)) (Finset.mem_univ i)
    exact lt_of_le_of_lt (h₁.trans h₂) (by simp [D])
  have hDpos : 0 < D := by simp [D]
  let d : Fin n → Fin n → NNReal := fun i j =>
    if i = j then 0 else if bad i j then D else w i j
  have hd_self : ∀ i, d i i = 0 := by
    intro i
    simp [d]
  have hd_comm : ∀ i j, d i j = d j i := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [d]
    · simp [d, hij, Ne.symm hij, hbad_comm, hw_comm]
  have hd_pos : ∀ i j, i ≠ j → 0 < d i j := by
    intro i j hij
    by_cases hbad : bad i j
    · simpa [d, hij, hbad] using hDpos
    · simpa [d, hij, hbad] using hw_pos i j hij
  have hd_eq_of_lt : ∀ i j, d i j < D → d i j = w i j := by
    intro i j hlt
    by_cases hij : i = j
    · subst j
      simp [d, hw_self]
    · by_cases hbad : bad i j
      · simp [d, hij, hbad] at hlt
      · simp [d, hij, hbad]
  have hpath_eq : ∀ (x y : Fin n) (l : List (Fin n)),
      ((x :: l).zipWith d (l ++ [y])).sum < D →
        ((x :: l).zipWith d (l ++ [y])).sum =
          ((x :: l).zipWith w (l ++ [y])).sum := by
    intro x y l
    induction l generalizing x with
    | nil =>
        intro hlt
        simpa using hd_eq_of_lt x y (by simpa using hlt)
    | cons z l ih =>
        intro hlt
        simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons] at hlt ⊢
        have hfirst : d x z < D :=
          lt_of_le_of_lt (by exact le_add_of_nonneg_right zero_le) hlt
        have htail : ((z :: l).zipWith d (l ++ [y])).sum < D :=
          lt_of_le_of_lt (by exact le_add_of_nonneg_left zero_le) hlt
        rw [hd_eq_of_lt x z hfirst, ih z htail]
  have hbroken : ∀ (x y : Fin n) (l : List (Fin n)),
      ((x :: l).zipWith w (l ++ [y])).sum < w x y →
        D ≤ ((x :: l).zipWith d (l ++ [y])).sum := by
    intro x y l
    induction l generalizing x with
    | nil => simp
    | cons z l ih =>
        intro hlt
        simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons] at hlt ⊢
        by_cases htail : w z y ≤ ((z :: l).zipWith w (l ++ [y])).sum
        · have htri : w x y > w x z + w z y :=
            lt_of_le_of_lt (add_le_add (le_refl (w x z)) htail) hlt
          have hxz : x ≠ z := by
            intro hxz
            subst z
            simp [hw_self] at htri
          have hzy : z ≠ y := by
            intro hzy
            subst y
            simp [hw_self] at htri
          have hxy : x ≠ y := by
            intro hxy
            subst y
            simp [hw_self] at htri
          have htri' : M x y > M x z + M z y := by
            rw [← hw_coe x y, ← hw_coe x z, ← hw_coe z y]
            exact_mod_cast htri
          have ht : violating_triangle M {x, z, y} := by
            refine ⟨?_, x, by simp, z, by simp, y, by simp, hxz, hzy, hxy, htri'⟩
            simp [Finset.card_insert_of_notMem, hxz, hzy, hxy]
          have hbadxz : bad x z := by
            simp only [bad, Finset.mem_biUnion]
            refine ⟨{x, z, y}, ?_, ?_⟩
            · simpa [violating_triangles] using ht
            · simp [Finset.mem_offDiag, hxz]
          have hd_xz : d x z = D := by simp [d, hxz, hbadxz]
          rw [hd_xz]
          exact le_add_of_nonneg_right zero_le
        · have hrec := ih z (lt_of_not_ge htail)
          exact hrec.trans (le_add_of_nonneg_left zero_le)
  let P : PseudoMetricSpace (Fin n) := PseudoMetricSpace.ofPreNNDist d hd_self hd_comm
  let N : metric_matrix n := fun i j => @dist (Fin n) P.toDist i j
  have hsafe : ∀ i j, ¬bad i j → N i j = M i j := by
    intro i j hsafe
    by_cases hij : i = j
    · subst j
      simp [N, P, hdiag]
    · have hdij : d i j = w i j := by simp [d, hij, hsafe]
      apply le_antisymm
      · calc
          N i j ≤ (d i j : ℝ) := by
            simpa [N, P] using
              PseudoMetricSpace.dist_ofPreNNDist_le d hd_self hd_comm i j
          _ = M i j := by rw [hdij, hw_coe]
      · rw [← hw_coe]
        change (w i j : ℝ) ≤
          @dist (Fin n) (@PseudoMetricSpace.toDist (Fin n)
            (PseudoMetricSpace.ofPreNNDist d hd_self hd_comm)) i j
        rw [PseudoMetricSpace.dist_ofPreNNDist]
        apply NNReal.coe_le_coe.mpr
        refine le_ciInf fun l => ?_
        by_contra hnot
        have hlt : ((i :: l).zipWith d (l ++ [j])).sum < w i j := lt_of_not_ge hnot
        have hltD : ((i :: l).zipWith d (l ++ [j])).sum < D := hlt.trans (hw_lt_D i j)
        have heq := hpath_eq i j l hltD
        have hlarge := hbroken i j l (by simpa [heq] using hlt)
        exact (not_le_of_gt hltD) hlarge
  have hpositive : ∀ i j, i ≠ j → 0 < N i j := by
    intro i j hij
    let S : Finset (Fin n × Fin n) := Finset.univ.offDiag
    have hS : S.Nonempty := ⟨(i, j), by simp [S, hij]⟩
    let δ : NNReal := S.inf' hS (fun p => d p.1 p.2)
    have hδpos : 0 < δ := by
      obtain ⟨p, hp, hpδ⟩ := Finset.exists_mem_eq_inf' hS (fun p => d p.1 p.2)
      have hpδ' : δ = d p.1 p.2 := by simpa [δ] using hpδ
      rw [hpδ']
      exact hd_pos p.1 p.2 (by simpa [S] using hp)
    have hpath_lower : ∀ (x y : Fin n) (l : List (Fin n)), x ≠ y →
        δ ≤ ((x :: l).zipWith d (l ++ [y])).sum := by
      intro x y l
      induction l generalizing x with
      | nil =>
          intro hxy
          have hmem : (x, y) ∈ S := by simp [S, hxy]
          have hmin : δ ≤ d x y := by
            change S.inf' hS (fun p => d p.1 p.2) ≤ d x y
            exact Finset.inf'_le (f := fun p : Fin n × Fin n => d p.1 p.2) hmem
          simpa using hmin
      | cons z l ih =>
          intro hxy
          simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons]
          by_cases hxz : x = z
          · subst z
            simpa [hd_self] using ih x hxy
          · have hmem : (x, z) ∈ S := by simp [S, hxz]
            have hmin : δ ≤ d x z := by
                change S.inf' hS (fun p => d p.1 p.2) ≤ d x z
                exact Finset.inf'_le (f := fun p : Fin n × Fin n => d p.1 p.2)
                  hmem
            exact hmin.trans (le_add_of_nonneg_right zero_le)
    change 0 <
      @dist (Fin n) (@PseudoMetricSpace.toDist (Fin n)
        (PseudoMetricSpace.ofPreNNDist d hd_self hd_comm)) i j
    rw [PseudoMetricSpace.dist_ofPreNNDist]
    exact NNReal.coe_pos.mpr <| lt_of_lt_of_le hδpos <| le_ciInf fun l => hpath_lower i j l hij
  refine ⟨N, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · constructor
      · intro i
        simp [N, P]
      · constructor
        · exact hpositive
        · intro i j
          simpa [N, P] using P.dist_comm i j
    · intro i j k
      simpa [N, P] using P.dist_triangle i j k
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp
    by_contra hnot
    exact hp.2 (hsafe p.1 p.2 hnot).symm

@[blueprint "lem:many-violating-triangles"
  (statement := /-- Let $n\in\mathbb N$ and $\varepsilon\in\mathbb R$ satisfy $0<\varepsilon<1$, and let $M$ be a symmetric $n\times n$ real matrix that vanishes on the diagonal and is strictly positive off the diagonal. If every metric $n\times n$ real matrix differs from $M$ in at least $\varepsilon n^2$ ordered entries, then there are at least $\varepsilon n^2/6$ three-element vertex sets $t$ for which some ordering $i,j,k$ of the vertices of $t$ satisfies $M(i,k)>M(i,j)+M(j,k)$. -/)
  (proof := /-- Apply \cref{lem:metric-repair-cover-for-many-violating-triangles} to obtain a metric matrix $N$ whose changed ordered entries are covered by the off-diagonals of the violating triangles. Each such triangle has three vertices and therefore six ordered off-diagonal pairs, so the union bound and \cref{def:matrix-hamming-distance} give $d_{\ell_0}(M,N)\leq 6|T(M)|$. On the other hand, \cref{def:epsilon-far-from-metric} gives $\varepsilon n^2\leq d_{\ell_0}(M,N)$. Dividing the resulting inequality by $6$ proves the claim. -/)
  (title := /-- Many Violating Triangles in a Far Matrix -/)
  (latexEnv := "lemma")]
lemma many_violating_triangles {n : ℕ} {ε : ℝ} {M : metric_matrix n}
    (hε₀ : 0 < ε) (hε₁ : ε < 1) (hclean : clean_matrix M)
    (hfar : epsilon_far_from_metric ε M) :
    ε * (n : ℝ) ^ (2 : ℕ) / 6 ≤ (violating_triangles M).card := by
  classical
  obtain ⟨N, hN, hsupport⟩ := metric_repair_cover_for_many_violating_triangles hclean
  have hdist := hfar N hN
  have hcard : matrix_hamming_distance M N ≤ 6 * (violating_triangles M).card := by
    rw [matrix_hamming_distance]
    calc
      ((Finset.univ.product Finset.univ).filter fun p => M p.1 p.2 ≠ N p.1 p.2).card ≤
          ((violating_triangles M).biUnion Finset.offDiag).card :=
        Finset.card_le_card hsupport
      _ ≤ ∑ t ∈ violating_triangles M, t.offDiag.card := Finset.card_biUnion_le
      _ = ∑ _t ∈ violating_triangles M, 6 := by
        apply Finset.sum_congr rfl
        intro t ht
        have ht' : violating_triangle M t := by
          simpa [violating_triangles] using ht
        simp [Finset.offDiag_card, ht'.1]
      _ = 6 * (violating_triangles M).card := by simp [Nat.mul_comm]
  have hcard' : (matrix_hamming_distance M N : ℝ) ≤ 6 * (violating_triangles M).card := by
    exact_mod_cast hcard
  linarith

@[blueprint "lem:finite-interval-omission-selection"
  (statement := /-- Let \(S\) be a finite set, and for each \(k\in S\) let
  \(I_k=[\ell_k,u_k]\) be a nonempty closed interval with \(u_k>0\). Fix a
  positive integer \(q\). If every \(x>0\) is omitted by at least \(q\) of the
  intervals, then there are \(x>0\) and disjoint subfamilies \(L,R\subseteq S\)
  such that
  \[
    |L|=\left\lceil\frac q2\right\rceil,\qquad
    |R|=\left\lfloor\frac q2\right\rfloor,
  \]
  every interval indexed by \(L\) has right endpoint at most \(x\), every
  interval indexed by \(R\) has left endpoint greater than \(x\), and fewer
  than \(\lceil q/2\rceil\) intervals have right endpoint strictly less than
  \(x\). -/)
  (proof := /-- Order the multiset of right endpoints \(u_k\), with
  multiplicity indexed by \(S\), and take \(x\) to be the
  \(\lceil q/2\rceil\)-th endpoint. The positivity of every \(u_k\) gives
  \(x>0\). By the defining order-statistic inequalities, at least
  \(\lceil q/2\rceil\) endpoints are at most \(x\), whereas fewer than
  \(\lceil q/2\rceil\) are strictly smaller; choose \(L\) from the former
  indices. At least \(q\) intervals omit \(x\). Any such interval not lying
  strictly to the left of \(x\) must have left endpoint greater than \(x\),
  because its endpoints are ordered. Removing the fewer than
  \(\lceil q/2\rceil\) intervals lying strictly to the left leaves at least
  \(\lfloor q/2\rfloor\) intervals strictly to the right; choose \(R\) among
  them. The inequalities \(u_k\leq x<\ell_{k'}\) show that \(L\) and \(R\)
  are disjoint and establish every asserted invariant. -/)
  (title := /-- Finite Interval Omission Selection -/)
  (latexEnv := "lemma")]
lemma finite_interval_omission_selection {α : Type*} [DecidableEq α]
    (S : Finset α) (lower upper : α → ℝ) (q : ℕ)
    (hq : 0 < q)
    (hupper : ∀ k ∈ S, 0 < upper k)
    (hordered : ∀ k ∈ S, lower k ≤ upper k)
    (homit : ∀ x : ℝ, 0 < x →
      q ≤ (S.filter fun k => x < lower k ∨ upper k < x).card) :
    ∃ x : ℝ, 0 < x ∧
      ∃ L R : Finset α,
        L ⊆ S ∧ R ⊆ S ∧ Disjoint L R ∧
          L.card = (q + 1) / 2 ∧ R.card = q / 2 ∧
            (∀ k ∈ L, upper k ≤ x) ∧
              (∀ k ∈ R, x < lower k) ∧
                (S.filter fun k => upper k < x).card < (q + 1) / 2 := by
  classical
  let m := (q + 1) / 2
  have hmpos : 0 < m := by
    dsimp [m]
    omega
  have hqS : q ≤ S.card := by
    exact (homit 1 zero_lt_one).trans (Finset.card_filter_le _ _)
  have hmS : m ≤ S.card := by
    dsimp [m]
    omega
  have hSne : S.Nonempty := Finset.card_pos.mp (hq.trans_le hqS)
  let U := S.image upper
  have hUne : U.Nonempty := hSne.image upper
  let xmax := U.max' hUne
  have hxmaxU : xmax ∈ U := by
    exact U.max'_mem hUne
  have hbelowMax : ∀ k ∈ S, upper k ≤ xmax := by
    intro k hk
    exact U.le_max' (upper k) (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
  let G := U.filter fun y => m ≤ (S.filter fun k => upper k ≤ y).card
  have hxmaxG : xmax ∈ G := by
    rw [Finset.mem_filter]
    refine ⟨hxmaxU, ?_⟩
    have heq : S.filter (fun k => upper k ≤ xmax) = S := by
      exact Finset.filter_eq_self.mpr hbelowMax
    simpa [heq] using hmS
  have hGne : G.Nonempty := ⟨xmax, hxmaxG⟩
  let x := G.min' hGne
  have hxG : x ∈ G := G.min'_mem hGne
  have hxU : x ∈ U := (Finset.mem_filter.mp hxG).1
  have hmx : m ≤ (S.filter fun k => upper k ≤ x).card :=
    (Finset.mem_filter.mp hxG).2
  have hxpos : 0 < x := by
    rcases Finset.mem_image.mp hxU with ⟨k, hk, hkx⟩
    rw [← hkx]
    exact hupper k hk
  let T := S.filter fun k => upper k < x
  have hTsmall : T.card < m := by
    by_contra hnot
    have hmT : m ≤ T.card := Nat.le_of_not_gt hnot
    have hTne : T.Nonempty := Finset.card_pos.mp (hmpos.trans_le hmT)
    let V := T.image upper
    have hVne : V.Nonempty := hTne.image upper
    let y := V.max' hVne
    have hyV : y ∈ V := V.max'_mem hVne
    have hyx : y < x := by
      rcases Finset.mem_image.mp hyV with ⟨k, hkT, hky⟩
      rw [← hky]
      exact (Finset.mem_filter.mp hkT).2
    have hTV : ∀ k ∈ T, upper k ≤ y := by
      intro k hkT
      exact V.le_max' (upper k) (Finset.mem_image.mpr ⟨k, hkT, rfl⟩)
    have hTsub : T ⊆ S.filter fun k => upper k ≤ y := by
      intro k hkT
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hkT).1, hTV k hkT⟩
    have hyU : y ∈ U := by
      rcases Finset.mem_image.mp hyV with ⟨k, hkT, hky⟩
      rw [← hky]
      exact Finset.mem_image.mpr ⟨k, (Finset.mem_filter.mp hkT).1, rfl⟩
    have hyG : y ∈ G := by
      rw [Finset.mem_filter]
      exact ⟨hyU, hmT.trans (Finset.card_le_card hTsub)⟩
    have hxy : x ≤ y := G.min'_le y hyG
    exact (not_lt_of_ge hxy) hyx
  obtain ⟨L, hLsub, hLcard⟩ := Finset.exists_subset_card_eq hmx
  let R₀ := S.filter fun k => x < lower k
  have hdisjTR : Disjoint R₀ T := by
    refine Finset.disjoint_left.mpr ?_
    intro k hkR hkT
    have hkS := (Finset.mem_filter.mp hkR).1
    have hkright := (Finset.mem_filter.mp hkR).2
    have hkleft := (Finset.mem_filter.mp hkT).2
    exact (not_lt_of_ge (hordered k hkS)) (hkleft.trans hkright)
  have hqsplit : q ≤ R₀.card + T.card := by
    calc
      q ≤ (S.filter fun k => x < lower k ∨ upper k < x).card := homit x hxpos
      _ = R₀.card + T.card := by
        rw [Finset.filter_or, Finset.card_union_of_disjoint hdisjTR]
  have hqR : q / 2 ≤ R₀.card := by
    dsimp [m] at hTsmall
    omega
  obtain ⟨R, hRsub, hRcard⟩ := Finset.exists_subset_card_eq hqR
  refine ⟨x, hxpos, L, R, ?_, ?_, ?_, hLcard, hRcard, ?_, ?_, ?_⟩
  · exact hLsub.trans (Finset.filter_subset _ _)
  · exact hRsub.trans (Finset.filter_subset _ _)
  · refine Finset.disjoint_left.mpr ?_
    intro k hkL hkR
    have hkS : k ∈ S := (hLsub.trans (Finset.filter_subset _ _)) hkL
    have hku := (Finset.mem_filter.mp (hLsub hkL)).2
    have hkl := (Finset.mem_filter.mp (hRsub hkR)).2
    exact (not_lt_of_ge (hordered k hkS)) (hku.trans_lt hkl)
  · intro k hkL
    exact (Finset.mem_filter.mp (hLsub hkL)).2
  · intro k hkR
    exact (Finset.mem_filter.mp (hRsub hkR)).2
  · simpa [T, m] using hTsmall

@[blueprint "lem:heavy-pair-bucket-embedding"
  (statement := /-- Let \(B\) be a finite set of bucket labels and let \(S,U\)
  be finite sets. Suppose every member of \(S\) is either fixed or is assigned
  to one label in \(B\). For \(e\in B\), let \(C_e\subseteq U\) be its
  candidate set. Assume that each bucket has at most \(K\) members, each
  \(C_e\) has at least \(K+R\) members, fixed members lie in \(U\) and in no
  \(C_e\), two distinct candidate sets meet in at most one point, and each
  candidate set meets candidate sets belonging to at most \(R\) other labels.
  Then there is an injection of \(S\) into \(U\) which fixes every fixed
  member and maps the \(e\)-bucket into \(C_e\). -/)
  (proof := /-- First observe that, for \(e\in B\) and
  \(E\subseteq B\setminus\{e\}\),
  \[
    \left|C_e\cap\bigcup_{e'\in E}C_{e'}\right|\leq R.
  \]
  The intersection on the left is covered by the sets
  \(C_e\cap C_{e'}\) for those \(e'\in E\) that conflict with \(e\).
  Each such set has cardinality at most one, and the conflict hypothesis
  permits at most \(R\) such labels.

  We now induct on \(B\). If \(B\) is empty, every member of \(S\) is
  fixed, so the identity map has all the required properties. For the
  induction step write \(B=E\cup\{e\}\), with \(e\notin E\), and let
  \(S_0\) consist of the members whose owner is not \(e\). All hypotheses
  restrict from \(B,S\) to \(E,S_0\), so the induction hypothesis gives
  an admissible injection \(\varphi_0\) on \(S_0\). Put
  \(V=\varphi_0(S_0)\).

  We claim that \(|C_e\cap V|\leq R\). A fixed member of \(S_0\) is
  mapped to itself and cannot lie in \(C_e\) by the disjointness hypothesis.
  Every other member has an owner \(e'\in E\), and its image lies in
  \(C_{e'}\). Consequently
  \[
    C_e\cap V\subseteq C_e\cap\bigcup_{e'\in E}C_{e'},
  \]
  and the preliminary bound proves the claim. Hence
  \[
    |C_e\setminus V|\geq (K+R)-R=K.
  \]
  Since the \(e\)-bucket has cardinality at most \(K\), choose an injection
  from that bucket into \(C_e\setminus V\), and combine it with
  \(\varphi_0\). The two images are disjoint by construction, so the
  combined map is injective on \(S\). It fixes every fixed member, sends
  every owned member into its owner's candidate set, and has image in \(U\)
  because fixed members and all candidate sets lie in \(U\). -/)
  (title := /-- Collision-Free Embedding of Heavy-Pair Buckets -/)
  (latexEnv := "lemma")]
lemma heavy_pair_bucket_embedding {α β : Type*} [DecidableEq α] [DecidableEq β]
    (B : Finset α) (S U : Finset β) (owner : β → Option α)
    (candidate : α → Finset β) (K R : ℕ)
    (howner : ∀ x ∈ S,
      owner x = none ∨ ∃ e ∈ B, owner x = some e)
    (hfixed : ∀ x ∈ S, owner x = none → x ∈ U)
    (hbucket : ∀ e ∈ B,
      (S.filter fun x => owner x = some e).card ≤ K)
    (hcandidate : ∀ e ∈ B, K + R ≤ (candidate e).card)
    (hcandidateU : ∀ e ∈ B, candidate e ⊆ U)
    (hfixed_disjoint : ∀ e ∈ B,
      Disjoint (S.filter fun x => owner x = none) (candidate e))
    (hpairwise : ∀ e ∈ B, ∀ e' ∈ B, e ≠ e' →
      (candidate e ∩ candidate e').card ≤ 1)
    (hconflicts : ∀ e ∈ B,
      (B.filter fun e' =>
        e' ≠ e ∧ (candidate e ∩ candidate e').Nonempty).card ≤ R) :
    ∃ φ : β → β,
      Set.InjOn φ (↑S : Set β) ∧
        (∀ x ∈ S, owner x = none → φ x = x) ∧
          (∀ x ∈ S, ∀ e ∈ B, owner x = some e → φ x ∈ candidate e) ∧
            Finset.image φ S ⊆ U := by
  classical
  have hintersection (e : α) (heB : e ∈ B) (E : Finset α)
      (hEB : E ⊆ B) (heE : e ∉ E) :
      (candidate e ∩ E.biUnion candidate).card ≤ R := by
    let C := E.filter fun e' => (candidate e ∩ candidate e').Nonempty
    have hsub :
        candidate e ∩ E.biUnion candidate ⊆
          C.biUnion fun e' => candidate e ∩ candidate e' := by
      intro x hx
      rw [Finset.mem_inter] at hx
      rcases Finset.mem_biUnion.mp hx.2 with ⟨e', he'E, hxe'⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨e', ?_, Finset.mem_inter.mpr ⟨hx.1, hxe'⟩⟩
      exact Finset.mem_filter.mpr
        ⟨he'E, ⟨x, Finset.mem_inter.mpr ⟨hx.1, hxe'⟩⟩⟩
    calc
      (candidate e ∩ E.biUnion candidate).card ≤
          (C.biUnion fun e' => candidate e ∩ candidate e').card :=
        Finset.card_le_card hsub
      _ ≤ ∑ e' ∈ C, (candidate e ∩ candidate e').card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _e' ∈ C, 1 := by
        apply Finset.sum_le_sum
        intro e' he'C
        have he'E : e' ∈ E := (Finset.mem_filter.mp he'C).1
        apply hpairwise e heB e' (hEB he'E)
        intro heq
        subst e'
        exact heE he'E
      _ = C.card := by simp
      _ ≤ (B.filter fun e' =>
          e' ≠ e ∧ (candidate e ∩ candidate e').Nonempty).card := by
        apply Finset.card_le_card
        intro e' he'C
        rcases Finset.mem_filter.mp he'C with ⟨he'E, hinter⟩
        apply Finset.mem_filter.mpr
        refine ⟨hEB he'E, ?_, hinter⟩
        intro heq
        subst e'
        exact heE he'E
      _ ≤ R := hconflicts e heB
  induction B using Finset.induction_on generalizing S with
  | empty =>
      refine ⟨id, ?_, ?_, ?_, ?_⟩
      · intro x hx y hy hxy
        exact hxy
      · intro x hx hnone
        rfl
      · intro x hx e he
        simp at he
      · intro y hy
        rcases Finset.mem_image.mp hy with ⟨x, hxS, rfl⟩
        rcases howner x hxS with hnone | howned
        · exact hfixed x hxS hnone
        · rcases howned with ⟨e, he, hxe⟩
          simp at he
  | @insert e E heE ih =>
      let S₀ := S.filter fun x => owner x ≠ some e
      have howner₀ : ∀ x ∈ S₀,
          owner x = none ∨ ∃ e' ∈ E, owner x = some e' := by
        intro x hx
        have hxS := (Finset.mem_filter.mp hx).1
        have hxne := (Finset.mem_filter.mp hx).2
        rcases howner x hxS with hnone | ⟨e', he', hxe'⟩
        · exact Or.inl hnone
        · rcases Finset.mem_insert.mp he' with rfl | he'E
          · exact False.elim (hxne hxe')
          · exact Or.inr ⟨e', he'E, hxe'⟩
      have hfixed₀ : ∀ x ∈ S₀, owner x = none → x ∈ U := by
        intro x hx
        exact hfixed x (Finset.mem_filter.mp hx).1
      have hbucket₀ : ∀ e' ∈ E,
          (S₀.filter fun x => owner x = some e').card ≤ K := by
        intro e' he'
        apply le_trans (Finset.card_le_card ?_) (hbucket e' (by simp [he']))
        intro x hx
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1,
            (Finset.mem_filter.mp hx).2⟩
      have hcandidate₀ : ∀ e' ∈ E, K + R ≤ (candidate e').card := by
        intro e' he'
        exact hcandidate e' (by simp [he'])
      have hcandidateU₀ : ∀ e' ∈ E, candidate e' ⊆ U := by
        intro e' he'
        exact hcandidateU e' (by simp [he'])
      have hfixed_disjoint₀ : ∀ e' ∈ E,
          Disjoint (S₀.filter fun x => owner x = none) (candidate e') := by
        intro e' he'
        apply Finset.disjoint_left.mpr
        intro x hxfix hxcand
        exact (Finset.disjoint_left.mp (hfixed_disjoint e' (by simp [he'])))
          (Finset.mem_filter.mpr
            ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hxfix).1).1,
              (Finset.mem_filter.mp hxfix).2⟩)
          hxcand
      have hpairwise₀ : ∀ e' ∈ E, ∀ e'' ∈ E, e' ≠ e'' →
          (candidate e' ∩ candidate e'').card ≤ 1 := by
        intro e' he' e'' he'' hne
        exact hpairwise e' (by simp [he']) e'' (by simp [he'']) hne
      have hconflicts₀ : ∀ e' ∈ E,
          (E.filter fun e'' =>
            e'' ≠ e' ∧ (candidate e' ∩ candidate e'').Nonempty).card ≤ R := by
        intro e' he'
        apply le_trans (Finset.card_le_card ?_) (hconflicts e' (by simp [he']))
        intro e'' he''
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_insert_of_mem (Finset.mem_filter.mp he'').1,
            (Finset.mem_filter.mp he'').2⟩
      obtain ⟨φ₀, hφ₀inj, hφ₀fixed, hφ₀candidate, hφ₀U⟩ :=
        ih S₀ howner₀ hfixed₀ hbucket₀ hcandidate₀ hcandidateU₀
          hfixed_disjoint₀ hpairwise₀ hconflicts₀ (by
            intro e' he' E' hE' he'E'
            apply hintersection e' (by simp [he']) E'
            · intro z hz
              simp [hE' hz]
            · exact he'E')
      let V := Finset.image φ₀ S₀
      have hinter_used : (candidate e ∩ V).card ≤ R := by
        apply le_trans (Finset.card_le_card ?_)
          (hintersection e (by simp) E (by simp) heE)
        intro y hy
        rcases Finset.mem_inter.mp hy with ⟨hycand, hyV⟩
        rcases Finset.mem_image.mp hyV with ⟨x, hxS₀, rfl⟩
        have hxS := (Finset.mem_filter.mp hxS₀).1
        have hxne := (Finset.mem_filter.mp hxS₀).2
        apply Finset.mem_inter.mpr
        refine ⟨hycand, ?_⟩
        rcases howner x hxS with hnone | ⟨e', he', hxe'⟩
        · have hxfix : x ∈ S.filter fun z => owner z = none :=
            Finset.mem_filter.mpr ⟨hxS, hnone⟩
          have hxcand : x ∈ candidate e := by
            simpa [hφ₀fixed x hxS₀ hnone] using hycand
          exact False.elim
            ((Finset.disjoint_left.mp (hfixed_disjoint e (by simp)))
              hxfix hxcand)
        · rcases Finset.mem_insert.mp he' with rfl | he'E
          · exact False.elim (hxne hxe')
          · apply Finset.mem_biUnion.mpr
            refine ⟨e', he'E, ?_⟩
            exact hφ₀candidate x hxS₀ e' he'E hxe'
      let Q := S.filter fun x => owner x = some e
      let A := candidate e \ V
      have hQA : Fintype.card ↥Q ≤ A.card := by
        have hq := hbucket e (by simp)
        change Q.card ≤ K at hq
        have hc := hcandidate e (by simp)
        rw [Fintype.card_coe, Finset.card_sdiff]
        rw [Finset.inter_comm V (candidate e)]
        apply le_trans hq
        apply Nat.le_sub_of_add_le
        omega
      obtain ⟨g, hg⟩ := Function.Embedding.exists_of_card_le_finset hQA
      have hgmem (x : ↥Q) : g x ∈ A :=
        hg ⟨x, rfl⟩
      let φ : β → β := fun x =>
        if hx : x ∈ Q then g ⟨x, hx⟩ else φ₀ x
      refine ⟨φ, ?_, ?_, ?_, ?_⟩
      · intro x hxS y hyS hxy
        simp only [Finset.mem_coe] at hxS hyS
        by_cases hxQ : x ∈ Q
        · by_cases hyQ : y ∈ Q
          · have hsubeq : (⟨x, hxQ⟩ : ↥Q) = ⟨y, hyQ⟩ := by
              apply g.injective
              simpa [φ, hxQ, hyQ] using hxy
            exact congrArg Subtype.val hsubeq
          · have hyS₀ : y ∈ S₀ := by
              apply Finset.mem_filter.mpr
              refine ⟨hyS, ?_⟩
              intro hyowner
              exact hyQ (Finset.mem_filter.mpr ⟨hyS, hyowner⟩)
            have hgyA := hgmem ⟨x, hxQ⟩
            have hgyV : g ⟨x, hxQ⟩ ∈ V := by
              apply Finset.mem_image.mpr
              refine ⟨y, hyS₀, ?_⟩
              simpa [φ, hxQ, hyQ] using hxy.symm
            exact False.elim ((Finset.mem_sdiff.mp hgyA).2 hgyV)
        · by_cases hyQ : y ∈ Q
          · have hxS₀ : x ∈ S₀ := by
              apply Finset.mem_filter.mpr
              refine ⟨hxS, ?_⟩
              intro hxowner
              exact hxQ (Finset.mem_filter.mpr ⟨hxS, hxowner⟩)
            have hgyA := hgmem ⟨y, hyQ⟩
            have hgyV : g ⟨y, hyQ⟩ ∈ V := by
              apply Finset.mem_image.mpr
              refine ⟨x, hxS₀, ?_⟩
              simpa [φ, hxQ, hyQ] using hxy
            exact False.elim ((Finset.mem_sdiff.mp hgyA).2 hgyV)
          · apply hφ₀inj
            · exact Finset.mem_filter.mpr
                ⟨hxS, fun hxowner =>
                  hxQ (Finset.mem_filter.mpr ⟨hxS, hxowner⟩)⟩
            · exact Finset.mem_filter.mpr
                ⟨hyS, fun hyowner =>
                  hyQ (Finset.mem_filter.mpr ⟨hyS, hyowner⟩)⟩
            · simpa [φ, hxQ, hyQ] using hxy
      · intro x hxS hxowner
        have hxQ : x ∉ Q := by
          simp [Q, hxowner]
        have hxS₀ : x ∈ S₀ :=
          Finset.mem_filter.mpr ⟨hxS, by simp [hxowner]⟩
        have hfix := hφ₀fixed x hxS₀ hxowner
        simpa [φ, hxQ] using hfix
      · intro x hxS e' he' hxowner
        rcases Finset.mem_insert.mp he' with rfl | he'E
        · have hxQ : x ∈ Q := Finset.mem_filter.mpr ⟨hxS, hxowner⟩
          have hxA := hgmem ⟨x, hxQ⟩
          simpa [φ, hxQ] using (Finset.mem_sdiff.mp hxA).1
        · have hene : e' ≠ e := by
            intro heq
            subst e'
            exact heE he'E
          have hxQ : x ∉ Q := by
            intro hx
            have heq : some e' = some e := by
              rw [← hxowner]
              exact (Finset.mem_filter.mp hx).2
            exact hene (Option.some.inj heq)
          have hxS₀ : x ∈ S₀ :=
            Finset.mem_filter.mpr
              ⟨hxS, by simpa [hxowner] using hene⟩
          have hcand := hφ₀candidate x hxS₀ e' he'E hxowner
          simpa [φ, hxQ] using hcand
      · intro y hy
        rcases Finset.mem_image.mp hy with ⟨x, hxS, rfl⟩
        by_cases hxQ : x ∈ Q
        · apply hcandidateU e (by simp)
          have hxA := hgmem ⟨x, hxQ⟩
          simpa [φ, hxQ] using (Finset.mem_sdiff.mp hxA).1
        · apply hφ₀U
          apply Finset.mem_image.mpr
          refine ⟨x, ?_, by simp [φ, hxQ]⟩
          exact Finset.mem_filter.mpr
            ⟨hxS, fun hxowner =>
              hxQ (Finset.mem_filter.mpr ⟨hxS, hxowner⟩)⟩

@[blueprint "lem:heavy-pair-simultaneous-replacement-data"
  (statement := /-- Let \(0<\varepsilon<1\), let \(n\geq1\), let \(M\) be a clean
  matrix that is
  \(\varepsilon/2\)-far from the metric property, and suppose that every vertex
  belongs to at most \(h\) violating triangles, where
  \[
    h\leq \frac{\varepsilon^{1/3}n^{4/3}}{16}.
  \]
  Put \(D=10n^{2/3}/\varepsilon^{1/3}\). There exist a clean matrix \(M_2\)
  that is \(19\varepsilon/40\)-far from the metric property, a family \(H\) of
  heavy pairs, an owner map on the violating triangles of \(M_2\), and an
  injection \(\varphi:T(M_2)\to T(M)\) with the following properties. Every
  nonheavy pair has degree at most \(D\) in \(T(M)\); a triangle owned by
  \(e\in H\) is mapped to a triangle containing \(e\); fewer than
  \(201D/400\) triangles are owned by any fixed \(e\); and fewer than \(D/400\)
  triangles owned by other pairs have images containing \(e\). -/)
  (proof := /-- Let \(H\) consist of the two-element sets \(e=\{i,j\}\) whose
  degree in \(T(M)\), as defined in \cref{def:pair-triangle-degree}, exceeds
  \(D\). If \(D\geq n\), take \(H=\varnothing\), \(M_2=M\), the identity
  injection, and the constantly empty owner map; a pair belongs to at most
  \(n\) three-element sets, and all asserted bucket bounds are vacuous. Assume
  henceforth that \(D<n\).

  For every vertex \(i\), double-counting incidences between the triangles
  through \(i\) and their two incident pairs gives
  \[
    \frac D2\deg_H(i)<d_{T(M)}(i)\leq h.
  \]
  Thus \(\deg_H(i)<a:=\varepsilon^{2/3}n^{2/3}/80\), so fewer than \(2a\)
  heavy pairs meet a fixed heavy pair. Cubing \(D<n\), using
  \(0<\varepsilon<1\), gives \(\varepsilon n>1000\). Summing the degree bound
  in \(H\) and dividing by two yields \(2|H|\leq\varepsilon n^2/40\).

  Fix \(e=\{i,j\}\in H\). For each \(k\notin\{i,j\}\) such that neither
  \(\{i,k\}\) nor \(\{j,k\}\) is heavy, consider
  \[
    I_{e,k}=[\,|M(i,k)-M(j,k)|,\ M(i,k)+M(j,k)\,].
  \]
  There is \(x_e>0\) omitted by fewer than \(D/2\) of these intervals. If
  not, apply \cref{lem:finite-interval-omission-selection} with
  \(q=\lceil D/2\rceil\). It gives two collections, of sizes at least \(D/4\)
  and \(D/5\), such that every interval in the first lies strictly to the left
  of every interval in the second. For their third vertices \(k,\ell\), the
  separation inequality forces either \(\{i,k,\ell\}\) or
  \(\{j,k,\ell\}\) to be in \(T(M)\). Distinct pairs \(\{k,\ell\}\) yield
  distinct triangles, so \(i\) or \(j\) has degree at least \(D^2/50>h\), a
  contradiction.

  Define \(M_2\) in one step by replacing both entries on every \(e\in H\)
  by \(x_e\) and retaining all other entries. The intervals for \(e\) involve
  only nonheavy entries, hence entries never replaced; consequently their
  omission bounds hold simultaneously. The positive symmetric replacements
  preserve \cref{def:clean-matrix}. Moreover, \(M_2\) differs from \(M\) on
  at most \(2|H|\leq\varepsilon n^2/40\) ordered entries. The triangle
  inequality for \cref{def:matrix-hamming-distance}, together with
  \cref{def:epsilon-far-from-metric}, shows that \(M_2\) is
  \(19\varepsilon/40\)-far.

  Order \(H\). Give a member of \(T(M_2)\) containing a heavy pair to its
  first such pair, and leave a triangle containing no heavy pair unowned. A
  bucket for \(e\) has fewer than \(D/2+2a<201D/400\) members: those whose
  other two pairs are nonheavy are counted by intervals omitting \(x_e\), and
  every remaining member determines a heavy pair adjacent to \(e\). For
  \(e\in H\), let its candidates be the members of \(T(M)\) containing \(e\).
  There are more than \(D\) candidates. Candidate families for two distinct
  heavy pairs intersect in at most one triangle, and only adjacent heavy pairs
  have a common candidate. Let \(K\) be the maximum bucket cardinality and
  let \(R\) be the maximum number of heavy pairs conflicting with a fixed
  heavy pair. The preceding estimates give
  \(K+R<202D/400<D\), so the integral candidate cardinalities are at least
  \(K+R\). The fixed unowned triangles lie in \(T(M)\) and in no candidate
  family. Hence \cref{lem:heavy-pair-bucket-embedding} gives an injection
  \(\varphi:T(M_2)\to T(M)\) that fixes unowned triangles and sends each owned
  triangle into its owner's candidate family.

  Finally fix \(e\in H\). An image containing \(e\) whose source has a
  different owner must come from the bucket of a heavy pair adjacent to \(e\).
  Two distinct pairs determine at most one three-element set, and fewer than
  \(2a<D/400\) heavy pairs are adjacent to \(e\). This proves the foreign-image
  bound and completes all the asserted invariants. -/)
  (title := /-- Data for Simultaneous Heavy-Pair Replacement -/)
  (latexEnv := "lemma")]
lemma heavy_pair_simultaneous_replacement_data {n : ℕ} {ε : ℝ}
    {M : metric_matrix n} (hn : 0 < n) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hclean : clean_matrix M)
    (hfar : epsilon_far_from_metric (ε / 2) M) (h : ℕ)
    (hh : (h : ℝ) ≤
      ε ^ (1 / 3 : ℝ) * (n : ℝ) ^ (4 / 3 : ℝ) / 16)
    (hdegree : ∀ i, vertex_triangle_degree (violating_triangles M) i ≤ h) :
    ∃ D : ℝ,
      D = 10 * (n : ℝ) ^ (2 / 3 : ℝ) / ε ^ (1 / 3 : ℝ) ∧
      ∃ M₂ : metric_matrix n,
      ∃ H : Finset (Finset (Fin n)),
        ∃ owner : Finset (Fin n) → Option (Finset (Fin n)),
          ∃ φ : Finset (Fin n) → Finset (Fin n),
            clean_matrix M₂ ∧
              epsilon_far_from_metric (19 * ε / 40) M₂ ∧
                Set.InjOn φ (↑(violating_triangles M₂) : Set (Finset (Fin n))) ∧
                  Finset.image φ (violating_triangles M₂) ⊆ violating_triangles M ∧
                    0 < D ∧
                      (∀ i j, i ≠ j → ({i, j} : Finset (Fin n)) ∉ H →
                        (pair_triangle_degree (violating_triangles M) i j : ℝ) ≤ D) ∧
                        (∀ t ∈ violating_triangles M₂, ∀ e ∈ H,
                          owner t = some e → e ⊆ φ t) ∧
                          (∀ e ∈ H,
                            (((violating_triangles M₂).filter fun t =>
                              owner t = some e).card : ℝ) < 201 * D / 400) ∧
                            ∀ e ∈ H,
                              (((violating_triangles M₂).filter fun t =>
                                owner t ≠ some e ∧ e ⊆ φ t).card : ℝ) < D / 400 := by
  classical
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = ε ^ (1 / 3 : ℝ) := ⟨_, rfl⟩
  obtain ⟨v, hvdef⟩ : ∃ v : ℝ, v = (n : ℝ) ^ (1 / 3 : ℝ) := ⟨_, rfl⟩
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hu0 : 0 < u := by rw [hudef]; exact Real.rpow_pos_of_pos hε₀ _
  have hu1 : u < 1 := by rw [hudef]; exact Real.rpow_lt_one hε₀.le hε₁ (by norm_num)
  have hv1 : (1 : ℝ) ≤ v := by
    rw [hvdef]
    exact Real.one_le_rpow hnR (by norm_num)
  have hu3 : u ^ (3 : ℕ) = ε := by
    rw [hudef, ← Real.rpow_natCast (ε ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul hε₀.le]
    norm_num
  have hv3 : v ^ (3 : ℕ) = (n : ℝ) := by
    rw [hvdef, ← Real.rpow_natCast ((n : ℝ) ^ (1 / 3 : ℝ)) 3,
      ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  have hn23 : (n : ℝ) ^ (2 / 3 : ℝ) = v ^ (2 : ℕ) := by
    rw [hvdef, ← Real.rpow_natCast ((n : ℝ) ^ (1 / 3 : ℝ)) 2,
      ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  have hn43 : (n : ℝ) ^ (4 / 3 : ℝ) = v ^ (4 : ℕ) := by
    rw [hvdef, ← Real.rpow_natCast ((n : ℝ) ^ (1 / 3 : ℝ)) 4,
      ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  obtain ⟨D, hDdef⟩ :
      ∃ D : ℝ, D = 10 * (n : ℝ) ^ (2 / 3 : ℝ) / ε ^ (1 / 3 : ℝ) := ⟨_, rfl⟩
  refine ⟨D, hDdef, ?_⟩
  have hDuv : D = 10 * v ^ (2 : ℕ) / u := by rw [hDdef, hn23, hudef]
  have hD10 : (10 : ℝ) ≤ D := by
    rw [hDuv, le_div_iff₀ hu0]
    nlinarith
  have hDpos : 0 < D := by linarith
  have hhuv : (h : ℝ) ≤ u * v ^ (4 : ℕ) / 16 := by
    rw [hn43, ← hudef] at hh
    exact hh
  by_cases hcase : (h : ℝ) ≤ D
  · refine ⟨M, ∅, (fun _ => none), id, hclean, ?_, Set.injOn_id _, ?_, hDpos,
      ?_, ?_, ?_, ?_⟩
    · intro N hN
      have hd := hfar N hN
      have hnn : (0 : ℝ) ≤ (n : ℝ) ^ (2 : ℕ) := by positivity
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ε / 40) hnn]
    · simp
    · intro i j hij _
      have hmono : ((violating_triangles M).filter fun t => i ∈ t ∧ j ∈ t) ⊆
          ((violating_triangles M).filter fun t => i ∈ t) := by
        intro t ht
        rcases Finset.mem_filter.mp ht with ⟨h1, h2, -⟩
        exact Finset.mem_filter.mpr ⟨h1, h2⟩
      have hv := hdegree i
      simp only [vertex_triangle_degree] at hv
      have hcard : pair_triangle_degree (violating_triangles M) i j ≤ h := by
        simp only [pair_triangle_degree]
        exact le_trans (Finset.card_le_card hmono) hv
      have hcardR : (pair_triangle_degree (violating_triangles M) i j : ℝ) ≤ (h : ℝ) := by
        exact_mod_cast hcard
      linarith
    · intro t ht e he
      simp at he
    · intro e he
      simp at he
    · intro e he
      simp at he
  · have hDh : D < (h : ℝ) := lt_of_not_ge hcase
    have hDu : D * u = 10 * v ^ (2 : ℕ) := by
      rw [hDuv]
      field_simp
    have hvpos : (0 : ℝ) < v := lt_of_lt_of_le zero_lt_one hv1
    have hv2pos : (0 : ℝ) < v ^ (2 : ℕ) := by positivity
    have hstep1 : D * u < (h : ℝ) * u := mul_lt_mul_of_pos_right hDh hu0
    have hstep2 : (h : ℝ) * u ≤ u * v ^ (4 : ℕ) / 16 * u :=
      mul_le_mul_of_nonneg_right hhuv hu0.le
    have hstep3 : 10 * v ^ (2 : ℕ) < u ^ (2 : ℕ) * v ^ (4 : ℕ) / 16 := by
      have hring : u * v ^ (4 : ℕ) / 16 * u = u ^ (2 : ℕ) * v ^ (4 : ℕ) / 16 := by ring
      linarith only [hring, hstep1, hstep2, hDu]
    have hUV : 160 < u ^ (2 : ℕ) * v ^ (2 : ℕ) := by
      nlinarith only [hstep3, hv2pos, hv1]
    have huv : 12 < u * v := by
      nlinarith only [hUV, mul_pos hu0 hvpos, hu0, hvpos]
    have hDsq : D ^ (2 : ℕ) * u ^ (2 : ℕ) = 100 * v ^ (4 : ℕ) := by
      calc D ^ (2 : ℕ) * u ^ (2 : ℕ) = (D * u) ^ (2 : ℕ) := by ring
        _ = (10 * v ^ (2 : ℕ)) ^ (2 : ℕ) := by rw [hDu]
        _ = 100 * v ^ (4 : ℕ) := by ring
    have hD2pos : (0 : ℝ) < D ^ (2 : ℕ) := by positivity
    have heps : 100 * u * v ^ (4 : ℕ) = ε * D ^ (2 : ℕ) := by
      calc 100 * u * v ^ (4 : ℕ) = u * (100 * v ^ (4 : ℕ)) := by ring
        _ = u * (D ^ (2 : ℕ) * u ^ (2 : ℕ)) := by rw [hDsq]
        _ = u ^ (3 : ℕ) * D ^ (2 : ℕ) := by ring
        _ = ε * D ^ (2 : ℕ) := by rw [hu3]
    have h1600 : 1600 * (h : ℝ) < D ^ (2 : ℕ) := by
      linarith only [hhuv, heps,
        mul_pos (by linarith only [hε₁] : (0 : ℝ) < 1 - ε) hD2pos]
    have heD : ε * D = 10 * (u ^ (2 : ℕ) * v ^ (2 : ℕ)) := by
      calc ε * D = u ^ (3 : ℕ) * D := by rw [hu3]
        _ = u ^ (2 : ℕ) * (D * u) := by ring
        _ = u ^ (2 : ℕ) * (10 * v ^ (2 : ℕ)) := by rw [hDu]
        _ = 10 * (u ^ (2 : ℕ) * v ^ (2 : ℕ)) := by ring
    have hDbig : 1600 < D := by
      linarith only [heD, hUV,
        mul_pos (by linarith only [hε₁] : (0 : ℝ) < 1 - ε) hDpos]
    have hT3 : ∀ t ∈ violating_triangles M, t.card = 3 := by
      intro t ht
      have ht' : violating_triangle M t := by
        simpa [violating_triangles] using ht
      exact ht'.1
    have hpsymm : ∀ a b : Fin n,
        pair_triangle_degree (violating_triangles M) a b =
          pair_triangle_degree (violating_triangles M) b a := by
      intro a b
      simp only [pair_triangle_degree]
      congr 1
      ext t
      simp only [Finset.mem_filter]
      tauto
    have hdc : ∀ i : Fin n, ∑ k ∈ Finset.univ.erase i,
        pair_triangle_degree (violating_triangles M) i k ≤ 2 * h := by
      intro i
      have hmain : ∑ k ∈ Finset.univ.erase i,
          pair_triangle_degree (violating_triangles M) i k ≤
          2 * vertex_triangle_degree (violating_triangles M) i := by
        simp only [pair_triangle_degree, vertex_triangle_degree]
        have hstep : ∀ k ∈ Finset.univ.erase i,
            ((violating_triangles M).filter fun t => i ∈ t ∧ k ∈ t).card =
              ∑ t ∈ violating_triangles M, if i ∈ t ∧ k ∈ t then 1 else 0 := by
          intro k _
          rw [Finset.card_filter]
        rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
        have hinner : ∀ t ∈ violating_triangles M,
            (∑ k ∈ Finset.univ.erase i, if i ∈ t ∧ k ∈ t then 1 else 0) =
              if i ∈ t then 2 else 0 := by
          intro t ht
          by_cases hit : i ∈ t
          · rw [if_pos hit]
            have hone : (∑ k ∈ Finset.univ.erase i, if i ∈ t ∧ k ∈ t then 1 else 0) =
                ∑ k ∈ Finset.univ.erase i, if k ∈ t then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro k _
              simp [hit]
            rw [hone, ← Finset.card_filter]
            have hset : ((Finset.univ.erase i).filter fun k => k ∈ t) = t.erase i := by
              ext k
              simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
              tauto
            rw [hset, Finset.card_erase_of_mem hit, hT3 t ht]
          · rw [if_neg hit]
            apply Finset.sum_eq_zero
            intro k _
            simp [hit]
        rw [Finset.sum_congr rfl hinner]
        have hfin : (∑ t ∈ violating_triangles M, if i ∈ t then 2 else 0) =
            2 * ((violating_triangles M).filter fun t => i ∈ t).card := by
          rw [Finset.card_filter, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t _
          by_cases hit : i ∈ t <;> simp [hit]
        rw [hfin]
      have := hdegree i
      omega
    obtain ⟨heavy, hheavy⟩ : ∃ hv : Fin n → Fin n → Prop, ∀ a b,
        hv a b ↔ D < (pair_triangle_degree (violating_triangles M) a b : ℝ) :=
      ⟨_, fun _ _ => Iff.rfl⟩
    have hheavysymm : ∀ a b, heavy a b → heavy b a := by
      intro a b hab
      rw [hheavy] at hab
      rw [hheavy, hpsymm b a]
      exact hab
    have hNb : ∀ i : Fin n,
        ((Finset.univ.filter fun k => k ≠ i ∧ heavy i k).card : ℝ) * D ≤ 2 * h := by
      intro i
      have hsub : (Finset.univ.filter fun k => k ≠ i ∧ heavy i k) ⊆
          Finset.univ.erase i := by
        intro k hk
        rcases Finset.mem_filter.mp hk with ⟨-, hki, -⟩
        exact Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩
      have h1 : ∑ _k ∈ Finset.univ.filter (fun k => k ≠ i ∧ heavy i k), D ≤
          ∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ heavy i k),
            (pair_triangle_degree (violating_triangles M) i k : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        rcases Finset.mem_filter.mp hk with ⟨-, -, hk2⟩
        exact le_of_lt ((hheavy i k).mp hk2)
      have h2 : ∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ heavy i k),
            (pair_triangle_degree (violating_triangles M) i k : ℝ) ≤
          ∑ k ∈ Finset.univ.erase i,
            (pair_triangle_degree (violating_triangles M) i k : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro k _ _
        positivity
      have h3 : ∑ k ∈ Finset.univ.erase i,
          (pair_triangle_degree (violating_triangles M) i k : ℝ) ≤ 2 * h := by
        have := hdc i
        have hcast2 : ((∑ k ∈ Finset.univ.erase i,
            pair_triangle_degree (violating_triangles M) i k : ℕ) : ℝ) ≤
            ((2 * h : ℕ) : ℝ) := by exact_mod_cast this
        push_cast at hcast2
        exact hcast2
      have h4 : ∑ _k ∈ Finset.univ.filter (fun k => k ≠ i ∧ heavy i k), D =
          ((Finset.univ.filter fun k => k ≠ i ∧ heavy i k).card : ℝ) * D := by
        rw [Finset.sum_const, nsmul_eq_mul]
      linarith only [h1, h2, h3, h4]
    have hcard3 : ∀ a b c : Fin n, a ≠ b → b ≠ c → a ≠ c →
        ({a, b, c} : Finset (Fin n)).card = 3 := by
      intro a b c hab hbc hac
      rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
        Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
    have hmk : ∀ (t : Finset (Fin n)) (a b c : Fin n), t.card = 3 → a ∈ t → b ∈ t → c ∈ t →
        a ≠ b → b ≠ c → a ≠ c → M a c > M a b + M b c → t ∈ violating_triangles M := by
      intro t a b c ht ha hb hc hab hbc hac hlt
      have hv : violating_triangle M t := ⟨ht, a, ha, b, hb, c, hc, hab, hbc, hac, hlt⟩
      simpa [violating_triangles] using hv
    have hkey : ∀ i j : Fin n, ∃ z : ℝ, 0 < z ∧ (i ≠ j → heavy i j →
        ((((Finset.univ.filter fun k =>
            k ≠ i ∧ k ≠ j ∧ ¬ heavy i k ∧ ¬ heavy j k).filter
          fun k => z < |M i k - M j k| ∨ M i k + M j k < z).card : ℝ) < D / 2)) := by
      intro i j
      by_cases hij : i = j
      · exact ⟨1, one_pos, fun hne => absurd hij hne⟩
      by_cases hhij : heavy i j
      · obtain ⟨S, hSdef⟩ : ∃ S : Finset (Fin n), S =
            Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j ∧ ¬ heavy i k ∧ ¬ heavy j k) :=
          ⟨_, rfl⟩
        have hmem : ∀ k ∈ S, k ≠ i ∧ k ≠ j ∧ ¬ heavy i k ∧ ¬ heavy j k := by
          intro k hk
          rw [hSdef] at hk
          exact (Finset.mem_filter.mp hk).2
        have hmain : ∃ z : ℝ, 0 < z ∧
            (((S.filter fun k => z < |M i k - M j k| ∨ M i k + M j k < z).card : ℝ) <
              D / 2) := by
          by_contra hcontra
          have hcon : ∀ z : ℝ, 0 < z →
              D / 2 ≤ ((S.filter fun k =>
                z < |M i k - M j k| ∨ M i k + M j k < z).card : ℝ) := by
            intro z hz
            by_contra hlt
            exact hcontra ⟨z, hz, lt_of_not_ge hlt⟩
          obtain ⟨q, hqdef⟩ : ∃ q : ℕ, q = ⌈D / 2⌉₊ := ⟨_, rfl⟩
          have hqpos : 0 < q := by
            rw [hqdef]
            exact Nat.ceil_pos.mpr (by linarith only [hDpos])
          have hqD : (D / 2 : ℝ) ≤ (q : ℝ) := by
            rw [hqdef]
            exact Nat.le_ceil _
          have hupper : ∀ k ∈ S, 0 < M i k + M j k := by
            intro k hk
            obtain ⟨hki, hkj, -, -⟩ := hmem k hk
            have hb1 : 0 < M i k := hclean.2.1 i k (Ne.symm hki)
            have hb2 : 0 < M j k := hclean.2.1 j k (Ne.symm hkj)
            linarith only [hb1, hb2]
          have hordered : ∀ k ∈ S, |M i k - M j k| ≤ M i k + M j k := by
            intro k hk
            obtain ⟨hki, hkj, -, -⟩ := hmem k hk
            have hb1 : 0 < M i k := hclean.2.1 i k (Ne.symm hki)
            have hb2 : 0 < M j k := hclean.2.1 j k (Ne.symm hkj)
            rw [abs_le]
            constructor
            · linarith only [hb1, hb2]
            · linarith only [hb1, hb2]
          have homit : ∀ z : ℝ, 0 < z →
              q ≤ (S.filter fun k => z < |M i k - M j k| ∨ M i k + M j k < z).card := by
            intro z hz
            rw [hqdef]
            exact Nat.ceil_le.mpr (hcon z hz)
          obtain ⟨x, hx0, L, R, hLS, hRS, hdisj, hLcard, hRcard, hLup, hRlow, -⟩ :=
            finite_interval_omission_selection S (fun k => |M i k - M j k|)
              (fun k => M i k + M j k) q hqpos hupper hordered homit
          have hviol : ∀ k ∈ L, ∀ l ∈ R,
              ({i, k, l} : Finset (Fin n)) ∈ violating_triangles M ∨
                ({j, k, l} : Finset (Fin n)) ∈ violating_triangles M := by
            intro k hk l hl
            obtain ⟨hki, hkj, -, -⟩ := hmem k (hLS hk)
            obtain ⟨hli, hlj, -, -⟩ := hmem l (hRS hl)
            have hkl : k ≠ l := by
              intro hc
              have hkR : k ∈ R := by rw [hc]; exact hl
              exact (Finset.disjoint_left.mp hdisj hk) hkR
            have hsep : M i k + M j k < |M i l - M j l| :=
              lt_of_le_of_lt (hLup k hk) (hRlow l hl)
            have hs1 : M k j = M j k := hclean.2.2 k j
            have hs2 : M k i = M i k := hclean.2.2 k i
            have hik : i ≠ k := Ne.symm hki
            have hil : i ≠ l := Ne.symm hli
            have hjk : j ≠ k := Ne.symm hkj
            have hjl : j ≠ l := Ne.symm hlj
            rcases abs_cases (M i l - M j l) with ⟨habs, -⟩ | ⟨habs, -⟩
            · rw [habs] at hsep
              by_cases hc1 : M i k + M k l < M i l
              · exact Or.inl (hmk ({i, k, l} : Finset (Fin n)) i k l
                  (hcard3 i k l hik hkl hil) (by simp) (by simp) (by simp)
                  hik hkl hil (by linarith only [hc1]))
              · have hc1' : M i l ≤ M i k + M k l := not_lt.mp hc1
                exact Or.inr (hmk ({j, k, l} : Finset (Fin n)) k j l
                  (hcard3 j k l hjk hkl hjl) (by simp) (by simp) (by simp)
                  hkj hjl hkl (by linarith only [hsep, hc1', hs1]))
            · rw [habs] at hsep
              by_cases hc1 : M j k + M k l < M j l
              · exact Or.inr (hmk ({j, k, l} : Finset (Fin n)) j k l
                  (hcard3 j k l hjk hkl hjl) (by simp) (by simp) (by simp)
                  hjk hkl hjl (by linarith only [hc1]))
              · have hc1' : M j l ≤ M j k + M k l := not_lt.mp hc1
                exact Or.inl (hmk ({i, k, l} : Finset (Fin n)) k i l
                  (hcard3 i k l hik hkl hil) (by simp) (by simp) (by simp)
                  hki hil hkl (by linarith only [hsep, hc1', hs2]))
          obtain ⟨ψ, hψ⟩ : ∃ ψ : Fin n × Fin n → Finset (Fin n), ∀ p, ψ p =
              if ({i, p.1, p.2} : Finset (Fin n)) ∈ violating_triangles M
                then ({i, p.1, p.2} : Finset (Fin n))
                else ({j, p.1, p.2} : Finset (Fin n)) := ⟨_, fun _ => rfl⟩
          have hinjcard : (L ×ˢ R).card ≤
              (((violating_triangles M).filter fun t => i ∈ t) ∪
                ((violating_triangles M).filter fun t => j ∈ t)).card := by
            refine Finset.card_le_card_of_injOn ψ ?_ ?_
            · intro p hp
              rcases Finset.mem_product.mp (Finset.mem_coe.mp hp) with ⟨hp1, hp2⟩
              by_cases hif : ({i, p.1, p.2} : Finset (Fin n)) ∈ violating_triangles M
              · rw [hψ p, if_pos hif]
                exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hif, by simp⟩)
              · rw [hψ p, if_neg hif]
                rcases hviol p.1 hp1 p.2 hp2 with hA | hB
                · exact absurd hA hif
                · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hB, by simp⟩)
            · intro p hp p' hp' heq
              rw [hψ p, hψ p'] at heq
              rcases Finset.mem_product.mp (Finset.mem_coe.mp hp) with ⟨hp1, hp2⟩
              rcases Finset.mem_product.mp (Finset.mem_coe.mp hp') with ⟨hr1, hr2⟩
              have ha1 : p.1 ≠ i := (hmem p.1 (hLS hp1)).1
              have ha2 : p.2 ≠ i := (hmem p.2 (hRS hp2)).1
              have ha3 : p.1 ≠ j := (hmem p.1 (hLS hp1)).2.1
              have ha4 : p.2 ≠ j := (hmem p.2 (hRS hp2)).2.1
              have hb1 : p'.1 ≠ i := (hmem p'.1 (hLS hr1)).1
              have hb2 : p'.2 ≠ i := (hmem p'.2 (hRS hr2)).1
              have hcross1 : p.1 ≠ p'.2 := by
                intro hc
                have hmm : p.1 ∈ R := by rw [hc]; exact hr2
                exact (Finset.disjoint_left.mp hdisj hp1) hmm
              have hcross2 : p.2 ≠ p'.1 := by
                intro hc
                have hmm : p'.1 ∈ R := by rw [← hc]; exact hp2
                exact (Finset.disjoint_left.mp hdisj hr1) hmm
              by_cases h1 : ({i, p.1, p.2} : Finset (Fin n)) ∈ violating_triangles M
              · by_cases h2 : ({i, p'.1, p'.2} : Finset (Fin n)) ∈ violating_triangles M
                · rw [if_pos h1, if_pos h2] at heq
                  have hk : p.1 = p'.1 := by
                    have hmm : p.1 ∈ ({i, p'.1, p'.2} : Finset (Fin n)) := by
                      rw [← heq]; simp
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hmm
                    rcases hmm with hA | hA | hA
                    · exact absurd hA ha1
                    · exact hA
                    · exact absurd hA hcross1
                  have hl : p.2 = p'.2 := by
                    have hmm : p.2 ∈ ({i, p'.1, p'.2} : Finset (Fin n)) := by
                      rw [← heq]; simp
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hmm
                    rcases hmm with hA | hA | hA
                    · exact absurd hA ha2
                    · exact absurd hA hcross2
                    · exact hA
                  exact Prod.ext hk hl
                · rw [if_pos h1, if_neg h2] at heq
                  exfalso
                  have hmm : i ∈ ({j, p'.1, p'.2} : Finset (Fin n)) := by
                    rw [← heq]; simp
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hmm
                  rcases hmm with hA | hA | hA
                  · exact hij hA
                  · exact absurd hA (Ne.symm hb1)
                  · exact absurd hA (Ne.symm hb2)
              · by_cases h2 : ({i, p'.1, p'.2} : Finset (Fin n)) ∈ violating_triangles M
                · rw [if_neg h1, if_pos h2] at heq
                  exfalso
                  have hmm : i ∈ ({j, p.1, p.2} : Finset (Fin n)) := by
                    rw [heq]; simp
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hmm
                  rcases hmm with hA | hA | hA
                  · exact hij hA
                  · exact absurd hA (Ne.symm ha1)
                  · exact absurd hA (Ne.symm ha2)
                · rw [if_neg h1, if_neg h2] at heq
                  have hk : p.1 = p'.1 := by
                    have hmm : p.1 ∈ ({j, p'.1, p'.2} : Finset (Fin n)) := by
                      rw [← heq]; simp
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hmm
                    rcases hmm with hA | hA | hA
                    · exact absurd hA ha3
                    · exact hA
                    · exact absurd hA hcross1
                  have hl : p.2 = p'.2 := by
                    have hmm : p.2 ∈ ({j, p'.1, p'.2} : Finset (Fin n)) := by
                      rw [← heq]; simp
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hmm
                    rcases hmm with hA | hA | hA
                    · exact absurd hA ha4
                    · exact absurd hA hcross2
                    · exact hA
                  exact Prod.ext hk hl
          have hdegsum : (((violating_triangles M).filter fun t => i ∈ t) ∪
              ((violating_triangles M).filter fun t => j ∈ t)).card ≤ 2 * h := by
            have hu := Finset.card_union_le ((violating_triangles M).filter fun t => i ∈ t)
              ((violating_triangles M).filter fun t => j ∈ t)
            have hdi := hdegree i
            have hdj := hdegree j
            simp only [vertex_triangle_degree] at hdi hdj
            omega
          have hcards : L.card * R.card ≤ 2 * h := by
            have hpc : (L ×ˢ R).card = L.card * R.card := Finset.card_product L R
            omega
          obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = (((q + 1) / 2 : ℕ) : ℝ) := ⟨_, rfl⟩
          obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = ((q / 2 : ℕ) : ℝ) := ⟨_, rfl⟩
          have hprodR : X * Y ≤ 2 * (h : ℝ) := by
            rw [hXdef, hYdef, ← hLcard, ← hRcard]
            exact_mod_cast hcards
          have hYX : Y ≤ X := by
            rw [hXdef, hYdef]
            have hnn : q / 2 ≤ (q + 1) / 2 := by omega
            exact_mod_cast hnn
          have hYq : (q : ℝ) ≤ 2 * Y + 1 := by
            rw [hYdef]
            have hnn : q ≤ 2 * (q / 2) + 1 := by omega
            exact_mod_cast hnn
          have hY0 : (0 : ℝ) ≤ Y := by
            rw [hYdef]
            exact Nat.cast_nonneg _
          have hYc : D / 4 - 1 / 2 ≤ Y := by linarith only [hYq, hqD]
          have hc0 : (0 : ℝ) ≤ D / 4 - 1 / 2 := by linarith only [hDbig]
          have hsq : (D / 4 - 1 / 2) * (D / 4 - 1 / 2) ≤ X * Y :=
            le_trans (mul_self_le_mul_self hc0 hYc) (mul_le_mul_of_nonneg_right hYX hY0)
          linarith only [hsq, hprodR, h1600, hDpos,
            mul_pos (by linarith only [hDbig] : (0 : ℝ) < D - 1600) hDpos]
        obtain ⟨z, hz0, hzc⟩ := hmain
        refine ⟨z, hz0, fun _ _ => ?_⟩
        rw [← hSdef]
        exact hzc
      · exact ⟨1, one_pos, fun _ hc => absurd hc hhij⟩
    have hswap : ∀ i j : Fin n, ∀ z : ℝ,
        ((Finset.univ.filter fun k => k ≠ i ∧ k ≠ j ∧ ¬ heavy i k ∧ ¬ heavy j k).filter
            fun k => z < |M i k - M j k| ∨ M i k + M j k < z) =
          ((Finset.univ.filter fun k => k ≠ j ∧ k ≠ i ∧ ¬ heavy j k ∧ ¬ heavy i k).filter
            fun k => z < |M j k - M i k| ∨ M j k + M i k < z) := by
      intro i j z
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [abs_sub_comm (M i k) (M j k), add_comm (M i k) (M j k)]
      tauto
    choose g hgpos hgom using hkey
    obtain ⟨y, hydef⟩ : ∃ y : Fin n → Fin n → ℝ, ∀ a b, y a b = g (min a b) (max a b) :=
      ⟨_, fun _ _ => rfl⟩
    have hypos : ∀ a b, 0 < y a b := by
      intro a b
      rw [hydef]
      exact hgpos _ _
    have hysymm : ∀ a b, y a b = y b a := by
      intro a b
      rw [hydef, hydef, min_comm, max_comm]
    have hyom : ∀ i j : Fin n, i ≠ j → heavy i j →
        ((((Finset.univ.filter fun k =>
            k ≠ i ∧ k ≠ j ∧ ¬ heavy i k ∧ ¬ heavy j k).filter
          fun k => y i j < |M i k - M j k| ∨ M i k + M j k < y i j).card : ℝ) < D / 2) := by
      intro i j hij hh2
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · have hmin : min i j = i := min_eq_left hlt.le
        have hmax : max i j = j := max_eq_right hlt.le
        have hg := hgom i j hij hh2
        rw [hydef, hmin, hmax]
        exact hg
      · have hmin : min i j = j := min_eq_right hlt.le
        have hmax : max i j = i := max_eq_left hlt.le
        have hg := hgom j i (Ne.symm hij) (hheavysymm i j hh2)
        rw [hydef, hmin, hmax, hswap i j (g j i)]
        exact hg
    obtain ⟨M₂, hM₂app⟩ : ∃ M₂ : metric_matrix n, ∀ a b, M₂ a b =
        if a = b then 0 else if heavy a b then y a b else M a b :=
      ⟨fun a b => if a = b then 0 else if heavy a b then y a b else M a b, fun _ _ => rfl⟩
    have hM₂diag : ∀ a, M₂ a a = 0 := by
      intro a
      rw [hM₂app]
      simp
    have hM₂pos : ∀ a b, a ≠ b → 0 < M₂ a b := by
      intro a b hab
      rw [hM₂app, if_neg hab]
      by_cases hh2 : heavy a b
      · rw [if_pos hh2]
        exact hypos a b
      · rw [if_neg hh2]
        exact hclean.2.1 a b hab
    have hM₂symm : ∀ a b, M₂ a b = M₂ b a := by
      intro a b
      by_cases hab : a = b
      · rw [hab]
      · rw [hM₂app, hM₂app, if_neg hab, if_neg (Ne.symm hab)]
        by_cases hh2 : heavy a b
        · rw [if_pos hh2, if_pos (hheavysymm a b hh2), hysymm]
        · have hh3 : ¬ heavy b a := fun hc => hh2 (hheavysymm b a hc)
          rw [if_neg hh2, if_neg hh3, hclean.2.2 a b]
    have hM₂clean : clean_matrix M₂ := ⟨hM₂diag, hM₂pos, hM₂symm⟩
    have hM₂eq : ∀ a b, a ≠ b → ¬ heavy a b → M₂ a b = M a b := by
      intro a b hab hh2
      rw [hM₂app, if_neg hab, if_neg hh2]
    have hM₂heavy : ∀ a b, a ≠ b → heavy a b → M₂ a b = y a b := by
      intro a b hab hh2
      rw [hM₂app, if_neg hab, if_pos hh2]
    have hHamNat : matrix_hamming_distance M M₂ ≤
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≠ p.2 ∧ heavy p.1 p.2).card := by
      rw [matrix_hamming_distance]
      apply Finset.card_le_card
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨-, hne⟩
      have hp12 : p.1 ≠ p.2 := by
        intro hc
        apply hne
        rw [hc, hclean.1 p.2, hM₂diag]
      have hph : heavy p.1 p.2 := by
        by_contra hh2
        exact hne (hM₂eq p.1 p.2 hp12 hh2).symm
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp12, hph⟩
    have hrow : ∀ i : Fin n,
        ∑ j : Fin n, (pair_triangle_degree (violating_triangles M) i j : ℝ) ≤ 3 * h := by
      intro i
      have hsplit : ∑ j : Fin n, (pair_triangle_degree (violating_triangles M) i j : ℝ) =
          (pair_triangle_degree (violating_triangles M) i i : ℝ) +
            ∑ j ∈ Finset.univ.erase i,
              (pair_triangle_degree (violating_triangles M) i j : ℝ) :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
      have hdiag : (pair_triangle_degree (violating_triangles M) i i : ℝ) ≤ (h : ℝ) := by
        have heqset : ((violating_triangles M).filter fun t => i ∈ t ∧ i ∈ t) =
            ((violating_triangles M).filter fun t => i ∈ t) := by
          apply Finset.filter_congr
          intro t _
          tauto
        have hnat : pair_triangle_degree (violating_triangles M) i i ≤ h := by
          simp only [pair_triangle_degree]
          rw [heqset]
          have hdi := hdegree i
          simp only [vertex_triangle_degree] at hdi
          exact hdi
        exact_mod_cast hnat
      have hrest : ∑ j ∈ Finset.univ.erase i,
          (pair_triangle_degree (violating_triangles M) i j : ℝ) ≤ 2 * h := by
        have hnat := hdc i
        have hcast2 : ((∑ j ∈ Finset.univ.erase i,
            pair_triangle_degree (violating_triangles M) i j : ℕ) : ℝ) ≤
            ((2 * h : ℕ) : ℝ) := by exact_mod_cast hnat
        push_cast at hcast2
        exact hcast2
      linarith only [hsplit, hdiag, hrest]
    have hAcount : ((Finset.univ.filter fun p : Fin n × Fin n =>
        p.1 ≠ p.2 ∧ heavy p.1 p.2).card : ℝ) * D ≤ 3 * h * n := by
      have h1 : ∑ _p ∈ (Finset.univ.filter fun p : Fin n × Fin n =>
            p.1 ≠ p.2 ∧ heavy p.1 p.2), D ≤
          ∑ p ∈ (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≠ p.2 ∧ heavy p.1 p.2),
            (pair_triangle_degree (violating_triangles M) p.1 p.2 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact le_of_lt ((hheavy p.1 p.2).mp (Finset.mem_filter.mp hp).2.2)
      have h2 : ∑ p ∈ (Finset.univ.filter fun p : Fin n × Fin n =>
            p.1 ≠ p.2 ∧ heavy p.1 p.2),
            (pair_triangle_degree (violating_triangles M) p.1 p.2 : ℝ) ≤
          ∑ p : Fin n × Fin n,
            (pair_triangle_degree (violating_triangles M) p.1 p.2 : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro p _ _
        positivity
      have h3 : ∑ p : Fin n × Fin n,
          (pair_triangle_degree (violating_triangles M) p.1 p.2 : ℝ) ≤ 3 * h * n := by
        rw [Fintype.sum_prod_type]
        have hstep : ∑ i : Fin n, ∑ j : Fin n,
            (pair_triangle_degree (violating_triangles M) i j : ℝ) ≤
            ∑ _i : Fin n, 3 * (h : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          exact hrow i
        have hconst : ∑ _i : Fin n, 3 * (h : ℝ) = 3 * h * n := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
          ring
        linarith only [hstep, hconst]
      have h4 : ∑ _p ∈ (Finset.univ.filter fun p : Fin n × Fin n =>
          p.1 ≠ p.2 ∧ heavy p.1 p.2), D =
          ((Finset.univ.filter fun p : Fin n × Fin n =>
            p.1 ≠ p.2 ∧ heavy p.1 p.2).card : ℝ) * D := by
        rw [Finset.sum_const, nsmul_eq_mul]
      linarith only [h1, h2, h3, h4]
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith only [hnR]
    have hεDn : ε * D * (n : ℝ) = 10 * (u ^ (2 : ℕ) * v ^ (5 : ℕ)) := by
      calc ε * D * (n : ℝ) = u ^ (3 : ℕ) * D * v ^ (3 : ℕ) := by rw [hu3, hv3]
        _ = u ^ (2 : ℕ) * v ^ (3 : ℕ) * (D * u) := by ring
        _ = u ^ (2 : ℕ) * v ^ (3 : ℕ) * (10 * v ^ (2 : ℕ)) := by rw [hDu]
        _ = 10 * (u ^ (2 : ℕ) * v ^ (5 : ℕ)) := by ring
    have h120 : 120 * (h : ℝ) ≤ ε * D * (n : ℝ) := by
      rw [hεDn]
      have hkey1 : (0 : ℝ) < u * v ^ (4 : ℕ) := by positivity
      nlinarith only [hhuv, huv, hkey1]
    have hAbound : ((Finset.univ.filter fun p : Fin n × Fin n =>
        p.1 ≠ p.2 ∧ heavy p.1 p.2).card : ℝ) ≤ ε * (n : ℝ) ^ (2 : ℕ) / 40 := by
      have hmul := mul_le_mul_of_nonneg_right h120 (le_of_lt hnpos)
      have hstep : 40 * ((Finset.univ.filter fun p : Fin n × Fin n =>
          p.1 ≠ p.2 ∧ heavy p.1 p.2).card : ℝ) * D ≤ ε * (n : ℝ) ^ (2 : ℕ) * D := by
        linarith only [hAcount, hmul]
      have hdiv := le_of_mul_le_mul_right hstep hDpos
      linarith only [hdiv]
    have hHam : (matrix_hamming_distance M M₂ : ℝ) ≤ ε * (n : ℝ) ^ (2 : ℕ) / 40 := by
      have hcast : (matrix_hamming_distance M M₂ : ℝ) ≤
          ((Finset.univ.filter fun p : Fin n × Fin n =>
            p.1 ≠ p.2 ∧ heavy p.1 p.2).card : ℝ) := by exact_mod_cast hHamNat
      linarith only [hcast, hAbound]
    have hfar₂ : epsilon_far_from_metric (19 * ε / 40) M₂ := by
      intro N hN
      have hd := hfar N hN
      have htriNat : matrix_hamming_distance M N ≤
          matrix_hamming_distance M M₂ + matrix_hamming_distance M₂ N := by
        rw [matrix_hamming_distance, matrix_hamming_distance, matrix_hamming_distance]
        refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpmem, hne⟩
        by_cases hMM : M p.1 p.2 = M₂ p.1 p.2
        · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hpmem, ?_⟩)
          rw [← hMM]
          exact hne
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpmem, hMM⟩)
      have htri : (matrix_hamming_distance M N : ℝ) ≤
          (matrix_hamming_distance M M₂ : ℝ) + (matrix_hamming_distance M₂ N : ℝ) := by
        exact_mod_cast htriNat
      linarith only [hd, hHam, htri]
    have hthird : ∀ (t : Finset (Fin n)) (a b : Fin n), t.card = 3 → a ≠ b → a ∈ t → b ∈ t →
        ∃ c : Fin n, c ≠ a ∧ c ≠ b ∧ t = {a, b, c} := by
      intro t a b ht hab ha hb
      have hsub : ({a, b} : Finset (Fin n)) ⊆ t := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact ha
        · rw [Finset.mem_singleton] at hx'
          subst hx'
          exact hb
      have hcard2 : ({a, b} : Finset (Fin n)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
      have hinter : ({a, b} : Finset (Fin n)) ∩ t = {a, b} := Finset.inter_eq_left.mpr hsub
      have hsdiff : (t \ ({a, b} : Finset (Fin n))).card = 1 := by
        rw [Finset.card_sdiff, hinter, ht, hcard2]
      obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hsdiff
      have hcmem : c ∈ t \ ({a, b} : Finset (Fin n)) := by
        rw [hc]
        simp
      rcases Finset.mem_sdiff.mp hcmem with ⟨hct, hcnot⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcnot
      refine ⟨c, hcnot.1, hcnot.2, ?_⟩
      have hsub3 : ({a, b, c} : Finset (Fin n)) ⊆ t := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact ha
        · exact hb
        · exact hct
      have hcard3' : ({a, b, c} : Finset (Fin n)).card = 3 :=
        hcard3 a b c hab (Ne.symm hcnot.2) (Ne.symm hcnot.1)
      have hle : t.card ≤ ({a, b, c} : Finset (Fin n)).card := by
        rw [ht, hcard3']
      exact (Finset.eq_of_subset_of_card_le hsub3 hle).symm
    have hpaireq : ∀ a b c d : Fin n, ({a, b} : Finset (Fin n)) = {c, d} → a ≠ b →
        (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
      intro a b c d hset hab
      have ha : a ∈ ({c, d} : Finset (Fin n)) := by
        rw [← hset]
        simp
      have hb : b ∈ ({c, d} : Finset (Fin n)) := by
        rw [← hset]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl
      · rcases hb with rfl | rfl
        · exact absurd rfl hab
        · exact Or.inl ⟨rfl, rfl⟩
      · rcases hb with rfl | rfl
        · exact Or.inr ⟨rfl, rfl⟩
        · exact absurd rfl hab
    obtain ⟨H, hHdef⟩ : ∃ H : Finset (Finset (Fin n)), H =
        (Finset.univ.filter fun p : Fin n × Fin n =>
          p.1 ≠ p.2 ∧ heavy p.1 p.2).image (fun p => {p.1, p.2}) := ⟨_, rfl⟩
    have hHin : ∀ a b : Fin n, a ≠ b → heavy a b → ({a, b} : Finset (Fin n)) ∈ H := by
      intro a b hab hh2
      rw [hHdef]
      exact Finset.mem_image.mpr
        ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hh2⟩, rfl⟩
    have hHrep : ∀ e ∈ H, ∃ a b : Fin n, a ≠ b ∧ heavy a b ∧ e = {a, b} := by
      intro e he
      rw [hHdef] at he
      rcases Finset.mem_image.mp he with ⟨p, hp, hpe⟩
      rcases Finset.mem_filter.mp hp with ⟨-, hne, hh2⟩
      exact ⟨p.1, p.2, hne, hh2, hpe.symm⟩
    have hHheavy : ∀ a b : Fin n, a ≠ b → ({a, b} : Finset (Fin n)) ∈ H → heavy a b := by
      intro a b hab he
      obtain ⟨c, d, hcd, hh2, heq⟩ := hHrep _ he
      rcases hpaireq a b c d heq hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hh2
      · exact hheavysymm _ _ hh2
    have hHcard2 : ∀ e ∈ H, e.card = 2 := by
      intro e he
      obtain ⟨a, b, hab, -, rfl⟩ := hHrep e he
      rw [Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
    have hown_ex : ∀ t : Finset (Fin n), ∃ o : Option (Finset (Fin n)),
        (∀ e ∈ H, o = some e → e ⊆ t) ∧ (o = none ∨ ∃ e ∈ H, o = some e) ∧
          (o = none → ∀ e ∈ H, ¬ e ⊆ t) := by
      intro t
      by_cases hex : ∃ e, e ∈ H ∧ e ⊆ t
      · obtain ⟨e, heH, het⟩ := hex
        refine ⟨some e, ?_, Or.inr ⟨e, heH, rfl⟩, ?_⟩
        · intro e' he' heq
          have : e = e' := Option.some_inj.mp heq
          rw [← this]
          exact het
        · intro hcon
          exact absurd hcon (by simp)
      · refine ⟨none, ?_, Or.inl rfl, ?_⟩
        · intro e' he' heq
          exact absurd heq (by simp)
        · intro _ e heH hsub
          exact hex ⟨e, heH, hsub⟩
    choose owner hown1 hown2 hown3 using hown_ex
    have hT₂3 : ∀ t ∈ violating_triangles M₂, t.card = 3 := by
      intro t ht
      have ht' : violating_triangle M₂ t := by
        simpa [violating_triangles] using ht
      exact ht'.1
    have hagree : ∀ (t : Finset (Fin n)), (∀ e ∈ H, ¬ e ⊆ t) →
        ∀ a ∈ t, ∀ b ∈ t, a ≠ b → M₂ a b = M a b := by
      intro t hnoheavy a ha b hb hab
      refine hM₂eq a b hab ?_
      intro hh2
      refine hnoheavy ({a, b} : Finset (Fin n)) (hHin a b hab hh2) ?_
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact ha
      · rw [Finset.mem_singleton] at hx'
        subst hx'
        exact hb
    have hfixmem : ∀ t ∈ violating_triangles M₂, (∀ e ∈ H, ¬ e ⊆ t) →
        t ∈ violating_triangles M := by
      intro t ht hnoheavy
      have ht' : violating_triangle M₂ t := by
        simpa [violating_triangles] using ht
      obtain ⟨hcardt, a, ha, b, hb, c, hc, hab, hbc, hac, hlt⟩ := ht'
      have e1 : M₂ a c = M a c := hagree t hnoheavy a ha c hc hac
      have e2 : M₂ a b = M a b := hagree t hnoheavy a ha b hb hab
      have e3 : M₂ b c = M b c := hagree t hnoheavy b hb c hc hbc
      refine hmk t a b c hcardt ha hb hc hab hbc hac ?_
      rw [← e1, ← e2, ← e3]
      exact hlt
    have hcandeq : ∀ a b : Fin n, ((violating_triangles M).filter fun t =>
        ({a, b} : Finset (Fin n)) ⊆ t) =
        ((violating_triangles M).filter fun t => a ∈ t ∧ b ∈ t) := by
      intro a b
      apply Finset.filter_congr
      intro t _
      constructor
      · intro hsub
        exact ⟨hsub (by simp), hsub (by simp)⟩
      · intro hmem x hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact hmem.1
        · rw [Finset.mem_singleton] at hx'
          subst hx'
          exact hmem.2
    have hcandbig : ∀ a b : Fin n, a ≠ b → heavy a b →
        D < (((violating_triangles M).filter fun t =>
          ({a, b} : Finset (Fin n)) ⊆ t).card : ℝ) := by
      intro a b hab hh2
      rw [hcandeq a b]
      have hd := (hheavy a b).mp hh2
      simpa [pair_triangle_degree] using hd
    have hbucketlt : ∀ e ∈ H, (((violating_triangles M₂).filter fun t =>
        owner t = some e).card : ℝ) < 201 * D / 400 := by
      intro e he
      obtain ⟨i, j, hij, hh2, rfl⟩ := hHrep e he
      obtain ⟨O, hOdef⟩ : ∃ O : Finset (Fin n), O =
          ((Finset.univ.filter fun k => k ≠ i ∧ k ≠ j ∧ ¬ heavy i k ∧ ¬ heavy j k).filter
            fun k => y i j < |M i k - M j k| ∨ M i k + M j k < y i j) := ⟨_, rfl⟩
      obtain ⟨Ni, hNidef⟩ : ∃ Ni : Finset (Fin n), Ni =
          Finset.univ.filter fun k => k ≠ i ∧ heavy i k := ⟨_, rfl⟩
      obtain ⟨Nj, hNjdef⟩ : ∃ Nj : Finset (Fin n), Nj =
          Finset.univ.filter fun k => k ≠ j ∧ heavy j k := ⟨_, rfl⟩
      have hb1 : M₂ i j = y i j := hM₂heavy i j hij hh2
      have hb2 : M₂ j i = y i j := by
        rw [hM₂heavy j i (Ne.symm hij) (hheavysymm i j hh2), hysymm]
      have hsub : ((violating_triangles M₂).filter fun t =>
          owner t = some ({i, j} : Finset (Fin n))) ⊆
          (O ∪ Ni ∪ Nj).image fun k => ({i, j, k} : Finset (Fin n)) := by
        intro t ht
        rcases Finset.mem_filter.mp ht with ⟨htT, htown⟩
        have hetsub : ({i, j} : Finset (Fin n)) ⊆ t := hown1 t _ he htown
        have hi : i ∈ t := hetsub (by simp)
        have hj : j ∈ t := hetsub (by simp)
        obtain ⟨k, hki, hkj, htk⟩ := hthird t i j (hT₂3 t htT) hij hi hj
        have hdisj : ∀ x ∈ t, x = i ∨ x = j ∨ x = k := by
          intro x hx
          rw [htk] at hx
          simpa using hx
        refine Finset.mem_image.mpr ⟨k, ?_, htk.symm⟩
        by_cases hik : heavy i k
        · refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr ?_)))
          rw [hNidef]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hki, hik⟩
        · by_cases hjk : heavy j k
          · refine Finset.mem_union.mpr (Or.inr ?_)
            rw [hNjdef]
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkj, hjk⟩
          · refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl ?_)))
            rw [hOdef]
            refine Finset.mem_filter.mpr
              ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hki, hkj, hik, hjk⟩, ?_⟩
            by_cases hom : y i j < |M i k - M j k| ∨ M i k + M j k < y i j
            · exact hom
            · exfalso
              rcases not_or.mp hom with ⟨hn1, hn2⟩
              have c1 : M i k - M j k ≤ y i j := (abs_le.mp (not_lt.mp hn1)).2
              have c2 : M j k - M i k ≤ y i j := by
                have hneg := (abs_le.mp (not_lt.mp hn1)).1
                linarith only [hneg]
              have c3 : y i j ≤ M i k + M j k := not_lt.mp hn2
              have hb3 : M₂ i k = M i k := hM₂eq i k (Ne.symm hki) hik
              have hb4 : M₂ k i = M i k := by
                rw [hM₂symm k i]
                exact hb3
              have hb5 : M₂ j k = M j k := hM₂eq j k (Ne.symm hkj) hjk
              have hb6 : M₂ k j = M j k := by
                rw [hM₂symm k j]
                exact hb5
              have hnv : ∀ x z w : Fin n, (x = i ∨ x = j ∨ x = k) → (z = i ∨ z = j ∨ z = k) →
                  (w = i ∨ w = j ∨ w = k) → x ≠ z → z ≠ w → x ≠ w →
                  ¬ (M₂ x w > M₂ x z + M₂ z w) := by
                intro x z w hx hz hw hxz hzw hxw hgt
                rcases hx with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl <;>
                  rcases hw with rfl | rfl | rfl <;>
                  first
                    | exact absurd rfl hxz
                    | exact absurd rfl hzw
                    | exact absurd rfl hxw
                    | linarith only [hgt, hb1, hb2, hb3, hb4, hb5, hb6, c1, c2, c3]
              have htv : violating_triangle M₂ t := by
                simpa [violating_triangles] using htT
              obtain ⟨-, a₁, ha₁, a₂, ha₂, a₃, ha₃, h12, h23, h13, hlt⟩ := htv
              exact hnv a₁ a₂ a₃ (hdisj a₁ ha₁) (hdisj a₂ ha₂) (hdisj a₃ ha₃) h12 h23 h13 hlt
      have hc1 : ((violating_triangles M₂).filter fun t =>
          owner t = some ({i, j} : Finset (Fin n))).card ≤ (O ∪ Ni ∪ Nj).card :=
        le_trans (Finset.card_le_card hsub) Finset.card_image_le
      have hc2 : (O ∪ Ni ∪ Nj).card ≤ O.card + Ni.card + Nj.card :=
        le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)
      have hR : (((violating_triangles M₂).filter fun t =>
          owner t = some ({i, j} : Finset (Fin n))).card : ℝ) ≤
          (O.card : ℝ) + (Ni.card : ℝ) + (Nj.card : ℝ) := by
        exact_mod_cast le_trans hc1 hc2
      have hOlt : (O.card : ℝ) < D / 2 := by
        rw [hOdef]
        exact hyom i j hij hh2
      have hNi : (Ni.card : ℝ) * D ≤ 2 * h := by
        rw [hNidef]
        exact hNb i
      have hNj : (Nj.card : ℝ) * D ≤ 2 * h := by
        rw [hNjdef]
        exact hNb j
      have s1 := mul_le_mul_of_nonneg_right hR hDpos.le
      have s2 := mul_lt_mul_of_pos_right hOlt hDpos
      have s5 : (((violating_triangles M₂).filter fun t =>
          owner t = some ({i, j} : Finset (Fin n))).card : ℝ) * D < 201 * D / 400 * D := by
        linarith only [s1, s2, hNi, hNj, h1600]
      exact lt_of_mul_lt_mul_right s5 hDpos.le
    obtain ⟨cand, hcanddef⟩ : ∃ c : Finset (Fin n) → Finset (Finset (Fin n)), ∀ e,
        c e = (violating_triangles M).filter (fun t => e ⊆ t) := ⟨_, fun _ => rfl⟩
    have hpairwise : ∀ e ∈ H, ∀ e' ∈ H, e ≠ e' → (cand e ∩ cand e').card ≤ 1 := by
      intro e he e' he' hne
      apply Finset.card_le_one.mpr
      intro t ht t' ht'
      rcases Finset.mem_inter.mp ht with ⟨ht1, ht2⟩
      rcases Finset.mem_inter.mp ht' with ⟨ht1', ht2'⟩
      rw [hcanddef] at ht1 ht2 ht1' ht2'
      have hetsub : e ⊆ t := (Finset.mem_filter.mp ht1).2
      have he'tsub : e' ⊆ t := (Finset.mem_filter.mp ht2).2
      have hetsub' : e ⊆ t' := (Finset.mem_filter.mp ht1').2
      have he'tsub' : e' ⊆ t' := (Finset.mem_filter.mp ht2').2
      have htc : t.card = 3 := hT3 t (Finset.mem_filter.mp ht1).1
      have htc' : t'.card = 3 := hT3 t' (Finset.mem_filter.mp ht1').1
      have hec : e.card = 2 := hHcard2 e he
      have he'c : e'.card = 2 := hHcard2 e' he'
      have hunioncard : (e ∪ e').card + (e ∩ e').card = e.card + e'.card :=
        Finset.card_union_add_card_inter e e'
      have hinter : (e ∩ e').card ≤ 1 := by
        rcases le_or_gt (e ∩ e').card 1 with hle | hgt
        · exact hle
        · exfalso
          have h1 : e ∩ e' = e :=
            Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
          have h2 : e ∩ e' = e' :=
            Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
          exact hne (h1.symm.trans h2)
      have hsubt : e ∪ e' ⊆ t := Finset.union_subset hetsub he'tsub
      have hsubt' : e ∪ e' ⊆ t' := Finset.union_subset hetsub' he'tsub'
      have hE : t.card ≤ (e ∪ e').card := by omega
      have hE' : t'.card ≤ (e ∪ e').card := by omega
      have heq1 : e ∪ e' = t := Finset.eq_of_subset_of_card_le hsubt hE
      have heq2 : e ∪ e' = t' := Finset.eq_of_subset_of_card_le hsubt' hE'
      rw [← heq1, ← heq2]
    have hconflt : ∀ e ∈ H, ((H.filter fun e' =>
        e' ≠ e ∧ (cand e ∩ cand e').Nonempty).card : ℝ) < D / 400 := by
      intro e he
      obtain ⟨i, j, hij, hh2, rfl⟩ := hHrep e he
      obtain ⟨Ni, hNidef⟩ : ∃ Ni : Finset (Fin n), Ni =
          Finset.univ.filter fun k => k ≠ i ∧ heavy i k := ⟨_, rfl⟩
      obtain ⟨Nj, hNjdef⟩ : ∃ Nj : Finset (Fin n), Nj =
          Finset.univ.filter fun k => k ≠ j ∧ heavy j k := ⟨_, rfl⟩
      have hsub : (H.filter fun e' => e' ≠ ({i, j} : Finset (Fin n)) ∧
          (cand {i, j} ∩ cand e').Nonempty) ⊆
          (Ni.image fun x => ({i, x} : Finset (Fin n))) ∪
            (Nj.image fun x => ({j, x} : Finset (Fin n))) := by
        intro e' he'
        rcases Finset.mem_filter.mp he' with ⟨he'H, hne', hnonempty⟩
        obtain ⟨t, htmem⟩ := hnonempty
        rcases Finset.mem_inter.mp htmem with ⟨ht1, ht2⟩
        rw [hcanddef] at ht1 ht2
        rcases Finset.mem_filter.mp ht1 with ⟨htT, hesub⟩
        have he'sub : e' ⊆ t := (Finset.mem_filter.mp ht2).2
        have hi : i ∈ t := hesub (by simp)
        have hj : j ∈ t := hesub (by simp)
        obtain ⟨k, hki, hkj, htk⟩ := hthird t i j (hT3 t htT) hij hi hj
        obtain ⟨a, b, hab, -, rfl⟩ := hHrep e' he'H
        have hdisj : ∀ x ∈ t, x = i ∨ x = j ∨ x = k := by
          intro x hx
          rw [htk] at hx
          simpa using hx
        have hha : a ∈ t := he'sub (by simp)
        have hhb : b ∈ t := he'sub (by simp)
        have hsplit : ({a, b} : Finset (Fin n)) = {i, k} ∨
            ({a, b} : Finset (Fin n)) = {j, k} := by
          have h1 := hdisj a hha
          have h2 := hdisj b hhb
          rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
            first
              | exact absurd rfl hab
              | exact absurd rfl hne'
              | exact absurd (Finset.pair_comm _ _) hne'
              | exact Or.inl rfl
              | exact Or.inr rfl
              | exact Or.inl (Finset.pair_comm _ _)
              | exact Or.inr (Finset.pair_comm _ _)
        rcases hsplit with hcase | hcase
        · rw [hcase]
          refine Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨k, ?_, rfl⟩))
          rw [hNidef]
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hki, ?_⟩
          exact hHheavy i k (Ne.symm hki) (hcase ▸ he'H)
        · rw [hcase]
          refine Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨k, ?_, rfl⟩))
          rw [hNjdef]
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkj, ?_⟩
          exact hHheavy j k (Ne.symm hkj) (hcase ▸ he'H)
      have hNi : (Ni.card : ℝ) * D ≤ 2 * h := by
        rw [hNidef]
        exact hNb i
      have hNj : (Nj.card : ℝ) * D ≤ 2 * h := by
        rw [hNjdef]
        exact hNb j
      have hkeybnd : ∀ m : ℕ, (m : ℝ) ≤ (Ni.card : ℝ) + (Nj.card : ℝ) → (m : ℝ) < D / 400 := by
        intro m hm
        have s1 := mul_le_mul_of_nonneg_right hm hDpos.le
        have s5 : (m : ℝ) * D < D / 400 * D := by
          linarith only [s1, hNi, hNj, h1600]
        exact lt_of_mul_lt_mul_right s5 hDpos.le
      refine hkeybnd _ ?_
      have hc1 : (H.filter fun e' => e' ≠ ({i, j} : Finset (Fin n)) ∧
          (cand {i, j} ∩ cand e').Nonempty).card ≤ Ni.card + Nj.card :=
        le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_union_le _ _)
          (Nat.add_le_add Finset.card_image_le Finset.card_image_le))
      exact_mod_cast hc1
    obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = ⌈201 * D / 400⌉₊ := ⟨_, rfl⟩
    obtain ⟨R, hRdef⟩ : ∃ R : ℕ, R = ⌈D / 400⌉₊ := ⟨_, rfl⟩
    have hKle : (201 * D / 400 : ℝ) ≤ (K : ℝ) := by
      rw [hKdef]
      exact Nat.le_ceil _
    have hRle : (D / 400 : ℝ) ≤ (R : ℝ) := by
      rw [hRdef]
      exact Nat.le_ceil _
    have hKlt : (K : ℝ) < 201 * D / 400 + 1 := by
      rw [hKdef]
      exact Nat.ceil_lt_add_one (by positivity)
    have hRlt : (R : ℝ) < D / 400 + 1 := by
      rw [hRdef]
      exact Nat.ceil_lt_add_one (by positivity)
    have hbucketK : ∀ e ∈ H, ((violating_triangles M₂).filter fun t =>
        owner t = some e).card ≤ K := by
      intro e he
      have h2 : ((((violating_triangles M₂).filter fun t => owner t = some e).card : ℝ)) <
          (K : ℝ) := lt_of_lt_of_le (hbucketlt e he) hKle
      exact le_of_lt (by exact_mod_cast h2)
    have hcandcard : ∀ e ∈ H, D < ((cand e).card : ℝ) := by
      intro e he
      obtain ⟨i, j, hij, hh2, rfl⟩ := hHrep e he
      rw [hcanddef]
      exact hcandbig i j hij hh2
    have hcandKR : ∀ e ∈ H, K + R ≤ (cand e).card := by
      intro e he
      have h1 := hcandcard e he
      have h3 : ((K + R : ℕ) : ℝ) < ((cand e).card : ℝ) := by
        push_cast
        linarith only [hKlt, hRlt, h1, hDbig]
      exact le_of_lt (by exact_mod_cast h3)
    have hownerS : ∀ t ∈ violating_triangles M₂,
        owner t = none ∨ ∃ e ∈ H, owner t = some e := fun t _ => hown2 t
    have hfixedS : ∀ t ∈ violating_triangles M₂, owner t = none →
        t ∈ violating_triangles M := fun t ht hnone => hfixmem t ht (hown3 t hnone)
    have hcandU : ∀ e ∈ H, cand e ⊆ violating_triangles M := by
      intro e he
      rw [hcanddef]
      exact Finset.filter_subset _ _
    have hdisjS : ∀ e ∈ H, Disjoint ((violating_triangles M₂).filter fun t =>
        owner t = none) (cand e) := by
      intro e he
      refine Finset.disjoint_left.mpr ?_
      intro t ht htc
      rcases Finset.mem_filter.mp ht with ⟨-, hnone⟩
      rw [hcanddef] at htc
      exact hown3 t hnone e he (Finset.mem_filter.mp htc).2
    have hconfR : ∀ e ∈ H, (H.filter fun e' =>
        e' ≠ e ∧ (cand e ∩ cand e').Nonempty).card ≤ R := by
      intro e he
      have h2 : (((H.filter fun e' =>
          e' ≠ e ∧ (cand e ∩ cand e').Nonempty).card : ℝ)) < (R : ℝ) :=
        lt_of_lt_of_le (hconflt e he) hRle
      exact le_of_lt (by exact_mod_cast h2)
    obtain ⟨φ, hφinj, hφfix, hφplaced, hφimage⟩ :=
      heavy_pair_bucket_embedding H (violating_triangles M₂) (violating_triangles M) owner cand
        K R hownerS hfixedS hbucketK hcandKR hcandU hdisjS hpairwise hconfR
    refine ⟨M₂, H, owner, φ, hM₂clean, hfar₂, hφinj, hφimage, hDpos, ?_, ?_, hbucketlt, ?_⟩
    · intro i j hij hnotH
      by_cases hle : (pair_triangle_degree (violating_triangles M) i j : ℝ) ≤ D
      · exact hle
      · exact absurd (hHin i j hij ((hheavy i j).mpr (lt_of_not_ge hle))) hnotH
    · intro t ht e he hown
      have h1 := hφplaced t ht e he hown
      rw [hcanddef] at h1
      exact (Finset.mem_filter.mp h1).2
    · intro e he
      have hforeignowner : ∀ t ∈ (violating_triangles M₂).filter (fun t =>
          owner t ≠ some e ∧ e ⊆ φ t), ∃ e' ∈ H, owner t = some e' ∧ e' ≠ e ∧
            φ t ∈ cand e ∩ cand e' := by
        intro t ht
        rcases Finset.mem_filter.mp ht with ⟨htT, hne, hsub⟩
        rcases hown2 t with hnone | ⟨e', he'H, hsome⟩
        · exfalso
          have hfix := hφfix t htT hnone
          rw [hfix] at hsub
          exact hown3 t hnone e he hsub
        · have hne2 : e' ≠ e := by
            intro hcon
            rw [hcon] at hsome
            exact hne hsome
          have hp := hφplaced t htT e' he'H hsome
          refine ⟨e', he'H, hsome, hne2, Finset.mem_inter.mpr ⟨?_, hp⟩⟩
          rw [hcanddef]
          exact Finset.mem_filter.mpr ⟨hcandU e' he'H hp, hsub⟩
      have hmapsto : Set.MapsTo (fun t => (owner t).getD ∅)
          (↑((violating_triangles M₂).filter fun t => owner t ≠ some e ∧ e ⊆ φ t) :
            Set (Finset (Fin n)))
          (↑(H.filter fun e' => e' ≠ e ∧ (cand e ∩ cand e').Nonempty) :
            Set (Finset (Fin n))) := by
        intro t ht
        obtain ⟨e', he'H, hsome, hne2, hmem⟩ := hforeignowner t (Finset.mem_coe.mp ht)
        have hg : (owner t).getD ∅ = e' := by simp [hsome]
        refine Finset.mem_coe.mpr ?_
        have hres : ((owner t).getD ∅) ∈
            (H.filter fun e' => e' ≠ e ∧ (cand e ∩ cand e').Nonempty) := by
          rw [hg]
          exact Finset.mem_filter.mpr ⟨he'H, hne2, ⟨φ t, hmem⟩⟩
        exact hres
      have hinjon : Set.InjOn (fun t => (owner t).getD ∅)
          (↑((violating_triangles M₂).filter fun t => owner t ≠ some e ∧ e ⊆ φ t) :
            Set (Finset (Fin n))) := by
        intro t1 ht1 t2 ht2 heqow
        have hm1 := Finset.mem_coe.mp ht1
        have hm2 := Finset.mem_coe.mp ht2
        obtain ⟨e1, he1H, hsome1, hne1, hmem1⟩ := hforeignowner t1 hm1
        obtain ⟨e2, he2H, hsome2, hne2, hmem2⟩ := hforeignowner t2 hm2
        have hg1 : (owner t1).getD ∅ = e1 := by simp [hsome1]
        have hg2 : (owner t2).getD ∅ = e2 := by simp [hsome2]
        have heq' : e1 = e2 := by
          rw [← hg1, ← hg2]
          exact heqow
        have hmem2' : φ t2 ∈ cand e ∩ cand e1 := by
          rw [heq']
          exact hmem2
        have hone := hpairwise e he e1 he1H (Ne.symm hne1)
        have hφeq : φ t1 = φ t2 := Finset.card_le_one.mp hone _ hmem1 _ hmem2'
        exact hφinj (Finset.mem_coe.mpr (Finset.mem_filter.mp hm1).1)
          (Finset.mem_coe.mpr (Finset.mem_filter.mp hm2).1) hφeq
      have hcard := Finset.card_le_card_of_injOn _ hmapsto hinjon
      exact lt_of_le_of_lt (by exact_mod_cast hcard) (hconflt e he)

@[blueprint "lem:heavy-pair-bucket-image-degree-bound"
  (statement := /-- Let \(S,U\) be finite families of subsets of \([n]\), let
  \(H\) be a family of pairs, and let \(\varphi:S\to U\) be injective. Suppose
  \(D>0\), every nonheavy pair has degree at most \(D\) in \(U\), and every
  member of \(S\) owned by \(e\in H\) has image containing \(e\). If fewer
  than \(201D/400\) members are owned by each \(e\), and fewer than \(D/400\)
  members with another owner have images containing \(e\), then every pair
  has degree at most \(D\) in \(\varphi(S)\). -/)
  (proof := /-- Set \(V=\varphi(S)\). If \(\{i,j\}\notin H\), then
  \(V\subseteq U\), so monotonicity of the filter in
  \cref{def:pair-triangle-degree} gives
  \(d_V(i,j)\leq d_U(i,j)\leq D\).

  Now let \(e=\{i,j\}\in H\). Because \(\varphi\) is injective on \(S\),
  its restriction is a bijection from the members of \(S\) whose images
  contain \(e\) onto the members of \(V\) containing \(e\). Partition the
  former set according as its owner is or is not \(e\). In the first part,
  the placement hypothesis is automatic and the cardinality is less than
  \(201D/400\). The second part has cardinality less than \(D/400\) by the
  foreign-image hypothesis. Hence
  \[
    d_V(i,j)<\frac{202D}{400}<D,
  \]
  where the final inequality uses \(D>0\). This proves the assertion for
  every distinct \(i,j\). -/)
  (title := /-- Pair-Degree Bound for a Bucket Embedding -/)
  (latexEnv := "lemma")]
lemma heavy_pair_bucket_image_degree_bound {n : ℕ}
    (S U H : Finset (Finset (Fin n)))
    (owner : Finset (Fin n) → Option (Finset (Fin n)))
    (φ : Finset (Fin n) → Finset (Fin n)) (D : ℝ)
    (hD : 0 < D)
    (hφinj : Set.InjOn φ (↑S : Set (Finset (Fin n))))
    (himage : Finset.image φ S ⊆ U)
    (hlight : ∀ i j, i ≠ j → ({i, j} : Finset (Fin n)) ∉ H →
      (pair_triangle_degree U i j : ℝ) ≤ D)
    (hplaced : ∀ t ∈ S, ∀ e ∈ H, owner t = some e → e ⊆ φ t)
    (hown : ∀ e ∈ H,
      ((S.filter fun t => owner t = some e).card : ℝ) < 201 * D / 400)
    (hforeign : ∀ e ∈ H,
      ((S.filter fun t => owner t ≠ some e ∧ e ⊆ φ t).card : ℝ) < D / 400) :
    ∀ i j, i ≠ j →
      (pair_triangle_degree (Finset.image φ S) i j : ℝ) ≤ D := by
  classical
  intro i j hij
  by_cases hH : ({i, j} : Finset (Fin n)) ∈ H
  · have hsub :
        ((Finset.image φ S).filter fun t => i ∈ t ∧ j ∈ t) ⊆
          Finset.image φ
            ((S.filter fun s => owner s = some ({i, j} : Finset (Fin n))) ∪
              (S.filter fun s => owner s ≠ some ({i, j} : Finset (Fin n)) ∧
                ({i, j} : Finset (Fin n)) ⊆ φ s)) := by
      intro t ht
      rcases Finset.mem_filter.mp ht with ⟨htimg, hti, htj⟩
      rcases Finset.mem_image.mp htimg with ⟨s, hsS, rfl⟩
      apply Finset.mem_image.mpr
      refine ⟨s, ?_, rfl⟩
      by_cases ho : owner s = some ({i, j} : Finset (Fin n))
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hsS, ho⟩)
      · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hsS, ho, ?_⟩)
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact hti
        · rw [Finset.mem_singleton] at hx'
          subst hx'
          exact htj
    have hcard :
        ((Finset.image φ S).filter fun t => i ∈ t ∧ j ∈ t).card ≤
          (S.filter fun s => owner s = some ({i, j} : Finset (Fin n))).card +
            (S.filter fun s => owner s ≠ some ({i, j} : Finset (Fin n)) ∧
              ({i, j} : Finset (Fin n)) ⊆ φ s).card := by
      calc
        ((Finset.image φ S).filter fun t => i ∈ t ∧ j ∈ t).card ≤
            (Finset.image φ
              ((S.filter fun s => owner s = some ({i, j} : Finset (Fin n))) ∪
                (S.filter fun s => owner s ≠ some ({i, j} : Finset (Fin n)) ∧
                  ({i, j} : Finset (Fin n)) ⊆ φ s))).card :=
          Finset.card_le_card hsub
        _ ≤ ((S.filter fun s => owner s = some ({i, j} : Finset (Fin n))) ∪
              (S.filter fun s => owner s ≠ some ({i, j} : Finset (Fin n)) ∧
                ({i, j} : Finset (Fin n)) ⊆ φ s)).card :=
          Finset.card_image_le
        _ ≤ _ := Finset.card_union_le _ _
    have hcardR :
        (((Finset.image φ S).filter fun t => i ∈ t ∧ j ∈ t).card : ℝ) ≤
          ((S.filter fun s => owner s = some ({i, j} : Finset (Fin n))).card : ℝ) +
            ((S.filter fun s => owner s ≠ some ({i, j} : Finset (Fin n)) ∧
              ({i, j} : Finset (Fin n)) ⊆ φ s).card : ℝ) := by
      exact_mod_cast hcard
    have h1 := hown _ hH
    have h2 := hforeign _ hH
    simp only [pair_triangle_degree]
    linarith
  · have hsub :
        ((Finset.image φ S).filter fun t => i ∈ t ∧ j ∈ t) ⊆
          U.filter fun t => i ∈ t ∧ j ∈ t := by
      intro t ht
      rcases Finset.mem_filter.mp ht with ⟨htimg, hmem⟩
      exact Finset.mem_filter.mpr ⟨himage htimg, hmem⟩
    have hcardR :
        (((Finset.image φ S).filter fun t => i ∈ t ∧ j ∈ t).card : ℝ) ≤
          ((U.filter fun t => i ∈ t ∧ j ∈ t).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hl := hlight i j hij hH
    simp only [pair_triangle_degree] at hl ⊢
    linarith

@[blueprint "lem:heavy-pair-simultaneous-reassignment"
  (statement := /-- Let \(0<\varepsilon<1\), let \(M'\) be a clean matrix that is \(\varepsilon/2\)-far from the metric property, and let \(h\in\mathbb N\). Suppose
  \[
    d_{T(M')}(i)\leq h\leq
      \frac{\varepsilon^{1/3}n^{4/3}}{16}
    \qquad(i\in[n]).
  \]
  Then \(T(M')\) has a subfamily \(\widetilde T\) such that
  \[
    |\widetilde T|\geq\frac{19\varepsilon n^2}{240}
    \quad\text{and}\quad
    d_{\widetilde T}(i,j)\leq
      \frac{10n^{2/3}}{\varepsilon^{1/3}}
  \]
  for every pair of distinct vertices \(i,j\in[n]\). -/)
  (proof := /-- Apply
  \cref{lem:heavy-pair-simultaneous-replacement-data} to obtain a clean
  matrix \(M_2\), a family \(H\) of heavy pairs, an owner map, and an
  injection \(\varphi:T(M_2)\to T(M)\) satisfying the light-pair,
  owned-bucket, and foreign-image bounds. In particular, \(M_2\) is
  \(19\varepsilon/40\)-far from the metric property.

  Apply \cref{lem:many-violating-triangles} to \(M_2\) with proximity
  parameter \(19\varepsilon/40\). Since \(0<\varepsilon<1\), this
  parameter lies in \((0,1)\), and therefore
  \[
    |T(M_2)|\geq
      \frac{(19\varepsilon/40)n^2}{6}
      =\frac{19\varepsilon n^2}{240}.
  \]

  Set \(\widetilde T=\varphi(T(M_2))\). Injectivity of \(\varphi\)
  gives \(|\widetilde T|=|T(M_2)|\), and the image invariant gives
  \(\widetilde T\subseteq T(M)\). Finally,
  \cref{lem:heavy-pair-bucket-image-degree-bound}, applied to the remaining
  invariants, gives
  \[
    d_{\widetilde T}(i,j)\leq
      \frac{10n^{2/3}}{\varepsilon^{1/3}}
  \]
  for all distinct \(i,j\). These are precisely the three required
  conclusions. -/)
  (title := /-- Simultaneous Reassignment at Heavy Pairs -/)
  (latexEnv := "lemma")]
lemma heavy_pair_simultaneous_reassignment {n : ℕ} {ε : ℝ}
    {M : metric_matrix n} (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hclean : clean_matrix M)
    (hfar : epsilon_far_from_metric (ε / 2) M) (h : ℕ)
    (hh : (h : ℝ) ≤
      ε ^ (1 / 3 : ℝ) * (n : ℝ) ^ (4 / 3 : ℝ) / 16)
    (hdegree : ∀ i, vertex_triangle_degree (violating_triangles M) i ≤ h) :
    ∃ T : Finset (Finset (Fin n)),
      T ⊆ violating_triangles M ∧
        19 * ε * (n : ℝ) ^ (2 : ℕ) / 240 ≤ T.card ∧
          ∀ i j, i ≠ j →
            (pair_triangle_degree T i j : ℝ) ≤
              10 * (n : ℝ) ^ (2 / 3 : ℝ) / ε ^ (1 / 3 : ℝ) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
    · subst hn0
      norm_num
    · intro i j hij
      subst hn0
      exact i.elim0
  obtain ⟨D, hDval, M₂, H, owner, φ, hclean₂, hfar₂, hinj, himage, hDpos,
    hlight, hplaced, hown, hforeign⟩ :=
    heavy_pair_simultaneous_replacement_data hn hε₀ hε₁ hclean hfar h hh hdegree
  refine ⟨Finset.image φ (violating_triangles M₂), himage, ?_, ?_⟩
  · have hmany := many_violating_triangles (ε := 19 * ε / 40) (M := M₂)
      (by linarith) (by linarith) hclean₂ hfar₂
    have hcardeq :
        (Finset.image φ (violating_triangles M₂)).card =
          (violating_triangles M₂).card :=
      Finset.card_image_of_injOn hinj
    rw [hcardeq]
    linarith
  · intro i j hij
    have hbound :=
      heavy_pair_bucket_image_degree_bound (violating_triangles M₂)
        (violating_triangles M) H owner φ D hDpos hinj himage hlight hplaced
        hown hforeign i j hij
    rw [← hDval]
    exact hbound

@[blueprint "lem:bounded-degree-violating-family"
  (statement := /-- Let $M$ and $\varepsilon$ satisfy the hypotheses of \,\cref{lem:many-violating-triangles}. Fix $h,r\in\mathbb N$, and suppose that
  \[
    h\leq \frac{\varepsilon^{1/3}n^{4/3}}{16}.
  \]
  If at most $r$ vertices have violating-triangle degree at least $h$, and $r\leq\varepsilon n/4$, then there is a subfamily $\widetilde T\subseteq T(M)$ with at least $19\varepsilon n^2/240$ members, vertex degrees at most $h$, and pair degrees $d_{\widetilde T}(i,j)\leq 10n^{2/3}/\varepsilon^{1/3}$ for all distinct vertices $i$ and $j$. -/)
  (proof := /-- Let \(I\) be the set of vertices whose degree in \(T(M)\) is at least \(h\). The farness hypothesis implies \(n\geq2\), since on a set with at most one element every clean matrix is a metric. Let \(m>0\) be the largest off-diagonal entry of \(M\). Define \(M'\) by retaining the diagonal entries, replacing every off-diagonal entry incident with \(I\) by \(m\), and leaving every other entry unchanged. This definition is symmetric, preserves the zero diagonal, and has positive off-diagonal entries, so \(M'\) is clean.

  Since \(|I|\leq r\leq\varepsilon n/4\), the matrices \(M\) and \(M'\) differ on at most \(2|I|n\leq\varepsilon n^2/2\) ordered entries. For every metric matrix \(N\), the triangle inequality for Hamming distance gives
  \[
    d_{\ell_0}(M',N)\geq d_{\ell_0}(M,N)-d_{\ell_0}(M,M')
      \geq\frac{\varepsilon n^2}{2}.
  \]
  Thus \(M'\) is \(\varepsilon/2\)-far from the metric property. The hypotheses
  also force \(h>0\): if \(h=0\), then \(I=[n]\), whereas
  \(n\leq r\leq\varepsilon n/4<n\). If a triangle meets \(I\), two of its
  sides have length \(m\), while its third side has length at most \(m\);
  hence it is nonviolating in \(M'\). A triangle disjoint from \(I\) is
  unchanged. It follows that
  \(T(M')\subseteq T(M)\), and
  \[
    d_{T(M')}(i)<h\quad(i\in[n]).
  \]

  Apply \,\cref{lem:heavy-pair-simultaneous-reassignment} to \(M'\). It gives a family \(\widetilde T\subseteq T(M')\) of cardinality at least \(19\varepsilon n^2/240\) and with every pair degree at most \(10n^{2/3}/\varepsilon^{1/3}\). Since \(\widetilde T\subseteq T(M')\subseteq T(M)\), its vertex degree at \(i\) is at most \(d_{T(M')}(i)<h\), and therefore at most \(h\). This proves all the assertions. -/)
  (title := /-- A Large Bounded-Degree Family of Violations -/)
  (latexEnv := "lemma")]
lemma bounded_degree_violating_family {n : ℕ} {ε : ℝ} {M : metric_matrix n}
    (hε₀ : 0 < ε) (hε₁ : ε < 1) (hclean : clean_matrix M)
    (hfar : epsilon_far_from_metric ε M) (h r : ℕ)
    (hh : (h : ℝ) ≤
      ε ^ (1 / 3 : ℝ) * (n : ℝ) ^ (4 / 3 : ℝ) / 16)
    (hfew : ((Finset.univ.filter fun i =>
      h ≤ vertex_triangle_degree (violating_triangles M) i).card : ℝ) ≤ r)
    (hr : (r : ℝ) ≤ ε * n / 4) :
    ∃ T : Finset (Finset (Fin n)),
      T ⊆ violating_triangles M ∧
        19 * ε * (n : ℝ) ^ (2 : ℕ) / 240 ≤ T.card ∧
          (∀ i, vertex_triangle_degree T i ≤ h) ∧
            ∀ i j, i ≠ j →
              (pair_triangle_degree T i j : ℝ) ≤
                10 * (n : ℝ) ^ (2 / 3 : ℝ) / ε ^ (1 / 3 : ℝ) := by
  classical
  obtain ⟨I, hIdef⟩ : ∃ I : Finset (Fin n), I =
      Finset.univ.filter fun i =>
        h ≤ vertex_triangle_degree (violating_triangles M) i :=
    ⟨_, rfl⟩
  have hIcard : (I.card : ℝ) ≤ r := by
    rw [hIdef]; exact hfew
  have hImem : ∀ i, i ∈ I ↔
      h ≤ vertex_triangle_degree (violating_triangles M) i := by
    intro i
    rw [hIdef]
    simp
  have hsumnonneg : (0 : ℝ) ≤ ∑ p : Fin n × Fin n, |M p.1 p.2| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = 1 + ∑ p : Fin n × Fin n, |M p.1 p.2| :=
    ⟨_, rfl⟩
  have hmpos : 0 < m := by rw [hmdef]; linarith
  have hMlt : ∀ i j, M i j < m := by
    intro i j
    have h1 : |M i j| ≤ ∑ p : Fin n × Fin n, |M p.1 p.2| :=
      Finset.single_le_sum (f := fun p : Fin n × Fin n => |M p.1 p.2|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ (i, j))
    have h2 : M i j ≤ |M i j| := le_abs_self _
    rw [hmdef]
    linarith
  obtain ⟨M', hM'app⟩ : ∃ M' : metric_matrix n, ∀ i j, M' i j =
      if i = j then 0 else if i ∈ I ∨ j ∈ I then m else M i j :=
    ⟨fun i j => if i = j then 0 else if i ∈ I ∨ j ∈ I then m else M i j,
      fun _ _ => rfl⟩
  have hM'pos : ∀ i j, i ≠ j → 0 < M' i j := by
    intro i j hij
    rw [hM'app, if_neg hij]
    by_cases hI : i ∈ I ∨ j ∈ I
    · rw [if_pos hI]; exact hmpos
    · rw [if_neg hI]; exact hclean.2.1 i j hij
  have hM'clean : clean_matrix M' := by
    refine ⟨?_, hM'pos, ?_⟩
    · intro i
      rw [hM'app]
      simp
    · intro i j
      by_cases hij : i = j
      · rw [hij]
      · rw [hM'app, hM'app, if_neg hij, if_neg (Ne.symm hij)]
        by_cases hI : i ∈ I ∨ j ∈ I
        · rw [if_pos hI, if_pos (Or.symm hI)]
        · rw [if_neg hI, if_neg (fun hc => hI (Or.symm hc))]
          exact hclean.2.2 i j
  have hM'le : ∀ i j, M' i j ≤ m := by
    intro i j
    rw [hM'app]
    split_ifs with h1 h2
    · exact hmpos.le
    · exact le_refl m
    · exact (hMlt i j).le
  have hM'eqI : ∀ i j, i ≠ j → (i ∈ I ∨ j ∈ I) → M' i j = m := by
    intro i j hij hI
    rw [hM'app, if_neg hij, if_pos hI]
  have hnoI : ∀ t ∈ violating_triangles M', ∀ v ∈ t, v ∉ I := by
    intro t ht v hvt hvI
    have ht' : violating_triangle M' t := by
      simpa [violating_triangles] using ht
    obtain ⟨hcard, i, hi, j, hj, k, hk, hij, hjk, hik, hviol⟩ := ht'
    have htriple : ({i, j, k} : Finset (Fin n)) = t := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hi
        · rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hj
          · rw [Finset.mem_singleton] at hx
            subst hx
            exact hk
      · rw [hcard]
        rw [Finset.card_insert_of_notMem (by simp [hij, hik]),
          Finset.card_insert_of_notMem (by simp [hjk])]
        simp
    have hvmem : v = i ∨ v = j ∨ v = k := by
      rw [← htriple] at hvt
      rcases Finset.mem_insert.mp hvt with hx | hx
      · exact Or.inl hx
      · rcases Finset.mem_insert.mp hx with hy | hy
        · exact Or.inr (Or.inl hy)
        · exact Or.inr (Or.inr (Finset.mem_singleton.mp hy))
    have hikle : M' i k ≤ m := hM'le i k
    rcases hvmem with rfl | rfl | rfl
    · have h1 : M' v j = m := hM'eqI v j hij (Or.inl hvI)
      have h2 : 0 < M' j k := hM'pos j k hjk
      linarith
    · have h1 : M' i v = m := hM'eqI i v hij (Or.inr hvI)
      have h2 : M' v k = m := hM'eqI v k hjk (Or.inl hvI)
      linarith
    · have h1 : M' j v = m := hM'eqI j v hjk (Or.inr hvI)
      have h2 : 0 < M' i j := hM'pos i j hij
      linarith
  have hsub : violating_triangles M' ⊆ violating_triangles M := by
    intro t ht
    have ht' : violating_triangle M' t := by
      simpa [violating_triangles] using ht
    have hentry : ∀ x ∈ t, ∀ y ∈ t, M' x y = M x y := by
      intro x hx y hy
      by_cases hxy : x = y
      · rw [hM'app, if_pos hxy, hxy]
        exact (hclean.1 y).symm
      · rw [hM'app, if_neg hxy, if_neg]
        intro hc
        rcases hc with hc | hc
        · exact hnoI t ht x hx hc
        · exact hnoI t ht y hy hc
    obtain ⟨hcard, i, hi, j, hj, k, hk, hij, hjk, hik, hviol⟩ := ht'
    have hnew : violating_triangle M t := by
      refine ⟨hcard, i, hi, j, hj, k, hk, hij, hjk, hik, ?_⟩
      rw [← hentry i hi k hk, ← hentry i hi j hj, ← hentry j hj k hk]
      exact hviol
    simpa [violating_triangles] using hnew
  have hdeg' : ∀ i, vertex_triangle_degree (violating_triangles M') i ≤ h := by
    intro i
    by_cases hiI : i ∈ I
    · have hempty : ((violating_triangles M').filter fun t => i ∈ t) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro t ht
        rcases Finset.mem_filter.mp ht with ⟨htv, hit⟩
        exact hnoI t htv i hit hiI
      simp only [vertex_triangle_degree, hempty]
      simp
    · have hlt : vertex_triangle_degree (violating_triangles M) i < h := by
        by_contra hc
        exact hiI ((hImem i).mpr (not_lt.mp hc))
      have hmono : vertex_triangle_degree (violating_triangles M') i ≤
          vertex_triangle_degree (violating_triangles M) i := by
        simp only [vertex_triangle_degree]
        exact Finset.card_le_card (Finset.filter_subset_filter _ hsub)
      omega
  have hdistNat : matrix_hamming_distance M M' ≤ 2 * (I.card * n) := by
    rw [matrix_hamming_distance]
    refine le_trans (Finset.card_le_card
      (t := (I ×ˢ Finset.univ) ∪ (Finset.univ ×ˢ I)) ?_) ?_
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨-, hne⟩
      by_cases hpp : p.1 = p.2
      · exfalso
        apply hne
        rw [hM'app, if_pos hpp, hpp]
        exact hclean.1 p.2
      · by_cases hI : p.1 ∈ I ∨ p.2 ∈ I
        · rcases hI with hI | hI
          · exact Finset.mem_union_left _
              (Finset.mem_product.mpr ⟨hI, Finset.mem_univ _⟩)
          · exact Finset.mem_union_right _
              (Finset.mem_product.mpr ⟨Finset.mem_univ _, hI⟩)
        · exfalso
          apply hne
          rw [hM'app, if_neg hpp, if_neg hI]
    · refine (Finset.card_union_le _ _).trans ?_
      simp [Finset.card_product, two_mul, Nat.mul_comm]
  have hdistR : (matrix_hamming_distance M M' : ℝ) ≤ 2 * ((I.card : ℝ) * n) := by
    exact_mod_cast hdistNat
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsq : ((n : ℝ)) ^ (2 : ℕ) = (n : ℝ) * (n : ℝ) := by ring
  have hstep : (I.card : ℝ) * (n : ℝ) ≤ (ε * n / 4) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right (hIcard.trans hr) hnn
  have hfar' : epsilon_far_from_metric (ε / 2) M' := by
    intro N hN
    have hMN := hfar N hN
    have htriNat : matrix_hamming_distance M N ≤
        matrix_hamming_distance M M' + matrix_hamming_distance M' N := by
      rw [matrix_hamming_distance, matrix_hamming_distance,
        matrix_hamming_distance]
      refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpmem, hne⟩
      by_cases hMM : M p.1 p.2 = M' p.1 p.2
      · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hpmem, ?_⟩)
        rw [← hMM]
        exact hne
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpmem, hMM⟩)
    have htri : (matrix_hamming_distance M N : ℝ) ≤
        (matrix_hamming_distance M M' : ℝ) +
          (matrix_hamming_distance M' N : ℝ) := by
      exact_mod_cast htriNat
    rw [hsq] at hMN ⊢
    linarith
  obtain ⟨T, hTsub, hTcard, hTpair⟩ :=
    heavy_pair_simultaneous_reassignment hε₀ hε₁ hM'clean hfar' h hh hdeg'
  refine ⟨T, hTsub.trans hsub, hTcard, ?_, hTpair⟩
  intro i
  have hmono : vertex_triangle_degree T i ≤
      vertex_triangle_degree (violating_triangles M') i := by
    simp only [vertex_triangle_degree]
    exact Finset.card_le_card (Finset.filter_subset_filter _ hTsub)
  exact hmono.trans (hdeg' i)

@[blueprint "lem:finite-sum-variance-decomposition"
  (statement := /-- Let $A$ and $B$ be finite types with $B$ nonempty, and let $g:A\to B\to\mathbb R$. The total sum of squared deviations from the mean over $A\times B$ is the sum of the within-$B$ squared deviations in each fiber and the cardinality of $B$ times the sum of squared deviations of the fiber means from the total mean. -/)
  (proof := /-- In each fiber, insert and subtract its mean. Expanding the square produces a within-fiber square, a cross term, and the squared difference between the fiber and total means. The cross term vanishes because the deviations from the fiber mean sum to zero. Summing the resulting identity over $A$ gives the decomposition. -/)
  (title := /-- Variance Decomposition for Finite Sums -/)
  (latexEnv := "lemma")]
lemma finite_sum_variance_decomposition {A B : Type} [Fintype A] [Fintype B]
    (hB : 0 < Fintype.card B) (g : A → B → ℝ) :
    (∑ a, ∑ x, (g a x - (∑ a, ∑ x, g a x) /
      ((Fintype.card A : ℝ) * Fintype.card B)) ^ 2) =
      (∑ a, ∑ x, (g a x - (∑ y, g a y) / (Fintype.card B : ℝ)) ^ 2) +
      (Fintype.card B : ℝ) * ∑ a, ((∑ y, g a y) / (Fintype.card B : ℝ) -
        (∑ a, ∑ x, g a x) / ((Fintype.card A : ℝ) * Fintype.card B)) ^ 2 := by
  classical
  have hexpand (a : A) (m : ℝ) :
      (∑ x, (g a x - m) ^ 2) =
        (∑ x, (g a x - (∑ y, g a y) / (Fintype.card B : ℝ)) ^ 2) +
        (Fintype.card B : ℝ) * ((∑ y, g a y) / (Fintype.card B : ℝ) - m) ^ 2 := by
    have hc : ∑ x, (g a x - (∑ y, g a y) / (Fintype.card B : ℝ)) = 0 := by
      rw [Finset.sum_sub_distrib]
      simp
      field_simp
      ring
    calc
      _ = ∑ x, ((g a x - (∑ y, g a y) / (Fintype.card B : ℝ)) ^ 2 +
          2 * ((∑ y, g a y) / (Fintype.card B : ℝ) - m) *
            (g a x - (∑ y, g a y) / (Fintype.card B : ℝ)) +
          ((∑ y, g a y) / (Fintype.card B : ℝ) - m) ^ 2) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        rw [← Finset.mul_sum]
        rw [hc]
        simp
  calc
    _ = ∑ a, ((∑ x, (g a x - (∑ y, g a y) / (Fintype.card B : ℝ)) ^ 2) +
        (Fintype.card B : ℝ) * ((∑ y, g a y) / (Fintype.card B : ℝ) -
          (∑ a, ∑ x, g a x) / ((Fintype.card A : ℝ) * Fintype.card B)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hexpand a _
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]

@[blueprint "lem:finite-sum-pairwise-square-identity"
  (statement := /-- For a nonempty finite type $A$ and a function $u:A\to\mathbb R$, the sum of $(u(a)-u(b))^2$ over ordered pairs $(a,b)$ equals twice $|A|$ times the sum of squared deviations of $u$ from its mean. -/)
  (proof := /-- Subtract the mean from every value of $u$. These centered values sum to zero. Expanding each squared pairwise difference therefore kills the mixed term after summation, while each centered square occurs $|A|$ times in each of the two remaining terms. -/)
  (title := /-- Pairwise Squared Differences and the Finite Mean -/)
  (latexEnv := "lemma")]
lemma finite_sum_pairwise_square_identity {A : Type} [Fintype A]
    (hA : 0 < Fintype.card A) (u : A → ℝ) :
    (∑ a, ∑ b, (u a - u b) ^ 2) = 2 * (Fintype.card A : ℝ) *
      ∑ a, (u a - (∑ b, u b) / (Fintype.card A : ℝ)) ^ 2 := by
  classical
  let m : ℝ := (∑ b, u b) / (Fintype.card A : ℝ)
  have hc : ∑ a, (u a - m) = 0 := by
    dsimp [m]
    rw [Finset.sum_sub_distrib]
    simp
    field_simp
    ring
  have hone (a : A) : ∑ b, ((u a - m) - (u b - m)) ^ 2 =
      (Fintype.card A : ℝ) * (u a - m) ^ 2 + ∑ b, (u b - m) ^ 2 := by
    simp_rw [sub_sq]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum, hc]
    ring
  change (∑ a, ∑ b, (u a - u b) ^ 2) =
    2 * (Fintype.card A : ℝ) * ∑ a, (u a - m) ^ 2
  calc
    _ = ∑ a, ∑ b, ((u a - m) - (u b - m)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = ∑ a, ((Fintype.card A : ℝ) * (u a - m) ^ 2 +
        ∑ b, (u b - m) ^ 2) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hone a
    _ = _ := by
      rw [Finset.sum_add_distrib]
      rw [← Finset.mul_sum]
      rw [show (∑ _a : A, ∑ b, (u b - m) ^ 2) =
        (Fintype.card A : ℝ) * ∑ b, (u b - m) ^ 2 by simp]
      ring

@[blueprint "lem:finite-sum-cauchy-schwarz"
  (statement := /-- If $B$ is a nonempty finite type and $v:B\to\mathbb R$, then $(\sum_xv(x))^2\leq |B|\sum_xv(x)^2$. -/)
  (proof := /-- The sum of the squares of the deviations of $v$ from its finite mean is nonnegative. Expanding that sum and clearing the nonzero cardinality of $B$ gives exactly the claimed inequality. -/)
  (title := /-- Cauchy--Schwarz for a Finite Sum -/)
  (latexEnv := "lemma")]
lemma finite_sum_cauchy_schwarz {B : Type} [Fintype B]
    (hB : 0 < Fintype.card B) (v : B → ℝ) :
    (∑ x, v x) ^ 2 ≤ (Fintype.card B : ℝ) * ∑ x, (v x) ^ 2 := by
  classical
  let m : ℝ := (∑ x, v x) / (Fintype.card B : ℝ)
  have hs : 0 ≤ ∑ x, (v x - m) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hid : (Fintype.card B : ℝ) * (∑ x, (v x - m) ^ 2) =
      (Fintype.card B : ℝ) * (∑ x, v x ^ 2) - (∑ x, v x) ^ 2 := by
    simp_rw [sub_sq]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.sum_mul]
    dsimp [m]
    have hb0 : (Fintype.card B : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (ne_of_gt hB)
    field_simp
    rw [← Finset.mul_sum]
    ring
  nlinarith only [hs, hid]

@[blueprint "lem:finite-product-efron-stein"
  (statement := /-- Let $n$ be positive and let $f:(\operatorname{Fin}s\to\operatorname{Fin}n)\to\mathbb R$. Twice $n$ times the unnormalized variance of $f$ is at most the sum, over coordinates, inputs, and replacement values, of the squared change caused by replacing that coordinate. -/)
  (proof := /-- Induct on the number of coordinates. Separate the first coordinate and apply the variance decomposition in \cref{lem:finite-sum-variance-decomposition}. The within-fiber contribution is the pairwise squared-difference identity \cref{lem:finite-sum-pairwise-square-identity}. Apply the induction hypothesis to the fiber means; \cref{lem:finite-sum-cauchy-schwarz} bounds every squared change of a fiber mean by the average of the pointwise squared changes. Reindexing the first and remaining coordinates gives the asserted update sum. -/)
  (title := /-- Efron--Stein Inequality for a Finite Product -/)
  (latexEnv := "lemma")]
lemma finite_product_efron_stein {n s : ℕ} (hn : 0 < n)
    (f : (Fin s → Fin n) → ℝ) :
    2 * (n : ℝ) *
        ∑ x, (f x - (∑ z, f z) / (n : ℝ) ^ s) ^ 2 ≤
      ∑ i, ∑ x, ∑ y, (f x - f (Function.update x i y)) ^ 2 := by
  classical
  induction s with
  | zero =>
      simp [Subsingleton.elim]
  | succ s ih =>
      let e : (Fin n × (Fin s → Fin n)) ≃ (Fin (s + 1) → Fin n) :=
        Fin.insertNthEquiv (fun _ => Fin n) 0
      let g : (Fin s → Fin n) → Fin n → ℝ := fun a y => f (e (y, a))
      let m : (Fin s → Fin n) → ℝ :=
        fun a => (∑ y, g a y) / (n : ℝ)
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hnCard : 0 < Fintype.card (Fin n) := by simpa using hn
      have hsum (F : (Fin (s + 1) → Fin n) → ℝ) :
          (∑ x, F x) = ∑ a, ∑ y, F (e (y, a)) := by
        rw [← e.sum_comp, Fintype.sum_prod_type_right]
      have hdec :
          (∑ a, ∑ y, (g a y -
              (∑ a, ∑ y, g a y) / (n : ℝ) ^ (s + 1)) ^ 2) =
            (∑ a, ∑ y, (g a y - m a) ^ 2) +
              (n : ℝ) * ∑ a, (m a -
                (∑ a, ∑ y, g a y) / (n : ℝ) ^ (s + 1)) ^ 2 := by
        simpa [m, pow_succ, mul_comm] using
          (finite_sum_variance_decomposition (A := Fin s → Fin n)
            (B := Fin n) hnCard g)
      have hwithin :
          2 * (n : ℝ) * (∑ a, ∑ y, (g a y - m a) ^ 2) =
            ∑ a, ∑ y, ∑ z, (g a y - g a z) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        simpa [m] using
          (finite_sum_pairwise_square_identity hnCard (g a)).symm
      have hmean := ih m
      have hmean' :
          2 * (n : ℝ) * (n : ℝ) *
              ∑ a, (m a - (∑ b, m b) / (n : ℝ) ^ s) ^ 2 ≤
            (n : ℝ) *
              ∑ i, ∑ a, ∑ b, (m a - m (Function.update a i b)) ^ 2 := by
        nlinarith only [hmean, le_of_lt hnR]
      have hmean_sum :
          (∑ b, m b) / (n : ℝ) ^ s =
            (∑ a, ∑ y, g a y) / (n : ℝ) ^ (s + 1) := by
        have hm_sum :
            (∑ b, m b) = (∑ a, ∑ y, g a y) / (n : ℝ) := by
          dsimp [m]
          rw [Finset.sum_div]
        rw [hm_sum, pow_succ]
        ring
      rw [hmean_sum] at hmean'
      have hcs (i : Fin s) (a : Fin s → Fin n) (b : Fin n) :
          (n : ℝ) * (m a - m (Function.update a i b)) ^ 2 ≤
            ∑ y, (g a y - g (Function.update a i b) y) ^ 2 := by
        have hc := finite_sum_cauchy_schwarz hnCard
          (fun y => g a y - g (Function.update a i b) y)
        have hm : m a - m (Function.update a i b) =
            (∑ y, (g a y - g (Function.update a i b) y)) / (n : ℝ) := by
          dsimp [m]
          rw [Finset.sum_sub_distrib]
          ring
        rw [hm]
        calc
          (n : ℝ) *
              ((∑ y, (g a y - g (Function.update a i b) y)) /
                (n : ℝ)) ^ 2 =
              (∑ y, (g a y - g (Function.update a i b) y)) ^ 2 /
                (n : ℝ) := by field_simp
          _ ≤ _ := (div_le_iff₀ hnR).2 (by simpa [mul_comm] using hc)
      have htail :
          (n : ℝ) *
              ∑ i, ∑ a, ∑ b, (m a - m (Function.update a i b)) ^ 2 ≤
            ∑ i, ∑ a, ∑ b, ∑ y,
              (g a y - g (Function.update a i b) y) ^ 2 := by
        simp_rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun i hi =>
          Finset.sum_le_sum fun a ha =>
            Finset.sum_le_sum fun b hb => hcs i a b
      have hmain :
          2 * (n : ℝ) *
              ∑ a, ∑ y, (g a y -
                (∑ a, ∑ y, g a y) / (n : ℝ) ^ (s + 1)) ^ 2 ≤
            (∑ a, ∑ y, ∑ z, (g a y - g a z) ^ 2) +
              ∑ i, ∑ a, ∑ b, ∑ y,
                (g a y - g (Function.update a i b) y) ^ 2 := by
        calc
          _ = (∑ a, ∑ y, ∑ z, (g a y - g a z) ^ 2) +
                2 * (n : ℝ) * (n : ℝ) *
                  ∑ a, (m a -
                    (∑ a, ∑ y, g a y) / (n : ℝ) ^ (s + 1)) ^ 2 := by
              rw [hdec, mul_add, hwithin]
              ring
          _ ≤ _ := add_le_add_right (hmean'.trans htail) _
      have hzero (a : Fin s → Fin n) (y z : Fin n) :
          e (z, a) = Function.update (e (y, a)) 0 z := by
        ext j
        refine Fin.cases ?_ (fun k => ?_) j
        · simp [e]
        · simp [e]
      have hsucc (a : Fin s → Fin n) (i : Fin s) (y b : Fin n) :
          e (y, Function.update a i b) =
            Function.update (e (y, a)) i.succ b := by
        funext j
        refine Fin.cases ?_ (fun k => ?_) j
        · have hzero_succ : (0 : Fin (s + 1)) ≠ i.succ := by
            exact (Fin.succ_ne_zero i).symm
          simp [e, Function.update, hzero_succ]
        · by_cases hki : k = i
          · subst k
            simp [e, Function.update]
          · have hsucc_ne : k.succ ≠ i.succ := by
              exact fun h => hki (Fin.succ_injective s h)
            simp [e, Function.update, hki, hsucc_ne]
      have hrhs :
          (∑ i, ∑ x, ∑ y, (f x - f (Function.update x i y)) ^ 2) =
            (∑ a, ∑ y, ∑ z, (g a y - g a z) ^ 2) +
              ∑ i, ∑ a, ∑ b, ∑ y,
                (g a y - g (Function.update a i b) y) ^ 2 := by
        rw [Fin.sum_univ_succ]
        rw [hsum]
        simp_rw [← hzero]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [hsum]
        simp_rw [← hsucc]
        simp only [g]
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_comm]
      rw [hrhs]
      rw [hsum]
      rw [hsum]
      exact hmain

@[blueprint "lem:three-value-sample-hit-lower-count"
  (statement := /-- Put $q=\lfloor s/3\rfloor$. For any three values $a,b,c\in[n]$, the number of samples $x:[s]\to[n]$ whose image contains all three values is at least
  \[
  q^3(n-1)^{3(q-1)}n^{s-3q}.
  \]
  -/)
  (proof := /-- Split the coordinates into three blocks of size $q$ and a remainder of size $s-3q$. In the first block choose one position with value $a$ and require all other values to avoid $a$; impose the analogous conditions for $b$ and $c$ in the second and third blocks, and leave the remainder arbitrary. The chosen position in each block is uniquely recoverable, so this construction is injective. Each block contributes $q(n-1)^{q-1}$ choices and the remainder contributes $n^{s-3q}$ choices. -/)
  (title := /-- Lower Count for Hitting Three Prescribed Values -/)
  (latexEnv := "lemma")]
lemma three_value_sample_hit_lower_count {n s : ℕ} (hs : 3 ≤ s)
    (a b c : Fin n) :
    let q := s / 3
    q ^ 3 * (n - 1) ^ (3 * (q - 1)) * n ^ (s - 3 * q) ≤
      Fintype.card {x : Fin s → Fin n //
        a ∈ Finset.univ.image x ∧ b ∈ Finset.univ.image x ∧
          c ∈ Finset.univ.image x} := by
  classical
  let q := s / 3
  let r := s % 3
  have hq : 0 < q := by
    dsimp [q]
    omega
  have htotal : q + (q + (q + r)) = s := by
    have hmod := Nat.mod_add_div s 3
    dsimp [q, r]
    omega
  let inner : Fin q ⊕ Fin r ≃ Fin (q + r) := finSumFinEquiv
  let middle : Fin q ⊕ (Fin q ⊕ Fin r) ≃ Fin (q + (q + r)) :=
    (Equiv.sumCongr (Equiv.refl (Fin q)) inner).trans finSumFinEquiv
  let outer :
      Fin q ⊕ (Fin q ⊕ (Fin q ⊕ Fin r)) ≃ Fin (q + (q + (q + r))) :=
    (Equiv.sumCongr (Equiv.refl (Fin q)) middle).trans finSumFinEquiv
  let idx : Fin q ⊕ (Fin q ⊕ (Fin q ⊕ Fin r)) ≃ Fin s :=
    outer.trans (finCongr htotal)
  let Block (v : Fin n) :=
    Σ p : Fin q, ({j : Fin q // j ≠ p} → {w : Fin n // w ≠ v})
  let blockFun (v : Fin n) : Block v → (Fin q → Fin n) := fun z j =>
    if h : j = z.1 then v else (z.2 ⟨j, h⟩).1
  have hblock (v : Fin n) : Function.Injective (blockFun v) := by
    rintro ⟨p, z⟩ ⟨p', z'⟩ hfun
    have hp : p = p' := by
      by_contra hne
      have hv := congrFun hfun p
      simp only [blockFun, dif_pos rfl, dif_neg hne] at hv
      exact (z' ⟨p, hne⟩).2 hv.symm
    subst p'
    have hz : z = z' := by
      funext j
      apply Subtype.ext
      have hv := congrFun hfun j.1
      simp only [blockFun, dif_neg j.2] at hv
      exact hv
    subst z'
    rfl
  let Source := Block a × Block b × Block c × (Fin r → Fin n)
  let sample : Source → (Fin s → Fin n) := fun z i =>
    match idx.symm i with
    | Sum.inl j => blockFun a z.1 j
    | Sum.inr (Sum.inl j) => blockFun b z.2.1 j
    | Sum.inr (Sum.inr (Sum.inl j)) => blockFun c z.2.2.1 j
    | Sum.inr (Sum.inr (Sum.inr j)) => z.2.2.2 j
  have hsample : Function.Injective sample := by
    intro z z' hzz
    have ha : z.1 = z'.1 := hblock a (by
      funext j
      have hv := congrFun hzz (idx (Sum.inl j))
      simpa [sample] using hv)
    have hb : z.2.1 = z'.2.1 := hblock b (by
      funext j
      have hv := congrFun hzz (idx (Sum.inr (Sum.inl j)))
      simpa [sample] using hv)
    have hc : z.2.2.1 = z'.2.2.1 := hblock c (by
      funext j
      have hv := congrFun hzz (idx (Sum.inr (Sum.inr (Sum.inl j))))
      simpa [sample] using hv)
    have hr : z.2.2.2 = z'.2.2.2 := by
      funext j
      have hv := congrFun hzz (idx (Sum.inr (Sum.inr (Sum.inr j))))
      simpa [sample] using hv
    exact Prod.ext ha (Prod.ext hb (Prod.ext hc hr))
  let toHit : Source → {x : Fin s → Fin n //
      a ∈ Finset.univ.image x ∧ b ∈ Finset.univ.image x ∧
        c ∈ Finset.univ.image x} := fun z =>
    ⟨sample z, by
      refine ⟨?_, ?_, ?_⟩
      · refine Finset.mem_image.mpr ⟨idx (Sum.inl z.1.1), Finset.mem_univ _, ?_⟩
        simp [sample, blockFun]
      · refine Finset.mem_image.mpr
          ⟨idx (Sum.inr (Sum.inl z.2.1.1)), Finset.mem_univ _, ?_⟩
        simp [sample, blockFun]
      · refine Finset.mem_image.mpr
          ⟨idx (Sum.inr (Sum.inr (Sum.inl z.2.2.1.1))),
            Finset.mem_univ _, ?_⟩
        simp [sample, blockFun]⟩
  have htoHit : Function.Injective toHit := by
    intro z z' h
    apply hsample
    exact congrArg Subtype.val h
  have hcard := Fintype.card_le_of_injective toHit htoHit
  have hBlock (v : Fin n) :
      Fintype.card (Block v) = q * (n - 1) ^ (q - 1) := by
    simp only [Block, Fintype.card_sigma, Fintype.card_fun,
      Fintype.card_subtype_compl, Fintype.card_fin]
    simp [Finset.card_filter, hq]
  have hr_eq : r = s - 3 * q := by
    omega
  dsimp only
  change q ^ 3 * (n - 1) ^ (3 * (q - 1)) * n ^ (s - 3 * q) ≤ _
  rw [← hr_eq]
  calc
    q ^ 3 * (n - 1) ^ (3 * (q - 1)) * n ^ r =
        Fintype.card Source := by
      simp only [Source, Fintype.card_prod, Fintype.card_fun,
        Fintype.card_fin, hBlock]
      rw [show (n - 1) ^ (3 * (q - 1)) =
        (n - 1) ^ (q - 1) * ((n - 1) ^ (q - 1) *
          (n - 1) ^ (q - 1)) by
            rw [← pow_add, ← pow_add]
            congr 1
            omega]
      simp [pow_succ]
      ring
    _ ≤ _ := hcard

@[blueprint "lem:three-value-sample-hit-lower-probability"
  (statement := /-- If $3\leq s$ and $2s\leq n$, then for any $a,b,c\in[n]$ the proportion of samples $x:[s]\to[n]$ whose image contains $a,b,c$ is at least $s^3/(250n^3)$. -/)
  (proof := /-- Apply \cref{lem:three-value-sample-hit-lower-count} with $q=\lfloor s/3\rfloor$. Since $s\geq3$, one has $q\geq s/5$. The remaining factor is $(1-1/n)^{3(q-1)}$; Bernoulli's inequality and $3(q-1)\leq s\leq n/2$ bound it below by $1/2$. Dividing the resulting count by $n^s$ gives the claim. -/)
  (title := /-- Lower Probability for Hitting Three Values -/)
  (latexEnv := "lemma")]
lemma three_value_sample_hit_lower_probability {n s : ℕ}
    (hs : 3 ≤ s) (hsn : 2 * s ≤ n) (a b c : Fin n) :
    (1 / 250 : ℝ) * (s : ℝ) ^ 3 / (n : ℝ) ^ 3 ≤
      (Fintype.card {x : Fin s → Fin n //
        a ∈ Finset.univ.image x ∧ b ∈ Finset.univ.image x ∧
          c ∈ Finset.univ.image x} : ℝ) / (n : ℝ) ^ s := by
  classical
  let q := s / 3
  let k := 3 * (q - 1)
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : 0 < q := by
    dsimp [q]
    omega
  have hq_bound : s ≤ 5 * q := by
    dsimp [q]
    omega
  have hk : k ≤ s := by
    dsimp [k]
    omega
  have hk_half : 2 * k ≤ n := by omega
  have hbase : (-2 : ℝ) ≤ -(1 / (n : ℝ)) := by
    have hn_one : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hinv : (1 / (n : ℝ)) ≤ 1 := by
      exact (div_le_one hnR).2 hn_one
    linarith
  have hbern := one_add_mul_le_pow hbase k
  have hpow : (1 / 2 : ℝ) ≤
      ((n - 1 : ℕ) : ℝ) ^ k / (n : ℝ) ^ k := by
    rw [← div_pow]
    have hcast : (((n - 1 : ℕ) : ℝ) / (n : ℝ)) =
        1 + -(1 / (n : ℝ)) := by
      rw [Nat.cast_sub (by omega)]
      field_simp
      ring
    rw [hcast]
    have hkR : (2 : ℝ) * k ≤ n := by exact_mod_cast hk_half
    have hlin : (1 / 2 : ℝ) ≤ 1 + (k : ℝ) * (-(1 / (n : ℝ))) := by
      field_simp
      nlinarith
    exact hlin.trans hbern
  have hqR : (s : ℝ) / 5 ≤ q := by
    have hc : (s : ℝ) ≤ 5 * q := by exact_mod_cast hq_bound
    linarith
  have hqpow :
      (s : ℝ) ^ 3 / 125 ≤ (q : ℝ) ^ 3 := by
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (s : ℝ) / 5)
      hqR 3
    norm_num [div_pow] at hp ⊢
    nlinarith
  have hcountNat := three_value_sample_hit_lower_count hs a b c
  have hcount :
      ((q ^ 3 * (n - 1) ^ k * n ^ (s - 3 * q) : ℕ) : ℝ) ≤
        (Fintype.card {x : Fin s → Fin n //
          a ∈ Finset.univ.image x ∧ b ∈ Finset.univ.image x ∧
            c ∈ Finset.univ.image x} : ℝ) := by
    have hcountNat' :
        q ^ 3 * (n - 1) ^ k * n ^ (s - 3 * q) ≤
          Fintype.card {x : Fin s → Fin n //
            a ∈ Finset.univ.image x ∧ b ∈ Finset.univ.image x ∧
              c ∈ Finset.univ.image x} := by
      simpa [q, k] using hcountNat
    exact_mod_cast hcountNat'
  have hexp : 3 + k + (s - 3 * q) = s := by
    dsimp [k]
    omega
  have hratio :
      (((q ^ 3 * (n - 1) ^ k * n ^ (s - 3 * q) : ℕ) : ℝ) /
          (n : ℝ) ^ s) =
        ((q : ℝ) ^ 3 / (n : ℝ) ^ 3) *
          ((((n - 1 : ℕ) : ℝ) ^ k) / (n : ℝ) ^ k) := by
    norm_num only [Nat.cast_mul, Nat.cast_pow]
    have hnpow : (n : ℝ) ^ s =
        (n : ℝ) ^ 3 * (n : ℝ) ^ k * (n : ℝ) ^ (s - 3 * q) := by
      rw [← pow_add, ← pow_add, hexp]
    rw [hnpow]
    field_simp
  have hden : (0 : ℝ) < (n : ℝ) ^ s := pow_pos hnR _
  calc
    (1 / 250 : ℝ) * (s : ℝ) ^ 3 / (n : ℝ) ^ 3 ≤
        ((q : ℝ) ^ 3 / (n : ℝ) ^ 3) *
          ((((n - 1 : ℕ) : ℝ) ^ k) / (n : ℝ) ^ k) := by
      have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := pow_pos hnR _
      have hqnonneg : (0 : ℝ) ≤ (q : ℝ) ^ 3 := by positivity
      have hfactor := mul_le_mul hqpow hpow (by norm_num) hqnonneg
      field_simp at hfactor ⊢
      nlinarith
    _ = ((q ^ 3 * (n - 1) ^ k * n ^ (s - 3 * q) : ℕ) : ℝ) /
          (n : ℝ) ^ s := hratio.symm
    _ ≤ _ := (div_le_div_iff_of_pos_right hden).2 hcount

@[blueprint "lem:sampled-triangle-mean-lower-bound"
  (statement := /-- For a family $T$ of three-element subsets of $[n]$, if $3\leq s$ and $2s\leq n$, then the mean sampled-triangle count is at least $|T|s^3/(250n^3)$. -/)
  (proof := /-- Write the sampled count as the sum of the indicators of the individual triangles and interchange the two finite sums. For every $t\in T$, choose its three distinct vertices using the cardinality-three hypothesis. The lower hitting estimate \cref{lem:three-value-sample-hit-lower-probability} bounds the average of its indicator below by $s^3/(250n^3)$. Summing this uniform estimate over $T$ proves the assertion. -/)
  (title := /-- Mean Lower Bound for Sampled Triangles -/)
  (latexEnv := "lemma")]
lemma sampled_triangle_mean_lower_bound {n : ℕ}
    (T : Finset (Finset (Fin n))) (s : ℕ)
    (hT : ∀ t ∈ T, t.card = 3) (hs : 3 ≤ s) (hsn : 2 * s ≤ n) :
    (1 / 250 : ℝ) * T.card * (s : ℝ) ^ 3 / (n : ℝ) ^ 3 ≤
      sampled_triangle_mean T s := by
  classical
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmean :
      sampled_triangle_mean T s =
        ∑ t ∈ T, (Fintype.card {x : Fin s → Fin n //
          ∀ u ∈ t, u ∈ Finset.univ.image x} : ℝ) / (n : ℝ) ^ s := by
    rw [sampled_triangle_mean]
    rw [show (Fintype.card (Fin s → Fin n) : ℝ) = (n : ℝ) ^ s by simp]
    rw [← Finset.sum_div]
    congr 1
    calc
      (∑ sample : Fin s → Fin n, (sampled_triangle_count T sample : ℝ)) =
          ∑ sample : Fin s → Fin n, ∑ t ∈ T,
            if ∀ u ∈ t, u ∈ Finset.univ.image sample then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro sample hsample
        simp [sampled_triangle_count]
      _ = ∑ t ∈ T, ∑ sample : Fin s → Fin n,
            if ∀ u ∈ t, u ∈ Finset.univ.image sample then (1 : ℝ) else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ t ∈ T, (Fintype.card {x : Fin s → Fin n //
            ∀ u ∈ t, u ∈ Finset.univ.image x} : ℝ) := by
        apply Finset.sum_congr rfl
        intro t ht
        simp only [Finset.sum_boole, Finset.mem_image, Finset.mem_univ,
          true_and, Nat.cast_inj]
        exact (Fintype.card_subtype _).symm
  rw [hmean]
  calc
    (1 / 250 : ℝ) * T.card * (s : ℝ) ^ 3 / (n : ℝ) ^ 3 =
        ∑ _t ∈ T, (1 / 250 : ℝ) * (s : ℝ) ^ 3 / (n : ℝ) ^ 3 := by
      simp
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro t ht
      obtain ⟨a, b, c, hab, hac, hbc, htset⟩ :=
        Finset.card_eq_three.mp (hT t ht)
      have h := three_value_sample_hit_lower_probability hs hsn a b c
      simpa [htset] using h

@[blueprint "lem:finite-filter-card-difference"
  (statement := /-- For two decidable predicates on a finite set, the absolute difference between the cardinalities of their filters is at most the number of elements on which the predicates differ. -/)
  (proof := /-- Express both filter cardinalities as sums of zero--one indicators. The triangle inequality bounds the absolute value of the sum of their differences by the sum of the absolute values, and a case split on the two predicates identifies each absolute value with the indicator that they differ. -/)
  (title := /-- Difference of Two Filter Cardinalities -/)
  (latexEnv := "lemma")]
lemma finite_filter_card_difference {A : Type} [DecidableEq A]
    (S : Finset A) (p q : A → Prop) [DecidablePred p] [DecidablePred q] :
    |((S.filter p).card : ℝ) - (S.filter q).card| ≤
      ((S.filter fun x => p x ≠ q x).card : ℝ) := by
  classical
  have hp : ((S.filter p).card : ℝ) =
      ∑ x ∈ S, if p x then (1 : ℝ) else 0 := by
    exact (Finset.sum_boole p S).symm
  have hq : ((S.filter q).card : ℝ) =
      ∑ x ∈ S, if q x then (1 : ℝ) else 0 := by
    exact (Finset.sum_boole q S).symm
  have hd : ((S.filter fun x => p x ≠ q x).card : ℝ) =
      ∑ x ∈ S, if p x ≠ q x then (1 : ℝ) else 0 := by
    exact (Finset.sum_boole (fun x => p x ≠ q x) S).symm
  rw [hp, hq, ← Finset.sum_sub_distrib, hd]
  calc
    |∑ x ∈ S, ((if p x then (1 : ℝ) else 0) -
        (if q x then (1 : ℝ) else 0))| ≤
        ∑ x ∈ S, |((if p x then (1 : ℝ) else 0) -
          (if q x then (1 : ℝ) else 0))| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hp : p x <;> by_cases hq : q x <;> simp [hp, hq]

@[blueprint "lem:finite-sample-hit-upper-bound"
  (statement := /-- Let $U$ be a finite set of values in $[n]$. Among all functions $x:[s]\to[n]$, the number whose image contains $U$, multiplied by $n^{|U|}$, is at most $s^{|U|}n^s$. -/)
  (proof := /-- For every sample containing $U$, choose one preimage position for each member of $U$. This injects the set of successful samples into the disjoint union, over maps $\phi:U\to[s]$, of samples satisfying $x(\phi(u))=u$. A noninjective $\phi$ has no such samples. If $\phi$ is injective, freely replacing the values at its image defines an injection from the corresponding constrained samples times $[n]^U$ into all samples. Thus each fiber, after multiplication by $n^{|U|}$, has size at most $n^s$; summing over the $s^{|U|}$ choices of $\phi$ proves the bound. -/)
  (title := /-- Uniform-Sample Hitting Bound -/)
  (latexEnv := "lemma")]
lemma finite_sample_hit_upper_bound {n s : ℕ} (U : Finset (Fin n)) :
    n ^ U.card *
        Fintype.card {x : Fin s → Fin n // ∀ u ∈ U, u ∈ Finset.univ.image x} ≤
      s ^ U.card * n ^ s := by
  classical
  let V := ↥U
  let Hit := {x : Fin s → Fin n // ∀ u ∈ U, u ∈ Finset.univ.image x}
  let Choice := V → Fin s
  let Good : Choice → Type := fun φ =>
    {x : Fin s → Fin n // ∀ u : V, x (φ u) = u.1}
  let choosePos : Hit → Choice := fun x u =>
    Classical.choose (by
      have hu := x.2 u.1 u.2
      simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hu)
  let enc : Hit → Σ φ, Good φ := fun x =>
    ⟨choosePos x, ⟨x.1, fun u =>
      Classical.choose_spec (by
        have hu := x.2 u.1 u.2
        simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hu)⟩⟩
  have henc : Function.Injective enc := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun q : Σ φ, Good φ => q.2.1) hxy
  have hHit :
      Fintype.card Hit ≤ Fintype.card (Σ φ, Good φ) :=
    Fintype.card_le_of_injective enc henc
  have hGood (φ : Choice) :
      Fintype.card (Good φ) * n ^ U.card ≤ n ^ s := by
    by_cases hφ : Function.Injective φ
    · let extendMap : Good φ × (V → Fin n) → (Fin s → Fin n) :=
        fun p => Function.extend φ p.2 p.1.1
      have hext : Function.Injective extendMap := by
        rintro ⟨x, z⟩ ⟨x', z'⟩ heq
        have hz : z = z' := by
          funext u
          have hv := congrFun heq (φ u)
          simpa only [extendMap, hφ.extend_apply] using hv
        have hx : x = x' := by
          apply Subtype.ext
          funext i
          by_cases hi : ∃ u, φ u = i
          · obtain ⟨u, rfl⟩ := hi
            exact (x.2 u).trans (x'.2 u).symm
          · have hv := congrFun heq i
            simpa only [extendMap, Function.extend_apply' _ _ _ hi] using hv
        cases hx
        cases hz
        rfl
      have hc := Fintype.card_le_of_injective extendMap hext
      simpa [V, Good, Fintype.card_fun, Fintype.card_prod, mul_comm] using hc
    · have hempty : IsEmpty (Good φ) := by
        rw [Function.not_injective_iff] at hφ
        obtain ⟨u, v, huv, huvφ⟩ := hφ
        refine ⟨fun x => ?_⟩
        apply huvφ
        apply Subtype.ext
        have hxv := x.2 v
        rw [← huv] at hxv
        exact (x.2 u).symm.trans hxv
      have hcard : Fintype.card (Good φ) = 0 := Fintype.card_eq_zero
      simp [hcard]
  calc
    n ^ U.card * Fintype.card Hit ≤
        n ^ U.card * Fintype.card (Σ φ, Good φ) :=
      Nat.mul_le_mul_left _ hHit
    _ = ∑ φ : Choice, n ^ U.card * Fintype.card (Good φ) := by
      rw [Fintype.card_sigma, Finset.mul_sum]
    _ ≤ ∑ _φ : Choice, n ^ s :=
      Finset.sum_le_sum fun φ hφ => by simpa [mul_comm] using hGood φ
    _ = s ^ U.card * n ^ s := by
      simp [Choice, V, Fintype.card_fun]

@[blueprint "lem:triangle-vertex-degree-square-identity"
  (statement := /-- For a finite family $T$ of finite vertex sets, the sum of squared vertex degrees equals the number of triples $(v,t,u)$ with $t,u\in T$ and $v\in t\cap u$, counted as a real number. -/)
  (proof := /-- Expand each degree as a sum of zero--one membership indicators and distribute the square into an ordered double sum. -/)
  (title := /-- Vertex-Degree Square Identity -/)
  (latexEnv := "lemma")]
lemma triangle_vertex_degree_square_identity {n : ℕ}
    (T : Finset (Finset (Fin n))) :
    (∑ v, (vertex_triangle_degree T v : ℝ) ^ 2) =
      ∑ v, ∑ t ∈ T, ∑ u ∈ T,
        if v ∈ t ∧ v ∈ u then (1 : ℝ) else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro v hv
  simp only [vertex_triangle_degree, Nat.cast_card, pow_two]
  have hdeg : ((T.filter fun t => v ∈ t).card : ℝ) =
      ∑ t ∈ T, if v ∈ t then (1 : ℝ) else 0 := by simp
  rw [hdeg]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hvt : v ∈ t <;> by_cases hvu : v ∈ u <;>
    simp [hvt, hvu]

@[blueprint "lem:triangle-pair-degree-square-identity"
  (statement := /-- For a finite family $T$ of finite vertex sets, the sum of squared ordered-pair degrees equals the number of quadruples $(v,w,t,u)$ with $t,u\in T$ and $v,w\in t\cap u$, counted as a real number. -/)
  (proof := /-- Expand each ordered-pair degree as a sum of zero--one simultaneous-membership indicators and distribute its square into an ordered double sum. -/)
  (title := /-- Pair-Degree Square Identity -/)
  (latexEnv := "lemma")]
lemma triangle_pair_degree_square_identity {n : ℕ}
    (T : Finset (Finset (Fin n))) :
    (∑ v, ∑ w, (pair_triangle_degree T v w : ℝ) ^ 2) =
      ∑ v, ∑ w, ∑ t ∈ T, ∑ u ∈ T,
        if v ∈ t ∧ w ∈ t ∧ v ∈ u ∧ w ∈ u then (1 : ℝ) else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro w hw
  simp only [pair_triangle_degree, Nat.cast_card, pow_two]
  have hdeg : ((T.filter fun t => v ∈ t ∧ w ∈ t).card : ℝ) =
      ∑ t ∈ T, if v ∈ t ∧ w ∈ t then (1 : ℝ) else 0 := by simp
  rw [hdeg]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hvt : v ∈ t <;> by_cases hwt : w ∈ t <;>
    by_cases hvu : v ∈ u <;> by_cases hwu : w ∈ u <;>
      simp [hvt, hwt, hvu, hwu]

@[blueprint "lem:finite-sample-hit-upper-probability"
  (statement := /-- If $n>0$, the proportion of maps $x:[s]\to[n]$ whose image contains a prescribed finite set $U$ is at most $(s/n)^{|U|}$. -/)
  (proof := /-- Divide the counting inequality in \cref{lem:finite-sample-hit-upper-bound} by the positive quantity $n^{s+|U|}$. -/)
  (title := /-- Uniform-Sample Hitting Probability Bound -/)
  (latexEnv := "lemma")]
lemma finite_sample_hit_upper_probability {n s : ℕ} (hn : 0 < n)
    (U : Finset (Fin n)) :
    (Fintype.card {x : Fin s → Fin n //
        ∀ u ∈ U, u ∈ Finset.univ.image x} : ℝ) / (n : ℝ) ^ s ≤
      (s : ℝ) ^ U.card / (n : ℝ) ^ U.card := by
  have h := finite_sample_hit_upper_bound (s := s) U
  have hR :
      (n : ℝ) ^ U.card *
          (Fintype.card {x : Fin s → Fin n //
            ∀ u ∈ U, u ∈ Finset.univ.image x} : ℝ) ≤
        (s : ℝ) ^ U.card * (n : ℝ) ^ s := by
    exact_mod_cast h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hns : (0 : ℝ) < (n : ℝ) ^ s := pow_pos hnR _
  have hnU : (0 : ℝ) < (n : ℝ) ^ U.card := pow_pos hnR _
  apply (div_le_div_iff₀ hns hnU).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hR

@[blueprint "lem:triangle-completion-second-moment-bound"
  (statement := /-- Let $T$ be a family of three-element subsets of $[n]$, let $r+1\leq n$, and for a sample $x:[r]\to[n]$ let $A_v(x)$ count the members $t\in T$ containing $v$ for which every vertex of $t\setminus\{v\}$ occurs in $x$. Then
  \[
  \frac1{n^r}\sum_{v,x}A_v(x)^2
  \leq 3|T|\frac{(r+1)^2}{n^2}
   +\sum_{v,w}d_T(v,w)^2\frac{(r+1)^3}{n^3}
   +\sum_vd_T(v)^2\frac{(r+1)^4}{n^4}.
  \]
  -/)
  (proof := /-- Expand $A_v(x)^2$ as an ordered sum over $t,u\in T$. The required sample must hit $(t\setminus\{v\})\cup(u\setminus\{v\})$. This union has size two when $t=u$, size three when the distinct triangles share another vertex, and size four otherwise. Apply \cref{lem:finite-sample-hit-upper-probability} in the three cases. The diagonal triples $(v,t,t)$ number $3|T|$; the pairs sharing an additional vertex are bounded by the ordered-pair degree-square sum from \cref{lem:triangle-pair-degree-square-identity}; and all pairs containing $v$ are counted by \cref{lem:triangle-vertex-degree-square-identity}. -/)
  (title := /-- Second Moment of Triangle Completions -/)
  (latexEnv := "lemma")]
lemma triangle_completion_second_moment_bound {n r : ℕ}
    (T : Finset (Finset (Fin n))) (hT : ∀ t ∈ T, t.card = 3)
    (hn : 0 < n) (hrn : r + 1 ≤ n) :
    (∑ v, ∑ x : Fin r → Fin n,
        ((T.filter fun t => v ∈ t ∧
          ∀ u ∈ t.erase v, u ∈ Finset.univ.image x).card : ℝ) ^ 2) /
        (n : ℝ) ^ r ≤
      3 * T.card * (r + 1 : ℝ) ^ 2 / (n : ℝ) ^ 2 +
        (∑ v, ∑ w, (pair_triangle_degree T v w : ℝ) ^ 2) *
          (r + 1 : ℝ) ^ 3 / (n : ℝ) ^ 3 +
        (∑ v, (vertex_triangle_degree T v : ℝ) ^ 2) *
          (r + 1 : ℝ) ^ 4 / (n : ℝ) ^ 4 := by
  classical
  let P : Fin n → Finset (Fin n) → (Fin r → Fin n) → Prop :=
    fun v t x => v ∈ t ∧ ∀ u ∈ t.erase v, u ∈ Finset.univ.image x
  let p : ℝ := (r + 1 : ℝ) / (n : ℝ)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    exact (div_le_one hnR).2 (by exact_mod_cast hrn)
  have herase (v : Fin n) (t : Finset (Fin n)) (ht : t ∈ T)
      (hvt : v ∈ t) : (t.erase v).card = 2 := by
    rw [Finset.card_erase_of_mem hvt, hT t ht]
  have hinter_le_one (v : Fin n) (t u : Finset (Fin n))
      (ht : t ∈ T) (hu : u ∈ T) (hvt : v ∈ t) (hvu : v ∈ u)
      (htu : t ≠ u) :
      ((t.erase v) ∩ (u.erase v)).card ≤ 1 := by
    have htcard := herase v t ht hvt
    have hucard := herase v u hu hvu
    by_contra hnot
    have htwo : ((t.erase v) ∩ (u.erase v)).card = 2 := by
      have hle := Finset.card_le_card (Finset.inter_subset_left :
        (t.erase v ∩ u.erase v) ⊆ t.erase v)
      omega
    have heqt : (t.erase v) ∩ (u.erase v) = t.erase v :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hequ : (t.erase v) ∩ (u.erase v) = u.erase v :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    apply htu
    calc
      t = insert v (t.erase v) := (Finset.insert_erase hvt).symm
      _ = insert v (u.erase v) := by rw [← heqt, hequ]
      _ = u := Finset.insert_erase hvu
  have hunion_card (v : Fin n) (t u : Finset (Fin n))
      (ht : t ∈ T) (hu : u ∈ T) (hvt : v ∈ t) (hvu : v ∈ u) :
      let U := (t.erase v) ∪ (u.erase v)
      if t = u then U.card = 2
      else if ((t.erase v) ∩ (u.erase v)).Nonempty then U.card = 3
      else U.card = 4 := by
    dsimp only
    by_cases htu : t = u
    · subst u
      simp [herase v t ht hvt]
    · rw [if_neg htu]
      have htcard := herase v t ht hvt
      have hucard := herase v u hu hvu
      have hsum := Finset.card_union_add_card_inter (t.erase v) (u.erase v)
      by_cases hinter : ((t.erase v) ∩ (u.erase v)).Nonempty
      · rw [if_pos hinter]
        have hpos := Finset.card_pos.mpr hinter
        have hle := hinter_le_one v t u ht hu hvt hvu htu
        omega
      · rw [if_neg hinter]
        have hz : ((t.erase v) ∩ (u.erase v)).card = 0 :=
          Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hinter)
        omega
  have hr_le : (r : ℝ) / (n : ℝ) ≤ p := by
    dsimp [p]
    apply (div_le_div_iff_of_pos_right hnR).2
    norm_num
  have hpow_le (k : ℕ) :
      (r : ℝ) ^ k / (n : ℝ) ^ k ≤ p ^ k := by
    rw [← div_pow]
    exact pow_le_pow_left₀ (by positivity) hr_le k
  have hprob (v : Fin n) (t u : Finset (Fin n))
      (ht : t ∈ T) (hu : u ∈ T) (hvt : v ∈ t) (hvu : v ∈ u) :
      (∑ x : Fin r → Fin n, if P v t x ∧ P v u x then (1 : ℝ) else 0) /
          (n : ℝ) ^ r ≤
        p ^ 4 + (if t = u then p ^ 2 else 0) +
          ∑ w, if w ∈ t.erase v ∧ w ∈ u.erase v then p ^ 3 else 0 := by
    let U := (t.erase v) ∪ (u.erase v)
    have hsum :
        (∑ x : Fin r → Fin n, if P v t x ∧ P v u x then (1 : ℝ) else 0) =
          (Fintype.card {x : Fin r → Fin n //
            ∀ z ∈ U, z ∈ Finset.univ.image x} : ℝ) := by
      simp only [P, U, Finset.mem_union]
      have hiff : ∀ x : Fin r → Fin n,
          ((v ∈ t ∧ ∀ z ∈ t.erase v, z ∈ Finset.univ.image x) ∧
            v ∈ u ∧ ∀ z ∈ u.erase v, z ∈ Finset.univ.image x) ↔
          ∀ z, z ∈ t.erase v ∨ z ∈ u.erase v →
            z ∈ Finset.univ.image x := by
        intro x
        simp only [hvt, hvu, true_and]
        constructor
        · rintro ⟨htx, hux⟩ z (hz | hz)
          · exact htx z hz
          · exact hux z hz
        · intro hx
          exact ⟨fun z hz => hx z (Or.inl hz), fun z hz => hx z (Or.inr hz)⟩
      simp_rw [hiff]
      simp only [Finset.sum_boole, Nat.cast_inj]
      exact (Fintype.card_subtype _).symm
    rw [hsum]
    have hupp := finite_sample_hit_upper_probability (s := r) hn U
    have hcard := hunion_card v t u ht hu hvt hvu
    dsimp only at hcard
    by_cases htu : t = u
    · rw [if_pos htu] at hcard ⊢
      rw [hcard] at hupp
      have hp2 := (hupp.trans (hpow_le 2))
      have hsumnn : 0 ≤
          ∑ w, if w ∈ t.erase v ∧ w ∈ u.erase v then p ^ 3 else 0 :=
        Finset.sum_nonneg fun _ _ => by positivity
      nlinarith [hp2, hsumnn, pow_nonneg hp0 4]
    · rw [if_neg htu] at hcard ⊢
      by_cases hinter : ((t.erase v) ∩ (u.erase v)).Nonempty
      · rw [if_pos hinter] at hcard
        rw [hcard] at hupp
        have hp3 := hupp.trans (hpow_le 3)
        obtain ⟨w, hw⟩ := hinter
        have hw' : w ∈ t.erase v ∧ w ∈ u.erase v :=
          ⟨(Finset.mem_inter.mp hw).1, (Finset.mem_inter.mp hw).2⟩
        have hone : p ^ 3 ≤
            ∑ w, if w ∈ t.erase v ∧ w ∈ u.erase v then p ^ 3 else 0 := by
          calc
            p ^ 3 =
                (if w ∈ t.erase v ∧ w ∈ u.erase v then p ^ 3 else 0) := by
              simp [hw']
            _ ≤ _ := by
              apply Finset.single_le_sum
                (s := Finset.univ)
                (f := fun z : Fin n =>
                  if z ∈ t.erase v ∧ z ∈ u.erase v then p ^ 3 else 0)
              · intro z hz
                split <;> positivity
              · exact Finset.mem_univ w
        nlinarith [pow_nonneg hp0 4]
      · rw [if_neg hinter] at hcard
        rw [hcard] at hupp
        have hp4 := hupp.trans (hpow_le 4)
        have hsumnn : 0 ≤
            ∑ w, if w ∈ t.erase v ∧ w ∈ u.erase v then p ^ 3 else 0 :=
          Finset.sum_nonneg fun _ _ => by positivity
        nlinarith [hp4, hsumnn]
  have hA (v : Fin n) (x : Fin r → Fin n) :
      ((T.filter fun t => v ∈ t ∧
        ∀ u ∈ t.erase v, u ∈ Finset.univ.image x).card : ℝ) =
        ∑ t ∈ T, if P v t x then (1 : ℝ) else 0 := by
    simp [P]
  have hdiag :
      (∑ v, ∑ t ∈ T, ∑ u ∈ T,
        if v ∈ t ∧ v ∈ u ∧ t = u then (1 : ℝ) else 0) =
          3 * T.card := by
    calc
      _ = ∑ v, ∑ t ∈ T, if v ∈ t then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        apply Finset.sum_congr rfl
        intro t ht
        by_cases hvt : v ∈ t
        · simp only [hvt, true_and]
          rw [Finset.sum_eq_single t]
          · simp [hvt]
          · intro u hu hne
            by_cases hvu : v ∈ u
            · simp [hvt, hvu, hne.symm]
            · simp [hvu]
          · exact fun hnot => (hnot ht).elim
        · simp [hvt]
      _ = ∑ t ∈ T, ∑ v, if v ∈ t then (1 : ℝ) else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ _t ∈ T, (3 : ℝ) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [show (∑ v, if v ∈ t then (1 : ℝ) else 0) = t.card by simp]
        rw [hT t ht]
        norm_num
      _ = _ := by simp [mul_comm]
  have hraw :
      (∑ v, ∑ x : Fin r → Fin n,
          ((T.filter fun t => v ∈ t ∧
            ∀ u ∈ t.erase v, u ∈ Finset.univ.image x).card : ℝ) ^ 2) /
          (n : ℝ) ^ r ≤
        p ^ 4 * (∑ v, (vertex_triangle_degree T v : ℝ) ^ 2) +
          p ^ 3 * (∑ v, ∑ w, (pair_triangle_degree T v w : ℝ) ^ 2) +
          p ^ 2 * (3 * T.card) := by
    have hexpand :
        (∑ v, ∑ x : Fin r → Fin n,
            ((T.filter fun t => v ∈ t ∧
              ∀ u ∈ t.erase v, u ∈ Finset.univ.image x).card : ℝ) ^ 2) /
            (n : ℝ) ^ r =
          ∑ v, ∑ t ∈ T, ∑ u ∈ T,
            (∑ x : Fin r → Fin n,
              if P v t x ∧ P v u x then (1 : ℝ) else 0) /
                (n : ℝ) ^ r := by
      simp_rw [← Finset.sum_div]
      congr 1
      apply Finset.sum_congr rfl
      intro v hv
      simp_rw [hA, pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hpt : P v t x <;> by_cases hpu : P v u x <;>
        simp [hpt, hpu]
    rw [hexpand]
    calc
      _ ≤ ∑ v, ∑ t ∈ T, ∑ u ∈ T,
          if v ∈ t ∧ v ∈ u then
            p ^ 4 + (if t = u then p ^ 2 else 0) +
              ∑ w, if w ∈ t.erase v ∧ w ∈ u.erase v then p ^ 3 else 0
          else 0 := by
        apply Finset.sum_le_sum
        intro v hv
        apply Finset.sum_le_sum
        intro t ht
        apply Finset.sum_le_sum
        intro u hu
        by_cases hvt : v ∈ t
        · by_cases hvu : v ∈ u
          · simpa [hvt, hvu] using hprob v t u ht hu hvt hvu
          · simp [P, hvu]
        · simp [P, hvt]
      _ ≤ ∑ v, ∑ t ∈ T, ∑ u ∈ T, (
          p ^ 4 * (if v ∈ t ∧ v ∈ u then (1 : ℝ) else 0) +
            p ^ 3 * (∑ w : Fin n,
              if v ∈ t ∧ w ∈ t ∧ v ∈ u ∧ w ∈ u then (1 : ℝ) else 0) +
            p ^ 2 *
              (if v ∈ t ∧ v ∈ u ∧ t = u then (1 : ℝ) else 0)) := by
        apply Finset.sum_le_sum
        intro v hv
        apply Finset.sum_le_sum
        intro t ht
        apply Finset.sum_le_sum
        intro u hu
        by_cases hvt : v ∈ t
        · by_cases hvu : v ∈ u
          · have hsum :
                (∑ w,
                    if w ∈ t.erase v ∧ w ∈ u.erase v then p ^ 3 else 0) ≤
                  p ^ 3 * (∑ w,
                    if w ∈ t ∧ w ∈ u then (1 : ℝ) else 0) := by
              simp_rw [Finset.mul_sum]
              apply Finset.sum_le_sum
              intro w hw
              by_cases hwe : w ∈ t.erase v ∧ w ∈ u.erase v
              · have hmem : w ∈ t ∧ w ∈ u :=
                  ⟨Finset.mem_of_mem_erase hwe.1,
                    Finset.mem_of_mem_erase hwe.2⟩
                rw [if_pos hwe, if_pos hmem]
                simpa using le_refl (p ^ 3)
              · by_cases hmem : w ∈ t ∧ w ∈ u
                · by_cases hwv : w = v
                  · subst w
                    simp [hvt, hvu, pow_nonneg hp0 3]
                  · have her : w ∈ t.erase v ∧ w ∈ u.erase v :=
                      ⟨Finset.mem_erase.mpr ⟨hwv, hmem.1⟩,
                        Finset.mem_erase.mpr ⟨hwv, hmem.2⟩⟩
                    exact (hwe her).elim
                · rw [if_neg hwe, if_neg hmem]
                  norm_num
            simp only [hvt, hvu, true_and, if_true]
            by_cases htu : t = u
            · subst u
              simp only [if_pos rfl, if_true]
              nlinarith [hsum]
            · simp only [htu, if_false]
              nlinarith [hsum]
          · simp [hvu, pow_nonneg hp0 2, pow_nonneg hp0 3,
              pow_nonneg hp0 4]
        · simp [hvt, pow_nonneg hp0 2, pow_nonneg hp0 3,
            pow_nonneg hp0 4]
      _ = _ := by
        have hpair_reindex :
            (∑ v, ∑ t ∈ T, ∑ u ∈ T, ∑ w,
              if v ∈ t ∧ w ∈ t ∧ v ∈ u ∧ w ∈ u
                then (1 : ℝ) else 0) =
              ∑ v, ∑ w, ∑ t ∈ T, ∑ u ∈ T,
                if v ∈ t ∧ w ∈ t ∧ v ∈ u ∧ w ∈ u
                  then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro v hv
          calc
            (∑ t ∈ T, ∑ u ∈ T, ∑ w,
                if v ∈ t ∧ w ∈ t ∧ v ∈ u ∧ w ∈ u
                  then (1 : ℝ) else 0) =
                ∑ t ∈ T, ∑ w, ∑ u ∈ T,
                  if v ∈ t ∧ w ∈ t ∧ v ∈ u ∧ w ∈ u
                    then (1 : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro t ht
              rw [Finset.sum_comm]
            _ = _ := by rw [Finset.sum_comm]
        rw [triangle_vertex_degree_square_identity T,
          triangle_pair_degree_square_identity T, ← hdiag,
          ← hpair_reindex]
        simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
  dsimp [p] at hraw
  convert hraw using 1 <;> ring

@[blueprint "lem:sampled-triangle-variance-upper-bound"
  (statement := /-- Let $T$ be a family of three-element subsets of $[n]$, where $n>0$, and suppose that $r+1\leq n$. Then the sampled triangle count based on $r+1$ draws satisfies
  \[
  \operatorname{Var}(X_T)\leq
  6|T|\frac{(r+1)^3}{n^3}
  +2\sum_{v,w}d_T(v,w)^2\frac{(r+1)^4}{n^4}
  +2\sum_vd_T(v)^2\frac{(r+1)^5}{n^5}.
  \]
  -/)
  (proof := /-- Apply the finite-product Efron--Stein inequality from \cref{lem:finite-product-efron-stein}. After deleting the resampled coordinate, a triangle whose indicator changes must be completed by either the old or the new coordinate value; \cref{lem:finite-filter-card-difference} therefore bounds the absolute change in the count by the sum of the corresponding two completion counts. Squaring, summing over the old and new values, and then summing over coordinates gives four times $n(r+1)$ times the unnormalised completion second moment. Divide by $2n^{r+2}$ and apply \cref{lem:triangle-completion-second-moment-bound}. -/)
  (title := /-- Variance Bound from Triangle Completions -/)
  (latexEnv := "lemma")]
lemma sampled_triangle_variance_upper_bound {n r : ℕ}
    (T : Finset (Finset (Fin n))) (hT : ∀ t ∈ T, t.card = 3)
    (hn : 0 < n) (hrn : r + 1 ≤ n) :
    sampled_triangle_variance T (r + 1) ≤
      6 * T.card * (r + 1 : ℝ) ^ 3 / (n : ℝ) ^ 3 +
        2 * (∑ v, ∑ w, (pair_triangle_degree T v w : ℝ) ^ 2) *
          (r + 1 : ℝ) ^ 4 / (n : ℝ) ^ 4 +
        2 * (∑ v, (vertex_triangle_degree T v : ℝ) ^ 2) *
          (r + 1 : ℝ) ^ 5 / (n : ℝ) ^ 5 := by
  classical
  let f : (Fin (r + 1) → Fin n) → ℝ :=
    fun x => (sampled_triangle_count T x : ℝ)
  let A : Fin n → (Fin r → Fin n) → ℝ := fun v z =>
    ((T.filter fun t => v ∈ t ∧
      ∀ u ∈ t.erase v, u ∈ Finset.univ.image z).card : ℝ)
  let Q : Fin n → (Fin r → Fin n) → Finset (Fin n) → Prop :=
    fun a z t => ∀ u ∈ t, u = a ∨ u ∈ Finset.univ.image z
  let e (i : Fin (r + 1)) :
      (Fin n × (Fin r → Fin n)) ≃ (Fin (r + 1) → Fin n) :=
    Fin.insertNthEquiv (fun _ => Fin n) i
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have himage (i : Fin (r + 1)) (a : Fin n) (z : Fin r → Fin n)
      (u : Fin n) :
      u ∈ Finset.univ.image (e i (a, z)) ↔
        u = a ∨ u ∈ Finset.univ.image z := by
    constructor
    · intro hu
      obtain ⟨j, hj, hju⟩ := Finset.mem_image.mp hu
      rcases Fin.eq_self_or_eq_succAbove i j with hji | ⟨k, hjk⟩
      · subst j
        left
        simpa [e] using hju.symm
      · subst j
        right
        exact Finset.mem_image.mpr
          ⟨k, Finset.mem_univ k, by simpa [e] using hju⟩
    · rintro (rfl | hu)
      · exact Finset.mem_image.mpr
          ⟨i, Finset.mem_univ i, by simp [e]⟩
      · obtain ⟨k, hk, hku⟩ := Finset.mem_image.mp hu
        exact Finset.mem_image.mpr
          ⟨i.succAbove k, Finset.mem_univ _, by simpa [e] using hku⟩
  have hcount (i : Fin (r + 1)) (a : Fin n) (z : Fin r → Fin n) :
      f (e i (a, z)) = ((T.filter (Q a z)).card : ℝ) := by
    dsimp [f, sampled_triangle_count]
    have hfilter :
        (T.filter fun t =>
          ∀ u ∈ t, u ∈ Finset.univ.image (e i (a, z))) =
            T.filter (Q a z) := by
      apply Finset.filter_congr
      intro t ht
      constructor
      · intro hall u hu
        exact (himage i a z u).mp (hall u hu)
      · intro hall u hu
        exact (himage i a z u).mpr (hall u hu)
    rw [hfilter]
  have hdiff (a b : Fin n) (z : Fin r → Fin n) :
      (T.filter fun t => Q a z t ≠ Q b z t) ⊆
        (T.filter fun t => a ∈ t ∧
          ∀ u ∈ t.erase a, u ∈ Finset.univ.image z) ∪
        (T.filter fun t => b ∈ t ∧
          ∀ u ∈ t.erase b, u ∈ Finset.univ.image z) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_union] at ht ⊢
    rcases ht with ⟨ht, hd⟩
    by_cases ha : Q a z t
    · have hb : ¬Q b z t := by
        intro hb
        exact hd (propext ⟨fun _ => hb, fun _ => ha⟩)
      dsimp [Q] at ha hb
      push Not at hb
      obtain ⟨u, hut, hub, huz⟩ := hb
      have hua : u = a := (ha u hut).resolve_right huz
      subst u
      left
      refine ⟨ht, hut, ?_⟩
      intro u hu
      exact (ha u (Finset.mem_of_mem_erase hu)).resolve_left
        (Finset.ne_of_mem_erase hu)
    · have hb : Q b z t := by
        by_contra hb
        exact hd (propext
          ⟨fun h => (ha h).elim, fun h => (hb h).elim⟩)
      dsimp [Q] at ha hb
      push Not at ha
      obtain ⟨u, hut, hua, huz⟩ := ha
      have hub : u = b := (hb u hut).resolve_right huz
      subst u
      right
      refine ⟨ht, hut, ?_⟩
      intro u hu
      exact (hb u (Finset.mem_of_mem_erase hu)).resolve_left
        (Finset.ne_of_mem_erase hu)
  have hchange (i : Fin (r + 1)) (a b : Fin n) (z : Fin r → Fin n) :
      |f (e i (a, z)) - f (e i (b, z))| ≤ A a z + A b z := by
    rw [hcount, hcount]
    calc
      |(((T.filter (Q a z)).card : ℝ) -
          ((T.filter (Q b z)).card : ℝ))| ≤
          ((T.filter fun t => Q a z t ≠ Q b z t).card : ℝ) :=
        finite_filter_card_difference T (Q a z) (Q b z)
      _ ≤ (((T.filter fun t => a ∈ t ∧
            ∀ u ∈ t.erase a, u ∈ Finset.univ.image z) ∪
          (T.filter fun t => b ∈ t ∧
            ∀ u ∈ t.erase b, u ∈ Finset.univ.image z)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (hdiff a b z)
      _ ≤ A a z + A b z := by
        dsimp [A]
        exact_mod_cast Finset.card_union_le
          (T.filter fun t => a ∈ t ∧
            ∀ u ∈ t.erase a, u ∈ Finset.univ.image z)
          (T.filter fun t => b ∈ t ∧
            ∀ u ∈ t.erase b, u ∈ Finset.univ.image z)
  have hupdate (i : Fin (r + 1)) (a b : Fin n) (z : Fin r → Fin n) :
      Function.update (e i (a, z)) i b = e i (b, z) := by
    funext j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩ <;>
      simp [e]
  have hsq (i : Fin (r + 1)) (a b : Fin n) (z : Fin r → Fin n) :
      (f (e i (a, z)) - f (e i (b, z))) ^ 2 ≤
        2 * (A a z) ^ 2 + 2 * (A b z) ^ 2 := by
    calc
      (f (e i (a, z)) - f (e i (b, z))) ^ 2 =
          |f (e i (a, z)) - f (e i (b, z))| ^ 2 := by
        rw [sq_abs]
      _ ≤ (A a z + A b z) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (hchange i a b z) 2
      _ ≤ _ := by
        nlinarith [sq_nonneg (A a z - A b z)]
  have hcoordinate (i : Fin (r + 1)) :
      (∑ x, ∑ y,
          (f x - f (Function.update x i y)) ^ 2) ≤
        4 * (n : ℝ) * ∑ v, ∑ z, (A v z) ^ 2 := by
    calc
      (∑ x, ∑ y, (f x - f (Function.update x i y)) ^ 2) =
          ∑ z, ∑ a, ∑ b,
            (f (e i (a, z)) - f (e i (b, z))) ^ 2 := by
        rw [← (e i).sum_comp, Fintype.sum_prod_type_right]
        apply Finset.sum_congr rfl
        intro z hz
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        rw [hupdate]
      _ ≤ ∑ z, ∑ a, ∑ b,
          (2 * (A a z) ^ 2 + 2 * (A b z) ^ 2) := by
        exact Finset.sum_le_sum fun z hz =>
          Finset.sum_le_sum fun a ha =>
            Finset.sum_le_sum fun b hb => hsq i a b z
      _ = 4 * (n : ℝ) * ∑ z, ∑ v, (A v z) ^ 2 := by
        simp_rw [Finset.sum_add_distrib]
        simp
        simp_rw [Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro z hz
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro v hv
        ring
      _ = _ := by rw [Finset.sum_comm]
  have hupdates :
      (∑ i, ∑ x, ∑ y,
          (f x - f (Function.update x i y)) ^ 2) ≤
        4 * (n : ℝ) * (r + 1 : ℝ) *
          ∑ v, ∑ z, (A v z) ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin (r + 1),
          4 * (n : ℝ) * ∑ v, ∑ z, (A v z) ^ 2 :=
        Finset.sum_le_sum fun i hi => hcoordinate i
      _ = _ := by simp; ring
  have hes := finite_product_efron_stein hn f
  have hmean :
      (∑ z, f z) / (n : ℝ) ^ (r + 1) =
        sampled_triangle_mean T (r + 1) := by
    simp [f, sampled_triangle_mean]
  rw [hmean] at hes
  have hraw := hes.trans hupdates
  have hsum_nonneg : 0 ≤ ∑ v, ∑ z, (A v z) ^ 2 :=
    Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hunnormalized :
      (∑ x, (f x - sampled_triangle_mean T (r + 1)) ^ 2) ≤
        2 * (r + 1 : ℝ) * ∑ v, ∑ z, (A v z) ^ 2 := by
    nlinarith [hraw]
  have hvariance :
      sampled_triangle_variance T (r + 1) ≤
        2 * ((r + 1 : ℝ) / (n : ℝ)) *
          ((∑ v, ∑ z, (A v z) ^ 2) / (n : ℝ) ^ r) := by
    rw [sampled_triangle_variance]
    simp only [Fintype.card_fun, Fintype.card_fin]
    norm_num only [Nat.cast_pow]
    change (∑ x, (f x - sampled_triangle_mean T (r + 1)) ^ 2) /
        (n : ℝ) ^ (r + 1) ≤ _
    calc
      _ ≤ (2 * (r + 1 : ℝ) * ∑ v, ∑ z, (A v z) ^ 2) /
          (n : ℝ) ^ (r + 1) :=
        div_le_div_of_nonneg_right hunnormalized (by positivity)
      _ = _ := by
        rw [pow_succ]
        field_simp
  have hcompletion := triangle_completion_second_moment_bound T hT hn hrn
  have hcompletion' :
      ((∑ v, ∑ z, (A v z) ^ 2) / (n : ℝ) ^ r) ≤
        3 * T.card * (((r + 1 : ℝ) / (n : ℝ)) ^ 2) +
          (∑ v, ∑ w, (pair_triangle_degree T v w : ℝ) ^ 2) *
            (((r + 1 : ℝ) / (n : ℝ)) ^ 3) +
          (∑ v, (vertex_triangle_degree T v : ℝ) ^ 2) *
            (((r + 1 : ℝ) / (n : ℝ)) ^ 4) := by
    dsimp [A]
    convert hcompletion using 1 <;> ring
  calc
    sampled_triangle_variance T (r + 1) ≤
        2 * ((r + 1 : ℝ) / (n : ℝ)) *
          ((∑ v, ∑ z, (A v z) ^ 2) / (n : ℝ) ^ r) := hvariance
    _ ≤ 2 * ((r + 1 : ℝ) / (n : ℝ)) *
        (3 * T.card * (((r + 1 : ℝ) / (n : ℝ)) ^ 2) +
          (∑ v, ∑ w, (pair_triangle_degree T v w : ℝ) ^ 2) *
            (((r + 1 : ℝ) / (n : ℝ)) ^ 3) +
          (∑ v, (vertex_triangle_degree T v : ℝ) ^ 2) *
            (((r + 1 : ℝ) / (n : ℝ)) ^ 4)) :=
      mul_le_mul_of_nonneg_left hcompletion' (by positivity)
    _ = _ := by
      field_simp
      ring

@[blueprint "lem:sampled-triangle-moment-bounds"
  (statement := /-- There are absolute real constants $c_1,c_2>0$ such that, for every $n,s\in\mathbb N$ and every finite family $T$ of three-element subsets of $[n]$, if $3\leq s$ and $2s\leq n$, then the following holds. Sample $s$ elements of $[n]$ independently and uniformly with replacement, and let $X_T$ count the members of $T$ all of whose vertices occur in the sample. Then
  \[
  \mathbb E X_T\geq c_1|T|s^3/n^3
  \]
  and
  \[
  \operatorname{Var}(X_T)\leq c_2\bigl(\mathbb E X_T+\sum_i d_T(i)^2s^5/n^5+\sum_{i,j}d_T(i,j)^2s^4/n^4\bigr),
  \]
  where $d_T(i)$ is the number of members of $T$ containing $i$, and $d_T(i,j)$ is the number containing both $i$ and $j$; the last sum ranges over all ordered pairs $(i,j)\in[n]^2$. -/)
  (proof := /-- Take $c_1=1/250$ and $c_2=1500$. The mean estimate is exactly \cref{lem:sampled-triangle-mean-lower-bound}; in particular, $|T|s^3/n^3\leq250\mathbb E X_T$. Write $s=r+1$, which is possible because $s\geq3$. The variance estimate \cref{lem:sampled-triangle-variance-upper-bound} gives
  \[
  \operatorname{Var}(X_T)\leq
  6|T|s^3/n^3+2\sum_{i,j}d_T(i,j)^2s^4/n^4
  +2\sum_i d_T(i)^2s^5/n^5.
  \]
  Substitute the preceding mean bound into its first term. The other two displayed terms are nonnegative, and $2\leq1500$, so enlarging all three coefficients to $1500$ yields the claimed upper bound. -/)
  (title := /-- First and Second Moments of the Sampled Triangle Count -/)
  (latexEnv := "lemma")]
lemma sampled_triangle_moment_bounds :
    ∃ cLower cUpper : ℝ, 0 < cLower ∧ 0 < cUpper ∧
      ∀ (n : ℕ) (T : Finset (Finset (Fin n))) (s : ℕ),
        (∀ t ∈ T, t.card = 3) → 3 ≤ s → 2 * s ≤ n →
          cLower * T.card * (s : ℝ) ^ (3 : ℕ) / (n : ℝ) ^ (3 : ℕ) ≤
              sampled_triangle_mean T s ∧
            sampled_triangle_variance T s ≤ cUpper *
              (sampled_triangle_mean T s +
                (∑ i, (vertex_triangle_degree T i : ℝ) ^ (2 : ℕ)) *
                    (s : ℝ) ^ (5 : ℕ) / (n : ℝ) ^ (5 : ℕ) +
                (∑ i, ∑ j, (pair_triangle_degree T i j : ℝ) ^ (2 : ℕ)) *
                    (s : ℝ) ^ (4 : ℕ) / (n : ℝ) ^ (4 : ℕ)) := by
  refine ⟨(1 / 250 : ℝ), 1500, by norm_num, by norm_num, ?_⟩
  intro n T s hT hs hsn
  have hn : 0 < n := by omega
  have hmean := sampled_triangle_mean_lower_bound T s hT hs hsn
  refine ⟨hmean, ?_⟩
  let r := s - 1
  have hrs : r + 1 = s := by
    dsimp [r]
    omega
  have hrn : r + 1 ≤ n := by omega
  have hvar :=
    sampled_triangle_variance_upper_bound (r := r) T hT hn hrn
  rw [hrs] at hvar
  have hrsR : (r : ℝ) + 1 = (s : ℝ) := by exact_mod_cast hrs
  rw [hrsR] at hvar
  let M : ℝ := sampled_triangle_mean T s
  let X : ℝ := (T.card : ℝ) * (s : ℝ) ^ 3 / (n : ℝ) ^ 3
  let V : ℝ :=
    (∑ i, (vertex_triangle_degree T i : ℝ) ^ 2) *
      (s : ℝ) ^ 5 / (n : ℝ) ^ 5
  let P : ℝ :=
    (∑ i, ∑ j, (pair_triangle_degree T i j : ℝ) ^ 2) *
      (s : ℝ) ^ 4 / (n : ℝ) ^ 4
  have hX : X ≤ 250 * M := by
    dsimp [X, M]
    calc
      (T.card : ℝ) * (s : ℝ) ^ 3 / (n : ℝ) ^ 3 =
          250 * ((1 / 250 : ℝ) * T.card * (s : ℝ) ^ 3 /
            (n : ℝ) ^ 3) := by ring
      _ ≤ 250 * sampled_triangle_mean T s :=
        mul_le_mul_of_nonneg_left hmean (by norm_num)
  have hV : 0 ≤ V := by
    dsimp [V]
    apply div_nonneg
    · exact mul_nonneg
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        (pow_nonneg (by positivity) _)
    · positivity
  have hP : 0 ≤ P := by
    dsimp [P]
    apply div_nonneg
    · exact mul_nonneg
        (Finset.sum_nonneg fun _ _ =>
          Finset.sum_nonneg fun _ _ => sq_nonneg _)
        (pow_nonneg (by positivity) _)
    · positivity
  have hvar' : sampled_triangle_variance T s ≤
      6 * X + 2 * P + 2 * V := by
    dsimp [X, P, V]
    convert hvar using 1 <;> ring
  change sampled_triangle_variance T s ≤ 1500 * (M + V + P)
  nlinarith

@[blueprint "def:clean-input-canonicalize"
  (statement := /-- The canonical cleaning of a real matrix sets diagonal entries to zero, retains a positive symmetric off-diagonal pair, and replaces every other off-diagonal pair by one. -/)
  (title := /-- Canonical Cleaning of a Matrix -/)
  (latexEnv := "definition")]
noncomputable def clean_input_canonicalize {n : ℕ} (M : metric_matrix n) :
    metric_matrix n := fun i j =>
  if i = j then 0
  else if M i j = M j i ∧ 0 < M i j ∧ 0 < M j i then M i j else 1

@[blueprint "lem:clean-input-canonicalize-clean"
  (statement := /-- The canonical cleaning of every real matrix is clean. -/)
  (proof := /-- The diagonal clause gives zero diagonal entries. Off the diagonal, the retained entries are positive by the retention condition and all replacement entries equal one. The retention condition is invariant under exchanging the two indices, and retained pairs have equal values, so the cleaned matrix is symmetric. -/)
  (title := /-- Canonical Cleaning Is Clean -/)
  (latexEnv := "lemma")]
lemma clean_input_canonicalize_clean {n : ℕ} (M : metric_matrix n) :
    clean_matrix (clean_input_canonicalize M) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp [clean_input_canonicalize]
  · intro i j hij
    simp only [clean_input_canonicalize, if_neg hij]
    split_ifs with h
    · exact h.2.1
    · norm_num
  · intro i j
    by_cases hij : i = j
    · subst j
      simp [clean_input_canonicalize]
    · simp only [clean_input_canonicalize, if_neg hij, if_neg (Ne.symm hij)]
      by_cases h : M i j = M j i ∧ 0 < M i j ∧ 0 < M j i
      · rw [if_pos h]
        rw [if_pos ⟨h.1.symm, h.2.2, h.2.1⟩]
        exact h.1
      · rw [if_neg h]
        rw [if_neg]
        intro hrev
        exact h ⟨hrev.1.symm, hrev.2.2, hrev.2.1⟩

@[blueprint "lem:clean-input-canonicalize-metric"
  (statement := /-- Canonical cleaning fixes every matrix that already defines a metric. -/)
  (proof := /-- A metric matrix is clean by \cref{def:metric-matrix-property}. Its diagonal entries are therefore zero, and each off-diagonal pair is symmetric and strictly positive, so every branch of \cref{def:clean-input-canonicalize} returns the original entry. -/)
  (title := /-- Canonical Cleaning Fixes Metrics -/)
  (latexEnv := "lemma")]
lemma clean_input_canonicalize_metric {n : ℕ} {M : metric_matrix n}
    (hM : metric_matrix_property M) : clean_input_canonicalize M = M := by
  classical
  funext i j
  rcases hM.1 with ⟨hdiag, hpos, hsymm⟩
  by_cases hij : i = j
  · subst j
    simp [clean_input_canonicalize, hdiag]
  · simp [clean_input_canonicalize, hij, hsymm, hpos i j hij,
      hpos j i (Ne.symm hij)]

@[blueprint "lem:clean-input-canonicalize-local"
  (statement := /-- If two matrices agree at both orientations of a pair $(i,j)$, then their canonical cleanings agree at $(i,j)$. -/)
  (proof := /-- Substitute the two assumed entry equalities into the case distinction in \cref{def:clean-input-canonicalize}. -/)
  (title := /-- Canonical Cleaning Is Pairwise Local -/)
  (latexEnv := "lemma")]
lemma clean_input_canonicalize_local {n : ℕ} {M N : metric_matrix n} {i j : Fin n}
    (hij : M i j = N i j) (hji : M j i = N j i) :
    clean_input_canonicalize M i j = clean_input_canonicalize N i j := by
  classical
  simp [clean_input_canonicalize, hij, hji]

@[blueprint "lem:clean-input-canonicalize-far"
  (statement := /-- If $M$ is $\varepsilon$-far from the metric property and canonical cleaning changes fewer than $\varepsilon n^2/2$ entries, then the cleaned matrix is $\varepsilon/2$-far from the metric property. -/)
  (proof := /-- Fix a metric matrix $N$. Apply \cref{lem:finite-filter-card-difference} to the predicates that an entry of $M$, respectively its canonical cleaning, differs from $N$. The resulting reverse triangle inequality bounds the Hamming distance from the cleaned matrix to $N$ below by the distance from $M$ to $N$ minus the number of entries changed by cleaning. The two hypotheses then give the claimed $\varepsilon n^2/2$ lower bound. -/)
  (title := /-- Farness Survives a Small Canonical Cleaning -/)
  (latexEnv := "lemma")]
lemma clean_input_canonicalize_far {n : ℕ} {ε : ℝ} {M : metric_matrix n}
    (hfar : epsilon_far_from_metric ε M)
    (hsmall : (matrix_hamming_distance M (clean_input_canonicalize M) : ℝ) <
      ε * (n : ℝ) ^ (2 : ℕ) / 2) :
    epsilon_far_from_metric (ε / 2) (clean_input_canonicalize M) := by
  classical
  intro N hN
  have hMN := hfar N hN
  have hdiff := finite_filter_card_difference
    (Finset.univ.product Finset.univ)
    (fun p : Fin n × Fin n => M p.1 p.2 ≠ N p.1 p.2)
    (fun p : Fin n × Fin n => clean_input_canonicalize M p.1 p.2 ≠ N p.1 p.2)
  have hxor :
      ((Finset.univ.product Finset.univ).filter (fun p : Fin n × Fin n =>
        (M p.1 p.2 ≠ N p.1 p.2) ≠
          (clean_input_canonicalize M p.1 p.2 ≠ N p.1 p.2))).card ≤
        ((Finset.univ.product Finset.univ).filter (fun p : Fin n × Fin n =>
          M p.1 p.2 ≠ clean_input_canonicalize M p.1 p.2)).card := by
    apply Finset.card_le_card
    intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    refine ⟨hp.1, ?_⟩
    intro heq
    apply hp.2
    simpa [heq]
  have htri : (matrix_hamming_distance M N : ℝ) -
      matrix_hamming_distance (clean_input_canonicalize M) N ≤
        matrix_hamming_distance M (clean_input_canonicalize M) := by
    rw [matrix_hamming_distance, matrix_hamming_distance, matrix_hamming_distance]
    exact (le_abs_self _).trans (hdiff.trans (by exact_mod_cast hxor))
  linarith

@[blueprint "def:clean-input-uniform-pmf"
  (statement := /-- On a nonempty finite type $\alpha$, the uniform probability mass function assigns mass $|\alpha|^{-1}$ to every element. -/)
  (title := /-- Uniform Probability Mass Function on a Finite Type -/)
  (latexEnv := "definition")]
noncomputable def clean_input_uniform_pmf (α : Type) [Fintype α] [Nonempty α] : PMF α :=
  PMF.ofFintype (fun _ => (Fintype.card α : ENNReal)⁻¹) (by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by simp) (by simp))

@[blueprint "lem:clean-input-reduction-sampling"
  (statement := /-- Let $D$ be a subset of a nonempty finite type $\alpha$. If $t|D|\geq 2|\alpha|$, then $t$ independent uniform samples from $\alpha$ hit $D$ with probability at least $2/3$. -/)
  (proof := /-- By \cref{def:clean-input-uniform-pmf}, the samples that avoid $D$ are precisely the functions from $[t]$ to the complement of $D$, so their proportion is $(1-|D|/|\alpha|)^t$. If the complement is empty the result is immediate. Otherwise Bernoulli's inequality, applied after dividing by the complement size, shows that the ratio of all samples to avoiding samples is at least $1+t|D|/(|\alpha|-|D|)\geq3$. Hence the avoiding probability is at most $1/3$, and the hitting probability is at least $2/3$. -/)
  (title := /-- Repeated Uniform Sampling Hits a Large Subset -/)
  (latexEnv := "lemma")]
lemma clean_input_reduction_sampling {α : Type} [Fintype α] [Nonempty α] [DecidableEq α]
    (D : Finset α) (t : ℕ) (ht : 2 * Fintype.card α ≤ t * D.card) :
    (clean_input_uniform_pmf (Fin t → α)).map
        (fun x => decide (∃ i, x i ∈ D)) true ≥ (2 : ENNReal) / 3 := by
  classical
  let N := Fintype.card α
  let d := D.card
  let c := N - d
  have hN : 0 < N := Fintype.card_pos
  have hdN : d ≤ N := by
    dsimp [d, N]
    exact Finset.card_le_univ D
  have hcN : c ≤ N := Nat.sub_le N d
  have htpos : 0 < t := by
    by_contra h
    have htzero : t = 0 := Nat.eq_zero_of_not_pos h
    subst t
    simp only [zero_mul] at ht
    omega
  have hpower : 3 * c ^ t ≤ N ^ t := by
    by_cases hc : c = 0
    · simp [hc, htpos]
    · have htd : 2 * c ≤ t * d := (Nat.mul_le_mul_left 2 hcN).trans ht
      have hmul : 2 * c ^ t ≤ t * c ^ (t - 1) * d := by
        have hm := Nat.mul_le_mul_left (c ^ (t - 1)) htd
        rw [show c ^ t = c ^ (t - 1) * c by
          rw [← pow_succ]
          congr
          omega]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hm
      have hbern : c ^ t + t * c ^ (t - 1) * d ≤ (c + d) ^ t :=
        pow_add_mul_le_add_pow (Nat.zero_le c) (Nat.zero_le (2 * c + d)) t
      calc
        3 * c ^ t = c ^ t + 2 * c ^ t := by omega
        _ ≤ c ^ t + t * c ^ (t - 1) * d := Nat.add_le_add_left hmul _
        _ ≤ (c + d) ^ t := hbern
        _ = N ^ t := by rw [Nat.sub_add_cancel hdN]
  have havoid :
      Fintype.card {x : Fin t → α // ¬ ∃ i, x i ∈ D} = c ^ t := by
    simp only [not_exists]
    calc
      Fintype.card {x : Fin t → α // ∀ i, x i ∉ D} =
          Fintype.card (Fin t → {a : α // a ∉ D}) :=
        Fintype.card_congr
          (@Equiv.subtypePiEquivPi (Fin t) (fun _ => α) (fun _ a => a ∉ D))
      _ = (Fintype.card {a : α // a ∉ D}) ^ t := by simp
      _ = c ^ t := by simp [c, N, d, Fintype.card_subtype_compl]
  have htotal : Fintype.card (Fin t → α) = N ^ t := by simp [N]
  have hpartition := Fintype.card_subtype_compl
    (fun x : Fin t → α => ∃ i, x i ∈ D)
  have hhit :
      2 * Fintype.card (Fin t → α) ≤
        3 * Fintype.card {x : Fin t → α // ∃ i, x i ∈ D} := by
    rw [htotal]
    rw [havoid] at hpartition
    omega
  simp only [PMF.map_apply]
  simp only [clean_input_uniform_pmf, PMF.ofFintype_apply,
    true_eq_decide_iff, tsum_fintype]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  apply (ENNReal.le_div_iff_mul_le (by simp) (by simp)).2
  rw [ENNReal.div_eq_inv_mul]
  have hhit' :
      (2 : ENNReal) * Fintype.card (Fin t → α) ≤
        3 * ({x ∈ (Finset.univ : Finset (Fin t → α)) | ∃ i, x i ∈ D}.card : ENNReal) := by
    have hhitNat :
        2 * Fintype.card (Fin t → α) ≤
          3 * {x ∈ (Finset.univ : Finset (Fin t → α)) | ∃ i, x i ∈ D}.card := by
      simpa [Fintype.card_subtype] using hhit
    exact_mod_cast hhitNat
  calc
    3⁻¹ * 2 * Fintype.card (Fin t → α) =
        3⁻¹ * ((2 : ENNReal) * Fintype.card (Fin t → α)) := by ring
    _ ≤ 3⁻¹ * (3 * ({x ∈ (Finset.univ : Finset (Fin t → α)) |
        ∃ i, x i ∈ D}.card : ENNReal)) :=
      mul_le_mul_left' hhit' _
    _ = ({x ∈ (Finset.univ : Finset (Fin t → α)) | ∃ i, x i ∈ D}.card : ENNReal) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel]
      · simp
      · norm_num
      · norm_num

@[blueprint "def:clean-input-product-pmf"
  (statement := /-- The product of probability mass functions $p$ and $q$ is obtained by sampling from $p$ and then independently from $q$. -/)
  (title := /-- Product of Probability Mass Functions -/)
  (latexEnv := "definition")]
noncomputable def clean_input_product_pmf {α β : Type} (p : PMF α) (q : PMF β) :
    PMF (α × β) := p.bind fun a => q.map fun b => (a, b)

@[blueprint "lem:clean-input-product-pmf-bounds"
  (statement := /-- For independent seeds with Boolean acceptance predicates $f$ and $g$, the conjunction rejects with probability at least that of either predicate alone; if $g$ is always true, its acceptance probability equals that of $f$. -/)
  (proof := /-- Expand the product law from \cref{def:clean-input-product-pmf} and the push-forward probabilities as iterated nonnegative sums. If $f(a)$ is false, every inner outcome is false and the inner mass is one, yielding the first lower bound. Interchanging the independent sums gives the second. If $g$ is identically true, the conjunction equals $f$ pointwise, and summing the second distribution to one gives the acceptance equality. -/)
  (title := /-- Probability Bounds for Conjoined Independent Tests -/)
  (latexEnv := "lemma")]
lemma clean_input_product_pmf_bounds {α β : Type} (p : PMF α) (q : PMF β)
    (f : α → Bool) (g : β → Bool) :
    (p.map f false ≤
        (clean_input_product_pmf p q).map (fun z => f z.1 && g z.2) false) ∧
      (q.map g false ≤
        (clean_input_product_pmf p q).map (fun z => f z.1 && g z.2) false) ∧
      ((∀ b, g b = true) →
        (clean_input_product_pmf p q).map (fun z => f z.1 && g z.2) true =
          p.map f true) := by
  have hleft {γ δ : Type} (r : PMF γ) (s : PMF δ)
      (u : γ → Bool) (v : δ → Bool) :
      r.map u false ≤
        (clean_input_product_pmf r s).map (fun z => u z.1 && v z.2) false := by
    rw [clean_input_product_pmf, PMF.map_bind]
    simp_rw [PMF.map_comp]
    change r.map u false ≤ (r.bind fun a => s.map fun b => u a && v b) false
    simp only [PMF.bind_apply, PMF.map_apply]
    apply ENNReal.tsum_le_tsum
    intro a
    cases hua : u a <;> simp [hua, ENNReal.tsum_mul_left]
  have hswap :
      (clean_input_product_pmf p q).map (fun z => f z.1 && g z.2) =
        (clean_input_product_pmf q p).map (fun z => g z.1 && f z.2) := by
    simp only [clean_input_product_pmf, PMF.map_bind, PMF.map_comp,
      Function.comp_apply]
    change (p.bind fun a => q.bind fun b => PMF.pure (f a && g b)) =
      (q.bind fun b => p.bind fun a => PMF.pure (g b && f a))
    simpa [Bool.and_comm] using
      PMF.bind_comm p q (fun a b => PMF.pure (f a && g b))
  refine ⟨hleft p q f g, ?_⟩
  constructor
  · rw [hswap]
    exact hleft q p g f
  · intro hg
    rw [clean_input_product_pmf, PMF.map_bind]
    simp_rw [PMF.map_comp]
    change (p.bind fun a => q.map (fun b => f a && g b)) true = p.map f true
    have hout : ∀ a b, (f a && g b) = f a := by
      intro a b
      rw [hg b]
      exact Bool.and_true _
    simp_rw [hout]
    have hconst : ∀ a, q.map (fun _ : β => f a) = PMF.pure (f a) := by
      intro a
      change q.map (Function.const β (f a)) = PMF.pure (f a)
      exact PMF.map_const q (f a)
    simp_rw [hconst]
    exact congrArg (fun r : PMF Bool => r true) (PMF.bind_pure_comp f p)

@[blueprint "lem:clean-metric-tester-upper-bound"
  (statement := /-- There are absolute constants $n_0\in\mathbb N$ and $C>0$ such that, for every $n\geq n_0$ and $0<\varepsilon<1$, a non-adaptive tester on clean matrices has perfect completeness, rejects every clean $\varepsilon$-far matrix with probability at least $2/3$, and makes at most $C n^{2/3}/\varepsilon^{4/3}$ queries for every random seed. -/)
  (proof := /-- Run the high-degree subroutine and the sampled-violation subroutine with independent randomness, rejecting if either subroutine finds a violation. In the low-degree case, \,\cref{lem:bounded-degree-violating-family} supplies a large family $T$ with controlled vertex and pair degrees and with $T\subseteq T(M)$. By \,\cref{def:violating-triangles,def:violating-triangle}, every member of $T(M)$, and hence every member of $T$, has cardinality three. Thus \,\cref{lem:sampled-triangle-moment-bounds} applies to $T$; its estimates, followed by the Chebyshev inequality and a constant number of repetitions, give rejection probability at least $5/6$ for the sampled-violation subroutine. In the complementary high-degree case the source asserts the same $5/6$ guarantee for the high-degree subroutine but defers its proof to the appendix. Each subroutine accepts a metric matrix surely, so their composition has perfect completeness; a union-bound allocation of the constant failure probabilities gives soundness at least $2/3$. The two non-adaptive query sets may be fixed from their random seeds in advance, and the sum of their query bounds is at most a constant multiple of $n^{2/3}/\varepsilon^{4/3}$. -/)
  (title := /-- Metric Testing on Clean Matrices -/)
  (latexEnv := "lemma")]
lemma clean_metric_tester_upper_bound :
    ∃ n₀ : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∃ A : nonadaptive_matrix_tester n,
          tester_uses_at_most A (C * metric_testing_query_scale n ε) ∧
            clean_metric_tester_guarantee A ε := by
  classical
  refine ⟨100, 10^10, by norm_num, ?_⟩
  intro n hn ε hε₀ hε₁
  have hnpos : 0 < n := by omega
  letI : NeZero n := ⟨Nat.ne_of_gt hnpos⟩
  have hn100 : (100:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = ε ^ (1/3:ℝ) := ⟨_, rfl⟩
  obtain ⟨v, hvdef⟩ : ∃ v : ℝ, v = (n:ℝ) ^ (1/3:ℝ) := ⟨_, rfl⟩
  have hupos : 0 < u := by rw [hudef]; exact Real.rpow_pos_of_pos hε₀ _
  have hvpos : 0 < v := by rw [hvdef]; exact Real.rpow_pos_of_pos (by linarith) _
  have hu3 : u^3 = ε := by
    rw [hudef, ← Real.rpow_natCast (ε ^ (1/3:ℝ)) 3, ← Real.rpow_mul hε₀.le]
    norm_num
  have hv3 : v^3 = (n:ℝ) := by
    rw [hvdef, ← Real.rpow_natCast ((n:ℝ) ^ (1/3:ℝ)) 3, ← Real.rpow_mul (by positivity)]
    norm_num
  have hu1 : u ≤ 1 := by
    by_contra hc
    have hc' : 1 < u := lt_of_not_ge hc
    have hcube : 1 < u^3 := by nlinarith [sq_nonneg u, sq_nonneg (u-1), sq_nonneg (u+1)]
    rw [hu3] at hcube
    linarith
  have hv4 : 4 ≤ v := by
    by_contra hc
    have hc' : v < 4 := lt_of_not_ge hc
    have hcube : v^3 < 64 := by nlinarith [sq_nonneg v, sq_nonneg (v-4)]
    rw [hv3] at hcube
    linarith
  have hv2 : v^2 = (n:ℝ)^(2/3:ℝ) := by
    rw [hvdef, ← Real.rpow_natCast ((n:ℝ)^(1/3:ℝ)) 2, ← Real.rpow_mul (by positivity)]
    norm_num
  have hv43 : v^4 = (n:ℝ)^(4/3:ℝ) := by
    rw [hvdef, ← Real.rpow_natCast ((n:ℝ)^(1/3:ℝ)) 4, ← Real.rpow_mul (by positivity)]
    norm_num
  have hu4 : u^4 = ε^(4/3:ℝ) := by
    rw [hudef, ← Real.rpow_natCast (ε^(1/3:ℝ)) 4, ← Real.rpow_mul hε₀.le]
    norm_num
  have hQ : metric_testing_query_scale n ε = v^2/u^4 := by
    rw [metric_testing_query_scale, hv2, hu4]
  obtain ⟨H, hHdef⟩ : ∃ H : ℕ, H = ⌊u*v^4/16⌋₊ := ⟨_, rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R : ℕ, R = ⌊ε*(n:ℝ)/4⌋₊ := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s : ℕ, s = min ⌊26*v/u^2⌋₊ (n/2) := ⟨_, rfl⟩
  obtain ⟨t1, ht1def⟩ : ∃ t1 : ℕ, t1 =
      (if 16 ≤ u*v^4 then ⌈24*v^6/(u^3*(H:ℝ))⌉₊ else ⌈12*v^3/u^3⌉₊) := ⟨_, rfl⟩
  obtain ⟨t2, ht2def⟩ : ∃ t2 : ℕ, t2 = ⌈10^9*v^2/(u^4*(s:ℝ)^2)⌉₊ := ⟨_, rfl⟩
  have hVone : (1:ℝ) ≤ v^2/u^4 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hu1, hupos, hv4]
  have hs3 : 3 ≤ s := by
    have h1 : 26 ≤ ⌊26*v/u^2⌋₊ := by
      apply Nat.le_floor
      rw [le_div_iff₀ (by positivity)]
      push_cast
      nlinarith [hu1, hupos, hv4]
    have h2 : 3 ≤ n/2 := by omega
    rw [hsdef]
    omega
  have hsn : 2*s ≤ n := by
    have h1 : s ≤ n/2 := by rw [hsdef]; exact min_le_right _ _
    omega
  have hspos : (0:ℝ) < (s:ℝ) := by
    have : 0 < s := by omega
    exact_mod_cast this
  have hsu2 : u^2*(s:ℝ) ≤ 26*v := by
    have hfl : (s:ℝ) ≤ 26*v/u^2 := by
      have h1 : s ≤ ⌊26*v/u^2⌋₊ := by rw [hsdef]; exact min_le_left _ _
      have h2 : ((s:ℝ)) ≤ ((⌊26*v/u^2⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
      exact h2.trans (Nat.floor_le (by positivity))
    rw [le_div_iff₀ (by positivity)] at hfl
    linarith
  have huvs : u*v ≤ 4*(s:ℝ) := by
    rcases le_total ⌊26*v/u^2⌋₊ (n/2) with hc | hc
    · have hse : s = ⌊26*v/u^2⌋₊ := by rw [hsdef]; omega
      have hlt : 26*v/u^2 < (s:ℝ) + 1 := by
        rw [hse]
        exact Nat.lt_floor_add_one (26*v/u^2)
      have hw : (1:ℝ) ≤ v/u^2 := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [hu1, hupos, hv4]
      have hexp : 26*v/u^2 = 26*(v/u^2) := by ring
      rw [hexp] at hlt
      have huv2 : u*v ≤ 100*(v/u^2) := by
        rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
        nlinarith [hu1, hupos, hvpos, hv4]
      linarith
    · have hse : s = n/2 := by rw [hsdef]; omega
      have hs2 : (n:ℝ) ≤ 2*(s:ℝ) + 2 := by
        have : n ≤ 2*s + 2 := by omega
        exact_mod_cast this
      nlinarith [hu1, hupos, hvpos, hv4, hv3, hs2]
  have hHb : (H:ℝ) ≤ u*v^4/16 := by
    rw [hHdef]; exact Nat.floor_le (by positivity)
  have ht1b : (t1:ℝ) ≤ 769*(v^2/u^4) := by
    rw [ht1def]
    by_cases hbig : 16 ≤ u*v^4
    · rw [if_pos hbig]
      have hH1 : 1 ≤ H := by
        rw [hHdef]
        apply Nat.le_floor
        push_cast
        linarith
      have hHR1 : (1:ℝ) ≤ (H:ℝ) := by exact_mod_cast hH1
      have hHlow : u*v^4/32 ≤ (H:ℝ) := by
        have hlt : u*v^4/16 < (H:ℝ) + 1 := by
          rw [hHdef]
          exact Nat.lt_floor_add_one (u*v^4/16)
        rcases le_total (u*v^4/16) 2 with hx | hx
        · linarith
        · linarith
      have hHpos : (0:ℝ) < (H:ℝ) := by linarith
      have hup : 24*v^6/(u^3*(H:ℝ)) ≤ 768*v^2/u^4 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hHlow (by positivity : (0:ℝ) ≤ 768*v^2*u^3)]
      have hceil : (⌈24*v^6/(u^3*(H:ℝ))⌉₊ : ℝ) < 24*v^6/(u^3*(H:ℝ)) + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      have hVR : 768*v^2/u^4 = 768*(v^2/u^4) := by ring
      rw [hVR] at hup
      linarith
    · rw [if_neg hbig]
      have hsmall : u*v^4 < 16 := lt_of_not_ge hbig
      have hup : 12*v^3/u^3 ≤ 48*(v^2/u^4) := by
        rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hsmall, hupos, hvpos, hv4, sq_nonneg v,
          mul_le_mul_of_nonneg_left hsmall.le (by positivity : (0:ℝ) ≤ 12*v^2)]
      have hceil : (⌈12*v^3/u^3⌉₊ : ℝ) < 12*v^3/u^3 + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      linarith
  have ht2b : (t2:ℝ) ≤ 10^9*v^2/(u^4*(s:ℝ)^2) + 1 := by
    rw [ht2def]
    exact le_of_lt (Nat.ceil_lt_add_one (by positivity))
  have ht2low : 10^9*v^2/(u^4*(s:ℝ)^2) ≤ (t2:ℝ) := by
    rw [ht2def]
    exact Nat.le_ceil _
  have hs2b : (s:ℝ)^2 ≤ 676*(v^2/u^4) := by
    rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul hsu2 hsu2 (by positivity) (by positivity)]
  have hmoment : ∀ T : Finset (Finset (Fin n)), (∀ t ∈ T, t.card = 3) →
      ∀ hd hD : ℕ, (∀ v, vertex_triangle_degree T v ≤ hd) →
      (∀ v w, v ≠ w → pair_triangle_degree T v w ≤ hD) →
      (∑ y : Fin s → Fin n, ((sampled_triangle_count T y : ℝ))^2) / (n:ℝ)^s ≤
        (T.card:ℝ)^2 * ((s:ℝ)/n)^6 + 3*(hd:ℝ)*(T.card:ℝ)*((s:ℝ)/n)^5
          + 9*(hD:ℝ)*(T.card:ℝ)*((s:ℝ)/n)^4 + (T.card:ℝ)*((s:ℝ)/n)^3 := by
    intro T hT hd hD hdeg hpair
    have hn : 0 < n := hnpos
    classical
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    have hpowpos : (0:ℝ) < (n:ℝ)^s := by positivity
    have hcount : ∀ y : Fin s → Fin n, ((sampled_triangle_count T y : ℝ)) =
        ∑ t ∈ T, (if (∀ i ∈ t, i ∈ Finset.univ.image y) then (1:ℝ) else 0) := by
      intro y
      simp [sampled_triangle_count]
    have hsq : ∀ y : Fin s → Fin n, ((sampled_triangle_count T y : ℝ))^2 =
        ∑ t ∈ T, ∑ u ∈ T, (if (∀ i ∈ t ∪ u, i ∈ Finset.univ.image y) then (1:ℝ) else 0) := by
      intro y
      rw [hcount y, sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u hu => ?_
      have hiff : (∀ i ∈ t ∪ u, i ∈ Finset.univ.image y) ↔
          ((∀ i ∈ t, i ∈ Finset.univ.image y) ∧ (∀ i ∈ u, i ∈ Finset.univ.image y)) :=
        Finset.forall_mem_union
      by_cases hb : (∀ i ∈ t ∪ u, i ∈ Finset.univ.image y)
      · obtain ⟨h1, h2⟩ := hiff.mp hb
        rw [if_pos hb, if_pos h1, if_pos h2, mul_one]
      · rw [if_neg hb]
        have hno : ¬ ((∀ i ∈ t, i ∈ Finset.univ.image y) ∧
            (∀ i ∈ u, i ∈ Finset.univ.image y)) := fun hc => hb (hiff.mpr hc)
        by_cases h1 : (∀ i ∈ t, i ∈ Finset.univ.image y)
        · have h2 : ¬ (∀ i ∈ u, i ∈ Finset.univ.image y) := fun h2 => hno ⟨h1, h2⟩
          rw [if_neg h2, mul_zero]
        · rw [if_neg h1, zero_mul]

    have hswap : (∑ y : Fin s → Fin n, ((sampled_triangle_count T y : ℝ))^2) =
        ∑ t ∈ T, ∑ u ∈ T,
          ((Finset.univ.filter (fun y : Fin s → Fin n =>
            ∀ i ∈ t ∪ u, i ∈ Finset.univ.image y)).card : ℝ) := by
      rw [Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => hsq y), Finset.sum_comm]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u hu => ?_
      exact Finset.sum_boole _ _
    have hhit : ∀ U : Finset (Fin n),
        ((Finset.univ.filter (fun y : Fin s → Fin n =>
          ∀ i ∈ U, i ∈ Finset.univ.image y)).card : ℝ)
          ≤ (n:ℝ)^s * (((s:ℝ)/(n:ℝ))^U.card) := by
      intro U
      have h := finite_sample_hit_upper_probability (n := n) (s := s) hn U
      rw [Fintype.card_subtype] at h
      rw [div_pow]
      rw [div_le_iff₀ hpowpos] at h
      calc ((Finset.univ.filter (fun y : Fin s → Fin n =>
              ∀ i ∈ U, i ∈ Finset.univ.image y)).card : ℝ)
          ≤ (s:ℝ)^U.card / (n:ℝ)^U.card * (n:ℝ)^s := h
        _ = (n:ℝ)^s * ((s:ℝ)^U.card / (n:ℝ)^U.card) := by ring
    have hstep : (∑ y : Fin s → Fin n, ((sampled_triangle_count T y : ℝ))^2)
        ≤ (n:ℝ)^s * (∑ t ∈ T, ∑ u ∈ T, ((s:ℝ)/(n:ℝ))^((t ∪ u).card)) := by
      rw [hswap, Finset.mul_sum]
      refine Finset.sum_le_sum fun t ht => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun u hu => hhit (t ∪ u)
    obtain ⟨p, hpdef⟩ : ∃ p : ℝ, p = (s:ℝ)/(n:ℝ) := ⟨_, rfl⟩
    have hp0 : (0:ℝ) ≤ p := by rw [hpdef]; positivity
    have hpow6 : ∀ m : ℕ, m ≤ 3 → p^(6-m) ≤ p^6 + (if 1 ≤ m then p^5 else 0)
        + (if 2 ≤ m then p^4 else 0) + (if 3 ≤ m then p^3 else 0) := by
      intro m hm
      have h3 : (0:ℝ) ≤ p^3 := by positivity
      have h4 : (0:ℝ) ≤ p^4 := by positivity
      have h5 : (0:ℝ) ≤ p^5 := by positivity
      have h6 : (0:ℝ) ≤ p^6 := by positivity
      interval_cases m <;> norm_num <;> linarith
    have hinner : ∀ t ∈ T, (∑ u ∈ T, p^((t ∪ u).card)) ≤
        (T.card:ℝ)*p^6 + 3*(hd:ℝ)*p^5 + 9*(hD:ℝ)*p^4 + p^3 := by
      intro t ht
      have hbound : ∀ u ∈ T, p^((t ∪ u).card) ≤ p^6 + (if 1 ≤ (t ∩ u).card then p^5 else 0)
          + (if 2 ≤ (t ∩ u).card then p^4 else 0) + (if 3 ≤ (t ∩ u).card then p^3 else 0) := by
        intro u hu
        have hcards := Finset.card_union_add_card_inter t u
        rw [hT t ht, hT u hu] at hcards
        have hle : (t ∩ u).card ≤ 3 := by
          have := Finset.card_le_card (Finset.inter_subset_left (s₁ := t) (s₂ := u))
          rw [hT t ht] at this
          exact this
        have heq : (t ∪ u).card = 6 - (t ∩ u).card := by omega
        rw [heq]
        exact hpow6 _ hle
      have hsum1 := Finset.sum_le_sum hbound
      have hexpand : (∑ u ∈ T, (p^6 + (if 1 ≤ (t ∩ u).card then p^5 else 0)
            + (if 2 ≤ (t ∩ u).card then p^4 else 0) + (if 3 ≤ (t ∩ u).card then p^3 else 0)))
          = (T.card:ℝ)*p^6 + ((T.filter fun u => 1 ≤ (t ∩ u).card).card : ℝ)*p^5
            + ((T.filter fun u => 2 ≤ (t ∩ u).card).card : ℝ)*p^4
            + ((T.filter fun u => 3 ≤ (t ∩ u).card).card : ℝ)*p^3 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter]
        simp [Finset.sum_const, mul_comm]
      have hS1 : ((T.filter fun u => 1 ≤ (t ∩ u).card).card : ℝ) ≤ 3*(hd:ℝ) := by
        have hsub : (T.filter fun u => 1 ≤ (t ∩ u).card) ⊆
            t.biUnion (fun v => T.filter fun u => v ∈ u) := by
          intro u hu
          rw [Finset.mem_filter] at hu
          obtain ⟨huT, hcard⟩ := hu
          obtain ⟨v, hv⟩ := Finset.card_pos.mp hcard
          rw [Finset.mem_inter] at hv
          exact Finset.mem_biUnion.mpr ⟨v, hv.1, Finset.mem_filter.mpr ⟨huT, hv.2⟩⟩
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_biUnion_le (s := t) (t := fun v => T.filter fun u => v ∈ u)
        have h3 : ∑ v ∈ t, (T.filter fun u => v ∈ u).card ≤ ∑ _v ∈ t, hd :=
          Finset.sum_le_sum fun v hv => by simpa [vertex_triangle_degree] using hdeg v
        rw [Finset.sum_const, hT t ht, smul_eq_mul] at h3
        have h4 : (T.filter fun u => 1 ≤ (t ∩ u).card).card ≤ 3 * hd := by omega
        exact_mod_cast h4
      have hS2 : ((T.filter fun u => 2 ≤ (t ∩ u).card).card : ℝ) ≤ 9*(hD:ℝ) := by
        have hsub : (T.filter fun u => 2 ≤ (t ∩ u).card) ⊆
            (t ×ˢ t).biUnion (fun q => T.filter fun u => q.1 ≠ q.2 ∧ q.1 ∈ u ∧ q.2 ∈ u) := by
          intro u hu
          rw [Finset.mem_filter] at hu
          obtain ⟨huT, hcard⟩ := hu
          obtain ⟨v, hv, w, hw, hvw⟩ := Finset.one_lt_card.mp hcard
          rw [Finset.mem_inter] at hv hw
          exact Finset.mem_biUnion.mpr ⟨(v, w), Finset.mem_product.mpr ⟨hv.1, hw.1⟩,
            Finset.mem_filter.mpr ⟨huT, hvw, hv.2, hw.2⟩⟩
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_biUnion_le (s := t ×ˢ t)
          (t := fun q : Fin n × Fin n => T.filter fun u => q.1 ≠ q.2 ∧ q.1 ∈ u ∧ q.2 ∈ u)
        have h3 : ∑ q ∈ t ×ˢ t,
            (T.filter fun u => q.1 ≠ q.2 ∧ q.1 ∈ u ∧ q.2 ∈ u).card ≤ ∑ _q ∈ t ×ˢ t, hD := by
          refine Finset.sum_le_sum fun q hq => ?_
          by_cases hne : q.1 = q.2
          · have hemp : (T.filter fun u => q.1 ≠ q.2 ∧ q.1 ∈ u ∧ q.2 ∈ u) = ∅ :=
              Finset.filter_false_of_mem fun u hu hc => hc.1 hne
            simp [hemp]
          · have hmono : (T.filter fun u => q.1 ≠ q.2 ∧ q.1 ∈ u ∧ q.2 ∈ u) ⊆
                (T.filter fun u => q.1 ∈ u ∧ q.2 ∈ u) := by
              intro u hu
              rw [Finset.mem_filter] at hu ⊢
              exact ⟨hu.1, hu.2.2.1, hu.2.2.2⟩
            have hcard2 : (T.filter fun u => q.1 ∈ u ∧ q.2 ∈ u).card =
                pair_triangle_degree T q.1 q.2 := by simp [pair_triangle_degree]
            calc (T.filter fun u => q.1 ≠ q.2 ∧ q.1 ∈ u ∧ q.2 ∈ u).card
                ≤ (T.filter fun u => q.1 ∈ u ∧ q.2 ∈ u).card := Finset.card_le_card hmono
              _ = pair_triangle_degree T q.1 q.2 := hcard2
              _ ≤ hD := hpair q.1 q.2 hne
        rw [Finset.sum_const, Finset.card_product, hT t ht, smul_eq_mul] at h3
        have h4 : (T.filter fun u => 2 ≤ (t ∩ u).card).card ≤ 9 * hD := by omega
        exact_mod_cast h4
      have hS3 : ((T.filter fun u => 3 ≤ (t ∩ u).card).card : ℝ) ≤ 1 := by
        have hsub : (T.filter fun u => 3 ≤ (t ∩ u).card) ⊆ {t} := by
          intro u hu
          rw [Finset.mem_filter] at hu
          obtain ⟨huT, hcard⟩ := hu
          have h1 : t ∩ u = t := Finset.eq_of_subset_of_card_le Finset.inter_subset_left
            (by rw [hT t ht]; exact hcard)
          have h2 : t ∩ u = u := Finset.eq_of_subset_of_card_le Finset.inter_subset_right
            (by rw [hT u huT]; exact hcard)
          rw [Finset.mem_singleton, ← h1, h2]
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_singleton] at h1
        exact_mod_cast h1
      have h5 : (0:ℝ) ≤ p^5 := by positivity
      have h4 : (0:ℝ) ≤ p^4 := by positivity
      have h3 : (0:ℝ) ≤ p^3 := by positivity
      rw [hexpand] at hsum1
      nlinarith only [hsum1, hS1, hS2, hS3, h5, h4, h3]
    have hdouble : (∑ t ∈ T, ∑ u ∈ T, p^((t ∪ u).card)) ≤
        (T.card:ℝ)^2*p^6 + 3*(hd:ℝ)*(T.card:ℝ)*p^5 + 9*(hD:ℝ)*(T.card:ℝ)*p^4
          + (T.card:ℝ)*p^3 := by
      have h1 := Finset.sum_le_sum hinner
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_const, Finset.sum_const, Finset.sum_const, Finset.sum_const] at h1
      simp only [nsmul_eq_mul] at h1
      calc (∑ t ∈ T, ∑ u ∈ T, p^((t ∪ u).card))
          ≤ (T.card:ℝ) * ((T.card:ℝ)*p^6) + (T.card:ℝ) * (3*(hd:ℝ)*p^5)
              + (T.card:ℝ) * (9*(hD:ℝ)*p^4) + (T.card:ℝ) * p^3 := h1
        _ = _ := by ring
    rw [div_le_iff₀ hpowpos]
    rw [hpdef] at hdouble
    calc (∑ y : Fin s → Fin n, ((sampled_triangle_count T y : ℝ))^2)
        ≤ (n:ℝ)^s * (∑ t ∈ T, ∑ u ∈ T, ((s:ℝ)/(n:ℝ))^((t ∪ u).card)) := hstep
      _ ≤ (n:ℝ)^s * ((T.card:ℝ)^2 * ((s:ℝ)/n)^6 + 3*(hd:ℝ)*(T.card:ℝ)*((s:ℝ)/n)^5
            + 9*(hD:ℝ)*(T.card:ℝ)*((s:ℝ)/n)^4 + (T.card:ℝ)*((s:ℝ)/n)^3) := by
          exact mul_le_mul_of_nonneg_left hdouble (le_of_lt hpowpos)
      _ = ((T.card:ℝ)^2 * ((s:ℝ)/n)^6 + 3*(hd:ℝ)*(T.card:ℝ)*((s:ℝ)/n)^5
            + 9*(hD:ℝ)*(T.card:ℝ)*((s:ℝ)/n)^4 + (T.card:ℝ)*((s:ℝ)/n)^3) * (n:ℝ)^s := by ring
  have hhitcount : ∀ T : Finset (Finset (Fin n)), (∀ t ∈ T, t.card = 3) →
      ∀ hd hD : ℕ, (∀ v, vertex_triangle_degree T v ≤ hd) →
      (∀ v w, v ≠ w → pair_triangle_degree T v w ≤ hD) → 0 < T.card →
      (125000 * (1 + 3*(hd:ℝ)*(n:ℝ)/((T.card:ℝ)*(s:ℝ))
        + 9*(hD:ℝ)*(n:ℝ)^2/((T.card:ℝ)*(s:ℝ)^2)
        + (n:ℝ)^3/((T.card:ℝ)*(s:ℝ)^3)) ≤ (t2:ℝ)) →
      2 * (n:ℝ)^s ≤ (t2:ℝ) *
        ((Finset.univ.filter (fun y : Fin s → Fin n =>
          0 < sampled_triangle_count T y)).card : ℝ) := by
    intro T hT hd hD hdeg hpair hθ ht2
    have hn : 0 < n := hnpos
    have hs : 3 ≤ s := hs3
    classical
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    have hsR : (0:ℝ) < s := by exact_mod_cast (by omega : 0 < s)
    have hθR : (0:ℝ) < (T.card:ℝ) := by exact_mod_cast hθ
    have hpowpos : (0:ℝ) < (n:ℝ)^s := by positivity
    obtain ⟨p, hpdef⟩ : ∃ p:ℝ, p = (s:ℝ)/(n:ℝ) := ⟨_, rfl⟩
    have hppos : (0:ℝ) < p := by rw [hpdef]; positivity
    obtain ⟨A, hAdef⟩ : ∃ A:ℝ, A = ∑ y : Fin s → Fin n,
        (sampled_triangle_count T y : ℝ) := ⟨_, rfl⟩
    obtain ⟨B, hBdef⟩ : ∃ B:ℝ, B = ∑ y : Fin s → Fin n,
        ((sampled_triangle_count T y : ℝ))^2 := ⟨_, rfl⟩
    obtain ⟨K, hKdef⟩ : ∃ K:ℝ, K = ((Finset.univ.filter (fun y : Fin s → Fin n =>
        0 < sampled_triangle_count T y)).card : ℝ) := ⟨_, rfl⟩
    obtain ⟨W, hWdef⟩ : ∃ W:ℝ, W = (T.card:ℝ)^2*p^6 + 3*(hd:ℝ)*(T.card:ℝ)*p^5
        + 9*(hD:ℝ)*(T.card:ℝ)*p^4 + (T.card:ℝ)*p^3 := ⟨_, rfl⟩
    have hcardfun : (Fintype.card (Fin s → Fin n) : ℝ) = (n:ℝ)^s := by simp
    have hAlow : (n:ℝ)^s * ((1/250) * (T.card:ℝ) * p^3) ≤ A := by
      have hmean := sampled_triangle_mean_lower_bound T s hT hs hsn
      rw [sampled_triangle_mean, hcardfun, ← hAdef, le_div_iff₀ hpowpos] at hmean
      rw [hpdef, div_pow]
      calc (n:ℝ)^s * ((1/250) * (T.card:ℝ) * ((s:ℝ)^3/(n:ℝ)^3))
          = (1/250) * (T.card:ℝ) * (s:ℝ)^3/(n:ℝ)^3 * (n:ℝ)^s := by ring
        _ ≤ A := hmean
    have hApos : 0 < A := lt_of_lt_of_le (by positivity) hAlow
    have hBup : B ≤ (n:ℝ)^s * W := by
      have h := hmoment T hT hd hD hdeg hpair
      rw [div_le_iff₀ hpowpos] at h
      rw [hBdef, hWdef, hpdef]
      calc (∑ y : Fin s → Fin n, ((sampled_triangle_count T y : ℝ))^2)
          ≤ ((T.card:ℝ)^2 * ((s:ℝ)/n)^6 + 3*(hd:ℝ)*(T.card:ℝ)*((s:ℝ)/n)^5
            + 9*(hD:ℝ)*(T.card:ℝ)*((s:ℝ)/n)^4 + (T.card:ℝ)*((s:ℝ)/n)^3) * (n:ℝ)^s := h
        _ = (n:ℝ)^s * ((T.card:ℝ)^2*((s:ℝ)/n)^6 + 3*(hd:ℝ)*(T.card:ℝ)*((s:ℝ)/n)^5
            + 9*(hD:ℝ)*(T.card:ℝ)*((s:ℝ)/n)^4 + (T.card:ℝ)*((s:ℝ)/n)^3) := by ring
    have hAB : A ≤ B := by
      rw [hAdef, hBdef]
      refine Finset.sum_le_sum fun y _ => ?_
      have h1 : sampled_triangle_count T y ≤ (sampled_triangle_count T y)^2 :=
        Nat.le_self_pow (by norm_num) _
      exact_mod_cast h1
    have hBpos : 0 < B := lt_of_lt_of_le hApos hAB
    have hCS : A^2 ≤ K * B := by
      obtain ⟨S, hSdef⟩ : ∃ S : Finset (Fin s → Fin n), S =
          Finset.univ.filter (fun y : Fin s → Fin n =>
            0 < sampled_triangle_count T y) := ⟨_, rfl⟩
      have hAS : A = ∑ y ∈ S, (sampled_triangle_count T y : ℝ) := by
        rw [hAdef]
        refine (Finset.sum_subset (by rw [hSdef]; exact Finset.filter_subset _ _) ?_).symm
        intro y _ hy
        rw [hSdef, Finset.mem_filter] at hy
        have : sampled_triangle_count T y = 0 := by
          by_contra hc
          exact hy ⟨Finset.mem_univ _, Nat.pos_of_ne_zero hc⟩
        rw [this]; norm_num
      have hBS : ∑ y ∈ S, ((sampled_triangle_count T y : ℝ))^2 ≤ B := by
        rw [hBdef]
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (by rw [hSdef]; exact Finset.filter_subset _ _) ?_
        intro y _ _
        positivity
      have hKS : K = (S.card : ℝ) := by rw [hKdef, hSdef]
      obtain ⟨c, hcdef⟩ : ∃ c:ℝ, c = B / A := ⟨_, rfl⟩
      have hcpos : 0 < c := by rw [hcdef]; positivity
      have hpt : ∀ y ∈ S, (sampled_triangle_count T y : ℝ) ≤
          (((sampled_triangle_count T y : ℝ))^2/c + c)/2 := by
        intro y _
        obtain ⟨x, hx⟩ : ∃ x:ℝ, x = (sampled_triangle_count T y : ℝ) := ⟨_, rfl⟩
        rw [← hx, ← sub_nonneg]
        have hkey : (x^2/c + c)/2 - x = (x - c)^2/(2*c) := by
          field_simp
          ring
        rw [hkey]
        positivity
      have hsum := Finset.sum_le_sum hpt
      rw [← hAS] at hsum
      have hexpand : (∑ y ∈ S, (((sampled_triangle_count T y : ℝ))^2/c + c)/2)
          = (∑ y ∈ S, ((sampled_triangle_count T y : ℝ))^2)/c/2 + (S.card:ℝ)*c/2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_div,
          nsmul_eq_mul]
        ring
      rw [hexpand] at hsum
      have h1 : A ≤ B/c/2 + (S.card:ℝ)*c/2 := by
        have h2 : (∑ y ∈ S, ((sampled_triangle_count T y : ℝ))^2)/c/2 ≤ B/c/2 := by
          gcongr
        linarith only [hsum, h2]
      rw [hcdef] at h1
      have h3 : B/(B/A) = A := by field_simp
      rw [h3] at h1
      have h6 : A ≤ (S.card:ℝ)*(B/A) := by linarith only [h1]
      have h7 : A * A ≤ (S.card:ℝ)*(B/A) * A := mul_le_mul_of_nonneg_right h6 hApos.le
      have h8 : (S.card:ℝ)*(B/A) * A = (S.card:ℝ)*B := by field_simp
      rw [hKS]
      calc A^2 = A*A := by ring
        _ ≤ (S.card:ℝ)*(B/A)*A := h7
        _ = (S.card:ℝ)*B := h8
    have hKnonneg : 0 ≤ K := by rw [hKdef]; positivity
    have hident : 125000 * (1 + 3*(hd:ℝ)*(n:ℝ)/((T.card:ℝ)*(s:ℝ))
        + 9*(hD:ℝ)*(n:ℝ)^2/((T.card:ℝ)*(s:ℝ)^2)
        + (n:ℝ)^3/((T.card:ℝ)*(s:ℝ)^3)) * ((n:ℝ)^s * ((1/250) * (T.card:ℝ) * p^3))^2
        = 2 * (n:ℝ)^s * ((n:ℝ)^s * W) := by
      rw [hWdef, hpdef]
      field_simp
      ring
    have hstep1 : ((n:ℝ)^s * ((1/250) * (T.card:ℝ) * p^3))^2 ≤ K * B := by
      have haa : (0:ℝ) ≤ (n:ℝ)^s * ((1/250) * (T.card:ℝ) * p^3) := by positivity
      calc ((n:ℝ)^s * ((1/250) * (T.card:ℝ) * p^3))^2 ≤ A^2 := by
            nlinarith only [hAlow, haa]
        _ ≤ K * B := hCS
    have hstep2 : 2 * (n:ℝ)^s * ((n:ℝ)^s * W) ≤ (t2:ℝ) * (K * B) := by
      calc 2 * (n:ℝ)^s * ((n:ℝ)^s * W)
          = 125000 * (1 + 3*(hd:ℝ)*(n:ℝ)/((T.card:ℝ)*(s:ℝ))
              + 9*(hD:ℝ)*(n:ℝ)^2/((T.card:ℝ)*(s:ℝ)^2)
              + (n:ℝ)^3/((T.card:ℝ)*(s:ℝ)^3))
              * ((n:ℝ)^s * ((1/250) * (T.card:ℝ) * p^3))^2 := hident.symm
        _ ≤ (t2:ℝ) * ((n:ℝ)^s * ((1/250) * (T.card:ℝ) * p^3))^2 := by
            apply mul_le_mul_of_nonneg_right ht2 (by positivity)
        _ ≤ (t2:ℝ) * (K * B) := by
            apply mul_le_mul_of_nonneg_left hstep1
            positivity
    have hBpos' : 0 < B := hBpos
    have hfinal : 2 * (n:ℝ)^s * ((n:ℝ)^s * W) ≤ (t2:ℝ) * K * B := by
      calc 2 * (n:ℝ)^s * ((n:ℝ)^s * W) ≤ (t2:ℝ) * (K * B) := hstep2
        _ = (t2:ℝ) * K * B := by ring
    have hWB : (n:ℝ)^s * W ≥ B := hBup
    have h2 : 2 * (n:ℝ)^s * B ≤ (t2:ℝ) * K * B := by
      calc 2 * (n:ℝ)^s * B ≤ 2 * (n:ℝ)^s * ((n:ℝ)^s * W) := by
            apply mul_le_mul_of_nonneg_left hWB (by positivity)
        _ ≤ (t2:ℝ) * K * B := hfinal
    have h3 : 2 * (n:ℝ)^s ≤ (t2:ℝ) * K := le_of_mul_le_mul_right (by linarith only [h2]) hBpos
    rw [hKdef] at h3
    exact h3
  have harith : ∀ u v s θ hh hD : ℝ, ∀ nn : ℝ,
      0 < u → u ≤ 1 → 4 ≤ v → 3 ≤ s → nn = v^3 → u^2*s ≤ 26*v → u*v ≤ 4*s →
      19*u^3*v^6/240 ≤ θ → hh ≤ u*v^4/16 → hD ≤ 10*v^2/u → 0 ≤ hh → 0 ≤ hD →
      125000*(1 + 3*hh*nn/(θ*s) + 9*hD*nn^2/(θ*s^2) + nn^3/(θ*s^3))
        ≤ 10^9*v^2/(u^4*s^2) := by
    intro u v s θ hh hD nn hupos hu1 hv4 hs3 hn hu2s huv hθ hhb hDb hhnn hDnn
    have hspos : (0:ℝ) < s := by linarith
    have hvpos : (0:ℝ) < v := by linarith
    have hθ0 : (0:ℝ) < 19*u^3*v^6/240 := by positivity
    have hθpos : (0:ℝ) < θ := lt_of_lt_of_le hθ0 hθ
    have hnnpos : (0:ℝ) < nn := by rw [hn]; positivity
    have hR : (0:ℝ) < u^4*s^2 := by positivity
    have hsq : (u^2*s)*(u^2*s) ≤ (26*v)*(26*v) :=
      mul_le_mul hu2s hu2s (by positivity) (by positivity)
    have ha : (125000:ℝ) ≤ 250000000*v^2/(u^4*s^2) := by
      rw [le_div_iff₀ hR]
      nlinarith [hsq, sq_nonneg v]
    have hb : 375000*hh*nn/(θ*s) ≤ 250000000*v^2/(u^4*s^2) := by
      rw [div_le_div_iff₀ (by positivity) hR]
      calc 375000*hh*nn*(u^4*s^2)
          ≤ 375000*(u*v^4/16)*(v^3)*(u^4*s^2) := by
            rw [hn]; gcongr
        _ = (23437.5*(u^2*s))*(u^3*v^7*s) := by ring
        _ ≤ (23437.5*(26*v))*(u^3*v^7*s) := by
            gcongr
        _ = 609375*u^3*v^8*s := by ring
        _ ≤ 250000000*v^2*((19*u^3*v^6/240)*s) := by
            have hX : (0:ℝ) ≤ u^3*v^8*s := by positivity
            nlinarith [hX]
        _ ≤ 250000000*v^2*(θ*s) := by gcongr
    have hc : 1125000*hD*nn^2/(θ*s^2) ≤ 250000000*v^2/(u^4*s^2) := by
      rw [div_le_div_iff₀ (by positivity) hR]
      calc 1125000*hD*nn^2*(u^4*s^2)
          ≤ 1125000*(10*v^2/u)*(v^3)^2*(u^4*s^2) := by
            rw [hn]; gcongr
        _ = 11250000*u^3*v^8*s^2 := by field_simp; ring
        _ ≤ 250000000*v^2*((19*u^3*v^6/240)*s^2) := by
            have hX : (0:ℝ) ≤ u^3*v^8*s^2 := by positivity
            nlinarith [hX]
        _ ≤ 250000000*v^2*(θ*s^2) := by gcongr
    have hd : 125000*nn^3/(θ*s^3) ≤ 250000000*v^2/(u^4*s^2) := by
      rw [div_le_div_iff₀ (by positivity) hR]
      calc 125000*nn^3*(u^4*s^2)
          = (125000*(u*v))*(u^3*v^8*s^2) := by rw [hn]; ring
        _ ≤ (125000*(4*s))*(u^3*v^8*s^2) := by
            gcongr
        _ = 500000*u^3*v^8*s^3 := by ring
        _ ≤ 250000000*v^2*((19*u^3*v^6/240)*s^3) := by
            have hX : (0:ℝ) ≤ u^3*v^8*s^3 := by positivity
            nlinarith [hX]
        _ ≤ 250000000*v^2*(θ*s^3) := by gcongr
    have hsum : 125000*(1 + 3*hh*nn/(θ*s) + 9*hD*nn^2/(θ*s^2) + nn^3/(θ*s^3))
        = 125000 + 375000*hh*nn/(θ*s) + 1125000*hD*nn^2/(θ*s^2)
          + 125000*nn^3/(θ*s^3) := by ring
    rw [hsum]
    have hfour : (250000000:ℝ)*v^2/(u^4*s^2) + 250000000*v^2/(u^4*s^2)
        + 250000000*v^2/(u^4*s^2) + 250000000*v^2/(u^4*s^2) = 10^9*v^2/(u^4*s^2) := by
      ring
    linarith [ha, hb, hc, hd]
  refine ⟨{ Seed := (Fin t1 → Fin n × Fin n × Fin n) × (Fin t2 → (Fin s → Fin n))
            coins := clean_input_product_pmf
              (clean_input_uniform_pmf (Fin t1 → Fin n × Fin n × Fin n))
              (clean_input_uniform_pmf (Fin t2 → (Fin s → Fin n)))
            queries := fun z =>
              (Finset.univ.biUnion fun l : Fin t1 =>
                ({((z.1 l).1, (z.1 l).2.1), ((z.1 l).2.1, (z.1 l).2.2),
                  ((z.1 l).1, (z.1 l).2.2)} : Finset (Fin n × Fin n))) ∪
              (Finset.univ.biUnion fun k : Fin t2 =>
                Finset.univ.image fun q : Fin s × Fin s => (z.2 k q.1, z.2 k q.2))
            output := fun z M =>
              (decide (∀ l : Fin t1, ¬ ((z.1 l).1 ≠ (z.1 l).2.1 ∧ (z.1 l).2.1 ≠ (z.1 l).2.2 ∧
                  (z.1 l).1 ≠ (z.1 l).2.2 ∧
                  M (z.1 l).1 (z.1 l).2.1 + M (z.1 l).2.1 (z.1 l).2.2 <
                    M (z.1 l).1 (z.1 l).2.2))) &&
                (decide (∀ k : Fin t2,
                  sampled_triangle_count (violating_triangles M) (z.2 k) = 0))
            output_eq_of_query_eq := by
              intro z M N hMN
              have hq1 : ∀ l : Fin t1,
                  M (z.1 l).1 (z.1 l).2.1 = N (z.1 l).1 (z.1 l).2.1 ∧
                  M (z.1 l).2.1 (z.1 l).2.2 = N (z.1 l).2.1 (z.1 l).2.2 ∧
                  M (z.1 l).1 (z.1 l).2.2 = N (z.1 l).1 (z.1 l).2.2 := by
                intro l
                refine ⟨hMN ((z.1 l).1, (z.1 l).2.1) ?_, hMN ((z.1 l).2.1, (z.1 l).2.2) ?_,
                  hMN ((z.1 l).1, (z.1 l).2.2) ?_⟩ <;>
                  exact Finset.mem_union_left _
                    (Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, by simp⟩)
              have hcnt : ∀ k : Fin t2,
                  sampled_triangle_count (violating_triangles M) (z.2 k)
                    = sampled_triangle_count (violating_triangles N) (z.2 k) := by
                intro k
                have hag : ∀ i j : Fin n, i ∈ Finset.univ.image (z.2 k) →
                    j ∈ Finset.univ.image (z.2 k) → M i j = N i j := by
                  intro i j hi hj
                  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hi
                  obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hj
                  exact hMN (z.2 k a, z.2 k b) (Finset.mem_union_right _
                    (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _,
                      Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, rfl⟩⟩))
                have hfil : ((violating_triangles M).filter
                      fun t => ∀ i ∈ t, i ∈ Finset.univ.image (z.2 k))
                    = ((violating_triangles N).filter
                      fun t => ∀ i ∈ t, i ∈ Finset.univ.image (z.2 k)) := by
                  apply Finset.ext
                  intro t
                  simp only [Finset.mem_filter, violating_triangles, Finset.mem_univ, true_and]
                  constructor
                  · intro htt
                    obtain ⟨hvt, hin⟩ := htt
                    obtain ⟨i, hi, j, hj, k', hk', hij, hjk, hik, hgt⟩ := hvt.2
                    refine ⟨⟨hvt.1, i, hi, j, hj, k', hk', hij, hjk, hik, ?_⟩, hin⟩
                    rw [← hag i k' (hin i hi) (hin k' hk'), ← hag i j (hin i hi) (hin j hj),
                      ← hag j k' (hin j hj) (hin k' hk')]
                    exact hgt
                  · intro htt
                    obtain ⟨hvt, hin⟩ := htt
                    obtain ⟨i, hi, j, hj, k', hk', hij, hjk, hik, hgt⟩ := hvt.2
                    refine ⟨⟨hvt.1, i, hi, j, hj, k', hk', hij, hjk, hik, ?_⟩, hin⟩
                    rw [hag i k' (hin i hi) (hin k' hk'), hag i j (hin i hi) (hin j hj),
                      hag j k' (hin j hj) (hin k' hk')]
                    exact hgt
                unfold sampled_triangle_count
                congr 1
              apply congrArg₂ Bool.and
              · have hP : ∀ l : Fin t1,
                    (M (z.1 l).1 (z.1 l).2.1 + M (z.1 l).2.1 (z.1 l).2.2 <
                        M (z.1 l).1 (z.1 l).2.2)
                      ↔ (N (z.1 l).1 (z.1 l).2.1 + N (z.1 l).2.1 (z.1 l).2.2 <
                        N (z.1 l).1 (z.1 l).2.2) := by
                  intro l
                  rw [(hq1 l).1, (hq1 l).2.1, (hq1 l).2.2]
                apply decide_eq_decide.mpr
                constructor
                · intro hall l hc
                  exact hall l ⟨hc.1, hc.2.1, hc.2.2.1, (hP l).mpr hc.2.2.2⟩
                · intro hall l hc
                  exact hall l ⟨hc.1, hc.2.1, hc.2.2.1, (hP l).mp hc.2.2.2⟩
              · apply decide_eq_decide.mpr
                constructor
                · intro hall k
                  rw [← hcnt k]
                  exact hall k
                · intro hall k
                  rw [hcnt k]
                  exact hall k }, ?_, ?_⟩
  · intro z
    change ((((Finset.univ.biUnion fun l : Fin t1 =>
        ({((z.1 l).1, (z.1 l).2.1), ((z.1 l).2.1, (z.1 l).2.2),
          ((z.1 l).1, (z.1 l).2.2)} : Finset (Fin n × Fin n))) ∪
      (Finset.univ.biUnion fun k : Fin t2 =>
        Finset.univ.image fun q : Fin s × Fin s => (z.2 k q.1, z.2 k q.2))).card : ℝ)
      ≤ 10^10 * metric_testing_query_scale n ε)
    have hc1 : (Finset.univ.biUnion fun l : Fin t1 =>
        ({((z.1 l).1, (z.1 l).2.1), ((z.1 l).2.1, (z.1 l).2.2),
          ((z.1 l).1, (z.1 l).2.2)} : Finset (Fin n × Fin n))).card ≤ 3*t1 := by
      refine le_trans Finset.card_biUnion_le ?_
      have hb : ∀ l : Fin t1, ({((z.1 l).1, (z.1 l).2.1), ((z.1 l).2.1, (z.1 l).2.2),
          ((z.1 l).1, (z.1 l).2.2)} : Finset (Fin n × Fin n)).card ≤ 3 := by
        intro l
        refine le_trans (Finset.card_insert_le _ _) ?_
        have h2 := Finset.card_insert_le ((z.1 l).2.1, (z.1 l).2.2)
          ({((z.1 l).1, (z.1 l).2.2)} : Finset (Fin n × Fin n))
        simp only [Finset.card_singleton] at h2
        omega
      refine le_trans (Finset.sum_le_sum fun l _ => hb l) ?_
      simp [mul_comm]
    have hc2 : (Finset.univ.biUnion fun k : Fin t2 =>
        Finset.univ.image fun q : Fin s × Fin s => (z.2 k q.1, z.2 k q.2)).card
          ≤ t2*s^2 := by
      refine le_trans Finset.card_biUnion_le ?_
      have hb : ∀ k : Fin t2, (Finset.univ.image fun q : Fin s × Fin s =>
          (z.2 k q.1, z.2 k q.2)).card ≤ s^2 := by
        intro k
        refine le_trans Finset.card_image_le ?_
        simp [Finset.card_univ, pow_two]
      refine le_trans (Finset.sum_le_sum fun k _ => hb k) ?_
      simp [mul_comm]
    have hunion := Finset.card_union_le
      (Finset.univ.biUnion fun l : Fin t1 =>
        ({((z.1 l).1, (z.1 l).2.1), ((z.1 l).2.1, (z.1 l).2.2),
          ((z.1 l).1, (z.1 l).2.2)} : Finset (Fin n × Fin n)))
      (Finset.univ.biUnion fun k : Fin t2 =>
        Finset.univ.image fun q : Fin s × Fin s => (z.2 k q.1, z.2 k q.2))
    have hreal : (((Finset.univ.biUnion fun l : Fin t1 =>
        ({((z.1 l).1, (z.1 l).2.1), ((z.1 l).2.1, (z.1 l).2.2),
          ((z.1 l).1, (z.1 l).2.2)} : Finset (Fin n × Fin n))) ∪
      (Finset.univ.biUnion fun k : Fin t2 =>
        Finset.univ.image fun q : Fin s × Fin s => (z.2 k q.1, z.2 k q.2))).card : ℝ)
        ≤ 3*(t1:ℝ) + (t2:ℝ)*(s:ℝ)^2 := by
      have hnat : (((Finset.univ.biUnion fun l : Fin t1 =>
          ({((z.1 l).1, (z.1 l).2.1), ((z.1 l).2.1, (z.1 l).2.2),
            ((z.1 l).1, (z.1 l).2.2)} : Finset (Fin n × Fin n))) ∪
        (Finset.univ.biUnion fun k : Fin t2 =>
          Finset.univ.image fun q : Fin s × Fin s => (z.2 k q.1, z.2 k q.2))).card)
          ≤ 3*t1 + t2*s^2 := by omega
      exact_mod_cast hnat
    rw [hQ]
    have hmul : (t2:ℝ)*(s:ℝ)^2 ≤ (10^9*v^2/(u^4*(s:ℝ)^2) + 1)*(s:ℝ)^2 :=
      mul_le_mul_of_nonneg_right ht2b (by positivity)
    have heq : (10^9*v^2/(u^4*(s:ℝ)^2) + 1)*(s:ℝ)^2 = 10^9*(v^2/u^4) + (s:ℝ)^2 := by
      field_simp
    rw [heq] at hmul
    linarith [hreal, ht1b, hs2b, hmul, hVone]
  · have hacc : ∀ (Sd : Type) (co : PMF Sd) (fo : Sd → Bool), (∀ x, fo x = true) →
        (co.map fo) true = 1 := by
      intro Sd co fo hfo
      have hconst : fo = Function.const Sd true := funext hfo
      rw [hconst, PMF.map_const]
      simp
    constructor
    · intro M hM
      have hempty : violating_triangles M = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro t ht
        rw [violating_triangles, Finset.mem_filter] at ht
        obtain ⟨-, -, i, hi, j, hj, k, hk, hij, hjk, hik, hgt⟩ := ht
        have := hM.2 i j k
        linarith
      rw [tester_acceptance_probability]
      refine hacc _ _ _ ?_
      intro x
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨?_, ?_⟩
      · intro l hc
        have := hM.2 (x.1 l).1 (x.1 l).2.1 (x.1 l).2.2
        linarith [hc.2.2.2]
      · intro k
        simp [sampled_triangle_count, hempty]
    · intro M hclean hfar
      obtain ⟨D1, hD1def⟩ : ∃ D1 : Finset (Fin n × Fin n × Fin n), D1 =
          Finset.univ.filter (fun q : Fin n × Fin n × Fin n =>
            q.1 ≠ q.2.1 ∧ q.2.1 ≠ q.2.2 ∧ q.1 ≠ q.2.2 ∧
              M q.1 q.2.1 + M q.2.1 q.2.2 < M q.1 q.2.2) := ⟨_, rfl⟩
      obtain ⟨D2, hD2def⟩ : ∃ D2 : Finset (Fin s → Fin n), D2 =
          Finset.univ.filter (fun y : Fin s → Fin n =>
            0 < sampled_triangle_count (violating_triangles M) y) := ⟨_, rfl⟩
      let U1 : PMF (Fin t1 → Fin n × Fin n × Fin n) :=
        clean_input_uniform_pmf (Fin t1 → Fin n × Fin n × Fin n)
      let U2 : PMF (Fin t2 → (Fin s → Fin n)) :=
        clean_input_uniform_pmf (Fin t2 → (Fin s → Fin n))
      let fo : (Fin t1 → Fin n × Fin n × Fin n) → Bool := fun x =>
        decide (∀ l : Fin t1, ¬ ((x l).1 ≠ (x l).2.1 ∧ (x l).2.1 ≠ (x l).2.2 ∧
          (x l).1 ≠ (x l).2.2 ∧
            M (x l).1 (x l).2.1 + M (x l).2.1 (x l).2.2 < M (x l).1 (x l).2.2))
      let go : (Fin t2 → (Fin s → Fin n)) → Bool := fun y =>
        decide (∀ k : Fin t2, sampled_triangle_count (violating_triangles M) (y k) = 0)
      have hproduct := clean_input_product_pmf_bounds U1 U2 fo go
      rw [tester_rejection_probability]
      change (2:ENNReal)/3 ≤ (clean_input_product_pmf U1 U2).map
        (fun z => fo z.1 && go z.2) false
      have hfrej : 2 * Fintype.card (Fin n × Fin n × Fin n) ≤ t1 * D1.card →
          (2:ENNReal)/3 ≤ U1.map fo false := by
        intro hc
        have hhitting := clean_input_reduction_sampling D1 t1 hc
        have heq : U1.map fo false = U1.map (fun x => decide (∃ l, x l ∈ D1)) true := by
          simp only [PMF.map_apply]
          apply tsum_congr
          intro x
          have hiff : (∃ l, x l ∈ D1) ↔ ¬ (∀ l : Fin t1,
              ¬ ((x l).1 ≠ (x l).2.1 ∧ (x l).2.1 ≠ (x l).2.2 ∧ (x l).1 ≠ (x l).2.2 ∧
                M (x l).1 (x l).2.1 + M (x l).2.1 (x l).2.2 < M (x l).1 (x l).2.2)) := by
            rw [hD1def]
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not]
          by_cases hx : ∃ l, x l ∈ D1
          · have h1 : fo x = false := by
              simp only [fo, decide_eq_false_iff_not]
              exact hiff.mp hx
            have h2 : decide (∃ l, x l ∈ D1) = true := decide_eq_true hx
            rw [h1, h2]
            simp
          · have h1 : fo x = true := by
              simp only [fo, decide_eq_true_eq]
              exact not_not.mp fun hcon => hx (hiff.mpr hcon)
            have h2 : decide (∃ l, x l ∈ D1) = false := decide_eq_false hx
            rw [h1, h2]
            simp
        rw [heq]
        exact hhitting
      have hgrej : 2 * Fintype.card (Fin s → Fin n) ≤ t2 * D2.card →
          (2:ENNReal)/3 ≤ U2.map go false := by
        intro hc
        have hhitting := clean_input_reduction_sampling D2 t2 hc
        have heq : U2.map go false = U2.map (fun y => decide (∃ k, y k ∈ D2)) true := by
          simp only [PMF.map_apply]
          apply tsum_congr
          intro y
          have hiff : (∃ k, y k ∈ D2) ↔ ¬ (∀ k : Fin t2,
              sampled_triangle_count (violating_triangles M) (y k) = 0) := by
            rw [hD2def]
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall,
              Nat.pos_iff_ne_zero]
          by_cases hy : ∃ k, y k ∈ D2
          · have h1 : go y = false := by
              simp only [go, decide_eq_false_iff_not]
              exact hiff.mp hy
            have h2 : decide (∃ k, y k ∈ D2) = true := decide_eq_true hy
            rw [h1, h2]
            simp
          · have h1 : go y = true := by
              simp only [go, decide_eq_true_eq]
              exact not_not.mp fun hcon => hy (hiff.mpr hcon)
            have h2 : decide (∃ k, y k ∈ D2) = false := decide_eq_false hy
            rw [h1, h2]
            simp
        rw [heq]
        exact hhitting
      have hu0 : u ≠ 0 := ne_of_gt hupos
      have hnn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      have hcard3 : Fintype.card (Fin n × Fin n × Fin n) = n * n * n := by
        simp [Fintype.card_prod, Nat.mul_assoc]
      have hcards : Fintype.card (Fin s → Fin n) = n^s := by simp
      have hex : ∀ t : Finset (Fin n), ∃ q : Fin n × Fin n × Fin n,
          t ∈ violating_triangles M → (q ∈ D1 ∧ t = {q.1, q.2.1, q.2.2}) := by
        intro t
        by_cases ht : t ∈ violating_triangles M
        · rw [violating_triangles, Finset.mem_filter] at ht
          obtain ⟨-, hc3, i, hi, j, hj, k, hk, hij, hjk, hik, hgt⟩ := ht
          refine ⟨(i, j, k), fun _ => ⟨?_, ?_⟩⟩
          · rw [hD1def, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, hij, hjk, hik, hgt⟩
          · refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
            · intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl | rfl <;> assumption
            · rw [hc3, Finset.card_eq_three.mpr ⟨i, j, k, hij, hik, hjk, rfl⟩]
        · exact ⟨(⟨0, hnpos⟩, ⟨0, hnpos⟩, ⟨0, hnpos⟩), fun hc => absurd hc ht⟩
      choose F hF using hex
      have hTD1 : (violating_triangles M).card ≤ D1.card := by
        refine Finset.card_le_card_of_injOn F (fun t ht => (hF t ht).1) ?_
        intro a ha b hb hab
        simp only [Finset.mem_coe] at ha hb
        rw [(hF a ha).2, (hF b hb).2, hab]
      have hdegsum : ∑ i : Fin n, vertex_triangle_degree (violating_triangles M) i
          = 3 * (violating_triangles M).card := by
        have h1 : ∀ i : Fin n, vertex_triangle_degree (violating_triangles M) i
            = ∑ t ∈ violating_triangles M, if i ∈ t then 1 else 0 := by
          intro i
          rw [vertex_triangle_degree, Finset.card_filter]
        rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h1 i), Finset.sum_comm]
        have h2 : ∀ t ∈ violating_triangles M,
            (∑ i : Fin n, if i ∈ t then 1 else 0) = 3 := by
          intro t ht
          rw [violating_triangles, Finset.mem_filter] at ht
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul,
            mul_one, ht.2.1]
        rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]
      have hbranch1 : 2*(n:ℝ)^3 ≤ (t1:ℝ)*((violating_triangles M).card:ℝ) →
          (2:ENNReal)/3 ≤ (clean_input_product_pmf U1 U2).map
            (fun z => fo z.1 && go z.2) false := by
        intro hlow1
        refine le_trans (hfrej ?_) hproduct.1
        rw [hcard3]
        have hd1 : ((violating_triangles M).card : ℝ) ≤ (D1.card : ℝ) := by
          exact_mod_cast hTD1
        have ht1nn : (0:ℝ) ≤ (t1:ℝ) := Nat.cast_nonneg _
        have hreal : ((2*(n*n*n) : ℕ) : ℝ) ≤ ((t1 * D1.card : ℕ) : ℝ) := by
          push_cast
          nlinarith [hlow1, mul_le_mul_of_nonneg_left hd1 ht1nn]
        exact_mod_cast hreal
      by_cases hbig : 16 ≤ u*v^4
      · have hH1 : 1 ≤ H := by
          rw [hHdef]
          apply Nat.le_floor
          push_cast
          linarith
        have hHR1 : (1:ℝ) ≤ (H:ℝ) := by exact_mod_cast hH1
        have hHne : (H:ℝ) ≠ 0 := by intro hc; rw [hc] at hHR1; linarith
        obtain ⟨I, hIdef⟩ : ∃ I : Finset (Fin n), I = Finset.univ.filter
            (fun i => H ≤ vertex_triangle_degree (violating_triangles M) i) := ⟨_, rfl⟩
        by_cases hlow : ((I.card : ℝ)) ≤ (R:ℝ)
        · have hHb' : (H:ℝ) ≤ ε^(1/3:ℝ)*(n:ℝ)^(4/3:ℝ)/16 := by
            rw [← hudef, ← hv43]
            exact hHb
          have hεn4 : (0:ℝ) ≤ ε*(n:ℝ)/4 := by
            have h1 : (0:ℝ) ≤ ε*(n:ℝ) := mul_nonneg hε₀.le hnn
            linarith
          have hRb : (R:ℝ) ≤ ε*(n:ℝ)/4 := by
            rw [hRdef]
            exact Nat.floor_le hεn4
          have hfew : ((Finset.univ.filter fun i =>
              H ≤ vertex_triangle_degree (violating_triangles M) i).card : ℝ) ≤ (R:ℝ) := by
            rw [← hIdef]
            exact hlow
          obtain ⟨T, hTsub, hTcard, hTdeg, hTpair⟩ :=
            bounded_degree_violating_family hε₀ hε₁ hclean hfar H R hHb' hfew hRb
          have hT3 : ∀ t ∈ T, t.card = 3 := by
            intro t ht
            have h := hTsub ht
            rw [violating_triangles, Finset.mem_filter] at h
            exact h.2.1
          have hTposR : (0:ℝ) < (T.card:ℝ) := by
            have h1 : (0:ℝ) < ε*(n:ℝ)^(2:ℕ) := mul_pos hε₀ (by positivity)
            linarith [hTcard]
          have hTpos : 0 < T.card := by exact_mod_cast hTposR
          obtain ⟨hD, hDdef⟩ : ∃ hD : ℕ, hD = ⌊10*v^2/u⌋₊ := ⟨_, rfl⟩
          have hDb : (hD:ℝ) ≤ 10*v^2/u := by
            rw [hDdef]
            exact Nat.floor_le (by positivity)
          have hpairT : ∀ i j : Fin n, i ≠ j → pair_triangle_degree T i j ≤ hD := by
            intro i j hij
            rw [hDdef]
            apply Nat.le_floor
            have h := hTpair i j hij
            rw [hv2, hudef]
            exact h
          have hthird : 125000 * (1 + 3*(H:ℝ)*(n:ℝ)/((T.card:ℝ)*(s:ℝ))
              + 9*(hD:ℝ)*(n:ℝ)^2/((T.card:ℝ)*(s:ℝ)^2)
              + (n:ℝ)^3/((T.card:ℝ)*(s:ℝ)^3)) ≤ (t2:ℝ) := by
            have hs3R : (3:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs3
            have hθ : 19*u^3*v^6/240 ≤ (T.card:ℝ) := by
              have heq : 19*u^3*v^6/240 = 19*ε*(n:ℝ)^(2:ℕ)/240 := by
                rw [← hu3, ← hv3]; ring
              rw [heq]
              exact hTcard
            have h := harith u v (s:ℝ) (T.card:ℝ) (H:ℝ) (hD:ℝ) (n:ℝ)
              hupos hu1 hv4 hs3R hv3.symm hsu2 huvs hθ hHb hDb
              (Nat.cast_nonneg H) (Nat.cast_nonneg hD)
            linarith [ht2low]
          have hcount := hhitcount T hT3 H hD hTdeg hpairT hTpos hthird
          refine le_trans (hgrej ?_) hproduct.2.1
          rw [hcards]
          have hsub : (Finset.univ.filter (fun y : Fin s → Fin n =>
              0 < sampled_triangle_count T y)) ⊆ D2 := by
            rw [hD2def]
            intro y hy
            rw [Finset.mem_filter] at hy ⊢
            refine ⟨hy.1, lt_of_lt_of_le hy.2 ?_⟩
            unfold sampled_triangle_count
            exact Finset.card_le_card (Finset.filter_subset_filter _ hTsub)
          have hsubR : ((Finset.univ.filter (fun y : Fin s → Fin n =>
              0 < sampled_triangle_count T y)).card : ℝ) ≤ (D2.card:ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
          have ht2nn : (0:ℝ) ≤ (t2:ℝ) := Nat.cast_nonneg _
          have hreal : ((2*n^s : ℕ):ℝ) ≤ ((t2*D2.card : ℕ):ℝ) := by
            push_cast
            nlinarith [hcount, mul_le_mul_of_nonneg_left hsubR ht2nn]
          exact_mod_cast hreal
        · refine hbranch1 ?_
          have hIge : ε*(n:ℝ)/4 ≤ (I.card:ℝ) := by
            have h1 : R < I.card := by exact_mod_cast lt_of_not_ge hlow
            have h2 : ε*(n:ℝ)/4 < (R:ℝ) + 1 := by
              rw [hRdef]
              exact Nat.lt_floor_add_one _
            have h3 : (R:ℝ) + 1 ≤ (I.card:ℝ) := by
              have h4 : R + 1 ≤ I.card := h1
              exact_mod_cast h4
            linarith
          have hsum1 : I.card * H ≤ ∑ i : Fin n,
              vertex_triangle_degree (violating_triangles M) i := by
            calc I.card * H = ∑ _i ∈ I, H := by rw [Finset.sum_const, smul_eq_mul]
              _ ≤ ∑ i ∈ I, vertex_triangle_degree (violating_triangles M) i :=
                  Finset.sum_le_sum (fun i hi => by
                    rw [hIdef, Finset.mem_filter] at hi; exact hi.2)
              _ ≤ ∑ i : Fin n, vertex_triangle_degree (violating_triangles M) i :=
                  Finset.sum_le_sum_of_subset (Finset.subset_univ I)
          have hsum2 : (I.card:ℝ)*(H:ℝ) ≤ 3*((violating_triangles M).card:ℝ) := by
            rw [hdegsum] at hsum1
            have h5 : ((I.card * H : ℕ):ℝ) ≤ ((3*(violating_triangles M).card : ℕ):ℝ) := by
              exact_mod_cast hsum1
            push_cast at h5
            linarith
          have hVTlow : ε*(n:ℝ)*(H:ℝ)/12 ≤ ((violating_triangles M).card:ℝ) := by
            have h4 : ε*(n:ℝ)/4*(H:ℝ) ≤ (I.card:ℝ)*(H:ℝ) :=
              mul_le_mul_of_nonneg_right hIge (Nat.cast_nonneg H)
            linarith
          have hVTnn : (0:ℝ) ≤ ε*(n:ℝ)*(H:ℝ)/12 := by
            have h1 : (0:ℝ) ≤ ε*(n:ℝ) := mul_nonneg hε₀.le hnn
            have h2 : (0:ℝ) ≤ ε*(n:ℝ)*(H:ℝ) := mul_nonneg h1 (Nat.cast_nonneg H)
            linarith
          have ht1low : 24*v^6/(u^3*(H:ℝ)) ≤ (t1:ℝ) := by
            rw [ht1def, if_pos hbig]
            exact Nat.le_ceil _
          have hprod : (24*v^6/(u^3*(H:ℝ))) * (ε*(n:ℝ)*(H:ℝ)/12) = 2*(n:ℝ)^3 := by
            rw [← hu3, ← hv3]
            field_simp
            ring
          rw [← hprod]
          exact mul_le_mul ht1low hVTlow hVTnn (Nat.cast_nonneg t1)
      · refine hbranch1 ?_
        have hVT := many_violating_triangles hε₀ hε₁ hclean hfar
        have ht1low : 12*v^3/u^3 ≤ (t1:ℝ) := by
          rw [ht1def, if_neg hbig]
          exact Nat.le_ceil _
        have hVTnn : (0:ℝ) ≤ ε*(n:ℝ)^(2:ℕ)/6 := by
          have h1 : (0:ℝ) ≤ ε*(n:ℝ)^(2:ℕ) := mul_nonneg hε₀.le (by positivity)
          linarith
        have hprod : (12*v^3/u^3) * (ε*(n:ℝ)^(2:ℕ)/6) = 2*(n:ℝ)^3 := by
          rw [← hu3, ← hv3]
          field_simp
          ring
        rw [← hprod]
        exact mul_le_mul ht1low hVT hVTnn (Nat.cast_nonneg t1)

@[blueprint "lem:clean-input-reduction"
  (statement := /-- Suppose that there exist $n_0\in\mathbb N$ and $C>0$ such that, for every $n\geq n_0$ and every $0<\varepsilon<1$, there is a non-adaptive tester making at most $C n^{2/3}/\varepsilon^{4/3}$ queries for each random seed, accepting every metric matrix with probability one, and rejecting every clean matrix that is $\varepsilon$-far from the metric property with probability at least $2/3$. Then there exist $n_0'\in\mathbb N$ and $C'>0$ such that, for every $n\geq n_0'$ and every $0<\varepsilon<1$, there is a non-adaptive tester making at most $C'n^{2/3}/\varepsilon^{4/3}$ queries for each random seed, accepting every metric matrix with probability one, and rejecting every matrix that is $\varepsilon$-far from the metric property with probability at least $2/3$. -/)
  (proof := /-- Use the canonical cleaning $\widehat M$ from \cref{def:clean-input-canonicalize}, which is clean by \cref{lem:clean-input-canonicalize-clean} and fixes every metric matrix by \cref{lem:clean-input-canonicalize-metric}. Invoke the assumed clean-input tester with parameter $\varepsilon/8$. Independently choose $t=\lceil4/\varepsilon\rceil$ uniformly sampled ordered entries using \cref{def:clean-input-uniform-pmf}, and accept precisely when the clean tester accepts $\widehat M$ and every sampled entry agrees with its cleaned value. Query each clean-tester entry, each sampled entry, and their reversals; \cref{lem:clean-input-canonicalize-local} proves that this output depends only on those queries. The union contains at most twice the clean tester's queries plus $2t$ entries. Real-power monotonicity bounds the former by $128C n^{2/3}/\varepsilon^{4/3}$ and $t<4/\varepsilon+1$ bounds the latter by $10n^{2/3}/\varepsilon^{4/3}$. For completeness, canonical cleaning fixes the metric input, the sample check always accepts, and \cref{lem:clean-input-product-pmf-bounds} identifies the product test's acceptance probability with that of the clean tester. For soundness, if cleaning changes fewer than $\varepsilon n^2/2$ entries, \cref{lem:clean-input-canonicalize-far} makes $\widehat M$ $\varepsilon/2$-far, hence $\varepsilon/8$-far, and the clean tester rejects with probability at least $2/3$. Otherwise $t$ times the number of changed entries is at least $2n^2$, so \cref{lem:clean-input-reduction-sampling} makes the sample check reject with probability at least $2/3$. In either case \cref{lem:clean-input-product-pmf-bounds} transfers the relevant rejection probability to the conjoined tester. -/)
  (title := /-- Reduction from Arbitrary Inputs to Clean Inputs -/)
  (latexEnv := "lemma")]
lemma clean_input_reduction
    (hcleanTester :
      ∃ n₀ : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ n : ℕ, n₀ ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 →
          ∃ A : nonadaptive_matrix_tester n,
            tester_uses_at_most A (C * metric_testing_query_scale n ε) ∧
              clean_metric_tester_guarantee A ε) :
    ∃ n₀ : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∃ A : nonadaptive_matrix_tester n,
          tester_uses_at_most A (C * metric_testing_query_scale n ε) ∧
            metric_tester_guarantee A ε := by
  classical
  rcases hcleanTester with ⟨n₀, C, hC, htester⟩
  refine ⟨max n₀ 1, 128 * C + 10, by positivity, ?_⟩
  intro n hn ε hε₀ hε₁
  have hn₀ : n₀ ≤ n := (le_max_left n₀ 1).trans hn
  have hnone : 1 ≤ n := (le_max_right n₀ 1).trans hn
  have hnpos : 0 < n := Nat.zero_lt_of_lt hnone
  letI : NeZero n := ⟨Nat.ne_of_gt hnpos⟩
  have hεeight₀ : 0 < ε / 8 := by positivity
  have hεeight₁ : ε / 8 < 1 := by linarith
  obtain ⟨A, hAquery, hAguarantee⟩ := htester n hn₀ (ε / 8) hεeight₀ hεeight₁
  let t : ℕ := ⌈4 / ε⌉₊
  let U : PMF (Fin t → Fin n × Fin n) :=
    clean_input_uniform_pmf (Fin t → Fin n × Fin n)
  let B : nonadaptive_matrix_tester n :=
    { Seed := A.Seed × (Fin t → Fin n × Fin n)
      coins := clean_input_product_pmf A.coins U
      queries := fun z =>
        A.queries z.1 ∪ (A.queries z.1).image (fun p => (p.2, p.1)) ∪
          Finset.univ.image z.2 ∪
            (Finset.univ.image z.2).image (fun p => (p.2, p.1))
      output := fun z M =>
        A.output z.1 (clean_input_canonicalize M) &&
          decide (∀ k, M (z.2 k).1 (z.2 k).2 =
            clean_input_canonicalize M (z.2 k).1 (z.2 k).2)
      output_eq_of_query_eq := by
        intro z M N hMN
        apply congrArg₂ Bool.and
        · apply A.output_eq_of_query_eq
          intro p hp
          apply clean_input_canonicalize_local
          · exact hMN p (by simp [hp])
          · exact hMN (p.2, p.1) (by simp [hp])
        · apply decide_eq_decide.mpr
          constructor
          · intro h k
            have hforward := hMN (z.2 k) (by simp)
            have hreverse := hMN ((z.2 k).2, (z.2 k).1) (by
              apply Finset.mem_union_right
              apply Finset.mem_image.mpr
              refine ⟨z.2 k, ?_, rfl⟩
              exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
            calc
              N (z.2 k).1 (z.2 k).2 = M (z.2 k).1 (z.2 k).2 := hforward.symm
              _ = clean_input_canonicalize M (z.2 k).1 (z.2 k).2 := h k
              _ = clean_input_canonicalize N (z.2 k).1 (z.2 k).2 :=
                clean_input_canonicalize_local hforward hreverse
          · intro h k
            have hforward := hMN (z.2 k) (by simp)
            have hreverse := hMN ((z.2 k).2, (z.2 k).1) (by
              apply Finset.mem_union_right
              apply Finset.mem_image.mpr
              refine ⟨z.2 k, ?_, rfl⟩
              exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
            calc
              M (z.2 k).1 (z.2 k).2 = N (z.2 k).1 (z.2 k).2 := hforward
              _ = clean_input_canonicalize N (z.2 k).1 (z.2 k).2 := h k
              _ = clean_input_canonicalize M (z.2 k).1 (z.2 k).2 :=
                (clean_input_canonicalize_local hforward hreverse).symm }
  refine ⟨B, ?_, ?_⟩
  · intro z
    change (((A.queries z.1 ∪ (A.queries z.1).image (fun p => (p.2, p.1))) ∪
        Finset.univ.image z.2) ∪
          (Finset.univ.image z.2).image (fun p => (p.2, p.1))).card ≤
      (128 * C + 10) * metric_testing_query_scale n ε
    have hcardNat :
        (((A.queries z.1 ∪ (A.queries z.1).image (fun p => (p.2, p.1))) ∪
          Finset.univ.image z.2) ∪
            (Finset.univ.image z.2).image (fun p => (p.2, p.1))).card ≤
          2 * (A.queries z.1).card + 2 * t := by
      have h₁ := Finset.card_union_le (A.queries z.1)
        ((A.queries z.1).image (fun p => (p.2, p.1)))
      have h₂ := Finset.card_union_le
        (A.queries z.1 ∪ (A.queries z.1).image (fun p => (p.2, p.1)))
        (Finset.univ.image z.2)
      have h₃ := Finset.card_union_le
        ((A.queries z.1 ∪ (A.queries z.1).image (fun p => (p.2, p.1))) ∪
          Finset.univ.image z.2)
        ((Finset.univ.image z.2).image (fun p => (p.2, p.1)))
      have hAimage : ((A.queries z.1).image (fun p => (p.2, p.1))).card ≤
          (A.queries z.1).card := Finset.card_image_le
      have hsample : (Finset.univ.image z.2).card ≤ t := by
        simpa using (Finset.card_image_le :
          (Finset.univ.image z.2).card ≤ (Finset.univ : Finset (Fin t)).card)
      have hsampleImage :
          ((Finset.univ.image z.2).image (fun p => (p.2, p.1))).card ≤
            (Finset.univ.image z.2).card := Finset.card_image_le
      omega
    have hcardReal :
        ((((A.queries z.1 ∪ (A.queries z.1).image (fun p => (p.2, p.1))) ∪
          Finset.univ.image z.2) ∪
            (Finset.univ.image z.2).image (fun p => (p.2, p.1))).card : ℝ) ≤
          2 * ((A.queries z.1).card : ℝ) + 2 * t := by
      exact_mod_cast hcardNat
    calc
      ((((A.queries z.1 ∪ (A.queries z.1).image (fun p => (p.2, p.1))) ∪
        Finset.univ.image z.2) ∪
          (Finset.univ.image z.2).image (fun p => (p.2, p.1))).card : ℝ) ≤
          2 * ((A.queries z.1).card : ℝ) + 2 * t := hcardReal
      _ ≤ (128 * C + 10) * metric_testing_query_scale n ε := by
        have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hnone
        have hnPow : (1 : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ) :=
          Real.one_le_rpow hnR (by norm_num)
        have hεPowPos : 0 < ε ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hε₀ _
        have hεPowLe : ε ^ (4 / 3 : ℝ) ≤ ε := by
          convert Real.rpow_le_rpow_of_exponent_ge hε₀ hε₁.le (by norm_num :
            (1 : ℝ) ≤ 4 / 3) using 1 <;> norm_num
        have hInv : 1 / ε ≤ 1 / ε ^ (4 / 3 : ℝ) := by
          exact one_div_le_one_div_of_le hεPowPos hεPowLe
        have hQ : 1 / ε ≤ metric_testing_query_scale n ε := by
          rw [metric_testing_query_scale]
          exact hInv.trans (div_le_div_of_nonneg_right hnPow hεPowPos.le)
        have hQone : (1 : ℝ) ≤ metric_testing_query_scale n ε := by
          have : (1 : ℝ) ≤ 1 / ε := (le_div_iff₀ hε₀).2 (by simpa using hε₁.le)
          exact this.trans hQ
        have htReal : (t : ℝ) < 4 / ε + 1 := by
          dsimp [t]
          exact Nat.ceil_lt_add_one (by positivity)
        have htBound : (2 : ℝ) * t ≤ 10 * metric_testing_query_scale n ε := by
          have hfour : (4 : ℝ) / ε = 4 * (1 / ε) := by ring
          rw [hfour] at htReal
          nlinarith
        have hEightPow : (8 : ℝ) ^ (4 / 3 : ℝ) ≤ 64 := by
          calc
            (8 : ℝ) ^ (4 / 3 : ℝ) ≤ (8 : ℝ) ^ (2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 64 := by norm_num
        have hScaleEq : metric_testing_query_scale n (ε / 8) =
            (8 : ℝ) ^ (4 / 3 : ℝ) * metric_testing_query_scale n ε := by
          rw [metric_testing_query_scale, metric_testing_query_scale,
            Real.div_rpow hε₀.le (by norm_num : (0 : ℝ) ≤ 8)]
          field_simp
        have hScale : metric_testing_query_scale n (ε / 8) ≤
            64 * metric_testing_query_scale n ε := by
          rw [hScaleEq]
          exact mul_le_mul_of_nonneg_right hEightPow (by
            rw [metric_testing_query_scale]
            positivity)
        have hA := hAquery z.1
        have hA' : 2 * ((A.queries z.1).card : ℝ) ≤
            128 * C * metric_testing_query_scale n ε := by
          calc
            2 * ((A.queries z.1).card : ℝ) ≤
                2 * (C * metric_testing_query_scale n (ε / 8)) := by linarith
            _ ≤ 2 * (C * (64 * metric_testing_query_scale n ε)) := by
              gcongr
            _ = 128 * C * metric_testing_query_scale n ε := by ring
        nlinarith
  · constructor
    · intro M hM
      have hfix := clean_input_canonicalize_metric hM
      have hproduct := clean_input_product_pmf_bounds A.coins U
        (fun seed => A.output seed (clean_input_canonicalize M))
        (fun sample => decide (∀ k, M (sample k).1 (sample k).2 =
          clean_input_canonicalize M (sample k).1 (sample k).2))
      have hsampleTrue : ∀ sample : Fin t → Fin n × Fin n,
          decide (∀ k, M (sample k).1 (sample k).2 =
            clean_input_canonicalize M (sample k).1 (sample k).2) = true := by
        intro sample
        simp [hfix]
      have hAaccept := hAguarantee.1 M hM
      rw [tester_acceptance_probability] at hAaccept ⊢
      change (clean_input_product_pmf A.coins U).map
        (fun z => A.output z.1 (clean_input_canonicalize M) &&
          decide (∀ k, M (z.2 k).1 (z.2 k).2 =
            clean_input_canonicalize M (z.2 k).1 (z.2 k).2)) true = 1
      rw [hproduct.2.2 hsampleTrue]
      simpa [hfix] using hAaccept
    · intro M hfar
      let D : Finset (Fin n × Fin n) :=
        (Finset.univ.product Finset.univ).filter fun p =>
          M p.1 p.2 ≠ clean_input_canonicalize M p.1 p.2
      let f : A.Seed → Bool := fun seed =>
        A.output seed (clean_input_canonicalize M)
      let g : (Fin t → Fin n × Fin n) → Bool := fun sample =>
        decide (∀ k, M (sample k).1 (sample k).2 =
          clean_input_canonicalize M (sample k).1 (sample k).2)
      have hproduct := clean_input_product_pmf_bounds A.coins U f g
      change (2 : ENNReal) / 3 ≤
        (clean_input_product_pmf A.coins U).map
          (fun z => f z.1 && g z.2) false
      by_cases hsmall :
          (matrix_hamming_distance M (clean_input_canonicalize M) : ℝ) <
            ε * (n : ℝ) ^ (2 : ℕ) / 2
      · have hfarHalf := clean_input_canonicalize_far hfar hsmall
        have hfarEight : epsilon_far_from_metric (ε / 8)
            (clean_input_canonicalize M) := by
          intro N hN
          have h := hfarHalf N hN
          have hnSq : (0 : ℝ) ≤ (n : ℝ) ^ (2 : ℕ) := by positivity
          nlinarith
        have hAreject := hAguarantee.2 (clean_input_canonicalize M)
          (clean_input_canonicalize_clean M) hfarEight
        exact hAreject.trans hproduct.1
      · have hlarge : ε * (n : ℝ) ^ (2 : ℕ) / 2 ≤
            (matrix_hamming_distance M (clean_input_canonicalize M) : ℝ) :=
          le_of_not_gt hsmall
        have htLower : 4 / ε ≤ (t : ℝ) := by
          dsimp [t]
          exact Nat.le_ceil (4 / ε)
        have hmul : (4 / ε) * (ε * (n : ℝ) ^ (2 : ℕ) / 2) ≤
            (t : ℝ) * matrix_hamming_distance M (clean_input_canonicalize M) :=
          mul_le_mul htLower hlarge (by positivity) (by positivity)
        have hsampleReal : 2 * (n : ℝ) ^ (2 : ℕ) ≤ (t : ℝ) * D.card := by
          have heq : (4 / ε) * (ε * (n : ℝ) ^ (2 : ℕ) / 2) =
              2 * (n : ℝ) ^ (2 : ℕ) := by
            field_simp
            ring
          rw [heq] at hmul
          simpa [D, matrix_hamming_distance] using hmul
        have hsampleNat : 2 * Fintype.card (Fin n × Fin n) ≤ t * D.card := by
          have hcard : Fintype.card (Fin n × Fin n) = n ^ 2 := by
            simp [pow_two]
          rw [hcard]
          exact_mod_cast hsampleReal
        have hhit := clean_input_reduction_sampling D t hsampleNat
        have hsampleReject : U.map g false =
            U.map (fun sample => decide (∃ k, sample k ∈ D)) true := by
          simp only [PMF.map_apply]
          apply tsum_congr
          intro sample
          by_cases h : ∃ k, sample k ∈ D
          · simp [g, h, D]
          · simp [g, h, D]
        have hUreject : (2 : ENNReal) / 3 ≤ U.map g false := by
          rw [hsampleReject]
          simpa [U] using hhit
        exact hUreject.trans hproduct.2.1

@[blueprint "thm:testing-metrics-upper-bound"
  (statement := /-- There are absolute constants $n_0\in\mathbb N$ and $C>0$ such that, for every $n\geq n_0$ and every $\varepsilon\in(0,1)$, there exists a randomized non-adaptive algorithm with query access to an unknown matrix $M\in\mathbb R^{n\times n}$ which makes at most $C n^{2/3}/\varepsilon^{4/3}$ queries, accepts every metric matrix with probability one, and rejects every matrix that is $\varepsilon$-far from the metric property with probability at least $2/3$. -/)
  (proof := /-- Apply \,\cref{lem:clean-metric-tester-upper-bound} to obtain the one-sided non-adaptive tester under the clean-input promise. The reduction \,\cref{lem:clean-input-reduction} removes that promise, preserves perfect completeness and rejection probability at least $2/3$, and absorbs its additional queries into the same asymptotic bound. -/)
  (title := /-- Testing Metrics---Upper Bound -/)
  (latexEnv := "theorem")]
theorem testing_metrics_upper_bound :
    ∃ n₀ : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∃ A : nonadaptive_matrix_tester n,
          tester_uses_at_most A (C * metric_testing_query_scale n ε) ∧
            metric_tester_guarantee A ε := by
  exact clean_input_reduction clean_metric_tester_upper_bound

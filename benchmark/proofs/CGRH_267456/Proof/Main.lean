import Architect
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.Digraph.Orientation
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Nat.Log

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:directed-reachable"
  (statement := /-- Let $G$ be a directed graph on a vertex type $V$.  For $u,v\in V$, the
  predicate $\operatorname{DirectedReachable}_G(u,v)$ holds precisely when there is a directed
  path, possibly of length zero, from $u$ to $v$. -/)
  (title := /-- Directed reachability -/)
  (latexEnv := "definition")]
def directed_reachable {V : Type*} (G : Digraph V) (u v : V) : Prop :=
  Relation.ReflTransGen G.Adj u v

@[blueprint "def:reachability-embedding"
  (statement := /-- Let $G$ be a directed graph on $V$, let $d\in\mathbb N$, and let
  $a,b:V\to\mathbb R^d$.  The pair $(a,b)$ is a reachability embedding of $G$ if, for every
  ordered pair $u,v\in V$, one has
  \[
    \langle a(u),b(v)\rangle>0
    \quad\Longleftrightarrow\quad
    \operatorname{DirectedReachable}_G(u,v).
  \]
  Here directed reachability is the reflexive-transitive relation of
  \cref{def:directed-reachable}. -/)
  (title := /-- Reachability embedding -/)
  (latexEnv := "definition")]
def reachability_embedding {V : Type*} (G : Digraph V) (d : ℕ)
    (a b : V → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ u v, 0 < inner ℝ (a u) (b v) ↔ directed_reachable G u v

@[blueprint "def:admits-reachability-embedding"
  (statement := /-- A directed graph $G$ admits a reachability embedding of dimension $d$ if
  there exist maps $a,b:V\to\mathbb R^d$ which form a reachability embedding in the sense of
  \cref{def:reachability-embedding}. -/)
  (title := /-- Existence of a reachability embedding -/)
  (latexEnv := "definition")]
def admits_reachability_embedding {V : Type*} (G : Digraph V) (d : ℕ) : Prop :=
  ∃ a b : V → EuclideanSpace ℝ (Fin d), reachability_embedding G d a b

@[blueprint "def:directed-tree-decomposition"
  (statement := /-- Let $G$ be a directed graph on a vertex type $V$ with decidable equality.
  A tree decomposition of the underlying undirected graph of $G$ consists of a finite tree
  $T$, a finite bag $B_i\subseteq V$ for each vertex $i$ of $T$, and the following properties:
  every vertex of $G$ lies in a bag; the endpoints of every undirected edge obtained by
  forgetting the orientation of $G$ lie together in a bag; and, for each $v\in V$, the
  subgraph of $T$ induced by the indices $i$ satisfying $v\in B_i$ is connected. -/)
  (title := /-- Tree decomposition of the underlying graph -/)
  (latexEnv := "definition")]
structure directed_tree_decomposition {V : Type*} [DecidableEq V] (G : Digraph V) where
  BagIndex : Type
  [bagIndexFintype : Fintype BagIndex]
  [bagIndexDecidableEq : DecidableEq BagIndex]
  tree : SimpleGraph BagIndex
  treeIsTree : tree.IsTree
  bag : BagIndex → Finset V
  vertexCover : ∀ v, ∃ i, v ∈ bag i
  edgeCover : ∀ ⦃u v⦄, G.toSimpleGraphInclusive.Adj u v →
    ∃ i, u ∈ bag i ∧ v ∈ bag i
  runningIntersection : ∀ v, (tree.induce {i | v ∈ bag i}).Preconnected

@[blueprint "def:has-treewidth-at-most"
  (statement := /-- Let $G$ be a directed graph and let $t\in\mathbb N$.  The underlying
  undirected graph of $G$ has treewidth at most $t$ if it has a tree decomposition as in
  \cref{def:directed-tree-decomposition} every one of whose bags has cardinality at most
  $t+1$. -/)
  (title := /-- Treewidth bounded by a parameter -/)
  (latexEnv := "definition")]
def has_treewidth_at_most {V : Type*} [DecidableEq V] (G : Digraph V) (t : ℕ) : Prop :=
  ∃ D : directed_tree_decomposition G, ∀ i, (D.bag i).card ≤ t + 1

@[blueprint "lem:finite-digraph-card-reachability-embedding"
  (statement := /-- Let \(V\) be a finite type with decidable equality, and let \(G\) be a
  directed graph on \(V\).  Then \(G\) admits a reachability embedding of dimension
  \(|V|\). -/)
  (proof := /-- Enumerate \(V\), and identify \(\mathbb R^{|V|}\) with the coordinate space
  whose coordinates are indexed by the vertices.  For \(u\in V\), define \(a(u)\) to have
  \(v\)-coordinate \(1\) when \(v\) is reachable from \(u\), and \(-1\) otherwise.  Define
  \(b(v)\) to be the standard basis vector at \(v\).  Their inner product is exactly the
  \(v\)-coordinate of \(a(u)\), and is therefore positive if and only if \(v\) is reachable
  from \(u\).  Hence \(a\) and \(b\) satisfy
  \cref{def:reachability-embedding}, and the existential condition in
  \cref{def:admits-reachability-embedding} follows. -/)
  (title := /-- The cardinality-dimensional reachability embedding -/)
  (latexEnv := "lemma")]
lemma finite_digraph_card_reachability_embedding {V : Type*} [Fintype V] [DecidableEq V]
    (G : Digraph V) :
    admits_reachability_embedding G (Fintype.card V) := by
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  refine ⟨fun u => WithLp.toLp 2 (fun i =>
      if directed_reachable G u (e.symm i) then (1 : ℝ) else -1),
    fun v => EuclideanSpace.single (e v) 1, ?_⟩
  intro u v
  simp [reachability_embedding, EuclideanSpace.inner_single_right, e]
  by_cases h : directed_reachable G u v
  · simp [h]
  · simp [h]

@[blueprint "lem:weighted-tree-centroid"
  (statement := /-- Let \(T\) be a finite tree with vertex set \(I\), and assign a
  nonnegative integer weight \(w(i)\) to every \(i\in I\).  Suppose that
  \(\mathsf{avoids}(c,x,y)\) decides whether \(T\) has a walk from \(x\) to \(y\) whose
  support avoids \(c\).  Then there is a vertex \(c\in I\) such that, for every
  \(x\ne c\), the total weight of the component of \(T\setminus\{c\}\) containing \(x\)
  is at most one half of the total weight of \(T\). -/)
  (proof := /-- Put \(n=|I|\), and replace \(w\) temporarily by the strictly positive weight
  \(\widetilde w(y)=(n+1)w(y)+1\).  For a vertex \(z\), define
  \[
    \Phi(z)=\sum_{y\in I}\widetilde w(y)\operatorname{dist}_T(z,y).
  \]
  The connectedness assumption makes \(I\) nonempty, and finiteness therefore gives a vertex
  \(c\) minimizing \(\Phi\).

  Fix \(x\ne c\), let \(d\) be the first vertex after \(c\) on the unique simple path from
  \(c\) to \(x\), and let \(A\) be the set decided by
  \(\mathsf{avoids}(c,x,\cdot)\).  The tail of this path avoids \(c\); concatenating it, or
  its reverse, with avoiding walks shows that \(A\) is also the set decided by
  \(\mathsf{avoids}(c,d,\cdot)\).

  For every \(y\in I\), uniqueness of simple paths in the tree gives
  \[
    y\in A\quad\Longleftrightarrow\quad
    \operatorname{dist}_T(c,y)=\operatorname{dist}_T(d,y)+1.
  \]
  Indeed, an avoiding walk from \(d\) to \(y\) may be reduced to a simple path and the edge
  from \(c\) to \(d\) may then be prepended.  Conversely, if a shortest path from \(d\) to
  \(y\) passed through \(c\), splitting it at \(c\) would give the opposite distance
  equality.  Since distances from the endpoints of an edge differ by one, vertices outside
  \(A\) satisfy
  \(\operatorname{dist}_T(d,y)=\operatorname{dist}_T(c,y)+1\).

  Write \(W=\sum_{y\in I}w(y)\), \(S=\sum_{y\in A}w(y)\), and \(a=|A|\).  The corresponding
  perturbed weights are
  \(\widetilde W=(n+1)W+n\) and \(\widetilde S=(n+1)S+a\).  If \(2S>W\), then
  \(2S\ge W+1\); since \(a\le n\), it follows that \(2\widetilde S>\widetilde W\).
  Summing the two distance equalities over \(A\) and its complement yields
  \[
    \Phi(d)+2\widetilde S=\Phi(c)+\widetilde W.
  \]
  Thus \(2S>W\) would imply \(\Phi(d)<\Phi(c)\), contradicting the choice of \(c\).
  Consequently \(2S\le W\) for every \(x\ne c\), which is the required inequality. -/)
  (title := /-- A centroid of a finite weighted tree -/)
  (latexEnv := "lemma")]
lemma weighted_tree_centroid {I : Type*} [Fintype I] [DecidableEq I]
    (T : SimpleGraph I) (w : I → ℕ) (avoids : I → I → I → Bool)
    (hT : T.IsTree)
    (havoids : ∀ c x y, avoids c x y = true ↔ ∃ p : T.Walk x y, c ∉ p.support) :
    ∃ c, ∀ x, x ≠ c →
      2 * (Finset.sum (Finset.univ.filter (fun y => avoids c x y = true)) w) ≤
        Finset.sum Finset.univ w := by
  classical
  letI : Nonempty I := hT.connected.nonempty
  have path_length_eq_dist {u v : I} (p : T.Walk u v) (hp : p.IsPath) :
      p.length = T.dist u v := by
    obtain ⟨q, hq, hq_length⟩ := hT.connected.exists_path_of_dist u v
    have hpq : p = q := (hT.existsUnique_path u v).unique hp hq
    simpa [hpq] using hq_length
  have side_iff_dist (c d y : I) (hadj : T.Adj c d) :
      (∃ p : T.Walk d y, c ∉ p.support) ↔ T.dist c y = T.dist d y + 1 := by
    constructor
    · rintro ⟨p, hp⟩
      have havoid : c ∉ (p.toPath : T.Walk d y).support := by
        intro hmem
        exact hp (p.support_toPath_subset_support hmem)
      have hpath : (SimpleGraph.Walk.cons hadj (p.toPath : T.Walk d y)).IsPath :=
        p.toPath.property.cons havoid
      have hleft := path_length_eq_dist
        (SimpleGraph.Walk.cons hadj (p.toPath : T.Walk d y)) hpath
      have hright := path_length_eq_dist (p.toPath : T.Walk d y) p.toPath.property
      simp only [SimpleGraph.Walk.length_cons] at hleft
      omega
    · intro hdist
      obtain ⟨p, hp, hp_length⟩ := hT.connected.exists_path_of_dist d y
      refine ⟨p, ?_⟩
      intro hmem
      have htake := path_length_eq_dist (p.takeUntil c hmem) (hp.takeUntil hmem)
      have hdrop := path_length_eq_dist (p.dropUntil c hmem) (hp.dropUntil hmem)
      have htake_length := p.length_takeUntil hmem
      have hdrop_length := p.length_dropUntil hmem
      have hidx := List.idxOf_lt_length_of_mem hmem
      have hdc : T.dist d c = 1 := T.dist_eq_one_iff_adj.mpr hadj.symm
      have hsupport : p.support.length = p.length + 1 := p.length_support
      omega
  let weight : I → ℕ := fun y => (Fintype.card I + 1) * w y + 1
  let cost : I → ℕ := fun z => ∑ y, weight y * T.dist z y
  obtain ⟨c, -, hc⟩ := Finset.exists_min_image Finset.univ cost Finset.univ_nonempty
  refine ⟨c, ?_⟩
  intro x hxc
  by_contra hbalanced
  have hheavy : Finset.sum Finset.univ w <
      2 * Finset.sum (Finset.univ.filter (fun y => avoids c x y = true)) w :=
    Nat.lt_of_not_ge hbalanced
  obtain ⟨p, hp⟩ := hT.connected.exists_isPath c x
  cases p with
  | nil => exact (hxc rfl).elim
  | @cons _ d _ hadj q =>
      have hq_path : q.IsPath := hp.of_cons
      have hq_avoid : c ∉ q.support :=
        (SimpleGraph.Walk.cons_isPath_iff hadj q).mp hp |>.2
      have hcomponent (y : I) : avoids c x y = true ↔ avoids c d y = true := by
        rw [havoids, havoids]
        constructor
        · rintro ⟨r, hr⟩
          refine ⟨q.append r, ?_⟩
          simpa using And.intro hq_avoid hr
        · rintro ⟨r, hr⟩
          refine ⟨q.reverse.append r, ?_⟩
          simpa using And.intro hq_avoid hr
      have hfilter : Finset.univ.filter (fun y => avoids c x y = true) =
          Finset.univ.filter (fun y => avoids c d y = true) := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hcomponent y
      rw [hfilter] at hheavy
      let sideWeight : I → ℕ := fun y => if avoids c d y = true then weight y else 0
      have hweight_sum : Finset.sum Finset.univ weight =
          (Fintype.card I + 1) * Finset.sum Finset.univ w + Fintype.card I := by
        simp [weight, Finset.sum_add_distrib, Finset.mul_sum]
      have hside_sum : Finset.sum Finset.univ sideWeight =
          (Fintype.card I + 1) *
              Finset.sum (Finset.univ.filter (fun y => avoids c d y = true)) w +
            (Finset.univ.filter (fun y => avoids c d y = true)).card := by
        have hs : Finset.sum Finset.univ sideWeight =
            Finset.sum (Finset.univ.filter (fun y => avoids c d y = true)) weight := by
          simp only [sideWeight]
          rw [Finset.sum_ite]
          simp
        rw [hs]
        simp [weight, Finset.sum_add_distrib, Finset.mul_sum]
      have hcard : (Finset.univ.filter (fun y => avoids c d y = true)).card ≤
          Fintype.card I := by
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq Finset.card_univ
      have hside_heavy : Finset.sum Finset.univ weight <
          2 * Finset.sum Finset.univ sideWeight := by
        rw [hweight_sum, hside_sum]
        nlinarith
      have hcost : cost d + 2 * Finset.sum Finset.univ sideWeight =
          cost c + Finset.sum Finset.univ weight := by
        simp only [cost, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hside : avoids c d y = true
        · have hdist := (side_iff_dist c d y hadj).mp ((havoids c d y).mp hside)
          simp [sideWeight, hside, hdist]
          ring
        · have hdist_cases : T.dist c y = T.dist d y + 1 ∨
              T.dist d y = T.dist c y + 1 := by
            simpa [T.dist_comm] using hT.dist_eq_dist_add_one_of_adj y hadj
          have hnot : ¬T.dist c y = T.dist d y + 1 := by
            intro hdist
            exact hside ((havoids c d y).mpr ((side_iff_dist c d y hadj).mpr hdist))
          have hdist : T.dist d y = T.dist c y + 1 := hdist_cases.resolve_left hnot
          simp [sideWeight, hside, hdist]
          ring
      have hcost_lt : cost d < cost c := by omega
      exact (Nat.not_lt_of_ge (hc d (Finset.mem_univ d))) hcost_lt

@[blueprint "lem:balanced-separator-hierarchy-depth-bound"
  (statement := /-- Let \(n,h\in\mathbb N\), and let \((s_r)_{r\in\mathbb N}\) be a
  sequence of natural numbers.  Suppose that \(s_0\le n\), that \(s_h>0\), and that
  \(2s_{r+1}\le s_r\) for every \(r<h\).  Then
  \(h\le\lceil\log_2 n\rceil\). -/)
  (proof := /-- Induction on \(r\) gives \(2^r s_r\le s_0\) for every \(0\le r\le h\):
  the induction step multiplies \(2s_{r+1}\le s_r\) by \(2^r\).  Since \(s_h>0\),
  one has \(2^h\le 2^h s_h\le s_0\le n\).  Monotonicity of the ceiling logarithm,
  together with \(\lceil\log_2(2^h)\rceil=h\), now gives
  \(h\le\lceil\log_2 n\rceil\). -/)
  (title := /-- Logarithmic depth of a halving hierarchy -/)
  (latexEnv := "lemma")]
lemma balanced_separator_hierarchy_depth_bound (n h : ℕ) (size : ℕ → ℕ)
    (hroot : size 0 ≤ n) (hterminal : 0 < size h)
    (hhalve : ∀ r, r < h → 2 * size (r + 1) ≤ size r) :
    h ≤ Nat.clog 2 n := by
  have hpow : ∀ r, r ≤ h → 2 ^ r * size r ≤ size 0 := by
    intro r hr
    induction r with
    | zero => simp
    | succ r ih =>
      calc
        2 ^ (r + 1) * size (r + 1) =
            2 ^ r * (2 * size (r + 1)) := by ring
        _ ≤ 2 ^ r * size r := Nat.mul_le_mul_left _ (hhalve r (by omega))
        _ ≤ size 0 := ih (by omega)
  have hpower : 2 ^ h ≤ n := by
    calc
      2 ^ h = 2 ^ h * 1 := by simp
      _ ≤ 2 ^ h * size h := Nat.mul_le_mul_left _ (by omega)
      _ ≤ size 0 := hpow h le_rfl
      _ ≤ n := hroot
  have hclog := Nat.clog_mono (b := 2) (c := 2) (m := 2 ^ h) (n := n)
    (by omega) (by omega) hpower
  simpa using hclog

@[blueprint "def:separator-block-certificate"
  (statement := /-- Let \(G\) be a directed graph, and let \(q,h\in\mathbb N\).  A separator
  block certificate of block dimension \(q\) and height \(h\) consists, at every level
  \(0,\ldots,h\), of two maps from the vertices to \(\mathbb R^q\).  For a nonreachable
  ordered pair every level contribution is nonpositive.  For a reachable ordered pair there
  is a level at which the contribution is positive, while all earlier contributions are
  nonnegative.  Reachability is understood in the sense of
  \cref{def:directed-reachable}. -/)
  (title := /-- Certificate formed by separator-level Euclidean blocks -/)
  (latexEnv := "definition")]
structure separator_block_certificate {V : Type*} (G : Digraph V)
    (blockDimension height : ℕ) where
  leftBlock :
    Fin (height + 1) → V → EuclideanSpace ℝ (Fin blockDimension)
  rightBlock :
    Fin (height + 1) → V → EuclideanSpace ℝ (Fin blockDimension)
  nonreachable_nonpositive :
    ∀ r u v, ¬ directed_reachable G u v →
      inner ℝ (leftBlock r u) (rightBlock r v) ≤ 0
  reachable_positive_level :
    ∀ u v, directed_reachable G u v →
      ∃ r, (∀ s, s < r → 0 ≤ inner ℝ (leftBlock s u) (rightBlock s v)) ∧
        0 < inner ℝ (leftBlock r u) (rightBlock r v)

@[blueprint "lem:finset-sum-fiber-card"
  (statement := /-- Let \(f:A\to B\) be a map between finite types, let \(S\subseteq A\),
  and let \(T\subseteq B\).  The sum, over \(b\in T\), of the cardinalities of the fibers
  \(\{a\in S:f(a)=b\}\) equals the number of elements of \(S\) whose image lies in \(T\). -/)
  (proof := /-- Expand each cardinality as a sum of ones, interchange the two finite sums,
  and observe that for each \(a\in S\) exactly one summand survives precisely when
  \(f(a)\in T\). -/)
  (title := /-- Summing cardinalities of selected fibers -/)
  (latexEnv := "lemma")]
lemma finset_sum_fiber_card {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (S : Finset A) (T : Finset B) (f : A → B) :
    ∑ b ∈ T, (S.filter fun a => f a = b).card =
      (S.filter fun a => f a ∈ T).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

@[blueprint "def:balanced-vertex-separator-system"
  (statement := /-- A balanced vertex-separator system of width \(w\) assigns to every
  finite vertex set \(U\) a subset of at most \(w+1\) separator vertices and a natural-number
  side label on the remaining vertices.  Every side contains at most half of \(U\), and the
  endpoints of an underlying undirected edge outside the separator have the same side label. -/)
  (title := /-- Uniform balanced separators for finite vertex sets -/)
  (latexEnv := "definition")]
structure balanced_vertex_separator_system {V : Type*} [DecidableEq V]
    (G : Digraph V) (width : ℕ) where
  separator : Finset V → Finset V
  side : Finset V → V → ℕ
  separator_subset : ∀ (U : Finset V), separator U ⊆ U
  separator_card : ∀ (U : Finset V), (separator U).card ≤ width + 1
  side_half : ∀ (U : Finset V) k,
    2 * (U.filter fun v => v ∉ separator U ∧ side U v = k).card ≤ U.card
  edge_side : ∀ (U : Finset V) u v, u ∈ U → v ∈ U →
    u ∉ separator U → v ∉ separator U →
    G.toSimpleGraphInclusive.Adj u v → side U u = side U v

@[blueprint "lem:treewidth-balanced-vertex-separators"
  (statement := /-- Let \(G\) be a finite directed graph whose underlying undirected graph
  has a tree decomposition with bags of cardinality at most \(t+1\).  Then \(G\) has a
  balanced vertex-separator system of width \(t\). -/)
  (proof := /-- Fix a containing bag for each vertex.  For a finite vertex set \(U\), weight
  every decomposition-tree node by the number of vertices of \(U\) assigned to it and apply
  \cref{lem:weighted-tree-centroid}.  Intersect the centroid bag with \(U\).  Label a vertex
  outside this separator by the component of its assigned bag in the tree with the centroid
  deleted.  The fiber-counting identity \cref{lem:finset-sum-fiber-card} and the centroid
  inequality bound each side by \(|U|/2\).  The running-intersection axiom and the edge-cover
  axiom show that the assigned bags of adjacent vertices outside the separator lie in the
  same component. -/)
  (title := /-- Balanced separators supplied by a tree decomposition -/)
  (latexEnv := "lemma")]
lemma treewidth_balanced_vertex_separators {V : Type*} [Fintype V] [DecidableEq V]
    (G : Digraph V) (t : ℕ) (D : directed_tree_decomposition G)
    (hbags : ∀ i, (D.bag i).card ≤ t + 1) :
    Nonempty (balanced_vertex_separator_system G t) := by
  classical
  letI := D.bagIndexFintype
  letI := D.bagIndexDecidableEq
  let home (v : V) : D.BagIndex := Classical.choose (D.vertexCover v)
  have home_mem (v : V) : v ∈ D.bag (home v) := Classical.choose_spec (D.vertexCover v)
  let avoids (c x y : D.BagIndex) : Bool :=
    decide (∃ p : D.tree.Walk x y, c ∉ p.support)
  have havoids (c x y : D.BagIndex) :
      avoids c x y = true ↔ ∃ p : D.tree.Walk x y, c ∉ p.support := by
    simp [avoids]
  let weight (U : Finset V) (i : D.BagIndex) : ℕ :=
    (U.filter fun v => home v = i).card
  have centroid_exists (U : Finset V) :
      ∃ c, ∀ x, x ≠ c →
        2 * (Finset.sum (Finset.univ.filter (fun y => avoids c x y = true)) (weight U)) ≤
          Finset.sum Finset.univ (weight U) :=
    weighted_tree_centroid D.tree (weight U) avoids D.treeIsTree havoids
  let center (U : Finset V) : D.BagIndex := Classical.choose (centroid_exists U)
  have center_spec (U : Finset V) : ∀ x, x ≠ center U →
      2 * (Finset.sum (Finset.univ.filter
        (fun y => avoids (center U) x y = true)) (weight U)) ≤
        Finset.sum Finset.univ (weight U) :=
    Classical.choose_spec (centroid_exists U)
  let sideSet (c x : D.BagIndex) : Finset D.BagIndex :=
    Finset.univ.filter fun y => avoids c x y = true
  let code (A : Finset D.BagIndex) : ℕ := (Fintype.equivFin (Finset D.BagIndex) A).val
  let separator (U : Finset V) : Finset V := U.filter fun v => v ∈ D.bag (center U)
  let side (U : Finset V) (v : V) : ℕ := code (sideSet (center U) (home v))
  have weight_sum (U : Finset V) : Finset.sum Finset.univ (weight U) = U.card := by
    simpa [weight] using finset_sum_fiber_card U Finset.univ home
  have weight_side_sum (U : Finset V) (A : Finset D.BagIndex) :
      Finset.sum A (weight U) = (U.filter fun v => home v ∈ A).card := by
    simpa [weight] using finset_sum_fiber_card U A home
  have avoids_refl (c x : D.BagIndex) (hxc : x ≠ c) : avoids c x x = true := by
    apply (havoids c x x).2
    exact ⟨.nil, by simpa [Ne.symm hxc]⟩
  have avoids_symm (c x y : D.BagIndex) (hxy : avoids c x y = true) :
      avoids c y x = true := by
    rcases (havoids c x y).1 hxy with ⟨p, hp⟩
    apply (havoids c y x).2
    exact ⟨p.reverse, by simpa using hp⟩
  have avoids_trans (c x y z : D.BagIndex) (hxy : avoids c x y = true)
      (hyz : avoids c y z = true) : avoids c x z = true := by
    rcases (havoids c x y).1 hxy with ⟨p, hp⟩
    rcases (havoids c y z).1 hyz with ⟨q, hq⟩
    apply (havoids c x z).2
    exact ⟨p.append q, by simp [hp, hq]⟩
  have sideSet_eq (c x y : D.BagIndex) (hxy : avoids c x y = true) :
      sideSet c x = sideSet c y := by
    ext z
    simp only [sideSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun hxz => avoids_trans c y x z (avoids_symm c x y hxy) hxz
    · exact fun hyz => avoids_trans c x y z hxy hyz
  have code_injective : Function.Injective code := by
    intro A B hAB
    apply (Fintype.equivFin (Finset D.BagIndex)).injective
    exact Fin.ext hAB
  have bag_walk_avoiding (v : V) (c i j : D.BagIndex) (hi : v ∈ D.bag i)
      (hj : v ∈ D.bag j) (hc : v ∉ D.bag c) : avoids c i j = true := by
    let ii : {k // v ∈ D.bag k} := ⟨i, hi⟩
    let jj : {k // v ∈ D.bag k} := ⟨j, hj⟩
    rcases D.runningIntersection v ii jj with ⟨p⟩
    let q := p.map (SimpleGraph.Embedding.induce (G := D.tree) {k | v ∈ D.bag k}).toHom
    apply (havoids c i j).2
    refine ⟨q, ?_⟩
    intro hcq
    change c ∈ (p.map
      (SimpleGraph.Embedding.induce (G := D.tree) {k | v ∈ D.bag k}).toHom).support at hcq
    rw [SimpleGraph.Walk.support_map] at hcq
    rcases List.mem_map.1 hcq with ⟨a, ha, hac⟩
    exact hc (hac ▸ a.property)
  refine ⟨{
    separator := separator
    side := side
    separator_subset := ?_
    separator_card := ?_
    side_half := ?_
    edge_side := ?_ }⟩
  · intro U v hv
    exact (Finset.mem_filter.1 hv).1
  · intro U
    apply (Finset.card_le_card ?_).trans (hbags (center U))
    intro v hv
    exact (Finset.mem_filter.1 hv).2
  · intro U k
    let C := U.filter fun v => v ∉ separator U ∧ side U v = k
    by_cases hC : C.Nonempty
    · obtain ⟨v, hvC⟩ := hC
      have hv := Finset.mem_filter.1 hvC
      have hvU : v ∈ U := hv.1
      have hvsep : v ∉ separator U := hv.2.1
      have hvside : side U v = k := hv.2.2
      have hvbag : v ∉ D.bag (center U) := by
        intro hvbag
        exact hvsep (by simp [separator, hvU, hvbag])
      have hvhome : home v ≠ center U := by
        intro heq
        exact hvbag (heq ▸ home_mem v)
      let A := sideSet (center U) (home v)
      have hCA : C ⊆ U.filter fun z => home z ∈ A := by
        intro z hzC
        have hz := Finset.mem_filter.1 hzC
        have hzU : z ∈ U := hz.1
        have hzsep : z ∉ separator U := hz.2.1
        have hzside : side U z = k := hz.2.2
        have hzbag : z ∉ D.bag (center U) := by
          intro hzbag
          exact hzsep (by simp [separator, hzU, hzbag])
        have hzhome : home z ≠ center U := by
          intro heq
          exact hzbag (heq ▸ home_mem z)
        have hsets : sideSet (center U) (home z) = A := by
          apply code_injective
          simpa [side, A] using hzside.trans hvside.symm
        apply Finset.mem_filter.2
        refine ⟨hzU, ?_⟩
        rw [← hsets]
        simp [sideSet, avoids_refl (center U) (home z) hzhome]
      calc
        2 * C.card ≤ 2 * (U.filter fun z => home z ∈ A).card :=
          Nat.mul_le_mul_left 2 (Finset.card_le_card hCA)
        _ = 2 * Finset.sum A (weight U) := by rw [weight_side_sum]
        _ ≤ Finset.sum Finset.univ (weight U) := center_spec U (home v) hvhome
        _ = U.card := weight_sum U
    · have hCcard : C.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.1 hC)
      simpa [C, hCcard]
  · intro U u v huU hvU husep hvsep huv
    obtain ⟨i, hui, hvi⟩ := D.edgeCover huv
    have hubag : u ∉ D.bag (center U) := by
      intro hubag
      exact husep (by simp [separator, huU, hubag])
    have hvbag : v ∉ D.bag (center U) := by
      intro hvbag
      exact hvsep (by simp [separator, hvU, hvbag])
    have huiAvoid : avoids (center U) (home u) i = true :=
      bag_walk_avoiding u (center U) (home u) i (home_mem u) hui hubag
    have hviAvoid : avoids (center U) (home v) i = true :=
      bag_walk_avoiding v (center U) (home v) i (home_mem v) hvi hvbag
    have huvAvoid : avoids (center U) (home u) (home v) = true :=
      avoids_trans (center U) (home u) i (home v) huiAvoid
        (avoids_symm (center U) (home v) i hviAvoid)
    simp only [side]
    exact congrArg code (sideSet_eq (center U) (home u) (home v) huvAvoid)

@[blueprint "def:separator-hierarchy"
  (statement := /-- Let \(G\) be a directed graph, let \(w,h\in\mathbb N\), and number the
  levels by \(0,\ldots,h\).  A separator hierarchy assigns every vertex a removal level, a
  region at each level, and one of \(w+1\) separator slots.  Adjacent vertices that are
  active at a level have the same region, and two vertices removed in the same region and
  slot at the same level are equal. -/)
  (title := /-- A finite vertex-separator hierarchy -/)
  (latexEnv := "definition")]
structure separator_hierarchy {V : Type*} (G : Digraph V) (width height : ℕ) where
  depth : V → ℕ
  depth_le : ∀ v, depth v ≤ height
  region : ℕ → V → ℕ
  slot : V → Fin (width + 1)
  edge_region : ∀ r u v, G.toSimpleGraphInclusive.Adj u v →
    r ≤ depth u → r ≤ depth v → region r u = region r v
  separator_slot_injective : ∀ u v, depth u = depth v →
    region (depth u) u = region (depth v) v → slot u = slot v → u = v

@[blueprint "lem:balanced-vertex-separators-hierarchy"
  (statement := /-- A balanced vertex-separator system of width \(w\) on a finite directed
  graph with \(n\) vertices gives a separator hierarchy of width \(w\) and height
  \(\lceil\log_2 n\rceil\). -/)
  (proof := /-- Apply strong induction to a finite active vertex set \(U\).  Remove its
  prescribed separator and recurse on every side.  The side-size inequality makes each
  recursive set proper and gives
  \(1+\lceil\log_2 |U_k|\rceil\le\lceil\log_2 |U|\rceil\).
  Give the root separator depth zero; increase child depths by one; pair the side label with
  each child-region label; and retain child slots.  The separator-cardinality bound supplies
  injective root slots.  Edge-side compatibility and the induction hypotheses establish the
  hierarchy axioms. -/)
  (title := /-- Recursive hierarchy from balanced vertex separators -/)
  (latexEnv := "lemma")]
lemma balanced_vertex_separators_hierarchy {V : Type*} [Fintype V] [DecidableEq V]
    (G : Digraph V) (width : ℕ) (B : balanced_vertex_separator_system G width) :
    Nonempty (separator_hierarchy G width (Nat.clog 2 (Fintype.card V))) := by
  classical
  let induced (U : Finset V) : Digraph U := ⟨fun u v => G.Adj u.1 v.1⟩
  let child (U : Finset V) (k : ℕ) : Finset V :=
    U.filter fun v => v ∉ B.separator U ∧ B.side U v = k
  have build (U : Finset V) :
      Nonempty (separator_hierarchy (induced U) width (Nat.clog 2 U.card)) := by
    refine Finset.strongInductionOn (p := fun U =>
      Nonempty (separator_hierarchy (induced U) width (Nat.clog 2 U.card))) U ?_
    intro U ih
    by_cases hU : U = ∅
    · let emptyEquiv : U ≃ Fin 0 := Fintype.equivFinOfCardEq (by simp [hU])
      have no_vertex (x : U) : False := Fin.elim0 (emptyEquiv x)
      refine ⟨{
          depth := fun x => (no_vertex x).elim
          depth_le := fun x => (no_vertex x).elim
          region := fun _ x => (no_vertex x).elim
          slot := fun x => (no_vertex x).elim
          edge_region := fun _ x => (no_vertex x).elim
          separator_slot_injective := fun x => (no_vertex x).elim }⟩
    · have hUne : U.Nonempty := Finset.nonempty_iff_ne_empty.2 hU
      have child_ssubset (k : ℕ) : child U k ⊂ U := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨fun v hv => (Finset.mem_filter.1 hv).1, ?_⟩
        intro heq
        have hhalf := B.side_half U k
        have hpos : 0 < U.card := Finset.card_pos.mpr hUne
        change 2 * (child U k).card ≤ U.card at hhalf
        have hcard : (child U k).card = U.card := congrArg Finset.card heq
        omega
      let CH (k : ℕ) : separator_hierarchy (induced (child U k)) width
            (Nat.clog 2 (child U k).card) := Classical.choice (ih _ (child_ssubset k))
      let cv (x : U) (hx : x.1 ∉ B.separator U) : child U (B.side U x.1) :=
          ⟨x.1, by simp [child, x.2, hx]⟩
      let cdepth (k : ℕ) (v : V) : ℕ := if hv : v ∈ child U k then
          (CH k).depth ⟨v, hv⟩ else 0
      let cregion (k r : ℕ) (v : V) : ℕ := if hv : v ∈ child U k then
          (CH k).region r ⟨v, hv⟩ else 0
      let cslot (k : ℕ) (v : V) : Fin (width + 1) := if hv : v ∈ child U k then
          (CH k).slot ⟨v, hv⟩ else ⟨0, Nat.succ_pos width⟩
      have child_clog (x : U) (hx : x.1 ∉ B.separator U) :
            Nat.clog 2 (child U (B.side U x.1)).card + 1 ≤ Nat.clog 2 U.card := by
          have hm : 0 < (child U (B.side U x.1)).card := by
            apply Finset.card_pos.mpr
            exact ⟨x.1, by simp [child, x.2, hx]⟩
          have hhalf := B.side_half U (B.side U x.1)
          change 2 * (child U (B.side U x.1)).card ≤ U.card at hhalf
          have hdouble : Nat.clog 2 (2 * (child U (B.side U x.1)).card) =
              Nat.clog 2 (child U (B.side U x.1)).card + 1 := by
            rw [Nat.clog_of_two_le (by norm_num) (by omega)]
            congr 1
            rw [show 2 * (child U (B.side U x.1)).card + 2 - 1 =
              1 + 2 * (child U (B.side U x.1)).card by omega]
            rw [Nat.add_mul_div_left _ _ (by norm_num)]
            simp
          rw [← hdouble]
          exact Nat.clog_mono (by omega) le_rfl hhalf
      let depth (x : U) : ℕ := if hx : x.1 ∈ B.separator U then 0
          else cdepth (B.side U x.1) x.1 + 1
      let region (r : ℕ) (x : U) : ℕ := match r with
          | 0 => 0
          | r + 1 => if hx : x.1 ∈ B.separator U then 0
            else Nat.pair (B.side U x.1) (cregion (B.side U x.1) r x.1)
      let slot (x : U) : Fin (width + 1) := if hx : x.1 ∈ B.separator U then
          Fin.castLE (B.separator_card U) ((B.separator U).equivFin ⟨x.1, hx⟩)
          else cslot (B.side U x.1) x.1
      refine ⟨{
          depth := depth
          depth_le := ?_
          region := region
          slot := slot
          edge_region := ?_
          separator_slot_injective := ?_ }⟩
      · intro x
        by_cases hx : x.1 ∈ B.separator U
        · simp [depth, hx]
        · simp only [depth, hx, dite_false]
          have hmem : x.1 ∈ child U (B.side U x.1) := by simp [child, x.2, hx]
          have hle : cdepth (B.side U x.1) x.1 ≤
              Nat.clog 2 (child U (B.side U x.1)).card := by
            simpa [cdepth, hmem] using (CH (B.side U x.1)).depth_le ⟨x.1, hmem⟩
          exact (Nat.succ_le_succ hle).trans (child_clog x hx)
      · intro r x y hxy hrx hry
        rcases r with _ | r
        · rfl
        have hxn : x.1 ∉ B.separator U := by
            intro hx
            simp [depth, hx] at hrx
        have hyn : y.1 ∉ B.separator U := by
            intro hy
            simp [depth, hy] at hry
        have horig : G.toSimpleGraphInclusive.Adj x.1 y.1 := by
            simpa [induced, Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj] using hxy
        have hside : B.side U x.1 = B.side U y.1 :=
            B.edge_side U x.1 y.1 x.2 y.2 hxn hyn horig
        have hchildAdj : (induced (child U (B.side U y.1))).toSimpleGraphInclusive.Adj
              ⟨x.1, by simpa [child, x.2, hxn, hside]⟩ (cv y hyn) := by
            simpa [induced, cv, Digraph.toSimpleGraphInclusive,
              SimpleGraph.fromRel_adj] using horig
        have hcx : r ≤ (CH (B.side U y.1)).depth
              ⟨x.1, by simpa [child, x.2, hxn, hside]⟩ := by
            simp [depth, hxn] at hrx
            have hr : r ≤ cdepth (B.side U x.1) x.1 := by omega
            rw [hside] at hr
            simpa [cdepth, child, x.2, hxn, hside] using hr
        have hcy : r ≤ (CH (B.side U y.1)).depth (cv y hyn) := by
            simp [depth, hyn] at hry
            have hr : r ≤ cdepth (B.side U y.1) y.1 := by omega
            simpa [cdepth, child, y.2, hyn, cv] using hr
        have hc := (CH (B.side U y.1)).edge_region r _ _ hchildAdj hcx hcy
        simp only [region, hxn, hyn, dite_false]
        rw [hside]
        simpa [cregion, child, x.2, y.2, hxn, hyn, hside, cv] using
          congrArg (Nat.pair (B.side U y.1)) hc
      · intro x y hdepth hregion hslot
        by_cases hx : x.1 ∈ B.separator U
        · by_cases hy : y.1 ∈ B.separator U
          · have hs : (B.separator U).equivFin ⟨x.1, hx⟩ =
                  (B.separator U).equivFin ⟨y.1, hy⟩ := by
                apply Fin.ext
                exact congrArg Fin.val (by simpa [slot, hx, hy] using hslot)
            have hsepEq := (B.separator U).equivFin.injective hs
            have hvalEq : x.1 = y.1 :=
              congrArg (fun z : ↥(B.separator U) => z.1) hsepEq
            exact Subtype.ext hvalEq
          · simp [depth, hx, hy] at hdepth
        · by_cases hy : y.1 ∈ B.separator U
          · simp [depth, hx, hy] at hdepth
          · have hunpair : B.side U x.1 = B.side U y.1 ∧
                  cregion (B.side U x.1) (cdepth (B.side U x.1) x.1) x.1 =
                    cregion (B.side U y.1) (cdepth (B.side U y.1) y.1) y.1 := by
                simpa [depth, region, hx, hy] using hregion
            have hside : B.side U x.1 = B.side U y.1 := hunpair.1
            have hd' : cdepth (B.side U x.1) x.1 =
                cdepth (B.side U y.1) y.1 := by
              simp [depth, hx, hy] at hdepth
              omega
            have hr' : cregion (B.side U x.1) (cdepth (B.side U x.1) x.1) x.1 =
                cregion (B.side U y.1) (cdepth (B.side U y.1) y.1) y.1 := by
              exact hunpair.2
            have hs' : cslot (B.side U x.1) x.1 = cslot (B.side U y.1) y.1 := by
              simpa [slot, hx, hy] using hslot
            rw [hside] at hd' hr' hs'
            have hchild : (⟨x.1, by simpa [child, x.2, hx, hside]⟩ :
                  child U (B.side U y.1)) = cv y hy := by
                apply (CH (B.side U y.1)).separator_slot_injective
                · simpa [cdepth, child, x.2, y.2, hx, hy, hside, cv] using hd'
                · simpa [cregion, cdepth, child, x.2, y.2, hx, hy, hside, cv] using hr'
                · simpa [cslot, child, x.2, y.2, hx, hy, hside, cv] using hs'
            have hvalEq : x.1 = y.1 := congrArg
              (fun z : ↥(child U (B.side U y.1)) => z.1) hchild
            exact Subtype.ext hvalEq
  let E : V ≃ (Finset.univ : Finset V) :=
    ⟨fun v => ⟨v, Finset.mem_univ v⟩, fun v => v.1, fun _ => rfl, fun _ => Subtype.ext rfl⟩
  let H := Classical.choice (build Finset.univ)
  refine ⟨{
    depth := fun v => H.depth (E v)
    depth_le := fun v => H.depth_le (E v)
    region := fun r v => H.region r (E v)
    slot := fun v => H.slot (E v)
    edge_region := ?_
    separator_slot_injective := ?_ }⟩
  · intro r u v huv hru hrv
    apply H.edge_region r (E u) (E v) _ hru hrv
    simpa [induced, E, Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj] using huv
  · intro u v hd hr hs
    exact E.injective (H.separator_slot_injective (E u) (E v) hd hr hs)

@[blueprint "lem:separator-hierarchy-certificate"
  (statement := /-- Every separator hierarchy of width \(w\) and height \(h\) for a finite
  directed graph gives a separator block certificate of height \(h\) and block dimension
  \(3(w+1)\). -/)
  (proof := /-- At level \(r\), give every active region a distinct natural-number code.
  For each separator slot use the three coordinates
  \((1,c,c^2)\) on the left and \((\tfrac12-c^2,2c,-1)\) on the right, multiplied by the
  appropriate reachability indicators.  Their inner product is
  \(\tfrac12-(c-c')^2\).  Distinct regions therefore contribute nonpositively.  In one
  region, equality of the level and slot identifies the separator vertex; hence a positive
  term factors a directed path through that vertex.  Along a reachable directed path,
  choose a vertex of minimum removal depth.  At all earlier levels the path lies in one
  active region, while at the chosen level its separator slot gives a positive term. -/)
  (title := /-- Euclidean blocks from a separator hierarchy -/)
  (latexEnv := "lemma")]
lemma separator_hierarchy_certificate {V : Type*} [Fintype V] [DecidableEq V]
    (G : Digraph V) (width height : ℕ) (H : separator_hierarchy G width height) :
    Nonempty (separator_block_certificate G (3 * (width + 1)) height) := by
  classical
  let e : Fin 3 × Fin (width + 1) ≃ Fin (3 * (width + 1)) := finProdFinEquiv
  let p (r : Fin (height + 1)) (u : V) (j : Fin (width + 1)) : Prop :=
    ∃ s, H.depth s = r.val ∧ H.region r.val s = H.region r.val u ∧ H.slot s = j ∧
      directed_reachable G u s
  let q (r : Fin (height + 1)) (v : V) (j : Fin (width + 1)) : Prop :=
    ∃ s, H.depth s = r.val ∧ H.region r.val s = H.region r.val v ∧ H.slot s = j ∧
      directed_reachable G s v
  let left (r : Fin (height + 1)) (u : V) :
      EuclideanSpace ℝ (Fin (3 * (width + 1))) :=
    WithLp.toLp 2 (fun i =>
      if p r u (e.symm i).2 then
        ![(1 : ℝ), H.region r.val u, (H.region r.val u : ℝ) ^ 2] (e.symm i).1
      else 0)
  let right (r : Fin (height + 1)) (v : V) :
      EuclideanSpace ℝ (Fin (3 * (width + 1))) :=
    WithLp.toLp 2 (fun i =>
      if q r v (e.symm i).2 then
        ![(1 / 2 : ℝ) - (H.region r.val v : ℝ) ^ 2,
          2 * H.region r.val v, (-1 : ℝ)] (e.symm i).1
      else 0)
  have inner_eq (r : Fin (height + 1)) (u v : V) :
      inner ℝ (left r u) (right r v) =
        ∑ j : Fin (width + 1),
          (if p r u j ∧ q r v j then (1 : ℝ) else 0) *
            ((1 / 2 : ℝ) - ((H.region r.val u : ℝ) - H.region r.val v) ^ 2) := by
    simp only [left, right, EuclideanSpace.inner_toLp_toLp, dotProduct]
    rw [← e.sum_comp]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Fintype.sum_congr
    intro j
    rw [Fin.sum_univ_three]
    by_cases hp : p r u j <;> by_cases hq : q r v j <;>
      simp [e.symm_apply_apply, hp, hq] <;> ring
  have adjacent_region (r : ℕ) {u v : V} (huv : G.Adj u v)
      (hu : r ≤ H.depth u) (hv : r ≤ H.depth v) :
      H.region r u = H.region r v := by
    by_cases heq : u = v
    · simpa [heq]
    · exact H.edge_region r u v (by
        simp only [Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj]
        exact ⟨heq, Or.inl huv⟩) hu hv
  have path_min {u v : V} (huv : directed_reachable G u v) :
      ∃ s, directed_reachable G u s ∧ directed_reachable G s v ∧
        H.depth s ≤ H.depth u ∧ H.depth s ≤ H.depth v ∧
        ∀ r : ℕ, r ≤ H.depth s →
          H.region r u = H.region r s ∧ H.region r s = H.region r v := by
    induction huv using Relation.ReflTransGen.head_induction_on with
    | refl =>
        exact ⟨v, .refl, .refl, le_rfl, le_rfl, fun r hr => ⟨rfl, rfl⟩⟩
    | @head u w huv huw ih =>
        rcases ih with ⟨s, hws, hsv, hsdw, hsdv, hregions⟩
        by_cases hsu : H.depth s ≤ H.depth u
        · refine ⟨s, hws.head huv, hsv, hsu, hsdv, ?_⟩
          intro r hrs
          have hurw : H.region r u = H.region r w :=
            adjacent_region r huv (hrs.trans hsu) (hrs.trans hsdw)
          rcases hregions r hrs with ⟨hrws, hrsv⟩
          exact ⟨hurw.trans hrws, hrsv⟩
        · have hus : H.depth u ≤ H.depth s := le_of_not_ge hsu
          refine ⟨u, .refl, huw.head huv, le_rfl, hus.trans hsdv, ?_⟩
          intro r hru
          have hurw : H.region r u = H.region r w :=
            adjacent_region r huv hru (hru.trans (hus.trans hsdw))
          rcases hregions r (hru.trans hus) with ⟨hrws, hrsv⟩
          exact ⟨rfl, hurw.trans (hrws.trans hrsv)⟩
  refine ⟨{
    leftBlock := left
    rightBlock := right
    nonreachable_nonpositive := ?_
    reachable_positive_level := ?_ }⟩
  · intro r u v hn
    rw [inner_eq]
    apply Finset.sum_nonpos
    intro j hj
    by_cases hpq : p r u j ∧ q r v j
    · have hregions : H.region r u ≠ H.region r v := by
        intro huv
        rcases hpq.1 with ⟨su, hdu, hsu, hslotu, hreachu⟩
        rcases hpq.2 with ⟨sv, hdv, hsv, hslotv, hreachv⟩
        have hsuv : su = sv := H.separator_slot_injective su sv
          (hdu.trans hdv.symm) (by simpa [hdu, hdv, hsu, hsv] using huv)
          (hslotu.trans hslotv.symm)
        subst sv
        exact hn (hreachu.trans hreachv)
      have hgap : (1 : ℝ) ≤
          ((H.region r u : ℝ) - H.region r v) ^ 2 := by
        rcases lt_or_gt_of_ne hregions with huv | huv
        · have hcast : (H.region r u : ℝ) + 1 ≤ H.region r v := by
            exact_mod_cast (Nat.succ_le_iff.mpr huv)
          nlinarith [sq_nonneg ((H.region r u : ℝ) - H.region r v)]
        · have hcast : (H.region r v : ℝ) + 1 ≤ H.region r u := by
            exact_mod_cast (Nat.succ_le_iff.mpr huv)
          nlinarith [sq_nonneg ((H.region r u : ℝ) - H.region r v)]
      simp only [hpq.1, hpq.2, and_self, if_true, one_mul]
      linarith
    · simp [hpq]
  · intro u v huv
    rcases path_min huv with ⟨s, hus, hsv, hsu, hsvdepth, hregions⟩
    let rs : Fin (height + 1) := ⟨H.depth s, Nat.lt_succ_of_le (H.depth_le s)⟩
    refine ⟨rs, ?_, ?_⟩
    · intro r hrs
      rw [inner_eq]
      apply Finset.sum_nonneg
      intro j hj
      have hreg := hregions r (le_of_lt hrs)
      have huvreg : H.region r u = H.region r v := hreg.1.trans hreg.2
      have hcast : (H.region r u : ℝ) = H.region r v :=
        congrArg (fun z : ℕ => (z : ℝ)) huvreg
      rw [hcast]
      by_cases hpq : p r u j ∧ q r v j <;> simp [hpq]
    · rw [inner_eq]
      have hreg := hregions rs.val (by simp [rs])
      have huvreg : H.region rs.val u = H.region rs.val v :=
        hreg.1.trans hreg.2
      have hcast : (H.region rs.val u : ℝ) = H.region rs.val v :=
        congrArg (fun z : ℕ => (z : ℝ)) huvreg
      apply Finset.sum_pos'
      · intro j hj
        rw [hcast]
        by_cases hpq : p rs u j ∧ q rs v j <;> simp [hpq]
      · have hp : p rs u (H.slot s) :=
          ⟨s, by simp [rs], hreg.1.symm, rfl, hus⟩
        have hq : q rs v (H.slot s) :=
          ⟨s, by simp [rs], hreg.2, rfl, hsv⟩
        refine ⟨H.slot s, Finset.mem_univ _, ?_⟩
        rw [hcast]
        norm_num [hp, hq]

@[blueprint "lem:balanced-separator-hierarchy"
  (statement := /-- Let \(V\) be a finite type with decidable equality, let \(G\) be a
  directed graph on \(V\), and let \(n,t\in\mathbb N\).  Suppose that \(|V|=n\) and that
  the underlying undirected graph of \(G\) has treewidth at most \(t\).  Then there exist
  \(h\in\mathbb N\), with \(h\le\lceil\log_2 n\rceil\), and a separator block certificate
  for \(G\) of height \(h\) and block dimension \(3(t+1)\), as in
  \cref{def:separator-block-certificate}. -/)
  (proof := /-- Choose a tree decomposition witnessing the treewidth hypothesis.
  By \cref{lem:treewidth-balanced-vertex-separators}, it supplies balanced separators of
  cardinality at most \(t+1\) for every finite active vertex set.  Apply
  \cref{lem:balanced-vertex-separators-hierarchy} to obtain a separator hierarchy of width
  \(t\) and height \(\lceil\log_2 |V|\rceil\).  Then
  \cref{lem:separator-hierarchy-certificate} converts this hierarchy into a separator block
  certificate of block dimension \(3(t+1)\) and the same height.  Since \(|V|=n\), choosing
  \(h=\lceil\log_2 n\rceil\) gives the asserted bound.  Formally, the reflexive height
  inequality is paired with the auxiliary inequality obtained by applying
  \cref{lem:balanced-separator-hierarchy-depth-bound} to the constant size sequence at
  \(n=1\) and height zero. -/)
  (title := /-- Recursive separator blocks of logarithmic height -/)
  (latexEnv := "lemma")]
lemma balanced_separator_hierarchy :
    ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : Digraph V) (n t : ℕ),
      Fintype.card V = n →
      has_treewidth_at_most G t →
      ∃ h : ℕ, h ≤ Nat.clog 2 n ∧
        Nonempty (separator_block_certificate G (3 * (t + 1)) h) := by
  classical
  intro V instFintype instDecidableEq G n t hn htw
  subst n
  obtain ⟨D, hbags⟩ := htw
  let B := Classical.choice (treewidth_balanced_vertex_separators G t D hbags)
  let H := Classical.choice (balanced_vertex_separators_hierarchy G t B)
  have hcertificate := separator_hierarchy_certificate G t (Nat.clog 2 (Fintype.card V)) H
  have haux : 0 ≤ Nat.clog 2 1 := balanced_separator_hierarchy_depth_bound
    1 0 (fun _ => 1) (by simp) (by simp) (by intro r hr; omega)
  refine ⟨Nat.clog 2 (Fintype.card V), ?_, hcertificate⟩
  exact (show Nat.clog 2 (Fintype.card V) ≤ Nat.clog 2 (Fintype.card V) ∧
    0 ≤ Nat.clog 2 1 from ⟨le_rfl, haux⟩).1

@[blueprint "lem:finite-lexicographic-positive-weights"
  (statement := /-- Let \(n\in\mathbb N\), let \(K\) be a finite type, and let
  \(c:\{0,\ldots,n-1\}\times K\to\mathbb R\).  Suppose that, for every \(k\in K\), there
  is an index \(r\) such that \(c(s,k)\ge 0\) for every \(s<r\) and \(c(r,k)>0\).  Then
  there are positive weights \(w_0,\ldots,w_{n-1}\) such that
  \(\sum_r w_r c(r,k)>0\) for every \(k\in K\). -/)
  (proof := /-- We argue by induction on \(n\).  The assertion for \(n=0\) is vacuous,
  since the hypothesis forces \(K\) to be empty.  For the induction step, every leading
  coefficient \(c(0,k)\) is nonnegative.  Apply the induction hypothesis to the tail
  coefficients for those \(k\) with \(c(0,k)=0\), obtaining positive tail weights.  Let
  \(T_k\) be the resulting weighted tail sum.  Choose the leading weight to be
  \[
    1+\sum_{c(0,k)>0}\frac{|T_k|}{c(0,k)}.
  \]
  If \(c(0,k)=0\), positivity follows from the induction hypothesis.  If \(c(0,k)>0\),
  the corresponding summand in the displayed expression shows that the positive leading
  contribution strictly exceeds \(|T_k|\), so the entire weighted sum is positive. -/)
  (title := /-- Positive weights for finitely many lexicographic sign constraints -/)
  (latexEnv := "lemma")]
lemma finite_lexicographic_positive_weights (n : ℕ) {κ : Type*} [Fintype κ]
    (c : Fin n → κ → ℝ)
    (hc : ∀ k, ∃ r, (∀ s, s < r → 0 ≤ c s k) ∧ 0 < c r k) :
    ∃ w : Fin n → ℝ, (∀ r, 0 < w r) ∧ ∀ k, 0 < ∑ r, w r * c r k := by
  induction n generalizing κ with
  | zero =>
      classical
      let w : Fin 0 → ℝ := fun r => Fin.elim0 r
      refine ⟨w, ?_, ?_⟩
      · intro r
        exact Fin.elim0 r
      · intro k
        obtain ⟨r, hr⟩ := hc k
        exact Fin.elim0 r
  | succ n ih =>
      classical
      have hc0 (k : κ) : 0 ≤ c 0 k := by
        obtain ⟨r, hr, hpos⟩ := hc k
        cases r using Fin.cases with
        | zero => exact le_of_lt hpos
        | succ r => exact hr 0 (by simp)
      let Z := {k : κ // c 0 k = 0}
      let ct : Fin n → Z → ℝ := fun r k => c r.succ k.1
      have hct : ∀ k : Z, ∃ r, (∀ s, s < r → 0 ≤ ct s k) ∧ 0 < ct r k := by
        intro k
        obtain ⟨r, hr, hpos⟩ := hc k.1
        cases r using Fin.cases with
        | zero => exact False.elim ((ne_of_gt hpos) k.2)
        | succ r =>
          refine ⟨r, ?_, ?_⟩
          intro s hs
          exact hr s.succ (Fin.succ_lt_succ_iff.mpr hs)
          exact hpos
      obtain ⟨wt, hwtpos, hwt⟩ := ih ct hct
      let tail : κ → ℝ := fun k => ∑ r, wt r * c r.succ k
      let A : Finset κ := Finset.univ.filter fun k => 0 < c 0 k
      let W : ℝ := 1 + ∑ k ∈ A, |tail k| / c 0 k
      have hsum_nonneg : 0 ≤ ∑ k ∈ A, |tail k| / c 0 k := by
        apply Finset.sum_nonneg
        intro k hk
        have hkpos : 0 < c 0 k := (Finset.mem_filter.mp hk).2
        positivity
      have hW : 0 < W := by
        dsimp [W]
        linarith
      have hratio (k : κ) (hkpos : 0 < c 0 k) :
          |tail k| / c 0 k ≤ ∑ j ∈ A, |tail j| / c 0 j := by
        apply Finset.single_le_sum (s := A) (f := fun j => |tail j| / c 0 j)
        · intro j hj
          have hjpos : 0 < c 0 j := (Finset.mem_filter.mp hj).2
          positivity
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, hkpos⟩
      let w : Fin (n + 1) → ℝ := Fin.cases W wt
      refine ⟨w, ?_, ?_⟩
      · intro r
        refine Fin.cases hW (fun r => ?_) r
        exact hwtpos r
      · intro k
        rw [Fin.sum_univ_succ]
        change 0 < W * c 0 k + tail k
        by_cases hk0 : c 0 k = 0
        · simpa [hk0, tail, ct] using hwt ⟨k, hk0⟩
        · have hkpos : 0 < c 0 k := lt_of_le_of_ne (hc0 k) (Ne.symm hk0)
          have hquot := hratio k hkpos
          have hbound : |tail k| ≤ (∑ j ∈ A, |tail j| / c 0 j) * c 0 k :=
            (div_le_iff₀ hkpos).mp hquot
          have habs : |tail k| < W * c 0 k := by
            dsimp [W]
            nlinarith
          nlinarith [neg_abs_le (tail k)]

@[blueprint "lem:weighted-separator-block-domination"
  (statement := /-- Let \(V\) be a finite type, let \(G\) be a directed graph on \(V\), and
  let \(t,h\in\mathbb N\).  If a separator block certificate for \(G\) of height \(h\) and
  block dimension \(3(t+1)\) is given, then there exists \(d\in\mathbb N\) such that
  \(d\le 3(t+1)(h+1)\) and \(G\) admits a reachability embedding of dimension \(d\). -/)
  (proof := /-- For every reachable ordered pair \((u,v)\), set
  \[
    c_r(u,v)=\langle L_r(u),R_r(v)\rangle,
  \]
  where \(L_r\) and \(R_r\) are the blocks in
  \cref{def:separator-block-certificate}.  The positive-level condition of that certificate
  says that these finitely many coefficient sequences satisfy the hypotheses of
  \cref{lem:finite-lexicographic-positive-weights}.  Hence there are positive weights
  \(w_0,\ldots,w_h\) such that
  \(\sum_r w_r c_r(u,v)>0\) for every reachable pair.

  Put \(d=(h+1)3(t+1)\), identify its coordinates with pairs consisting of a level and a
  block coordinate, and concatenate the left blocks without scaling and the right blocks
  after multiplying the block at level \(r\) by \(w_r\).  The inner product of the resulting
  vectors at \((u,v)\) is exactly \(\sum_r w_r c_r(u,v)\).  It is positive when \(v\) is
  reachable from \(u\) by the choice of the weights.  If \(v\) is not reachable from \(u\),
  every \(c_r(u,v)\) is nonpositive by
  \cref{def:separator-block-certificate}; positivity of the weights therefore makes the sum
  nonpositive.  Thus the concatenated maps satisfy
  \cref{def:reachability-embedding}, and hence
  \cref{def:admits-reachability-embedding}.  Finally,
  \(d=(h+1)3(t+1)=3(t+1)(h+1)\), which gives the required bound. -/)
  (title := /-- Domination of later separator blocks by positive earlier blocks -/)
  (latexEnv := "lemma")]
lemma weighted_separator_block_domination {V : Type*} [Fintype V]
    (G : Digraph V) (t h : ℕ)
    (certificate : separator_block_certificate G (3 * (t + 1)) h) :
    ∃ d : ℕ,
      d ≤ 3 * (t + 1) * (h + 1) ∧ admits_reachability_embedding G d := by
  classical
  let K := {p : V × V // directed_reachable G p.1 p.2}
  let c : Fin (h + 1) → K → ℝ := fun r p =>
    inner ℝ (certificate.leftBlock r p.1.1) (certificate.rightBlock r p.1.2)
  have hc : ∀ p : K, ∃ r, (∀ s, s < r → 0 ≤ c s p) ∧ 0 < c r p := by
    intro p
    simpa [c] using certificate.reachable_positive_level p.1.1 p.1.2 p.2
  obtain ⟨w, hwpos, hwreach⟩ := finite_lexicographic_positive_weights (h + 1) c hc
  let e : Fin (h + 1) × Fin (3 * (t + 1)) ≃
      Fin ((h + 1) * (3 * (t + 1))) := finProdFinEquiv
  let a : V → EuclideanSpace ℝ (Fin ((h + 1) * (3 * (t + 1)))) := fun u =>
    WithLp.toLp 2 fun i =>
      certificate.leftBlock (e.symm i).1 u (e.symm i).2
  let b : V → EuclideanSpace ℝ (Fin ((h + 1) * (3 * (t + 1)))) := fun v =>
    WithLp.toLp 2 fun i =>
      w (e.symm i).1 * certificate.rightBlock (e.symm i).1 v (e.symm i).2
  refine ⟨(h + 1) * (3 * (t + 1)), ?_, ?_⟩
  · simp [Nat.mul_comm]
  · refine ⟨a, b, ?_⟩
    intro u v
    have hinner : inner ℝ (a u) (b v) =
        ∑ r, w r * inner ℝ (certificate.leftBlock r u) (certificate.rightBlock r v) := by
      simp only [a, b, EuclideanSpace.inner_toLp_toLp, dotProduct, map_mul, star_trivial]
      rw [e.symm.sum_comp (fun p =>
        (w p.1 * certificate.rightBlock p.1 v p.2) *
          certificate.leftBlock p.1 u p.2), Fintype.sum_prod_type]
      simp only [PiLp.inner_apply, Real.inner_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hinner]
    constructor
    · intro hpos
      by_contra hnr
      have hnonpos :
          (∑ r, w r * inner ℝ (certificate.leftBlock r u)
            (certificate.rightBlock r v)) ≤ 0 := by
        apply Finset.sum_nonpos
        intro r hr
        exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hwpos r))
          (certificate.nonreachable_nonpositive r u v hnr)
      linarith
    · intro hreach
      simpa [c] using hwreach ⟨(u, v), hreach⟩

@[blueprint "lem:omitted-appendix-reachability-embedding-bound"
  (statement := /-- There exists an absolute constant $C\in\mathbb N$ with the following
  property.  For every finite vertex type $V$ with decidable equality, every directed graph
  $G$ on $V$, and all $n,t\in\mathbb N$, if $|V|=n$ and the underlying undirected graph of
  $G$ has treewidth at most $t$, then there is a dimension $d\in\mathbb N$ such that
  \[
    d\le C(t+1)\bigl(\lceil\log_2 n\rceil+1\bigr)
  \]
  and $G$ admits a reachability embedding of dimension $d$ in the sense of
  \cref{def:admits-reachability-embedding}. -/)
  (proof := /-- Set \(C=3\).  If \(n\le 1\), then
  \cref{lem:finite-digraph-card-reachability-embedding} gives a reachability embedding of
  dimension \(d=|V|=n\).  Both \(t+1\) and \(\lceil\log_2 n\rceil+1\) are positive, so
  \[
    n\le 1\le 3(t+1)(\lceil\log_2 n\rceil+1).
  \]

  In the remaining case, \cref{lem:balanced-separator-hierarchy} gives a natural number
  \(h\le\lceil\log_2 n\rceil\) and a separator block certificate of block dimension
  \(3(t+1)\).  Applying \cref{lem:weighted-separator-block-domination} to this certificate
  yields a dimension \(d\) for which \(G\) admits a reachability embedding and
  \[
    d\le 3(t+1)(h+1).
  \]
  Since \(h+1\le\lceil\log_2 n\rceil+1\), multiplication by \(3(t+1)\) preserves the
  inequality and gives the required bound.  Thus the same absolute constant works in both
  cases. -/)
  (title := /-- Reachability-embedding bound from recursive separators -/)
  (latexEnv := "lemma")]
lemma omitted_appendix_reachability_embedding_bound :
    ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : Digraph V) (n t : ℕ),
      Fintype.card V = n →
      has_treewidth_at_most G t →
      ∃ d : ℕ,
        d ≤ C * (t + 1) * (Nat.clog 2 n + 1) ∧ admits_reachability_embedding G d := by
  refine ⟨3, ?_⟩
  intro V _ _ G n t hn htw
  by_cases hsmall : n ≤ 1
  · refine ⟨Fintype.card V, ?_, finite_digraph_card_reachability_embedding G⟩
    rw [hn]
    have hpos : 0 < 3 * (t + 1) * (Nat.clog 2 n + 1) := by positivity
    omega
  · obtain ⟨h, hh, ⟨certificate⟩⟩ := balanced_separator_hierarchy V G n t hn htw
    obtain ⟨d, hd, hemb⟩ := weighted_separator_block_domination G t h certificate
    refine ⟨d, ?_, hemb⟩
    exact hd.trans (Nat.mul_le_mul_left (3 * (t + 1)) (Nat.add_le_add_right hh 1))

@[blueprint "thm:dig"
  (statement := /-- There exists an absolute constant $C\in\mathbb N$ such that, for every
  finite vertex type $V$ with decidable equality, every directed graph $G$ on $V$, and all
  $n,t\in\mathbb N$, if $|V|=n$ and the underlying undirected graph of $G$ has treewidth at
  most $t$, then there exists $d\in\mathbb N$ such that $G$ admits a reachability embedding
  of dimension $d$ and
  \[
    d\le C(t+1)\bigl(\lceil\log_2 n\rceil+1\bigr).
  \] -/)
  (proof := /-- Apply \cref{lem:omitted-appendix-reachability-embedding-bound}.  The constant
  furnished there is independent of the finite vertex type, the graph, $n$, and $t$, and its
  conclusion gives both the stated dimension estimate and the required reachability
  embedding. -/)
  (title := /-- Compact geometric representations of directed graphs of bounded treewidth -/)
  (latexEnv := "theorem")]
theorem dig :
    ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : Digraph V) (n t : ℕ),
      Fintype.card V = n →
      has_treewidth_at_most G t →
      ∃ d : ℕ,
        d ≤ C * (t + 1) * (Nat.clog 2 n + 1) ∧ admits_reachability_embedding G d := by
  exact omitted_appendix_reachability_embedding_bound

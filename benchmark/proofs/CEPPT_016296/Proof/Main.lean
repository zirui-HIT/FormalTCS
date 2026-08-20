import Architect
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:edge-weighted-tree"
  (statement := /-- An \emph{edge-weighted tree} on a vertex type $V$ is a triple
    $(G, h, w)$ consisting of a simple graph $G$ on $V$, a proof $h$ that $G$ is a
    tree (connected and acyclic, with $V$ nonempty), and an edge-weight function
    $w : \mathrm{Sym}^2(V) \to \mathbb{R}$ assigning a real weight to each unordered
    pair of vertices. -/)
  (title := /-- Edge-weighted tree -/)
  (latexEnv := "definition")]
structure edge_weighted_tree (V : Type*) where
  graph : SimpleGraph V
  isTree : graph.IsTree
  weight : Sym2 V → ℝ

@[blueprint "def:tree-dist"
  (statement := /-- Let $T = (G, h, w)$ be an \cref{def:edge-weighted-tree} on a
    vertex type $V$, and let $x, y \in V$. Since $G$ is a tree, there is a unique
    simple path $p$ from $x$ to $y$ in $G$. The \emph{tree distance} $d_T(x, y)$ is
    the total edge weight $\sum_{e \in E(p)} w(e)$ of the edges of that path. -/)
  (title := /-- Tree distance -/)
  (latexEnv := "definition")]
noncomputable def tree_dist {V : Type*} (T : edge_weighted_tree V) (x y : V) : ℝ :=
  (((T.isTree.existsUnique_path x y).exists.choose).edges.map T.weight).sum

@[blueprint "def:plane-tree"
  (statement := /-- A \emph{plane tree} is a triple $(V, T, \iota)$ consisting of a
    vertex type $V$, an \cref{def:edge-weighted-tree} $T$ on $V$ (whose internal
    vertices may be Steiner points that do not belong to the input), and a placement
    map $\iota : \mathbb{R}^2 \to V$ recording, for each point of the Euclidean plane
    $\mathbb{R}^2$, the vertex of $T$ that represents it. -/)
  (title := /-- Plane tree with Steiner points -/)
  (latexEnv := "definition")]
structure plane_tree where
  vertex : Type
  tree : edge_weighted_tree vertex
  place : EuclideanSpace ℝ (Fin 2) → vertex

@[blueprint "def:two-tree-cover"
  (statement := /-- Let $P \subseteq \mathbb{R}^2$ be a set of points in the
    Euclidean plane, and let $T_1, T_2$ be two \cref{def:plane-tree}s with placement
    maps $\iota_1, \iota_2$. We say that $\{T_1, T_2\}$ is a \emph{two-tree Steiner
    cover of $P$ with stretch $\sqrt{26}$} if for every pair of points $x, y \in P$
    there exists an index $i \in \{1, 2\}$ such that the \cref{def:tree-dist}
    $d_{T_i}(\iota_i(x), \iota_i(y))$ satisfies
    $\|x - y\| \le d_{T_i}(\iota_i(x), \iota_i(y)) \le \sqrt{26}\,\|x - y\|$, where
    $\|\cdot\|$ denotes the Euclidean distance. -/)
  (title := /-- Two-tree Steiner cover with stretch $\sqrt{26}$ -/)
  (latexEnv := "definition")]
def two_tree_cover (P : Set (EuclideanSpace ℝ (Fin 2)))
    (T₁ T₂ : plane_tree) : Prop :=
  ∀ x ∈ P, ∀ y ∈ P,
    (dist x y ≤ tree_dist T₁.tree (T₁.place x) (T₁.place y) ∧
        tree_dist T₁.tree (T₁.place x) (T₁.place y) ≤ Real.sqrt 26 * dist x y) ∨
      (dist x y ≤ tree_dist T₂.tree (T₂.place x) (T₂.place y) ∧
        tree_dist T₂.tree (T₂.place x) (T₂.place y) ≤ Real.sqrt 26 * dist x y)

@[blueprint "lem:tree-dist-eq-of-is-path"
  (statement := /-- Let $T = (G, h, w)$ be an \cref{def:edge-weighted-tree} on a vertex
    type $V$, and let $x, y \in V$. If $p$ is a walk from $x$ to $y$ in $G$ that is a
    simple path, then the \cref{def:tree-dist} $d_T(x, y)$ equals the total edge weight
    $\sum_{e \in E(p)} w(e)$ of $p$. -/)
  (proof := /-- Since $G$ is a tree, the walk chosen to define $d_T(x, y)$ is the unique
    simple path from $x$ to $y$. As the given walk $p$ is also a simple path from $x$ to
    $y$, uniqueness forces it to coincide with the chosen path, so their edge lists are
    equal and hence their weighted sums agree. -/)
  (title := /-- Tree distance along any simple path -/)
  (latexEnv := "lemma")]
lemma tree_dist_eq_of_is_path {V : Type*} (T : edge_weighted_tree V) {x y : V}
    (p : T.graph.Walk x y) (hp : p.IsPath) :
    tree_dist T x y = (p.edges.map T.weight).sum := by
  have hu := T.isTree.existsUnique_path x y
  have hchoose : ((T.isTree.existsUnique_path x y).exists.choose).IsPath :=
    (T.isTree.existsUnique_path x y).exists.choose_spec
  have h : (T.isTree.existsUnique_path x y).exists.choose = p := hu.unique hchoose hp
  unfold tree_dist
  rw [h]

@[blueprint "lem:reach-const"
  (statement := /-- Let $G$ be a simple graph on a vertex type $V$ and let
    $f : V \to W$ be a function that is constant on adjacent vertices, i.e.
    $f(a) = f(b)$ whenever $a$ and $b$ are adjacent in $G$. Then $f$ is constant on
    each connected set: if $u$ and $v$ are joined by a walk in $G$, then
    $f(u) = f(v)$. -/)
  (proof := /-- Reachability of $v$ from $u$ is the reflexive transitive closure of
    the adjacency relation. We argue by induction on this closure. In the reflexive
    base case $u = v$, the equality $f(u) = f(v)$ is immediate. In the transitive
    step, a reachability $u \rightsquigarrow b$ is extended by an edge $b \sim c$;
    the inductive hypothesis gives $f(u) = f(b)$ and the hypothesis on $f$ applied to
    the edge $b \sim c$ gives $f(b) = f(c)$, so $f(u) = f(c)$. -/)
  (title := /-- Functions constant on edges are constant on components -/)
  (latexEnv := "lemma")]
lemma reach_const {V W : Type*} {G : SimpleGraph V} (f : V → W)
    (hf : ∀ a b : V, G.Adj a b → f a = f b) {u v : V} (h : G.Reachable u v) :
    f u = f v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | tail _ hadj ih => exact ih.trans (hf _ _ hadj)

@[blueprint "lem:path-graph-is-tree"
  (statement := /-- For every natural number $n$, the \emph{path graph} on $n+1$
    vertices, whose vertices are $\{0, 1, \dots, n\}$ and whose edges join
    consecutive integers, is a tree: it is connected and acyclic. -/)
  (proof := /-- The path graph on $n+1$ vertices is connected. For acyclicity we
    show, using the bridge characterisation of acyclic graphs, that every edge is a
    bridge. Let $\{v, w\}$ be an edge, so the values of $v$ and $w$ are two
    consecutive integers; write $m$ for the smaller of the two. Consider the function
    sending a vertex $k$ to the truth value of $k \le m$. Any edge of the graph with
    this one edge removed joins two integers $i, i+1$ with $i \ne m$, hence its two
    endpoints lie on the same side of the threshold $m$, so this function is constant
    on edges of the reduced graph. By \cref{lem:reach-const} it is then
    constant along any walk in the reduced graph. But $v$ and $w$ lie on opposite
    sides of $m$, so there is no walk between them once $\{v, w\}$ is removed; that is,
    $\{v, w\}$ is a bridge. -/)
  (title := /-- The path graph is a tree -/)
  (latexEnv := "lemma")]
lemma path_graph_is_tree (n : ℕ) : (SimpleGraph.pathGraph (n + 1)).IsTree := by
  refine ⟨SimpleGraph.pathGraph_connected n, ?_⟩
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro v w hvw
  rw [SimpleGraph.isBridge_iff]
  intro hreach
  set m := min v.val w.val with hm
  have hf : ∀ a b : Fin (n + 1),
      ((SimpleGraph.pathGraph (n + 1)).deleteEdges {s(v, w)}).Adj a b →
      decide (a.val ≤ m) = decide (b.val ≤ m) := by
    intro a b hab
    rw [SimpleGraph.deleteEdges_adj] at hab
    obtain ⟨hadj, hne⟩ := hab
    rw [SimpleGraph.pathGraph_adj] at hadj
    have hvw' := hvw
    rw [SimpleGraph.pathGraph_adj] at hvw'
    simp only [decide_eq_decide]
    have hne' : ¬ ((a = v ∧ b = w) ∨ (a = w ∧ b = v)) := by
      intro hcontra
      apply hne
      rw [Set.mem_singleton_iff]
      rcases hcontra with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap
    simp only [Fin.ext_iff] at hne'
    push Not at hne'
    omega
  have hconst := reach_const (fun k : Fin (n + 1) => decide (k.val ≤ m)) hf hreach
  simp only [decide_eq_decide] at hconst
  have hvw' := hvw
  rw [SimpleGraph.pathGraph_adj] at hvw'
  omega

@[blueprint "def:line-weight"
  (statement := /-- Given a vertex type $\mathrm{Fin}\,N$ and a real-valued coordinate
    function $g : \mathrm{Fin}\,N \to \mathbb{R}$, the \emph{line weight} assigns to the
    unordered pair $\{i, j\}$ the value $2\,|g(i) - g(j)|$. This is a well-defined
    function on unordered pairs because $|g(i) - g(j)| = |g(j) - g(i)|$. -/)
  (title := /-- Line weight of a coordinate function -/)
  (latexEnv := "definition")]
noncomputable def line_weight {N : ℕ} (g : Fin N → ℝ) : Sym2 (Fin N) → ℝ :=
  Sym2.lift ⟨fun i j => 2 * |g i - g j|, fun i j => by dsimp only; rw [abs_sub_comm (g i) (g j)]⟩

@[blueprint "lem:line-walk"
  (statement := /-- Let $N$ be a natural number and $g : \mathrm{Fin}\,N \to \mathbb{R}$ a
    monotone function. For any two vertices $a, b$ of the \cref{lem:path-graph-is-tree}
    with $a + d = b$ (so $a \le b$), there is a walk $W$ from $a$ to $b$ in the path
    graph which is a simple path, every vertex of which has index between $a$ and $b$,
    and whose total \cref{def:line-weight} is $\sum_{e \in E(W)} 2\,|g(\cdot)-g(\cdot)|
    = 2\,(g(b) - g(a))$. -/)
  (proof := /-- We argue by induction on $d$. If $d = 0$ then $a = b$; the empty walk
    is a path, its only vertex is $a$, and its edge weight sum is $0 = 2(g(b) - g(a))$.
    For the step $d + 1$, set $a' = a + 1$, which satisfies $a' + d = b$ and is adjacent
    to $a$ in the path graph. By the induction hypothesis there is a path $W'$ from $a'$
    to $b$ with all vertex indices in $[a', b]$ and weight sum $2(g(b) - g(a'))$.
    Prepending the edge $\{a, a'\}$ yields a walk $W$ from $a$ to $b$; since every vertex
    of $W'$ has index at least $a' = a+1 > a$, the vertex $a$ is not in $W'$, so $W$ is a
    path with all vertex indices in $[a, b]$. Its weight sum is
    $2\,|g(a) - g(a')| + 2(g(b) - g(a'))$; as $g$ is monotone and $a \le a'$ we have
    $|g(a) - g(a')| = g(a') - g(a)$, giving $2(g(b) - g(a))$. -/)
  (title := /-- Monotone telescoping walk in the path graph -/)
  (latexEnv := "lemma")]
lemma line_walk {N : ℕ} (g : Fin N → ℝ) (hg : Monotone g) :
    ∀ (d : ℕ) (a b : Fin N), a.val + d = b.val →
      ∃ W : (SimpleGraph.pathGraph N).Walk a b, W.IsPath ∧
        (∀ v ∈ W.support, a.val ≤ v.val ∧ v.val ≤ b.val) ∧
        (W.edges.map (line_weight g)).sum = 2 * (g b - g a) := by
  intro d
  induction d with
  | zero =>
    intro a b hab
    have hab' : a = b := Fin.ext (by omega)
    subst hab'
    refine ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, ?_, ?_⟩
    · intro v hv
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
      subst hv
      omega
    · simp
  | succ d ih =>
    intro a b hab
    have hbN : b.val < N := b.isLt
    have ha1 : a.val + 1 < N := by omega
    set a' : Fin N := ⟨a.val + 1, ha1⟩ with ha'
    have hadj : (SimpleGraph.pathGraph N).Adj a a' := by
      rw [SimpleGraph.pathGraph_adj]
      left
      simp [ha']
    have hstep : a'.val + d = b.val := by simp [ha']; omega
    obtain ⟨W', hW'p, hW'supp, hW'sum⟩ := ih a' b hstep
    have hnotin : a ∉ W'.support := by
      intro hcon
      have := (hW'supp a hcon).1
      simp only [ha'] at this
      omega
    refine ⟨SimpleGraph.Walk.cons hadj W', ?_, ?_, ?_⟩
    · rw [SimpleGraph.Walk.cons_isPath_iff]
      exact ⟨hW'p, hnotin⟩
    · intro v hv
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact ⟨le_refl _, by omega⟩
      · have := hW'supp v hv
        simp only [ha'] at this
        exact ⟨by omega, this.2⟩
    · rw [SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons, hW'sum]
      have hle : g a ≤ g a' := hg (by rw [Fin.le_def, ha']; omega)
      have hw : line_weight g s(a, a') = 2 * |g a - g a'| := rfl
      rw [hw, abs_of_nonpos (by linarith)]
      ring

@[blueprint "lem:line-tree-dist"
  (statement := /-- Let $g : \mathrm{Fin}\,(m+1) \to \mathbb{R}$ be a monotone
    coordinate function, and consider the \cref{def:edge-weighted-tree} whose underlying
    graph is the \cref{lem:path-graph-is-tree} on $m+1$ vertices with edge weights given
    by the \cref{def:line-weight} of $g$. For any two vertices $a, b$, the
    \cref{def:tree-dist} equals $2\,|g(a) - g(b)|$. -/)
  (proof := /-- Assume first $a \le b$. By \cref{lem:line-walk} there is a simple path
    $W$ from $a$ to $b$ in the path graph whose total \cref{def:line-weight} is
    $2\,(g(b) - g(a))$. By \cref{lem:tree-dist-eq-of-is-path} the \cref{def:tree-dist}
    equals this weighted sum, and since $g$ is monotone we have $g(a) \le g(b)$, so
    $2\,(g(b) - g(a)) = 2\,|g(a) - g(b)|$. If instead $b \le a$, apply the same argument
    to the path from $b$ to $a$ and reverse it; reversing a path leaves it a path and
    does not change the sum of its edge weights, and now $g(b) \le g(a)$ gives
    $2\,(g(a) - g(b)) = 2\,|g(a) - g(b)|$. -/)
  (title := /-- Tree distance in a line tree -/)
  (latexEnv := "lemma")]
lemma line_tree_dist {m : ℕ} (g : Fin (m + 1) → ℝ) (hg : Monotone g) (a b : Fin (m + 1)) :
    tree_dist ⟨SimpleGraph.pathGraph (m + 1), path_graph_is_tree m, line_weight g⟩ a b
      = 2 * |g a - g b| := by
  set T : edge_weighted_tree (Fin (m + 1)) :=
    ⟨SimpleGraph.pathGraph (m + 1), path_graph_is_tree m, line_weight g⟩ with hT
  have hweight : T.weight = line_weight g := rfl
  rcases le_total a.val b.val with hab | hab
  · obtain ⟨W, hWp, _, hWsum⟩ := line_walk g hg (b.val - a.val) a b (by omega)
    have key := tree_dist_eq_of_is_path T
      (show T.graph.Walk a b from W) hWp
    have hedges : (show T.graph.Walk a b from W).edges = W.edges := rfl
    rw [key, hweight, hedges, hWsum]
    have hle : g a ≤ g b := hg (by rw [Fin.le_def]; omega)
    rw [abs_of_nonpos (by linarith)]
    ring
  · obtain ⟨W, hWp, _, hWsum⟩ := line_walk g hg (a.val - b.val) b a (by omega)
    have key := tree_dist_eq_of_is_path T
      (show T.graph.Walk a b from W.reverse) hWp.reverse
    have hedges : (show T.graph.Walk a b from W.reverse).edges
        = W.edges.reverse := SimpleGraph.Walk.edges_reverse W
    rw [key, hweight, hedges, List.map_reverse, List.sum_reverse, hWsum]
    have hle : g b ≤ g a := hg (by rw [Fin.le_def]; omega)
    rw [abs_of_nonneg (by linarith)]

@[blueprint "lem:line-plane-tree-exists"
  (statement := /-- Let $P \subseteq \mathbb{R}^2$ be a finite nonempty set and let
    $c : \mathbb{R}^2 \to \mathbb{R}$ be a coordinate function. Then there is a
    \cref{def:plane-tree} $T$ such that for every $x, y \in P$ the
    \cref{def:tree-dist} of the placements of $x$ and $y$ equals $2\,|c(x) - c(y)|$. -/)
  (proof := /-- Let $S = \{\,c(p) : p \in P\,\}$ be the finite set of coordinate values,
    which is nonempty. Writing $m + 1 = |S|$, the increasing enumeration of $S$ gives a
    monotone map $g : \mathrm{Fin}\,(m+1) \to \mathbb{R}$ with image $S$. As underlying
    \cref{def:edge-weighted-tree} take the \cref{lem:path-graph-is-tree} on $m+1$
    vertices with the \cref{def:line-weight} of $g$, and let the placement map send a
    point $p$ to the index of $c(p)$ in the enumeration when
    $c(p) \in S$ (and to $0$ otherwise). For $p \in P$ we have $c(p) \in S$, so
    $g(\iota(p)) = c(p)$. Hence by \cref{lem:line-tree-dist} the tree distance of the
    placements of $x, y \in P$ is $2\,|g(\iota(x)) - g(\iota(y))| = 2\,|c(x) - c(y)|$. -/)
  (title := /-- Line tree realizing a coordinate metric -/)
  (latexEnv := "lemma")]
lemma line_plane_tree_exists (P : Set (EuclideanSpace ℝ (Fin 2))) (hP : P.Finite)
    (hne : P.Nonempty) (coord : EuclideanSpace ℝ (Fin 2) → ℝ) :
    ∃ T : plane_tree, ∀ x ∈ P, ∀ y ∈ P,
      tree_dist T.tree (T.place x) (T.place y) = 2 * |coord x - coord y| := by
  classical
  set S : Finset ℝ := hP.toFinset.image coord with hS
  have hmem : ∀ p ∈ P, coord p ∈ S := by
    intro p hp
    exact Finset.mem_image.2 ⟨p, by rw [Set.Finite.mem_toFinset]; exact hp, rfl⟩
  have hScard : 0 < S.card := by
    rw [Finset.card_pos]
    obtain ⟨p, hp⟩ := hne
    exact ⟨coord p, hmem p hp⟩
  obtain ⟨m, hm⟩ : ∃ m, S.card = m + 1 := ⟨S.card - 1, by omega⟩
  set g : Fin (m + 1) → ℝ := fun i => S.orderEmbOfFin hm i with hg
  have hgmono : Monotone g := fun a b hab => (S.orderEmbOfFin hm).monotone hab
  set place : EuclideanSpace ℝ (Fin 2) → Fin (m + 1) :=
    fun p => if h : coord p ∈ S then (S.orderIsoOfFin hm).symm ⟨coord p, h⟩ else ⟨0, by omega⟩
    with hplace
  have hgplace : ∀ p ∈ P, g (place p) = coord p := by
    intro p hp
    have hcp := hmem p hp
    simp only [hplace, dif_pos hcp, hg]
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  refine ⟨⟨Fin (m + 1),
      ⟨SimpleGraph.pathGraph (m + 1), path_graph_is_tree m, line_weight g⟩, place⟩, ?_⟩
  intro x hx y hy
  simp only
  rw [line_tree_dist g hgmono (place x) (place y), hgplace x hx, hgplace y hy]

@[blueprint "lem:dominant-coord-bound"
  (statement := /-- Let $a, b \ge 0$ be reals with $b \le a$. Then the Euclidean length
    $\sqrt{a^2 + b^2}$ satisfies $\sqrt{a^2 + b^2} \le 2a$ and
    $2a \le \sqrt{26}\,\sqrt{a^2 + b^2}$. -/)
  (proof := /-- For the first inequality, since $0 \le 2a$ it suffices to check
    $a^2 + b^2 \le (2a)^2 = 4a^2$; as $b \le a$ gives $b^2 \le a^2$, we have
    $a^2 + b^2 \le 2a^2 \le 4a^2$. For the second inequality, note $2 \le \sqrt{26}$
    (since $2^2 = 4 \le 26$) and $a \le \sqrt{a^2 + b^2}$ (since $a^2 \le a^2 + b^2$).
    Multiplying these two nonnegative inequalities gives
    $2a \le \sqrt{26}\,\sqrt{a^2 + b^2}$. -/)
  (title := /-- Stretch bounds along the dominant coordinate -/)
  (latexEnv := "lemma")]
lemma dominant_coord_bound (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a) :
    Real.sqrt (a ^ 2 + b ^ 2) ≤ 2 * a ∧
      2 * a ≤ Real.sqrt 26 * Real.sqrt (a ^ 2 + b ^ 2) := by
  have hb2 : b ^ 2 ≤ a ^ 2 := by nlinarith
  refine ⟨?_, ?_⟩
  · rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith⟩
  · have h26 : (2 : ℝ) ≤ Real.sqrt 26 :=
      (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
    have hage : a ≤ Real.sqrt (a ^ 2 + b ^ 2) :=
      (Real.le_sqrt ha (by positivity)).2 (by nlinarith)
    have hsqrt_nonneg : (0 : ℝ) ≤ Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_nonneg _
    calc 2 * a ≤ Real.sqrt 26 * a := by nlinarith
      _ ≤ Real.sqrt 26 * Real.sqrt (a ^ 2 + b ^ 2) := by
          apply mul_le_mul_of_nonneg_left hage
          linarith

@[blueprint "thm:steiner"
  (statement := /-- Every finite set of points $P \subseteq \mathbb{R}^2$ in the
    Euclidean plane admits a Steiner tree cover consisting of two trees with stretch
    $\sqrt{26}$: there exist two \cref{def:plane-tree}s $T_1, T_2$ such that
    $\{T_1, T_2\}$ is a \cref{def:two-tree-cover} of $P$. -/)
  (proof := /-- If $P$ is empty the cover condition is vacuous; the two trees may be
    taken to be the trivial single-vertex \cref{lem:path-graph-is-tree}. So assume $P$
    is nonempty. We use two line-metric trees. Applying \cref{lem:line-plane-tree-exists}
    to the first coordinate function $p \mapsto p_0$ yields a \cref{def:plane-tree}
    $T_1$ whose \cref{def:tree-dist} between the placements of $x, y \in P$ equals
    $2\,|x_0 - y_0|$; applying it to the second coordinate $p \mapsto p_1$ yields a
    \cref{def:plane-tree} $T_2$ realizing $2\,|x_1 - y_1|$. Fix $x, y \in P$. By the
    Euclidean distance formula, $\|x - y\| = \sqrt{|x_0-y_0|^2 + |x_1-y_1|^2}$. Choose
    the dominant coordinate: if $|x_1 - y_1| \le |x_0 - y_0|$ select $T_1$, otherwise
    $T_2$. In either case the tree distance is $2a$ where $a$ is the larger of the two
    absolute coordinate differences and $b$ the smaller, and $\|x - y\| =
    \sqrt{a^2 + b^2}$. By \cref{lem:dominant-coord-bound} we then have
    $\|x - y\| \le 2a \le \sqrt{26}\,\|x - y\|$, which is exactly the required bound for
    the chosen tree. -/)
  (title := /-- Two-tree Steiner cover of the Euclidean plane -/)
  (latexEnv := "theorem")]
theorem steiner (P : Set (EuclideanSpace ℝ (Fin 2))) (hP : P.Finite) :
    ∃ T₁ T₂ : plane_tree, two_tree_cover P T₁ T₂ := by
  rcases P.eq_empty_or_nonempty with hP0 | hne
  · refine ⟨⟨Fin 1,
        ⟨SimpleGraph.pathGraph 1, path_graph_is_tree 0, line_weight (fun _ => 0)⟩,
        fun _ => 0⟩,
      ⟨Fin 1,
        ⟨SimpleGraph.pathGraph 1, path_graph_is_tree 0, line_weight (fun _ => 0)⟩,
        fun _ => 0⟩, ?_⟩
    intro x hx
    rw [hP0] at hx
    exact ((Set.mem_empty_iff_false x).mp hx).elim
  · obtain ⟨T₁, hT₁⟩ := line_plane_tree_exists P hP hne (fun p => p 0)
    obtain ⟨T₂, hT₂⟩ := line_plane_tree_exists P hP hne (fun p => p 1)
    refine ⟨T₁, T₂, ?_⟩
    intro x hx y hy
    have hd1 := hT₁ x hx y hy
    have hd2 := hT₂ x hx y hy
    have hdist : dist x y = Real.sqrt (|x 0 - y 0| ^ 2 + |x 1 - y 1| ^ 2) := by
      rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq]
    rcases le_total |x 1 - y 1| |x 0 - y 0| with hab | hab
    · left
      rw [hd1, hdist]
      exact dominant_coord_bound _ _ (abs_nonneg _) (abs_nonneg _) hab
    · right
      rw [hd2, hdist, add_comm (|x 0 - y 0| ^ 2) (|x 1 - y 1| ^ 2)]
      exact dominant_coord_bound _ _ (abs_nonneg _) (abs_nonneg _) hab

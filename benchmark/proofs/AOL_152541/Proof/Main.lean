import Architect
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:learner"
  (statement := /-- Let $X$ be a set of instances and $Y$ a set of labels. A *deterministic learner*
  is a map $A : (X \times Y)^* \times X \to 2^Y$: given the trace of the rounds played so far and
  the instance of the current round, it returns the set of labels predicted for that instance. -/)
  (title := /-- Deterministic learner -/)
  (latexEnv := "definition")]
abbrev learner (X Y : Type*) := List (X × Y) → X → Set Y

@[blueprint "def:compat-set"
  (statement := /-- Let $X$ be a set of instances, $Y$ a set of labels, $h : X \to 2^Y$ a
  multivalued hypothesis and $n \in \mathbb{N}$. The *compatibility set* $\mathcal{C}_h(n)$ is the
  set of traces $xy = ((x_0,y_0),\dots,(x_{n-1},y_{n-1})) \in (X \times Y)^*$ of length exactly $n$
  such that $y_k \in h(x_k)$ for every $k < n$. -/)
  (title := /-- Traces compatible with a hypothesis -/)
  (latexEnv := "definition")]
def compat_set {X Y : Type*} (h : X → Set Y) (n : ℕ) : Set (List (X × Y)) :=
  {xy | xy.length = n ∧ ∀ p ∈ xy, p.2 ∈ h p.1}

@[blueprint "def:compat-set-class"
  (statement := /-- Let $\mathcal{H} \subseteq \{X \to 2^Y\}$ be a hypothesis class and
  $n \in \mathbb{N}$. The set of *realizable traces* of length $n$ is
  $\mathcal{C}_{\mathcal{H}}(n) := \bigcup_{h \in \mathcal{H}} \mathcal{C}_h(n)$, with
  $\mathcal{C}_h(n)$ as in \cref{def:compat-set}. -/)
  (title := /-- Realizable traces of a hypothesis class -/)
  (latexEnv := "definition")]
def compat_set_class {X Y : Type*} (H : Set (X → Set Y)) (n : ℕ) : Set (List (X × Y)) :=
  {xy | ∃ h ∈ H, xy ∈ compat_set h n}

@[blueprint "def:mistake-set"
  (statement := /-- Let $A$ be a deterministic learner as in \cref{def:learner}, let
  $h : X \to 2^Y$ and let $xy \in (X \times Y)^*$ be a trace. The *mistake set*
  $\mathcal{M}^A_h(xy) \subseteq \mathbb{N}$ is the set of rounds $k < |xy|$ such that, writing
  $(x_k,y_k)$ for the round-$k$ entry of $xy$ and $\alpha_k := A(xy_{:k}, x_k)$ for the prediction
  of $A$ on the length-$k$ prefix $xy_{:k}$ of $xy$ and the instance $x_k$, at least one of the
  following two conditions holds: $y_k \notin \alpha_k$ (*overconfidence*), or
  $\alpha_k \setminus h(x_k) \neq \emptyset$, equivalently $\alpha_k \not\subseteq h(x_k)$
  (*underconfidence*). Mistakes are not revealed to the learner: the trace records only the
  instances and the labels. -/)
  (title := /-- Mistake set of a learner on a trace -/)
  (latexEnv := "definition")]
def mistake_set {X Y : Type*} (A : learner X Y) (h : X → Set Y)
    (xy : List (X × Y)) : Set ℕ :=
  {k | ∃ p : X × Y, xy[k]? = some p ∧
    (p.2 ∉ A (xy.take k) p.1 ∨ ¬ A (xy.take k) p.1 ⊆ h p.1)}

@[blueprint "def:mistake-bound-hyp"
  (statement := /-- Let $A$ be a deterministic learner, $h : X \to 2^Y$ and $N \in \mathbb{N}$.
  The *mistake bound of $A$ against $h$ over horizon $N$* is
  \[ \mathcal{M}^A_h(N) := \sup \{|\mathcal{M}^A_h(xy)| \mid xy \in \mathcal{C}_h(N)\}, \]
  where $\mathcal{M}^A_h(xy)$ is as in \cref{def:mistake-set}, $\mathcal{C}_h(N)$ is as in
  \cref{def:compat-set}, the cardinality is the natural cardinality of a set of rounds, and the
  supremum is taken in $\mathbb{N}$ with the convention $\sup \emptyset = 0$. -/)
  (title := /-- Mistake bound against a single hypothesis -/)
  (latexEnv := "definition")]
noncomputable def mistake_bound_hyp {X Y : Type*} (A : learner X Y) (h : X → Set Y) (N : ℕ) : ℕ :=
  sSup ((fun xy => (mistake_set A h xy).ncard) '' compat_set h N)

@[blueprint "def:mistake-bound-class"
  (statement := /-- Let $\mathcal{H} \subseteq \{X \to 2^Y\}$, let $A$ be a deterministic learner
  and let $N \in \mathbb{N}$. The *mistake bound of $A$ against $\mathcal{H}$ over horizon $N$* is
  \[ \mathcal{M}^A_{\mathcal{H}}(N) := \sup \{\mathcal{M}^A_h(N) \mid h \in \mathcal{H}\}, \]
  with $\mathcal{M}^A_h(N)$ as in \cref{def:mistake-bound-hyp} and $\sup \emptyset = 0$. -/)
  (title := /-- Mistake bound against a hypothesis class -/)
  (latexEnv := "definition")]
noncomputable def mistake_bound_class {X Y : Type*} (H : Set (X → Set Y)) (A : learner X Y)
    (N : ℕ) : ℕ :=
  sSup ((fun h => mistake_bound_hyp A h N) '' H)

@[blueprint "def:minimax-mistake-bound"
  (statement := /-- Let $\mathcal{H} \subseteq \{X \to 2^Y\}$ and $N \in \mathbb{N}$. The
  *minimax mistake bound* of $\mathcal{H}$ over horizon $N$ is
  \[ \mathcal{M}^*_{\mathcal{H}}(N) := \inf_A \mathcal{M}^A_{\mathcal{H}}(N), \]
  the infimum being taken in $\mathbb{N}$ over all deterministic learners
  $A$ of \cref{def:learner}, with $\mathcal{M}^A_{\mathcal{H}}(N)$ as in
  \cref{def:mistake-bound-class}. -/)
  (title := /-- Minimax mistake bound -/)
  (latexEnv := "definition")]
noncomputable def minimax_mistake_bound {X Y : Type*} (H : Set (X → Set Y)) (N : ℕ) : ℕ :=
  sInf (Set.range fun A : learner X Y => mistake_bound_class H A N)

@[blueprint "def:ambiguous-tree"
  (statement := /-- Let $\mathcal{H} \subseteq \{X \to 2^Y\}$. An *ambiguous shattered
  $\mathcal{H}$-tree* is a finite rooted tree whose vertices are encoded by their addresses: a
  vertex is the word $u \in Y^*$ of edge labels read along the path from the root, so that the root
  is the empty word $\varepsilon$, the parent of $u \cdot y$ is $u$, and the children of $u$ are
  the vertices of the form $u \cdot y$; in this encoding distinct children of a vertex
  automatically carry distinct labels. Formally, such a tree
  $T = (V, \mathbf{x}, \mathbf{h}, \mathrm{DE})$ consists of a vertex set $V \subseteq Y^*$, an
  instance labelling $\mathbf{x} : Y^* \to X$, a hypothesis labelling
  $\mathbf{h} : Y^* \to \{X \to 2^Y\}$ and a set $\mathrm{DE} \subseteq Y^*$ of *default*
  vertices, subject to the following conditions. Call $u \in V$ *internal* if $u \cdot y \in V$ for
  some $y \in Y$, and a *leaf* otherwise.

  (i) $V$ is finite, contains $\varepsilon$, and is closed under prefixes.

  (ii) Every internal $u \in V$ has exactly one default child: there is a unique $y \in Y$ with
  $u \cdot y \in V$ and $u \cdot y \in \mathrm{DE}$.

  (iii) For every leaf $u \in V$ one has $\mathbf{h}_u \in \mathcal{H}$, and $\mathbf{h}_u$ is
  compatible with the root path of $u$, that is $u_k \in \mathbf{h}_u(\mathbf{x}_{u_{:k}})$ for
  every $k < |u|$, where $u_{:k}$ is the length-$k$ prefix of $u$. -/)
  (title := /-- Ambiguous shattered tree -/)
  (latexEnv := "definition")]
structure ambiguous_tree {X Y : Type*} (H : Set (X → Set Y)) where
  verts : Set (List Y)
  inst : List Y → X
  hyp : List Y → (X → Set Y)
  defaults : Set (List Y)
  root_mem : ([] : List Y) ∈ verts
  prefix_closed : ∀ u ∈ verts, ∀ w : List Y, w <+: u → w ∈ verts
  verts_finite : verts.Finite
  default_child : ∀ u ∈ verts, (∃ y : Y, u ++ [y] ∈ verts) →
    ∃! y : Y, u ++ [y] ∈ verts ∧ u ++ [y] ∈ defaults
  leaf_hyp_mem : ∀ u ∈ verts, (¬ ∃ y : Y, u ++ [y] ∈ verts) → hyp u ∈ H
  leaf_hyp_compat : ∀ u ∈ verts, (¬ ∃ y : Y, u ++ [y] ∈ verts) →
    ∀ (k : ℕ) (y : Y), u[k]? = some y → y ∈ hyp u (inst (u.take k))

@[blueprint "def:tree-depth"
  (statement := /-- Let $T$ be an ambiguous shattered $\mathcal{H}$-tree as in
  \cref{def:ambiguous-tree}, with vertex set $V$. Its *depth* is
  $\mathrm{dep}(T) := \sup \{|u| \mid u \in V\}$, the supremum being taken in $\mathbb{N}$; it is
  finite because $V$ is finite, and $\mathrm{dep}(T) = 0$ precisely when $V = \{\varepsilon\}$. -/)
  (title := /-- Depth of an ambiguous shattered tree -/)
  (latexEnv := "definition")]
noncomputable def tree_depth {X Y : Type*} {H : Set (X → Set Y)} (T : ambiguous_tree H) : ℕ :=
  sSup ((fun u : List Y => u.length) '' T.verts)

@[blueprint "def:tree-leaves"
  (statement := /-- Let $T$ be an ambiguous shattered $\mathcal{H}$-tree as in
  \cref{def:ambiguous-tree}, with vertex set $V$. Its set of *leaves* is
  $\mathrm{Lf}(T) := \{u \in V \mid u \cdot y \notin V \text{ for every } y \in Y\}$. -/)
  (title := /-- Leaves of an ambiguous shattered tree -/)
  (latexEnv := "definition")]
def tree_leaves {X Y : Type*} {H : Set (X → Set Y)} (T : ambiguous_tree H) : Set (List Y) :=
  {u | u ∈ T.verts ∧ ¬ ∃ y : Y, u ++ [y] ∈ T.verts}

@[blueprint "def:relevant-edges"
  (statement := /-- Let $T = (V,\mathbf{x},\mathbf{h},\mathrm{DE})$ be an ambiguous shattered
  $\mathcal{H}$-tree as in \cref{def:ambiguous-tree} and let $u \in Y^*$. The *relevant-edge set*
  $R_T(u) \subseteq \mathbb{N}$ consists of those indices $k < |u|$ for which the $k$-th edge of
  the root path of $u$, namely the edge from $u_{:k}$ to $u_{:(k+1)}$, satisfies at least one of
  the following two conditions: $u_{:(k+1)} \notin \mathrm{DE}$, that is the edge is not the
  default edge at $u_{:k}$; or there exists $z \in Y$ with $u_{:k} \cdot z \in V$ and
  $z \notin \mathbf{h}_u(\mathbf{x}_{u_{:k}})$, that is some child of $u_{:k}$ carries a label that
  the hypothesis labelling $u$ does not allow at the instance $\mathbf{x}_{u_{:k}}$. -/)
  (title := /-- Relevant edges on a root path -/)
  (latexEnv := "definition")]
def relevant_edges {X Y : Type*} {H : Set (X → Set Y)} (T : ambiguous_tree H)
    (u : List Y) : Set ℕ :=
  {k | k < u.length ∧
    (u.take (k + 1) ∉ T.defaults ∨
      ∃ z : Y, u.take k ++ [z] ∈ T.verts ∧ z ∉ T.hyp u (T.inst (u.take k)))}

@[blueprint "def:tree-rank-weighted"
  (statement := /-- Let $T$ be an ambiguous shattered $\mathcal{H}$-tree as in
  \cref{def:ambiguous-tree} and let $w : \{X \to 2^Y\} \to \mathbb{N}$ be a weight function. The
  *$w$-weighted rank* of $T$ is
  \[ \mathrm{rank}_w(T) := \inf_{u \in \mathrm{Lf}(T)} \left(|R_T(u)| + w(\mathbf{h}_u)\right), \]
  with $\mathrm{Lf}(T)$ as in \cref{def:tree-leaves} and $R_T(u)$ as in
  \cref{def:relevant-edges}, the infimum being taken in $\mathbb{N}$ with the convention
  $\inf \emptyset = 0$. -/)
  (title := /-- Weighted rank of an ambiguous shattered tree -/)
  (latexEnv := "definition")]
noncomputable def tree_rank_weighted {X Y : Type*} {H : Set (X → Set Y)} (T : ambiguous_tree H)
    (w : (X → Set Y) → ℕ) : ℕ :=
  sInf ((fun u => (relevant_edges T u).ncard + w (T.hyp u)) '' tree_leaves T)

@[blueprint "def:tree-rank"
  (statement := /-- The *rank* of an ambiguous shattered $\mathcal{H}$-tree $T$ is its weighted
  rank for the zero weight, $\mathrm{rank}(T) := \mathrm{rank}_0(T) =
  \inf_{u \in \mathrm{Lf}(T)} |R_T(u)|$, with $\mathrm{rank}_w$ as in
  \cref{def:tree-rank-weighted}. -/)
  (title := /-- Rank of an ambiguous shattered tree -/)
  (latexEnv := "definition")]
noncomputable def tree_rank {X Y : Type*} {H : Set (X → Set Y)} (T : ambiguous_tree H) : ℕ :=
  tree_rank_weighted T (fun _ => 0)

@[blueprint "def:al-dim-weighted"
  (statement := /-- Let $\mathcal{H} \subseteq \{X \to 2^Y\}$, let
  $w : \{X \to 2^Y\} \to \mathbb{N}$ and let $n \in \mathbb{N}$. The *$w$-weighted ambiguous
  Littlestone dimension of $\mathcal{H}$ at depth $n$* is
  \[ \mathrm{AL}_w(\mathcal{H},n) := \sup \{\mathrm{rank}_w(T) \mid T \text{ an ambiguous
  shattered } \mathcal{H}\text{-tree with } \mathrm{dep}(T) \le n\}, \]
  with $\mathrm{rank}_w$ as in \cref{def:tree-rank-weighted} and $\mathrm{dep}$ as in
  \cref{def:tree-depth}; the supremum is taken in $\mathbb{N}$ with $\sup \emptyset = 0$. -/)
  (title := /-- Weighted ambiguous Littlestone dimension -/)
  (latexEnv := "definition")]
noncomputable def al_dim_weighted {X Y : Type*} (H : Set (X → Set Y)) (w : (X → Set Y) → ℕ)
    (n : ℕ) : ℕ :=
  sSup {r : ℕ | ∃ T : ambiguous_tree H, tree_depth T ≤ n ∧ tree_rank_weighted T w = r}

@[blueprint "def:al-dim"
  (statement := /-- Let $\mathcal{H} \subseteq \{X \to 2^Y\}$ and $n \in \mathbb{N}$. The
  *ambiguous Littlestone dimension of $\mathcal{H}$ at depth $n$* is
  $\mathrm{AL}(\mathcal{H},n) := \mathrm{AL}_0(\mathcal{H},n)$, the maximal rank of an ambiguous
  shattered $\mathcal{H}$-tree of depth at most $n$, with $\mathrm{AL}_w$ as in
  \cref{def:al-dim-weighted}. -/)
  (title := /-- Ambiguous Littlestone dimension at bounded depth -/)
  (latexEnv := "definition")]
noncomputable def al_dim {X Y : Type*} (H : Set (X → Set Y)) (n : ℕ) : ℕ :=
  al_dim_weighted H (fun _ => 0) n

@[blueprint "def:unfalsified"
  (statement := /-- Let $\mathcal{H} \subseteq \{X \to 2^Y\}$ and let $xy \in (X \times Y)^*$ be a
  trace. The *unfalsified subclass* of $\mathcal{H}$ after $xy$ is
  \[ \mathcal{H}^{xy}_{\mathrm{uf}} := \{h \in \mathcal{H} \mid xy \in \mathcal{C}_h(|xy|)\}, \]
  the set of hypotheses of $\mathcal{H}$ compatible with every round of $xy$, with
  $\mathcal{C}_h$ as in \cref{def:compat-set}. -/)
  (title := /-- Unfalsified subclass after a trace -/)
  (latexEnv := "definition")]
def unfalsified {X Y : Type*} (H : Set (X → Set Y)) (xy : List (X × Y)) : Set (X → Set Y) :=
  {h ∈ H | xy ∈ compat_set h xy.length}

@[blueprint "def:aoa-weight"
  (statement := /-- Let $A$ be a deterministic learner and let $xy \in (X \times Y)^*$. The
  *mistake weight after $xy$* is the function $w^{xy}_A$ assigning to a hypothesis
  $h : X \to 2^Y$ the number $w^{xy}_A(h) := |\mathcal{M}^A_h(xy)|$ of mistakes that $A$ has
  already made on the trace $xy$ if the true hypothesis is $h$, with $\mathcal{M}^A_h(xy)$ as in
  \cref{def:mistake-set}. -/)
  (title := /-- Mistake weight after a trace -/)
  (latexEnv := "definition")]
noncomputable def aoa_weight {X Y : Type*} (A : learner X Y) (xy : List (X × Y))
    (h : X → Set Y) : ℕ := (mistake_set A h xy).ncard

@[blueprint "def:aoa-invariant"
  (statement := /-- Let $\mathcal{H} \subseteq \{X \to 2^Y\}$, let $N \in \mathbb{N}$ and let $A$
  be a deterministic learner. Say that $A$ *satisfies the ambiguous-optimal-algorithm invariant
  for horizon $N$* if for every $k < N$, every $\overline{xy} \in \mathcal{C}_{\mathcal{H}}(k)$,
  every $x^* \in X$ and every $y^* \in Y$ with
  $\overline{xy}x^*y^* \in \mathcal{C}_{\mathcal{H}}(k+1)$ one has
  \[ \mathrm{AL}_{w^{\overline{xy}x^*y^*}_A}\left(\mathcal{H}^{\overline{xy}x^*y^*}_{\mathrm{uf}},
  N-(k+1)\right) \le \mathrm{AL}_{w^{\overline{xy}}_A}\left(\mathcal{H}^{\overline{xy}}_{\mathrm{uf}},
  N-k\right), \]
  where $\overline{xy}x^*y^*$ denotes the trace $\overline{xy}$ extended by the round
  $(x^*,y^*)$, the subtraction is truncated subtraction in $\mathbb{N}$,
  $\mathcal{C}_{\mathcal{H}}$ is as in \cref{def:compat-set-class},
  $\mathcal{H}^{\cdot}_{\mathrm{uf}}$ as in \cref{def:unfalsified}, $w^{\cdot}_A$ as in
  \cref{def:aoa-weight} and $\mathrm{AL}_w$ as in \cref{def:al-dim-weighted}. -/)
  (title := /-- Ambiguous-optimal-algorithm invariant -/)
  (latexEnv := "definition")]
def aoa_invariant {X Y : Type*} (H : Set (X → Set Y)) (N : ℕ) (A : learner X Y) : Prop :=
  ∀ k < N, ∀ xy ∈ compat_set_class H k, ∀ (x : X) (y : Y),
    (xy ++ [(x, y)]) ∈ compat_set_class H (k + 1) →
      al_dim_weighted (unfalsified H (xy ++ [(x, y)]))
          (aoa_weight A (xy ++ [(x, y)])) (N - (k + 1)) ≤
        al_dim_weighted (unfalsified H xy) (aoa_weight A xy) (N - k)

@[blueprint "lem:tree-forces-mistakes"
  (statement := /-- Let $\mathcal{H} \subseteq \{X \to 2^Y\}$, let $T$ be an ambiguous shattered
  $\mathcal{H}$-tree as in \cref{def:ambiguous-tree} and let $A$ be a deterministic learner as in
  \cref{def:learner}. Then there exist a leaf $u \in \mathrm{Lf}(T)$ and a trace
  $xy \in \mathcal{C}_{\mathbf{h}_u}(|u|)$ of length $|u|$ compatible with the leaf hypothesis
  $\mathbf{h}_u$ such that
  \[ R_T(u) \subseteq \mathcal{M}^A_{\mathbf{h}_u}(xy), \]
  with $\mathrm{Lf}(T)$ as in \cref{def:tree-leaves}, $\mathcal{C}_h$ as in
  \cref{def:compat-set}, $R_T$ as in \cref{def:relevant-edges} and $\mathcal{M}^A_h$ as in
  \cref{def:mistake-set}. -/)
  (proof := /-- Write $T = (V,\mathbf{x},\mathbf{h},\mathrm{DE})$. To each vertex word $v \in Y^*$
  associate its *canonical trace* $\overline{v} \in (X \times Y)^*$ of length $|v|$ whose round-$k$
  entry is $(\mathbf{x}_{v_{:k}}, v_k)$ for $k < |v|$, where $v_{:k}$ is the length-$k$ prefix of
  $v$. This assignment is prefix-stable: for every $k$ the length-$k$ prefix of $\overline{v}$
  equals the canonical trace $\overline{v_{:k}}$ of the length-$k$ prefix of $v$, because both are
  the length-$k$ list whose round-$j$ entry is $(\mathbf{x}_{v_{:j}}, v_j)$.

  Call a word $v$ *good* if $v \in V$ and, for every $k < |v|$, writing
  $\alpha_k := A(\overline{v_{:k}}, \mathbf{x}_{v_{:k}})$ for the prediction of $A$ on the
  canonical trace of $v_{:k}$ and the instance $\mathbf{x}_{v_{:k}}$, at least one of the following
  holds: $v_k \notin \alpha_k$ (the round-$k$ label is unpredicted), or both $v_{:(k+1)} \in
  \mathrm{DE}$ and every child label $z$ of $v_{:k}$, i.e. every $z \in Y$ with $v_{:k} \cdot z \in
  V$, satisfies $z \in \alpha_k$. The empty word $\varepsilon$ is good: it lies in $V$ by condition
  (i) of \cref{def:ambiguous-tree} and the round condition is vacuous. The set of good words is a
  subset of $V$, hence finite by condition (i); choose a good word $u$ of maximal length among all
  good words.

  We claim $u$ is a leaf. Suppose not; then $u$ is internal, so it has a child $u \cdot y_0 \in V$.
  Distinguish two cases. If some child $u \cdot a \in V$ has $a \notin A(\overline{u},
  \mathbf{x}_u)$, then $u \cdot a$ is good: its round conditions for $k < |u|$ coincide with those
  of $u$ because $\overline{(u \cdot a)_{:k}} = \overline{u_{:k}}$, $(u \cdot a)_{:(k+1)} =
  u_{:(k+1)}$ and $(u \cdot a)_k = u_k$ for $k < |u|$, and the new round $k = |u|$ satisfies the
  first disjunct since $(u \cdot a)_{|u|} = a \notin A(\overline{u}, \mathbf{x}_u)$. Otherwise every
  child label $a$ of $u$ satisfies $a \in A(\overline{u}, \mathbf{x}_u)$; let $b$ be the unique
  $y \in Y$ with $u \cdot y \in V$ and $u \cdot y \in \mathrm{DE}$, which exists by condition (ii)
  of \cref{def:ambiguous-tree} because $u$ is internal. Then $u \cdot b$ is good: the round
  conditions for $k < |u|$ again coincide with those of $u$, and the new round $k = |u|$ satisfies
  the second disjunct, since $(u \cdot b)_{:(|u|+1)} = u \cdot b \in \mathrm{DE}$ and every child
  label $z$ of $u$ lies in $A(\overline{u}, \mathbf{x}_u)$. In either case we produced a good word
  of length $|u| + 1 > |u|$, contradicting the maximality of $u$. Hence $u \in \mathrm{Lf}(T)$ in
  the sense of \cref{def:tree-leaves}.

  Put $h := \mathbf{h}_u$ and take the trace $\overline{u}$, of length $|u|$. For every $k < |u|$
  the round-$k$ entry of $\overline{u}$ is $(\mathbf{x}_{u_{:k}}, u_k)$, and by condition (iii) of
  \cref{def:ambiguous-tree} applied to the leaf $u$ we have $u_k \in h(\mathbf{x}_{u_{:k}})$; thus
  every round label of $\overline{u}$ is compatible with $h$, i.e. $\overline{u} \in
  \mathcal{C}_h(|u|)$ in the sense of \cref{def:compat-set}.

  Finally let $k \in R_T(u)$; we show $k \in \mathcal{M}^A_h(\overline{u})$. By
  \cref{def:relevant-edges} we have $k < |u|$ and either $u_{:(k+1)} \notin \mathrm{DE}$ or there is
  $z \in Y$ with $u_{:k} \cdot z \in V$ and $z \notin h(\mathbf{x}_{u_{:k}})$. Since $u$ is good,
  the round-$k$ alternative for $u$ holds. If it is the first disjunct, then $u_k \notin \alpha_k$
  with $\alpha_k = A(\overline{u_{:k}}, \mathbf{x}_{u_{:k}})$; as the round-$k$ entry of
  $\overline{u}$ is $(\mathbf{x}_{u_{:k}}, u_k)$ and its length-$k$ prefix is $\overline{u_{:k}}$,
  this is exactly the overconfidence condition of \cref{def:mistake-set}, so $k \in
  \mathcal{M}^A_h(\overline{u})$. Otherwise the second disjunct holds: $u_{:(k+1)} \in \mathrm{DE}$
  and every child label of $u_{:k}$ lies in $\alpha_k$. Then the case $u_{:(k+1)} \notin
  \mathrm{DE}$ of \cref{def:relevant-edges} is excluded, so there is $z \in Y$ with $u_{:k} \cdot z
  \in V$ and $z \notin h(\mathbf{x}_{u_{:k}})$; by goodness $z \in \alpha_k$, whence $z \in
  \alpha_k \setminus h(\mathbf{x}_{u_{:k}})$ and $\alpha_k \not\subseteq h(\mathbf{x}_{u_{:k}})$,
  the underconfidence condition of \cref{def:mistake-set}, so again $k \in
  \mathcal{M}^A_h(\overline{u})$. Therefore $R_T(u) \subseteq \mathcal{M}^A_h(\overline{u})$, as
  required. -/)
  (title := /-- An ambiguous shattered tree forces mistakes on its relevant edges -/)
  (latexEnv := "lemma")]
lemma tree_forces_mistakes {X Y : Type*} {H : Set (X → Set Y)} (T : ambiguous_tree H)
    (A : learner X Y) :
    ∃ u ∈ tree_leaves T, ∃ xy ∈ compat_set (T.hyp u) u.length,
      relevant_edges T u ⊆ mistake_set A (T.hyp u) xy := by
  classical
  let tr : List Y → List (X × Y) := fun v => v.mapIdx (fun i y => (T.inst (v.take i), y))
  have htr : ∀ v : List Y, tr v = v.mapIdx (fun i y => (T.inst (v.take i), y)) := fun _ => rfl
  have hlen : ∀ v : List Y, (tr v).length = v.length := by
    intro v; rw [htr]; simp
  have hget : ∀ (v : List Y) (k : ℕ) (hk : k < v.length),
      (tr v)[k]? = some (T.inst (v.take k), v[k]) := by
    intro v k hk
    rw [htr, List.getElem?_mapIdx, List.getElem?_eq_getElem hk]
    rfl
  have hcons : ∀ (v : List Y) (k : ℕ), (tr v).take k = tr (v.take k) := by
    intro v k
    simp only [htr]
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      have hik : i < k := by
        simp only [List.length_take, List.length_mapIdx, lt_min_iff] at h1
        exact h1.1
      simp only [List.getElem_take, List.getElem_mapIdx, List.take_take,
        Nat.min_eq_left hik.le]
  let good : List Y → Prop := fun p => p ∈ T.verts ∧
    ∀ (k : ℕ) (_ : k < p.length),
      p[k] ∉ A (tr (p.take k)) (T.inst (p.take k)) ∨
        (p.take (k + 1) ∈ T.defaults ∧
          ∀ z : Y, p.take k ++ [z] ∈ T.verts → z ∈ A (tr (p.take k)) (T.inst (p.take k)))
  have hroot : good [] := by
    refine ⟨T.root_mem, ?_⟩
    intro k hk
    simp at hk
  have hfin : {p : List Y | good p}.Finite :=
    T.verts_finite.subset (by intro p hp; exact hp.1)
  obtain ⟨u, hu⟩ := hfin.exists_maximalFor List.length _ ⟨[], hroot⟩
  have hu_good : good u := hu.1
  have hu_max : ∀ ⦃j : List Y⦄, good j → u.length ≤ j.length → j.length ≤ u.length := hu.2
  have hu_verts : u ∈ T.verts := hu_good.1
  have hleaf : ¬ ∃ y : Y, u ++ [y] ∈ T.verts := by
    rintro ⟨y0, hy0⟩
    by_cases hcase : ∃ a : Y, u ++ [a] ∈ T.verts ∧ a ∉ A (tr u) (T.inst u)
    · obtain ⟨a, ha_mem, ha_notin⟩ := hcase
      have hgood' : good (u ++ [a]) := by
        refine ⟨ha_mem, ?_⟩
        intro k hk
        rcases Nat.lt_or_ge k u.length with hlt | hge
        · have e1 : (u ++ [a]).take k = u.take k :=
            List.take_append_of_le_length (Nat.le_of_lt hlt)
          have e2 : (u ++ [a]).take (k + 1) = u.take (k + 1) :=
            List.take_append_of_le_length hlt
          have e3 : (u ++ [a])[k] = u[k] := List.getElem_append_left hlt
          simp only [e1, e2, e3]
          exact hu_good.2 k hlt
        · have hkeq : k = u.length := by
            have h := hk
            simp only [List.length_append, List.length_cons, List.length_nil] at h
            omega
          subst hkeq
          have eu : (u ++ [a]).take u.length = u := by
            rw [List.take_append_of_le_length (le_refl _), List.take_length]
          have ea : (u ++ [a])[u.length] = a := by simp
          simp only [eu, ea]
          exact Or.inl ha_notin
      have hle : u.length ≤ (u ++ [a]).length := by simp
      have hcontra := hu_max hgood' hle
      simp only [List.length_append, List.length_cons, List.length_nil] at hcontra
      omega
    · have hcase' : ∀ z : Y, u ++ [z] ∈ T.verts → z ∈ A (tr u) (T.inst u) := by
        intro z hz
        by_contra hcon
        exact hcase ⟨z, hz, hcon⟩
      obtain ⟨b, ⟨hb_verts, hb_def⟩, _⟩ := T.default_child u hu_verts ⟨y0, hy0⟩
      have hgood' : good (u ++ [b]) := by
        refine ⟨hb_verts, ?_⟩
        intro k hk
        rcases Nat.lt_or_ge k u.length with hlt | hge
        · have e1 : (u ++ [b]).take k = u.take k :=
            List.take_append_of_le_length (Nat.le_of_lt hlt)
          have e2 : (u ++ [b]).take (k + 1) = u.take (k + 1) :=
            List.take_append_of_le_length hlt
          have e3 : (u ++ [b])[k] = u[k] := List.getElem_append_left hlt
          simp only [e1, e2, e3]
          exact hu_good.2 k hlt
        · have hkeq : k = u.length := by
            have h := hk
            simp only [List.length_append, List.length_cons, List.length_nil] at h
            omega
          subst hkeq
          have eu : (u ++ [b]).take u.length = u := by
            rw [List.take_append_of_le_length (le_refl _), List.take_length]
          have es : (u ++ [b]).take (u.length + 1) = u ++ [b] := by
            rw [show u.length + 1 = (u ++ [b]).length by simp, List.take_length]
          simp only [eu, es]
          refine Or.inr ⟨hb_def, ?_⟩
          intro z hz
          exact hcase' z hz
      have hle : u.length ≤ (u ++ [b]).length := by simp
      have hcontra := hu_max hgood' hle
      simp only [List.length_append, List.length_cons, List.length_nil] at hcontra
      omega
  refine ⟨u, ⟨hu_verts, hleaf⟩, tr u, ⟨hlen u, ?_⟩, ?_⟩
  · intro p hp
    rw [List.mem_iff_getElem] at hp
    obtain ⟨i, hi, hpi⟩ := hp
    have hiu : i < u.length := by have h := hi; rwa [hlen u] at h
    have hval : (tr u)[i] = (T.inst (u.take i), u[i]) := by
      have h1 := hget u i hiu
      rw [List.getElem?_eq_getElem hi] at h1
      exact Option.some_inj.mp h1
    have hpeq : p = (T.inst (u.take i), u[i]) := hpi.symm.trans hval
    subst hpeq
    exact T.leaf_hyp_compat u hu_verts hleaf i (u[i]) (List.getElem?_eq_getElem hiu)
  · intro k hk
    simp only [relevant_edges, Set.mem_setOf_eq] at hk
    obtain ⟨hk_lt, hk_disj⟩ := hk
    have hstep := hu_good.2 k hk_lt
    rw [← hcons u k] at hstep
    simp only [mistake_set, Set.mem_setOf_eq]
    refine ⟨(T.inst (u.take k), u[k]), hget u k hk_lt, ?_⟩
    rcases hstep with hovc | ⟨hdef, hall⟩
    · exact Or.inl hovc
    · rcases hk_disj with hnd | ⟨z, hz_mem, hz_notin⟩
      · exact absurd hdef hnd
      · refine Or.inr ?_
        intro hsub
        exact hz_notin (hsub (hall z hz_mem))

@[blueprint "lem:rank-le-mistake-bound"
  (statement := /-- Let $\mathcal{H} \subseteq \{X \to 2^Y\}$, let $T$ be an ambiguous shattered
  $\mathcal{H}$-tree as in \cref{def:ambiguous-tree}, let $A$ be a deterministic learner and set
  $n := \mathrm{dep}(T)$. Then there exists $h \in \mathcal{H}$ and $m \le n$ with
  \[ \mathrm{rank}(T) \le \mathcal{M}^A_h(m), \]
  where $\mathrm{dep}$ is as in \cref{def:tree-depth}, $\mathrm{rank}$ as in
  \cref{def:tree-rank} and $\mathcal{M}^A_h(m)$ as in \cref{def:mistake-bound-hyp}. -/)
  (proof := /-- By \cref{lem:tree-forces-mistakes} there are a leaf $u \in \mathrm{Lf}(T)$ and a
  trace $xy \in \mathcal{C}_{\mathbf{h}_u}(|u|)$ with $R_T(u) \subseteq
  \mathcal{M}^A_{\mathbf{h}_u}(xy)$. Put $h := \mathbf{h}_u$ and $m := |u|$; then
  $h \in \mathcal{H}$ by condition (iii) of \cref{def:ambiguous-tree}, and $m \le
  \mathrm{dep}(T) = n$ because $u \in V$ and $\mathrm{dep}(T)$ is the supremum of the lengths of
  the vertices of $T$, a supremum over a finite and hence bounded set.

  The set $\mathcal{M}^A_h(xy)$ is contained in $\{0,1,\dots,m-1\}$ by \cref{def:mistake-set} and
  is therefore finite, so the inclusion $R_T(u) \subseteq \mathcal{M}^A_h(xy)$ gives
  $|R_T(u)| \le |\mathcal{M}^A_h(xy)|$. Since $u \in \mathrm{Lf}(T)$ and the weight is zero,
  $\mathrm{rank}(T) = \inf_{u' \in \mathrm{Lf}(T)} |R_T(u')| \le |R_T(u)|$ by
  \cref{def:tree-rank,def:tree-rank-weighted}. Finally $xy \in \mathcal{C}_h(m)$, so
  $|\mathcal{M}^A_h(xy)|$ belongs to the set whose supremum defines $\mathcal{M}^A_h(m)$ in
  \cref{def:mistake-bound-hyp}; that set is a set of natural numbers indexed by traces of length
  $m$ over the finite label set $Y$ and every one of its elements is at most $m$, hence it is
  bounded above and $|\mathcal{M}^A_h(xy)| \le \mathcal{M}^A_h(m)$. Chaining the three
  inequalities yields $\mathrm{rank}(T) \le \mathcal{M}^A_h(m)$. -/)
  (title := /-- The rank of a tree is a mistake lower bound at the tree's depth -/)
  (latexEnv := "lemma")]
lemma rank_le_mistake_bound {X Y : Type*} [Fintype Y] {H : Set (X → Set Y)}
    (T : ambiguous_tree H) (A : learner X Y) :
    ∃ h ∈ H, ∃ m ≤ tree_depth T, tree_rank T ≤ mistake_bound_hyp A h m := by
  classical
  obtain ⟨u, hu_leaf, xy, hxy_compat, hsub⟩ := tree_forces_mistakes T A
  have hu_verts : u ∈ T.verts := hu_leaf.1
  have hu_noext : ¬ ∃ y : Y, u ++ [y] ∈ T.verts := hu_leaf.2
  set h := T.hyp u with hh_def
  have hsub_iio : ∀ zw : List (X × Y), mistake_set A h zw ⊆ Set.Iio zw.length := by
    intro zw k hk
    obtain ⟨p, hp, -⟩ := hk
    rw [Set.mem_Iio]
    exact (List.getElem?_eq_some_iff.1 hp).1
  have hncard_le : ∀ zw : List (X × Y), (mistake_set A h zw).ncard ≤ zw.length := by
    intro zw
    calc (mistake_set A h zw).ncard
        ≤ (Set.Iio zw.length).ncard :=
          Set.ncard_le_ncard (hsub_iio zw) (Set.finite_Iio _)
      _ = zw.length := by
          rw [← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]
  refine ⟨h, T.leaf_hyp_mem u hu_verts hu_noext, u.length, ?_, ?_⟩
  · exact le_csSup (T.verts_finite.image _).bddAbove ⟨u, hu_verts, rfl⟩
  · calc tree_rank T
        ≤ (relevant_edges T u).ncard := by
          unfold tree_rank tree_rank_weighted
          exact Nat.sInf_le ⟨u, hu_leaf, by simp⟩
      _ ≤ (mistake_set A h xy).ncard :=
          Set.ncard_le_ncard hsub ((Set.finite_Iio _).subset (hsub_iio xy))
      _ ≤ mistake_bound_hyp A h u.length := by
          refine le_csSup ⟨u.length, ?_⟩ ⟨xy, hxy_compat, rfl⟩
          rintro b ⟨zw, hzw, rfl⟩
          rw [← hzw.1]
          exact hncard_le zw

@[blueprint "lem:mistake-set-subset-iio"
  (statement := /-- Let $A$ be a deterministic learner as in \cref{def:learner}, let
  $h : X \to 2^Y$ and let $xy \in (X \times Y)^*$ be a trace. Then the mistake set
  $\mathcal{M}^A_h(xy)$ of \cref{def:mistake-set} is contained in $\{0,1,\dots,|xy|-1\}$; that is,
  every mistake round is a valid index of $xy$. -/)
  (proof := /-- Let $k \in \mathcal{M}^A_h(xy)$. By \cref{def:mistake-set} there is a round
  $p$ with $xy_k = p$, i.e. the trace has an entry at index $k$. A list has an entry at index $k$
  only when $k < |xy|$, so $k \in \{0,1,\dots,|xy|-1\}$. -/)
  (title := /-- Mistake rounds are valid indices of the trace -/)
  (latexEnv := "lemma")]
lemma mistake_set_subset_iio {X Y : Type*} (A : learner X Y) (h : X → Set Y)
    (xy : List (X × Y)) : mistake_set A h xy ⊆ Set.Iio xy.length := by
  intro k hk
  obtain ⟨p, hp, -⟩ := hk
  rw [Set.mem_Iio]
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hp
  exact hlt

@[blueprint "lem:mistake-ncard-le-length"
  (statement := /-- Let $A$ be a deterministic learner, $h : X \to 2^Y$ and
  $xy \in (X \times Y)^*$ a trace. Then $|\mathcal{M}^A_h(xy)| \le |xy|$, where
  $\mathcal{M}^A_h(xy)$ is as in \cref{def:mistake-set}. -/)
  (proof := /-- By \cref{lem:mistake-set-subset-iio} the mistake set $\mathcal{M}^A_h(xy)$ is
  contained in $\{0,1,\dots,|xy|-1\}$, a finite set of cardinality $|xy|$. Monotonicity of the
  natural cardinality under inclusion into a finite set therefore gives
  $|\mathcal{M}^A_h(xy)| \le |xy|$. -/)
  (title := /-- The number of mistakes is bounded by the trace length -/)
  (latexEnv := "lemma")]
lemma mistake_ncard_le_length {X Y : Type*} (A : learner X Y) (h : X → Set Y)
    (xy : List (X × Y)) : (mistake_set A h xy).ncard ≤ xy.length := by
  calc (mistake_set A h xy).ncard
      ≤ (Set.Iio xy.length).ncard :=
        Set.ncard_le_ncard (mistake_set_subset_iio A h xy) (Set.finite_Iio _)
    _ = xy.length := by rw [← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]

@[blueprint "lem:mistake-set-mono-append"
  (statement := /-- Let $A$ be a deterministic learner, $h : X \to 2^Y$ and let
  $xy, l \in (X \times Y)^*$ be traces. Then $\mathcal{M}^A_h(xy) \subseteq
  \mathcal{M}^A_h(xy \mathbin{+\!\!+} l)$, with $\mathcal{M}^A_h$ as in \cref{def:mistake-set}. -/)
  (proof := /-- Let $k \in \mathcal{M}^A_h(xy)$. By \cref{lem:mistake-set-subset-iio} we have
  $k < |xy|$. Consequently the round-$k$ entry of $xy \mathbin{+\!\!+} l$ equals that of $xy$, and
  since $k \le |xy|$ the length-$k$ prefix of $xy \mathbin{+\!\!+} l$ equals the length-$k$ prefix
  of $xy$. Hence the overconfidence and underconfidence conditions of \cref{def:mistake-set} at
  round $k$ for $xy \mathbin{+\!\!+} l$ coincide with those for $xy$, so
  $k \in \mathcal{M}^A_h(xy \mathbin{+\!\!+} l)$. -/)
  (title := /-- Mistakes are preserved when the trace is extended on the right -/)
  (latexEnv := "lemma")]
lemma mistake_set_mono_append {X Y : Type*} (A : learner X Y) (h : X → Set Y)
    (xy l : List (X × Y)) : mistake_set A h xy ⊆ mistake_set A h (xy ++ l) := by
  intro k hk
  have hlt : k < xy.length := mistake_set_subset_iio A h xy hk
  obtain ⟨p, hp, hcond⟩ := hk
  refine ⟨p, ?_, ?_⟩
  · rw [List.getElem?_append_left hlt]; exact hp
  · rwa [List.take_append_of_le_length hlt.le]

@[blueprint "lem:compat-append-replicate"
  (statement := /-- Let $h : X \to 2^Y$, let $m \le N$ be natural numbers, let
  $xy \in \mathcal{C}_h(m)$ be a trace compatible with $h$ over horizon $m$, and let $x \in X$,
  $y \in Y$ with $y \in h(x)$. Then the trace obtained from $xy$ by appending $N - m$ copies of the
  round $(x,y)$ lies in $\mathcal{C}_h(N)$, with $\mathcal{C}_h$ as in \cref{def:compat-set}. -/)
  (proof := /-- By \cref{def:compat-set} we have $|xy| = m$ and every round of $xy$ has its label
  in $h$ of its instance. The appended list of $N - m$ copies of $(x,y)$ has length $N - m$, so the
  concatenation has length $m + (N - m) = N$ because $m \le N$. Each round of the concatenation is
  either a round of $xy$, whose label lies in $h$ of its instance by assumption, or an appended
  copy $(x,y)$, whose label $y$ lies in $h(x)$ by hypothesis. Hence the concatenation lies in
  $\mathcal{C}_h(N)$. -/)
  (title := /-- Padding a compatible trace with a fixed compatible round preserves compatibility -/)
  (latexEnv := "lemma")]
lemma compat_append_replicate {X Y : Type*} (h : X → Set Y) {m N : ℕ} (hmN : m ≤ N)
    {xy : List (X × Y)} (hxy : xy ∈ compat_set h m) {x : X} {y : Y} (hy : y ∈ h x) :
    xy ++ List.replicate (N - m) (x, y) ∈ compat_set h N := by
  obtain ⟨hlen, hcomp⟩ := hxy
  refine ⟨?_, ?_⟩
  · rw [List.length_append, List.length_replicate, hlen, Nat.add_sub_cancel' hmN]
  · intro p hp
    rcases List.mem_append.1 hp with hp' | hp'
    · exact hcomp p hp'
    · rw [List.eq_of_mem_replicate hp']; exact hy

@[blueprint "lem:mistake-bound-horizon-mono"
  (statement := /-- Let $\mathcal{H} \subseteq \{X \to 2^Y\}$ be such that for every
  $h \in \mathcal{H}$ there exists $x \in X$ with $h(x) \neq \emptyset$. Let $A$ be a deterministic
  learner, let $h \in \mathcal{H}$ and let $m \le N$ be natural numbers. Then
  \[ \mathcal{M}^A_h(m) \le \mathcal{M}^A_h(N), \]
  with $\mathcal{M}^A_h$ as in \cref{def:mistake-bound-hyp}. -/)
  (proof := /-- Fix a trace $xy \in \mathcal{C}_h(m)$; it suffices to exhibit a trace
  $xy' \in \mathcal{C}_h(N)$ with $|\mathcal{M}^A_h(xy)| \le |\mathcal{M}^A_h(xy')|$. Indeed, by
  \cref{def:mistake-bound-hyp} the quantity $\mathcal{M}^A_h(m)$ is the supremum of the set of
  values $|\mathcal{M}^A_h(xy)|$ for $xy \in \mathcal{C}_h(m)$, and every such value is bounded by
  $\mathcal{M}^A_h(N)$: for $xy \in \mathcal{C}_h(m)$ the value $|\mathcal{M}^A_h(xy)|$ is at most
  $|\mathcal{M}^A_h(xy')|$, which in turn belongs to the set defining $\mathcal{M}^A_h(N)$ and is
  therefore at most its supremum; this last step is licit because that set is bounded above, every
  one of its elements being at most $N$ by \cref{lem:mistake-ncard-le-length} applied to a trace of
  length $N$.

  It remains to construct $xy'$. By hypothesis there are $x \in X$ and $y \in Y$ with $y \in h(x)$.
  Let $xy'$ be the trace obtained from $xy$ by appending $N - m$ copies of the round $(x,y)$. Then
  $xy' \in \mathcal{C}_h(N)$ by \cref{lem:compat-append-replicate}, using $m \le N$. Moreover
  $\mathcal{M}^A_h(xy) \subseteq \mathcal{M}^A_h(xy')$ by \cref{lem:mistake-set-mono-append}, since
  $xy'$ extends $xy$ on the right. The set $\mathcal{M}^A_h(xy')$ is finite, being contained in
  $\{0,\dots,|xy'|-1\}$ by \cref{lem:mistake-set-subset-iio}, so monotonicity of the natural
  cardinality under this inclusion gives $|\mathcal{M}^A_h(xy)| \le |\mathcal{M}^A_h(xy')|$, as
  required. -/)
  (title := /-- Monotonicity of the mistake bound in the horizon -/)
  (latexEnv := "lemma")]
lemma mistake_bound_horizon_mono {X Y : Type*} {H : Set (X → Set Y)}
    (hne : ∀ h ∈ H, ∃ x : X, (h x).Nonempty) (A : learner X Y) {h : X → Set Y} (hh : h ∈ H)
    {m N : ℕ} (hmN : m ≤ N) :
    mistake_bound_hyp A h m ≤ mistake_bound_hyp A h N := by
  obtain ⟨x, y, hy⟩ := hne h hh
  apply csSup_le'
  rintro a ⟨xy, hxy, rfl⟩
  set xy' := xy ++ List.replicate (N - m) (x, y) with hxy'def
  have hxy'mem : xy' ∈ compat_set h N := compat_append_replicate h hmN hxy hy
  have hsub : mistake_set A h xy ⊆ mistake_set A h xy' :=
    mistake_set_mono_append A h xy (List.replicate (N - m) (x, y))
  have hfin : (mistake_set A h xy').Finite :=
    (Set.finite_Iio _).subset (mistake_set_subset_iio A h xy')
  have hle : (mistake_set A h xy).ncard ≤ (mistake_set A h xy').ncard :=
    Set.ncard_le_ncard hsub hfin
  refine hle.trans (le_csSup ?_ ?_)
  · refine ⟨N, ?_⟩
    rintro b ⟨zw, hzw, rfl⟩
    have : zw.length = N := hzw.1
    rw [← this]
    exact mistake_ncard_le_length A h zw
  · exact ⟨xy', hxy'mem, rfl⟩

@[blueprint "lem:rank-le-minimax"
  (statement := /-- Let $\mathcal{H} \subseteq \{X \to 2^Y\}$ with $Y$ finite, such
  that for every $h \in \mathcal{H}$ there exists $x \in X$ with $h(x) \neq \emptyset$. Let
  $N \in \mathbb{N}$ and let $T$ be an ambiguous shattered $\mathcal{H}$-tree with
  $\mathrm{dep}(T) \le N$. Then
  \[ \mathrm{rank}(T) \le \mathcal{M}^*_{\mathcal{H}}(N), \]
  with $\mathrm{dep}$ as in \cref{def:tree-depth}, $\mathrm{rank}$ as in \cref{def:tree-rank} and
  $\mathcal{M}^*_{\mathcal{H}}$ as in \cref{def:minimax-mistake-bound}. -/)
  (proof := /-- By \cref{def:minimax-mistake-bound} the quantity $\mathcal{M}^*_{\mathcal{H}}(N)$
  is the infimum over deterministic learners of $\mathcal{M}^A_{\mathcal{H}}(N)$, so by the
  characterisation of the infimum of a set of natural numbers as a greatest lower bound it suffices
  to prove $\mathrm{rank}(T) \le \mathcal{M}^A_{\mathcal{H}}(N)$ for every deterministic learner
  $A$.

  Fix such an $A$. By \cref{lem:rank-le-mistake-bound} there are $h \in \mathcal{H}$ and
  $m \le \mathrm{dep}(T)$ with $\mathrm{rank}(T) \le \mathcal{M}^A_h(m)$. Since
  $\mathrm{dep}(T) \le N$ we have $m \le N$, so \cref{lem:mistake-bound-horizon-mono} applied to
  $h$ and $m \le N$ gives $\mathcal{M}^A_h(m) \le \mathcal{M}^A_h(N)$. Finally $h \in \mathcal{H}$,
  so $\mathcal{M}^A_h(N)$ belongs to the set whose supremum defines
  $\mathcal{M}^A_{\mathcal{H}}(N)$ in \cref{def:mistake-bound-class}, and every element of that set
  is at most $N$ because, by \cref{lem:mistake-ncard-le-length}, a mistake set on a trace of
  length $N$ has cardinality at most $N$; the set is therefore bounded above and
  $\mathcal{M}^A_h(N) \le \mathcal{M}^A_{\mathcal{H}}(N)$. Chaining the three inequalities gives
  $\mathrm{rank}(T) \le \mathcal{M}^A_{\mathcal{H}}(N)$. -/)
  (title := /-- The rank of a bounded-depth tree bounds the minimax mistake bound from below -/)
  (latexEnv := "lemma")]
lemma rank_le_minimax {X Y : Type*} [Fintype Y] {H : Set (X → Set Y)}
    (hne : ∀ h ∈ H, ∃ x : X, (h x).Nonempty) {N : ℕ} (T : ambiguous_tree H)
    (hT : tree_depth T ≤ N) :
    tree_rank T ≤ minimax_mistake_bound H N := by
  classical
  apply le_csInf (Set.range_nonempty _)
  rintro b ⟨A, rfl⟩
  obtain ⟨h, hh, m, hm, hrank⟩ := rank_le_mistake_bound T A
  have hmN : m ≤ N := hm.trans hT
  have h1 : mistake_bound_hyp A h m ≤ mistake_bound_hyp A h N :=
    mistake_bound_horizon_mono hne A hh hmN
  have h2 : mistake_bound_hyp A h N ≤ mistake_bound_class H A N := by
    apply le_csSup
    · refine ⟨N, ?_⟩
      rintro c ⟨h', -, rfl⟩
      apply csSup_le'
      rintro a ⟨xy, hxy, rfl⟩
      rw [← hxy.1]
      exact mistake_ncard_le_length A h' xy
    · exact ⟨h, hh, rfl⟩
  exact hrank.trans (h1.trans h2)

@[blueprint "lem:al-le-minimax"
  (statement := /-- Let $\mathcal{H} \subseteq \{X \to 2^Y\}$ with $Y$ finite, such
  that for every $h \in \mathcal{H}$ there exists $x \in X$ with $h(x) \neq \emptyset$. Then for
  every $N \in \mathbb{N}$,
  \[ \mathrm{AL}(\mathcal{H},N) \le \mathcal{M}^*_{\mathcal{H}}(N), \]
  with $\mathrm{AL}$ as in \cref{def:al-dim} and $\mathcal{M}^*_{\mathcal{H}}$ as in
  \cref{def:minimax-mistake-bound}. -/)
  (proof := /-- By \cref{def:al-dim,def:al-dim-weighted}, $\mathrm{AL}(\mathcal{H},N)$ is the
  supremum of the set $S$ of natural numbers of the form $\mathrm{rank}(T)$ for $T$ an ambiguous
  shattered $\mathcal{H}$-tree with $\mathrm{dep}(T) \le N$. To bound a supremum of natural numbers
  by $\mathcal{M}^*_{\mathcal{H}}(N)$ it suffices to bound every element of $S$ by
  $\mathcal{M}^*_{\mathcal{H}}(N)$. So let $r \in S$, say $r = \mathrm{rank}(T)$ with
  $\mathrm{dep}(T) \le N$. Then $r \le \mathcal{M}^*_{\mathcal{H}}(N)$ by
  \cref{lem:rank-le-minimax}. Hence $\mathrm{AL}(\mathcal{H},N) = \sup S \le
  \mathcal{M}^*_{\mathcal{H}}(N)$. -/)
  (title := /-- Lower bound: the ambiguous Littlestone dimension bounds the minimax mistake bound -/)
  (latexEnv := "lemma")]
lemma al_le_minimax {X Y : Type*} [Fintype Y] {H : Set (X → Set Y)}
    (hne : ∀ h ∈ H, ∃ x : X, (h x).Nonempty) (N : ℕ) :
    al_dim H N ≤ minimax_mistake_bound H N := by
  apply csSup_le'
  rintro r ⟨T, hT, rfl⟩
  exact rank_le_minimax hne T hT

@[blueprint "def:mistake-inc"
  (statement := /-- Let $\alpha \subseteq Y$ be a prediction, $h : X \to 2^Y$ a hypothesis,
  $x \in X$ an instance and $y \in Y$ a label. The *one-round mistake increment*
  $\mathrm{inc}(\alpha, h, x, y)$ equals $1$ if predicting $\alpha$ at $x$ and observing $y$ is a
  mistake against $h$ in the sense of \cref{def:mistake-set}, that is if $y \notin \alpha$
  (overconfidence) or $\alpha \not\subseteq h(x)$ (underconfidence), and equals $0$ otherwise. -/)
  (title := /-- One-round mistake increment -/)
  (latexEnv := "definition")]
noncomputable def mistake_inc {X Y : Type*} (α : Set Y) (h : X → Set Y) (x : X) (y : Y) : ℕ :=
  haveI := Classical.propDecidable (y ∉ α ∨ ¬ α ⊆ h x)
  if (y ∉ α ∨ ¬ α ⊆ h x) then 1 else 0

@[blueprint "lem:aoa-weight-append"
  (statement := /-- Let $A$ be a deterministic learner as in \cref{def:learner}, let
  $h : X \to 2^Y$, let $xy \in (X \times Y)^*$ be a trace and let $x \in X$, $y \in Y$. Then the
  mistake weight of \cref{def:aoa-weight} after extending $xy$ by the round $(x,y)$ satisfies
  \[ w^{xy(x,y)}_A(h) = w^{xy}_A(h) + \mathrm{inc}(A(xy,x), h, x, y), \]
  with $w^{\cdot}_A$ as in \cref{def:aoa-weight} and $\mathrm{inc}$ as in \cref{def:mistake-inc}. -/)
  (proof := /-- By \cref{def:mistake-set} the mistake set $\mathcal{M}^A_h(xy(x,y))$ splits as the
  disjoint union of $\mathcal{M}^A_h(xy)$, consisting of the rounds $k < |xy|$ where the entry and
  prefix agree with those of $xy$, and the singleton $\{|xy|\}$ if the final round is a mistake and
  the empty set otherwise; the final round uses the prefix $xy$ and the entry $(x,y)$, so it is a
  mistake exactly when $y \notin A(xy,x)$ or $A(xy,x) \not\subseteq h(x)$. The two parts are
  disjoint because every element of $\mathcal{M}^A_h(xy)$ is a valid index of $xy$, hence smaller
  than $|xy|$ by \cref{lem:mistake-set-subset-iio}. Taking natural cardinalities and using
  \cref{def:aoa-weight} and
  \cref{def:mistake-inc} yields the claim. -/)
  (title := /-- Mistake weight under a one-round extension -/)
  (latexEnv := "lemma")]
lemma aoa_weight_append {X Y : Type*} (A : learner X Y) (h : X → Set Y)
    (xy : List (X × Y)) (x : X) (y : Y) :
    aoa_weight A (xy ++ [(x, y)]) h = aoa_weight A xy h + mistake_inc (A xy x) h x y := by
  classical
  have hunion : mistake_set A h (xy ++ [(x, y)]) =
      mistake_set A h xy ∪
        (if (y ∉ A xy x ∨ ¬ A xy x ⊆ h x) then ({xy.length} : Set ℕ) else ∅) := by
    ext k
    constructor
    · rintro ⟨p, hp, hcond⟩
      obtain ⟨hk, hp'⟩ := List.getElem?_eq_some_iff.1 hp
      rw [List.length_append, List.length_cons, List.length_nil] at hk
      rcases lt_or_ge k xy.length with hlt | hge
      · left
        refine ⟨p, ?_, ?_⟩
        · rw [List.getElem?_append_left hlt] at hp; exact hp
        · rwa [List.take_append_of_le_length hlt.le] at hcond
      · have hkeq : k = xy.length := by omega
        subst hkeq
        right
        have hpe : p = (x, y) := by
          have hval : (xy ++ [(x, y)])[xy.length]? = some (x, y) := by
            rw [List.getElem?_append_right (le_refl _)]; simp
          rw [hval] at hp; exact (Option.some_inj.1 hp).symm
        subst hpe
        have htk : (xy ++ [(x, y)]).take xy.length = xy := by
          rw [List.take_append_of_le_length (le_refl _), List.take_length]
        rw [htk] at hcond
        rw [if_pos hcond]; exact Set.mem_singleton _
    · intro hk
      rcases hk with hk | hk
      · obtain ⟨p, hp, hcond⟩ := hk
        have hlt : k < xy.length := mistake_set_subset_iio A h xy ⟨p, hp, hcond⟩
        refine ⟨p, ?_, ?_⟩
        · rw [List.getElem?_append_left hlt]; exact hp
        · rwa [List.take_append_of_le_length hlt.le]
      · by_cases hc : (y ∉ A xy x ∨ ¬ A xy x ⊆ h x)
        · rw [if_pos hc] at hk
          rw [Set.mem_singleton_iff] at hk
          subst hk
          refine ⟨(x, y), ?_, ?_⟩
          · rw [List.getElem?_append_right (le_refl _)]; simp
          · have htk : (xy ++ [(x, y)]).take xy.length = xy := by
              rw [List.take_append_of_le_length (le_refl _), List.take_length]
            rw [htk]; exact hc
        · rw [if_neg hc] at hk; exact absurd hk (Set.notMem_empty k)
  have hfin1 : (mistake_set A h xy).Finite :=
    (Set.finite_Iio _).subset (mistake_set_subset_iio A h xy)
  have hfin2 : (if (y ∉ A xy x ∨ ¬ A xy x ⊆ h x) then ({xy.length} : Set ℕ) else ∅).Finite := by
    split_ifs
    · exact Set.finite_singleton _
    · exact Set.finite_empty
  have hdisj : Disjoint (mistake_set A h xy)
      (if (y ∉ A xy x ∨ ¬ A xy x ⊆ h x) then ({xy.length} : Set ℕ) else ∅) := by
    rw [Set.disjoint_left]
    intro a ha hb
    have hlt : a < xy.length := mistake_set_subset_iio A h xy ha
    split_ifs at hb with hc
    · rw [Set.mem_singleton_iff] at hb; omega
    · exact Set.notMem_empty a hb
  rw [aoa_weight, aoa_weight, hunion, Set.ncard_union_eq hdisj hfin1 hfin2]
  congr 1
  rw [mistake_inc]
  split_ifs with hc
  · exact Set.ncard_singleton _
  · exact Set.ncard_empty _

@[blueprint "lem:unfalsified-append"
  (statement := /-- Let $\mathcal{H} \subseteq \{X \to 2^Y\}$, let $xy \in (X \times Y)^*$ be a
  trace and let $x \in X$, $y \in Y$. Then the unfalsified subclass of \cref{def:unfalsified}
  after extending $xy$ by the round $(x,y)$ is
  \[ \mathcal{H}^{xy(x,y)}_{\mathrm{uf}}
  = \{h \in \mathcal{H}^{xy}_{\mathrm{uf}} \mid y \in h(x)\}, \]
  the hypotheses of $\mathcal{H}^{xy}_{\mathrm{uf}}$ additionally compatible with the new round. -/)
  (proof := /-- By \cref{def:unfalsified,def:compat-set} a hypothesis $h$ lies in
  $\mathcal{H}^{xy(x,y)}_{\mathrm{uf}}$ iff $h \in \mathcal{H}$ and every round of $xy(x,y)$ has
  its label in $h$ of its instance. Since the rounds of $xy(x,y)$ are those of $xy$ together with
  the final round $(x,y)$, this condition is equivalent to $h \in \mathcal{H}$, every round of
  $xy$ being compatible with $h$, and $y \in h(x)$; that is, $h \in \mathcal{H}^{xy}_{\mathrm{uf}}$
  and $y \in h(x)$. -/)
  (title := /-- Unfalsified subclass under a one-round extension -/)
  (latexEnv := "lemma")]
lemma unfalsified_append {X Y : Type*} (H : Set (X → Set Y)) (xy : List (X × Y)) (x : X) (y : Y) :
    unfalsified H (xy ++ [(x, y)]) = {h ∈ unfalsified H xy | y ∈ h x} := by
  ext h
  simp only [unfalsified, compat_set, Set.mem_setOf_eq, Set.sep_setOf, List.length_append,
    List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨hH, -, hall⟩
    refine ⟨⟨hH, trivial, fun p hp => hall p (Or.inl hp)⟩, ?_⟩
    exact hall (x, y) (Or.inr rfl)
  · rintro ⟨⟨hH, -, hall⟩, hy⟩
    refine ⟨hH, trivial, ?_⟩
    rintro p (hp | rfl)
    · exact hall p hp
    · exact hy

@[blueprint "def:tree-coe"
  (statement := /-- Let $\mathcal{G} \subseteq \mathcal{G}'$ and let $T$ be an ambiguous shattered
  $\mathcal{G}$-tree of \cref{def:ambiguous-tree}. Since every leaf hypothesis of $T$ lies in
  $\mathcal{G} \subseteq \mathcal{G}'$, the same underlying data
  $(V,\mathbf{x},\mathbf{h},\mathrm{DE})$ is also an ambiguous shattered $\mathcal{G}'$-tree,
  denoted $T$ reinterpreted over $\mathcal{G}'$. -/)
  (title := /-- Reinterpreting a tree over a larger class -/)
  (latexEnv := "definition")]
def tree_coe {X Y : Type*} {G G' : Set (X → Set Y)} (hsub : G ⊆ G')
    (T : ambiguous_tree G) : ambiguous_tree G' where
  verts := T.verts
  inst := T.inst
  hyp := T.hyp
  defaults := T.defaults
  root_mem := T.root_mem
  prefix_closed := T.prefix_closed
  verts_finite := T.verts_finite
  default_child := T.default_child
  leaf_hyp_mem := fun u hu hl => hsub (T.leaf_hyp_mem u hu hl)
  leaf_hyp_compat := T.leaf_hyp_compat

@[blueprint "def:join-tree"
  (statement := /-- Let $\mathcal{G} \subseteq \{X \to 2^Y\}$, let $x_0 \in X$ be a root instance,
  let $C \subseteq Y$ be a finite set of child labels with a distinguished default label
  $d \in C$, and let $(\mathrm{sub}_y)_{y \in Y}$ be a family of ambiguous shattered
  $\mathcal{G}$-trees such that for every $y \in C$ every leaf hypothesis of $\mathrm{sub}_y$ takes
  the value $y$ at $x_0$. The *join tree* is the ambiguous shattered $\mathcal{G}$-tree with root
  $\varepsilon$ labelled by $x_0$, whose children are the vertices $y$ for $y \in C$, the child $d$
  being the default one, and whose subtree hanging under the edge $y$ is a copy of
  $\mathrm{sub}_y$; formally its vertices are $\varepsilon$ together with $y \cdot v$ for $y \in C$
  and $v$ a vertex of $\mathrm{sub}_y$, its instance and hypothesis labellings restrict to those of
  $\mathrm{sub}_y$ on each subtree, and its default set consists of $d$ together with the non-root
  default vertices of each subtree prefixed by their edge label. -/)
  (title := /-- Join of subtrees at a common root -/)
  (latexEnv := "definition")]
def join_tree {X Y : Type*} {G : Set (X → Set Y)} (x0 : X) (C : Finset Y) (d : Y)
    (hd : d ∈ C) (sub : Y → ambiguous_tree G)
    (hcompat : ∀ y ∈ C, ∀ v ∈ tree_leaves (sub y), y ∈ (sub y).hyp v x0) :
    ambiguous_tree G where
  verts := {w | w = [] ∨ ∃ y ∈ C, ∃ v ∈ (sub y).verts, w = y :: v}
  inst := fun w => match w with
    | [] => x0
    | y :: v => (sub y).inst v
  hyp := fun w => match w with
    | [] => (sub d).hyp []
    | y :: v => (sub y).hyp v
  defaults := {w | w = [d] ∨ ∃ y ∈ C, ∃ v ∈ (sub y).defaults, v ≠ [] ∧ w = y :: v}
  root_mem := Or.inl rfl
  prefix_closed := by
    intro u hu w hw
    rcases hu with rfl | ⟨y, hyC, v, hv, rfl⟩
    · rw [List.prefix_nil.1 hw]; exact Or.inl rfl
    · rcases w with _ | ⟨a, w'⟩
      · exact Or.inl rfl
      · rw [List.cons_prefix_cons] at hw
        obtain ⟨rfl, hw'⟩ := hw
        exact Or.inr ⟨a, hyC, w', (sub a).prefix_closed v hv w' hw', rfl⟩
  verts_finite := by
    apply Set.Finite.subset
      ((Set.Finite.biUnion C.finite_toSet
        (fun y _ => ((sub y).verts_finite).image (fun v => y :: v))).insert [])
    intro w hw
    rcases hw with rfl | ⟨y, hyC, v, hv, rfl⟩
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_iff.2 (Or.inr (Set.mem_biUnion hyC (Set.mem_image_of_mem _ hv)))
  default_child := by
    intro u hu hchild
    rcases hu with rfl | ⟨y0, hy0C, v0, hv0, rfl⟩
    · refine ⟨d, ⟨?_, ?_⟩, ?_⟩
      · rw [List.nil_append]; exact Or.inr ⟨d, hd, [], (sub d).root_mem, rfl⟩
      · rw [List.nil_append]; exact Or.inl rfl
      · rintro y' ⟨hy'v, hy'd⟩
        rw [List.nil_append] at hy'd
        rcases hy'd with h1 | ⟨y2, hy2C, v2, hv2, hv2ne, h2⟩
        · exact (List.cons.inj h1).1
        · exact absurd (List.cons.inj h2).2.symm hv2ne
    · obtain ⟨z, hz⟩ := hchild
      rw [List.cons_append] at hz
      have hzsub : v0 ++ [z] ∈ (sub y0).verts := by
        rcases hz with h0 | ⟨y', hy'C, v', hv', heq⟩
        · exact absurd h0 (by simp)
        · obtain ⟨rfl, rfl⟩ := List.cons.inj heq; exact hv'
      obtain ⟨e, ⟨he_v, he_d⟩, he_uniq⟩ := (sub y0).default_child v0 hv0 ⟨z, hzsub⟩
      refine ⟨e, ⟨?_, ?_⟩, ?_⟩
      · rw [List.cons_append]; exact Or.inr ⟨y0, hy0C, v0 ++ [e], he_v, rfl⟩
      · rw [List.cons_append]
        exact Or.inr ⟨y0, hy0C, v0 ++ [e], he_d, by simp, rfl⟩
      · rintro e' ⟨he'v, he'd⟩
        rw [List.cons_append] at he'v he'd
        have hv'' : v0 ++ [e'] ∈ (sub y0).verts := by
          rcases he'v with h0 | ⟨y', hy'C, v', hv', heq⟩
          · exact absurd h0 (by simp)
          · obtain ⟨rfl, rfl⟩ := List.cons.inj heq; exact hv'
        have hd'' : v0 ++ [e'] ∈ (sub y0).defaults := by
          rcases he'd with h0 | ⟨y', hy'C, v', hv', hv'ne, heq⟩
          · exact absurd (List.cons.inj h0).2 (by simp)
          · obtain ⟨rfl, rfl⟩ := List.cons.inj heq; exact hv'
        exact he_uniq e' ⟨hv'', hd''⟩
  leaf_hyp_mem := by
    intro u hu hleaf
    rcases hu with rfl | ⟨y0, hy0C, v0, hv0, rfl⟩
    · exact absurd ⟨d, Or.inr ⟨d, hd, [], (sub d).root_mem, by rw [List.nil_append]⟩⟩ hleaf
    · have hvleaf : ¬ ∃ z : Y, v0 ++ [z] ∈ (sub y0).verts := by
        rintro ⟨z, hz⟩
        exact hleaf ⟨z, by rw [List.cons_append]; exact Or.inr ⟨y0, hy0C, v0 ++ [z], hz, rfl⟩⟩
      exact (sub y0).leaf_hyp_mem v0 hv0 hvleaf
  leaf_hyp_compat := by
    intro u hu hleaf k y hk
    rcases hu with rfl | ⟨y0, hy0C, v0, hv0, rfl⟩
    · exact absurd (List.getElem?_eq_some_iff.1 hk).1 (by simp)
    · have hvleaf : ¬ ∃ z : Y, v0 ++ [z] ∈ (sub y0).verts := by
        rintro ⟨z, hz⟩
        exact hleaf ⟨z, by rw [List.cons_append]; exact Or.inr ⟨y0, hy0C, v0 ++ [z], hz, rfl⟩⟩
      rcases k with _ | j
      · rw [List.getElem?_cons_zero] at hk
        obtain rfl := Option.some_inj.1 hk
        exact hcompat y0 hy0C v0 ⟨hv0, hvleaf⟩
      · rw [List.getElem?_cons_succ] at hk
        have hcp := (sub y0).leaf_hyp_compat v0 hv0 hvleaf j y hk
        simpa [List.take_succ_cons] using hcp

@[blueprint "lem:tree-leaves-nonempty"
  (statement := /-- Every ambiguous shattered $\mathcal{H}$-tree $T$ of \cref{def:ambiguous-tree}
  has at least one leaf, i.e. $\mathrm{Lf}(T) \neq \emptyset$, with $\mathrm{Lf}$ as in
  \cref{def:tree-leaves}. -/)
  (proof := /-- The vertex set $V$ is finite by \cref{def:ambiguous-tree} and non-empty since it
  contains the root $\varepsilon$. Choose $u \in V$ of maximal length. If $u$ had a child
  $u \cdot y \in V$, that child would be strictly longer, contradicting maximality; hence $u$ has
  no child and is a leaf of \cref{def:tree-leaves}. -/)
  (title := /-- Every tree has a leaf -/)
  (latexEnv := "lemma")]
lemma tree_leaves_nonempty {X Y : Type*} {G : Set (X → Set Y)} (T : ambiguous_tree G) :
    (tree_leaves T).Nonempty := by
  classical
  obtain ⟨u, hu, hmax⟩ :=
    T.verts_finite.exists_maximalFor (fun v : List Y => v.length) _ ⟨[], T.root_mem⟩
  refine ⟨u, hu, ?_⟩
  rintro ⟨y, hy⟩
  have hle : u.length ≤ (u ++ [y]).length := by simp
  have hcon := hmax hy hle
  simp only [List.length_append, List.length_cons, List.length_nil] at hcon
  omega

@[blueprint "lem:relevant-edges-ncard-le"
  (statement := /-- Let $T$ be an ambiguous shattered $\mathcal{H}$-tree and $u \in Y^*$. Then
  $|R_T(u)| \le |u|$, with $R_T$ as in \cref{def:relevant-edges}. -/)
  (proof := /-- By \cref{def:relevant-edges} every element of $R_T(u)$ is an index $k < |u|$, so
  $R_T(u) \subseteq \{0,\dots,|u|-1\}$, a set of cardinality $|u|$. Monotonicity of the natural
  cardinality under inclusion into a finite set gives $|R_T(u)| \le |u|$. -/)
  (title := /-- Relevant edges are indexed within the root path -/)
  (latexEnv := "lemma")]
lemma relevant_edges_ncard_le {X Y : Type*} {G : Set (X → Set Y)} (T : ambiguous_tree G)
    (u : List Y) : (relevant_edges T u).ncard ≤ u.length := by
  have hsub : relevant_edges T u ⊆ Set.Iio u.length := by
    intro k hk; exact hk.1
  calc (relevant_edges T u).ncard
      ≤ (Set.Iio u.length).ncard := Set.ncard_le_ncard hsub (Set.finite_Iio _)
    _ = u.length := by rw [← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]

@[blueprint "lem:length-le-tree-depth"
  (statement := /-- Let $T$ be an ambiguous shattered $\mathcal{H}$-tree with vertex set $V$ and
  let $u \in V$. Then $|u| \le \mathrm{dep}(T)$, with $\mathrm{dep}$ as in
  \cref{def:tree-depth}. -/)
  (proof := /-- By \cref{def:tree-depth} the depth is the supremum of the lengths of the vertices
  of $T$, taken over the finite vertex set $V$. Since $u \in V$, the length $|u|$ is one of the
  elements of this bounded set, hence at most its supremum. -/)
  (title := /-- Vertex length is bounded by the depth -/)
  (latexEnv := "lemma")]
lemma length_le_tree_depth {X Y : Type*} {G : Set (X → Set Y)} (T : ambiguous_tree G)
    {u : List Y} (hu : u ∈ T.verts) : u.length ≤ tree_depth T := by
  apply le_csSup
  · exact (T.verts_finite.image _).bddAbove
  · exact ⟨u, hu, rfl⟩

@[blueprint "lem:tree-rank-weighted-le"
  (statement := /-- Let $T$ be an ambiguous shattered $\mathcal{G}$-tree, let
  $w : \{X \to 2^Y\} \to \mathbb{N}$ and let $B \in \mathbb{N}$ satisfy $w(h) \le B$ for every
  $h \in \mathcal{G}$. Then $\mathrm{rank}_w(T) \le \mathrm{dep}(T) + B$, with $\mathrm{rank}_w$ as
  in \cref{def:tree-rank-weighted} and $\mathrm{dep}$ as in \cref{def:tree-depth}. -/)
  (proof := /-- By \cref{lem:tree-leaves-nonempty} there is a leaf $u \in \mathrm{Lf}(T)$. By
  \cref{def:tree-rank-weighted} the rank is the infimum over leaves of $|R_T(v)| + w(\mathbf{h}_v)$,
  so it is at most the value $|R_T(u)| + w(\mathbf{h}_u)$ at this particular leaf. By
  \cref{lem:relevant-edges-ncard-le} and \cref{lem:length-le-tree-depth} we have
  $|R_T(u)| \le |u| \le \mathrm{dep}(T)$, and since $u$ is a leaf $\mathbf{h}_u \in \mathcal{G}$ by
  \cref{def:ambiguous-tree}, whence $w(\mathbf{h}_u) \le B$. Adding gives
  $|R_T(u)| + w(\mathbf{h}_u) \le \mathrm{dep}(T) + B$. -/)
  (title := /-- The weighted rank is bounded by depth plus the weight bound -/)
  (latexEnv := "lemma")]
lemma tree_rank_weighted_le {X Y : Type*} {G : Set (X → Set Y)} (T : ambiguous_tree G)
    (w : (X → Set Y) → ℕ) (B : ℕ) (hB : ∀ h ∈ G, w h ≤ B) :
    tree_rank_weighted T w ≤ tree_depth T + B := by
  obtain ⟨u, hu_leaf⟩ := tree_leaves_nonempty T
  have hu_verts : u ∈ T.verts := hu_leaf.1
  have hu_hyp : T.hyp u ∈ G := T.leaf_hyp_mem u hu_verts hu_leaf.2
  have hmem : (relevant_edges T u).ncard + w (T.hyp u) ∈
      (fun v => (relevant_edges T v).ncard + w (T.hyp v)) '' tree_leaves T :=
    ⟨u, hu_leaf, rfl⟩
  refine (Nat.sInf_le hmem).trans ?_
  have h1 : (relevant_edges T u).ncard ≤ tree_depth T :=
    (relevant_edges_ncard_le T u).trans (length_le_tree_depth T hu_verts)
  have h2 : w (T.hyp u) ≤ B := hB _ hu_hyp
  omega

@[blueprint "lem:al-dim-weighted-bddAbove"
  (statement := /-- Let $\mathcal{G} \subseteq \{X \to 2^Y\}$, let
  $w : \{X \to 2^Y\} \to \mathbb{N}$ and $B, n \in \mathbb{N}$ with $w(h) \le B$ for every
  $h \in \mathcal{G}$. Then the set of $w$-weighted ranks of ambiguous shattered
  $\mathcal{G}$-trees of depth at most $n$, whose supremum defines
  $\mathrm{AL}_w(\mathcal{G},n)$ in \cref{def:al-dim-weighted}, is bounded above by $n + B$. -/)
  (proof := /-- Let $\rho$ belong to the set, say $\rho = \mathrm{rank}_w(T)$ with
  $\mathrm{dep}(T) \le n$. By \cref{lem:tree-rank-weighted-le},
  $\rho \le \mathrm{dep}(T) + B \le n + B$. Hence $n + B$ is an upper bound. -/)
  (title := /-- The weighted-rank set is bounded when the weight is bounded -/)
  (latexEnv := "lemma")]
lemma al_dim_weighted_bddAbove {X Y : Type*} {G : Set (X → Set Y)} (w : (X → Set Y) → ℕ)
    (B n : ℕ) (hB : ∀ h ∈ G, w h ≤ B) :
    BddAbove {r : ℕ | ∃ T : ambiguous_tree G, tree_depth T ≤ n ∧ tree_rank_weighted T w = r} := by
  refine ⟨n + B, ?_⟩
  rintro r ⟨T, hd, rfl⟩
  exact (tree_rank_weighted_le T w B hB).trans (by omega)

@[blueprint "lem:le-al-dim-weighted"
  (statement := /-- Let $\mathcal{G} \subseteq \{X \to 2^Y\}$, let
  $w : \{X \to 2^Y\} \to \mathbb{N}$ and $B, n \in \mathbb{N}$ with $w(h) \le B$ for every
  $h \in \mathcal{G}$. Then for every ambiguous shattered $\mathcal{G}$-tree $T$ with
  $\mathrm{dep}(T) \le n$ one has $\mathrm{rank}_w(T) \le \mathrm{AL}_w(\mathcal{G},n)$, with
  $\mathrm{AL}_w$ as in \cref{def:al-dim-weighted}. -/)
  (proof := /-- By \cref{def:al-dim-weighted}, $\mathrm{AL}_w(\mathcal{G},n)$ is the supremum of
  the set of ranks of $\mathcal{G}$-trees of depth at most $n$. By
  \cref{lem:al-dim-weighted-bddAbove} this set is bounded above, and $\mathrm{rank}_w(T)$ belongs
  to it because $\mathrm{dep}(T) \le n$; therefore $\mathrm{rank}_w(T)$ is at most the supremum. -/)
  (title := /-- A bounded-depth rank is dominated by the weighted dimension -/)
  (latexEnv := "lemma")]
lemma le_al_dim_weighted {X Y : Type*} {G : Set (X → Set Y)} (w : (X → Set Y) → ℕ)
    (B n : ℕ) (hB : ∀ h ∈ G, w h ≤ B) (T : ambiguous_tree G) (hd : tree_depth T ≤ n) :
    tree_rank_weighted T w ≤ al_dim_weighted G w n := by
  apply le_csSup (al_dim_weighted_bddAbove w B n hB)
  exact ⟨T, hd, rfl⟩

@[blueprint "lem:exists-tree-of-le-al-dim"
  (statement := /-- Let $\mathcal{G} \subseteq \{X \to 2^Y\}$, let
  $w : \{X \to 2^Y\} \to \mathbb{N}$ and $B, n, r \in \mathbb{N}$ with $w(h) \le B$ for every
  $h \in \mathcal{G}$, with $1 \le r$ and $r \le \mathrm{AL}_w(\mathcal{G},n)$. Then there exists an
  ambiguous shattered $\mathcal{G}$-tree $T$ with $\mathrm{dep}(T) \le n$ and
  $r \le \mathrm{rank}_w(T)$, with $\mathrm{AL}_w$ as in \cref{def:al-dim-weighted}. -/)
  (proof := /-- By \cref{def:al-dim-weighted}, $\mathrm{AL}_w(\mathcal{G},n)$ is the supremum of
  the set $S$ of ranks of $\mathcal{G}$-trees of depth at most $n$. Since $\mathrm{AL}_w \ge r \ge
  1 > 0$ and the supremum of the empty set is $0$, $S$ is non-empty; by
  \cref{lem:al-dim-weighted-bddAbove} it is bounded above. Hence its supremum belongs to $S$, so
  there is a tree $T$ with $\mathrm{dep}(T) \le n$ and $\mathrm{rank}_w(T) = \mathrm{AL}_w \ge r$.
  -/)
  (title := /-- A weighted dimension at least $r$ is witnessed by a tree of rank at least $r$ -/)
  (latexEnv := "lemma")]
lemma exists_tree_of_le_al_dim {X Y : Type*} {G : Set (X → Set Y)} (w : (X → Set Y) → ℕ)
    (B n r : ℕ) (hB : ∀ h ∈ G, w h ≤ B) (hr : 1 ≤ r) (hle : r ≤ al_dim_weighted G w n) :
    ∃ T : ambiguous_tree G, tree_depth T ≤ n ∧ r ≤ tree_rank_weighted T w := by
  set S := {ρ : ℕ | ∃ T : ambiguous_tree G, tree_depth T ≤ n ∧ tree_rank_weighted T w = ρ} with hS
  have hne : S.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [al_dim_weighted, ← hS, hcon] at hle
    rw [show (sSup (∅ : Set ℕ)) = 0 from csSup_empty] at hle
    omega
  have hmem : sSup S ∈ S := Nat.sSup_mem hne (al_dim_weighted_bddAbove w B n hB)
  obtain ⟨T, hd, hrank⟩ := hmem
  refine ⟨T, hd, ?_⟩
  rw [hrank]
  exact hle

@[blueprint "lem:join-child-iff"
  (statement := /-- In the join tree of \cref{def:join-tree}, a singleton word $[z]$ is a vertex iff
  $z \in C$. -/)
  (proof := /-- By \cref{def:join-tree} a vertex is either $\varepsilon$ or of the form
  $y \cdot w$ with $y \in C$ and $w$ a vertex of $\mathrm{sub}_y$. The word $[z]$ is not
  $\varepsilon$; and $[z] = y \cdot w$ forces $y = z$ and $w = \varepsilon$, which is a vertex of
  $\mathrm{sub}_z$ by the root axiom of \cref{def:ambiguous-tree}. Hence $[z]$ is a vertex iff
  $z \in C$. -/)
  (title := /-- Singleton vertices of the join tree -/)
  (latexEnv := "lemma")]
lemma join_child_iff {X Y : Type*} {G : Set (X → Set Y)} (x0 : X) (C : Finset Y) (d : Y)
    (hd : d ∈ C) (sub : Y → ambiguous_tree G)
    (hc : ∀ y ∈ C, ∀ v ∈ tree_leaves (sub y), y ∈ (sub y).hyp v x0) (z : Y) :
    ([z] ∈ (join_tree x0 C d hd sub hc).verts) ↔ z ∈ C := by
  constructor
  · rintro (h | ⟨y, hyC, v, hv, heq⟩)
    · exact absurd h (by simp)
    · obtain ⟨rfl, -⟩ := List.cons.inj heq; exact hyC
  · intro hz
    exact Or.inr ⟨z, hz, [], (sub z).root_mem, rfl⟩

@[blueprint "lem:join-leaf-iff"
  (statement := /-- In the join tree of \cref{def:join-tree}, a word $u$ is a leaf iff it is of the
  form $y \cdot v$ with $y \in C$ and $v$ a leaf of $\mathrm{sub}_y$, with $\mathrm{Lf}$ as in
  \cref{def:tree-leaves}. -/)
  (proof := /-- The root $\varepsilon$ is not a leaf because $d \in C$ gives the child $[d]$. Any
  other vertex is $y \cdot v$ with $y \in C$ and $v$ a vertex of $\mathrm{sub}_y$ by
  \cref{def:join-tree}; it has a child in the join tree iff $v$ has a child in $\mathrm{sub}_y$,
  so $y \cdot v$ is a leaf iff $v$ is a leaf of $\mathrm{sub}_y$ by \cref{def:tree-leaves}. -/)
  (title := /-- Leaves of the join tree -/)
  (latexEnv := "lemma")]
lemma join_leaf_iff {X Y : Type*} {G : Set (X → Set Y)} (x0 : X) (C : Finset Y) (d : Y)
    (hd : d ∈ C) (sub : Y → ambiguous_tree G)
    (hc : ∀ y ∈ C, ∀ v ∈ tree_leaves (sub y), y ∈ (sub y).hyp v x0) (u : List Y) :
    (u ∈ tree_leaves (join_tree x0 C d hd sub hc)) ↔
      ∃ y ∈ C, ∃ v ∈ tree_leaves (sub y), u = y :: v := by
  constructor
  · rintro ⟨huv, hul⟩
    rcases huv with rfl | ⟨y, hyC, v, hv, rfl⟩
    · exact absurd ⟨d, Or.inr ⟨d, hd, [], (sub d).root_mem, by rw [List.nil_append]⟩⟩ hul
    · refine ⟨y, hyC, v, ⟨hv, ?_⟩, rfl⟩
      rintro ⟨z, hz⟩
      exact hul ⟨z, by rw [List.cons_append]; exact Or.inr ⟨y, hyC, v ++ [z], hz, rfl⟩⟩
  · rintro ⟨y, hyC, v, ⟨hv, hvl⟩, rfl⟩
    refine ⟨Or.inr ⟨y, hyC, v, hv, rfl⟩, ?_⟩
    rintro ⟨z, hz⟩
    rw [List.cons_append] at hz
    rcases hz with h0 | ⟨y', hy'C, v', hv', heq⟩
    · exact absurd h0 (by simp)
    · obtain ⟨rfl, rfl⟩ := List.cons.inj heq
      exact hvl ⟨z, hv'⟩

@[blueprint "lem:join-depth-le"
  (statement := /-- Let $m \in \mathbb{N}$ and suppose every subtree $\mathrm{sub}_y$ with $y \in C$
  of the join tree of \cref{def:join-tree} has depth at most $m$. Then the join tree has depth at
  most $m+1$, with $\mathrm{dep}$ as in \cref{def:tree-depth}. -/)
  (proof := /-- By \cref{def:tree-depth} the depth is the supremum of the lengths of the vertices.
  A vertex is either $\varepsilon$, of length $0 \le m+1$, or $y \cdot v$ with $y \in C$ and $v$ a
  vertex of $\mathrm{sub}_y$; then $|y \cdot v| = |v| + 1 \le \mathrm{dep}(\mathrm{sub}_y) + 1 \le
  m+1$ using \cref{lem:length-le-tree-depth}. Hence $m+1$ bounds all vertex lengths, so it bounds
  their supremum. -/)
  (title := /-- Depth of the join tree -/)
  (latexEnv := "lemma")]
lemma join_depth_le {X Y : Type*} {G : Set (X → Set Y)} (x0 : X) (C : Finset Y) (d : Y)
    (hd : d ∈ C) (sub : Y → ambiguous_tree G)
    (hc : ∀ y ∈ C, ∀ v ∈ tree_leaves (sub y), y ∈ (sub y).hyp v x0) (m : ℕ)
    (hsub : ∀ y ∈ C, tree_depth (sub y) ≤ m) :
    tree_depth (join_tree x0 C d hd sub hc) ≤ m + 1 := by
  refine csSup_le ⟨0, ?_⟩ ?_
  · exact ⟨[], (join_tree x0 C d hd sub hc).root_mem, rfl⟩
  rintro n ⟨u, huv, rfl⟩
  rcases huv with rfl | ⟨y, hyC, v, hv, rfl⟩
  · simp
  · have : v.length ≤ m := (length_le_tree_depth (sub y) hv).trans (hsub y hyC)
    simp only [List.length_cons]
    omega

@[blueprint "lem:tree-coe-eq"
  (statement := /-- Let $\mathcal{G} \subseteq \mathcal{G}'$ and let $T$ be an ambiguous shattered
  $\mathcal{G}$-tree. Its reinterpretation over $\mathcal{G}'$ of \cref{def:tree-coe} has the same
  leaves, relevant-edge sets, depth and $w$-weighted rank as $T$ for every weight $w$. -/)
  (proof := /-- The reinterpretation of \cref{def:tree-coe} copies the underlying data
  $(V,\mathbf{x},\mathbf{h},\mathrm{DE})$ of $T$ verbatim, so \cref{def:tree-leaves},
  \cref{def:relevant-edges}, \cref{def:tree-depth} and \cref{def:tree-rank-weighted} all evaluate
  identically; the equalities hold by reflexivity. -/)
  (title := /-- Reinterpretation preserves all tree quantities -/)
  (latexEnv := "lemma")]
lemma tree_coe_eq {X Y : Type*} {G G' : Set (X → Set Y)} (hsub : G ⊆ G')
    (T : ambiguous_tree G) (w : (X → Set Y) → ℕ) :
    tree_leaves (tree_coe hsub T) = tree_leaves T ∧
      (∀ u, relevant_edges (tree_coe hsub T) u = relevant_edges T u) ∧
      tree_depth (tree_coe hsub T) = tree_depth T ∧
      tree_rank_weighted (tree_coe hsub T) w = tree_rank_weighted T w :=
  ⟨rfl, fun _ => rfl, rfl, rfl⟩

@[blueprint "lem:join-relevant-succ-mem"
  (statement := /-- In the join tree of \cref{def:join-tree}, for $y \in C$ and $v \in Y^*$ and
  $j \in \mathbb{N}$, the index $j+1$ is relevant for the vertex $y \cdot v$ iff $j$ is relevant
  for $v$ in $\mathrm{sub}_y$, with $R$ as in \cref{def:relevant-edges}. -/)
  (proof := /-- Unfolding \cref{def:relevant-edges} for the vertex $y \cdot v$ at index $j+1$: the
  length-$(j+2)$ prefix is $y$ followed by the length-$(j+1)$ prefix of $v$, so it lies in the
  default set of the join tree of \cref{def:join-tree} iff the corresponding prefix of $v$ lies in
  the default set of $\mathrm{sub}_y$ (the singleton-root default $[d]$ cannot arise for a prefix of
  positive length), and the child at that prefix, together with the hypothesis value, matches that
  of $\mathrm{sub}_y$ at index $j$. Hence the two membership conditions are equivalent. -/)
  (title := /-- Non-root relevant edges of a join-tree vertex -/)
  (latexEnv := "lemma")]
lemma join_relevant_succ_mem {X Y : Type*} {G : Set (X → Set Y)} (x0 : X) (C : Finset Y) (d : Y)
    (hd : d ∈ C) (sub : Y → ambiguous_tree G)
    (hc : ∀ y ∈ C, ∀ v ∈ tree_leaves (sub y), y ∈ (sub y).hyp v x0) (y : Y) (hyC : y ∈ C)
    (v : List Y) (j : ℕ) :
    (j + 1 ∈ relevant_edges (join_tree x0 C d hd sub hc) (y :: v)) ↔
      (j ∈ relevant_edges (sub y) v) := by
  simp only [relevant_edges, Set.mem_setOf_eq, List.length_cons, List.take_succ_cons,
    List.cons_append]
  constructor
  · rintro ⟨hlt, hdisj⟩
    refine ⟨by omega, ?_⟩
    have htne : List.take (j + 1) v ≠ [] := by
      apply List.ne_nil_of_length_pos; rw [List.length_take]; omega
    rcases hdisj with hnd | ⟨z, hzv, hznot⟩
    · left
      intro hcon
      apply hnd
      exact Or.inr ⟨y, hyC, v.take (j + 1), hcon, htne, rfl⟩
    · right
      refine ⟨z, ?_, hznot⟩
      rcases hzv with h0 | ⟨y', hy'C, v', hv', heq⟩
      · exact absurd h0 (by simp)
      · obtain ⟨rfl, rfl⟩ := List.cons.inj heq; exact hv'
  · rintro ⟨hlt, hdisj⟩
    refine ⟨by omega, ?_⟩
    rcases hdisj with hnd | ⟨z, hzv, hznot⟩
    · left
      intro hcon
      apply hnd
      rcases hcon with h1 | ⟨y', hy'C, v', hv', hv'ne, heq⟩
      · exfalso
        have h2 := (List.cons.inj h1).2
        have : List.take (j + 1) v ≠ [] := by
          apply List.ne_nil_of_length_pos; rw [List.length_take]; omega
        exact this h2
      · obtain ⟨rfl, rfl⟩ := List.cons.inj heq; exact hv'
    · right
      exact ⟨z, Or.inr ⟨y, hyC, v.take j ++ [z], hzv, rfl⟩, hznot⟩

@[blueprint "lem:join-relevant-zero-mem"
  (statement := /-- In the join tree of \cref{def:join-tree}, for $y \in C$ and a vertex
  $y \cdot v$ with $y \neq d$, the root index $0$ is relevant for $y \cdot v$, with $R$ as in
  \cref{def:relevant-edges}. -/)
  (proof := /-- The length-$1$ prefix of $y \cdot v$ is $[y]$. Since $y \neq d$, the word $[y]$ is
  not the root default $[d]$, and being of length $1$ it is not a positive-length default of a
  subtree either, so $[y] \notin \mathrm{DE}$; by \cref{def:relevant-edges} the index $0$ is
  therefore relevant. -/)
  (title := /-- The root edge of a non-default branch is relevant -/)
  (latexEnv := "lemma")]
lemma join_relevant_zero_mem {X Y : Type*} {G : Set (X → Set Y)} (x0 : X) (C : Finset Y) (d : Y)
    (hd : d ∈ C) (sub : Y → ambiguous_tree G)
    (hc : ∀ y ∈ C, ∀ v ∈ tree_leaves (sub y), y ∈ (sub y).hyp v x0) (y : Y) (v : List Y)
    (hyd : y ≠ d) :
    (0 ∈ relevant_edges (join_tree x0 C d hd sub hc) (y :: v)) := by
  simp only [relevant_edges, Set.mem_setOf_eq, List.length_cons]
  refine ⟨by omega, Or.inl ?_⟩
  intro hcon
  rw [List.take_succ_cons, List.take_zero] at hcon
  rcases hcon with h1 | ⟨y', hy'C, v', hv', hv'ne, heq⟩
  · exact hyd (List.cons.inj h1).1
  · exact hv'ne (List.cons.inj heq).2.symm

@[blueprint "lem:join-relevant-zero-mem'"
  (statement := /-- In the join tree of \cref{def:join-tree}, for $y \in C$ and a vertex
  $y \cdot v$ with leaf hypothesis $h$, if some child $z \in C$ satisfies $z \notin h(x_0)$ then the
  root index $0$ is relevant for $y \cdot v$, with $R$ as in \cref{def:relevant-edges}. -/)
  (proof := /-- By \cref{lem:join-child-iff} the singleton $[z]$ is a child of the root, and
  $z \notin \mathbf{h}_{y \cdot v}(\mathbf{x}_\varepsilon) = h(x_0)$; by the second clause of
  \cref{def:relevant-edges} this makes the root index $0$ relevant. -/)
  (title := /-- A forbidden child makes the root edge relevant -/)
  (latexEnv := "lemma")]
lemma join_relevant_zero_mem' {X Y : Type*} {G : Set (X → Set Y)} (x0 : X) (C : Finset Y) (d : Y)
    (hd : d ∈ C) (sub : Y → ambiguous_tree G)
    (hc : ∀ y ∈ C, ∀ v ∈ tree_leaves (sub y), y ∈ (sub y).hyp v x0) (y : Y) (v : List Y)
    (z : Y) (hzC : z ∈ C) (hznot : z ∉ (sub y).hyp v x0) :
    (0 ∈ relevant_edges (join_tree x0 C d hd sub hc) (y :: v)) := by
  simp only [relevant_edges, Set.mem_setOf_eq, List.length_cons]
  refine ⟨by omega, Or.inr ⟨z, ?_, ?_⟩⟩
  · rw [List.take_zero, List.nil_append]
    exact (join_child_iff x0 C d hd sub hc z).2 hzC
  · rw [List.take_zero]
    exact hznot

@[blueprint "lem:join-relevant-ge-base"
  (statement := /-- In the join tree of \cref{def:join-tree}, for $y \in C$ and a vertex
  $y \cdot v$, one has $|R(y \cdot v)| \ge |R_{\mathrm{sub}_y}(v)|$, with $R$ as in
  \cref{def:relevant-edges}. -/)
  (proof := /-- By \cref{lem:join-relevant-succ-mem} the map $j \mapsto j+1$ sends
  $R_{\mathrm{sub}_y}(v)$ injectively into $R(y \cdot v)$; monotonicity of the natural cardinality
  under an injective image into a finite set gives the inequality. -/)
  (title := /-- Base bound for relevant edges of a join-tree vertex -/)
  (latexEnv := "lemma")]
lemma join_relevant_ge_base {X Y : Type*} {G : Set (X → Set Y)} (x0 : X) (C : Finset Y) (d : Y)
    (hd : d ∈ C) (sub : Y → ambiguous_tree G)
    (hc : ∀ y ∈ C, ∀ v ∈ tree_leaves (sub y), y ∈ (sub y).hyp v x0) (y : Y) (hyC : y ∈ C)
    (v : List Y) :
    (relevant_edges (sub y) v).ncard ≤
      (relevant_edges (join_tree x0 C d hd sub hc) (y :: v)).ncard := by
  set J := join_tree x0 C d hd sub hc with hJ
  have hsub : (fun j => j + 1) '' relevant_edges (sub y) v ⊆ relevant_edges J (y :: v) := by
    rintro k ⟨j, hj, rfl⟩
    exact (join_relevant_succ_mem x0 C d hd sub hc y hyC v j).2 hj
  have hfinJ : (relevant_edges J (y :: v)).Finite :=
    (Set.finite_Iio _).subset (fun k hk => hk.1)
  calc (relevant_edges (sub y) v).ncard
      = ((fun j => j + 1) '' relevant_edges (sub y) v).ncard :=
        (Set.ncard_image_of_injective _ (add_left_injective 1)).symm
    _ ≤ (relevant_edges J (y :: v)).ncard := Set.ncard_le_ncard hsub hfinJ

@[blueprint "lem:join-relevant-ge-succ"
  (statement := /-- In the join tree of \cref{def:join-tree}, for $y \in C$ and a vertex
  $y \cdot v$, if the root index $0$ is relevant for $y \cdot v$ then
  $|R(y \cdot v)| \ge |R_{\mathrm{sub}_y}(v)| + 1$, with $R$ as in \cref{def:relevant-edges}. -/)
  (proof := /-- By \cref{lem:join-relevant-succ-mem} the injective image of $R_{\mathrm{sub}_y}(v)$
  under $j \mapsto j+1$ is contained in $R(y \cdot v)$ and consists of positive indices, so it does
  not contain $0$; adjoining the relevant index $0$ gives an $(|R_{\mathrm{sub}_y}(v)|+1)$-element
  subset of $R(y \cdot v)$, whence the bound by monotonicity of cardinality. -/)
  (title := /-- Incremented bound when the root edge is relevant -/)
  (latexEnv := "lemma")]
lemma join_relevant_ge_succ {X Y : Type*} {G : Set (X → Set Y)} (x0 : X) (C : Finset Y) (d : Y)
    (hd : d ∈ C) (sub : Y → ambiguous_tree G)
    (hc : ∀ y ∈ C, ∀ v ∈ tree_leaves (sub y), y ∈ (sub y).hyp v x0) (y : Y) (hyC : y ∈ C)
    (v : List Y)
    (hzero : 0 ∈ relevant_edges (join_tree x0 C d hd sub hc) (y :: v)) :
    (relevant_edges (sub y) v).ncard + 1 ≤
      (relevant_edges (join_tree x0 C d hd sub hc) (y :: v)).ncard := by
  set J := join_tree x0 C d hd sub hc with hJ
  have hsub : insert 0 ((fun j => j + 1) '' relevant_edges (sub y) v) ⊆
      relevant_edges J (y :: v) := by
    rintro k hk
    rcases hk with rfl | ⟨j, hj, rfl⟩
    · exact hzero
    · exact (join_relevant_succ_mem x0 C d hd sub hc y hyC v j).2 hj
  have hfinJ : (relevant_edges J (y :: v)).Finite :=
    (Set.finite_Iio _).subset (fun k hk => hk.1)
  have hfinImg : ((fun j => j + 1) '' relevant_edges (sub y) v).Finite :=
    (((Set.finite_Iio _).subset (fun k (hk : k ∈ relevant_edges (sub y) v) => hk.1))).image _
  have hnotmem : (0 : ℕ) ∉ (fun j => j + 1) '' relevant_edges (sub y) v := by
    rintro ⟨j, -, hj⟩; exact Nat.succ_ne_zero j hj
  have hins : (insert 0 ((fun j => j + 1) '' relevant_edges (sub y) v)).ncard =
      (relevant_edges (sub y) v).ncard + 1 := by
    rw [Set.ncard_insert_of_notMem hnotmem hfinImg,
      Set.ncard_image_of_injective _ (add_left_injective 1)]
  calc (relevant_edges (sub y) v).ncard + 1
      = (insert 0 ((fun j => j + 1) '' relevant_edges (sub y) v)).ncard := hins.symm
    _ ≤ (relevant_edges J (y :: v)).ncard := Set.ncard_le_ncard hsub hfinJ

@[blueprint "lem:mistake-set-prefix-congr"
  (statement := /-- Let $A, B$ be deterministic learners as in \cref{def:learner}, let
  $h : X \to 2^Y$ and let $xy \in (X \times Y)^*$ be a trace. If $A$ and $B$ agree on every proper
  prefix of $xy$, that is $A(xy_{:k}) = B(xy_{:k})$ for all $k < |xy|$, then
  $\mathcal{M}^A_h(xy) = \mathcal{M}^B_h(xy)$, with $\mathcal{M}$ as in \cref{def:mistake-set}. -/)
  (proof := /-- A round $k$ belongs to $\mathcal{M}^A_h(xy)$ iff $k < |xy|$ and the prediction
  $A(xy_{:k}, x_k)$ is a mistake against $h$ at $(x_k,y_k)$, by \cref{def:mistake-set}. For each
  such $k$ the hypothesis gives $A(xy_{:k}) = B(xy_{:k})$, so the mistake condition for $A$ and for
  $B$ at round $k$ coincide; hence the two mistake sets are equal. -/)
  (title := /-- Mistake sets depend only on predictions on proper prefixes -/)
  (latexEnv := "lemma")]
lemma mistake_set_prefix_congr {X Y : Type*} (A B : learner X Y) (h : X → Set Y)
    (xy : List (X × Y)) (hAB : ∀ k, k < xy.length → A (xy.take k) = B (xy.take k)) :
    mistake_set A h xy = mistake_set B h xy := by
  ext k
  simp only [mistake_set, Set.mem_setOf_eq]
  constructor
  · rintro ⟨p, hp, hcond⟩
    have hlt : k < xy.length := (List.getElem?_eq_some_iff.1 hp).1
    rw [← hAB k hlt]; exact ⟨p, hp, hcond⟩
  · rintro ⟨p, hp, hcond⟩
    have hlt : k < xy.length := (List.getElem?_eq_some_iff.1 hp).1
    rw [hAB k hlt]; exact ⟨p, hp, hcond⟩

@[blueprint "lem:aoa-weight-prefix-congr"
  (statement := /-- Let $A, B$ be deterministic learners, $h : X \to 2^Y$ and
  $xy \in (X \times Y)^*$. If $A$ and $B$ agree on every proper prefix of $xy$, then
  $w^{xy}_A(h) = w^{xy}_B(h)$, with $w^{\cdot}_{\cdot}$ as in \cref{def:aoa-weight}. -/)
  (proof := /-- By \cref{def:aoa-weight} the weight is the cardinality of the mistake set, which is
  unchanged under the hypothesis by \cref{lem:mistake-set-prefix-congr}. -/)
  (title := /-- The mistake weight depends only on predictions on proper prefixes -/)
  (latexEnv := "lemma")]
lemma aoa_weight_prefix_congr {X Y : Type*} (A B : learner X Y) (h : X → Set Y)
    (xy : List (X × Y)) (hAB : ∀ k, k < xy.length → A (xy.take k) = B (xy.take k)) :
    aoa_weight A xy h = aoa_weight B xy h := by
  rw [aoa_weight, aoa_weight, mistake_set_prefix_congr A B h xy hAB]

@[blueprint "lem:aoa-weight-le"
  (statement := /-- Let $A$ be a deterministic learner, $h : X \to 2^Y$ and
  $xy \in (X \times Y)^*$. Then $w^{xy}_A(h) \le |xy|$, with $w^{\cdot}_A$ as in
  \cref{def:aoa-weight}. -/)
  (proof := /-- By \cref{def:aoa-weight} the weight equals $|\mathcal{M}^A_h(xy)|$, which is at
  most $|xy|$ by \cref{lem:mistake-ncard-le-length}. -/)
  (title := /-- The mistake weight is bounded by the trace length -/)
  (latexEnv := "lemma")]
lemma aoa_weight_le {X Y : Type*} (A : learner X Y) (h : X → Set Y) (xy : List (X × Y)) :
    aoa_weight A xy h ≤ xy.length := mistake_ncard_le_length A h xy

@[blueprint "lem:mistake-inc-le"
  (statement := /-- Let $\alpha \subseteq Y$, $h : X \to 2^Y$, $x \in X$ and $y \in Y$. Then the
  one-round mistake increment satisfies $\mathrm{inc}(\alpha,h,x,y) \le 1$, with $\mathrm{inc}$ as
  in \cref{def:mistake-inc}. -/)
  (proof := /-- By \cref{def:mistake-inc} the increment is either $1$ or $0$, so it is at most $1$.
  -/)
  (title := /-- The one-round mistake increment is at most one -/)
  (latexEnv := "lemma")]
lemma mistake_inc_le {X Y : Type*} (α : Set Y) (h : X → Set Y) (x : X) (y : Y) :
    mistake_inc α h x y ≤ 1 := by
  rw [mistake_inc]; split_ifs <;> omega

@[blueprint "lem:le-tree-rank-weighted"
  (statement := /-- Let $T$ be an ambiguous shattered $\mathcal{G}$-tree, $w$ a weight and
  $r \in \mathbb{N}$. If $r \le |R_T(u)| + w(\mathbf{h}_u)$ for every leaf $u$ of $T$, then
  $r \le \mathrm{rank}_w(T)$, with $R_T$ as in \cref{def:relevant-edges} and $\mathrm{rank}_w$ as
  in \cref{def:tree-rank-weighted}. -/)
  (proof := /-- By \cref{def:tree-rank-weighted} the rank is the infimum over leaves of
  $|R_T(u)| + w(\mathbf{h}_u)$, over the non-empty leaf set of \cref{lem:tree-leaves-nonempty}. A
  lower bound of every element of a non-empty set of natural numbers is at most its infimum, so
  $r \le \mathrm{rank}_w(T)$. -/)
  (title := /-- A uniform leaf lower bound bounds the weighted rank -/)
  (latexEnv := "lemma")]
lemma le_tree_rank_weighted {X Y : Type*} {G : Set (X → Set Y)} (T : ambiguous_tree G)
    (w : (X → Set Y) → ℕ) (r : ℕ)
    (h : ∀ u ∈ tree_leaves T, r ≤ (relevant_edges T u).ncard + w (T.hyp u)) :
    r ≤ tree_rank_weighted T w := by
  rw [tree_rank_weighted]
  apply le_csInf (Set.Nonempty.image _ (tree_leaves_nonempty T))
  rintro b ⟨u, hu, rfl⟩
  exact h u hu

@[blueprint "lem:tree-rank-weighted-le-leaf"
  (statement := /-- Let $T$ be an ambiguous shattered $\mathcal{G}$-tree, $w$ a weight and $u$ a
  leaf of $T$. Then $\mathrm{rank}_w(T) \le |R_T(u)| + w(\mathbf{h}_u)$, with $\mathrm{rank}_w$ as
  in \cref{def:tree-rank-weighted} and $R_T$ as in \cref{def:relevant-edges}. -/)
  (proof := /-- By \cref{def:tree-rank-weighted} the rank is the infimum over the leaves of
  $|R_T(v)| + w(\mathbf{h}_v)$, and the value at the particular leaf $u$ belongs to that set; an
  infimum of natural numbers is at most any element of the set. -/)
  (title := /-- The weighted rank is at most any leaf value -/)
  (latexEnv := "lemma")]
lemma tree_rank_weighted_le_leaf {X Y : Type*} {G : Set (X → Set Y)} (T : ambiguous_tree G)
    (w : (X → Set Y) → ℕ) {u : List Y} (hu : u ∈ tree_leaves T) :
    tree_rank_weighted T w ≤ (relevant_edges T u).ncard + w (T.hyp u) :=
  Nat.sInf_le ⟨u, hu, rfl⟩

@[blueprint "lem:mistake-inc-eq-zero-or-one"
  (statement := /-- Let $\alpha \subseteq Y$, $h : X \to 2^Y$, $x \in X$ and $y \in Y$. Then the
  one-round mistake increment of \cref{def:mistake-inc} is $0$ or $1$; it equals $1$ iff
  $y \notin \alpha$ or $\alpha \not\subseteq h(x)$, and $0$ otherwise. -/)
  (proof := /-- By \cref{def:mistake-inc} the increment is defined as $1$ when
  $y \notin \alpha$ or $\alpha \not\subseteq h(x)$ and $0$ otherwise, from which both claims are
  immediate. -/)
  (title := /-- Value of the one-round mistake increment -/)
  (latexEnv := "lemma")]
lemma mistake_inc_eq_zero_or_one {X Y : Type*} (α : Set Y) (h : X → Set Y) (x : X) (y : Y) :
    (mistake_inc α h x y = 0 ∧ ¬ (y ∉ α ∨ ¬ α ⊆ h x)) ∨
      (mistake_inc α h x y = 1 ∧ (y ∉ α ∨ ¬ α ⊆ h x)) := by
  classical
  rw [mistake_inc]
  by_cases hcond : (y ∉ α ∨ ¬ α ⊆ h x)
  · right; rw [if_pos hcond]; exact ⟨rfl, hcond⟩
  · left; rw [if_neg hcond]; exact ⟨rfl, hcond⟩

@[blueprint "def:aoa-objective"
  (statement := /-- Let $\mathcal{H} \subseteq \{X \to 2^Y\}$, let $m \in \mathbb{N}$, let
  $w : \{X \to 2^Y\} \to \mathbb{N}$ be a weight, let $xy \in (X \times Y)^*$ be a trace and let
  $x \in X$. The *one-round objective at prediction $\alpha \subseteq Y$* is
  \[ \Phi(\alpha) := \max_{y \in Y} \mathrm{AL}_{w + \mathrm{inc}(\alpha,\cdot,x,y)}
  \left(\mathcal{H}^{xy(x,y)}_{\mathrm{uf}}, m\right), \]
  the maximum being taken over the finite label set $Y$ with $\max \emptyset = 0$, with $\mathrm{AL}_w$
  as in \cref{def:al-dim-weighted}, $\mathcal{H}^{\cdot}_{\mathrm{uf}}$ as in \cref{def:unfalsified}
  and $\mathrm{inc}$ as in \cref{def:mistake-inc}. -/)
  (title := /-- One-round min-max objective -/)
  (latexEnv := "definition")]
noncomputable def aoa_objective {X Y : Type*} [Fintype Y] (H : Set (X → Set Y)) (m : ℕ)
    (w : (X → Set Y) → ℕ) (xy : List (X × Y)) (x : X) (α : Set Y) : ℕ :=
  Finset.univ.sup fun y : Y =>
    al_dim_weighted (unfalsified H (xy ++ [(x, y)])) (fun h => w h + mistake_inc α h x y) m

@[blueprint "lem:one-step-drop"
  (statement := /-- Let $\mathcal{G} \subseteq \{X \to 2^Y\}$ with $Y$ finite, let
  $w : \{X \to 2^Y\} \to \mathbb{N}$ be a weight bounded by $B$ on $\mathcal{G}$, let $x \in X$, let
  $n \ge 1$ and $r \ge 1$. Suppose that for every prediction $\alpha \subseteq Y$,
  \[ r \le \max_{y \in Y} \mathrm{AL}_{w + \mathrm{inc}(\alpha,\cdot,x,y)}
  \left(\{h \in \mathcal{G} \mid y \in h(x)\}, n-1\right). \]
  Then $r \le \mathrm{AL}_w(\mathcal{G}, n)$, with $\mathrm{AL}_w$ as in \cref{def:al-dim-weighted}
  and $\mathrm{inc}$ as in \cref{def:mistake-inc}. -/)
  (proof := /-- Since $r \ge 1$ and the maximum over an empty label set is $0$, the label set $Y$ is
  non-empty. For each $\alpha$ the maximum over the finite set $Y$ is attained, so there is a label
  $y^\alpha$ with $\mathrm{AL}_{w + \mathrm{inc}(\alpha,\cdot,x,y^\alpha)}(\{h \in \mathcal{G} \mid
  y^\alpha \in h(x)\}, n-1) \ge r$; the weight $w + \mathrm{inc}$ is bounded by $B+1$ on the
  subclass by \cref{lem:mistake-inc-le}, so by \cref{lem:exists-tree-of-le-al-dim} there is an
  ambiguous shattered $\{h \in \mathcal{G} \mid y^\alpha \in h(x)\}$-tree $T^\alpha$, reinterpreted
  over $\mathcal{G}$ by \cref{def:tree-coe} and \cref{lem:tree-coe-eq}, of depth at most $n-1$ whose
  $(w + \mathrm{inc}(\alpha,\cdot,x,y^\alpha))$-weighted rank is at least $r$, and each of whose
  leaf hypotheses $h$ satisfies $y^\alpha \in h(x)$.

  Set $\hat{\alpha} := \{y \mid \exists \alpha,\ y = y^\alpha \text{ and } y \notin \alpha\}$ and
  $\hat{y} := y^{\hat{\alpha}}$. Then $\hat{y} \in \hat{\alpha}$: otherwise $\alpha := \hat{\alpha}$
  would witness $\hat{y} \in \hat{\alpha}$, a contradiction. Take as children the labels of
  $\hat{\alpha}$, with $\hat{y}$ the default one, and under the edge $c$ hang the subtree
  $T^{\mathrm{pr}(c)}$ where $\mathrm{pr}(\hat{y}) := \hat{\alpha}$ and, for $c \in \hat{\alpha}$
  with $c \neq \hat{y}$, $\mathrm{pr}(c)$ is a witness with $c = y^{\mathrm{pr}(c)}$ and $c \notin
  \mathrm{pr}(c)$; in all cases $y^{\mathrm{pr}(c)} = c$. Form the join tree of \cref{def:join-tree}
  with root instance $x$; the compatibility hypothesis holds because each leaf hypothesis $h$ of the
  $c$-subtree satisfies $c \in h(x)$. By \cref{lem:join-depth-le} its depth is at most $n$.

  For its rank, consider a leaf $c \cdot v$ with leaf hypothesis $h$, so $v$ is a leaf of the
  $c$-subtree by \cref{lem:join-leaf-iff} and by \cref{lem:tree-rank-weighted-le-leaf} together
  with the rank bound
  $r \le |R_{c}(v)| + w(h) + \mathrm{inc}(\mathrm{pr}(c),h,x,c)$, where $R_c$ denotes the
  relevant-edge set of the $c$-subtree. The increment $\mathrm{inc}(\mathrm{pr}(c),h,x,c)$ is
  either $0$ or $1$ by \cref{lem:mistake-inc-eq-zero-or-one}. If $\mathrm{inc}(\mathrm{pr}(c),h,x,c) = 0$ then
  $r \le |R_c(v)| + w(h) \le |R(c \cdot v)| + w(h)$ by \cref{lem:join-relevant-ge-base}. If
  $\mathrm{inc} = 1$ then the root edge of $c \cdot v$ is relevant: for $c \neq \hat{y}$ it is
  non-default by \cref{lem:join-relevant-zero-mem}; for $c = \hat{y}$, since $\hat{y} \in
  \hat{\alpha}$ the increment forces $\hat{\alpha} \not\subseteq h(x)$, giving a child $z \in
  \hat{\alpha}$ with $z \notin h(x)$ and hence relevance by \cref{lem:join-relevant-zero-mem'}. In
  either case \cref{lem:join-relevant-ge-succ} gives $|R(c \cdot v)| \ge |R_c(v)| + 1$, so
  $|R(c \cdot v)| + w(h) \ge |R_c(v)| + 1 + w(h) \ge r$. By \cref{lem:le-tree-rank-weighted} the
  join tree has $w$-weighted rank at least $r$, and by \cref{lem:le-al-dim-weighted} we conclude
  $r \le \mathrm{AL}_w(\mathcal{G}, n)$. -/)
  (title := /-- One-round min-max drop of the weighted dimension -/)
  (latexEnv := "lemma")]
lemma one_step_drop {X Y : Type*} [Fintype Y] (G : Set (X → Set Y)) (w : (X → Set Y) → ℕ)
    (B : ℕ) (hB : ∀ h ∈ G, w h ≤ B) (x : X) (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r)
    (hmax : ∀ α : Set Y, r ≤ Finset.univ.sup
      (fun y : Y => al_dim_weighted {h ∈ G | y ∈ h x}
        (fun h => w h + mistake_inc α h x y) (n - 1))) :
    r ≤ al_dim_weighted G w n := by
  classical
  haveI hYne : Nonempty Y := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    haveI := hcon
    have hz := hmax ∅
    simp only [Finset.univ_eq_empty, Finset.sup_empty, Nat.bot_eq_zero, Nat.le_zero] at hz
    omega
  have hwit : ∀ α : Set Y, ∃ (y : Y) (T : ambiguous_tree G),
      tree_depth T ≤ n - 1 ∧ (∀ v ∈ tree_leaves T, y ∈ T.hyp v x) ∧
        r ≤ tree_rank_weighted T (fun h => w h + mistake_inc α h x y) := by
    intro α
    obtain ⟨y, -, hy⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      (fun y : Y => al_dim_weighted {h ∈ G | y ∈ h x}
        (fun h => w h + mistake_inc α h x y) (n - 1))
    have hry : r ≤ al_dim_weighted {h ∈ G | y ∈ h x}
        (fun h => w h + mistake_inc α h x y) (n - 1) := by
      rw [← hy]; exact hmax α
    have hBsub : ∀ h ∈ {h ∈ G | y ∈ h x}, (fun h => w h + mistake_inc α h x y) h ≤ B + 1 := by
      rintro h ⟨hhG, -⟩
      have hwB := hB h hhG
      have hiB := mistake_inc_le α h x y
      show w h + mistake_inc α h x y ≤ B + 1
      omega
    obtain ⟨T0, hd0, hrank0⟩ :=
      exists_tree_of_le_al_dim (fun h => w h + mistake_inc α h x y) (B + 1) (n - 1) r hBsub hr hry
    refine ⟨y, tree_coe (Set.sep_subset G _) T0, ?_, ?_, ?_⟩
    · obtain ⟨-, -, hdep, -⟩ := tree_coe_eq (Set.sep_subset G _) T0 (fun h => w h + mistake_inc α h x y)
      rw [hdep]; exact hd0
    · intro v hv
      obtain ⟨hleaf, -, -, -⟩ := tree_coe_eq (Set.sep_subset G _) T0 (fun h => w h + mistake_inc α h x y)
      rw [hleaf] at hv
      have := T0.leaf_hyp_mem v hv.1 hv.2
      exact this.2
    · obtain ⟨-, -, -, hrank⟩ := tree_coe_eq (Set.sep_subset G _) T0 (fun h => w h + mistake_inc α h x y)
      rw [hrank]; exact hrank0
  choose yy TT hTTd hTTleaf hTTrank using hwit
  set Ah : Set Y := {y | ∃ α : Set Y, y = yy α ∧ y ∉ α} with hAhdef
  set yhat : Y := yy Ah with hyhatdef
  have hyhat_mem : yhat ∈ Ah := by
    by_contra hcon
    exact hcon ⟨Ah, hyhatdef, hcon⟩
  set pr : Y → Set Y := fun c =>
    if hc : c ∈ Ah then (if c = yhat then Ah else hc.choose) else Ah with hprdef
  have hpr_yhat : pr yhat = Ah := by
    simp only [hprdef, dif_pos hyhat_mem, if_pos rfl, if_true]
  have hyyc : ∀ c ∈ Ah, yy (pr c) = c := by
    intro c hc
    simp only [hprdef, dif_pos hc]
    by_cases hcy : c = yhat
    · rw [if_pos hcy, ← hyhatdef]; exact hcy.symm
    · rw [if_neg hcy]; exact (hc.choose_spec.1).symm
  set sub : Y → ambiguous_tree G := fun c => TT (pr c) with hsubdef
  set C : Finset Y := (Set.toFinite Ah).toFinset with hCdef
  have hCmem : ∀ y, y ∈ C ↔ y ∈ Ah := by
    intro y; rw [hCdef]; exact Set.Finite.mem_toFinset _
  have hdC : yhat ∈ C := (hCmem yhat).2 hyhat_mem
  have hcompat : ∀ y ∈ C, ∀ v ∈ tree_leaves (sub y), y ∈ (sub y).hyp v x := by
    intro c hcC v hv
    have hcAh := (hCmem c).1 hcC
    have h1 := hTTleaf (pr c) v hv
    rw [hsubdef]
    rw [hyyc c hcAh] at h1
    exact h1
  refine le_al_dim_weighted w B n hB (join_tree x C yhat hdC sub hcompat) ?_ |>.trans' ?_
  ·
    have hdep : ∀ y ∈ C, tree_depth (sub y) ≤ n - 1 := by
      intro c hcC
      rw [hsubdef]; exact hTTd (pr c)
    have := join_depth_le x C yhat hdC sub hcompat (n - 1) hdep
    omega
  ·
    apply le_tree_rank_weighted
    intro u hu
    rw [join_leaf_iff] at hu
    obtain ⟨c, hcC, v, hvleaf, rfl⟩ := hu
    have hcAh := (hCmem c).1 hcC
    set h := (sub c).hyp v with hhdef
    have hrankleaf : r ≤ (relevant_edges (sub c) v).ncard + w h + mistake_inc (pr c) h x c := by
      have hle := tree_rank_weighted_le_leaf (sub c) (fun hh => w hh + mistake_inc (pr c) hh x c)
        hvleaf
      have hr2 : r ≤ tree_rank_weighted (sub c) (fun hh => w hh + mistake_inc (pr c) hh x c) := by
        have hraw := hTTrank (pr c)
        rw [hyyc c hcAh] at hraw
        simp only [hsubdef]; exact hraw
      have : r ≤ (relevant_edges (sub c) v).ncard + (w h + mistake_inc (pr c) h x c) :=
        hr2.trans hle
      omega
    have hjoinhyp : (join_tree x C yhat hdC sub hcompat).hyp (c :: v) = h := rfl
    rw [hjoinhyp]
    rcases mistake_inc_eq_zero_or_one (pr c) h x c with ⟨hinc0, -⟩ | ⟨hinc1, hcond⟩
    ·
      have hbase := join_relevant_ge_base x C yhat hdC sub hcompat c hcC v
      rw [hinc0] at hrankleaf
      omega
    ·
      have hzero : 0 ∈ relevant_edges (join_tree x C yhat hdC sub hcompat) (c :: v) := by
        by_cases hcy : c = yhat
        ·
          subst hcy
          rw [hpr_yhat] at hcond
          have hncon : ¬ Ah ⊆ h x := by
            rcases hcond with hov | hun
            · exact absurd hyhat_mem hov
            · exact hun
          obtain ⟨z, hzAh, hznot⟩ := Set.not_subset.1 hncon
          exact join_relevant_zero_mem' x C yhat hdC sub hcompat yhat v z ((hCmem z).2 hzAh) hznot
        ·
          exact join_relevant_zero_mem x C yhat hdC sub hcompat c v hcy
      have hsucc := join_relevant_ge_succ x C yhat hdC sub hcompat c hcC v hzero
      rw [hinc1] at hrankleaf
      omega

@[blueprint "def:finite-argmin"
  (statement := /-- Let $\alpha$ be a finite non-empty type and $f : \alpha \to \mathbb{N}$. The
  predicate $\mathrm{argmin}(f)$ asserts the existence of a point $a_0$ with $f(a_0) \le f(a)$ for
  every $a$, a minimiser of $f$ over the finite type. -/)
  (title := /-- Existence of a minimiser on a finite type -/)
  (latexEnv := "definition")]
def finite_argmin {α : Type*} [Fintype α] [Nonempty α] (f : α → ℕ) :
    ∃ a0 : α, ∀ a, f a0 ≤ f a := by
  classical
  obtain ⟨a, -, ha⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  exact ⟨a, fun a' => ha a' (Finset.mem_univ _)⟩

@[blueprint "def:aoa-learner"
  (statement := /-- Let $\mathcal{H} \subseteq \{X \to 2^Y\}$ with $Y$ finite and let
  $N \in \mathbb{N}$. The *ambiguous optimal algorithm* $A^\star$ is the deterministic learner of
  \cref{def:learner} defined by well-founded recursion on the length of the trace: on a trace
  $xy \in (X \times Y)^*$ and instance $x \in X$ it predicts a set $\alpha \subseteq Y$ minimising
  the one-round objective $\Phi(\alpha)$ of \cref{def:aoa-objective} with weight $w^{xy}_{A^\star}$
  and depth parameter $N - (|xy|+1)$, where $w^{xy}_{A^\star}$ of \cref{def:aoa-weight} depends only
  on the values of $A^\star$ on proper prefixes of $xy$, so that the recursion is well founded. The
  minimiser exists because $2^Y$ is a finite non-empty type. -/)
  (title := /-- Ambiguous optimal algorithm -/)
  (latexEnv := "definition")]
noncomputable def aoa_learner {X Y : Type*} [Fintype Y] (H : Set (X → Set Y)) (N : ℕ) :
    learner X Y :=
  (measure (fun xy : List (X × Y) => xy.length)).wf.fix
    (fun xy rec x =>
      Classical.choose (finite_argmin
        (fun α : Set Y =>
          Finset.univ.sup (fun y : Y =>
            al_dim_weighted (unfalsified H (xy ++ [(x, y)]))
              (fun h =>
                aoa_weight
                  (fun xy' x' => if hh : xy'.length < xy.length then rec xy' hh x' else ∅) xy h
                  + mistake_inc α h x y)
              (N - (xy.length + 1))))))

@[blueprint "lem:aoa-learner-spec"
  (statement := /-- Let $\mathcal{H} \subseteq \{X \to 2^Y\}$ with $Y$ finite, let $N \in
  \mathbb{N}$, let $A^\star$ be the ambiguous optimal algorithm of \cref{def:aoa-learner}, let
  $xy \in (X \times Y)^*$ and $x \in X$. Then the prediction $A^\star(xy,x)$ minimises the one-round
  objective $\Phi$ of \cref{def:aoa-objective} with weight $w^{xy}_{A^\star}$ and depth parameter
  $N - (|xy|+1)$: for every $\beta \subseteq Y$,
  \[ \Phi\left(A^\star(xy,x)\right) \le \Phi(\beta), \]
  with $w^{\cdot}_{\cdot}$ as in \cref{def:aoa-weight}. -/)
  (proof := /-- By the fixed-point equation of well-founded recursion, $A^\star(xy,x)$ equals the
  chosen minimiser of the objective built from the restriction of $A^\star$ to proper prefixes of
  $xy$. By \cref{lem:aoa-weight-prefix-congr} the weight $w^{xy}$ computed from that restriction
  agrees with $w^{xy}_{A^\star}$, since $w^{xy}$ of \cref{def:aoa-weight} depends only on the
  values on proper prefixes and every proper prefix $xy_{:k}$ with $k < |xy|$ has length $k <
  |xy|$. Hence the objective coincides with $\Phi$ of \cref{def:aoa-objective}, and the defining
  property of the chosen minimiser is exactly the stated inequality. -/)
  (title := /-- The ambiguous optimal algorithm minimises the one-round objective -/)
  (latexEnv := "lemma")]
lemma aoa_learner_spec {X Y : Type*} [Fintype Y] (H : Set (X → Set Y)) (N : ℕ)
    (xy : List (X × Y)) (x : X) (β : Set Y) :
    aoa_objective H (N - (xy.length + 1)) (aoa_weight (aoa_learner H N) xy) xy x
        (aoa_learner H N xy x) ≤
      aoa_objective H (N - (xy.length + 1)) (aoa_weight (aoa_learner H N) xy) xy x β := by
  classical
  have hweq : aoa_weight
      (fun xy' x' => if hh : xy'.length < xy.length then aoa_learner H N xy' x' else ∅) xy =
      aoa_weight (aoa_learner H N) xy := by
    funext h
    apply aoa_weight_prefix_congr
    intro k hk
    have hlt : (xy.take k).length < xy.length := by
      rw [List.length_take]; omega
    simp only [dif_pos hlt]
  have hfix : aoa_learner H N xy x =
      Classical.choose (finite_argmin
        (fun α : Set Y =>
          Finset.univ.sup (fun y : Y =>
            al_dim_weighted (unfalsified H (xy ++ [(x, y)]))
              (fun h =>
                aoa_weight
                  (fun xy' x' => if hh : xy'.length < xy.length then aoa_learner H N xy' x'
                    else ∅) xy h
                  + mistake_inc α h x y)
              (N - (xy.length + 1))))) := by
    conv_lhs => rw [aoa_learner, WellFounded.fix_eq]
    rfl
  have hAeq : aoa_learner H N xy x =
      Classical.choose (finite_argmin
        (fun α : Set Y =>
          Finset.univ.sup (fun y : Y =>
            al_dim_weighted (unfalsified H (xy ++ [(x, y)]))
              (fun h => aoa_weight (aoa_learner H N) xy h + mistake_inc α h x y)
              (N - (xy.length + 1))))) := by
    rw [hfix, hweq]
  set f : Set Y → ℕ := fun α : Set Y =>
    Finset.univ.sup (fun y : Y =>
      al_dim_weighted (unfalsified H (xy ++ [(x, y)]))
        (fun h => aoa_weight (aoa_learner H N) xy h + mistake_inc α h x y)
        (N - (xy.length + 1))) with hfdef
  have hspec := Classical.choose_spec (finite_argmin f)
  have hAeq' : aoa_learner H N xy x = Classical.choose (finite_argmin f) := hAeq
  rw [hAeq']
  show f (Classical.choose (finite_argmin f)) ≤ f β
  exact hspec β

@[blueprint "lem:aoa-one-step"
  (statement := /-- Let $\mathcal{H} \subseteq \{X \to 2^Y\}$ with $Y$ finite and let
  $N \in \mathbb{N}$. Then there exists a deterministic learner $A$ as in \cref{def:learner}
  satisfying the ambiguous-optimal-algorithm invariant for horizon $N$ of
  \cref{def:aoa-invariant}: for every $k < N$, every
  $\overline{xy} \in \mathcal{C}_{\mathcal{H}}(k)$, every $x^* \in X$ and every $y^* \in Y$ with
  $\overline{xy}x^*y^* \in \mathcal{C}_{\mathcal{H}}(k+1)$,
  \[ \mathrm{AL}_{w^{\overline{xy}x^*y^*}_A}\left(\mathcal{H}^{\overline{xy}x^*y^*}_{\mathrm{uf}},
  N-(k+1)\right) \le \mathrm{AL}_{w^{\overline{xy}}_A}\left(\mathcal{H}^{\overline{xy}}_{\mathrm{uf}},
  N-k\right). \] -/)
  (proof := /-- Take $A$ to be the ambiguous optimal learner of \cref{def:aoa-learner}, which on a
  trace $\overline{xy}$ and instance $x^*$ predicts a set achieving
  \[ \min_{\alpha \in 2^Y} \max_{y \in Y}
  \mathrm{AL}_{w^{\overline{xy}}_A + \mathrm{inc}(\alpha,\cdot,x^*,y)}
  \left(\{h \in \mathcal{H}^{\overline{xy}}_{\mathrm{uf}} \mid y \in h(x^*)\}, N-(k+1)\right); \]
  we verify it satisfies the invariant of \cref{def:aoa-invariant}. Fix $k < N$, a trace
  $\overline{xy} \in \mathcal{C}_{\mathcal{H}}(k)$, an instance $x^*$ and a label $y^*$ with
  $\overline{xy}x^*y^* \in \mathcal{C}_{\mathcal{H}}(k+1)$, and write $m := |\overline{xy}| = k$.

  By \cref{lem:aoa-weight-append} the extended weight satisfies
  $w^{\overline{xy}x^*y^*}_A(h) = w^{\overline{xy}}_A(h) + \mathrm{inc}(A(\overline{xy},x^*),h,x^*,y^*)$
  for every $h$, so the left-hand side of the invariant equals
  $\mathrm{AL}_{w^{\overline{xy}}_A + \mathrm{inc}(\alpha,\cdot,x^*,y^*)}
  (\mathcal{H}^{\overline{xy}x^*y^*}_{\mathrm{uf}}, N-(k+1))$ with $\alpha := A(\overline{xy},x^*)$.
  Bounding this single term $y^*$ by the maximum over all labels, it is at most the objective value
  \[ r := \max_{y \in Y}
  \mathrm{AL}_{w^{\overline{xy}}_A + \mathrm{inc}(\alpha,\cdot,x^*,y)}
  \left(\mathcal{H}^{\overline{xy}x^*y}_{\mathrm{uf}}, N-(k+1)\right) \]
  attained by the prediction $\alpha$. It therefore suffices to show
  $r \le \mathrm{AL}_{w^{\overline{xy}}_A}(\mathcal{H}^{\overline{xy}}_{\mathrm{uf}}, N-k)$.

  If $r = 0$ this is immediate. Otherwise $r \ge 1$, and we apply \cref{lem:one-step-drop} with the
  class $\mathcal{H}^{\overline{xy}}_{\mathrm{uf}}$, the weight $w^{\overline{xy}}_A$, the bound
  $m$ (valid since $w^{\overline{xy}}_A(h) \le |\overline{xy}| = m$ for every unfalsified $h$ by
  \cref{lem:aoa-weight-le}), the instance $x^*$, horizon $N-k$ and value $r$. Its hypothesis is that
  for every prediction $\beta \in 2^Y$,
  \[ r \le \max_{y \in Y} \mathrm{AL}_{w^{\overline{xy}}_A + \mathrm{inc}(\beta,\cdot,x^*,y)}
  \left(\{h \in \mathcal{H}^{\overline{xy}}_{\mathrm{uf}} \mid y \in h(x^*)\}, N-k-1\right). \]
  This holds because $\alpha$ minimises the objective of \cref{def:aoa-objective}, so by
  \cref{lem:aoa-learner-spec} the objective value at $\alpha$ is at most its value at $\beta$, and by
  \cref{lem:unfalsified-append} the class $\mathcal{H}^{\overline{xy}x^*y}_{\mathrm{uf}}$ equals
  $\{h \in \mathcal{H}^{\overline{xy}}_{\mathrm{uf}} \mid y \in h(x^*)\}$, identifying the two
  maxima. Thus \cref{lem:one-step-drop} yields
  $r \le \mathrm{AL}_{w^{\overline{xy}}_A}(\mathcal{H}^{\overline{xy}}_{\mathrm{uf}}, N-k)$, which
  completes the proof. -/)
  (title := /-- One-step minimax invariant for the ambiguous optimal algorithm -/)
  (latexEnv := "lemma")]
lemma aoa_one_step {X Y : Type*} [Fintype Y] (H : Set (X → Set Y)) (N : ℕ) :
    ∃ A : learner X Y, aoa_invariant H N A := by
  classical
  refine ⟨aoa_learner H N, ?_⟩
  intro k hk xy hxy x y hxy'
  set A := aoa_learner H N with hAdef
  obtain ⟨h0, hh0, hlen, hcomp0⟩ := hxy
  subst k
  set m := xy.length with hm
  have hLHS : al_dim_weighted (unfalsified H (xy ++ [(x, y)]))
        (aoa_weight A (xy ++ [(x, y)])) (N - (m + 1)) =
      al_dim_weighted (unfalsified H (xy ++ [(x, y)]))
        (fun h => aoa_weight A xy h + mistake_inc (A xy x) h x y) (N - (m + 1)) := by
    congr 1
    funext h
    exact aoa_weight_append A h xy x y
  rw [hLHS]
  set r := aoa_objective H (N - (m + 1)) (aoa_weight A xy) xy x (A xy x) with hrdef
  have hLE : al_dim_weighted (unfalsified H (xy ++ [(x, y)]))
      (fun h => aoa_weight A xy h + mistake_inc (A xy x) h x y) (N - (m + 1)) ≤ r := by
    rw [hrdef, aoa_objective]
    apply Finset.le_sup (b := y)
    exact Finset.mem_univ y
  refine le_trans hLE ?_
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · rw [hr0]; exact Nat.zero_le _
  · have hB : ∀ h ∈ unfalsified H xy, aoa_weight A xy h ≤ m := by
      intro h _; rw [hm]; exact aoa_weight_le A h xy
    have hmax : ∀ α : Set Y, r ≤ Finset.univ.sup (fun yy : Y =>
        al_dim_weighted {h ∈ unfalsified H xy | yy ∈ h x}
          (fun h => aoa_weight A xy h + mistake_inc α h x yy) (N - m - 1)) := by
      intro α
      have hspec := aoa_learner_spec H N xy x α
      rw [← hAdef] at hspec
      have heq : aoa_objective H (N - (m + 1)) (aoa_weight A xy) xy x α =
          Finset.univ.sup (fun yy : Y =>
            al_dim_weighted {h ∈ unfalsified H xy | yy ∈ h x}
              (fun h => aoa_weight A xy h + mistake_inc α h x yy) (N - m - 1)) := by
        rw [aoa_objective]
        apply Finset.sup_congr rfl
        intro yy _
        rw [unfalsified_append, show N - (m + 1) = N - m - 1 from by omega]
      calc r ≤ aoa_objective H (N - (m + 1)) (aoa_weight A xy) xy x α := hspec
        _ = _ := heq
    have hfinal := one_step_drop (unfalsified H xy) (aoa_weight A xy) m hB x (N - m) r
      (by omega) hrpos hmax
    simpa using hfinal

@[blueprint "lem:aoa-chain"
  (statement := /-- Let $\mathcal{H} \subseteq \{X \to 2^Y\}$, let $N \in \mathbb{N}$ and let $A$ be
  a deterministic learner satisfying the ambiguous-optimal-algorithm invariant for horizon $N$ of
  \cref{def:aoa-invariant}. Then for every trace
  $\overline{xy} \in \mathcal{C}_{\mathcal{H}}(N)$,
  \[ \mathrm{AL}_{w^{\overline{xy}}_A}\left(\mathcal{H}^{\overline{xy}}_{\mathrm{uf}},0\right)
  \le \mathrm{AL}(\mathcal{H},N), \]
  with $w^{\cdot}_A$ as in \cref{def:aoa-weight}, $\mathcal{H}^{\cdot}_{\mathrm{uf}}$ as in
  \cref{def:unfalsified}, $\mathrm{AL}_w$ as in \cref{def:al-dim-weighted} and $\mathrm{AL}$ as in
  \cref{def:al-dim}. -/)
  (proof := /-- We prove, by induction on $j \le N$, that for every
  $\overline{xy} \in \mathcal{C}_{\mathcal{H}}(j)$,
  \[ \mathrm{AL}_{w^{\overline{xy}}_A}\left(\mathcal{H}^{\overline{xy}}_{\mathrm{uf}}, N-j\right)
  \le \mathrm{AL}_{w^{\varepsilon}_A}\left(\mathcal{H}^{\varepsilon}_{\mathrm{uf}}, N\right). \]
  For $j = 0$ the only trace of length $0$ is the empty trace $\varepsilon$ and the claim is an
  equality. Assume the claim for $j$ and let $j + 1 \le N$ and
  $\overline{xy}' \in \mathcal{C}_{\mathcal{H}}(j+1)$. Write $\overline{xy}'
  = \overline{xy}x^*y^*$ where $\overline{xy}$ consists of the first $j$ rounds and $(x^*,y^*)$ is
  the last round; then $\overline{xy} \in \mathcal{C}_{\mathcal{H}}(j)$, because a hypothesis
  compatible with all $j+1$ rounds of $\overline{xy}'$ is compatible with its first $j$ rounds.
  Since $j < N$, the invariant of \cref{def:aoa-invariant} applied with $k := j$ gives
  \[ \mathrm{AL}_{w^{\overline{xy}x^*y^*}_A}
  \left(\mathcal{H}^{\overline{xy}x^*y^*}_{\mathrm{uf}}, N-(j+1)\right) \le
  \mathrm{AL}_{w^{\overline{xy}}_A}\left(\mathcal{H}^{\overline{xy}}_{\mathrm{uf}}, N-j\right), \]
  and the induction hypothesis bounds the right-hand side by
  $\mathrm{AL}_{w^{\varepsilon}_A}(\mathcal{H}^{\varepsilon}_{\mathrm{uf}}, N)$, completing the
  induction.

  Applying the claim with $j := N$ to a trace $\overline{xy} \in \mathcal{C}_{\mathcal{H}}(N)$, and
  noting $N - N = 0$, we obtain
  \[ \mathrm{AL}_{w^{\overline{xy}}_A}\left(\mathcal{H}^{\overline{xy}}_{\mathrm{uf}},0\right) \le
  \mathrm{AL}_{w^{\varepsilon}_A}\left(\mathcal{H}^{\varepsilon}_{\mathrm{uf}}, N\right). \]
  It remains to identify the right-hand side with $\mathrm{AL}(\mathcal{H},N)$. On the empty trace
  the mistake set $\mathcal{M}^A_h(\varepsilon)$ is empty for every $h$ by \cref{def:mistake-set},
  since there is no round index $k < 0$; hence $w^{\varepsilon}_A$ is identically $0$ by
  \cref{def:aoa-weight}, and so the weighted rank of \cref{def:tree-rank-weighted} coincides with
  the rank of \cref{def:tree-rank} for every tree. Moreover
  $\mathcal{H}^{\varepsilon}_{\mathrm{uf}} = \mathcal{H}$ by \cref{def:unfalsified}, because the
  compatibility condition of \cref{def:compat-set} on the empty trace is vacuous. Therefore
  $\mathrm{AL}_{w^{\varepsilon}_A}(\mathcal{H}^{\varepsilon}_{\mathrm{uf}}, N) =
  \mathrm{AL}(\mathcal{H},N)$ by \cref{def:al-dim,def:al-dim-weighted}. -/)
  (title := /-- Chaining the invariant over the whole horizon -/)
  (latexEnv := "lemma")]
lemma aoa_chain {X Y : Type*} {H : Set (X → Set Y)} {N : ℕ} {A : learner X Y}
    (hA : aoa_invariant H N A) (xy : List (X × Y)) (hxy : xy ∈ compat_set_class H N) :
    al_dim_weighted (unfalsified H xy) (aoa_weight A xy) 0 ≤ al_dim H N := by
  have hAeq : al_dim H N = al_dim_weighted H (fun _ => 0) N := rfl
  have key : ∀ j : ℕ, j ≤ N → ∀ w ∈ compat_set_class H j,
      al_dim_weighted (unfalsified H w) (aoa_weight A w) (N - j) ≤ al_dim H N := by
    intro j
    induction j with
    | zero =>
      intro _ w hw
      obtain ⟨h, hh, hcompat⟩ := hw
      have hlen : w.length = 0 := hcompat.1
      have hwnil : w = [] := List.length_eq_zero_iff.mp hlen
      subst hwnil
      have e1 : unfalsified H ([] : List (X × Y)) = H := by
        ext g; simp [unfalsified, compat_set]
      have e2 : aoa_weight A ([] : List (X × Y)) = fun _ => 0 := by
        funext g; simp [aoa_weight, mistake_set]
      rw [e1, e2, Nat.sub_zero, hAeq]
    | succ j ih =>
      intro _ w hw
      obtain ⟨h, hh, hcompat⟩ := hw
      have hlen : w.length = j + 1 := hcompat.1
      have hne : w ≠ [] := by
        intro hnil; rw [hnil] at hlen; simp at hlen
      have hstep_eq : w.dropLast ++ [((w.getLast hne).1, (w.getLast hne).2)] = w :=
        List.dropLast_append_getLast hne
      have hprevlen : w.dropLast.length = j := by
        rw [List.length_dropLast, hlen]
        omega
      have hprevcompat : w.dropLast ∈ compat_set h j := by
        refine ⟨hprevlen, ?_⟩
        intro p hp
        exact hcompat.2 p (List.mem_of_mem_dropLast hp)
      have hprevclass : w.dropLast ∈ compat_set_class H j := ⟨h, hh, hprevcompat⟩
      have hjN : j < N := by omega
      have hinv := hA j hjN w.dropLast hprevclass (w.getLast hne).1 (w.getLast hne).2
        (by rw [hstep_eq]; exact ⟨h, hh, hcompat⟩)
      rw [hstep_eq] at hinv
      have hih := ih (le_of_lt hjN) w.dropLast hprevclass
      exact le_trans hinv hih
  have hfinal := key N (le_refl N) xy hxy
  rwa [Nat.sub_self] at hfinal

@[blueprint "lem:weight-le-al-zero"
  (statement := /-- Let $\mathcal{H} \subseteq \{X \to 2^Y\}$, let $A$ be a deterministic learner,
  let $N \in \mathbb{N}$, let $\overline{xy} \in (X \times Y)^*$ be a trace of length $N$ and let
  $h \in \mathcal{H}$ with $\overline{xy} \in \mathcal{C}_h(N)$. Then
  \[ \left|\mathcal{M}^A_h(\overline{xy})\right| \le
  \mathrm{AL}_{w^{\overline{xy}}_A}\left(\mathcal{H}^{\overline{xy}}_{\mathrm{uf}},0\right), \]
  with $\mathcal{M}^A_h$ as in \cref{def:mistake-set}, $w^{\cdot}_A$ as in \cref{def:aoa-weight},
  $\mathcal{H}^{\cdot}_{\mathrm{uf}}$ as in \cref{def:unfalsified} and $\mathrm{AL}_w$ as in
  \cref{def:al-dim-weighted}. -/)
  (proof := /-- If $X$ is empty there is no round to play, so $\mathcal{M}^A_h(\overline{xy})$ is
  empty by \cref{def:mistake-set} and its cardinality is $0$, which is trivially at most the
  right-hand side. So assume $X$ has an element $x_0$.

  Since $h \in \mathcal{H}$ and $\overline{xy} \in \mathcal{C}_h(N)$ with $|\overline{xy}| = N$, we
  have $h \in \mathcal{H}^{\overline{xy}}_{\mathrm{uf}}$ by \cref{def:unfalsified}. Consider the
  one-vertex tree $T_h$ whose vertex set is $\{\varepsilon\}$, with constant instance labelling
  $x_0$, with hypothesis labelling assigning $h$ to the root, and with empty set of default
  vertices. Its vertex set is finite, contains the root and is closed under prefixes; the root has
  no child, so the condition on default children of \cref{def:ambiguous-tree} is vacuous; and the
  root is a leaf whose hypothesis $h$ lies in $\mathcal{H}^{\overline{xy}}_{\mathrm{uf}}$ and is
  vacuously compatible with its empty root path. Hence $T_h$ is an ambiguous shattered
  $\mathcal{H}^{\overline{xy}}_{\mathrm{uf}}$-tree, and $\mathrm{dep}(T_h) = 0$ by
  \cref{def:tree-depth}.

  Its unique leaf is the root, whose relevant-edge set is empty by \cref{def:relevant-edges} since
  the root path has length $0$. Therefore, by \cref{def:tree-rank-weighted} and
  \cref{def:aoa-weight}, the leaf value equals
  \[ |R_{T_h}(\varepsilon)| + w^{\overline{xy}}_A(h) = 0 + w^{\overline{xy}}_A(h) =
  \left|\mathcal{M}^A_h(\overline{xy})\right|, \]
  so $|\mathcal{M}^A_h(\overline{xy})| \le \mathrm{rank}_{w^{\overline{xy}}_A}(T_h)$ by the
  leaf lower bound of \cref{lem:le-tree-rank-weighted}, its unique leaf being the root.

  Finally, the weight $w^{\overline{xy}}_A$ is bounded on
  $\mathcal{H}^{\overline{xy}}_{\mathrm{uf}}$ by $|\overline{xy}|$ by \cref{lem:aoa-weight-le},
  and $\mathrm{dep}(T_h) = 0 \le 0$, so \cref{lem:le-al-dim-weighted} gives
  $\mathrm{rank}_{w^{\overline{xy}}_A}(T_h) \le \mathrm{AL}_{w^{\overline{xy}}_A}
  (\mathcal{H}^{\overline{xy}}_{\mathrm{uf}},0)$. Combining the two inequalities yields
  $|\mathcal{M}^A_h(\overline{xy})| \le \mathrm{AL}_{w^{\overline{xy}}_A}
  (\mathcal{H}^{\overline{xy}}_{\mathrm{uf}},0)$. -/)
  (title := /-- The accumulated mistake count is bounded by the depth-zero weighted dimension -/)
  (latexEnv := "lemma")]
lemma weight_le_al_zero {X Y : Type*} {H : Set (X → Set Y)} (A : learner X Y) {N : ℕ}
    {xy : List (X × Y)} (hlen : xy.length = N) {h : X → Set Y} (hh : h ∈ H)
    (hxy : xy ∈ compat_set h N) :
    (mistake_set A h xy).ncard ≤ al_dim_weighted (unfalsified H xy) (aoa_weight A xy) 0 := by
  classical
  by_cases hX : Nonempty X
  · obtain ⟨x0⟩ := hX
    have hh_uf : h ∈ unfalsified H xy := ⟨hh, by rw [hlen]; exact hxy⟩
    let T : ambiguous_tree (unfalsified H xy) :=
      { verts := {[]}
        inst := fun _ => x0
        hyp := fun _ => h
        defaults := ∅
        root_mem := rfl
        prefix_closed := by
          rintro u hu w hw
          have hu0 : u = [] := hu
          subst hu0
          have hw0 : w = [] := List.prefix_nil.mp hw
          subst hw0
          rfl
        verts_finite := Set.finite_singleton _
        default_child := by
          rintro u hu ⟨y, hy⟩
          have hu0 : u = [] := hu
          subst hu0
          simp at hy
        leaf_hyp_mem := by
          rintro u _ _
          exact hh_uf
        leaf_hyp_compat := by
          rintro u hu _ k y hk
          have hu0 : u = [] := hu
          subst hu0
          simp at hk }
    have hd : tree_depth T ≤ 0 := by
      have hverts : T.verts = ({[]} : Set (List Y)) := rfl
      simp only [tree_depth, hverts, Set.image_singleton, List.length_nil,
        csSup_singleton, le_refl]
    have hB : ∀ g ∈ unfalsified H xy, aoa_weight A xy g ≤ xy.length :=
      fun g _ => aoa_weight_le A g xy
    have hrank : (mistake_set A h xy).ncard ≤ tree_rank_weighted T (aoa_weight A xy) := by
      apply le_tree_rank_weighted
      intro u hu
      have hu0 : u = [] := hu.1
      subst hu0
      exact Nat.le_add_left _ _
    calc (mistake_set A h xy).ncard
        ≤ tree_rank_weighted T (aoa_weight A xy) := hrank
      _ ≤ al_dim_weighted (unfalsified H xy) (aoa_weight A xy) 0 :=
          le_al_dim_weighted (aoa_weight A xy) xy.length 0 hB T hd
  · have hempty : mistake_set A h xy = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro k ⟨p, -, -⟩
      exact hX ⟨p.1⟩
    rw [hempty, Set.ncard_empty]
    exact Nat.zero_le _

@[blueprint "lem:minimax-le-al"
  (statement := /-- Let $\mathcal{H} \subseteq \{X \to 2^Y\}$ with $Y$ finite. Then for every
  $N \in \mathbb{N}$,
  \[ \mathcal{M}^*_{\mathcal{H}}(N) \le \mathrm{AL}(\mathcal{H},N), \]
  with $\mathcal{M}^*_{\mathcal{H}}$ as in \cref{def:minimax-mistake-bound} and $\mathrm{AL}$ as in
  \cref{def:al-dim}. -/)
  (proof := /-- By \cref{lem:aoa-one-step} there is a deterministic learner $A^*$ satisfying the
  ambiguous-optimal-algorithm invariant for horizon $N$. By \cref{def:minimax-mistake-bound} the
  minimax bound is an infimum over learners, so
  $\mathcal{M}^*_{\mathcal{H}}(N) \le \mathcal{M}^{A^*}_{\mathcal{H}}(N)$, and it suffices to prove
  $\mathcal{M}^{A^*}_{\mathcal{H}}(N) \le \mathrm{AL}(\mathcal{H},N)$.

  By \cref{def:mistake-bound-class} the quantity $\mathcal{M}^{A^*}_{\mathcal{H}}(N)$ is the
  supremum over $h \in \mathcal{H}$ of $\mathcal{M}^{A^*}_h(N)$, and by
  \cref{def:mistake-bound-hyp} each $\mathcal{M}^{A^*}_h(N)$ is the supremum of
  $|\mathcal{M}^{A^*}_h(\overline{xy})|$ over $\overline{xy} \in \mathcal{C}_h(N)$. Since a
  supremum of natural numbers is bounded by any upper bound of the set, it suffices to show
  \[ \left|\mathcal{M}^{A^*}_h(\overline{xy})\right| \le \mathrm{AL}(\mathcal{H},N) \]
  for every $h \in \mathcal{H}$ and every $\overline{xy} \in \mathcal{C}_h(N)$.

  Fix such $h$ and $\overline{xy}$; then $|\overline{xy}| = N$ by \cref{def:compat-set}, and
  $\overline{xy} \in \mathcal{C}_{\mathcal{H}}(N)$ by \cref{def:compat-set-class} since
  $h \in \mathcal{H}$. By \cref{lem:weight-le-al-zero},
  \[ \left|\mathcal{M}^{A^*}_h(\overline{xy})\right| \le
  \mathrm{AL}_{w^{\overline{xy}}_{A^*}}\left(\mathcal{H}^{\overline{xy}}_{\mathrm{uf}},0\right), \]
  and by \cref{lem:aoa-chain} the right-hand side is at most $\mathrm{AL}(\mathcal{H},N)$. The
  claimed inequality follows. -/)
  (title := /-- Upper bound: the ambiguous optimal algorithm makes at most $\mathrm{AL}(\mathcal{H},N)$ mistakes -/)
  (latexEnv := "lemma")]
lemma minimax_le_al {X Y : Type*} [Fintype Y] (H : Set (X → Set Y)) (N : ℕ) :
    minimax_mistake_bound H N ≤ al_dim H N := by
  obtain ⟨A, hA⟩ := aoa_one_step H N
  rw [minimax_mistake_bound]
  refine (Nat.sInf_le (Set.mem_range_self A)).trans ?_
  rw [mistake_bound_class]
  apply csSup_le'
  rintro n ⟨h, hh, rfl⟩
  simp only
  rw [mistake_bound_hyp]
  apply csSup_le'
  rintro m ⟨xy, hxy, rfl⟩
  exact (weight_le_al_zero A hxy.1 hh hxy).trans (aoa_chain hA xy ⟨h, hh, hxy⟩)

@[blueprint "thm:minimax-eq-al"
  (statement := /-- Let $Y$ be a finite set of labels, let $X$ be a set of instances and let
  $\mathcal{H} \subseteq \{X \to 2^Y\}$ be a non-empty class of multivalued hypotheses such that
  for every $h \in \mathcal{H}$ there exists $x \in X$ with $h(x) \neq \emptyset$. Then for every
  $N \in \mathbb{N}$,
  \[ \mathcal{M}^*_{\mathcal{H}}(N) = \mathrm{AL}(\mathcal{H},N), \]
  that is, the minimax mistake bound of the ambiguous online learning game over horizon $N$ of
  \cref{def:minimax-mistake-bound} equals the ambiguous Littlestone dimension of $\mathcal{H}$
  restricted to trees of depth at most $N$ of \cref{def:al-dim}. -/)
  (proof := /-- The two inequalities are proved separately. The inequality
  $\mathcal{M}^*_{\mathcal{H}}(N) \le \mathrm{AL}(\mathcal{H},N)$ is \cref{lem:minimax-le-al},
  which requires only the finiteness of $Y$. The reverse inequality
  $\mathrm{AL}(\mathcal{H},N) \le \mathcal{M}^*_{\mathcal{H}}(N)$ is \cref{lem:al-le-minimax},
  which uses the hypothesis that every $h \in \mathcal{H}$ is non-vacuous, that is that there
  exists $x \in X$ with $h(x) \neq \emptyset$. By the antisymmetry of the order on $\mathbb{N}$
  the two inequalities give the asserted equality. -/)
  (title := /-- The minimax mistake bound equals the ambiguous Littlestone dimension -/)
  (latexEnv := "theorem")]
theorem minimax_eq_al {X Y : Type*} [Fintype Y] {H : Set (X → Set Y)} (hH : H.Nonempty)
    (hne : ∀ h ∈ H, ∃ x : X, (h x).Nonempty) (N : ℕ) :
    minimax_mistake_bound H N = al_dim H N := by
  exact le_antisymm (minimax_le_al H N) (al_le_minimax hne N)

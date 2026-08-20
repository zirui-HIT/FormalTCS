import Architect
import Mathlib

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:cut-value"
  (statement := /-- Let $V$ be a finite vertex type and let a graph on $V$ be represented by a
  weight function $w : V \to V \to \mathbb{R}$, where $w(u,v)$ is the weight of the edge between
  $u$ and $v$. For a subset $S \subseteq V$ with complement $V \setminus S$, the \emph{cut value}
  of $S$ is
  \[ \mathrm{cut}_w(S) \;=\; \sum_{u \in S}\;\sum_{v \in V \setminus S} w(u,v), \]
  the total weight of edges having exactly one endpoint in $S$. -/)
  (title := /-- Cut value of a vertex subset -/)
  (latexEnv := "definition")]
def cut_value {V : Type*} [Fintype V] [DecidableEq V] (w : V → V → ℝ) (S : Finset V) : ℝ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, w u v

@[blueprint "def:weighted-degree"
  (statement := /-- For a graph on a finite vertex type $V$ given by a weight function
  $w : V \to V \to \mathbb{R}$ and a vertex $v \in V$, the \emph{degree} of $v$ is
  \[ \deg_w(v) \;=\; \sum_{u \in V} w(v,u), \]
  the total weight of edges incident to $v$. For an unweighted graph this is the number of
  neighbours of $v$. -/)
  (title := /-- Weighted degree of a vertex -/)
  (latexEnv := "definition")]
def weighted_degree {V : Type*} [Fintype V] (w : V → V → ℝ) (v : V) : ℝ :=
  ∑ u, w v u

@[blueprint "def:crossing-weight"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ be a graph on a finite vertex type $V$, let
  $S \subseteq V$ be a cut, and let $v \in V$. The \emph{crossing weight} of $v$ with respect to
  $S$, denoted $\mathrm{cr}_S(v)$, is the total weight of edges incident to $v$ that cross the cut
  $(S, V \setminus S)$: it equals $\sum_{u \in V \setminus S} w(v,u)$ when $v \in S$, and
  $\sum_{u \in S} w(v,u)$ when $v \notin S$. -/)
  (title := /-- Crossing weight of a vertex at a cut -/)
  (latexEnv := "definition")]
def crossing_weight {V : Type*} [Fintype V] [DecidableEq V] (w : V → V → ℝ)
    (S : Finset V) (v : V) : ℝ :=
  if v ∈ S then ∑ u ∈ Sᶜ, w v u else ∑ u ∈ S, w v u

@[blueprint "def:friendliness-ratio"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ be a graph on a finite vertex type $V$, let
  $S \subseteq V$ be a cut, and let $v \in V$. The \emph{friendliness ratio} of $v$ with respect
  to $S$ is
  \[ 1 - \frac{\mathrm{cr}_S(v)}{\deg_w(v)}, \]
  where $\mathrm{cr}_S(v)$ is the crossing weight of $v$ at $S$ (see \cref{def:crossing-weight})
  and $\deg_w(v)$ is the degree of $v$ (see \cref{def:weighted-degree}). It measures the fraction
  of the weight incident to $v$ that stays on $v$'s own side of the cut. -/)
  (title := /-- Friendliness ratio of a vertex at a cut -/)
  (latexEnv := "definition")]
noncomputable def friendliness_ratio {V : Type*} [Fintype V] [DecidableEq V] (w : V → V → ℝ)
    (S : Finset V) (v : V) : ℝ :=
  1 - crossing_weight w S v / weighted_degree w v

@[blueprint "def:is-friendly-cut"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ be a graph on a finite vertex type $V$ and let
  $\alpha \in \mathbb{R}$. A cut $S \subseteq V$ is \emph{$\alpha$-friendly} if every vertex
  $v \in V$ has friendliness ratio at least $\alpha$ with respect to $S$, that is,
  $1 - \mathrm{cr}_S(v)/\deg_w(v) \ge \alpha$ for all $v \in V$ (see
  \cref{def:friendliness-ratio}). -/)
  (title := /-- $\alpha$-friendly cut -/)
  (latexEnv := "definition")]
def is_friendly_cut {V : Type*} [Fintype V] [DecidableEq V] (w : V → V → ℝ)
    (α : ℝ) (S : Finset V) : Prop :=
  ∀ v : V, α ≤ friendliness_ratio w S v

@[blueprint "def:contracted-graph"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ be a graph on a finite vertex type $V$ and let
  $\pi : V \to W$ assign to each vertex the super-vertex of $W$ into which it is contracted. The
  \emph{contracted graph} $\pi_\ast w : W \to W \to \mathbb{R}$ is defined, for distinct
  super-vertices $a \ne b$, by
  \[ (\pi_\ast w)(a,b) \;=\; \sum_{u \in \pi^{-1}(a)}\;\sum_{v \in \pi^{-1}(b)} w(u,v), \]
  the total weight of edges of $G$ running between the two parts, and by $(\pi_\ast w)(a,a) = 0$,
  discarding edges internal to a part. -/)
  (title := /-- Contraction of a graph along a partition map -/)
  (latexEnv := "definition")]
def contracted_graph {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (w : V → V → ℝ) (π : V → W) : W → W → ℝ :=
  fun a b =>
    if a = b then 0
    else ∑ u ∈ Finset.univ.filter (fun u => π u = a),
          ∑ v ∈ Finset.univ.filter (fun v => π v = b), w u v

@[blueprint "def:has-connected-contraction-fibres"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ be a weighted graph and let
  $\pi : V \to W$ assign each original vertex to a super-vertex. The fibres of $\pi$ are
  \emph{connected contraction fibres} if, whenever $\pi(u)=\pi(v)$, there is a finite walk from
  $u$ to $v$ all of whose consecutive vertices are joined by a nonzero edge of $w$ in at least
  one orientation. Equivalently, $u$ and $v$ are related by the reflexive transitive closure of
  the underlying adjacency relation $w(x,y)\ne 0$ or $w(y,x)\ne 0$. -/)
  (title := /-- Connected fibres of a contraction map -/)
  (latexEnv := "definition")]
def has_connected_contraction_fibres {V W : Type*} (w : V → V → ℝ) (π : V → W) : Prop :=
  ∀ u v : V, π u = π v →
    Relation.ReflTransGen (fun x y : V => w x y ≠ 0 ∨ w y x ≠ 0) u v

@[blueprint "def:is-contraction"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ be a graph on a finite vertex type $V$. A graph
  $H : W \to W \to \mathbb{R}$ on a finite vertex type $W$ is a \emph{contraction} of $w$ if there
  is a surjection $\pi : V \to W$ whose fibres are connected in the underlying graph of $w$ (see
  \cref{def:has-connected-contraction-fibres}) and for which $H = \pi_\ast w$. Thus $H$ is obtained
  from $w$ by contracting connected vertex sets into super-vertices and retaining precisely the
  edges between distinct fibres (see \cref{def:contracted-graph}). -/)
  (title := /-- Contraction of a graph -/)
  (latexEnv := "definition")]
def is_contraction {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (w : V → V → ℝ) (H : W → W → ℝ) : Prop :=
  ∃ π : V → W, Function.Surjective π ∧ has_connected_contraction_fibres w π ∧
    H = contracted_graph w π

@[blueprint "def:is-friendly-cut-sparsifier"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ be a graph on a finite vertex type $V$ and let
  $\alpha, \mathrm{budget} \in \mathbb{R}$. A graph $H : W \to W \to \mathbb{R}$ on a finite vertex
  type $W$ is an \emph{$(\alpha,\mathrm{budget})$-friendly cut sparsifier} of $w$ if there is a
  surjection $\pi : V \to W$ with connected fibres (see
  \cref{def:has-connected-contraction-fibres}) such that $H = \pi_\ast w$ (so $H$ is a contraction
  of $w$; see \cref{def:is-contraction}) and, for every $\alpha$-friendly cut $S \subseteq V$ (see
  \cref{def:is-friendly-cut}) whose cut value $\mathrm{cut}_w(S)$ is at most $\mathrm{budget}$ (see
  \cref{def:cut-value}), membership in $S$ is constant on every fibre of $\pi$ and the induced cut
  $\pi(S) \subseteq W$ satisfies $\mathrm{cut}_H(\pi(S)) = \mathrm{cut}_w(S)$. Thus preservation
  records both that no crossing edge is contracted and that the cut value is unchanged. -/)
  (title := /-- $(\alpha,\mathrm{budget})$-friendly cut sparsifier -/)
  (latexEnv := "definition")]
def is_friendly_cut_sparsifier {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (α budget : ℝ) (w : V → V → ℝ) (H : W → W → ℝ) : Prop :=
  ∃ π : V → W, Function.Surjective π ∧ has_connected_contraction_fibres w π ∧
    H = contracted_graph w π ∧
    ∀ S : Finset V, is_friendly_cut w α S → cut_value w S ≤ budget →
      (∀ u v : V, π u = π v → (u ∈ S ↔ v ∈ S)) ∧
        cut_value H (S.image π) = cut_value w S

@[blueprint "def:friendly-sparsifier-access"
  (statement := /-- For vertex types $V$ and $W$, an explicit-access representation of a friendly
  cut sparsifier consists of a contraction map $\pi : V \to W$ and a weight function
  $e_{\mathrm{fr}} : V \to V \to \mathbb{R}$ for the stored cross-fibre edges. The value
  $e_{\mathrm{fr}}(u,v)$ retains the original endpoints $u,v\in V$ of each sparsifier edge; the
  validity predicate in \cref{def:is-friendly-sparsifier-access} requires it to equal the original
  graph weight across distinct fibres and to vanish within a fibre. This representation makes the
  information available to an algorithm explicit instead of hiding the contraction map and edge
  endpoints inside an existential proposition. -/)
  (title := /-- Explicit access to a friendly cut sparsifier -/)
  (latexEnv := "definition")]
structure friendly_sparsifier_access (V W : Type*) where
  projection : V → W
  edgeWeights : V → V → ℝ

@[blueprint "def:is-friendly-sparsifier-access"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ be a graph and let
  $\mathcal H_{\mathrm{fr}}$ be explicit friendly-sparsifier data (see
  \cref{def:friendly-sparsifier-access}), with contraction map $\pi$ and stored endpoint weights
  $e_{\mathrm{fr}}$. For parameters $\alpha,\mathrm{budget}\in\mathbb{R}$, the data are valid if
  $\pi$ is surjective, every fibre of $\pi$ is connected in $w$ (see
  \cref{def:has-connected-contraction-fibres}), and
  \[
    e_{\mathrm{fr}}(u,v)=
    \begin{cases}0,&\pi(u)=\pi(v),\\ w(u,v),&\pi(u)\ne\pi(v),\end{cases}
  \]
  for all $u,v\in V$. Moreover, every $\alpha$-friendly cut $S$ of value at most
  $\mathrm{budget}$ is preserved by the induced contracted graph
  $\pi_\ast e_{\mathrm{fr}}$ (see \cref{def:contracted-graph}): membership in $S$ is constant on
  every contraction fibre, and the cut induced by $\pi(S)$ has value $\mathrm{cut}_w(S)$. -/)
  (title := /-- Valid explicit access to a friendly cut sparsifier -/)
  (latexEnv := "definition")]
def is_friendly_sparsifier_access {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (α budget : ℝ) (w : V → V → ℝ)
    (Hfr : friendly_sparsifier_access V W) : Prop :=
  Function.Surjective Hfr.projection ∧
    has_connected_contraction_fibres w Hfr.projection ∧
    (∀ u v : V, Hfr.edgeWeights u v =
      if Hfr.projection u = Hfr.projection v then 0 else w u v) ∧
    ∀ S : Finset V, is_friendly_cut w α S → cut_value w S ≤ budget →
      (∀ u v : V, Hfr.projection u = Hfr.projection v → (u ∈ S ↔ v ∈ S)) ∧
        cut_value (contracted_graph Hfr.edgeWeights Hfr.projection) (S.image Hfr.projection) =
          cut_value w S

@[blueprint "def:min-st-cut-value"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ be a graph on a finite vertex type $V$ and let
  $s, t \in V$. The \emph{minimum $s,t$-cut value} $\lambda_w(s,t)$ is the infimum of the cut
  values $\mathrm{cut}_w(S)$ (see \cref{def:cut-value}) over all subsets $S \subseteq V$ that
  separate $s$ from $t$, i.e. with $s \in S$ and $t \notin S$:
  \[ \lambda_w(s,t) \;=\; \inf\{\, \mathrm{cut}_w(S) \;:\; s \in S,\ t \notin S \,\}. \] -/)
  (title := /-- Minimum $s,t$-cut value -/)
  (latexEnv := "definition")]
noncomputable def min_st_cut_value {V : Type*} [Fintype V] [DecidableEq V] (w : V → V → ℝ)
    (s t : V) : ℝ :=
  sInf ((fun S => cut_value w S) '' {S : Finset V | s ∈ S ∧ t ∉ S})

@[blueprint "def:is-min-st-cut"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ be a graph on a finite vertex type $V$ and let
  $s, t \in V$. A subset $S \subseteq V$ is a \emph{minimum $s,t$-cut} of $w$ if it separates $s$
  from $t$, namely $s \in S$ and $t \notin S$, and its cut value attains the minimum $s,t$-cut
  value: $\mathrm{cut}_w(S) = \lambda_w(s,t)$ (see \cref{def:cut-value} and
  \cref{def:min-st-cut-value}). -/)
  (title := /-- Minimum $s,t$-cut -/)
  (latexEnv := "definition")]
def is_min_st_cut {V : Type*} [Fintype V] [DecidableEq V] (w : V → V → ℝ)
    (s t : V) (S : Finset V) : Prop :=
  s ∈ S ∧ t ∉ S ∧ cut_value w S = min_st_cut_value w s t

@[blueprint "def:is-apmc-sparsifier"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ be a graph on a finite vertex type $V$. A graph
  $H : U \to U \to \mathbb{R}$ on a finite vertex type $U$, together with an injection
  $\iota : V \hookrightarrow U$ realizing $U \supseteq V$, is an \emph{all-pairs minimum cut (APMC)
  sparsifier} of $w$ if for every pair of distinct vertices $s, t \in V$ with $s \ne t$ there
  exists a set $S \subseteq U$ such that:
  $S$ is a minimum $\iota(s),\iota(t)$-cut of $H$; its restriction $\iota^{-1}(S) \subseteq V$ is a
  minimum $s,t$-cut of $w$; the two cut values agree,
  $\mathrm{cut}_H(S) = \mathrm{cut}_w(\iota^{-1}(S))$; and the minimum cut values agree,
  $\lambda_H(\iota(s),\iota(t)) = \lambda_w(s,t)$ (see \cref{def:cut-value},
  \cref{def:min-st-cut-value}, and \cref{def:is-min-st-cut}). The condition ranges only over
  distinct pairs because a minimum $s,t$-cut, which must separate $s$ from $t$, is defined only
  for $s \ne t$. -/)
  (title := /-- All-pairs minimum cut (APMC) sparsifier -/)
  (latexEnv := "definition")]
def is_apmc_sparsifier {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (w : V → V → ℝ) (ι : V → U) (H : U → U → ℝ) : Prop :=
  Function.Injective ι ∧
    ∀ s t : V, s ≠ t → ∃ S : Finset U,
      is_min_st_cut H (ι s) (ι t) S ∧
      is_min_st_cut w s t (Finset.univ.filter (fun v : V => ι v ∈ S)) ∧
      cut_value H S = cut_value w (Finset.univ.filter (fun v : V => ι v ∈ S)) ∧
      min_st_cut_value H (ι s) (ι t) = min_st_cut_value w s t

@[blueprint "def:edge-count"
  (statement := /-- For a graph $H : U \to U \to \mathbb{R}$ on a finite vertex type $U$, the
  \emph{number of edges} $|E(H)|$ is the number of unordered pairs $\{a,b\}$ of distinct vertices
  ($a \ne b$) that carry a nonzero weight, i.e. with $H(a,b) \ne 0$ or $H(b,a) \ne 0$. -/)
  (title := /-- Number of edges of a graph -/)
  (latexEnv := "definition")]
noncomputable def edge_count {U : Type*} [Fintype U] (H : U → U → ℝ) : ℕ :=
  {e : Sym2 U |
      ¬ e.IsDiag ∧ Sym2.lift ⟨fun a b => H a b ≠ 0 ∨ H b a ≠ 0, fun _ _ => propext or_comm⟩ e}.ncard

@[blueprint "def:costed-apmc-constructor"
  (statement := /-- For finite vertex types $V$ and $W$, a \emph{costed APMC constructor} is a
  deterministic procedure represented by two functions. Given explicit friendly-sparsifier access
  $\mathcal H_{\mathrm{fr}}$ on $(V,W)$ (see \cref{def:friendly-sparsifier-access}) and a table
  $d : V \to \mathbb{R}$ of vertex degrees, its field $\mathrm{run}$ returns a weighted graph on
  $V\sqcup W$, and its field $\mathrm{runningTime}$ returns the number of elementary operations
  used on that input. In particular, neither function receives the original graph: its only graph
  data are the supplied sparsifier representation and degree table. -/)
  (title := /-- A costed constructor for APMC sparsifiers -/)
  (latexEnv := "definition")]
structure costed_apmc_constructor (V W : Type*) where
  run : friendly_sparsifier_access V W → (V → ℝ) → (V ⊕ W) → (V ⊕ W) → ℝ
  runningTime : friendly_sparsifier_access V W → (V → ℝ) → ℕ

@[blueprint "def:is-linear-time-apmc-construction"
  (statement := /-- Let $A$ be a costed APMC constructor on vertex types $V$ and $W$ (see
  \cref{def:costed-apmc-constructor}). The constructor runs in time
  $O(|E_{\mathrm{fr}}|+|V|)$ if there is a constant $C\in\mathbb{N}_{>0}$ such that, for every
  explicit sparsifier input $\mathcal H_{\mathrm{fr}}$ and every degree table $d : V\to\mathbb{R}$,
  \[
    \mathrm{runningTime}_A(\mathcal H_{\mathrm{fr}},d)
      \le C\bigl(|E_{\mathrm{fr}}|+|V|\bigr).
  \]
  Here $|E_{\mathrm{fr}}|$ is the support size of the stored cross-fibre edge weights, counted by
  \cref{def:edge-count}. The same constant must work for all inputs on these vertex types. -/)
  (title := /-- Linear-time bound for an APMC constructor -/)
  (latexEnv := "definition")]
def is_linear_time_apmc_construction {V W : Type*} [Fintype V]
    (A : costed_apmc_constructor V W) : Prop :=
  ∃ C : ℕ, 0 < C ∧
    ∀ (Hfr : friendly_sparsifier_access V W) (degrees : V → ℝ),
      A.runningTime Hfr degrees ≤ C * (edge_count Hfr.edgeWeights + Fintype.card V)

@[blueprint "def:is-simple-unweighted-graph"
  (statement := /-- A weight function $w : V \to V \to \mathbb{R}$ on a vertex type $V$ represents a
  \emph{simple unweighted graph} if it is symmetric ($w(u,v) = w(v,u)$ for all $u,v$), loopless
  ($w(v,v) = 0$ for all $v$), and has unit edge weights (for all $u,v$, either $w(u,v) = 0$ or
  $w(u,v) = 1$). -/)
  (title := /-- Simple unweighted graph -/)
  (latexEnv := "definition")]
def is_simple_unweighted_graph {V : Type*} (w : V → V → ℝ) : Prop :=
  (∀ u v, w u v = w v u) ∧ (∀ v, w v v = 0) ∧ (∀ u v : V, w u v = 0 ∨ w u v = 1)

@[blueprint "lem:aou-cut-nonneg"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ represent a simple unweighted graph on a
  finite vertex type $V$ (see \cref{def:is-simple-unweighted-graph}). Then for every subset
  $A \subseteq V$ the cut value is nonnegative, $0 \le \mathrm{cut}_w(A)$ (see
  \cref{def:cut-value}). -/)
  (proof := /-- By \cref{def:cut-value}, $\mathrm{cut}_w(A) = \sum_{u \in A} \sum_{v \in V
  \setminus A} w(u,v)$ is a double sum of weights $w(u,v)$. Since $w$ represents a simple unweighted
  graph (see \cref{def:is-simple-unweighted-graph}), each weight satisfies $w(u,v) = 0$ or
  $w(u,v) = 1$, so $w(u,v) \ge 0$; a sum of nonnegative terms is nonnegative. -/)
  (title := /-- Nonnegativity of the cut value -/)
  (latexEnv := "lemma")]
lemma aou_cut_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (hG : is_simple_unweighted_graph w) (A : Finset V) :
    0 ≤ cut_value w A := by
  unfold cut_value
  apply Finset.sum_nonneg
  intro u _
  apply Finset.sum_nonneg
  intro v _
  rcases hG.2.2 u v with h | h <;> rw [h] <;> norm_num

@[blueprint "lem:aou-min-cut-le"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ represent a simple unweighted graph on a
  finite vertex type $V$ (see \cref{def:is-simple-unweighted-graph}), let $s, t \in V$, and let
  $S \subseteq V$ be a minimum $s,t$-cut of $w$ (see \cref{def:is-min-st-cut}). Then for every
  subset $A \subseteq V$ that separates $s$ from $t$, i.e. $s \in A$ and $t \notin A$, one has
  $\mathrm{cut}_w(S) \le \mathrm{cut}_w(A)$ (see \cref{def:cut-value}). -/)
  (proof := /-- By \cref{def:is-min-st-cut}, $\mathrm{cut}_w(S) = \lambda_w(s,t)$, and by
  \cref{def:min-st-cut-value} the latter is the infimum of $\mathrm{cut}_w(\cdot)$ over all subsets
  separating $s$ from $t$. This set of cut values is bounded below by $0$, since every cut value is
  nonnegative by \cref{lem:aou-cut-nonneg}. As $A$ separates $s$ from $t$, its cut value
  $\mathrm{cut}_w(A)$ lies in this set, so the infimum is at most $\mathrm{cut}_w(A)$; hence
  $\mathrm{cut}_w(S) \le \mathrm{cut}_w(A)$. -/)
  (title := /-- A minimum cut is minimal among separating cuts -/)
  (latexEnv := "lemma")]
lemma aou_min_cut_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (hG : is_simple_unweighted_graph w)
    (s t : V) (S A : Finset V) (hS : is_min_st_cut w s t S)
    (hsA : s ∈ A) (htA : t ∉ A) :
    cut_value w S ≤ cut_value w A := by
  have hbdd : BddBelow ((fun S' => cut_value w S') '' {S' : Finset V | s ∈ S' ∧ t ∉ S'}) := by
    refine ⟨0, ?_⟩
    rintro x ⟨S', -, rfl⟩
    exact aou_cut_nonneg w hG S'
  have hmem : cut_value w A ∈
      (fun S' => cut_value w S') '' {S' : Finset V | s ∈ S' ∧ t ∉ S'} :=
    ⟨A, ⟨hsA, htA⟩, rfl⟩
  calc cut_value w S = min_st_cut_value w s t := hS.2.2
    _ ≤ cut_value w A := csInf_le hbdd hmem

@[blueprint "lem:aou-degree-ge-two"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ represent a simple unweighted graph on a
  finite vertex type $V$ (see \cref{def:is-simple-unweighted-graph}) and let $v \in V$. If the
  degree $\deg_w(v)$ (see \cref{def:weighted-degree}) is positive and different from $1$, then
  $\deg_w(v) \ge 2$. -/)
  (proof := /-- By \cref{def:weighted-degree}, $\deg_w(v) = \sum_{u} w(v,u)$. Since $w$ represents a
  simple unweighted graph (see \cref{def:is-simple-unweighted-graph}), each weight $w(v,u)$ equals
  $0$ or $1$, so $w(v,u) = \mathbf{1}[w(v,u) = 1]$ and the sum equals the number $n$ of vertices $u$
  with $w(v,u) = 1$; thus $\deg_w(v) = n$ with $n$ a natural number. From $\deg_w(v) > 0$ we get
  $n \ge 1$, and from $\deg_w(v) \ne 1$ we get $n \ne 1$, hence $n \ge 2$ and
  $\deg_w(v) = n \ge 2$. -/)
  (title := /-- A nonzero degree distinct from one is at least two -/)
  (latexEnv := "lemma")]
lemma aou_degree_ge_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (hG : is_simple_unweighted_graph w) (v : V)
    (hne : weighted_degree w v ≠ 1) (hpos : 0 < weighted_degree w v) :
    2 ≤ weighted_degree w v := by
  have h1 : weighted_degree w v = ∑ u, (if w v u = 1 then (1 : ℝ) else 0) := by
    unfold weighted_degree
    apply Finset.sum_congr rfl
    intro u _
    rcases hG.2.2 v u with h | h <;> rw [h] <;> simp
  rw [h1, Finset.sum_boole] at hne hpos ⊢
  set n := (Finset.univ.filter (fun x => w v x = 1)).card with hndef
  have hn0 : 0 < n := by exact_mod_cast hpos
  have hn1 : n ≠ 1 := by
    intro h; apply hne; rw [h]; norm_num
  have hge : 2 ≤ n := by omega
  exact_mod_cast hge

@[blueprint "lem:aou-degree-nonneg"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ represent a simple unweighted graph on a
  finite vertex type $V$ (see \cref{def:is-simple-unweighted-graph}) and let $v \in V$. Then the
  degree of $v$ is nonnegative, $0 \le \deg_w(v)$ (see \cref{def:weighted-degree}). -/)
  (proof := /-- By \cref{def:weighted-degree}, $\deg_w(v) = \sum_{u} w(v,u)$. Each weight
  $w(v,u)$ equals $0$ or $1$ by \cref{def:is-simple-unweighted-graph}, hence is nonnegative, and a
  sum of nonnegative reals is nonnegative. -/)
  (title := /-- Nonnegativity of the degree -/)
  (latexEnv := "lemma")]
lemma aou_degree_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (hG : is_simple_unweighted_graph w) (v : V) :
    0 ≤ weighted_degree w v := by
  unfold weighted_degree
  apply Finset.sum_nonneg
  intro u _
  rcases hG.2.2 v u with h | h <;> rw [h] <;> norm_num

@[blueprint "lem:aou-cut-value-singleton"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ represent a simple unweighted graph on a
  finite vertex type $V$ (see \cref{def:is-simple-unweighted-graph}) and let $x \in V$. Then the
  cut value of the singleton $\{x\}$ equals the degree of $x$, i.e.
  $\mathrm{cut}_w(\{x\}) = \deg_w(x)$ (see \cref{def:cut-value} and \cref{def:weighted-degree}). -/)
  (proof := /-- By \cref{def:cut-value}, $\mathrm{cut}_w(\{x\}) = \sum_{u \in \{x\}} \sum_{v \in
  \{x\}^{c}} w(u,v) = \sum_{v \in \{x\}^{c}} w(x,v)$. Splitting the full sum $\sum_{v} w(x,v)$ over
  $\{x\}$ and its complement gives $\sum_{v} w(x,v) = w(x,x) + \sum_{v \in \{x\}^{c}} w(x,v)$, and
  $w(x,x) = 0$ because $w$ represents a simple unweighted graph (see
  \cref{def:is-simple-unweighted-graph}). Hence $\sum_{v \in \{x\}^{c}} w(x,v) = \sum_{v} w(x,v) =
  \deg_w(x)$ (see \cref{def:weighted-degree}). -/)
  (title := /-- Cut value of a singleton is its degree -/)
  (latexEnv := "lemma")]
lemma aou_cut_value_singleton
    {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (hG : is_simple_unweighted_graph w) (x : V) :
    cut_value w {x} = weighted_degree w x := by
  unfold cut_value weighted_degree
  rw [Finset.sum_singleton]
  have h := Finset.sum_add_sum_compl {x} (fun v => w x v)
  rw [Finset.sum_singleton, hG.2.1 x, zero_add] at h
  exact h

@[blueprint "lem:aou-cut-value-compl-singleton"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ represent a simple unweighted graph on a
  finite vertex type $V$ (see \cref{def:is-simple-unweighted-graph}) and let $x \in V$. Then the
  cut value of the complement of the singleton $\{x\}$ equals the degree of $x$, i.e.
  $\mathrm{cut}_w(V \setminus \{x\}) = \deg_w(x)$ (see \cref{def:cut-value} and
  \cref{def:weighted-degree}). -/)
  (proof := /-- By \cref{def:cut-value}, $\mathrm{cut}_w(\{x\}^{c}) = \sum_{u \in \{x\}^{c}}
  \sum_{v \in (\{x\}^{c})^{c}} w(u,v)$; since $(\{x\}^{c})^{c} = \{x\}$, the inner sum is $w(u,x)$,
  so $\mathrm{cut}_w(\{x\}^{c}) = \sum_{u \in \{x\}^{c}} w(u,x)$. Symmetry of $w$ (see
  \cref{def:is-simple-unweighted-graph}) gives $w(u,x) = w(x,u)$, whence the sum equals
  $\sum_{u \in \{x\}^{c}} w(x,u)$. Splitting the full sum $\sum_{u} w(x,u)$ over $\{x\}$ and its
  complement and using $w(x,x) = 0$ yields $\sum_{u \in \{x\}^{c}} w(x,u) = \sum_{u} w(x,u) =
  \deg_w(x)$ (see \cref{def:weighted-degree}). -/)
  (title := /-- Cut value of a co-singleton is the degree -/)
  (latexEnv := "lemma")]
lemma aou_cut_value_compl_singleton
    {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (hG : is_simple_unweighted_graph w) (x : V) :
    cut_value w ({x}ᶜ) = weighted_degree w x := by
  unfold cut_value weighted_degree
  rw [compl_compl]
  have h1 : ∀ u, ∑ v ∈ ({x} : Finset V), w u v = w u x := by
    intro u; rw [Finset.sum_singleton]
  simp_rw [h1]
  have h2 : ∀ u, w u x = w x u := fun u => hG.1 u x
  simp_rw [h2]
  have h := Finset.sum_add_sum_compl {x} (fun u => w x u)
  rw [Finset.sum_singleton, hG.2.1 x, zero_add] at h
  exact h

@[blueprint "lem:aou-crossing-mem-le-cut"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ represent a simple unweighted graph on a
  finite vertex type $V$ (see \cref{def:is-simple-unweighted-graph}), let $S \subseteq V$, and let
  $x \in S$. Then the crossing weight of $x$ with respect to $S$ is at most the cut value of $S$,
  i.e. $\mathrm{cr}_S(x) \le \mathrm{cut}_w(S)$ (see \cref{def:crossing-weight} and
  \cref{def:cut-value}). -/)
  (proof := /-- Since $x \in S$, by \cref{def:crossing-weight} the crossing weight is
  $\mathrm{cr}_S(x) = \sum_{v \in V \setminus S} w(x,v)$, which is the summand of index $x$ in the
  double sum $\mathrm{cut}_w(S) = \sum_{u \in S} \sum_{v \in V \setminus S} w(u,v)$ (see
  \cref{def:cut-value}). Every summand $\sum_{v \in V \setminus S} w(u,v)$ is nonnegative because
  each weight $w(u,v)$ equals $0$ or $1$ by \cref{def:is-simple-unweighted-graph}; hence a single
  nonnegative summand is bounded above by the total sum. -/)
  (title := /-- Crossing weight of a member is at most the cut value -/)
  (latexEnv := "lemma")]
lemma aou_crossing_mem_le_cut
    {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (hG : is_simple_unweighted_graph w) (S : Finset V) (x : V)
    (hx : x ∈ S) :
    crossing_weight w S x ≤ cut_value w S := by
  unfold crossing_weight cut_value
  rw [if_pos hx]
  apply Finset.single_le_sum (f := fun u => ∑ v ∈ Sᶜ, w u v) ?_ hx
  intro u _
  apply Finset.sum_nonneg
  intro v _
  rcases hG.2.2 u v with h | h <;> rw [h] <;> norm_num

@[blueprint "lem:aou-cut-symm"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ represent a simple unweighted graph on a
  finite vertex type $V$ (see \cref{def:is-simple-unweighted-graph}) and let $S \subseteq V$. Then
  the cut values of $S$ and its complement agree, $\mathrm{cut}_w(V \setminus S) =
  \mathrm{cut}_w(S)$ (see \cref{def:cut-value}). -/)
  (proof := /-- By \cref{def:cut-value}, $\mathrm{cut}_w(S^{c}) = \sum_{u \in S^{c}} \sum_{v \in
  (S^{c})^{c}} w(u,v) = \sum_{u \in S^{c}} \sum_{v \in S} w(u,v)$, using $(S^{c})^{c} = S$.
  Interchanging the two finite sums rewrites this as $\sum_{v \in S} \sum_{u \in S^{c}} w(u,v)$, and
  symmetry of $w$ (see \cref{def:is-simple-unweighted-graph}) gives $w(u,v) = w(v,u)$, so the
  expression equals $\sum_{v \in S} \sum_{u \in S^{c}} w(v,u) = \mathrm{cut}_w(S)$ by
  \cref{def:cut-value}. -/)
  (title := /-- Cut value is invariant under complementation -/)
  (latexEnv := "lemma")]
lemma aou_cut_symm
    {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (hG : is_simple_unweighted_graph w) (S : Finset V) :
    cut_value w Sᶜ = cut_value w S := by
  unfold cut_value
  rw [compl_compl, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact hG.1 b a

@[blueprint "lem:aou-cut-erase"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ represent a simple unweighted graph on a
  finite vertex type $V$ (see \cref{def:is-simple-unweighted-graph}), let $S \subseteq V$, and let
  $x \in S$. Then removing $x$ from $S$ changes the cut value by
  \[ \mathrm{cut}_w(S \setminus \{x\}) = \mathrm{cut}_w(S) + \deg_w(x) - 2\,\mathrm{cr}_S(x), \]
  where $\mathrm{cut}_w$ is the cut value (see \cref{def:cut-value}), $\deg_w$ the degree (see
  \cref{def:weighted-degree}), and $\mathrm{cr}_S$ the crossing weight (see
  \cref{def:crossing-weight}). -/)
  (proof := /-- Write $\mathrm{cr}_S(x) = \sum_{v \in V \setminus S} w(x,v)$ since $x \in S$ (see
  \cref{def:crossing-weight}). The complement of $S \setminus \{x\}$ is $(V \setminus S) \cup
  \{x\}$, and $x \notin V \setminus S$, so for each $u$,
  $\sum_{v \in (V \setminus S) \cup \{x\}} w(u,v) = w(u,x) + \sum_{v \in V \setminus S} w(u,v)$.
  Summing over $u \in S \setminus \{x\}$ and distributing gives
  $\mathrm{cut}_w(S \setminus \{x\}) = \sum_{u \in S \setminus \{x\}} w(u,x) + \sum_{u \in S
  \setminus \{x\}} \sum_{v \in V \setminus S} w(u,v)$ (see \cref{def:cut-value}). By
  \cref{def:cut-value}, adding back the $u = x$ term shows $\sum_{u \in S \setminus \{x\}} \sum_{v
  \in V \setminus S} w(u,v) = \mathrm{cut}_w(S) - \mathrm{cr}_S(x)$. For the other summand, adding
  back the $u = x$ term and using $w(x,x) = 0$ (see \cref{def:is-simple-unweighted-graph}) gives
  $\sum_{u \in S \setminus \{x\}} w(u,x) = \sum_{u \in S} w(u,x)$; symmetry of $w$ (see
  \cref{def:is-simple-unweighted-graph}) turns this into $\sum_{u \in S} w(x,u)$, and splitting the
  full sum $\sum_u w(x,u) = \deg_w(x)$ over $S$ and $V \setminus S$ gives $\sum_{u \in S} w(x,u) =
  \deg_w(x) - \mathrm{cr}_S(x)$ (see \cref{def:weighted-degree}). Combining the two summands yields
  the stated identity. -/)
  (title := /-- Cut-value change under removing a vertex -/)
  (latexEnv := "lemma")]
lemma aou_cut_erase
    {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (hG : is_simple_unweighted_graph w) (S : Finset V) (x : V)
    (hx : x ∈ S) :
    cut_value w (S.erase x)
      = cut_value w S + weighted_degree w x - 2 * crossing_weight w S x := by
  have hxc : x ∉ Sᶜ := by simp [hx]
  have hcr : crossing_weight w S x = ∑ v ∈ Sᶜ, w x v := by
    unfold crossing_weight; rw [if_pos hx]
  have expand :
      cut_value w (S.erase x)
        = (∑ u ∈ S.erase x, w u x) + ∑ u ∈ S.erase x, ∑ v ∈ Sᶜ, w u v := by
    unfold cut_value
    rw [Finset.compl_erase, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.sum_insert hxc]
  have A : (∑ v ∈ Sᶜ, w x v) + ∑ u ∈ S.erase x, ∑ v ∈ Sᶜ, w u v = cut_value w S := by
    unfold cut_value
    exact Finset.add_sum_erase S (fun u => ∑ v ∈ Sᶜ, w u v) hx
  have Bsum : w x x + ∑ u ∈ S.erase x, w u x = ∑ u ∈ S, w u x :=
    Finset.add_sum_erase S (fun u => w u x) hx
  have Bsym : ∑ u ∈ S, w u x = ∑ u ∈ S, w x u := by
    apply Finset.sum_congr rfl; intro u _; exact hG.1 u x
  have Bsplit : (∑ u ∈ S, w x u) + ∑ u ∈ Sᶜ, w x u = weighted_degree w x :=
    Finset.sum_add_sum_compl S (fun u => w x u)
  rw [expand, hcr]
  rw [hG.2.1 x] at Bsum
  linarith [A, Bsum, Bsym, Bsplit]

@[blueprint "lem:aou-cut-insert"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ represent a simple unweighted graph on a
  finite vertex type $V$ (see \cref{def:is-simple-unweighted-graph}), let $S \subseteq V$, and let
  $x \notin S$. Then adding $x$ to $S$ changes the cut value by
  \[ \mathrm{cut}_w(S \cup \{x\}) = \mathrm{cut}_w(S) + \deg_w(x) - 2\,\mathrm{cr}_S(x), \]
  where $\mathrm{cut}_w$ is the cut value (see \cref{def:cut-value}), $\deg_w$ the degree (see
  \cref{def:weighted-degree}), and $\mathrm{cr}_S$ the crossing weight (see
  \cref{def:crossing-weight}). -/)
  (proof := /-- By \cref{lem:aou-cut-symm}, $\mathrm{cut}_w(S \cup \{x\}) = \mathrm{cut}_w((S \cup
  \{x\})^{c})$, and $(S \cup \{x\})^{c} = S^{c} \setminus \{x\}$ with $x \in S^{c}$. Applying
  \cref{lem:aou-cut-erase} to $S^{c}$ and $x$ gives $\mathrm{cut}_w(S^{c} \setminus \{x\}) =
  \mathrm{cut}_w(S^{c}) + \deg_w(x) - 2\,\mathrm{cr}_{S^{c}}(x)$. Now $\mathrm{cut}_w(S^{c}) =
  \mathrm{cut}_w(S)$ by \cref{lem:aou-cut-symm}, and since $x \in S^{c}$ the crossing weight
  $\mathrm{cr}_{S^{c}}(x) = \sum_{v \in S} w(x,v) = \mathrm{cr}_S(x)$ because $x \notin S$ (see
  \cref{def:crossing-weight}). Substituting yields the stated identity. -/)
  (title := /-- Cut-value change under inserting a vertex -/)
  (latexEnv := "lemma")]
lemma aou_cut_insert
    {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (hG : is_simple_unweighted_graph w) (S : Finset V) (x : V)
    (hx : x ∉ S) :
    cut_value w (insert x S)
      = cut_value w S + weighted_degree w x - 2 * crossing_weight w S x := by
  have hxc : x ∈ Sᶜ := Finset.mem_compl.mpr hx
  have hcr : crossing_weight w Sᶜ x = crossing_weight w S x := by
    unfold crossing_weight
    rw [if_pos hxc, if_neg hx, compl_compl]
  rw [← aou_cut_symm w hG (insert x S), Finset.compl_insert,
      aou_cut_erase w hG Sᶜ x hxc, aou_cut_symm w hG S, hcr]

@[blueprint "lem:aou-crossing-pair-le"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ represent a simple unweighted graph on a
  finite vertex type $V$ (see \cref{def:is-simple-unweighted-graph}) and let $S \subseteq V$ with
  $s \in S$ and $t \notin S$. Then the crossing weights of $s$ and $t$ with respect to $S$ satisfy
  $\mathrm{cr}_S(s) + \mathrm{cr}_S(t) \le \mathrm{cut}_w(S) + 1$ (see \cref{def:crossing-weight}
  and \cref{def:cut-value}). -/)
  (proof := /-- Since $s \in S$, by \cref{def:crossing-weight} we have $\mathrm{cr}_S(s) = \sum_{v
  \in V \setminus S} w(s,v)$, and since $t \notin S$ we have $\mathrm{cr}_S(t) = \sum_{u \in S}
  w(t,u)$. Taking out the $u = s$ summand from the double sum $\mathrm{cut}_w(S) = \sum_{u \in S}
  \sum_{v \in V \setminus S} w(u,v)$ (see \cref{def:cut-value}) gives $\mathrm{cut}_w(S) =
  \mathrm{cr}_S(s) + \sum_{u \in S \setminus \{s\}} \sum_{v \in V \setminus S} w(u,v)$. Likewise
  taking out the $u = s$ summand from $\mathrm{cr}_S(t)$ gives $\mathrm{cr}_S(t) = w(t,s) + \sum_{u
  \in S \setminus \{s\}} w(t,u)$. For each $u \in S \setminus \{s\}$, symmetry of $w$ (see
  \cref{def:is-simple-unweighted-graph}) gives $w(t,u) = w(u,t)$, and since $t \in V \setminus S$
  and weights are $0$ or $1$, $w(u,t)$ is one nonnegative summand of $\sum_{v \in V \setminus S}
  w(u,v)$, so $w(t,u) \le \sum_{v \in V \setminus S} w(u,v)$; summing over $u \in S \setminus \{s\}$
  yields $\sum_{u \in S \setminus \{s\}} w(t,u) \le \sum_{u \in S \setminus \{s\}} \sum_{v \in V
  \setminus S} w(u,v)$. Finally $w(t,s) \le 1$ because each weight is $0$ or $1$ (see
  \cref{def:is-simple-unweighted-graph}). Combining these gives $\mathrm{cr}_S(s) + \mathrm{cr}_S(t)
  \le \mathrm{cut}_w(S) + 1$. -/)
  (title := /-- Total crossing weight at the two endpoints -/)
  (latexEnv := "lemma")]
lemma aou_crossing_pair_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (hG : is_simple_unweighted_graph w) (S : Finset V) (s t : V)
    (hs : s ∈ S) (ht : t ∉ S) :
    crossing_weight w S s + crossing_weight w S t ≤ cut_value w S + 1 := by
  have hcrs : crossing_weight w S s = ∑ v ∈ Sᶜ, w s v := by
    unfold crossing_weight; rw [if_pos hs]
  have hcrt : crossing_weight w S t = ∑ u ∈ S, w t u := by
    unfold crossing_weight; rw [if_neg ht]
  have htc : t ∈ Sᶜ := Finset.mem_compl.mpr ht
  have hcut : cut_value w S = (∑ v ∈ Sᶜ, w s v) + ∑ u ∈ S.erase s, ∑ v ∈ Sᶜ, w u v := by
    unfold cut_value
    exact (Finset.add_sum_erase S (fun u => ∑ v ∈ Sᶜ, w u v) hs).symm
  have hcrt2 : (∑ u ∈ S, w t u) = w t s + ∑ u ∈ S.erase s, w t u :=
    (Finset.add_sum_erase S (fun u => w t u) hs).symm
  have htail : (∑ u ∈ S.erase s, w t u) ≤ ∑ u ∈ S.erase s, ∑ v ∈ Sᶜ, w u v := by
    apply Finset.sum_le_sum
    intro u _
    rw [hG.1 t u]
    apply Finset.single_le_sum (f := fun v => w u v) ?_ htc
    intro v _
    rcases hG.2.2 u v with h | h <;> rw [h] <;> norm_num
  have hwts : w t s ≤ 1 := by rcases hG.2.2 t s with h | h <;> rw [h] <;> norm_num
  rw [hcrs, hcrt, hcrt2, hcut]
  linarith [htail, hwts]

@[blueprint "lem:aou-nonendpoint-friendly"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ represent a simple unweighted graph on a
  finite vertex type $V$ (see \cref{def:is-simple-unweighted-graph}), let $s, t \in V$, and let
  $S \subseteq V$ be a minimum $s,t$-cut of $w$ (see \cref{def:is-min-st-cut}). Then every vertex
  $x \in V$ with $x \ne s$ and $x \ne t$ has friendliness ratio at least $\tfrac{1}{2}$ with respect
  to $S$, i.e. $\tfrac{1}{2} \le 1 - \mathrm{cr}_S(x)/\deg_w(x)$ (see
  \cref{def:friendliness-ratio}). -/)
  (proof := /-- We first show $2\,\mathrm{cr}_S(x) \le \deg_w(x)$ (see \cref{def:crossing-weight}
  and \cref{def:weighted-degree}), by cases on whether $x \in S$. If $x \in S$, then $S \setminus
  \{x\}$ still separates $s$ from $t$ since $s \in S$, $s \ne x$, and $t \notin S$; minimality of
  $S$ gives $\mathrm{cut}_w(S) \le \mathrm{cut}_w(S \setminus \{x\})$ by \cref{lem:aou-min-cut-le},
  and \cref{lem:aou-cut-erase} evaluates the right side as $\mathrm{cut}_w(S) + \deg_w(x) -
  2\,\mathrm{cr}_S(x)$, so $0 \le \deg_w(x) - 2\,\mathrm{cr}_S(x)$. If $x \notin S$, then $S \cup
  \{x\}$ still separates $s$ from $t$ since $s \in S$, $t \notin S$, and $t \ne x$; minimality gives
  $\mathrm{cut}_w(S) \le \mathrm{cut}_w(S \cup \{x\})$ by \cref{lem:aou-min-cut-le}, and
  \cref{lem:aou-cut-insert} evaluates the right side as $\mathrm{cut}_w(S) + \deg_w(x) -
  2\,\mathrm{cr}_S(x)$, giving the same bound. Now $\deg_w(x) \ge 0$ by \cref{lem:aou-degree-nonneg}
  (see \cref{def:weighted-degree}). If $\deg_w(x) = 0$ then, by the division-by-zero convention,
  $\mathrm{cr}_S(x)/\deg_w(x) = 0$ and the friendliness ratio equals $1 \ge \tfrac{1}{2}$. If
  $\deg_w(x) > 0$, then $2\,\mathrm{cr}_S(x) \le \deg_w(x)$ gives
  $\mathrm{cr}_S(x)/\deg_w(x) \le \tfrac{1}{2}$, hence the friendliness ratio
  $1 - \mathrm{cr}_S(x)/\deg_w(x) \ge \tfrac{1}{2}$ (see \cref{def:friendliness-ratio}). -/)
  (title := /-- Non-endpoints of a minimum cut are friendly -/)
  (latexEnv := "lemma")]
lemma aou_nonendpoint_friendly
    {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (hG : is_simple_unweighted_graph w)
    (s t : V) (S : Finset V) (hS : is_min_st_cut w s t S) (x : V)
    (hxs : x ≠ s) (hxt : x ≠ t) :
    (1 : ℝ) / 2 ≤ friendliness_ratio w S x := by
  have hcross : 2 * crossing_weight w S x ≤ weighted_degree w x := by
    by_cases hxS : x ∈ S
    · have hsep_s : s ∈ S.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxs, hS.1⟩
      have hsep_t : t ∉ S.erase x := fun h => hS.2.1 (Finset.mem_of_mem_erase h)
      have hle := aou_min_cut_le w hG s t S (S.erase x) hS hsep_s hsep_t
      rw [aou_cut_erase w hG S x hxS] at hle
      linarith
    · have hsep_s : s ∈ insert x S := Finset.mem_insert.mpr (Or.inr hS.1)
      have hsep_t : t ∉ insert x S := by
        rw [Finset.mem_insert]
        rintro (h | h)
        · exact hxt h.symm
        · exact hS.2.1 h
      have hle := aou_min_cut_le w hG s t S (insert x S) hS hsep_s hsep_t
      rw [aou_cut_insert w hG S x hxS] at hle
      linarith
  have hdeg := aou_degree_nonneg w hG x
  rcases lt_or_eq_of_le hdeg with hpos | hz
  · have hd2 : crossing_weight w S x / weighted_degree w x ≤ 1 / 2 := by
      rw [div_le_iff₀ hpos]; linarith
    unfold friendliness_ratio
    linarith
  · unfold friendliness_ratio
    rw [← hz, div_zero, sub_zero]
    norm_num

@[blueprint "lem:aou-not-both-unfriendly"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ represent a simple unweighted graph on a
  finite vertex type $V$ (see \cref{def:is-simple-unweighted-graph}) in which no vertex has degree
  $1$, i.e. $\deg_w(v) \ne 1$ for all $v \in V$ (see \cref{def:weighted-degree}). Let $s, t \in V$
  and let $S \subseteq V$ be a minimum $s,t$-cut of $w$ (see \cref{def:is-min-st-cut}). Then $s$ and
  $t$ cannot both have friendliness ratio strictly below $\tfrac{1}{6}$ with respect to $S$ (see
  \cref{def:friendliness-ratio}). -/)
  (proof := /-- Suppose for contradiction that both $s$ and $t$ have friendliness ratio below
  $\tfrac{1}{6}$, that is $1 - \mathrm{cr}_S(s)/\deg_w(s) < \tfrac{1}{6}$ and $1 -
  \mathrm{cr}_S(t)/\deg_w(t) < \tfrac{1}{6}$ (see \cref{def:friendliness-ratio}). Since $S$ is a
  minimum $s,t$-cut, $s \in S$ and $t \notin S$, so in particular $s \ne t$. The degrees are
  nonnegative by \cref{lem:aou-degree-nonneg}; if $\deg_w(s) = 0$ then $\mathrm{cr}_S(s)/\deg_w(s) =
  0$ by the division convention and the friendliness ratio of $s$ would equal $1 \ge \tfrac{1}{6}$,
  a contradiction, so $\deg_w(s) > 0$, and likewise $\deg_w(t) > 0$. From $\deg_w(s) > 0$ and
  $\deg_w(s) \ne 1$, \cref{lem:aou-degree-ge-two} gives $\deg_w(s) \ge 2$, and similarly
  $\deg_w(t) \ge 2$. The friendliness bounds rearrange, using $\deg_w(s), \deg_w(t) > 0$, to
  $\mathrm{cr}_S(s) > \tfrac{5}{6}\deg_w(s)$ and $\mathrm{cr}_S(t) > \tfrac{5}{6}\deg_w(t)$.
  Because $\{s\}$ separates $s$ from $t$, \cref{lem:aou-min-cut-le} together with
  \cref{lem:aou-cut-value-singleton} gives $\mathrm{cut}_w(S) \le \mathrm{cut}_w(\{s\}) =
  \deg_w(s)$; because $V \setminus \{t\}$ separates $s$ from $t$, \cref{lem:aou-min-cut-le} together
  with \cref{lem:aou-cut-value-compl-singleton} gives $\mathrm{cut}_w(S) \le \mathrm{cut}_w(V
  \setminus \{t\}) = \deg_w(t)$; hence $\deg_w(s) + \deg_w(t) \ge 2\,\mathrm{cut}_w(S)$. Adding the
  two crossing bounds and using this yields $\mathrm{cr}_S(s) + \mathrm{cr}_S(t) >
  \tfrac{5}{6}(\deg_w(s) + \deg_w(t)) \ge \tfrac{5}{3}\,\mathrm{cut}_w(S)$. On the other hand,
  \cref{lem:aou-crossing-pair-le} gives $\mathrm{cr}_S(s) + \mathrm{cr}_S(t) \le \mathrm{cut}_w(S) +
  1$, so $\mathrm{cut}_w(S) + 1 > \tfrac{5}{3}\,\mathrm{cut}_w(S)$, i.e. $\mathrm{cut}_w(S) <
  \tfrac{3}{2}$. But $\mathrm{cr}_S(s) \le \mathrm{cut}_w(S)$ by \cref{lem:aou-crossing-mem-le-cut}
  (as $s \in S$), while $\mathrm{cr}_S(s) > \tfrac{5}{6}\deg_w(s) \ge \tfrac{5}{3}$, so
  $\mathrm{cut}_w(S) > \tfrac{5}{3} > \tfrac{3}{2}$, contradicting $\mathrm{cut}_w(S) <
  \tfrac{3}{2}$. -/)
  (title := /-- The two endpoints are not both unfriendly -/)
  (latexEnv := "lemma")]
lemma aou_not_both_unfriendly
    {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (hG : is_simple_unweighted_graph w)
    (hdeg : ∀ v : V, weighted_degree w v ≠ 1)
    (s t : V) (S : Finset V) (hS : is_min_st_cut w s t S) :
    ¬ (friendliness_ratio w S s < 1 / 6 ∧ friendliness_ratio w S t < 1 / 6) := by
  rintro ⟨hs, ht⟩
  have hst : s ≠ t := fun h => hS.2.1 (h ▸ hS.1)
  unfold friendliness_ratio at hs ht
  have hds_nonneg := aou_degree_nonneg w hG s
  have hdt_nonneg := aou_degree_nonneg w hG t
  have hds_pos : 0 < weighted_degree w s := by
    rcases lt_or_eq_of_le hds_nonneg with h | h
    · exact h
    · exfalso; rw [← h, div_zero, sub_zero] at hs; norm_num at hs
  have hdt_pos : 0 < weighted_degree w t := by
    rcases lt_or_eq_of_le hdt_nonneg with h | h
    · exact h
    · exfalso; rw [← h, div_zero, sub_zero] at ht; norm_num at ht
  have hds2 : 2 ≤ weighted_degree w s := aou_degree_ge_two w hG s (hdeg s) hds_pos
  have hdt2 : 2 ≤ weighted_degree w t := aou_degree_ge_two w hG t (hdeg t) hdt_pos
  have hcrs : 5 / 6 * weighted_degree w s < crossing_weight w S s := by
    have h56 : (5 : ℝ) / 6 < crossing_weight w S s / weighted_degree w s := by linarith
    rwa [lt_div_iff₀ hds_pos] at h56
  have hcrt : 5 / 6 * weighted_degree w t < crossing_weight w S t := by
    have h56 : (5 : ℝ) / 6 < crossing_weight w S t / weighted_degree w t := by linarith
    rwa [lt_div_iff₀ hdt_pos] at h56
  have hcut_s : cut_value w S ≤ weighted_degree w s := by
    have hsep_s : s ∈ ({s} : Finset V) := Finset.mem_singleton_self s
    have hsep_t : t ∉ ({s} : Finset V) := by
      rw [Finset.mem_singleton]; exact fun h => hst h.symm
    have h := aou_min_cut_le w hG s t S {s} hS hsep_s hsep_t
    rwa [aou_cut_value_singleton w hG s] at h
  have hcut_t : cut_value w S ≤ weighted_degree w t := by
    have hsep_s : s ∈ ({t}ᶜ : Finset V) := by
      rw [Finset.mem_compl, Finset.mem_singleton]; exact hst
    have hsep_t : t ∉ ({t}ᶜ : Finset V) := by simp
    have h := aou_min_cut_le w hG s t S ({t}ᶜ) hS hsep_s hsep_t
    rwa [aou_cut_value_compl_singleton w hG t] at h
  have hpair := aou_crossing_pair_le w hG S s t hS.1 hS.2.1
  have hcrs_le := aou_crossing_mem_le_cut w hG S s hS.1
  linarith

@[blueprint "lem:at-most-one-unfriendly"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ represent a simple unweighted graph on a
  finite vertex type $V$ (see \cref{def:is-simple-unweighted-graph}) in which no vertex has degree
  $1$, that is, $\deg_w(v) \ne 1$ for every $v \in V$ (see \cref{def:weighted-degree}). Let
  $s, t \in V$ and let $S \subseteq V$ be a minimum $s,t$-cut of $G$ (see \cref{def:is-min-st-cut})
  that is not $\tfrac{1}{6}$-friendly (see \cref{def:is-friendly-cut}), i.e. at least one vertex has
  friendliness ratio (see \cref{def:friendliness-ratio}) strictly below $\tfrac{1}{6}$ with respect
  to $S$. Then there is a unique vertex $v \in V$ whose friendliness ratio with respect to $S$ is
  strictly below $\tfrac{1}{6}$, and this vertex satisfies $v = s$ or $v = t$. -/)
  (proof := /-- We first record that any unfriendly vertex is an endpoint: if $u \in V$ has
  friendliness ratio strictly below $\tfrac{1}{6}$ with respect to $S$ and $u \ne s$ and $u \ne t$,
  then by \cref{lem:aou-nonendpoint-friendly} its friendliness ratio is at least $\tfrac{1}{2}$,
  which contradicts being below $\tfrac{1}{6}$; hence every vertex of friendliness ratio below
  $\tfrac{1}{6}$ equals $s$ or $t$. Since $S$ is not $\tfrac{1}{6}$-friendly (see
  \cref{def:is-friendly-cut}), at least one vertex has friendliness ratio strictly below
  $\tfrac{1}{6}$ (see \cref{def:friendliness-ratio}). We split on whether $s$ is unfriendly.

  If $s$ has friendliness ratio strictly below $\tfrac{1}{6}$, take $v = s$. For any $u$ with
  friendliness ratio below $\tfrac{1}{6}$, the preceding paragraph gives $u = s$ or $u = t$; the
  case $u = t$ is impossible because then both $s$ and $t$ would be unfriendly, contradicting
  \cref{lem:aou-not-both-unfriendly}, so $u = s$. Conversely $s$ itself is unfriendly by assumption.
  Thus the vertices of friendliness ratio below $\tfrac{1}{6}$ are exactly $\{s\}$, and $v = s$
  satisfies $v = s \lor v = t$.

  If $s$ has friendliness ratio at least $\tfrac{1}{6}$, take $v = t$. The vertex exhibited above as
  unfriendly equals $s$ or $t$ by the first paragraph, and it is not $s$, so it is $t$; hence $t$ is
  unfriendly. For any $u$ with friendliness ratio below $\tfrac{1}{6}$, again $u = s$ or $u = t$,
  and $u = s$ is impossible since $s$ is friendly, so $u = t$. Conversely $t$ is unfriendly. Thus
  the vertices of friendliness ratio below $\tfrac{1}{6}$ are exactly $\{t\}$, and $v = t$ satisfies
  $v = s \lor v = t$. In both cases the unfriendly vertex is unique and is $s$ or $t$. -/)
  (title := /-- At most one unfriendly endpoint of a minimum cut -/)
  (latexEnv := "lemma")]
lemma at_most_one_unfriendly
    {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (hG : is_simple_unweighted_graph w)
    (hdeg : ∀ v : V, weighted_degree w v ≠ 1)
    (s t : V) (S : Finset V) (hS : is_min_st_cut w s t S)
    (hunfr : ¬ is_friendly_cut w (1 / 6) S) :
    ∃ v : V, (v = s ∨ v = t) ∧ ∀ u : V, friendliness_ratio w S u < 1 / 6 ↔ u = v := by
  have endpoint : ∀ u : V, friendliness_ratio w S u < 1 / 6 → u = s ∨ u = t := by
    intro u hu
    by_contra hcon
    have hus : u ≠ s := fun h => hcon (Or.inl h)
    have hut : u ≠ t := fun h => hcon (Or.inr h)
    have hfr := aou_nonendpoint_friendly w hG s t S hS u hus hut
    linarith
  simp only [is_friendly_cut, not_forall, not_le] at hunfr
  obtain ⟨v0, hv0⟩ := hunfr
  by_cases hs : friendliness_ratio w S s < 1 / 6
  · refine ⟨s, Or.inl rfl, ?_⟩
    intro u
    constructor
    · intro hu
      rcases endpoint u hu with h | h
      · exact h
      · exact absurd ⟨hs, h ▸ hu⟩ (aou_not_both_unfriendly w hG hdeg s t S hS)
    · intro hu; subst hu; exact hs
  · refine ⟨t, Or.inr rfl, ?_⟩
    have ht : friendliness_ratio w S t < 1 / 6 := by
      rcases endpoint v0 hv0 with h | h
      · subst h; exact absurd hv0 hs
      · subst h; exact hv0
    intro u
    constructor
    · intro hu
      rcases endpoint u hu with h | h
      · subst h; exact absurd hu hs
      · exact h
    · intro hu; subst hu; exact ht

@[blueprint "lem:structure-min-st-cut"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ represent a simple unweighted graph on a finite
  vertex type $V$ (see \cref{def:is-simple-unweighted-graph}) in which no vertex has degree $1$,
  i.e. $\deg_w(v) \ne 1$ for all $v \in V$ (see \cref{def:weighted-degree}). Let $s, t \in V$ and
  let $S \subseteq V$ be an inclusion-minimal minimum $s,t$-cut of $G$ (see
  \cref{def:is-min-st-cut}): $S$ is a minimum $s,t$-cut and no proper subset $S' \subsetneq S$ is a
  minimum $s,t$-cut. Suppose the vertex $s$ has friendliness ratio (see
  \cref{def:friendliness-ratio}) strictly below $\tfrac{1}{6}$ with respect to $S$. Then
  $X = S \setminus \{s\}$ is a $\tfrac{1}{6}$-friendly cut of $G$ (see \cref{def:is-friendly-cut})
  and its cut value satisfies $\mathrm{cut}_w(X) \le 2\deg_w(s)$ (see \cref{def:cut-value}). -/)
  (proof := /-- If $S = \{s\}$ then $X = \emptyset$, which is vacuously $\tfrac{1}{6}$-friendly and
  satisfies $\mathrm{cut}_w(X) = 0 \le 2\deg_w(s)$; the argument below covers this case uniformly.
  Write $X = S \setminus \{s\}$. We verify the two claims separately.

  \emph{Friendliness of $X$.} We show every vertex $v \in V$ has friendliness ratio at least
  $\tfrac{1}{6}$ with respect to $X$ (see \cref{def:friendliness-ratio}), splitting on the position
  of $v$.

  If $v = s$: first $\deg_w(s) > 0$, for otherwise $\deg_w(s) = 0$ (using
  $\deg_w(s) \ge 0$ from \cref{lem:aou-degree-nonneg}) would make the friendliness ratio of $s$
  with respect to $S$ equal $1 \ge \tfrac{1}{6}$ by the division-by-zero convention, contradicting
  the hypothesis $\mathrm{fr}_S(s) < \tfrac{1}{6}$. Since $s \in S$ and $s \notin X$, the crossing
  weight of $s$ at $X$ is $\mathrm{cr}_X(s) = \sum_{u \in X} w(s,u) = \sum_{u \in S} w(s,u) =
  \deg_w(s) - \mathrm{cr}_S(s)$, using $w(s,s) = 0$ and splitting $\deg_w(s) = \sum_u w(s,u)$ over
  $S$ and its complement (see \cref{def:crossing-weight}, \cref{def:weighted-degree}). Hence the
  friendliness ratio of $s$ at $X$ equals
  $1 - (\deg_w(s) - \mathrm{cr}_S(s))/\deg_w(s) = \mathrm{cr}_S(s)/\deg_w(s)$; and the hypothesis
  $1 - \mathrm{cr}_S(s)/\deg_w(s) < \tfrac{1}{6}$ gives $\mathrm{cr}_S(s)/\deg_w(s) > \tfrac{5}{6}
  \ge \tfrac{1}{6}$.

  If $v \in S$ and $v \ne s$ (so $v \in X$): the set $S \setminus \{v\}$ still separates $s$ from
  $t$, so it is not a minimum $s,t$-cut by inclusion-minimality of $S$ (see
  \cref{def:is-min-st-cut}); with $\mathrm{cut}_w(S) \le \mathrm{cut}_w(S \setminus \{v\})$ from
  \cref{lem:aou-min-cut-le} this inequality is strict, and \cref{lem:aou-cut-erase} evaluates
  $\mathrm{cut}_w(S \setminus \{v\}) = \mathrm{cut}_w(S) + \deg_w(v) - 2\,\mathrm{cr}_S(v)$, whence
  $2\,\mathrm{cr}_S(v) < \deg_w(v)$. Because $w$ is a simple unweighted graph (see
  \cref{def:is-simple-unweighted-graph}), $\deg_w(v)$, $\mathrm{cr}_S(v)$ and $w(v,s)$ are
  nonnegative integers with $w(v,s) \le 1$; from $2\,\mathrm{cr}_S(v) < \deg_w(v)$ and
  $\deg_w(v) \ne 1$ (so $\deg_w(v) = 0$ is excluded and $\deg_w(v) \ge 2$) one checks the integer
  inequality $6(\mathrm{cr}_S(v) + w(v,s)) \le 5\deg_w(v)$. Removing $s$ from $S$ places $s$ on the
  opposite side of $v$, so $\mathrm{cr}_X(v) = \mathrm{cr}_S(v) + w(v,s)$ (see
  \cref{def:crossing-weight}); therefore the friendliness ratio of $v$ at $X$ is
  $1 - \mathrm{cr}_X(v)/\deg_w(v) = 1 - (\mathrm{cr}_S(v) + w(v,s))/\deg_w(v) \ge 1 - \tfrac{5}{6}
  = \tfrac{1}{6}$.

  If $v \notin S$ (so $v \ne s$): since $s \in S$, removing $s$ from $S$ moves $s$ to $v$'s own
  side, so $\mathrm{cr}_X(v) = \mathrm{cr}_S(v) - w(v,s) \le \mathrm{cr}_S(v)$ (see
  \cref{def:crossing-weight}), and as $\deg_w(v) \ge 0$ by \cref{lem:aou-degree-nonneg} the
  friendliness ratio of $v$ at $X$ is at least its friendliness ratio at $S$ (see
  \cref{def:friendliness-ratio}). It thus suffices that $\mathrm{fr}_S(v) \ge \tfrac{1}{6}$. If
  $v \ne t$, then $v$ is a non-endpoint and $\mathrm{fr}_S(v) \ge \tfrac{1}{2} \ge \tfrac{1}{6}$ by
  \cref{lem:aou-nonendpoint-friendly}. If $v = t$, then since $s$ is unfriendly $S$ is not
  $\tfrac{1}{6}$-friendly (see \cref{def:is-friendly-cut}), so by \cref{lem:at-most-one-unfriendly}
  the unique unfriendly vertex is $s$; as $s \ne t$, the vertex $t$ is friendly,
  $\mathrm{fr}_S(t) \ge \tfrac{1}{6}$. In all cases $\mathrm{fr}_X(v) \ge \tfrac{1}{6}$, so $X$ is
  $\tfrac{1}{6}$-friendly.

  \emph{Cut-value bound.} By \cref{lem:aou-cut-erase},
  $\mathrm{cut}_w(X) = \mathrm{cut}_w(S) + \deg_w(s) - 2\,\mathrm{cr}_S(s)$, and
  $\mathrm{cr}_S(s) \ge 0$ since each weight is nonnegative (see \cref{def:crossing-weight},
  \cref{def:is-simple-unweighted-graph}). Because $\{s\}$ separates $s$ from $t$,
  \cref{lem:aou-min-cut-le} together with \cref{lem:aou-cut-value-singleton} gives
  $\mathrm{cut}_w(S) \le \mathrm{cut}_w(\{s\}) = \deg_w(s)$. Hence
  $\mathrm{cut}_w(X) \le \mathrm{cut}_w(S) + \deg_w(s) \le 2\deg_w(s)$ (see \cref{def:cut-value}). -/)
  (title := /-- Structure of a minimal minimum cut with an unfriendly endpoint -/)
  (latexEnv := "lemma")]
lemma structure_min_st_cut
    {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (hG : is_simple_unweighted_graph w)
    (hdeg : ∀ v : V, weighted_degree w v ≠ 1)
    (s t : V) (S : Finset V) (hS : is_min_st_cut w s t S)
    (hmin : ∀ S' : Finset V, S' ⊂ S → ¬ is_min_st_cut w s t S')
    (hs : friendliness_ratio w S s < 1 / 6) :
    is_friendly_cut w (1 / 6) (S.erase s) ∧
      cut_value w (S.erase s) ≤ 2 * weighted_degree w s := by
  have hsS : s ∈ S := hS.1
  have htS : t ∉ S := hS.2.1
  have hst : s ≠ t := fun h => htS (h ▸ hsS)
  refine ⟨?_, ?_⟩
  · intro v
    by_cases hvs : v = s
    · rw [hvs]
      have hds_nonneg := aou_degree_nonneg w hG s
      have hds_pos : 0 < weighted_degree w s := by
        rcases lt_or_eq_of_le hds_nonneg with h | h
        · exact h
        · exfalso
          unfold friendliness_ratio at hs
          rw [← h, div_zero, sub_zero] at hs
          norm_num at hs
      have hcrXs : crossing_weight w (S.erase s) s
          = weighted_degree w s - crossing_weight w S s := by
        have hs_notin : s ∉ S.erase s := by simp
        unfold crossing_weight
        rw [if_neg hs_notin, if_pos hsS, Finset.sum_erase_eq_sub hsS, hG.2.1 s]
        have hsplit := Finset.sum_add_sum_compl S (fun u => w s u)
        unfold weighted_degree
        linarith [hsplit]
      have hhs : 5 / 6 < crossing_weight w S s / weighted_degree w s := by
        unfold friendliness_ratio at hs
        linarith
      unfold friendliness_ratio
      rw [hcrXs, sub_div, div_self (ne_of_gt hds_pos)]
      linarith [hhs]
    · by_cases hvS : v ∈ S
      · have hvt : v ≠ t := fun h => htS (h ▸ hvS)
        have hsub : S.erase v ⊂ S := Finset.erase_ssubset hvS
        have hsep_s : s ∈ S.erase v := Finset.mem_erase.mpr ⟨fun h => hvs h.symm, hsS⟩
        have hsep_t : t ∉ S.erase v := fun h => htS (Finset.mem_of_mem_erase h)
        have hle := aou_min_cut_le w hG s t S (S.erase v) hS hsep_s hsep_t
        have hne : cut_value w (S.erase v) ≠ cut_value w S := by
          intro heq
          exact (hmin _ hsub) ⟨hsep_s, hsep_t, heq.trans hS.2.2⟩
        have hlt : cut_value w S < cut_value w (S.erase v) :=
          lt_of_le_of_ne hle (Ne.symm hne)
        rw [aou_cut_erase w hG S v hvS] at hlt
        have hstrict : 2 * crossing_weight w S v < weighted_degree w v := by linarith
        have hcrX : crossing_weight w (S.erase s) v
            = crossing_weight w S v + w v s := by
          have hv_erase : v ∈ S.erase s := Finset.mem_erase.mpr ⟨hvs, hvS⟩
          unfold crossing_weight
          rw [if_pos hv_erase, if_pos hvS, Finset.compl_erase,
            Finset.sum_insert (by simp [hsS])]
          ring
        obtain ⟨m, hm⟩ : ∃ m : ℕ, weighted_degree w v = (m : ℝ) := by
          refine ⟨∑ u, (if w v u = 1 then 1 else 0 : ℕ), ?_⟩
          rw [Nat.cast_sum]
          unfold weighted_degree
          apply Finset.sum_congr rfl
          intro u _
          rcases hG.2.2 v u with h | h <;> rw [h] <;> simp
        obtain ⟨n, hn⟩ : ∃ n : ℕ, crossing_weight w S v = (n : ℝ) := by
          refine ⟨∑ u ∈ Sᶜ, (if w v u = 1 then 1 else 0 : ℕ), ?_⟩
          rw [Nat.cast_sum]
          have hcrS_eq : crossing_weight w S v = ∑ u ∈ Sᶜ, w v u := by
            unfold crossing_weight
            rw [if_pos hvS]
          rw [hcrS_eq]
          apply Finset.sum_congr rfl
          intro u _
          rcases hG.2.2 v u with h | h <;> rw [h] <;> simp
        obtain ⟨k, hk, hk1⟩ : ∃ k : ℕ, w v s = (k : ℝ) ∧ k ≤ 1 := by
          rcases hG.2.2 v s with h | h
          · exact ⟨0, by rw [h]; simp, by norm_num⟩
          · exact ⟨1, by rw [h]; simp, le_refl 1⟩
        have h0 : 0 ≤ crossing_weight w S v := by rw [hn]; exact Nat.cast_nonneg n
        have hd_pos : 0 < weighted_degree w v := by linarith
        have hstrict_nat : 2 * n < m := by
          have hh := hstrict
          rw [hm, hn] at hh
          exact_mod_cast hh
        have hm_ne : m ≠ 1 := by
          intro h
          apply hdeg v
          rw [hm, h]
          norm_num
        have key : 6 * (crossing_weight w S v + w v s)
            ≤ 5 * weighted_degree w v := by
          rw [hm, hn, hk]
          have hnat : 6 * (n + k) ≤ 5 * m := by omega
          exact_mod_cast hnat
        have hratio : (crossing_weight w S v + w v s) / weighted_degree w v ≤ 5 / 6 := by
          rw [div_le_iff₀ hd_pos]
          linarith [key]
        unfold friendliness_ratio
        rw [hcrX]
        linarith [hratio]
      · have hcrX_out : crossing_weight w (S.erase s) v
            = crossing_weight w S v - w v s := by
          have hv_notin_erase : v ∉ S.erase s := fun h => hvS (Finset.mem_of_mem_erase h)
          unfold crossing_weight
          rw [if_neg hv_notin_erase, if_neg hvS]
          exact Finset.sum_erase_eq_sub hsS
        have hdv_nonneg := aou_degree_nonneg w hG v
        have hwvs0 : 0 ≤ w v s := by
          rcases hG.2.2 v s with h | h <;> rw [h] <;> norm_num
        have hmono : friendliness_ratio w S v ≤ friendliness_ratio w (S.erase s) v := by
          unfold friendliness_ratio
          rw [hcrX_out]
          rcases eq_or_lt_of_le hdv_nonneg with hd0 | hdpos
          · rw [← hd0]; simp
          · rw [sub_div]
            have hpos : 0 ≤ w v s / weighted_degree w v :=
              div_nonneg hwvs0 (le_of_lt hdpos)
            linarith
        have hSbound : 1 / 6 ≤ friendliness_ratio w S v := by
          by_cases hvt : v = t
          · rw [hvt]
            have hunfr : ¬ is_friendly_cut w (1 / 6) S := by
              intro hfr
              exact absurd (hfr s) (not_le.mpr hs)
            obtain ⟨v0, -, hv0_iff⟩ :=
              at_most_one_unfriendly w hG hdeg s t S hS hunfr
            have hsv0 : s = v0 := (hv0_iff s).mp hs
            by_contra hc
            rw [not_le] at hc
            have htv0 : t = v0 := (hv0_iff t).mp hc
            exact hst (htv0.trans hsv0.symm).symm
          · have h12 := aou_nonendpoint_friendly w hG s t S hS v hvs hvt
            linarith
        linarith [hmono, hSbound]
  · have hcr_s_nonneg : 0 ≤ crossing_weight w S s := by
      unfold crossing_weight
      rw [if_pos hsS]
      apply Finset.sum_nonneg
      intro u _
      rcases hG.2.2 s u with h | h <;> rw [h] <;> norm_num
    have hcut_s : cut_value w S ≤ weighted_degree w s := by
      have hsep_s : s ∈ ({s} : Finset V) := Finset.mem_singleton_self s
      have hsep_t : t ∉ ({s} : Finset V) := by
        rw [Finset.mem_singleton]
        exact fun h => hst h.symm
      have h := aou_min_cut_le w hG s t S {s} hS hsep_s hsep_t
      rwa [aou_cut_value_singleton w hG s] at h
    rw [aou_cut_erase w hG S s hsS]
    linarith

@[blueprint "lem:aou-cut-submodular"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ represent a simple unweighted graph on a finite
  vertex type $V$ (see \cref{def:is-simple-unweighted-graph}) and let $A, C \subseteq V$. Then the
  cut value (see \cref{def:cut-value}) is submodular:
  \[ \mathrm{cut}_w(A \cup C) + \mathrm{cut}_w(A \cap C) \le \mathrm{cut}_w(A) + \mathrm{cut}_w(C). \] -/)
  (proof := /-- For a subset $X \subseteq V$, expand $\mathrm{cut}_w(X) = \sum_{u} \sum_{v}
  \mathbf{1}[u \in X \wedge v \notin X]\, w(u,v)$ over all ordered pairs $(u,v)$, which agrees with
  \cref{def:cut-value} because the summand vanishes unless $u \in X$ and $v \in V \setminus X$.
  Applying this to $A \cup C$, $A \cap C$, $A$, and $C$, it suffices to prove the pointwise
  inequality
  \[ \mathbf{1}[u \in A \cup C \wedge v \notin A \cup C]\,w(u,v) + \mathbf{1}[u \in A \cap C \wedge
  v \notin A \cap C]\,w(u,v) \le \mathbf{1}[u \in A \wedge v \notin A]\,w(u,v) + \mathbf{1}[u \in C
  \wedge v \notin C]\,w(u,v) \]
  for each ordered pair $(u,v)$. Since $w(u,v) \ge 0$ (its value is $0$ or $1$ by
  \cref{def:is-simple-unweighted-graph}), this reduces to comparing the indicator coefficients,
  which is verified by exhausting the finitely many cases for the memberships of $u$ and $v$ in $A$
  and in $C$: in every case the number of the two sets $A \cup C$, $A \cap C$ that separate $u$
  from $v$ (with $u$ inside and $v$ outside) is at most the corresponding number for $A$, $C$.
  Summing the pointwise inequality over all $(u,v)$ gives the claim. -/)
  (title := /-- Submodularity of the cut function -/)
  (latexEnv := "lemma")]
lemma aou_cut_submodular
    {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (hG : is_simple_unweighted_graph w) (A C : Finset V) :
    cut_value w (A ∪ C) + cut_value w (A ∩ C) ≤ cut_value w A + cut_value w C := by
  have hd : ∀ X : Finset V, cut_value w X = ∑ u, ∑ v, (if u ∈ X ∧ v ∉ X then w u v else 0) := by
    intro X
    unfold cut_value
    symm
    calc ∑ u, ∑ v, (if u ∈ X ∧ v ∉ X then w u v else 0)
        = ∑ u, (if u ∈ X then ∑ v, (if v ∉ X then w u v else 0) else 0) := by
          apply Finset.sum_congr rfl; intro u _
          by_cases hu : u ∈ X <;> simp [hu]
      _ = ∑ u ∈ X, ∑ v, (if v ∉ X then w u v else 0) := by
          rw [Finset.sum_ite_mem, Finset.univ_inter]
      _ = ∑ u ∈ X, ∑ v ∈ Xᶜ, w u v := by
          apply Finset.sum_congr rfl; intro u _
          rw [← Finset.sum_filter]
          congr 1; ext v; simp [Finset.mem_compl]
  rw [hd (A ∪ C), hd (A ∩ C), hd A, hd C, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro u _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro v _
  have wnn : (0 : ℝ) ≤ w u v := by rcases hG.2.2 u v with h | h <;> rw [h] <;> norm_num
  simp only [Finset.mem_union, Finset.mem_inter]
  by_cases ha : u ∈ A <;> by_cases hc : u ∈ C <;> by_cases hva : v ∈ A <;> by_cases hvc : v ∈ C <;>
    simp_all <;> linarith

@[blueprint "lem:aou-exists-minimal-min-cut"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ represent a simple unweighted graph on a finite
  vertex type $V$ (see \cref{def:is-simple-unweighted-graph}) and let $s, t \in V$ with $s \ne t$.
  Then there exists a minimum $s,t$-cut $S$ of $G$ (see \cref{def:is-min-st-cut}) that is
  inclusion-minimal: no proper subset $S' \subsetneq S$ is a minimum $s,t$-cut. -/)
  (proof := /-- The minimum $s,t$-cut value $\lambda_w(s,t)$ (see \cref{def:min-st-cut-value}) is the
  infimum of $\mathrm{cut}_w$ (see \cref{def:cut-value}) over the sets separating $s$ from $t$, i.e.
  those with $s \in S'$ and $t \notin S'$. This family is nonempty, since $\{s\}$ separates $s$ from
  $t$ (as $s \ne t$), and it is finite because $V$ is finite; hence the infimum is attained and there
  is a minimum $s,t$-cut $S_0$ (see \cref{def:is-min-st-cut}). Among the finitely many minimum
  $s,t$-cuts choose one, $S$, of least cardinality. If some proper subset $S' \subsetneq S$ were a
  minimum $s,t$-cut, it would satisfy $|S'| < |S|$, contradicting the minimality of $|S|$. Hence no
  proper subset of $S$ is a minimum $s,t$-cut. -/)
  (title := /-- Existence of an inclusion-minimal minimum cut -/)
  (latexEnv := "lemma")]
lemma aou_exists_minimal_min_cut
    {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (s t : V) (hst : s ≠ t) :
    ∃ S : Finset V, is_min_st_cut w s t S ∧
      ∀ S' : Finset V, S' ⊂ S → ¬ is_min_st_cut w s t S' := by
  classical
  have hne0 : ({S' : Finset V | s ∈ S' ∧ t ∉ S'}).Nonempty := ⟨{s}, by simp [Ne.symm hst]⟩
  have hmem : min_st_cut_value w s t ∈
      (fun S' => cut_value w S') '' {S' : Finset V | s ∈ S' ∧ t ∉ S'} := by
    unfold min_st_cut_value
    exact (hne0.image _).csInf_mem ((Set.toFinite _).image _)
  obtain ⟨S0, hS0, hval0⟩ := hmem
  have hS0min : is_min_st_cut w s t S0 := ⟨hS0.1, hS0.2, hval0⟩
  set F : Finset (Finset V) := Finset.univ.filter (fun S => is_min_st_cut w s t S) with hF
  have hFne : F.Nonempty := ⟨S0, by simp [hF, hS0min]⟩
  obtain ⟨S, hSF, hSmin⟩ := Finset.exists_min_image F Finset.card hFne
  have hSmc : is_min_st_cut w s t S := by simpa [hF] using hSF
  refine ⟨S, hSmc, ?_⟩
  intro S' hsub hS'
  have hmemF : S' ∈ F := by simp [hF, hS']
  have hcard := hSmin S' hmemF
  have hlt : S'.card < S.card := Finset.card_lt_card hsub
  omega

@[blueprint "lem:aou-minimal-cut-subset"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ represent a simple unweighted graph on a finite
  vertex type $V$ (see \cref{def:is-simple-unweighted-graph}) and let $s, t \in V$. Let $S$ be an
  inclusion-minimal minimum $s,t$-cut of $G$ (see \cref{def:is-min-st-cut}): $S$ is a minimum
  $s,t$-cut and no proper subset $S' \subsetneq S$ is a minimum $s,t$-cut. Then $S \subseteq T$ for
  every minimum $s,t$-cut $T$. -/)
  (proof := /-- Both $S \cap T$ and $S \cup T$ separate $s$ from $t$: since $s \in S$ and $s \in T$
  we have $s \in S \cap T \subseteq S \cup T$, and since $t \notin S$, $t \notin T$ we have
  $t \notin S \cup T \supseteq S \cap T$ (see \cref{def:is-min-st-cut}). By \cref{lem:aou-min-cut-le}
  applied to the minimum $s,t$-cut $S$, $\mathrm{cut}_w(S) \le \mathrm{cut}_w(S \cap T)$ and
  $\mathrm{cut}_w(S) \le \mathrm{cut}_w(S \cup T)$ (see \cref{def:cut-value}). By submodularity
  \cref{lem:aou-cut-submodular}, $\mathrm{cut}_w(S \cup T) + \mathrm{cut}_w(S \cap T) \le
  \mathrm{cut}_w(S) + \mathrm{cut}_w(T)$, and since $S$ and $T$ are both minimum $s,t$-cuts,
  $\mathrm{cut}_w(T) = \mathrm{cut}_w(S)$. Combining these three inequalities forces
  $\mathrm{cut}_w(S \cap T) = \mathrm{cut}_w(S)$, so $S \cap T$ is itself a minimum $s,t$-cut. As
  $S \cap T \subseteq S$ and, by inclusion-minimality of $S$, $S \cap T$ cannot be a proper subset
  of $S$, we get $S \cap T = S$, i.e. $S \subseteq T$. -/)
  (title := /-- An inclusion-minimal minimum cut lies inside every minimum cut -/)
  (latexEnv := "lemma")]
lemma aou_minimal_cut_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (hG : is_simple_unweighted_graph w) (s t : V) (S T : Finset V)
    (hS : is_min_st_cut w s t S)
    (hSmin : ∀ S' : Finset V, S' ⊂ S → ¬ is_min_st_cut w s t S')
    (hT : is_min_st_cut w s t T) :
    S ⊆ T := by
  have hsI : s ∈ S ∩ T := Finset.mem_inter.2 ⟨hS.1, hT.1⟩
  have htI : t ∉ S ∩ T := fun h => hS.2.1 (Finset.mem_inter.1 h).1
  have hsU : s ∈ S ∪ T := Finset.mem_union.2 (Or.inl hS.1)
  have htU : t ∉ S ∪ T := by
    simp only [Finset.mem_union, not_or]; exact ⟨hS.2.1, hT.2.1⟩
  have h1 := aou_min_cut_le w hG s t S (S ∩ T) hS hsI htI
  have h2 := aou_min_cut_le w hG s t S (S ∪ T) hS hsU htU
  have hsm := aou_cut_submodular w hG S T
  have hTval : cut_value w T = cut_value w S := by rw [hT.2.2, hS.2.2]
  have hIval : cut_value w (S ∩ T) = cut_value w S := by linarith
  have hImin : is_min_st_cut w s t (S ∩ T) := ⟨hsI, htI, by rw [hIval]; exact hS.2.2⟩
  have hIeq : S ∩ T = S := by
    by_contra hne
    exact hSmin (S ∩ T) (Finset.inter_subset_left.ssubset_of_ne hne) hImin
  rw [Finset.inter_eq_left] at hIeq
  exact hIeq

@[blueprint "lem:aou-min-cut-value-symm"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ represent a simple unweighted graph on a finite
  vertex type $V$ (see \cref{def:is-simple-unweighted-graph}) and let $s, t \in V$. Then the minimum
  cut value is symmetric, $\lambda_w(s,t) = \lambda_w(t,s)$ (see \cref{def:min-st-cut-value}). -/)
  (proof := /-- By \cref{def:min-st-cut-value}, $\lambda_w(s,t)$ is the infimum of $\mathrm{cut}_w$
  (see \cref{def:cut-value}) over the sets $S$ with $s \in S$ and $t \notin S$, and $\lambda_w(t,s)$
  is the infimum over the sets with $t \in S$ and $s \notin S$. The map $S \mapsto V \setminus S$ is
  a bijection between these two families: $s \in S$ and $t \notin S$ if and only if
  $t \in V \setminus S$ and $s \notin V \setminus S$. Moreover $\mathrm{cut}_w(V \setminus S) =
  \mathrm{cut}_w(S)$ by \cref{lem:aou-cut-symm}. Hence the two families have the same set of cut
  values, and their infima coincide. -/)
  (title := /-- Symmetry of the minimum cut value -/)
  (latexEnv := "lemma")]
lemma aou_min_cut_value_symm
    {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (hG : is_simple_unweighted_graph w) (s t : V) :
    min_st_cut_value w s t = min_st_cut_value w t s := by
  unfold min_st_cut_value
  congr 1
  ext x
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact ⟨Sᶜ, ⟨by simpa using hS.2, by simpa using hS.1⟩, aou_cut_symm w hG S⟩
  · rintro ⟨S, hS, rfl⟩
    exact ⟨Sᶜ, ⟨by simpa using hS.2, by simpa using hS.1⟩, aou_cut_symm w hG S⟩

@[blueprint "lem:aou-friendly-cut-compl"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ be a graph on a finite vertex type $V$, let
  $\alpha \in \mathbb{R}$, and let $S \subseteq V$. If $S$ is $\alpha$-friendly (see
  \cref{def:is-friendly-cut}), then its complement $V \setminus S$ is $\alpha$-friendly as well. -/)
  (proof := /-- Fix $v \in V$. The crossing weight is invariant under complementation,
  $\mathrm{cr}_{V \setminus S}(v) = \mathrm{cr}_S(v)$ (see \cref{def:crossing-weight}): if $v \in S$
  then $v \notin V \setminus S$, so both equal $\sum_{u \in V \setminus S} w(v,u)$; if $v \notin S$
  then $v \in V \setminus S$, so both equal $\sum_{u \in S} w(v,u)$, using
  $(V \setminus S)^{c} = S$. Consequently the friendliness ratio of $v$ at $V \setminus S$ equals
  its friendliness ratio at $S$ (see \cref{def:friendliness-ratio}), which is at least $\alpha$ by
  hypothesis (see \cref{def:is-friendly-cut}). Since $v$ was arbitrary, $V \setminus S$ is
  $\alpha$-friendly. -/)
  (title := /-- Friendliness is invariant under complementation -/)
  (latexEnv := "lemma")]
lemma aou_friendly_cut_compl
    {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (α : ℝ) (S : Finset V) (h : is_friendly_cut w α S) :
    is_friendly_cut w α Sᶜ := by
  intro v
  have hv0 := h v
  unfold friendliness_ratio crossing_weight at hv0 ⊢
  by_cases hv : v ∈ S <;> simp_all [compl_compl]

@[blueprint "lem:encoding-structural-result"
  (statement := /-- Let $w : V \to V \to \mathbb{R}$ represent a simple unweighted graph on a finite
  vertex type $V$ with $n = |V|$ vertices (see \cref{def:is-simple-unweighted-graph}) in which no
  vertex has degree $1$, i.e. $\deg_w(v) \ne 1$ for all $v \in V$ (see \cref{def:weighted-degree}).
  Let $H_{\mathrm{fr}}$ be a $(1/6, 2n)$-friendly cut sparsifier of $G$ on a finite vertex type
  $V_{\mathrm{fr}}$ (see \cref{def:is-friendly-cut-sparsifier}). Then for every pair of distinct
  vertices $s, t \in V$ there exists a minimum $s,t$-cut $S$ of $G$ (see \cref{def:is-min-st-cut}),
  with $s \in S$ and $t \notin S$, that is recoverable from $H_{\mathrm{fr}}$ and the vertex degrees
  of $G$ in the following structural sense: either $S$ is $\tfrac{1}{6}$-friendly (see
  \cref{def:is-friendly-cut}); or $S \setminus \{s\}$ is a $\tfrac{1}{6}$-friendly cut with
  $\mathrm{cut}_w(S \setminus \{s\}) \le 2\deg_w(s)$ (see \cref{def:cut-value}); or
  $(V \setminus S) \setminus \{t\}$ is a $\tfrac{1}{6}$-friendly cut with
  $\mathrm{cut}_w((V \setminus S) \setminus \{t\}) \le 2\deg_w(t)$. -/)
  (proof := /-- Fix distinct $s, t \in V$. By \cref{lem:aou-exists-minimal-min-cut} there is an
  inclusion-minimal minimum $s,t$-cut $S$, so $s \in S$, $t \notin S$, and no proper subset of $S$
  is a minimum $s,t$-cut (see \cref{def:is-min-st-cut}).

  If $S$ is $\tfrac{1}{6}$-friendly (see \cref{def:is-friendly-cut}), the first alternative holds
  with the set $S$.

  Otherwise, suppose first that the source $s$ has friendliness ratio (see
  \cref{def:friendliness-ratio}) strictly below $\tfrac{1}{6}$ with respect to $S$. Then
  \cref{lem:structure-min-st-cut} applies to $s, t, S$ and shows that $S \setminus \{s\}$ is a
  $\tfrac{1}{6}$-friendly cut with $\mathrm{cut}_w(S \setminus \{s\}) \le 2\deg_w(s)$ (see
  \cref{def:cut-value}, \cref{def:weighted-degree}), which is the second alternative with the set
  $S$.

  Otherwise $\mathrm{fr}_S(s) \ge \tfrac{1}{6}$. By \cref{lem:aou-exists-minimal-min-cut} applied
  to the pair $t, s$ there is an inclusion-minimal minimum $t,s$-cut $B$, so $t \in B$ and
  $s \notin B$. Its complement $B^{c}$ satisfies $s \in B^{c}$ and $t \notin B^{c}$, and
  $\mathrm{cut}_w(B^{c}) = \mathrm{cut}_w(B) = \lambda_w(t,s) = \lambda_w(s,t)$ by
  \cref{lem:aou-cut-symm} and \cref{lem:aou-min-cut-value-symm} (see \cref{def:min-st-cut-value}),
  so $B^{c}$ is a minimum $s,t$-cut (see \cref{def:is-min-st-cut}). We return the set $B^{c}$ and
  distinguish three subcases; note that $(B^{c})^{c} = B$.

  If the vertex $t$ has friendliness ratio strictly below $\tfrac{1}{6}$ with respect to $B$, then
  \cref{lem:structure-min-st-cut} applies to $t, s, B$ and shows that $B \setminus \{t\}$ is a
  $\tfrac{1}{6}$-friendly cut with $\mathrm{cut}_w(B \setminus \{t\}) \le 2\deg_w(t)$; since
  $(B^{c})^{c} \setminus \{t\} = B \setminus \{t\}$, this is the third alternative with the set
  $B^{c}$.

  If instead $B$ is $\tfrac{1}{6}$-friendly, then $B^{c} = (B^{c})^{c\,c}$ is $\tfrac{1}{6}$-friendly
  by \cref{lem:aou-friendly-cut-compl}, so the first alternative holds with the set $B^{c}$.

  Finally, suppose $B$ is not $\tfrac{1}{6}$-friendly while $\mathrm{fr}_B(t) \ge \tfrac{1}{6}$. As
  $B$ is a minimum $t,s$-cut that is not $\tfrac{1}{6}$-friendly, \cref{lem:at-most-one-unfriendly}
  provides a unique vertex of friendliness ratio below $\tfrac{1}{6}$, equal to $t$ or $s$; since
  $\mathrm{fr}_B(t) \ge \tfrac{1}{6}$ that vertex is $s$, so $\mathrm{fr}_B(s) < \tfrac{1}{6}$. We
  derive a contradiction. By \cref{lem:aou-minimal-cut-subset}, the inclusion-minimal minimum
  $s,t$-cut $S$ is contained in every minimum $s,t$-cut, in particular $S \subseteq B^{c}$, whence
  $B \subseteq S^{c}$. Because $s \notin B$, the crossing weight of $s$ at $B$ is
  $\mathrm{cr}_B(s) = \sum_{u \in B} w(s,u)$, and because $s \in S$ it is
  $\mathrm{cr}_S(s) = \sum_{u \in S^{c}} w(s,u)$ (see \cref{def:crossing-weight}); since
  $B \subseteq S^{c}$ and all weights are nonnegative, $\mathrm{cr}_B(s) \le \mathrm{cr}_S(s)$.
  Moreover $\deg_w(s) > 0$: otherwise $\deg_w(s) = 0$ (using $\deg_w(s) \ge 0$ from
  \cref{lem:aou-degree-nonneg}) would make $\mathrm{fr}_B(s) = 1 \ge \tfrac{1}{6}$ by the
  division-by-zero convention (see \cref{def:friendliness-ratio}), contradicting
  $\mathrm{fr}_B(s) < \tfrac{1}{6}$. Rearranging the two friendliness bounds using $\deg_w(s) > 0$
  gives $\mathrm{cr}_B(s) > \tfrac{5}{6}\deg_w(s)$ and $\mathrm{cr}_S(s) \le \tfrac{5}{6}\deg_w(s)$,
  which together with $\mathrm{cr}_B(s) \le \mathrm{cr}_S(s)$ is impossible. This rules out the final
  subcase, so one of the first three alternatives always holds. -/)
  (title := /-- Structural encoding of minimum cuts via a friendly cut sparsifier -/)
  (latexEnv := "lemma")]
lemma encoding_structural_result
    {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (hG : is_simple_unweighted_graph w)
    (hdeg : ∀ v : V, weighted_degree w v ≠ 1)
    {Wv : Type*} [Fintype Wv] [DecidableEq Wv]
    (Hfr : Wv → Wv → ℝ)
    (hfr : is_friendly_cut_sparsifier (1 / 6) (2 * (Fintype.card V : ℝ)) w Hfr) :
    ∀ s t : V, s ≠ t → ∃ S : Finset V,
      is_min_st_cut w s t S ∧
        ( is_friendly_cut w (1 / 6) S ∨
          ( is_friendly_cut w (1 / 6) (S.erase s) ∧
              cut_value w (S.erase s) ≤ 2 * weighted_degree w s ) ∨
          ( is_friendly_cut w (1 / 6) (Sᶜ.erase t) ∧
              cut_value w (Sᶜ.erase t) ≤ 2 * weighted_degree w t ) ) := by
  intro s t hst
  obtain ⟨S, hSmc, hSmin⟩ := aou_exists_minimal_min_cut w s t hst
  by_cases hSfr : is_friendly_cut w (1 / 6) S
  · exact ⟨S, hSmc, Or.inl hSfr⟩
  · by_cases hfrs : friendliness_ratio w S s < 1 / 6
    · exact ⟨S, hSmc, Or.inr (Or.inl (structure_min_st_cut w hG hdeg s t S hSmc hSmin hfrs))⟩
    · replace hfrs : 1 / 6 ≤ friendliness_ratio w S s := not_lt.mp hfrs
      obtain ⟨B, hBmc, hBmin⟩ := aou_exists_minimal_min_cut w t s hst.symm
      have hsBc : s ∈ Bᶜ := Finset.mem_compl.2 hBmc.2.1
      have htBc : t ∉ Bᶜ := by simp [hBmc.1]
      have hBcval : cut_value w Bᶜ = min_st_cut_value w s t := by
        rw [aou_cut_symm w hG B, hBmc.2.2, aou_min_cut_value_symm w hG t s]
      have hBc_mincut : is_min_st_cut w s t Bᶜ := ⟨hsBc, htBc, hBcval⟩
      by_cases hfrBt : friendliness_ratio w B t < 1 / 6
      · obtain ⟨hfr, hcut⟩ := structure_min_st_cut w hG hdeg t s B hBmc hBmin hfrBt
        refine ⟨Bᶜ, hBc_mincut, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
        · rw [compl_compl]; exact hfr
        · rw [compl_compl]; exact hcut
      · by_cases hBfr : is_friendly_cut w (1 / 6) B
        · exact ⟨Bᶜ, hBc_mincut, Or.inl (aou_friendly_cut_compl w (1 / 6) B hBfr)⟩
        · obtain ⟨v, hv_or, hv_iff⟩ := at_most_one_unfriendly w hG hdeg t s B hBmc hBfr
          have hfrBv : friendliness_ratio w B v < 1 / 6 := (hv_iff v).mpr rfl
          have hvs : v = s := by
            rcases hv_or with h | h
            · exact absurd (h ▸ hfrBv) hfrBt
            · exact h
          rw [hvs] at hfrBv
          exfalso
          have hSsub : S ⊆ Bᶜ := aou_minimal_cut_subset w hG s t S Bᶜ hSmc hSmin hBc_mincut
          have hBsub : B ⊆ Sᶜ := by
            intro x hx
            rw [Finset.mem_compl]
            intro hxS
            have hh := hSsub hxS
            rw [Finset.mem_compl] at hh
            exact hh hx
          have hsS : s ∈ S := hSmc.1
          have hcrB : crossing_weight w B s = ∑ u ∈ B, w s u := by
            unfold crossing_weight; rw [if_neg hBmc.2.1]
          have hcrS : crossing_weight w S s = ∑ u ∈ Sᶜ, w s u := by
            unfold crossing_weight; rw [if_pos hsS]
          have hcrle : crossing_weight w B s ≤ crossing_weight w S s := by
            rw [hcrB, hcrS]
            apply Finset.sum_le_sum_of_subset_of_nonneg hBsub
            intro u _ _
            rcases hG.2.2 s u with h | h <;> rw [h] <;> norm_num
          have hds_nn := aou_degree_nonneg w hG s
          have hds_pos : 0 < weighted_degree w s := by
            rcases lt_or_eq_of_le hds_nn with h | h
            · exact h
            · exfalso
              unfold friendliness_ratio at hfrBv
              rw [← h, div_zero, sub_zero] at hfrBv
              norm_num at hfrBv
          unfold friendliness_ratio at hfrBv hfrs
          have hB56 : 5 / 6 < crossing_weight w B s / weighted_degree w s := by linarith
          have hB56' : 5 / 6 * weighted_degree w s < crossing_weight w B s := by
            rwa [lt_div_iff₀ hds_pos] at hB56
          have hS56 : crossing_weight w S s / weighted_degree w s ≤ 5 / 6 := by linarith
          have hS56' : crossing_weight w S s ≤ 5 / 6 * weighted_degree w s := by
            rw [div_le_iff₀ hds_pos] at hS56; linarith
          linarith [hcrle, hB56', hS56']

@[blueprint "def:apmc-star-graph"
  (statement := /-- Given explicit friendly-sparsifier access data
  $\mathcal H_{\mathrm{fr}}=(\pi,e_{\mathrm{fr}})$ and a degree table $d$ on $V$, the star graph
  on $V\sqcup W$ retains every stored edge $e_{\mathrm{fr}}(u,v)$ between original vertices and
  joins each original vertex $v$ to the proxy $\pi(v)$ with weight
  $d(v)-\sum_x e_{\mathrm{fr}}(v,x)$. All other proxy incidences have weight zero. -/)
  (title := /-- Star transform of explicit friendly-sparsifier data -/)
  (latexEnv := "definition")]
noncomputable def apmc_star_graph
    {V W : Type*} [Fintype V] [DecidableEq W]
    (Hfr : friendly_sparsifier_access V W) (degrees : V → ℝ) :
    (V ⊕ W) → (V ⊕ W) → ℝ
  | Sum.inl u, Sum.inl v => Hfr.edgeWeights u v
  | Sum.inl v, Sum.inr q =>
      if Hfr.projection v = q then degrees v - ∑ x, Hfr.edgeWeights v x else 0
  | Sum.inr q, Sum.inl v =>
      if Hfr.projection v = q then degrees v - ∑ x, Hfr.edgeWeights v x else 0
  | Sum.inr _, Sum.inr _ => 0

@[blueprint "def:apmc-star-constructor"
  (statement := /-- For finite types $V$ and $W$, the star constructor applies
  \cref{def:apmc-star-graph} to its explicit sparsifier input and degree table. Its recorded
  operation count is $|E_{\mathrm{fr}}|+|V|$. -/)
  (title := /-- Costed star-transform constructor -/)
  (latexEnv := "definition")]
noncomputable def apmc_star_constructor
    {V W : Type*} [Fintype V] [DecidableEq W] :
    costed_apmc_constructor V W where
  run := apmc_star_graph
  runningTime := fun Hfr _ => edge_count Hfr.edgeWeights + Fintype.card V

@[blueprint "lem:apmc-star-internal-weight"
  (statement := /-- Let $w$ be a graph and let
  $\mathcal H_{\mathrm{fr}}=(\pi,e_{\mathrm{fr}})$ be valid explicit friendly-sparsifier
  access data. For every $v\in V$, the degree of $v$ minus its stored cross-fibre degree equals
  the total weight from $v$ to its own contraction fibre:
  \[
    \deg_w(v)-\sum_x e_{\mathrm{fr}}(v,x)
      =\sum_{x:\,\pi(x)=\pi(v)}w(v,x).
  \] -/)
  (proof := /-- Expand the degree using \cref{def:weighted-degree}. By validity of the access data
  in \cref{def:is-friendly-sparsifier-access}, the stored weight is zero within the fibre of $v$
  and equals $w(v,x)$ outside that fibre. Subtracting term by term therefore cancels precisely the
  cross-fibre summands and leaves the displayed internal-fibre sum. -/)
  (title := /-- The proxy weight is the internal-fibre degree -/)
  (latexEnv := "lemma")]
lemma apmc_star_internal_weight
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (w : V → V → ℝ) (Hfr : friendly_sparsifier_access V W)
    (hfr : is_friendly_sparsifier_access (1 / 6) (2 * (Fintype.card V : ℝ)) w Hfr)
    (v : V) :
    weighted_degree w v - ∑ x, Hfr.edgeWeights v x =
      ∑ x ∈ Finset.univ.filter (fun x => Hfr.projection x = Hfr.projection v), w v x := by
  unfold weighted_degree
  rw [show (∑ x, w v x) - ∑ x, Hfr.edgeWeights v x =
      ∑ x, (w v x - Hfr.edgeWeights v x) by rw [Finset.sum_sub_distrib]]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  rw [hfr.2.2.1]
  by_cases h : Hfr.projection v = Hfr.projection x <;> simp [h, eq_comm]

@[blueprint "lem:apmc-star-cut-value"
  (statement := /-- For original-side vertices $S\subseteq V$ and proxy-side vertices
  $Q\subseteq W$, the cut value of the star graph at $S\sqcup Q$ is the sum of the stored
  original-edge cut, the proxy weights of vertices of $S$ whose proxies lie outside $Q$, and the
  proxy weights of vertices outside $S$ whose proxies lie in $Q$. -/)
  (proof := /-- Expand the cut value by \cref{def:cut-value} and split both finite sums over
  $V\sqcup W$. The four resulting blocks are evaluated from \cref{def:apmc-star-graph}. The
  original--original block is the stored-edge cut, the proxy--proxy block vanishes, and in each
  mixed block the equality test selects exactly the proxy attached to the relevant original
  vertex. Reordering the finite sum in the proxy--original block gives the stated formula. -/)
  (title := /-- Cut formula for the star transform -/)
  (latexEnv := "lemma")]
lemma apmc_star_cut_value
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (Hfr : friendly_sparsifier_access V W) (degrees : V → ℝ)
    (S : Finset V) (Q : Finset W) :
    cut_value (apmc_star_graph Hfr degrees) (S.disjSum Q) =
      (∑ u ∈ S, ∑ v ∈ Sᶜ, Hfr.edgeWeights u v) +
      (∑ v ∈ S, if Hfr.projection v ∈ Q then 0
        else degrees v - ∑ x, Hfr.edgeWeights v x) +
      ∑ v ∈ Sᶜ, if Hfr.projection v ∈ Q
        then degrees v - ∑ x, Hfr.edgeWeights v x else 0 := by
  classical
  unfold cut_value
  rw [show (S.disjSum Q)ᶜ = Sᶜ.disjSum Qᶜ by ext z <;> cases z <;> simp]
  simp only [Finset.sum_disjSum, apmc_star_graph, Finset.sum_add_distrib]
  have hswap :
      (∑ q ∈ Q, ∑ v ∈ Sᶜ, if Hfr.projection v = q
        then degrees v - ∑ x, Hfr.edgeWeights v x else 0) =
      ∑ v ∈ Sᶜ, ∑ q ∈ Q, if Hfr.projection v = q
        then degrees v - ∑ x, Hfr.edgeWeights v x else 0 := by
    rw [Finset.sum_comm]
  rw [hswap]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq']
  have hleft :
      (∑ v ∈ S, if Hfr.projection v ∈ Qᶜ
        then degrees v - ∑ x, Hfr.edgeWeights v x else 0) =
      ∑ v ∈ S, if Hfr.projection v ∈ Q then 0
        else degrees v - ∑ x, Hfr.edgeWeights v x := by
    apply Finset.sum_congr rfl
    intro v hv
    by_cases h : Hfr.projection v ∈ Q <;> simp [h]
  rw [hleft]
  simp only [Finset.sum_const_zero, add_zero]
  ring

@[blueprint "lem:apmc-star-cut-lower-bound"
  (statement := /-- Let $w$ be a simple unweighted graph and let
  $\mathcal H_{\mathrm{fr}}$ be valid explicit friendly-sparsifier access data. For every
  $S\subseteq V$ and $Q\subseteq W$, the cut of the star graph at $S\sqcup Q$ has value at least
  the value of the original cut $S$. -/)
  (proof := /-- Apply the star-cut formula from \cref{lem:apmc-star-cut-value} and replace each
  proxy weight by its internal-fibre degree using \cref{lem:apmc-star-internal-weight}. The stored
  original edges contribute exactly the crossing edges whose endpoints lie in different fibres.
  For an original crossing edge whose endpoints lie in the same fibre, the common proxy lies on
  one side of the star cut: the endpoint on the opposite side contributes that edge through its
  proxy weight. Nonnegativity of the unweighted graph weights permits restriction of each
  internal-fibre sum to these crossing neighbours. Summing over all original crossing edges gives
  the required inequality. -/)
  (title := /-- Every star cut dominates its original restriction -/)
  (latexEnv := "lemma")]
lemma apmc_star_cut_lower_bound
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (w : V → V → ℝ) (hG : is_simple_unweighted_graph w)
    (Hfr : friendly_sparsifier_access V W)
    (hfr : is_friendly_sparsifier_access (1 / 6) (2 * (Fintype.card V : ℝ)) w Hfr)
    (S : Finset V) (Q : Finset W) :
    cut_value w S ≤
      cut_value (apmc_star_graph Hfr (weighted_degree w)) (S.disjSum Q) := by
  rw [apmc_star_cut_value]
  simp_rw [apmc_star_internal_weight w Hfr hfr]
  simp_rw [hfr.2.2.1]
  unfold cut_value
  have hnonneg : ∀ u v : V, 0 ≤ w u v := by
    intro u v
    rcases hG.2.2 u v with h | h <;> rw [h] <;> norm_num
  have hdecomp :
      (∑ u ∈ S, ∑ v ∈ Sᶜ, w u v) =
        (∑ u ∈ S, ∑ v ∈ Sᶜ,
          if Hfr.projection u = Hfr.projection v then 0 else w u v) +
        (∑ u ∈ S, ∑ v ∈ Sᶜ,
          if Hfr.projection u ∈ Q then 0
          else if Hfr.projection u = Hfr.projection v then w u v else 0) +
        ∑ u ∈ S, ∑ v ∈ Sᶜ,
          if Hfr.projection v ∈ Q then
            if Hfr.projection u = Hfr.projection v then w u v else 0
          else 0 := by
    calc
      (∑ u ∈ S, ∑ v ∈ Sᶜ, w u v) =
          ∑ u ∈ S, ∑ v ∈ Sᶜ,
            ((if Hfr.projection u = Hfr.projection v then 0 else w u v) +
            (if Hfr.projection u ∈ Q then 0
              else if Hfr.projection u = Hfr.projection v then w u v else 0) +
            if Hfr.projection v ∈ Q then
              if Hfr.projection u = Hfr.projection v then w u v else 0
            else 0) := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        by_cases hp : Hfr.projection u = Hfr.projection v
        · by_cases hq : Hfr.projection u ∈ Q
          · have hqv : Hfr.projection v ∈ Q := by rwa [← hp]
            simp [hp, hq, hqv, hG.1 u v]
          · have hqv : Hfr.projection v ∉ Q := by rwa [← hp]
            simp [hp, hq, hqv]
        · simp [hp]
      _ = _ := by
        simp_rw [Finset.sum_add_distrib]
  have hleft :
      (∑ u ∈ S, ∑ v ∈ Sᶜ,
        if Hfr.projection u ∈ Q then 0
        else if Hfr.projection u = Hfr.projection v then w u v else 0) ≤
      ∑ u ∈ S, if Hfr.projection u ∈ Q then 0
        else ∑ x ∈ Finset.univ.filter
          (fun x => Hfr.projection x = Hfr.projection u), w u x := by
    apply Finset.sum_le_sum
    intro u hu
    by_cases hq : Hfr.projection u ∈ Q
    · simp [hq]
    · simp only [hq, ↓reduceIte]
      rw [Finset.sum_filter]
      have heq :
          (∑ x ∈ Sᶜ, if Hfr.projection u = Hfr.projection x then w u x else 0) =
          ∑ x ∈ Sᶜ, if Hfr.projection x = Hfr.projection u then w u x else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hp : Hfr.projection u = Hfr.projection x <;> simp [hp, eq_comm]
      rw [heq]
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Sᶜ)
      intro x hx hxS
      by_cases hp : Hfr.projection u = Hfr.projection x
      · simp [hp, hnonneg u x, eq_comm]
      · simp [hp, Ne.symm hp]
  have hright :
      (∑ u ∈ S, ∑ v ∈ Sᶜ,
        if Hfr.projection v ∈ Q then
          if Hfr.projection u = Hfr.projection v then w u v else 0
        else 0) ≤
      ∑ v ∈ Sᶜ, if Hfr.projection v ∈ Q then
        ∑ x ∈ Finset.univ.filter
          (fun x => Hfr.projection x = Hfr.projection v), w v x
        else 0 := by
    have hswap :
        (∑ u ∈ S, ∑ v ∈ Sᶜ,
          if Hfr.projection v ∈ Q then
            if Hfr.projection u = Hfr.projection v then w u v else 0
          else 0) =
        ∑ v ∈ Sᶜ, ∑ u ∈ S,
          if Hfr.projection v ∈ Q then
            if Hfr.projection u = Hfr.projection v then w u v else 0
          else 0 := by
      rw [Finset.sum_comm]
    rw [hswap]
    apply Finset.sum_le_sum
    intro v hv
    by_cases hq : Hfr.projection v ∈ Q
    · simp only [hq, ↓reduceIte]
      rw [Finset.sum_filter]
      have heq :
          (∑ u ∈ S, if Hfr.projection u = Hfr.projection v then w u v else 0) =
          ∑ u ∈ S, if Hfr.projection u = Hfr.projection v then w v u else 0 := by
        apply Finset.sum_congr rfl
        intro u hu
        by_cases hp : Hfr.projection u = Hfr.projection v
        · simp [hp, hG.1 u v]
        · simp [hp]
      rw [heq]
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      intro u hu huS
      by_cases hp : Hfr.projection u = Hfr.projection v
      · rw [if_pos hp]
        exact hnonneg v u
      · simp [hp]
    · simp [hq]
  rw [hdecomp]
  exact add_le_add (add_le_add_right hleft _) hright

@[blueprint "lem:apmc-star-lift-fibre-cut"
  (statement := /-- Let $S\subseteq V$ be constant on every contraction fibre of valid explicit
  access data $\mathcal H_{\mathrm{fr}}=(\pi,e_{\mathrm{fr}})$. If each proxy is placed on the
  side occupied by its fibre, then the cut $S\sqcup\pi(S)$ of the star graph has exactly the
  original cut value $\mathrm{cut}_w(S)$. -/)
  (proof := /-- Use the cut formula \cref{lem:apmc-star-cut-value} and identify proxy weights by
  \cref{lem:apmc-star-internal-weight}. Fibre-constancy gives
  $\pi(v)\in\pi(S)$ exactly when $v\in S$, so neither mixed proxy term contributes. It also
  ensures that every edge crossing $S$ joins distinct fibres. The access-validity equation then
  identifies every stored crossing weight with its original weight, proving equality with
  \cref{def:cut-value}. -/)
  (title := /-- Exact star lift of a fibre-constant cut -/)
  (latexEnv := "lemma")]
lemma apmc_star_lift_fibre_cut
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (w : V → V → ℝ) (Hfr : friendly_sparsifier_access V W)
    (hfr : is_friendly_sparsifier_access (1 / 6) (2 * (Fintype.card V : ℝ)) w Hfr)
    (S : Finset V)
    (hconst : ∀ u v : V, Hfr.projection u = Hfr.projection v → (u ∈ S ↔ v ∈ S)) :
    cut_value (apmc_star_graph Hfr (weighted_degree w))
        (S.disjSum (S.image Hfr.projection)) =
      cut_value w S := by
  rw [apmc_star_cut_value]
  simp_rw [apmc_star_internal_weight w Hfr hfr]
  simp_rw [hfr.2.2.1]
  have hmem : ∀ v : V, Hfr.projection v ∈ S.image Hfr.projection ↔ v ∈ S := by
    intro v
    constructor
    · intro hv
      obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
      exact (hconst u v huv).mp hu
    · intro hv
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
  simp_rw [hmem]
  unfold cut_value
  have hleftzero :
      (∑ x ∈ S, if x ∈ S then 0
        else ∑ y ∈ Finset.univ.filter
          (fun y => Hfr.projection y = Hfr.projection x), w x y) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp [hx]
  have hrightzero :
      (∑ x ∈ Sᶜ, if x ∈ S then
        ∑ y ∈ Finset.univ.filter
          (fun y => Hfr.projection y = Hfr.projection x), w x y else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hxS : x ∉ S := Finset.mem_compl.mp hx
    simp [hxS]
  rw [hleftzero, hrightzero]
  simp only [add_zero]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  have hne : Hfr.projection u ≠ Hfr.projection v := by
    intro hp
    exact (Finset.mem_compl.mp hv) ((hconst u v hp).mp hu)
  simp [hne]

@[blueprint "lem:apmc-star-lift-erased-cut"
  (statement := /-- Let $a\in S\subseteq V$. Suppose that $S\setminus\{a\}$ is constant on
  every contraction fibre of valid explicit access data. Place original vertices according to
  $S$ and proxies according to the fibres of $S\setminus\{a\}$. Then the resulting star cut has
  value exactly $\mathrm{cut}_w(S)$. -/)
  (proof := /-- Apply \cref{lem:apmc-star-cut-value} and
  \cref{lem:apmc-star-internal-weight}. Fibre-constancy shows that every vertex other than $a$ is
  on the same side as its proxy, while $a$ is opposite its proxy. Thus the only proxy contribution
  is the internal-fibre degree of $a$. Every crossing edge incident with a different fibre is
  retained as a stored original edge. Within the fibre of $a$, no vertex other than $a$ belongs
  to $S$: otherwise it would belong to $S\setminus\{a\}$ and fibre-constancy would force $a$ to
  belong there as well. The internal-fibre proxy weight therefore supplies exactly the remaining
  crossing edges at $a$; the loop at $a$ has weight zero by
  \cref{def:is-simple-unweighted-graph}. -/)
  (title := /-- Exact star lift after erasing one endpoint -/)
  (latexEnv := "lemma")]
lemma apmc_star_lift_erased_cut
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (w : V → V → ℝ) (hG : is_simple_unweighted_graph w)
    (Hfr : friendly_sparsifier_access V W)
    (hfr : is_friendly_sparsifier_access (1 / 6) (2 * (Fintype.card V : ℝ)) w Hfr)
    (S : Finset V) (a : V) (ha : a ∈ S)
    (hconst : ∀ u v : V, Hfr.projection u = Hfr.projection v →
      (u ∈ S.erase a ↔ v ∈ S.erase a)) :
    cut_value (apmc_star_graph Hfr (weighted_degree w))
        (S.disjSum ((S.erase a).image Hfr.projection)) =
      cut_value w S := by
  rw [apmc_star_cut_value]
  simp_rw [apmc_star_internal_weight w Hfr hfr]
  simp_rw [hfr.2.2.1]
  have hmem : ∀ v : V,
      Hfr.projection v ∈ (S.erase a).image Hfr.projection ↔ v ∈ S.erase a := by
    intro v
    constructor
    · intro hv
      obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
      exact (hconst u v huv).mp hu
    · intro hv
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
  simp_rw [hmem]
  unfold cut_value
  have hrightzero :
      (∑ x ∈ Sᶜ, if x ∈ S.erase a then
        ∑ y ∈ Finset.univ.filter
          (fun y => Hfr.projection y = Hfr.projection x), w x y else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hxS : x ∉ S := Finset.mem_compl.mp hx
    have hxE : x ∉ S.erase a := fun h => hxS (Finset.mem_of_mem_erase h)
    simp [hxE]
  have hleftproxy :
      (∑ x ∈ S, if x ∈ S.erase a then 0
        else ∑ y ∈ Finset.univ.filter
          (fun y => Hfr.projection y = Hfr.projection x), w x y) =
      ∑ y ∈ Finset.univ.filter
        (fun y => Hfr.projection y = Hfr.projection a), w a y := by
    have hother : ∀ b ∈ S, b ≠ a →
        (if b ∈ S.erase a then 0
        else ∑ y ∈ Finset.univ.filter
          (fun y => Hfr.projection y = Hfr.projection b), w b y) = 0 := by
      intro b hb hba
      have hbE : b ∈ S.erase a := Finset.mem_erase.mpr ⟨hba, hb⟩
      simp [hbE]
    have hmissing : a ∉ S →
        (if a ∈ S.erase a then 0
        else ∑ y ∈ Finset.univ.filter
          (fun y => Hfr.projection y = Hfr.projection a), w a y) = 0 := by
      intro h
      exact (h ha).elim
    simpa using Finset.sum_eq_single a hother hmissing
  have hinternal :
      (∑ x ∈ Finset.univ.filter
        (fun x => Hfr.projection x = Hfr.projection a), w a x) =
      ∑ x ∈ Sᶜ, if Hfr.projection a = Hfr.projection x then w a x else 0 := by
    rw [Finset.sum_filter]
    have horient :
        (∑ x, if Hfr.projection x = Hfr.projection a then w a x else 0) =
        ∑ x, if Hfr.projection a = Hfr.projection x then w a x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hp : Hfr.projection x = Hfr.projection a
      · simp [hp, eq_comm]
      · simp [hp, Ne.symm hp]
    rw [horient]
    symm
    apply Finset.sum_subset (Finset.subset_univ Sᶜ)
    intro x hx hxSc
    have hxS : x ∈ S := by simpa using hxSc
    by_cases hp : Hfr.projection a = Hfr.projection x
    · have hxa : x = a := by
        by_contra hne
        have hxE : x ∈ S.erase a := Finset.mem_erase.mpr ⟨hne, hxS⟩
        have haE : a ∈ S.erase a := (hconst x a hp.symm).mp hxE
        simpa using haE
      subst x
      simp [hG.2.1 a]
    · simp [hp]
  have hregular :
      (∑ u ∈ S.erase a, ∑ v ∈ Sᶜ,
        if Hfr.projection u = Hfr.projection v then 0 else w u v) =
      ∑ u ∈ S.erase a, ∑ v ∈ Sᶜ, w u v := by
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    have hne : Hfr.projection u ≠ Hfr.projection v := by
      intro hp
      have hvE : v ∉ S.erase a := fun h =>
        (Finset.mem_compl.mp hv) (Finset.mem_of_mem_erase h)
      exact hvE ((hconst u v hp).mp hu)
    simp [hne]
  have haedge :
      (∑ v ∈ Sᶜ, if Hfr.projection a = Hfr.projection v then 0 else w a v) +
        (∑ x ∈ Finset.univ.filter
          (fun x => Hfr.projection x = Hfr.projection a), w a x) =
      ∑ v ∈ Sᶜ, w a v := by
    rw [hinternal, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hp : Hfr.projection a = Hfr.projection v <;> simp [hp]
  rw [hrightzero, hleftproxy, add_zero]
  rw [← Finset.sum_erase_add S
    (fun u => ∑ v ∈ Sᶜ,
      if Hfr.projection u = Hfr.projection v then 0 else w u v) ha]
  rw [← Finset.sum_erase_add S (fun u => ∑ v ∈ Sᶜ, w u v) ha]
  calc
    ((∑ u ∈ S.erase a, ∑ v ∈ Sᶜ,
        if Hfr.projection u = Hfr.projection v then 0 else w u v) +
      ∑ v ∈ Sᶜ,
        if Hfr.projection a = Hfr.projection v then 0 else w a v) +
      ∑ x ∈ Finset.univ.filter
        (fun x => Hfr.projection x = Hfr.projection a), w a x =
      (∑ u ∈ S.erase a, ∑ v ∈ Sᶜ,
        if Hfr.projection u = Hfr.projection v then 0 else w u v) +
      ((∑ v ∈ Sᶜ,
        if Hfr.projection a = Hfr.projection v then 0 else w a v) +
      ∑ x ∈ Finset.univ.filter
        (fun x => Hfr.projection x = Hfr.projection a), w a x) := by ring
    _ = _ := by rw [hregular, haedge]

@[blueprint "lem:apmc-star-cut-complement"
  (statement := /-- For valid explicit access data of a simple unweighted graph, the star graph is
  symmetric. Consequently every star cut has the same value as its complement. -/)
  (proof := /-- Expand both cut values using \cref{def:cut-value}, interchange the two finite
  sums, and compare weights in opposite orientations. For two original vertices, access validity
  in \cref{def:is-friendly-sparsifier-access} reduces both stored weights to the corresponding
  original weights, which agree by symmetry in \cref{def:is-simple-unweighted-graph}. The two
  mixed cases agree directly from \cref{def:apmc-star-graph}, and proxy--proxy weights vanish. -/)
  (title := /-- Complement symmetry of star cuts -/)
  (latexEnv := "lemma")]
lemma apmc_star_cut_complement
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (w : V → V → ℝ) (hG : is_simple_unweighted_graph w)
    (Hfr : friendly_sparsifier_access V W)
    (hfr : is_friendly_sparsifier_access (1 / 6) (2 * (Fintype.card V : ℝ)) w Hfr)
    (X : Finset (V ⊕ W)) :
    cut_value (apmc_star_graph Hfr (weighted_degree w)) Xᶜ =
      cut_value (apmc_star_graph Hfr (weighted_degree w)) X := by
  unfold cut_value
  rw [compl_compl, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  cases x <;> cases y
  · simp [apmc_star_graph, hfr.2.2.1, hG.1, eq_comm]
  · simp [apmc_star_graph]
  · simp [apmc_star_graph]
  · simp [apmc_star_graph]

@[blueprint "lem:apmc-star-edge-count"
  (statement := /-- The star transform contains at most the stored original edges plus one proxy
  edge for each original vertex:
  \[
    |E(H_{\mathrm{star}})|\le |E_{\mathrm{fr}}|+|V|.
  \] -/)
  (proof := /-- By \cref{def:apmc-star-graph}, every nonzero unordered edge of the star graph is
  of one of two forms. An edge joining two original vertices is the image of a nonzero stored
  edge under the inclusion $V\hookrightarrow V\sqcup W$. A mixed edge must join a vertex $v$ to
  its unique proxy $\pi(v)$, so these edges lie in the image of a set indexed by $V$; no edge
  joins two proxies. Thus the star-edge support is contained in the union of an image of
  $E_{\mathrm{fr}}$ and an image of $V$. Subadditivity of finite cardinality and the fact that
  images do not increase cardinality give the bound in \cref{def:edge-count}. -/)
  (title := /-- Edge bound for the star transform -/)
  (latexEnv := "lemma")]
lemma apmc_star_edge_count
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (Hfr : friendly_sparsifier_access V W) (degrees : V → ℝ) :
    edge_count (apmc_star_graph Hfr degrees) ≤
      edge_count Hfr.edgeWeights + Fintype.card V := by
  classical
  let E0 : Set (Sym2 V) := {e | ¬ e.IsDiag ∧
    Sym2.lift ⟨fun a b => Hfr.edgeWeights a b ≠ 0 ∨ Hfr.edgeWeights b a ≠ 0,
      fun _ _ => propext or_comm⟩ e}
  let ES : Set (Sym2 (V ⊕ W)) := {e | ¬ e.IsDiag ∧
    Sym2.lift ⟨fun a b => apmc_star_graph Hfr degrees a b ≠ 0 ∨
      apmc_star_graph Hfr degrees b a ≠ 0, fun _ _ => propext or_comm⟩ e}
  let f : Sym2 V → Sym2 (V ⊕ W) := Sym2.map Sum.inl
  let g : V → Sym2 (V ⊕ W) :=
    fun v => s(Sum.inl v, Sum.inr (Hfr.projection v))
  have hsub : ES ⊆ f '' E0 ∪ Set.range g := by
    intro e
    refine Sym2.inductionOn e ?_
    intro x y hxy
    cases x with
    | inl u =>
      cases y with
      | inl v =>
        apply Set.mem_union_left
        refine ⟨s(u, v), ?_, ?_⟩
        · simpa [ES, E0, apmc_star_graph] using hxy
        · simp [f]
      | inr q =>
        apply Set.mem_union_right
        have hp : Hfr.projection u = q := by
          by_contra h
          simp [ES, apmc_star_graph, h] at hxy
        subst q
        exact ⟨u, by simp [g]⟩
    | inr q =>
      cases y with
      | inl v =>
        apply Set.mem_union_right
        have hp : Hfr.projection v = q := by
          by_contra h
          simp [ES, apmc_star_graph, h] at hxy
        subst q
        exact ⟨v, by simp [g, Sym2.eq_iff]⟩
      | inr r =>
        simp [ES, apmc_star_graph] at hxy
  unfold edge_count
  change ES.ncard ≤ E0.ncard + Fintype.card V
  calc
    ES.ncard ≤ (f '' E0 ∪ Set.range g).ncard := Set.ncard_le_ncard hsub
    _ ≤ (f '' E0).ncard + (Set.range g).ncard :=
      Set.ncard_union_le (f '' E0) (Set.range g)
    _ ≤ E0.ncard + (Set.range g).ncard :=
      Nat.add_le_add (Set.ncard_image_le) (le_refl _)
    _ ≤ E0.ncard + Fintype.card V := by
      have hrange : (Set.range g).ncard ≤ (Set.univ : Set V).ncard := by
        rw [← Set.image_univ]
        exact Set.ncard_image_le
      exact Nat.add_le_add (le_refl _) (by simpa using hrange)

@[blueprint "lem:apmc-unweighted-degree-le-card"
  (statement := /-- In a simple unweighted graph on a finite vertex type $V$, every weighted
  degree is at most $|V|$. -/)
  (proof := /-- Expand the degree by \cref{def:weighted-degree}. Every summand is either $0$ or
  $1$ by \cref{def:is-simple-unweighted-graph}, hence is at most $1$. Summing these pointwise
  inequalities over $V$ gives the asserted bound. -/)
  (title := /-- Unweighted degree is bounded by the vertex count -/)
  (latexEnv := "lemma")]
lemma apmc_unweighted_degree_le_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (hG : is_simple_unweighted_graph w) (v : V) :
    weighted_degree w v ≤ (Fintype.card V : ℝ) := by
  unfold weighted_degree
  calc
    (∑ u, w v u) ≤ ∑ _u : V, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro u hu
      rcases hG.2.2 v u with h | h <;> rw [h] <;> norm_num
    _ = (Fintype.card V : ℝ) := by simp

@[blueprint "lem:apmc-finite-min-cut-le"
  (statement := /-- For an arbitrary real-weighted graph on a finite vertex type, a minimum
  $s,t$-cut has value at most every other cut separating $s$ from $t$. -/)
  (proof := /-- The separating subsets form a finite family, so their image under
  \cref{def:cut-value} is bounded below. The value of any separating cut belongs to this image.
  By \cref{def:min-st-cut-value}, the minimum-cut value is its infimum, and
  \cref{def:is-min-st-cut} identifies the value of the given minimum cut with that infimum. -/)
  (title := /-- Minimality of a finite weighted minimum cut -/)
  (latexEnv := "lemma")]
lemma apmc_finite_min_cut_le
    {U : Type*} [Fintype U] [DecidableEq U]
    (H : U → U → ℝ) (s t : U) (S A : Finset U)
    (hS : is_min_st_cut H s t S) (hsA : s ∈ A) (htA : t ∉ A) :
    cut_value H S ≤ cut_value H A := by
  have hfinite :
      ((fun T => cut_value H T) '' {T : Finset U | s ∈ T ∧ t ∉ T}).Finite :=
    (Set.toFinite _).image _
  have hmem : cut_value H A ∈
      (fun T => cut_value H T) '' {T : Finset U | s ∈ T ∧ t ∉ T} :=
    ⟨A, ⟨hsA, htA⟩, rfl⟩
  calc
    cut_value H S = min_st_cut_value H s t := hS.2.2
    _ ≤ cut_value H A := csInf_le hfinite.bddBelow hmem

@[blueprint "thm:apmc-sparsifier-construction"
  (statement := /-- Fix finite vertex types $V$ and $V_{\mathrm{fr}}$. There is a single costed
  constructor $A$ (see \cref{def:costed-apmc-constructor}) with the following property. For every
  simple unweighted graph $G$ on $V$, represented by $w : V\to V\to\mathbb{R}$ (see
  \cref{def:is-simple-unweighted-graph}), and every valid explicit-access representation
  $\mathcal H_{\mathrm{fr}}$ of a $(1/6,2|V|)$-friendly cut sparsifier on
  $V_{\mathrm{fr}}$ (see \cref{def:is-friendly-sparsifier-access}), the constructor receives only
  $\mathcal H_{\mathrm{fr}}$ and the degree table $v\mapsto\deg_w(v)$. If
  $\deg_w(v)\ne 1$ for every $v\in V$, its output
  \[
    H_{\mathrm{ap}}=A.\mathrm{run}(\mathcal H_{\mathrm{fr}},\deg_w)
  \]
  is an APMC sparsifier of $G$ on $V\sqcup V_{\mathrm{fr}}$, with the original vertices included
  by $\mathrm{inl}$ (see \cref{def:is-apmc-sparsifier}), and
  \[
    |E(H_{\mathrm{ap}})|\le |E_{\mathrm{fr}}|+|V|.
  \]
  Here $|E_{\mathrm{fr}}|$ counts the stored cross-fibre edges with their original endpoints (see
  \cref{def:friendly-sparsifier-access, def:edge-count}). Moreover, $A$ satisfies the uniform
  running-time contract $O(|E_{\mathrm{fr}}|+|V|)$ of
  \cref{def:is-linear-time-apmc-construction}. -/)
  (proof := /-- Take $A$ to be the costed star constructor of
  \cref{def:apmc-star-constructor}. Its recorded operation count is
  $|E_{\mathrm{fr}}|+|V|$, so the linear-time contract holds with constant $1$. Fix valid access
  data $\mathcal H_{\mathrm{fr}}=(\pi,e_{\mathrm{fr}})$ for a simple unweighted graph $w$.
  The access equation implies that contracting $e_{\mathrm{fr}}$ along $\pi$ gives the same
  graph as contracting $w$; hence the access data determine a friendly cut sparsifier in the sense
  required by \cref{lem:encoding-structural-result}.

  Fix distinct $s,t\in V$, and let $S$ be the minimum $s,t$-cut supplied by
  \cref{lem:encoding-structural-result}. By \cref{lem:aou-min-cut-le} and
  \cref{lem:aou-cut-value-singleton}, its value is at most $\deg_w(s)$. The degree bound
  \cref{lem:apmc-unweighted-degree-le-card} therefore gives
  $\mathrm{cut}_w(S)\le 2|V|$. The same degree bound converts each of the two exceptional bounds
  in the structural trichotomy into the preservation budget $2|V|$.

  If $S$ is friendly, access validity makes it constant on contraction fibres, and
  \cref{lem:apmc-star-lift-fibre-cut} produces a star cut restricting to $S$ with value
  $\mathrm{cut}_w(S)$. If $S\setminus\{s\}$ is friendly, place proxies according to that
  erased cut and apply \cref{lem:apmc-star-lift-erased-cut}; the resulting star cut again restricts
  to $S$ and has the same value. In the third case apply the same erased-cut lemma to
  $S^c\setminus\{t\}$, then complement the resulting star cut. Its value is unchanged by
  \cref{lem:apmc-star-cut-complement}, and \cref{lem:aou-cut-symm} identifies the original
  complementary cut value with $\mathrm{cut}_w(S)$. Thus in every case there is a star cut
  $\widehat S$ separating $\mathrm{inl}(s)$ from $\mathrm{inl}(t)$, restricting to $S$, and
  having value $\mathrm{cut}_w(S)$.

  By \cref{lem:aou-exists-minimal-min-cut}, choose a minimum star cut $Y$ for the embedded
  terminals. Its original restriction $T$ separates $s$ from $t$. Minimality of $S$ gives
  $\mathrm{cut}_w(S)\le\mathrm{cut}_w(T)$, and
  \cref{lem:apmc-star-cut-lower-bound} gives
  $\mathrm{cut}_w(T)\le\mathrm{cut}_{H_{\mathrm{ap}}}(Y)$. Conversely,
  \cref{lem:apmc-finite-min-cut-le} gives
  $\mathrm{cut}_{H_{\mathrm{ap}}}(Y)\le
  \mathrm{cut}_{H_{\mathrm{ap}}}(\widehat S)$. Since the latter equals
  $\mathrm{cut}_w(S)$, all inequalities are equalities. Hence $\widehat S$ is a minimum star cut,
  its restriction is the minimum cut $S$, and both minimum-cut values agree, which is exactly
  \cref{def:is-apmc-sparsifier}. Finally,
  \cref{lem:apmc-star-edge-count} gives
  $|E(H_{\mathrm{ap}})|\le |E_{\mathrm{fr}}|+|V|$. -/)
  (title := /-- Linear-time APMC sparsifier construction from explicit friendly-sparsifier access -/)
  (latexEnv := "theorem")]
theorem apmc_sparsifier_construction
    {V : Type*} [Fintype V] [DecidableEq V]
    {Wv : Type*} [Fintype Wv] [DecidableEq Wv] :
    ∃ A : costed_apmc_constructor V Wv,
      is_linear_time_apmc_construction A ∧
      ∀ (w : V → V → ℝ) (hG : is_simple_unweighted_graph w)
        (Hfr : friendly_sparsifier_access V Wv)
        (hfr : is_friendly_sparsifier_access
          (1 / 6) (2 * (Fintype.card V : ℝ)) w Hfr)
        (hdeg : ∀ v : V, weighted_degree w v ≠ 1),
        is_apmc_sparsifier w Sum.inl (A.run Hfr (weighted_degree w)) ∧
          edge_count (A.run Hfr (weighted_degree w)) ≤
            edge_count Hfr.edgeWeights + Fintype.card V := by
  refine ⟨apmc_star_constructor, ?_, ?_⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro Hfr degrees
    simp [apmc_star_constructor]
  · intro w hG Hfr hfr hdeg
    constructor
    · unfold is_apmc_sparsifier
      refine ⟨Sum.inl_injective, ?_⟩
      intro s t hst
      have hcontract :
          contracted_graph Hfr.edgeWeights Hfr.projection =
            contracted_graph w Hfr.projection := by
        funext a b
        unfold contracted_graph
        by_cases hab : a = b
        · simp [hab]
        · simp only [hab, ↓reduceIte]
          apply Finset.sum_congr rfl
          intro u hu
          have hpu : Hfr.projection u = a := by simpa using hu
          apply Finset.sum_congr rfl
          intro v hv
          have hpv : Hfr.projection v = b := by simpa using hv
          rw [hfr.2.2.1]
          rw [if_neg]
          intro huv
          apply hab
          rw [← hpu, ← hpv, huv]
      have hfs : is_friendly_cut_sparsifier
          (1 / 6) (2 * (Fintype.card V : ℝ)) w
          (contracted_graph Hfr.edgeWeights Hfr.projection) :=
        ⟨Hfr.projection, hfr.1, hfr.2.1, hcontract, hfr.2.2.2⟩
      obtain ⟨S, hS, hstruct⟩ :=
        encoding_structural_result w hG hdeg
          (contracted_graph Hfr.edgeWeights Hfr.projection) hfs s t hst
      have hdegcard : ∀ v : V, weighted_degree w v ≤ (Fintype.card V : ℝ) :=
        fun v => apmc_unweighted_degree_le_card w hG v
      have hSledeg : cut_value w S ≤ weighted_degree w s := by
        calc
          cut_value w S ≤ cut_value w {s} :=
            aou_min_cut_le w hG s t S {s} hS (by simp) (by simpa using hst.symm)
          _ = weighted_degree w s := aou_cut_value_singleton w hG s
      have hSbudget : cut_value w S ≤ 2 * (Fintype.card V : ℝ) := by
        have hcard : 0 ≤ (Fintype.card V : ℝ) := by positivity
        nlinarith [hdegcard s]
      obtain ⟨X, hsX, htX, hrestrict, hcut⟩ :
          ∃ X : Finset (V ⊕ Wv), Sum.inl s ∈ X ∧ Sum.inl t ∉ X ∧
            Finset.univ.filter (fun v : V => Sum.inl v ∈ X) = S ∧
            cut_value (apmc_star_graph Hfr (weighted_degree w)) X = cut_value w S := by
        rcases hstruct with hSf | hrest
        · have hconst := (hfr.2.2.2 S hSf hSbudget).1
          refine ⟨S.disjSum (S.image Hfr.projection), ?_, ?_, ?_, ?_⟩
          · simpa using hS.1
          · simpa using hS.2.1
          · ext v
            simp
          · exact apmc_star_lift_fibre_cut w Hfr hfr S hconst
        · rcases hrest with hsCase | htCase
          · have hbudget : cut_value w (S.erase s) ≤
                2 * (Fintype.card V : ℝ) := by
              have hcard : 0 ≤ (Fintype.card V : ℝ) := by positivity
              nlinarith [hsCase.2, hdegcard s]
            have hconst := (hfr.2.2.2 (S.erase s) hsCase.1 hbudget).1
            refine ⟨S.disjSum ((S.erase s).image Hfr.projection), ?_, ?_, ?_, ?_⟩
            · simpa using hS.1
            · simpa using hS.2.1
            · ext v
              simp
            · exact apmc_star_lift_erased_cut w hG Hfr hfr S s hS.1 hconst
          · have hbudget : cut_value w (Sᶜ.erase t) ≤
                2 * (Fintype.card V : ℝ) := by
              have hcard : 0 ≤ (Fintype.card V : ℝ) := by positivity
              nlinarith [htCase.2, hdegcard t]
            have hconst := (hfr.2.2.2 (Sᶜ.erase t) htCase.1 hbudget).1
            let Y : Finset (V ⊕ Wv) :=
              Sᶜ.disjSum ((Sᶜ.erase t).image Hfr.projection)
            refine ⟨Yᶜ, ?_, ?_, ?_, ?_⟩
            · simp [Y, hS.1]
            · simp [Y, hS.2.1]
            · ext v
              simp [Y]
            · calc
                cut_value (apmc_star_graph Hfr (weighted_degree w)) Yᶜ =
                    cut_value (apmc_star_graph Hfr (weighted_degree w)) Y :=
                  apmc_star_cut_complement w hG Hfr hfr Y
                _ = cut_value w Sᶜ := by
                  exact apmc_star_lift_erased_cut w hG Hfr hfr Sᶜ t
                    (by simpa using hS.2.1) hconst
                _ = cut_value w S := aou_cut_symm w hG S
      obtain ⟨Y, hY, hYminimal⟩ :=
        aou_exists_minimal_min_cut
          (apmc_star_graph Hfr (weighted_degree w)) (Sum.inl s) (Sum.inl t)
          (Sum.inl_injective.ne hst)
      have hsYL : s ∈ Y.toLeft := by simpa using hY.1
      have htYL : t ∉ Y.toLeft := by simpa using hY.2.1
      have hXY : cut_value (apmc_star_graph Hfr (weighted_degree w)) X ≤
          cut_value (apmc_star_graph Hfr (weighted_degree w)) Y := by
        calc
          cut_value (apmc_star_graph Hfr (weighted_degree w)) X = cut_value w S := hcut
          _ ≤ cut_value w Y.toLeft :=
            aou_min_cut_le w hG s t S Y.toLeft hS hsYL htYL
          _ ≤ cut_value (apmc_star_graph Hfr (weighted_degree w))
              (Y.toLeft.disjSum Y.toRight) :=
            apmc_star_cut_lower_bound w hG Hfr hfr Y.toLeft Y.toRight
          _ = cut_value (apmc_star_graph Hfr (weighted_degree w)) Y := by
            rw [Finset.toLeft_disjSum_toRight]
      have hYX : cut_value (apmc_star_graph Hfr (weighted_degree w)) Y ≤
          cut_value (apmc_star_graph Hfr (weighted_degree w)) X :=
        apmc_finite_min_cut_le
          (apmc_star_graph Hfr (weighted_degree w)) (Sum.inl s) (Sum.inl t)
          Y X hY hsX htX
      have hcuts : cut_value (apmc_star_graph Hfr (weighted_degree w)) X =
          cut_value (apmc_star_graph Hfr (weighted_degree w)) Y :=
        le_antisymm hXY hYX
      have hXmin : is_min_st_cut
          (apmc_star_graph Hfr (weighted_degree w)) (Sum.inl s) (Sum.inl t) X :=
        ⟨hsX, htX, hcuts.trans hY.2.2⟩
      refine ⟨X, hXmin, ?_, ?_, ?_⟩
      · rwa [hrestrict]
      · simpa [apmc_star_constructor, hrestrict] using hcut
      · calc
          min_st_cut_value (apmc_star_graph Hfr (weighted_degree w))
              (Sum.inl s) (Sum.inl t) =
              cut_value (apmc_star_graph Hfr (weighted_degree w)) X := hXmin.2.2.symm
          _ = cut_value w S := hcut
          _ = min_st_cut_value w s t := hS.2.2
    · exact apmc_star_edge_count Hfr (weighted_degree w)

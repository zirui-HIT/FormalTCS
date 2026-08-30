import Architect
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Sym.Sym2
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sym
import Mathlib.Analysis.LocallyConvex.Separation

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

@[blueprint "def:cross-cluster-ind"
  (statement := /-- For a cluster $C \subseteq V$, the boundary indicator
    $\mathrm{crossClusterInd}(C) : \mathrm{Sym}_2 V \to \mathbb R$ assigns to an edge
    $e = \{u,v\}$ the value $\bigl|\mathbf 1_{u\in C} - \mathbf 1_{v\in C}\bigr|$, which
    equals $1$ when exactly one endpoint of $e$ lies in $C$ (i.e. $e \in \partial C$) and
    $0$ otherwise. The value is symmetric in the two endpoints. -/)
  (title := /-- Boundary indicator of a cluster -/)
  (latexEnv := "definition")]
def cross_cluster_ind (C : Finset V) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => |(if u ∈ C then (1 : ℝ) else 0) - (if v ∈ C then (1 : ℝ) else 0)|,
    fun u v => abs_sub_comm _ _⟩

@[blueprint "def:cross-partition-ind"
  (statement := /-- For a partition $\mathcal P$ of $V$, the boundary indicator
    $\mathrm{crossPartitionInd}(\mathcal P) : \mathrm{Sym}_2 V \to \mathbb R$ assigns the value
    $1$ to an edge $e$ whenever $e$ crosses some cluster $C \in \mathcal P$ (equivalently, the two
    endpoints of $e$ lie in different clusters, so $e \in \partial\mathcal P$) and $0$ otherwise. -/)
  (title := /-- Boundary indicator of a partition -/)
  (latexEnv := "definition")]
noncomputable def cross_partition_ind (P : Finpartition (Finset.univ : Finset V)) : Sym2 V → ℝ :=
  fun e => if ∃ C ∈ P.parts, cross_cluster_ind C e = 1 then (1 : ℝ) else 0

@[blueprint "def:cross-union-ind"
  (statement := /-- Given two edge indicators $w_1, w_2 : \mathrm{Sym}_2 V \to \mathbb R$, the union
    indicator $\mathrm{crossUnionInd}(w_1, w_2)$ assigns $1$ to an edge $e$ whenever $w_1(e) = 1$ or
    $w_2(e) = 1$, and $0$ otherwise. It models membership in the union of the two edge sets. -/)
  (title := /-- Indicator of a union of edge sets -/)
  (latexEnv := "definition")]
noncomputable def cross_union_ind (w₁ w₂ : Sym2 V → ℝ) : Sym2 V → ℝ :=
  fun e => if w₁ e = 1 ∨ w₂ e = 1 then (1 : ℝ) else 0

@[blueprint "def:deg-weighted"
  (statement := /-- For capacities $c : \mathrm{Sym}_2 V \to \mathbb R$ and an edge indicator
    $w : \mathrm{Sym}_2 V \to \mathbb R$, the weighted degree of a vertex $v$ is
    $\deg_w(v) = \sum_{e \ni v} w(e)\, c(e)$, the sum being over all edges incident to $v$. Taking
    $w$ to be $\mathrm{crossPartitionInd}(\mathcal P)$ recovers $\deg_{\partial\mathcal P}(v)$. -/)
  (title := /-- Weighted degree of a vertex -/)
  (latexEnv := "definition")]
def deg_weighted (c : Sym2 V → ℝ) (w : Sym2 V → ℝ) (v : V) : ℝ :=
  ∑ e : Sym2 V, if v ∈ e then w e * c e else 0

@[blueprint "def:delta-cut"
  (statement := /-- For capacities $c$ and a cluster $C \subseteq V$, the cut value is
    $\delta C = \sum_{e \in \partial C} c(e) = \sum_{e} \mathrm{crossClusterInd}(C, e)\, c(e)$,
    the total capacity of the edges with exactly one endpoint in $C$. -/)
  (title := /-- Capacity of a cut -/)
  (latexEnv := "definition")]
def delta_cut (c : Sym2 V → ℝ) (C : Finset V) : ℝ :=
  ∑ e : Sym2 V, cross_cluster_ind C e * c e

@[blueprint "def:restrict-to"
  (statement := /-- The restriction $\mathbf x|_S$ of a vector $\mathbf x : V \to \mathbb R$ to a set
    $S \subseteq V$ is the vector agreeing with $\mathbf x$ on $S$ and equal to $0$ outside $S$. -/)
  (title := /-- Restriction of a vector to a set -/)
  (latexEnv := "definition")]
def restrict_to (S : Finset V) (d : V → ℝ) : V → ℝ :=
  fun v => if v ∈ S then d v else 0

@[blueprint "def:is-flow"
  (statement := /-- A flow on $G$ is an antisymmetric function $f : V \to V \to \mathbb R$, where
    $f(u,v)$ denotes the (signed) flow sent from $u$ to $v$; antisymmetry means
    $f(u,v) = -f(v,u)$ for all $u,v \in V$. -/)
  (title := /-- Antisymmetric flow -/)
  (latexEnv := "definition")]
def is_flow (f : V → V → ℝ) : Prop :=
  ∀ u v, f u v = - f v u

@[blueprint "def:has-congestion"
  (statement := /-- A flow $f$ has congestion $\alpha$ with respect to capacities $c$ if the flow
    on every edge is at most $\alpha$ times its capacity, i.e. $|f(u,v)| \le \alpha\, c(\{u,v\})$
    for all $u,v \in V$. -/)
  (title := /-- Congestion of a flow -/)
  (latexEnv := "definition")]
def has_congestion (c : Sym2 V → ℝ) (α : ℝ) (f : V → V → ℝ) : Prop :=
  ∀ u v, |f u v| ≤ α * c s(u, v)

@[blueprint "def:is-demand"
  (statement := /-- A vector $\mathbf b : V \to \mathbb R$ is a demand if it sums to zero,
    $\sum_{v \in V} \mathbf b(v) = 0$. -/)
  (title := /-- Demand vector -/)
  (latexEnv := "definition")]
def is_demand (b : V → ℝ) : Prop :=
  ∑ v, b v = 0

@[blueprint "def:routes"
  (statement := /-- A flow $f$ routes a demand $\mathbf b$ if every vertex $v$ receives net flow
    $\mathbf b(v)$, i.e. $\sum_{u \in V} f(u,v) = \mathbf b(v)$ for all $v \in V$. -/)
  (title := /-- Routing a demand -/)
  (latexEnv := "definition")]
def routes (f : V → V → ℝ) (b : V → ℝ) : Prop :=
  ∀ v, ∑ u, f u v = b v

@[blueprint "def:mixes"
  (statement := /-- A vertex weighting $\mathbf d : V \to \mathbb R_{\ge 0}$ mixes in $G$ with
    congestion $\alpha$ if for every demand $\mathbf b$ with $|\mathbf b| \le \mathbf d$
    entrywise there exists a flow of congestion $\alpha$ routing $\mathbf b$. -/)
  (title := /-- Mixing of a vertex weighting -/)
  (latexEnv := "definition")]
def mixes (c : Sym2 V → ℝ) (α : ℝ) (d : V → ℝ) : Prop :=
  ∀ b : V → ℝ, is_demand b → (∀ v, |b v| ≤ d v) →
    ∃ f, is_flow f ∧ has_congestion c α f ∧ routes f b

@[blueprint "def:mixes-simultaneously"
  (statement := /-- A finite family of vertex weightings $\{\mathbf d_i : i \in s\}$ mixes
    simultaneously in $G$ with congestion $\alpha$ if for every choice of demands
    $\mathbf b_i$ with $|\mathbf b_i| \le \mathbf d_i$ for all $i \in s$, there exists a single flow
    of congestion $\alpha$ routing the aggregate demand $\sum_{i \in s} \mathbf b_i$. -/)
  (title := /-- Simultaneous mixing of a family -/)
  (latexEnv := "definition")]
def mixes_simultaneously (c : Sym2 V → ℝ) (α : ℝ) {ι : Type*} (d : ι → V → ℝ)
    (s : Finset ι) : Prop :=
  ∀ b : ι → V → ℝ, (∀ i ∈ s, is_demand (b i)) → (∀ i ∈ s, ∀ v, |b i v| ≤ d i v) →
    ∃ f, is_flow f ∧ has_congestion c α f ∧ routes f (fun v => ∑ i ∈ s, b i v)

@[blueprint "def:is-congestion-approx"
  (statement := /-- A collection $\mathcal C$ of subsets of $V$ is a congestion-approximator of
    quality $q$ if for every demand $\mathbf b$ satisfying $\bigl|\sum_{v \in C} \mathbf b(v)\bigr|
    \le \delta C$ for all $C \in \mathcal C$, there exists a flow of congestion $q$ routing
    $\mathbf b$. -/)
  (title := /-- Congestion-approximator of a given quality -/)
  (latexEnv := "definition")]
def is_congestion_approx (c : Sym2 V → ℝ) (𝒞 : Finset (Finset V)) (q : ℝ) : Prop :=
  ∀ b : V → ℝ, is_demand b → (∀ C ∈ 𝒞, |∑ v ∈ C, b v| ≤ delta_cut c C) →
    ∃ f, is_flow f ∧ has_congestion c q f ∧ routes f b

@[blueprint "def:refinement"
  (statement := /-- Given partitions $\mathcal P_1, \ldots$ of $V$ indexed by $\mathbb N$ and
    indices $i \le L$, the common refinement $\mathcal R_{\ge i}$ of
    $\mathcal P_i, \mathcal P_{i+1}, \ldots, \mathcal P_L$ is the infimum
    $\bigsqcap_{j \in [i,L]} \mathcal P_j$ in the lattice of finite partitions of $V$; its parts are
    the nonempty intersections $C_i \cap C_{i+1} \cap \cdots \cap C_L$ with $C_j \in \mathcal P_j$. -/)
  (title := /-- Common refinement of a range of partitions -/)
  (latexEnv := "definition")]
def refinement (P : ℕ → Finpartition (Finset.univ : Finset V)) (i L : ℕ) :
    Finpartition (Finset.univ : Finset V) :=
  (Finset.Icc i L).inf (fun j => P j)

@[blueprint "def:cut-collection"
  (statement := /-- The cut collection associated to partitions $\mathcal P_1, \ldots, \mathcal P_L$
    is $\mathcal C = \bigcup_{i \in [L]} \mathcal R_{\ge i}$, the union over $i \in \{1,\ldots,L\}$ of
    the parts of the common refinements $\mathcal R_{\ge i}$. -/)
  (title := /-- The collection of cuts -/)
  (latexEnv := "definition")]
def cut_collection (P : ℕ → Finpartition (Finset.univ : Finset V)) (L : ℕ) : Finset (Finset V) :=
  (Finset.Icc 1 L).biUnion (fun i => (refinement P i L).parts)

@[blueprint "def:valid-hierarchy"
  (statement := /-- Partitions $\mathcal P_1, \ldots, \mathcal P_L$ of $V$ form a valid hierarchy if
    $\mathcal P_1 = \bot$ is the partition into singletons $\{\{v\} : v \in V\}$ and
    $\mathcal P_L = \top$ is the partition $\{V\}$ into a single cluster. -/)
  (title := /-- Valid partition hierarchy -/)
  (latexEnv := "definition")]
def valid_hierarchy (P : ℕ → Finpartition (Finset.univ : Finset V)) (L : ℕ) : Prop :=
  P 1 = ⊥ ∧ P L = ⊤

@[blueprint "def:mixing-hypothesis"
  (statement := /-- The mixing hypothesis with congestion $\alpha$ holds for partitions
    $\mathcal P_1, \ldots, \mathcal P_L$ if for each $i \in [L-1]$ the family of vertex weightings
    $\bigl\{ \deg_{\partial\mathcal P_i \cup \partial C}\big|_C : C \in \mathcal P_{i+1} \bigr\}$
    mixes simultaneously in $G$ with congestion $\alpha$. -/)
  (title := /-- Mixing hypothesis of the hierarchy -/)
  (latexEnv := "definition")]
def mixing_hypothesis (c : Sym2 V → ℝ) (α : ℝ)
    (P : ℕ → Finpartition (Finset.univ : Finset V)) (L : ℕ) : Prop :=
  ∀ i ∈ Finset.Icc 1 (L - 1),
    mixes_simultaneously c α
      (fun C : Finset V =>
        restrict_to C
          (deg_weighted c (cross_union_ind (cross_partition_ind (P i)) (cross_cluster_ind C))))
      (P (i + 1)).parts

@[blueprint "def:directed-path"
  (statement := /-- A finite directed path on $V$ consists of a nonnegative integer $\ell$ and a
    sequence $(x_0,\ldots,x_\ell)$ of vertices. Repetitions are permitted; the directed edges
    traversed by the path are the ordered pairs $(x_j,x_{j+1})$ for $0\le j<\ell$. -/)
  (title := /-- Finite directed path -/)
  (latexEnv := "definition")]
structure directed_path (V : Type*) where
  length : ℕ
  vertex : Fin (length + 1) → V

@[blueprint "def:directed-path-edge-count"
  (statement := /-- For a directed path $p=(x_0,\ldots,x_\ell)$ and vertices $u,v$, the number
    $N_p(u,v)$ counts the indices $j<\ell$ for which $(x_j,x_{j+1})=(u,v)$. -/)
  (title := /-- Directed edge multiplicity along a path -/)
  (latexEnv := "definition")]
def directed_path_edge_count (p : directed_path V) (u v : V) : ℕ :=
  ∑ k : Fin p.length,
    if p.vertex (Fin.castSucc k) = u ∧ p.vertex (Fin.succ k) = v then 1 else 0

@[blueprint "def:path-transport"
  (statement := /-- A path transport on $V$ is a finite indexed family of directed paths
    $(p_k)_{k\in\operatorname{Fin}(N)}$ together with nonnegative real weights
    $(\lambda_k)_{k\in\operatorname{Fin}(N)}$. The weight $\lambda_k$ is the amount of flow
    carried by the path $p_k$. -/)
  (title := /-- Finite nonnegative weighted path family -/)
  (latexEnv := "definition")]
structure path_transport (V : Type*) where
  cardinality : ℕ
  path : Fin cardinality → directed_path V
  weight : Fin cardinality → ℝ
  weight_nonnegative : ∀ k, 0 ≤ weight k

@[blueprint "def:path-source-mass"
  (statement := /-- For a path transport $T$, its gross source mass at a vertex $v$ is
    $\operatorname{src}_T(v)=\sum_{k:x_0^k=v}\lambda_k$, where $x_0^k$ is the first vertex of
    the path $p_k$. -/)
  (title := /-- Gross source mass of a path transport -/)
  (latexEnv := "definition")]
def path_source_mass (T : path_transport V) (v : V) : ℝ :=
  ∑ k : Fin T.cardinality,
    if (T.path k).vertex ⟨0, Nat.zero_lt_succ _⟩ = v then T.weight k else 0

@[blueprint "def:path-receipt-mass"
  (statement := /-- For a path transport $T$, its gross receipt mass at a vertex $v$ is
    $\operatorname{rec}_T(v)=\sum_{k:x_{\ell_k}^k=v}\lambda_k$, where
    $x_{\ell_k}^k$ is the last vertex of the path $p_k$. -/)
  (title := /-- Gross receipt mass of a path transport -/)
  (latexEnv := "definition")]
def path_receipt_mass (T : path_transport V) (v : V) : ℝ :=
  ∑ k : Fin T.cardinality,
    if (T.path k).vertex (Fin.last (T.path k).length) = v then T.weight k else 0

@[blueprint "def:path-edge-load"
  (statement := /-- The undirected edge load of a path transport $T$ on $\{u,v\}$ is
    $\sum_k\lambda_k\bigl(N_{p_k}(u,v)+N_{p_k}(v,u)\bigr)$. Thus every traversal is charged
    positively, independently of its orientation and without cancellation. -/)
  (title := /-- Gross edge load of a path transport -/)
  (latexEnv := "definition")]
def path_edge_load (T : path_transport V) (u v : V) : ℝ :=
  ∑ k : Fin T.cardinality,
    T.weight k * ((directed_path_edge_count (T.path k) u v : ℝ) +
      (directed_path_edge_count (T.path k) v u : ℝ))

@[blueprint "def:path-induced-flow"
  (statement := /-- The signed flow induced by a path transport $T$ is
    $f_T(u,v)=\sum_k\lambda_k\bigl(N_{p_k}(u,v)-N_{p_k}(v,u)\bigr)$. It records the net
    oriented use of each edge, whereas \cref{def:path-edge-load} records its gross use. -/)
  (title := /-- Signed flow induced by a path transport -/)
  (latexEnv := "definition")]
def path_induced_flow (T : path_transport V) (u v : V) : ℝ :=
  ∑ k : Fin T.cardinality,
    T.weight k * ((directed_path_edge_count (T.path k) u v : ℝ) -
      (directed_path_edge_count (T.path k) v u : ℝ))

@[blueprint "def:directed-path-prefix"
  (statement := /-- If $p=(x_0,\ldots,x_\ell)$ and $0\le t\le\ell$, the prefix
    $p|_{[0,t]}$ is the directed path $(x_0,\ldots,x_t)$. -/)
  (title := /-- Prefix of a directed path -/)
  (latexEnv := "definition")]
def directed_path_prefix (p : directed_path V) (cutoff : Fin (p.length + 1)) :
    directed_path V where
  length := cutoff.val
  vertex := fun k =>
    p.vertex ⟨k.val,
      lt_of_lt_of_le k.isLt (Nat.succ_le_succ (Nat.le_of_lt_succ cutoff.isLt))⟩

@[blueprint "def:stopped-path-transport"
  (statement := /-- Let $T=(p_k,\lambda_k)$ be a path transport and choose, for every $k$, a
    stopping index $t_k$ on $p_k$. The stopped transport retains the weights $\lambda_k$ and
    replaces each $p_k$ by its prefix ending at $t_k$. -/)
  (title := /-- Path transport stopped at selected vertices -/)
  (latexEnv := "definition")]
def stopped_path_transport (T : path_transport V)
    (cutoff : (k : Fin T.cardinality) → Fin ((T.path k).length + 1)) : path_transport V where
  cardinality := T.cardinality
  path := fun k => directed_path_prefix (T.path k) (cutoff k)
  weight := T.weight
  weight_nonnegative := T.weight_nonnegative

@[blueprint "def:fractional-stopped-path-transport"
  (statement := /-- Let $T=(p_k,\lambda_k)_{k=0}^{N-1}$ be a path transport. Given
    nonnegative coefficients $\theta_k$ and stopping indices $t_k$ on the paths $p_k$, the
    fractional stopped transport $T[\theta,t]$ consists of the prefixes
    $p_k|_{[0,t_k]}$ with weights $\theta_k\lambda_k$. No upper bound on an individual
    coefficient is imposed by this definition. -/)
  (title := /-- Fractionally weighted stopped path transport -/)
  (latexEnv := "definition")]
def fractional_stopped_path_transport (T : path_transport V)
    (scale : Fin T.cardinality → ℝ) (hscale : ∀ k, 0 ≤ scale k)
    (cutoff : (k : Fin T.cardinality) → Fin ((T.path k).length + 1)) : path_transport V where
  cardinality := T.cardinality
  path := fun k => directed_path_prefix (T.path k) (cutoff k)
  weight := fun k => scale k * T.weight k
  weight_nonnegative := fun k => mul_nonneg (hscale k) (T.weight_nonnegative k)

@[blueprint "def:admissible-stopping-decomposition"
  (statement := /-- Fix a level $i$, a hierarchy
    $\mathcal P_1,\ldots,\mathcal P_L$, a congestion parameter $\beta$, a
    nonnegative weighted path transport $T=(p_k,\lambda_k)$, and an incoming
    residual demand $\mathbf a$. An admissible stopping decomposition consists
    of an outgoing residual $\mathbf a'$, correction demands
    $\mathbf q_{j,C}$, coefficients $\theta_{j,k,s}$, stopping indices
    $t_{j,k,s}$, orientations $\varepsilon_{j,k,s}$, and a stopped flow
    $g_{\mathrm{stop}}$.

    The residual $\mathbf a'$ is bounded by
    $\deg_{\partial\mathcal P_{i+1}}$ and, as a direct invariant, satisfies
    every cut inequality for every suffix refinement
    $\mathcal R_{\ge r}$ with $r\in[i+1,L]$. Each
    $\mathbf q_{j,C}$ is a demand supported on $C\in\mathcal P_j$ and is
    pointwise bounded by
    $(\deg_{\partial\mathcal P_{j-1}}+\deg_{\partial C})|_C$.
    Every coefficient belongs to $[0,1]$, and the total normalized
    coefficient charged to a fixed original path is at most $8L$.

    The endpoint identity
    \[
      \mathbf a-\mathbf a'
        -\sum_{j=i+1}^{L}\sum_{C\in\mathcal P_j}\mathbf q_{j,C}
      =\sum_{j=i+1}^{L}\sum_{k,s}
        \theta_{j,k,s}\lambda_k
        (\mathbf 1_{t_{j,k,s}}-\mathbf 1_{\varepsilon_{j,k,s}})
    \]
    holds vertexwise. Finally, $g_{\mathrm{stop}}$ routes this endpoint
    demand and has congestion at most $8L\beta$. -/)
  (title := /-- Existential stopped-path decomposition data -/)
  (latexEnv := "definition")]
def admissible_stopping_decomposition (c : Sym2 V → ℝ) (β : ℝ)
    (P : ℕ → Finpartition (Finset.univ : Finset V)) (L i : ℕ)
    (T : path_transport V) (a : V → ℝ) : Prop :=
  ∃ (a' : V → ℝ) (q : ℕ → Finset V → V → ℝ)
    (scale : ℕ → Fin T.cardinality → Fin 8 → ℝ)
    (cutoff : (j : ℕ) → (k : Fin T.cardinality) → Fin 8 →
      Fin ((T.path k).length + 1))
    (forward : ℕ → Fin T.cardinality → Fin 8 → Bool)
    (gstop : V → V → ℝ),
    is_demand a' ∧
    (∀ v, |a' v| ≤
      deg_weighted c (cross_partition_ind (P (i + 1))) v) ∧
    (∀ r ∈ Finset.Icc (i + 1) L, ∀ D ∈ (refinement P r L).parts,
      |∑ v ∈ D, a' v| ≤ delta_cut c D) ∧
    (∀ j ∈ Finset.Icc (i + 1) L, ∀ C ∈ (P j).parts,
      is_demand (q j C) ∧
      (∀ v, v ∉ C → q j C v = 0) ∧
      (∀ v, |q j C v| ≤
        restrict_to C
          (fun w =>
            deg_weighted c (cross_partition_ind (P (j - 1))) w +
            deg_weighted c (cross_cluster_ind C) w) v)) ∧
    (∀ j ∈ Finset.Icc (i + 1) L, ∀ k, ∀ s : Fin 8,
      0 ≤ scale j k s ∧ scale j k s ≤ 1) ∧
    (∀ k, (∑ j ∈ Finset.Icc (i + 1) L, ∑ s : Fin 8, scale j k s) ≤
      8 * (L : ℝ)) ∧
    (∀ v, a v - a' v -
      ∑ j ∈ Finset.Icc (i + 1) L, ∑ C ∈ (P j).parts, q j C v =
        ∑ j ∈ Finset.Icc (i + 1) L,
          ∑ k : Fin T.cardinality, ∑ s : Fin 8,
            scale j k s * T.weight k *
              ((if (T.path k).vertex (cutoff j k s) = v then (1 : ℝ) else 0) -
                if (if forward j k s = true then
                    (T.path k).vertex
                      ⟨0, Nat.zero_lt_succ (T.path k).length⟩
                  else (T.path k).vertex (Fin.last (T.path k).length)) = v
                then (1 : ℝ) else 0)) ∧
    is_flow gstop ∧
    routes gstop
      (fun v => a v - a' v -
        ∑ j ∈ Finset.Icc (i + 1) L, ∑ C ∈ (P j).parts, q j C v) ∧
    has_congestion c (8 * (L : ℝ) * β) gstop

@[blueprint "def:transport-endpoint-coverage"
  (statement := /-- Fix a level $i$ and a nonnegative weighted path transport
    $T=(p_k,\lambda_k)$. The transport has endpoint coverage with congestion
    $\beta$ if every demand $\mathbf a$ bounded by
    $\deg_{\partial\mathcal P_i}$ and satisfying the cut inequalities for all
    suffix refinements $\mathcal R_{\ge r}$, $r\in[i+1,L]$, admits an
    admissible stopping decomposition
    (\cref{def:admissible-stopping-decomposition}). Thus endpoint coverage is
    existential: it supplies the outgoing residual, corrections, stopping
    coefficients, cutoffs, orientations, endpoint identity, and stopped flow,
    including the suffix-refinement cut bounds as an explicit invariant. -/)
  (title := /-- Existential endpoint coverage for stopped path redistribution -/)
  (latexEnv := "definition")]
def transport_endpoint_coverage (c : Sym2 V → ℝ) (β : ℝ)
    (P : ℕ → Finpartition (Finset.univ : Finset V)) (L i : ℕ)
    (T : path_transport V) : Prop :=
  ∀ a : V → ℝ,
    is_demand a →
    (∀ v, |a v| ≤ deg_weighted c (cross_partition_ind (P i)) v) →
    (∀ r ∈ Finset.Icc (i + 1) L, ∀ D ∈ (refinement P r L).parts,
      |∑ v ∈ D, a v| ≤ delta_cut c D) →
    admissible_stopping_decomposition c β P L i T a

@[blueprint "def:flow-hypothesis"
  (statement := /-- The flow hypothesis with congestion $\beta$ holds for partitions
    $\mathcal P_1,\ldots,\mathcal P_L$ if, for every $i\in[L-1]$, there is a finite
    nonnegative weighted path family $T_i$ (\cref{def:path-transport}) such that every
    positive-weight path has distinct initial and terminal vertices. Its gross source at
    every vertex $v$ is exactly $\deg_{\partial\mathcal P_{i+1}}(v)$, its gross receipt at
    $v$ lies in $[0,\tfrac12\deg_{\partial\mathcal P_i}(v)]$, and its gross load on each
    edge $\{u,v\}$ is at most $\beta c(\{u,v\})$ (\cref{def:path-source-mass,
    def:path-receipt-mass, def:path-edge-load}). In addition, $T_i$ has endpoint
    coverage at level $i$ (\cref{def:transport-endpoint-coverage}): every
    admissible residual demand can be decomposed into a next-level residual,
    part-supported correction demands, and stopped path portions with the
    prescribed conservation and congestion bounds. -/)
  (title := /-- Flow hypothesis of the hierarchy -/)
  (latexEnv := "definition")]
def flow_hypothesis (c : Sym2 V → ℝ) (β : ℝ)
    (P : ℕ → Finpartition (Finset.univ : Finset V)) (L : ℕ) : Prop :=
  ∀ i ∈ Finset.Icc 1 (L - 1),
    ∃ T : path_transport V,
      (∀ k, 0 < T.weight k →
        (T.path k).vertex ⟨0, Nat.zero_lt_succ (T.path k).length⟩ ≠
          (T.path k).vertex (Fin.last (T.path k).length)) ∧
      (∀ v, path_source_mass T v =
        deg_weighted c (cross_partition_ind (P (i + 1))) v) ∧
      (∀ v, 0 ≤ path_receipt_mass T v ∧
        path_receipt_mass T v ≤
          (1 / 2) * deg_weighted c (cross_partition_ind (P i)) v) ∧
      (∀ u v, path_edge_load T u v ≤ β * c s(u, v)) ∧
      transport_endpoint_coverage c β P L i T

@[blueprint "thm:transport-endpoint-coverage-of-flow-hypothesis"
  (statement := /-- Let $c : \operatorname{Sym}^2(V)\to\mathbb R$ be
    nonnegative, let $\beta\ge 1$ and $L\ge 1$, and let
    $\mathcal P : \mathbb N\to\operatorname{Finpartition}(V)$ satisfy
    $\mathcal P_L=\top$. Fix $i\in[1,L-1]$ and assume the flow hypothesis
    with congestion $\beta$ (\cref{def:flow-hypothesis}). Then there exists a
    path transport $T$ such that every positive-weight path has distinct
    initial and terminal vertices, the source mass at every $v$ equals
    $\deg_{\partial\mathcal P_{i+1}}(v)$, the receipt mass at every $v$ lies
    in $[0,\tfrac12\deg_{\partial\mathcal P_i}(v)]$, the load on every edge
    $\{u,v\}$ is at most $\beta c(\{u,v\})$, and $T$ has endpoint coverage
    at level $i$ (\cref{def:path-source-mass,def:path-receipt-mass,
    def:path-edge-load,def:transport-endpoint-coverage}). -/)
  (proof := /-- Specialize the flow hypothesis
    (\cref{def:flow-hypothesis}) at $i$. This yields a path transport $T_i$
    whose positive-weight paths have distinct endpoints, whose source mass is
    $\deg_{\partial\mathcal P_{i+1}}$, whose receipt mass lies between $0$ and
    $\tfrac12\deg_{\partial\mathcal P_i}$, and whose edge load is bounded by
    $\beta c$. The same witness includes endpoint coverage at level $i$
    (\cref{def:transport-endpoint-coverage}), so all five asserted properties
    follow directly. -/)
  (title := /-- Extracting a flow witness with endpoint coverage -/)
  (latexEnv := "theorem")]
theorem transport_endpoint_coverage_of_flow_hypothesis (c : Sym2 V → ℝ)
    (β : ℝ) (P : ℕ → Finpartition (Finset.univ : Finset V)) (L i : ℕ)
    (hc : ∀ e, 0 ≤ c e) (hβ : 1 ≤ β) (hL : 1 ≤ L)
    (hPL : P L = ⊤) (hi : i ∈ Finset.Icc 1 (L - 1))
    (hflow : flow_hypothesis c β P L) :
    ∃ T : path_transport V,
      (∀ k, 0 < T.weight k →
        (T.path k).vertex ⟨0, Nat.zero_lt_succ (T.path k).length⟩ ≠
          (T.path k).vertex (Fin.last (T.path k).length)) ∧
      (∀ v, path_source_mass T v =
        deg_weighted c (cross_partition_ind (P (i + 1))) v) ∧
      (∀ v, 0 ≤ path_receipt_mass T v ∧
        path_receipt_mass T v ≤
          (1 / 2) * deg_weighted c (cross_partition_ind (P i)) v) ∧
      (∀ u v, path_edge_load T u v ≤ β * c s(u, v)) ∧
      transport_endpoint_coverage c β P L i T := by
  exact hflow i hi

@[blueprint "lem:deg-boundary-top-zero"
  (statement := /-- Let $\mathcal P_L = \top$ be the partition $\{V\}$ consisting of the single
    cluster $V$. Then $\deg_{\partial\mathcal P_L}(v) = 0$ for every vertex $v \in V$. -/)
  (proof := /-- Since $\mathcal P_L = \{V\}$, both endpoints of every edge $e$ lie in the same
    unique cluster $V$, so $e$ does not cross the boundary of $\mathcal P_L$ and
    $\mathrm{crossPartitionInd}(\mathcal P_L, e) = 0$ for all $e$ (\cref{def:cross-partition-ind}).
    Hence every summand of $\deg_{\partial\mathcal P_L}(v)$ (\cref{def:deg-weighted}) vanishes, and the
    total is $0$. -/)
  (title := /-- Boundary degree of the top partition vanishes -/)
  (latexEnv := "lemma")]
lemma deg_boundary_top_zero (c : Sym2 V → ℝ)
    (P : ℕ → Finpartition (Finset.univ : Finset V)) (L : ℕ) (hPL : P L = ⊤) :
    ∀ v, deg_weighted c (cross_partition_ind (P L)) v = 0 := by
  intro v
  have hw : cross_partition_ind (P L) = fun _ => (0 : ℝ) := by
    funext e
    rw [hPL]
    unfold cross_partition_ind
    rw [if_neg]
    rintro ⟨C, hC, hCe⟩
    have hCu : C = Finset.univ := Finset.mem_singleton.1 (Finpartition.parts_top_subset _ hC)
    subst hCu
    revert hCe
    refine Sym2.ind (fun u v => ?_) e
    simp [cross_cluster_ind]
  unfold deg_weighted
  rw [hw]
  simp

@[blueprint "lem:bottom-residual-bound"
  (statement := /-- Let $V$ be finite, let
    $c : \operatorname{Sym}^2(V) \to \mathbb R$ satisfy $c(e)\ge 0$ for every $e$, and let
    $P : \mathbb N\to\operatorname{Part}(V)$ be a sequence of partitions. Fix
    $L\in\mathbb N$ with $1\le L$, and suppose that $P_1=\bot$ is the singleton partition.
    If $\mathbf b:V\to\mathbb R$ satisfies
    \[
      \left|\sum_{v\in C}\mathbf b(v)\right|\le\delta C
    \]
    for every $C$ in the cut collection
    $\mathcal C=\bigcup_{i\in[L]}\mathcal R_{\ge i}$
    (\cref{def:delta-cut, def:cut-collection}), then, for every $v\in V$,
    \[
      |\mathbf b(v)|\le\deg_{\partial P_1}(v).
    \]
    Here the right-hand side is the weighted degree defined using the boundary indicator of
    $P_1$ (\cref{def:cross-partition-ind, def:deg-weighted}). -/)
  (proof := /-- Because $1\le L$, the index $1$ belongs to $[1,L]$. The common refinement
    $\mathcal R_{\ge1}$ is the infimum of the partitions with indices in this interval
    (\cref{def:refinement}). Since one of these partitions is $P_1=\bot$, this infimum is
    $\bot$. Thus $\{v\}$ is a part of $\mathcal R_{\ge1}$, and hence
    $\{v\}\in\mathcal C$ for every $v\in V$ by the definition of the cut collection
    (\cref{def:cut-collection}). Applying the assumed cut inequality to $\{v\}$ gives
    \[
      |\mathbf b(v)|=\left|\sum_{u\in\{v\}}\mathbf b(u)\right|
      \le\delta\{v\}.
    \]
    To compare the two quantities on the right, represent an unordered pair as $e=\{u,w\}$.
    If $u=w$, then both its singleton-cut indicator and its singleton-partition boundary
    indicator vanish. If $u\ne w$, then the singleton-partition indicator is $1$, and the
    singleton-cut indicator for $\{v\}$ is $1$ exactly when $v=u$ or $v=w$
    (\cref{def:cross-cluster-ind, def:cross-partition-ind}). Consequently the summands in the
    definitions of cut capacity and weighted degree agree for every unordered pair
    (\cref{def:delta-cut, def:deg-weighted}), so
    $\delta\{v\}=\deg_{\partial P_1}(v)$. Substitution in the preceding inequality proves the
    claim. -/)
  (title := /-- The cut constraints bound the initial residual -/)
  (latexEnv := "lemma")]
lemma bottom_residual_bound (c : Sym2 V → ℝ)
    (P : ℕ → Finpartition (Finset.univ : Finset V)) (L : ℕ)
    (hc : ∀ e, 0 ≤ c e) (hL : 1 ≤ L) (hP1 : P 1 = ⊥)
    (b : V → ℝ)
    (hcut : ∀ C ∈ cut_collection P L, |∑ v ∈ C, b v| ≤ delta_cut c C) :
    ∀ v, |b v| ≤ deg_weighted c (cross_partition_ind (P 1)) v := by
  intro v
  have h1 : 1 ∈ Finset.Icc 1 L := Finset.mem_Icc.mpr ⟨le_rfl, hL⟩
  have href : refinement P 1 L = ⊥ := by
    apply le_antisymm
    · simpa [refinement, hP1] using
        (Finset.inf_le (f := fun j => P j) h1)
    · exact bot_le
  have hsingle : {v} ∈ cut_collection P L := by
    simp only [cut_collection, Finset.mem_biUnion]
    exact ⟨1, h1, by simp [href]⟩
  have hv := hcut {v} hsingle
  have hdelta : delta_cut c {v} =
      deg_weighted c (cross_partition_ind (P 1)) v := by
    rw [hP1]
    unfold delta_cut deg_weighted
    apply Finset.sum_congr rfl
    intro e _
    refine Sym2.ind (fun u w => ?_) e
    by_cases huw : u = w
    · subst w
      simp [cross_cluster_ind, cross_partition_ind]
    · have hex : ∃ a, |(if u = a then (1 : ℝ) else 0) -
          (if w = a then 1 else 0)| = 1 := ⟨u, by simp [Ne.symm huw]⟩
      by_cases hvu : v = u
      · simp [cross_cluster_ind, cross_partition_ind, hvu, Ne.symm huw, hex]
      · by_cases hvw : v = w
        · simp [cross_cluster_ind, cross_partition_ind, hvw, huw, hex]
        · simp [cross_cluster_ind, cross_partition_ind, hvu, hvw,
            Ne.symm hvu, Ne.symm hvw]
  simpa [hdelta] using hv

@[blueprint "def:stopped-piece-demand"
  (statement := /-- Let $T=(p_k,\lambda_k)$ be a path transport, let
    $\theta\in\mathbb R$, let $t$ be an index of $p_k$, and choose an orientation.
    In the forward orientation the stopped piece runs from the initial vertex of
    $p_k$ to $p_k(t)$; in the reverse orientation it runs from the terminal vertex
    of $p_k$ to $p_k(t)$. Its endpoint demand is $\theta\lambda_k$ at $p_k(t)$
    minus $\theta\lambda_k$ at the corresponding oriented source. -/)
  (title := /-- Endpoint demand of one oriented stopped path piece -/)
  (latexEnv := "definition")]
def stopped_piece_demand (T : path_transport V) (k : Fin T.cardinality)
    (scale : ℝ) (cutoff : Fin ((T.path k).length + 1))
    (forward : Bool) (v : V) : ℝ :=
  scale * T.weight k *
    ((if (T.path k).vertex cutoff = v then (1 : ℝ) else 0) -
      if (if forward = true then
          (T.path k).vertex ⟨0, Nat.zero_lt_succ (T.path k).length⟩
        else (T.path k).vertex (Fin.last (T.path k).length)) = v
      then (1 : ℝ) else 0)

@[blueprint "def:stopped-piece-flow"
  (statement := /-- In the notation of
    \cref{def:stopped-piece-demand}, the signed flow of the oriented stopped
    piece is $\theta\lambda_k$ times the signed edge count on the prefix from the
    initial vertex to the cutoff in the forward orientation. In the reverse
    orientation it is $\theta\lambda_k$ times the signed edge count on the suffix
    from the terminal vertex back to the cutoff. -/)
  (title := /-- Signed flow of one oriented stopped path piece -/)
  (latexEnv := "definition")]
def stopped_piece_flow (T : path_transport V) (k : Fin T.cardinality)
    (scale : ℝ) (cutoff : Fin ((T.path k).length + 1))
    (forward : Bool) (u v : V) : ℝ :=
  if forward = true then
    scale * T.weight k *
      ((directed_path_edge_count (directed_path_prefix (T.path k) cutoff) u v : ℝ) -
        (directed_path_edge_count (directed_path_prefix (T.path k) cutoff) v u : ℝ))
  else
    scale * T.weight k *
      (((directed_path_edge_count (T.path k) v u : ℝ) -
          (directed_path_edge_count (directed_path_prefix (T.path k) cutoff) v u : ℝ)) -
        ((directed_path_edge_count (T.path k) u v : ℝ) -
          (directed_path_edge_count (directed_path_prefix (T.path k) cutoff) u v : ℝ)))

@[blueprint "def:residual-stopping-certificate"
  (statement := /-- Fix $i\in[1,L-1]$, a hierarchy
    $\mathcal P_1,\ldots,\mathcal P_L$, a congestion parameter $\beta$, and
    an initial residual demand $\mathbf a$. A multilevel residual-stopping
    certificate consists of a terminal residual $\mathbf a'$, a correction
    $\mathbf q_{j,C}$ for every $j\in[i+1,L]$ and
    $C\in\mathcal P_j$, and an aggregate stopped-path flow
    $g_{\mathrm{stop}}$.

    The terminal residual is a demand bounded by
    $\deg_{\partial\mathcal P_{i+1}}$ and satisfies every cut inequality for
    the suffix refinements $\mathcal R_{\ge r}$, $i+1\le r\le L$. Each
    $\mathbf q_{j,C}$ is a demand supported on $C$ and obeys
    \[
      |\mathbf q_{j,C}|
      \le
      \bigl(\deg_{\partial\mathcal P_{j-1}}+
             \deg_{\partial C}\bigr)|_C.
    \]
    Thus the correction at stage $j$ is controlled by precisely the weighting
    available to the level-$(j-1)$ simultaneous mixing hypothesis. In
    particular, corrections at later levels may transfer imbalance between
    distinct parts of $\mathcal P_{i+1}$ when the intervening partitions are
    not nested.

    Finally, $g_{\mathrm{stop}}$ has congestion at most $8L\beta$ and routes
    the part of $\mathbf a-\mathbf a'$ left after all level-indexed
    corrections:
    \[
      \operatorname{div}g_{\mathrm{stop}}
      =\mathbf a-\mathbf a'
       -\sum_{j=i+1}^{L}\sum_{C\in\mathcal P_j}\mathbf q_{j,C}.
    \]
    -/)
  (title := /-- Multilevel certificate for residual stopping and correction -/)
  (latexEnv := "definition")]
def residual_stopping_certificate (c : Sym2 V → ℝ)
    (β : ℝ) (P : ℕ → Finpartition (Finset.univ : Finset V))
    (L i : ℕ) (a : V → ℝ) : Prop :=
  ∃ (a' : V → ℝ) (q : ℕ → Finset V → V → ℝ)
    (gstop : V → V → ℝ),
    is_demand a' ∧
    (∀ v, |a' v| ≤ deg_weighted c (cross_partition_ind (P (i + 1))) v) ∧
    (∀ j ∈ Finset.Icc (i + 1) L, ∀ C ∈ (refinement P j L).parts,
      |∑ v ∈ C, a' v| ≤ delta_cut c C) ∧
    (∀ j ∈ Finset.Icc (i + 1) L, ∀ C ∈ (P j).parts,
      is_demand (q j C) ∧
      (∀ v, v ∉ C → q j C v = 0) ∧
      (∀ v, |q j C v| ≤
        restrict_to C
          (fun w =>
            deg_weighted c (cross_partition_ind (P (j - 1))) w +
            deg_weighted c (cross_cluster_ind C) w) v)) ∧
    is_flow gstop ∧
    routes gstop
      (fun v => a v - a' v -
        ∑ j ∈ Finset.Icc (i + 1) L, ∑ C ∈ (P j).parts, q j C v) ∧
    has_congestion c (8 * (L : ℝ) * β) gstop

@[blueprint "lem:residual-stopping-certificate-exists"
  (statement := /-- Let $V$ be a finite vertex set, let
    $c:\operatorname{Sym}^2(V)\to\mathbb R$ be nonnegative, and let
    $\beta\ge1$. Let $P:\mathbb N\to\operatorname{Part}(V)$ be a sequence
    of partitions, let $L\ge1$ with $P_L=\top$, and fix
    $i\in[1,L-1]$. Suppose that the flow hypothesis with congestion $\beta$
    holds for the whole hierarchy (\cref{def:flow-hypothesis}); in particular,
    its level-$i$ transport has endpoint coverage
    (\cref{def:transport-endpoint-coverage}). Let
    $\mathbf a$ be a demand satisfying
    $|\mathbf a|\le\deg_{\partial P_i}$ and
    \[
      |\mathbf a(C)|\le\delta C
      \qquad
      \bigl(j\in[i+1,L],\ C\in\mathcal R_{\ge j}\bigr).
    \]
    Then there exists a multilevel residual-stopping certificate
    (\cref{def:residual-stopping-certificate}) for $\mathbf a$. In particular,
    it records a terminal residual bounded by
    $\deg_{\partial P_{i+1}}$, level-indexed correction demands supported on
    parts of $P_j$ for every $j\in[i+1,L]$, and an aggregate stopped flow of
    congestion at most $8L\beta$. -/)
  (proof := /-- Specialize the hierarchy flow hypothesis
    (\cref{def:flow-hypothesis}) at $i$ and choose its path transport $T_i$.
    Besides the four marginal path conditions, this witness carries endpoint
    coverage at level $i$ (\cref{def:transport-endpoint-coverage}).
    Apply that coverage property to $\mathbf a$. The hypotheses that
    $\mathbf a$ is a demand, that
    $|\mathbf a|\le\deg_{\partial P_i}$, and that
    $|\mathbf a(D)|\le\delta D$ for every
    $r\in[i+1,L]$ and $D\in\mathcal R_{\ge r}$ are precisely its three
    premises. It therefore yields an admissible stopping decomposition
    (\cref{def:admissible-stopping-decomposition}).

    Let $\mathbf a'$, $\mathbf q$, and $g_{\mathrm{stop}}$ be the residual,
    correction demands, and stopped flow in this decomposition. Discard the
    auxiliary stopping coefficients, cutoff indices, and orientations. The
    remaining clauses state that $\mathbf a'$ is a demand bounded by
    $\deg_{\partial P_{i+1}}$ and obeys every required suffix-refinement cut
    inequality; each $\mathbf q_{j,C}$ is a demand supported on $C$ with the
    required pointwise bound; and $g_{\mathrm{stop}}$ routes
    \[
      \mathbf a-\mathbf a'
       -\sum_{j=i+1}^{L}\sum_{C\in P_j}\mathbf q_{j,C}
    \]
    with congestion at most $8L\beta$. These are exactly the clauses of the
    residual stopping certificate
    (\cref{def:residual-stopping-certificate}). -/)
  (title := /-- Existence of a multilevel stopping certificate -/)
  (latexEnv := "lemma")]
lemma residual_stopping_certificate_exists (c : Sym2 V → ℝ)
    (β : ℝ) (P : ℕ → Finpartition (Finset.univ : Finset V)) (L i : ℕ)
    (hc : ∀ e, 0 ≤ c e) (hβ : 1 ≤ β)
    (hflow : flow_hypothesis c β P L)
    (hL : 1 ≤ L) (hPL : P L = ⊤) (hi : i ∈ Finset.Icc 1 (L - 1))
    (a : V → ℝ) (ha : is_demand a)
    (habound : ∀ v, |a v| ≤ deg_weighted c (cross_partition_ind (P i)) v)
    (hacut : ∀ j ∈ Finset.Icc (i + 1) L, ∀ C ∈ (refinement P j L).parts,
      |∑ v ∈ C, a v| ≤ delta_cut c C) :
    residual_stopping_certificate c β P L i a := by
  rcases hflow i hi with ⟨T, _, _, _, _, hcover⟩
  rcases hcover a ha habound hacut with
    ⟨a', q, scale, cutoff, forward, gstop, ha', habound', hacut', hq,
      _, _, _, hgstop, hroutes, hcong⟩
  exact ⟨a', q, gstop, ha', habound', hacut', hq, hgstop, hroutes, hcong⟩

@[blueprint "thm:residual-transfer-step"
  (statement := /-- Let $L\ge1$, let $c : \operatorname{Sym}^2(V)\to\mathbb R$ satisfy
    $c(e)\ge0$ for every edge $e$, and let $\alpha,\beta\ge1$. Let
    $\mathcal P_1,\ldots,\mathcal P_L$ be partitions of $V$ such that
    $\mathcal P_L=\top=\{V\}$. Fix $i\in[1,L-1]$ and suppose both the
    simultaneous mixing hypothesis with congestion $\alpha$
    (\cref{def:mixing-hypothesis}) and the canonical flow hypothesis with
    congestion $\beta$ (\cref{def:flow-hypothesis}) hold for the entire
    hierarchy, so each witnessing transport also has endpoint coverage at its
    level. Let
    $\mathbf d_i=\deg_{\partial\mathcal P_i}$. If a demand $\mathbf a$ satisfies
    $|\mathbf a|\le\mathbf d_i$ and the cut inequalities on every part of every
    $\mathcal R_{\ge j}$, $i+1\le j\le L$, then there are a demand
    $\mathbf a^+$ and a flow $g$ such that
    $|\mathbf a^+|\le\mathbf d_{i+1}$, the same future-refinement cut inequalities hold
    for $\mathbf a^+$, $g$ routes $\mathbf a-\mathbf a^+$, and $g$ has congestion at
    most $16L\alpha\beta$. -/)
  (proof := /-- Apply \cref{lem:residual-stopping-certificate-exists} to
    $\mathbf a$ and the endpoint-covered flow hypothesis. We obtain a terminal residual
    $\mathbf a^+$, correction demands
    $\mathbf q_{j,C}$ for $j\in[i+1,L]$ and $C\in\mathcal P_j$, and a
    stopped flow $g_{\mathrm{stop}}$. The certificate gives all asserted
    properties of $\mathbf a^+$ and
    \[
      \operatorname{div}g_{\mathrm{stop}}
      =\mathbf a-\mathbf a^+
       -\sum_{j=i+1}^{L}\sum_{C\in\mathcal P_j}\mathbf q_{j,C},
      \qquad
      \operatorname{cong}(g_{\mathrm{stop}})\le8L\beta.
    \]

    Fix $j\in[i+1,L]$. For every $C\in\mathcal P_j$, the certificate says
    that $\mathbf q_{j,C}$ is a demand supported on $C$ and that
    \[
      |\mathbf q_{j,C}|
      \le
      \bigl(\deg_{\partial\mathcal P_{j-1}}+
             \deg_{\partial C}\bigr)|_C.
    \]
    Nonnegativity of $c$ implies that one half of the right-hand side is
    bounded by
    $\deg_{\partial\mathcal P_{j-1}\cup\partial C}|_C$.
    Since $j-1\in[1,L-1]$, the level-$(j-1)$ simultaneous mixing hypothesis
    supplies a flow $h_j$ routing
    $\frac12\sum_{C\in\mathcal P_j}\mathbf q_{j,C}$ with congestion at
    most $\alpha$. Hence $2h_j$ routes the unscaled sum and has congestion at
    most $2\alpha$.

    Let $g_{\mathrm{mix}}=\sum_{j=i+1}^{L}2h_j$. There are at most $L$
    summands, so $g_{\mathrm{mix}}$ has congestion at most $2L\alpha$ and
    routes the sum of all level-indexed corrections. Thus
    $g=g_{\mathrm{stop}}+g_{\mathrm{mix}}$ is a flow routing
    $\mathbf a-\mathbf a^+$. For every $u,v$,
    \[
      |g(u,v)|\le(8L\beta+2L\alpha)c(\{u,v\})
        \le16L\alpha\beta c(\{u,v\}),
    \]
    since $L,\alpha,\beta\ge1$. This proves all the asserted properties. -/)
  (title := /-- Transfer a residual through one hierarchy level -/)
  (latexEnv := "theorem")]
theorem residual_transfer_step (c : Sym2 V → ℝ) (α β : ℝ)
    (P : ℕ → Finpartition (Finset.univ : Finset V)) (L i : ℕ)
    (hc : ∀ e, 0 ≤ c e) (hα : 1 ≤ α) (hβ : 1 ≤ β) (hL : 1 ≤ L)
    (hPL : P L = ⊤)
    (hi : i ∈ Finset.Icc 1 (L - 1))
    (hmix : mixing_hypothesis c α P L)
    (hflow : flow_hypothesis c β P L)
    (a : V → ℝ) (ha : is_demand a)
    (habound : ∀ v, |a v| ≤ deg_weighted c (cross_partition_ind (P i)) v)
    (hacut : ∀ j ∈ Finset.Icc (i + 1) L, ∀ C ∈ (refinement P j L).parts,
      |∑ v ∈ C, a v| ≤ delta_cut c C) :
    ∃ (a' : V → ℝ) (g : V → V → ℝ),
      is_demand a' ∧
      (∀ v, |a' v| ≤ deg_weighted c (cross_partition_ind (P (i + 1))) v) ∧
      (∀ j ∈ Finset.Icc (i + 1) L, ∀ C ∈ (refinement P j L).parts,
        |∑ v ∈ C, a' v| ≤ delta_cut c C) ∧
      is_flow g ∧ has_congestion c (16 * (L : ℝ) * α * β) g ∧
      routes g (fun v => a v - a' v) := by
  rcases residual_stopping_certificate_exists c β P L i hc hβ hflow hL hPL hi a ha
      habound hacut with
    ⟨a', q, gstop, ha', habound', hacut', hq, hgstop, hroutes, hcong⟩
  have hhalf_degree (j : ℕ) (C : Finset V) (v : V) :
      (1 / 2 : ℝ) *
          (deg_weighted c (cross_partition_ind (P (j - 1))) v +
            deg_weighted c (cross_cluster_ind C) v) ≤
        deg_weighted c
          (cross_union_ind (cross_partition_ind (P (j - 1))) (cross_cluster_ind C)) v := by
    simp only [deg_weighted, ← Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    by_cases hve : v ∈ e
    · simp only [hve, if_pos]
      induction e using Sym2.inductionOn with
      | _ x y =>
          by_cases hp : ∃ D ∈ (P (j - 1)).parts, cross_cluster_ind D s(x, y) = 1
          · have hpart : cross_partition_ind (P (j - 1)) s(x, y) = 1 := by
              simp [cross_partition_ind, hp]
            by_cases hx : x ∈ C <;> by_cases hy : y ∈ C <;>
              simp [hpart, cross_union_ind, cross_cluster_ind, hx, hy] <;>
              nlinarith [hc s(x, y)]
          · have hpart : cross_partition_ind (P (j - 1)) s(x, y) = 0 := by
              simp [cross_partition_ind, hp]
            by_cases hx : x ∈ C <;> by_cases hy : y ∈ C <;>
              simp [hpart, cross_union_ind, cross_cluster_ind, hx, hy] <;>
              nlinarith [hc s(x, y)]
    · simp [hve]
  unfold mixing_hypothesis at hmix
  have hlevel : ∀ j ∈ Finset.Icc (i + 1) L,
      ∃ g : V → V → ℝ,
        is_flow g ∧ has_congestion c (2 * α) g ∧
          routes g (fun v => ∑ C ∈ (P j).parts, q j C v) := by
    intro j hj
    have hjpred : j - 1 ∈ Finset.Icc 1 (L - 1) := by
      simp only [Finset.mem_Icc] at hi hj ⊢
      omega
    have hjpos : 1 ≤ j := by
      simp only [Finset.mem_Icc] at hi hj
      omega
    have hm := hmix (j - 1) hjpred
    simp only [Nat.sub_add_cancel hjpos] at hm
    rcases hm (fun C v => (1 / 2 : ℝ) * q j C v) (by
        intro C hC
        have hqsum := (hq j hj C hC).1
        unfold is_demand at hqsum
        unfold is_demand
        rw [← Finset.mul_sum]
        rw [hqsum, mul_zero]) (by
        intro C hC v
        rcases hq j hj C hC with ⟨hqdem, hqsupp, hqbound⟩
        by_cases hv : v ∈ C
        · rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          calc
            (1 / 2 : ℝ) * |q j C v| ≤
                (1 / 2 : ℝ) *
                  restrict_to C
                    (fun w =>
                      deg_weighted c (cross_partition_ind (P (j - 1))) w +
                        deg_weighted c (cross_cluster_ind C) w) v :=
              mul_le_mul_of_nonneg_left (hqbound v) (by norm_num)
            _ = (1 / 2 : ℝ) *
                  (deg_weighted c (cross_partition_ind (P (j - 1))) v +
                    deg_weighted c (cross_cluster_ind C) v) := by
              simp [restrict_to, hv]
            _ ≤ deg_weighted c
                  (cross_union_ind (cross_partition_ind (P (j - 1)))
                    (cross_cluster_ind C)) v := hhalf_degree j C v
            _ = restrict_to C
                  (deg_weighted c
                    (cross_union_ind (cross_partition_ind (P (j - 1)))
                      (cross_cluster_ind C))) v := by
              simp [restrict_to, hv]
        · have hz := hqsupp v hv
          simp [hz, restrict_to, hv]) with
      ⟨g, hgflow, hgcong, hgroutes⟩
    refine ⟨fun u v => 2 * g u v, ?_, ?_, ?_⟩
    · intro u v
      change 2 * g u v = -(2 * g v u)
      rw [hgflow u v, hgflow v u]
      ring
    · intro u v
      rw [abs_mul]
      norm_num
      nlinarith [hgcong u v]
    · intro v
      calc
        ∑ u, 2 * g u v = 2 * ∑ u, g u v := by rw [Finset.mul_sum]
        _ = 2 * ∑ C ∈ (P j).parts, (1 / 2 : ℝ) * q j C v := by
          rw [hgroutes v]
        _ = ∑ C ∈ (P j).parts, q j C v := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro C hC
          ring
  have hlevel' : ∀ j, ∃ g : V → V → ℝ,
      j ∈ Finset.Icc (i + 1) L →
        is_flow g ∧ has_congestion c (2 * α) g ∧
          routes g (fun v => ∑ C ∈ (P j).parts, q j C v) := by
    intro j
    by_cases hj : j ∈ Finset.Icc (i + 1) L
    · rcases hlevel j hj with ⟨g, hg⟩
      exact ⟨g, fun _ => hg⟩
    · exact ⟨fun _ _ => 0, fun hj' => (hj hj').elim⟩
  choose gmix hgmix using hlevel'
  refine ⟨a',
    fun u v => gstop u v + ∑ j ∈ Finset.Icc (i + 1) L, gmix j u v,
    ha', habound', hacut', ?_, ?_, ?_⟩
  · intro u v
    have hsum : (∑ j ∈ Finset.Icc (i + 1) L, gmix j u v) =
        -∑ j ∈ Finset.Icc (i + 1) L, gmix j v u := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      exact (hgmix j hj).1 u v
    change gstop u v + (∑ j ∈ Finset.Icc (i + 1) L, gmix j u v) =
      -(gstop v u + ∑ j ∈ Finset.Icc (i + 1) L, gmix j v u)
    rw [hgstop u v, hsum]
    ring
  · intro u v
    have hcard_nat : (Finset.Icc (i + 1) L).card ≤ L := by
      simp
    have hcard_real : ((Finset.Icc (i + 1) L).card : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast hcard_nat
    have hα0 : 0 ≤ α := by linarith
    have hterm_nonneg : 0 ≤ (2 * α) * c s(u, v) :=
      mul_nonneg (mul_nonneg (by norm_num) hα0) (hc s(u, v))
    calc
      |gstop u v + ∑ j ∈ Finset.Icc (i + 1) L, gmix j u v| ≤
          |gstop u v| + |∑ j ∈ Finset.Icc (i + 1) L, gmix j u v| := abs_add_le _ _
      _ ≤ |gstop u v| +
          ∑ j ∈ Finset.Icc (i + 1) L, |gmix j u v| :=
        add_le_add le_rfl
          (Finset.abs_sum_le_sum_abs (fun j => gmix j u v) (Finset.Icc (i + 1) L))
      _ ≤ (8 * (L : ℝ) * β) * c s(u, v) +
          ∑ j ∈ Finset.Icc (i + 1) L, (2 * α) * c s(u, v) := by
        gcongr with j hj
        · exact hcong u v
        · exact (hgmix j hj).2.1 u v
      _ = (8 * (L : ℝ) * β) * c s(u, v) +
          ((Finset.Icc (i + 1) L).card : ℝ) * ((2 * α) * c s(u, v)) := by
        simp
      _ ≤ (8 * (L : ℝ) * β) * c s(u, v) +
          (L : ℝ) * ((2 * α) * c s(u, v)) := by
        gcongr
      _ ≤ (16 * (L : ℝ) * α * β) * c s(u, v) := by
        have hβ0 : 0 ≤ β := by linarith
        have hL0 : 0 ≤ (L : ℝ) := by positivity
        have hc0 := hc s(u, v)
        nlinarith [mul_nonneg hL0 hc0,
          mul_nonneg (mul_nonneg hL0 hα0) hc0,
          mul_nonneg (mul_nonneg hL0 hβ0) hc0,
          mul_nonneg (mul_nonneg (mul_nonneg hL0 hα0) hβ0) hc0]
  · intro v
    rw [Finset.sum_add_distrib, hroutes v]
    have hswap :
        (∑ u, ∑ j ∈ Finset.Icc (i + 1) L, gmix j u v) =
          ∑ j ∈ Finset.Icc (i + 1) L, ∑ u, gmix j u v := by
      rw [Finset.sum_comm]
    rw [hswap]
    have hsumroutes :
        (∑ j ∈ Finset.Icc (i + 1) L, ∑ u, gmix j u v) =
          ∑ j ∈ Finset.Icc (i + 1) L, ∑ C ∈ (P j).parts, q j C v := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (hgmix j hj).2.2 v
    rw [hsumroutes]
    ring

@[blueprint "thm:residual-iteration"
  (statement := /-- Let $L\ge1$, let $c : \operatorname{Sym}^2(V)\to\mathbb R$ be
    nonnegative, let $\alpha,\beta\ge1$, and let
    $\mathcal P_1,\ldots,\mathcal P_L$ satisfy $\mathcal P_1=\bot$ and
    $\mathcal P_L=\top$, together with the simultaneous mixing hypothesis
    (\cref{def:mixing-hypothesis}) and the flow hypothesis with congestion $\beta$
    (\cref{def:flow-hypothesis}). Thus, for every
    $i\in[1,L-1]$, every positive-weight path in its witnessing family has
    distinct endpoints, and that family has the prescribed source and receipt
    masses and edge load at most $\beta c$, as well as endpoint coverage at
    level $i$. For every demand $\mathbf b$ satisfying
    the inequalities for the cut collection \cref{def:cut-collection}, there are residual
    demands $\mathbf b_1,\ldots,\mathbf b_L$ and flows $f_1,\ldots,f_{L-1}$ such that
    $\mathbf b_1=\mathbf b$, each $\mathbf b_i$ is bounded by
    $\deg_{\partial\mathcal P_i}$ and satisfies all cut inequalities belonging to later
    common refinements, and $f_i$ routes $\mathbf b_i-\mathbf b_{i+1}$ with congestion
    $16L\alpha\beta$. -/)
  (proof := /-- Set $\mathbf b_1=\mathbf b$. The pointwise bound at level $1$ is
    \cref{lem:bottom-residual-bound}. Every part of every
    $\mathcal R_{\ge j}$, $1\le j\le L$, belongs to the cut collection
    (\cref{def:cut-collection}), so the assumed cut inequalities give the
    level-$1$ suffix constraints.

    Suppose that $i\in[1,L-1]$ and that $\mathbf b_i$ has been constructed
    with the asserted demand, pointwise, and suffix-cut invariants. Apply
    \cref{thm:residual-transfer-step} with the full mixing and flow
    hypotheses. The induction invariants provide its demand bound and all
    suffix-refinement cut hypotheses. The transfer theorem therefore supplies
    $\mathbf b_{i+1}$ and $f_i$. The residual $\mathbf b_{i+1}$ is a demand,
    is bounded pointwise by
    $\deg_{\partial\mathcal P_{i+1}}$, and satisfies every cut inequality
    for $\mathcal R_{\ge j}$ with $j\in[i+1,L]$. Moreover, $f_i$ routes
    $\mathbf b_i-\mathbf b_{i+1}$ with congestion
    $16L\alpha\beta$.

    Finite induction on $i=1,\ldots,L-1$ now constructs all entries of the two
    sequences on the required index intervals; define their values outside
    those intervals arbitrarily. Each asserted property is respectively the
    base invariant or the conclusion of the corresponding transfer step.
    When $L=1$, the transfer interval is empty, and the base construction
    already gives the conclusion. -/)
  (title := /-- Iterate the residual transfer through the hierarchy -/)
  (latexEnv := "theorem")]
theorem residual_iteration (c : Sym2 V → ℝ) (α β : ℝ)
    (P : ℕ → Finpartition (Finset.univ : Finset V)) (L : ℕ)
    (hc : ∀ e, 0 ≤ c e) (hα : 1 ≤ α) (hβ : 1 ≤ β) (hL : 1 ≤ L)
    (hP1 : P 1 = ⊥)
    (hPL : P L = ⊤)
    (hmix : mixing_hypothesis c α P L)
    (hflow : flow_hypothesis c β P L)
    (b : V → ℝ) (hb : is_demand b)
    (hcut : ∀ C ∈ cut_collection P L, |∑ v ∈ C, b v| ≤ delta_cut c C) :
    ∃ (bseq : ℕ → V → ℝ) (fseq : ℕ → V → V → ℝ),
      bseq 1 = b ∧
      (∀ i ∈ Finset.Icc 1 L,
        is_demand (bseq i) ∧
        (∀ v, |bseq i v| ≤ deg_weighted c (cross_partition_ind (P i)) v) ∧
        (∀ j ∈ Finset.Icc i L, ∀ C ∈ (refinement P j L).parts,
          |∑ v ∈ C, bseq i v| ≤ delta_cut c C)) ∧
      (∀ i ∈ Finset.Icc 1 (L - 1),
        is_flow (fseq i) ∧
        has_congestion c (16 * (L : ℝ) * α * β) (fseq i) ∧
        routes (fseq i) (fun v => bseq i v - bseq (i + 1) v)) := by
  have hbasebound : ∀ v, |b v| ≤
      deg_weighted c (cross_partition_ind (P 1)) v :=
    bottom_residual_bound c P L hc hL hP1 b hcut
  have hbasecuts : ∀ j ∈ Finset.Icc 1 L, ∀ C ∈ (refinement P j L).parts,
      |∑ v ∈ C, b v| ≤ delta_cut c C := by
    intro j hj C hC
    apply hcut C
    simp only [cut_collection, Finset.mem_biUnion]
    exact ⟨j, hj, hC⟩
  let Good : ℕ → Prop := fun k =>
    ∃ (bseq : ℕ → V → ℝ) (fseq : ℕ → V → V → ℝ),
      bseq 1 = b ∧
      (∀ i ∈ Finset.Icc 1 k,
        is_demand (bseq i) ∧
        (∀ v, |bseq i v| ≤ deg_weighted c (cross_partition_ind (P i)) v) ∧
        (∀ j ∈ Finset.Icc i L, ∀ C ∈ (refinement P j L).parts,
          |∑ v ∈ C, bseq i v| ≤ delta_cut c C)) ∧
      (∀ i ∈ Finset.Icc 1 (k - 1),
        is_flow (fseq i) ∧
        has_congestion c (16 * (L : ℝ) * α * β) (fseq i) ∧
        routes (fseq i) (fun v => bseq i v - bseq (i + 1) v))
  have hgood1 : Good 1 := by
    refine ⟨fun _ => b, fun _ _ _ => 0, rfl, ?_, ?_⟩
    · intro i hi
      have hi1 : i = 1 := by
        simpa using hi
      subst i
      exact ⟨hb, hbasebound, hbasecuts⟩
    · simp
  have hstep : ∀ k, 1 ≤ k → k < L → Good k → Good (k + 1) := by
    intro k hk1 hkL
    rintro ⟨bseq, fseq, hbseq1, hbseq, hfseq⟩
    have hk : k ∈ Finset.Icc 1 (L - 1) := by
      simp only [Finset.mem_Icc]
      omega
    have hkinv := hbseq k (Finset.mem_Icc.mpr ⟨hk1, le_rfl⟩)
    have hkcut : ∀ j ∈ Finset.Icc (k + 1) L,
        ∀ C ∈ (refinement P j L).parts,
          |∑ v ∈ C, bseq k v| ≤ delta_cut c C := by
      intro j hj
      apply hkinv.2.2 j
      simp only [Finset.mem_Icc] at hj ⊢
      omega
    rcases residual_transfer_step c α β P L k hc hα hβ hL hPL hk hmix hflow
        (bseq k) hkinv.1 hkinv.2.1 hkcut with
      ⟨a', g, ha', habound', hacut', hg, hcong, hroutes⟩
    let bseq' := Function.update bseq (k + 1) a'
    let fseq' := Function.update fseq k g
    refine ⟨bseq', fseq', ?_, ?_, ?_⟩
    · have hk0 : k ≠ 0 := by omega
      simp [bseq', Function.update, hbseq1, hk0]
    · intro i hi
      by_cases hik : i = k + 1
      · subst i
        simpa [bseq'] using And.intro ha' (And.intro habound' hacut')
      · have hiold : i ∈ Finset.Icc 1 k := by
          simp only [Finset.mem_Icc] at hi ⊢
          omega
        simpa [bseq', hik] using hbseq i hiold
    · intro i hi
      by_cases hik : i = k
      · subst i
        simpa [bseq', fseq'] using And.intro hg (And.intro hcong hroutes)
      · have hiold : i ∈ Finset.Icc 1 (k - 1) := by
          simp only [Finset.mem_Icc, Nat.add_sub_cancel] at hi ⊢
          omega
        have hile := (Finset.mem_Icc.mp hiold).2
        have hik' : i ≠ k + 1 := by omega
        simpa [bseq', fseq', hik, hik'] using hfseq i hiold
  have hall : ∀ k, 1 ≤ k → k ≤ L → Good k := by
    intro k hk1
    induction k, hk1 using Nat.le_induction with
    | base =>
        intro
        exact hgood1
    | succ k hk1 ih =>
        intro hkL
        apply hstep k hk1 (by omega)
        exact ih (by omega)
  simpa [Good] using hall L hL le_rfl

@[blueprint "lem:cut-approx-reduction"
  (statement := /-- Consider a capacitated graph $G = (V,E)$ with nonnegative capacities $c$, and
    parameters $\alpha, \beta \ge 1$. Suppose partitions $\mathcal P_1, \ldots, \mathcal P_L$ of $V$
    with $L \ge 1$ satisfy $\mathcal P_1 = \bot$ (the singleton partition) and
    $\mathcal P_L = \top = \{V\}$ (the one-cluster partition), the mixing hypothesis
    (\cref{def:mixing-hypothesis}) with congestion $\alpha$, and the canonical
    flow hypothesis (\cref{def:flow-hypothesis}) with congestion $\beta$,
    whose level witnesses include endpoint coverage.
    Then for every demand
    $\mathbf b$ satisfying
    $\bigl|\sum_{v \in C} \mathbf b(v)\bigr| \le \delta C$ for all $C$ in the cut collection
    $\mathcal C = \bigcup_{i \in [L]} \mathcal R_{\ge i}$ (\cref{def:cut-collection}), there exist a
    vector $\mathbf b'$ with $|\mathbf b'| \le \deg_{\partial\mathcal P_L}$ (\cref{def:deg-weighted})
    and a flow $f$ of congestion $16 L^2 \alpha\beta$ routing $\mathbf b - \mathbf b'$. -/)
  (proof := /-- Apply \cref{thm:residual-iteration} to the demand $\mathbf b$, using the
    initial- and final-partition identities together with the mixing and flow hypotheses.
    This gives demands
    $\mathbf b_1,\ldots,\mathbf b_L$ and flows $f_1,\ldots,f_{L-1}$ such that
    $\mathbf b_1=\mathbf b$. For every $i\in[1,L]$, the demand $\mathbf b_i$ is bounded
    pointwise by $\deg_{\partial\mathcal P_i}$; and, for every $i\in[1,L-1]$, the
    antisymmetric function $f_i$ routes $\mathbf b_i-\mathbf b_{i+1}$ and has congestion
    at most $16L\alpha\beta$.

    Set $\mathbf b'=\mathbf b_L$ and
    \[
      f(u,v)=\sum_{i=1}^{L-1}f_i(u,v).
    \]
    Since $L\in[1,L]$, the level-$L$ pointwise invariant yields
    $|\mathbf b'(v)|\le\deg_{\partial\mathcal P_L}(v)$ for every $v\in V$. A finite sum
    of antisymmetric functions is antisymmetric, so $f$ is a flow
    (\cref{def:is-flow}). By linearity of the divergence and the routing identities for
    the $f_i$ (\cref{def:routes}), the sum telescopes:
    \[
      \operatorname{div}f
      =\sum_{i=1}^{L-1}(\mathbf b_i-\mathbf b_{i+1})
      =\mathbf b_1-\mathbf b_L
      =\mathbf b-\mathbf b'.
    \]
    This identity also covers $L=1$, when the sum is empty and
    $\mathbf b'=\mathbf b$.

    Finally, for every pair of vertices $u,v$, the triangle inequality and the
    congestion bound for each level flow give
    \[
      |f(u,v)|
      \le \sum_{i=1}^{L-1}|f_i(u,v)|
      \le (L-1)\,16L\alpha\beta\,c(\{u,v\})
      \le 16L^2\alpha\beta\,c(\{u,v\}).
    \]
    The last inequality follows from $L\ge1$, $\alpha,\beta\ge1$, and
    $c(\{u,v\})\ge0$. Hence $f$ has
    congestion at most $16L^2\alpha\beta$ (\cref{def:has-congestion}) and routes
    $\mathbf b-\mathbf b'$, as required. -/)
  (title := /-- Reduction to a residual boundary demand -/)
  (latexEnv := "lemma")]
lemma cut_approx_reduction (c : Sym2 V → ℝ) (α β : ℝ)
    (P : ℕ → Finpartition (Finset.univ : Finset V)) (L : ℕ)
    (hc : ∀ e, 0 ≤ c e) (hα : 1 ≤ α) (hβ : 1 ≤ β) (hL : 1 ≤ L)
    (hP1 : P 1 = ⊥)
    (hPL : P L = ⊤)
    (hmix : mixing_hypothesis c α P L) (hflow : flow_hypothesis c β P L)
    (b : V → ℝ) (hb : is_demand b)
    (hcut : ∀ C ∈ cut_collection P L, |∑ v ∈ C, b v| ≤ delta_cut c C) :
    ∃ (b' : V → ℝ) (f : V → V → ℝ),
      (∀ v, |b' v| ≤ deg_weighted c (cross_partition_ind (P L)) v) ∧
      is_flow f ∧ has_congestion c (16 * (L : ℝ) ^ 2 * α * β) f ∧
      routes f (fun v => b v - b' v) := by
  obtain ⟨bseq, fseq, hb1, hbseq, hfseq⟩ :=
    residual_iteration c α β P L hc hα hβ hL hP1 hPL hmix hflow b hb hcut
  let I := Finset.Icc 1 (L - 1)
  refine ⟨bseq L, (fun u v => ∑ i ∈ I, fseq i u v), ?_, ?_, ?_, ?_⟩
  · exact (hbseq L (Finset.mem_Icc.mpr ⟨hL, le_rfl⟩)).2.1
  · intro u v
    calc
      ∑ i ∈ I, fseq i u v = ∑ i ∈ I, -fseq i v u := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hfseq i (by simpa [I] using hi)).1 u v
      _ = -(∑ i ∈ I, fseq i v u) := by simp
  · intro u v
    have hsub : I ⊆ Finset.range L := by
      intro i hi
      simp only [I, Finset.mem_Icc] at hi
      simp only [Finset.mem_range]
      omega
    have hcard : I.card ≤ L := by
      calc
        I.card ≤ (Finset.range L).card := Finset.card_le_card hsub
        _ = L := Finset.card_range L
    have hfactor : 0 ≤ (16 * (L : ℝ) * α * β) * c s(u, v) := by
      have hcuv : 0 ≤ c s(u, v) := hc _
      positivity
    calc
      |∑ i ∈ I, fseq i u v| ≤ ∑ i ∈ I, |fseq i u v| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ I, (16 * (L : ℝ) * α * β) * c s(u, v) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (hfseq i (by simpa [I] using hi)).2.1 u v
      _ = (I.card : ℝ) * ((16 * (L : ℝ) * α * β) * c s(u, v)) := by simp
      _ ≤ (L : ℝ) * ((16 * (L : ℝ) * α * β) * c s(u, v)) := by
        apply mul_le_mul_of_nonneg_right _ hfactor
        exact_mod_cast hcard
      _ = (16 * (L : ℝ) ^ 2 * α * β) * c s(u, v) := by ring
  · intro v
    calc
      ∑ u, ∑ i ∈ I, fseq i u v = ∑ i ∈ I, ∑ u, fseq i u v := by
        rw [Finset.sum_comm]
      _ = ∑ i ∈ I, (bseq i v - bseq (i + 1) v) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hfseq i (by simpa [I] using hi)).2.2 v
      _ = b v - bseq L v := by
        have hI : I = Finset.Ico 1 L := by
          ext i
          simp [I]
          omega
        rw [hI]
        calc
          ∑ i ∈ Finset.Ico 1 L, (bseq i v - bseq (i + 1) v) =
              -(∑ i ∈ Finset.Ico 1 L, (bseq (i + 1) v - bseq i v)) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = -(bseq L v - bseq 1 v) := by
            have htel : (∑ i ∈ Finset.Ico 1 L,
                (bseq (i + 1) v - bseq i v)) = bseq L v - bseq 1 v := by
              exact Finset.sum_Ico_sub (fun i => bseq i v) hL
            rw [htel]
          _ = b v - bseq L v := by rw [hb1]; ring

@[blueprint "thm:cut-approx"
  (statement := /-- Consider a finite capacitated graph $G = (V,E)$ encoded by a function $c$ on unordered
    pairs of vertices: absent edges have capacity zero, while every present edge has capacity in
    $[1,W]$, where $W \ge 1$. Let $\alpha, \beta \ge 1$. Suppose partitions
    $\mathcal P_1, \ldots, \mathcal P_L$ of $V$ with $L \ge 1$ form a valid hierarchy
    (\cref{def:valid-hierarchy}), i.e. $\mathcal P_1 = \bot$ is the singleton partition and
    $\mathcal P_L = \top = \{V\}$, and suppose the mixing hypothesis
    (\cref{def:mixing-hypothesis}) holds with congestion $\alpha$ and the
    canonical flow hypothesis (\cref{def:flow-hypothesis}) holds with
    congestion $\beta$, with endpoint coverage included in every level
    witness. Then the cut collection
    $\mathcal C = \bigcup_{i \in [L]} \mathcal R_{\ge i}$ (\cref{def:cut-collection}) is a
    congestion-approximator of quality $16 L^2 \alpha\beta$ (\cref{def:is-congestion-approx}). -/)
  (proof := /-- Let $\mathbf b : V \to \mathbb R$ be a demand satisfying
    $\bigl|\sum_{v \in C} \mathbf b(v)\bigr| \le \delta C$ for every cut $C \in \mathcal C$
    (\cref{def:cut-collection}); we must produce a flow of congestion $16 L^2 \alpha\beta$ routing
    $\mathbf b$. The capacity hypothesis implies $c(e) \ge 0$ for every unordered pair $e$, and
    validity of the hierarchy gives $\mathcal P_1 = \bot$ and
    $\mathcal P_L = \top$. Applying
    \cref{lem:cut-approx-reduction} to $\mathbf b$ yields a demand
    $\mathbf b'$ with $|\mathbf b'| \le \deg_{\partial\mathcal P_L}$ (\cref{def:deg-weighted}) and a
    flow $f$ of congestion $16 L^2 \alpha\beta$ routing $\mathbf b - \mathbf b'$. Since the hierarchy
    is valid we have $\mathcal P_L = \top = \{V\}$, so \cref{lem:deg-boundary-top-zero} gives
    $\deg_{\partial\mathcal P_L}(v) = 0$ for every $v$. Therefore $|\mathbf b'(v)| \le 0$ for all $v$,
    which forces $\mathbf b' = \mathbf 0$, and hence $f$ routes $\mathbf b - \mathbf b' = \mathbf b$
    with congestion $16 L^2 \alpha\beta$. As $\mathbf b$ was an arbitrary demand respecting the cut
    constraints, $\mathcal C$ is a congestion-approximator of quality $16 L^2 \alpha\beta$
    (\cref{def:is-congestion-approx}). -/)
  (title := /-- Cut-based congestion-approximator from a partition hierarchy -/)
  (latexEnv := "theorem")]
theorem cut_approx (c : Sym2 V → ℝ) (W α β : ℝ)
    (P : ℕ → Finpartition (Finset.univ : Finset V)) (L : ℕ)
    (hW : 1 ≤ W) (hc : ∀ e, c e = 0 ∨ (1 ≤ c e ∧ c e ≤ W))
    (hα : 1 ≤ α) (hβ : 1 ≤ β) (hL : 1 ≤ L)
    (hhier : valid_hierarchy P L)
    (hmix : mixing_hypothesis c α P L) (hflow : flow_hypothesis c β P L) :
    is_congestion_approx c (cut_collection P L) (16 * (L : ℝ) ^ 2 * α * β) := by
  unfold is_congestion_approx
  intro b hb hcut
  have hc' : ∀ e, 0 ≤ c e := by
    intro e
    rcases hc e with he | he
    · rw [he]
    · exact le_trans zero_le_one he.1
  obtain ⟨b', f, hb', hf, hcong, hroutes⟩ :=
    cut_approx_reduction c α β P L hc' hα hβ hL hhier.1 hhier.2 hmix hflow b hb hcut
  have hb'zero : b' = 0 := by
    funext v
    have hdeg := deg_boundary_top_zero c P L hhier.2 v
    have hbound := hb' v
    rw [hdeg] at hbound
    exact abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))
  refine ⟨f, hf, hcong, ?_⟩
  simpa [hb'zero] using hroutes

import Architect
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.List.TFAE

set_option linter.all false
set_option maxHeartbeats 500000

open SimpleGraph

@[blueprint "def:graph"
  (statement := /-- A \emph{graph} is a pair $\mathbf{G} = (V, G)$ consisting of a vertex type
    $V$ and a simple graph $G$ on $V$, i.e.\ an irreflexive symmetric adjacency relation. This
    bundling lets a \emph{class of graphs} be modelled as a predicate on such pairs. -/)
  (title := /-- Bundled simple graph -/)
  (latexEnv := "definition")]
structure graph where
  V : Type
  G : SimpleGraph V

@[blueprint "def:tec"
  (statement := /-- A \emph{$2$-edge-coloured graph} is a triple $(V, R, B)$ where $V$ is a
    vertex type and $R, B$ are simple graphs on $V$ (the \emph{red} and \emph{blue} graphs)
    whose edge sets are disjoint: for all $u, v \in V$ one never has both $R\text{-}\mathrm{Adj}(u,v)$
    and $B\text{-}\mathrm{Adj}(u,v)$. -/)
  (title := /-- $2$-edge-coloured graph -/)
  (latexEnv := "definition")]
structure tec where
  V : Type
  red : SimpleGraph V
  blue : SimpleGraph V
  disjoint : ∀ u v, ¬ (red.Adj u v ∧ blue.Adj u v)

@[blueprint "def:tec-hom"
  (statement := /-- Given $2$-edge-coloured graphs $A$ and $B$, we write
    $A \to B$ if there is a vertex map $f : V(A) \to V(B)$ that is colour- and
    adjacency-preserving: for all $u, v$, if $u, v$ are red-adjacent in $A$ then $f(u), f(v)$
    are red-adjacent in $B$, and likewise for blue. See \cref{def:tec}. -/)
  (title := /-- Homomorphism of $2$-edge-coloured graphs -/)
  (latexEnv := "definition")]
def tec_hom (A B : tec) : Prop :=
  ∃ f : A.V → B.V,
    (∀ u v, A.red.Adj u v → B.red.Adj (f u) (f v)) ∧
    (∀ u v, A.blue.Adj u v → B.blue.Adj (f u) (f v))

@[blueprint "def:tec-inj-hom"
  (statement := /-- Given $2$-edge-coloured graphs $A$ and $B$, we write $A \hookrightarrow B$
    if there is an \emph{injective} colour- and adjacency-preserving vertex map
    $f : V(A) \to V(B)$, i.e.\ $f$ is injective and preserves both colours as in
    \cref{def:tec-hom}. -/)
  (title := /-- Injective homomorphism of $2$-edge-coloured graphs -/)
  (latexEnv := "definition")]
def tec_inj_hom (A B : tec) : Prop :=
  ∃ f : A.V → B.V, Function.Injective f ∧
    (∀ u v, A.red.Adj u v → B.red.Adj (f u) (f v)) ∧
    (∀ u v, A.blue.Adj u v → B.blue.Adj (f u) (f v))

@[blueprint "def:star"
  (statement := /-- For a graph $\mathbf{H} = (V, H)$, its \emph{complete $2$-edge-coloured
    graph} $H^{\ast}$ is the $2$-edge-coloured graph on $V$ with blue graph $H$ and red graph
    the complement $H^{c}$; thus every pair of distinct vertices is either blue (an edge of $H$)
    or red (a non-edge of $H$), and no pair is both. See \cref{def:graph} and \cref{def:tec}. -/)
  (title := /-- The complete $2$-edge-coloured graph $H^{\ast}$ -/)
  (latexEnv := "definition")]
def star (H : graph) : tec where
  V := H.V
  red := H.Gᶜ
  blue := H.G
  disjoint := by
    intro u v h
    exact ((SimpleGraph.compl_adj H.G u v).1 h.1).2 h.2

@[blueprint "def:csp"
  (statement := /-- For a $2$-edge-coloured graph $T$, the constraint satisfaction problem
    $\mathrm{CSP}(T)$ is the class of \emph{finite} $2$-edge-coloured graphs $A$ that admit a
    homomorphism $A \to T$ (see \cref{def:tec-hom}). It is regarded as the predicate on
    $2$-edge-coloured graphs holding exactly of such yes-instances. -/)
  (title := /-- The problem $\mathrm{CSP}(T)$ -/)
  (latexEnv := "definition")]
def csp (T : tec) : tec → Prop :=
  fun A => Finite A.V ∧ tec_hom A T

@[blueprint "def:inj-csp"
  (statement := /-- For a $2$-edge-coloured graph $T$, the injective constraint satisfaction
    problem $\mathrm{injCSP}(T)$ is the class of finite $2$-edge-coloured graphs $A$ that admit
    an injective homomorphism $A \hookrightarrow T$ (see \cref{def:tec-inj-hom}). -/)
  (title := /-- The problem $\mathrm{injCSP}(T)$ -/)
  (latexEnv := "definition")]
def inj_csp (T : tec) : tec → Prop :=
  fun A => Finite A.V ∧ tec_inj_hom A T

@[blueprint "def:sp"
  (statement := /-- For a class of graphs $\mathcal{C}$ (a predicate on graphs, see
    \cref{def:graph}), the sandwich problem $\mathrm{SP}(\mathcal{C})$ is the class of finite
    $2$-edge-coloured graphs $A = (V, B, R)$ (blue edges $B$, red non-edges $R$) that are
    yes-instances: there exists a simple graph $E'$ on $V$ with $B \subseteq E'$ and
    $E' \cap R = \varnothing$ such that $(V, E') \in \mathcal{C}$. -/)
  (title := /-- The sandwich problem $\mathrm{SP}(\mathcal{C})$ -/)
  (latexEnv := "definition")]
def sp (C : graph → Prop) : tec → Prop :=
  fun A => Finite A.V ∧ ∃ E' : SimpleGraph A.V,
    (∀ u v, A.blue.Adj u v → E'.Adj u v) ∧
    (∀ u v, E'.Adj u v → ¬ A.red.Adj u v) ∧
    C ⟨A.V, E'⟩

@[blueprint "def:iso-closed"
  (statement := /-- A class of graphs $\mathcal{C}$ is \emph{closed under isomorphism} if
    whenever $\mathbf{G}$ and $\mathbf{H}$ are graphs with $G \simeq H$ (an isomorphism of
    simple graphs) and $\mathbf{G} \in \mathcal{C}$, then $\mathbf{H} \in \mathcal{C}$. This is
    the blanket assumption imposed on all classes in the paper. See \cref{def:graph}. -/)
  (title := /-- Isomorphism-closed class -/)
  (latexEnv := "definition")]
def iso_closed (C : graph → Prop) : Prop :=
  ∀ G H : graph, Nonempty (G.G ≃g H.G) → C G → C H

@[blueprint "def:hereditary"
  (statement := /-- A class of graphs $\mathcal{C}$ is \emph{hereditary} if it is closed under
    taking induced subgraphs of its finite members: for every \emph{finite} graph
    $\mathbf{G} = (V, G) \in \mathcal{C}$ (i.e.\ $V$ finite) and every subset $s \subseteq V$,
    the induced subgraph $(s, G[s])$ belongs to $\mathcal{C}$. The finiteness restriction
    matches the paper's convention that the sandwich and constraint-satisfaction classes are
    classes of finite $2$-edge-coloured graphs. See \cref{def:graph}. -/)
  (title := /-- Hereditary class -/)
  (latexEnv := "definition")]
def hereditary (C : graph → Prop) : Prop :=
  ∀ (G : graph) (s : Set G.V), Finite G.V → C G → C ⟨_, G.G.induce s⟩

@[blueprint "def:jep"
  (statement := /-- A class of graphs $\mathcal{C}$ has the \emph{joint embedding property}
    (JEP) if for all \emph{finite} graphs $\mathbf{G}, \mathbf{H} \in \mathcal{C}$ (i.e.\ with
    $V(\mathbf{G})$ and $V(\mathbf{H})$ finite) there is a \emph{finite} graph
    $\mathbf{F} \in \mathcal{C}$ together with induced-subgraph embeddings
    $G \hookrightarrow F$ and $H \hookrightarrow F$ (graph embeddings, whose images are induced
    subgraphs). Requiring the common host to be finite makes the finite members of
    $\mathcal{C}$ directed under induced embeddings, as prescribed by the paper's convention
    that the sandwich and constraint-satisfaction classes consist of finite
    $2$-edge-coloured graphs. See \cref{def:graph}. -/)
  (title := /-- Joint embedding property -/)
  (latexEnv := "definition")]
def jep (C : graph → Prop) : Prop :=
  ∀ G H : graph, Finite G.V → Finite H.V → C G → C H →
    ∃ F : graph, Finite F.V ∧ C F ∧ Nonempty (G.G ↪g F.G) ∧ Nonempty (H.G ↪g F.G)

@[blueprint "def:split-blow-up"
  (statement := /-- Let $\mathbf{G} = (V, G)$ be a graph, let $\mathrm{twin} : V \to \mathrm{Prop}$
    designate for each vertex whether it is substituted by a set of \emph{twins}
    (an independent set, $\mathrm{twin}(u)$ true) or of \emph{co-twins} (a clique,
    $\mathrm{twin}(u)$ false), and let $\beta : V \to \mathrm{Type}$ assign to each vertex the
    substituting set. The \emph{split blow-up} $\mathrm{SBU}(G, \mathrm{twin}, \beta)$ is the
    simple graph on $\bigsqcup_{u \in V} \beta(u)$ in which two distinct vertices lying over
    $u$ and $w$ are adjacent iff either $u = w$ and $u$ is a co-twin vertex, or $u \neq w$ and
    $u, w$ are adjacent in $G$. See \cref{def:graph}. -/)
  (title := /-- Split blow-up of a graph -/)
  (latexEnv := "definition")]
def split_blow_up (G : graph) (twin : G.V → Prop) (β : G.V → Type) :
    SimpleGraph (Σ u, β u) :=
  SimpleGraph.fromRel (fun p q =>
    (p.1 = q.1 ∧ ¬ twin p.1) ∨ (p.1 ≠ q.1 ∧ G.G.Adj p.1 q.1))

@[blueprint "def:preserved-split-blow-up"
  (statement := /-- A class of graphs $\mathcal{C}$ is \emph{preserved under split blow-ups} if
    for every finite graph $\mathbf{G} = (V, G) \in \mathcal{C}$ there is a designation
    $\mathrm{twin} : V \to \mathrm{Prop}$ (a partition of $V$ into twin- and co-twin-vertices)
    such that, for every family $\beta : V \to \mathrm{Type}$ of finite non-empty substituting
    sets, the split blow-up
    $(\bigsqcup_u \beta(u), \mathrm{SBU}(G, \mathrm{twin}, \beta))$ belongs to $\mathcal{C}$.
    Thus the predicate concerns precisely the finite split blow-ups visible to the sandwich and
    constraint-satisfaction problems. See \cref{def:split-blow-up}. -/)
  (title := /-- Preservation under split blow-ups -/)
  (latexEnv := "definition")]
def preserved_split_blow_up (C : graph → Prop) : Prop :=
  ∀ G : graph, Finite G.V → C G → ∃ twin : G.V → Prop,
    ∀ β : G.V → Type, (∀ u, Finite (β u)) → (∀ u, Nonempty (β u)) →
      C ⟨_, split_blow_up G twin β⟩

@[blueprint "def:age"
  (statement := /-- For a graph $\mathbf{H} = (V, H)$, its \emph{age} $\mathrm{Age}(\mathbf{H})$
    is the class of finite graphs $\mathbf{G} = (W, G)$ that embed into $\mathbf{H}$ as an
    induced subgraph, i.e.\ $W$ is finite and there is a graph embedding
    $G \hookrightarrow H$. See \cref{def:graph}. -/)
  (title := /-- Age of a graph -/)
  (latexEnv := "definition")]
def age (H : graph) (G : graph) : Prop :=
  Finite G.V ∧ Nonempty (G.G ↪g H.G)

@[blueprint "def:is-universal"
  (statement := /-- A graph $\mathbf{H}$ is \emph{universal} in a class $\mathcal{C}$ if
    $\mathbf{H} \in \mathcal{C}$ and its age equals the finite graphs of $\mathcal{C}$: for
    every finite graph $\mathbf{G}$, one has $\mathbf{G} \in \mathrm{Age}(\mathbf{H})$ iff
    $\mathbf{G} \in \mathcal{C}$. See \cref{def:age}. -/)
  (title := /-- Universal graph in a class -/)
  (latexEnv := "definition")]
def is_universal (C : graph → Prop) (H : graph) : Prop :=
  C H ∧ ∀ G : graph, Finite G.V → (age H G ↔ C G)

@[blueprint "def:tec-sum"
  (statement := /-- The \emph{disjoint union} $A + B$ of two $2$-edge-coloured graphs is the
    $2$-edge-coloured graph on $V(A) \sqcup V(B)$ whose red (resp.\ blue) graph is the disjoint
    union of the red (resp.\ blue) graphs of $A$ and $B$; no edge joins the two sides. See
    \cref{def:tec}. -/)
  (title := /-- Disjoint union of $2$-edge-coloured graphs -/)
  (latexEnv := "definition")]
def tec_sum (A B : tec) : tec where
  V := A.V ⊕ B.V
  red := A.red.sum B.red
  blue := A.blue.sum B.blue
  disjoint := by
    rintro (u | u) (v | v) ⟨hr, hb⟩ <;>
      first
        | exact A.disjoint u v ⟨hr, hb⟩
        | exact B.disjoint u v ⟨hr, hb⟩
        | simp_all

@[blueprint "lem:ramsey-offdiag"
  (statement := /-- For all $p, q \in \mathbb{N}$ there is $r \in \mathbb{N}$ such that for
    every type $V$, every simple graph $G$ on $V$, and every finite set $W$ of vertices with
    $r \le |W|$, there is a subset $s \subseteq W$ that is either a clique of size $p$ (all
    distinct pairs adjacent) or an independent set of size $q$ (all distinct pairs
    non-adjacent) in $G$. -/)
  (proof := /-- We argue by induction on $p$, and for each $p$ by induction on $q$. If $p = 0$
    the empty set is a clique of size $0$ contained in $W$, so $r = 0$ works; symmetrically, if
    $q = 0$ the empty set is an independent set of size $0$, so $r = 0$ works. Suppose the claim
    holds for the pairs $(p, q+1)$ with bound $r_2$ and $(p+1, q)$ with bound $r_1$, and set
    $r = r_1 + r_2 + 1$. Let $W$ satisfy $r \le |W|$; then $W$ is non-empty, so fix $v \in W$.
    Partition $W \setminus \{v\}$ into the set $A$ of neighbours of $v$ and the set $B$ of
    non-neighbours of $v$, so that $|A| + |B| = |W| - 1 \ge r_1 + r_2$; hence $|A| \ge r_2$ or
    $|B| \ge r_1$. If $|A| \ge r_2$, then within $A$ there is either an independent set of size
    $q+1$, which lies in $W$ and finishes the proof, or a clique $s$ of size $p$; since every
    vertex of $A$ is adjacent to $v$ and $v \notin A$, the set $s \cup \{v\}$ is a clique of
    size $p+1$ contained in $W$. If $|B| \ge r_1$, then within $B$ there is either a clique of
    size $p+1$, which lies in $W$ and finishes the proof, or an independent set $s$ of size $q$;
    since no vertex of $B$ is adjacent to $v$ and $v \notin B$, the set $s \cup \{v\}$ is an
    independent set of size $q+1$ contained in $W$. -/)
  (title := /-- Finite off-diagonal Ramsey theorem for two colours -/)
  (latexEnv := "lemma")]
lemma ramsey_offdiag (p q : ℕ) :
    ∃ r : ℕ, ∀ (V : Type) (G : SimpleGraph V) (W : Finset V), r ≤ W.card →
      (∃ s : Finset V, s ⊆ W ∧ s.card = p ∧
          (∀ u ∈ s, ∀ w ∈ s, u ≠ w → G.Adj u w)) ∨
      (∃ s : Finset V, s ⊆ W ∧ s.card = q ∧
          (∀ u ∈ s, ∀ w ∈ s, u ≠ w → ¬ G.Adj u w)) := by
  induction p generalizing q with
  | zero =>
    exact ⟨0, fun _ _ W _ => Or.inl ⟨∅, by simp, by simp, by simp⟩⟩
  | succ p ihp =>
    induction q with
    | zero =>
      exact ⟨0, fun _ _ W _ => Or.inr ⟨∅, by simp, by simp, by simp⟩⟩
    | succ q ihq =>
      obtain ⟨r1, hr1⟩ := ihq
      obtain ⟨r2, hr2⟩ := ihp (q + 1)
      refine ⟨r1 + r2 + 1, fun V G W hW => ?_⟩
      classical
      obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < W.card by omega)
      set A := (W.erase v).filter (fun x => G.Adj v x) with hA
      set B := (W.erase v).filter (fun x => ¬ G.Adj v x) with hB
      have hAsub : A ⊆ W.erase v := by rw [hA]; exact Finset.filter_subset _ _
      have hBsub : B ⊆ W.erase v := by rw [hB]; exact Finset.filter_subset _ _
      have hcardsum : A.card + B.card = (W.erase v).card := by
        rw [hA, hB]; exact Finset.card_filter_add_card_filter_not (fun x => G.Adj v x)
      have hWerase : (W.erase v).card = W.card - 1 := Finset.card_erase_of_mem hv
      have hsplit : r2 ≤ A.card ∨ r1 ≤ B.card := by omega
      rcases hsplit with hAcard | hBcard
      · rcases hr2 V G A hAcard with ⟨s, hsA, hscard, hsc⟩ | ⟨s, hsA, hscard, hsi⟩
        · have hvs : v ∉ s := fun h => Finset.notMem_erase v W (hAsub (hsA h))
          refine Or.inl ⟨insert v s, ?_, ?_, ?_⟩
          · rw [Finset.insert_subset_iff]
            exact ⟨hv, fun x hx => Finset.erase_subset _ _ (hAsub (hsA hx))⟩
          · rw [Finset.card_insert_of_notMem hvs, hscard]
          · intro a ha b hb hab
            rw [Finset.mem_insert] at ha hb
            rcases ha with rfl | ha <;> rcases hb with rfl | hb
            · exact absurd rfl hab
            · have hbA := hsA hb; rw [hA, Finset.mem_filter] at hbA; exact hbA.2
            · have haA := hsA ha; rw [hA, Finset.mem_filter] at haA; exact haA.2.symm
            · exact hsc a ha b hb hab
        · exact Or.inr ⟨s, fun x hx => Finset.erase_subset _ _ (hAsub (hsA hx)), hscard, hsi⟩
      · rcases hr1 V G B hBcard with ⟨s, hsB, hscard, hsc⟩ | ⟨s, hsB, hscard, hsi⟩
        · exact Or.inl ⟨s, fun x hx => Finset.erase_subset _ _ (hBsub (hsB hx)), hscard, hsc⟩
        · have hvs : v ∉ s := fun h => Finset.notMem_erase v W (hBsub (hsB h))
          refine Or.inr ⟨insert v s, ?_, ?_, ?_⟩
          · rw [Finset.insert_subset_iff]
            exact ⟨hv, fun x hx => Finset.erase_subset _ _ (hBsub (hsB hx))⟩
          · rw [Finset.card_insert_of_notMem hvs, hscard]
          · intro a ha b hb hab
            rw [Finset.mem_insert] at ha hb
            rcases ha with rfl | ha <;> rcases hb with rfl | hb
            · exact absurd rfl hab
            · have hbB := hsB hb; rw [hB, Finset.mem_filter] at hbB; exact hbB.2
            · have haB := hsB ha; rw [hB, Finset.mem_filter] at haB
              exact fun hadj => haB.2 hadj.symm
            · exact hsi a ha b hb hab

@[blueprint "lem:ramsey"
  (statement := /-- For every $n \in \mathbb{N}$ there is $r \in \mathbb{N}$ such that for every
    finite type $V$ with $r \le |V|$ and every simple graph $G$ on $V$, there is a subset
    $s \subseteq V$ with $|s| = n$ that is either a clique (all distinct pairs adjacent) or an
    independent set (all distinct pairs non-adjacent) in $G$. -/)
  (proof := /-- Apply \cref{lem:ramsey-offdiag} with $p = q = n$ to obtain a bound $r$ such that
    every finite vertex set of size at least $r$ contains, in any simple graph, either a clique
    of size $n$ or an independent set of size $n$. Given a finite type $V$ with $r \le |V|$ and a
    simple graph $G$ on $V$, apply this to the set of all vertices of $V$, whose cardinality is
    $|V| \ge r$: the resulting subset $s$ has size $n$ and is a clique or an independent set of
    $G$, which is exactly the required disjunction. -/)
  (title := /-- Finite Ramsey: monochromatic clique or independent set -/)
  (latexEnv := "lemma")]
lemma ramsey (n : ℕ) :
    ∃ r : ℕ, ∀ (V : Type) [Fintype V], r ≤ Fintype.card V →
      ∀ G : SimpleGraph V, ∃ s : Finset V, s.card = n ∧
        ((∀ u ∈ s, ∀ v ∈ s, u ≠ v → G.Adj u v) ∨
         (∀ u ∈ s, ∀ v ∈ s, u ≠ v → ¬ G.Adj u v)) := by
  obtain ⟨r, hr⟩ := ramsey_offdiag n n
  refine ⟨r, ?_⟩
  intro V _ hV G
  have huniv : r ≤ (Finset.univ : Finset V).card := by rw [Finset.card_univ]; exact hV
  rcases hr V G Finset.univ huniv with ⟨s, _, hscard, hs⟩ | ⟨s, _, hscard, hs⟩
  · exact ⟨s, hscard, Or.inl hs⟩
  · exact ⟨s, hscard, Or.inr hs⟩

@[blueprint "lem:csp-disjoint-union"
  (statement := /-- Let $T$ be a $2$-edge-coloured graph and $A, B$ finite $2$-edge-coloured
    graphs with $A, B \in \mathrm{CSP}(T)$. Then their disjoint union $A + B$ also lies in
    $\mathrm{CSP}(T)$. See \cref{def:csp} and \cref{def:tec-sum}. -/)
  (proof := /-- Constraint satisfaction problems are closed under disjoint unions: given
    homomorphisms $f_A : A \to T$ and $f_B : B \to T$, the map on $V(A) \sqcup V(B)$ that applies
    $f_A$ on the left and $f_B$ on the right is colour- and adjacency-preserving, since no edge
    of $A + B$ joins the two sides, and $V(A) \sqcup V(B)$ is finite. Hence
    $A + B \in \mathrm{CSP}(T)$. -/)
  (title := /-- $\mathrm{CSP}$ is closed under disjoint unions -/)
  (latexEnv := "lemma")]
lemma csp_disjoint_union (T : tec) (A B : tec)
    (hA : csp T A) (hB : csp T B) : csp T (tec_sum A B) := by
  obtain ⟨hAfin, fA, hAr, hAb⟩ := hA
  obtain ⟨hBfin, fB, hBr, hBb⟩ := hB
  haveI : Finite A.V := hAfin
  haveI : Finite B.V := hBfin
  haveI := Fintype.ofFinite A.V
  haveI := Fintype.ofFinite B.V
  refine ⟨(inferInstance : Finite (A.V ⊕ B.V)), Sum.elim fA fB, ?_, ?_⟩
  · rintro (u | u) (v | v) h
    · exact hAr u v (by simpa [tec_sum] using h)
    · simp [tec_sum] at h
    · simp [tec_sum] at h
    · exact hBr u v (by simpa [tec_sum] using h)
  · rintro (u | u) (v | v) h
    · exact hAb u v (by simpa [tec_sum] using h)
    · simp [tec_sum] at h
    · simp [tec_sum] at h
    · exact hBb u v (by simpa [tec_sum] using h)

@[blueprint "def:exists-universal-code"
  (statement := /-- For each natural number $n$, let $E_n$ be the finite graph decoded from $n$
    as a dependent pair consisting of a natural number $k$ and a simple graph on
    $\operatorname{Fin}(k)$; if decoding fails, let $E_n$ be the empty graph. -/)
  (title := /-- An enumeration of finite graphs -/)
  (latexEnv := "definition")]
noncomputable def exists_universal_code (n : Nat) : graph :=
  letI (k : Nat) : Fintype (SimpleGraph (Fin k)) := Fintype.ofFinite _
  letI (k : Nat) : Encodable (SimpleGraph (Fin k)) := Fintype.toEncodable _
  match (Encodable.decode n : Option (Σ k : Nat, SimpleGraph (Fin k))) with
  | some p => ⟨Fin p.1, p.2⟩
  | none => ⟨Fin 0, ⊥⟩

@[blueprint "lem:exists-universal-code-complete"
  (statement := /-- Every finite graph is isomorphic to one of the graphs $E_n$ from
    \cref{def:exists-universal-code}. -/)
  (proof := /-- Equip the vertex type with its canonical finite-type structure and transport the
    graph along an equivalence with $\operatorname{Fin}(k)$. Encode the resulting dependent pair;
    decoding this code returns the pair itself by the defining inverse law for the encoding in
    \cref{def:exists-universal-code}, and the transport equivalence is a graph isomorphism. -/)
  (title := /-- Completeness of the finite-graph enumeration -/)
  (latexEnv := "lemma")]
lemma exists_universal_code_complete (G : graph) (hG : Finite G.V) :
    ∃ n : Nat, Nonempty (G.G ≃g (exists_universal_code n).G) := by
  letI : Finite G.V := hG
  letI : Fintype G.V := Fintype.ofFinite G.V
  letI (k : Nat) : Fintype (SimpleGraph (Fin k)) := Fintype.ofFinite _
  letI (k : Nat) : Encodable (SimpleGraph (Fin k)) := Fintype.toEncodable _
  let e := Fintype.equivFin G.V
  let p : Σ k : Nat, SimpleGraph (Fin k) := ⟨Fintype.card G.V, G.G.map e⟩
  refine ⟨Encodable.encode p, ?_⟩
  unfold exists_universal_code
  rw [Encodable.encodek]
  simpa [p] using
    (show Nonempty (G.G ≃g G.G.map e) from ⟨SimpleGraph.Iso.map e G.G⟩)

@[blueprint "def:exists-universal-next"
  (statement := /-- Given a finite member $X$ of $\mathcal C$ and an index $n$, define the next
    stage to be a finite member containing induced copies of both $X$ and $E_n$ when
    $E_n\in\mathcal C$, and to be $X$ itself otherwise; retain the corresponding embeddings. -/)
  (title := /-- One extension step in the universal chain -/)
  (latexEnv := "definition")]
noncomputable def exists_universal_next (C : graph → Prop) (hjep : jep C)
    (X : {G : graph // Finite G.V ∧ C G}) (n : Nat) :
    Σ Y : {G : graph // Finite G.V ∧ C G},
      (X.1.G ↪g Y.1.G) × (C (exists_universal_code n) →
        (exists_universal_code n).G ↪g Y.1.G) := by
  by_cases h : C (exists_universal_code n)
  · have hfin : Finite (exists_universal_code n).V := by
      unfold exists_universal_code
      split <;> infer_instance
    let hJ := hjep X.1 (exists_universal_code n) X.2.1 hfin X.2.2 h
    let F := Classical.choose hJ
    let hF := Classical.choose_spec hJ
    exact ⟨⟨F, hF.1, hF.2.1⟩, Classical.choice hF.2.2.1,
      fun _ => Classical.choice hF.2.2.2⟩
  · exact ⟨X, SimpleGraph.Embedding.refl, fun hc => (h hc).elim⟩

@[blueprint "def:exists-universal-chain"
  (statement := /-- Starting with a fixed finite member of $\mathcal C$, recursively apply
    \cref{def:exists-universal-next} to obtain a sequence of finite members of $\mathcal C$. -/)
  (title := /-- The chain of finite class members -/)
  (latexEnv := "definition")]
noncomputable def exists_universal_chain (C : graph → Prop) (hjep : jep C)
    (hne : ∃ G : graph, Finite G.V ∧ C G) : Nat → {G : graph // Finite G.V ∧ C G}
  | 0 => ⟨Classical.choose hne, Classical.choose_spec hne⟩
  | n + 1 => (exists_universal_next C hjep (exists_universal_chain C hjep hne n) n).1

@[blueprint "def:exists-universal-step"
  (statement := /-- The retained embedding from the $n$th stage of
    \cref{def:exists-universal-chain} into its successor stage. -/)
  (title := /-- Successor embeddings in the universal chain -/)
  (latexEnv := "definition")]
noncomputable def exists_universal_step (C : graph → Prop) (hjep : jep C)
    (hne : ∃ G : graph, Finite G.V ∧ C G) (n : Nat) :
    (exists_universal_chain C hjep hne n).1.G ↪g
      (exists_universal_chain C hjep hne (n + 1)).1.G :=
  (exists_universal_next C hjep (exists_universal_chain C hjep hne n) n).2.1

@[blueprint "def:exists-universal-map"
  (statement := /-- For $i\le j$, compose the successor embeddings of
    \cref{def:exists-universal-step} to obtain an induced embedding from the $i$th stage into
    the $j$th stage. -/)
  (title := /-- Transition embeddings in the universal chain -/)
  (latexEnv := "definition")]
noncomputable def exists_universal_map (C : graph → Prop) (hjep : jep C)
    (hne : ∃ G : graph, Finite G.V ∧ C G) {i j : Nat} (hij : i ≤ j) :
    (exists_universal_chain C hjep hne i).1.G ↪g
      (exists_universal_chain C hjep hne j).1.G :=
  Nat.leRec (SimpleGraph.Embedding.refl)
    (fun _ _ e => (exists_universal_step C hjep hne _).comp e) hij

@[blueprint "lem:exists-universal-map-self"
  (statement := /-- The transition embedding of \cref{def:exists-universal-map} from any stage
    to itself is the identity embedding. -/)
  (proof := /-- This is the base equation of the recursion on the inequality used in
    \cref{def:exists-universal-map}. -/)
  (title := /-- Identity transition embedding -/)
  (latexEnv := "lemma")]
lemma exists_universal_map_self (C : graph → Prop) (hjep : jep C)
    (hne : ∃ G : graph, Finite G.V ∧ C G) (i : Nat) :
    exists_universal_map C hjep hne (Nat.le_refl i) = SimpleGraph.Embedding.refl := by
  simp [exists_universal_map]

@[blueprint "lem:exists-universal-map-succ"
  (statement := /-- The transition of \cref{def:exists-universal-map} from stage $i$ to stage
    $j+1$ is the transition from $i$ to $j$ followed by the successor embedding at $j$. -/)
  (proof := /-- This is the successor equation for the recursion defining
    \cref{def:exists-universal-map}. -/)
  (title := /-- Successor equation for transition embeddings -/)
  (latexEnv := "lemma")]
lemma exists_universal_map_succ (C : graph → Prop) (hjep : jep C)
    (hne : ∃ G : graph, Finite G.V ∧ C G) {i j : Nat} (hij : i ≤ j) :
    exists_universal_map C hjep hne (Nat.le_succ_of_le hij) =
      (exists_universal_step C hjep hne j).comp
        (exists_universal_map C hjep hne hij) := by
  unfold exists_universal_map
  exact Nat.leRec_succ _ _ hij

@[blueprint "lem:exists-universal-map-trans"
  (statement := /-- If $i\le j\le k$, then the transition embedding from $i$ to $k$ in
    \cref{def:exists-universal-map} is the composite of the transitions from $i$ to $j$ and
    from $j$ to $k$. -/)
  (proof := /-- Induct on $j\le k$. The base case is
    \cref{lem:exists-universal-map-self}. At a successor, apply
    \cref{lem:exists-universal-map-succ} to both transitions and use the induction hypothesis;
    associativity of embedding composition then identifies the two sides. -/)
  (title := /-- Composition of transition embeddings -/)
  (latexEnv := "lemma")]
lemma exists_universal_map_trans (C : graph → Prop) (hjep : jep C)
    (hne : ∃ G : graph, Finite G.V ∧ C G) {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k) :
    exists_universal_map C hjep hne (hij.trans hjk) =
      (exists_universal_map C hjep hne hjk).comp
        (exists_universal_map C hjep hne hij) := by
  induction hjk with
  | refl => simp [exists_universal_map_self]
  | @step k hjk ih =>
      rw [exists_universal_map_succ C hjep hne (hij.trans hjk),
        exists_universal_map_succ C hjep hne hjk, ih]
      rfl

@[blueprint "lem:exists-universal-code-embeds"
  (statement := /-- If the coded finite graph $E_n$ belongs to $\mathcal C$, then it embeds as
    an induced subgraph of stage $n+1$ of \cref{def:exists-universal-chain}. -/)
  (proof := /-- Under the membership hypothesis, \cref{def:exists-universal-next} retains the
    second embedding supplied by the joint embedding property; the successor equation in
    \cref{def:exists-universal-chain} identifies its codomain with stage $n+1$. -/)
  (title := /-- Each class member appears in the chain -/)
  (latexEnv := "lemma")]
lemma exists_universal_code_embeds (C : graph → Prop) (hjep : jep C)
    (hne : ∃ G : graph, Finite G.V ∧ C G) (n : Nat)
    (hC : C (exists_universal_code n)) :
    Nonempty ((exists_universal_code n).G ↪g
      (exists_universal_chain C hjep hne (n + 1)).1.G) := by
  exact ⟨(exists_universal_next C hjep (exists_universal_chain C hjep hne n) n).2.2 hC⟩

@[blueprint "def:exists-universal-setoid"
  (statement := /-- On the disjoint union of the vertex types in
    \cref{def:exists-universal-chain}, identify two stage vertices when their images agree in a
    common later stage under \cref{def:exists-universal-map}. -/)
  (title := /-- The vertex equivalence relation of the direct limit -/)
  (latexEnv := "definition")]
noncomputable def exists_universal_setoid (C : graph → Prop) (hjep : jep C)
    (hne : ∃ G : graph, Finite G.V ∧ C G) :
    Setoid (Σ n : Nat, (exists_universal_chain C hjep hne n).1.V) where
  r x y := ∃ (k : Nat) (hx : x.1 ≤ k) (hy : y.1 ≤ k),
    exists_universal_map C hjep hne hx x.2 = exists_universal_map C hjep hne hy y.2
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact ⟨x.1, Nat.le_refl _, Nat.le_refl _, rfl⟩
    · intro x y h
      obtain ⟨k, hx, hy, hxy⟩ := h
      exact ⟨k, hy, hx, hxy.symm⟩
    · intro x y z hxy hyz
      obtain ⟨j, hx, hy, hxy⟩ := hxy
      obtain ⟨k, hy', hz, hyz⟩ := hyz
      let l := max j k
      have hjl : j ≤ l := le_max_left _ _
      have hkl : k ≤ l := le_max_right _ _
      refine ⟨l, hx.trans hjl, hz.trans hkl, ?_⟩
      rw [exists_universal_map_trans C hjep hne hx hjl,
        exists_universal_map_trans C hjep hne hz hkl]
      change exists_universal_map C hjep hne hjl
          (exists_universal_map C hjep hne hx x.2) =
        exists_universal_map C hjep hne hkl
          (exists_universal_map C hjep hne hz z.2)
      rw [hxy, ← hyz]
      change ((exists_universal_map C hjep hne hjl).comp
          (exists_universal_map C hjep hne hy)) y.2 =
        ((exists_universal_map C hjep hne hkl).comp
          (exists_universal_map C hjep hne hy')) y.2
      rw [← exists_universal_map_trans C hjep hne hy hjl,
        ← exists_universal_map_trans C hjep hne hy' hkl]

@[blueprint "def:exists-universal-pre-adj"
  (statement := /-- Two stage vertices are preliminarily adjacent when their images are adjacent
    in some common later member of \cref{def:exists-universal-chain}. -/)
  (title := /-- Adjacency before passage to the direct limit -/)
  (latexEnv := "definition")]
noncomputable def exists_universal_pre_adj (C : graph → Prop) (hjep : jep C)
    (hne : ∃ G : graph, Finite G.V ∧ C G)
    (x y : Σ n : Nat, (exists_universal_chain C hjep hne n).1.V) : Prop :=
  ∃ (k : Nat) (hx : x.1 ≤ k) (hy : y.1 ≤ k),
    (exists_universal_chain C hjep hne k).1.G.Adj
      (exists_universal_map C hjep hne hx x.2)
      (exists_universal_map C hjep hne hy y.2)

@[blueprint "lem:exists-universal-pre-adj-symm"
  (statement := /-- The preliminary adjacency relation of
    \cref{def:exists-universal-pre-adj} is symmetric. -/)
  (proof := /-- Keep the same common stage and interchange the two transition images; symmetry
    of the simple graph at that stage gives the required adjacency. -/)
  (title := /-- Symmetry of preliminary adjacency -/)
  (latexEnv := "lemma")]
lemma exists_universal_pre_adj_symm (C : graph → Prop) (hjep : jep C)
    (hne : ∃ G : graph, Finite G.V ∧ C G)
    {x y : Σ n : Nat, (exists_universal_chain C hjep hne n).1.V}
    (h : exists_universal_pre_adj C hjep hne x y) :
    exists_universal_pre_adj C hjep hne y x := by
  obtain ⟨k, hx, hy, hxy⟩ := h
  exact ⟨k, hy, hx, hxy.symm⟩

@[blueprint "lem:exists-universal-pre-adj-congr"
  (statement := /-- Preliminary adjacency from \cref{def:exists-universal-pre-adj} is invariant
    under replacing either stage vertex by an equivalent representative for
    \cref{def:exists-universal-setoid}. -/)
  (proof := /-- For replacement in the first coordinate, choose a common stage above the stage
    witnessing adjacency and the stage witnessing equivalence. Push adjacency to that stage by
    the transition embedding and use \cref{lem:exists-universal-map-trans} to push the equality
    of representatives there as well. Reversing the equivalence proves the converse. Replacement
    in the second coordinate follows by applying \cref{lem:exists-universal-pre-adj-symm}, the
    first-coordinate result, and symmetry once more. -/)
  (title := /-- Representative invariance of preliminary adjacency -/)
  (latexEnv := "lemma")]
lemma exists_universal_pre_adj_congr (C : graph → Prop) (hjep : jep C)
    (hne : ∃ G : graph, Finite G.V ∧ C G)
    {x x' y y' : Σ n : Nat, (exists_universal_chain C hjep hne n).1.V}
    (hxx' : (exists_universal_setoid C hjep hne).r x x')
    (hyy' : (exists_universal_setoid C hjep hne).r y y') :
    exists_universal_pre_adj C hjep hne x y ↔
      exists_universal_pre_adj C hjep hne x' y' := by
  have forward : ∀ {a b c : Σ n : Nat, (exists_universal_chain C hjep hne n).1.V},
      (exists_universal_setoid C hjep hne).r a b →
      exists_universal_pre_adj C hjep hne a c →
      exists_universal_pre_adj C hjep hne b c := by
    intro a b c hab hac
    obtain ⟨j, ha, hb, hab⟩ := hab
    obtain ⟨k, ha', hc, hac⟩ := hac
    let l := max j k
    have hjl : j ≤ l := le_max_left _ _
    have hkl : k ≤ l := le_max_right _ _
    have hacl : (exists_universal_chain C hjep hne l).1.G.Adj
        (exists_universal_map C hjep hne (ha'.trans hkl) a.2)
        (exists_universal_map C hjep hne (hc.trans hkl) c.2) := by
      rw [exists_universal_map_trans C hjep hne ha' hkl,
        exists_universal_map_trans C hjep hne hc hkl]
      exact (exists_universal_map C hjep hne hkl).map_rel_iff'.2 hac
    have heq : exists_universal_map C hjep hne (ha.trans hjl) a.2 =
        exists_universal_map C hjep hne (hb.trans hjl) b.2 := by
      rw [exists_universal_map_trans C hjep hne ha hjl,
        exists_universal_map_trans C hjep hne hb hjl]
      exact congrArg (exists_universal_map C hjep hne hjl) hab
    refine ⟨l, hb.trans hjl, hc.trans hkl, ?_⟩
    rw [← heq]
    exact hacl
  have hleft : ∀ {a b c : Σ n : Nat, (exists_universal_chain C hjep hne n).1.V},
      (exists_universal_setoid C hjep hne).r a b →
      (exists_universal_pre_adj C hjep hne a c ↔
        exists_universal_pre_adj C hjep hne b c) := by
    intro a b c hab
    exact ⟨forward hab, forward ((exists_universal_setoid C hjep hne).symm hab)⟩
  constructor
  · intro hxy
    have hx'y := (hleft hxx').1 hxy
    have hyx' := exists_universal_pre_adj_symm C hjep hne hx'y
    have hy'x' := (hleft hyy').1 hyx'
    exact exists_universal_pre_adj_symm C hjep hne hy'x'
  · intro hx'y'
    have hy'x' := exists_universal_pre_adj_symm C hjep hne hx'y'
    have hyx' := (hleft hyy').2 hy'x'
    have hx'y := exists_universal_pre_adj_symm C hjep hne hyx'
    exact (hleft hxx').2 hx'y

@[blueprint "lem:exists-universal-pre-adj-same"
  (statement := /-- For two vertices represented in the same stage, preliminary adjacency from
    \cref{def:exists-universal-pre-adj} is equivalent to adjacency in that stage. -/)
  (proof := /-- An adjacency witnessed at a later stage reflects back along the transition graph
    embedding. Conversely, adjacency at the given stage witnesses preliminary adjacency there;
    \cref{lem:exists-universal-map-self} identifies both transition images with the original
    vertices. -/)
  (title := /-- Preliminary adjacency within one stage -/)
  (latexEnv := "lemma")]
lemma exists_universal_pre_adj_same (C : graph → Prop) (hjep : jep C)
    (hne : ∃ G : graph, Finite G.V ∧ C G) (i : Nat)
    (a b : (exists_universal_chain C hjep hne i).1.V) :
    exists_universal_pre_adj C hjep hne ⟨i, a⟩ ⟨i, b⟩ ↔
      (exists_universal_chain C hjep hne i).1.G.Adj a b := by
  constructor
  · rintro ⟨k, ha, hb, hab⟩
    have hp : ha = hb := Subsingleton.elim _ _
    subst hb
    exact (exists_universal_map C hjep hne ha).map_rel_iff'.1 hab
  · intro hab
    refine ⟨i, Nat.le_refl _, Nat.le_refl _, ?_⟩
    simpa [exists_universal_map_self] using hab

@[blueprint "def:exists-universal-limit"
  (statement := /-- The direct-limit graph of \cref{def:exists-universal-chain} has as vertices
    the quotient by \cref{def:exists-universal-setoid}; its adjacency is the quotient of
    \cref{def:exists-universal-pre-adj}. -/)
  (title := /-- Direct limit of the universal chain -/)
  (latexEnv := "definition")]
noncomputable def exists_universal_limit (C : graph → Prop) (hjep : jep C)
    (hne : ∃ G : graph, Finite G.V ∧ C G) : graph where
  V := Quotient (exists_universal_setoid C hjep hne)
  G :=
    { Adj := fun q r => Quotient.liftOn₂ q r
        (exists_universal_pre_adj C hjep hne)
        (by
          intro x x' y y' hxx' hyy'
          exact propext (exists_universal_pre_adj_congr C hjep hne hxx' hyy'))
      symm := ⟨by
        intro q r
        refine Quotient.inductionOn₂ q r ?_
        intro x y hxy
        exact exists_universal_pre_adj_symm C hjep hne hxy⟩
      loopless := ⟨by
        intro q
        refine Quotient.inductionOn q ?_
        intro x hxx
        exact (exists_universal_chain C hjep hne x.1).1.G.loopless.irrefl x.2
          ((exists_universal_pre_adj_same C hjep hne x.1 x.2 x.2).1 hxx)⟩ }

@[blueprint "def:exists-universal-stage-embedding"
  (statement := /-- Every graph in \cref{def:exists-universal-chain} embeds as an induced
    subgraph of its direct limit \cref{def:exists-universal-limit} by sending a stage vertex to
    its equivalence class. -/)
  (title := /-- Embedding of a stage into the direct limit -/)
  (latexEnv := "definition")]
noncomputable def exists_universal_stage_embedding (C : graph → Prop) (hjep : jep C)
    (hne : ∃ G : graph, Finite G.V ∧ C G) (i : Nat) :
    (exists_universal_chain C hjep hne i).1.G ↪g (exists_universal_limit C hjep hne).G where
  toFun a := Quotient.mk _ ⟨i, a⟩
  inj' := by
    intro a b hab
    obtain ⟨k, ha, hb, hab⟩ := Quotient.exact hab
    have hp : ha = hb := Subsingleton.elim _ _
    subst hb
    exact (exists_universal_map C hjep hne ha).injective hab
  map_rel_iff' := by
    intro a b
    change exists_universal_pre_adj C hjep hne ⟨i, a⟩ ⟨i, b⟩ ↔
      (exists_universal_chain C hjep hne i).1.G.Adj a b
    exact exists_universal_pre_adj_same C hjep hne i a b

@[blueprint "lem:exists-universal-mem-of-stage-embedding"
  (statement := /-- If a graph embeds as an induced subgraph of one stage of
    \cref{def:exists-universal-chain}, then it belongs to $\mathcal C$. -/)
  (proof := /-- Apply heredity to the range of the embedding inside the finite stage. The
    embedding induces an isomorphism between the original graph and the graph induced on that
    range, so isomorphism closure transports membership back to the original graph. -/)
  (title := /-- Membership inherited from a chain stage -/)
  (latexEnv := "lemma")]
lemma exists_universal_mem_of_stage_embedding (C : graph → Prop)
    (hiso : iso_closed C) (hher : hereditary C) (hjep : jep C)
    (hne : ∃ G : graph, Finite G.V ∧ C G) (G : graph) (i : Nat)
    (e : G.G ↪g (exists_universal_chain C hjep hne i).1.G) : C G := by
  let F := (exists_universal_chain C hjep hne i).1
  have hsub : C ⟨Set.range e, F.G.induce (Set.range e)⟩ :=
    hher F (Set.range e) (exists_universal_chain C hjep hne i).2.1
      (exists_universal_chain C hjep hne i).2.2
  exact hiso ⟨Set.range e, F.G.induce (Set.range e)⟩ G
    ⟨e.isoInduceRange.symm⟩ hsub

@[blueprint "lem:exists-universal-finite-embedding-lifts"
  (statement := /-- Every finite graph that embeds into
    \cref{def:exists-universal-limit} already embeds into one finite stage of
    \cref{def:exists-universal-chain}. -/)
  (proof := /-- Choose a stage representative for the image of each vertex. Since the domain is
    finite, the finitely many representative indices have a maximum $k$. Send each vertex to the
    image of its representative in stage $k$ under \cref{def:exists-universal-map}. The quotient
    equality, using \cref{lem:exists-universal-map-self}, shows that composing this map with
    \cref{def:exists-universal-stage-embedding} recovers the original embedding. Consequently the
    map is injective. Its adjacency-reflection law follows from
    \cref{lem:exists-universal-pre-adj-same} at stage $k$ and the representative invariance in
    \cref{lem:exists-universal-pre-adj-congr}; hence it is a graph embedding. -/)
  (title := /-- Finite embeddings into the limit occur at a stage -/)
  (latexEnv := "lemma")]
lemma exists_universal_finite_embedding_lifts (C : graph → Prop) (hjep : jep C)
    (hne : ∃ G : graph, Finite G.V ∧ C G) (G : graph) (hG : Finite G.V)
    (e : G.G ↪g (exists_universal_limit C hjep hne).G) :
    ∃ i : Nat, Nonempty (G.G ↪g (exists_universal_chain C hjep hne i).1.G) := by
  classical
  letI : Finite G.V := hG
  letI : Fintype G.V := Fintype.ofFinite G.V
  let rep (v : G.V) := Quotient.out (e v)
  let k := Finset.univ.sup (fun v : G.V => (rep v).1)
  have hk (v : G.V) : (rep v).1 ≤ k :=
    Finset.le_sup (s := Finset.univ) (f := fun w : G.V => (rep w).1)
      (Finset.mem_univ v)
  let f (v : G.V) := exists_universal_map C hjep hne (hk v) (rep v).2
  have hq (v : G.V) : exists_universal_stage_embedding C hjep hne k (f v) = e v := by
    calc
      Quotient.mk _ ⟨k, f v⟩ = Quotient.mk _ (rep v) := by
        apply Quotient.sound
        exact ⟨k, Nat.le_refl _, hk v, by simp [f, exists_universal_map_self]⟩
      _ = e v := Quotient.out_eq (e v)
  refine ⟨k, ⟨{ toFun := f, inj' := ?_, map_rel_iff' := ?_ }⟩⟩
  · intro a b hab
    apply e.injective
    rw [← hq a, ← hq b, hab]
  · intro a b
    have hra : (exists_universal_setoid C hjep hne).r ⟨k, f a⟩ (rep a) :=
      ⟨k, Nat.le_refl _, hk a, by simp [f, exists_universal_map_self]⟩
    have hrb : (exists_universal_setoid C hjep hne).r ⟨k, f b⟩ (rep b) :=
      ⟨k, Nat.le_refl _, hk b, by simp [f, exists_universal_map_self]⟩
    calc
      (exists_universal_chain C hjep hne k).1.G.Adj (f a) (f b) ↔
          exists_universal_pre_adj C hjep hne ⟨k, f a⟩ ⟨k, f b⟩ :=
        (exists_universal_pre_adj_same C hjep hne k (f a) (f b)).symm
      _ ↔ exists_universal_pre_adj C hjep hne (rep a) (rep b) :=
        exists_universal_pre_adj_congr C hjep hne hra hrb
      _ ↔ (exists_universal_limit C hjep hne).G.Adj (e a) (e b) := by
        rw [← Quotient.out_eq (e a), ← Quotient.out_eq (e b)]
        rfl
      _ ↔ G.G.Adj a b := e.map_rel_iff'

@[blueprint "lem:exists-universal"
  (statement := /-- Let $\mathcal{C}$ be a class of graphs that is closed under isomorphism,
    hereditary, has the joint embedding property, and suppose moreover that $\mathcal{C}$ has a
    non-empty finite part, i.e.\ there exists a \emph{finite} graph $\mathbf{G}$ (with
    $V(\mathbf{G})$ finite) such that $\mathbf{G} \in \mathcal{C}$. Then there is a graph
    $\mathbf{H}$ whose age equals the finite graphs of $\mathcal{C}$: for every finite graph
    $\mathbf{G}$ one has $\mathbf{G} \in \mathrm{Age}(\mathbf{H})$ iff $\mathbf{G} \in
    \mathcal{C}$. Such an $\mathbf{H}$ is a universal graph for the finite part of $\mathcal{C}$;
    we do \emph{not} assert $\mathbf{H} \in \mathcal{C}$, since the Fra\"iss\'e limit realising
    the age need not itself be a member of $\mathcal{C}$, and the downstream use of this graph
    (through \cref{lem:sp-eq-injcsp-of-universal} and \cref{lem:csp-star-subset-sp}) only refers
    to its age. See \cref{def:hereditary}, \cref{def:jep} and \cref{def:age}. -/)
  (proof := /-- Take $\mathbf H$ to be the direct-limit graph from
    \cref{def:exists-universal-limit}. Suppose first that a finite graph $G$ lies in
    $\mathrm{Age}(\mathbf H)$. Its induced embedding into $\mathbf H$ lifts to an embedding into
    a finite chain stage by \cref{lem:exists-universal-finite-embedding-lifts}; heredity and
    isomorphism closure then give $G\in\mathcal C$ by
    \cref{lem:exists-universal-mem-of-stage-embedding}. Conversely, let $G$ be finite and belong
    to $\mathcal C$. By \cref{lem:exists-universal-code-complete}, it is isomorphic to a coded
    graph $E_n$. Isomorphism closure gives $E_n\in\mathcal C$, and
    \cref{lem:exists-universal-code-embeds} embeds $E_n$ into stage $n+1$. Composing this
    embedding with the isomorphism and with the stage embedding from
    \cref{def:exists-universal-stage-embedding} embeds $G$ into $\mathbf H$. Thus the age of
    $\mathbf H$ is exactly the finite part of $\mathcal C$. -/)
  (title := /-- Existence of an age-realising universal graph -/)
  (latexEnv := "lemma")]
lemma exists_universal (C : graph → Prop)
    (hiso : iso_closed C) (hher : hereditary C) (hjep : jep C)
    (hne : ∃ G : graph, Finite G.V ∧ C G) :
    ∃ H : graph, ∀ G : graph, Finite G.V → (age H G ↔ C G) := by
  refine ⟨exists_universal_limit C hjep hne, ?_⟩
  intro G hG
  constructor
  · rintro ⟨_, ⟨e⟩⟩
    obtain ⟨i, ⟨ei⟩⟩ :=
      exists_universal_finite_embedding_lifts C hjep hne G hG e
    exact exists_universal_mem_of_stage_embedding C hiso hher hjep hne G i ei
  · intro hC
    obtain ⟨n, ⟨eiso⟩⟩ := exists_universal_code_complete G hG
    have hcode : C (exists_universal_code n) :=
      hiso G (exists_universal_code n) ⟨eiso⟩ hC
    obtain ⟨ecode⟩ := exists_universal_code_embeds C hjep hne n hcode
    refine ⟨hG, ⟨?_⟩⟩
    exact (exists_universal_stage_embedding C hjep hne (n + 1)).comp
      (ecode.comp eiso.toEmbedding)

@[blueprint "lem:sp-eq-injcsp-of-universal"
  (statement := /-- Let $\mathcal{C}$ be a class of graphs and let $\mathbf{H}$ be a universal
    graph in $\mathcal{C}$ (see \cref{def:is-universal}). Then, as classes of finite
    $2$-edge-coloured graphs, $\mathrm{SP}(\mathcal{C}) = \mathrm{injCSP}(H^{\ast})$. See
    \cref{def:sp}, \cref{def:inj-csp} and \cref{def:star}. -/)
  (proof := /-- Fix a $2$-edge-coloured graph $A$; we show $A \in \mathrm{SP}(\mathcal{C})$ iff
    $A \in \mathrm{injCSP}(H^{\ast})$ (see \cref{def:sp}, \cref{def:inj-csp}, \cref{def:star}).
    Suppose first $A \in \mathrm{SP}(\mathcal{C})$, witnessed by a finite $V(A)$ and a simple
    graph $E'$ on $V(A)$ with $B(A) \subseteq E'$, $E' \cap R(A) = \varnothing$, and
    $(V(A), E') \in \mathcal{C}$. Since $V(A)$ is finite and $\mathbf{H}$ is universal
    (\cref{def:is-universal}), the graph $(V(A), E')$ lies in $\mathrm{Age}(\mathbf{H})$
    (\cref{def:age}), so there is an induced-subgraph embedding $\varphi : E' \hookrightarrow H$.
    This $\varphi$ is injective; if $R(A)$-adjacent vertices $u, v$ are given then
    $\varphi(u) \neq \varphi(v)$ and $\varphi(u), \varphi(v)$ are non-adjacent in $H$ (because
    $E' \cap R(A) = \varnothing$ gives $\neg E'.\mathrm{Adj}(u,v)$ and $\varphi$ preserves and
    reflects adjacency), i.e.\ they are red-adjacent in $H^{\ast}$; and $B(A)$-adjacent vertices
    map to $H$-adjacent, i.e.\ blue-adjacent, vertices because $B(A) \subseteq E'$. Hence
    $A \hookrightarrow H^{\ast}$ and $A \in \mathrm{injCSP}(H^{\ast})$. Conversely, suppose
    $f : A \hookrightarrow H^{\ast}$ is an injective homomorphism. Let $E'$ be the pullback of
    $H$ along $f$, i.e.\ the simple graph on $V(A)$ with $u, v$ adjacent iff $f(u), f(v)$ are
    adjacent in $H$. Then $B(A) \subseteq E'$ because $f$ preserves blue edges, and
    $E' \cap R(A) = \varnothing$ because $f$ maps every $R(A)$-edge to a red edge of $H^{\ast}$,
    i.e.\ to a non-edge of $H$. As $f$ is injective, $E'$ embeds into $H$ as an induced subgraph,
    so $(V(A), E') \in \mathrm{Age}(\mathbf{H}) = \mathcal{C}$ by universality; thus
    $A \in \mathrm{SP}(\mathcal{C})$. -/)
  (title := /-- Universal graph identifies $\mathrm{SP}(\mathcal{C})$ with $\mathrm{injCSP}(H^{\ast})$ -/)
  (latexEnv := "lemma")]
lemma sp_eq_injcsp_of_universal (C : graph → Prop) (H : graph)
    (hu : is_universal C H) : sp C = inj_csp (star H) := by
  funext A
  apply propext
  constructor
  · rintro ⟨hfin, E', hblue, hred, hCE⟩
    refine ⟨hfin, ?_⟩
    have hage : age H ⟨A.V, E'⟩ := (hu.2 ⟨A.V, E'⟩ hfin).2 hCE
    obtain ⟨φ⟩ := hage.2
    refine ⟨φ, φ.injective, ?_, ?_⟩
    · intro u v huv
      have hne : φ u ≠ φ v := φ.injective.ne huv.ne
      have hnotE : ¬ E'.Adj u v := fun h => hred u v h huv
      have hnotG : ¬ H.G.Adj (φ u) (φ v) := by
        rw [φ.map_adj_iff]; exact hnotE
      show H.Gᶜ.Adj (φ u) (φ v)
      rw [SimpleGraph.compl_adj]
      exact ⟨hne, hnotG⟩
    · intro u v huv
      have hE : E'.Adj u v := hblue u v huv
      show H.G.Adj (φ u) (φ v)
      rw [φ.map_adj_iff]
      exact hE
  · rintro ⟨hfin, f, hinj, hred, hblue⟩
    refine ⟨hfin, H.G.comap f, ?_, ?_, ?_⟩
    · intro u v huv
      rw [SimpleGraph.comap_adj]
      exact hblue u v huv
    · intro u v huv hred'
      rw [SimpleGraph.comap_adj] at huv
      have hc : H.Gᶜ.Adj (f u) (f v) := hred u v hred'
      rw [SimpleGraph.compl_adj] at hc
      exact hc.2 huv
    · have hemb : Nonempty ((H.G.comap f) ↪g H.G) :=
        ⟨SimpleGraph.Embedding.comap ⟨f, hinj⟩ H.G⟩
      exact (hu.2 ⟨A.V, H.G.comap f⟩ hfin).1 ⟨hfin, hemb⟩

@[blueprint "lem:csp-star-subset-sp"
  (statement := /-- Let $\mathcal{C}$ be a class of graphs that is closed under isomorphism and
    preserved under split blow-ups, and let $\mathbf{H}$ be a universal graph in $\mathcal{C}$.
    Then every finite $2$-edge-coloured graph $A \in \mathrm{CSP}(H^{\ast})$ is a yes-instance of
    the sandwich problem, i.e.\ $A \in \mathrm{SP}(\mathcal{C})$. See \cref{def:csp},
    \cref{def:star}, \cref{def:sp}, \cref{def:iso-closed}, \cref{def:preserved-split-blow-up}
    and \cref{def:is-universal}. -/)
  (proof := /-- Fix $A \in \mathrm{CSP}(H^{\ast})$ (\cref{def:csp}), witnessed by a homomorphism
    $f : A \to H^{\ast}$ with $V(A)$ finite; we build a yes-instance of $\mathrm{SP}(\mathcal{C})$
    (\cref{def:sp}). Let $S := f(V(A)) \subseteq V(H)$ and let $\mathbf{G} := (S, H[S])$ be the
    induced subgraph of $\mathbf{H}$ on $S$. Then $\mathbf{G}$ is finite and embeds into
    $\mathbf{H}$ as an induced subgraph, so $\mathbf{G} \in \mathrm{Age}(\mathbf{H}) = \mathcal{C}$
    by universality (\cref{def:is-universal}, \cref{def:age}). By preservation under finite split
    blow-ups (\cref{def:preserved-split-blow-up}) there is a designation
    $\mathrm{twin} : S \to \mathrm{Prop}$ such that every split blow-up of $\mathbf{G}$ along
    $\mathrm{twin}$ with finite non-empty fibres lies in $\mathcal{C}$. Blow up each vertex
    $y \in S$ by its fibre $f^{-1}(y)$. Each fibre is finite because it is a subtype of the
    finite set $V(A)$, and it is non-empty because $y \in S = f(V(A))$; hence the resulting
    split blow-up $\mathbf{G}'$ (\cref{def:split-blow-up}) lies in $\mathcal{C}$, and its vertex set
    $\bigsqcup_{y \in S} f^{-1}(y)$ is in canonical bijection with $V(A)$ via
    $x \mapsto (f(x), x)$. Transporting $\mathbf{G}'$ along this bijection yields a simple graph
    $E'$ on $V(A)$ with $(V(A), E') \in \mathcal{C}$ by closure under isomorphism
    (\cref{def:iso-closed}). By construction, distinct $u, v$ with $f(u) \neq f(v)$ are
    $E'$-adjacent iff $f(u), f(v)$ are adjacent in $H$. Since $f$ preserves blue edges into
    $H^{\ast}$, every $B(A)$-edge $uv$ has $f(u), f(v)$ adjacent in $H$, in particular
    $f(u) \neq f(v)$, so $B(A) \subseteq E'$. If some $uv$ were both $E'$-adjacent and an
    $R(A)$-edge, then $f(u) \neq f(v)$ and $f(u), f(v)$ would be adjacent in $H$ (from $E'$) yet
    non-adjacent in $H$ (as $f$ maps $R(A)$-edges to red edges of $H^{\ast}$), a contradiction;
    hence $E' \cap R(A) = \varnothing$. Therefore $(V(A), E')$ witnesses
    $A \in \mathrm{SP}(\mathcal{C})$. -/)
  (title := /-- $\mathrm{CSP}(H^{\ast}) \subseteq \mathrm{SP}(\mathcal{C})$ via fibre blow-ups -/)
  (latexEnv := "lemma")]
lemma csp_star_subset_sp (C : graph → Prop) (hiso : iso_closed C)
    (hpres : preserved_split_blow_up C) (H : graph) (hu : is_universal C H)
    (A : tec) (hA : csp (star H) A) : sp C A := by
  rcases hA with ⟨hfin, f, hred, hblue⟩
  letI : Finite A.V := hfin
  let g : A.V → Set.range f := fun x => ⟨f x, Set.mem_range_self x⟩
  have hg_surj : Function.Surjective g := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  letI : Finite (Set.range f) := Finite.of_surjective g hg_surj
  let G : graph := ⟨Set.range f, H.G.comap (Subtype.val : Set.range f → H.V)⟩
  have hage : age H G := by
    refine ⟨by infer_instance, ?_⟩
    dsimp [G]
    exact ⟨SimpleGraph.Embedding.comap
      ⟨(Subtype.val : Set.range f → H.V), Subtype.val_injective⟩ H.G⟩
  have hCG : C G := (hu.2 G (by infer_instance)).1 hage
  obtain ⟨twin, htwin⟩ := hpres G (by infer_instance) hCG
  let β : G.V → Type := fun y => {x : A.V // g x = y}
  have hβfin : ∀ y, Finite (β y) := by
    intro y
    dsimp [β]
    infer_instance
  have hβne : ∀ y, Nonempty (β y) := by
    intro y
    obtain ⟨x, hx⟩ := hg_surj y
    exact ⟨⟨x, hx⟩⟩
  have hCB : C ⟨_, split_blow_up G twin β⟩ := htwin β hβfin hβne
  let e : (Σ y, β y) ≃ A.V := Equiv.sigmaFiberEquiv g
  let E' : SimpleGraph A.V := (split_blow_up G twin β).comap e.symm
  have hCE : C ⟨A.V, E'⟩ := by
    apply hiso ⟨_, split_blow_up G twin β⟩ ⟨A.V, E'⟩
    · simpa [E'] using
        (show Nonempty
          (split_blow_up G twin β ≃g (split_blow_up G twin β).comap e.symm) from
          ⟨(SimpleGraph.Iso.comap e.symm (split_blow_up G twin β)).symm⟩)
    · exact hCB
  refine ⟨hfin, E', ?_, ?_, hCE⟩
  · intro u v huv
    have hH : H.G.Adj (f u) (f v) := hblue u v huv
    have hgne : g u ≠ g v := fun h => hH.ne (congrArg Subtype.val h)
    change ((split_blow_up G twin β).comap e.symm).Adj u v
    rw [SimpleGraph.comap_adj]
    unfold split_blow_up
    rw [SimpleGraph.fromRel_adj]
    change e.symm u ≠ e.symm v ∧
      (((g u = g v ∧ ¬ twin (g u)) ∨ (g u ≠ g v ∧ G.G.Adj (g u) (g v))) ∨
       ((g v = g u ∧ ¬ twin (g v)) ∨ (g v ≠ g u ∧ G.G.Adj (g v) (g u))))
    refine ⟨e.symm.injective.ne huv.ne, Or.inl (Or.inr ⟨hgne, ?_⟩)⟩
    change H.G.Adj (f u) (f v)
    exact hH
  · intro u v huv hruv
    have hc : H.Gᶜ.Adj (f u) (f v) := hred u v hruv
    rw [SimpleGraph.compl_adj] at hc
    have hgne : g u ≠ g v := fun h => hc.1 (congrArg Subtype.val h)
    change ((split_blow_up G twin β).comap e.symm).Adj u v at huv
    rw [SimpleGraph.comap_adj] at huv
    unfold split_blow_up at huv
    rw [SimpleGraph.fromRel_adj] at huv
    change e.symm u ≠ e.symm v ∧
      (((g u = g v ∧ ¬ twin (g u)) ∨ (g u ≠ g v ∧ G.G.Adj (g u) (g v))) ∨
       ((g v = g u ∧ ¬ twin (g v)) ∨ (g v ≠ g u ∧ G.G.Adj (g v) (g u)))) at huv
    rcases huv.2 with (h | h) <;> rcases h with (h | h)
    · exact hgne h.1
    · apply hc.2
      have hadj := h.2
      change H.G.Adj (f u) (f v) at hadj
      exact hadj
    · exact hgne h.1.symm
    · apply hc.2
      have hadj := h.2
      change H.G.Adj (f v) (f u) at hadj
      exact hadj.symm

@[blueprint "lem:h-to-star"
  (statement := /-- Let $\mathcal{C}$ be a class of graphs that is closed under isomorphism,
    hereditary, has the joint embedding property, and is preserved under split blow-ups, and let
    $\mathbf{H}$ be a universal graph in $\mathcal{C}$. Then, as classes of finite
    $2$-edge-coloured graphs, $\mathrm{SP}(\mathcal{C}) = \mathrm{injCSP}(H^{\ast})$ and
    $\mathrm{injCSP}(H^{\ast}) = \mathrm{CSP}(H^{\ast})$. See \cref{def:sp}, \cref{def:inj-csp},
    \cref{def:csp}, \cref{def:star} and \cref{def:is-universal}. -/)
  (proof := /-- We prove the two equalities separately. The equality
    $\mathrm{SP}(\mathcal{C}) = \mathrm{injCSP}(H^{\ast})$ is exactly
    \cref{lem:sp-eq-injcsp-of-universal}, applied to the universal graph $\mathbf{H}$. For the
    equality $\mathrm{injCSP}(H^{\ast}) = \mathrm{CSP}(H^{\ast})$ we argue by mutual inclusion at
    each finite $2$-edge-coloured graph $A$. Every injective homomorphism is a homomorphism, so
    $A \in \mathrm{injCSP}(H^{\ast})$ implies $A \in \mathrm{CSP}(H^{\ast})$. Conversely, if
    $A \in \mathrm{CSP}(H^{\ast})$ then $A \in \mathrm{SP}(\mathcal{C})$ by
    \cref{lem:csp-star-subset-sp}, and hence $A \in \mathrm{injCSP}(H^{\ast})$ by the first
    equality. Therefore the two classes coincide. -/)
  (title := /-- Universal graph collapses $\mathrm{SP}$, $\mathrm{CSP}$ and $\mathrm{injCSP}$ -/)
  (latexEnv := "lemma")]
lemma h_to_star (C : graph → Prop)
    (hiso : iso_closed C) (hher : hereditary C) (hjep : jep C)
    (hpres : preserved_split_blow_up C) (H : graph) (hu : is_universal C H) :
    sp C = inj_csp (star H) ∧ inj_csp (star H) = csp (star H) := by
  refine ⟨sp_eq_injcsp_of_universal C H hu, ?_⟩
  funext A
  apply propext
  constructor
  · rintro ⟨hfin, f, -, hred, hblue⟩
    exact ⟨hfin, f, hred, hblue⟩
  · intro hA
    have hsp : sp C A := csp_star_subset_sp C hiso hpres H hu A hA
    rw [sp_eq_injcsp_of_universal C H hu] at hsp
    exact hsp

@[blueprint "lem:h-to-star-of-finite-universal"
  (statement := /-- Let $\mathcal{C}$ be a hereditary class of graphs closed under isomorphism,
    with the joint embedding property, and preserved under split blow-ups. If a graph
    $\mathbf{H}$ has age equal to the finite members of
    $\mathcal{C}$, then $\mathrm{SP}(\mathcal{C}) = \mathrm{injCSP}(H^{\ast})$ and
    $\mathrm{injCSP}(H^{\ast}) = \mathrm{CSP}(H^{\ast})$. No assumption that
    $\mathbf{H} \in \mathcal{C}$ is required. -/)
  (proof := /-- Enlarge $\mathcal{C}$ to the class $\mathcal{D}$ consisting of its members
    together with every graph having an infinite vertex set. On finite graphs the classes
    $\mathcal{C}$ and $\mathcal{D}$ coincide. Hence $\mathcal{D}$ is hereditary, has the joint
    embedding property, and is preserved under split blow-ups; it is also closed under
    isomorphism, since graph isomorphisms preserve finiteness. Moreover,
    $\mathbf{H}$ is universal in $\mathcal{D}$: the assumed age equality supplies the finite
    part, while $\mathbf{H} \in \mathcal{D}$ follows either from infinitude or, when
    $\mathbf{H}$ is finite, from its identity embedding into itself. Applying
    \cref{lem:h-to-star} to $\mathcal{D}$ gives both required equalities with
    $\mathrm{SP}(\mathcal{D})$. Since sandwich witnesses are finite,
    $\mathrm{SP}(\mathcal{C}) = \mathrm{SP}(\mathcal{D})$, which yields the result. -/)
  (title := /-- An age-realising graph collapses $\mathrm{SP}$, $\mathrm{CSP}$ and
    $\mathrm{injCSP}$ -/)
  (latexEnv := "lemma")]
lemma h_to_star_of_finite_universal (C : graph → Prop)
    (hiso : iso_closed C) (hher : hereditary C) (hjep : jep C)
    (hpres : preserved_split_blow_up C) (H : graph)
    (hu : ∀ G : graph, Finite G.V → (age H G ↔ C G)) :
    sp C = inj_csp (star H) ∧ inj_csp (star H) = csp (star H) := by
  classical
  let D : graph → Prop := fun G => C G ∨ ¬ Finite G.V
  have hDfinite (G : graph) (hG : Finite G.V) : D G ↔ C G := by
    simp [D, hG]
  have hDiso : iso_closed D := by
    intro G K hGK hDG
    change C G ∨ ¬ Finite G.V at hDG
    change C K ∨ ¬ Finite K.V
    rcases hDG with hCG | hGinf
    · exact Or.inl (hiso G K hGK hCG)
    · right
      intro hK
      obtain ⟨e⟩ := hGK
      letI : Finite K.V := hK
      exact hGinf (Finite.of_equiv K.V e.toEquiv.symm)
  have hDher : hereditary D := by
    intro G s hG hDG
    exact Or.inl (hher G s hG ((hDfinite G hG).1 hDG))
  have hDjep : jep D := by
    intro G K hG hK hDG hDK
    obtain ⟨F, hF, hCF, eG, eK⟩ :=
      hjep G K hG hK ((hDfinite G hG).1 hDG) ((hDfinite K hK).1 hDK)
    exact ⟨F, hF, Or.inl hCF, eG, eK⟩
  have hDpres : preserved_split_blow_up D := by
    intro G hG hDG
    have hCG : C G := (hDfinite G hG).1 hDG
    obtain ⟨twin, htwin⟩ := hpres G hG hCG
    refine ⟨twin, ?_⟩
    intro β hβfinite hβnonempty
    exact Or.inl (htwin β hβfinite hβnonempty)
  have hDH : D H := by
    change C H ∨ ¬ Finite H.V
    by_cases hH : Finite H.V
    · left
      exact (hu H hH).1 ⟨hH, ⟨SimpleGraph.Embedding.refl⟩⟩
    · exact Or.inr hH
  have hDu : is_universal D H := by
    refine ⟨hDH, ?_⟩
    intro G hG
    exact (hu G hG).trans (hDfinite G hG).symm
  have hspCD : sp C = sp D := by
    funext A
    apply propext
    constructor
    · rintro ⟨hfinite, E', hblue, hred, hC⟩
      exact ⟨hfinite, E', hblue, hred, Or.inl hC⟩
    · rintro ⟨hfinite, E', hblue, hred, hD⟩
      exact ⟨hfinite, E', hblue, hred, (hDfinite ⟨A.V, E'⟩ hfinite).1 hD⟩
  obtain ⟨hDspinj, hDinjsp⟩ := h_to_star D hDiso hDher hDjep hDpres H hDu
  exact ⟨hspCD.trans hDspinj, hDinjsp⟩

@[blueprint "lem:three-of-one"
  (statement := /-- Let $\mathcal{C}$ be a class of graphs closed under isomorphism containing at
    least one finite graph. If $\mathcal{C}$ is hereditary, has the joint embedding property, and
    is preserved under split blow-ups, then there is a graph $\mathbf{H}$ with
    $\mathrm{SP}(\mathcal{C}) = \mathrm{CSP}(H^{\ast})$ and
    $\mathrm{CSP}(H^{\ast}) = \mathrm{injCSP}(H^{\ast})$. The non-emptiness side condition is
    what \cref{lem:exists-universal} consumes: an empty class admits no universal graph, while
    $\mathrm{CSP}(T)$ always contains the empty instance. See \cref{def:sp}, \cref{def:csp},
    \cref{def:inj-csp} and \cref{def:star}. -/)
  (proof := /-- By \cref{lem:exists-universal} there is a graph $\mathbf{H}$ whose age is the
    finite part of $\mathcal{C}$. Applying \cref{lem:h-to-star-of-finite-universal} to
    $\mathbf{H}$ gives
    $\mathrm{SP}(\mathcal{C}) = \mathrm{injCSP}(H^{\ast})$ and
    $\mathrm{injCSP}(H^{\ast}) = \mathrm{CSP}(H^{\ast})$; rearranging these two equalities yields
    $\mathrm{SP}(\mathcal{C}) = \mathrm{CSP}(H^{\ast})$ and
    $\mathrm{CSP}(H^{\ast}) = \mathrm{injCSP}(H^{\ast})$, as required. -/)
  (title := /-- (1) $\Rightarrow$ (3) -/)
  (latexEnv := "lemma")]
lemma three_of_one (C : graph → Prop)
    (hiso : iso_closed C) (hher : hereditary C) (hjep : jep C)
    (hpres : preserved_split_blow_up C) (hne : ∃ G : graph, Finite G.V ∧ C G) :
    ∃ H : graph, sp C = csp (star H) ∧ csp (star H) = inj_csp (star H) := by
  obtain ⟨H, hu⟩ := exists_universal C hiso hher hjep hne
  obtain ⟨hsp, hinj⟩ :=
    h_to_star_of_finite_universal C hiso hher hjep hpres H hu
  exact ⟨H, hsp.trans hinj, hinj.symm⟩

@[blueprint "lem:two-of-three"
  (statement := /-- If there is a graph $\mathbf{H}$ with
    $\mathrm{SP}(\mathcal{C}) = \mathrm{CSP}(H^{\ast})$ and
    $\mathrm{CSP}(H^{\ast}) = \mathrm{injCSP}(H^{\ast})$, then there is a $2$-edge-coloured graph
    $T$ with $\mathrm{CSP}(T) = \mathrm{SP}(\mathcal{C})$. See \cref{def:csp}, \cref{def:sp} and
    \cref{def:star}. -/)
  (proof := /-- Take $T := H^{\ast}$, which is a $2$-edge-coloured graph. The hypothesis gives
    $\mathrm{SP}(\mathcal{C}) = \mathrm{CSP}(H^{\ast})$, hence
    $\mathrm{CSP}(T) = \mathrm{CSP}(H^{\ast}) = \mathrm{SP}(\mathcal{C})$, which is the desired
    witness. -/)
  (title := /-- (3) $\Rightarrow$ (2) -/)
  (latexEnv := "lemma")]
lemma two_of_three (C : graph → Prop)
    (h : ∃ H : graph, sp C = csp (star H) ∧ csp (star H) = inj_csp (star H)) :
    ∃ T : tec, csp T = sp C := by
  obtain ⟨H, hsp, _⟩ := h
  exact ⟨star H, hsp.symm⟩

@[blueprint "lem:hereditary-of-two"
  (statement := /-- Let $\mathcal{C}$ be a class of graphs closed under isomorphism. If there is
    a $2$-edge-coloured graph $T$ with $\mathrm{CSP}(T) = \mathrm{SP}(\mathcal{C})$, then
    $\mathcal{C}$ is hereditary. See \cref{def:csp}, \cref{def:sp} and \cref{def:hereditary}. -/)
  (proof := /-- Let $\mathbf{G} \in \mathcal{C}$ and let $\mathbf{H}$ be an induced subgraph of
    $\mathbf{G}$; by \cref{def:hereditary} we may assume $\mathbf{G}$ is finite, so that
    $\mathbf{H}$ is finite as well. There is an evident colour-preserving homomorphism
    $H^{\ast} \to G^{\ast}$ induced by the inclusion of vertices. Since $\mathbf{G} \in
    \mathcal{C}$ and $\mathbf{G}$ is finite, $G^{\ast}$ is a yes-instance of the sandwich problem
    for $\mathcal{C}$, so by $\mathrm{CSP}(T) = \mathrm{SP}(\mathcal{C})$ we get
    $G^{\ast} \to T$; composing with $H^{\ast} \to G^{\ast}$ gives $H^{\ast} \to T$, i.e.\
    $H^{\ast}$ is a yes-instance again, and hence $\mathbf{H} \in \mathcal{C}$. Thus
    $\mathcal{C}$ is closed under taking induced subgraphs of its finite members. -/)
  (title := /-- (2) $\Rightarrow$ hereditary -/)
  (latexEnv := "lemma")]
lemma hereditary_of_two (C : graph → Prop)
    (hiso : iso_closed C) (h : ∃ T : tec, csp T = sp C) : hereditary C := by
  obtain ⟨T, hT⟩ := h
  intro G s hfin hCG
  haveI : Finite G.V := hfin
  have hGsp : sp C (star G) := by
    refine ⟨hfin, G.G, fun u v h => h, ?_, hCG⟩
    intro u v huv hred
    exact ((SimpleGraph.compl_adj G.G u v).1 hred).2 huv
  have hGcsp : csp T (star G) := by rw [hT]; exact hGsp
  obtain ⟨fG, hfGred, hfGblue⟩ := hGcsp.2
  have hHcsp : csp T (star ⟨↥s, G.G.induce s⟩) := by
    refine ⟨(inferInstance : Finite (↥s)), fun w : ↥s => fG (↑w : G.V), ?_, ?_⟩
    · intro u v huv
      have h2 := (SimpleGraph.compl_adj (G.G.induce s) u v).1 huv
      exact hfGred u.1 v.1
        ((SimpleGraph.compl_adj G.G u.1 v.1).2 ⟨Subtype.coe_injective.ne h2.1, h2.2⟩)
    · intro u v huv
      exact hfGblue u.1 v.1 huv
  have hHsp : sp C (star ⟨↥s, G.G.induce s⟩) := by rw [← hT]; exact hHcsp
  obtain ⟨_, E', hb, hr, hCE⟩ := hHsp
  have hEeq : E' = G.G.induce s := by
    ext u v
    constructor
    · intro he
      have hne := he.ne
      by_contra hcon
      exact hr u v he ((SimpleGraph.compl_adj (G.G.induce s) u v).2 ⟨hne, hcon⟩)
    · intro he
      exact hb u v he
  rw [hEeq] at hCE
  exact hCE

@[blueprint "lem:blowup-single"
  (statement := /-- Let $\mathcal{C}$ be a class of graphs closed under isomorphism and
    hereditary, and suppose there is a $2$-edge-coloured graph $T$ with
    $\mathrm{CSP}(T) = \mathrm{SP}(\mathcal{C})$. Let $\mathbf{G} = (V, G) \in \mathcal{C}$ be a
    \emph{finite} graph (i.e.\ $V$ finite), let $v \in V$, and let $\beta : V \to \mathrm{Type}$
    assign non-empty sets with $\beta(u)$ a singleton for $u \neq v$ and $\beta(v)$ a
    \emph{finite} set (so that $v$ is substituted by a positive integer number
    $n = |\beta(v)|$ of vertices). Then \emph{some} choice of designation works: there is a
    proposition $\mathrm{isTwin}$ (either all twins, $\mathrm{isTwin}$ true, or all co-twins,
    $\mathrm{isTwin}$ false) for which the split blow-up substituting $v$ by $\beta(v)$ again
    lies in $\mathcal{C}$; note the substituted graph is finite because $V$ and $\beta(v)$ are
    finite. Only one designation is asserted, because the Ramsey argument below extracts a
    monochromatic set that is a clique \emph{or} an independent set, the choice being forced by
    the sandwich solution rather than free. See \cref{def:split-blow-up}, \cref{def:csp} and
    \cref{def:sp}. -/)
  (proof := /-- Put $n=|\beta(v)|$, and choose $r$ from \cref{lem:ramsey}. The complete
    $2$-edge-coloured graph $G^{\ast}$ is a sandwich yes-instance, witnessed by $G$ itself;
    hence the equality $\mathrm{CSP}(T)=\mathrm{SP}(\mathcal C)$ supplies a colour-preserving
    homomorphism $G^{\ast}\to T$. Here we use \cref{def:star, def:csp, def:sp}.

    Define a finite $2$-edge-coloured graph $A$ on
    $V(G)\times\operatorname{Option}(\operatorname{Fin} r)$ by pulling both colours of
    $G^{\ast}$ back along the first projection. Composing that projection with
    $G^{\ast}\to T$ proves $A\in\mathrm{CSP}(T)$, and therefore $A\in\mathrm{SP}(\mathcal C)$.
    Thus there is a graph $E$ on $V(A)$ such that $(V(A),E)\in\mathcal C$, every blue edge of
    $A$ belongs to $E$, and no red edge of $A$ belongs to $E$. In particular, whenever two
    vertices of $A$ have distinct first coordinates, they are $E$-adjacent if and only if
    their first coordinates are adjacent in $G$.

    Apply \cref{lem:ramsey} to the graph on $\operatorname{Fin} r$ in which $i$ and $j$ are
    adjacent precisely when $(v,\operatorname{some} i)$ and
    $(v,\operatorname{some} j)$ are $E$-adjacent. We obtain a set $s$ of cardinality $n$
    which is a clique or an independent set. Choose a bijection $e:\beta(v)\to s$, and set
    $\mathrm{isTwin}$ to be false in the clique case and true in the independent-set case.
    Define
    \[
      f:\bigsqcup_{u\in V(G)}\beta(u)\longrightarrow V(A)
    \]
    by $f(v,a)=(v,\operatorname{some}(e(a)))$ and
    $f(u,a)=(u,\operatorname{none})$ for $u\ne v$. This map is injective: the map over $v$ is
    induced by the bijection $e$, while every fiber $\beta(u)$ with $u\ne v$ is a
    subsingleton.

    The preceding characterization of cross-fiber edges, together with the homogeneity of
    $s$, shows that $f$ is an induced graph embedding from the split blow-up in
    \cref{def:split-blow-up} into $E$. Its image-induced subgraph belongs to $\mathcal C$ by
    heredity, \cref{def:hereditary}; the canonical isomorphism from the split blow-up to this
    image then transfers membership back by isomorphism closure,
    \cref{def:iso-closed}. Hence the asserted designation yields a split blow-up in
    $\mathcal C$. -/)
  (title := /-- Single-vertex twin/co-twin substitution stays in $\mathcal{C}$ -/)
  (latexEnv := "lemma")]
lemma blowup_single (C : graph → Prop)
    (hiso : iso_closed C) (hher : hereditary C) (h : ∃ T : tec, csp T = sp C)
    (G : graph) (hVfin : Finite G.V) (hG : C G) (v : G.V) (β : G.V → Type)
    (hβv : Finite (β v))
    (hβ : ∀ u, u ≠ v → Subsingleton (β u)) (hne : ∀ u, Nonempty (β u)) :
    ∃ isTwin : Prop, C ⟨_, split_blow_up G (fun _ => isTwin) β⟩ := by
  classical
  haveI : Finite G.V := hVfin
  letI : Fintype G.V := Fintype.ofFinite G.V
  haveI : Finite (β v) := hβv
  letI : Fintype (β v) := Fintype.ofFinite (β v)
  obtain ⟨T, hT⟩ := h
  have hGsp : sp C (star G) := by
    refine ⟨hVfin, G.G, fun _ _ h => h, ?_, hG⟩
    intro u w huw hred
    exact ((SimpleGraph.compl_adj G.G u w).1 hred).2 huw
  have hGcsp : csp T (star G) := by
    rw [hT]
    exact hGsp
  obtain ⟨g, hgred, hgblue⟩ := hGcsp.2
  obtain ⟨r, hr⟩ := ramsey (Fintype.card (β v))
  let A : tec :=
    { V := G.V × Option (Fin r)
      red := G.Gᶜ.comap Prod.fst
      blue := G.G.comap Prod.fst
      disjoint := by
        intro p q hpq
        exact ((SimpleGraph.compl_adj G.G p.1 q.1).1 hpq.1).2 hpq.2 }
  have hAfin : Finite A.V := by
    dsimp [A]
    infer_instance
  have hAcsp : csp T A := by
    refine ⟨hAfin, fun p => g p.1, ?_, ?_⟩
    · intro p q hpq
      exact hgred p.1 q.1 hpq
    · intro p q hpq
      exact hgblue p.1 q.1 hpq
  have hAsp : sp C A := by
    rw [← hT]
    exact hAcsp
  obtain ⟨_, E, hblue, hred, hCE⟩ := hAsp
  obtain ⟨s, hscard, hs⟩ :=
    hr (Fin r) (by simp) (E.comap fun i : Fin r => (v, some i))
  let ev : β v ≃ ↥s :=
    Fintype.equivOfCardEq (by simpa using hscard.symm)
  obtain ⟨isTwin, hmono⟩ :
      ∃ isTwin : Prop, ∀ a b : β v,
        E.Adj (v, some (ev a).1) (v, some (ev b).1) ↔ a ≠ b ∧ ¬ isTwin := by
    rcases hs with hclique | hindep
    · refine ⟨False, ?_⟩
      intro a b
      constructor
      · intro hab
        exact ⟨fun h => hab.ne (by rw [h]), by simp⟩
      · rintro ⟨hab, _⟩
        have hev : (ev a).1 ≠ (ev b).1 := by
          intro he
          apply hab
          exact ev.injective (Subtype.ext he)
        simpa using hclique (ev a).1 (ev a).2 (ev b).1 (ev b).2 hev
    · refine ⟨True, ?_⟩
      intro a b
      constructor
      · intro hab
        exfalso
        by_cases heq : a = b
        · exact hab.ne (by rw [heq])
        · have hev : (ev a).1 ≠ (ev b).1 := by
            intro he
            apply heq
            exact ev.injective (Subtype.ext he)
          exact (hindep (ev a).1 (ev a).2 (ev b).1 (ev b).2 hev) (by simpa using hab)
      · rintro ⟨_, hfalse⟩
        exact False.elim (hfalse trivial)
  let f : (Σ u, β u) → A.V := fun p =>
    if huv : p.1 = v then
      (p.1, some (ev (huv ▸ p.2)).1)
    else
      (p.1, none)
  have hf_v (a : β v) : f ⟨v, a⟩ = (v, some (ev a).1) := by
    simp [f]
  have hf_fst (p : Σ u, β u) : (f p).1 = p.1 := by
    dsimp [f]
    split <;> rfl
  have hf_inj : Function.Injective f := by
    rintro ⟨u, a⟩ ⟨w, b⟩ heq
    have huw : u = w := by
      have hfirst := congrArg Prod.fst heq
      simpa only [hf_fst] using hfirst
    subst w
    congr 1
    by_cases huv : u = v
    · subst u
      have hsecond := congrArg Prod.snd heq
      simp [f] at hsecond
      exact hsecond
    · letI : Subsingleton (β u) := hβ u huv
      exact Subsingleton.elim _ _
  have hcross (p q : A.V) (hpq : p.1 ≠ q.1) :
      E.Adj p q ↔ G.G.Adj p.1 q.1 := by
    constructor
    · intro hE
      by_contra hGpq
      exact hred p q hE
        ((SimpleGraph.compl_adj G.G p.1 q.1).2 ⟨hpq, hGpq⟩)
    · intro hGpq
      exact hblue p q hGpq
  let emb : split_blow_up G (fun _ => isTwin) β ↪g E :=
    ⟨⟨f, hf_inj⟩, by
      rintro ⟨u, a⟩ ⟨w, b⟩
      by_cases huw : u = w
      · subst w
        by_cases huv : u = v
        · subst u
          change E.Adj (f ⟨v, a⟩) (f ⟨v, b⟩) ↔ _
          rw [hf_v, hf_v, hmono]
          simp [split_blow_up]
        · letI : Subsingleton (β u) := hβ u huv
          have hab : a = b := Subsingleton.elim _ _
          subst b
          simp
      · change E.Adj (f ⟨u, a⟩) (f ⟨w, b⟩) ↔ _
        rw [hcross]
        · rw [hf_fst, hf_fst]
          simp [split_blow_up, huw, Ne.symm huw, SimpleGraph.adj_comm]
        · simpa only [hf_fst] using huw⟩
  have hCind : C ⟨_, E.induce (Set.range emb)⟩ :=
    hher ⟨A.V, E⟩ (Set.range emb) hAfin hCE
  refine ⟨isTwin, ?_⟩
  exact hiso _ _ ⟨emb.isoInduceRange.symm⟩ hCind

@[blueprint "lem:star-sp-of-mem"
  (statement := /-- Let $\mathcal{C}$ be a class of graphs and let $\mathbf{G} = (V, G)$ be a
    \emph{finite} graph (i.e.\ $V$ finite) with $\mathbf{G} \in \mathcal{C}$. Then its complete
    $2$-edge-coloured graph $G^{\ast}$ is a yes-instance of the sandwich problem
    $\mathrm{SP}(\mathcal{C})$, witnessed by the edge set $E' = G$ itself. See \cref{def:graph},
    \cref{def:star} and \cref{def:sp}. -/)
  (proof := /-- By \cref{def:star} the graph $G^{\ast}$ has vertex set $V$, blue graph $G$ and
    red graph the complement $G^{c}$. Take $E' = G$. Then trivially $B(G^{\ast}) = G \subseteq E'$;
    for the red edges, if $uv$ is an edge of $E' = G$ then $u, v$ are $G$-adjacent, so $uv$ is not
    a non-edge of $G$, i.e.\ $uv \notin G^{c} = R(G^{\ast})$; and $(V, E') = (V, G) = \mathbf{G}
    \in \mathcal{C}$. Since $V$ is finite this exhibits $G^{\ast}$ as a yes-instance of
    $\mathrm{SP}(\mathcal{C})$ (see \cref{def:sp}). -/)
  (title := /-- The complete graph of a member is a sandwich yes-instance -/)
  (latexEnv := "lemma")]
lemma star_sp_of_mem (C : graph → Prop) (G : graph) (hfin : Finite G.V)
    (hG : C G) : sp C (star G) := by
  refine ⟨hfin, G.G, ?_, ?_, hG⟩
  · intro u v h
    exact h
  · intro u v h
    intro hc
    exact ((SimpleGraph.compl_adj G.G u v).1 hc).2 h

@[blueprint "lem:jep-of-two"
  (statement := /-- Let $\mathcal{C}$ be a class of graphs closed under isomorphism. If there is
    a $2$-edge-coloured graph $T$ with $\mathrm{CSP}(T) = \mathrm{SP}(\mathcal{C})$, then
    $\mathcal{C}$ has the joint embedding property. See \cref{def:csp}, \cref{def:sp} and
    \cref{def:jep}. -/)
  (proof := /-- To prove the joint embedding property, fix \emph{finite}
    $\mathbf{G}, \mathbf{H} \in \mathcal{C}$.
    Their complete $2$-edge-coloured graphs $G^{\ast}, H^{\ast}$ are yes-instances of
    $\mathrm{SP}(\mathcal{C})$ by \cref{lem:star-sp-of-mem}, hence lie in $\mathrm{CSP}(T)$ since
    $\mathrm{CSP}(T) = \mathrm{SP}(\mathcal{C})$. By \cref{lem:csp-disjoint-union} their disjoint
    union $G^{\ast} + H^{\ast} \in \mathrm{CSP}(T) = \mathrm{SP}(\mathcal{C})$, so there is a
    simple graph $E'$ on $V(G) \sqcup V(H)$ with $B(G^{\ast} + H^{\ast}) \subseteq E'$,
    $E' \cap R(G^{\ast} + H^{\ast}) = \varnothing$ and $(V(G) \sqcup V(H), E') \in \mathcal{C}$.
    Take $\mathbf{F} = (V(G) \sqcup V(H), E')$. Its vertex set is finite because $V(G)$ and
    $V(H)$ are finite. The left inclusion $V(G) \hookrightarrow V(G) \sqcup V(H)$ is a graph
    embedding $G \hookrightarrow F$: for $u, v \in V(G)$, if $uv \in E'$ then $u \neq v$ and
    $uv$ is not red in $G^{\ast} + H^{\ast}$, i.e.\ $uv$ is not a non-edge of $G$, so
    $uv \in E(G)$; conversely every blue edge $uv$ of $G^{\ast}$ (an edge of $G$) lies in $E'$
    since $B(G^{\ast} + H^{\ast}) \subseteq E'$. The right inclusion gives
    $H \hookrightarrow F$ symmetrically. Hence the finite graph $\mathbf{F} \in \mathcal{C}$
    contains both $\mathbf{G}$ and $\mathbf{H}$ as induced subgraphs, proving the joint embedding
    property. -/)
  (title := /-- (2) $\Rightarrow$ joint embedding property -/)
  (latexEnv := "lemma")]
lemma jep_of_two (C : graph → Prop)
    (hiso : iso_closed C) (h : ∃ T : tec, csp T = sp C) : jep C := by
  rcases h with ⟨T, hT⟩
  unfold jep
  intro G H hGfin hHfin hGC hHC
  have hGsp : sp C (star G) := star_sp_of_mem C G hGfin hGC
  have hHsp : sp C (star H) := star_sp_of_mem C H hHfin hHC
  have hGcsp : csp T (star G) := by
    rw [hT]
    exact hGsp
  have hHcsp : csp T (star H) := by
    rw [hT]
    exact hHsp
  have hsumcsp : csp T (tec_sum (star G) (star H)) :=
    csp_disjoint_union T (star G) (star H) hGcsp hHcsp
  have hsumsp : sp C (tec_sum (star G) (star H)) := by
    rw [← hT]
    exact hsumcsp
  rcases hsumsp with ⟨hsumfin, E, hblue, hred, hCE⟩
  refine ⟨⟨G.V ⊕ H.V, E⟩, hsumfin, hCE, ?_, ?_⟩
  · refine ⟨⟨⟨Sum.inl, Sum.inl_injective⟩, ?_⟩⟩
    intro u v
    constructor
    · intro huvE
      by_contra hGadj
      have huv : u ≠ v := by
        intro huv
        subst v
        exact E.irrefl huvE
      exact hred _ _ huvE (by
        change G.Gᶜ.Adj u v
        exact (SimpleGraph.compl_adj G.G u v).2 ⟨huv, hGadj⟩)
    · intro hGadj
      apply hblue
      change G.G.Adj u v
      exact hGadj
  · refine ⟨⟨⟨Sum.inr, Sum.inr_injective⟩, ?_⟩⟩
    intro u v
    constructor
    · intro huvE
      by_contra hHadj
      have huv : u ≠ v := by
        intro huv
        subst v
        exact E.irrefl huvE
      exact hred _ _ huvE (by
        change H.Gᶜ.Adj u v
        exact (SimpleGraph.compl_adj H.G u v).2 ⟨huv, hHadj⟩)
    · intro hHadj
      apply hblue
      change H.G.Adj u v
      exact hHadj

@[blueprint "lem:blowup-all-finite"
  (statement := /-- Let $\mathcal C$ be isomorphism-closed and hereditary, with
    $\mathrm{CSP}(T)=\mathrm{SP}(\mathcal C)$ for some $T$. Every finite non-empty family of
    fibres over a finite $\mathbf G\in\mathcal C$ admits a designation whose split blow-up is
    in $\mathcal C$. See \cref{def:split-blow-up}. -/)
  (proof := /-- The non-empty subsingleton base case is \cref{lem:blowup-single}. Otherwise,
    use \cref{lem:ramsey} in every fibre of a sufficiently large finite coloured graph mapping
    to $T$. The sandwich solution contains homogeneous sets of the required fibre sizes.
    Their clique/independent-set alternatives define the designation, and their product is an
    induced embedding of the desired split blow-up. Heredity and isomorphism closure finish. -/)
  (title := /-- A designation for one finite family of fibres -/)
  (latexEnv := "lemma")]
lemma blowup_all_finite (C : graph → Prop)
    (hiso : iso_closed C) (hher : hereditary C) (h : ∃ T : tec, csp T = sp C)
    (G : graph) (hVfin : Finite G.V) (hG : C G) (β : G.V → Type)
    (hβfin : ∀ u, Finite (β u)) (hβne : ∀ u, Nonempty (β u)) :
    ∃ twin : G.V → Prop, C ⟨_, split_blow_up G twin β⟩ := by
  classical
  haveI : Finite G.V := hVfin
  letI : Fintype G.V := Fintype.ofFinite G.V
  letI (u : G.V) : Finite (β u) := hβfin u
  letI (u : G.V) : Fintype (β u) := Fintype.ofFinite (β u)
  by_cases hspecial : Nonempty G.V ∧ Subsingleton G.V
  · letI : Nonempty G.V := hspecial.1
    letI : Subsingleton G.V := hspecial.2
    let v : G.V := Classical.choice hspecial.1
    have hsub : ∀ u, u ≠ v → Subsingleton (β u) := by
      intro u huv
      exact (huv (Subsingleton.elim u v)).elim
    obtain ⟨isTwin, hC⟩ :=
      blowup_single C hiso hher h G hVfin hG v β (hβfin v) hsub hβne
    exact ⟨fun _ => isTwin, hC⟩
  · obtain ⟨T, hT⟩ := h
    have hGsp : sp C (star G) := by
      refine ⟨hVfin, G.G, fun _ _ h => h, ?_, hG⟩
      intro u v huv hred
      exact ((SimpleGraph.compl_adj G.G u v).1 hred).2 huv
    have hGcsp : csp T (star G) := by
      rw [hT]
      exact hGsp
    obtain ⟨g, hgred, hgblue⟩ := hGcsp.2
    choose r hr using fun u => ramsey (Fintype.card (β u))
    let A : tec :=
      { V := Σ u, Fin (r u)
        red := G.Gᶜ.comap Sigma.fst
        blue := G.G.comap Sigma.fst
        disjoint := by
          intro p q hpq
          exact ((SimpleGraph.compl_adj G.G p.1 q.1).1 hpq.1).2 hpq.2 }
    have hAfin : Finite A.V := by
      dsimp [A]
      infer_instance
    have hAcsp : csp T A := by
      refine ⟨hAfin, fun p => g p.1, ?_, ?_⟩
      · intro p q hpq
        exact hgred p.1 q.1 hpq
      · intro p q hpq
        exact hgblue p.1 q.1 hpq
    have hAsp : sp C A := by
      rw [← hT]
      exact hAcsp
    obtain ⟨_, E, hblue, hred, hCE⟩ := hAsp
    choose s hscard hs using fun u =>
      hr u (Fin (r u)) (by simp) (E.comap fun i : Fin (r u) => ⟨u, i⟩)
    let ev (u : G.V) : β u ≃ ↥(s u) :=
      Fintype.equivOfCardEq (by simpa using (hscard u).symm)
    have hchoice : ∀ u, ∃ isTwin : Prop, ∀ a b : β u,
        E.Adj ⟨u, (ev u a).1⟩ ⟨u, (ev u b).1⟩ ↔ a ≠ b ∧ ¬ isTwin := by
      intro u
      rcases hs u with hclique | hindep
      · refine ⟨False, ?_⟩
        intro a b
        constructor
        · intro hab
          exact ⟨fun heq => hab.ne (by rw [heq]), by simp⟩
        · rintro ⟨hab, _⟩
          have hev : (ev u a).1 ≠ (ev u b).1 := by
            intro heq
            apply hab
            exact (ev u).injective (Subtype.ext heq)
          simpa using hclique (ev u a).1 (ev u a).2 (ev u b).1 (ev u b).2 hev
      · refine ⟨True, ?_⟩
        intro a b
        constructor
        · intro hab
          exfalso
          by_cases heq : a = b
          · exact hab.ne (by rw [heq])
          · have hev : (ev u a).1 ≠ (ev u b).1 := by
              intro hval
              apply heq
              exact (ev u).injective (Subtype.ext hval)
            exact (hindep (ev u a).1 (ev u a).2 (ev u b).1 (ev u b).2 hev)
              (by simpa using hab)
        · rintro ⟨_, hfalse⟩
          exact False.elim (hfalse trivial)
    choose twin hmono using hchoice
    let f : (Σ u, β u) → A.V := fun p => ⟨p.1, (ev p.1 p.2).1⟩
    have hf (u : G.V) (a : β u) : f ⟨u, a⟩ = ⟨u, (ev u a).1⟩ := rfl
    have hf_fst (p : Σ u, β u) : (f p).1 = p.1 := rfl
    have hf_inj : Function.Injective f := by
      rintro ⟨u, a⟩ ⟨v, b⟩ heq
      have huv : u = v := congrArg Sigma.fst heq
      subst v
      congr 1
      apply (ev u).injective
      apply Subtype.ext
      exact eq_of_heq (Sigma.mk.inj_iff.mp heq).2
    have hcross (p q : A.V) (hpq : p.1 ≠ q.1) :
        E.Adj p q ↔ G.G.Adj p.1 q.1 := by
      constructor
      · intro hE
        by_contra hGpq
        exact hred p q hE
          ((SimpleGraph.compl_adj G.G p.1 q.1).2 ⟨hpq, hGpq⟩)
      · intro hGpq
        exact hblue p q hGpq
    let emb : split_blow_up G twin β ↪g E :=
      ⟨⟨f, hf_inj⟩, by
        rintro ⟨u, a⟩ ⟨v, b⟩
        by_cases huv : u = v
        · subst v
          change E.Adj (f ⟨u, a⟩) (f ⟨u, b⟩) ↔ _
          rw [hf, hf, hmono u]
          simp [split_blow_up]
        · change E.Adj (f ⟨u, a⟩) (f ⟨v, b⟩) ↔ _
          rw [hcross]
          · rw [hf_fst, hf_fst]
            simp [split_blow_up, huv, Ne.symm huv, SimpleGraph.adj_comm]
          · simpa only [hf_fst] using huv⟩
    have hCind : C ⟨_, E.induce (Set.range emb)⟩ :=
      hher ⟨A.V, E⟩ (Set.range emb) hAfin hCE
    exact ⟨twin, hiso _ _ ⟨emb.isoInduceRange.symm⟩ hCind⟩

@[blueprint "lem:uniform-blowup-choice"
  (statement := /-- Let $\mathcal C$ be isomorphism-closed and hereditary, and let
    $\mathbf G=(V,G)$ be a finite graph. If every finite non-empty family of fibres admits
    some successful designation, then one designation works for every such family. -/)
  (proof := /-- If no designation works uniformly, choose for each of the finitely many
    designations $d:V\to\mathrm{Prop}$ a finite non-empty counterexample $\beta_d$. Apply the
    hypothesis to $\gamma(u)=\bigsqcup_d\beta_d(u)$, obtaining a successful designation
    $d_0$. Selecting the $d_0$-summand in every fibre gives an induced embedding of the
    $\beta_{d_0}$-blow-up into the $\gamma$-blow-up. Heredity and isomorphism closure contradict
    the choice of $\beta_{d_0}$. See \cref{def:hereditary}, \cref{def:iso-closed} and
    \cref{def:split-blow-up}. -/)
  (title := /-- Uniformizing finite split-blow-up choices -/)
  (latexEnv := "lemma")]
lemma uniform_blowup_choice (C : graph → Prop)
    (hiso : iso_closed C) (hher : hereditary C) (G : graph)
    (hVfin : Finite G.V)
    (hfamily : ∀ β : G.V → Type, (∀ u, Finite (β u)) → (∀ u, Nonempty (β u)) →
      ∃ twin : G.V → Prop, C ⟨_, split_blow_up G twin β⟩) :
    ∃ twin : G.V → Prop, ∀ β : G.V → Type,
      (∀ u, Finite (β u)) → (∀ u, Nonempty (β u)) →
        C ⟨_, split_blow_up G twin β⟩ := by
  classical
  haveI : Finite G.V := hVfin
  letI : Fintype G.V := Fintype.ofFinite G.V
  by_contra hnone
  push Not at hnone
  let toTwin (d : G.V → Bool) : G.V → Prop := fun u => d u = true
  have hnoneBool : ∀ d : G.V → Bool, ∃ β : G.V → Type,
      (∀ u, Finite (β u)) ∧ (∀ u, Nonempty (β u)) ∧
        ¬ C ⟨_, split_blow_up G (toTwin d) β⟩ := by
    intro d
    exact hnone (toTwin d)
  choose β hβfin hβne hβbad using hnoneBool
  letI : Fintype (G.V → Bool) := inferInstance
  letI (d : G.V → Bool) (u : G.V) : Finite (β d u) := hβfin d u
  letI (d : G.V → Bool) (u : G.V) : Fintype (β d u) := Fintype.ofFinite (β d u)
  let γ (u : G.V) := Σ d : G.V → Bool, β d u
  letI (u : G.V) : Fintype (γ u) := by
    dsimp [γ]
    infer_instance
  have hγfin : ∀ u, Finite (γ u) := by
    intro u
    dsimp [γ]
    infer_instance
  have hγne : ∀ u, Nonempty (γ u) := by
    intro u
    let d : G.V → Bool := fun _ => true
    exact Nonempty.map (fun a => ⟨d, a⟩) (hβne d u)
  obtain ⟨twin, hCtwin⟩ := hfamily γ hγfin hγne
  let d : G.V → Bool := fun u => decide (twin u)
  have hd : toTwin d = twin := by
    funext u
    simp [toTwin, d]
  have hCtwin' : C ⟨_, split_blow_up G (toTwin d) γ⟩ := by
    simpa only [hd] using hCtwin
  let f : (Σ u, β d u) → (Σ u, γ u) :=
    fun p => ⟨p.1, ⟨d, p.2⟩⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨u, a⟩ ⟨v, b⟩ heq
    have huv : u = v := congrArg Sigma.fst heq
    subst v
    congr 1
    have hsigma : (⟨d, a⟩ : γ u) = ⟨d, b⟩ :=
      eq_of_heq (Sigma.mk.inj_iff.mp heq).2
    exact eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2
  let emb : split_blow_up G (toTwin d) (β d) ↪g
      split_blow_up G (toTwin d) γ :=
    ⟨⟨f, hf_inj⟩, by
      rintro ⟨u, a⟩ ⟨v, b⟩
      by_cases huv : u = v
      · subst v
        have hpair : (⟨d, a⟩ : γ u) = ⟨d, b⟩ ↔ a = b := by
          constructor
          · intro heq
            exact eq_of_heq (Sigma.mk.inj_iff.mp heq).2
          · intro heq
            subst b
            rfl
        simp [f, split_blow_up, hpair]
      · simp [f, split_blow_up, huv, Ne.symm huv, SimpleGraph.adj_comm]⟩
  have hbigfin : Finite (Σ u, γ u) := by
    infer_instance
  have hCind :
      C ⟨_, (split_blow_up G (toTwin d) γ).induce (Set.range emb)⟩ :=
    hher ⟨_, split_blow_up G (toTwin d) γ⟩ (Set.range emb) hbigfin hCtwin'
  have hCsmall : C ⟨_, split_blow_up G (toTwin d) (β d)⟩ :=
    hiso _ _ ⟨emb.isoInduceRange.symm⟩ hCind
  exact hβbad d hCsmall

@[blueprint "lem:preserved-of-two"
  (statement := /-- Let $\mathcal{C}$ be a class of graphs closed under isomorphism. If there is
    a $2$-edge-coloured graph $T$ with $\mathrm{CSP}(T) = \mathrm{SP}(\mathcal{C})$, then
    $\mathcal{C}$ is preserved under split blow-ups of finite members by finite non-empty
    fibres. See \cref{def:csp}, \cref{def:sp} and \cref{def:preserved-split-blow-up}. -/)
  (proof := /-- By \cref{lem:hereditary-of-two}, the class $\mathcal C$ is hereditary. Fix a
    finite $\mathbf G\in\mathcal C$. For every finite non-empty fibre family,
    \cref{lem:blowup-all-finite} supplies some successful twin/co-twin designation.
    The finite compactness argument \cref{lem:uniform-blowup-choice} then supplies one
    designation that works simultaneously for all such fibre families. This is precisely the
    property in \cref{def:preserved-split-blow-up}. -/)
  (title := /-- (2) $\Rightarrow$ preservation under split blow-ups -/)
  (latexEnv := "lemma")]
lemma preserved_of_two (C : graph → Prop)
    (hiso : iso_closed C) (h : ∃ T : tec, csp T = sp C) :
    preserved_split_blow_up C := by
  have hher : hereditary C := hereditary_of_two C hiso h
  intro G hVfin hG
  apply uniform_blowup_choice C hiso hher G hVfin
  intro β hβfin hβne
  exact blowup_all_finite C hiso hher h G hVfin hG β hβfin hβne

@[blueprint "thm:sp-csp-tfae"
  (statement := /-- Let $\mathcal{C}$ be a class of graphs closed under isomorphism. The
    following are equivalent:
    \begin{enumerate}
      \item $\mathcal{C}$ is hereditary, has the joint embedding property, and every finite
        member admits a twin/co-twin designation under which all split blow-ups by finite
        non-empty fibres remain in $\mathcal{C}$;
      \item there is a $2$-edge-coloured graph $T$ with
        $\mathrm{CSP}(T) = \mathrm{SP}(\mathcal{C})$;
      \item there is a graph $\mathbf{H}$ with
        $\mathrm{SP}(\mathcal{C}) = \mathrm{CSP}(H^{\ast}) = \mathrm{injCSP}(H^{\ast})$.
    \end{enumerate}
    See \cref{def:hereditary}, \cref{def:jep}, \cref{def:preserved-split-blow-up},
    \cref{def:csp}, \cref{def:sp}, \cref{def:inj-csp} and \cref{def:star}.

    Besides closure under isomorphism, $\mathcal{C}$ is assumed to contain at least one finite
    graph. This is the paper's standing convention for a class of graphs rather than an added
    restriction, and it is needed: for $\mathcal{C} = \varnothing$ item (1) holds vacuously while
    (2) fails, since $\mathrm{CSP}(T)$ always contains the empty instance whereas
    $\mathrm{SP}(\varnothing) = \varnothing$. Nothing is assumed about the members of
    $\mathcal{C}$ beyond that; in particular $\mathcal{C}$ may contain infinite graphs, as the
    universal graph $\mathbf{H}$ of \cref{lem:exists-universal} generally is. -/)
  (proof := /-- We prove (1) $\Rightarrow$ (3) $\Rightarrow$ (2) $\Rightarrow$ (1). The
    implication (1) $\Rightarrow$ (3) is \cref{lem:three-of-one}, and (3) $\Rightarrow$ (2) is
    \cref{lem:two-of-three}. For (2) $\Rightarrow$ (1), \cref{lem:hereditary-of-two} gives that
    $\mathcal{C}$ is hereditary, \cref{lem:jep-of-two} gives the joint embedding property, and
    \cref{lem:preserved-of-two} gives preservation under split blow-ups of finite members by
    finite non-empty fibres. Combining the three implications closes the cycle, so the three
    statements are equivalent. -/)
  (title := /-- Sandwich problems as $\mathrm{CSP}$s: the equivalence -/)
  (latexEnv := "theorem")]
theorem sp_csp_tfae (C : graph → Prop) (hiso : iso_closed C)
    (hne : ∃ G : graph, Finite G.V ∧ C G) :
    List.TFAE
      [ hereditary C ∧ jep C ∧ preserved_split_blow_up C,
        ∃ T : tec, csp T = sp C,
        ∃ H : graph, sp C = csp (star H) ∧ csp (star H) = inj_csp (star H) ] := by
  tfae_have 1 → 3 := by
    rintro ⟨hher, hjep, hpres⟩
    exact three_of_one C hiso hher hjep hpres hne
  tfae_have 3 → 2 := two_of_three C
  tfae_have 2 → 1 := by
    intro h
    exact
      ⟨hereditary_of_two C hiso h, jep_of_two C hiso h,
        preserved_of_two C hiso h⟩
  tfae_finish

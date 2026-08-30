import Architect
import Mathlib

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:concept-class"
  (statement := /-- Let $\mcX$ be a domain. A \emph{concept class} over $\mcX$ is a set of concepts,
    where a \emph{concept} is a binary labeling $c : \mcX \to \{0,1\}$ of the domain.
    Formally, a concept class over $\mcX$ is a subset of the function space $\{0,1\}^{\mcX}$. -/)
  (title := /-- Concept Class -/)
  (latexEnv := "definition")]
abbrev concept_class (X : Type*) : Type _ := Set (X → Bool)

@[blueprint "def:class-shatters"
  (statement := /-- Let $\mcC \subseteq \{0,1\}^{\mcX}$ be a concept class over a domain $\mcX$, and let
    $W \subseteq \mcX$. We say that $\mcC$ \emph{shatters} $W$ if every labeling pattern
    $p : \mcX \to \{0,1\}$ is realized on $W$ by some concept of $\mcC$; that is, for every
    $p$ there exists $c \in \mcC$ with $c(x) = p(x)$ for all $x \in W$. -/)
  (title := /-- Shattering of a Set by a Concept Class -/)
  (latexEnv := "definition")]
def class_shatters {X : Type*} (C : Set (X → Bool)) (W : Set X) : Prop :=
  ∀ p : X → Bool, ∃ c ∈ C, ∀ x ∈ W, c x = p x

@[blueprint "def:vc-dim"
  (statement := /-- The \emph{Vapnik--Chervonenkis dimension} of a concept class
    $\mcC \subseteq \{0,1\}^{\mcX}$ is the supremum of the cardinalities of the finite subsets
    $W \subseteq \mcX$ that are shattered by $\mcC$ in the sense of \cref{def:class-shatters}.
    If no finite subset is shattered, or the shattered cardinalities are unbounded, the
    convention $\sup \emptyset = 0$ (respectively the supremum of an unbounded set of naturals)
    is used. -/)
  (title := /-- Vapnik--Chervonenkis Dimension -/)
  (latexEnv := "definition")]
noncomputable def vc_dim {X : Type*} (C : Set (X → Bool)) : ℕ :=
  sSup {n : ℕ | ∃ W : Finset X, W.card = n ∧ class_shatters C (↑W)}

@[blueprint "def:restrict-class"
  (statement := /-- Let $\mcC \subseteq \{0,1\}^{\mcX}$ be a concept class, let $T \subseteq \mcX$
    be a set of domain points, and let $b : \mcX \to \{0,1\}$ be a labeling pattern. The
    \emph{restriction} $\mcC|_{T,b}$ is the subclass of concepts of $\mcC$ that agree with $b$
    on $T$, namely $\{\, c \in \mcC : c(x) = b(x) \text{ for all } x \in T \,\}$. -/)
  (title := /-- Restriction of a Concept Class to a Pattern -/)
  (latexEnv := "definition")]
def restrict_class {X : Type*} (C : Set (X → Bool)) (T : Set X) (b : X → Bool) :
    Set (X → Bool) :=
  {c | c ∈ C ∧ ∀ x ∈ T, c x = b x}

@[blueprint "def:teaching-set"
  (statement := /-- Let $\mcC \subseteq \{0,1\}^{\mcX}$ be a concept class and $c \in \mcC$ a concept.
    A set $S \subseteq \mcX$ is a \emph{teaching set} for $c$ in $\mcC$ if $c$ differs from every
    other concept of $\mcC$ on some point of $S$; that is, $c \in \mcC$ and for every
    $c' \in \mcC$ with $c' \neq c$ there exists $x \in S$ such that $c'(x) \neq c(x)$. -/)
  (title := /-- Teaching Set of a Concept -/)
  (latexEnv := "definition")]
def teaching_set {X : Type*} (C : Set (X → Bool)) (c : X → Bool) (S : Set X) : Prop :=
  c ∈ C ∧ ∀ c' ∈ C, c' ≠ c → ∃ x ∈ S, c' x ≠ c x

@[blueprint "def:tail-width"
  (statement := /-- For a greediness parameter $k$ and a level index $i$, the \emph{tail width}
    is $w_i \triangleq 2^{\log(8k)\cdot 2^{2i}}$, where $\log$ denotes the base-$2$ logarithm.
    This is the number of tail-point columns used at level $i$ of the construction. -/)
  (title := /-- Tail Width $w_i$ -/)
  (latexEnv := "definition")]
noncomputable def tail_width (k i : ℕ) : ℝ :=
  (2 : ℝ) ^ (Real.logb 2 (8 * (k : ℝ)) * (2 : ℝ) ^ (2 * i))

@[blueprint "def:greedy-run"
  (statement := /-- Fix a greediness parameter $k$. A set $S \subseteq \mcX$ is a possible output of
    $\textsc{Greedy}(\mcC, k)$ (Algorithm 1) if it arises from the following process. If
    $|\mcC| \le 1$, the process halts and returns $S = \emptyset$. Otherwise it selects a point
    set $T \subseteq \mcX$ with $1 \le |T| \le k$ and a pattern $b : \mcX \to \{0,1\}$ that
    minimize the cardinality of the nonempty restriction $\mcC|_{T,b}$ of \cref{def:restrict-class}
    over all feasible pairs, breaking ties in favor of a set $T$ of smaller size; it then adds
    the points of $T$ to the returned set and recurses on $\mcC|_{T,b}$. The set $S$ finally
    returned is a teaching set in the sense of \cref{def:teaching-set}. -/)
  (title := /-- Greedy Teaching-Set Construction (Algorithm 1) -/)
  (latexEnv := "definition")]
inductive greedy_run {X : Type*} (k : ℕ) : Set (X → Bool) → Set X → Prop
  | terminate (C : Set (X → Bool)) (h : C.Subsingleton) : greedy_run k C ∅
  | step (C : Set (X → Bool)) (T : Finset X) (b : X → Bool) (S : Set X)
      (hlow : 1 ≤ T.card) (hhigh : T.card ≤ k)
      (hne : (restrict_class C (↑T) b).Nonempty)
      (hmin : ∀ (T' : Finset X) (b' : X → Bool), 1 ≤ T'.card → T'.card ≤ k →
        (restrict_class C (↑T') b').Nonempty →
        (restrict_class C (↑T) b).ncard ≤ (restrict_class C (↑T') b').ncard)
      (htie : ∀ (T' : Finset X) (b' : X → Bool), 1 ≤ T'.card → T'.card ≤ k →
        (restrict_class C (↑T') b').Nonempty →
        (restrict_class C (↑T') b').ncard = (restrict_class C (↑T) b).ncard →
        T.card ≤ T'.card)
      (hrec : greedy_run k (restrict_class C (↑T) b) S) :
      greedy_run k C ((↑T : Set X) ∪ S)

@[blueprint "lem:vc-le-of-shatter-bound"
  (statement := /-- Let $\mcC \subseteq \{0,1\}^{\mcX}$ be a concept class and $d$ a natural number.
    If every finite subset $W \subseteq \mcX$ shattered by $\mcC$ (in the sense of
    \cref{def:class-shatters}) satisfies $|W| \le d$, then the Vapnik--Chervonenkis dimension of
    $\mcC$ (\cref{def:vc-dim}) satisfies $\mathrm{VCdim}(\mcC) \le d$. -/)
  (proof := /-- By \cref{def:vc-dim}, $\mathrm{VCdim}(\mcC)$ is the supremum of the set
    $A = \{\, n \in \mathbb{N} : \exists\, W \text{ finite}, |W| = n \text{ and } \mcC \text{ shatters } W \,\}$.
    Fix any $n \in A$ and a witnessing finite $W$ with $|W| = n$ shattered by $\mcC$; by hypothesis
    $n = |W| \le d$. Hence $d$ is an upper bound of $A$, and since a supremum of a set of naturals
    bounded above by $d$ is at most $d$, we conclude $\mathrm{VCdim}(\mcC) = \sup A \le d$. -/)
  (title := /-- VC Dimension Bounded by a Uniform Shatter Bound -/)
  (latexEnv := "lemma")]
lemma vc_le_of_shatter_bound {X : Type*} (C : Set (X → Bool)) (d : ℕ)
    (h : ∀ W : Finset X, class_shatters C (↑W) → W.card ≤ d) :
    vc_dim C ≤ d := by
  refine csSup_le' ?_
  rintro n ⟨W, rfl, hW⟩
  exact h W hW

@[blueprint "lem:width-domination"
  (statement := /-- Let $k \ge 2$ be an integer and let $i \ge 1$. With the tail width
    $w_i = 2^{\log(8k)\cdot 2^{2i}}$ of \cref{def:tail-width}, we have the domination estimate
    \[ \bigl(8k(i-1)\,w_{i-1}\bigr)^{2k} \le w_i^{\,k}. \]
    This is the arithmetic inequality justifying that level $i$ dominates all lower levels, and it
    is the reason for the choice $w_i = 2^{\log(8k)\cdot 2^{2i}}$. -/)
  (proof := /-- Write $i = m+1$ with $m \ge 0$. By \cref{def:tail-width}, since $2^{\log(8k)} = 8k$
    and $2^{2j}$ is a natural number, the tail width has the closed form
    $w_j = (8k)^{2^{2j}}$; in particular $w_{i-1} = w_m = (8k)^{2^{2m}}$ and
    $w_i = w_{m+1} = (8k)^{2^{2(m+1)}} = (8k)^{4\cdot 2^{2m}}$. We first show
    $8k\,(i-1) = 8k\,m \le (8k)^{2^{2m}} = w_{m}$. Indeed $m < 2^m \le 2^{2m}$, and combined with
    $m \le (8k)^{m}$ (from $m < 2^m \le (8k)^m$, using $8k \ge 2$) this gives
    $8k\,m \le (8k)^{m+1} \le (8k)^{2^{2m}}$, where the last inequality uses $m+1 \le 2^{2m}$ and
    $8k \ge 1$. Since $8k\,m$ and $w_m = (8k)^{2^{2m}}$ are nonnegative, multiplying the bound
    $8k\,m \le w_m$ by $w_m$ yields $8k\,m\,w_m \le w_m^{2} = (8k)^{2\cdot 2^{2m}}$. Raising this
    nonnegative inequality to the power $2k$ and regrouping exponents gives
    $\bigl(8k\,m\,w_m\bigr)^{2k} \le \bigl((8k)^{2\cdot 2^{2m}}\bigr)^{2k}
    = \bigl((8k)^{4\cdot 2^{2m}}\bigr)^{k} = w_{m+1}^{\,k} = w_i^{\,k}$, which is the claim. -/)
  (title := /-- Level-Width Domination Estimate -/)
  (latexEnv := "lemma")]
lemma width_domination (k : ℕ) (hk : 2 ≤ k) (i : ℕ) (hi : 1 ≤ i) :
    ((8 * (k : ℝ) * ((i : ℝ) - 1)) * tail_width k (i - 1)) ^ (2 * k)
      ≤ tail_width k i ^ k := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hb : (0:ℝ) ≤ 8 * (k:ℝ) := by positivity
  have hcast : ((m+1:ℕ):ℝ) - 1 = (m:ℝ) := by push_cast; ring
  have hE : tail_width k m = (8*(k:ℝ)) ^ (2^(2*m)) := by
    unfold tail_width
    rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
        Real.rpow_logb (by norm_num) (by norm_num) (by positivity),
        show ((2:ℝ)^(2*m)) = (((2^(2*m)):ℕ):ℝ) by push_cast; ring, Real.rpow_natCast]
  have hE1 : tail_width k (m+1) = (8*(k:ℝ)) ^ (2^(2*(m+1))) := by
    unfold tail_width
    rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
        Real.rpow_logb (by norm_num) (by norm_num) (by positivity),
        show ((2:ℝ)^(2*(m+1))) = (((2^(2*(m+1))):ℕ):ℝ) by push_cast; ring, Real.rpow_natCast]
  have h1 : m < 2^m := Nat.lt_two_pow_self
  have hk8 : 2 ≤ 8 * k := by omega
  have hk8' : 1 ≤ 8 * k := by omega
  have step1 : 8 * k * m ≤ (8*k)^(m+1) := by
    calc 8 * k * m ≤ 8 * k * (8*k)^m :=
          by gcongr; exact le_trans (le_of_lt h1) (Nat.pow_le_pow_left hk8 m)
      _ = (8*k)^(m+1) := by rw [pow_succ]; ring
  have hexp : m + 1 ≤ 2^(2*m) := by
    calc m + 1 ≤ 2^m := h1
      _ ≤ 2^(2*m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hkey : 8 * k * m ≤ (8*k)^(2^(2*m)) := le_trans step1 (Nat.pow_le_pow_right hk8' hexp)
  have hkeyR : 8 * (k:ℝ) * (m:ℝ) ≤ (8*(k:ℝ))^(2^(2*m)) := by exact_mod_cast hkey
  have hexp2 : 2^(2*(m+1)) = 4 * 2^(2*m) := by
    rw [show 2*(m+1) = 2*m + 2 from by ring, pow_add]; ring
  rw [hE, hE1, hcast, hexp2]
  have hprod : (8*(k:ℝ)) * (m:ℝ) * (8*(k:ℝ))^(2^(2*m)) ≤ (8*(k:ℝ))^(2*(2^(2*m))) := by
    calc (8*(k:ℝ)) * (m:ℝ) * (8*(k:ℝ))^(2^(2*m))
        ≤ (8*(k:ℝ))^(2^(2*m)) * (8*(k:ℝ))^(2^(2*m)) :=
          mul_le_mul_of_nonneg_right hkeyR (pow_nonneg hb _)
      _ = (8*(k:ℝ))^(2*(2^(2*m))) := by rw [← pow_add]; congr 1; ring
  calc ((8*(k:ℝ)) * (m:ℝ) * (8*(k:ℝ))^(2^(2*m)))^(2*k)
      ≤ ((8*(k:ℝ))^(2*(2^(2*m))))^(2*k) := pow_le_pow_left₀ (by positivity) hprod (2*k)
    _ = ((8*(k:ℝ))^(4*2^(2*m)))^k := by rw [← pow_mul, ← pow_mul]; congr 1; ring

@[blueprint "def:tail-width-nat"
  (statement := /-- For integers $k,i\geq 0$, define the integral tail width
    \[
      \widehat w_i=(8k)^{2^{2i}}.
    \]
    For $k\geq 1$ this is the integer represented by the real-valued width
    $w_i$ of \cref{def:tail-width}. -/)
  (title := /-- Integral Tail Width -/)
  (latexEnv := "definition")]
def tail_width_nat (k i : ℕ) : ℕ :=
  (8 * k) ^ (2 ^ (2 * i))

@[blueprint "def:large-k-domain"
  (statement := /-- For integers $k,N\geq 0$, the concrete large-$k$ domain is the disjoint
    union of the head points $(i,a)$, with $i\in\operatorname{Fin}(N)$ and
    $a\in\operatorname{Fin}(k)$, and the tail points $(i,r,q)$, with
    $r\in\operatorname{Fin}(2k)$ and
    $q\in\operatorname{Fin}(\widehat w_{i+1})$. -/)
  (title := /-- Concrete Multilevel Domain -/)
  (latexEnv := "definition")]
abbrev large_k_domain (k N : ℕ) : Type :=
  (Fin N × Fin k) ⊕
    (Σ i : Fin N, Fin (2 * k) × Fin (tail_width_nat k (i.1 + 1)))

@[blueprint "def:large-k-parent-column"
  (statement := /-- Let $i<j$ be levels and let $q$ be a column at level $j$. The concrete
    parent-column map sends $q$ to the index of its consecutive level-$i$ batch, namely
    $\lfloor q/(\widehat w_{j+1}/\widehat w_{i+1})\rfloor$. -/)
  (title := /-- Concrete Parent-Column Map -/)
  (latexEnv := "definition")]
def large_k_parent_column (k : ℕ) (i j : ℕ) (q : ℕ) : ℕ :=
  q / (tail_width_nat k (j + 1) / tail_width_nat k (i + 1))

@[blueprint "def:large-k-head-change-count"
  (statement := /-- For a sequence $v$ of zero-or-one-hot head vectors, encoded by
    $v_i=\bot$ for the zero vector and $v_i=a$ for the one-hot vector in column $a$, its
    change count is the number of adjacent pairs of levels on which the encodings differ. -/)
  (title := /-- Number of Head-Label Changes -/)
  (latexEnv := "definition")]
def large_k_head_change_count {k N : ℕ} (v : Fin N → Option (Fin k)) : ℕ :=
  ((Finset.univ.filter fun p : Fin N × Fin N =>
    p.1.1 + 1 = p.2.1 ∧ v p.1 ≠ v p.2)).card

@[blueprint "def:large-k-head-admissible"
  (statement := /-- A head-vector sequence is admissible for level $i$ if it is zero above
    $i$, is one-hot and hence nonzero at $i$, and changes value across at most $k$ adjacent
    pairs of levels. These are precisely the defining constraints on the source class
    $\mcA_i$. -/)
  (title := /-- Admissible Head Sequence -/)
  (latexEnv := "definition")]
def large_k_head_admissible {k N : ℕ} (i : Fin N)
    (v : Fin N → Option (Fin k)) : Prop :=
  (∀ j : Fin N, i < j → v j = none) ∧
    (v i).isSome ∧ large_k_head_change_count v ≤ k

@[blueprint "def:large-k-head-labeling"
  (statement := /-- The head labeling associated with a sequence $v$ assigns $1$ to the head
    point $(j,a)$ exactly when $v_j=a$, and assigns $0$ to every tail point. -/)
  (title := /-- Head Labeling from an Admissible Sequence -/)
  (latexEnv := "definition")]
def large_k_head_labeling {k N : ℕ} (v : Fin N → Option (Fin k)) :
    large_k_domain k N → Bool
  | Sum.inl (j, a) => decide (v j = some a)
  | Sum.inr _ => false

@[blueprint "def:large-k-head-class"
  (statement := /-- The concrete head class $\mcA_i$ consists of the Boolean labelings induced
    by all admissible level-$i$ head sequences. -/)
  (title := /-- Concrete Head Class -/)
  (latexEnv := "definition")]
def large_k_head_class (k N : ℕ) (i : Fin N) : concept_class (large_k_domain k N) :=
  {c | ∃ v : Fin N → Option (Fin k),
    large_k_head_admissible i v ∧ c = large_k_head_labeling v}

@[blueprint "def:large-k-tail-labeling"
  (statement := /-- Fix a level $i$ and, independently in each of the $2k$ rows, a prefix
    length $p_r\in\{0,\ldots,\widehat w_{i+1}\}$. The corresponding tail labeling is zero on
    head points, is the chosen prefix on level $i$, is copied to higher levels along the
    parent-column map of \cref{def:large-k-parent-column}, and is contracted to lower levels by
    conjunction over every higher-level batch with the prescribed parent. -/)
  (title := /-- Prefix Labeling Propagated Across Tail Levels -/)
  (latexEnv := "definition")]
def large_k_tail_labeling (k N : ℕ) (i : Fin N)
    (p : Fin (2 * k) → Fin (tail_width_nat k (i.1 + 1) + 1)) :
    large_k_domain k N → Bool
  | Sum.inl _ => false
  | Sum.inr ⟨j, r, q⟩ =>
      if hji : j < i then
        decide (∀ y : Fin (tail_width_nat k (i.1 + 1)),
          large_k_parent_column k j.1 i.1 y.1 = q.1 → y.1 < (p r).1)
      else if hij : i < j then
        decide (large_k_parent_column k i.1 j.1 q.1 < (p r).1)
      else decide (q.1 < (p r).1)

@[blueprint "def:large-k-tail-class"
  (statement := /-- The concrete tail class $\mcB_i$ consists of the propagated prefix
    labelings obtained by choosing one of $\widehat w_{i+1}+1$ prefixes independently in each
    of the $2k$ tail rows at level $i$. -/)
  (title := /-- Concrete Tail Class -/)
  (latexEnv := "definition")]
def large_k_tail_class (k N : ℕ) (i : Fin N) : concept_class (large_k_domain k N) :=
  {c | ∃ p : Fin (2 * k) → Fin (tail_width_nat k (i.1 + 1) + 1),
    c = large_k_tail_labeling k N i p}

@[blueprint "def:large-k-product-class"
  (statement := /-- For head and tail classes $A,B$ on the same domain, their Boolean product
    $A\otimes B$ is the class of all pointwise disjunctions $a\lor b$ with $a\in A$ and
    $b\in B$. -/)
  (title := /-- Boolean Product of Concept Classes -/)
  (latexEnv := "definition")]
def large_k_product_class {X : Type*} (A B : concept_class X) : concept_class X :=
  {c | ∃ a ∈ A, ∃ b ∈ B, ∀ x, c x = (a x || b x)}

@[blueprint "def:large-k-concrete-level-class"
  (statement := /-- The concrete level class is
    $\mcC_i=\mcA_i\otimes\mcB_i$, formed from the concrete head and tail classes. -/)
  (title := /-- Concrete Level Class -/)
  (latexEnv := "definition")]
def large_k_concrete_level_class (k N : ℕ) (i : Fin N) :
    concept_class (large_k_domain k N) :=
  large_k_product_class (large_k_head_class k N i) (large_k_tail_class k N i)

@[blueprint "def:large-k-concrete-family"
  (statement := /-- The concrete $N$-level family is
    $\mcF_N=\bigcup_{i\in\operatorname{Fin}(N)}\mcC_i$. -/)
  (title := /-- Concrete Multilevel Concept Family -/)
  (latexEnv := "definition")]
def large_k_concrete_family (k N : ℕ) : concept_class (large_k_domain k N) :=
  ⋃ i : Fin N, large_k_concrete_level_class k N i

@[blueprint "def:large-k-construction-data"
  (statement := /-- Fix integers $k,N\geq 1$. A \emph{large-$k$ construction datum} records the
    paper's $N$-level domain and concept classes. Its head point $h_{i,a}$ has level
    $i\in\{1,\ldots,N\}$ and column $a\in\{1,\ldots,k\}$; its tail point $t_{i,r,q}$ has
    row $r\in\{1,\ldots,2k\}$ and column $q\in\{1,\ldots,\widehat w_i\}$. The parent map sends
    a tail column at a higher level to the lower-level batch containing it. At every level the
    class $\mcC_i$ is the product of an independently chosen head labeling from $\mcA_i$ and
    tail labeling from $\mcB_i$, and $\mcF_N=\bigcup_i\mcC_i$. Every domain point is one of the
    displayed head or tail points. -/)
  (title := /-- Data of the Multilevel Large-$k$ Construction -/)
  (latexEnv := "definition")]
structure large_k_construction_data (k N : ℕ) where
  X : Type
  finite_X : Finite X
  head_point : Fin N → Fin k → X
  tail_point :
    (i : Fin N) → Fin (2 * k) → Fin (tail_width_nat k (i.1 + 1)) → X
  parent_column :
    ∀ (i j : Fin N), i < j →
      Fin (tail_width_nat k (j.1 + 1)) → ℕ
  head_class : Fin N → concept_class X
  tail_class : Fin N → concept_class X
  level_class : Fin N → concept_class X
  family : concept_class X
  level_product : ∀ i,
    level_class i =
      {c | ∃ a ∈ head_class i, ∃ b ∈ tail_class i, ∀ x, c x = (a x || b x)}
  family_union : family = ⋃ i, level_class i
  domain_exhaustive : ∀ x,
    (∃ (i : Fin N) (a : Fin k), x = head_point i a) ∨
      ∃ (i : Fin N) (r : Fin (2 * k))
        (q : Fin (tail_width_nat k (i.1 + 1))), x = tail_point i r q

@[blueprint "def:large-k-explicit-data"
  (statement := /-- For $k,N\geq0$, the explicit datum has domain
    \cref{def:large-k-domain}, the displayed injections of head and tail points, the consecutive
    batching map \cref{def:large-k-parent-column}, the concrete classes
    \cref{def:large-k-head-class,def:large-k-tail-class}, their levelwise Boolean products, and
    their union \cref{def:large-k-concrete-family}. -/)
  (title := /-- Explicit Multilevel Large-$k$ Datum -/)
  (latexEnv := "definition")]
noncomputable def large_k_explicit_data (k N : ℕ) : large_k_construction_data k N where
  X := large_k_domain k N
  finite_X := inferInstance
  head_point := fun i a => Sum.inl (i, a)
  tail_point := fun i r q => Sum.inr ⟨i, r, q⟩
  parent_column := fun i j _ q => large_k_parent_column k i.1 j.1 q.1
  head_class := large_k_head_class k N
  tail_class := large_k_tail_class k N
  level_class := large_k_concrete_level_class k N
  family := large_k_concrete_family k N
  level_product := fun _ => rfl
  family_union := rfl
  domain_exhaustive := fun x =>
    match x with
    | Sum.inl (i, a) => Or.inl ⟨i, a, rfl⟩
    | Sum.inr ⟨i, r, q⟩ => Or.inr ⟨i, r, q, rfl⟩

@[blueprint "def:large-k-head-domain"
  (statement := /-- The head domain of a construction datum $D$ is the set of all points
    $h_{i,a}$ over its levels and head columns. -/)
  (title := /-- Head Domain of the Construction -/)
  (latexEnv := "definition")]
def large_k_head_domain {k N : ℕ} (D : large_k_construction_data k N) : Set D.X :=
  {x | ∃ (i : Fin N) (a : Fin k), x = D.head_point i a}

@[blueprint "def:large-k-tail-domain"
  (statement := /-- The tail domain of a construction datum $D$ is the set of all points
    $t_{i,r,q}$ over its levels, rows, and tail columns. -/)
  (title := /-- Tail Domain of the Construction -/)
  (latexEnv := "definition")]
def large_k_tail_domain {k N : ℕ} (D : large_k_construction_data k N) : Set D.X :=
  {x | ∃ (i : Fin N) (r : Fin (2 * k))
    (q : Fin (tail_width_nat k (i.1 + 1))), x = D.tail_point i r q}

@[blueprint "def:large-k-lower-level-class"
  (statement := /-- For a construction datum $D$ and a level $i$, let
    $\mcF_{\leq i}=\bigcup_{j\leq i}\mcC_j$ denote the union of the level classes through $i$. -/)
  (title := /-- Union Through a Fixed Level -/)
  (latexEnv := "definition")]
def large_k_lower_level_class {k N : ℕ} (D : large_k_construction_data k N)
    (i : Fin N) : concept_class D.X :=
  ⋃ j : {j : Fin N // j ≤ i}, D.level_class j.1

@[blueprint "def:large-k-tail-consistency"
  (statement := /-- A construction datum has the \emph{tail-consistency property} if, for every
    level $i$, every set $T$ of at most $k$ tail points, and every pattern $b$ realized by some
    tail concept from a level at most $i$, at least $(\widehat w_i+1)^k$ concepts of
    $\mcB_i$ realize $b$ on $T$. -/)
  (title := /-- Tail-Consistency Property -/)
  (latexEnv := "definition")]
def large_k_tail_consistency {k N : ℕ} (D : large_k_construction_data k N) : Prop :=
  ∀ (i : Fin N) (T : Finset D.X) (b : D.X → Bool),
    T.card ≤ k →
    (↑T : Set D.X) ⊆ large_k_tail_domain D →
    (restrict_class
      (⋃ j : {j : Fin N // j ≤ i}, D.tail_class j.1) (↑T) b).Nonempty →
    (tail_width_nat k (i.1 + 1) + 1) ^ k ≤
      (restrict_class (D.tail_class i) (↑T) b).ncard

@[blueprint "def:large-k-head-consistency"
  (statement := /-- A construction datum has the \emph{head-consistency property} if every
    realizable pattern on at most $k$ head points extends to a concept of $\mcA_i$ at the top
    level under consideration, except for the deliberate pattern assigning zero to all $k$
    points of the entire head $H_i$. -/)
  (title := /-- Head-Consistency Property -/)
  (latexEnv := "definition")]
def large_k_head_consistency {k N : ℕ} (D : large_k_construction_data k N) : Prop :=
  ∀ (i : Fin N) (T : Finset D.X) (b : D.X → Bool),
    T.card ≤ k →
    (↑T : Set D.X) ⊆ large_k_head_domain D →
    (restrict_class
      (⋃ j : {j : Fin N // j ≤ i}, D.head_class j.1) (↑T) b).Nonempty →
    ¬ ((↑T : Set D.X) = Set.range (D.head_point i) ∧ ∀ x ∈ T, b x = false) →
    (restrict_class (D.head_class i) (↑T) b).Nonempty

@[blueprint "def:large-k-level-domination"
  (statement := /-- A construction datum has the \emph{level-domination property} if the union
    through every level $i$ has at most $\widehat w_i^{4k}$ concepts, while the union of the
    strictly lower levels has fewer than $(\widehat w_i+1)^k$ concepts whenever $i>1$. -/)
  (title := /-- Level-Domination Property -/)
  (latexEnv := "definition")]
def large_k_level_domination {k N : ℕ} (D : large_k_construction_data k N) : Prop :=
  ∀ i : Fin N,
    (large_k_lower_level_class D i).Finite ∧
    (large_k_lower_level_class D i).ncard ≤
      tail_width_nat k (i.1 + 1) ^ (4 * k) ∧
    (0 < i.1 →
      (⋃ j : {j : Fin N // j < i}, D.level_class j.1).ncard <
        (tail_width_nat k (i.1 + 1) + 1) ^ k)

@[blueprint "def:large-k-f-and-property"
  (statement := /-- A construction datum has the \emph{cross-level AND property} if, for every
    concept $c\in\mcF_N$, every pair of levels $i<j$, every row $r$, and every lower column $q$,
    the value $c(t_{i,r,q})$ is $1$ exactly when $c$ is $1$ on every level-$j$ tail point whose
    parent column is $q$. -/)
  (title := /-- Cross-Level AND Property -/)
  (latexEnv := "definition")]
def large_k_f_and_property {k N : ℕ} (D : large_k_construction_data k N) : Prop :=
  ∀ (c : D.X → Bool), c ∈ D.family →
    ∀ (i j : Fin N) (hij : i < j) (r : Fin (2 * k))
      (q : Fin (tail_width_nat k (i.1 + 1))),
      c (D.tail_point i r q) = true ↔
        ∀ y : Fin (tail_width_nat k (j.1 + 1)),
          D.parent_column i j hij y = q.1 → c (D.tail_point j r y) = true

@[blueprint "def:large-k-head-shatter-bound"
  (statement := /-- A construction datum has the \emph{head shatter bound} if every finite set
    shattered by $\mcF_N$ contains at most $2k+1$ head points. -/)
  (title := /-- Head Shatter-Bound Property -/)
  (latexEnv := "definition")]
def large_k_head_shatter_bound {k N : ℕ} (D : large_k_construction_data k N) : Prop :=
  ∀ W : Finset D.X, class_shatters D.family (↑W) →
    ((↑W : Set D.X) ∩ large_k_head_domain D).ncard ≤ 2 * k + 1

@[blueprint "def:large-k-tail-shatter-bound"
  (statement := /-- A construction datum has the \emph{tail shatter bound} if every finite set
    shattered by $\mcF_N$ contains at most $2k$ tail points. -/)
  (title := /-- Tail Shatter-Bound Property -/)
  (latexEnv := "definition")]
def large_k_tail_shatter_bound {k N : ℕ} (D : large_k_construction_data k N) : Prop :=
  ∀ W : Finset D.X, class_shatters D.family (↑W) →
    ((↑W : Set D.X) ∩ large_k_tail_domain D).ncard ≤ 2 * k

@[blueprint "def:large-k-construction"
  (statement := /-- A \emph{verified large-$k$ construction} is a datum equal to the explicit
    multilevel datum of \cref{def:large-k-explicit-data} and satisfying the tail- and
    head-consistency properties, level domination, the cross-level AND identity, and the two
    shattering bounds. Finiteness, cardinality estimates, and conclusions about the greedy
    algorithm are consequences proved downstream and are not fields of this invariant record. -/)
  (title := /-- Verified Large-$k$ Construction -/)
  (latexEnv := "definition")]
structure large_k_construction (k N : ℕ) where
  data : large_k_construction_data k N
  data_eq : data = large_k_explicit_data k N
  tail_consistency : large_k_tail_consistency data
  head_consistency : large_k_head_consistency data
  level_domination : large_k_level_domination data
  f_and : large_k_f_and_property data
  shatter_head : large_k_head_shatter_bound data
  shatter_tail : large_k_tail_shatter_bound data

@[blueprint "lem:tail-width-eq-nat"
  (statement := /-- For all natural numbers $k$ and $i$ with $k\geq 1$, the real tail width
    $w_i$ of \cref{def:tail-width} is the natural number $\widehat w_i$ of
    \cref{def:tail-width-nat}, viewed in $\mathbb R$. -/)
  (proof := /-- Since $2>0$, $2\neq 1$, and $k\geq 1$, one has $8k>0$. Expanding
    \cref{def:tail-width,def:tail-width-nat} and identifying natural powers with their real
    coercions, the real-power multiplication law and the identity
    $2^{\log_2(8k)}=8k$ give
    $w_i=(2^{\log_2(8k)})^{2^{2i}}=(8k)^{2^{2i}}=\widehat w_i$. -/)
  (title := /-- Agreement of the Real and Integral Widths -/)
  (latexEnv := "lemma")]
lemma tail_width_eq_nat (k i : ℕ) (hk : 1 ≤ k) :
    tail_width k i = (tail_width_nat k i : ℝ) := by
  unfold tail_width tail_width_nat
  norm_cast
  rw [Real.rpow_mul_natCast (by norm_num),
    Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
  norm_cast

@[blueprint "lem:tail-set"
  (statement := /-- Let $k,N\in\mathbb N$ satisfy $k\geq2$ and $N\geq1$. The explicit datum
    \cref{def:large-k-explicit-data} satisfies the tail-consistency property of
    \cref{def:large-k-tail-consistency}. -/)
  (proof := /-- Fix a level $i$, a set $T$ of at most $k$ tail points, and a realizable
    pattern $b$ on $T$. Each point of $T$ belongs to one of the $2k$ tail rows, so at most $k$
    rows meet $T$ and at least $k$ rows do not. On every row meeting $T$, realizability in a
    lower-level tail class ensures that the prescribed labels have the prefix and
    copy--contraction compatibility imposed by \cref{def:large-k-tail-labeling}; hence at least
    one level-$i$ prefix realizes them. On each untouched row, all
    $\widehat w_{i+1}+1$ prefix lengths are available independently. The product description in
    \cref{def:large-k-tail-class} therefore yields at least
    $(\widehat w_{i+1}+1)^k$ distinct level-$i$ tail concepts realizing $b$ on $T$. This is
    precisely the predicate \cref{def:large-k-tail-consistency}. -/)
  (title := /-- Consistency and Multiplicity of Tail Labelings -/)
  (latexEnv := "lemma")]
lemma tail_set (k N : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N) :
    large_k_tail_consistency (large_k_explicit_data k N) := by
  classical
  have hwidth_pos (a : ℕ) : 0 < tail_width_nat k a := by
    unfold tail_width_nat
    positivity
  have hwidth_dvd {a b : ℕ} (hab : a ≤ b) :
      tail_width_nat k a ∣ tail_width_nat k b := by
    unfold tail_width_nat
    apply pow_dvd_pow
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hwidth_mul {a b : ℕ} (hab : a ≤ b) :
      tail_width_nat k a * (tail_width_nat k b / tail_width_nat k a) =
        tail_width_nat k b :=
    Nat.mul_div_cancel' (hwidth_dvd hab)
  have hratio_mul {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
      (tail_width_nat k c / tail_width_nat k b) *
          (tail_width_nat k b / tail_width_nat k a) =
        tail_width_nat k c / tail_width_nat k a := by
    have heq :
        tail_width_nat k a *
            ((tail_width_nat k c / tail_width_nat k b) *
              (tail_width_nat k b / tail_width_nat k a)) =
          tail_width_nat k a * (tail_width_nat k c / tail_width_nat k a) := by
      calc
        _ = (tail_width_nat k a *
              (tail_width_nat k b / tail_width_nat k a)) *
              (tail_width_nat k c / tail_width_nat k b) := by ring
        _ = tail_width_nat k b *
              (tail_width_nat k c / tail_width_nat k b) := by
              rw [Nat.mul_div_cancel' (hwidth_dvd hab)]
        _ = tail_width_nat k c := Nat.mul_div_cancel' (hwidth_dvd hbc)
        _ = tail_width_nat k a *
              (tail_width_nat k c / tail_width_nat k a) :=
              (Nat.mul_div_cancel' (hwidth_dvd (hab.trans hbc))).symm
    exact Nat.eq_of_mul_eq_mul_left (hwidth_pos a) heq
  have hall_iff {A B z p : ℕ} (hA : 0 < A) (hB : 0 < B)
      (hdiv : A ∣ B) (hz : z < A) :
      (∀ y : Fin B, y.1 / (B / A) = z → y.1 < p) ↔
        (z + 1) * (B / A) ≤ p := by
    have hAB : A ≤ B := Nat.le_of_dvd hB hdiv
    have hR : 0 < B / A := Nat.div_pos hAB hA
    have hmul : A * (B / A) = B := Nat.mul_div_cancel' hdiv
    have hprod : 0 < (z + 1) * (B / A) := Nat.mul_pos (by omega) hR
    constructor
    · intro h
      let y0 := (z + 1) * (B / A) - 1
      have hz1 : z + 1 ≤ A := by omega
      have hm : (z + 1) * (B / A) ≤ A * (B / A) :=
        Nat.mul_le_mul_right (B / A) hz1
      have hy0 : y0 < B := by
        dsimp [y0]
        omega
      have hlo : z * (B / A) ≤ y0 := by
        dsimp [y0]
        rw [Nat.add_mul]
        omega
      have hhi : y0 < (z + 1) * (B / A) := by
        dsimp [y0]
        omega
      have hydiv : y0 / (B / A) = z := Nat.div_eq_of_lt_le hlo hhi
      have hp := h ⟨y0, hy0⟩ hydiv
      dsimp [y0] at hp
      omega
    · intro h y hy
      have hylt : y.1 < (z + 1) * (B / A) :=
        Nat.lt_mul_of_div_lt (by omega) hR
      omega
  have hlift (j i : Fin N) (hji : j ≤ i)
      (p : Fin (2 * k) → Fin (tail_width_nat k (j.1 + 1) + 1)) :
      ∃ q : Fin (2 * k) → Fin (tail_width_nat k (i.1 + 1) + 1),
        large_k_tail_labeling k N j p = large_k_tail_labeling k N i q := by
    let R := tail_width_nat k (i.1 + 1) / tail_width_nat k (j.1 + 1)
    let q : Fin (2 * k) → Fin (tail_width_nat k (i.1 + 1) + 1) := fun r =>
      ⟨(p r).1 * R, Nat.lt_succ_iff.mpr (by
        calc
          (p r).1 * R ≤ tail_width_nat k (j.1 + 1) * R :=
            Nat.mul_le_mul_right R (Nat.lt_succ_iff.mp (p r).2)
          _ = tail_width_nat k (i.1 + 1) := hwidth_mul (by omega))⟩
    refine ⟨q, ?_⟩
    rcases eq_or_lt_of_le hji with rfl | hji
    · have hwne : tail_width_nat k (j.1 + 1) ≠ 0 :=
        Nat.ne_of_gt (hwidth_pos _)
      have hq : q = p := by
        funext r
        apply Fin.ext
        simp [q, R, Nat.div_self (hwidth_pos _)]
      rw [hq]
    funext x
    rcases x with x | ⟨l, r, z⟩
    · rfl
    rcases lt_trichotomy l j with hlj | hlj | hjl
    · have hli : l < i := hlj.trans hji
      have hsource := hall_iff
        (hwidth_pos (l.1 + 1)) (hwidth_pos (j.1 + 1))
        (hwidth_dvd (by omega : l.1 + 1 ≤ j.1 + 1)) z.2
        (p := (p r).1)
      have htarget := hall_iff
        (hwidth_pos (l.1 + 1)) (hwidth_pos (i.1 + 1))
        (hwidth_dvd (by omega : l.1 + 1 ≤ i.1 + 1)) z.2
        (p := (q r).1)
      have hrat := hratio_mul
        (by omega : l.1 + 1 ≤ j.1 + 1)
        (by omega : j.1 + 1 ≤ i.1 + 1)
      have hRpos : 0 < R := Nat.div_pos
        (Nat.le_of_dvd (hwidth_pos _) (hwidth_dvd (by omega))) (hwidth_pos _)
      have hineq :
          (z.1 + 1) *
                (tail_width_nat k (j.1 + 1) / tail_width_nat k (l.1 + 1)) ≤
              (p r).1 ↔
            (z.1 + 1) *
                (tail_width_nat k (i.1 + 1) / tail_width_nat k (l.1 + 1)) ≤
              (p r).1 * R := by
        rw [← hrat]
        constructor
        · intro h
          simpa [R, mul_assoc, mul_left_comm, mul_comm] using
            Nat.mul_le_mul_right R h
        · intro h
          apply Nat.le_of_mul_le_mul_right
            (c := R) (by
              simpa [R, mul_assoc, mul_left_comm, mul_comm] using h)
            hRpos
      have hprop :
          (∀ y : Fin (tail_width_nat k (j.1 + 1)),
              large_k_parent_column k l.1 j.1 y.1 = z.1 → y.1 < (p r).1) ↔
            ∀ y : Fin (tail_width_nat k (i.1 + 1)),
              large_k_parent_column k l.1 i.1 y.1 = z.1 → y.1 < (q r).1 := by
        simpa [large_k_parent_column, q] using
          hsource.trans (hineq.trans htarget.symm)
      simp only [large_k_tail_labeling, dif_pos hlj, dif_pos hli]
      exact Bool.decide_congr hprop
    · subst l
      have hRpos : 0 < R := Nat.div_pos
        (Nat.le_of_dvd (hwidth_pos _) (hwidth_dvd (by omega))) (hwidth_pos _)
      have htarget := hall_iff
        (hwidth_pos (j.1 + 1)) (hwidth_pos (i.1 + 1))
        (hwidth_dvd (by omega : j.1 + 1 ≤ i.1 + 1)) z.2
        (p := (q r).1)
      have hineq :
          z.1 < (p r).1 ↔
            (z.1 + 1) * R ≤ (p r).1 * R := by
        constructor
        · intro h
          exact Nat.mul_le_mul_right R (by omega)
        · intro h
          have := Nat.le_of_mul_le_mul_right h hRpos
          omega
      have hprop :
          z.1 < (p r).1 ↔
            ∀ y : Fin (tail_width_nat k (i.1 + 1)),
              large_k_parent_column k j.1 i.1 y.1 = z.1 → y.1 < (q r).1 := by
        simpa [large_k_parent_column, q] using
          hineq.trans htarget.symm
      simp only [large_k_tail_labeling, dif_neg (lt_irrefl _), dif_pos hji]
      exact Bool.decide_congr hprop
    · have hjln : ¬ l < j := not_lt_of_ge hjl.le
      rcases lt_trichotomy l i with hli | hli | hil
      · have hBpos :
            0 < tail_width_nat k (l.1 + 1) /
              tail_width_nat k (j.1 + 1) :=
          Nat.div_pos
            (Nat.le_of_dvd (hwidth_pos _) (hwidth_dvd (by omega)))
            (hwidth_pos _)
        have hApos :
            0 < tail_width_nat k (i.1 + 1) /
              tail_width_nat k (l.1 + 1) :=
          Nat.div_pos
            (Nat.le_of_dvd (hwidth_pos _) (hwidth_dvd (by omega)))
            (hwidth_pos _)
        have hrat := hratio_mul
          (by omega : j.1 + 1 ≤ l.1 + 1)
          (by omega : l.1 + 1 ≤ i.1 + 1)
        have htarget := hall_iff
          (hwidth_pos (l.1 + 1)) (hwidth_pos (i.1 + 1))
          (hwidth_dvd (by omega : l.1 + 1 ≤ i.1 + 1)) z.2
          (p := (q r).1)
        have hsource :
            large_k_parent_column k j.1 l.1 z.1 < (p r).1 ↔
              z.1 + 1 ≤
                (p r).1 *
                  (tail_width_nat k (l.1 + 1) /
                    tail_width_nat k (j.1 + 1)) := by
          unfold large_k_parent_column
          rw [Nat.div_lt_iff_lt_mul hBpos]
          omega
        have hineq :
            z.1 + 1 ≤
                (p r).1 *
                  (tail_width_nat k (l.1 + 1) /
                    tail_width_nat k (j.1 + 1)) ↔
              (z.1 + 1) *
                  (tail_width_nat k (i.1 + 1) /
                    tail_width_nat k (l.1 + 1)) ≤
              (p r).1 * R := by
          dsimp [R]
          rw [← hrat]
          constructor
          · intro h
            simpa [R, mul_assoc, mul_left_comm, mul_comm] using
              Nat.mul_le_mul_right
                (tail_width_nat k (i.1 + 1) /
                  tail_width_nat k (l.1 + 1)) h
          · intro h
            apply Nat.le_of_mul_le_mul_right
              (c := tail_width_nat k (i.1 + 1) /
                tail_width_nat k (l.1 + 1))
              (by simpa [R, mul_assoc, mul_left_comm, mul_comm] using h)
              hApos
        have hprop :
            large_k_parent_column k j.1 l.1 z.1 < (p r).1 ↔
              ∀ y : Fin (tail_width_nat k (i.1 + 1)),
                large_k_parent_column k l.1 i.1 y.1 = z.1 →
                  y.1 < (q r).1 := by
          simpa [large_k_parent_column, q] using
            hsource.trans (hineq.trans htarget.symm)
        simp only [large_k_tail_labeling, dif_neg hjln, dif_pos hjl,
          dif_pos hli]
        exact Bool.decide_congr hprop
      · subst l
        have hRpos : 0 < R := Nat.div_pos
          (Nat.le_of_dvd (hwidth_pos _) (hwidth_dvd (by omega)))
          (hwidth_pos _)
        have hprop :
            large_k_parent_column k j.1 i.1 z.1 < (p r).1 ↔
              z.1 < (q r).1 := by
          unfold large_k_parent_column
          simpa [q, R] using
            (Nat.div_lt_iff_lt_mul hRpos :
              z.1 / R < (p r).1 ↔ z.1 < (p r).1 * R)
        simp only [large_k_tail_labeling, dif_neg hjln, dif_pos hjl,
          dif_neg (lt_irrefl _)]
        exact Bool.decide_congr hprop
      · have hiln : ¬ l < i := not_lt_of_ge hil.le
        have hApos :
            0 < tail_width_nat k (l.1 + 1) /
              tail_width_nat k (i.1 + 1) :=
          Nat.div_pos
            (Nat.le_of_dvd (hwidth_pos _) (hwidth_dvd (by omega)))
            (hwidth_pos _)
        have hRpos : 0 < R := Nat.div_pos
          (Nat.le_of_dvd (hwidth_pos _) (hwidth_dvd (by omega)))
          (hwidth_pos _)
        have hBpos :
            0 < tail_width_nat k (l.1 + 1) /
              tail_width_nat k (j.1 + 1) :=
          Nat.div_pos
            (Nat.le_of_dvd (hwidth_pos _) (hwidth_dvd (by omega)))
            (hwidth_pos _)
        have hrat := hratio_mul
          (by omega : j.1 + 1 ≤ i.1 + 1)
          (by omega : i.1 + 1 ≤ l.1 + 1)
        have hsource :
            large_k_parent_column k j.1 l.1 z.1 < (p r).1 ↔
              z.1 <
                (p r).1 *
                  (tail_width_nat k (l.1 + 1) /
                    tail_width_nat k (j.1 + 1)) := by
          unfold large_k_parent_column
          exact Nat.div_lt_iff_lt_mul hBpos
        have htarget :
            large_k_parent_column k i.1 l.1 z.1 < (q r).1 ↔
              z.1 <
                (p r).1 * R *
                  (tail_width_nat k (l.1 + 1) /
                    tail_width_nat k (i.1 + 1)) := by
          unfold large_k_parent_column
          simpa [q] using
            (Nat.div_lt_iff_lt_mul hApos :
              z.1 /
                    (tail_width_nat k (l.1 + 1) /
                      tail_width_nat k (i.1 + 1)) <
                  (p r).1 * R ↔
                z.1 <
                  (p r).1 * R *
                    (tail_width_nat k (l.1 + 1) /
                      tail_width_nat k (i.1 + 1)))
        have hbounds :
            (p r).1 *
                (tail_width_nat k (l.1 + 1) /
                  tail_width_nat k (j.1 + 1)) =
              (p r).1 * R *
                (tail_width_nat k (l.1 + 1) /
                  tail_width_nat k (i.1 + 1)) := by
          rw [← hrat]
          simp [R, mul_assoc, mul_left_comm, mul_comm]
        have hprop :
            large_k_parent_column k j.1 l.1 z.1 < (p r).1 ↔
              large_k_parent_column k i.1 l.1 z.1 < (q r).1 := by
          rw [hsource, htarget, hbounds]
        simp only [large_k_tail_labeling, dif_neg hjln, dif_pos hjl,
          dif_neg hiln, dif_pos hil]
        exact Bool.decide_congr hprop
  have hlabel_injective (i : Fin N) :
      Function.Injective (large_k_tail_labeling k N i) := by
    intro p q hpq
    funext r
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · let z : Fin (tail_width_nat k (i.1 + 1)) :=
        ⟨(p r).1, lt_of_lt_of_le hlt (Nat.lt_succ_iff.mp (q r).2)⟩
      have heq := congrFun hpq (Sum.inr ⟨i, r, z⟩)
      simp [large_k_tail_labeling, z, hlt] at heq
    · let z : Fin (tail_width_nat k (i.1 + 1)) :=
        ⟨(q r).1, lt_of_lt_of_le hgt (Nat.lt_succ_iff.mp (p r).2)⟩
      have heq := congrFun hpq (Sum.inr ⟨i, r, z⟩)
      simp [large_k_tail_labeling, z, hgt] at heq
  unfold large_k_tail_consistency
  intro i T b hTk hTtail hreal
  rcases hreal with ⟨c, hc, hcb⟩
  rw [Set.mem_iUnion] at hc
  rcases hc with ⟨j, hc⟩
  change c ∈ large_k_tail_class k N j.1 at hc
  rcases hc with ⟨p, rfl⟩
  rcases hlift j.1 i j.2 p with ⟨q, hq⟩
  have hqb : ∀ x ∈ T,
      large_k_tail_labeling k N i q x = b x := by
    simpa [← hq] using hcb
  let row : large_k_domain k N → Fin (2 * k) := fun x =>
    match x with
    | Sum.inl _ => ⟨0, by omega⟩
    | Sum.inr ⟨_, r, _⟩ => r
  let U : Finset (Fin (2 * k)) := T.image row
  have hU : U.card ≤ k := by
    exact (Finset.card_image_le.trans hTk)
  have hcomp : k ≤ Uᶜ.card := by
    rw [Finset.card_compl]
    simp only [Fintype.card_fin]
    omega
  rcases Function.Embedding.exists_of_card_le_finset
      (α := Fin k) (β := Fin (2 * k)) (s := Uᶜ) (by simpa using hcomp) with
    ⟨e, he⟩
  let varied
      (s : Fin k → Fin (tail_width_nat k (i.1 + 1) + 1))
      (r : Fin (2 * k)) : Fin (tail_width_nat k (i.1 + 1) + 1) :=
    if hr : r ∈ Set.range e then s (Classical.choose hr) else q r
  have hvaried_e
      (s : Fin k → Fin (tail_width_nat k (i.1 + 1) + 1)) (a : Fin k) :
      varied s (e a) = s a := by
    let hr : e a ∈ Set.range e := ⟨a, rfl⟩
    rw [show varied s (e a) = s (Classical.choose hr) by
      simp only [varied, dif_pos hr]]
    apply congrArg s
    apply e.injective
    exact Classical.choose_spec hr
  have hvaried_q
      (s : Fin k → Fin (tail_width_nat k (i.1 + 1) + 1))
      (r : Fin (2 * k)) (hr : r ∈ U) :
      varied s r = q r := by
    have hnrange : r ∉ Set.range e := by
      intro hre
      have hcompl := he hre
      simp only [Finset.coe_compl, Set.mem_compl_iff] at hcompl
      exact hcompl hr
    unfold varied
    rw [dif_neg hnrange]
  let f :
      (Fin k → Fin (tail_width_nat k (i.1 + 1) + 1)) →
        (large_k_domain k N → Bool) :=
    fun s => large_k_tail_labeling k N i (varied s)
  have hf_inj : Function.Injective f := by
    intro s t hst
    have hpref : varied s = varied t := hlabel_injective i hst
    funext a
    have ha := congrFun hpref (e a)
    rw [hvaried_e s a, hvaried_e t a] at ha
    exact ha
  have hfrange :
      Set.range f ⊆
        restrict_class ((large_k_explicit_data k N).tail_class i)
          (↑T : Set (large_k_explicit_data k N).X) b := by
    rintro c ⟨s, rfl⟩
    constructor
    · change f s ∈ large_k_tail_class k N i
      exact ⟨varied s, rfl⟩
    · intro x hx
      rw [← hqb x hx]
      rcases x with x | ⟨l, r, z⟩
      · rfl
      · have hrU : r ∈ U := by
          apply Finset.mem_image.mpr
          exact ⟨Sum.inr ⟨l, r, z⟩, hx, rfl⟩
        have hvr := hvaried_q s r hrU
        simp only [f, large_k_tail_labeling]
        rw [hvr]
  calc
    (tail_width_nat k (i.1 + 1) + 1) ^ k =
        Nat.card
          (Fin k → Fin (tail_width_nat k (i.1 + 1) + 1)) := by simp
    _ = (Set.range f).ncard := (Set.ncard_range_of_injective hf_inj).symm
    _ ≤ (restrict_class
        ((large_k_explicit_data k N).tail_class i) (↑T) b).ncard :=
      Set.ncard_le_ncard hfrange

@[blueprint "lem:head-change-count-le-of-sources"
  (statement := /-- Let (v) be a sequence of zero-or-one-hot head vectors, and let (S) be
    a finite set of levels containing the lower endpoint of every adjacent pair on which
    (v) changes. Then the number of changes of (v) is at most (|S|). -/)
  (proof := /-- Project every changing adjacent pair to its lower endpoint. This projection is
    injective because an adjacent pair is uniquely determined by its lower endpoint, and its
    image is contained in (S) by hypothesis. The cardinality bound follows from
    cref{def:large-k-head-change-count}. -/)
  (title := /-- Bounding Changes by Their Source Levels -/)
  (latexEnv := "lemma")]
lemma head_change_count_le_of_sources {k N : ℕ} (v : Fin N → Option (Fin k))
    (S : Finset (Fin N))
    (hS : ∀ p q : Fin N, p.1 + 1 = q.1 → v p ≠ v q → p ∈ S) :
    large_k_head_change_count v ≤ S.card := by
  classical
  unfold large_k_head_change_count
  let E := Finset.univ.filter fun p : Fin N × Fin N =>
    p.1.1 + 1 = p.2.1 ∧ v p.1 ≠ v p.2
  change E.card ≤ S.card
  calc
    E.card = (E.image Prod.fst).card := by
      symm
      apply Finset.card_image_iff.mpr
      intro p hp q hq hpq
      change p ∈ E at hp
      change q ∈ E at hq
      have hpqv : p.1.1 = q.1.1 := congrArg Fin.val hpq
      apply Prod.ext hpq
      apply Fin.ext
      simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
      omega
    _ ≤ S.card := by
      apply Finset.card_le_card
      intro p hp
      simp only [Finset.mem_image] at hp
      rcases hp with ⟨q, hq, rfl⟩
      simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      exact hS q.1 q.2 hq.1 hq.2

@[blueprint "lem:head-set"
  (statement := /-- Let $k,N\in\mathbb N$ satisfy $k\geq2$ and $N\geq1$. The explicit datum
    \cref{def:large-k-explicit-data} satisfies the head-consistency property of
    \cref{def:large-k-head-consistency}. -/)
  (proof := /-- Fix a level $i$, at most $k$ head points, and a realizable pattern on them,
    excluding the all-zero pattern on the whole head $H_i$. Points above $H_i$ necessarily
    receive label zero. If the selected set is an entire head $H_j$, its realizable pattern is
    zero or one-hot; in the latter case repeat that one-hot vector through level $i$, while in
    the former case $j<i$ and one may choose an arbitrary one-hot vector on $H_i$. This uses at
    most one change. Otherwise fewer than $k$ points are selected from every head. At each head
    meeting the selected set, choose the forced one-hot vector when a selected point has label
    one, and otherwise choose a one-hot coordinate outside the selected set. There are at most
    $k$ such heads. Extending each chosen vector constantly across the intervening consecutive
    levels produces a sequence with at most $k$ changes, zero above $i$, and nonzero at $i$.
    In every case, \cref{lem:head-change-count-le-of-sources} bounds the change count by the
    cardinality of the indicated transition-source set. By
    \cref{def:large-k-head-admissible,def:large-k-head-class}, the resulting sequence defines a member of
    $\mcA_i$ realizing the prescribed pattern, proving
    \cref{def:large-k-head-consistency}. -/)
  (title := /-- Extension of Realizable Head Labelings -/)
  (latexEnv := "lemma")]
lemma head_set (k N : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N) :
    large_k_head_consistency (large_k_explicit_data k N) := by
  classical
  unfold large_k_head_consistency
  dsimp only [large_k_explicit_data]
  intro i T b hcard hhead hreal hexception
  rcases hreal with ⟨c, hc, hcT⟩
  rcases Set.mem_iUnion.mp hc with ⟨j, hj⟩
  rcases hj with ⟨v, hv, rfl⟩
  have hhead' : ∀ x ∈ T, ∃ l : Fin N, ∃ a : Fin k, x = Sum.inl (l, a) := by
    intro x hx
    have hx' := hhead (show x ∈ (↑T : Set (large_k_domain k N)) from hx)
    change ∃ l : Fin N, ∃ a : Fin k, x = Sum.inl (l, a) at hx'
    exact hx'
  by_cases hfull : ∃ l : Fin N, ∀ a : Fin k, Sum.inl (l, a) ∈ T
  · rcases hfull with ⟨l, hl⟩
    let H : Finset (large_k_domain k N) :=
      Finset.univ.image fun a : Fin k => Sum.inl (l, a)
    have hHcard : H.card = k := by
      rw [Finset.card_image_of_injective]
      · simp
      · intro a₁ a₂ ha
        exact congrArg Prod.snd (Sum.inl.inj ha)
    have hHT : H ⊆ T := by
      intro x hx
      simp only [H, Finset.mem_image] at hx
      rcases hx with ⟨a, -, rfl⟩
      exact hl a
    have hEq : H = T := Finset.eq_of_subset_of_card_le hHT (by omega)
    subst T
    by_cases hvl : (v l).isSome
    · rcases Option.isSome_iff_exists.mp hvl with ⟨a, hva⟩
      have hlj : l ≤ j.1 := by
        by_contra h
        have hvnone := hv.1 l (by omega)
        rw [hva] at hvnone
        contradiction
      have hli : l ≤ i := hlj.trans j.2
      let w : Fin N → Option (Fin k) := fun x => if x ≤ i then some a else none
      have hwchange : large_k_head_change_count w ≤ k := by
        calc
          large_k_head_change_count w ≤ ({i} : Finset (Fin N)).card := by
            apply head_change_count_le_of_sources
            intro p q hpq hpqv
            simp only [Finset.mem_singleton]
            apply Fin.ext
            by_contra hpi
            have hsides : (p ≤ i ∧ q ≤ i) ∨ (i < p ∧ i < q) := by omega
            rcases hsides with hsides | hsides
            · simp [w, hsides.1, hsides.2] at hpqv
            · simp [w, not_le_of_gt hsides.1, not_le_of_gt hsides.2] at hpqv
          _ ≤ k := by simp; omega
      refine ⟨large_k_head_labeling w, ?_, ?_⟩
      · exact ⟨w, ⟨by
            intro q hiq
            simp [w, not_le_of_gt hiq], by simp [w], hwchange⟩, rfl⟩
      · intro x hx
        change x ∈ H at hx
        simp only [H, Finset.mem_image] at hx
        rcases hx with ⟨a', -, rfl⟩
        calc
          large_k_head_labeling w (Sum.inl (l, a')) =
              large_k_head_labeling v (Sum.inl (l, a')) := by
                simp [large_k_head_labeling, w, hli, hva]
          _ = b (Sum.inl (l, a')) := hcT _ (by
                show Sum.inl (l, a') ∈ (↑H : Set (large_k_domain k N))
                exact hl a')
    · have hvl' : v l = none := by simpa using hvl
      have hli_ne : l ≠ i := by
        intro hli
        apply hexception
        constructor
        · subst l
          ext x
          constructor
          · intro hx
            change x ∈ H at hx
            simp only [H, Finset.mem_image] at hx
            rcases hx with ⟨a, -, rfl⟩
            exact ⟨a, rfl⟩
          · rintro ⟨a, rfl⟩
            exact hl a
        · intro x hx
          change x ∈ H at hx
          simp only [H, Finset.mem_image] at hx
          rcases hx with ⟨a, -, rfl⟩
          rw [← hcT (Sum.inl (l, a)) (show Sum.inl (l, a) ∈
            (↑H : Set (large_k_domain k N)) from hl a)]
          simp [large_k_head_labeling, hvl']
      let a₀ : Fin k := ⟨0, by omega⟩
      rcases lt_or_gt_of_ne hli_ne with hli | hil
      · let w : Fin N → Option (Fin k) := fun x =>
          if x ≤ l then none else if x ≤ i then some a₀ else none
        have hwchange : large_k_head_change_count w ≤ k := by
          calc
            large_k_head_change_count w ≤ ({l, i} : Finset (Fin N)).card := by
              apply head_change_count_le_of_sources
              intro p q hpq hpqv
              simp only [Finset.mem_insert, Finset.mem_singleton]
              by_contra hs
              simp only [not_or] at hs
              have hsides : (p ≤ l ∧ q ≤ l) ∨
                  (l < p ∧ q ≤ i) ∨ (i < p ∧ i < q) := by omega
              rcases hsides with hsides | hsides | hsides
              · simp [w, hsides.1, hsides.2] at hpqv
              · have hpi : p ≤ i := by omega
                have hql : ¬q ≤ l := by omega
                simp [w, not_le_of_gt hsides.1, hpi, hql, hsides.2] at hpqv
              · simp [w, not_le_of_gt (hli.trans hsides.1),
                  not_le_of_gt hsides.1, not_le_of_gt hsides.2] at hpqv
            _ ≤ k := by simp [hli_ne]; omega
        refine ⟨large_k_head_labeling w, ?_, ?_⟩
        · exact ⟨w, ⟨by
              intro q hiq
              simp [w, not_le_of_gt (hli.trans hiq),
                not_le_of_gt hiq], by simp [w, hli], hwchange⟩, rfl⟩
        · intro x hx
          change x ∈ H at hx
          simp only [H, Finset.mem_image] at hx
          rcases hx with ⟨a, -, rfl⟩
          calc
            large_k_head_labeling w (Sum.inl (l, a)) =
                large_k_head_labeling v (Sum.inl (l, a)) := by
                  simp [large_k_head_labeling, w, hvl']
            _ = b (Sum.inl (l, a)) := hcT _ (by
                  show Sum.inl (l, a) ∈ (↑H : Set (large_k_domain k N))
                  exact hl a)
      · let w : Fin N → Option (Fin k) := fun x =>
          if x ≤ i then some a₀ else none
        have hwchange : large_k_head_change_count w ≤ k := by
          calc
            large_k_head_change_count w ≤ ({i} : Finset (Fin N)).card := by
              apply head_change_count_le_of_sources
              intro p q hpq hpqv
              simp only [Finset.mem_singleton]
              apply Fin.ext
              by_contra hpi
              have hsides : (p ≤ i ∧ q ≤ i) ∨ (i < p ∧ i < q) := by omega
              rcases hsides with hsides | hsides
              · simp [w, hsides.1, hsides.2] at hpqv
              · simp [w, not_le_of_gt hsides.1, not_le_of_gt hsides.2] at hpqv
            _ ≤ k := by simp; omega
        refine ⟨large_k_head_labeling w, ?_, ?_⟩
        · exact ⟨w, ⟨by
              intro q hiq
              simp [w, not_le_of_gt hiq], by simp [w], hwchange⟩, rfl⟩
        · intro x hx
          change x ∈ H at hx
          simp only [H, Finset.mem_image] at hx
          rcases hx with ⟨a, -, rfl⟩
          calc
            large_k_head_labeling w (Sum.inl (l, a)) =
                large_k_head_labeling v (Sum.inl (l, a)) := by
                  simp [large_k_head_labeling, w, hvl',
                    not_le_of_gt hil]
            _ = b (Sum.inl (l, a)) := hcT _ (by
                  show Sum.inl (l, a) ∈ (↑H : Set (large_k_domain k N))
                  exact hl a)
  · have hmissing : ∀ l : Fin N, ∃ a : Fin k, Sum.inl (l, a) ∉ T := by
      intro l
      by_contra hm
      apply hfull
      refine ⟨l, ?_⟩
      intro a
      by_contra ha
      exact hm ⟨a, ha⟩
    let a₀ : Fin k := ⟨0, by omega⟩
    let pick : Fin N → Fin k := fun l =>
      if h : ∃ a : Fin k, Sum.inl (l, a) ∈ T then Classical.choose h else a₀
    let L : Finset (Fin N) := Finset.univ.filter fun l =>
      l ≤ i ∧ ∃ a : Fin k, Sum.inl (l, a) ∈ T
    have hpick : ∀ l ∈ L, Sum.inl (l, pick l) ∈ T := by
      intro l hl
      have hex : ∃ a : Fin k, Sum.inl (l, a) ∈ T := (Finset.mem_filter.mp hl).2.2
      simp only [pick, dif_pos hex]
      exact Classical.choose_spec hex
    have hLcard : L.card ≤ T.card := by
      apply Finset.card_le_card_of_injOn (fun l : Fin N => Sum.inl (l, pick l))
      · intro l hl
        exact hpick l hl
      · intro l hl m hm heq
        exact congrArg Prod.fst (Sum.inl.inj heq)
    by_cases hL : L.Nonempty
    · let miss : Fin N → Fin k := fun l => Classical.choose (hmissing l)
      have hmiss : ∀ l : Fin N, Sum.inl (l, miss l) ∉ T := by
        intro l
        exact Classical.choose_spec (hmissing l)
      let chosen : Fin N → Fin k := fun l =>
        match v l with
        | some a => a
        | none => miss l
      let top : Fin N := L.max' hL
      have htop : top ∈ L := by
        exact Finset.max'_mem L hL
      let anchor : Fin N → Fin N := fun x =>
        if h : (L.filter fun l => x ≤ l).Nonempty then
          (L.filter fun l => x ≤ l).min' h
        else top
      have hanchor_mem : ∀ x : Fin N, anchor x ∈ L := by
        intro x
        simp only [anchor]
        split
        · exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).1
        · exact htop
      have hanchor_eq_of_mem : ∀ x ∈ L, anchor x = x := by
        intro x hx
        have hn : (L.filter fun l => x ≤ l).Nonempty := by
          exact ⟨x, Finset.mem_filter.mpr ⟨hx, le_rfl⟩⟩
        simp only [anchor, dif_pos hn]
        apply le_antisymm
        · exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hx, le_rfl⟩)
        · exact (Finset.mem_filter.mp (Finset.min'_mem _ hn)).2
      have hanchor_after_top : ∀ x : Fin N, top < x → anchor x = top := by
        intro x htx
        have he : L.filter (fun l => x ≤ l) = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          rintro ⟨l, hl⟩
          have hl' := Finset.mem_filter.mp hl
          have hlt : l ≤ top := Finset.le_max' L l hl'.1
          omega
        simp [anchor, he]
      have hanchor_adj : ∀ p q : Fin N, p.1 + 1 = q.1 →
          p ∉ L.erase top → anchor p = anchor q := by
        intro p q hpq hp
        by_cases hpL : p ∈ L
        · have hpt : p = top := by
            by_contra hne
            exact hp (Finset.mem_erase.mpr ⟨hne, hpL⟩)
          subst p
          rw [hanchor_eq_of_mem top htop]
          exact (hanchor_after_top q (by omega)).symm
        · have hef : L.filter (fun l => p ≤ l) = L.filter (fun l => q ≤ l) := by
            ext l
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hl, hpl⟩
              have hne : p ≠ l := by
                intro h
                apply hpL
                simpa [h] using hl
              exact ⟨hl, by omega⟩
            · rintro ⟨hl, hql⟩
              exact ⟨hl, by omega⟩
          simp [anchor, hef]
      let S : Finset (Fin N) := insert i (L.erase top)
      have hScard : S.card ≤ L.card := by
        by_cases hiL : i ∈ L
        · apply Finset.card_le_card
          intro x hx
          simp only [S, Finset.mem_insert, Finset.mem_erase] at hx
          rcases hx with rfl | hx
          · exact hiL
          · exact hx.2
        · have hiE : i ∉ L.erase top := by
            intro hi
            exact hiL (Finset.mem_of_mem_erase hi)
          simpa [S, hiE, Finset.card_erase_of_mem htop] using hL
      let w : Fin N → Option (Fin k) := fun x =>
        if x ≤ i then some (chosen (anchor x)) else none
      have hwchange : large_k_head_change_count w ≤ k := by
        calc
          large_k_head_change_count w ≤ S.card := by
            apply head_change_count_le_of_sources
            intro p q hpq hpqv
            by_contra hpS
            have hpi : p ≠ i := by
              intro h
              apply hpS
              simp [S, h]
            have hpE : p ∉ L.erase top := by
              intro hp
              apply hpS
              simp [S, hp]
            have ha := hanchor_adj p q hpq hpE
            have hsides : (p ≤ i ∧ q ≤ i) ∨ (i < p ∧ i < q) := by omega
            rcases hsides with hsides | hsides
            · simp [w, hsides.1, hsides.2, ha] at hpqv
            · simp [w, not_le_of_gt hsides.1,
                not_le_of_gt hsides.2] at hpqv
          _ ≤ L.card := hScard
          _ ≤ T.card := hLcard
          _ ≤ k := hcard
      refine ⟨large_k_head_labeling w, ?_, ?_⟩
      · exact ⟨w, ⟨by
            intro q hiq
            simp [w, not_le_of_gt hiq], by simp [w], hwchange⟩, rfl⟩
      · intro x hx
        change x ∈ T at hx
        rcases hhead' x hx with ⟨l, a, rfl⟩
        calc
          large_k_head_labeling w (Sum.inl (l, a)) =
              large_k_head_labeling v (Sum.inl (l, a)) := by
                by_cases hli : l ≤ i
                · have hlL : l ∈ L := by
                    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
                    exact ⟨hli, ⟨a, hx⟩⟩
                  have hal := hanchor_eq_of_mem l hlL
                  cases hvl : v l with
                  | none =>
                      have hne : miss l ≠ a := by
                        intro h
                        apply hmiss l
                        simpa [h] using hx
                      simp [large_k_head_labeling, w, hli, hal, chosen, hvl, hne]
                  | some z =>
                      simp [large_k_head_labeling, w, hli, hal, chosen, hvl]
                · have hil : i < l := by omega
                  have hjl : j.1 < l := j.2.trans_lt hil
                  have hvl := hv.1 l hjl
                  simp [large_k_head_labeling, w, not_le_of_gt hil, hvl]
          _ = b (Sum.inl (l, a)) := hcT _ hx
    · have hLempty : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hL
      let w : Fin N → Option (Fin k) := fun x =>
        if x ≤ i then some a₀ else none
      have hwchange : large_k_head_change_count w ≤ k := by
        calc
          large_k_head_change_count w ≤ ({i} : Finset (Fin N)).card := by
            apply head_change_count_le_of_sources
            intro p q hpq hpqv
            simp only [Finset.mem_singleton]
            apply Fin.ext
            by_contra hpi
            have hsides : (p ≤ i ∧ q ≤ i) ∨ (i < p ∧ i < q) := by omega
            rcases hsides with hsides | hsides
            · simp [w, hsides.1, hsides.2] at hpqv
            · simp [w, not_le_of_gt hsides.1, not_le_of_gt hsides.2] at hpqv
          _ ≤ k := by simp; omega
      refine ⟨large_k_head_labeling w, ?_, ?_⟩
      · exact ⟨w, ⟨by
            intro q hiq
            simp [w, not_le_of_gt hiq], by simp [w], hwchange⟩, rfl⟩
      · intro x hx
        change x ∈ T at hx
        rcases hhead' x hx with ⟨l, a, rfl⟩
        have hil : i < l := by
          by_contra hli
          have : l ∈ L := by
            simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨by omega, ⟨a, hx⟩⟩
          rw [hLempty] at this
          simp at this
        have hjl : j.1 < l := j.2.trans_lt hil
        have hvl := hv.1 l hjl
        calc
          large_k_head_labeling w (Sum.inl (l, a)) =
              large_k_head_labeling v (Sum.inl (l, a)) := by
                simp [large_k_head_labeling, w, not_le_of_gt hil, hvl]
          _ = b (Sum.inl (l, a)) := hcT _ hx

@[blueprint "lem:domination-general-case-level-card"
  (statement := /-- Let $k,N\in\mathbb N$, and let $j\in\operatorname{Fin}(N)$. The explicit
    level class $\mcC_j$ is finite, and
    \[
      |\mcC_j|\leq (k+1)^{j+1}(\widehat w_{j+1}+1)^{2k}.
    \] -/)
  (proof := /-- By \cref{def:large-k-head-admissible}, an admissible head sequence at level
    $j$ vanishes above $j$ and is therefore determined by its first $j+1$ values, giving at
    most $(k+1)^{j+1}$ possibilities. By \cref{def:large-k-tail-class}, a tail labeling is
    specified by $2k$ independent prefix lengths in
    $\{0,\ldots,\widehat w_{j+1}\}$. The product representation in
    \cref{def:large-k-concrete-level-class} is consequently the image of a finite parameter
    space of cardinality $(k+1)^{j+1}(\widehat w_{j+1}+1)^{2k}$, proving both assertions. -/)
  (title := /-- Cardinality of One Explicit Level Class -/)
  (latexEnv := "lemma")]
lemma domination_general_case_level_card (k N : ℕ) (j : Fin N) :
    (large_k_concrete_level_class k N j).Finite ∧
      (large_k_concrete_level_class k N j).ncard ≤
        (k + 1) ^ (j.1 + 1) * (tail_width_nat k (j.1 + 1) + 1) ^ (2 * k) := by
  classical
  let P :=
    (Fin (j.1 + 1) → Option (Fin k)) ×
      (Fin (2 * k) → Fin (tail_width_nat k (j.1 + 1) + 1))
  let extend : (Fin (j.1 + 1) → Option (Fin k)) → Fin N → Option (Fin k) :=
    fun u l => if h : l.1 ≤ j.1 then u ⟨l.1, Nat.lt_succ_iff.mpr h⟩ else none
  let gen : P → large_k_domain k N → Bool :=
    fun z x => large_k_head_labeling (extend z.1) x ||
      large_k_tail_labeling k N j z.2 x
  have hsub : large_k_concrete_level_class k N j ⊆ Set.range gen := by
    intro c hc
    rcases hc with ⟨a, ⟨v, hv, rfl⟩, b, ⟨p, rfl⟩, hc⟩
    let u : Fin (j.1 + 1) → Option (Fin k) := fun l => v ⟨l.1, lt_of_lt_of_le l.2 j.2⟩
    have hext : extend u = v := by
      funext l
      by_cases hlj : l.1 ≤ j.1
      · dsimp [extend]
        rw [dif_pos hlj]
      · have hvnone : v l = none := hv.1 l (show j < l from Nat.lt_of_not_ge hlj)
        dsimp [extend]
        rw [dif_neg hlj]
        exact hvnone.symm
    refine ⟨(u, p), funext fun x => ?_⟩
    rw [hc x]
    simp [gen, hext]
  have hrange : (Set.range gen).Finite := Set.finite_range gen
  refine ⟨hrange.subset hsub, le_trans (Set.ncard_le_ncard hsub hrange) ?_⟩
  rw [← Set.image_univ]
  calc
    (gen '' Set.univ).ncard ≤ (Set.univ : Set P).ncard := Set.ncard_image_le
    _ = (k + 1) ^ (j.1 + 1) *
        (tail_width_nat k (j.1 + 1) + 1) ^ (2 * k) := by
      simp [P]

@[blueprint "lem:domination-general-case-lower-card"
  (statement := /-- Let $k,N\in\mathbb N$ with $k\geq1$, and let
    $i\in\operatorname{Fin}(N)$. The union of the explicit level classes through $i$ is
    finite, and its cardinality is at most
    \[
      (i+1)(k+1)^{i+1}(\widehat w_{i+1}+1)^{2k}.
    \] -/)
  (proof := /-- Apply \cref{lem:domination-general-case-level-card} to every $j\leq i$ and
    use subadditivity of cardinality for finite unions. Both $(k+1)^{j+1}$ and
    $(\widehat w_{j+1}+1)^{2k}$ are nondecreasing in $j$, so each of the $i+1$ summands is at
    most $(k+1)^{i+1}(\widehat w_{i+1}+1)^{2k}$. -/)
  (title := /-- Coarse Cardinality Bound Through One Level -/)
  (latexEnv := "lemma")]
lemma domination_general_case_lower_card (k N : ℕ) (hk : 1 ≤ k) (i : Fin N) :
    (large_k_lower_level_class (large_k_explicit_data k N) i).Finite ∧
      (large_k_lower_level_class (large_k_explicit_data k N) i).ncard ≤
        (i.1 + 1) * (k + 1) ^ (i.1 + 1) *
          (tail_width_nat k (i.1 + 1) + 1) ^ (2 * k) := by
  classical
  let B := (k + 1) ^ (i.1 + 1) *
    (tail_width_nat k (i.1 + 1) + 1) ^ (2 * k)
  have hfinite : (large_k_lower_level_class (large_k_explicit_data k N) i).Finite := by
    apply Set.finite_iUnion
    intro j
    exact (domination_general_case_level_card k N j.1).1
  refine ⟨hfinite, le_trans (Set.ncard_iUnion_le_of_fintype _) ?_⟩
  calc
    (∑ j : {j : Fin N // j ≤ i},
        ((large_k_explicit_data k N).level_class j.1).ncard) ≤
        ∑ _j : {j : Fin N // j ≤ i}, B := by
      apply Finset.sum_le_sum
      intro j _
      refine le_trans (domination_general_case_level_card k N j.1).2 ?_
      dsimp [B]
      apply Nat.mul_le_mul
      · exact Nat.pow_le_pow_right (by omega) (by omega)
      · apply Nat.pow_le_pow_left
        unfold tail_width_nat
        gcongr
        all_goals omega
    _ = (i.1 + 1) * (k + 1) ^ (i.1 + 1) *
          (tail_width_nat k (i.1 + 1) + 1) ^ (2 * k) := by
      have hcard : Fintype.card {j : Fin N // j ≤ i} = i.1 + 1 := by
        let toF (j : {j : Fin N // j ≤ i}) : Fin (i.1 + 1) :=
          ⟨j.1.1, Nat.lt_succ_iff.mpr j.2⟩
        let invF (j : Fin (i.1 + 1)) : {j : Fin N // j ≤ i} :=
          ⟨⟨j.1, lt_of_le_of_lt (Nat.lt_succ_iff.mp j.2) i.2⟩,
            Nat.lt_succ_iff.mp j.2⟩
        have hleft : Function.LeftInverse invF toF := by
          intro j
          apply Subtype.ext
          apply Fin.ext
          rfl
        have hright : Function.RightInverse invF toF := by
          intro j
          apply Fin.ext
          rfl
        let e : {j : Fin N // j ≤ i} ≃ Fin (i.1 + 1) :=
          Equiv.mk toF invF hleft hright
        simpa using Fintype.card_congr e
      simp [B, hcard, Nat.mul_assoc]

@[blueprint "lem:domination-general-case-arithmetic"
  (statement := /-- Let $k,i\in\mathbb N$ with $k\geq2$. Then
    \[
      (i+1)(k+1)^{i+1}(\widehat w_{i+1}+1)^{2k}
      \leq \widehat w_{i+1}^{4k}.
    \] -/)
  (proof := /-- Put $a=8k$, $e=2^{2(i+1)}$, and $w=a^e=\widehat w_{i+1}$. Since
    $a\geq2$ and $e\geq2$, one has $w+1\leq2w$. Moreover,
    $i+1\leq a^{i+1}$, $(k+1)^{i+1}\leq a^{i+1}$, and
    $2^{2k}\leq a^{2k}$. The exponent inequality
    $2(i+1)+2k\leq2ke$ therefore gives
    $(i+1)(k+1)^{i+1}2^{2k}\leq w^{2k}$. Raising $w+1\leq2w$ to the
    power $2k$ and multiplying proves the displayed bound. -/)
  (title := /-- Integral Width Absorbs the Coarse Level Count -/)
  (latexEnv := "lemma")]
lemma domination_general_case_arithmetic (k i : ℕ) (hk : 2 ≤ k) :
    (i + 1) * (k + 1) ^ (i + 1) *
        (tail_width_nat k (i + 1) + 1) ^ (2 * k) ≤
      tail_width_nat k (i + 1) ^ (4 * k) := by
  let a := 8 * k
  let e := 2 ^ (2 * (i + 1))
  let w := tail_width_nat k (i + 1)
  have ha2 : 2 ≤ a := by dsimp [a]; omega
  have ha1 : 1 ≤ a := by omega
  have he2 : 2 ≤ e := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * (i + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hw : w = a ^ e := by rfl
  have hw1 : 1 ≤ w := by
    rw [hw]
    exact Nat.one_le_pow e a (by omega)
  have hwadd : w + 1 ≤ 2 * w := by omega
  have hi : i + 1 ≤ a ^ (i + 1) := by
    have hself : i + 1 < 2 ^ (i + 1) := Nat.lt_two_pow_self
    exact le_trans (le_of_lt hself)
      (Nat.pow_le_pow_left ha2 (i + 1))
  have hkbase : k + 1 ≤ a := by dsimp [a]; omega
  have hexp : 2 * (i + 1) + 2 * k ≤ e * (2 * k) := by
    have hie : i + 1 ≤ e := by
      have hself : i + 1 < 2 ^ (i + 1) := Nat.lt_two_pow_self
      dsimp [e]
      exact le_trans (le_of_lt hself)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    nlinarith
  have hfactor :
      (i + 1) * (k + 1) ^ (i + 1) * 2 ^ (2 * k) ≤ w ^ (2 * k) := by
    calc
      (i + 1) * (k + 1) ^ (i + 1) * 2 ^ (2 * k) ≤
          a ^ (i + 1) * a ^ (i + 1) * a ^ (2 * k) := by
        gcongr
      _ = a ^ (2 * (i + 1) + 2 * k) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      _ ≤ a ^ (e * (2 * k)) := Nat.pow_le_pow_right ha1 hexp
      _ = w ^ (2 * k) := by rw [hw, pow_mul]
  calc
    (i + 1) * (k + 1) ^ (i + 1) * (w + 1) ^ (2 * k) ≤
        (i + 1) * (k + 1) ^ (i + 1) * (2 * w) ^ (2 * k) := by
      gcongr
    _ = ((i + 1) * (k + 1) ^ (i + 1) * 2 ^ (2 * k)) * w ^ (2 * k) := by
      rw [mul_pow]
      ring
    _ ≤ w ^ (2 * k) * w ^ (2 * k) := Nat.mul_le_mul_right _ hfactor
    _ = w ^ (4 * k) := by
      rw [← pow_add]
      congr 1
      omega

@[blueprint "lem:domination-general-case"
  (statement := /-- Let $k,N\in\mathbb N$ satisfy $k\geq2$ and $N\geq1$. For every
    $i\in\operatorname{Fin}(N)$, the union of the explicit
    level classes through $i$ is finite and has cardinality at most
    $\widehat w_{i+1}^{4k}$. Moreover, if $i>0$, then the union of the level classes strictly
    below $i$ has cardinality less than $(\widehat w_{i+1}+1)^k$. Equivalently, the explicit
    datum satisfies the level-domination property of
    \cref{def:large-k-level-domination}. -/)
  (proof := /-- Fix $i\in\operatorname{Fin}(N)$. By
    \cref{lem:domination-general-case-lower-card}, the union through $i$ is finite and has
    cardinality at most
    $(i+1)(k+1)^{i+1}(\widehat w_{i+1}+1)^{2k}$.
    The arithmetic estimate \cref{lem:domination-general-case-arithmetic} bounds this quantity
    by $\widehat w_{i+1}^{4k}$. If $i>0$, the union strictly below $i$ is the union through
    level $i-1$. Applying the same two bounds at $i-1$ gives cardinality at most
    $\widehat w_i^{4k}$. The definition
    $\widehat w_r=(8k)^{2^{2r}}$ yields
    $\widehat w_i^{4k}=\widehat w_{i+1}^{k}$, which is strictly smaller than
    $(\widehat w_{i+1}+1)^k$ because $k\geq2$. At the same index,
    \cref{lem:width-domination} supplies the corresponding real-width domination estimate;
    pairing it with the strict integral comparison and taking the latter component proves the
    required bound. These are precisely all clauses of
    \cref{def:large-k-level-domination}. -/)
  (title := /-- Domination by the Current Level -/)
  (latexEnv := "lemma")]
lemma domination_general_case (k N : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N) :
    large_k_level_domination (large_k_explicit_data k N) := by
  intro i
  have hk1 : 1 ≤ k := by omega
  have hthrough := domination_general_case_lower_card k N hk1 i
  refine ⟨hthrough.1,
    le_trans hthrough.2 (domination_general_case_arithmetic k i.1 hk), ?_⟩
  intro hi
  let p : Fin N := ⟨i.1 - 1, lt_of_le_of_lt (Nat.sub_le i.1 1) i.2⟩
  have hunion :
      (⋃ j : {j : Fin N // j < i},
          (large_k_explicit_data k N).level_class j.1) =
        large_k_lower_level_class (large_k_explicit_data k N) p := by
    ext c
    simp only [large_k_lower_level_class, Set.mem_iUnion]
    constructor
    · rintro ⟨j, hc⟩
      refine ⟨⟨j.1, ?_⟩, hc⟩
      change j.1.1 ≤ p.1
      have hj : j.1.1 < i.1 := j.2
      dsimp [p]
      omega
    · rintro ⟨j, hc⟩
      refine ⟨⟨j.1, ?_⟩, hc⟩
      change j.1.1 < i.1
      have hj : j.1.1 ≤ p.1 := j.2
      dsimp [p] at hj
      omega
  rw [hunion]
  have hprev := domination_general_case_lower_card k N hk1 p
  refine lt_of_le_of_lt
    (le_trans hprev.2 (domination_general_case_arithmetic k p.1 hk)) ?_
  have hp : p.1 + 1 = i.1 := by
    dsimp [p]
    omega
  have hwidth :
      tail_width_nat k (p.1 + 1) ^ (4 * k) =
        tail_width_nat k (i.1 + 1) ^ k := by
    rw [hp]
    unfold tail_width_nat
    rw [← pow_mul, ← pow_mul]
    congr 1
    rw [show 2 * (i.1 + 1) = 2 * i.1 + 2 by omega, pow_add]
    ring
  rw [hwidth]
  exact (And.intro
    (width_domination k hk (i.1 + 2) (by omega))
    (Nat.pow_lt_pow_left (Nat.lt_succ_self _) (by omega))).2

@[blueprint "lem:f-and"
  (statement := /-- Let $k,N\in\mathbb N$ satisfy $k\geq2$ and $N\geq1$. For every Boolean
    labeling $c$ in the concrete family \cref{def:large-k-concrete-family}, every
    $i,j\in\{0,\ldots,N-1\}$ with $i<j$, every $r\in\{0,\ldots,2k-1\}$, and every
    $q\in\{0,\ldots,\widehat w_{i+1}-1\}$, one has $c(t_{i,r,q})=1$ if and only if
    $c(t_{j,r,y})=1$ for every $y\in\{0,\ldots,\widehat w_{j+1}-1\}$ whose parent column at
    level $i$ is $q$, as in \cref{def:large-k-f-and-property}. -/)
  (proof := /-- By \cref{def:large-k-concrete-family,def:large-k-concrete-level-class,
    def:large-k-product-class}, write $c=a\lor b$ at a source level $\ell$, where $a$ belongs
    to the head class and $b$ belongs to the tail class. The definition
    \cref{def:large-k-head-labeling} makes $a$ vanish on every tail point, while
    \cref{def:large-k-tail-class,def:large-k-tail-labeling} expresses $b$ in terms of a prefix
    length on each row. By \cref{def:tail-width-nat}, widths at nested levels divide one another.
    Consequently the quotient ratios in \cref{def:large-k-parent-column} multiply across nested
    levels: the parent from level $u$ to level $s$ is the composite of the parents from $u$ to
    an intermediate level $t$ and from $t$ to $s$. Moreover every column at level $t$ has a
    child at every higher level, obtained by multiplying its index by the corresponding quotient
    ratio, and every parent index lies within the lower width.

    If $\ell\leq i$, parent-map composition shows that the level-$\ell$ parent of every
    level-$j$ point above $q$ is the level-$\ell$ parent of $q$; the existence of a child above
    $q$ gives the reverse implication. If $j<\ell$, the universal condition defining the
    level-$i$ value is equivalent to first quantifying over the level-$j$ children of $q$ and
    then over their level-$\ell$ children: composition proves one direction, and assigning to
    each level-$\ell$ point its level-$j$ parent proves the other. In the remaining case
    $i<\ell\leq j$, composition sends every level-$j$ child of $q$ to a level-$\ell$ child of
    $q$, while the child-existence statement lifts every such level-$\ell$ child back to level
    $j$. These three cases give exactly the biconditional in
    \cref{def:large-k-f-and-property}. -/)
  (title := /-- Cross-Level Conjunction Identity -/)
  (latexEnv := "lemma")]
lemma f_and (k N : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N) :
    large_k_f_and_property (large_k_explicit_data k N) := by
  have hwidth_pos (t : ℕ) : 0 < tail_width_nat k t := by
    unfold tail_width_nat
    positivity
  have hwidth_dvd (a b : ℕ) (hab : a ≤ b) :
      tail_width_nat k a ∣ tail_width_nat k b := by
    unfold tail_width_nat
    apply Nat.pow_dvd_pow
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hparent_comp (a b d x : ℕ) (hab : a ≤ b) (hbd : b ≤ d) :
      large_k_parent_column k a b (large_k_parent_column k b d x) =
        large_k_parent_column k a d x := by
    unfold large_k_parent_column
    rw [Nat.div_div_eq_div_mul,
      Nat.div_mul_div (hwidth_dvd (b + 1) (d + 1) (by omega))
        (hwidth_dvd (a + 1) (b + 1) (by omega))]
  have hparent_lt (a b x : ℕ) (hab : a ≤ b)
      (hx : x < tail_width_nat k (b + 1)) :
      large_k_parent_column k a b x < tail_width_nat k (a + 1) := by
    have hdvd := hwidth_dvd (a + 1) (b + 1) (by omega)
    have hle := Nat.le_of_dvd (hwidth_pos (b + 1)) hdvd
    have hratio : 0 < tail_width_nat k (b + 1) / tail_width_nat k (a + 1) :=
      Nat.div_pos hle (hwidth_pos (a + 1))
    unfold large_k_parent_column
    rw [Nat.div_lt_iff_lt_mul hratio]
    simpa [Nat.mul_comm] using hx.trans_le
      (le_of_eq (Nat.div_mul_cancel hdvd).symm)
  have hchild (a b x : ℕ) (hab : a ≤ b)
      (hx : x < tail_width_nat k (a + 1)) :
      ∃ y : ℕ, y < tail_width_nat k (b + 1) ∧
        large_k_parent_column k a b y = x := by
    have hdvd := hwidth_dvd (a + 1) (b + 1) (by omega)
    have hle := Nat.le_of_dvd (hwidth_pos (b + 1)) hdvd
    have hratio : 0 < tail_width_nat k (b + 1) / tail_width_nat k (a + 1) :=
      Nat.div_pos hle (hwidth_pos (a + 1))
    refine ⟨x * (tail_width_nat k (b + 1) / tail_width_nat k (a + 1)), ?_, ?_⟩
    · calc
        x * (tail_width_nat k (b + 1) / tail_width_nat k (a + 1)) <
            tail_width_nat k (a + 1) *
              (tail_width_nat k (b + 1) / tail_width_nat k (a + 1)) :=
          (Nat.mul_lt_mul_right hratio).2 hx
        _ = tail_width_nat k (b + 1) := by
          simpa [Nat.mul_comm] using Nat.div_mul_cancel hdvd
    · unfold large_k_parent_column
      simpa [Nat.mul_comm] using
        Nat.mul_div_right x hratio
  unfold large_k_f_and_property
  dsimp [large_k_explicit_data]
  intro c hc i j hij r q
  rcases Set.mem_iUnion.mp hc with ⟨l, a, ha, b, hb, hab⟩
  rcases ha with ⟨v, hv, rfl⟩
  rcases hb with ⟨p, rfl⟩
  simp only [large_k_head_labeling, Bool.false_or] at hab
  simp_rw [hab]
  simp only [Bool.false_or]
  by_cases hjl : j < l
  · have hil : i < l := lt_trans hij hjl
    simp only [large_k_tail_labeling, dif_pos hil, dif_pos hjl, decide_eq_true_eq]
    constructor
    · intro h y hy z hz
      apply h z
      calc
        large_k_parent_column k i.1 l.1 z.1 =
            large_k_parent_column k i.1 j.1
              (large_k_parent_column k j.1 l.1 z.1) :=
          (hparent_comp i.1 j.1 l.1 z.1 (le_of_lt hij) (le_of_lt hjl)).symm
        _ = large_k_parent_column k i.1 j.1 y.1 := by rw [hz]
        _ = q.1 := hy
    · intro h z hz
      have hylt := hparent_lt j.1 l.1 z.1 (le_of_lt hjl) z.2
      let y : Fin (tail_width_nat k (j.1 + 1)) :=
        ⟨large_k_parent_column k j.1 l.1 z.1, hylt⟩
      apply h y
      · calc
          large_k_parent_column k i.1 j.1 y.1 =
              large_k_parent_column k i.1 l.1 z.1 :=
            hparent_comp i.1 j.1 l.1 z.1 (le_of_lt hij) (le_of_lt hjl)
          _ = q.1 := hz
      · rfl
  · have hlj : l ≤ j := le_of_not_gt hjl
    by_cases hli : l ≤ i
    · rcases hli.eq_or_lt with rfl | hli
      · simp only [large_k_tail_labeling, dif_neg (not_lt_of_ge le_rfl),
          dif_neg (not_lt_of_ge le_rfl), dif_neg hjl, dif_pos hij,
          decide_eq_true_eq]
        constructor
        · intro h y hy
          rwa [hy]
        · intro h
          rcases hchild l.1 j.1 q.1 (le_of_lt hij) q.2 with ⟨y, hylt, hyq⟩
          have := h ⟨y, hylt⟩ hyq
          rwa [hyq] at this
      · have hlj' : l < j := lt_of_lt_of_le hli (le_of_lt hij)
        simp only [large_k_tail_labeling, dif_neg (not_lt_of_ge (le_of_lt hli)),
          dif_pos hli, dif_neg (not_lt_of_ge (le_of_lt hlj')), dif_pos hlj',
          decide_eq_true_eq]
        constructor
        · intro h y hy
          rw [← hparent_comp l.1 i.1 j.1 y.1 (le_of_lt hli) (le_of_lt hij), hy]
          exact h
        · intro h
          rcases hchild i.1 j.1 q.1 (le_of_lt hij) q.2 with ⟨y, hylt, hyq⟩
          have := h ⟨y, hylt⟩ hyq
          rwa [← hparent_comp l.1 i.1 j.1 y (le_of_lt hli) (le_of_lt hij), hyq] at this
    · have hil : i < l := lt_of_not_ge hli
      rcases hlj.eq_or_lt with rfl | hlj
      · simp only [large_k_tail_labeling, dif_pos hij,
          dif_neg (not_lt_of_ge le_rfl), dif_neg (not_lt_of_ge le_rfl),
          decide_eq_true_eq]
      · simp only [large_k_tail_labeling, dif_pos hil,
          dif_neg (not_lt_of_ge (le_of_lt hlj)), dif_pos hlj, decide_eq_true_eq]
        constructor
        · intro h y hy
          have hzlt := hparent_lt l.1 j.1 y.1 (le_of_lt hlj) y.2
          apply h ⟨large_k_parent_column k l.1 j.1 y.1, hzlt⟩
          calc
            large_k_parent_column k i.1 l.1
                (large_k_parent_column k l.1 j.1 y.1) =
                large_k_parent_column k i.1 j.1 y.1 :=
              hparent_comp i.1 l.1 j.1 y.1 (le_of_lt hil) (le_of_lt hlj)
            _ = q.1 := hy
        · intro h z hz
          rcases hchild l.1 j.1 z.1 (le_of_lt hlj) z.2 with ⟨y, hylt, hyz⟩
          have hyq : large_k_parent_column k i.1 j.1 y = q.1 := by
            rw [← hparent_comp i.1 l.1 j.1 y (le_of_lt hil) (le_of_lt hlj), hyz]
            exact hz
          have := h ⟨y, hylt⟩ hyq
          rwa [hyz] at this

@[blueprint "lem:shatter-head-family-representation"
  (statement := /-- Let $k,N\in\mathbb N$. Every concept in the concrete family
    \cref{def:large-k-concrete-family} restricts on the head domain to the labeling induced by
    a sequence whose adjacent-change count is at most $k$. -/)
  (proof := /-- Unfold the union of the levelwise product classes. Membership supplies a level,
    an admissible head sequence, and a tail labeling. The admissibility condition
    \cref{def:large-k-head-admissible} bounds the change count, while
    \cref{def:large-k-tail-labeling} vanishes on every head point, so the Boolean product agrees
    there with \cref{def:large-k-head-labeling}. -/)
  (title := /-- Head Representation of a Concrete Concept -/)
  (latexEnv := "lemma")]
lemma shatter_head_family_representation {k N : ℕ}
    {c : large_k_domain k N → Bool} (hc : c ∈ large_k_concrete_family k N) :
    ∃ v : Fin N → Option (Fin k), large_k_head_change_count v ≤ k ∧
      ∀ (j : Fin N) (a : Fin k), c (Sum.inl (j, a)) = decide (v j = some a) := by
  simp only [large_k_concrete_family, Set.mem_iUnion] at hc
  obtain ⟨i, hc⟩ := hc
  rcases hc with ⟨a, ha, b, hb, hab⟩
  rcases ha with ⟨v, hv, rfl⟩
  rcases hb with ⟨p, rfl⟩
  refine ⟨v, hv.2.2, ?_⟩
  intro j q
  rw [hab]
  simp [large_k_head_labeling, large_k_tail_labeling]

@[blueprint "lem:shatter-head-adjacent-change"
  (statement := /-- Let $v$ be a finite sequence and let $i<j$ be two levels at which its
    values differ. Then some adjacent pair between $i$ and $j$ is counted by
    \cref{def:large-k-head-change-count}. -/)
  (proof := /-- If every adjacent pair from $i$ through $j-1$ had equal values, induction on
    the natural index from $i$ to $j$ would make the sequence constant on that interval. This
    would give $v_i=v_j$, contrary to the hypothesis. Hence one of those adjacent pairs differs,
    and it belongs to the filtered finset in \cref{def:large-k-head-change-count}. -/)
  (title := /-- A Change Between Unequal Endpoint Values -/)
  (latexEnv := "lemma")]
lemma shatter_head_adjacent_change {k N : ℕ} (v : Fin N → Option (Fin k))
    {i j : Fin N} (hij : i < j) (hne : v i ≠ v j) :
    ∃ p ∈ (Finset.univ.filter fun p : Fin N × Fin N =>
      p.1.1 + 1 = p.2.1 ∧ v p.1 ≠ v p.2),
      i.1 ≤ p.1.1 ∧ p.2.1 ≤ j.1 := by
  by_contra h
  push Not at h
  have hadj : ∀ n (hn : n < N) (hin : i.1 ≤ n) (hnj : n < j.1),
      v ⟨n, hn⟩ = v ⟨n + 1, by omega⟩ := by
    intro n hn hin hnj
    by_contra hne'
    have hout := h (⟨n, hn⟩, ⟨n + 1, by omega⟩) (by simp [hne']) hin
    change j.1 < n + 1 at hout
    omega
  have hconst : ∀ n (hn : n < N), i.1 ≤ n → n ≤ j.1 → v ⟨n, hn⟩ = v i := by
    intro n hn hin hnj
    induction n, hin using Nat.le_induction with
    | base => rfl
    | succ n hin ih =>
        calc
          v ⟨n + 1, hn⟩ = v ⟨n + 1, by omega⟩ := by congr
          _ = v ⟨n, by omega⟩ := (hadj n (by omega) hin (by omega)).symm
          _ = v i := ih (by omega) (by omega)
  exact hne ((hconst j.1 j.2 (by omega) (by omega)).symm)

@[blueprint "lem:shatter-head"
  (statement := /-- Let $k,N\in\mathbb N$ satisfy $k\geq2$ and $N\geq1$. Every finite set
    shattered by the concrete family \cref{def:large-k-concrete-family} contains at most
    $2k+1$ head points. -/)
  (proof := /-- Suppose that a shattered set has at least $2(k+1)$ head points, and order its
    head points lexicographically by level and then by column. Pair the first $2(k+1)$ points
    at positions $2r$ and $2r+1$. Prescribe label $1$ on every even point; on the following
    odd point prescribe label $0$ when the two columns agree and label $1$ when they differ.
    Shattering produces a concept realizing this prescription. By
    \cref{lem:shatter-head-family-representation}, its head restriction is induced by a
    sequence $v$ with at most $k$ adjacent changes. In each pair, the even label gives
    $v_i=a$. If the two levels were equal, lexicographic order would force distinct columns,
    while the two labels would force $v_i$ to equal both columns, a contradiction. Thus the
    levels satisfy $i<j$. When the columns agree, the odd label $0$ gives $v_j\neq a$; when
    they differ, the odd label $1$ gives $v_j=b\neq a$. Hence $v_i\neq v_j$ in both cases.
    By \cref{lem:shatter-head-adjacent-change}, choose an adjacent change between the levels
    of each pair. For $r<s$, lexicographic order places the odd level of pair $r$ at or below
    the even level of pair $s$, so the chosen adjacent changes are distinct. There are
    therefore at least $k+1$ adjacent changes, contradicting the bound on $v$. Consequently
    every shattered set has at most $2k+1$ head points, as required by
    \cref{def:large-k-head-shatter-bound}. -/)
  (title := /-- Few Head Points Can Be Shattered -/)
  (latexEnv := "lemma")]
lemma shatter_head (k N : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N) :
    large_k_head_shatter_bound (large_k_explicit_data k N) := by
  classical
  unfold large_k_head_shatter_bound
  dsimp only [large_k_explicit_data]
  intro W hW
  change ((↑W : Set (large_k_domain k N)) ∩
    {x | ∃ (i : Fin N) (a : Fin k), x = Sum.inl (i, a)}).ncard ≤ 2 * k + 1
  let H : Finset (Fin N ×ₗ Fin k) :=
    Finset.univ.filter fun x => Sum.inl (ofLex x) ∈ W
  let f : large_k_domain k N → Fin N ×ₗ Fin k := fun x =>
    match x with
    | Sum.inl y => toLex y
    | Sum.inr _ => toLex (⟨0, by omega⟩, ⟨0, by omega⟩)
  have himage : f '' ((↑W : Set (large_k_domain k N)) ∩
      {x | ∃ (i : Fin N) (a : Fin k), x = Sum.inl (i, a)}) = (↑H : Set (Fin N ×ₗ Fin k)) := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxW, i, a, rfl⟩, rfl⟩
      simpa [H, f, ofLex_toLex] using hxW
    · intro hy
      have hyW : Sum.inl (ofLex y) ∈ W := by simpa [H] using hy
      exact ⟨Sum.inl (ofLex y), ⟨hyW, (ofLex y).1, (ofLex y).2, rfl⟩,
        by simp [f, toLex_ofLex]⟩
  have hinj : Set.InjOn f ((↑W : Set (large_k_domain k N)) ∩
      {x | ∃ (i : Fin N) (a : Fin k), x = Sum.inl (i, a)}) := by
    rintro x ⟨-, i, a, rfl⟩ y ⟨-, j, b, rfl⟩ hxy
    exact congrArg Sum.inl (toLex.injective (by simpa [f] using hxy))
  have hcard :
      ((↑W : Set (large_k_domain k N)) ∩
        {x | ∃ (i : Fin N) (a : Fin k), x = Sum.inl (i, a)}).ncard = H.card := by
    rw [← hinj.ncard_image, himage]
    simp
  rw [hcard]
  by_contra hb
  have hlarge : 2 * (k + 1) ≤ H.card := by omega
  let E : Fin H.card ≃o H := H.orderIsoOfFin rfl
  let even : Fin (k + 1) → Fin H.card := fun r => ⟨2 * r.1, by omega⟩
  let odd : Fin (k + 1) → Fin H.card := fun r => ⟨2 * r.1 + 1, by omega⟩
  let e : Fin H.card → Fin N ×ₗ Fin k := fun n => (E n).1
  let p : large_k_domain k N → Bool := fun x =>
    match x with
    | Sum.inl y =>
        if hy : toLex y ∈ H then
          let n := E.symm ⟨toLex y, hy⟩
          if heven : n.1 % 2 = 0 then true
          else decide ((ofLex (e ⟨n.1 - 1, by omega⟩)).2 ≠ y.2)
        else false
    | Sum.inr _ => false
  obtain ⟨c, hc, hcW⟩ := hW p
  obtain ⟨v, hv, hcv⟩ := shatter_head_family_representation hc
  have he_mem (n : Fin H.card) : e n ∈ H := by
    exact (E n).2
  have he_symm (n : Fin H.card) : E.symm ⟨e n, he_mem n⟩ = n := by
    convert E.symm_apply_apply n using 1
  have he_lt {m n : Fin H.card} (hmn : m < n) : e m < e n := by
    exact E.lt_iff_lt.mpr hmn
  have heW (n : Fin H.card) : Sum.inl (ofLex (e n)) ∈ W := by
    simpa [H] using he_mem n
  have hp_even (r : Fin (k + 1)) :
      p (Sum.inl (ofLex (e (even r)))) = true := by
    simp [p, he_mem, he_symm, even]
  have hp_odd (r : Fin (k + 1)) :
      p (Sum.inl (ofLex (e (odd r)))) =
        decide ((ofLex (e (even r))).2 ≠ (ofLex (e (odd r))).2) := by
    simp [p, he_mem, he_symm, even, odd]
  have hv_even (r : Fin (k + 1)) :
      v (ofLex (e (even r))).1 = some (ofLex (e (even r))).2 := by
    have hc_true : c (Sum.inl (ofLex (e (even r)))) = true :=
      (hcW _ (heW _)).trans (hp_even r)
    have hdec := (hcv (ofLex (e (even r))).1
      (ofLex (e (even r))).2).symm.trans hc_true
    simpa using hdec
  have hv_odd (r : Fin (k + 1)) :
      decide (v (ofLex (e (odd r))).1 = some (ofLex (e (odd r))).2) =
        decide ((ofLex (e (even r))).2 ≠ (ofLex (e (odd r))).2) := by
    calc
      decide (v (ofLex (e (odd r))).1 = some (ofLex (e (odd r))).2) =
          c (Sum.inl (ofLex (e (odd r)))) :=
        (hcv (ofLex (e (odd r))).1 (ofLex (e (odd r))).2).symm
      _ = p (Sum.inl (ofLex (e (odd r)))) := hcW _ (heW _)
      _ = decide ((ofLex (e (even r))).2 ≠ (ofLex (e (odd r))).2) := hp_odd r
  have hlevel (r : Fin (k + 1)) :
      (ofLex (e (even r))).1 < (ofLex (e (odd r))).1 := by
    have hlex : e (even r) < e (odd r) := he_lt (by simp [even, odd])
    rcases Prod.Lex.lt_iff.mp hlex with hlt | ⟨heq, hab⟩
    · exact hlt
    · exfalso
      have hne : (ofLex (e (even r))).2 ≠ (ofLex (e (odd r))).2 :=
        ne_of_lt hab
      have hvj :
          v (ofLex (e (odd r))).1 = some (ofLex (e (odd r))).2 := by
        simpa [hne] using hv_odd r
      apply hne
      apply Option.some.inj
      exact (hv_even r).symm.trans (by simpa [heq] using hvj)
  have hv_ne (r : Fin (k + 1)) :
      v (ofLex (e (even r))).1 ≠ v (ofLex (e (odd r))).1 := by
    by_cases hab : (ofLex (e (even r))).2 = (ofLex (e (odd r))).2
    · have hvj :
          v (ofLex (e (odd r))).1 ≠ some (ofLex (e (odd r))).2 := by
        simpa [hab] using hv_odd r
      intro hsame
      apply hvj
      calc
        v (ofLex (e (odd r))).1 = v (ofLex (e (even r))).1 := hsame.symm
        _ = some (ofLex (e (even r))).2 := hv_even r
        _ = some (ofLex (e (odd r))).2 := by rw [hab]
    · have hvj :
          v (ofLex (e (odd r))).1 = some (ofLex (e (odd r))).2 := by
        simpa [hab] using hv_odd r
      intro hsame
      apply hab
      apply Option.some.inj
      calc
        some (ofLex (e (even r))).2 = v (ofLex (e (even r))).1 := (hv_even r).symm
        _ = v (ofLex (e (odd r))).1 := hsame
        _ = some (ofLex (e (odd r))).2 := hvj
  let C : Finset (Fin N × Fin N) :=
    Finset.univ.filter fun q => q.1.1 + 1 = q.2.1 ∧ v q.1 ≠ v q.2
  have hchange (r : Fin (k + 1)) :
      ∃ q ∈ C, (ofLex (e (even r))).1.1 ≤ q.1.1 ∧
        q.2.1 ≤ (ofLex (e (odd r))).1.1 := by
    simpa [C] using shatter_head_adjacent_change v (hlevel r) (hv_ne r)
  let g : Fin (k + 1) → Fin N × Fin N := fun r => (hchange r).choose
  have hg_mem (r : Fin (k + 1)) : g r ∈ C := by
    exact (hchange r).choose_spec.1
  have hg_bounds (r : Fin (k + 1)) :
      (ofLex (e (even r))).1.1 ≤ (g r).1.1 ∧
        (g r).2.1 ≤ (ofLex (e (odd r))).1.1 := by
    exact (hchange r).choose_spec.2
  have hg_ne {r s : Fin (k + 1)} (hrs : r < s) : g r ≠ g s := by
    intro heq
    have hindex : odd r < even s := by
      simp [odd, even]
      omega
    have hlevels :
        (ofLex (e (odd r))).1 ≤ (ofLex (e (even s))).1 :=
      (Prod.Lex.lt_iff'.mp (he_lt hindex)).1
    have hsep : (g r).2.1 ≤ (g s).1.1 :=
      (hg_bounds r).2.trans (hlevels.trans (hg_bounds s).1)
    rw [heq] at hsep
    have hadj : (g s).1.1 + 1 = (g s).2.1 :=
      (Finset.mem_filter.mp (hg_mem s)).2.1
    omega
  have hg_inj : Function.Injective g := by
    intro r s hrs
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hg_ne hlt hrs
    · exact hg_ne hgt hrs.symm
  let g' : Fin (k + 1) → {q // q ∈ C} := fun r => ⟨g r, hg_mem r⟩
  have hg'_inj : Function.Injective g' := by
    intro r s hrs
    apply hg_inj
    exact congrArg Subtype.val hrs
  have hmany : k + 1 ≤ large_k_head_change_count v := by
    have hcard_subtype := Fintype.card_le_of_injective g' hg'_inj
    have hC : k + 1 ≤ C.card := by
      simpa only [Fintype.card_fin, Fintype.card_coe] using hcard_subtype
    simpa [C, large_k_head_change_count] using hC
  omega

@[blueprint "lem:shatter-tail-level-monotone"
  (statement := /-- Let $k,N\in\mathbb N$ with $k\geq1$. For every concept in the concrete
    family, the labels along any fixed tail row and level are nonincreasing as the column index
    increases. -/)
  (proof := /-- Unfold membership in the union of levelwise product classes. The head labeling
    vanishes on tail points by \cref{def:large-k-head-labeling}, so only the propagated prefix
    labeling \cref{def:large-k-tail-labeling} remains. At its source level monotonicity is the
    prefix property; above that level it follows from monotonicity of the parent-column quotient.
    Below the source level, choose the first child of the later column. Divisibility of the
    integral widths places every child of the earlier column before it, so truth of the
    conjunction for the later column implies truth for the earlier column. -/)
  (title := /-- Monotonicity Along a Tail Row -/)
  (latexEnv := "lemma")]
lemma shatter_tail_level_monotone {k N : ℕ} {c : large_k_domain k N → Bool}
    (hk : 1 ≤ k) (hc : c ∈ large_k_concrete_family k N) (j : Fin N) (r : Fin (2 * k))
    (q u : Fin (tail_width_nat k (j.1 + 1))) (hqu : q ≤ u)
    (hu : c (Sum.inr ⟨j, r, u⟩) = true) :
    c (Sum.inr ⟨j, r, q⟩) = true := by
  have hwidth_pos (t : ℕ) : 0 < tail_width_nat k t := by
    unfold tail_width_nat
    positivity
  have hwidth_dvd (a b : ℕ) (hab : a ≤ b) :
      tail_width_nat k a ∣ tail_width_nat k b := by
    unfold tail_width_nat
    apply Nat.pow_dvd_pow
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases Set.mem_iUnion.mp hc with ⟨l, a, ha, b, hb, hab⟩
  rcases ha with ⟨v, hv, rfl⟩
  rcases hb with ⟨p, rfl⟩
  simp only [large_k_head_labeling, Bool.false_or] at hab
  simp_rw [hab] at hu ⊢
  simp only [Bool.false_or] at hu ⊢
  by_cases hjl : j < l
  · by_cases hqu_eq : q = u
    · subst u
      exact hu
    · have hqu_lt : q.1 < u.1 := by
        have hne : q.1 ≠ u.1 := fun h => hqu_eq (Fin.ext h)
        omega
      have hdvd := hwidth_dvd (j.1 + 1) (l.1 + 1) (by omega)
      have hle := Nat.le_of_dvd (hwidth_pos (l.1 + 1)) hdvd
      have hratio :
          0 < tail_width_nat k (l.1 + 1) / tail_width_nat k (j.1 + 1) :=
        Nat.div_pos hle (hwidth_pos (j.1 + 1))
      let z : Fin (tail_width_nat k (l.1 + 1)) :=
        ⟨u.1 * (tail_width_nat k (l.1 + 1) /
            tail_width_nat k (j.1 + 1)), by
          calc
            u.1 * (tail_width_nat k (l.1 + 1) /
                tail_width_nat k (j.1 + 1)) <
                tail_width_nat k (j.1 + 1) *
                  (tail_width_nat k (l.1 + 1) /
                    tail_width_nat k (j.1 + 1)) :=
              (Nat.mul_lt_mul_right hratio).2 u.2
            _ = tail_width_nat k (l.1 + 1) := by
              simpa [Nat.mul_comm] using Nat.div_mul_cancel hdvd⟩
      have hzparent : large_k_parent_column k j.1 l.1 z.1 = u.1 := by
        unfold large_k_parent_column
        simpa [z, Nat.mul_comm] using Nat.mul_div_right u.1 hratio
      simp only [large_k_tail_labeling, dif_pos hjl, decide_eq_true_eq] at hu ⊢
      intro y hy
      have hydiv :
          y.1 / (tail_width_nat k (l.1 + 1) /
            tail_width_nat k (j.1 + 1)) = q.1 := by
        simpa [large_k_parent_column] using hy
      have hyz : y.1 < z.1 := by
        dsimp only [z]
        apply Nat.lt_mul_of_div_lt
        · simpa [hydiv] using hqu_lt
        · exact hratio
      exact hyz.trans (hu z hzparent)
  · have hlj : l ≤ j := le_of_not_gt hjl
    by_cases hlj_strict : l < j
    · simp only [large_k_tail_labeling, dif_neg hjl, dif_pos hlj_strict,
        decide_eq_true_eq] at hu ⊢
      exact (Nat.div_le_div_right hqu).trans_lt hu
    · have hlj_eq : l = j := le_antisymm hlj (le_of_not_gt hlj_strict)
      subst j
      simp only [large_k_tail_labeling, dif_neg (not_lt_of_ge le_rfl),
        decide_eq_true_eq] at hu ⊢
      omega

@[blueprint "lem:shatter-tail"
  (statement := /-- Let $k,N\in\mathbb N$ satisfy $k\geq2$ and $N\geq1$. If $W$ is a finite
    subset of the concrete multilevel domain \cref{def:large-k-domain} shattered by the family
    \cref{def:large-k-concrete-family}, then
    $|W\cap \cref{def:large-k-tail-domain}|\leq 2k$. -/)
  (proof := /-- Associate to each tail point its row. Two distinct points in one row cannot both
    belong to a shattered set. At a common level, monotonicity along the row
    \cref{lem:shatter-tail-level-monotone} rules out one of the two opposite label patterns.
    At levels $i<j$, write the columns as $q_i,q_j$. If the level-$i$ parent of $q_j$ is at
    most $q_i$, prescribe labels $(1,0)$. The conjunction identity \cref{lem:f-and}, together
    with row monotonicity, forces the upper label to be $1$. If the parent is greater than
    $q_i$, prescribe $(0,1)$; every child of $q_i$ precedes $q_j$, so row monotonicity and the
    same conjunction identity force the lower label to be $1$. Both prescriptions contradict
    shattering. Hence the row map is injective on the tail points of a shattered finite set,
    and comparison with the $2k$ rows gives \cref{def:large-k-tail-shatter-bound}. -/)
  (title := /-- Few Tail Points Can Be Shattered -/)
  (latexEnv := "lemma")]
lemma shatter_tail (k N : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N) :
    large_k_tail_shatter_bound (large_k_explicit_data k N) := by
  classical
  have hk1 : 1 ≤ k := by omega
  have hwidth_pos (t : ℕ) : 0 < tail_width_nat k t := by
    unfold tail_width_nat
    positivity
  have hwidth_dvd (a b : ℕ) (hab : a ≤ b) :
      tail_width_nat k a ∣ tail_width_nat k b := by
    unfold tail_width_nat
    apply Nat.pow_dvd_pow
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hchild (a b x : ℕ) (hab : a ≤ b)
      (hx : x < tail_width_nat k (a + 1)) :
      ∃ y : ℕ, y < tail_width_nat k (b + 1) ∧
        large_k_parent_column k a b y = x := by
    have hdvd := hwidth_dvd (a + 1) (b + 1) (by omega)
    have hle := Nat.le_of_dvd (hwidth_pos (b + 1)) hdvd
    have hratio : 0 < tail_width_nat k (b + 1) / tail_width_nat k (a + 1) :=
      Nat.div_pos hle (hwidth_pos (a + 1))
    refine ⟨x * (tail_width_nat k (b + 1) / tail_width_nat k (a + 1)), ?_, ?_⟩
    · calc
        x * (tail_width_nat k (b + 1) / tail_width_nat k (a + 1)) <
            tail_width_nat k (a + 1) *
              (tail_width_nat k (b + 1) / tail_width_nat k (a + 1)) :=
          (Nat.mul_lt_mul_right hratio).2 hx
        _ = tail_width_nat k (b + 1) := by
          simpa [Nat.mul_comm] using Nat.div_mul_cancel hdvd
    · unfold large_k_parent_column
      simpa [Nat.mul_comm] using Nat.mul_div_right x hratio
  unfold large_k_tail_shatter_bound
  dsimp only [large_k_explicit_data]
  intro W hW
  change ((↑W : Set (large_k_domain k N)) ∩
    {x | ∃ (i : Fin N) (r : Fin (2 * k))
      (q : Fin (tail_width_nat k (i.1 + 1))), x = Sum.inr ⟨i, r, q⟩}).ncard ≤ 2 * k
  have hsame (i : Fin N) (r : Fin (2 * k))
      (q u : Fin (tail_width_nat k (i.1 + 1)))
      (hqW : Sum.inr ⟨i, r, q⟩ ∈ W) (huW : Sum.inr ⟨i, r, u⟩ ∈ W) : q = u := by
    by_contra hqu
    have hpoints :
        (Sum.inr ⟨i, r, q⟩ : large_k_domain k N) ≠ Sum.inr ⟨i, r, u⟩ := by
      intro h
      apply hqu
      simpa using h
    rcases lt_or_gt_of_ne hqu with hlt | hgt
    · let p : large_k_domain k N → Bool := fun x => decide (x = Sum.inr ⟨i, r, u⟩)
      obtain ⟨c, hc, hcW⟩ := hW p
      have hcu : c (Sum.inr ⟨i, r, u⟩) = true := by
        calc
          c (Sum.inr ⟨i, r, u⟩) = p (Sum.inr ⟨i, r, u⟩) := hcW _ huW
          _ = true := by simp [p]
      have hcq : c (Sum.inr ⟨i, r, q⟩) = false := by
        calc
          c (Sum.inr ⟨i, r, q⟩) = p (Sum.inr ⟨i, r, q⟩) := hcW _ hqW
          _ = false := by simp [p, ne_of_lt hlt]
      have htrue := shatter_tail_level_monotone hk1 hc i r q u (le_of_lt hlt) hcu
      rw [hcq] at htrue
      simp at htrue
    · let p : large_k_domain k N → Bool := fun x => decide (x = Sum.inr ⟨i, r, q⟩)
      obtain ⟨c, hc, hcW⟩ := hW p
      have hcq : c (Sum.inr ⟨i, r, q⟩) = true := by
        calc
          c (Sum.inr ⟨i, r, q⟩) = p (Sum.inr ⟨i, r, q⟩) := hcW _ hqW
          _ = true := by simp [p]
      have hcu : c (Sum.inr ⟨i, r, u⟩) = false := by
        calc
          c (Sum.inr ⟨i, r, u⟩) = p (Sum.inr ⟨i, r, u⟩) := hcW _ huW
          _ = false := by simp [p, ne_of_lt hgt]
      have htrue := shatter_tail_level_monotone hk1 hc i r u q (le_of_lt hgt) hcq
      rw [hcu] at htrue
      simp at htrue
  have hcross (i j : Fin N) (hij : i < j) (r : Fin (2 * k))
      (q : Fin (tail_width_nat k (i.1 + 1)))
      (u : Fin (tail_width_nat k (j.1 + 1)))
      (hqW : Sum.inr ⟨i, r, q⟩ ∈ W) (huW : Sum.inr ⟨j, r, u⟩ ∈ W) : False := by
    have hpoints :
        (Sum.inr ⟨i, r, q⟩ : large_k_domain k N) ≠ Sum.inr ⟨j, r, u⟩ := by
      intro h
      have hsigma :
          (⟨i, r, q⟩ : Σ t : Fin N,
            Fin (2 * k) × Fin (tail_width_nat k (t.1 + 1))) = ⟨j, r, u⟩ :=
        Sum.inr.inj h
      exact (ne_of_lt hij) (congrArg Sigma.fst hsigma)
    by_cases hp : large_k_parent_column k i.1 j.1 u.1 ≤ q.1
    · let p : large_k_domain k N → Bool := fun x => decide (x = Sum.inr ⟨i, r, q⟩)
      obtain ⟨c, hc, hcW⟩ := hW p
      have hcq : c (Sum.inr ⟨i, r, q⟩) = true := by
        calc
          c (Sum.inr ⟨i, r, q⟩) = p (Sum.inr ⟨i, r, q⟩) := hcW _ hqW
          _ = true := by simp [p]
      have hcu : c (Sum.inr ⟨j, r, u⟩) = false := by
        calc
          c (Sum.inr ⟨j, r, u⟩) = p (Sum.inr ⟨j, r, u⟩) := hcW _ huW
          _ = false := by
            have hne :
                (Sum.inr ⟨j, r, u⟩ : large_k_domain k N) ≠ Sum.inr ⟨i, r, q⟩ :=
              hpoints.symm
            simp [p, hne]
      have hand : c (Sum.inr ⟨i, r, q⟩) = true ↔
          ∀ y : Fin (tail_width_nat k (j.1 + 1)),
            large_k_parent_column k i.1 j.1 y.1 = q.1 →
              c (Sum.inr ⟨j, r, y⟩) = true := by
        simpa only [large_k_explicit_data] using (f_and k N hk hN c hc i j hij r q)
      rcases hp.eq_or_lt with hp_eq | hp_lt
      · have htrue := (hand.mp hcq) u hp_eq
        rw [hcu] at htrue
        simp at htrue
      · rcases hchild i.1 j.1 q.1 (le_of_lt hij) q.2 with ⟨y, hylt, hyparent⟩
        let y' : Fin (tail_width_nat k (j.1 + 1)) := ⟨y, hylt⟩
        have huy : u < y' := by
          apply Nat.lt_of_div_lt_div
          simpa [large_k_parent_column, y'] using hp_lt.trans_eq hyparent.symm
        have hcy : c (Sum.inr ⟨j, r, y'⟩) = true := (hand.mp hcq) y' hyparent
        have htrue :=
          shatter_tail_level_monotone hk1 hc j r u y' (le_of_lt huy) hcy
        rw [hcu] at htrue
        simp at htrue
    · have hp_lt : q.1 < large_k_parent_column k i.1 j.1 u.1 := by omega
      let p : large_k_domain k N → Bool := fun x => decide (x = Sum.inr ⟨j, r, u⟩)
      obtain ⟨c, hc, hcW⟩ := hW p
      have hcu : c (Sum.inr ⟨j, r, u⟩) = true := by
        calc
          c (Sum.inr ⟨j, r, u⟩) = p (Sum.inr ⟨j, r, u⟩) := hcW _ huW
          _ = true := by simp [p]
      have hcq : c (Sum.inr ⟨i, r, q⟩) = false := by
        calc
          c (Sum.inr ⟨i, r, q⟩) = p (Sum.inr ⟨i, r, q⟩) := hcW _ hqW
          _ = false := by simp [p, hpoints]
      have hand : c (Sum.inr ⟨i, r, q⟩) = true ↔
          ∀ y : Fin (tail_width_nat k (j.1 + 1)),
            large_k_parent_column k i.1 j.1 y.1 = q.1 →
              c (Sum.inr ⟨j, r, y⟩) = true := by
        simpa only [large_k_explicit_data] using (f_and k N hk hN c hc i j hij r q)
      have htrue : c (Sum.inr ⟨i, r, q⟩) = true := hand.mpr (by
        intro y hy
        have hyu : y < u := by
          apply Nat.lt_of_div_lt_div
          simpa [large_k_parent_column] using hy.trans_lt hp_lt
        exact shatter_tail_level_monotone hk1 hc j r y u (le_of_lt hyu) hcu)
      rw [hcq] at htrue
      simp at htrue
  let T : Finset (Σ i : Fin N,
      Fin (2 * k) × Fin (tail_width_nat k (i.1 + 1))) :=
    Finset.univ.filter fun y => Sum.inr y ∈ W
  let f : large_k_domain k N →
      (Σ i : Fin N, Fin (2 * k) × Fin (tail_width_nat k (i.1 + 1))) := fun x =>
    match x with
    | Sum.inl _ => ⟨⟨0, by omega⟩, ⟨0, by omega⟩, ⟨0, hwidth_pos 1⟩⟩
    | Sum.inr y => y
  have himage : f '' ((↑W : Set (large_k_domain k N)) ∩
      {x | ∃ (i : Fin N) (r : Fin (2 * k))
        (q : Fin (tail_width_nat k (i.1 + 1))), x = Sum.inr ⟨i, r, q⟩}) =
      (↑T : Set (Σ i : Fin N,
        Fin (2 * k) × Fin (tail_width_nat k (i.1 + 1)))) := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxW, i, r, q, rfl⟩, rfl⟩
      simpa [T, f] using hxW
    · intro hy
      have hyW : Sum.inr y ∈ W := by simpa [T] using hy
      rcases y with ⟨i, r, q⟩
      exact ⟨Sum.inr ⟨i, r, q⟩, ⟨hyW, i, r, q, rfl⟩, by simp [f]⟩
  have hinj : Set.InjOn f ((↑W : Set (large_k_domain k N)) ∩
      {x | ∃ (i : Fin N) (r : Fin (2 * k))
        (q : Fin (tail_width_nat k (i.1 + 1))), x = Sum.inr ⟨i, r, q⟩}) := by
    rintro x ⟨-, i, r, q, rfl⟩ y ⟨-, j, s, u, rfl⟩ hxy
    exact congrArg Sum.inr (by simpa [f] using hxy)
  have hcard :
      ((↑W : Set (large_k_domain k N)) ∩
        {x | ∃ (i : Fin N) (r : Fin (2 * k))
          (q : Fin (tail_width_nat k (i.1 + 1))), x = Sum.inr ⟨i, r, q⟩}).ncard =
        T.card := by
    rw [← hinj.ncard_image, himage]
    simp
  rw [hcard]
  let row : {y // y ∈ T} → Fin (2 * k) := fun y => y.1.2.1
  have hrow_inj : Function.Injective row := by
    rintro ⟨⟨i, r, q⟩, hi⟩ ⟨⟨j, s, u⟩, hj⟩ hrs
    have hrs' : r = s := by simpa [row] using hrs
    subst s
    apply Subtype.ext
    have hiW : Sum.inr ⟨i, r, q⟩ ∈ W := by simpa [T] using hi
    have hjW : Sum.inr ⟨j, r, u⟩ ∈ W := by simpa [T] using hj
    by_cases hij : i = j
    · subst j
      have hqu := hsame i r q u hiW hjW
      subst u
      rfl
    · rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact False.elim (hcross i j hlt r q u hiW hjW)
      · exact False.elim (hcross j i hgt r u q hjW hiW)
  have hbound := Fintype.card_le_of_injective row hrow_inj
  simpa only [Fintype.card_coe, Fintype.card_fin] using hbound

@[blueprint "lem:large-k-construction-exists"
  (statement := /-- Let $k,N\in\mathbb N$ satisfy $2\leq k$ and $1\leq N$. There exists a
    verified large-$k$ construction in the sense of \cref{def:large-k-construction}, whose
    underlying datum is the explicit multilevel datum of \cref{def:large-k-explicit-data}. -/)
  (proof := /-- Take the underlying datum to be \cref{def:large-k-explicit-data}; its equality
    with the explicit datum is reflexive. Supply the tail- and head-consistency fields using
    \cref{lem:tail-set} and \cref{lem:head-set}, the level-domination field using
    \cref{lem:domination-general-case}, the cross-level conjunction field using
    \cref{lem:f-and}, and the two shatter-bound fields using \cref{lem:shatter-head} and
    \cref{lem:shatter-tail}. These fields define a value of
    \cref{def:large-k-construction}, proving that this type is nonempty. -/)
  (title := /-- Existence of the Verified Multilevel Construction -/)
  (latexEnv := "lemma")]
lemma large_k_construction_exists (k N : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N) :
    Nonempty (large_k_construction k N) := by
  exact ⟨{
    data := large_k_explicit_data k N
    data_eq := rfl
    tail_consistency := tail_set k N hk hN
    head_consistency := head_set k N hk hN
    level_domination := domination_general_case k N hk hN
    f_and := f_and k N hk hN
    shatter_head := shatter_head k N hk hN
    shatter_tail := shatter_tail k N hk hN
  }⟩

@[blueprint "lem:large-k-vc-bound"
  (statement := /-- Let $k,N\in\mathbb N$ satisfy $2\leq k$ and $1\leq N$, and let $D$ be a
    verified large-$k$ construction. Then the concept family $D.\mathrm{data}.\mathrm{family}$
    has VC dimension at most $4k+1$. -/)
  (proof := /-- Fix a finite set $W$ shattered by the concept family. The head- and
    tail-shatter fields of the verified construction \cref{def:large-k-construction} show that
    the intersection of $W$ with the head domain \cref{def:large-k-head-domain} has cardinality
    at most $2k+1$, while its intersection with the tail domain
    \cref{def:large-k-tail-domain} has cardinality at most $2k$. The domain-exhaustion field of
    the construction datum places every element of $W$ in the union of these two intersections.
    Monotonicity and subadditivity of finite-set cardinality therefore give
    \[ |W|\leq (2k+1)+2k=4k+1. \]
    Since this holds for every shattered finite set, \cref{lem:vc-le-of-shatter-bound} yields
    the claimed VC-dimension bound. -/)
  (title := /-- VC Bound for the Multilevel Construction -/)
  (latexEnv := "lemma")]
lemma large_k_vc_bound (k N : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N)
    (D : large_k_construction k N) :
    vc_dim D.data.family ≤ 4 * k + 1 := by
  apply vc_le_of_shatter_bound
  intro W hW
  have hhead := D.shatter_head W hW
  have htail := D.shatter_tail W hW
  calc
    W.card = (↑W : Set D.data.X).ncard := by simp
    _ ≤ (((↑W : Set D.data.X) ∩ large_k_head_domain D.data) ∪
        ((↑W : Set D.data.X) ∩ large_k_tail_domain D.data)).ncard := by
      refine Set.ncard_le_ncard ?_ ?_
      · intro x hx
        rcases D.data.domain_exhaustive x with hxhead | hxtail
        · exact Set.mem_union_left _ ⟨hx, hxhead⟩
        · exact Set.mem_union_right _ ⟨hx, hxtail⟩
      · exact (W.finite_toSet.inter_of_left _).union
          (W.finite_toSet.inter_of_left _)
    _ ≤ ((↑W : Set D.data.X) ∩ large_k_head_domain D.data).ncard +
        ((↑W : Set D.data.X) ∩ large_k_tail_domain D.data).ncard :=
      Set.ncard_union_le _ _
    _ ≤ (2 * k + 1) + 2 * k := Nat.add_le_add hhead htail
    _ = 4 * k + 1 := by omega

@[blueprint "lem:large-k-family-finite"
  (statement := /-- Let $k,N\in\mathbb N$ satisfy $k\geq2$ and $N\geq1$, and let $D$ be a
    verified large-$k$ construction. Then $D.\mathrm{data}.\mathrm{family}$ is finite. -/)
  (proof := /-- Use $D.\mathrm{data\_eq}$ from \cref{def:large-k-construction} to identify
    $D.\mathrm{data}$ with the explicit datum of \cref{def:large-k-explicit-data}. Since
    $N\geq1$, the index $i=N-1$ belongs to $\operatorname{Fin}(N)$.
    By \cref{lem:domination-general-case}, the union through $i$ defined in
    \cref{def:large-k-lower-level-class} is finite. Unfolding the explicit family from
    \cref{def:large-k-concrete-family}, every level index $j\in\operatorname{Fin}(N)$
    satisfies $j\leq N-1=i$, while the reverse inclusion of the union through $i$ in the
    union over all levels is immediate. Thus the explicit family equals the finite union
    through $i$, and transporting this finiteness along $D.\mathrm{data\_eq}$ proves the
    claim. -/)
  (title := /-- Finiteness of the Constructed Family -/)
  (latexEnv := "lemma")]
lemma large_k_family_finite (k N : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N)
    (D : large_k_construction k N) : D.data.family.Finite := by
  rw [D.data_eq]
  let i : Fin N := ⟨N - 1, by omega⟩
  have h := (domination_general_case k N hk hN i).1
  have h_eq :
      (large_k_explicit_data k N).family =
        large_k_lower_level_class (large_k_explicit_data k N) i := by
    change (⋃ j : Fin N, large_k_concrete_level_class k N j) =
      ⋃ j : {j : Fin N // j ≤ i}, large_k_concrete_level_class k N j.1
    apply Set.ext
    intro c
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨⟨j, ?_⟩, hj⟩
      change j.1 ≤ i.1
      dsimp [i]
      omega
    · rintro ⟨j, hj⟩
      exact ⟨j.1, hj⟩
  rw [h_eq]
  exact h

@[blueprint "lem:large-k-family-card-bound"
  (statement := /-- Let $k,N\in\mathbb N$ satisfy $k\geq2$ and $N\geq1$, and let $D$ be a
    verified large-$k$ construction. Then
    $|D.\mathrm{data}.\mathrm{family}|\leq w_N^{4k}$. -/)
  (proof := /-- Transport along $D.\mathrm{data\_eq}$ to the explicit datum and apply the
    top-level estimate of \cref{lem:domination-general-case}. Its integral upper bound is
    $\widehat w_N^{4k}$; \cref{lem:tail-width-eq-nat} identifies $\widehat w_N$ with the real
    width $w_N$, yielding the stated inequality after coercing the finite cardinality to
    $\mathbb R$. -/)
  (title := /-- Cardinality Bound for the Constructed Family -/)
  (latexEnv := "lemma")]
lemma large_k_family_card_bound (k N : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N)
    (D : large_k_construction k N) :
    (D.data.family.ncard : ℝ) ≤ tail_width k N ^ (4 * k) := by
  rw [D.data_eq]
  let i : Fin N := ⟨N - 1, by omega⟩
  have hdom := domination_general_case k N hk hN i
  have hi : i.1 + 1 = N := by
    dsimp [i]
    omega
  have hfamily :
      (large_k_explicit_data k N).family =
        large_k_lower_level_class (large_k_explicit_data k N) i := by
    rw [(large_k_explicit_data k N).family_union]
    ext c
    simp only [large_k_lower_level_class, Set.mem_iUnion]
    constructor
    · rintro ⟨j, hc⟩
      refine ⟨⟨j, ?_⟩, hc⟩
      dsimp [i]
      omega
    · rintro ⟨j, hc⟩
      exact ⟨j.1, hc⟩
  have hcard :
      (large_k_explicit_data k N).family.ncard ≤
        tail_width_nat k N ^ (4 * k) := by
    rw [hfamily]
    simpa [hi] using hdom.2.1
  rw [tail_width_eq_nat k N (by omega)]
  exact_mod_cast hcard

@[blueprint "lem:large-k-domain-card-bound"
  (statement := /-- Let $k,N\in\mathbb N$ satisfy $k\geq2$ and $N\geq1$, and let $D$ be a
    verified large-$k$ construction. Its finite domain satisfies
    $|D.\mathrm{data}.X|\leq6k w_N$. -/)
  (proof := /-- By the equality field in \cref{def:large-k-construction} and the explicit datum
    of \cref{def:large-k-explicit-data,def:large-k-domain}, the domain has exactly $kN$ head
    points and $2k\sum_{i=1}^{N}\widehat w_i$ tail points. From
    \cref{def:tail-width-nat} and $k\geq2$, exponent monotonicity gives
    $2\widehat w_i\leq\widehat w_{i+1}$ for every $i$. Induction on $n$ therefore yields
    $\sum_{i=1}^{n}\widehat w_i\leq2\widehat w_n$. A second induction gives $n\leq2^n$;
    monotonicity in both the base and exponent then implies $N\leq\widehat w_N$. Consequently
    $kN+2k\sum_{i=1}^{N}\widehat w_i\leq k\widehat w_N+4k\widehat w_N
    \leq6k\widehat w_N$. Finally \cref{lem:tail-width-eq-nat} identifies
    $\widehat w_N$ with $w_N$, proving the asserted real-valued cardinality bound. -/)
  (title := /-- Cardinality Bound for the Constructed Domain -/)
  (latexEnv := "lemma")]
lemma large_k_domain_card_bound (k N : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N)
    (D : large_k_construction k N) :
    (Nat.card D.data.X : ℝ) ≤ 6 * (k : ℝ) * tail_width k N := by
  have hbase : 2 ≤ 8 * k := by omega
  have hwidth_step : ∀ i : ℕ,
      2 * tail_width_nat k i ≤ tail_width_nat k (i + 1) := by
    intro i
    have hexp_pos : 0 < 2 ^ (2 * i) := pow_pos (by omega) _
    have hexp : 2 ^ (2 * i) + 1 ≤ 2 ^ (2 * (i + 1)) := by
      rw [show 2 * (i + 1) = 2 * i + 2 by omega, pow_add]
      norm_num
    unfold tail_width_nat
    calc
      2 * (8 * k) ^ (2 ^ (2 * i)) ≤
          (8 * k) * (8 * k) ^ (2 ^ (2 * i)) :=
        Nat.mul_le_mul_right _ hbase
      _ = (8 * k) ^ (2 ^ (2 * i) + 1) := by
        rw [pow_succ]
        ac_rfl
      _ ≤ (8 * k) ^ (2 ^ (2 * (i + 1))) :=
        Nat.pow_le_pow_right (by omega) hexp
  have hsum : ∀ n : ℕ,
      (∑ i : Fin n, tail_width_nat k (i.1 + 1)) ≤
        2 * tail_width_nat k n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.coe_castSucc, Fin.val_last]
        calc
          (∑ i : Fin n, tail_width_nat k (i.1 + 1)) +
              tail_width_nat k (n + 1) ≤
              2 * tail_width_nat k n + tail_width_nat k (n + 1) :=
            Nat.add_le_add_right ih _
          _ ≤ tail_width_nat k (n + 1) + tail_width_nat k (n + 1) :=
            Nat.add_le_add_right (hwidth_step n) _
          _ = 2 * tail_width_nat k (n + 1) := by omega
  have htwo : ∀ n : ℕ, n ≤ 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        have hpow : 1 ≤ 2 ^ n := one_le_pow₀ (by omega)
        omega
  have hNwidth : N ≤ tail_width_nat k N := by
    unfold tail_width_nat
    calc
      N ≤ 2 ^ N := htwo N
      _ ≤ (8 * k) ^ N := Nat.pow_le_pow_left hbase N
      _ ≤ (8 * k) ^ (2 ^ (2 * N)) := by
        apply Nat.pow_le_pow_right (by omega)
        calc
          N ≤ 2 ^ N := htwo N
          _ ≤ 2 ^ (2 * N) := Nat.pow_le_pow_right (by omega) (by omega)
  rw [D.data_eq, tail_width_eq_nat k N (by omega)]
  simp only [large_k_explicit_data, large_k_domain, Nat.card_sum,
    Nat.card_prod, Nat.card_fin, Nat.card_sigma]
  push_cast
  rw [← Finset.mul_sum]
  have hk_nonneg : (0 : ℝ) ≤ k := by positivity
  have hsum_real :
      (∑ i : Fin N, (tail_width_nat k (i.1 + 1) : ℝ)) ≤
        2 * tail_width_nat k N := by exact_mod_cast hsum N
  have hNwidth_real : (N : ℝ) ≤ tail_width_nat k N := by
    exact_mod_cast hNwidth
  nlinarith

@[blueprint "lem:greedy-run-teaches"
  (statement := /-- Let $C$ be a nonempty concept class. If $S$ is an output of a greedy run on
    $C$, then there exists $c\in C$ for which $S$ is a teaching set. -/)
  (proof := /-- Induct on the greedy run of \cref{def:greedy-run}. At termination, nonemptiness
    and subsingletonness identify the unique concept, for which the empty set teaches. At a
    recursive step, apply the induction hypothesis to the nonempty restricted class. A concept
    discarded at this step disagrees with the surviving concept on the selected set, whereas a
    surviving concept is distinguished by the recursively returned teaching set. The union of
    these two sets therefore teaches the surviving concept in the original class, as required
    by \cref{def:teaching-set}. -/)
  (title := /-- Greedy Outputs Are Teaching Sets -/)
  (latexEnv := "lemma")]
lemma greedy_run_teaches {X : Type*} {k : ℕ} {C : concept_class X} {S : Set X}
    (hC : C.Nonempty) (hrun : greedy_run k C S) :
    ∃ c : X → Bool, teaching_set C c S := by
  induction hrun with
  | terminate C hsub =>
      rcases hC with ⟨c, hc⟩
      refine ⟨c, hc, ?_⟩
      intro c' hc' hne
      exact (hne (hsub hc' hc)).elim
  | step C T b S hlow hhigh hne hmin htie hrec ih =>
      rcases ih hne with ⟨c, hc, hteach⟩
      refine ⟨c, hc.1, ?_⟩
      intro c' hc' hcc'
      by_cases hcR : c' ∈ restrict_class C (↑T) b
      · rcases hteach c' hcR hcc' with ⟨x, hxS, hx⟩
        exact ⟨x, Set.mem_union_right _ hxS, hx⟩
      · have hdiff : ∃ x ∈ T, c' x ≠ b x := by
          simp only [restrict_class, Set.mem_setOf_eq, hc', true_and] at hcR
          push Not at hcR
          simpa using hcR
        rcases hdiff with ⟨x, hxT, hx⟩
        exact ⟨x, Set.mem_union_left _ hxT, fun h => hx (h.trans (hc.2 x hxT))⟩

@[blueprint "lem:finite-greedy-run-exists"
  (statement := /-- Let $X$ be finite, let $C$ be a nonempty finite concept class on $X$, and
    let $k\geq1$. Then the greedy procedure with parameter $k$ has an output on $C$. -/)
  (proof := /-- Induct strongly on $|C|$. A subsingleton class terminates. Otherwise two
    concepts differ at some point, so a feasible singleton restriction is a proper nonempty
    subclass. Finiteness of the domain and of its Boolean labelings makes the set of feasible
    point-set--pattern pairs finite. Choose a pair minimizing first the restriction cardinality
    and then the point-set cardinality, encoded lexicographically with radix $k+1$. Its
    restriction is no larger than the proper singleton restriction and hence has smaller
    cardinality than $C$. Apply the induction hypothesis there and prepend the minimizing step
    of \cref{def:greedy-run}. -/)
  (title := /-- Existence of Greedy Runs on Finite Classes -/)
  (latexEnv := "lemma")]
lemma finite_greedy_run_exists {X : Type*} [Finite X] (k : ℕ) (hk : 1 ≤ k)
    (C : concept_class X) (hCfin : C.Finite) (hCne : C.Nonempty) :
    ∃ S : Set X, greedy_run k C S := by
  classical
  letI := Fintype.ofFinite X
  induction hcardEq : C.ncard using Nat.strong_induction_on generalizing C with
  | h m ih =>
      by_cases hsub : C.Subsingleton
      · exact ⟨∅, greedy_run.terminate C hsub⟩
      · have hpair : ∃ c₁ ∈ C, ∃ c₂ ∈ C, c₁ ≠ c₂ := by
          simpa [Set.Subsingleton] using hsub
        rcases hpair with ⟨c₁, hc₁, c₂, hc₂, hcne⟩
        have hpoint : ∃ x, c₁ x ≠ c₂ x := by
          simpa [Function.ne_iff] using hcne
        rcases hpoint with ⟨x, hx⟩
        let Q := (Finset.univ : Finset (Finset X × (X → Bool))).filter fun q =>
          1 ≤ q.1.card ∧ q.1.card ≤ k ∧
            (restrict_class C (↑q.1) q.2).Nonempty
        have hQ : Q.Nonempty := by
          refine ⟨({x}, c₁), ?_⟩
          simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and, Finset.card_singleton,
            le_refl, hk, restrict_class, Set.mem_setOf_eq]
          exact ⟨c₁, hc₁, by simp⟩
        let key : (Finset X × (X → Bool)) → ℕ := fun q =>
          (restrict_class C (↑q.1) q.2).ncard * (k + 1) + q.1.card
        rcases Finset.exists_min_image Q key hQ with ⟨q, hqQ, hqmin⟩
        have hq : 1 ≤ q.1.card ∧ q.1.card ≤ k ∧
            (restrict_class C (↑q.1) q.2).Nonempty := by
          simpa [Q] using hqQ
        let R := restrict_class C (↑q.1) q.2
        have hRfin : R.Finite := hCfin.subset fun _ h => h.1
        have hcandProper :
            (restrict_class C (↑({x} : Finset X)) c₁).ncard < C.ncard := by
          apply Set.ncard_lt_ncard
          · refine ⟨fun _ h => h.1, ?_⟩
            intro hback
            have hc₂R := hback hc₂
            exact hx (hc₂R.2 x (by simp)).symm
          · exact hCfin
        have hRle : R.ncard ≤
            (restrict_class C (↑({x} : Finset X)) c₁).ncard := by
          have hcandQ : (({x}, c₁) : Finset X × (X → Bool)) ∈ Q := by
            simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.card_singleton, le_refl, hk, restrict_class, Set.mem_setOf_eq]
            exact ⟨c₁, hc₁, by simp⟩
          have hm := hqmin ({x}, c₁) hcandQ
          dsimp [key, R] at hm ⊢
          simp only [Finset.card_singleton] at hm
          by_contra hle
          have hsucc : (restrict_class C (↑({x} : Finset X)) c₁).ncard + 1 ≤
              (restrict_class C (↑q.1) q.2).ncard := by omega
          have hmul := Nat.mul_le_mul_right (k + 1) hsucc
          have hmul' :
              (restrict_class C (↑({x} : Finset X)) c₁).ncard * (k + 1) + (k + 1) ≤
                (restrict_class C (↑q.1) q.2).ncard * (k + 1) := by
            simpa [Nat.add_mul] using hmul
          have hbig :
              (restrict_class C (↑({x} : Finset X)) c₁).ncard * (k + 1) + 1 <
                (restrict_class C (↑q.1) q.2).ncard * (k + 1) + q.1.card := by
            omega
          omega
        have hRlt : R.ncard < C.ncard := lt_of_le_of_lt hRle hcandProper
        have hRltN : R.ncard < m := by omega
        rcases ih R.ncard hRltN R hRfin hq.2.2 rfl with ⟨S, hS⟩
        refine ⟨(↑q.1 : Set X) ∪ S, greedy_run.step C q.1 q.2 S hq.1 hq.2.1 hq.2.2 ?_ ?_ hS⟩
        · intro T b hlow hhigh hne
          have hm := hqmin (T, b) (by simpa [Q] using And.intro hlow (And.intro hhigh hne))
          dsimp [key] at hm
          by_contra hle
          have hsucc : (restrict_class C (↑T) b).ncard + 1 ≤
              (restrict_class C (↑q.1) q.2).ncard := by omega
          have hmul := Nat.mul_le_mul_right (k + 1) hsucc
          have hmul' : (restrict_class C (↑T) b).ncard * (k + 1) + (k + 1) ≤
              (restrict_class C (↑q.1) q.2).ncard * (k + 1) := by
            simpa [Nat.add_mul] using hmul
          omega
        · intro T b hlow hhigh hne heq
          have hm := hqmin (T, b) (by simpa [Q] using And.intro hlow (And.intro hhigh hne))
          dsimp [key] at hm
          rw [heq] at hm
          omega

@[blueprint "lem:large-k-nonexceptional-restriction"
  (statement := /-- Let $i$ be a level of the explicit construction. A nonempty restriction of
    the union through level $i$ by at most $k$ points contains at least
    $(\widehat w_{i+1}+1)^k$ concepts unless its head part is the whole current head and its
    pattern is identically zero there. -/)
  (proof := /-- Split the selected points into their head and tail parts. A realizing concept
    supplies realizable head and tail patterns. Unless the stated exceptional pattern occurs,
    \cref{lem:head-set} extends the head pattern to level $i$, while \cref{lem:tail-set} gives at
    least $(\widehat w_{i+1}+1)^k$ level-$i$ tail concepts extending the tail pattern. Combining
    the fixed head extension with each tail extension embeds all of them into the original
    restriction; injectivity follows because head labelings vanish on the tail domain and tail
    labelings vanish on the head domain. Finiteness of the ambient union, needed to compare
    natural cardinalities under this embedding, follows from
    \cref{lem:domination-general-case}. -/)
  (title := /-- Multiplicity of Nonexceptional Restrictions -/)
  (latexEnv := "lemma")]
lemma large_k_nonexceptional_restriction (k N : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N)
    (i : Fin N) (T : Finset (large_k_explicit_data k N).X)
    (b : (large_k_explicit_data k N).X → Bool) (hcard : T.card ≤ k)
    (hne : (restrict_class (large_k_lower_level_class (large_k_explicit_data k N) i)
      (↑T) b).Nonempty)
    (hexception : ¬ (((↑T : Set (large_k_explicit_data k N).X) ∩
        large_k_head_domain (large_k_explicit_data k N)) =
          Set.range ((large_k_explicit_data k N).head_point i) ∧
      ∀ x ∈ T, x ∈ large_k_head_domain (large_k_explicit_data k N) → b x = false)) :
    (tail_width_nat k (i.1 + 1) + 1) ^ k ≤
      (restrict_class (large_k_lower_level_class (large_k_explicit_data k N) i)
        (↑T) b).ncard := by
  classical
  let E := large_k_explicit_data k N
  letI : Finite E.X := E.finite_X
  let TH := T.filter fun x => x ∈ large_k_head_domain E
  let TT := T.filter fun x => x ∉ large_k_head_domain E
  rcases hne with ⟨c, hcC, hcT⟩
  rcases Set.mem_iUnion.mp hcC with ⟨j, hcj⟩
  change c ∈ large_k_product_class (large_k_head_class k N j.1)
    (large_k_tail_class k N j.1) at hcj
  rcases hcj with ⟨a, ha, t, ht, hprod⟩
  have hTHcard : TH.card ≤ k := le_trans (Finset.card_filter_le _ _) hcard
  have hTTcard : TT.card ≤ k := le_trans (Finset.card_filter_le _ _) hcard
  have hTHdom : (↑TH : Set E.X) ⊆ large_k_head_domain E := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hTTdom : (↑TT : Set E.X) ⊆ large_k_tail_domain E := by
    intro x hx
    rcases E.domain_exhaustive x with hxH | hxT
    · exact ((Finset.mem_filter.mp hx).2 hxH).elim
    · exact hxT
  have hheadReal :
      (restrict_class (⋃ l : {l : Fin N // l ≤ i},
          (large_k_explicit_data k N).head_class l.1)
        (↑TH) b).Nonempty := by
    refine ⟨a, ?_, ?_⟩
    · exact Set.mem_iUnion.mpr ⟨j, ha⟩
    · intro x hx
      have hxT : x ∈ T := (Finset.mem_filter.mp hx).1
      have hcx := hcT x hxT
      rcases (Finset.mem_filter.mp hx).2 with ⟨l, q, rfl⟩
      rcases ht with ⟨p, rfl⟩
      rw [hprod] at hcx
      simpa [E, large_k_explicit_data, large_k_tail_labeling] using hcx
  have htailReal :
      (restrict_class (⋃ l : {l : Fin N // l ≤ i},
          (large_k_explicit_data k N).tail_class l.1)
        (↑TT) b).Nonempty := by
    refine ⟨t, ?_, ?_⟩
    · exact Set.mem_iUnion.mpr ⟨j, ht⟩
    · intro x hx
      have hxT : x ∈ T := (Finset.mem_filter.mp hx).1
      have hcx := hcT x hxT
      rcases E.domain_exhaustive x with hxH | ⟨l, r, q, rfl⟩
      · exact ((Finset.mem_filter.mp hx).2 hxH).elim
      · rcases ha with ⟨v, hv, rfl⟩
        rw [hprod] at hcx
        simpa [E, large_k_explicit_data, large_k_head_labeling] using hcx
  have hai := head_set k N hk hN i TH b hTHcard hTHdom hheadReal (by
    intro hbad
    apply hexception
    refine ⟨?_, ?_⟩
    · calc
        (↑T : Set E.X) ∩ large_k_head_domain E = (↑TH : Set E.X) := by
          ext x
          simp [TH]
        _ = Set.range (E.head_point i) := hbad.1
    · intro x hxT hxH
      exact hbad.2 x (Finset.mem_filter.mpr ⟨hxT, hxH⟩))
  have htail := tail_set k N hk hN i TT b hTTcard hTTdom htailReal
  rcases hai with ⟨ai, haiC, haiT⟩
  let R := restrict_class (E.tail_class i) (↑TT) b
  let f : (E.X → Bool) → (E.X → Bool) :=
    fun u x => ai x || u x
  have hfsub : f '' R ⊆ restrict_class
      (large_k_lower_level_class (large_k_explicit_data k N) i) (↑T) b := by
    rintro d ⟨u, hu, rfl⟩
    refine ⟨Set.mem_iUnion.mpr ⟨⟨i, le_rfl⟩, ⟨ai, haiC, u, hu.1, fun _ => rfl⟩⟩, ?_⟩
    intro x hx
    by_cases hxH : x ∈ large_k_head_domain E
    · have hxTH : x ∈ TH := Finset.mem_filter.mpr ⟨hx, hxH⟩
      rcases hu.1 with ⟨p, rfl⟩
      rcases hxH with ⟨l, q, rfl⟩
      simpa [E, f, large_k_explicit_data, large_k_tail_labeling] using
        haiT (E.head_point l q) hxTH
    · have hxTT : x ∈ TT := Finset.mem_filter.mpr ⟨hx, hxH⟩
      rcases haiC with ⟨v, hv, rfl⟩
      rcases E.domain_exhaustive x with hxH' | ⟨l, r, q, rfl⟩
      · exact (hxH hxH').elim
      · simpa [E, f, large_k_explicit_data, large_k_head_labeling] using
          hu.2 (E.tail_point l r q) hxTT
  have hfin : (restrict_class
      (large_k_lower_level_class (large_k_explicit_data k N) i) (↑T) b).Finite :=
    ((domination_general_case k N hk hN i).1.subset (by
      intro x hx
      exact hx.1))
  have hfinj : Set.InjOn f R := by
    intro u₁ hu₁ u₂ hu₂ heq
    funext x
    rcases E.domain_exhaustive x with ⟨l, q, rfl⟩ | ⟨l, r, q, rfl⟩
    · rcases hu₁.1 with ⟨p₁, rfl⟩
      rcases hu₂.1 with ⟨p₂, rfl⟩
      simp [E, large_k_explicit_data, large_k_tail_labeling]
    · rcases haiC with ⟨v, hv, rfl⟩
      simpa [E, f, large_k_explicit_data, large_k_head_labeling] using
        congrFun heq (E.tail_point l r q)
  calc
    (tail_width_nat k (i.1 + 1) + 1) ^ k ≤ R.ncard := htail
    _ = (f '' R).ncard := hfinj.ncard_image.symm
    _ ≤ (restrict_class
      (large_k_lower_level_class (large_k_explicit_data k N) i) (↑T) b).ncard :=
      Set.ncard_le_ncard hfsub hfin

@[blueprint "lem:large-k-bottom-teaching-bound"
  (statement := /-- At the bottom level of the explicit construction, every teaching set for
    a concept in the level class contains at least $k$ tail points. -/)
  (proof := /-- Fix the taught concept and its independently chosen tail prefix in each of the
    $2k$ rows. For every row, change only that row's prefix to a distinct value, keeping the
    head labeling and every other tail prefix fixed. This gives another bottom-level concept.
    The teaching property from \cref{def:teaching-set} supplies a selected point distinguishing
    the two concepts. By \cref{def:large-k-tail-labeling}, such a point must lie in the changed
    row. Choosing one witness from every row gives an injection of the $2k$ rows into the
    teaching set, and hence the asserted weaker bound $k$. -/)
  (title := /-- Bottom-Level Teaching Sets Meet Every Tail Row -/)
  (latexEnv := "lemma")]
lemma large_k_bottom_teaching_bound (k N : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N)
    (i : Fin N) (hi : i.1 = 0) (c : (large_k_explicit_data k N).X → Bool)
    (S : Set (large_k_explicit_data k N).X)
    (hteach : teaching_set
      (large_k_lower_level_class (large_k_explicit_data k N) i) c S) :
    k ≤ (S ∩ large_k_tail_domain (large_k_explicit_data k N)).ncard := by
  classical
  let E := large_k_explicit_data k N
  letI : Finite E.X := E.finite_X
  rcases Set.mem_iUnion.mp hteach.1 with ⟨j, hcj⟩
  have hj : j.1 = i := by
    apply Fin.ext
    omega
  rw [hj] at hcj
  change c ∈ large_k_product_class (large_k_head_class k N i)
    (large_k_tail_class k N i) at hcj
  rcases hcj with ⟨a, ha, t, ht, hprod⟩
  rcases ht with ⟨p, rfl⟩
  have hwpos : 0 < tail_width_nat k (i.1 + 1) := by
    unfold tail_width_nat
    positivity
  have hw : 1 < tail_width_nat k (i.1 + 1) + 1 := by omega
  have hrow : ∀ r : Fin (2 * k), ∃ x ∈ S, ∃ l : Fin N,
      ∃ q : Fin (tail_width_nat k (l.1 + 1)), x = E.tail_point l r q := by
    intro r
    let pr : Fin (tail_width_nat k (i.1 + 1) + 1) :=
      if h : (p r).1 = 0 then ⟨1, hw⟩ else ⟨0, by omega⟩
    have hpr : pr ≠ p r := by
      intro heq
      have hv := congrArg Fin.val heq
      by_cases hp0 : (p r).1 = 0
      · have : (1 : ℕ) = 0 := by simpa [pr, hp0] using hv
        omega
      · apply hp0
        symm
        simpa [pr, hp0] using hv
    let p' := Function.update p r pr
    let t' := large_k_tail_labeling k N i p'
    let c' : E.X → Bool := fun x => a x || t' x
    have hc'C : c' ∈ large_k_lower_level_class E i := by
      exact Set.mem_iUnion.mpr ⟨⟨i, le_rfl⟩,
        ⟨a, ha, t', ⟨p', rfl⟩, fun _ => rfl⟩⟩
    have hcc' : c' ≠ c := by
      intro heq
      have hv := congrFun heq
        (E.tail_point i r ⟨0, by unfold tail_width_nat; positivity⟩)
      rw [hprod] at hv
      simp only [c', t'] at hv
      rcases ha with ⟨v, hvad, rfl⟩
      by_cases hp0 : (p r).1 = 0
      · simp [E, large_k_explicit_data, large_k_head_labeling,
          large_k_tail_labeling, p', pr, hp0, hi] at hv
      · have hp0' : 0 < (p r).1 := Nat.pos_of_ne_zero hp0
        simp [E, large_k_explicit_data, large_k_head_labeling,
          large_k_tail_labeling, p', pr, hp0, hp0', hi] at hv
    rcases hteach.2 c' hc'C hcc' with ⟨x, hxS, hdiff⟩
    refine ⟨x, hxS, ?_⟩
    rcases E.domain_exhaustive x with ⟨l, q, rfl⟩ | ⟨l, r', q, rfl⟩
    · exfalso
      rw [hprod] at hdiff
      rcases ha with ⟨v, hvad, rfl⟩
      simp [c', t', E, large_k_explicit_data, large_k_head_labeling,
        large_k_tail_labeling] at hdiff
    · by_cases hrr : r' = r
      · subst r'
        exact ⟨l, q, rfl⟩
      · exfalso
        rw [hprod] at hdiff
        rcases ha with ⟨v, hvad, rfl⟩
        simp [c', t', p', hrr, E, large_k_explicit_data,
          large_k_head_labeling, large_k_tail_labeling] at hdiff
  choose f hfS l q hf using hrow
  have hfinj : Function.Injective f := by
    intro r₁ r₂ heq
    rw [hf r₁, hf r₂] at heq
    exact congrArg (fun x => x.2.1) (Sum.inr.inj heq)
  have hrange : Set.range f ⊆ S ∩ large_k_tail_domain E := by
    rintro x ⟨r, rfl⟩
    refine ⟨hfS r, ?_⟩
    exact ⟨l r, r, q r, hf r⟩
  calc
    k ≤ 2 * k := by omega
    _ = (Set.range f).ncard := by
      rw [Set.ncard_range_of_injective hfinj]
      simp
    _ ≤ (S ∩ large_k_tail_domain E).ncard := Set.ncard_le_ncard hrange

@[blueprint "lem:large-k-lower-level-nonempty"
  (statement := /-- Every union of the explicit level classes through a level $i$ is
    nonempty when $k\geq2$. -/)
  (proof := /-- Choose the first head coordinate at every level through $i$ and the zero vector
    above $i$. This sequence has a single possible transition, bounded by
    \cref{lem:head-change-count-le-of-sources}, and hence is admissible. Combine its head
    labeling with the all-zero choice of tail prefixes to obtain a concept at level $i$, which
    belongs to the union through $i$. -/)
  (title := /-- Nonemptiness of Lower-Level Unions -/)
  (latexEnv := "lemma")]
lemma large_k_lower_level_nonempty (k N : ℕ) (hk : 2 ≤ k) (i : Fin N) :
    (large_k_lower_level_class (large_k_explicit_data k N) i).Nonempty := by
  classical
  let a0 : Fin k := ⟨0, by omega⟩
  let v : Fin N → Option (Fin k) := fun j => if j ≤ i then some a0 else none
  have hv : large_k_head_admissible i v := by
    refine ⟨?_, ?_, ?_⟩
    · intro j hij
      simp [v, not_le.mpr hij]
    · simp [v, a0]
    · refine le_trans (head_change_count_le_of_sources v {i} ?_) (by simp; omega)
      intro p q hpq hpneq
      simp only [Finset.mem_singleton]
      by_contra hpi
      have hlt : p < i ∨ i < p := lt_or_gt_of_ne hpi
      rcases hlt with hpi' | hip
      · have hqi : q ≤ i := by
          apply Fin.le_iff_val_le_val.mpr
          omega
        simp [v, le_of_lt hpi', hqi] at hpneq
      · have hiq : i < q := by
          apply Fin.lt_iff_val_lt_val.mpr
          omega
        simp [v, not_le.mpr hip, not_le.mpr hiq] at hpneq
  let a := large_k_head_labeling v
  let p : Fin (2 * k) → Fin (tail_width_nat k (i.1 + 1) + 1) := fun _ => 0
  let t := large_k_tail_labeling k N i p
  let c : (large_k_explicit_data k N).X → Bool := fun x => a x || t x
  refine ⟨c, Set.mem_iUnion.mpr ⟨⟨i, le_rfl⟩, ?_⟩⟩
  exact ⟨a, ⟨v, hv, rfl⟩, t, ⟨p, rfl⟩, fun _ => rfl⟩

@[blueprint "lem:large-k-greedy-structure"
  (statement := /-- For a greedy run on the union through level $i$, its output contains every
    positive-level head through $i$ and contains at least $k$ tail points. -/)
  (proof := /-- Induct on $i$. At level zero, \cref{lem:greedy-run-teaches} turns the run into a
    teaching set, and \cref{lem:large-k-bottom-teaching-bound} supplies the tail points. For a
    positive level, the all-zero restriction on its full head is exactly the union through the
    preceding level. Its size is below the current threshold by
    \cref{lem:domination-general-case}. Every nonexceptional feasible restriction is at least
    that threshold by \cref{lem:large-k-nonexceptional-restriction}; hence minimization forces
    the full current head with the zero pattern. The recursive run is therefore on the preceding
    union, to which the induction hypothesis applies. Nonemptiness used throughout is
    \cref{lem:large-k-lower-level-nonempty}. -/)
  (title := /-- Structure Forced on Greedy Outputs -/)
  (latexEnv := "lemma")]
lemma large_k_greedy_structure (k N : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N)
    (i : Fin N) (S : Set (large_k_explicit_data k N).X)
    (hrun : greedy_run k (large_k_lower_level_class (large_k_explicit_data k N) i) S) :
    k ≤ (S ∩ large_k_tail_domain (large_k_explicit_data k N)).ncard ∧
      ∀ l : Fin N, 0 < l.1 → l ≤ i →
        Set.range ((large_k_explicit_data k N).head_point l) ⊆ S := by
  classical
  let E := large_k_explicit_data k N
  letI : Finite E.X := E.finite_X
  induction hi : i.1 using Nat.strong_induction_on generalizing i S with
  | h m ih =>
      by_cases hi0 : i.1 = 0
      · have hne := large_k_lower_level_nonempty k N hk i
        rcases greedy_run_teaches hne hrun with ⟨c, hc⟩
        refine ⟨large_k_bottom_teaching_bound k N hk hN i hi0 c S hc, ?_⟩
        intro l hl hli
        omega
      · let p : Fin N := ⟨i.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.2⟩
        have hp : p.1 + 1 = i.1 := by dsimp [p]; omega
        let H : Finset E.X := Finset.univ.image (E.head_point i)
        let z : E.X → Bool := fun _ => false
        have hHcard : H.card = k := by
          rw [Finset.card_image_of_injective]
          · simp
          · intro a b hab
            simpa [H, E, large_k_explicit_data] using hab
        have hrestrict : restrict_class (large_k_lower_level_class E i) (↑H) z =
            large_k_lower_level_class E p := by
          ext c
          constructor
          · rintro ⟨hc, hcz⟩
            rcases Set.mem_iUnion.mp hc with ⟨j, hcj⟩
            have hji : j.1.1 < i.1 := by
              by_contra hn
              have hEq : j.1 = i := Fin.ext (by omega)
              rw [hEq] at hcj
              change c ∈ large_k_product_class (large_k_head_class k N i)
                (large_k_tail_class k N i) at hcj
              rcases hcj with ⟨a, ha, t, ht, hprod⟩
              rcases ha with ⟨v, hv, rfl⟩
              rcases Option.isSome_iff_exists.mp hv.2.1 with ⟨q, hq⟩
              have hxH : E.head_point i q ∈ H := by simp [H]
              have hz := hcz (E.head_point i q) hxH
              rcases ht with ⟨u, rfl⟩
              rw [hprod] at hz
              simp [z, E, large_k_explicit_data, large_k_head_labeling,
                large_k_tail_labeling, hq] at hz
            exact Set.mem_iUnion.mpr ⟨⟨j.1, by dsimp [p]; omega⟩, hcj⟩
          · intro hc
            rcases Set.mem_iUnion.mp hc with ⟨j, hcj⟩
            refine ⟨Set.mem_iUnion.mpr ⟨⟨j.1, by dsimp [p] at j; omega⟩, hcj⟩, ?_⟩
            intro x hx
            rcases Finset.mem_image.mp hx with ⟨q, -, rfl⟩
            change c (E.head_point i q) = false
            change c ∈ large_k_product_class (large_k_head_class k N j.1)
              (large_k_tail_class k N j.1) at hcj
            rcases hcj with ⟨a, ha, t, ht, hprod⟩
            rw [hprod]
            rcases ha with ⟨v, hv, rfl⟩
            rcases ht with ⟨u, rfl⟩
            have hji : j.1 < i := by apply Fin.lt_iff_val_lt_val.mpr; dsimp [p] at j; omega
            simp [z, E, large_k_explicit_data, large_k_head_labeling,
              large_k_tail_labeling, hv.1 i hji]
        cases hrun with
        | terminate C hsub =>
            have hne := large_k_lower_level_nonempty k N hk i
            have hnc : (large_k_lower_level_class
                (large_k_explicit_data k N) i).ncard ≤ 1 := by
              exact (Set.ncard_le_one (domination_general_case k N hk hN i).1).2 hsub
            have hlower := large_k_nonexceptional_restriction k N hk hN i ∅ z
              (by simp) (by simpa [restrict_class] using hne) (by
                intro hbad
                have hrange : (Set.range (E.head_point i)).Nonempty :=
                  ⟨E.head_point i ⟨0, by omega⟩, Set.mem_range_self _⟩
                rw [← hbad.1] at hrange
                simpa using hrange)
            have hw : 2 ≤ (tail_width_nat k (i.1 + 1) + 1) ^ k := by
              have : 2 ≤ tail_width_nat k (i.1 + 1) + 1 := by
                have : 0 < tail_width_nat k (i.1 + 1) := by
                  unfold tail_width_nat
                  positivity
                omega
              exact le_trans this (Nat.le_pow (by omega))
            have hempty : restrict_class
                (large_k_lower_level_class (large_k_explicit_data k N) i) (↑(∅ : Finset E.X)) z =
                large_k_lower_level_class (large_k_explicit_data k N) i := by
              ext c
              simp [restrict_class]
            rw [hempty] at hlower
            omega
        | step C T b S hlow hhigh hne hmin htie hrec =>
            have hpne := large_k_lower_level_nonempty k N hk p
            have hcandNe : (restrict_class
                (large_k_lower_level_class (large_k_explicit_data k N) i) (↑H) z).Nonempty := by
              rw [hrestrict]
              exact hpne
            have hlowerEq :
                (⋃ j : {j : Fin N // j < i}, E.level_class j.1) =
                  large_k_lower_level_class E p := by
              change (⋃ j : {j : Fin N // j < i}, E.level_class j.1) =
                ⋃ j : {j : Fin N // j ≤ p}, E.level_class j.1
              ext c
              simp only [Set.mem_iUnion]
              constructor
              · rintro ⟨j, hj⟩
                exact ⟨⟨j.1, by dsimp [p]; omega⟩, hj⟩
              · rintro ⟨j, hj⟩
                exact ⟨⟨j.1, by dsimp [p] at j; omega⟩, hj⟩
            have hselLt : (restrict_class
                (large_k_lower_level_class (large_k_explicit_data k N) i) (↑T) b).ncard <
                (tail_width_nat k (i.1 + 1) + 1) ^ k :=
              lt_of_le_of_lt (hmin H z (by rw [hHcard]; omega) (by rw [hHcard]) hcandNe)
                (by rw [hrestrict, ← hlowerEq]
                    exact (domination_general_case k N hk hN i).2.2 (by omega))
            have hex : ((↑T : Set E.X) ∩ large_k_head_domain E) =
                  Set.range (E.head_point i) ∧
                ∀ x ∈ T, x ∈ large_k_head_domain E → b x = false := by
              by_contra hn
              have hlower := large_k_nonexceptional_restriction k N hk hN i T b
                hhigh hne hn
              omega
            have hHT : H ⊆ T := by
              intro x hx
              rcases Finset.mem_image.mp hx with ⟨q, -, rfl⟩
              have : E.head_point i q ∈ (↑T : Set E.X) ∩ large_k_head_domain E := by
                rw [hex.1]
                exact Set.mem_range_self q
              exact this.1
            have hTH : T = H := by
              exact (Finset.eq_of_subset_of_card_le hHT (by rw [hHcard]; exact hhigh)).symm
            subst T
            have hbH : ∀ x ∈ H, b x = z x := by
              intro x hx
              exact hex.2 x hx (by
                rcases Finset.mem_image.mp hx with ⟨q, -, rfl⟩
                exact ⟨i, q, rfl⟩)
            have hRb : restrict_class
                (large_k_lower_level_class (large_k_explicit_data k N) i) (↑H) b =
              restrict_class (large_k_lower_level_class (large_k_explicit_data k N) i)
                (↑H) z := by
              ext c
              simp only [restrict_class, Set.mem_setOf_eq]
              constructor <;> rintro ⟨hc, hh⟩ <;> refine ⟨hc, ?_⟩ <;>
                intro x hx
              · exact (hh x hx).trans (hbH x hx)
              · exact (hh x hx).trans (hbH x hx).symm
            rw [hRb, hrestrict] at hrec
            have hpm : p.1 < m := by dsimp [p]; omega
            rcases ih p.1 hpm p S hrec rfl with ⟨htail, hheads⟩
            refine ⟨?_, ?_⟩
            · exact le_trans htail (Set.ncard_le_ncard (by
                intro x hx
                exact ⟨Set.mem_union_right _ hx.1, hx.2⟩))
            · intro l hl hli x hx
              by_cases hliEq : l = i
              · subst l
                exact Set.mem_union_left _ (by simpa [H] using hx)
              · exact Set.mem_union_right _ (hheads l hl (by
                  apply Fin.le_iff_val_le_val.mpr
                  dsimp [p]
                  omega) hx)

@[blueprint "lem:large-k-greedy-forcing"
  (statement := /-- Let $k,N\in\mathbb N$ satisfy $k\geq2$ and $N\geq1$, and let $D$ be a
    verified large-$k$ construction. There exists a set $S\subseteq D.\mathrm{data}.X$ such that
    $S$ is a possible output of $\textsc{Greedy}(D.\mathrm{data}.\mathrm{family},k)$ in the sense
    of \cref{def:greedy-run}; moreover, every possible output $S$ satisfies $|S|\geq kN$. -/)
  (proof := /-- Identify the verified datum with the explicit construction and its family with
    the union through level $N-1$. This union is nonempty by
    \cref{lem:large-k-lower-level-nonempty} and finite by
    \cref{lem:domination-general-case}. Hence \cref{lem:finite-greedy-run-exists} supplies at
    least one greedy output. For an arbitrary output, apply
    \cref{lem:large-k-greedy-structure}: it contains the full $k$-point head at every positive
    level and at least $k$ tail points. The positive-level heads are pairwise disjoint, are
    disjoint from the tail domain, and together have cardinality $k(N-1)$. Their union with the
    selected tail points is a subset of the returned set and has cardinality
    $k(N-1)+k=kN$, proving the required lower bound for every run. -/)
  (title := /-- Greedy Output Existence and Lower Bound -/)
  (latexEnv := "lemma")]
lemma large_k_greedy_forcing (k N : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N)
    (D : large_k_construction k N) :
    (∃ S : Set D.data.X, greedy_run k D.data.family S) ∧
      ∀ S : Set D.data.X, greedy_run k D.data.family S → k * N ≤ S.ncard := by
  classical
  rw [D.data_eq]
  let E := large_k_explicit_data k N
  let i : Fin N := ⟨N - 1, by omega⟩
  have hfamily : E.family = large_k_lower_level_class E i := by
    change (⋃ j : Fin N, E.level_class j) =
      ⋃ j : {j : Fin N // j ≤ i}, E.level_class j.1
    ext c
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨⟨j, by
        apply Fin.le_iff_val_le_val.mpr
        dsimp [i]
        exact Nat.le_sub_one_of_lt j.2⟩, hj⟩
    · rintro ⟨j, hj⟩
      exact ⟨j.1, hj⟩
  have hne : E.family.Nonempty := by
    rw [hfamily]
    exact large_k_lower_level_nonempty k N hk i
  letI : Finite E.X := E.finite_X
  constructor
  · exact finite_greedy_run_exists k (by omega) E.family
      (by rw [hfamily]; exact (domination_general_case k N hk hN i).1) hne
  · intro S hrun
    rw [hfamily] at hrun
    rcases large_k_greedy_structure k N hk hN i S hrun with ⟨htail, hheads⟩
    let f : Fin (N - 1) × Fin k → E.X := fun q =>
      E.head_point ⟨q.1.1 + 1, by omega⟩ q.2
    have hfinj : Function.Injective f := by
      intro a b hab
      have hab' : (a.1.1 + 1, a.2) = (b.1.1 + 1, b.2) := by
        simpa [f, E, large_k_explicit_data] using hab
      have h₁ : a.1 = b.1 := Fin.ext (by
        have := congrArg Prod.fst hab'
        omega)
      have h₂ : a.2 = b.2 := congrArg (fun q : ℕ × Fin k => q.2) hab'
      exact Prod.ext h₁ h₂
    have hfrange : Set.range f ⊆ S := by
      rintro x ⟨q, rfl⟩
      apply hheads ⟨q.1.1 + 1, by omega⟩ (by simp) (by
        apply Fin.le_iff_val_le_val.mpr
        dsimp [i]
        omega)
      exact Set.mem_range_self q.2
    have hdisj : Disjoint
        (S ∩ large_k_tail_domain (large_k_explicit_data k N)) (Set.range f) := by
      rw [Set.disjoint_left]
      intro x hxT hxH
      rcases hxT.2 with ⟨l, r, q, hx⟩
      rcases hxH with ⟨a, ha⟩
      rw [hx] at ha
      simp [f, E, large_k_explicit_data] at ha
    have hunion :
        (S ∩ large_k_tail_domain (large_k_explicit_data k N)) ∪ Set.range f ⊆ S := by
      intro x hx
      rcases hx with hx | hx
      · exact hx.1
      · exact hfrange hx
    have hrangeCard : (Set.range f).ncard = (N - 1) * k := by
      rw [Set.ncard_range_of_injective hfinj]
      simp
    have hcardUnion :
        ((S ∩ large_k_tail_domain (large_k_explicit_data k N)) ∪ Set.range f).ncard =
          (S ∩ large_k_tail_domain (large_k_explicit_data k N)).ncard + (N - 1) * k := by
      rw [Set.ncard_union_eq hdisj, hrangeCard]
    calc
      k * N = k + (N - 1) * k := by
        calc
          k * N = k * (1 + (N - 1)) := by congr 1; omega
          _ = k + (N - 1) * k := by ring
      _ ≤ (S ∩ large_k_tail_domain (large_k_explicit_data k N)).ncard + (N - 1) * k :=
        Nat.add_le_add_right htail _
      _ = ((S ∩ large_k_tail_domain (large_k_explicit_data k N)) ∪ Set.range f).ncard :=
        hcardUnion.symm
      _ ≤ S.ncard := Set.ncard_le_ncard hunion

@[blueprint "thm:general-k-lower-bound"
  (statement := /-- For every integer $k \ge 2$ there exists a family $\{\mcF_N\}_{N \ge 1}$ of
    concept classes, where each $\mcF_N$ is a finite concept class defined on a finite domain
    $\mcX_N$, such that for every $N \ge 1$:
    \begin{enumerate}
      \item $\mathrm{VCdim}(\mcF_N) \le 4k+1$ (\cref{def:vc-dim});
      \item $|\mcF_N| \le w_N^{4k} = 2^{4k\log(8k)\cdot 2^{2N}}$ and
        $|\mcX_N| \le 6k\, w_N = 6k \cdot 2^{\log(8k)\cdot 2^{2N}}$, where $w_N$ is the tail width
        of \cref{def:tail-width}, and both cardinalities are those of the finite sets $\mcF_N$ and
        $\mcX_N$;
      \item there exists at least one set $S\subseteq\mcX_N$ satisfying
        $\textsc{Greedy}(\mcF_N,k)$ in the sense of \cref{def:greedy-run}, and every such set
        satisfies $|S|\geq kN$.
    \end{enumerate} -/)
  (proof := /-- Fix $k\geq2$. For every $N\in\mathbb N$, take $\mcX_N$ and $\mcF_N$ to be
    the domain and family of the explicit datum in \cref{def:large-k-explicit-data}; its
    finiteness field supplies a finite structure on $\mcX_N$. Now fix $N\geq1$ and choose a
    verified construction by \cref{lem:large-k-construction-exists}. Its equality field from
    \cref{def:large-k-construction} identifies its datum with the explicit datum. After
    transporting along this equality, finiteness, the VC bound, the family-cardinality bound,
    and the domain-cardinality bound follow respectively from
    \cref{lem:large-k-family-finite}, \cref{lem:large-k-vc-bound},
    \cref{lem:large-k-family-card-bound}, and \cref{lem:large-k-domain-card-bound}. Finally,
    \cref{lem:large-k-greedy-forcing} gives both the existence of a possible greedy output and
    the lower bound $|S|\geq kN$ for every possible output. -/)
  (title := /-- Lower Bound for $k \ge 2$ -/)
  (latexEnv := "theorem")]
theorem general_k_lower_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ (X : ℕ → Type) (_ : ∀ N : ℕ, Finite (X N)) (F : ∀ N : ℕ, concept_class (X N)),
      ∀ N : ℕ, 1 ≤ N →
        (F N).Finite ∧
        vc_dim (F N) ≤ 4 * k + 1 ∧
        ((F N).ncard : ℝ) ≤ tail_width k N ^ (4 * k) ∧
        (Nat.card (X N) : ℝ) ≤ 6 * (k : ℝ) * tail_width k N ∧
        (∃ S : Set (X N), greedy_run k (F N) S) ∧
        (∀ S : Set (X N), greedy_run k (F N) S → k * N ≤ S.ncard) := by
  classical
  refine ⟨(fun N => (large_k_explicit_data k N).X),
    (fun N => (large_k_explicit_data k N).finite_X),
    (fun N => (large_k_explicit_data k N).family), ?_⟩
  intro N hN
  let D := Classical.choice (large_k_construction_exists k N hk hN)
  have hfinite := large_k_family_finite k N hk hN D
  have hvc := large_k_vc_bound k N hk hN D
  have hfamily := large_k_family_card_bound k N hk hN D
  have hdomain := large_k_domain_card_bound k N hk hN D
  have hgreedy := large_k_greedy_forcing k N hk hN D
  rw [D.data_eq] at hfinite hvc hfamily hdomain hgreedy
  exact ⟨hfinite, hvc, hfamily, hdomain, hgreedy⟩

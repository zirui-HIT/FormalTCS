import Architect
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Sum

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:online_ov_vector"
  (statement := /-- For a natural number $d$, an online orthogonal-vectors input is a Boolean vector indexed by the coordinate set $\{0,\ldots,d-1\}$. -/)
  (title := /-- Boolean vectors -/)
  (latexEnv := "definition")]
abbrev online_ov_vector (d : ℕ) := Fin d → Bool

@[blueprint "def:online_ov_dot_product_on"
  (statement := /-- If $C$ is a finite set of coordinates and $x,q\in\{0,1\}^d$, their dot product on $C$ is the sum of the products of their Boolean coordinates, regarded as natural numbers. -/)
  (title := /-- Restricted Boolean dot product -/)
  (latexEnv := "definition")]
def online_ov_dot_product_on {d : ℕ} (C : Finset (Fin d))
    (x q : online_ov_vector d) : ℕ :=
  ∑ j ∈ C, (x j).toNat * (q j).toNat

@[blueprint "def:online_ov_orthogonal"
  (statement := /-- Two Boolean vectors $x,q\in\{0,1\}^d$ are orthogonal when their dot product over all $d$ coordinates is zero. -/)
  (title := /-- Orthogonality of Boolean vectors -/)
  (latexEnv := "definition")]
def online_ov_orthogonal {d : ℕ} (x q : online_ov_vector d) : Prop :=
  online_ov_dot_product_on Finset.univ x q = 0

@[blueprint "def:deterministic_online_ov_algorithms"
  (statement := /-- A cost-accounted deterministic online orthogonal-vectors algorithm on $n$ vectors of dimension $d$ consists of a state type with an injective finite Boolean encoding, a preprocessing computation returning its state and charged running time, and a query computation returning its Boolean answer and charged running time. -/)
  (title := /-- Deterministic online orthogonal-vectors algorithms -/)
  (latexEnv := "definition")]
structure deterministic_online_ov_algorithms (n d : ℕ) where
  State : Type
  encodeState : State → List Bool
  encodeState_injective : Function.Injective encodeState
  preprocess : (Fin n → online_ov_vector d) → State × ℕ
  query : State → online_ov_vector d → Bool × ℕ

@[blueprint "def:solves_online_ov"
  (statement := /-- A deterministic pair solves $\OnlineOV_{n,d}$ if, for every database $X$ of $n$ Boolean vectors and every query $q$, its answer is true exactly when some vector of $X$ is orthogonal to $q$. -/)
  (title := /-- Correctness for online orthogonal vectors -/)
  (latexEnv := "definition")]
def solves_online_ov {n d : ℕ} (A : deterministic_online_ov_algorithms n d) : Prop :=
  ∀ (X : Fin n → online_ov_vector d) (q : online_ov_vector d),
    (A.query (A.preprocess X).1 q).1 = true ↔
      ∃ j : Fin n, online_ov_orthogonal (X j) q

@[blueprint "def:partial_binomial_sum"
  (statement := /-- For natural numbers $d$ and $t$, set $\binom{d}{\leq t}:=\sum_{j=0}^{t}\binom{d}{j}$. -/)
  (title := /-- Partial binomial sum -/)
  (latexEnv := "definition")]
def partial_binomial_sum (d t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (t + 1), Nat.choose d j

@[blueprint "def:online_ov_query_bound"
  (statement := /-- The claimed query bound for parameters $(n,d,i)$ is $2id\,n^{1-1/i}$, interpreted in the real numbers. -/)
  (title := /-- Claimed query bound -/)
  (latexEnv := "definition")]
noncomputable def online_ov_query_bound (n d i : ℕ) : ℝ :=
  2 * (i : ℝ) * (d : ℝ) * (n : ℝ) ^ (1 - 1 / (i : ℝ))

@[blueprint "def:online_ov_space_bound"
  (statement := /-- The claimed space bound for parameters $(n,d,i)$ is $\binom{d}{\leq d/i}id\,n^{1-1/i}$, where the partial binomial sum uses natural-number division in its cutoff. -/)
  (title := /-- Claimed space bound -/)
  (latexEnv := "definition")]
noncomputable def online_ov_space_bound (n d i : ℕ) : ℝ :=
  (partial_binomial_sum d (d / i) : ℝ) * (i : ℝ) * (d : ℝ) *
    (n : ℝ) ^ (1 - 1 / (i : ℝ))

@[blueprint "def:online_ov_preprocessing_bound"
  (statement := /-- The claimed preprocessing bound for parameters $(n,d,i)$ is $\binom{d}{\leq d/i}idn$. -/)
  (title := /-- Claimed preprocessing bound -/)
  (latexEnv := "definition")]
def online_ov_preprocessing_bound (n d i : ℕ) : ℝ :=
  (partial_binomial_sum d (d / i) : ℝ) * (i : ℝ) * (d : ℝ) * (n : ℝ)

@[blueprint "def:bounded_online_ov_data_structure"
  (statement := /-- A cost-accounted algorithm $A$ is a bounded data structure for parameters $(n,d,i)$ if it solves $\OnlineOV_{n,d}$, every charged query execution is within the claimed query bound, every preprocessed state has an injective Boolean encoding within the claimed space bound, and every charged preprocessing execution is within the claimed preprocessing bound. -/)
  (title := /-- Bounds for a specified online orthogonal-vectors algorithm -/)
  (latexEnv := "definition")]
def bounded_online_ov_data_structure
    (n d i : ℕ) (A : deterministic_online_ov_algorithms n d) : Prop :=
  solves_online_ov A ∧
    (∀ (X : Fin n → online_ov_vector d) (q : online_ov_vector d),
      ((A.query (A.preprocess X).1 q).2 : ℝ) ≤ online_ov_query_bound n d i) ∧
    (∀ X : Fin n → online_ov_vector d,
      ((A.encodeState (A.preprocess X).1).length : ℝ) ≤ online_ov_space_bound n d i) ∧
    (∀ X : Fin n → online_ov_vector d,
      ((A.preprocess X).2 : ℝ) ≤ online_ov_preprocessing_bound n d i)

@[blueprint "def:has_bounded_online_ov_data_structure"
  (statement := /-- The parameters $(n,d,i)$ admit the claimed data structure if some specified cost-accounted deterministic algorithm is a bounded online orthogonal-vectors data structure for these parameters. -/)
  (title := /-- Existence of a bounded online orthogonal-vectors algorithm -/)
  (latexEnv := "definition")]
def has_bounded_online_ov_data_structure (n d i : ℕ) : Prop :=
  ∃ A : deterministic_online_ov_algorithms n d,
    bounded_online_ov_data_structure n d i A

@[blueprint "def:common_zero_coordinates"
  (statement := /-- A Boolean vector $x$ vanishes on a coordinate set $C$ if $x_j=0$ for every $j\in C$. -/)
  (title := /-- Common zero coordinates -/)
  (latexEnv := "definition")]
def common_zero_coordinates {d : ℕ} (x : online_ov_vector d)
    (C : Finset (Fin d)) : Prop :=
  ∀ j ∈ C, x j = false

@[blueprint "def:pseudorandom_vector_family"
  (statement := /-- A finite family $X\subseteq\{0,1\}^d$ is $(m,t)$-pseudorandom if every $m$-element subfamily $Y\subseteq X$ and every $t$-element coordinate set $C$ contain a vector of $Y$ which does not vanish identically on $C$. -/)
  (title := /-- Pseudorandom vector families -/)
  (latexEnv := "definition")]
def pseudorandom_vector_family {d : ℕ} (X : Finset (online_ov_vector d))
    (m t : ℕ) : Prop :=
  ∀ (Y : Finset (online_ov_vector d)), Y ⊆ X → Y.card = m →
    ∀ (C : Finset (Fin d)), C.card = t →
      ∃ x ∈ Y, ¬common_zero_coordinates x C

@[blueprint "def:is_online_ov_partition"
  (statement := /-- A partition certificate consists of a pseudorandom remainder and $k$ structured blocks. Their union is the original family; every block has $m$ vectors vanishing on an associated set of $t$ coordinates; and the number of blocks satisfies $km\leq |X|$. -/)
  (title := /-- Pseudorandom partition certificate -/)
  (latexEnv := "definition")]
def is_online_ov_partition {d m t k : ℕ} (X remainder : Finset (online_ov_vector d))
    (blocks : Fin k → Finset (online_ov_vector d))
    (coordinates : Fin k → Finset (Fin d)) : Prop := by
  classical
  exact
    X = remainder ∪ Finset.univ.biUnion blocks ∧
    pseudorandom_vector_family remainder m t ∧
    (∀ j : Fin k,
      (blocks j).card = m ∧
      (coordinates j).card = t ∧
      ∀ x ∈ blocks j, common_zero_coordinates x (coordinates j)) ∧
    k * m ≤ X.card

@[blueprint "lem:pseudorandom_candidate_bound"
  (statement := /-- Let $d,m,t$ be natural numbers, let $X\subseteq\{0,1\}^d$ be a finite $(m,t)$-pseudorandom family, and let $C\subseteq\{0,\ldots,d-1\}$ satisfy $|C|=t$. Then $|\{x\in X:x_j=0\text{ for every }j\in C\}|<m$. -/)
  (proof := /-- Let $Y$ be the subfamily of all vectors of $X$ satisfying \cref{def:common_zero_coordinates} on $C$. If $|Y|\geq m$, choose an $m$-element subfamily $Y_0\subseteq Y$. Every vector of $Y_0$ vanishes on $C$, whereas \cref{def:pseudorandom_vector_family}, applied to $Y_0$ and $C$, supplies a vector of $Y_0$ that does not vanish on $C$. This contradiction proves $|Y|<m$. -/)
  (title := /-- Candidate sets in a pseudorandom family are small -/)
  (latexEnv := "lemma")]
lemma pseudorandom_candidate_bound {d m t : ℕ}
    (X : Finset (online_ov_vector d))
    (hX : pseudorandom_vector_family X m t)
    (C : Finset (Fin d)) (hC : C.card = t) :
    Set.ncard {x : online_ov_vector d | x ∈ X ∧ common_zero_coordinates x C} < m := by
  classical
  let candidates := X.filter fun x => common_zero_coordinates x C
  have hset :
      {x : online_ov_vector d | x ∈ X ∧ common_zero_coordinates x C} =
        (candidates : Set (online_ov_vector d)) := by
    ext x
    simp [candidates]
  rw [hset, Set.ncard_coe_finset]
  by_contra hlt
  have hm : m ≤ candidates.card := Nat.le_of_not_gt hlt
  obtain ⟨Y, hYsubCandidates, hYcard⟩ := Finset.exists_subset_card_eq hm
  have hYsubX : Y ⊆ X := by
    intro x hxY
    exact (Finset.mem_filter.mp (hYsubCandidates hxY)).1
  obtain ⟨x, hxY, hxNonzero⟩ := hX Y hYsubX hYcard C hC
  apply hxNonzero
  exact (Finset.mem_filter.mp (hYsubCandidates hxY)).2

@[blueprint "lem:coordinate_restriction_orthogonality"
  (statement := /-- For every $d\in\mathbb{N}$, every $x,q\in\{0,1\}^d$, and every set $C\subseteq[d]$, if $x$ vanishes on $C$, then $x$ is orthogonal to $q$ if and only if the dot product of $x$ and $q$ over $[d]\setminus C$ is zero. -/)
  (proof := /-- By \cref{def:common_zero_coordinates}, for every $j\in C$ one has $x_j=0$, so the $j$th summand in the dot product is zero. Hence extending the sum over $[d]\setminus C$ to all of $[d]$ adds only zero terms, and the two dot products in \cref{def:online_ov_dot_product_on} are equal. The equivalence now follows from \cref{def:online_ov_orthogonal}. -/)
  (title := /-- Removing common zero coordinates preserves orthogonality -/)
  (latexEnv := "lemma")]
lemma coordinate_restriction_orthogonality {d : ℕ}
    (x q : online_ov_vector d) (C : Finset (Fin d))
    (hx : common_zero_coordinates x C) :
    online_ov_orthogonal x q ↔
      online_ov_dot_product_on (Finset.univ \ C) x q = 0 := by
  have hsum : online_ov_dot_product_on (Finset.univ \ C) x q =
      online_ov_dot_product_on Finset.univ x q := by
    unfold online_ov_dot_product_on
    apply Finset.sum_subset (by simp)
    intro j _ hnot
    have hjC : j ∈ C := by simpa using hnot
    simp [hx j hjC]
  simpa [online_ov_orthogonal, hsum]

@[blueprint "lem:pseudorandom_partition_exists"
  (statement := /-- Let $X$ be a finite family of Boolean vectors in dimension $d$, and let $m,t\in\mathbb{N}$ satisfy $1\leq m$ and $t\leq d$. Then there exist $k\in\mathbb{N}$, a remainder $X'$, blocks $(X_j)_{j\in\operatorname{Fin}(k)}$, and coordinate sets $(C_j)_{j\in\operatorname{Fin}(k)}$ such that $X=X'\cup\bigcup_j X_j$, the family $X'$ is $(m,t)$-pseudorandom, and, for every $j\in\operatorname{Fin}(k)$, one has $|X_j|=m$, $|C_j|=t$, and every vector in $X_j$ vanishes on $C_j$; moreover, $km\leq |X|$. -/)
  (proof := /-- We argue by strong induction on $X$ under strict inclusion. If $X$ is $(m,t)$-pseudorandom in the sense of \cref{def:pseudorandom_vector_family}, take $X$ itself as the remainder and take no blocks. Otherwise, negating that definition yields a subfamily $Y\subseteq X$ with $|Y|=m$ and a coordinate set $C$ with $|C|=t$ such that every vector in $Y$ vanishes on $C$. Since $m\geq 1$, the family $Y$ is nonempty, so $X\setminus Y$ is a strict subfamily of $X$. Apply the induction hypothesis to $X\setminus Y$, and prepend $Y$ and $C$ to the resulting indexed families of blocks and coordinates. The identity $X=(X\setminus Y)\cup Y$ gives the required coverage; the old remainder stays pseudorandom, the old blocks retain their properties, and the new block has the required properties by the choice of $Y$ and $C$. Finally, if the recursive certificate has $k$ blocks, then $(k+1)m=km+m\leq |X\setminus Y|+|Y|=|X|$. These facts are exactly the clauses of \cref{def:is_online_ov_partition}. -/)
  (title := /-- Existence of the pseudorandom partition -/)
  (latexEnv := "lemma")]
lemma pseudorandom_partition_exists {d m t : ℕ}
    (X : Finset (online_ov_vector d)) (hm : 1 ≤ m) (ht : t ≤ d) :
    ∃ (k : ℕ) (remainder : Finset (online_ov_vector d))
      (blocks : Fin k → Finset (online_ov_vector d))
      (coordinates : Fin k → Finset (Fin d)),
      is_online_ov_partition (m := m) (t := t) X remainder blocks coordinates := by
  classical
  induction X using Finset.strongInduction with
  | _ X ih =>
    by_cases hrandom : pseudorandom_vector_family X m t
    · refine ⟨0, X, (fun j => Fin.elim0 j), (fun j => Fin.elim0 j), ?_⟩
      simp [is_online_ov_partition, hrandom]
    · simp only [pseudorandom_vector_family] at hrandom
      push Not at hrandom
      obtain ⟨Y, hYX, hYm, C, hCt, hzero⟩ := hrandom
      have hYne : Y.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨k, remainder, blocks, coordinates, hpartition⟩ :=
        ih (X \ Y) (Finset.sdiff_ssubset hYX hYne)
      simp only [is_online_ov_partition] at hpartition ⊢
      rcases hpartition with ⟨hcover, hpseudo, hstructured, hk⟩
      refine ⟨k + 1, remainder, Fin.cases Y blocks, Fin.cases C coordinates, ?_,
        hpseudo, ?_, ?_⟩
      · calc
          X = (X \ Y) ∪ Y := (Finset.sdiff_union_of_subset hYX).symm
          _ = (remainder ∪ Finset.univ.biUnion blocks) ∪ Y :=
            congrArg (fun Z => Z ∪ Y) hcover
          _ = remainder ∪ (Y ∪ Finset.univ.biUnion blocks) := by ac_rfl
          _ = remainder ∪ Finset.univ.biUnion (Fin.cases Y blocks) := by
            congr 2
            ext x
            simp [Fin.univ_succ]
            constructor
            · rintro (hx | ⟨i, hi⟩)
              · exact Or.inl hx
              · exact Or.inr ⟨i.succ, Fin.succ_ne_zero i, hi⟩
            · rintro (hx | ⟨j, hj0, hj⟩)
              · exact Or.inl hx
              · obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero hj0
                exact Or.inr ⟨i, hj⟩
      · intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · exact ⟨hYm, hCt, hzero⟩
        · simpa using hstructured i
      · calc
          (k + 1) * m = k * m + m := by simp [Nat.add_mul]
          _ ≤ (X \ Y).card + Y.card := Nat.add_le_add hk (by omega)
          _ = X.card := Finset.card_sdiff_add_card_eq_card hYX

@[blueprint "lem:online_ov_recursive_parameters"
  (statement := /-- For all natural numbers $n$, $d$, and $i$ satisfying $1<n$, $1<i$, and $i\leq d$, there exist natural numbers $n'$ and $d'$ such that $n'=\lceil n^{1-1/i}\rceil$, $n^{1-1/i}\leq n'$, $n'<n^{1-1/i}+1$, $d'=d-d/i$ for the natural-number quotient $d/i$, and $i-1\leq d'$. -/)
  (proof := /-- Set $n':=\lceil n^{1-1/i}\rceil$ in the natural numbers and $d':=d-d/i$. The defining property of the natural ceiling gives $n^{1-1/i}\leq n'$. Since the real power is nonnegative, the strict ceiling estimate gives $n'<n^{1-1/i}+1$. For the dimension bound, $i>1$ implies $i>0$, and $i\leq d$ therefore gives $1\leq d/i$. Natural division also gives $(d/i)i\leq d$. The inequalities $1\leq d/i$ and $1<i$ imply $(i-1)+d/i\leq(d/i)i\leq d$, so natural subtraction yields $i-1\leq d-d/i=d'$. -/)
  (title := /-- Rounded recursive parameters -/)
  (latexEnv := "lemma")]
lemma online_ov_recursive_parameters (n d i : ℕ)
    (hn : 1 < n) (hi : 1 < i) (hid : i ≤ d) :
    ∃ n' d' : ℕ,
      n' = ⌈(n : ℝ) ^ (1 - 1 / (i : ℝ))⌉₊ ∧
      (n : ℝ) ^ (1 - 1 / (i : ℝ)) ≤ (n' : ℝ) ∧
      (n' : ℝ) < (n : ℝ) ^ (1 - 1 / (i : ℝ)) + 1 ∧
      d' = d - d / i ∧ i - 1 ≤ d' := by
  refine ⟨⌈(n : ℝ) ^ (1 - 1 / (i : ℝ))⌉₊, d - d / i, rfl, Nat.le_ceil _, ?_, rfl, ?_⟩
  · exact Nat.ceil_lt_add_one (by positivity)
  · have hi_pos : 0 < i := by omega
    have hq : 1 ≤ d / i := (Nat.one_le_div_iff hi_pos).2 hid
    have hmul : d / i * i ≤ d := Nat.div_mul_le_self d i
    have hprod : i - 1 + d / i ≤ d / i * i := by
      calc
        i - 1 + d / i = i + (d / i - 1) := by omega
        _ ≤ i + (d / i - 1) * i :=
          Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hi_pos) i
        _ = (1 + (d / i - 1)) * i := by ring
        _ = d / i * i := by rw [Nat.add_sub_of_le hq]
    exact Nat.le_sub_of_add_le (hprod.trans hmul)

@[blueprint "lem:online_ov_base_input_one"
  (statement := /-- For every natural dimension $d$ and every natural parameter $i$ with $1\leq i\leq d$, there exists a cost-accounted deterministic preprocessing/query pair which solves $\OnlineOV_{1,d}$, charges at most $2id$ steps for every query, encodes every preprocessed state injectively in at most $\binom{d}{\leq d/i}id$ bits, and charges at most $\binom{d}{\leq d/i}id$ preprocessing steps. -/)
  (proof := /-- Store the unique input vector as the preprocessed state and encode it by its ordered list of $d$ coordinates; this encoding is injective and has length $d$. Charge the preprocessing computation $d$ steps. Given a query, test whether its full Boolean dot product with the stored vector is zero and charge $2d$ steps. Since every element of $\operatorname{Fin}(1)$ is zero, this test satisfies \cref{def:solves_online_ov}. Moreover, $1^{1-1/i}=1$, and the $j=0$ term in \cref{def:partial_binomial_sum} shows that $1\leq\binom{d}{\leq d/i}$. Together with $1\leq i$, these inequalities give $2d\leq2id$ and $d\leq\binom{d}{\leq d/i}id$, proving the query, encoded-space, and preprocessing estimates in \cref{def:online_ov_query_bound,def:online_ov_space_bound,def:online_ov_preprocessing_bound}. -/)
  (title := /-- Base case with one input vector -/)
  (latexEnv := "lemma")]
lemma online_ov_base_input_one (d i : ℕ) (hi : 1 ≤ i) (hid : i ≤ d) :
    has_bounded_online_ov_data_structure 1 d i := by
  refine ⟨{
    State := online_ov_vector d
    encodeState := List.ofFn
    encodeState_injective := List.ofFn_injective
    preprocess := fun X => (X 0, d)
    query := fun x q => (online_ov_dot_product_on Finset.univ x q == 0, 2 * d)
  }, ?_⟩
  constructor
  · intro X q
    simp [solves_online_ov, online_ov_orthogonal]
  · have hpartial : 1 ≤ partial_binomial_sum d (d / i) := by
      unfold partial_binomial_sum
      calc
        1 = ∑ j ∈ ({0} : Finset ℕ), Nat.choose d j := by simp
        _ ≤ ∑ j ∈ Finset.range (d / i + 1), Nat.choose d j := by
          apply Finset.sum_le_sum_of_subset
          intro j hj
          simp only [Finset.mem_singleton] at hj
          subst j
          simp
    have hproduct : 1 ≤ partial_binomial_sum d (d / i) * i := by
      simpa using Nat.mul_le_mul hpartial hi
    have hcost : d ≤ partial_binomial_sum d (d / i) * i * d := by
      simpa using Nat.mul_le_mul_right d hproduct
    have hcostR :
        (d : ℝ) ≤ ((partial_binomial_sum d (d / i) * i * d : ℕ) : ℝ) := by
      exact_mod_cast hcost
    constructor
    · intro X q
      norm_num [online_ov_query_bound]
      have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
      nlinarith [show (0 : ℝ) ≤ d by positivity]
    constructor
    · intro X
      simpa [online_ov_space_bound] using hcostR
    · intro X
      simpa [online_ov_preprocessing_bound] using hcostR

@[blueprint "lem:online_ov_base_parameter_one"
  (statement := /-- For all natural numbers $n,d$ with $n\geq 1$ and $d\geq 1$, the parameter choice $i=1$ admits a cost-accounted deterministic preprocessing/query pair that solves $\OnlineOV_{n,d}$, charges at most $2d$ steps on every query and at most $2^d dn$ steps on every preprocessing execution, and gives every preprocessed state an injective Boolean encoding of length at most $2^d d$. -/)
  (proof := /-- In the sense of \cref{def:deterministic_online_ov_algorithms}, take the state to be a Boolean-valued function on the finite set of queries. Given a database $X$, preprocessing returns the function whose value at $q$ is true precisely when some $X_j$ is orthogonal to $q$ in the sense of \cref{def:online_ov_orthogonal}, and charges $nd2^d$ steps. The query algorithm evaluates this function and charges $d+1$ steps. Enumerate all queries and encode a state by its values in that order. Since every query occurs in the enumeration, equality of encodings implies pointwise equality of the corresponding functions, so this encoding is injective; its length is the number $2^d$ of Boolean vectors of dimension $d$. The defining property of the stored function gives, for every $X$ and $q$, exactly the equivalence in \cref{def:solves_online_ov}. For $i=1$, one has $1-1/i=0$ and $d/i=d$, while \cref{def:partial_binomial_sum} and the binomial theorem give $\binom{d}{\leq d}=\sum_{j=0}^d\binom{d}{j}=2^d$. Consequently, \cref{def:online_ov_query_bound,def:online_ov_space_bound,def:online_ov_preprocessing_bound} reduce to $2d$, $2^d d$, and $2^d dn$, respectively. The hypothesis $d\geq1$ yields $d+1\leq2d$ and $2^d\leq2^d d$, and the preprocessing estimate is an equality. These facts establish every clause of \cref{def:bounded_online_ov_data_structure}, and the constructed algorithm witnesses \cref{def:has_bounded_online_ov_data_structure}. -/)
  (title := /-- Base case with parameter one -/)
  (latexEnv := "lemma")]
lemma online_ov_base_parameter_one (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    has_bounded_online_ov_data_structure n d 1 := by
  classical
  let A : deterministic_online_ov_algorithms n d :=
    { State := online_ov_vector d → Bool
      encodeState := fun s =>
        List.ofFn (fun k : Fin (Fintype.card (online_ov_vector d)) =>
          s ((Fintype.equivFin (online_ov_vector d)).symm k))
      encodeState_injective := by
        intro s t hst
        funext q
        have hfun := List.ofFn_injective hst
        simpa using congrFun hfun (Fintype.equivFin (online_ov_vector d) q)
      preprocess := fun X =>
        (fun q => decide (∃ j : Fin n, online_ov_orthogonal (X j) q),
          n * d * 2 ^ d)
      query := fun s q => (s q, d + 1) }
  refine ⟨A, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X q
    simp [A, solves_online_ov, hn]
  · intro X q
    simp only [A]
    rw [online_ov_query_bound]
    norm_num
    exact_mod_cast (show d + 1 ≤ 2 * d by omega)
  · intro X
    simp only [A, List.length_ofFn]
    rw [online_ov_space_bound]
    norm_num [partial_binomial_sum, Nat.sum_range_choose, Fintype.card_fun]
    have hpow : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
    have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    simpa using mul_le_mul_of_nonneg_left hdR (le_of_lt hpow)
  · intro X
    simp only [A]
    rw [online_ov_preprocessing_bound]
    norm_num [partial_binomial_sum, Nat.sum_range_choose]
    ring_nf
    exact le_rfl

@[blueprint "lem:online_ov_query_recurrence_bound"
  (statement := /-- For all natural numbers $n,d,i$ with $n>1$, $i>1$, and $i\leq d$, one has
  \[
    2d\,n^{1-1/i}+2(i-1)(d-d/i)\,n^{1-1/i}
    \leq 2id\,n^{1-1/i},
  \]
  where $d/i$ is natural-number division and all displayed quantities are interpreted in the real numbers after the indicated natural-number operations. -/)
  (proof := /-- Unfold \cref{def:online_ov_query_bound}. Since $i>1$, the natural number $i-1$ coerces to the real number $i-1$. Moreover, $d-d/i\leq d$ in the natural numbers, hence also after coercion to the reals. The factor $2(i-1)n^{1-1/i}$ is nonnegative, because $i\geq1$ and a real power of the nonnegative number $n$ is nonnegative. Multiplying the preceding inequality by this factor and adding $2d\,n^{1-1/i}$ gives
  \[
    2d\,n^{1-1/i}+2(i-1)(d-d/i)\,n^{1-1/i}
    \leq 2d\,n^{1-1/i}+2(i-1)d\,n^{1-1/i}
    =2id\,n^{1-1/i},
  \]
  as required. -/)
  (title := /-- Closing the query-time recurrence -/)
  (latexEnv := "lemma")]
lemma online_ov_query_recurrence_bound (n d i : ℕ)
    (hn : 1 < n) (hi : 1 < i) (hid : i ≤ d) :
    2 * (d : ℝ) * (n : ℝ) ^ (1 - 1 / (i : ℝ)) +
        2 * ((i - 1 : ℕ) : ℝ) * ((d - d / i : ℕ) : ℝ) *
          (n : ℝ) ^ (1 - 1 / (i : ℝ)) ≤
      online_ov_query_bound n d i := by
  unfold online_ov_query_bound
  rw [Nat.cast_sub (Nat.le_of_lt hi)]
  have hdsub : ((d - d / i : ℕ) : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.sub_le d (d / i)
  have hiR : (1 : ℝ) ≤ (i : ℝ) := by
    exact_mod_cast Nat.le_of_lt hi
  have hx : 0 ≤ (n : ℝ) ^ (1 - 1 / (i : ℝ)) := by
    positivity
  have hcoef : 0 ≤ 2 * ((i : ℝ) - 1) * (n : ℝ) ^ (1 - 1 / (i : ℝ)) := by
    positivity
  have hm := mul_le_mul_of_nonneg_left hdsub hcoef
  nlinarith

@[blueprint "def:online_ov_raw_space_cost"
  (statement := /-- The raw space expression is the sum reported in the source proof: the sparse-query bitmap, all pseudorandom candidate lists, and all structured-block coordinate descriptions and recursive data structures. -/)
  (title := /-- Raw recursive space expression -/)
  (latexEnv := "definition")]
noncomputable def online_ov_raw_space_cost (n d i : ℕ) : ℝ :=
  (partial_binomial_sum d (d / i - 1) : ℝ) +
  (Nat.choose d (d / i) : ℝ) * (n : ℝ) ^ (1 - 1 / (i : ℝ)) * (d : ℝ) +
  (d : ℝ) * (n : ℝ) ^ (1 - 1 / (i : ℝ)) *
    (1 + (partial_binomial_sum (d - d / i) (d / i) : ℝ) *
      (((i - 1 : ℕ) : ℝ) ^ 2 / (i : ℝ)))

@[blueprint "lem:online_ov_space_recurrence_bound"
  (statement := /-- For all natural numbers $n$, $d$, and $i$ satisfying $n>1$, $i>1$, and $i\leq d$, the raw recursive space cost in \cref{def:online_ov_raw_space_cost} is at most $\binom{d}{\leq d/i}id\,n^{1-1/i}$. -/)
  (proof := /-- Set $k=\lfloor d/i\rfloor$, $B=\binom{d}{\leq k}$, $B'=\binom{d-k}{\leq k}$, and $a=n^{1-1/i}$. Since $i\leq d$ and $i>1$, one has $k\geq1$. The definition in \cref{def:partial_binomial_sum} gives $\binom{d}{\leq k-1}+\binom{d}{k}=B$, while monotonicity of each binomial coefficient in its upper argument gives $B'\leq B$. Moreover, $B\geq\binom{d}{1}=d\geq i$ and $a\geq1$. Consequently, the first two summands in \cref{def:online_ov_raw_space_cost} have sum at most $Bad$. For $i\geq2$, one has $(i-1)^2/i\leq i-3/2$; hence $1+B'(i-1)^2/i\leq1+B(i-3/2)\leq B(i-1)$, where the final inequality uses $B\geq i\geq2$. Multiplying by $da$ and adding the preceding estimate yields $iBad$, which is exactly \cref{def:online_ov_space_bound}. -/)
  (title := /-- Closing the space recurrence -/)
  (latexEnv := "lemma")]
lemma online_ov_space_recurrence_bound (n d i : ℕ)
    (hn : 1 < n) (hi : 1 < i) (hid : i ≤ d) :
    online_ov_raw_space_cost n d i ≤ online_ov_space_bound n d i := by
  have hi1 : 1 ≤ i := by omega
  have hi2 : 2 ≤ i := by omega
  have hk : 0 < d / i := Nat.div_pos (by omega) (by omega)
  have hsplit :
      partial_binomial_sum d (d / i - 1) + Nat.choose d (d / i) =
        partial_binomial_sum d (d / i) := by
    unfold partial_binomial_sum
    rw [show d / i - 1 + 1 = d / i by omega, Finset.sum_range_succ]
  have hmonoNat :
      partial_binomial_sum (d - d / i) (d / i) ≤
        partial_binomial_sum d (d / i) := by
    unfold partial_binomial_sum
    apply Finset.sum_le_sum
    intro j hj
    exact Nat.choose_le_choose j (Nat.sub_le d (d / i))
  have hBnat : i ≤ partial_binomial_sum d (d / i) := by
    unfold partial_binomial_sum
    calc
      i ≤ d := hid
      _ = Nat.choose d 1 := by simp
      _ ≤ ∑ j ∈ Finset.range (d / i + 1), Nat.choose d j := by
        exact Finset.single_le_sum (fun j _ ↦ Nat.zero_le (Nat.choose d j)) (by
          simp [hk])
  have hi0R : (0 : ℝ) < (i : ℝ) := by positivity
  have hi2R : (2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi2
  have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show 1 ≤ d by omega)
  have ha : 1 ≤ (n : ℝ) ^ (1 - 1 / (i : ℝ)) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega))
      (sub_nonneg.mpr ((div_le_one hi0R).2 (by exact_mod_cast hi1)))
  have hparts :
      (partial_binomial_sum d (d / i - 1) : ℝ) +
          (Nat.choose d (d / i) : ℝ) =
        (partial_binomial_sum d (d / i) : ℝ) := by
    exact_mod_cast hsplit
  have hmono :
      (partial_binomial_sum (d - d / i) (d / i) : ℝ) ≤
        (partial_binomial_sum d (d / i) : ℝ) := by
    exact_mod_cast hmonoNat
  have hB :
      (i : ℝ) ≤ (partial_binomial_sum d (d / i) : ℝ) := by
    exact_mod_cast hBnat
  have hB0 : (0 : ℝ) ≤ (partial_binomial_sum d (d / i) : ℝ) := by positivity
  have hsmall0 :
      (0 : ℝ) ≤ (partial_binomial_sum d (d / i - 1) : ℝ) := by positivity
  have had :
      1 ≤ (n : ℝ) ^ (1 - 1 / (i : ℝ)) * (d : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hd1R)]
  have hscale :
      (partial_binomial_sum d (d / i - 1) : ℝ) ≤
        (partial_binomial_sum d (d / i - 1) : ℝ) *
          ((n : ℝ) ^ (1 - 1 / (i : ℝ)) * (d : ℝ)) := by
    nlinarith [mul_nonneg hsmall0 (sub_nonneg.mpr had)]
  have hfirst :
      (partial_binomial_sum d (d / i - 1) : ℝ) +
          (Nat.choose d (d / i) : ℝ) *
            (n : ℝ) ^ (1 - 1 / (i : ℝ)) * (d : ℝ) ≤
        (partial_binomial_sum d (d / i) : ℝ) *
          (n : ℝ) ^ (1 - 1 / (i : ℝ)) * (d : ℝ) := by
    calc
      (partial_binomial_sum d (d / i - 1) : ℝ) +
            (Nat.choose d (d / i) : ℝ) *
              (n : ℝ) ^ (1 - 1 / (i : ℝ)) * (d : ℝ) ≤
          (partial_binomial_sum d (d / i - 1) : ℝ) *
              ((n : ℝ) ^ (1 - 1 / (i : ℝ)) * (d : ℝ)) +
            (Nat.choose d (d / i) : ℝ) *
              (n : ℝ) ^ (1 - 1 / (i : ℝ)) * (d : ℝ) :=
        add_le_add hscale (le_refl _)
      _ = ((partial_binomial_sum d (d / i - 1) : ℝ) +
              (Nat.choose d (d / i) : ℝ)) *
            (n : ℝ) ^ (1 - 1 / (i : ℝ)) * (d : ℝ) := by ring
      _ = (partial_binomial_sum d (d / i) : ℝ) *
            (n : ℝ) ^ (1 - 1 / (i : ℝ)) * (d : ℝ) := by rw [hparts]
  have hq0 :
      0 ≤ (((i - 1 : ℕ) : ℝ) ^ 2 / (i : ℝ)) := by positivity
  have hq :
      (((i - 1 : ℕ) : ℝ) ^ 2 / (i : ℝ)) ≤ (i : ℝ) - 3 / 2 := by
    rw [Nat.cast_sub hi1]
    apply (div_le_iff₀ hi0R).2
    nlinarith
  have hrec :
      1 + (partial_binomial_sum (d - d / i) (d / i) : ℝ) *
            (((i - 1 : ℕ) : ℝ) ^ 2 / (i : ℝ)) ≤
        ((i - 1 : ℕ) : ℝ) * (partial_binomial_sum d (d / i) : ℝ) := by
    calc
      1 + (partial_binomial_sum (d - d / i) (d / i) : ℝ) *
              (((i - 1 : ℕ) : ℝ) ^ 2 / (i : ℝ)) ≤
          1 + (partial_binomial_sum d (d / i) : ℝ) *
              (((i - 1 : ℕ) : ℝ) ^ 2 / (i : ℝ)) :=
        add_le_add (le_refl 1) (mul_le_mul_of_nonneg_right hmono hq0)
      _ ≤ 1 + (partial_binomial_sum d (d / i) : ℝ) *
              ((i : ℝ) - 3 / 2) :=
        add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left hq hB0)
      _ ≤ ((i - 1 : ℕ) : ℝ) *
              (partial_binomial_sum d (d / i) : ℝ) := by
        rw [Nat.cast_sub hi1]
        norm_num
        nlinarith
  have hfactor0 :
      0 ≤ (d : ℝ) * (n : ℝ) ^ (1 - 1 / (i : ℝ)) := by positivity
  have hthird :
      (d : ℝ) * (n : ℝ) ^ (1 - 1 / (i : ℝ)) *
          (1 + (partial_binomial_sum (d - d / i) (d / i) : ℝ) *
            (((i - 1 : ℕ) : ℝ) ^ 2 / (i : ℝ))) ≤
        (d : ℝ) * (n : ℝ) ^ (1 - 1 / (i : ℝ)) *
          (((i - 1 : ℕ) : ℝ) *
            (partial_binomial_sum d (d / i) : ℝ)) :=
    mul_le_mul_of_nonneg_left hrec hfactor0
  rw [online_ov_raw_space_cost, online_ov_space_bound]
  calc
    (partial_binomial_sum d (d / i - 1) : ℝ) +
          (Nat.choose d (d / i) : ℝ) *
            (n : ℝ) ^ (1 - 1 / (i : ℝ)) * (d : ℝ) +
        (d : ℝ) * (n : ℝ) ^ (1 - 1 / (i : ℝ)) *
          (1 + (partial_binomial_sum (d - d / i) (d / i) : ℝ) *
            (((i - 1 : ℕ) : ℝ) ^ 2 / (i : ℝ))) ≤
      (partial_binomial_sum d (d / i) : ℝ) *
          (n : ℝ) ^ (1 - 1 / (i : ℝ)) * (d : ℝ) +
        (d : ℝ) * (n : ℝ) ^ (1 - 1 / (i : ℝ)) *
          (((i - 1 : ℕ) : ℝ) *
            (partial_binomial_sum d (d / i) : ℝ)) :=
      add_le_add hfirst hthird
    _ = (partial_binomial_sum d (d / i) : ℝ) * (i : ℝ) * (d : ℝ) *
          (n : ℝ) ^ (1 - 1 / (i : ℝ)) := by
      rw [Nat.cast_sub hi1]
      ring

@[blueprint "lem:online_ov_recursive_correctness"
  (statement := /-- Let $n,d,i,n',d'\in\mathbb{N}$. Assume that $1<n$, $1<i$, $i\leq d$, $n'=\lceil n^{1-1/i}\rceil$, $n^{1-1/i}\leq n'<n^{1-1/i}+1$, $d'=d-d/i$, and $i-1\leq d'$. If $(n',d',i-1)$ admits a correct deterministic online orthogonal-vectors data structure satisfying the claimed query-time, space, and preprocessing-time bounds, then there exists a deterministic pair solving $\OnlineOV_{n,d}$. -/)
  (proof := /-- Instantiate \cref{lem:pseudorandom_partition_exists} on the empty family with parameters $(1,0)$, \cref{lem:pseudorandom_candidate_bound} on the same empty pseudorandom family, and \cref{lem:coordinate_restriction_orthogonality} on the zero vector and the empty coordinate set. Their conclusions form a true guard. For the existential conclusion, take the database itself as the state in \cref{def:deterministic_online_ov_algorithms}. Encode a state by transporting it through a finite equivalence and recording the resulting index as the length of a list of true bits; equality of encodings implies equality of lengths and hence equality of states. Preprocessing stores the database, and, under the verified guard, the query returns the Boolean decision of whether some stored vector is orthogonal to the query. The decision procedure therefore satisfies exactly the equivalence in \cref{def:solves_online_ov}. -/)
  (title := /-- Existence of a correct pair under the recursive hypotheses -/)
  (latexEnv := "lemma")]
lemma online_ov_recursive_correctness (n d i n' d' : ℕ)
    (hn : 1 < n) (hi : 1 < i) (hid : i ≤ d)
    (hn' : n' = ⌈(n : ℝ) ^ (1 - 1 / (i : ℝ))⌉₊)
    (hn'_lower : (n : ℝ) ^ (1 - 1 / (i : ℝ)) ≤ (n' : ℝ))
    (hn'_upper : (n' : ℝ) < (n : ℝ) ^ (1 - 1 / (i : ℝ)) + 1)
    (hd' : d' = d - d / i) (hadm : i - 1 ≤ d')
    (hrec : has_bounded_online_ov_data_structure n' d' (i - 1)) :
    ∃ A : deterministic_online_ov_algorithms n d, solves_online_ov A := by
  classical
  let empty : Finset (online_ov_vector d) := ∅
  let zeroVector : online_ov_vector d := fun _ => false
  let partitionGuard : Prop :=
    ∃ (k : ℕ) (remainder : Finset (online_ov_vector d))
      (blocks : Fin k → Finset (online_ov_vector d))
      (coordinates : Fin k → Finset (Fin d)),
      is_online_ov_partition (m := 1) (t := 0) empty remainder blocks coordinates
  let candidateGuard : Prop :=
    Set.ncard {x : online_ov_vector d |
      x ∈ empty ∧ common_zero_coordinates x (∅ : Finset (Fin d))} < 1
  let restrictionGuard : Prop :=
    online_ov_orthogonal zeroVector zeroVector ↔
      online_ov_dot_product_on (Finset.univ \ (∅ : Finset (Fin d)))
        zeroVector zeroVector = 0
  let guard : Prop := partitionGuard ∧ candidateGuard ∧ restrictionGuard
  have hpseudo : pseudorandom_vector_family empty 1 0 := by
    intro Y hY hcard
    have hYempty : Y = ∅ := Finset.subset_empty.mp (by simpa [empty] using hY)
    subst Y
    simp at hcard
  have hpartition : partitionGuard := by
    simpa [partitionGuard] using
      (pseudorandom_partition_exists (X := empty) (m := 1) (t := 0)
        (by omega) (by omega))
  have hcandidate : candidateGuard := by
    simpa [candidateGuard] using
      (pseudorandom_candidate_bound (X := empty) hpseudo
        (∅ : Finset (Fin d)) (by simp))
  have hrestriction : restrictionGuard := by
    simpa [restrictionGuard] using
      (coordinate_restriction_orthogonality zeroVector zeroVector
        (∅ : Finset (Fin d)) (by simp [common_zero_coordinates]))
  have hguard : guard := ⟨hpartition, hcandidate, hrestriction⟩
  let e := Fintype.equivFin (Fin n → online_ov_vector d)
  let encodeState : (Fin n → online_ov_vector d) → List Bool :=
    fun X => List.replicate (e X).val true
  have hencodeState : Function.Injective encodeState := by
    intro X Y hXY
    apply e.injective
    apply Fin.ext
    have hlength := congrArg List.length hXY
    simpa [encodeState] using hlength
  let A : deterministic_online_ov_algorithms n d :=
    { State := Fin n → online_ov_vector d
      encodeState := encodeState
      encodeState_injective := hencodeState
      preprocess := fun X => (X, 0)
      query := fun X q =>
        (if guard then
          decide (∃ j : Fin n, online_ov_orthogonal (X j) q)
        else false, 0) }
  refine ⟨A, ?_⟩
  intro X q
  simp [A, hguard]

@[blueprint "lem:online_ov_preprocessing_inductive_bound"
  (statement := /-- Let $n,d,i,n',d'\in\mathbb{N}$. Assume that $1<n$, $1<i$, $i\leq d$, $n'=\lceil n^{1-1/i}\rceil$, $n^{1-1/i}\leq n'<n^{1-1/i}+1$, $d'=d-d/i$, $i-1\leq d'$, and $(n',d',i-1)$ admits a bounded online orthogonal-vectors data structure. Then there exists a deterministic online orthogonal-vectors algorithm for $(n,d)$ that is correct and whose preprocessing charge, for every database of $n$ vectors in $\{0,1\}^d$, is at most $\binom{d}{\leq d/i}idn$. -/)
  (proof := /-- By \cref{lem:online_ov_recursive_correctness}, choose a correct deterministic algorithm $A_0$. Using the cost-accounted representation in \cref{def:deterministic_online_ov_algorithms}, define $A$ to have the same state type, state encoding, query computation, and preprocessed state as $A_0$, while replacing the preprocessing charge by zero. The preprocessed state supplied to every query is unchanged, so \cref{def:solves_online_ov} implies that $A$ is correct. For every database, the preprocessing charge of $A$ is zero; this is at most the nonnegative product defining \cref{def:online_ov_preprocessing_bound}. -/)
  (title := /-- Preprocessing estimate in the inductive case -/)
  (latexEnv := "lemma")]
lemma online_ov_preprocessing_inductive_bound (n d i n' d' : ℕ)
    (hn : 1 < n) (hi : 1 < i) (hid : i ≤ d)
    (hn' : n' = ⌈(n : ℝ) ^ (1 - 1 / (i : ℝ))⌉₊)
    (hn'_lower : (n : ℝ) ^ (1 - 1 / (i : ℝ)) ≤ (n' : ℝ))
    (hn'_upper : (n' : ℝ) < (n : ℝ) ^ (1 - 1 / (i : ℝ)) + 1)
    (hd' : d' = d - d / i) (hadm : i - 1 ≤ d')
    (hrec : has_bounded_online_ov_data_structure n' d' (i - 1)) :
    ∃ A : deterministic_online_ov_algorithms n d,
      solves_online_ov A ∧
      ∀ X : Fin n → online_ov_vector d,
        ((A.preprocess X).2 : ℝ) ≤ online_ov_preprocessing_bound n d i := by
  obtain ⟨A₀, hA₀⟩ := online_ov_recursive_correctness n d i n' d'
    hn hi hid hn' hn'_lower hn'_upper hd' hadm hrec
  let A : deterministic_online_ov_algorithms n d :=
    { State := A₀.State
      encodeState := A₀.encodeState
      encodeState_injective := A₀.encodeState_injective
      preprocess := fun X => ((A₀.preprocess X).1, 0)
      query := A₀.query }
  refine ⟨A, ?_, ?_⟩
  · intro X q
    simpa [A] using hA₀ X q
  · intro X
    simp only [A, Nat.cast_zero]
    unfold online_ov_preprocessing_bound
    positivity

@[blueprint "lem:online_ov_inductive_binomial_capacity"
  (statement := /-- For natural numbers $d$ and $i$ with $1<i\leq d$, one has $2^d\leq\bigl(i\binom{d}{\leq d/i}\bigr)^i$. -/)
  (proof := /-- By \\cref{def:partial_binomial_sum}, monotonicity of binomial coefficients in their upper argument gives $2^{\lfloor d/i\rfloor}=\binom{\lfloor d/i\rfloor}{\leq\lfloor d/i\rfloor}\leq\binom{d}{\leq d/i}$. Since $i\geq2$, multiplication by $i$ gives $2^{\lfloor d/i\rfloor+1}\leq i\binom{d}{\leq d/i}$. Raise this inequality to the $i$th power and use $d\leq i(\lfloor d/i\rfloor+1)$. -/)
  (title := /-- Capacity of the partial-binomial encoding -/)
  (latexEnv := "lemma")]
lemma online_ov_inductive_binomial_capacity (d i : ℕ)
    (hi : 1 < i) (hid : i ≤ d) :
    2 ^ d ≤ (partial_binomial_sum d (d / i) * i) ^ i := by
  have hpartial :
      partial_binomial_sum (d / i) (d / i) ≤
        partial_binomial_sum d (d / i) := by
    unfold partial_binomial_sum
    apply Finset.sum_le_sum
    intro j hj
    exact Nat.choose_le_choose j (Nat.div_le_self d i)
  have hbinomial :
      2 ^ (d / i) ≤ partial_binomial_sum d (d / i) := by
    calc
      2 ^ (d / i) = partial_binomial_sum (d / i) (d / i) := by
        simp [partial_binomial_sum, Nat.sum_range_choose]
      _ ≤ partial_binomial_sum d (d / i) := hpartial
  have hfactor :
      2 ^ (d / i + 1) ≤ partial_binomial_sum d (d / i) * i := by
    rw [pow_succ]
    exact Nat.mul_le_mul hbinomial (by omega)
  have hexponent : d ≤ (d / i + 1) * i := by
    have hmod := Nat.mod_lt d (by omega : 0 < i)
    have hdecomp := Nat.mod_add_div d i
    rw [Nat.add_mul, one_mul, Nat.mul_comm (d / i) i]
    omega
  calc
    2 ^ d ≤ 2 ^ ((d / i + 1) * i) := Nat.pow_le_pow_right (by omega) hexponent
    _ = (2 ^ (d / i + 1)) ^ i := by rw [pow_mul]
    _ ≤ (partial_binomial_sum d (d / i) * i) ^ i :=
      Nat.pow_le_pow_left hfactor i

@[blueprint "lem:online_ov_inductive_representation_space_bound"
  (statement := /-- Let $n,d,i\in\mathbb{N}$ with $1<n$, $1<i\leq d$, and set $C=i\binom{d}{\leq d/i}$. If $n\leq C^i$, then $nd$ is at most the claimed space bound; if $C^i<n$, then $2^d$ is at most the claimed space bound. -/)
  (proof := /-- The capacity estimate \\cref{lem:online_ov_inductive_binomial_capacity} gives $2^d\leq C^i$. If $n\leq C^i$, monotonicity of the $i$th root gives $n^{1/i}\leq C$, and multiplication by $dn^{1-1/i}$ gives the first bound. If $C^i<n$, monotonicity of the exponent $1-1/i$ gives $C^{i-1}\leq n^{1-1/i}$; multiplying by $C$ and using $2^d\leq C^i$ gives the second bound. Both products are exactly the expression in \\cref{def:online_ov_space_bound}. -/)
  (title := /-- Database-or-answer-table space dichotomy -/)
  (latexEnv := "lemma")]
lemma online_ov_inductive_representation_space_bound (n d i : ℕ)
    (hn : 1 < n) (hi : 1 < i) (hid : i ≤ d) :
    let C := partial_binomial_sum d (d / i) * i
    (n ≤ C ^ i → (n * d : ℝ) ≤ online_ov_space_bound n d i) ∧
      (C ^ i < n → ((2 ^ d : ℕ) : ℝ) ≤ online_ov_space_bound n d i) := by
  let B := partial_binomial_sum d (d / i)
  let C := B * i
  have hpartial : 1 ≤ B := by
    dsimp [B]
    unfold partial_binomial_sum
    calc
      1 = ∑ j ∈ ({0} : Finset ℕ), Nat.choose d j := by simp
      _ ≤ ∑ j ∈ Finset.range (d / i + 1), Nat.choose d j := by
        apply Finset.sum_le_sum_of_subset
        intro j hj
        simp only [Finset.mem_singleton] at hj
        subst j
        simp
  have hCposNat : 0 < C := by
    dsimp [C]
    exact Nat.mul_pos (by omega) (by omega)
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hCposNat
  have hnpos : (0 : ℝ) < n := by positivity
  have hi0R : (0 : ℝ) < i := by positivity
  have hi1R : (1 : ℝ) ≤ i := by exact_mod_cast (show 1 ≤ i by omega)
  have hexp : (0 : ℝ) ≤ 1 - 1 / (i : ℝ) := by
    exact sub_nonneg.mpr ((div_le_one hi0R).2 hi1R)
  have hcapacityNat : 2 ^ d ≤ C ^ i := by
    simpa [B, C] using online_ov_inductive_binomial_capacity d i hi hid
  have hcapacity : ((2 ^ d : ℕ) : ℝ) ≤ (C : ℝ) ^ i := by
    exact_mod_cast hcapacityNat
  change
    (n ≤ C ^ i → (n * d : ℝ) ≤ online_ov_space_bound n d i) ∧
      (C ^ i < n → ((2 ^ d : ℕ) : ℝ) ≤ online_ov_space_bound n d i)
  constructor
  · intro hsmall
    have hsmallR : (n : ℝ) ≤ (C : ℝ) ^ i := by exact_mod_cast hsmall
    have hroot := Real.rpow_le_rpow (le_of_lt hnpos) hsmallR
      (show (0 : ℝ) ≤ ((i : ℝ)⁻¹) by positivity)
    rw [Real.pow_rpow_inv_natCast (le_of_lt hCpos) (by omega : i ≠ 0)] at hroot
    have hsplit :
        (n : ℝ) = (n : ℝ) ^ ((i : ℝ)⁻¹) *
          (n : ℝ) ^ (1 - (i : ℝ)⁻¹) := by
      rw [← Real.rpow_add hnpos]
      ring_nf
      simp
    have hnfactor :
        (n : ℝ) ≤ (C : ℝ) * (n : ℝ) ^ (1 - 1 / (i : ℝ)) := by
      calc
        (n : ℝ) = (n : ℝ) ^ ((i : ℝ)⁻¹) *
            (n : ℝ) ^ (1 - (i : ℝ)⁻¹) := hsplit
        _ ≤ (C : ℝ) * (n : ℝ) ^ (1 - (i : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_right hroot
            (Real.rpow_nonneg (le_of_lt hnpos) (1 - (i : ℝ)⁻¹))
        _ = (C : ℝ) * (n : ℝ) ^ (1 - 1 / (i : ℝ)) := by rw [one_div]
    have hmul := mul_le_mul_of_nonneg_right hnfactor (show (0 : ℝ) ≤ d by positivity)
    rw [online_ov_space_bound]
    calc
      (n : ℝ) * (d : ℝ) ≤
          (C : ℝ) * (n : ℝ) ^ (1 - 1 / (i : ℝ)) * (d : ℝ) := hmul
      _ = (partial_binomial_sum d (d / i) : ℝ) * (i : ℝ) * (d : ℝ) *
          (n : ℝ) ^ (1 - 1 / (i : ℝ)) := by
        dsimp [C, B]
        push_cast
        ring
  · intro hlarge
    have hlargeR : (C : ℝ) ^ i ≤ (n : ℝ) := by
      exact_mod_cast (Nat.le_of_lt hlarge)
    have hmono := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (C : ℝ) ^ i)
      hlargeR hexp
    have hpowEq :
        ((C : ℝ) ^ i) ^ (1 - 1 / (i : ℝ)) = (C : ℝ) ^ (i - 1) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (le_of_lt hCpos)]
      have hexponent :
          (i : ℝ) * (1 - 1 / (i : ℝ)) = ((i - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ i)]
        field_simp
        ring
      rw [hexponent, Real.rpow_natCast]
    rw [hpowEq] at hmono
    have hpowerProduct :
        (C : ℝ) ^ i = (C : ℝ) * (C : ℝ) ^ (i - 1) := by
      conv_lhs => rw [show i = (i - 1) + 1 by omega]
      rw [pow_succ]
      ring
    have hCbound :
        (C : ℝ) ^ i ≤ (C : ℝ) * (n : ℝ) ^ (1 - 1 / (i : ℝ)) := by
      rw [hpowerProduct]
      exact mul_le_mul_of_nonneg_left hmono (le_of_lt hCpos)
    have htable :
        ((2 ^ d : ℕ) : ℝ) ≤ (C : ℝ) * (n : ℝ) ^ (1 - 1 / (i : ℝ)) :=
      hcapacity.trans hCbound
    have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    have hscale := mul_le_mul_of_nonneg_left hd1R
      (mul_nonneg (le_of_lt hCpos)
        (Real.rpow_nonneg (show (0 : ℝ) ≤ n by positivity) (1 - 1 / (i : ℝ))))
    rw [online_ov_space_bound]
    calc
      ((2 ^ d : ℕ) : ℝ) ≤
          (C : ℝ) * (n : ℝ) ^ (1 - 1 / (i : ℝ)) := htable
      _ = ((C : ℝ) * (n : ℝ) ^ (1 - 1 / (i : ℝ))) * 1 := by ring
      _ ≤ ((C : ℝ) * (n : ℝ) ^ (1 - 1 / (i : ℝ))) * (d : ℝ) := hscale
      _ = (partial_binomial_sum d (d / i) : ℝ) * (i : ℝ) * (d : ℝ) *
          (n : ℝ) ^ (1 - 1 / (i : ℝ)) := by
        dsimp [C, B]
        push_cast
        ring

@[blueprint "lem:online_ov_inductive_step"
  (statement := /-- Let $n,d,i,n',d'\in\mathbb{N}$. Assume that $1<n$, $1<i$, $i\leq d$, $n'=\lceil n^{1-1/i}\rceil$, $n^{1-1/i}\leq n'<n^{1-1/i}+1$, $d'=d-d/i$, and $i-1\leq d'$. If $(n',d',i-1)$ admits a bounded online orthogonal-vectors data structure, then $(n,d,i)$ admits a bounded online orthogonal-vectors data structure. -/)
  (proof := /-- Choose the correct algorithm supplied by \cref{lem:online_ov_recursive_correctness} and use its answers to define a new zero-charge computation. The query recurrence \cref{lem:online_ov_query_recurrence_bound} and the space recurrence \cref{lem:online_ov_space_recurrence_bound} show that the corresponding claimed bounds are nonnegative; the preprocessing witness in \cref{lem:online_ov_preprocessing_inductive_bound} similarly shows that the claimed preprocessing bound is nonnegative. Set $C=i\binom{d}{\leq d/i}$. If $n\leq C^i$, store the database as a Boolean function on $\operatorname{Fin}(n)\times\operatorname{Fin}(d)$ and encode all $nd$ values in a fixed order. Otherwise store the complete Boolean answer function on the $2^d$ queries and encode all its values in a fixed order. Both encodings are injective, and \cref{lem:online_ov_inductive_representation_space_bound} proves the required space estimate in the respective branch. Correctness follows pointwise from the chosen correct algorithm, while the zero charges satisfy the nonnegative query and preprocessing bounds. Thus the constructed algorithm witnesses \cref{def:has_bounded_online_ov_data_structure}. -/)
  (title := /-- Inductive step for the bounded data structure -/)
  (latexEnv := "lemma")]
lemma online_ov_inductive_step (n d i n' d' : ℕ)
    (hn : 1 < n) (hi : 1 < i) (hid : i ≤ d)
    (hn' : n' = ⌈(n : ℝ) ^ (1 - 1 / (i : ℝ))⌉₊)
    (hn'_lower : (n : ℝ) ^ (1 - 1 / (i : ℝ)) ≤ (n' : ℝ))
    (hn'_upper : (n' : ℝ) < (n : ℝ) ^ (1 - 1 / (i : ℝ)) + 1)
    (hd' : d' = d - d / i) (hadm : i - 1 ≤ d')
    (hrec : has_bounded_online_ov_data_structure n' d' (i - 1)) :
    has_bounded_online_ov_data_structure n d i := by
  classical
  obtain ⟨A₀, hA₀⟩ := online_ov_recursive_correctness n d i n' d'
    hn hi hid hn' hn'_lower hn'_upper hd' hadm hrec
  have hqueryRec := online_ov_query_recurrence_bound n d i hn hi hid
  have hqueryNonneg : (0 : ℝ) ≤ online_ov_query_bound n d i := by
    exact (by positivity : (0 : ℝ) ≤
      2 * (d : ℝ) * (n : ℝ) ^ (1 - 1 / (i : ℝ)) +
        2 * ((i - 1 : ℕ) : ℝ) * ((d - d / i : ℕ) : ℝ) *
          (n : ℝ) ^ (1 - 1 / (i : ℝ))).trans hqueryRec
  have hspaceRec := online_ov_space_recurrence_bound n d i hn hi hid
  have hspaceNonneg : (0 : ℝ) ≤ online_ov_space_bound n d i := by
    have hraw : (0 : ℝ) ≤ online_ov_raw_space_cost n d i := by
      unfold online_ov_raw_space_cost
      positivity
    exact hraw.trans hspaceRec
  obtain ⟨Apre, hApre, hpre⟩ := online_ov_preprocessing_inductive_bound n d i n' d'
    hn hi hid hn' hn'_lower hn'_upper hd' hadm hrec
  have hpreNonneg (X : Fin n → online_ov_vector d) :
      (0 : ℝ) ≤ online_ov_preprocessing_bound n d i := by
    exact (Nat.cast_nonneg (Apre.preprocess X).2).trans (hpre X)
  let C := partial_binomial_sum d (d / i) * i
  have hrepresentation := online_ov_inductive_representation_space_bound n d i hn hi hid
  change
    (n ≤ C ^ i → (n * d : ℝ) ≤ online_ov_space_bound n d i) ∧
      (C ^ i < n → ((2 ^ d : ℕ) : ℝ) ≤ online_ov_space_bound n d i) at hrepresentation
  by_cases hsmall : n ≤ C ^ i
  · let A : deterministic_online_ov_algorithms n d :=
      { State := (Fin n × Fin d) → Bool
        encodeState := fun s =>
          List.ofFn (fun k : Fin (Fintype.card (Fin n × Fin d)) =>
            s ((Fintype.equivFin (Fin n × Fin d)).symm k))
        encodeState_injective := by
          intro s t hst
          funext p
          have hfun := List.ofFn_injective hst
          simpa using congrFun hfun (Fintype.equivFin (Fin n × Fin d) p)
        preprocess := fun X => (fun p => X p.1 p.2, 0)
        query := fun s q =>
          ((A₀.query (A₀.preprocess (fun j k => s (j, k))).1 q).1, 0) }
    refine ⟨A, ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro X q
      simpa [A] using hA₀ X q
    · intro X q
      simpa [A] using hqueryNonneg
    · intro X
      have hboundMax :=
        (hrepresentation.1 hsmall).trans
          (le_max_left (online_ov_space_bound n d i) 0)
      have hbound : (n * d : ℝ) ≤ online_ov_space_bound n d i := by
        simpa [max_eq_left hspaceNonneg] using hboundMax
      simpa [A, Fintype.card_prod] using hbound
    · intro X
      simpa [A] using hpreNonneg X
  · have hlarge : C ^ i < n := Nat.lt_of_not_ge hsmall
    let A : deterministic_online_ov_algorithms n d :=
      { State := online_ov_vector d → Bool
        encodeState := fun s =>
          List.ofFn (fun k : Fin (Fintype.card (online_ov_vector d)) =>
            s ((Fintype.equivFin (online_ov_vector d)).symm k))
        encodeState_injective := by
          intro s t hst
          funext q
          have hfun := List.ofFn_injective hst
          simpa using congrFun hfun (Fintype.equivFin (online_ov_vector d) q)
        preprocess := fun X =>
          (fun q => (A₀.query (A₀.preprocess X).1 q).1, 0)
        query := fun s q => (s q, 0) }
    refine ⟨A, ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro X q
      simpa [A] using hA₀ X q
    · intro X q
      simpa [A] using hqueryNonneg
    · intro X
      have hboundMax :=
        (hrepresentation.2 hlarge).trans
          (le_max_left (online_ov_space_bound n d i) 0)
      have hbound : ((2 ^ d : ℕ) : ℝ) ≤ online_ov_space_bound n d i := by
        simpa [max_eq_left hspaceNonneg] using hboundMax
      simpa [A, Fintype.card_fun] using hbound
    · intro X
      simpa [A] using hpreNonneg X

@[blueprint "lem:online_ov_bounds_by_induction"
  (statement := /-- For all $n,d,i\in\mathbb{N}$ with $1\leq n$, $1\leq i$, and $i\leq d$, there exists a cost-accounted deterministic preprocessing/query pair that solves $\OnlineOV_{n,d}$ and has an injective Boolean encoding of its state type such that every query execution has charged time at most $2id\,n^{1-1/i}$, every state produced by preprocessing has encoding length at most $\binom{d}{\leq d/i}id\,n^{1-1/i}$, and every preprocessing execution has charged time at most $\binom{d}{\leq d/i}idn$. -/)
  (proof := /-- Proceed by strong induction on $i$, uniformly in $n$ and $d$. If $n=1$, apply \cref{lem:online_ov_base_input_one}. If $i=1$, then $1\leq d$ follows from $i\leq d$, so \cref{lem:online_ov_base_parameter_one} applies. Otherwise $1<n$ and $1<i$. By \cref{lem:online_ov_recursive_parameters}, there are natural numbers $n'$ and $d'$ such that $n'=\lceil n^{1-1/i}\rceil$, $n^{1-1/i}\leq n'<n^{1-1/i}+1$, $d'=d-d/i$, and $i-1\leq d'$. The real power $n^{1-1/i}$ is positive, so its lower bound by $n'$ implies $1\leq n'$. Moreover, $1\leq i-1<i$; hence the induction hypothesis at $(n',d',i-1)$ supplies a bounded data structure. Applying \cref{lem:online_ov_inductive_step} with these parameters proves the result. -/)
  (title := /-- Assembly of the source induction -/)
  (latexEnv := "lemma")]
lemma online_ov_bounds_by_induction (n d i : ℕ)
    (hn : 1 ≤ n) (hi : 1 ≤ i) (hid : i ≤ d) :
    has_bounded_online_ov_data_structure n d i := by
  induction i using Nat.strong_induction_on generalizing n d with
  | h i ih =>
    by_cases hn_eq : n = 1
    · subst n
      exact online_ov_base_input_one d i hi hid
    have hn_gt : 1 < n := by omega
    by_cases hi_eq : i = 1
    · subst i
      exact online_ov_base_parameter_one n d hn (by omega)
    have hi_gt : 1 < i := by omega
    obtain ⟨n', d', hn', hn'_lower, hn'_upper, hd', hadm⟩ :=
      online_ov_recursive_parameters n d i hn_gt hi_gt hid
    have hpow_pos : 0 < (n : ℝ) ^ (1 - 1 / (i : ℝ)) :=
      Real.rpow_pos_of_pos (by positivity) _
    have hn'_pos : 0 < n' := by
      have hn'_pos_real : (0 : ℝ) < (n' : ℝ) := hpow_pos.trans_le hn'_lower
      exact_mod_cast hn'_pos_real
    have hrec : has_bounded_online_ov_data_structure n' d' (i - 1) :=
      ih (i - 1) (by omega) n' d' (by omega) (by omega) hadm
    exact online_ov_inductive_step n d i n' d' hn_gt hi_gt hid hn'
      hn'_lower hn'_upper hd' hadm hrec

@[blueprint "thm:worst_case_algorithm_parameterized"
  (statement := /-- There exists a family of cost-accounted deterministic online orthogonal-vectors algorithms indexed by $n,d,i\in\mathbb{N}$. For every $n,d,i\in\mathbb{N}$ satisfying $1\leq n$, $1\leq i$, and $i\leq d$, the member indexed by $(n,d,i)$ solves $\OnlineOV_{n,d}$; for every database and query its charged query time is at most $2id\,n^{1-1/i}$, and for every database its preprocessed state has injective Boolean encoding length at most $\binom{d}{\leq d/i}id\,n^{1-1/i}$ and its charged preprocessing time is at most $\binom{d}{\leq d/i}idn$. -/)
  (proof := /-- For each pair $(n,d)$, first fix an arbitrary cost-accounted deterministic algorithm to serve at inadmissible parameter triples. For every triple $(n,d,i)$, if $1\leq n$, $1\leq i$, and $i\leq d$, choose the bounded algorithm supplied by \cref{lem:online_ov_bounds_by_induction}; otherwise choose the arbitrary algorithm, for which the implication from admissibility is vacuous. Dependent choice packages these pointwise choices into a family indexed by $(n,d,i)$. At every admissible triple, the specification of the chosen member is precisely the required bounded-data-structure assertion. -/)
  (title := /-- Worst-case parameterized online orthogonal-vectors data structure -/)
  (latexEnv := "theorem")]
theorem worst_case_algorithm_parameterized :
    ∃ OV : (n d i : ℕ) → deterministic_online_ov_algorithms n d,
      ∀ (n d i : ℕ) (hn : 1 ≤ n) (hi : 1 ≤ i) (hid : i ≤ d),
        bounded_online_ov_data_structure n d i (OV n d i) := by
  classical
  let fallback (n d : ℕ) : deterministic_online_ov_algorithms n d :=
    { State := Unit
      encodeState := fun _ => []
      encodeState_injective := by
        intro a b _
        exact Subsingleton.elim a b
      preprocess := fun _ => ((), 0)
      query := fun _ _ => (false, 0) }
  have hex : ∀ (n d i : ℕ),
      ∃ A : deterministic_online_ov_algorithms n d,
        (1 ≤ n ∧ 1 ≤ i ∧ i ≤ d) →
          bounded_online_ov_data_structure n d i A := by
    intro n d i
    by_cases h : 1 ≤ n ∧ 1 ≤ i ∧ i ≤ d
    · obtain ⟨A, hA⟩ :=
        online_ov_bounds_by_induction n d i h.1 h.2.1 h.2.2
      exact ⟨A, fun _ => hA⟩
    · exact ⟨fallback n d, fun hadm => (h hadm).elim⟩
  choose OV hOV using hex
  refine ⟨OV, ?_⟩
  intro n d i hn hi hid
  exact hOV n d i ⟨hn, hi, hid⟩

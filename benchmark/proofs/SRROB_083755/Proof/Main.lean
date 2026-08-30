import Architect
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.BitVec
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.ProductMeasure

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:random-tape"
  (statement := /-- A random tape is an infinite sequence of bits, indexed by the natural numbers. -/)
  (title := /-- Infinite random tape -/)
  (latexEnv := "definition")]
abbrev random_tape : Type := ℕ → Bool

@[blueprint "def:fair-bit-measure"
  (statement := /-- The fair-bit measure is the Bernoulli probability measure on $\{\mathtt{false},\mathtt{true}\}$ that assigns probability $1/2$ to each bit. -/)
  (title := /-- Fair-bit measure -/)
  (latexEnv := "definition")]
noncomputable def fair_bit_measure : MeasureTheory.Measure Bool :=
  ProbabilityTheory.bernoulliMeasure false true
    ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩

@[blueprint "def:fair-random-tape-measure"
  (statement := /-- The fair random-tape measure is the countable product of the fair-bit measure from \cref{def:fair-bit-measure}, one factor for every tape position. -/)
  (title := /-- Fair product measure on random tapes -/)
  (latexEnv := "definition")]
noncomputable def fair_random_tape_measure : MeasureTheory.Measure random_tape :=
  MeasureTheory.Measure.infinitePi (fun _ : ℕ => fair_bit_measure)

@[blueprint "def:static-retrieval-instance"
  (statement := /-- For natural numbers $U,n,V$, a static retrieval instance consists of a set $S\subseteq\operatorname{Fin}(U)$ of cardinality $n$ and an assignment of a value in $\operatorname{Fin}(V)$ to every universe element.  Only the values at elements of $S$ are part of the retrieval requirement; values outside $S$ are immaterial. -/)
  (title := /-- Static retrieval instance -/)
  (latexEnv := "definition")]
structure static_retrieval_instance (U n V : ℕ) where
  keySet : Finset (Fin U)
  keySet_card : keySet.card = n
  value : Fin U → Fin V

@[blueprint "def:retrieval-probe-tree"
  (statement := /-- For a memory of $m$ cells of $w$ bits and an answer range $\operatorname{Fin}(V)$, a retrieval probe tree is a finite adaptive computation.  A leaf returns an element of $\operatorname{Fin}(V)$, while an internal node selects a cell address and chooses its continuation as a function of the $w$-bit word read from that cell. -/)
  (title := /-- Adaptive cell-probe query tree -/)
  (latexEnv := "definition")]
inductive retrieval_probe_tree (m w V : ℕ) where
  | answer : Fin V → retrieval_probe_tree m w V
  | probe : Fin m → (BitVec w → retrieval_probe_tree m w V) →
      retrieval_probe_tree m w V

@[blueprint "def:execute-retrieval-probe-tree"
  (statement := /-- Given a memory $D:\operatorname{Fin}(m)\to\operatorname{BitVec}(w)$, execution follows the unique branch selected by the contents of each probed cell and returns the element of $\operatorname{Fin}(V)$ stored at the resulting leaf. -/)
  (title := /-- Execution of a probe tree -/)
  (latexEnv := "definition")]
def execute_retrieval_probe_tree {m w V : ℕ}
    (memory : Fin m → BitVec w) : retrieval_probe_tree m w V → Fin V
  | .answer output => output
  | .probe address next =>
      execute_retrieval_probe_tree memory (next (memory address))

@[blueprint "def:count-retrieval-probes"
  (statement := /-- For a fixed memory and probe tree, the query cost is the number of internal nodes visited along the execution path. -/)
  (title := /-- Number of cell probes -/)
  (latexEnv := "definition")]
def count_retrieval_probes {m w V : ℕ}
    (memory : Fin m → BitVec w) : retrieval_probe_tree m w V → ℕ
  | .answer _ => 0
  | .probe address next =>
      1 + count_retrieval_probes memory (next (memory address))

@[blueprint "def:probed-cells-upto"
  (statement := /-- Let $D:\operatorname{Fin}(m)\to\operatorname{BitVec}(w)$ be a memory, let $L$ be a natural number, and let $Q$ be a probe tree of \cref{def:retrieval-probe-tree}.  The truncated probe set of $Q$ at budget $L$ collects the addresses probed along the execution path of \cref{def:execute-retrieval-probe-tree} during its first $L$ probes: it is empty if $L=0$ or if $Q$ is a leaf, and for $L=L'+1$ and $Q$ the probe node with address $i$ and continuation $Q'$ it is $\{i\}$ together with the truncated probe set, at budget $L'$, of the continuation $Q'(D(i))$ selected by the content of cell $i$.  An immediate induction on $L$ shows that this set has at most $L$ elements, and that it contains every cell read by the execution whenever the probe count of \cref{def:count-retrieval-probes} is at most $L$. -/)
  (title := /-- Truncated set of probed cells -/)
  (latexEnv := "definition")]
def probed_cells_upto {m w V : ℕ} (memory : Fin m → BitVec w) :
    ℕ → retrieval_probe_tree m w V → Finset (Fin m)
  | 0, _ => ∅
  | _ + 1, .answer _ => ∅
  | L + 1, .probe address next =>
      insert address (probed_cells_upto memory L (next (memory address)))

@[blueprint "def:untouched-cells"
  (statement := /-- Let $p:\operatorname{Fin}(U)\to\mathcal P(\operatorname{Fin}(m))$ assign to every key a finite set of cell addresses, and let $K\subseteq\operatorname{Fin}(U)$ be a set of keys.  The untouched cells of $K$ under $p$ are the cells outside $\bigcup_{x\in K}p(x)$, that is, the complement in $\operatorname{Fin}(m)$ of the union of the probe sets of the keys of $K$. -/)
  (title := /-- Cells untouched by a set of keys -/)
  (latexEnv := "definition")]
def untouched_cells {U m : ℕ} (probeSet : Fin U → Finset (Fin m))
    (keys : Finset (Fin U)) : Finset (Fin m) :=
  (Finset.univ : Finset (Fin m)) \ keys.biUnion probeSet

@[blueprint "def:randomized-static-retrieval-scheme"
  (statement := /-- A randomized static retrieval scheme for parameters $(U,n,V,w,m)$ consists of an encoder, which maps an instance and an infinite random tape to a memory of $m$ words of $w$ bits, and a query algorithm, which maps a key and the same tape to an adaptive probe tree with answer range $\operatorname{Fin}(V)$.  Its only source of randomness is the tape.  For every instance, stored key, and tape, executing the query tree against the encoded memory must return the assigned value. -/)
  (title := /-- Randomized static retrieval scheme -/)
  (latexEnv := "definition")]
structure randomized_static_retrieval_scheme (U n V w m : ℕ) where
  encode :
    static_retrieval_instance U n V → random_tape → Fin m → BitVec w
  query : Fin U → random_tape → retrieval_probe_tree m w V
  correct :
    ∀ (input : static_retrieval_instance U n V) (x : Fin U),
      x ∈ input.keySet →
      ∀ tape : random_tape,
        execute_retrieval_probe_tree (encode input tape) (query x tape) =
          input.value x

@[blueprint "def:expected-retrieval-query-cost"
  (statement := /-- For a scheme, a fixed instance, and a fixed query key, the expected query cost is the integral of the number of probes over the fair product measure on the infinite random tape from \cref{def:fair-random-tape-measure}. -/)
  (title := /-- Expected query cost -/)
  (latexEnv := "definition")]
noncomputable def expected_retrieval_query_cost {U n V w m : ℕ}
    (scheme : randomized_static_retrieval_scheme U n V w m)
    (input : static_retrieval_instance U n V) (x : Fin U) : ℝ :=
  ∫ tape : random_tape,
    (count_retrieval_probes (scheme.encode input tape)
      (scheme.query x tape) : ℝ) ∂fair_random_tape_measure

@[blueprint "def:has-expected-query-cost"
  (statement := /-- A randomized scheme has expected query cost at most $t$ if, for every stored instance and every query key $x\in\operatorname{Fin}(U)$ of the universe, the real-valued probe-count function on the fair random tape is integrable and its expectation in \cref{def:expected-retrieval-query-cost} is at most $t$.  The bound is imposed at every universe key, not only at the stored keys: the cell-probe cost of a query is defined for every key, and the cell-sampling argument counts, for each cell, the queries of the whole universe that read it. -/)
  (title := /-- Uniform expected query bound -/)
  (latexEnv := "definition")]
def has_expected_query_cost {U n V w m : ℕ}
    (scheme : randomized_static_retrieval_scheme U n V w m) (t : ℕ) : Prop :=
  ∀ (input : static_retrieval_instance U n V) (x : Fin U),
    MeasureTheory.Integrable
          (fun tape : random_tape =>
            (count_retrieval_probes (scheme.encode input tape)
              (scheme.query x tape) : ℝ))
          fair_random_tape_measure ∧
        expected_retrieval_query_cost scheme input x ≤ (t : ℝ)

@[blueprint "def:polynomial-retrieval-parameters"
  (statement := /-- For fixed polynomial exponents $a,b$, the parameters $(n,U,V,w)$ lie in the retrieval regime if $2n\leq U\leq n^a$, $V\leq n^b$, $1<V$, and $\log_2 V\leq w$.  The condition $1<V$ makes the real value size $\log_2 V$ positive. -/)
  (title := /-- Polynomial parameter regime -/)
  (latexEnv := "definition")]
def polynomial_retrieval_parameters
    (n U V w a b : ℕ) : Prop :=
  2 * n ≤ U ∧ U ≤ n ^ a ∧ V ≤ n ^ b ∧ 1 < V ∧
    Real.logb 2 (V : ℝ) ≤ (w : ℝ)

@[blueprint "def:retrieval-space-threshold"
  (statement := /-- For a positive real constant $C$, the asserted bit-space threshold is
  \[
    n\log_2 V+
    \left\lfloor n\exp\!\left(-C\frac{wt}{\log_2 V}\right)\right\rfloor .
  \]
  The floor term is a natural number coerced to the reals.  In the parameter regime of \cref{def:polynomial-retrieval-parameters}, the denominator $\log_2 V$ is positive. -/)
  (title := /-- Explicit retrieval space threshold -/)
  (latexEnv := "definition")]
noncomputable def retrieval_space_threshold
    (C : ℝ) (n V w t : ℕ) : ℝ :=
  (n : ℝ) * Real.logb 2 (V : ℝ) +
    (Nat.floor
      ((n : ℝ) * Real.exp
        (-C * (((w : ℝ) * (t : ℝ)) / Real.logb 2 (V : ℝ)))) : ℝ)

@[blueprint "lem:retrieval-value-assignments-le-memory-count"
  (statement := /-- Let $U,n,V,w,m$ be natural numbers with $n\leq U$ and $0<V$, and let a randomized static retrieval scheme of \cref{def:randomized-static-retrieval-scheme} for the parameters $(U,n,V,w,m)$ be given.  Then
  \[
    V^{n}\leq 2^{mw}
  \]
  as natural numbers. -/)
  (proof := /-- Since $n\leq U$, the universe $\operatorname{Fin}(U)$ has a subset $S$ with $|S|=n$.  Fix the tape $\tau_0$ that is identically $\mathtt{false}$.  For a function $h:S\to\operatorname{Fin}(V)$ let $I_h$ be the instance of \cref{def:static-retrieval-instance} with key set $S$, cardinality witness $|S|=n$, and value function sending $y\in S$ to $h(y)$ and every $y\notin S$ to the element $0$ of $\operatorname{Fin}(V)$, which exists because $0<V$.

  First, for every $h$ and every $x\in S$,
  \[
    \operatorname{exec}\bigl(\operatorname{encode}(I_h,\tau_0),\operatorname{query}(x,\tau_0)\bigr)=h(x).
  \]
  Indeed, the correctness clause of \cref{def:randomized-static-retrieval-scheme}, applied to the instance $I_h$, the stored key $x$, and the tape $\tau_0$, states that the left-hand side, computed as in \cref{def:execute-retrieval-probe-tree}, equals the value that $I_h$ assigns to $x$, and that value is $h(x)$ because $x\in S$.

  Now consider the map
  \[
    \Psi:h\longmapsto\bigl(i\mapsto\text{the numerical value in }\operatorname{Fin}(2^{w})\text{ of }\operatorname{encode}(I_h,\tau_0)(i)\bigr),
  \]
  from $S\to\operatorname{Fin}(V)$ to $\operatorname{Fin}(m)\to\operatorname{Fin}(2^{w})$, where a $w$-bit word is identified with its numerical value, an identification that is injective.  We claim $\Psi$ is injective.  Suppose $\Psi(h)=\Psi(h')$.  Comparing the two functions at each cell $i$ and using injectivity of that identification gives $\operatorname{encode}(I_h,\tau_0)=\operatorname{encode}(I_{h'},\tau_0)$ as memories.  Let $x\in S$.  The query tree $\operatorname{query}(x,\tau_0)$ depends only on $x$ and $\tau_0$, hence is the same for $I_h$ and $I_{h'}$, so the displayed correctness identity, applied to $h$ and to $h'$, gives
  \[
    h(x)=\operatorname{exec}\bigl(\operatorname{encode}(I_h,\tau_0),\operatorname{query}(x,\tau_0)\bigr)
        =\operatorname{exec}\bigl(\operatorname{encode}(I_{h'},\tau_0),\operatorname{query}(x,\tau_0)\bigr)=h'(x).
  \]
  As $x\in S$ was arbitrary, $h=h'$, proving the claim.

  Counting the domain and codomain of an injection between finite types,
  \[
    V^{n}=V^{|S|}=\bigl|S\to\operatorname{Fin}(V)\bigr|
      \leq\bigl|\operatorname{Fin}(m)\to\operatorname{Fin}(2^{w})\bigr|=(2^{w})^{m}=2^{wm}=2^{mw},
  \]
  which is the asserted inequality. -/)
  (title := /-- Counting value assignments against memory configurations -/)
  (latexEnv := "lemma")]
lemma retrieval_value_assignments_le_memory_count :
    ∀ (U n V w m : ℕ)
      (scheme : randomized_static_retrieval_scheme U n V w m),
      n ≤ U → 0 < V → V ^ n ≤ 2 ^ (m * w) := by
  intro U n V w m scheme hnU hV
  classical
  obtain ⟨S, -, hS⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin U))) (n := n)
      (by simpa using hnU)
  have key : ∀ (h : {x : Fin U // x ∈ S} → Fin V) (x : Fin U) (hx : x ∈ S),
      execute_retrieval_probe_tree
          (scheme.encode
            ⟨S, hS, fun y => if hy : y ∈ S then h ⟨y, hy⟩ else ⟨0, hV⟩⟩
            (fun _ => false))
          (scheme.query x (fun _ => false)) = h ⟨x, hx⟩ := by
    intro h x hx
    have hcorrect :=
      scheme.correct
        ⟨S, hS, fun y => if hy : y ∈ S then h ⟨y, hy⟩ else ⟨0, hV⟩⟩ x hx
        (fun _ => false)
    simpa [hx] using hcorrect
  have hinj :
      Function.Injective
        (fun h : {x : Fin U // x ∈ S} → Fin V =>
          fun i : Fin m =>
            (scheme.encode
              ⟨S, hS, fun y => if hy : y ∈ S then h ⟨y, hy⟩ else ⟨0, hV⟩⟩
              (fun _ => false) i).toFin) := by
    intro h h' hEq
    have hmem :
        scheme.encode
            ⟨S, hS, fun y => if hy : y ∈ S then h ⟨y, hy⟩ else ⟨0, hV⟩⟩
            (fun _ => false) =
          scheme.encode
            ⟨S, hS, fun y => if hy : y ∈ S then h' ⟨y, hy⟩ else ⟨0, hV⟩⟩
            (fun _ => false) := by
      funext i
      exact BitVec.toFin_injective (congrFun hEq i)
    funext x
    obtain ⟨x, hx⟩ := x
    rw [← key h x hx, ← key h' x hx, hmem]
  have hcard := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_coe, hS] at hcard
  simp only [Fintype.card_fin] at hcard
  rw [mul_comm m w, pow_mul]
  exact hcard

@[blueprint "lem:logb-two-mul-le-of-pow-le-two-pow"
  (statement := /-- Let $V,n,k$ be natural numbers with $0<V$ and $V^{n}\leq 2^{k}$.  Then
  \[
    n\log_2 V\leq k
  \]
  as real numbers. -/)
  (proof := /-- Since $0<V$, the real number $V$ is positive, hence so is $V^{n}$.  Casting the natural-number inequality $V^{n}\leq 2^{k}$ to the reals gives $V^{n}\leq 2^{k}$ in $\mathbb R$.  The base-$2$ logarithm is monotone on the positive reals because $2>1$, so, the left-hand side being positive,
  \[
    \log_2\bigl(V^{n}\bigr)\leq\log_2\bigl(2^{k}\bigr).
  \]
  The logarithm of a natural power satisfies $\log_2(x^{j})=j\log_2 x$, so the left-hand side equals $n\log_2 V$ and the right-hand side equals $k\log_2 2=k$, using $\log_2 2=1$, which holds because $2>1$.  Combining the two displays yields $n\log_2 V\leq k$. -/)
  (title := /-- From a power bound to a logarithmic bound -/)
  (latexEnv := "lemma")]
lemma logb_two_mul_le_of_pow_le_two_pow :
    ∀ (V n k : ℕ), 0 < V → V ^ n ≤ 2 ^ k →
      (n : ℝ) * Real.logb 2 (V : ℝ) ≤ (k : ℝ) := by
  intro V n k hV hle
  have hVpos : (0 : ℝ) < (V : ℝ) := by exact_mod_cast hV
  have hpow : (0 : ℝ) < (V : ℝ) ^ n := pow_pos hVpos n
  have hcast : ((V : ℝ)) ^ n ≤ (2 : ℝ) ^ k := by exact_mod_cast hle
  have hmono : Real.logb 2 ((V : ℝ) ^ n) ≤ Real.logb 2 ((2 : ℝ) ^ k) :=
    Real.logb_le_logb_of_le (by norm_num) hpow hcast
  rwa [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num),
    mul_one] at hmono

@[blueprint "lem:retrieval-space-at-least-value-bits"
  (statement := /-- Let $U,n,V,w,m$ be natural numbers with $n\leq U$ and $0<V$.  Every randomized static retrieval scheme of \cref{def:randomized-static-retrieval-scheme} for the parameters $(U,n,V,w,m)$ satisfies
  \[
    n\log_2 V\leq mw .
  \]
  This is the plain information-theoretic content of the retrieval requirement, with no reference to query time. -/)
  (proof := /-- Let $U,n,V,w,m$ be natural numbers, let a scheme be given, and assume $n\leq U$ and $0<V$.  Applying \cref{lem:retrieval-value-assignments-le-memory-count} to these data yields the counting bound
  \[
    V^{n}\leq 2^{mw}
  \]
  in the natural numbers.  Applying \cref{lem:logb-two-mul-le-of-pow-le-two-pow} with the exponent $k\coloneqq mw$, using $0<V$ and this counting bound, yields $n\log_2 V\leq mw$ in the reals, where the right-hand side is the cast of the natural number $mw$.  Since the cast of a product of natural numbers is the product of their casts, that cast equals $m\cdot w$ as a product of two real numbers, which is exactly the asserted inequality $n\log_2 V\leq mw$. -/)
  (title := /-- Encoding bound: value bits do not exceed memory bits -/)
  (latexEnv := "lemma")]
lemma retrieval_space_at_least_value_bits :
    ∀ (U n V w m : ℕ)
      (scheme : randomized_static_retrieval_scheme U n V w m),
      n ≤ U → 0 < V →
      (n : ℝ) * Real.logb 2 (V : ℝ) ≤ (m : ℝ) * (w : ℝ) := by
  intro U n V w m scheme hnU hV
  have hcount :=
    retrieval_value_assignments_le_memory_count U n V w m scheme hnU hV
  have hlog :=
    logb_two_mul_le_of_pow_le_two_pow V n (m * w) hV hcount
  rwa [Nat.cast_mul] at hlog

@[blueprint "lem:fair-random-tape-measure-is-probability"
  (statement := /-- The fair random-tape measure of \cref{def:fair-random-tape-measure} is a probability measure: the space of infinite tapes has total mass $1$. -/)
  (proof := /-- By \cref{def:fair-bit-measure} the fair-bit measure is the Bernoulli measure on $\{\mathtt{false},\mathtt{true}\}$ with parameter $1/2$, and a Bernoulli measure whose parameter lies in the unit interval is a probability measure.  By \cref{def:fair-random-tape-measure} the fair random-tape measure is the countable product of one such factor for every tape position, and the product of a family of probability measures is a probability measure. -/)
  (title := /-- The fair tape measure is a probability measure -/)
  (latexEnv := "lemma")]
lemma fair_random_tape_measure_is_probability :
    MeasureTheory.IsProbabilityMeasure fair_random_tape_measure := by
  unfold fair_random_tape_measure fair_bit_measure
  infer_instance

@[blueprint "lem:card-value-functions-fixed-off-key-set"
  (statement := /-- Let $U,V$ be natural numbers, let $c_0\in\operatorname{Fin}(V)$, and let $X\subseteq\operatorname{Fin}(U)$.  The number of functions $g:\operatorname{Fin}(U)\to\operatorname{Fin}(V)$ with $g(x)=c_0$ for every $x\notin X$ equals $V^{|X|}$. -/)
  (proof := /-- Such a $g$ is exactly a member of the product set $\prod_{x}A_x$, where $A_x=\operatorname{Fin}(V)$ for $x\in X$ and $A_x=\{c_0\}$ for $x\notin X$: the membership condition $g(x)\in A_x$ is vacuous for $x\in X$ and says $g(x)=c_0$ for $x\notin X$.  The cardinality of such a product set is $\prod_x|A_x|$, and $|A_x|=V$ for $x\in X$ while $|A_x|=1$ otherwise, so the product equals $\prod_{x\in X}V=V^{|X|}$. -/)
  (title := /-- Counting value functions constant off a key set -/)
  (latexEnv := "lemma")]
lemma card_value_functions_fixed_off_key_set :
    ∀ (U V : ℕ) (c₀ : Fin V) (X : Finset (Fin U)),
      ((Finset.univ : Finset (Fin U → Fin V)).filter
          (fun g => ∀ x : Fin U, x ∉ X → g x = c₀)).card = V ^ X.card := by
  intro U V c₀ X
  classical
  have hset : ((Finset.univ : Finset (Fin U → Fin V)).filter
      (fun g => ∀ x : Fin U, x ∉ X → g x = c₀))
      = Fintype.piFinset
          (fun x : Fin U => if x ∈ X then (Finset.univ : Finset (Fin V)) else {c₀}) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hg x
      by_cases hx : x ∈ X
      · simp [hx]
      · simp [hx, hg x hx]
    · intro hg x hx
      have hgx := hg x
      simp [hx] at hgx
      exact hgx
  rw [hset, Fintype.card_piFinset]
  rw [Finset.prod_congr rfl
    (fun x _ => by by_cases hx : x ∈ X <;> simp [hx] : ∀ x ∈ (Finset.univ : Finset (Fin U)),
      (if x ∈ X then (Finset.univ : Finset (Fin V)) else {c₀}).card
        = if x ∈ X then V else 1)]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

@[blueprint "lem:probe-count-family-integrable-expectation"
  (statement := /-- Let $\iota$ be a type, let $S\subseteq\iota$ be finite, let $p\mapsto I_p$ assign a static retrieval instance of \cref{def:static-retrieval-instance} to every index, and let $p\mapsto K_p$ assign a finite set of query keys.  Let a randomized static retrieval scheme of \cref{def:randomized-static-retrieval-scheme} satisfy the expected-cost hypothesis of \cref{def:has-expected-query-cost} for $t$.  Then the total probe count
  \[
    \tau\mapsto\sum_{p\in S}\sum_{x\in K_p}\operatorname{probes}(I_p,x,\tau),
  \]
  with $\operatorname{probes}$ the count of \cref{def:count-retrieval-probes} of the query tree for $x$ against the memory encoded from $I_p$ on $\tau$, is integrable for the fair random-tape measure of \cref{def:fair-random-tape-measure}, and its integral is at most $\sum_{p\in S}|K_p|\,t$. -/)
  (proof := /-- The natural-number-valued total, cast to the reals, equals the real-valued double sum $\sum_{p\in S}\sum_{x\in K_p}\operatorname{probes}(I_p,x,\tau)$, because casting from the natural numbers to the reals commutes with finite sums.

  For each index $p\in S$ and each key $x\in K_p$, the summand $\tau\mapsto\operatorname{probes}(I_p,x,\tau)$ is integrable by the first clause of \cref{def:has-expected-query-cost}, applied to the instance $I_p$ and the key $x$; this clause is imposed at every universe key, so it is available for every $x$.  A finite sum of integrable functions is integrable, so, applying this twice, the double sum is integrable.  This proves the first assertion.

  For the second, linearity of the Bochner integral over finite sums of integrable functions, applied twice with the integrability just established, gives
  \[
    \int\sum_{p\in S}\sum_{x\in K_p}\operatorname{probes}(I_p,x,\tau)\,d\tau
      =\sum_{p\in S}\sum_{x\in K_p}\int\operatorname{probes}(I_p,x,\tau)\,d\tau .
  \]
  By \cref{def:expected-retrieval-query-cost} the inner integral is the expected query cost of the scheme at the instance $I_p$ and the key $x$, which is at most $t$ by the second clause of \cref{def:has-expected-query-cost}.  Summing these $|K_p|$ bounds over $x\in K_p$ gives $|K_p|\,t$ for each $p$, and summing over $p\in S$ gives $\sum_{p\in S}|K_p|\,t$, as asserted. -/)
  (title := /-- Integrability and expectation of a family of probe counts -/)
  (latexEnv := "lemma")]
lemma probe_count_family_integrable_expectation :
    ∀ (U n V w m t : ℕ) (scheme : randomized_static_retrieval_scheme U n V w m)
      (ι : Type) (S : Finset ι) (inst : ι → static_retrieval_instance U n V)
      (keys : ι → Finset (Fin U)),
      has_expected_query_cost scheme t →
      MeasureTheory.Integrable
          (fun tape : random_tape =>
            ((∑ p ∈ S, ∑ x ∈ keys p,
              count_retrieval_probes (scheme.encode (inst p) tape)
                (scheme.query x tape) : ℕ) : ℝ))
          fair_random_tape_measure ∧
        ∫ tape : random_tape,
            ((∑ p ∈ S, ∑ x ∈ keys p,
              count_retrieval_probes (scheme.encode (inst p) tape)
                (scheme.query x tape) : ℕ) : ℝ) ∂fair_random_tape_measure
          ≤ ∑ p ∈ S, ((keys p).card : ℝ) * (t : ℝ) := by
  intro U n V w m t scheme ι S inst keys hcost
  have hpush : ∀ tape : random_tape,
      ((∑ p ∈ S, ∑ x ∈ keys p,
          count_retrieval_probes (scheme.encode (inst p) tape)
            (scheme.query x tape) : ℕ) : ℝ)
        = ∑ p ∈ S, ∑ x ∈ keys p,
            ((count_retrieval_probes (scheme.encode (inst p) tape)
              (scheme.query x tape) : ℕ) : ℝ) := by
    intro tape
    push_cast
    rfl
  have hint : MeasureTheory.Integrable
      (fun tape : random_tape =>
        ∑ p ∈ S, ∑ x ∈ keys p,
          ((count_retrieval_probes (scheme.encode (inst p) tape)
            (scheme.query x tape) : ℕ) : ℝ))
      fair_random_tape_measure := by
    refine MeasureTheory.integrable_finsetSum _ (fun p _ => ?_)
    exact MeasureTheory.integrable_finsetSum _ (fun x _ => (hcost (inst p) x).1)
  constructor
  · simp only [hpush]
    exact hint
  · simp only [hpush]
    rw [MeasureTheory.integral_finsetSum _ (fun p _ =>
      MeasureTheory.integrable_finsetSum _ (fun x _ => (hcost (inst p) x).1))]
    refine Finset.sum_le_sum (fun p _ => ?_)
    rw [MeasureTheory.integral_finsetSum _ (fun x _ => (hcost (inst p) x).1)]
    calc (∑ x ∈ keys p, ∫ tape : random_tape,
            ((count_retrieval_probes (scheme.encode (inst p) tape)
              (scheme.query x tape) : ℕ) : ℝ) ∂fair_random_tape_measure)
        ≤ ∑ _x ∈ keys p, (t : ℝ) := Finset.sum_le_sum (fun x _ => (hcost (inst p) x).2)
      _ = ((keys p).card : ℝ) * (t : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]

@[blueprint "lem:card-normalized-instances"
  (statement := /-- Let $U,n,V$ be natural numbers and let $c_0\in\operatorname{Fin}(V)$.  Call a pair $(X,g)$, consisting of a set $X\subseteq\operatorname{Fin}(U)$ and a function $g:\operatorname{Fin}(U)\to\operatorname{Fin}(V)$, normalized if $|X|=n$ and $g(x)=c_0$ for every $x\notin X$.  The number of normalized pairs equals $\binom Un V^{n}$. -/)
  (proof := /-- Counting the pairs in the product of the finite type of sets $X$ with the finite type of functions $g$, the number of normalized pairs is
  \[
    \sum_{X}\sum_{g}\mathbf 1\bigl[|X|=n\ \text{and}\ g=c_0\ \text{off}\ X\bigr]
      =\sum_{X}\mathbf 1[|X|=n]\cdot\#\{g:g=c_0\ \text{off}\ X\},
  \]
  since for $|X|\neq n$ the inner sum vanishes term by term.  For $|X|=n$, \cref{lem:card-value-functions-fixed-off-key-set} evaluates the inner count as $V^{|X|}=V^{n}$.  Hence the total equals $V^{n}$ times the number of sets $X\subseteq\operatorname{Fin}(U)$ with $|X|=n$.  The sets of size $n$ inside a universe of size $U$ are exactly the $n$-element members of the powerset of $\operatorname{Fin}(U)$, and there are $\binom Un$ of them.  Therefore the number of normalized pairs is $\binom UnV^{n}$. -/)
  (title := /-- The number of normalized instances -/)
  (latexEnv := "lemma")]
lemma card_normalized_instances :
    ∀ (U n V : ℕ) (c₀ : Fin V),
      ((Finset.univ : Finset (Finset (Fin U) × (Fin U → Fin V))).filter
          (fun p => p.1.card = n ∧ ∀ x : Fin U, x ∉ p.1 → p.2 x = c₀)).card
        = Nat.choose U n * V ^ n := by
  intro U n V c₀
  classical
  rw [← Finset.univ_product_univ, Finset.card_filter, Finset.sum_product]
  have h1 : ∀ X : Finset (Fin U),
      (∑ g : Fin U → Fin V,
        if X.card = n ∧ ∀ x : Fin U, x ∉ X → g x = c₀ then 1 else 0)
        = if X.card = n then V ^ n else 0 := by
    intro X
    by_cases hX : X.card = n
    · simp only [hX, true_and, if_true]
      rw [← Finset.card_filter, card_value_functions_fixed_off_key_set U V c₀ X, hX]
    · simp [hX]
  rw [Finset.sum_congr rfl (fun X _ => h1 X), ← Finset.sum_filter, Finset.sum_const,
    smul_eq_mul]
  congr 1
  have hpow : (Finset.univ : Finset (Finset (Fin U))).filter (fun X => X.card = n)
      = Finset.powersetCard n (Finset.univ : Finset (Fin U)) := by
    rw [Finset.powersetCard_eq_filter, Finset.powerset_univ]
  rw [hpow, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

@[blueprint "lem:few-indices-exceed-ten-times-average"
  (statement := /-- Let $P$ be a finite index set, let $f:P\to\mathbb N$, and let $K$ be a positive natural number with $\sum_{p\in P}f(p)\leq 2|P|K$.  Then
  \[
    10\,\bigl|\{p\in P:f(p)>20K\}\bigr|\leq|P| .
  \] -/)
  (proof := /-- Write $B\coloneqq\{p\in P:f(p)>20K\}$, a subset of $P$.  Every $p\in B$ satisfies $f(p)\geq 20K$, so bounding each term of the sum over $B$ from below by $20K$ gives $20K\,|B|\leq\sum_{p\in B}f(p)$.  Since $f$ takes nonnegative values and $B\subseteq P$, we have $\sum_{p\in B}f(p)\leq\sum_{p\in P}f(p)$, and the hypothesis bounds the latter by $2|P|K$.  Chaining the three estimates,
  \[
    20K\,|B|\leq 2|P|K .
  \]
  Because $K>0$ we may cancel the factor $2K$, obtaining $10|B|\leq|P|$, as asserted. -/)
  (title := /-- Markov bound for a finite family of counts -/)
  (latexEnv := "lemma")]
lemma few_indices_exceed_ten_times_average :
    ∀ (ι : Type) (P : Finset ι) (f : ι → ℕ) (K : ℕ),
      0 < K → (∑ p ∈ P, f p) ≤ 2 * P.card * K →
      10 * (P.filter (fun p => 20 * K < f p)).card ≤ P.card := by
  intro ι P f K hK hsum
  classical
  set B := P.filter (fun p => 20 * K < f p) with hB
  have hsub : B ⊆ P := Finset.filter_subset _ _
  have hlow : B.card * (20 * K) ≤ ∑ p ∈ B, f p := by
    have := Finset.card_nsmul_le_sum B f (20 * K) (fun p hp => by
      have hp' : 20 * K < f p := (Finset.mem_filter.mp hp).2
      omega)
    simpa [smul_eq_mul, mul_comm] using this
  have hmono : (∑ p ∈ B, f p) ≤ ∑ p ∈ P, f p :=
    Finset.sum_le_sum_of_subset hsub
  have hchain : B.card * (20 * K) ≤ 2 * P.card * K := le_trans hlow (le_trans hmono hsum)
  have h2 : (10 * B.card) * (2 * K) ≤ P.card * (2 * K) := by
    calc (10 * B.card) * (2 * K) = B.card * (20 * K) := by ring
      _ ≤ 2 * P.card * K := hchain
      _ = P.card * (2 * K) := by ring
  exact Nat.le_of_mul_le_mul_right h2 (by omega)

@[blueprint "lem:exists-good-random-tape"
  (statement := /-- Let $U,n,V,w,m,t$ be natural numbers with $0<n$, $n\leq U$ and $0<t$, let $c_0\in\operatorname{Fin}(V)$, and let a randomized static retrieval scheme of \cref{def:randomized-static-retrieval-scheme} satisfy the expected-cost hypothesis of \cref{def:has-expected-query-cost} for $t$.  Call a pair $(X,g)$, with $X\subseteq\operatorname{Fin}(U)$ of cardinality $n$ and $g:\operatorname{Fin}(U)\to\operatorname{Fin}(V)$ equal to $c_0$ off $X$, a normalized instance; there are exactly $\binom Un V^{n}$ of them.  Then there exist one tape $\tau$ and a set $\mathcal G$ of normalized instances with
  \[
    4\binom Un V^{n}\leq 5\,|\mathcal G| ,
  \]
  such that every $(X,g)\in\mathcal G$, written as the instance $I=(X,g)$ of \cref{def:static-retrieval-instance}, satisfies the two deterministic probe bounds
  \[
    \sum_{x\in\operatorname{Fin}(U)}\operatorname{probes}(I,x,\tau)\leq 20Ut,
    \qquad
    \sum_{x\in X}\operatorname{probes}(I,x,\tau)\leq 20nt,
  \]
  where $\operatorname{probes}(I,x,\tau)$ is the probe count of \cref{def:count-retrieval-probes} of the query tree for $x$ against the memory encoded from $I$ on $\tau$. -/)
  (proof := /-- From $0<n$ and $n\leq U$ we get $0<U$.  Since $n\leq U=|\operatorname{Fin}(U)|$, the universe contains at least one subset $X_0$ of cardinality exactly $n$; fix such an $X_0$.  For a pair $p=(X,g)$ define the instance $I_p$ of \cref{def:static-retrieval-instance} to be $(X,g)$ when $|X|=n$, using that equality as the cardinality witness, and the auxiliary instance $(X_0,g)$ otherwise; the second branch never occurs for normalized pairs and serves only to make $p\mapsto I_p$ total.  Let $P$ be the finite set of normalized pairs, that is, the pairs $p$ with $|X|=n$ and $g(x)=c_0$ for every $x\notin X$.

  \emph{Step 1: two expectation bounds.}  For a tape $\tau$ put
  \[
    A(\tau)\coloneqq\sum_{p\in P}\sum_{x\in\operatorname{Fin}(U)}\operatorname{probes}(I_p,x,\tau),
    \qquad
    B(\tau)\coloneqq\sum_{p\in P}\sum_{x\in X_p}\operatorname{probes}(I_p,x,\tau),
  \]
  where $X_p$ is the first component of $p$ and $\operatorname{probes}(I,x,\tau)$ is the count of \cref{def:count-retrieval-probes} of the query tree for $x$ against the memory encoded from $I$ on $\tau$.  Applying \cref{lem:probe-count-family-integrable-expectation} to the family $P$ with key sets $\operatorname{Fin}(U)$, and then again with key sets $X_p$, shows that $A$ and $B$ are integrable for the measure of \cref{def:fair-random-tape-measure} and that
  \[
    \mathbb E[A]\leq\sum_{p\in P}Ut=|P|\,Ut,
    \qquad
    \mathbb E[B]\leq\sum_{p\in P}|X_p|\,t=|P|\,nt,
  \]
  the last equality because $|X_p|=n$ for every $p\in P$ by the definition of $P$.

  \emph{Step 2: one tape good for both bounds.}  The function $\tau\mapsto n\,A(\tau)+U\,B(\tau)$ is integrable, being a linear combination of the two integrable functions of Step 1.  By \cref{lem:fair-random-tape-measure-is-probability} the fair random-tape measure is a probability measure, so the first moment method provides a tape $\tau$ with
  \[
    n\,A(\tau)+U\,B(\tau)\leq n\,\mathbb E[A]+U\,\mathbb E[B]\leq 2|P|\,nUt .
  \]
  Fix this $\tau$ and abbreviate $g_1(p)\coloneqq\sum_{x\in\operatorname{Fin}(U)}\operatorname{probes}(I_p,x,\tau)$ and $g_2(p)\coloneqq\sum_{x\in X_p}\operatorname{probes}(I_p,x,\tau)$, so that $A(\tau)=\sum_{p\in P}g_1(p)$ and $B(\tau)=\sum_{p\in P}g_2(p)$.  Both $n\,A(\tau)$ and $U\,B(\tau)$ are nonnegative, so each is at most $2|P|\,nUt$ on its own.  Cancelling the positive factor $n$ in the first and the positive factor $U$ in the second yields
  \[
    \sum_{p\in P}g_1(p)\leq 2|P|\,(Ut),
    \qquad
    \sum_{p\in P}g_2(p)\leq 2|P|\,(nt),
  \]
  where these inequalities between natural numbers follow from the corresponding real inequalities by injectivity of the cast.

  \emph{Step 3: discarding the two bad families.}  Since $0<U$ and $0<t$ we have $Ut>0$, and since $0<n$ and $0<t$ we have $nt>0$.  Applying \cref{lem:few-indices-exceed-ten-times-average} to $g_1$ with $K\coloneqq Ut$ and to $g_2$ with $K\coloneqq nt$, using the two sums of Step 2, gives
  \[
    10\,\bigl|\{p\in P:g_1(p)>20Ut\}\bigr|\leq|P|,
    \qquad
    10\,\bigl|\{p\in P:g_2(p)>20nt\}\bigr|\leq|P| .
  \]
  Define $\mathcal G\coloneqq\{p\in P:g_1(p)\leq 20Ut\ \text{and}\ g_2(p)\leq 20nt\}$.  Every $p\in\mathcal G$ lies in $P$, hence satisfies $|X_p|=n$ and $g_p=c_0$ off $X_p$, which are the first two required properties.

  For the cardinality bound, split $P$ according to whether $g_1(p)\leq 20Ut$, and split the first part according to whether $g_2(p)\leq 20nt$: the two splittings give
  \[
    |P|=\bigl|\{p\in P:g_1(p)\leq 20Ut\}\bigr|+\bigl|\{p\in P:g_1(p)>20Ut\}\bigr|
  \]
  and $\bigl|\{p\in P:g_1(p)\leq 20Ut\}\bigr|=|\mathcal G|+D$, where $D$ counts the $p$ with $g_1(p)\leq 20Ut$ and $g_2(p)>20nt$.  The set counted by $D$ is contained in $\{p\in P:g_2(p)>20nt\}$, so $10D\leq|P|$.  Combining the two displayed decompositions with the two bounds of this step gives $4|P|\leq 5|\mathcal G|$.  By \cref{lem:card-normalized-instances} we have $|P|=\binom UnV^{n}$, so this is the asserted inequality $4\binom UnV^{n}\leq5|\mathcal G|$.

  Finally, let $p\in\mathcal G$ and let $h$ be any proof that $|X_p|=n$.  Then $I_p$ is, by the first branch of its definition, the instance $(X_p,g_p)$ with cardinality witness $h$, so the two membership conditions defining $\mathcal G$ read exactly $\sum_{x\in\operatorname{Fin}(U)}\operatorname{probes}(I_p,x,\tau)\leq 20Ut$ and $\sum_{x\in X_p}\operatorname{probes}(I_p,x,\tau)\leq 20nt$, which after reassociating the products $20\cdot(Ut)=20\cdot U\cdot t$ and $20\cdot(nt)=20\cdot n\cdot t$ are the two required deterministic probe bounds. -/)
  (title := /-- One tape good for four fifths of the instances -/)
  (latexEnv := "lemma")]
lemma exists_good_random_tape :
    ∀ (U n V w m t : ℕ)
      (scheme : randomized_static_retrieval_scheme U n V w m)
      (c₀ : Fin V),
      0 < n → n ≤ U → 0 < t →
      has_expected_query_cost scheme t →
      ∃ tape : random_tape,
        ∃ good : Finset (Finset (Fin U) × (Fin U → Fin V)),
          (∀ p ∈ good, p.1.card = n) ∧
          (∀ p ∈ good, ∀ x : Fin U, x ∉ p.1 → p.2 x = c₀) ∧
          4 * (Nat.choose U n * V ^ n) ≤ 5 * good.card ∧
          (∀ p ∈ good, ∀ h : p.1.card = n,
            (∑ x : Fin U,
                count_retrieval_probes
                  (scheme.encode ⟨p.1, h, p.2⟩ tape)
                  (scheme.query x tape)) ≤ 20 * U * t ∧
            (∑ x ∈ p.1,
                count_retrieval_probes
                  (scheme.encode ⟨p.1, h, p.2⟩ tape)
                  (scheme.query x tape)) ≤ 20 * n * t) := by
  intro U n V w m t scheme c₀ hn hnU ht hcost
  haveI : MeasureTheory.IsProbabilityMeasure fair_random_tape_measure :=
    fair_random_tape_measure_is_probability
  have hU : 0 < U := lt_of_lt_of_le hn hnU
  obtain ⟨X₀, hX₀⟩ : ∃ X : Finset (Fin U), X.card = n := by
    obtain ⟨X, -, hX⟩ := Finset.exists_subset_card_eq
      (show n ≤ (Finset.univ : Finset (Fin U)).card by simpa using hnU)
    exact ⟨X, hX⟩
  set inst : Finset (Fin U) × (Fin U → Fin V) → static_retrieval_instance U n V :=
    fun p => if h : p.1.card = n then ⟨p.1, h, p.2⟩ else ⟨X₀, hX₀, p.2⟩ with hinst
  set P := (Finset.univ : Finset (Finset (Fin U) × (Fin U → Fin V))).filter
      (fun p => p.1.card = n ∧ ∀ x : Fin U, x ∉ p.1 → p.2 x = c₀) with hPdef
  obtain ⟨hAint, hAbd⟩ := probe_count_family_integrable_expectation U n V w m t scheme
      (Finset (Fin U) × (Fin U → Fin V)) P inst (fun _ => Finset.univ) hcost
  obtain ⟨hBint, hBbd⟩ := probe_count_family_integrable_expectation U n V w m t scheme
      (Finset (Fin U) × (Fin U → Fin V)) P inst (fun p => p.1) hcost
  have hAbd' : ∫ tape : random_tape,
      ((∑ p ∈ P, ∑ _x : Fin U,
        count_retrieval_probes (scheme.encode (inst p) tape)
          (scheme.query _x tape) : ℕ) : ℝ) ∂fair_random_tape_measure
      ≤ (P.card : ℝ) * ((U : ℝ) * (t : ℝ)) := by
    refine le_trans hAbd (le_of_eq ?_)
    simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hBbd' : ∫ tape : random_tape,
      ((∑ p ∈ P, ∑ x ∈ p.1,
        count_retrieval_probes (scheme.encode (inst p) tape)
          (scheme.query x tape) : ℕ) : ℝ) ∂fair_random_tape_measure
      ≤ (P.card : ℝ) * ((n : ℝ) * (t : ℝ)) := by
    refine le_trans hBbd (le_of_eq ?_)
    have hterm : ∀ p ∈ P, ((p.1.card : ℝ)) * (t : ℝ) = (n : ℝ) * (t : ℝ) := by
      intro p hp
      rw [(Finset.mem_filter.mp hp).2.1]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  have hGint : MeasureTheory.Integrable
      (fun tape : random_tape =>
        (n : ℝ) * ((∑ p ∈ P, ∑ _x : Fin U,
            count_retrieval_probes (scheme.encode (inst p) tape)
              (scheme.query _x tape) : ℕ) : ℝ)
          + (U : ℝ) * ((∑ p ∈ P, ∑ x ∈ p.1,
            count_retrieval_probes (scheme.encode (inst p) tape)
              (scheme.query x tape) : ℕ) : ℝ))
      fair_random_tape_measure := (hAint.const_mul _).add (hBint.const_mul _)
  obtain ⟨tape, htape⟩ := MeasureTheory.exists_le_integral hGint
  rw [MeasureTheory.integral_add (hAint.const_mul _) (hBint.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at htape
  set g₁ : Finset (Fin U) × (Fin U → Fin V) → ℕ := fun p =>
    ∑ x : Fin U, count_retrieval_probes (scheme.encode (inst p) tape)
      (scheme.query x tape) with hg1
  set g₂ : Finset (Fin U) × (Fin U → Fin V) → ℕ := fun p =>
    ∑ x ∈ p.1, count_retrieval_probes (scheme.encode (inst p) tape)
      (scheme.query x tape) with hg2
  have hnonneg₁ : (0 : ℝ) ≤ (n : ℝ) * ((∑ p ∈ P, g₁ p : ℕ) : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hnonneg₂ : (0 : ℝ) ≤ (U : ℝ) * ((∑ p ∈ P, g₂ p : ℕ) : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hsum₁ : (∑ p ∈ P, g₁ p) ≤ 2 * P.card * (U * t) := by
    have hreal : (n : ℝ) * ((∑ p ∈ P, g₁ p : ℕ) : ℝ)
        ≤ (n : ℝ) * ((2 : ℝ) * (P.card : ℝ) * ((U : ℝ) * (t : ℝ))) := by
      nlinarith [htape, hAbd', hBbd', hnonneg₂, Nat.cast_nonneg (α := ℝ) n,
        Nat.cast_nonneg (α := ℝ) U]
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hkey := le_of_mul_le_mul_left hreal hn'
    exact_mod_cast hkey
  have hsum₂ : (∑ p ∈ P, g₂ p) ≤ 2 * P.card * (n * t) := by
    have hreal : (U : ℝ) * ((∑ p ∈ P, g₂ p : ℕ) : ℝ)
        ≤ (U : ℝ) * ((2 : ℝ) * (P.card : ℝ) * ((n : ℝ) * (t : ℝ))) := by
      nlinarith [htape, hAbd', hBbd', hnonneg₁, Nat.cast_nonneg (α := ℝ) n,
        Nat.cast_nonneg (α := ℝ) U]
    have hU' : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hU
    have hkey := le_of_mul_le_mul_left hreal hU'
    exact_mod_cast hkey
  have hbad₁ : 10 * (P.filter (fun p => 20 * (U * t) < g₁ p)).card ≤ P.card :=
    few_indices_exceed_ten_times_average _ P g₁ (U * t) (Nat.mul_pos hU ht) hsum₁
  have hbad₂ : 10 * (P.filter (fun p => 20 * (n * t) < g₂ p)).card ≤ P.card :=
    few_indices_exceed_ten_times_average _ P g₂ (n * t) (Nat.mul_pos hn ht) hsum₂
  classical
  refine ⟨tape, (P.filter (fun p => g₁ p ≤ 20 * (U * t))).filter
    (fun p => g₂ p ≤ 20 * (n * t)), ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).2.1
  · intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).2.2
  · have hcard : P.card = Nat.choose U n * V ^ n :=
      card_normalized_instances U n V c₀
    have hsplit₁ : (P.filter (fun p => g₁ p ≤ 20 * (U * t))).card
        + (P.filter (fun p => ¬ g₁ p ≤ 20 * (U * t))).card = P.card :=
      Finset.filter_card_add_filter_neg_card_eq_card _
    have hsplit₂ : ((P.filter (fun p => g₁ p ≤ 20 * (U * t))).filter
          (fun p => g₂ p ≤ 20 * (n * t))).card
        + ((P.filter (fun p => g₁ p ≤ 20 * (U * t))).filter
          (fun p => ¬ g₂ p ≤ 20 * (n * t))).card
        = (P.filter (fun p => g₁ p ≤ 20 * (U * t))).card :=
      Finset.filter_card_add_filter_neg_card_eq_card _
    have hle₁ : (P.filter (fun p => ¬ g₁ p ≤ 20 * (U * t))).card
        = (P.filter (fun p => 20 * (U * t) < g₁ p)).card := by
      congr 1
      exact Finset.filter_congr (fun p _ => by simp [Nat.not_le])
    have hle₂ : ((P.filter (fun p => g₁ p ≤ 20 * (U * t))).filter
          (fun p => ¬ g₂ p ≤ 20 * (n * t))).card
        ≤ (P.filter (fun p => 20 * (n * t) < g₂ p)).card := by
      refine Finset.card_le_card (fun p hp => ?_)
      have h1 := Finset.mem_filter.mp hp
      have h2 := Finset.mem_filter.mp h1.1
      exact Finset.mem_filter.mpr ⟨h2.1, by omega⟩
    rw [← hcard]
    omega
  · intro p hp h
    have hinstp : inst p = ⟨p.1, h, p.2⟩ := dif_pos h
    have h1 : g₁ p ≤ 20 * (U * t) := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    have h2 : g₂ p ≤ 20 * (n * t) := (Finset.mem_filter.mp hp).2
    rw [hg1] at h1
    rw [hg2] at h2
    simp only [hinstp] at h1 h2
    exact ⟨by simpa [mul_assoc] using h1, by simpa [mul_assoc] using h2⟩

@[blueprint "lem:untouched-cells-sum-eq-choose-sum"
  (statement := /-- Let $U,m,n$ be natural numbers and let $p:\operatorname{Fin}(U)\to\mathcal P(\operatorname{Fin}(m))$ assign a finite set of cells to every key.  For a cell $i\in\operatorname{Fin}(m)$ write $a_i\coloneqq|\{x\in\operatorname{Fin}(U):i\in p(x)\}|$ for its load.  Then, with untouched cells as in \cref{def:untouched-cells},
  \[
    \sum_{X}\bigl|\operatorname{untouched}(p,X)\bigr|=\sum_{i\in\operatorname{Fin}(m)}\binom{U-a_i}{n},
  \]
  the left-hand sum ranging over all $X\subseteq\operatorname{Fin}(U)$ with $|X|=n$.  Both sides are natural numbers. -/)
  (proof := /-- By \cref{def:untouched-cells}, $\operatorname{untouched}(p,X)$ is the set of cells $i$ with $i\notin\bigcup_{x\in X}p(x)$, so its cardinality equals $\sum_{i\in\operatorname{Fin}(m)}[\,i\notin\bigcup_{x\in X}p(x)\,]$, where $[\cdot]$ denotes the indicator taking the value $1$ when the condition holds and $0$ otherwise.  Summing over all $n$-element sets $X$ and exchanging the two finite sums,
  \[
    \sum_{X}\bigl|\operatorname{untouched}(p,X)\bigr|
      =\sum_{i\in\operatorname{Fin}(m)}\#\bigl\{X:|X|=n,\ i\notin\textstyle\bigcup_{x\in X}p(x)\bigr\}.
  \]
  Fix $i$.  The condition $i\notin\bigcup_{x\in X}p(x)$ says exactly that $i\notin p(x)$ for every $x\in X$, that is, that $X$ is contained in the set $A_i\coloneqq\{x\in\operatorname{Fin}(U):i\notin p(x)\}$.  Hence the $n$-element sets $X$ counted for $i$ are precisely the $n$-element subsets of $A_i$, and there are $\binom{|A_i|}{n}$ of them.  Finally $A_i$ is the complement in $\operatorname{Fin}(U)$ of the set $\{x:i\in p(x)\}$ of cardinality $a_i$, so $|A_i|=U-a_i$.  Substituting gives the asserted identity. -/)
  (title := /-- Untouched cells counted cell by cell -/)
  (latexEnv := "lemma")]
lemma untouched_cells_sum_eq_choose_sum :
    ∀ (U m n : ℕ) (probeSet : Fin U → Finset (Fin m)),
      ∑ X ∈ Finset.powersetCard n (Finset.univ : Finset (Fin U)),
          (untouched_cells probeSet X).card
        = ∑ i : Fin m,
            Nat.choose
              (U - ((Finset.univ : Finset (Fin U)).filter
                (fun x : Fin U => i ∈ probeSet x)).card) n := by
  intro U m n probeSet
  have hcard : ∀ X : Finset (Fin U),
      (untouched_cells probeSet X).card
        = ∑ i : Fin m, if i ∉ X.biUnion probeSet then 1 else 0 := by
    intro X
    simp only [untouched_cells, Finset.sdiff_eq_filter, Finset.card_filter]
  have hfilter : ∀ i : Fin m,
      (Finset.powersetCard n (Finset.univ : Finset (Fin U))).filter
          (fun X => i ∉ X.biUnion probeSet)
        = Finset.powersetCard n
            ((Finset.univ : Finset (Fin U)).filter (fun x : Fin U => i ∉ probeSet x)) := by
    intro i
    ext X
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_biUnion, not_exists,
      not_and, Finset.subset_iff, Finset.mem_univ, true_and]
    tauto
  calc ∑ X ∈ Finset.powersetCard n (Finset.univ : Finset (Fin U)),
          (untouched_cells probeSet X).card
      = ∑ X ∈ Finset.powersetCard n (Finset.univ : Finset (Fin U)),
          ∑ i : Fin m, if i ∉ X.biUnion probeSet then 1 else 0 :=
        Finset.sum_congr rfl (fun X _ => hcard X)
    _ = ∑ i : Fin m, ∑ X ∈ Finset.powersetCard n (Finset.univ : Finset (Fin U)),
          if i ∉ X.biUnion probeSet then 1 else 0 := Finset.sum_comm
    _ = ∑ i : Fin m, ((Finset.powersetCard n (Finset.univ : Finset (Fin U))).filter
          (fun X => i ∉ X.biUnion probeSet)).card :=
        Finset.sum_congr rfl (fun i _ => (Finset.card_filter _ _).symm)
    _ = ∑ i : Fin m, Nat.choose
          (U - ((Finset.univ : Finset (Fin U)).filter
            (fun x : Fin U => i ∈ probeSet x)).card) n := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hfilter i, Finset.card_powersetCard]
        congr 1
        simp [Finset.card_compl, ← Finset.compl_filter]

@[blueprint "lem:cell-load-sum-eq-probe-card-sum"
  (statement := /-- Let $U,m$ be natural numbers and let $p:\operatorname{Fin}(U)\to\mathcal P(\operatorname{Fin}(m))$ assign a finite set of cells to every key.  Then
  \[
    \sum_{i\in\operatorname{Fin}(m)}\bigl|\{x\in\operatorname{Fin}(U):i\in p(x)\}\bigr|
      =\sum_{x\in\operatorname{Fin}(U)}|p(x)| .
  \] -/)
  (proof := /-- Both sides count the pairs $(x,i)\in\operatorname{Fin}(U)\times\operatorname{Fin}(m)$ with $i\in p(x)$.  Precisely, for each $i$ we have $|\{x:i\in p(x)\}|=\sum_{x\in\operatorname{Fin}(U)}[\,i\in p(x)\,]$ and for each $x$ we have $|p(x)|=\sum_{i\in\operatorname{Fin}(m)}[\,i\in p(x)\,]$, where $[\cdot]$ is the indicator of the displayed condition.  Exchanging the order of the two finite sums of indicators turns the first expression into the second. -/)
  (title := /-- Total cell load equals total probe-set size -/)
  (latexEnv := "lemma")]
lemma cell_load_sum_eq_probe_card_sum :
    ∀ (U m : ℕ) (probeSet : Fin U → Finset (Fin m)),
      ∑ i : Fin m, ((Finset.univ : Finset (Fin U)).filter
          (fun x : Fin U => i ∈ probeSet x)).card
        = ∑ x : Fin U, (probeSet x).card := by
  intro U m probeSet
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp

@[blueprint "lem:exp-neg-two-mul-le-one-sub"
  (statement := /-- For every real number $y$ with $0\leq y\leq\frac12$ one has $e^{-2y}\leq 1-y$. -/)
  (proof := /-- Fix such a $y$.  Since $0\leq y$, the number $1+2y$ is positive.  The elementary inequality $1+z\leq e^{z}$, applied at $z=2y$, gives $0<1+2y\leq e^{2y}$, and passing to reciprocals in this inequality between positive numbers yields
  \[
    e^{-2y}=\bigl(e^{2y}\bigr)^{-1}\leq(1+2y)^{-1}.
  \]
  It remains to check $(1+2y)^{-1}\leq 1-y$.  Multiplying by the positive number $1+2y$, this is equivalent to $1\leq(1-y)(1+2y)=1+y-2y^{2}$, that is, to $2y^{2}\leq y$, which holds because $0\leq y\leq\frac12$ gives $2y^{2}=y\cdot 2y\leq y$.  Chaining the two displayed inequalities gives $e^{-2y}\leq 1-y$. -/)
  (title := /-- Exponential bound below one half -/)
  (latexEnv := "lemma")]
lemma exp_neg_two_mul_le_one_sub :
    ∀ y : ℝ, 0 ≤ y → y ≤ 1 / 2 → Real.exp (-(2 * y)) ≤ 1 - y := by
  intro y hy0 hy1
  have hpos : (0 : ℝ) < 1 + 2 * y := by linarith
  have hexp : 1 + 2 * y ≤ Real.exp (2 * y) := by
    have := Real.add_one_le_exp (2 * y)
    linarith
  have h1 : Real.exp (-(2 * y)) ≤ (1 + 2 * y)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ hpos hexp
  have h2 : (1 + 2 * y)⁻¹ ≤ 1 - y := by
    rw [inv_le_iff_one_le_mul₀ hpos]
    nlinarith
  linarith

@[blueprint "lem:choose-sub-ge-pow-mul-choose"
  (statement := /-- Let $U,n,a$ be natural numbers with $0<U$, $2n\leq U$ and $4a\leq U$.  Then
  \[
    \binom Un\left(1-\frac{2a}U\right)^{n}\leq\binom{U-a}{n},
  \]
  where the left-hand side is computed in the real numbers and $U-a$ denotes the truncated difference of natural numbers, which here coincides with the ordinary difference because $a\leq U$. -/)
  (proof := /-- From $4a\leq U$ we get $a\leq U$, and from $2n\leq U$ together with $4a\leq U$ we get $4(n+a)\leq 2U+U\leq 4U$, hence $n+a\leq U$ and therefore $n\leq U-a$.  Also $\frac{2a}U\leq\frac12\leq1$, so $\theta\coloneqq1-\frac{2a}U$ satisfies $0\leq\theta$.

  Since $n!>0$, the asserted inequality is equivalent to the inequality obtained after multiplying both sides by $n!$.  The falling factorial satisfies $N^{\underline n}=n!\binom Nn$ and $N^{\underline n}=\prod_{j=0}^{n-1}(N-j)$ for every natural number $N$; applied to $N=U$ and to $N=U-a$, and using $n\leq U-a$ so that no truncation occurs when the natural-number differences $U-j$ and $(U-a)-j$ with $j<n$ are read in the reals, this gives
  \[
    n!\binom Un=\prod_{j=0}^{n-1}(U-j),\qquad
    n!\binom{U-a}{n}=\prod_{j=0}^{n-1}(U-a-j).
  \]
  Thus it suffices to prove $\theta^{n}\prod_{j=0}^{n-1}(U-j)\leq\prod_{j=0}^{n-1}(U-a-j)$, and since $\theta^{n}\prod_{j<n}(U-j)=\prod_{j<n}\theta(U-j)$, it suffices to compare the products factorwise.

  Fix $j<n$.  First, $2j<2n\leq U$, so $U-2j>0$, and $j<n\leq U$ gives $U-j>0$; combined with $\theta\geq0$ this yields $0\leq\theta(U-j)$.  Second,
  \[
    (U-a-j)-\theta(U-j)=\frac{a(U-2j)}U\geq0 ,
  \]
  because $a\geq0$, $U-2j\geq0$ and $U>0$.  Hence $0\leq\theta(U-j)\leq U-a-j$ for every $j<n$, and multiplying these inequalities over $j=0,\dots,n-1$ gives the required comparison of products. -/)
  (title := /-- Binomial coefficient of a depleted universe -/)
  (latexEnv := "lemma")]
lemma choose_sub_ge_pow_mul_choose :
    ∀ (U n a : ℕ), 0 < U → 2 * n ≤ U → 4 * a ≤ U →
      (Nat.choose U n : ℝ) * (1 - 2 * (a : ℝ) / (U : ℝ)) ^ n
        ≤ (Nat.choose (U - a) n : ℝ) := by
  intro U n a hU hn ha
  have hU0 : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hU
  have haU : a ≤ U := by omega
  have hna : n ≤ U - a := by omega
  have haR : (4 : ℝ) * (a : ℝ) ≤ (U : ℝ) := by exact_mod_cast ha
  have hnR : (2 : ℝ) * (n : ℝ) ≤ (U : ℝ) := by exact_mod_cast hn
  have haR0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hθ0 : (0 : ℝ) ≤ 1 - 2 * (a : ℝ) / (U : ℝ) := by
    rw [sub_nonneg, div_le_one hU0]
    linarith
  have hfacpos : (0 : ℝ) < (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hprodU : (Nat.factorial n : ℝ) * (Nat.choose U n : ℝ)
      = ∏ j ∈ Finset.range n, ((U : ℝ) - (j : ℝ)) := by
    have hd : ((Nat.descFactorial U n : ℕ) : ℝ)
        = ∏ j ∈ Finset.range n, ((U : ℝ) - (j : ℝ)) := by
      rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
      refine Finset.prod_congr rfl (fun j hj => ?_)
      have hj' : j < n := Finset.mem_range.mp hj
      have hjU : j ≤ U := by omega
      rw [Nat.cast_sub hjU]
    rw [← hd, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  have hprodUa : (Nat.factorial n : ℝ) * (Nat.choose (U - a) n : ℝ)
      = ∏ j ∈ Finset.range n, ((U : ℝ) - (a : ℝ) - (j : ℝ)) := by
    have hd : ((Nat.descFactorial (U - a) n : ℕ) : ℝ)
        = ∏ j ∈ Finset.range n, ((U : ℝ) - (a : ℝ) - (j : ℝ)) := by
      rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
      refine Finset.prod_congr rfl (fun j hj => ?_)
      have hj' : j < n := Finset.mem_range.mp hj
      have hjU : j ≤ U - a := by omega
      rw [Nat.cast_sub hjU, Nat.cast_sub haU]
    rw [← hd, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  rw [← mul_le_mul_iff_of_pos_left hfacpos, ← mul_assoc, hprodU, hprodUa]
  have hsplit : (∏ j ∈ Finset.range n, ((U : ℝ) - (j : ℝ)))
        * (1 - 2 * (a : ℝ) / (U : ℝ)) ^ n
      = ∏ j ∈ Finset.range n, ((1 - 2 * (a : ℝ) / (U : ℝ)) * ((U : ℝ) - (j : ℝ))) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    ring
  rw [hsplit]
  refine Finset.prod_le_prod (fun j hj => ?_) (fun j hj => ?_)
  · have hj' : j < n := Finset.mem_range.mp hj
    have hjR : (j : ℝ) < (n : ℝ) := by exact_mod_cast hj'
    have : (0 : ℝ) ≤ (U : ℝ) - (j : ℝ) := by linarith
    exact mul_nonneg hθ0 this
  · have hj' : j < n := Finset.mem_range.mp hj
    have hjR : (j : ℝ) < (n : ℝ) := by exact_mod_cast hj'
    have hkey : ((U : ℝ) - (a : ℝ) - (j : ℝ))
        - (1 - 2 * (a : ℝ) / (U : ℝ)) * ((U : ℝ) - (j : ℝ))
        = (a : ℝ) * ((U : ℝ) - 2 * (j : ℝ)) / (U : ℝ) := by
      field_simp
      ring
    have hnonneg : (0 : ℝ) ≤ (a : ℝ) * ((U : ℝ) - 2 * (j : ℝ)) / (U : ℝ) := by
      apply div_nonneg _ (le_of_lt hU0)
      apply mul_nonneg haR0
      linarith
    linarith [hkey ▸ hnonneg]

@[blueprint "lem:choose-sub-ge-exp-mul-choose"
  (statement := /-- Let $U,n,a$ be natural numbers with $0<U$, $2n\leq U$ and $4a\leq U$.  Then
  \[
    \binom Un\exp\!\left(-\frac{4na}U\right)\leq\binom{U-a}{n},
  \]
  the left-hand side being computed in the real numbers. -/)
  (proof := /-- Put $y\coloneqq\frac{2a}U$.  Then $y\geq0$, and $4a\leq U$ with $U>0$ gives $y\leq\frac12$.  By \cref{lem:exp-neg-two-mul-le-one-sub}, $e^{-2y}\leq1-y$, and both sides are nonnegative because $e^{-2y}>0$.  Raising this inequality between nonnegative reals to the $n$-th power gives
  \[
    \exp\!\left(-\frac{4na}U\right)=\bigl(e^{-2y}\bigr)^{n}\leq(1-y)^{n}
    =\left(1-\frac{2a}U\right)^{n},
  \]
  where the first equality uses $-\frac{4na}U=n\cdot(-2y)$ and the identity $e^{nz}=(e^{z})^{n}$.  Multiplying by the nonnegative number $\binom Un$ and combining with \cref{lem:choose-sub-ge-pow-mul-choose}, which gives $\binom Un\left(1-\frac{2a}U\right)^{n}\leq\binom{U-a}{n}$, yields the assertion. -/)
  (title := /-- Exponential form of the depleted binomial bound -/)
  (latexEnv := "lemma")]
lemma choose_sub_ge_exp_mul_choose :
    ∀ (U n a : ℕ), 0 < U → 2 * n ≤ U → 4 * a ≤ U →
      (Nat.choose U n : ℝ)
          * Real.exp (-((4 : ℝ) * (n : ℝ) * (a : ℝ) / (U : ℝ)))
        ≤ (Nat.choose (U - a) n : ℝ) := by
  intro U n a hU hn ha
  have hU0 : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hU
  have haR : (4 : ℝ) * (a : ℝ) ≤ (U : ℝ) := by exact_mod_cast ha
  have haR0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hy0 : (0 : ℝ) ≤ 2 * (a : ℝ) / (U : ℝ) :=
    div_nonneg (by linarith) (le_of_lt hU0)
  have hy1 : 2 * (a : ℝ) / (U : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hU0]
    linarith
  have hstep := exp_neg_two_mul_le_one_sub (2 * (a : ℝ) / (U : ℝ)) hy0 hy1
  have hpow : Real.exp (-((4 : ℝ) * (n : ℝ) * (a : ℝ) / (U : ℝ)))
      ≤ (1 - 2 * (a : ℝ) / (U : ℝ)) ^ n := by
    have hrw : -((4 : ℝ) * (n : ℝ) * (a : ℝ) / (U : ℝ))
        = (n : ℝ) * (-(2 * (2 * (a : ℝ) / (U : ℝ)))) := by
      ring
    rw [hrw, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) hstep n
  have hchoose : (0 : ℝ) ≤ (Nat.choose U n : ℝ) := Nat.cast_nonneg _
  calc (Nat.choose U n : ℝ) * Real.exp (-((4 : ℝ) * (n : ℝ) * (a : ℝ) / (U : ℝ)))
      ≤ (Nat.choose U n : ℝ) * (1 - 2 * (a : ℝ) / (U : ℝ)) ^ n :=
        mul_le_mul_of_nonneg_left hpow hchoose
    _ ≤ (Nat.choose (U - a) n : ℝ) := choose_sub_ge_pow_mul_choose U n a hU hn ha

@[blueprint "lem:sum-exp-neg-ge-card-mul-exp-neg"
  (statement := /-- Let $m$ be a natural number, let $s\subseteq\operatorname{Fin}(m)$ be a finite set of indices, let $g:\operatorname{Fin}(m)\to\mathbb R$, and let $Y\in\mathbb R$ satisfy $\sum_{i\in s}g(i)\leq|s|\,Y$.  Then
  \[
    |s|\,e^{-Y}\leq\sum_{i\in s}e^{-g(i)} .
  \] -/)
  (proof := /-- This is the tangent-line form of Jensen's inequality for the convex function $z\mapsto e^{-z}$.  For every index $i$, the elementary inequality $1+z\leq e^{z}$ applied at $z=Y-g(i)$ gives $1+(Y-g(i))\leq e^{Y-g(i)}$, and multiplying by the nonnegative number $e^{-Y}$ yields
  \[
    e^{-Y}\bigl(1+Y-g(i)\bigr)\leq e^{-Y}e^{Y-g(i)}=e^{-g(i)} .
  \]
  Summing this over $i\in s$ and using $\sum_{i\in s}\bigl(1+Y-g(i)\bigr)=|s|(1+Y)-\sum_{i\in s}g(i)$, we obtain
  \[
    e^{-Y}\left(|s|(1+Y)-\sum_{i\in s}g(i)\right)\leq\sum_{i\in s}e^{-g(i)} .
  \]
  By hypothesis $\sum_{i\in s}g(i)\leq|s|\,Y$, so $|s|(1+Y)-\sum_{i\in s}g(i)\geq|s|(1+Y)-|s|Y=|s|$; multiplying this inequality by the nonnegative number $e^{-Y}$ gives $|s|\,e^{-Y}\leq e^{-Y}\left(|s|(1+Y)-\sum_{i\in s}g(i)\right)$.  Combining the last two displays proves the claim. -/)
  (title := /-- Tangent-line bound for a sum of exponentials -/)
  (latexEnv := "lemma")]
lemma sum_exp_neg_ge_card_mul_exp_neg :
    ∀ (m : ℕ) (s : Finset (Fin m)) (g : Fin m → ℝ) (Y : ℝ),
      (∑ i ∈ s, g i) ≤ (s.card : ℝ) * Y →
      (s.card : ℝ) * Real.exp (-Y) ≤ ∑ i ∈ s, Real.exp (-(g i)) := by
  intro m s g Y hsum
  have hexp0 : (0 : ℝ) ≤ Real.exp (-Y) := Real.exp_nonneg _
  have key : ∀ i ∈ s, Real.exp (-Y) * (1 + (Y - g i)) ≤ Real.exp (-(g i)) := by
    intro i _
    have h1 : 1 + (Y - g i) ≤ Real.exp (Y - g i) := by
      have := Real.add_one_le_exp (Y - g i)
      linarith
    calc Real.exp (-Y) * (1 + (Y - g i))
        ≤ Real.exp (-Y) * Real.exp (Y - g i) := mul_le_mul_of_nonneg_left h1 hexp0
      _ = Real.exp (-(g i)) := by
          rw [← Real.exp_add]
          ring_nf
  have hexpand : ∑ i ∈ s, Real.exp (-Y) * (1 + (Y - g i))
      = Real.exp (-Y) * ((s.card : ℝ) * (1 + Y) - ∑ i ∈ s, g i) := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul]
    ring
  have hlower : Real.exp (-Y) * (s.card : ℝ)
      ≤ Real.exp (-Y) * ((s.card : ℝ) * (1 + Y) - ∑ i ∈ s, g i) := by
    apply mul_le_mul_of_nonneg_left _ hexp0
    nlinarith
  have hsum_le := Finset.sum_le_sum key
  rw [hexpand] at hsum_le
  calc (s.card : ℝ) * Real.exp (-Y) = Real.exp (-Y) * (s.card : ℝ) := by ring
    _ ≤ Real.exp (-Y) * ((s.card : ℝ) * (1 + Y) - ∑ i ∈ s, g i) := hlower
    _ ≤ ∑ i ∈ s, Real.exp (-(g i)) := hsum_le

@[blueprint "lem:light-cells-card-ge-half"
  (statement := /-- Let $U,m,c$ be natural numbers with $0<U$, and let $a:\operatorname{Fin}(m)\to\mathbb N$ satisfy $\sum_{i}a_i\leq c$ and $8c\leq Um$.  Call an index $i$ light if $4a_i\leq U$.  Then the set $\Lambda$ of light indices satisfies
  \[
    \frac m2\leq|\Lambda| .
  \] -/)
  (proof := /-- Let $B\coloneqq\{i:4a_i>U\}$ be the set of non-light indices, so that $|\Lambda|+|B|=m$ because $\Lambda$ and $B$ partition $\operatorname{Fin}(m)$.  For every $i\in B$ we have $U\leq 4a_i$, hence
  \[
    U|B|=\sum_{i\in B}U\leq\sum_{i\in B}4a_i=4\sum_{i\in B}a_i\leq4\sum_{i}a_i\leq4c ,
  \]
  the second-to-last step because $B\subseteq\operatorname{Fin}(m)$ and all terms $a_i$ are nonnegative.  Doubling and using the hypothesis $8c\leq Um$,
  \[
    U\cdot(2|B|)=2U|B|\leq8c\leq Um .
  \]
  Since $U>0$, cancelling the factor $U$ gives $2|B|\leq m$.  Therefore $2|\Lambda|=2m-2|B|\geq2m-m=m$, which is the assertion after division by $2$. -/)
  (title := /-- At least half of the cells are lightly loaded -/)
  (latexEnv := "lemma")]
lemma light_cells_card_ge_half :
    ∀ (U m c : ℕ) (a : Fin m → ℕ), 0 < U → (∑ i : Fin m, a i) ≤ c → 8 * c ≤ U * m →
      (m : ℝ) / 2
        ≤ (((Finset.univ : Finset (Fin m)).filter (fun i : Fin m => 4 * a i ≤ U)).card : ℝ) := by
  intro U m c a hU hsum hcm
  set L := (Finset.univ : Finset (Fin m)).filter (fun i : Fin m => 4 * a i ≤ U) with hL
  set B := (Finset.univ : Finset (Fin m)).filter (fun i : Fin m => ¬ 4 * a i ≤ U) with hB
  have hpart : L.card + B.card = m := by
    rw [hL, hB, Finset.filter_card_add_filter_neg_card_eq_card]
    simp
  have hBload : U * B.card ≤ 4 * c := by
    have h1 : ∑ _i ∈ B, U ≤ ∑ i ∈ B, 4 * a i := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      have := (Finset.mem_filter.mp (hB ▸ hi)).2
      omega
    have h2 : ∑ i ∈ B, 4 * a i = 4 * ∑ i ∈ B, a i := by
      rw [Finset.mul_sum]
    have h3 : ∑ i ∈ B, a i ≤ ∑ i : Fin m, a i :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ B)
    have h4 : ∑ _i ∈ B, U = B.card * U := by
      rw [Finset.sum_const, smul_eq_mul]
    rw [h4] at h1
    rw [h2] at h1
    calc U * B.card = B.card * U := Nat.mul_comm _ _
      _ ≤ 4 * ∑ i ∈ B, a i := h1
      _ ≤ 4 * c := by omega
  have hBhalf : 2 * B.card ≤ m := by
    have : U * (2 * B.card) ≤ U * m := by
      calc U * (2 * B.card) = 2 * (U * B.card) := by ring
        _ ≤ 2 * (4 * c) := by omega
        _ = 8 * c := by ring
        _ ≤ U * m := hcm
    exact Nat.le_of_mul_le_mul_left this hU
  have hLnat : m ≤ 2 * L.card := by omega
  have : (m : ℝ) ≤ 2 * (L.card : ℝ) := by exact_mod_cast hLnat
  linarith

@[blueprint "lem:average-untouched-cells-lower-bound"
  (statement := /-- Let $U,n,m,c$ be natural numbers with $0<U$ and $2n\leq U$, and let $p:\operatorname{Fin}(U)\to\mathcal P(\operatorname{Fin}(m))$ assign a finite set of cells to every key, with total load $\sum_{x\in\operatorname{Fin}(U)}|p(x)|\leq c$ and $8c\leq Um$.  Then, with untouched cells as in \cref{def:untouched-cells},
  \[
    \binom Un\cdot\frac m2\cdot\exp\!\left(-\frac{8nc}{Um}\right)
    \leq\sum_{X}\bigl|\operatorname{untouched}(p,X)\bigr| ,
  \]
  the sum ranging over all $X\subseteq\operatorname{Fin}(U)$ with $|X|=n$.  Equivalently, a uniformly random $n$-subset leaves at least $\frac m2e^{-8nc/(Um)}$ cells unread on average. -/)
  (proof := /-- If $m=0$ the left-hand side vanishes, because it carries the factor $\frac m2$, while the right-hand side is a sum of nonnegative terms; the assertion holds in that degenerate case.  Assume from now on that $m>0$, and for a cell $i\in\operatorname{Fin}(m)$ let $a_i\coloneqq|\{x\in\operatorname{Fin}(U):i\in p(x)\}|$ denote its load.

  \emph{Step 1: cell-by-cell counting.}  By \cref{lem:untouched-cells-sum-eq-choose-sum},
  \[
    \sum_{X}\bigl|\operatorname{untouched}(p,X)\bigr|=\sum_{i\in\operatorname{Fin}(m)}\binom{U-a_i}{n},
  \]
  and by \cref{lem:cell-load-sum-eq-probe-card-sum} together with the hypothesis on the total load,
  \[
    \sum_{i\in\operatorname{Fin}(m)}a_i=\sum_{x\in\operatorname{Fin}(U)}|p(x)|\leq c .
  \]

  \emph{Step 2: the light cells.}  Call a cell $i$ light if $4a_i\leq U$, and let $\Lambda\subseteq\operatorname{Fin}(m)$ be the set of light cells.  Since $\sum_i a_i\leq c$, $8c\leq Um$ and $0<U$, \cref{lem:light-cells-card-ge-half} gives
  \[
    \frac m2\leq|\Lambda| .
  \]

  \emph{Step 3: averaging over the light cells.}  Set $Y\coloneqq\frac{8nc}{Um}$ and $g(i)\coloneqq\frac{4na_i}U$; both are nonnegative because $U>0$ and $m>0$.  Restricting the load bound of Step 1 to $\Lambda$ and using $|\Lambda|\geq\frac m2$,
  \[
    \sum_{i\in\Lambda}g(i)=\frac{4n}U\sum_{i\in\Lambda}a_i\leq\frac{4nc}U=\frac m2\cdot Y\leq|\Lambda|\,Y .
  \]
  Hence \cref{lem:sum-exp-neg-ge-card-mul-exp-neg}, applied to the set $\Lambda$, the function $g$ and the number $Y$, yields
  \[
    |\Lambda|\,e^{-Y}\leq\sum_{i\in\Lambda}e^{-g(i)} .
  \]

  \emph{Step 4: conclusion.}  For every light cell $i$ the hypotheses $0<U$, $2n\leq U$ and $4a_i\leq U$ let us apply \cref{lem:choose-sub-ge-exp-mul-choose}, which gives
  \[
    \binom Un e^{-g(i)}=\binom Un\exp\!\left(-\frac{4na_i}U\right)\leq\binom{U-a_i}{n} .
  \]
  Combining the displays, and using that $\binom Un\geq0$ and $e^{-Y}\geq0$ so that the bound $\frac m2\leq|\Lambda|$ of Step 2 may be multiplied through,
  \[
    \binom Un\cdot\frac m2\cdot e^{-Y}
      \leq\binom Un\cdot|\Lambda|\,e^{-Y}
      \leq\binom Un\sum_{i\in\Lambda}e^{-g(i)}
      =\sum_{i\in\Lambda}\binom Un e^{-g(i)}
      \leq\sum_{i\in\Lambda}\binom{U-a_i}{n} .
  \]
  Finally the omitted cells contribute nonnegative terms, so $\sum_{i\in\Lambda}\binom{U-a_i}{n}\leq\sum_{i\in\operatorname{Fin}(m)}\binom{U-a_i}{n}$, which equals $\sum_X\bigl|\operatorname{untouched}(p,X)\bigr|$ by Step 1.  Since $Y=\frac{8nc}{Um}$, this is precisely the asserted inequality. -/)
  (title := /-- Average number of cells left unread by a random key set -/)
  (latexEnv := "lemma")]
lemma average_untouched_cells_lower_bound :
    ∀ (U n m c : ℕ) (probeSet : Fin U → Finset (Fin m)),
      0 < U → 2 * n ≤ U →
      (∑ x : Fin U, (probeSet x).card) ≤ c →
      8 * c ≤ U * m →
      (Nat.choose U n : ℝ) * ((m : ℝ) / 2) *
          Real.exp (-(8 : ℝ) * (n : ℝ) * (c : ℝ) / ((U : ℝ) * (m : ℝ)))
        ≤ ∑ X ∈ Finset.powersetCard n (Finset.univ : Finset (Fin U)),
            ((untouched_cells probeSet X).card : ℝ) := by
  intro U n m c probeSet hU hn hload hcm
  have hRHSnonneg : ∀ X ∈ Finset.powersetCard n (Finset.univ : Finset (Fin U)),
      (0 : ℝ) ≤ ((untouched_cells probeSet X).card : ℝ) := fun X _ => Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos m with hm | hm
  · have hzero : (Nat.choose U n : ℝ) * ((m : ℝ) / 2)
        * Real.exp (-(8 : ℝ) * (n : ℝ) * (c : ℝ) / ((U : ℝ) * (m : ℝ))) = 0 := by
      simp [hm]
    rw [hzero]
    exact Finset.sum_nonneg hRHSnonneg
  set a : Fin m → ℕ :=
    fun i => ((Finset.univ : Finset (Fin U)).filter (fun x : Fin U => i ∈ probeSet x)).card
    with ha
  have hnat := untouched_cells_sum_eq_choose_sum U m n probeSet
  have hRHSeq : ∑ X ∈ Finset.powersetCard n (Finset.univ : Finset (Fin U)),
        ((untouched_cells probeSet X).card : ℝ)
      = ∑ i : Fin m, (Nat.choose (U - a i) n : ℝ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hnat
  have hloadA : (∑ i : Fin m, a i) ≤ c := by
    rw [ha, cell_load_sum_eq_probe_card_sum U m probeSet]
    exact hload
  set L := (Finset.univ : Finset (Fin m)).filter (fun i : Fin m => 4 * a i ≤ U) with hL
  have hLcard : (m : ℝ) / 2 ≤ (L.card : ℝ) :=
    light_cells_card_ge_half U m c a hU hloadA hcm
  set Y : ℝ := (8 : ℝ) * (n : ℝ) * (c : ℝ) / ((U : ℝ) * (m : ℝ)) with hY
  set g : Fin m → ℝ := fun i => (4 : ℝ) * (n : ℝ) * (a i : ℝ) / (U : ℝ) with hg
  have hU0 : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hU
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hY0 : (0 : ℝ) ≤ Y := by
    rw [hY]
    positivity
  have hsumg : (∑ i ∈ L, g i) ≤ (L.card : ℝ) * Y := by
    have h1 : (∑ i ∈ L, g i)
        = ((4 : ℝ) * (n : ℝ) / (U : ℝ)) * ∑ i ∈ L, (a i : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hg]
      ring
    have h2 : (∑ i ∈ L, (a i : ℝ)) ≤ (c : ℝ) := by
      have hsub : (∑ i ∈ L, a i) ≤ ∑ i : Fin m, a i :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ L)
      have : (∑ i ∈ L, a i) ≤ c := le_trans hsub hloadA
      exact_mod_cast Nat.cast_le.mpr this
    have h3 : (∑ i ∈ L, g i) ≤ (4 : ℝ) * (n : ℝ) * (c : ℝ) / (U : ℝ) := by
      rw [h1]
      have hcoef : (0 : ℝ) ≤ (4 : ℝ) * (n : ℝ) / (U : ℝ) := by positivity
      calc ((4 : ℝ) * (n : ℝ) / (U : ℝ)) * ∑ i ∈ L, (a i : ℝ)
          ≤ ((4 : ℝ) * (n : ℝ) / (U : ℝ)) * (c : ℝ) := mul_le_mul_of_nonneg_left h2 hcoef
        _ = (4 : ℝ) * (n : ℝ) * (c : ℝ) / (U : ℝ) := by ring
    have h4 : (4 : ℝ) * (n : ℝ) * (c : ℝ) / (U : ℝ) ≤ (L.card : ℝ) * Y := by
      have hhalf : ((m : ℝ) / 2) * Y = (4 : ℝ) * (n : ℝ) * (c : ℝ) / (U : ℝ) := by
        rw [hY]
        field_simp
        ring
      calc (4 : ℝ) * (n : ℝ) * (c : ℝ) / (U : ℝ) = ((m : ℝ) / 2) * Y := hhalf.symm
        _ ≤ (L.card : ℝ) * Y := mul_le_mul_of_nonneg_right hLcard hY0
    linarith
  have hjensen : (L.card : ℝ) * Real.exp (-Y) ≤ ∑ i ∈ L, Real.exp (-(g i)) :=
    sum_exp_neg_ge_card_mul_exp_neg m L g Y hsumg
  have hchoose0 : (0 : ℝ) ≤ (Nat.choose U n : ℝ) := Nat.cast_nonneg _
  have hcell : ∀ i ∈ L,
      (Nat.choose U n : ℝ) * Real.exp (-(g i)) ≤ (Nat.choose (U - a i) n : ℝ) := by
    intro i hi
    have hlight : 4 * a i ≤ U := (Finset.mem_filter.mp hi).2
    have := choose_sub_ge_exp_mul_choose U n (a i) hU hn hlight
    rw [hg]
    exact this
  have hexpY : Real.exp (-(8 : ℝ) * (n : ℝ) * (c : ℝ) / ((U : ℝ) * (m : ℝ)))
      = Real.exp (-Y) := by
    rw [hY]
    congr 1
    ring
  rw [hRHSeq, hexpY]
  calc (Nat.choose U n : ℝ) * ((m : ℝ) / 2) * Real.exp (-Y)
      ≤ (Nat.choose U n : ℝ) * ((L.card : ℝ) * Real.exp (-Y)) := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hchoose0
        exact mul_le_mul_of_nonneg_right hLcard (Real.exp_nonneg _)
    _ ≤ (Nat.choose U n : ℝ) * ∑ i ∈ L, Real.exp (-(g i)) :=
        mul_le_mul_of_nonneg_left hjensen hchoose0
    _ = ∑ i ∈ L, (Nat.choose U n : ℝ) * Real.exp (-(g i)) := Finset.mul_sum _ _ _
    _ ≤ ∑ i ∈ L, (Nat.choose (U - a i) n : ℝ) := Finset.sum_le_sum hcell
    _ ≤ ∑ i : Fin m, (Nat.choose (U - a i) n : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ L)
          (fun i _ _ => Nat.cast_nonneg _)

@[blueprint "lem:exp-add-exp-neg-le-two-exp-sq-half"
  (statement := /-- For every real number $u$ with $|u|\leq1$,
  \[
    e^{u}+e^{-u}\leq 2e^{u^{2}/2}.
  \]
  Equivalently $\cosh u\leq e^{u^{2}/2}$ on the interval $[-1,1]$. -/)
  (proof := /-- Fix $u$ with $|u|\leq1$.  The Taylor estimate for the real exponential with four terms, applied at $u$ and at $-u$, gives
  \[
    \left|e^{\pm u}-\left(1\pm u+\frac{u^{2}}2\pm\frac{u^{3}}6\right)\right|
      \leq|u|^{4}\cdot\frac{5}{4!\cdot4}=\frac{5}{96}|u|^{4},
  \]
  the hypothesis $|u|\leq1$ being exactly what that estimate requires, and $|-u|=|u|\leq1$ giving the second instance.  Since $|u|^{4}=u^{4}$, this bounds $e^{u}$ and $e^{-u}$ above and below by explicit polynomials in $u$.  Adding the two upper bounds, the odd powers cancel and
  \[
    e^{u}+e^{-u}\leq 2+u^{2}+\frac{5}{48}u^{4}.
  \]
  On the other side, every partial sum of the exponential series at the nonnegative argument $u^{2}/2$ is at most $e^{u^{2}/2}$; taking three terms,
  \[
    1+\frac{u^{2}}2+\frac{u^{4}}8\leq e^{u^{2}/2},
    \qquad\text{hence}\qquad
    2+u^{2}+\frac{u^{4}}4\leq 2e^{u^{2}/2}.
  \]
  Since $\frac5{48}\leq\frac14$ and $u^{4}\geq0$, the first display is at most the second, which is the assertion. -/)
  (title := /-- Hyperbolic cosine bound on the unit interval -/)
  (latexEnv := "lemma")]
lemma exp_add_exp_neg_le_two_exp_sq_half :
    ∀ u : ℝ, |u| ≤ 1 →
      Real.exp u + Real.exp (-u) ≤ 2 * Real.exp (u ^ 2 / 2) := by
  intro u hu
  have h1 := Real.exp_bound hu (n := 4) (by norm_num)
  have h2 := Real.exp_bound (x := -u) (by rwa [abs_neg]) (n := 4) (by norm_num)
  have h3 := Real.sum_le_exp_of_nonneg (x := u ^ 2 / 2) (by positivity) 3
  simp [Finset.sum_range_succ, Nat.factorial] at h1 h2 h3
  rw [abs_le] at h1 h2
  have habs : |u| ^ 4 = u ^ 4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : (0:ℝ) ≤ u ^ 4)]
  rw [habs] at h1 h2
  nlinarith [h1.1, h1.2, h2.1, h2.2, h3, sq_nonneg u, sq_nonneg (u ^ 2)]

@[blueprint "lem:exp-neg-mul-le-convex-combination"
  (statement := /-- Let $z,\theta,\Lambda$ be real numbers with $0<\Lambda$ and $|z|\leq\Lambda$.  Then
  \[
    e^{-\theta z}\leq\frac{\Lambda-z}{2\Lambda}e^{\theta\Lambda}
      +\frac{\Lambda+z}{2\Lambda}e^{-\theta\Lambda}.
  \]
  This is the chord of the exponential joining the endpoints $\theta\Lambda$ and $-\theta\Lambda$, evaluated at the intermediate point $-\theta z$. -/)
  (proof := /-- Put $a\coloneqq\frac{\Lambda-z}{2\Lambda}$ and $b\coloneqq\frac{\Lambda+z}{2\Lambda}$.  From $|z|\leq\Lambda$ we get $-\Lambda\leq z\leq\Lambda$, so $a\geq0$ and $b\geq0$ because both numerators are nonnegative and $2\Lambda>0$; moreover $a+b=\frac{2\Lambda}{2\Lambda}=1$, again using $\Lambda>0$.  Next,
  \[
    a\,(\theta\Lambda)+b\,(-\theta\Lambda)
      =\theta\Lambda\,(a-b)=\theta\Lambda\cdot\frac{-2z}{2\Lambda}=-\theta z .
  \]
  The real exponential is convex on all of $\mathbb R$, so applying the definition of convexity at the points $\theta\Lambda$ and $-\theta\Lambda$ with the weights $a$ and $b$ gives
  \[
    e^{-\theta z}=e^{a(\theta\Lambda)+b(-\theta\Lambda)}
      \leq a\,e^{\theta\Lambda}+b\,e^{-\theta\Lambda},
  \]
  which is the assertion. -/)
  (title := /-- Chord bound for the exponential -/)
  (latexEnv := "lemma")]
lemma exp_neg_mul_le_convex_combination :
    ∀ z theta Lb : ℝ, 0 < Lb → |z| ≤ Lb →
      Real.exp (-theta * z) ≤
        ((Lb - z) / (2 * Lb)) * Real.exp (theta * Lb) +
          ((Lb + z) / (2 * Lb)) * Real.exp (-(theta * Lb)) := by
  intro z theta Lb hLb hz
  rw [abs_le] at hz
  have ha : (0:ℝ) ≤ (Lb - z) / (2 * Lb) := by
    apply div_nonneg (by linarith) (by linarith)
  have hb : (0:ℝ) ≤ (Lb + z) / (2 * Lb) := by
    apply div_nonneg (by linarith) (by linarith)
  have hab : (Lb - z) / (2 * Lb) + (Lb + z) / (2 * Lb) = 1 := by
    field_simp
    ring
  have hcv := convexOn_exp.2 (Set.mem_univ (theta * Lb))
    (Set.mem_univ (-(theta * Lb))) ha hb hab
  simp only [smul_eq_mul] at hcv
  have harg : (Lb - z) / (2 * Lb) * (theta * Lb) +
      (Lb + z) / (2 * Lb) * -(theta * Lb) = -theta * z := by
    field_simp
    ring
  rwa [harg] at hcv

@[blueprint "lem:sum-exp-neg-le-of-pairwise-close"
  (statement := /-- Let $A\subseteq\operatorname{Fin}(U)$ be a nonempty finite set, let $\nu:\operatorname{Fin}(U)\to\mathbb R$, and let $\theta,\Lambda$ be real numbers with $\theta\geq0$, $\Lambda>0$ and $\theta\Lambda\leq1$.  Assume $|\nu(a)-\nu(a')|\leq\Lambda$ for all $a,a'\in A$, and write $\bar\nu\coloneqq|A|^{-1}\sum_{a\in A}\nu(a)$.  Then
  \[
    \sum_{a\in A}e^{-\theta\nu(a)}
      \leq|A|\,e^{-\theta\bar\nu}\,e^{\theta^{2}\Lambda^{2}/2}.
  \] -/)
  (proof := /-- Write $c\coloneqq|A|$, which is a positive real because $A$ is nonempty, and set $z_a\coloneqq\nu(a)-\bar\nu$ for $a\in A$.

  First, $\sum_{a\in A}z_a=\sum_{a\in A}\nu(a)-c\bar\nu=0$ by the definition of $\bar\nu$.  Second, for each $a\in A$,
  \[
    z_a=\nu(a)-\frac1c\sum_{a'\in A}\nu(a')=\frac1c\sum_{a'\in A}\bigl(\nu(a)-\nu(a')\bigr),
  \]
  so by the triangle inequality and the hypothesis, $|z_a|\leq\frac1c\sum_{a'\in A}\Lambda=\Lambda$.

  Now fix $a\in A$.  Since $e^{-\theta\nu(a)}=e^{-\theta\bar\nu}e^{-\theta z_a}$ and $|z_a|\leq\Lambda$ with $\Lambda>0$, \cref{lem:exp-neg-mul-le-convex-combination} applied to $z_a$ gives
  \[
    e^{-\theta\nu(a)}\leq e^{-\theta\bar\nu}
      \left(\frac{\Lambda-z_a}{2\Lambda}e^{\theta\Lambda}
        +\frac{\Lambda+z_a}{2\Lambda}e^{-\theta\Lambda}\right),
  \]
  the factor $e^{-\theta\bar\nu}$ being positive.  Summing over $a\in A$ and using $\sum_{a\in A}z_a=0$ together with $\sum_{a\in A}\Lambda=c\Lambda$, the two coefficient sums are both $\frac{c\Lambda}{2\Lambda}=\frac c2$, so
  \[
    \sum_{a\in A}e^{-\theta\nu(a)}
      \leq e^{-\theta\bar\nu}\cdot\frac c2\left(e^{\theta\Lambda}+e^{-\theta\Lambda}\right).
  \]
  Finally $|\theta\Lambda|=\theta\Lambda\leq1$ because $\theta\geq0$ and $\Lambda>0$, so \cref{lem:exp-add-exp-neg-le-two-exp-sq-half} applied to $u\coloneqq\theta\Lambda$ yields $e^{\theta\Lambda}+e^{-\theta\Lambda}\leq2e^{\theta^{2}\Lambda^{2}/2}$.  Substituting this into the previous display gives the assertion. -/)
  (title := /-- Exponential average of pairwise close values -/)
  (latexEnv := "lemma")]
lemma sum_exp_neg_le_of_pairwise_close :
    ∀ (U : ℕ) (A : Finset (Fin U)) (nu : Fin U → ℝ) (theta Lb : ℝ),
      0 ≤ theta → 0 < Lb → theta * Lb ≤ 1 → A.Nonempty →
      (∀ a ∈ A, ∀ a' ∈ A, |nu a - nu a'| ≤ Lb) →
      (∑ a ∈ A, Real.exp (-theta * nu a))
        ≤ (A.card : ℝ) *
            Real.exp (-theta * ((∑ a ∈ A, nu a) / (A.card : ℝ))) *
            Real.exp (theta ^ 2 * Lb ^ 2 / 2) := by
  intro U A nu theta Lb htheta hLb hthetaLb hA hdiff
  have hcpos : (0:ℝ) < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hA
  set c : ℝ := (A.card : ℝ) with hc
  set nbar : ℝ := (∑ a ∈ A, nu a) / c with hnbar
  have hsumz : ∑ a ∈ A, (nu a - nbar) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hnbar]
    field_simp
    ring
  have hzabs : ∀ a ∈ A, |nu a - nbar| ≤ Lb := by
    intro a ha
    have hrepr : nu a - nbar = (∑ a' ∈ A, (nu a - nu a')) / c := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hnbar]
      field_simp
      ring
    rw [hrepr, abs_div, abs_of_pos hcpos, div_le_iff₀ hcpos]
    calc |∑ a' ∈ A, (nu a - nu a')| ≤ ∑ a' ∈ A, |nu a - nu a'| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a' ∈ A, Lb := Finset.sum_le_sum (fun a' ha' => hdiff a ha a' ha')
      _ = Lb * c := by rw [Finset.sum_const, nsmul_eq_mul, hc]; ring
  have hchord : ∀ a ∈ A,
      Real.exp (-theta * nu a) ≤
        Real.exp (-theta * nbar) *
          (((Lb - (nu a - nbar)) / (2 * Lb)) * Real.exp (theta * Lb) +
            ((Lb + (nu a - nbar)) / (2 * Lb)) * Real.exp (-(theta * Lb))) := by
    intro a ha
    have hsplit : Real.exp (-theta * nu a) =
        Real.exp (-theta * nbar) * Real.exp (-theta * (nu a - nbar)) := by
      rw [← Real.exp_add]; ring_nf
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left
      (exp_neg_mul_le_convex_combination (nu a - nbar) theta Lb hLb (hzabs a ha))
      (Real.exp_pos _).le
  calc ∑ a ∈ A, Real.exp (-theta * nu a)
      ≤ ∑ a ∈ A, Real.exp (-theta * nbar) *
          (((Lb - (nu a - nbar)) / (2 * Lb)) * Real.exp (theta * Lb) +
            ((Lb + (nu a - nbar)) / (2 * Lb)) * Real.exp (-(theta * Lb))) :=
        Finset.sum_le_sum hchord
    _ = Real.exp (-theta * nbar) *
          ((c / 2) * (Real.exp (theta * Lb) + Real.exp (-(theta * Lb)))) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
          ← Finset.sum_div, ← Finset.sum_div, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hsumz]
        field_simp
        ring
    _ ≤ Real.exp (-theta * nbar) *
          ((c / 2) * (2 * Real.exp ((theta * Lb) ^ 2 / 2))) := by
        have habs : |theta * Lb| ≤ 1 := by
          rw [abs_of_nonneg (by positivity)]
          exact hthetaLb
        have := exp_add_exp_neg_le_two_exp_sq_half (theta * Lb) habs
        have hchalf : (0:ℝ) ≤ c / 2 := by positivity
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left this hchalf) (Real.exp_pos _).le
    _ = c * Real.exp (-theta * nbar) * Real.exp (theta ^ 2 * Lb ^ 2 / 2) := by
        rw [mul_pow]
        ring

@[blueprint "lem:sum-insert-powersetCard-double-count"
  (statement := /-- Let $B\subseteq\operatorname{Fin}(U)$ be a finite set, let $j$ be a natural number, and let $g$ be a real-valued function on finite subsets of $\operatorname{Fin}(U)$.  Then
  \[
    \sum_{x\in B}\ \sum_{Z\subseteq B\setminus\{x\},\ |Z|=j} g(Z\cup\{x\})
      =(j+1)\sum_{Y\subseteq B,\ |Y|=j+1} g(Y).
  \] -/)
  (proof := /-- Both sides count the pairs consisting of a $(j+1)$-subset of $B$ together with a distinguished element of it.

  Consider the index set $\mathcal S$ of pairs $(x,Z)$ with $x\in B$ and $Z\subseteq B\setminus\{x\}$, $|Z|=j$, and the index set $\mathcal T$ of pairs $(Y,x)$ with $Y\subseteq B$, $|Y|=j+1$, and $x\in Y$.  Define $\iota(x,Z)\coloneqq(Z\cup\{x\},x)$ and $\kappa(Y,x)\coloneqq(x,Y\setminus\{x\})$.

  If $(x,Z)\in\mathcal S$ then $Z\cup\{x\}\subseteq B$ because $Z\subseteq B\setminus\{x\}\subseteq B$ and $x\in B$, and $x\notin Z$ gives $|Z\cup\{x\}|=j+1$; also $x\in Z\cup\{x\}$, so $\iota(x,Z)\in\mathcal T$.  If $(Y,x)\in\mathcal T$ then $x\in Y\subseteq B$, and $Y\setminus\{x\}\subseteq B\setminus\{x\}$ with $|Y\setminus\{x\}|=j$ since $x\in Y$, so $\kappa(Y,x)\in\mathcal S$.  Moreover $\kappa(\iota(x,Z))=(x,(Z\cup\{x\})\setminus\{x\})=(x,Z)$ because $x\notin Z$, and $\iota(\kappa(Y,x))=((Y\setminus\{x\})\cup\{x\},x)=(Y,x)$ because $x\in Y$.  Hence $\iota$ and $\kappa$ are mutually inverse bijections between $\mathcal S$ and $\mathcal T$, and $g$ evaluated at the first component is matched by construction.

  Reindexing the left-hand double sum along this bijection therefore gives
  \[
    \sum_{x\in B}\ \sum_{Z} g(Z\cup\{x\})
      =\sum_{Y\subseteq B,\ |Y|=j+1}\ \sum_{x\in Y} g(Y)
      =\sum_{Y\subseteq B,\ |Y|=j+1}|Y|\,g(Y),
  \]
  and $|Y|=j+1$ for every such $Y$, which yields the asserted identity. -/)
  (title := /-- Double counting subsets with a distinguished element -/)
  (latexEnv := "lemma")]
lemma sum_insert_powersetCard_double_count :
    ∀ (U j : ℕ) (B : Finset (Fin U)) (g : Finset (Fin U) → ℝ),
      (∑ x ∈ B, ∑ Z ∈ Finset.powersetCard j (B.erase x), g (insert x Z))
        = ((j : ℝ) + 1) *
            ∑ Y ∈ Finset.powersetCard (j + 1) B, g Y := by
  intro U j B g
  have key : (∑ x ∈ B, ∑ Z ∈ Finset.powersetCard j (B.erase x), g (insert x Z))
      = ∑ Y ∈ Finset.powersetCard (j + 1) B, ∑ _x ∈ Y, g Y := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_nbij' (i := fun p => ⟨insert p.1 p.2, p.1⟩)
      (j := fun q => ⟨q.2, q.1.erase q.2⟩) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨x, Z⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hp ⊢
      obtain ⟨hxB, hZsub, hZcard⟩ := hp
      have hxZ : x ∉ Z := fun hx => (Finset.mem_erase.mp (hZsub hx)).1 rfl
      refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self _ _⟩
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hxB
        · exact Finset.mem_of_mem_erase (hZsub hy)
      · rw [Finset.card_insert_of_notMem hxZ, hZcard]
    · rintro ⟨Y, x⟩ hq
      simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hq ⊢
      obtain ⟨⟨hYsub, hYcard⟩, hxY⟩ := hq
      refine ⟨hYsub hxY, ?_, ?_⟩
      · intro y hy
        exact Finset.mem_erase.mpr
          ⟨(Finset.mem_erase.mp hy).1, hYsub (Finset.mem_of_mem_erase hy)⟩
      · rw [Finset.card_erase_of_mem hxY, hYcard]
        omega
    · rintro ⟨x, Z⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hp
      have hxZ : x ∉ Z := fun hx => (Finset.mem_erase.mp (hp.2.1 hx)).1 rfl
      simp [Finset.erase_insert hxZ]
    · rintro ⟨Y, x⟩ hq
      simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hq
      simp [Finset.insert_erase hq.2]
    · rintro ⟨x, Z⟩ _
      rfl
  rw [key]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro Y hY
  rw [Finset.sum_const, Finset.mem_powersetCard.mp hY |>.2, nsmul_eq_mul]
  push_cast
  ring

@[blueprint "lem:untouched-cells-card-swap-diff"
  (statement := /-- Let $p:\operatorname{Fin}(U)\to\mathcal P(\operatorname{Fin}(m))$ satisfy $|p(x)|\leq L$ for every key $x$, and let $Z\subseteq\operatorname{Fin}(U)$ be a finite set of keys.  Then for all keys $x,x'$,
  \[
    \bigl|\,|\operatorname{untouched}(p,Z\cup\{x\})|-|\operatorname{untouched}(p,Z\cup\{x'\})|\,\bigr|\leq L,
  \]
  where $\operatorname{untouched}$ is as in \cref{def:untouched-cells}. -/)
  (proof := /-- Abbreviate $W\coloneqq\bigcup_{y\in Z}p(y)$, so that by \cref{def:untouched-cells}
  \[
    \operatorname{untouched}(p,Z\cup\{x\})
      =\operatorname{Fin}(m)\setminus\bigl(W\cup p(x)\bigr),
  \]
  the union over $Z\cup\{x\}$ being $W\cup p(x)$, and similarly for $x'$.

  Write $N\coloneqq\operatorname{Fin}(m)\setminus W$ for the cells untouched by $Z$ alone.  Then
  \[
    \operatorname{untouched}(p,Z\cup\{x\})=N\setminus p(x),
    \qquad
    \operatorname{untouched}(p,Z\cup\{x'\})=N\setminus p(x') .
  \]
  Since $|N|\leq|N\setminus p(x)|+|p(x)|$ and $N\setminus p(x)\subseteq N$, we get
  \[
    |N|-L\leq|N|-|p(x)|\leq|N\setminus p(x)|\leq|N| ,
  \]
  using $|p(x)|\leq L$, and the same two-sided estimate holds for $x'$.  Both quantities therefore lie in the interval $[\,|N|-L,\,|N|\,]$ of length $L$, so their difference is at most $L$ in absolute value, which is the assertion. -/)
  (title := /-- Bounded difference under swapping one key -/)
  (latexEnv := "lemma")]
lemma untouched_cells_card_swap_diff :
    ∀ (U m L : ℕ) (probeSet : Fin U → Finset (Fin m)) (Z : Finset (Fin U)),
      (∀ x : Fin U, (probeSet x).card ≤ L) →
      ∀ x x' : Fin U,
        |((untouched_cells probeSet (insert x Z)).card : ℝ) -
            ((untouched_cells probeSet (insert x' Z)).card : ℝ)| ≤ (L : ℝ) := by
  intro U m L probeSet Z hL x x'
  set N : Finset (Fin m) :=
    (Finset.univ : Finset (Fin m)) \ Z.biUnion probeSet with hN
  have hrewrite : ∀ y : Fin U,
      untouched_cells probeSet (insert y Z) = N \ probeSet y := by
    intro y
    ext i
    simp [untouched_cells, hN, Finset.mem_sdiff, Finset.mem_biUnion,
      Finset.mem_insert, or_imp, forall_and, not_or, and_assoc, and_comm]
  have hbound : ∀ y : Fin U,
      (N.card : ℝ) - (L : ℝ) ≤ ((N \ probeSet y).card : ℝ) ∧
        ((N \ probeSet y).card : ℝ) ≤ (N.card : ℝ) := by
    intro y
    constructor
    · have h1 : N.card ≤ (N \ probeSet y).card + (probeSet y).card :=
        Finset.card_le_card_sdiff_add_card
      have h2 : (probeSet y).card ≤ L := hL y
      have : (N.card : ℝ) ≤ ((N \ probeSet y).card : ℝ) + (L : ℝ) := by
        exact_mod_cast le_trans (by exact_mod_cast h1)
          (by exact_mod_cast Nat.add_le_add_left h2 _)
      linarith
    · exact_mod_cast Finset.card_le_card (Finset.sdiff_subset)
  rw [hrewrite x, hrewrite x', abs_le]
  obtain ⟨hx1, hx2⟩ := hbound x
  obtain ⟨hx'1, hx'2⟩ := hbound x'
  constructor <;> linarith

@[blueprint "def:untouched-average"
  (statement := /-- Let $p:\operatorname{Fin}(U)\to\mathcal P(\operatorname{Fin}(m))$ be a probe assignment, let $Z\subseteq\operatorname{Fin}(U)$ be a set of already exposed keys, and let $r$ be a natural number.  The conditional untouched average is
  \[
    A_r(Z)\coloneqq\binom{|\operatorname{Fin}(U)\setminus Z|}{r}^{-1}
      \sum_{S\subseteq\operatorname{Fin}(U)\setminus Z,\ |S|=r}
        \bigl|\operatorname{untouched}(p,Z\cup S)\bigr| ,
  \]
  the average of \cref{def:untouched-cells} over all ways of completing $Z$ by $r$ further keys chosen outside $Z$.  The quotient is the real division, so the value is $0$ by convention when the binomial coefficient vanishes. -/)
  (title := /-- Conditional average of untouched cells -/)
  (latexEnv := "definition")]
noncomputable def untouched_average {U m : ℕ} (probeSet : Fin U → Finset (Fin m))
    (Z : Finset (Fin U)) (r : ℕ) : ℝ :=
  (∑ S ∈ Finset.powersetCard r ((Finset.univ : Finset (Fin U)) \ Z),
      ((untouched_cells probeSet (Z ∪ S)).card : ℝ)) /
    (Nat.choose (((Finset.univ : Finset (Fin U)) \ Z).card) r : ℝ)

@[blueprint "lem:sdiff-insert-eq-erase-sdiff"
  (statement := /-- For every finite set $Z\subseteq\operatorname{Fin}(U)$ and every key $x$,
  \[
    \operatorname{Fin}(U)\setminus(Z\cup\{x\})
      =\bigl(\operatorname{Fin}(U)\setminus Z\bigr)\setminus\{x\} .
  \] -/)
  (proof := /-- Both sides are subsets of $\operatorname{Fin}(U)$, so it suffices to compare membership.  A key $i$ lies in the left-hand side exactly when $i\notin Z\cup\{x\}$, that is, exactly when $i\neq x$ and $i\notin Z$.  It lies in the right-hand side exactly when $i\neq x$ and $i\in\operatorname{Fin}(U)\setminus Z$, that is, exactly when $i\neq x$ and $i\notin Z$.  The two conditions coincide, so the sets are equal. -/)
  (title := /-- Complement of an augmented exposed set -/)
  (latexEnv := "lemma")]
lemma sdiff_insert_eq_erase_sdiff :
    ∀ (U : ℕ) (Z : Finset (Fin U)) (x : Fin U),
      (Finset.univ : Finset (Fin U)) \ insert x Z
        = ((Finset.univ : Finset (Fin U)) \ Z).erase x := by
  intro U Z x
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, true_and,
    Finset.mem_insert, not_or, and_comm]

@[blueprint "lem:untouched-average-tower"
  (statement := /-- Let $p:\operatorname{Fin}(U)\to\mathcal P(\operatorname{Fin}(m))$ be a probe assignment, let $Z\subseteq\operatorname{Fin}(U)$, write $B\coloneqq\operatorname{Fin}(U)\setminus Z$, and let $r$ be a natural number with $r+1\leq|B|$.  Then the conditional averages of \cref{def:untouched-average} satisfy
  \[
    \frac1{|B|}\sum_{x\in B}A_r\bigl(Z\cup\{x\}\bigr)=A_{r+1}(Z).
  \] -/)
  (proof := /-- Write $\Phi(W)\coloneqq|\operatorname{untouched}(p,W)|$ and $g(Y)\coloneqq\Phi(Z\cup Y)$, and abbreviate $N\coloneqq|B|$, so $N\geq r+1\geq1$.

  Fix $x\in B$.  By \cref{lem:sdiff-insert-eq-erase-sdiff} we have $\operatorname{Fin}(U)\setminus(Z\cup\{x\})=B\setminus\{x\}$, whose cardinality is $N-1$ because $x\in B$.  Hence, by \cref{def:untouched-average},
  \[
    A_r\bigl(Z\cup\{x\}\bigr)
      =\binom{N-1}{r}^{-1}\sum_{S\subseteq B\setminus\{x\},\ |S|=r}\Phi\bigl((Z\cup\{x\})\cup S\bigr),
  \]
  and $(Z\cup\{x\})\cup S=Z\cup(\{x\}\cup S)$, so each summand equals $g(S\cup\{x\})$.

  Summing over $x\in B$ and pulling out the constant factor $\binom{N-1}{r}^{-1}$, \cref{lem:sum-insert-powersetCard-double-count} applied to $B$, to $r$, and to $g$ gives
  \[
    \sum_{x\in B}A_r\bigl(Z\cup\{x\}\bigr)
      =\binom{N-1}{r}^{-1}(r+1)\sum_{Y\subseteq B,\ |Y|=r+1}g(Y).
  \]
  On the other hand $A_{r+1}(Z)=\binom N{r+1}^{-1}\sum_{Y\subseteq B,\ |Y|=r+1}g(Y)$ by \cref{def:untouched-average}.  The absorption identity for binomial coefficients gives $N\binom{N-1}r=\binom N{r+1}(r+1)$, using $N\geq1$ to write $N=(N-1)+1$.  Since $r\leq N-1$ and $r+1\leq N$, both $\binom{N-1}r$ and $\binom N{r+1}$ are positive, and $N>0$; dividing the previous display by $N$ and using the identity therefore yields
  \[
    \frac1N\sum_{x\in B}A_r\bigl(Z\cup\{x\}\bigr)
      =\frac{(r+1)}{N\binom{N-1}r}\sum_{Y}g(Y)
      =\binom N{r+1}^{-1}\sum_{Y}g(Y)=A_{r+1}(Z),
  \]
  as asserted. -/)
  (title := /-- Tower identity for conditional averages -/)
  (latexEnv := "lemma")]
lemma untouched_average_tower :
    ∀ (U m r : ℕ) (probeSet : Fin U → Finset (Fin m)) (Z : Finset (Fin U)),
      r + 1 ≤ (((Finset.univ : Finset (Fin U)) \ Z).card) →
      (∑ x ∈ (Finset.univ : Finset (Fin U)) \ Z,
          untouched_average probeSet (insert x Z) r) /
          ((((Finset.univ : Finset (Fin U)) \ Z).card : ℝ))
        = untouched_average probeSet Z (r + 1) := by
  intro U m r probeSet Z hr
  set B := (Finset.univ : Finset (Fin U)) \ Z with hB
  set N := B.card with hN
  have hNpos : 0 < N := lt_of_lt_of_le (Nat.succ_pos r) hr
  have hchoose1 : 0 < Nat.choose (N - 1) r :=
    Nat.choose_pos (by omega)
  have hchoose2 : 0 < Nat.choose N (r + 1) := Nat.choose_pos hr
  have hkey : ∀ x ∈ B, untouched_average probeSet (insert x Z) r
      = (∑ S ∈ Finset.powersetCard r (B.erase x),
          ((untouched_cells probeSet (Z ∪ insert x S)).card : ℝ)) /
        (Nat.choose (N - 1) r : ℝ) := by
    intro x hx
    rw [untouched_average, sdiff_insert_eq_erase_sdiff, ← hB,
      Finset.card_erase_of_mem hx, ← hN]
    refine congrArg (fun s => s / (Nat.choose (N - 1) r : ℝ)) ?_
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.insert_union, Finset.union_insert]
  rw [Finset.sum_congr rfl hkey, ← Finset.sum_div,
    sum_insert_powersetCard_double_count U r B
      (fun Y => ((untouched_cells probeSet (Z ∪ Y)).card : ℝ)),
    untouched_average, ← hB, ← hN]
  have habs : N * Nat.choose (N - 1) r = Nat.choose N (r + 1) * (r + 1) := by
    have := Nat.succ_mul_choose_eq (N - 1) r
    rw [Nat.succ_eq_add_one] at this
    rw [show N - 1 + 1 = N by omega] at this
    exact this
  have habsR : (N : ℝ) * (Nat.choose (N - 1) r : ℝ)
      = (Nat.choose N (r + 1) : ℝ) * ((r : ℝ) + 1) := by
    have := congrArg (fun k : ℕ => (k : ℝ)) habs
    push_cast at this
    exact this
  have h1 : ((Nat.choose (N - 1) r : ℝ)) ≠ 0 := by positivity
  have h2 : ((Nat.choose N (r + 1) : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr hchoose2.ne'
  have h3 : ((N : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
  rw [div_div, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination
    (-(∑ Y ∈ Finset.powersetCard (r + 1) B,
      ((untouched_cells probeSet (Z ∪ Y)).card : ℝ))) * habsR

@[blueprint "lem:untouched-average-swap-diff"
  (statement := /-- Let $p:\operatorname{Fin}(U)\to\mathcal P(\operatorname{Fin}(m))$ satisfy $|p(y)|\leq L$ for every key $y$, let $Z\subseteq\operatorname{Fin}(U)$, put $B\coloneqq\operatorname{Fin}(U)\setminus Z$, and let $r$ be a natural number.  Then for all $x,x'\in B$ the conditional averages of \cref{def:untouched-average} satisfy
  \[
    \bigl|A_r(Z\cup\{x\})-A_r(Z\cup\{x'\})\bigr|\leq L .
  \] -/)
  (proof := /-- Write $\Phi(W)\coloneqq|\operatorname{untouched}(p,W)|$.  If $x=x'$ the two averages coincide and the claim holds because $L\geq0$; assume $x\neq x'$ from now on.

  By \cref{lem:sdiff-insert-eq-erase-sdiff} we have $\operatorname{Fin}(U)\setminus(Z\cup\{y\})=B\setminus\{y\}$ for every key $y$, and $|B\setminus\{y\}|=|B|-1$ whenever $y\in B$.  Hence, by \cref{def:untouched-average},
  \[
    A_r(Z\cup\{y\})=\frac1K\sum_{S\subseteq B\setminus\{y\},\ |S|=r}\Phi\bigl((Z\cup\{y\})\cup S\bigr),
    \qquad K\coloneqq\binom{|B|-1}r ,
  \]
  for $y\in\{x,x'\}$.

  If $r>|B|-1$ then $K=0$ and the index family is empty for both $y$, so both averages are $0$ and the claim is trivial.  Assume therefore $r\leq|B|-1$, so that $K>0$.

  Let $\sigma$ be the transposition exchanging $x$ and $x'$.  If $S\subseteq B\setminus\{x\}$ then every $s\in S$ satisfies $s\neq x$ and $s\in B$, so $\sigma(s)$ equals $x\in B$ when $s=x'$ and equals $s$ otherwise; in both cases $\sigma(s)\in B\setminus\{x'\}$, using $x\neq x'$.  As $\sigma$ is injective, $S\mapsto\sigma(S)$ therefore maps $\{S\subseteq B\setminus\{x\}:|S|=r\}$ into $\{S'\subseteq B\setminus\{x'\}:|S'|=r\}$; the same argument with the roles of $x$ and $x'$ exchanged gives the reverse map, and $\sigma\circ\sigma=\operatorname{id}$ shows the two are mutually inverse.  Reindexing the second sum along this bijection,
  \[
    A_r(Z\cup\{x\})-A_r(Z\cup\{x'\})
      =\frac1K\sum_{S\subseteq B\setminus\{x\},\ |S|=r}
        \Bigl(\Phi\bigl((Z\cup\{x\})\cup S\bigr)-\Phi\bigl((Z\cup\{x'\})\cup\sigma(S)\bigr)\Bigr).
  \]

  Fix such an $S$ and distinguish two cases.  If $x'\in S$, then, since $x\notin S$, we have $\sigma(S)=(S\setminus\{x'\})\cup\{x\}$, whence
  \[
    (Z\cup\{x'\})\cup\sigma(S)=Z\cup\{x,x'\}\cup(S\setminus\{x'\})=Z\cup\{x\}\cup S
      =(Z\cup\{x\})\cup S,
  \]
  so the corresponding bracket vanishes.  If $x'\notin S$, then no element of $S$ is moved by $\sigma$, so $\sigma(S)=S$, and the bracket is
  \[
    \Phi\bigl(\{x\}\cup(Z\cup S)\bigr)-\Phi\bigl(\{x'\}\cup(Z\cup S)\bigr),
  \]
  which \cref{lem:untouched-cells-card-swap-diff}, applied to the key set $Z\cup S$ and the hypothesis $|p(y)|\leq L$, bounds by $L$ in absolute value.

  Thus every bracket is at most $L$ in absolute value, so by the triangle inequality the sum is at most $KL$ in absolute value; dividing by $K>0$ gives the assertion. -/)
  (title := /-- Bounded difference of conditional averages -/)
  (latexEnv := "lemma")]
lemma untouched_average_swap_diff :
    ∀ (U m L r : ℕ) (probeSet : Fin U → Finset (Fin m)) (Z : Finset (Fin U)),
      (∀ y : Fin U, (probeSet y).card ≤ L) →
      ∀ x ∈ (Finset.univ : Finset (Fin U)) \ Z,
        ∀ x' ∈ (Finset.univ : Finset (Fin U)) \ Z,
          |untouched_average probeSet (insert x Z) r -
              untouched_average probeSet (insert x' Z) r| ≤ (L : ℝ) := by
  intro U m L r probeSet Z hL x hx x' hx'
  set B := (Finset.univ : Finset (Fin U)) \ Z with hB
  have hcardx : (B.erase x).card = B.card - 1 := Finset.card_erase_of_mem hx
  have hcardx' : (B.erase x').card = B.card - 1 := Finset.card_erase_of_mem hx'
  rcases eq_or_ne x x' with rfl | hne
  · simpa using Nat.cast_nonneg (α := ℝ) L
  rcases lt_or_ge (B.card - 1) r with hlt | hge
  · have hzero : ∀ y ∈ B, untouched_average probeSet (insert y Z) r = 0 := by
      intro y hy
      rw [untouched_average, sdiff_insert_eq_erase_sdiff, ← hB,
        Finset.card_erase_of_mem hy]
      rw [Nat.choose_eq_zero_of_lt hlt]
      simp
    rw [hzero x hx, hzero x' hx']
    simpa using Nat.cast_nonneg (α := ℝ) L
  · set K := Nat.choose (B.card - 1) r with hK
    have hKpos : 0 < K := Nat.choose_pos hge
    have hKR : (0:ℝ) < (K : ℝ) := by exact_mod_cast hKpos
    have hmemimg : ∀ (u u' : Fin U) (S : Finset (Fin U)) (i : Fin U),
        i ∈ Finset.image (Equiv.swap u u') S ↔ (Equiv.swap u u') i ∈ S := by
      intro u u' S i
      rw [Finset.mem_image]
      constructor
      · rintro ⟨s, hs, rfl⟩
        rwa [Equiv.swap_apply_self]
      · intro h
        exact ⟨_, h, Equiv.swap_apply_self _ _ _⟩
    have himg : ∀ u u' : Fin U, u ≠ u' → u ∈ B → u' ∈ B →
        ∀ S ∈ Finset.powersetCard r (B.erase u),
          Finset.image (Equiv.swap u u') S ∈
            Finset.powersetCard r (B.erase u') := by
      intro u u' huu' huB _hu'B S hS
      rw [Finset.mem_powersetCard] at hS ⊢
      obtain ⟨hSsub, hScard⟩ := hS
      refine ⟨?_, ?_⟩
      · intro i hi
        rw [Finset.mem_image] at hi
        obtain ⟨s, hs, rfl⟩ := hi
        obtain ⟨hsu, hsB⟩ := Finset.mem_erase.mp (hSsub hs)
        rw [Finset.mem_erase]
        by_cases hsu' : s = u'
        · subst hsu'
          rw [Equiv.swap_apply_right]
          exact ⟨huu', huB⟩
        · rw [Equiv.swap_apply_of_ne_of_ne hsu hsu']
          exact ⟨hsu', hsB⟩
      · rw [Finset.card_image_of_injective _ (Equiv.swap u u').injective, hScard]
    have hsum2 :
        (∑ S ∈ Finset.powersetCard r (B.erase x),
            ((untouched_cells probeSet
              (insert x' Z ∪ Finset.image (Equiv.swap x x') S)).card : ℝ))
          = ∑ S' ∈ Finset.powersetCard r (B.erase x'),
              ((untouched_cells probeSet (insert x' Z ∪ S')).card : ℝ) := by
      refine Finset.sum_nbij' (i := fun S => Finset.image (Equiv.swap x x') S)
        (j := fun S' => Finset.image (Equiv.swap x x') S')
        (himg x x' hne hx hx') ?_ ?_ ?_ (fun S _ => rfl)
      · intro S' hS'
        have := himg x' x hne.symm hx' hx S' hS'
        rwa [Equiv.swap_comm] at this
      · intro S _
        rw [Finset.image_image]
        exact Finset.image_congr (fun i _ => Equiv.swap_apply_self x x' i)
          |>.trans Finset.image_id
      · intro S' _
        rw [Finset.image_image]
        exact Finset.image_congr (fun i _ => Equiv.swap_apply_self x x' i)
          |>.trans Finset.image_id
    have hterm : ∀ S ∈ Finset.powersetCard r (B.erase x),
        |((untouched_cells probeSet (insert x Z ∪ S)).card : ℝ) -
            ((untouched_cells probeSet
              (insert x' Z ∪ Finset.image (Equiv.swap x x') S)).card : ℝ)|
          ≤ (L : ℝ) := by
      intro S hS
      have hxS : x ∉ S := fun hmem =>
        (Finset.mem_erase.mp (Finset.mem_powersetCard.mp hS |>.1 hmem)).1 rfl
      by_cases hx'S : x' ∈ S
      · have hEq : insert x' Z ∪ Finset.image (Equiv.swap x x') S
            = insert x Z ∪ S := by
          ext i
          rw [Finset.mem_union, Finset.mem_union, Finset.mem_insert,
            Finset.mem_insert, hmemimg x x' S i]
          by_cases h1 : i = x
          · subst h1
            simp [Equiv.swap_apply_left, hx'S]
          · by_cases h2 : i = x'
            · subst h2
              simp [Equiv.swap_apply_right, hx'S]
            · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
              simp [h1, h2]
        rw [hEq]
        simpa using Nat.cast_nonneg (α := ℝ) L
      · have hEq : Finset.image (Equiv.swap x x') S = S := by
          ext i
          rw [hmemimg x x' S i]
          by_cases h1 : i = x
          · subst h1
            simp [Equiv.swap_apply_left, hxS, hx'S]
          · by_cases h2 : i = x'
            · subst h2
              simp [Equiv.swap_apply_right, hxS, hx'S]
            · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
        rw [hEq, Finset.insert_union, Finset.insert_union]
        exact untouched_cells_card_swap_diff U m L probeSet (Z ∪ S) hL x x'
    rw [untouched_average, untouched_average, sdiff_insert_eq_erase_sdiff,
      sdiff_insert_eq_erase_sdiff, ← hB, hcardx, hcardx', ← hK, ← hsum2,
      div_sub_div_same, abs_div, abs_of_pos hKR, div_le_iff₀ hKR,
      ← Finset.sum_sub_distrib]
    calc |∑ S ∈ Finset.powersetCard r (B.erase x),
            (((untouched_cells probeSet (insert x Z ∪ S)).card : ℝ) -
              ((untouched_cells probeSet
                (insert x' Z ∪ Finset.image (Equiv.swap x x') S)).card : ℝ))|
        ≤ ∑ S ∈ Finset.powersetCard r (B.erase x),
            |((untouched_cells probeSet (insert x Z ∪ S)).card : ℝ) -
              ((untouched_cells probeSet
                (insert x' Z ∪ Finset.image (Equiv.swap x x') S)).card : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _S ∈ Finset.powersetCard r (B.erase x), (L : ℝ) :=
          Finset.sum_le_sum hterm
      _ = (L : ℝ) * (K : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard, hcardx,
            ← hK]
          ring

@[blueprint "lem:untouched-mgf-induction"
  (statement := /-- Let $p:\operatorname{Fin}(U)\to\mathcal P(\operatorname{Fin}(m))$ satisfy $|p(y)|\leq L$ for every key $y$, and let $\theta\geq0$ satisfy $\theta L\leq1$.  Then for every natural number $r$ and every $Z\subseteq\operatorname{Fin}(U)$ with $r\leq|\operatorname{Fin}(U)\setminus Z|$,
  \[
    \sum_{S\subseteq\operatorname{Fin}(U)\setminus Z,\ |S|=r}
      e^{-\theta\,|\operatorname{untouched}(p,Z\cup S)|}
    \leq\binom{|\operatorname{Fin}(U)\setminus Z|}{r}\,
      e^{-\theta A_r(Z)}\,e^{r\theta^{2}L^{2}/2},
  \]
  where $A_r$ is the conditional average of \cref{def:untouched-average}. -/)
  (proof := /-- Induct on $r$, uniformly in $Z$.

  For $r=0$ the left-hand side is the single term indexed by $S=\emptyset$, namely $e^{-\theta|\operatorname{untouched}(p,Z)|}$, and by \cref{def:untouched-average} $A_0(Z)=\binom{|B|}0^{-1}|\operatorname{untouched}(p,Z)|=|\operatorname{untouched}(p,Z)|$ with $B\coloneqq\operatorname{Fin}(U)\setminus Z$.  The right-hand side is $1\cdot e^{-\theta A_0(Z)}\cdot e^{0}$, so the two sides are equal.

  Assume the statement for $r$ and all $Z$, and let $Z$ satisfy $r+1\leq|B|$, $B\coloneqq\operatorname{Fin}(U)\setminus Z$; in particular $|B|\geq1$, so $B$ is nonempty.  Splitting each $(r+1)$-subset $S\subseteq B$ according to a distinguished element and applying \cref{lem:sum-insert-powersetCard-double-count} to $B$, to $r$ and to the function $Y\mapsto e^{-\theta|\operatorname{untouched}(p,Z\cup Y)|}$,
  \[
    (r+1)\sum_{S\subseteq B,\ |S|=r+1}e^{-\theta|\operatorname{untouched}(p,Z\cup S)|}
      =\sum_{x\in B}\ \sum_{S'\subseteq B\setminus\{x\},\ |S'|=r}
        e^{-\theta|\operatorname{untouched}(p,Z\cup\{x\}\cup S')|} .
  \]
  For each $x\in B$ we have $\operatorname{Fin}(U)\setminus(Z\cup\{x\})=B\setminus\{x\}$ by \cref{lem:sdiff-insert-eq-erase-sdiff}, of cardinality $|B|-1\geq r$, so the induction hypothesis applied to $Z\cup\{x\}$ bounds the inner sum by $\binom{|B|-1}re^{-\theta A_r(Z\cup\{x\})}e^{r\theta^{2}L^{2}/2}$.  Summing over $x\in B$,
  \[
    (r+1)\sum_{S}e^{-\theta|\operatorname{untouched}(p,Z\cup S)|}
      \leq\binom{|B|-1}r e^{r\theta^{2}L^{2}/2}
        \sum_{x\in B}e^{-\theta A_r(Z\cup\{x\})} .
  \]

  The values $\nu(x)\coloneqq A_r(Z\cup\{x\})$, for $x\in B$, are pairwise within $L$ of one another by \cref{lem:untouched-average-swap-diff}.  Since $\theta\geq0$, $L>0$ and $\theta L\leq1$, \cref{lem:sum-exp-neg-le-of-pairwise-close} applied to the nonempty set $B$ gives
  \[
    \sum_{x\in B}e^{-\theta\nu(x)}
      \leq|B|\,e^{-\theta\bar\nu}e^{\theta^{2}L^{2}/2},
    \qquad \bar\nu=\frac1{|B|}\sum_{x\in B}\nu(x).
  \]
  By \cref{lem:untouched-average-tower}, $\bar\nu=A_{r+1}(Z)$.  Substituting,
  \[
    (r+1)\sum_{S}e^{-\theta|\operatorname{untouched}(p,Z\cup S)|}
      \leq\binom{|B|-1}r|B|\,e^{-\theta A_{r+1}(Z)}e^{(r+1)\theta^{2}L^{2}/2},
  \]
  where the two exponential factors were combined using $e^{a}e^{b}=e^{a+b}$.  Finally the absorption identity $|B|\binom{|B|-1}r=\binom{|B|}{r+1}(r+1)$ holds because $|B|\geq1$, and dividing by $r+1>0$ gives exactly the assertion for $r+1$. -/)
  (title := /-- Inductive exponential moment bound -/)
  (latexEnv := "lemma")]
lemma untouched_mgf_induction :
    ∀ (U m L : ℕ) (probeSet : Fin U → Finset (Fin m)) (theta : ℝ),
      0 < L → (∀ y : Fin U, (probeSet y).card ≤ L) →
      0 ≤ theta → theta * (L : ℝ) ≤ 1 →
      ∀ (r : ℕ) (Z : Finset (Fin U)),
        r ≤ (((Finset.univ : Finset (Fin U)) \ Z).card) →
        (∑ S ∈ Finset.powersetCard r ((Finset.univ : Finset (Fin U)) \ Z),
            Real.exp (-theta * ((untouched_cells probeSet (Z ∪ S)).card : ℝ)))
          ≤ (Nat.choose (((Finset.univ : Finset (Fin U)) \ Z).card) r : ℝ) *
              Real.exp (-theta * untouched_average probeSet Z r) *
              Real.exp ((r : ℝ) * (theta ^ 2 * (L : ℝ) ^ 2 / 2)) := by
  intro U m L probeSet theta hLpos hL htheta hthetaL r
  have hLR : (0:ℝ) < (L : ℝ) := by exact_mod_cast hLpos
  induction r with
  | zero =>
      intro Z _
      rw [Finset.powersetCard_zero, untouched_average]
      simp
  | succ r ih =>
      intro Z hr
      set B := (Finset.univ : Finset (Fin U)) \ Z with hB
      set N := B.card with hN
      have hNpos : 0 < N := lt_of_lt_of_le (Nat.succ_pos r) hr
      have hBne : B.Nonempty := Finset.card_pos.mp hNpos
      have hNR : (0:ℝ) < (N : ℝ) := by exact_mod_cast hNpos
      have hdouble := sum_insert_powersetCard_double_count U r B
        (fun Y => Real.exp (-theta *
          ((untouched_cells probeSet (Z ∪ Y)).card : ℝ)))
      have hinner : ∀ x ∈ B,
          (∑ S ∈ Finset.powersetCard r (B.erase x),
              Real.exp (-theta *
                ((untouched_cells probeSet (Z ∪ insert x S)).card : ℝ)))
            ≤ (Nat.choose (N - 1) r : ℝ) *
                Real.exp (-theta * untouched_average probeSet (insert x Z) r) *
                Real.exp ((r : ℝ) * (theta ^ 2 * (L : ℝ) ^ 2 / 2)) := by
        intro x hx
        have hcard : ((Finset.univ : Finset (Fin U)) \ insert x Z).card = N - 1 := by
          rw [sdiff_insert_eq_erase_sdiff, ← hB, Finset.card_erase_of_mem hx]
        have hle : r ≤ ((Finset.univ : Finset (Fin U)) \ insert x Z).card := by
          rw [hcard]; omega
        have := ih (insert x Z) hle
        rw [hcard] at this
        refine le_trans (le_of_eq ?_) this
        rw [sdiff_insert_eq_erase_sdiff, ← hB]
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [Finset.insert_union, Finset.union_insert]
      have hstep1 : ((r : ℝ) + 1) *
          (∑ Y ∈ Finset.powersetCard (r + 1) B,
            Real.exp (-theta * ((untouched_cells probeSet (Z ∪ Y)).card : ℝ)))
          ≤ (Nat.choose (N - 1) r : ℝ) *
              Real.exp ((r : ℝ) * (theta ^ 2 * (L : ℝ) ^ 2 / 2)) *
              ∑ x ∈ B,
                Real.exp (-theta * untouched_average probeSet (insert x Z) r) := by
        rw [← hdouble, Finset.mul_sum]
        refine Finset.sum_le_sum fun x hx => ?_
        refine le_trans (hinner x hx) (le_of_eq ?_)
        ring
      have hclose := sum_exp_neg_le_of_pairwise_close U B
        (fun x => untouched_average probeSet (insert x Z) r) theta (L : ℝ)
        htheta hLR hthetaL hBne
        (fun x hx x' hx' =>
          untouched_average_swap_diff U m L r probeSet Z hL x hx x' hx')
      have htower := untouched_average_tower U m r probeSet Z hr
      rw [← hB, ← hN] at htower
      rw [htower] at hclose
      have hchoose1 : 0 < Nat.choose (N - 1) r := Nat.choose_pos (by omega)
      have habsR : (N : ℝ) * (Nat.choose (N - 1) r : ℝ)
          = (Nat.choose N (r + 1) : ℝ) * ((r : ℝ) + 1) := by
        have h := Nat.succ_mul_choose_eq (N - 1) r
        rw [Nat.succ_eq_add_one, show N - 1 + 1 = N by omega] at h
        exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) h
      have hcoef : (0:ℝ) ≤ (Nat.choose (N - 1) r : ℝ) *
          Real.exp ((r : ℝ) * (theta ^ 2 * (L : ℝ) ^ 2 / 2)) := by positivity
      have hstep2 := le_trans hstep1
        (mul_le_mul_of_nonneg_left hclose hcoef)
      have hrpos : (0:ℝ) < (r : ℝ) + 1 := by positivity
      rw [← mul_le_mul_iff_of_pos_left hrpos]
      refine le_trans hstep2 (le_of_eq ?_)
      rw [← hN, Nat.cast_add, Nat.cast_one]
      have hexp : Real.exp (((r : ℝ) + 1) * (theta ^ 2 * (L : ℝ) ^ 2 / 2))
          = Real.exp ((r : ℝ) * (theta ^ 2 * (L : ℝ) ^ 2 / 2)) *
            Real.exp (theta ^ 2 * (L : ℝ) ^ 2 / 2) := by
        rw [← Real.exp_add]
        ring_nf
      rw [hexp]
      linear_combination
        (Real.exp (-theta * untouched_average probeSet Z (r + 1)) *
          Real.exp ((r : ℝ) * (theta ^ 2 * (L : ℝ) ^ 2 / 2)) *
          Real.exp (theta ^ 2 * (L : ℝ) ^ 2 / 2)) * habsR

@[blueprint "lem:untouched-cells-chernoff"
  (statement := /-- Let $U,n,m,L$ be natural numbers with $n\leq U$ and $0<L$, let $p:\operatorname{Fin}(U)\to\mathcal P(\operatorname{Fin}(m))$ satisfy $|p(x)|\leq L$ for every key $x$, and let $\lambda$ and $\theta$ be real numbers with $\theta\geq0$ and $\theta L\leq1$.  Write $\mu\coloneqq\binom Un^{-1}\sum_{X}|\operatorname{untouched}(p,X)|$ for the average of \cref{def:untouched-cells} over the $n$-subsets of $\operatorname{Fin}(U)$.  Then
  \[
    \#\left\{X:|X|=n,\ \bigl|\operatorname{untouched}(p,X)\bigr|\leq\mu-\lambda\right\}
    \leq\binom Un\exp\!\left(\frac{n\theta^{2}L^{2}}2-\theta\lambda\right).
  \] -/)
  (proof := /-- Write $\Phi(X)\coloneqq|\operatorname{untouched}(p,X)|$ and let $F$ denote the set on the left-hand side.

  Apply \cref{lem:untouched-mgf-induction} with $r\coloneqq n$ and $Z\coloneqq\emptyset$.  Then $\operatorname{Fin}(U)\setminus\emptyset=\operatorname{Fin}(U)$ has cardinality $U\geq n$, and $\emptyset\cup S=S$, so by \cref{def:untouched-average} the conditional average $A_n(\emptyset)$ is exactly $\mu$ and the conclusion reads
  \[
    \sum_{X:|X|=n}e^{-\theta\Phi(X)}\leq\binom Un e^{-\theta\mu}e^{n\theta^{2}L^{2}/2}. \tag{$*$}
  \]

  On the other hand, every $X\in F$ satisfies $\Phi(X)\leq\mu-\lambda$, hence $-\theta\Phi(X)\geq-\theta(\mu-\lambda)$ because $\theta\geq0$, and the monotonicity of the exponential gives $e^{-\theta\Phi(X)}\geq e^{-\theta\mu}e^{\theta\lambda}$.  Summing this over $X\in F$ and then enlarging the index set from $F$ to all $n$-subsets, which is legitimate because every summand $e^{-\theta\Phi(X)}$ is positive,
  \[
    |F|\,e^{-\theta\mu}e^{\theta\lambda}
      \leq\sum_{X\in F}e^{-\theta\Phi(X)}
      \leq\sum_{X:|X|=n}e^{-\theta\Phi(X)} .
  \]

  Combining with $(*)$ and cancelling the positive factor $e^{-\theta\mu}$ yields $|F|\,e^{\theta\lambda}\leq\binom Une^{n\theta^{2}L^{2}/2}$.  Dividing by $e^{\theta\lambda}>0$ and using $e^{-\theta\lambda}=1/e^{\theta\lambda}$ together with $e^{a}e^{b}=e^{a+b}$ gives the assertion. -/)
  (title := /-- Exponential-moment deviation bound -/)
  (latexEnv := "lemma")]
lemma untouched_cells_chernoff :
    ∀ (U n m L : ℕ) (probeSet : Fin U → Finset (Fin m)) (lam theta : ℝ),
      n ≤ U → 0 < L →
      (∀ x : Fin U, (probeSet x).card ≤ L) →
      0 ≤ theta → theta * (L : ℝ) ≤ 1 →
      (((Finset.powersetCard n (Finset.univ : Finset (Fin U))).filter
          (fun X =>
            ((untouched_cells probeSet X).card : ℝ) ≤
              (∑ Y ∈ Finset.powersetCard n (Finset.univ : Finset (Fin U)),
                  ((untouched_cells probeSet Y).card : ℝ)) /
                (Nat.choose U n : ℝ) - lam)).card : ℝ)
        ≤ (Nat.choose U n : ℝ) *
            Real.exp ((n : ℝ) * theta ^ 2 * (L : ℝ) ^ 2 / 2 - theta * lam) := by
  intro U n m L probeSet lam theta hnU hLpos hL htheta hthetaL
  set mu : ℝ :=
    (∑ Y ∈ Finset.powersetCard n (Finset.univ : Finset (Fin U)),
      ((untouched_cells probeSet Y).card : ℝ)) / (Nat.choose U n : ℝ) with hmu
  set F := (Finset.powersetCard n (Finset.univ : Finset (Fin U))).filter
    (fun X => ((untouched_cells probeSet X).card : ℝ) ≤ mu - lam) with hF
  have huniv : (Finset.univ : Finset (Fin U)) \ (∅ : Finset (Fin U))
      = (Finset.univ : Finset (Fin U)) := Finset.sdiff_empty
  have hcard : ((Finset.univ : Finset (Fin U)) \ (∅ : Finset (Fin U))).card = U := by
    rw [huniv, Finset.card_univ, Fintype.card_fin]
  have hmgf := untouched_mgf_induction U m L probeSet theta hLpos hL htheta
    hthetaL n ∅ (by rw [hcard]; exact hnU)
  rw [hcard, huniv] at hmgf
  simp only [Finset.empty_union] at hmgf
  have havg : untouched_average probeSet ∅ n = mu := by
    rw [untouched_average, hcard, huniv, hmu]
    simp only [Finset.empty_union]
  rw [havg] at hmgf
  have hlow : (F.card : ℝ) * (Real.exp (-theta * mu) * Real.exp (theta * lam))
      ≤ ∑ X ∈ Finset.powersetCard n (Finset.univ : Finset (Fin U)),
          Real.exp (-theta * ((untouched_cells probeSet X).card : ℝ)) := by
    calc (F.card : ℝ) * (Real.exp (-theta * mu) * Real.exp (theta * lam))
        = ∑ _X ∈ F, Real.exp (-theta * mu) * Real.exp (theta * lam) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ X ∈ F,
            Real.exp (-theta * ((untouched_cells probeSet X).card : ℝ)) := by
          refine Finset.sum_le_sum fun X hX => ?_
          have hXle : ((untouched_cells probeSet X).card : ℝ) ≤ mu - lam :=
            (Finset.mem_filter.mp hX).2
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          nlinarith [htheta]
      _ ≤ ∑ X ∈ Finset.powersetCard n (Finset.univ : Finset (Fin U)),
            Real.exp (-theta * ((untouched_cells probeSet X).card : ℝ)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) fun X _ _ => (Real.exp_pos _).le
  have hcombine : (F.card : ℝ) * (Real.exp (-theta * mu) * Real.exp (theta * lam))
      ≤ (Nat.choose U n : ℝ) * Real.exp (-theta * mu) *
          Real.exp ((n : ℝ) * (theta ^ 2 * (L : ℝ) ^ 2 / 2)) :=
    le_trans hlow hmgf
  have hexppos : (0:ℝ) < Real.exp (-theta * mu) := Real.exp_pos _
  have hlampos : (0:ℝ) < Real.exp (theta * lam) := Real.exp_pos _
  rw [← mul_le_mul_iff_of_pos_left hexppos]
  calc Real.exp (-theta * mu) * (F.card : ℝ)
      = ((F.card : ℝ) * (Real.exp (-theta * mu) * Real.exp (theta * lam))) /
          Real.exp (theta * lam) := by
        field_simp
    _ ≤ ((Nat.choose U n : ℝ) * Real.exp (-theta * mu) *
          Real.exp ((n : ℝ) * (theta ^ 2 * (L : ℝ) ^ 2 / 2))) /
          Real.exp (theta * lam) := by
        gcongr
    _ = Real.exp (-theta * mu) *
          ((Nat.choose U n : ℝ) *
            Real.exp ((n : ℝ) * theta ^ 2 * (L : ℝ) ^ 2 / 2 - theta * lam)) := by
        rw [Real.exp_sub]
        field_simp

@[blueprint "lem:untouched-cells-filter-empty"
  (statement := /-- Let $U,n,m,L$ be natural numbers with $n\leq U$, let $p:\operatorname{Fin}(U)\to\mathcal P(\operatorname{Fin}(m))$ satisfy $|p(x)|\leq L$ for every key $x$, and let $\lambda>nL$.  Writing $\mu\coloneqq\binom Un^{-1}\sum_{X}|\operatorname{untouched}(p,X)|$ for the average of \cref{def:untouched-cells} over the $n$-subsets of $\operatorname{Fin}(U)$, the set
  \[
    \left\{X:|X|=n,\ \bigl|\operatorname{untouched}(p,X)\bigr|\leq\mu-\lambda\right\}
  \]
  is empty. -/)
  (proof := /-- Write $\Phi(X)\coloneqq|\operatorname{untouched}(p,X)|$ and suppose, for contradiction, that some $n$-subset $X$ satisfies $\Phi(X)\leq\mu-\lambda$.

  First, $\Phi(X)\geq m-nL$.  Indeed, by \cref{def:untouched-cells} the set $\operatorname{untouched}(p,X)$ is the complement in $\operatorname{Fin}(m)$ of $\bigcup_{x\in X}p(x)$, so $\Phi(X)=m-\bigl|\bigcup_{x\in X}p(x)\bigr|$, while
  \[
    \Bigl|\bigcup_{x\in X}p(x)\Bigr|\leq\sum_{x\in X}|p(x)|\leq|X|\cdot L=nL ,
  \]
  using $|p(x)|\leq L$ and $|X|=n$.

  Second, $\mu\leq m$.  Every $\Phi(Y)$ is the cardinality of a subset of $\operatorname{Fin}(m)$, hence at most $m$; summing over the $\binom Un$ subsets $Y$ gives $\sum_Y\Phi(Y)\leq\binom Un m$, and $\binom Un>0$ because $n\leq U$, so dividing by $\binom Un$ yields $\mu\leq m$.

  Combining, $m-nL\leq\Phi(X)\leq\mu-\lambda\leq m-\lambda$, whence $\lambda\leq nL$, contradicting $\lambda>nL$. -/)
  (title := /-- No key set deviates by more than the total probe budget -/)
  (latexEnv := "lemma")]
lemma untouched_cells_filter_empty :
    ∀ (U n m L : ℕ) (probeSet : Fin U → Finset (Fin m)) (lam : ℝ),
      n ≤ U →
      (∀ x : Fin U, (probeSet x).card ≤ L) →
      (n : ℝ) * (L : ℝ) < lam →
      ((Finset.powersetCard n (Finset.univ : Finset (Fin U))).filter
          (fun X =>
            ((untouched_cells probeSet X).card : ℝ) ≤
              (∑ Y ∈ Finset.powersetCard n (Finset.univ : Finset (Fin U)),
                  ((untouched_cells probeSet Y).card : ℝ)) /
                (Nat.choose U n : ℝ) - lam)) = ∅ := by
  intro U n m L probeSet lam hnU hL hlam
  have hchoose : 0 < Nat.choose U n := Nat.choose_pos hnU
  have hchooseR : (0:ℝ) < (Nat.choose U n : ℝ) := by exact_mod_cast hchoose
  have hle : ∀ Y : Finset (Fin U),
      ((untouched_cells probeSet Y).card : ℝ) ≤ (m : ℝ) := by
    intro Y
    have := Finset.card_le_univ (untouched_cells probeSet Y)
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have hmu : (∑ Y ∈ Finset.powersetCard n (Finset.univ : Finset (Fin U)),
      ((untouched_cells probeSet Y).card : ℝ)) / (Nat.choose U n : ℝ)
      ≤ (m : ℝ) := by
    rw [div_le_iff₀ hchooseR]
    calc (∑ Y ∈ Finset.powersetCard n (Finset.univ : Finset (Fin U)),
          ((untouched_cells probeSet Y).card : ℝ))
        ≤ ∑ _Y ∈ Finset.powersetCard n (Finset.univ : Finset (Fin U)), (m : ℝ) :=
          Finset.sum_le_sum fun Y _ => hle Y
      _ = (m : ℝ) * (Nat.choose U n : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard,
            Finset.card_univ, Fintype.card_fin]
          ring
  rw [Finset.filter_eq_empty_iff]
  intro X hX hcontra
  have hXcard : X.card = n := (Finset.mem_powersetCard.mp hX).2
  have hunion : (X.biUnion probeSet).card ≤ n * L := by
    calc (X.biUnion probeSet).card ≤ ∑ x ∈ X, (probeSet x).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ X, L := Finset.sum_le_sum fun x _ => hL x
      _ = n * L := by rw [Finset.sum_const, smul_eq_mul, hXcard]
  have hlow : (m : ℝ) - (n : ℝ) * (L : ℝ)
      ≤ ((untouched_cells probeSet X).card : ℝ) := by
    have hcard : (untouched_cells probeSet X).card
        = m - (X.biUnion probeSet).card := by
      rw [untouched_cells, Finset.card_univ_sdiff, Fintype.card_fin]
    have hleq : (X.biUnion probeSet).card ≤ m :=
      le_trans (Finset.card_le_univ _)
        (by rw [Fintype.card_fin])
    rw [hcard]
    have hsub : ((m - (X.biUnion probeSet).card : ℕ) : ℝ)
        = (m : ℝ) - ((X.biUnion probeSet).card : ℝ) := by
      exact Nat.cast_sub hleq
    rw [hsub]
    have : ((X.biUnion probeSet).card : ℝ) ≤ (n : ℝ) * (L : ℝ) := by
      exact_mod_cast hunion
    linarith
  linarith [hle X, hmu, hlow, hcontra]

@[blueprint "lem:untouched-cells-deviation-count"
  (statement := /-- Let $U,n,m,L$ be natural numbers with $n\leq U$ and $0<L$, let $p:\operatorname{Fin}(U)\to\mathcal P(\operatorname{Fin}(m))$ satisfy $|p(x)|\leq L$ for every key $x$, and let $\lambda\geq0$.  Write $\mu\coloneqq\binom Un^{-1}\sum_{X}|\operatorname{untouched}(p,X)|$ for the average of \cref{def:untouched-cells} over the $n$-subsets $X$ of $\operatorname{Fin}(U)$.  Then
  \[
    \#\left\{X:|X|=n,\ \bigl|\operatorname{untouched}(p,X)\bigr|\leq\mu-\lambda\right\}
    \leq\binom Un\exp\!\left(-\frac{\lambda^{2}}{2nL^{2}}\right).
  \]
  Equivalently, a uniformly random $n$-subset leaves at most $\mu-\lambda$ cells unread with probability at most $e^{-\lambda^{2}/(2nL^{2})}$. -/)
  (proof := /-- Write $\Phi(X)\coloneqq|\operatorname{untouched}(p,X)|$ and let $F$ denote the counted set, so the claim is $|F|\leq\binom Un e^{-\lambda^{2}/(2nL^{2})}$.

  \emph{Degenerate case $n=0$.}  There is exactly one $0$-subset, namely $\emptyset$, so $F\subseteq\{\emptyset\}$ gives $|F|\leq1$.  On the right, $\binom U0=1$ and the exponent $-\lambda^{2}/(2\cdot0\cdot L^{2})$ has vanishing denominator, so the exponential factor is $e^{0}=1$; the bound reads $|F|\leq1$ and holds.  Assume $n\geq1$ from now on, so $n>0$ as a real number.

  \emph{Case $\lambda>nL$.}  Here \cref{lem:untouched-cells-filter-empty}, whose hypotheses $n\leq U$ and $|p(x)|\leq L$ are available, shows $F=\emptyset$, so $|F|=0$, while the right-hand side is a product of nonnegative factors; the bound is immediate.

  \emph{Case $\lambda\leq nL$.}  Set
  \[
    \theta\coloneqq\frac{\lambda}{nL^{2}} ,
  \]
  which is nonnegative because $\lambda\geq0$, $n>0$ and $L>0$.  Moreover $\theta L\leq1$: clearing the positive denominator, this is $\lambda L\leq nL^{2}$, which follows from $\lambda\leq nL$ on multiplying by $L>0$.

  Apply \cref{lem:untouched-cells-chernoff} with this $\theta$; its hypotheses $n\leq U$, $0<L$, $|p(x)|\leq L$, $\theta\geq0$ and $\theta L\leq1$ all hold.  It gives
  \[
    |F|\leq\binom Un\exp\!\left(\frac{n\theta^{2}L^{2}}2-\theta\lambda\right).
  \]
  Since $\binom Un\geq0$, it suffices to compare the exponents, and by the monotonicity of the exponential it suffices to prove
  \[
    \frac{n\theta^{2}L^{2}}2-\theta\lambda\leq-\frac{\lambda^{2}}{2nL^{2}} .
  \]
  Substituting $\theta=\lambda/(nL^{2})$ and clearing the positive denominator $2nL^{2}$, the left-hand side equals
  \[
    \frac{n L^{2}}2\cdot\frac{\lambda^{2}}{n^{2}L^{4}}-\frac{\lambda^{2}}{nL^{2}}
      =\frac{\lambda^{2}}{2nL^{2}}-\frac{\lambda^{2}}{nL^{2}}
      =-\frac{\lambda^{2}}{2nL^{2}} ,
  \]
  so the required inequality holds with equality.  This is exactly the choice of $\theta$ optimizing the exponential-moment bound, and it completes the proof. -/)
  (title := /-- Few key sets read unusually many cells -/)
  (latexEnv := "lemma")]
lemma untouched_cells_deviation_count :
    ∀ (U n m L : ℕ) (probeSet : Fin U → Finset (Fin m)) (lam : ℝ),
      n ≤ U → 0 < L →
      (∀ x : Fin U, (probeSet x).card ≤ L) →
      0 ≤ lam →
      (((Finset.powersetCard n (Finset.univ : Finset (Fin U))).filter
          (fun X =>
            ((untouched_cells probeSet X).card : ℝ) ≤
              (∑ Y ∈ Finset.powersetCard n (Finset.univ : Finset (Fin U)),
                  ((untouched_cells probeSet Y).card : ℝ)) /
                (Nat.choose U n : ℝ) - lam)).card : ℝ)
        ≤ (Nat.choose U n : ℝ) *
            Real.exp (-(lam ^ 2) / (2 * (n : ℝ) * (L : ℝ) ^ 2)) := by
  intro U n m L probeSet lam hnU hLpos hL hlam
  have hLR : (0:ℝ) < (L : ℝ) := by exact_mod_cast hLpos
  set F := (Finset.powersetCard n (Finset.univ : Finset (Fin U))).filter
    (fun X =>
      ((untouched_cells probeSet X).card : ℝ) ≤
        (∑ Y ∈ Finset.powersetCard n (Finset.univ : Finset (Fin U)),
            ((untouched_cells probeSet Y).card : ℝ)) /
          (Nat.choose U n : ℝ) - lam) with hF
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · have hFsub : F ⊆ Finset.powersetCard 0 (Finset.univ : Finset (Fin U)) :=
      Finset.filter_subset _ _
    have hcardF : (F.card : ℝ) ≤ 1 := by
      have := Finset.card_le_card hFsub
      rw [Finset.card_powersetCard, Nat.choose_zero_right] at this
      exact_mod_cast this
    rw [Nat.choose_zero_right]
    norm_num
    simpa using hcardF
  · have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    rcases le_or_gt lam ((n : ℝ) * (L : ℝ)) with hsmall | hbig
    · set theta : ℝ := lam / ((n : ℝ) * (L : ℝ) ^ 2) with htheta
      have hthetanonneg : 0 ≤ theta := by positivity
      have hthetaL : theta * (L : ℝ) ≤ 1 := by
        rw [htheta, div_mul_eq_mul_div, div_le_one (by positivity)]
        nlinarith [hLR, hnR, hsmall]
      have hmain := untouched_cells_chernoff U n m L probeSet lam theta hnU
        hLpos hL hthetanonneg hthetaL
      refine le_trans hmain ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      rw [htheta]
      field_simp
      linarith
    · have hempty := untouched_cells_filter_empty U n m L probeSet lam hnU hL hbig
      rw [hF, hempty]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity

@[blueprint "def:retrieval-replay-probe-tree"
  (statement := /-- Given a finite stream of cell words, a cache of previously read cells, and a probe budget, replay a retrieval probe tree by consuming one stream word exactly when a cell is requested for the first time.  The result consists of the updated cache, the unused suffix of the stream, and the returned value when the tree terminates within the budget. -/)
  (title := /-- Cached replay of one retrieval query -/)
  (latexEnv := "definition")]
def retrieval_replay_probe_tree {m w V : ℕ}
    (cache : Fin m → Option (BitVec w)) (stream : List (BitVec w)) :
    ℕ → retrieval_probe_tree m w V →
      ((Fin m → Option (BitVec w)) × List (BitVec w)) × Option (Fin V)
  | _, .answer output => ((cache, stream), some output)
  | 0, .probe _ _ => ((cache, stream), none)
  | L + 1, .probe address next =>
      match cache address with
      | some word => retrieval_replay_probe_tree cache stream L (next word)
      | none =>
          match stream with
          | [] => ((cache, []), none)
          | word :: rest =>
              retrieval_replay_probe_tree
                (Function.update cache address (some word)) rest L (next word)

@[blueprint "def:retrieval-replay-probe-list"
  (statement := /-- Replay a finite list of retrieval probe trees in order with a common cache and word stream, using the same probe budget for every tree, and record the optional output of each replay. -/)
  (title := /-- Cached replay of a list of retrieval queries -/)
  (latexEnv := "definition")]
def retrieval_replay_probe_list {m w V : ℕ} :
    (Fin m → Option (BitVec w)) → List (BitVec w) → ℕ →
      List (retrieval_probe_tree m w V) →
      ((Fin m → Option (BitVec w)) × List (BitVec w)) × List (Option (Fin V))
  | cache, stream, _, [] => ((cache, stream), [])
  | cache, stream, L, tree :: trees =>
      let first := retrieval_replay_probe_tree cache stream L tree
      let rest := retrieval_replay_probe_list first.1.1 first.1.2 L trees
      (rest.1, first.2 :: rest.2)

@[blueprint "def:retrieval-trace-probe-tree"
  (statement := /-- For a fixed memory, an initial set of known cells, and a probe budget, trace one retrieval probe tree.  The trace records, in first-request order, each newly encountered address together with its memory word, and also records the optional output when execution terminates within the budget. -/)
  (title := /-- First-request trace of one retrieval query -/)
  (latexEnv := "definition")]
def retrieval_trace_probe_tree {m w V : ℕ} (memory : Fin m → BitVec w) :
    Finset (Fin m) → ℕ → retrieval_probe_tree m w V →
      (Finset (Fin m) × List (Fin m × BitVec w)) × Option (Fin V)
  | seen, _, .answer output => ((seen, []), some output)
  | seen, 0, .probe _ _ => ((seen, []), none)
  | seen, L + 1, .probe address next =>
      if address ∈ seen then
        retrieval_trace_probe_tree memory seen L (next (memory address))
      else
        let rest := retrieval_trace_probe_tree memory (insert address seen) L
          (next (memory address))
        ((rest.1.1, (address, memory address) :: rest.1.2), rest.2)

@[blueprint "def:retrieval-trace-probe-list"
  (statement := /-- Trace a finite list of retrieval probe trees against one memory in order, carrying the set of previously encountered cells between queries and concatenating their first-request traces. -/)
  (title := /-- First-request trace of a list of retrieval queries -/)
  (latexEnv := "definition")]
def retrieval_trace_probe_list {m w V : ℕ} (memory : Fin m → BitVec w) :
    Finset (Fin m) → ℕ → List (retrieval_probe_tree m w V) →
      (Finset (Fin m) × List (Fin m × BitVec w)) × List (Option (Fin V))
  | seen, _, [] => ((seen, []), [])
  | seen, L, tree :: trees =>
      let first := retrieval_trace_probe_tree memory seen L tree
      let rest := retrieval_trace_probe_list memory first.1.1 L trees
      ((rest.1.1, first.1.2 ++ rest.1.2), first.2 :: rest.2)

@[blueprint "def:retrieval-cache-of-memory"
  (statement := /-- The cache induced by a memory and a finite set of known addresses stores the memory word at each known address and is undefined elsewhere. -/)
  (title := /-- Cache induced by a memory -/)
  (latexEnv := "definition")]
def retrieval_cache_of_memory {m w : ℕ} (memory : Fin m → BitVec w)
    (seen : Finset (Fin m)) : Fin m → Option (BitVec w) :=
  fun address => if address ∈ seen then some (memory address) else none

@[blueprint "def:probed-cells-list-upto"
  (statement := /-- The cells probed by a list of retrieval probe trees up to a common budget are the union of their truncated probe sets from \cref{def:probed-cells-upto}. -/)
  (title := /-- Truncated probe set of a query list -/)
  (latexEnv := "definition")]
def probed_cells_list_upto {m w V : ℕ} (memory : Fin m → BitVec w) (L : ℕ) :
    List (retrieval_probe_tree m w V) → Finset (Fin m)
  | [] => ∅
  | tree :: trees =>
      probed_cells_upto memory L tree ∪ probed_cells_list_upto memory L trees

@[blueprint "lem:retrieval-trace-probe-tree-spec"
  (statement := /-- Let $D$ be a memory, let $A$ be a finite set of already known addresses, let $L$ be a probe budget, and let $Q$ be a retrieval probe tree.  The trace of \cref{def:retrieval-trace-probe-tree} has final known set $A\cup\operatorname{probed}_{\leq L}(D,Q)$; its number of recorded words is the increase in the cardinality of the known set; its optional output is the execution result exactly when the probe count is at most $L$; and replaying its recorded words from the cache induced by $D$ and $A$ reproduces the final cache and optional output while leaving any appended suffix unused. -/)
  (proof := /-- Induct on the budget $L$.  A leaf records no word, leaves the cache unchanged, and returns its answer.  A probe with zero budget records no word and returns no answer.  For a positive budget at a probe node, distinguish whether its address is already in $A$.  If it is, both tracing and replay use the cached word and the induction hypothesis applies to the selected continuation.  If it is not, tracing records the memory word, inserts the address into $A$, and then invokes the continuation.  Replay consumes precisely that new head word, its cache update is the cache induced by the enlarged known set, and the induction hypothesis applies.  The cardinality identity follows from the fact that insertion of a new address increases cardinality by one.  The definitions \cref{def:retrieval-trace-probe-tree}, \cref{def:retrieval-replay-probe-tree}, \cref{def:retrieval-cache-of-memory}, \cref{def:probed-cells-upto}, \cref{def:count-retrieval-probes}, and \cref{def:execute-retrieval-probe-tree} give the four assertions in each case. -/)
  (title := /-- Correctness of a first-request query trace -/)
  (latexEnv := "lemma")]
lemma retrieval_trace_probe_tree_spec :
    ∀ {m w V : ℕ} (memory : Fin m → BitVec w) (seen : Finset (Fin m))
      (L : ℕ) (tree : retrieval_probe_tree m w V),
      let trace := retrieval_trace_probe_tree memory seen L tree
      trace.1.1 = seen ∪ probed_cells_upto memory L tree ∧
      seen.card + trace.1.2.length = trace.1.1.card ∧
      trace.2 = (if count_retrieval_probes memory tree ≤ L then
          some (execute_retrieval_probe_tree memory tree) else none) ∧
      ∀ extra : List (BitVec w),
        retrieval_replay_probe_tree (retrieval_cache_of_memory memory seen)
            (trace.1.2.map Prod.snd ++ extra) L tree =
          ((retrieval_cache_of_memory memory trace.1.1, extra), trace.2) := by
  intro m w V memory seen L
  induction L generalizing seen with
  | zero =>
      intro tree
      cases tree with
      | answer output =>
          simp [retrieval_trace_probe_tree, retrieval_replay_probe_tree,
            probed_cells_upto, count_retrieval_probes,
            execute_retrieval_probe_tree]
      | probe address next =>
          simp [retrieval_trace_probe_tree, retrieval_replay_probe_tree,
            probed_cells_upto, count_retrieval_probes]
  | succ L ih =>
      intro tree
      cases tree with
      | answer output =>
          simp [retrieval_trace_probe_tree, retrieval_replay_probe_tree,
            probed_cells_upto, count_retrieval_probes,
            execute_retrieval_probe_tree]
      | probe address next =>
          by_cases haddress : address ∈ seen
          · have hrec := ih seen (next (memory address))
            rw [retrieval_trace_probe_tree, if_pos haddress]
            rcases hrec with ⟨hseen, hcard, hout, hreplay⟩
            constructor
            · rw [probed_cells_upto]
              simpa [hseen, haddress, Finset.union_assoc, Finset.union_left_comm,
                Finset.union_comm]
            constructor
            · exact hcard
            constructor
            · have hle : 1 + count_retrieval_probes memory (next (memory address)) ≤ L + 1 ↔
                  count_retrieval_probes memory (next (memory address)) ≤ L := by omega
              simpa only [probed_cells_upto, count_retrieval_probes,
                execute_retrieval_probe_tree, hle] using hout
            · intro extra
              simpa [retrieval_replay_probe_tree, retrieval_cache_of_memory,
                haddress] using hreplay extra
          · have hcache : Function.update (retrieval_cache_of_memory memory seen) address
                (some (memory address)) =
              retrieval_cache_of_memory memory (insert address seen) := by
              funext other
              by_cases hEq : other = address
              · subst other
                simp [retrieval_cache_of_memory, haddress]
              · simp [retrieval_cache_of_memory, Function.update, hEq, haddress]
            have hrec := ih (insert address seen) (next (memory address))
            dsimp only at hrec ⊢
            rw [retrieval_trace_probe_tree, if_neg haddress]
            simp only [probed_cells_upto, count_retrieval_probes,
              execute_retrieval_probe_tree, Nat.add_le_add_iff_left]
            rcases hrec with ⟨hseen, hcard, hout, hreplay⟩
            constructor
            · simpa [hseen, Finset.union_assoc, Finset.union_left_comm,
                Finset.union_comm]
            constructor
            · simp only [List.length_cons]
              rw [← hcard, Finset.card_insert_of_notMem haddress]
              omega
            constructor
            · have hle : 1 + count_retrieval_probes memory (next (memory address)) ≤ L + 1 ↔
                  count_retrieval_probes memory (next (memory address)) ≤ L := by omega
              simpa only [hle] using hout
            · intro extra
              simpa [retrieval_replay_probe_tree, retrieval_cache_of_memory,
                haddress, hcache] using hreplay extra

@[blueprint "lem:retrieval-trace-probe-list-spec"
  (statement := /-- Let $D$ be a memory, let $A$ be a finite set of already known addresses, let $L$ be a probe budget, and let $\mathcal Q$ be a finite list of retrieval probe trees.  The combined trace of \cref{def:retrieval-trace-probe-list} has final known set $A$ united with the truncated probe sets of all trees in $\mathcal Q$; its length is the increase in cardinality of the known set; its optional outputs record exactly which queries terminate within budget; and replaying its recorded words by \cref{def:retrieval-replay-probe-list} reproduces those outputs and the final cache. -/)
  (proof := /-- Induct on the list $\mathcal Q$.  The empty list is immediate.  For a head tree $Q$ and tail list, apply \cref{lem:retrieval-trace-probe-tree-spec} to $Q$ from the initial known set $A$, and apply the induction hypothesis to the tail from the final known set of the head trace.  The final-set identity follows by associativity of union, and the trace-length identity follows by adding the two cardinality increases.  For replay, first replay the head trace while appending the complete tail trace as unused input; the single-query specification leaves exactly that suffix.  The induction hypothesis then replays the tail and leaves the arbitrary final suffix unchanged. -/)
  (title := /-- Correctness of a first-request query-list trace -/)
  (latexEnv := "lemma")]
lemma retrieval_trace_probe_list_spec :
    ∀ {m w V : ℕ} (memory : Fin m → BitVec w) (seen : Finset (Fin m))
      (L : ℕ) (trees : List (retrieval_probe_tree m w V)),
      let trace := retrieval_trace_probe_list memory seen L trees
      trace.1.1 = seen ∪ probed_cells_list_upto memory L trees ∧
      seen.card + trace.1.2.length = trace.1.1.card ∧
      trace.2 = trees.map (fun tree =>
        if count_retrieval_probes memory tree ≤ L then
          some (execute_retrieval_probe_tree memory tree) else none) ∧
      ∀ extra : List (BitVec w),
        retrieval_replay_probe_list (retrieval_cache_of_memory memory seen)
            (trace.1.2.map Prod.snd ++ extra) L trees =
          ((retrieval_cache_of_memory memory trace.1.1, extra), trace.2) := by
  intro m w V memory seen L trees
  induction trees generalizing seen with
  | nil =>
      simp [retrieval_trace_probe_list, retrieval_replay_probe_list,
        probed_cells_list_upto]
  | cons tree trees ih =>
      have hfirst := retrieval_trace_probe_tree_spec memory seen L tree
      let first := retrieval_trace_probe_tree memory seen L tree
      have hrest := ih first.1.1
      let rest := retrieval_trace_probe_list memory first.1.1 L trees
      change first.1.1 = seen ∪ probed_cells_upto memory L tree ∧
          seen.card + first.1.2.length = first.1.1.card ∧
          first.2 = (if count_retrieval_probes memory tree ≤ L then
            some (execute_retrieval_probe_tree memory tree) else none) ∧
          (∀ extra : List (BitVec w),
            retrieval_replay_probe_tree (retrieval_cache_of_memory memory seen)
                (first.1.2.map Prod.snd ++ extra) L tree =
              ((retrieval_cache_of_memory memory first.1.1, extra), first.2)) at hfirst
      change rest.1.1 = first.1.1 ∪ probed_cells_list_upto memory L trees ∧
          first.1.1.card + rest.1.2.length = rest.1.1.card ∧
          rest.2 = trees.map (fun nextTree =>
            if count_retrieval_probes memory nextTree ≤ L then
              some (execute_retrieval_probe_tree memory nextTree) else none) ∧
          (∀ extra : List (BitVec w),
            retrieval_replay_probe_list (retrieval_cache_of_memory memory first.1.1)
                (rest.1.2.map Prod.snd ++ extra) L trees =
              ((retrieval_cache_of_memory memory rest.1.1, extra), rest.2)) at hrest
      rcases hfirst with ⟨hfirstSeen, hfirstCard, hfirstOut, hfirstReplay⟩
      rcases hrest with ⟨hrestSeen, hrestCard, hrestOut, hrestReplay⟩
      change rest.1.1 = seen ∪ probed_cells_list_upto memory L (tree :: trees) ∧
          seen.card + (first.1.2 ++ rest.1.2).length = rest.1.1.card ∧
          first.2 :: rest.2 = (tree :: trees).map (fun nextTree =>
            if count_retrieval_probes memory nextTree ≤ L then
              some (execute_retrieval_probe_tree memory nextTree) else none) ∧
          ∀ extra : List (BitVec w),
            retrieval_replay_probe_list (retrieval_cache_of_memory memory seen)
                ((first.1.2 ++ rest.1.2).map Prod.snd ++ extra) L (tree :: trees) =
              ((retrieval_cache_of_memory memory rest.1.1, extra), first.2 :: rest.2)
      constructor
      · rw [hrestSeen, hfirstSeen, probed_cells_list_upto]
        simp only [Finset.union_assoc]
      constructor
      · simp only [List.length_append]
        omega
      constructor
      · simp only [List.map_cons]
        rw [hfirstOut, hrestOut]
      · intro extra
        simp only [List.map_append, List.append_assoc,
          retrieval_replay_probe_list]
        rw [hfirstReplay (rest.1.2.map Prod.snd ++ extra)]
        rw [hrestReplay extra]

@[blueprint "def:retrieval-slow-values"
  (statement := /-- Given an ordered key list, an aligned list of optional query outputs, and a value assignment, retain in order exactly the assigned values at positions whose optional output is absent. -/)
  (title := /-- Values at unfinished query positions -/)
  (latexEnv := "definition")]
def retrieval_slow_values {κ α : Type} (value : κ → α) :
    List κ → List (Option α) → List α
  | key :: keys, none :: outputs => value key :: retrieval_slow_values value keys outputs
  | _ :: keys, some _ :: outputs => retrieval_slow_values value keys outputs
  | _, _ => []

@[blueprint "def:retrieval-merge-values"
  (statement := /-- Merge a list of optional values with a fallback stream by retaining every present value and replacing every absent value by the next fallback value; if the fallback stream is exhausted, use a fixed default. -/)
  (title := /-- Merge optional outputs with fallback values -/)
  (latexEnv := "definition")]
def retrieval_merge_values {α : Type} (default : α) :
    List (Option α) → List α → List α
  | [], _ => []
  | some value :: outputs, fallback =>
      value :: retrieval_merge_values default outputs fallback
  | none :: outputs, value :: fallback =>
      value :: retrieval_merge_values default outputs fallback
  | none :: outputs, [] =>
      default :: retrieval_merge_values default outputs []

@[blueprint "lem:list-takeD-eq-append-of-length-le"
  (statement := /-- Let $A$ be a type, let $d\in A$, let $\ell$ be a finite list in $A$, and let $K$ be a natural number.  If $|\ell|\leq K$, then padding $\ell$ to length $K$ with $d$ gives $\ell$ followed by some suffix. -/)
  (proof := /-- Induct on $K$.  For $K=0$, the length hypothesis forces $\ell$ to be empty.  For $K+1$, if $\ell$ is empty the entire padded list is a list of copies of $d$; if $\ell=a::\ell'$, the length hypothesis gives $|\ell'|\leq K$, and the induction hypothesis supplies a suffix after $\ell'$.  Prepending $a$ gives the required decomposition. -/)
  (title := /-- A padded list extends the original list -/)
  (latexEnv := "lemma")]
lemma list_takeD_eq_append_of_length_le :
    ∀ {α : Type} (default : α) (K : ℕ) (items : List α),
      items.length ≤ K → ∃ extra, List.takeD K items default = items ++ extra := by
  intro α default K
  induction K with
  | zero =>
      intro items hlen
      have : items = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
      subst items
      exact ⟨[], rfl⟩
  | succ K ih =>
      intro items hlen
      cases items with
      | nil =>
          exact ⟨List.replicate (K + 1) default, by
            simp [List.takeD, List.replicate_succ]⟩
      | cons item items =>
          obtain ⟨extra, hextra⟩ := ih items (by simpa using hlen)
          exact ⟨extra, by simp [List.takeD, hextra]⟩

@[blueprint "lem:retrieval-first-request-encoding-bound"
  (statement := /-- Let $P$ be a finite family of normalized retrieval instances with $n$ keys in $\operatorname{Fin}(U)$ and values in $\operatorname{Fin}(V)$.  Fix one query tree for each universe key and one memory for each instance.  Suppose each stored value is returned correctly, every combined first-request trace at budget $L$ has at most $K$ words, and every trace has at most $S$ absent outputs.  If an instance is determined by its key set and value function, then
  \[
    |P|\leq \binom Un 2^{wK}V^S.
  \] -/)
  (proof := /-- Encode an instance by three fixed-length objects: its $n$-element key set, its first-request word trace padded to length $K$, and the assigned values at exactly those trace positions with absent outputs, padded to length $S$.  The word and slow-value padding is legitimate by \cref{lem:list-takeD-eq-append-of-length-le}.  By \cref{lem:retrieval-trace-probe-list-spec}, replaying the padded word trace reproduces the optional output list, so equal key-set and word codes give equal optional outputs and hence identify the same slow positions.  Merging the present outputs with the padded slow-value code by \cref{def:retrieval-merge-values} reconstructs the values on the ordered key set; normalization reconstructs the values off that set.  Thus the encoding is injective.  Its three factors have cardinalities $\binom Un$, $(2^w)^K=2^{wK}$, and $V^S$, respectively, which gives the bound. -/)
  (title := /-- Counting first-request encodings -/)
  (latexEnv := "lemma")]
lemma retrieval_first_request_encoding_bound :
    ∀ (U n V w m L K S : ℕ) (c₀ : Fin V)
      (ι : Type) [DecidableEq ι] (P : Finset ι)
      (keySet : ι → Finset (Fin U)) (value : ι → Fin U → Fin V)
      (memory : ι → Fin m → BitVec w) (query : Fin U → retrieval_probe_tree m w V),
      (∀ p ∈ P, (keySet p).card = n) →
      (∀ p ∈ P, ∀ x : Fin U, x ∉ keySet p → value p x = c₀) →
      (∀ p ∈ P, ∀ x ∈ keySet p,
        execute_retrieval_probe_tree (memory p) (query x) = value p x) →
      (∀ p ∈ P,
        let trees := (keySet p).toList.map query
        let trace := retrieval_trace_probe_list (memory p) ∅ L trees
        trace.1.2.length ≤ K) →
      (∀ p ∈ P,
        let trees := (keySet p).toList.map query
        let trace := retrieval_trace_probe_list (memory p) ∅ L trees
        (retrieval_slow_values (value p) (keySet p).toList trace.2).length ≤ S) →
      (∀ p ∈ P, ∀ q ∈ P,
        keySet p = keySet q → value p = value q → p = q) →
      P.card ≤ Nat.choose U n * 2 ^ (w * K) * V ^ S := by
  intro U n V w m L K S c₀ ι instι P keySet value memory query
    hkeyCard hnormalized hcorrect htraceBound hslowBound hseparate
  classical
  let trees : ι → List (retrieval_probe_tree m w V) :=
    fun p => (keySet p).toList.map query
  let trace : ι → (Finset (Fin m) × List (Fin m × BitVec w)) × List (Option (Fin V)) :=
    fun p => retrieval_trace_probe_list (memory p) ∅ L (trees p)
  let traceWords : ι → List (BitVec w) := fun p => (trace p).1.2.map Prod.snd
  let slowValues : ι → List (Fin V) := fun p =>
    retrieval_slow_values (value p) (keySet p).toList (trace p).2
  let keyCode : (p : ι) → p ∈ P →
      {X // X ∈ Finset.powersetCard n (Finset.univ : Finset (Fin U))} :=
    fun p hp => ⟨keySet p, by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hkeyCard p hp⟩⟩
  let wordCode : ι → List.Vector (Fin (2 ^ w)) K := fun p =>
    ⟨List.takeD K ((traceWords p).map BitVec.toFin) 0,
      List.takeD_length K ((traceWords p).map BitVec.toFin) 0⟩
  let slowCode : ι → List.Vector (Fin V) S := fun p =>
    ⟨List.takeD S (slowValues p) c₀, List.takeD_length S (slowValues p) c₀⟩
  let encode : (p : ↥P) →
      {X // X ∈ Finset.powersetCard n (Finset.univ : Finset (Fin U))} ×
        List.Vector (Fin (2 ^ w)) K × List.Vector (Fin V) S :=
    fun p => (keyCode p.1 p.2, wordCode p.1, slowCode p.1)
  have houtputForm : ∀ p ∈ P,
      (trace p).2 = (keySet p).toList.map (fun x =>
        if count_retrieval_probes (memory p) (query x) ≤ L then
          some (value p x) else none) := by
    intro p hp
    have hspec := (retrieval_trace_probe_list_spec
      (memory p) (∅ : Finset (Fin m)) L (trees p)).2.2.1
    rw [hspec]
    simp only [trees, List.map_map]
    apply List.map_congr_left
    intro x hx
    have hxKey : x ∈ keySet p := by simpa using hx
    by_cases hfast : count_retrieval_probes (memory p) (query x) ≤ L
    · simp [hfast, hcorrect p hp x hxKey]
    · simp [hfast]
  have hmergePattern : ∀ (keys : List (Fin U)) (assigned : Fin U → Fin V)
      (fast : Fin U → Prop) [DecidablePred fast] (extra : List (Fin V)),
      retrieval_merge_values c₀
          (keys.map (fun x => if fast x then some (assigned x) else none))
          (retrieval_slow_values assigned keys
              (keys.map (fun x => if fast x then some (assigned x) else none)) ++ extra)
        = keys.map assigned := by
    intro keys
    induction keys with
    | nil => intro assigned fast instFast extra; rfl
    | cons key keys ih =>
        intro assigned fast instFast extra
        by_cases hfast : fast key
        · simp [hfast, retrieval_slow_values, retrieval_merge_values, ih]
        · simp [hfast, retrieval_slow_values, retrieval_merge_values, ih]
  have hinjective : Function.Injective encode := by
    intro p q hencode
    have hkeys : keySet p.1 = keySet q.1 := by
      exact congrArg (fun code => code.1.1) hencode
    have hwords : (wordCode p.1).toList.map BitVec.ofFin =
        (wordCode q.1).toList.map BitVec.ofFin := by
      exact congrArg (fun code => code.2.1.toList.map BitVec.ofFin) hencode
    have hslow : (slowCode p.1).toList = (slowCode q.1).toList := by
      exact congrArg (fun code => code.2.2.toList) hencode
    have htraceP : (traceWords p.1).length ≤ K := by
      simpa [trees, trace, traceWords] using htraceBound p.1 p.2
    have htraceQ : (traceWords q.1).length ≤ K := by
      simpa [trees, trace, traceWords] using htraceBound q.1 q.2
    obtain ⟨wordExtraP, hwordPadP⟩ :=
      list_takeD_eq_append_of_length_le (0 : Fin (2 ^ w)) K
        ((traceWords p.1).map BitVec.toFin) (by simpa using htraceP)
    obtain ⟨wordExtraQ, hwordPadQ⟩ :=
      list_takeD_eq_append_of_length_le (0 : Fin (2 ^ w)) K
        ((traceWords q.1).map BitVec.toFin) (by simpa using htraceQ)
    have hroundtrip : ∀ words : List (BitVec w),
        words.map (BitVec.ofFin ∘ BitVec.toFin) = words := by
      intro words
      induction words with
      | nil => rfl
      | cons word words ih =>
          simp [Function.comp_apply, BitVec.ofFin_toFin, ih]
    have hwordPadP' : (wordCode p.1).toList.map BitVec.ofFin =
        traceWords p.1 ++ wordExtraP.map BitVec.ofFin := by
      change (List.takeD K ((traceWords p.1).map BitVec.toFin) 0).map BitVec.ofFin = _
      rw [hwordPadP, List.map_append, List.map_map]
      rw [hroundtrip]
    have hwordPadQ' : (wordCode q.1).toList.map BitVec.ofFin =
        traceWords q.1 ++ wordExtraQ.map BitVec.ofFin := by
      change (List.takeD K ((traceWords q.1).map BitVec.toFin) 0).map BitVec.ofFin = _
      rw [hwordPadQ, List.map_append, List.map_map]
      rw [hroundtrip]
    have hdecodedP :
        (retrieval_replay_probe_list (fun _ : Fin m => none)
          ((wordCode p.1).toList.map BitVec.ofFin)
          L (trees p.1)).2 = (trace p.1).2 := by
      have hreplay := (retrieval_trace_probe_list_spec
        (memory p.1) (∅ : Finset (Fin m)) L (trees p.1)).2.2.2
          (wordExtraP.map BitVec.ofFin)
      have hout := congrArg Prod.snd hreplay
      have hempty : retrieval_cache_of_memory (memory p.1) ∅ =
          (fun _ : Fin m => none) := by
        funext address
        simp [retrieval_cache_of_memory]
      rw [hempty, ← hwordPadP'] at hout
      simpa [trace] using hout
    have hdecodedQ :
        (retrieval_replay_probe_list (fun _ : Fin m => none)
          ((wordCode q.1).toList.map BitVec.ofFin)
          L (trees q.1)).2 = (trace q.1).2 := by
      have hreplay := (retrieval_trace_probe_list_spec
        (memory q.1) (∅ : Finset (Fin m)) L (trees q.1)).2.2.2
          (wordExtraQ.map BitVec.ofFin)
      have hout := congrArg Prod.snd hreplay
      have hempty : retrieval_cache_of_memory (memory q.1) ∅ =
          (fun _ : Fin m => none) := by
        funext address
        simp [retrieval_cache_of_memory]
      rw [hempty, ← hwordPadQ'] at hout
      simpa [trace] using hout
    have houtputs : (trace p.1).2 = (trace q.1).2 := by
      rw [← hdecodedP, ← hdecodedQ, hwords]
      simp [trees, hkeys]
    have hslowP : (slowValues p.1).length ≤ S := by
      simpa [trees, trace, slowValues] using hslowBound p.1 p.2
    have hslowQ : (slowValues q.1).length ≤ S := by
      simpa [trees, trace, slowValues] using hslowBound q.1 q.2
    obtain ⟨slowExtraP, hslowPadP⟩ :=
      list_takeD_eq_append_of_length_le c₀ S (slowValues p.1) hslowP
    obtain ⟨slowExtraQ, hslowPadQ⟩ :=
      list_takeD_eq_append_of_length_le c₀ S (slowValues q.1) hslowQ
    have hmergedP : retrieval_merge_values c₀ (trace p.1).2 (slowCode p.1).toList =
        (keySet p.1).toList.map (value p.1) := by
      change retrieval_merge_values c₀ (trace p.1).2
        (List.takeD S (slowValues p.1) c₀) = _
      rw [hslowPadP]
      change retrieval_merge_values c₀ (trace p.1).2
        (retrieval_slow_values (value p.1) (keySet p.1).toList (trace p.1).2 ++
          slowExtraP) = _
      rw [houtputForm p.1 p.2]
      exact hmergePattern (keySet p.1).toList (value p.1)
        (fun x => count_retrieval_probes (memory p.1) (query x) ≤ L) slowExtraP
    have hmergedQ : retrieval_merge_values c₀ (trace q.1).2 (slowCode q.1).toList =
        (keySet q.1).toList.map (value q.1) := by
      change retrieval_merge_values c₀ (trace q.1).2
        (List.takeD S (slowValues q.1) c₀) = _
      rw [hslowPadQ]
      change retrieval_merge_values c₀ (trace q.1).2
        (retrieval_slow_values (value q.1) (keySet q.1).toList (trace q.1).2 ++
          slowExtraQ) = _
      rw [houtputForm q.1 q.2]
      exact hmergePattern (keySet q.1).toList (value q.1)
        (fun x => count_retrieval_probes (memory q.1) (query x) ≤ L) slowExtraQ
    have hvaluesList : (keySet p.1).toList.map (value p.1) =
        (keySet p.1).toList.map (value q.1) := by
      rw [← hmergedP, houtputs, hslow, hmergedQ, hkeys]
    have hpoint : ∀ (items : List (Fin U)),
        items.map (value p.1) = items.map (value q.1) →
        ∀ x ∈ items, value p.1 x = value q.1 x := by
      intro items
      induction items with
      | nil => simp
      | cons item items ih =>
          intro heq x hx
          simp only [List.map_cons, List.cons.injEq] at heq
          rcases heq with ⟨hhead, htail⟩
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hhead
          · exact ih htail x hx
    have hvalues : value p.1 = value q.1 := by
      funext x
      by_cases hx : x ∈ keySet p.1
      · exact hpoint (keySet p.1).toList hvaluesList x (by simpa using hx)
      · rw [hnormalized p.1 p.2 x hx, hnormalized q.1 q.2 x]
        simpa [hkeys] using hx
    apply Subtype.ext
    exact hseparate p.1 p.2 q.1 q.2 hkeys hvalues
  have hcard := Fintype.card_le_of_injective encode hinjective
  simpa [encode, Fintype.card_prod, Fintype.card_coe, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, pow_mul, mul_assoc] using hcard

@[blueprint "lem:retrieval-memory-candidate-encoding-bound"
  (statement := /-- Let $P$ be a finite family of normalized retrieval instances, each represented by a memory of $m$ words of $w$ bits.  Suppose that for every memory $D$ there is a finite candidate family $\mathcal X(D)$ of key sets, every instance represented by $D$ has its key set in $\mathcal X(D)$, and $|\mathcal X(D)|\leq B$.  If the represented memory and key set recover the value assignment, then
  \[
    |P|\leq 2^{mw}B
  \]
  as an inequality of real numbers. -/)
  (proof := /-- Group $P$ by the numerical representation of its memory, using the injective identification of a $w$-bit word with $\operatorname{Fin}(2^w)$.  In a fixed memory fiber, mapping an instance to its key set is injective: equality of key sets and memories makes correctness recover equal values on the key set, while normalization gives equality off it.  The fiber therefore has cardinality at most $|\mathcal X(D)|\leq B$.  Summing this bound over all $(2^w)^m=2^{mw}$ numerical memories proves the claim. -/)
  (title := /-- Counting instances by memory and candidate key set -/)
  (latexEnv := "lemma")]
lemma retrieval_memory_candidate_encoding_bound :
    ∀ (U V w m : ℕ) (c₀ : Fin V) (B : ℝ)
      (ι : Type) [DecidableEq ι] (P : Finset ι)
      (keySet : ι → Finset (Fin U)) (value : ι → Fin U → Fin V)
      (memory : ι → Fin m → BitVec w) (query : Fin U → retrieval_probe_tree m w V)
      (candidates : (Fin m → BitVec w) → Finset (Finset (Fin U))),
      (∀ p ∈ P, ∀ x : Fin U, x ∉ keySet p → value p x = c₀) →
      (∀ p ∈ P, ∀ x ∈ keySet p,
        execute_retrieval_probe_tree (memory p) (query x) = value p x) →
      (∀ p ∈ P, keySet p ∈ candidates (memory p)) →
      (∀ D, ((candidates D).card : ℝ) ≤ B) →
      (∀ p ∈ P, ∀ q ∈ P,
        keySet p = keySet q → value p = value q → p = q) →
      (P.card : ℝ) ≤ (2 ^ (m * w) : ℕ) * B := by
  intro U V w m c₀ B ι instι P keySet value memory query candidates
    hnormalized hcorrect heligible hcandidates hseparate
  classical
  let memoryCode : ι → (Fin m → Fin (2 ^ w)) :=
    fun p i => (memory p i).toFin
  let decodedMemory : (Fin m → Fin (2 ^ w)) → Fin m → BitVec w :=
    fun code i => BitVec.ofFin (code i)
  have hdecode : ∀ p, decodedMemory (memoryCode p) = memory p := by
    intro p
    funext i
    exact BitVec.ofFin_toFin (memory p i)
  have hfiber : ∀ code : Fin m → Fin (2 ^ w),
      (((P.filter fun p => memoryCode p = code).card : ℕ) : ℝ) ≤ B := by
    intro code
    let fiber := P.filter fun p => memoryCode p = code
    let keyCode : (p : ↥fiber) → {X // X ∈ candidates (decodedMemory code)} :=
      fun p => ⟨keySet p.1, by
        have hpP : p.1 ∈ P := (Finset.mem_filter.mp p.2).1
        have hpCode : memoryCode p.1 = code := (Finset.mem_filter.mp p.2).2
        have hmem : memory p.1 = decodedMemory code := by
          rw [← hdecode p.1, hpCode]
        simpa [hmem] using heligible p.1 hpP⟩
    have hinj : Function.Injective keyCode := by
      intro p q hkeyCode
      have hpP : p.1 ∈ P := (Finset.mem_filter.mp p.2).1
      have hqP : q.1 ∈ P := (Finset.mem_filter.mp q.2).1
      have hpCode : memoryCode p.1 = code := (Finset.mem_filter.mp p.2).2
      have hqCode : memoryCode q.1 = code := (Finset.mem_filter.mp q.2).2
      have hkeys : keySet p.1 = keySet q.1 := congrArg Subtype.val hkeyCode
      have hmem : memory p.1 = memory q.1 := by
        rw [← hdecode p.1, ← hdecode q.1, hpCode, hqCode]
      have hvalues : value p.1 = value q.1 := by
        funext x
        by_cases hx : x ∈ keySet p.1
        · rw [← hcorrect p.1 hpP x hx, ← hcorrect q.1 hqP x]
          · rw [hmem]
          · simpa [hkeys] using hx
        · rw [hnormalized p.1 hpP x hx, hnormalized q.1 hqP x]
          simpa [hkeys] using hx
      apply Subtype.ext
      exact hseparate p.1 hpP q.1 hqP hkeys hvalues
    have hnat : fiber.card ≤ (candidates (decodedMemory code)).card := by
      simpa [fiber] using Fintype.card_le_of_injective keyCode hinj
    exact le_trans (by exact_mod_cast hnat) (hcandidates (decodedMemory code))
  have hcardEq : P.card = ∑ code : Fin m → Fin (2 ^ w),
      (P.filter fun p => memoryCode p = code).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro p hp
    simp
  calc
    (P.card : ℝ) = ∑ code : Fin m → Fin (2 ^ w),
        (((P.filter fun p => memoryCode p = code).card : ℕ) : ℝ) := by
          rw [hcardEq]
          push_cast
          rfl
    _ ≤ ∑ _code : Fin m → Fin (2 ^ w), B :=
      Finset.sum_le_sum fun code _ => hfiber code
    _ = (2 ^ (m * w) : ℕ) * B := by
      simp [Fintype.card_fun, pow_mul, mul_comm]

@[blueprint "lem:probed-cells-upto-card-le"
  (statement := /-- For every memory, probe tree, and budget $L$, the truncated probe set from \cref{def:probed-cells-upto} has cardinality at most $L$ and at most the full probe count from \cref{def:count-retrieval-probes}. -/)
  (proof := /-- Induct on $L$.  The zero-budget set is empty.  At positive budget a leaf again gives the empty set.  At a probe node, insertion of the current address increases cardinality by at most one, and the induction hypothesis bounds the continuation both by the remaining budget and by its probe count; adding one gives the two asserted bounds. -/)
  (title := /-- Cardinality bounds for truncated probe sets -/)
  (latexEnv := "lemma")]
lemma probed_cells_upto_card_le :
    ∀ {m w V : ℕ} (memory : Fin m → BitVec w) (L : ℕ)
      (tree : retrieval_probe_tree m w V),
      (probed_cells_upto memory L tree).card ≤ L ∧
      (probed_cells_upto memory L tree).card ≤ count_retrieval_probes memory tree := by
  intro m w V memory L
  induction L with
  | zero => intro tree; simp [probed_cells_upto]
  | succ L ih =>
      intro tree
      cases tree with
      | answer output => simp [probed_cells_upto, count_retrieval_probes]
      | probe address next =>
          have hrec := ih (next (memory address))
          have hinsert := Finset.card_insert_le address
            (probed_cells_upto memory L (next (memory address)))
          simp only [probed_cells_upto, count_retrieval_probes]
          constructor <;> omega

@[blueprint "lem:probed-cells-list-upto-map-eq-biUnion"
  (statement := /-- For a list of query keys, the truncated probe set of the corresponding query-tree list from \cref{def:probed-cells-list-upto} is the finite union of the individual truncated probe sets over the set of keys occurring in the list. -/)
  (proof := /-- Induct on the key list.  Both sides are empty for the empty list.  For a head key and a tail list, unfold \cref{def:probed-cells-list-upto}; the induction hypothesis identifies the tail union, and the finite-set union and biunion insertion identities identify the result. -/)
  (title := /-- Query-list probe sets as a finite biunion -/)
  (latexEnv := "lemma")]
lemma probed_cells_list_upto_map_eq_biUnion :
    ∀ {U m w V : ℕ} (memory : Fin m → BitVec w) (L : ℕ)
      (query : Fin U → retrieval_probe_tree m w V) (keys : List (Fin U)),
      probed_cells_list_upto memory L (keys.map query) =
        keys.toFinset.biUnion (fun x => probed_cells_upto memory L (query x)) := by
  intro U m w V memory L query keys
  induction keys with
  | nil => simp [probed_cells_list_upto]
  | cons key keys ih =>
      simp [probed_cells_list_upto, ih, Finset.biUnion_insert]

@[blueprint "lem:retrieval-slow-values-length"
  (statement := /-- If an optional-output list marks a key by an absent value exactly when a decidable predicate fails, then the list from \cref{def:retrieval-slow-values} has length equal to the number of keys where that predicate fails. -/)
  (proof := /-- Induct on the key list and split on the predicate at the head.  A successful head contributes neither a slow value nor a filtered key, while a failed head contributes one to both; the induction hypothesis handles the tail. -/)
  (title := /-- Number of stored slow-query values -/)
  (latexEnv := "lemma")]
lemma retrieval_slow_values_length :
    ∀ {κ α : Type} (value : κ → α) (keys : List κ)
      (fast : κ → Prop) [DecidablePred fast],
      (retrieval_slow_values value keys
        (keys.map (fun x => if fast x then some (value x) else none))).length =
        (keys.filter fun x => ¬ fast x).length := by
  intro κ α value keys
  induction keys with
  | nil => intro fast instFast; rfl
  | cons key keys ih =>
      intro fast instFast
      by_cases hfast : fast key
      · simp [hfast, retrieval_slow_values, ih]
      · simp [hfast, retrieval_slow_values, ih]

@[blueprint "lem:logb-two-exponential-count-bound"
  (statement := /-- Let $V,n,k$ be natural numbers with $0<V$, and let $x\geq0$.  If
  \[
    V^n\leq 4\cdot2^k e^{-x}
  \]
  as real numbers, then
  \[
    \frac{x}{\log 2}\leq k+2-n\log_2V.
  \] -/)
  (proof := /-- Both sides of the assumed inequality are positive.  Apply the monotonicity of the natural logarithm, expand the logarithm of each product and power, and use $\log(e^{-x})=-x$ and $\log4=2\log2$.  Since $\log2>0$, division by $\log2$ preserves the inequality, and the identity $\log_2V=\log V/\log2$ gives the result. -/)
  (title := /-- Logarithmic form of an exponentially discounted count -/)
  (latexEnv := "lemma")]
lemma logb_two_exponential_count_bound :
    ∀ (V n k : ℕ) (x : ℝ), 0 < V → 0 ≤ x →
      ((V ^ n : ℕ) : ℝ) ≤ 4 * ((2 ^ k : ℕ) : ℝ) * Real.exp (-x) →
      x / Real.log 2 ≤ (k : ℝ) + 2 - (n : ℝ) * Real.logb 2 (V : ℝ) := by
  intro V n k x hV hx hcount
  have hVreal : (0 : ℝ) < (V : ℝ) := by exact_mod_cast hV
  have hpowV : (0 : ℝ) < ((V ^ n : ℕ) : ℝ) := by positivity
  have hpowTwo : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  have hright : (0 : ℝ) < 4 * ((2 ^ k : ℕ) : ℝ) * Real.exp (-x) := by positivity
  have hlog := (Real.log_le_log_iff hpowV hright).2 hcount
  have hlogTwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogFour : Real.log 4 = 2 * Real.log 2 := by
    calc
      Real.log 4 = Real.log ((2 : ℝ) * 2) := by norm_num
      _ = Real.log 2 + Real.log 2 := Real.log_mul (by norm_num) (by norm_num)
      _ = 2 * Real.log 2 := by ring
  norm_num [Nat.cast_pow, Real.log_mul, Real.log_pow, Real.log_exp,
    hlogFour] at hlog
  rw [Real.logb]
  apply (div_le_iff₀ hlogTwo).2
  field_simp
  nlinarith

@[blueprint "lem:retrieval-branch-one-numeric-contradiction"
  (statement := /-- Let $n,v,z,R,M,\theta,s,w$ be real numbers with $n>0$, $v\geq1$, and $z\geq1$.  Assume $e^{20000z}\leq n$, $R\leq ne^{-20000z}$, $M<nv+R$, $\theta w\geq\frac14nve^{-160z}$, $sv\leq\frac1{32}nve^{-160z}$, and $(n-s)v\leq M-\theta w+2$.  These inequalities are contradictory. -/)
  (proof := /-- Combining the last four inequalities gives
  \[
    \frac7{32}nve^{-160z}<R+2.
  \]
  The first two assumptions imply $1\leq ne^{-20000z}$ and hence $R+2\leq3ne^{-20000z}$.  Canceling the positive factor $n$ and using $v\geq1$ yields $\frac7{32}e^{19840z}<3$.  On the other hand, $e^{19840z}\geq1+19840z\geq19841$ because $z\geq1$, a numerical contradiction. -/)
  (title := /-- Numerical contradiction in the large-untouched branch -/)
  (latexEnv := "lemma")]
lemma retrieval_branch_one_numeric_contradiction :
    ∀ (n v z R M theta s w : ℝ),
      0 < n → 1 ≤ v → 1 ≤ z → 0 ≤ R →
      Real.exp (20000 * z) ≤ n →
      R ≤ n * Real.exp (-(20000 * z)) →
      M < n * v + R →
      n * v / 4 * Real.exp (-(160 * z)) ≤ theta * w →
      s * v ≤ n * v / 32 * Real.exp (-(160 * z)) →
      (n - s) * v ≤ M - theta * w + 2 → False := by
  intro n v z R M theta s w hn hv hz hRnonneg hnexp hR hM htheta hs hcount
  have hexpCancel : Real.exp (20000 * z) * Real.exp (-(20000 * z)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  have hone : 1 ≤ n * Real.exp (-(20000 * z)) := by
    nlinarith [Real.exp_pos (-(20000 * z))]
  have hmain : (7 / 32 : ℝ) * n * v * Real.exp (-(160 * z)) <
      3 * n * Real.exp (-(20000 * z)) := by
    nlinarith [Real.exp_pos (-(160 * z)), Real.exp_pos (-(20000 * z))]
  have hnnonneg : 0 ≤ n := hn.le
  have hcancelN : (7 / 32 : ℝ) * v * Real.exp (-(160 * z)) <
      3 * Real.exp (-(20000 * z)) := by
    have hdiv := (div_lt_div_iff_of_pos_right hn).2 hmain
    field_simp at hdiv
    nlinarith
  have hexpSplit : Real.exp (-(160 * z)) =
      Real.exp (19840 * z) * Real.exp (-(20000 * z)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexpSplit] at hcancelN
  have hcancelExp : (7 / 32 : ℝ) * v * Real.exp (19840 * z) < 3 := by
    have hpos := Real.exp_pos (-(20000 * z))
    have hdiv := (div_lt_div_iff_of_pos_right hpos).2 hcancelN
    field_simp at hdiv
    nlinarith
  have hsmall : (7 / 32 : ℝ) * Real.exp (19840 * z) < 3 := by
    nlinarith [Real.exp_pos (19840 * z)]
  have hexpLarge := Real.add_one_le_exp (19840 * z)
  norm_num at hsmall ⊢
  nlinarith

@[blueprint "lem:retrieval-branch-two-numeric-contradiction"
  (statement := /-- Let $n,v,z,R,M,x$ be real numbers with $n>0$, $v\geq1$, $z\geq1$, $e^{20000z}\leq n$, $R\leq ne^{-20000z}$, and $M<nv+R$.  If
  \[
    \frac{ne^{-640z}}{52428800z^2}\leq x,
    \qquad
    \frac{x}{\log2}\leq M+2-nv,
  \]
  then the assumptions are contradictory. -/)
  (proof := /-- Since $0<\log2<1$, the two upper bounds and $1\leq ne^{-20000z}$ imply $x<3ne^{-20000z}$.  Comparing this with the lower bound and canceling positive factors gives
  \[
    e^{19360z}<3\cdot52428800\,z^2.
  \]
  Put $y=9680z$.  The standard bound $2y\leq e^y$ gives $(19360z)^2\leq e^{2y}=e^{19360z}$.  Since $z\geq1$ and $19360^2>3\cdot52428800$, this contradicts the preceding display. -/)
  (title := /-- Numerical contradiction in the deviation branch -/)
  (latexEnv := "lemma")]
lemma retrieval_branch_two_numeric_contradiction :
    ∀ (n v z R M x : ℝ),
      0 < n → 1 ≤ v → 1 ≤ z → 0 ≤ R →
      Real.exp (20000 * z) ≤ n →
      R ≤ n * Real.exp (-(20000 * z)) →
      M < n * v + R →
      n * Real.exp (-(640 * z)) / (52428800 * z ^ 2) ≤ x →
      x / Real.log 2 ≤ M + 2 - n * v → False := by
  intro n v z R M x hn hv hz hRnonneg hnexp hR hM hxLower hxUpper
  have hlogPos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogLe : Real.log 2 ≤ 1 := by
    have h := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h.le
  have hexpCancel : Real.exp (20000 * z) * Real.exp (-(20000 * z)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  have hone : 1 ≤ n * Real.exp (-(20000 * z)) := by
    nlinarith [Real.exp_pos (-(20000 * z))]
  have hxSmall : x < 3 * n * Real.exp (-(20000 * z)) := by
    have hxDiv : x / Real.log 2 < R + 2 := by nlinarith
    have hxMul : x < (R + 2) * Real.log 2 := (div_lt_iff₀ hlogPos).mp hxDiv
    have hRtwoNonneg : 0 ≤ R + 2 := by nlinarith
    nlinarith [Real.exp_pos (-(20000 * z))]
  have hzPos : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hexpSmall : Real.exp (19360 * z) < 3 * 52428800 * z ^ 2 := by
    have hnegPos := Real.exp_pos (-(20000 * z))
    have hdenPos : 0 < (52428800 : ℝ) * z ^ 2 := by positivity
    have hcombined : n * Real.exp (-(640 * z)) /
        ((52428800 : ℝ) * z ^ 2) < 3 * n * Real.exp (-(20000 * z)) :=
      lt_of_le_of_lt hxLower hxSmall
    have hcancelN := (div_lt_div_iff_of_pos_right hn).2 hcombined
    field_simp at hcancelN
    have hsplit : Real.exp (-(640 * z)) =
        Real.exp (19360 * z) * Real.exp (-(20000 * z)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsplit] at hcancelN
    field_simp at hcancelN ⊢
    nlinarith
  have htwo := Real.two_mul_le_exp (x := 9680 * z)
  have hsq : (19360 * z) ^ 2 ≤ Real.exp (19360 * z) := by
    have hnonneg : 0 ≤ 19360 * z := by positivity
    have hlinear : 19360 * z ≤ Real.exp (9680 * z) := by nlinarith
    have hsquare := mul_self_le_mul_self hnonneg hlinear
    calc
      (19360 * z) ^ 2 ≤ (Real.exp (9680 * z)) ^ 2 := by simpa [pow_two] using hsquare
      _ = Real.exp (19360 * z) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
  have : (3 : ℝ) * 52428800 * z ^ 2 < (19360 * z) ^ 2 := by
    nlinarith [sq_nonneg z]
  nlinarith

@[blueprint "lem:untouched-cells-below-threshold-count"
  (statement := /-- Let $p:\operatorname{Fin}(U)\to\mathcal P(\operatorname{Fin}(m))$ have total load at most $c$ and individual set sizes at most $L$, where $0<U$, $2n\leq U$, $0<L$, and $8c\leq Um$.  If $\theta\geq0$ and
  \[
    2\theta\leq\frac m2\exp\!\left(-\frac{8nc}{Um}\right),
  \]
  then the number of $n$-subsets $X$ with fewer than $\theta$ untouched cells is at most
  \[
    \binom Un\exp\!\left(-\frac{\theta^2}{2nL^2}\right).
  \] -/)
  (proof := /-- By \cref{lem:average-untouched-cells-lower-bound}, the mean number of untouched cells is at least the displayed exponential lower bound and hence at least $2\theta$.  Therefore every set with fewer than $\theta$ untouched cells lies in the lower-deviation event at distance $\theta$ below the mean.  Apply \cref{lem:untouched-cells-deviation-count} with deviation parameter $\theta$ and use inclusion of the former event in the latter. -/)
  (title := /-- Counting key sets below an untouched-cell threshold -/)
  (latexEnv := "lemma")]
lemma untouched_cells_below_threshold_count :
    ∀ (U n m L c : ℕ) (probeSet : Fin U → Finset (Fin m)) (theta : ℝ),
      0 < U → 2 * n ≤ U → n ≤ U → 0 < L →
      (∑ x : Fin U, (probeSet x).card) ≤ c → 8 * c ≤ U * m →
      (∀ x, (probeSet x).card ≤ L) → 0 ≤ theta →
      2 * theta ≤ (m : ℝ) / 2 *
        Real.exp (-(8 : ℝ) * (n : ℝ) * (c : ℝ) / ((U : ℝ) * (m : ℝ))) →
      (((Finset.powersetCard n (Finset.univ : Finset (Fin U))).filter
        (fun X => ((untouched_cells probeSet X).card : ℝ) < theta)).card : ℝ) ≤
        (Nat.choose U n : ℝ) *
          Real.exp (-(theta ^ 2) / (2 * (n : ℝ) * (L : ℝ) ^ 2)) := by
  intro U n m L c probeSet theta hU h2nU hnU hL hload hcm hcard htheta hthetaExp
  have hchooseNat : 0 < Nat.choose U n := Nat.choose_pos hnU
  have hchoose : (0 : ℝ) < (Nat.choose U n : ℝ) := by exact_mod_cast hchooseNat
  have hmean := average_untouched_cells_lower_bound U n m c probeSet hU h2nU hload hcm
  have hmeanLower : (m : ℝ) / 2 *
      Real.exp (-(8 : ℝ) * (n : ℝ) * (c : ℝ) / ((U : ℝ) * (m : ℝ))) ≤
      (∑ X ∈ Finset.powersetCard n (Finset.univ : Finset (Fin U)),
        ((untouched_cells probeSet X).card : ℝ)) / (Nat.choose U n : ℝ) := by
    apply (le_div_iff₀ hchoose).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmean
  have htwoTheta : 2 * theta ≤
      (∑ X ∈ Finset.powersetCard n (Finset.univ : Finset (Fin U)),
        ((untouched_cells probeSet X).card : ℝ)) / (Nat.choose U n : ℝ) :=
    le_trans hthetaExp hmeanLower
  have hdev := untouched_cells_deviation_count U n m L probeSet theta hnU hL hcard htheta
  have hsubset : ((Finset.powersetCard n (Finset.univ : Finset (Fin U))).filter
      (fun X => ((untouched_cells probeSet X).card : ℝ) < theta)) ⊆
      ((Finset.powersetCard n (Finset.univ : Finset (Fin U))).filter
      (fun X => ((untouched_cells probeSet X).card : ℝ) ≤
        (∑ Y ∈ Finset.powersetCard n (Finset.univ : Finset (Fin U)),
          ((untouched_cells probeSet Y).card : ℝ)) / (Nat.choose U n : ℝ) - theta)) := by
    intro X hX
    have hmemb := Finset.mem_filter.mp hX
    apply Finset.mem_filter.mpr
    exact ⟨hmemb.1, by nlinarith⟩
  exact le_trans (by exact_mod_cast Finset.card_le_card hsubset) hdev

@[blueprint "lem:retrieval-branch-two-scale-lower-bound"
  (statement := /-- Let $n,z,m,t,L$ be positive real numbers.  If $nt\leq zm$ and
  \[
    L^2\leq\bigl(1280t e^{160z}\bigr)^2,
  \]
  then
  \[
    \frac{n e^{-640z}}{52428800z^2}
    \leq
    \frac{\bigl((m/4)e^{-160z}\bigr)^2}{2nL^2}.
  \] -/)
  (proof := /-- Square $nt\leq zm$, which preserves the inequality because both sides are nonnegative.  After clearing the two positive denominators, use the assumed upper bound on $L^2$.  The resulting left-hand side is
  \[
    3276800(nt)^2e^{-320z},
  \]
  because $1280^2\cdot2=3276800$ and $e^{-640z}e^{320z}=e^{-320z}$.  The squared inequality bounds this by $3276800(zm)^2e^{-320z}$, which is exactly the cleared right-hand side since $52428800/16=3276800$ and $(e^{-160z})^2=e^{-320z}$. -/)
  (title := /-- Scale estimate for the low-untouched branch -/)
  (latexEnv := "lemma")]
lemma retrieval_branch_two_scale_lower_bound :
    ∀ n z m t L : ℝ,
      0 < n → 0 < z → 0 < m → 0 < t → 0 < L →
      n * t ≤ z * m →
      L ^ 2 ≤ (1280 * t * Real.exp (160 * z)) ^ 2 →
      n * Real.exp (-(640 * z)) / (52428800 * z ^ 2) ≤
        (m / 4 * Real.exp (-(160 * z))) ^ 2 / (2 * n * L ^ 2) := by
  intro n z m t L hn hz hm ht hL hntzm hLsq
  have hsq : (n * t) ^ 2 ≤ (z * m) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (le_of_lt hn) (le_of_lt ht)) hntzm 2
  have hLstep := mul_le_mul_of_nonneg_left hLsq
    (show 0 ≤ 2 * n ^ 2 * Real.exp (-(640 * z)) by positivity)
  have hsqstep := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ 3276800 * Real.exp (-(320 * z)) by positivity)
  have hexpPosSq : Real.exp (160 * z) ^ 2 = Real.exp (320 * z) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hexpCancel : Real.exp (-(640 * z)) * Real.exp (320 * z) =
      Real.exp (-(320 * z)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexpNegSq : Real.exp (-(160 * z)) ^ 2 = Real.exp (-(320 * z)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  apply (div_le_div_iff₀ (by positivity : 0 < 52428800 * z ^ 2)
    (by positivity : 0 < 2 * n * L ^ 2)).2
  calc
    n * Real.exp (-(640 * z)) * (2 * n * L ^ 2) =
        (2 * n ^ 2 * Real.exp (-(640 * z))) * L ^ 2 := by ring
    _ ≤ (2 * n ^ 2 * Real.exp (-(640 * z))) *
        (1280 * t * Real.exp (160 * z)) ^ 2 := hLstep
    _ = (3276800 * Real.exp (-(320 * z))) * (n * t) ^ 2 := by
      rw [show (1280 * t * Real.exp (160 * z)) ^ 2 =
        1280 ^ 2 * t ^ 2 * Real.exp (160 * z) ^ 2 by ring, hexpPosSq]
      rw [show 2 * n ^ 2 * Real.exp (-(640 * z)) *
        (1280 ^ 2 * t ^ 2 * Real.exp (320 * z)) =
        3276800 * (n * t) ^ 2 *
          (Real.exp (-(640 * z)) * Real.exp (320 * z)) by ring, hexpCancel]
      ring
    _ ≤ (3276800 * Real.exp (-(320 * z))) * (z * m) ^ 2 := hsqstep
    _ = (m / 4 * Real.exp (-(160 * z))) ^ 2 * (52428800 * z ^ 2) := by
      rw [show (m / 4 * Real.exp (-(160 * z))) ^ 2 =
        (m / 4) ^ 2 * Real.exp (-(160 * z)) ^ 2 by ring, hexpNegSq]
      ring

@[blueprint "lem:positive-expected-retrieval-query-cost"
  (statement := /-- Let $U,n,V,w,m,t$ be natural numbers with $0<n\leq U$ and $1<V$.  If a randomized static retrieval scheme with these parameters has expected query cost at most $t$ in the sense of \cref{def:has-expected-query-cost}, then $0<t$. -/)
  (proof := /-- Suppose that $t=0$.  Choose a key set $S\subseteq\operatorname{Fin}(U)$ of cardinality $n$ and a key $x\in S$.  Since $1<V$, there are distinct values $0,1\in\operatorname{Fin}(V)$.  Form two instances with key set $S$, one assigning the constant value $0$ and the other the constant value $1$.  For each instance, \cref{def:has-expected-query-cost} gives an integrable nonnegative probe-count function whose integral, by \cref{def:expected-retrieval-query-cost}, is at most zero; hence each function vanishes almost everywhere.  The fair tape measure is a probability measure by \cref{lem:fair-random-tape-measure-is-probability}, so there is a tape on which both probe counts vanish.  The common query tree for $x$ must then be a leaf for both memories and consequently returns the same answer on both.  This contradicts the correctness clause of \cref{def:randomized-static-retrieval-scheme}, which requires the two answers to be the distinct values $0$ and $1$. -/)
  (title := /-- Positive expected cost for a nontrivial value range -/)
  (latexEnv := "lemma")]
lemma positive_expected_retrieval_query_cost :
    ∀ (U n V w m t : ℕ)
      (scheme : randomized_static_retrieval_scheme U n V w m),
      0 < n → n ≤ U → 1 < V → has_expected_query_cost scheme t → 0 < t := by
  intro U n V w m t scheme hn hnU hV hcost
  by_contra ht
  have ht0 : t = 0 := Nat.eq_zero_of_not_pos ht
  subst t
  classical
  obtain ⟨S, -, hS⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin U))) (n := n)
      (by simpa using hnU)
  have hSne : S.Nonempty := Finset.card_pos.mp (hS.trans_gt hn)
  obtain ⟨x, hx⟩ := hSne
  let z : Fin V := ⟨0, by omega⟩
  let o : Fin V := ⟨1, hV⟩
  let input₀ : static_retrieval_instance U n V := ⟨S, hS, fun _ => z⟩
  let input₁ : static_retrieval_instance U n V := ⟨S, hS, fun _ => o⟩
  let f₀ : random_tape → ℝ := fun tape =>
    (count_retrieval_probes (scheme.encode input₀ tape) (scheme.query x tape) : ℝ)
  let f₁ : random_tape → ℝ := fun tape =>
    (count_retrieval_probes (scheme.encode input₁ tape) (scheme.query x tape) : ℝ)
  have hf₀int : MeasureTheory.Integrable f₀ fair_random_tape_measure :=
    (hcost input₀ x).1
  have hf₁int : MeasureTheory.Integrable f₁ fair_random_tape_measure :=
    (hcost input₁ x).1
  have hf₀le : ∫ tape, f₀ tape ∂fair_random_tape_measure ≤ 0 := by
    simpa [f₀, expected_retrieval_query_cost] using (hcost input₀ x).2
  have hf₁le : ∫ tape, f₁ tape ∂fair_random_tape_measure ≤ 0 := by
    simpa [f₁, expected_retrieval_query_cost] using (hcost input₁ x).2
  have hf₀zero : f₀ =ᵐ[fair_random_tape_measure] 0 := by
    apply (MeasureTheory.integral_eq_zero_iff_of_nonneg
      (fun tape => Nat.cast_nonneg (count_retrieval_probes
        (scheme.encode input₀ tape) (scheme.query x tape))) hf₀int).mp
    exact le_antisymm hf₀le (MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall (fun tape => Nat.cast_nonneg
        (count_retrieval_probes (scheme.encode input₀ tape) (scheme.query x tape)))))
  have hf₁zero : f₁ =ᵐ[fair_random_tape_measure] 0 := by
    apply (MeasureTheory.integral_eq_zero_iff_of_nonneg
      (fun tape => Nat.cast_nonneg (count_retrieval_probes
        (scheme.encode input₁ tape) (scheme.query x tape))) hf₁int).mp
    exact le_antisymm hf₁le (MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall (fun tape => Nat.cast_nonneg
        (count_retrieval_probes (scheme.encode input₁ tape) (scheme.query x tape)))))
  letI : MeasureTheory.IsProbabilityMeasure fair_random_tape_measure :=
    fair_random_tape_measure_is_probability
  obtain ⟨tape, htape₀, htape₁⟩ := (hf₀zero.and hf₁zero).exists
  have hcount₀ : count_retrieval_probes
      (scheme.encode input₀ tape) (scheme.query x tape) = 0 := by
    have htape₀' : ((count_retrieval_probes
        (scheme.encode input₀ tape) (scheme.query x tape) : ℕ) : ℝ) = 0 := by
      simpa [f₀] using htape₀
    exact_mod_cast htape₀'
  have hcount₁ : count_retrieval_probes
      (scheme.encode input₁ tape) (scheme.query x tape) = 0 := by
    have htape₁' : ((count_retrieval_probes
        (scheme.encode input₁ tape) (scheme.query x tape) : ℕ) : ℝ) = 0 := by
      simpa [f₁] using htape₁
    exact_mod_cast htape₁'
  have hsame : execute_retrieval_probe_tree
      (scheme.encode input₀ tape) (scheme.query x tape) =
      execute_retrieval_probe_tree (scheme.encode input₁ tape) (scheme.query x tape) := by
    cases htree : scheme.query x tape with
    | answer output => rfl
    | probe address next =>
        simp [htree, count_retrieval_probes] at hcount₀
  have hcorrect₀ := scheme.correct input₀ x hx tape
  have hcorrect₁ := scheme.correct input₁ x hx tape
  have hzo : z = o := by
    simpa [input₀, input₁] using hcorrect₀.symm.trans (hsame.trans hcorrect₁)
  have := congrArg Fin.val hzo
  simp [z, o] at this

@[blueprint "lem:retrieval-space-not-strictly-below"
  (statement := /-- For every pair of fixed polynomial exponents $a,b$, there exists a positive constant $C=C(a,b)$ such that the following holds for all natural numbers $n,U,V,w,t,m$.  Every randomized static retrieval scheme with answer range $\operatorname{Fin}(V)$ and $m$ cells of $w$ bits, whose parameters satisfy \cref{def:polynomial-retrieval-parameters} and whose probe-count functions are integrable with expectations at most $t$ in the sense of \cref{def:has-expected-query-cost}, has no strict bit-space inequality
  \[
    mw<
    n\log_2 V+
    \left\lfloor n\exp\!\left(-C\frac{wt}{\log_2 V}\right)\right\rfloor .
  \] -/)
  (proof := /-- Take $C\coloneqq20000$, which is positive and independent of every other parameter.  Fix $n,U,V,w,t,m$ and a scheme satisfying \cref{def:polynomial-retrieval-parameters} and \cref{def:has-expected-query-cost} for $t$, write
  \[
    v\coloneqq\log_2V,\qquad z\coloneqq\frac{wt}v,\qquad R\coloneqq\left\lfloor ne^{-20000z}\right\rfloor,
  \]
  and suppose for contradiction that $mw<nv+R$.

  \emph{Step 0: normalizations.}  Since $1<V$ we have $v\geq1>0$, and $\log_2V\leq w$ gives $w\geq1$.  If $R=0$ the assumption reads $mw<nv$, contradicting \cref{lem:retrieval-space-at-least-value-bits}, applicable because $n\leq2n\leq U$ and $0<V$; hence $R\geq1$ and therefore
  \[
    n\geq e^{20000z}.
  \]
  In particular $n\geq1$ and $U\geq2n\geq2$.  Moreover $t\geq1$ by \cref{lem:positive-expected-retrieval-query-cost}: a zero expected-cost bound would force two instances with distinct stored values to return the same answer on a common zero-probe tape.  Thus $z=wt/v\geq w/v\geq1$ because $v\leq w$.  Finally $mw\geq nv$ by \cref{lem:retrieval-space-at-least-value-bits}, so
  \[
    m\geq\frac{nv}w\geq\frac{e^{20000z}}w\geq160t,
  \]
  the last step following from $e^{20000z}\geq1+20000z$, $z\geq1$, and $wt=zv\leq zw$.

  \emph{Step 1: a good tape and a large good family.}  Put
  \[
    L\coloneqq\left\lceil640\,t\,e^{160z}\right\rceil,\qquad
    \theta\coloneqq\frac m4e^{-160z},\qquad
    \lambda\coloneqq\frac m4e^{-160z}.
  \]
  Apply \cref{lem:exists-good-random-tape} with $c_0\coloneqq0\in\operatorname{Fin}(V)$, legitimate since $0<n$, $n\leq U$ and $0<t$, to obtain a tape $\tau$ and a family $\mathcal G$ of normalized instances $I=(X,g)$, where $|X|=n$ and $g$ vanishes off $X$, such that $4\binom UnV^{n}\leq5|\mathcal G|$ and every $I\in\mathcal G$ satisfies, for $D_I\coloneqq\operatorname{encode}(I,\tau)$,
  \[
    \sum_{x\in\operatorname{Fin}(U)}\operatorname{probes}(D_I,x)\leq20Ut,
    \qquad
    \sum_{x\in X}\operatorname{probes}(D_I,x)\leq20nt,
  \]
  where $\operatorname{probes}(D,x)$ abbreviates the count of \cref{def:count-retrieval-probes} for $\operatorname{query}(x,\tau)$ against $D$.  For $I\in\mathcal G$ set $p_I(x)\coloneqq\operatorname{probed}_{\leq L}(D_I,\operatorname{query}(x,\tau))$, the truncated probe set of \cref{def:probed-cells-upto}, and $\Phi_I(X')\coloneqq|\operatorname{untouched}(p_I,X')|$ as in \cref{def:untouched-cells}.  The two bounds in \cref{lem:probed-cells-upto-card-le} give $|p_I(x)|\leq L$ for all $x$ and $\sum_x|p_I(x)|\leq20Ut$.  Call $x$ \emph{slow} for $I$ if $\operatorname{probes}(D_I,x)>L$; since the probe counts of the keys of $X$ sum to at most $20nt$, the number $s_I$ of slow keys in $X$ satisfies $s_I\leq20nt/L\eqqcolon S_0$, and we set $S\coloneqq\lfloor S_0\rfloor$.

  \emph{Step 2: the untouched-cell scale.}  For a fixed memory satisfying the total-load bound, write $\mu$ for the mean of $\Phi(X')$ over all $n$-subsets.  The lower-bound argument packaged in \cref{lem:untouched-cells-below-threshold-count}, with $c\coloneqq20Ut$, applies because $0<U$, $2n\leq U$, $\sum_x|p(x)|\leq20Ut$, and $8\cdot20Ut\leq Um$ by $m\geq160t$.  Its mean estimate is
  \[
    \mu_I\geq\frac m2\exp\!\left(-\frac{8n\cdot20Ut}{Um}\right)=\frac m2e^{-160nt/m}\geq\frac m2e^{-160z},
  \]
  the last inequality because $m\geq nv/w$ gives $nt/m\leq wt/v=z$.  Hence $\theta=\mu_I-\left(\mu_I-\tfrac m4e^{-160z}\right)\leq\mu_I-\lambda$.

  \emph{Step 3: the two encodings.}  Split $\mathcal G=\mathcal G_1\sqcup\mathcal G_2$, where $\mathcal G_1\coloneqq\{I\in\mathcal G:\Phi_I(X)\geq\theta\}$ and $\mathcal G_2$ is its complement in $\mathcal G$.  Since $4\binom UnV^{n}\leq5|\mathcal G|=5(|\mathcal G_1|+|\mathcal G_2|)$, one of the two satisfies
  \[
    \frac25\binom UnV^{n}\leq|\mathcal G_j| .
  \]

  \emph{Branch 1.}  Suppose this holds for $j=1$, and put $K\coloneqq m-\lceil\theta\rceil$.  Map $I=(X,g)\in\mathcal G_1$ to the triple consisting of $X$, the sequence of the contents under $D_I$ of the cells of $T_I\coloneqq\bigcup_{x\in X}p_I(x)$ listed in \emph{first-request order} and padded with zero words to length exactly $K$, and the sequence of the values $g(x)$ at the slow keys of $X$ in increasing order, padded with $0$ to length exactly $S$.  Here first-request order is the order in which the following deterministic procedure, run by the receiver, first asks for a cell: process the keys of $X$ in increasing order and, for each, simulate $\operatorname{query}(x,\tau)$ for at most $L$ probes using \cref{def:execute-retrieval-probe-tree}, requesting the next unseen word whenever the simulation probes a cell whose content is not yet known.  This is well defined and the padding is legitimate: by \cref{def:untouched-cells}, $|T_I|=m-\Phi_I(X)\leq m-\theta\leq K$, and $s_I\leq S_0$ with $s_I$ an integer gives $s_I\leq S$.

  The map is injective.  By \cref{lem:probed-cells-list-upto-map-eq-biUnion}, the cells requested by the ordered query list are exactly $T_I$.  The receiver knows $\tau$, $X$, $L$ and the word block, so \cref{lem:retrieval-trace-probe-list-spec} lets him replay the procedure and recover the optional outputs.  The absent outputs are precisely the slow keys, and \cref{lem:retrieval-slow-values-length} bounds their padded value list by $S$.  Correctness recovers $g$ on every fast key, the value block recovers it on every slow key, and normalization recovers it off $X$.  Thus the hypotheses of \cref{lem:retrieval-first-request-encoding-bound} hold and give $|\mathcal G_1|\leq\binom Un\cdot2^{wK}\cdot V^{S}$.  Cancelling $\binom Un$ and applying \cref{lem:logb-two-mul-le-of-pow-le-two-pow} gives
  \[
    \frac25\binom UnV^{n}\leq\binom Un2^{wK}V^{S}
    \quad\Longrightarrow\quad
    nv-Sv-\log_2\tfrac52\leq wK\leq mw-\theta w .
  \]
  Now $\theta w=\frac{mw}4e^{-160z}\geq\frac{nv}4e^{-160z}$, while $L\geq640te^{160z}$ gives $Sv\leq\frac{20ntv}L\leq\frac{nv}{32}e^{-160z}$, and $mw<nv+R$.  Substituting,
  \[
    \frac{nv}4e^{-160z}\leq mw-nv+Sv+\log_2\tfrac52
    <R+\frac{nv}{32}e^{-160z}+2,
  \]
  hence $\frac7{32}nve^{-160z}\leq R+2\leq ne^{-20000z}+2$.  The elementary estimates are exactly the hypotheses of \cref{lem:retrieval-branch-one-numeric-contradiction}, which uses $n\geq e^{20000z}$ and $z\geq1$ to derive the impossible inequality $e^{19840z}<14$.

  \emph{Branch 2.}  Suppose instead the count holds for $j=2$.  Map $I=(X,g)\in\mathcal G_2$ to the pair consisting of the memory $D_I$ and the index of $X$ in the canonically ordered family $\mathcal X(D)\coloneqq\{X':|X'|=n,\ \Phi_D(X')<\theta\}$.  By \cref{lem:untouched-cells-below-threshold-count}, every memory satisfying the total-load bound has $|\mathcal X(D)|\leq\binom Un\exp\!\left(-\lambda^{2}/(2nL^{2})\right)$.  The memory and key set recover $g$ by correctness on $X$ and normalization off $X$, so \cref{lem:retrieval-memory-candidate-encoding-bound} gives
  \[
    \frac25\binom UnV^{n}\leq2^{mw}\binom Un\exp\!\left(-\frac{\lambda^{2}}{2nL^{2}}\right),
    \quad\text{so}\quad
    \frac{\lambda^{2}}{2nL^{2}}\log_2e\leq mw-nv+\log_2\tfrac52<R+2 .
  \]
  Applying \cref{lem:logb-two-exponential-count-bound} to this estimate yields the displayed logarithmic inequality.  Since $z\geq1$ and $t\geq1$ we have $640te^{160z}\geq1$, so $L\leq1280te^{160z}$; with $\lambda=\frac m4e^{-160z}$ and $m\geq nv/w$, \cref{lem:retrieval-branch-two-scale-lower-bound} gives
  \[
    \frac{\lambda^{2}}{2nL^{2}}
      \geq\frac{n^{2}v^{2}e^{-320z}/(16w^{2})}{2n\cdot1638400\,t^{2}e^{320z}}
      =\frac{n\,e^{-640z}}{52428800\,z^{2}},
  \]
  using $v^{2}/(w^{2}t^{2})=z^{-2}$.  Combining with $R+2\leq ne^{-20000z}+2\leq3ne^{-20000z}$, valid because $n\geq e^{20000z}$, and $\log_2e\geq1$,
  \[
    e^{19360z}\leq 3\cdot52428800\,z^{2}.
  \]
  This contradicts \cref{lem:retrieval-branch-two-numeric-contradiction}, which compares $e^{19360z}$ with $(19360z)^2$ for $z\geq1$.

  Both branches are impossible, so the assumed strict inequality $mw<nv+R$ cannot hold. -/)
  (title := /-- Isolated communication lower-bound step -/)
  (latexEnv := "lemma")]
lemma retrieval_space_not_strictly_below :
    ∀ (a b : ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (n U V w t m : ℕ)
        (scheme : randomized_static_retrieval_scheme U n V w m),
        polynomial_retrieval_parameters n U V w a b →
        has_expected_query_cost scheme t →
        ¬(m : ℝ) * (w : ℝ) < retrieval_space_threshold C n V w t := by
  intro a b
  refine ⟨20000, by norm_num, ?_⟩
  intro n U V w t m scheme hparameters hcost hbelow
  rcases hparameters with ⟨h2nU, hUna, hVnb, hV, hvw⟩
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    cases b <;> simp at hVnb <;> omega
  have hnU : n ≤ U := by omega
  have hU : 0 < U := lt_of_lt_of_le hn hnU
  have hVpos : 0 < V := by omega
  let v : ℝ := Real.logb 2 (V : ℝ)
  have hv : 1 ≤ v := by
    dsimp [v]
    rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast (show 2 ≤ V by omega))
  have hvpos : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hw : 0 < w := by
    have : (1 : ℝ) ≤ (w : ℝ) := le_trans hv hvw
    exact_mod_cast this
  have ht : 0 < t :=
    positive_expected_retrieval_query_cost U n V w m t scheme hn hnU hV hcost
  let z : ℝ := ((w : ℝ) * (t : ℝ)) / v
  have hzv : z * v = (w : ℝ) * (t : ℝ) := by
    dsimp [z]
    field_simp
  have hz : 1 ≤ z := by
    apply (le_div_iff₀ hvpos).2
    have htOne : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    nlinarith [show (0 : ℝ) ≤ (w : ℝ) by positivity]
  have hbase : (n : ℝ) * v ≤ (m : ℝ) * (w : ℝ) := by
    simpa [v] using retrieval_space_at_least_value_bits U n V w m scheme hnU hVpos
  let R : ℕ := Nat.floor ((n : ℝ) * Real.exp (-(20000 * z)))
  have hbelow' : (m : ℝ) * (w : ℝ) < (n : ℝ) * v + (R : ℝ) := by
    simpa [retrieval_space_threshold, v, z, R] using hbelow
  have hR : 0 < R := by
    by_contra hR
    have hR0 : R = 0 := Nat.eq_zero_of_not_pos hR
    rw [hR0, Nat.cast_zero, add_zero] at hbelow'
    exact (not_lt_of_ge hbase) hbelow'
  have hRnonneg : (0 : ℝ) ≤ (R : ℝ) := by positivity
  have hRupper : (R : ℝ) ≤ (n : ℝ) * Real.exp (-(20000 * z)) := by
    exact Nat.floor_le (by positivity)
  have hnExp : Real.exp (20000 * z) ≤ (n : ℝ) := by
    have hRone : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    have hone : 1 ≤ (n : ℝ) * Real.exp (-(20000 * z)) := le_trans hRone hRupper
    have hcancel : Real.exp (20000 * z) * Real.exp (-(20000 * z)) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      simp
    nlinarith [Real.exp_pos (20000 * z), Real.exp_pos (-(20000 * z))]
  have hm160 : (160 : ℝ) * (t : ℝ) ≤ (m : ℝ) := by
    have hexp := Real.add_one_le_exp (20000 * z)
    have hn160z : (160 : ℝ) * z ≤ (n : ℝ) := by nlinarith
    have hnv : (160 : ℝ) * ((w : ℝ) * (t : ℝ)) ≤ (n : ℝ) * v := by
      nlinarith [hzv]
    have hwreal : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
    nlinarith
  have hm : 0 < m := by
    have htReal : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
    have : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by positivity) hm160
    exact_mod_cast this
  let L : ℕ := Nat.ceil ((640 : ℝ) * (t : ℝ) * Real.exp (160 * z))
  have hLarg : 1 ≤ (640 : ℝ) * (t : ℝ) * Real.exp (160 * z) := by
    have htOne : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    have hexpOne : 1 ≤ Real.exp (160 * z) := (Real.one_le_exp_iff).2 (by positivity)
    nlinarith
  have hLpos : 0 < L := by
    have hceil : (1 : ℝ) ≤ (L : ℝ) :=
      le_trans hLarg (Nat.le_ceil ((640 : ℝ) * (t : ℝ) * Real.exp (160 * z)))
    exact_mod_cast hceil
  have hLlower : (640 : ℝ) * (t : ℝ) * Real.exp (160 * z) ≤ (L : ℝ) :=
    Nat.le_ceil _
  have hLupper : (L : ℝ) ≤ (1280 : ℝ) * (t : ℝ) * Real.exp (160 * z) := by
    have hceil := Nat.ceil_lt_add_one
      (a := (640 : ℝ) * (t : ℝ) * Real.exp (160 * z)) (by positivity)
    nlinarith
  let theta : ℝ := (m : ℝ) / 4 * Real.exp (-(160 * z))
  let lam : ℝ := theta
  have hthetaNonneg : 0 ≤ theta := by positivity
  have hthetaLeM : theta ≤ (m : ℝ) := by
    have hexpLe : Real.exp (-(160 * z)) ≤ 1 := (Real.exp_le_one_iff).2 (by nlinarith)
    have hmReal : (0 : ℝ) ≤ (m : ℝ) := by positivity
    dsimp [theta]
    nlinarith [Real.exp_pos (-(160 * z))]
  have hceilTheta : Nat.ceil theta ≤ m := Nat.ceil_le.mpr hthetaLeM
  let K : ℕ := m - Nat.ceil theta
  let S : ℕ := Nat.floor (((20 : ℝ) * (n : ℝ) * (t : ℝ)) / (L : ℝ))
  have hSupper : (S : ℝ) ≤ ((20 : ℝ) * (n : ℝ) * (t : ℝ)) / (L : ℝ) := by
    exact Nat.floor_le (by positivity)
  have hSleN : S ≤ n := by
    have hLreal : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
    have hratio : ((20 : ℝ) * (n : ℝ) * (t : ℝ)) / (L : ℝ) ≤ (n : ℝ) := by
      apply (div_le_iff₀ hLreal).2
      have htReal : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
      have hexpOne : 1 ≤ Real.exp (160 * z) := (Real.one_le_exp_iff).2 (by positivity)
      have hscale := mul_le_mul_of_nonneg_left hexpOne
        (show (0 : ℝ) ≤ 640 * (t : ℝ) by positivity)
      have hL20 : (20 : ℝ) * (t : ℝ) ≤ (L : ℝ) := by nlinarith [hLlower]
      have hmulN := mul_le_mul_of_nonneg_left hL20
        (show (0 : ℝ) ≤ (n : ℝ) by positivity)
      nlinarith
    exact_mod_cast le_trans hSupper hratio
  have hSv : (S : ℝ) * v ≤
      (n : ℝ) * v / 32 * Real.exp (-(160 * z)) := by
    have hLreal : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
    have htReal : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
    have hexpPos := Real.exp_pos (160 * z)
    have hexpCancel : Real.exp (160 * z) * Real.exp (-(160 * z)) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      simp
    have hSratio := hSupper
    apply le_trans (mul_le_mul_of_nonneg_right hSratio hvpos.le)
    rw [show ((20 : ℝ) * (n : ℝ) * (t : ℝ)) / (L : ℝ) * v =
      ((20 : ℝ) * (n : ℝ) * (t : ℝ) * v) / (L : ℝ) by ring]
    apply (div_le_iff₀ hLreal).2
    have hmul := mul_le_mul_of_nonneg_left hLlower
      (show (0 : ℝ) ≤ (n : ℝ) * v / 32 * Real.exp (-(160 * z)) by positivity)
    calc
      (20 : ℝ) * (n : ℝ) * (t : ℝ) * v =
          ((n : ℝ) * v / 32 * Real.exp (-(160 * z))) *
            ((640 : ℝ) * (t : ℝ) * Real.exp (160 * z)) := by
              field_simp
              nlinarith
      _ ≤ ((n : ℝ) * v / 32 * Real.exp (-(160 * z))) * (L : ℝ) := hmul
  obtain ⟨X₀, -, hX₀⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin U))) (n := n)
      (by simpa using hnU)
  let inst : Finset (Fin U) × (Fin U → Fin V) → static_retrieval_instance U n V :=
    fun p => if h : p.1.card = n then ⟨p.1, h, p.2⟩ else ⟨X₀, hX₀, p.2⟩
  obtain ⟨tape, good, hgoodCard, hgoodNorm, hgoodSize, hgoodCost⟩ :=
    exists_good_random_tape U n V w m t scheme ⟨0, hVpos⟩ hn hnU ht hcost
  let memory : Finset (Fin U) × (Fin U → Fin V) → Fin m → BitVec w :=
    fun p => scheme.encode (inst p) tape
  let query : Fin U → retrieval_probe_tree m w V := fun x => scheme.query x tape
  let probeSet : (Finset (Fin U) × (Fin U → Fin V)) → Fin U → Finset (Fin m) :=
    fun p x => probed_cells_upto (memory p) L (query x)
  have hinstGood : ∀ (p : Finset (Fin U) × (Fin U → Fin V)) (hp : p ∈ good),
      inst p = ⟨p.1, hgoodCard p hp, p.2⟩ := by
    intro p hp
    simp [inst, hgoodCard p hp]
  have hload : ∀ p ∈ good, (∑ x : Fin U, (probeSet p x).card) ≤ 20 * U * t := by
    intro p hp
    calc
      (∑ x : Fin U, (probeSet p x).card) ≤
          ∑ x : Fin U, count_retrieval_probes (memory p) (query x) :=
        Finset.sum_le_sum fun x _ => (probed_cells_upto_card_le (memory p) L (query x)).2
      _ ≤ 20 * U * t := by
        have h := (hgoodCost p hp (hgoodCard p hp)).1
        simpa [memory, query, hinstGood p hp] using h
  have hstoredCost : ∀ p ∈ good,
      (∑ x ∈ p.1, count_retrieval_probes (memory p) (query x)) ≤ 20 * n * t := by
    intro p hp
    have h := (hgoodCost p hp (hgoodCard p hp)).2
    simpa [memory, query, hinstGood p hp] using h
  have hslowCard : ∀ p ∈ good,
      ((p.1.filter fun x => L < count_retrieval_probes (memory p) (query x)).card) ≤ S := by
    intro p hp
    let slow := p.1.filter fun x => L < count_retrieval_probes (memory p) (query x)
    have hsumLower : slow.card * L ≤
        ∑ x ∈ p.1, count_retrieval_probes (memory p) (query x) := by
      have hlocal : slow.card * L ≤ ∑ x ∈ slow,
          count_retrieval_probes (memory p) (query x) := by
        simpa [mul_comm] using Finset.card_nsmul_le_sum slow
          (fun x => count_retrieval_probes (memory p) (query x)) L
          (fun x hx => by
            have := (Finset.mem_filter.mp hx).2
            omega)
      exact le_trans hlocal (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
    have hprod : slow.card * L ≤ 20 * n * t := le_trans hsumLower (hstoredCost p hp)
    have hLreal : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
    have hreal : (slow.card : ℝ) ≤ ((20 : ℝ) * (n : ℝ) * (t : ℝ)) / (L : ℝ) := by
      apply (le_div_iff₀ hLreal).2
      exact_mod_cast hprod
    have hfloor : slow.card ≤ Nat.floor (((20 : ℝ) * (n : ℝ) * (t : ℝ)) / (L : ℝ)) :=
      (Nat.le_floor_iff (by positivity)).2 hreal
    simpa [slow, S] using hfloor
  let high : Finset (Finset (Fin U) × (Fin U → Fin V)) :=
    good.filter fun p => theta ≤ ((untouched_cells (probeSet p) p.1).card : ℝ)
  let low : Finset (Finset (Fin U) × (Fin U → Fin V)) :=
    good.filter fun p => ¬ theta ≤ ((untouched_cells (probeSet p) p.1).card : ℝ)
  have hsplit : high.card + low.card = good.card := by
    dsimp [high, low]
    exact Finset.filter_card_add_filter_neg_card_eq_card _
  by_cases hlarge : 2 * (Nat.choose U n * V ^ n) ≤ 5 * high.card
  · have htraceHigh : ∀ p ∈ high,
        let trees := p.1.toList.map query
        let trace := retrieval_trace_probe_list (memory p) ∅ L trees
        trace.1.2.length ≤ K := by
      intro p hp
      have hpGood := (Finset.mem_filter.mp hp).1
      have hpTheta := (Finset.mem_filter.mp hp).2
      let trees := p.1.toList.map query
      let trace := retrieval_trace_probe_list (memory p) ∅ L trees
      have hspec := retrieval_trace_probe_list_spec (memory p) (∅ : Finset (Fin m)) L trees
      have hfinal := hspec.1
      have hlength := hspec.2.1
      have hunion : probed_cells_list_upto (memory p) L trees = p.1.biUnion (probeSet p) := by
        simpa [trees, probeSet] using
          probed_cells_list_upto_map_eq_biUnion (memory p) L query p.1.toList
      have htraceLen : trace.1.2.length = (p.1.biUnion (probeSet p)).card := by
        rw [show trace = retrieval_trace_probe_list (memory p) ∅ L trees by rfl]
        simp only [Finset.card_empty, zero_add] at hlength
        rw [hfinal, Finset.empty_union, hunion] at hlength
        exact hlength
      have hpartition : (untouched_cells (probeSet p) p.1).card +
          (p.1.biUnion (probeSet p)).card = m := by
        simpa [untouched_cells] using Finset.card_sdiff_add_card_eq_card
          (Finset.subset_univ (p.1.biUnion (probeSet p)))
      have hceil : Nat.ceil theta ≤ (untouched_cells (probeSet p) p.1).card :=
        Nat.ceil_le.mpr hpTheta
      dsimp only
      rw [htraceLen]
      dsimp [K]
      omega
    have hslowHigh : ∀ p ∈ high,
        let trees := p.1.toList.map query
        let trace := retrieval_trace_probe_list (memory p) ∅ L trees
        (retrieval_slow_values p.2 p.1.toList trace.2).length ≤ S := by
      intro p hp
      have hpGood := (Finset.mem_filter.mp hp).1
      let trees := p.1.toList.map query
      let trace := retrieval_trace_probe_list (memory p) ∅ L trees
      have houtputs := (retrieval_trace_probe_list_spec
        (memory p) (∅ : Finset (Fin m)) L trees).2.2.1
      have hcorrectP : ∀ x ∈ p.1,
          execute_retrieval_probe_tree (memory p) (query x) = p.2 x := by
        intro x hx
        have hc := scheme.correct (inst p) x (by simpa [inst, hgoodCard p hpGood] using hx) tape
        simpa [memory, query, inst, hgoodCard p hpGood] using hc
      have hform : trace.2 = p.1.toList.map (fun x =>
          if count_retrieval_probes (memory p) (query x) ≤ L then some (p.2 x) else none) := by
        rw [show trace = retrieval_trace_probe_list (memory p) ∅ L trees by rfl, houtputs]
        simp only [trees, List.map_map]
        apply List.map_congr_left
        intro x hx
        have hxP : x ∈ p.1 := by simpa using hx
        by_cases hfast : count_retrieval_probes (memory p) (query x) ≤ L
        · simp [hfast, hcorrectP x hxP]
        · simp [hfast]
      dsimp only
      rw [hform, retrieval_slow_values_length]
      have hlist : (p.1.toList.filter fun x =>
          ¬ count_retrieval_probes (memory p) (query x) ≤ L).length =
          (p.1.filter fun x => L < count_retrieval_probes (memory p) (query x)).card := by
        let items := p.1.toList.filter fun x =>
          ¬ count_retrieval_probes (memory p) (query x) ≤ L
        calc
          items.length = items.toFinset.card :=
            (List.toFinset_card_of_nodup (p.1.nodup_toList.filter _)).symm
          _ = (p.1.filter fun x => L < count_retrieval_probes (memory p) (query x)).card := by
            congr 1
            ext x
            simp [items, Nat.not_le]
      rw [hlist]
      exact hslowCard p hpGood
    have hcountHigh := retrieval_first_request_encoding_bound U n V w m L K S
      ⟨0, hVpos⟩ _ high (fun p => p.1) (fun p => p.2) memory query
      (fun p hp => hgoodCard p (Finset.mem_filter.mp hp).1)
      (fun p hp => hgoodNorm p (Finset.mem_filter.mp hp).1)
      (fun p hp x hx => by
        have hpGood := (Finset.mem_filter.mp hp).1
        have hc := scheme.correct (inst p) x (by simpa [inst, hgoodCard p hpGood] using hx) tape
        simpa [memory, query, inst, hgoodCard p hpGood] using hc)
      htraceHigh hslowHigh
      (fun p hp q hq hkeys hvalues => by cases p; cases q; simp_all)
    have hchoosePos : 0 < Nat.choose U n := Nat.choose_pos hnU
    have hrough : V ^ n ≤ 4 * (2 ^ (w * K) * V ^ S) := by
      have hcombined : 2 * (Nat.choose U n * V ^ n) ≤
          5 * (Nat.choose U n * 2 ^ (w * K) * V ^ S) :=
        le_trans hlarge (Nat.mul_le_mul_left 5 hcountHigh)
      have hcancel : 2 * V ^ n ≤ 5 * (2 ^ (w * K) * V ^ S) := by
        have hc : Nat.choose U n * (2 * V ^ n) ≤
            Nat.choose U n * (5 * (2 ^ (w * K) * V ^ S)) := by
          calc
            Nat.choose U n * (2 * V ^ n) = 2 * (Nat.choose U n * V ^ n) := by ring
            _ ≤ 5 * (Nat.choose U n * 2 ^ (w * K) * V ^ S) := hcombined
            _ = Nat.choose U n * (5 * (2 ^ (w * K) * V ^ S)) := by ring
        exact Nat.le_of_mul_le_mul_left hc hchoosePos
      omega
    have hpow : V ^ (n - S) ≤ 2 ^ (w * K + 2) := by
      have hfactor : V ^ (n - S) * V ^ S = V ^ n := by
        rw [← pow_add, Nat.sub_add_cancel hSleN]
      have hVsPos : 0 < V ^ S := pow_pos hVpos S
      rw [← hfactor] at hrough
      have hcancel := Nat.le_of_mul_le_mul_right (by
        calc
          V ^ (n - S) * V ^ S ≤ 4 * (2 ^ (w * K) * V ^ S) := hrough
          _ = (4 * 2 ^ (w * K)) * V ^ S := by ring) hVsPos
      simpa [pow_add, mul_comm] using hcancel
    have hlog := logb_two_mul_le_of_pow_le_two_pow V (n - S) (w * K + 2) hVpos hpow
    have hKreal : (K : ℝ) ≤ (m : ℝ) - theta := by
      have hceilLower : theta ≤ (Nat.ceil theta : ℝ) := Nat.le_ceil theta
      have hcastSub : (K : ℝ) = (m : ℝ) - (Nat.ceil theta : ℝ) := by
        dsimp [K]
        rw [Nat.cast_sub hceilTheta]
      rw [hcastSub]
      linarith
    have hcountNumeric : ((n : ℝ) - (S : ℝ)) * v ≤
        (m : ℝ) * (w : ℝ) - theta * (w : ℝ) + 2 := by
      rw [Nat.cast_sub hSleN] at hlog
      have hwReal : (0 : ℝ) ≤ (w : ℝ) := by positivity
      have := mul_le_mul_of_nonneg_left hKreal hwReal
      norm_num [Nat.cast_add, Nat.cast_mul] at hlog
      nlinarith
    have hthetaLower : (n : ℝ) * v / 4 * Real.exp (-(160 * z)) ≤
        theta * (w : ℝ) := by
      dsimp [theta]
      have hexpPos := Real.exp_pos (-(160 * z))
      nlinarith
    exact retrieval_branch_one_numeric_contradiction (n : ℝ) v z (R : ℝ)
      ((m : ℝ) * (w : ℝ)) theta (S : ℝ) (w : ℝ)
      (by exact_mod_cast hn) hv hz hRnonneg hnExp hRupper hbelow'
      hthetaLower hSv hcountNumeric
  · have hsmall : 2 * (Nat.choose U n * V ^ n) ≤ 5 * low.card := by
      omega
    let candidates : (Fin m → BitVec w) → Finset (Finset (Fin U)) := fun D =>
      if (∑ x : Fin U, (probed_cells_upto D L (query x)).card) ≤ 20 * U * t then
        (Finset.powersetCard n (Finset.univ : Finset (Fin U))).filter
          (fun X => ((untouched_cells (fun x => probed_cells_upto D L (query x)) X).card : ℝ) < theta)
      else ∅
    have hcandidates : ∀ D, ((candidates D).card : ℝ) ≤
        (Nat.choose U n : ℝ) * Real.exp (-(lam ^ 2) /
          (2 * (n : ℝ) * (L : ℝ) ^ 2)) := by
      intro D
      by_cases hD : (∑ x : Fin U, (probed_cells_upto D L (query x)).card) ≤ 20 * U * t
      · let pD : Fin U → Finset (Fin m) := fun x => probed_cells_upto D L (query x)
        have hUreal : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hU
        have hmReal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
        have hmBoundNat : 160 * t ≤ m := by exact_mod_cast hm160
        have hcm : 8 * (20 * U * t) ≤ U * m := by
          have hmul := Nat.mul_le_mul_left U hmBoundNat
          simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
        have hntm : (n : ℝ) * (t : ℝ) / (m : ℝ) ≤ z := by
          have hwReal : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
          have hratio : (n : ℝ) / (m : ℝ) ≤ (w : ℝ) / v := by
            apply (div_le_div_iff₀ hmReal hvpos).2
            simpa [mul_comm] using hbase
          calc
            (n : ℝ) * (t : ℝ) / (m : ℝ) = ((n : ℝ) / (m : ℝ)) * (t : ℝ) := by
              field_simp
            _ ≤ ((w : ℝ) / v) * (t : ℝ) :=
              mul_le_mul_of_nonneg_right hratio (by positivity)
            _ = z := by dsimp [z]; field_simp
        have hexponent :
            -(8 : ℝ) * (n : ℝ) * ((20 * U * t : ℕ) : ℝ) /
                ((U : ℝ) * (m : ℝ)) =
              -(160 * ((n : ℝ) * (t : ℝ) / (m : ℝ))) := by
          push_cast
          field_simp
          ring
        have hexpMono : Real.exp (-(160 * z)) ≤
            Real.exp (-(8 : ℝ) * (n : ℝ) * ((20 * U * t : ℕ) : ℝ) /
              ((U : ℝ) * (m : ℝ))) := by
          rw [hexponent]
          apply Real.exp_le_exp.mpr
          exact neg_le_neg (mul_le_mul_of_nonneg_left hntm (by norm_num))
        have hthetaExp : 2 * theta ≤ (m : ℝ) / 2 *
            Real.exp (-(8 : ℝ) * (n : ℝ) * ((20 * U * t : ℕ) : ℝ) /
              ((U : ℝ) * (m : ℝ))) := by
          dsimp [theta]
          have hmul := mul_le_mul_of_nonneg_left hexpMono (show (0 : ℝ) ≤ (m : ℝ) / 2 by positivity)
          calc
            2 * ((m : ℝ) / 4 * Real.exp (-(160 * z))) =
                (m : ℝ) / 2 * Real.exp (-(160 * z)) := by ring
            _ ≤ (m : ℝ) / 2 * Real.exp (-(8 : ℝ) * (n : ℝ) *
                ((20 * U * t : ℕ) : ℝ) / ((U : ℝ) * (m : ℝ))) := hmul
        have hdev := untouched_cells_below_threshold_count U n m L (20 * U * t)
          pD theta hU h2nU hnU hLpos (by simpa [pD] using hD) hcm
          (fun x => (probed_cells_upto_card_le D L (query x)).1)
          hthetaNonneg hthetaExp
        change (((if (∑ x : Fin U, (probed_cells_upto D L (query x)).card) ≤ 20 * U * t then
          (Finset.powersetCard n (Finset.univ : Finset (Fin U))).filter
            (fun X => ((untouched_cells (fun x => probed_cells_upto D L (query x)) X).card : ℝ) <
              theta)
          else ∅).card : ℝ) ≤
          (Nat.choose U n : ℝ) * Real.exp (-(lam ^ 2) /
            (2 * (n : ℝ) * (L : ℝ) ^ 2)))
        rw [if_pos hD]
        simpa [pD, lam] using hdev
      · have hempty : candidates D = ∅ := by
          change (if (∑ x : Fin U, (probed_cells_upto D L (query x)).card) ≤ 20 * U * t then
            (Finset.powersetCard n (Finset.univ : Finset (Fin U))).filter
              (fun X => ((untouched_cells (fun x => probed_cells_upto D L (query x)) X).card : ℝ) < theta)
            else ∅) = ∅
          rw [if_neg hD]
        rw [hempty]
        simp only [Finset.card_empty, Nat.cast_zero]
        positivity
    have heligible : ∀ p ∈ low, p.1 ∈ candidates (memory p) := by
      intro p hp
      have hpGood := (Finset.mem_filter.mp hp).1
      have hpLow := (Finset.mem_filter.mp hp).2
      change p.1 ∈ (if (∑ x : Fin U, (probed_cells_upto (memory p) L (query x)).card) ≤ 20 * U * t then
        (Finset.powersetCard n (Finset.univ : Finset (Fin U))).filter
          (fun X => ((untouched_cells (fun x => probed_cells_upto (memory p) L (query x)) X).card : ℝ) < theta)
        else ∅)
      rw [if_pos (by simpa [probeSet] using hload p hpGood)]
      apply Finset.mem_filter.mpr
      constructor
      · rw [Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _, hgoodCard p hpGood⟩
      · simpa [probeSet] using lt_of_not_ge hpLow
    have hcountLow := retrieval_memory_candidate_encoding_bound U V w m ⟨0, hVpos⟩
      ((Nat.choose U n : ℝ) * Real.exp (-(lam ^ 2) /
        (2 * (n : ℝ) * (L : ℝ) ^ 2))) _ low (fun p => p.1) (fun p => p.2)
      memory query candidates
      (fun p hp => hgoodNorm p (Finset.mem_filter.mp hp).1)
      (fun p hp x hx => by
        have hpGood := (Finset.mem_filter.mp hp).1
        have hc := scheme.correct (inst p) x (by simpa [inst, hgoodCard p hpGood] using hx) tape
        simpa [memory, query, inst, hgoodCard p hpGood] using hc)
      heligible hcandidates
      (fun p hp q hq hkeys hvalues => Prod.ext hkeys hvalues)
    have hchoosePos : 0 < Nat.choose U n := Nat.choose_pos hnU
    have hVpowPos : (0 : ℝ) < ((V ^ n : ℕ) : ℝ) := by positivity
    have hcountExp : (((V ^ n : ℕ) : ℝ)) ≤
        4 * ((2 ^ (m * w) : ℕ) : ℝ) * Real.exp (-(lam ^ 2) /
          (2 * (n : ℝ) * (L : ℝ) ^ 2)) := by
      have hsmall' : 2 * Nat.choose U n * V ^ n ≤ 5 * low.card := by
        simpa [mul_assoc] using hsmall
      have hlowerReal : (2 : ℝ) * (Nat.choose U n : ℝ) * ((V ^ n : ℕ) : ℝ) ≤
          5 * (low.card : ℝ) := by exact_mod_cast hsmall'
      have hcombined := le_trans hlowerReal (mul_le_mul_of_nonneg_left hcountLow (by norm_num))
      have hchooseReal : (0 : ℝ) < (Nat.choose U n : ℝ) := by exact_mod_cast hchoosePos
      have hcancel : (2 : ℝ) * ((V ^ n : ℕ) : ℝ) ≤
          5 * ((2 ^ (m * w) : ℕ) : ℝ) * Real.exp (-(lam ^ 2) /
            (2 * (n : ℝ) * (L : ℝ) ^ 2)) := by
        have hcombined' : (Nat.choose U n : ℝ) *
            (2 * ((V ^ n : ℕ) : ℝ)) ≤
            (Nat.choose U n : ℝ) *
              (5 * ((2 ^ (m * w) : ℕ) : ℝ) * Real.exp (-(lam ^ 2) /
                (2 * (n : ℝ) * (L : ℝ) ^ 2))) := by
          calc
            (Nat.choose U n : ℝ) * (2 * ((V ^ n : ℕ) : ℝ)) =
                2 * (Nat.choose U n : ℝ) * ((V ^ n : ℕ) : ℝ) := by ring
            _ ≤ 5 * (((2 ^ (m * w) : ℕ) : ℝ) * ((Nat.choose U n : ℝ) *
                Real.exp (-(lam ^ 2) / (2 * (n : ℝ) * (L : ℝ) ^ 2)))) := hcombined
            _ = (Nat.choose U n : ℝ) *
                (5 * ((2 ^ (m * w) : ℕ) : ℝ) * Real.exp (-(lam ^ 2) /
                  (2 * (n : ℝ) * (L : ℝ) ^ 2))) := by ring
        exact le_of_mul_le_mul_left hcombined' hchooseReal
      have hnonneg : 0 ≤ ((2 ^ (m * w) : ℕ) : ℝ) *
          Real.exp (-(lam ^ 2) / (2 * (n : ℝ) * (L : ℝ) ^ 2)) := by positivity
      linarith
    let x : ℝ := lam ^ 2 / (2 * (n : ℝ) * (L : ℝ) ^ 2)
    have hxNonneg : 0 ≤ x := by positivity
    have hlogCount := logb_two_exponential_count_bound V n (m * w) x hVpos hxNonneg
      (by
        dsimp [x]
        simpa only [neg_div] using hcountExp)
    have hxUpper : x / Real.log 2 ≤
        (m : ℝ) * (w : ℝ) + 2 - (n : ℝ) * v := by
      simpa [v, Nat.cast_mul] using hlogCount
    have hxLower : (n : ℝ) * Real.exp (-(640 * z)) /
        (52428800 * z ^ 2) ≤ x := by
      have hLreal : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
      have htReal : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
      have hwReal : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
      have hmReal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      have hmLower : (n : ℝ) * v / (w : ℝ) ≤ (m : ℝ) := by
        apply (div_le_iff₀ hwReal).2
        exact hbase
      have hnv : (n : ℝ) * v ≤ (m : ℝ) * (w : ℝ) :=
        (div_le_iff₀ hwReal).mp hmLower
      have hmult := mul_le_mul_of_nonneg_right hnv (le_of_lt htReal)
      have hntzm : (n : ℝ) * (t : ℝ) ≤ z * (m : ℝ) := by
        have hmult' : v * ((n : ℝ) * (t : ℝ)) ≤ v * (z * (m : ℝ)) := by
          calc
            v * ((n : ℝ) * (t : ℝ)) = (n : ℝ) * v * (t : ℝ) := by ring
            _ ≤ (m : ℝ) * (w : ℝ) * (t : ℝ) := hmult
            _ = (m : ℝ) * ((w : ℝ) * (t : ℝ)) := by ring
            _ = (m : ℝ) * (z * v) := by rw [hzv]
            _ = v * (z * (m : ℝ)) := by ring
        exact le_of_mul_le_mul_left hmult' hvpos
      have hLsq : (L : ℝ) ^ 2 ≤
          ((1280 : ℝ) * (t : ℝ) * Real.exp (160 * z)) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity) hLupper 2
      dsimp [x, lam, theta]
      exact retrieval_branch_two_scale_lower_bound (n : ℝ) z (m : ℝ) (t : ℝ)
        (L : ℝ) (by exact_mod_cast hn) (lt_of_lt_of_le zero_lt_one hz) hmReal htReal
        hLreal hntzm hLsq
    exact retrieval_branch_two_numeric_contradiction (n : ℝ) v z (R : ℝ)
      ((m : ℝ) * (w : ℝ)) x (by exact_mod_cast hn) hv hz hRnonneg
      hnExp hRupper hbelow' hxLower hxUpper

@[blueprint "thm:randomized-static-retrieval-space-lower-bound"
  (statement := /-- Fix polynomial exponents $a,b$.  There exists a positive constant $C=C(a,b)$ such that, for all natural numbers $n,U,V,w,t,m$ satisfying $2n\leq U\leq n^a$, $V\leq n^b$, $1<V$, and $\log_2 V\leq w$, every randomized static retrieval scheme storing $n$ key--value pairs from $\operatorname{Fin}(U)$ with values in $\operatorname{Fin}(V)$ in $m$ cells of $w$ bits, for which the probe-count function of every fixed instance and every fixed universe key is integrable over the fair random tape and has expectation at most $t$, satisfies
  \[
    n\log_2 V+
    \left\lfloor n\exp\!\left(-C\frac{wt}{\log_2 V}\right)\right\rfloor
    \leq mw .
  \]
  Equivalently, its bit space is at least $n\log_2 V+\lfloor n e^{-O(wt/\log_2 V)}\rfloor$, where the hidden constant may depend on the fixed polynomial bounds $a,b$ but is independent of $n,U,V,w,t,m$ and the scheme. -/)
  (proof := /-- Fix $a,b$ and choose the positive constant supplied by \cref{lem:retrieval-space-not-strictly-below}.  For arbitrary parameters and a scheme satisfying the polynomial restrictions and expected-cost hypothesis, that lemma rules out the strict real inequality placing $mw$ below the threshold.  The linear order on the real numbers therefore places the threshold at most $mw$, which is the asserted lower bound. -/)
  (title := /-- Randomized static retrieval space lower bound -/)
  (latexEnv := "theorem")]
theorem randomized_static_retrieval_space_lower_bound :
    ∀ (a b : ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (n U V w t m : ℕ)
        (scheme : randomized_static_retrieval_scheme U n V w m),
        polynomial_retrieval_parameters n U V w a b →
        has_expected_query_cost scheme t →
        retrieval_space_threshold C n V w t ≤ (m : ℝ) * (w : ℝ) := by
  intro a b
  simpa only [not_lt] using retrieval_space_not_strictly_below a b

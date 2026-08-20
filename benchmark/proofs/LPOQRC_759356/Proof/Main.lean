import Architect
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:same-set-query"
  (statement := /-- Let $U$ be a universe.  A same-set query is an ordered pair
  $(x,y)\in U\times U$ whose answer records whether $x$ and $y$ lie in the same
  class of the hidden partition. -/)
  (title := /-- Same-set queries -/)
  (latexEnv := "definition")]
abbrev same_set_query (U : Type) := U × U

@[blueprint "def:same-set-oracle"
  (statement := /-- Let $U$ be a universe.  A Boolean same-set oracle assigns an
  answer to every query in $U\times U$, with the value $\mathtt{true}$ denoting
  membership in a common hidden class. -/)
  (title := /-- Boolean same-set oracles -/)
  (latexEnv := "definition")]
abbrev same_set_oracle (U : Type) := same_set_query U → Bool

@[blueprint "def:same-set-oracle-represents"
  (statement := /-- Let $P$ be a partition of $U$, represented by an equivalence
  relation, and let $\mathcal O$ be a Boolean same-set oracle.  We say that
  $\mathcal O$ represents $P$ if, for every $x,y\in U$, the value
  $\mathcal O(x,y)$ is $\mathtt{true}$ if and only if $x$ and $y$ are
  $P$-equivalent. -/)
  (title := /-- Oracles representing hidden partitions -/)
  (latexEnv := "definition")]
def same_set_oracle_represents {U : Type} (P : Setoid U)
    (oracle : same_set_oracle U) : Prop :=
  ∀ x y : U, oracle (x, y) = true ↔ P.r x y

@[blueprint "def:deterministic-pair-query-algorithm"
  (statement := /-- Let $U$ be a universe.  A deterministic pair-query algorithm
  with zero remaining rounds outputs a partition of $U$.  An algorithm with
  $s+1$ remaining rounds chooses a finite ordered list $Q$ of queries, receives
  all answers to $Q$ simultaneously, and deterministically selects an algorithm
  with $s$ remaining rounds as a function of that complete answer vector.  Thus
  later batches may depend on earlier answers, whereas no query in a batch may
  depend on another answer from the same batch. -/)
  (title := /-- Deterministic batched pair-query algorithms -/)
  (latexEnv := "definition")]
inductive deterministic_pair_query_algorithm (U : Type) : ℕ → Type where
  | output (learnedPartition : Setoid U) : deterministic_pair_query_algorithm U 0
  | query {remainingRounds : ℕ} (batch : List (same_set_query U))
      (next : (Fin batch.length → Bool) →
        deterministic_pair_query_algorithm U remainingRounds) :
      deterministic_pair_query_algorithm U (remainingRounds + 1)

@[blueprint "def:run-pair-query-algorithm"
  (statement := /-- Given a deterministic pair-query algorithm $A$ and an oracle
  $\mathcal O$, execute each batch against $\mathcal O$ and follow the unique
  continuation selected by its answer vector.  The result is the partition
  output after the prescribed number of rounds. -/)
  (title := /-- Execution of a pair-query algorithm -/)
  (latexEnv := "definition")]
def run_pair_query_algorithm {U : Type} :
    {rounds : ℕ} → deterministic_pair_query_algorithm U rounds →
      same_set_oracle U → Setoid U
  | 0, .output learnedPartition, _ => learnedPartition
  | _ + 1, .query batch next, oracle =>
      run_pair_query_algorithm (next (fun i => oracle (batch.get i))) oracle

@[blueprint "def:pair-query-count"
  (statement := /-- Given a deterministic pair-query algorithm $A$ and an oracle
  $\mathcal O$, its pathwise query count is the sum of the lengths of all batches
  encountered while executing $A$ against $\mathcal O$. -/)
  (title := /-- Pathwise number of pair queries -/)
  (latexEnv := "definition")]
def pair_query_count {U : Type} :
    {rounds : ℕ} → deterministic_pair_query_algorithm U rounds →
      same_set_oracle U → ℕ
  | 0, .output _, _ => 0
  | _ + 1, .query batch next, oracle =>
      batch.length + pair_query_count (next (fun i => oracle (batch.get i))) oracle

@[blueprint "def:pair-query-algorithm-learns"
  (statement := /-- Let $A$ be a deterministic pair-query algorithm on $U$ and
  let $P$ be a partition of $U$.  The algorithm $A$ learns $P$ if, for every
  Boolean oracle representing $P$, execution of $A$ against that oracle outputs
  exactly the equivalence relation $P$. -/)
  (title := /-- Exact learning of a hidden partition -/)
  (latexEnv := "definition")]
def pair_query_algorithm_learns {U : Type} {rounds : ℕ}
    (algorithm : deterministic_pair_query_algorithm U rounds) (P : Setoid U) : Prop :=
  ∀ oracle : same_set_oracle U,
    same_set_oracle_represents P oracle → run_pair_query_algorithm algorithm oracle = P

@[blueprint "def:partition-has-at-most-classes"
  (statement := /-- Let $P$ be a partition of $U$ and let $k\in\mathbb N$.  The
  partition $P$ has at most $k$ classes if the quotient type $U/P$ has natural
  cardinality at most $k$. -/)
  (title := /-- Partitions with a bounded number of classes -/)
  (latexEnv := "definition")]
def partition_has_at_most_classes {U : Type} (P : Setoid U) (k : ℕ) : Prop :=
  Nat.card (Quotient P) ≤ k

@[blueprint "def:pair-query-budget"
  (statement := /-- For natural numbers $n,k,r$, define
  \[
    B(n,k,r)=8n^{1+1/(2^r-1)}k^{1-1/(2^r-1)}.
  \]
  The powers of $n$ and $k$ are real powers, while $2^r$ is the ordinary
  natural-exponent power in $\mathbb R$. -/)
  (title := /-- The pair-query budget -/)
  (latexEnv := "definition")]
noncomputable def pair_query_budget (n k r : ℕ) : ℝ :=
  8 * Real.rpow (n : ℝ) (1 + 1 / ((2 : ℝ) ^ r - 1)) *
    Real.rpow (k : ℝ) (1 - 1 / ((2 : ℝ) ^ r - 1))

@[blueprint "def:learns-k-partitions-with-budget"
  (statement := /-- Let $U$ be finite, let $A$ be an $r$-round deterministic
  pair-query algorithm on $U$, let $k\in\mathbb N$, and let $B\in\mathbb R$.
  The algorithm $A$ learns all $k$-partitions within budget $B$ if, for every
  partition $P$ of $U$ having at most $k$ classes, the algorithm learns $P$ and,
  for every Boolean oracle representing $P$, its pathwise query count is at most
  $B$. -/)
  (title := /-- Uniform learning within a query budget -/)
  (latexEnv := "definition")]
def learns_k_partitions_with_budget {U : Type} [Fintype U] {rounds : ℕ}
    (algorithm : deterministic_pair_query_algorithm U rounds) (k : ℕ) (budget : ℝ) : Prop :=
  ∀ P : Setoid U, partition_has_at_most_classes P k →
    pair_query_algorithm_learns algorithm P ∧
      ∀ oracle : same_set_oracle U, same_set_oracle_represents P oracle →
        (pair_query_count algorithm oracle : ℝ) ≤ budget

@[blueprint "def:pair-query-extend"
  (statement := /-- Let $A$ be a deterministic pair-query algorithm with $m$
  remaining rounds and let $C$ assign, to each partition of $U$, a deterministic
  pair-query algorithm with $p$ remaining rounds.  The extension $\mathrm{ext}(C,A)$
  runs $A$ to completion and then, on the partition $A$ outputs, continues with
  $C$.  It has $p+m$ remaining rounds. -/)
  (title := /-- Sequential extension of a pair-query algorithm -/)
  (latexEnv := "definition")]
def pair_query_extend {U : Type} {p : ℕ}
    (cont : Setoid U → deterministic_pair_query_algorithm U p) :
    {m : ℕ} → deterministic_pair_query_algorithm U m →
      deterministic_pair_query_algorithm U (p + m)
  | 0, .output learnedPartition => cont learnedPartition
  | _ + 1, .query batch next =>
      .query batch (fun ans => pair_query_extend cont (next ans))

@[blueprint "lem:run-pair-query-extend"
  (statement := /-- For every algorithm $A$, continuation $C$ and oracle
  $\mathcal O$, executing the extension $\mathrm{ext}(C,A)$ against $\mathcal O$
  is the same as executing $C$ applied to the partition that $A$ outputs on
  $\mathcal O$. -/)
  (proof := /-- Induct on the structure of $A$.  If $A$ outputs a partition, the
  extension is $C$ applied to that partition, so both sides agree.  If $A$ first
  queries a batch and continues with $\mathrm{next}$, then execution feeds the
  answer vector to $\mathrm{next}$ on both sides, and the inductive hypothesis
  for the selected continuation closes the goal. -/)
  (title := /-- Execution of a sequential extension -/)
  (latexEnv := "lemma")]
lemma run_pair_query_extend {U : Type} {p : ℕ}
    (cont : Setoid U → deterministic_pair_query_algorithm U p) :
    ∀ {m : ℕ} (A : deterministic_pair_query_algorithm U m)
      (oracle : same_set_oracle U),
      run_pair_query_algorithm (pair_query_extend cont A) oracle
        = run_pair_query_algorithm (cont (run_pair_query_algorithm A oracle)) oracle := by
  intro m A
  induction A with
  | output learnedPartition => intro oracle; rfl
  | query batch next ih =>
      intro oracle
      simp only [pair_query_extend, run_pair_query_algorithm]
      exact ih _ oracle

@[blueprint "lem:count-pair-query-extend"
  (statement := /-- For every algorithm $A$, continuation $C$ and oracle
  $\mathcal O$, the pathwise query count of the extension $\mathrm{ext}(C,A)$ on
  $\mathcal O$ equals the count of $A$ on $\mathcal O$ plus the count of $C$
  applied to the partition that $A$ outputs on $\mathcal O$. -/)
  (proof := /-- Induct on the structure of $A$.  If $A$ outputs a partition, the
  extension is $C$ applied to that partition and $A$ contributes no queries, so
  the counts agree.  If $A$ queries a batch and continues with $\mathrm{next}$,
  both sides add the batch length, and the inductive hypothesis for the selected
  continuation together with associativity of addition closes the goal. -/)
  (title := /-- Query count of a sequential extension -/)
  (latexEnv := "lemma")]
lemma count_pair_query_extend {U : Type} {p : ℕ}
    (cont : Setoid U → deterministic_pair_query_algorithm U p) :
    ∀ {m : ℕ} (A : deterministic_pair_query_algorithm U m)
      (oracle : same_set_oracle U),
      pair_query_count (pair_query_extend cont A) oracle
        = pair_query_count A oracle
          + pair_query_count (cont (run_pair_query_algorithm A oracle)) oracle := by
  intro m A
  induction A with
  | output learnedPartition =>
      intro oracle
      simp [pair_query_extend, pair_query_count, run_pair_query_algorithm]
  | query batch next ih =>
      intro oracle
      simp only [pair_query_extend, pair_query_count, run_pair_query_algorithm]
      rw [ih _ oracle, Nat.add_assoc]

@[blueprint "def:pair-query-parallel"
  (statement := /-- Let $A$ and $B$ be deterministic pair-query algorithms on
  $U$ with the same number $s$ of remaining rounds.  Their parallel product runs
  both simultaneously: in each round it poses the concatenation of the two
  batches, splits the answer vector back into the two halves, and continues on
  each side.  After $s$ rounds each side outputs a partition, and the product
  outputs their join in the lattice of partitions of $U$. -/)
  (title := /-- Parallel product of pair-query algorithms -/)
  (latexEnv := "definition")]
def pair_query_parallel {U : Type} :
    {s : ℕ} → deterministic_pair_query_algorithm U s →
      deterministic_pair_query_algorithm U s →
        deterministic_pair_query_algorithm U s
  | 0, .output P, .output Q => .output (P ⊔ Q)
  | _ + 1, .query b1 n1, .query b2 n2 =>
      .query (b1 ++ b2) (fun ans =>
        pair_query_parallel
          (n1 (fun i => ans ⟨i.val, by rw [List.length_append]; omega⟩))
          (n2 (fun j => ans ⟨b1.length + j.val, by rw [List.length_append]; omega⟩)))

@[blueprint "lem:run-pair-query-parallel"
  (statement := /-- For all algorithms $A,B$ on $U$ with the same number of
  remaining rounds and every oracle $\mathcal O$, executing the parallel product
  of $A$ and $B$ against $\mathcal O$ outputs the join, in the partition lattice
  of $U$, of the partitions that $A$ and $B$ individually output on
  $\mathcal O$. -/)
  (proof := /-- Induct on the common round count.  With zero rounds both
  algorithms output partitions and the product outputs their join by definition.
  With one more round, the product poses the concatenated batch; by
  \cref{def:pair-query-parallel} the left continuation receives the answers to
  the first block and the right continuation the answers to the second block, so
  after rewriting the answer indices through the append lemmas the two
  continuations coincide with those of $A$ and $B$, and the inductive hypothesis
  yields the join. -/)
  (title := /-- Execution of a parallel product -/)
  (latexEnv := "lemma")]
lemma run_pair_query_parallel {U : Type} :
    ∀ {s : ℕ} (A B : deterministic_pair_query_algorithm U s)
      (oracle : same_set_oracle U),
      run_pair_query_algorithm (pair_query_parallel A B) oracle
        = run_pair_query_algorithm A oracle ⊔ run_pair_query_algorithm B oracle := by
  intro s
  induction s with
  | zero =>
      intro A B oracle
      match A, B with
      | .output P, .output Q => rfl
  | succ s ih =>
      intro A B oracle
      match A, B with
      | .query b1 n1, .query b2 n2 =>
          simp only [pair_query_parallel, run_pair_query_algorithm]
          rw [ih]
          have hleft : (fun i : Fin b1.length =>
              oracle ((b1 ++ b2).get ⟨i.val, by rw [List.length_append]; omega⟩))
              = fun i : Fin b1.length => oracle (b1.get i) := by
            funext i
            simp only [List.get_eq_getElem, List.getElem_append_left i.isLt]
          have hright : (fun j : Fin b2.length =>
              oracle ((b1 ++ b2).get ⟨b1.length + j.val, by rw [List.length_append]; omega⟩))
              = fun j : Fin b2.length => oracle (b2.get j) := by
            funext j
            simp only [List.get_eq_getElem,
              List.getElem_append_right (Nat.le_add_right b1.length j.val),
              Nat.add_sub_cancel_left]
          rw [hleft, hright]

@[blueprint "lem:count-pair-query-parallel"
  (statement := /-- For all algorithms $A,B$ on $U$ with the same number of
  remaining rounds and every oracle $\mathcal O$, the pathwise query count of
  the parallel product on $\mathcal O$ equals the sum of the pathwise query
  counts of $A$ and $B$ on $\mathcal O$. -/)
  (proof := /-- Induct on the common round count.  With zero rounds both
  algorithms output partitions and contribute no queries, so both sides are
  zero.  With one more round, the concatenated batch has length equal to the sum
  of the two batch lengths; rewriting the answer indices through the append
  lemmas identifies the continuations with those of $A$ and $B$, and the
  inductive hypothesis together with commutativity and associativity of addition
  rearranges the four summands into the required sum. -/)
  (title := /-- Query count of a parallel product -/)
  (latexEnv := "lemma")]
lemma count_pair_query_parallel {U : Type} :
    ∀ {s : ℕ} (A B : deterministic_pair_query_algorithm U s)
      (oracle : same_set_oracle U),
      pair_query_count (pair_query_parallel A B) oracle
        = pair_query_count A oracle + pair_query_count B oracle := by
  intro s
  induction s with
  | zero =>
      intro A B oracle
      match A, B with
      | .output P, .output Q => rfl
  | succ s ih =>
      intro A B oracle
      match A, B with
      | .query b1 n1, .query b2 n2 =>
          simp only [pair_query_parallel, pair_query_count, run_pair_query_algorithm,
            List.length_append]
          have hleft : (fun i : Fin b1.length =>
              (fun i : Fin (b1 ++ b2).length => oracle ((b1 ++ b2).get i))
                ⟨i.val, by rw [List.length_append]; omega⟩)
              = fun i : Fin b1.length => oracle (b1.get i) := by
            funext i
            simp only [List.get_eq_getElem, List.getElem_append_left i.isLt]
          have hright : (fun j : Fin b2.length =>
              (fun i : Fin (b1 ++ b2).length => oracle ((b1 ++ b2).get i))
                ⟨b1.length + j.val, by rw [List.length_append]; omega⟩)
              = fun j : Fin b2.length => oracle (b2.get j) := by
            funext j
            simp only [List.get_eq_getElem,
              List.getElem_append_right (Nat.le_add_right b1.length j.val),
              Nat.add_sub_cancel_left]
          rw [ih, hleft, hright]
          omega

@[blueprint "def:pair-query-one-round"
  (statement := /-- Let $U$ be a type and let $L$ be a finite list of ordered
  queries in $U\times U$.  The one-round algorithm $\mathrm{oneRound}(L)$ poses
  the whole list $L$ in a single round and, from the answer vector, outputs the
  equivalence relation generated by those pairs of $L$ whose answer is
  $\mathtt{true}$. -/)
  (title := /-- The single-round list algorithm -/)
  (latexEnv := "definition")]
def pair_query_one_round {U : Type} (L : List (same_set_query U)) :
    deterministic_pair_query_algorithm U 1 :=
  .query L (fun ans =>
    .output (Relation.EqvGen.setoid
      (fun x y => ∃ i : Fin L.length, L.get i = (x, y) ∧ ans i = true)))

@[blueprint "lem:count-pair-query-one-round"
  (statement := /-- For every list $L$ and oracle $\mathcal O$, the pathwise
  query count of $\mathrm{oneRound}(L)$ on $\mathcal O$ equals the length of
  $L$. -/)
  (proof := /-- Unfold \cref{def:pair-query-one-round} and
  \cref{def:pair-query-count}: the single batch is $L$, of length $\lvert
  L\rvert$, and the continuation outputs immediately, contributing no further
  queries. -/)
  (title := /-- Query count of the single-round list algorithm -/)
  (latexEnv := "lemma")]
lemma count_pair_query_one_round {U : Type} (L : List (same_set_query U))
    (oracle : same_set_oracle U) :
    pair_query_count (pair_query_one_round L) oracle = L.length := by
  simp [pair_query_one_round, pair_query_count]

@[blueprint "lem:run-pair-query-one-round"
  (statement := /-- For every list $L$ and oracle $\mathcal O$, executing
  $\mathrm{oneRound}(L)$ against $\mathcal O$ outputs the equivalence relation
  generated by the relation that holds of $(x,y)$ when some entry of $L$ equals
  $(x,y)$ and $\mathcal O$ answers $\mathtt{true}$ on it. -/)
  (proof := /-- Unfold \cref{def:pair-query-one-round} and the one-step execution
  of \cref{def:run-pair-query-algorithm}: the answer vector supplied to the
  continuation is $i\mapsto\mathcal O(L_i)$, and substituting it into the
  generating relation yields the stated closure. -/)
  (title := /-- Execution of the single-round list algorithm -/)
  (latexEnv := "lemma")]
lemma run_pair_query_one_round {U : Type} (L : List (same_set_query U))
    (oracle : same_set_oracle U) :
    run_pair_query_algorithm (pair_query_one_round L) oracle
      = Relation.EqvGen.setoid
          (fun x y => ∃ i : Fin L.length, L.get i = (x, y) ∧ oracle (L.get i) = true) := by
  rfl

@[blueprint "def:pair-query-transport"
  (statement := /-- Let $g:U\to V$ and $h:V\to U$ be functions and let $A$ be a
  deterministic pair-query algorithm on $V$ with $s$ remaining rounds.  The
  transport $\mathrm{transport}(g,h,A)$ is a pair-query algorithm on $U$ with $s$
  remaining rounds: each $V$-query $(a,b)$ that $A$ would pose is translated to
  the $U$-query $(h\,a,h\,b)$, the answers are fed back unchanged, and the final
  partition $Q$ of $V$ produced by $A$ is returned as the pullback
  $\mathrm{comap}\,g\,Q$ on $U$. -/)
  (title := /-- Transport of a pair-query algorithm along maps -/)
  (latexEnv := "definition")]
def pair_query_transport {U V : Type} (g : U → V) (h : V → U) :
    {s : ℕ} → deterministic_pair_query_algorithm V s →
      deterministic_pair_query_algorithm U s
  | 0, .output Q => .output (Setoid.comap g Q)
  | _ + 1, .query batch next =>
      .query (batch.map (fun q => (h q.1, h q.2))) (fun ans =>
        pair_query_transport g h
          (next (fun i => ans ⟨i.val, by rw [List.length_map]; exact i.isLt⟩)))

@[blueprint "lem:run-pair-query-transport"
  (statement := /-- For all $g:U\to V$, $h:V\to U$, algorithm $A$ on $V$ and
  oracle $\mathcal O$ on $U$, executing $\mathrm{transport}(g,h,A)$ against
  $\mathcal O$ returns $\mathrm{comap}\,g$ of the partition that $A$ outputs on
  the induced oracle $(a,b)\mapsto\mathcal O(h\,a,h\,b)$. -/)
  (proof := /-- Induct on the round count of $A$.  With zero rounds $A$ outputs a
  partition and by \cref{def:pair-query-transport} the transport returns its
  pullback.  With one more round the transported batch is the image of $A$'s
  batch under $h$; hence the $i$-th supplied answer is $\mathcal O(h\,a_i,h\,b_i)$,
  which is exactly the induced-oracle answer to $A$'s $i$-th query after
  rewriting the index through the map-length lemma, and the inductive hypothesis
  for the selected continuation closes the goal. -/)
  (title := /-- Execution of a transported algorithm -/)
  (latexEnv := "lemma")]
lemma run_pair_query_transport {U V : Type} (g : U → V) (h : V → U) :
    ∀ {s : ℕ} (A : deterministic_pair_query_algorithm V s)
      (oracle : same_set_oracle U),
      run_pair_query_algorithm (pair_query_transport g h A) oracle
        = Setoid.comap g
            (run_pair_query_algorithm A (fun q => oracle (h q.1, h q.2))) := by
  intro s
  induction s with
  | zero =>
      intro A oracle
      match A with
      | .output Q => rfl
  | succ s ih =>
      intro A oracle
      match A with
      | .query batch next =>
          simp only [pair_query_transport, run_pair_query_algorithm]
          rw [ih]
          congr 2
          congr 1
          funext i
          simp only [List.get_eq_getElem, List.getElem_map]

@[blueprint "lem:count-pair-query-transport"
  (statement := /-- For all $g:U\to V$, $h:V\to U$, algorithm $A$ on $V$ and
  oracle $\mathcal O$ on $U$, the pathwise query count of
  $\mathrm{transport}(g,h,A)$ on $\mathcal O$ equals the pathwise query count of
  $A$ on the induced oracle $(a,b)\mapsto\mathcal O(h\,a,h\,b)$. -/)
  (proof := /-- Induct on the round count of $A$.  With zero rounds both counts
  are zero.  With one more round the transported batch has the same length as
  $A$'s batch by the map-length lemma, and after rewriting the answer index the
  selected continuation matches, so the inductive hypothesis gives equality of
  the remaining counts. -/)
  (title := /-- Query count of a transported algorithm -/)
  (latexEnv := "lemma")]
lemma count_pair_query_transport {U V : Type} (g : U → V) (h : V → U) :
    ∀ {s : ℕ} (A : deterministic_pair_query_algorithm V s)
      (oracle : same_set_oracle U),
      pair_query_count (pair_query_transport g h A) oracle
        = pair_query_count A (fun q => oracle (h q.1, h q.2)) := by
  intro s
  induction s with
  | zero =>
      intro A oracle
      match A with
      | .output Q => rfl
  | succ s ih =>
      intro A oracle
      match A with
      | .query batch next =>
          simp only [pair_query_transport, pair_query_count, run_pair_query_algorithm,
            List.length_map]
          rw [ih]
          congr 2
          congr 1
          funext i
          simp only [List.get_eq_getElem, List.getElem_map]

@[blueprint "def:pair-query-const"
  (statement := /-- Let $U$ be a type, $P$ a partition of $U$ and $s\in\mathbb N$.
  The constant algorithm $\mathrm{const}(P,s)$ uses $s$ rounds, poses the empty
  batch in each round, and finally outputs the fixed partition $P$. -/)
  (title := /-- The constant-output algorithm -/)
  (latexEnv := "definition")]
def pair_query_const {U : Type} (P : Setoid U) :
    (s : ℕ) → deterministic_pair_query_algorithm U s
  | 0 => .output P
  | s + 1 => .query [] (fun _ => pair_query_const P s)

@[blueprint "lem:run-pair-query-const"
  (statement := /-- For every partition $P$, round count $s$ and oracle
  $\mathcal O$, executing $\mathrm{const}(P,s)$ against $\mathcal O$ outputs
  $P$. -/)
  (proof := /-- Induct on $s$.  For $s=0$ the algorithm outputs $P$ by
  \cref{def:pair-query-const}.  For $s+1$ the single empty batch is answered on
  $\mathrm{Fin}\,0$ and the continuation reduces to the case $s$ by the inductive
  hypothesis. -/)
  (title := /-- Execution of the constant-output algorithm -/)
  (latexEnv := "lemma")]
lemma run_pair_query_const {U : Type} (P : Setoid U) :
    ∀ (s : ℕ) (oracle : same_set_oracle U),
      run_pair_query_algorithm (pair_query_const P s) oracle = P := by
  intro s
  induction s with
  | zero => intro oracle; rfl
  | succ s ih =>
      intro oracle
      simp only [pair_query_const, run_pair_query_algorithm]
      exact ih _

@[blueprint "lem:count-pair-query-const"
  (statement := /-- For every partition $P$, round count $s$ and oracle
  $\mathcal O$, the pathwise query count of $\mathrm{const}(P,s)$ on $\mathcal O$
  is $0$. -/)
  (proof := /-- Induct on $s$.  For $s=0$ no query is posed.  For $s+1$ the empty
  batch has length $0$ and the continuation contributes nothing by the inductive
  hypothesis. -/)
  (title := /-- Query count of the constant-output algorithm -/)
  (latexEnv := "lemma")]
lemma count_pair_query_const {U : Type} (P : Setoid U) :
    ∀ (s : ℕ) (oracle : same_set_oracle U),
      pair_query_count (pair_query_const P s) oracle = 0 := by
  intro s
  induction s with
  | zero => intro oracle; rfl
  | succ s ih =>
      intro oracle
      simp only [pair_query_const, pair_query_count, run_pair_query_algorithm,
        List.length_nil, Nat.zero_add]
      exact ih _

@[blueprint "lem:all-pairs-within-budget"
  (statement := /-- Let $U$ be a finite universe of cardinality $n$, let
  $k,R\ge 1$ and let $B\in\mathbb R$ satisfy $n^2\le B$.  Then there is a
  deterministic $R$-round pair-query algorithm on $U$ that learns every
  partition of $U$ into at most $k$ classes within budget $B$. -/)
  (proof := /-- Pose in the first round the list of all ordered pairs of $U$ and,
  in the remaining $R-1$ rounds, pose no query, finally returning the
  equivalence relation generated by the true pairs, combining
  \cref{def:pair-query-one-round}, \cref{def:pair-query-extend} and
  \cref{def:pair-query-const}.  Run this in parallel
  (\cref{def:pair-query-parallel}) with the silent constant algorithm that only
  ever outputs the trivial partition $\bot$.  On an oracle representing a
  partition $P$ the generated relation is exactly $P$ by
  \cref{lem:run-pair-query-one-round}, \cref{lem:run-pair-query-extend} and
  \cref{lem:run-pair-query-const}, and the parallel output is the join with
  $\bot$, namely $P$, by \cref{lem:run-pair-query-parallel}, so the algorithm
  learns $P$; its query count equals $n^2$ by
  \cref{lem:count-pair-query-one-round}, \cref{lem:count-pair-query-extend},
  \cref{lem:count-pair-query-const} and \cref{lem:count-pair-query-parallel},
  which is at most $B$. -/)
  (title := /-- The all-pairs algorithm within a quadratic budget -/)
  (latexEnv := "lemma")]
lemma all_pairs_within_budget {U : Type} [Fintype U] {R k : ℕ} (hR : 1 ≤ R)
    (B : ℝ) (hB : ((Fintype.card U : ℝ)) ^ 2 ≤ B) :
    ∃ A : deterministic_pair_query_algorithm U R,
      learns_k_partitions_with_budget A k B := by
  obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
  set L : List (same_set_query U) := (Finset.univ : Finset (U × U)).toList with hL
  set Amain : deterministic_pair_query_algorithm U (R' + 1) :=
    pair_query_extend (fun P => pair_query_const P R') (pair_query_one_round L) with hAmain
  refine ⟨pair_query_parallel Amain (pair_query_const (⊥ : Setoid U) (R' + 1)), ?_⟩
  intro P _
  have hrun : ∀ oracle : same_set_oracle U, same_set_oracle_represents P oracle →
      run_pair_query_algorithm Amain oracle = P := by
    intro oracle hOracle
    rw [hAmain, run_pair_query_extend, run_pair_query_const, run_pair_query_one_round]
    apply Setoid.ext
    intro x y
    have hgen : (fun x y => ∃ i : Fin L.length, L.get i = (x, y) ∧ oracle (L.get i) = true)
        = fun x y => P.r x y := by
      funext x y
      apply propext
      constructor
      · rintro ⟨i, hi, hb⟩
        rw [hi] at hb
        exact (hOracle x y).1 hb
      · intro hxy
        have hmem : (x, y) ∈ L := by rw [hL, Finset.mem_toList]; exact Finset.mem_univ _
        obtain ⟨i, hi⟩ := List.mem_iff_get.1 hmem
        exact ⟨i, hi, by rw [hi]; exact (hOracle x y).2 hxy⟩
    rw [hgen]
    have hEq : Relation.EqvGen (fun x y => P.r x y) = fun x y => P.r x y :=
      P.iseqv.eqvGen_eq
    change Relation.EqvGen (fun x y => P.r x y) x y ↔ P.r x y
    rw [hEq]
  refine ⟨?_, ?_⟩
  · intro oracle hOracle
    rw [run_pair_query_parallel, run_pair_query_const, hrun oracle hOracle, sup_bot_eq]
  · intro oracle hOracle
    rw [count_pair_query_parallel, count_pair_query_const, Nat.add_zero, hAmain,
      count_pair_query_extend, count_pair_query_one_round, count_pair_query_const,
      Nat.add_zero]
    have hlen : L.length = Fintype.card U * Fintype.card U := by
      rw [hL, Finset.length_toList, Finset.card_univ, Fintype.card_prod]
    rw [hlen]
    push_cast
    rw [← sq]
    exact hB

@[blueprint "lem:budget-step-arith"
  (statement := /-- Let $a,b$ be real numbers with $0<a<1$, $0\le b$ and
  $(1-a)(1+b)=1+a$, and let $n,k,\gamma,\sigma,\gamma_0$ be real numbers with
  $1\le k$, $1\le n$, $\gamma_0=\tfrac14(n/k)^{1-a}$, $2<\gamma_0$,
  $\gamma_0\le\gamma\le\gamma_0+1$ and $\sigma\le n/\gamma+1$.  Then
  \[
    \sigma n+8(\gamma k)^{1+b}k^{1-b}\le 8n^{1+a}k^{1-a}.
  \] -/)
  (proof := /-- Write $X=n^{1+a}k^{1-a}>0$.  Since
  $\gamma_0=\tfrac14(n/k)^{1-a}$ one gets $n^2/\gamma_0=4X$, whence
  $\sigma n\le n^2/\gamma+n\le n^2/\gamma_0+n=4X+n\le 5X$, using $n\le X$.  Next
  $(\gamma k)^{1+b}k^{1-b}=\gamma^{1+b}k^2$, and $\gamma_0^{1+b}k^2=(1/4)^{1+b}X$
  by the exponent identity $(1-a)(1+b)=1+a$.  From $\gamma\le\gamma_0+1\le
  \tfrac32\gamma_0$ we obtain $\gamma^{1+b}k^2\le(3/8)^{1+b}X\le\tfrac38X$, so
  $8\gamma^{1+b}k^2\le 3X$.  Adding the two estimates gives $\le 8X$. -/)
  (title := /-- The recursion budget inequality -/)
  (latexEnv := "lemma")]
lemma budget_step_arith (a b : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 ≤ b)
    (hid : (1 - a) * (1 + b) = 1 + a)
    (nn kk gr sr g0 : ℝ) (hk : 1 ≤ kk) (hn : 1 ≤ nn)
    (hg0def : g0 = (1 / 4) * (nn / kk) ^ (1 - a))
    (hg0 : 2 < g0) (hgr_lo : g0 ≤ gr) (hgr_hi : gr ≤ g0 + 1)
    (hsr : sr ≤ nn / gr + 1) :
    sr * nn + 8 * (gr * kk) ^ (1 + b) * kk ^ (1 - b)
      ≤ 8 * nn ^ (1 + a) * kk ^ (1 - a) := by
  have hnn0 : (0 : ℝ) < nn := lt_of_lt_of_le one_pos hn
  have hkk0 : (0 : ℝ) < kk := lt_of_lt_of_le one_pos hk
  have hg0pos : 0 < g0 := by linarith
  have hgrpos : 0 < gr := by linarith
  set X := nn ^ (1 + a) * kk ^ (1 - a) with hX
  have hXpos : 0 < X := by rw [hX]; positivity
  have hsq : nn * nn = nn ^ (1 + a) * nn ^ (1 - a) := by
    rw [← Real.rpow_add hnn0, show (1 : ℝ) + a + (1 - a) = 2 by ring,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  have hnnr : (nn : ℝ) ^ (1 - a) ≠ 0 := by positivity
  have hkkr : (kk : ℝ) ^ (1 - a) ≠ 0 := by positivity
  have hka : (kk : ℝ) ^ (1 + a) ≠ 0 := by positivity
  have e1 : nn * nn / g0 = 4 * X := by
    rw [hg0def, Real.div_rpow hnn0.le hkk0.le, hsq, hX]
    field_simp
  have e2 : (gr * kk) ^ (1 + b) * kk ^ (1 - b) = gr ^ (1 + b) * kk ^ (2 : ℝ) := by
    rw [Real.mul_rpow hgrpos.le hkk0.le, mul_assoc, ← Real.rpow_add hkk0,
      show (1 + b) + (1 - b) = (2 : ℝ) by ring]
  have hkkexp : (kk : ℝ) ^ (2 : ℝ) = kk ^ (1 + a) * kk ^ (1 - a) := by
    rw [← Real.rpow_add hkk0]; norm_num
  have g0pow : g0 ^ (1 + b) * kk ^ (2 : ℝ) = (1 / 4) ^ (1 + b) * X := by
    rw [hg0def, Real.mul_rpow (by norm_num) (by positivity),
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ nn / kk), hid,
      Real.div_rpow hnn0.le hkk0.le, hX, hkkexp]
    field_simp
  have hnnX : nn ≤ X := by
    rw [hX]
    calc nn = nn ^ (1 : ℝ) := (Real.rpow_one nn).symm
      _ ≤ nn ^ (1 + a) := by
          apply Real.rpow_le_rpow_of_exponent_le hn; linarith
      _ = nn ^ (1 + a) * 1 := (mul_one _).symm
      _ ≤ nn ^ (1 + a) * kk ^ (1 - a) := by
          apply mul_le_mul_of_nonneg_left (Real.one_le_rpow hk (by linarith)) (by positivity)
  have key1 : sr * nn ≤ 5 * X := by
    have hsrnn : sr * nn ≤ (nn / gr + 1) * nn :=
      mul_le_mul_of_nonneg_right hsr hnn0.le
    have expand : (nn / gr + 1) * nn = nn * nn / gr + nn := by
      rw [add_mul, one_mul, div_mul_eq_mul_div]
    have hdiv : nn * nn / gr ≤ nn * nn / g0 := by
      apply div_le_div_of_nonneg_left (by positivity) hg0pos hgr_lo
    rw [expand] at hsrnn
    rw [e1] at hdiv
    linarith
  have hgr32 : gr ≤ (3 / 2) * g0 := by linarith
  have hgrpow : gr ^ (1 + b) ≤ (3 / 2) ^ (1 + b) * g0 ^ (1 + b) := by
    have h := Real.rpow_le_rpow hgrpos.le hgr32 (by linarith : (0 : ℝ) ≤ 1 + b)
    rwa [Real.mul_rpow (by norm_num) hg0pos.le] at h
  have hfrac : ((3 : ℝ) / 8) ^ (1 + b) ≤ 3 / 8 := by
    have h := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 3 / 8)
      (by norm_num : (3 : ℝ) / 8 ≤ 1) (by linarith : (1 : ℝ) ≤ 1 + b)
    rwa [Real.rpow_one] at h
  have hcombine : gr ^ (1 + b) * kk ^ (2 : ℝ) ≤ (3 / 8) * X := by
    have step1 : gr ^ (1 + b) * kk ^ (2 : ℝ)
        ≤ (3 / 2) ^ (1 + b) * g0 ^ (1 + b) * kk ^ (2 : ℝ) :=
      mul_le_mul_of_nonneg_right hgrpow (by positivity)
    have step2 : (3 / 2) ^ (1 + b) * g0 ^ (1 + b) * kk ^ (2 : ℝ)
        = (3 / 8) ^ (1 + b) * X := by
      rw [mul_assoc, g0pow, ← mul_assoc, ← Real.mul_rpow (by norm_num) (by norm_num)]
      norm_num
    rw [step2] at step1
    have step3 : ((3 : ℝ) / 8) ^ (1 + b) * X ≤ (3 / 8) * X :=
      mul_le_mul_of_nonneg_right hfrac hXpos.le
    linarith
  have key2 : 8 * (gr * kk) ^ (1 + b) * kk ^ (1 - b) ≤ 3 * X := by
    rw [mul_assoc, e2]
    linarith
  have hgoalX : (8 : ℝ) * nn ^ (1 + a) * kk ^ (1 - a) = 8 * X := by rw [hX]; ring
  rw [hgoalX]
  linarith

@[blueprint "lem:pair-query-budget-mono-left"
  (statement := /-- For natural numbers $m\le n$ and any $k,r$, the budget is
  monotone in its first argument: $B(m,k,r)\le B(n,k,r)$. -/)
  (proof := /-- Unfold \cref{def:pair-query-budget}.  The factor
  $8k^{1-1/(2^r-1)}$ is nonnegative and common to both sides, while
  $m^{1+1/(2^r-1)}\le n^{1+1/(2^r-1)}$ holds because the exponent
  $1+1/(2^r-1)$ is nonnegative and the real power is monotone in its base. -/)
  (title := /-- Monotonicity of the budget in the universe size -/)
  (latexEnv := "lemma")]
lemma pair_query_budget_mono_left {m n : ℕ} (hmn : m ≤ n) (k r : ℕ) :
    pair_query_budget m k r ≤ pair_query_budget n k r := by
  unfold pair_query_budget
  have hexp : (0 : ℝ) ≤ 1 + 1 / ((2 : ℝ) ^ r - 1) := by
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num)
    rcases eq_or_lt_of_le h2 with h | h
    · rw [← h]; norm_num
    · have hpos : (0 : ℝ) < (2 : ℝ) ^ r - 1 := by linarith
      have hinv : (0 : ℝ) ≤ 1 / ((2 : ℝ) ^ r - 1) := le_of_lt (div_pos one_pos hpos)
      linarith
  have hbase : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hpow : (m : ℝ) ^ (1 + 1 / ((2 : ℝ) ^ r - 1))
      ≤ (n : ℝ) ^ (1 + 1 / ((2 : ℝ) ^ r - 1)) :=
    Real.rpow_le_rpow (Nat.cast_nonneg m) hbase hexp
  have hcoef : (0 : ℝ) ≤ 8 := by norm_num
  have hk : (0 : ℝ) ≤ Real.rpow (k : ℝ) (1 - 1 / ((2 : ℝ) ^ r - 1)) :=
    Real.rpow_nonneg (Nat.cast_nonneg k) _
  calc 8 * Real.rpow (m : ℝ) (1 + 1 / ((2 : ℝ) ^ r - 1))
          * Real.rpow (k : ℝ) (1 - 1 / ((2 : ℝ) ^ r - 1))
        ≤ 8 * Real.rpow (n : ℝ) (1 + 1 / ((2 : ℝ) ^ r - 1))
          * Real.rpow (k : ℝ) (1 - 1 / ((2 : ℝ) ^ r - 1)) := by
          apply mul_le_mul_of_nonneg_right _ hk
          apply mul_le_mul_of_nonneg_left hpow hcoef

@[blueprint "lem:exists-balanced-grouping"
  (statement := /-- Let $U$ be a finite universe of cardinality $n$ and let
  $g,s\ge 1$ with $n\le g\cdot s$.  Then there is a function
  $\mathrm{gid}:U\to\mathrm{Fin}\,g$ assigning to each element a group index such
  that the number of ordered pairs $(x,y)$ lying in a common group, i.e. with
  $\mathrm{gid}\,x=\mathrm{gid}\,y$, is at most $n\cdot s$. -/)
  (proof := /-- Fix a bijection $e:U\simeq\mathrm{Fin}\,n$ and set
  $\mathrm{gid}\,x=\lfloor e(x)/s\rfloor$, which lands in $\mathrm{Fin}\,g$ because
  $e(x)<n\le g s$.  For each group index $c$ the map $y\mapsto e(y)\bmod s$ is
  injective on the fibre $\{y:\mathrm{gid}\,y=c\}$, since an element is recovered
  from its quotient and remainder; hence each fibre has at most $s$ elements.  The
  number of common-group ordered pairs equals
  $\sum_{x}\lvert\{y:\mathrm{gid}\,y=\mathrm{gid}\,x\}\rvert\le\sum_x s=n s$. -/)
  (title := /-- A balanced grouping of a finite universe -/)
  (latexEnv := "lemma")]
lemma exists_balanced_grouping {U : Type} [Fintype U] {g s : ℕ} (hg : 0 < g)
    (hs : 0 < s) (hn : Fintype.card U ≤ g * s) :
    ∃ gid : U → Fin g,
      (Finset.univ.filter (fun p : U × U => gid p.1 = gid p.2)).card
        ≤ Fintype.card U * s := by
  classical
  set n := Fintype.card U with hnc
  set e := Fintype.equivFin U with he
  have hb : ∀ x : U, (e x).val / s < g := by
    intro x
    rw [Nat.div_lt_iff_lt_mul hs]
    exact lt_of_lt_of_le (e x).isLt hn
  set gid : U → Fin g := fun x => ⟨(e x).val / s, hb x⟩ with hgid
  refine ⟨gid, ?_⟩
  have hfiber : ∀ c : Fin g,
      (Finset.univ.filter (fun y : U => gid y = c)).card ≤ s := by
    intro c
    rw [← Finset.card_range s]
    apply Finset.card_le_card_of_injOn (fun y : U => (e y).val % s)
    · intro y _
      exact Finset.mem_coe.2 (Finset.mem_range.2 (Nat.mod_lt _ hs))
    · intro y1 hy1 y2 hy2 hmod
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hy1 hy2
      have hmod' : (e y1).val % s = (e y2).val % s := hmod
      have hdiv : (e y1).val / s = (e y2).val / s :=
        Fin.mk.inj_iff.1 (hy1.trans hy2.symm)
      have h1 := Nat.div_add_mod (e y1).val s
      have h2 := Nat.div_add_mod (e y2).val s
      rw [hdiv, hmod'] at h1
      have hval : (e y1).val = (e y2).val := by omega
      exact e.injective (Fin.ext hval)
  calc (Finset.univ.filter (fun p : U × U => gid p.1 = gid p.2)).card
        = ∑ x : U, (Finset.univ.filter (fun y : U => gid x = gid y)).card := by
          simp_rw [Finset.card_filter]
          rw [Fintype.sum_prod_type
            (f := fun p : U × U => if gid p.1 = gid p.2 then 1 else 0)]
    _ ≤ ∑ _x : U, s := by
          apply Finset.sum_le_sum
          intro x _
          refine le_trans (le_of_eq ?_) (hfiber (gid x))
          congr 1
          ext y
          simp [eq_comm]
    _ = n * s := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

@[blueprint "lem:card-quotient-meet-ker-le"
  (statement := /-- Let $U$ be finite, $\mathrm{gid}:U\to\mathrm{Fin}\,g$ and $P$
  a partition of $U$.  The number of classes of the meet
  $\ker(\mathrm{gid})\sqcap P$ is at most $g$ times the number of classes of
  $P$. -/)
  (proof := /-- Send the class of $x$ under $\ker(\mathrm{gid})\sqcap P$ to the
  pair $(\mathrm{gid}\,x,[x]_P)$.  This is well defined because two elements
  related by $\ker(\mathrm{gid})\sqcap P$ share both their group index and their
  $P$-class, and it is injective because equal images force both conjuncts,
  hence relation by the meet.  Therefore the quotient injects into
  $\mathrm{Fin}\,g\times(U/P)$, whose cardinality is $g\cdot\lvert U/P\rvert$. -/)
  (title := /-- Class count of a meet with a kernel -/)
  (latexEnv := "lemma")]
lemma card_quotient_meet_ker_le {U : Type} [Finite U] {g : ℕ} (gid : U → Fin g)
    (P : Setoid U) :
    Nat.card (Quotient (Setoid.ker gid ⊓ P)) ≤ g * Nat.card (Quotient P) := by
  classical
  set S : Setoid U := Setoid.ker gid ⊓ P with hS
  have hrel : ∀ x y : U, S.r x y ↔ (gid x = gid y ∧ P.r x y) := by
    intro x y; exact Setoid.inf_iff_and
  let f : Quotient S → Fin g × Quotient P :=
    Quotient.lift (fun x => (gid x, Quotient.mk P x)) (by
      intro a b hab
      have := (hrel a b).1 hab
      obtain ⟨h1, h2⟩ := this
      apply Prod.ext
      · exact h1
      · exact Quotient.sound h2)
  have hfinj : Function.Injective f := by
    intro x y hxy
    induction x using Quotient.ind with
    | _ a =>
      induction y using Quotient.ind with
      | _ b =>
        have h1 : gid a = gid b := congrArg Prod.fst hxy
        have h2 : Quotient.mk P a = Quotient.mk P b := congrArg Prod.snd hxy
        have h2' : P.r a b := Quotient.exact h2
        exact Quotient.sound ((hrel a b).2 ⟨h1, h2'⟩)
  calc Nat.card (Quotient S)
        ≤ Nat.card (Fin g × Quotient P) := Nat.card_le_card_of_injective f hfinj
    _ = g * Nat.card (Quotient P) := by
          rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin]

@[blueprint "lem:exists-descent-partition"
  (statement := /-- Let $Q\le P$ be partitions of $U$ with $U$ finite.  There is a
  partition $P_Q$ of the quotient $U/Q$ whose pullback along the quotient map is
  $P$, whose number of classes is at most that of $P$, and which relates two
  classes exactly when chosen representatives are $P$-equivalent. -/)
  (proof := /-- Let $\varphi:U/Q\to U/P$ send $[x]_Q\mapsto[x]_P$; this is well
  defined because $Q\le P$.  Take $P_Q=\ker\varphi$.  Its pullback along
  $[\cdot]_Q$ relates $x,y$ iff $[x]_P=[y]_P$, i.e. iff $P$ holds, so it equals
  $P$.  The lift of $\varphi$ to $U/P_Q$ is injective, so $\lvert U/P_Q\rvert\le
  \lvert U/P\rvert$.  Finally $P_Q$ relates two classes iff $\varphi$ agrees on
  them, i.e. iff their representatives are $P$-equivalent. -/)
  (title := /-- Descent of a partition to a quotient -/)
  (latexEnv := "lemma")]
lemma exists_descent_partition {U : Type} [Finite U] (Q P : Setoid U)
    (hQP : ∀ a b, Q.r a b → P.r a b) :
    ∃ PQ : Setoid (Quotient Q),
      Setoid.comap (Quotient.mk Q) PQ = P ∧
        Nat.card (Quotient PQ) ≤ Nat.card (Quotient P) ∧
        ∀ a b : Quotient Q, PQ.r a b ↔ P.r a.out b.out := by
  classical
  let φ : Quotient Q → Quotient P :=
    Quotient.lift (Quotient.mk P) (fun a b h => Quotient.sound (hQP a b h))
  have hφmk : ∀ x : U, φ (Quotient.mk Q x) = Quotient.mk P x := fun x => rfl
  refine ⟨Setoid.ker φ, ?_, ?_, ?_⟩
  · apply Setoid.ext
    intro x y
    rw [Setoid.comap_rel, Setoid.ker_def, hφmk, hφmk]
    exact Quotient.eq
  · exact Nat.card_le_card_of_injective _ (Setoid.kerLift_injective φ)
  · intro a b
    have ha : φ a = Quotient.mk P a.out := by
      conv_lhs => rw [← Quotient.out_eq a]
      exact hφmk a.out
    have hb : φ b = Quotient.mk P b.out := by
      conv_lhs => rw [← Quotient.out_eq b]
      exact hφmk b.out
    rw [Setoid.ker_def, ha, hb]
    exact Quotient.eq

@[blueprint "lem:run-grouping-round"
  (statement := /-- Let $\mathrm{gid}:U\to\mathrm{Fin}\,g$ and let $P$ be a
  partition of $U$.  Let $L$ be the list of all ordered pairs lying in a common
  group.  For an oracle representing $P$, running the single-round algorithm on
  $L$ outputs the meet $\ker(\mathrm{gid})\sqcap P$. -/)
  (proof := /-- By \cref{lem:run-pair-query-one-round} the output is the
  equivalence closure of the relation holding of $(x,y)$ when some entry of $L$
  equals $(x,y)$ and the oracle answers true.  A pair is in $L$ iff the two
  points share a group, and the oracle answers true iff they are $P$-equivalent;
  hence the generating relation is exactly ``same group and $P$-equivalent'',
  which is already an equivalence relation equal to $\ker(\mathrm{gid})\sqcap P$,
  so its closure equals it. -/)
  (title := /-- Output of the grouping round -/)
  (latexEnv := "lemma")]
lemma run_grouping_round {U : Type} [Fintype U] {g : ℕ} (gid : U → Fin g)
    (P : Setoid U) (oracle : same_set_oracle U)
    (hrep : same_set_oracle_represents P oracle) :
    run_pair_query_algorithm
        (pair_query_one_round
          ((Finset.univ.filter (fun p : U × U => gid p.1 = gid p.2)).toList)) oracle
      = Setoid.ker gid ⊓ P := by
  classical
  set L : List (same_set_query U) :=
    (Finset.univ.filter (fun p : U × U => gid p.1 = gid p.2)).toList with hL
  rw [run_pair_query_one_round]
  have hR : (fun x y => ∃ i : Fin L.length, L.get i = (x, y) ∧ oracle (L.get i) = true)
      = fun x y => (Setoid.ker gid ⊓ P).r x y := by
    funext x y
    apply propext
    constructor
    · rintro ⟨i, hi, hb⟩
      have hmem : (x, y) ∈ L := hi ▸ L.get_mem i
      rw [hL, Finset.mem_toList, Finset.mem_filter] at hmem
      rw [hi] at hb
      exact ⟨hmem.2, (hrep x y).1 hb⟩
    · intro hxy
      obtain ⟨hg1, hp1⟩ := hxy
      have hmem : (x, y) ∈ L := by
        rw [hL, Finset.mem_toList, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hg1⟩
      obtain ⟨i, hi⟩ := List.mem_iff_get.1 hmem
      exact ⟨i, hi, by rw [hi]; exact (hrep x y).2 hp1⟩
  apply Setoid.ext
  intro x y
  rw [hR]
  change Relation.EqvGen (fun x y => (Setoid.ker gid ⊓ P).r x y) x y
    ↔ (Setoid.ker gid ⊓ P).r x y
  have heq : Relation.EqvGen (fun x y => (Setoid.ker gid ⊓ P).r x y)
      = fun x y => (Setoid.ker gid ⊓ P).r x y := (Setoid.ker gid ⊓ P).iseqv.eqvGen_eq
  rw [heq]

@[blueprint "lem:sq-le-budget-of-small"
  (statement := /-- Let $r\ge 1$ and $k\ge 1$ and let $n$ be a natural number.  If
  $\tfrac14(n/k)^{1-1/(2^r-1)}\le 2$, then $n^2\le B(n,k,r)$. -/)
  (proof := /-- Writing $a=1/(2^r-1)\in(0,1]$, the hypothesis is equivalent to
  $(n/k)^{1-a}\le 8$.  Since $n^2=n^{1+a}n^{1-a}$ and $n^{1-a}=(n/k)^{1-a}k^{1-a}
  \le 8k^{1-a}$, we get $n^2\le 8n^{1+a}k^{1-a}=B(n,k,r)$; the case $n=0$ is
  immediate. -/)
  (title := /-- The quadratic budget in the base regime -/)
  (latexEnv := "lemma")]
lemma sq_le_budget_of_small {n k r : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k)
    (hsmall : (1 / 4) * ((n : ℝ) / k) ^ (1 - 1 / ((2 : ℝ) ^ r - 1)) ≤ 2) :
    (n : ℝ) ^ 2 ≤ pair_query_budget n k r := by
  unfold pair_query_budget
  set a := 1 / ((2 : ℝ) ^ r - 1) with ha
  have h2r1 : (1 : ℝ) ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num)
  have h2rr : (2 : ℝ) ^ r = ((2 ^ r : ℕ) : ℝ) := by push_cast; ring
  have h2rge : (2 : ℝ) ≤ (2 : ℝ) ^ r := by
    rw [h2rr]
    have : (2 : ℕ) ≤ 2 ^ r := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
    exact_mod_cast this
  have hden : (0 : ℝ) < (2 : ℝ) ^ r - 1 := by linarith
  have ha0 : 0 < a := by rw [ha]; exact div_pos one_pos hden
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one hden]; linarith
  have hexp1 : (0 : ℝ) ≤ 1 + a := by linarith
  have hexpm : (0 : ℝ) ≤ 1 - a := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    simp only [Nat.cast_zero]
    rw [show ((0 : ℝ) ^ 2) = 0 by norm_num]
    have hkr : (0 : ℝ) ≤ (k : ℝ) ^ (1 - a) := Real.rpow_nonneg hk0.le _
    have h0r : (0 : ℝ) ≤ (0 : ℝ) ^ (1 + a) := Real.rpow_nonneg le_rfl _
    positivity
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hsq : (n : ℝ) ^ 2 = (n : ℝ) ^ (1 + a) * (n : ℝ) ^ (1 - a) := by
      rw [← Real.rpow_add hn0, show (1 + a) + (1 - a) = (2 : ℝ) by ring,
        show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hnk : ((n : ℝ) / k) ^ (1 - a) ≤ 8 := by linarith
    have hnam : (n : ℝ) ^ (1 - a) = ((n : ℝ) / k) ^ (1 - a) * (k : ℝ) ^ (1 - a) := by
      rw [Real.div_rpow hn0.le hk0.le, div_mul_cancel₀]
      positivity
    have hkr : (0 : ℝ) ≤ (k : ℝ) ^ (1 - a) := Real.rpow_nonneg hk0.le _
    have hbound : (n : ℝ) ^ (1 - a) ≤ 8 * (k : ℝ) ^ (1 - a) := by
      rw [hnam]
      exact mul_le_mul_of_nonneg_right hnk hkr
    have hn1a : (0 : ℝ) ≤ (n : ℝ) ^ (1 + a) := Real.rpow_nonneg hn0.le _
    calc (n : ℝ) ^ 2 = (n : ℝ) ^ (1 + a) * (n : ℝ) ^ (1 - a) := hsq
      _ ≤ (n : ℝ) ^ (1 + a) * (8 * (k : ℝ) ^ (1 - a)) :=
          mul_le_mul_of_nonneg_left hbound hn1a
      _ = 8 * (n : ℝ) ^ (1 + a) * (k : ℝ) ^ (1 - a) := by ring

@[blueprint "lem:pair-query-recursion-step"
  (statement := /-- Let $U$ be finite with $k\ge 1$ and let
  $\mathrm{gid}:U\to\mathrm{Fin}\,g$ be a grouping in which the number of ordered
  common-group pairs is at most $\lvert U\rvert\cdot s$.  Suppose that for every
  finite type $V$ there is a deterministic $m$-round algorithm learning every
  $k$-partition of $V$ within budget $B(\lvert V\rvert,k,m)$.  Then there is a
  deterministic $(m+1)$-round algorithm on $U$ learning every $k$-partition of
  $U$ within budget $\lvert U\rvert\cdot s+B(g\cdot k,k,m)$. -/)
  (proof := /-- Query all common-group pairs in round one; on an oracle
  representing $P$ this outputs $\ker(\mathrm{gid})\sqcap P$ by
  \cref{lem:run-grouping-round}.  Continue with the assumed $m$-round algorithm on
  the quotient by $\ker(\mathrm{gid})\sqcap P$, transported back along the
  quotient map and a section (\cref{lem:run-pair-query-extend},
  \cref{lem:run-pair-query-transport}).  The descent partition of
  \cref{lem:exists-descent-partition} has at most $k$ classes and pulls back to
  $P$, so the whole algorithm learns $P$.  For the count,
  \cref{lem:count-pair-query-extend}, \cref{lem:count-pair-query-one-round} and
  \cref{lem:count-pair-query-transport} give total
  $\lvert U\rvert\cdot s$ plus the sub-count, which is at most $B$ of the quotient
  size; that size is at most $g\cdot k$ by
  \cref{lem:card-quotient-meet-ker-le}, and
  \cref{lem:pair-query-budget-mono-left} finishes. -/)
  (title := /-- One recursion step of the pair-query construction -/)
  (latexEnv := "lemma")]
lemma pair_query_recursion_step {U : Type} [Fintype U] {m k g s : ℕ}
    (hk : 1 ≤ k) (gid : U → Fin g)
    (hcount : (Finset.univ.filter (fun p : U × U => gid p.1 = gid p.2)).card
        ≤ Fintype.card U * s)
    (Balg : ∀ (V : Type) [Fintype V],
      ∃ B : deterministic_pair_query_algorithm V m,
        learns_k_partitions_with_budget B k (pair_query_budget (Fintype.card V) k m)) :
    ∃ A : deterministic_pair_query_algorithm U (m + 1),
      learns_k_partitions_with_budget A k
        ((Fintype.card U : ℝ) * s + pair_query_budget (g * k) k m) := by
  classical
  haveI : Finite U := inferInstance
  have Bspec : ∀ (V : Type) [Fintype V],
      learns_k_partitions_with_budget ((Balg V).choose) k
        (pair_query_budget (Fintype.card V) k m) := fun V _ => (Balg V).choose_spec
  refine ⟨pair_query_extend
    (fun Q => pair_query_transport (Quotient.mk Q) Quotient.out
      (letI : Fintype (Quotient Q) := Fintype.ofFinite (Quotient Q); (Balg (Quotient Q)).choose))
    (pair_query_one_round
      ((Finset.univ.filter (fun p : U × U => gid p.1 = gid p.2)).toList)), ?_⟩
  intro P hP
  letI instFQ1 : Fintype (Quotient (Setoid.ker gid ⊓ P)) := Fintype.ofFinite _
  obtain ⟨PQ, hcomap, hcardPQ, hrelPQ⟩ :=
    exists_descent_partition (Setoid.ker gid ⊓ P) P
      (fun a b h => (Setoid.inf_iff_and.1 h).2)
  have hPQclasses : partition_has_at_most_classes PQ k := le_trans hcardPQ hP
  have hcardQ1 : Fintype.card (Quotient (Setoid.ker gid ⊓ P)) ≤ g * k := by
    rw [← Nat.card_eq_fintype_card]
    exact le_trans (card_quotient_meet_ker_le gid P) (mul_le_mul_left' hP g)
  refine ⟨?_, ?_⟩
  · intro oracle hrep
    set oracle' : same_set_oracle (Quotient (Setoid.ker gid ⊓ P)) :=
      fun q => oracle (Quotient.out q.1, Quotient.out q.2) with horacle'
    have hrep' : same_set_oracle_represents PQ oracle' := by
      intro a b
      show oracle (Quotient.out a, Quotient.out b) = true ↔ PQ.r a b
      rw [hrep (Quotient.out a) (Quotient.out b), hrelPQ a b]
    have hrunB : run_pair_query_algorithm ((Balg (Quotient (Setoid.ker gid ⊓ P))).choose)
        oracle' = PQ :=
      ((Bspec (Quotient (Setoid.ker gid ⊓ P))) PQ hPQclasses).1 oracle' hrep'
    show run_pair_query_algorithm (pair_query_extend _ _) oracle = P
    rw [run_pair_query_extend, run_grouping_round gid P oracle hrep,
      run_pair_query_transport]
    show Setoid.comap (Quotient.mk (Setoid.ker gid ⊓ P))
        (run_pair_query_algorithm ((Balg (Quotient (Setoid.ker gid ⊓ P))).choose)
          (fun q => oracle (Quotient.out q.1, Quotient.out q.2))) = P
    rw [← horacle', hrunB]
    exact hcomap
  · intro oracle hrep
    set oracle' : same_set_oracle (Quotient (Setoid.ker gid ⊓ P)) :=
      fun q => oracle (Quotient.out q.1, Quotient.out q.2) with horacle'
    have hrep' : same_set_oracle_represents PQ oracle' := by
      intro a b
      show oracle (Quotient.out a, Quotient.out b) = true ↔ PQ.r a b
      rw [hrep (Quotient.out a) (Quotient.out b), hrelPQ a b]
    have hcnt : pair_query_count (pair_query_extend
        (fun Q => pair_query_transport (Quotient.mk Q) Quotient.out
          (letI : Fintype (Quotient Q) := Fintype.ofFinite (Quotient Q); (Balg (Quotient Q)).choose))
        (pair_query_one_round
          ((Finset.univ.filter (fun p : U × U => gid p.1 = gid p.2)).toList))) oracle
        = (Finset.univ.filter (fun p : U × U => gid p.1 = gid p.2)).toList.length
          + pair_query_count ((Balg (Quotient (Setoid.ker gid ⊓ P))).choose) oracle' := by
      rw [count_pair_query_extend, run_grouping_round gid P oracle hrep,
        count_pair_query_one_round]
      show _ + pair_query_count (pair_query_transport (Quotient.mk (Setoid.ker gid ⊓ P))
          Quotient.out ((Balg (Quotient (Setoid.ker gid ⊓ P))).choose)) oracle = _
      rw [count_pair_query_transport, ← horacle']
    show (pair_query_count (pair_query_extend _ _) oracle : ℝ) ≤ _
    rw [hcnt]
    have hL1 : ((Finset.univ.filter (fun p : U × U => gid p.1 = gid p.2)).toList.length : ℝ)
        ≤ (Fintype.card U : ℝ) * s := by
      rw [Finset.length_toList]
      calc ((Finset.univ.filter (fun p : U × U => gid p.1 = gid p.2)).card : ℝ)
          ≤ ((Fintype.card U * s : ℕ) : ℝ) := by exact_mod_cast hcount
        _ = (Fintype.card U : ℝ) * s := by push_cast; ring
    have hL2 : (pair_query_count ((Balg (Quotient (Setoid.ker gid ⊓ P))).choose) oracle' : ℝ)
        ≤ pair_query_budget (g * k) k m := by
      have hb := ((Bspec (Quotient (Setoid.ker gid ⊓ P))) PQ hPQclasses).2 oracle' hrep'
      exact le_trans hb (pair_query_budget_mono_left hcardQ1 k m)
    push_cast
    linarith [hL1, hL2]

@[blueprint "lem:main-pair-query-recursion"
  (statement := /-- For every $r\ge 1$, every $k\ge 1$ and every finite universe
  $U$, there is a deterministic $r$-round pair-query algorithm on $U$ that learns
  every partition of $U$ into at most $k$ classes within budget
  $B(\lvert U\rvert,k,r)$. -/)
  (proof := /-- Induct on $r$.  If $\tfrac14(\lvert U\rvert/k)^{1-1/(2^r-1)}\le 2$
  then $\lvert U\rvert^2\le B$ by \cref{lem:sq-le-budget-of-small}, and the
  all-pairs algorithm suffices by \cref{lem:all-pairs-within-budget}.  Otherwise
  $r\ge 2$; choose $g=\lceil\tfrac14(\lvert U\rvert/k)^{1-1/(2^r-1)}\rceil$ groups
  and block size $s=\lceil\lvert U\rvert/g\rceil$, pick a balanced grouping by
  \cref{lem:exists-balanced-grouping}, and apply one recursion step
  \cref{lem:pair-query-recursion-step} with the inductive hypothesis on quotients.
  This yields an algorithm within budget $\lvert U\rvert\cdot s+B(gk,k,r-1)$; the
  chosen $g$ and $s$ satisfy the hypotheses of \cref{lem:budget-step-arith}, whose
  conclusion bounds this quantity by $B(\lvert U\rvert,k,r)$. -/)
  (title := /-- The recursive pair-query construction -/)
  (latexEnv := "lemma")]
lemma main_pair_query_recursion :
    ∀ (r : ℕ), 1 ≤ r → ∀ (k : ℕ), 1 ≤ k → ∀ (U : Type) [Fintype U],
      ∃ A : deterministic_pair_query_algorithm U r,
        learns_k_partitions_with_budget A k (pair_query_budget (Fintype.card U) k r) := by
  intro r
  induction r with
  | zero => intro h; omega
  | succ m ih =>
    intro _ k hk U _
    classical
    set n := Fintype.card U with hnc
    set a : ℝ := 1 / ((2 : ℝ) ^ (m + 1) - 1) with ha
    by_cases hg0le : (1 / 4) * ((n : ℝ) / k) ^ (1 - a) ≤ 2
    · refine all_pairs_within_budget (by omega) _ ?_
      exact sq_le_budget_of_small (by omega) hk hg0le
    · have hg0gt : (2 : ℝ) < (1 / 4) * ((n : ℝ) / k) ^ (1 - a) := not_le.1 hg0le
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h0 | h
        · exfalso; apply hg0le
          have haeq : a = 1 := by rw [ha, h0]; norm_num
          rw [haeq, sub_self, Real.rpow_zero]; norm_num
        · exact h
      have htge : (2 : ℝ) ≤ (2 : ℝ) ^ m := by
        calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
          _ ≤ (2 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hm1
      have hpow_succ : (2 : ℝ) ^ (m + 1) = 2 * (2 : ℝ) ^ m := by rw [pow_succ]; ring
      have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by rw [hpow_succ]; linarith
      have hda : (0 : ℝ) < (2 : ℝ) ^ (m + 1) - 1 := by linarith
      have ha0 : 0 < a := by rw [ha]; exact div_pos one_pos hda
      have ha1 : a < 1 := by rw [ha, div_lt_one hda]; linarith
      have hdb : (0 : ℝ) < (2 : ℝ) ^ m - 1 := by linarith
      set b : ℝ := 1 / ((2 : ℝ) ^ m - 1) with hb
      have hb0 : 0 ≤ b := by rw [hb]; exact le_of_lt (div_pos one_pos hdb)
      have hid : (1 - a) * (1 + b) = 1 + a := by
        rw [ha, hb, hpow_succ]
        have h1 : (2 : ℝ) ^ m - 1 ≠ 0 := ne_of_gt hdb
        have h2 : 2 * (2 : ℝ) ^ m - 1 ≠ 0 := by
          have : (0 : ℝ) < 2 * (2 : ℝ) ^ m - 1 := by linarith
          exact ne_of_gt this
        field_simp
        ring
      have hnpos : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h0 | h
        · exfalso; apply hg0le
          rw [h0]
          simp only [Nat.cast_zero, zero_div]
          rw [Real.zero_rpow (show (0 : ℝ) < 1 - a by linarith).ne']
          norm_num
        · exact h
      have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
      set g : ℕ := ⌈(1 / 4) * ((n : ℝ) / k) ^ (1 - a)⌉₊ with hgdef
      set s : ℕ := ⌈(n : ℝ) / g⌉₊ with hsdef
      have hg0nonneg : (0 : ℝ) ≤ (1 / 4) * ((n : ℝ) / k) ^ (1 - a) := by positivity
      have hg1 : (2 : ℝ) < (g : ℝ) := by
        rw [hgdef]; exact lt_of_lt_of_le hg0gt (Nat.le_ceil _)
      have hgr : (0 : ℝ) < (g : ℝ) := by linarith
      have hgpos : 0 < g := by exact_mod_cast hgr
      have hspos : 0 < s := by
        rw [hsdef]; exact Nat.ceil_pos.2 (div_pos hnr hgr)
      have hsr' : (n : ℝ) / (g : ℝ) ≤ (s : ℝ) := by rw [hsdef]; exact Nat.le_ceil _
      have hnle : n ≤ g * s := by
        have h := (div_le_iff₀ hgr).1 hsr'
        have hcast : (n : ℝ) ≤ ((g * s : ℕ) : ℝ) := by
          push_cast; linarith [h, mul_comm (s : ℝ) (g : ℝ)]
        exact_mod_cast hcast
      obtain ⟨gid, hgcount⟩ := exists_balanced_grouping (g := g) (s := s) hgpos hspos hnle
      obtain ⟨A, hA⟩ := pair_query_recursion_step (m := m) (k := k) (g := g) (s := s)
        hk gid hgcount (fun V _ => ih hm1 k hk V)
      refine ⟨A, fun P hP => ⟨(hA P hP).1, fun oracle hrep =>
        le_trans ((hA P hP).2 oracle hrep) ?_⟩⟩
      have hpow : ∀ x y : ℝ, Real.rpow x y = x ^ y := fun _ _ => rfl
      simp only [pair_query_budget, hpow]
      rw [← ha, ← hb]
      push_cast
      have hgr_lo : (1 / 4) * ((n : ℝ) / k) ^ (1 - a) ≤ (g : ℝ) := by
        rw [hgdef]; exact Nat.le_ceil _
      have hgr_hi : (g : ℝ) ≤ (1 / 4) * ((n : ℝ) / k) ^ (1 - a) + 1 := by
        rw [hgdef]; exact le_of_lt (Nat.ceil_lt_add_one hg0nonneg)
      have hsr : (s : ℝ) ≤ (n : ℝ) / (g : ℝ) + 1 := by
        rw [hsdef]; exact le_of_lt (Nat.ceil_lt_add_one (le_of_lt (div_pos hnr hgr)))
      have key := budget_step_arith a b ha0 ha1 hb0 hid (n : ℝ) (k : ℝ) (g : ℝ) (s : ℝ)
        ((1 / 4) * ((n : ℝ) / k) ^ (1 - a)) hk' hn' rfl hg0gt hgr_lo hgr_hi hsr
      linarith [key, mul_comm (n : ℝ) (s : ℝ)]

@[blueprint "lem:asserted-pair-query-upper-bound"
  (statement := /-- Let $r,k\geq 1$, and let $U$ be a finite universe of
  cardinality $n$.  There exists a deterministic $r$-round pair-query algorithm
  on $U$ which learns every partition of $U$ into at most $k$ classes and whose
  number of queries, on every oracle path representing such a partition, is at
  most
  \[
    8n^{1+1/(2^r-1)}k^{1-1/(2^r-1)}.
  \] -/)
  (proof := /-- This is exactly the conclusion of the recursive construction
  \cref{lem:main-pair-query-recursion}, instantiated at the given positive
  integers $r$ and $k$ and the given finite universe $U$. -/)
  (title := /-- Pair-query upper bound (existence of the algorithm) -/)
  (latexEnv := "lemma")]
lemma asserted_pair_query_upper_bound (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k)
    (U : Type) [Fintype U] :
    ∃ algorithm : deterministic_pair_query_algorithm U r,
      learns_k_partitions_with_budget algorithm k
        (pair_query_budget (Fintype.card U) k r) := by
  exact main_pair_query_recursion r hr k hk U

@[blueprint "thm:pair-query-upper-bound"
  (statement := /-- For every pair of integers $r,k\geq 1$ and every finite
  universe $U$ of cardinality $n$, there exists a deterministic $r$-round
  algorithm which learns every partition of $U$ into at most $k$ classes using,
  on every corresponding oracle path, at most
  \[
    8n^{1+1/(2^r-1)}k^{1-1/(2^r-1)}
  \]
  pairwise same-set queries. -/)
  (proof := /-- Apply the existence assertion isolated in
  \cref{lem:asserted-pair-query-upper-bound} with the given positive integers
  $r$ and $k$ and the given finite universe $U$. -/)
  (title := /-- Pair-query upper bound -/)
  (latexEnv := "theorem")]
theorem pair_query_upper_bound (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k)
    (U : Type) [Fintype U] :
    ∃ algorithm : deterministic_pair_query_algorithm U r,
      learns_k_partitions_with_budget algorithm k
        (pair_query_budget (Fintype.card U) k r) := by
  exact asserted_pair_query_upper_bound r k hr hk U

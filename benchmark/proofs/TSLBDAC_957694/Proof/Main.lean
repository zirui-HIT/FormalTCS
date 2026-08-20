import Architect
import Mathlib.RingTheory.Binomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:ROBP"
  (statement := /-- Let $k \ge 2$, $n \ge 1$ and $w \ge 1$ be integers. A \emph{length-$n$
    width-$w$ read-once branching program} (ROBP) over the alphabet $[k]$ consists of a
    directed layered multigraph with $n+1$ layers $V_0, \dots, V_n$, in which $V_0$ is a
    single start vertex, every non-terminal vertex has exactly $|[k]| = k$ outgoing edges
    labelled by the distinct alphabet symbols, every terminal vertex carries an output
    label, and every layer contains at most $w$ vertices. We represent such a program by
    fixing the common vertex set $\mathrm{Fin}\ w$ for all layers: the field `start` is the
    unique vertex of $V_0$, the field `step t v a` is the endpoint in layer $V_{t+1}$ of the
    edge leaving the vertex $v \in V_t$ labelled by the symbol $a \in [k]$, and the field
    `out` assigns to each vertex of the terminal layer $V_n$ its output label, which for the
    $k$-counter approximate counting problem is a $k$-tuple of real numbers. Fixing the
    vertex set to $\mathrm{Fin}\ w$ in every layer is exactly the width-$w$ restriction,
    since a layer with fewer than $w$ vertices is obtained by leaving vertices
    unreachable. -/)
  (title := /-- Read-Once Branching Program of Length $n$ and Width $w$ -/)
  (latexEnv := "definition")]
structure ROBP (k n w : ℕ) where
  start : Fin w
  step : Fin n → Fin w → Fin k → Fin w
  out : Fin w → Fin k → ℝ

@[blueprint "def:ROBP-run"
  (statement := /-- Let $k \ge 2$, $n \ge 1$ and $w \ge 1$ be integers, let $P$ be a
    length-$n$ width-$w$ ROBP over $[k]$ as in \cref{def:ROBP}, and let $x \in [k]^n$ be an
    input. The \emph{terminal vertex reached by $P$ on $x$} is the vertex
    $v_n \in V_n$ determined by $v_0 = \mathrm{start}$ and
    $v_{t+1} = \mathrm{step}\ t\ v_t\ x_t$ for every $t$ with $0 \le t \le n-1$; that is, the
    computation starts at the start vertex and, having read the symbol $x_t$ in layer $V_t$,
    follows the outgoing edge of $v_t$ labelled $x_t$ into layer $V_{t+1}$. Since each input
    symbol is read exactly once and in order, this is the read-once computation of $P$
    on $x$. -/)
  (title := /-- The Terminal Vertex Reached by a Read-Once Branching Program -/)
  (latexEnv := "definition")]
def ROBP_run {k n w : ℕ} (P : ROBP k n w) (x : Fin n → Fin k) : Fin w :=
  Fin.foldl n (fun v t => P.step t v (x t)) P.start

@[blueprint "def:symbol-count"
  (statement := /-- Let $k \ge 2$ and $n \ge 1$ be integers, let $x \in [k]^n$ be an input
    and let $j \in [k]$ be an alphabet symbol. The \emph{multiplicity of $j$ in $x$} is the
    cardinality $\#\{i \in [n] : x_i = j\}$ of the set of positions of $x$ carrying the
    symbol $j$. This is the exact quantity that the $j$-th counter of the $k$-counter
    approximate counting problem is required to estimate. -/)
  (title := /-- Multiplicity of an Alphabet Symbol in an Input String -/)
  (latexEnv := "definition")]
def symbol_count {k n : ℕ} (x : Fin n → Fin k) (j : Fin k) : ℕ :=
  (Finset.univ.filter fun i : Fin n => x i = j).card

@[blueprint "def:computes-approx-count"
  (statement := /-- Let $k \ge 2$ and $n \ge 1$ be integers, let $w \ge 1$ be an integer, let
    $\Delta \ge 0$ be a real number and let $P$ be a length-$n$ width-$w$ ROBP over $[k]$ as
    in \cref{def:ROBP}. We say that $P$ \emph{computes}
    $\mathrm{ApproxCount}_{k\text{-}\mathrm{counter}}[n,\Delta]$ if for every input
    $x \in [k]^n$ the output $P(x) = (\hat S_1, \dots, \hat S_k)$ of $P$ on $x$, namely the
    output label of the terminal vertex reached by $P$ on $x$ in the sense of
    \cref{def:ROBP-run}, is a \emph{valid output} for $x$: for every $j \in [k]$,
    $$\left| \hat S_j - \#\{i \in [n] : x_i = j\} \right| \le \Delta,$$
    where $\#\{i \in [n] : x_i = j\}$ is the multiplicity of $j$ in $x$ in the sense of
    \cref{def:symbol-count}. Thus every one of the $k$ counters must be correct up to the
    additive error $\Delta$, simultaneously and on every input. -/)
  (title := /-- Computing $k$-Counter Approximate Counting Within Additive Error $\Delta$ -/)
  (latexEnv := "definition")]
def computes_approx_count {k n w : ℕ} (P : ROBP k n w) (Δ : ℝ) : Prop :=
  ∀ x : Fin n → Fin k, ∀ j : Fin k,
    |P.out (ROBP_run P x) j - (symbol_count x j : ℝ)| ≤ Δ

@[blueprint "lem:k-counter-choose-sum-range"
  (statement := /-- Let $k \ge 1$ be an integer and let $N$ be a nonnegative integer. Then
    $$\sum_{t=0}^{N-1} \binom{t+k-1}{k-1} = \binom{N+k-1}{k},$$
    an identity of real numbers, where the empty sum for $N = 0$ is $0$. -/)
  (proof := /-- Write $k = K+1$ with $K = k-1 \ge 0$, so that $t+k-1 = t+K$ for every
    nonnegative integer $t$, and $N+k-1 = N+K$ and $k = K+1$. It suffices to prove the
    identity
    $$\sum_{t=0}^{N-1} \binom{t+K}{K} = \binom{N+K}{K+1}$$
    between nonnegative integers, since the asserted identity of real numbers is obtained
    from it by applying the ring homomorphism from the integers to the reals, which commutes
    with finite sums. We distinguish two cases. If $N = 0$, the left-hand side is the empty
    sum, hence $0$, and the right-hand side is $\binom{K}{K+1} = 0$ because $K < K+1$. If
    $N = M+1$ for a nonnegative integer $M$, then Zhu Shijie's hockey-stick identity in the
    form $\sum_{t=0}^{M} \binom{t+K}{K} = \binom{M+K+1}{K+1}$ gives the claim, since
    $N+K = M+1+K = M+K+1$. -/)
  (title := /-- Hockey-Stick Evaluation of a Partial Sum of Binomial Coefficients -/)
  (latexEnv := "lemma")]
lemma k_counter_choose_sum_range (k N : ℕ) (hk : 1 ≤ k) :
    ∑ t ∈ Finset.range N, (Nat.choose (t + k - 1) (k - 1) : ℝ)
      = (Nat.choose (N + k - 1) k : ℝ) := by
  obtain ⟨K, rfl⟩ : ∃ K : ℕ, k = K + 1 := ⟨k - 1, by omega⟩
  have e1 : ∀ t : ℕ, t + (K + 1) - 1 = t + K := by
    intro t
    omega
  have hnat : ∑ t ∈ Finset.range N, Nat.choose (t + K) K = Nat.choose (N + K) (K + 1) := by
    cases N with
    | zero => simp [Nat.choose_eq_zero_of_lt]
    | succ M =>
      have e2 : M + 1 + K = M + K + 1 := by omega
      rw [e2]
      exact Nat.sum_range_add_choose M K
  simp only [e1, Nat.add_sub_cancel]
  exact_mod_cast hnat

@[blueprint "lem:k-counter-choose-threshold"
  (statement := /-- Let $k$, $n$, $w$ and $m$ be nonnegative integers, where every difference
    of nonnegative integers below denotes truncated subtraction. Assume that
    $\binom{m+k-1}{k-1} \le w$ and that every nonnegative integer $m'$ with $m' \le n-1$ and
    $\binom{m'+k-1}{k-1} \le w$ satisfies $m' \le m$. Then for every nonnegative integer $t$
    with $t < n$ we have $\binom{t+k-1}{k-1} \le w$ if and only if $t \le m$. -/)
  (proof := /-- Let $t$ be a nonnegative integer with $t < n$; we prove the two implications
    separately. Assume first that $\binom{t+k-1}{k-1} \le w$. Since $t < n$ we have
    $t \le n-1$, so the maximality hypothesis applied to $m' = t$ yields $t \le m$. Assume
    conversely that $t \le m$. Then $t+k-1 \le m+k-1$, so the monotonicity of the binomial
    coefficient $a \mapsto \binom{a}{k-1}$ in its upper argument gives
    $\binom{t+k-1}{k-1} \le \binom{m+k-1}{k-1}$, and the hypothesis
    $\binom{m+k-1}{k-1} \le w$ gives $\binom{t+k-1}{k-1} \le w$ by transitivity. -/)
  (title := /-- Characterization of the Indices Whose Binomial Coefficient Does Not Exceed the Width -/)
  (latexEnv := "lemma")]
lemma k_counter_choose_threshold (k n w m : ℕ) (hmw : Nat.choose (m + k - 1) (k - 1) ≤ w)
    (hmax : ∀ m' : ℕ, m' ≤ n - 1 → Nat.choose (m' + k - 1) (k - 1) ≤ w → m' ≤ m)
    (t : ℕ) (ht : t < n) :
    Nat.choose (t + k - 1) (k - 1) ≤ w ↔ t ≤ m := by
  constructor
  · intro h
    exact hmax t (by omega) h
  · intro h
    exact le_trans (Nat.choose_le_choose (k - 1) (by omega)) hmw

@[blueprint "lem:k-counter-truncated-sum"
  (statement := /-- Let $k \ge 2$, $n \ge 1$ and $w \ge 1$ be integers, and let $m$ be a
    nonnegative integer such that $m \le n-1$, such that $\binom{m+k-1}{k-1} \le w$, and such
    that every nonnegative integer $m'$ with $m' \le n-1$ and $\binom{m'+k-1}{k-1} \le w$
    satisfies $m' \le m$; that is, $m$ is the largest nonnegative integer with $m \le n-1$
    and $\binom{m+k-1}{k-1} \le w$. Then
    $$\sum_{t=0}^{n-1} \max\left(0, \binom{t+k-1}{k-1} - w\right)
      = \binom{n+k-1}{k} - \binom{m+k}{k} - (n-m-1)w.$$ -/)
  (proof := /-- Since $m \le n-1$ and $n \ge 1$, we have $m+1 \le n$, so the index set
    $\{0, 1, \dots, n-1\}$ is the disjoint union of $\{0, 1, \dots, m\}$ and
    $\{m+1, \dots, n-1\}$, and the sum splits accordingly as
    $$\sum_{t=0}^{n-1} \max\left(0, \binom{t+k-1}{k-1} - w\right)
      = \sum_{t=0}^{m} \max\left(0, \binom{t+k-1}{k-1} - w\right)
        + \sum_{t=m+1}^{n-1} \max\left(0, \binom{t+k-1}{k-1} - w\right).$$
    We evaluate the two partial sums separately, using throughout the criterion of
    \cref{lem:k-counter-choose-threshold}: for every integer $t$ with $0 \le t < n$ we have
    $\binom{t+k-1}{k-1} \le w$ if and only if $t \le m$.

    First, let $t$ be an integer with $0 \le t \le m$. Then $t < n$, since $m+1 \le n$, so
    \cref{lem:k-counter-choose-threshold} gives $\binom{t+k-1}{k-1} \le w$ and hence
    $\binom{t+k-1}{k-1} - w \le 0$, so that
    $\max\left(0, \binom{t+k-1}{k-1} - w\right) = 0$. Consequently the first partial sum
    vanishes.

    Second, let $t$ be an integer with $m+1 \le t \le n-1$. If we had
    $\binom{t+k-1}{k-1} \le w$, then \cref{lem:k-counter-choose-threshold}, applicable since
    $t < n$, would give $t \le m$, contradicting $t \ge m+1$; hence
    $w < \binom{t+k-1}{k-1}$ and therefore
    $\max\left(0, \binom{t+k-1}{k-1} - w\right) = \binom{t+k-1}{k-1} - w$. Splitting the
    resulting sum of differences into a difference of sums, we obtain
    $$\sum_{t=m+1}^{n-1} \max\left(0, \binom{t+k-1}{k-1} - w\right)
      = \sum_{t=m+1}^{n-1} \binom{t+k-1}{k-1} - \sum_{t=m+1}^{n-1} w.$$
    The second sum on the right is a sum of the constant $w$ over an index set of cardinality
    $n-(m+1)$, which equals $(n-m-1)w$ because $m+1 \le n$ makes the cast of the truncated
    difference $n-(m+1)$ to the reals equal to $n-m-1$.

    It remains to evaluate $\sum_{t=m+1}^{n-1} \binom{t+k-1}{k-1}$. By
    \cref{lem:k-counter-choose-sum-range}, applied with $N = n$ and with $N = m+1$ and using
    $k \ge 1$, we have $\sum_{t=0}^{n-1} \binom{t+k-1}{k-1} = \binom{n+k-1}{k}$ and
    $\sum_{t=0}^{m} \binom{t+k-1}{k-1} = \binom{m+1+k-1}{k} = \binom{m+k}{k}$. Splitting
    $\sum_{t=0}^{n-1} \binom{t+k-1}{k-1}$ at $m+1$, which is legitimate because $m+1 \le n$,
    gives
    $$\sum_{t=m+1}^{n-1} \binom{t+k-1}{k-1}
      = \sum_{t=0}^{n-1} \binom{t+k-1}{k-1} - \sum_{t=0}^{m} \binom{t+k-1}{k-1}
      = \binom{n+k-1}{k} - \binom{m+k}{k}.$$
    Substituting the three evaluations into the splitting of the original sum yields
    $$\sum_{t=0}^{n-1} \max\left(0, \binom{t+k-1}{k-1} - w\right)
      = 0 + \left(\binom{n+k-1}{k} - \binom{m+k}{k}\right) - (n-m-1)w,$$
    which is the asserted identity. -/)
  (title := /-- Evaluation of the Truncated Binomial Sum -/)
  (latexEnv := "lemma")]
lemma k_counter_truncated_sum (k n w m : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n) (hw : 1 ≤ w)
    (hmn : m ≤ n - 1) (hmw : Nat.choose (m + k - 1) (k - 1) ≤ w)
    (hmax : ∀ m' : ℕ, m' ≤ n - 1 → Nat.choose (m' + k - 1) (k - 1) ≤ w → m' ≤ m) :
    ∑ t ∈ Finset.range n, max (0 : ℝ) ((Nat.choose (t + k - 1) (k - 1) : ℝ) - w)
      = (Nat.choose (n + k - 1) k : ℝ) - (Nat.choose (m + k) k : ℝ)
        - ((n : ℝ) - m - 1) * w := by
  have hmn' : m + 1 ≤ n := by omega
  have hzero : ∑ t ∈ Finset.range (m + 1),
      max (0 : ℝ) ((Nat.choose (t + k - 1) (k - 1) : ℝ) - w) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro t ht
    have htm : t ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    have htn : t < n := by omega
    have hle : Nat.choose (t + k - 1) (k - 1) ≤ w :=
      (k_counter_choose_threshold k n w m hmw hmax t htn).mpr htm
    have hle' : (Nat.choose (t + k - 1) (k - 1) : ℝ) ≤ (w : ℝ) := by exact_mod_cast hle
    exact max_eq_left (by linarith)
  have hrest : ∑ t ∈ Finset.Ico (m + 1) n,
      max (0 : ℝ) ((Nat.choose (t + k - 1) (k - 1) : ℝ) - w)
      = ∑ t ∈ Finset.Ico (m + 1) n, ((Nat.choose (t + k - 1) (k - 1) : ℝ) - w) := by
    refine Finset.sum_congr rfl ?_
    intro t ht
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp ht
    have hgt : w < Nat.choose (t + k - 1) (k - 1) := by
      by_contra hcon
      have := (k_counter_choose_threshold k n w m hmw hmax t h2).mp (not_lt.mp hcon)
      omega
    have hgt' : (w : ℝ) ≤ (Nat.choose (t + k - 1) (k - 1) : ℝ) := by exact_mod_cast hgt.le
    exact max_eq_right (by linarith)
  have hcard : ∑ _t ∈ Finset.Ico (m + 1) n, (w : ℝ) = ((n : ℝ) - m - 1) * w := by
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have : ((n - (m + 1) : ℕ) : ℝ) = (n : ℝ) - m - 1 := by
      have := Nat.cast_sub (R := ℝ) hmn'
      push_cast at this ⊢
      linarith
    rw [this]
  have hIco : ∑ t ∈ Finset.Ico (m + 1) n, (Nat.choose (t + k - 1) (k - 1) : ℝ)
      = (Nat.choose (n + k - 1) k : ℝ) - (Nat.choose (m + k) k : ℝ) := by
    have h1 := k_counter_choose_sum_range k n (by omega)
    have h2 := k_counter_choose_sum_range k (m + 1) (by omega)
    have h3 := Finset.sum_range_add_sum_Ico
      (fun t => (Nat.choose (t + k - 1) (k - 1) : ℝ)) hmn'
    have e : m + 1 + k - 1 = m + k := by omega
    rw [e] at h2
    linarith
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun t => max (0 : ℝ) ((Nat.choose (t + k - 1) (k - 1) : ℝ) - w)) hmn'
  rw [← hsplit, hzero, hrest, Finset.sum_sub_distrib, hIco, hcard]
  ring

@[blueprint "lem:k-counter-potential-bound"
  (statement := /-- Let $k \ge 2$, $n \ge 1$ and $w \ge 1$ be integers, let $\Delta$ be a real
    number with $0 \le \Delta \le \frac{n}{2(k-1)}$, and suppose that there exists a length-$n$
    width-$w$ ROBP $P$ over the alphabet $[k]$, in the sense of \cref{def:ROBP}, such that $P$
    computes $\mathrm{ApproxCount}_{k\text{-}\mathrm{counter}}[n,\Delta]$ in the sense of
    \cref{def:computes-approx-count}. Then
    $$\binom{n+k-1}{k} - \binom{n-2(k-1)\Delta+k-1}{k}
      \ge \sum_{t=0}^{n-1} \max\left(0, \binom{t+k-1}{k-1} - w\right),$$
    where $\binom{n-2(k-1)\Delta+k-1}{k}$ denotes the generalized binomial coefficient with
    real upper argument. -/)
  (proof := /-- Fix a program $P$ witnessing the hypothesis. For each $t\le n$ and each state
    $v$ reachable after $t$ symbols in the sense of \cref{def:ROBP-run}, define its
    \emph{anchor} $A_{t,v}$ by taking, in each alphabet coordinate, the minimum multiplicity
    from \cref{def:symbol-count} among all length-$t$ inputs reaching $v$. Thus $A_{t,v}$ is
    contained in the count multiset of every such input. If the edge labelled $j$ leads from
    $v$ to $v'$, appending $j$ to an input attaining each coordinate minimum at $v$ shows that
    $$A_{t+1,v'}\le A_{t,v}+\{j\}.$$

    Put $N=n-2(k-1)\Delta$. For a terminal state $v$, choose an input $x$ reaching $v$ that
    attains the minimum multiplicity in one fixed coordinate $j_0$. For each $j\ne j_0$, choose
    an input $y_j$ reaching $v$ that attains the minimum in coordinate $j$. The outputs on
    $x$ and $y_j$ agree, so the correctness condition in \cref{def:computes-approx-count}
    gives $\#_j(x)\le \#_j(y_j)+2\Delta$. Summing over the $k-1$ coordinates distinct from
    $j_0$ yields $|A_{n,v}|\ge N$.

    Conversely, every multiset $b$ on $[k]$ with $|b|<N$ occurs as an anchor before time $n$.
    Read any ordering of $b$; the resulting anchor is contained in $b$. While the anchor is
    not equal to $b$, append a symbol whose anchor multiplicity is deficient. The transition
    inequality keeps each subsequent anchor contained in $b$. If equality never occurred,
    the terminal anchor would have cardinality at most $|b|<N$, contradicting the terminal
    bound. Hence these multisets inject into reachable state--time pairs by choosing one such
    occurrence.

    Let $q=\lceil N\rceil$, and let $m$ be the largest integer with $m\le n-1$ and
    $\binom{m+k-1}{k-1}\le w$. Split the multisets of cardinality less than $q$ according as
    their cardinality is at most $m$ or at least $m+1$. Stars and bars counts the first class
    by $\binom{m+k}{k}$. For the second class, the chosen occurrence has time at least $m+1$;
    its time offset and program state therefore inject this class into
    $[n-m-1]\times[w]$. Consequently
    $$\binom{q+k-1}{k}\le \binom{m+k}{k}+(n-m-1)w.$$
    Since $0\le N\le q$, comparison of the nonnegative factors in the falling-factorial
    formula gives $\binom{N+k-1}{k}\le\binom{q+k-1}{k}$. Finally,
    \cref{lem:k-counter-truncated-sum} identifies the sum in the conclusion with
    $\binom{n+k-1}{k}-\binom{m+k}{k}-(n-m-1)w$. Substitution and rearrangement yield the
    asserted inequality. -/)
  (title := /-- Potential Bound for Programs Computing $k$-Counter Approximate Counting -/)
  (latexEnv := "lemma")]
lemma k_counter_potential_bound (k n w : ℕ) (Δ : ℝ) (hk : 2 ≤ k) (hn : 1 ≤ n) (hw : 1 ≤ w)
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ (n : ℝ) / (2 * ((k : ℝ) - 1)))
    (hP : ∃ P : ROBP k n w, computes_approx_count P Δ) :
    (Nat.choose (n + k - 1) k : ℝ)
        - Ring.choose ((n : ℝ) - 2 * ((k : ℝ) - 1) * Δ + (k : ℝ) - 1) k
      ≥ ∑ t ∈ Finset.range n, max (0 : ℝ) ((Nat.choose (t + k - 1) (k - 1) : ℝ) - w) := by
  classical
  rcases hP with ⟨P, hP⟩
  let run (t : ℕ) (ht : t ≤ n) (x : Fin t → Fin k) : Fin w :=
    Fin.foldl t
      (fun v i => P.step ⟨i, lt_of_lt_of_le i.isLt ht⟩ v (x i)) P.start
  let hist (t : ℕ) (x : Fin t → Fin k) : Multiset (Fin k) := (List.ofFn x : List (Fin k))
  have hist_card (t : ℕ) (x : Fin t → Fin k) : (hist t x).card = t := by
    simp [hist]
  have hist_count (t : ℕ) (x : Fin t → Fin k) (j : Fin k) :
      (hist t x).count j = symbol_count x j := by
    simpa [hist, symbol_count] using
      (Fin.card_filter_univ_eq_vector_get_eq_count j (List.Vector.ofFn x)).symm
  have run_snoc (t : ℕ) (ht : t < n) (x : Fin t → Fin k) (j : Fin k) :
      run (t + 1) (Nat.succ_le_iff.mpr ht) (Fin.lastCases j x) =
        P.step ⟨t, ht⟩ (run t ht.le x) j := by
    simp [run, Fin.foldl_succ_last]
  let Reach (t : ℕ) (ht : t ≤ n) :=
    {v : Fin w // ∃ x : Fin t → Fin k, run t ht x = v}
  let inputs (t : ℕ) (ht : t ≤ n) (v : Reach t ht) : Finset (Fin t → Fin k) :=
    Finset.univ.filter fun x => run t ht x = v
  have inputs_nonempty (t : ℕ) (ht : t ≤ n) (v : Reach t ht) :
      (inputs t ht v).Nonempty := by
    rcases v.property with ⟨x, hx⟩
    exact ⟨x, by simp [inputs, hx]⟩
  let minCount (t : ℕ) (ht : t ≤ n) (v : Reach t ht) (j : Fin k) : ℕ :=
    ((inputs t ht v).image fun x => symbol_count x j).min'
      ((inputs_nonempty t ht v).image _)
  have minCount_le (t : ℕ) (ht : t ≤ n) (v : Reach t ht) (j : Fin k)
      (x : Fin t → Fin k) (hx : run t ht x = v) :
      minCount t ht v j ≤ symbol_count x j := by
    apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨x, by simp [inputs, hx], rfl⟩
  have minCount_attained (t : ℕ) (ht : t ≤ n) (v : Reach t ht) (j : Fin k) :
      ∃ x : Fin t → Fin k, run t ht x = v ∧ symbol_count x j = minCount t ht v j := by
    have hmem := Finset.min'_mem
      ((inputs t ht v).image fun x => symbol_count x j)
      ((inputs_nonempty t ht v).image fun x => symbol_count x j)
    rcases Finset.mem_image.mp hmem with ⟨x, hx, hcount⟩
    exact ⟨x, (Finset.mem_filter.mp hx).2, hcount⟩
  let anchor (t : ℕ) (ht : t ≤ n) (v : Reach t ht) : Multiset (Fin k) :=
    ∑ j : Fin k, Multiset.replicate (minCount t ht v j) j
  have anchor_count (t : ℕ) (ht : t ≤ n) (v : Reach t ht) (j : Fin k) :
      (anchor t ht v).count j = minCount t ht v j := by
    simpa only [anchor, Multiset.count_sum', Multiset.count_replicate,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have anchor_card (t : ℕ) (ht : t ≤ n) (v : Reach t ht) :
      (anchor t ht v).card = ∑ j : Fin k, minCount t ht v j := by
    simp [anchor]
  have anchor_le_hist (t : ℕ) (ht : t ≤ n) (v : Reach t ht)
      (x : Fin t → Fin k) (hx : run t ht x = v) : anchor t ht v ≤ hist t x := by
    rw [Multiset.le_iff_count]
    intro j
    rw [anchor_count t ht v j, hist_count t x j]
    exact minCount_le t ht v j x hx
  have anchor_card_le (t : ℕ) (ht : t ≤ n) (v : Reach t ht) :
      (anchor t ht v).card ≤ t := by
    rcases v.property with ⟨x, hx⟩
    simpa [hist_card t x] using Multiset.card_le_card (anchor_le_hist t ht v x hx)
  have symbol_count_snoc (t : ℕ) (x : Fin t → Fin k) (j l : Fin k) :
      symbol_count (Fin.lastCases j x) l =
        symbol_count x l + if j = l then 1 else 0 := by
    rw [← hist_count (t + 1) (Fin.lastCases j x) l, ← hist_count t x l]
    simp only [hist, List.ofFn_succ_last, Fin.lastCases_castSucc,
      Fin.lastCases_last, List.count_append, List.count_cons, List.count_nil]
    by_cases h : j = l <;> simp [h]
  let next (t : ℕ) (ht : t < n) (v : Reach t ht.le) (j : Fin k) :
      Reach (t + 1) (Nat.succ_le_iff.mpr ht) :=
    ⟨P.step ⟨t, ht⟩ v j, by
      rcases v.property with ⟨x, hx⟩
      exact ⟨Fin.lastCases j x, by rw [run_snoc, hx]⟩⟩
  have anchor_next_le (t : ℕ) (ht : t < n) (v : Reach t ht.le) (j : Fin k) :
      anchor (t + 1) (Nat.succ_le_iff.mpr ht) (next t ht v j)
        ≤ anchor t ht.le v + {j} := by
    rw [Multiset.le_iff_count]
    intro l
    rw [Multiset.count_add,
      anchor_count (t + 1) (Nat.succ_le_iff.mpr ht) (next t ht v j) l,
      anchor_count t ht.le v l]
    simp only [Multiset.count_singleton]
    rcases minCount_attained t ht.le v l with ⟨x, hx, hxl⟩
    calc
      minCount (t + 1) (Nat.succ_le_iff.mpr ht) (next t ht v j) l
          ≤ symbol_count (Fin.lastCases j x) l := by
            apply minCount_le (t + 1) (Nat.succ_le_iff.mpr ht)
              (next t ht v j) l (Fin.lastCases j x)
            simpa only [next] using
              (run_snoc t ht x j).trans (congrArg (fun u => P.step ⟨t, ht⟩ u j) hx)
      _ = symbol_count x l + if j = l then 1 else 0 := symbol_count_snoc t x j l
      _ = minCount t ht.le v l + if l = j then 1 else 0 := by
        rw [hxl]
        simp only [eq_comm]
  have run_full (x : Fin n → Fin k) : run n le_rfl x = ROBP_run P x := by
    simp only [run, ROBP_run]
  have symbol_count_sum (t : ℕ) (x : Fin t → Fin k) :
      ∑ j : Fin k, symbol_count x j = t := by
    have hcard := Multiset.sum_count_eq_card
      (s := Finset.univ) (m := hist t x) (by simp)
    simpa only [Finset.sum_const_zero, Finset.sum_filter, Finset.mem_univ,
      hist_count, hist_card, Finset.sum_attach] using hcard
  have same_state_count_le (x y : Fin n → Fin k)
      (hxy : run n le_rfl x = run n le_rfl y) (j : Fin k) :
      (symbol_count x j : ℝ) ≤ symbol_count y j + 2 * Δ := by
    have hx := (abs_le.mp (hP x j)).1
    have hy := (abs_le.mp (hP y j)).2
    have hout : P.out (ROBP_run P x) j = P.out (ROBP_run P y) j := by
      rw [← run_full x, ← run_full y, hxy]
    rw [hout] at hx
    linarith
  have terminal_anchor_card (v : Reach n le_rfl) :
      (n : ℝ) - 2 * ((k : ℝ) - 1) * Δ
        ≤ ((anchor n le_rfl v).card : ℝ) := by
    let j0 : Fin k := ⟨0, by omega⟩
    rcases minCount_attained n le_rfl v j0 with ⟨x, hx, hx0⟩
    have hpoint (j : Fin k) :
        (symbol_count x j : ℝ) ≤
          minCount n le_rfl v j + if j = j0 then 0 else 2 * Δ := by
      by_cases hj : j = j0
      · subst j
        simp [hx0]
      · rcases minCount_attained n le_rfl v j with ⟨y, hy, hyj⟩
        have hxy : run n le_rfl x = run n le_rfl y := hx.trans hy.symm
        simpa [hj, hyj] using same_state_count_le x y hxy j
    have hsum := Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) =>
      hpoint j
    have hleft : ∑ j : Fin k, (symbol_count x j : ℝ) = (n : ℝ) := by
      exact_mod_cast symbol_count_sum n x
    have hmin :
        ∑ j : Fin k, (minCount n le_rfl v j : ℝ) =
          ((anchor n le_rfl v).card : ℝ) := by
      exact_mod_cast (anchor_card n le_rfl v).symm
    have herr :
        (∑ j : Fin k, if j = j0 then (0 : ℝ) else 2 * Δ) =
          2 * ((k : ℝ) - 1) * Δ := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j0)]
      have hconst :
          (∑ j ∈ (Finset.univ : Finset (Fin k)).erase j0,
              if j = j0 then (0 : ℝ) else 2 * Δ) =
            ∑ _j ∈ (Finset.univ : Finset (Fin k)).erase j0, 2 * Δ := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [(Finset.mem_erase.mp hj).1]
      rw [hconst]
      simp only [if_true, add_zero, Finset.sum_const, Finset.card_erase_of_mem,
        Finset.mem_univ, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
      ring
    rw [Finset.sum_add_distrib, hleft, hmin, herr] at hsum
    linarith
  have realize_anchor (b : Multiset (Fin k))
      (hb : (b.card : ℝ) < (n : ℝ) - 2 * ((k : ℝ) - 1) * Δ) :
      ∃ t : ℕ, ∃ ht : t < n, ∃ v : Reach t ht.le, anchor t ht.le v = b := by
    have hb_lt_n : b.card < n := by
      have hk1 : (1 : ℝ) ≤ k := by
        exact_mod_cast (by omega : 1 ≤ k)
      have hnonneg : 0 ≤ 2 * ((k : ℝ) - 1) * Δ :=
        mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hk1)) hΔ0
      have : (b.card : ℝ) < n := by linarith
      exact_mod_cast this
    have hb_le_n : b.card ≤ n := hb_lt_n.le
    let vec : List.Vector (Fin k) b.card := ⟨b.toList, by simp⟩
    let x0 : Fin b.card → Fin k := vec.get
    have hx0 : hist b.card x0 = b := by
      change (List.ofFn x0 : Multiset (Fin k)) = b
      rw [← List.Vector.toList_ofFn]
      simp [x0, vec]
    have transport_anchor_le {a c : ℕ} (hac : a = c) (ha : a ≤ n) (hc : c ≤ n)
        (x : Fin a → Fin k) (q : Multiset (Fin k))
        (h : anchor a ha ⟨run a ha x, ⟨x, rfl⟩⟩ ≤ q) :
        anchor c hc
          ⟨run c hc (fun i => x (Fin.cast hac.symm i)),
            ⟨(fun i => x (Fin.cast hac.symm i)), rfl⟩⟩ ≤ q := by
      subst c
      simpa using h
    by_contra hreal
    have hnone (t : ℕ) (ht : t < n) (v : Reach t ht.le) :
        anchor t ht.le v ≠ b := by
      intro hv
      exact hreal ⟨t, ht, v, hv⟩
    have grow :
        ∀ d : ℕ, ∀ hd : b.card + d ≤ n,
          ∃ x : Fin (b.card + d) → Fin k,
            anchor (b.card + d) hd
              ⟨run (b.card + d) hd x, ⟨x, rfl⟩⟩ ≤ b := by
      intro d
      induction d with
      | zero =>
          intro hd
          refine ⟨x0, ?_⟩
          simpa only [Nat.add_zero] using
            (anchor_le_hist b.card hb_le_n
              ⟨run b.card hb_le_n x0, ⟨x0, rfl⟩⟩ x0 rfl).trans_eq hx0
      | succ d ih =>
          intro hd
          have hd' : b.card + d ≤ n := by omega
          have ht : b.card + d < n := by omega
          rcases ih hd' with ⟨x, hx⟩
          let v : Reach (b.card + d) hd' :=
            ⟨run (b.card + d) hd' x, ⟨x, rfl⟩⟩
          have hvle : anchor (b.card + d) hd' v ≤ b := by
            simpa only [v] using hx
          have hvne : anchor (b.card + d) hd' v ≠ b :=
            hnone (b.card + d) ht v
          have hj : ∃ j : Fin k,
              (anchor (b.card + d) hd' v).count j < b.count j := by
            by_contra h
            push Not at h
            have hrev : b ≤ anchor (b.card + d) hd' v := by
              rw [Multiset.le_iff_count]
              exact h
            exact hvne (le_antisymm hvle hrev)
          rcases hj with ⟨j, hj⟩
          let y : Fin (b.card + d + 1) → Fin k := Fin.lastCases j x
          have hplus : anchor (b.card + d) hd' v + {j} ≤ b := by
            rw [Multiset.le_iff_count]
            intro l
            rw [Multiset.count_add, Multiset.count_singleton]
            by_cases hlj : l = j
            · subst l
              simp only [if_true]
              omega
            · simp only [hlj, if_false, add_zero]
              exact (Multiset.le_iff_count.mp hvle) l
          have hstep := (anchor_next_le (b.card + d) ht v j).trans hplus
          have hvnext :
              next (b.card + d) ht v j =
                ⟨run (b.card + d + 1) (Nat.succ_le_iff.mpr ht) y, ⟨y, rfl⟩⟩ := by
            apply Subtype.ext
            simp only [next, v, y]
            simpa only [Subsingleton.elim hd' ht.le] using
              (run_snoc (b.card + d) ht x j).symm
          rw [hvnext] at hstep
          have hac : b.card + d + 1 = b.card + (d + 1) := by omega
          let x' : Fin (b.card + (d + 1)) → Fin k :=
            fun i => y (Fin.cast hac.symm i)
          refine ⟨x', ?_⟩
          simpa only [x'] using
            transport_anchor_le hac (Nat.succ_le_iff.mpr ht) hd y b hstep
    rcases grow (n - b.card) (by omega) with ⟨x, hx⟩
    have hsum : b.card + (n - b.card) = n := Nat.add_sub_of_le hb_le_n
    let xf : Fin n → Fin k := fun i => x (Fin.cast hsum.symm i)
    have hfinal :
        anchor n le_rfl ⟨run n le_rfl xf, ⟨xf, rfl⟩⟩ ≤ b := by
      simpa only [xf] using
        transport_anchor_le hsum (by omega) le_rfl x b hx
    have hterminal :=
      terminal_anchor_card ⟨run n le_rfl xf, ⟨xf, rfl⟩⟩
    have hcard :
        ((anchor n le_rfl
          ⟨run n le_rfl xf, ⟨xf, rfl⟩⟩).card : ℝ) ≤ b.card := by
      exact_mod_cast Multiset.card_le_card hfinal
    linarith
  let N : ℝ := (n : ℝ) - 2 * ((k : ℝ) - 1) * Δ
  have hkR : (1 : ℝ) < k := by
    exact_mod_cast (by omega : 1 < k)
  have hden : 0 < 2 * ((k : ℝ) - 1) := by positivity
  have hN0 : 0 ≤ N := by
    have hmul := (le_div_iff₀ hden).mp hΔ
    dsimp only [N]
    nlinarith
  have hNle : N ≤ n := by
    dsimp only [N]
    have hnonneg : 0 ≤ 2 * ((k : ℝ) - 1) * Δ :=
      mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hkR.le)) hΔ0
    linarith
  let q : ℕ := ⌈N⌉₊
  have hq_le_n : q ≤ n := by
    exact Nat.ceil_le.mpr (by simpa only [q] using hNle)
  let good : Finset ℕ :=
    (Finset.range n).filter fun t => Nat.choose (t + k - 1) (k - 1) ≤ w
  have good_nonempty : good.Nonempty := by
    refine ⟨0, ?_⟩
    simp only [good, Finset.mem_filter, Finset.mem_range]
    constructor
    · omega
    · simpa using hw
  let m : ℕ := good.max' good_nonempty
  have hm_mem : m ∈ good := by
    exact Finset.max'_mem good good_nonempty
  have hm_lt_n : m < n := by
    exact Finset.mem_range.mp (Finset.mem_filter.mp hm_mem).1
  have hmn : m ≤ n - 1 := by omega
  have hmw : Nat.choose (m + k - 1) (k - 1) ≤ w := by
    exact (Finset.mem_filter.mp hm_mem).2
  have hmax (m' : ℕ) (hm'n : m' ≤ n - 1)
      (hm'w : Nat.choose (m' + k - 1) (k - 1) ≤ w) : m' ≤ m := by
    apply Finset.le_max' good m'
    simp only [good, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hm'w⟩
  let B := Σ r : Fin q, Sym (Fin k) r
  let bm (z : B) : Multiset (Fin k) := z.2.1
  have bm_card (z : B) : (bm z).card = z.1 := z.2.2
  have bm_injective : Function.Injective bm := by
    rintro ⟨r, a⟩ ⟨s, b⟩ hab
    have hrs : r = s := by
      apply Fin.ext
      have hcard := congrArg Multiset.card hab
      rw [bm_card ⟨r, a⟩, bm_card ⟨s, b⟩] at hcard
      exact hcard
    subst s
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext hab))
  let D := Σ t : Fin n, Reach t t.isLt.le
  have realize_B (z : B) :
      ∃ d : D, anchor d.1 d.1.isLt.le d.2 = bm z := by
    have hbz : ((bm z).card : ℝ) < N := by
      rw [bm_card z]
      exact Nat.lt_ceil.mp (by simpa only [q] using z.1.isLt)
    rcases realize_anchor (bm z) (by simpa only [N] using hbz) with
      ⟨t, ht, v, hv⟩
    exact ⟨⟨⟨t, ht⟩, v⟩, hv⟩
  let hit (z : B) : D := Classical.choose (realize_B z)
  have hit_spec (z : B) :
      anchor (hit z).1 (hit z).1.isLt.le (hit z).2 = bm z :=
    Classical.choose_spec (realize_B z)
  have hit_injective : Function.Injective hit := by
    intro a b hab
    apply bm_injective
    rw [← hit_spec a, ← hit_spec b, hab]
  have hit_time_ge_card (z : B) : (z.1 : ℕ) ≤ ((hit z).1 : ℕ) := by
    rw [← bm_card z, ← hit_spec z]
    exact anchor_card_le (hit z).1 (hit z).1.isLt.le (hit z).2
  let lowP (z : B) : Prop := z.1 < m + 1
  let Low := {z : B // lowP z}
  let High := {z : B // ¬ lowP z}
  let LowSpace := Σ r : Fin (m + 1), Sym (Fin k) r
  let lowMap (z : Low) : LowSpace :=
    ⟨⟨z.1.1, z.2⟩, ⟨bm z.1, bm_card z.1⟩⟩
  have lowMap_injective : Function.Injective lowMap := by
    intro a b hab
    apply Subtype.ext
    apply bm_injective
    exact congrArg (fun z : LowSpace => (z.2.1 : Multiset (Fin k))) hab
  let symE1 (a r : ℕ) :
      {s : Sym (Fin a.succ) r.succ // (0 : Fin a.succ) ∈ s} ≃
        Sym (Fin a.succ) r :=
    { toFun := fun s => s.1.erase 0 s.2
      invFun := fun s => ⟨Sym.cons 0 s, Sym.mem_cons_self 0 s⟩
      left_inv := by intro s; simp
      right_inv := by intro s; simp }
  let symE2 (a r : ℕ) :
      {s : Sym (Fin a.succ.succ) r // (0 : Fin a.succ.succ) ∉ s} ≃
        Sym (Fin a.succ) r :=
    { toFun := fun s => Sym.map (Fin.predAbove 0) s.1
      invFun := fun s =>
        ⟨Sym.map (Fin.succAbove 0) s,
          (mt Sym.mem_map.1) (not_exists.2 fun t =>
            not_and.2 fun _ => Fin.succAbove_ne _ t)⟩
      left_inv := by
        intro s
        ext1
        simp only [Sym.map_map]
        refine (Sym.map_congr fun v hv => ?_).trans (Sym.map_id' _)
        exact Fin.succAbove_predAbove (ne_of_mem_of_not_mem hv s.2)
      right_inv := by
        intro s
        simp only [Sym.map_map, Function.comp_apply, ← Fin.castSucc_zero,
          Fin.predAbove_succAbove, Sym.map_id'] }
  let rec local_card_sym : ∀ a r : ℕ,
      Fintype.card (Sym (Fin a) r) = Nat.multichoose a r
    | a, 0 => by simp
    | 0, r + 1 => by
        rw [Nat.multichoose_zero_succ]
        exact Fintype.card_eq_zero
    | 1, r + 1 => by simp
    | a + 2, r + 1 => by
        rw [Nat.multichoose_succ_succ,
          ← local_card_sym (a + 1) (r + 1),
          ← local_card_sym (a + 2) r,
          add_comm (Fintype.card _), ← Fintype.card_sum]
        refine Fintype.card_congr (Equiv.symm ?_)
        exact ((symE1 (a + 1) r).symm.sumCongr
          (symE2 a (r + 1)).symm).trans
            (Equiv.sumCompl (fun s : Sym (Fin (a + 2)) (r + 1) =>
              (0 : Fin (a + 2)) ∈ s))
  have card_LowSpace : Fintype.card LowSpace = Nat.choose (m + k) k := by
    simp only [LowSpace, Fintype.card_sigma, Fintype.card_fin]
    simp_rw [local_card_sym]
    rw [Fin.sum_univ_eq_sum_range]
    simpa only [Nat.add_comm] using Nat.sum_range_multichoose m k
  have card_Low_le : Fintype.card Low ≤ Nat.choose (m + k) k := by
    rw [← card_LowSpace]
    exact Fintype.card_le_of_injective lowMap lowMap_injective
  let highCode (z : High) : Fin (n - (m + 1)) × Fin w :=
    (⟨(hit z.1).1 - (m + 1), by
        have hz : m + 1 ≤ z.1.1 := Nat.le_of_not_gt z.2
        have hzt := hit_time_ge_card z.1
        omega⟩,
      (hit z.1).2.1)
  have highCode_injective : Function.Injective highCode := by
    intro a b hab
    have htimeSub := congrArg (fun p : Fin (n - (m + 1)) × Fin w => p.1.1) hab
    have hstate := congrArg (fun p : Fin (n - (m + 1)) × Fin w => p.2) hab
    have htime : (hit a.1).1 = (hit b.1).1 := by
      apply Fin.ext
      have ha : m + 1 ≤ (hit a.1).1 := by
        exact (Nat.le_of_not_gt a.2).trans (hit_time_ge_card a.1)
      have hb : m + 1 ≤ (hit b.1).1 := by
        exact (Nat.le_of_not_gt b.2).trans (hit_time_ge_card b.1)
      dsimp only [highCode] at htimeSub
      omega
    apply Subtype.ext
    apply hit_injective
    dsimp only [highCode] at hstate
    have raw_injective :
        Function.Injective (fun d : D => (d.1, d.2.1)) := by
      rintro ⟨ta, va⟩ ⟨tb, vb⟩ habRaw
      have ht : ta = tb := congrArg Prod.fst habRaw
      subst tb
      exact Sigma.ext rfl
        (heq_of_eq (Subtype.ext (congrArg Prod.snd habRaw)))
    apply raw_injective
    exact congrArg₂ (fun (t : Fin n) (s : Fin w) => (t, s)) htime hstate
  have card_High_le :
      Fintype.card High ≤ (n - (m + 1)) * w := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using
      Fintype.card_le_of_injective highCode highCode_injective
  have card_partition :
      Fintype.card B = Fintype.card Low + Fintype.card High := by
    have hcomp := Fintype.card_subtype_compl lowP
    have hlow := Fintype.card_subtype_le lowP
    change Fintype.card High =
      Fintype.card B - Fintype.card Low at hcomp
    change Fintype.card Low ≤ Fintype.card B at hlow
    omega
  have card_B_le :
      Fintype.card B ≤ Nat.choose (m + k) k + (n - m - 1) * w := by
    have hsub : n - (m + 1) = n - m - 1 := by omega
    rw [card_partition, ← hsub]
    exact Nat.add_le_add card_Low_le card_High_le
  have card_B : Fintype.card B = Nat.choose (q + k - 1) k := by
    simp only [B, Fintype.card_sigma, Fintype.card_fin]
    simp_rw [local_card_sym]
    rw [Fin.sum_univ_eq_sum_range]
    cases q with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty, zero_add]
        exact (Nat.choose_eq_zero_of_lt (by omega)).symm
    | succ q' =>
        have harg : q' + 1 + k - 1 = k + q' := by omega
        rw [harg]
        simpa only [Nat.add_comm] using Nat.sum_range_multichoose q' k
  have hNq : N ≤ (q : ℝ) := by
    simpa only [q] using (Nat.le_ceil N)
  have hprod :
      (∏ j ∈ Finset.range k, (N + (k : ℝ) - 1 - j)) ≤
        ∏ j ∈ Finset.range k, ((q : ℝ) + k - 1 - j) := by
    apply Finset.prod_le_prod
    · intro j hj
      have hjlt : j < k := Finset.mem_range.mp hj
      have hjR : (j : ℝ) + 1 ≤ k := by
        exact_mod_cast (Nat.succ_le_iff.mpr hjlt)
      linarith
    · intro j hj
      linarith
  have hdesc :
      (descPochhammer ℝ k).eval (N + k - 1) ≤
        (descPochhammer ℝ k).eval ((q : ℝ) + k - 1) := by
    simpa only [descPochhammer_eval_eq_prod_range] using hprod
  have desc_eval_eq_smeval (x : ℝ) :
      (descPochhammer ℝ k).eval x =
        (descPochhammer ℤ k).smeval x := by
    rw [← descPochhammer_map (RingHom.smulOneHom : ℤ →+* ℝ) k,
      Polynomial.eval_map,
      Polynomial.eval₂_smulOneHom_eq_smeval]
  rw [desc_eval_eq_smeval, desc_eval_eq_smeval,
    Ring.descPochhammer_eq_factorial_smul_choose,
    Ring.descPochhammer_eq_factorial_smul_choose] at hdesc
  have hkfac : (0 : ℝ) < k.factorial := by positivity
  have hchoose :
      Ring.choose (N + k - 1) k ≤
        Ring.choose ((q : ℝ) + k - 1) k := by
    simp only [nsmul_eq_mul] at hdesc
    exact le_of_mul_le_mul_left hdesc hkfac
  have hqk : 1 ≤ q + k := by omega
  have hqcast : (q : ℝ) + k - 1 = ((q + k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show q + k - 1 = q + k - 1 from rfl)
  rw [hqcast, Ring.choose_natCast] at hchoose
  have hcardNat :
      Nat.choose (q + k - 1) k ≤
        Nat.choose (m + k) k + (n - m - 1) * w := by
    rw [← card_B]
    exact card_B_le
  have hcardReal :
      (Nat.choose (q + k - 1) k : ℝ) ≤
        Nat.choose (m + k) k + ((n - m - 1 : ℕ) : ℝ) * w := by
    exact_mod_cast hcardNat
  have hsubcast :
      ((n - m - 1 : ℕ) : ℝ) = (n : ℝ) - m - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n - m)]
    rw [Nat.cast_sub (by omega : m ≤ n)]
    norm_num
  rw [hsubcast] at hcardReal
  have hchooseFinal :
      Ring.choose (N + k - 1) k ≤
        Nat.choose (m + k) k + ((n : ℝ) - m - 1) * w :=
    hchoose.trans hcardReal
  rw [k_counter_truncated_sum k n w m hk hn hw hmn hmw hmax]
  dsimp only [N] at hchooseFinal
  linarith

@[blueprint "thm:k-counter-lb"
  (statement := /-- \emph{($k$-counter lower bound.)} Let $k \ge 2$, $n \ge 1$ and $w \ge 1$ be
    integers and let $\Delta$ be a real number with $0 \le \Delta \le \frac{n}{2(k-1)}$.
    Suppose that there exists a length-$n$ width-$w$ ROBP $P$ over the alphabet $[k]$, in the
    sense of \cref{def:ROBP}, such that $P$ computes
    $\mathrm{ApproxCount}_{k\text{-}\mathrm{counter}}[n,\Delta]$ in the sense of
    \cref{def:computes-approx-count}. Let $m$ be the largest nonnegative integer such that
    $m \le n-1$ and
    $\binom{m+k-1}{k-1} \le w$. Then
    $$\binom{m+k}{k} + (n-m-1)w \ge \binom{n-2(k-1)\Delta+k-1}{k},$$
    where $\binom{n-2(k-1)\Delta+k-1}{k}$ denotes the generalized binomial coefficient with
    real upper argument. -/)
  (proof := /-- By \cref{lem:k-counter-potential-bound} applied to the program $P$ we have
    $$\binom{n+k-1}{k} - \binom{n-2(k-1)\Delta+k-1}{k}
      \ge \sum_{t=0}^{n-1} \max\left(0, \binom{t+k-1}{k-1} - w\right),$$
    and by \cref{lem:k-counter-truncated-sum} applied to $m$, which is by hypothesis the
    largest integer with $m \le n-1$ and $\binom{m+k-1}{k-1} \le w$, the right-hand side
    equals $\binom{n+k-1}{k} - \binom{m+k}{k} - (n-m-1)w$. Hence
    $$\binom{n+k-1}{k} - \binom{n-2(k-1)\Delta+k-1}{k}
      \ge \binom{n+k-1}{k} - \binom{m+k}{k} - (n-m-1)w.$$
    Cancelling the term $\binom{n+k-1}{k}$, which occurs on both sides, and rearranging gives
    $$\binom{m+k}{k} + (n-m-1)w \ge \binom{n-2(k-1)\Delta+k-1}{k},$$
    as asserted. -/)
  (title := /-- $k$-Counter Lower Bound for Deterministic Approximate Counting -/)
  (latexEnv := "theorem")]
theorem k_counter_lb (k n w m : ℕ) (Δ : ℝ) (hk : 2 ≤ k) (hn : 1 ≤ n) (hw : 1 ≤ w)
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ (n : ℝ) / (2 * ((k : ℝ) - 1)))
    (hP : ∃ P : ROBP k n w, computes_approx_count P Δ)
    (hmn : m ≤ n - 1) (hmw : Nat.choose (m + k - 1) (k - 1) ≤ w)
    (hmax : ∀ m' : ℕ, m' ≤ n - 1 → Nat.choose (m' + k - 1) (k - 1) ≤ w → m' ≤ m) :
    (Nat.choose (m + k) k : ℝ) + ((n : ℝ) - m - 1) * w
      ≥ Ring.choose ((n : ℝ) - 2 * ((k : ℝ) - 1) * Δ + (k : ℝ) - 1) k := by
  have hpot := k_counter_potential_bound k n w Δ hk hn hw hΔ0 hΔ hP
  rw [k_counter_truncated_sum k n w m hk hn hw hmn hmw hmax] at hpot
  linarith

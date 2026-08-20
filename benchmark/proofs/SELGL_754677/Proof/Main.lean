import Architect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Computability.DFA
import Mathlib.Data.Set.Card

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators

@[blueprint "def:finite-dfa"
  (statement := /-- Let $\Sigma$ be an alphabet. A finite deterministic finite-state automaton over $\Sigma$ consists of a natural number $n$ and a deterministic finite-state automaton with state type $\operatorname{Fin}(n)$. No external bound is imposed on $n$. -/)
  (title := /-- Finite deterministic finite-state automata -/)
  (latexEnv := "definition")]
structure finite_dfa (α : Type) where
  stateCount : ℕ
  automaton : DFA α (Fin stateCount)

@[blueprint "def:finite-dfa-language"
  (statement := /-- The language $L(A)$ of a finite deterministic finite-state automaton $A$ is the set of finite words accepted by its underlying automaton from its initial state. -/)
  (title := /-- Language accepted by a finite automaton -/)
  (latexEnv := "definition")]
def finite_dfa_language {α : Type} (A : finite_dfa α) : Language α :=
  A.automaton.accepts

@[blueprint "def:bounded-dfa"
  (statement := /-- Let $\Sigma$ be an alphabet and let $s\in\mathbb{N}$. A bounded deterministic finite-state automaton over $\Sigma$ consists of a natural number $n\leq s$ and a deterministic finite-state automaton with state type $\operatorname{Fin}(n)$. -/)
  (title := /-- Bounded deterministic finite-state automata -/)
  (latexEnv := "definition")]
structure bounded_dfa (α : Type) (s : ℕ) where
  stateCount : ℕ
  stateCount_le : stateCount ≤ s
  automaton : DFA α (Fin stateCount)

@[blueprint "def:bounded-dfa-language"
  (statement := /-- The language $L(A)$ of a bounded deterministic finite-state automaton $A$ is the set of finite words accepted by its underlying automaton from its initial state. -/)
  (title := /-- Language accepted by a bounded automaton -/)
  (latexEnv := "definition")]
def bounded_dfa_language {α : Type} {s : ℕ} (A : bounded_dfa α s) : Language α :=
  A.automaton.accepts

@[blueprint "def:language-enumeration"
  (statement := /-- Let $K\subseteq\Sigma^*$. A language enumeration of $K$ is a surjection $w:\mathbb{N}\twoheadrightarrow K$, where the codomain is the subtype of words belonging to $K$. -/)
  (title := /-- Surjective enumeration of a language -/)
  (latexEnv := "definition")]
abbrev language_enumeration {α : Type} (K : Language α) :=
  {w : ℕ → {x : List α // x ∈ K} // Function.Surjective w}

@[blueprint "def:stream-prefix"
  (statement := /-- Let $w:\mathbb{N}\twoheadrightarrow K$ be a language enumeration and let $t\in\mathbb{N}$. The encoded stream prefix at time $t$ is obtained by concatenating the symbols of $w(0),\ldots,w(t-1)$ in order and placing a distinguished word-boundary token after each word. Thus every entry of the resulting list is either one alphabet symbol or one boundary token. -/)
  (title := /-- Symbol-by-symbol encoding of an enumeration prefix -/)
  (latexEnv := "definition")]
def stream_prefix {α : Type} {K : Language α} (w : language_enumeration K) (t : ℕ) :
    List (Option α) :=
  (List.ofFn fun i : Fin t => (w.1 i).1).flatMap
    fun x => x.map some ++ [none]

@[blueprint "def:streaming-generator"
  (statement := /-- Let $\Sigma$ be an alphabet and let $s\in\mathbb{N}$ be the state bound for the target class. A streaming generator with $m$ bits of working memory consists of an initial Boolean vector indexed by $\operatorname{Fin}(m)$, a transition map that updates this vector after reading one token in $\Sigma\sqcup\{\mathtt{boundary}\}$, and a map from the current vector to an arbitrary finite DFA. The parameter $s$ does not bound the number of states of this output DFA. The generator's only persistent configuration is the $m$-bit vector; in particular, its output cannot inspect the previously consumed stream except through that vector. -/)
  (title := /-- Finite-memory symbol-streaming generator -/)
  (latexEnv := "definition")]
structure streaming_generator (α : Type) (s : ℕ) where
  memoryBits : ℕ
  initial : Fin memoryBits → Bool
  step : (Fin memoryBits → Bool) → Option α → (Fin memoryBits → Bool)
  output : (Fin memoryBits → Bool) → finite_dfa α

@[blueprint "def:generator-family"
  (statement := /-- A generator family assigns a streaming generator to every finite alphabet $\Sigma$ and every positive state bound $s$. The assignment is uniform in the target language and its enumeration. -/)
  (title := /-- Uniform family of streaming generators -/)
  (latexEnv := "definition")]
structure generator_family where
  generator : ∀ {α : Type} [Fintype α] (s : ℕ) (hs : 0 < s), streaming_generator α s

@[blueprint "def:streaming-generator-run"
  (statement := /-- Let $G$ be a streaming generator and let $u$ be a finite token stream. The configuration reached by $G$ on $u$ is obtained from its initial memory vector by applying its one-token transition successively to the tokens of $u$ in their given order. -/)
  (title := /-- Configuration reached after a finite token stream -/)
  (latexEnv := "definition")]
def streaming_generator_run {α : Type} {s : ℕ} (G : streaming_generator α s)
    (input : List (Option α)) : Fin G.memoryBits → Bool :=
  input.foldl G.step G.initial

@[blueprint "def:generated-language"
  (statement := /-- Given a generator family $\mathcal A$, a target-state bound $s$ satisfying $0<s$, and a finite token stream $u$, run the one-token transition of $\mathcal A$ successively over $u$. The generated language is the language accepted by the unrestricted finite DFA determined by the resulting memory configuration. -/)
  (title := /-- Language output by a generator -/)
  (latexEnv := "definition")]
def generated_language (F : generator_family) {α : Type} [Fintype α] (s : ℕ)
    (hs : 0 < s) (input : List (Option α)) : Language α :=
  finite_dfa_language
    ((F.generator s hs).output (streaming_generator_run (F.generator s hs) input))

@[blueprint "def:outputs-within-state-bound"
  (statement := /-- A generator family has outputs within the target-state bound if, for every finite alphabet $\Sigma$, every positive target-state bound $s$, and every finite token stream, the finite DFA produced by the corresponding streaming generator has at most $s$ states. This is an optional property of a generator family, not a restriction in the definition of a streaming generator. -/)
  (title := /-- Generator outputs within the target-state bound -/)
  (latexEnv := "definition")]
def outputs_within_state_bound (F : generator_family) : Prop :=
  ∀ {α : Type} [Fintype α] (s : ℕ) (hs : 0 < s) (input : List (Option α)),
    ((F.generator s hs).output
      (streaming_generator_run (F.generator s hs) input)).stateCount ≤ s

@[blueprint "def:uses-polynomial-space"
  (statement := /-- A generator family $\mathcal A$ uses polynomial space if there exist constants $C,d\in\mathbb{N}$ such that, for every finite alphabet $\Sigma$ and every positive state bound $s$, the persistent configuration of its streaming machine has at most $C(s+|\Sigma|+1)^d$ Boolean coordinates. This bound concerns the actual width of every reachable machine configuration and is independent of the length of the consumed stream. -/)
  (title := /-- Uniform polynomial-space usage -/)
  (latexEnv := "definition")]
def uses_polynomial_space (F : generator_family) : Prop :=
  ∃ C d : ℕ,
    ∀ {α : Type} [Fintype α] (s : ℕ) (hs : 0 < s),
      (F.generator (α := α) s hs).memoryBits ≤
        C * (s + Fintype.card α + 1) ^ d

@[blueprint "def:language-symmetric-difference"
  (statement := /-- The symmetric difference of languages $K,L\subseteq\Sigma^*$ is $(K\setminus L)\cup(L\setminus K)$. -/)
  (title := /-- Symmetric difference of languages -/)
  (latexEnv := "definition")]
def language_symmetric_difference {α : Type} (K L : Language α) : Set (List α) :=
  (K \ L) ∪ (L \ K)

@[blueprint "def:eventually-finite-symmetric-difference"
  (statement := /-- A generator family has eventually finite symmetric difference if, for every finite alphabet $\Sigma$, positive state bound $s$, target DFA $A$ with at most $s$ states, and surjective enumeration $w$ of $L(A)$, there is a time $t_0$ after which the generated language and $L(A)$ have finite symmetric difference. -/)
  (title := /-- Eventual finite symmetric difference -/)
  (latexEnv := "definition")]
def eventually_finite_symmetric_difference (F : generator_family) : Prop :=
  ∀ {α : Type} [Fintype α] (s : ℕ) (hs : 0 < s) (target : bounded_dfa α s)
    (w : language_enumeration (bounded_dfa_language target)),
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      (language_symmetric_difference
        (generated_language F s hs (stream_prefix w t))
        (bounded_dfa_language target)).Finite

@[blueprint "def:eventually-no-hallucination"
  (statement := /-- A generator family satisfies eventual no-hallucination if, for every finite alphabet $\Sigma$, positive state bound $s$, target DFA $A$ with at most $s$ states, and surjective enumeration $w$ of $L(A)$, every sufficiently late output language is contained in $L(A)$. -/)
  (title := /-- Eventual no-hallucination -/)
  (latexEnv := "definition")]
def eventually_no_hallucination (F : generator_family) : Prop :=
  ∀ {α : Type} [Fintype α] (s : ℕ) (hs : 0 < s) (target : bounded_dfa α s)
    (w : language_enumeration (bounded_dfa_language target)),
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      generated_language F s hs (stream_prefix w t) ≤
        bounded_dfa_language target

@[blueprint "def:has-generation-gap-order"
  (statement := /-- A generator family has generation gap $O(k^{2s-2})$ if, for every fixed positive state bound $s$, there are constants $C,k_0\in\mathbb{N}$ such that for every finite alphabet $\Sigma$ of cardinality $k\geq k_0$, every target DFA $A$ with at most $s$ states, and every surjective enumeration of $L(A)$, all sufficiently late outputs omit a finite set of at most $Ck^{2s-2}$ target words. -/)
  (title := /-- Asymptotic generation-gap bound -/)
  (latexEnv := "definition")]
def has_generation_gap_order (F : generator_family) : Prop :=
  ∀ (s : ℕ) (hs : 0 < s), ∃ C k₀ : ℕ,
    ∀ {α : Type} [Fintype α], k₀ ≤ Fintype.card α →
      ∀ (target : bounded_dfa α s)
        (w : language_enumeration (bounded_dfa_language target)),
        ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
          (bounded_dfa_language target \
            generated_language F s hs (stream_prefix w t)).Finite ∧
          (bounded_dfa_language target \
            generated_language F s hs (stream_prefix w t)).ncard ≤
              C * Fintype.card α ^ (2 * s - 2)

@[blueprint "def:prec2-candidate"
  (statement := /-- For a finite alphabet $\Sigma$ and a positive state bound $s$, a candidate consists of an $s$-state transition table, a start state, and a Boolean table of accepting states. -/)
  (title := /-- Finite data for an $s$-state candidate DFA -/)
  (latexEnv := "definition")]
structure prec2_candidate (α : Type) (s : ℕ) where
  step : Fin s → α → Fin s
  start : Fin s
  accept : Fin s → Bool

@[blueprint "def:prec2-candidate-fintype"
  (statement := /-- When $\Sigma$ is finite, the type of $s$-state candidates over $\Sigma$ is finite. -/)
  (title := /-- Finiteness of the candidate space -/)
  (latexEnv := "definition")]
noncomputable instance prec2_candidate_fintype {α : Type} [Fintype α] (s : ℕ) :
    Fintype (prec2_candidate α s) := by
  classical
  exact Fintype.ofEquiv
    ((Fin s → α → Fin s) × Fin s × (Fin s → Bool))
    { toFun := fun A => ⟨A.1, A.2.1, A.2.2⟩
      invFun := fun A => ⟨A.step, A.start, A.accept⟩
      left_inv := by intro A; rfl
      right_inv := by intro A; rfl }

@[blueprint "def:prec2-candidate-dfa"
  (statement := /-- The finite DFA associated with a candidate uses its transition and start tables and accepts precisely the states whose Boolean acceptance entry is true. -/)
  (title := /-- DFA represented by a candidate -/)
  (latexEnv := "definition")]
def prec2_candidate_dfa {α : Type} {s : ℕ} (A : prec2_candidate α s) : finite_dfa α :=
  ⟨s, ⟨A.step, A.start, {q | A.accept q = true}⟩⟩

@[blueprint "def:prec2-candidate-language"
  (statement := /-- The language of a candidate is the language accepted by its represented finite DFA. -/)
  (title := /-- Language represented by a candidate -/)
  (latexEnv := "definition")]
def prec2_candidate_language {α : Type} {s : ℕ} (A : prec2_candidate α s) : Language α :=
  finite_dfa_language (prec2_candidate_dfa A)

@[blueprint "def:prec2-padded-candidate"
  (statement := /-- A target DFA with $n\leq s$ states is padded to an $s$-state candidate by embedding its states into $\operatorname{Fin}(s)$ and making every padding state return to the embedded start state. -/)
  (title := /-- Padding a bounded DFA to exactly $s$ states -/)
  (latexEnv := "definition")]
noncomputable def prec2_padded_candidate {α : Type} {s : ℕ}
    (target : bounded_dfa α s) : prec2_candidate α s := by
  classical
  exact
    { step := fun q a => if hq : q.val < target.stateCount then
          Fin.castLE target.stateCount_le (target.automaton.step ⟨q.val, hq⟩ a)
        else
          Fin.castLE target.stateCount_le target.automaton.start
      start := Fin.castLE target.stateCount_le target.automaton.start
      accept := fun q => if hq : q.val < target.stateCount then
          decide (⟨q.val, hq⟩ ∈ target.automaton.accept)
        else false }

@[blueprint "lem:prec2-padded-candidate-language"
  (statement := /-- Padding a bounded DFA to the ambient state bound preserves its accepted language exactly. -/)
  (proof := /-- By \cref{def:prec2-padded-candidate}, every state reached from the embedded start state remains embedded, and its transition is the embedding of the corresponding target transition. Induction on the input word therefore identifies the two terminal states, while the Boolean acceptance table agrees with the target acceptance predicate on every embedded state. The represented language from \cref{def:prec2-candidate-language} is consequently the bounded target language. -/)
  (title := /-- Language preservation under DFA padding -/)
  (latexEnv := "lemma")]
lemma prec2_padded_candidate_language {α : Type} {s : ℕ}
    (target : bounded_dfa α s) :
    prec2_candidate_language (prec2_padded_candidate target) =
      bounded_dfa_language target := by
  classical
  ext x
  have hrun : ∀ (q : Fin target.stateCount),
      List.foldl (prec2_padded_candidate target).step
          (Fin.castLE target.stateCount_le q) x =
        Fin.castLE target.stateCount_le (List.foldl target.automaton.step q x) := by
    induction x with
    | nil => intro q; rfl
    | cons a x ih =>
        intro q
        simp only [List.foldl_cons]
        rw [show (prec2_padded_candidate target).step
              (Fin.castLE target.stateCount_le q) a =
            Fin.castLE target.stateCount_le (target.automaton.step q a) by
          simp [prec2_padded_candidate]]
        exact ih (target.automaton.step q a)
  simp only [prec2_candidate_language, prec2_candidate_dfa,
    finite_dfa_language, bounded_dfa_language, DFA.accepts, DFA.acceptsFrom,
    DFA.evalFrom, Set.mem_setOf_eq]
  change (prec2_padded_candidate target).accept
      (List.foldl (prec2_padded_candidate target).step
        (prec2_padded_candidate target).start x) = true ↔
    List.foldl target.automaton.step target.automaton.start x ∈
      target.automaton.accept
  rw [show (prec2_padded_candidate target).start =
      Fin.castLE target.stateCount_le target.automaton.start by
    simp [prec2_padded_candidate]]
  rw [hrun target.automaton.start]
  simp [prec2_padded_candidate]

@[blueprint "def:prec2-almost-inclusion"
  (statement := /-- For candidates $A$ and $B$, write $A\preccurlyeq^*B$ when $L(A)\setminus L(B)$ is finite. -/)
  (title := /-- Inclusion modulo finitely many words -/)
  (latexEnv := "definition")]
def prec2_almost_inclusion {α : Type} {s : ℕ}
    (A B : prec2_candidate α s) : Prop :=
  (prec2_candidate_language A \ prec2_candidate_language B).Finite

@[blueprint "def:prec2-candidate-rank"
  (statement := /-- The rank of a candidate is the number of candidates almost included in it. -/)
  (title := /-- Almost-inclusion rank of a candidate -/)
  (latexEnv := "definition")]
noncomputable def prec2_candidate_rank {α : Type} [Fintype α] {s : ℕ}
    (A : prec2_candidate α s) : ℕ := by
  classical
  exact (Finset.univ.filter fun B : prec2_candidate α s =>
    prec2_almost_inclusion B A).card

@[blueprint "lem:prec2-candidate-rank-strict"
  (statement := /-- If $A$ is almost included in $B$ but $B$ is not almost included in $A$, then the almost-inclusion rank of $A$ is strictly smaller than that of $B$. -/)
  (proof := /-- The candidates almost included in $A$ form a subset of those almost included in $B$: transitivity follows because $L(D)\setminus L(B)$ is contained in the union of $L(D)\setminus L(A)$ and $L(A)\setminus L(B)$. The inclusion is strict because $B$ belongs to its own lower set but, by hypothesis, not to the lower set of $A$. Strict monotonicity of finite-set cardinality and \cref{def:prec2-candidate-rank} give the result. -/)
  (title := /-- Strict growth of the almost-inclusion rank -/)
  (latexEnv := "lemma")]
lemma prec2_candidate_rank_strict {α : Type} [Fintype α] {s : ℕ}
    {A B : prec2_candidate α s}
    (hAB : prec2_almost_inclusion A B)
    (hBA : ¬ prec2_almost_inclusion B A) :
    prec2_candidate_rank A < prec2_candidate_rank B := by
  classical
  let lower (C : prec2_candidate α s) :=
    Finset.univ.filter fun D : prec2_candidate α s =>
      prec2_almost_inclusion D C
  have htrans : ∀ {C D E : prec2_candidate α s},
      prec2_almost_inclusion C D → prec2_almost_inclusion D E →
        prec2_almost_inclusion C E := by
    intro C D E hCD hDE
    apply (hCD.union hDE).subset
    intro x hx
    by_cases hxD : x ∈ prec2_candidate_language D
    · exact Or.inr ⟨hxD, hx.2⟩
    · exact Or.inl ⟨hx.1, hxD⟩
  have hsub : lower A ⊆ lower B := by
    intro D hD
    simp only [lower, Finset.mem_filter, Finset.mem_univ, true_and] at hD ⊢
    exact htrans hD hAB
  have hBB : prec2_almost_inclusion B B := by
    rw [prec2_almost_inclusion]
    convert (Set.finite_empty : (∅ : Set (List α)).Finite)
    ext x
    constructor
    · intro hx
      exact (hx.2 hx.1).elim
    · intro hx
      change False at hx
      exact hx.elim
  have hproper : lower A ⊂ lower B :=
    (Finset.ssubset_iff_of_subset hsub).2 ⟨B, by
      simp only [lower, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hBB, by
      simp only [lower, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hBA⟩
  simpa [prec2_candidate_rank, lower] using Finset.card_lt_card hproper

@[blueprint "def:prec2-candidate-code"
  (statement := /-- The code of a candidate is its index in a fixed equivalence with the finite initial segment whose length is the number of candidates. -/)
  (title := /-- Finite code of a candidate -/)
  (latexEnv := "definition")]
noncomputable def prec2_candidate_code {α : Type} [Fintype α] {s : ℕ}
    (A : prec2_candidate α s) : ℕ :=
  (Fintype.equivFin (prec2_candidate α s) A).val

@[blueprint "def:prec2-candidate-key"
  (statement := /-- The key of a candidate orders first by almost-inclusion rank and then by its finite code. -/)
  (title := /-- Rank-refined key of a candidate -/)
  (latexEnv := "definition")]
noncomputable def prec2_candidate_key {α : Type} [Fintype α] {s : ℕ}
    (A : prec2_candidate α s) : ℕ :=
  prec2_candidate_rank A * Fintype.card (prec2_candidate α s) +
    prec2_candidate_code A

@[blueprint "lem:prec2-candidate-key-injective"
  (statement := /-- Distinct candidates have distinct rank-refined keys. -/)
  (proof := /-- Reduce equality of the keys from \cref{def:prec2-candidate-key} modulo the positive number of candidates. The rank multiples vanish, and each code from \cref{def:prec2-candidate-code} is already smaller than that modulus. Equality of codes then implies equality of candidates through the fixed equivalence. -/)
  (title := /-- Injectivity of candidate keys -/)
  (latexEnv := "lemma")]
lemma prec2_candidate_key_injective {α : Type} [Fintype α] {s : ℕ} :
    Function.Injective (@prec2_candidate_key α _ s) := by
  classical
  intro A B h
  let N := Fintype.card (prec2_candidate α s)
  have hN : 0 < N := Fintype.card_pos_iff.mpr ⟨A⟩
  have hmod := congrArg (fun n : ℕ => n % N) h
  have hltA : prec2_candidate_code A < N :=
    (Fintype.equivFin (prec2_candidate α s) A).isLt
  have hltB : prec2_candidate_code B < N :=
    (Fintype.equivFin (prec2_candidate α s) B).isLt
  have hcode : prec2_candidate_code A = prec2_candidate_code B := by
    simpa [prec2_candidate_key, N, Nat.add_mod, Nat.mul_mod,
      Nat.mod_eq_of_lt hltA, Nat.mod_eq_of_lt hltB] using hmod
  apply (Fintype.equivFin (prec2_candidate α s)).injective
  apply Fin.ext
  exact hcode

@[blueprint "lem:prec2-candidate-key-strict"
  (statement := /-- Strict almost inclusion forces strict growth of the rank-refined candidate key. -/)
  (proof := /-- By \cref{lem:prec2-candidate-rank-strict}, the rank increases by at least one. Each finite code from \cref{def:prec2-candidate-code} is smaller than the number of candidates, so the entire key block of the lower rank precedes every key in the higher-rank block defined by \cref{def:prec2-candidate-key}. -/)
  (title := /-- Strict growth of candidate keys -/)
  (latexEnv := "lemma")]
lemma prec2_candidate_key_strict {α : Type} [Fintype α] {s : ℕ}
    {A B : prec2_candidate α s}
    (hAB : prec2_almost_inclusion A B)
    (hBA : ¬ prec2_almost_inclusion B A) :
    prec2_candidate_key A < prec2_candidate_key B := by
  classical
  have hrank := prec2_candidate_rank_strict hAB hBA
  let N := Fintype.card (prec2_candidate α s)
  have hcodeA : prec2_candidate_code A < N :=
    (Fintype.equivFin (prec2_candidate α s) A).isLt
  have hstep : prec2_candidate_rank A * N + prec2_candidate_code A <
      (prec2_candidate_rank A + 1) * N := by
    rw [Nat.add_mul]
    simpa using Nat.add_lt_add_left hcodeA (prec2_candidate_rank A * N)
  calc
    prec2_candidate_key A < (prec2_candidate_rank A + 1) * N := by
      simpa [prec2_candidate_key, N] using hstep
    _ ≤ prec2_candidate_rank B * N :=
      Nat.mul_le_mul_right N (Nat.succ_le_iff.mpr hrank)
    _ ≤ prec2_candidate_key B := by
      simp [prec2_candidate_key, N]

@[blueprint "def:prec2-universal-candidate"
  (statement := /-- For a positive state bound, the universal candidate stays in its current state and declares every state accepting. -/)
  (title := /-- A canonical inhabited candidate -/)
  (latexEnv := "definition")]
def prec2_universal_candidate {α : Type} {s : ℕ} (hs : 0 < s) :
    prec2_candidate α s where
  step q _ := q
  start := ⟨0, hs⟩
  accept _ := true

@[blueprint "def:prec2-least-candidate"
  (statement := /-- Given a nonempty property of candidates, select a candidate satisfying it whose rank-refined key is least. -/)
  (title := /-- Least-key candidate satisfying a property -/)
  (latexEnv := "definition")]
noncomputable def prec2_least_candidate {α : Type} [Fintype α] {s : ℕ}
    (P : prec2_candidate α s → Prop) (hP : ∃ A, P A) : prec2_candidate α s := by
  classical
  let Q := fun n : ℕ => ∃ A, P A ∧ prec2_candidate_key A = n
  have hQ : ∃ n, Q n := by
    obtain ⟨A, hA⟩ := hP
    exact ⟨prec2_candidate_key A, A, hA, rfl⟩
  exact Classical.choose (Nat.find_spec hQ)

@[blueprint "lem:prec2-least-candidate-spec"
  (statement := /-- The least-key selector returns a candidate satisfying the prescribed property. -/)
  (proof := /-- Unfold \cref{def:prec2-least-candidate}. The specification theorem for the least natural number supplies a candidate satisfying the property at the selected key, and the outer choice returns precisely that witness. -/)
  (title := /-- Specification of the least-key selector -/)
  (latexEnv := "lemma")]
lemma prec2_least_candidate_spec {α : Type} [Fintype α] {s : ℕ}
    (P : prec2_candidate α s → Prop) (hP : ∃ A, P A) :
    P (prec2_least_candidate P hP) := by
  classical
  let Q := fun n : ℕ => ∃ A, P A ∧ prec2_candidate_key A = n
  have hQ : ∃ n, Q n := by
    obtain ⟨A, hA⟩ := hP
    exact ⟨prec2_candidate_key A, A, hA, rfl⟩
  have hspec := Nat.find_spec hQ
  change P (Classical.choose hspec)
  exact (Classical.choose_spec hspec).1

@[blueprint "lem:prec2-least-candidate-minimal"
  (statement := /-- The key chosen by the least-key selector is at most the key of every other candidate satisfying the property. -/)
  (proof := /-- For any competing candidate, its key satisfies the natural-number predicate used in \cref{def:prec2-least-candidate}. Minimality of `Nat.find`, together with its witness equation, gives the required key inequality. -/)
  (title := /-- Minimality of the least-key selector -/)
  (latexEnv := "lemma")]
lemma prec2_least_candidate_minimal {α : Type} [Fintype α] {s : ℕ}
    (P : prec2_candidate α s → Prop) (hP : ∃ A, P A)
    (A : prec2_candidate α s) (hA : P A) :
    prec2_candidate_key (prec2_least_candidate P hP) ≤ prec2_candidate_key A := by
  classical
  let Q := fun n : ℕ => ∃ B, P B ∧ prec2_candidate_key B = n
  have hQ : ∃ n, Q n := by
    obtain ⟨B, hB⟩ := hP
    exact ⟨prec2_candidate_key B, B, hB, rfl⟩
  have hfind := Nat.find_min' hQ (show Q (prec2_candidate_key A) from ⟨A, hA, rfl⟩)
  have hspec := Nat.find_spec hQ
  change prec2_candidate_key (Classical.choose hspec) ≤ prec2_candidate_key A
  rw [(Classical.choose_spec hspec).2]
  exact hfind

@[blueprint "def:prec2-first-candidate"
  (statement := /-- The first candidate is the least candidate in the rank-refined linear order. -/)
  (title := /-- Least candidate -/)
  (latexEnv := "definition")]
noncomputable def prec2_first_candidate {α : Type} [Fintype α] {s : ℕ}
    (hs : 0 < s) : prec2_candidate α s :=
  prec2_least_candidate (fun _ => True) ⟨prec2_universal_candidate hs, trivial⟩

@[blueprint "lem:prec2-first-candidate-minimal"
  (statement := /-- The key of the first candidate is no larger than the key of any candidate. -/)
  (proof := /-- The candidate from \cref{def:prec2-first-candidate} applies the least-key selector to the always-true property. Its minimality from \cref{lem:prec2-least-candidate-minimal} therefore compares it with every candidate. -/)
  (title := /-- Minimality of the first candidate -/)
  (latexEnv := "lemma")]
lemma prec2_first_candidate_minimal {α : Type} [Fintype α] {s : ℕ}
    (hs : 0 < s) (A : prec2_candidate α s) :
    prec2_candidate_key (prec2_first_candidate (α := α) hs) ≤ prec2_candidate_key A := by
  classical
  exact prec2_least_candidate_minimal (fun _ : prec2_candidate α s => True)
    ⟨prec2_universal_candidate hs, trivial⟩ A trivial

@[blueprint "def:prec2-next-candidate"
  (statement := /-- If a candidate with larger key exists, the next candidate is the one with least such key; otherwise it is the current candidate. -/)
  (title := /-- Successor in the candidate key order -/)
  (latexEnv := "definition")]
noncomputable def prec2_next_candidate {α : Type} [Fintype α] {s : ℕ}
    (A : prec2_candidate α s) : prec2_candidate α s := by
  classical
  let later := fun B : prec2_candidate α s =>
    prec2_candidate_key A < prec2_candidate_key B
  if h : ∃ B, later B then exact prec2_least_candidate later h else exact A

@[blueprint "def:prec2-advance-candidate"
  (statement := /-- On a word rejected by the current candidate, advance to the candidate with the least strictly larger key, if one exists; on an accepted word, or if the current key is maximal, remain at the current candidate. -/)
  (title := /-- Rank-ordered candidate update -/)
  (latexEnv := "definition")]
noncomputable def prec2_advance_candidate {α : Type} [Fintype α] {s : ℕ}
    (A : prec2_candidate α s) (x : List α) : prec2_candidate α s := by
  classical
  exact if x ∈ prec2_candidate_language A then A else prec2_next_candidate A

@[blueprint "lem:prec2-advance-bounded-by-target"
  (statement := /-- If the current candidate does not accept a target word and its key is at most the target candidate's key, then the update strictly increases the key but does not pass the target key. -/)
  (proof := /-- The current and target candidates are distinct because they disagree on the target word, so the assumed key inequality is strict by \cref{lem:prec2-candidate-key-injective}. Thus the target satisfies the later-candidate predicate in \cref{def:prec2-advance-candidate}. The selector specification \cref{lem:prec2-least-candidate-spec} gives strict progress, and its minimality \cref{lem:prec2-least-candidate-minimal} bounds the chosen key by the target key. -/)
  (title := /-- Progress without passing the target -/)
  (latexEnv := "lemma")]
lemma prec2_advance_bounded_by_target {α : Type} [Fintype α] {s : ℕ}
    {A T : prec2_candidate α s} {x : List α}
    (hAT : prec2_candidate_key A ≤ prec2_candidate_key T)
    (hxA : x ∉ prec2_candidate_language A)
    (hxT : x ∈ prec2_candidate_language T) :
    prec2_candidate_key A < prec2_candidate_key (prec2_advance_candidate A x) ∧
      prec2_candidate_key (prec2_advance_candidate A x) ≤ prec2_candidate_key T := by
  classical
  have hne : A ≠ T := by
    intro h
    subst T
    exact hxA hxT
  have hkeyne : prec2_candidate_key A ≠ prec2_candidate_key T := by
    intro h
    exact hne (prec2_candidate_key_injective h)
  have hkeylt : prec2_candidate_key A < prec2_candidate_key T :=
    lt_of_le_of_ne hAT hkeyne
  let later := fun B : prec2_candidate α s =>
    prec2_candidate_key A < prec2_candidate_key B
  have hT : later T := hkeylt
  have hlater : ∃ B, later B := ⟨T, hT⟩
  have hselected := prec2_least_candidate_spec later hlater
  have hbound := prec2_least_candidate_minimal later hlater T hT
  have hadvance : prec2_advance_candidate A x = prec2_least_candidate later hlater := by
    simp [prec2_advance_candidate, prec2_next_candidate, hxA, later, hlater]
  rw [hadvance]
  exact ⟨hselected, hbound⟩

@[blueprint "def:prec2-configuration"
  (statement := /-- A learner configuration consists of its current candidate and the state reached by that candidate while scanning the current word. -/)
  (title := /-- Abstract learner configuration -/)
  (latexEnv := "definition")]
abbrev prec2_configuration (α : Type) (s : ℕ) := prec2_candidate α s × Fin s

@[blueprint "def:prec2-memory-bits"
  (statement := /-- For alphabet cardinality $k$ and state bound $s$, allocate $4(s+k+1)^4$ Boolean memory coordinates. -/)
  (title := /-- Polynomial memory width -/)
  (latexEnv := "definition")]
def prec2_memory_bits (s k : ℕ) : ℕ := 4 * (s + k + 1) ^ 4

@[blueprint "lem:prec2-configuration-cardinality"
  (statement := /-- For every finite alphabet and positive state bound, the number of abstract learner configurations is at most $2^{4(s+|\Sigma|+1)^4}$, the number of Boolean vectors of the allocated width. -/)
  (proof := /-- A candidate has $s^{s|\Sigma|}$ transition tables, $s$ choices of start state, and $2^s$ Boolean acceptance tables; a configuration has one further factor $s$. The elementary bound $s\leq 2^s$ converts this product to at most $2^{s^2|\Sigma|+3s}$. Since $s>0$, this exponent is bounded by $4(s+|\Sigma|+1)^4$, which is \cref{def:prec2-memory-bits}. -/)
  (title := /-- Polynomial bit encoding capacity -/)
  (latexEnv := "lemma")]
lemma prec2_configuration_cardinality {α : Type} [Fintype α] {s : ℕ}
    (hs : 0 < s) :
    Fintype.card (prec2_configuration α s) ≤ 2 ^ prec2_memory_bits s (Fintype.card α) := by
  classical
  have hcard : Fintype.card (prec2_configuration α s) =
      s ^ (s * Fintype.card α) * s * 2 ^ s * s := by
    simp [prec2_configuration, prec2_candidate_fintype, Fintype.ofEquiv_card,
      Nat.pow_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, hs.ne']
    rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]
  have htwo : ∀ n : ℕ, n ≤ 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Nat.pow_succ]
        have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        omega
  let k := Fintype.card α
  have htransitions : s ^ (s * k) ≤ 2 ^ (s * s * k) := by
    calc
      s ^ (s * k) ≤ (2 ^ s) ^ (s * k) :=
        Nat.pow_le_pow_left (htwo s) _
      _ = 2 ^ (s * s * k) := by
        simp [Nat.pow_mul, Nat.mul_assoc]
  have hproduct : s ^ (s * k) * s * 2 ^ s * s ≤ 2 ^ (s * s * k + 3 * s) := by
    have h1 := Nat.mul_le_mul htransitions (htwo s)
    have h2 := Nat.mul_le_mul h1 (le_refl (2 ^ s))
    have h3 := Nat.mul_le_mul h2 (htwo s)
    calc
      s ^ (s * k) * s * 2 ^ s * s ≤
          2 ^ (s * s * k) * 2 ^ s * 2 ^ s * 2 ^ s := h3
      _ = 2 ^ (s * s * k + 3 * s) := by
        rw [show s * s * k + 3 * s = s * s * k + s + s + s by omega]
        simp [Nat.pow_add, Nat.mul_assoc]
  have hexponent : s * s * k + 3 * s ≤ prec2_memory_bits s k := by
    let n := s + k + 1
    have hsN : s ≤ n := by dsimp [n]; omega
    have hkN : k ≤ n := by dsimp [n]; omega
    have hnpos : 0 < n := by simp [n]
    have hcube : s * s * k ≤ n ^ 3 := by
      simpa [Nat.pow_succ, Nat.mul_assoc] using
        Nat.mul_le_mul (Nat.mul_le_mul hsN hsN) hkN
    have hnCube : n ≤ n ^ 3 := Nat.le_pow (by omega)
    have hsum : s * s * k + 3 * s ≤ 4 * n ^ 3 := by
      calc
        s * s * k + 3 * s ≤ n ^ 3 + 3 * n :=
          Nat.add_le_add hcube (Nat.mul_le_mul_left 3 hsN)
        _ ≤ n ^ 3 + 3 * n ^ 3 :=
          Nat.add_le_add_left (Nat.mul_le_mul_left 3 hnCube) _
        _ = 4 * n ^ 3 := by omega
    have hpow : n ^ 3 ≤ n ^ 4 := Nat.pow_le_pow_right hnpos (by omega)
    exact hsum.trans (Nat.mul_le_mul_left 4 hpow) |>.trans_eq (by simp [prec2_memory_bits, n])
  rw [hcard]
  simpa [k] using hproduct.trans (Nat.pow_le_pow_right (by omega) hexponent)

@[blueprint "def:prec2-configuration-embedding"
  (statement := /-- Every abstract configuration injects into the Boolean vectors of the allocated polynomial width. -/)
  (title := /-- Boolean encoding of abstract configurations -/)
  (latexEnv := "definition")]
noncomputable def prec2_configuration_embedding {α : Type} [Fintype α] {s : ℕ}
    (hs : 0 < s) :
    prec2_configuration α s ↪ (Fin (prec2_memory_bits s (Fintype.card α)) → Bool) := by
  classical
  let m := prec2_memory_bits s (Fintype.card α)
  let eConfig := (Fintype.equivFin (prec2_configuration α s)).toEmbedding
  let eBound := Fin.castLEEmb (prec2_configuration_cardinality (α := α) hs)
  let eBits : (Fin m → Bool) ≃ Fin (2 ^ m) :=
    Fintype.equivFinOfCardEq (by simp)
  exact eConfig.trans (eBound.trans eBits.symm.toEmbedding)

@[blueprint "def:prec2-encode-configuration"
  (statement := /-- Encode an abstract learner configuration as a Boolean memory vector. -/)
  (title := /-- Configuration encoder -/)
  (latexEnv := "definition")]
noncomputable def prec2_encode_configuration {α : Type} [Fintype α] {s : ℕ}
    (hs : 0 < s) (c : prec2_configuration α s) :
    Fin (prec2_memory_bits s (Fintype.card α)) → Bool :=
  prec2_configuration_embedding hs c

@[blueprint "def:prec2-decode-configuration"
  (statement := /-- Decode a Boolean memory vector by taking the generalized inverse of the configuration encoder. -/)
  (title := /-- Configuration decoder -/)
  (latexEnv := "definition")]
noncomputable def prec2_decode_configuration {α : Type} [Fintype α] {s : ℕ}
    (hs : 0 < s) (v : Fin (prec2_memory_bits s (Fintype.card α)) → Bool) :
    prec2_configuration α s := by
  letI : Nonempty (prec2_configuration α s) :=
    ⟨prec2_universal_candidate hs, ⟨0, hs⟩⟩
  exact Function.invFun (prec2_encode_configuration hs) v

@[blueprint "lem:prec2-decode-encode"
  (statement := /-- Decoding an encoded abstract configuration returns the original configuration. -/)
  (proof := /-- The capacity bound \cref{lem:prec2-configuration-cardinality} justifies the embedding used in \cref{def:prec2-configuration-embedding}. Thus the encoder in \cref{def:prec2-encode-configuration} is injective, and the generalized inverse used in \cref{def:prec2-decode-configuration} is a left inverse of every injective function. -/)
  (title := /-- Left-inverse law for the configuration encoding -/)
  (latexEnv := "lemma")]
lemma prec2_decode_encode {α : Type} [Fintype α] {s : ℕ}
    (hs : 0 < s) (c : prec2_configuration α s) :
    prec2_decode_configuration hs (prec2_encode_configuration hs c) = c := by
  letI : Nonempty (prec2_configuration α s) :=
    ⟨prec2_universal_candidate hs, ⟨0, hs⟩⟩
  by_cases hcapacity : Fintype.card (prec2_configuration α s) ≤
      2 ^ prec2_memory_bits s (Fintype.card α)
  · exact Function.leftInverse_invFun (prec2_configuration_embedding hs).injective c
  · exact (hcapacity (prec2_configuration_cardinality hs)).elim

@[blueprint "def:prec2-configuration-step"
  (statement := /-- A symbol token advances the current candidate's state. A boundary token resets an accepting candidate, and otherwise replaces it by its key successor and starts that successor. -/)
  (title := /-- Token transition on abstract configurations -/)
  (latexEnv := "definition")]
noncomputable def prec2_configuration_step {α : Type} [Fintype α] {s : ℕ}
    (c : prec2_configuration α s) (token : Option α) : prec2_configuration α s :=
  match token with
  | some a => (c.1, c.1.step c.2 a)
  | none => if c.1.accept c.2 then (c.1, c.1.start)
      else let B := prec2_next_candidate c.1; (B, B.start)

@[blueprint "def:prec2-initial-configuration"
  (statement := /-- The initial abstract configuration consists of the least candidate at its start state. -/)
  (title := /-- Initial learner configuration -/)
  (latexEnv := "definition")]
noncomputable def prec2_initial_configuration {α : Type} [Fintype α] {s : ℕ}
    (hs : 0 < s) : prec2_configuration α s :=
  let A := prec2_first_candidate hs
  (A, A.start)

@[blueprint "lem:prec2-configuration-process-word"
  (statement := /-- Starting a candidate at its start state and processing one encoded word followed by a boundary yields the candidate update at that word, reset to its start state. -/)
  (proof := /-- Induction over the word and \cref{def:prec2-configuration-step} show that symbol tokens leave the candidate fixed and reproduce its DFA state fold. At the boundary, this terminal state is accepting exactly when the word belongs to the language from \cref{def:prec2-candidate-language}; the two branches are therefore exactly \cref{def:prec2-advance-candidate}, and both reset the resulting candidate to its start state. -/)
  (title := /-- Abstract transition over one complete word -/)
  (latexEnv := "lemma")]
lemma prec2_configuration_process_word {α : Type} [Fintype α] {s : ℕ}
    (A : prec2_candidate α s) (x : List α) :
    List.foldl prec2_configuration_step (A, A.start) (x.map some ++ [none]) =
      let B := prec2_advance_candidate A x; (B, B.start) := by
  classical
  have hsymbols : ∀ (q : Fin s),
      List.foldl prec2_configuration_step (A, q) (x.map some) =
        (A, List.foldl A.step q x) := by
    induction x with
    | nil => intro q; rfl
    | cons a x ih =>
        intro q
        simp only [List.map_cons, List.foldl_cons]
        rw [show prec2_configuration_step (A, q) (some a) = (A, A.step q a) by
          rfl]
        exact ih (A.step q a)
  rw [List.foldl_append, hsymbols]
  simp only [List.foldl_cons, List.foldl_nil]
  change (if A.accept (List.foldl A.step A.start x) then
      (A, A.start)
    else let B := prec2_next_candidate A; (B, B.start)) =
      let B := prec2_advance_candidate A x; (B, B.start)
  by_cases hx : x ∈ prec2_candidate_language A
  · have haccept : A.accept (List.foldl A.step A.start x) = true := by
      change A.accept (List.foldl A.step A.start x) = true at hx
      exact hx
    simp [haccept, prec2_advance_candidate, hx]
  · have hreject : A.accept (List.foldl A.step A.start x) = false := by
      cases h : A.accept (List.foldl A.step A.start x) with
      | false => rfl
      | true =>
          exfalso
          apply hx
          change A.accept (List.foldl A.step A.start x) = true
          exact h
    simp [hreject, prec2_advance_candidate, hx]

@[blueprint "def:prec2-streaming-generator"
  (statement := /-- The streaming generator encodes the abstract initial configuration, decodes and updates it on each token before re-encoding, and outputs the candidate DFA in the decoded configuration. -/)
  (title := /-- Encoded rank-iteration streaming generator -/)
  (latexEnv := "definition")]
noncomputable def prec2_streaming_generator {α : Type} [Fintype α] (s : ℕ)
    (hs : 0 < s) : streaming_generator α s where
  memoryBits := prec2_memory_bits s (Fintype.card α)
  initial := prec2_encode_configuration hs (prec2_initial_configuration hs)
  step v token := prec2_encode_configuration hs
    (prec2_configuration_step (prec2_decode_configuration hs v) token)
  output v := prec2_candidate_dfa (prec2_decode_configuration hs v).1

@[blueprint "def:prec2-generator-family"
  (statement := /-- The rank-iteration generator family assigns the encoded streaming generator to every finite alphabet and every positive state bound. -/)
  (title := /-- Rank-iteration generator family -/)
  (latexEnv := "definition")]
noncomputable def prec2_generator_family : generator_family where
  generator s hs := prec2_streaming_generator s hs

@[blueprint "def:prec2-candidate-sequence"
  (statement := /-- Along an enumeration, the candidate sequence starts from the least candidate and applies the candidate update to each successive enumerated word. -/)
  (title := /-- Candidate sequence along an enumeration -/)
  (latexEnv := "definition")]
noncomputable def prec2_candidate_sequence {α : Type} [Fintype α] {s : ℕ}
    (hs : 0 < s) {K : Language α} (w : language_enumeration K) :
    ℕ → prec2_candidate α s
  | 0 => prec2_first_candidate hs
  | t + 1 => prec2_advance_candidate (prec2_candidate_sequence hs w t) (w.1 t).1

@[blueprint "lem:prec2-stream-prefix-successor"
  (statement := /-- The token prefix through time $t+1$ is the prefix through time $t$ followed by the symbols of word $w(t)$ and one boundary token. -/)
  (proof := /-- Unfold \cref{def:stream-prefix}, split `List.ofFn` at its final entry, and distribute `flatMap` over the resulting append. -/)
  (title := /-- Successor decomposition of a stream prefix -/)
  (latexEnv := "lemma")]
lemma prec2_stream_prefix_successor {α : Type} {K : Language α}
    (w : language_enumeration K) (t : ℕ) :
    stream_prefix w (t + 1) =
      stream_prefix w t ++ ((w.1 t).1.map some ++ [none]) := by
  unfold stream_prefix
  rw [List.ofFn_succ_last, List.flatMap_append]
  simp

@[blueprint "lem:prec2-abstract-prefix-run"
  (statement := /-- Running the abstract token transition through the first $t$ enumerated words yields the $t$th candidate at its start state. -/)
  (proof := /-- Induct on $t$. The initial case is \cref{def:prec2-initial-configuration}. For the successor case, decompose the stream by \cref{lem:prec2-stream-prefix-successor}, apply the induction hypothesis, and process the final complete word using \cref{lem:prec2-configuration-process-word}; this is precisely the recursion in \cref{def:prec2-candidate-sequence}. -/)
  (title := /-- Abstract run invariant at word boundaries -/)
  (latexEnv := "lemma")]
lemma prec2_abstract_prefix_run {α : Type} [Fintype α] {s : ℕ}
    (hs : 0 < s) {K : Language α} (w : language_enumeration K) (t : ℕ) :
    List.foldl prec2_configuration_step (prec2_initial_configuration hs)
        (stream_prefix w t) =
      (prec2_candidate_sequence hs w t, (prec2_candidate_sequence hs w t).start) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [prec2_stream_prefix_successor, List.foldl_append, ih]
      rw [prec2_configuration_process_word]
      rfl

@[blueprint "lem:prec2-encoded-run"
  (statement := /-- Starting from an encoded configuration, the concrete Boolean-memory run over any token list is the encoding of the corresponding abstract run. -/)
  (proof := /-- Induct over the token list. At each transition, unfold \cref{def:prec2-streaming-generator}; the decoder cancels the current encoder by \cref{lem:prec2-decode-encode}, leaving the abstract transition before re-encoding. -/)
  (title := /-- Simulation of the abstract run by Boolean memory -/)
  (latexEnv := "lemma")]
lemma prec2_encoded_run {α : Type} [Fintype α] {s : ℕ}
    (hs : 0 < s) (c : prec2_configuration α s) (input : List (Option α)) :
    List.foldl (prec2_streaming_generator s hs).step
        (prec2_encode_configuration hs c) input =
      prec2_encode_configuration hs
        (List.foldl prec2_configuration_step c input) := by
  induction input generalizing c with
  | nil => rfl
  | cons token input ih =>
      simp only [List.foldl_cons]
      rw [show (prec2_streaming_generator s hs).step
            (prec2_encode_configuration hs c) token =
          prec2_encode_configuration hs (prec2_configuration_step c token) by
        simp [prec2_streaming_generator, prec2_decode_encode]]
      exact ih (prec2_configuration_step c token)

@[blueprint "lem:prec2-generated-language-sequence"
  (statement := /-- After the first $t$ enumerated words, the encoded generator outputs exactly the language of the $t$th candidate. -/)
  (proof := /-- Expand \cref{def:generated-language} and the family from \cref{def:prec2-generator-family}. The simulation \cref{lem:prec2-encoded-run} and boundary invariant \cref{lem:prec2-abstract-prefix-run} identify the final encoding, which decodes by \cref{lem:prec2-decode-encode}; the output definition is then \cref{def:prec2-candidate-language}. -/)
  (title := /-- Generated language equals the current candidate language -/)
  (latexEnv := "lemma")]
lemma prec2_generated_language_sequence {α : Type} [Fintype α] {s : ℕ}
    (hs : 0 < s) {K : Language α} (w : language_enumeration K) (t : ℕ) :
    generated_language prec2_generator_family s hs (stream_prefix w t) =
      prec2_candidate_language (prec2_candidate_sequence hs w t) := by
  rw [generated_language, streaming_generator_run]
  change finite_dfa_language
      ((prec2_streaming_generator s hs).output
        (List.foldl (prec2_streaming_generator s hs).step
          (prec2_streaming_generator s hs).initial (stream_prefix w t))) = _
  rw [show (prec2_streaming_generator s hs).initial =
      prec2_encode_configuration hs (prec2_initial_configuration hs) by rfl]
  rw [prec2_encoded_run, prec2_abstract_prefix_run]
  simp [prec2_streaming_generator, prec2_decode_encode, prec2_candidate_language]

@[blueprint "lem:prec2-candidate-sequence-bounded"
  (statement := /-- Along an enumeration of a bounded target language, every candidate key is at most the key of the padded target candidate. -/)
  (proof := /-- Induct on time. Initially this is \cref{lem:prec2-first-candidate-minimal}. If the current candidate accepts the next target word, \cref{def:prec2-advance-candidate} leaves it fixed. Otherwise the padded target accepts that word by \cref{lem:prec2-padded-candidate-language}, so \cref{lem:prec2-advance-bounded-by-target} preserves the upper bound. -/)
  (title := /-- The candidate sequence never passes the target -/)
  (latexEnv := "lemma")]
lemma prec2_candidate_sequence_bounded {α : Type} [Fintype α] {s : ℕ}
    (hs : 0 < s) (target : bounded_dfa α s)
    (w : language_enumeration (bounded_dfa_language target)) (t : ℕ) :
    prec2_candidate_key (prec2_candidate_sequence hs w t) ≤
      prec2_candidate_key (prec2_padded_candidate target) := by
  induction t with
  | zero => exact prec2_first_candidate_minimal hs _
  | succ t ih =>
      let A := prec2_candidate_sequence hs w t
      let x := (w.1 t).1
      have hxT : x ∈ prec2_candidate_language (prec2_padded_candidate target) := by
        rw [prec2_padded_candidate_language]
        exact (w.1 t).2
      by_cases hxA : x ∈ prec2_candidate_language A
      · simpa [prec2_candidate_sequence, prec2_advance_candidate, A, x, hxA] using ih
      · have h := prec2_advance_bounded_by_target ih hxA hxT
        simpa [prec2_candidate_sequence, A, x] using h.2

@[blueprint "lem:prec2-candidate-sequence-finite-difference"
  (statement := /-- Along every surjective enumeration of a bounded target, all sufficiently late candidate languages have finite symmetric difference from the target language. -/)
  (proof := /-- Candidate keys are bounded by \cref{lem:prec2-candidate-sequence-bounded}. Each successor step is either stationary or strictly increasing by \cref{lem:prec2-advance-bounded-by-target}, so the bounded natural-valued key sequence is eventually constant; injectivity from \cref{lem:prec2-candidate-key-injective} makes the candidates themselves constant. If the stabilized candidate omitted infinitely many target words, surjectivity would place an omitted word after the stabilization time, forcing another strict update, a contradiction. Thus the target-minus-candidate difference is finite. By \cref{lem:prec2-padded-candidate-language}, the padded candidate represents the target exactly, and the stabilized key is no larger than its key. If the reverse difference were infinite, \cref{lem:prec2-candidate-key-strict} would put the padded target strictly before the stabilized candidate, again a contradiction. The union of the two finite differences is the required symmetric difference. -/)
  (title := /-- Eventual finite symmetric difference of candidate languages -/)
  (latexEnv := "lemma")]
lemma prec2_candidate_sequence_finite_difference {α : Type} [Fintype α] {s : ℕ}
    (hs : 0 < s) (target : bounded_dfa α s)
    (w : language_enumeration (bounded_dfa_language target)) :
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      (language_symmetric_difference
        (prec2_candidate_language (prec2_candidate_sequence hs w t))
        (bounded_dfa_language target)).Finite := by
  classical
  let T := prec2_padded_candidate target
  let seq := prec2_candidate_sequence hs w
  have hbounded : ∀ t, prec2_candidate_key (seq t) ≤ prec2_candidate_key T := by
    intro t
    exact prec2_candidate_sequence_bounded hs target w t
  have hstep : ∀ t, prec2_candidate_key (seq t) ≤ prec2_candidate_key (seq (t + 1)) := by
    intro t
    let x := (w.1 t).1
    have hxT : x ∈ prec2_candidate_language T := by
      dsimp [T, x]
      rw [prec2_padded_candidate_language]
      exact (w.1 t).2
    by_cases hx : x ∈ prec2_candidate_language (seq t)
    · simpa [seq, prec2_candidate_sequence, prec2_advance_candidate, x, hx]
    · have h := prec2_advance_bounded_by_target (hbounded t) hx hxT
      simpa [seq, prec2_candidate_sequence, x] using h.1.le
  have hmono : Monotone (fun t => prec2_candidate_key (seq t)) :=
    monotone_nat_of_le_succ hstep
  obtain ⟨b, N, hconstant⟩ :=
    converges_of_monotone_of_bounded hmono hbounded
  let C := seq N
  have hstable : ∀ t, N ≤ t → seq t = C := by
    intro t ht
    apply prec2_candidate_key_injective
    rw [hconstant t ht, hconstant N (le_refl N)]
  have hmissing :
      (bounded_dfa_language target \ prec2_candidate_language C).Finite := by
    let seen : Finset (List α) := (Finset.range N).image fun n => (w.1 n).1
    apply (seen.finite_toSet).subset
    intro x hx
    obtain ⟨n, hn⟩ := w.2 ⟨x, hx.1⟩
    have hnval : (w.1 n).1 = x := congrArg Subtype.val hn
    have hnlt : n < N := by
      by_contra hnot
      have hNn : N ≤ n := Nat.le_of_not_gt hnot
      have hreject : (w.1 n).1 ∉ prec2_candidate_language (seq n) := by
        rw [hstable n hNn, hnval]
        exact hx.2
      have hacceptT : (w.1 n).1 ∈ prec2_candidate_language T := by
        dsimp [T]
        rw [prec2_padded_candidate_language]
        exact (w.1 n).2
      have hprogress :=
        (prec2_advance_bounded_by_target (hbounded n) hreject hacceptT).1
      have hsame : prec2_candidate_key (seq n) = prec2_candidate_key (seq (n + 1)) := by
        rw [hconstant n hNn, hconstant (n + 1) (by omega)]
      apply (ne_of_lt hprogress)
      simpa [seq, prec2_candidate_sequence] using hsame
    change x ∈ (seen : Set (List α))
    simp only [seen, Finset.mem_coe, Finset.mem_image, Finset.mem_range]
    exact ⟨n, hnlt, hnval⟩
  have hCTkey : prec2_candidate_key C ≤ prec2_candidate_key T := hbounded N
  have hTC : prec2_almost_inclusion T C := by
    dsimp [prec2_almost_inclusion, T]
    rw [prec2_padded_candidate_language]
    exact hmissing
  have hCT : prec2_almost_inclusion C T := by
    by_contra hnot
    have hstrict := prec2_candidate_key_strict hTC hnot
    exact (not_lt_of_ge hCTkey) hstrict
  refine ⟨N, ?_⟩
  intro t ht
  change (language_symmetric_difference
    (prec2_candidate_language (seq t)) (bounded_dfa_language target)).Finite
  rw [hstable t ht]
  rw [language_symmetric_difference]
  have hreverse :
      (prec2_candidate_language C \ bounded_dfa_language target).Finite := by
    dsimp [prec2_almost_inclusion, T] at hCT
    rw [prec2_padded_candidate_language] at hCT
    exact hCT
  exact hreverse.union hmissing

@[blueprint "lem:prec2-finite-symmetric-difference"
  (statement := /-- There exists a family $\mathcal A$ of symbol-by-symbol streaming generators with the following three properties. Its Boolean memory width is bounded by $C(s+|\Sigma|+1)^d$ for some $C,d\in\mathbb N$, uniformly over every finite alphabet $\Sigma$ and every positive state bound $s$; every output DFA has at most $s$ states; and, for every target DFA $A$ with at most $s$ states and every surjection $w:\mathbb N\twoheadrightarrow L(A)$, there exists $t_0\in\mathbb N$ such that, for every $t\geq t_0$, the language output after the first $t$ enumerated words has finite symmetric difference from $L(A)$. -/)
  (proof := /-- Take the family \cref{def:prec2-generator-family}. Its memory width is $4(s+|\Sigma|+1)^4$ by \cref{def:prec2-memory-bits}, so it satisfies \cref{def:uses-polynomial-space} with constants $C=d=4$. Every output is the finite DFA represented by a candidate and therefore has exactly $s$ states, which gives \cref{def:outputs-within-state-bound}. For an arbitrary bounded target and surjective enumeration, \cref{lem:prec2-candidate-sequence-finite-difference} supplies a time after which the current candidate language has finite symmetric difference from the target. The simulation identity \cref{lem:prec2-generated-language-sequence} identifies this candidate language with the generated language at every stream prefix, proving \cref{def:eventually-finite-symmetric-difference}. -/)
  (title := /-- Convergence of the $\prec_2$ iteration -/)
  (latexEnv := "lemma")]
lemma prec2_finite_symmetric_difference :
    ∃ F : generator_family,
      uses_polynomial_space F ∧
      outputs_within_state_bound F ∧
      eventually_finite_symmetric_difference F := by
  refine ⟨prec2_generator_family, ?_, ?_, ?_⟩
  · refine ⟨4, 4, ?_⟩
    intro α inst s hs
    change prec2_memory_bits s (Fintype.card α) ≤
      4 * (s + Fintype.card α + 1) ^ 4
    exact le_refl _
  · intro α inst s hs input
    change s ≤ s
    exact le_refl s
  · intro α inst s hs target w
    obtain ⟨t₀, ht₀⟩ := prec2_candidate_sequence_finite_difference hs target w
    refine ⟨t₀, ?_⟩
    intro t ht
    rw [prec2_generated_language_sequence]
    exact ht₀ t ht

@[blueprint "lem:finite-setoid-strict-chain-bound"
  (statement := /-- Let $X$ be a nonempty finite type and let $(R_k)_{k\in\mathbb{N}}$ be equivalence relations on $X$. If $R_k$ is strictly finer than $R_{k+1}$ for every $k<m$, then $m<|X|$. -/)
  (proof := /-- Each strict refinement induces a surjective, noninjective map from the quotient by $R_k$ to the quotient by $R_{k+1}$, so the quotient cardinality decreases strictly. After $m$ steps it is still positive because $X$ is nonempty, whereas the initial quotient has cardinality at most $|X|$. Summing the strict decreases gives $m<|X|$. -/)
  (title := /-- Length of a strict chain of finite setoids -/)
  (latexEnv := "lemma")]
lemma finite_setoid_strict_chain_bound {ι : Type} [Fintype ι] [Nonempty ι]
    (R : ℕ → Setoid ι) {m : ℕ}
    (hstrict : ∀ k < m, R k < R (k + 1)) :
    m < Fintype.card ι := by
  classical
  let c (k : ℕ) := Fintype.card (Quotient (R k))
  have hcard_strict : ∀ k < m, c (k + 1) < c k := by
    intro k hk
    rcases hstrict k hk with ⟨hRS, hnot⟩
    apply Fintype.card_lt_of_surjective_not_injective (Setoid.map_of_le hRS)
    · intro q
      refine Quotient.inductionOn q ?_
      intro x
      exact ⟨Quotient.mk (R k) x, rfl⟩
    · intro hinj
      apply hnot
      intro x y hxy
      apply Quotient.exact
      apply hinj
      exact Quotient.sound hxy
  have htelescope : ∀ n ≤ m, n + c n ≤ c 0 := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
        have hnlt : n < m := by omega
        have hstep := hcard_strict n hnlt
        have hih := ih (by omega)
        omega
  have hm := htelescope m le_rfl
  have hpos : 0 < c m := Fintype.card_pos_iff.mpr
    ⟨Quotient.mk (R m) (Classical.choice (inferInstance : Nonempty ι))⟩
  have hc0 : c 0 ≤ Fintype.card ι := Fintype.card_quotient_le (R 0)
  omega

@[blueprint "lem:finite-symmetric-difference-short-word"
  (statement := /-- Let $\Sigma$ be an alphabet, let $s\in\mathbb{N}$, and let $A$ and $B$ be DFAs over $\Sigma$, each with at most $s$ states. If $L(A)\mathbin{\triangle}L(B)$ is finite, then every $x\in L(A)\mathbin{\triangle}L(B)$ satisfies $|x|<2s-1$. -/)
  (proof := /-- Let $D=L(A)\mathbin{\triangle}L(B)$ as in \cref{def:language-symmetric-difference}, and choose $y\in D$ of maximal length. On the disjoint union of the state sets of $A$ and $B$, let $R_k$ identify two states when the languages accepted from those states, in the sense of \cref{def:bounded-dfa-language}, agree on every word of length at least $k$. For each $k\leq |y|$, split $y=uv$ with $|v|=k$. The states reached after reading $u$ are $R_{k+1}$-equivalent: a longer distinguishing continuation would produce a member of $D$ longer than $y$. They are not $R_k$-equivalent because $v$ distinguishes them. Thus $R_k<R_{k+1}$ for all $k<|y|+1$. By \cref{lem:finite-setoid-strict-chain-bound}, $|y|+1$ is smaller than the total number of states of $A$ and $B$, which is at most $2s$. Since $|x|\leq |y|$, it follows that $|x|<2s-1$. -/)
  (title := /-- Length cutoff for a finite symmetric difference -/)
  (latexEnv := "lemma")]
lemma finite_symmetric_difference_short_word {α : Type} {s : ℕ}
    (A B : bounded_dfa α s)
    (hfinite :
      (language_symmetric_difference
        (bounded_dfa_language A) (bounded_dfa_language B)).Finite)
    {x : List α}
    (hx : x ∈ language_symmetric_difference
      (bounded_dfa_language A) (bounded_dfa_language B)) :
    x.length < 2 * s - 1 := by
  classical
  let D := language_symmetric_difference
    (bounded_dfa_language A) (bounded_dfa_language B)
  have hmem_iff (w : List α) :
      w ∈ D ↔ ¬ (w ∈ bounded_dfa_language A ↔
        w ∈ bounded_dfa_language B) := by
    simp only [D, language_symmetric_difference, Set.mem_union, Set.mem_diff]
    tauto
  have hDfinite : D.Finite := hfinite
  have hxD : x ∈ D := hx
  have hnonempty : hDfinite.toFinset.Nonempty := by
    refine ⟨x, ?_⟩
    simpa using hxD
  have finite_has_max : ∀ (T : Finset (List α)), T.Nonempty →
      ∃ y ∈ T, ∀ z ∈ T, z.length ≤ y.length := by
    intro T hT
    induction T using Finset.induction_on with
    | empty => simp at hT
    | @insert a T ha ih =>
        by_cases hTne : T.Nonempty
        · obtain ⟨y, hyT, hymax⟩ := ih hTne
          by_cases hay : a.length ≤ y.length
          · refine ⟨y, Finset.mem_insert_of_mem hyT, ?_⟩
            intro z hz
            rcases Finset.mem_insert.mp hz with rfl | hzT
            · exact hay
            · exact hymax z hzT
          · refine ⟨a, Finset.mem_insert_self a T, ?_⟩
            intro z hz
            rcases Finset.mem_insert.mp hz with rfl | hzT
            · exact le_rfl
            · have := hymax z hzT
              omega
        · refine ⟨a, Finset.mem_insert_self a T, ?_⟩
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hzT
          · exact le_rfl
          · exact False.elim (hTne ⟨z, hzT⟩)
  obtain ⟨y, hyfin, hymax⟩ := finite_has_max hDfinite.toFinset hnonempty
  have hyD : y ∈ D := by
    simpa using hyfin
  have hxy : x.length ≤ y.length := by
    exact hymax x (by simpa using hxD)
  let stateLanguage :
      (Fin A.stateCount ⊕ Fin B.stateCount) → Language α
    | Sum.inl q => A.automaton.acceptsFrom q
    | Sum.inr q => B.automaton.acceptsFrom q
  let R : ℕ → Setoid (Fin A.stateCount ⊕ Fin B.stateCount) := fun k =>
    { r := fun p q => ∀ z : List α, k ≤ z.length →
        (z ∈ stateLanguage p ↔ z ∈ stateLanguage q)
      iseqv := by
        refine ⟨?_, ?_, ?_⟩
        · intro p z hz
          rfl
        · intro p q hpq z hz
          exact (hpq z hz).symm
        · intro p q r hpq hqr z hz
          exact (hpq z hz).trans (hqr z hz) }
  have mem_eval_append_A (u z : List α) :
      z ∈ A.automaton.acceptsFrom (A.automaton.eval u) ↔
        u ++ z ∈ bounded_dfa_language A := by
    change A.automaton.evalFrom
        (A.automaton.evalFrom A.automaton.start u) z ∈ A.automaton.accept ↔
      A.automaton.evalFrom A.automaton.start (u ++ z) ∈ A.automaton.accept
    rw [A.automaton.evalFrom_of_append]
  have mem_eval_append_B (u z : List α) :
      z ∈ B.automaton.acceptsFrom (B.automaton.eval u) ↔
        u ++ z ∈ bounded_dfa_language B := by
    change B.automaton.evalFrom
        (B.automaton.evalFrom B.automaton.start u) z ∈ B.automaton.accept ↔
      B.automaton.evalFrom B.automaton.start (u ++ z) ∈ B.automaton.accept
    rw [B.automaton.evalFrom_of_append]
  letI : Nonempty (Fin A.stateCount ⊕ Fin B.stateCount) :=
    ⟨Sum.inl A.automaton.start⟩
  have hstrict : ∀ k < y.length + 1, R k < R (k + 1) := by
    intro k hk
    have hky : k ≤ y.length := by omega
    let u := y.take (y.length - k)
    let v := y.drop (y.length - k)
    have huv : u ++ v = y := by
      exact List.take_append_drop (y.length - k) y
    have hulen : u.length = y.length - k := by
      simp [u, hky]
    have hvlen : v.length = k := by
      simp [v]
      omega
    have hle : R k ≤ R (k + 1) := by
      intro p q hpq z hz
      exact hpq z (by omega)
    refine ⟨hle, ?_⟩
    intro hreverse
    have hlong : R (k + 1)
        (Sum.inl (A.automaton.eval u))
        (Sum.inr (B.automaton.eval u)) := by
      intro z hz
      have hlength : y.length < (u ++ z).length := by
        simp only [List.length_append, hulen]
        omega
      have hnotmem : u ++ z ∉ D := by
        intro huzD
        have huzfin : u ++ z ∈ hDfinite.toFinset := by
          simpa using huzD
        have := hymax (u ++ z) huzfin
        omega
      have happiff : u ++ z ∈ bounded_dfa_language A ↔
          u ++ z ∈ bounded_dfa_language B := by
        exact Classical.byContradiction fun hnotiff =>
          hnotmem ((hmem_iff (u ++ z)).2 hnotiff)
      simpa only [stateLanguage, mem_eval_append_A, mem_eval_append_B] using happiff
    have hnotshort : ¬ R k
        (Sum.inl (A.automaton.eval u))
        (Sum.inr (B.automaton.eval u)) := by
      intro hshort
      have hviff := hshort v (by omega)
      have hyiff : y ∈ bounded_dfa_language A ↔
          y ∈ bounded_dfa_language B := by
        rw [← huv]
        simpa only [stateLanguage, mem_eval_append_A, mem_eval_append_B] using hviff
      exact (hmem_iff y).1 hyD hyiff
    exact hnotshort (hreverse hlong)
  have hchain := finite_setoid_strict_chain_bound R hstrict
  have hcard : Fintype.card (Fin A.stateCount ⊕ Fin B.stateCount) ≤ 2 * s := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    have hA := A.stateCount_le
    have hB := B.stateCount_le
    omega
  omega

@[blueprint "lem:bounded-length-language-cardinality"
  (statement := /-- Let $\Sigma$ be a finite alphabet of cardinality $k$, and let $n\in\mathbb{N}$. Then the number of words in $\Sigma^*$ of length strictly less than $n$ is $\sum_{i=0}^{n-1}k^i$. -/)
  (proof := /-- For each $m\in\mathbb{N}$, the words of length exactly $m$ form a finite set: their subtype is the type of length-$m$ vectors over $\Sigma$, whose cardinality is $k^m$. The sets of words of length less than $m$ are therefore finite by induction on $m$. For the cardinality formula, proceed again by induction on $n$. The assertion is immediate for $n=0$. For the successor step, the words of length less than $n+1$ are the disjoint union of the words of length less than $n$ and the words of length exactly $n$. Additivity of finite cardinality, the induction hypothesis, and the cardinality $k^n$ of the latter set give $\sum_{i=0}^{n-1}k^i+k^n=\sum_{i=0}^{n}k^i$, as required. -/)
  (title := /-- Number of words below a length cutoff -/)
  (latexEnv := "lemma")]
lemma bounded_length_language_cardinality {α : Type} [Fintype α] (n : ℕ) :
    ({x : List α | x.length < n} : Set (List α)).ncard =
      ∑ i ∈ Finset.range n, Fintype.card α ^ i := by
  classical
  have finite_length_eq (m : ℕ) :
      ({x : List α | x.length = m} : Set (List α)).Finite := by
    change Finite (List.Vector α m)
    infer_instance
  have finite_length_lt (m : ℕ) :
      ({x : List α | x.length < m} : Set (List α)).Finite := by
    induction m with
    | zero =>
        simp
    | succ m ih =>
        have hdecomp :
            {x : List α | x.length < m + 1} =
              {x : List α | x.length < m} ∪
                {x : List α | x.length = m} := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_union]
          omega
        rw [hdecomp]
        exact ih.union (finite_length_eq m)
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hdecomp :
          {x : List α | x.length < n + 1} =
            {x : List α | x.length < n} ∪ {x : List α | x.length = n} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_union]
        omega
      have hdisjoint : Disjoint
          {x : List α | x.length < n} {x : List α | x.length = n} := by
        rw [Set.disjoint_left]
        intro x hx hxeq
        exact (Nat.ne_of_lt hx) hxeq
      have hexact :
          ({x : List α | x.length = n} : Set (List α)).ncard =
            Fintype.card α ^ n := by
        change Nat.card (List.Vector α n) = Fintype.card α ^ n
        rw [Nat.card_eq_fintype_card, card_vector]
      rw [hdecomp, Set.ncard_union_eq hdisjoint (finite_length_lt n)
        (finite_length_eq n), ih, hexact, Finset.sum_range_succ]

@[blueprint "lem:geometric-word-count-is-big-o"
  (statement := /-- For every $s\in\mathbb{N}$, there exist $C,k_0\in\mathbb{N}$ such that, for every $k\in\mathbb{N}$ with $k_0\leq k$, one has $\sum_{0\leq i<2s-1} k^i\leq Ck^{2s-2}$, where the bounds use natural-number subtraction (so the sum is empty when $s=0$). -/)
  (proof := /-- Take $C=2s-1$ and $k_0=1$, with subtraction in $\mathbb N$, and fix $k\geq 1$. We prove by induction on $n\leq 2s-1$ that the sum of $k^i$ over $0\leq i<n$ is at most $n k^{2s-2}$. For $n=0$ the sum is empty. In the successor case, $n+1\leq 2s-1$ implies $n\leq 2s-2$, so monotonicity of powers for the positive integer $k$ gives $k^n\leq k^{2s-2}$. Adding this inequality to the induction hypothesis gives the asserted bound for $n+1$. Taking $n=2s-1$ proves the result. -/)
  (title := /-- Asymptotic bound for the geometric word count -/)
  (latexEnv := "lemma")]
lemma geometric_word_count_is_big_o (s : ℕ) :
    ∃ C k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (∑ i ∈ Finset.range (2 * s - 1), k ^ i) ≤ C * k ^ (2 * s - 2) := by
  refine ⟨2 * s - 1, 1, ?_⟩
  intro k hk
  have hsum : ∀ n : ℕ, n ≤ 2 * s - 1 →
      (∑ i ∈ Finset.range n, k ^ i) ≤ n * k ^ (2 * s - 2) := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ]
        calc
          (∑ i ∈ Finset.range n, k ^ i) + k ^ n ≤
              n * k ^ (2 * s - 2) + k ^ (2 * s - 2) := by
            exact Nat.add_le_add (ih (by omega)) (Nat.pow_le_pow_right hk (by omega))
          _ = (n + 1) * k ^ (2 * s - 2) := by simp [Nat.add_mul]
  exact hsum (2 * s - 1) (by omega)

@[blueprint "lem:long-word-intersection-finite-dfa"
  (statement := /-- Let $A$ be a finite DFA over an alphabet $\Sigma$, and let $n\in\mathbb N$. There exists a finite DFA $B$ such that, for every word $x\in\Sigma^*$, one has $x\in L(B)$ if and only if $x\in L(A)$ and $n\leq |x|$. -/)
  (proof := /-- Construct a DFA on $n+1$ states which records the input length, saturated at $n$, and accepts precisely its saturated state. Induction on the input word shows that evaluation from a state $q$ ends at the state indexed by $\min(q+|x|,n)$, so this DFA accepts exactly the words of length at least $n$. Intersect it with $A$ and reindex the product of their finite state types by a type of the form $\operatorname{Fin}(m)$, as required by \cref{def:finite-dfa}. The language identity in \cref{def:finite-dfa-language} then gives the claimed characterization. -/)
  (title := /-- Restriction of a finite DFA to long words -/)
  (latexEnv := "lemma")]
lemma long_word_intersection_finite_dfa {α : Type} (A : finite_dfa α) (n : ℕ) :
    ∃ B : finite_dfa α, ∀ x : List α,
      x ∈ finite_dfa_language B ↔
        x ∈ finite_dfa_language A ∧ n ≤ x.length := by
  classical
  let lengthAutomaton : DFA α (Fin (n + 1)) :=
    { step := fun q _ =>
        ⟨min (q.val + 1) n, Nat.lt_succ_iff.mpr (Nat.min_le_right _ _)⟩
      start := ⟨0, Nat.zero_lt_succ n⟩
      accept := {q | q.val = n} }
  have hEval (x : List α) (q : Fin (n + 1)) :
      (lengthAutomaton.evalFrom q x).val = min (q.val + x.length) n := by
    induction x generalizing q with
    | nil =>
        simp only [DFA.evalFrom_nil, List.length_nil, Nat.add_zero]
        exact (Nat.min_eq_left (Nat.le_of_lt_succ q.isLt)).symm
    | cons a x ih =>
        rw [DFA.evalFrom_cons, ih]
        simp only [lengthAutomaton, List.length_cons]
        by_cases hqn : q.val + 1 ≤ n
        · rw [Nat.min_eq_left hqn]
          congr 1
          omega
        · have hnq : n ≤ q.val + 1 := by omega
          rw [Nat.min_eq_right hnq]
          have hleft : min (n + x.length) n = n := Nat.min_eq_right (Nat.le_add_right n x.length)
          have hright : min (q.val + (x.length + 1)) n = n := Nat.min_eq_right (by omega)
          rw [hleft, hright]
  have hAccept (x : List α) :
      x ∈ lengthAutomaton.accepts ↔ n ≤ x.length := by
    rw [DFA.mem_accepts]
    change (lengthAutomaton.evalFrom lengthAutomaton.start x).val = n ↔ n ≤ x.length
    rw [hEval]
    simp only [lengthAutomaton]
    omega
  let B : finite_dfa α :=
    { stateCount := Fintype.card (Fin A.stateCount × Fin (n + 1))
      automaton := DFA.reindex (Fintype.equivFin _)
        (A.automaton.inter lengthAutomaton) }
  refine ⟨B, ?_⟩
  intro x
  change x ∈ (DFA.reindex (Fintype.equivFin _)
    (A.automaton.inter lengthAutomaton)).accepts ↔
      x ∈ A.automaton.accepts ∧ n ≤ x.length
  rw [DFA.accepts_reindex, DFA.accepts_inter]
  change (x ∈ A.automaton.accepts ∧ x ∈ lengthAutomaton.accepts) ↔
    x ∈ A.automaton.accepts ∧ n ≤ x.length
  rw [hAccept]

@[blueprint "lem:prec2-eventual-no-hallucination"
  (statement := /-- Let $\mathcal A$ be a generator family with polynomially bounded persistent memory. Assume that, for every finite alphabet $\Sigma$, every positive state bound $s$, and every finite input stream, the output DFA of $\mathcal A$ has at most $s$ states. Assume also that, for every at-most-$s$-state target DFA $T$ and every surjective enumeration of $L(T)$, the output language of $\mathcal A$ has finite symmetric difference from $L(T)$ at every sufficiently late time. Then there exists a generator family $\mathcal A^{\geq}$ with polynomially bounded persistent memory such that every sufficiently late output is contained in $L(T)$. Moreover, for each positive $s$, there exist $C,k_0\in\mathbb N$ such that, over every finite alphabet of cardinality $k\geq k_0$, for every at-most-$s$-state target and every surjective enumeration of its language, every sufficiently late output omits a finite set of at most $Ck^{2s-2}$ target words. -/)
  (proof := /-- For an alphabet $\Sigma$ and a positive state bound $s$, retain the memory vector, initial configuration, and token transition of $\mathcal A$. Given a memory configuration, let $A$ be the output DFA of $\mathcal A$. Apply \cref{lem:long-word-intersection-finite-dfa} with $n=2s-1$ to choose a finite output DFA accepting exactly $L(A)\cap\{x:|x|\geq 2s-1\}$. This changes only the output map, not the persistent configuration, so the polynomial bound in \cref{def:uses-polynomial-space} is inherited verbatim.

Fix an at-most-$s$-state target $T$ and a surjective enumeration of $L(T)$. By \cref{def:eventually-finite-symmetric-difference}, there is a time after which the symmetric difference of $L(A)$ and $L(T)$ is finite. At every such time, \cref{def:outputs-within-state-bound} allows $A$ to be regarded as an at-most-$s$-state DFA. If a word $x$ of length at least $2s-1$ belonged to exactly one of $L(A)$ and $L(T)$, then \cref{lem:finite-symmetric-difference-short-word} would give $|x|<2s-1$, a contradiction. Hence the two languages agree on every word of length at least $2s-1$, and therefore
\[
  L(\mathcal A^{\geq}(t))
  = L(T)\cap\{x:|x|\geq 2s-1\}.
\]
In particular, the output is contained in $L(T)$, as required by \cref{def:eventually-no-hallucination}, and every omitted target word has length less than $2s-1$. Induction on the cutoff, using the finiteness of the type of words of each fixed length, shows that the set of words below the cutoff is finite. By \cref{lem:bounded-length-language-cardinality}, its cardinality is exactly $\sum_{i<2s-1}|\Sigma|^i$. Applying \cref{lem:geometric-word-count-is-big-o} bounds the omitted set by $C|\Sigma|^{2s-2}$ for all sufficiently large alphabets, uniformly over the target and its enumeration. This is \cref{def:has-generation-gap-order}. -/)
  (title := /-- No-hallucination by removing short words -/)
  (latexEnv := "lemma")]
lemma prec2_eventual_no_hallucination (F : generator_family)
    (hspace : uses_polynomial_space F)
    (hbound : outputs_within_state_bound F)
    (hF : eventually_finite_symmetric_difference F) :
    ∃ F' : generator_family,
      uses_polynomial_space F' ∧
      eventually_no_hallucination F' ∧
      has_generation_gap_order F' := by
  classical
  let restrictDFA : ∀ {α : Type}, finite_dfa α → ℕ → finite_dfa α :=
    fun {α} A n => Classical.choose (long_word_intersection_finite_dfa A n)
  have restrictDFA_spec {α : Type} (A : finite_dfa α) (n : ℕ) (x : List α) :
      x ∈ finite_dfa_language (restrictDFA A n) ↔
        x ∈ finite_dfa_language A ∧ n ≤ x.length := by
    simpa only [restrictDFA] using
      (Classical.choose_spec (long_word_intersection_finite_dfa A n) x)
  let F' : generator_family :=
    { generator := fun s hs =>
        { memoryBits := (F.generator s hs).memoryBits
          initial := (F.generator s hs).initial
          step := (F.generator s hs).step
          output := fun m =>
            restrictDFA ((F.generator s hs).output m) (2 * s - 1) } }
  have generated_language_F'_iff {α : Type} [Fintype α]
      (s : ℕ) (hs : 0 < s) (input : List (Option α)) (x : List α) :
      x ∈ generated_language F' s hs input ↔
        x ∈ generated_language F s hs input ∧ 2 * s - 1 ≤ x.length := by
    simpa only [generated_language, F', streaming_generator_run] using
      (restrictDFA_spec
        ((F.generator s hs).output
          (streaming_generator_run (F.generator s hs) input))
        (2 * s - 1) x)
  have long_words_agree {α : Type} [Fintype α]
      (s : ℕ) (hs : 0 < s) (target : bounded_dfa α s)
      (input : List (Option α))
      (hfinite : (language_symmetric_difference
        (generated_language F s hs input)
        (bounded_dfa_language target)).Finite)
      (x : List α) (hxlong : 2 * s - 1 ≤ x.length) :
      x ∈ generated_language F s hs input ↔
        x ∈ bounded_dfa_language target := by
    let current : bounded_dfa α s :=
      { stateCount := ((F.generator s hs).output
          (streaming_generator_run (F.generator s hs) input)).stateCount
        stateCount_le := hbound s hs input
        automaton := ((F.generator s hs).output
          (streaming_generator_run (F.generator s hs) input)).automaton }
    have hfiniteCurrent :
        (language_symmetric_difference
          (bounded_dfa_language current)
          (bounded_dfa_language target)).Finite := by
      simpa only [current, bounded_dfa_language, generated_language,
        finite_dfa_language] using hfinite
    constructor
    · intro hxF
      by_contra hxTarget
      have hxSym : x ∈ language_symmetric_difference
          (bounded_dfa_language current) (bounded_dfa_language target) := by
        simp only [language_symmetric_difference, Set.mem_union, Set.mem_diff]
        left
        exact ⟨hxF, hxTarget⟩
      have hshort := finite_symmetric_difference_short_word
        current target hfiniteCurrent hxSym
      omega
    · intro hxTarget
      by_contra hxF
      have hxSym : x ∈ language_symmetric_difference
          (bounded_dfa_language current) (bounded_dfa_language target) := by
        simp only [language_symmetric_difference, Set.mem_union, Set.mem_diff]
        right
        exact ⟨hxTarget, hxF⟩
      have hshort := finite_symmetric_difference_short_word
        current target hfiniteCurrent hxSym
      omega
  have hspace' : uses_polynomial_space F' := by
    rcases hspace with ⟨C, d, hCd⟩
    refine ⟨C, d, ?_⟩
    intro α inst s hs
    simpa only [F'] using hCd (α := α) s hs
  have hnoHallucination : eventually_no_hallucination F' := by
    intro α inst s hs target w
    rcases hF s hs target w with ⟨t₀, ht₀⟩
    refine ⟨t₀, ?_⟩
    intro t ht
    intro x hx
    have hxParts := (generated_language_F'_iff s hs (stream_prefix w t) x).mp hx
    exact (long_words_agree s hs target (stream_prefix w t)
      (ht₀ t ht) x hxParts.2).mp hxParts.1
  have hgap : has_generation_gap_order F' := by
    intro s hs
    rcases geometric_word_count_is_big_o s with ⟨C, k₀, hC⟩
    refine ⟨C, k₀, ?_⟩
    intro α inst hk target w
    rcases hF s hs target w with ⟨t₀, ht₀⟩
    refine ⟨t₀, ?_⟩
    intro t ht
    let shortWords : Set (List α) := {x | x.length < 2 * s - 1}
    have hshortFinite : shortWords.Finite := by
      have finiteLengthEq (m : ℕ) :
          ({x : List α | x.length = m} : Set (List α)).Finite := by
        change Finite (List.Vector α m)
        infer_instance
      have finiteLengthLt (m : ℕ) :
          ({x : List α | x.length < m} : Set (List α)).Finite := by
        induction m with
        | zero => simp
        | succ m ih =>
            apply (ih.union (finiteLengthEq m)).subset
            intro x hx
            simp only [Set.mem_setOf_eq] at hx
            simp only [Set.mem_setOf_eq, Set.mem_union]
            omega
      exact finiteLengthLt (2 * s - 1)
    have hmissingSubset :
        (bounded_dfa_language target \
            generated_language F' s hs (stream_prefix w t)) ≤ shortWords := by
      intro x hx
      change x.length < 2 * s - 1
      by_contra hxnotShort
      have hxlong : 2 * s - 1 ≤ x.length := by omega
      have hxF : x ∈ generated_language F s hs (stream_prefix w t) :=
        (long_words_agree s hs target (stream_prefix w t)
          (ht₀ t ht) x hxlong).mpr hx.1
      have hxF' : x ∈ generated_language F' s hs (stream_prefix w t) :=
        (generated_language_F'_iff s hs (stream_prefix w t) x).mpr ⟨hxF, hxlong⟩
      exact hx.2 hxF'
    constructor
    · exact hshortFinite.subset hmissingSubset
    · calc
        (bounded_dfa_language target \
            generated_language F' s hs (stream_prefix w t)).ncard ≤
            shortWords.ncard := Set.ncard_le_ncard hmissingSubset hshortFinite
        _ = ∑ i ∈ Finset.range (2 * s - 1), Fintype.card α ^ i := by
          exact bounded_length_language_cardinality (α := α) (2 * s - 1)
        _ ≤ C * Fintype.card α ^ (2 * s - 2) := hC (Fintype.card α) hk
  exact ⟨F', hspace', hnoHallucination, hgap⟩

@[blueprint "thm:space-efficient-language-generation"
  (statement := /-- There exists a generator family $\mathcal A$, uniform over all finite alphabets $\Sigma$ and positive state bounds $s$, whose finite-memory machines read each input enumeration one alphabet symbol or word-boundary token at a time. There are constants $C,d\in\mathbb N$ such that every such machine has at most $C(s+|\Sigma|+1)^d$ persistent Boolean memory coordinates. For every DFA $T$ over $\Sigma$ with at most $s$ states and every surjection $w:\mathbb N\twoheadrightarrow L(T)$, there exists $t_0\in\mathbb N$ such that, for every $t\geq t_0$, the output language after the first $t$ enumerated words is contained in $L(T)$. Moreover, for every positive $s$ there exist $C_s,k_0\in\mathbb N$ such that, whenever $|\Sigma|\geq k_0$, for every such target $T$ and surjection $w$ there exists $t_0\in\mathbb N$ for which, at every $t\geq t_0$, the set of omitted target words is finite and has cardinality at most $C_s|\Sigma|^{2s-2}$. -/)
  (proof := /-- Choose the symbol-streaming generator family supplied by \cref{lem:prec2-finite-symmetric-difference}. It uses polynomial working space, each of its output DFAs has at most the target-state bound, and its output language eventually has finite symmetric difference from every target under every surjective enumeration. Apply \cref{lem:prec2-eventual-no-hallucination} to these three properties. The resulting post-processed family has the same polynomial-size persistent configuration, eventually outputs a sublanguage of the target, and has generation gap $O(k^{2s-2})$. These are exactly the three conclusions asserted by the theorem. -/)
  (title := /-- Space-efficient language generation -/)
  (latexEnv := "theorem")]
theorem space_efficient_language_generation :
    ∃ F : generator_family,
      uses_polynomial_space F ∧
      eventually_no_hallucination F ∧
      has_generation_gap_order F := by
  obtain ⟨F, hspace, hbound, hfinite⟩ := prec2_finite_symmetric_difference
  exact prec2_eventual_no_hallucination F hspace hbound hfinite

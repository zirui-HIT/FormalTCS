import Architect
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Countable.Defs

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:enumerates"
  (statement := /-- Let $U$ be a countable universe and let $L \subseteq U$ be a language.
    A function $e : \N \to U$ \emph{enumerates} $L$ when every value $e(n)$ lies in $L$
    and every element of $L$ occurs as some value; formally,
    $(\forall n \in \N,\ e(n) \in L) \wedge (\forall x \in L,\ \exists n \in \N,\ e(n) = x)$. -/)
  (title := /-- Enumeration of a Language -/)
  (latexEnv := "definition")]
def enumerates {U : Type*} (L : Set U) (e : ℕ → U) : Prop :=
  (∀ n, e n ∈ L) ∧ ∀ x ∈ L, ∃ n, e n = x

@[blueprint "def:prefix-seq"
  (statement := /-- For a function $e : \N \to U$ and a time $t \in \N$, the \emph{observed prefix}
    $\mathrm{prefixSeq}(e, t)$ is the finite ordered sequence $(e(0), e(1), \dots, e(t-1))$,
    obtained by mapping $e$ over the indices $0, 1, \dots, t-1$. It records the strings seen by
    a list identifier after $t$ observation steps. -/)
  (title := /-- Observed Prefix of an Enumeration -/)
  (latexEnv := "definition")]
def prefix_seq {U : Type*} (e : ℕ → U) (t : ℕ) : List U :=
  (List.range t).map e

@[blueprint "def:list-identifies"
  (statement := /-- Fix a collection $C : \N \to \mathcal{P}(U)$ and a list size $k \in \N$.
    Given a language $L \subseteq U$ and an output list $\mu : \mathrm{Fin}\,k \to \N$ of $k$ indices,
    we say $\mu$ \emph{contains the identity} of $L$, written $L \sqsubseteq \mu$, when there is a
    position $j \in \mathrm{Fin}\,k$ with $C(\mu(j)) = L$. -/)
  (title := /-- A List Contains the Identity of a Language -/)
  (latexEnv := "definition")]
def list_identifies {U : Type*} (C : ℕ → Set U) (L : Set U) {k : ℕ}
    (μ : Fin k → ℕ) : Prop :=
  ∃ j : Fin k, C (μ j) = L

@[blueprint "def:identifies-in-limit"
  (statement := /-- A $k$-list identifier $A : U^{\ast} \to (\mathrm{Fin}\,k \to \N)$
    \emph{identifies $C$ in the limit} when, for every index $z \in \N$ and every enumeration
    $e$ of the language $C(z)$ (\cref{def:enumerates}), there exists a finite time $t^{\star} \in \N$
    such that for all $t \ge t^{\star}$ the output list $A(\mathrm{prefixSeq}(e, t))$ contains the
    identity of $C(z)$ (\cref{def:prefix-seq}, \cref{def:list-identifies}). -/)
  (title := /-- List Identification in the Limit -/)
  (latexEnv := "definition")]
def identifies_in_limit {U : Type*} {k : ℕ} (C : ℕ → Set U)
    (A : List U → Fin k → ℕ) : Prop :=
  ∀ z : ℕ, ∀ e : ℕ → U, enumerates (C z) e →
    ∃ tStar : ℕ, ∀ t : ℕ, tStar ≤ t → list_identifies C (C z) (A (prefix_seq e t))

@[blueprint "def:identifiable"
  (statement := /-- A collection $C : \N \to \mathcal{P}(U)$ is \emph{identifiable in the limit with a
    list of size $k$} when there exists a $k$-list identifier $A : U^{\ast} \to (\mathrm{Fin}\,k \to \N)$
    that identifies $C$ in the limit (\cref{def:identifies-in-limit}). -/)
  (title := /-- Identifiability with a List of Size $k$ -/)
  (latexEnv := "definition")]
def identifiable {U : Type*} (C : ℕ → Set U) (k : ℕ) : Prop :=
  ∃ A : List U → Fin k → ℕ, identifies_in_limit C A

@[blueprint "def:angluin-predicate"
  (statement := /-- For a collection $C : \N \to \mathcal{P}(U)$, an index $i \in \N$, and a level
    $k \in \N$, the \emph{recursive tell-tale predicate} $\Psi(C, i, k)$ is defined by recursion on $k$.
    At level $0$ it is False (the convention $\Psi(\cdot, \cdot, 0) = \text{False}$). For $k \ge 1$,
    $\Psi(C, i, k)$ holds iff there exists a finite set $T \subseteq C(i)$ such that for every index $j$
    with $C(j) \subsetneq C(i)$, either $T \nsubseteq C(j)$ or $\Psi(C, j, k-1)$. In particular,
    $\Psi(C, i, 1)$ holds iff there is a finite $T \subseteq C(i)$ with $T \nsubseteq C(j)$ for every
    $C(j) \subsetneq C(i)$. -/)
  (title := /-- The Recursive Tell-Tale Predicate $\Psi$ -/)
  (latexEnv := "definition")]
def angluin_predicate {U : Type*} (C : ℕ → Set U) : ℕ → ℕ → Prop
  | _, 0 => False
  | i, (k + 1) =>
      ∃ T : Set U, T.Finite ∧ T ⊆ C i ∧
        ∀ j, C j ⊂ C i → (¬ (T ⊆ C j) ∨ angluin_predicate C j k)

@[blueprint "def:k-angluin-condition"
  (statement := /-- A collection $C : \N \to \mathcal{P}(U)$ \emph{satisfies the $k$-Angluin condition}
    when the recursive tell-tale predicate $\Psi(C, i, k)$ holds for every index $i \in \N$
    (\cref{def:angluin-predicate}). -/)
  (title := /-- The $k$-Angluin Condition -/)
  (latexEnv := "definition")]
def k_angluin_condition {U : Type*} (C : ℕ → Set U) (k : ℕ) : Prop :=
  ∀ i, angluin_predicate C i k

@[blueprint "def:telltale"
  (statement := /-- For a collection $C : \N \to \mathcal{P}(U)$, a level $m \in \N$, and an index
    $i \in \N$, the set $\mathrm{telltale}(C, m, i)$ is defined by cases on $m$: it is the empty set when
    $m = 0$, and when $m = m' + 1$ it is a fixed finite tell-tale set witnessing $\Psi(C, i, m)$
    (\cref{def:angluin-predicate}), selected by the axiom of choice when $\Psi(C, i, m)$ holds, and the
    empty set otherwise. -/)
  (title := /-- Tell-Tale Witness Selector -/)
  (latexEnv := "definition")]
noncomputable def telltale {U : Type*} (C : ℕ → Set U) : ℕ → ℕ → Set U
  | 0, _ => ∅
  | (m + 1), i =>
      @dite (Set U) (angluin_predicate C i (m + 1)) (Classical.propDecidable _)
        (fun h => h.choose) (fun _ => ∅)

@[blueprint "def:pick-index"
  (statement := /-- Given a collection $C : \N \to \mathcal{P}(U)$, a level $m \in \N$, a candidate
    index set $I \subseteq \N$, and an observed sample $S \subseteq U$, the index
    $\mathrm{pickIndex}(C, m, I, S)$ is the least index $i \in I$ such that $S \subseteq C(i)$ and
    $\mathrm{telltale}(C, m, i) \subseteq S$ (\cref{def:telltale}), if such an index exists, and $0$
    otherwise. -/)
  (title := /-- Least Consistent Candidate Index -/)
  (latexEnv := "definition")]
noncomputable def pick_index {U : Type*} (C : ℕ → Set U) (m : ℕ) (I : Set ℕ) (S : Set U) : ℕ :=
  @dite ℕ (∃ i, i ∈ I ∧ S ⊆ C i ∧ telltale C m i ⊆ S) (Classical.propDecidable _)
    (fun h => @Nat.find _ (Classical.decPred _) h) (fun _ => 0)

@[blueprint "def:list-identify"
  (statement := /-- Given a collection $C : \N \to \mathcal{P}(U)$, a list length $m \in \N$, a
    candidate index set $I \subseteq \N$, and an observed sample $S \subseteq U$, the tuple
    $\mathrm{listIdentify}(C, m, I, S) : \mathrm{Fin}\,m \to \N$ is defined by recursion on $m$: it is
    the empty tuple when $m = 0$, and when $m = m' + 1$ its first entry is
    $i^{\star} = \mathrm{pickIndex}(C, m, I, S)$ (\cref{def:pick-index}) and its remaining $m'$ entries
    are $\mathrm{listIdentify}(C, m', I', S)$ on the descended candidate set
    $I' = \{\, j : C(j) \subsetneq C(i^{\star}) \text{ and } \mathrm{telltale}(C, m, i^{\star}) \subseteq
    C(j) \,\}$ (\cref{def:telltale}). -/)
  (title := /-- Recursive List Identifier -/)
  (latexEnv := "definition")]
noncomputable def list_identify {U : Type*} (C : ℕ → Set U) :
    (m : ℕ) → Set ℕ → Set U → (Fin m → ℕ)
  | 0, _, _ => Fin.elim0
  | (m + 1), I, S =>
      Fin.cons (pick_index C (m + 1) I S)
        (list_identify C m
          {j | C j ⊂ C (pick_index C (m + 1) I S) ∧
            telltale C (m + 1) (pick_index C (m + 1) I S) ⊆ C j} S)

@[blueprint "lem:enum-covers-finite"
  (statement := /-- Let $L \subseteq U$ and let $e : \N \to U$ enumerate $L$ (\cref{def:enumerates}).
    Then for every finite subset $F \subseteq L$ there is a time $T \in \N$ such that for all $t \ge T$
    every element of $F$ occurs in the observed prefix $\mathrm{prefixSeq}(e, t)$
    (\cref{def:prefix-seq}); that is, $F \subseteq \{\, x : x \in \mathrm{prefixSeq}(e, t) \,\}$. -/)
  (proof := /-- We argue by induction on the finite set $F$. For $F = \emptyset$ take $T = 0$; the
    empty set is contained in every prefix. For the inductive step $F = \{a\} \cup s$ with $a \notin s$,
    the inductive hypothesis applied to $s \subseteq L$ yields a time $T_s$ with $s \subseteq
    \mathrm{prefixSeq}(e, t)$ for all $t \ge T_s$. Since $a \in L$, the enumeration property
    (\cref{def:enumerates}) provides an index $n_a$ with $e(n_a) = a$. Set $T = \max(T_s, n_a + 1)$.
    For $t \ge T$ we have $t \ge T_s$, so $s \subseteq \mathrm{prefixSeq}(e, t)$, and $n_a < t$, so
    $a = e(n_a) \in \mathrm{prefixSeq}(e, t)$; hence $\{a\} \cup s \subseteq \mathrm{prefixSeq}(e, t)$. -/)
  (title := /-- Finite Subsets Are Eventually Observed -/)
  (latexEnv := "lemma")]
lemma enum_covers_finite {U : Type*} (L : Set U) (e : ℕ → U)
    (he : enumerates L e) :
    ∀ F : Set U, F.Finite → F ⊆ L →
      ∃ T : ℕ, ∀ t : ℕ, T ≤ t → F ⊆ {x | x ∈ prefix_seq e t} := by
  intro F hF
  induction F, hF using Set.Finite.induction_on with
  | empty => exact fun _ => ⟨0, fun t _ x hx => (Set.mem_empty_iff_false x).mp hx |>.elim⟩
  | @insert a s ha hs ih =>
      intro hsub
      obtain ⟨Ts, hTs⟩ := ih (fun x hx => hsub (Set.mem_insert_of_mem a hx))
      obtain ⟨na, hna⟩ := he.2 a (hsub (Set.mem_insert a s))
      refine ⟨max Ts (na + 1), fun t ht x hx => ?_⟩
      rcases hx with rfl | hx
      · exact List.mem_map.mpr
          ⟨na, List.mem_range.mpr
            (lt_of_lt_of_le (Nat.lt_succ_self na) (le_trans (le_max_right _ _) ht)), hna⟩
      · exact hTs t (le_trans (le_max_left _ _) ht) hx

@[blueprint "lem:telltale-finite"
  (statement := /-- For every collection $C : \N \to \mathcal{P}(U)$, level $m \in \N$, and index
    $i \in \N$, the set $\mathrm{telltale}(C, m, i)$ (\cref{def:telltale}) is finite. -/)
  (proof := /-- We argue by cases on $m$. If $m = 0$ then $\mathrm{telltale}(C, 0, i) = \emptyset$
    (\cref{def:telltale}), which is finite. If $m = m' + 1$ then $\mathrm{telltale}(C, m' + 1, i)$ is,
    by definition (\cref{def:telltale}), either the chosen witness set of $\Psi(C, i, m' + 1)$ when that
    predicate holds, or $\emptyset$ otherwise. In the first case the chosen witness is finite by the
    defining property of $\Psi$ (\cref{def:angluin-predicate}); in the second case $\emptyset$ is
    finite. -/)
  (title := /-- Tell-Tale Sets Are Finite -/)
  (latexEnv := "lemma")]
lemma telltale_finite {U : Type*} (C : ℕ → Set U) (m i : ℕ) :
    (telltale C m i).Finite := by
  cases m with
  | zero => simp [telltale]
  | succ m' =>
      rw [telltale]
      by_cases h : angluin_predicate C i (m' + 1)
      · rw [dif_pos h]; exact h.choose_spec.1
      · rw [dif_neg h]; exact Set.finite_empty

@[blueprint "lem:telltale-spec"
  (statement := /-- Let $C : \N \to \mathcal{P}(U)$, let $i \in \N$ and $m \in \N$, and suppose
    $\Psi(C, i, m + 1)$ holds (\cref{def:angluin-predicate}). Then the tell-tale set
    $T = \mathrm{telltale}(C, m + 1, i)$ (\cref{def:telltale}) satisfies $T \subseteq C(i)$, and for
    every index $j$ with $C(j) \subsetneq C(i)$ either $T \nsubseteq C(j)$ or $\Psi(C, j, m)$ holds. -/)
  (proof := /-- Since $\Psi(C, i, m + 1)$ holds, the set $\mathrm{telltale}(C, m + 1, i)$ equals the
    witness $T$ chosen for $\Psi(C, i, m + 1)$ (\cref{def:telltale}). By the defining property of the
    predicate (\cref{def:angluin-predicate}), this witness is a finite subset $T \subseteq C(i)$ such
    that for every $j$ with $C(j) \subsetneq C(i)$, either $T \nsubseteq C(j)$ or $\Psi(C, j, m)$ holds.
    These are exactly the two asserted conclusions. -/)
  (title := /-- Defining Property of the Tell-Tale Selector -/)
  (latexEnv := "lemma")]
lemma telltale_spec {U : Type*} (C : ℕ → Set U) (i m : ℕ)
    (h : angluin_predicate C i (m + 1)) :
    telltale C (m + 1) i ⊆ C i ∧
      ∀ j, C j ⊂ C i → (¬ (telltale C (m + 1) i ⊆ C j) ∨ angluin_predicate C j m) := by
  have hpick : telltale C (m + 1) i = h.choose := by rw [telltale]; exact dif_pos h
  rw [hpick]
  exact ⟨h.choose_spec.2.1, h.choose_spec.2.2⟩

@[blueprint "lem:pick-index-spec"
  (statement := /-- Let $C : \N \to \mathcal{P}(U)$, $m \in \N$, $I \subseteq \N$, and $S \subseteq U$,
    and suppose there exists an index $i \in I$ with $S \subseteq C(i)$ and
    $\mathrm{telltale}(C, m, i) \subseteq S$ (\cref{def:telltale}). Then the chosen index
    $i^{\star} = \mathrm{pickIndex}(C, m, I, S)$ (\cref{def:pick-index}) itself satisfies
    $i^{\star} \in I$, $S \subseteq C(i^{\star})$, and $\mathrm{telltale}(C, m, i^{\star}) \subseteq S$,
    and moreover no index $i < i^{\star}$ satisfies all three of these feasibility conditions. -/)
  (proof := /-- Since a feasible index exists, $\mathrm{pickIndex}(C, m, I, S)$ is by definition the
    least natural number satisfying the feasibility predicate $i \in I \wedge S \subseteq C(i) \wedge
    \mathrm{telltale}(C, m, i) \subseteq S$ (\cref{def:pick-index}, \cref{def:telltale}). The
    minimization operator's specification gives that this least index itself satisfies the predicate,
    yielding $i^{\star} \in I$, $S \subseteq C(i^{\star})$, and $\mathrm{telltale}(C, m, i^{\star})
    \subseteq S$; and its minimality gives that no strictly smaller index satisfies the predicate. -/)
  (title := /-- The Chosen Index Is Least Feasible -/)
  (latexEnv := "lemma")]
lemma pick_index_spec {U : Type*} (C : ℕ → Set U) (m : ℕ) (I : Set ℕ) (S : Set U)
    (h : ∃ i, i ∈ I ∧ S ⊆ C i ∧ telltale C m i ⊆ S) :
    (pick_index C m I S ∈ I ∧ S ⊆ C (pick_index C m I S) ∧
        telltale C m (pick_index C m I S) ⊆ S) ∧
      ∀ i, i < pick_index C m I S → ¬ (i ∈ I ∧ S ⊆ C i ∧ telltale C m i ⊆ S) := by
  have hpick : pick_index C m I S = @Nat.find _ (Classical.decPred _) h := by
    rw [pick_index]; exact dif_pos h
  refine ⟨?_, ?_⟩
  · rw [hpick]; exact @Nat.find_spec _ (Classical.decPred _) h
  · intro i hi; rw [hpick] at hi; exact @Nat.find_min _ (Classical.decPred _) h i hi

@[blueprint "lem:eventually-all-below"
  (statement := /-- Let $P : \N \to \N \to \mathrm{Prop}$ be a family of predicates and let $N \in \N$.
    Suppose that for every index $i < N$ there is a threshold $T_i \in \N$ such that $P(t, i)$ holds for
    all $t \ge T_i$. Then there is a single threshold $T \in \N$ such that for all $t \ge T$ and all
    $i < N$, $P(t, i)$ holds. -/)
  (proof := /-- We argue by induction on $N$. For $N = 0$ take $T = 0$; there is no index $i < 0$, so
    the conclusion holds vacuously. For the inductive step $N = n + 1$, the inductive hypothesis applied
    to the restriction of the assumption to indices $i < n$ yields a threshold $T_0$ with $P(t, i)$ for
    all $t \ge T_0$ and all $i < n$. Applying the assumption to $i = n$ (which satisfies $n < n + 1$)
    yields a threshold $T_n$ with $P(t, n)$ for all $t \ge T_n$. Set $T = \max(T_0, T_n)$. For $t \ge T$
    and $i < n + 1$ we have $i < n$ or $i = n$: in the first case $t \ge T_0$ gives $P(t, i)$; in the
    second case $t \ge T_n$ gives $P(t, n)$. -/)
  (title := /-- Uniform Threshold over Finitely Many Indices -/)
  (latexEnv := "lemma")]
lemma eventually_all_below (P : ℕ → ℕ → Prop) :
    ∀ N : ℕ, (∀ i, i < N → ∃ Ti, ∀ t, Ti ≤ t → P t i) →
      ∃ T, ∀ t, T ≤ t → ∀ i, i < N → P t i := by
  intro N
  induction N with
  | zero => intro _; exact ⟨0, fun _ _ i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
      intro h
      obtain ⟨T0, hT0⟩ := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
      obtain ⟨Tn, hTn⟩ := h n (Nat.lt_succ_self n)
      refine ⟨max T0 Tn, fun t ht i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · exact hT0 t (le_trans (le_max_left _ _) ht) i hlt
      · subst heq; exact hTn t (le_trans (le_max_right _ _) ht)

@[blueprint "lem:pick-index-stabilizes"
  (statement := /-- Let $C : \N \to \mathcal{P}(U)$, $m \in \N$, $I \subseteq \N$, $z \in I$, and let
    $S : \N \to \mathcal{P}(U)$ be a sample sequence with $S(t) \subseteq C(z)$ for all $t$ and such that
    every finite subset of $C(z)$ is eventually contained in $S(t)$; suppose the tell-tale
    $\mathrm{telltale}(C, m, z) \subseteq C(z)$ (\cref{def:telltale}). Then there exist an index
    $i^{\star} \in I$ and a time $T$ such that $C(z) \subseteq C(i^{\star})$,
    $\mathrm{telltale}(C, m, i^{\star}) \subseteq C(z)$, and for all $t \ge T$ the picked index
    $\mathrm{pickIndex}(C, m, I, S(t)) = i^{\star}$ (\cref{def:pick-index}). -/)
  (proof := /-- Let $Q(i)$ abbreviate $i \in I \wedge C(z) \subseteq C(i) \wedge
    \mathrm{telltale}(C, m, i) \subseteq C(z)$. Since $z \in I$, $C(z) \subseteq C(z)$, and
    $\mathrm{telltale}(C, m, z) \subseteq C(z)$, the index $z$ satisfies $Q$, so a least such index
    $i^{\star}$ exists; it satisfies $i^{\star} \in I$, $C(z) \subseteq C(i^{\star})$, and
    $\mathrm{telltale}(C, m, i^{\star}) \subseteq C(z)$, and every $j < i^{\star}$ fails $Q$. Because
    $\mathrm{telltale}(C, m, i^{\star})$ is finite (\cref{lem:telltale-finite}) and contained in $C(z)$,
    the coverage hypothesis yields $T_1$ with $\mathrm{telltale}(C, m, i^{\star}) \subseteq S(t)$ for all
    $t \ge T_1$; together with $S(t) \subseteq C(z) \subseteq C(i^{\star})$ this makes $i^{\star}$
    feasible for all $t \ge T_1$. For each $j < i^{\star}$ the failure of $Q(j)$ makes $j$ eventually
    infeasible: if $j \notin I$ or $\mathrm{telltale}(C, m, j) \nsubseteq C(z)$ then $j$ is infeasible at
    every time (using $S(t) \subseteq C(z)$ for the latter), and if instead $C(z) \nsubseteq C(j)$ then
    some $x \in C(z) \setminus C(j)$ eventually appears in $S(t)$ by coverage, so $S(t) \nsubseteq C(j)$;
    aggregating these finitely many thresholds (\cref{lem:eventually-all-below}) gives $T_2$ with every
    $j < i^{\star}$ infeasible for $t \ge T_2$. For $t \ge \max(T_1, T_2)$ a feasible index exists, so
    $\mathrm{pickIndex}$ returns the least feasible index (\cref{lem:pick-index-spec}); it is
    $\le i^{\star}$ since $i^{\star}$ is feasible and $\ge i^{\star}$ since all smaller indices are
    infeasible, hence equals $i^{\star}$. -/)
  (title := /-- The Picked Index Stabilizes -/)
  (latexEnv := "lemma")]
lemma pick_index_stabilizes {U : Type*} (C : ℕ → Set U) (m : ℕ) (I : Set ℕ) (z : ℕ)
    (S : ℕ → Set U) (hsub : ∀ t, S t ⊆ C z)
    (hcov : ∀ F : Set U, F.Finite → F ⊆ C z → ∃ T, ∀ t, T ≤ t → F ⊆ S t)
    (hzI : z ∈ I) (hz_tt : telltale C m z ⊆ C z) :
    ∃ i₀ T, i₀ ∈ I ∧ C z ⊆ C i₀ ∧ telltale C m i₀ ⊆ C z ∧
      ∀ t, T ≤ t → pick_index C m I (S t) = i₀ := by
  classical
  have hex : ∃ i, i ∈ I ∧ C z ⊆ C i ∧ telltale C m i ⊆ C z :=
    ⟨z, hzI, subset_rfl, hz_tt⟩
  set i₀ := Nat.find hex with hi₀def
  have hi₀ : i₀ ∈ I ∧ C z ⊆ C i₀ ∧ telltale C m i₀ ⊆ C z := Nat.find_spec hex
  have hmin : ∀ j, j < i₀ → ¬ (j ∈ I ∧ C z ⊆ C j ∧ telltale C m j ⊆ C z) :=
    fun j hj => Nat.find_min hex hj
  obtain ⟨T1, hT1⟩ := hcov (telltale C m i₀) (telltale_finite C m i₀) hi₀.2.2
  have hfeas0 : ∀ t, T1 ≤ t → i₀ ∈ I ∧ S t ⊆ C i₀ ∧ telltale C m i₀ ⊆ S t :=
    fun t ht => ⟨hi₀.1, fun x hx => hi₀.2.1 (hsub t hx), hT1 t ht⟩
  have hbelow : ∀ j, j < i₀ → ∃ Tj, ∀ t, Tj ≤ t →
      ¬ (j ∈ I ∧ S t ⊆ C j ∧ telltale C m j ⊆ S t) := by
    intro j hj
    have hnotQ := hmin j hj
    by_cases hjI : j ∈ I
    · by_cases htt : telltale C m j ⊆ C z
      · have hnsub : ¬ (C z ⊆ C j) := fun h => hnotQ ⟨hjI, h, htt⟩
        rw [Set.not_subset] at hnsub
        obtain ⟨x, hxz, hxj⟩ := hnsub
        obtain ⟨Tj, hTj⟩ := hcov {x} (Set.finite_singleton x) (Set.singleton_subset_iff.mpr hxz)
        exact ⟨Tj, fun t ht hfeas =>
          hxj (hfeas.2.1 (hTj t ht (Set.mem_singleton_iff.mpr rfl)))⟩
      · rw [Set.not_subset] at htt
        obtain ⟨x, hxtt, hxz⟩ := htt
        exact ⟨0, fun t _ hfeas => hxz (hsub t (hfeas.2.2 hxtt))⟩
    · exact ⟨0, fun t _ hfeas => hjI hfeas.1⟩
  obtain ⟨T2, hT2⟩ := eventually_all_below
    (fun t j => ¬ (j ∈ I ∧ S t ⊆ C j ∧ telltale C m j ⊆ S t)) i₀ hbelow
  refine ⟨i₀, max T1 T2, hi₀.1, hi₀.2.1, hi₀.2.2, fun t ht => ?_⟩
  have ht1 : T1 ≤ t := le_trans (le_max_left _ _) ht
  have ht2 : T2 ≤ t := le_trans (le_max_right _ _) ht
  have hfeasi₀ : i₀ ∈ I ∧ S t ⊆ C i₀ ∧ telltale C m i₀ ⊆ S t := hfeas0 t ht1
  obtain ⟨hpickfeas, hpickmin⟩ := pick_index_spec C m I (S t) ⟨i₀, hfeasi₀⟩
  set p := pick_index C m I (S t) with hp
  have hle : p ≤ i₀ := not_lt.mp (fun hlt => (hpickmin i₀ hlt) hfeasi₀)
  have hge : i₀ ≤ p := not_lt.mp (fun hlt => (hT2 t ht2 p hlt) hpickfeas)
  exact le_antisymm hle hge

@[blueprint "lem:list-identify-converges"
  (statement := /-- Let $C : \N \to \mathcal{P}(U)$. For every list length $m \in \N$, candidate set
    $I \subseteq \N$, target index $z \in I$, and sample sequence $S : \N \to \mathcal{P}(U)$ with
    $S(t) \subseteq C(z)$ for all $t$, with every finite subset of $C(z)$ eventually contained in
    $S(t)$, and with $\Psi(C, j, m)$ holding for every $j \in I$ (\cref{def:angluin-predicate}), there
    is a time $T$ such that for all $t \ge T$ the output tuple
    $\mathrm{listIdentify}(C, m, I, S(t))$ (\cref{def:list-identify}) contains some entry naming
    $C(z)$; that is, there is $j \in \mathrm{Fin}\,m$ with $C(\mathrm{listIdentify}(C, m, I, S(t))(j))
    = C(z)$. -/)
  (proof := /-- We induct on $m$. If $m = 0$ then $\Psi(C, z, 0)$ is False (\cref{def:angluin-predicate}),
    contradicting the hypothesis that $\Psi(C, j, 0)$ holds for every $j \in I$ applied to $z \in I$;
    the claim is vacuous. For $m = n + 1$: the hypothesis gives $\Psi(C, z, n+1)$, so
    $\mathrm{telltale}(C, n+1, z) \subseteq C(z)$ (\cref{lem:telltale-spec}). By
    \cref{lem:pick-index-stabilizes} there are $i^{\star} \in I$ and $T_0$ with $C(z) \subseteq
    C(i^{\star})$, $\mathrm{telltale}(C, n+1, i^{\star}) \subseteq C(z)$, and
    $\mathrm{pickIndex}(C, n+1, I, S(t)) = i^{\star}$ for all $t \ge T_0$; hence for such $t$ the output
    equals $\mathrm{listIdentify}(C, n+1, I, S(t)) = \mathrm{cons}(i^{\star}, \mathrm{listIdentify}(C, n,
    I', S(t)))$ where $I' = \{\, j : C(j) \subsetneq C(i^{\star}) \text{ and }
    \mathrm{telltale}(C, n+1, i^{\star}) \subseteq C(j) \,\}$ (\cref{def:list-identify}). If
    $C(i^{\star}) = C(z)$, the first entry already names $C(z)$. Otherwise $C(z) \subsetneq C(i^{\star})$,
    so $z \in I'$; and for every $j \in I'$, since $C(j) \subsetneq C(i^{\star})$ and
    $\mathrm{telltale}(C, n+1, i^{\star}) \subseteq C(j)$, \cref{lem:telltale-spec} applied to
    $\Psi(C, i^{\star}, n+1)$ forces $\Psi(C, j, n)$. The inductive hypothesis applied to $n$, $I'$,
    $z$, and $S$ yields $T_1$ and, for each $t \ge T_1$, an index $j'$ with the tail output
    $\mathrm{listIdentify}(C, n, I', S(t))(j') = C(z)$. For $t \ge \max(T_0, T_1)$ the entry at position
    $j'+1$ of the full output equals that tail entry (\cref{def:list-identify}), naming $C(z)$. -/)
  (title := /-- Convergence of the Recursive List Identifier -/)
  (latexEnv := "lemma")]
lemma list_identify_converges {U : Type*} (C : ℕ → Set U) :
    ∀ (m : ℕ) (I : Set ℕ) (z : ℕ) (S : ℕ → Set U),
      (∀ t, S t ⊆ C z) →
      (∀ F : Set U, F.Finite → F ⊆ C z → ∃ T, ∀ t, T ≤ t → F ⊆ S t) →
      z ∈ I → (∀ j ∈ I, angluin_predicate C j m) →
      ∃ T, ∀ t, T ≤ t → ∃ j : Fin m, C ((list_identify C m I (S t)) j) = C z := by
  intro m
  induction m with
  | zero =>
      intro I z _ _ _ hzI hpsi
      exact absurd (hpsi z hzI) (by rw [angluin_predicate]; exact not_false)
  | succ n ih =>
      intro I z S hsub hcov hzI hpsi
      have hz_tt : telltale C (n + 1) z ⊆ C z := (telltale_spec C z n (hpsi z hzI)).1
      obtain ⟨i₀, T0, hi₀I, hzsub, htt_sub, hstab⟩ :=
        pick_index_stabilizes C (n + 1) I z S hsub hcov hzI hz_tt
      have heq : ∀ t, T0 ≤ t →
          list_identify C (n + 1) I (S t) =
            Fin.cons i₀ (list_identify C n
              {j | C j ⊂ C i₀ ∧ telltale C (n + 1) i₀ ⊆ C j} (S t)) := by
        intro t ht
        conv_lhs => rw [list_identify]
        rw [hstab t ht]
      by_cases hcase : C i₀ = C z
      · exact ⟨T0, fun t ht => ⟨0, by rw [heq t ht, Fin.cons_zero]; exact hcase⟩⟩
      · have hzss : C z ⊂ C i₀ := hzsub.ssubset_of_ne (Ne.symm hcase)
        have hpsi' : ∀ j ∈ {j | C j ⊂ C i₀ ∧ telltale C (n + 1) i₀ ⊆ C j},
            angluin_predicate C j n := by
          intro j hj
          rcases (telltale_spec C i₀ n (hpsi i₀ hi₀I)).2 j hj.1 with hno | hyes
          · exact absurd hj.2 hno
          · exact hyes
        have hzI' : z ∈ {j | C j ⊂ C i₀ ∧ telltale C (n + 1) i₀ ⊆ C j} := ⟨hzss, htt_sub⟩
        obtain ⟨T1, hT1⟩ := ih {j | C j ⊂ C i₀ ∧ telltale C (n + 1) i₀ ⊆ C j} z S
          hsub hcov hzI' hpsi'
        refine ⟨max T0 T1, fun t ht => ?_⟩
        obtain ⟨j', hj'⟩ := hT1 t (le_trans (le_max_right _ _) ht)
        exact ⟨j'.succ, by
          rw [heq t (le_trans (le_max_left _ _) ht), Fin.cons_succ]; exact hj'⟩

@[blueprint "lem:k-angluin-sufficient"
  (statement := /-- Let $U$ be countable, let $C : \N \to \mathcal{P}(U)$ be a collection of nonempty
    languages, and let $k \ge 1$. If $C$ satisfies the $k$-Angluin condition
    (\cref{def:k-angluin-condition}), then $C$ is identifiable in the limit with a list of size $k$
    (\cref{def:identifiable}). -/)
  (proof := /-- We exhibit a $k$-list identifier and show it identifies $C$ in the limit
    (\cref{def:identifies-in-limit}). As identifier we take, on any observed sample, the recursive
    list identifier $\mathrm{listIdentify}(C, k, \N, S)$ (\cref{def:list-identify}) with full initial
    candidate set $I = \N$, applied to the set $S = \{\, x : x \in \mathrm{prefixSeq}(e, t) \,\}$ of
    strings appearing in the observed prefix (\cref{def:prefix-seq}). To verify the
    identification-in-the-limit criterion (\cref{def:identifies-in-limit}), fix an index $z \in \N$ and
    an enumeration $e$ of $C(z)$ (\cref{def:enumerates}). Every string appearing in a prefix lies in
    $C(z)$, since each value $e(n)$ lies in $C(z)$ by \cref{def:enumerates}; hence the sample sequence
    $S_t = \{\, x : x \in \mathrm{prefixSeq}(e, t) \,\}$ satisfies $S_t \subseteq C(z)$ for all $t$.
    Moreover every finite subset of $C(z)$ is eventually contained in $S_t$ by
    \cref{lem:enum-covers-finite}. The target index $z$ lies in the full candidate set $\N$, and by
    hypothesis $\Psi(C, j, k)$ holds for every $j$ (\cref{def:angluin-predicate}), in particular for
    every $j \in \N$. Therefore \cref{lem:list-identify-converges}, applied with list length $k$,
    candidate set $\N$, target $z$, and sample sequence $S_t$, yields a time $t^{\star}$ such that for
    all $t \ge t^{\star}$ the output tuple $\mathrm{listIdentify}(C, k, \N, S_t)$ has an entry naming
    $C(z)$, i.e. contains the identity of $C(z)$ (\cref{def:list-identifies}). This is exactly the
    identification-in-the-limit criterion, so the identifier identifies $C$ in the limit and $C$ is
    identifiable with a list of size $k$ (\cref{def:identifiable}). -/)
  (title := /-- Sufficiency of the $k$-Angluin Condition (Upper Bound) -/)
  (latexEnv := "lemma")]
lemma k_angluin_sufficient {U : Type*} [Countable U] (C : ℕ → Set U)
    (hne : ∀ i, (C i).Nonempty) {k : ℕ} (hk : 1 ≤ k)
    (hC : k_angluin_condition C k) : identifiable C k := by
  refine ⟨fun L => list_identify C k Set.univ {x | x ∈ L}, ?_⟩
  intro z e he
  have hsub : ∀ t, {x | x ∈ prefix_seq e t} ⊆ C z := by
    intro t x hx
    simp only [Set.mem_setOf_eq, prefix_seq, List.mem_map, List.mem_range] at hx
    obtain ⟨n, _, rfl⟩ := hx
    exact he.1 n
  have hcov := enum_covers_finite (C z) e he
  obtain ⟨T, hT⟩ := list_identify_converges C k Set.univ z
    (fun t => {x | x ∈ prefix_seq e t}) hsub
    (fun F hF hFsub => hcov F hF hFsub) (Set.mem_univ z) (fun j _ => hC j)
  exact ⟨T, fun t ht => hT t ht⟩

@[blueprint "lem:enum-exists"
  (statement := /-- Let $U$ be a countable universe and let $L \subseteq U$ be a nonempty language.
    Then there exists a function $e : \N \to U$ that enumerates $L$ in the sense of
    \cref{def:enumerates}; that is, every value $e(n)$ lies in $L$, and every element of $L$ occurs as
    some value $e(n)$. -/)
  (proof := /-- Since $U$ is countable, the language $L$, viewed as a set, is countable. As $L$ is
    nonempty and countable, there is a function $f : \N \to U$ whose range equals $L$. Take $e := f$.
    For every $n \in \N$ we have $e(n) = f(n) \in \operatorname{range}(f) = L$. Conversely, for every
    $x \in L = \operatorname{range}(f)$ there is $n \in \N$ with $f(n) = x$, i.e. $e(n) = x$. Hence $e$
    enumerates $L$ in the sense of \cref{def:enumerates}. -/)
  (title := /-- Existence of an Enumeration of a Nonempty Countable Language -/)
  (latexEnv := "lemma")]
lemma enum_exists {U : Type*} [Countable U] (L : Set U) (hL : L.Nonempty) :
    ∃ e : ℕ → U, enumerates L e := by
  have hne : Nonempty L := hL.to_subtype
  obtain ⟨f, hf⟩ := exists_surjective_nat L
  refine ⟨fun n => (f n : U), ?_, ?_⟩
  · intro n
    exact (f n).2
  · intro x hx
    obtain ⟨y, hy⟩ := hf ⟨x, hx⟩
    exact ⟨y, by show (↑(f y) : U) = x; rw [hy]⟩

@[blueprint "lem:append-enum"
  (statement := /-- Let $U$ be a type, let $L \subseteq U$ be a language, let $\sigma$ be a finite list
    all of whose entries lie in $L$, and let $e : \N \to U$ enumerate $L$ (\cref{def:enumerates}).
    Then there exists a function $e' : \N \to U$ that enumerates $L$ and such that, for every
    $t \in \N$, the observed prefix of length $|\sigma| + t$ satisfies
    $\mathrm{prefixSeq}(e', |\sigma| + t) = \sigma \mathbin{+\!\!+} \mathrm{prefixSeq}(e, t)$
    (\cref{def:prefix-seq}). -/)
  (proof := /-- Define $e'(n) := \sigma[n]$ when $n < |\sigma|$ and $e'(n) := e(n - |\sigma|)$ otherwise.
    First, $e'$ enumerates $L$. For every $n$, if $n < |\sigma|$ then $e'(n) = \sigma[n]$ is an entry of
    $\sigma$, hence lies in $L$ by hypothesis; otherwise $e'(n) = e(n - |\sigma|) \in L$ since $e$
    enumerates $L$. For surjectivity, given $x \in L$ there is $m$ with $e(m) = x$ because $e$
    enumerates $L$, and then $e'(|\sigma| + m) = e((|\sigma| + m) - |\sigma|) = e(m) = x$. Second, we
    verify the prefix identity by comparing entries at each index $j < |\sigma| + t$. Both sides have
    length $|\sigma| + t$. If $j < |\sigma|$, the left entry is $e'(j) = \sigma[j]$ and the right entry
    is $\sigma[j]$. If $j \ge |\sigma|$, the left entry is $e'(j) = e(j - |\sigma|)$ and the right entry
    is $\mathrm{prefixSeq}(e, t)[j - |\sigma|] = e(j - |\sigma|)$. Hence the two lists agree. -/)
  (title := /-- Prepending a Finite List to an Enumeration -/)
  (latexEnv := "lemma")]
lemma append_enum {U : Type*} (L : Set U) (σ : List U) (hσ : ∀ x ∈ σ, x ∈ L)
    (e : ℕ → U) (he : enumerates L e) :
    ∃ e' : ℕ → U, enumerates L e' ∧
      ∀ t : ℕ, prefix_seq e' (σ.length + t) = σ ++ prefix_seq e t := by
  refine ⟨fun n => if h : n < σ.length then σ[n]'h else e (n - σ.length), ⟨?_, ?_⟩, ?_⟩
  · intro n
    by_cases h : n < σ.length
    · simp only [dif_pos h]
      exact hσ _ (List.getElem_mem h)
    · simp only [dif_neg h]
      exact he.1 _
  · intro x hx
    obtain ⟨m, hm⟩ := he.2 x hx
    refine ⟨σ.length + m, ?_⟩
    have h : ¬ (σ.length + m < σ.length) := by omega
    simp only [dif_neg h]
    rw [Nat.add_sub_cancel_left]
    exact hm
  · intro t
    apply List.ext_getElem
    · simp [prefix_seq]
    · intro j h1 h2
      simp only [prefix_seq, List.getElem_map, List.getElem_range]
      by_cases hj : j < σ.length
      · rw [List.getElem_append_left hj]
        simp only [dif_pos hj]
      · rw [List.getElem_append_right (by omega)]
        simp only [dif_neg hj, prefix_seq, List.getElem_map, List.getElem_range]

@[blueprint "lem:locking-seq"
  (statement := /-- Let $U$ be a countable universe, let $C : \N \to \mathcal{P}(U)$ be a collection of
    nonempty languages, let $n \in \N$, let $A : U^{\ast} \to (\mathrm{Fin}\,n \to \N)$ be a
    $n$-list identifier, let $i \in \N$, and let $\rho$ be a finite list all of whose entries lie in
    $C(i)$. Here $\rho$ is an arbitrary finite list serving as a fixed prefix. Assume that for every
    enumeration $e$ of $C(i)$ (\cref{def:enumerates}) there is a time
    $t^{\star}$ such that for all $t \ge t^{\star}$ some slot $p$ of $A(\rho \mathbin{+\!\!+}
    \mathrm{prefixSeq}(e, t))$ names $C(i)$, i.e. $C(A(\rho \mathbin{+\!\!+} \mathrm{prefixSeq}(e, t))(p))
    = C(i)$ (\cref{def:prefix-seq}). Then there exists a finite list $\sigma$ (a locking sequence),
    all of whose entries lie in $C(i)$, such that for every finite list $\tau$ with all entries in
    $C(i)$, some slot $p$ of $A(\rho \mathbin{+\!\!+} \sigma \mathbin{+\!\!+} \tau)$ names $C(i)$. -/)
  (proof := /-- Suppose, for contradiction, that no such $\sigma$ exists: for every finite list
    $\sigma$ with entries in $C(i)$ there is a finite list $\tau$ with entries in $C(i)$ such that
    every slot $p$ satisfies $C(A(\rho \mathbin{+\!\!+} \sigma \mathbin{+\!\!+} \tau)(p)) \ne C(i)$. By the
    axiom of choice, fix a function $\tau(\cdot)$ selecting such a bad extension for each list. Fix an
    enumeration $e_0$ of $C(i)$ (\cref{lem:enum-exists}). Define an increasing chain of finite lists by
    $g(0) = []$ and $g(m+1) = g(m) \mathbin{+\!\!+} [e_0(m)] \mathbin{+\!\!+} \tau(g(m) \mathbin{+\!\!+}
    [e_0(m)])$; every entry of every $g(m)$ lies in $C(i)$, and $g(m)$ is a prefix of $g(m+1)$, so
    $g(a)$ is a prefix of $g(b)$ whenever $a \le b$, and $|g(m)| \ge m$. Let $e^{\star}(m) := g(m+1)[m]$,
    which is well defined since $|g(m+1)| \ge m+1$. By prefix agreement along the chain, for every $m$
    and every $N$ with $m < |g(N)|$ we have $e^{\star}(m) = g(N)[m]$; consequently
    $\mathrm{prefixSeq}(e^{\star}, |g(N)|) = g(N)$ for all $N$. The function $e^{\star}$ enumerates
    $C(i)$: every value $g(m+1)[m]$ is an entry of $g(m+1)$, hence lies in $C(i)$; and for $x \in C(i)$
    there is $m$ with $e_0(m) = x$, and then $e^{\star}(|g(m)|) = g(m+1)[|g(m)|] = e_0(m) = x$. By the
    identification hypothesis applied to $e^{\star}$, there is $t^{\star}$ such that for all
    $t \ge t^{\star}$ some slot of $A(\rho \mathbin{+\!\!+} \mathrm{prefixSeq}(e^{\star}, t))$ names
    $C(i)$. Choose $N$ with $|g(N+1)| \ge t^{\star}$ (possible since $|g(N+1)| \ge N+1$). At
    $t = |g(N+1)|$ we have $\rho \mathbin{+\!\!+} \mathrm{prefixSeq}(e^{\star}, t) = \rho \mathbin{+\!\!+}
    g(N+1)$, and by construction $g(N+1) = (g(N) \mathbin{+\!\!+} [e_0(N)]) \mathbin{+\!\!+} \tau(g(N)
    \mathbin{+\!\!+} [e_0(N)])$ is a bad extension, so every slot $p$ satisfies $C(A(\rho \mathbin{+\!\!+}
    g(N+1))(p)) \ne C(i)$, contradicting that some slot names $C(i)$. -/)
  (title := /-- Existence of a Locking Sequence -/)
  (latexEnv := "lemma")]
lemma locking_seq {U : Type*} [Countable U] (C : ℕ → Set U) {n : ℕ}
    (A : List U → Fin n → ℕ) (i : ℕ) (ρ : List U)
    (hCi : (C i).Nonempty)
    (hid : ∀ e : ℕ → U, enumerates (C i) e →
      ∃ tStar : ℕ, ∀ t : ℕ, tStar ≤ t → ∃ p, C (A (ρ ++ prefix_seq e t) p) = C i) :
    ∃ σ : List U, (∀ x ∈ σ, x ∈ C i) ∧
      ∀ τ : List U, (∀ x ∈ τ, x ∈ C i) → ∃ p, C (A (ρ ++ σ ++ τ) p) = C i := by
  by_contra hcon
  push Not at hcon
  classical
  obtain ⟨e0, he0⟩ := enum_exists (C i) hCi
  obtain ⟨x0, hx0⟩ := hCi
  have gd : ∀ (l : List U) (m : ℕ) (h : m < l.length), l.getD m x0 = l[m] := by
    intro l m h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  set badτ : List U → List U :=
    fun σ => if h : ∀ x ∈ σ, x ∈ C i then (hcon σ h).choose else [] with hbadτ
  have hbadmem : ∀ σ : List U, (∀ x ∈ σ, x ∈ C i) → ∀ x ∈ badτ σ, x ∈ C i := by
    intro σ hσ x hx
    simp only [hbadτ, dif_pos hσ] at hx
    exact (hcon σ hσ).choose_spec.1 x hx
  have hbadne : ∀ σ : List U, (∀ x ∈ σ, x ∈ C i) →
      ∀ p, C (A (ρ ++ σ ++ badτ σ) p) ≠ C i := by
    intro σ hσ p
    have hbeq : badτ σ = (hcon σ hσ).choose := by simp only [hbadτ, dif_pos hσ]
    rw [hbeq]
    exact (hcon σ hσ).choose_spec.2 p
  let g : ℕ → List U := fun m =>
    Nat.rec ([] : List U) (fun m gm => (gm ++ [e0 m]) ++ badτ (gm ++ [e0 m])) m
  have hg0 : g 0 = [] := rfl
  have hgsucc : ∀ m, g (m + 1) = (g m ++ [e0 m]) ++ badτ (g m ++ [e0 m]) := fun _ => rfl
  have hgmem : ∀ m, ∀ x ∈ g m, x ∈ C i := by
    intro m
    induction m with
    | zero => intro x hx; rw [hg0] at hx; simp at hx
    | succ m ih =>
      intro x hx
      rw [hgsucc] at hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · rw [List.mem_append] at hx
        rcases hx with hx | hx
        · exact ih x hx
        · rw [List.mem_singleton] at hx; subst hx; exact he0.1 m
      · refine hbadmem _ ?_ x hx
        intro y hy
        rw [List.mem_append] at hy
        rcases hy with hy | hy
        · exact ih y hy
        · rw [List.mem_singleton] at hy; subst hy; exact he0.1 m
  have hgvalid : ∀ m, ∀ x ∈ g m ++ [e0 m], x ∈ C i := by
    intro m x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hgmem m x hx
    · rw [List.mem_singleton] at hx; subst hx; exact he0.1 m
  have hgpre : ∀ m, g m <+: g (m + 1) := by
    intro m
    rw [hgsucc]
    exact (List.prefix_append (g m) [e0 m]).trans (List.prefix_append _ _)
  have hgmono : ∀ a b, a ≤ b → g a <+: g b := by
    intro a b hab
    induction b with
    | zero => obtain rfl : a = 0 := Nat.le_zero.mp hab; exact List.prefix_rfl
    | succ b ih =>
      rcases Nat.lt_or_ge a (b + 1) with h | h
      · exact (ih (Nat.lt_succ_iff.mp h)).trans (hgpre b)
      · obtain rfl : a = b + 1 := le_antisymm hab h; exact List.prefix_rfl
  have hglen : ∀ m, m ≤ (g m).length := by
    intro m
    induction m with
    | zero => rw [hg0]; simp
    | succ m ih =>
      rw [hgsucc, List.length_append, List.length_append, List.length_singleton]
      omega
  let estar : ℕ → U := fun m => (g (m + 1)).getD m x0
  have hagree : ∀ N m, m < (g N).length → (g N).getD m x0 = estar m := by
    intro N m hm
    show (g N).getD m x0 = (g (m + 1)).getD m x0
    have hmm1 : m < (g (m + 1)).length :=
      lt_of_lt_of_le (Nat.lt_succ_self m) (hglen (m + 1))
    have hNM : g N <+: g (max N (m + 1)) := hgmono N _ (le_max_left _ _)
    have hm1M : g (m + 1) <+: g (max N (m + 1)) := hgmono (m + 1) _ (le_max_right _ _)
    rw [gd _ _ hm, gd _ _ hmm1, hNM.getElem hm, hm1M.getElem hmm1]
  have hpre : ∀ M, prefix_seq estar (g M).length = g M := by
    intro M
    apply List.ext_getElem
    · simp [prefix_seq]
    · intro j h1 h2
      simp only [prefix_seq, List.getElem_map, List.getElem_range]
      rw [← hagree M j h2, gd _ _ h2]
  have hestar : enumerates (C i) estar := by
    constructor
    · intro m
      show (g (m + 1)).getD m x0 ∈ C i
      have hmm1 : m < (g (m + 1)).length :=
        lt_of_lt_of_le (Nat.lt_succ_self m) (hglen (m + 1))
      rw [gd _ _ hmm1]
      exact hgmem (m + 1) _ (List.getElem_mem hmm1)
    · intro x hx
      obtain ⟨m, hm⟩ := he0.2 x hx
      refine ⟨(g m).length, ?_⟩
      have hlt : (g m).length < (g (m + 1)).length := by
        rw [hgsucc, List.length_append, List.length_append, List.length_singleton]
        omega
      have hkey := hagree (m + 1) (g m).length hlt
      rw [← hkey, hgsucc m]
      rw [gd _ _ (by rw [List.length_append, List.length_append, List.length_singleton]; omega)]
      rw [List.getElem_append_left (by rw [List.length_append, List.length_singleton]; omega),
        List.getElem_append_right (le_refl _)]
      simp [hm]
  obtain ⟨tStar, htStar⟩ := hid estar hestar
  have ht : tStar ≤ (g (tStar + 1)).length :=
    le_trans (by omega) (hglen (tStar + 1))
  obtain ⟨p, hp⟩ := htStar (g (tStar + 1)).length ht
  rw [hpre (tStar + 1)] at hp
  have hne := hbadne (g tStar ++ [e0 tStar]) (hgvalid tStar) p
  rw [hgsucc tStar, ← List.append_assoc] at hp
  exact hne hp

@[blueprint "lem:necessary-gen"
  (statement := /-- Let $U$ be a countable universe and let $C : \N \to \mathcal{P}(U)$ be a collection
    of nonempty languages. For every list size $n \in \N$, every $n$-list identifier
    $A : U^{\ast} \to (\mathrm{Fin}\,n \to \N)$, every finite list $\rho$, and every index $i \in \N$
    all of whose (that is, $\rho$'s) entries lie in $C(i)$, the following holds: if for every index $z$
    with $C(z) \subseteq C(i)$ whose (that is, $\rho$'s) entries all lie in $C(z)$ and every enumeration
    $e$ of $C(z)$ (\cref{def:enumerates}) there is a time $t^{\star}$ such that for all $t \ge t^{\star}$
    some slot $p$ of $A(\rho \mathbin{+\!\!+} \mathrm{prefixSeq}(e, t))$ names $C(z)$, i.e.
    $C(A(\rho \mathbin{+\!\!+} \mathrm{prefixSeq}(e, t))(p)) = C(z)$ (\cref{def:prefix-seq}), then the
    recursive tell-tale predicate $\Psi(C, i, n)$ holds (\cref{def:angluin-predicate}). -/)
  (proof := /-- We argue by induction on $n$, the statement being universally quantified over $A$,
    $\rho$, and $i$.

    In the base case $n = 0$, the predicate $\Psi(C, i, 0)$ is False by convention
    (\cref{def:angluin-predicate}), so it suffices to derive a contradiction. Since $C(i)$ is nonempty,
    it admits an enumeration $e$ (\cref{lem:enum-exists}). Applying the hypothesis at $z = i$, whose
    side conditions $C(i) \subseteq C(i)$ and $\rho \subseteq C(i)$ both hold, yields a time
    $t^{\star}$; taking $t = t^{\star}$ produces a slot $p \in \mathrm{Fin}\,0$. As $\mathrm{Fin}\,0$ is
    empty, this is impossible.

    In the inductive step from $n$ to $n + 1$, assume the statement for $n$. Fix $A$, $\rho$, $i$, the
    hypothesis $\rho \subseteq C(i)$, and the identification hypothesis $H$. Applying $H$ at $z = i$
    shows that for every enumeration of $C(i)$ some slot of $A(\rho \mathbin{+\!\!+} \cdot)$ eventually
    names $C(i)$, so by \cref{lem:locking-seq} there is a locking sequence $\sigma$ with entries in
    $C(i)$ such that for every finite list $\tau$ with entries in $C(i)$ some slot of
    $A(\rho \mathbin{+\!\!+} \sigma \mathbin{+\!\!+} \tau)$ names $C(i)$. Let
    $T := \{\, x : x \in \rho \mathbin{+\!\!+} \sigma \,\}$; it is finite and, since every entry of
    $\rho$ and of $\sigma$ lies in $C(i)$, satisfies $T \subseteq C(i)$. We verify the tell-tale
    condition for $\Psi(C, i, n+1)$ (\cref{def:angluin-predicate}) with this $T$. Fix $j$ with
    $C(j) \subsetneq C(i)$. If $T \nsubseteq C(j)$, the first disjunct holds. Otherwise $T \subseteq
    C(j)$, so all entries of $\rho \mathbin{+\!\!+} \sigma$ lie in $C(j)$, and we must show
    $\Psi(C, j, n)$.

    Define the residual $n$-list identifier $A'$ by $A'(w)(r) := A(w)(\mathrm{succAbove}(q(w), r))$,
    where $q(w) \in \mathrm{Fin}\,(n+1)$ is a slot with $C(A(w)(q(w))) = C(i)$ when such a slot exists
    and is $0$ otherwise, and $\mathrm{succAbove}(q(w), \cdot) : \mathrm{Fin}\,n \to \mathrm{Fin}\,(n+1)$
    is the order-preserving embedding whose image omits $q(w)$. We apply the induction hypothesis to
    $A'$, the prefix $\rho \mathbin{+\!\!+} \sigma$, and the index $j$. The prefix condition holds because
    $T \subseteq C(j)$. For the identification hypothesis, fix an index $z$ with $C(z) \subseteq C(j)$
    whose associated prefix condition gives $\rho \mathbin{+\!\!+} \sigma \subseteq C(z)$, and an
    enumeration $e$ of $C(z)$. Then $C(z) \subseteq C(i)$, and $C(z) \ne C(i)$ because $C(z) \subseteq
    C(j) \subsetneq C(i)$. Since every entry of $\sigma$ lies in $C(z)$, \cref{lem:append-enum} produces
    an enumeration $e'$ of $C(z)$ with $\mathrm{prefixSeq}(e', |\sigma| + t) = \sigma \mathbin{+\!\!+}
    \mathrm{prefixSeq}(e, t)$. Applying $H$ at $z$ with $e'$ (its side conditions $C(z) \subseteq C(i)$
    and $\rho \subseteq C(z)$ hold) yields a time $t_0$ such that for all $t \ge t_0$ some slot $p$
    satisfies $C(A(\rho \mathbin{+\!\!+} \sigma \mathbin{+\!\!+} \mathrm{prefixSeq}(e, t))(p)) = C(z)$,
    using $\rho \mathbin{+\!\!+} \mathrm{prefixSeq}(e', |\sigma| + t) = \rho \mathbin{+\!\!+} \sigma
    \mathbin{+\!\!+} \mathrm{prefixSeq}(e, t)$. Write $w := \rho \mathbin{+\!\!+} \sigma \mathbin{+\!\!+}
    \mathrm{prefixSeq}(e, t)$. Because the entries of $\mathrm{prefixSeq}(e, t)$ lie in $C(z) \subseteq
    C(i)$, the locking property yields a slot naming $C(i)$, so $q(w)$ is well defined and
    $C(A(w)(q(w))) = C(i)$. As $C(z) \ne C(i)$, the slot $p$ differs from $q(w)$, hence $p =
    \mathrm{succAbove}(q(w), r)$ for some $r \in \mathrm{Fin}\,n$; therefore $C(A'(w)(r)) =
    C(A(w)(p)) = C(z)$. This establishes the identification hypothesis for $A'$, so the induction
    hypothesis gives $\Psi(C, j, n)$, the second disjunct. Hence $\Psi(C, i, n+1)$ holds, completing
    the induction. -/)
  (title := /-- Relativized Necessity by Induction on the List Size -/)
  (latexEnv := "lemma")]
lemma necessary_gen {U : Type*} [Countable U] (C : ℕ → Set U)
    (hne : ∀ i, (C i).Nonempty) :
    ∀ (n : ℕ) (A : List U → Fin n → ℕ) (ρ : List U) (i : ℕ),
      (∀ x ∈ ρ, x ∈ C i) →
      (∀ z, C z ⊆ C i → (∀ x ∈ ρ, x ∈ C z) → ∀ e : ℕ → U, enumerates (C z) e →
        ∃ tStar, ∀ t, tStar ≤ t → ∃ p, C (A (ρ ++ prefix_seq e t) p) = C z) →
      angluin_predicate C i n := by
  classical
  intro n
  induction n with
  | zero =>
    intro A ρ i hρ H
    obtain ⟨e, he⟩ := enum_exists (C i) (hne i)
    obtain ⟨t0, ht0⟩ := H i subset_rfl hρ e he
    obtain ⟨p, _⟩ := ht0 t0 le_rfl
    exact p.elim0
  | succ n ih =>
    intro A ρ i hρ H
    obtain ⟨σ, hσmem, hσlock⟩ := locking_seq C A i ρ (hne i) (H i subset_rfl hρ)
    show ∃ T : Set U, T.Finite ∧ T ⊆ C i ∧
      ∀ j, C j ⊂ C i → (¬ (T ⊆ C j) ∨ angluin_predicate C j n)
    refine ⟨{x | x ∈ ρ ++ σ}, List.finite_toSet _, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hρ x h
      · exact hσmem x h
    · intro j hji
      by_cases hTj : {x | x ∈ ρ ++ σ} ⊆ C j
      · right
        set q : List U → Fin (n + 1) :=
          fun w => if h : ∃ p : Fin (n + 1), C (A w p) = C i then h.choose else 0 with hq
        set A' : List U → Fin n → ℕ := fun w r => A w ((q w).succAbove r) with hA'
        have hρnew : ∀ x ∈ ρ ++ σ, x ∈ C j := fun x hx => hTj hx
        have Hnew : ∀ z, C z ⊆ C j → (∀ x ∈ ρ ++ σ, x ∈ C z) →
            ∀ e : ℕ → U, enumerates (C z) e →
              ∃ tStar, ∀ t, tStar ≤ t →
                ∃ r, C (A' ((ρ ++ σ) ++ prefix_seq e t) r) = C z := by
          intro z hzj hρσz e he
          have hzi : C z ⊆ C i := hzj.trans hji.1
          have hzne : C z ≠ C i := by
            intro heq; rw [heq] at hzj; exact hji.2 hzj
          have hσz : ∀ x ∈ σ, x ∈ C z :=
            fun x hx => hρσz x (List.mem_append.mpr (Or.inr hx))
          have hρz : ∀ x ∈ ρ, x ∈ C z :=
            fun x hx => hρσz x (List.mem_append.mpr (Or.inl hx))
          obtain ⟨e', he', hpre'⟩ := append_enum (C z) σ hσz e he
          obtain ⟨t0, ht0⟩ := H z hzi hρz e' he'
          refine ⟨t0, fun t ht => ?_⟩
          obtain ⟨p, hp⟩ := ht0 (σ.length + t) (by omega)
          rw [hpre' t, ← List.append_assoc] at hp
          have hτ : ∀ x ∈ prefix_seq e t, x ∈ C i := by
            intro x hx
            simp only [prefix_seq, List.mem_map, List.mem_range] at hx
            obtain ⟨m, _, rfl⟩ := hx
            exact hzi (he.1 m)
          obtain ⟨pi, hpi⟩ := hσlock (prefix_seq e t) hτ
          set w := (ρ ++ σ) ++ prefix_seq e t with hw
          have hex : ∃ p : Fin (n + 1), C (A w p) = C i := ⟨pi, hpi⟩
          have hqw : C (A w (q w)) = C i := by
            simp only [hq]
            rw [dif_pos hex]
            exact hex.choose_spec
          have hpne : p ≠ q w := by
            intro h; apply hzne; rw [← hp, h]; exact hqw
          obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq hpne
          refine ⟨r, ?_⟩
          simp only [hA']
          rw [hr]
          exact hp
        exact ih A' (ρ ++ σ) j hρnew Hnew
      · left; exact hTj

@[blueprint "lem:k-angluin-necessary"
  (statement := /-- Let $U$ be countable, let $C : \N \to \mathcal{P}(U)$ be a collection of nonempty
    languages, and let $k \ge 1$. If $C$ is identifiable in the limit with a list of size $k$
    (\cref{def:identifiable}), then $C$ satisfies the $k$-Angluin condition
    (\cref{def:k-angluin-condition}). -/)
  (proof := /-- Since $C$ is identifiable with a list of size $k$ (\cref{def:identifiable}), fix a
    $k$-list identifier $A : U^{\ast} \to (\mathrm{Fin}\,k \to \N)$ that identifies $C$ in the limit
    (\cref{def:identifies-in-limit}). We must show that $\Psi(C, i, k)$ holds for every index $i$
    (\cref{def:k-angluin-condition}, \cref{def:angluin-predicate}); fix such an $i$. We invoke the
    relativized necessity statement \cref{lem:necessary-gen} with list size $k$, identifier $A$, empty
    prefix $\rho = []$, and index $i$. Its prefix hypothesis holds vacuously, as the empty list has no
    entries. For its identification hypothesis, fix an index $z$ with $C(z) \subseteq C(i)$ and an
    enumeration $e$ of $C(z)$ (\cref{def:enumerates}). Because $A$ identifies $C$ in the limit, there is
    a time $t^{\star}$ such that for all $t \ge t^{\star}$ the output list $A(\mathrm{prefixSeq}(e, t))$
    contains the identity of $C(z)$ (\cref{def:list-identifies}), i.e. some slot $p$ satisfies
    $C(A(\mathrm{prefixSeq}(e, t))(p)) = C(z)$; since $\rho = []$ we have
    $\rho \mathbin{+\!\!+} \mathrm{prefixSeq}(e, t) = \mathrm{prefixSeq}(e, t)$, so this is exactly the
    required conclusion. Therefore \cref{lem:necessary-gen} yields $\Psi(C, i, k)$. As $i$ was
    arbitrary, $C$ satisfies the $k$-Angluin condition (\cref{def:k-angluin-condition}). -/)
  (title := /-- Necessity of the $k$-Angluin Condition (Lower Bound) -/)
  (latexEnv := "lemma")]
lemma k_angluin_necessary {U : Type*} [Countable U] (C : ℕ → Set U)
    (hne : ∀ i, (C i).Nonempty) {k : ℕ} (hk : 1 ≤ k)
    (hId : identifiable C k) : k_angluin_condition C k := by
  obtain ⟨A, hA⟩ := hId
  intro i
  refine necessary_gen C hne k A [] i (by simp) ?_
  intro z hzi _ e he
  obtain ⟨tStar, htStar⟩ := hA z e he
  refine ⟨tStar, fun t ht => ?_⟩
  obtain ⟨p, hp⟩ := htStar t ht
  exact ⟨p, by simpa using hp⟩

@[blueprint "thm:k-list-identification-characterization"
  (statement := /-- Let $U$ be a countable universe and let $C = (L_1, L_2, \dots)$, presented as
    $C : \N \to \mathcal{P}(U)$, be a collection of nonempty languages, with list size $k \ge 1$.
    Then $C$ is identifiable in the limit with a list of size $k$ (\cref{def:identifiable}) if and only
    if $C$ satisfies the $k$-Angluin condition (\cref{def:k-angluin-condition}). -/)
  (proof := /-- The forward implication, that identifiability implies the $k$-Angluin condition, is
    \cref{lem:k-angluin-necessary}. The reverse implication, that the $k$-Angluin condition implies
    identifiability, is \cref{lem:k-angluin-sufficient}. Combining the two directions yields the stated
    equivalence. -/)
  (title := /-- Characterization of $k$-List Identification -/)
  (latexEnv := "theorem")]
theorem k_list_identification_characterization {U : Type*} [Countable U]
    (C : ℕ → Set U) (hne : ∀ i, (C i).Nonempty) {k : ℕ} (hk : 1 ≤ k) :
    identifiable C k ↔ k_angluin_condition C k := by
  exact ⟨k_angluin_necessary C hne hk, k_angluin_sufficient C hne hk⟩

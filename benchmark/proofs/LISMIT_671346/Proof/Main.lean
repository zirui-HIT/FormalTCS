import Architect
import Mathlib.Computability.Language
import Mathlib.Data.Set.Countable
import Mathlib.Data.Fintype.Card

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:palette"
  (statement := /-- Let $\Sigma$ be a finite alphabet with $k := |\Sigma|$ elements. The
    \emph{palette} is the finite set $P := \{0, 1, \dots, k\}$ of $k + 1$ colors, formalized
    as the finite type $\mathrm{Fin}(k + 1)$. -/)
  (title := /-- Palette of $k+1$ colors -/)
  (latexEnv := "definition")]
abbrev palette (α : Type*) [Fintype α] := Fin (Fintype.card α + 1)

@[blueprint "def:trace-coloring"
  (statement := /-- Let $\Sigma$ be a finite alphabet of size $k$. A \emph{trace coloring
    function} is a map $c : \Sigma^{*} \to P$ assigning to every finite string over $\Sigma$ a
    color in the palette $P$ of size $k + 1$ (\cref{def:palette}). -/)
  (title := /-- Trace coloring function -/)
  (latexEnv := "definition")]
abbrev trace_coloring (α : Type*) [Fintype α] := List α → palette α

@[blueprint "def:color-trace"
  (statement := /-- Let $c$ be a trace coloring function (\cref{def:trace-coloring}) over a
    finite alphabet $\Sigma$. For a string $x = x_1 x_2 \cdots x_n \in \Sigma^{*}$, the
    \emph{color trace} of $x$ under $c$ is the sequence
    $\mathrm{trace}_c(x) := (c(\varepsilon), c(x_{\le 1}), c(x_{\le 2}), \dots, c(x_{\le n}))$,
    where $x_{\le i} = x_1 \cdots x_i$ denotes the length-$i$ prefix of $x$ and $\varepsilon$ is
    the empty string. It has length $n + 1$. -/)
  (title := /-- Color trace of a string -/)
  (latexEnv := "definition")]
def color_trace {α : Type*} [Fintype α] (c : trace_coloring α) (x : List α) : List (palette α) :=
  (List.range (x.length + 1)).map (fun i => c (x.take i))

@[blueprint "def:annotated-string"
  (statement := /-- Over a finite alphabet $\Sigma$, an \emph{annotated string} is a pair
    $(x, \tau)$ consisting of a string $x \in \Sigma^{*}$ together with a sequence $\tau$ of
    colors drawn from the palette $P$ (\cref{def:palette}). It records a string paired with its
    color trace, as presented to the learner. -/)
  (title := /-- Annotated string -/)
  (latexEnv := "definition")]
abbrev annotated_string (α : Type*) [Fintype α] := List α × List (palette α)

@[blueprint "def:coloring-family"
  (statement := /-- Let $\Sigma$ be a finite alphabet of size $k$. A \emph{coloring family}
    $\{c_L\}_{L}$ assigns to each language $L$ over $\Sigma$ a trace coloring function
    $c_L$ (\cref{def:trace-coloring}) into the palette $P$ of size $k + 1$. -/)
  (title := /-- Coloring family -/)
  (latexEnv := "definition")]
abbrev coloring_family (α : Type*) [Fintype α] := Language α → trace_coloring α

@[blueprint "def:is-text"
  (statement := /-- Let $K$ be a language over a finite alphabet $\Sigma$. A \emph{text} for $K$
    is a function $t : \mathbb{N} \to \Sigma^{*}$ that enumerates exactly the strings of $K$;
    that is, for every string $x \in \Sigma^{*}$ one has $x \in K$ if and only if there exists
    $n \in \mathbb{N}$ with $t(n) = x$. -/)
  (title := /-- Text enumerating a language -/)
  (latexEnv := "definition")]
def is_text {α : Type*} (K : Language α) (t : ℕ → List α) : Prop :=
  ∀ x, x ∈ K ↔ ∃ n, t n = x

@[blueprint "def:learner"
  (statement := /-- Over a finite alphabet $\Sigma$, a \emph{learner} (identification algorithm)
    is a function $\mathcal{A}$ mapping every finite sequence of annotated strings
    (\cref{def:annotated-string}) to a guessed language, which is its current hypothesis for the
    target language. -/)
  (title := /-- Learner -/)
  (latexEnv := "definition")]
abbrev learner (α : Type*) [Fintype α] := List (annotated_string α) → Language α

@[blueprint "def:annotated-history"
  (statement := /-- Let $c$ be a trace coloring function (\cref{def:trace-coloring}) and
    $t : \mathbb{N} \to \Sigma^{*}$ a text. The \emph{annotated history} at time $n$ is the
    finite sequence
    $\big( (t(0), \mathrm{trace}_c(t(0))), \dots, (t(n-1), \mathrm{trace}_c(t(n-1))) \big)$
    of the first $n$ annotated strings (\cref{def:annotated-string}, \cref{def:color-trace})
    presented to the learner. -/)
  (title := /-- Annotated history at time $n$ -/)
  (latexEnv := "definition")]
def annotated_history {α : Type*} [Fintype α] (c : trace_coloring α) (t : ℕ → List α)
    (n : ℕ) : List (annotated_string α) :=
  (List.range n).map (fun i => (t i, color_trace c (t i)))

@[blueprint "def:identifies-in-limit"
  (statement := /-- Let $K$ be a language, $c$ a trace coloring function
    (\cref{def:trace-coloring}), $t$ a text, and $\mathcal{A}$ a learner (\cref{def:learner}).
    We say $\mathcal{A}$ \emph{identifies $K$ in the limit} from the enumeration $t$ annotated by
    $c$ if there exists a time $t^{*} \in \mathbb{N}$ such that for every $n \ge t^{*}$ the
    learner's guess on the annotated history at time $n$ (\cref{def:annotated-history}) is
    equal to $K$. -/)
  (title := /-- Identification of a language in the limit -/)
  (latexEnv := "definition")]
def identifies_in_limit {α : Type*} [Fintype α] (c : trace_coloring α) (t : ℕ → List α)
    (A : learner α) (K : Language α) : Prop :=
  ∃ tstar, ∀ n, tstar ≤ n → A (annotated_history c t n) = K

@[blueprint "def:identifiable-with-traces"
  (statement := /-- Let $\Sigma$ be a finite alphabet of size $k$ and $\mathcal{C}$ a collection
    of languages over $\Sigma$. The collection $\mathcal{C}$ is \emph{identifiable in the limit
    with color traces} if there exist a learner $\mathcal{A}$ (\cref{def:learner}) and a coloring
    family $\{c_L\}_{L}$ (\cref{def:coloring-family}) into a palette of size $k + 1$ such that for
    every language $K \in \mathcal{C}$ and every text $t$ for $K$ (\cref{def:is-text}), the
    learner $\mathcal{A}$ identifies $K$ in the limit (\cref{def:identifies-in-limit}) from the
    enumeration $t$ annotated by $c_K$. -/)
  (title := /-- Identifiability in the limit with color traces -/)
  (latexEnv := "definition")]
def identifiable_with_traces {α : Type*} [Fintype α] (C : Set (Language α)) : Prop :=
  ∃ (A : learner α) (cf : coloring_family α),
    ∀ K ∈ C, ∀ t : ℕ → List α, is_text K t → identifies_in_limit (cf K) t A K

@[blueprint "thm:main-theorem"
  (statement := /-- Let $\mathcal{C}$ be a countable collection of nonempty languages over a
    finite alphabet $\Sigma$ of size $k$. Then $\mathcal{C}$ is identifiable in the limit with
    color traces (\cref{def:identifiable-with-traces}); that is, there exist trace coloring
    functions $\{c_L\}_{L \in \mathcal{C}}$ mapping into a palette $P$ of size $k + 1$ and a
    learner that together make $\mathcal{C}$ identifiable in the limit with color traces. -/)
  (proof := /-- We give an explicit coloring family and learner. If the alphabet is empty
    (that is, $k = 0$), then $\Sigma^{*} = \{\varepsilon\}$, so every nonempty language equals
    $\{\varepsilon\}$ and the constant learner returning $\{\varepsilon\}$ identifies each of
    them; likewise if $\mathcal{C}$ is empty there is nothing to identify. Otherwise $k \ge 1$,
    so the palette $P$ of size $k + 1$ contains the two distinct colors $0$ and $1$. Since
    $\mathcal{C}$ is countable and nonempty, enumerate it as $\mathcal{C} = \{f(e) : e \in
    \mathbb{N}\}$ and, for each $K \in \mathcal{C}$, fix an index $e_K$ with $f(e_K) = K$.
    Color strings by length: define $c_K(w) = 1$ if $|w| \le e_K$ and $c_K(w) = 0$ otherwise.
    Then the color trace of a string $x$ under $c_K$ is $1^{\min(|x|+1,\, e_K+1)} 0^{\cdots}$;
    in particular it contains the color $0$ exactly when $|x| \ge e_K + 1$, and whenever it
    does its number of $1$'s equals $e_K + 1$. The learner inspects its annotated history: if
    some annotated string has a trace containing the color $0$, it reads off $e := (\text{number
    of } 1\text{'s}) - 1$ and outputs $f(e)$; otherwise it outputs the finite set of strings
    seen so far. Every string in a text for $K$ lies in $K = f(e_K)$, so any $0$-bearing trace
    in the history decodes to $e_K$ and yields $f(e_K) = K$. If $K$ contains a string of length
    $\ge e_K + 1$, that string eventually appears in the text, the decode branch fires from then
    on, and the guess is $K$. Otherwise every string of $K$ has length $\le e_K$, so $K$ is a
    subset of the finite set of strings of length $\le e_K$, hence finite; then no trace ever
    contains $0$, the learner always returns the set of seen strings, and this set equals $K$
    once every string of $K$ has been enumerated. In all cases the learner identifies $K$ in the
    limit, so $\mathcal{C}$ is identifiable in the limit with color traces
    (\cref{def:identifiable-with-traces}). -/)
  (title := /-- Identification in the Limit with $k+1$ Colors -/)
  (latexEnv := "theorem")]
theorem main_theorem {α : Type*} [Fintype α] (C : Set (Language α))
    (hCountable : C.Countable) (hNonempty : ∀ L ∈ C, L.Nonempty) :
    identifiable_with_traces C := by
  classical
  by_cases hcard : Fintype.card α = 0
  · have hempty : ∀ x : List α, x = [] := by
      intro x
      cases x with
      | nil => rfl
      | cons a t => exact absurd (Fintype.card_pos_iff.mpr ⟨a⟩) (by omega)
    refine ⟨fun _ => {[]}, fun _ => (fun _ => 0), ?_⟩
    intro K hK t ht
    refine ⟨0, fun n _ => ?_⟩
    show ({[]} : Language α) = K
    symm
    apply Set.eq_singleton_iff_unique_mem.mpr
    obtain ⟨y, hy⟩ := hNonempty K hK
    exact ⟨by rw [← hempty y]; exact hy, fun z _ => hempty z⟩
  haveI : Nontrivial (palette α) := by
    have h2 : 2 ≤ Fintype.card α + 1 := by
      have := Nat.one_le_iff_ne_zero.mpr hcard; omega
    exact Fin.nontrivial_iff_two_le.mpr h2
  have h10 : (1 : palette α) ≠ 0 := by
    intro hcontra
    have hv := congrArg Fin.val hcontra
    rw [Fin.val_zero] at hv
    rw [Fin.val_one'] at hv
    rw [Nat.mod_eq_of_lt (by omega)] at hv
    omega
  rcases C.eq_empty_or_nonempty with hCempty | hCne
  · refine ⟨fun _ => (∅ : Set (List α)), fun _ => (fun _ => 0), ?_⟩
    intro K hK
    simp [hCempty] at hK
  obtain ⟨f, hf⟩ := hCountable.exists_eq_range hCne
  set idx : Language α → ℕ := fun K => if h : ∃ e, f e = K then h.choose else 0 with hidx
  have hidx_spec : ∀ K ∈ C, f (idx K) = K := by
    intro K hK
    have hex : ∃ e, f e = K := by rw [hf, Set.mem_range] at hK; exact hK
    simp only [hidx, dif_pos hex]
    exact hex.choose_spec
  set cf : coloring_family α := fun K w => if w.length ≤ idx K then (1 : palette α) else 0 with hcf
  set A : learner α := fun hist =>
    match hist.find? (fun p => decide ((0 : palette α) ∈ p.2)) with
    | some p => f (p.2.count 1 - 1)
    | none => {x | x ∈ hist.map Prod.fst} with hA
  have hAsome : ∀ (hist : List (annotated_string α)) (p : annotated_string α),
      hist.find? (fun p => decide ((0 : palette α) ∈ p.2)) = some p →
      A hist = f (p.2.count 1 - 1) := by
    intro hist p hp; simp only [hA]; rw [hp]
  have hAnone : ∀ (hist : List (annotated_string α)),
      hist.find? (fun p => decide ((0 : palette α) ∈ p.2)) = none →
      A hist = {x | x ∈ hist.map Prod.fst} := by
    intro hist hp; simp only [hA]; rw [hp]
  have hcountP : ∀ (e m : ℕ), ((List.range m).countP (fun i => decide (i ≤ e))) = min m (e + 1) := by
    intro e m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.countP_append, ih]
      have hsingle : ([k].countP (fun i => decide (i ≤ e))) = if k ≤ e then 1 else 0 := by
        by_cases hk : k ≤ e
        · rw [if_pos hk]; simp [List.countP_cons, hk]
        · rw [if_neg hk]; simp [List.countP_cons, hk]
      rw [hsingle]
      by_cases hk : k ≤ e
      · rw [if_pos hk]; omega
      · rw [if_neg hk]; omega
  have hcnt : ∀ (e n : ℕ),
      ((List.range n).map (fun i => if i ≤ e then (1 : palette α) else 0)).count 1 = min n (e + 1) := by
    intro e n
    rw [List.count_eq_countP, List.countP_map, ← hcountP e n]
    apply List.countP_congr
    intro i _
    simp only [Function.comp_apply]
    by_cases h : i ≤ e
    · rw [if_pos h]; simp [h]
    · rw [if_neg h]; simp only [decide_eq_true_eq, h, decide_false, iff_false]
      simpa using h10.symm
  have hzero_mem : ∀ (e n : ℕ),
      (0 : palette α) ∈ ((List.range n).map (fun i => if i ≤ e then (1 : palette α) else 0)) ↔ e + 1 < n := by
    intro e n
    rw [List.mem_map]
    constructor
    · rintro ⟨i, hi, hv⟩
      rw [List.mem_range] at hi
      by_cases h : i ≤ e
      · rw [if_pos h] at hv; exact absurd hv h10
      · omega
    · intro he
      exact ⟨e + 1, List.mem_range.mpr (by omega), by rw [if_neg (by omega)]⟩
  haveI : Finite α := Finite.of_fintype α
  have hfin_le : ∀ m : ℕ, {l : List α | l.length ≤ m}.Finite := by
    have key : ∀ m : ℕ, ∃ L : List (List α), ∀ l : List α, l.length ≤ m → l ∈ L := by
      intro m
      induction m with
      | zero => exact ⟨[[]], fun l hl => by
          have : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)
          simp [this]⟩
      | succ k ih =>
        obtain ⟨L, hL⟩ := ih
        refine ⟨L ++ (Finset.univ : Finset α).toList.flatMap (fun a => L.map (fun l => a :: l)), ?_⟩
        intro l hl
        cases l with
        | nil => exact List.mem_append_left _ (hL [] (by simp))
        | cons a t =>
          apply List.mem_append_right
          rw [List.mem_flatMap]
          exact ⟨a, Finset.mem_toList.mpr (Finset.mem_univ a),
            List.mem_map.mpr ⟨t, hL t (by simpa using Nat.le_of_succ_le_succ hl), rfl⟩⟩
    intro m
    obtain ⟨L, hL⟩ := key m
    exact Set.Finite.subset L.finite_toSet (fun l hl => hL l hl)
  have hbd : ∀ (s : Set ℕ), s.Finite → ∃ b, ∀ n ∈ s, n ≤ b := by
    intro s hs
    refine hs.induction_on _ ⟨0, by simp⟩ ?_
    rintro a t _ _ ⟨b, hb⟩
    refine ⟨max a b, ?_⟩
    intro n hn
    rcases hn with rfl | hn
    · exact le_max_left _ _
    · exact le_trans (hb n hn) (le_max_right _ _)
  refine ⟨A, cf, ?_⟩
  intro K hK t ht
  set e := idx K with he
  have hfeK : f e = K := hidx_spec K hK
  have Ftrace : ∀ x : List α,
      color_trace (cf K) x
        = (List.range (x.length + 1)).map (fun i => if i ≤ e then (1 : palette α) else 0) := by
    intro x
    unfold color_trace
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp only [hcf]
    have hlen : (x.take i).length = i := by rw [List.length_take]; omega
    rw [hlen]
  have htmem : ∀ j, t j ∈ K := fun j => (ht (t j)).mpr ⟨j, rfl⟩
  have hdecode : ∀ (n : ℕ) (p : annotated_string α),
      (annotated_history (cf K) t n).find? (fun p => decide ((0 : palette α) ∈ p.2)) = some p →
      A (annotated_history (cf K) t n) = K := by
    intro n p hp
    rw [hAsome _ p hp]
    have hpmem : p ∈ annotated_history (cf K) t n := List.mem_of_find?_eq_some hp
    unfold annotated_history at hpmem
    rw [List.mem_map] at hpmem
    obtain ⟨j, hj, hpj⟩ := hpmem
    rw [List.mem_range] at hj
    have hpred : (0 : palette α) ∈ p.2 := by
      have := List.find?_some hp
      simpa using this
    subst hpj
    simp only at hpred ⊢
    rw [Ftrace (t j)] at hpred ⊢
    rw [hzero_mem e ((t j).length + 1)] at hpred
    rw [hcnt e ((t j).length + 1)]
    have : min ((t j).length + 1) (e + 1) = e + 1 := by omega
    rw [this]
    simpa using hfeK
  by_cases hlong : ∃ x ∈ K, e + 1 ≤ x.length
  · obtain ⟨x, hxK, hxlen⟩ := hlong
    obtain ⟨m, hm⟩ := (ht x).mp hxK
    refine ⟨m + 1, fun n hn => ?_⟩
    have hxm : x = t m := hm.symm
    have hzero : (0 : palette α) ∈ color_trace (cf K) (t m) := by
      rw [Ftrace (t m)]
      rw [hzero_mem e ((t m).length + 1)]
      rw [← hxm]; omega
    have hpair : (t m, color_trace (cf K) (t m)) ∈ annotated_history (cf K) t n := by
      unfold annotated_history
      rw [List.mem_map]
      exact ⟨m, List.mem_range.mpr (by omega), rfl⟩
    rcases hfind : (annotated_history (cf K) t n).find?
        (fun p => decide ((0 : palette α) ∈ p.2)) with _ | p
    · exfalso
      have := (List.find?_eq_none).mp hfind (t m, color_trace (cf K) (t m)) hpair
      simp only [decide_eq_true_eq] at this
      exact this hzero
    · exact hdecode n p hfind
  · have hlong2 : ∀ x ∈ K, x.length ≤ e := by
      intro x hx
      by_contra h
      exact hlong ⟨x, hx, by omega⟩
    have hKfin : K.Finite := Set.Finite.subset (hfin_le e)
      (fun x hx => by simp only [Set.mem_setOf_eq]; exact hlong2 x hx)
    set tidx : List α → ℕ := fun x => if h : ∃ i, t i = x then h.choose else 0 with htidx
    have htidx_spec : ∀ x ∈ K, t (tidx x) = x := by
      intro x hx
      have hex : ∃ i, t i = x := (ht x).mp hx
      simp only [htidx, dif_pos hex]
      exact hex.choose_spec
    obtain ⟨b, hb⟩ := hbd (tidx '' K) (hKfin.image tidx)
    refine ⟨b + 1, fun n hn => ?_⟩
    have hnone : (annotated_history (cf K) t n).find?
        (fun p => decide ((0 : palette α) ∈ p.2)) = none := by
      rw [List.find?_eq_none]
      intro p hpmem
      unfold annotated_history at hpmem
      rw [List.mem_map] at hpmem
      obtain ⟨j, _, rfl⟩ := hpmem
      simp only [decide_eq_true_eq]
      rw [Ftrace (t j), hzero_mem e ((t j).length + 1)]
      have := hlong2 (t j) (htmem j)
      omega
    rw [hAnone _ hnone]
    ext x
    simp only [Set.mem_setOf_eq, annotated_history, List.map_map, List.mem_map, List.mem_range,
      Function.comp_apply]
    constructor
    · rintro ⟨j, _, rfl⟩
      exact htmem j
    · intro hx
      exact ⟨tidx x, by have : tidx x ≤ b := hb (tidx x) (Set.mem_image_of_mem tidx hx); omega,
        htidx_spec x hx⟩

import Architect
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Order.Lattice.Nat

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:observed-set"
  (statement := /-- For an input stream $x\colon \mathbb N\to\Sigma^*$ and a time $t\in\mathbb N$, the observed set $S_t$ is the set of distinct strings $x_s$ with $s<t$. -/)
  (title := /-- Observed strings -/)
  (latexEnv := "definition")]
def observed_set {α : Type*} (input : ℕ → α) (t : ℕ) : Set α :=
  input '' Set.Iio t

@[blueprint "def:language-family-intersection"
  (statement := /-- Let $\mathcal C=(L_i)_{i\in\mathbb N}$ be an indexed family of languages. For $A\subseteq\mathbb N$, define $L_A=\bigcap_{i\in A}L_i$. The intersection over the empty index set is the universal language. -/)
  (title := /-- Intersection of a subcollection of languages -/)
  (latexEnv := "definition")]
def language_family_intersection {α : Type*} (C : ℕ → Set α) (A : Set ℕ) : Set α :=
  ⋂ i, ⋂ (_ : i ∈ A), C i

@[blueprint "def:nonuniform-complexity"
  (statement := /-- For a one-based index $i$, the non-uniform complexity $m_{\mathcal C}(L_i)$ is the supremum of the cardinalities of all finite intersections $L_A$ such that $A$ is a finite subset of $\{1,\ldots,i\}$ containing $i$. Thus the supremum is $0$ if there is no such finite intersection. -/)
  (title := /-- Non-uniform complexity -/)
  (latexEnv := "definition")]
noncomputable def nonuniform_complexity {α : Type*} (C : ℕ → Set α) (i : ℕ) : ℕ :=
  sSup {n : ℕ | ∃ A : Set ℕ,
    A.Finite ∧ A ⊆ Set.Icc 1 i ∧ i ∈ A ∧
      (language_family_intersection C A).Finite ∧
      n = (language_family_intersection C A).ncard}

@[blueprint "def:greedy-selected-indices"
  (statement := /-- Fix a set $S$ of observed strings. The greedy algorithm begins with no selected language. After processing index $n+1$, it adjoins $n+1$ precisely when $S\subseteq L_{n+1}$ and the intersection of the previously selected languages with $L_{n+1}$ is infinite. -/)
  (title := /-- Languages selected by the greedy algorithm -/)
  (latexEnv := "definition")]
noncomputable def greedy_selected_indices {α : Type*}
    (C : ℕ → Set α) (S : Set α) : ℕ → Set ℕ
  | 0 => ∅
  | n + 1 =>
      @ite (Set ℕ)
        (S ⊆ C (n + 1) ∧
          (language_family_intersection C (greedy_selected_indices C S n) ∩
            C (n + 1)).Infinite)
        (Classical.propDecidable _)
        (insert (n + 1) (greedy_selected_indices C S n))
        (greedy_selected_indices C S n)

@[blueprint "def:greedy-intersection"
  (statement := /-- After the first $t$ languages have been processed against an observed set $S$, the maintained set $I_t$ is the intersection of the languages whose indices the greedy rule selected. -/)
  (title := /-- Maintained greedy intersection -/)
  (latexEnv := "definition")]
def greedy_intersection {α : Type*}
    (C : ℕ → Set α) (S : Set α) (t : ℕ) : Set α :=
  language_family_intersection C (greedy_selected_indices C S t)

@[blueprint "def:greedy-output"
  (statement := /-- At time $t$, the greedy algorithm chooses an arbitrary element of $I_t\setminus S_t$ when this set is nonempty. The fallback value is immaterial and is used only to make the choice a total function. -/)
  (title := /-- Output of the greedy intersection algorithm -/)
  (latexEnv := "definition")]
noncomputable def greedy_output {α : Type*} [Nonempty α]
    (C : ℕ → Set α) (input : ℕ → α) (t : ℕ) : α :=
  @dite α
    (greedy_intersection C (observed_set input t) t \
      observed_set input t).Nonempty
    (Classical.propDecidable _)
    (fun h => h.choose)
    (fun _ => Classical.choice (inferInstance : Nonempty α))

@[blueprint "lem:observed-set-finite"
  (statement := /-- For every type $\alpha$, every input stream $x\colon\mathbb N\to\alpha$, and every time $t\in\mathbb N$, the observed set $S_t=\{x_s:s<t\}$ is finite. -/)
  (proof := /-- The initial interval $\{s\in\mathbb N:s<t\}$ is finite, and the image of a finite set under the input map is finite. By the definition of $S_t$ in \cref{def:observed-set}, this image is exactly the observed set. -/)
  (title := /-- Finiteness of the observed set -/)
  (latexEnv := "lemma")]
lemma observed_set_finite {α : Type*} (input : ℕ → α) (t : ℕ) :
    (observed_set input t).Finite := by
  simpa only [observed_set] using (Set.finite_Iio t).image input

@[blueprint "lem:observed-set-card-le-time"
  (statement := /-- For every type $\alpha$, every input stream $x\colon\mathbb N\to\alpha$, and every time $t\in\mathbb N$, the observed set $S_t=\{x_s:s<t\}$ satisfies $|S_t|\le t$. -/)
  (proof := /-- By \cref{def:observed-set}, $S_t$ is the image of the finite initial interval $\{s\in\mathbb N:s<t\}$ under $x$. The natural cardinality of an image is at most that of its domain, and this initial interval has natural cardinality $t$. Therefore $|S_t|\le t$. -/)
  (title := /-- The observation count is bounded by time -/)
  (latexEnv := "lemma")]
lemma observed_set_card_le_time {α : Type*} (input : ℕ → α) (t : ℕ) :
    (observed_set input t).ncard ≤ t := by
  simpa only [observed_set, Set.ncard_Iio_nat] using
    (Set.ncard_image_le (f := input) (s := Set.Iio t) (Set.finite_Iio t))

@[blueprint "lem:enumeration-contains-observed"
  (statement := /-- Let $\alpha$ be a type, let $L\subseteq\alpha$, and let $x\colon\mathbb N\to\alpha$ satisfy $\operatorname{range}(x)=L$. Then, for every $t\in\mathbb N$, the observed set $S_t=\{x_s:s<t\}$ satisfies $S_t\subseteq L$. -/)
  (proof := /-- Every member of $S_t$ is, by \cref{def:observed-set}, equal to $x_s$ for some $s<t$. It therefore belongs to the range of $x$, which is $L$ by hypothesis. -/)
  (title := /-- Observations belong to the enumerated language -/)
  (latexEnv := "lemma")]
lemma enumeration_contains_observed {α : Type*} (input : ℕ → α) (L : Set α)
    (hEnumeration : Set.range input = L) (t : ℕ) :
    observed_set input t ⊆ L := by
  rintro y ⟨s, hs, rfl⟩
  rw [← hEnumeration]
  exact Set.mem_range_self s

@[blueprint "lem:threshold-implies-target-considered"
  (statement := /-- Let $\alpha$ be a type, let $x\colon\mathbb N\to\alpha$ be an input stream, and let $i^*,t\in\mathbb N$. If $i^*$ does not exceed the cardinality of the observed set $S_t=\{x_s:s<t\}$, then $i^*\le t$. -/)
  (proof := /-- The hypothesis gives $i^*\le |S_t|$, while \cref{lem:observed-set-card-le-time} gives $|S_t|\le t$. Transitivity yields $i^*\le t$. -/)
  (title := /-- The threshold brings the target into consideration -/)
  (latexEnv := "lemma")]
lemma threshold_implies_target_considered {α : Type*} (input : ℕ → α)
    (iStar t : ℕ) (hThreshold : iStar ≤ (observed_set input t).ncard) :
    iStar ≤ t := by
  exact hThreshold.trans (observed_set_card_le_time input t)

@[blueprint "lem:greedy-selected-indices-finite-bounded"
  (statement := /-- Let $\alpha$ be a type. For every indexed family $C\colon \mathbb{N}\to\mathcal{P}(\alpha)$, every set $S\subseteq\alpha$, and every $t\in\mathbb{N}$, the set of indices selected by the greedy rule after $t$ steps is finite and is contained in $\{i\in\mathbb{N}:1\leq i\leq t\}$. -/)
  (proof := /-- Proceed by induction on $t$. For $t=0$, \cref{def:greedy-selected-indices} gives the empty set, which is finite and contained in the empty interval $\{i\in\mathbb{N}:1\leq i\leq 0\}$. Suppose the assertion holds after $n$ steps. By \cref{def:greedy-selected-indices}, after step $n+1$ the selected set is either unchanged or obtained by adjoining $n+1$. The induction hypothesis makes the old set finite, and each of its elements lies between $1$ and $n$, hence between $1$ and $n+1$. In the insertion branch, adjoining one element preserves finiteness, while the new element $n+1$ satisfies $1\leq n+1\leq n+1$. Thus both conclusions hold after $n+1$ steps. -/)
  (title := /-- Finiteness and range of the selected indices -/)
  (latexEnv := "lemma")]
lemma greedy_selected_indices_finite_bounded {α : Type*}
    (C : ℕ → Set α) (S : Set α) (t : ℕ) :
    (greedy_selected_indices C S t).Finite ∧
      greedy_selected_indices C S t ⊆ Set.Icc 1 t := by
  induction t with
  | zero =>
      simp [greedy_selected_indices]
  | succ n ih =>
      simp only [greedy_selected_indices]
      split_ifs <;> simp_all [Set.subset_def] <;>
        intro a ha <;>
        exact Nat.le_trans (ih.2 a ha).2 (Nat.le_succ n)

@[blueprint "lem:greedy-intersection-contains-observed"
  (statement := /-- For every type $\alpha$, every indexed family $\mathcal C=(L_i)_{i\in\mathbb N}$ of subsets of $\alpha$, every set $S\subseteq\alpha$, and every $t\in\mathbb N$, the maintained greedy intersection satisfies $S\subseteq I_t$. -/)
  (proof := /-- We argue by induction on $t$. By \cref{def:greedy-selected-indices}, no index is selected at $t=0$; hence \cref{def:language-family-intersection, def:greedy-intersection} give $I_0=\alpha$, so $S\subseteq I_0$. Suppose that $S\subseteq I_t$. At stage $t+1$, \cref{def:greedy-selected-indices} either leaves the selected index set unchanged or adjoins $t+1$. In the first case, \cref{def:greedy-intersection} gives $I_{t+1}=I_t$, and the induction hypothesis applies. In the second case, the selection condition gives $S\subseteq L_{t+1}$; combining this with $S\subseteq I_t$ and \cref{def:language-family-intersection, def:greedy-intersection} yields $S\subseteq I_t\cap L_{t+1}=I_{t+1}$. -/)
  (title := /-- The maintained intersection contains the observations -/)
  (latexEnv := "lemma")]
lemma greedy_intersection_contains_observed {α : Type*}
    (C : ℕ → Set α) (S : Set α) (t : ℕ) :
    S ⊆ greedy_intersection C S t := by
  induction t with
  | zero =>
      simp [greedy_intersection, greedy_selected_indices,
        language_family_intersection]
  | succ n ih =>
      rw [greedy_intersection, greedy_selected_indices]
      split <;> simp_all [greedy_intersection, language_family_intersection]

@[blueprint "lem:greedy-intersection-infinite"
  (statement := /-- Let $\alpha$ be a type and let $\mathcal C=(L_i)_{i\in\mathbb N}$ be an indexed family of subsets of $\alpha$. If $L_i$ is infinite for every $i\ge 1$, then, for every subset $S\subseteq\alpha$ and every $t\in\mathbb N$, the maintained greedy intersection $I_t$ is infinite. -/)
  (proof := /-- Since $L_1$ is infinite and is contained in $\alpha$, the universal subset of $\alpha$ is infinite. By \cref{def:greedy-selected-indices, def:greedy-intersection, def:language-family-intersection}, this universal set is $I_0$. We now induct on $t$. If the selection condition at stage $t+1$ is false, the selected index set, and hence the maintained intersection, is unchanged, so the induction hypothesis applies. If the condition is true, then the new maintained intersection is $I_t\cap L_{t+1}$, whose infinitude is the second conjunct of the selection condition. Thus $I_t$ is infinite for every $t\in\mathbb N$. -/)
  (title := /-- Infinitude of the maintained intersection -/)
  (latexEnv := "lemma")]
lemma greedy_intersection_infinite {α : Type*} (C : ℕ → Set α)
    (hLanguagesInfinite : ∀ i, 1 ≤ i → (C i).Infinite)
    (S : Set α) (t : ℕ) :
    (greedy_intersection C S t).Infinite := by
  induction t with
  | zero =>
      have h : (Set.univ : Set α).Infinite :=
        (hLanguagesInfinite 1 (by omega)).mono (Set.subset_univ _)
      simpa [greedy_intersection, greedy_selected_indices,
        language_family_intersection] using h
  | succ n ih =>
      rw [greedy_intersection, greedy_selected_indices]
      split_ifs with h
      · simpa [language_family_intersection, Set.inter_comm] using h.2
      · exact ih

@[blueprint "lem:greedy-intersection-decreases"
  (statement := /-- Let $\alpha$ be a type, let $C=(C_i)_{i\in\mathbb N}$ be an indexed family of subsets of $\alpha$, and let $S\subseteq\alpha$. For all $r,t\in\mathbb N$ with $r\le t$, the maintained intersections satisfy $I_t\subseteq I_r$. -/)
  (proof := /-- Induct on the relation $r\le t$. The reflexive case is immediate. At a successor stage, \cref{def:greedy-selected-indices} either leaves the selected index set unchanged or adjoins the new index. By \cref{def:language-family-intersection,def:greedy-intersection}, the maintained intersection is therefore unchanged or is contained in its predecessor. Composing this one-step inclusion with the induction hypothesis yields $I_{t+1}\subseteq I_r$. -/)
  (title := /-- Monotonic decrease of the maintained intersection -/)
  (latexEnv := "lemma")]
lemma greedy_intersection_decreases {α : Type*}
    (C : ℕ → Set α) (S : Set α) {r t : ℕ} (hrt : r ≤ t) :
    greedy_intersection C S t ⊆ greedy_intersection C S r := by
  induction hrt with
  | refl =>
      exact Set.Subset.rfl
  | @step t hrt ih =>
      apply Set.Subset.trans ?_ ih
      simp only [greedy_intersection, greedy_selected_indices]
      split_ifs <;>
        first
        | exact Set.Subset.rfl
        | (intro x hx
           simp only [language_family_intersection, Set.mem_iInter] at hx ⊢
           intro i hi
           exact hx i (Set.mem_insert_of_mem _ hi))

@[blueprint "lem:eligible-intersection-card-le-complexity"
  (statement := /-- Let $\alpha$ be a type, let $\mathcal C=(L_j)_{j\in\mathbb N}$ be an indexed family of subsets of $\alpha$, and let $i\in\mathbb N$. For every finite set $A\subseteq\mathbb N$ such that $A\subseteq\{1,\ldots,i\}$ and $i\in A$, if $L_A$ is finite, then $|L_A|\le m_{\mathcal C}(L_i)$. -/)
  (proof := /-- The interval $\{1,\ldots,i\}$ is finite, so its collection of subsets is finite. The image of this collection under $B\mapsto |L_B|$ is therefore finite and hence bounded above. Every cardinality in the set defining $m_{\mathcal C}(L_i)$ in \cref{def:nonuniform-complexity} belongs to this image, because its witnessing index set is contained in $\{1,\ldots,i\}$. Thus the defining set is bounded above. The hypotheses on $A$ also show that $|L_A|$ itself belongs to that defining set. The conditionally complete supremum property now gives $|L_A|\le m_{\mathcal C}(L_i)$. -/)
  (title := /-- Eligible finite intersections are bounded by complexity -/)
  (latexEnv := "lemma")]
lemma eligible_intersection_card_le_complexity {α : Type*}
    (C : ℕ → Set α) (i : ℕ) (A : Set ℕ)
    (hFiniteIndices : A.Finite) (hIndices : A ⊆ Set.Icc 1 i)
    (hi : i ∈ A) (hFiniteIntersection : (language_family_intersection C A).Finite) :
    (language_family_intersection C A).ncard ≤ nonuniform_complexity C i := by
  unfold nonuniform_complexity
  apply le_csSup
  · refine ((((Set.finite_Icc (1 : ℕ) i).finite_subsets.image
      (fun B : Set ℕ => (language_family_intersection C B).ncard)).subset ?_).bddAbove)
    rintro n ⟨B, _, hB, _, _, rfl⟩
    exact ⟨B, hB, rfl⟩
  · exact ⟨A, hFiniteIndices, hIndices, hi, hFiniteIntersection, rfl⟩

@[blueprint "lem:target-candidate-infinite"
  (statement := /-- Let $\alpha$ be a type, let $\mathcal C=(L_i)_{i\in\mathbb N}$ be an indexed family of subsets of $\alpha$, let $S\subseteq\alpha$, and let $i^*\in\mathbb N$ satisfy $1\le i^*$. If $S\subseteq L_{i^*}$ and $m_{\mathcal C}(L_{i^*})+1\le |S|$, then the candidate intersection $I_{i^*-1}\cap L_{i^*}$ is infinite. -/)
  (proof := /-- Assume instead that $I_{i^*-1}\cap L_{i^*}$ is finite. By \cref{lem:greedy-selected-indices-finite-bounded}, adjoining $i^*$ to the previously selected indices produces a finite subset of $\{1,\ldots,i^*\}$ containing $i^*$. By \cref{def:language-family-intersection, def:greedy-intersection}, its language intersection is precisely $I_{i^*-1}\cap L_{i^*}$. Moreover, \cref{lem:greedy-intersection-contains-observed} and the hypothesis $S\subseteq L_{i^*}$ show that $S$ is contained in this finite intersection. Hence its cardinality is at least $|S|$, and thus at least $m_{\mathcal C}(L_{i^*})+1$. On the other hand, \cref{lem:eligible-intersection-card-le-complexity} bounds the same cardinality by $m_{\mathcal C}(L_{i^*})$, a contradiction. -/)
  (title := /-- Infinitude of the target candidate intersection -/)
  (latexEnv := "lemma")]
lemma target_candidate_infinite {α : Type*}
    (C : ℕ → Set α) (S : Set α) (iStar : ℕ)
    (hPositive : 1 ≤ iStar) (hObservedTarget : S ⊆ C iStar)
    (hLarge : nonuniform_complexity C iStar + 1 ≤ S.ncard) :
    (greedy_intersection C S (iStar - 1) ∩ C iStar).Infinite := by
  classical
  by_contra hInfinite
  have hFinite : (greedy_intersection C S (iStar - 1) ∩ C iStar).Finite :=
    Set.not_infinite.mp hInfinite
  let A : Set ℕ := insert iStar (greedy_selected_indices C S (iStar - 1))
  have hSelected := greedy_selected_indices_finite_bounded C S (iStar - 1)
  have hAFinite : A.Finite := hSelected.1.insert iStar
  have hASubset : A ⊆ Set.Icc 1 iStar := by
    intro j hj
    rcases hj with (rfl | hj)
    · exact ⟨hPositive, le_rfl⟩
    · have hj' := hSelected.2 hj
      exact ⟨hj'.1, Nat.le_trans hj'.2 (Nat.sub_le iStar 1)⟩
  have hi : iStar ∈ A := Set.mem_insert iStar _
  have hEq : language_family_intersection C A =
      greedy_intersection C S (iStar - 1) ∩ C iStar := by
    ext x
    simp [A, language_family_intersection, greedy_intersection, and_comm]
  have hFamilyFinite : (language_family_intersection C A).Finite := hEq ▸ hFinite
  have hBound := eligible_intersection_card_le_complexity C iStar A hAFinite hASubset hi
    hFamilyFinite
  have hObs : S ⊆ greedy_intersection C S (iStar - 1) ∩ C iStar := by
    intro x hx
    exact ⟨greedy_intersection_contains_observed C S (iStar - 1) hx,
      hObservedTarget hx⟩
  have hCard := Set.ncard_le_ncard hObs hFinite
  rw [hEq] at hBound
  omega

@[blueprint "lem:greedy-intersection-subset-target"
  (statement := /-- Let $\alpha$ be a type, let $\mathcal C=(L_i)_{i\in\mathbb N}$ be an indexed family of subsets of $\alpha$, let $S\subseteq\alpha$, and let $i^*,t\in\mathbb N$ satisfy $1\le i^*\le t$. If $S\subseteq L_{i^*}$ and $m_{\mathcal C}(L_{i^*})+1\le |S|$, then the maintained greedy intersection after the first $t$ stages is a subset of $L_{i^*}$. -/)
  (proof := /-- By \cref{lem:target-candidate-infinite}, the candidate intersection $I_{i^*-1}\cap L_{i^*}$ is infinite. Together with $S\subseteq L_{i^*}$, \cref{def:greedy-selected-indices} therefore adjoins $i^*$ at stage $i^*$. The definitions in \cref{def:language-family-intersection,def:greedy-intersection} then give $I_{i^*}\subseteq L_{i^*}$. Since $i^*\le t$, \cref{lem:greedy-intersection-decreases} gives $I_t\subseteq I_{i^*}$, and transitivity yields $I_t\subseteq L_{i^*}$. -/)
  (title := /-- Persistence of the target-language containment -/)
  (latexEnv := "lemma")]
lemma greedy_intersection_subset_target {α : Type*}
    (C : ℕ → Set α) (S : Set α) (iStar t : ℕ)
    (hPositive : 1 ≤ iStar) (hTime : iStar ≤ t)
    (hObservedTarget : S ⊆ C iStar)
    (hLarge : nonuniform_complexity C iStar + 1 ≤ S.ncard) :
    greedy_intersection C S t ⊆ C iStar := by
  rcases iStar with _ | n
  · omega
  · apply Set.Subset.trans (greedy_intersection_decreases C S hTime)
    simp only [greedy_intersection, greedy_selected_indices]
    rw [if_pos]
    · exact Set.iInter₂_subset (n + 1) (Set.mem_insert (n + 1) _)
    · exact ⟨hObservedTarget, by
        simpa only [greedy_intersection, Nat.add_sub_cancel] using
          target_candidate_infinite C S (n + 1) hPositive hObservedTarget hLarge⟩

@[blueprint "lem:greedy-output-mem"
  (statement := /-- Let $\alpha$ be a nonempty type, let $C=(C_i)_{i\in\mathbb N}$ be a family of subsets of $\alpha$ such that $C_i$ is infinite for every $i\ge 1$, and let $x\colon\mathbb N\to\alpha$ be an input stream. For every $t\in\mathbb N$, the greedy output at time $t$ belongs to $I_t\setminus S_t$, where $S_t$ is the observed set determined by $x$ and $I_t$ is the maintained greedy intersection determined by $C$ and $S_t$. -/)
  (proof := /-- By \cref{lem:greedy-intersection-infinite}, $I_t$ is infinite, whereas \cref{lem:observed-set-finite} shows that $S_t$ is finite. Removing $S_t$ therefore leaves an infinite, and hence nonempty, set. The nonempty branch of the choice in \cref{def:greedy-output} is consequently taken, and its chosen element belongs to $I_t\setminus S_t$. -/)
  (title := /-- Validity of the greedy output choice -/)
  (latexEnv := "lemma")]
lemma greedy_output_mem {α : Type*} [Nonempty α]
    (C : ℕ → Set α) (hLanguagesInfinite : ∀ i, 1 ≤ i → (C i).Infinite)
    (input : ℕ → α) (t : ℕ) :
    greedy_output C input t ∈
      greedy_intersection C (observed_set input t) t \ observed_set input t := by
  have hNonempty :
      (greedy_intersection C (observed_set input t) t \
        observed_set input t).Nonempty :=
    ((greedy_intersection_infinite C hLanguagesInfinite
      (observed_set input t) t).sdiff
      (observed_set_finite input t)).nonempty
  simpa only [greedy_output, dif_pos hNonempty] using hNonempty.choose_spec

@[blueprint "thm:nonuniform-generation-upper-bound"
  (statement := /-- Let $\Sigma$ be a finite alphabet, and let $\mathcal C=(L_1,L_2,\ldots)$ be a countable indexed collection of infinite languages contained in $\Sigma^*$. Fix a positive index $i^*$ and let $x\colon\mathbb N\to\Sigma^*$ be any enumeration of $L_{i^*}$. For every time $t$ satisfying
  \[
    |S_t|\ge \max\{i^*,m_{\mathcal C}(L_{i^*})+1\},
  \]
  the greedy intersection algorithm outputs an element of $L_{i^*}\setminus S_t$. -/)
  (proof := /-- Since the range of the input is $L_{i^*}$, \cref{lem:enumeration-contains-observed} yields $S_t\subseteq L_{i^*}$. The threshold gives both $i^*\le |S_t|$ and $m_{\mathcal C}(L_{i^*})+1\le |S_t|$. The former inequality and \cref{lem:threshold-implies-target-considered} imply $i^*\le t$. Applying \cref{lem:greedy-intersection-subset-target} now gives $I_t\subseteq L_{i^*}$. Finally, \cref{lem:greedy-output-mem} places the generated string in $I_t\setminus S_t$, and hence in $L_{i^*}\setminus S_t$. -/)
  (title := /-- Non-uniform generation upper bound -/)
  (latexEnv := "theorem")]
theorem nonuniform_generation_upper_bound {σ : Type*} [Fintype σ]
    (C : ℕ → Set (List σ)) (hLanguagesInfinite : ∀ i, 1 ≤ i → (C i).Infinite)
    (iStar : ℕ) (hPositive : 1 ≤ iStar)
    (input : ℕ → List σ) (hEnumeration : Set.range input = C iStar)
    (t : ℕ)
    (hThreshold : max iStar (nonuniform_complexity C iStar + 1) ≤
      (observed_set input t).ncard) :
    greedy_output C input t ∈ C iStar \ observed_set input t := by
  have hObservedTarget : observed_set input t ⊆ C iStar :=
    enumeration_contains_observed input (C iStar) hEnumeration t
  have hIndexBound : iStar ≤ (observed_set input t).ncard :=
    (Nat.le_max_left iStar (nonuniform_complexity C iStar + 1)).trans hThreshold
  have hLarge : nonuniform_complexity C iStar + 1 ≤
      (observed_set input t).ncard :=
    (Nat.le_max_right iStar (nonuniform_complexity C iStar + 1)).trans hThreshold
  have hTime : iStar ≤ t :=
    threshold_implies_target_considered input iStar t hIndexBound
  have hTarget : greedy_intersection C (observed_set input t) t ⊆ C iStar :=
    greedy_intersection_subset_target C (observed_set input t) iStar t
      hPositive hTime hObservedTarget hLarge
  have hOutput : greedy_output C input t ∈
      greedy_intersection C (observed_set input t) t \ observed_set input t :=
    greedy_output_mem C hLanguagesInfinite input t
  exact Set.mem_sdiff_of_mem (hTarget hOutput.1) hOutput.2

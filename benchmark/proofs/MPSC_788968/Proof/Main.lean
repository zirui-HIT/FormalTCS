import Architect
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Order.Monotone.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:is-submodular"
  (statement := /-- Let $S$ be a finite ground set and let $\varphi \colon 2^{S} \to \mathbb{R}$
    be a real-valued set function. The function $\varphi$ is \emph{submodular} if for all
    subsets $X, Y \subseteq S$ one has
    $\varphi(X \cap Y) + \varphi(X \cup Y) \le \varphi(X) + \varphi(Y)$. -/)
  (title := /-- Submodular set function -/)
  (latexEnv := "definition")]
def is_submodular {S : Type*} [DecidableEq S] (φ : Finset S → ℝ) : Prop :=
  ∀ X Y : Finset S, φ (X ∩ Y) + φ (X ∪ Y) ≤ φ X + φ Y

@[blueprint "def:is-polymatroid"
  (statement := /-- Let $S$ be a finite ground set. A set function
    $\varphi \colon 2^{S} \to \mathbb{R}$ is a \emph{polymatroid function} if it is increasing
    (i.e. $X \subseteq Y$ implies $\varphi(X) \le \varphi(Y)$), submodular in the sense of
    \cref{def:is-submodular}, and satisfies $\varphi(\emptyset) = 0$. -/)
  (title := /-- Polymatroid function -/)
  (latexEnv := "definition")]
def is_polymatroid {S : Type*} [DecidableEq S] (φ : Finset S → ℝ) : Prop :=
  Monotone φ ∧ is_submodular φ ∧ φ ∅ = 0

@[blueprint "def:is-k-polymatroid"
  (statement := /-- Let $S$ be a finite ground set and let $k \in \mathbb{R}$. A set function
    $\varphi \colon 2^{S} \to \mathbb{R}$ is a \emph{$k$-polymatroid function} if it is a
    polymatroid function in the sense of \cref{def:is-polymatroid} and additionally satisfies
    $\varphi(X) \le k \cdot |X|$ for every $X \subseteq S$. -/)
  (title := /-- $k$-polymatroid function -/)
  (latexEnv := "definition")]
def is_k_polymatroid {S : Type*} [DecidableEq S] (k : ℝ) (φ : Finset S → ℝ) : Prop :=
  is_polymatroid φ ∧ ∀ X : Finset S, φ X ≤ k * (X.card : ℝ)

@[blueprint "def:is-integer-valued"
  (statement := /-- A set function $\varphi \colon 2^{S} \to \mathbb{R}$ is
    \emph{integer-valued} if for every subset $X \subseteq S$ the value $\varphi(X)$ is an
    integer, i.e. there exists $n \in \mathbb{Z}$ with $\varphi(X) = n$. -/)
  (title := /-- Integer-valued set function -/)
  (latexEnv := "definition")]
def is_integer_valued {S : Type*} (φ : Finset S → ℝ) : Prop :=
  ∀ X : Finset S, ∃ n : ℤ, φ X = (n : ℝ)

@[blueprint "def:is-coupling"
  (statement := /-- Let $S_1$ and $S_2$ be finite ground sets and let
    $\varphi_1 \colon 2^{S_1} \to \mathbb{R}$ and $\varphi_2 \colon 2^{S_2} \to \mathbb{R}$ be
    set functions. A set function $\varphi \colon 2^{S_1 \times S_2} \to \mathbb{R}$ is a
    \emph{coupling} of $\varphi_1$ and $\varphi_2$ if
    $\varphi(X_1 \times S_2) = \varphi_1(X_1) \cdot \varphi_2(S_2)$ for every $X_1 \subseteq S_1$
    and $\varphi(S_1 \times X_2) = \varphi_1(S_1) \cdot \varphi_2(X_2)$ for every
    $X_2 \subseteq S_2$. -/)
  (title := /-- Coupling of two set functions -/)
  (latexEnv := "definition")]
def is_coupling {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    (φ₁ : Finset S₁ → ℝ) (φ₂ : Finset S₂ → ℝ) (φ : Finset (S₁ × S₂) → ℝ) : Prop :=
  (∀ X₁ : Finset S₁,
      φ (X₁ ×ˢ (Finset.univ : Finset S₂)) = φ₁ X₁ * φ₂ (Finset.univ : Finset S₂)) ∧
  (∀ X₂ : Finset S₂,
      φ ((Finset.univ : Finset S₁) ×ˢ X₂) = φ₁ (Finset.univ : Finset S₁) * φ₂ X₂)

@[blueprint "def:in-base-polyhedron"
  (statement := /-- Let $S$ be a finite ground set and let $\varphi \colon 2^{S} \to \mathbb{R}$
    be a set function. A vector $\mu \colon S \to \mathbb{R}$, extended additively to subsets by
    $\mu(Z) = \sum_{i \in Z} \mu(i)$, lies in the \emph{base polyhedron} $B(\varphi)$ if it is
    nonnegative ($\mu(i) \ge 0$ for every $i \in S$), tight on the ground set
    ($\sum_{i \in S} \mu(i) = \varphi(S)$), and satisfies $\mu(Z) \le \varphi(Z)$ for every
    subset $Z \subseteq S$. -/)
  (title := /-- Base polyhedron of a set function -/)
  (latexEnv := "definition")]
def in_base_polyhedron {S : Type*} [Fintype S] (φ : Finset S → ℝ) (μ : S → ℝ) : Prop :=
  (∀ i : S, 0 ≤ μ i) ∧
  (∑ i : S, μ i = φ (Finset.univ : Finset S)) ∧
  (∀ Z : Finset S, ∑ i ∈ Z, μ i ≤ φ Z)

@[blueprint "lem:greedy-base"
  (statement := /-- Let $S$ be a finite ground set, let $\varphi \colon 2^{S} \to \mathbb{R}$ be a
    polymatroid function in the sense of \cref{def:is-polymatroid}, and let $T \subseteq S$. Then
    there exists a vector $\mu \colon S \to \mathbb{R}$ with the following properties: $\mu$ is
    nonnegative ($\mu(i) \ge 0$ for every $i \in S$); $\mu$ is supported on $T$ ($\mu(i) = 0$ for
    every $i \notin T$); $\mu$ is tight on $T$ ($\sum_{i \in T} \mu(i) = \varphi(T)$); $\mu$
    satisfies $\sum_{i \in Z} \mu(i) \le \varphi(Z)$ for every $Z \subseteq T$; and, whenever
    $\varphi$ is integer-valued in the sense of \cref{def:is-integer-valued}, every value
    $\mu(i)$ is an integer. -/)
  (proof := /-- We argue by strong induction on the finite set $T$. If $T = \emptyset$, take
    $\mu \equiv 0$; nonnegativity and support are immediate, and since $\varphi(\emptyset) = 0$ by
    \cref{def:is-polymatroid} both $\sum_{i \in \emptyset} \mu(i) = 0 = \varphi(\emptyset)$ and,
    for the only subset $Z = \emptyset$, $\sum_{i \in Z} \mu(i) = 0 \le \varphi(\emptyset)$ hold;
    integrality is clear as $0 \in \mathbb{Z}$.

    If $T \neq \emptyset$, choose $a \in T$ and set $T' = T \setminus \{a\}$, so
    $T' \subsetneq T$. By the induction hypothesis applied to $T'$ there is $\mu'$ that is
    nonnegative, supported on $T'$, tight on $T'$ with $\sum_{i \in T'} \mu'(i) = \varphi(T')$,
    satisfies $\sum_{i \in Z} \mu'(i) \le \varphi(Z)$ for every $Z \subseteq T'$, and is
    integer-valued when $\varphi$ is. Define $\mu(a) = \varphi(T) - \varphi(T')$ and
    $\mu(i) = \mu'(i)$ for $i \neq a$. Since $\varphi$ is increasing (\cref{def:is-polymatroid})
    and $T' \subseteq T$ we have $\varphi(T') \le \varphi(T)$, so $\mu(a) \ge 0$ and $\mu$ is
    nonnegative; $\mu$ is supported on $T$ because $i \notin T$ implies $i \neq a$ and
    $i \notin T'$. Tightness on $T$ follows from
    $\sum_{i \in T} \mu(i) = \mu(a) + \sum_{i \in T'} \mu'(i)
    = (\varphi(T) - \varphi(T')) + \varphi(T') = \varphi(T)$.

    For $Z \subseteq T$ we distinguish two cases. If $a \notin Z$, then $Z \subseteq T'$ and
    $\sum_{i \in Z} \mu(i) = \sum_{i \in Z} \mu'(i) \le \varphi(Z)$ by the induction hypothesis.
    If $a \in Z$, then $Z \cap T' = Z \setminus \{a\}$ and $Z \cup T' = T$, so submodularity of
    $\varphi$ (\cref{def:is-polymatroid}, via \cref{def:is-submodular}) applied to $Z$ and $T'$
    gives $\varphi(Z \setminus \{a\}) + \varphi(T) \le \varphi(Z) + \varphi(T')$. Combining this
    with the induction hypothesis $\sum_{i \in Z \setminus \{a\}} \mu'(i) \le
    \varphi(Z \setminus \{a\})$ yields
    $\sum_{i \in Z} \mu(i) = \mu(a) + \sum_{i \in Z \setminus \{a\}} \mu'(i)
    \le (\varphi(T) - \varphi(T')) + \varphi(Z \setminus \{a\}) \le \varphi(Z)$.

    Finally, if $\varphi$ is integer-valued (\cref{def:is-integer-valued}), then
    $\mu(a) = \varphi(T) - \varphi(T')$ is a difference of integers, hence an integer, and
    $\mu(i) = \mu'(i)$ is an integer for $i \neq a$ by the induction hypothesis. -/)
  (title := /-- Greedy vertex of the base polyhedron -/)
  (latexEnv := "lemma")]
lemma greedy_base {S : Type*} [Fintype S] [DecidableEq S]
    (φ : Finset S → ℝ) (hφ : is_polymatroid φ) (T : Finset S) :
    ∃ μ : S → ℝ,
      (∀ i, 0 ≤ μ i) ∧
      (∀ i, i ∉ T → μ i = 0) ∧
      (∑ i ∈ T, μ i = φ T) ∧
      (∀ Z, Z ⊆ T → ∑ i ∈ Z, μ i ≤ φ Z) ∧
      (is_integer_valued φ → ∀ i, ∃ n : ℤ, μ i = (n : ℝ)) := by
  induction T using Finset.strongInduction with
  | _ T ih =>
    rcases Finset.eq_empty_or_nonempty T with hT | hT
    · subst hT
      refine ⟨fun _ => 0, ?_, ?_, ?_, ?_, ?_⟩
      · intro i; exact le_refl 0
      · intro i _; rfl
      · simp [hφ.2.2]
      · intro Z hZ
        have hZe : Z = ∅ := Finset.subset_empty.mp hZ
        subst hZe
        simp [hφ.2.2]
      · intro _ i; exact ⟨0, by simp⟩
    · obtain ⟨a, haT⟩ := hT
      obtain ⟨μ', hpos', hsupp', htight', hsub', hint'⟩ :=
        ih (T.erase a) (Finset.erase_ssubset haT)
      set c := φ T - φ (T.erase a) with hc
      have ha_not : a ∉ T.erase a := by simp
      have hmono : φ (T.erase a) ≤ φ T := hφ.1 (Finset.erase_subset a T)
      have hc_nonneg : 0 ≤ c := by rw [hc]; exact sub_nonneg.mpr hmono
      have hsum_eq : ∀ (s : Finset S), a ∉ s →
          ∑ i ∈ s, Function.update μ' a c i = ∑ i ∈ s, μ' i := by
        intro s hs
        apply Finset.sum_congr rfl
        intro i hi
        exact Function.update_of_ne (ne_of_mem_of_not_mem hi hs) c μ'
      refine ⟨Function.update μ' a c, ?_, ?_, ?_, ?_, ?_⟩
      · intro i
        by_cases hi : i = a
        · rw [hi, Function.update_self a c μ']; exact hc_nonneg
        · rw [Function.update_of_ne hi c μ']; exact hpos' i
      · intro i hiT
        have hia : i ≠ a := (ne_of_mem_of_not_mem haT hiT).symm
        rw [Function.update_of_ne hia c μ']
        exact hsupp' i (fun h => hiT (Finset.mem_of_mem_erase h))
      · have e1 : ∑ i ∈ T, Function.update μ' a c i
            = Function.update μ' a c a + ∑ i ∈ T.erase a, Function.update μ' a c i :=
          (Finset.add_sum_erase T (Function.update μ' a c) haT).symm
        rw [e1, Function.update_self a c μ', hsum_eq (T.erase a) ha_not, htight', hc]
        exact sub_add_cancel (φ T) (φ (T.erase a))
      · intro Z hZT
        by_cases haZ : a ∈ Z
        · have eZ : ∑ i ∈ Z, Function.update μ' a c i
              = Function.update μ' a c a + ∑ i ∈ Z.erase a, Function.update μ' a c i :=
            (Finset.add_sum_erase Z (Function.update μ' a c) haZ).symm
          rw [eZ, Function.update_self a c μ', hsum_eq (Z.erase a) (by simp)]
          have hbound : ∑ i ∈ Z.erase a, μ' i ≤ φ (Z.erase a) :=
            hsub' (Z.erase a) (Finset.erase_subset_erase a hZT)
          have hZinter : Z ∩ (T.erase a) = Z.erase a := by
            ext x
            simp only [Finset.mem_inter, Finset.mem_erase]
            constructor
            · rintro ⟨hxZ, hxne, _⟩; exact ⟨hxne, hxZ⟩
            · rintro ⟨hxne, hxZ⟩; exact ⟨hxZ, hxne, hZT hxZ⟩
          have hZunion : Z ∪ (T.erase a) = T := by
            ext x
            simp only [Finset.mem_union, Finset.mem_erase]
            constructor
            · rintro (hxZ | ⟨_, hxT⟩)
              · exact hZT hxZ
              · exact hxT
            · intro hxT
              by_cases hxa : x = a
              · left; rw [hxa]; exact haZ
              · right; exact ⟨hxa, hxT⟩
          have hsubmod := hφ.2.1 Z (T.erase a)
          rw [hZinter, hZunion] at hsubmod
          rw [hc]
          have s1 : φ T - φ (T.erase a) + ∑ i ∈ Z.erase a, μ' i
              ≤ φ T - φ (T.erase a) + φ (Z.erase a) :=
            (add_le_add_iff_left (φ T - φ (T.erase a))).mpr hbound
          have s2 : φ T - φ (T.erase a) + φ (Z.erase a) ≤ φ Z := by
            rw [sub_add_eq_add_sub, sub_le_iff_le_add, add_comm (φ T) (φ (Z.erase a))]
            exact hsubmod
          exact le_trans s1 s2
        · rw [hsum_eq Z haZ]
          exact hsub' Z (Finset.subset_erase.mpr ⟨hZT, haZ⟩)
      · intro hiv i
        by_cases hi : i = a
        · rw [hi, Function.update_self a c μ', hc]
          obtain ⟨n₁, hn₁⟩ := hiv T
          obtain ⟨n₂, hn₂⟩ := hiv (T.erase a)
          exact ⟨n₁ - n₂, by rw [hn₁, hn₂, Int.cast_sub]⟩
        · rw [Function.update_of_ne hi c μ']
          exact hint' hiv i

@[blueprint "lem:base-polyhedron-integral"
  (statement := /-- Let $S$ be a finite ground set and let $\varphi \colon 2^{S} \to \mathbb{R}$
    be a polymatroid function in the sense of \cref{def:is-polymatroid}. Then the base polyhedron
    $B(\varphi)$ of \cref{def:in-base-polyhedron} is nonempty: there exists a vector
    $\mu \colon S \to \mathbb{R}$ with $\mu \in B(\varphi)$. Moreover, $\mu$ may be chosen to be
    integral whenever $\varphi$ is integer-valued in the sense of \cref{def:is-integer-valued},
    i.e. if $\varphi$ is integer-valued then $\mu(i) \in \mathbb{Z}$ for every $i \in S$. -/)
  (proof := /-- Apply \cref{lem:greedy-base} to the polymatroid function $\varphi$ with
    $T = S$ (the full ground set). This yields a vector $\mu \colon S \to \mathbb{R}$ that is
    nonnegative, tight on $S$ with $\sum_{i \in S} \mu(i) = \varphi(S)$, satisfies
    $\sum_{i \in Z} \mu(i) \le \varphi(Z)$ for every $Z \subseteq S$, and is integer-valued
    whenever $\varphi$ is integer-valued in the sense of \cref{def:is-integer-valued}. These are
    exactly the conditions defining $\mu \in B(\varphi)$ in \cref{def:in-base-polyhedron}, so
    $\mu$ witnesses the nonemptiness of $B(\varphi)$, and the same $\mu$ is integral when
    $\varphi$ is integer-valued. -/)
  (title := /-- Nonemptiness and integrality of the base polyhedron -/)
  (latexEnv := "lemma")]
lemma base_polyhedron_integral {S : Type*} [Fintype S] [DecidableEq S]
    (φ : Finset S → ℝ) (hφ : is_polymatroid φ) :
    ∃ μ : S → ℝ, in_base_polyhedron φ μ ∧
      (is_integer_valued φ → ∀ i : S, ∃ n : ℤ, μ i = (n : ℝ)) := by
  obtain ⟨μ, hpos, _, htight, hsub, hint⟩ := greedy_base φ hφ (Finset.univ : Finset S)
  refine ⟨μ, ⟨hpos, ?_, ?_⟩, hint⟩
  · simpa using htight
  · intro Z; exact hsub Z (Finset.subset_univ Z)

@[blueprint "lem:finset-sum-le-sum-real"
  (statement := /-- Let $I$ be a finite index set, let $s \subseteq I$ be a finite subset, and let
    $f, g \colon I \to \mathbb{R}$ be real-valued functions. If $f(i) \le g(i)$ for every
    $i \in s$, then $\sum_{i \in s} f(i) \le \sum_{i \in s} g(i)$. -/)
  (proof := /-- We argue by induction on the finite set $s$. If $s = \emptyset$ both sums are
    $0$, so the inequality is the equality $0 \le 0$. For the inductive step, write
    $s = \{a\} \cup t$ with $a \notin t$. By additivity of the sum over an inserted element,
    $\sum_{i \in s} f(i) = f(a) + \sum_{i \in t} f(i)$ and likewise for $g$. The hypothesis gives
    $f(a) \le g(a)$, and the induction hypothesis applied to the restriction of the pointwise
    bound to $t$ gives $\sum_{i \in t} f(i) \le \sum_{i \in t} g(i)$. Adding these two
    inequalities yields $\sum_{i \in s} f(i) \le \sum_{i \in s} g(i)$. -/)
  (title := /-- Monotonicity of real finite sums -/)
  (latexEnv := "lemma")]
lemma finset_sum_le_sum_real {I : Type*} (s : Finset I) (f g : I → ℝ)
    (h : ∀ i ∈ s, f i ≤ g i) : (∑ i ∈ s, f i) ≤ ∑ i ∈ s, g i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hle : f a ≤ g a := h a (Finset.mem_insert_self a t)
    have ih' : (∑ i ∈ t, f i) ≤ ∑ i ∈ t, g i :=
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact add_le_add hle ih'

@[blueprint "lem:finset-sum-mul-real"
  (statement := /-- Let $I$ be a finite index set, let $s \subseteq I$ be a finite subset, let
    $f \colon I \to \mathbb{R}$ be a real-valued function, and let $c \in \mathbb{R}$. Then
    $\left(\sum_{i \in s} f(i)\right) \cdot c = \sum_{i \in s} f(i) \cdot c$. -/)
  (proof := /-- We argue by induction on the finite set $s$. If $s = \emptyset$ both sides are
    $0$. For the inductive step, write $s = \{a\} \cup t$ with $a \notin t$. Additivity of the
    sum over an inserted element gives $\sum_{i \in s} f(i) = f(a) + \sum_{i \in t} f(i)$, and
    likewise $\sum_{i \in s} f(i) \cdot c = f(a) \cdot c + \sum_{i \in t} f(i) \cdot c$.
    Multiplying the first identity by $c$ and using right distributivity of multiplication over
    addition, $\left(f(a) + \sum_{i \in t} f(i)\right) \cdot c = f(a) \cdot c +
    \left(\sum_{i \in t} f(i)\right) \cdot c$, and the induction hypothesis rewrites
    $\left(\sum_{i \in t} f(i)\right) \cdot c$ as $\sum_{i \in t} f(i) \cdot c$, which yields the
    claim. -/)
  (title := /-- Right distributivity of multiplication over real finite sums -/)
  (latexEnv := "lemma")]
lemma finset_sum_mul_real {I : Type*} (s : Finset I) (f : I → ℝ) (c : ℝ) :
    (∑ i ∈ s, f i) * c = ∑ i ∈ s, f i * c := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_mul, ih]

@[blueprint "lem:finset-mul-sum-real"
  (statement := /-- Let $I$ be a finite index set, let $s \subseteq I$ be a finite subset, let
    $f \colon I \to \mathbb{R}$ be a real-valued function, and let $c \in \mathbb{R}$. Then
    $c \cdot \left(\sum_{i \in s} f(i)\right) = \sum_{i \in s} c \cdot f(i)$. -/)
  (proof := /-- Commuting the two factors, $c \cdot \left(\sum_{i \in s} f(i)\right) =
    \left(\sum_{i \in s} f(i)\right) \cdot c$, which by \cref{lem:finset-sum-mul-real} equals
    $\sum_{i \in s} f(i) \cdot c$; commuting each summand back gives $\sum_{i \in s} c \cdot f(i)$,
    as required. -/)
  (title := /-- Left distributivity of multiplication over real finite sums -/)
  (latexEnv := "lemma")]
lemma finset_mul_sum_real {I : Type*} (s : Finset I) (f : I → ℝ) (c : ℝ) :
    c * (∑ i ∈ s, f i) = ∑ i ∈ s, c * f i := by
  rw [mul_comm, finset_sum_mul_real]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

@[blueprint "lem:finset-sum-product-real"
  (statement := /-- Let $A$ and $B$ be types with decidable equality, let $s \subseteq A$ and
    $t \subseteq B$ be finite subsets, and let $f \colon A \times B \to \mathbb{R}$. Then the sum
    of $f$ over the Cartesian product $s \times t$ equals the iterated sum
    $\sum_{a \in s} \sum_{b \in t} f(a, b)$. -/)
  (proof := /-- Write the Cartesian product as the disjoint indexed union $s \times t =
    \bigcup_{a \in s} \{a\} \times t$, where for each $a \in s$ the fibre is the image of $t$
    under the injection $b \mapsto (a, b)$. These fibres are pairwise disjoint because their first
    coordinates differ. Summing over a disjoint union splits the sum over the product as
    $\sum_{a \in s} \sum_{p \in \{a\} \times t} f(p)$. For each fixed $a$, the map
    $b \mapsto (a, b)$ is injective, so summing over the image reduces to
    $\sum_{b \in t} f(a, b)$. Combining these gives $\sum_{p \in s \times t} f(p) =
    \sum_{a \in s} \sum_{b \in t} f(a, b)$. -/)
  (title := /-- Sum over a Cartesian product as an iterated sum -/)
  (latexEnv := "lemma")]
lemma finset_sum_product_real {A B : Type*} [DecidableEq A] [DecidableEq B]
    (s : Finset A) (t : Finset B) (f : A × B → ℝ) :
    (∑ p ∈ s ×ˢ t, f p) = ∑ a ∈ s, ∑ b ∈ t, f (a, b) := by
  classical
  rw [Finset.product_eq_biUnion]
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_image]
    intro b _ b' _ hbb'
    exact (Prod.mk.injEq a b a b' ▸ hbb').2
  · intro a _ a' _ haa'
    simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_coe]
    rintro p ⟨b, _, rfl⟩ ⟨b', _, hb'⟩
    exact haa' (congrArg Prod.fst hb').symm

@[blueprint "lem:exists-marginal-weights"
  (statement := /-- Let $S$ be a finite ground set and let $\varphi \colon 2^{S} \to \mathbb{R}$
    be a polymatroid function in the sense of \cref{def:is-polymatroid}. Then there exists a
    weight vector $w \colon S \to \mathbb{R}$ that is nonnegative ($w(i) \ge 0$ for every
    $i \in S$) and whose total mass equals the value of $\varphi$ on the full ground set,
    $\sum_{i \in S} w(i) = \varphi(S)$. -/)
  (proof := /-- Let $n = |S|$ be the cardinality of the ground set and set the uniform weight
    $w(i) = \varphi(S)/n$ for every $i \in S$. Since $\varphi$ is a polymatroid function it is
    increasing and satisfies $\varphi(\emptyset) = 0$; as $\emptyset \subseteq S$ this gives
    $\varphi(S) \ge \varphi(\emptyset) = 0$, and $n \ge 0$, so $w(i) = \varphi(S)/n \ge 0$ by
    nonnegativity of division. For the total mass, $\sum_{i \in S} w(i) = n \cdot
    (\varphi(S)/n)$. If $n \neq 0$ this equals $\varphi(S)$ by cancellation. If $n = 0$ then $S$
    is empty, so its universal finset equals $\emptyset$ and $\varphi(S) = \varphi(\emptyset) = 0$,
    while the empty sum is also $0$; hence the identity holds in both cases. -/)
  (title := /-- Existence of nonnegative marginal weights -/)
  (latexEnv := "lemma")]
lemma exists_marginal_weights {S : Type*} [Fintype S] [DecidableEq S]
    (φ : Finset S → ℝ) (hφ : is_polymatroid φ) :
    ∃ w : S → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = φ Finset.univ := by
  classical
  obtain ⟨mono, _, e⟩ := hφ
  have hnn : 0 ≤ φ (Finset.univ : Finset S) := by
    have := mono (Finset.empty_subset (Finset.univ : Finset S))
    rwa [e] at this
  refine ⟨fun _ => φ (Finset.univ : Finset S)
      / ((Finset.univ : Finset S).card : ℝ), ?_, ?_⟩
  · intro _
    exact div_nonneg hnn (Nat.cast_nonneg _)
  · rw [Finset.sum_const, nsmul_eq_mul]
    by_cases hc : ((Finset.univ : Finset S).card : ℝ) = 0
    · rw [hc, zero_mul]
      have hcard : (Finset.univ : Finset S).card = 0 := by exact_mod_cast hc
      have hempty : (Finset.univ : Finset S) = ∅ := by
        rw [← Finset.card_eq_zero, hcard]
      rw [hempty, e]
    · rw [mul_div_cancel₀ _ hc]

@[blueprint "lem:submodular-coupling-of-weights"
  (statement := /-- Let $S_1$ and $S_2$ be finite ground sets and let
    $\varphi_1 \colon 2^{S_1} \to \mathbb{R}$ and $\varphi_2 \colon 2^{S_2} \to \mathbb{R}$ be
    polymatroid functions in the sense of \cref{def:is-polymatroid}. Suppose $w_1 \colon S_1 \to
    \mathbb{R}$ and $w_2 \colon S_2 \to \mathbb{R}$ are nonnegative weights whose total masses
    equal the values of $\varphi_1$ and $\varphi_2$ on the full ground sets, i.e. $w_1(i) \ge 0$
    and $w_2(j) \ge 0$ for all $i \in S_1$, $j \in S_2$, and $\sum_{i \in S_1} w_1(i) =
    \varphi_1(S_1)$ and $\sum_{j \in S_2} w_2(j) = \varphi_2(S_2)$. Then the set function
    $\varphi \colon 2^{S_1 \times S_2} \to \mathbb{R}$ defined by
    $\varphi(Z) = \sum_{j \in S_2} w_2(j)\,\varphi_1(Z^j) + \sum_{i \in S_1} w_1(i)\,\varphi_2(Z_i)
    - \sum_{(i,j) \in Z} w_1(i)\,w_2(j)$, where $Z^j = \{\, i \in S_1 : (i,j) \in Z \,\}$ is the
    $j$-th column slice and $Z_i = \{\, j \in S_2 : (i,j) \in Z \,\}$ is the $i$-th row slice, is
    submodular in the sense of \cref{def:is-submodular} and is a coupling of $\varphi_1$ and
    $\varphi_2$ in the sense of \cref{def:is-coupling}. -/)
  (proof := /-- Define $\varphi(Z) = \sum_{j \in S_2} w_2(j)\,\varphi_1(Z^j)
    + \sum_{i \in S_1} w_1(i)\,\varphi_2(Z_i) - \sum_{(i,j) \in Z} w_1(i)\,w_2(j)$, where the
    column slice $Z^j$ and row slice $Z_i$ are the finite sets $\{i : (i,j) \in Z\}$ and
    $\{j : (i,j) \in Z\}$. We verify the two required properties for this $\varphi$.

    \emph{Submodularity.} Fix $X, Y \subseteq S_1 \times S_2$. Taking column slices commutes with
    union and intersection, $(X \cup Y)^j = X^j \cup Y^j$ and $(X \cap Y)^j = X^j \cap Y^j$, and
    likewise for row slices. Since $\varphi_1$ is submodular (\cref{def:is-submodular}) and each
    $w_2(j) \ge 0$, for every $j$ we have $w_2(j)\,(\varphi_1(X^j \cap Y^j) + \varphi_1(X^j \cup
    Y^j)) \le w_2(j)\,(\varphi_1(X^j) + \varphi_1(Y^j))$; summing these inequalities over $j$ with
    \cref{lem:finset-sum-le-sum-real} yields $\sum_j w_2(j)\,\varphi_1((X\cap Y)^j) + \sum_j
    w_2(j)\,\varphi_1((X\cup Y)^j) \le \sum_j w_2(j)\,\varphi_1(X^j) + \sum_j w_2(j)\,
    \varphi_1(Y^j)$. The analogous inequality for the row terms follows the same way from
    submodularity of $\varphi_2$ and $w_1(i) \ge 0$ via \cref{lem:finset-sum-le-sum-real}. For the
    product term, summing over the disjoint decomposition of a set into its intersection and union
    gives $\sum_{(i,j) \in X \cap Y} w_1(i)w_2(j) + \sum_{(i,j) \in X \cup Y} w_1(i)w_2(j) =
    \sum_{(i,j) \in X} w_1(i)w_2(j) + \sum_{(i,j) \in Y} w_1(i)w_2(j)$. Combining the two
    inequalities with this equality and regrouping yields $\varphi(X \cap Y) + \varphi(X \cup Y)
    \le \varphi(X) + \varphi(Y)$, which is submodularity in the sense of \cref{def:is-submodular}.

    \emph{Coupling.} Fix $X_1 \subseteq S_1$ and consider $Z = X_1 \times S_2$. For each column
    index $j$ the slice $Z^j = X_1$, so $\sum_j w_2(j)\,\varphi_1(Z^j) = \varphi_1(X_1) \sum_j
    w_2(j) = \varphi_1(X_1)\,\varphi_2(S_2)$ using $\sum_j w_2(j) = \varphi_2(S_2)$ and
    \cref{lem:finset-sum-mul-real}. The row slice $Z_i$ equals $S_2$ when $i \in X_1$ and
    $\emptyset$ otherwise, so the row term collapses to $\sum_{i \in X_1} w_1(i)\,\varphi_2(S_2)$
    (using $\varphi_2(\emptyset) = 0$). Splitting the product term over the Cartesian product with
    \cref{lem:finset-sum-product-real} gives $\sum_{(i,j) \in X_1 \times S_2} w_1(i)w_2(j) =
    \sum_{i \in X_1} w_1(i)\,\varphi_2(S_2)$, which cancels the row term exactly, leaving
    $\varphi(X_1 \times S_2) = \varphi_1(X_1)\,\varphi_2(S_2)$. Symmetrically, for $Z = S_1 \times
    X_2$ the row slices are all $X_2$, so the row term equals $\varphi_1(S_1)\,\varphi_2(X_2)$ via
    $\sum_i w_1(i) = \varphi_1(S_1)$ and \cref{lem:finset-sum-mul-real}, while the column term
    reduces to $\sum_{j \in X_2} w_2(j)\,\varphi_1(S_1)$; expanding the product term with
    \cref{lem:finset-sum-product-real}, factoring each inner sum by \cref{lem:finset-mul-sum-real},
    and using $\sum_i w_1(i) = \varphi_1(S_1)$ shows the column and product terms are equal and
    cancel, giving $\varphi(S_1 \times X_2) = \varphi_1(S_1)\,\varphi_2(X_2)$. These are exactly
    the two marginal identities of \cref{def:is-coupling}. -/)
  (title := /-- Submodular coupling from marginal weights -/)
  (latexEnv := "lemma")]
lemma submodular_coupling_of_weights {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    [DecidableEq S₁] [DecidableEq S₂]
    (φ₁ : Finset S₁ → ℝ) (φ₂ : Finset S₂ → ℝ)
    (h₁ : is_polymatroid φ₁) (h₂ : is_polymatroid φ₂)
    (w₁ : S₁ → ℝ) (w₂ : S₂ → ℝ)
    (hw₁ : ∀ i, 0 ≤ w₁ i) (hw₂ : ∀ j, 0 ≤ w₂ j)
    (hsw₁ : ∑ i, w₁ i = φ₁ Finset.univ) (hsw₂ : ∑ j, w₂ j = φ₂ Finset.univ) :
    ∃ φ : Finset (S₁ × S₂) → ℝ, is_submodular φ ∧ is_coupling φ₁ φ₂ φ := by
  classical
  obtain ⟨_, sub₁, e₁⟩ := h₁
  obtain ⟨_, sub₂, e₂⟩ := h₂
  refine ⟨fun Z => (∑ j, w₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ Z)))
      + (∑ i, w₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ Z)))
      - ∑ p ∈ Z, w₁ p.1 * w₂ p.2, ?_, ?_, ?_⟩
  · intro X Y
    have hcolU : ∀ j : S₂, Finset.univ.filter (fun i => (i, j) ∈ X ∪ Y)
        = Finset.univ.filter (fun i => (i, j) ∈ X) ∪ Finset.univ.filter (fun i => (i, j) ∈ Y) := by
      intro j; ext i; simp [Finset.mem_filter, Finset.mem_union]
    have hcolI : ∀ j : S₂, Finset.univ.filter (fun i => (i, j) ∈ X ∩ Y)
        = Finset.univ.filter (fun i => (i, j) ∈ X) ∩ Finset.univ.filter (fun i => (i, j) ∈ Y) := by
      intro j; ext i; simp [Finset.mem_filter, Finset.mem_inter]
    have hrowU : ∀ i : S₁, Finset.univ.filter (fun j => (i, j) ∈ X ∪ Y)
        = Finset.univ.filter (fun j => (i, j) ∈ X) ∪ Finset.univ.filter (fun j => (i, j) ∈ Y) := by
      intro i; ext j; simp [Finset.mem_filter, Finset.mem_union]
    have hrowI : ∀ i : S₁, Finset.univ.filter (fun j => (i, j) ∈ X ∩ Y)
        = Finset.univ.filter (fun j => (i, j) ∈ X) ∩ Finset.univ.filter (fun j => (i, j) ∈ Y) := by
      intro i; ext j; simp [Finset.mem_filter, Finset.mem_inter]
    have hA : (∑ j, w₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ X ∩ Y)))
          + (∑ j, w₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ X ∪ Y)))
        ≤ (∑ j, w₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ X)))
          + (∑ j, w₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ Y))) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply finset_sum_le_sum_real
      intro j _
      rw [hcolI j, hcolU j, ← mul_add, ← mul_add]
      exact mul_le_mul_of_nonneg_left (sub₁ _ _) (hw₂ j)
    have hB : (∑ i, w₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ X ∩ Y)))
          + (∑ i, w₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ X ∪ Y)))
        ≤ (∑ i, w₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ X)))
          + (∑ i, w₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ Y))) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply finset_sum_le_sum_real
      intro i _
      rw [hrowI i, hrowU i, ← mul_add, ← mul_add]
      exact mul_le_mul_of_nonneg_left (sub₂ _ _) (hw₁ i)
    have hC : (∑ p ∈ X ∩ Y, w₁ p.1 * w₂ p.2) + (∑ p ∈ X ∪ Y, w₁ p.1 * w₂ p.2)
        = (∑ p ∈ X, w₁ p.1 * w₂ p.2) + (∑ p ∈ Y, w₁ p.1 * w₂ p.2) := by
      rw [add_comm]
      exact Finset.sum_union_inter
    rw [sub_add_sub_comm, sub_add_sub_comm, hC]
    apply sub_le_sub_right
    exact (add_add_add_comm _ _ _ _).trans_le
      ((add_le_add hA hB).trans_eq (add_add_add_comm _ _ _ _))
  · intro X₁
    have hcol : ∀ j : S₂,
        Finset.univ.filter (fun i => (i, j) ∈ X₁ ×ˢ (Finset.univ : Finset S₂)) = X₁ := by
      intro j; ext i; simp [Finset.mem_filter, Finset.mem_product]
    have hrowmem : ∀ i : S₁,
        Finset.univ.filter (fun j => (i, j) ∈ X₁ ×ˢ (Finset.univ : Finset S₂))
          = if i ∈ X₁ then (Finset.univ : Finset S₂) else ∅ := by
      intro i
      by_cases hi : i ∈ X₁
      · rw [if_pos hi]; ext j; simp [Finset.mem_filter, Finset.mem_product, hi]
      · rw [if_neg hi]; ext j; simp [Finset.mem_filter, Finset.mem_product, hi]
    have hA : (∑ j, w₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ X₁ ×ˢ (Finset.univ : Finset S₂))))
        = φ₁ X₁ * φ₂ Finset.univ := by
      have : (∑ j, w₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ X₁ ×ˢ (Finset.univ : Finset S₂))))
          = ∑ j, w₂ j * φ₁ X₁ := by
        apply Finset.sum_congr rfl
        intro j _; rw [hcol j]
      rw [this, ← finset_sum_mul_real, hsw₂, mul_comm]
    have hB : (∑ i, w₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ X₁ ×ˢ (Finset.univ : Finset S₂))))
        = ∑ i ∈ X₁, w₁ i * φ₂ Finset.univ := by
      have hpt : ∀ i : S₁,
          w₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ X₁ ×ˢ (Finset.univ : Finset S₂)))
            = if i ∈ X₁ then w₁ i * φ₂ Finset.univ else 0 := by
        intro i
        by_cases hi : i ∈ X₁
        · rw [hrowmem i, if_pos hi, if_pos hi]
        · rw [hrowmem i, if_neg hi, if_neg hi, e₂, mul_zero]
      rw [Finset.sum_congr rfl (fun i _ => hpt i)]
      rw [← Finset.sum_filter, Finset.filter_univ_mem]
    have hC : (∑ p ∈ X₁ ×ˢ (Finset.univ : Finset S₂), w₁ p.1 * w₂ p.2)
        = ∑ i ∈ X₁, w₁ i * φ₂ Finset.univ := by
      rw [finset_sum_product_real]
      apply Finset.sum_congr rfl
      intro i _
      rw [← hsw₂, mul_comm, finset_sum_mul_real]
      apply Finset.sum_congr rfl
      intro b _
      rw [mul_comm]
    show (∑ j, w₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ X₁ ×ˢ (Finset.univ : Finset S₂))))
        + (∑ i, w₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ X₁ ×ˢ (Finset.univ : Finset S₂))))
        - (∑ p ∈ X₁ ×ˢ (Finset.univ : Finset S₂), w₁ p.1 * w₂ p.2) = φ₁ X₁ * φ₂ Finset.univ
    rw [hA, hB, hC, add_sub_cancel_right]
  · intro X₂
    have hrow : ∀ i : S₁,
        Finset.univ.filter (fun j => (i, j) ∈ (Finset.univ : Finset S₁) ×ˢ X₂) = X₂ := by
      intro i; ext j; simp [Finset.mem_filter, Finset.mem_product]
    have hcolmem : ∀ j : S₂,
        Finset.univ.filter (fun i => (i, j) ∈ (Finset.univ : Finset S₁) ×ˢ X₂)
          = if j ∈ X₂ then (Finset.univ : Finset S₁) else ∅ := by
      intro j
      by_cases hj : j ∈ X₂
      · rw [if_pos hj]; ext i; simp [Finset.mem_filter, Finset.mem_product, hj]
      · rw [if_neg hj]; ext i; simp [Finset.mem_filter, Finset.mem_product, hj]
    have hB : (∑ i, w₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ (Finset.univ : Finset S₁) ×ˢ X₂)))
        = φ₁ Finset.univ * φ₂ X₂ := by
      have : (∑ i, w₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ (Finset.univ : Finset S₁) ×ˢ X₂)))
          = ∑ i, w₁ i * φ₂ X₂ := by
        apply Finset.sum_congr rfl
        intro i _; rw [hrow i]
      rw [this, ← finset_sum_mul_real, hsw₁]
    have hA : (∑ j, w₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ (Finset.univ : Finset S₁) ×ˢ X₂)))
        = ∑ j ∈ X₂, w₂ j * φ₁ Finset.univ := by
      have hpt : ∀ j : S₂,
          w₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ (Finset.univ : Finset S₁) ×ˢ X₂))
            = if j ∈ X₂ then w₂ j * φ₁ Finset.univ else 0 := by
        intro j
        by_cases hj : j ∈ X₂
        · rw [hcolmem j, if_pos hj, if_pos hj]
        · rw [hcolmem j, if_neg hj, if_neg hj, e₁, mul_zero]
      rw [Finset.sum_congr rfl (fun j _ => hpt j)]
      rw [← Finset.sum_filter, Finset.filter_univ_mem]
    have hC : (∑ p ∈ (Finset.univ : Finset S₁) ×ˢ X₂, w₁ p.1 * w₂ p.2)
        = ∑ j ∈ X₂, w₂ j * φ₁ Finset.univ := by
      rw [finset_sum_product_real]
      have hstep : (∑ i, ∑ j ∈ X₂, w₁ i * w₂ j)
          = ∑ i, w₁ i * (∑ j ∈ X₂, w₂ j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← finset_mul_sum_real]
      rw [hstep, ← finset_sum_mul_real, hsw₁, ← finset_sum_mul_real]
      rw [mul_comm]
    show (∑ j, w₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ (Finset.univ : Finset S₁) ×ˢ X₂)))
        + (∑ i, w₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ (Finset.univ : Finset S₁) ×ˢ X₂)))
        - (∑ p ∈ (Finset.univ : Finset S₁) ×ˢ X₂, w₁ p.1 * w₂ p.2) = φ₁ Finset.univ * φ₂ X₂
    rw [hA, hB, hC, add_sub_cancel_left]

@[blueprint "lem:submodular-coupling"
  (statement := /-- Let $S_1$ and $S_2$ be finite ground sets and let
    $\varphi_1 \colon 2^{S_1} \to \mathbb{R}$ and $\varphi_2 \colon 2^{S_2} \to \mathbb{R}$ be
    polymatroid functions in the sense of \cref{def:is-polymatroid}. Then there exists a set
    function $\varphi \colon 2^{S_1 \times S_2} \to \mathbb{R}$ that is submodular in the sense of
    \cref{def:is-submodular} and is a coupling of $\varphi_1$ and $\varphi_2$ in the sense of
    \cref{def:is-coupling}. -/)
  (proof := /-- This is the existence of a submodular coupling given by the explicit coupling
    formula built from marginal weights. Since $\varphi_1$ and $\varphi_2$ are polymatroid
    functions, \cref{lem:exists-marginal-weights} applied to each yields nonnegative weight
    vectors $w_1 \colon S_1 \to \mathbb{R}$ and $w_2 \colon S_2 \to \mathbb{R}$ with $\sum_{i \in
    S_1} w_1(i) = \varphi_1(S_1)$ and $\sum_{j \in S_2} w_2(j) = \varphi_2(S_2)$. Feeding these
    weights into \cref{lem:submodular-coupling-of-weights} produces a set function $\varphi \colon
    2^{S_1 \times S_2} \to \mathbb{R}$ that is submodular in the sense of \cref{def:is-submodular}
    and satisfies the two marginal coupling identities of \cref{def:is-coupling}, which is the
    required coupling. -/)
  (title := /-- Existence of a submodular coupling -/)
  (latexEnv := "lemma")]
lemma submodular_coupling {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    [DecidableEq S₁] [DecidableEq S₂]
    (φ₁ : Finset S₁ → ℝ) (φ₂ : Finset S₂ → ℝ)
    (h₁ : is_polymatroid φ₁) (h₂ : is_polymatroid φ₂) :
    ∃ φ : Finset (S₁ × S₂) → ℝ, is_submodular φ ∧ is_coupling φ₁ φ₂ φ := by
  obtain ⟨w₁, hw₁, hsw₁⟩ := exists_marginal_weights φ₁ h₁
  obtain ⟨w₂, hw₂, hsw₂⟩ := exists_marginal_weights φ₂ h₂
  exact submodular_coupling_of_weights φ₁ φ₂ h₁ h₂ w₁ w₂ hw₁ hw₂ hsw₁ hsw₂

@[blueprint "lem:exists-finset-argmin"
  (statement := /-- Let $\alpha$ be a type, let $s$ be a finite subset of $\alpha$, and let
    $g \colon \alpha \to \mathbb{R}$. If $s$ is nonempty, then there exists $a \in s$ such that
    $g(a) \le g(b)$ for every $b \in s$. -/)
  (proof := /-- We argue by induction on the finite set $s$. If $s$ is empty the nonemptiness
    hypothesis is contradictory. Otherwise write $s$ as the insertion of an element $x$ into a
    finite set $t$ with $x \notin t$. If $t$ is empty, then $s$ has the single element $x$, and
    $a = x$ satisfies $g(a) \le g(b)$ for the only member $b = x$. If $t$ is nonempty, the
    induction hypothesis yields $a \in t$ with $g(a) \le g(b)$ for all $b \in t$. By totality of
    the order on $\mathbb{R}$ either $g(x) \le g(a)$ or $g(a) \le g(x)$. In the first case $x$ is a
    minimizer over $s$, since $g(x) \le g(a) \le g(b)$ for $b \in t$ and $g(x) \le g(x)$. In the
    second case $a$ is a minimizer over $s$, since $g(a) \le g(x)$ and $g(a) \le g(b)$ for
    $b \in t$. -/)
  (title := /-- Existence of an argmin over a nonempty finite set -/)
  (latexEnv := "lemma")]
lemma exists_finset_argmin {α : Type*} (s : Finset α) (g : α → ℝ) :
    s.Nonempty → ∃ a ∈ s, ∀ b ∈ s, g a ≤ g b := by
  classical
  induction s using Finset.induction with
  | empty => intro hs; exact (Finset.not_nonempty_empty hs).elim
  | @insert x t hx ih =>
    intro _
    rcases t.eq_empty_or_nonempty with ht | ht
    · subst ht
      refine ⟨x, by simp, ?_⟩
      intro b hb
      rw [Finset.mem_insert] at hb
      rcases hb with rfl | hb
      · exact le_refl _
      · exact absurd hb (by simp)
    · obtain ⟨a, ha, hamin⟩ := ih ht
      rcases le_total (g x) (g a) with h | h
      · refine ⟨x, Finset.mem_insert_self x t, ?_⟩
        intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact le_refl _
        · exact h.trans (hamin b hb)
      · refine ⟨a, Finset.mem_insert_of_mem ha, ?_⟩
        intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact h
        · exact hamin b hb

@[blueprint "lem:exists-superset-min"
  (statement := /-- Let $S$ be a finite ground set that is a fintype, and let
    $f \colon 2^{S} \to \mathbb{R}$. For every subset $Z \subseteq S$ there exists a superset
    $Y \supseteq Z$ with $f(Y) \le f(W)$ for every $W \supseteq Z$; that is, $f$ attains its
    minimum over the supersets of $Z$. -/)
  (proof := /-- We prove, by strong induction on the cardinality $n$ of the complement
    $S \setminus Z$, that for every $Z$ with $|S \setminus Z| = n$ such a minimizing superset
    exists. If $n = 0$ then $S \setminus Z = \emptyset$, so $Z = S$; the only superset of $Z$
    inside $S$ is $Z$ itself, and $Y = Z$ works. If $n > 0$, then for each element
    $e \in S \setminus Z$ the set $Z \cup \{e\}$ has strictly smaller complement, so the induction
    hypothesis provides a superset $Y_e \supseteq Z \cup \{e\}$ minimizing $f$ over supersets of
    $Z \cup \{e\}$. Applying \cref{lem:exists-finset-argmin} to the finite index set
    $S \setminus Z$ and the map $e \mapsto f(Y_e)$ yields an index $e_1$ with
    $f(Y_{e_1}) \le f(Y_e)$ for all $e$. If $f(Z) \le f(Y_{e_1})$ we take $Y = Z$; otherwise we
    take $Y = Y_{e_1}$. In either case, given any $W \supseteq Z$, either $W = Z$, handled
    directly, or $W$ strictly contains $Z$, so it contains some $e \in S \setminus Z$; then
    $Z \cup \{e\} \subseteq W$ gives $f(Y_e) \le f(W)$, and combining with the choice of $e_1$ and
    the case split shows $f(Y) \le f(W)$. -/)
  (title := /-- Minimizer over the supersets of a set -/)
  (latexEnv := "lemma")]
lemma exists_superset_min {T : Type*} [Fintype T] [DecidableEq T]
    (f : Finset T → ℝ) (Z : Finset T) :
    ∃ Y, Z ⊆ Y ∧ ∀ W, Z ⊆ W → f Y ≤ f W := by
  classical
  suffices H : ∀ n : ℕ, ∀ Z : Finset T, (Finset.univ \ Z).card = n →
      ∃ Y, Z ⊆ Y ∧ ∀ W, Z ⊆ W → f Y ≤ f W by
    exact H _ Z rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Z hn
    rcases (Finset.univ \ Z).eq_empty_or_nonempty with hE | hE
    · have huniv : Finset.univ ⊆ Z := Finset.sdiff_eq_empty_iff_subset.mp hE
      have hZ : Z = Finset.univ := Finset.Subset.antisymm (Finset.subset_univ Z) huniv
      refine ⟨Z, Finset.Subset.refl _, ?_⟩
      intro W hW
      have hWZ : W = Z :=
        Finset.Subset.antisymm (by rw [hZ]; exact Finset.subset_univ W) hW
      exact le_of_eq (congrArg f hWZ.symm)
    · obtain ⟨e0, he0⟩ := hE
      have hkey : ∀ e : ↥(Finset.univ \ Z),
          ∃ Y, insert e.1 Z ⊆ Y ∧ ∀ W, insert e.1 Z ⊆ W → f Y ≤ f W := by
        intro e
        have hss : Finset.univ \ insert e.1 Z ⊂ Finset.univ \ Z := by
          refine (Finset.ssubset_iff_of_subset
            (Finset.sdiff_subset_sdiff (Finset.Subset.refl _)
              (Finset.subset_insert e.1 Z))).mpr ?_
          exact ⟨e.1, e.2, by simp⟩
        have hlt : (Finset.univ \ insert e.1 Z).card < n := by
          rw [← hn]; exact Finset.card_lt_card hss
        exact ih _ hlt (insert e.1 Z) rfl
      choose Ymin hsub hmin using hkey
      obtain ⟨e1, -, he1min⟩ :=
        exists_finset_argmin (Finset.univ : Finset ↥(Finset.univ \ Z))
          (fun e => f (Ymin e)) ⟨⟨e0, he0⟩, Finset.mem_univ _⟩
      rcases le_total (f Z) (f (Ymin e1)) with hle | hle
      · refine ⟨Z, Finset.Subset.refl _, ?_⟩
        intro W hW
        rcases eq_or_ne W Z with rfl | hWne
        · exact le_refl _
        · obtain ⟨e, heW, heZ⟩ :=
            Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hW, hWne.symm⟩)
          have heE : e ∈ Finset.univ \ Z := Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, heZ⟩
          have hiW : insert e Z ⊆ W := Finset.insert_subset_iff.mpr ⟨heW, hW⟩
          calc f Z ≤ f (Ymin e1) := hle
            _ ≤ f (Ymin ⟨e, heE⟩) := he1min ⟨e, heE⟩ (Finset.mem_univ _)
            _ ≤ f W := hmin ⟨e, heE⟩ W hiW
      · refine ⟨Ymin e1, (Finset.subset_insert _ _).trans (hsub e1), ?_⟩
        intro W hW
        rcases eq_or_ne W Z with rfl | hWne
        · exact hle
        · obtain ⟨e, heW, heZ⟩ :=
            Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hW, hWne.symm⟩)
          have heE : e ∈ Finset.univ \ Z := Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, heZ⟩
          have hiW : insert e Z ⊆ W := Finset.insert_subset_iff.mpr ⟨heW, hW⟩
          calc f (Ymin e1) ≤ f (Ymin ⟨e, heE⟩) := he1min ⟨e, heE⟩ (Finset.mem_univ _)
            _ ≤ f W := hmin ⟨e, heE⟩ W hiW

@[blueprint "lem:monotone-hull"
  (statement := /-- Let $S$ be a finite ground set that is a fintype, and let
    $f \colon 2^{S} \to \mathbb{R}$ be submodular in the sense of \cref{def:is-submodular}. Then
    there exists a set function $g \colon 2^{S} \to \mathbb{R}$ that is submodular
    (\cref{def:is-submodular}) and increasing, satisfies $g(Z) \le f(W)$ whenever $Z \subseteq W$,
    and for every $Z$ there is a superset $Y \supseteq Z$ with $g(Z) = f(Y)$. Equivalently $g$ is
    the monotone lower envelope $g(Z) = \min_{W \supseteq Z} f(W)$. -/)
  (proof := /-- For each $Z$, \cref{lem:exists-superset-min} provides a superset $Y_Z \supseteq Z$
    minimizing $f$ over the supersets of $Z$; set $g(Z) = f(Y_Z)$, so that $g(Z) \le f(W)$ for
    every $W \supseteq Z$ and $g(Z) = f(Y_Z)$ with $Z \subseteq Y_Z$. Monotonicity: if
    $Z \subseteq Z'$, then $Y_{Z'} \supseteq Z' \supseteq Z$, so $g(Z) \le f(Y_{Z'}) = g(Z')$.
    Submodularity: for subsets $A, B$, from $A \cup B \subseteq Y_A \cup Y_B$ and
    $A \cap B \subseteq Y_A \cap Y_B$ we get $g(A \cup B) \le f(Y_A \cup Y_B)$ and
    $g(A \cap B) \le f(Y_A \cap Y_B)$; adding these and applying submodularity of $f$
    (\cref{def:is-submodular}) to $Y_A$ and $Y_B$ gives
    $g(A \cap B) + g(A \cup B) \le f(Y_A \cap Y_B) + f(Y_A \cup Y_B) \le f(Y_A) + f(Y_B)
    = g(A) + g(B)$. -/)
  (title := /-- Monotone lower envelope of a submodular function -/)
  (latexEnv := "lemma")]
lemma monotone_hull {T : Type*} [Fintype T] [DecidableEq T]
    (f : Finset T → ℝ) (hf : is_submodular f) :
    ∃ g : Finset T → ℝ, is_submodular g ∧ Monotone g ∧
      (∀ Z W, Z ⊆ W → g Z ≤ f W) ∧ (∀ Z, ∃ Y, Z ⊆ Y ∧ g Z = f Y) := by
  classical
  choose Y hYsub hYmin using (fun Z => exists_superset_min f Z)
  refine ⟨fun Z => f (Y Z), ?_, ?_, ?_, ?_⟩
  · intro A B
    have h1 : f (Y (A ∪ B)) ≤ f (Y A ∪ Y B) :=
      hYmin (A ∪ B) (Y A ∪ Y B) (Finset.union_subset_union (hYsub A) (hYsub B))
    have h2 : f (Y (A ∩ B)) ≤ f (Y A ∩ Y B) :=
      hYmin (A ∩ B) (Y A ∩ Y B) (Finset.inter_subset_inter (hYsub A) (hYsub B))
    exact (add_le_add h2 h1).trans (hf (Y A) (Y B))
  · intro A B hAB
    exact hYmin A (Y B) (le_trans hAB (hYsub B))
  · intro Z W hZW
    exact hYmin Z W hZW
  · intro Z
    exact ⟨Y Z, hYsub Z, rfl⟩

@[blueprint "lem:sum-prod-col-regroup"
  (statement := /-- Let $S_1$ and $S_2$ be finite ground sets and let $Z \subseteq S_1 \times S_2$
    be a finite subset. For every function $f \colon S_1 \times S_2 \to \mathbb{R}$ one has
    $\sum_{p \in Z} f(p) = \sum_{j \in S_2} \sum_{i \in Z^j} f(i, j)$, where $Z^j = \{\, i \in S_1 :
    (i, j) \in Z \,\}$ is the $j$-th column slice. -/)
  (proof := /-- Group the sum over $Z$ by second coordinate: since every $p \in Z$ has second
    coordinate in $S_2$, fiberwise summation gives $\sum_{p \in Z} f(p) = \sum_{j \in S_2}
    \sum_{p \in Z,\ p_2 = j} f(p)$. For each fixed $j$, the map $i \mapsto (i, j)$ is a bijection
    between the column slice $Z^j = \{\, i : (i, j) \in Z \,\}$ and the fiber $\{\, p \in Z :
    p_2 = j \,\}$, with inverse $p \mapsto p_1$; transporting the sum along this bijection replaces
    $\sum_{p \in Z,\ p_2 = j} f(p)$ by $\sum_{i \in Z^j} f(i, j)$. Combining the two steps yields
    the claim. -/)
  (title := /-- Column regrouping of a sum over a product subset -/)
  (latexEnv := "lemma")]
lemma sum_prod_col_regroup {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    [DecidableEq S₁] [DecidableEq S₂]
    (Z : Finset (S₁ × S₂)) (f : S₁ × S₂ → ℝ) :
    (∑ p ∈ Z, f p)
      = ∑ j, ∑ i ∈ Finset.univ.filter (fun i => (i, j) ∈ Z), f (i, j) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p => p.2) (t := Finset.univ)
      (fun p _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro j _
  refine Finset.sum_bij' (fun p _ => p.1) (fun i _ => (i, j)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.mem_filter] at hp; rw [← hp.2]; exact hp.1
  · intro i hi; rw [Finset.mem_filter] at hi ⊢; exact ⟨hi.2, rfl⟩
  · intro p hp; rw [Finset.mem_filter] at hp; ext <;> simp [hp.2]
  · intro i _; rfl
  · intro p hp; rw [Finset.mem_filter] at hp; rw [← hp.2]

@[blueprint "lem:sum-prod-row-regroup"
  (statement := /-- Let $S_1$ and $S_2$ be finite ground sets and let $Z \subseteq S_1 \times S_2$
    be a finite subset. For every function $f \colon S_1 \times S_2 \to \mathbb{R}$ one has
    $\sum_{p \in Z} f(p) = \sum_{i \in S_1} \sum_{j \in Z_i} f(i, j)$, where $Z_i = \{\, j \in S_2 :
    (i, j) \in Z \,\}$ is the $i$-th row slice. -/)
  (proof := /-- Group the sum over $Z$ by first coordinate: since every $p \in Z$ has first
    coordinate in $S_1$, fiberwise summation gives $\sum_{p \in Z} f(p) = \sum_{i \in S_1}
    \sum_{p \in Z,\ p_1 = i} f(p)$. For each fixed $i$, the map $j \mapsto (i, j)$ is a bijection
    between the row slice $Z_i = \{\, j : (i, j) \in Z \,\}$ and the fiber $\{\, p \in Z :
    p_1 = i \,\}$, with inverse $p \mapsto p_2$; transporting the sum along this bijection replaces
    $\sum_{p \in Z,\ p_1 = i} f(p)$ by $\sum_{j \in Z_i} f(i, j)$. Combining the two steps yields
    the claim. -/)
  (title := /-- Row regrouping of a sum over a product subset -/)
  (latexEnv := "lemma")]
lemma sum_prod_row_regroup {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    [DecidableEq S₁] [DecidableEq S₂]
    (Z : Finset (S₁ × S₂)) (f : S₁ × S₂ → ℝ) :
    (∑ p ∈ Z, f p)
      = ∑ i, ∑ j ∈ Finset.univ.filter (fun j => (i, j) ∈ Z), f (i, j) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p => p.1) (t := Finset.univ)
      (fun p _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro i _
  refine Finset.sum_bij' (fun p _ => p.2) (fun j _ => (i, j)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.mem_filter] at hp; rw [← hp.2]; exact hp.1
  · intro j hj; rw [Finset.mem_filter] at hj ⊢; exact ⟨hj.2, rfl⟩
  · intro p hp; rw [Finset.mem_filter] at hp; ext <;> simp [hp.2]
  · intro j _; rfl
  · intro p hp; rw [Finset.mem_filter] at hp; rw [← hp.2]

@[blueprint "lem:sum-integer-valued"
  (statement := /-- Let $I$ be a type and let $s \subseteq I$ be a finite subset. If
    $f \colon I \to \mathbb{R}$ takes an integer value at every element of $s$, i.e. for each
    $i \in s$ there is $n \in \mathbb{Z}$ with $f(i) = n$, then $\sum_{i \in s} f(i)$ is an
    integer. -/)
  (proof := /-- We argue by induction on the finite set $s$. If $s = \emptyset$ the sum is $0$,
    which equals the integer $0$. For the inductive step write $s$ as the insertion of $a$ into a
    finite set $t$ with $a \notin t$; then $\sum_{i \in s} f(i) = f(a) + \sum_{i \in t} f(i)$.
    By hypothesis $f(a) = n$ for some integer $n$, and by the induction hypothesis (whose premise
    holds for every element of $t \subseteq s$) $\sum_{i \in t} f(i) = m$ for some integer $m$;
    hence the total equals the integer $n + m$. -/)
  (title := /-- Integrality of a finite sum of integer values -/)
  (latexEnv := "lemma")]
lemma sum_integer_valued {I : Type*} (s : Finset I) (f : I → ℝ)
    (h : ∀ i ∈ s, ∃ n : ℤ, f i = (n : ℝ)) : ∃ n : ℤ, (∑ i ∈ s, f i) = (n : ℝ) := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨0, by simp⟩
  | @insert a t ha ih =>
    rw [Finset.sum_insert ha]
    obtain ⟨n, hn⟩ := h a (Finset.mem_insert_self a t)
    obtain ⟨m, hm⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact ⟨n + m, by push_cast; rw [hn, hm]⟩

@[blueprint "def:weighted-coupling"
  (statement := /-- Let $S_1$ and $S_2$ be finite ground sets, let
    $\varphi_1 \colon 2^{S_1} \to \mathbb{R}$ and $\varphi_2 \colon 2^{S_2} \to \mathbb{R}$ be set
    functions, and let $\mu_1 \colon S_1 \to \mathbb{R}$ and $\mu_2 \colon S_2 \to \mathbb{R}$ be
    weight vectors. The \emph{weighted coupling} associated with these data is the set function
    $\varphi \colon 2^{S_1 \times S_2} \to \mathbb{R}$ defined by
    $\varphi(Z) = \sum_{j \in S_2} \mu_2(j)\,\varphi_1(Z^j) + \sum_{i \in S_1} \mu_1(i)\,
    \varphi_2(Z_i) - \sum_{(i,j) \in Z} \mu_1(i)\,\mu_2(j)$, where $Z^j = \{\, i \in S_1 :
    (i, j) \in Z \,\}$ is the $j$-th column slice and $Z_i = \{\, j \in S_2 : (i, j) \in Z \,\}$
    is the $i$-th row slice. -/)
  (title := /-- Weighted coupling set function -/)
  (latexEnv := "definition")]
def weighted_coupling {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    [DecidableEq S₁] [DecidableEq S₂]
    (φ₁ : Finset S₁ → ℝ) (φ₂ : Finset S₂ → ℝ) (μ₁ : S₁ → ℝ) (μ₂ : S₂ → ℝ) :
    Finset (S₁ × S₂) → ℝ :=
  fun Z => (∑ j, μ₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ Z)))
      + (∑ i, μ₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ Z)))
      - ∑ p ∈ Z, μ₁ p.1 * μ₂ p.2

@[blueprint "lem:weighted-coupling-submodular"
  (statement := /-- Let $S_1$ and $S_2$ be finite ground sets and let
    $\varphi_1 \colon 2^{S_1} \to \mathbb{R}$ and $\varphi_2 \colon 2^{S_2} \to \mathbb{R}$ be
    polymatroid functions in the sense of \cref{def:is-polymatroid}. Let $\mu_1 \colon S_1 \to
    \mathbb{R}$ and $\mu_2 \colon S_2 \to \mathbb{R}$ be nonnegative weight vectors, i.e.
    $\mu_1(i) \ge 0$ and $\mu_2(j) \ge 0$ for all $i \in S_1$, $j \in S_2$. Then the weighted
    coupling of \cref{def:weighted-coupling} is submodular in the sense of
    \cref{def:is-submodular}. -/)
  (proof := /-- Fix $X, Y \subseteq S_1 \times S_2$. Taking column slices commutes with union and
    intersection, $(X \cup Y)^j = X^j \cup Y^j$ and $(X \cap Y)^j = X^j \cap Y^j$, and likewise
    for row slices. Since $\varphi_1$ is submodular (\cref{def:is-submodular}) and each
    $\mu_2(j) \ge 0$, for every $j$ we have $\mu_2(j)\,(\varphi_1(X^j \cap Y^j) + \varphi_1(X^j
    \cup Y^j)) \le \mu_2(j)\,(\varphi_1(X^j) + \varphi_1(Y^j))$; summing over $j$ via
    \cref{lem:finset-sum-le-sum-real} gives the column inequality. The same argument with
    $\varphi_2$ and $\mu_1 \ge 0$, again using \cref{lem:finset-sum-le-sum-real}, gives the row
    inequality.
    For the bilinear term, $\sum_{p \in X \cap Y} + \sum_{p \in X \cup Y} = \sum_{p \in X} +
    \sum_{p \in Y}$ by inclusion-exclusion for finite sums. Adding the column and row inequalities
    and subtracting the bilinear identity gives $\varphi(X \cap Y) + \varphi(X \cup Y) \le
    \varphi(X) + \varphi(Y)$, which is submodularity. -/)
  (title := /-- Submodularity of the weighted coupling -/)
  (latexEnv := "lemma")]
lemma weighted_coupling_submodular {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    [DecidableEq S₁] [DecidableEq S₂]
    (φ₁ : Finset S₁ → ℝ) (φ₂ : Finset S₂ → ℝ)
    (h₁ : is_polymatroid φ₁) (h₂ : is_polymatroid φ₂)
    (μ₁ : S₁ → ℝ) (μ₂ : S₂ → ℝ) (hμ₁ : ∀ i, 0 ≤ μ₁ i) (hμ₂ : ∀ j, 0 ≤ μ₂ j) :
    is_submodular (weighted_coupling φ₁ φ₂ μ₁ μ₂) := by
  classical
  obtain ⟨_, sub₁, _⟩ := h₁
  obtain ⟨_, sub₂, _⟩ := h₂
  intro X Y
  simp only [weighted_coupling]
  have hcolU : ∀ j : S₂, Finset.univ.filter (fun i => (i, j) ∈ X ∪ Y)
      = Finset.univ.filter (fun i => (i, j) ∈ X) ∪ Finset.univ.filter (fun i => (i, j) ∈ Y) := by
    intro j; ext i; simp [Finset.mem_filter, Finset.mem_union]
  have hcolI : ∀ j : S₂, Finset.univ.filter (fun i => (i, j) ∈ X ∩ Y)
      = Finset.univ.filter (fun i => (i, j) ∈ X) ∩ Finset.univ.filter (fun i => (i, j) ∈ Y) := by
    intro j; ext i; simp [Finset.mem_filter, Finset.mem_inter]
  have hrowU : ∀ i : S₁, Finset.univ.filter (fun j => (i, j) ∈ X ∪ Y)
      = Finset.univ.filter (fun j => (i, j) ∈ X) ∪ Finset.univ.filter (fun j => (i, j) ∈ Y) := by
    intro i; ext j; simp [Finset.mem_filter, Finset.mem_union]
  have hrowI : ∀ i : S₁, Finset.univ.filter (fun j => (i, j) ∈ X ∩ Y)
      = Finset.univ.filter (fun j => (i, j) ∈ X) ∩ Finset.univ.filter (fun j => (i, j) ∈ Y) := by
    intro i; ext j; simp [Finset.mem_filter, Finset.mem_inter]
  have hA : (∑ j, μ₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ X ∩ Y)))
        + (∑ j, μ₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ X ∪ Y)))
      ≤ (∑ j, μ₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ X)))
        + (∑ j, μ₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ Y))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply finset_sum_le_sum_real
    intro j _
    rw [hcolI j, hcolU j, ← mul_add, ← mul_add]
    exact mul_le_mul_of_nonneg_left (sub₁ _ _) (hμ₂ j)
  have hB : (∑ i, μ₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ X ∩ Y)))
        + (∑ i, μ₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ X ∪ Y)))
      ≤ (∑ i, μ₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ X)))
        + (∑ i, μ₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ Y))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply finset_sum_le_sum_real
    intro i _
    rw [hrowI i, hrowU i, ← mul_add, ← mul_add]
    exact mul_le_mul_of_nonneg_left (sub₂ _ _) (hμ₁ i)
  have hC : (∑ p ∈ X ∩ Y, μ₁ p.1 * μ₂ p.2) + (∑ p ∈ X ∪ Y, μ₁ p.1 * μ₂ p.2)
      = (∑ p ∈ X, μ₁ p.1 * μ₂ p.2) + (∑ p ∈ Y, μ₁ p.1 * μ₂ p.2) := by
    rw [add_comm]
    exact Finset.sum_union_inter
  rw [sub_add_sub_comm, sub_add_sub_comm, hC]
  apply sub_le_sub_right
  exact (add_add_add_comm _ _ _ _).trans_le
    ((add_le_add hA hB).trans_eq (add_add_add_comm _ _ _ _))

@[blueprint "lem:weighted-coupling-is-coupling"
  (statement := /-- Let $S_1$ and $S_2$ be finite ground sets and let
    $\varphi_1 \colon 2^{S_1} \to \mathbb{R}$ and $\varphi_2 \colon 2^{S_2} \to \mathbb{R}$ be
    polymatroid functions in the sense of \cref{def:is-polymatroid}. Let $\mu_1 \colon S_1 \to
    \mathbb{R}$ and $\mu_2 \colon S_2 \to \mathbb{R}$ be weight vectors whose total masses equal
    the values of $\varphi_1$ and $\varphi_2$ on the full ground sets, i.e. $\sum_{i \in S_1}
    \mu_1(i) = \varphi_1(S_1)$ and $\sum_{j \in S_2} \mu_2(j) = \varphi_2(S_2)$. Then the weighted
    coupling of \cref{def:weighted-coupling} is a coupling of $\varphi_1$ and $\varphi_2$ in the
    sense of \cref{def:is-coupling}. -/)
  (proof := /-- Write $\varphi$ for the weighted coupling. Fix $X_1 \subseteq S_1$ and consider
    $Z = X_1 \times S_2$. Each column slice $Z^j$ equals $X_1$, so the column term is
    $\sum_j \mu_2(j)\,\varphi_1(X_1) = \varphi_1(X_1)\,\varphi_2(S_2)$ using $\sum_j \mu_2(j) =
    \varphi_2(S_2)$ and \cref{lem:finset-sum-mul-real}. The row slice $Z_i$ equals $S_2$ when
    $i \in X_1$ and $\emptyset$ otherwise, so the row term collapses to $\sum_{i \in X_1}
    \mu_1(i)\,\varphi_2(S_2)$ using $\varphi_2(\emptyset) = 0$. Splitting the bilinear term over
    the Cartesian product with \cref{lem:finset-sum-product-real} gives $\sum_{i \in X_1}
    \mu_1(i)\,\varphi_2(S_2)$, which cancels the row term, leaving $\varphi(X_1 \times S_2) =
    \varphi_1(X_1)\,\varphi_2(S_2)$. Symmetrically, for $Z = S_1 \times X_2$ the row slices are
    all $X_2$, so the row term equals $\varphi_1(S_1)\,\varphi_2(X_2)$ via $\sum_i \mu_1(i) =
    \varphi_1(S_1)$ and \cref{lem:finset-sum-mul-real}, while the column term reduces to
    $\sum_{j \in X_2} \mu_2(j)\,\varphi_1(S_1)$; expanding the bilinear term with
    \cref{lem:finset-sum-product-real}, factoring each inner sum by \cref{lem:finset-mul-sum-real},
    and using $\sum_i \mu_1(i) = \varphi_1(S_1)$ shows the column and bilinear terms cancel, giving
    $\varphi(S_1 \times X_2) = \varphi_1(S_1)\,\varphi_2(X_2)$. These are the two marginal
    identities of \cref{def:is-coupling}. -/)
  (title := /-- The weighted coupling is a coupling -/)
  (latexEnv := "lemma")]
lemma weighted_coupling_is_coupling {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    [DecidableEq S₁] [DecidableEq S₂]
    (φ₁ : Finset S₁ → ℝ) (φ₂ : Finset S₂ → ℝ)
    (h₁ : is_polymatroid φ₁) (h₂ : is_polymatroid φ₂)
    (μ₁ : S₁ → ℝ) (μ₂ : S₂ → ℝ)
    (hsμ₁ : ∑ i, μ₁ i = φ₁ Finset.univ) (hsμ₂ : ∑ j, μ₂ j = φ₂ Finset.univ) :
    is_coupling φ₁ φ₂ (weighted_coupling φ₁ φ₂ μ₁ μ₂) := by
  classical
  obtain ⟨_, _, e₁⟩ := h₁
  obtain ⟨_, _, e₂⟩ := h₂
  constructor
  · intro X₁
    simp only [weighted_coupling]
    have hcol : ∀ j : S₂,
        Finset.univ.filter (fun i => (i, j) ∈ X₁ ×ˢ (Finset.univ : Finset S₂)) = X₁ := by
      intro j; ext i; simp [Finset.mem_filter, Finset.mem_product]
    have hrowmem : ∀ i : S₁,
        Finset.univ.filter (fun j => (i, j) ∈ X₁ ×ˢ (Finset.univ : Finset S₂))
          = if i ∈ X₁ then (Finset.univ : Finset S₂) else ∅ := by
      intro i
      by_cases hi : i ∈ X₁
      · rw [if_pos hi]; ext j; simp [Finset.mem_filter, Finset.mem_product, hi]
      · rw [if_neg hi]; ext j; simp [Finset.mem_filter, Finset.mem_product, hi]
    have hA : (∑ j, μ₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ X₁ ×ˢ (Finset.univ : Finset S₂))))
        = φ₁ X₁ * φ₂ Finset.univ := by
      have : (∑ j, μ₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ X₁ ×ˢ (Finset.univ : Finset S₂))))
          = ∑ j, μ₂ j * φ₁ X₁ := by
        apply Finset.sum_congr rfl
        intro j _; rw [hcol j]
      rw [this, ← finset_sum_mul_real, hsμ₂, mul_comm]
    have hB : (∑ i, μ₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ X₁ ×ˢ (Finset.univ : Finset S₂))))
        = ∑ i ∈ X₁, μ₁ i * φ₂ Finset.univ := by
      have hpt : ∀ i : S₁,
          μ₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ X₁ ×ˢ (Finset.univ : Finset S₂)))
            = if i ∈ X₁ then μ₁ i * φ₂ Finset.univ else 0 := by
        intro i
        by_cases hi : i ∈ X₁
        · rw [hrowmem i, if_pos hi, if_pos hi]
        · rw [hrowmem i, if_neg hi, if_neg hi, e₂, mul_zero]
      rw [Finset.sum_congr rfl (fun i _ => hpt i)]
      rw [← Finset.sum_filter, Finset.filter_univ_mem]
    have hC : (∑ p ∈ X₁ ×ˢ (Finset.univ : Finset S₂), μ₁ p.1 * μ₂ p.2)
        = ∑ i ∈ X₁, μ₁ i * φ₂ Finset.univ := by
      rw [finset_sum_product_real]
      apply Finset.sum_congr rfl
      intro i _
      rw [← hsμ₂, mul_comm, finset_sum_mul_real]
      apply Finset.sum_congr rfl
      intro b _
      rw [mul_comm]
    rw [hA, hB, hC, add_sub_cancel_right]
  · intro X₂
    simp only [weighted_coupling]
    have hrow : ∀ i : S₁,
        Finset.univ.filter (fun j => (i, j) ∈ (Finset.univ : Finset S₁) ×ˢ X₂) = X₂ := by
      intro i; ext j; simp [Finset.mem_filter, Finset.mem_product]
    have hcolmem : ∀ j : S₂,
        Finset.univ.filter (fun i => (i, j) ∈ (Finset.univ : Finset S₁) ×ˢ X₂)
          = if j ∈ X₂ then (Finset.univ : Finset S₁) else ∅ := by
      intro j
      by_cases hj : j ∈ X₂
      · rw [if_pos hj]; ext i; simp [Finset.mem_filter, Finset.mem_product, hj]
      · rw [if_neg hj]; ext i; simp [Finset.mem_filter, Finset.mem_product, hj]
    have hB : (∑ i, μ₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ (Finset.univ : Finset S₁) ×ˢ X₂)))
        = φ₁ Finset.univ * φ₂ X₂ := by
      have : (∑ i, μ₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ (Finset.univ : Finset S₁) ×ˢ X₂)))
          = ∑ i, μ₁ i * φ₂ X₂ := by
        apply Finset.sum_congr rfl
        intro i _; rw [hrow i]
      rw [this, ← finset_sum_mul_real, hsμ₁]
    have hA : (∑ j, μ₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ (Finset.univ : Finset S₁) ×ˢ X₂)))
        = ∑ j ∈ X₂, μ₂ j * φ₁ Finset.univ := by
      have hpt : ∀ j : S₂,
          μ₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ (Finset.univ : Finset S₁) ×ˢ X₂))
            = if j ∈ X₂ then μ₂ j * φ₁ Finset.univ else 0 := by
        intro j
        by_cases hj : j ∈ X₂
        · rw [hcolmem j, if_pos hj, if_pos hj]
        · rw [hcolmem j, if_neg hj, if_neg hj, e₁, mul_zero]
      rw [Finset.sum_congr rfl (fun j _ => hpt j)]
      rw [← Finset.sum_filter, Finset.filter_univ_mem]
    have hC : (∑ p ∈ (Finset.univ : Finset S₁) ×ˢ X₂, μ₁ p.1 * μ₂ p.2)
        = ∑ j ∈ X₂, μ₂ j * φ₁ Finset.univ := by
      rw [finset_sum_product_real]
      have hstep : (∑ i, ∑ j ∈ X₂, μ₁ i * μ₂ j)
          = ∑ i, μ₁ i * (∑ j ∈ X₂, μ₂ j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← finset_mul_sum_real]
      rw [hstep, ← finset_sum_mul_real, hsμ₁, ← finset_sum_mul_real]
      rw [mul_comm]
    rw [hA, hB, hC, add_sub_cancel_left]

@[blueprint "lem:weighted-row-bilinear-le"
  (statement := /-- Let $S_1$ and $S_2$ be finite ground sets, let
    $\varphi_2 \colon 2^{S_2} \to \mathbb{R}$ be a set function, and let $\mu_1 \colon S_1 \to
    \mathbb{R}$ and $\mu_2 \colon S_2 \to \mathbb{R}$ be weight vectors with $\mu_1(i) \ge 0$ for
    all $i$. Suppose $\sum_{j \in W} \mu_2(j) \le \varphi_2(W)$ for every $W \subseteq S_2$. Then
    for every $Z \subseteq S_1 \times S_2$ the bilinear term is dominated by the row term:
    $\sum_{(i,j) \in Z} \mu_1(i)\,\mu_2(j) \le \sum_{i \in S_1} \mu_1(i)\,\varphi_2(Z_i)$, where
    $Z_i = \{\, j \in S_2 : (i, j) \in Z \,\}$. -/)
  (proof := /-- Regroup the bilinear sum by rows using \cref{lem:sum-prod-row-regroup}:
    $\sum_{(i,j) \in Z} \mu_1(i)\,\mu_2(j) = \sum_{i \in S_1} \sum_{j \in Z_i} \mu_1(i)\,\mu_2(j)$.
    By \cref{lem:finset-mul-sum-real} the inner sum equals $\mu_1(i) \sum_{j \in Z_i} \mu_2(j)$.
    For each $i$, since $\mu_1(i) \ge 0$ and $\sum_{j \in Z_i} \mu_2(j) \le \varphi_2(Z_i)$ by the
    base-polyhedron hypothesis, monotonicity of multiplication by a nonnegative factor gives
    $\mu_1(i) \sum_{j \in Z_i} \mu_2(j) \le \mu_1(i)\,\varphi_2(Z_i)$. Summing these inequalities
    over $i$ with \cref{lem:finset-sum-le-sum-real} yields the claim. -/)
  (title := /-- The bilinear term is dominated by the row term -/)
  (latexEnv := "lemma")]
lemma weighted_row_bilinear_le {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    [DecidableEq S₁] [DecidableEq S₂]
    (φ₂ : Finset S₂ → ℝ) (μ₁ : S₁ → ℝ) (μ₂ : S₂ → ℝ)
    (hμ₁ : ∀ i, 0 ≤ μ₁ i)
    (hbase₂ : ∀ W : Finset S₂, ∑ j ∈ W, μ₂ j ≤ φ₂ W)
    (Z : Finset (S₁ × S₂)) :
    (∑ p ∈ Z, μ₁ p.1 * μ₂ p.2)
      ≤ ∑ i, μ₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ Z)) := by
  classical
  rw [sum_prod_row_regroup Z (fun p => μ₁ p.1 * μ₂ p.2)]
  apply finset_sum_le_sum_real
  intro i _
  have hinner : (∑ j ∈ Finset.univ.filter (fun j => (i, j) ∈ Z), μ₁ (i, j).1 * μ₂ (i, j).2)
      = μ₁ i * ∑ j ∈ Finset.univ.filter (fun j => (i, j) ∈ Z), μ₂ j := by
    rw [finset_mul_sum_real]
  rw [hinner]
  exact mul_le_mul_of_nonneg_left
    (hbase₂ (Finset.univ.filter (fun j => (i, j) ∈ Z))) (hμ₁ i)

@[blueprint "lem:weighted-col-bilinear-le"
  (statement := /-- Let $S_1$ and $S_2$ be finite ground sets, let
    $\varphi_1 \colon 2^{S_1} \to \mathbb{R}$ be a set function, and let $\mu_1 \colon S_1 \to
    \mathbb{R}$ and $\mu_2 \colon S_2 \to \mathbb{R}$ be weight vectors with $\mu_2(j) \ge 0$ for
    all $j$. Suppose $\sum_{i \in W} \mu_1(i) \le \varphi_1(W)$ for every $W \subseteq S_1$. Then
    for every $Z \subseteq S_1 \times S_2$ the bilinear term is dominated by the column term:
    $\sum_{(i,j) \in Z} \mu_1(i)\,\mu_2(j) \le \sum_{j \in S_2} \mu_2(j)\,\varphi_1(Z^j)$, where
    $Z^j = \{\, i \in S_1 : (i, j) \in Z \,\}$. -/)
  (proof := /-- Regroup the bilinear sum by columns using \cref{lem:sum-prod-col-regroup}:
    $\sum_{(i,j) \in Z} \mu_1(i)\,\mu_2(j) = \sum_{j \in S_2} \sum_{i \in Z^j} \mu_1(i)\,\mu_2(j)$.
    By \cref{lem:finset-sum-mul-real} the inner sum equals $\left(\sum_{i \in Z^j} \mu_1(i)\right)
    \mu_2(j)$. For each $j$, since $\mu_2(j) \ge 0$ and $\sum_{i \in Z^j} \mu_1(i) \le
    \varphi_1(Z^j)$ by the base-polyhedron hypothesis, monotonicity of multiplication by a
    nonnegative factor gives $\left(\sum_{i \in Z^j} \mu_1(i)\right)\mu_2(j) \le \varphi_1(Z^j)\,
    \mu_2(j) = \mu_2(j)\,\varphi_1(Z^j)$. Summing over $j$ with \cref{lem:finset-sum-le-sum-real}
    yields the claim. -/)
  (title := /-- The bilinear term is dominated by the column term -/)
  (latexEnv := "lemma")]
lemma weighted_col_bilinear_le {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    [DecidableEq S₁] [DecidableEq S₂]
    (φ₁ : Finset S₁ → ℝ) (μ₁ : S₁ → ℝ) (μ₂ : S₂ → ℝ)
    (hμ₂ : ∀ j, 0 ≤ μ₂ j)
    (hbase₁ : ∀ W : Finset S₁, ∑ i ∈ W, μ₁ i ≤ φ₁ W)
    (Z : Finset (S₁ × S₂)) :
    (∑ p ∈ Z, μ₁ p.1 * μ₂ p.2)
      ≤ ∑ j, μ₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ Z)) := by
  classical
  rw [sum_prod_col_regroup Z (fun p => μ₁ p.1 * μ₂ p.2)]
  apply finset_sum_le_sum_real
  intro j _
  have hinner : (∑ i ∈ Finset.univ.filter (fun i => (i, j) ∈ Z), μ₁ (i, j).1 * μ₂ (i, j).2)
      = (∑ i ∈ Finset.univ.filter (fun i => (i, j) ∈ Z), μ₁ i) * μ₂ j := by
    rw [finset_sum_mul_real]
  rw [hinner, mul_comm (μ₂ j)]
  exact mul_le_mul_of_nonneg_right
    (hbase₁ (Finset.univ.filter (fun i => (i, j) ∈ Z))) (hμ₂ j)

@[blueprint "lem:weighted-coupling-kbound"
  (statement := /-- Let $S_1$ and $S_2$ be finite ground sets and let $k_1, k_2 \in \mathbb{R}$.
    Let $\varphi_1 \colon 2^{S_1} \to \mathbb{R}$ and $\varphi_2 \colon 2^{S_2} \to \mathbb{R}$ be
    set functions with $\varphi_1(X) \le k_1 |X|$ for all $X$ and $\varphi_2(Y) \le k_2 |Y|$ for
    all $Y$. Let $\mu_1 \colon S_1 \to \mathbb{R}$ and $\mu_2 \colon S_2 \to \mathbb{R}$ be
    nonnegative weight vectors satisfying the base-polyhedron subset inequalities
    $\sum_{i \in W} \mu_1(i) \le \varphi_1(W)$ for all $W \subseteq S_1$ and $\sum_{j \in W}
    \mu_2(j) \le \varphi_2(W)$ for all $W \subseteq S_2$. Then the weighted coupling of
    \cref{def:weighted-coupling} satisfies $\varphi(Z) \le (k_1 \cdot k_2)\,|Z|$ for every
    $Z \subseteq S_1 \times S_2$. -/)
  (proof := /-- Write $\varphi(Z) = C + R - B$ with column term $C = \sum_j \mu_2(j)\,
    \varphi_1(Z^j)$, row term $R = \sum_i \mu_1(i)\,\varphi_2(Z_i)$, and bilinear term
    $B = \sum_{(i,j) \in Z} \mu_1(i)\,\mu_2(j)$. Bounding $\varphi_1(Z^j) \le k_1 |Z^j|$ for each
    column (with $\mu_2(j) \ge 0$) and regrouping by columns via \cref{lem:sum-prod-col-regroup}
    gives $C \le k_1 \sum_{(i,j) \in Z} \mu_2(j)$; similarly,
    bounding $\varphi_2(Z_i) \le k_2 |Z_i|$ and regrouping by rows via
    \cref{lem:sum-prod-row-regroup} gives $R \le k_2 \sum_{(i,j) \in Z} \mu_1(i)$. Hence
    $\varphi(Z) \le \sum_{(i,j) \in Z} \bigl(k_1 \mu_2(j) + k_2 \mu_1(i) - \mu_1(i)\mu_2(j)\bigr)$.
    For each $(i,j) \in Z$, the base-polyhedron singleton inequalities give $\mu_1(i) \le
    \varphi_1(\{i\}) \le k_1$ and $\mu_2(j) \le \varphi_2(\{j\}) \le k_2$, whence
    $(k_1 - \mu_1(i))(k_2 - \mu_2(j)) \ge 0$, i.e. $k_1 \mu_2(j) + k_2 \mu_1(i) - \mu_1(i)\mu_2(j)
    \le k_1 k_2$. Summing over $Z$ with \cref{lem:finset-sum-le-sum-real} and evaluating the
    constant sum gives $\varphi(Z) \le (k_1 k_2)\,|Z|$. -/)
  (title := /-- The weighted coupling obeys the $k_1 k_2$-bound -/)
  (latexEnv := "lemma")]
lemma weighted_coupling_kbound {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    [DecidableEq S₁] [DecidableEq S₂]
    (φ₁ : Finset S₁ → ℝ) (φ₂ : Finset S₂ → ℝ) (k₁ k₂ : ℝ)
    (hk₁ : ∀ X : Finset S₁, φ₁ X ≤ k₁ * (X.card : ℝ))
    (hk₂ : ∀ Y : Finset S₂, φ₂ Y ≤ k₂ * (Y.card : ℝ))
    (μ₁ : S₁ → ℝ) (μ₂ : S₂ → ℝ) (hμ₁ : ∀ i, 0 ≤ μ₁ i) (hμ₂ : ∀ j, 0 ≤ μ₂ j)
    (hbase₁ : ∀ W : Finset S₁, ∑ i ∈ W, μ₁ i ≤ φ₁ W)
    (hbase₂ : ∀ W : Finset S₂, ∑ j ∈ W, μ₂ j ≤ φ₂ W)
    (Z : Finset (S₁ × S₂)) :
    weighted_coupling φ₁ φ₂ μ₁ μ₂ Z ≤ (k₁ * k₂) * (Z.card : ℝ) := by
  classical
  have hμ₁k : ∀ i, μ₁ i ≤ k₁ := by
    intro i
    have h1 := hbase₁ {i}
    rw [Finset.sum_singleton] at h1
    have h2 := hk₁ {i}
    rw [Finset.card_singleton, Nat.cast_one, mul_one] at h2
    exact le_trans h1 h2
  have hμ₂k : ∀ j, μ₂ j ≤ k₂ := by
    intro j
    have h1 := hbase₂ {j}
    rw [Finset.sum_singleton] at h1
    have h2 := hk₂ {j}
    rw [Finset.card_singleton, Nat.cast_one, mul_one] at h2
    exact le_trans h1 h2
  have hCol : (∑ j, μ₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ Z)))
      ≤ ∑ p ∈ Z, k₁ * μ₂ p.2 := by
    have hstep : (∑ j, μ₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ Z)))
        ≤ ∑ j, μ₂ j * (k₁ * ((Finset.univ.filter (fun i => (i, j) ∈ Z)).card : ℝ)) := by
      apply finset_sum_le_sum_real
      intro j _
      exact mul_le_mul_of_nonneg_left (hk₁ _) (hμ₂ j)
    refine le_trans hstep (le_of_eq ?_)
    rw [sum_prod_col_regroup Z (fun p => k₁ * μ₂ p.2)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have h : (∑ i ∈ Finset.univ.filter (fun i => (i, j) ∈ Z), k₁ * μ₂ (i, j).2)
        = ∑ _i ∈ Finset.univ.filter (fun i => (i, j) ∈ Z), k₁ * μ₂ j := rfl
    rw [h, Finset.sum_const, nsmul_eq_mul]
    rw [mul_comm (μ₂ j), ← mul_assoc, mul_comm k₁, mul_assoc]
  have hRow : (∑ i, μ₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ Z)))
      ≤ ∑ p ∈ Z, k₂ * μ₁ p.1 := by
    have hstep : (∑ i, μ₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ Z)))
        ≤ ∑ i, μ₁ i * (k₂ * ((Finset.univ.filter (fun j => (i, j) ∈ Z)).card : ℝ)) := by
      apply finset_sum_le_sum_real
      intro i _
      exact mul_le_mul_of_nonneg_left (hk₂ _) (hμ₁ i)
    refine le_trans hstep (le_of_eq ?_)
    rw [sum_prod_row_regroup Z (fun p => k₂ * μ₁ p.1)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h : (∑ j ∈ Finset.univ.filter (fun j => (i, j) ∈ Z), k₂ * μ₁ (i, j).1)
        = ∑ _j ∈ Finset.univ.filter (fun j => (i, j) ∈ Z), k₂ * μ₁ i := rfl
    rw [h, Finset.sum_const, nsmul_eq_mul]
    rw [mul_comm (μ₁ i), ← mul_assoc, mul_comm k₂, mul_assoc]
  have hsum : weighted_coupling φ₁ φ₂ μ₁ μ₂ Z
      ≤ (∑ p ∈ Z, k₁ * μ₂ p.2) + (∑ p ∈ Z, k₂ * μ₁ p.1) - ∑ p ∈ Z, μ₁ p.1 * μ₂ p.2 := by
    simp only [weighted_coupling]
    exact sub_le_sub_right (add_le_add hCol hRow) _
  have hcombine : (∑ p ∈ Z, k₁ * μ₂ p.2) + (∑ p ∈ Z, k₂ * μ₁ p.1) - ∑ p ∈ Z, μ₁ p.1 * μ₂ p.2
      = ∑ p ∈ Z, (k₁ * μ₂ p.2 + k₂ * μ₁ p.1 - μ₁ p.1 * μ₂ p.2) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  have hbound : (∑ p ∈ Z, (k₁ * μ₂ p.2 + k₂ * μ₁ p.1 - μ₁ p.1 * μ₂ p.2))
      ≤ ∑ p ∈ Z, k₁ * k₂ := by
    apply finset_sum_le_sum_real
    intro p _
    have h := mul_nonneg (sub_nonneg.mpr (hμ₁k p.1)) (sub_nonneg.mpr (hμ₂k p.2))
    rw [mul_sub, sub_mul, sub_mul, mul_comm (μ₁ p.1) k₂] at h
    rw [← sub_nonneg]
    have e : k₁ * k₂ - (k₁ * μ₂ p.2 + k₂ * μ₁ p.1 - μ₁ p.1 * μ₂ p.2)
        = k₁ * k₂ - k₂ * μ₁ p.1 - (k₁ * μ₂ p.2 - μ₁ p.1 * μ₂ p.2) := by
      rw [add_comm (k₁ * μ₂ p.2) (k₂ * μ₁ p.1), add_sub_assoc, sub_add_eq_sub_sub]
    rw [e]; exact h
  have hconst : (∑ _p ∈ Z, k₁ * k₂) = (k₁ * k₂) * (Z.card : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  calc weighted_coupling φ₁ φ₂ μ₁ μ₂ Z
      ≤ (∑ p ∈ Z, k₁ * μ₂ p.2) + (∑ p ∈ Z, k₂ * μ₁ p.1) - ∑ p ∈ Z, μ₁ p.1 * μ₂ p.2 := hsum
    _ = ∑ p ∈ Z, (k₁ * μ₂ p.2 + k₂ * μ₁ p.1 - μ₁ p.1 * μ₂ p.2) := hcombine
    _ ≤ ∑ _p ∈ Z, k₁ * k₂ := hbound
    _ = (k₁ * k₂) * (Z.card : ℝ) := hconst

@[blueprint "lem:weighted-coupling-col-lower"
  (statement := /-- Let $S_1$ and $S_2$ be finite ground sets and let
    $\varphi_1 \colon 2^{S_1} \to \mathbb{R}$ and $\varphi_2 \colon 2^{S_2} \to \mathbb{R}$ be
    polymatroid functions in the sense of \cref{def:is-polymatroid}. Let $\mu_1 \colon S_1 \to
    \mathbb{R}$ and $\mu_2 \colon S_2 \to \mathbb{R}$ be nonnegative weight vectors with
    $\sum_{j \in S_2} \mu_2(j) = \varphi_2(S_2)$ and with $\sum_{j \in W} \mu_2(j) \le
    \varphi_2(W)$ for every $W \subseteq S_2$. Then for every $X_1 \subseteq S_1$ and every
    $W \subseteq S_1 \times S_2$ containing the rectangle $X_1 \times S_2$, the weighted coupling
    of \cref{def:weighted-coupling} satisfies $\varphi_1(X_1)\,\varphi_2(S_2) \le \varphi(W)$. -/)
  (proof := /-- Write $\varphi(W) = C + R - B$ with column term $C = \sum_j \mu_2(j)\,
    \varphi_1(W^j)$, row term $R = \sum_i \mu_1(i)\,\varphi_2(W_i)$, and bilinear term
    $B = \sum_{(i,j) \in W} \mu_1(i)\,\mu_2(j)$. Since $X_1 \times S_2 \subseteq W$, each column
    slice satisfies $X_1 \subseteq W^j$, so monotonicity of $\varphi_1$ (\cref{def:is-polymatroid})
    and $\mu_2(j) \ge 0$ give $\mu_2(j)\,\varphi_1(X_1) \le \mu_2(j)\,\varphi_1(W^j)$; summing
    these via \cref{lem:finset-sum-le-sum-real} and using $\sum_j \mu_2(j) = \varphi_2(S_2)$ with
    \cref{lem:finset-sum-mul-real} yields
    $\varphi_1(X_1)\,\varphi_2(S_2) \le C$. By \cref{lem:weighted-row-bilinear-le},
    $B \le R$, i.e. $R - B \ge 0$, using the base-polyhedron inequalities for $\mu_2$ and
    nonnegativity of $\mu_1$. Therefore $\varphi(W) = C + (R - B) \ge C \ge
    \varphi_1(X_1)\,\varphi_2(S_2)$. -/)
  (title := /-- Column lower bound for the weighted coupling on a rectangle -/)
  (latexEnv := "lemma")]
lemma weighted_coupling_col_lower {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    [DecidableEq S₁] [DecidableEq S₂]
    (φ₁ : Finset S₁ → ℝ) (φ₂ : Finset S₂ → ℝ)
    (h₁ : is_polymatroid φ₁)
    (μ₁ : S₁ → ℝ) (μ₂ : S₂ → ℝ) (hμ₁ : ∀ i, 0 ≤ μ₁ i) (hμ₂ : ∀ j, 0 ≤ μ₂ j)
    (hsμ₂ : ∑ j, μ₂ j = φ₂ Finset.univ)
    (hbase₂ : ∀ W : Finset S₂, ∑ j ∈ W, μ₂ j ≤ φ₂ W)
    (X₁ : Finset S₁) (W : Finset (S₁ × S₂))
    (hW : X₁ ×ˢ (Finset.univ : Finset S₂) ⊆ W) :
    φ₁ X₁ * φ₂ (Finset.univ : Finset S₂) ≤ weighted_coupling φ₁ φ₂ μ₁ μ₂ W := by
  classical
  obtain ⟨mono₁, _, _⟩ := h₁
  have hcol : ∀ j : S₂, X₁ ⊆ Finset.univ.filter (fun i => (i, j) ∈ W) := by
    intro j i hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hW ?_⟩
    rw [Finset.mem_product]; exact ⟨hi, Finset.mem_univ _⟩
  have hColLower : φ₁ X₁ * φ₂ (Finset.univ : Finset S₂)
      ≤ ∑ j, μ₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ W)) := by
    have hstep : (∑ j, μ₂ j * φ₁ X₁)
        ≤ ∑ j, μ₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ W)) := by
      apply finset_sum_le_sum_real
      intro j _
      exact mul_le_mul_of_nonneg_left (mono₁ (hcol j)) (hμ₂ j)
    have heq : (∑ j, μ₂ j * φ₁ X₁) = φ₁ X₁ * φ₂ (Finset.univ : Finset S₂) := by
      rw [← finset_sum_mul_real, hsμ₂, mul_comm]
    rw [← heq]; exact hstep
  have hRB : (∑ p ∈ W, μ₁ p.1 * μ₂ p.2)
      ≤ ∑ i, μ₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ W)) :=
    weighted_row_bilinear_le φ₂ μ₁ μ₂ hμ₁ hbase₂ W
  simp only [weighted_coupling]
  have : φ₁ X₁ * φ₂ (Finset.univ : Finset S₂)
      ≤ (∑ j, μ₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ W)))
        + ((∑ i, μ₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ W)))
          - ∑ p ∈ W, μ₁ p.1 * μ₂ p.2) := by
    have h0 : (0 : ℝ) ≤ (∑ i, μ₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ W)))
        - ∑ p ∈ W, μ₁ p.1 * μ₂ p.2 := sub_nonneg.mpr hRB
    calc φ₁ X₁ * φ₂ (Finset.univ : Finset S₂)
        ≤ ∑ j, μ₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ W)) := hColLower
      _ = (∑ j, μ₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ W))) + 0 := (add_zero _).symm
      _ ≤ (∑ j, μ₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ W)))
          + ((∑ i, μ₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ W)))
            - ∑ p ∈ W, μ₁ p.1 * μ₂ p.2) := by
          exact add_le_add (le_refl _) h0
  rw [← add_sub_assoc] at this
  exact this

@[blueprint "lem:weighted-coupling-row-lower"
  (statement := /-- Let $S_1$ and $S_2$ be finite ground sets and let
    $\varphi_1 \colon 2^{S_1} \to \mathbb{R}$ and $\varphi_2 \colon 2^{S_2} \to \mathbb{R}$ be
    polymatroid functions in the sense of \cref{def:is-polymatroid}. Let $\mu_1 \colon S_1 \to
    \mathbb{R}$ and $\mu_2 \colon S_2 \to \mathbb{R}$ be nonnegative weight vectors with
    $\sum_{i \in S_1} \mu_1(i) = \varphi_1(S_1)$ and with $\sum_{i \in W} \mu_1(i) \le
    \varphi_1(W)$ for every $W \subseteq S_1$. Then for every $X_2 \subseteq S_2$ and every
    $W \subseteq S_1 \times S_2$ containing the rectangle $S_1 \times X_2$, the weighted coupling
    of \cref{def:weighted-coupling} satisfies $\varphi_1(S_1)\,\varphi_2(X_2) \le \varphi(W)$. -/)
  (proof := /-- Write $\varphi(W) = C + R - B$ with column term $C = \sum_j \mu_2(j)\,
    \varphi_1(W^j)$, row term $R = \sum_i \mu_1(i)\,\varphi_2(W_i)$, and bilinear term
    $B = \sum_{(i,j) \in W} \mu_1(i)\,\mu_2(j)$. Since $S_1 \times X_2 \subseteq W$, each row
    slice satisfies $X_2 \subseteq W_i$, so monotonicity of $\varphi_2$ (\cref{def:is-polymatroid})
    and $\mu_1(i) \ge 0$ give $\mu_1(i)\,\varphi_2(X_2) \le \mu_1(i)\,\varphi_2(W_i)$; summing
    these via \cref{lem:finset-sum-le-sum-real} and using $\sum_i \mu_1(i) = \varphi_1(S_1)$ with
    \cref{lem:finset-sum-mul-real} yields
    $\varphi_1(S_1)\,\varphi_2(X_2) \le R$. By \cref{lem:weighted-col-bilinear-le}, $B \le C$, i.e.
    $C - B \ge 0$, using the base-polyhedron inequalities for $\mu_1$ and nonnegativity of
    $\mu_2$. Therefore $\varphi(W) = R + (C - B) \ge R \ge \varphi_1(S_1)\,\varphi_2(X_2)$. -/)
  (title := /-- Row lower bound for the weighted coupling on a rectangle -/)
  (latexEnv := "lemma")]
lemma weighted_coupling_row_lower {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    [DecidableEq S₁] [DecidableEq S₂]
    (φ₁ : Finset S₁ → ℝ) (φ₂ : Finset S₂ → ℝ)
    (h₂ : is_polymatroid φ₂)
    (μ₁ : S₁ → ℝ) (μ₂ : S₂ → ℝ) (hμ₁ : ∀ i, 0 ≤ μ₁ i) (hμ₂ : ∀ j, 0 ≤ μ₂ j)
    (hsμ₁ : ∑ i, μ₁ i = φ₁ Finset.univ)
    (hbase₁ : ∀ W : Finset S₁, ∑ i ∈ W, μ₁ i ≤ φ₁ W)
    (X₂ : Finset S₂) (W : Finset (S₁ × S₂))
    (hW : (Finset.univ : Finset S₁) ×ˢ X₂ ⊆ W) :
    φ₁ (Finset.univ : Finset S₁) * φ₂ X₂ ≤ weighted_coupling φ₁ φ₂ μ₁ μ₂ W := by
  classical
  obtain ⟨mono₂, _, _⟩ := h₂
  have hrow : ∀ i : S₁, X₂ ⊆ Finset.univ.filter (fun j => (i, j) ∈ W) := by
    intro i j hj
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hW ?_⟩
    rw [Finset.mem_product]; exact ⟨Finset.mem_univ _, hj⟩
  have hRowLower : φ₁ (Finset.univ : Finset S₁) * φ₂ X₂
      ≤ ∑ i, μ₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ W)) := by
    have hstep : (∑ i, μ₁ i * φ₂ X₂)
        ≤ ∑ i, μ₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ W)) := by
      apply finset_sum_le_sum_real
      intro i _
      exact mul_le_mul_of_nonneg_left (mono₂ (hrow i)) (hμ₁ i)
    have heq : (∑ i, μ₁ i * φ₂ X₂) = φ₁ (Finset.univ : Finset S₁) * φ₂ X₂ := by
      rw [← finset_sum_mul_real, hsμ₁]
    rw [← heq]; exact hstep
  have hCB : (∑ p ∈ W, μ₁ p.1 * μ₂ p.2)
      ≤ ∑ j, μ₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ W)) :=
    weighted_col_bilinear_le φ₁ μ₁ μ₂ hμ₂ hbase₁ W
  simp only [weighted_coupling]
  have hgoal : φ₁ (Finset.univ : Finset S₁) * φ₂ X₂
      ≤ ((∑ j, μ₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ W)))
          - ∑ p ∈ W, μ₁ p.1 * μ₂ p.2)
        + ∑ i, μ₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ W)) := by
    have h0 : (0 : ℝ) ≤ (∑ j, μ₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ W)))
        - ∑ p ∈ W, μ₁ p.1 * μ₂ p.2 := sub_nonneg.mpr hCB
    calc φ₁ (Finset.univ : Finset S₁) * φ₂ X₂
        ≤ ∑ i, μ₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ W)) := hRowLower
      _ = 0 + ∑ i, μ₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ W)) := (zero_add _).symm
      _ ≤ ((∑ j, μ₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ W)))
            - ∑ p ∈ W, μ₁ p.1 * μ₂ p.2)
          + ∑ i, μ₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ W)) := by
          exact add_le_add h0 (le_refl _)
  have hrewrite : ((∑ j, μ₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ W)))
          - ∑ p ∈ W, μ₁ p.1 * μ₂ p.2)
        + ∑ i, μ₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ W))
      = (∑ j, μ₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ W)))
        + (∑ i, μ₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ W)))
        - ∑ p ∈ W, μ₁ p.1 * μ₂ p.2 := by
    rw [sub_add_eq_add_sub]
  rw [hrewrite] at hgoal
  exact hgoal

@[blueprint "lem:weighted-coupling-integer"
  (statement := /-- Let $S_1$ and $S_2$ be finite ground sets and let
    $\varphi_1 \colon 2^{S_1} \to \mathbb{R}$, $\varphi_2 \colon 2^{S_2} \to \mathbb{R}$,
    $\mu_1 \colon S_1 \to \mathbb{R}$ and $\mu_2 \colon S_2 \to \mathbb{R}$ take integer values,
    i.e. every $\varphi_1(X)$, $\varphi_2(Y)$, $\mu_1(i)$ and $\mu_2(j)$ is an integer. Then for
    every $Z \subseteq S_1 \times S_2$ the value of the weighted coupling of
    \cref{def:weighted-coupling} is an integer. -/)
  (proof := /-- The weighted coupling value is $\varphi(Z) = C + R - B$ with $C = \sum_j
    \mu_2(j)\,\varphi_1(Z^j)$, $R = \sum_i \mu_1(i)\,\varphi_2(Z_i)$ and $B = \sum_{(i,j) \in Z}
    \mu_1(i)\,\mu_2(j)$. Each summand of $C$ is a product $\mu_2(j)\,\varphi_1(Z^j)$ of integers,
    hence an integer, so by \cref{lem:sum-integer-valued} the sum $C$ is an integer; the same
    argument shows $R$ and $B$ are integers. A difference of sums of integers is an integer,
    so $\varphi(Z)$ is an integer. -/)
  (title := /-- Integrality of the weighted coupling -/)
  (latexEnv := "lemma")]
lemma weighted_coupling_integer {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    [DecidableEq S₁] [DecidableEq S₂]
    (φ₁ : Finset S₁ → ℝ) (φ₂ : Finset S₂ → ℝ) (μ₁ : S₁ → ℝ) (μ₂ : S₂ → ℝ)
    (hiμ₁ : ∀ i, ∃ n : ℤ, μ₁ i = (n : ℝ)) (hiμ₂ : ∀ j, ∃ n : ℤ, μ₂ j = (n : ℝ))
    (hiφ₁ : ∀ X, ∃ n : ℤ, φ₁ X = (n : ℝ)) (hiφ₂ : ∀ X, ∃ n : ℤ, φ₂ X = (n : ℝ))
    (Z : Finset (S₁ × S₂)) :
    ∃ n : ℤ, weighted_coupling φ₁ φ₂ μ₁ μ₂ Z = (n : ℝ) := by
  classical
  simp only [weighted_coupling]
  obtain ⟨a, ha⟩ := sum_integer_valued Finset.univ
    (fun j => μ₂ j * φ₁ (Finset.univ.filter (fun i => (i, j) ∈ Z)))
    (by
      intro j _
      obtain ⟨p, hp⟩ := hiμ₂ j
      obtain ⟨q, hq⟩ := hiφ₁ (Finset.univ.filter (fun i => (i, j) ∈ Z))
      exact ⟨p * q, by rw [hp, hq, Int.cast_mul]⟩)
  obtain ⟨b, hb⟩ := sum_integer_valued Finset.univ
    (fun i => μ₁ i * φ₂ (Finset.univ.filter (fun j => (i, j) ∈ Z)))
    (by
      intro i _
      obtain ⟨p, hp⟩ := hiμ₁ i
      obtain ⟨q, hq⟩ := hiφ₂ (Finset.univ.filter (fun j => (i, j) ∈ Z))
      exact ⟨p * q, by rw [hp, hq, Int.cast_mul]⟩)
  obtain ⟨c, hc⟩ := sum_integer_valued Z (fun p => μ₁ p.1 * μ₂ p.2)
    (by
      intro p _
      obtain ⟨u, hu⟩ := hiμ₁ p.1
      obtain ⟨v, hv⟩ := hiμ₂ p.2
      exact ⟨u * v, by rw [hu, hv, Int.cast_mul]⟩)
  exact ⟨a + b - c, by rw [ha, hb, hc, Int.cast_sub, Int.cast_add]⟩

@[blueprint "thm:poly"
  (statement := /-- Let $S_1$ and $S_2$ be finite ground sets and let $k_1, k_2 \in \mathbb{R}$.
    Let $\varphi_1 \colon 2^{S_1} \to \mathbb{R}$ be a $k_1$-polymatroid function and
    $\varphi_2 \colon 2^{S_2} \to \mathbb{R}$ be a $k_2$-polymatroid function in the sense of
    \cref{def:is-k-polymatroid}. Then there exists a set function
    $\varphi \colon 2^{S_1 \times S_2} \to \mathbb{R}$ that is a $(k_1 \cdot k_2)$-polymatroid
    function (\cref{def:is-k-polymatroid}) and a coupling of $\varphi_1$ and $\varphi_2$
    (\cref{def:is-coupling}); moreover $\varphi$ is integer-valued
    (\cref{def:is-integer-valued}) whenever both $\varphi_1$ and $\varphi_2$ are
    integer-valued. -/)
  (proof := /-- Since $\varphi_1$ and $\varphi_2$ are polymatroid functions, applying
    \cref{lem:base-polyhedron-integral} to each yields base-polyhedron vectors $\mu_1$ and
    $\mu_2$ that are nonnegative, tight ($\sum_i \mu_1(i) = \varphi_1(S_1)$ and $\sum_j \mu_2(j) =
    \varphi_2(S_2)$), satisfy the subset inequalities $\sum_{i \in W} \mu_1(i) \le \varphi_1(W)$
    and $\sum_{j \in W} \mu_2(j) \le \varphi_2(W)$, and are integral when $\varphi_1$
    respectively $\varphi_2$ are integer-valued. The existence of a submodular coupling of
    $\varphi_1$ and $\varphi_2$ is guaranteed by \cref{lem:submodular-coupling}; we strengthen
    it here to a $(k_1 k_2)$-polymatroid coupling by exhibiting an explicit monotone construction.
    Let $f = \varphi^{\mu_1,\mu_2}$ be the weighted
    coupling of \cref{def:weighted-coupling}; it is submodular by
    \cref{lem:weighted-coupling-submodular} and is a coupling of $\varphi_1$ and $\varphi_2$ by
    \cref{lem:weighted-coupling-is-coupling}. Let $g$ be the monotone lower envelope of $f$
    obtained from \cref{lem:monotone-hull}: $g$ is submodular and increasing, satisfies
    $g(Z) \le f(W)$ whenever $Z \subseteq W$, and for each $Z$ there is a superset $Y \supseteq Z$
    with $g(Z) = f(Y)$. We show $g$ is the required function. \emph{Coupling.} For the column
    identity, $g(X_1 \times S_2) \le f(X_1 \times S_2) = \varphi_1(X_1)\,\varphi_2(S_2)$ by the
    envelope inequality (taking $W = X_1 \times S_2$) and
    \cref{lem:weighted-coupling-is-coupling}; for the reverse inequality, choosing a minimizing
    superset $Y \supseteq X_1 \times S_2$ with $g(X_1 \times S_2) = f(Y)$,
    \cref{lem:weighted-coupling-col-lower} gives $\varphi_1(X_1)\,\varphi_2(S_2) \le f(Y)$. The row
    identity follows symmetrically from \cref{lem:weighted-coupling-is-coupling} and
    \cref{lem:weighted-coupling-row-lower}. \emph{Polymatroid.} $g$ is increasing and submodular
    by \cref{lem:monotone-hull}; $g(\emptyset) = 0$ because $g(\emptyset \times S_2) =
    \varphi_1(\emptyset)\,\varphi_2(S_2) = 0$ by the column identity and $\varphi_1(\emptyset) =
    0$; and the $(k_1 k_2)$-bound holds since $g(Z) \le f(Z) \le (k_1 k_2)\,|Z|$ by the envelope
    inequality and \cref{lem:weighted-coupling-kbound}. \emph{Integrality.} When $\varphi_1$ and
    $\varphi_2$ are integer-valued, $\mu_1$ and $\mu_2$ are integral, so for the superset $Y$ with
    $g(Z) = f(Y)$ the value $f(Y)$ is an integer by \cref{lem:weighted-coupling-integer}; hence
    $g(Z)$ is an integer. Thus $g$ is the required coupling. -/)
  (title := /-- Polymatroid coupling of two polymatroids -/)
  (latexEnv := "theorem")]
theorem poly {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    [DecidableEq S₁] [DecidableEq S₂]
    (k₁ k₂ : ℝ) (φ₁ : Finset S₁ → ℝ) (φ₂ : Finset S₂ → ℝ)
    (h₁ : is_k_polymatroid k₁ φ₁) (h₂ : is_k_polymatroid k₂ φ₂) :
    ∃ φ : Finset (S₁ × S₂) → ℝ,
      is_k_polymatroid (k₁ * k₂) φ ∧ is_coupling φ₁ φ₂ φ ∧
      (is_integer_valued φ₁ → is_integer_valued φ₂ → is_integer_valued φ) := by
  classical
  haveI : Fintype (S₁ × S₂) :=
    Fintype.mk (Finset.univ ×ˢ Finset.univ) (fun x => by simp [Finset.mem_product])
  obtain ⟨hp₁, hk₁⟩ := h₁
  obtain ⟨hp₂, hk₂⟩ := h₂
  obtain ⟨μ₁, hbp₁, hint₁⟩ := base_polyhedron_integral φ₁ hp₁
  obtain ⟨μ₂, hbp₂, hint₂⟩ := base_polyhedron_integral φ₂ hp₂
  obtain ⟨hμ₁nn, hsμ₁, hbase₁⟩ := hbp₁
  obtain ⟨hμ₂nn, hsμ₂, hbase₂⟩ := hbp₂
  have _hsc : ∃ φ : Finset (S₁ × S₂) → ℝ, is_submodular φ ∧ is_coupling φ₁ φ₂ φ :=
    submodular_coupling φ₁ φ₂ hp₁ hp₂
  have hfsub : is_submodular (weighted_coupling φ₁ φ₂ μ₁ μ₂) :=
    weighted_coupling_submodular φ₁ φ₂ hp₁ hp₂ μ₁ μ₂ hμ₁nn hμ₂nn
  obtain ⟨g, hgsub, hgmono, hgle, hgeq⟩ := monotone_hull _ hfsub
  have hfcoup : is_coupling φ₁ φ₂ (weighted_coupling φ₁ φ₂ μ₁ μ₂) :=
    weighted_coupling_is_coupling φ₁ φ₂ hp₁ hp₂ μ₁ μ₂ hsμ₁ hsμ₂
  have hgcoup₁ : ∀ X₁ : Finset S₁,
      g (X₁ ×ˢ (Finset.univ : Finset S₂)) = φ₁ X₁ * φ₂ (Finset.univ : Finset S₂) := by
    intro X₁
    refine le_antisymm ?_ ?_
    · have hle : g (X₁ ×ˢ (Finset.univ : Finset S₂))
          ≤ weighted_coupling φ₁ φ₂ μ₁ μ₂ (X₁ ×ˢ (Finset.univ : Finset S₂)) :=
        hgle _ _ (Finset.Subset.refl _)
      rwa [hfcoup.1 X₁] at hle
    · obtain ⟨Y, hYsub, hYeq⟩ := hgeq (X₁ ×ˢ (Finset.univ : Finset S₂))
      rw [hYeq]
      exact weighted_coupling_col_lower φ₁ φ₂ hp₁ μ₁ μ₂ hμ₁nn hμ₂nn hsμ₂ hbase₂ X₁ Y hYsub
  have hgcoup₂ : ∀ X₂ : Finset S₂,
      g ((Finset.univ : Finset S₁) ×ˢ X₂) = φ₁ (Finset.univ : Finset S₁) * φ₂ X₂ := by
    intro X₂
    refine le_antisymm ?_ ?_
    · have hle : g ((Finset.univ : Finset S₁) ×ˢ X₂)
          ≤ weighted_coupling φ₁ φ₂ μ₁ μ₂ ((Finset.univ : Finset S₁) ×ˢ X₂) :=
        hgle _ _ (Finset.Subset.refl _)
      rwa [hfcoup.2 X₂] at hle
    · obtain ⟨Y, hYsub, hYeq⟩ := hgeq ((Finset.univ : Finset S₁) ×ˢ X₂)
      rw [hYeq]
      exact weighted_coupling_row_lower φ₁ φ₂ hp₂ μ₁ μ₂ hμ₁nn hμ₂nn hsμ₁ hbase₁ X₂ Y hYsub
  have hgempty : g ∅ = 0 := by
    have h := hgcoup₁ ∅
    rw [Finset.empty_product] at h
    rw [h, hp₁.2.2, zero_mul]
  have hgkbound : ∀ X : Finset (S₁ × S₂), g X ≤ (k₁ * k₂) * (X.card : ℝ) := by
    intro X
    exact le_trans (hgle X X (Finset.Subset.refl _))
      (weighted_coupling_kbound φ₁ φ₂ k₁ k₂ hk₁ hk₂ μ₁ μ₂ hμ₁nn hμ₂nn hbase₁ hbase₂ X)
  refine ⟨g, ⟨⟨hgmono, hgsub, hgempty⟩, hgkbound⟩, ⟨hgcoup₁, hgcoup₂⟩, ?_⟩
  intro hiv₁ hiv₂ X
  obtain ⟨Y, _, hYeq⟩ := hgeq X
  rw [hYeq]
  exact weighted_coupling_integer φ₁ φ₂ μ₁ μ₂ (hint₁ hiv₁) (hint₂ hiv₂) hiv₁ hiv₂ Y

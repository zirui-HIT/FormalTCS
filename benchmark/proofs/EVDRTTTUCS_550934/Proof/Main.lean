import Architect
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Radon
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Lattice.Nat

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:is-union-of-convex"
  (statement := /-- Let $d \ge 1$ and $s \ge 1$ be integers. A set $C \subseteq \Re^d$ is
    \emph{$s$-convex} if there exists a family $(K_i)_{i \in \{1, \dots, s\}}$ of convex
    subsets of $\Re^d$ such that $C = \bigcup_{i=1}^{s} K_i$; that is, $C$ is a union of
    $s$ convex sets. Members of the family are not required to be nonempty or distinct,
    so every $s$-convex set is also $s'$-convex for every $s' \ge s$. The notion of a
    \emph{$t$-convex} set is defined analogously, with $t$ in place of $s$. -/)
  (title := /-- Unions of $s$ convex sets -/)
  (latexEnv := "definition")]
def is_union_of_convex (d s : ℕ) (C : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ K : Fin s → Set (EuclideanSpace ℝ (Fin d)),
    (∀ i, Convex ℝ (K i)) ∧ C = ⋃ i, K i

@[blueprint "def:has-radon-partition-property"
  (statement := /-- Let $d, s, t \ge 1$ and $n \ge 0$ be integers. We say that $n$
    \emph{has the $(d,s,t)$-Radon partition property} if for every set $P \subseteq \Re^d$
    of exactly $n$ points there is a partition $P = A \cup B$ with $A \cap B = \emptyset$
    such that, for every $s$-convex set $C \subseteq \Re^d$ with $A \subseteq C$ and every
    $t$-convex set $D \subseteq \Re^d$ with $B \subseteq D$, one has $C \cap D \neq \emptyset$.
    Here $s$-convexity and $t$-convexity are understood in the sense of
    \cref{def:is-union-of-convex}. -/)
  (title := /-- The $(d,s,t)$-Radon partition property of an integer -/)
  (latexEnv := "definition")]
def has_radon_partition_property (d s t n : ℕ) : Prop :=
  ∀ P : Finset (EuclideanSpace ℝ (Fin d)), P.card = n →
    ∃ A B : Finset (EuclideanSpace ℝ (Fin d)),
      A ∪ B = P ∧ Disjoint A B ∧
      ∀ C D : Set (EuclideanSpace ℝ (Fin d)),
        is_union_of_convex d s C → is_union_of_convex d t D →
        (A : Set (EuclideanSpace ℝ (Fin d))) ⊆ C →
        (B : Set (EuclideanSpace ℝ (Fin d))) ⊆ D →
        (C ∩ D).Nonempty

@[blueprint "def:radon-number"
  (statement := /-- Let $d, s, t \ge 1$ be integers. The \emph{Radon number}
    $f(d,s,t)$ is the least integer $n$ having the $(d,s,t)$-Radon partition property of
    \cref{def:has-radon-partition-property}, that is,
    \[ f(d,s,t) = \inf \{ n \in \mathbb{N} : n \text{ has the } (d,s,t)\text{-Radon partition property} \}, \]
    the infimum being taken in $\mathbb{N}$ and understood to be $0$ when the set is empty.
    Radon's theorem is the case $f(d,1,1) = d+2$. -/)
  (title := /-- The Radon number $f(d,s,t)$ for unions of convex sets -/)
  (latexEnv := "definition")]
noncomputable def radon_number (d s t : ℕ) : ℕ :=
  sInf {n : ℕ | has_radon_partition_property d s t n}

@[blueprint "lem:radon-number-le-of-property"
  (statement := /-- Let $d$, $s$, $t$ and $n$ be arbitrary natural numbers, with no
    lower bounds imposed on any of them. If $n$ has the $(d,s,t)$-Radon partition
    property of \cref{def:has-radon-partition-property}, then $f(d,s,t) \le n$, where
    $f$ is the Radon number of \cref{def:radon-number}. -/)
  (proof := /-- By \cref{def:radon-number}, $f(d,s,t) = \inf S$, where
    $S = \{ m \in \mathbb{N} : m \text{ has the } (d,s,t)\text{-Radon partition property} \}$
    and the infimum is taken in $\mathbb{N}$. The hypothesis states precisely that
    $n \in S$. Since the infimum of a nonempty subset of $\mathbb{N}$ is a lower bound
    for that subset, we get $\inf S \le n$, that is $f(d,s,t) \le n$. -/)
  (title := /-- A witness bounds the Radon number -/)
  (latexEnv := "lemma")]
lemma radon_number_le_of_property (d s t n : ℕ)
    (h : has_radon_partition_property d s t n) :
    radon_number d s t ≤ n := by
  exact Nat.sInf_le h

@[blueprint "lem:sum-choose-le-pow-exp"
  (statement := /-- Let $D$ and $n$ be integers with $1 \le D \le n$. Then the partial sum of
    binomial coefficients up to $D$ obeys
    \[ \sum_{k=0}^{D} \binom{n}{k} \le \left( \frac{n}{D} \right)^{D} e^{D} . \] -/)
  (proof := /-- Put $x = D/n$, so $0 < x \le 1$ and $n/D \ge 1$. Fix $k$ with $0 \le k \le D$.
    Since $n/D \ge 1$ and $D - k \ge 0$ we have $(n/D)^{D-k} \ge 1$, and because
    $(D/n)^{k} = ((n/D)^{k})^{-1}$ we get the identity
    $(n/D)^{D} (D/n)^{k} = (n/D)^{D-k}$. As $\binom{n}{k} \ge 0$, multiplying the inequality
    $(n/D)^{D-k} \ge 1$ by $\binom{n}{k}$ yields
    \[ \binom{n}{k} \le \binom{n}{k} (n/D)^{D-k} = (n/D)^{D} \left( \binom{n}{k} x^{k} \right) . \]
    Summing this over $k = 0, \dots, D$ and pulling the factor $(n/D)^{D}$ out of the sum gives
    \[ \sum_{k=0}^{D} \binom{n}{k} \le (n/D)^{D} \sum_{k=0}^{D} \binom{n}{k} x^{k} . \]
    All terms $\binom{n}{k} x^{k}$ are nonnegative and $D \le n$, so extending the range of
    summation from $\{0, \dots, D\}$ to $\{0, \dots, n\}$ only increases the sum. By the
    binomial theorem $\sum_{k=0}^{n} \binom{n}{k} x^{k} = (1 + x)^{n}$. Finally
    $1 + x \le e^{x}$ with $1 + x > 0$, so raising to the $n$-th power gives
    $(1+x)^{n} \le (e^{x})^{n} = e^{nx} = e^{D}$, because $nx = n \cdot (D/n) = D$. Combining
    the displayed inequalities with $(n/D)^{D} \ge 0$ gives the assertion. -/)
  (title := /-- A partial sum of binomial coefficients is at most $(n/D)^{D} e^{D}$ -/)
  (latexEnv := "lemma")]
lemma sum_choose_le_pow_exp (n D : ℕ) (hD : 0 < D) (hDn : D ≤ n) :
    ∑ k ∈ Finset.range (D + 1), (n.choose k : ℝ)
      ≤ ((n : ℝ) / (D : ℝ)) ^ D * Real.exp (D : ℝ) := by
  have hDR : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le hD hDn)
  have hndR : (D : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hDn
  have hxpos : (0 : ℝ) < (D : ℝ) / (n : ℝ) := div_pos hDR hnR
  have hge : (1 : ℝ) ≤ (n : ℝ) / (D : ℝ) := by
    rw [le_div_iff₀ hDR]; linarith
  have hpowD : (0 : ℝ) ≤ ((n : ℝ) / (D : ℝ)) ^ D :=
    pow_nonneg (div_nonneg (le_of_lt hnR) (le_of_lt hDR)) D
  have hterm : ∀ k ∈ Finset.range (D + 1),
      (n.choose k : ℝ)
        ≤ ((n : ℝ) / (D : ℝ)) ^ D * ((n.choose k : ℝ) * ((D : ℝ) / (n : ℝ)) ^ k) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hkD : k ≤ D := Nat.lt_succ_iff.mp hk
    have hne : ((n : ℝ) / (D : ℝ)) ≠ 0 := ne_of_gt (div_pos hnR hDR)
    have hinv : ((D : ℝ) / (n : ℝ)) ^ k = (((n : ℝ) / (D : ℝ)) ^ k)⁻¹ := by
      rw [← inv_pow, inv_div]
    have hratio : ((n : ℝ) / (D : ℝ)) ^ D * ((D : ℝ) / (n : ℝ)) ^ k
        = ((n : ℝ) / (D : ℝ)) ^ (D - k) := by
      rw [hinv, pow_sub₀ _ hne hkD]
    have hone : (1 : ℝ) ≤ ((n : ℝ) / (D : ℝ)) ^ (D - k) := by
      simpa using pow_le_pow_left₀ zero_le_one hge (D - k)
    have hcnn : (0 : ℝ) ≤ (n.choose k : ℝ) := Nat.cast_nonneg _
    have heq : ((n : ℝ) / (D : ℝ)) ^ D * ((n.choose k : ℝ) * ((D : ℝ) / (n : ℝ)) ^ k)
        = (n.choose k : ℝ) * ((n : ℝ) / (D : ℝ)) ^ (D - k) := by
      have hring : ((n : ℝ) / (D : ℝ)) ^ D * ((n.choose k : ℝ) * ((D : ℝ) / (n : ℝ)) ^ k)
          = (n.choose k : ℝ) * (((n : ℝ) / (D : ℝ)) ^ D * ((D : ℝ) / (n : ℝ)) ^ k) := by ring
      rw [hring, hratio]
    rw [heq]
    exact le_mul_of_one_le_right hcnn hone
  have hstep1 : ∑ k ∈ Finset.range (D + 1), (n.choose k : ℝ)
      ≤ ((n : ℝ) / (D : ℝ)) ^ D
        * ∑ k ∈ Finset.range (D + 1), ((n.choose k : ℝ) * ((D : ℝ) / (n : ℝ)) ^ k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hstep2 : ∑ k ∈ Finset.range (D + 1), ((n.choose k : ℝ) * ((D : ℝ) / (n : ℝ)) ^ k)
      ≤ ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℝ) * ((D : ℝ) / (n : ℝ)) ^ k) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) ?_
    intro k _ _
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_of_lt hxpos) k)
  have hstep3 : ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℝ) * ((D : ℝ) / (n : ℝ)) ^ k)
      = (1 + (D : ℝ) / (n : ℝ)) ^ n := by
    have hbinom := add_pow ((D : ℝ) / (n : ℝ)) 1 n
    simp only [one_pow, mul_one] at hbinom
    rw [show (1 + (D : ℝ) / (n : ℝ)) ^ n = ((D : ℝ) / (n : ℝ) + 1) ^ n from by ring, hbinom]
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  have hstep4 : (1 + (D : ℝ) / (n : ℝ)) ^ n ≤ Real.exp (D : ℝ) := by
    have hle : 1 + (D : ℝ) / (n : ℝ) ≤ Real.exp ((D : ℝ) / (n : ℝ)) := by
      have := Real.add_one_le_exp ((D : ℝ) / (n : ℝ))
      linarith
    have hpow : (1 + (D : ℝ) / (n : ℝ)) ^ n ≤ Real.exp ((D : ℝ) / (n : ℝ)) ^ n :=
      pow_le_pow_left₀ (by linarith) hle n
    have hmul : Real.exp ((D : ℝ) / (n : ℝ)) ^ n = Real.exp (D : ℝ) := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    linarith
  calc ∑ k ∈ Finset.range (D + 1), (n.choose k : ℝ)
      ≤ ((n : ℝ) / (D : ℝ)) ^ D
        * ∑ k ∈ Finset.range (D + 1), ((n.choose k : ℝ) * ((D : ℝ) / (n : ℝ)) ^ k) := hstep1
    _ ≤ ((n : ℝ) / (D : ℝ)) ^ D
        * ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℝ) * ((D : ℝ) / (n : ℝ)) ^ k) :=
        mul_le_mul_of_nonneg_left hstep2 hpowD
    _ = ((n : ℝ) / (D : ℝ)) ^ D * (1 + (D : ℝ) / (n : ℝ)) ^ n := by rw [hstep3]
    _ ≤ ((n : ℝ) / (D : ℝ)) ^ D * Real.exp (D : ℝ) :=
        mul_le_mul_of_nonneg_left hstep4 hpowD

@[blueprint "lem:sum-choose-pascal"
  (statement := /-- Let $m$ and $D$ be nonnegative integers. Then
    \[ \sum_{k=0}^{D} \binom{m+1}{k} = \sum_{k=0}^{D} \binom{m}{k} + \sum_{k=0}^{D-1} \binom{m}{k},
    \]
    where the last sum is empty when $D = 0$. -/)
  (proof := /-- We argue by induction on $D$. For $D = 0$ both sides equal $1$, since
    $\binom{m+1}{0} = \binom{m}{0} = 1$ and the last sum is empty. Assume the identity for $D$.
    Splitting off the top term of the left-hand sum and applying the induction hypothesis gives
    \[ \sum_{k=0}^{D+1} \binom{m+1}{k}
       = \sum_{k=0}^{D} \binom{m}{k} + \sum_{k=0}^{D-1} \binom{m}{k} + \binom{m+1}{D+1} . \]
    Pascal's rule gives $\binom{m+1}{D+1} = \binom{m}{D} + \binom{m}{D+1}$, and splitting off the
    top terms of the two sums on the right-hand side for $D+1$ gives
    \[ \sum_{k=0}^{D+1} \binom{m}{k} + \sum_{k=0}^{D} \binom{m}{k}
       = \sum_{k=0}^{D} \binom{m}{k} + \binom{m}{D+1} + \sum_{k=0}^{D-1} \binom{m}{k}
         + \binom{m}{D} . \]
    The two expressions agree, which is the identity for $D+1$. -/)
  (title := /-- Pascal's rule for partial sums of binomial coefficients -/)
  (latexEnv := "lemma")]
lemma sum_choose_pascal (m D : ℕ) :
    ∑ k ∈ Finset.range (D + 1), (m + 1).choose k
      = (∑ k ∈ Finset.range (D + 1), m.choose k) + ∑ k ∈ Finset.range D, m.choose k := by
  induction D with
  | zero => simp
  | succ D ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (f := fun k => m.choose k) (n := D + 1),
        Finset.sum_range_succ (f := fun k => m.choose k) (n := D), Nat.choose_succ_succ]
      ring

@[blueprint "lem:card-le-one-of-no-shattered-point"
  (statement := /-- Let $X$ be a finite set and let $\mathcal{A}$ be a finite family of subsets of
    $X$. Assume that no one-element subset of $X$ is shattered by $\mathcal{A}$, in the sense that
    for every $T \subseteq X$ with $|T| = 1$ there is a subset $T' \subseteq T$ with
    $S \cap T \neq T'$ for every $S \in \mathcal{A}$. Then $|\mathcal{A}| \le 1$. -/)
  (proof := /-- We show that any two members of $\mathcal{A}$ coincide. Let
    $S_1, S_2 \in \mathcal{A}$ and suppose $S_1 \neq S_2$. Then there is an element $y$ belonging
    to exactly one of $S_1$, $S_2$; since $S_1 \subseteq X$ and $S_2 \subseteq X$, we have
    $y \in X$, so $T = \{y\}$ is a one-element subset of $X$. For any $S \in \mathcal{A}$ we have
    $S \cap T = \{y\}$ if $y \in S$ and $S \cap T = \emptyset$ otherwise. As $y$ lies in exactly
    one of $S_1$, $S_2$, the two sets $S_1 \cap T$ and $S_2 \cap T$ are $\emptyset$ and $\{y\}$ in
    some order, so both subsets of $T$ are of the form $S \cap T$ with $S \in \mathcal{A}$. This
    contradicts the hypothesis applied to $T$, because the subset $T'$ it provides is either
    $\emptyset$ or $\{y\}$. Hence $S_1 = S_2$, and a family in which all members are equal has at
    most one element. -/)
  (title := /-- A family shattering no point has at most one member -/)
  (latexEnv := "lemma")]
lemma card_le_one_of_no_shattered_point {α : Type*} [DecidableEq α] (X : Finset α)
    (𝒜 : Finset (Finset α)) (h1 : ∀ S ∈ 𝒜, S ⊆ X)
    (h2 : ∀ T ⊆ X, T.card = 1 → ∃ T' ⊆ T, ∀ S ∈ 𝒜, S ∩ T ≠ T') :
    𝒜.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro S hS S' hS'
  by_contra hne
  obtain ⟨y, hy⟩ : ∃ y, (y ∈ S) ≠ (y ∈ S') := by
    by_contra hall
    exact hne (Finset.ext (fun y => by
      have := not_exists.mp hall y
      exact iff_of_eq (not_ne_iff.mp this)))
  have hyX : y ∈ X := by
    rcases Classical.em (y ∈ S) with hyS | hyS
    · exact h1 S hS hyS
    · have hyS' : y ∈ S' := by
        rcases Classical.em (y ∈ S') with h | h
        · exact h
        · exact absurd (by simp [hyS, h]) hy
      exact h1 S' hS' hyS'
  obtain ⟨T', hT'sub, hT'⟩ := h2 {y} (Finset.singleton_subset_iff.mpr hyX) (Finset.card_singleton y)
  have hSy : ∀ S₀ : Finset α, S₀ ∩ {y} = if y ∈ S₀ then {y} else ∅ := by
    intro S₀
    rcases Classical.em (y ∈ S₀) with h | h
    · simp [Finset.inter_singleton_of_mem h, h]
    · simp [Finset.inter_singleton_of_notMem h, h]
  rcases Finset.subset_singleton_iff.mp hT'sub with hT'eq | hT'eq
  · rcases Classical.em (y ∈ S) with hyS | hyS
    · have hyS' : y ∉ S' := by
        rcases Classical.em (y ∈ S') with h | h
        · exact absurd (by simp [hyS, h]) hy
        · exact h
      exact hT' S' hS' (by rw [hSy S', if_neg hyS', hT'eq])
    · exact hT' S hS (by rw [hSy S, if_neg hyS, hT'eq])
  · rcases Classical.em (y ∈ S) with hyS | hyS
    · exact hT' S hS (by rw [hSy S, if_pos hyS, hT'eq])
    · have hyS' : y ∈ S' := by
        rcases Classical.em (y ∈ S') with h | h
        · exact h
        · exact absurd (by simp [hyS, h]) hy
      exact hT' S' hS' (by rw [hSy S', if_pos hyS', hT'eq])

@[blueprint "lem:sauer-shelah"
  (statement := /-- Let $X$ be a finite set, let $D$ be a nonnegative integer, and let
    $\mathcal{A}$ be a finite family of subsets of $X$. Assume that $\mathcal{A}$ shatters no
    subset of $X$ of size $D+1$, that is, for every $T \subseteq X$ with $|T| = D+1$ there is a
    subset $T' \subseteq T$ such that $S \cap T \neq T'$ for every $S \in \mathcal{A}$. Then
    \[ |\mathcal{A}| \le \sum_{k=0}^{D} \binom{|X|}{k} . \] -/)
  (proof := /-- We argue by strong induction on $X$ with respect to strict inclusion, the
    statement being quantified over all $D$ and all families $\mathcal{A}$ of subsets of $X$.

    Suppose first that $X = \emptyset$. Then every $S \in \mathcal{A}$ satisfies $S = \emptyset$,
    so $|\mathcal{A}| \le 1$, and the right-hand side is at least the $k=0$ term
    $\binom{0}{0} = 1$.

    Otherwise fix $a \in X$ and set $Y = X \setminus \{a\}$, so that $Y \subsetneq X$,
    $a \notin Y$ and $|X| = |Y| + 1$. If $D = 0$, then no one-element subset of $X$ is
    shattered, so $|\mathcal{A}| \le 1$ by \cref{lem:card-le-one-of-no-shattered-point}, and
    the right-hand side is again at least $1$. So assume $D = D_0 + 1$.

    Following the standard shifting argument, define two families of subsets of $Y$:
    \[ \mathcal{A}_0 = \{ S \setminus \{a\} : S \in \mathcal{A} \}, \qquad
       \mathcal{A}_1 = \{ S \in \mathcal{A} : a \notin S,\ S \cup \{a\} \in \mathcal{A} \} . \]
    The map $S \mapsto S \setminus \{a\}$ sends $\mathcal{A}$ onto $\mathcal{A}_0$, and the
    preimage of a set $R \in \mathcal{A}_0$ consists of $R$ and $R \cup \{a\}$ only; it has two
    elements exactly when both lie in $\mathcal{A}$, i.e. exactly when $R \in \mathcal{A}_1$.
    Hence
    \[ |\mathcal{A}| \le |\mathcal{A}_0| + |\mathcal{A}_1| . \]

    We check the shattering hypotheses on $Y$. If $T \subseteq Y$ has $|T| = D+1$, then
    $T \subseteq X$ and any witness $T'$ for $T$ against $\mathcal{A}$ also works against
    $\mathcal{A}_0$: for $R = S \setminus \{a\} \in \mathcal{A}_0$ we have
    $R \cap T = S \cap T$ because $a \notin T$. So $\mathcal{A}_0$ shatters no subset of $Y$ of
    size $D+1$, and the induction hypothesis applied to $Y$, $D$ and $\mathcal{A}_0$ gives
    $|\mathcal{A}_0| \le \sum_{k=0}^{D} \binom{|Y|}{k}$.

    If $T \subseteq Y$ has $|T| = D_0+1$, consider $T \cup \{a\} \subseteq X$, which has
    $|T \cup \{a\}| = D_0 + 2 = D+1$ since $a \notin T$. Let $T'$ be a witness for it against
    $\mathcal{A}$. We claim $T' \setminus \{a\}$ is a witness for $T$ against $\mathcal{A}_1$.
    Indeed, let $S \in \mathcal{A}_1$ and suppose $S \cap T = T' \setminus \{a\}$. Both $S$ and
    $S \cup \{a\}$ lie in $\mathcal{A}$, and $a \notin S$, so
    $S \cap (T \cup \{a\}) = S \cap T = T' \setminus \{a\}$ and
    $(S \cup \{a\}) \cap (T \cup \{a\}) = (S \cap T) \cup \{a\} = (T' \setminus \{a\}) \cup \{a\}$.
    If $a \in T'$ the second set equals $T'$, and if $a \notin T'$ the first set equals $T'$; in
    both cases some member of $\mathcal{A}$ meets $T \cup \{a\}$ in exactly $T'$, contradicting
    the choice of $T'$. So $\mathcal{A}_1$ shatters no subset of $Y$ of size $D_0+1$, and the
    induction hypothesis applied to $Y$, $D_0$ and $\mathcal{A}_1$ gives
    $|\mathcal{A}_1| \le \sum_{k=0}^{D_0} \binom{|Y|}{k}$.

    Adding the two bounds and using $|X| = |Y| + 1$ together with
    \cref{lem:sum-choose-pascal} in the form
    $\sum_{k=0}^{D} \binom{|Y|+1}{k} = \sum_{k=0}^{D} \binom{|Y|}{k}
      + \sum_{k=0}^{D-1} \binom{|Y|}{k}$
    yields $|\mathcal{A}| \le \sum_{k=0}^{D} \binom{|X|}{k}$, as required. -/)
  (title := /-- The Sauer--Shelah lemma -/)
  (latexEnv := "lemma")]
lemma sauer_shelah {α : Type*} [DecidableEq α] :
    ∀ (X : Finset α) (D : ℕ) (𝒜 : Finset (Finset α)), (∀ S ∈ 𝒜, S ⊆ X) →
      (∀ T ⊆ X, T.card = D + 1 → ∃ T' ⊆ T, ∀ S ∈ 𝒜, S ∩ T ≠ T') →
      𝒜.card ≤ ∑ k ∈ Finset.range (D + 1), X.card.choose k := by
  intro X
  induction X using Finset.strongInduction with
  | _ X ih =>
    intro D 𝒜 hsub hshat
    rcases Finset.eq_empty_or_nonempty X with rfl | ⟨a, haX⟩
    · have hone : 𝒜.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro S hS S' hS'
        rw [Finset.subset_empty.mp (hsub S hS), Finset.subset_empty.mp (hsub S' hS')]
      refine hone.trans ?_
      calc (1 : ℕ) = (Nat.choose 0 0) := by simp
        _ ≤ ∑ k ∈ Finset.range (D + 1), (Finset.empty : Finset α).card.choose k := by
            refine Finset.single_le_sum (f := fun k => (Finset.empty : Finset α).card.choose k)
              (fun _ _ => Nat.zero_le _) ?_
            simp
    · match D with
      | 0 =>
          refine (card_le_one_of_no_shattered_point X 𝒜 hsub hshat).trans ?_
          calc (1 : ℕ) = X.card.choose 0 := by simp
            _ ≤ ∑ k ∈ Finset.range 1, X.card.choose k := by simp
      | (D₀ + 1) =>
        set Y : Finset α := X.erase a with hY
        have hYsub : Y ⊂ X := Finset.erase_ssubset haX
        have haY : a ∉ Y := Finset.notMem_erase a X
        have hXcard : X.card = Y.card + 1 := by
          rw [hY, Finset.card_erase_of_mem haX]
          exact (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr ⟨a, haX⟩)).symm
        classical
        set 𝒜₀ : Finset (Finset α) := 𝒜.image (fun S => S.erase a) with h𝒜₀
        set 𝒜₁ : Finset (Finset α) :=
          {S ∈ 𝒜 | a ∉ S ∧ insert a S ∈ 𝒜} with h𝒜₁
        have hsplit : 𝒜.card ≤ 𝒜₀.card + 𝒜₁.card := by
          have hcard : 𝒜.card
              = ∑ R ∈ 𝒜₀, {S ∈ 𝒜 | S.erase a = R}.card := by
            rw [h𝒜₀, Finset.card_eq_sum_card_fiberwise (f := fun S => S.erase a)]
            intro S hS
            exact Finset.mem_image_of_mem _ hS
          have hfib : ∀ R ∈ 𝒜₀, {S ∈ 𝒜 | S.erase a = R}.card
              ≤ 1 + (if R ∈ 𝒜₁ then 1 else 0) := by
            intro R hR
            by_cases hR1 : R ∈ 𝒜₁
            · have hsub2 : {S ∈ 𝒜 | S.erase a = R} ⊆ {R, insert a R} := by
                intro S hS
                rw [Finset.mem_filter] at hS
                have := hS.2
                by_cases haS : a ∈ S
                · have : insert a R = S := by
                    rw [← this, Finset.insert_erase haS]
                  simp [← this]
                · have : R = S := by
                    rw [← hS.2, Finset.erase_eq_of_notMem haS]
                  simp [this]
              refine (Finset.card_le_card hsub2).trans ?_
              simp only [hR1, if_pos]
              exact (Finset.card_insert_le _ _).trans (by simp)
            · have hsub2 : {S ∈ 𝒜 | S.erase a = R} ⊆ {R} ∨
                  {S ∈ 𝒜 | S.erase a = R} ⊆ {insert a R} := by
                by_cases haR : a ∈ R
                · right
                  intro S hS
                  rw [Finset.mem_filter] at hS
                  exact absurd (hS.2 ▸ Finset.notMem_erase a S) (by simp [haR])
                · rcases Classical.em (R ∈ 𝒜) with hRA | hRA
                  · left
                    intro S hS
                    rw [Finset.mem_filter] at hS
                    by_cases haS : a ∈ S
                    · exfalso
                      apply hR1
                      rw [h𝒜₁, Finset.mem_filter]
                      refine ⟨hRA, haR, ?_⟩
                      rw [← hS.2, Finset.insert_erase haS]
                      exact hS.1
                    · have : R = S := by
                        rw [← hS.2, Finset.erase_eq_of_notMem haS]
                      simp [this]
                  · right
                    intro S hS
                    rw [Finset.mem_filter] at hS
                    by_cases haS : a ∈ S
                    · have : insert a R = S := by
                        rw [← hS.2, Finset.insert_erase haS]
                      simp [← this]
                    · exfalso
                      apply hRA
                      have : R = S := by
                        rw [← hS.2, Finset.erase_eq_of_notMem haS]
                      rw [this]
                      exact hS.1
              rcases hsub2 with h | h
              · exact (Finset.card_le_card h).trans (by simp)
              · exact (Finset.card_le_card h).trans (by simp)
          calc 𝒜.card = ∑ R ∈ 𝒜₀, {S ∈ 𝒜 | S.erase a = R}.card := hcard
            _ ≤ ∑ R ∈ 𝒜₀, (1 + (if R ∈ 𝒜₁ then 1 else 0)) := Finset.sum_le_sum hfib
            _ = 𝒜₀.card + ∑ R ∈ 𝒜₀, (if R ∈ 𝒜₁ then 1 else 0) := by
                rw [Finset.sum_add_distrib]
                simp
            _ ≤ 𝒜₀.card + 𝒜₁.card := by
                have : ∑ R ∈ 𝒜₀, (if R ∈ 𝒜₁ then 1 else 0) ≤ 𝒜₁.card := by
                  rw [Finset.sum_ite_mem]
                  simpa using Finset.card_le_card
                    (Finset.inter_subset_right (s₁ := 𝒜₀) (s₂ := 𝒜₁))
                omega
        have h0sub : ∀ S ∈ 𝒜₀, S ⊆ Y := by
          intro S hS
          rw [h𝒜₀, Finset.mem_image] at hS
          obtain ⟨R, hR, rfl⟩ := hS
          intro x hx
          rw [hY, Finset.mem_erase]
          exact ⟨(Finset.mem_erase.mp hx).1, hsub R hR (Finset.mem_of_mem_erase hx)⟩
        have h0shat : ∀ T ⊆ Y, T.card = D₀ + 1 + 1 → ∃ T' ⊆ T, ∀ S ∈ 𝒜₀, S ∩ T ≠ T' := by
          intro T hT hTcard
          have hTX : T ⊆ X := hT.trans (Finset.erase_subset a X)
          obtain ⟨T', hT'sub, hT'⟩ := hshat T hTX hTcard
          refine ⟨T', hT'sub, ?_⟩
          intro S hS
          rw [h𝒜₀, Finset.mem_image] at hS
          obtain ⟨R, hR, rfl⟩ := hS
          have haT : a ∉ T := fun h => haY (hT h)
          have : R.erase a ∩ T = R ∩ T := by
            ext x
            simp only [Finset.mem_inter, Finset.mem_erase]
            constructor
            · rintro ⟨⟨_, hx⟩, hxT⟩; exact ⟨hx, hxT⟩
            · rintro ⟨hx, hxT⟩
              exact ⟨⟨fun h => haT (h ▸ hxT), hx⟩, hxT⟩
          rw [this]
          exact hT' R hR
        have h1sub : ∀ S ∈ 𝒜₁, S ⊆ Y := by
          intro S hS
          rw [h𝒜₁, Finset.mem_filter] at hS
          intro x hx
          rw [hY, Finset.mem_erase]
          exact ⟨fun h => hS.2.1 (h ▸ hx), hsub S hS.1 hx⟩
        have h1shat : ∀ T ⊆ Y, T.card = D₀ + 1 → ∃ T' ⊆ T, ∀ S ∈ 𝒜₁, S ∩ T ≠ T' := by
          intro T hT hTcard
          have haT : a ∉ T := fun h => haY (hT h)
          have hTaX : insert a T ⊆ X := by
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact haX
            · exact (hT.trans (Finset.erase_subset a X)) hx
          have hTacard : (insert a T).card = D₀ + 1 + 1 := by
            rw [Finset.card_insert_of_notMem haT, hTcard]
          obtain ⟨T', hT'sub, hT'⟩ := hshat (insert a T) hTaX hTacard
          refine ⟨T'.erase a, (Finset.erase_subset_erase a hT'sub).trans (by
            simp [Finset.erase_insert haT]), ?_⟩
          intro S hS hcontra
          rw [h𝒜₁, Finset.mem_filter] at hS
          obtain ⟨hSA, haS, hSaA⟩ := hS
          have hST : S ∩ insert a T = S ∩ T := by
            rw [Finset.inter_insert_of_notMem haS]
          have hSaT : (insert a S) ∩ (insert a T) = insert a (S ∩ T) := by
            rw [Finset.insert_inter_of_mem (Finset.mem_insert_self a T), Finset.inter_insert_of_notMem haS]
          by_cases haT' : a ∈ T'
          · refine hT' (insert a S) hSaA ?_
            rw [hSaT, hcontra, Finset.insert_erase haT']
          · refine hT' S hSA ?_
            rw [hST, hcontra, Finset.erase_eq_of_notMem haT']
        have hb0 := ih Y hYsub (D₀ + 1) 𝒜₀ h0sub h0shat
        have hb1 := ih Y hYsub D₀ 𝒜₁ h1sub h1shat
        calc 𝒜.card ≤ 𝒜₀.card + 𝒜₁.card := hsplit
          _ ≤ (∑ k ∈ Finset.range (D₀ + 1 + 1), Y.card.choose k)
                + ∑ k ∈ Finset.range (D₀ + 1), Y.card.choose k := Nat.add_le_add hb0 hb1
          _ = ∑ k ∈ Finset.range (D₀ + 1 + 1), (Y.card + 1).choose k :=
              (sum_choose_pascal Y.card (D₀ + 1)).symm
          _ = ∑ k ∈ Finset.range (D₀ + 1 + 1), X.card.choose k := by rw [hXcard]

@[blueprint "lem:exists-separating-functional"
  (statement := /-- Let $A$ and $B$ be finite subsets of $\Re^{d}$ whose convex hulls are
    disjoint, i.e. $CH(A) \cap CH(B) = \emptyset$. Then there exist a vector $v \in \Re^{d}$ and a
    real number $c$ such that
    \[ \langle v, x \rangle < c \quad (x \in A), \qquad
       c < \langle v, y \rangle \quad (y \in B) . \] -/)
  (proof := /-- We first dispose of the degenerate cases. If $A = \emptyset$, put $v = 0$ and
    $c = -1$: there is nothing to check on $A$, and $-1 < 0 = \langle 0, y \rangle$ for every
    $y \in B$. If $B = \emptyset$, put $v = 0$ and $c = 1$: then
    $\langle 0, x \rangle = 0 < 1$ for every $x \in A$, and there is nothing to check on $B$.

    Now suppose both $A$ and $B$ are nonempty. The set
    $K = CH(B) - CH(A) = \{ y - x : y \in CH(B),\ x \in CH(A) \}$ is convex, being the difference
    of two convex sets, and it is compact, being the image of the compact set
    $CH(B) \times CH(A)$ under the continuous map $(y,x) \mapsto y - x$; the hulls are compact
    because $A$ and $B$ are finite. Moreover $0 \notin K$: otherwise $y = x$ for some
    $x \in CH(A)$, $y \in CH(B)$, contradicting $CH(A) \cap CH(B) = \emptyset$. Since $K$ is
    nonempty, convex and complete (being compact), the Hilbert projection theorem provides
    $p \in K$ with $\|0 - p\| = \inf_{w \in K} \|0 - w\|$, and the variational characterisation of
    this nearest point gives $\langle 0 - p, w - p \rangle \le 0$ for all $w \in K$, i.e.
    \[ \langle p, w \rangle \ge \langle p, p \rangle = \|p\|^{2} \quad (w \in K) . \]
    As $0 \notin K$ we have $p \neq 0$, so $\|p\|^{2} > 0$.

    Set $v = p$ and
    \[ c = \max_{x \in A} \langle p, x \rangle + \tfrac{1}{2} \|p\|^{2} , \]
    the maximum being over the nonempty finite set $A$. For $x \in A$ we have
    $\langle p, x \rangle \le \max_{x' \in A} \langle p, x' \rangle
      < \max_{x' \in A} \langle p, x' \rangle + \tfrac12 \|p\|^{2} = c$ since $\|p\|^2 > 0$.
    For $y \in B$ and any $x \in A$ we have $y - x \in K$, hence
    $\langle p, y \rangle - \langle p, x \rangle = \langle p, y - x \rangle \ge \|p\|^{2}$, so
    $\langle p, y \rangle \ge \langle p, x \rangle + \|p\|^{2}$. Applying this with an
    $x \in A$ attaining the maximum gives
    $\langle p, y \rangle \ge \max_{x' \in A} \langle p, x' \rangle + \|p\|^{2} > c$, because
    $\|p\|^{2} > \tfrac12 \|p\|^{2}$. This is the required pair of strict inequalities. -/)
  (title := /-- Strict separation of disjoint convex hulls of finite sets -/)
  (latexEnv := "lemma")]
lemma exists_separating_functional {d : ℕ} (A B : Finset (EuclideanSpace ℝ (Fin d)))
    (hdisj : (convexHull ℝ (A : Set (EuclideanSpace ℝ (Fin d)))
      ∩ convexHull ℝ (B : Set (EuclideanSpace ℝ (Fin d)))) = ∅) :
    ∃ (v : EuclideanSpace ℝ (Fin d)) (c : ℝ),
      (∀ x ∈ A, inner ℝ v x < c) ∧ (∀ y ∈ B, c < inner ℝ v y) := by
  classical
  rcases A.eq_empty_or_nonempty with rfl | hA
  · exact ⟨0, -1, by simp, by intro y _; simpa using by norm_num⟩
  rcases B.eq_empty_or_nonempty with rfl | hB
  · exact ⟨0, 1, by intro x _; simpa using by norm_num, by simp⟩
  set hullA : Set (EuclideanSpace ℝ (Fin d)) :=
    convexHull ℝ (A : Set (EuclideanSpace ℝ (Fin d))) with hhullA
  set hullB : Set (EuclideanSpace ℝ (Fin d)) :=
    convexHull ℝ (B : Set (EuclideanSpace ℝ (Fin d))) with hhullB
  set K : Set (EuclideanSpace ℝ (Fin d)) :=
    (fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => q.1 - q.2)
      '' (hullB ×ˢ hullA) with hK
  have hKconv : Convex ℝ K := by
    rintro w₁ ⟨⟨y₁, x₁⟩, ⟨hy₁, hx₁⟩, rfl⟩ w₂ ⟨⟨y₂, x₂⟩, ⟨hy₂, hx₂⟩, rfl⟩ a b ha hb hab
    refine ⟨(a • y₁ + b • y₂, a • x₁ + b • x₂),
      ⟨(convex_convexHull ℝ _) hy₁ hy₂ ha hb hab, (convex_convexHull ℝ _) hx₁ hx₂ ha hb hab⟩, ?_⟩
    simp only [smul_sub]
    abel
  have hcompA : IsCompact hullA :=
    Set.Finite.isCompact_convexHull (𝕜 := ℝ) A.finite_toSet
  have hcompB : IsCompact hullB :=
    Set.Finite.isCompact_convexHull (𝕜 := ℝ) B.finite_toSet
  have hKcompact : IsCompact K :=
    (hcompB.prod hcompA).image (continuous_fst.sub continuous_snd)
  have hKne : K.Nonempty := by
    obtain ⟨y, hyB⟩ := hB
    obtain ⟨x, hxA⟩ := hA
    exact ⟨y - x, ⟨(y, x), ⟨subset_convexHull ℝ _ hyB, subset_convexHull ℝ _ hxA⟩, rfl⟩⟩
  have hzero : (0 : EuclideanSpace ℝ (Fin d)) ∉ K := by
    rintro ⟨⟨y, x⟩, ⟨hy, hx⟩, hyx⟩
    have hxy : x = y := (sub_eq_zero.mp hyx).symm
    rw [Set.eq_empty_iff_forall_notMem] at hdisj
    exact hdisj x ⟨hx, hxy ▸ hy⟩
  obtain ⟨p, hpK, hpmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hKne hKcompact.isComplete hKconv 0
  have hvar : ∀ w ∈ K, inner ℝ (0 - p) (w - p) ≤ (0 : ℝ) :=
    (norm_eq_iInf_iff_real_inner_le_zero hKconv hpK).mp hpmin
  have hpne : p ≠ 0 := fun h => hzero (h ▸ hpK)
  have hpsq : (0 : ℝ) < inner ℝ p p := real_inner_self_pos.mpr hpne
  have hlow : ∀ w ∈ K, inner ℝ p p ≤ inner ℝ p w := by
    intro w hw
    have := hvar w hw
    rw [zero_sub, inner_neg_left, inner_sub_right] at this
    linarith
  obtain ⟨x₀, hx₀A, hx₀max⟩ := A.exists_max_image (fun x => (inner ℝ p x : ℝ)) hA
  refine ⟨p, inner ℝ p x₀ + inner ℝ p p / 2, ?_, ?_⟩
  · intro x hxA
    have := hx₀max x hxA
    linarith
  · intro y hyB
    have hxy : y - x₀ ∈ K := by
      exact ⟨(y, x₀), ⟨subset_convexHull ℝ _ hyB, subset_convexHull ℝ _ hx₀A⟩, rfl⟩
    have := hlow _ hxy
    rw [inner_sub_right] at this
    linarith

@[blueprint "lem:halfspace-cut-card-bound"
  (statement := /-- Let $d \ge 0$, let $P \subseteq \Re^{d}$ be finite, and let $\mathcal{A}$ be a
    finite family of subsets of $P$ each of which is cut out by an open halfspace, i.e. for every
    $S \in \mathcal{A}$ there are $v \in \Re^{d}$ and $c \in \Re$ with
    $S = \{ p \in P : \langle v, p \rangle < c \}$. Then
    \[ |\mathcal{A}| \le \sum_{k=0}^{d+1} \binom{|P|}{k} . \] -/)
  (proof := /-- By \cref{lem:sauer-shelah} applied with $D = d+1$ it suffices to show that
    $\mathcal{A}$ shatters no subset $T \subseteq P$ with $|T| = d+2$.

    Fix such a $T$ and let $f : T \to \Re^{d}$ be the inclusion of $T$, so that $f$ is a family of
    $d+2$ vectors. The family $f$ is not affinely independent: an affinely independent family
    satisfies $|T| \le \dim \operatorname{vectorSpan}(f) + 1$, and
    $\dim \operatorname{vectorSpan}(f) \le \dim \Re^{d} = d$, whence $|T| \le d+1$, contradicting
    $|T| = d+2$. Therefore Radon's theorem yields a subset $I$ of $T$ with
    \[ CH(f(I)) \cap CH(f(I^{c})) \neq \emptyset . \]
    Let $T'$ be the finite subset of $T$ consisting of the points of $I$, so that
    $f(I) \subseteq T'$ and $f(I^{c}) \subseteq T \setminus T'$.

    We claim $T'$ witnesses the failure of shattering. Suppose $S \in \mathcal{A}$ satisfies
    $S \cap T = T'$, and write $S = \{ p \in P : \langle v, p \rangle < c \}$. Every point of
    $f(I)$ lies in $T' = S \cap T$, hence in $S$, hence satisfies $\langle v, \cdot \rangle < c$.
    The set $\{ y : \langle v, y \rangle < c \}$ is convex, because for $y_1, y_2$ in it and
    $a, b \ge 0$ with $a + b = 1$ we have
    $\langle v, a y_1 + b y_2 \rangle = a \langle v, y_1 \rangle + b \langle v, y_2 \rangle < c$,
    so $CH(f(I)) \subseteq \{ y : \langle v, y \rangle < c \}$. Every point of $f(I^{c})$ lies in
    $T$ but not in $T' = S \cap T$, hence not in $S$, hence satisfies
    $\langle v, \cdot \rangle \ge c$; the set $\{ y : c \le \langle v, y \rangle \}$ is convex by
    the same computation, so $CH(f(I^{c})) \subseteq \{ y : c \le \langle v, y \rangle \}$. A point
    in the intersection of the two hulls would then satisfy both $\langle v, z \rangle < c$ and
    $c \le \langle v, z \rangle$, which is impossible. This contradicts the nonemptiness supplied
    by Radon's theorem, so no $S \in \mathcal{A}$ has $S \cap T = T'$. -/)
  (title := /-- Halfspace cuts of a finite point set are few -/)
  (latexEnv := "lemma")]
lemma halfspace_cut_card_bound {d : ℕ} (P : Finset (EuclideanSpace ℝ (Fin d)))
    (𝒜 : Finset (Finset (EuclideanSpace ℝ (Fin d)))) (hsub : ∀ S ∈ 𝒜, S ⊆ P)
    (hcut : ∀ S ∈ 𝒜, ∃ (v : EuclideanSpace ℝ (Fin d)) (c : ℝ),
      ∀ p ∈ P, (p ∈ S ↔ inner ℝ v p < c)) :
    𝒜.card ≤ ∑ k ∈ Finset.range (d + 2), P.card.choose k := by
  classical
  refine sauer_shelah P (d + 1) 𝒜 hsub ?_
  intro T hTP hTcard
  have hnotai : ¬ AffineIndependent ℝ (fun x : {x // x ∈ T} => x.val) := by
    intro hai
    have hcard := hai.card_le_finrank_succ
    rw [Fintype.card_coe, hTcard] at hcard
    have hle : Module.finrank ℝ
        (vectorSpan ℝ (Set.range (fun x : {x // x ∈ T} => x.val)))
          ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) := Submodule.finrank_le _
    rw [finrank_euclideanSpace_fin] at hle
    omega
  obtain ⟨I, hI⟩ := Convex.radon_partition hnotai
  refine ⟨(T.attach.filter (fun x => x ∈ I)).image (fun x => x.val), ?_, ?_⟩
  · intro p hp
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and] at hp
    obtain ⟨x, _, rfl⟩ := hp
    exact x.2
  · intro S hSA hST
    obtain ⟨v, c, hvc⟩ := hcut S hSA
    have hIsub : (fun x : {x // x ∈ T} => x.val) '' I
        ⊆ {y : EuclideanSpace ℝ (Fin d) | inner ℝ v y < c} := by
      rintro y ⟨x, hxI, rfl⟩
      have hxT' : x.val ∈ (T.attach.filter (fun x => x ∈ I)).image (fun x => x.val) := by
        exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hxI⟩)
      rw [← hST, Finset.mem_inter] at hxT'
      exact (hvc _ (hsub S hSA hxT'.1)).mp hxT'.1
    have hIcsub : (fun x : {x // x ∈ T} => x.val) '' Iᶜ
        ⊆ {y : EuclideanSpace ℝ (Fin d) | c ≤ inner ℝ v y} := by
      rintro y ⟨x, hxI, rfl⟩
      have hxT' : x.val ∉ (T.attach.filter (fun x => x ∈ I)).image (fun x => x.val) := by
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and, not_exists]
        rintro x' ⟨hx'I, hx'eq⟩
        exact hxI (by rwa [show x = x' from Subtype.ext hx'eq.symm])
      rw [← hST] at hxT'
      have hxS : x.val ∉ S := by
        intro hxS
        exact hxT' (Finset.mem_inter.mpr ⟨hxS, x.2⟩)
      have := (hvc _ (hTP x.2)).not.mp hxS
      exact le_of_not_gt this
    have hlin : IsLinearMap ℝ (fun y : EuclideanSpace ℝ (Fin d) => (inner ℝ v y : ℝ)) :=
      ⟨fun y₁ y₂ => inner_add_right _ _ _, fun a y => real_inner_smul_right v y a⟩
    have hconvlt : Convex ℝ {y : EuclideanSpace ℝ (Fin d) | inner ℝ v y < c} :=
      convex_halfSpace_lt hlin c
    have hconvge : Convex ℝ {y : EuclideanSpace ℝ (Fin d) | c ≤ inner ℝ v y} :=
      convex_halfSpace_ge hlin c
    obtain ⟨z, hz₁, hz₂⟩ := hI
    have h₁ := convexHull_min hIsub hconvlt hz₁
    have h₂ := convexHull_min hIcsub hconvge hz₂
    simp only [Set.mem_setOf_eq] at h₁ h₂
    linarith

@[blueprint "lem:exists-cut-tuple-of-separated"
  (statement := /-- Let $d \ge 0$ and $s, t \ge 1$, let $P \subseteq \Re^{d}$ be finite and let
    $A \subseteq P$, and put $B = P \setminus A$. Assume there are an $s$-convex set $C$ and a
    $t$-convex set $D$, in the sense of \cref{def:is-union-of-convex}, with $A \subseteq C$,
    $B \subseteq D$ and $C \cap D = \emptyset$. Then there is a family
    $(f_{i,j})_{(i,j) \in \{1,\dots,s\} \times \{1,\dots,t\}}$ of subsets of $P$ such that each
    $f_{i,j}$ is cut out of $P$ by an open halfspace, i.e. there are $v \in \Re^{d}$ and
    $c \in \Re$ with $f_{i,j} = \{ p \in P : \langle v, p \rangle < c \}$, and such that
    \[ A = \{ p \in P : \exists i,\ \forall j,\ p \in f_{i,j} \} . \] -/)
  (proof := /-- Write $C = \bigcup_{i} K_i$ and $D = \bigcup_{j} L_j$ with all $K_i$ and $L_j$
    convex, as provided by \cref{def:is-union-of-convex}. Since $s \ge 1$ and $t \ge 1$ the index
    sets are nonempty, so we may fix base indices and define colourings
    $\alpha : \Re^{d} \to \{1,\dots,s\}$ and $\beta : \Re^{d} \to \{1,\dots,t\}$ such that
    $p \in K_{\alpha(p)}$ for every $p \in A$ and $p \in L_{\beta(p)}$ for every $p \in B$: for
    $p \in A$ we have $p \in C = \bigcup_i K_i$, so some $K_i$ contains $p$ and we let
    $\alpha(p)$ be such an index, and outside $A$ we let $\alpha$ take the base value; $\beta$ is
    defined symmetrically from $B \subseteq D$.

    Put $A_i = \{ p \in A : \alpha(p) = i \}$ and $B_j = \{ p \in B : \beta(p) = j \}$. By
    construction $A_i \subseteq K_i$ and $B_j \subseteq L_j$, and $K_i$, $L_j$ are convex, so
    $CH(A_i) \subseteq K_i$ and $CH(B_j) \subseteq L_j$. Since $K_i \subseteq C$ and
    $L_j \subseteq D$ and $C \cap D = \emptyset$, any point of $CH(A_i) \cap CH(B_j)$ would lie in
    $C \cap D$; hence $CH(A_i) \cap CH(B_j) = \emptyset$ for all $i$ and $j$.

    By \cref{lem:exists-separating-functional} there are, for each pair $(i,j)$, a vector
    $v_{i,j}$ and a real $c_{i,j}$ with $\langle v_{i,j}, x \rangle < c_{i,j}$ for all
    $x \in A_i$ and $c_{i,j} < \langle v_{i,j}, y \rangle$ for all $y \in B_j$. Define
    $f_{i,j} = \{ p \in P : \langle v_{i,j}, p \rangle < c_{i,j} \}$. Each $f_{i,j}$ is a subset of
    $P$ cut out by an open halfspace, as required.

    It remains to identify $A$. If $p \in A$ then $p \in P$, and taking $i = \alpha(p)$ we have
    $p \in A_i$, hence $\langle v_{i,j}, p \rangle < c_{i,j}$ and so $p \in f_{i,j}$ for every $j$;
    thus $p$ belongs to the right-hand side. Conversely, let $p \in P$ and let $i$ be an index with
    $p \in f_{i,j}$ for all $j$, and suppose $p \notin A$. Then $p \in B$, so with
    $j = \beta(p)$ we have $p \in B_j$ and therefore
    $c_{i,j} < \langle v_{i,j}, p \rangle$, while $p \in f_{i,j}$ gives
    $\langle v_{i,j}, p \rangle < c_{i,j}$, a contradiction. Hence $p \in A$, and the two sets
    coincide. -/)
  (title := /-- Encoding a separated partition by halfspace cuts -/)
  (latexEnv := "lemma")]
lemma exists_cut_tuple_of_separated {d s t : ℕ} (hs : 0 < s) (ht : 0 < t)
    (P A : Finset (EuclideanSpace ℝ (Fin d))) (hAP : A ⊆ P)
    (C D : Set (EuclideanSpace ℝ (Fin d)))
    (hC : is_union_of_convex d s C) (hD : is_union_of_convex d t D)
    (hAC : (A : Set (EuclideanSpace ℝ (Fin d))) ⊆ C)
    (hBD : ((P \ A : Finset (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d))) ⊆ D)
    (hCD : C ∩ D = ∅) :
    ∃ f : Fin s × Fin t → Finset (EuclideanSpace ℝ (Fin d)),
      (∀ ij, f ij ⊆ P) ∧
      (∀ ij, ∃ (v : EuclideanSpace ℝ (Fin d)) (c : ℝ), ∀ p ∈ P,
        (p ∈ f ij ↔ inner ℝ v p < c)) ∧
      A = P.filter (fun p => ∃ i : Fin s, ∀ j : Fin t, p ∈ f (i, j)) := by
  classical
  obtain ⟨K, hKconv, hCK⟩ := hC
  obtain ⟨L, hLconv, hDL⟩ := hD
  have hcolA_ex : ∀ p : EuclideanSpace ℝ (Fin d), ∃ i : Fin s, p ∈ A → p ∈ K i := by
    intro p
    by_cases hp : p ∈ A
    · have hpC : p ∈ C := hAC (by exact_mod_cast hp)
      rw [hCK, Set.mem_iUnion] at hpC
      obtain ⟨i, hi⟩ := hpC
      exact ⟨i, fun _ => hi⟩
    · exact ⟨⟨0, hs⟩, fun h => absurd h hp⟩
  have hcolB_ex : ∀ p : EuclideanSpace ℝ (Fin d), ∃ j : Fin t, p ∈ P \ A → p ∈ L j := by
    intro p
    by_cases hp : p ∈ P \ A
    · have hpD : p ∈ D := hBD (by exact_mod_cast hp)
      rw [hDL, Set.mem_iUnion] at hpD
      obtain ⟨j, hj⟩ := hpD
      exact ⟨j, fun _ => hj⟩
    · exact ⟨⟨0, ht⟩, fun h => absurd h hp⟩
  choose colA hcolA using hcolA_ex
  choose colB hcolB using hcolB_ex
  have hsep : ∀ ij : Fin s × Fin t, ∃ (v : EuclideanSpace ℝ (Fin d)) (c : ℝ),
      (∀ x ∈ A.filter (fun p => colA p = ij.1), inner ℝ v x < c) ∧
      (∀ y ∈ (P \ A).filter (fun p => colB p = ij.2), c < inner ℝ v y) := by
    intro ij
    refine exists_separating_functional _ _ ?_
    have h1 : convexHull ℝ ((A.filter (fun p => colA p = ij.1) :
        Finset (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d))) ⊆ K ij.1 := by
      refine convexHull_min ?_ (hKconv ij.1)
      intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
      exact hx.2 ▸ hcolA x hx.1
    have h2 : convexHull ℝ (((P \ A).filter (fun p => colB p = ij.2) :
        Finset (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d))) ⊆ L ij.2 := by
      refine convexHull_min ?_ (hLconv ij.2)
      intro y hy
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hy
      exact hy.2 ▸ hcolB y hy.1
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz1, hz2⟩
    have hzC : z ∈ C := by rw [hCK]; exact Set.mem_iUnion.2 ⟨ij.1, h1 hz1⟩
    have hzD : z ∈ D := by rw [hDL]; exact Set.mem_iUnion.2 ⟨ij.2, h2 hz2⟩
    rw [Set.eq_empty_iff_forall_notMem] at hCD
    exact hCD z ⟨hzC, hzD⟩
  choose v c hv1 hv2 using hsep
  refine ⟨fun ij => P.filter (fun p => inner ℝ (v ij) p < c ij),
    fun ij => Finset.filter_subset _ _,
    fun ij => ⟨v ij, c ij, fun p hp => by simp [Finset.mem_filter, hp]⟩, ?_⟩
  ext p
  simp only [Finset.mem_filter]
  constructor
  · intro hpA
    exact ⟨hAP hpA, colA p, fun j =>
      ⟨hAP hpA, hv1 (colA p, j) p (Finset.mem_filter.mpr ⟨hpA, rfl⟩)⟩⟩
  · rintro ⟨hpP, i, hi⟩
    by_contra hpA
    have hpB : p ∈ P \ A := Finset.mem_sdiff.mpr ⟨hpP, hpA⟩
    have hgt := hv2 (i, colB p) p (Finset.mem_filter.mpr ⟨hpB, rfl⟩)
    have hlt := (hi (colB p)).2
    linarith

@[blueprint "lem:radon-property-of-count"
  (statement := /-- Let $d \ge 0$, $s, t \ge 1$ and $n \ge 0$ be integers and suppose that
    \[ \left( \sum_{k=0}^{d+1} \binom{n}{k} \right)^{st} < 2^{n} . \]
    Then $n$ has the $(d,s,t)$-Radon partition property of
    \cref{def:has-radon-partition-property}. -/)
  (proof := /-- Let $P \subseteq \Re^{d}$ be a set of exactly $n$ points and suppose, for
    contradiction, that no partition of $P$ has the required property. For a subset $A \subseteq P$
    apply this to the partition $A \cup (P \setminus A)$, which is indeed a partition of $P$ into
    disjoint parts: the property must fail, so there are an $s$-convex $C \supseteq A$ and a
    $t$-convex $D \supseteq P \setminus A$ with $C \cap D$ empty. By
    \cref{lem:exists-cut-tuple-of-separated} we obtain a family $(f_{i,j})$ of subsets of $P$, each
    cut out of $P$ by an open halfspace, with
    $A = \{ p \in P : \exists i,\ \forall j,\ p \in f_{i,j} \}$.

    Let $\mathcal{C}$ be the family of all subsets of $P$ that are cut out of $P$ by some open
    halfspace. By \cref{lem:halfspace-cut-card-bound},
    $|\mathcal{C}| \le \sum_{k=0}^{d+1} \binom{n}{k}$. The previous paragraph assigns to every
    $A \subseteq P$ a tuple $g(A) = (f_{i,j}) \in \mathcal{C}^{\{1,\dots,s\} \times \{1,\dots,t\}}$,
    and the displayed identity recovers $A$ from $g(A)$; hence $g$ is injective on the family of
    subsets of $P$. Consequently
    \[ 2^{n} = |\{ A : A \subseteq P \}| \le |\mathcal{C}|^{st}
       \le \left( \sum_{k=0}^{d+1} \binom{n}{k} \right)^{st} < 2^{n} , \]
    where the last inequality is the hypothesis. This contradiction shows that some partition of
    $P$ has the required property, so $n$ has the $(d,s,t)$-Radon partition property. -/)
  (title := /-- A counting criterion for the Radon partition property -/)
  (latexEnv := "lemma")]
lemma radon_property_of_count {d s t n : ℕ} (hs : 0 < s) (ht : 0 < t)
    (hlt : (∑ k ∈ Finset.range (d + 2), n.choose k) ^ (s * t) < 2 ^ n) :
    has_radon_partition_property d s t n := by
  classical
  intro P hPcard
  by_contra hno
  have key : ∀ A : Finset (EuclideanSpace ℝ (Fin d)), A ⊆ P →
      ∃ f : Fin s × Fin t → Finset (EuclideanSpace ℝ (Fin d)),
        (∀ ij, f ij ⊆ P) ∧
        (∀ ij, ∃ (v : EuclideanSpace ℝ (Fin d)) (c : ℝ), ∀ p ∈ P,
          (p ∈ f ij ↔ inner ℝ v p < c)) ∧
        A = P.filter (fun p => ∃ i : Fin s, ∀ j : Fin t, p ∈ f (i, j)) := by
    intro A hAP
    have h1 : A ∪ (P \ A) = P := Finset.union_sdiff_of_subset hAP
    have h2 : Disjoint A (P \ A) := Finset.disjoint_sdiff
    have h3 : ¬ ∀ C D : Set (EuclideanSpace ℝ (Fin d)),
        is_union_of_convex d s C → is_union_of_convex d t D →
        (A : Set (EuclideanSpace ℝ (Fin d))) ⊆ C →
        ((P \ A : Finset (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d))) ⊆ D →
        (C ∩ D).Nonempty := fun h => hno ⟨A, P \ A, h1, h2, h⟩
    push Not at h3
    obtain ⟨C, D, hC, hD, hAC, hBD, hCD⟩ := h3
    exact exists_cut_tuple_of_separated hs ht P A hAP C D hC hD hAC hBD hCD
  set 𝒞 : Finset (Finset (EuclideanSpace ℝ (Fin d))) :=
    P.powerset.filter (fun S => ∃ (v : EuclideanSpace ℝ (Fin d)) (c : ℝ), ∀ p ∈ P,
      (p ∈ S ↔ inner ℝ v p < c)) with h𝒞
  have h𝒞card : 𝒞.card ≤ ∑ k ∈ Finset.range (d + 2), n.choose k := by
    have := halfspace_cut_card_bound P 𝒞
      (fun S hS => Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)
      (fun S hS => (Finset.mem_filter.mp hS).2)
    rwa [hPcard] at this
  have key' : ∀ A : Finset (EuclideanSpace ℝ (Fin d)),
      ∃ f : Fin s × Fin t → Finset (EuclideanSpace ℝ (Fin d)), A ⊆ P →
        ((∀ ij, f ij ∈ 𝒞) ∧
          A = P.filter (fun p => ∃ i : Fin s, ∀ j : Fin t, p ∈ f (i, j))) := by
    intro A
    by_cases hAP : A ⊆ P
    · obtain ⟨f, hf1, hf2, hf3⟩ := key A hAP
      refine ⟨f, fun _ => ⟨fun ij => ?_, hf3⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hf1 ij), hf2 ij⟩
    · exact ⟨fun _ => ∅, fun h => absurd h hAP⟩
  choose g hg using key'
  have hmaps : Set.MapsTo g (P.powerset : Set (Finset (EuclideanSpace ℝ (Fin d))))
      ((Fintype.piFinset (fun _ : Fin s × Fin t => 𝒞) :
        Finset (Fin s × Fin t → Finset (EuclideanSpace ℝ (Fin d)))) :
          Set (Fin s × Fin t → Finset (EuclideanSpace ℝ (Fin d)))) := by
    intro A hA
    have hAP : A ⊆ P := Finset.mem_powerset.mp (by exact_mod_cast hA)
    simp only [Finset.mem_coe, Fintype.mem_piFinset]
    exact (hg A hAP).1
  have hinj : Set.InjOn g (P.powerset : Set (Finset (EuclideanSpace ℝ (Fin d)))) := by
    intro A hA A' hA' heq
    have hAP : A ⊆ P := Finset.mem_powerset.mp (by exact_mod_cast hA)
    have hAP' : A' ⊆ P := Finset.mem_powerset.mp (by exact_mod_cast hA')
    rw [(hg A hAP).2, (hg A' hAP').2, heq]
  have hcard := Finset.card_le_card_of_injOn g hmaps hinj
  rw [Finset.card_powerset, hPcard, Fintype.card_piFinset, Finset.prod_const,
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hcard
  have hmono : 𝒞.card ^ (s * t) ≤ (∑ k ∈ Finset.range (d + 2), n.choose k) ^ (s * t) :=
    Nat.pow_le_pow_left h𝒞card _
  omega

@[blueprint "lem:exists-ceil-witness"
  (statement := /-- Write $\lambda = \log 2$ and
    $K_{0} = \frac{3}{\lambda} + \frac{2}{\lambda^{2}} \log \frac{2}{\lambda}
      + \frac{2}{\lambda}$. Let $D \ge 1$ and $u \ge 1$ be integers and put $L = \log(u+1)$.
    Then there exists an integer $N$ with $D \le N$,
    \[ D u \left( 1 + \log \frac{N}{D} \right) < N \lambda \]
    and
    \[ N \le 2 K_{0} \, D \, u \, L . \] -/)
  (proof := /-- Since $1 < 2$ we have $\lambda > 0$, and from $1 + 1 \le e^{1}$ we get
    $2 \le e$, hence $\lambda = \log 2 \le \log e = 1$. Since $u \ge 1$ we have $u + 1 \ge 2$, so
    $L = \log(u+1) \ge \log 2 = \lambda > 0$. Also $2/\lambda \ge 2 > 1$ because
    $\lambda \le 1$, so $\log(2/\lambda) \ge 0$.

    Put
    \[ A = 3 + \frac{2}{\lambda} \left( \log \frac{2}{\lambda} + L \right) , \]
    write $m = D u$ and let $N = \lceil A m \rceil$. All three summands of $A$ are nonnegative, so
    $A \ge 3$; since $m \ge 1$ this gives $A m \ge 3 \ge 1$, hence
    $N \ge A m \ge 3 m \ge 3 D \ge D$, and $N < A m + 1 \le 2 A m$.

    We first record the pointwise estimates. Since $m = D u$ we have $N / D \le 2 A m / D = 2 A u$,
    so monotonicity of the logarithm gives
    \[ \log \frac{N}{D} \le \log(2 A u) = \lambda + \log A + \log u , \]
    and $\log u \le L$ because $0 < u \le u+1$. Applying $\log x \le x - 1$ to
    $x = (\lambda/2) A > 0$ and using $\log(\lambda/2) = - \log(2/\lambda)$ gives
    \[ \log A \le \frac{\lambda}{2} A - 1 + \log \frac{2}{\lambda} . \]
    Combining the three displays,
    \[ 1 + \log \frac{N}{D} \le \lambda + \frac{\lambda}{2} A + \log \frac{2}{\lambda} + L . \]

    Next, by the definition of $A$,
    \[ \frac{\lambda}{2} A = \frac{3\lambda}{2} + \log \frac{2}{\lambda} + L , \]
    so that
    \[ A \lambda - \left( \lambda + \frac{\lambda}{2} A + \log \frac{2}{\lambda} + L \right)
       = \frac{\lambda}{2} A - \lambda - \log \frac{2}{\lambda} - L
       = \frac{3\lambda}{2} - \lambda = \frac{\lambda}{2} > 0 . \]
    Hence $\lambda + \frac{\lambda}{2} A + \log \frac{2}{\lambda} + L < A \lambda$. Multiplying by
    $m \ge 1 > 0$ and using the previous paragraph together with $A m \le N$ yields
    \[ m \left( 1 + \log \frac{N}{D} \right)
         \le m \left( \lambda + \frac{\lambda}{2} A + \log \frac{2}{\lambda} + L \right)
         < m A \lambda \le N \lambda , \]
    which is the first assertion since $m = D u$.

    For the second, we bound $A \le K_{0} L$. Indeed $3 = \frac{3}{\lambda} \lambda
      \le \frac{3}{\lambda} L$ since $\lambda \le L$; next, $\log(2/\lambda) \ge 0$ and
    $\lambda \le L$ give $\frac{2}{\lambda} \log \frac{2}{\lambda}
      \le \frac{2}{\lambda^{2}} \log \frac{2}{\lambda} \, L$; and the remaining summand is
    $\frac{2}{\lambda} L$ itself. Therefore $N \le 2 A m \le 2 K_{0} D u L$, as stated. -/)
  (title := /-- A logarithmic witness for the counting criterion -/)
  (latexEnv := "lemma")]
lemma exists_ceil_witness (D u : ℕ) (hD : 1 ≤ D) (hu : 1 ≤ u) :
    ∃ N : ℕ, D ≤ N ∧
      ((D : ℝ) * (u : ℝ)) * (1 + Real.log ((N : ℝ) / (D : ℝ))) < (N : ℝ) * Real.log 2 ∧
      (N : ℝ) ≤ 2 * (3 / Real.log 2 + 2 / Real.log 2 ^ 2 * Real.log (2 / Real.log 2)
        + 2 / Real.log 2) * (D : ℝ) * (u : ℝ) * Real.log ((u : ℝ) + 1) := by
  have hlam_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlam_le : Real.log 2 ≤ 1 := by
    have h2 : (2:ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1:ℝ)
      linarith
    calc Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) h2
      _ = 1 := Real.log_exp 1
  set lam := Real.log 2 with hlamdef
  have hDR : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hDpos : (0:ℝ) < (D:ℝ) := by linarith
  have huR : (1:ℝ) ≤ (u:ℝ) := by exact_mod_cast hu
  have hupos : (0:ℝ) < (u:ℝ) := by linarith
  set L := Real.log ((u:ℝ) + 1) with hLdef
  have hLlam : lam ≤ L := by
    rw [hLdef, hlamdef]
    exact Real.log_le_log (by norm_num) (by linarith)
  have hLpos : 0 < L := lt_of_lt_of_le hlam_pos hLlam
  have hu_pos : (0:ℝ) < 2 / lam := by positivity
  have hlogu_nonneg : 0 ≤ Real.log (2 / lam) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hlam_pos]
    linarith
  set A := 3 + (2 / lam) * (Real.log (2 / lam) + L) with hAdef
  have hApos : (3:ℝ) ≤ A := by
    have : 0 ≤ (2 / lam) * (Real.log (2 / lam) + L) := by positivity
    rw [hAdef]; linarith
  set m := (D:ℝ) * (u:ℝ) with hmdef
  have hmR : (1:ℝ) ≤ m := by rw [hmdef]; nlinarith
  have hmpos : (0:ℝ) < m := by linarith
  have hmD : (D:ℝ) ≤ m := by rw [hmdef]; nlinarith
  have hAmpos : (1:ℝ) ≤ A * m := by nlinarith
  set N := ⌈A * m⌉₊ with hNdef
  have hNge : A * m ≤ (N:ℝ) := Nat.le_ceil _
  have hNlt : (N:ℝ) < A * m + 1 := Nat.ceil_lt_add_one (by linarith)
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hN2 : (N:ℝ) ≤ 2 * (A * m) := by linarith
  have hND : (D:ℝ) ≤ (N:ℝ) := by nlinarith
  have hN1 : D ≤ N := by exact_mod_cast hND
  refine ⟨N, hN1, ?_, ?_⟩
  · have hNdiv : (N:ℝ) / (D:ℝ) ≤ 2 * (A * (u:ℝ)) := by
      rw [div_le_iff₀ hDpos]
      calc (N:ℝ) ≤ 2 * (A * m) := hN2
        _ = 2 * (A * (u:ℝ)) * (D:ℝ) := by rw [hmdef]; ring
    have hlogN : Real.log ((N:ℝ) / (D:ℝ)) ≤ lam + Real.log A + Real.log (u:ℝ) := by
      have h1 : Real.log ((N:ℝ) / (D:ℝ)) ≤ Real.log (2 * (A * (u:ℝ))) :=
        Real.log_le_log (by positivity) hNdiv
      have h2 : Real.log (2 * (A * (u:ℝ))) = lam + (Real.log A + Real.log (u:ℝ)) := by
        rw [Real.log_mul (by norm_num) (by positivity),
          Real.log_mul (by linarith) (by linarith), hlamdef]
      linarith [h1, h2.le, h2.ge]
    have hlogm : Real.log (u:ℝ) ≤ L := by
      rw [hLdef]
      exact Real.log_le_log hupos (by linarith)
    have hlogA : Real.log A ≤ (lam / 2) * A - 1 + Real.log (2 / lam) := by
      have hx : (0:ℝ) < (lam / 2) * A := by positivity
      have h1 : Real.log ((lam / 2) * A) ≤ (lam / 2) * A - 1 :=
        Real.log_le_sub_one_of_pos hx
      have h2 : Real.log ((lam / 2) * A) = Real.log (lam / 2) + Real.log A :=
        Real.log_mul (by positivity) (by linarith)
      have h3 : Real.log (lam / 2) = - Real.log (2 / lam) := by
        rw [← Real.log_inv]
        congr 1
        field_simp
      rw [h2, h3] at h1
      linarith
    have hAhalf : (lam / 2) * A = (3 * lam / 2) + Real.log (2 / lam) + L := by
      rw [hAdef]
      field_simp
      ring
    have hkey : lam + (lam / 2) * A + Real.log (2 / lam) + L < A * lam := by
      have hAlam : A * lam = (lam / 2) * A + (lam / 2) * A := by ring
      rw [hAlam, hAhalf]
      linarith
    have hstep : m * (1 + Real.log ((N:ℝ) / (D:ℝ)))
        ≤ m * (lam + (lam / 2) * A + Real.log (2 / lam) + L) := by
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hmpos)
      linarith
    calc ((D:ℝ) * (u:ℝ)) * (1 + Real.log ((N:ℝ) / (D:ℝ)))
        = m * (1 + Real.log ((N:ℝ) / (D:ℝ))) := by rw [hmdef]
      _ ≤ m * (lam + (lam / 2) * A + Real.log (2 / lam) + L) := hstep
      _ < m * (A * lam) := by
          exact mul_lt_mul_of_pos_left hkey hmpos
      _ = (A * m) * lam := by ring
      _ ≤ (N:ℝ) * lam := by
          exact mul_le_mul_of_nonneg_right hNge (le_of_lt hlam_pos)
  · have hAK : A ≤ (3 / lam + 2 / lam ^ 2 * Real.log (2 / lam) + 2 / lam) * L := by
      have h1 : (3:ℝ) ≤ 3 / lam * L := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hlam_pos]
        nlinarith
      have h2 : (2 / lam) * Real.log (2 / lam) ≤ 2 / lam ^ 2 * Real.log (2 / lam) * L := by
        have hfac : 2 / lam ^ 2 * Real.log (2 / lam) * L - (2 / lam) * Real.log (2 / lam)
            = (2 / lam ^ 2) * Real.log (2 / lam) * (L - lam) := by
          field_simp
        nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 2 / lam ^ 2) hlogu_nonneg)
          (by linarith : (0:ℝ) ≤ L - lam)]
      rw [hAdef]
      have hexp : (2 / lam) * (Real.log (2 / lam) + L)
          = (2 / lam) * Real.log (2 / lam) + (2 / lam) * L := by ring
      rw [hexp]
      nlinarith
    calc (N:ℝ) ≤ 2 * (A * m) := hN2
      _ ≤ 2 * (((3 / lam + 2 / lam ^ 2 * Real.log (2 / lam) + 2 / lam) * L) * m) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_right hAK (le_of_lt hmpos)
      _ = 2 * (3 / lam + 2 / lam ^ 2 * Real.log (2 / lam) + 2 / lam) * (D:ℝ) * (u:ℝ) * L := by
          rw [hmdef]; ring

@[blueprint "lem:count-of-log-bound"
  (statement := /-- Let $d \ge 0$ and $s, t \ge 1$ be integers, put $D = d+2$, and let $N$ be an
    integer with $D \le N$. Assume that
    \[ D \, s t \left( 1 + \log \frac{N}{D} \right) < N \log 2 . \]
    Then
    \[ \left( \sum_{k=0}^{d+1} \binom{N}{k} \right)^{st} < 2^{N} . \] -/)
  (proof := /-- All quantities are compared after casting to the reals; since both sides are
    positive integers, it suffices to prove the inequality of their real images.

    First we claim $\sum_{k=0}^{d+1} \binom{N}{k} \le (e N / D)^{D}$. Since the omitted term
    $\binom{N}{D}$ is nonnegative, the left-hand side is at most $\sum_{k=0}^{D} \binom{N}{k}$, and
    \cref{lem:sum-choose-le-pow-exp} applied with the pair $(N, D)$, which is legitimate because
    $1 \le D \le N$, bounds this by $(N/D)^{D} e^{D}$. Finally
    $(N/D)^{D} e^{D} = (e N / D)^{D}$ because $e^{D} = (e^{1})^{D}$ and powers multiply.

    Since $D \le N$ we have $N/D \ge 1$, so $e N / D > 0$ and
    \[ \log \frac{e N}{D} = 1 + \log \frac{N}{D} . \]
    Raising the first display to the power $st$ therefore gives
    \[ \left( \sum_{k=0}^{d+1} \binom{N}{k} \right)^{st}
       \le \left( \frac{eN}{D} \right)^{D \, st}
       = \exp\!\left( D \, st \left( 1 + \log \frac{N}{D} \right) \right) , \]
    using $x^{k} = \exp(k \log x)$ for $x > 0$. On the other hand $2^{N} = \exp(N \log 2)$. As
    $\exp$ is strictly monotone and $D \, st (1 + \log(N/D)) < N \log 2$ by hypothesis, we conclude
    $\left( \sum_{k=0}^{d+1} \binom{N}{k} \right)^{st} < 2^{N}$. -/)
  (title := /-- The logarithmic inequality implies the counting inequality -/)
  (latexEnv := "lemma")]
lemma count_of_log_bound {d s t N : ℕ} (hN : d + 2 ≤ N)
    (hkey : (((d : ℝ) + 2) * ((s : ℝ) * (t : ℝ)))
      * (1 + Real.log ((N : ℝ) / ((d : ℝ) + 2))) < (N : ℝ) * Real.log 2) :
    (∑ k ∈ Finset.range (d + 2), N.choose k) ^ (s * t) < 2 ^ N := by
  have hDpos : (0:ℝ) < (d:ℝ) + 2 := by positivity
  have hNR : ((d:ℝ) + 2) ≤ (N:ℝ) := by
    have : ((d + 2 : ℕ) : ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    push_cast at this
    linarith
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  set W : ℝ := Real.exp 1 * (N:ℝ) / ((d:ℝ) + 2) with hWdef
  have hWpos : (0:ℝ) < W := by rw [hWdef]; positivity
  have hsum_le : (∑ k ∈ Finset.range (d + 2), N.choose k : ℝ) ≤ W ^ (d + 2) := by
    have hbase := sum_choose_le_pow_exp N (d + 2) (by omega) hN
    have hext : (∑ k ∈ Finset.range (d + 2), (N.choose k : ℝ))
        ≤ ∑ k ∈ Finset.range (d + 2 + 1), (N.choose k : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) ?_
      intro k _ _
      exact Nat.cast_nonneg _
    have hcast : ((d + 2 : ℕ) : ℝ) = (d:ℝ) + 2 := by push_cast; ring
    rw [hcast] at hbase
    have hWpow : ((N:ℝ) / ((d:ℝ) + 2)) ^ (d + 2) * Real.exp ((d:ℝ) + 2) = W ^ (d + 2) := by
      have hexp : Real.exp ((d:ℝ) + 2) = Real.exp 1 ^ (d + 2) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [hexp, hWdef, show Real.exp 1 * (N:ℝ) / ((d:ℝ) + 2)
        = ((N:ℝ) / ((d:ℝ) + 2)) * Real.exp 1 from by ring, mul_pow]
    rw [hWpow] at hbase
    push_cast at hext ⊢
    linarith
  have hpowexp : W ^ ((d + 2) * (s * t))
      = Real.exp ((((d:ℝ) + 2) * ((s:ℝ) * (t:ℝ)))
        * (1 + Real.log ((N:ℝ) / ((d:ℝ) + 2)))) := by
    have hlog : Real.log W = 1 + Real.log ((N:ℝ) / ((d:ℝ) + 2)) := by
      rw [hWdef, show Real.exp 1 * (N:ℝ) / ((d:ℝ) + 2)
        = Real.exp 1 * ((N:ℝ) / ((d:ℝ) + 2)) from by ring,
        Real.log_mul (by positivity) (by positivity), Real.log_exp]
    rw [← Real.exp_log hWpos, ← Real.exp_nat_mul, hlog]
    congr 1
    push_cast
    ring
  have hlhs : ((∑ k ∈ Finset.range (d + 2), N.choose k : ℕ) : ℝ) ^ (s * t)
      ≤ Real.exp ((((d:ℝ) + 2) * ((s:ℝ) * (t:ℝ)))
        * (1 + Real.log ((N:ℝ) / ((d:ℝ) + 2)))) := by
    have hnn : (0:ℝ) ≤ (∑ k ∈ Finset.range (d + 2), N.choose k : ℕ) := by positivity
    have hstep : ((∑ k ∈ Finset.range (d + 2), N.choose k : ℕ) : ℝ) ^ (s * t)
        ≤ (W ^ (d + 2)) ^ (s * t) := by
      refine pow_le_pow_left₀ hnn ?_ _
      push_cast at hsum_le ⊢
      exact hsum_le
    rw [← pow_mul] at hstep
    rw [hpowexp] at hstep
    exact hstep
  have hrhs : ((2:ℝ) ^ N) = Real.exp ((N:ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hfinal : ((∑ k ∈ Finset.range (d + 2), N.choose k : ℕ) : ℝ) ^ (s * t) < (2:ℝ) ^ N := by
    rw [hrhs]
    exact lt_of_le_of_lt hlhs (Real.exp_lt_exp.mpr hkey)
  have hcastfinal :
      (((∑ k ∈ Finset.range (d + 2), N.choose k) ^ (s * t) : ℕ) : ℝ) < ((2 ^ N : ℕ) : ℝ) := by
    push_cast
    push_cast at hfinal
    exact hfinal
  exact_mod_cast hcastfinal

@[blueprint "lem:radon-property-bound"
  (statement := /-- There exists a real constant $C > 0$ such that for all integers
    $d, s, t \ge 1$ there is a nonnegative integer $n$ with
    \[ n \le C \, d \, s \, t \log(st+1), \]
    where $\log$ denotes the natural logarithm, such that $n$ has the $(d,s,t)$-Radon
    partition property of \cref{def:has-radon-partition-property}. The constant $C$ is
    chosen before $d$, $s$ and $t$, so it depends on none of them. -/)
  (proof := /-- Write $\lambda = \log 2$,
    \[ K_{0} = \frac{3}{\lambda} + \frac{2}{\lambda^{2}} \log \frac{2}{\lambda}
         + \frac{2}{\lambda} , \qquad C = 6 K_{0} . \]
    Since $\lambda > 0$ and, because $\lambda \le 1$, also $2/\lambda \ge 2 > 1$ and hence
    $\log(2/\lambda) \ge 0$, every summand of $K_{0}$ is nonnegative and the first is positive;
    thus $K_{0} > 0$ and $C > 0$. The constant $C$ involves only $\lambda$, so it depends on none
    of $d$, $s$, $t$.

    Fix integers $d, s, t \ge 1$ and put $D = d + 2$ and $u = st$, so $D \ge 1$ and $u \ge 1$. By
    \cref{lem:exists-ceil-witness} applied to $D$ and $u$ there is an integer $N$ with
    $D \le N$,
    \[ D u \left( 1 + \log \frac{N}{D} \right) < N \lambda \]
    and
    \[ N \le 2 K_{0} \, D \, u \log(u+1) . \]
    We take $n = N$.

    The displayed strict inequality is exactly the hypothesis of
    \cref{lem:count-of-log-bound}, which therefore gives
    \[ \left( \sum_{k=0}^{d+1} \binom{N}{k} \right)^{st} < 2^{N} , \]
    and \cref{lem:radon-property-of-count} then shows that $N$ has the $(d,s,t)$-Radon partition
    property of \cref{def:has-radon-partition-property}. This is the second assertion.

    For the size bound, note that $d \ge 1$ gives $D = d + 2 \le 3 d$, so
    \[ N \le 2 K_{0} D u \log(u+1) \le 2 K_{0} \cdot 3 d \cdot s t \cdot \log(st+1)
       = C \, d \, s \, t \log(st+1) , \]
    where we used $u = st$, that $\log(st+1) \ge \log 2 > 0$ is nonnegative, and $K_{0} > 0$.
    This is the required inequality $n \le C \, d \, s \, t \log(st+1)$. -/)
  (title := /-- Existence of a partition witness of size $O(dst\log(st+1))$ -/)
  (latexEnv := "lemma")]
lemma radon_property_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ d s t : ℕ, 1 ≤ d → 1 ≤ s → 1 ≤ t →
      ∃ n : ℕ, (n : ℝ) ≤ C * (d : ℝ) * (s : ℝ) * (t : ℝ) * Real.log ((s : ℝ) * (t : ℝ) + 1) ∧
        has_radon_partition_property d s t n := by
  have hlam_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlam_le : Real.log 2 ≤ 1 := by
    have h2 : (2:ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1:ℝ)
      linarith
    calc Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) h2
      _ = 1 := Real.log_exp 1
  set lam := Real.log 2 with hlamdef
  have hlogu_nonneg : 0 ≤ Real.log (2 / lam) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hlam_pos]
    linarith
  set K₀ := 3 / lam + 2 / lam ^ 2 * Real.log (2 / lam) + 2 / lam with hK₀def
  have hK₀pos : 0 < K₀ := by
    have h1 : (0:ℝ) < 3 / lam := by positivity
    have h2 : (0:ℝ) ≤ 2 / lam ^ 2 * Real.log (2 / lam) := by positivity
    have h3 : (0:ℝ) < 2 / lam := by positivity
    rw [hK₀def]; linarith
  refine ⟨6 * K₀, by linarith, ?_⟩
  intro d s t hd hs ht
  obtain ⟨N, hND, hNlog, hNsize⟩ := exists_ceil_witness (d + 2) (s * t) (by omega) (by
    exact Nat.one_le_iff_ne_zero.mpr (by positivity))
  have hcastD : ((d + 2 : ℕ) : ℝ) = (d:ℝ) + 2 := by push_cast; ring
  have hcastu : ((s * t : ℕ) : ℝ) = (s:ℝ) * (t:ℝ) := by push_cast; ring
  rw [hcastD, hcastu] at hNlog hNsize
  refine ⟨N, ?_, ?_⟩
  · have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    have hsR : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
    have htR : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
    have hLpos : 0 < Real.log ((s:ℝ) * (t:ℝ) + 1) := by
      refine Real.log_pos ?_
      nlinarith
    have hD3 : (d:ℝ) + 2 ≤ 3 * (d:ℝ) := by linarith
    calc (N:ℝ)
        ≤ 2 * K₀ * ((d:ℝ) + 2) * ((s:ℝ) * (t:ℝ)) * Real.log ((s:ℝ) * (t:ℝ) + 1) := hNsize
      _ ≤ 2 * K₀ * (3 * (d:ℝ)) * ((s:ℝ) * (t:ℝ)) * Real.log ((s:ℝ) * (t:ℝ) + 1) := by
          have hfac : (0:ℝ) ≤ 2 * K₀ := by linarith
          have hrest : (0:ℝ) ≤ ((s:ℝ) * (t:ℝ)) * Real.log ((s:ℝ) * (t:ℝ) + 1) := by
            have : (0:ℝ) ≤ (s:ℝ) * (t:ℝ) := by positivity
            exact mul_nonneg this (le_of_lt hLpos)
          nlinarith
      _ = 6 * K₀ * (d:ℝ) * (s:ℝ) * (t:ℝ) * Real.log ((s:ℝ) * (t:ℝ) + 1) := by ring
  · refine radon_property_of_count hs ht ?_
    refine count_of_log_bound hND ?_
    exact hNlog

@[blueprint "thm:main"
  (statement := /-- $f(d,s,t) = O(dst \log(st+1))$. Explicitly, there exists a real
    constant $C > 0$, independent of $d$, $s$ and $t$, such that for all integers
    $d, s, t \ge 1$ the Radon number of \cref{def:radon-number} satisfies
    \[ f(d,s,t) \le C \, d \, s \, t \log(st+1), \]
    where $\log$ denotes the natural logarithm. -/)
  (proof := /-- Let $C > 0$ be the constant provided by \cref{lem:radon-property-bound},
    which depends on none of $d$, $s$, $t$. Fix integers $d, s, t \ge 1$. By
    \cref{lem:radon-property-bound} there is an integer $n$ with
    $n \le C \, d \, s \, t \log(st+1)$ which has the $(d,s,t)$-Radon partition property.
    Applying \cref{lem:radon-number-le-of-property} to this $n$ gives
    $f(d,s,t) \le n$. Combining the two inequalities yields
    $f(d,s,t) \le n \le C \, d \, s \, t \log(st+1)$, which is the assertion with the same
    constant $C$. -/)
  (title := /-- The Radon number for unions of convex sets is $O(dst\log(st+1))$ -/)
  (latexEnv := "theorem")]
theorem main :
    ∃ C : ℝ, 0 < C ∧ ∀ d s t : ℕ, 1 ≤ d → 1 ≤ s → 1 ≤ t →
      (radon_number d s t : ℝ) ≤
        C * (d : ℝ) * (s : ℝ) * (t : ℝ) * Real.log ((s : ℝ) * (t : ℝ) + 1) := by
  obtain ⟨C, hCpos, hC⟩ := radon_property_bound
  refine ⟨C, hCpos, ?_⟩
  intro d s t hd hs ht
  obtain ⟨n, hn, hprop⟩ := hC d s t hd hs ht
  have hle : (radon_number d s t : ℝ) ≤ (n : ℝ) :=
    Nat.cast_le.mpr (radon_number_le_of_property d s t n hprop)
  exact le_trans hle hn

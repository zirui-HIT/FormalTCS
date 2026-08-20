import Architect
import Mathlib

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:empirical-noise-rate"
  (statement := /-- Let $U$ be a universe of strings, $L \subseteq U$ a language, and
  $x = (x_t)_{t \in \mathbb{N}}$ a stream of elements of $U$. For $n \in \mathbb{N}$, the
  \emph{empirical noise rate} of $L$ on the prefix $x_{1:n}$ is
  $R(L; x_{1:n}) = \frac{1}{n}\,\bigl\lvert \{\, t < n : x_t \notin L \,\} \bigr\rvert$,
  the fraction of the first $n$ revealed elements that fall outside $L$. -/)
  (title := /-- Empirical Noise Rate -/)
  (latexEnv := "definition")]
noncomputable def empirical_noise_rate {U : Type*} (L : Set U) (x : ℕ → U) (n : ℕ) : ℝ :=
  (Set.ncard {t : ℕ | t < n ∧ x t ∉ L} : ℝ) / (n : ℝ)

@[blueprint "def:generation-in-the-limit"
  (statement := /-- Let $U$ be a universe, $G : (\mathbb{N} \to U) \to \mathbb{N} \to U$ an
  element-based generator (writing $w_n = G(x)(n)$ for its output at round $n$ on the stream
  $x = (x_t)_{t \in \mathbb{N}}$), and $K \subseteq U$ a target language. We say that $G$
  \emph{generates $K$ in the limit on $x$} if there exists a finite time $n^\star \in \mathbb{N}$
  such that for every $n \geq n^\star$ the output is consistent with $K$, i.e. $w_n \in K$. -/)
  (title := /-- Language Generation in the Limit -/)
  (latexEnv := "definition")]
def generation_in_the_limit {U : Type*} (G : (ℕ → U) → ℕ → U) (K : Set U) (x : ℕ → U) : Prop :=
  ∃ nStar : ℕ, ∀ n : ℕ, nStar ≤ n → G x n ∈ K

@[blueprint "def:element-based"
  (statement := /-- Let $U$ be a universe. A generator
  $G : (\mathbb{N} \to U) \to \mathbb{N} \to U$ is \emph{element-based} if, on every stream
  $x = (x_t)_{t \in \mathbb{N}}$ and at every round $n \in \mathbb{N}$, its output
  $w_n = G(x)(n)$ is novel: it avoids both the revealed prefix and the earlier outputs, i.e.
  $w_n \notin \{x_0, \dots, x_n\} \cup \{w_0, \dots, w_{n-1}\}$. -/)
  (title := /-- Element-based Generator -/)
  (latexEnv := "definition")]
def element_based {U : Type*} (G : (ℕ → U) → ℕ → U) : Prop :=
  ∀ (x : ℕ → U) (n : ℕ), G x n ∉ (x '' Set.Iic n ∪ (fun m => G x m) '' Set.Iio n)

@[blueprint "def:enumeration-o1-noise-omission"
  (statement := /-- Let $U$ be a universe and $K \subseteq U$ a language. A stream
  $x = (x_t)_{t \in \mathbb{N}}$ is an \emph{$o(1)$-noise enumeration of $K$ with arbitrary
  omissions} if there exists a subset $\hat{K} \subseteq K$ with $\lvert \hat{K} \rvert = \infty$
  such that every element $a \in \hat{K}$ occurs exactly once in the stream (there is a unique
  $t$ with $x_t = a$) and the empirical noise rate of $\hat{K}$ vanishes, i.e.
  $R(\hat{K}; x_{1:n}) \to 0$ as $n \to \infty$ (see \cref{def:empirical-noise-rate}). -/)
  (title := /-- Enumeration with $o(1)$-Noise and Arbitrary Omissions -/)
  (latexEnv := "definition")]
def enumeration_o1_noise_omission {U : Type*} (x : ℕ → U) (K : Set U) : Prop :=
  ∃ Khat : Set U, Khat ⊆ K ∧ Khat.Infinite ∧
    (∀ a ∈ Khat, ∃! t : ℕ, x t = a) ∧
    Filter.Tendsto (fun n => empirical_noise_rate Khat x n) Filter.atTop (nhds (0 : ℝ))

@[blueprint "def:collection-closure"
  (statement := /-- Let $U$ be a universe and $\mathcal{L} = (L_i)_{i \in \mathbb{N}}$ a countable
  collection of languages over $U$. For a set of indices $S \subseteq \mathbb{N}$, the
  \emph{closure} $\mathrm{Cl}(S)$ is the intersection $\bigcap_{i \in S} L_i$ of the languages
  whose indices lie in $S$. -/)
  (title := /-- Closure of a Subcollection -/)
  (latexEnv := "definition")]
def collection_closure {U : Type*} (L : ℕ → Set U) (S : Set ℕ) : Set U :=
  ⋂ i ∈ S, L i

@[blueprint "def:threshold"
  (statement := /-- The \emph{threshold sequence} is defined by
  $c_i = \dfrac{1}{2^{\,i+1}}$ for $i \in \mathbb{N}$. -/)
  (title := /-- Threshold Sequence -/)
  (latexEnv := "definition")]
noncomputable def threshold (i : ℕ) : ℝ := 1 / 2 ^ (i + 1)

@[blueprint "lem:meta-algorithm-prefix-stabilizes"
  (statement := /-- Let $P : \mathbb{N} \times \mathbb{N} \to \mathbb{N} \cup \{\infty\}$ assign to
  each language index $i$ and round $n$ a priority $P_i^{(n)}$. Assume that for all $i, n$ the
  priorities are non-decreasing in $n$, i.e. $P_i^{(n)} \leq P_i^{(n+1)}$, and lower bounded by the
  index, i.e. $i \leq P_i^{(n)}$. For $p \in \mathbb{N}$ set $P_i^{\infty} = \sup_n P_i^{(n)}$ and
  $\mathcal{L}(p) = \{\, i : P_i^{\infty} \leq p \,\}$. Then there exists $n^\star \in \mathbb{N}$
  such that for all $n \geq n^\star$: (a) $P_i^{(n)} \leq p$ for all $i \in \mathcal{L}(p)$;
  (b) $P_i^{(n)} > p$ for all $i \notin \mathcal{L}(p)$; and
  (c) $P_i^{(n+1)} = P_i^{(n)}$ for all $i \in \mathcal{L}(p)$. -/)
  (proof := /-- Since $P_i^{(n)}$ is non-decreasing in $n$ and lower bounded by $i$, we have
  $P_i^{\infty} \geq P_i^{(n)} \geq i$ whenever $n \geq i$; hence
  $\mathcal{L}(p) \subseteq \{1, \dots, p\}$ and $P_i^{(n)} > p$ for all $n \geq i > p$. For each of
  the finitely many indices $i \leq p$, the sequence $(P_i^{(n)})_n$ is monotone with limit
  $P_i^{\infty}$, so either $P_i^{(n)} = P_i^{\infty} \leq p$ for all sufficiently large $n$, or
  $P_i^{(n)} > p$ for all sufficiently large $n$. Choosing $n^\star$ to be the maximum of the
  finitely many rounds past which each of these finitely many alternatives becomes settled yields
  claims (a), (b), and (c) simultaneously. -/)
  (title := /-- Prefix Priority Stabilization -/)
  (latexEnv := "lemma")]
lemma meta_algorithm_prefix_stabilizes
    (P : ℕ → ℕ → ℕ∞)
    (hmono : ∀ i n, P i n ≤ P i (n + 1))
    (hlb : ∀ (i : ℕ) (n : ℕ), (i : ℕ∞) ≤ P i n)
    (p : ℕ) :
    ∃ nStar : ℕ, ∀ n : ℕ, nStar ≤ n →
      (∀ i : ℕ, (⨆ m, P i m) ≤ (p : ℕ∞) → P i n ≤ (p : ℕ∞)) ∧
      (∀ i : ℕ, ¬ ((⨆ m, P i m) ≤ (p : ℕ∞)) → (p : ℕ∞) < P i n) ∧
      (∀ i : ℕ, (⨆ m, P i m) ≤ (p : ℕ∞) → P i (n + 1) = P i n) := by
  have hmono' : ∀ i, Monotone (P i) := fun i => monotone_nat_of_le_succ (hmono i)
  have key : ∀ i : ℕ, ∃ mi : ℕ, ∀ n : ℕ, mi ≤ n →
      (((⨆ m, P i m) ≤ (p : ℕ∞)) → P i (n + 1) = P i n) ∧
      (¬ ((⨆ m, P i m) ≤ (p : ℕ∞)) → (p : ℕ∞) < P i n) := by
    intro i
    by_cases hle : (⨆ m, P i m) ≤ (p : ℕ∞)
    · have hbound : ∀ n, P i n ≤ (p : ℕ∞) := fun n => (le_iSup (P i) n).trans hle
      have hfin : ∀ n, P i n ≠ ⊤ := fun n => ne_top_of_le_ne_top (ENat.coe_ne_top p) (hbound n)
      have hmono_h : Monotone (fun n => (P i n).toNat) := by
        intro a b hab
        exact ENat.toNat_le_toNat (hmono' i hab) (hfin b)
      have hbdd : BddAbove (Set.range (fun n => (P i n).toNat)) := by
        refine ⟨p, ?_⟩
        rintro _ ⟨n, rfl⟩
        exact ENat.toNat_le_of_le_coe (hbound n)
      obtain ⟨m0, hm0⟩ :=
        Nat.sSup_mem (⟨(P i 0).toNat, 0, rfl⟩ :
          (Set.range (fun n => (P i n).toNat)).Nonempty) hbdd
      refine ⟨m0, fun n hn => ⟨fun _ => ?_, fun hcon => absurd hle hcon⟩⟩
      have hconst : ∀ k, m0 ≤ k →
          (P i k).toNat = sSup (Set.range (fun n => (P i n).toNat)) := by
        intro k hk
        refine le_antisymm (le_csSup hbdd ⟨k, rfl⟩) ?_
        calc sSup (Set.range (fun n => (P i n).toNat)) = (P i m0).toNat := hm0.symm
          _ ≤ (P i k).toNat := hmono_h hk
      have e1 : (P i (n + 1)).toNat = (P i n).toNat := by
        rw [hconst (n + 1) (le_trans hn (Nat.le_succ n)), hconst n hn]
      have h1 : ((P i n).toNat : ℕ∞) = P i n := ENat.coe_toNat (hfin n)
      have h2 : ((P i (n + 1)).toNat : ℕ∞) = P i (n + 1) := ENat.coe_toNat (hfin (n + 1))
      rw [← h1, ← h2, e1]
    · obtain ⟨m0, hm0⟩ := lt_iSup_iff.mp (not_le.mp hle)
      refine ⟨m0, fun n hn => ⟨fun hcon => absurd hcon hle, fun _ => ?_⟩⟩
      exact lt_of_lt_of_le hm0 (hmono' i hn)
  choose f hf using key
  refine ⟨(Finset.range (p + 1)).sup f, fun n hn => ⟨?_, ?_, ?_⟩⟩
  · intro i hisup
    exact (le_iSup (P i) n).trans hisup
  · intro i hisup
    by_cases hip : i ≤ p
    · have hfi : f i ≤ n :=
        le_trans (Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hip))) hn
      exact (hf i n hfi).2 hisup
    · have hip' : p < i := Nat.lt_of_not_le hip
      exact lt_of_lt_of_le (by exact_mod_cast hip') (hlb i n)
  · intro i hisup
    have hip : i ≤ p := by
      have hcast : (i : ℕ∞) ≤ (p : ℕ∞) := (hlb i 0).trans ((le_iSup (P i) 0).trans hisup)
      exact_mod_cast hcast
    have hfi : f i ≤ n :=
      le_trans (Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hip))) hn
    exact (hf i n hfi).1 hisup

@[blueprint "lem:threshold-sum-le-half"
  (statement := /-- For the threshold sequence of \cref{def:threshold},
  $\sum_{i=1}^{\infty} c_i = \sum_{i=1}^{\infty} \frac{1}{2^{\,i+1}} = \frac{1}{2}$. -/)
  (proof := /-- By \cref{def:threshold}, $\sum_{i=1}^{\infty} c_i = \sum_{i=1}^{\infty} 2^{-(i+1)}
  = \frac{1}{4} \sum_{i=0}^{\infty} 2^{-i}$. The geometric series $\sum_{i=0}^{\infty} 2^{-i}$
  converges to $\frac{1}{1 - 1/2} = 2$, so $\sum_{i=1}^{\infty} c_i = \frac{1}{4} \cdot 2
  = \frac{1}{2}$. -/)
  (title := /-- Summability of the Threshold Sequence -/)
  (latexEnv := "lemma")]
lemma threshold_sum_le_half :
    ∑' i : ℕ, threshold (i + 1) = 1 / 2 := by
  have h : ∀ n : ℕ, threshold (n + 1) = (1 / 2 : ℝ) / 2 / 2 ^ n := by
    intro n
    unfold threshold
    rw [pow_add]
    ring
  rw [tsum_congr h, tsum_geometric_two' (1 / 2 : ℝ)]

@[blueprint "lem:threshold-finset-sum-le-half"
  (statement := /-- For every finite set $T \subseteq \{\, i \in \mathbb{N} : i \geq 1 \,\}$ of
  positive indices, the partial sum of the threshold sequence over $T$ is bounded by one half:
  $\sum_{i \in T} c_i \leq \frac{1}{2}$, where $c_i = \frac{1}{2^{\,i+1}}$ (\cref{def:threshold}). -/)
  (proof := /-- Reindex $T$ through the map $i \mapsto i - 1$, which is injective on $T$ because
  every $i \in T$ satisfies $i \geq 1$; writing $T' = \{\, i - 1 : i \in T \,\}$ and using
  $(i - 1) + 1 = i$ for $i \geq 1$, we get $\sum_{i \in T} c_i = \sum_{j \in T'} c_{j+1}$. The
  sequence $j \mapsto c_{j+1}$ is nonnegative and summable, so comparing a finite partial sum with
  the full series gives $\sum_{j \in T'} c_{j+1} \leq \sum_{j=0}^{\infty} c_{j+1}$. By
  \cref{lem:threshold-sum-le-half}, $\sum_{j=0}^{\infty} c_{j+1} = \frac{1}{2}$, hence
  $\sum_{i \in T} c_i \leq \frac{1}{2}$. -/)
  (title := /-- Partial Sums of the Threshold Sequence -/)
  (latexEnv := "lemma")]
lemma threshold_finset_sum_le_half (T : Finset ℕ) (hT : ∀ i ∈ T, 1 ≤ i) :
    ∑ i ∈ T, threshold i ≤ 1 / 2 := by
  have hsummable : Summable (fun j : ℕ => threshold (j + 1)) := by
    have hcongr : (fun j : ℕ => threshold (j + 1)) = (fun j : ℕ => (1 / 2 : ℝ) / 2 / 2 ^ j) := by
      funext j
      unfold threshold
      rw [pow_add]
      ring
    rw [hcongr]
    exact summable_geometric_two' (1 / 2 : ℝ)
  have hnonneg : ∀ j : ℕ, 0 ≤ threshold (j + 1) := by
    intro j
    unfold threshold
    positivity
  have hinj_img : ∀ a ∈ T, ∀ b ∈ T, a - 1 = b - 1 → a = b := by
    intro a ha b hb hab
    have h1 := hT a ha
    have h2 := hT b hb
    omega
  have himg : ∑ j ∈ T.image (fun i => i - 1), threshold (j + 1) = ∑ i ∈ T, threshold i := by
    rw [Finset.sum_image hinj_img]
    apply Finset.sum_congr rfl
    intro i hi
    have hi1 : i - 1 + 1 = i := by
      have := hT i hi
      omega
    rw [hi1]
  calc ∑ i ∈ T, threshold i
      = ∑ j ∈ T.image (fun i => i - 1), threshold (j + 1) := himg.symm
    _ ≤ ∑' j : ℕ, threshold (j + 1) :=
        hsummable.sum_le_tsum _ (fun j _ => hnonneg j)
    _ = 1 / 2 := threshold_sum_le_half

@[blueprint "lem:bad-positions-ncard-le-half"
  (statement := /-- Let $\mathcal{L} = (L_i)_{i \in \mathbb{N}}$ be a countable collection over a
  universe $U$, let $S \subseteq \{\, i \in \mathbb{N} : i \geq 1 \,\}$ be a set of positive
  indices, let $x = (x_t)_{t \in \mathbb{N}}$ be a stream, and let $n \geq 1$. If for every
  $i \in S$ the empirical noise rate obeys $R(L_i; x_{1:n}) \leq c_i$
  (\cref{def:empirical-noise-rate}, \cref{def:threshold}), then the number of revealed positions
  $t < n$ whose element $x_t$ lies outside the closure
  $\mathrm{Cl}(S) = \bigcap_{i \in S} L_i$ (\cref{def:collection-closure}) satisfies
  $\bigl\lvert \{\, t < n : x_t \notin \mathrm{Cl}(S) \,\} \bigr\rvert \leq \frac{n}{2}$. -/)
  (proof := /-- Write $B = \{\, t < n : x_t \notin \mathrm{Cl}(S) \,\}$, which is finite because
  $B \subseteq \{0, \dots, n-1\}$. Each $t \in B$ has $x_t \notin \bigcap_{i \in S} L_i$, so there
  is an index $g(t) \in S$ with $x_t \notin L_{g(t)}$; fix one such index for each $t \in B$ and
  let $S_0 = \{\, g(t) : t \in B \,\}$, a finite subset of $S$. Then
  $B \subseteq \bigcup_{i \in S_0} \{\, t < n : x_t \notin L_i \,\}$, so by subadditivity of
  cardinality over the finite index set $S_0$,
  $\lvert B \rvert \leq \sum_{i \in S_0} \bigl\lvert \{\, t < n : x_t \notin L_i \,\} \bigr\rvert$.
  For each $i$, $\bigl\lvert \{\, t < n : x_t \notin L_i \,\} \bigr\rvert = n\,R(L_i; x_{1:n})$ by
  \cref{def:empirical-noise-rate} together with $n \geq 1$. Using $R(L_i; x_{1:n}) \leq c_i$ for
  $i \in S_0 \subseteq S$ and $n \geq 0$, we obtain
  $\lvert B \rvert \leq \sum_{i \in S_0} n\,R(L_i; x_{1:n}) \leq n \sum_{i \in S_0} c_i$. Since
  $S_0 \subseteq S \subseteq \{\, i : i \geq 1 \,\}$, \cref{lem:threshold-finset-sum-le-half} gives
  $\sum_{i \in S_0} c_i \leq \frac{1}{2}$, hence $\lvert B \rvert \leq \frac{n}{2}$. -/)
  (title := /-- Bound on Revealed Positions Outside the Closure -/)
  (latexEnv := "lemma")]
lemma bad_positions_ncard_le_half {U : Type*}
    (L : ℕ → Set U) (S : Set ℕ) (x : ℕ → U) (n : ℕ)
    (hn : 1 ≤ n)
    (hS : S ⊆ {i : ℕ | 1 ≤ i})
    (hbound : ∀ i ∈ S, empirical_noise_rate (L i) x n ≤ threshold i) :
    (({t : ℕ | t < n ∧ x t ∉ collection_closure L S}).ncard : ℝ) ≤ n / 2 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnnonneg : (0 : ℝ) ≤ n := le_of_lt hnpos
  have hwit : ∀ t, t ∈ {t : ℕ | t < n ∧ x t ∉ collection_closure L S} →
      ∃ i, i ∈ S ∧ x t ∉ L i := by
    intro t ht
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact ht.2 (Set.mem_iInter₂.mpr hcon)
  have hwit' : ∀ t : ℕ, ∃ i : ℕ,
      t ∈ {t : ℕ | t < n ∧ x t ∉ collection_closure L S} → i ∈ S ∧ x t ∉ L i := by
    intro t
    by_cases ht : t ∈ {t : ℕ | t < n ∧ x t ∉ collection_closure L S}
    · obtain ⟨i, hiS, hiL⟩ := hwit t ht
      exact ⟨i, fun _ => ⟨hiS, hiL⟩⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose g hg using hwit'
  have hBfin : ({t : ℕ | t < n ∧ x t ∉ collection_closure L S}).Finite :=
    (Set.finite_Iio n).subset (fun t ht => ht.1)
  set S0 : Finset ℕ := hBfin.toFinset.image g with hS0def
  have hS0S : ∀ i ∈ S0, i ∈ S := by
    intro i hi
    rw [hS0def, Finset.mem_image] at hi
    obtain ⟨t, htB, rfl⟩ := hi
    rw [Set.Finite.mem_toFinset] at htB
    exact (hg t htB).1
  have hBcover : {t : ℕ | t < n ∧ x t ∉ collection_closure L S} ⊆
      ⋃ i ∈ S0, {t : ℕ | t < n ∧ x t ∉ L i} := by
    intro t ht
    rw [Set.mem_iUnion₂]
    refine ⟨g t, ?_, ht.1, (hg t ht).2⟩
    rw [hS0def, Finset.mem_image]
    exact ⟨t, (Set.Finite.mem_toFinset hBfin).mpr ht, rfl⟩
  have hUfin : (⋃ i ∈ S0, {t : ℕ | t < n ∧ x t ∉ L i}).Finite := by
    apply Set.Finite.biUnion S0.finite_toSet
    intro i _
    exact (Set.finite_Iio n).subset (fun t ht => ht.1)
  have hcard1 : ({t : ℕ | t < n ∧ x t ∉ collection_closure L S}).ncard ≤
      (⋃ i ∈ S0, {t : ℕ | t < n ∧ x t ∉ L i}).ncard :=
    Set.ncard_le_ncard hBcover hUfin
  have hcard2 : (⋃ i ∈ S0, {t : ℕ | t < n ∧ x t ∉ L i}).ncard ≤
      ∑ i ∈ S0, ({t : ℕ | t < n ∧ x t ∉ L i}).ncard :=
    Finset.set_ncard_biUnion_le S0 (fun i => {t : ℕ | t < n ∧ x t ∉ L i})
  have hbadle : ∀ i ∈ S0, (({t : ℕ | t < n ∧ x t ∉ L i}).ncard : ℝ) ≤ (n : ℝ) * threshold i := by
    intro i hi
    have hR := hbound i (hS0S i hi)
    have heq : empirical_noise_rate (L i) x n
        = (({t : ℕ | t < n ∧ x t ∉ L i}).ncard : ℝ) / n := rfl
    rw [heq, div_le_iff₀ hnpos] at hR
    rw [mul_comm] at hR
    exact hR
  calc (({t : ℕ | t < n ∧ x t ∉ collection_closure L S}).ncard : ℝ)
      ≤ ((∑ i ∈ S0, ({t : ℕ | t < n ∧ x t ∉ L i}).ncard : ℕ) : ℝ) := by
        exact_mod_cast le_trans hcard1 hcard2
    _ = ∑ i ∈ S0, (({t : ℕ | t < n ∧ x t ∉ L i}).ncard : ℝ) := by push_cast; rfl
    _ ≤ ∑ i ∈ S0, (n : ℝ) * threshold i := Finset.sum_le_sum hbadle
    _ = (n : ℝ) * ∑ i ∈ S0, threshold i := by rw [Finset.mul_sum]
    _ ≤ (n : ℝ) * (1 / 2) := by
        apply mul_le_mul_of_nonneg_left _ hnnonneg
        exact threshold_finset_sum_le_half S0 (fun i hi => hS (hS0S i hi))
    _ = n / 2 := by ring

@[blueprint "lem:closure-infinite-of-noise-bound"
  (statement := /-- Let $\mathcal{L} = (L_i)_{i \in \mathbb{N}}$ be a countable collection over a
  universe $U$, let $S \subseteq \{\, i \in \mathbb{N} : i \geq 1 \,\}$ be a set of positive
  indices, let
  $x = (x_t)_{t \in \mathbb{N}}$ be a stream, and let $K \subseteq U$. Suppose $x$ is an
  $o(1)$-noise enumeration of $K$ with arbitrary omissions (\cref{def:enumeration-o1-noise-omission}),
  and suppose that for all sufficiently large $n$ the empirical noise rates are controlled by the
  thresholds along $S$: for every $i \in S$, $R(L_i; x_{1:n}) \leq c_i$
  (\cref{def:empirical-noise-rate}, \cref{def:threshold}). Then the closure
  $\mathrm{Cl}(S) = \bigcap_{i \in S} L_i$ (\cref{def:collection-closure}) is infinite. -/)
  (proof := /-- Suppose for contradiction that $\mathrm{Cl}(S) = \bigcap_{i \in S} L_i$
  (\cref{def:collection-closure}) is finite, and set $M = \lvert \mathrm{Cl}(S) \rvert$. Extract from
  the $o(1)$-noise enumeration (\cref{def:enumeration-o1-noise-omission}) a subset $\hat{K}$ in which
  every element occurs exactly once and whose empirical noise rate (\cref{def:empirical-noise-rate})
  tends to $0$; hence for all sufficiently large $n$ we have $R(\hat{K}; x_{1:n}) \leq \frac{1}{4}$,
  while the threshold bound $R(L_i; x_{1:n}) \leq c_i$ (\cref{def:threshold}) holds for all
  $i \in S$. Choose such an $n$ with $n \geq 1$ and $n > 4M$. Split the rounds $t < n$ into the bad
  positions $B = \{\, t < n : x_t \notin \mathrm{Cl}(S) \,\}$, the noise positions
  $N = \{\, t < n : x_t \notin \hat{K} \,\}$, and the good positions
  $G = \{\, t < n : x_t \in \mathrm{Cl}(S) \text{ and } x_t \in \hat{K} \,\}$; since every round lies
  in at least one of these sets, $n \leq \lvert B \rvert + \lvert N \rvert + \lvert G \rvert$. By
  \cref{lem:bad-positions-ncard-le-half}, $\lvert B \rvert \leq \frac{n}{2}$, and by the definition
  of the empirical noise rate $\lvert N \rvert = n\,R(\hat{K}; x_{1:n}) \leq \frac{n}{4}$, so
  $\lvert G \rvert \geq \frac{n}{4}$. Because each element of $\hat{K}$ occurs exactly once, the map
  $t \mapsto x_t$ is injective on $G$, whence its image is a subset of $\mathrm{Cl}(S)$ of
  cardinality $\lvert G \rvert \geq \frac{n}{4}$. Therefore $\frac{n}{4} \leq M$, contradicting
  $n > 4M$. Hence $\mathrm{Cl}(S)$ is infinite. -/)
  (title := /-- Infinitude of the Closure under Vanishing Noise -/)
  (latexEnv := "lemma")]
lemma closure_infinite_of_noise_bound {U : Type*}
    (L : ℕ → Set U) (S : Set ℕ) (x : ℕ → U) (K : Set U)
    (hS : S ⊆ {i : ℕ | 1 ≤ i})
    (hcont : enumeration_o1_noise_omission x K)
    (hbound : ∀ᶠ n in Filter.atTop, ∀ i ∈ S, empirical_noise_rate (L i) x n ≤ threshold i) :
    (collection_closure L S).Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨Khat, hKhatK, hKhatInf, hKhatUniq, hKhatNoise⟩ := hcont
  have hnoise : ∀ᶠ m in Filter.atTop, empirical_noise_rate Khat x m ≤ 1 / 4 :=
    hKhatNoise.eventually_le_const (by norm_num)
  obtain ⟨n, hbnd_n, hnoise_n, hbig_n, hge1_n⟩ :=
    (hbound.and (hnoise.and ((Filter.eventually_gt_atTop
      (4 * (collection_closure L S).ncard)).and (Filter.eventually_ge_atTop 1)))).exists
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hge1_n
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hIioFin : (Set.Iio n).Finite := Set.finite_Iio n
  have hBadFin : {t : ℕ | t < n ∧ x t ∉ collection_closure L S}.Finite :=
    hIioFin.subset (fun t ht => ht.1)
  have hNoiseFin : {t : ℕ | t < n ∧ x t ∉ Khat}.Finite :=
    hIioFin.subset (fun t ht => ht.1)
  have hGoodKFin :
      {t : ℕ | t < n ∧ x t ∈ collection_closure L S ∧ x t ∈ Khat}.Finite :=
    hIioFin.subset (fun t ht => ht.1)
  have hcover : Set.Iio n ⊆
      {t : ℕ | t < n ∧ x t ∉ collection_closure L S} ∪
        {t : ℕ | t < n ∧ x t ∉ Khat} ∪
        {t : ℕ | t < n ∧ x t ∈ collection_closure L S ∧ x t ∈ Khat} := by
    intro t ht
    rw [Set.mem_Iio] at ht
    simp only [Set.mem_union, Set.mem_setOf_eq]
    by_cases h1 : x t ∈ collection_closure L S
    · by_cases h2 : x t ∈ Khat
      · exact Or.inr ⟨ht, h1, h2⟩
      · exact Or.inl (Or.inr ⟨ht, h2⟩)
    · exact Or.inl (Or.inl ⟨ht, h1⟩)
  have hUnionFin :
      ({t : ℕ | t < n ∧ x t ∉ collection_closure L S} ∪
        {t : ℕ | t < n ∧ x t ∉ Khat} ∪
        {t : ℕ | t < n ∧ x t ∈ collection_closure L S ∧ x t ∈ Khat}).Finite :=
    (hBadFin.union hNoiseFin).union hGoodKFin
  have hn_le :
      n ≤ {t : ℕ | t < n ∧ x t ∉ collection_closure L S}.ncard +
            {t : ℕ | t < n ∧ x t ∉ Khat}.ncard +
            {t : ℕ | t < n ∧ x t ∈ collection_closure L S ∧ x t ∈ Khat}.ncard := by
    calc n = (Set.Iio n).ncard := (Set.ncard_Iio_nat n).symm
      _ ≤ ({t : ℕ | t < n ∧ x t ∉ collection_closure L S} ∪
            {t : ℕ | t < n ∧ x t ∉ Khat} ∪
            {t : ℕ | t < n ∧ x t ∈ collection_closure L S ∧ x t ∈ Khat}).ncard :=
          Set.ncard_le_ncard hcover hUnionFin
      _ ≤ ({t : ℕ | t < n ∧ x t ∉ collection_closure L S} ∪
            {t : ℕ | t < n ∧ x t ∉ Khat}).ncard +
            {t : ℕ | t < n ∧ x t ∈ collection_closure L S ∧ x t ∈ Khat}.ncard :=
          Set.ncard_union_le _ _
      _ ≤ ({t : ℕ | t < n ∧ x t ∉ collection_closure L S}.ncard +
            {t : ℕ | t < n ∧ x t ∉ Khat}.ncard) +
            {t : ℕ | t < n ∧ x t ∈ collection_closure L S ∧ x t ∈ Khat}.ncard :=
          Nat.add_le_add_right (Set.ncard_union_le _ _) _
  have hNoiseCard :
      empirical_noise_rate Khat x n * n = ({t : ℕ | t < n ∧ x t ∉ Khat}.ncard : ℝ) := by
    unfold empirical_noise_rate
    rw [div_mul_cancel₀ _ hne]
  have hNoiseHalf : ({t : ℕ | t < n ∧ x t ∉ Khat}.ncard : ℝ) ≤ n / 4 := by
    rw [← hNoiseCard]
    calc empirical_noise_rate Khat x n * n ≤ (1 / 4) * n :=
          mul_le_mul_of_nonneg_right hnoise_n (le_of_lt hnpos)
      _ = n / 4 := by ring
  have hBadHalf := bad_positions_ncard_le_half L S x n hge1_n hS hbnd_n
  have hInj : Set.InjOn x
      {t : ℕ | t < n ∧ x t ∈ collection_closure L S ∧ x t ∈ Khat} := by
    intro s hs t ht hst
    obtain ⟨t0, _, huniq⟩ := hKhatUniq (x s) hs.2.2
    have e1 : s = t0 := huniq s rfl
    have e2 : t = t0 := huniq t hst.symm
    rw [e1, e2]
  have hImgSub :
      x '' {t : ℕ | t < n ∧ x t ∈ collection_closure L S ∧ x t ∈ Khat} ⊆
        collection_closure L S := by
    rintro a ⟨t, ht, rfl⟩
    exact ht.2.1
  have hImgCard :
      (x '' {t : ℕ | t < n ∧ x t ∈ collection_closure L S ∧ x t ∈ Khat}).ncard =
        {t : ℕ | t < n ∧ x t ∈ collection_closure L S ∧ x t ∈ Khat}.ncard :=
    hInj.ncard_image
  have hGoodK_le_M :
      {t : ℕ | t < n ∧ x t ∈ collection_closure L S ∧ x t ∈ Khat}.ncard ≤
        (collection_closure L S).ncard := by
    rw [← hImgCard]
    exact Set.ncard_le_ncard hImgSub hfin
  have hn_le_real : (n : ℝ) ≤
      ({t : ℕ | t < n ∧ x t ∉ collection_closure L S}.ncard : ℝ) +
        ({t : ℕ | t < n ∧ x t ∉ Khat}.ncard : ℝ) +
        ({t : ℕ | t < n ∧ x t ∈ collection_closure L S ∧ x t ∈ Khat}.ncard : ℝ) := by
    exact_mod_cast hn_le
  have hGoodKreal :
      ({t : ℕ | t < n ∧ x t ∈ collection_closure L S ∧ x t ∈ Khat}.ncard : ℝ) ≤
        ((collection_closure L S).ncard : ℝ) := by exact_mod_cast hGoodK_le_M
  have hbig_real : (4 : ℝ) * ((collection_closure L S).ncard : ℝ) < n := by
    exact_mod_cast hbig_n
  linarith [hBadHalf, hNoiseHalf, hn_le_real, hGoodKreal, hbig_real]

@[blueprint "lem:constant-vanishing-noise-sufficient-generation"
  (statement := /-- Consider the intersection algorithm executed with an arbitrary threshold
  sequence, producing at each round $n$ priorities $P_i^{(n)} \in \mathbb{N} \cup \{\infty\}$ that
  are non-decreasing in $n$ and satisfy $i \leq P_i^{(n)}$. Fix $p \geq 1$ and let
  $\mathcal{L}(p) = \{\, i : P_i^{\infty} \leq p \,\}$, where $P_i^{\infty} = \sup_n P_i^{(n)}$. If
  the closure $\mathrm{Cl}(\mathcal{L}(p)) = \bigcap_{i \in \mathcal{L}(p)} L_i$
  (\cref{def:collection-closure}) is infinite, then there is a generator $\mathcal{G}$ that
  generates $\mathrm{Cl}(\mathcal{L}(p))$ in the limit on $x$
  (\cref{def:generation-in-the-limit}). -/)
  (proof := /-- Since $\mathrm{Cl}(\mathcal{L}(p))$ is infinite by hypothesis, it is in particular
  nonempty, so fix an element $a \in \mathrm{Cl}(\mathcal{L}(p))$. Define the generator
  $\mathcal{G}$ to be the constant generator whose output at every round $n$ on every stream is
  $a$. Taking $n^\star = 0$ in \cref{def:generation-in-the-limit}, for every $n \geq 0$ the output
  $\mathcal{G}(x)(n) = a$ lies in $\mathrm{Cl}(\mathcal{L}(p))$; hence $\mathcal{G}$ generates
  $\mathrm{Cl}(\mathcal{L}(p))$ in the limit on $x$. -/)
  (title := /-- Sufficient Condition for Generation -/)
  (latexEnv := "lemma")]
lemma constant_vanishing_noise_sufficient_generation {U : Type*}
    (L : ℕ → Set U) (x : ℕ → U)
    (P : ℕ → ℕ → ℕ∞)
    (hmono : ∀ i n, P i n ≤ P i (n + 1))
    (hlb : ∀ (i : ℕ) (n : ℕ), (i : ℕ∞) ≤ P i n)
    (p : ℕ) (hp : 1 ≤ p)
    (hInf : (collection_closure L {i : ℕ | (⨆ m, P i m) ≤ (p : ℕ∞)}).Infinite) :
    ∃ G : (ℕ → U) → ℕ → U,
      generation_in_the_limit G (collection_closure L {i : ℕ | (⨆ m, P i m) ≤ (p : ℕ∞)}) x := by
  obtain ⟨a, ha⟩ := hInf.nonempty
  exact ⟨fun _ _ => a, 0, fun n _ => ha⟩

@[blueprint "lem:infinite-causal-sets-admit-element-based-selector"
  (statement := /-- Let $U$ be infinite, and suppose that each stream $x : \mathbb{N} \to U$ and
  round $n$ is assigned an infinite admissible set $C(x,n) \subseteq U$. Assume that $C(x,n)$
  depends only on $x_0,\ldots,x_n$. Then there is an element-based, prefix-causal generator $G$
  whose round-$n$ output belongs to $C(x,n)$ for every $x$ and $n$. -/)
  (proof := /-- Recursively retain the finite set of outputs used before each round. At round $n$,
  choose an element of $C(x,n)$ outside both this finite set and the finite observed prefix
  $\{x_0,\ldots,x_n\}$. Such an element exists because $C(x,n)$ is infinite. Induction on the
  round shows that every earlier output is retained, so the resulting generator is element-based
  in the sense of \cref{def:element-based}. A second induction shows that equal observed prefixes
  give equal retained sets; prefix-causality of $C$ then gives equal choices. -/)
  (title := /-- A Causal Fresh Selector from Infinite Admissible Sets -/)
  (latexEnv := "lemma")]
lemma infinite_causal_sets_admit_element_based_selector {U : Type*} [Infinite U]
    (C : (ℕ → U) → ℕ → Set U)
    (hInf : ∀ x n, (C x n).Infinite)
    (hcausal : ∀ (x y : ℕ → U) (n : ℕ),
      (∀ t ∈ Set.Iic n, x t = y t) → C x n = C y n) :
    ∃ G : (ℕ → U) → ℕ → U,
      element_based G ∧
      (∀ (x y : ℕ → U) (n : ℕ),
        (∀ t ∈ Set.Iic n, x t = y t) → G x n = G y n) ∧
      ∀ x n, G x n ∈ C x n := by
  classical
  let seen : (ℕ → U) → ℕ → Finset U :=
    fun x n => (Finset.range (n + 1)).image x
  let pick : (x : ℕ → U) → (n : ℕ) → Finset U → U :=
    fun x n used =>
      Classical.choose ((hInf x n).exists_notMem_finset (seen x n ∪ used))
  have pick_spec (x : ℕ → U) (n : ℕ) (used : Finset U) :
      pick x n used ∈ C x n ∧ pick x n used ∉ seen x n ∪ used :=
    Classical.choose_spec ((hInf x n).exists_notMem_finset (seen x n ∪ used))
  let states : (ℕ → U) → ℕ → Finset U :=
    fun x n => Nat.rec ∅ (fun k used => insert (pick x k used) used) n
  have states_zero (x : ℕ → U) : states x 0 = ∅ := rfl
  have states_succ (x : ℕ → U) (n : ℕ) :
      states x (n + 1) = insert (pick x n (states x n)) (states x n) := by
    rfl
  let G : (ℕ → U) → ℕ → U := fun x n => pick x n (states x n)
  have past_mem (x : ℕ → U) (m n : ℕ) (hmn : m < n) : G x m ∈ states x n := by
    induction n with
    | zero => omega
    | succ n ih =>
        rw [states_succ]
        by_cases hmn' : m = n
        · subst m
          simpa only [G] using
            (Finset.mem_insert_self (pick x n (states x n)) (states x n))
        · exact Finset.mem_insert_of_mem (ih (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hmn) hmn'))
  have seen_eq (x y : ℕ → U) (n : ℕ)
      (hxy : ∀ t ∈ Set.Iic n, x t = y t) : seen x n = seen y n := by
    apply Finset.image_congr
    intro t ht
    exact hxy t (Set.mem_Iic.mpr (Nat.le_of_lt_succ (Finset.mem_range.mp ht)))
  have states_eq (x y : ℕ → U) (n : ℕ)
      (hxy : ∀ t ∈ Set.Iic n, x t = y t) : states x n = states y n := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [states_succ, states_succ]
        have hxy' : ∀ t ∈ Set.Iic n, x t = y t := by
          intro t ht
          exact hxy t (Set.mem_Iic.mpr (le_trans (Set.mem_Iic.mp ht) (Nat.le_succ n)))
        have hs : states x n = states y n := ih hxy'
        have hp : seen x n = seen y n := seen_eq x y n hxy'
        have hC : C x n = C y n := hcausal x y n hxy'
        rw [hs]
        congr 1
        simp only [pick]
        congr
        funext u
        rw [hC, hp]
  refine ⟨G, ?_, ?_, ?_⟩
  · intro x n hmem
    have hfresh := (pick_spec x n (states x n)).2
    rw [Set.mem_union] at hmem
    rcases hmem with hobs | hpast
    · rcases hobs with ⟨t, ht, heq⟩
      apply hfresh
      have hseen : x t ∈ seen x n := by
        apply Finset.mem_image.mpr
        refine ⟨t, ?_, rfl⟩
        exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Set.mem_Iic.mp ht))
      have hout : G x n ∈ seen x n := heq ▸ hseen
      simpa only [G] using Finset.mem_union_left (states x n) hout
    · rcases hpast with ⟨m, hm, heq⟩
      apply hfresh
      have hused : G x m ∈ states x n := past_mem x m n (Set.mem_Iio.mp hm)
      have hout : G x n ∈ states x n := heq ▸ hused
      simpa only [G] using Finset.mem_union_right (seen x n) hout
  · intro x y n hxy
    have hs : states x n = states y n := states_eq x y n hxy
    have hp : seen x n = seen y n := seen_eq x y n hxy
    have hC : C x n = C y n := hcausal x y n hxy
    simp only [G, pick]
    congr
    funext u
    rw [hC, hp, hs]
  · intro x n
    exact (pick_spec x n (states x n)).1

@[blueprint "def:vanishing-shift"
  (statement := /-- For a collection $\mathcal{L}=(L_i)_{i\in\mathbb N}$, its shifted collection
  has the whole universe at index zero and $L_i$ at index $i+1$. -/)
  (title := /-- Shifted Language Collection -/)
  (latexEnv := "definition")]
def vanishing_shift {U : Type*} (L : ℕ → Set U) : ℕ → Set U
  | 0 => Set.univ
  | i + 1 => L i

@[blueprint "def:vanishing-priority-nat"
  (statement := /-- The finite priority of language $L_i$ starts at $i+1$ and, after round $n+1$,
  is raised to at least $n+2$ whenever its empirical noise exceeds $c_{i+1}$. -/)
  (title := /-- Finite Historical Noise Priority -/)
  (latexEnv := "definition")]
noncomputable def vanishing_priority_nat {U : Type*}
    (L : ℕ → Set U) (x : ℕ → U) (i : ℕ) : ℕ → ℕ :=
  Nat.rec (i + 1) (fun n p =>
    max p (if threshold (i + 1) < empirical_noise_rate (L i) x (n + 1)
      then n + 2 else i + 1))

@[blueprint "def:vanishing-priority"
  (statement := /-- Index zero has infinite priority. The priority of shifted index $i+1$ is the
  finite historical noise priority of $L_i$, regarded as an extended natural number. -/)
  (title := /-- Shifted Extended Priority -/)
  (latexEnv := "definition")]
noncomputable def vanishing_priority {U : Type*}
    (L : ℕ → Set U) (x : ℕ → U) : ℕ → ℕ → ℕ∞
  | 0, _ => ⊤
  | i + 1, n => vanishing_priority_nat L x i n

@[blueprint "def:vanishing-selected-level"
  (statement := /-- At round $n$, the selected level is the greatest $q\leq n$ for which the
  intersection of shifted languages whose current priority is at most $q$ is infinite. -/)
  (title := /-- Greatest Infinite-Closure Priority Level -/)
  (latexEnv := "definition")]
noncomputable def vanishing_selected_level {U : Type*}
    (L : ℕ → Set U) (x : ℕ → U) (n : ℕ) : ℕ :=
  @Nat.findGreatest (fun q =>
    (collection_closure (vanishing_shift L)
      {j : ℕ | vanishing_priority L x j n ≤ (q : ℕ∞)}).Infinite)
    (fun _ => Classical.propDecidable _) n

@[blueprint "def:vanishing-admissible"
  (statement := /-- The admissible set at round $n$ is the intersection selected by the greatest
  infinite-closure priority level at that round. -/)
  (title := /-- Vanishing-Noise Admissible Output Set -/)
  (latexEnv := "definition")]
noncomputable def vanishing_admissible {U : Type*}
    (L : ℕ → Set U) (x : ℕ → U) (n : ℕ) : Set U :=
  collection_closure (vanishing_shift L)
    {j : ℕ | vanishing_priority L x j n ≤ (vanishing_selected_level L x n : ℕ∞)}

@[blueprint "lem:vanishing-priority-monotone-lower-bound"
  (statement := /-- For every collection and stream, shifted priorities are non-decreasing in the
  round and the priority of index $j$ is always at least $j$. -/)
  (proof := /-- Index zero has priority $\infty$. For index $i+1$, the recursive update is a
  maximum with the preceding priority, proving monotonicity, and its initial value is $i+1$,
  proving the lower bound by induction. -/)
  (title := /-- Monotonicity and Index Lower Bound of Priorities -/)
  (latexEnv := "lemma")]
lemma vanishing_priority_monotone_lower_bound {U : Type*}
    (L : ℕ → Set U) (x : ℕ → U) :
    (∀ j n, vanishing_priority L x j n ≤ vanishing_priority L x j (n + 1)) ∧
    ∀ (j n : ℕ), (j : ℕ∞) ≤ vanishing_priority L x j n := by
  constructor
  · intro j n
    cases j with
    | zero => simp [vanishing_priority]
    | succ i =>
        simp only [vanishing_priority, vanishing_priority_nat, Nat.rec_add_one]
        exact ENat.coe_le_coe.mpr (Nat.le_max_left _ _)
  · intro j n
    cases j with
    | zero => simp
    | succ i =>
        simp only [vanishing_priority]
        apply ENat.coe_le_coe.mpr
        induction n with
        | zero => simp [vanishing_priority_nat]
        | succ n ih =>
            simp only [vanishing_priority_nat, Nat.rec_add_one]
            exact ih.trans (Nat.le_max_left _ _)

@[blueprint "lem:vanishing-priority-causal"
  (statement := /-- If two streams agree through round $n$, then every shifted priority computed
  at round $n$ is the same on the two streams. -/)
  (proof := /-- Agreement through round $n$ makes every empirical noise rate on a prefix of length
  at most $n$ equal. Induction through the recursive maximum updates therefore gives equality of
  every priority at round $n$. -/)
  (title := /-- Prefix-Causality of Historical Priorities -/)
  (latexEnv := "lemma")]
lemma vanishing_priority_causal {U : Type*} (L : ℕ → Set U)
    (x y : ℕ → U) (n : ℕ) (hxy : ∀ t ∈ Set.Iic n, x t = y t) :
    ∀ j, vanishing_priority L x j n = vanishing_priority L y j n := by
  have rate_eq (i m : ℕ) (hmn : m ≤ n) :
      empirical_noise_rate (L i) x m = empirical_noise_rate (L i) y m := by
    unfold empirical_noise_rate
    have hset : {t : ℕ | t < m ∧ x t ∉ L i} = {t : ℕ | t < m ∧ y t ∉ L i} := by
      ext t
      by_cases htm : t < m
      · have htn : t ≤ n := (Nat.le_of_lt htm).trans hmn
        simp only [Set.mem_setOf_eq]
        rw [hxy t (Set.mem_Iic.mpr htn)]
      · simp [htm]
    rw [hset]
  intro j
  cases j with
  | zero => rfl
  | succ i =>
      simp only [vanishing_priority]
      apply ENat.coe_inj.mpr
      induction n with
      | zero => rfl
      | succ n ih =>
          change max (vanishing_priority_nat L x i n)
              (if threshold (i + 1) < empirical_noise_rate (L i) x (n + 1)
                then n + 2 else i + 1) =
            max (vanishing_priority_nat L y i n)
              (if threshold (i + 1) < empirical_noise_rate (L i) y (n + 1)
                then n + 2 else i + 1)
          have hxy' : ∀ t ∈ Set.Iic n, x t = y t := by
            intro t ht
            exact hxy t (Set.mem_Iic.mpr ((Set.mem_Iic.mp ht).trans (Nat.le_succ n)))
          rw [ih hxy' (fun i m hm => rate_eq i m (hm.trans (Nat.le_succ n)))]
          rw [rate_eq i (n + 1) (Nat.le_refl _)]

@[blueprint "lem:vanishing-admissible-infinite-causal"
  (statement := /-- For every infinite universe, collection, stream, and round, the vanishing-noise
  admissible set is infinite; moreover, its value at round $n$ depends only on the stream through
  round $n$. -/)
  (proof := /-- By \cref{lem:vanishing-priority-monotone-lower-bound}, no shifted priority is at
  most zero: index zero has infinite priority, and every positive index is bounded below by
  itself. Thus level zero selects the empty index set, whose closure is the whole infinite
  universe, so the greatest admissible level also has infinite closure. If two prefixes agree,
  \cref{lem:vanishing-priority-causal} makes all their current priorities equal. Hence the
  infinite-closure predicates, greatest levels, and resulting closures are equal. -/)
  (title := /-- Infinitude and Prefix-Causality of Admissible Sets -/)
  (latexEnv := "lemma")]
lemma vanishing_admissible_infinite_causal {U : Type*} [Infinite U] :
    (∀ (L : ℕ → Set U) (x : ℕ → U) (n : ℕ),
      (vanishing_admissible L x n).Infinite) ∧
    ∀ (L : ℕ → Set U) (x y : ℕ → U) (n : ℕ),
      (∀ t ∈ Set.Iic n, x t = y t) →
      vanishing_admissible L x n = vanishing_admissible L y n := by
  constructor
  · intro L x n
    have hempty : {j : ℕ | vanishing_priority L x j n ≤ (0 : ℕ∞)} = ∅ := by
      ext j
      change vanishing_priority L x j n ≤ (0 : ℕ∞) ↔ False
      constructor
      · intro hj
        cases j with
        | zero => simpa [vanishing_priority] using hj
        | succ j =>
            have hlb := (vanishing_priority_monotone_lower_bound L x).2 (j + 1) n
            have hne : ¬ ((j + 1 : ℕ∞) ≤ 0) := by simp
            exact hne (hlb.trans hj)
      · exact False.elim
    have hzero :
        (collection_closure (vanishing_shift L)
          {j : ℕ | vanishing_priority L x j n ≤ (0 : ℕ∞)}).Infinite := by
      rw [hempty]
      simpa [collection_closure] using (Set.infinite_univ : (Set.univ : Set U).Infinite)
    unfold vanishing_admissible vanishing_selected_level
    let P : ℕ → Prop := fun q => (collection_closure (vanishing_shift L)
      {j : ℕ | vanishing_priority L x j n ≤ (q : ℕ∞)}).Infinite
    letI : DecidablePred P := fun _ => Classical.propDecidable _
    change P (Nat.findGreatest P n)
    exact Nat.findGreatest_spec (P := P) (Nat.zero_le n) hzero
  · intro L x y n hxy
    have hp : ∀ j, vanishing_priority L x j n = vanishing_priority L y j n :=
      vanishing_priority_causal L x y n hxy
    have hsets (q : ℕ) :
        {j : ℕ | vanishing_priority L x j n ≤ (q : ℕ∞)} =
          {j : ℕ | vanishing_priority L y j n ≤ (q : ℕ∞)} := by
      ext j
      simp only [Set.mem_setOf_eq, hp j]
    have hlevel : vanishing_selected_level L x n = vanishing_selected_level L y n := by
      unfold vanishing_selected_level
      congr 1
      funext q
      rw [hsets q]
    unfold vanishing_admissible
    rw [hlevel]
    congr 1
    exact hsets (vanishing_selected_level L y n)

@[blueprint "lem:vanishing-target-priority-bounded"
  (statement := /-- If $x$ is an $o(1)$-noise enumeration with arbitrary omissions of $L_{i^\star}$,
  then the supremum of the priority of shifted index $i^\star+1$ is bounded by a positive natural
  level. -/)
  (proof := /-- Unpack \cref{def:enumeration-o1-noise-omission} to obtain an infinite retained
  subset $\widehat K\subseteq L_{i^\star}$ whose empirical noise tends to zero. The noise rate of
  $L_{i^\star}$ is no larger than that of $\widehat K$, so it is eventually below the positive
  threshold $c_{i^\star+1}$. Thereafter the historical priority is never raised. Induction on the
  recursive priority therefore bounds every round by the maximum of $i^\star+1$ and the first
  round from which the threshold bound holds; taking the supremum preserves this finite bound. -/)
  (title := /-- Bounded Priority of a Valid Target -/)
  (latexEnv := "lemma")]
lemma vanishing_target_priority_bounded {U : Type*}
    (L : ℕ → Set U) (istar : ℕ) (x : ℕ → U)
    (hx : enumeration_o1_noise_omission x (L istar)) :
    ∃ p : ℕ, 1 ≤ p ∧
      (⨆ n, vanishing_priority L x (istar + 1) n) ≤ (p : ℕ∞) := by
  obtain ⟨Khat, hKhat, _, _, hnoise⟩ := hx
  have rate_le (n : ℕ) :
      empirical_noise_rate (L istar) x n ≤ empirical_noise_rate Khat x n := by
    unfold empirical_noise_rate
    have hsub : {t : ℕ | t < n ∧ x t ∉ L istar} ⊆
        {t : ℕ | t < n ∧ x t ∉ Khat} := by
      intro t ht
      exact ⟨ht.1, fun hmem => ht.2 (hKhat hmem)⟩
    have hfin : {t : ℕ | t < n ∧ x t ∉ Khat}.Finite :=
      (Set.finite_Iio n).subset (fun t ht => ht.1)
    have hcard := Set.ncard_le_ncard hsub hfin
    apply div_le_div_of_nonneg_right
    · exact_mod_cast hcard
    · positivity
  have hthreshold : 0 < threshold (istar + 1) := by
    unfold threshold
    positivity
  have hevent : ∀ᶠ n in Filter.atTop,
      empirical_noise_rate (L istar) x n ≤ threshold (istar + 1) :=
    (hnoise.eventually_le_const hthreshold).mono
      (fun n hn => (rate_le n).trans hn)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  let p := max (istar + 1) N
  have hraw (n : ℕ) : vanishing_priority_nat L x istar n ≤ p := by
    induction n with
    | zero =>
        change istar + 1 ≤ p
        exact Nat.le_max_left _ _
    | succ n ih =>
        change max (vanishing_priority_nat L x istar n)
            (if threshold (istar + 1) < empirical_noise_rate (L istar) x (n + 1)
              then n + 2 else istar + 1) ≤ p
        by_cases hearly : n + 1 < N
        · apply max_le ih
          split
          · exact (show n + 2 ≤ N by omega).trans (Nat.le_max_right _ _)
          · exact Nat.le_max_left _ _
        · have hrate := hN (n + 1) (Nat.le_of_not_gt hearly)
          rw [if_neg (not_lt_of_ge hrate)]
          exact max_le ih (Nat.le_max_left _ _)
  refine ⟨p, ?_, ?_⟩
  · exact (Nat.succ_le_succ (Nat.zero_le istar)).trans (Nat.le_max_left _ _)
  · apply iSup_le
    intro n
    simp only [vanishing_priority]
    exact ENat.coe_le_coe.mpr (hraw n)

@[blueprint "lem:vanishing-noise-eventually-admissible-sets"
  (statement := /-- Over every infinite universe $U$, there is a rule assigning to each countable
  collection $\mathcal{L}$, stream $x$, and round $n$ an infinite set $C(\mathcal{L},x,n)$.
  The set at round $n$ depends only on $x_0,\ldots,x_n$. If every language in $\mathcal{L}$ is
  infinite and $x$ is an $o(1)$-noise enumeration with arbitrary omissions of a target
  $L_{i^\star}$, then $C(\mathcal{L},x,n) \subseteq L_{i^\star}$ for all sufficiently large $n$. -/)
  (proof := /-- By \cref{lem:vanishing-admissible-infinite-causal}, the shifted-priority
  construction supplies infinite admissible sets and depends only on the observed prefix. Fix a
  valid target. Its shifted priority is bounded by some positive finite level $p$ by
  \cref{lem:vanishing-target-priority-bounded}. The priorities are non-decreasing and bounded below
  by their indices by \cref{lem:vanishing-priority-monotone-lower-bound}, so
  \cref{lem:meta-algorithm-prefix-stabilizes} identifies, after a finite round, the current indices
  of priority at most $p$ with the indices whose limiting priority is at most $p$. Membership in
  this limiting class precludes every sufficiently late threshold violation. Its indices are
  positive because shifted index zero has infinite priority; therefore
  \cref{lem:closure-infinite-of-noise-bound} makes the limiting closure infinite. The level $p$ is
  consequently available to the greatest-level rule at all sufficiently large rounds.
  \Cref{lem:constant-vanishing-noise-sufficient-generation} also supplies a fixed witness in this
  limiting closure. Since the target index has priority at most $p$, both that witness and every
  element of each later chosen closure belong to the target language. -/)
  (title := /-- Eventually Target-Contained Infinite Admissible Sets -/)
  (latexEnv := "lemma")]
lemma vanishing_noise_eventually_admissible_sets {U : Type*} [Infinite U] :
    ∃ C : (ℕ → Set U) → (ℕ → U) → ℕ → Set U,
      (∀ L x n, (C L x n).Infinite) ∧
      (∀ (L : ℕ → Set U) (x y : ℕ → U) (n : ℕ),
        (∀ t ∈ Set.Iic n, x t = y t) → C L x n = C L y n) ∧
      ∀ (L : ℕ → Set U) (istar : ℕ) (x : ℕ → U),
        (∀ i, (L i).Infinite) →
        enumeration_o1_noise_omission x (L istar) →
        ∀ᶠ n in Filter.atTop, C L x n ⊆ L istar := by
  classical
  refine ⟨vanishing_admissible,
    vanishing_admissible_infinite_causal.1,
    vanishing_admissible_infinite_causal.2, ?_⟩
  intro L istar x _ hx
  obtain ⟨p, hp, htarget⟩ := vanishing_target_priority_bounded L istar x hx
  have hstruct := vanishing_priority_monotone_lower_bound L x
  obtain ⟨nStable, hStable⟩ :=
    meta_algorithm_prefix_stabilizes (vanishing_priority L x) hstruct.1 hstruct.2 p
  let S : Set ℕ := {j : ℕ | (⨆ m, vanishing_priority L x j m) ≤ (p : ℕ∞)}
  have hSpos : S ⊆ {j : ℕ | 1 ≤ j} := by
    intro j hj
    change (⨆ m, vanishing_priority L x j m) ≤ (p : ℕ∞) at hj
    cases j with
    | zero =>
        have htop : (⊤ : ℕ∞) ≤ (p : ℕ∞) := by
          apply (le_iSup (fun m => vanishing_priority L x 0 m) 0).trans
          exact hj
        simp [vanishing_priority] at htop
    | succ j => exact Nat.succ_le_succ (Nat.zero_le j)
  have hbounds : ∀ᶠ n in Filter.atTop, ∀ j ∈ S,
      empirical_noise_rate (vanishing_shift L j) x n ≤ threshold j := by
    filter_upwards [Filter.eventually_ge_atTop p] with n hn
    intro j hj
    change (⨆ m, vanishing_priority L x j m) ≤ (p : ℕ∞) at hj
    cases j with
    | zero =>
        have htop : (⊤ : ℕ∞) ≤ (p : ℕ∞) := by
          apply (le_iSup (fun m => vanishing_priority L x 0 m) 0).trans
          exact hj
        simp [vanishing_priority] at htop
    | succ i =>
        change empirical_noise_rate (L i) x n ≤ threshold (i + 1)
        by_contra hbad
        have hbad' : threshold (i + 1) < empirical_noise_rate (L i) x n :=
          lt_of_not_ge hbad
        cases n with
        | zero => omega
        | succ m =>
            have hrecord : (m + 2 : ℕ∞) ≤
                vanishing_priority L x (i + 1) (m + 1) := by
              simp only [vanishing_priority]
              apply ENat.coe_le_coe.mpr
              change m + 2 ≤ max (vanishing_priority_nat L x i m)
                (if threshold (i + 1) < empirical_noise_rate (L i) x (m + 1)
                  then m + 2 else i + 1)
              rw [if_pos hbad']
              exact Nat.le_max_right _ _
            have hbelow : vanishing_priority L x (i + 1) (m + 1) ≤ (p : ℕ∞) :=
              (le_iSup (fun r => vanishing_priority L x (i + 1) r) (m + 1)).trans hj
            have hcast : (m + 2 : ℕ∞) ≤ (p : ℕ∞) := hrecord.trans hbelow
            have hnat : m + 2 ≤ p := ENat.coe_le_coe.mp hcast
            omega
  have hclosure : (collection_closure (vanishing_shift L) S).Infinite :=
    closure_infinite_of_noise_bound (vanishing_shift L) S x (L istar) hSpos hx hbounds
  obtain ⟨gWitness, hgWitness⟩ :=
    constant_vanishing_noise_sufficient_generation (vanishing_shift L) x
      (vanishing_priority L x) hstruct.1 hstruct.2 p hp hclosure
  obtain ⟨nWitness, hnWitness⟩ := hgWitness
  let aWitness := gWitness x nWitness
  have haWitness : aWitness ∈ collection_closure (vanishing_shift L) S :=
    hnWitness nWitness (Nat.le_refl _)
  filter_upwards [Filter.eventually_ge_atTop nStable, Filter.eventually_ge_atTop p]
      with n hnStable hpn
  have hparts := hStable n hnStable
  have hset : {j : ℕ | vanishing_priority L x j n ≤ (p : ℕ∞)} = S := by
    ext j
    change (vanishing_priority L x j n ≤ (p : ℕ∞)) ↔
      ((⨆ m, vanishing_priority L x j m) ≤ (p : ℕ∞))
    constructor
    · intro hj
      by_contra hnot
      exact (not_lt_of_ge hj) (hparts.2.1 j hnot)
    · exact hparts.1 j
  have hcurrent :
      (collection_closure (vanishing_shift L)
        {j : ℕ | vanishing_priority L x j n ≤ (p : ℕ∞)}).Infinite := by
    rw [hset]
    exact hclosure
  have hplevel : p ≤ vanishing_selected_level L x n := by
    unfold vanishing_selected_level
    let P : ℕ → Prop := fun q => (collection_closure (vanishing_shift L)
      {j : ℕ | vanishing_priority L x j n ≤ (q : ℕ∞)}).Infinite
    letI : DecidablePred P := fun _ => Classical.propDecidable _
    change p ≤ Nat.findGreatest P n
    exact Nat.le_findGreatest hpn hcurrent
  intro u hu
  have htarget_now : vanishing_priority L x (istar + 1) n ≤ (p : ℕ∞) :=
    (le_iSup (fun m => vanishing_priority L x (istar + 1) m) n).trans htarget
  have htarget_level : vanishing_priority L x (istar + 1) n ≤
      (vanishing_selected_level L x n : ℕ∞) :=
    htarget_now.trans (ENat.coe_le_coe.mpr hplevel)
  by_cases hua : u = aWitness
  · rw [hua]
    have haAll : ∀ j : ℕ, j ∈ S → aWitness ∈ vanishing_shift L j := by
      simpa [collection_closure] using haWitness
    simpa [vanishing_shift] using haAll (istar + 1) htarget
  have huall : ∀ j : ℕ,
      vanishing_priority L x j n ≤ (vanishing_selected_level L x n : ℕ∞) →
      u ∈ vanishing_shift L j := by
    simpa [vanishing_admissible, collection_closure] using hu
  simpa [vanishing_shift] using huall (istar + 1) htarget_level

@[blueprint "thm:vanishing-noise-generation"
  (statement := /-- There is a generator scheme $\mathcal{G}$ that assigns to every countable
  collection $\mathcal{L} = (L_i)_{i \in \mathbb{N}}$ of languages over an infinite universe $U$ an
  element-based generator $\mathcal{G}(\mathcal{L}) : (\mathbb{N} \to U) \to \mathbb{N} \to U$
  (\cref{def:element-based}) that is prefix-causal: for every $n \in \mathbb{N}$ and every two
  streams $x,y : \mathbb{N} \to U$ satisfying $x_t = y_t$ for all $t \leq n$, one has
  $\mathcal{G}(\mathcal{L})(x)(n) = \mathcal{G}(\mathcal{L})(y)(n)$. This scheme has the
  following property: for every countable collection
  $\mathcal{L} = (L_i)_{i \in \mathbb{N}}$ of infinite languages over $U$, every target index
  $i^\star$ with $K = L_{i^\star}$, and every stream $x$ that is an $o(1)$-noise enumeration of $K$
  with arbitrary omissions (\cref{def:enumeration-o1-noise-omission}), the generator
  $\mathcal{G}(\mathcal{L})$ generates $K$ in the limit on $x$
  (\cref{def:generation-in-the-limit}). The generator scheme $\mathcal{G}$ is fixed once and for
  all, independently of $\mathcal{L}$; only its instantiation $\mathcal{G}(\mathcal{L})$ depends on
  the collection, matching the paper's construction of the generator from the collection
  $\mathcal{L}$. -/)
  (proof := /-- Apply \cref{lem:vanishing-noise-eventually-admissible-sets} to obtain, for every
  collection and observed prefix, an infinite admissible set that is prefix-causal and is
  eventually contained in every valid target language. For each collection, apply
  \cref{lem:infinite-causal-sets-admit-element-based-selector} to choose an element-based,
  prefix-causal generator whose round-$n$ output lies in the corresponding admissible set. Choose
  these generators simultaneously over all collections to form the scheme $\mathcal{G}$. Now fix
  a collection of infinite languages, a target $L_{i^\star}$, and a valid contaminated enumeration
  of that target. From some round onward the admissible set is contained in $L_{i^\star}$, while
  every output of $\mathcal{G}(\mathcal{L})$ belongs to that admissible set. Thus every sufficiently
  late output belongs to $L_{i^\star}$, which is precisely generation in the limit
  (\cref{def:generation-in-the-limit}). -/)
  (title := /-- Generation with Vanishing Noise Rate and Arbitrary Omissions -/)
  (latexEnv := "theorem")]
theorem vanishing_noise_generation {U : Type*} [Infinite U] :
    ∃ G : (ℕ → Set U) → (ℕ → U) → ℕ → U,
      ∀ (L : ℕ → Set U),
        element_based (G L) ∧
        (∀ (x y : ℕ → U) (n : ℕ),
          (∀ t ∈ Set.Iic n, x t = y t) →
          G L x n = G L y n) ∧
        ∀ (istar : ℕ) (x : ℕ → U),
          (∀ i, (L i).Infinite) →
          enumeration_o1_noise_omission x (L istar) →
          generation_in_the_limit (G L) (L istar) x := by
  classical
  obtain ⟨C, hCInf, hCcausal, hCtarget⟩ :=
    vanishing_noise_eventually_admissible_sets (U := U)
  have hselector (L : ℕ → Set U) :
      ∃ g : (ℕ → U) → ℕ → U,
        element_based g ∧
        (∀ (x y : ℕ → U) (n : ℕ),
          (∀ t ∈ Set.Iic n, x t = y t) → g x n = g y n) ∧
        ∀ x n, g x n ∈ C L x n :=
    infinite_causal_sets_admit_element_based_selector
      (C L) (hCInf L) (hCcausal L)
  let G : (ℕ → Set U) → (ℕ → U) → ℕ → U :=
    fun L => Classical.choose (hselector L)
  refine ⟨G, fun L => ?_⟩
  have hG := Classical.choose_spec (hselector L)
  refine ⟨hG.1, hG.2.1, ?_⟩
  intro istar x hL hx
  rw [generation_in_the_limit]
  obtain ⟨nStar, hnStar⟩ :=
    Filter.eventually_atTop.1 (hCtarget L istar x hL hx)
  exact ⟨nStar, fun n hn => hnStar n hn (hG.2.2 x n)⟩

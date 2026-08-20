import Architect
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Order.ConditionallyCompleteLattice.Basic

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:ocp-interval"
  (statement := /-- A prediction interval is a pair of real endpoints
    $(\mathrm{lo}, \mathrm{hi})$, representing the closed interval
    $[\mathrm{lo}, \mathrm{hi}] \subseteq \mathbb{R}$ played by the algorithm on a
    given day. -/)
  (title := /-- Prediction interval -/)
  (latexEnv := "definition")]
structure ocp_interval where
  lo : ℝ
  hi : ℝ

@[blueprint "def:ocp-vol"
  (statement := /-- The volume $\mathrm{vol}(I)$ of a prediction interval
    $I = (\mathrm{lo}, \mathrm{hi})$ (see \cref{def:ocp-interval}) is its length
    $\mathrm{hi} - \mathrm{lo}$, i.e. the Lebesgue measure of the closed interval
    $[\mathrm{lo}, \mathrm{hi}]$. -/)
  (title := /-- Volume of a prediction interval -/)
  (latexEnv := "definition")]
def ocp_vol (I : ocp_interval) : ℝ := I.hi - I.lo

@[blueprint "def:ocp-covers"
  (statement := /-- A prediction interval $I = (\mathrm{lo}, \mathrm{hi})$ (see
    \cref{def:ocp-interval}) covers a point $y \in \mathbb{R}$ if and only if
    $\mathrm{lo} \le y \le \mathrm{hi}$. -/)
  (title := /-- Coverage of a point by an interval -/)
  (latexEnv := "definition")]
def ocp_covers (I : ocp_interval) (y : ℝ) : Prop := I.lo ≤ y ∧ y ≤ I.hi

@[blueprint "def:ocp-opt-vol"
  (statement := /-- Fix a horizon $T \in \mathbb{N}$, a sequence
    $S = (y_0, \dots, y_{T-1})$ with $y_t \in \mathbb{R}$, and a target miscoverage
    rate $\alpha$. The optimal in-hindsight volume $\mathrm{Opt}_S(\alpha)$ is the
    infimum of the volume $\mathrm{vol}(I)$ (see \cref{def:ocp-vol}) over all
    prediction intervals $I$ whose empirical coverage satisfies
    $\#\{\, t : I \text{ covers } y_t \,\} \ge (1-\alpha) T$ (coverage in the sense
    of \cref{def:ocp-covers}); equivalently, the smallest volume of a fixed
    interval achieving $(1-\alpha)$-coverage in hindsight. -/)
  (title := /-- Optimal in-hindsight volume -/)
  (latexEnv := "definition")]
noncomputable def ocp_opt_vol (T : ℕ) (S : Fin T → ℝ) (α : ℝ) : ℝ :=
  sInf { v : ℝ | ∃ I : ocp_interval, ocp_vol I = v ∧
    (1 - α) * (T : ℝ) ≤ (({i : Fin T | ocp_covers I (S i)}.ncard : ℝ)) }

@[blueprint "def:ocp-error-rate"
  (statement := /-- The allowable error-rate schedule is defined by $R(0) = 1$ and
    $R(t) = \alpha T / t$ for every day $t > 0$, where $\alpha \ge 0$ is the target
    miscoverage rate and $T \in \mathbb{N}$ is the horizon. -/)
  (title := /-- Allowable error-rate schedule -/)
  (latexEnv := "definition")]
noncomputable def ocp_error_rate (α : ℝ) (T : ℕ) (t : ℕ) : ℝ :=
  if t = 0 then 1 else α * (T : ℝ) / (t : ℝ)

@[blueprint "def:ocp-mistakes-upto"
  (statement := /-- For a prediction interval $I$ and a day count $t \in \mathbb{N}$,
    the number of mistakes up to day $t$ is
    $\#\{\, i < t : I \text{ does not cover } y_i \,\}$: the number of days with index
    strictly below $t$ on which $I$ fails to cover the observed point (coverage in
    the sense of \cref{def:ocp-covers}). -/)
  (title := /-- Mistakes up to a given day -/)
  (latexEnv := "definition")]
noncomputable def ocp_mistakes_upto (T : ℕ) (S : Fin T → ℝ) (I : ocp_interval)
    (t : ℕ) : ℕ :=
  {i : Fin T | (i : ℕ) < t ∧ ¬ ocp_covers I (S i)}.ncard

@[blueprint "def:ocp-feasible"
  (statement := /-- Let $\alpha \ge 0$, $T \in \mathbb{N}$, $S$ a sequence, $I$ a
    prediction interval, and $t \in \mathbb{N}$. The interval $I$ is feasible on day
    $t$ if its number of mistakes up to day $t$ (see \cref{def:ocp-mistakes-upto})
    satisfies $(\text{mistakes up to } t) \le R(t)\, t$, where $R$ is the error-rate
    schedule of \cref{def:ocp-error-rate}. -/)
  (title := /-- Feasible interval on a given day -/)
  (latexEnv := "definition")]
def ocp_feasible (α : ℝ) (T : ℕ) (S : Fin T → ℝ) (I : ocp_interval) (t : ℕ) : Prop :=
  (ocp_mistakes_upto T S I t : ℝ) ≤ ocp_error_rate α T t * (t : ℝ)

@[blueprint "def:ocp-total-mistakes"
  (statement := /-- Given the intervals $I_t$ played on each day $t \in [T]$,
    encoded as a function $t \mapsto I_t$, the total number of mistakes is
    $\sum_{t=1}^{T} \mathbf{1}\{ y_t \notin I_t \}
    = \#\{\, t : I_t \text{ does not cover } y_t \,\}$ (coverage in the sense of
    \cref{def:ocp-covers}). -/)
  (title := /-- Total number of mistakes -/)
  (latexEnv := "definition")]
noncomputable def ocp_total_mistakes (T : ℕ) (S : Fin T → ℝ)
    (play : Fin T → ocp_interval) : ℕ :=
  {t : Fin T | ¬ ocp_covers (play t) (S t)}.ncard

@[blueprint "def:ocp-meta-alg-guarantee"
  (statement := /-- Fix parameters $\mathsf{minwidth} > 0$, $\mu > 3$,
    $\alpha \ge 0$, a horizon $T \in \mathbb{N}$, and a sequence $S$. A meta-algorithm
    guarantee packages the output of the external Meta-algorithm Guarantee for
    Arbitrary Sequences for the Meta-algorithm for Online Conformal Prediction: the
    interval $I_t$ played on each day $t \in [T]$ (a function $t \mapsto I_t$), a
    nonnegative absolute constant $c_0$, the volume guarantee
    $\mathrm{vol}(I_t) \le \mu \max\{ \mathrm{Opt}_S(\alpha), \mathsf{minwidth} \}$ for
    every day $t$ (volume as in \cref{def:ocp-vol}, optimum as in
    \cref{def:ocp-opt-vol}), and the mistake guarantee that, whenever all intervals
    feasible (in the sense of \cref{def:ocp-feasible}) on any two days after
    $2\alpha T + 1$ share a commonly covered day among the first $2\alpha T + 1$ days
    (so that these days form a single epoch), the total number of mistakes (see
    \cref{def:ocp-total-mistakes}) is at most
    $(2\alpha T + 1) + c_0 \frac{\log(1/\mathsf{minwidth})}{\log \mu} (\alpha T + 1)$.
    The constant $c_0$ and the reset-count and per-phase mistake bounds it encodes
    are imported verbatim from the external theorem and are not reproved here. -/)
  (title := /-- Meta-algorithm guarantee (external interface) -/)
  (latexEnv := "definition")]
structure ocp_meta_alg_guarantee (minwidth μ α : ℝ) (T : ℕ) (S : Fin T → ℝ) where
  play : Fin T → ocp_interval
  metaConst : ℝ
  metaConst_nonneg : 0 ≤ metaConst
  volume_bound : ∀ t : Fin T, ocp_vol (play t) ≤ μ * max (ocp_opt_vol T S α) minwidth
  mistakes_bound :
    (∀ (I₁ I₂ : ocp_interval) (t₁ t₂ : ℕ),
        2 * α * (T : ℝ) + 1 < (t₁ : ℝ) → t₁ < t₂ → t₂ ≤ T →
        ocp_feasible α T S I₁ t₁ → ocp_feasible α T S I₂ t₂ →
        ∃ i : Fin T, ((i : ℕ) : ℝ) < 2 * α * (T : ℝ) + 1 ∧
          ocp_covers I₁ (S i) ∧ ocp_covers I₂ (S i)) →
      (ocp_total_mistakes T S play : ℝ) ≤
        (2 * α * (T : ℝ) + 1) +
          metaConst * (Real.log (1 / minwidth) / Real.log μ) * (α * (T : ℝ) + 1)

@[blueprint "lem:ocp-feasible-iff-few-mistakes"
  (statement := /-- Let $\alpha \ge 0$, $T \in \mathbb{N}$, $S$ a sequence, $I$ a
    prediction interval, and $t \in \mathbb{N}$ with $t > 0$. Under the schedule
    $R(t) = \alpha T / t$, the interval $I$ is feasible on day $t$ if and only if its
    number of mistakes up to day $t$ is at most $\alpha T$. -/)
  (proof := /-- By \cref{def:ocp-feasible}, $I$ is feasible on day $t$ if and only if
    $m \le R(t)\, t$, where $m$ denotes the number of mistakes up to day $t$ from
    \cref{def:ocp-mistakes-upto}. Since $t > 0$, the schedule \cref{def:ocp-error-rate}
    gives $R(t) = \alpha T / t$, so $R(t)\, t = (\alpha T / t)\, t = \alpha T$.
    Therefore feasibility on day $t$ is equivalent to $m \le \alpha T$. -/)
  (title := /-- Feasibility equals at most $\alpha T$ mistakes -/)
  (latexEnv := "lemma")]
lemma ocp_feasible_iff_few_mistakes (α : ℝ) (T : ℕ) (S : Fin T → ℝ)
    (I : ocp_interval) (t : ℕ) (ht : 0 < t) :
    ocp_feasible α T S I t ↔ (ocp_mistakes_upto T S I t : ℝ) ≤ α * (T : ℝ) := by
  have htR : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht.ne'
  unfold ocp_feasible ocp_error_rate
  rw [if_neg ht.ne', div_mul_cancel₀ _ htR]

@[blueprint "lem:ocp-two-large-subsets-intersect"
  (statement := /-- Let $\iota$ be a type with decidable equality, and let $s, A, B$
    be finite subsets of $\iota$ with $A \subseteq s$ and $B \subseteq s$. If
    $|s| < |A| + |B|$, then the intersection $A \cap B$ is nonempty. -/)
  (proof := /-- By the inclusion–exclusion identity for finite sets,
    $|A \cup B| + |A \cap B| = |A| + |B|$. Since $A \subseteq s$ and $B \subseteq s$
    we have $A \cup B \subseteq s$, and monotonicity of cardinality gives
    $|A \cup B| \le |s|$. Substituting,
    $|A \cap B| = |A| + |B| - |A \cup B| \ge |A| + |B| - |s| > 0$, where the strict
    inequality is the hypothesis $|s| < |A| + |B|$. A finite set of strictly positive
    cardinality is nonempty, hence $A \cap B$ is nonempty. -/)
  (title := /-- Two large subsets of a finite set intersect -/)
  (latexEnv := "lemma")]
lemma ocp_two_large_subsets_intersect {ι : Type*} [DecidableEq ι]
    (s A B : Finset ι) (hA : A ⊆ s) (hB : B ⊆ s) (h : s.card < A.card + B.card) :
    (A ∩ B).Nonempty := by
  rw [← Finset.card_pos]
  have hunion : (A ∪ B).card ≤ s.card := Finset.card_le_card (Finset.union_subset hA hB)
  have key : (A ∪ B).card + (A ∩ B).card = A.card + B.card :=
    Finset.card_union_add_card_inter A B
  omega

@[blueprint "lem:ocp-feasible-intervals-overlap"
  (statement := /-- Let $\alpha \ge 0$, $T \in \mathbb{N}$, and $S$ a sequence. Let
    $t_1, t_2 \in \mathbb{N}$ with $2\alpha T + 1 < t_1$, $t_1 < t_2$, and
    $t_2 \le T$, and let $I_1, I_2$ be prediction intervals feasible on days $t_1$ and
    $t_2$ respectively (in the sense of \cref{def:ocp-feasible}). Then there exists a
    day $i$ with $i < 2\alpha T + 1$ such that both $I_1$ and $I_2$ cover $y_i$. -/)
  (proof := /-- Consider the block $D$ of days whose index is below $2\alpha T + 1$,
    a set of at least $2\alpha T + 1$ days. Since $t_1, t_2 > 2\alpha T + 1 > 0$,
    \cref{lem:ocp-feasible-iff-few-mistakes} applies to both intervals, so each of
    $I_1$ and $I_2$ makes at most $\alpha T$ mistakes among the days of $D$;
    equivalently, each covers at least $|D| - \alpha T \ge (2\alpha T + 1) - \alpha T
    = \alpha T + 1$ of them. Let $A$ and $B$ be the sets of days in $D$ covered by
    $I_1$ and $I_2$ respectively; then $|A| + |B| \ge 2(\alpha T + 1)
    = 2\alpha T + 2 > |D|$. Applying \cref{lem:ocp-two-large-subsets-intersect} to
    $A, B \subseteq D$ shows $A \cap B$ is nonempty, so there is a day $i \in D$, that
    is $i < 2\alpha T + 1$, covered by both $I_1$ and $I_2$. -/)
  (title := /-- Feasible intervals on late days overlap -/)
  (latexEnv := "lemma")]
lemma ocp_feasible_intervals_overlap (α : ℝ) (T : ℕ) (S : Fin T → ℝ) (hα : 0 ≤ α)
    (I₁ I₂ : ocp_interval) (t₁ t₂ : ℕ)
    (h₁ : 2 * α * (T : ℝ) + 1 < (t₁ : ℝ)) (h₁₂ : t₁ < t₂) (h₂ : t₂ ≤ T)
    (hf₁ : ocp_feasible α T S I₁ t₁) (hf₂ : ocp_feasible α T S I₂ t₂) :
    ∃ i : Fin T, ((i : ℕ) : ℝ) < 2 * α * (T : ℝ) + 1 ∧
      ocp_covers I₁ (S i) ∧ ocp_covers I₂ (S i) := by
  classical
  have hTnn : (0:ℝ) ≤ (T:ℝ) := Nat.cast_nonneg T
  have h2aT : (0:ℝ) ≤ 2 * α * (T:ℝ) := by
    have := mul_nonneg hα hTnn
    nlinarith
  have ht₁ : 0 < t₁ := by
    have : (0:ℝ) < (t₁:ℝ) := by linarith
    exact_mod_cast this
  have ht₂ : 0 < t₂ := lt_trans ht₁ h₁₂
  have hm₁ : (ocp_mistakes_upto T S I₁ t₁ : ℝ) ≤ α * (T:ℝ) :=
    (ocp_feasible_iff_few_mistakes α T S I₁ t₁ ht₁).mp hf₁
  have hm₂ : (ocp_mistakes_upto T S I₂ t₂ : ℝ) ≤ α * (T:ℝ) :=
    (ocp_feasible_iff_few_mistakes α T S I₂ t₂ ht₂).mp hf₂
  set N : ℕ := ⌈2 * α * (T:ℝ) + 1⌉₊ with hNdef
  have hNlb : 2 * α * (T:ℝ) + 1 ≤ (N:ℝ) := by rw [hNdef]; exact Nat.le_ceil _
  have hNt₁ : N ≤ t₁ := by rw [hNdef]; exact Nat.ceil_le.mpr h₁.le
  have hNT : N ≤ T := le_trans hNt₁ (le_trans h₁₂.le h₂)
  set D : Finset (Fin T) := Finset.univ.filter (fun i => (i:ℕ) < N) with hD
  set A : Finset (Fin T) := D.filter (fun i => ocp_covers I₁ (S i)) with hA
  set B : Finset (Fin T) := D.filter (fun i => ocp_covers I₂ (S i)) with hB
  set A' : Finset (Fin T) := D.filter (fun i => ¬ ocp_covers I₁ (S i)) with hA'
  set B' : Finset (Fin T) := D.filter (fun i => ¬ ocp_covers I₂ (S i)) with hB'
  have hDcard : D.card = N := by
    rw [hD, Fin.card_filter_val_lt]; exact min_eq_right hNT
  have hpart₁ : A.card + A'.card = D.card := by
    rw [hA, hA']; exact Finset.card_filter_add_card_filter_not (fun i => ocp_covers I₁ (S i))
  have hpart₂ : B.card + B'.card = D.card := by
    rw [hB, hB']; exact Finset.card_filter_add_card_filter_not (fun i => ocp_covers I₂ (S i))
  have hcardA' : A'.card ≤ ocp_mistakes_upto T S I₁ t₁ := by
    rw [← Set.ncard_coe_finset A']
    unfold ocp_mistakes_upto
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    intro i hi
    rw [Finset.mem_coe, hA', Finset.mem_filter, hD, Finset.mem_filter] at hi
    exact ⟨lt_of_lt_of_le hi.1.2 hNt₁, hi.2⟩
  have hcardB' : B'.card ≤ ocp_mistakes_upto T S I₂ t₂ := by
    rw [← Set.ncard_coe_finset B']
    unfold ocp_mistakes_upto
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    intro i hi
    rw [Finset.mem_coe, hB', Finset.mem_filter, hD, Finset.mem_filter] at hi
    exact ⟨lt_of_lt_of_le hi.1.2 (le_trans hNt₁ h₁₂.le), hi.2⟩
  have hA'R : (A'.card : ℝ) ≤ α * (T:ℝ) := le_trans (by exact_mod_cast hcardA') hm₁
  have hB'R : (B'.card : ℝ) ≤ α * (T:ℝ) := le_trans (by exact_mod_cast hcardB') hm₂
  have hsumnat : A'.card + B'.card < D.card := by
    have hsum : (A'.card : ℝ) + (B'.card : ℝ) < (D.card : ℝ) := by
      rw [hDcard]; linarith [hA'R, hB'R, hNlb]
    exact_mod_cast hsum
  have hkey : D.card < A.card + B.card := by omega
  have hAsub : A ⊆ D := by rw [hA]; exact Finset.filter_subset _ _
  have hBsub : B ⊆ D := by rw [hB]; exact Finset.filter_subset _ _
  obtain ⟨i, hi⟩ := ocp_two_large_subsets_intersect D A B hAsub hBsub hkey
  rw [Finset.mem_inter] at hi
  obtain ⟨hiA, hiB⟩ := hi
  rw [hA, Finset.mem_filter] at hiA
  rw [hB, Finset.mem_filter] at hiB
  have hiD := hiA.1
  rw [hD, Finset.mem_filter] at hiD
  have hlt : (i:ℕ) < N := hiD.2
  rw [hNdef] at hlt
  exact ⟨i, Nat.lt_ceil.mp hlt, hiA.2, hiB.2⟩

@[blueprint "lem:ocp-mistake-bound-collapse"
  (statement := /-- Let $a, C, L \in \mathbb{R}$ with $a \ge 0$, $C \ge 0$, and
    $L \ge 1$. Then $(2a + 1) + C\, L\, (a + 1) \le (C + 2)\, L\, (a + 1)$. -/)
  (proof := /-- Since $a \ge 0$ we have $a + 1 \ge 1$, and with $L \ge 1$ this gives
    $L(a+1) \ge a + 1$. Hence $2 L (a+1) \ge 2(a+1) = 2a + 2 \ge 2a + 1$. Adding the
    nonnegative quantity $C\, L\, (a+1)$ to both sides of the inequality
    $2a + 1 \le 2 L (a+1)$ yields
    $(2a+1) + C L (a+1) \le 2 L (a+1) + C L (a+1) = (C + 2) L (a + 1)$. -/)
  (title := /-- Asymptotic collapse of the mistake bound -/)
  (latexEnv := "lemma")]
lemma ocp_mistake_bound_collapse (a C L : ℝ) (ha : 0 ≤ a) (hC : 0 ≤ C) (hL : 1 ≤ L) :
    (2 * a + 1) + C * L * (a + 1) ≤ (C + 2) * L * (a + 1) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hL) (by linarith : (0:ℝ) ≤ a + 1)]

@[blueprint "thm:ocp-optimal-algorithm-for-arbitrary-order"
  (statement := /-- Fix a scale lower bound $\mathsf{minwidth} > 0$, a multiplicative
    volume approximation $\mu > 3$, a target miscoverage rate $\alpha \ge 0$, a
    horizon $T \in \mathbb{N}$, and a sequence $S = (y_0, \dots, y_{T-1})$. Assume the
    scale is small enough that $\log(1/\mathsf{minwidth}) / \log \mu \ge 1$. Given the
    external meta-algorithm guarantee \cref{def:ocp-meta-alg-guarantee} for these
    parameters, the intervals $I_t$ it plays satisfy the approximately optimal volume
    bound $\mathrm{vol}(I_t) \le \mu \max\{ \mathrm{Opt}_S(\alpha), \mathsf{minwidth} \}$
    for every day $t \in [T]$, and, writing $c_0 \ge 0$ for the constant supplied by
    that guarantee \cref{def:ocp-meta-alg-guarantee}, the total number of mistakes
    obeys the explicit bound
    $\sum_{t} \mathbf{1}\{ y_t \notin I_t \}
    \le (c_0 + 2) \frac{\log(1/\mathsf{minwidth})}{\log \mu} (\alpha T + 1)$. -/)
  (proof := /-- The volume bound is exactly the volume-guarantee field of
    \cref{def:ocp-meta-alg-guarantee}. For the mistake bound, by
    \cref{lem:ocp-feasible-intervals-overlap} any two intervals feasible on days after
    $2\alpha T + 1$ share a commonly covered day and hence overlap, so all such days
    form a single epoch. Feeding this single-epoch hypothesis to the mistake-guarantee
    field of \cref{def:ocp-meta-alg-guarantee} bounds the total number of mistakes by
    $(2\alpha T + 1) + c_0 \frac{\log(1/\mathsf{minwidth})}{\log \mu} (\alpha T + 1)$,
    where $c_0 \ge 0$ is the constant supplied by the guarantee. Applying
    \cref{lem:ocp-mistake-bound-collapse} with $a = \alpha T$, $C = c_0$, and
    $L = \log(1/\mathsf{minwidth}) / \log \mu \ge 1$ absorbs the additive
    $(2\alpha T + 1)$ term, giving the stated bound with constant $C = c_0 + 2$. -/)
  (title := /-- Approximately optimal deterministic algorithm for arbitrary sequences -/)
  (latexEnv := "theorem")]
theorem ocp_optimal_algorithm_for_arbitrary_order
    (minwidth μ α : ℝ) (T : ℕ) (S : Fin T → ℝ)
    (hminwidth : 0 < minwidth) (hμ : 3 < μ) (hα : 0 ≤ α)
    (hlog : 1 ≤ Real.log (1 / minwidth) / Real.log μ)
    (G : ocp_meta_alg_guarantee minwidth μ α T S) :
    (∀ t : Fin T, ocp_vol (G.play t) ≤ μ * max (ocp_opt_vol T S α) minwidth) ∧
      (ocp_total_mistakes T S G.play : ℝ) ≤
        (G.metaConst + 2) * (Real.log (1 / minwidth) / Real.log μ) * (α * (T : ℝ) + 1) := by
  refine ⟨G.volume_bound, ?_⟩
  have hTnn : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
  have hmb := G.mistakes_bound (ocp_feasible_intervals_overlap α T S hα)
  have hcollapse := ocp_mistake_bound_collapse (α * (T : ℝ)) G.metaConst
    (Real.log (1 / minwidth) / Real.log μ) (mul_nonneg hα hTnn) G.metaConst_nonneg hlog
  linarith [hmb, hcollapse]

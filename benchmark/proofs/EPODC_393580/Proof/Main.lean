import Architect
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:grid-point"
  (statement := /-- For a discretization parameter $m \in \mathbb{N}$ with $m \geq 1$ and an
    index $i \in \mathbb{N}$, the $i$-th grid point is $p_i = i/m \in \mathbb{R}$. The grid is
    $B_m = \{p_0, p_1, \dots, p_m\} = \{0, 1/m, \dots, 1\}$, so that $p_i \in [0,1]$ exactly
    when $i \leq m$. -/)
  (title := /-- Grid Point of the Discretization $B_m$ -/)
  (latexEnv := "definition")]
noncomputable def grid_point (m i : ℕ) : ℝ := (i : ℝ) / (m : ℝ)

@[blueprint "def:ece"
  (statement := /-- Let $T \in \mathbb{N}$ be a horizon, let $p : \{0,\dots,T-1\} \to \mathbb{R}$
    be a sequence of predictions and let $y : \{0,\dots,T-1\} \to \mathbb{R}$ be a sequence of
    outcomes. The expected calibration error of $p$ against $y$ is
    \[ \mathrm{ECE}(p^{1:T}, y^{1:T})
        = \sum_{v \in V} \left| \sum_{t=1}^{T} \mathbf{1}[p^t = v]\,(p^t - y^t) \right|, \]
    where $V$ is the (finite) set of values actually taken by $p^{1:T}$. Summing over $V$
    rather than over all of $[0,1]$ changes nothing, since every value $v$ not attained by
    $p^{1:T}$ contributes an empty inner sum. -/)
  (title := /-- Expected Calibration Error -/)
  (latexEnv := "definition")]
noncomputable def ece (T : ℕ) (p y : ℕ → ℝ) : ℝ :=
  ∑ v ∈ (Finset.range T).image p,
    |∑ t ∈ (Finset.range T).filter (fun t => p t = v), (p t - y t)|

@[blueprint "def:calibrated"
  (statement := /-- A prediction sequence $q^{1:T}$ is perfectly calibrated for the outcome
    sequence $y^{1:T}$ if $\mathrm{ECE}(q^{1:T}, y^{1:T}) = 0$; equivalently, for every value
    $v$ attained by $q^{1:T}$ one has $\sum_{t=1}^{T} \mathbf{1}[q^t = v]\,(q^t - y^t) = 0$.
    The set of perfectly calibrated sequences is denoted $\mathcal{C}(y^{1:T})$. -/)
  (title := /-- Perfectly Calibrated Prediction Sequence -/)
  (latexEnv := "definition")]
noncomputable def calibrated (T : ℕ) (q y : ℕ → ℝ) : Prop := ece T q y = 0

@[blueprint "def:l1-dist"
  (statement := /-- For two sequences $p^{1:T}, q^{1:T}$ the $\ell_1$ distance over the horizon
    $T$ is $\|p^{1:T} - q^{1:T}\|_1 = \sum_{t=1}^{T} |p^t - q^t|$. -/)
  (title := /-- $\ell_1$ Distance Between Prediction Sequences -/)
  (latexEnv := "definition")]
noncomputable def l1_dist (T : ℕ) (p q : ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range T, |p t - q t|

@[blueprint "def:cal-dist"
  (statement := /-- The distance to calibration of a prediction sequence $p^{1:T}$ against an
    outcome sequence $y^{1:T}$ is
    \[ \mathrm{CalDist}(p^{1:T}, y^{1:T})
        = \inf_{q^{1:T} \in \mathcal{C}(y^{1:T})} \|p^{1:T} - q^{1:T}\|_1, \]
    the infimum of the $\ell_1$ distance from $p^{1:T}$ to the set $\mathcal{C}(y^{1:T})$ of
    perfectly calibrated sequences of \cref{def:calibrated}. The infimum is used in place of
    the minimum of the source statement; the set is nonempty and the $\ell_1$ distance is
    bounded below by $0$, so the infimum is attained-or-approached and every upper bound
    proved for a particular calibrated witness bounds it. -/)
  (title := /-- Distance to Calibration -/)
  (latexEnv := "definition")]
noncomputable def cal_dist (T : ℕ) (p y : ℕ → ℝ) : ℝ :=
  sInf {d : ℝ | ∃ q : ℕ → ℝ, calibrated T q y ∧ d = l1_dist T p q}

@[blueprint "def:cond-bias"
  (statement := /-- For a prediction sequence $\tilde p$, an outcome sequence $y$, a number of
    elapsed rounds $t \in \mathbb{N}$ and a value $v \in \mathbb{R}$, the conditional bias is
    \[ \alpha_{\tilde p^{1:t}}(v) = \sum_{s=1}^{t} \mathbf{1}[\tilde p^s = v]\,(\tilde p^s - y^s). \]
    It accumulates the signed error of all rounds up to time $t$ on which the value $v$ was
    predicted. -/)
  (title := /-- Conditional Bias of a Value After $t$ Rounds -/)
  (latexEnv := "definition")]
noncomputable def cond_bias (t : ℕ) (pt y : ℕ → ℝ) (v : ℝ) : ℝ :=
  ∑ s ∈ (Finset.range t).filter (fun s => pt s = v), (pt s - y s)

@[blueprint "def:cond-avg"
  (statement := /-- For a prediction sequence $p^{1:T}$, an outcome sequence $y^{1:T}$ and a
    value $v \in \mathbb{R}$, the conditional average outcome is
    \[ \overline{y}^T(v)
        = \frac{\sum_{t=1}^{T} \mathbf{1}[p^t = v]\, y^t}{\sum_{t=1}^{T} \mathbf{1}[p^t = v]}, \]
    the average of the outcomes on those rounds where the prediction equalled $v$. When $v$ is
    never predicted, the denominator vanishes and the quotient is $0$ by the Lean convention for
    division by zero; this case is irrelevant below, since only values actually attained by
    $p^{1:T}$ are used. -/)
  (title := /-- Conditional Average Outcome -/)
  (latexEnv := "definition")]
noncomputable def cond_avg (T : ℕ) (p y : ℕ → ℝ) (v : ℝ) : ℝ :=
  (∑ t ∈ (Finset.range T).filter (fun t => p t = v), y t) /
    (((Finset.range T).filter (fun t => p t = v)).card : ℝ)

@[blueprint "def:aosa-run"
  (statement := /-- Fix a horizon $T \in \mathbb{N}$ and a discretization parameter
    $m \in \mathbb{N}$. Let $y : \mathbb{N} \to \mathbb{R}$ be an outcome sequence, let
    $p : \mathbb{N} \to \mathbb{R}$ be the sequence of issued predictions, let
    $\tilde p : \mathbb{N} \to \mathbb{R}$ be the sequence of internal look-ahead predictions,
    and let $i : \mathbb{N} \to \mathbb{N}$ record the index chosen at each round. The tuple
    $(y, p, \tilde p, i)$ is a run of Algorithm 1 (\textsf{AOSA}) with parameter $m$ over $T$
    rounds if $m \geq 1$ and, for every round $t < T$:
    \begin{enumerate}
      \item $y^t \in \{0,1\}$;
      \item $i^t + 1 \leq m$, so that $p_{i^t}$ and $p_{i^t+1}$ are adjacent points of $B_m$;
      \item $\alpha_{\tilde p^{1:t}}(p_{i^t}) \leq 0$ and
            $\alpha_{\tilde p^{1:t}}(p_{i^t+1}) \geq 0$, i.e. the chosen pair brackets a sign
            change of the look-ahead bias;
      \item $p^t \in \{p_{i^t}, p_{i^t+1}\}$, i.e. the issued prediction is one of the two
            bracketing grid points, chosen arbitrarily;
      \item $\tilde p^t \in \{p_{i^t}, p_{i^t+1}\}$ and
            $|\tilde p^t - y^t| \leq |p_{i^t} - y^t|$ and
            $|\tilde p^t - y^t| \leq |p_{i^t+1} - y^t|$, i.e. the look-ahead prediction is the
            bracketing grid point closest to the realized outcome.
    \end{enumerate}
    Algorithm 1 is modelled as a predicate rather than as a function because the issued
    prediction $p^t$ is chosen arbitrarily among the two bracketing grid points; the predicate
    captures exactly this nondeterminism, so a bound proved for every run is a guarantee of the
    algorithm against every outcome sequence. -/)
  (title := /-- A Run of Algorithm 1 (\textsf{AOSA}) -/)
  (latexEnv := "definition")]
def aosa_run (T m : ℕ) (y p pt : ℕ → ℝ) (idx : ℕ → ℕ) : Prop :=
  1 ≤ m ∧ ∀ t < T,
    (y t = 0 ∨ y t = 1) ∧
    idx t + 1 ≤ m ∧
    cond_bias t pt y (grid_point m (idx t)) ≤ 0 ∧
    0 ≤ cond_bias t pt y (grid_point m (idx t + 1)) ∧
    (p t = grid_point m (idx t) ∨ p t = grid_point m (idx t + 1)) ∧
    (pt t = grid_point m (idx t) ∨ pt t = grid_point m (idx t + 1)) ∧
    |pt t - y t| ≤ |grid_point m (idx t) - y t| ∧
    |pt t - y t| ≤ |grid_point m (idx t + 1) - y t|

@[blueprint "lem:cal-dist-le-of-calibrated"
  (statement := /-- Let $T \in \mathbb{N}$, let $p, y, q : \mathbb{N} \to \mathbb{R}$ and suppose
    that $q^{1:T}$ is perfectly calibrated for $y^{1:T}$ in the sense of \cref{def:calibrated}.
    Then $\mathrm{CalDist}(p^{1:T}, y^{1:T}) \leq \|p^{1:T} - q^{1:T}\|_1$. -/)
  (proof := /-- By \cref{def:cal-dist}, $\mathrm{CalDist}(p^{1:T}, y^{1:T})$ is the infimum of
    the set $S = \{d : \exists q', \mathrm{ECE}(q'^{1:T}, y^{1:T}) = 0 \text{ and }
    d = \|p^{1:T} - q'^{1:T}\|_1\}$. Taking $q' = q$, which is admissible by hypothesis, shows
    $\|p^{1:T} - q^{1:T}\|_1 \in S$. Every element of $S$ is of the form $\|p^{1:T} - q'^{1:T}\|_1
    = \sum_{t=1}^{T} |p^t - q'^t| \geq 0$ by \cref{def:l1-dist}, since each summand is an absolute
    value; hence $S$ is bounded below by $0$. An infimum of a nonempty set that is bounded below
    is at most any of its members, so $\inf S \leq \|p^{1:T} - q^{1:T}\|_1$. -/)
  (title := /-- Distance to Calibration is Bounded by any Calibrated Witness -/)
  (latexEnv := "lemma")]
lemma cal_dist_le_of_calibrated (T : ℕ) (p y q : ℕ → ℝ) (hq : calibrated T q y) :
    cal_dist T p y ≤ l1_dist T p q := by
  refine csInf_le ⟨0, ?_⟩ ⟨q, hq, rfl⟩
  rintro d ⟨q', -, rfl⟩
  exact Finset.sum_nonneg fun t _ => abs_nonneg _

@[blueprint "lem:cond-avg-fibre-sum-zero"
  (statement := /-- Let $T \in \mathbb{N}$, let $p, y : \mathbb{N} \to \mathbb{R}$ and let
    $u \in \mathbb{R}$. Then the signed error accumulated by the conditional average outcome
    $\overline{y}^T(u)$ of \cref{def:cond-avg} over the fibre of rounds on which $u$ was
    predicted vanishes:
    \[ \sum_{t = 0}^{T-1} \mathbf{1}[p^t = u]\,\bigl( \overline{y}^T(u) - y^t \bigr) = 0. \] -/)
  (proof := /-- Write $S_u = \{t : 0 \leq t < T,\ p^t = u\}$ for the fibre of $u$ and
    $N_u = |S_u|$ for its cardinality. Splitting the sum over the subtraction and evaluating the
    constant sum gives
    \[ \sum_{t \in S_u} \bigl( \overline{y}^T(u) - y^t \bigr)
       = N_u \cdot \overline{y}^T(u) - \sum_{t \in S_u} y^t, \]
    and by \cref{def:cond-avg} we have $\overline{y}^T(u) = \bigl(\sum_{t \in S_u} y^t\bigr)/N_u$,
    so the right-hand side equals $N_u \cdot \bigl(\sum_{t \in S_u} y^t\bigr)/N_u
    - \sum_{t \in S_u} y^t$. We distinguish two cases according to whether $u$ is predicted at
    some round before $T$. If $N_u = 0$, then $S_u = \emptyset$, both sums are empty and the
    expression is $0 - 0 = 0$. If $N_u \neq 0$, then $N_u \neq 0$ as a real number as well, hence
    $N_u \cdot \bigl(\sum_{t \in S_u} y^t\bigr)/N_u = \sum_{t \in S_u} y^t$ and the difference is
    again $0$. -/)
  (title := /-- The Conditional Average Cancels the Outcomes on its Own Fibre -/)
  (latexEnv := "lemma")]
lemma cond_avg_fibre_sum_zero (T : ℕ) (p y : ℕ → ℝ) (u : ℝ) :
    ∑ t ∈ (Finset.range T).filter (fun t => p t = u), (cond_avg T p y u - y t) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, cond_avg]
  by_cases h : ((Finset.range T).filter (fun t => p t = u)).card = 0
  · rw [Finset.card_eq_zero] at h
    rw [h]
    simp
  · rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr h), sub_self]

@[blueprint "lem:cond-avg-inner-sum-zero"
  (statement := /-- Let $T \in \mathbb{N}$, let $p, y : \mathbb{N} \to \mathbb{R}$ and let
    $v \in \mathbb{R}$. Define $q^t = \overline{y}^T(p^t)$ using the conditional average outcome
    of \cref{def:cond-avg}. Then the inner sum of \cref{def:ece} attached to the value $v$
    vanishes:
    \[ \sum_{t = 0}^{T-1} \mathbf{1}[q^t = v]\,(q^t - y^t) = 0. \] -/)
  (proof := /-- Let $A_v = \{t : 0 \leq t < T,\ q^t = v\}$ be the index set of the sum. Every
    $t \in A_v$ satisfies $t < T$, so $p^t$ lies in the image $p(\{0, \dots, T-1\})$, which is a
    finite set of reals. Grouping the rounds of $A_v$ according to the value of $p^t$ therefore
    decomposes the sum into fibres:
    \[ \sum_{t \in A_v} (q^t - y^t)
       = \sum_{u \in p(\{0,\dots,T-1\})} \ \sum_{t \in A_v,\ p^t = u} (q^t - y^t). \]
    It suffices to prove that each inner summand vanishes, so fix $u$ in the image of $p$. We
    distinguish two cases according to the value of $\overline{y}^T(u)$.

    If $\overline{y}^T(u) \neq v$, the index set $\{t \in A_v : p^t = u\}$ is empty: for such a
    $t$ we would have $q^t = \overline{y}^T(p^t) = \overline{y}^T(u)$ and simultaneously
    $q^t = v$, contradicting $\overline{y}^T(u) \neq v$. An empty sum is $0$.

    If $\overline{y}^T(u) = v$, then $\{t \in A_v : p^t = u\}$ is exactly the full fibre
    $\{t : 0 \leq t < T,\ p^t = u\}$: the inclusion from left to right is immediate, and
    conversely any $t < T$ with $p^t = u$ satisfies $q^t = \overline{y}^T(u) = v$, so it lies in
    $A_v$. On that fibre $p^t = u$, hence $q^t = \overline{y}^T(u)$, and the sum becomes
    $\sum_{t < T,\ p^t = u} \bigl( \overline{y}^T(u) - y^t \bigr)$, which is $0$ by
    \cref{lem:cond-avg-fibre-sum-zero}. -/)
  (title := /-- Each Value Contributes No Bias to the Conditional-Average Sequence -/)
  (latexEnv := "lemma")]
lemma cond_avg_inner_sum_zero (T : ℕ) (p y : ℕ → ℝ) (v : ℝ) :
    ∑ t ∈ (Finset.range T).filter (fun t => cond_avg T p y (p t) = v),
      (cond_avg T p y (p t) - y t) = 0 := by
  rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.range T).image p)
    (fun t ht => Finset.mem_image_of_mem p (Finset.mem_filter.mp ht).1)]
  refine Finset.sum_eq_zero fun u _ => ?_
  by_cases hv : cond_avg T p y u = v
  · have hset : (((Finset.range T).filter (fun t => cond_avg T p y (p t) = v)).filter
        (fun t => p t = u)) = (Finset.range T).filter (fun t => p t = u) := by
      ext t
      simp only [Finset.mem_filter, and_assoc]
      constructor
      · rintro ⟨ht, -, htu⟩
        exact ⟨ht, htu⟩
      · rintro ⟨ht, htu⟩
        exact ⟨ht, by rw [htu]; exact hv, htu⟩
    rw [hset, ← cond_avg_fibre_sum_zero T p y u]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [(Finset.mem_filter.mp ht).2]
  · refine Finset.sum_eq_zero fun t ht => ?_
    simp only [Finset.mem_filter] at ht
    exact absurd (by rw [← ht.2]; exact ht.1.2) hv

@[blueprint "lem:cond-avg-calibrated"
  (statement := /-- Let $T \in \mathbb{N}$ and let $p, y : \mathbb{N} \to \mathbb{R}$. Define the
    sequence $q^{1:T}$ by $q^t = \overline{y}^T(p^t)$, the conditional average outcome of
    \cref{def:cond-avg} evaluated at the prediction issued at round $t$. Then $q^{1:T}$ is
    perfectly calibrated for $y^{1:T}$, that is, $\mathrm{ECE}(q^{1:T}, y^{1:T}) = 0$. -/)
  (proof := /-- By \cref{def:calibrated} the claim is $\mathrm{ECE}(q^{1:T}, y^{1:T}) = 0$, and by
    \cref{def:ece} this expected calibration error is the sum, over the values $v$ attained by
    $q^{1:T}$, of the absolute values $\bigl| \sum_{t=0}^{T-1} \mathbf{1}[q^t = v]\,(q^t - y^t)
    \bigr|$. A finite sum vanishes as soon as each of its terms vanishes, so it suffices to fix
    such a value $v$ and to show that the corresponding term is $0$. By
    \cref{lem:cond-avg-inner-sum-zero} the inner sum $\sum_{t=0}^{T-1} \mathbf{1}[q^t = v]\,
    (q^t - y^t)$ is $0$, and $|0| = 0$, so the term vanishes as required. -/)
  (title := /-- The Conditional-Average Sequence is Perfectly Calibrated -/)
  (latexEnv := "lemma")]
lemma cond_avg_calibrated (T : ℕ) (p y : ℕ → ℝ) :
    calibrated T (fun t => cond_avg T p y (p t)) y := by
  unfold calibrated ece
  exact Finset.sum_eq_zero fun v _ => by rw [cond_avg_inner_sum_zero T p y v, abs_zero]

@[blueprint "lem:cond-avg-mul-card"
  (statement := /-- Let $T \in \mathbb{N}$, let $p, y : \mathbb{N} \to \mathbb{R}$ and let
    $v \in \mathbb{R}$. Write $N_v = |\{t < T : p^t = v\}|$ for the number of rounds before $T$
    on which the value $v$ was predicted. Then
    \[ N_v \cdot \overline{y}^T(v) = \sum_{t < T,\ p^t = v} y^t, \]
    where $\overline{y}^T(v)$ is the conditional average outcome of \cref{def:cond-avg}. -/)
  (proof := /-- We distinguish two cases according to whether $N_v$ vanishes.
    If $N_v = 0$, then the set $\{t < T : p^t = v\}$ is empty, so the right-hand side is an empty
    sum and equals $0$, while the left-hand side is $0 \cdot \overline{y}^T(v) = 0$; both sides
    agree. If $N_v \neq 0$, then $N_v \neq 0$ as a real number, and by \cref{def:cond-avg} we have
    $\overline{y}^T(v) = \left(\sum_{t < T,\ p^t = v} y^t\right) / N_v$. Hence
    $N_v \cdot \overline{y}^T(v)
      = \left(\sum_{t < T,\ p^t = v} y^t\right) / N_v \cdot N_v
      = \sum_{t < T,\ p^t = v} y^t$, the last step being cancellation of the nonzero factor
    $N_v$. -/)
  (title := /-- The Conditional Average Times the Fibre Cardinality is the Fibre Sum -/)
  (latexEnv := "lemma")]
lemma cond_avg_mul_card (T : ℕ) (p y : ℕ → ℝ) (v : ℝ) :
    ((((Finset.range T).filter (fun t => p t = v)).card : ℝ)) * cond_avg T p y v
      = ∑ t ∈ (Finset.range T).filter (fun t => p t = v), y t := by
  by_cases h : ((Finset.range T).filter (fun t => p t = v)).card = 0
  · have hempty : (Finset.range T).filter (fun t => p t = v) = ∅ :=
      Finset.card_eq_zero.mp h
    rw [h, hempty]
    simp
  · have hne : ((((Finset.range T).filter (fun t => p t = v)).card : ℝ)) ≠ 0 :=
      Nat.cast_ne_zero.mpr h
    rw [cond_avg, mul_comm, div_mul_cancel₀ _ hne]

@[blueprint "lem:fiber-card-mul-abs-sub-cond-avg"
  (statement := /-- Let $T \in \mathbb{N}$, let $p, y : \mathbb{N} \to \mathbb{R}$ and let
    $v \in \mathbb{R}$. Write $N_v = |\{t < T : p^t = v\}|$. Then
    \[ N_v \cdot \left| v - \overline{y}^T(v) \right|
        = \left| \sum_{t < T,\ p^t = v} (p^t - y^t) \right|, \]
    where $\overline{y}^T(v)$ is the conditional average outcome of \cref{def:cond-avg}. -/)
  (proof := /-- On the fibre $\{t < T : p^t = v\}$ every summand $p^t$ equals $v$, so
    $\sum_{t < T,\ p^t = v} p^t = N_v \cdot v$. By \cref{lem:cond-avg-mul-card} we also have
    $N_v \cdot \overline{y}^T(v) = \sum_{t < T,\ p^t = v} y^t$. Subtracting the second identity
    from the first and distributing the sum over the difference gives
    \[ N_v \cdot \left( v - \overline{y}^T(v) \right)
        = \sum_{t < T,\ p^t = v} p^t - \sum_{t < T,\ p^t = v} y^t
        = \sum_{t < T,\ p^t = v} (p^t - y^t). \]
    Taking absolute values and using $|N_v \cdot x| = |N_v| \cdot |x| = N_v \cdot |x|$, which
    holds because $N_v \geq 0$, yields the claim. -/)
  (title := /-- The Fibre Contribution to the $\ell_1$ Distance Equals the Fibre Bias -/)
  (latexEnv := "lemma")]
lemma fiber_card_mul_abs_sub_cond_avg (T : ℕ) (p y : ℕ → ℝ) (v : ℝ) :
    ((((Finset.range T).filter (fun t => p t = v)).card : ℝ)) * |v - cond_avg T p y v|
      = |∑ t ∈ (Finset.range T).filter (fun t => p t = v), (p t - y t)| := by
  have hp : ∑ t ∈ (Finset.range T).filter (fun t => p t = v), p t
      = ((((Finset.range T).filter (fun t => p t = v)).card : ℝ)) * v := by
    rw [Finset.sum_congr rfl (fun t ht => (Finset.mem_filter.mp ht).2), Finset.sum_const,
      nsmul_eq_mul]
  have key : ((((Finset.range T).filter (fun t => p t = v)).card : ℝ)) * (v - cond_avg T p y v)
      = ∑ t ∈ (Finset.range T).filter (fun t => p t = v), (p t - y t) := by
    rw [mul_sub, cond_avg_mul_card, ← hp, Finset.sum_sub_distrib]
  rw [← key, abs_mul, Nat.abs_cast]

@[blueprint "lem:l1-dist-cond-avg-eq-ece"
  (statement := /-- Let $T \in \mathbb{N}$ and let $p, y : \mathbb{N} \to \mathbb{R}$. With
    $q^t = \overline{y}^T(p^t)$ the conditional-average sequence of \cref{def:cond-avg}, one has
    \[ \|p^{1:T} - q^{1:T}\|_1 = \mathrm{ECE}(p^{1:T}, y^{1:T}), \]
    where the left-hand side is the $\ell_1$ distance of \cref{def:l1-dist} and the right-hand
    side is the expected calibration error of \cref{def:ece}. No hypothesis is imposed on $p$
    or $y$; in particular they need not take values in $[0,1]$ or in $\{0,1\}$. -/)
  (proof := /-- This is the displayed computation of the source proof. Unfolding
    \cref{def:l1-dist} and \cref{def:ece}, the claim reads
    \[ \sum_{t < T} \left| p^t - \overline{y}^T(p^t) \right|
        = \sum_{v \in V} \left| \sum_{t < T,\ p^t = v} (p^t - y^t) \right|, \]
    where $V = \{p^t : t < T\}$ is the finite set of values attained by $p^{1:T}$.
    We first regroup the left-hand sum by the value of the prediction. The map $t \mapsto p^t$
    sends $\{t : t < T\}$ into $V$, so the fibrewise summation formula applies and gives
    \[ \sum_{t < T} \left| p^t - \overline{y}^T(p^t) \right|
        = \sum_{v \in V} \ \sum_{t < T,\ p^t = v} \left| p^t - \overline{y}^T(p^t) \right|. \]
    It therefore suffices to prove, for each fixed $v \in V$, that
    $\sum_{t < T,\ p^t = v} \left| p^t - \overline{y}^T(p^t) \right|
      = \left| \sum_{t < T,\ p^t = v} (p^t - y^t) \right|$.
    Fix such a $v$. Every index $t$ occurring in the inner sum satisfies $p^t = v$, so each
    summand equals the constant $\left| v - \overline{y}^T(v) \right|$; summing a constant over
    the fibre gives
    $\sum_{t < T,\ p^t = v} \left| p^t - \overline{y}^T(p^t) \right|
      = N_v \cdot \left| v - \overline{y}^T(v) \right|$, where
    $N_v = |\{t < T : p^t = v\}|$. By \cref{lem:fiber-card-mul-abs-sub-cond-avg} this last
    quantity equals $\left| \sum_{t < T,\ p^t = v} (p^t - y^t) \right|$, which is the required
    fibre identity and completes the proof. -/)
  (title := /-- The $\ell_1$ Distance to the Conditional-Average Sequence Equals the ECE -/)
  (latexEnv := "lemma")]
lemma l1_dist_cond_avg_eq_ece (T : ℕ) (p y : ℕ → ℝ) :
    l1_dist T p (fun t => cond_avg T p y (p t)) = ece T p y := by
  rw [l1_dist, ece,
    ← Finset.sum_fiberwise_of_maps_to (g := p) (t := (Finset.range T).image p)
      (fun t ht => Finset.mem_image_of_mem p ht)
      (fun t => |p t - cond_avg T p y (p t)|)]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Finset.sum_congr rfl
      (fun t ht => by rw [(Finset.mem_filter.mp ht).2] :
        ∀ t ∈ (Finset.range T).filter (fun t => p t = v),
          |p t - cond_avg T p y (p t)| = |v - cond_avg T p y v|),
    Finset.sum_const, nsmul_eq_mul, fiber_card_mul_abs_sub_cond_avg]

@[blueprint "lem:cal-dist-le-ece"
  (statement := /-- (Lemma 1 of the source, after \cite{qiao2024distance}.) Let
    $T \in \mathbb{N}$ be a horizon and let $p, y : \mathbb{N} \to \mathbb{R}$ be arbitrary
    real-valued sequences, read as the predictions $p^{1:T}$ and the outcomes $y^{1:T}$ over
    the first $T$ rounds; no restriction to $[0,1]$ or to $\{0,1\}$ is imposed. Then the
    distance to calibration of \cref{def:cal-dist} is bounded by the expected calibration
    error of \cref{def:ece}, that is,
    \[ \mathrm{CalDist}(p^{1:T}, y^{1:T}) \leq \mathrm{ECE}(p^{1:T}, y^{1:T}). \] -/)
  (proof := /-- Consider the sequence $q^{1:T}$ defined by $q^t = \overline{y}^T(p^t)$, using the
    conditional average outcome of \cref{def:cond-avg}. By \cref{lem:cond-avg-calibrated} the
    sequence $q^{1:T}$ is perfectly calibrated for $y^{1:T}$, so
    \cref{lem:cal-dist-le-of-calibrated} applies and yields
    $\mathrm{CalDist}(p^{1:T}, y^{1:T}) \leq \|p^{1:T} - q^{1:T}\|_1$. By
    \cref{lem:l1-dist-cond-avg-eq-ece} the right-hand side equals
    $\mathrm{ECE}(p^{1:T}, y^{1:T})$, which gives the claim. -/)
  (title := /-- Distance to Calibration is Bounded by the Expected Calibration Error -/)
  (latexEnv := "lemma")]
lemma cal_dist_le_ece (T : ℕ) (p y : ℕ → ℝ) :
    cal_dist T p y ≤ ece T p y := by
  calc cal_dist T p y
      ≤ l1_dist T p (fun t => cond_avg T p y (p t)) :=
        cal_dist_le_of_calibrated T p y _ (cond_avg_calibrated T p y)
    _ = ece T p y := l1_dist_cond_avg_eq_ece T p y

@[blueprint "lem:calibrated-self"
  (statement := /-- Let $T \in \mathbb{N}$ and let $y : \mathbb{N} \to \mathbb{R}$. Then the
    outcome sequence $y^{1:T}$ is perfectly calibrated for itself in the sense of
    \cref{def:calibrated}, that is, $\mathrm{ECE}(y^{1:T}, y^{1:T}) = 0$. In particular the set
    $\mathcal{C}(y^{1:T})$ of perfectly calibrated sequences is nonempty. -/)
  (proof := /-- By \cref{def:ece} we have
    \[ \mathrm{ECE}(y^{1:T}, y^{1:T})
        = \sum_{v \in V} \left| \sum_{t = 0}^{T-1} \mathbf{1}[y^t = v]\,(y^t - y^t) \right|, \]
    where $V$ is the set of values attained by $y^{1:T}$. For every round $t$ the summand
    $y^t - y^t$ equals $0$, so each inner sum is a sum of zeros and hence equals $0$; its absolute
    value is therefore $0$ as well. The outer sum is thus a sum of zeros over $V$ and equals $0$,
    which by \cref{def:calibrated} is exactly the assertion that $y^{1:T}$ is perfectly calibrated
    for $y^{1:T}$. -/)
  (title := /-- An Outcome Sequence Is Perfectly Calibrated for Itself -/)
  (latexEnv := "lemma")]
lemma calibrated_self (T : ℕ) (y : ℕ → ℝ) : calibrated T y y := by
  simp [calibrated, ece]

@[blueprint "lem:l1-dist-triangle"
  (statement := /-- Let $T \in \mathbb{N}$ and let $p, \tilde p, q : \mathbb{N} \to \mathbb{R}$.
    Then the $\ell_1$ distance of \cref{def:l1-dist} satisfies the triangle inequality
    \[ \|p^{1:T} - q^{1:T}\|_1
        \leq \|p^{1:T} - \tilde p^{1:T}\|_1 + \|\tilde p^{1:T} - q^{1:T}\|_1. \] -/)
  (proof := /-- By \cref{def:l1-dist} all three quantities are sums over the rounds
    $t \in \{0, \dots, T-1\}$, and the right-hand side may be written as the single sum
    $\sum_{t=0}^{T-1} \bigl( |p^t - \tilde p^t| + |\tilde p^t - q^t| \bigr)$. It therefore suffices
    to compare the two sums termwise. For a fixed round $t$ the triangle inequality for the
    absolute value on $\mathbb{R}$, applied to $p^t - q^t = (p^t - \tilde p^t) +
    (\tilde p^t - q^t)$, gives $|p^t - q^t| \leq |p^t - \tilde p^t| + |\tilde p^t - q^t|$. Summing
    these termwise inequalities over $t \in \{0, \dots, T-1\}$ yields the claim. -/)
  (title := /-- Triangle Inequality for the $\ell_1$ Distance -/)
  (latexEnv := "lemma")]
lemma l1_dist_triangle (T : ℕ) (p pt q : ℕ → ℝ) :
    l1_dist T p q ≤ l1_dist T p pt + l1_dist T pt q := by
  rw [l1_dist, l1_dist, l1_dist, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun t _ => abs_sub_le _ _ _

@[blueprint "lem:cal-dist-le-shift"
  (statement := /-- Let $T \in \mathbb{N}$ and let $p, \tilde p, y : \mathbb{N} \to \mathbb{R}$.
    Then
    \[ \mathrm{CalDist}(p^{1:T}, y^{1:T})
        \leq \mathrm{CalDist}(\tilde p^{1:T}, y^{1:T}) + \|p^{1:T} - \tilde p^{1:T}\|_1. \] -/)
  (proof := /-- The claim is equivalent, by moving the summand $\|p^{1:T} - \tilde p^{1:T}\|_1$ to
    the left-hand side, to the inequality
    \[ \mathrm{CalDist}(p^{1:T}, y^{1:T}) - \|p^{1:T} - \tilde p^{1:T}\|_1
        \leq \mathrm{CalDist}(\tilde p^{1:T}, y^{1:T}), \]
    and by \cref{def:cal-dist} the right-hand side is the infimum of the set
    $S = \{ \|\tilde p^{1:T} - q^{1:T}\|_1 : q^{1:T} \in \mathcal{C}(y^{1:T}) \}$. A real number is
    at most the infimum of a nonempty set as soon as it is a lower bound of that set, so it
    suffices to prove two things: that $S$ is nonempty, and that
    $\mathrm{CalDist}(p^{1:T}, y^{1:T}) - \|p^{1:T} - \tilde p^{1:T}\|_1$ is a lower bound of $S$.
    For nonemptiness, the outcome sequence $y^{1:T}$ itself lies in $\mathcal{C}(y^{1:T})$ by
    \cref{lem:calibrated-self}, so $\|\tilde p^{1:T} - y^{1:T}\|_1 \in S$.
    For the lower bound, let $q^{1:T} \in \mathcal{C}(y^{1:T})$ be arbitrary, so that the
    corresponding element of $S$ is $\|\tilde p^{1:T} - q^{1:T}\|_1$. Since $q^{1:T}$ is perfectly
    calibrated for $y^{1:T}$, \cref{lem:cal-dist-le-of-calibrated} gives
    $\mathrm{CalDist}(p^{1:T}, y^{1:T}) \leq \|p^{1:T} - q^{1:T}\|_1$, and
    \cref{lem:l1-dist-triangle} gives
    $\|p^{1:T} - q^{1:T}\|_1 \leq \|p^{1:T} - \tilde p^{1:T}\|_1 + \|\tilde p^{1:T} - q^{1:T}\|_1$.
    Chaining these two inequalities and subtracting $\|p^{1:T} - \tilde p^{1:T}\|_1$ from both
    sides yields
    $\mathrm{CalDist}(p^{1:T}, y^{1:T}) - \|p^{1:T} - \tilde p^{1:T}\|_1
     \leq \|\tilde p^{1:T} - q^{1:T}\|_1$, as required. Hence the infimum bound holds and the
    stated inequality follows. -/)
  (title := /-- Distance to Calibration Changes by at Most the $\ell_1$ Perturbation -/)
  (latexEnv := "lemma")]
lemma cal_dist_le_shift (T : ℕ) (p pt y : ℕ → ℝ) :
    cal_dist T p y ≤ cal_dist T pt y + l1_dist T p pt := by
  rw [← sub_le_iff_le_add]
  refine le_csInf ⟨l1_dist T pt y, y, calibrated_self T y, rfl⟩ ?_
  rintro d ⟨q, hq, rfl⟩
  have h1 : cal_dist T p y ≤ l1_dist T p q := cal_dist_le_of_calibrated T p y q hq
  have h2 : l1_dist T p q ≤ l1_dist T p pt + l1_dist T pt q := l1_dist_triangle T p pt q
  linarith

@[blueprint "lem:abs-add-le-max-of-mul-nonpos"
  (statement := /-- Let $a, b \in \mathbb{R}$ satisfy $a \cdot b \leq 0$, that is, at least one of
    $a$ and $b$ is zero or the two have strictly opposite signs. Then
    $|a + b| \leq \max\{|a|, |b|\}$. -/)
  (proof := /-- Write $M = \max\{|a|, |b|\}$, so that $|a| \leq M$ and $|b| \leq M$, and recall the
    elementary bounds $-|a| \leq a \leq |a|$ and $-|b| \leq b \leq |b|$. The conclusion
    $|a + b| \leq M$ is equivalent to the pair of inequalities $-M \leq a + b$ and $a + b \leq M$,
    so it suffices to establish both. The hypothesis $ab \leq 0$ forces one of the two cases
    $0 \leq a$ and $b \leq 0$, or $a \leq 0$ and $0 \leq b$, since a product of two strictly
    positive numbers or of two strictly negative numbers is strictly positive.
    In the first case, $0 \leq a$ and $b \leq 0$, we get $a + b \leq a \leq |a| \leq M$ from
    $b \leq 0$, and $-M \leq -|b| \leq b \leq a + b$ from $0 \leq a$. In the second case,
    $a \leq 0$ and $0 \leq b$, we get $a + b \leq b \leq |b| \leq M$ from $a \leq 0$, and
    $-M \leq -|a| \leq a \leq a + b$ from $0 \leq b$. In both cases the two required inequalities
    hold, whence $|a + b| \leq \max\{|a|, |b|\}$. -/)
  (title := /-- Cancellation Bound for Terms of Opposite Sign -/)
  (latexEnv := "lemma")]
lemma abs_add_le_max_of_mul_nonpos (a b : ℝ) (hab : a * b ≤ 0) :
    |a + b| ≤ max |a| |b| := by
  have hamax : |a| ≤ max |a| |b| := le_max_left _ _
  have hbmax : |b| ≤ max |a| |b| := le_max_right _ _
  have hane := neg_abs_le a
  have hale := le_abs_self a
  have hbne := neg_abs_le b
  have hble := le_abs_self b
  rcases mul_nonpos_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [abs_le] <;>
    constructor <;> linarith

@[blueprint "lem:abs-grid-point-sub-outcome-le-one"
  (statement := /-- Let $m, i \in \mathbb{N}$ with $1 \leq m$ and $i \leq m$, and let
    $y \in \mathbb{R}$ with $y = 0$ or $y = 1$. Then $|p_i - y| \leq 1$, where $p_i = i/m$ is the
    grid point of \cref{def:grid-point}. -/)
  (proof := /-- Since $1 \leq m$ we have $m > 0$, so $p_i = i/m \geq 0$; and since $i \leq m$ we
    have $i/m \leq m/m = 1$. Thus $p_i \in [0,1]$. If $y = 0$ then
    $|p_i - y| = |p_i| = p_i \leq 1$. If $y = 1$ then $|p_i - y| = |p_i - 1| = 1 - p_i \leq 1$,
    using $p_i \geq 0$. In both cases $|p_i - y| \leq 1$. -/)
  (title := /-- Grid Points Are Within Distance One of a Binary Outcome -/)
  (latexEnv := "lemma")]
lemma abs_grid_point_sub_outcome_le_one (m i : ℕ) (hm : 1 ≤ m) (hi : i ≤ m) (yv : ℝ)
    (hy : yv = 0 ∨ yv = 1) : |grid_point m i - yv| ≤ 1 := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have h0 : 0 ≤ grid_point m i := div_nonneg (Nat.cast_nonneg i) hm0.le
  have h1 : grid_point m i ≤ 1 := by
    rw [grid_point, div_le_one hm0]
    exact_mod_cast hi
  rcases hy with rfl | rfl <;> rw [abs_le] <;> constructor <;> linarith

@[blueprint "lem:cond-bias-succ"
  (statement := /-- Let $t \in \mathbb{N}$, let $\tilde p, y : \mathbb{N} \to \mathbb{R}$ and let
    $v \in \mathbb{R}$. If $\tilde p^t = v$ then
    $\alpha_{\tilde p^{1:t+1}}(v) = \alpha_{\tilde p^{1:t}}(v) + (v - y^t)$, and if
    $\tilde p^t \neq v$ then $\alpha_{\tilde p^{1:t+1}}(v) = \alpha_{\tilde p^{1:t}}(v)$, where
    $\alpha$ is the conditional bias of \cref{def:cond-bias}. -/)
  (proof := /-- By \cref{def:cond-bias}, $\alpha_{\tilde p^{1:t}}(v)$ is the sum of
    $\tilde p^s - y^s$ over those $s < t$ with $\tilde p^s = v$. Rewriting each such sum over a
    filtered index set as the sum of the indicator-weighted terms
    $\mathbf{1}[\tilde p^s = v]\,(\tilde p^s - y^s)$ over all $s < t$, and then splitting off the
    last index of $\{s : s < t+1\}$, gives
    \[ \alpha_{\tilde p^{1:t+1}}(v)
        = \alpha_{\tilde p^{1:t}}(v)
          + \mathbf{1}[\tilde p^t = v]\,(\tilde p^t - y^t). \]
    It remains to identify the last term in each of the two exhaustive cases. If
    $\tilde p^t = v$, the indicator equals $1$ and substituting $\tilde p^t = v$ in the increment
    turns it into $v - y^t$, so both sides reduce to
    $\alpha_{\tilde p^{1:t}}(v) + (v - y^t)$. If $\tilde p^t \neq v$, both indicators vanish, so
    both sides reduce to $\alpha_{\tilde p^{1:t}}(v)$. In either case the claimed identity
    holds. -/)
  (title := /-- One-Round Recurrence for the Conditional Bias -/)
  (latexEnv := "lemma")]
lemma cond_bias_succ (t : ℕ) (pt y : ℕ → ℝ) (v : ℝ) :
    cond_bias (t + 1) pt y v =
      cond_bias t pt y v + (if pt t = v then v - y t else 0) := by
  simp only [cond_bias, Finset.sum_filter, Finset.sum_range_succ]
  rcases eq_or_ne (pt t) v with h | h
  · rw [if_pos h, if_pos h, h]
  · rw [if_neg h, if_neg h]

@[blueprint "lem:grid-point-lt-succ"
  (statement := /-- Let $m, i \in \mathbb{N}$ with $m \geq 1$. Then the grid points of
    \cref{def:grid-point} satisfy $p_i < p_{i+1}$. -/)
  (proof := /-- By \cref{def:grid-point} the assertion reads $i/m < (i+1)/m$. From $m \geq 1$ we
    get $0 < m$ as a real number, so division by $m$ is strictly monotone and the assertion is
    equivalent to $i < i + 1$, which holds for every $i \in \mathbb{N}$. -/)
  (title := /-- Adjacent Grid Points Are Strictly Increasing -/)
  (latexEnv := "lemma")]
lemma grid_point_lt_succ (m i : ℕ) (hm : 1 ≤ m) :
    grid_point m i < grid_point m (i + 1) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [grid_point, grid_point, div_lt_div_iff_of_pos_right hm0]
  push_cast
  linarith

@[blueprint "lem:lower-grid-increment-nonneg"
  (statement := /-- Let $a, b, y \in \mathbb{R}$ satisfy $0 \leq a$, $a < b$ and $b \leq 1$, and
    let $y \in \{0,1\}$. If $|a - y| \leq |b - y|$, then $0 \leq a - y$. -/)
  (proof := /-- Since $y \in \{0,1\}$, two cases arise. If $y = 0$, then $a - y = a \geq 0$ by
    hypothesis. If $y = 1$, then $a - 1 \leq 0$ because $a < b$ and $b \leq 1$, and $b - 1 \leq 0$
    because $b \leq 1$; hence $|a - 1| = -(a - 1)$ and $|b - 1| = -(b - 1)$, so the hypothesis
    $|a - y| \leq |b - y|$ becomes $-(a - 1) \leq -(b - 1)$, that is $b \leq a$. Together with
    $a < b$ this is contradictory, so the hypotheses of this case are inconsistent and the
    conclusion $0 \leq a - y$ follows from them. -/)
  (title := /-- The Lower Bracketing Point Does Not Undershoot the Outcome -/)
  (latexEnv := "lemma")]
lemma lower_grid_increment_nonneg (a b yv : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hy : yv = 0 ∨ yv = 1) (hd : |a - yv| ≤ |b - yv|) : 0 ≤ a - yv := by
  rcases hy with rfl | rfl
  · linarith
  · have h1 : a - 1 ≤ 0 := by linarith
    have h2 : b - 1 ≤ 0 := by linarith
    rw [abs_of_nonpos h1, abs_of_nonpos h2] at hd
    linarith

@[blueprint "lem:upper-grid-increment-nonpos"
  (statement := /-- Let $a, b, y \in \mathbb{R}$ satisfy $0 \leq a$, $a < b$ and $b \leq 1$, and
    let $y \in \{0,1\}$. If $|b - y| \leq |a - y|$, then $b - y \leq 0$. -/)
  (proof := /-- Since $y \in \{0,1\}$, two cases arise. If $y = 1$, then $b - y = b - 1 \leq 0$
    because $b \leq 1$. If $y = 0$, then $b - 0 \geq 0$ because $0 \leq a$ and $a < b$, and
    $a - 0 \geq 0$ by hypothesis; hence $|b - 0| = b - 0$ and $|a - 0| = a - 0$, so the hypothesis
    $|b - y| \leq |a - y|$ becomes $b \leq a$. Together with $a < b$ this is contradictory, so the
    hypotheses of this case are inconsistent and the conclusion $b - y \leq 0$ follows from
    them. -/)
  (title := /-- The Upper Bracketing Point Does Not Overshoot the Outcome -/)
  (latexEnv := "lemma")]
lemma upper_grid_increment_nonpos (a b yv : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hy : yv = 0 ∨ yv = 1) (hd : |b - yv| ≤ |a - yv|) : b - yv ≤ 0 := by
  rcases hy with rfl | rfl
  · have h1 : 0 ≤ b - 0 := by linarith
    have h2 : 0 ≤ a - 0 := by linarith
    rw [abs_of_nonneg h1, abs_of_nonneg h2] at hd
    linarith
  · linarith

@[blueprint "lem:lookahead-sign-opposes"
  (statement := /-- Let $T, m \in \mathbb{N}$ and let $(y, p, \tilde p, i)$ be a run of Algorithm 1
    in the sense of \cref{def:aosa-run}. Let $t < T$ and set $v = \tilde p^t$, the look-ahead
    prediction issued at round $t$. Then
    \[ \alpha_{\tilde p^{1:t}}(v) \cdot (v - y^t) \leq 0, \]
    where $\alpha$ is the conditional bias of \cref{def:cond-bias}; that is, the bias accumulated
    at $v$ over the rounds before $t$ and the new increment $v - y^t$ are never both nonzero of
    the same sign. -/)
  (proof := /-- This is the source proof's claim that $\alpha_{\tilde p^{1:t-1}}(p_i)$ and
    $p_i - y^t$ either take the value $0$ or differ in sign, which the source asserts by
    inspecting the two possible cases of Algorithm 1. Write $i = i^t$, $a = p_i$ and
    $b = p_{i+1}$. Unfolding \cref{def:aosa-run} at the round $t < T$ gives $m \geq 1$ together
    with $y^t \in \{0,1\}$, $i + 1 \leq m$, $\alpha_{\tilde p^{1:t}}(a) \leq 0$,
    $0 \leq \alpha_{\tilde p^{1:t}}(b)$, $v = \tilde p^t \in \{a, b\}$,
    $|v - y^t| \leq |a - y^t|$ and $|v - y^t| \leq |b - y^t|$.

    We first record the three facts about the bracketing pair that both cases use. Since
    $m \geq 1$ we have $m > 0$ as a real number, so $a = i/m \geq 0$ by \cref{def:grid-point}
    because $i \geq 0$; also $b = (i+1)/m \leq 1$ by \cref{def:grid-point} because
    $i + 1 \leq m$; and $a < b$ by \cref{lem:grid-point-lt-succ}, whose hypothesis $m \geq 1$
    holds.

    Suppose first $v = a$. Substituting $v = a$ in the distance inequality
    $|v - y^t| \leq |b - y^t|$ gives $|a - y^t| \leq |b - y^t|$, so
    \cref{lem:lower-grid-increment-nonneg}, applied with the facts $0 \leq a$, $a < b$, $b \leq 1$
    and $y^t \in \{0,1\}$, yields $0 \leq a - y^t$. Since $\alpha_{\tilde p^{1:t}}(a) \leq 0$, the
    product of a nonpositive and a nonnegative real is nonpositive, so
    $\alpha_{\tilde p^{1:t}}(v) \cdot (v - y^t) \leq 0$.

    Suppose now $v = b$. Substituting $v = b$ in the distance inequality
    $|v - y^t| \leq |a - y^t|$ gives $|b - y^t| \leq |a - y^t|$, so
    \cref{lem:upper-grid-increment-nonpos}, applied with the same four facts, yields
    $b - y^t \leq 0$. Since $0 \leq \alpha_{\tilde p^{1:t}}(b)$, the product of a nonnegative and
    a nonpositive real is nonpositive, so $\alpha_{\tilde p^{1:t}}(v) \cdot (v - y^t) \leq 0$.
    As $v \in \{a, b\}$, these two cases are exhaustive. -/)
  (title := /-- The Look-Ahead Update Opposes the Accumulated Bias -/)
  (latexEnv := "lemma")]
lemma lookahead_sign_opposes (T m : ℕ) (y p pt : ℕ → ℝ) (idx : ℕ → ℕ)
    (hrun : aosa_run T m y p pt idx) (t : ℕ) (ht : t < T) :
    cond_bias t pt y (pt t) * (pt t - y t) ≤ 0 := by
  obtain ⟨hm, hstep⟩ := hrun
  obtain ⟨hy, hidx, hlo, hhi, -, hpt, hd1, hd2⟩ := hstep t ht
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have ha0 : (0 : ℝ) ≤ grid_point m (idx t) := div_nonneg (Nat.cast_nonneg _) hm0.le
  have hb1 : grid_point m (idx t + 1) ≤ 1 := by
    rw [grid_point, div_le_one hm0]
    exact_mod_cast hidx
  have hab : grid_point m (idx t) < grid_point m (idx t + 1) := grid_point_lt_succ m (idx t) hm
  rcases hpt with h | h
  · rw [h] at hd2 ⊢
    exact mul_nonpos_of_nonpos_of_nonneg hlo
      (lower_grid_increment_nonneg _ _ _ ha0 hab hb1 hy hd2)
  · rw [h] at hd1 ⊢
    exact mul_nonpos_of_nonneg_of_nonpos hhi
      (upper_grid_increment_nonpos _ _ _ ha0 hab hb1 hy hd1)

@[blueprint "lem:cond-bias-abs-le-one"
  (statement := /-- Let $T, m \in \mathbb{N}$ and let $(y, p, \tilde p, i)$ be a run of Algorithm 1
    in the sense of \cref{def:aosa-run}. Then for every $t \leq T$ and every grid index
    $j \leq m$,
    \[ \left| \alpha_{\tilde p^{1:t}}(p_j) \right| \leq 1, \]
    where $\alpha_{\tilde p^{1:t}}$ is the conditional bias of \cref{def:cond-bias} taken along
    the look-ahead sequence $\tilde p$ and $p_j = j/m$ is the grid point of
    \cref{def:grid-point}. -/)
  (proof := /-- Fix a grid index $j \leq m$ and induct on $t$. For $t = 0$ the index set of
    \cref{def:cond-bias} is empty, so $\alpha_{\tilde p^{1:0}}(p_j) = 0$ and the bound holds.

    For the inductive step, let $t \in \mathbb{N}$ with $t + 1 \leq T$ and assume, as induction
    hypothesis, that $|\alpha_{\tilde p^{1:t}}(p_j)| \leq 1$ holds whenever $t \leq T$; since
    $t + 1 \leq T$ we have $t < T$, so the hypothesis is available and the round $t$ data of
    \cref{def:aosa-run} may be used. By \cref{lem:cond-bias-succ},
    if $\tilde p^t \neq p_j$ then $\alpha_{\tilde p^{1:t+1}}(p_j) = \alpha_{\tilde p^{1:t}}(p_j)$
    and the bound is inherited unchanged. Otherwise $\tilde p^t = p_j$ and
    \cref{lem:cond-bias-succ} gives
    $\alpha_{\tilde p^{1:t+1}}(p_j) = \alpha_{\tilde p^{1:t}}(p_j) + (p_j - y^t)$. By
    \cref{lem:lookahead-sign-opposes} applied at the round $t < T$, the look-ahead value
    $v = \tilde p^t$ satisfies $\alpha_{\tilde p^{1:t}}(v) \cdot (v - y^t) \leq 0$; substituting
    $\tilde p^t = p_j$ this reads
    $\alpha_{\tilde p^{1:t}}(p_j) \cdot (p_j - y^t) \leq 0$, so
    \cref{lem:abs-add-le-max-of-mul-nonpos} yields
    \[ \left| \alpha_{\tilde p^{1:t+1}}(p_j) \right|
        \leq \max\left\{ \left| \alpha_{\tilde p^{1:t}}(p_j) \right|, |p_j - y^t| \right\}. \]
    The first entry is at most $1$ by the induction hypothesis. The second is at most $1$ by
    \cref{lem:abs-grid-point-sub-outcome-le-one}, whose hypotheses hold because $1 \leq m$ and
    $y^t \in \{0,1\}$ by \cref{def:aosa-run} and because $j \leq m$ by assumption. Hence the
    maximum is at most $1$, completing the induction. -/)
  (title := /-- Every Grid Point Accumulates Bias at Most One in Absolute Value -/)
  (latexEnv := "lemma")]
lemma cond_bias_abs_le_one (T m : ℕ) (y p pt : ℕ → ℝ) (idx : ℕ → ℕ)
    (hrun : aosa_run T m y p pt idx) (t : ℕ) (ht : t ≤ T) (j : ℕ) (hj : j ≤ m) :
    |cond_bias t pt y (grid_point m j)| ≤ 1 := by
  have hm : 1 ≤ m := hrun.1
  induction t with
  | zero => simp [cond_bias]
  | succ t ih =>
    have htT : t < T := by omega
    have hyt : y t = 0 ∨ y t = 1 := (hrun.2 t htT).1
    have hincr : |grid_point m j - y t| ≤ 1 :=
      abs_grid_point_sub_outcome_le_one m j hm hj (y t) hyt
    rw [cond_bias_succ]
    rcases eq_or_ne (pt t) (grid_point m j) with h | h
    · rw [if_pos h]
      refine (abs_add_le_max_of_mul_nonpos _ _ ?_).trans (max_le (ih htT.le) hincr)
      have hsign := lookahead_sign_opposes T m y p pt idx hrun t htT
      rwa [h] at hsign
    · rw [if_neg h, add_zero]
      exact ih htT.le

@[blueprint "lem:lookahead-values-on-grid"
  (statement := /-- Let $T, m \in \mathbb{N}$ and let $(y, p, \tilde p, i)$ be a run of Algorithm 1
    in the sense of \cref{def:aosa-run}. Then every value attained by $\tilde p^{1:T}$ is a grid
    point $p_j$ with $j \leq m$; formally, the image of $\{0,\dots,T-1\}$ under $\tilde p$ is
    contained in the image of $\{0,\dots,m\}$ under $j \mapsto p_j$. The same holds for the issued
    predictions $p^{1:T}$. -/)
  (proof := /-- Let $t < T$. By \cref{def:aosa-run}, $\tilde p^t$ equals $p_{i^t}$ or
    $p_{i^t+1}$, and likewise $p^t$ equals $p_{i^t}$ or $p_{i^t+1}$. In either case the value is
    of the form $p_j$ with $j \in \{i^t, i^t + 1\}$, and $i^t + 1 \leq m$ by \cref{def:aosa-run},
    so $j \leq m$ in both cases. Hence each attained value lies in the image of $\{0,\dots,m\}$
    under $j \mapsto p_j$. -/)
  (title := /-- All Predictions Lie on the Grid $B_m$ -/)
  (latexEnv := "lemma")]
lemma lookahead_values_on_grid (T m : ℕ) (y p pt : ℕ → ℝ) (idx : ℕ → ℕ)
    (hrun : aosa_run T m y p pt idx) :
    (Finset.range T).image pt ⊆ (Finset.range (m + 1)).image (grid_point m) ∧
      (Finset.range T).image p ⊆ (Finset.range (m + 1)).image (grid_point m) := by
  obtain ⟨-, h⟩ := hrun
  constructor
  · intro v hv
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨-, hidx, -, -, -, hpt, -, -⟩ := h t (Finset.mem_range.mp ht)
    rcases hpt with hpt | hpt
    · exact Finset.mem_image.mpr ⟨idx t, Finset.mem_range.mpr (by omega), hpt.symm⟩
    · exact Finset.mem_image.mpr ⟨idx t + 1, Finset.mem_range.mpr (by omega), hpt.symm⟩
  · intro v hv
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨-, hidx, -, -, hp, -, -, -⟩ := h t (Finset.mem_range.mp ht)
    rcases hp with hp | hp
    · exact Finset.mem_image.mpr ⟨idx t, Finset.mem_range.mpr (by omega), hp.symm⟩
    · exact Finset.mem_image.mpr ⟨idx t + 1, Finset.mem_range.mpr (by omega), hp.symm⟩

@[blueprint "lem:ece-lookahead-le"
  (statement := /-- (Theorem 2 of the source, for the look-ahead sequence.) Let
    $T, m \in \mathbb{N}$ and let $(y, p, \tilde p, i)$ be a run of Algorithm 1 in the sense of
    \cref{def:aosa-run}. Then
    \[ \mathrm{ECE}(\tilde p^{1:T}, y^{1:T}) \leq m + 1. \] -/)
  (proof := /-- By \cref{def:ece}, $\mathrm{ECE}(\tilde p^{1:T}, y^{1:T})$ is exactly the sum of
    $|\alpha_{\tilde p^{1:T}}(v)|$, in the notation of \cref{def:cond-bias}, over the finite set
    $V$ of values $v$ attained by $\tilde p^{1:T}$, since for each such $v$ the inner sum of
    \cref{def:ece} is the conditional bias $\alpha_{\tilde p^{1:T}}(v)$.

    We first bound each summand. Let $v \in V$. By the first assertion of
    \cref{lem:lookahead-values-on-grid}, $V$ is contained in the image of $\{0,\dots,m\}$ under
    $j \mapsto p_j$, so there is an index $j \leq m$ with $v = p_j$. Applying
    \cref{lem:cond-bias-abs-le-one} with $t = T$, which is admissible since $T \leq T$ and
    $j \leq m$, gives $|\alpha_{\tilde p^{1:T}}(p_j)| \leq 1$, that is,
    $|\alpha_{\tilde p^{1:T}}(v)| \leq 1$.

    Summing this uniform bound over $V$ shows that
    $\mathrm{ECE}(\tilde p^{1:T}, y^{1:T}) \leq |V|$, the cardinality of $V$ viewed as a real
    number. Since $V$ is contained in the image of $\{0,\dots,m\}$ under $j \mapsto p_j$ by
    \cref{lem:lookahead-values-on-grid}, monotonicity of cardinality under inclusion gives
    $|V| \leq |\{p_j : j \leq m\}|$, and the image of a set under a map has at most as many
    elements as the set itself, so $|\{p_j : j \leq m\}| \leq m + 1$ because $\{0,\dots,m\}$ has
    $m + 1$ elements. Chaining these three inequalities yields
    $\mathrm{ECE}(\tilde p^{1:T}, y^{1:T}) \leq m + 1$. -/)
  (title := /-- The Look-Ahead Sequence Has Expected Calibration Error at Most $m+1$ -/)
  (latexEnv := "lemma")]
lemma ece_lookahead_le (T m : ℕ) (y p pt : ℕ → ℝ) (idx : ℕ → ℕ)
    (hrun : aosa_run T m y p pt idx) :
    ece T pt y ≤ (m : ℝ) + 1 := by
  have hsub := (lookahead_values_on_grid T m y p pt idx hrun).1
  have hbound : ∀ v ∈ (Finset.range T).image pt, |cond_bias T pt y v| ≤ 1 := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (hsub hv)
    exact cond_bias_abs_le_one T m y p pt idx hrun T le_rfl j
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  calc ece T pt y = ∑ v ∈ (Finset.range T).image pt, |cond_bias T pt y v| := rfl
    _ ≤ ∑ _v ∈ (Finset.range T).image pt, (1 : ℝ) := Finset.sum_le_sum hbound
    _ = (((Finset.range T).image pt).card : ℝ) := by simp
    _ ≤ ((((Finset.range (m + 1)).image (grid_point m)).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (m : ℝ) + 1 := by
        have := Finset.card_image_le (s := Finset.range (m + 1)) (f := grid_point m)
        rw [Finset.card_range] at this
        exact_mod_cast Nat.cast_le.mpr this

@[blueprint "lem:cal-dist-lookahead-le"
  (statement := /-- Let $T, m \in \mathbb{N}$ and let $(y, p, \tilde p, i)$ be a run of Algorithm 1
    in the sense of \cref{def:aosa-run}. Then
    \[ \mathrm{CalDist}(\tilde p^{1:T}, y^{1:T}) \leq m + 1. \] -/)
  (proof := /-- By \cref{lem:cal-dist-le-ece} applied to the sequence $\tilde p^{1:T}$ we have
    $\mathrm{CalDist}(\tilde p^{1:T}, y^{1:T}) \leq \mathrm{ECE}(\tilde p^{1:T}, y^{1:T})$, and by
    \cref{lem:ece-lookahead-le} the latter is at most $m + 1$. Chaining the two inequalities gives
    the claim. -/)
  (title := /-- Distance to Calibration of the Look-Ahead Sequence -/)
  (latexEnv := "lemma")]
lemma cal_dist_lookahead_le (T m : ℕ) (y p pt : ℕ → ℝ) (idx : ℕ → ℕ)
    (hrun : aosa_run T m y p pt idx) :
    cal_dist T pt y ≤ (m : ℝ) + 1 := by
  calc cal_dist T pt y ≤ ece T pt y := cal_dist_le_ece T pt y
    _ ≤ (m : ℝ) + 1 := ece_lookahead_le T m y p pt idx hrun

@[blueprint "lem:grid-point-succ-sub"
  (statement := /-- Let $m, i \in \mathbb{N}$ with $1 \leq m$. Then the two adjacent grid points
    of \cref{def:grid-point} with indices $i$ and $i + 1$ satisfy
    \[ p_{i+1} - p_i = \frac{1}{m}. \] -/)
  (proof := /-- By \cref{def:grid-point} we have $p_{i+1} = \frac{i+1}{m}$ and
    $p_i = \frac{i}{m}$, where $i$ and $i+1$ are cast from $\mathbb{N}$ to $\mathbb{R}$. Since the
    two fractions have the same denominator,
    $p_{i+1} - p_i = \frac{(i+1) - i}{m} = \frac{1}{m}$, using that the cast of $i + 1$ equals the
    cast of $i$ plus $1$. -/)
  (title := /-- Adjacent Grid Points Are at Distance $1/m$ -/)
  (latexEnv := "lemma")]
lemma grid_point_succ_sub (m i : ℕ) :
    grid_point m (i + 1) - grid_point m i = 1 / (m : ℝ) := by
  unfold grid_point
  rw [div_sub_div_same]
  push_cast
  ring_nf

@[blueprint "lem:abs-pred-sub-lookahead-le"
  (statement := /-- Let $T, m \in \mathbb{N}$, let $(y, p, \tilde p, i)$ be a run of Algorithm 1
    in the sense of \cref{def:aosa-run} and let $t < T$ be a round. Then the issued and the
    look-ahead prediction of round $t$ satisfy
    \[ |p^t - \tilde p^t| \leq \frac{1}{m}. \] -/)
  (proof := /-- By \cref{def:aosa-run} the run provides $m \geq 1$, hence $1/m \geq 0$, and for
    the round $t < T$ it provides $p^t \in \{p_{i^t}, p_{i^t+1}\}$ and
    $\tilde p^t \in \{p_{i^t}, p_{i^t+1}\}$, where $p_j$ denotes the grid point of
    \cref{def:grid-point}. We distinguish the four resulting cases. If $p^t = \tilde p^t$, which
    covers the two cases $p^t = \tilde p^t = p_{i^t}$ and $p^t = \tilde p^t = p_{i^t+1}$, then
    $|p^t - \tilde p^t| = 0 \leq 1/m$. If $p^t = p_{i^t}$ and $\tilde p^t = p_{i^t+1}$, then
    $|p^t - \tilde p^t| = |p_{i^t+1} - p_{i^t}| = 1/m$ by \cref{lem:grid-point-succ-sub} together
    with $1/m \geq 0$; the remaining case $p^t = p_{i^t+1}$, $\tilde p^t = p_{i^t}$ is identical
    after exchanging the two arguments of the absolute value. In all four cases
    $|p^t - \tilde p^t| \leq 1/m$. -/)
  (title := /-- Per-Round Distance Between the Issued and the Look-Ahead Prediction -/)
  (latexEnv := "lemma")]
lemma abs_pred_sub_lookahead_le (T m : ℕ) (y p pt : ℕ → ℝ) (idx : ℕ → ℕ)
    (hrun : aosa_run T m y p pt idx) (t : ℕ) (ht : t < T) :
    |p t - pt t| ≤ 1 / (m : ℝ) := by
  obtain ⟨hm, hall⟩ := hrun
  obtain ⟨-, -, -, -, hp, hpt, -, -⟩ := hall t ht
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  have h0 : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  have hspacing := grid_point_succ_sub m (idx t)
  rcases hp with hp | hp <;> rcases hpt with hpt | hpt <;> rw [hp, hpt]
  · simpa using h0
  · rw [abs_sub_comm, hspacing, abs_of_nonneg h0]
  · rw [hspacing, abs_of_nonneg h0]
  · simpa using h0

@[blueprint "lem:l1-dist-pred-lookahead-le"
  (statement := /-- Let $T, m \in \mathbb{N}$ and let $(y, p, \tilde p, i)$ be a run of Algorithm 1
    in the sense of \cref{def:aosa-run}. Then
    \[ \|p^{1:T} - \tilde p^{1:T}\|_1 \leq \frac{T}{m}. \] -/)
  (proof := /-- Let $t < T$. By \cref{def:aosa-run} both $p^t$ and $\tilde p^t$ belong to the
    two-element set $\{p_{i^t}, p_{i^t+1}\}$ of adjacent grid points of \cref{def:grid-point}, so
    \cref{lem:abs-pred-sub-lookahead-le} gives $|p^t - \tilde p^t| \leq \frac{1}{m}$ for every
    round $t < T$. By \cref{def:l1-dist} the quantity
    $\|p^{1:T} - \tilde p^{1:T}\|_1$ is the sum of the $T$ terms $|p^t - \tilde p^t|$ over the
    rounds $t < T$, so summing the per-round bound term by term yields
    $\|p^{1:T} - \tilde p^{1:T}\|_1 \leq \sum_{t < T} \frac{1}{m}$. The right-hand side is a sum
    of $T$ equal terms, hence equals $T \cdot \frac{1}{m} = \frac{T}{m}$, which gives the
    claim. -/)
  (title := /-- The Issued and Look-Ahead Predictions Differ by at Most $T/m$ in $\ell_1$ -/)
  (latexEnv := "lemma")]
lemma l1_dist_pred_lookahead_le (T m : ℕ) (y p pt : ℕ → ℝ) (idx : ℕ → ℕ)
    (hrun : aosa_run T m y p pt idx) :
    l1_dist T p pt ≤ (T : ℝ) / (m : ℝ) := by
  have hstep : ∀ t ∈ Finset.range T, |p t - pt t| ≤ 1 / (m : ℝ) := fun t ht =>
    abs_pred_sub_lookahead_le T m y p pt idx hrun t (Finset.mem_range.mp ht)
  have hsum : ∑ t ∈ Finset.range T, |p t - pt t| ≤ ∑ _t ∈ Finset.range T, 1 / (m : ℝ) :=
    Finset.sum_le_sum hstep
  have hconst : ∑ _t ∈ Finset.range T, 1 / (m : ℝ) = (T : ℝ) / (m : ℝ) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one_div]
  calc l1_dist T p pt = ∑ t ∈ Finset.range T, |p t - pt t| := rfl
    _ ≤ ∑ _t ∈ Finset.range T, 1 / (m : ℝ) := hsum
    _ = (T : ℝ) / (m : ℝ) := hconst

@[blueprint "lem:cal-dist-aosa-le-grid"
  (statement := /-- Let $T, m \in \mathbb{N}$ and let $(y, p, \tilde p, i)$ be a run of Algorithm 1
    in the sense of \cref{def:aosa-run}. Then the issued predictions satisfy
    \[ \mathrm{CalDist}(p^{1:T}, y^{1:T}) \leq m + 1 + \frac{T}{m}. \] -/)
  (proof := /-- By \cref{lem:cal-dist-le-shift} applied to $p^{1:T}$ and $\tilde p^{1:T}$,
    \[ \mathrm{CalDist}(p^{1:T}, y^{1:T})
        \leq \mathrm{CalDist}(\tilde p^{1:T}, y^{1:T}) + \|p^{1:T} - \tilde p^{1:T}\|_1. \]
    The first summand is at most $m + 1$ by \cref{lem:cal-dist-lookahead-le}, and the second is at
    most $T/m$ by \cref{lem:l1-dist-pred-lookahead-le}. Adding the two bounds gives
    $\mathrm{CalDist}(p^{1:T}, y^{1:T}) \leq m + 1 + T/m$. -/)
  (title := /-- Calibration Guarantee for Algorithm 1 with a General Grid Parameter -/)
  (latexEnv := "lemma")]
lemma cal_dist_aosa_le_grid (T m : ℕ) (y p pt : ℕ → ℝ) (idx : ℕ → ℕ)
    (hrun : aosa_run T m y p pt idx) :
    cal_dist T p y ≤ (m : ℝ) + 1 + (T : ℝ) / (m : ℝ) := by
  have hshift : cal_dist T p y ≤ cal_dist T pt y + l1_dist T p pt :=
    cal_dist_le_shift T p pt y
  have hlook : cal_dist T pt y ≤ (m : ℝ) + 1 :=
    cal_dist_lookahead_le T m y p pt idx hrun
  have hl1 : l1_dist T p pt ≤ (T : ℝ) / (m : ℝ) :=
    l1_dist_pred_lookahead_le T m y p pt idx hrun
  linarith

@[blueprint "lem:grid-size-bound-sqrt"
  (statement := /-- Let $T, m \in \mathbb{N}$ with $1 \leq m$, and suppose the discretization
    parameter realizes the choice of the source analysis exactly, that is, $m = \sqrt{T}$ as real
    numbers. Then
    \[ m + 1 + \frac{T}{m} \leq 2\sqrt{T} + 1. \] -/)
  (proof := /-- Substituting the hypothesis $m = \sqrt{T}$ into the left-hand side gives
    \[ m + 1 + \frac{T}{m} = \sqrt{T} + 1 + \frac{T}{\sqrt{T}}. \]
    Since $T \geq 0$, we have $\frac{T}{\sqrt{T}} = \sqrt{T}$: for $T > 0$ this follows from
    $\left(\sqrt{T}\right)^2 = T$ together with $\sqrt{T} > 0$, and for $T = 0$ both sides equal
    $0$, using the convention that division by zero yields zero. Hence the left-hand side equals
    $\sqrt{T} + 1 + \sqrt{T} = 2\sqrt{T} + 1$, and in particular it is at most
    $2\sqrt{T} + 1$. -/)
  (title := /-- Optimizing the Grid Parameter at $m = \sqrt{T}$ -/)
  (latexEnv := "lemma")]
lemma grid_size_bound_sqrt (T m : ℕ) (hm : 1 ≤ m) (hms : (m : ℝ) = Real.sqrt T) :
    (m : ℝ) + 1 + (T : ℝ) / (m : ℝ) ≤ 2 * Real.sqrt T + 1 := by
  rw [hms, Real.div_sqrt]
  linarith

@[blueprint "thm:alg"
  (statement := /-- (Theorem 1 of the source.) Let $T \in \mathbb{N}$ be a horizon and let
    $m \in \mathbb{N}$ be the discretization parameter of Algorithm 1, chosen as in the source
    analysis so that $1 \leq m$ and $m = \sqrt{T}$ as real numbers. Let
    $y : \mathbb{N} \to \mathbb{R}$ be an arbitrary sequence of outcomes and let
    $(y, p, \tilde p, i)$ be a run of Algorithm 1 (\textsf{AOSA}) in the sense of
    \cref{def:aosa-run}, with issued predictions $p^{1:T}$. Then
    \[ \mathrm{CalDist}(p^{1:T}, y^{1:T}) \leq 2\sqrt{T} + 1. \]
    Since the hypothesis quantifies over every run and every outcome sequence, this is exactly the
    guarantee of Algorithm 1 against any sequence of outcomes. -/)
  (proof := /-- By \cref{lem:cal-dist-aosa-le-grid} the run satisfies
    $\mathrm{CalDist}(p^{1:T}, y^{1:T}) \leq m + 1 + \frac{T}{m}$. By
    \cref{lem:grid-size-bound-sqrt}, whose hypotheses $1 \leq m$ and $m = \sqrt{T}$ hold by
    assumption, the right-hand side is at most $2\sqrt{T} + 1$.
    Chaining the two inequalities gives $\mathrm{CalDist}(p^{1:T}, y^{1:T}) \leq 2\sqrt{T} + 1$. -/)
  (title := /-- Algorithm 1 (\textsf{AOSA}) Attains Distance to Calibration $2\sqrt{T} + 1$ -/)
  (latexEnv := "theorem")]
theorem alg (T m : ℕ) (y p pt : ℕ → ℝ) (idx : ℕ → ℕ) (hm : 1 ≤ m)
    (hms : (m : ℝ) = Real.sqrt T)
    (hrun : aosa_run T m y p pt idx) :
    cal_dist T p y ≤ 2 * Real.sqrt T + 1 := by
  have hgrid : cal_dist T p y ≤ (m : ℝ) + 1 + (T : ℝ) / (m : ℝ) :=
    cal_dist_aosa_le_grid T m y p pt idx hrun
  have hopt : (m : ℝ) + 1 + (T : ℝ) / (m : ℝ) ≤ 2 * Real.sqrt T + 1 :=
    grid_size_bound_sqrt T m hm hms
  exact hgrid.trans hopt

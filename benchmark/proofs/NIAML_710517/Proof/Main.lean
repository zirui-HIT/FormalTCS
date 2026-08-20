import Architect
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Union
import Mathlib.Topology.MetricSpace.Pseudo.Basic

set_option linter.all false
set_option maxHeartbeats 500000

open scoped RealInnerProductSpace

@[blueprint "def:mse"
  (statement := /-- Let $H$ be a real inner product space, understood as the space $L^2(\mathcal{D})$
  of square-integrable random variables over the fixed data distribution $\mathcal{D}$, so that
  $\langle u, v \rangle = \mathbb{E}[uv]$ and $\|u\| = \sqrt{\mathbb{E}[u^2]}$. For a target
  $y \in H$ and a predictor $f \in H$, the \emph{mean squared error} of $f$ relative to $y$ is
  \[ \mathrm{MSE}(f) = \mathbb{E}[(f - y)^2] = \|f - y\|^2 . \] -/)
  (title := /-- Mean Squared Error -/)
  (latexEnv := "definition")]
def mse {H : Type*} [NormedAddCommGroup H] (y f : H) : ℝ :=
  ‖f - y‖ ^ 2

@[blueprint "def:path-orthogonality"
  (statement := /-- Let $H$ be a real inner product space as in \cref{def:mse}, let $y \in H$ be the
  target, let $x : \iota \to H$ assign to each feature index $l$ the feature variable $x_l$, let
  $S : \mathbb{N} \to \mathrm{Finset}(\iota)$ assign to each position $t$ on the path the finite set
  $S_t$ of feature indices observed by the agent at position $t$, and let
  $\hat{y} : \mathbb{N} \to H$ assign to each position $t$ the prediction $\hat{y}_t$ of the agent at
  that position. We say that the family $(\hat{y}_t)_{t \in \mathbb{N}}$ is
  \emph{path-orthogonal} for $(y, x, S)$ when the following three conditions hold.
  \begin{enumerate}
    \item (Self-orthogonality) For every $t \in \mathbb{N}$,
      $\mathbb{E}[\hat{y}_t(\hat{y}_t - y)] = 0$.
    \item (Multiaccuracy with respect to the locally observed features) For every
      $t \in \mathbb{N}$ and every $l \in S_t$, $\mathbb{E}[x_l(\hat{y}_t - y)] = 0$.
    \item (Multiaccuracy with respect to the predecessor's prediction) For every
      $t \in \mathbb{N}$, $\mathbb{E}[\hat{y}_t(\hat{y}_{t+1} - y)] = 0$.
  \end{enumerate}
  These are exactly the three consequences of the paper's learning model that the argument uses: each
  agent minimises the expected squared error over linear functions of its own inputs, hence its
  residual is orthogonal to each of its inputs, and on a path the prediction of the agent at position
  $t$ is one of the inputs of the agent at position $t+1$. The learning model itself is not
  formalised here; only these consequences are assumed. -/)
  (title := /-- Path Orthogonality of a Family of Predictors -/)
  (latexEnv := "definition")]
def path_orthogonality {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (y : H) (xfeat : ι → H) (S : ℕ → Finset ι) (yhat : ℕ → H) : Prop :=
  (∀ t : ℕ, ⟪yhat t, yhat t - y⟫ = 0) ∧
    (∀ t : ℕ, ∀ l ∈ S t, ⟪xfeat l, yhat t - y⟫ = 0) ∧
      (∀ t : ℕ, ⟪yhat t, yhat (t + 1) - y⟫ = 0)

@[blueprint "lem:mse-decomposition"
  (statement := /-- Let $H$ be a real inner product space, let $y \in H$ be a target and let
  $f, g \in H$ be predictors. Then, with $\mathrm{MSE}$ as in \cref{def:mse},
  \[ \mathrm{MSE}(f) = \mathrm{MSE}(g) - 2\mathbb{E}[g(f - y)] + 2\mathbb{E}[f(f - y)]
     - \mathbb{E}[(f - g)^2] . \] -/)
  (proof := /-- Write $u = f - y$, $v = g - y$, so that $f - g = u - v$, and recall from
  \cref{def:mse} that $\mathrm{MSE}(f) = \|u\|^2$ and $\mathrm{MSE}(g) = \|v\|^2$. Since the inner
  product is bilinear and symmetric,
  \[ -2\mathbb{E}[g(f-y)] + 2\mathbb{E}[f(f-y)] = 2\langle f - g, u \rangle
     = 2\langle u - v, u \rangle = 2\|u\|^2 - 2\langle u, v \rangle , \]
  and expanding the last term gives
  \[ \mathbb{E}[(f-g)^2] = \|u - v\|^2 = \|u\|^2 - 2\langle u, v \rangle + \|v\|^2 . \]
  Substituting both displays into the right-hand side of the assertion yields
  \[ \|v\|^2 + \bigl(2\|u\|^2 - 2\langle u, v\rangle\bigr)
     - \bigl(\|u\|^2 - 2\langle u, v \rangle + \|v\|^2\bigr) = \|u\|^2 = \mathrm{MSE}(f) , \]
  which is the claimed identity. -/)
  (title := /-- MSE Decomposition -/)
  (latexEnv := "lemma")]
lemma mse_decomposition {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (y f g : H) :
    mse y f = mse y g - 2 * ⟪g, f - y⟫ + 2 * ⟪f, f - y⟫ - ‖f - g‖ ^ 2 := by
  simp only [mse, ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    real_inner_comm y f, real_inner_comm y g, real_inner_comm g f]
  ring

@[blueprint "lem:stability"
  (statement := /-- Let $H$ be a real inner product space, let $y \in H$ be a target and let
  $f, g \in H$ be predictors. Assume that $f$ is self-orthogonal, that is
  $\mathbb{E}[f(f - y)] = 0$, and that $f$ is multiaccurate with respect to $g$, that is
  $\mathbb{E}[g(f - y)] = 0$. Then, with $\mathrm{MSE}$ as in \cref{def:mse},
  \[ \mathbb{E}[(f - g)^2] = \mathrm{MSE}(g) - \mathrm{MSE}(f) . \] -/)
  (proof := /-- By \cref{lem:mse-decomposition},
  \[ \mathrm{MSE}(f) = \mathrm{MSE}(g) - 2\mathbb{E}[g(f - y)] + 2\mathbb{E}[f(f - y)]
     - \mathbb{E}[(f - g)^2] . \]
  The hypotheses $\mathbb{E}[g(f - y)] = 0$ and $\mathbb{E}[f(f - y)] = 0$ make the two middle terms
  vanish, so $\mathrm{MSE}(f) = \mathrm{MSE}(g) - \mathbb{E}[(f - g)^2]$. Solving this equation for
  $\mathbb{E}[(f - g)^2] = \|f - g\|^2$ gives the assertion. -/)
  (title := /-- Stability: Squared Distance Equals MSE Gap -/)
  (latexEnv := "lemma")]
lemma stability {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (y f g : H)
    (hself : ⟪f, f - y⟫ = 0) (hmulti : ⟪g, f - y⟫ = 0) :
    ‖f - g‖ ^ 2 = mse y g - mse y f := by
  have hdec := mse_decomposition y f g
  rw [hself, hmulti] at hdec
  linarith

@[blueprint "lem:mse-competitive-bound"
  (statement := /-- Let $H$ be a real inner product space, let $y \in H$ be a target and let
  $f, g \in H$ be predictors. Then, with $\mathrm{MSE}$ as in \cref{def:mse},
  \[ \mathrm{MSE}(f) \le \mathrm{MSE}(g) + 2\bigl|\mathbb{E}[g(f - y)]\bigr|
     + 2\bigl|\mathbb{E}[f(f - y)]\bigr| . \] -/)
  (proof := /-- By \cref{lem:mse-decomposition},
  \[ \mathrm{MSE}(f) = \mathrm{MSE}(g) - 2\mathbb{E}[g(f - y)] + 2\mathbb{E}[f(f - y)]
     - \mathbb{E}[(f - g)^2] . \]
  We bound the right-hand side from above term by term. First,
  $-2\mathbb{E}[g(f-y)] \le 2|\mathbb{E}[g(f-y)]|$ and
  $2\mathbb{E}[f(f-y)] \le 2|\mathbb{E}[f(f-y)]|$, since $r \le |r|$ and $-r \le |r|$ for every real
  $r$. Second, $\mathbb{E}[(f - g)^2] = \|f - g\|^2 \ge 0$, so discarding the term
  $-\mathbb{E}[(f-g)^2]$ can only increase the right-hand side. Combining the three estimates gives
  the claimed inequality. -/)
  (title := /-- Competitive MSE Bound Against an Arbitrary Predictor -/)
  (latexEnv := "lemma")]
lemma mse_competitive_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (y f g : H) :
    mse y f ≤ mse y g + 2 * |⟪g, f - y⟫| + 2 * |⟪f, f - y⟫| := by
  have hdecomp := mse_decomposition y f g
  have hg : -⟪g, f - y⟫ ≤ |⟪g, f - y⟫| := neg_le_abs _
  have hf : ⟪f, f - y⟫ ≤ |⟪f, f - y⟫| := le_abs_self _
  have hfg : (0 : ℝ) ≤ ‖f - g‖ ^ 2 := sq_nonneg _
  linarith

@[blueprint "lem:consecutive-closeness"
  (statement := /-- Let $H$ be a real inner product space, let $y \in H$, let $x : \iota \to H$,
  let $S : \mathbb{N} \to \mathrm{Finset}(\iota)$ and let $\hat{y} : \mathbb{N} \to H$ be
  path-orthogonal for $(y, x, S)$ in the sense of \cref{def:path-orthogonality}. Then for every
  $t \in \mathbb{N}$, with $\mathrm{MSE}$ as in \cref{def:mse},
  \[ \mathbb{E}\bigl[(\hat{y}_{t+1} - \hat{y}_t)^2\bigr]
     = \mathrm{MSE}(\hat{y}_t) - \mathrm{MSE}(\hat{y}_{t+1}) . \] -/)
  (proof := /-- Fix $t \in \mathbb{N}$ and apply \cref{lem:stability} with $f = \hat{y}_{t+1}$ and
  $g = \hat{y}_t$. Its two hypotheses hold: self-orthogonality
  $\mathbb{E}[\hat{y}_{t+1}(\hat{y}_{t+1} - y)] = 0$ is the first clause of
  \cref{def:path-orthogonality} applied at position $t+1$, and multiaccuracy with respect to
  $\hat{y}_t$, namely $\mathbb{E}[\hat{y}_t(\hat{y}_{t+1} - y)] = 0$, is the third clause of
  \cref{def:path-orthogonality} applied at position $t$. Hence
  $\|\hat{y}_{t+1} - \hat{y}_t\|^2 = \mathrm{MSE}(\hat{y}_t) - \mathrm{MSE}(\hat{y}_{t+1})$, which is
  the assertion. -/)
  (title := /-- Per-Step MSE Improvement Equals Squared Predictor Distance -/)
  (latexEnv := "lemma")]
lemma consecutive_closeness {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (y : H) (xfeat : ι → H) (S : ℕ → Finset ι) (yhat : ℕ → H)
    (horth : path_orthogonality y xfeat S yhat) (t : ℕ) :
    ‖yhat (t + 1) - yhat t‖ ^ 2 = mse y (yhat t) - mse y (yhat (t + 1)) := by
  exact stability y (yhat (t + 1)) (yhat t) (horth.1 (t + 1)) (horth.2.2 t)

@[blueprint "lem:consecutive-improvement-nonneg"
  (statement := /-- Let $H$ be a real inner product space, let $y \in H$, let $x : \iota \to H$,
  let $S : \mathbb{N} \to \mathrm{Finset}(\iota)$ and let $\hat{y} : \mathbb{N} \to H$ be
  path-orthogonal for $(y, x, S)$ in the sense of \cref{def:path-orthogonality}. Then for every
  $t \in \mathbb{N}$, with $\mathrm{MSE}$ as in \cref{def:mse},
  \[ 0 \le \mathrm{MSE}(\hat{y}_t) - \mathrm{MSE}(\hat{y}_{t+1}) . \]
  That is, the mean squared error is nonincreasing along the path. -/)
  (proof := /-- Fix $t \in \mathbb{N}$. By \cref{lem:consecutive-closeness},
  \[ \mathrm{MSE}(\hat{y}_t) - \mathrm{MSE}(\hat{y}_{t+1})
     = \|\hat{y}_{t+1} - \hat{y}_t\|^2 , \]
  and the square of a norm is nonnegative. -/)
  (title := /-- Monotonicity of the MSE Along the Path -/)
  (latexEnv := "lemma")]
lemma consecutive_improvement_nonneg {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (y : H) (xfeat : ι → H) (S : ℕ → Finset ι) (yhat : ℕ → H)
    (horth : path_orthogonality y xfeat S yhat) (t : ℕ) :
    0 ≤ mse y (yhat t) - mse y (yhat (t + 1)) := by
  rw [← consecutive_closeness y xfeat S yhat horth t]
  exact sq_nonneg _

@[blueprint "lem:mse-telescope"
  (statement := /-- Let $H$ be a real normed additive commutative group, for instance the space
  $H$ of \cref{def:mse} with its norm; no inner product structure is used here. Let $y \in H$ be a
  target, let $\hat{y} : \mathbb{N} \to H$ be an arbitrary family of predictors and let
  $m, n \in \mathbb{N}$ satisfy $m \le n$. Then, with $\mathrm{MSE}$ as in \cref{def:mse},
  \[ \sum_{t = m}^{n-1} \bigl(\mathrm{MSE}(\hat{y}_t) - \mathrm{MSE}(\hat{y}_{t+1})\bigr)
     = \mathrm{MSE}(\hat{y}_m) - \mathrm{MSE}(\hat{y}_n) , \]
  the sum being taken over the half-open integer interval $[m, n)$. -/)
  (proof := /-- Write $F(t) = \mathrm{MSE}(\hat{y}_t)$ for the real sequence of mean squared errors
  along the path; no hypothesis on $\hat{y}$ is needed beyond $m \le n$.

  The standard telescoping identity for sums of consecutive differences over a half-open interval
  of natural numbers, applied to $F$ with the hypothesis $m \le n$, gives
  \[ \sum_{t = m}^{n-1} \bigl(F(t+1) - F(t)\bigr) = F(n) - F(m) . \]

  Since the index set $[m, n)$ is finite and each summand is a difference of two real numbers, a
  sum of differences splits as the difference of the two sums. Applying this splitting to the
  displayed identity and to the assertion to be proved reduces both to statements about the two
  sums
  \[ \Sigma_0 = \sum_{t = m}^{n-1} F(t), \qquad \Sigma_1 = \sum_{t = m}^{n-1} F(t+1) , \]
  namely the identity becomes $\Sigma_1 - \Sigma_0 = F(n) - F(m)$, while the assertion becomes
  $\Sigma_0 - \Sigma_1 = F(m) - F(n)$. The latter is obtained from the former by negating both
  sides, which is a valid deduction in the ordered field of real numbers, and this is the
  assertion. -/)
  (title := /-- Telescoping of the Per-Step MSE Improvements -/)
  (latexEnv := "lemma")]
lemma mse_telescope {H : Type*} [NormedAddCommGroup H] (y : H) (yhat : ℕ → H) {m n : ℕ}
    (hmn : m ≤ n) :
    ∑ t ∈ Finset.Ico m n, (mse y (yhat t) - mse y (yhat (t + 1)))
      = mse y (yhat m) - mse y (yhat n) := by
  have h := Finset.sum_Ico_sub (fun t => mse y (yhat t)) hmn
  simp only [Finset.sum_sub_distrib] at h ⊢
  linarith

@[blueprint "lem:sum-sqrt-sq-le"
  (statement := /-- Let $s$ be a finite set of natural numbers and let $d : \mathbb{N} \to
  \mathbb{R}$ satisfy $d_t \ge 0$ for every $t \in s$. Then
  \[ \Bigl(\sum_{t \in s} \sqrt{d_t}\Bigr)^2 \le |s| \sum_{t \in s} d_t , \]
  where $|s|$ denotes the cardinality of $s$. -/)
  (proof := /-- By the Cauchy-Schwarz inequality applied to the family $(\sqrt{d_t})_{t \in s}$ and
  the constant family $1$,
  \[ \Bigl(\sum_{t \in s} \sqrt{d_t}\Bigr)^2 \le |s| \sum_{t \in s} \bigl(\sqrt{d_t}\bigr)^2 . \]
  For each $t \in s$ we have $d_t \ge 0$ by hypothesis, hence $(\sqrt{d_t})^2 = d_t$. Substituting
  this identity into the right-hand side gives the assertion. -/)
  (title := /-- Cauchy-Schwarz for a Sum of Square Roots -/)
  (latexEnv := "lemma")]
lemma sum_sqrt_sq_le (s : Finset ℕ) (d : ℕ → ℝ) (hd : ∀ t ∈ s, 0 ≤ d t) :
    (∑ t ∈ s, Real.sqrt (d t)) ^ 2 ≤ (s.card : ℝ) * ∑ t ∈ s, d t := by
  calc (∑ t ∈ s, Real.sqrt (d t)) ^ 2
      ≤ (s.card : ℝ) * ∑ t ∈ s, Real.sqrt (d t) ^ 2 := sq_sum_le_card_mul_sum_sq
    _ = (s.card : ℝ) * ∑ t ∈ s, d t := by
        congr 1
        exact Finset.sum_congr rfl fun t ht => Real.sq_sqrt (hd t ht)

@[blueprint "lem:partial-improvement-le-total"
  (statement := /-- Let $H$ be a real inner product space, let $y \in H$, let $x : \iota \to H$,
  let $S : \mathbb{N} \to \mathrm{Finset}(\iota)$ and let $\hat{y} : \mathbb{N} \to H$ be
  path-orthogonal for $(y, x, S)$ in the sense of \cref{def:path-orthogonality}. Let
  $a, m, b \in \mathbb{N}$ satisfy $a \le m \le b$ and let $\varepsilon \in \mathbb{R}$ be the total
  improvement across the subsequence, that is
  $\mathrm{MSE}(\hat{y}_a) - \mathrm{MSE}(\hat{y}_b) = \varepsilon$, with $\mathrm{MSE}$ as in
  \cref{def:mse}. Then
  \[ \sum_{t = m}^{b-1} \bigl(\mathrm{MSE}(\hat{y}_t) - \mathrm{MSE}(\hat{y}_{t+1})\bigr)
     \le \varepsilon . \] -/)
  (proof := /-- By \cref{lem:mse-telescope} applied with the bounds $m \le b$,
  \[ \sum_{t = m}^{b-1} \bigl(\mathrm{MSE}(\hat{y}_t) - \mathrm{MSE}(\hat{y}_{t+1})\bigr)
     = \mathrm{MSE}(\hat{y}_m) - \mathrm{MSE}(\hat{y}_b) . \]
  It therefore suffices to prove $\mathrm{MSE}(\hat{y}_m) \le \mathrm{MSE}(\hat{y}_a)$, since then
  \[ \mathrm{MSE}(\hat{y}_m) - \mathrm{MSE}(\hat{y}_b)
     \le \mathrm{MSE}(\hat{y}_a) - \mathrm{MSE}(\hat{y}_b) = \varepsilon . \]
  To that end apply \cref{lem:mse-telescope} once more, now with the bounds $a \le m$, to get
  \[ \mathrm{MSE}(\hat{y}_a) - \mathrm{MSE}(\hat{y}_m)
     = \sum_{t = a}^{m-1} \bigl(\mathrm{MSE}(\hat{y}_t) - \mathrm{MSE}(\hat{y}_{t+1})\bigr) . \]
  Every summand is nonnegative by \cref{lem:consecutive-improvement-nonneg}, so the sum is
  nonnegative and $\mathrm{MSE}(\hat{y}_m) \le \mathrm{MSE}(\hat{y}_a)$, as required. -/)
  (title := /-- Improvement on a Terminal Segment is at Most the Total Improvement -/)
  (latexEnv := "lemma")]
lemma partial_improvement_le_total {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (y : H) (xfeat : ι → H) (S : ℕ → Finset ι) (yhat : ℕ → H)
    (horth : path_orthogonality y xfeat S yhat) {a m b : ℕ} (ham : a ≤ m) (hmb : m ≤ b)
    {ε : ℝ} (hε : mse y (yhat a) - mse y (yhat b) = ε) :
    ∑ t ∈ Finset.Ico m b, (mse y (yhat t) - mse y (yhat (t + 1))) ≤ ε := by
  have hmb' := mse_telescope y yhat hmb
  have ham' := mse_telescope y yhat ham
  have hpref : 0 ≤ ∑ t ∈ Finset.Ico a m, (mse y (yhat t) - mse y (yhat (t + 1))) :=
    Finset.sum_nonneg fun t _ => consecutive_improvement_nonneg y xfeat S yhat horth t
  rw [hmb']
  linarith

@[blueprint "lem:predictor-distance-le-sqrt-sum"
  (statement := /-- Let $H$ be a real inner product space, let $y \in H$, let $x : \iota \to H$,
  let $S : \mathbb{N} \to \mathrm{Finset}(\iota)$ and let $\hat{y} : \mathbb{N} \to H$ be
  path-orthogonal for $(y, x, S)$ in the sense of \cref{def:path-orthogonality}. Let
  $m, b \in \mathbb{N}$ satisfy $m \le b$. Then, with $\mathrm{MSE}$ as in \cref{def:mse},
  \[ \bigl\|\hat{y}_b - \hat{y}_m\bigr\|
     \le \sum_{t = m}^{b-1}
       \sqrt{\mathrm{MSE}(\hat{y}_t) - \mathrm{MSE}(\hat{y}_{t+1})} , \]
  the sum being taken over the half-open integer interval $[m, b)$. -/)
  (proof := /-- We first identify each per-step distance. Fix $t \in \mathbb{N}$. By
  \cref{lem:consecutive-closeness},
  \[ \bigl\|\hat{y}_{t+1} - \hat{y}_t\bigr\|^2
     = \mathrm{MSE}(\hat{y}_t) - \mathrm{MSE}(\hat{y}_{t+1}) , \]
  and the distance between $\hat{y}_t$ and $\hat{y}_{t+1}$ equals
  $\|\hat{y}_t - \hat{y}_{t+1}\| = \|\hat{y}_{t+1} - \hat{y}_t\|$, the second equality because a
  norm is invariant under negation. Since $\|\hat{y}_{t+1} - \hat{y}_t\| \ge 0$ and
  $\sqrt{r^2} = r$ for every $r \ge 0$, taking square roots in the displayed identity gives
  \[ \mathrm{dist}(\hat{y}_t, \hat{y}_{t+1})
     = \sqrt{\mathrm{MSE}(\hat{y}_t) - \mathrm{MSE}(\hat{y}_{t+1})} \qquad
     \text{for every } t \in \mathbb{N} . \]

  Now $\|\hat{y}_b - \hat{y}_m\| = \mathrm{dist}(\hat{y}_m, \hat{y}_b)$, again because a norm is
  invariant under negation. The polygon (iterated triangle) inequality for the finite sequence
  $\hat{y}_m, \hat{y}_{m+1}, \ldots, \hat{y}_b$, available because $m \le b$, yields
  \[ \mathrm{dist}(\hat{y}_m, \hat{y}_b)
     \le \sum_{t = m}^{b-1} \mathrm{dist}(\hat{y}_t, \hat{y}_{t+1}) . \]
  Substituting the per-step identity into each summand turns the right-hand side into
  $\sum_{t = m}^{b-1} \sqrt{\mathrm{MSE}(\hat{y}_t) - \mathrm{MSE}(\hat{y}_{t+1})}$, which is the
  assertion. -/)
  (title := /-- Telescoping Bound on the Distance to a Later Predictor -/)
  (latexEnv := "lemma")]
lemma predictor_distance_le_sqrt_sum {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (y : H) (xfeat : ι → H) (S : ℕ → Finset ι) (yhat : ℕ → H)
    (horth : path_orthogonality y xfeat S yhat) {m b : ℕ} (hmb : m ≤ b) :
    ‖yhat b - yhat m‖
      ≤ ∑ t ∈ Finset.Ico m b, Real.sqrt (mse y (yhat t) - mse y (yhat (t + 1))) := by
  have hstep : ∀ t : ℕ, dist (yhat t) (yhat (t + 1))
      = Real.sqrt (mse y (yhat t) - mse y (yhat (t + 1))) := by
    intro t
    rw [← consecutive_closeness y xfeat S yhat horth t, Real.sqrt_sq (norm_nonneg _),
      dist_eq_norm, ← norm_neg, neg_sub]
  calc ‖yhat b - yhat m‖ = dist (yhat m) (yhat b) := by
        rw [dist_eq_norm, ← norm_neg, neg_sub]
    _ ≤ ∑ t ∈ Finset.Ico m b, dist (yhat t) (yhat (t + 1)) := dist_le_Ico_sum_dist yhat hmb
    _ = ∑ t ∈ Finset.Ico m b, Real.sqrt (mse y (yhat t) - mse y (yhat (t + 1))) :=
        Finset.sum_congr rfl fun t _ => hstep t

@[blueprint "lem:predictor-distance-bound"
  (statement := /-- Let $H$ be a real inner product space, let $y \in H$, let $x : \iota \to H$,
  let $S : \mathbb{N} \to \mathrm{Finset}(\iota)$ and let $\hat{y} : \mathbb{N} \to H$ be
  path-orthogonal for $(y, x, S)$ in the sense of \cref{def:path-orthogonality}. Let
  $a, m, b \in \mathbb{N}$ satisfy $a \le m \le b$ and let $\varepsilon \in \mathbb{R}$ satisfy
  $\mathrm{MSE}(\hat{y}_a) - \mathrm{MSE}(\hat{y}_b) = \varepsilon$, with $\mathrm{MSE}$ as in
  \cref{def:mse}. Then
  \[ \mathbb{E}\bigl[(\hat{y}_b - \hat{y}_m)^2\bigr] \le (b - m)\,\varepsilon . \] -/)
  (proof := /-- Write $\Delta_t = \mathrm{MSE}(\hat{y}_t) - \mathrm{MSE}(\hat{y}_{t+1})$ for the
  improvement made at step $t$; here $t$ ranges over all of $\mathbb{N}$, and the sums below are
  taken over the half-open integer interval $[m, b)$, which is legitimate because $m \le b$.

  By \cref{lem:consecutive-improvement-nonneg} we have $\Delta_t \ge 0$ for every
  $t \in \mathbb{N}$, in particular for every $t \in [m, b)$. By
  \cref{lem:predictor-distance-le-sqrt-sum}, applied with the bound $m \le b$,
  \[ \bigl\|\hat{y}_b - \hat{y}_m\bigr\| \le \sum_{t = m}^{b-1} \sqrt{\Delta_t} . \]
  The left-hand side is a norm, hence nonnegative, so squaring preserves this inequality:
  \[ \bigl\|\hat{y}_b - \hat{y}_m\bigr\|^2
     \le \Bigl(\sum_{t = m}^{b-1} \sqrt{\Delta_t}\Bigr)^2 . \]
  By \cref{lem:sum-sqrt-sq-le}, applied to the nonnegative family $(\Delta_t)$ indexed by the
  interval $[m, b)$, whose cardinality is $b - m$,
  \[ \Bigl(\sum_{t = m}^{b-1} \sqrt{\Delta_t}\Bigr)^2
     \le (b - m) \sum_{t = m}^{b-1} \Delta_t . \]
  Finally $\sum_{t = m}^{b-1} \Delta_t \le \varepsilon$ by
  \cref{lem:partial-improvement-le-total}, applied with the bounds $a \le m \le b$ and the
  hypothesis $\mathrm{MSE}(\hat{y}_a) - \mathrm{MSE}(\hat{y}_b) = \varepsilon$; since
  $b - m \ge 0$, multiplying this inequality by $b - m$ gives
  $(b - m) \sum_{t = m}^{b-1} \Delta_t \le (b - m)\varepsilon$. Chaining the three displayed
  inequalities gives the assertion. -/)
  (title := /-- L2 Distance to a Later Predictor on the Path -/)
  (latexEnv := "lemma")]
lemma predictor_distance_bound {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (y : H) (xfeat : ι → H) (S : ℕ → Finset ι) (yhat : ℕ → H)
    (horth : path_orthogonality y xfeat S yhat) {a m b : ℕ} (ham : a ≤ m) (hmb : m ≤ b)
    {ε : ℝ} (hε : mse y (yhat a) - mse y (yhat b) = ε) :
    ‖yhat b - yhat m‖ ^ 2 ≤ ((b - m : ℕ) : ℝ) * ε := by
  set d : ℕ → ℝ := fun t => mse y (yhat t) - mse y (yhat (t + 1))
  have hdnonneg : ∀ t ∈ Finset.Ico m b, 0 ≤ d t := fun t _ =>
    consecutive_improvement_nonneg y xfeat S yhat horth t
  have htri : ‖yhat b - yhat m‖ ≤ ∑ t ∈ Finset.Ico m b, Real.sqrt (d t) :=
    predictor_distance_le_sqrt_sum y xfeat S yhat horth hmb
  have hcard : ((Finset.Ico m b).card : ℝ) = ((b - m : ℕ) : ℝ) := by
    rw [Nat.card_Ico]
  have hsum : ∑ t ∈ Finset.Ico m b, d t ≤ ε :=
    partial_improvement_le_total y xfeat S yhat horth ham hmb hε
  calc ‖yhat b - yhat m‖ ^ 2 ≤ (∑ t ∈ Finset.Ico m b, Real.sqrt (d t)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) htri 2
    _ ≤ ((b - m : ℕ) : ℝ) * ∑ t ∈ Finset.Ico m b, d t := by
        rw [← hcard]; exact sum_sqrt_sq_le _ d hdnonneg
    _ ≤ ((b - m : ℕ) : ℝ) * ε := by
        exact mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)

@[blueprint "lem:feature-norm-bound"
  (statement := /-- Let $H$ be a real inner product space, let $u \in H$ and let
  $M \in \mathbb{R}$ satisfy $M \ge 0$ and $\mathbb{E}[u^2] \le M^2$, where
  $\mathbb{E}[u^2] = \langle u, u \rangle$. Then $\|u\| \le M$. -/)
  (proof := /-- Since $\langle u, u \rangle = \|u\|^2$, the hypothesis reads $\|u\|^2 \le M^2$. Both
  $\|u\|$ and $M$ are nonnegative, and the squaring map is strictly monotone on the nonnegative
  reals; hence $\|u\|^2 \le M^2$ forces $\|u\| \le M$, for otherwise $M < \|u\|$ would give
  $M^2 < \|u\|^2$, a contradiction. -/)
  (title := /-- Second Moment Bound Yields an L2 Norm Bound -/)
  (latexEnv := "lemma")]
lemma feature_norm_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (u : H)
    {M : ℝ} (hM : 0 ≤ M) (hu : ⟪u, u⟫ ≤ M ^ 2) :
    ‖u‖ ≤ M := by
  rw [real_inner_self_eq_norm_sq] at hu
  exact le_of_sq_le_sq hu hM

@[blueprint "lem:feature-residual-inner-shift"
  (statement := /-- Let $H$ be a real inner product space, let $y \in H$, let $x : \iota \to H$,
  let $S : \mathbb{N} \to \mathrm{Finset}(\iota)$ and let $\hat{y} : \mathbb{N} \to H$ be
  path-orthogonal for $(y, x, S)$ in the sense of \cref{def:path-orthogonality}. Let
  $m, b \in \mathbb{N}$ and let $l \in S_m$ be a feature index observed by the agent at position
  $m$. Then
  \[ \mathbb{E}[x_l(\hat{y}_b - y)] = \mathbb{E}[x_l(\hat{y}_b - \hat{y}_m)] . \] -/)
  (proof := /-- Since $l \in S_m$, the second clause of \cref{def:path-orthogonality} applied at
  position $m$ gives $\mathbb{E}[x_l(\hat{y}_m - y)] = 0$. In the additive group $H$ we have the
  identity $\hat{y}_b - \hat{y}_m = (\hat{y}_b - y) - (\hat{y}_m - y)$. Substituting it into the
  right-hand side of the assertion and using additivity of the inner product in its second
  argument,
  \[ \mathbb{E}[x_l(\hat{y}_b - \hat{y}_m)]
     = \mathbb{E}[x_l(\hat{y}_b - y)] - \mathbb{E}[x_l(\hat{y}_m - y)]
     = \mathbb{E}[x_l(\hat{y}_b - y)] - 0 , \]
  which is the assertion. -/)
  (title := /-- Shifting the Final Residual by an Orthogonal Prediction -/)
  (latexEnv := "lemma")]
lemma feature_residual_inner_shift {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (y : H) (xfeat : ι → H) (S : ℕ → Finset ι) (yhat : ℕ → H)
    (horth : path_orthogonality y xfeat S yhat) {m : ℕ} (b : ℕ) {l : ι} (hl : l ∈ S m) :
    ⟪xfeat l, yhat b - y⟫ = ⟪xfeat l, yhat b - yhat m⟫ := by
  have h0 : ⟪xfeat l, yhat m - y⟫ = 0 := horth.2.1 m l hl
  have hsplit : yhat b - yhat m = (yhat b - y) - (yhat m - y) := by abel
  rw [hsplit, inner_sub_right (𝕜 := ℝ) (xfeat l) (yhat b - y) (yhat m - y), h0, sub_zero]

@[blueprint "lem:predictor-distance-le-sqrt-total"
  (statement := /-- Let $H$ be a real inner product space, let $y \in H$, let $x : \iota \to H$,
  let $S : \mathbb{N} \to \mathrm{Finset}(\iota)$ and let $\hat{y} : \mathbb{N} \to H$ be
  path-orthogonal for $(y, x, S)$ in the sense of \cref{def:path-orthogonality}. Let
  $a, m, b \in \mathbb{N}$ satisfy $a \le m \le b$ and let $\varepsilon \in \mathbb{R}$ satisfy
  $\varepsilon \ge 0$ and $\mathrm{MSE}(\hat{y}_a) - \mathrm{MSE}(\hat{y}_b) = \varepsilon$, with
  $\mathrm{MSE}$ as in \cref{def:mse}. Then
  \[ \bigl\|\hat{y}_b - \hat{y}_m\bigr\| \le \sqrt{(b - a)\,\varepsilon} . \] -/)
  (proof := /-- By \cref{lem:predictor-distance-bound}, applied with $a \le m \le b$ and the
  hypothesis $\mathrm{MSE}(\hat{y}_a) - \mathrm{MSE}(\hat{y}_b) = \varepsilon$,
  \[ \bigl\|\hat{y}_b - \hat{y}_m\bigr\|^2 \le (b - m)\,\varepsilon . \]
  From $a \le m$ we get $b - m \le b - a$ for the truncated difference of natural numbers, hence
  the same inequality between their real casts; multiplying it by $\varepsilon \ge 0$ gives
  $(b - m)\varepsilon \le (b - a)\varepsilon$. Chaining the two inequalities,
  \[ \bigl\|\hat{y}_b - \hat{y}_m\bigr\|^2 \le (b - a)\,\varepsilon . \]
  The real number $(b - a)\varepsilon$ is nonnegative, being a product of the nonnegative cast
  $b - a$ with $\varepsilon \ge 0$, and $\|\hat{y}_b - \hat{y}_m\| \ge 0$ because it is a norm. For
  nonnegative reals $u$ and $v$ one has $u \le \sqrt{v}$ if and only if $u^2 \le v$; applying this
  equivalence with $u = \|\hat{y}_b - \hat{y}_m\|$ and $v = (b - a)\varepsilon$ to the last display
  yields the assertion. -/)
  (title := /-- L2 Distance to a Later Predictor via the Total Improvement -/)
  (latexEnv := "lemma")]
lemma predictor_distance_le_sqrt_total {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (y : H) (xfeat : ι → H) (S : ℕ → Finset ι) (yhat : ℕ → H)
    (horth : path_orthogonality y xfeat S yhat) {a m b : ℕ} (ham : a ≤ m) (hmb : m ≤ b)
    {ε : ℝ} (hεnonneg : 0 ≤ ε) (hε : mse y (yhat a) - mse y (yhat b) = ε) :
    ‖yhat b - yhat m‖ ≤ Real.sqrt (((b - a : ℕ) : ℝ) * ε) := by
  have hpd : ‖yhat b - yhat m‖ ^ 2 ≤ ((b - m : ℕ) : ℝ) * ε :=
    predictor_distance_bound y xfeat S yhat horth ham hmb hε
  have hmono : ((b - m : ℕ) : ℝ) * ε ≤ ((b - a : ℕ) : ℝ) * ε :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le_sub_left ham b)) hεnonneg
  have hnonneg : (0 : ℝ) ≤ ((b - a : ℕ) : ℝ) * ε := mul_nonneg (Nat.cast_nonneg _) hεnonneg
  exact (Real.le_sqrt (norm_nonneg _) hnonneg).mpr (hpd.trans hmono)

@[blueprint "lem:feature-residual-bound"
  (statement := /-- Let $H$ be a real inner product space, let $y \in H$, let $x : \iota \to H$,
  let $S : \mathbb{N} \to \mathrm{Finset}(\iota)$ and let $\hat{y} : \mathbb{N} \to H$ be
  path-orthogonal for $(y, x, S)$ in the sense of \cref{def:path-orthogonality}. Let
  $a, m, b \in \mathbb{N}$ satisfy $a \le m \le b$, let $\varepsilon \in \mathbb{R}$ satisfy
  $\varepsilon \ge 0$ and $\mathrm{MSE}(\hat{y}_a) - \mathrm{MSE}(\hat{y}_b) = \varepsilon$ with
  $\mathrm{MSE}$ as in \cref{def:mse}, let $l \in S_m$ be a feature index observed by the agent at
  position $m$, and let $M_X \in \mathbb{R}$ satisfy $M_X \ge 0$ and $\|x_l\| \le M_X$. Then
  \[ \bigl|\mathbb{E}[x_l(\hat{y}_b - y)]\bigr| \le M_X \sqrt{(b - a)\,\varepsilon} . \] -/)
  (proof := /-- By \cref{lem:feature-residual-inner-shift}, applied at the position $m$ with the
  feature index $l \in S_m$, the prediction $\hat{y}_m$ may be inserted in place of the target:
  \[ \mathbb{E}[x_l(\hat{y}_b - y)] = \mathbb{E}[x_l(\hat{y}_b - \hat{y}_m)] . \]
  It therefore suffices to bound $\bigl|\mathbb{E}[x_l(\hat{y}_b - \hat{y}_m)]\bigr|$. By the
  Cauchy-Schwarz inequality for the real inner product,
  \[ \bigl|\mathbb{E}[x_l(\hat{y}_b - \hat{y}_m)]\bigr|
     \le \|x_l\| \cdot \bigl\|\hat{y}_b - \hat{y}_m\bigr\| . \]
  By \cref{lem:predictor-distance-le-sqrt-total}, applied with $a \le m \le b$, with
  $\varepsilon \ge 0$ and with
  $\mathrm{MSE}(\hat{y}_a) - \mathrm{MSE}(\hat{y}_b) = \varepsilon$,
  \[ \bigl\|\hat{y}_b - \hat{y}_m\bigr\| \le \sqrt{(b - a)\,\varepsilon} . \]
  We now combine the two estimates. Since $\|x_l\| \ge 0$, multiplying the last inequality by
  $\|x_l\|$ gives
  $\|x_l\| \cdot \|\hat{y}_b - \hat{y}_m\| \le \|x_l\| \sqrt{(b-a)\varepsilon}$. Since
  $\sqrt{(b-a)\varepsilon} \ge 0$, the hypothesis $\|x_l\| \le M_X$ gives
  $\|x_l\| \sqrt{(b-a)\varepsilon} \le M_X \sqrt{(b-a)\varepsilon}$. Chaining the four displayed
  relations yields
  \[ \bigl|\mathbb{E}[x_l(\hat{y}_b - y)]\bigr| \le M_X \sqrt{(b - a)\varepsilon} , \]
  as asserted. -/)
  (title := /-- Correlation of a Feature with the Final Residual -/)
  (latexEnv := "lemma")]
lemma feature_residual_bound {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (y : H) (xfeat : ι → H) (S : ℕ → Finset ι) (yhat : ℕ → H)
    (horth : path_orthogonality y xfeat S yhat) {a m b : ℕ} (ham : a ≤ m) (hmb : m ≤ b)
    {ε : ℝ} (hεnonneg : 0 ≤ ε) (hε : mse y (yhat a) - mse y (yhat b) = ε)
    {l : ι} (hl : l ∈ S m) {MX : ℝ} (hMX : 0 ≤ MX) (hxl : ‖xfeat l‖ ≤ MX) :
    |⟪xfeat l, yhat b - y⟫| ≤ MX * Real.sqrt (((b - a : ℕ) : ℝ) * ε) := by
  have hshift : ⟪xfeat l, yhat b - y⟫ = ⟪xfeat l, yhat b - yhat m⟫ :=
    feature_residual_inner_shift y xfeat S yhat horth b hl
  have hcs : |⟪xfeat l, yhat b - yhat m⟫| ≤ ‖xfeat l‖ * ‖yhat b - yhat m‖ :=
    abs_real_inner_le_norm _ _
  have hdist : ‖yhat b - yhat m‖ ≤ Real.sqrt (((b - a : ℕ) : ℝ) * ε) :=
    predictor_distance_le_sqrt_total y xfeat S yhat horth ham hmb hεnonneg hε
  calc |⟪xfeat l, yhat b - y⟫| = |⟪xfeat l, yhat b - yhat m⟫| := by rw [hshift]
    _ ≤ ‖xfeat l‖ * ‖yhat b - yhat m‖ := hcs
    _ ≤ ‖xfeat l‖ * Real.sqrt (((b - a : ℕ) : ℝ) * ε) :=
        mul_le_mul_of_nonneg_left hdist (norm_nonneg _)
    _ ≤ MX * Real.sqrt (((b - a : ℕ) : ℝ) * ε) :=
        mul_le_mul_of_nonneg_right hxl (Real.sqrt_nonneg _)

@[blueprint "lem:inner-abs-le-weighted-sum"
  (statement := /-- Let $H$ be a real inner product space, let $\iota$ be a type, let
  $\alpha : \iota \to \mathbb{R}$, let $x : \iota \to H$, let $F$ be a finite subset of $\iota$ and
  let $r \in H$. Then, writing $\mathbb{E}[uv] = \langle u, v \rangle$ as in \cref{def:mse},
  \[ \Bigl|\mathbb{E}\Bigl[\Bigl(\sum_{l \in F} \alpha_l x_l\Bigr) r\Bigr]\Bigr|
     \le \sum_{l \in F} |\alpha_l| \cdot \bigl|\mathbb{E}[x_l r]\bigr| . \] -/)
  (proof := /-- The inner product is additive in its first argument, so it commutes with the finite
  sum $\sum_{l \in F} \alpha_l x_l$, and it is homogeneous in its first argument over the real
  scalars, so $\langle \alpha_l x_l, r \rangle = \alpha_l \langle x_l, r \rangle$ for every
  $l \in F$. Applying the first fact and then the second one summand at a time gives
  \[ \Bigl\langle \sum_{l \in F} \alpha_l x_l, r \Bigr\rangle
     = \sum_{l \in F} \bigl\langle \alpha_l x_l, r \bigr\rangle
     = \sum_{l \in F} \alpha_l \langle x_l, r \rangle . \]
  It therefore suffices to bound $\bigl|\sum_{l \in F} \alpha_l \langle x_l, r \rangle\bigr|$. By the
  triangle inequality for the absolute value on a finite sum of real numbers,
  \[ \Bigl|\sum_{l \in F} \alpha_l \langle x_l, r \rangle\Bigr|
     \le \sum_{l \in F} \bigl|\alpha_l \langle x_l, r \rangle\bigr| , \]
  and since the absolute value is multiplicative on $\mathbb{R}$, each summand satisfies
  $\bigl|\alpha_l \langle x_l, r \rangle\bigr| = |\alpha_l| \cdot |\langle x_l, r \rangle|$, so the
  two sums are equal term by term. Chaining the displayed identity, the triangle inequality and this
  term-by-term identity yields the assertion. -/)
  (title := /-- Weighted Triangle Inequality for a Linear Combination Against a Fixed Vector -/)
  (latexEnv := "lemma")]
lemma inner_abs_le_weighted_sum {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (α : ι → ℝ) (xfeat : ι → H) (F : Finset ι) (r : H) :
    |⟪∑ l ∈ F, α l • xfeat l, r⟫| ≤ ∑ l ∈ F, |α l| * |⟪xfeat l, r⟫| := by
  have hexp : ⟪∑ l ∈ F, α l • xfeat l, r⟫ = ∑ l ∈ F, α l * ⟪xfeat l, r⟫ := by
    rw [sum_inner]
    exact Finset.sum_congr rfl fun l _ => real_inner_smul_left _ _ _
  rw [hexp]
  calc |∑ l ∈ F, α l * ⟪xfeat l, r⟫| ≤ ∑ l ∈ F, |α l * ⟪xfeat l, r⟫| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ l ∈ F, |α l| * |⟪xfeat l, r⟫| :=
        Finset.sum_congr rfl fun l _ => abs_mul _ _

@[blueprint "lem:feature-residual-bound-on-union"
  (statement := /-- Let $H$ be a real inner product space, let $y \in H$, let $x : \iota \to H$ with
  $\iota$ carrying decidable equality, let $S : \mathbb{N} \to \mathrm{Finset}(\iota)$ and let
  $\hat{y} : \mathbb{N} \to H$ be path-orthogonal for $(y, x, S)$ in the sense of
  \cref{def:path-orthogonality}. Let $a, b \in \mathbb{N}$, let $\varepsilon \in \mathbb{R}$ satisfy
  $\varepsilon \ge 0$ and $\mathrm{MSE}(\hat{y}_a) - \mathrm{MSE}(\hat{y}_b) = \varepsilon$ with
  $\mathrm{MSE}$ as in \cref{def:mse}, and let $l \in \bigcup_{m \in (a, b]} S_m$ be a feature index
  observed by at least one agent at a position in $(a, b]$. Let $M_X \in \mathbb{R}$ satisfy
  $M_X \ge 0$ and $\mathbb{E}[x_l^2] \le M_X^2$. Then
  \[ \bigl|\mathbb{E}[x_l(\hat{y}_b - y)]\bigr| \le M_X \sqrt{(b - a)\,\varepsilon} . \] -/)
  (proof := /-- By the description of membership in a union indexed by a finite set, the hypothesis
  $l \in \bigcup_{m \in (a, b]} S_m$ provides a position $m$ with $m \in (a, b]$ and $l \in S_m$.
  From $m \in (a, b]$ we get $a < m$, hence $a \le m$, and also $m \le b$.

  The hypotheses $\mathbb{E}[x_l^2] \le M_X^2$ and $M_X \ge 0$ give $\|x_l\| \le M_X$ by
  \cref{lem:feature-norm-bound}, applied to the vector $x_l$.

  Now apply \cref{lem:feature-residual-bound} with this position $m$, for which $a \le m \le b$
  holds, with the feature index $l \in S_m$, with the hypotheses $\varepsilon \ge 0$ and
  $\mathrm{MSE}(\hat{y}_a) - \mathrm{MSE}(\hat{y}_b) = \varepsilon$, and with the bound
  $\|x_l\| \le M_X$ just established. It yields
  $\bigl|\mathbb{E}[x_l(\hat{y}_b - y)]\bigr| \le M_X \sqrt{(b - a)\varepsilon}$, which is the
  assertion. -/)
  (title := /-- Correlation of a Feature of the Subsequence with the Final Residual -/)
  (latexEnv := "lemma")]
lemma feature_residual_bound_on_union {ι H : Type*} [DecidableEq ι] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (y : H) (xfeat : ι → H) (S : ℕ → Finset ι) (yhat : ℕ → H)
    (horth : path_orthogonality y xfeat S yhat) {a b : ℕ} {ε : ℝ} (hεnonneg : 0 ≤ ε)
    (hε : mse y (yhat a) - mse y (yhat b) = ε) {l : ι} (hl : l ∈ (Finset.Ioc a b).biUnion S)
    {MX : ℝ} (hMX : 0 ≤ MX) (hmom : ⟪xfeat l, xfeat l⟫ ≤ MX ^ 2) :
    |⟪xfeat l, yhat b - y⟫| ≤ MX * Real.sqrt (((b - a : ℕ) : ℝ) * ε) := by
  obtain ⟨m, hm, hlm⟩ := Finset.mem_biUnion.mp hl
  obtain ⟨ham, hmb⟩ := Finset.mem_Ioc.mp hm
  exact feature_residual_bound y xfeat S yhat horth ham.le hmb hεnonneg hε hlm hMX
    (feature_norm_bound (xfeat l) hMX hmom)

@[blueprint "lem:comparator-correlation-bound"
  (statement := /-- Let $H$ be a real inner product space, let $y \in H$, let $x : \iota \to H$ with
  $\iota$ carrying decidable equality, let $S : \mathbb{N} \to \mathrm{Finset}(\iota)$ and let
  $\hat{y} : \mathbb{N} \to H$ be path-orthogonal for $(y, x, S)$ in the sense of
  \cref{def:path-orthogonality}. Let $a, b \in \mathbb{N}$ with $a < b$, and let
  $F = \bigcup_{m \in (a, b]} S_m$ be the union of the feature index sets of the agents at the
  positions $a+1, \ldots, b$ of the path. Let $\alpha : \iota \to \mathbb{R}$ and let
  $g = \sum_{l \in F} \alpha_l x_l$ be the associated linear predictor. Assume
  \[ \sum_{l \in F} |\alpha_l| \le A_g, \qquad
     \mathbb{E}[x_l^2] \le M_X^2 \ \text{ for all } l \in F, \qquad M_X \ge 0, \]
  and let $\varepsilon \in \mathbb{R}$ satisfy $\varepsilon \ge 0$ and
  $\mathrm{MSE}(\hat{y}_a) - \mathrm{MSE}(\hat{y}_b) = \varepsilon$, with $\mathrm{MSE}$ as in
  \cref{def:mse}. Then
  \[ \bigl|\mathbb{E}[g(\hat{y}_b - y)]\bigr| \le A_g M_X \sqrt{(b - a)\,\varepsilon} . \] -/)
  (proof := /-- Write $r = \hat{y}_b - y$ for the final residual. Expanding $g$ by linearity of the
  inner product in its first argument and abbreviate $B = M_X \sqrt{(b - a)\varepsilon}$. The
  quantity $B$ is nonnegative, being the product of $M_X \ge 0$ with a square root.

  For every $l \in F$ the hypotheses of \cref{lem:feature-residual-bound-on-union} are met: the
  family $\hat{y}$ is path-orthogonal for $(y, x, S)$, we have $\varepsilon \ge 0$ and
  $\mathrm{MSE}(\hat{y}_a) - \mathrm{MSE}(\hat{y}_b) = \varepsilon$, the index $l$ lies in
  $F = \bigcup_{m \in (a, b]} S_m$, and $M_X \ge 0$ with $\mathbb{E}[x_l^2] \le M_X^2$ by the
  second-moment hypothesis applied at $l$. That lemma therefore gives
  $\bigl|\mathbb{E}[x_l r]\bigr| \le B$, and multiplying this inequality by the nonnegative factor
  $|\alpha_l|$ yields
  \[ |\alpha_l| \cdot \bigl|\mathbb{E}[x_l r]\bigr| \le |\alpha_l| \, B
     \qquad \text{for every } l \in F . \]

  We now estimate the left-hand side of the assertion in four steps. First, by
  \cref{lem:inner-abs-le-weighted-sum}, applied to the coefficients $\alpha$, the features $x$, the
  finite index set $F$ and the vector $r$,
  \[ \bigl|\mathbb{E}[g \cdot r]\bigr|
     \le \sum_{l \in F} |\alpha_l| \cdot \bigl|\mathbb{E}[x_l r]\bigr| . \]
  Second, summing the displayed pointwise bound over the finite set $F$, which preserves the
  inequality term by term,
  \[ \sum_{l \in F} |\alpha_l| \cdot \bigl|\mathbb{E}[x_l r]\bigr|
     \le \sum_{l \in F} |\alpha_l| \, B . \]
  Third, the constant $B$ factors out of the finite sum, so
  $\sum_{l \in F} |\alpha_l| \, B = \bigl(\sum_{l \in F} |\alpha_l|\bigr) B$. Fourth, the hypothesis
  $\sum_{l \in F} |\alpha_l| \le A_g$ multiplied by $B \ge 0$ gives
  $\bigl(\sum_{l \in F} |\alpha_l|\bigr) B \le A_g B$. Chaining the four steps and using
  associativity of multiplication to rewrite
  $A_g B = A_g M_X \sqrt{(b - a)\varepsilon}$ gives the assertion. -/)
  (title := /-- Correlation of the Comparison Predictor with the Final Residual -/)
  (latexEnv := "lemma")]
lemma comparator_correlation_bound {ι H : Type*} [DecidableEq ι] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (y : H) (xfeat : ι → H) (S : ℕ → Finset ι) (yhat : ℕ → H)
    (horth : path_orthogonality y xfeat S yhat) (α : ι → ℝ) {a b : ℕ} (hab : a < b)
    {ε : ℝ} (hεnonneg : 0 ≤ ε) (hε : mse y (yhat a) - mse y (yhat b) = ε) {Ag MX : ℝ}
    (hAg : ∑ l ∈ (Finset.Ioc a b).biUnion S, |α l| ≤ Ag) (hMX : 0 ≤ MX)
    (hmom : ∀ l ∈ (Finset.Ioc a b).biUnion S, ⟪xfeat l, xfeat l⟫ ≤ MX ^ 2) :
    |⟪∑ l ∈ (Finset.Ioc a b).biUnion S, α l • xfeat l, yhat b - y⟫|
      ≤ Ag * MX * Real.sqrt (((b - a : ℕ) : ℝ) * ε) := by
  set F := (Finset.Ioc a b).biUnion S with hF
  set B := MX * Real.sqrt (((b - a : ℕ) : ℝ) * ε) with hB
  have hBnonneg : 0 ≤ B := mul_nonneg hMX (Real.sqrt_nonneg _)
  have hterm : ∀ l ∈ F, |α l| * |⟪xfeat l, yhat b - y⟫| ≤ |α l| * B := fun l hl =>
    mul_le_mul_of_nonneg_left
      (feature_residual_bound_on_union y xfeat S yhat horth hεnonneg hε hl hMX (hmom l hl))
      (abs_nonneg _)
  calc |⟪∑ l ∈ F, α l • xfeat l, yhat b - y⟫|
      ≤ ∑ l ∈ F, |α l| * |⟪xfeat l, yhat b - y⟫| :=
        inner_abs_le_weighted_sum α xfeat F (yhat b - y)
    _ ≤ ∑ l ∈ F, |α l| * B := Finset.sum_le_sum hterm
    _ = (∑ l ∈ F, |α l|) * B := (Finset.sum_mul _ _ _).symm
    _ ≤ Ag * B := mul_le_mul_of_nonneg_right hAg hBnonneg
    _ = Ag * MX * Real.sqrt (((b - a : ℕ) : ℝ) * ε) := by rw [hB, mul_assoc]

@[blueprint "thm:small-improvement-path"
  (statement := /-- (Competing with bounded-norm predictors on a path.) Let $H$ be a real inner
  product space, understood as $L^2(\mathcal{D})$ as in \cref{def:mse}, let $y \in H$ be the target,
  let $x : \iota \to H$ be the feature variables with $\iota$ carrying decidable equality, let
  $S : \mathbb{N} \to \mathrm{Finset}(\iota)$ record the feature index set observed by the agent at
  each position of the path, and let $\hat{y} : \mathbb{N} \to H$ record the agents' predictions
  along the path, assumed path-orthogonal for $(y, x, S)$ in the sense of
  \cref{def:path-orthogonality}. Let $a, b \in \mathbb{N}$ with $a < b$; here $a$ is the position
  immediately preceding the subsequence and $b$ is its last position, so that the subsequence
  consists of the positions $a+1, \ldots, b$ and $N_{\mathrm{path}} = b - a$ is the number of agents
  on it. Let $F = \bigcup_{m \in (a, b]} S_m$ be the union of the feature index sets of the agents on
  the subsequence, let $\alpha : \iota \to \mathbb{R}$ and let $g = \sum_{l \in F} \alpha_l x_l$ be
  the comparison linear predictor. Assume:
  \begin{enumerate}
    \item the total improvement satisfies
      $\mathrm{MSE}(\hat{y}_a) - \mathrm{MSE}(\hat{y}_b) = \varepsilon_{\mathrm{path}}$ with
      $\varepsilon_{\mathrm{path}} \ge 0$;
    \item the coefficients have bounded $\ell^1$ norm, $\sum_{l \in F} |\alpha_l| \le A_g$;
    \item the features have bounded second moments, $\mathbb{E}[x_l^2] \le M_X^2$ for all
      $l \in F$, where $M_X \ge 0$.
  \end{enumerate}
  Then
  \[ \mathrm{MSE}(\hat{y}_b) \le \mathrm{MSE}(g)
     + 2 A_g M_X \sqrt{N_{\mathrm{path}}} \cdot \sqrt{\varepsilon_{\mathrm{path}}} , \]
  that is, $\mathrm{MSE}(\hat{y}_b) \le \mathrm{MSE}(g) + C\sqrt{\varepsilon_{\mathrm{path}}}$ with
  $C = 2 A_g M_X \sqrt{N_{\mathrm{path}}}$. -/)
  (proof := /-- Abbreviate $\varepsilon = \varepsilon_{\mathrm{path}}$ and
  $N = N_{\mathrm{path}} = b - a$. By \cref{lem:mse-competitive-bound}, applied with
  $f = \hat{y}_b$ and the comparison predictor $g$,
  \[ \mathrm{MSE}(\hat{y}_b) \le \mathrm{MSE}(g)
     + 2\bigl|\mathbb{E}[g(\hat{y}_b - y)]\bigr|
     + 2\bigl|\mathbb{E}[\hat{y}_b(\hat{y}_b - y)]\bigr| . \]
  The last term vanishes: by the first clause of \cref{def:path-orthogonality} applied at position
  $b$, the predictor $\hat{y}_b$ is self-orthogonal, so
  $\mathbb{E}[\hat{y}_b(\hat{y}_b - y)] = 0$. It therefore remains to bound
  $\bigl|\mathbb{E}[g(\hat{y}_b - y)]\bigr|$, and by
  \cref{lem:comparator-correlation-bound}, whose hypotheses are exactly assumptions (1)-(3)
  together with $a < b$ and path-orthogonality,
  \[ \bigl|\mathbb{E}[g(\hat{y}_b - y)]\bigr| \le A_g M_X \sqrt{N \varepsilon} . \]
  Since $N \ge 0$, the square root is multiplicative on the factorisation $N\varepsilon$, that is
  $\sqrt{N\varepsilon} = \sqrt{N}\sqrt{\varepsilon}$. Substituting the two displays gives
  \[ \mathrm{MSE}(\hat{y}_b) \le \mathrm{MSE}(g) + 2 A_g M_X \sqrt{N} \sqrt{\varepsilon} , \]
  which is the assertion with $C = 2 A_g M_X \sqrt{N}$. -/)
  (title := /-- Competing with Bounded-Norm Predictors on a Path -/)
  (latexEnv := "theorem")]
theorem small_improvement_path {ι H : Type*} [DecidableEq ι] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (y : H) (xfeat : ι → H) (S : ℕ → Finset ι) (yhat : ℕ → H)
    (horth : path_orthogonality y xfeat S yhat) (α : ι → ℝ) {a b : ℕ} (hab : a < b)
    {ε : ℝ} (hεnonneg : 0 ≤ ε) (hε : mse y (yhat a) - mse y (yhat b) = ε) {Ag MX : ℝ}
    (hAg : ∑ l ∈ (Finset.Ioc a b).biUnion S, |α l| ≤ Ag) (hMX : 0 ≤ MX)
    (hmom : ∀ l ∈ (Finset.Ioc a b).biUnion S, ⟪xfeat l, xfeat l⟫ ≤ MX ^ 2) :
    mse y (yhat b) ≤ mse y (∑ l ∈ (Finset.Ioc a b).biUnion S, α l • xfeat l)
      + 2 * Ag * MX * Real.sqrt ((b - a : ℕ) : ℝ) * Real.sqrt ε := by
  have hself : ⟪yhat b, yhat b - y⟫ = 0 := horth.1 b
  have hcomp := mse_competitive_bound y (yhat b) (∑ l ∈ (Finset.Ioc a b).biUnion S, α l • xfeat l)
  have hcorr := comparator_correlation_bound y xfeat S yhat horth α hab hεnonneg hε hAg hMX hmom
  have hsqrt : Real.sqrt (((b - a : ℕ) : ℝ) * ε)
      = Real.sqrt ((b - a : ℕ) : ℝ) * Real.sqrt ε :=
    Real.sqrt_mul (Nat.cast_nonneg _) ε
  rw [hsqrt] at hcorr
  rw [hself, abs_zero] at hcomp
  linarith [hcomp, hcorr]

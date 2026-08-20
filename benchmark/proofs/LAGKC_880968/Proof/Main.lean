import Architect
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Topology.MetricSpace.Defs

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators

@[blueprint "def:single-center-cost"
  (statement := /-- Let $V$ be a metric space, let $X\subseteq V$ be finite, let $q\in\mathbb N$, and let $c\in V$.  The single-center $\ell_q$ cost of $X$ at $c$ is
  \[
    \operatorname{cost}_q(X,c)=\sum_{x\in X}d(x,c)^q.
  \] -/)
  (title := /-- Single-center clustering cost -/)
  (latexEnv := "definition")]
noncomputable def single_center_cost {V : Type*} [MetricSpace V]
    (q : ℕ) (points : Finset V) (center : V) : ℝ :=
  ∑ point ∈ points, dist point center ^ q

@[blueprint "def:trimmed-single-center-cost"
  (statement := /-- Let $V$ be a metric space, let $X\subseteq V$ be finite, let $q\in\mathbb N$, let $\alpha\in\mathbb R$, and let $c\in V$.  The $\alpha$-trimmed single-center cost is
  \[
    \operatorname{tcost}_{q,\alpha}(X,c)
      =\inf\left\{\operatorname{cost}_q(Y,c):
        Y\subseteq X,\ (1-\alpha)|X|\leq |Y|\right\}.
  \]
  Thus a feasible core may discard at most an $\alpha$ fraction of $X$.  In the applications below, $0<\alpha<1/2$; because the family of cores is then finite and nonempty, the infimum is attained. -/)
  (title := /-- Trimmed single-center clustering cost -/)
  (latexEnv := "definition")]
noncomputable def trimmed_single_center_cost {V : Type*} [MetricSpace V]
    [DecidableEq V] (q : ℕ) (alpha : ℝ) (points : Finset V) (center : V) : ℝ :=
  sInf {value : ℝ | ∃ core : Finset V,
    core ⊆ points ∧
      (1 - alpha) * (points.card : ℝ) ≤ (core.card : ℝ) ∧
      value = single_center_cost q core center}

@[blueprint "def:distance-to-centers"
  (statement := /-- Let $V$ be a metric space, let $q\in\mathbb N$, let $C\subseteq V$ be finite, and let $x\in V$.  The $q$-power distance from $x$ to $C$ is
  \[
    d_q(x,C)=\inf_{c\in C}d(x,c)^q.
  \]
  In every subsequent use, $C$ has positive cardinality, so this infimum is a minimum. -/)
  (title := /-- Distance cost to a finite center set -/)
  (latexEnv := "definition")]
noncomputable def distance_to_centers {V : Type*} [MetricSpace V]
    (q : ℕ) (centers : Finset V) (point : V) : ℝ :=
  sInf ((fun center : V => dist point center ^ q) '' (centers : Set V))

@[blueprint "def:clustering-cost"
  (statement := /-- Let $V$ be a metric space, let $X,C\subseteq V$ be finite, and let $q\in\mathbb N$.  Using \cref{def:distance-to-centers}, define
  \[
    \operatorname{cost}_q(X,C)=\sum_{x\in X}d_q(x,C).
  \] -/)
  (title := /-- Finite metric clustering cost -/)
  (latexEnv := "definition")]
noncomputable def clustering_cost {V : Type*} [MetricSpace V]
    (q : ℕ) (points centers : Finset V) : ℝ :=
  ∑ point ∈ points, distance_to_centers q centers point

@[blueprint "def:optimal-clustering-cost"
  (statement := /-- Let $V$ be a finite metric space, let $X\subseteq V$ be finite, and let $k,q\in\mathbb N$.  Using \cref{def:clustering-cost}, define the optimal $k$-clustering cost by
  \[
    \operatorname{OPT}_q(X,k)
      =\inf\{\operatorname{cost}_q(X,C): C\subseteq V,\ |C|=k\}.
  \]
  The target theorem assumes $1\leq k\leq |V|$, so the feasible family is nonempty. -/)
  (title := /-- Optimal finite metric clustering cost -/)
  (latexEnv := "definition")]
noncomputable def optimal_clustering_cost {V : Type*} [MetricSpace V]
    (q k : ℕ) (points : Finset V) : ℝ :=
  sInf {value : ℝ | ∃ centers : Finset V,
    centers.card = k ∧ value = clustering_cost q points centers}

@[blueprint "def:predictor-label-error"
  (statement := /-- Let $X$ be a finite subset of a finite metric space $V$, let $k,q\in\mathbb N$, let $0\leq\lambda\leq\alpha$, and let $\Pi,L:X\to\{0,\ldots,k-1\}$ be respectively a predicted and a reference labeling.  Let $c_i\in V$ be the reference center of label $i$, and require $c_{L(x)}$ to minimize the distance from $x$ among the reference centers; when several centers attain the minimum, $L(x)$ may select any of their labels.  The predictor has label error at most $\lambda$ relative to this $\alpha$-approximately optimal reference clustering if the centers $c_i$ are pairwise distinct,
  \[
    \sum_{i<k}\operatorname{cost}_q(\{x\in X:L(x)=i\},c_i)
      \leq (1+\alpha)\operatorname{OPT}_q(X,k),
  \]
  and, for every label $i$, both the number of reference-$i$ points not predicted as $i$ and the number of predicted-$i$ points whose reference label is not $i$ are at most a $\lambda$ fraction of the corresponding reference and predicted classes. -/)
  (title := /-- Precision-and-recall label error -/)
  (latexEnv := "definition")]
noncomputable def predictor_label_error {V : Type*} [MetricSpace V] [Fintype V]
    [DecidableEq V] (points : Finset V) (k q : ℕ) (alpha lambda : ℝ)
    (predictor referenceLabel : V → Fin k) (referenceCenter : Fin k → V) : Prop :=
  0 ≤ lambda ∧ lambda ≤ alpha ∧ Function.Injective referenceCenter ∧
    (∀ point ∈ points,
      ∀ label : Fin k,
        dist point (referenceCenter (referenceLabel point)) ≤
          dist point (referenceCenter label)) ∧
    (∑ label : Fin k,
      single_center_cost q (points.filter fun point => referenceLabel point = label)
        (referenceCenter label)) ≤
      (1 + alpha) * optimal_clustering_cost q k points ∧
    ∀ label : Fin k,
      ((points.filter fun point =>
          referenceLabel point = label ∧ predictor point ≠ label).card : ℝ) ≤
        lambda * ((points.filter fun point => referenceLabel point = label).card : ℝ) ∧
      ((points.filter fun point =>
          predictor point = label ∧ referenceLabel point ≠ label).card : ℝ) ≤
        lambda * ((points.filter fun point => predictor point = label).card : ℝ)

@[blueprint "def:costed-computation"
  (statement := /-- A costed computation with output type $A$ consists of its output together with the number of primitive steps performed to obtain it.  The step count is part of the computation itself, rather than an independently supplied certificate. -/)
  (title := /-- Operationally costed computation -/)
  (latexEnv := "definition")]
structure costed_computation (A : Type*) where
  output : A
  steps : ℕ

@[blueprint "def:costed-then"
  (statement := /-- Given a costed computation $M$ and a continuation assigning a costed computation $N(a)$ to each possible output $a$ of $M$, their sequential composition first executes $M$ and then $N$ on its output.  Its output is that of the second computation, and its step count is the sum of the two step counts plus one composition step. -/)
  (title := /-- Sequential composition of costed computations -/)
  (latexEnv := "definition")]
def costed_then {A B : Type*} (first : costed_computation A)
    (next : A → costed_computation B) : costed_computation B :=
  let second := next first.output
  ⟨second.output, first.steps + second.steps + 1⟩

@[blueprint "def:costed-list-fold"
  (statement := /-- Let $b_1,\ldots,b_n$ be a list, let $a_0$ be an initial state, and suppose each state transition returns both its successor state and the primitive cost of computing it.  The costed left fold applies these transitions in order and records the sum of their costs, together with one loop step per list element. -/)
  (title := /-- Operationally costed list fold -/)
  (latexEnv := "definition")]
def costed_list_fold {A B : Type*} (items : List B) (initial : A)
    (step : A → B → costed_computation A) : costed_computation A :=
  items.foldl (fun computation item =>
    let successor := step computation.output item
    ⟨successor.output, computation.steps + successor.steps + 1⟩) ⟨initial, 0⟩

@[blueprint "def:get-center"
  (statement := /-- Let $V$ be a finite metric space, let $X\subseteq V$, let $q\in\mathbb N$, and let $\alpha\in\mathbb R$.  The routine $\operatorname{GetCenter}_{q,\alpha}(X)$ scans every $c\in V$.  For $q=1$ it minimizes $\operatorname{cost}_1(X,c)$; for $q=2$ it minimizes the robust score $\operatorname{tcost}_{2,\alpha}(X,c)$ from \cref{def:trimmed-single-center-cost}.  Ties are resolved by the fixed enumeration of $V$.  Computing a trimmed score amounts to selecting the required number of smallest squared residuals, and the recorded step bound charges a quadratic scan of $X$ for each comparison.  The result is optional only so that the same definition is total when $V$ is empty. -/)
  (title := /-- Robust GetCenter routine -/)
  (latexEnv := "definition")]
noncomputable def get_center {V : Type*} [MetricSpace V] [Fintype V]
    [DecidableEq V] (points : Finset V) (q : ℕ) (alpha : ℝ) :
    costed_computation (Option V) :=
  costed_list_fold (Finset.univ.toList : List V) (none : Option V)
    (fun current candidate =>
      let score := fun center : V =>
        if q = 2 then trimmed_single_center_cost q alpha points center
        else single_center_cost q points center
      let next := match current with
        | none => some candidate
        | some incumbent =>
            if score candidate < score incumbent then some candidate else some incumbent
      ⟨next, 2 * points.card ^ 2 + 2 * points.card + 1⟩)

@[blueprint "def:learning-augmented-k-clustering-algorithm"
  (statement := /-- A learning-augmented $k$-clustering algorithm is a single polymorphic procedure defined uniformly over all finite metric spaces.  On an input consisting of a finite point set $X\subseteq V$, a number $k$ of clusters, an exponent $q$, a real parameter $\alpha$, and a predictor $\Pi:V\to\{0,\ldots,k-1\}$, it returns an operationally costed computation, as in \cref{def:costed-computation}, whose output is a finite set of centers. -/)
  (title := /-- Uniform interface for learning-augmented clustering -/)
  (latexEnv := "definition")]
structure learning_augmented_k_clustering_algorithm where
  run : {V : Type} → [MetricSpace V] → [Fintype V] → [DecidableEq V] →
    Finset V → (k q : ℕ) → ℝ → (V → Fin k) → costed_computation (Finset V)

@[blueprint "def:algorithm-one"
  (statement := /-- Algorithm~1 is the fixed learning-augmented clustering procedure from the source, expressed in the operational model of \cref{def:costed-computation}.  For each predicted label $i\in\{0,\ldots,k-1\}$, it forms the predicted class $X_i=\{x\in X:\Pi(x)=i\}$ and invokes \cref{def:get-center}.  In particular, when $q=2$ the chosen center minimizes the trimmed squared-distance objective rather than the squared cost of the contaminated class itself.  Each comparison and loop iteration contributes to the step count through \cref{def:costed-list-fold}.  The selected centers are then padded, by a further finite scan, until either their cardinality is $k$ or every ambient point has been considered.  Thus both the returned center set and its running time arise from one finite sequence of operations; no independent runtime field is stipulated. -/)
  (title := /-- Algorithm 1 -/)
  (latexEnv := "definition")]
noncomputable def algorithm_one : learning_augmented_k_clustering_algorithm where
  run := fun {V} _ _ _ points k q alpha predictor =>
    let selected := costed_list_fold (Finset.univ.toList : List (Fin k)) ∅
      (fun centers label =>
        let predictedClass := points.filter fun point => predictor point = label
        let best := get_center predictedClass q alpha
        ⟨match best.output with
          | none => centers
          | some center => insert center centers,
          best.steps⟩)
    costed_then selected fun centers =>
      costed_list_fold (Finset.univ.toList : List V) centers
        (fun padded point =>
          ⟨if padded.card < k then insert point padded else padded, 1⟩)

@[blueprint "def:algorithm-runs-in-polynomial-time"
  (statement := /-- Let $A$ be a uniform learning-augmented clustering algorithm as in \cref{def:learning-augmented-k-clustering-algorithm}.  We say that $A$ runs in polynomial time in the finite-metric oracle model if there exist natural numbers $C>0$ and $d$, chosen independently of the input metric space, such that for every finite metric space $V$, every finite input set $X\subseteq V$, every $k,q,\alpha$, and every predictor $\Pi$, the operational step count of $A$ is at most
  \[
    C\,(|V|+k+1)^d.
  \] -/)
  (title := /-- Uniform polynomial running time -/)
  (latexEnv := "definition")]
def algorithm_runs_in_polynomial_time
    (algorithm : learning_augmented_k_clustering_algorithm) : Prop :=
  ∃ coefficient degree : ℕ, 0 < coefficient ∧
    ∀ {V : Type} [MetricSpace V] [Fintype V] [DecidableEq V]
      (points : Finset V) (k q : ℕ) (alpha : ℝ) (predictor : V → Fin k),
      (algorithm.run points k q alpha predictor).steps ≤
        coefficient * (Fintype.card V + k + 1) ^ degree

@[blueprint "lem:dominant-subset-linear-cost"
  (statement := /-- Let $V$ be a metric space, let $X=P\sqcup Q$ be finite, and let $0\leq\alpha<1$.  Suppose
  \[
    |P|\geq(1-\alpha)|X|,\qquad |Q|\leq\alpha|X|.
  \]
  If $C_P$ minimizes the single-center linear cost of $P$ and $C_X$ minimizes that of $X$, then
  \[
    \operatorname{cost}_1(X,C_P)
      \leq\left(1+\frac{2\alpha}{1-\alpha}\right)
        \operatorname{cost}_1(X,C_X).
  \] -/)
  (proof := /-- For each $p\in P$, the triangle inequality gives
  $d(C_P,C_X)\leq d(C_P,p)+d(p,C_X)$.  Summing over $P$ and using the minimality of $C_P$ yields
  \[
    |P|d(C_P,C_X)\leq 2\operatorname{cost}_1(P,C_X).
  \]
  For every $q\in Q$, another application of the triangle inequality gives
  $d(q,C_P)\leq d(q,C_X)+d(C_X,C_P)$.  Summing this inequality, using the minimality of $C_P$ on $P$, and then substituting the preceding bound gives
  \[
    \operatorname{cost}_1(X,C_P)
      \leq \operatorname{cost}_1(X,C_X)
        +\frac{2|Q|}{|P|}\operatorname{cost}_1(P,C_X).
  \]
  The cardinality hypotheses imply $|Q|/|P|\leq\alpha/(1-\alpha)$, and the asserted estimate follows from
  $\operatorname{cost}_1(P,C_X)\leq\operatorname{cost}_1(X,C_X)$. -/)
  (title := /-- Dominant-subset estimate for linear distance -/)
  (latexEnv := "lemma")]
lemma dominant_subset_linear_cost {V : Type*} [MetricSpace V] [DecidableEq V]
    (X P Q : Finset V) (centerP centerX : V) (alpha : ℝ)
    (hPartition : X = P ∪ Q) (hDisjoint : Disjoint P Q)
    (hAlphaNonneg : 0 ≤ alpha) (hAlphaLtOne : alpha < 1)
    (hP : (1 - alpha) * (X.card : ℝ) ≤ (P.card : ℝ))
    (hQ : (Q.card : ℝ) ≤ alpha * (X.card : ℝ))
    (hCenterP : ∀ center : V,
      single_center_cost 1 P centerP ≤ single_center_cost 1 P center)
    (hCenterX : ∀ center : V,
      single_center_cost 1 X centerX ≤ single_center_cost 1 X center) :
    single_center_cost 1 X centerP ≤
      (1 + 2 * alpha / (1 - alpha)) * single_center_cost 1 X centerX := by
  by_cases hX : X = ∅
  · simp [single_center_cost, hX]
  have hOneMinusAlpha : 0 < 1 - alpha := sub_pos.mpr hAlphaLtOne
  have hCostUnion (center : V) :
      single_center_cost 1 X center =
        single_center_cost 1 P center + single_center_cost 1 Q center := by
    rw [hPartition]
    simp [single_center_cost, Finset.sum_union hDisjoint]
  have hDistanceSum :
      (P.card : ℝ) * dist centerP centerX ≤
        2 * single_center_cost 1 P centerX := by
    calc
      (P.card : ℝ) * dist centerP centerX =
          ∑ point ∈ P, dist centerP centerX := by simp
      _ ≤ ∑ point ∈ P, (dist point centerP + dist point centerX) := by
        apply Finset.sum_le_sum
        intro point hPoint
        calc
          dist centerP centerX ≤ dist centerP point + dist point centerX :=
            dist_triangle centerP point centerX
          _ = dist point centerP + dist point centerX := by
            rw [dist_comm centerP point]
      _ = single_center_cost 1 P centerP + single_center_cost 1 P centerX := by
        simp [single_center_cost, Finset.sum_add_distrib]
      _ ≤ 2 * single_center_cost 1 P centerX := by
        nlinarith [hCenterP centerX]
  have hQCost :
      single_center_cost 1 Q centerP ≤
        single_center_cost 1 Q centerX +
          (Q.card : ℝ) * dist centerP centerX := by
    calc
      single_center_cost 1 Q centerP = ∑ point ∈ Q, dist point centerP := by
        simp [single_center_cost]
      _ ≤ ∑ point ∈ Q, (dist point centerX + dist centerP centerX) := by
        apply Finset.sum_le_sum
        intro point hPoint
        calc
          dist point centerP ≤ dist point centerX + dist centerX centerP :=
            dist_triangle point centerX centerP
          _ = dist point centerX + dist centerP centerX := by
            rw [dist_comm centerX centerP]
      _ = single_center_cost 1 Q centerX +
          (Q.card : ℝ) * dist centerP centerX := by
        simp [single_center_cost, Finset.sum_add_distrib]
  have hPCost :
      single_center_cost 1 P centerX ≤ single_center_cost 1 X centerX := by
    have hQCostNonneg : 0 ≤ single_center_cost 1 Q centerX := by
      unfold single_center_cost
      exact Finset.sum_nonneg fun point hPoint => pow_nonneg dist_nonneg 1
    rw [hCostUnion centerX]
    exact le_add_of_nonneg_right hQCostNonneg
  have hDistanceCost :
      (P.card : ℝ) * dist centerP centerX ≤
        2 * single_center_cost 1 X centerX := by
    exact hDistanceSum.trans (mul_le_mul_of_nonneg_left hPCost (by norm_num))
  have hCardCross :
      (1 - alpha) * (Q.card : ℝ) ≤ alpha * (P.card : ℝ) := by
    have hQScaled := mul_le_mul_of_nonneg_left hQ (le_of_lt hOneMinusAlpha)
    have hPScaled := mul_le_mul_of_nonneg_left hP hAlphaNonneg
    nlinarith
  have hQRatio :
      (Q.card : ℝ) ≤ alpha * (P.card : ℝ) / (1 - alpha) := by
    apply (le_div_iff₀ hOneMinusAlpha).2
    nlinarith [hCardCross]
  have hRemainder :
      (Q.card : ℝ) * dist centerP centerX ≤
        (2 * alpha / (1 - alpha)) * single_center_cost 1 X centerX := by
    have hRatioNonneg : 0 ≤ alpha / (1 - alpha) :=
      div_nonneg hAlphaNonneg (le_of_lt hOneMinusAlpha)
    calc
      (Q.card : ℝ) * dist centerP centerX ≤
          (alpha * (P.card : ℝ) / (1 - alpha)) * dist centerP centerX :=
        mul_le_mul_of_nonneg_right hQRatio dist_nonneg
      _ = (alpha / (1 - alpha)) *
          ((P.card : ℝ) * dist centerP centerX) := by ring
      _ ≤ (alpha / (1 - alpha)) *
          (2 * single_center_cost 1 X centerX) :=
        mul_le_mul_of_nonneg_left hDistanceCost hRatioNonneg
      _ = (2 * alpha / (1 - alpha)) * single_center_cost 1 X centerX := by ring
  have hTotal :
      single_center_cost 1 X centerP ≤
        single_center_cost 1 X centerX +
          (Q.card : ℝ) * dist centerP centerX := by
    calc
      single_center_cost 1 X centerP =
          single_center_cost 1 P centerP + single_center_cost 1 Q centerP :=
        hCostUnion centerP
      _ ≤ single_center_cost 1 P centerX +
          (single_center_cost 1 Q centerX +
            (Q.card : ℝ) * dist centerP centerX) :=
        add_le_add (hCenterP centerX) hQCost
      _ = single_center_cost 1 X centerX +
          (Q.card : ℝ) * dist centerP centerX := by
        rw [hCostUnion centerX]
        ring
  nlinarith [hTotal, hRemainder]

@[blueprint "lem:dominant-subset-squared-cost"
  (statement := /-- Let $V$ be a metric space, let $X=P\sqcup Q$ be finite, and let $0\leq\alpha<1/8$.  Suppose
  \[
    |P|\geq(1-\alpha)|X|,\qquad |Q|\leq\alpha|X|.
  \]
  If $C_P$ minimizes the single-center squared-distance cost of $P$ and $C_X$ minimizes that of $X$, then
  \[
    \operatorname{cost}_2(X,C_P)
      \leq\left(1+6\sqrt{\frac{\alpha}{1-\alpha}}\right)
        \operatorname{cost}_2(X,C_X).
  \] -/)
  (proof := /-- If $X$ is empty, the assertion is immediate.  If $\alpha=0$, the cardinality bound forces $Q=\varnothing$, so $X=P$ and the assertion follows from the minimality of $C_P$ on $P$.  Assume henceforth that $\alpha>0$, and put
  \[
    r=\frac{\alpha}{1-\alpha},\qquad s=\sqrt r,\qquad
    D=d(C_P,C_X),\qquad T=\operatorname{cost}_2(X,C_X).
  \]
  The hypothesis $\alpha<1/8$ implies $0<s\leq1/2$.  For every $p\in P$, the triangle inequality and $(a+b)^2\leq2a^2+2b^2$ give
  \[
    D^2\leq2d(p,C_P)^2+2d(p,C_X)^2.
  \]
  Summing over $P$ and using the minimality of $C_P$ yields
  \[
    |P|D^2\leq4\operatorname{cost}_2(P,C_X)\leq4T.
  \]
  The two cardinality hypotheses imply $|Q|\leq r|P|=s^2|P|$; hence
  \[
    |Q|D^2\leq4s^2T.
  \]
  For every $q\in Q$, the triangle inequality and the nonnegativity of
  $(2s\,d(q,C_X)-D)^2$ give
  \[
    2s\,d(q,C_P)^2
      \leq2s(1+2s)d(q,C_X)^2+(2s+1)D^2.
  \]
  After summing this inequality and applying the preceding displacement bound,
  \[
    2s\,\operatorname{cost}_2(Q,C_P)
      \leq2s(1+2s)\operatorname{cost}_2(Q,C_X)
        +4s^2(2s+1)T.
  \]
  Finally, $\operatorname{cost}_2(P,C_P)\leq
  \operatorname{cost}_2(P,C_X)$,
  $\operatorname{cost}_2(Q,C_X)\leq T$, and $2s\leq1$.  Adding these inequalities and expanding the coefficients gives
  \[
    \operatorname{cost}_2(X,C_P)\leq(1+6s)T,
  \]
  which is the claimed estimate. -/)
  (title := /-- Dominant-subset estimate for squared distance -/)
  (latexEnv := "lemma")]
lemma dominant_subset_squared_cost {V : Type*} [MetricSpace V] [DecidableEq V]
    (X P Q : Finset V) (centerP centerX : V) (alpha : ℝ)
    (hPartition : X = P ∪ Q) (hDisjoint : Disjoint P Q)
    (hAlphaNonneg : 0 ≤ alpha) (hAlphaLt : alpha < (1 : ℝ) / 8)
    (hP : (1 - alpha) * (X.card : ℝ) ≤ (P.card : ℝ))
    (hQ : (Q.card : ℝ) ≤ alpha * (X.card : ℝ))
    (hCenterP : ∀ center : V,
      single_center_cost 2 P centerP ≤ single_center_cost 2 P center)
    (hCenterX : ∀ center : V,
      single_center_cost 2 X centerX ≤ single_center_cost 2 X center) :
    single_center_cost 2 X centerP ≤
      (1 + 6 * Real.sqrt (alpha / (1 - alpha))) *
        single_center_cost 2 X centerX := by
  by_cases hXempty : X = ∅
  · simp [hXempty, single_center_cost]
  by_cases hAlphaZero : alpha = 0
  · subst alpha
    have hQcard : Q.card = 0 := by
      have hQcardReal : (Q.card : ℝ) = 0 := by
        apply le_antisymm
        · simpa using hQ
        · positivity
      exact_mod_cast hQcardReal
    have hQempty : Q = ∅ := Finset.card_eq_zero.mp hQcard
    rw [hQempty, Finset.union_empty] at hPartition
    subst X
    simpa using hCenterP centerX
  have hAlphaPos : 0 < alpha := lt_of_le_of_ne hAlphaNonneg (Ne.symm hAlphaZero)
  have hAlphaLtOne : alpha < 1 := by linarith
  have hOneMinusPos : 0 < 1 - alpha := sub_pos.mpr hAlphaLtOne
  let ratio : ℝ := alpha / (1 - alpha)
  let scale : ℝ := Real.sqrt ratio
  have hRatioPos : 0 < ratio := div_pos hAlphaPos hOneMinusPos
  have hScalePos : 0 < scale := Real.sqrt_pos.2 hRatioPos
  have hScaleSq : scale ^ 2 = ratio := Real.sq_sqrt (le_of_lt hRatioPos)
  have hScaleLeHalf : scale ≤ (1 : ℝ) / 2 := by
    rw [show scale ≤ (1 : ℝ) / 2 ↔ scale ^ 2 ≤ ((1 : ℝ) / 2) ^ 2 by
      constructor
      · intro h
        nlinarith [sq_nonneg scale]
      · intro h
        nlinarith [le_of_lt hScalePos]]
    rw [hScaleSq]
    dsimp [ratio]
    apply (div_le_iff₀ hOneMinusPos).2
    nlinarith
  have hCostSplit (center : V) :
      single_center_cost 2 X center =
        single_center_cost 2 P center + single_center_cost 2 Q center := by
    simp only [single_center_cost, hPartition, Finset.sum_union hDisjoint]
  have hCostNonneg (S : Finset V) (center : V) :
      0 ≤ single_center_cost 2 S center := by
    exact Finset.sum_nonneg fun point _ => sq_nonneg (dist point center)
  have hPCostLeXCost :
      single_center_cost 2 P centerX ≤ single_center_cost 2 X centerX := by
    rw [hCostSplit centerX]
    exact le_add_of_nonneg_right (hCostNonneg Q centerX)
  have hPointwiseP (point : V) :
      dist centerP centerX ^ 2 ≤
        2 * dist point centerP ^ 2 + 2 * dist point centerX ^ 2 := by
    have hTriangle := dist_triangle centerP point centerX
    rw [dist_comm centerP point] at hTriangle
    have hCenterDistNonneg : 0 ≤ dist centerP centerX := dist_nonneg
    have hPointPNonneg : 0 ≤ dist point centerP := dist_nonneg
    have hPointXNonneg : 0 ≤ dist point centerX := dist_nonneg
    nlinarith [sq_nonneg (dist point centerP - dist point centerX)]
  have hDisplacement :
      (P.card : ℝ) * dist centerP centerX ^ 2 ≤
        4 * single_center_cost 2 X centerX := by
    calc
      (P.card : ℝ) * dist centerP centerX ^ 2 =
          ∑ point ∈ P, dist centerP centerX ^ 2 := by simp
      _ ≤ ∑ point ∈ P,
          (2 * dist point centerP ^ 2 + 2 * dist point centerX ^ 2) := by
            exact Finset.sum_le_sum fun point _ => hPointwiseP point
      _ = 2 * single_center_cost 2 P centerP +
          2 * single_center_cost 2 P centerX := by
            simp only [single_center_cost, Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ 4 * single_center_cost 2 P centerX := by
            nlinarith [hCenterP centerX]
      _ ≤ 4 * single_center_cost 2 X centerX := by
            nlinarith [hPCostLeXCost]
  have hCardRatio : (Q.card : ℝ) ≤ ratio * (P.card : ℝ) := by
    dsimp [ratio]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hOneMinusPos).2
    have hAlphaP := mul_le_mul_of_nonneg_left hP hAlphaNonneg
    have hOneMinusQ := mul_le_mul_of_nonneg_left hQ (le_of_lt hOneMinusPos)
    nlinarith
  have hQDisplacement :
      (Q.card : ℝ) * dist centerP centerX ^ 2 ≤
        4 * scale ^ 2 * single_center_cost 2 X centerX := by
    have hDistSqNonneg : 0 ≤ dist centerP centerX ^ 2 := sq_nonneg _
    have hCardScaled := mul_le_mul_of_nonneg_right hCardRatio hDistSqNonneg
    have hRatioNonneg : 0 ≤ ratio := le_of_lt hRatioPos
    have hDispScaled := mul_le_mul_of_nonneg_left hDisplacement hRatioNonneg
    rw [hScaleSq]
    nlinarith
  have hPointwiseQ (point : V) :
      2 * scale * dist point centerP ^ 2 ≤
        2 * scale * (1 + 2 * scale) * dist point centerX ^ 2 +
          (2 * scale + 1) * dist centerP centerX ^ 2 := by
    have hTriangle := dist_triangle point centerX centerP
    have hLeftNonneg : 0 ≤ dist point centerP := dist_nonneg
    have hPointXNonneg : 0 ≤ dist point centerX := dist_nonneg
    have hCenterDistNonneg : 0 ≤ dist centerX centerP := dist_nonneg
    rw [dist_comm centerX centerP] at hTriangle
    have hSquareTriangle :
        dist point centerP ^ 2 ≤
          (dist point centerX + dist centerP centerX) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hTriangle)
        (add_nonneg (add_nonneg hPointXNonneg hCenterDistNonneg) hLeftNonneg)]
    nlinarith [sq_nonneg (2 * scale * dist point centerX - dist centerP centerX)]
  have hQCost :
      2 * scale * single_center_cost 2 Q centerP ≤
        2 * scale * (1 + 2 * scale) * single_center_cost 2 Q centerX +
          (2 * scale + 1) * ((Q.card : ℝ) * dist centerP centerX ^ 2) := by
    calc
      2 * scale * single_center_cost 2 Q centerP =
          ∑ point ∈ Q, 2 * scale * dist point centerP ^ 2 := by
            simp only [single_center_cost, Finset.mul_sum]
      _ ≤ ∑ point ∈ Q,
          (2 * scale * (1 + 2 * scale) * dist point centerX ^ 2 +
            (2 * scale + 1) * dist centerP centerX ^ 2) := by
              exact Finset.sum_le_sum fun point _ => hPointwiseQ point
      _ = 2 * scale * (1 + 2 * scale) * single_center_cost 2 Q centerX +
          (2 * scale + 1) * ((Q.card : ℝ) * dist centerP centerX ^ 2) := by
            simp only [single_center_cost, Finset.sum_add_distrib, Finset.mul_sum,
              Finset.sum_const, nsmul_eq_mul]
            ring
  have hXCostNonneg : 0 ≤ single_center_cost 2 X centerX := hCostNonneg X centerX
  have hQXCostNonneg : 0 ≤ single_center_cost 2 Q centerX := hCostNonneg Q centerX
  have hQCostLeXCost :
      single_center_cost 2 Q centerX ≤ single_center_cost 2 X centerX := by
    rw [hCostSplit centerX]
    exact le_add_of_nonneg_left (hCostNonneg P centerX)
  have hScaledQDisplacement :=
    mul_le_mul_of_nonneg_left hQDisplacement (by positivity : 0 ≤ 2 * scale + 1)
  rw [hCostSplit centerX] at hScaledQDisplacement hXCostNonneg hQCostLeXCost
  rw [hCostSplit centerP, hCostSplit centerX]
  change single_center_cost 2 P centerP + single_center_cost 2 Q centerP ≤
    (1 + 6 * scale) *
      (single_center_cost 2 P centerX + single_center_cost 2 Q centerX)
  have hCenterPMin := hCenterP centerX
  have hScaledCenterPMin :=
    mul_le_mul_of_nonneg_left hCenterPMin (le_of_lt hScalePos)
  have hQCostCombined :
      2 * scale * single_center_cost 2 Q centerP ≤
        2 * scale * (1 + 2 * scale) * single_center_cost 2 Q centerX +
          (2 * scale + 1) *
            (4 * scale ^ 2 *
              (single_center_cost 2 P centerX + single_center_cost 2 Q centerX)) := by
    nlinarith [hQCost, hScaledQDisplacement]
  have hTwiceScaleLeOne : 2 * scale ≤ 1 := by nlinarith
  apply (mul_le_mul_iff_of_pos_left hScalePos).mp
  nlinarith [sq_nonneg scale,
    mul_nonneg (sub_nonneg.mpr hQCostLeXCost) (sq_nonneg scale),
    mul_nonneg (sub_nonneg.mpr hTwiceScaleLeOne)
      (mul_nonneg (sq_nonneg scale) hXCostNonneg)]

@[blueprint "lem:list-foldl-minimum"
  (statement := /-- Let $s:A\to\mathbb R$, let $a_0\in A$, and let $L$ be a finite list in $A$.  Starting from $a_0$, replace the current element by the next element of $L$ exactly when the latter has strictly smaller $s$-value.  If the final element is $a$, then $s(a)\leq s(a_0)$ and $s(a)\leq s(x)$ for every $x\in L$. -/)
  (proof := /-- Induct on $L$.  At each step, the new incumbent has score no larger than both the preceding incumbent and the element just inspected.  The induction hypothesis for the remaining list therefore gives both assertions. -/)
  (title := /-- Correctness of a strict argmin fold -/)
  (latexEnv := "lemma")]
lemma list_foldl_minimum {A : Type*} (score : A → ℝ) (items : List A)
    (initial selected : A)
    (hSelected :
      items.foldl (fun current candidate =>
        if score candidate < score current then candidate else current) initial = selected) :
    score selected ≤ score initial ∧
      ∀ candidate ∈ items, score selected ≤ score candidate := by
  induction items generalizing initial selected with
  | nil =>
      simp at hSelected
      subst selected
      simp
  | cons candidate rest inductionHypothesis =>
      simp only [List.foldl_cons] at hSelected
      by_cases hBetter : score candidate < score initial
      · rw [if_pos hBetter] at hSelected
        obtain ⟨hCandidate, hRest⟩ :=
          inductionHypothesis candidate selected hSelected
        constructor
        · exact hCandidate.trans hBetter.le
        · intro point hPoint
          rw [List.mem_cons] at hPoint
          rcases hPoint with rfl | hPoint
          · exact hCandidate
          · exact hRest point hPoint
      · rw [if_neg hBetter] at hSelected
        obtain ⟨hInitial, hRest⟩ :=
          inductionHypothesis initial selected hSelected
        constructor
        · exact hInitial
        · intro point hPoint
          rw [List.mem_cons] at hPoint
          rcases hPoint with rfl | hPoint
          · exact hInitial.trans (le_of_not_gt hBetter)
          · exact hRest point hPoint

@[blueprint "lem:get-center-output-minimum"
  (statement := /-- Let $V$ be a finite metric space.  If \cref{def:get-center} returns $a$ on input $(X,q,\alpha)$, then the score used by that invocation at $a$ is no larger than its value at any $c\in V$.  Thus the score is the trimmed cost when $q=2$ and the full cost otherwise. -/)
  (proof := /-- Unfold \cref{def:get-center} and its costed list fold.  The ambient enumeration cannot be empty because the output is present.  Its first element initializes the scan, after which \cref{lem:list-foldl-minimum} proves that the returned element minimizes the score over every element of the enumeration, hence over $V$. -/)
  (title := /-- The GetCenter output minimizes its prescribed score -/)
  (latexEnv := "lemma")]
lemma get_center_output_minimum {V : Type*} [MetricSpace V] [Fintype V]
    [DecidableEq V] (points : Finset V) (q : ℕ) (alpha : ℝ) (selected : V)
    (hOutput : (get_center points q alpha).output = some selected) :
    ∀ center : V,
      (if q = 2 then trimmed_single_center_cost q alpha points selected
        else single_center_cost q points selected) ≤
      (if q = 2 then trimmed_single_center_cost q alpha points center
        else single_center_cost q points center) := by
  classical
  let score := fun center : V =>
    if q = 2 then trimmed_single_center_cost q alpha points center
    else single_center_cost q points center
  let choose := fun current candidate : V =>
    if score candidate < score current then candidate else current
  let chooseOption := fun current : Option V => fun candidate : V =>
    match current with
    | none => some candidate
    | some incumbent => some (choose incumbent candidate)
  let costedStep := fun current : Option V => fun candidate : V =>
    (⟨chooseOption current candidate,
      2 * points.card ^ 2 + 2 * points.card + 1⟩ : costed_computation (Option V))
  have hFoldOutput (items : List V)
      (computation : costed_computation (Option V)) :
      (items.foldl (fun current item =>
        let successor := costedStep current.output item
        (⟨successor.output, current.steps + successor.steps + 1⟩ :
          costed_computation (Option V))) computation).output =
        items.foldl chooseOption computation.output := by
    induction items generalizing computation with
    | nil => rfl
    | cons candidate rest inductionHypothesis =>
        simp only [List.foldl_cons]
        exact inductionHypothesis _
  have hOutput' :
      (Finset.univ.toList.foldl chooseOption none : Option V) = some selected := by
    have hOutput'' :
      (Finset.univ.toList.foldl (fun current item =>
        let successor := costedStep current.output item
        (⟨successor.output, current.steps + successor.steps + 1⟩ :
          costed_computation (Option V))) ⟨none, 0⟩).output = some selected := by
      simpa only [get_center, costed_list_fold, costedStep, chooseOption,
        choose, score, apply_ite] using hOutput
    rw [hFoldOutput] at hOutput''
    exact hOutput''
  have hCandidates : (Finset.univ.toList : List V) ≠ [] := by
    intro hEmpty
    rw [hEmpty] at hOutput'
    simp at hOutput'
  obtain ⟨first, rest, hCandidatesEq⟩ := List.exists_cons_of_ne_nil hCandidates
  rw [hCandidatesEq] at hOutput'
  simp only [List.foldl_cons, chooseOption] at hOutput'
  have hOptionFold (items : List V) (initial : V) :
      items.foldl chooseOption (some initial) =
        some (items.foldl choose initial) := by
    induction items generalizing initial with
    | nil => rfl
    | cons candidate tail inductionHypothesis =>
        simp only [List.foldl_cons, chooseOption]
        exact inductionHypothesis (choose initial candidate)
  rw [hOptionFold] at hOutput'
  injection hOutput' with hSelected
  obtain ⟨hFirst, hRest⟩ :=
    list_foldl_minimum score rest first selected hSelected
  intro center
  have hCenter : center ∈ (Finset.univ.toList : List V) := by simp
  rw [hCandidatesEq, List.mem_cons] at hCenter
  change score selected ≤ score center
  rcases hCenter with rfl | hCenter
  · exact hFirst
  · exact hRest center hCenter

@[blueprint "lem:trimmed-single-center-cost-specification"
  (statement := /-- Let $X$ be finite and let $\alpha\geq0$.  For every center $c$, the value $\operatorname{tcost}_{q,\alpha}(X,c)$ is attained by a core $S\subseteq X$ with $|S|\geq(1-\alpha)|X|$.  Moreover, it is no larger than the full cost of any core satisfying these two conditions. -/)
  (proof := /-- By \cref{def:trimmed-single-center-cost}, the trimmed cost is the infimum of the costs of feasible cores.  This set of values is finite because every core belongs to the powerset of $X$, and it is nonempty because $X$ itself is feasible when $\alpha\geq0$.  The infimum of a nonempty finite set is a member of the set and is bounded above by each member. -/)
  (title := /-- Attainment and comparison for the trimmed cost -/)
  (latexEnv := "lemma")]
lemma trimmed_single_center_cost_specification {V : Type*} [MetricSpace V]
    [DecidableEq V] (q : ℕ) (alpha : ℝ) (points : Finset V) (center : V)
    (hAlphaNonneg : 0 ≤ alpha) :
    (∃ core : Finset V,
      core ⊆ points ∧
      (1 - alpha) * (points.card : ℝ) ≤ (core.card : ℝ) ∧
      trimmed_single_center_cost q alpha points center =
        single_center_cost q core center) ∧
    ∀ core : Finset V,
      core ⊆ points →
      (1 - alpha) * (points.card : ℝ) ≤ (core.card : ℝ) →
      trimmed_single_center_cost q alpha points center ≤
        single_center_cost q core center := by
  let values : Set ℝ := {value : ℝ | ∃ core : Finset V,
    core ⊆ points ∧
      (1 - alpha) * (points.card : ℝ) ≤ (core.card : ℝ) ∧
      value = single_center_cost q core center}
  have hValuesFinite : values.Finite := by
    apply (Finset.finite_toSet points.powerset).image
      (fun core : Finset V => single_center_cost q core center) |>.subset
    intro value hValue
    rcases hValue with ⟨core, hCore, _, rfl⟩
    exact ⟨core, by simpa using hCore, rfl⟩
  have hPointsFeasible :
      (1 - alpha) * (points.card : ℝ) ≤ (points.card : ℝ) := by
    have hCardNonneg : 0 ≤ (points.card : ℝ) := by positivity
    nlinarith
  have hValuesNonempty : values.Nonempty := by
    exact ⟨single_center_cost q points center, points, Finset.Subset.rfl,
      hPointsFeasible, rfl⟩
  have hDefinition :
      trimmed_single_center_cost q alpha points center = sInf values := rfl
  constructor
  · rw [hDefinition]
    exact hValuesNonempty.csInf_mem hValuesFinite
  · intro core hCore hCard
    rw [hDefinition]
    apply csInf_le hValuesFinite.bddBelow
    exact ⟨core, hCore, hCard, rfl⟩

@[blueprint "lem:get-center-linear-robustness"
  (statement := /-- Let $0<\alpha<1/2$, and let finite sets $T,X$ satisfy $|T\setminus X|\leq\alpha|T|$ and $|X\setminus T|\leq\alpha|X|$.  If \cref{def:get-center} returns $a$ on $(X,1,\alpha)$, then, for every $c$,
  \[
    \operatorname{cost}_1(T,a)
      \leq\left(1+\frac{14\alpha}{1-2\alpha}\right)
        \operatorname{cost}_1(T,c).
  \] -/)
  (proof := /-- Put $P=T\cap X$, $R=T\setminus X$, and $Q=X\setminus T$, and choose centers minimizing the linear costs of $P$ and $T$.  The estimate of \cref{lem:dominant-subset-linear-cost} bounds the $T$-cost of the $P$-center by the reference cost.  By \cref{lem:get-center-output-minimum}, optimality of $a$ on $X=P\sqcup Q$ and the triangle inequality imply
  \[
    (|P|-|Q|)d(a,c_P)\leq2\operatorname{cost}_1(P,c_P)
  \]
  and
  \[
    \operatorname{cost}_1(T,a)
      \leq\operatorname{cost}_1(T,c_P)+(|Q|+|R|)d(a,c_P).
  \]
  The two error hypotheses give
  $|Q|+|R|\leq 2\alpha(|P|-|Q|)/(1-2\alpha)$.
  Substitution and elementary simplification, using $\alpha<1/2$, give the stated constant. -/)
  (title := /-- Linear robustness of GetCenter -/)
  (latexEnv := "lemma")]
lemma get_center_linear_robustness {V : Type*} [MetricSpace V] [Fintype V]
    [DecidableEq V] (referenceClass predictedClass : Finset V) (alpha : ℝ)
    (referenceCenter selectedCenter : V)
    (hAlphaPos : 0 < alpha) (hAlphaLt : alpha < (1 : ℝ) / 2)
    (hFalseNegative : ((referenceClass \ predictedClass).card : ℝ) ≤
      alpha * (referenceClass.card : ℝ))
    (hFalsePositive : ((predictedClass \ referenceClass).card : ℝ) ≤
      alpha * (predictedClass.card : ℝ))
    (hOutput : (get_center predictedClass 1 alpha).output = some selectedCenter) :
    single_center_cost 1 referenceClass selectedCenter ≤
      (1 + 14 * alpha / (1 - 2 * alpha)) *
        single_center_cost 1 referenceClass referenceCenter := by
  classical
  by_cases hReferenceEmpty : referenceClass = ∅
  · simp [hReferenceEmpty, single_center_cost]
  let common := referenceClass ∩ predictedClass
  let missed := referenceClass \ predictedClass
  let extra := predictedClass \ referenceClass
  have hReferencePartition : referenceClass = common ∪ missed := by
    ext point
    simp [common, missed]
    tauto
  have hPredictedPartition : predictedClass = common ∪ extra := by
    ext point
    simp [common, extra]
    tauto
  have hReferenceDisjoint : Disjoint common missed := by
    rw [Finset.disjoint_left]
    intro point hCommon hMissed
    simp only [common, missed, Finset.mem_inter, Finset.mem_sdiff] at hCommon hMissed
    exact hMissed.2 hCommon.2
  have hPredictedDisjoint : Disjoint common extra := by
    rw [Finset.disjoint_left]
    intro point hCommon hExtra
    simp only [common, extra, Finset.mem_inter, Finset.mem_sdiff] at hCommon hExtra
    exact hExtra.2 hCommon.1
  have hReferenceCard : (referenceClass.card : ℝ) =
      (common.card : ℝ) + (missed.card : ℝ) := by
    rw [hReferencePartition, Finset.card_union_of_disjoint hReferenceDisjoint]
    push_cast
    rfl
  have hPredictedCard : (predictedClass.card : ℝ) =
      (common.card : ℝ) + (extra.card : ℝ) := by
    rw [hPredictedPartition, Finset.card_union_of_disjoint hPredictedDisjoint]
    push_cast
    rfl
  have hCommonReference :
      (1 - alpha) * (referenceClass.card : ℝ) ≤ (common.card : ℝ) := by
    change (missed.card : ℝ) ≤ alpha * (referenceClass.card : ℝ) at hFalseNegative
    nlinarith
  have hCommonPredicted :
      (1 - alpha) * (predictedClass.card : ℝ) ≤ (common.card : ℝ) := by
    change (extra.card : ℝ) ≤ alpha * (predictedClass.card : ℝ) at hFalsePositive
    nlinarith
  have hAlphaNonneg : 0 ≤ alpha := hAlphaPos.le
  have hAlphaLtOne : alpha < 1 := by linarith
  have hOneMinusAlpha : 0 < 1 - alpha := sub_pos.mpr hAlphaLtOne
  have hOneMinusTwiceAlpha : 0 < 1 - 2 * alpha := by linarith
  have hUniverseNonempty : (Finset.univ : Finset V).Nonempty :=
    ⟨selectedCenter, Finset.mem_univ selectedCenter⟩
  obtain ⟨commonCenter, _, hCommonCenter⟩ :=
    Finset.exists_min_image (Finset.univ : Finset V)
      (fun center => single_center_cost 1 common center) hUniverseNonempty
  obtain ⟨bestReferenceCenter, _, hBestReferenceCenter⟩ :=
    Finset.exists_min_image (Finset.univ : Finset V)
      (fun center => single_center_cost 1 referenceClass center) hUniverseNonempty
  have hCommonCenterMin (center : V) :
      single_center_cost 1 common commonCenter ≤
        single_center_cost 1 common center :=
    hCommonCenter center (Finset.mem_univ center)
  have hBestReferenceCenterMin (center : V) :
      single_center_cost 1 referenceClass bestReferenceCenter ≤
        single_center_cost 1 referenceClass center :=
    hBestReferenceCenter center (Finset.mem_univ center)
  have hDominant :
      single_center_cost 1 referenceClass commonCenter ≤
        (1 + 2 * alpha / (1 - alpha)) *
          single_center_cost 1 referenceClass bestReferenceCenter :=
    dominant_subset_linear_cost referenceClass common missed commonCenter
      bestReferenceCenter alpha hReferencePartition hReferenceDisjoint
      hAlphaNonneg hAlphaLtOne hCommonReference hFalseNegative
      hCommonCenterMin hBestReferenceCenterMin
  have hReferenceCostNonneg (center : V) :
      0 ≤ single_center_cost 1 referenceClass center := by
    unfold single_center_cost
    exact Finset.sum_nonneg fun point hPoint => pow_nonneg dist_nonneg 1
  have hMissedCostNonneg (center : V) :
      0 ≤ single_center_cost 1 missed center := by
    unfold single_center_cost
    exact Finset.sum_nonneg fun point hPoint => pow_nonneg dist_nonneg 1
  have hCostReferenceUnion (center : V) :
      single_center_cost 1 referenceClass center =
        single_center_cost 1 common center + single_center_cost 1 missed center := by
    rw [hReferencePartition]
    simp [single_center_cost, Finset.sum_union hReferenceDisjoint]
  have hCostPredictedUnion (center : V) :
      single_center_cost 1 predictedClass center =
        single_center_cost 1 common center + single_center_cost 1 extra center := by
    rw [hPredictedPartition]
    simp [single_center_cost, Finset.sum_union hPredictedDisjoint]
  have hSelectedMin :
      single_center_cost 1 predictedClass selectedCenter ≤
        single_center_cost 1 predictedClass commonCenter := by
    simpa using
      (get_center_output_minimum predictedClass 1 alpha selectedCenter hOutput
        commonCenter)
  let displacement := dist selectedCenter commonCenter
  have hExtraCost :
      single_center_cost 1 extra commonCenter ≤
        single_center_cost 1 extra selectedCenter +
          (extra.card : ℝ) * displacement := by
    calc
      single_center_cost 1 extra commonCenter =
          ∑ point ∈ extra, dist point commonCenter := by
        simp [single_center_cost]
      _ ≤ ∑ point ∈ extra, (dist point selectedCenter + displacement) := by
        apply Finset.sum_le_sum
        intro point hPoint
        calc
          dist point commonCenter ≤
              dist point selectedCenter + dist selectedCenter commonCenter :=
            dist_triangle point selectedCenter commonCenter
          _ = dist point selectedCenter + displacement := rfl
      _ = single_center_cost 1 extra selectedCenter +
          (extra.card : ℝ) * displacement := by
        simp [single_center_cost, Finset.sum_add_distrib]
  have hCommonSelected :
      single_center_cost 1 common selectedCenter ≤
        single_center_cost 1 common commonCenter +
          (extra.card : ℝ) * displacement := by
    rw [hCostPredictedUnion selectedCenter,
      hCostPredictedUnion commonCenter] at hSelectedMin
    nlinarith
  have hDistanceSum :
      (common.card : ℝ) * displacement ≤
        single_center_cost 1 common selectedCenter +
          single_center_cost 1 common commonCenter := by
    calc
      (common.card : ℝ) * displacement =
          ∑ point ∈ common, displacement := by simp
      _ ≤ ∑ point ∈ common,
          (dist point selectedCenter + dist point commonCenter) := by
        apply Finset.sum_le_sum
        intro point hPoint
        calc
          displacement ≤ dist selectedCenter point + dist point commonCenter :=
            dist_triangle selectedCenter point commonCenter
          _ = dist point selectedCenter + dist point commonCenter := by
            rw [dist_comm selectedCenter point]
      _ = single_center_cost 1 common selectedCenter +
          single_center_cost 1 common commonCenter := by
        simp [single_center_cost, Finset.sum_add_distrib]
  have hDisplacementCost :
      ((common.card : ℝ) - (extra.card : ℝ)) * displacement ≤
        2 * single_center_cost 1 common commonCenter := by
    nlinarith
  have hMissedCost :
      single_center_cost 1 missed selectedCenter ≤
        single_center_cost 1 missed commonCenter +
          (missed.card : ℝ) * displacement := by
    calc
      single_center_cost 1 missed selectedCenter =
          ∑ point ∈ missed, dist point selectedCenter := by
        simp [single_center_cost]
      _ ≤ ∑ point ∈ missed, (dist point commonCenter + displacement) := by
        apply Finset.sum_le_sum
        intro point hPoint
        calc
          dist point selectedCenter ≤
              dist point commonCenter + dist commonCenter selectedCenter :=
            dist_triangle point commonCenter selectedCenter
          _ = dist point commonCenter + displacement := by
            rw [dist_comm commonCenter selectedCenter]
      _ = single_center_cost 1 missed commonCenter +
          (missed.card : ℝ) * displacement := by
        simp [single_center_cost, Finset.sum_add_distrib]
  have hSelectedReference :
      single_center_cost 1 referenceClass selectedCenter ≤
        single_center_cost 1 referenceClass commonCenter +
          ((extra.card : ℝ) + (missed.card : ℝ)) * displacement := by
    rw [hCostReferenceUnion selectedCenter,
      hCostReferenceUnion commonCenter]
    nlinarith
  have hExtraCross :
      (1 - alpha) * (extra.card : ℝ) ≤ alpha * (common.card : ℝ) := by
    nlinarith
  have hMissedCross :
      (1 - alpha) * (missed.card : ℝ) ≤ alpha * (common.card : ℝ) := by
    nlinarith
  have hCommonCardPos : 0 < (common.card : ℝ) := by
    have hReferenceCardPos : 0 < (referenceClass.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hReferenceEmpty)
    nlinarith
  have hCardDifferencePos :
      0 < (common.card : ℝ) - (extra.card : ℝ) := by
    nlinarith
  have hCardRatio :
      (extra.card : ℝ) + (missed.card : ℝ) ≤
        (2 * alpha / (1 - 2 * alpha)) *
          ((common.card : ℝ) - (extra.card : ℝ)) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hOneMinusTwiceAlpha).2
    nlinarith
  have hRatioNonneg : 0 ≤ 2 * alpha / (1 - 2 * alpha) :=
    div_nonneg (mul_nonneg (by norm_num) hAlphaNonneg)
      hOneMinusTwiceAlpha.le
  have hRemainder :
      ((extra.card : ℝ) + (missed.card : ℝ)) * displacement ≤
        (4 * alpha / (1 - 2 * alpha)) *
          single_center_cost 1 referenceClass commonCenter := by
    have hCommonCostLeReference :
        single_center_cost 1 common commonCenter ≤
          single_center_cost 1 referenceClass commonCenter := by
      rw [hCostReferenceUnion commonCenter]
      exact le_add_of_nonneg_right (hMissedCostNonneg commonCenter)
    calc
      ((extra.card : ℝ) + (missed.card : ℝ)) * displacement ≤
          ((2 * alpha / (1 - 2 * alpha)) *
            ((common.card : ℝ) - (extra.card : ℝ))) * displacement :=
        mul_le_mul_of_nonneg_right hCardRatio dist_nonneg
      _ = (2 * alpha / (1 - 2 * alpha)) *
          (((common.card : ℝ) - (extra.card : ℝ)) * displacement) := by ring
      _ ≤ (2 * alpha / (1 - 2 * alpha)) *
          (2 * single_center_cost 1 common commonCenter) :=
        mul_le_mul_of_nonneg_left hDisplacementCost hRatioNonneg
      _ ≤ (2 * alpha / (1 - 2 * alpha)) *
          (2 * single_center_cost 1 referenceClass commonCenter) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hCommonCostLeReference (by norm_num))
          hRatioNonneg
      _ = (4 * alpha / (1 - 2 * alpha)) *
          single_center_cost 1 referenceClass commonCenter := by ring
  have hSelectedVsCommon :
      single_center_cost 1 referenceClass selectedCenter ≤
        (1 + 4 * alpha / (1 - 2 * alpha)) *
          single_center_cost 1 referenceClass commonCenter := by
    nlinarith
  have hDominantReference :
      single_center_cost 1 referenceClass commonCenter ≤
        (1 + 2 * alpha / (1 - alpha)) *
          single_center_cost 1 referenceClass referenceCenter := by
    calc
      single_center_cost 1 referenceClass commonCenter ≤
          (1 + 2 * alpha / (1 - alpha)) *
            single_center_cost 1 referenceClass bestReferenceCenter := hDominant
      _ ≤ (1 + 2 * alpha / (1 - alpha)) *
          single_center_cost 1 referenceClass referenceCenter := by
        apply mul_le_mul_of_nonneg_left (hBestReferenceCenterMin referenceCenter)
        positivity
  have hFirstFactorNonneg : 0 ≤ 1 + 4 * alpha / (1 - 2 * alpha) := by
    positivity
  have hCombined :
      single_center_cost 1 referenceClass selectedCenter ≤
        ((1 + 4 * alpha / (1 - 2 * alpha)) *
          (1 + 2 * alpha / (1 - alpha))) *
            single_center_cost 1 referenceClass referenceCenter :=
    hSelectedVsCommon.trans (by
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left hDominantReference hFirstFactorNonneg))
  have hCoefficient :
      (1 + 4 * alpha / (1 - 2 * alpha)) *
          (1 + 2 * alpha / (1 - alpha)) ≤
        1 + 14 * alpha / (1 - 2 * alpha) := by
    have hSmallRatio : alpha / (1 - alpha) ≤ alpha / (1 - 2 * alpha) := by
      exact div_le_div_of_nonneg_left hAlphaNonneg hOneMinusTwiceAlpha
        (by linarith)
    have hRatioLeOne : alpha / (1 - alpha) ≤ 1 := by
      apply (div_le_iff₀ hOneMinusAlpha).2
      linarith
    have hLargeRatioNonneg : 0 ≤ alpha / (1 - 2 * alpha) := by positivity
    have hProductRatio :
        (alpha / (1 - 2 * alpha)) * (alpha / (1 - alpha)) ≤
          alpha / (1 - 2 * alpha) := by
      simpa using mul_le_mul_of_nonneg_left hRatioLeOne hLargeRatioNonneg
    ring_nf at hSmallRatio hRatioLeOne hLargeRatioNonneg hProductRatio ⊢
    nlinarith
  exact hCombined.trans (mul_le_mul_of_nonneg_right hCoefficient
    (hReferenceCostNonneg referenceCenter))

@[blueprint "lem:weighted-square-triangle"
  (statement := /-- If $s,x,y,z\geq0$ and $z\leq x+y$, then
  \[
    2sz^2\leq2s(1+2s)x^2+(2s+1)y^2.
  \] -/)
  (proof := /-- Square $z\leq x+y$ and use the nonnegativity of $(2sx-y)^2$.  Expanding and collecting terms gives the displayed inequality. -/)
  (title := /-- A weighted squared triangle inequality -/)
  (latexEnv := "lemma")]
lemma weighted_square_triangle (scale x y z : ℝ)
    (hScale : 0 ≤ scale) (hX : 0 ≤ x) (hY : 0 ≤ y) (hZ : 0 ≤ z)
    (hTriangle : z ≤ x + y) :
    2 * scale * z ^ 2 ≤
      2 * scale * (1 + 2 * scale) * x ^ 2 + (2 * scale + 1) * y ^ 2 := by
  have hSquare : z ^ 2 ≤ (x + y) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hTriangle)
      (add_nonneg (add_nonneg hX hY) hZ)]
  nlinarith [sq_nonneg (2 * scale * x - y)]

@[blueprint "lem:contaminated-trimmed-core-cardinality"
  (statement := /-- Let $0<\alpha<1/2$.  Suppose finite sets $T,X,S$ satisfy $S\subseteq X$,
  \[
    |T\setminus X|\leq\alpha|T|,
    \quad |X\setminus T|\leq\alpha|X|,
    \quad |S|\geq(1-\alpha)|X|.
  \]
  Then, with $U=T\cap S$,
  \[
    |T\setminus S|+|S\setminus T|
      \leq\frac{3\alpha}{(1-\alpha)(1-2\alpha)}|U|.
  \] -/)
  (proof := /-- Put $P=T\cap X$.  The two contamination bounds give $|P|\geq(1-\alpha)|T|$ and $|P|\geq(1-\alpha)|X|$.  At most $\alpha|X|$ points of $X$ lie outside $S$, so $|T\cap S|\geq(1-2\alpha)|X|$.  Moreover, $T\setminus S$ is the disjoint union of $T\setminus X$ and $(T\cap X)\setminus S$, while $S\setminus T\subseteq X\setminus T$.  Hence the total exceptional cardinality is at most $3\alpha|X|/(1-\alpha)$.  Combining the last two estimates proves the claim. -/)
  (title := /-- Exceptional mass of a contaminated trimmed core -/)
  (latexEnv := "lemma")]
lemma contaminated_trimmed_core_cardinality {V : Type*} [DecidableEq V]
    (referenceClass predictedClass core : Finset V) (alpha : ℝ)
    (hAlphaPos : 0 < alpha) (hAlphaLt : alpha < (1 : ℝ) / 2)
    (hFalseNegative : ((referenceClass \ predictedClass).card : ℝ) ≤
      alpha * (referenceClass.card : ℝ))
    (hFalsePositive : ((predictedClass \ referenceClass).card : ℝ) ≤
      alpha * (predictedClass.card : ℝ))
    (hCoreSubset : core ⊆ predictedClass)
    (hCoreCard : (1 - alpha) * (predictedClass.card : ℝ) ≤
      (core.card : ℝ)) :
    ((referenceClass \ core).card : ℝ) +
        ((core \ referenceClass).card : ℝ) ≤
      (3 * alpha / ((1 - alpha) * (1 - 2 * alpha))) *
        ((referenceClass ∩ core).card : ℝ) := by
  let originalCommon := referenceClass ∩ predictedClass
  let originallyMissed := referenceClass \ predictedClass
  let originallyExtra := predictedClass \ referenceClass
  let common := referenceClass ∩ core
  let missed := referenceClass \ core
  let extra := core \ referenceClass
  let omitted := predictedClass \ core
  let lostCommon := originalCommon \ core
  have hAlphaNonneg : 0 ≤ alpha := hAlphaPos.le
  have hOneMinusAlpha : 0 < 1 - alpha := by linarith
  have hOneMinusTwiceAlpha : 0 < 1 - 2 * alpha := by linarith
  have hReferenceOriginalPartition :
      referenceClass = originalCommon ∪ originallyMissed := by
    ext point
    simp [originalCommon, originallyMissed]
    tauto
  have hPredictedOriginalPartition :
      predictedClass = originalCommon ∪ originallyExtra := by
    ext point
    simp [originalCommon, originallyExtra]
    tauto
  have hReferenceOriginalDisjoint : Disjoint originalCommon originallyMissed := by
    rw [Finset.disjoint_left]
    intro point hCommon hMissed
    simp only [originalCommon, originallyMissed, Finset.mem_inter,
      Finset.mem_sdiff] at hCommon hMissed
    exact hMissed.2 hCommon.2
  have hPredictedOriginalDisjoint : Disjoint originalCommon originallyExtra := by
    rw [Finset.disjoint_left]
    intro point hCommon hExtra
    simp only [originalCommon, originallyExtra, Finset.mem_inter,
      Finset.mem_sdiff] at hCommon hExtra
    exact hExtra.2 hCommon.1
  have hReferenceOriginalCard : (referenceClass.card : ℝ) =
      (originalCommon.card : ℝ) + (originallyMissed.card : ℝ) := by
    rw [hReferenceOriginalPartition,
      Finset.card_union_of_disjoint hReferenceOriginalDisjoint]
    push_cast
    rfl
  have hPredictedOriginalCard : (predictedClass.card : ℝ) =
      (originalCommon.card : ℝ) + (originallyExtra.card : ℝ) := by
    rw [hPredictedOriginalPartition,
      Finset.card_union_of_disjoint hPredictedOriginalDisjoint]
    push_cast
    rfl
  have hOriginalCommonReference :
      (1 - alpha) * (referenceClass.card : ℝ) ≤
        (originalCommon.card : ℝ) := by
    change (originallyMissed.card : ℝ) ≤
      alpha * (referenceClass.card : ℝ) at hFalseNegative
    nlinarith
  have hOriginalCommonPredicted :
      (1 - alpha) * (predictedClass.card : ℝ) ≤
        (originalCommon.card : ℝ) := by
    change (originallyExtra.card : ℝ) ≤
      alpha * (predictedClass.card : ℝ) at hFalsePositive
    nlinarith
  have hPredictedCorePartition : predictedClass = core ∪ omitted := by
    ext point
    simp only [Finset.mem_union, omitted, Finset.mem_sdiff]
    constructor
    · intro hPoint
      by_cases hPointCore : point ∈ core
      · exact Or.inl hPointCore
      · exact Or.inr ⟨hPoint, hPointCore⟩
    · intro hPoint
      rcases hPoint with hPoint | hPoint
      · exact hCoreSubset hPoint
      · exact hPoint.1
  have hOriginalCommonPartition : originalCommon = common ∪ lostCommon := by
    ext point
    simp only [originalCommon, common, lostCommon, Finset.mem_inter,
      Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨hReference, hPredicted⟩
      by_cases hPointCore : point ∈ core
      · exact Or.inl ⟨hReference, hPointCore⟩
      · exact Or.inr ⟨⟨hReference, hPredicted⟩, hPointCore⟩
    · intro hPoint
      rcases hPoint with hPoint | hPoint
      · exact ⟨hPoint.1, hCoreSubset hPoint.2⟩
      · exact hPoint.1
  have hMissedPartition : missed = originallyMissed ∪ lostCommon := by
    ext point
    simp [missed, originallyMissed, lostCommon, originalCommon]
    tauto
  have hPredictedCoreDisjoint : Disjoint core omitted := by
    rw [Finset.disjoint_left]
    intro point hPointCore hPointOmitted
    simp only [omitted, Finset.mem_sdiff] at hPointOmitted
    exact hPointOmitted.2 hPointCore
  have hOriginalCommonDisjoint : Disjoint common lostCommon := by
    rw [Finset.disjoint_left]
    intro point hPointCommon hPointLost
    simp only [common, lostCommon, Finset.mem_inter,
      Finset.mem_sdiff] at hPointCommon hPointLost
    exact hPointLost.2 hPointCommon.2
  have hMissedDisjoint : Disjoint originallyMissed lostCommon := by
    rw [Finset.disjoint_left]
    intro point hPointMissed hPointLost
    simp only [originallyMissed, lostCommon, originalCommon, Finset.mem_sdiff,
      Finset.mem_inter] at hPointMissed hPointLost
    exact hPointMissed.2 hPointLost.1.2
  have hPredictedCoreCard : (predictedClass.card : ℝ) =
      (core.card : ℝ) + (omitted.card : ℝ) := by
    rw [hPredictedCorePartition,
      Finset.card_union_of_disjoint hPredictedCoreDisjoint]
    push_cast
    rfl
  have hOriginalCommonCard : (originalCommon.card : ℝ) =
      (common.card : ℝ) + (lostCommon.card : ℝ) := by
    rw [hOriginalCommonPartition,
      Finset.card_union_of_disjoint hOriginalCommonDisjoint]
    push_cast
    rfl
  have hMissedCard : (missed.card : ℝ) =
      (originallyMissed.card : ℝ) + (lostCommon.card : ℝ) := by
    rw [hMissedPartition, Finset.card_union_of_disjoint hMissedDisjoint]
    push_cast
    rfl
  have hOmittedBound : (omitted.card : ℝ) ≤
      alpha * (predictedClass.card : ℝ) := by
    nlinarith
  have hLostSubsetOmitted : lostCommon ⊆ omitted := by
    intro point hPoint
    simp only [lostCommon, originalCommon, omitted, Finset.mem_sdiff,
      Finset.mem_inter] at hPoint ⊢
    exact ⟨hPoint.1.2, hPoint.2⟩
  have hLostBound : (lostCommon.card : ℝ) ≤
      alpha * (predictedClass.card : ℝ) := by
    have hCardLe : lostCommon.card ≤ omitted.card :=
      Finset.card_le_card hLostSubsetOmitted
    have hCardLeReal : (lostCommon.card : ℝ) ≤ (omitted.card : ℝ) := by
      exact_mod_cast hCardLe
    exact hCardLeReal.trans hOmittedBound
  have hExtraSubsetOriginalExtra : extra ⊆ originallyExtra := by
    intro point hPoint
    simp only [extra, originallyExtra, Finset.mem_sdiff] at hPoint ⊢
    exact ⟨hCoreSubset hPoint.1, hPoint.2⟩
  have hExtraBound : (extra.card : ℝ) ≤
      alpha * (predictedClass.card : ℝ) := by
    have hCardLe : extra.card ≤ originallyExtra.card :=
      Finset.card_le_card hExtraSubsetOriginalExtra
    have hCardLeReal : (extra.card : ℝ) ≤ (originallyExtra.card : ℝ) := by
      exact_mod_cast hCardLe
    exact hCardLeReal.trans hFalsePositive
  have hReferenceVsPredicted : (referenceClass.card : ℝ) ≤
      (predictedClass.card : ℝ) / (1 - alpha) := by
    apply (le_div_iff₀ hOneMinusAlpha).2
    have hCommonSubset : originalCommon ⊆ predictedClass := by
      intro point hPoint
      have hPoint' : point ∈ referenceClass ∧ point ∈ predictedClass := by
        simpa only [originalCommon, Finset.mem_inter] using hPoint
      exact hPoint'.2
    have hCommonCardLe : originalCommon.card ≤ predictedClass.card :=
      Finset.card_le_card hCommonSubset
    have hCommonCardLeReal :
        (originalCommon.card : ℝ) ≤ (predictedClass.card : ℝ) := by
      exact_mod_cast hCommonCardLe
    simpa only [mul_comm] using
      hOriginalCommonReference.trans hCommonCardLeReal
  have hCommonLower :
      (1 - 2 * alpha) * (predictedClass.card : ℝ) ≤
        (common.card : ℝ) := by
    nlinarith
  have hExceptionalBound :
      (missed.card : ℝ) + (extra.card : ℝ) ≤
        (3 * alpha / (1 - alpha)) * (predictedClass.card : ℝ) := by
    have hScaledReference :=
      mul_le_mul_of_nonneg_left hReferenceVsPredicted hAlphaNonneg
    rw [hMissedCard, div_mul_eq_mul_div]
    apply (le_div_iff₀ hOneMinusAlpha).2
    nlinarith
  have hCoefficientNonneg : 0 ≤ 3 * alpha / (1 - alpha) := by positivity
  have hPredictedVsCommon : (predictedClass.card : ℝ) ≤
      (common.card : ℝ) / (1 - 2 * alpha) := by
    apply (le_div_iff₀ hOneMinusTwiceAlpha).2
    simpa only [mul_comm] using hCommonLower
  change (missed.card : ℝ) + (extra.card : ℝ) ≤
    (3 * alpha / ((1 - alpha) * (1 - 2 * alpha))) * (common.card : ℝ)
  calc
    (missed.card : ℝ) + (extra.card : ℝ) ≤
        (3 * alpha / (1 - alpha)) * (predictedClass.card : ℝ) :=
      hExceptionalBound
    _ ≤ (3 * alpha / (1 - alpha)) *
        ((common.card : ℝ) / (1 - 2 * alpha)) :=
      mul_le_mul_of_nonneg_left hPredictedVsCommon hCoefficientNonneg
    _ = (3 * alpha / ((1 - alpha) * (1 - 2 * alpha))) *
        (common.card : ℝ) := by
      field_simp

@[blueprint "lem:squared-core-transfer"
  (statement := /-- Let $T,S$ be finite subsets of a metric space, let $c,a$ be centers, and let $\rho>0$.  Suppose
  \[
    |T\setminus S|+|S\setminus T|\leq\rho|T\cap S|,
  \]
  $\operatorname{cost}_2(S,a)\leq\operatorname{cost}_2(S,c)$, and
  $\operatorname{cost}_2(S,a)\leq\operatorname{cost}_2(T,c)$.  Then
  \[
    \operatorname{cost}_2(T,a)
      \leq(1+6\sqrt\rho+4\rho)\operatorname{cost}_2(T,c).
  \] -/)
  (proof := /-- Put $U=T\cap S$, $E=T\setminus S$, $A=S\setminus T$, and $D=d(a,c)$.  The squared triangle inequality on $U$ and the two cost hypotheses give $|U|D^2\leq4\operatorname{cost}_2(T,c)$.  Hence the cardinality hypothesis gives $(|E|+|A|)D^2\leq4\rho\operatorname{cost}_2(T,c)$.  Apply \cref{lem:weighted-square-triangle} on $E$ in the direction from $c$ to $a$ and on $A$ in the reverse direction, with weight $\sqrt\rho$.  The hypothesis comparing the two costs on $S$ cancels the common part, and collecting the two exceptional estimates yields the coefficient $1+6\sqrt\rho+4\rho$. -/)
  (title := /-- Transfer from a robust core to a reference set -/)
  (latexEnv := "lemma")]
lemma squared_core_transfer {V : Type*} [MetricSpace V] [DecidableEq V]
    (referenceClass core : Finset V) (referenceCenter selectedCenter : V)
    (ratio : ℝ) (hRatioPos : 0 < ratio)
    (hExceptionalCard :
      ((referenceClass \ core).card : ℝ) +
          ((core \ referenceClass).card : ℝ) ≤
        ratio * ((referenceClass ∩ core).card : ℝ))
    (hCoreComparison : single_center_cost 2 core selectedCenter ≤
      single_center_cost 2 core referenceCenter)
    (hCoreCostLeReference : single_center_cost 2 core selectedCenter ≤
      single_center_cost 2 referenceClass referenceCenter) :
    single_center_cost 2 referenceClass selectedCenter ≤
      (1 + 6 * Real.sqrt ratio + 4 * ratio) *
        single_center_cost 2 referenceClass referenceCenter := by
  let common := referenceClass ∩ core
  let missed := referenceClass \ core
  let extra := core \ referenceClass
  have hReferencePartition : referenceClass = common ∪ missed := by
    ext point
    simp [common, missed]
    tauto
  have hCorePartition : core = common ∪ extra := by
    ext point
    simp [common, extra]
    tauto
  have hReferenceDisjoint : Disjoint common missed := by
    rw [Finset.disjoint_left]
    intro point hCommon hMissed
    simp only [common, missed, Finset.mem_inter, Finset.mem_sdiff] at hCommon hMissed
    exact hMissed.2 hCommon.2
  have hCoreDisjoint : Disjoint common extra := by
    rw [Finset.disjoint_left]
    intro point hCommon hExtra
    simp only [common, extra, Finset.mem_inter, Finset.mem_sdiff] at hCommon hExtra
    exact hExtra.2 hCommon.1
  have hCostReferenceUnion (center : V) :
      single_center_cost 2 referenceClass center =
        single_center_cost 2 common center + single_center_cost 2 missed center := by
    rw [hReferencePartition]
    simp [single_center_cost, Finset.sum_union hReferenceDisjoint]
  have hCostCoreUnion (center : V) :
      single_center_cost 2 core center =
        single_center_cost 2 common center + single_center_cost 2 extra center := by
    rw [hCorePartition]
    simp [single_center_cost, Finset.sum_union hCoreDisjoint]
  have hCostNonneg (points : Finset V) (center : V) :
      0 ≤ single_center_cost 2 points center := by
    unfold single_center_cost
    exact Finset.sum_nonneg fun point hPoint => pow_nonneg dist_nonneg 2
  have hCommonReferenceCostLe :
      single_center_cost 2 common referenceCenter ≤
        single_center_cost 2 referenceClass referenceCenter := by
    rw [hCostReferenceUnion referenceCenter]
    exact le_add_of_nonneg_right (hCostNonneg missed referenceCenter)
  have hCommonSelectedCostLe :
      single_center_cost 2 common selectedCenter ≤
        single_center_cost 2 referenceClass referenceCenter := by
    rw [hCostCoreUnion selectedCenter] at hCoreCostLeReference
    exact (le_add_of_nonneg_right (hCostNonneg extra selectedCenter)).trans
      hCoreCostLeReference
  let scale := Real.sqrt ratio
  have hScalePos : 0 < scale := Real.sqrt_pos.2 hRatioPos
  have hScaleSq : scale ^ 2 = ratio := Real.sq_sqrt hRatioPos.le
  let displacement := dist selectedCenter referenceCenter
  have hPointwiseCommon (point : V) :
      displacement ^ 2 ≤
        2 * dist point selectedCenter ^ 2 +
          2 * dist point referenceCenter ^ 2 := by
    change dist selectedCenter referenceCenter ^ 2 ≤
      2 * dist point selectedCenter ^ 2 + 2 * dist point referenceCenter ^ 2
    have hTriangle := dist_triangle selectedCenter point referenceCenter
    rw [dist_comm selectedCenter point] at hTriangle
    have hSelectedNonneg : 0 ≤ dist point selectedCenter := dist_nonneg
    have hReferenceNonneg : 0 ≤ dist point referenceCenter := dist_nonneg
    have hCenterNonneg : 0 ≤ dist selectedCenter referenceCenter := dist_nonneg
    nlinarith [sq_nonneg
      (dist point selectedCenter - dist point referenceCenter)]
  have hDisplacement :
      (common.card : ℝ) * displacement ^ 2 ≤
        4 * single_center_cost 2 referenceClass referenceCenter := by
    calc
      (common.card : ℝ) * displacement ^ 2 =
          ∑ point ∈ common, displacement ^ 2 := by simp
      _ ≤ ∑ point ∈ common,
          (2 * dist point selectedCenter ^ 2 +
            2 * dist point referenceCenter ^ 2) := by
        exact Finset.sum_le_sum fun point _ => hPointwiseCommon point
      _ = 2 * single_center_cost 2 common selectedCenter +
          2 * single_center_cost 2 common referenceCenter := by
        simp only [single_center_cost, Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ 4 * single_center_cost 2 referenceClass referenceCenter := by
        nlinarith
  have hExceptionalCard' :
      (missed.card : ℝ) + (extra.card : ℝ) ≤
        ratio * (common.card : ℝ) := by
    simpa only [common, missed, extra] using hExceptionalCard
  have hExceptionalDisplacement :
      ((missed.card : ℝ) + (extra.card : ℝ)) * displacement ^ 2 ≤
        4 * scale ^ 2 *
          single_center_cost 2 referenceClass referenceCenter := by
    have hScaledCard :=
      mul_le_mul_of_nonneg_right hExceptionalCard' (sq_nonneg displacement)
    have hScaledDistance :=
      mul_le_mul_of_nonneg_left hDisplacement hRatioPos.le
    rw [hScaleSq]
    nlinarith
  have hPointwiseForward (point : V) :
      2 * scale * dist point selectedCenter ^ 2 ≤
        2 * scale * (1 + 2 * scale) * dist point referenceCenter ^ 2 +
          (2 * scale + 1) * displacement ^ 2 := by
    apply weighted_square_triangle scale (dist point referenceCenter)
      displacement (dist point selectedCenter) hScalePos.le dist_nonneg
      dist_nonneg dist_nonneg
    simpa only [displacement, dist_comm referenceCenter selectedCenter] using
      (dist_triangle point referenceCenter selectedCenter)
  have hPointwiseBackward (point : V) :
      2 * scale * dist point referenceCenter ^ 2 ≤
        2 * scale * (1 + 2 * scale) * dist point selectedCenter ^ 2 +
          (2 * scale + 1) * displacement ^ 2 := by
    apply weighted_square_triangle scale (dist point selectedCenter)
      displacement (dist point referenceCenter) hScalePos.le dist_nonneg
      dist_nonneg dist_nonneg
    simpa only [displacement] using
      (dist_triangle point selectedCenter referenceCenter)
  have hMissedDifference :
      2 * scale * single_center_cost 2 missed selectedCenter ≤
        2 * scale * (1 + 2 * scale) *
          single_center_cost 2 missed referenceCenter +
        (2 * scale + 1) * ((missed.card : ℝ) * displacement ^ 2) := by
    calc
      2 * scale * single_center_cost 2 missed selectedCenter =
          ∑ point ∈ missed, 2 * scale * dist point selectedCenter ^ 2 := by
        simp only [single_center_cost, Finset.mul_sum]
      _ ≤ ∑ point ∈ missed,
          (2 * scale * (1 + 2 * scale) * dist point referenceCenter ^ 2 +
            (2 * scale + 1) * displacement ^ 2) := by
        exact Finset.sum_le_sum fun point _ => hPointwiseForward point
      _ = 2 * scale * (1 + 2 * scale) *
          single_center_cost 2 missed referenceCenter +
        (2 * scale + 1) * ((missed.card : ℝ) * displacement ^ 2) := by
        simp only [single_center_cost, Finset.sum_add_distrib, Finset.mul_sum,
          Finset.sum_const, nsmul_eq_mul]
        ring
  have hExtraDifference :
      2 * scale * single_center_cost 2 extra referenceCenter ≤
        2 * scale * (1 + 2 * scale) *
          single_center_cost 2 extra selectedCenter +
        (2 * scale + 1) * ((extra.card : ℝ) * displacement ^ 2) := by
    calc
      2 * scale * single_center_cost 2 extra referenceCenter =
          ∑ point ∈ extra, 2 * scale * dist point referenceCenter ^ 2 := by
        simp only [single_center_cost, Finset.mul_sum]
      _ ≤ ∑ point ∈ extra,
          (2 * scale * (1 + 2 * scale) * dist point selectedCenter ^ 2 +
            (2 * scale + 1) * displacement ^ 2) := by
        exact Finset.sum_le_sum fun point _ => hPointwiseBackward point
      _ = 2 * scale * (1 + 2 * scale) *
          single_center_cost 2 extra selectedCenter +
        (2 * scale + 1) * ((extra.card : ℝ) * displacement ^ 2) := by
        simp only [single_center_cost, Finset.sum_add_distrib, Finset.mul_sum,
          Finset.sum_const, nsmul_eq_mul]
        ring
  rw [hCostCoreUnion selectedCenter,
    hCostCoreUnion referenceCenter] at hCoreComparison
  have hMissedReferenceLe :
      single_center_cost 2 missed referenceCenter ≤
        single_center_cost 2 referenceClass referenceCenter := by
    rw [hCostReferenceUnion referenceCenter]
    exact le_add_of_nonneg_left (hCostNonneg common referenceCenter)
  have hExtraSelectedLe :
      single_center_cost 2 extra selectedCenter ≤
        single_center_cost 2 referenceClass referenceCenter := by
    have hExtraLeCore : single_center_cost 2 extra selectedCenter ≤
        single_center_cost 2 core selectedCenter := by
      rw [hCostCoreUnion selectedCenter]
      exact le_add_of_nonneg_left (hCostNonneg common selectedCenter)
    exact hExtraLeCore.trans hCoreCostLeReference
  have hExceptionalCosts :
      single_center_cost 2 missed referenceCenter +
          single_center_cost 2 extra selectedCenter ≤
        2 * single_center_cost 2 referenceClass referenceCenter := by
    nlinarith
  have hFourScaleSqNonneg : 0 ≤ 4 * scale ^ 2 := by positivity
  have hScaledCostBound := mul_le_mul_of_nonneg_left hExceptionalCosts
    hFourScaleSqNonneg
  have hScaledDisplacementBound :=
    mul_le_mul_of_nonneg_left hExceptionalDisplacement (by positivity : 0 ≤ 2 * scale + 1)
  have hScaledDifference :
      2 * scale *
        ((single_center_cost 2 common selectedCenter +
            single_center_cost 2 missed selectedCenter) -
          (single_center_cost 2 common referenceCenter +
            single_center_cost 2 missed referenceCenter)) ≤
        4 * scale ^ 2 *
          (single_center_cost 2 missed referenceCenter +
            single_center_cost 2 extra selectedCenter) +
        (2 * scale + 1) *
          (((missed.card : ℝ) + (extra.card : ℝ)) * displacement ^ 2) := by
    nlinarith [hMissedDifference, hExtraDifference]
  have hScaledDifferenceBound :
      2 * scale *
        ((single_center_cost 2 common selectedCenter +
            single_center_cost 2 missed selectedCenter) -
          (single_center_cost 2 common referenceCenter +
            single_center_cost 2 missed referenceCenter)) ≤
        (12 * scale ^ 2 + 8 * scale ^ 3) *
          single_center_cost 2 referenceClass referenceCenter := by
    nlinarith [hScaledCostBound, hScaledDisplacementBound]
  rw [hCostReferenceUnion referenceCenter] at hScaledDifferenceBound
  rw [hCostReferenceUnion selectedCenter,
    hCostReferenceUnion referenceCenter]
  change single_center_cost 2 common selectedCenter +
      single_center_cost 2 missed selectedCenter ≤
    (1 + 6 * scale + 4 * ratio) *
      (single_center_cost 2 common referenceCenter +
        single_center_cost 2 missed referenceCenter)
  rw [← hScaleSq]
  nlinarith [hScaledDifferenceBound,
    hCostNonneg referenceClass referenceCenter]

@[blueprint "lem:get-center-squared-direct-robustness"
  (statement := /-- Under the same two-sided contamination hypotheses, put
  \[
    \rho(\alpha)=\frac{3\alpha}{(1-\alpha)(1-2\alpha)}.
  \]
  If \cref{def:get-center} returns $a$ on $(X,2,\alpha)$, then, for every $c$,
  \[
    \operatorname{cost}_2(T,a)
      \leq\bigl(1+6\sqrt{\rho(\alpha)}+4\rho(\alpha)\bigr)
        \operatorname{cost}_2(T,c).
  \] -/)
  (proof := /-- By \cref{lem:trimmed-single-center-cost-specification}, choose a feasible core $S\subseteq X$ attaining the trimmed score at $a$.  The intersection $P=T\cap X$ is also feasible, and \cref{lem:get-center-output-minimum} gives
  $\operatorname{cost}_2(S,a)\leq\operatorname{cost}_2(P,c)$ as well as
  $\operatorname{cost}_2(S,a)\leq\operatorname{cost}_2(S,c)$.
  By \cref{lem:contaminated-trimmed-core-cardinality}, with $U=T\cap S$, $E=T\setminus S$, and $A=S\setminus T$,
  \[
    |E|+|A|\leq\rho(\alpha)|U|.
  \]
  The hypotheses of \cref{lem:squared-core-transfer} are therefore satisfied with $S$ and $\rho(\alpha)$.  That lemma gives an excess of at most
  $(6\sqrt{\rho(\alpha)}+4\rho(\alpha))\operatorname{cost}_2(T,c)$, which is the asserted estimate. -/)
  (title := /-- Direct squared-cost robustness of GetCenter -/)
  (latexEnv := "lemma")]
lemma get_center_squared_direct_robustness {V : Type*} [MetricSpace V] [Fintype V]
    [DecidableEq V] (referenceClass predictedClass : Finset V) (alpha : ℝ)
    (referenceCenter selectedCenter : V)
    (hAlphaPos : 0 < alpha) (hAlphaLt : alpha < (1 : ℝ) / 2)
    (hFalseNegative : ((referenceClass \ predictedClass).card : ℝ) ≤
      alpha * (referenceClass.card : ℝ))
    (hFalsePositive : ((predictedClass \ referenceClass).card : ℝ) ≤
      alpha * (predictedClass.card : ℝ))
    (hOutput : (get_center predictedClass 2 alpha).output = some selectedCenter) :
    single_center_cost 2 referenceClass selectedCenter ≤
      (1 + 6 * Real.sqrt
          (3 * alpha / ((1 - alpha) * (1 - 2 * alpha))) +
        4 * (3 * alpha / ((1 - alpha) * (1 - 2 * alpha)))) *
          single_center_cost 2 referenceClass referenceCenter := by
  classical
  have hAlphaNonneg : 0 ≤ alpha := hAlphaPos.le
  obtain ⟨⟨core, hCoreSubset, hCoreCard, hCoreScore⟩, _⟩ :=
    trimmed_single_center_cost_specification 2 alpha predictedClass
      selectedCenter hAlphaNonneg
  have hSelectedTrimmedMin (center : V) :
      trimmed_single_center_cost 2 alpha predictedClass selectedCenter ≤
        trimmed_single_center_cost 2 alpha predictedClass center := by
    simpa using
      (get_center_output_minimum predictedClass 2 alpha selectedCenter hOutput center)
  have hCoreComparison (center : V) :
      single_center_cost 2 core selectedCenter ≤
        single_center_cost 2 core center := by
    have hCoreUpper :=
      (trimmed_single_center_cost_specification 2 alpha predictedClass center
        hAlphaNonneg).2 core hCoreSubset hCoreCard
    rw [hCoreScore] at hSelectedTrimmedMin
    exact (hSelectedTrimmedMin center).trans hCoreUpper
  let originalCommon := referenceClass ∩ predictedClass
  let originallyExtra := predictedClass \ referenceClass
  have hPredictedPartition :
      predictedClass = originalCommon ∪ originallyExtra := by
    ext point
    simp [originalCommon, originallyExtra]
    tauto
  have hPredictedDisjoint : Disjoint originalCommon originallyExtra := by
    rw [Finset.disjoint_left]
    intro point hCommon hExtra
    simp only [originalCommon, originallyExtra, Finset.mem_inter,
      Finset.mem_sdiff] at hCommon hExtra
    exact hExtra.2 hCommon.1
  have hPredictedCard : (predictedClass.card : ℝ) =
      (originalCommon.card : ℝ) + (originallyExtra.card : ℝ) := by
    rw [hPredictedPartition, Finset.card_union_of_disjoint hPredictedDisjoint]
    push_cast
    rfl
  have hOriginalCommonCard :
      (1 - alpha) * (predictedClass.card : ℝ) ≤
        (originalCommon.card : ℝ) := by
    change (originallyExtra.card : ℝ) ≤
      alpha * (predictedClass.card : ℝ) at hFalsePositive
    nlinarith
  have hOriginalCommonSubsetPredicted : originalCommon ⊆ predictedClass := by
    intro point hPoint
    have hPoint' : point ∈ referenceClass ∧ point ∈ predictedClass := by
      simpa only [originalCommon, Finset.mem_inter] using hPoint
    exact hPoint'.2
  have hOriginalCommonSubsetReference : originalCommon ⊆ referenceClass := by
    intro point hPoint
    have hPoint' : point ∈ referenceClass ∧ point ∈ predictedClass := by
      simpa only [originalCommon, Finset.mem_inter] using hPoint
    exact hPoint'.1
  have hOriginalCommonCostLeReference :
      single_center_cost 2 originalCommon referenceCenter ≤
        single_center_cost 2 referenceClass referenceCenter := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hOriginalCommonSubsetReference
    intro point hPoint hNotMem
    exact pow_nonneg dist_nonneg 2
  have hCoreCostLeReference :
      single_center_cost 2 core selectedCenter ≤
        single_center_cost 2 referenceClass referenceCenter := by
    have hTrimmedReference :=
      (trimmed_single_center_cost_specification 2 alpha predictedClass
        referenceCenter hAlphaNonneg).2 originalCommon
        hOriginalCommonSubsetPredicted hOriginalCommonCard
    calc
      single_center_cost 2 core selectedCenter =
          trimmed_single_center_cost 2 alpha predictedClass selectedCenter :=
        hCoreScore.symm
      _ ≤ trimmed_single_center_cost 2 alpha predictedClass referenceCenter :=
        hSelectedTrimmedMin referenceCenter
      _ ≤ single_center_cost 2 originalCommon referenceCenter := hTrimmedReference
      _ ≤ single_center_cost 2 referenceClass referenceCenter :=
        hOriginalCommonCostLeReference
  let ratio := 3 * alpha / ((1 - alpha) * (1 - 2 * alpha))
  have hRatioPos : 0 < ratio := by
    dsimp [ratio]
    have hOneMinusAlpha : 0 < 1 - alpha := by linarith
    have hOneMinusTwiceAlpha : 0 < 1 - 2 * alpha := by linarith
    positivity
  have hExceptionalCard :
      ((referenceClass \ core).card : ℝ) +
          ((core \ referenceClass).card : ℝ) ≤
        ratio * ((referenceClass ∩ core).card : ℝ) := by
    dsimp [ratio]
    exact contaminated_trimmed_core_cardinality referenceClass predictedClass
      core alpha hAlphaPos hAlphaLt hFalseNegative hFalsePositive
      hCoreSubset hCoreCard
  exact squared_core_transfer referenceClass core referenceCenter selectedCenter
    ratio hRatioPos hExceptionalCard (hCoreComparison referenceCenter)
    hCoreCostLeReference

@[blueprint "lem:get-center-squared-robustness"
  (statement := /-- Under the two-sided contamination hypotheses, put
  \[
    \rho(\alpha)=\frac{3\alpha}{(1-\alpha)(1-2\alpha)}.
  \]
  If \cref{def:get-center} returns $a$ on $(X,2,\alpha)$, then, for every $c$,
  \[
    \operatorname{cost}_2(T,a)
      \leq(1+6\sqrt{\rho(\alpha)}+4\rho(\alpha))
        \left(1+6\sqrt{\frac{\rho(\alpha)}{1-\rho(\alpha)}}\right)
        \operatorname{cost}_2(T,c).
  \] -/)
  (proof := /-- The direct factor is supplied by \cref{lem:get-center-squared-direct-robustness}.  For sufficiently small $\alpha$, choose an attaining core by \cref{lem:trimmed-single-center-cost-specification}.  The exceptional-set estimate \cref{lem:contaminated-trimmed-core-cardinality} shows that $T\cap S$ omits at most a $\rho(\alpha)$ fraction of $T$.  Since then $\rho(\alpha)<1/8$, \cref{lem:dominant-subset-squared-cost} bounds the cost on $T$ of a center minimizing $T\cap S$ by the second displayed factor times the reference cost.  Apply the direct estimate with this common-core center and multiply the two bounds.  Outside that small neighborhood, apply the direct estimate with $c$ itself; the second factor is at least one, so the displayed, deliberately larger bound remains valid. -/)
  (title := /-- Squared-cost robustness of GetCenter -/)
  (latexEnv := "lemma")]
lemma get_center_squared_robustness {V : Type*} [MetricSpace V] [Fintype V]
    [DecidableEq V] (referenceClass predictedClass : Finset V) (alpha : ℝ)
    (referenceCenter selectedCenter : V)
    (hAlphaPos : 0 < alpha) (hAlphaLt : alpha < (1 : ℝ) / 2)
    (hFalseNegative : ((referenceClass \ predictedClass).card : ℝ) ≤
      alpha * (referenceClass.card : ℝ))
    (hFalsePositive : ((predictedClass \ referenceClass).card : ℝ) ≤
      alpha * (predictedClass.card : ℝ))
    (hOutput : (get_center predictedClass 2 alpha).output = some selectedCenter) :
    let ratio := 3 * alpha / ((1 - alpha) * (1 - 2 * alpha))
    single_center_cost 2 referenceClass selectedCenter ≤
      ((1 + 6 * Real.sqrt ratio + 4 * ratio) *
        (1 + 6 * Real.sqrt (ratio / (1 - ratio)))) *
          single_center_cost 2 referenceClass referenceCenter := by
  classical
  dsimp only
  let ratio := 3 * alpha / ((1 - alpha) * (1 - 2 * alpha))
  have hRatioPos : 0 < ratio := by
    dsimp [ratio]
    have hOneMinusAlpha : 0 < 1 - alpha := by linarith
    have hOneMinusTwiceAlpha : 0 < 1 - 2 * alpha := by linarith
    positivity
  have hDirect (center : V) :
      single_center_cost 2 referenceClass selectedCenter ≤
        (1 + 6 * Real.sqrt ratio + 4 * ratio) *
          single_center_cost 2 referenceClass center := by
    dsimp [ratio]
    exact get_center_squared_direct_robustness referenceClass predictedClass
      alpha center selectedCenter hAlphaPos hAlphaLt hFalseNegative
      hFalsePositive hOutput
  have hCostNonneg (center : V) :
      0 ≤ single_center_cost 2 referenceClass center := by
    unfold single_center_cost
    exact Finset.sum_nonneg fun point hPoint => pow_nonneg dist_nonneg 2
  have hDirectFactorNonneg : 0 ≤ 1 + 6 * Real.sqrt ratio + 4 * ratio := by
    positivity
  have hSecondFactorNonneg : 0 ≤ 1 + 6 * Real.sqrt (ratio / (1 - ratio)) := by
    positivity
  have hSecondFactorOne : 1 ≤ 1 + 6 * Real.sqrt (ratio / (1 - ratio)) := by
    nlinarith [Real.sqrt_nonneg (ratio / (1 - ratio))]
  by_cases hAlphaSmall : alpha < (1 : ℝ) / 100
  · have hRatioLt : ratio < (1 : ℝ) / 8 := by
      dsimp [ratio]
      have hDenominatorPos : 0 < (1 - alpha) * (1 - 2 * alpha) := by
        apply mul_pos <;> linarith
      apply (div_lt_iff₀ hDenominatorPos).2
      nlinarith [sq_nonneg alpha]
    have hAlphaNonneg : 0 ≤ alpha := hAlphaPos.le
    obtain ⟨⟨core, hCoreSubset, hCoreCard, _⟩, _⟩ :=
      trimmed_single_center_cost_specification 2 alpha predictedClass
        selectedCenter hAlphaNonneg
    let common := referenceClass ∩ core
    let missed := referenceClass \ core
    have hPartition : referenceClass = common ∪ missed := by
      ext point
      simp [common, missed]
      tauto
    have hDisjoint : Disjoint common missed := by
      rw [Finset.disjoint_left]
      intro point hCommon hMissed
      simp only [common, missed, Finset.mem_inter, Finset.mem_sdiff] at hCommon hMissed
      exact hMissed.2 hCommon.2
    have hCardEq : (referenceClass.card : ℝ) =
        (common.card : ℝ) + (missed.card : ℝ) := by
      rw [hPartition, Finset.card_union_of_disjoint hDisjoint]
      push_cast
      rfl
    have hExceptional := contaminated_trimmed_core_cardinality
      referenceClass predictedClass core alpha hAlphaPos hAlphaLt
      hFalseNegative hFalsePositive hCoreSubset hCoreCard
    have hMissedLeExceptional : (missed.card : ℝ) ≤
        (missed.card : ℝ) + ((core \ referenceClass).card : ℝ) := by
      have hCardNonneg : 0 ≤ ((core \ referenceClass).card : ℝ) := by positivity
      linarith
    have hCommonCardLeReference : (common.card : ℝ) ≤
        (referenceClass.card : ℝ) := by
      have hSubset : common ⊆ referenceClass := by
        intro point hPoint
        have hPoint' : point ∈ referenceClass ∧ point ∈ core := by
          simpa only [common, Finset.mem_inter] using hPoint
        exact hPoint'.1
      exact_mod_cast Finset.card_le_card hSubset
    have hMissedBound : (missed.card : ℝ) ≤
        ratio * (referenceClass.card : ℝ) := by
      change (missed.card : ℝ) ≤ ratio * (referenceClass.card : ℝ)
      have hRatioNonneg : 0 ≤ ratio := hRatioPos.le
      calc
        (missed.card : ℝ) ≤
            (missed.card : ℝ) + ((core \ referenceClass).card : ℝ) :=
          hMissedLeExceptional
        _ ≤ ratio * (common.card : ℝ) := by
          simpa only [ratio, common, missed] using hExceptional
        _ ≤ ratio * (referenceClass.card : ℝ) :=
          mul_le_mul_of_nonneg_left hCommonCardLeReference hRatioNonneg
    have hCommonBound :
        (1 - ratio) * (referenceClass.card : ℝ) ≤ (common.card : ℝ) := by
      nlinarith
    have hUniverseNonempty : (Finset.univ : Finset V).Nonempty :=
      ⟨selectedCenter, Finset.mem_univ selectedCenter⟩
    obtain ⟨commonCenter, _, hCommonCenter⟩ :=
      Finset.exists_min_image (Finset.univ : Finset V)
        (fun center => single_center_cost 2 common center) hUniverseNonempty
    obtain ⟨bestReferenceCenter, _, hBestReferenceCenter⟩ :=
      Finset.exists_min_image (Finset.univ : Finset V)
        (fun center => single_center_cost 2 referenceClass center) hUniverseNonempty
    have hCommonCenterMin (center : V) :
        single_center_cost 2 common commonCenter ≤
          single_center_cost 2 common center :=
      hCommonCenter center (Finset.mem_univ center)
    have hBestReferenceCenterMin (center : V) :
        single_center_cost 2 referenceClass bestReferenceCenter ≤
          single_center_cost 2 referenceClass center :=
      hBestReferenceCenter center (Finset.mem_univ center)
    have hDominant := dominant_subset_squared_cost referenceClass common missed
      commonCenter bestReferenceCenter ratio hPartition hDisjoint hRatioPos.le
      hRatioLt hCommonBound hMissedBound hCommonCenterMin hBestReferenceCenterMin
    have hDominantReference :
        single_center_cost 2 referenceClass commonCenter ≤
          (1 + 6 * Real.sqrt (ratio / (1 - ratio))) *
            single_center_cost 2 referenceClass referenceCenter := by
      exact hDominant.trans (mul_le_mul_of_nonneg_left
        (hBestReferenceCenterMin referenceCenter) hSecondFactorNonneg)
    exact (hDirect commonCenter).trans (by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hDominantReference hDirectFactorNonneg)
  · have hEnlarged :
        single_center_cost 2 referenceClass referenceCenter ≤
          (1 + 6 * Real.sqrt (ratio / (1 - ratio))) *
            single_center_cost 2 referenceClass referenceCenter := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hSecondFactorOne
        (hCostNonneg referenceCenter)
    exact (hDirect referenceCenter).trans (by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hEnlarged hDirectFactorNonneg)

@[blueprint "lem:get-center-squared-error-small"
  (statement := /-- For $0<\alpha<1/100$, put $\rho=3\alpha/((1-\alpha)(1-2\alpha))$.  Then
  \[
    (1+6\sqrt\rho+4\rho)
      \left(1+6\sqrt{\frac{\rho}{1-\rho}}\right)-1
      \leq1000\sqrt\alpha.
  \] -/)
  (proof := /-- On this interval, $0<\rho<1/8$, $\rho\leq4\alpha$, and $\rho/(1-\rho)\leq8\alpha$.  Hence $\sqrt\rho\leq2\sqrt\alpha$ and $\sqrt{\rho/(1-\rho)}\leq3\sqrt\alpha$.  Expanding the product and using $0<\sqrt\alpha<1$ gives the stated, deliberately generous constant. -/)
  (title := /-- A small-parameter bound for the squared error factor -/)
  (latexEnv := "lemma")]
lemma get_center_squared_error_small (alpha : ℝ)
    (hAlphaPos : 0 < alpha) (hAlphaSmall : alpha < (1 : ℝ) / 100) :
    let ratio := 3 * alpha / ((1 - alpha) * (1 - 2 * alpha))
    (1 + 6 * Real.sqrt ratio + 4 * ratio) *
        (1 + 6 * Real.sqrt (ratio / (1 - ratio))) - 1 ≤
      1000 * Real.sqrt alpha := by
  dsimp only
  let ratio := 3 * alpha / ((1 - alpha) * (1 - 2 * alpha))
  have hDenominatorPos : 0 < (1 - alpha) * (1 - 2 * alpha) := by
    apply mul_pos <;> linarith
  have hRatioPos : 0 < ratio := by
    dsimp [ratio]
    positivity
  have hRatioLe : ratio ≤ 4 * alpha := by
    dsimp [ratio]
    apply (div_le_iff₀ hDenominatorPos).2
    nlinarith [sq_nonneg alpha]
  have hRatioLt : ratio < (1 : ℝ) / 8 := by
    nlinarith
  have hOneMinusRatio : 0 < 1 - ratio := by linarith
  have hSecondRatioLe : ratio / (1 - ratio) ≤ 8 * alpha := by
    have hRatioFraction : ratio / (1 - ratio) ≤ 2 * ratio := by
      apply (div_le_iff₀ hOneMinusRatio).2
      nlinarith [sq_nonneg ratio]
    linarith
  let rootAlpha := Real.sqrt alpha
  let rootRatio := Real.sqrt ratio
  let rootSecond := Real.sqrt (ratio / (1 - ratio))
  have hRootAlphaSq : rootAlpha ^ 2 = alpha := Real.sq_sqrt hAlphaPos.le
  have hRootRatioSq : rootRatio ^ 2 = ratio := Real.sq_sqrt hRatioPos.le
  have hSecondRatioNonneg : 0 ≤ ratio / (1 - ratio) := by positivity
  have hRootSecondSq : rootSecond ^ 2 = ratio / (1 - ratio) :=
    Real.sq_sqrt hSecondRatioNonneg
  have hRootAlphaNonneg : 0 ≤ rootAlpha := Real.sqrt_nonneg alpha
  have hRootRatioNonneg : 0 ≤ rootRatio := Real.sqrt_nonneg ratio
  have hRootSecondNonneg : 0 ≤ rootSecond :=
    Real.sqrt_nonneg (ratio / (1 - ratio))
  have hRootRatioLe : rootRatio ≤ 2 * rootAlpha := by
    nlinarith [sq_nonneg (rootRatio + 2 * rootAlpha)]
  have hRootSecondLe : rootSecond ≤ 3 * rootAlpha := by
    nlinarith [sq_nonneg (rootSecond + 3 * rootAlpha)]
  have hRootAlphaLeOne : rootAlpha ≤ 1 := by
    nlinarith [sq_nonneg (rootAlpha + 1)]
  have hRootAlphaSqLe : rootAlpha ^ 2 ≤ rootAlpha := by
    nlinarith [mul_nonneg hRootAlphaNonneg (sub_nonneg.mpr hRootAlphaLeOne)]
  have hRootProduct : rootRatio * rootSecond ≤
      6 * rootAlpha ^ 2 := by
    have hProduct := mul_le_mul hRootRatioLe hRootSecondLe
      hRootSecondNonneg (mul_nonneg (by norm_num) hRootAlphaNonneg)
    nlinarith
  have hRatioTimesRoot : ratio * rootSecond ≤
      12 * rootAlpha ^ 3 := by
    have hRatioAsRoot : ratio = rootRatio ^ 2 := hRootRatioSq.symm
    rw [hRatioAsRoot]
    have hRootRatioSqLe : rootRatio ^ 2 ≤ 4 * rootAlpha ^ 2 := by
      nlinarith [sq_nonneg (rootRatio + 2 * rootAlpha)]
    have hProduct := mul_le_mul hRootRatioSqLe hRootSecondLe
      hRootSecondNonneg (by positivity)
    nlinarith
  have hRootAlphaCubeLe : rootAlpha ^ 3 ≤ rootAlpha := by
    have hSquaredLeOne : rootAlpha ^ 2 ≤ 1 := by nlinarith
    have hProduct := mul_le_mul_of_nonneg_left hSquaredLeOne hRootAlphaNonneg
    nlinarith
  change (1 + 6 * rootRatio + 4 * ratio) *
      (1 + 6 * rootSecond) - 1 ≤ 1000 * rootAlpha
  nlinarith [hRootRatioLe, hRootSecondLe, hRootProduct,
    hRatioTimesRoot, hRootAlphaSqLe, hRootAlphaCubeLe]

@[blueprint "lem:get-center-robustness"
  (statement := /-- There is a family of functions $\eta_q:\mathbb R\to\mathbb R$, indexed by $q\in\mathbb N$ and independent of the metric instance, such that, for each $q\in\{1,2\}$,
  \[
    \eta_q(\alpha)=O\bigl(\alpha^{1/q}\bigr)
    \qquad(\alpha\to0^+\text{ within }(0,1/2)).
  \]
  For every finite metric space $V$, all finite subsets $T,X\subseteq V$, every $q\in\{1,2\}$, every $0<\alpha<1/2$, and all $c,a\in V$, suppose
  \[
    |T\setminus X|\leq\alpha|T|,
    \qquad |X\setminus T|\leq\alpha|X|.
  \]
  If \cref{def:get-center} returns $a$ on input $(X,q,\alpha)$, then
  \[
    \operatorname{cost}_q(T,a)
      \leq \bigl(1+\eta_q(\alpha)\bigr)\operatorname{cost}_q(T,c).
  \]
  The same family $\eta_q$ works uniformly for all choices of $V,T,X,c$, and $a$. -/)
  (proof := /-- Put
  \[
    \rho(\alpha)=\frac{3\alpha}{(1-\alpha)(1-2\alpha)},
    \qquad
    F(\alpha)=(1+6\sqrt{\rho(\alpha)}+4\rho(\alpha))
      \left(1+6\sqrt{\frac{\rho(\alpha)}{1-\rho(\alpha)}}\right).
  \]
  Define the total error family by
  \[
    \eta_1(\alpha)=100\alpha+
      \begin{cases}0,&\alpha<1/100,\\
      14\alpha/(1-2\alpha),&\alpha\geq1/100,\end{cases}
  \]
  \[
    \eta_2(\alpha)=1000\sqrt\alpha+
      \begin{cases}0,&\alpha<1/100,\\
      F(\alpha)-1,&\alpha\geq1/100,\end{cases}
  \]
  and set \(\eta_q=0\) for all remaining indices.  In a right neighborhood of zero the correction terms vanish.  Consequently \(\eta_1(\alpha)=100\alpha\) and \(\eta_2(\alpha)=1000\sqrt\alpha\) there, proving the two required Big-O estimates.

  For \(q=1\), \cref{lem:get-center-linear-robustness} gives the multiplicative error \(14\alpha/(1-2\alpha)\).  When \(\alpha<1/100\), this is at most \(100\alpha\); otherwise it is one of the two nonnegative summands defining \(\eta_1\).  Thus the linear estimate follows.

  For \(q=2\), \cref{lem:get-center-squared-robustness} gives the factor \(F(\alpha)\).  When \(\alpha<1/100\), \cref{lem:get-center-squared-error-small} gives \(F(\alpha)-1\leq1000\sqrt\alpha\); otherwise \(F(\alpha)-1\) is one of the summands defining \(\eta_2\).  These estimates are uniform in the finite metric space and in all centers and classes, which proves the assertion. -/)
  (title := /-- Robustness of GetCenter under label contamination -/)
  (latexEnv := "lemma")]
lemma get_center_robustness :
    ∃ centerError : ℕ → ℝ → ℝ,
      (∀ q : ℕ, q = 1 ∨ q = 2 →
        Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioo 0 ((1 : ℝ) / 2)))
          (centerError q)
          (fun alpha : ℝ => Real.rpow alpha ((q : ℝ)⁻¹))) ∧
      ∀ {V : Type} [MetricSpace V] [Fintype V] [DecidableEq V]
        (referenceClass predictedClass : Finset V) (q : ℕ),
        q = 1 ∨ q = 2 →
        ∀ (alpha : ℝ) (referenceCenter selectedCenter : V),
          0 < alpha → alpha < (1 : ℝ) / 2 →
          ((referenceClass \ predictedClass).card : ℝ) ≤
              alpha * (referenceClass.card : ℝ) →
          ((predictedClass \ referenceClass).card : ℝ) ≤
              alpha * (predictedClass.card : ℝ) →
          (get_center predictedClass q alpha).output = some selectedCenter →
          single_center_cost q referenceClass selectedCenter ≤
            (1 + centerError q alpha) *
              single_center_cost q referenceClass referenceCenter := by
  let ratio := fun alpha : ℝ =>
    3 * alpha / ((1 - alpha) * (1 - 2 * alpha))
  let squaredFactor := fun alpha : ℝ =>
    (1 + 6 * Real.sqrt (ratio alpha) + 4 * ratio alpha) *
      (1 + 6 * Real.sqrt (ratio alpha / (1 - ratio alpha)))
  let centerError := fun q : ℕ => fun alpha : ℝ =>
    if q = 1 then
      100 * alpha + if alpha < (1 : ℝ) / 100 then 0
        else 14 * alpha / (1 - 2 * alpha)
    else if q = 2 then
      1000 * Real.sqrt alpha + if alpha < (1 : ℝ) / 100 then 0
        else squaredFactor alpha - 1
    else 0
  refine ⟨centerError, ?_, ?_⟩
  · intro q hQ
    rcases hQ with rfl | rfl
    · apply Asymptotics.IsBigO.of_bound 100
      have hSmallNhds : Set.Iio ((1 : ℝ) / 100) ∈ nhds 0 :=
        Iio_mem_nhds (by norm_num)
      have hSmall : ∀ᶠ alpha : ℝ in
          nhdsWithin 0 (Set.Ioo 0 ((1 : ℝ) / 2)), alpha < (1 : ℝ) / 100 :=
        Filter.Eventually.filter_mono inf_le_left hSmallNhds
      filter_upwards [self_mem_nhdsWithin, hSmall] with alpha hInterval hAlphaSmall
      have hAlphaNonneg : 0 ≤ alpha := hInterval.1.le
      norm_num [centerError, hAlphaSmall, Real.rpow_one,
        Real.norm_of_nonneg hAlphaNonneg]
    · apply Asymptotics.IsBigO.of_bound 1000
      have hSmallNhds : Set.Iio ((1 : ℝ) / 100) ∈ nhds 0 :=
        Iio_mem_nhds (by norm_num)
      have hSmall : ∀ᶠ alpha : ℝ in
          nhdsWithin 0 (Set.Ioo 0 ((1 : ℝ) / 2)), alpha < (1 : ℝ) / 100 :=
        Filter.Eventually.filter_mono inf_le_left hSmallNhds
      filter_upwards [self_mem_nhdsWithin, hSmall] with alpha hInterval hAlphaSmall
      have hAlphaNonneg : 0 ≤ alpha := hInterval.1.le
      have hRpow : Real.rpow alpha (((2 : ℕ) : ℝ)⁻¹) = Real.sqrt alpha := by
        rw [show (((2 : ℕ) : ℝ)⁻¹) = 1 / (2 : ℝ) by norm_num]
        exact (Real.sqrt_eq_rpow alpha).symm
      norm_num [centerError, hAlphaSmall, hRpow,
        Real.norm_of_nonneg (Real.sqrt_nonneg alpha)]
      rw [← Real.sqrt_eq_rpow, abs_of_nonneg (Real.sqrt_nonneg alpha)]
  · intro V _ _ _ referenceClass predictedClass q hQ alpha referenceCenter
      selectedCenter hAlphaPos hAlphaLt hFalseNegative hFalsePositive hOutput
    have hReferenceCostNonneg :
        0 ≤ single_center_cost q referenceClass referenceCenter := by
      unfold single_center_cost
      exact Finset.sum_nonneg fun point hPoint => pow_nonneg dist_nonneg q
    rcases hQ with rfl | rfl
    · have hLinear := get_center_linear_robustness referenceClass predictedClass
        alpha referenceCenter selectedCenter hAlphaPos hAlphaLt hFalseNegative
        hFalsePositive hOutput
      have hDenominatorPos : 0 < 1 - 2 * alpha := by linarith
      have hErrorBound : 14 * alpha / (1 - 2 * alpha) ≤ centerError 1 alpha := by
        dsimp [centerError]
        by_cases hAlphaSmall : alpha < (1 : ℝ) / 100
        · rw [if_pos hAlphaSmall, add_zero]
          apply (div_le_iff₀ hDenominatorPos).2
          nlinarith
        · rw [if_neg hAlphaSmall]
          have hAlphaNonneg : 0 ≤ alpha := hAlphaPos.le
          nlinarith
      exact hLinear.trans (mul_le_mul_of_nonneg_right
        (by linarith : 1 + 14 * alpha / (1 - 2 * alpha) ≤
          1 + centerError 1 alpha) hReferenceCostNonneg)
    · have hSquared := get_center_squared_robustness referenceClass predictedClass
        alpha referenceCenter selectedCenter hAlphaPos hAlphaLt hFalseNegative
        hFalsePositive hOutput
      have hErrorBound : squaredFactor alpha - 1 ≤ centerError 2 alpha := by
        dsimp [centerError]
        by_cases hAlphaSmall : alpha < (1 : ℝ) / 100
        · rw [if_pos hAlphaSmall, add_zero]
          dsimp [squaredFactor, ratio]
          exact get_center_squared_error_small alpha hAlphaPos hAlphaSmall
        · rw [if_neg hAlphaSmall]
          nlinarith [Real.sqrt_nonneg alpha]
      have hCoefficient : squaredFactor alpha ≤ 1 + centerError 2 alpha := by
        linarith
      change single_center_cost 2 referenceClass selectedCenter ≤
        (1 + centerError 2 alpha) *
          single_center_cost 2 referenceClass referenceCenter
      exact hSquared.trans (mul_le_mul_of_nonneg_right hCoefficient
        hReferenceCostNonneg)

@[blueprint "lem:algorithm-one-global-approximation"
  (statement := /-- There is a function $\varepsilon:\mathbb N\to(\mathbb R\to\mathbb R)$, independent of the metric instance, such that, for every $q\in\{1,2\}$,
  \[
    \varepsilon_q(\alpha)=O(\alpha^{1/q})
    \qquad(\alpha\to0^+\text{ within }(0,1/2)).
  \]
  More precisely, let $V$ be any finite metric space, let $X\subseteq V$ be finite, and let $k,q\in\mathbb N$ satisfy $0<k\leq |V|$ and $q\in\{1,2\}$.  For every $\alpha,\lambda\in\mathbb R$, every predictor and reference labeling $\Pi,L:V\to\operatorname{Fin}(k)$, and every reference-center map $c:\operatorname{Fin}(k)\to V$, if $0<\alpha<1/2$ and \cref{def:predictor-label-error} holds for $(X,k,q,\alpha,\lambda,\Pi,L,c)$, then the output of \cref{def:algorithm-one} consists of exactly $k$ centers and satisfies
  \[
    \operatorname{cost}_q(X,A_1(X,\Pi))
      \leq (1+\varepsilon_q(\alpha))\operatorname{OPT}_q(X,k).
  \] -/)
  (proof := /-- Choose the family $\eta_q$ supplied by \cref{lem:get-center-robustness} and define
  \[
    \varepsilon_q(\alpha)
      =|\eta_q(\alpha)|+\alpha+|\eta_q(\alpha)|\alpha
      =(1+|\eta_q(\alpha)|)(1+\alpha)-1.
  \]
  Taking absolute values preserves the Big-O estimate for $\eta_q$.  On $(0,1/2)$, the identity function is bounded and is $O(\alpha^{1/q})$ for $q\in\{1,2\}$; for $q=2$ this follows from $\alpha\leq\sqrt\alpha$.  Hence the sum above is $O(\alpha^{1/q})$.

  Fix an admissible instance.  For each $i\in\operatorname{Fin}(k)$, let
  \[
    T_i=\{x\in X:L(x)=i\},
    \qquad X_i=\{x\in X:\Pi(x)=i\}.
  \]
  The false-negative and false-positive inequalities in \cref{def:predictor-label-error}, together with $\lambda\leq\alpha$, give
  \[
    |T_i\setminus X_i|\leq\alpha|T_i|,
    \qquad |X_i\setminus T_i|\leq\alpha|X_i|.
  \]
  Since $k>0$ and $k\leq|V|$, the ambient space is nonempty.  Unfolding \cref{def:get-center} and \cref{def:costed-list-fold} shows that its scan therefore returns some center $a_i$ on every $X_i$.  Applying \cref{lem:get-center-robustness} to $(T_i,X_i,c_i,a_i)$ gives
  \[
    \operatorname{cost}_q(T_i,a_i)
      \leq(1+\eta_q(\alpha))\operatorname{cost}_q(T_i,c_i).
  \]
  Each reference cost is nonnegative and $\eta_q(\alpha)\leq|\eta_q(\alpha)|$, so summing these inequalities yields
  \[
    \sum_i\operatorname{cost}_q(T_i,a_i)
      \leq(1+|\eta_q(\alpha)|)
        \sum_i\operatorname{cost}_q(T_i,c_i).
  \]
  By \cref{def:distance-to-centers}, the distance cost of a point $x\in T_i$ to any center set containing $a_i$ is at most $d(x,a_i)^q$.  The classes $T_i$ partition $X$, and therefore the clustering cost of such a center set is at most the left-hand side above.  The reference-cost clause of \cref{def:predictor-label-error} bounds the final sum by $(1+\alpha)\operatorname{OPT}_q(X,k)$.  Multiplication by the nonnegative factor $1+|\eta_q(\alpha)|$ gives the asserted factor $1+\varepsilon_q(\alpha)$.

  It remains to identify the operational output.  The first fold in \cref{def:algorithm-one} inserts every $a_i$, adds at most one center for each of the $k$ labels, and hence produces a set of cardinality at most $k$.  In the padding fold, the current set is preserved, its cardinality never exceeds $k$, and each scanned ambient point is inserted whenever the cardinality is still smaller than $k$.  If the final cardinality were smaller than $k$, every point of $V$ would have been inserted, contradicting $k\leq|V|$.  Thus the output contains every $a_i$, has cardinality exactly $k$, and satisfies the preceding cost estimate. -/)
  (title := /-- Global approximation bridge for Algorithm 1 -/)
  (latexEnv := "lemma")]
lemma algorithm_one_global_approximation :
    ∃ approximationError : ℕ → ℝ → ℝ,
      (∀ q : ℕ, q = 1 ∨ q = 2 →
        Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioo 0 ((1 : ℝ) / 2)))
          (approximationError q)
          (fun alpha : ℝ => Real.rpow alpha ((q : ℝ)⁻¹))) ∧
      ∀ {V : Type} [MetricSpace V] [Fintype V] [DecidableEq V]
        (points : Finset V) (k q : ℕ),
        0 < k → k ≤ Fintype.card V → q = 1 ∨ q = 2 →
        ∀ (alpha lambda : ℝ) (predictor referenceLabel : V → Fin k)
          (referenceCenter : Fin k → V),
          0 < alpha → alpha < (1 : ℝ) / 2 →
          predictor_label_error points k q alpha lambda predictor referenceLabel
            referenceCenter →
          (algorithm_one.run points k q alpha predictor).output.card = k ∧
          clustering_cost q points
              (algorithm_one.run points k q alpha predictor).output ≤
            (1 + approximationError q alpha) * optimal_clustering_cost q k points := by
  classical
  obtain ⟨centerError, hCenterBigO, hCenterRobustness⟩ :=
    get_center_robustness
  let approximationError := fun q : ℕ => fun alpha : ℝ =>
    |centerError q alpha| + alpha + |centerError q alpha| * alpha
  refine ⟨approximationError, ?_, ?_⟩
  · intro q hQ
    let l := nhdsWithin 0 (Set.Ioo 0 ((1 : ℝ) / 2))
    let comparison := fun alpha : ℝ =>
      Real.rpow alpha ((q : ℝ)⁻¹)
    have hAbsolute :
        (fun alpha : ℝ => |centerError q alpha|) =O[l] comparison := by
      simpa only [Real.norm_eq_abs] using
        (hCenterBigO q hQ).norm_left
    have hAlphaBound :
        (fun alpha : ℝ => alpha) =O[l] (fun _ : ℝ => (1 : ℝ)) := by
      apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [self_mem_nhdsWithin] with alpha hAlpha
      have hAlphaAbs : |alpha| ≤ 1 := by
        rw [abs_of_pos hAlpha.1]
        linarith [hAlpha.2]
      simpa using hAlphaAbs
    have hProduct :
        (fun alpha : ℝ => |centerError q alpha| * alpha) =O[l] comparison := by
      simpa only [mul_one] using hAbsolute.mul hAlphaBound
    have hAlpha :
        (fun alpha : ℝ => alpha) =O[l] comparison := by
      rcases hQ with rfl | rfl
      · simpa [comparison, Real.rpow_one] using
          (Asymptotics.isBigO_refl (fun alpha : ℝ => alpha) l)
      · apply Asymptotics.IsBigO.of_bound 1
        filter_upwards [self_mem_nhdsWithin] with alpha hAlphaInterval
        have hAlphaNonneg : 0 ≤ alpha := hAlphaInterval.1.le
        have hRpow :
            Real.rpow alpha (((2 : ℕ) : ℝ)⁻¹) = Real.sqrt alpha := by
          rw [show (((2 : ℕ) : ℝ)⁻¹) = 1 / (2 : ℝ) by norm_num]
          exact (Real.sqrt_eq_rpow alpha).symm
        have hAlphaLeSqrt : alpha ≤ Real.sqrt alpha := by
          apply (Real.le_sqrt hAlphaNonneg hAlphaNonneg).2
          have hAlphaLeOne : alpha ≤ 1 := by linarith [hAlphaInterval.2]
          nlinarith
        dsimp only [comparison]
        rw [hRpow, Real.norm_of_nonneg hAlphaNonneg,
          Real.norm_of_nonneg (Real.sqrt_nonneg alpha)]
        simpa using hAlphaLeSqrt
    simpa only [approximationError] using
      (hAbsolute.add hAlpha).add hProduct
  · intro V _ _ _ points k q hKPos hKCard hQ alpha lambda predictor
      referenceLabel referenceCenter hAlphaPos hAlphaLt hPredictor
    rcases hPredictor with
      ⟨hLambdaNonneg, hLambdaAlpha, hReferenceInjective, hNearest,
        hReferenceBound, hLabelError⟩
    haveI : Nonempty V :=
      Fintype.card_pos_iff.mp (lt_of_lt_of_le hKPos hKCard)
    have hCostedOutput {A B : Type} (items : List B) (initial : A)
        (step : A → B → costed_computation A) :
        (costed_list_fold items initial step).output =
          items.foldl (fun current item => (step current item).output) initial := by
      unfold costed_list_fold
      have hAux (remaining : List B) (current : costed_computation A) :
          (remaining.foldl (fun computation item =>
            let successor := step computation.output item
            ⟨successor.output, computation.steps + successor.steps + 1⟩)
              current).output =
            remaining.foldl (fun state item => (step state item).output)
              current.output := by
        induction remaining generalizing current with
        | nil => rfl
        | cons item rest inductionHypothesis =>
            simp only [List.foldl_cons]
            exact inductionHypothesis _
      exact hAux items ⟨initial, 0⟩
    have hGetCenterSome (predictedClass : Finset V) :
        ∃ selectedCenter : V,
          (get_center predictedClass q alpha).output = some selectedCenter := by
      let score := fun center : V =>
        if q = 2 then
          trimmed_single_center_cost q alpha predictedClass center
        else single_center_cost q predictedClass center
      let chooseCenter := fun current : Option V => fun candidate : V =>
        match current with
        | none => some candidate
        | some incumbent =>
            if score candidate < score incumbent then some candidate
            else some incumbent
      let centerStep := fun current : Option V => fun candidate : V =>
        (⟨chooseCenter current candidate,
          2 * predictedClass.card ^ 2 + 2 * predictedClass.card + 1⟩ :
          costed_computation (Option V))
      have hOutput :
          (get_center predictedClass q alpha).output =
            (Finset.univ.toList : List V).foldl chooseCenter none := by
        change
          (costed_list_fold (Finset.univ.toList : List V) none
            centerStep).output =
            (Finset.univ.toList : List V).foldl chooseCenter none
        exact hCostedOutput (Finset.univ.toList : List V) none centerStep
      have hPreserved (items : List V) (current : Option V)
          (hCurrent : ∃ center, current = some center) :
          ∃ center, items.foldl chooseCenter current = some center := by
        induction items generalizing current with
        | nil => simpa using hCurrent
        | cons candidate rest inductionHypothesis =>
            apply inductionHypothesis
            rcases hCurrent with ⟨incumbent, rfl⟩
            by_cases hBetter : score candidate < score incumbent
            · exact ⟨candidate, by simp [chooseCenter, hBetter]⟩
            · exact ⟨incumbent, by simp [chooseCenter, hBetter]⟩
      cases hItems : (Finset.univ.toList : List V) with
      | nil =>
          exfalso
          have hEmpty : (Finset.univ : Finset V) = ∅ := by
            simpa using hItems
          exact Finset.univ_nonempty.ne_empty hEmpty
      | cons first rest =>
          rw [hOutput, hItems, List.foldl_cons]
          exact hPreserved rest (some first) ⟨first, rfl⟩
    have hAllCenters :
        ∀ label : Fin k, ∃ selectedCenter : V,
          (get_center (points.filter fun point => predictor point = label)
            q alpha).output = some selectedCenter :=
      fun label => hGetCenterSome
        (points.filter fun point => predictor point = label)
    choose selectedCenter hSelectedCenter using hAllCenters
    let selectedStep := fun centers : Finset V => fun label : Fin k =>
      match (get_center (points.filter fun point => predictor point = label)
          q alpha).output with
      | none => centers
      | some center => insert center centers
    let selectedCenters : Finset V :=
      (Finset.univ.toList : List (Fin k)).foldl selectedStep ∅
    have hSelectedStepSubset (centers : Finset V) (label : Fin k) :
        centers ⊆ selectedStep centers label := by
      intro center hCenter
      simp only [selectedStep]
      split
      · exact hCenter
      · exact Finset.mem_insert_of_mem hCenter
    have hFoldSubset (items : List (Fin k)) (centers : Finset V) :
        centers ⊆ items.foldl selectedStep centers := by
      induction items generalizing centers with
      | nil => exact Finset.Subset.rfl
      | cons label rest inductionHypothesis =>
          simp only [List.foldl_cons]
          exact (hSelectedStepSubset centers label).trans
            (inductionHypothesis (selectedStep centers label))
    have hSelectedCenterMemList (items : List (Fin k))
        (centers : Finset V) (label : Fin k) (hLabel : label ∈ items) :
        selectedCenter label ∈ items.foldl selectedStep centers := by
      induction items generalizing centers with
      | nil => simp at hLabel
      | cons head rest inductionHypothesis =>
          rw [List.mem_cons] at hLabel
          simp only [List.foldl_cons]
          rcases hLabel with rfl | hLabel
          · apply hFoldSubset rest (selectedStep centers label)
            simp [selectedStep, hSelectedCenter label]
          · exact inductionHypothesis (selectedStep centers head) hLabel
    have hSelectedCenterMem (label : Fin k) :
        selectedCenter label ∈ selectedCenters := by
      apply hSelectedCenterMemList (Finset.univ.toList : List (Fin k)) ∅ label
      simp
    have hSelectedStepCard (centers : Finset V) (label : Fin k) :
        (selectedStep centers label).card ≤ centers.card + 1 := by
      simp only [selectedStep]
      split
      · omega
      · exact Finset.card_insert_le _ _
    have hSelectedCardList (items : List (Fin k)) (centers : Finset V) :
        (items.foldl selectedStep centers).card ≤ centers.card + items.length := by
      induction items generalizing centers with
      | nil => simp
      | cons label rest inductionHypothesis =>
          simp only [List.foldl_cons, List.length_cons]
          calc
            (rest.foldl selectedStep (selectedStep centers label)).card ≤
                (selectedStep centers label).card + rest.length :=
              inductionHypothesis (selectedStep centers label)
            _ ≤ centers.card + (rest.length + 1) := by
              have := hSelectedStepCard centers label
              omega
    have hSelectedCard : selectedCenters.card ≤ k := by
      simpa [selectedCenters] using
        hSelectedCardList (Finset.univ.toList : List (Fin k)) ∅
    let paddingStep := fun centers : Finset V => fun point : V =>
      if centers.card < k then insert point centers else centers
    let outputCenters : Finset V :=
      (Finset.univ.toList : List V).foldl paddingStep selectedCenters
    have hPaddingInvariant (items : List V) (centers : Finset V)
        (hCentersCard : centers.card ≤ k) :
        centers ⊆ items.foldl paddingStep centers ∧
          (items.foldl paddingStep centers).card ≤ k ∧
          ((items.foldl paddingStep centers).card = k ∨
            ∀ point ∈ items, point ∈ items.foldl paddingStep centers) := by
      induction items generalizing centers with
      | nil =>
          refine ⟨Finset.Subset.rfl, hCentersCard, Or.inr ?_⟩
          simp
      | cons point rest inductionHypothesis =>
          simp only [List.foldl_cons]
          by_cases hSmall : centers.card < k
          · have hNextCard : (paddingStep centers point).card ≤ k := by
              simp only [paddingStep, if_pos hSmall]
              have := Finset.card_insert_le (s := centers) (a := point)
              omega
            obtain ⟨hNextSubset, hFinalCard, hFinal⟩ :=
              inductionHypothesis (paddingStep centers point) hNextCard
            have hCurrentNext : centers ⊆ paddingStep centers point := by
              simp [paddingStep, hSmall]
            refine ⟨hCurrentNext.trans hNextSubset, hFinalCard, ?_⟩
            · rcases hFinal with hCard | hContains
              · exact Or.inl hCard
              · refine Or.inr ?_
                intro candidate hCandidate
                rw [List.mem_cons] at hCandidate
                rcases hCandidate with rfl | hCandidate
                · apply hNextSubset
                  simp [paddingStep, hSmall]
                · exact hContains candidate hCandidate
          · have hCurrentCard : centers.card = k := by omega
            have hNext : paddingStep centers point = centers := by
              simp [paddingStep, hSmall]
            obtain ⟨hNextSubset, hFinalCard, _⟩ :=
              inductionHypothesis centers hCentersCard
            rw [hNext]
            refine ⟨hNextSubset, hFinalCard, Or.inl ?_⟩
            exact le_antisymm hFinalCard
              (hCurrentCard ▸ Finset.card_le_card hNextSubset)
    obtain ⟨hSelectedSubsetOutput, hOutputCardLe, hOutputAlternative⟩ :=
      hPaddingInvariant (Finset.univ.toList : List V) selectedCenters
        hSelectedCard
    have hOutputCard : outputCenters.card = k := by
      change ((Finset.univ.toList : List V).foldl paddingStep
        selectedCenters).card = k
      rcases hOutputAlternative with hCard | hContains
      · exact hCard
      · have hUniverseSubset :
            (Finset.univ : Finset V) ⊆
              (Finset.univ.toList : List V).foldl paddingStep
                selectedCenters := by
          intro point hPoint
          exact hContains point (by simpa using hPoint)
        have hAmbientCard :
            Fintype.card V ≤
              ((Finset.univ.toList : List V).foldl paddingStep
                selectedCenters).card := by
          simpa using Finset.card_le_card hUniverseSubset
        omega
    have hSelectedSubset : selectedCenters ⊆ outputCenters := by
      exact hSelectedSubsetOutput
    have hAlgorithmOutput :
        (algorithm_one.run points k q alpha predictor).output =
          outputCenters := by
      simp only [algorithm_one, costed_then]
      change
        (costed_list_fold (Finset.univ.toList : List V)
          (costed_list_fold (Finset.univ.toList : List (Fin k)) ∅
            (fun centers label =>
              let best := get_center
                (points.filter fun point => predictor point = label) q alpha
              ⟨match best.output with
                | none => centers
                | some center => insert center centers,
                best.steps⟩)).output
          (fun centers point =>
            ⟨if centers.card < k then insert point centers else centers,
              1⟩)).output = outputCenters
      rw [hCostedOutput, hCostedOutput]
    have hFalseNegative (label : Fin k) :
        (((points.filter fun point => referenceLabel point = label) \
          (points.filter fun point => predictor point = label)).card : ℝ) ≤
          alpha *
            ((points.filter fun point =>
              referenceLabel point = label).card : ℝ) := by
      have hSet :
          (points.filter fun point => referenceLabel point = label) \
              (points.filter fun point => predictor point = label) =
            points.filter fun point =>
              referenceLabel point = label ∧ predictor point ≠ label := by
        ext point
        simp only [Finset.mem_sdiff, Finset.mem_filter, not_and, and_iff_left_iff_imp]
        tauto
      rw [hSet]
      exact (hLabelError label).1.trans
        (mul_le_mul_of_nonneg_right hLambdaAlpha (Nat.cast_nonneg _))
    have hFalsePositive (label : Fin k) :
        (((points.filter fun point => predictor point = label) \
          (points.filter fun point => referenceLabel point = label)).card : ℝ) ≤
          alpha *
            ((points.filter fun point =>
              predictor point = label).card : ℝ) := by
      have hSet :
          (points.filter fun point => predictor point = label) \
              (points.filter fun point => referenceLabel point = label) =
            points.filter fun point =>
              predictor point = label ∧ referenceLabel point ≠ label := by
        ext point
        simp only [Finset.mem_sdiff, Finset.mem_filter, not_and, and_iff_left_iff_imp]
        tauto
      rw [hSet]
      exact (hLabelError label).2.trans
        (mul_le_mul_of_nonneg_right hLambdaAlpha (Nat.cast_nonneg _))
    have hClassBound (label : Fin k) :
        single_center_cost q
            (points.filter fun point => referenceLabel point = label)
            (selectedCenter label) ≤
          (1 + centerError q alpha) *
            single_center_cost q
              (points.filter fun point => referenceLabel point = label)
              (referenceCenter label) := by
      exact hCenterRobustness
        (points.filter fun point => referenceLabel point = label)
        (points.filter fun point => predictor point = label) q hQ alpha
        (referenceCenter label) (selectedCenter label) hAlphaPos hAlphaLt
        (hFalseNegative label) (hFalsePositive label)
        (hSelectedCenter label)
    have hReferenceCostNonneg :
        0 ≤ ∑ label : Fin k,
          single_center_cost q
            (points.filter fun point => referenceLabel point = label)
            (referenceCenter label) := by
      apply Finset.sum_nonneg
      intro label hLabel
      unfold single_center_cost
      exact Finset.sum_nonneg fun point hPoint =>
        pow_nonneg dist_nonneg q
    have hSelectedCostBound :
        (∑ label : Fin k,
          single_center_cost q
            (points.filter fun point => referenceLabel point = label)
            (selectedCenter label)) ≤
          (1 + |centerError q alpha|) *
            ∑ label : Fin k,
              single_center_cost q
                (points.filter fun point => referenceLabel point = label)
                (referenceCenter label) := by
      calc
        (∑ label : Fin k,
            single_center_cost q
              (points.filter fun point => referenceLabel point = label)
              (selectedCenter label)) ≤
            ∑ label : Fin k,
              (1 + centerError q alpha) *
                single_center_cost q
                  (points.filter fun point => referenceLabel point = label)
                  (referenceCenter label) := by
              exact Finset.sum_le_sum fun label hLabel => hClassBound label
        _ = (1 + centerError q alpha) *
              ∑ label : Fin k,
                single_center_cost q
                  (points.filter fun point => referenceLabel point = label)
                  (referenceCenter label) := by
              rw [Finset.mul_sum]
        _ ≤ (1 + |centerError q alpha|) *
              ∑ label : Fin k,
                single_center_cost q
                  (points.filter fun point => referenceLabel point = label)
                  (referenceCenter label) := by
              apply mul_le_mul_of_nonneg_right _ hReferenceCostNonneg
              linarith [le_abs_self (centerError q alpha)]
    have hDistanceBound (point : V) :
        distance_to_centers q outputCenters point ≤
          dist point (selectedCenter (referenceLabel point)) ^ q := by
      unfold distance_to_centers
      apply csInf_le
      · refine ⟨0, ?_⟩
        rintro value ⟨center, hCenter, rfl⟩
        exact pow_nonneg dist_nonneg q
      · refine ⟨selectedCenter (referenceLabel point), ?_, rfl⟩
        exact hSelectedSubset
          (hSelectedCenterMem (referenceLabel point))
    have hAssignmentBound :
        clustering_cost q points outputCenters ≤
          ∑ label : Fin k,
            single_center_cost q
              (points.filter fun point => referenceLabel point = label)
              (selectedCenter label) := by
      unfold clustering_cost
      calc
        (∑ point ∈ points, distance_to_centers q outputCenters point) ≤
            ∑ point ∈ points,
              dist point (selectedCenter (referenceLabel point)) ^ q := by
          exact Finset.sum_le_sum fun point hPoint =>
            hDistanceBound point
        _ = ∑ label : Fin k,
              single_center_cost q
                (points.filter fun point => referenceLabel point = label)
                (selectedCenter label) := by
          simp only [single_center_cost]
          symm
          simp_rw [Finset.sum_filter]
          rw [Finset.sum_comm]
          simp
    have hCoefficientNonneg : 0 ≤ 1 + |centerError q alpha| := by
      positivity
    have hFinalCost :
        clustering_cost q points outputCenters ≤
          ((1 + |centerError q alpha|) * (1 + alpha)) *
            optimal_clustering_cost q k points := by
      calc
        clustering_cost q points outputCenters ≤
            ∑ label : Fin k,
              single_center_cost q
                (points.filter fun point => referenceLabel point = label)
                (selectedCenter label) := hAssignmentBound
        _ ≤ (1 + |centerError q alpha|) *
              ∑ label : Fin k,
                single_center_cost q
                  (points.filter fun point => referenceLabel point = label)
                  (referenceCenter label) := hSelectedCostBound
        _ ≤ (1 + |centerError q alpha|) *
              ((1 + alpha) * optimal_clustering_cost q k points) :=
            mul_le_mul_of_nonneg_left hReferenceBound hCoefficientNonneg
        _ = ((1 + |centerError q alpha|) * (1 + alpha)) *
              optimal_clustering_cost q k points := by ring
    constructor
    · rw [hAlgorithmOutput]
      exact hOutputCard
    · rw [hAlgorithmOutput]
      convert hFinalCost using 1
      dsimp only [approximationError]
      ring

@[blueprint "lem:algorithm-one-polynomial-runtime"
  (statement := /-- There exist natural numbers $C>0$ and $d$, independent of all inputs, such that for every finite metric space $V$, every finite set $X\subseteq V$, all $k,q\in\mathbb{N}$ and $\alpha\in\mathbb{R}$, and every predictor $\Pi:V\to\operatorname{Fin}(k)$, the operational step count of \cref{def:algorithm-one} is at most
  \[
    C\,(|V|+k+1)^d.
  \]
  Equivalently, \cref{def:algorithm-one} satisfies the uniform polynomial-time condition of \cref{def:algorithm-runs-in-polynomial-time}. -/)
  (proof := /-- An induction on the list in \cref{def:costed-list-fold} shows that a fold over $\ell$ items whose transitions cost at most $b$ has step count at most $\ell(b+1)$.  Put $n=|V|$.  Every predicted class has cardinality at most $n$, so \cref{def:get-center}, which scans the $n$ ambient candidates, costs at most $n(2n^2+2n+2)$ steps.  Applying the fold bound to the $k$ labels in \cref{def:algorithm-one}, then to its padding scan with transition cost $1$, and finally adding the composition step from \cref{def:costed-then}, gives
  \[
    k\bigl(n(2n^2+2n+2)+1\bigr)+2n+1
      \leq 8(n+k+1)^4.
  \]
  The coefficient $8$ and degree $4$ are independent of every input, which is exactly \cref{def:algorithm-runs-in-polynomial-time}. -/)
  (title := /-- Polynomial running time of Algorithm 1 -/)
  (latexEnv := "lemma")]
lemma algorithm_one_polynomial_runtime :
    algorithm_runs_in_polynomial_time algorithm_one := by
  have foldl_steps_le {A B : Type} (items : List B)
      (computation : costed_computation A)
      (step : A → B → costed_computation A) (bound : ℕ)
      (hstep : ∀ state item, (step state item).steps ≤ bound) :
      (items.foldl (fun computation item =>
        let successor := step computation.output item
        ⟨successor.output, computation.steps + successor.steps + 1⟩)
        computation).steps ≤
        computation.steps + items.length * (bound + 1) := by
    induction items generalizing computation with
    | nil => simp
    | cons item items ih =>
        rw [List.foldl_cons]
        apply le_trans (ih _)
        have h := hstep computation.output item
        dsimp
        rw [Nat.add_mul]
        omega
  have costed_list_fold_steps_le {A B : Type} (items : List B)
      (initial : A) (step : A → B → costed_computation A) (bound : ℕ)
      (hstep : ∀ state item, (step state item).steps ≤ bound) :
      (costed_list_fold items initial step).steps ≤
        items.length * (bound + 1) := by
    simpa [costed_list_fold] using
      (foldl_steps_le (A := A) (B := B) items
        (⟨initial, 0⟩ : costed_computation A) step bound hstep)
  unfold algorithm_runs_in_polynomial_time
  refine ⟨8, 4, by omega, ?_⟩
  intro V _ _ _ points k q alpha predictor
  let n := Fintype.card V
  let innerBound := n * (2 * n ^ 2 + 2 * n + 2)
  have get_center_steps_le (subset : Finset V) :
      (get_center subset q alpha).steps ≤ innerBound := by
    let centerStep : Option V → V → costed_computation (Option V) :=
      fun current candidate =>
        let score := fun center : V =>
          if q = 2 then trimmed_single_center_cost q alpha subset center
          else single_center_cost q subset center
        let next := match current with
          | none => some candidate
          | some incumbent =>
              if score candidate < score incumbent then some candidate
              else some incumbent
        ⟨next, 2 * subset.card ^ 2 + 2 * subset.card + 1⟩
    have hfold := costed_list_fold_steps_le (A := Option V) (B := V)
      (Finset.univ.toList : List V) (none : Option V) centerStep
      (2 * subset.card ^ 2 + 2 * subset.card + 1) (by
        intro state item
        exact le_rfl)
    have hcard : subset.card ≤ n := by
      simpa [n] using Finset.card_le_univ subset
    have hsq : subset.card ^ 2 ≤ n ^ 2 := by
      simpa [pow_two] using Nat.mul_le_mul hcard hcard
    have hpoly :
        2 * subset.card ^ 2 + 2 * subset.card + 2 ≤
          2 * n ^ 2 + 2 * n + 2 := by
      omega
    change (costed_list_fold (Finset.univ.toList : List V)
      (none : Option V) centerStep).steps ≤ innerBound
    calc
      _ ≤ (Finset.univ.toList : List V).length *
          (2 * subset.card ^ 2 + 2 * subset.card + 1 + 1) := hfold
      _ = n * (2 * subset.card ^ 2 + 2 * subset.card + 2) := by
        simp [n]
      _ ≤ innerBound := Nat.mul_le_mul_left n hpoly
  let selectedStep : Finset V → Fin k → costed_computation (Finset V) :=
    fun centers label =>
      let predictedClass := points.filter fun point => predictor point = label
      let best := get_center predictedClass q alpha
      ⟨match best.output with
        | none => centers
        | some center => insert center centers,
        best.steps⟩
  let selected :=
    costed_list_fold (Finset.univ.toList : List (Fin k)) ∅ selectedStep
  have hselected : selected.steps ≤ k * (innerBound + 1) := by
    have hfold := costed_list_fold_steps_le (A := Finset V) (B := Fin k)
      (Finset.univ.toList : List (Fin k)) ∅ selectedStep innerBound (by
        intro centers label
        change (get_center (points.filter fun point =>
          predictor point = label) q alpha).steps ≤ innerBound
        exact get_center_steps_le _)
    simpa [selected] using hfold
  let paddingStep : Finset V → V → costed_computation (Finset V) :=
    fun padded point =>
      ⟨if padded.card < k then insert point padded else padded, 1⟩
  have hpadding (initial : Finset V) :
      (costed_list_fold (Finset.univ.toList : List V)
        initial paddingStep).steps ≤ 2 * n := by
    have hfold := costed_list_fold_steps_le (A := Finset V) (B := V)
      (Finset.univ.toList : List V) initial paddingStep 1 (by
        intro state item
        exact le_rfl)
    simpa [n, Nat.mul_comm] using hfold
  have hruntime :
      (algorithm_one.run points k q alpha predictor).steps ≤
        k * (innerBound + 1) + 2 * n + 1 := by
    change (costed_then selected (fun centers =>
      costed_list_fold (Finset.univ.toList : List V)
        centers paddingStep)).steps ≤ _
    simp only [costed_then]
    exact Nat.add_le_add_right
      (Nat.add_le_add hselected (hpadding selected.output)) 1
  let s := n + k + 1
  have hn : n ≤ s := by omega
  have hk : k ≤ s := by omega
  have hspos : 1 ≤ s := by omega
  have hsquare : s ≤ s ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul_left s hspos
  have hn_square : n ≤ s ^ 2 := le_trans hn hsquare
  have hone_square : 1 ≤ s ^ 2 := le_trans hspos hsquare
  have hn_sq : n ^ 2 ≤ s ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hn hn
  have hbase : 2 * n ^ 2 + 2 * n + 2 ≤ 6 * s ^ 2 := by
    omega
  have hinner : innerBound ≤ 6 * s ^ 3 := by
    calc
      innerBound = n * (2 * n ^ 2 + 2 * n + 2) := rfl
      _ ≤ n * (6 * s ^ 2) := Nat.mul_le_mul_left n hbase
      _ ≤ s * (6 * s ^ 2) := Nat.mul_le_mul_right (6 * s ^ 2) hn
      _ = 6 * s ^ 3 := by ring
  have hone_cube : 1 ≤ s ^ 3 := by
    exact Nat.one_le_pow 3 s hspos
  have hinner_plus : innerBound + 1 ≤ 7 * s ^ 3 := by
    omega
  have hselected_poly :
      k * (innerBound + 1) ≤ 7 * s ^ 4 := by
    calc
      _ ≤ k * (7 * s ^ 3) := Nat.mul_le_mul_left k hinner_plus
      _ ≤ s * (7 * s ^ 3) := Nat.mul_le_mul_right (7 * s ^ 3) hk
      _ = 7 * s ^ 4 := by ring
  have hpadding_poly : 2 * n + 1 ≤ s ^ 4 := by
    have hns : n + 1 ≤ s := by omega
    have hpad_sq : 2 * n + 1 ≤ (n + 1) ^ 2 := by
      have hexpand : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
      rw [hexpand]
      omega
    have hsq_mono : (n + 1) ^ 2 ≤ s ^ 2 :=
      Nat.pow_le_pow_left hns 2
    have hfourth : s ^ 2 ≤ s ^ 4 := by
      calc
        s ^ 2 ≤ (s ^ 2) ^ 2 := Nat.pow_le_pow_left hsquare 2
        _ = s ^ 4 := by ring
    exact le_trans hpad_sq (le_trans hsq_mono hfourth)
  calc
    (algorithm_one.run points k q alpha predictor).steps ≤
        k * (innerBound + 1) + 2 * n + 1 := hruntime
    _ ≤ 8 * s ^ 4 := by omega
    _ = 8 * (Fintype.card V + k + 1) ^ 4 := by rfl

@[blueprint "thm:learning-augmented-k-clustering-approximation"
  (statement := /-- There is an approximation-error family $\varepsilon_q$, depending only on $q$, such that, uniformly over every finite general metric space, every finite point set $X$, and every feasible $k$, the following holds.  For $q\in\{1,2\}$, $0<\alpha<1/2$, and a predictor with label error rate $0\leq\lambda\leq\alpha$ relative to the nearest-center classes of a $(1+\alpha)$-approximately optimal reference clustering, with arbitrary assignments when several reference centers are tied, the fixed procedure \cref{def:algorithm-one} runs in polynomial time and outputs exactly $k$ centers whose cost is a
  \[
    1+O(\alpha^{1/q})
  \]
  multiple of the optimal $k$-clustering cost. -/)
  (proof := /-- The uniformly quantified approximation family, the cardinality assertion, and the cost estimate are supplied by \cref{lem:algorithm-one-global-approximation}.  The step count of the same operational computation is polynomially bounded by \cref{lem:algorithm-one-polynomial-runtime}.  Conjoining these two conclusions proves the theorem. -/)
  (title := /-- Learning-augmented metric $k$-clustering approximation -/)
  (latexEnv := "theorem")]
theorem learning_augmented_k_clustering_approximation :
    algorithm_runs_in_polynomial_time algorithm_one ∧
      ∃ approximationError : ℕ → ℝ → ℝ,
        (∀ q : ℕ, q = 1 ∨ q = 2 →
          Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioo 0 ((1 : ℝ) / 2)))
            (approximationError q)
            (fun alpha : ℝ => Real.rpow alpha ((q : ℝ)⁻¹))) ∧
        ∀ {V : Type} [MetricSpace V] [Fintype V] [DecidableEq V]
          (points : Finset V) (k q : ℕ),
          0 < k → k ≤ Fintype.card V → q = 1 ∨ q = 2 →
          ∀ (alpha lambda : ℝ) (predictor referenceLabel : V → Fin k)
            (referenceCenter : Fin k → V),
            0 < alpha → alpha < (1 : ℝ) / 2 →
            predictor_label_error points k q alpha lambda predictor referenceLabel
              referenceCenter →
            (algorithm_one.run points k q alpha predictor).output.card = k ∧
            clustering_cost q points
                (algorithm_one.run points k q alpha predictor).output ≤
              (1 + approximationError q alpha) *
                optimal_clustering_cost q k points := by
  exact ⟨algorithm_one_polynomial_runtime, algorithm_one_global_approximation⟩

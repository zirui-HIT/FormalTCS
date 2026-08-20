import Architect
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:online-learner"
  (statement := /-- An online learner is a deterministic rule which, given a finite history of query--response pairs and a new query point, returns a real-valued prediction. -/)
  (title := /-- Online learners -/)
  (latexEnv := "definition")]
def online_learner := List (ℝ × ℝ) → ℝ → ℝ

@[blueprint "def:online-loss-from"
  (statement := /-- For a real exponent $p$, a learner $A$, a target function $f$, an observed history, and a finite list of future queries, define the cumulative online loss by adding the $p$-th power of the absolute prediction error at each trial and then revealing the corresponding value of $f$ to the learner. -/)
  (title := /-- Cumulative loss from a history -/)
  (latexEnv := "definition")]
noncomputable def online_loss_from (p : ℝ) (A : online_learner) (f : ℝ → ℝ) :
    List (ℝ × ℝ) → List ℝ → ENNReal
  | _, [] => 0
  | history, x :: xs =>
      ENNReal.ofReal (|A history x - f x| ^ p) +
        online_loss_from p A f (history ++ [(x, f x)]) xs

@[blueprint "def:online-loss"
  (statement := /-- For a real exponent $p$, a learner $A$, a target function $f$, and a finite query sequence, the first queried value is revealed to initialize the learner without incurring loss. The online loss is the cumulative prediction loss on the remaining queries, starting from the one-point observed history. The empty query sequence also has zero loss. -/)
  (title := /-- Online cumulative prediction loss -/)
  (latexEnv := "definition")]
noncomputable def online_loss (p : ℝ) (A : online_learner) (f : ℝ → ℝ)
    (queries : List ℝ) : ENNReal :=
  match queries with
  | [] => 0
  | x :: xs => online_loss_from p A f [(x, f x)] xs

@[blueprint "def:worst-case-loss"
  (statement := /-- Given an exponent $p$, a learner $A$, and a class $\mathcal F$ of real functions, the worst-case loss is the supremum of the cumulative losses over all $f\in\mathcal F$ and all finite query sequences every term of which belongs to $[0,1]$. -/)
  (title := /-- Worst-case loss of a learner -/)
  (latexEnv := "definition")]
noncomputable def worst_case_loss (p : ℝ) (A : online_learner)
    (F : Set (ℝ → ℝ)) : ENNReal :=
  ⨆ f : {f : ℝ → ℝ // f ∈ F},
    ⨆ queries : {queries : List ℝ // ∀ x ∈ queries, x ∈ Set.Icc (0 : ℝ) 1},
      online_loss p A f.1 queries.1

@[blueprint "def:optimal-loss"
  (statement := /-- Given an exponent $p$ and a function class $\mathcal F$, the optimal worst-case loss $\operatorname{opt}_p(\mathcal F)$ is the infimum, over all online learners, of their worst-case cumulative $p$-power loss. -/)
  (title := /-- Optimal worst-case online loss -/)
  (latexEnv := "definition")]
noncomputable def optimal_loss (p : ℝ) (F : Set (ℝ → ℝ)) : ENNReal :=
  ⨅ A : online_learner, worst_case_loss p A F

@[blueprint "def:smooth-function-class"
  (statement := /-- For $q\in\mathbb R$, let $\mathcal F_q$ be the class of functions $f:\mathbb R\to\mathbb R$ which are absolutely continuous on $[0,1]$, for which $x\mapsto |f'(x)|^q$ is integrable on that interval, and which satisfy $\int_0^1 |f'(x)|^q\,dx\leq 1$. Only the restriction of such a function to $[0,1]$ is queried in the learning problem. -/)
  (title := /-- The smoothness class $\mathcal F_q$ -/)
  (latexEnv := "definition")]
def smooth_function_class (q : ℝ) : Set (ℝ → ℝ) :=
  {f | AbsolutelyContinuousOnInterval f 0 1 ∧
    IntervalIntegrable (fun x => |deriv f x| ^ q) MeasureTheory.volume 0 1 ∧
    (∫ x in (0 : ℝ)..1, |deriv f x| ^ q) ≤ 1}

@[blueprint "def:positive-parameter-filter"
  (statement := /-- The filter of positive parameters tending to zero is the neighborhood filter of $0$ restricted to the interval $(0,1)$. -/)
  (title := /-- Positive parameters tending to zero -/)
  (latexEnv := "definition")]
def positive_parameter_filter : Filter ℝ :=
  nhdsWithin 0 (Set.Ioo 0 1)

@[blueprint "def:positive-parameter-pair-filter"
  (statement := /-- Let $m(\delta,\epsilon)=\min(\delta,\epsilon)$. The two-parameter limiting filter is the pullback under $m$ of the filter of positive parameters tending to zero, restricted to $(0,1)\times(0,1)$. Thus a property holds eventually precisely when it holds uniformly for positive pairs whose minimum is sufficiently small; either coordinate may remain bounded away from zero. -/)
  (title := /-- Positive parameter pairs with minimum tending to zero -/)
  (latexEnv := "definition")]
def positive_parameter_pair_filter : Filter (ℝ × ℝ) :=
  Filter.comap (fun z : ℝ × ℝ => min z.1 z.2) positive_parameter_filter ⊓
    Filter.principal (Set.prod (Set.Ioo 0 1) (Set.Ioo 0 1))

@[blueprint "def:ennreal-is-big-o-upper"
  (statement := /-- Let $l$ be a filter and let $f,g$ take values in $[0,\infty]$. We write that $f$ has upper order $O_l(g)$ if there is a finite nonnegative constant $C$ such that $f(x)\leq Cg(x)$ eventually along $l$. -/)
  (title := /-- Upper big-O for extended nonnegative functions -/)
  (latexEnv := "definition")]
def ennreal_is_big_o_upper {α : Type*} (l : Filter α)
    (f g : α → ENNReal) : Prop :=
  ∃ C : NNReal, ∀ᶠ x in l, f x ≤ (C : ENNReal) * g x

@[blueprint "def:inverse-parameter-scale"
  (statement := /-- For a real parameter $x$, its inverse scale is the extended nonnegative number obtained from $x^{-1}$. On positive parameters this is exactly $1/x$. -/)
  (title := /-- Inverse parameter scale -/)
  (latexEnv := "definition")]
noncomputable def inverse_parameter_scale (x : ℝ) : ENNReal :=
  ENNReal.ofReal x⁻¹

@[blueprint "def:twopointtwo-nearest-learner"
  (statement := /-- Given a finite nonempty history and a new query $x$, predict the observed value at a history point having minimum distance from $x$; on the empty history, predict $0$. -/)
  (title := /-- The nearest-neighbor learner -/)
  (latexEnv := "definition")]
noncomputable def twopointtwo_nearest_learner : online_learner :=
  fun history x =>
    match history.argmin (fun z : ℝ × ℝ => |x - z.1|) with
    | some z => z.2
    | none => 0

@[blueprint "def:twopointtwo-nearest-edges-from"
  (statement := /-- Starting from an observed history and a list of future queries, record for every query the ordered pair consisting of a nearest previously observed query and the new query, updating the history with the target value after each step. -/)
  (title := /-- Nearest-neighbor insertion edges -/)
  (latexEnv := "definition")]
noncomputable def twopointtwo_nearest_edges_from (f : ℝ → ℝ) :
    List (ℝ × ℝ) → List ℝ → List (ℝ × ℝ)
  | _, [] => []
  | history, x :: xs =>
      match history.argmin (fun z : ℝ × ℝ => |x - z.1|) with
      | some z => (z.1, x) ::
          twopointtwo_nearest_edges_from f (history ++ [(x, f x)]) xs
      | none => twopointtwo_nearest_edges_from f (history ++ [(x, f x)]) xs

@[blueprint "lem:twopointtwo-loss-as-edge-sum"
  (statement := /-- If every response in a nonempty history is the value of a target function $f$ at the corresponding query, then the future loss of the nearest-neighbor learner is the sum, over its insertion edges, of the powered endpoint differences of $f$. -/)
  (proof := /-- Induct on the future query list using \cref{def:online-loss-from,def:twopointtwo-nearest-learner,def:twopointtwo-nearest-edges-from}. Nonemptiness ensures that the argument minimum always returns a history element. Its response equals the corresponding value of $f$ by consistency of the history, and appending the newly revealed pair preserves consistency for the induction hypothesis. -/)
  (title := /-- Nearest-neighbor loss as an insertion-edge sum -/)
  (latexEnv := "lemma")]
lemma twopointtwo_loss_as_edge_sum (p : ℝ) (f : ℝ → ℝ)
    (history : List (ℝ × ℝ)) (xs : List ℝ) (hne : history ≠ [])
    (hconsistent : ∀ z ∈ history, z.2 = f z.1) :
    online_loss_from p twopointtwo_nearest_learner f history xs =
      ((twopointtwo_nearest_edges_from f history xs).map
        (fun e => ENNReal.ofReal (|f e.1 - f e.2| ^ p))).sum := by
  induction xs generalizing history with
  | nil => simp [online_loss_from, twopointtwo_nearest_edges_from]
  | cons x xs ih =>
      cases harg : history.argmin (fun z : ℝ × ℝ => |x - z.1|) with
      | none => exact (hne (List.argmin_eq_none.mp harg)).elim
      | some z =>
          have hzarg : z ∈ history.argmin (fun w : ℝ × ℝ => |x - w.1|) := by
            simp [harg]
          have hzmem : z ∈ history := List.argmin_mem hzarg
          have hzval : z.2 = f z.1 := hconsistent z hzmem
          have hne' : history ++ [(x, f x)] ≠ [] := by simp
          have hconsistent' : ∀ w ∈ history ++ [(x, f x)], w.2 = f w.1 := by
            intro w hw
            simp only [List.mem_append, List.mem_singleton] at hw
            rcases hw with hw | rfl
            · exact hconsistent w hw
            · rfl
          simp [online_loss_from, twopointtwo_nearest_learner,
            twopointtwo_nearest_edges_from, harg, hzval,
            ih (history := history ++ [(x, f x)]) hne' hconsistent']

@[blueprint "lem:twopointtwo-edges-nearest-initial"
  (statement := /-- Every insertion edge produced from a history is no longer than the distance from its new endpoint to any query point in that initial history. -/)
  (proof := /-- Induct on the future query list in \cref{def:twopointtwo-nearest-edges-from}. For the first edge this is the defining minimality property of the list argument minimum. For every later edge, apply the induction hypothesis after appending the first new observation; every query in the original history remains in the enlarged history. -/)
  (title := /-- Initial-point comparison for insertion edges -/)
  (latexEnv := "lemma")]
lemma twopointtwo_edges_nearest_initial (f : ℝ → ℝ)
    (history : List (ℝ × ℝ)) (xs : List ℝ) :
    ∀ e ∈ twopointtwo_nearest_edges_from f history xs,
      ∀ b ∈ history, |e.2 - e.1| ≤ |e.2 - b.1| := by
  induction xs generalizing history with
  | nil => simp [twopointtwo_nearest_edges_from]
  | cons x xs ih =>
      cases harg : history.argmin (fun z : ℝ × ℝ => |x - z.1|) with
      | none =>
          have hempty : history = [] := List.argmin_eq_none.mp harg
          subst history
          simp [twopointtwo_nearest_edges_from]
      | some z =>
          intro e he b hb
          simp only [twopointtwo_nearest_edges_from, harg, List.mem_cons] at he
          rcases he with rfl | he
          · have hzarg : z ∈ history.argmin
                (fun w : ℝ × ℝ => |x - w.1|) := by simp [harg]
            simpa [abs_sub_comm] using List.le_of_mem_argmin hb hzarg
          · exact ih (history := history ++ [(x, f x)]) e he b
              (List.mem_append_left _ hb)

@[blueprint "lem:twopointtwo-left-crossing-edges-halve"
  (statement := /-- Fix $t\in\mathbb R$. Among the nearest-neighbor insertion edges directed from left to right whose half-open interval contains $t$, every later edge has length at most half the preceding edge's length. -/)
  (proof := /-- Induct on the query list. Suppose an initial edge $(a,x)$ and a later edge $(c,d)$ both satisfy $a<t\le x$ and $c<t\le d$. By \cref{lem:twopointtwo-edges-nearest-initial}, the later length is at most both $|d-a|$ and $|d-x|$. The latter comparison forces $d\le x$, since otherwise $c<t\le x<d$ gives the reverse strict inequality. Consequently the two comparisons read $d-c\le d-a$ and $d-c\le x-d$; adding them gives $2(d-c)\le x-a$. The induction hypothesis handles all pairs of later edges. -/)
  (title := /-- Halving of left-to-right crossing edges -/)
  (latexEnv := "lemma")]
lemma twopointtwo_left_crossing_edges_halve (f : ℝ → ℝ)
    (history : List (ℝ × ℝ)) (xs : List ℝ) (t : ℝ) :
    (((twopointtwo_nearest_edges_from f history xs).filter
        (fun e => e.1 < t ∧ t ≤ e.2)).map
      (fun e => |e.2 - e.1|)).Pairwise (fun u v => 2 * v ≤ u) := by
  induction xs generalizing history with
  | nil => simp [twopointtwo_nearest_edges_from]
  | cons x xs ih =>
      cases harg : history.argmin (fun z : ℝ × ℝ => |x - z.1|) with
      | none =>
          simpa [twopointtwo_nearest_edges_from, harg] using
            ih (history := history ++ [(x, f x)])
      | some z =>
          by_cases hcross : z.1 < t ∧ t ≤ x
          · simp only [twopointtwo_nearest_edges_from, harg]
            simp only [List.filter_cons]
            rw [if_pos (by simpa using hcross)]
            simp only [List.map_cons, List.pairwise_cons]
            constructor
            · intro v hv
              rcases List.mem_map.mp hv with ⟨e, he, rfl⟩
              have he' := List.mem_filter.mp he
              have hnear := twopointtwo_edges_nearest_initial f
                (history ++ [(x, f x)]) xs e he'.1
              have hecross : e.1 < t ∧ t ≤ e.2 := of_decide_eq_true he'.2
              have hzarg : z ∈ history.argmin
                  (fun w : ℝ × ℝ => |x - w.1|) := by simp [harg]
              have hzmem : z ∈ history ++ [(x, f x)] :=
                List.mem_append_left _ (List.argmin_mem hzarg)
              have hxmem : (x, f x) ∈ history ++ [(x, f x)] := by simp
              have hz := hnear z hzmem
              have hx' := hnear (x, f x) hxmem
              simp only [Prod.fst] at hx'
              have hedle : e.2 ≤ x := by
                by_contra hnot
                have hxd : x < e.2 := lt_of_not_ge hnot
                rw [abs_of_nonneg (by linarith [hecross.1, hecross.2]),
                  abs_of_nonneg (by linarith)] at hx'
                linarith [hecross.1, hecross.2]
              rw [abs_of_nonneg (by linarith [hecross.1, hecross.2]),
                abs_of_nonneg (by linarith [hcross.1, hecross.2])] at hz
              rw [abs_of_nonneg (by linarith [hecross.1, hecross.2]),
                abs_of_nonpos (by linarith)] at hx'
              rw [abs_of_nonneg (by linarith [hecross.1, hecross.2]),
                abs_of_nonneg (by linarith [hcross.1, hcross.2])]
              linarith
            · exact ih (history := history ++ [(x, f x)])
          · simpa [twopointtwo_nearest_edges_from, harg, hcross] using
              ih (history := history ++ [(x, f x)])

@[blueprint "lem:twopointtwo-right-crossing-edges-halve"
  (statement := /-- Fix $t\in\mathbb R$. Among the nearest-neighbor insertion edges directed from right to left whose half-open interval contains $t$, every later edge has length at most half the preceding edge's length. -/)
  (proof := /-- Induct on the query list. If $(a,x)$ is the initial crossing edge and $(c,d)$ is a later one, \cref{lem:twopointtwo-edges-nearest-initial} compares the later length with the distances from $d$ to both $a$ and $x$. These comparisons force $x\le d$ and, after adding them, give $2(c-d)\le a-x$. Apply the induction hypothesis to the remaining edges. -/)
  (title := /-- Halving of right-to-left crossing edges -/)
  (latexEnv := "lemma")]
lemma twopointtwo_right_crossing_edges_halve (f : ℝ → ℝ)
    (history : List (ℝ × ℝ)) (xs : List ℝ) (t : ℝ) :
    (((twopointtwo_nearest_edges_from f history xs).filter
        (fun e => e.2 < t ∧ t ≤ e.1)).map
      (fun e => |e.2 - e.1|)).Pairwise (fun u v => 2 * v ≤ u) := by
  induction xs generalizing history with
  | nil => simp [twopointtwo_nearest_edges_from]
  | cons x xs ih =>
      cases harg : history.argmin (fun z : ℝ × ℝ => |x - z.1|) with
      | none =>
          simpa [twopointtwo_nearest_edges_from, harg] using
            ih (history := history ++ [(x, f x)])
      | some z =>
          by_cases hcross : x < t ∧ t ≤ z.1
          · simp only [twopointtwo_nearest_edges_from, harg]
            simp only [List.filter_cons]
            rw [if_pos (by simpa using hcross)]
            simp only [List.map_cons, List.pairwise_cons]
            constructor
            · intro v hv
              rcases List.mem_map.mp hv with ⟨e, he, rfl⟩
              have he' := List.mem_filter.mp he
              have hnear := twopointtwo_edges_nearest_initial f
                (history ++ [(x, f x)]) xs e he'.1
              have hecross : e.2 < t ∧ t ≤ e.1 := of_decide_eq_true he'.2
              have hzarg : z ∈ history.argmin
                  (fun w : ℝ × ℝ => |x - w.1|) := by simp [harg]
              have hzmem : z ∈ history ++ [(x, f x)] :=
                List.mem_append_left _ (List.argmin_mem hzarg)
              have hxmem : (x, f x) ∈ history ++ [(x, f x)] := by simp
              have hz := hnear z hzmem
              have hx' := hnear (x, f x) hxmem
              simp only [Prod.fst] at hx'
              have hxle : x ≤ e.2 := by
                by_contra hnot
                have hdx : e.2 < x := lt_of_not_ge hnot
                rw [abs_of_nonpos (by linarith [hecross.1, hecross.2]),
                  abs_of_nonpos (by linarith)] at hx'
                linarith [hecross.1, hecross.2]
              rw [abs_of_nonpos (by linarith [hecross.1, hecross.2]),
                abs_of_nonpos (by linarith [hcross.2, hecross.1])] at hz
              rw [abs_of_nonpos (by linarith [hecross.1, hecross.2]),
                abs_of_nonneg (by linarith)] at hx'
              rw [abs_of_nonpos (by linarith [hecross.1, hecross.2]),
                abs_of_nonpos (by linarith [hcross.1, hcross.2])]
              linarith
            · exact ih (history := history ++ [(x, f x)])
          · simpa [twopointtwo_nearest_edges_from, harg, hcross] using
              ih (history := history ++ [(x, f x)])

@[blueprint "lem:twopointtwo-halving-rpow-sum"
  (statement := /-- Let $\eta>0$ and $B\ge0$. If a finite list of nonnegative reals starts below $B$ and every entry after another is at most half of it, then the sum of their $\eta$-powers is at most $B^\eta/(1-2^{-\eta})$. -/)
  (proof := /-- Induct on the list. For a head $a$, pairwise halving bounds every tail entry by $a/2$, so the induction hypothesis bounds the tail sum by $(a/2)^\eta/(1-2^{-\eta})$. Since $(a/2)^\eta=a^\eta2^{-\eta}$, adding the head gives exactly $a^\eta/(1-2^{-\eta})$. Monotonicity of the positive power and $a\le B$ gives the stated bound. -/)
  (title := /-- Geometric bound for a halving list -/)
  (latexEnv := "lemma")]
lemma twopointtwo_halving_rpow_sum (η B : ℝ) (hη : 0 < η) (hB : 0 ≤ B)
    (l : List ℝ) (hnonneg : ∀ u ∈ l, 0 ≤ u) (hbound : ∀ u ∈ l, u ≤ B)
    (hpair : l.Pairwise (fun u v => 2 * v ≤ u)) :
    (l.map (fun u => u ^ η)).sum ≤ B ^ η / (1 - (1 / 2 : ℝ) ^ η) := by
  induction l generalizing B with
  | nil =>
      have hr : 0 < 1 - (1 / 2 : ℝ) ^ η := by
        have : (1 / 2 : ℝ) ^ η < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hη
        linarith
      simp only [List.map_nil, List.sum_nil]
      exact div_nonneg (Real.rpow_nonneg hB _) hr.le
  | cons a l ih =>
      have ha : 0 ≤ a := hnonneg a (by simp)
      have haB : a ≤ B := hbound a (by simp)
      have htail_nonneg : ∀ u ∈ l, 0 ≤ u := by
        intro u hu
        exact hnonneg u (by simp [hu])
      have hpair' := (List.pairwise_cons.mp hpair)
      have htail_bound : ∀ u ∈ l, u ≤ a / 2 := by
        intro u hu
        have := hpair'.1 u hu
        linarith
      have htail := ih (B := a / 2) (by positivity) htail_nonneg htail_bound hpair'.2
      have hr : 0 < 1 - (1 / 2 : ℝ) ^ η := by
        have : (1 / 2 : ℝ) ^ η < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hη
        linarith
      have hsplit : (a / 2) ^ η = a ^ η * (1 / 2 : ℝ) ^ η := by
        rw [show a / 2 = a * (1 / 2 : ℝ) by ring,
          Real.mul_rpow ha (by norm_num)]
      have ha_sum : a ^ η + (a / 2) ^ η / (1 - (1 / 2 : ℝ) ^ η) =
          a ^ η / (1 - (1 / 2 : ℝ) ^ η) := by
        rw [hsplit]
        field_simp [ne_of_gt hr]
        ring
      have hpow : a ^ η ≤ B ^ η := Real.rpow_le_rpow ha haB hη.le
      simp only [List.map_cons, List.sum_cons]
      calc
        a ^ η + (l.map fun u => u ^ η).sum ≤
            a ^ η + (a / 2) ^ η / (1 - (1 / 2 : ℝ) ^ η) := add_le_add_right htail _
        _ = a ^ η / (1 - (1 / 2 : ℝ) ^ η) := ha_sum
        _ ≤ B ^ η / (1 - (1 / 2 : ℝ) ^ η) := div_le_div_of_nonneg_right hpow hr.le

@[blueprint "lem:twopointtwo-edge-endpoints-in-unit-interval"
  (statement := /-- If every query in the initial history and every future query lies in $[0,1]$, then both endpoints of every nearest-neighbor insertion edge lie in $[0,1]$. -/)
  (proof := /-- Induct on the future queries using \cref{def:twopointtwo-nearest-edges-from}. An argument-minimum endpoint belongs to the current history, and the new endpoint is the current query. Appending that query preserves the unit-interval property required by the induction hypothesis. -/)
  (title := /-- Unit-interval location of insertion edges -/)
  (latexEnv := "lemma")]
lemma twopointtwo_edge_endpoints_in_unit_interval (f : ℝ → ℝ)
    (history : List (ℝ × ℝ)) (xs : List ℝ)
    (hhistory : ∀ z ∈ history, z.1 ∈ Set.Icc (0 : ℝ) 1)
    (hxs : ∀ x ∈ xs, x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ e ∈ twopointtwo_nearest_edges_from f history xs,
      e.1 ∈ Set.Icc (0 : ℝ) 1 ∧ e.2 ∈ Set.Icc (0 : ℝ) 1 := by
  induction xs generalizing history with
  | nil => simp [twopointtwo_nearest_edges_from]
  | cons x xs ih =>
      have hx : x ∈ Set.Icc (0 : ℝ) 1 := hxs x (by simp)
      have hxs' : ∀ y ∈ xs, y ∈ Set.Icc (0 : ℝ) 1 := by
        intro y hy
        exact hxs y (by simp [hy])
      have hhistory' : ∀ z ∈ history ++ [(x, f x)],
          z.1 ∈ Set.Icc (0 : ℝ) 1 := by
        intro z hz
        simp only [List.mem_append, List.mem_singleton] at hz
        rcases hz with hz | rfl
        · exact hhistory z hz
        · exact hx
      cases harg : history.argmin (fun z : ℝ × ℝ => |x - z.1|) with
      | none =>
          simpa [twopointtwo_nearest_edges_from, harg] using
            ih (history := history ++ [(x, f x)]) hhistory' hxs'
      | some z =>
          intro e he
          simp only [twopointtwo_nearest_edges_from, harg, List.mem_cons] at he
          rcases he with rfl | he
          · have hzarg : z ∈ history.argmin
                (fun w : ℝ × ℝ => |x - w.1|) := by simp [harg]
            exact ⟨hhistory z (List.argmin_mem hzarg), hx⟩
          · exact ih (history := history ++ [(x, f x)]) hhistory' hxs' e he

@[blueprint "lem:twopointtwo-crossing-weight-bound"
  (statement := /-- Let $0<\eta<1$, and suppose the initial and future queries lie in $[0,1]$. At every $t\in\mathbb R$, the sum of $|b-a|^\eta$ over nearest-neighbor insertion edges $(a,b)$ whose half-open unoriented intervals contain $t$ is at most $4/\eta$. -/)
  (proof := /-- Split the crossing edges into their left-to-right and right-to-left sublists. By \cref{lem:twopointtwo-left-crossing-edges-halve,lem:twopointtwo-right-crossing-edges-halve}, each sublist of lengths is pairwise halving. The endpoint bound in \cref{lem:twopointtwo-edge-endpoints-in-unit-interval} makes every length at most $1$, so \cref{lem:twopointtwo-halving-rpow-sum} bounds each directional sum by $(1-2^{-\eta})^{-1}$. Convexity of $s\mapsto2^{-s}$ on $[0,1]$ gives $2^{-\eta}\le1-\eta/2$, hence each directional sum is at most $2/\eta$. Adding the two directions proves the claim. -/)
  (title := /-- Pointwise crossing-weight bound -/)
  (latexEnv := "lemma")]
lemma twopointtwo_crossing_weight_bound (η : ℝ) (hη : η ∈ Set.Ioo (0 : ℝ) 1)
    (f : ℝ → ℝ) (history : List (ℝ × ℝ)) (xs : List ℝ)
    (hhistory : ∀ z ∈ history, z.1 ∈ Set.Icc (0 : ℝ) 1)
    (hxs : ∀ x ∈ xs, x ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    ((twopointtwo_nearest_edges_from f history xs).map (fun e =>
      if (e.1 < t ∧ t ≤ e.2) ∨ (e.2 < t ∧ t ≤ e.1) then
        |e.2 - e.1| ^ η else 0)).sum ≤ 4 / η := by
  classical
  let edges := twopointtwo_nearest_edges_from f history xs
  let left := (edges.filter (fun e => e.1 < t ∧ t ≤ e.2)).map
    (fun e => |e.2 - e.1|)
  let right := (edges.filter (fun e => e.2 < t ∧ t ≤ e.1)).map
    (fun e => |e.2 - e.1|)
  have hedge := twopointtwo_edge_endpoints_in_unit_interval f history xs hhistory hxs
  have hlength (e : ℝ × ℝ) (he : e ∈ edges) : |e.2 - e.1| ≤ 1 := by
    have heI := hedge e he
    rw [abs_le]
    constructor <;> linarith [heI.1.1, heI.1.2, heI.2.1, heI.2.2]
  have hleft_nonneg : ∀ u ∈ left, 0 ≤ u := by
    intro u hu
    rcases List.mem_map.mp hu with ⟨e, he, rfl⟩
    positivity
  have hleft_bound : ∀ u ∈ left, u ≤ 1 := by
    intro u hu
    rcases List.mem_map.mp hu with ⟨e, he, rfl⟩
    exact hlength e (List.mem_of_mem_filter he)
  have hright_nonneg : ∀ u ∈ right, 0 ≤ u := by
    intro u hu
    rcases List.mem_map.mp hu with ⟨e, he, rfl⟩
    positivity
  have hright_bound : ∀ u ∈ right, u ≤ 1 := by
    intro u hu
    rcases List.mem_map.mp hu with ⟨e, he, rfl⟩
    exact hlength e (List.mem_of_mem_filter he)
  have hleft_pair : left.Pairwise (fun u v => 2 * v ≤ u) := by
    exact twopointtwo_left_crossing_edges_halve f history xs t
  have hright_pair : right.Pairwise (fun u v => 2 * v ≤ u) := by
    exact twopointtwo_right_crossing_edges_halve f history xs t
  have hleft := twopointtwo_halving_rpow_sum η 1 hη.1 (by norm_num)
    left hleft_nonneg hleft_bound hleft_pair
  have hright := twopointtwo_halving_rpow_sum η 1 hη.1 (by norm_num)
    right hright_nonneg hright_bound hright_pair
  have hrpow_le : (1 / 2 : ℝ) ^ η ≤ 1 - η / 2 := by
    have hc := (convexOn_rpow_left (show 0 < (1 / 2 : ℝ) by norm_num)).2
      (Set.mem_univ 0) (Set.mem_univ 1) (sub_nonneg.mpr hη.2.le) hη.1.le
      (by ring : (1 - η) + η = 1)
    norm_num at hc
    nlinarith
  have hden : η / 2 ≤ 1 - (1 / 2 : ℝ) ^ η := by linarith
  have hdenpos : 0 < 1 - (1 / 2 : ℝ) ^ η := lt_of_lt_of_le (half_pos hη.1) hden
  have hfrac : 1 / (1 - (1 / 2 : ℝ) ^ η) ≤ 2 / η := by
    rw [div_le_div_iff₀ hdenpos hη.1]
    nlinarith
  have hfrac' : 1 ^ η / (1 - (1 / 2 : ℝ) ^ η) ≤ 2 / η := by
    simpa using hfrac
  have hleft' : (left.map (fun u => u ^ η)).sum ≤ 2 / η := hleft.trans hfrac'
  have hright' : (right.map (fun u => u ^ η)).sum ≤ 2 / η := hright.trans hfrac'
  have hsplit : (edges.map (fun e =>
      if t ∈ Set.uIoc e.1 e.2 then |e.2 - e.1| ^ η else 0)).sum =
      (left.map (fun u => u ^ η)).sum + (right.map (fun u => u ^ η)).sum := by
    have split_for : ∀ es : List (ℝ × ℝ),
        (es.map (fun e => if t ∈ Set.uIoc e.1 e.2 then
          |e.2 - e.1| ^ η else 0)).sum =
        (((es.filter (fun e => e.1 < t ∧ t ≤ e.2)).map
          (fun e => |e.2 - e.1|)).map (fun u => u ^ η)).sum +
        (((es.filter (fun e => e.2 < t ∧ t ≤ e.1)).map
          (fun e => |e.2 - e.1|)).map (fun u => u ^ η)).sum := by
      intro es
      induction es with
      | nil => simp
      | cons e es ih =>
          by_cases hl : e.1 < t ∧ t ≤ e.2
          · have hr : ¬(e.2 < t ∧ t ≤ e.1) := by
              intro hr
              linarith [hl.1, hl.2, hr.1, hr.2]
            simp only [List.map_cons, List.sum_cons]
            rw [ih]
            simp [hl, hr, Set.mem_uIoc]
            ring
          · by_cases hr : e.2 < t ∧ t ≤ e.1
            · simp only [List.map_cons, List.sum_cons]
              rw [ih]
              simp [hl, hr, Set.mem_uIoc]
              ring
            · simp only [List.map_cons, List.sum_cons]
              rw [ih]
              simp [hl, hr, Set.mem_uIoc]
    simpa [left, right] using split_for edges
  have hmembership : (edges.map (fun e =>
      if t ∈ Set.uIoc e.1 e.2 then |e.2 - e.1| ^ η else 0)).sum ≤ 4 / η := by
    rw [hsplit]
    calc
      (left.map (fun u => u ^ η)).sum + (right.map (fun u => u ^ η)).sum ≤
          2 / η + 2 / η := add_le_add hleft' hright'
      _ = 4 / η := by ring
  simpa [edges, Set.mem_uIoc] using hmembership

@[blueprint "lem:twopointtwo-action-charge-bound"
  (statement := /-- Let $0<\eta<1$ and $f\in\mathcal F_{1+\eta}$. For unit-interval initial and future queries, the sum over nearest-neighbor insertion edges $(a,b)$ of $|b-a|^\eta$ times the local $(1+\eta)$-action of $f$ on the interval between $a$ and $b$ is at most $4/\eta$. -/)
  (proof := /-- By \cref{lem:twopointtwo-edge-endpoints-in-unit-interval}, every insertion interval lies in $[0,1]$. Write each local action as an integral of the global nonnegative action density multiplied by the indicator of its insertion interval, and interchange the finite sum and integral. At every point the sum of the coefficients of the indicators is at most $4/\eta$ by \cref{lem:twopointtwo-crossing-weight-bound}. Integrating this pointwise estimate and using the total action bound from \cref{def:smooth-function-class} proves the claim. -/)
  (title := /-- Summed local-action charge -/)
  (latexEnv := "lemma")]
lemma twopointtwo_action_charge_bound (η : ℝ) (hη : η ∈ Set.Ioo (0 : ℝ) 1)
    (f : ℝ → ℝ) (hf : f ∈ smooth_function_class (1 + η))
    (history : List (ℝ × ℝ)) (xs : List ℝ)
    (hhistory : ∀ z ∈ history, z.1 ∈ Set.Icc (0 : ℝ) 1)
    (hxs : ∀ x ∈ xs, x ∈ Set.Icc (0 : ℝ) 1) :
    ((twopointtwo_nearest_edges_from f history xs).map (fun e =>
      |e.2 - e.1| ^ η * ∫ t in Set.uIoc e.1 e.2,
        |deriv f t| ^ (1 + η))).sum ≤ 4 / η := by
  classical
  rcases hf with ⟨hfac, hfint, hfaction⟩
  let edges := twopointtwo_nearest_edges_from f history xs
  let g : ℝ → ℝ := fun t => |deriv f t| ^ (1 + η)
  have hg_nonneg (t : ℝ) : 0 ≤ g t := Real.rpow_nonneg (abs_nonneg _) _
  have hedge := twopointtwo_edge_endpoints_in_unit_interval f history xs hhistory hxs
  have hsub (e : ℝ × ℝ) (he : e ∈ edges) :
      Set.uIoc e.1 e.2 ⊆ Set.Ioc (0 : ℝ) 1 := by
    have heI := hedge e he
    rw [Set.uIoc]
    intro t ht
    exact ⟨(le_min heI.1.1 heI.2.1).trans_lt ht.1,
      ht.2.trans (max_le heI.1.2 heI.2.2)⟩
  have hterm_integrable (e : ℝ × ℝ) (he : e ∈ edges) :
      MeasureTheory.Integrable (fun t =>
        if t ∈ Set.uIoc e.1 e.2 then |e.2 - e.1| ^ η * g t else 0) := by
    have hlocal : MeasureTheory.IntegrableOn g (Set.uIoc e.1 e.2) :=
      hfint.1.mono_set (hsub e he)
    rw [show (fun t => if t ∈ Set.uIoc e.1 e.2 then
        |e.2 - e.1| ^ η * g t else 0) =
      Set.indicator (Set.uIoc e.1 e.2) (fun t => |e.2 - e.1| ^ η * g t) by
        funext t
        simp [Set.indicator]]
    rw [MeasureTheory.integrable_indicator_iff measurableSet_uIoc]
    exact hlocal.const_mul (|e.2 - e.1| ^ η)
  have hrewrite (e : ℝ × ℝ) (he : e ∈ edges) :
      |e.2 - e.1| ^ η * ∫ t in Set.uIoc e.1 e.2, g t =
        ∫ t, if t ∈ Set.uIoc e.1 e.2 then |e.2 - e.1| ^ η * g t else 0 := by
    rw [← MeasureTheory.integral_const_mul]
    rw [← MeasureTheory.integral_indicator measurableSet_uIoc]
    rfl
  have hlist_integrable : ∀ l : List (ℝ × ℝ), (∀ e ∈ l, e ∈ edges) →
      MeasureTheory.Integrable (fun t =>
        (l.map (fun e => if t ∈ Set.uIoc e.1 e.2 then
          |e.2 - e.1| ^ η * g t else 0)).sum) := by
    intro l
    induction l with
    | nil => simp
    | cons e es ih =>
        intro hl
        simp only [List.map_cons, List.sum_cons]
        exact (hterm_integrable e (hl e (by simp))).add
          (ih (fun a ha => hl a (by simp [ha])))
  have hsum_integral : (edges.map (fun e =>
      |e.2 - e.1| ^ η * ∫ t in Set.uIoc e.1 e.2, g t)).sum =
      ∫ t, (edges.map (fun e =>
        if t ∈ Set.uIoc e.1 e.2 then |e.2 - e.1| ^ η * g t else 0)).sum := by
    have go : ∀ l : List (ℝ × ℝ), (∀ e ∈ l, e ∈ edges) →
        (l.map (fun e => |e.2 - e.1| ^ η * ∫ t in Set.uIoc e.1 e.2, g t)).sum =
          ∫ t, (l.map (fun e => if t ∈ Set.uIoc e.1 e.2 then
            |e.2 - e.1| ^ η * g t else 0)).sum := by
      intro l hl
      induction l with
      | nil => simp
      | cons e es ih =>
          have he : e ∈ edges := hl e (by simp)
          have hes : ∀ a ∈ es, a ∈ edges := by
            intro a ha
            exact hl a (by simp [ha])
          have hesi := hlist_integrable es hes
          rw [List.map_cons, List.sum_cons, hrewrite e he, ih hes]
          rw [← MeasureTheory.integral_add (hterm_integrable e he) hesi]
          rfl
    exact go edges (fun e he => he)
  rw [hsum_integral]
  have hpoint (t : ℝ) :
      (edges.map (fun e =>
        if t ∈ Set.uIoc e.1 e.2 then |e.2 - e.1| ^ η * g t else 0)).sum ≤
        (4 / η) * g t := by
    have hw := twopointtwo_crossing_weight_bound η hη f history xs hhistory hxs t
    have heq : (edges.map (fun e => if t ∈ Set.uIoc e.1 e.2 then
        |e.2 - e.1| ^ η * g t else 0)).sum =
        (edges.map (fun e => if t ∈ Set.uIoc e.1 e.2 then
          |e.2 - e.1| ^ η else 0)).sum * g t := by
      induction edges with
      | nil => simp
      | cons e es ih =>
          by_cases he : t ∈ Set.uIoc e.1 e.2 <;> simp [he, ih, add_mul]
    rw [heq]
    apply mul_le_mul_of_nonneg_right _ (hg_nonneg t)
    simpa [Set.mem_uIoc] using hw
  have hsum_int : MeasureTheory.Integrable (fun t =>
      (edges.map (fun e =>
        if t ∈ Set.uIoc e.1 e.2 then |e.2 - e.1| ^ η * g t else 0)).sum) :=
    hlist_integrable edges (fun e he => he)
  have hglobal_int : MeasureTheory.IntegrableOn (fun t => (4 / η) * g t)
      (Set.Ioc (0 : ℝ) 1) := hfint.1.const_mul (4 / η)
  have hglobal_indicator : MeasureTheory.Integrable
      (Set.indicator (Set.Ioc (0 : ℝ) 1) (fun t => (4 / η) * g t)) :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Ioc).2 hglobal_int
  have houtside (t : ℝ) (ht : t ∉ Set.Ioc (0 : ℝ) 1) :
      (edges.map (fun e =>
        if t ∈ Set.uIoc e.1 e.2 then |e.2 - e.1| ^ η * g t else 0)).sum = 0 := by
    apply List.sum_eq_zero
    intro u hu
    rcases List.mem_map.mp hu with ⟨e, he, rfl⟩
    have hnot : t ∉ Set.uIoc e.1 e.2 := fun hit => ht (hsub e he hit)
    simp [hnot]
  calc
    ∫ t, (edges.map (fun e =>
        if t ∈ Set.uIoc e.1 e.2 then |e.2 - e.1| ^ η * g t else 0)).sum ≤
        ∫ t in Set.Ioc (0 : ℝ) 1, (4 / η) * g t := by
      rw [← MeasureTheory.integral_indicator (measurableSet_Ioc :
        MeasurableSet (Set.Ioc (0 : ℝ) 1))]
      apply MeasureTheory.integral_mono hsum_int hglobal_indicator
      intro t
      by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
      · simpa [Set.indicator, ht] using hpoint t
      · simp [Set.indicator, ht, houtside t ht]
    _ = (4 / η) * ∫ t in (0 : ℝ)..1, g t := by
      rw [MeasureTheory.integral_const_mul,
        intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    _ ≤ 4 / η := by
      have hfour : 0 ≤ 4 / η := div_nonneg (by norm_num) hη.1.le
      exact (mul_le_mul_of_nonneg_left hfaction hfour).trans_eq (mul_one _)

@[blueprint "lem:twopointtwo-local-holder"
  (statement := /-- Let $0<\eta<1$, let $f\in\mathcal F_{1+\eta}$, and let $x,y\in[0,1]$. Then the $(1+\eta)$-power of $|f(x)-f(y)|$ is at most $|x-y|^\eta$ times the $(1+\eta)$-action of $f$ on the unoriented interval between $x$ and $y$. -/)
  (proof := /-- By absolute continuity in \cref{def:smooth-function-class}, the fundamental theorem of calculus bounds $|f(x)-f(y)|$ by the integral of $|f'|$ over the interval between the points. Hölder's inequality on that interval, with conjugate exponents $1+\eta$ and $(1+\eta)/\eta$, bounds this integral by the product of the local $(1+\eta)$-action to the power $1/(1+\eta)$ and $|x-y|^{\eta/(1+\eta)}$. Raising this inequality to the power $1+\eta$ gives the claim. -/)
  (title := /-- Local Hölder estimate from the action bound -/)
  (latexEnv := "lemma")]
lemma twopointtwo_local_holder (η : ℝ) (hη : η ∈ Set.Ioo (0 : ℝ) 1)
    (f : ℝ → ℝ) (hf : f ∈ smooth_function_class (1 + η))
    (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |f x - f y| ^ (1 + η) ≤
      |x - y| ^ η * ∫ z in Set.uIoc x y, |deriv f z| ^ (1 + η) := by
  rcases hf with ⟨hfac, hfint, hfaction⟩
  have hq : 0 < 1 + η := by linarith [hη.1]
  have hsubset : Set.uIoc x y ⊆ Set.Ioc (0 : ℝ) 1 := by
    rw [Set.uIoc]
    intro z hz
    constructor
    · exact lt_of_le_of_lt (le_min hx.1 hy.1) hz.1
    · exact hz.2.trans (max_le hx.2 hy.2)
  have hpower : MeasureTheory.Integrable (fun z => |deriv f z| ^ (1 + η))
      (MeasureTheory.volume.restrict (Set.uIoc x y)) := by
    exact hfint.1.mono_set hsubset
  have hfacxy : AbsolutelyContinuousOnInterval f x y := hfac.mono (by
    intro z hz
    rw [Set.uIcc] at hz
    have hz' : z ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨(le_min hx.1 hy.1).trans hz.1, hz.2.trans (max_le hx.2 hy.2)⟩
    simpa [Set.uIcc] using hz')
  have hpq : (1 + η).HolderConjugate ((1 + η) / η) := by
    refine ⟨?_, hq, div_pos hq hη.1⟩
    field_simp [hq.ne', hη.1.ne']
  let μ : MeasureTheory.Measure ℝ :=
    MeasureTheory.volume.restrict (Set.uIoc x y)
  let g : ℝ → ℝ := fun z => |deriv f z|
  have hg_meas : MeasureTheory.AEStronglyMeasurable g μ := by
    have hroot : MeasureTheory.AEStronglyMeasurable
        (fun z => (|deriv f z| ^ (1 + η)) ^ (1 + η)⁻¹) μ :=
      (Real.continuous_rpow_const (inv_nonneg.mpr hq.le)).comp_aestronglyMeasurable
        hpower.aestronglyMeasurable
    convert hroot using 1
    funext z
    dsimp [g]
    rw [← Real.rpow_mul (abs_nonneg (deriv f z)), mul_inv_cancel₀ hq.ne']
    simp
  letI : MeasureTheory.IsFiniteMeasure μ := by
    rw [MeasureTheory.isFiniteMeasure_restrict]
    simp [μ]
  have hg_mem : MeasureTheory.MemLp g (ENNReal.ofReal (1 + η)) μ := by
    apply (MeasureTheory.integrable_norm_rpow_iff hg_meas (by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      exact hq) (by simp)).mp
    rw [ENNReal.toReal_ofReal hq.le]
    simpa [μ, g, Real.norm_eq_abs] using hpower
  have hone_mem : MeasureTheory.MemLp (fun _ : ℝ => (1 : ℝ))
      (ENNReal.ofReal ((1 + η) / η)) μ :=
    MeasureTheory.memLp_const 1
  have hftc : |f x - f y| ≤ ∫ z in Set.uIoc x y, |deriv f z| := by
    calc
      |f x - f y| = |f y - f x| := abs_sub_comm _ _
      _ = |∫ z in x..y, deriv f z| :=
        congrArg abs hfacxy.integral_deriv_eq_sub.symm
      _ ≤ ∫ z in Set.uIoc x y, |deriv f z| := by
        simpa [Real.norm_eq_abs] using
          (intervalIntegral.norm_integral_le_integral_norm_uIoc
            (f := fun z => deriv f z) (a := x) (b := y))
  have hholder := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) hpq hg_mem hone_mem
  have hvol : MeasureTheory.volume.real (Set.uIoc x y) = |x - y| := by
    rw [MeasureTheory.Measure.real_def, Real.volume_uIoc,
      ENNReal.toReal_ofReal (abs_nonneg _)]
    exact abs_sub_comm _ _
  have hone : (∫ a : ℝ, ‖(1 : ℝ)‖ ^ ((1 + η) / η) ∂μ) ^
      (1 / ((1 + η) / η)) = |x - y| ^ (η / (1 + η)) := by
    simp [μ, MeasureTheory.Measure.real_def, Real.volume_uIoc,
      ENNReal.toReal_ofReal, abs_sub_comm, hq.ne', hη.1.ne']
  rw [hone] at hholder
  have hroot : ∫ z in Set.uIoc x y, |deriv f z| ≤
      (∫ z in Set.uIoc x y, |deriv f z| ^ (1 + η)) ^ (1 / (1 + η)) *
        |x - y| ^ (η / (1 + η)) := by
    simpa [μ, g, Real.norm_eq_abs] using hholder
  have henergy_nonneg : 0 ≤ ∫ z in Set.uIoc x y, |deriv f z| ^ (1 + η) :=
    MeasureTheory.integral_nonneg fun z => Real.rpow_nonneg (abs_nonneg _) _
  have habs : |f x - f y| ≤
      (∫ z in Set.uIoc x y, |deriv f z| ^ (1 + η)) ^ (1 / (1 + η)) *
        |x - y| ^ (η / (1 + η)) := hftc.trans hroot
  have hrpow := Real.rpow_le_rpow (abs_nonneg (f x - f y)) habs hq.le
  rw [Real.mul_rpow (Real.rpow_nonneg henergy_nonneg _)
      (Real.rpow_nonneg (abs_nonneg (x - y)) _),
    ← Real.rpow_mul henergy_nonneg, ← Real.rpow_mul (abs_nonneg (x - y))] at hrpow
  have hq_ne : 1 + η ≠ 0 := hq.ne'
  simpa [div_eq_mul_inv, hq_ne, Real.rpow_one, mul_comm, mul_left_comm,
    mul_assoc] using hrpow

@[blueprint "lem:twopointtwo-edge-error-sum-bound"
  (statement := /-- Let $0<\eta<1$ and $f\in\mathcal F_{1+\eta}$. For unit-interval initial and future queries, the sum of the $(1+\eta)$-powers of the endpoint differences over all nearest-neighbor insertion edges is at most $4/\eta$. -/)
  (proof := /-- For each insertion edge, apply the local Hölder estimate \cref{lem:twopointtwo-local-holder}; its endpoints lie in $[0,1]$ by \cref{lem:twopointtwo-edge-endpoints-in-unit-interval}. Sum the resulting inequalities over the edge list, and apply the aggregate local-action estimate \cref{lem:twopointtwo-action-charge-bound}. -/)
  (title := /-- Powered endpoint-error bound -/)
  (latexEnv := "lemma")]
lemma twopointtwo_edge_error_sum_bound (η : ℝ) (hη : η ∈ Set.Ioo (0 : ℝ) 1)
    (f : ℝ → ℝ) (hf : f ∈ smooth_function_class (1 + η))
    (history : List (ℝ × ℝ)) (xs : List ℝ)
    (hhistory : ∀ z ∈ history, z.1 ∈ Set.Icc (0 : ℝ) 1)
    (hxs : ∀ x ∈ xs, x ∈ Set.Icc (0 : ℝ) 1) :
    ((twopointtwo_nearest_edges_from f history xs).map
      (fun e => |f e.1 - f e.2| ^ (1 + η))).sum ≤ 4 / η := by
  have hedge := twopointtwo_edge_endpoints_in_unit_interval f history xs hhistory hxs
  calc
    ((twopointtwo_nearest_edges_from f history xs).map
        (fun e => |f e.1 - f e.2| ^ (1 + η))).sum ≤
      ((twopointtwo_nearest_edges_from f history xs).map (fun e =>
        |e.2 - e.1| ^ η * ∫ t in Set.uIoc e.1 e.2,
          |deriv f t| ^ (1 + η))).sum := by
        apply List.sum_le_sum
        intro e he
        simpa [abs_sub_comm] using twopointtwo_local_holder η hη f hf e.1 e.2
          (hedge e he).1 (hedge e he).2
    _ ≤ 4 / η := twopointtwo_action_charge_bound η hη f hf history xs
      hhistory hxs

@[blueprint "lem:twopointtwo-diagonal-bound"
  (statement := /-- As $\eta\to0$ through $0<\eta<1$, the optimal cumulative $(1+\eta)$-power prediction loss on $\mathcal F_{1+\eta}$ is $O(\eta^{-1})$. -/)
  (proof := /-- Fix $0<\eta<1$ and use the nearest-neighbor learner of \cref{def:twopointtwo-nearest-learner}. For any target $f\in\mathcal F_{1+\eta}$ and any finite query list in $[0,1]$, the first query is unscored by \cref{def:online-loss}. On the remaining queries, \cref{lem:twopointtwo-loss-as-edge-sum} identifies the learner's cumulative loss with the sum of the powered endpoint differences over its insertion edges. By \cref{lem:twopointtwo-edge-error-sum-bound}, that real sum is at most $4/\eta$, hence its extended-nonnegative image is at most $8\operatorname{ofReal}(\eta^{-1})$. Taking the supremum over targets and query lists in \cref{def:worst-case-loss}, then bounding the infimum in \cref{def:optimal-loss} by this learner, gives the same estimate for the optimal loss. The constant $8$ works for every $\eta\in(0,1)$, and therefore eventually along \cref{def:positive-parameter-filter}; \cref{def:ennreal-is-big-o-upper,def:inverse-parameter-scale} identify this estimate with the asserted $O(\eta^{-1})$ bound. -/)
  (title := /-- The diagonal nearest-neighbor bound -/)
  (latexEnv := "lemma")]
lemma twopointtwo_diagonal_bound :
    ennreal_is_big_o_upper positive_parameter_filter
      (fun η : ℝ => optimal_loss (1 + η) (smooth_function_class (1 + η)))
      inverse_parameter_scale := by
  unfold ennreal_is_big_o_upper
  refine ⟨8, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with η hη
  unfold optimal_loss
  refine iInf_le_of_le twopointtwo_nearest_learner ?_
  unfold worst_case_loss
  refine iSup_le fun f => ?_
  refine iSup_le fun queries => ?_
  rcases f with ⟨f, hf⟩
  rcases queries with ⟨queries, hqueries⟩
  cases queries with
  | nil => simp [online_loss]
  | cons x xs =>
      have hx : x ∈ Set.Icc (0 : ℝ) 1 := hqueries x (by simp)
      have hxs : ∀ y ∈ xs, y ∈ Set.Icc (0 : ℝ) 1 := by
        intro y hy
        exact hqueries y (by simp [hy])
      have hreal := twopointtwo_edge_error_sum_bound η hη f hf [(x, f x)] xs
        (by
          intro z hz
          simp only [List.mem_singleton] at hz
          subst z
          exact hx) hxs
      rw [show online_loss (1 + η) twopointtwo_nearest_learner f (x :: xs) =
          online_loss_from (1 + η) twopointtwo_nearest_learner f [(x, f x)] xs by
        rfl]
      rw [twopointtwo_loss_as_edge_sum (1 + η) f [(x, f x)] xs
        (by simp) (by simp)]
      let edges := twopointtwo_nearest_edges_from f [(x, f x)] xs
      have hofreal : (edges.map
          (fun e => ENNReal.ofReal (|f e.1 - f e.2| ^ (1 + η)))).sum =
          ENNReal.ofReal ((edges.map
            (fun e => |f e.1 - f e.2| ^ (1 + η))).sum) := by
        induction edges with
        | nil => simp
        | cons e es ih =>
            simp only [List.map_cons, List.sum_cons]
            rw [ih, ENNReal.ofReal_add (Real.rpow_nonneg (abs_nonneg _) _)
              (List.sum_nonneg fun u hu => by
                rcases List.mem_map.mp hu with ⟨a, ha, rfl⟩
                positivity)]
      rw [hofreal]
      calc
        ENNReal.ofReal ((edges.map
            (fun e => |f e.1 - f e.2| ^ (1 + η))).sum) ≤
            ENNReal.ofReal (4 / η) := ENNReal.ofReal_le_ofReal hreal
        _ ≤ ENNReal.ofReal (8 / η) := ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_right (by norm_num) hη.1.le)
        _ = (8 : ENNReal) * inverse_parameter_scale η := by
          simp [inverse_parameter_scale, div_eq_mul_inv, ENNReal.ofReal_mul]

@[blueprint "lem:epsilonless-smooth-function-oscillation"
  (statement := /-- Let $\epsilon\in(0,1)$ and $f\in\mathcal F_{1+\epsilon}$. Then
  $|f(x)-f(y)|\leq 1$ for all $x,y\in[0,1]$. -/)
  (proof := /-- By \cref{def:smooth-function-class}, the derivative of $f$ has
  $(1+\epsilon)$-power integral at most $1$ on the probability space $(0,1]$.
  Monotonicity of $L^p$ seminorms on a probability space bounds its $L^1$
  seminorm, and hence $\int_0^1 |f'(t)|\,dt$, by $1$.  For ordered
  $y\leq x$ in $[0,1]$, absolute continuity and the fundamental theorem of
  calculus give
  \[
    |f(x)-f(y)|\leq\int_y^x |f'(t)|\,dt
      \leq\int_0^1 |f'(t)|\,dt\leq1.
  \]
  Interchanging $x$ and $y$ proves the other order. -/)
  (title := /-- Unit oscillation of the smoothness class -/)
  (latexEnv := "lemma")]
lemma epsilonless_smooth_function_oscillation (ε : ℝ)
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (f : ℝ → ℝ)
    (hf : f ∈ smooth_function_class (1 + ε)) (x y : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |f x - f y| ≤ 1 := by
  rcases hf with ⟨hfac, hfint, hfbound⟩
  have hq_pos : 0 < 1 + ε := by linarith [hε.1]
  let μ : MeasureTheory.Measure ℝ :=
    MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)
  let g : ℝ → ℝ := fun z => |deriv f z|
  let q : NNReal := ⟨1 + ε, hq_pos.le⟩
  letI : MeasureTheory.IsProbabilityMeasure μ := ⟨by simp [μ]⟩
  have hq_toReal : (q : ENNReal).toReal = 1 + ε := by
    rw [← ENNReal.coe_toNNReal_eq_toReal, ENNReal.toNNReal_coe]
    rfl
  have hq_integrable : MeasureTheory.Integrable
      (fun z => |deriv f z| ^ (1 + ε)) μ := by
    change MeasureTheory.Integrable
      (fun z => |deriv f z| ^ (1 + ε))
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1))
    exact hfint.1
  have hg_meas : MeasureTheory.AEStronglyMeasurable g μ := by
    have hroot : MeasureTheory.AEStronglyMeasurable
        (fun z => (|deriv f z| ^ (1 + ε)) ^ (1 + ε)⁻¹) μ :=
      (Real.continuous_rpow_const (inv_nonneg.mpr hq_pos.le)).comp_aestronglyMeasurable
        hq_integrable.aestronglyMeasurable
    convert hroot using 1
    funext z
    dsimp [g]
    rw [← Real.rpow_mul (abs_nonneg (deriv f z))]
    rw [mul_inv_cancel₀ hq_pos.ne']
    simp
  have hq_zero : (q : ENNReal) ≠ 0 := by
    apply ENNReal.coe_ne_zero.mpr
    exact ne_of_gt hq_pos
  have hq_top : (q : ENNReal) ≠ ⊤ := by simp
  have hq_mem : MeasureTheory.MemLp g (q : ENNReal) μ := by
    apply (MeasureTheory.integrable_norm_rpow_iff hg_meas hq_zero hq_top).mp
    rw [hq_toReal]
    simpa [g, Real.norm_eq_abs] using hq_integrable
  have hq_norm_le : MeasureTheory.eLpNorm g (q : ENNReal) μ ≤ 1 := by
    rw [hq_mem.eLpNorm_eq_integral_rpow_norm hq_zero hq_top,
      ENNReal.ofReal_le_one]
    apply Real.rpow_le_one
    · exact MeasureTheory.integral_nonneg fun z =>
        Real.rpow_nonneg (norm_nonneg _) _
    · rw [hq_toReal]
      simpa [μ, g, Real.norm_eq_abs,
        intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hfbound
    · positivity
  have honeq : (1 : ENNReal) ≤ (q : ENNReal) := by
    exact_mod_cast (show (1 : ℝ) ≤ 1 + ε by linarith [hε.1])
  have hone_mem : MeasureTheory.MemLp g 1 μ := hq_mem.mono_exponent honeq
  have hone_norm_le : MeasureTheory.eLpNorm g 1 μ ≤ 1 :=
    (MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le honeq hg_meas).trans hq_norm_le
  have hintegral_le : (∫ z, |deriv f z| ∂μ) ≤ 1 := by
    rw [hone_mem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp),
      ENNReal.ofReal_le_one] at hone_norm_le
    simpa [g, Real.norm_eq_abs] using hone_norm_le
  have hinterval_le : (∫ z in (0 : ℝ)..1, |deriv f z|) ≤ 1 := by
    rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    simpa [μ] using hintegral_le
  have hordered (a b : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1)
      (hb : b ∈ Set.Icc (0 : ℝ) 1) (hba : b ≤ a) :
      |f a - f b| ≤ 1 := by
    have hsub : Set.uIcc b a ⊆ Set.uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le hba, Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      exact Set.Icc_subset_Icc hb.1 ha.2
    have hfi : IntervalIntegrable (fun z => |deriv f z|)
        MeasureTheory.volume 0 1 := by
      simpa [Real.norm_eq_abs] using hfac.intervalIntegrable_deriv.norm
    calc
      |f a - f b| = |∫ z in b..a, deriv f z| := by
        rw [(hfac.mono hsub).integral_deriv_eq_sub]
      _ ≤ ∫ z in b..a, |deriv f z| :=
        intervalIntegral.abs_integral_le_integral_abs hba
      _ ≤ ∫ z in (0 : ℝ)..1, |deriv f z| := by
        apply intervalIntegral.integral_mono_interval hb.1 hba ha.2
        · exact Filter.Eventually.of_forall fun z => abs_nonneg (deriv f z)
        · exact hfi
      _ ≤ 1 := hinterval_le
  rcases le_total y x with hyx | hxy
  · exact hordered x y hx hy hyx
  · simpa [abs_sub_comm] using hordered y x hy hx hxy

@[blueprint "lem:epsilonless-bounded-power-comparison"
  (statement := /-- Let $u,v,\delta,\epsilon\in\mathbb R$ satisfy
  $0<\epsilon\leq\delta<1$, $0\leq u\leq v$, and $u\leq2$. Then
  $u^{1+\delta}\leq2v^{1+\epsilon}$. -/)
  (proof := /-- The exponent difference satisfies
  $0\leq\delta-\epsilon\leq1$.  If $u=0$, the conclusion follows from
  $1+\delta>0$.  Otherwise, the real-power addition law, monotonicity in the
  base, and $u\leq2$ give
  \[
    u^{1+\delta}
      =u^{1+\epsilon}u^{\delta-\epsilon}
      \leq v^{1+\epsilon}2^{\delta-\epsilon}
      \leq2v^{1+\epsilon}.
  \] -/)
  (title := /-- Comparison of bounded real powers -/)
  (latexEnv := "lemma")]
lemma epsilonless_bounded_power_comparison (δ ε u v : ℝ)
    (hε : 0 < ε) (hδ : δ < 1) (hεδ : ε ≤ δ)
    (hu : 0 ≤ u) (huv : u ≤ v) (hu2 : u ≤ 2) :
    u ^ (1 + δ) ≤ 2 * v ^ (1 + ε) := by
  have hδ_pos : 0 < δ := lt_of_lt_of_le hε hεδ
  by_cases hu0 : u = 0
  · have hexponent_ne : 1 + δ ≠ 0 := ne_of_gt (by linarith)
    rw [hu0, Real.zero_rpow hexponent_ne]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (le_trans hu huv) _)
  have hu_pos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  have hdiff_nonneg : 0 ≤ δ - ε := sub_nonneg.mpr hεδ
  have hdiff_le : δ - ε ≤ 1 := by linarith
  have hexponent_nonneg : 0 ≤ 1 + ε := by linarith
  have hpower_mono : u ^ (1 + ε) ≤ v ^ (1 + ε) :=
    Real.rpow_le_rpow hu huv hexponent_nonneg
  have hfactor_le : u ^ (δ - ε) ≤ 2 := by
    calc
      u ^ (δ - ε) ≤ (2 : ℝ) ^ (δ - ε) :=
        Real.rpow_le_rpow hu hu2 hdiff_nonneg
      _ ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) hdiff_le
  calc
    u ^ (1 + δ) = u ^ ((1 + ε) + (δ - ε)) := by ring_nf
    _ = u ^ (1 + ε) * u ^ (δ - ε) :=
      Real.rpow_add hu_pos (1 + ε) (δ - ε)
    _ ≤ v ^ (1 + ε) * 2 := by
      exact mul_le_mul hpower_mono hfactor_le
        (Real.rpow_nonneg hu _) (Real.rpow_nonneg (le_trans hu huv) _)
    _ = 2 * v ^ (1 + ε) := by ring

@[blueprint "lem:epsilonless-clipped-learner-loss-comparison"
  (statement := /-- Let $\delta,\epsilon\in(0,1)$ satisfy
  $\epsilon\leq\delta$.  For every online learner $A$, there is an online
  learner $B$ such that
  \[
    \mathscr L_{1+\delta}(B,\mathcal F_{1+\epsilon})
      \leq2\mathscr L_{1+\epsilon}(A,\mathcal F_{1+\epsilon}).
  \] -/)
  (proof := /-- Given a nonempty history, let $B$ project the prediction of
  $A$ onto the interval of radius $1$ about the most recently observed
  response; on the empty history let it agree with $A$.  By
  \cref{lem:epsilonless-smooth-function-oscillation}, the next target value
  belongs to this interval.  Projection cannot increase its distance from the
  target, and the projected error is at most $2$.  Hence
  \cref{lem:epsilonless-bounded-power-comparison} bounds each
  $(1+\delta)$-power error of $B$ by twice the corresponding
  $(1+\epsilon)$-power error of $A$.  Induction on the remaining query list,
  using the recursive definition in \cref{def:online-loss-from}, gives the
  same inequality for cumulative loss.  The first observation in
  \cref{def:online-loss} supplies the required nonempty history.  Taking the
  two suprema in \cref{def:worst-case-loss} proves the stated bound. -/)
  (title := /-- Loss comparison for a clipped learner -/)
  (latexEnv := "lemma")]
lemma epsilonless_clipped_learner_loss_comparison (δ ε : ℝ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (hεδ : ε ≤ δ) (A : online_learner) :
    ∃ B : online_learner,
      worst_case_loss (1 + δ) B (smooth_function_class (1 + ε)) ≤
        (2 : ENNReal) *
          worst_case_loss (1 + ε) A (smooth_function_class (1 + ε)) := by
  let clip : ℝ → ℝ → ℝ :=
    fun center prediction =>
      max (center - 1) (min (center + 1) prediction)
  let B : online_learner :=
    fun history x =>
      match history.getLast? with
      | none => A history x
      | some (_, y) => clip y (A history x)
  have hclip (center prediction target : ℝ)
      (htarget : target ∈ Set.Icc (center - 1) (center + 1)) :
      |clip center prediction - target| ≤ |prediction - target| ∧
        |clip center prediction - target| ≤ 2 := by
    rcases htarget with ⟨htarget_lower, htarget_upper⟩
    by_cases hlower : prediction ≤ center - 1
    · have hclip_eq : clip center prediction = center - 1 := by
        dsimp [clip]
        rw [min_eq_right (by linarith), max_eq_left hlower]
      rw [hclip_eq, abs_of_nonpos (by linarith : center - 1 - target ≤ 0),
        abs_of_nonpos (by linarith : prediction - target ≤ 0)]
      constructor <;> linarith
    by_cases hupper : center + 1 ≤ prediction
    · have hclip_eq : clip center prediction = center + 1 := by
        dsimp [clip]
        rw [min_eq_left hupper, max_eq_right (by linarith)]
      rw [hclip_eq, abs_of_nonneg (by linarith : 0 ≤ center + 1 - target),
        abs_of_nonneg (by linarith : 0 ≤ prediction - target)]
      constructor <;> linarith
    · have hlower' : center - 1 ≤ prediction := by
        exact le_of_not_ge hlower
      have hupper' : prediction ≤ center + 1 := by
        exact le_of_not_ge hupper
      have hclip_eq : clip center prediction = prediction := by
        simp [clip, min_eq_right hupper', max_eq_right hlower']
      rw [hclip_eq]
      constructor
      · exact le_rfl
      · rw [abs_le]
        constructor <;> linarith
  have hloss_from (f : ℝ → ℝ)
      (hf : f ∈ smooth_function_class (1 + ε)) :
      ∀ (history : List (ℝ × ℝ)) (queries : List ℝ),
        (∃ x₀ ∈ Set.Icc (0 : ℝ) 1,
          history.getLast? = some (x₀, f x₀)) →
        (∀ x ∈ queries, x ∈ Set.Icc (0 : ℝ) 1) →
        online_loss_from (1 + δ) B f history queries ≤
          (2 : ENNReal) * online_loss_from (1 + ε) A f history queries := by
    intro history queries
    induction queries generalizing history with
    | nil =>
        intro _ _
        simp [online_loss_from]
    | cons x xs ih =>
        intro hhistory hqueries
        rcases hhistory with ⟨x₀, hx₀, hlast⟩
        have hx : x ∈ Set.Icc (0 : ℝ) 1 := hqueries x (by simp)
        have hxs : ∀ z ∈ xs, z ∈ Set.Icc (0 : ℝ) 1 := by
          intro z hz
          exact hqueries z (by simp [hz])
        have hoscillation : |f x - f x₀| ≤ 1 :=
          epsilonless_smooth_function_oscillation ε hε f hf x x₀ hx hx₀
        have htarget : f x ∈ Set.Icc (f x₀ - 1) (f x₀ + 1) := by
          rw [abs_le] at hoscillation
          constructor <;> linarith
        have hB : B history x = clip (f x₀) (A history x) := by
          simp [B, hlast]
        have hclip_bounds :=
          hclip (f x₀) (A history x) (f x) htarget
        have hpower :
            |B history x - f x| ^ (1 + δ) ≤
              2 * |A history x - f x| ^ (1 + ε) := by
          rw [hB]
          exact epsilonless_bounded_power_comparison δ ε
            |clip (f x₀) (A history x) - f x|
            |A history x - f x| hε.1 hδ.2 hεδ
            (abs_nonneg _) hclip_bounds.1 hclip_bounds.2
        have hterm :
            ENNReal.ofReal (|B history x - f x| ^ (1 + δ)) ≤
              (2 : ENNReal) *
                ENNReal.ofReal (|A history x - f x| ^ (1 + ε)) := by
          calc
            ENNReal.ofReal (|B history x - f x| ^ (1 + δ)) ≤
                ENNReal.ofReal
                  (2 * |A history x - f x| ^ (1 + ε)) :=
              ENNReal.ofReal_le_ofReal hpower
            _ = (2 : ENNReal) *
                ENNReal.ofReal (|A history x - f x| ^ (1 + ε)) := by
              rw [ENNReal.ofReal_mul (by norm_num)]
              norm_num
        have hrest :
            online_loss_from (1 + δ) B f
                (history ++ [(x, f x)]) xs ≤
              (2 : ENNReal) *
                online_loss_from (1 + ε) A f
                  (history ++ [(x, f x)]) xs := by
          apply ih (history ++ [(x, f x)])
          · exact ⟨x, hx, by simp⟩
          · exact hxs
        simp only [online_loss_from]
        calc
          ENNReal.ofReal (|B history x - f x| ^ (1 + δ)) +
                online_loss_from (1 + δ) B f
                  (history ++ [(x, f x)]) xs ≤
              (2 : ENNReal) *
                  ENNReal.ofReal (|A history x - f x| ^ (1 + ε)) +
                (2 : ENNReal) *
                  online_loss_from (1 + ε) A f
                    (history ++ [(x, f x)]) xs :=
            add_le_add hterm hrest
          _ = (2 : ENNReal) *
              (ENNReal.ofReal (|A history x - f x| ^ (1 + ε)) +
                online_loss_from (1 + ε) A f
                  (history ++ [(x, f x)]) xs) := by
            rw [mul_add]
  refine ⟨B, ?_⟩
  unfold worst_case_loss
  refine iSup_le fun f => iSup_le fun queries => ?_
  have hpoint :
      online_loss (1 + δ) B f.1 queries.1 ≤
        (2 : ENNReal) * online_loss (1 + ε) A f.1 queries.1 := by
    cases hqueries : queries.1 with
    | nil =>
        simp [online_loss, hqueries]
    | cons x xs =>
        simp only [online_loss, hqueries]
        apply hloss_from f.1 f.2 [(x, f.1 x)] xs
        · have hx : x ∈ Set.Icc (0 : ℝ) 1 :=
            queries.2 x (by rw [hqueries]; exact List.mem_cons_self)
          exact ⟨x, hx, rfl⟩
        · intro z hz
          exact queries.2 z (by
            rw [hqueries]
            exact List.mem_cons_of_mem x hz)
  have hsup :
      online_loss (1 + ε) A f.1 queries.1 ≤
        ⨆ g : {g : ℝ → ℝ // g ∈ smooth_function_class (1 + ε)},
          ⨆ qs : {qs : List ℝ // ∀ x ∈ qs, x ∈ Set.Icc (0 : ℝ) 1},
            online_loss (1 + ε) A g.1 qs.1 :=
    le_iSup_of_le f (le_iSup_of_le queries (le_refl _))
  exact hpoint.trans (mul_le_mul_left' hsup 2)

@[blueprint "lem:epsilonless-loss-exponent-comparison"
  (statement := /-- Let $\delta,\epsilon\in\mathbb R$ satisfy $0<\delta<1$, $0<\epsilon<1$, and $\epsilon\leq\delta$. Then
  \[
    \operatorname{opt}_{1+\delta}(\mathcal F_{1+\epsilon})
      \leq 2\operatorname{opt}_{1+\epsilon}(\mathcal F_{1+\epsilon}).
  \] -/)
  (proof := /-- Fix $0<\epsilon\leq\delta<1$.  For every online learner
  $A$, \cref{lem:epsilonless-clipped-learner-loss-comparison} supplies a
  learner $B$ such that
  \[
    \mathscr L_{1+\delta}(B,\mathcal F_{1+\epsilon})
      \leq2\mathscr L_{1+\epsilon}(A,\mathcal F_{1+\epsilon}).
  \]
  By \cref{def:optimal-loss}, the left-hand optimal loss is at most the
  loss of this $B$.  Taking the infimum over $A$ and distributing the finite
  factor $2$ through that infimum proves the asserted inequality. -/)
  (title := /-- Comparison in the loss exponent -/)
  (latexEnv := "lemma")]
lemma epsilonless_loss_exponent_comparison (δ ε : ℝ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (hεδ : ε ≤ δ) :
    optimal_loss (1 + δ) (smooth_function_class (1 + ε)) ≤
      (2 : ENNReal) * optimal_loss (1 + ε) (smooth_function_class (1 + ε)) := by
  unfold optimal_loss
  rw [ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
  refine le_iInf fun A => ?_
  obtain ⟨B, hB⟩ :=
    epsilonless_clipped_learner_loss_comparison δ ε hδ hε hεδ A
  exact (iInf_le _ B).trans hB

@[blueprint "lem:jensen-smoothness-exponent-comparison"
  (statement := /-- Let $\delta,\epsilon\in\mathbb R$ satisfy $0<\delta<1$, $0<\epsilon<1$, and $\delta\leq\epsilon$. Then
  \[
    \operatorname{opt}_{1+\delta}(\mathcal F_{1+\epsilon})
      \leq \operatorname{opt}_{1+\delta}(\mathcal F_{1+\delta}).
  \] -/)
  (proof := /-- Put $p=1+\delta$ and $q=1+\epsilon$. The hypotheses give $1<p\leq q<2$. Let $f\in\mathcal F_q$, and restrict Lebesgue measure to $(0,1]$, obtaining a probability measure. Integrability of $|f'|^q$ and positivity of $q$ imply measurability of $|f'|$, since $|f'|=(|f'|^q)^{1/q}$. Thus $|f'|$ belongs to $L^q$, and the integral identity for its $L^q$ norm, together with the defining action bound in \cref{def:smooth-function-class}, gives $\lVert f'\rVert_q\leq1$. Monotonicity of $L^r$ norms on a probability space yields $|f'|\in L^p$ and $\lVert f'\rVert_p\leq\lVert f'\rVert_q$. Applying the norm--integral identity once more gives
  \[
    \int_0^1 |f'(x)|^p\,dx
      \leq 1.
  \]
  Absolute continuity is unchanged, so \cref{def:smooth-function-class} yields $\mathcal F_q\subseteq\mathcal F_p$. Fix an online learner $A$. The subtype inclusion maps every target in $\mathcal F_q$ to the same function in $\mathcal F_p$; monotonicity of the two suprema in \cref{def:worst-case-loss} therefore gives
  \[
    \mathscr L_p(A,\mathcal F_q)\leq\mathscr L_p(A,\mathcal F_p).
  \]
  Taking the infimum over all $A$ and using \cref{def:optimal-loss} proves
  $\operatorname{opt}_p(\mathcal F_q)\leq\operatorname{opt}_p(\mathcal F_p)$, which is the claimed inequality. -/)
  (title := /-- Comparison in the smoothness exponent -/)
  (latexEnv := "lemma")]
lemma jensen_smoothness_exponent_comparison (δ ε : ℝ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (hδε : δ ≤ ε) :
    optimal_loss (1 + δ) (smooth_function_class (1 + ε)) ≤
      optimal_loss (1 + δ) (smooth_function_class (1 + δ)) := by
  have hp_pos : 0 < 1 + δ := by linarith [hδ.1]
  have hq_pos : 0 < 1 + ε := by linarith [hε.1]
  have hpq : 1 + δ ≤ 1 + ε := by linarith
  have hsubset : smooth_function_class (1 + ε) ⊆
      smooth_function_class (1 + δ) := by
    intro f hf
    rcases hf with ⟨hfac, hfint, hfbound⟩
    let μ : MeasureTheory.Measure ℝ :=
      MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)
    let g : ℝ → ℝ := fun x => |deriv f x|
    let p : NNReal := ⟨1 + δ, hp_pos.le⟩
    let q : NNReal := ⟨1 + ε, hq_pos.le⟩
    letI : MeasureTheory.IsProbabilityMeasure μ := ⟨by simp [μ]⟩
    have hp_toReal : (p : ENNReal).toReal = 1 + δ := by
      rw [← ENNReal.coe_toNNReal_eq_toReal, ENNReal.toNNReal_coe]
      rfl
    have hq_toReal : (q : ENNReal).toReal = 1 + ε := by
      rw [← ENNReal.coe_toNNReal_eq_toReal, ENNReal.toNNReal_coe]
      rfl
    have hq_raw_integrable : MeasureTheory.Integrable
        (fun x => |deriv f x| ^ (1 + ε)) μ := by
      change MeasureTheory.Integrable
        (fun x => |deriv f x| ^ (1 + ε))
        (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1))
      exact hfint.1
    have hg_meas : MeasureTheory.AEStronglyMeasurable g μ := by
      have hroot : MeasureTheory.AEStronglyMeasurable
          (fun x => (|deriv f x| ^ (1 + ε)) ^ (1 + ε)⁻¹) μ :=
        (Real.continuous_rpow_const (inv_nonneg.mpr hq_pos.le)).comp_aestronglyMeasurable
          hq_raw_integrable.aestronglyMeasurable
      convert hroot using 1
      funext x
      dsimp [g]
      rw [← Real.rpow_mul (abs_nonneg (deriv f x))]
      rw [mul_inv_cancel₀ hq_pos.ne']
      simp
    have hq_zero : (q : ENNReal) ≠ 0 := by
      apply ENNReal.coe_ne_zero.mpr
      apply ne_of_gt
      change 0 < 1 + ε
      exact hq_pos
    have hp_zero : (p : ENNReal) ≠ 0 := by
      apply ENNReal.coe_ne_zero.mpr
      apply ne_of_gt
      change 0 < 1 + δ
      exact hp_pos
    have hq_top : (q : ENNReal) ≠ ⊤ := by simp
    have hp_top : (p : ENNReal) ≠ ⊤ := by simp
    have hpq' : (p : ENNReal) ≤ (q : ENNReal) := by
      exact_mod_cast hpq
    have hq_integrable : MeasureTheory.Integrable
        (fun x => ‖g x‖ ^ (q : ENNReal).toReal) μ := by
      rw [hq_toReal]
      simpa [g, Real.norm_eq_abs] using hq_raw_integrable
    have hq_mem : MeasureTheory.MemLp g (q : ENNReal) μ :=
      (MeasureTheory.integrable_norm_rpow_iff hg_meas hq_zero hq_top).mp
        hq_integrable
    have hq_norm_le : MeasureTheory.eLpNorm g (q : ENNReal) μ ≤ 1 := by
      rw [hq_mem.eLpNorm_eq_integral_rpow_norm hq_zero hq_top,
        ENNReal.ofReal_le_one]
      apply Real.rpow_le_one
      · exact MeasureTheory.integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
      · rw [hq_toReal]
        simpa [μ, g, Real.norm_eq_abs,
          intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hfbound
      · positivity
    have hp_norm_le : MeasureTheory.eLpNorm g (p : ENNReal) μ ≤ 1 :=
      (MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le hpq' hg_meas).trans hq_norm_le
    have hp_mem : MeasureTheory.MemLp g (p : ENNReal) μ :=
      hq_mem.mono_exponent hpq'
    have hp_root_le :
        (∫ x, ‖g x‖ ^ (p : ENNReal).toReal ∂μ) ^
            (p : ENNReal).toReal⁻¹ ≤ 1 := by
      rw [hp_mem.eLpNorm_eq_integral_rpow_norm hp_zero hp_top,
        ENNReal.ofReal_le_one] at hp_norm_le
      exact hp_norm_le
    have hp_integral_le :
        (∫ x, ‖g x‖ ^ (p : ENNReal).toReal ∂μ) ≤ 1 := by
      by_contra h
      have hone_lt : 1 < ∫ x, ‖g x‖ ^ (p : ENNReal).toReal ∂μ :=
        lt_of_not_ge h
      have hroot_lt :
          1 < (∫ x, ‖g x‖ ^ (p : ENNReal).toReal ∂μ) ^
              (p : ENNReal).toReal⁻¹ :=
        Real.one_lt_rpow hone_lt
          (inv_pos.mpr (ENNReal.toReal_pos hp_zero hp_top))
      exact (not_lt_of_ge hp_root_le) hroot_lt
    refine ⟨hfac, ?_, ?_⟩
    · constructor
      · change MeasureTheory.Integrable
          (fun x => |deriv f x| ^ (1 + δ))
          (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1))
        have hp_power_integrable := hp_mem.integrable_norm_rpow hp_zero hp_top
        rw [hp_toReal] at hp_power_integrable
        simpa [μ, g, Real.norm_eq_abs] using hp_power_integrable
      · simp
    · rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      rw [hp_toReal] at hp_integral_le
      simpa [μ, g, Real.norm_eq_abs] using hp_integral_le
  unfold optimal_loss
  refine iInf_mono fun A => ?_
  unfold worst_case_loss
  refine iSup_le fun f => ?_
  exact le_iSup_of_le ⟨f.1, hsubset f.2⟩ (le_refl _)

@[blueprint "lem:finite-bound-assembly"
  (statement := /-- Uniformly for $\delta,\epsilon\in(0,1)$ as $\min(\delta,\epsilon)\to0$, the optimal $(1+\delta)$-power loss on $\mathcal F_{1+\epsilon}$ has upper order $O(\min(\delta,\epsilon)^{-1})$. -/)
  (proof := /-- By \cref{lem:twopointtwo-diagonal-bound}, there are a finite constant $C$ and a positive threshold $r$ such that the diagonal loss at every $\eta\in(0,1)$ with $\eta<r$ is at most $C\eta^{-1}$; this is the eventual estimate encoded by \cref{def:positive-parameter-filter,def:ennreal-is-big-o-upper,def:inverse-parameter-scale}. Fix $\delta,\epsilon\in(0,1)$ with $\min(\delta,\epsilon)<r$. If $\epsilon\leq\delta$, then \cref{lem:epsilonless-loss-exponent-comparison} bounds the desired loss by twice the diagonal loss at $\epsilon=\min(\delta,\epsilon)$, and hence by $2C\min(\delta,\epsilon)^{-1}$. If $\delta\leq\epsilon$, then \cref{lem:jensen-smoothness-exponent-comparison} bounds it by the diagonal loss at $\delta=\min(\delta,\epsilon)$, and hence by $C\min(\delta,\epsilon)^{-1}$. Thus the finite constant $2C$ works in both cases. By the definition of the limiting filter in \cref{def:positive-parameter-pair-filter}, this is precisely the required eventual upper bound. -/)
  (title := /-- Assembly of the two-parameter estimate -/)
  (latexEnv := "lemma")]
lemma finite_bound_assembly :
    ennreal_is_big_o_upper positive_parameter_pair_filter
      (fun z : ℝ × ℝ =>
        optimal_loss (1 + z.1) (smooth_function_class (1 + z.2)))
      (fun z : ℝ × ℝ => inverse_parameter_scale (min z.1 z.2)) := by
  unfold ennreal_is_big_o_upper
  rcases twopointtwo_diagonal_bound with ⟨C, hC⟩
  refine ⟨2 * C, ?_⟩
  rw [positive_parameter_pair_filter]
  have hdiag : ∀ᶠ z in Filter.comap (fun z : ℝ × ℝ => min z.1 z.2)
      positive_parameter_filter ⊓
      Filter.principal (Set.prod (Set.Ioo 0 1) (Set.Ioo 0 1)),
      optimal_loss (1 + min z.1 z.2)
          (smooth_function_class (1 + min z.1 z.2)) ≤
        (C : ENNReal) * inverse_parameter_scale (min z.1 z.2) := by
    apply Filter.Eventually.filter_mono inf_le_left
    exact hC.comap (fun z : ℝ × ℝ => min z.1 z.2)
  have hmem : ∀ᶠ z in Filter.comap (fun z : ℝ × ℝ => min z.1 z.2)
      positive_parameter_filter ⊓
      Filter.principal (Set.prod (Set.Ioo 0 1) (Set.Ioo 0 1)),
      z ∈ Set.prod (Set.Ioo 0 1) (Set.Ioo 0 1) := by
    apply Filter.Eventually.filter_mono inf_le_right
    simp
  filter_upwards [hdiag, hmem] with z hdiag hz
  rcases hz with ⟨hδ, hε⟩
  rcases le_total z.2 z.1 with hεδ | hδε
  · rw [min_eq_right hεδ] at hdiag ⊢
    calc
      optimal_loss (1 + z.1) (smooth_function_class (1 + z.2)) ≤
          (2 : ENNReal) * optimal_loss (1 + z.2)
            (smooth_function_class (1 + z.2)) :=
        epsilonless_loss_exponent_comparison z.1 z.2 hδ hε hεδ
      _ ≤ (2 : ENNReal) * ((C : ENNReal) * inverse_parameter_scale z.2) := by
        gcongr
      _ = ((2 * C : NNReal) : ENNReal) * inverse_parameter_scale z.2 := by
        simp [mul_assoc]
  · rw [min_eq_left hδε] at hdiag ⊢
    calc
      optimal_loss (1 + z.1) (smooth_function_class (1 + z.2)) ≤
          optimal_loss (1 + z.1) (smooth_function_class (1 + z.1)) :=
        jensen_smoothness_exponent_comparison z.1 z.2 hδ hε hδε
      _ ≤ (C : ENNReal) * inverse_parameter_scale z.1 := hdiag
      _ ≤ ((2 * C : NNReal) : ENNReal) * inverse_parameter_scale z.1 := by
        gcongr
        simpa using (mul_le_mul_right' (by norm_num : (1 : NNReal) ≤ 2) C)

@[blueprint "thm:finitebound"
  (statement := /-- For $\delta,\epsilon\in(0,1)$, uniformly as $\min(\delta,\epsilon)\to0$, one has
  \[
    \operatorname{opt}_{1+\delta}(\mathcal F_{1+\epsilon})
      = O\!\left(\min(\delta,\epsilon)^{-1}\right).
  \]
  In particular, the estimate applies when either parameter tends to zero while the other remains in a compact subinterval of $(0,1)$. -/)
  (proof := /-- With the online minimax loss interpreted by \cref{def:worst-case-loss,def:optimal-loss}, so that every adversarial query lies in $[0,1]$, and with the limiting regime interpreted by \cref{def:positive-parameter-pair-filter,def:ennreal-is-big-o-upper}, the assertion is exactly \cref{lem:finite-bound-assembly}. -/)
  (title := /-- Worst-case error bound for online learning of smooth functions -/)
  (latexEnv := "theorem")]
theorem finitebound :
    ennreal_is_big_o_upper positive_parameter_pair_filter
      (fun z : ℝ × ℝ =>
        optimal_loss (1 + z.1) (smooth_function_class (1 + z.2)))
      (fun z : ℝ × ℝ => inverse_parameter_scale (min z.1 z.2)) := by
  exact finite_bound_assembly

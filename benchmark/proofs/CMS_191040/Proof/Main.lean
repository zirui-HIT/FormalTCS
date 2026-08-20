import Architect
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:probability-forecast"
  (statement := /-- For an integer $K\geq 2$, a probability forecast is a vector
  $p\in\mathbb{R}^{K}$ with nonnegative coordinates and total mass one. -/)
  (title := /-- Probability forecasts on a finite outcome space -/)
  (latexEnv := "definition")]
def probability_forecast (K : ℕ) : Type :=
  {p : Fin K → ℝ // p ∈ stdSimplex ℝ (Fin K)}

@[blueprint "def:probability-forecast-measurable-space"
  (statement := /-- For every $K\in\mathbb{N}$, equip the probability
  simplex $\Delta_K$ with the Borel $\sigma$-algebra induced by its
  Euclidean subspace topology. -/)
  (title := /-- Borel structure on the probability simplex -/)
  (latexEnv := "definition")]
noncomputable instance probability_forecast_measurable_space (K : ℕ) :
    MeasurableSpace (probability_forecast K) :=
  (borel (Fin K → ℝ)).comap
    (fun prediction : probability_forecast K => prediction.1)

@[blueprint "def:expected-scoring-loss"
  (statement := /-- Let $K\in\mathbb{N}$ and let
  $\ell:\Delta_K\times [K]\to\mathbb{R}$ be a scoring loss.  For
  $p,q\in\Delta_K$, define
  $\ell(p,q)=\sum_{y\in[K]}q_y\ell(p,y)$. -/)
  (title := /-- Expected scoring loss -/)
  (latexEnv := "definition")]
def expected_scoring_loss {K : ℕ}
    (loss : probability_forecast K → Fin K → ℝ)
    (prediction truth : probability_forecast K) : ℝ :=
  ∑ outcome, truth.1 outcome * loss prediction outcome

@[blueprint "def:is-proper-scoring-loss"
  (statement := /-- A scoring loss $\ell$ on $\Delta_K$ is proper if, for every
  true distribution $q\in\Delta_K$ and every forecast $p\in\Delta_K$,
  $\ell(q,q)\leq\ell(p,q)$. -/)
  (title := /-- Proper scoring losses -/)
  (latexEnv := "definition")]
def is_proper_scoring_loss {K : ℕ}
    (loss : probability_forecast K → Fin K → ℝ) : Prop :=
  ∀ prediction truth : probability_forecast K,
    expected_scoring_loss loss truth truth ≤
      expected_scoring_loss loss prediction truth

@[blueprint "def:distinct-forecasts"
  (statement := /-- Given a horizon $T$ and external forecasts
  $q:[T]\to\Delta_K$, let $Q=\{q_t:t\in[T]\}$ be the finite set of
  forecasts that occur during the horizon. -/)
  (title := /-- Distinct external forecasts -/)
  (latexEnv := "definition")]
noncomputable def distinct_forecasts {K T : ℕ}
    (external : Fin T → probability_forecast K) :
    Finset (probability_forecast K) := by
  classical
  exact Finset.univ.image external

@[blueprint "def:forecast-bin"
  (statement := /-- For $q\in\Delta_K$, define its forecast bin by
  $I_q=\{t\in[T]:q_t=q\}$. -/)
  (title := /-- Rounds carrying a fixed forecast -/)
  (latexEnv := "definition")]
noncomputable def forecast_bin {K T : ℕ}
    (external : Fin T → probability_forecast K)
    (q : probability_forecast K) : Finset (Fin T) := by
  classical
  exact Finset.univ.filter (fun t => external t = q)

@[blueprint "def:forecast-bin-size"
  (statement := /-- For an external forecast $q$, let
  $n_T(q)=|I_q|$ denote the number of rounds in its forecast bin. -/)
  (title := /-- Forecast-bin multiplicity -/)
  (latexEnv := "definition")]
noncomputable def forecast_bin_size {K T : ℕ}
    (external : Fin T → probability_forecast K)
    (q : probability_forecast K) : ℕ :=
  (forecast_bin external q).card

@[blueprint "def:bin-comparator-loss"
  (statement := /-- For a scoring loss $\ell$, outcomes
  $y:[T]\to[K]$, and a forecast value $q$, define the optimal constant
  comparator loss on $I_q$ by
  $C_q=\inf_{p\in\Delta_K}\sum_{t\in I_q}\ell(p,y_t)$. -/)
  (title := /-- Optimal constant loss within one forecast bin -/)
  (latexEnv := "definition")]
noncomputable def bin_comparator_loss {K T : ℕ}
    (loss : probability_forecast K → Fin K → ℝ)
    (external : Fin T → probability_forecast K)
    (outcome : Fin T → Fin K)
    (q : probability_forecast K) : ℝ :=
  sInf (Set.range (fun prediction : probability_forecast K =>
    ∑ t ∈ forecast_bin external q, loss prediction (outcome t)))

@[blueprint "def:refinement-score"
  (statement := /-- The operational refinement score of external forecasts
  $q_{1:T}$ against outcomes $y_{1:T}$ is
  $R_T(q_{1:T},y_{1:T})=\sum_{q\in Q}C_q$, where $C_q$ is the optimal
  constant comparator loss on the bin $I_q$. -/)
  (title := /-- Operational refinement score -/)
  (latexEnv := "definition")]
noncomputable def refinement_score {K T : ℕ}
    (loss : probability_forecast K → Fin K → ℝ)
    (external : Fin T → probability_forecast K)
    (outcome : Fin T → Fin K) : ℝ :=
  ∑ q ∈ distinct_forecasts external,
    bin_comparator_loss loss external outcome q

@[blueprint "def:cumulative-expected-loss"
  (statement := /-- If $m_t=\mathbb{E}[\ell(p_t,y_t)]$ is the learner's
  expected loss on round $t$, define its expected cumulative loss by
  $L_T=\sum_{t\in[T]}m_t$. -/)
  (title := /-- Expected cumulative loss -/)
  (latexEnv := "definition")]
def cumulative_expected_loss {T : ℕ}
    (roundExpectedLoss : Fin T → ℝ) : ℝ :=
  ∑ t, roundExpectedLoss t

@[blueprint "def:expected-loss-online-learner"
  (statement := /-- Fix an outcome space $[K]$.  A possibly randomized
  online learner assigns to every finite sequence $h\in[K]^*$ of past
  outcomes a Borel probability measure $\mathsf{A}(h)$ on the probability
  simplex $\Delta_K$.  A forecast is sampled from this measure before the
  current outcome is observed; dependence only on $h$ expresses the online
  information constraint. -/)
  (title := /-- Randomized online probability forecasters -/)
  (latexEnv := "definition")]
def expected_loss_online_learner (K : ℕ) : Type :=
  List (Fin K) →
    MeasureTheory.ProbabilityMeasure (probability_forecast K)

@[blueprint "def:randomized-forecast-expected-loss"
  (statement := /-- Let $\ell:\Delta_K\times[K]\to\mathbb{R}$, let
  $\mu$ be a Borel probability measure on $\Delta_K$, and let $y\in[K]$.
  The expected loss of the randomized forecast $p\sim\mu$ against $y$ is
  \[
    \overline\ell(\mu,y)=\int_{\Delta_K}\ell(p,y)\,d\mu(p).
  \] -/)
  (title := /-- Expected scoring loss of a randomized forecast -/)
  (latexEnv := "definition")]
noncomputable def randomized_forecast_expected_loss {K : ℕ}
    (loss : probability_forecast K → Fin K → ℝ)
    (distribution :
      MeasureTheory.ProbabilityMeasure (probability_forecast K))
    (outcome : Fin K) : ℝ :=
  MeasureTheory.integral distribution.toMeasure
    (fun prediction => loss prediction outcome)

@[blueprint "def:learner-cumulative-expected-loss"
  (statement := /-- Let $\ell:\Delta_K\times[K]\to\mathbb{R}$, let
  $\mathsf{A}$ be a randomized online probability forecaster, and let
  $y=(y_0,\ldots,y_{n-1})$ be a finite outcome sequence.  Its cumulative
  expected loss on $y$ is
  \[
    \sum_{i=0}^{n-1}
      \overline\ell\bigl(\mathsf{A}(y_{<i}),y_i\bigr),
  \]
  where each summand is the expectation in
  \cref{def:randomized-forecast-expected-loss}. -/)
  (title := /-- Cumulative expected loss of an online learner -/)
  (latexEnv := "definition")]
noncomputable def learner_cumulative_expected_loss {K : ℕ}
    (loss : probability_forecast K → Fin K → ℝ)
    (learner : expected_loss_online_learner K)
    (outcomes : List (Fin K)) : ℝ :=
  ∑ i : Fin outcomes.length,
    randomized_forecast_expected_loss loss
      (learner (outcomes.take i.1)) (outcomes.get i)

@[blueprint "def:has-expected-regret-bound"
  (statement := /-- Let $\ell:\Delta_K\times[K]\to\mathbb{R}$ and
  $\alpha:\mathbb{R}\to\mathbb{R}$, and let $\mathsf{A}$ be a
  randomized online probability forecaster.  The learner has expected
  regret bounded by $\alpha$ if every map
  $p\mapsto\ell(p,y)$ is integrable with respect to every conditional
  forecast distribution $\mathsf{A}(h)$ and, for every $n\geq0$ and every
  outcome sequence $y_0,\ldots,y_{n-1}$,
  \[
  \sum_{i=0}^{n-1}
    \overline\ell\bigl(\mathsf{A}(y_{<i}),y_i\bigr)
  -\inf_{p\in\Delta_K}\sum_{i=0}^{n-1}\ell(p,y_i)
  \leq \alpha(n).
  \] -/)
  (title := /-- Uniform expected regret guarantee -/)
  (latexEnv := "definition")]
noncomputable def has_expected_regret_bound {K : ℕ}
    (loss : probability_forecast K → Fin K → ℝ)
    (learner : expected_loss_online_learner K)
    (alpha : ℝ → ℝ) : Prop :=
  (∀ history : List (Fin K), ∀ outcome : Fin K,
    MeasureTheory.Integrable (fun prediction => loss prediction outcome)
      (learner history).toMeasure) ∧
    ∀ outcomes : List (Fin K),
      learner_cumulative_expected_loss loss learner outcomes -
          sInf (Set.range (fun prediction : probability_forecast K =>
            ∑ i : Fin outcomes.length, loss prediction (outcomes.get i)))
        ≤ alpha (outcomes.length : ℝ)

@[blueprint "def:forecast-bin-outcome-history"
  (statement := /-- Given external forecasts $q_0,\ldots,q_{T-1}$ and
  outcomes $y_0,\ldots,y_{T-1}$, the bin history before round $t$ is the
  chronologically ordered list
  $(y_s:0\leq s<t,\ q_s=q_t)$. -/)
  (title := /-- Outcome history visible to one forecast-bin copy -/)
  (latexEnv := "definition")]
noncomputable def forecast_bin_outcome_history {K T : ℕ}
    (external : Fin T → probability_forecast K)
    (outcome : Fin T → Fin K)
    (t : Fin T) : List (Fin K) :=
  letI := Classical.decEq (probability_forecast K)
  (List.finRange t.1).filterMap (fun i =>
    let s : Fin T := i.castLT (Nat.lt_trans i.2 t.2)
    if external s = external t then some (outcome s) else none)

@[blueprint "def:binwise-reduction-round-expected-loss"
  (statement := /-- Let $\ell:\Delta_K\times[K]\to\mathbb{R}$ and let
  $\mathsf{A}$ be a randomized online probability forecaster.  The
  forecast-bin independent-copy reduction runs one fresh copy
  $\mathsf{A}_q$ for each external forecast value $q$.  On round $t$, the
  copy indexed by $q_t$ outputs the distribution
  $\mathsf{A}((y_s:s<t,\ q_s=q_t))$ before observing $y_t$, and its
  conditional expected loss is
  \[
    \overline\ell\bigl(
      \mathsf{A}((y_s:s<t,\ q_s=q_t)),y_t\bigr).
  \]
  Thus that copy receives exactly its own preceding outcomes and no
  observations from any other forecast bin. -/)
  (title := /-- Expected losses of the forecast-bin reduction -/)
  (latexEnv := "definition")]
noncomputable def binwise_reduction_round_expected_loss {K T : ℕ}
    (loss : probability_forecast K → Fin K → ℝ)
    (learner : expected_loss_online_learner K)
    (external : Fin T → probability_forecast K)
    (outcome : Fin T → Fin K)
    (t : Fin T) : ℝ :=
  randomized_forecast_expected_loss loss
    (learner (forecast_bin_outcome_history external outcome t)) (outcome t)

@[blueprint "def:bin-expected-loss"
  (statement := /-- For a forecast value $q$, define the learner's expected
  cumulative loss on the associated bin by
  $L_q=\sum_{t\in I_q}m_t$. -/)
  (title := /-- Expected loss within one forecast bin -/)
  (latexEnv := "definition")]
noncomputable def bin_expected_loss {K T : ℕ}
    (roundExpectedLoss : Fin T → ℝ)
    (external : Fin T → probability_forecast K)
    (q : probability_forecast K) : ℝ :=
  ∑ t ∈ forecast_bin external q, roundExpectedLoss t

@[blueprint "def:has-binwise-expected-regret"
  (statement := /-- Let $\alpha:\mathbb{R}\to\mathbb{R}$.  A run has
  bin-wise expected regret bounded by $\alpha$ if, for every $q\in Q$,
  $L_q-C_q\leq\alpha(n_T(q))$.  This is the interface supplied by running
  an independent copy of the base learner on each forecast bin. -/)
  (title := /-- Per-forecast expected regret guarantee -/)
  (latexEnv := "definition")]
noncomputable def has_binwise_expected_regret {K T : ℕ}
    (loss : probability_forecast K → Fin K → ℝ)
    (external : Fin T → probability_forecast K)
    (outcome : Fin T → Fin K)
    (roundExpectedLoss : Fin T → ℝ)
    (alpha : ℝ → ℝ) : Prop :=
  ∀ q ∈ distinct_forecasts external,
    bin_expected_loss roundExpectedLoss external q -
        bin_comparator_loss loss external outcome q
      ≤ alpha (forecast_bin_size external q : ℝ)

@[blueprint "lem:binwise-reduction-has-binwise-expected-regret"
  (statement := /-- Let $K,T\in\mathbb{N}$, let
  $\ell:\Delta_K\times[K]\to\mathbb{R}$, let $\mathsf{A}$ be a randomized
  online probability forecaster, and let
  $\alpha:\mathbb{R}\to\mathbb{R}$.  Suppose that
  $p\mapsto\ell(p,z)$ is integrable with respect to
  $\mathsf{A}(h)$ for every finite outcome history $h$ and every $z\in[K]$,
  and that the expected regret of $\mathsf{A}$ on every finite outcome
  sequence of length $n$ is at most $\alpha(n)$.  Given
  $q:[T]\to\Delta_K$ and $y:[T]\to[K]$, set
  \[
    m_t=\overline\ell\bigl(
      \mathsf{A}((y_s:s<t,\ q_s=q_t)),y_t\bigr).
  \]
  Then, for every $q'$ in $Q=\{q_t:t\in[T]\}$,
  \[
    \sum_{t:q_t=q'}m_t
      -\inf_{p\in\Delta_K}\sum_{t:q_t=q'}\ell(p,y_t)
    \leq \alpha(n_T(q')).
  \] -/)
  (proof := /-- Fix $q'\in Q$ and list the indices of
  $I_{q'}=\{t:q_t=q'\}$ in increasing order as
  $t_0<\cdots<t_{n_T(q')-1}$.  By
  \cref{def:forecast-bin-outcome-history,
  def:randomized-forecast-expected-loss,
  def:binwise-reduction-round-expected-loss}, at round $t_j$ the copy
  $\mathsf{A}_{q'}$ has received precisely
  $(y_{t_0},\ldots,y_{t_{j-1}})$ and incurs conditional expected loss
  $\overline\ell(
  \mathsf{A}((y_{t_0},\ldots,y_{t_{j-1}})),y_{t_j})$.
  Consequently, the bin loss defined in
  \cref{def:bin-expected-loss} is the cumulative
  expected loss of $\mathsf{A}$ on the finite sequence
  $(y_{t_0},\ldots,y_{t_{n_T(q')-1}})$.

  Apply the assumed uniform regret inequality
  \cref{def:has-expected-regret-bound} to this sequence.  Its length is
  $n_T(q')$ by \cref{def:forecast-bin-size}, and reindexing the finite
  comparator sum along the increasing enumeration of $I_{q'}$ identifies
  its infimum with \cref{def:bin-comparator-loss}.  This gives the required
  inequality for $q'$.  Since $q'$ was arbitrary, the resulting run
  satisfies \cref{def:has-binwise-expected-regret}. -/)
  (title := /-- Independent copies inherit the base regret guarantee -/)
  (latexEnv := "lemma")]
lemma binwise_reduction_has_binwise_expected_regret {K T : ℕ}
    (loss : probability_forecast K → Fin K → ℝ)
    (learner : expected_loss_online_learner K)
    (alpha : ℝ → ℝ)
    (hregret : has_expected_regret_bound loss learner alpha)
    (external : Fin T → probability_forecast K)
    (outcome : Fin T → Fin K) :
    has_binwise_expected_regret loss external outcome
      (binwise_reduction_round_expected_loss loss learner external outcome)
      alpha := by
  classical
  rw [has_binwise_expected_regret]
  intro q hq
  let l := (forecast_bin external q).sort (· ≤ ·)
  have hmem (i : Fin l.length) (t : Fin T) :
      t ∈ l.take i ↔ t ∈ forecast_bin external q ∧ t < l.get i := by
    constructor
    · intro ht
      rw [List.mem_take_iff_getElem] at ht
      obtain ⟨j, hj, rfl⟩ := ht
      constructor
      · apply (Finset.mem_sort (s := forecast_bin external q)
          (r := (· ≤ ·))).mp
        exact List.get_mem l ⟨j, by omega⟩
      · exact
          (Finset.sortedLT_sort (forecast_bin external q)).getElem_lt_getElem_of_lt
            (by omega)
    · rintro ⟨ht, hlt⟩
      have htl : t ∈ l := by
        apply (Finset.mem_sort (s := forecast_bin external q)
          (r := (· ≤ ·))).2
        exact ht
      rw [List.mem_iff_getElem] at htl
      obtain ⟨j, hj, rfl⟩ := htl
      rw [List.mem_take_iff_getElem]
      refine ⟨j, ?_, rfl⟩
      have hji :=
        (Finset.sortedLT_sort
          (forecast_bin external q)).getElem_lt_getElem_iff.mp hlt
      omega
  have hindices (i : Fin l.length) :
      List.filterMap (fun j =>
        let s : Fin T := j.castLT (Nat.lt_trans j.2 (l.get i).2)
        if external s = external (l.get i) then some s else none)
        (List.finRange (l.get i).1) = l.take i := by
    have hcurmem : l.get i ∈ forecast_bin external q :=
      (Finset.mem_sort (s := forecast_bin external q)
        (r := (· ≤ ·))).mp (List.get_mem l i)
    have hcurrent : external (l.get i) = q := by
      simpa [forecast_bin] using hcurmem
    have hsleft :
        (List.filterMap (fun j =>
          let s : Fin T := j.castLT (Nat.lt_trans j.2 (l.get i).2)
          if external s = external (l.get i) then some s else none)
          (List.finRange (l.get i).1)).Pairwise (· < ·) := by
      apply List.Pairwise.filterMap _ _ (List.pairwise_lt_finRange _)
      intro a b hab x hax y hby
      dsimp only at hax hby
      by_cases ha :
          external (a.castLT (Nat.lt_trans a.2 (l.get i).2)) =
            external (l.get i)
      · rw [if_pos ha] at hax
        simp only [Option.some.injEq] at hax
        by_cases hb :
            external (b.castLT (Nat.lt_trans b.2 (l.get i).2)) =
              external (l.get i)
        · rw [if_pos hb] at hby
          simp only [Option.some.injEq] at hby
          subst x
          subst y
          change a.1 < b.1
          exact hab
        · rw [if_neg hb] at hby
          simp at hby
      · rw [if_neg ha] at hax
        simp at hax
    have hsright : (l.take i).Pairwise (· ≤ ·) := by
      exact List.Pairwise.take
        (Finset.pairwise_sort (s := forecast_bin external q) (r := (· ≤ ·)))
    apply List.Perm.eq_of_pairwise' (hsleft.imp fun h => le_of_lt h) hsright
    apply
      (List.perm_ext_iff_of_nodup hsleft.nodup
        (List.Pairwise.take (Finset.sort_nodup _ _))).2
    intro t
    rw [List.mem_filterMap]
    constructor
    · rintro ⟨a, ha, hsome⟩
      dsimp only at hsome
      by_cases he :
          external (a.castLT (Nat.lt_trans a.2 (l.get i).2)) =
            external (l.get i)
      · rw [if_pos he] at hsome
        simp only [Option.some.injEq] at hsome
        subst t
        apply (hmem i _).2
        constructor
        · simp only [forecast_bin, Finset.mem_filter, Finset.mem_univ, true_and]
          exact he.trans hcurrent
        · change a.1 < (l.get i).1
          exact a.2
      · rw [if_neg he] at hsome
        simp at hsome
    · intro ht
      have htq := (hmem i t).1 ht
      have htext : external t = q := by
        simpa [forecast_bin] using htq.1
      let a : Fin (l.get i).1 := ⟨t.1, htq.2⟩
      let s : Fin T := a.castLT (Nat.lt_trans a.2 (l.get i).2)
      have hst : s = t := by
        apply Fin.ext
        rfl
      refine ⟨a, List.mem_finRange a, ?_⟩
      dsimp only
      rw [if_pos]
      · exact congrArg some hst
      · change external s = external (l.get i)
        rw [hst, htext, hcurrent]
  have hhist (i : Fin l.length) :
      forecast_bin_outcome_history external outcome (l.get i) =
        (l.map outcome).take i := by
    unfold forecast_bin_outcome_history
    rw [← List.map_take, ← hindices i, List.map_filterMap]
    congr 1
    funext j
    dsimp only
    split <;> rfl
  have h := hregret.2 (l.map outcome)
  rw [sub_le_iff_le_add] at h ⊢
  simp only [bin_expected_loss, binwise_reduction_round_expected_loss,
    bin_comparator_loss, forecast_bin_size, learner_cumulative_expected_loss,
    List.length_map, Finset.length_sort] at h ⊢
  convert h using 1
  · symm
    refine Finset.sum_bij
      (fun i _ => l.get (Fin.cast (List.length_map (as := l) outcome) i)) ?_ ?_ ?_ ?_
    · intro i hi
      apply (Finset.mem_sort (s := forecast_bin external q)
        (r := (· ≤ ·))).mp
      exact List.get_mem l (Fin.cast (List.length_map (as := l) outcome) i)
    · intro i₁ hi₁ i₂ hi₂ heq
      exact
        Fin.cast_injective (List.length_map (as := l) outcome)
          ((Finset.sortedLT_sort (forecast_bin external q)).injective heq)
    · intro t ht
      have htl : t ∈ l :=
        (Finset.mem_sort (s := forecast_bin external q)
          (r := (· ≤ ·))).2 ht
      rw [List.mem_iff_get] at htl
      obtain ⟨i, hi⟩ := htl
      let j : Fin (l.map outcome).length :=
        Fin.cast (List.length_map (as := l) outcome).symm i
      exact ⟨j, Finset.mem_univ j, by simpa [j] using hi⟩
    · intro i hi
      rw [hhist]
      congr 2
      · simp
  · have hlencard : l.length = (forecast_bin external q).card := by
      simp [l]
    have hfun :
        (fun prediction : probability_forecast K =>
          ∑ i : Fin (l.map outcome).length,
            loss prediction ((l.map outcome).get i)) =
        (fun prediction : probability_forecast K =>
          ∑ t ∈ forecast_bin external q, loss prediction (outcome t)) := by
      funext prediction
      refine Finset.sum_bij
        (fun i _ => l.get (Fin.cast (List.length_map (as := l) outcome) i))
        ?_ ?_ ?_ ?_
      · intro i hi
        apply (Finset.mem_sort (s := forecast_bin external q)
          (r := (· ≤ ·))).mp
        exact List.get_mem l (Fin.cast (List.length_map (as := l) outcome) i)
      · intro i₁ hi₁ i₂ hi₂ heq
        exact
          Fin.cast_injective (List.length_map (as := l) outcome)
            ((Finset.sortedLT_sort (forecast_bin external q)).injective heq)
      · intro t ht
        have htl : t ∈ l :=
          (Finset.mem_sort (s := forecast_bin external q)
            (r := (· ≤ ·))).2 ht
        rw [List.mem_iff_get] at htl
        obtain ⟨i, hi⟩ := htl
        let j : Fin (l.map outcome).length :=
          Fin.cast (List.length_map (as := l) outcome).symm i
        exact ⟨j, Finset.mem_univ j, by simpa [j] using hi⟩
      · intro i hi
        simp
    rw [hlencard, hfun]

@[blueprint "def:is-expected-calibeating-at-rate"
  (statement := /-- Let $\ell:\Delta_K\times[K]\to\mathbb{R}$, let
  $\mathsf{A}$ be a randomized online probability forecaster, let
  $q:[T]\to\Delta_K$ be an external forecast sequence, and let
  $y:[T]\to[K]$ be an outcome sequence.  Run an independent copy
  $\mathsf{A}_q$ on each forecast bin, and let
  $m_t=\mathbb{E}[\ell(p_t,y_t)]$, where $p_t$ is sampled before observing
  $y_t$ from the distribution output by $\mathsf{A}_{q_t}$.  This
  prediction process is expected calibeating at rate $r$ if
  \[
    \sum_{t\in[T]}m_t\leq R_T(q_{1:T},y_{1:T})+r.
  \] -/)
  (title := /-- Expected calibeating of the binwise reduction -/)
  (latexEnv := "definition")]
noncomputable def is_expected_calibeating_at_rate {K T : ℕ}
    (loss : probability_forecast K → Fin K → ℝ)
    (learner : expected_loss_online_learner K)
    (external : Fin T → probability_forecast K)
    (outcome : Fin T → Fin K)
    (rate : ℝ) : Prop :=
  cumulative_expected_loss
      (binwise_reduction_round_expected_loss loss learner external outcome)
    ≤ refinement_score loss external outcome + rate

@[blueprint "lem:cumulative-expected-loss-eq-sum-bins"
  (statement := /-- Let $q:[T]\to\Delta_K$ be any external forecast
  sequence and let $m:[T]\to\mathbb{R}$.  Then
  $\sum_{t\in[T]}m_t=\sum_{q\in Q}\sum_{t\in I_q}m_t$. -/)
  (proof := /-- Every round $t\in[T]$ belongs to the fiber indexed by the
  unique value $q_t\in Q$.  The fibers $I_q$, for $q\in Q$, therefore form
  a disjoint partition of $[T]$.  Applying finite fiberwise summation to
  $t\mapsto q_t$ and the summand $m_t$, and then unfolding
  \cref{def:cumulative-expected-loss, def:bin-expected-loss,
  def:distinct-forecasts, def:forecast-bin}, gives the asserted equality. -/)
  (title := /-- Expected loss decomposes over forecast bins -/)
  (latexEnv := "lemma")]
lemma cumulative_expected_loss_eq_sum_bins {K T : ℕ}
    (external : Fin T → probability_forecast K)
    (roundExpectedLoss : Fin T → ℝ) :
    cumulative_expected_loss roundExpectedLoss =
      ∑ q ∈ distinct_forecasts external,
        bin_expected_loss roundExpectedLoss external q := by
  classical
  simpa [cumulative_expected_loss, distinct_forecasts, bin_expected_loss,
    forecast_bin] using
    (Finset.sum_fiberwise_eq_sum_filter (s := Finset.univ)
      (t := Finset.univ.image external) external roundExpectedLoss).symm

@[blueprint "lem:aggregate-binwise-expected-regret"
  (statement := /-- For all $K,T\in\mathbb{N}$, let
  $\ell:\Delta_K\times[K]\to\mathbb{R}$ be a loss, let
  $q:[T]\to\Delta_K$ and $y:[T]\to[K]$, let
  $m:[T]\to\mathbb{R}$, and let $\alpha:\mathbb{R}\to\mathbb{R}$.
  Set $Q=\{q_t:t\in[T]\}$, $I_r=\{t\in[T]:q_t=r\}$,
  $n_T(r)=|I_r|$, $L_r=\sum_{t\in I_r}m_t$, and
  $C_r=\inf_{p\in\Delta_K}\sum_{t\in I_r}\ell(p,y_t)$.  If
  $L_r-C_r\leq\alpha(n_T(r))$ for every $r\in Q$, then
  $\sum_{t\in[T]}m_t-\sum_{r\in Q}C_r\leq
  \sum_{r\in Q}\alpha(n_T(r))$. -/)
  (proof := /-- By \cref{def:has-binwise-expected-regret}, for every
  $r\in Q$ one has $L_r-C_r\leq\alpha(n_T(r))$.  Summing these
  inequalities over $Q$ gives
  $\sum_{r\in Q}(L_r-C_r)\leq\sum_{r\in Q}\alpha(n_T(r))$.
  Distributivity of finite sums over subtraction rewrites the left-hand
  side as $\sum_{r\in Q}L_r-\sum_{r\in Q}C_r$.
  By \cref{lem:cumulative-expected-loss-eq-sum-bins}, the first sum is
  the cumulative expected loss, while \cref{def:refinement-score}
  identifies the second sum with the refinement score.  Substitution
  yields the asserted inequality. -/)
  (title := /-- Aggregation of the per-bin regret inequalities -/)
  (latexEnv := "lemma")]
lemma aggregate_binwise_expected_regret {K T : ℕ}
    (loss : probability_forecast K → Fin K → ℝ)
    (external : Fin T → probability_forecast K)
    (outcome : Fin T → Fin K)
    (roundExpectedLoss : Fin T → ℝ)
    (alpha : ℝ → ℝ)
    (hregret : has_binwise_expected_regret loss external outcome
      roundExpectedLoss alpha) :
    cumulative_expected_loss roundExpectedLoss -
        refinement_score loss external outcome
      ≤ ∑ q ∈ distinct_forecasts external,
          alpha (forecast_bin_size external q : ℝ) := by
  rw [cumulative_expected_loss_eq_sum_bins external roundExpectedLoss,
    refinement_score, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun q hq => hregret q hq

@[blueprint "lem:sum-forecast-bin-sizes"
  (statement := /-- For all $K,T\in\mathbb{N}$ and every external forecast
  sequence $q:[T]\to\Delta_K$, let $Q=\{q_t:t\in[T]\}$ and
  $n_T(p)=|\{t\in[T]:q_t=p\}|$.  Then
  $\sum_{p\in Q}n_T(p)=T$. -/)
  (proof := /-- The sets $I_q$, indexed by the image
  $Q=\{q_t:t\in[T]\}$, are precisely the fibers of the map
  $t\mapsto q_t$.  The finite fiber-cardinality formula therefore gives
  $|[T]|=\sum_{q\in Q}|I_q|$.  Since $|[T]|=T$, unfolding
  \cref{def:forecast-bin-size, def:forecast-bin, def:distinct-forecasts}
  gives the stated identity. -/)
  (title := /-- The forecast-bin multiplicities sum to the horizon -/)
  (latexEnv := "lemma")]
lemma sum_forecast_bin_sizes {K T : ℕ}
    (external : Fin T → probability_forecast K) :
    (∑ q ∈ distinct_forecasts external,
      forecast_bin_size external q) = T := by
  classical
  simpa [distinct_forecasts, forecast_bin_size, forecast_bin] using
    (Finset.card_eq_sum_card_fiberwise (s := Finset.univ)
      (t := Finset.univ.image external) (f := external) (by simp)).symm

@[blueprint "lem:concave-sum-bin-regret-bounds"
  (statement := /-- For all $K,T\in\mathbb{N}$, every external forecast
  sequence $q:[T]\to\Delta_K$, and every function
  $\alpha:\mathbb{R}\to\mathbb{R}$ that is concave on $[0,\infty)$, let
  $Q=\{q_t:t\in[T]\}$ and
  $n_T(p)=|\{t\in[T]:q_t=p\}|$.  Then
  $\sum_{p\in Q}\alpha(n_T(p))\leq
  |Q|\alpha(T/|Q|)$. -/)
  (proof := /-- If $T=0$, then $Q$ is empty and both sides vanish.  Suppose
  $T>0$.  By \cref{lem:sum-forecast-bin-sizes}, the bin sizes sum to $T$;
  hence $Q$ is nonempty.  Assign weight $1/|Q|$ to each $p\in Q$.  These
  weights are nonnegative and sum to one, while every $n_T(p)$ lies in
  $[0,\infty)$.  Jensen's inequality for the concave function $\alpha$
  therefore yields
  $|Q|^{-1}\sum_{p\in Q}\alpha(n_T(p))\leq
  \alpha\!\left(|Q|^{-1}\sum_{p\in Q}n_T(p)\right)
  =\alpha(T/|Q|)$.  Multiplication by the positive number $|Q|$ gives the
  claimed inequality. -/)
  (title := /-- Jensen bound for the sum of bin-wise regret rates -/)
  (latexEnv := "lemma")]
lemma concave_sum_bin_regret_bounds {K T : ℕ}
    (external : Fin T → probability_forecast K)
    (alpha : ℝ → ℝ)
    (hconcave : ConcaveOn ℝ (Set.Ici 0) alpha) :
    (∑ q ∈ distinct_forecasts external,
      alpha (forecast_bin_size external q : ℝ))
      ≤ ((distinct_forecasts external).card : ℝ) *
        alpha ((T : ℝ) / ((distinct_forecasts external).card : ℝ)) := by
  classical
  by_cases hT : T = 0
  · subst T
    simp [distinct_forecasts]
  · have hcard_nat : (distinct_forecasts external).card ≠ 0 := by
      intro hcard
      have hempty : distinct_forecasts external = ∅ := Finset.card_eq_zero.mp hcard
      have hsum := sum_forecast_bin_sizes external
      rw [hempty] at hsum
      apply hT
      simpa using hsum.symm
    have hcard : ((distinct_forecasts external).card : ℝ) ≠ 0 := by
      exact_mod_cast hcard_nat
    have hcard_pos : 0 < ((distinct_forecasts external).card : ℝ) := by
      positivity
    have hj := hconcave.le_map_sum
      (t := distinct_forecasts external)
      (w := fun _ => ((distinct_forecasts external).card : ℝ)⁻¹)
      (p := fun q => (forecast_bin_size external q : ℝ))
      (by intro i hi; positivity)
      (by simp [hcard])
      (by intro i hi; exact Set.mem_Ici.mpr (Nat.cast_nonneg _))
    have hsum_real :
        (∑ q ∈ distinct_forecasts external,
          (forecast_bin_size external q : ℝ)) = (T : ℝ) := by
      exact_mod_cast sum_forecast_bin_sizes external
    have hj_base :
        ((distinct_forecasts external).card : ℝ)⁻¹ *
            (∑ q ∈ distinct_forecasts external,
              alpha (forecast_bin_size external q : ℝ))
          ≤ alpha (((distinct_forecasts external).card : ℝ)⁻¹ *
              (T : ℝ)) := by
      simpa only [smul_eq_mul, ← Finset.mul_sum, hsum_real] using hj
    have hj' :
        ((distinct_forecasts external).card : ℝ)⁻¹ *
            (∑ q ∈ distinct_forecasts external,
              alpha (forecast_bin_size external q : ℝ))
          ≤ alpha ((T : ℝ) /
              ((distinct_forecasts external).card : ℝ)) := by
      simpa only [div_eq_mul_inv, mul_comm] using hj_base
    calc
      (∑ q ∈ distinct_forecasts external,
          alpha (forecast_bin_size external q : ℝ)) =
          ((distinct_forecasts external).card : ℝ) *
            (((distinct_forecasts external).card : ℝ)⁻¹ *
              (∑ q ∈ distinct_forecasts external,
                alpha (forecast_bin_size external q : ℝ))) := by
            rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
      _ ≤ ((distinct_forecasts external).card : ℝ) *
          alpha ((T : ℝ) /
            ((distinct_forecasts external).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hj' hcard_pos.le

@[blueprint "thm:calibeating-from-no-regret-upper-bound"
  (statement := /-- Let $K,T\in\mathbb{N}$ with $K\geq2$, let $\ell$ be a
  proper scoring loss on $\Delta_K$, let $\mathsf{A}$ be a possibly
  randomized online learner which assigns a Borel probability measure on
  $\Delta_K$ to every finite outcome history, and let
  $\alpha:\mathbb{R}\to\mathbb{R}$.  Assume that every function
  $p\mapsto\ell(p,z)$ is integrable with respect to every conditional
  forecast distribution $\mathsf{A}(h)$, that the expected regret of
  $\mathsf{A}$ on every finite outcome sequence of length $n$ is at most
  $\alpha(n)$, and that $\alpha$ is concave on $[0,\infty)$.  Given
  arbitrary external forecasts $q_{1:T}$ and outcomes $y_{1:T}$, let
  $Q=\{q_t:t\in[T]\}$ and run an independent copy $\mathsf{A}_q$ on the
  rounds in each forecast bin.  If
  $m_t=\mathbb{E}[\ell(p_t,y_t)]$ is the expected round loss produced by
  the copy $\mathsf{A}_{q_t}$, then this reduction satisfies
  \[
    L_T\leq R_T(q_{1:T},y_{1:T})+
      |Q|\alpha\!\left(\frac{T}{|Q|}\right).
  \] -/)
  (proof := /-- By
  \cref{lem:binwise-reduction-has-binwise-expected-regret}, the uniform
  regret guarantee for $\mathsf{A}$ applies to the outcome subsequence in
  each forecast bin and supplies the bin-wise expected-regret interface for
  the explicit independent-copy reduction.  Hence
  \cref{lem:aggregate-binwise-expected-regret} gives
  $L_T-R_T\leq\sum_{q\in Q}\alpha(n_T(q))$.  By
  \cref{lem:concave-sum-bin-regret-bounds}, the latter sum is at most
  $|Q|\alpha(T/|Q|)$.  Combining these inequalities and moving $R_T$ to the
  right-hand side is exactly the calibeating inequality in
  \cref{def:is-expected-calibeating-at-rate}. -/)
  (title := /-- Calibeating from no-regret learning: upper-bound reduction -/)
  (latexEnv := "theorem")]
theorem calibeating_from_no_regret_upper_bound {K T : ℕ}
    (hK : 2 ≤ K)
    (loss : probability_forecast K → Fin K → ℝ)
    (hproper : is_proper_scoring_loss loss)
    (learner : expected_loss_online_learner K)
    (alpha : ℝ → ℝ)
    (hregret : has_expected_regret_bound loss learner alpha)
    (external : Fin T → probability_forecast K)
    (outcome : Fin T → Fin K)
    (hconcave : ConcaveOn ℝ (Set.Ici 0) alpha) :
    is_expected_calibeating_at_rate loss learner external outcome
      (((distinct_forecasts external).card : ℝ) *
        alpha ((T : ℝ) /
          ((distinct_forecasts external).card : ℝ))) := by
  rw [is_expected_calibeating_at_rate]
  have hbin :=
    binwise_reduction_has_binwise_expected_regret loss learner alpha hregret
      external outcome
  have hagg :=
    aggregate_binwise_expected_regret loss external outcome
      (binwise_reduction_round_expected_loss loss learner external outcome)
      alpha hbin
  have hsum := concave_sum_bin_regret_bounds external alpha hconcave
  linarith

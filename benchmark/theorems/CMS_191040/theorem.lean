import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

def probability_forecast (K : ℕ) : Type :=
  {p : Fin K → ℝ // p ∈ stdSimplex ℝ (Fin K)}

noncomputable instance probability_forecast_measurable_space (K : ℕ) :
    MeasurableSpace (probability_forecast K) :=
  (borel (Fin K → ℝ)).comap
    (fun prediction : probability_forecast K => prediction.1)

def expected_scoring_loss {K : ℕ}
    (loss : probability_forecast K → Fin K → ℝ)
    (prediction truth : probability_forecast K) : ℝ :=
  ∑ outcome, truth.1 outcome * loss prediction outcome

def is_proper_scoring_loss {K : ℕ}
    (loss : probability_forecast K → Fin K → ℝ) : Prop :=
  ∀ prediction truth : probability_forecast K,
    expected_scoring_loss loss truth truth ≤
      expected_scoring_loss loss prediction truth

noncomputable def distinct_forecasts {K T : ℕ}
    (external : Fin T → probability_forecast K) :
    Finset (probability_forecast K) := by
  classical
  exact Finset.univ.image external

noncomputable def forecast_bin {K T : ℕ}
    (external : Fin T → probability_forecast K)
    (q : probability_forecast K) : Finset (Fin T) := by
  classical
  exact Finset.univ.filter (fun t => external t = q)

noncomputable def bin_comparator_loss {K T : ℕ}
    (loss : probability_forecast K → Fin K → ℝ)
    (external : Fin T → probability_forecast K)
    (outcome : Fin T → Fin K)
    (q : probability_forecast K) : ℝ :=
  sInf (Set.range (fun prediction : probability_forecast K =>
    ∑ t ∈ forecast_bin external q, loss prediction (outcome t)))

noncomputable def refinement_score {K T : ℕ}
    (loss : probability_forecast K → Fin K → ℝ)
    (external : Fin T → probability_forecast K)
    (outcome : Fin T → Fin K) : ℝ :=
  ∑ q ∈ distinct_forecasts external,
    bin_comparator_loss loss external outcome q

def cumulative_expected_loss {T : ℕ}
    (roundExpectedLoss : Fin T → ℝ) : ℝ :=
  ∑ t, roundExpectedLoss t

def expected_loss_online_learner (K : ℕ) : Type :=
  List (Fin K) →
    MeasureTheory.ProbabilityMeasure (probability_forecast K)

noncomputable def randomized_forecast_expected_loss {K : ℕ}
    (loss : probability_forecast K → Fin K → ℝ)
    (distribution :
      MeasureTheory.ProbabilityMeasure (probability_forecast K))
    (outcome : Fin K) : ℝ :=
  MeasureTheory.integral distribution.toMeasure
    (fun prediction => loss prediction outcome)

noncomputable def learner_cumulative_expected_loss {K : ℕ}
    (loss : probability_forecast K → Fin K → ℝ)
    (learner : expected_loss_online_learner K)
    (outcomes : List (Fin K)) : ℝ :=
  ∑ i : Fin outcomes.length,
    randomized_forecast_expected_loss loss
      (learner (outcomes.take i.1)) (outcomes.get i)

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

noncomputable def forecast_bin_outcome_history {K T : ℕ}
    (external : Fin T → probability_forecast K)
    (outcome : Fin T → Fin K)
    (t : Fin T) : List (Fin K) :=
  letI := Classical.decEq (probability_forecast K)
  (List.finRange t.1).filterMap (fun i =>
    let s : Fin T := i.castLT (Nat.lt_trans i.2 t.2)
    if external s = external t then some (outcome s) else none)

noncomputable def binwise_reduction_round_expected_loss {K T : ℕ}
    (loss : probability_forecast K → Fin K → ℝ)
    (learner : expected_loss_online_learner K)
    (external : Fin T → probability_forecast K)
    (outcome : Fin T → Fin K)
    (t : Fin T) : ℝ :=
  randomized_forecast_expected_loss loss
    (learner (forecast_bin_outcome_history external outcome t)) (outcome t)

noncomputable def is_expected_calibeating_at_rate {K T : ℕ}
    (loss : probability_forecast K → Fin K → ℝ)
    (learner : expected_loss_online_learner K)
    (external : Fin T → probability_forecast K)
    (outcome : Fin T → Fin K)
    (rate : ℝ) : Prop :=
  cumulative_expected_loss
      (binwise_reduction_round_expected_loss loss learner external outcome)
    ≤ refinement_score loss external outcome + rate

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
          ((distinct_forecasts external).card : ℝ))) := by sorry

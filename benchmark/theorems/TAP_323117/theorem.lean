import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

set_option linter.all false

structure canonical_conversation where
  horizon : ℕ
  horizon_pos : 0 < horizon
  label : Fin horizon → ℝ
  prediction : ℕ → Fin horizon → ℝ
  length : Fin horizon → ℕ
  label_mem : ∀ t, label t ∈ Set.Icc (0 : ℝ) 1
  prediction_mem : ∀ k t, prediction k t ∈ Set.Icc (0 : ℝ) 1

def round_subsequence (conversation : canonical_conversation) (k : ℕ) :
    Finset (Fin conversation.horizon) :=
  Finset.univ.filter fun t => k ≤ conversation.length t

def squared_error (conversation : canonical_conversation)
    (days : Finset (Fin conversation.horizon))
    (predictor : Fin conversation.horizon → ℝ) : ℝ :=
  ∑ t ∈ days, (predictor t - conversation.label t) ^ 2

noncomputable def bucket_index (width x : ℝ) : ℕ :=
  min ⌈width⁻¹⌉₊ (max 1 ⌈x / width⌉₊)

noncomputable def bucketed_round_prediction (conversation : canonical_conversation)
    (width : ℝ) (k : ℕ) (t : Fin conversation.horizon) : ℝ :=
  (bucket_index width
    (conversation.prediction (min k (conversation.length t)) t) : ℝ) * width

noncomputable def human_bucketed_round_prediction
    (conversation : canonical_conversation) (humanWidth : ℕ → ℝ)
    (k : ℕ) (t : Fin conversation.horizon) : ℝ :=
  bucketed_round_prediction conversation
    (humanWidth conversation.horizon) (k - k % 2) t

noncomputable def prediction_fiber (conversation : canonical_conversation)
    (days : Finset (Fin conversation.horizon))
    (predictor : Fin conversation.horizon → ℝ) (value : ℝ) :
    Finset (Fin conversation.horizon) := by
  classical
  exact days.filter fun t => predictor t = value

def perfectly_calibrated (conversation : canonical_conversation)
    (days : Finset (Fin conversation.horizon))
    (predictor : Fin conversation.horizon → ℝ) : Prop :=
  ∀ value : ℝ,
    (∑ t ∈ prediction_fiber conversation days predictor value,
      conversation.label t) =
      value * (prediction_fiber conversation days predictor value).card

noncomputable def previous_round_bucket_days (conversation : canonical_conversation)
    (width : ℝ) (k i : ℕ) : Finset (Fin conversation.horizon) := by
  classical
  exact (round_subsequence conversation k).filter fun t =>
    bucket_index width (conversation.prediction (k - 1) t) = i

def party_round (human : Bool) (k : ℕ) : Prop :=
  (human = true ∧ k % 2 = 0) ∨ (human = false ∧ k % 2 = 1)

def calibration_error_function (error : ℝ → ℝ) : Prop :=
  ConcaveOn ℝ (Set.Ici (0 : ℝ)) error ∧
  MonotoneOn error (Set.Ici (0 : ℝ))

def conversation_calibrated (conversation : canonical_conversation) (human : Bool)
    (error : ℝ → ℝ) (width : ℕ → ℝ) : Prop :=
  calibration_error_function error ∧
  0 < width conversation.horizon ∧
  width conversation.horizon ≤ 1 ∧
  (∃ bucketCount : ℕ, 1 ≤ bucketCount ∧
    width conversation.horizon = (bucketCount : ℝ)⁻¹) ∧
  ∀ k : ℕ, party_round human k →
    ∀ i : ℕ, 1 ≤ i → i ≤ ⌈(width conversation.horizon)⁻¹⌉₊ →
      ∃ calibrated : Fin conversation.horizon → ℝ,
        (∀ t ∈ previous_round_bucket_days conversation
            (width conversation.horizon) k i,
          calibrated t ∈ Set.Icc (0 : ℝ) 1) ∧
        perfectly_calibrated conversation
          (previous_round_bucket_days conversation
            (width conversation.horizon) k i) calibrated ∧
        (∑ t ∈ previous_round_bucket_days conversation
            (width conversation.horizon) k i,
          |conversation.prediction k t - calibrated t|) ≤
          error ((previous_round_bucket_days conversation
            (width conversation.horizon) k i).card : ℝ)

def epsilon_agreement_run (conversation : canonical_conversation)
    (epsilon : ℝ) : Prop :=
  (∀ t, 1 ≤ conversation.length t) ∧
  ∀ t,
    |conversation.prediction (conversation.length t) t -
      conversation.prediction (conversation.length t - 1) t| < epsilon ∧
    ∀ k, 1 ≤ k → k < conversation.length t →
      epsilon ≤ |conversation.prediction k t -
        conversation.prediction (k - 1) t|

noncomputable def agreement_by_round (conversation : canonical_conversation)
    (K delta : ℝ) : Prop := by
  classical
  exact ((Finset.univ.filter fun t : Fin conversation.horizon =>
    (conversation.length t : ℝ) ≤ K).card : ℝ) ≥
      (1 - delta) * conversation.horizon

noncomputable def beta_error (conversation : canonical_conversation)
    (humanError modelError : ℝ → ℝ)
    (humanWidth modelWidth : ℕ → ℝ) : ℝ :=
  3 * (modelWidth conversation.horizon + humanWidth conversation.horizon +
    modelError (modelWidth conversation.horizon * conversation.horizon) /
      (modelWidth conversation.horizon * conversation.horizon) +
    humanError (humanWidth conversation.horizon * conversation.horizon) /
      (humanWidth conversation.horizon * conversation.horizon))

theorem canonical
    (conversation : canonical_conversation)
    (humanError modelError : ℝ → ℝ)
    (humanWidth modelWidth : ℕ → ℝ)
    (epsilon delta : ℝ)
    (hepsilon : epsilon ∈ Set.Icc (0 : ℝ) 1)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) 1)
    (hhuman :
      conversation_calibrated conversation true humanError humanWidth)
    (hmodel :
      conversation_calibrated conversation false modelError modelWidth)
    (hrun : epsilon_agreement_run conversation epsilon) :
    (0 < epsilon ^ 2 * delta -
        beta_error conversation humanError modelError
          humanWidth modelWidth →
      ∃ K : ℝ,
        K ≤ 1 / (epsilon ^ 2 * delta -
          beta_error conversation humanError modelError
            humanWidth modelWidth) ∧
        agreement_by_round conversation K delta) ∧
    ∀ k : ℕ,
      2 ≤ k →
      k % 2 = 0 →
      delta * conversation.horizon ≤
        (round_subsequence conversation k).card →
      squared_error conversation Finset.univ
          (human_bucketed_round_prediction conversation
            humanWidth k) /
          conversation.horizon ≤
        min
          (squared_error conversation Finset.univ
                (bucketed_round_prediction conversation
                  (modelWidth conversation.horizon) 1) /
              conversation.horizon)
          (squared_error conversation Finset.univ
                (bucketed_round_prediction conversation
                  (humanWidth conversation.horizon) 2) /
              conversation.horizon) -
        (k : ℝ) * (epsilon ^ 2 * delta -
          beta_error conversation humanError modelError
            humanWidth modelWidth) := by sorry

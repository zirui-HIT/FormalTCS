import Architect
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:canonical-conversation"
  (statement := /-- A canonical conversation over a positive number \(T\) of days consists of labels \(y^t\in[0,1]\), a prediction transcript \(p^{t,k}\in[0,1]\), and a conversation length \(\ell^t\) for every day. The transcript records the Model at positive odd rounds and the Human at even rounds, including the Human's initial round \(0\). -/)
  (title := /-- Canonical conversation -/)
  (latexEnv := "definition")]
structure canonical_conversation where
  horizon : ℕ
  horizon_pos : 0 < horizon
  label : Fin horizon → ℝ
  prediction : ℕ → Fin horizon → ℝ
  length : Fin horizon → ℕ
  label_mem : ∀ t, label t ∈ Set.Icc (0 : ℝ) 1
  prediction_mem : ∀ k t, prediction k t ∈ Set.Icc (0 : ℝ) 1

@[blueprint "def:round-subsequence"
  (statement := /-- For a canonical conversation and a round \(k\), the round subsequence \(T^{\geq k}\) is the set of days \(t\) for which \(\ell^t\geq k\). -/)
  (title := /-- Round subsequence -/)
  (latexEnv := "definition")]
def round_subsequence (conversation : canonical_conversation) (k : ℕ) :
    Finset (Fin conversation.horizon) :=
  Finset.univ.filter fun t => k ≤ conversation.length t

@[blueprint "def:squared-error"
  (statement := /-- For a finite set \(S\) of days and a predictor \(p\), define
  \[
  \operatorname{SQErr}_S(p,y)=\sum_{t\in S}(p^t-y^t)^2.
  \] -/)
  (title := /-- Squared error -/)
  (latexEnv := "definition")]
def squared_error (conversation : canonical_conversation)
    (days : Finset (Fin conversation.horizon))
    (predictor : Fin conversation.horizon → ℝ) : ℝ :=
  ∑ t ∈ days, (predictor t - conversation.label t) ^ 2

@[blueprint "def:bucket-index"
  (statement := /-- For a width \(g>0\) and \(x\in[0,1]\), the bucket index is the positive ceiling index containing \(x\), truncated at \(\lceil g^{-1}\rceil\). This realizes the half-open width-\(g\) buckets with a closed final bucket. -/)
  (title := /-- Bucket index -/)
  (latexEnv := "definition")]
noncomputable def bucket_index (width x : ℝ) : ℕ :=
  min ⌈width⁻¹⌉₊ (max 1 ⌈x / width⌉₊)

@[blueprint "def:bucketed-round-prediction"
  (statement := /-- The width-\(g\) bucketed prediction at round \(k\) is the upper endpoint of the bucket containing the transcript prediction at round \(\min\{k,\ell^t\}\). Thus the sequence is frozen at the terminal prediction on every conversation ending before round \(k\). -/)
  (title := /-- Bucketed round prediction -/)
  (latexEnv := "definition")]
noncomputable def bucketed_round_prediction (conversation : canonical_conversation)
    (width : ℝ) (k : ℕ) (t : Fin conversation.horizon) : ℝ :=
  (bucket_index width
    (conversation.prediction (min k (conversation.length t)) t) : ℝ) * width

@[blueprint "def:party-aware-round-prediction"
  (statement := /-- Let \(g_h,g_m\colon\mathbb N\to\mathbb R\) be the Human and Model bucketing functions. The party-aware bucketed prediction at round \(k\) is obtained from \cref{def:bucketed-round-prediction} with width \(g_h(T)\) when \(k\) is even and width \(g_m(T)\) when \(k\) is odd. Thus it records the speaking party's prediction on active days and remains frozen at the terminal prediction on days whose conversations have already ended. -/)
  (title := /-- Party-aware bucketed round prediction -/)
  (latexEnv := "definition")]
noncomputable def party_aware_round_prediction
    (conversation : canonical_conversation)
    (humanWidth modelWidth : ℕ → ℝ)
    (k : ℕ) (t : Fin conversation.horizon) : ℝ :=
  bucketed_round_prediction conversation
    (if k % 2 = 0 then humanWidth conversation.horizon
      else modelWidth conversation.horizon) k t

@[blueprint "def:human-bucketed-round-prediction"
  (statement := /-- Let \(g_h\colon\mathbb N\to\mathbb R\) be the Human bucketing function. The Human's bucketed prediction at transcript round \(k\) is the width-\(g_h(T)\) bucketed prediction at the most recent even round, namely \(k-(k\bmod 2)\). Thus the Human prediction is carried unchanged through each intervening odd Model round, while on a day whose conversation has already terminated it remains frozen at the terminal prediction as in \cref{def:bucketed-round-prediction}. -/)
  (title := /-- Human bucketed prediction at every round -/)
  (latexEnv := "definition")]
noncomputable def human_bucketed_round_prediction
    (conversation : canonical_conversation) (humanWidth : ℕ → ℝ)
    (k : ℕ) (t : Fin conversation.horizon) : ℝ :=
  bucketed_round_prediction conversation
    (humanWidth conversation.horizon) (k - k % 2) t

@[blueprint "def:prediction-fiber"
  (statement := /-- Given a finite set \(S\), a predictor \(p\), and a value \(a\), the prediction fiber \(S_{p=a}\) consists of the days in \(S\) on which \(p^t=a\). -/)
  (title := /-- Prediction fiber -/)
  (latexEnv := "definition")]
noncomputable def prediction_fiber (conversation : canonical_conversation)
    (days : Finset (Fin conversation.horizon))
    (predictor : Fin conversation.horizon → ℝ) (value : ℝ) :
    Finset (Fin conversation.horizon) := by
  classical
  exact days.filter fun t => predictor t = value

@[blueprint "def:perfectly-calibrated"
  (statement := /-- A predictor \(p\) is perfectly calibrated on \(S\) if, for every value \(a\), the sum of the labels on \(S_{p=a}\) equals \(a\) times the cardinality of that fiber. -/)
  (title := /-- Perfect calibration -/)
  (latexEnv := "definition")]
def perfectly_calibrated (conversation : canonical_conversation)
    (days : Finset (Fin conversation.horizon))
    (predictor : Fin conversation.horizon → ℝ) : Prop :=
  ∀ value : ℝ,
    (∑ t ∈ prediction_fiber conversation days predictor value,
      conversation.label t) =
      value * (prediction_fiber conversation days predictor value).card

@[blueprint "def:calibration-distance"
  (statement := /-- The distance to calibration of \(p\) on \(S\) is the infimum of its \(\ell^1\)-distance from all \([0,1]\)-valued predictors that are perfectly calibrated on \(S\). -/)
  (title := /-- Distance to calibration -/)
  (latexEnv := "definition")]
noncomputable def calibration_distance (conversation : canonical_conversation)
    (days : Finset (Fin conversation.horizon))
    (predictor : Fin conversation.horizon → ℝ) : ℝ :=
  sInf {distance : ℝ | ∃ calibrated : Fin conversation.horizon → ℝ,
    (∀ t ∈ days, calibrated t ∈ Set.Icc (0 : ℝ) 1) ∧
    perfectly_calibrated conversation days calibrated ∧
    distance = ∑ t ∈ days, |predictor t - calibrated t|}

@[blueprint "def:previous-round-bucket-days"
  (statement := /-- For round \(k\), width \(g\), and bucket \(i\), let \(T(k,i)\) be the days reaching round \(k\) whose round-\((k-1)\) prediction belongs to bucket \(i\). -/)
  (title := /-- Previous-round bucket days -/)
  (latexEnv := "definition")]
noncomputable def previous_round_bucket_days (conversation : canonical_conversation)
    (width : ℝ) (k i : ℕ) : Finset (Fin conversation.horizon) := by
  classical
  exact (round_subsequence conversation k).filter fun t =>
    bucket_index width (conversation.prediction (k - 1) t) = i

@[blueprint "def:party-round"
  (statement := /-- A round belongs to the Human when it is even and to the Model when it is odd. -/)
  (title := /-- Party assigned to a round -/)
  (latexEnv := "definition")]
def party_round (human : Bool) (k : ℕ) : Prop :=
  (human = true ∧ k % 2 = 0) ∨ (human = false ∧ k % 2 = 1)

@[blueprint "def:calibration-error-function"
  (statement := /-- A calibration-error function is a function (f\colon\mathbb R\to\mathbb R) that is concave and nondecreasing on ([0,\infty)). -/)
  (title := /-- Calibration-error function -/)
  (latexEnv := "definition")]
def calibration_error_function (error : ℝ → ℝ) : Prop :=
  ConcaveOn ℝ (Set.Ici (0 : ℝ)) error ∧
  MonotoneOn error (Set.Ici (0 : ℝ))

@[blueprint "def:conversation-calibrated"
  (statement := /-- Let \(f\colon\mathbb R\to\mathbb R\) be a calibration-error function in the sense of \cref{def:calibration-error-function}, and let \(g\colon\mathbb N\to\mathbb R\) be a bucketing function. A party is \((f,g)\)-conversation-calibrated if \(g(T)\in(0,1]\) is the reciprocal of a positive integer and, at every round belonging to that party and in every previous-round bucket, its prediction admits a \([0,1]\)-valued perfectly calibrated surrogate at \(\ell^1\)-distance at most \(f\) of the bucket cardinality. -/)
  (title := /-- Conversation calibration -/)
  (latexEnv := "definition")]
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

@[blueprint "def:perfectly-conversation-calibrated"
  (statement := /-- A party is perfectly conversation-calibrated at width \(g\) if \(g(T)\in(0,1]\) is the reciprocal of a positive integer and its prediction is perfectly calibrated on every previous-round bucket at every round belonging to that party. -/)
  (title := /-- Perfect conversation calibration -/)
  (latexEnv := "definition")]
def perfectly_conversation_calibrated (conversation : canonical_conversation)
    (human : Bool) (width : ℕ → ℝ) : Prop :=
  0 < width conversation.horizon ∧
  width conversation.horizon ≤ 1 ∧
  (∃ bucketCount : ℕ, 1 ≤ bucketCount ∧
    width conversation.horizon = (bucketCount : ℝ)⁻¹) ∧
  ∀ k : ℕ, party_round human k →
    ∀ i : ℕ, 1 ≤ i → i ≤ ⌈(width conversation.horizon)⁻¹⌉₊ →
      perfectly_calibrated conversation
        (previous_round_bucket_days conversation
          (width conversation.horizon) k i)
        (conversation.prediction k)

@[blueprint "def:epsilon-agreement-run"
  (statement := /-- A canonical conversation is an \(\epsilon\)-agreement run if every day has at least one round, the two consecutive predictions at its terminal round differ by less than \(\epsilon\), and at every earlier positive round they differ by at least \(\epsilon\). -/)
  (title := /-- Canonical epsilon-agreement run -/)
  (latexEnv := "definition")]
def epsilon_agreement_run (conversation : canonical_conversation)
    (epsilon : ℝ) : Prop :=
  (∀ t, 1 ≤ conversation.length t) ∧
  ∀ t,
    |conversation.prediction (conversation.length t) t -
      conversation.prediction (conversation.length t - 1) t| < epsilon ∧
    ∀ k, 1 ≤ k → k < conversation.length t →
      epsilon ≤ |conversation.prediction k t -
        conversation.prediction (k - 1) t|

@[blueprint "def:agreement-by-round"
  (statement := /-- Agreement is reached by round \(K\) on a \(1-\delta\) fraction of days if at least \((1-\delta)T\) days have conversation length at most \(K\). -/)
  (title := /-- Agreement by a prescribed round -/)
  (latexEnv := "definition")]
noncomputable def agreement_by_round (conversation : canonical_conversation)
    (K delta : ℝ) : Prop := by
  classical
  exact ((Finset.univ.filter fun t : Fin conversation.horizon =>
    (conversation.length t : ℝ) ≤ K).card : ℝ) ≥
      (1 - delta) * conversation.horizon

@[blueprint "def:beta-error"
  (statement := /-- The accumulated calibration and bucketing error is
  \[
  \beta(T)=3\left(g_m(T)+g_h(T)+
  \frac{f_m(g_m(T)T)}{g_m(T)T}+
  \frac{f_h(g_h(T)T)}{g_h(T)T}\right).
  \] -/)
  (title := /-- Accumulated calibration error -/)
  (latexEnv := "definition")]
noncomputable def beta_error (conversation : canonical_conversation)
    (humanError modelError : ℝ → ℝ)
    (humanWidth modelWidth : ℕ → ℝ) : ℝ :=
  3 * (modelWidth conversation.horizon + humanWidth conversation.horizon +
    modelError (modelWidth conversation.horizon * conversation.horizon) /
      (modelWidth conversation.horizon * conversation.horizon) +
    humanError (humanWidth conversation.horizon * conversation.horizon) /
      (humanWidth conversation.horizon * conversation.horizon))

@[blueprint "lem:squared-error-nonnegative"
  (statement := /-- For every canonical conversation \(C\), every finite set \(S\subseteq \operatorname{Fin}(C.\mathrm{horizon})\) of days, and every predictor \(p\colon \operatorname{Fin}(C.\mathrm{horizon})\to\mathbb{R}\), one has \(\operatorname{SQErr}_S(p,C.\mathrm{label})\geq 0\). -/)
  (proof := /-- Every summand in \cref{def:squared-error} is a square and hence nonnegative. A finite sum of nonnegative real numbers is nonnegative. -/)
  (title := /-- Nonnegativity of squared error -/)
  (latexEnv := "lemma")]
lemma squared_error_nonnegative (conversation : canonical_conversation)
    (days : Finset (Fin conversation.horizon))
    (predictor : Fin conversation.horizon → ℝ) :
    0 ≤ squared_error conversation days predictor := by
  unfold squared_error
  exact Finset.sum_nonneg fun t ht =>
    sq_nonneg (predictor t - conversation.label t)

@[blueprint "lem:squared-error-at-most-cardinality"
  (statement := /-- For every canonical conversation with \(T\) days, every finite set \(S\) of its days, and every predictor \(p\colon\{0,\ldots,T-1\}\to\mathbb R\) satisfying \(p^t\in[0,1]\) for every \(t\in S\), one has \(\operatorname{SQErr}_S(p,y)\leq |S|\). -/)
  (proof := /-- Fix \(t\in S\). The label-range field of \cref{def:canonical-conversation} and the predictor hypothesis imply that both \(1-(p^t-y^t)\) and \(1+(p^t-y^t)\) are nonnegative. Their product is \(1-(p^t-y^t)^2\), so \((p^t-y^t)^2\leq1\). Applying this estimate termwise to the sum in \cref{def:squared-error} yields \(\operatorname{SQErr}_S(p,y)\leq\sum_{t\in S}1=|S|\). -/)
  (title := /-- Squared error is at most the number of selected days -/)
  (latexEnv := "lemma")]
lemma squared_error_at_most_cardinality
    (conversation : canonical_conversation)
    (days : Finset (Fin conversation.horizon))
    (predictor : Fin conversation.horizon → ℝ)
    (hpredictor : ∀ t ∈ days, predictor t ∈ Set.Icc (0 : ℝ) 1) :
    squared_error conversation days predictor ≤ days.card := by
  simp only [squared_error]
  calc
    ∑ t ∈ days, (predictor t - conversation.label t) ^ 2 ≤
        ∑ t ∈ days, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      rcases hpredictor t ht with ⟨hp0, hp1⟩
      rcases conversation.label_mem t with ⟨hy0, hy1⟩
      nlinarith [mul_nonneg
        (show 0 ≤ 1 - (predictor t - conversation.label t) by linarith)
        (show 0 ≤ 1 + (predictor t - conversation.label t) by linarith)]
    _ = days.card := by simp

@[blueprint "lem:calibrated-squared-error-perturbation"
  (statement := /-- Let \(C\) be a canonical conversation with horizon \(T\), let \(S\) be a finite set of elements of \(\operatorname{Fin}(T)\), let \(p,q\colon \operatorname{Fin}(T)\to\mathbb R\), and let \(\gamma\in\mathbb R\). Suppose that \(p^t,q^t\in[0,1]\) for every \(t\in S\), that \(p\) is perfectly calibrated on \(S\), and that
  \[
  \sum_{t\in S}|q^t-p^t|\leq\gamma.
  \]
  Then
  \[
  \operatorname{SQErr}_S(q,y)-\operatorname{SQErr}_S(p,y)\leq3\gamma.
  \] -/)
  (proof := /-- By \cref{def:squared-error}, the difference of the squared errors is the sum over \(t\in S\) of
  \[
  (q^t-y^t)^2-(p^t-y^t)^2=(q^t-p^t)(q^t+p^t-2y^t).
  \]
  The range hypotheses for \(p^t\), \(q^t\), and \(y^t\) imply \(-2\leq q^t+p^t-2y^t\leq2\). Consequently, each summand is at most \(2|q^t-p^t|\), and summing gives an upper bound of \(2\gamma\). The sum of the absolute differences is nonnegative and at most \(\gamma\), so \(\gamma\geq0\); hence \(2\gamma\leq3\gamma\), as required. -/)
  (title := /-- Squared-error stability under calibration perturbation -/)
  (latexEnv := "lemma")]
lemma calibrated_squared_error_perturbation
    (conversation : canonical_conversation)
    (days : Finset (Fin conversation.horizon))
    (perfect approximate : Fin conversation.horizon → ℝ) (gamma : ℝ)
    (hperfectRange : ∀ t ∈ days, perfect t ∈ Set.Icc (0 : ℝ) 1)
    (happroximateRange : ∀ t ∈ days,
      approximate t ∈ Set.Icc (0 : ℝ) 1)
    (hperfect : perfectly_calibrated conversation days perfect)
    (hclose : (∑ t ∈ days, |approximate t - perfect t|) ≤ gamma) :
    squared_error conversation days approximate -
      squared_error conversation days perfect ≤ 3 * gamma := by
  unfold squared_error
  have hgamma : 0 ≤ gamma := by
    calc
      0 ≤ ∑ t ∈ days, |approximate t - perfect t| := by
        exact Finset.sum_nonneg fun t _ => abs_nonneg _
      _ ≤ gamma := hclose
  calc
    (∑ t ∈ days, (approximate t - conversation.label t) ^ 2) -
          ∑ t ∈ days, (perfect t - conversation.label t) ^ 2 =
        ∑ t ∈ days, ((approximate t - conversation.label t) ^ 2 -
          (perfect t - conversation.label t) ^ 2) := by
            rw [Finset.sum_sub_distrib]
    _ ≤ ∑ t ∈ days, 2 * |approximate t - perfect t| := by
      apply Finset.sum_le_sum
      intro t ht
      have hp := hperfectRange t ht
      have hq := happroximateRange t ht
      have hy := conversation.label_mem t
      by_cases h : perfect t ≤ approximate t
      · rw [abs_of_nonneg (sub_nonneg.mpr h)]
        have hnonneg : 0 ≤ (approximate t - perfect t) *
            (2 - (approximate t + perfect t - 2 * conversation.label t)) := by
          exact mul_nonneg (sub_nonneg.mpr h) (by linarith [hq.2, hp.2, hy.1])
        nlinarith [hnonneg]
      · have hle : approximate t ≤ perfect t := le_of_not_ge h
        rw [abs_of_nonpos (sub_nonpos.mpr hle)]
        have hnonneg : 0 ≤ (perfect t - approximate t) *
            (2 + (approximate t + perfect t - 2 * conversation.label t)) := by
          exact mul_nonneg (sub_nonneg.mpr hle) (by linarith [hq.1, hp.1, hy.2])
        nlinarith [hnonneg]
    _ = 2 * ∑ t ∈ days, |approximate t - perfect t| := by
      rw [Finset.mul_sum]
    _ ≤ 3 * gamma := by nlinarith [hclose]

@[blueprint "lem:bucket-surrogates-stitch"
  (statement := /-- Let \(S=T^{\geq k}\), let \(n\geq1\), and suppose that \(\lceil w^{-1}\rceil=n\). Suppose further that, for every \(i\in\{1,\ldots,n\}\), a predictor \(q_i\) takes values in \([0,1]\) on the previous-round bucket \(T(k,i)\), is perfectly calibrated there, and has round-\(k\) prediction distance at most \(E_i\). Then there is a predictor \(q\) which takes values in \([0,1]\) on \(S\), is perfectly calibrated on \(S\), and has total distance at most \(\sum_{i=1}^n E_i\). -/)
  (proof := /-- By \cref{def:bucket-index}, every day has a unique bucket index in \(\{1,\ldots,n\}\). Define \(q\) on each bucket to equal its supplied predictor. The bucket sets from \cref{def:previous-round-bucket-days} partition \(S\). Hence the range and distance claims follow bucket by bucket. For each value \(a\), partition the \(a\)-fiber of \(q\) by bucket; the perfect-calibration identity from \cref{def:perfectly-calibrated} holds on each part, and summing those identities proves perfect calibration on \(S\). -/)
  (title := /-- Stitch bucketwise calibrated surrogates -/)
  (latexEnv := "lemma")]
lemma bucket_surrogates_stitch
    (conversation : canonical_conversation) (width : ℝ) (k n : ℕ)
    (bounds : ℕ → ℝ) (hn : 1 ≤ n)
    (hceil : Nat.ceil width⁻¹ = n)
    (hlocal : ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ∃ calibrated : Fin conversation.horizon → ℝ,
        (∀ t ∈ previous_round_bucket_days conversation width k i,
          calibrated t ∈ Set.Icc (0 : ℝ) 1) ∧
        perfectly_calibrated conversation
          (previous_round_bucket_days conversation width k i) calibrated ∧
        (∑ t ∈ previous_round_bucket_days conversation width k i,
          |conversation.prediction k t - calibrated t|) ≤ bounds i) :
    ∃ calibrated : Fin conversation.horizon → ℝ,
      (∀ t ∈ round_subsequence conversation k,
        calibrated t ∈ Set.Icc (0 : ℝ) 1) ∧
      perfectly_calibrated conversation
        (round_subsequence conversation k) calibrated ∧
      (∑ t ∈ round_subsequence conversation k,
        |conversation.prediction k t - calibrated t|) ≤
        ∑ i ∈ Finset.Icc 1 n, bounds i := by
  classical
  let localPredictor (i : ℕ) : Fin conversation.horizon → ℝ :=
    if hi : 1 ≤ i ∧ i ≤ n then
      Classical.choose (hlocal i hi.1 hi.2)
    else fun _ => 0
  have hlocalSpec (i : ℕ) (hi₁ : 1 ≤ i) (hi₂ : i ≤ n) :
      (∀ t ∈ previous_round_bucket_days conversation width k i,
        localPredictor i t ∈ Set.Icc (0 : ℝ) 1) ∧
      perfectly_calibrated conversation
        (previous_round_bucket_days conversation width k i)
        (localPredictor i) ∧
      (∑ t ∈ previous_round_bucket_days conversation width k i,
        |conversation.prediction k t - localPredictor i t|) ≤ bounds i := by
    have hlocalEq : localPredictor i =
        Classical.choose (hlocal i hi₁ hi₂) := by
      simp [localPredictor, hi₁, hi₂]
    rw [hlocalEq]
    exact Classical.choose_spec (hlocal i hi₁ hi₂)
  let index (t : Fin conversation.horizon) : ℕ :=
    bucket_index width (conversation.prediction (k - 1) t)
  have hindex (t : Fin conversation.horizon) :
      index t ∈ Finset.Icc 1 n := by
    rw [Finset.mem_Icc]
    change 1 ≤ min (Nat.ceil width⁻¹)
        (max 1 (Nat.ceil (conversation.prediction (k - 1) t / width))) ∧
      min (Nat.ceil width⁻¹)
        (max 1 (Nat.ceil (conversation.prediction (k - 1) t / width))) ≤ n
    rw [hceil]
    exact ⟨le_min hn (le_max_left _ _), min_le_left _ _⟩
  let calibrated (t : Fin conversation.horizon) : ℝ :=
    localPredictor (index t) t
  refine ⟨calibrated, ?_, ?_, ?_⟩
  · intro t ht
    have htBucket : t ∈ previous_round_bucket_days conversation width k (index t) := by
      simp [previous_round_bucket_days, index, ht]
    exact (hlocalSpec (index t) (Finset.mem_Icc.mp (hindex t)).1
      (Finset.mem_Icc.mp (hindex t)).2).1 t htBucket
  · unfold perfectly_calibrated
    intro value
    let totalFiber := prediction_fiber conversation
      (round_subsequence conversation k) calibrated value
    have hpartition (f : Fin conversation.horizon → ℝ) :
        (∑ t ∈ totalFiber, f t) =
          ∑ i ∈ Finset.Icc 1 n,
            ∑ t ∈ totalFiber.filter (fun t => index t = i), f t := by
      symm
      rw [Finset.sum_fiberwise_eq_sum_filter]
      rw [Finset.filter_eq_self.2]
      intro t ht
      exact hindex t
    have hfiber (i : ℕ) (hi : i ∈ Finset.Icc 1 n) :
        totalFiber.filter (fun t => index t = i) =
          prediction_fiber conversation
            (previous_round_bucket_days conversation width k i)
            (localPredictor i) value := by
      ext t
      simp only [totalFiber, prediction_fiber,
        previous_round_bucket_days, Finset.mem_filter]
      constructor
      · rintro ⟨⟨ht, hvalue⟩, hidx⟩
        refine ⟨⟨ht, ?_⟩, ?_⟩
        · exact hidx
        · simpa [calibrated, hidx] using hvalue
      · rintro ⟨⟨ht, hidx⟩, hvalue⟩
        refine ⟨⟨ht, ?_⟩, hidx⟩
        change index t = i at hidx
        simpa [calibrated, hidx] using hvalue
    change (∑ t ∈ totalFiber, conversation.label t) =
      value * (totalFiber.card : ℝ)
    calc
      (∑ t ∈ totalFiber, conversation.label t) =
          ∑ i ∈ Finset.Icc 1 n,
            ∑ t ∈ totalFiber.filter (fun t => index t = i),
              conversation.label t := hpartition conversation.label
      _ = ∑ i ∈ Finset.Icc 1 n,
            ∑ t ∈ prediction_fiber conversation
              (previous_round_bucket_days conversation width k i)
              (localPredictor i) value, conversation.label t := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hfiber i hi]
      _ = ∑ i ∈ Finset.Icc 1 n,
            value * ((prediction_fiber conversation
              (previous_round_bucket_days conversation width k i)
              (localPredictor i) value).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (hlocalSpec i (Finset.mem_Icc.mp hi).1
            (Finset.mem_Icc.mp hi).2).2.1 value
      _ = value * ∑ i ∈ Finset.Icc 1 n,
            ((prediction_fiber conversation
              (previous_round_bucket_days conversation width k i)
              (localPredictor i) value).card : ℝ) := by
          rw [Finset.mul_sum]
      _ = value * ∑ i ∈ Finset.Icc 1 n,
            ((totalFiber.filter (fun t => index t = i)).card : ℝ) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          rw [hfiber i hi]
      _ = value * (totalFiber.card : ℝ) := by
          congr 1
          have hmap : (totalFiber : Set (Fin conversation.horizon)).MapsTo
              index (Finset.Icc 1 n : Set ℕ) := by
            intro t ht
            exact hindex t
          have hcard := Finset.card_eq_sum_card_fiberwise hmap
          exact_mod_cast hcard.symm
  · have hpartition (f : Fin conversation.horizon → ℝ) :
        (∑ t ∈ round_subsequence conversation k, f t) =
          ∑ i ∈ Finset.Icc 1 n,
            ∑ t ∈ (round_subsequence conversation k).filter
              (fun t => index t = i), f t := by
      symm
      rw [Finset.sum_fiberwise_eq_sum_filter]
      rw [Finset.filter_eq_self.2]
      intro t ht
      exact hindex t
    calc
      (∑ t ∈ round_subsequence conversation k,
          |conversation.prediction k t - calibrated t|) =
        ∑ i ∈ Finset.Icc 1 n,
          ∑ t ∈ (round_subsequence conversation k).filter
            (fun t => index t = i),
            |conversation.prediction k t - calibrated t| :=
          hpartition fun t => |conversation.prediction k t - calibrated t|
      _ = ∑ i ∈ Finset.Icc 1 n,
          ∑ t ∈ previous_round_bucket_days conversation width k i,
            |conversation.prediction k t - localPredictor i t| := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr
          · ext t
            simp [previous_round_bucket_days, index]
          · intro t ht
            have hidx : index t = i := by
              have ht' : t ∈ (round_subsequence conversation k).filter
                  (fun t => index t = i) := by
                simpa [previous_round_bucket_days, index] using ht
              exact (Finset.mem_filter.mp ht').2
            simp [calibrated, hidx]
      _ ≤ ∑ i ∈ Finset.Icc 1 n, bounds i := by
          apply Finset.sum_le_sum
          intro i hi
          exact (hlocalSpec i (Finset.mem_Icc.mp hi).1
            (Finset.mem_Icc.mp hi).2).2.2

@[blueprint "lem:bucket-error-sum-bound"
  (statement := /-- Let \(f\colon\mathbb R\to\mathbb R\) be concave and nondecreasing on \([0,\infty)\), let \(w>0\), and suppose \(w=1/n\) for an integer \(n\geq1\). For every canonical conversation of horizon \(T\) and every round \(k\),
  \[
  \sum_{i=1}^{n} f\bigl(|T(k,i)|\bigr)
  \leq \frac{f(wT)}{w}.
  \] -/)
  (proof := /-- The previous-round buckets from \cref{def:previous-round-bucket-days} partition \(T^{\geq k}\), so their cardinalities have sum at most \(T\). A finite-set induction using the binary concavity inequality proves the equal-weight Jensen bound
  \[
  \sum_{i=1}^{n}f(a_i)\leq n f\!\left(\frac{\sum_i a_i}{n}\right).
  \]
  Since \(w=1/n\), multiplication by \(w\) bounds the weighted left-hand side by \(f(w|T^{\geq k}|)\). Monotonicity on \([0,\infty)\) and \(|T^{\geq k}|\leq T\) replace that argument by \(wT\); division by the positive number \(w\) gives the result. -/)
  (title := /-- Concave aggregate bucket-error bound -/)
  (latexEnv := "lemma")]
lemma bucket_error_sum_bound
    (conversation : canonical_conversation) (error : ℝ → ℝ)
    (width : ℝ) (k n : ℕ)
    (herror : calibration_error_function error)
    (hwidthPos : 0 < width) (hn : 1 ≤ n)
    (hwidth : width = (n : ℝ)⁻¹) :
    (∑ i ∈ Finset.Icc 1 n,
      error ((previous_round_bucket_days conversation width k i).card : ℝ)) ≤
      error (width * conversation.horizon) / width := by
  classical
  have hnNe : n ≠ 0 := by omega
  have hwidthInv : width⁻¹ = (n : ℝ) := by
    rw [hwidth, inv_inv]
  have hceil : Nat.ceil width⁻¹ = n := by
    rw [hwidthInv]
    exact Nat.ceil_natCast n
  let index (t : Fin conversation.horizon) : ℕ :=
    bucket_index width (conversation.prediction (k - 1) t)
  have hindex (t : Fin conversation.horizon) :
      index t ∈ Finset.Icc 1 n := by
    rw [Finset.mem_Icc]
    change 1 ≤ min (Nat.ceil width⁻¹)
        (max 1 (Nat.ceil (conversation.prediction (k - 1) t / width))) ∧
      min (Nat.ceil width⁻¹)
        (max 1 (Nat.ceil (conversation.prediction (k - 1) t / width))) ≤ n
    rw [hceil]
    exact ⟨le_min hn (le_max_left _ _), min_le_left _ _⟩
  let days := round_subsequence conversation k
  have hmap : (days : Set (Fin conversation.horizon)).MapsTo
      index (Finset.Icc 1 n : Set ℕ) := by
    intro t ht
    exact hindex t
  have hcardNat : days.card =
      ∑ i ∈ Finset.Icc 1 n,
        (previous_round_bucket_days conversation width k i).card := by
    simpa [days, index, previous_round_bucket_days] using
      (Finset.card_eq_sum_card_fiberwise hmap)
  have hcard :
      (∑ i ∈ Finset.Icc 1 n,
        ((previous_round_bucket_days conversation width k i).card : ℝ)) =
        (days.card : ℝ) := by
    exact_mod_cast hcardNat.symm
  have hdaysCard : (days.card : ℝ) ≤ conversation.horizon := by
    have hnat : days.card ≤ conversation.horizon := by
      simpa using Finset.card_le_univ days
    exact_mod_cast hnat
  have hconcave : ConcaveOn ℝ (Set.Ici (0 : ℝ)) error := herror.1
  have hmonotoneOn : MonotoneOn error (Set.Ici (0 : ℝ)) := herror.2
  let size (i : ℕ) : ℝ :=
    ((previous_round_bucket_days conversation width k i).card : ℝ)
  have haverage : ∀ s : Finset ℕ, s.Nonempty →
      (∑ i ∈ s, error (size i)) ≤
        (s.card : ℝ) * error ((∑ i ∈ s, size i) / (s.card : ℝ)) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro hs
      exact (Finset.not_nonempty_empty hs).elim
    · intro x s hx ih hsInsert
      by_cases hsEmpty : s = ∅
      · subst s
        simp
      · have hsNonempty : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hsEmpty
        have hcardPos : 0 < (s.card : ℝ) := by
          exact_mod_cast Finset.card_pos.mpr hsNonempty
        have hxNonneg : 0 ≤ size x := by
          simp [size]
        have hsumNonneg : 0 ≤ ∑ i ∈ s, size i := by
          exact Finset.sum_nonneg fun i hi => by simp [size]
        have havgNonneg : 0 ≤ (∑ i ∈ s, size i) / (s.card : ℝ) :=
          div_nonneg hsumNonneg (le_of_lt hcardPos)
        have hcoeffSum :
            1 / ((s.card : ℝ) + 1) +
              (s.card : ℝ) / ((s.card : ℝ) + 1) = 1 := by
          field_simp
          <;> ring
        have hbinary :
            (1 / ((s.card : ℝ) + 1)) * error (size x) +
                ((s.card : ℝ) / ((s.card : ℝ) + 1)) *
                  error ((∑ i ∈ s, size i) / (s.card : ℝ)) ≤
              error ((1 / ((s.card : ℝ) + 1)) * size x +
                ((s.card : ℝ) / ((s.card : ℝ) + 1)) *
                  ((∑ i ∈ s, size i) / (s.card : ℝ))) := by
          simpa [smul_eq_mul] using hconcave.2 hxNonneg havgNonneg
            (by positivity) (by positivity) hcoeffSum
        calc
          (∑ i ∈ insert x s, error (size i)) =
              error (size x) + ∑ i ∈ s, error (size i) := by simp [hx]
          _ ≤ error (size x) + (s.card : ℝ) *
              error ((∑ i ∈ s, size i) / (s.card : ℝ)) :=
                by linarith [ih hsNonempty]
          _ = ((s.card : ℝ) + 1) *
              ((1 / ((s.card : ℝ) + 1)) * error (size x) +
                ((s.card : ℝ) / ((s.card : ℝ) + 1)) *
                  error ((∑ i ∈ s, size i) / (s.card : ℝ))) := by
                field_simp
                <;> ring
          _ ≤ ((s.card : ℝ) + 1) *
              error ((1 / ((s.card : ℝ) + 1)) * size x +
                ((s.card : ℝ) / ((s.card : ℝ) + 1)) *
                  ((∑ i ∈ s, size i) / (s.card : ℝ))) :=
                mul_le_mul_of_nonneg_left hbinary (by positivity)
          _ = ((insert x s).card : ℝ) *
              error ((∑ i ∈ insert x s, size i) /
                ((insert x s).card : ℝ)) := by
                simp only [Finset.card_insert_of_notMem hx,
                  Nat.cast_add, Nat.cast_one, Finset.sum_insert hx]
                congr 1
                field_simp [ne_of_gt hcardPos]
                <;> ring
  have hIccNonempty : (Finset.Icc 1 n).Nonempty :=
    ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hn⟩⟩
  have haverageIcc := haverage (Finset.Icc 1 n) hIccNonempty
  have haverageIcc' :
      (∑ i ∈ Finset.Icc 1 n,
        error ((previous_round_bucket_days conversation width k i).card : ℝ)) ≤
      (n : ℝ) * error ((days.card : ℝ) / (n : ℝ)) := by
    simpa [size, hcard] using haverageIcc
  have hwidthCount : width * (n : ℝ) = 1 := by
    simp [hwidth, hnNe]
  have haverageArgument : (days.card : ℝ) / (n : ℝ) =
      width * (days.card : ℝ) := by
    simp [hwidth, div_eq_mul_inv, mul_comm]
  have hjensen :
      width * (∑ i ∈ Finset.Icc 1 n,
        error ((previous_round_bucket_days conversation width k i).card : ℝ)) ≤
      error (width * (days.card : ℝ)) := by
    calc
      width * (∑ i ∈ Finset.Icc 1 n,
          error ((previous_round_bucket_days conversation width k i).card : ℝ)) ≤
        width * ((n : ℝ) * error ((days.card : ℝ) / (n : ℝ))) :=
          mul_le_mul_of_nonneg_left haverageIcc' (le_of_lt hwidthPos)
      _ = error (width * (days.card : ℝ)) := by
          rw [← mul_assoc, hwidthCount, one_mul, haverageArgument]
  have harg : width * (days.card : ℝ) ≤
      width * conversation.horizon :=
    mul_le_mul_of_nonneg_left hdaysCard (le_of_lt hwidthPos)
  have hmonotone : error (width * (days.card : ℝ)) ≤
      error (width * conversation.horizon) :=
    hmonotoneOn (mul_nonneg (le_of_lt hwidthPos) (by positivity))
      (mul_nonneg (le_of_lt hwidthPos) (by positivity)) harg
  apply (le_div_iff₀ hwidthPos).2
  calc
    (∑ i ∈ Finset.Icc 1 n,
        error ((previous_round_bucket_days conversation width k i).card : ℝ)) * width =
      width * (∑ i ∈ Finset.Icc 1 n,
        error ((previous_round_bucket_days conversation width k i).card : ℝ)) :=
          mul_comm _ _
    _ ≤ error (width * (days.card : ℝ)) := hjensen
    _ ≤ error (width * conversation.horizon) := hmonotone

@[blueprint "lem:bucketwise-calibrated-surrogate"
  (statement := /-- Let a canonical conversation have horizon \(T\), let \(f\colon\mathbb R\to\mathbb R\) and \(g\colon\mathbb N\to\mathbb R\), and fix a party and a round \(k\in\mathbb N\). Suppose that the party is \((f,g)\)-conversation-calibrated and that round \(k\) belongs to that party. Then there exists a predictor \(q\colon\{0,\ldots,T-1\}\to\mathbb R\) which takes values in \([0,1]\) on \(T^{\geq k}\), is perfectly calibrated on \(T^{\geq k}\), and satisfies
  \[
  \sum_{t\in T^{\geq k}}|p^{t,k}-q^t|
  \leq \frac{f(g(T)T)}{g(T)}.
  \] -/)
  (proof := /-- Unpack \cref{def:conversation-calibrated}. Thus \(g(T)>0\), there is an integer \(n\geq1\) with \(g(T)=1/n\), and every previous-round bucket \(T(k,i)\), \(1\leq i\leq n\), has a calibrated surrogate whose distance is at most \(f(|T(k,i)|)\). Apply \cref{lem:bucket-surrogates-stitch} to these witnesses. It gives a predictor \(q\) which takes values in \([0,1]\) and is perfectly calibrated on \(T^{\geq k}\), together with
  \[
  \sum_{t\in T^{\geq k}}|p^{t,k}-q^t|
  \leq \sum_{i=1}^{n}f\bigl(|T(k,i)|\bigr).
  \]
  The concavity, monotonicity, positivity, and reciprocal-width facts obtained from the same hypothesis meet the assumptions of \cref{lem:bucket-error-sum-bound}, which bounds the right-hand side by \(f(g(T)T)/g(T)\). Transitivity yields the required estimate. -/)
  (title := /-- Aggregate calibrated surrogate -/)
  (latexEnv := "lemma")]
lemma bucketwise_calibrated_surrogate
    (conversation : canonical_conversation) (human : Bool)
    (error : ℝ → ℝ) (width : ℕ → ℝ) (k : ℕ)
    (hcalibration :
      conversation_calibrated conversation human error width)
    (hrole : party_round human k) :
    ∃ calibrated : Fin conversation.horizon → ℝ,
      (∀ t ∈ round_subsequence conversation k,
        calibrated t ∈ Set.Icc (0 : ℝ) 1) ∧
      perfectly_calibrated conversation
        (round_subsequence conversation k) calibrated ∧
      (∑ t ∈ round_subsequence conversation k,
        |conversation.prediction k t - calibrated t|) ≤
        error (width conversation.horizon * conversation.horizon) /
          width conversation.horizon := by
  rcases hcalibration with
    ⟨herror, hwidthPos, _, ⟨n, hn, hwidth⟩, hlocal⟩
  have hwidthInv : (width conversation.horizon)⁻¹ = (n : ℝ) := by
    rw [hwidth, inv_inv]
  have hceil : Nat.ceil (width conversation.horizon)⁻¹ = n := by
    rw [hwidthInv]
    exact Nat.ceil_natCast n
  have hlocal' : ∀ i : ℕ, 1 ≤ i → i ≤ n →
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
            (width conversation.horizon) k i).card : ℝ) := by
    intro i hi₁ hi₂
    exact hlocal k hrole i hi₁ (by simpa [hceil] using hi₂)
  obtain ⟨calibrated, hrange, hperfect, hclose⟩ :=
    bucket_surrogates_stitch conversation (width conversation.horizon) k n
      (fun i => error ((previous_round_bucket_days conversation
        (width conversation.horizon) k i).card : ℝ)) hn hceil hlocal'
  refine ⟨calibrated, hrange, hperfect, hclose.trans ?_⟩
  exact bucket_error_sum_bound conversation error
    (width conversation.horizon) k n herror hwidthPos hn hwidth

@[blueprint "lem:bucket-index-rounding-bounds"
  (statement := /-- Let \(w\in(0,1]\) be the reciprocal of an integer \(n\geq1\). For every \(x\in[0,1]\), the upper endpoint \(b_w(x)=w\,\operatorname{bucketIndex}_w(x)\) satisfies \(x\leq b_w(x)\leq x+w\). -/)
  (proof := /-- By \cref{def:bucket-index}, the untruncated index is the maximum of \(1\) and \(\lceil x/w\rceil\). Since \(x\leq1\) and \(w=1/n\), this index is at most \(n=\lceil w^{-1}\rceil\), so the truncation is inactive. The defining inequalities for the ceiling, multiplied by the positive number \(w\), give the two asserted endpoint bounds. -/)
  (title := /-- Bounds for reciprocal-width bucket rounding -/)
  (latexEnv := "lemma")]
lemma bucket_index_rounding_bounds
    (w x : ℝ) (n : ℕ) (hwpos : 0 < w) (hn : 1 ≤ n)
    (hw : w = (n : ℝ)⁻¹) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    x ≤ (bucket_index w x : ℝ) * w ∧
      (bucket_index w x : ℝ) * w ≤ x + w := by
  rcases hx with ⟨hx0, hx1⟩
  have hn0 : n ≠ 0 := by omega
  have hdiv_nonneg : 0 ≤ x / w := div_nonneg hx0 hwpos.le
  have hceil_le : ⌈x / w⌉₊ ≤ n := by
    rw [Nat.ceil_le]
    rw [hw]
    field_simp
    nlinarith
  have hceil_inv : ⌈w⁻¹⌉₊ = n := by
    rw [hw]
    simp [hn0]
  have hindex : bucket_index w x = max 1 ⌈x / w⌉₊ := by
    rw [bucket_index, hceil_inv, min_eq_right]
    exact max_le hn hceil_le
  rw [hindex]
  constructor
  · apply (div_le_iff₀ hwpos).mp
    exact (Nat.le_ceil (x / w)).trans (by exact_mod_cast le_max_right 1 ⌈x / w⌉₊)
  · have hmax : (max 1 ⌈x / w⌉₊ : ℝ) ≤ x / w + 1 := by
      apply max_le
      · nlinarith
      · exact (Nat.ceil_lt_add_one hdiv_nonneg).le
    have := mul_le_mul_of_nonneg_right hmax hwpos.le
    calc
      (↑(max 1 ⌈x / w⌉₊) : ℝ) * w ≤ (x / w + 1) * w := by
        simpa only [Nat.cast_max, Nat.cast_one] using this
      _ = x + w := by field_simp

@[blueprint "lem:separated-bucket-quadratic-bound"
  (statement := /-- Let \(w\in(0,1]\) be the reciprocal of an integer \(n\geq1\), and let \(x,z\in[0,1]\). If \(0<\epsilon\leq|x-z|\), then, writing \(b_w\) for upper-endpoint bucketing,
  \[
  (b_w(x)-x)^2-(b_w(z)-x)^2\leq w-(\epsilon-w)^2.
  \] -/)
  (proof := /-- Apply \cref{lem:bucket-index-rounding-bounds} to both \(x\) and \(z\). If \(\epsilon\geq w\), the triangle inequality gives \(|b_w(z)-x|\geq\epsilon-w\), while \(|b_w(x)-x|\leq w\), and \(w^2\leq w\). If \(0<\epsilon<w\), then either \(n=1\), in which case both bucketed values equal \(1\), or \(n\geq2\), in which case \(w\leq1/2\). In the latter case the left-hand side is at most \(w^2\), whereas \(w^2\leq w-(w-\epsilon)^2\). -/)
  (title := /-- Quadratic gain from separated reciprocal-width buckets -/)
  (latexEnv := "lemma")]
lemma separated_bucket_quadratic_bound
    (w x z epsilon : ℝ) (n : ℕ) (hwpos : 0 < w) (hwle : w ≤ 1)
    (hn : 1 ≤ n) (hw : w = (n : ℝ)⁻¹)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hepsilon : 0 < epsilon) (hsep : epsilon ≤ |x - z|) :
    ((bucket_index w x : ℝ) * w - x) ^ 2 -
        ((bucket_index w z : ℝ) * w - x) ^ 2 ≤
      w - (epsilon - w) ^ 2 := by
  let bx := (bucket_index w x : ℝ) * w
  let bz := (bucket_index w z : ℝ) * w
  change (bx - x) ^ 2 - (bz - x) ^ 2 ≤ w - (epsilon - w) ^ 2
  rcases bucket_index_rounding_bounds w x n hwpos hn hw hx with ⟨hxbx, hbxx⟩
  rcases bucket_index_rounding_bounds w z n hwpos hn hw hz with ⟨hzbz, hbzz⟩
  have hbx0 : 0 ≤ bx - x := by dsimp [bx]; linarith
  have hbxw : bx - x ≤ w := by dsimp [bx]; linarith
  have hbz0 : 0 ≤ bz - z := by dsimp [bz]; linarith
  have hbzw : bz - z ≤ w := by dsimp [bz]; linarith
  have hbx_sq : (bx - x) ^ 2 ≤ w ^ 2 :=
    (sq_le_sq₀ hbx0 hwpos.le).2 hbxw
  have habs : |x - z| ≤ 1 := by
    rw [abs_le]
    rcases hx with ⟨hx0, hx1⟩
    rcases hz with ⟨hz0, hz1⟩
    constructor <;> linarith
  have hepsilon_le : epsilon ≤ 1 := hsep.trans habs
  by_cases hnone : n = 1
  · subst n
    norm_num at hw
    subst w
    have hbx_one : bx = 1 := by simp [bx, bucket_index]
    have hbz_one : bz = 1 := by simp [bz, bucket_index]
    rw [hbx_one, hbz_one]
    nlinarith [sq_nonneg (epsilon - 1)]
  · have hntwo : 2 ≤ n := by omega
    have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hntwo
    have hwlehalf : w ≤ (1 : ℝ) / 2 := by
      rw [hw, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hnreal
    by_cases hew : epsilon ≤ w
    · have hdiff0 : 0 ≤ w - epsilon := by linarith
      have hdiffw : w - epsilon ≤ w := by linarith
      have hdiff_sq : (w - epsilon) ^ 2 ≤ w ^ 2 :=
        (sq_le_sq₀ hdiff0 hwpos.le).2 hdiffw
      have htwosq : 2 * w ^ 2 ≤ w := by
        have hmul := mul_le_mul_of_nonneg_left hwlehalf (show 0 ≤ 2 * w by positivity)
        nlinarith
      nlinarith [sq_nonneg (bz - x)]
    · have hwe : w ≤ epsilon := le_of_not_ge hew
      have htri : |x - z| ≤ |x - bz| + |bz - z| := by
        calc
          |x - z| = |(x - bz) + (bz - z)| := by ring_nf
          _ ≤ |x - bz| + |bz - z| := abs_add_le _ _
      have hbzabs : |bz - z| ≤ w := by rw [abs_of_nonneg hbz0]; exact hbzw
      have hlower : epsilon - w ≤ |bz - x| := by
        rw [abs_sub_comm]
        linarith
      have hlower_sq : (epsilon - w) ^ 2 ≤ (bz - x) ^ 2 := by
        rw [← sq_abs (bz - x)]
        exact (sq_le_sq₀ (by linarith) (abs_nonneg _)).2 hlower
      have hwsq : w ^ 2 ≤ w := by nlinarith [mul_nonneg hwpos.le (sub_nonneg.mpr hwle)]
      nlinarith

@[blueprint "lem:perfect-calibration-weighted-residual"
  (statement := /-- Let \(p\) be perfectly calibrated on a finite set \(S\) of days. For every function \(a\colon\mathbb R\to\mathbb R\),
  \[
  \sum_{t\in S}a(p^t)(p^t-y^t)=0.
  \] -/)
  (proof := /-- Partition \(S\) into the fibers of \(p\) from \cref{def:prediction-fiber}. On the fiber with value \(v\), the factor \(a(p^t)\) is the constant \(a(v)\), while perfect calibration from \cref{def:perfectly-calibrated} states that \(\sum_t(v-y^t)=0\). Hence every fiber contributes zero, and summing the fibers proves the identity. -/)
  (title := /-- Weighted residual identity for perfect calibration -/)
  (latexEnv := "lemma")]
lemma perfect_calibration_weighted_residual
    (conversation : canonical_conversation)
    (days : Finset (Fin conversation.horizon))
    (predictor : Fin conversation.horizon → ℝ) (weight : ℝ → ℝ)
    (hcalibrated : perfectly_calibrated conversation days predictor) :
    (∑ t ∈ days,
      weight (predictor t) * (predictor t - conversation.label t)) = 0 := by
  classical
  let values := days.image predictor
  have hfiber (value : ℝ) :
      (∑ t ∈ days with predictor t = value,
        weight (predictor t) * (predictor t - conversation.label t)) = 0 := by
    have hcal := hcalibrated value
    rw [prediction_fiber] at hcal
    calc
      (∑ t ∈ days with predictor t = value,
          weight (predictor t) * (predictor t - conversation.label t)) =
          ∑ t ∈ days with predictor t = value,
            weight value * (value - conversation.label t) := by
            apply Finset.sum_congr rfl
            intro t ht
            simp only [Finset.mem_filter] at ht
            rw [ht.2]
      _ = weight value *
          (∑ t ∈ days with predictor t = value,
            (value - conversation.label t)) := by rw [Finset.mul_sum]
      _ =
          weight value *
            ((value * (days.filter fun t => predictor t = value).card) -
              ∑ t ∈ days with predictor t = value, conversation.label t) := by
            congr 1
            rw [Finset.sum_sub_distrib]
            simp
            ring
      _ = 0 := by rw [hcal]; ring
  calc
    (∑ t ∈ days,
        weight (predictor t) * (predictor t - conversation.label t)) =
        ∑ value ∈ values, ∑ t ∈ days with predictor t = value,
          weight (predictor t) * (predictor t - conversation.label t) := by
      symm
      have hfiberwise :=
        Finset.sum_fiberwise_eq_sum_filter days values predictor
          (fun t => weight (predictor t) *
            (predictor t - conversation.label t))
      have hfilter : days.filter (fun t => predictor t ∈ values) = days := by
        apply Finset.filter_eq_self.2
        intro t ht
        exact Finset.mem_image.2 ⟨t, ht, rfl⟩
      rw [hfilter] at hfiberwise
      exact hfiberwise
    _ = 0 := by simp [hfiber]

@[blueprint "lem:perfect-calibration-squared-error-shift"
  (statement := /-- Let \(p\) be perfectly calibrated on a finite set \(S\), let \(c\in\mathbb R\), and let \(r\colon\mathbb R\to\mathbb R\). Then
  \[
  \sum_{t\in S}\bigl((r(p^t)-y^t)^2-(c-y^t)^2\bigr)
  =\sum_{t\in S}\bigl((r(p^t)-p^t)^2-(c-p^t)^2\bigr).
  \] -/)
  (proof := /-- Expand both squared errors around \(p^t\). The two cross terms are weighted residual sums with respective weights \(r(v)-v\) and \(c-v\), so both vanish by \cref{lem:perfect-calibration-weighted-residual}. The common sum of \((p^t-y^t)^2\) cancels, leaving the asserted identity. -/)
  (title := /-- Squared-error shift under perfect calibration -/)
  (latexEnv := "lemma")]
lemma perfect_calibration_squared_error_shift
    (conversation : canonical_conversation)
    (days : Finset (Fin conversation.horizon))
    (predictor : Fin conversation.horizon → ℝ)
    (rounded : ℝ → ℝ) (constant : ℝ)
    (hcalibrated : perfectly_calibrated conversation days predictor) :
    (∑ t ∈ days,
      ((rounded (predictor t) - conversation.label t) ^ 2 -
        (constant - conversation.label t) ^ 2)) =
      ∑ t ∈ days,
        ((rounded (predictor t) - predictor t) ^ 2 -
          (constant - predictor t) ^ 2) := by
  have hrounded := perfect_calibration_weighted_residual conversation days predictor
    (fun value => rounded value - value) hcalibrated
  have hconstant := perfect_calibration_weighted_residual conversation days predictor
    (fun value => constant - value) hcalibrated
  have hrounded' :
      (∑ t ∈ days, 2 * (rounded (predictor t) - predictor t) *
        (predictor t - conversation.label t)) = 0 := by
    calc
      _ = 2 * ∑ t ∈ days, (rounded (predictor t) - predictor t) *
          (predictor t - conversation.label t) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        ring
      _ = 0 := by rw [hrounded]; ring
  have hconstant' :
      (∑ t ∈ days, 2 * (constant - predictor t) *
        (predictor t - conversation.label t)) = 0 := by
    calc
      _ = 2 * ∑ t ∈ days, (constant - predictor t) *
          (predictor t - conversation.label t) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        ring
      _ = 0 := by rw [hconstant]; ring
  calc
    (∑ t ∈ days,
        ((rounded (predictor t) - conversation.label t) ^ 2 -
          (constant - conversation.label t) ^ 2)) =
        ∑ t ∈ days,
          (((rounded (predictor t) - predictor t) ^ 2 -
            (constant - predictor t) ^ 2) +
            2 * (rounded (predictor t) - predictor t) *
              (predictor t - conversation.label t) -
            2 * (constant - predictor t) *
              (predictor t - conversation.label t)) := by
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ = ∑ t ∈ days,
        ((rounded (predictor t) - predictor t) ^ 2 -
          (constant - predictor t) ^ 2) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [hrounded', hconstant']
      ring

@[blueprint "lem:fiberwise-perfect-calibration-squared-error-shift"
  (statement := /-- Let a finite day set \(S\) be partitioned by a key \(\kappa\). Suppose that \(p\) is perfectly calibrated on every nonempty key fiber. For arbitrary functions \(r\colon\mathbb R\to\mathbb R\) and \(c\) from keys to \(\mathbb R\),
  \[
  \sum_{t\in S}\bigl((r(p^t)-y^t)^2-(c(\kappa(t))-y^t)^2\bigr)
  =\sum_{t\in S}\bigl((r(p^t)-p^t)^2-(c(\kappa(t))-p^t)^2\bigr).
  \] -/)
  (proof := /-- Partition both sums into the finitely many key fibers represented in \(S\). On the fiber with key \(i\), replace \(c(\kappa(t))\) by the constant \(c(i)\), and apply \cref{lem:perfect-calibration-squared-error-shift} using the assumed perfect calibration on that fiber. Summing these fiber identities yields the result. -/)
  (title := /-- Squared-error shift for fiberwise perfect calibration -/)
  (latexEnv := "lemma")]
lemma fiberwise_perfect_calibration_squared_error_shift
    {α : Type} [DecidableEq α]
    (conversation : canonical_conversation)
    (days : Finset (Fin conversation.horizon))
    (key : Fin conversation.horizon → α)
    (predictor : Fin conversation.horizon → ℝ)
    (rounded : ℝ → ℝ) (constant : α → ℝ)
    (hcalibrated : ∀ value ∈ days.image key,
      perfectly_calibrated conversation
        (days.filter fun t => key t = value) predictor) :
    (∑ t ∈ days,
      ((rounded (predictor t) - conversation.label t) ^ 2 -
        (constant (key t) - conversation.label t) ^ 2)) =
      ∑ t ∈ days,
        ((rounded (predictor t) - predictor t) ^ 2 -
          (constant (key t) - predictor t) ^ 2) := by
  classical
  let values := days.image key
  have hpartition (f : Fin conversation.horizon → ℝ) :
      (∑ t ∈ days, f t) =
        ∑ value ∈ values, ∑ t ∈ days with key t = value, f t := by
    symm
    have hfiberwise := Finset.sum_fiberwise_eq_sum_filter days values key f
    have hfilter : days.filter (fun t => key t ∈ values) = days := by
      apply Finset.filter_eq_self.2
      intro t ht
      exact Finset.mem_image.2 ⟨t, ht, rfl⟩
    rw [hfilter] at hfiberwise
    exact hfiberwise
  rw [hpartition, hpartition]
  apply Finset.sum_congr rfl
  intro value hvalue
  have hshift := perfect_calibration_squared_error_shift conversation
    (days.filter fun t => key t = value) predictor rounded (constant value)
    (hcalibrated value (by simpa [values] using hvalue))
  calc
    (∑ t ∈ days with key t = value,
        ((rounded (predictor t) - conversation.label t) ^ 2 -
          (constant (key t) - conversation.label t) ^ 2)) =
        ∑ t ∈ days with key t = value,
          ((rounded (predictor t) - conversation.label t) ^ 2 -
            (constant value - conversation.label t) ^ 2) := by
      apply Finset.sum_congr rfl
      intro t ht
      simp only [Finset.mem_filter] at ht
      rw [ht.2]
    _ = ∑ t ∈ days with key t = value,
        ((rounded (predictor t) - predictor t) ^ 2 -
          (constant value - predictor t) ^ 2) := hshift
    _ = ∑ t ∈ days with key t = value,
        ((rounded (predictor t) - predictor t) ^ 2 -
          (constant (key t) - predictor t) ^ 2) := by
      apply Finset.sum_congr rfl
      intro t ht
      simp only [Finset.mem_filter] at ht
      rw [ht.2]

@[blueprint "lem:perfect-round-error-decrease"
  (statement := /-- Let a canonical conversation have horizon \(T\), let \(h\) be one of its two parties, let \(g\colon\mathbb N\to\mathbb R\), let \(\epsilon\in\mathbb R\), and let \(k\geq1\) be an integer round assigned to \(h\). If the conversation is an \(\epsilon\)-agreement run and \(h\) is perfectly conversation-calibrated at width \(g\), then
  \[
  \operatorname{SQErr}(\bar p^k,y)
  \leq \operatorname{SQErr}(\bar p^{k-1},y)
  -(\epsilon-g(T))^2|T^{\geq k+1}|+g(T)T.
  \] -/)
  (proof := /-- Put \(w=g(T)\), \(A=T^{\geq k}\), and \(B=T^{\geq k+1}\). Perfect conversation calibration supplies \(w\in(0,1]\), an integer \(n\geq1\) with \(w=n^{-1}\), and perfect calibration of the round-\(k\) prediction on every previous-round bucket; see \cref{def:perfectly-conversation-calibrated}. The terminal inequality in the \(\epsilon\)-agreement condition from \cref{def:epsilon-agreement-run} also implies \(\epsilon>0\). Partition \(A\) by the width-\(w\) bucket of the round-\((k-1)\) prediction. Applying \cref{lem:fiberwise-perfect-calibration-squared-error-shift} converts the change in squared error on \(A\) into the sum, over its days \(t\), of
  \[
  (b_w(p^{t,k})-p^{t,k})^2-(b_w(p^{t,k-1})-p^{t,k})^2.
  \]
  For \(t\in B\), the nonterminal separation clause in \cref{def:epsilon-agreement-run} gives \(\epsilon\leq|p^{t,k}-p^{t,k-1}|\), so \cref{lem:separated-bucket-quadratic-bound} bounds this summand by \(w-(\epsilon-w)^2\). For \(t\in A\setminus B\), \cref{lem:bucket-index-rounding-bounds} gives \(0\leq b_w(p^{t,k})-p^{t,k}\leq w\); since \(w^2\leq w\), the summand is at most \(w\). Thus the total change on \(A\) is at most \(w|A|-(\epsilon-w)^2|B|\). By \cref{def:round-subsequence,def:bucketed-round-prediction}, the two bucketed predictors coincide off \(A\), and \(|A|\leq T\). Substitution into the squared-error sum of \cref{def:squared-error} yields the claimed inequality. -/)
  (title := /-- Perfect-calibration one-round decrease -/)
  (latexEnv := "lemma")]
lemma perfect_round_error_decrease
    (conversation : canonical_conversation) (human : Bool)
    (width : ℕ → ℝ) (epsilon : ℝ) (k : ℕ)
    (hperfect :
      perfectly_conversation_calibrated conversation human width)
    (hrole : party_round human k)
    (hrun : epsilon_agreement_run conversation epsilon) (hk : 1 ≤ k) :
    squared_error conversation Finset.univ
        (bucketed_round_prediction conversation
          (width conversation.horizon) k) ≤
      squared_error conversation Finset.univ
        (bucketed_round_prediction conversation
          (width conversation.horizon) (k - 1)) -
      (epsilon - width conversation.horizon) ^ 2 *
        (round_subsequence conversation (k + 1)).card +
      width conversation.horizon * conversation.horizon := by
  classical
  rcases hperfect with ⟨hwpos, hwle, ⟨n, hn, hwrec⟩, hcalibrated⟩
  let w := width conversation.horizon
  change 0 < w at hwpos
  change w ≤ 1 at hwle
  change w = (n : ℝ)⁻¹ at hwrec
  have hepsilon : 0 < epsilon := by
    let t : Fin conversation.horizon := ⟨0, conversation.horizon_pos⟩
    have hterminal := (hrun.2 t).1
    exact (abs_nonneg _).trans_lt hterminal
  let active := round_subsequence conversation k
  let next := round_subsequence conversation (k + 1)
  let key : Fin conversation.horizon → ℕ := fun t =>
    bucket_index w (conversation.prediction (k - 1) t)
  let rounded : ℝ → ℝ := fun value => (bucket_index w value : ℝ) * w
  let constant : ℕ → ℝ := fun value => (value : ℝ) * w
  have hnext_active : next ⊆ active := by
    intro t ht
    simp only [next, active, round_subsequence, Finset.mem_filter,
      Finset.mem_univ, true_and] at ht ⊢
    omega
  have hfiber_calibrated : ∀ value ∈ active.image key,
      perfectly_calibrated conversation
        (active.filter fun t => key t = value) (conversation.prediction k) := by
    intro value hvalue
    rcases Finset.mem_image.1 hvalue with ⟨t, ht, rfl⟩
    have hceil_one : 1 ≤ ⌈w⁻¹⌉₊ := Nat.one_le_ceil_iff.2 (inv_pos.2 hwpos)
    have hkey_one : 1 ≤ key t := by
      dsimp [key, bucket_index]
      exact le_min hceil_one (le_max_left 1 ⌈conversation.prediction (k - 1) t / w⌉₊)
    have hkey_ceil : key t ≤ ⌈w⁻¹⌉₊ := by
      dsimp [key, bucket_index]
      exact min_le_left _ _
    have hcal := hcalibrated k hrole (key t) hkey_one hkey_ceil
    simpa only [active, key, previous_round_bucket_days] using hcal
  have hshift := fiberwise_perfect_calibration_squared_error_shift
    conversation active key (conversation.prediction k) rounded constant
    hfiber_calibrated
  have hactive_shift :
      (∑ t ∈ active,
        ((bucketed_round_prediction conversation w k t - conversation.label t) ^ 2 -
          (bucketed_round_prediction conversation w (k - 1) t -
            conversation.label t) ^ 2)) =
        ∑ t ∈ active,
          ((rounded (conversation.prediction k t) - conversation.prediction k t) ^ 2 -
            (constant (key t) - conversation.prediction k t) ^ 2) := by
    calc
      (∑ t ∈ active,
          ((bucketed_round_prediction conversation w k t - conversation.label t) ^ 2 -
            (bucketed_round_prediction conversation w (k - 1) t -
              conversation.label t) ^ 2)) =
          ∑ t ∈ active,
            ((rounded (conversation.prediction k t) - conversation.label t) ^ 2 -
              (constant (key t) - conversation.label t) ^ 2) := by
        apply Finset.sum_congr rfl
        intro t ht
        have htk : k ≤ conversation.length t := by
          simpa only [active, round_subsequence, Finset.mem_filter,
            Finset.mem_univ, true_and] using ht
        have htkprev : k - 1 ≤ conversation.length t := by omega
        simp only [bucketed_round_prediction, min_eq_left htk,
          min_eq_left htkprev, rounded, constant, key]
      _ = _ := hshift
  have hpointwise (t : Fin conversation.horizon) (ht : t ∈ active) :
      (rounded (conversation.prediction k t) - conversation.prediction k t) ^ 2 -
          (constant (key t) - conversation.prediction k t) ^ 2 ≤
        if t ∈ next then w - (epsilon - w) ^ 2 else w := by
    by_cases htnext : t ∈ next
    · rw [if_pos htnext]
      have htlength : k < conversation.length t := by
        have : k + 1 ≤ conversation.length t := by
          simpa only [next, round_subsequence, Finset.mem_filter,
            Finset.mem_univ, true_and] using htnext
        omega
      have hsep := (hrun.2 t).2 k hk htlength
      simpa only [rounded, constant, key, abs_sub_comm] using
        (separated_bucket_quadratic_bound w
          (conversation.prediction k t) (conversation.prediction (k - 1) t)
          epsilon n hwpos hwle hn hwrec
          (conversation.prediction_mem k t)
          (conversation.prediction_mem (k - 1) t) hepsilon hsep)
    · rw [if_neg htnext]
      rcases bucket_index_rounding_bounds w (conversation.prediction k t) n
        hwpos hn hwrec (conversation.prediction_mem k t) with ⟨hlower, hupper⟩
      have hdelta0 : 0 ≤ rounded (conversation.prediction k t) -
          conversation.prediction k t := by dsimp [rounded]; linarith
      have hdeltaw : rounded (conversation.prediction k t) -
          conversation.prediction k t ≤ w := by dsimp [rounded]; linarith
      have hdeltasq :
          (rounded (conversation.prediction k t) - conversation.prediction k t) ^ 2 ≤
            w ^ 2 := (sq_le_sq₀ hdelta0 hwpos.le).2 hdeltaw
      have hwsq : w ^ 2 ≤ w := by
        nlinarith [mul_nonneg hwpos.le (sub_nonneg.2 hwle)]
      nlinarith [sq_nonneg (constant (key t) - conversation.prediction k t)]
  have hactive_bound :
      (∑ t ∈ active,
        ((rounded (conversation.prediction k t) - conversation.prediction k t) ^ 2 -
          (constant (key t) - conversation.prediction k t) ^ 2)) ≤
        w * active.card - (epsilon - w) ^ 2 * next.card := by
    calc
      _ ≤ ∑ t ∈ active, if t ∈ next then w - (epsilon - w) ^ 2 else w := by
        exact Finset.sum_le_sum fun t ht => hpointwise t ht
      _ = w * active.card - (epsilon - w) ^ 2 * next.card := by
        rw [Finset.sum_ite]
        have hfilter_next : active.filter (fun t => t ∈ next) = next := by
          ext t
          simp [hnext_active]
        have hfilter_not : active.filter (fun t => ¬t ∈ next) = active \ next := by
          ext t
          simp
        rw [hfilter_next, hfilter_not]
        simp
        have hcard := Finset.card_sdiff_add_card_eq_card hnext_active
        have hcard_real : ((active \ next).card : ℝ) + next.card = active.card := by
          exact_mod_cast hcard
        nlinarith
  have hinactive (t : Fin conversation.horizon) (ht : t ∉ active) :
      bucketed_round_prediction conversation w k t =
        bucketed_round_prediction conversation w (k - 1) t := by
    have htlt : conversation.length t < k := by
      simpa only [active, round_subsequence, Finset.mem_filter,
        Finset.mem_univ, true_and, not_le] using ht
    have htprev : conversation.length t ≤ k - 1 := by omega
    simp only [bucketed_round_prediction, min_eq_right htlt.le,
      min_eq_right htprev]
  have hall_active :
      (∑ t ∈ Finset.univ,
        ((bucketed_round_prediction conversation w k t - conversation.label t) ^ 2 -
          (bucketed_round_prediction conversation w (k - 1) t -
            conversation.label t) ^ 2)) =
        ∑ t ∈ active,
          ((bucketed_round_prediction conversation w k t - conversation.label t) ^ 2 -
            (bucketed_round_prediction conversation w (k - 1) t -
              conversation.label t) ^ 2) := by
    symm
    apply Finset.sum_subset (by simp [active, round_subsequence])
    intro t htuniv htactive
    rw [hinactive t htactive]
    ring
  have hcard_active : (active.card : ℝ) ≤ conversation.horizon := by
    have hcard_nat : active.card ≤ conversation.horizon := by
      simpa using Finset.card_le_univ active
    exact_mod_cast hcard_nat
  change squared_error conversation Finset.univ
      (bucketed_round_prediction conversation w k) ≤
    squared_error conversation Finset.univ
        (bucketed_round_prediction conversation w (k - 1)) -
      (epsilon - w) ^ 2 * next.card + w * conversation.horizon
  unfold squared_error
  have htotal :
      (∑ t ∈ Finset.univ,
          (bucketed_round_prediction conversation w k t - conversation.label t) ^ 2) -
        (∑ t ∈ Finset.univ,
          (bucketed_round_prediction conversation w (k - 1) t -
            conversation.label t) ^ 2) ≤
        w * conversation.horizon - (epsilon - w) ^ 2 * next.card := by
    have hwcard : w * active.card ≤ w * conversation.horizon :=
      mul_le_mul_of_nonneg_left hcard_active hwpos.le
    rw [← Finset.sum_sub_distrib, hall_active, hactive_shift]
    nlinarith
  nlinarith

set_option maxHeartbeats 2000000 in
@[blueprint "lem:calibrated-two-endpoint-both-separated-forward-forward"
  (statement := /-- Let (w,epsilon,q,c,x_0,z_0,x_1,z_1in[0,1]), with (z_jleq cleq z_j+w) and (epsilon^2leq(x_j-z_j)^2) for (j=0,1). Add (epsilon^2) to each endpoint change in squared loss, subtract (3|x_j-q|+w) and (2(q-c)(q-j)), and combine the endpoint expressions with weights (1-q) and (q). The result is nonpositive. -/)
  (proof := /-- Split according to the signs of (x_0-q) and (x_1-q), resolve the absolute values, and expand. The interval hypotheses imply the nonnegativity of (q(1-q)), (w(1-w)), each (x_j(1-x_j)), each (z_j(1-z_j)), and (|x_j-q|(1-|x_j-q|)); the common rounding cell gives (|z_0-z_1|leq w). Together with both gap directions and both bounds on (epsilon^2), these polynomial inequalities prove every branch. -/)
  (title := /-- Direction-free both-separated endpoint estimate -/)
  (latexEnv := "lemma")]
lemma calibrated_two_endpoint_both_separated_forward_forward
    (w epsilon q c x₀ z₀ x₁ z₁ : ℝ)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) (hz₀ : z₀ ∈ Set.Icc (0 : ℝ) 1)
    (hx₁ : x₁ ∈ Set.Icc (0 : ℝ) 1) (hz₁ : z₁ ∈ Set.Icc (0 : ℝ) 1)
    (hz₀c : z₀ ≤ c) (hcz₀ : c ≤ z₀ + w)
    (hz₁c : z₁ ≤ c) (hcz₁ : c ≤ z₁ + w)
    (hsep₀sq : epsilon ^ 2 ≤ (x₀ - z₀) ^ 2)
    (hsep₁sq : epsilon ^ 2 ≤ (x₁ - z₁) ^ 2) :
    (1 - q) *
        (x₀ ^ 2 - z₀ ^ 2 + epsilon ^ 2 -
          3 * |x₀ - q| - w - 2 * (q - c) * q) +
      q *
        ((x₁ - 1) ^ 2 - (z₁ - 1) ^ 2 + epsilon ^ 2 -
          3 * |x₁ - q| - w - 2 * (q - c) * (q - 1)) ≤ 0 := by
  rcases hq with ⟨hq0, hq1⟩
  rcases hc with ⟨hc0, hc1⟩
  rcases hx₀ with ⟨hx₀0, hx₀1⟩
  rcases hz₀ with ⟨hz₀0, hz₀1⟩
  rcases hx₁ with ⟨hx₁0, hx₁1⟩
  rcases hz₁ with ⟨hz₁0, hz₁1⟩
  have hqprod : 0 ≤ q * (1 - q) :=
    mul_nonneg hq0 (sub_nonneg.mpr hq1)
  have hwprod : 0 ≤ w * (1 - w) :=
    mul_nonneg hw0 (sub_nonneg.mpr hw1)
  have hx₀prod : 0 ≤ x₀ * (1 - x₀) :=
    mul_nonneg hx₀0 (sub_nonneg.mpr hx₀1)
  have hx₁prod : 0 ≤ x₁ * (1 - x₁) :=
    mul_nonneg hx₁0 (sub_nonneg.mpr hx₁1)
  have hz₀prod : 0 ≤ z₀ * (1 - z₀) :=
    mul_nonneg hz₀0 (sub_nonneg.mpr hz₀1)
  have hz₁prod : 0 ≤ z₁ * (1 - z₁) :=
    mul_nonneg hz₁0 (sub_nonneg.mpr hz₁1)
  have habs₀le : |x₀ - q| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have habs₁le : |x₁ - q| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have habs₀prod : 0 ≤ |x₀ - q| * (1 - |x₀ - q|) :=
    mul_nonneg (abs_nonneg _) (sub_nonneg.mpr habs₀le)
  have habs₁prod : 0 ≤ |x₁ - q| * (1 - |x₁ - q|) :=
    mul_nonneg (abs_nonneg _) (sub_nonneg.mpr habs₁le)
  have hz₀z₁ : z₀ ≤ z₁ + w := by linarith
  have hz₁z₀ : z₁ ≤ z₀ + w := by linarith
  have hzdistprod :
      0 ≤ (w - (z₀ - z₁)) * (w + (z₀ - z₁)) :=
    mul_nonneg (by linarith) (by linarith)
  have hsep₀q := mul_le_mul_of_nonneg_left hsep₀sq hq0
  have hsep₀one :=
    mul_le_mul_of_nonneg_left hsep₀sq (sub_nonneg.mpr hq1)
  have hsep₁q := mul_le_mul_of_nonneg_left hsep₁sq hq0
  have hsep₁one :=
    mul_le_mul_of_nonneg_left hsep₁sq (sub_nonneg.mpr hq1)
  rcases le_total q x₀ with hqx₀ | hx₀q <;>
    rcases le_total q x₁ with hqx₁ | hx₁q
  · simp only [abs_of_nonneg (sub_nonneg.mpr hqx₀),
      abs_of_nonneg (sub_nonneg.mpr hqx₁)] at habs₀prod habs₁prod ⊢
    ring_nf at hqprod hwprod hx₀prod hx₁prod hz₀prod hz₁prod habs₀prod habs₁prod hzdistprod hsep₀q hsep₀one hsep₁q hsep₁one ⊢
    let s₀ := (x₀ - z₀) ^ 2 - epsilon ^ 2
    let s₁ := (x₁ - z₁) ^ 2 - epsilon ^ 2
    let p := w - z₀ + z₁
    let m := w + z₀ - z₁
    have hs₀ : 0 ≤ s₀ := by dsimp [s₀]; exact sub_nonneg.mpr hsep₀sq
    have hs₁ : 0 ≤ s₁ := by dsimp [s₁]; exact sub_nonneg.mpr hsep₁sq
    have hp : 0 ≤ p := by dsimp [p]; linarith
    have hm : 0 ≤ m := by dsimp [m]; linarith
    have hcert : 0 ≤
        (1 / 2 : ℝ) * m + q * (x₁ - q) + q * z₀ * (x₁ - q) +
        (1 / 2 : ℝ) * q * x₁ * p +
        (1 / 2 : ℝ) * q * (1 - x₁) * m +
        (3 / 2 : ℝ) * q * (1 - x₁) * (x₁ - q) +
        (1 - q) * x₀ * (x₁ - q) +
        (1 / 2 : ℝ) * (1 - q) * (1 - x₀) * (x₀ - q) +
        (1 - q) * z₀ * (x₀ - q) +
        (3 / 2 : ℝ) * (1 - q) * (1 - x₁) * (x₀ - q) +
        (1 / 2 : ℝ) * x₀ * (1 - x₁) * (x₁ - q) +
        x₀ * z₁ * (x₁ - q) +
        (1 / 2 : ℝ) * q * (1 - x₀) * (1 - x₁) * (x₁ - q) +
        (1 / 2 : ℝ) * (1 - q) * x₀ * (1 - x₀) * m +
        (1 / 2 : ℝ) * (1 - q) * x₀ * (1 - x₀) * (x₁ - q) +
        (1 / 4 : ℝ) * (1 - q) * x₀ * z₀ * m +
        (1 / 4 : ℝ) * (1 - q) * x₀ * (1 - z₀) * p +
        (1 / 4 : ℝ) * (1 - q) * x₀ * z₁ * m +
        (1 / 4 : ℝ) * (1 - q) * x₀ * (1 - z₁) * p +
        (1 / 2 : ℝ) * (1 - q) * (1 - x₀) * (1 - x₀) * p +
        (1 / 2 : ℝ) * (1 - q) * (1 - x₀) * (1 - x₀) * (x₀ - q) +
        (1 / 2 : ℝ) * (1 - q) * (1 - x₀) * (1 - x₁) * (x₀ - q) +
        x₀ * (1 - x₀) * z₁ * (x₁ - q) +
        (1 - x₀) * (1 - x₁) * z₁ * (x₀ - q) +
        (1 / 2 : ℝ) * s₀ * (1 - q) +
        (1 / 2 : ℝ) * s₀ * (1 - q) * (1 - x₀) +
        (1 / 2 : ℝ) * s₁ * q + (1 / 2 : ℝ) * s₁ * x₀ +
        (1 / 2 : ℝ) * s₁ * q * (1 - x₀) := by
      positivity
    ring_nf at hcert
    linarith [hcert]
  · simp only [abs_of_nonneg (sub_nonneg.mpr hqx₀),
      abs_of_nonpos (sub_nonpos.mpr hx₁q)] at habs₀prod habs₁prod ⊢
    ring_nf at hqprod hwprod hx₀prod hx₁prod hz₀prod hz₁prod habs₀prod habs₁prod hzdistprod hsep₀q hsep₀one hsep₁q hsep₁one ⊢
    let s₀ := (x₀ - z₀) ^ 2 - epsilon ^ 2
    let s₁ := (x₁ - z₁) ^ 2 - epsilon ^ 2
    let p := w - z₀ + z₁
    let m := w + z₀ - z₁
    have hs₀ : 0 ≤ s₀ := by dsimp [s₀]; exact sub_nonneg.mpr hsep₀sq
    have hs₁ : 0 ≤ s₁ := by dsimp [s₁]; exact sub_nonneg.mpr hsep₁sq
    have hp : 0 ≤ p := by dsimp [p]; linarith
    have hm : 0 ≤ m := by dsimp [m]; linarith
    by_cases hhalf : q ≤ (1 / 2 : ℝ)
    · have hh : 0 ≤ 1 - 2 * q := by linarith
      have hcert : 0 ≤
          (1 / 32 : ℝ) * p + (1 / 2 : ℝ) * m +
          (3 / 16 : ℝ) * (1 - x₀) * p + (1 / 32 : ℝ) * z₀ * p +
          (1 / 8 : ℝ) * z₁ * p + (1 / 2 : ℝ) * (x₀ - q) * (1 - 2 * q) +
          (3 / 2 : ℝ) * q * q * (q - x₁) +
          (1 / 16 : ℝ) * q * (1 - x₀) * m +
          (3 / 16 : ℝ) * q * z₀ * p + (1 / 4 : ℝ) * q * (1 - z₀) * m +
          q * x₁ * (q - x₁) + (1 / 4 : ℝ) * q * (1 - z₁) * m +
          (3 / 4 : ℝ) * q * (1 - z₁) * (q - x₁) +
          (7 / 16 : ℝ) * (1 - q) * x₀ * m +
          (1 / 2 : ℝ) * (1 - q) * (1 - x₀) * (x₀ - q) +
          (1 / 4 : ℝ) * (1 - q) * z₀ * (x₀ - q) +
          (3 / 4 : ℝ) * (1 - q) * (x₀ - q) * (1 - 2 * q) +
          (1 / 4 : ℝ) * (1 - w) * (x₀ - q) * (1 - 2 * q) +
          (1 / 2 : ℝ) * x₀ * x₁ * (q - x₁) +
          (1 / 4 : ℝ) * x₀ * (1 - z₁) * (q - x₁) +
          (1 / 2 : ℝ) * (1 - x₀) * (1 - x₀) * (x₀ - q) +
          (1 - x₀) * z₀ * (x₀ - q) +
          (1 / 2 : ℝ) * (1 - x₀) * (x₀ - q) * (1 - 2 * q) +
          (1 / 2 : ℝ) * z₀ * z₀ * (x₀ - q) +
          (1 / 8 : ℝ) * z₀ * (x₀ - q) * (1 - 2 * q) +
          (1 / 32 : ℝ) * (1 - z₀) * p * (1 - 2 * q) +
          (3 / 4 : ℝ) * x₁ * z₁ * (x₀ - q) +
          (1 / 4 : ℝ) * x₁ * (x₀ - q) * (1 - 2 * q) +
          (1 / 2 : ℝ) * z₁ * (1 - z₁) * (x₀ - q) +
          (1 / 8 : ℝ) * z₁ * (x₀ - q) * (1 - 2 * q) +
          (1 / 8 : ℝ) * (1 - z₁) * p * (1 - 2 * q) +
          (1 / 8 : ℝ) * p * (1 - 2 * q) * (1 - 2 * q) +
          (1 / 2 : ℝ) * s₀ + (1 / 2 : ℝ) * s₀ * (1 - x₀) +
          (1 / 2 : ℝ) * s₁ * x₀ := by
        positivity
      ring_nf at hcert
      linarith [hcert]
    · have hh : 0 ≤ 2 * q - 1 := by linarith
      have hcert : 0 ≤
          (1 / 16 : ℝ) * w + (15 / 32 : ℝ) * m +
          (1 / 8 : ℝ) * (1 - z₀) * p + (3 / 16 : ℝ) * x₁ * p +
          (1 / 32 : ℝ) * (1 - z₁) * p +
          (9 / 16 : ℝ) * (q - x₁) * (2 * q - 1) +
          (1 / 8 : ℝ) * q * (1 - q) * m +
          (1 / 2 : ℝ) * q * x₁ * (q - x₁) +
          (3 / 8 : ℝ) * q * (1 - x₁) * m +
          (1 / 4 : ℝ) * q * (1 - z₁) * (q - x₁) +
          (3 / 4 : ℝ) * q * (q - x₁) * (2 * q - 1) +
          (3 / 2 : ℝ) * (1 - q) * (1 - q) * (x₀ - q) +
          (1 - q) * (1 - x₀) * (x₀ - q) +
          (1 / 4 : ℝ) * (1 - q) * z₀ * m +
          (3 / 4 : ℝ) * (1 - q) * z₀ * (x₀ - q) +
          (1 / 4 : ℝ) * (1 - q) * z₁ * m +
          (3 / 16 : ℝ) * (1 - q) * (1 - z₁) * p +
          (3 / 16 : ℝ) * (1 - w) * (q - x₁) * (2 * q - 1) +
          (3 / 4 : ℝ) * (1 - x₀) * (1 - z₀) * (q - x₁) +
          (1 / 2 : ℝ) * (1 - x₀) * (1 - x₁) * (x₀ - q) +
          (1 / 4 : ℝ) * (1 - x₀) * (q - x₁) * (2 * q - 1) +
          (1 / 2 : ℝ) * z₀ * (1 - z₀) * (q - x₁) +
          (1 / 4 : ℝ) * z₀ * (1 - x₁) * (x₀ - q) +
          (1 / 8 : ℝ) * z₀ * p * (2 * q - 1) +
          (1 / 16 : ℝ) * (1 - z₀) * (q - x₁) * (2 * q - 1) +
          (1 / 2 : ℝ) * x₁ * x₁ * (q - x₁) +
          x₁ * (1 - z₁) * (q - x₁) +
          (1 / 2 : ℝ) * x₁ * (q - x₁) * (2 * q - 1) +
          (1 / 32 : ℝ) * z₁ * p * (2 * q - 1) +
          (1 / 2 : ℝ) * (1 - z₁) * (1 - z₁) * (q - x₁) +
          (3 / 16 : ℝ) * (1 - z₁) * (q - x₁) * (2 * q - 1) +
          (1 / 8 : ℝ) * p * (2 * q - 1) * (2 * q - 1) +
          (1 / 2 : ℝ) * s₀ * (1 - x₁) + (1 / 2 : ℝ) * s₁ +
          (1 / 2 : ℝ) * s₁ * x₁ := by
        positivity
      ring_nf at hcert
      linarith [hcert]
  · simp only [abs_of_nonpos (sub_nonpos.mpr hx₀q),
      abs_of_nonneg (sub_nonneg.mpr hqx₁)] at habs₀prod habs₁prod ⊢
    ring_nf at hqprod hwprod hx₀prod hx₁prod hz₀prod hz₁prod habs₀prod habs₁prod hzdistprod hsep₀q hsep₀one hsep₁q hsep₁one ⊢
    let s₀ := (x₀ - z₀) ^ 2 - epsilon ^ 2
    let s₁ := (x₁ - z₁) ^ 2 - epsilon ^ 2
    let p := w - z₀ + z₁
    let m := w + z₀ - z₁
    have hs₀ : 0 ≤ s₀ := by dsimp [s₀]; exact sub_nonneg.mpr hsep₀sq
    have hs₁ : 0 ≤ s₁ := by dsimp [s₁]; exact sub_nonneg.mpr hsep₁sq
    have hp : 0 ≤ p := by dsimp [p]; linarith
    have hm : 0 ≤ m := by dsimp [m]; linarith
    have hcert : 0 ≤
        (1 / 3 : ℝ) * w + (1 / 3 : ℝ) * m + q * (x₁ - q) +
        (1 - q) * (q - x₀) + q * (1 - q) * m +
        2 * q * (1 - q) * (q - x₀) +
        2 * q * (1 - q) * (x₁ - q) +
        2 * q * (1 - x₁) * (x₁ - q) +
        2 * q * z₁ * (x₁ - q) +
        2 * (1 - q) * x₀ * (q - x₀) +
        2 * (1 - q) * (1 - z₀) * (q - x₀) +
        (1 / 3 : ℝ) * q * q * q * p +
        (1 / 3 : ℝ) * (1 - q) * (1 - q) * (1 - q) * p +
        s₀ * (1 - q) + s₁ * q := by
      positivity
    ring_nf at hcert
    linarith [hcert]
  · simp only [abs_of_nonpos (sub_nonpos.mpr hx₀q),
      abs_of_nonpos (sub_nonpos.mpr hx₁q)] at habs₀prod habs₁prod ⊢
    ring_nf at hqprod hwprod hx₀prod hx₁prod hz₀prod hz₁prod habs₀prod habs₁prod hzdistprod hsep₀q hsep₀one hsep₁q hsep₁one ⊢
    let s₀ := (x₀ - z₀) ^ 2 - epsilon ^ 2
    let s₁ := (x₁ - z₁) ^ 2 - epsilon ^ 2
    let p := w - z₀ + z₁
    let m := w + z₀ - z₁
    have hs₀ : 0 ≤ s₀ := by dsimp [s₀]; exact sub_nonneg.mpr hsep₀sq
    have hs₁ : 0 ≤ s₁ := by dsimp [s₁]; exact sub_nonneg.mpr hsep₁sq
    have hp : 0 ≤ p := by dsimp [p]; linarith
    have hm : 0 ≤ m := by dsimp [m]; linarith
    have hcert : 0 ≤
        (1 / 2 : ℝ) * m + (1 - q) * (q - x₀) +
        (1 / 2 : ℝ) * q * (1 - q) * (q - x₀) +
        (3 / 2 : ℝ) * q * x₀ * (q - x₁) +
        (1 / 2 : ℝ) * q * x₁ * (q - x₁) +
        (1 / 2 : ℝ) * q * (1 - x₁) * (q - x₀) +
        (1 / 2 : ℝ) * (1 - q) * x₀ * m +
        2 * (1 - q) * x₀ * (q - x₀) +
        (1 / 2 : ℝ) * (1 - q) * (1 - x₀) * p +
        x₀ * (1 - z₁) * (q - x₁) +
        (1 - z₀) * (1 - x₁) * (q - x₀) +
        (1 - x₁) * (1 - z₁) * (q - x₀) +
        (1 / 2 : ℝ) * q * q * x₁ * (q - x₁) +
        (1 / 2 : ℝ) * q * q * (1 - x₁) * (q - x₀) +
        (1 / 2 : ℝ) * q * x₀ * (1 - x₁) * (q - x₀) +
        (1 / 4 : ℝ) * q * z₀ * (1 - x₁) * p +
        (1 / 4 : ℝ) * q * (1 - z₀) * (1 - x₁) * m +
        (1 / 2 : ℝ) * q * x₁ * x₁ * p +
        (1 / 2 : ℝ) * q * x₁ * x₁ * (q - x₁) +
        (1 / 2 : ℝ) * q * x₁ * (1 - x₁) * m +
        (1 / 4 : ℝ) * q * (1 - x₁) * z₁ * p +
        (1 / 4 : ℝ) * q * (1 - x₁) * (1 - z₁) * m +
        x₀ * (1 - z₀) * x₁ * (q - x₁) +
        (1 - z₀) * x₁ * (1 - x₁) * (q - x₀) +
        s₀ * (1 - q) + (1 / 2 : ℝ) * s₀ * q * (1 - x₁) +
        (1 / 2 : ℝ) * s₁ * q + (1 / 2 : ℝ) * s₁ * q * x₁ := by
      positivity
    ring_nf at hcert
    linarith [hcert]

set_option maxHeartbeats 10000000 in
@[blueprint "lem:calibrated-two-endpoint-both-separated-backward-forward"
  (statement := /-- Let (w,epsilon,q,c,x_0,z_0,x_1,z_1in[0,1]), with (z_jleq cleq z_j+w), (epsilon^2leq(x_j-z_j)^2), (x_0leq z_0), and (z_1leq x_1). Add (epsilon^2) to each endpoint change in squared loss, subtract (3|x_j-q|+w) and (2(q-c)(q-j)), and combine the endpoint expressions with weights (1-q) and (q). The result is nonpositive. -/)
  (proof := /-- Apply \cref{lem:calibrated-two-endpoint-both-separated-forward-forward}; its direction-free hypotheses include the present backward--forward case. -/)
  (title := /-- Backward-forward both-separated endpoint estimate -/)
  (latexEnv := "lemma")]
lemma calibrated_two_endpoint_both_separated_backward_forward
    (w epsilon q c x₀ z₀ x₁ z₁ : ℝ)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) (hz₀ : z₀ ∈ Set.Icc (0 : ℝ) 1)
    (hx₁ : x₁ ∈ Set.Icc (0 : ℝ) 1) (hz₁ : z₁ ∈ Set.Icc (0 : ℝ) 1)
    (hz₀c : z₀ ≤ c) (hcz₀ : c ≤ z₀ + w)
    (hz₁c : z₁ ≤ c) (hcz₁ : c ≤ z₁ + w)
    (hx₀z₀ : x₀ ≤ z₀) (hz₁x₁ : z₁ ≤ x₁)
    (hsep₀sq : epsilon ^ 2 ≤ (x₀ - z₀) ^ 2)
    (hsep₁sq : epsilon ^ 2 ≤ (x₁ - z₁) ^ 2) :
    (1 - q) *
        (x₀ ^ 2 - z₀ ^ 2 + epsilon ^ 2 -
          3 * |x₀ - q| - w - 2 * (q - c) * q) +
      q *
        ((x₁ - 1) ^ 2 - (z₁ - 1) ^ 2 + epsilon ^ 2 -
          3 * |x₁ - q| - w - 2 * (q - c) * (q - 1)) ≤ 0 := by
  exact calibrated_two_endpoint_both_separated_forward_forward
    w epsilon q c x₀ z₀ x₁ z₁ hw0 hw1 hq hc hx₀ hz₀ hx₁ hz₁
    hz₀c hcz₀ hz₁c hcz₁ hsep₀sq hsep₁sq

set_option maxHeartbeats 10000000 in
@[blueprint "lem:calibrated-two-endpoint-both-separated-forward-backward"
  (statement := /-- Let (w,epsilon,q,c,x_0,z_0,x_1,z_1in[0,1]), with (z_jleq cleq z_j+w), (epsilon^2leq(x_j-z_j)^2), (z_0leq x_0), and (x_1leq z_1). Add (epsilon^2) to each endpoint change in squared loss, subtract (3|x_j-q|+w) and (2(q-c)(q-j)), and combine the endpoint expressions with weights (1-q) and (q). The result is nonpositive. -/)
  (proof := /-- Apply \cref{lem:calibrated-two-endpoint-both-separated-forward-forward}; its direction-free hypotheses include the present forward--backward case. -/)
  (title := /-- Forward-backward both-separated endpoint estimate -/)
  (latexEnv := "lemma")]
lemma calibrated_two_endpoint_both_separated_forward_backward
    (w epsilon q c x₀ z₀ x₁ z₁ : ℝ)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) (hz₀ : z₀ ∈ Set.Icc (0 : ℝ) 1)
    (hx₁ : x₁ ∈ Set.Icc (0 : ℝ) 1) (hz₁ : z₁ ∈ Set.Icc (0 : ℝ) 1)
    (hz₀c : z₀ ≤ c) (hcz₀ : c ≤ z₀ + w)
    (hz₁c : z₁ ≤ c) (hcz₁ : c ≤ z₁ + w)
    (hz₀x₀ : z₀ ≤ x₀) (hx₁z₁ : x₁ ≤ z₁)
    (hsep₀sq : epsilon ^ 2 ≤ (x₀ - z₀) ^ 2)
    (hsep₁sq : epsilon ^ 2 ≤ (x₁ - z₁) ^ 2) :
    (1 - q) *
        (x₀ ^ 2 - z₀ ^ 2 + epsilon ^ 2 -
          3 * |x₀ - q| - w - 2 * (q - c) * q) +
      q *
        ((x₁ - 1) ^ 2 - (z₁ - 1) ^ 2 + epsilon ^ 2 -
          3 * |x₁ - q| - w - 2 * (q - c) * (q - 1)) ≤ 0 := by
  rcases hq with ⟨hq0, hq1⟩
  rcases hc with ⟨hc0, hc1⟩
  rcases hx₀ with ⟨hx₀0, hx₀1⟩
  rcases hz₀ with ⟨hz₀0, hz₀1⟩
  rcases hx₁ with ⟨hx₁0, hx₁1⟩
  rcases hz₁ with ⟨hz₁0, hz₁1⟩
  have hqprod : 0 ≤ q * (1 - q) :=
    mul_nonneg hq0 (sub_nonneg.mpr hq1)
  have hwprod : 0 ≤ w * (1 - w) :=
    mul_nonneg hw0 (sub_nonneg.mpr hw1)
  have hx₀prod : 0 ≤ x₀ * (1 - x₀) :=
    mul_nonneg hx₀0 (sub_nonneg.mpr hx₀1)
  have hx₁prod : 0 ≤ x₁ * (1 - x₁) :=
    mul_nonneg hx₁0 (sub_nonneg.mpr hx₁1)
  have hz₀prod : 0 ≤ z₀ * (1 - z₀) :=
    mul_nonneg hz₀0 (sub_nonneg.mpr hz₀1)
  have hz₁prod : 0 ≤ z₁ * (1 - z₁) :=
    mul_nonneg hz₁0 (sub_nonneg.mpr hz₁1)
  have habs₀le : |x₀ - q| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have habs₁le : |x₁ - q| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have habs₀prod : 0 ≤ |x₀ - q| * (1 - |x₀ - q|) :=
    mul_nonneg (abs_nonneg _) (sub_nonneg.mpr habs₀le)
  have habs₁prod : 0 ≤ |x₁ - q| * (1 - |x₁ - q|) :=
    mul_nonneg (abs_nonneg _) (sub_nonneg.mpr habs₁le)
  have hz₀z₁ : z₀ ≤ z₁ + w := by linarith
  have hz₁z₀ : z₁ ≤ z₀ + w := by linarith
  have hzdistprod :
      0 ≤ (w - (z₀ - z₁)) * (w + (z₀ - z₁)) :=
    mul_nonneg (by linarith) (by linarith)
  exact calibrated_two_endpoint_both_separated_forward_forward
    w epsilon q c x₀ z₀ x₁ z₁ hw0 hw1 ⟨hq0, hq1⟩ ⟨hc0, hc1⟩
    ⟨hx₀0, hx₀1⟩ ⟨hz₀0, hz₀1⟩ ⟨hx₁0, hx₁1⟩ ⟨hz₁0, hz₁1⟩
    hz₀c hcz₀ hz₁c hcz₁ hsep₀sq hsep₁sq

set_option maxHeartbeats 10000000 in
@[blueprint "lem:calibrated-two-endpoint-both-separated-backward-backward"
  (statement := /-- Let (w,epsilon,q,c,x_0,z_0,x_1,z_1in[0,1]), with (z_jleq cleq z_j+w), (epsilon^2leq(x_j-z_j)^2), and (x_jleq z_j) for (j=0,1). Add (epsilon^2) to each endpoint change in squared loss, subtract (3|x_j-q|+w) and (2(q-c)(q-j)), and combine the endpoint expressions with weights (1-q) and (q). The result is nonpositive. -/)
  (proof := /-- Apply \cref{lem:calibrated-two-endpoint-both-separated-forward-forward}; its direction-free hypotheses include the present backward--backward case. -/)
  (title := /-- Backward-backward both-separated endpoint estimate -/)
  (latexEnv := "lemma")]
lemma calibrated_two_endpoint_both_separated_backward_backward
    (w epsilon q c x₀ z₀ x₁ z₁ : ℝ)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) (hz₀ : z₀ ∈ Set.Icc (0 : ℝ) 1)
    (hx₁ : x₁ ∈ Set.Icc (0 : ℝ) 1) (hz₁ : z₁ ∈ Set.Icc (0 : ℝ) 1)
    (hz₀c : z₀ ≤ c) (hcz₀ : c ≤ z₀ + w)
    (hz₁c : z₁ ≤ c) (hcz₁ : c ≤ z₁ + w)
    (hx₀z₀ : x₀ ≤ z₀) (hx₁z₁ : x₁ ≤ z₁)
    (hsep₀sq : epsilon ^ 2 ≤ (x₀ - z₀) ^ 2)
    (hsep₁sq : epsilon ^ 2 ≤ (x₁ - z₁) ^ 2) :
    (1 - q) *
        (x₀ ^ 2 - z₀ ^ 2 + epsilon ^ 2 -
          3 * |x₀ - q| - w - 2 * (q - c) * q) +
      q *
        ((x₁ - 1) ^ 2 - (z₁ - 1) ^ 2 + epsilon ^ 2 -
          3 * |x₁ - q| - w - 2 * (q - c) * (q - 1)) ≤ 0 := by
  rcases hq with ⟨hq0, hq1⟩
  rcases hc with ⟨hc0, hc1⟩
  rcases hx₀ with ⟨hx₀0, hx₀1⟩
  rcases hz₀ with ⟨hz₀0, hz₀1⟩
  rcases hx₁ with ⟨hx₁0, hx₁1⟩
  rcases hz₁ with ⟨hz₁0, hz₁1⟩
  have hqprod : 0 ≤ q * (1 - q) :=
    mul_nonneg hq0 (sub_nonneg.mpr hq1)
  have hwprod : 0 ≤ w * (1 - w) :=
    mul_nonneg hw0 (sub_nonneg.mpr hw1)
  have hx₀prod : 0 ≤ x₀ * (1 - x₀) :=
    mul_nonneg hx₀0 (sub_nonneg.mpr hx₀1)
  have hx₁prod : 0 ≤ x₁ * (1 - x₁) :=
    mul_nonneg hx₁0 (sub_nonneg.mpr hx₁1)
  have hz₀prod : 0 ≤ z₀ * (1 - z₀) :=
    mul_nonneg hz₀0 (sub_nonneg.mpr hz₀1)
  have hz₁prod : 0 ≤ z₁ * (1 - z₁) :=
    mul_nonneg hz₁0 (sub_nonneg.mpr hz₁1)
  have habs₀le : |x₀ - q| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have habs₁le : |x₁ - q| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have habs₀prod : 0 ≤ |x₀ - q| * (1 - |x₀ - q|) :=
    mul_nonneg (abs_nonneg _) (sub_nonneg.mpr habs₀le)
  have habs₁prod : 0 ≤ |x₁ - q| * (1 - |x₁ - q|) :=
    mul_nonneg (abs_nonneg _) (sub_nonneg.mpr habs₁le)
  have hz₀z₁ : z₀ ≤ z₁ + w := by linarith
  have hz₁z₀ : z₁ ≤ z₀ + w := by linarith
  have hzdistprod :
      0 ≤ (w - (z₀ - z₁)) * (w + (z₀ - z₁)) :=
    mul_nonneg (by linarith) (by linarith)
  exact calibrated_two_endpoint_both_separated_forward_forward
    w epsilon q c x₀ z₀ x₁ z₁ hw0 hw1 ⟨hq0, hq1⟩ ⟨hc0, hc1⟩
    ⟨hx₀0, hx₀1⟩ ⟨hz₀0, hz₀1⟩ ⟨hx₁0, hx₁1⟩ ⟨hz₁0, hz₁1⟩
    hz₀c hcz₀ hz₁c hcz₁ hsep₀sq hsep₁sq

set_option maxHeartbeats 100000000 in
@[blueprint "lem:calibrated-two-endpoint-only-zero-separated"
  (statement := /-- Let (w,epsilon,q,c,x_0,z_0,x_1,z_1in[0,1]), with (z_jleq cleq z_j+w) for (j=0,1), ((x_1-z_1)^2leqepsilon^2), and (epsilon^2leq(x_0-z_0)^2). Charge (epsilon^2) only in the label-(0) change in squared loss, subtract (3|x_j-q|+w) and (2(q-c)(q-j)) from each endpoint expression, and combine them with weights (1-q) and (q). The result is nonpositive. -/)
  (proof := /-- Replace the label-zero separation charge by \((x_0-z_0)^2\), so that its change in squared loss becomes \(2x_0(x_0-z_0)\). First prove the stronger common-surrogate estimate in which \(z_0=z_1=z\). The label-one expression is maximized at \(x_1=q\). The label-zero expression is maximized either at \(x_0=q\) or at \(x_0=1\); in the latter case its excess is absorbed by the negative common-surrogate square. Finally choose the common surrogate to be \(z_0\) when \(q\leq1/2\), and \(z_1\) otherwise. Since \(|z_0-z_1|\leq w\), changing the other surrogate costs at most \(w\). -/)
  (title := /-- Label-zero-only separated endpoint estimate -/)
  (latexEnv := "lemma")]
lemma calibrated_two_endpoint_only_zero_separated
    (w epsilon q c x₀ z₀ x₁ z₁ : ℝ)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) (hz₀ : z₀ ∈ Set.Icc (0 : ℝ) 1)
    (hx₁ : x₁ ∈ Set.Icc (0 : ℝ) 1) (hz₁ : z₁ ∈ Set.Icc (0 : ℝ) 1)
    (hz₀c : z₀ ≤ c) (hcz₀ : c ≤ z₀ + w)
    (hz₁c : z₁ ≤ c) (hcz₁ : c ≤ z₁ + w)
    (hsep₀sq : epsilon ^ 2 ≤ (x₀ - z₀) ^ 2)
    (hnotsep₁sq : (x₁ - z₁) ^ 2 ≤ epsilon ^ 2) :
    (1 - q) *
        (x₀ ^ 2 - z₀ ^ 2 + epsilon ^ 2 -
          3 * |x₀ - q| - w - 2 * (q - c) * q) +
      q *
        ((x₁ - 1) ^ 2 - (z₁ - 1) ^ 2 -
          3 * |x₁ - q| - w - 2 * (q - c) * (q - 1)) ≤ 0 := by
  rcases hq with ⟨hq0, hq1⟩
  rcases hx₀ with ⟨hx₀0, hx₀1⟩
  rcases hz₀ with ⟨hz₀0, hz₀1⟩
  rcases hx₁ with ⟨hx₁0, hx₁1⟩
  rcases hz₁ with ⟨hz₁0, hz₁1⟩
  have hz₀z₁ : z₀ ≤ z₁ + w := by linarith
  have hz₁z₀ : z₁ ≤ z₀ + w := by linarith
  have hweight0 : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have hzero :
      x₀ ^ 2 - z₀ ^ 2 + epsilon ^ 2 ≤ 2 * x₀ * (x₀ - z₀) := by
    nlinarith [hsep₀sq]
  have hcommon (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
      (1 - q) * (2 * x₀ * (x₀ - z) - 3 * |x₀ - q|) +
        q * ((x₁ - 1) ^ 2 - (z - 1) ^ 2 - 3 * |x₁ - q|) ≤ 0 := by
    rcases hz with ⟨hz0, hz1⟩
    have hone :
        (x₁ - 1) ^ 2 - (z - 1) ^ 2 - 3 * |x₁ - q| ≤
          (q - 1) ^ 2 - (z - 1) ^ 2 := by
      rcases le_total q x₁ with hqx₁ | hx₁q
      · have hprod : 0 ≤ (x₁ - q) * (5 - q - x₁) :=
          mul_nonneg (sub_nonneg.mpr hqx₁) (by linarith)
        rw [abs_of_nonneg (sub_nonneg.mpr hqx₁)]
        nlinarith
      · have hprod : 0 ≤ (q - x₁) * (q + x₁ + 1) :=
          mul_nonneg (sub_nonneg.mpr hx₁q) (by positivity)
        rw [abs_of_nonpos (sub_nonpos.mpr hx₁q)]
        nlinarith
    have hone_weighted := mul_le_mul_of_nonneg_left hone hq0
    rcases le_total x₀ q with hx₀q | hqx₀
    · have hprod : 0 ≤
          (q - x₀) * (2 * q + 2 * x₀ - 2 * z + 3) :=
        mul_nonneg (sub_nonneg.mpr hx₀q) (by linarith)
      have hzero_q :
          2 * x₀ * (x₀ - z) - 3 * |x₀ - q| ≤
            2 * q * (q - z) := by
        rw [abs_of_nonpos (sub_nonpos.mpr hx₀q)]
        nlinarith
      have hzero_weighted :=
        mul_le_mul_of_nonneg_left hzero_q hweight0
      nlinarith [sq_nonneg (q - z)]
    · rw [abs_of_nonneg (sub_nonneg.mpr hqx₀)]
      by_cases hmiddle : 2 * (x₀ + q - z) ≤ 3
      · have hprod : 0 ≤
            (x₀ - q) * (3 - 2 * (x₀ + q - z)) :=
          mul_nonneg (sub_nonneg.mpr hqx₀) (sub_nonneg.mpr hmiddle)
        have hzero_q :
            2 * x₀ * (x₀ - z) - 3 * (x₀ - q) ≤
              2 * q * (q - z) := by
          nlinarith
        have hzero_weighted :=
          mul_le_mul_of_nonneg_left hzero_q hweight0
        nlinarith [sq_nonneg (q - z)]
      · have hfactor : 0 ≤ 2 * x₀ - 2 * z - 1 := by
          linarith
        have hprod : 0 ≤ (1 - x₀) * (2 * x₀ - 2 * z - 1) :=
          mul_nonneg (sub_nonneg.mpr hx₀1) hfactor
        have hzero_one :
            2 * x₀ * (x₀ - z) - 3 * (x₀ - q) ≤
              3 * q - 1 - 2 * z := by
          nlinarith
        have hzero_weighted :=
          mul_le_mul_of_nonneg_left hzero_one hweight0
        have hhalf : (1 / 2 : ℝ) ≤ q := by
          linarith
        have hdiffhalf : (1 / 2 : ℝ) ≤ q - z := by
          linarith
        have htwodiff : 0 ≤ 2 * (q - z) - 1 := by
          linarith
        have htwodiff_sq : 2 * (q - z) - 1 ≤ (q - z) ^ 2 := by
          nlinarith [sq_nonneg (q - z - 1)]
        have hweight_sq : (1 - q) ^ 2 ≤ q := by
          have hqprod : 0 ≤ q * (1 - q) :=
            mul_nonneg hq0 hweight0
          nlinarith
        have hfirst := mul_le_mul_of_nonneg_left htwodiff_sq
          (sq_nonneg (1 - q))
        have hsecond := mul_le_mul_of_nonneg_right hweight_sq
          (sq_nonneg (q - z))
        nlinarith
  have hzero_weighted := mul_le_mul_of_nonneg_left hzero hweight0
  by_cases hqhalf : q ≤ (1 / 2 : ℝ)
  · have hbase := hcommon z₀ ⟨hz₀0, hz₀1⟩
    have hshift : q * ((z₀ - 1) ^ 2 - (z₁ - 1) ^ 2) ≤ w := by
      rcases le_total z₀ z₁ with hz₀z₁' | hz₁z₀'
      · have hfactor0 : 0 ≤ 2 - z₀ - z₁ := by linarith
        have hfactor1 : 2 - z₀ - z₁ ≤ 2 := by linarith
        have hdiff0 : 0 ≤ (z₀ - 1) ^ 2 - (z₁ - 1) ^ 2 := by
          have hprod := mul_nonneg (sub_nonneg.mpr hz₀z₁') hfactor0
          nlinarith
        have hdiff2 : (z₀ - 1) ^ 2 - (z₁ - 1) ^ 2 ≤ 2 * w := by
          have hprod := mul_le_mul_of_nonneg_left hfactor1
            (sub_nonneg.mpr hz₀z₁')
          nlinarith
        have hmul := mul_le_mul_of_nonneg_right hqhalf hdiff0
        nlinarith [mul_le_mul_of_nonneg_left hdiff2 hq0]
      · have hdiff : (z₀ - 1) ^ 2 - (z₁ - 1) ^ 2 ≤ 0 := by
          have hprod : 0 ≤ (z₀ - z₁) * (2 - z₀ - z₁) :=
            mul_nonneg (sub_nonneg.mpr hz₁z₀') (by linarith)
          nlinarith
        exact le_trans (mul_nonpos_of_nonneg_of_nonpos hq0 hdiff) hw0
    nlinarith
  · have hbase := hcommon z₁ ⟨hz₁0, hz₁1⟩
    have hhalf : (1 / 2 : ℝ) ≤ q := by linarith
    have hweighthalf : 1 - q ≤ (1 / 2 : ℝ) := by linarith
    have hshift : (1 - q) * (2 * x₀ * (z₁ - z₀)) ≤ w := by
      rcases le_total z₀ z₁ with hz₀z₁' | hz₁z₀'
      · have hcoeff : 2 * (1 - q) * x₀ ≤ 1 := by
          have hmul := mul_le_mul hweighthalf hx₀1 hx₀0 (by norm_num)
          nlinarith
        have hmul := mul_le_mul_of_nonneg_right hcoeff
          (sub_nonneg.mpr hz₀z₁')
        nlinarith
      · have hnonpos : 2 * x₀ * (z₁ - z₀) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) hx₀0)
            (sub_nonpos.mpr hz₁z₀')
        exact le_trans (mul_nonpos_of_nonneg_of_nonpos hweight0 hnonpos) hw0
    nlinarith

set_option maxHeartbeats 10000000 in
@[blueprint "lem:calibrated-two-endpoint-only-one-separated"
  (statement := /-- Let (w,epsilon,q,c,x_0,z_0,x_1,z_1in[0,1]), with (z_jleq cleq z_j+w) for (j=0,1), ((x_0-z_0)^2leqepsilon^2), and (epsilon^2leq(x_1-z_1)^2). Charge (epsilon^2) only in the label-(1) change in squared loss, subtract (3|x_j-q|+w) and (2(q-c)(q-j)) from each endpoint expression, and combine them with weights (1-q) and (q). The result is nonpositive. -/)
  (proof := /-- Complement both endpoint pairs and interchange labels. The transformed hypotheses satisfy \cref{lem:calibrated-two-endpoint-only-zero-separated}; expanding its conclusion gives the label-one-only estimate. -/)
  (title := /-- Label-one-only separated endpoint estimate -/)
  (latexEnv := "lemma")]
lemma calibrated_two_endpoint_only_one_separated
    (w epsilon q c x₀ z₀ x₁ z₁ : ℝ)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) (hz₀ : z₀ ∈ Set.Icc (0 : ℝ) 1)
    (hx₁ : x₁ ∈ Set.Icc (0 : ℝ) 1) (hz₁ : z₁ ∈ Set.Icc (0 : ℝ) 1)
    (hz₀c : z₀ ≤ c) (hcz₀ : c ≤ z₀ + w)
    (hz₁c : z₁ ≤ c) (hcz₁ : c ≤ z₁ + w)
    (hnotsep₀sq : (x₀ - z₀) ^ 2 ≤ epsilon ^ 2)
    (hsep₁sq : epsilon ^ 2 ≤ (x₁ - z₁) ^ 2) :
    (1 - q) *
        (x₀ ^ 2 - z₀ ^ 2 -
          3 * |x₀ - q| - w - 2 * (q - c) * q) +
      q *
        ((x₁ - 1) ^ 2 - (z₁ - 1) ^ 2 + epsilon ^ 2 -
          3 * |x₁ - q| - w - 2 * (q - c) * (q - 1)) ≤ 0 := by
  rcases hq with ⟨hq0, hq1⟩
  rcases hc with ⟨hc0, hc1⟩
  rcases hx₀ with ⟨hx₀0, hx₀1⟩
  rcases hz₀ with ⟨hz₀0, hz₀1⟩
  rcases hx₁ with ⟨hx₁0, hx₁1⟩
  rcases hz₁ with ⟨hz₁0, hz₁1⟩
  have hqprod : 0 ≤ q * (1 - q) :=
    mul_nonneg hq0 (sub_nonneg.mpr hq1)
  have hwprod : 0 ≤ w * (1 - w) :=
    mul_nonneg hw0 (sub_nonneg.mpr hw1)
  have hx₀prod : 0 ≤ x₀ * (1 - x₀) :=
    mul_nonneg hx₀0 (sub_nonneg.mpr hx₀1)
  have hx₁prod : 0 ≤ x₁ * (1 - x₁) :=
    mul_nonneg hx₁0 (sub_nonneg.mpr hx₁1)
  have hz₀prod : 0 ≤ z₀ * (1 - z₀) :=
    mul_nonneg hz₀0 (sub_nonneg.mpr hz₀1)
  have hz₁prod : 0 ≤ z₁ * (1 - z₁) :=
    mul_nonneg hz₁0 (sub_nonneg.mpr hz₁1)
  have habs₀le : |x₀ - q| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have habs₁le : |x₁ - q| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have habs₀prod : 0 ≤ |x₀ - q| * (1 - |x₀ - q|) :=
    mul_nonneg (abs_nonneg _) (sub_nonneg.mpr habs₀le)
  have habs₁prod : 0 ≤ |x₁ - q| * (1 - |x₁ - q|) :=
    mul_nonneg (abs_nonneg _) (sub_nonneg.mpr habs₁le)
  have hz₀z₁ : z₀ ≤ z₁ + w := by linarith
  have hz₁z₀ : z₁ ≤ z₀ + w := by linarith
  have hzdistprod :
      0 ≤ (w - (z₀ - z₁)) * (w + (z₀ - z₁)) :=
    mul_nonneg (by linarith) (by linarith)
  let c' := max (1 - z₁) (1 - z₀)
  have hc' : c' ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨le_trans (by linarith) (le_max_left _ _),
      max_le (by linarith) (by linarith)⟩
  have hbound := calibrated_two_endpoint_only_zero_separated
    w epsilon (1 - q) c' (1 - x₁) (1 - z₁) (1 - x₀) (1 - z₀)
    hw0 hw1 ⟨by linarith, by linarith⟩ hc'
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    (le_max_left _ _) (max_le (by linarith) (by linarith))
    (le_max_right _ _) (max_le (by linarith) (by linarith))
    (by nlinarith [hsep₁sq]) (by nlinarith [hnotsep₀sq])
  have habs₁ : |(1 - x₁) - (1 - q)| = |x₁ - q| := by
    rw [show (1 - x₁) - (1 - q) = -(x₁ - q) by ring, abs_neg]
  have habs₀ : |(1 - x₀) - (1 - q)| = |x₀ - q| := by
    rw [show (1 - x₀) - (1 - q) = -(x₀ - q) by ring, abs_neg]
  rw [habs₁, habs₀] at hbound
  ring_nf at hbound ⊢
  exact hbound

set_option maxHeartbeats 2000000 in
@[blueprint "lem:calibrated-two-endpoint-neither-separated"
  (statement := /-- Let (w,q,c,x_0,z_0,x_1,z_1in[0,1]), with (z_jleq cleq z_j+w) for (j=0,1). If neither endpoint receives a separation charge, then after subtracting (3|x_j-q|+w) and (2(q-c)(q-j)) from each endpoint change in squared loss, their convex combination with weights (1-q) and (q) is nonpositive. -/)
  (proof := /-- Apply \cref{lem:calibrated-two-endpoint-both-separated-forward-forward} with separation parameter zero. Both separation hypotheses reduce to nonnegativity of a square, and both added charges vanish. -/)
  (title := /-- Uncharged two-endpoint estimate -/)
  (latexEnv := "lemma")]
lemma calibrated_two_endpoint_neither_separated
    (w q c x₀ z₀ x₁ z₁ : ℝ)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) (hz₀ : z₀ ∈ Set.Icc (0 : ℝ) 1)
    (hx₁ : x₁ ∈ Set.Icc (0 : ℝ) 1) (hz₁ : z₁ ∈ Set.Icc (0 : ℝ) 1)
    (hz₀c : z₀ ≤ c) (hcz₀ : c ≤ z₀ + w)
    (hz₁c : z₁ ≤ c) (hcz₁ : c ≤ z₁ + w) :
    (1 - q) *
        (x₀ ^ 2 - z₀ ^ 2 -
          3 * |x₀ - q| - w - 2 * (q - c) * q) +
      q *
        ((x₁ - 1) ^ 2 - (z₁ - 1) ^ 2 -
          3 * |x₁ - q| - w - 2 * (q - c) * (q - 1)) ≤ 0 := by
  have hsq₀ : (0 : ℝ) ^ 2 ≤ (x₀ - z₀) ^ 2 := by
    simpa using sq_nonneg (x₀ - z₀)
  have hsq₁ : (0 : ℝ) ^ 2 ≤ (x₁ - z₁) ^ 2 := by
    simpa using sq_nonneg (x₁ - z₁)
  simpa using calibrated_two_endpoint_both_separated_forward_forward
    w 0 q c x₀ z₀ x₁ z₁ hw0 hw1 hq hc hx₀ hz₀ hx₁ hz₁
    hz₀c hcz₀ hz₁c hcz₁ hsq₀ hsq₁

@[blueprint "lem:calibrated-rounded-two-endpoint-bound"
  (statement := /-- Let \(w,\epsilon,q,c,x_0,z_0,b_0,x_1,z_1,b_1\in[0,1]\). Suppose that \(z_j\leq c\leq z_j+w\) and \(x_j\leq b_j\leq x_j+w\) for \(j\in\{0,1\}\). For \(j=0,1\), charge \(\epsilon^2\) when \(\epsilon\leq|x_j-z_j|\). After subtracting \(3|x_j-q|+3w\) and the calibrated affine residual \(2(q-c)(q-j)\), the convex combination of the label-\(0\) and label-\(1\) expressions with weights \(1-q\) and \(q\) is nonpositive. -/)
  (proof := /-- First use the one-sided rounding hypotheses to replace each current rounded loss by the corresponding surrogate loss, at a cost of \(2w\) per endpoint. Split according to whether each pair \(x_j,z_j\) is \(\epsilon\)-separated. When both pairs are separated, split their directions and apply \cref{lem:calibrated-two-endpoint-both-separated-forward-forward,lem:calibrated-two-endpoint-both-separated-forward-backward,lem:calibrated-two-endpoint-both-separated-backward-forward,lem:calibrated-two-endpoint-both-separated-backward-backward}. When exactly one pair is separated, apply \cref{lem:calibrated-two-endpoint-only-zero-separated,lem:calibrated-two-endpoint-only-one-separated}, respectively. When neither is separated, apply \cref{lem:calibrated-two-endpoint-neither-separated}. In each case the endpoint estimate and the rounding cost give the asserted bound. -/)
  (title := /-- Two-endpoint calibrated rounding estimate -/)
  (latexEnv := "lemma")]
lemma calibrated_rounded_two_endpoint_bound
    (w epsilon q c x₀ z₀ b₀ x₁ z₁ b₁ : ℝ)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hepsilon0 : 0 ≤ epsilon)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) (hz₀ : z₀ ∈ Set.Icc (0 : ℝ) 1)
    (hb₀ : b₀ ∈ Set.Icc (0 : ℝ) 1)
    (hx₁ : x₁ ∈ Set.Icc (0 : ℝ) 1) (hz₁ : z₁ ∈ Set.Icc (0 : ℝ) 1)
    (hb₁ : b₁ ∈ Set.Icc (0 : ℝ) 1)
    (hz₀c : z₀ ≤ c) (hcz₀ : c ≤ z₀ + w)
    (hx₀b : x₀ ≤ b₀) (hbx₀ : b₀ ≤ x₀ + w)
    (hz₁c : z₁ ≤ c) (hcz₁ : c ≤ z₁ + w)
    (hx₁b : x₁ ≤ b₁) (hbx₁ : b₁ ≤ x₁ + w) :
    (1 - q) *
        (b₀ ^ 2 - c ^ 2 +
          (if epsilon ≤ |x₀ - z₀| then epsilon ^ 2 else 0) -
          3 * |x₀ - q| - 3 * w - 2 * (q - c) * q) +
      q *
        ((b₁ - 1) ^ 2 - (c - 1) ^ 2 +
          (if epsilon ≤ |x₁ - z₁| then epsilon ^ 2 else 0) -
          3 * |x₁ - q| - 3 * w - 2 * (q - c) * (q - 1)) ≤ 0 := by
  rcases hq with ⟨hq0, hq1⟩
  rcases hc with ⟨hc0, hc1⟩
  rcases hx₀ with ⟨hx₀0, hx₀1⟩
  rcases hz₀ with ⟨hz₀0, hz₀1⟩
  rcases hb₀ with ⟨hb₀0, hb₀1⟩
  rcases hx₁ with ⟨hx₁0, hx₁1⟩
  rcases hz₁ with ⟨hz₁0, hz₁1⟩
  rcases hb₁ with ⟨hb₁0, hb₁1⟩
  have hround₀ :
      b₀ ^ 2 - c ^ 2 ≤ x₀ ^ 2 - z₀ ^ 2 + 2 * w := by
    have hcurrent :
        0 ≤ (w - (b₀ - x₀)) * (b₀ + x₀) :=
      mul_nonneg (by linarith) (add_nonneg hb₀0 hx₀0)
    have hcurrent' : 0 ≤ w * (2 - b₀ - x₀) :=
      mul_nonneg hw0 (by linarith)
    have hprevious : 0 ≤ (c - z₀) * (c + z₀) :=
      mul_nonneg (sub_nonneg.mpr hz₀c) (add_nonneg hc0 hz₀0)
    nlinarith
  have hround₁ :
      (b₁ - 1) ^ 2 - (c - 1) ^ 2 ≤
        (x₁ - 1) ^ 2 - (z₁ - 1) ^ 2 + 2 * w := by
    have hcurrent : 0 ≤ (b₁ - x₁) * (2 - b₁ - x₁) :=
      mul_nonneg (sub_nonneg.mpr hx₁b) (by linarith)
    have hprevious :
        0 ≤ (w - (c - z₁)) * (2 - c - z₁) :=
      mul_nonneg (by linarith) (by linarith)
    have hprevious' : 0 ≤ w * (c + z₁) :=
      mul_nonneg hw0 (add_nonneg hc0 hz₁0)
    nlinarith
  have hround₀_weighted :=
    mul_le_mul_of_nonneg_left hround₀ (sub_nonneg.mpr hq1)
  have hround₁_weighted := mul_le_mul_of_nonneg_left hround₁ hq0
  have hreduce :
      (1 - q) *
          (b₀ ^ 2 - c ^ 2 +
            (if epsilon ≤ |x₀ - z₀| then epsilon ^ 2 else 0) -
            3 * |x₀ - q| - 3 * w - 2 * (q - c) * q) +
        q *
          ((b₁ - 1) ^ 2 - (c - 1) ^ 2 +
            (if epsilon ≤ |x₁ - z₁| then epsilon ^ 2 else 0) -
            3 * |x₁ - q| - 3 * w - 2 * (q - c) * (q - 1)) ≤
        (1 - q) *
          (x₀ ^ 2 - z₀ ^ 2 +
            (if epsilon ≤ |x₀ - z₀| then epsilon ^ 2 else 0) -
            3 * |x₀ - q| - w - 2 * (q - c) * q) +
        q *
          ((x₁ - 1) ^ 2 - (z₁ - 1) ^ 2 +
            (if epsilon ≤ |x₁ - z₁| then epsilon ^ 2 else 0) -
            3 * |x₁ - q| - w - 2 * (q - c) * (q - 1)) := by
    nlinarith [hround₀_weighted, hround₁_weighted]
  apply hreduce.trans
  by_cases hsep₀ : epsilon ≤ |x₀ - z₀|
  · have hsep₀sq : epsilon ^ 2 ≤ (x₀ - z₀) ^ 2 := by
      rw [← sq_abs (x₀ - z₀)]
      exact (sq_le_sq₀ hepsilon0 (abs_nonneg _)).2 hsep₀
    by_cases hsep₁ : epsilon ≤ |x₁ - z₁|
    · have hsep₁sq : epsilon ^ 2 ≤ (x₁ - z₁) ^ 2 := by
        rw [← sq_abs (x₁ - z₁)]
        exact (sq_le_sq₀ hepsilon0 (abs_nonneg _)).2 hsep₁
      rw [if_pos hsep₀, if_pos hsep₁]
      rcases le_total z₀ x₀ with hz₀x₀ | hx₀z₀ <;>
        rcases le_total z₁ x₁ with hz₁x₁ | hx₁z₁
      · exact calibrated_two_endpoint_both_separated_forward_forward
          w epsilon q c x₀ z₀ x₁ z₁ hw0 hw1
          ⟨hq0, hq1⟩ ⟨hc0, hc1⟩ ⟨hx₀0, hx₀1⟩ ⟨hz₀0, hz₀1⟩
          ⟨hx₁0, hx₁1⟩ ⟨hz₁0, hz₁1⟩ hz₀c hcz₀ hz₁c hcz₁
          hsep₀sq hsep₁sq
      · exact calibrated_two_endpoint_both_separated_forward_backward
          w epsilon q c x₀ z₀ x₁ z₁ hw0 hw1
          ⟨hq0, hq1⟩ ⟨hc0, hc1⟩ ⟨hx₀0, hx₀1⟩ ⟨hz₀0, hz₀1⟩
          ⟨hx₁0, hx₁1⟩ ⟨hz₁0, hz₁1⟩ hz₀c hcz₀ hz₁c hcz₁
          hz₀x₀ hx₁z₁ hsep₀sq hsep₁sq
      · exact calibrated_two_endpoint_both_separated_backward_forward
          w epsilon q c x₀ z₀ x₁ z₁ hw0 hw1
          ⟨hq0, hq1⟩ ⟨hc0, hc1⟩ ⟨hx₀0, hx₀1⟩ ⟨hz₀0, hz₀1⟩
          ⟨hx₁0, hx₁1⟩ ⟨hz₁0, hz₁1⟩ hz₀c hcz₀ hz₁c hcz₁
          hx₀z₀ hz₁x₁ hsep₀sq hsep₁sq
      · exact calibrated_two_endpoint_both_separated_backward_backward
          w epsilon q c x₀ z₀ x₁ z₁ hw0 hw1
          ⟨hq0, hq1⟩ ⟨hc0, hc1⟩ ⟨hx₀0, hx₀1⟩ ⟨hz₀0, hz₀1⟩
          ⟨hx₁0, hx₁1⟩ ⟨hz₁0, hz₁1⟩ hz₀c hcz₀ hz₁c hcz₁
          hx₀z₀ hx₁z₁ hsep₀sq hsep₁sq
    · have hnotsep₁' : |x₁ - z₁| < epsilon := lt_of_not_ge hsep₁
      have hnotsep₁sq : (x₁ - z₁) ^ 2 ≤ epsilon ^ 2 := by
        rw [← sq_abs (x₁ - z₁)]
        exact ((sq_lt_sq₀ (abs_nonneg _) hepsilon0).2 hnotsep₁').le
      rw [if_pos hsep₀, if_neg hsep₁]
      simpa only [add_zero] using calibrated_two_endpoint_only_zero_separated
        w epsilon q c x₀ z₀ x₁ z₁ hw0 hw1
        ⟨hq0, hq1⟩ ⟨hc0, hc1⟩ ⟨hx₀0, hx₀1⟩ ⟨hz₀0, hz₀1⟩
        ⟨hx₁0, hx₁1⟩ ⟨hz₁0, hz₁1⟩ hz₀c hcz₀ hz₁c hcz₁
        hsep₀sq hnotsep₁sq
  · by_cases hsep₁ : epsilon ≤ |x₁ - z₁|
    · have hsep₁sq : epsilon ^ 2 ≤ (x₁ - z₁) ^ 2 := by
        rw [← sq_abs (x₁ - z₁)]
        exact (sq_le_sq₀ hepsilon0 (abs_nonneg _)).2 hsep₁
      have hnotsep₀ : |x₀ - z₀| < epsilon := lt_of_not_ge hsep₀
      have hnotsep₀sq : (x₀ - z₀) ^ 2 ≤ epsilon ^ 2 := by
        rw [← sq_abs (x₀ - z₀)]
        exact ((sq_lt_sq₀ (abs_nonneg _) hepsilon0).2 hnotsep₀).le
      rw [if_neg hsep₀, if_pos hsep₁]
      simpa only [add_zero] using calibrated_two_endpoint_only_one_separated
        w epsilon q c x₀ z₀ x₁ z₁ hw0 hw1
        ⟨hq0, hq1⟩ ⟨hc0, hc1⟩ ⟨hx₀0, hx₀1⟩ ⟨hz₀0, hz₀1⟩
        ⟨hx₁0, hx₁1⟩ ⟨hz₁0, hz₁1⟩ hz₀c hcz₀ hz₁c hcz₁
        hnotsep₀sq hsep₁sq
    · rw [if_neg hsep₀, if_neg hsep₁]
      simpa only [add_zero] using calibrated_two_endpoint_neither_separated
        w q c x₀ z₀ x₁ z₁ hw0 hw1
        ⟨hq0, hq1⟩ ⟨hc0, hc1⟩ ⟨hx₀0, hx₀1⟩ ⟨hz₀0, hz₀1⟩
        ⟨hx₁0, hx₁1⟩ ⟨hz₁0, hz₁1⟩ hz₀c hcz₀ hz₁c hcz₁

@[blueprint "lem:calibrated-endpoint-pairing-sum"
  (statement := /-- Let (S) be a finite set of days, let (qin[0,1]), and suppose (sum_{tin S}y^t=q|S|). Let (A_0,A_1colon S	omathbb R). If
  [
  (1-q)A_0(t)+qA_1(s)leq0
  ]
  for every (t,sin S), then
  [
  sum_{tin S}igl((1-y^t)A_0(t)+y^tA_1(t)igr)leq0.
  ] -/)
  (proof := /-- If (q=0) or (q=1), the calibration identity and (y^tin[0,1]) force every label in (S) to equal that endpoint, and the pairwise hypothesis gives the result termwise. Otherwise (q(1-q)|S|>0). Multiply the pairwise inequality for ((t,s)) by ((1-y^t)y^s) and sum over (S	imes S). Calibration identifies the resulting left-hand side with (q(1-q)|S|) times the asserted sum, so positivity of this factor proves the claim. -/)
  (title := /-- Pairing endpoint inequalities on a calibrated fiber -/)
  (latexEnv := "lemma")]
lemma calibrated_endpoint_pairing_sum
    (conversation : canonical_conversation)
    (days : Finset (Fin conversation.horizon)) (q : ℝ)
    (A₀ A₁ : Fin conversation.horizon → ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hcalibration :
      (∑ t ∈ days, conversation.label t) = q * days.card)
    (hpair : ∀ t ∈ days, ∀ s ∈ days,
      (1 - q) * A₀ t + q * A₁ s ≤ 0) :
    (∑ t ∈ days,
      ((1 - conversation.label t) * A₀ t +
        conversation.label t * A₁ t)) ≤ 0 := by
  classical
  rcases hq with ⟨hq0, hq1⟩
  by_cases hdays : days = ∅
  · simp [hdays]
  have hdaysNonempty : days.Nonempty := Finset.nonempty_iff_ne_empty.mpr hdays
  by_cases hqzero : q = 0
  · have hsumzero : (∑ t ∈ days, conversation.label t) = 0 := by
      simpa [hqzero] using hcalibration
    have hyzero : ∀ t ∈ days, conversation.label t = 0 := by
      intro t ht
      have hsingle : conversation.label t ≤
          ∑ s ∈ days, conversation.label s :=
        Finset.single_le_sum (fun s _ => (conversation.label_mem s).1) ht
      nlinarith [(conversation.label_mem t).1]
    apply Finset.sum_nonpos
    intro t ht
    have hterm := hpair t ht t ht
    rw [hyzero t ht]
    simpa [hqzero] using hterm
  by_cases hqone : q = 1
  · have hsumone :
        (∑ t ∈ days, (1 - conversation.label t)) = 0 := by
      rw [Finset.sum_sub_distrib]
      simp [hcalibration, hqone]
    have hyone : ∀ t ∈ days, conversation.label t = 1 := by
      intro t ht
      have hsingle : 1 - conversation.label t ≤
          ∑ s ∈ days, (1 - conversation.label s) :=
        Finset.single_le_sum
          (s := days) (f := fun s => 1 - conversation.label s)
          (fun s _ => by linarith [(conversation.label_mem s).2]) ht
      nlinarith [(conversation.label_mem t).2]
    apply Finset.sum_nonpos
    intro t ht
    have hterm := hpair t ht t ht
    rw [hyone t ht]
    simpa [hqone] using hterm
  have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hqzero)
  have hqlt : q < 1 := lt_of_le_of_ne hq1 hqone
  have hsumcomplement :
      (∑ t ∈ days, (1 - conversation.label t)) =
        (1 - q) * days.card := by
    rw [Finset.sum_sub_distrib]
    simp [hcalibration]
    ring
  have hdouble :
      (∑ t ∈ days, ∑ s ∈ days,
        ((1 - conversation.label t) * conversation.label s) *
          ((1 - q) * A₀ t + q * A₁ s)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro t ht
    apply Finset.sum_nonpos
    intro s hs
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (by linarith [(conversation.label_mem t).2])
        (conversation.label_mem s).1)
      (hpair t ht s hs)
  have hfirst :
      (∑ t ∈ days, ∑ s ∈ days,
        ((1 - conversation.label t) * conversation.label s) *
          ((1 - q) * A₀ t)) =
        (1 - q) *
          (∑ t ∈ days, (1 - conversation.label t) * A₀ t) *
          (∑ s ∈ days, conversation.label s) := by
    calc
      _ = ∑ t ∈ days,
          ((1 - q) * (1 - conversation.label t) * A₀ t) *
            (∑ s ∈ days, conversation.label s) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          ring
      _ = _ := by
          have hcoeff :
              (∑ t ∈ days,
                (1 - q) * (1 - conversation.label t) * A₀ t) =
                (1 - q) *
                  ∑ t ∈ days, (1 - conversation.label t) * A₀ t := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro t ht
            ring
          rw [← Finset.sum_mul, hcoeff]
  have hsecond :
      (∑ t ∈ days, ∑ s ∈ days,
        ((1 - conversation.label t) * conversation.label s) *
          (q * A₁ s)) =
        q * (∑ t ∈ days, (1 - conversation.label t)) *
          (∑ s ∈ days, conversation.label s * A₁ s) := by
    calc
      _ = ∑ t ∈ days,
          (1 - conversation.label t) *
            (q * ∑ s ∈ days, conversation.label s * A₁ s) := by
          apply Finset.sum_congr rfl
          intro t ht
          calc
            _ = (1 - conversation.label t) * q *
                (∑ s ∈ days, conversation.label s * A₁ s) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro s hs
              ring
            _ = _ := by ring
      _ = _ := by
          rw [← Finset.sum_mul]
          ring
  have hdoubleIdentity :
      (∑ t ∈ days, ∑ s ∈ days,
        ((1 - conversation.label t) * conversation.label s) *
          ((1 - q) * A₀ t + q * A₁ s)) =
        q * (1 - q) * days.card *
          (∑ t ∈ days,
            ((1 - conversation.label t) * A₀ t +
              conversation.label t * A₁ t)) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [hfirst, hsecond, hcalibration, hsumcomplement]
    ring
  rw [hdoubleIdentity] at hdouble
  have hfactor :
      0 < q * (1 - q) * (days.card : ℝ) := by
    have hcardpos : 0 < (days.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hdaysNonempty
    exact mul_pos (mul_pos hqpos (by linarith)) hcardpos
  nlinarith

@[blueprint "lem:calibrated-rounded-bucket-sum-bound"
  (statement := /-- Let (S) be a finite set of days, let (q) be perfectly calibrated and ([0,1])-valued on (S), and let (cin[0,1]). Suppose (x^t,z^t,b^tin[0,1]), (z^tleq cleq z^t+w), and (x^tleq b^tleq x^t+w) on (S), where (0leq wleq1) and (epsilongeq0). Then the sum over (S) of
  [
  (b^t-y^t)^2-(c-y^t)^2+
  mathbf1_{{epsilonleq|x^t-z^t|}}epsilon^2
  -3|x^t-q^t|-3w
  ]
  is nonpositive. -/)
  (proof := /-- Partition (S) into fibers of (q). On a fiber with value (v), apply \cref{lem:calibrated-rounded-two-endpoint-bound} to every ordered pair of days, using the first day for the label-(0) endpoint and the second for the label-(1) endpoint. The calibration identity on that fiber and \cref{lem:calibrated-endpoint-pairing-sum} give a nonpositive sum after adding the affine correction (-2(v-c)(v-y^t)). Sum over all fibers. Finally, \cref{lem:perfect-calibration-weighted-residual} shows that the affine corrections sum to zero, leaving the displayed inequality. -/)
  (title := /-- Calibrated rounded estimate on one previous-round bucket -/)
  (latexEnv := "lemma")]
lemma calibrated_rounded_bucket_sum_bound
    (conversation : canonical_conversation)
    (days : Finset (Fin conversation.horizon))
    (calibrated x z b : Fin conversation.horizon → ℝ)
    (w epsilon c : ℝ)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hepsilon0 : 0 ≤ epsilon)
    (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hcalibratedRange : ∀ t ∈ days,
      calibrated t ∈ Set.Icc (0 : ℝ) 1)
    (hxRange : ∀ t ∈ days, x t ∈ Set.Icc (0 : ℝ) 1)
    (hzRange : ∀ t ∈ days, z t ∈ Set.Icc (0 : ℝ) 1)
    (hbRange : ∀ t ∈ days, b t ∈ Set.Icc (0 : ℝ) 1)
    (hzLower : ∀ t ∈ days, z t ≤ c)
    (hzUpper : ∀ t ∈ days, c ≤ z t + w)
    (hbLower : ∀ t ∈ days, x t ≤ b t)
    (hbUpper : ∀ t ∈ days, b t ≤ x t + w)
    (hperfect : perfectly_calibrated conversation days calibrated) :
    (∑ t ∈ days,
      ((b t - conversation.label t) ^ 2 -
        (c - conversation.label t) ^ 2 +
        (if epsilon ≤ |x t - z t| then epsilon ^ 2 else 0) -
        3 * |x t - calibrated t| - 3 * w)) ≤ 0 := by
  classical
  let A₀ (t : Fin conversation.horizon) : ℝ :=
    b t ^ 2 - c ^ 2 +
      (if epsilon ≤ |x t - z t| then epsilon ^ 2 else 0) -
      3 * |x t - calibrated t| - 3 * w -
      2 * (calibrated t - c) * calibrated t
  let A₁ (t : Fin conversation.horizon) : ℝ :=
    (b t - 1) ^ 2 - (c - 1) ^ 2 +
      (if epsilon ≤ |x t - z t| then epsilon ^ 2 else 0) -
      3 * |x t - calibrated t| - 3 * w -
      2 * (calibrated t - c) * (calibrated t - 1)
  let values := days.image calibrated
  have hfiber (value : ℝ) (hvalue : value ∈ values) :
      (∑ t ∈ prediction_fiber conversation days calibrated value,
        ((1 - conversation.label t) * A₀ t +
          conversation.label t * A₁ t)) ≤ 0 := by
    obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp hvalue
    apply calibrated_endpoint_pairing_sum conversation
      (prediction_fiber conversation days calibrated (calibrated t₀))
      (calibrated t₀) A₀ A₁ (hcalibratedRange t₀ ht₀)
      (hperfect (calibrated t₀))
    intro t ht s hs
    have ht' : t ∈ days ∧ calibrated t = calibrated t₀ := by
      simpa [prediction_fiber] using ht
    have hs' : s ∈ days ∧ calibrated s = calibrated t₀ := by
      simpa [prediction_fiber] using hs
    have hqt : calibrated t = calibrated t₀ := ht'.2
    have hqs : calibrated s = calibrated t₀ := hs'.2
    have hbound := calibrated_rounded_two_endpoint_bound
      w epsilon (calibrated t₀) c
      (x t) (z t) (b t) (x s) (z s) (b s)
      hw0 hw1 hepsilon0 (hcalibratedRange t₀ ht₀) hc
      (hxRange t ht'.1) (hzRange t ht'.1) (hbRange t ht'.1)
      (hxRange s hs'.1) (hzRange s hs'.1) (hbRange s hs'.1)
      (hzLower t ht'.1) (hzUpper t ht'.1)
      (hbLower t ht'.1) (hbUpper t ht'.1)
      (hzLower s hs'.1) (hzUpper s hs'.1)
      (hbLower s hs'.1) (hbUpper s hs'.1)
    simpa [A₀, A₁, hqt, hqs] using hbound
  have hpartition (f : Fin conversation.horizon → ℝ) :
      (∑ t ∈ days, f t) =
        ∑ value ∈ values,
          ∑ t ∈ prediction_fiber conversation days calibrated value, f t := by
    change (∑ t ∈ days, f t) =
      ∑ value ∈ values, ∑ t ∈ days with calibrated t = value, f t
    symm
    rw [Finset.sum_fiberwise_eq_sum_filter]
    rw [Finset.filter_eq_self.2]
    intro t ht
    exact Finset.mem_image.2 ⟨t, ht, rfl⟩
  have hendpoint :
      (∑ t ∈ days,
        ((1 - conversation.label t) * A₀ t +
          conversation.label t * A₁ t)) ≤ 0 := by
    rw [hpartition]
    exact Finset.sum_nonpos fun value hvalue => hfiber value hvalue
  have hresidual := perfect_calibration_weighted_residual
    conversation days calibrated (fun value => 2 * (value - c)) hperfect
  calc
    (∑ t ∈ days,
        ((b t - conversation.label t) ^ 2 -
          (c - conversation.label t) ^ 2 +
          (if epsilon ≤ |x t - z t| then epsilon ^ 2 else 0) -
          3 * |x t - calibrated t| - 3 * w)) =
        (∑ t ∈ days,
          ((1 - conversation.label t) * A₀ t +
            conversation.label t * A₁ t)) +
          ∑ t ∈ days, (2 * (calibrated t - c) *
            (calibrated t - conversation.label t)) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro t ht
              simp only [A₀, A₁]
              ring
    _ = (∑ t ∈ days,
          ((1 - conversation.label t) * A₀ t +
            conversation.label t * A₁ t)) := by rw [hresidual, add_zero]
    _ ≤ 0 := hendpoint

@[blueprint "lem:reciprocal-bucketed-value-bounds"
  (statement := /-- Let \(0<w\leq1\), let \(n\geq1\) be an integer with \(w=n^{-1}\), and let \(x\in[0,1]\). Then the upper bucket endpoint \(b_w(x)\) lies in \([0,1]\) and satisfies \(x\leq b_w(x)\leq x+w\). -/)
  (proof := /-- The two rounding inequalities are \cref{lem:bucket-index-rounding-bounds}. The bucket index is at most the ceiling of \(w^{-1}\), which equals \(n\), while \(nw=1\); together with positivity of \(w\), this places the upper endpoint in \([0,1]\). -/)
  (title := /-- Range and displacement of reciprocal-width bucketing -/)
  (latexEnv := "lemma")]
lemma reciprocal_bucketed_value_bounds
    (w x : ℝ) (n : ℕ) (hwpos : 0 < w) (hn : 1 ≤ n)
    (hw : w = (n : ℝ)⁻¹) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (bucket_index w x : ℝ) * w ∈ Set.Icc (0 : ℝ) 1 ∧
      x ≤ (bucket_index w x : ℝ) * w ∧
      (bucket_index w x : ℝ) * w ≤ x + w := by
  have hround := bucket_index_rounding_bounds w x n hwpos hn hw hx
  have hn0 : n ≠ 0 := by omega
  have hceil : ⌈w⁻¹⌉₊ = n := by
    rw [hw]
    simp [hn0]
  have hindex : bucket_index w x ≤ n := by
    rw [bucket_index, hceil]
    exact min_le_left _ _
  have hnonneg : 0 ≤ (bucket_index w x : ℝ) * w :=
    mul_nonneg (by positivity) hwpos.le
  have hone : (n : ℝ) * w = 1 := by simp [hw, hn0]
  have hupper : (bucket_index w x : ℝ) * w ≤ 1 := by
    calc
      (bucket_index w x : ℝ) * w ≤ (n : ℝ) * w :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hindex) hwpos.le
      _ = 1 := hone
  exact ⟨⟨hnonneg, hupper⟩, hround⟩

@[blueprint "lem:round-error-decrease"
  (statement := /-- Let \(C\) be a canonical conversation with horizon \(T\), let \(h\) be one of its two parties, let \(f\colon\mathbb R\to\mathbb R\) and \(g\colon\mathbb N\to\mathbb R\), let \(\epsilon\in\mathbb R\), and let \(k\geq1\) be an integer round assigned to \(h\). Suppose that \(h\) is \((f,g)\)-conversation-calibrated and that \(C\) is an \(\epsilon\)-agreement run. Then
  \[
  \operatorname{SQErr}(\bar p^k,y)
  \leq \operatorname{SQErr}(\bar p^{k-1},y)
  -\epsilon^2|T^{\geq k+1}|+3g(T)T
  +3\frac{f(g(T)T)}{g(T)}.
  \] -/)
  (proof := /-- Put \(w=g(T)\), \(A=T^{\geq k}\), \(B=T^{\geq k+1}\), and \(\Gamma=f(wT)/w\). First, \cref{lem:bucketwise-calibrated-surrogate} supplies a global \([0,1]\)-valued perfectly calibrated surrogate on \(A\), and \cref{lem:calibrated-squared-error-perturbation} records the corresponding squared-error stability bound with loss \(3\Gamma\). The special case in which the original predictions are perfectly conversation-calibrated is also bounded by \cref{lem:perfect-round-error-decrease}. For the general robust estimate, conversation calibration supplies an integer \(n\geq1\) with \(w=n^{-1}\). Partition \(A\) according to the width-\(w\) bucket \(i\in\{1,\ldots,n\}\) of the round-\((k-1)\) prediction, and on each part choose the \([0,1]\)-valued perfectly calibrated predictor supplied by the calibration hypothesis.

  For a fixed bucket, \cref{lem:reciprocal-bucketed-value-bounds} places the preceding bucket endpoint and every round-\(k\) bucketed prediction in \([0,1]\), and bounds each upper-rounding displacement by \(w\). Hence \cref{lem:calibrated-rounded-bucket-sum-bound}, applied with the actual round-\(k\) and round-\((k-1)\) predictions, bounds the sum over that bucket of the squared-error change plus the charge
  \[
  \epsilon^2\mathbf 1_{\{\epsilon\leq|p^{t,k}-p^{t,k-1}|\}}
  \]
  by three times the \(\ell^1\)-distance from the calibrated predictor plus \(3w\) per day. Summing over the bucket partition and applying \cref{lem:bucket-error-sum-bound} bounds the total distance term by \(\Gamma\).

  For every \(t\in A\), the agreement-run conditions show that \(\epsilon\leq|p^{t,k}-p^{t,k-1}|\) holds exactly when \(t\in B\): the forward implication uses the strict terminal inequality when the conversation ends at round \(k\), and the reverse implication uses the nonterminal separation inequality. Thus the total charge is \(\epsilon^2|B|\), and the preceding estimates give
  \[
  \operatorname{SQErr}(\bar p^k,y)-\operatorname{SQErr}(\bar p^{k-1},y)
  \leq-\epsilon^2|B|+3w|A|+3\Gamma.
  \]
  Outside \(A\), the two bucketed round predictors coincide. Therefore the same inequality holds for the full squared-error difference. Finally, \(|A|\leq T\) and \(w>0\), so replacing \(3w|A|\) by \(3wT\) proves the assertion. -/)
  (title := /-- Approximate-calibration one-round decrease -/)
  (latexEnv := "lemma")]
lemma round_error_decrease
    (conversation : canonical_conversation) (human : Bool)
    (error : ℝ → ℝ) (width : ℕ → ℝ)
    (epsilon : ℝ) (k : ℕ)
    (hcalibration :
      conversation_calibrated conversation human error width)
    (hrole : party_round human k)
    (hrun : epsilon_agreement_run conversation epsilon) (hk : 1 ≤ k) :
    squared_error conversation Finset.univ
        (bucketed_round_prediction conversation
          (width conversation.horizon) k) ≤
      squared_error conversation Finset.univ
        (bucketed_round_prediction conversation
          (width conversation.horizon) (k - 1)) -
      epsilon ^ 2 *
        (round_subsequence conversation (k + 1)).card +
      3 * width conversation.horizon * conversation.horizon +
      3 * (error (width conversation.horizon * conversation.horizon) /
        width conversation.horizon) := by
  classical
  obtain ⟨globalCalibrated, hglobalRange, hglobalPerfect, hglobalClose⟩ :=
    bucketwise_calibrated_surrogate conversation human error width k
      hcalibration hrole
  have hglobalPerturb :
      squared_error conversation (round_subsequence conversation k)
          (conversation.prediction k) -
        squared_error conversation (round_subsequence conversation k)
          globalCalibrated ≤
        3 * (error (width conversation.horizon * conversation.horizon) /
          width conversation.horizon) := by
    exact calibrated_squared_error_perturbation conversation
      (round_subsequence conversation k) globalCalibrated
      (conversation.prediction k)
      (error (width conversation.horizon * conversation.horizon) /
        width conversation.horizon)
      hglobalRange (fun t _ => conversation.prediction_mem k t)
      hglobalPerfect hglobalClose
  have hperfectCase :
      perfectly_conversation_calibrated conversation human width →
        squared_error conversation Finset.univ
            (bucketed_round_prediction conversation
              (width conversation.horizon) k) ≤
          squared_error conversation Finset.univ
              (bucketed_round_prediction conversation
                (width conversation.horizon) (k - 1)) -
            (epsilon - width conversation.horizon) ^ 2 *
              (round_subsequence conversation (k + 1)).card +
            width conversation.horizon * conversation.horizon := by
    intro hperfect
    exact perfect_round_error_decrease conversation human width epsilon k
      hperfect hrole hrun hk
  rcases hcalibration with
    ⟨herror, hwpos, hwle, ⟨n, hn, hwrec⟩, hlocal⟩
  let w := width conversation.horizon
  change 0 < w at hwpos
  change w ≤ 1 at hwle
  change w = (n : ℝ)⁻¹ at hwrec
  have hn0 : n ≠ 0 := by omega
  have hepsilon : 0 < epsilon := by
    let t : Fin conversation.horizon := ⟨0, conversation.horizon_pos⟩
    exact (abs_nonneg _).trans_lt (hrun.2 t).1
  let active := round_subsequence conversation k
  let next := round_subsequence conversation (k + 1)
  let index (t : Fin conversation.horizon) : ℕ :=
    bucket_index w (conversation.prediction (k - 1) t)
  have hceil : ⌈w⁻¹⌉₊ = n := by
    rw [hwrec]
    simp [hn0]
  have hindex (t : Fin conversation.horizon) :
      index t ∈ Finset.Icc 1 n := by
    rw [Finset.mem_Icc]
    change 1 ≤ min ⌈w⁻¹⌉₊
        (max 1 ⌈conversation.prediction (k - 1) t / w⌉₊) ∧
      min ⌈w⁻¹⌉₊
        (max 1 ⌈conversation.prediction (k - 1) t / w⌉₊) ≤ n
    rw [hceil]
    exact ⟨le_min hn (le_max_left _ _), min_le_left _ _⟩
  have hlocal' : ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ∃ calibrated : Fin conversation.horizon → ℝ,
        (∀ t ∈ previous_round_bucket_days conversation w k i,
          calibrated t ∈ Set.Icc (0 : ℝ) 1) ∧
        perfectly_calibrated conversation
          (previous_round_bucket_days conversation w k i) calibrated ∧
        (∑ t ∈ previous_round_bucket_days conversation w k i,
          |conversation.prediction k t - calibrated t|) ≤
          error ((previous_round_bucket_days conversation w k i).card : ℝ) := by
    intro i hi₁ hi₂
    have hiCeil : i ≤ ⌈(width conversation.horizon)⁻¹⌉₊ := by
      change i ≤ ⌈w⁻¹⌉₊
      simpa [hceil] using hi₂
    simpa only [w] using hlocal k hrole i hi₁ hiCeil
  let localPredictor (i : ℕ) : Fin conversation.horizon → ℝ :=
    if hi : 1 ≤ i ∧ i ≤ n then
      Classical.choose (hlocal' i hi.1 hi.2)
    else fun _ => 0
  have hlocalSpec (i : ℕ) (hi₁ : 1 ≤ i) (hi₂ : i ≤ n) :
      (∀ t ∈ previous_round_bucket_days conversation w k i,
        localPredictor i t ∈ Set.Icc (0 : ℝ) 1) ∧
      perfectly_calibrated conversation
        (previous_round_bucket_days conversation w k i)
        (localPredictor i) ∧
      (∑ t ∈ previous_round_bucket_days conversation w k i,
        |conversation.prediction k t - localPredictor i t|) ≤
        error ((previous_round_bucket_days conversation w k i).card : ℝ) := by
    have hEq : localPredictor i =
        Classical.choose (hlocal' i hi₁ hi₂) := by
      simp [localPredictor, hi₁, hi₂]
    rw [hEq]
    exact Classical.choose_spec (hlocal' i hi₁ hi₂)
  let calibrated (t : Fin conversation.horizon) : ℝ :=
    localPredictor (index t) t
  have hpartition (f : Fin conversation.horizon → ℝ) :
      (∑ t ∈ active, f t) =
        ∑ i ∈ Finset.Icc 1 n,
          ∑ t ∈ previous_round_bucket_days conversation w k i, f t := by
    symm
    change (∑ i ∈ Finset.Icc 1 n,
      ∑ t ∈ active with index t = i, f t) = ∑ t ∈ active, f t
    rw [Finset.sum_fiberwise_eq_sum_filter]
    rw [Finset.filter_eq_self.2]
    intro t ht
    exact hindex t
  have hbucket (i : ℕ) (hi : i ∈ Finset.Icc 1 n) :
      (∑ t ∈ previous_round_bucket_days conversation w k i,
        ((bucketed_round_prediction conversation w k t -
            conversation.label t) ^ 2 -
          ((i : ℝ) * w - conversation.label t) ^ 2 +
          (if epsilon ≤
              |conversation.prediction k t -
                conversation.prediction (k - 1) t|
            then epsilon ^ 2 else 0) -
          3 * |conversation.prediction k t - localPredictor i t| -
          3 * w)) ≤ 0 := by
    have hi₁ := (Finset.mem_Icc.mp hi).1
    have hi₂ := (Finset.mem_Icc.mp hi).2
    have hc : (i : ℝ) * w ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact mul_nonneg (by positivity) hwpos.le
      · calc
          (i : ℝ) * w ≤ (n : ℝ) * w :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hi₂) hwpos.le
          _ = 1 := by simp [hwrec, hn0]
    apply calibrated_rounded_bucket_sum_bound conversation
      (previous_round_bucket_days conversation w k i)
      (localPredictor i) (conversation.prediction k)
      (conversation.prediction (k - 1))
      (bucketed_round_prediction conversation w k)
      w epsilon ((i : ℝ) * w) hwpos.le hwle hepsilon.le hc
      (hlocalSpec i hi₁ hi₂).1
      (fun t _ => conversation.prediction_mem k t)
      (fun t _ => conversation.prediction_mem (k - 1) t)
      (fun t ht => by
        have htk : k ≤ conversation.length t := by
          simpa [round_subsequence] using (Finset.mem_filter.mp ht).1
        simpa [bucketed_round_prediction, min_eq_left htk] using
          (reciprocal_bucketed_value_bounds w
            (conversation.prediction k t) n hwpos hn hwrec
            (conversation.prediction_mem k t)).1)
      (fun t ht => by
        have hidx : bucket_index w
            (conversation.prediction (k - 1) t) = i :=
          (Finset.mem_filter.mp ht).2
        have hround := reciprocal_bucketed_value_bounds w
          (conversation.prediction (k - 1) t) n hwpos hn hwrec
          (conversation.prediction_mem (k - 1) t)
        simpa [hidx] using hround.2.1)
      (fun t ht => by
        have hidx : bucket_index w
            (conversation.prediction (k - 1) t) = i :=
          (Finset.mem_filter.mp ht).2
        have hround := reciprocal_bucketed_value_bounds w
          (conversation.prediction (k - 1) t) n hwpos hn hwrec
          (conversation.prediction_mem (k - 1) t)
        simpa [hidx] using hround.2.2)
      (fun t ht => by
        have htk : k ≤ conversation.length t := by
          simpa [round_subsequence] using (Finset.mem_filter.mp ht).1
        simpa [bucketed_round_prediction, min_eq_left htk] using
          (reciprocal_bucketed_value_bounds w
            (conversation.prediction k t) n hwpos hn hwrec
            (conversation.prediction_mem k t)).2.1)
      (fun t ht => by
        have htk : k ≤ conversation.length t := by
          simpa [round_subsequence] using (Finset.mem_filter.mp ht).1
        simpa [bucketed_round_prediction, min_eq_left htk] using
          (reciprocal_bucketed_value_bounds w
            (conversation.prediction k t) n hwpos hn hwrec
            (conversation.prediction_mem k t)).2.2)
      (hlocalSpec i hi₁ hi₂).2.1
  have hactive :
      (∑ t ∈ active,
        ((bucketed_round_prediction conversation w k t -
            conversation.label t) ^ 2 -
          (bucketed_round_prediction conversation w (k - 1) t -
            conversation.label t) ^ 2 +
          (if epsilon ≤
              |conversation.prediction k t -
                conversation.prediction (k - 1) t|
            then epsilon ^ 2 else 0) -
          3 * |conversation.prediction k t - calibrated t| - 3 * w)) ≤ 0 := by
    rw [hpartition]
    apply Finset.sum_nonpos
    intro i hi
    calc
      _ = ∑ t ∈ previous_round_bucket_days conversation w k i,
          (((bucketed_round_prediction conversation w k t -
              conversation.label t) ^ 2 -
            ((i : ℝ) * w - conversation.label t) ^ 2 +
            (if epsilon ≤ |conversation.prediction k t -
                conversation.prediction (k - 1) t|
              then epsilon ^ 2 else 0)) -
            3 * |conversation.prediction k t - localPredictor i t| -
            3 * w) := by
          apply Finset.sum_congr rfl
          intro t ht
          have hidx : index t = i := by
            simpa [index, previous_round_bucket_days] using
              (Finset.mem_filter.mp ht).2
          have htk : k ≤ conversation.length t := by
            simpa [round_subsequence] using (Finset.mem_filter.mp ht).1
          have htkprev : k - 1 ≤ conversation.length t := by omega
          simp [calibrated, hidx, bucketed_round_prediction,
            min_eq_left htkprev, index]
      _ ≤ 0 := hbucket i hi
  have hdistance :
      (∑ t ∈ active,
        |conversation.prediction k t - calibrated t|) ≤
        error (w * conversation.horizon) / w := by
    calc
      _ = ∑ i ∈ Finset.Icc 1 n,
          ∑ t ∈ previous_round_bucket_days conversation w k i,
            |conversation.prediction k t - calibrated t| := hpartition _
      _ = ∑ i ∈ Finset.Icc 1 n,
          ∑ t ∈ previous_round_bucket_days conversation w k i,
            |conversation.prediction k t - localPredictor i t| := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro t ht
          have hidx : index t = i := by
            simpa [index, previous_round_bucket_days] using
              (Finset.mem_filter.mp ht).2
          simp [calibrated, hidx]
      _ ≤ ∑ i ∈ Finset.Icc 1 n,
          error ((previous_round_bucket_days conversation w k i).card : ℝ) := by
          exact Finset.sum_le_sum fun i hi =>
            (hlocalSpec i (Finset.mem_Icc.mp hi).1
              (Finset.mem_Icc.mp hi).2).2.2
      _ ≤ error (w * conversation.horizon) / w :=
          bucket_error_sum_bound conversation error w k n herror hwpos hn hwrec
  have hnext_active : next ⊆ active := by
    intro t ht
    simp only [next, active, round_subsequence, Finset.mem_filter,
      Finset.mem_univ, true_and] at ht ⊢
    omega
  have hsep_iff (t : Fin conversation.horizon) (ht : t ∈ active) :
      epsilon ≤ |conversation.prediction k t -
        conversation.prediction (k - 1) t| ↔ t ∈ next := by
    constructor
    · intro hsep
      by_contra hnot
      have hlength : conversation.length t = k := by
        have hak : k ≤ conversation.length t := by
          simpa [active, round_subsequence] using ht
        have hlt : conversation.length t < k + 1 := by
          simpa [next, round_subsequence, not_le] using hnot
        omega
      have hterminal := (hrun.2 t).1
      rw [hlength] at hterminal
      exact (not_lt_of_ge hsep) (by simpa [abs_sub_comm] using hterminal)
    · intro htnext
      have hlt : k < conversation.length t := by
        have : k + 1 ≤ conversation.length t := by
          simpa [next, round_subsequence] using htnext
        omega
      exact (hrun.2 t).2 k hk hlt
  have hcharge :
      (∑ t ∈ active,
        if epsilon ≤ |conversation.prediction k t -
            conversation.prediction (k - 1) t|
          then epsilon ^ 2 else 0) =
        epsilon ^ 2 * next.card := by
    have hrewrite : (∑ t ∈ active,
        if epsilon ≤ |conversation.prediction k t -
            conversation.prediction (k - 1) t|
          then epsilon ^ 2 else 0) =
        ∑ t ∈ active, if t ∈ next then epsilon ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      simp only [hsep_iff t ht]
    rw [hrewrite, Finset.sum_ite]
    have hfilter : active.filter (fun t => t ∈ next) = next := by
      ext t
      simp [hnext_active]
    rw [hfilter]
    simp [mul_comm]
  have hloss_active :
      (∑ t ∈ active,
        ((bucketed_round_prediction conversation w k t -
            conversation.label t) ^ 2 -
          (bucketed_round_prediction conversation w (k - 1) t -
            conversation.label t) ^ 2)) ≤
        -epsilon ^ 2 * next.card + 3 * w * active.card +
          3 * (error (w * conversation.horizon) / w) := by
    have hrewrite :
        (∑ t ∈ active,
          ((bucketed_round_prediction conversation w k t -
              conversation.label t) ^ 2 -
            (bucketed_round_prediction conversation w (k - 1) t -
              conversation.label t) ^ 2 +
            (if epsilon ≤ |conversation.prediction k t -
                conversation.prediction (k - 1) t|
              then epsilon ^ 2 else 0) -
            3 * |conversation.prediction k t - calibrated t| - 3 * w)) =
          (∑ t ∈ active,
            ((bucketed_round_prediction conversation w k t -
                conversation.label t) ^ 2 -
              (bucketed_round_prediction conversation w (k - 1) t -
                conversation.label t) ^ 2)) +
          (∑ t ∈ active,
            if epsilon ≤ |conversation.prediction k t -
                conversation.prediction (k - 1) t|
              then epsilon ^ 2 else 0) -
          3 * (∑ t ∈ active,
            |conversation.prediction k t - calibrated t|) -
          3 * w * active.card := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_add_distrib]
      simp [← Finset.mul_sum]
      ring
    rw [hrewrite, hcharge] at hactive
    nlinarith
  have hinactive (t : Fin conversation.horizon) (ht : t ∉ active) :
      bucketed_round_prediction conversation w k t =
        bucketed_round_prediction conversation w (k - 1) t := by
    have htlt : conversation.length t < k := by
      simpa [active, round_subsequence, not_le] using ht
    have htprev : conversation.length t ≤ k - 1 := by omega
    simp [bucketed_round_prediction, min_eq_right htlt.le,
      min_eq_right htprev]
  have hall_active :
      (∑ t ∈ Finset.univ,
        ((bucketed_round_prediction conversation w k t -
            conversation.label t) ^ 2 -
          (bucketed_round_prediction conversation w (k - 1) t -
            conversation.label t) ^ 2)) =
        ∑ t ∈ active,
          ((bucketed_round_prediction conversation w k t -
              conversation.label t) ^ 2 -
            (bucketed_round_prediction conversation w (k - 1) t -
              conversation.label t) ^ 2) := by
    symm
    apply Finset.sum_subset (by simp [active, round_subsequence])
    intro t htuniv htactive
    rw [hinactive t htactive]
    ring
  have hcard_active : (active.card : ℝ) ≤ conversation.horizon := by
    exact_mod_cast (show active.card ≤ conversation.horizon by
      simpa using Finset.card_le_univ active)
  change squared_error conversation Finset.univ
      (bucketed_round_prediction conversation w k) ≤
    squared_error conversation Finset.univ
        (bucketed_round_prediction conversation w (k - 1)) -
      epsilon ^ 2 * next.card + 3 * w * conversation.horizon +
      3 * (error (w * conversation.horizon) / w)
  unfold squared_error
  have hwcard : 3 * w * active.card ≤ 3 * w * conversation.horizon :=
    mul_le_mul_of_nonneg_left hcard_active (by positivity)
  have htotal :
      (∑ t ∈ Finset.univ,
          (bucketed_round_prediction conversation w k t -
            conversation.label t) ^ 2) -
        (∑ t ∈ Finset.univ,
          (bucketed_round_prediction conversation w (k - 1) t -
            conversation.label t) ^ 2) ≤
        -epsilon ^ 2 * next.card + 3 * w * conversation.horizon +
          3 * (error (w * conversation.horizon) / w) := by
    rw [← Finset.sum_sub_distrib, hall_active]
    nlinarith
  nlinarith

@[blueprint "lem:common-upper-rounding-difference"
  (statement := /-- Let \(w\geq0\) and let \(x,z,y,b_x,b_z\in[0,1]\). If \(x\leq b_x\leq x+w\) and \(z\leq b_z\leq z+w\), then
  \[
  (b_x-y)^2-(b_z-y)^2\leq (x-y)^2-(z-y)^2+2w.
  \] -/)
  (proof := /-- At label (0), upper rounding can increase the current squared loss by at most (2w), while upper rounding the preceding prediction can only improve the difference. At label (1), the analogous bound follows with the two roles reversed. The difference of two squared losses is affine in the label, so the result for (y\in[0,1]) is the convex combination of these two endpoint bounds. -/)
  (title := /-- Difference bound for common upper rounding -/)
  (latexEnv := "lemma")]
lemma common_upper_rounding_difference
    (w y x z bx bz : ℝ)
    (hw : 0 ≤ w)
    (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hbx : bx ∈ Set.Icc (0 : ℝ) 1)
    (hbz : bz ∈ Set.Icc (0 : ℝ) 1)
    (hxbx : x ≤ bx) (hbxx : bx ≤ x + w)
    (hzbz : z ≤ bz) (hbzz : bz ≤ z + w) :
    (bx - y) ^ 2 - (bz - y) ^ 2 ≤
      (x - y) ^ 2 - (z - y) ^ 2 + 2 * w := by
  rcases hy with ⟨hy0, hy1⟩
  rcases hx with ⟨hx0, hx1⟩
  rcases hz with ⟨hz0, hz1⟩
  rcases hbx with ⟨hbx0, hbx1⟩
  rcases hbz with ⟨hbz0, hbz1⟩
  have hzero : bx ^ 2 - bz ^ 2 ≤ x ^ 2 - z ^ 2 + 2 * w := by
    have hcurrent : 0 ≤ (w - (bx - x)) * (bx + x) :=
      mul_nonneg (by linarith) (add_nonneg hbx0 hx0)
    have hprevious : 0 ≤ (bz - z) * (bz + z) :=
      mul_nonneg (sub_nonneg.mpr hzbz) (add_nonneg hbz0 hz0)
    have hw' : 0 ≤ w * (2 - bx - x) :=
      mul_nonneg hw (by linarith)
    nlinarith
  have hone :
      (bx - 1) ^ 2 - (bz - 1) ^ 2 ≤
        (x - 1) ^ 2 - (z - 1) ^ 2 + 2 * w := by
    have hcurrent : 0 ≤ (bx - x) * (2 - bx - x) :=
      mul_nonneg (sub_nonneg.mpr hxbx) (by linarith)
    have hprevious : 0 ≤ (w - (bz - z)) * (2 - bz - z) :=
      mul_nonneg (by linarith) (by linarith)
    have hw' : 0 ≤ w * (bz + z) :=
      mul_nonneg hw (add_nonneg hbz0 hz0)
    nlinarith
  have hzero' := mul_le_mul_of_nonneg_left hzero (sub_nonneg.mpr hy1)
  have hone' := mul_le_mul_of_nonneg_left hone hy0
  nlinarith

@[blueprint "lem:calibrated-unrounded-two-endpoint-bound"
  (statement := /-- Let \(w\in[0,1]\), \(\epsilon\geq0\), and \(q,c,x_0,z_0,x_1,z_1\in[0,1]\), with \(z_j\leq c\leq z_j+w\) for \(j=0,1\). Charge \(\epsilon^2\) at endpoint \(j\) when \(\epsilon\leq|x_j-z_j|\). After subtracting \(3|x_j-q|+w\) and the calibrated affine residual \(2(q-c)(q-j)\), the convex combination of the two endpoint squared-loss changes with weights \(1-q\) and \(q\) is nonpositive. -/)
  (proof := /-- Split according to whether each endpoint pair is \(\epsilon\)-separated. If both are separated, split again according to the direction of each displacement and apply \cref{lem:calibrated-two-endpoint-both-separated-forward-forward,lem:calibrated-two-endpoint-both-separated-forward-backward,lem:calibrated-two-endpoint-both-separated-backward-forward,lem:calibrated-two-endpoint-both-separated-backward-backward}. If exactly one pair is separated, apply \cref{lem:calibrated-two-endpoint-only-zero-separated,lem:calibrated-two-endpoint-only-one-separated}. If neither pair is separated, apply \cref{lem:calibrated-two-endpoint-neither-separated}. The square comparisons follow from \(\epsilon\geq0\). -/)
  (title := /-- Unrounded two-endpoint calibrated estimate -/)
  (latexEnv := "lemma")]
lemma calibrated_unrounded_two_endpoint_bound
    (w epsilon q c x₀ z₀ x₁ z₁ : ℝ)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hepsilon0 : 0 ≤ epsilon)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) (hz₀ : z₀ ∈ Set.Icc (0 : ℝ) 1)
    (hx₁ : x₁ ∈ Set.Icc (0 : ℝ) 1) (hz₁ : z₁ ∈ Set.Icc (0 : ℝ) 1)
    (hz₀c : z₀ ≤ c) (hcz₀ : c ≤ z₀ + w)
    (hz₁c : z₁ ≤ c) (hcz₁ : c ≤ z₁ + w) :
    (1 - q) *
        (x₀ ^ 2 - z₀ ^ 2 +
          (if epsilon ≤ |x₀ - z₀| then epsilon ^ 2 else 0) -
          3 * |x₀ - q| - w - 2 * (q - c) * q) +
      q *
        ((x₁ - 1) ^ 2 - (z₁ - 1) ^ 2 +
          (if epsilon ≤ |x₁ - z₁| then epsilon ^ 2 else 0) -
          3 * |x₁ - q| - w - 2 * (q - c) * (q - 1)) ≤ 0 := by
  rcases hq with ⟨hq0, hq1⟩
  rcases hc with ⟨hc0, hc1⟩
  rcases hx₀ with ⟨hx₀0, hx₀1⟩
  rcases hz₀ with ⟨hz₀0, hz₀1⟩
  rcases hx₁ with ⟨hx₁0, hx₁1⟩
  rcases hz₁ with ⟨hz₁0, hz₁1⟩
  by_cases hsep₀ : epsilon ≤ |x₀ - z₀|
  · have hsep₀sq : epsilon ^ 2 ≤ (x₀ - z₀) ^ 2 := by
      rw [← sq_abs (x₀ - z₀)]
      exact (sq_le_sq₀ hepsilon0 (abs_nonneg _)).2 hsep₀
    by_cases hsep₁ : epsilon ≤ |x₁ - z₁|
    · have hsep₁sq : epsilon ^ 2 ≤ (x₁ - z₁) ^ 2 := by
        rw [← sq_abs (x₁ - z₁)]
        exact (sq_le_sq₀ hepsilon0 (abs_nonneg _)).2 hsep₁
      rw [if_pos hsep₀, if_pos hsep₁]
      rcases le_total z₀ x₀ with hz₀x₀ | hx₀z₀ <;>
        rcases le_total z₁ x₁ with hz₁x₁ | hx₁z₁
      · exact calibrated_two_endpoint_both_separated_forward_forward
          w epsilon q c x₀ z₀ x₁ z₁ hw0 hw1
          ⟨hq0, hq1⟩ ⟨hc0, hc1⟩ ⟨hx₀0, hx₀1⟩ ⟨hz₀0, hz₀1⟩
          ⟨hx₁0, hx₁1⟩ ⟨hz₁0, hz₁1⟩ hz₀c hcz₀ hz₁c hcz₁
          hsep₀sq hsep₁sq
      · exact calibrated_two_endpoint_both_separated_forward_backward
          w epsilon q c x₀ z₀ x₁ z₁ hw0 hw1
          ⟨hq0, hq1⟩ ⟨hc0, hc1⟩ ⟨hx₀0, hx₀1⟩ ⟨hz₀0, hz₀1⟩
          ⟨hx₁0, hx₁1⟩ ⟨hz₁0, hz₁1⟩ hz₀c hcz₀ hz₁c hcz₁
          hz₀x₀ hx₁z₁ hsep₀sq hsep₁sq
      · exact calibrated_two_endpoint_both_separated_backward_forward
          w epsilon q c x₀ z₀ x₁ z₁ hw0 hw1
          ⟨hq0, hq1⟩ ⟨hc0, hc1⟩ ⟨hx₀0, hx₀1⟩ ⟨hz₀0, hz₀1⟩
          ⟨hx₁0, hx₁1⟩ ⟨hz₁0, hz₁1⟩ hz₀c hcz₀ hz₁c hcz₁
          hx₀z₀ hz₁x₁ hsep₀sq hsep₁sq
      · exact calibrated_two_endpoint_both_separated_backward_backward
          w epsilon q c x₀ z₀ x₁ z₁ hw0 hw1
          ⟨hq0, hq1⟩ ⟨hc0, hc1⟩ ⟨hx₀0, hx₀1⟩ ⟨hz₀0, hz₀1⟩
          ⟨hx₁0, hx₁1⟩ ⟨hz₁0, hz₁1⟩ hz₀c hcz₀ hz₁c hcz₁
          hx₀z₀ hx₁z₁ hsep₀sq hsep₁sq
    · have hnotsep₁' : |x₁ - z₁| < epsilon := lt_of_not_ge hsep₁
      have hnotsep₁sq : (x₁ - z₁) ^ 2 ≤ epsilon ^ 2 := by
        rw [← sq_abs (x₁ - z₁)]
        exact ((sq_lt_sq₀ (abs_nonneg _) hepsilon0).2 hnotsep₁').le
      rw [if_pos hsep₀, if_neg hsep₁]
      simpa only [add_zero] using calibrated_two_endpoint_only_zero_separated
        w epsilon q c x₀ z₀ x₁ z₁ hw0 hw1
        ⟨hq0, hq1⟩ ⟨hc0, hc1⟩ ⟨hx₀0, hx₀1⟩ ⟨hz₀0, hz₀1⟩
        ⟨hx₁0, hx₁1⟩ ⟨hz₁0, hz₁1⟩ hz₀c hcz₀ hz₁c hcz₁
        hsep₀sq hnotsep₁sq
  · by_cases hsep₁ : epsilon ≤ |x₁ - z₁|
    · have hsep₁sq : epsilon ^ 2 ≤ (x₁ - z₁) ^ 2 := by
        rw [← sq_abs (x₁ - z₁)]
        exact (sq_le_sq₀ hepsilon0 (abs_nonneg _)).2 hsep₁
      have hnotsep₀ : |x₀ - z₀| < epsilon := lt_of_not_ge hsep₀
      have hnotsep₀sq : (x₀ - z₀) ^ 2 ≤ epsilon ^ 2 := by
        rw [← sq_abs (x₀ - z₀)]
        exact ((sq_lt_sq₀ (abs_nonneg _) hepsilon0).2 hnotsep₀).le
      rw [if_neg hsep₀, if_pos hsep₁]
      simpa only [add_zero] using calibrated_two_endpoint_only_one_separated
        w epsilon q c x₀ z₀ x₁ z₁ hw0 hw1
        ⟨hq0, hq1⟩ ⟨hc0, hc1⟩ ⟨hx₀0, hx₀1⟩ ⟨hz₀0, hz₀1⟩
        ⟨hx₁0, hx₁1⟩ ⟨hz₁0, hz₁1⟩ hz₀c hcz₀ hz₁c hcz₁
        hnotsep₀sq hsep₁sq
    · rw [if_neg hsep₀, if_neg hsep₁]
      simpa only [add_zero] using calibrated_two_endpoint_neither_separated
        w q c x₀ z₀ x₁ z₁ hw0 hw1
        ⟨hq0, hq1⟩ ⟨hc0, hc1⟩ ⟨hx₀0, hx₀1⟩ ⟨hz₀0, hz₀1⟩
        ⟨hx₁0, hx₁1⟩ ⟨hz₁0, hz₁1⟩ hz₀c hcz₀ hz₁c hcz₁

@[blueprint "lem:calibrated-unrounded-bucket-sum-bound"
  (statement := /-- Let \(S\) be a finite set of days, let \(q\) be a perfectly calibrated \([0,1]\)-valued predictor on \(S\), and let \(c\in[0,1]\). Suppose that \(x^t,z^t\in[0,1]\) and \(z^t\leq c\leq z^t+w\) on \(S\), where \(w\in[0,1]\) and \(\epsilon\geq0\). Then the sum over \(S\) of
  \[
  (x^t-y^t)^2-(z^t-y^t)^2+
  \mathbf 1_{\{\epsilon\leq|x^t-z^t|\}}\epsilon^2
  -3|x^t-q^t|-w
  \]
  is nonpositive. -/)
  (proof := /-- Partition \(S\) into the fibers of the calibrated predictor. On each fiber, apply \cref{lem:calibrated-unrounded-two-endpoint-bound} to every ordered pair of days and then use \cref{lem:calibrated-endpoint-pairing-sum}. Summing the fiber estimates gives the desired squared-loss expression together with an affine calibration residual. The residual vanishes by \cref{lem:perfect-calibration-weighted-residual}. -/)
  (title := /-- Unrounded calibrated estimate on one bucket -/)
  (latexEnv := "lemma")]
lemma calibrated_unrounded_bucket_sum_bound
    (conversation : canonical_conversation)
    (days : Finset (Fin conversation.horizon))
    (calibrated x z : Fin conversation.horizon → ℝ)
    (w epsilon c : ℝ)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hepsilon0 : 0 ≤ epsilon)
    (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hcalibratedRange : ∀ t ∈ days,
      calibrated t ∈ Set.Icc (0 : ℝ) 1)
    (hxRange : ∀ t ∈ days, x t ∈ Set.Icc (0 : ℝ) 1)
    (hzRange : ∀ t ∈ days, z t ∈ Set.Icc (0 : ℝ) 1)
    (hzLower : ∀ t ∈ days, z t ≤ c)
    (hzUpper : ∀ t ∈ days, c ≤ z t + w)
    (hperfect : perfectly_calibrated conversation days calibrated) :
    (∑ t ∈ days,
      ((x t - conversation.label t) ^ 2 -
        (z t - conversation.label t) ^ 2 +
        (if epsilon ≤ |x t - z t| then epsilon ^ 2 else 0) -
        3 * |x t - calibrated t| - w)) ≤ 0 := by
  classical
  let A₀ (t : Fin conversation.horizon) : ℝ :=
    x t ^ 2 - z t ^ 2 +
      (if epsilon ≤ |x t - z t| then epsilon ^ 2 else 0) -
      3 * |x t - calibrated t| - w -
      2 * (calibrated t - c) * calibrated t
  let A₁ (t : Fin conversation.horizon) : ℝ :=
    (x t - 1) ^ 2 - (z t - 1) ^ 2 +
      (if epsilon ≤ |x t - z t| then epsilon ^ 2 else 0) -
      3 * |x t - calibrated t| - w -
      2 * (calibrated t - c) * (calibrated t - 1)
  let values := days.image calibrated
  have hfiber (value : ℝ) (hvalue : value ∈ values) :
      (∑ t ∈ prediction_fiber conversation days calibrated value,
        ((1 - conversation.label t) * A₀ t +
          conversation.label t * A₁ t)) ≤ 0 := by
    obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp hvalue
    apply calibrated_endpoint_pairing_sum conversation
      (prediction_fiber conversation days calibrated (calibrated t₀))
      (calibrated t₀) A₀ A₁ (hcalibratedRange t₀ ht₀)
      (hperfect (calibrated t₀))
    intro t ht s hs
    have ht' : t ∈ days ∧ calibrated t = calibrated t₀ := by
      simpa [prediction_fiber] using ht
    have hs' : s ∈ days ∧ calibrated s = calibrated t₀ := by
      simpa [prediction_fiber] using hs
    have hbound := calibrated_unrounded_two_endpoint_bound
      w epsilon (calibrated t₀) c
      (x t) (z t) (x s) (z s) hw0 hw1 hepsilon0
      (hcalibratedRange t₀ ht₀) hc
      (hxRange t ht'.1) (hzRange t ht'.1)
      (hxRange s hs'.1) (hzRange s hs'.1)
      (hzLower t ht'.1) (hzUpper t ht'.1)
      (hzLower s hs'.1) (hzUpper s hs'.1)
    simpa [A₀, A₁, ht'.2, hs'.2] using hbound
  have hpartition (f : Fin conversation.horizon → ℝ) :
      (∑ t ∈ days, f t) =
        ∑ value ∈ values,
          ∑ t ∈ prediction_fiber conversation days calibrated value, f t := by
    change (∑ t ∈ days, f t) =
      ∑ value ∈ values, ∑ t ∈ days with calibrated t = value, f t
    symm
    rw [Finset.sum_fiberwise_eq_sum_filter]
    rw [Finset.filter_eq_self.2]
    intro t ht
    exact Finset.mem_image.2 ⟨t, ht, rfl⟩
  have hendpoint :
      (∑ t ∈ days,
        ((1 - conversation.label t) * A₀ t +
          conversation.label t * A₁ t)) ≤ 0 := by
    rw [hpartition]
    exact Finset.sum_nonpos fun value hvalue => hfiber value hvalue
  have hresidual := perfect_calibration_weighted_residual
    conversation days calibrated (fun value => 2 * (value - c)) hperfect
  calc
    (∑ t ∈ days,
        ((x t - conversation.label t) ^ 2 -
          (z t - conversation.label t) ^ 2 +
          (if epsilon ≤ |x t - z t| then epsilon ^ 2 else 0) -
          3 * |x t - calibrated t| - w)) =
        (∑ t ∈ days,
          ((1 - conversation.label t) * A₀ t +
            conversation.label t * A₁ t)) +
          ∑ t ∈ days, (2 * (calibrated t - c) *
            (calibrated t - conversation.label t)) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro t ht
              simp only [A₀, A₁]
              ring
    _ = (∑ t ∈ days,
          ((1 - conversation.label t) * A₀ t +
            conversation.label t * A₁ t)) := by rw [hresidual, add_zero]
    _ ≤ 0 := hendpoint

@[blueprint "lem:raw-round-error-decrease"
  (statement := /-- Let \(C\) be a canonical conversation with horizon \(T\), let \(h\) be one of its parties, and let \(k\geq1\) be a round assigned to \(h\). If \(h\) is \((f,g)\)-conversation-calibrated and \(C\) is an \(\epsilon\)-agreement run, then the squared error of the terminally frozen raw transcript satisfies
  \[
  \operatorname{SQErr}(p^k,y)\leq
  \operatorname{SQErr}(p^{k-1},y)-\epsilon^2|T^{\geq k+1}|+g(T)T+
  3\frac{f(g(T)T)}{g(T)}.
  \] -/)
  (proof := /-- Partition the active set \(T^{\geq k}\) into the width-\(g(T)\) buckets of the preceding raw prediction. Conversation calibration supplies a perfectly calibrated surrogate on every bucket. Apply \cref{lem:calibrated-unrounded-bucket-sum-bound} on each bucket and sum the estimates. The total surrogate distance is bounded by \cref{lem:bucket-error-sum-bound}, while \cref{lem:reciprocal-bucketed-value-bounds} supplies the range and displacement of each preceding bucket endpoint. The agreement-run conditions identify the separation charge with \(\epsilon^2|T^{\geq k+1}|\). Outside the active set, the terminally frozen raw predictors at rounds \(k\) and \(k-1\) coincide; finally, \(|T^{\geq k}|\leq T\). -/)
  (title := /-- One-round decrease for the frozen raw transcript -/)
  (latexEnv := "lemma")]
lemma raw_round_error_decrease
    (conversation : canonical_conversation) (human : Bool)
    (error : ℝ → ℝ) (width : ℕ → ℝ)
    (epsilon : ℝ) (k : ℕ)
    (hcalibration :
      conversation_calibrated conversation human error width)
    (hrole : party_round human k)
    (hrun : epsilon_agreement_run conversation epsilon) (hk : 1 ≤ k) :
    squared_error conversation Finset.univ
        (fun t => conversation.prediction
          (min k (conversation.length t)) t) ≤
      squared_error conversation Finset.univ
        (fun t => conversation.prediction
          (min (k - 1) (conversation.length t)) t) -
      epsilon ^ 2 *
        (round_subsequence conversation (k + 1)).card +
      width conversation.horizon * conversation.horizon +
      3 * (error (width conversation.horizon * conversation.horizon) /
        width conversation.horizon) := by
  classical
  rcases hcalibration with
    ⟨herror, hwpos, hwle, ⟨n, hn, hwrec⟩, hlocal⟩
  let w := width conversation.horizon
  change 0 < w at hwpos
  change w ≤ 1 at hwle
  change w = (n : ℝ)⁻¹ at hwrec
  have hn0 : n ≠ 0 := by omega
  have hepsilon : 0 < epsilon := by
    let t : Fin conversation.horizon := ⟨0, conversation.horizon_pos⟩
    exact (abs_nonneg _).trans_lt (hrun.2 t).1
  let active := round_subsequence conversation k
  let next := round_subsequence conversation (k + 1)
  let index (t : Fin conversation.horizon) : ℕ :=
    bucket_index w (conversation.prediction (k - 1) t)
  have hceil : ⌈w⁻¹⌉₊ = n := by
    rw [hwrec]
    simp [hn0]
  have hindex (t : Fin conversation.horizon) :
      index t ∈ Finset.Icc 1 n := by
    rw [Finset.mem_Icc]
    change 1 ≤ min ⌈w⁻¹⌉₊
        (max 1 ⌈conversation.prediction (k - 1) t / w⌉₊) ∧
      min ⌈w⁻¹⌉₊
        (max 1 ⌈conversation.prediction (k - 1) t / w⌉₊) ≤ n
    rw [hceil]
    exact ⟨le_min hn (le_max_left _ _), min_le_left _ _⟩
  have hlocal' : ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ∃ calibrated : Fin conversation.horizon → ℝ,
        (∀ t ∈ previous_round_bucket_days conversation w k i,
          calibrated t ∈ Set.Icc (0 : ℝ) 1) ∧
        perfectly_calibrated conversation
          (previous_round_bucket_days conversation w k i) calibrated ∧
        (∑ t ∈ previous_round_bucket_days conversation w k i,
          |conversation.prediction k t - calibrated t|) ≤
          error ((previous_round_bucket_days conversation w k i).card : ℝ) := by
    intro i hi₁ hi₂
    have hiCeil : i ≤ ⌈(width conversation.horizon)⁻¹⌉₊ := by
      change i ≤ ⌈w⁻¹⌉₊
      simpa [hceil] using hi₂
    simpa only [w] using hlocal k hrole i hi₁ hiCeil
  let localPredictor (i : ℕ) : Fin conversation.horizon → ℝ :=
    if hi : 1 ≤ i ∧ i ≤ n then
      Classical.choose (hlocal' i hi.1 hi.2)
    else fun _ => 0
  have hlocalSpec (i : ℕ) (hi₁ : 1 ≤ i) (hi₂ : i ≤ n) :
      (∀ t ∈ previous_round_bucket_days conversation w k i,
        localPredictor i t ∈ Set.Icc (0 : ℝ) 1) ∧
      perfectly_calibrated conversation
        (previous_round_bucket_days conversation w k i)
        (localPredictor i) ∧
      (∑ t ∈ previous_round_bucket_days conversation w k i,
        |conversation.prediction k t - localPredictor i t|) ≤
        error ((previous_round_bucket_days conversation w k i).card : ℝ) := by
    have hEq : localPredictor i =
        Classical.choose (hlocal' i hi₁ hi₂) := by
      simp [localPredictor, hi₁, hi₂]
    rw [hEq]
    exact Classical.choose_spec (hlocal' i hi₁ hi₂)
  let calibrated (t : Fin conversation.horizon) : ℝ :=
    localPredictor (index t) t
  have hpartition (f : Fin conversation.horizon → ℝ) :
      (∑ t ∈ active, f t) =
        ∑ i ∈ Finset.Icc 1 n,
          ∑ t ∈ previous_round_bucket_days conversation w k i, f t := by
    symm
    change (∑ i ∈ Finset.Icc 1 n,
      ∑ t ∈ active with index t = i, f t) = ∑ t ∈ active, f t
    rw [Finset.sum_fiberwise_eq_sum_filter]
    rw [Finset.filter_eq_self.2]
    intro t ht
    exact hindex t
  have hbucket (i : ℕ) (hi : i ∈ Finset.Icc 1 n) :
      (∑ t ∈ previous_round_bucket_days conversation w k i,
        ((conversation.prediction k t - conversation.label t) ^ 2 -
          (conversation.prediction (k - 1) t - conversation.label t) ^ 2 +
          (if epsilon ≤
              |conversation.prediction k t -
                conversation.prediction (k - 1) t|
            then epsilon ^ 2 else 0) -
          3 * |conversation.prediction k t - localPredictor i t| - w)) ≤ 0 := by
    have hi₁ := (Finset.mem_Icc.mp hi).1
    have hi₂ := (Finset.mem_Icc.mp hi).2
    have hc : (i : ℝ) * w ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact mul_nonneg (by positivity) hwpos.le
      · calc
          (i : ℝ) * w ≤ (n : ℝ) * w :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hi₂) hwpos.le
          _ = 1 := by simp [hwrec, hn0]
    apply calibrated_unrounded_bucket_sum_bound conversation
      (previous_round_bucket_days conversation w k i)
      (localPredictor i) (conversation.prediction k)
      (conversation.prediction (k - 1))
      w epsilon ((i : ℝ) * w) hwpos.le hwle hepsilon.le hc
      (hlocalSpec i hi₁ hi₂).1
      (fun t _ => conversation.prediction_mem k t)
      (fun t _ => conversation.prediction_mem (k - 1) t)
      (fun t ht => by
        have hidx : bucket_index w
            (conversation.prediction (k - 1) t) = i :=
          (Finset.mem_filter.mp ht).2
        have hround := reciprocal_bucketed_value_bounds w
          (conversation.prediction (k - 1) t) n hwpos hn hwrec
          (conversation.prediction_mem (k - 1) t)
        simpa [hidx] using hround.2.1)
      (fun t ht => by
        have hidx : bucket_index w
            (conversation.prediction (k - 1) t) = i :=
          (Finset.mem_filter.mp ht).2
        have hround := reciprocal_bucketed_value_bounds w
          (conversation.prediction (k - 1) t) n hwpos hn hwrec
          (conversation.prediction_mem (k - 1) t)
        simpa [hidx] using hround.2.2)
      (hlocalSpec i hi₁ hi₂).2.1
  have hactive :
      (∑ t ∈ active,
        ((conversation.prediction k t - conversation.label t) ^ 2 -
          (conversation.prediction (k - 1) t - conversation.label t) ^ 2 +
          (if epsilon ≤
              |conversation.prediction k t -
                conversation.prediction (k - 1) t|
            then epsilon ^ 2 else 0) -
          3 * |conversation.prediction k t - calibrated t| - w)) ≤ 0 := by
    rw [hpartition]
    apply Finset.sum_nonpos
    intro i hi
    calc
      _ = ∑ t ∈ previous_round_bucket_days conversation w k i,
          (((conversation.prediction k t - conversation.label t) ^ 2 -
            (conversation.prediction (k - 1) t - conversation.label t) ^ 2 +
            (if epsilon ≤ |conversation.prediction k t -
                conversation.prediction (k - 1) t|
              then epsilon ^ 2 else 0)) -
            3 * |conversation.prediction k t - localPredictor i t| - w) := by
          apply Finset.sum_congr rfl
          intro t ht
          have hidx : index t = i := by
            simpa [index, previous_round_bucket_days] using
              (Finset.mem_filter.mp ht).2
          simp [calibrated, hidx]
      _ ≤ 0 := hbucket i hi
  have hdistance :
      (∑ t ∈ active,
        |conversation.prediction k t - calibrated t|) ≤
        error (w * conversation.horizon) / w := by
    calc
      _ = ∑ i ∈ Finset.Icc 1 n,
          ∑ t ∈ previous_round_bucket_days conversation w k i,
            |conversation.prediction k t - calibrated t| := hpartition _
      _ = ∑ i ∈ Finset.Icc 1 n,
          ∑ t ∈ previous_round_bucket_days conversation w k i,
            |conversation.prediction k t - localPredictor i t| := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro t ht
          have hidx : index t = i := by
            simpa [index, previous_round_bucket_days] using
              (Finset.mem_filter.mp ht).2
          simp [calibrated, hidx]
      _ ≤ ∑ i ∈ Finset.Icc 1 n,
          error ((previous_round_bucket_days conversation w k i).card : ℝ) := by
          exact Finset.sum_le_sum fun i hi =>
            (hlocalSpec i (Finset.mem_Icc.mp hi).1
              (Finset.mem_Icc.mp hi).2).2.2
      _ ≤ error (w * conversation.horizon) / w :=
          bucket_error_sum_bound conversation error w k n herror hwpos hn hwrec
  have hnext_active : next ⊆ active := by
    intro t ht
    simp only [next, active, round_subsequence, Finset.mem_filter,
      Finset.mem_univ, true_and] at ht ⊢
    omega
  have hsep_iff (t : Fin conversation.horizon) (ht : t ∈ active) :
      epsilon ≤ |conversation.prediction k t -
        conversation.prediction (k - 1) t| ↔ t ∈ next := by
    constructor
    · intro hsep
      by_contra hnot
      have hlength : conversation.length t = k := by
        have hak : k ≤ conversation.length t := by
          simpa [active, round_subsequence] using ht
        have hlt : conversation.length t < k + 1 := by
          simpa [next, round_subsequence, not_le] using hnot
        omega
      have hterminal := (hrun.2 t).1
      rw [hlength] at hterminal
      exact (not_lt_of_ge hsep) (by simpa [abs_sub_comm] using hterminal)
    · intro htnext
      have hlt : k < conversation.length t := by
        have : k + 1 ≤ conversation.length t := by
          simpa [next, round_subsequence] using htnext
        omega
      exact (hrun.2 t).2 k hk hlt
  have hcharge :
      (∑ t ∈ active,
        if epsilon ≤ |conversation.prediction k t -
            conversation.prediction (k - 1) t|
          then epsilon ^ 2 else 0) =
        epsilon ^ 2 * next.card := by
    have hrewrite : (∑ t ∈ active,
        if epsilon ≤ |conversation.prediction k t -
            conversation.prediction (k - 1) t|
          then epsilon ^ 2 else 0) =
        ∑ t ∈ active, if t ∈ next then epsilon ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      simp only [hsep_iff t ht]
    rw [hrewrite, Finset.sum_ite]
    have hfilter : active.filter (fun t => t ∈ next) = next := by
      ext t
      simp [hnext_active]
    rw [hfilter]
    simp [mul_comm]
  have hloss_active :
      (∑ t ∈ active,
        ((conversation.prediction k t - conversation.label t) ^ 2 -
          (conversation.prediction (k - 1) t - conversation.label t) ^ 2)) ≤
        -epsilon ^ 2 * next.card + w * active.card +
          3 * (error (w * conversation.horizon) / w) := by
    have hrewrite :
        (∑ t ∈ active,
          ((conversation.prediction k t - conversation.label t) ^ 2 -
            (conversation.prediction (k - 1) t - conversation.label t) ^ 2 +
            (if epsilon ≤ |conversation.prediction k t -
                conversation.prediction (k - 1) t|
              then epsilon ^ 2 else 0) -
            3 * |conversation.prediction k t - calibrated t| - w)) =
          (∑ t ∈ active,
            ((conversation.prediction k t - conversation.label t) ^ 2 -
              (conversation.prediction (k - 1) t - conversation.label t) ^ 2)) +
          (∑ t ∈ active,
            if epsilon ≤ |conversation.prediction k t -
                conversation.prediction (k - 1) t|
              then epsilon ^ 2 else 0) -
          3 * (∑ t ∈ active,
            |conversation.prediction k t - calibrated t|) - w * active.card := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_add_distrib]
      simp [← Finset.mul_sum]
      ring
    rw [hrewrite, hcharge] at hactive
    nlinarith
  let frozen (j : ℕ) (t : Fin conversation.horizon) : ℝ :=
    conversation.prediction (min j (conversation.length t)) t
  have hinactive (t : Fin conversation.horizon) (ht : t ∉ active) :
      frozen k t = frozen (k - 1) t := by
    have htlt : conversation.length t < k := by
      simpa [active, round_subsequence, not_le] using ht
    have htprev : conversation.length t ≤ k - 1 := by omega
    simp [frozen, min_eq_right htlt.le, min_eq_right htprev]
  have hall_active :
      (∑ t ∈ Finset.univ,
        ((frozen k t - conversation.label t) ^ 2 -
          (frozen (k - 1) t - conversation.label t) ^ 2)) =
        ∑ t ∈ active,
          ((conversation.prediction k t - conversation.label t) ^ 2 -
            (conversation.prediction (k - 1) t - conversation.label t) ^ 2) := by
    calc
      _ = ∑ t ∈ active,
          ((frozen k t - conversation.label t) ^ 2 -
            (frozen (k - 1) t - conversation.label t) ^ 2) := by
          symm
          apply Finset.sum_subset (by simp [active, round_subsequence])
          intro t htuniv htactive
          rw [hinactive t htactive]
          ring
      _ = _ := by
          apply Finset.sum_congr rfl
          intro t ht
          have htk : k ≤ conversation.length t := by
            simpa [active, round_subsequence] using ht
          have htkprev : k - 1 ≤ conversation.length t := by omega
          simp [frozen, min_eq_left htk, min_eq_left htkprev]
  have hcard_active : (active.card : ℝ) ≤ conversation.horizon := by
    exact_mod_cast (show active.card ≤ conversation.horizon by
      simpa using Finset.card_le_univ active)
  change squared_error conversation Finset.univ (frozen k) ≤
    squared_error conversation Finset.univ (frozen (k - 1)) -
      epsilon ^ 2 * next.card + w * conversation.horizon +
      3 * (error (w * conversation.horizon) / w)
  unfold squared_error
  have hwcard : w * active.card ≤ w * conversation.horizon :=
    mul_le_mul_of_nonneg_left hcard_active hwpos.le
  have htotal :
      (∑ t ∈ Finset.univ,
          (frozen k t - conversation.label t) ^ 2) -
        (∑ t ∈ Finset.univ,
          (frozen (k - 1) t - conversation.label t) ^ 2) ≤
        -epsilon ^ 2 * next.card + w * conversation.horizon +
          3 * (error (w * conversation.horizon) / w) := by
    rw [← Finset.sum_sub_distrib, hall_active]
    nlinarith
  nlinarith

@[blueprint "lem:two-round-error-decrease"
  (statement := /-- Let \(C\) be a canonical conversation with horizon \(T\), let \(\epsilon\in\mathbb R\), and let \(k\geq2\) be even. Suppose that the Human and Model are respectively \((f_h,g_h)\)- and \((f_m,g_m)\)-conversation-calibrated and that \(C\) is an \(\epsilon\)-agreement run. Then
  \[
  \begin{aligned}
  \operatorname{SQErr}(\bar p_h^k,y)
  &\leq \operatorname{SQErr}(\bar p_h^{k-2},y)
  -2\epsilon^2|T^{\geq k+1}|\\
  &\quad +3(g_m(T)+g_h(T))T
  +3\left(\frac{f_m(g_m(T)T)}{g_m(T)}
  +\frac{f_h(g_h(T)T)}{g_h(T)}\right).
  \end{aligned}
  \] -/)
  (proof := /-- For every round \(j\), freeze the raw transcript on a day after its terminal round. Apply \cref{lem:raw-round-error-decrease} to the Human at round \(k\) and to the Model at round \(k-1\). The intermediate frozen raw squared errors cancel. By the nesting in \cref{def:round-subsequence}, \(|T^{\geq k}|\geq|T^{\geq k+1}|\); since \(\epsilon^2\geq0\), the two separation charges are therefore at least \(2\epsilon^2|T^{\geq k+1}|\).

  It remains to replace the frozen raw predictions at rounds \(k\) and \(k-2\) by their common Human-width bucketings from \cref{def:bucketed-round-prediction}. The range and displacement assertions in \cref{lem:reciprocal-bucketed-value-bounds}, followed pointwise by \cref{lem:common-upper-rounding-difference}, show that this replacement increases the squared-error difference by at most \(2g_h(T)T\). Adding this to the raw width loss \((g_h(T)+g_m(T))T\), and using \(g_m(T)\geq0\), bounds the total width loss by \(3(g_m(T)+g_h(T))T\). The two calibration-error losses are already the displayed terms. -/)
  (title := /-- Two-round squared-error decrease -/)
  (latexEnv := "lemma")]
lemma two_round_error_decrease
    (conversation : canonical_conversation)
    (humanError modelError : ℝ → ℝ)
    (humanWidth modelWidth : ℕ → ℝ)
    (epsilon : ℝ) (k : ℕ)
    (hhuman :
      conversation_calibrated conversation true humanError humanWidth)
    (hmodel :
      conversation_calibrated conversation false modelError modelWidth)
    (hrun : epsilon_agreement_run conversation epsilon)
    (hk : 2 ≤ k) (hkeven : k % 2 = 0) :
    squared_error conversation Finset.univ
        (bucketed_round_prediction conversation
          (humanWidth conversation.horizon) k) ≤
      squared_error conversation Finset.univ
        (bucketed_round_prediction conversation
          (humanWidth conversation.horizon) (k - 2)) -
      2 * epsilon ^ 2 *
        (round_subsequence conversation (k + 1)).card +
      3 * (modelWidth conversation.horizon +
        humanWidth conversation.horizon) * conversation.horizon +
      3 * (modelError
          (modelWidth conversation.horizon * conversation.horizon) /
            modelWidth conversation.horizon +
        humanError
          (humanWidth conversation.horizon * conversation.horizon) /
            humanWidth conversation.horizon) := by
  classical
  let frozen (j : ℕ) (t : Fin conversation.horizon) : ℝ :=
    conversation.prediction (min j (conversation.length t)) t
  have hhumanRole : party_round true k := by
    left
    exact ⟨rfl, hkeven⟩
  have hmodelRole : party_round false (k - 1) := by
    right
    constructor
    · rfl
    · omega
  have hkone : 1 ≤ k := by omega
  have hkprev : 1 ≤ k - 1 := by omega
  have hhumanRaw := raw_round_error_decrease conversation true
    humanError humanWidth epsilon k hhuman hhumanRole hrun hkone
  have hmodelRaw := raw_round_error_decrease conversation false
    modelError modelWidth epsilon (k - 1) hmodel hmodelRole hrun hkprev
  have hsubsub : k - 1 - 1 = k - 2 := by omega
  have hsubadd : k - 1 + 1 = k := by omega
  change squared_error conversation Finset.univ (frozen k) ≤
      squared_error conversation Finset.univ (frozen (k - 1)) -
        epsilon ^ 2 * (round_subsequence conversation (k + 1)).card +
        humanWidth conversation.horizon * conversation.horizon +
        3 * (humanError
          (humanWidth conversation.horizon * conversation.horizon) /
            humanWidth conversation.horizon) at hhumanRaw
  change squared_error conversation Finset.univ (frozen (k - 1)) ≤
      squared_error conversation Finset.univ (frozen (k - 1 - 1)) -
        epsilon ^ 2 *
          (round_subsequence conversation (k - 1 + 1)).card +
        modelWidth conversation.horizon * conversation.horizon +
        3 * (modelError
          (modelWidth conversation.horizon * conversation.horizon) /
            modelWidth conversation.horizon) at hmodelRaw
  rw [hsubsub, hsubadd] at hmodelRaw
  have hsubset : round_subsequence conversation (k + 1) ⊆
      round_subsequence conversation k := by
    intro t ht
    simp only [round_subsequence, Finset.mem_filter, Finset.mem_univ,
      true_and] at ht ⊢
    omega
  have hcard :
      ((round_subsequence conversation (k + 1)).card : ℝ) ≤
        (round_subsequence conversation k).card := by
    exact_mod_cast Finset.card_le_card hsubset
  have hraw : squared_error conversation Finset.univ (frozen k) ≤
      squared_error conversation Finset.univ (frozen (k - 2)) -
        2 * epsilon ^ 2 *
          (round_subsequence conversation (k + 1)).card +
        (humanWidth conversation.horizon +
          modelWidth conversation.horizon) * conversation.horizon +
        3 * (humanError
            (humanWidth conversation.horizon * conversation.horizon) /
              humanWidth conversation.horizon +
          modelError
            (modelWidth conversation.horizon * conversation.horizon) /
              modelWidth conversation.horizon) := by
    nlinarith [sq_nonneg epsilon]
  obtain ⟨humanBuckets, hhumanBuckets, hhumanReciprocal⟩ :=
    hhuman.2.2.2.1
  have hhumanWidthPos : 0 < humanWidth conversation.horizon :=
    hhuman.2.1
  have hmodelWidthNonneg : 0 ≤ modelWidth conversation.horizon :=
    (hmodel.2.1).le
  have hroundPoint (t : Fin conversation.horizon) :
      (bucketed_round_prediction conversation
          (humanWidth conversation.horizon) k t - conversation.label t) ^ 2 -
        (bucketed_round_prediction conversation
          (humanWidth conversation.horizon) (k - 2) t -
            conversation.label t) ^ 2 ≤
      (frozen k t - conversation.label t) ^ 2 -
        (frozen (k - 2) t - conversation.label t) ^ 2 +
          2 * humanWidth conversation.horizon := by
    have hkBounds := reciprocal_bucketed_value_bounds
      (humanWidth conversation.horizon) (frozen k t) humanBuckets
      hhumanWidthPos hhumanBuckets hhumanReciprocal
      (conversation.prediction_mem (min k (conversation.length t)) t)
    have hkTwoBounds := reciprocal_bucketed_value_bounds
      (humanWidth conversation.horizon) (frozen (k - 2) t) humanBuckets
      hhumanWidthPos hhumanBuckets hhumanReciprocal
      (conversation.prediction_mem (min (k - 2) (conversation.length t)) t)
    apply common_upper_rounding_difference
      (humanWidth conversation.horizon) (conversation.label t)
      (frozen k t) (frozen (k - 2) t)
      (bucketed_round_prediction conversation
        (humanWidth conversation.horizon) k t)
      (bucketed_round_prediction conversation
        (humanWidth conversation.horizon) (k - 2) t)
      hhumanWidthPos.le (conversation.label_mem t)
      (conversation.prediction_mem (min k (conversation.length t)) t)
      (conversation.prediction_mem (min (k - 2) (conversation.length t)) t)
      (by simpa [bucketed_round_prediction, frozen] using hkBounds.1)
      (by simpa [bucketed_round_prediction, frozen] using hkTwoBounds.1)
      (by simpa [bucketed_round_prediction, frozen] using hkBounds.2.1)
      (by simpa [bucketed_round_prediction, frozen] using hkBounds.2.2)
      (by simpa [bucketed_round_prediction, frozen] using hkTwoBounds.2.1)
      (by simpa [bucketed_round_prediction, frozen] using hkTwoBounds.2.2)
  have hroundSum :
      (∑ t ∈ Finset.univ,
        ((bucketed_round_prediction conversation
            (humanWidth conversation.horizon) k t - conversation.label t) ^ 2 -
          (bucketed_round_prediction conversation
            (humanWidth conversation.horizon) (k - 2) t -
              conversation.label t) ^ 2)) ≤
      (∑ t ∈ Finset.univ,
        ((frozen k t - conversation.label t) ^ 2 -
          (frozen (k - 2) t - conversation.label t) ^ 2)) +
        2 * humanWidth conversation.horizon * conversation.horizon := by
    calc
      _ ≤ ∑ t ∈ Finset.univ,
          ((frozen k t - conversation.label t) ^ 2 -
            (frozen (k - 2) t - conversation.label t) ^ 2 +
              2 * humanWidth conversation.horizon) :=
        Finset.sum_le_sum fun t ht => hroundPoint t
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp
        ring
  unfold squared_error at hraw ⊢
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hroundSum
  nlinarith [mul_nonneg hmodelWidthNonneg
    (show (0 : ℝ) ≤ conversation.horizon by positivity)]

@[blueprint "lem:recursive-error-improvement"
  (statement := /-- Let \(C\) be a canonical conversation with horizon \(T\), let \(f_h,f_m\colon\mathbb R\to\mathbb R\) and \(g_h,g_m\colon\mathbb N\to\mathbb R\), and let \(\epsilon,\delta\in[0,1]\). Suppose that the Human and Model are respectively \((f_h,g_h)\)- and \((f_m,g_m)\)-conversation-calibrated and that \(C\) is an \(\epsilon\)-agreement run. Put \(q=\epsilon^2\delta-\beta(T)\). For every even Human round \(k\geq2\) satisfying \(|T^{\geq k+1}|\geq\delta T\),
  \[
  \frac{\operatorname{SQErr}(\bar p_h^k,y)}{T}
  \leq
  \min\left\{
  \frac{\operatorname{SQErr}(\bar p_m^1,y)}{T}-q,
  \frac{\operatorname{SQErr}(\bar p_h^2,y)}{T}
  \right\}-(k-2)q.
  \]
  Thus the recursive decrement is zero at the Human round-(2) baseline, while the Model round-(1) baseline also includes the preceding one-round decrement. -/)
  (proof := /-- Write \(T\) for the positive horizon and put
  \[
  q=\epsilon^2\delta-\beta(T).
  \]
  Apply \cref{lem:bucketwise-calibrated-surrogate} to the Human at round \(2\) and to the Model at round \(1\). Each resulting sum of absolute deviations is nonnegative. Since both bucket widths are positive, the corresponding calibration-loss ratios are nonnegative. Expanding \cref{def:beta-error} and clearing the positive factor \(T\) gives
  \[
  \beta(T)T=3(g_m(T)+g_h(T))T
    +3\left(\frac{f_m(g_m(T)T)}{g_m(T)}
      +\frac{f_h(g_h(T)T)}{g_h(T)}\right),
  \]
  and hence \(\beta(T)\geq0\).

  First suppose that \(|T^{\geq3}|\geq\delta T\). The Human instance of \cref{lem:round-error-decrease} at round \(2\) records the corresponding same-width bucketed estimate. For the mixed-width comparison required here, freeze the raw transcript after the terminal round as in \cref{def:bucketed-round-prediction}. The Human instance of \cref{lem:raw-round-error-decrease} at round \(2\) bounds the raw squared-error change from round \(1\) to round \(2\). By \cref{lem:reciprocal-bucketed-value-bounds}, the Human-width bucketing of the round-\(2\) raw prediction and the Model-width bucketing of the round-\(1\) raw prediction both lie in \([0,1]\), lie above their raw predictions, and move them by at most \(g_h(T)\) and \(g_m(T)\), respectively. Apply \cref{lem:common-upper-rounding-difference} with common displacement bound \(g_h(T)+g_m(T)\), and sum over all \(T\) days. The rounding contribution is at most \(2(g_h(T)+g_m(T))T\). Together with the raw-round contribution, the total loss is
  \[
  (3g_h(T)+2g_m(T))T+
    3\frac{f_h(g_h(T)T)}{g_h(T)},
  \]
  which is at most \(\beta(T)T\) because \(g_m(T)\geq0\) and the Model calibration-loss ratio is nonnegative. The survivor hypothesis therefore yields
  \[
  \operatorname{SQErr}(\bar p_h^2,y)
  \leq \operatorname{SQErr}(\bar p_m^1,y)-qT.
  \]

  Now use strong induction on the even Human round \(k\). The case \(k=2\) follows from the preceding inequality and the fact that the second entry of the displayed minimum is the left-hand side itself. For \(k\geq4\), nesting of the sets in \cref{def:round-subsequence} transfers the survivor hypothesis from \(T^{\geq k+1}\) to the induction index \(k-2\). The induction hypothesis thus bounds the normalized error at round \(k-2\). On the other hand, \cref{lem:two-round-error-decrease}, the lower bound \(|T^{\geq k+1}|\geq\delta T\), and the identity for \(\beta(T)T\) give
  \[
  \frac{\operatorname{SQErr}(\bar p_h^k,y)}{T}
  \leq
  \frac{\operatorname{SQErr}(\bar p_h^{k-2},y)}{T}
    -\bigl(2\epsilon^2\delta-\beta(T)\bigr)
  \leq
  \frac{\operatorname{SQErr}(\bar p_h^{k-2},y)}{T}-2q,
  \]
  where the second inequality uses \(\beta(T)\geq0\). Substituting the induction hypothesis and using the even-round identity in \cref{def:human-bucketed-round-prediction} changes the decrement from \((k-4)q\) to \((k-2)q\). This is the asserted inequality. -/)
  (title := /-- Recursive linear error improvement -/)
  (latexEnv := "lemma")]
lemma recursive_error_improvement
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
    ∀ k : ℕ,
      2 ≤ k →
      k % 2 = 0 →
      delta * conversation.horizon ≤
        (round_subsequence conversation (k + 1)).card →
      squared_error conversation Finset.univ
          (human_bucketed_round_prediction conversation
            humanWidth k) /
          conversation.horizon ≤
        min
          (squared_error conversation Finset.univ
                (bucketed_round_prediction conversation
                  (modelWidth conversation.horizon) 1) /
              conversation.horizon -
            (epsilon ^ 2 * delta -
              beta_error conversation humanError modelError
                humanWidth modelWidth))
          (squared_error conversation Finset.univ
                (bucketed_round_prediction conversation
                  (humanWidth conversation.horizon) 2) /
              conversation.horizon) -
          ((k : ℝ) - 2) * (epsilon ^ 2 * delta -
            beta_error conversation humanError modelError
              humanWidth modelWidth) := by
  classical
  have hTpos : (0 : ℝ) < conversation.horizon := by
    exact_mod_cast conversation.horizon_pos
  have hhumanWidthPos : 0 < humanWidth conversation.horizon :=
    hhuman.2.1
  have hmodelWidthPos : 0 < modelWidth conversation.horizon :=
    hmodel.2.1
  have hhumanRoleTwo : party_round true 2 := by
    simp [party_round]
  have hmodelRoleOne : party_round false 1 := by
    simp [party_round]
  have hhumanRoundTwo :=
    round_error_decrease conversation true humanError humanWidth epsilon 2
      hhuman hhumanRoleTwo hrun (by omega)
  have hhumanEven (j : ℕ) (hjeven : j % 2 = 0) :
      human_bucketed_round_prediction conversation humanWidth j =
        bucketed_round_prediction conversation
          (humanWidth conversation.horizon) j := by
    funext t
    simp [human_bucketed_round_prediction, hjeven]
  obtain ⟨humanCalibrated, _, _, hhumanClose⟩ :=
    bucketwise_calibrated_surrogate conversation true humanError
      humanWidth 2 hhuman hhumanRoleTwo
  obtain ⟨modelCalibrated, _, _, hmodelClose⟩ :=
    bucketwise_calibrated_surrogate conversation false modelError
      modelWidth 1 hmodel hmodelRoleOne
  have hhumanLoss :
      0 ≤ humanError
          (humanWidth conversation.horizon * conversation.horizon) /
        humanWidth conversation.horizon := by
    exact (Finset.sum_nonneg fun t _ =>
      abs_nonneg (conversation.prediction 2 t - humanCalibrated t)).trans
        hhumanClose
  have hmodelLoss :
      0 ≤ modelError
          (modelWidth conversation.horizon * conversation.horizon) /
        modelWidth conversation.horizon := by
    exact (Finset.sum_nonneg fun t _ =>
      abs_nonneg (conversation.prediction 1 t - modelCalibrated t)).trans
        hmodelClose
  have hbetaMul :
      beta_error conversation humanError modelError humanWidth modelWidth *
          conversation.horizon =
        3 * (modelWidth conversation.horizon +
            humanWidth conversation.horizon) * conversation.horizon +
          3 * (modelError
              (modelWidth conversation.horizon * conversation.horizon) /
                modelWidth conversation.horizon +
            humanError
              (humanWidth conversation.horizon * conversation.horizon) /
                humanWidth conversation.horizon) := by
    unfold beta_error
    field_simp [ne_of_gt hTpos, ne_of_gt hhumanWidthPos,
      ne_of_gt hmodelWidthPos]
    <;> ring
  have hbetaNonneg :
      0 ≤ beta_error conversation humanError modelError
        humanWidth modelWidth := by
    have hproduct :
        0 ≤ beta_error conversation humanError modelError
            humanWidth modelWidth * conversation.horizon := by
      rw [hbetaMul]
      nlinarith [mul_nonneg hmodelWidthPos.le hTpos.le,
        mul_nonneg hhumanWidthPos.le hTpos.le]
    by_contra hnegative
    have hproductNeg :
        beta_error conversation humanError modelError humanWidth modelWidth *
            conversation.horizon < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hnegative) hTpos
    linarith
  have hinitial
      (hsurvive :
        delta * conversation.horizon ≤
          (round_subsequence conversation 3).card) :
      squared_error conversation Finset.univ
          (bucketed_round_prediction conversation
            (humanWidth conversation.horizon) 2) ≤
        squared_error conversation Finset.univ
            (bucketed_round_prediction conversation
              (modelWidth conversation.horizon) 1) -
          (epsilon ^ 2 * delta -
            beta_error conversation humanError modelError
              humanWidth modelWidth) * conversation.horizon := by
    let frozen (j : ℕ) (t : Fin conversation.horizon) : ℝ :=
      conversation.prediction (min j (conversation.length t)) t
    have hraw := raw_round_error_decrease conversation true
      humanError humanWidth epsilon 2 hhuman hhumanRoleTwo hrun (by omega)
    change squared_error conversation Finset.univ (frozen 2) ≤
        squared_error conversation Finset.univ (frozen 1) -
          epsilon ^ 2 * (round_subsequence conversation 3).card +
          humanWidth conversation.horizon * conversation.horizon +
          3 * (humanError
            (humanWidth conversation.horizon * conversation.horizon) /
              humanWidth conversation.horizon) at hraw
    obtain ⟨humanBucketCount, hhumanBucketCount,
        hhumanReciprocal⟩ := hhuman.2.2.2.1
    obtain ⟨modelBucketCount, hmodelBucketCount,
        hmodelReciprocal⟩ := hmodel.2.2.2.1
    have hroundPoint (t : Fin conversation.horizon) :
        (bucketed_round_prediction conversation
              (humanWidth conversation.horizon) 2 t -
            conversation.label t) ^ 2 -
          (bucketed_round_prediction conversation
              (modelWidth conversation.horizon) 1 t -
            conversation.label t) ^ 2 ≤
        (frozen 2 t - conversation.label t) ^ 2 -
          (frozen 1 t - conversation.label t) ^ 2 +
            2 * (humanWidth conversation.horizon +
              modelWidth conversation.horizon) := by
      have hhumanBounds :=
        reciprocal_bucketed_value_bounds
          (humanWidth conversation.horizon) (frozen 2 t)
          humanBucketCount hhumanWidthPos hhumanBucketCount
          hhumanReciprocal
          (by
            simpa [frozen] using
              conversation.prediction_mem
                (min 2 (conversation.length t)) t)
      have hmodelBounds :=
        reciprocal_bucketed_value_bounds
          (modelWidth conversation.horizon) (frozen 1 t)
          modelBucketCount hmodelWidthPos hmodelBucketCount
          hmodelReciprocal
          (by
            simpa [frozen] using
              conversation.prediction_mem
                (min 1 (conversation.length t)) t)
      have hhumanBounds' :
          bucketed_round_prediction conversation
                (humanWidth conversation.horizon) 2 t ∈
              Set.Icc (0 : ℝ) 1 ∧
            frozen 2 t ≤
              bucketed_round_prediction conversation
                (humanWidth conversation.horizon) 2 t ∧
            bucketed_round_prediction conversation
                (humanWidth conversation.horizon) 2 t ≤
              frozen 2 t + humanWidth conversation.horizon := by
        simpa [bucketed_round_prediction, frozen] using hhumanBounds
      have hmodelBounds' :
          bucketed_round_prediction conversation
                (modelWidth conversation.horizon) 1 t ∈
              Set.Icc (0 : ℝ) 1 ∧
            frozen 1 t ≤
              bucketed_round_prediction conversation
                (modelWidth conversation.horizon) 1 t ∧
            bucketed_round_prediction conversation
                (modelWidth conversation.horizon) 1 t ≤
              frozen 1 t + modelWidth conversation.horizon := by
        simpa [bucketed_round_prediction, frozen] using hmodelBounds
      exact common_upper_rounding_difference
        (humanWidth conversation.horizon + modelWidth conversation.horizon)
        (conversation.label t) (frozen 2 t) (frozen 1 t)
        (bucketed_round_prediction conversation
          (humanWidth conversation.horizon) 2 t)
        (bucketed_round_prediction conversation
          (modelWidth conversation.horizon) 1 t)
        (add_nonneg hhumanWidthPos.le hmodelWidthPos.le)
        (conversation.label_mem t)
        (by
          simpa [frozen] using
            conversation.prediction_mem
              (min 2 (conversation.length t)) t)
        (by
          simpa [frozen] using
            conversation.prediction_mem
              (min 1 (conversation.length t)) t)
        hhumanBounds'.1 hmodelBounds'.1 hhumanBounds'.2.1
        (by linarith [hhumanBounds'.2.2])
        hmodelBounds'.2.1 (by linarith [hmodelBounds'.2.2])
    have hroundComparison :
        squared_error conversation Finset.univ
              (bucketed_round_prediction conversation
                (humanWidth conversation.horizon) 2) -
            squared_error conversation Finset.univ
              (bucketed_round_prediction conversation
                (modelWidth conversation.horizon) 1) ≤
          squared_error conversation Finset.univ (frozen 2) -
            squared_error conversation Finset.univ (frozen 1) +
              2 * (humanWidth conversation.horizon +
                modelWidth conversation.horizon) *
                  conversation.horizon := by
      unfold squared_error
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ t ∈ Finset.univ,
            ((frozen 2 t - conversation.label t) ^ 2 -
              (frozen 1 t - conversation.label t) ^ 2 +
                2 * (humanWidth conversation.horizon +
                  modelWidth conversation.horizon)) :=
          Finset.sum_le_sum fun t _ => hroundPoint t
        _ = _ := by
          rw [Finset.sum_add_distrib]
          simp
          ring
    have hcharge :
        epsilon ^ 2 * (delta * conversation.horizon) ≤
          epsilon ^ 2 *
            (round_subsequence conversation 3).card :=
      mul_le_mul_of_nonneg_left hsurvive (sq_nonneg epsilon)
    nlinarith [hraw, hroundComparison,
      mul_nonneg hmodelWidthPos.le hTpos.le]
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk hkeven hsurvive
      by_cases hkTwo : k = 2
      · subst k
        have hbase := hinitial hsurvive
        have hbaseNormalized :
            squared_error conversation Finset.univ
                  (bucketed_round_prediction conversation
                    (humanWidth conversation.horizon) 2) /
                conversation.horizon ≤
              squared_error conversation Finset.univ
                    (bucketed_round_prediction conversation
                      (modelWidth conversation.horizon) 1) /
                  conversation.horizon -
                (epsilon ^ 2 * delta -
                  beta_error conversation humanError modelError
                    humanWidth modelWidth) := by
          calc
            _ ≤ (squared_error conversation Finset.univ
                    (bucketed_round_prediction conversation
                      (modelWidth conversation.horizon) 1) -
                  (epsilon ^ 2 * delta -
                    beta_error conversation humanError modelError
                      humanWidth modelWidth) * conversation.horizon) /
                conversation.horizon :=
              (div_le_div_iff_of_pos_right hTpos).2 hbase
            _ = _ := by
              field_simp [ne_of_gt hTpos]
        rw [hhumanEven 2 (by norm_num)]
        norm_num
        exact hbaseNormalized
      · have hkFour : 4 ≤ k := by omega
        have hprevEven : (k - 2) % 2 = 0 := by omega
        have hsubset :
            round_subsequence conversation (k + 1) ⊆
              round_subsequence conversation (k - 2 + 1) := by
          intro t ht
          simp only [round_subsequence, Finset.mem_filter,
            Finset.mem_univ, true_and] at ht ⊢
          omega
        have hcard :
            (round_subsequence conversation (k + 1)).card ≤
              (round_subsequence conversation (k - 2 + 1)).card :=
          Finset.card_le_card hsubset
        have hsurvivePrev :
            delta * conversation.horizon ≤
              (round_subsequence conversation (k - 2 + 1)).card :=
          hsurvive.trans (by exact_mod_cast hcard)
        have hprevious :=
          ih (k - 2) (by omega) (by omega) hprevEven hsurvivePrev
        have hprevious' :
            squared_error conversation Finset.univ
                  (bucketed_round_prediction conversation
                    (humanWidth conversation.horizon) (k - 2)) /
                conversation.horizon ≤
              min
                  (squared_error conversation Finset.univ
                        (bucketed_round_prediction conversation
                          (modelWidth conversation.horizon) 1) /
                      conversation.horizon -
                    (epsilon ^ 2 * delta -
                      beta_error conversation humanError modelError
                        humanWidth modelWidth))
                  (squared_error conversation Finset.univ
                      (bucketed_round_prediction conversation
                        (humanWidth conversation.horizon) 2) /
                    conversation.horizon) -
                (((k - 2 : ℕ) : ℝ) - 2) *
                  (epsilon ^ 2 * delta -
                    beta_error conversation humanError modelError
                      humanWidth modelWidth) := by
          rw [hhumanEven (k - 2) hprevEven] at hprevious
          exact hprevious
        have htwo := two_round_error_decrease conversation humanError
          modelError humanWidth modelWidth epsilon k hhuman hmodel hrun hk
          hkeven
        have hcharge :
            2 * epsilon ^ 2 * (delta * conversation.horizon) ≤
              2 * epsilon ^ 2 *
                (round_subsequence conversation (k + 1)).card :=
          mul_le_mul_of_nonneg_left hsurvive
            (mul_nonneg (by positivity) (sq_nonneg epsilon))
        have htwoNormalized :
            squared_error conversation Finset.univ
                  (bucketed_round_prediction conversation
                    (humanWidth conversation.horizon) k) /
                conversation.horizon ≤
              squared_error conversation Finset.univ
                    (bucketed_round_prediction conversation
                      (humanWidth conversation.horizon) (k - 2)) /
                  conversation.horizon -
                2 * (epsilon ^ 2 * delta -
                  beta_error conversation humanError modelError
                    humanWidth modelWidth) := by
          have htwo' :
              squared_error conversation Finset.univ
                    (bucketed_round_prediction conversation
                      (humanWidth conversation.horizon) k) ≤
                squared_error conversation Finset.univ
                    (bucketed_round_prediction conversation
                      (humanWidth conversation.horizon) (k - 2)) -
                  2 * (epsilon ^ 2 * delta -
                    beta_error conversation humanError modelError
                      humanWidth modelWidth) * conversation.horizon := by
            nlinarith [htwo, hcharge, hbetaMul, hbetaNonneg]
          calc
            _ ≤ (squared_error conversation Finset.univ
                    (bucketed_round_prediction conversation
                      (humanWidth conversation.horizon) (k - 2)) -
                  2 * (epsilon ^ 2 * delta -
                    beta_error conversation humanError modelError
                      humanWidth modelWidth) * conversation.horizon) /
                conversation.horizon :=
              (div_le_div_iff_of_pos_right hTpos).2 htwo'
            _ = _ := by
              field_simp [ne_of_gt hTpos]
        have hkCast : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
          norm_num [Nat.cast_sub hk]
        rw [hhumanEven k hkeven]
        calc
          _ ≤ squared_error conversation Finset.univ
                  (bucketed_round_prediction conversation
                    (humanWidth conversation.horizon) (k - 2)) /
                conversation.horizon -
              2 * (epsilon ^ 2 * delta -
                beta_error conversation humanError modelError
                  humanWidth modelWidth) :=
            htwoNormalized
          _ ≤ (min
                  (squared_error conversation Finset.univ
                        (bucketed_round_prediction conversation
                          (modelWidth conversation.horizon) 1) /
                      conversation.horizon -
                    (epsilon ^ 2 * delta -
                      beta_error conversation humanError modelError
                        humanWidth modelWidth))
                  (squared_error conversation Finset.univ
                      (bucketed_round_prediction conversation
                        (humanWidth conversation.horizon) 2) /
                    conversation.horizon) -
                (((k - 2 : ℕ) : ℝ) - 2) *
                  (epsilon ^ 2 * delta -
                    beta_error conversation humanError modelError
                      humanWidth modelWidth)) -
              2 * (epsilon ^ 2 * delta -
                beta_error conversation humanError modelError
                  humanWidth modelWidth) :=
            sub_le_sub_right hprevious' _
          _ = _ := by
            rw [hkCast]
            ring

@[blueprint "lem:perfect-calibrated-squared-error-quarter-bound"
  (statement := /-- Let \(C\) be a canonical conversation, let \(S\) be a finite set of its days, and let \(p\) be perfectly calibrated on \(S\). Then
  \[
  \operatorname{SQErr}_S(p,C.\mathrm{label})\leq \frac{|S|}{4}.
  \] -/)
  (proof := /-- Apply \cref{lem:perfect-calibration-squared-error-shift} with the identity map and the constant predictor \(1/2\). The resulting identity shows that the squared error of \(p\) is at most that of the constant predictor \(1/2\), because the remaining sum is the negative of a sum of squares. Since every label lies in \([0,1]\) by \cref{def:canonical-conversation}, each squared error \((1/2-y^t)^2\) is at most \(1/4\). Summing over \(S\) gives the result. -/)
  (title := /-- Quarter-cardinality bound for a perfectly calibrated predictor -/)
  (latexEnv := "lemma")]
lemma perfect_calibrated_squared_error_quarter_bound
    (conversation : canonical_conversation)
    (days : Finset (Fin conversation.horizon))
    (predictor : Fin conversation.horizon → ℝ)
    (hperfect : perfectly_calibrated conversation days predictor) :
    squared_error conversation days predictor ≤ (days.card : ℝ) / 4 := by
  have hshift := perfect_calibration_squared_error_shift conversation days predictor
    (fun value => value) (1 / 2) hperfect
  have hsquares : 0 ≤ ∑ t ∈ days, ((1 / 2 : ℝ) - predictor t) ^ 2 :=
    Finset.sum_nonneg fun t _ => sq_nonneg _
  have hconstant :
      (∑ t ∈ days, ((1 / 2 : ℝ) - conversation.label t) ^ 2) ≤
        (days.card : ℝ) / 4 := by
    calc
      _ ≤ ∑ t ∈ days, (1 / 4 : ℝ) := by
        apply Finset.sum_le_sum
        intro t ht
        have hy := conversation.label_mem t
        nlinarith [mul_nonneg hy.1 (sub_nonneg.mpr hy.2)]
      _ = (days.card : ℝ) / 4 := by simp [div_eq_mul_inv]
  have hshift' :
      (∑ t ∈ days, (predictor t - conversation.label t) ^ 2) -
          (∑ t ∈ days, ((1 / 2 : ℝ) - conversation.label t) ^ 2) =
        -(∑ t ∈ days, ((1 / 2 : ℝ) - predictor t) ^ 2) := by
    simpa [Finset.sum_sub_distrib] using hshift
  unfold squared_error
  nlinarith [hshift']

@[blueprint "lem:surviving-round-bound"
  (statement := /-- Let \(C\) be a canonical conversation over \(T\) days, let \(f_h,f_m\colon\mathbb R\to\mathbb R\), let \(g_h,g_m\colon\mathbb N\to\mathbb R\), and let \(\epsilon,\delta\in[0,1]\). Assume that the Human is \((f_h,g_h)\)-conversation-calibrated, that the Model is \((f_m,g_m)\)-conversation-calibrated, and that \(C\) is an \(\epsilon\)-agreement run. Put \(q=\epsilon^2\delta-\beta(T)\), with \(\beta(T)\) as in \cref{def:beta-error}. For every \(k\in\mathbb N\) satisfying \(|T^{\geq k}|\geq\delta T\), one has
  \[
  kq\leq1.
  \] -/)
  (proof := /-- Write \(T\) for the positive horizon and
  \[
  q=\epsilon^2\delta-\beta(T).
  \]
  Applying \cref{lem:bucketwise-calibrated-surrogate} to the Human at round \(0\) gives a perfectly calibrated predictor on all days whose \(\ell^1\)-distance from the initial prediction is at most \(f_h(g_h(T)T)/g_h(T)\). By \cref{lem:perfect-calibrated-squared-error-quarter-bound} and \cref{lem:calibrated-squared-error-perturbation}, the unnormalized initial squared error \(S_0\) therefore satisfies
  \[
  S_0\leq \frac{T}{4}+3\frac{f_h(g_h(T)T)}{g_h(T)}.
  \]
  Independently, \cref{lem:squared-error-at-most-cardinality} bounds the same initial squared error by \(T\). Retaining both estimates gives
  \[
  S_0\leq\min\left\{\frac{T}{4}+3\frac{f_h(g_h(T)T)}{g_h(T)},T\right\},
  \]
  and in particular preserves the preceding sharper estimate used below.
  The same surrogate construction at Model round \(1\) shows that both calibration-loss ratios occurring in \(\beta(T)\) are nonnegative. Consequently \(\beta(T)\geq0\), and the definition in \cref{def:beta-error} gives the exact identity
  \[
  \beta(T)T=3(g_m(T)+g_h(T))T
    +3\left(\frac{f_m(g_m(T)T)}{g_m(T)}
      +\frac{f_h(g_h(T)T)}{g_h(T)}\right).
  \]

  Fix \(k\in\mathbb N\) with \(|T^{\geq k}|\geq\delta T\). The cases \(k=0\) and \(k=1\) follow from \(\beta(T)\geq0\), \(\epsilon,\delta\in[0,1]\), and hence \(q\leq1\). Suppose that \(k\geq2\). By the nesting in \cref{def:round-subsequence}, every \(T^{\geq j}\) with \(j\leq k\) also has cardinality at least \(\delta T\). Apply \cref{lem:raw-round-error-decrease} first at Model round \(1\). The displayed identity for \(\beta(T)T\) shows that the loss absorbed by \(\beta(T)T\) includes both the Model's one-round loss and the initial Human calibration term. Thus the squared error \(S_1\) of the frozen round-
  \(1\) transcript satisfies
  \[
  S_1\leq \frac{T}{4}-qT.
  \]
  For each \(j=2,\ldots,k-1\), apply \cref{lem:raw-round-error-decrease} to the party assigned to round \(j\). Since \(T^{\geq j+1}\) has cardinality at least \(\delta T\) and \(\beta(T)T\) dominates that party's width and calibration losses, each step gives \(S_j\leq S_{j-1}-qT\). Induction yields
  \[
  S_{k-1}\leq \frac{T}{4}-(k-1)qT.
  \]
  By \cref{lem:squared-error-nonnegative}, \(S_{k-1}\geq0\), so \((k-1)q\leq1/4\). If \(q\leq0\), the desired inequality is immediate. If \(q>0\), then \(k\leq2(k-1)\) because \(k\geq2\); hence \(kq\leq2(k-1)q\leq1/2\leq1\). -/)
  (title := /-- Bound for a sufficiently populated round -/)
  (latexEnv := "lemma")]
lemma surviving_round_bound
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
    ∀ k : ℕ,
      delta * conversation.horizon ≤
        (round_subsequence conversation k).card →
      (k : ℝ) *
          (epsilon ^ 2 * delta -
            beta_error conversation humanError modelError
              humanWidth modelWidth) ≤ 1 := by
  classical
  have hTpos : (0 : ℝ) < conversation.horizon := by
    exact_mod_cast conversation.horizon_pos
  have hhumanWidthPos : 0 < humanWidth conversation.horizon := hhuman.2.1
  have hmodelWidthPos : 0 < modelWidth conversation.horizon := hmodel.2.1
  have hhumanRole0 : party_round true 0 := by
    left
    norm_num
  have hmodelRole1 : party_round false 1 := by
    right
    norm_num
  obtain ⟨humanCalibrated, hhumanRange, hhumanPerfect, hhumanClose⟩ :=
    bucketwise_calibrated_surrogate conversation true humanError humanWidth 0
      hhuman hhumanRole0
  obtain ⟨modelCalibrated, _, _, hmodelClose⟩ :=
    bucketwise_calibrated_surrogate conversation false modelError modelWidth 1
      hmodel hmodelRole1
  have hhumanRatioNonneg :
      0 ≤ humanError
          (humanWidth conversation.horizon * conversation.horizon) /
        humanWidth conversation.horizon :=
    (Finset.sum_nonneg fun t _ =>
      abs_nonneg (conversation.prediction 0 t - humanCalibrated t)).trans
        hhumanClose
  have hmodelRatioNonneg :
      0 ≤ modelError
          (modelWidth conversation.horizon * conversation.horizon) /
        modelWidth conversation.horizon :=
    (Finset.sum_nonneg fun t _ =>
      abs_nonneg (conversation.prediction 1 t - modelCalibrated t)).trans
        hmodelClose
  have hhumanErrorNonneg :
      0 ≤ humanError
        (humanWidth conversation.horizon * conversation.horizon) := by
    calc
      0 ≤ (humanError
              (humanWidth conversation.horizon * conversation.horizon) /
            humanWidth conversation.horizon) *
          humanWidth conversation.horizon :=
        mul_nonneg hhumanRatioNonneg hhumanWidthPos.le
      _ = _ := div_mul_cancel₀ _ (ne_of_gt hhumanWidthPos)
  have hmodelErrorNonneg :
      0 ≤ modelError
        (modelWidth conversation.horizon * conversation.horizon) := by
    calc
      0 ≤ (modelError
              (modelWidth conversation.horizon * conversation.horizon) /
            modelWidth conversation.horizon) *
          modelWidth conversation.horizon :=
        mul_nonneg hmodelRatioNonneg hmodelWidthPos.le
      _ = _ := div_mul_cancel₀ _ (ne_of_gt hmodelWidthPos)
  have hbetaNonneg :
      0 ≤ beta_error conversation humanError modelError
        humanWidth modelWidth := by
    unfold beta_error
    have hhumanScaledNonneg :
        0 ≤ humanError
            (humanWidth conversation.horizon * conversation.horizon) /
          (humanWidth conversation.horizon * conversation.horizon) :=
      div_nonneg hhumanErrorNonneg
        (mul_nonneg hhumanWidthPos.le hTpos.le)
    have hmodelScaledNonneg :
        0 ≤ modelError
            (modelWidth conversation.horizon * conversation.horizon) /
          (modelWidth conversation.horizon * conversation.horizon) :=
      div_nonneg hmodelErrorNonneg
        (mul_nonneg hmodelWidthPos.le hTpos.le)
    nlinarith [hhumanWidthPos.le, hmodelWidthPos.le]
  have hbetaScale :
      beta_error conversation humanError modelError humanWidth modelWidth *
          conversation.horizon =
        3 * (modelWidth conversation.horizon +
            humanWidth conversation.horizon) * conversation.horizon +
          3 * (modelError
              (modelWidth conversation.horizon * conversation.horizon) /
                modelWidth conversation.horizon +
            humanError
              (humanWidth conversation.horizon * conversation.horizon) /
                humanWidth conversation.horizon) := by
    unfold beta_error
    field_simp [ne_of_gt hTpos, ne_of_gt hhumanWidthPos,
      ne_of_gt hmodelWidthPos]
    <;> ring
  have hhumanPerfect' :
      perfectly_calibrated conversation Finset.univ humanCalibrated := by
    simpa [round_subsequence] using hhumanPerfect
  have hhumanRange' :
      ∀ t ∈ Finset.univ, humanCalibrated t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [round_subsequence] using hhumanRange
  have hhumanClose' :
      (∑ t ∈ Finset.univ,
          |conversation.prediction 0 t - humanCalibrated t|) ≤
        humanError
            (humanWidth conversation.horizon * conversation.horizon) /
          humanWidth conversation.horizon := by
    simpa [round_subsequence] using hhumanClose
  have hinitialPerfect :=
    perfect_calibrated_squared_error_quarter_bound conversation Finset.univ
      humanCalibrated hhumanPerfect'
  have hinitialPerturb := calibrated_squared_error_perturbation conversation
    Finset.univ humanCalibrated (conversation.prediction 0)
    (humanError
      (humanWidth conversation.horizon * conversation.horizon) /
        humanWidth conversation.horizon)
    hhumanRange' (fun t _ => conversation.prediction_mem 0 t)
    hhumanPerfect' hhumanClose'
  have hunivCard :
      (((Finset.univ : Finset (Fin conversation.horizon)).card : ℕ) : ℝ) =
        conversation.horizon := by
    simp
  rw [hunivCard] at hinitialPerfect
  have hinitialSharp :
      squared_error conversation Finset.univ (conversation.prediction 0) ≤
        (conversation.horizon : ℝ) / 4 +
          3 * (humanError
            (humanWidth conversation.horizon * conversation.horizon) /
              humanWidth conversation.horizon) := by
    nlinarith [hinitialPerfect, hinitialPerturb]
  have hinitialCrude :
      squared_error conversation Finset.univ (conversation.prediction 0) ≤
        conversation.horizon := by
    simpa using squared_error_at_most_cardinality conversation Finset.univ
      (conversation.prediction 0)
      (fun t _ => conversation.prediction_mem 0 t)
  have hinitialCombined :
      squared_error conversation Finset.univ (conversation.prediction 0) ≤
        min
          ((conversation.horizon : ℝ) / 4 +
            3 * (humanError
              (humanWidth conversation.horizon * conversation.horizon) /
                humanWidth conversation.horizon))
          conversation.horizon :=
    le_min hinitialSharp hinitialCrude
  have hinitial :
      squared_error conversation Finset.univ (conversation.prediction 0) ≤
        (conversation.horizon : ℝ) / 4 +
          3 * (humanError
            (humanWidth conversation.horizon * conversation.horizon) /
              humanWidth conversation.horizon) :=
    hinitialCombined.trans (min_le_left _ _)
  have hepsilonSq : epsilon ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hepsilon.2)
      (show 0 ≤ 1 + epsilon by linarith [hepsilon.1])]
  have hchargeAtMostOne : epsilon ^ 2 * delta ≤ 1 := by
    have := mul_le_mul hepsilonSq hdelta.2 hdelta.1 (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  let q := epsilon ^ 2 * delta -
    beta_error conversation humanError modelError humanWidth modelWidth
  let frozen (j : ℕ) (t : Fin conversation.horizon) : ℝ :=
    conversation.prediction (min j (conversation.length t)) t
  have hqAtMostOne : q ≤ 1 := by
    dsimp [q]
    nlinarith
  intro k hsurvive
  by_cases hk0 : k = 0
  · subst k
    simp
  by_cases hk1 : k = 1
  · subst k
    simpa [q] using hqAtMostOne
  have hk2 : 2 ≤ k := by omega
  have hsurviveEarlier (j : ℕ) (hj : j ≤ k) :
      delta * conversation.horizon ≤
        (round_subsequence conversation j).card := by
    have hsubset : round_subsequence conversation k ⊆
        round_subsequence conversation j := by
      intro t ht
      simp only [round_subsequence, Finset.mem_filter, Finset.mem_univ,
        true_and] at ht ⊢
      omega
    calc
      _ ≤ ((round_subsequence conversation k).card : ℝ) := hsurvive
      _ ≤ ((round_subsequence conversation j).card : ℕ) := by
        exact_mod_cast Finset.card_le_card hsubset
  have hstep (j : ℕ) (hj : 1 ≤ j) (hjk : j + 1 ≤ k) :
      squared_error conversation Finset.univ (frozen j) ≤
        squared_error conversation Finset.univ (frozen (j - 1)) -
          q * conversation.horizon := by
    have hroundSurvive := hsurviveEarlier (j + 1) hjk
    have hcharge :
        epsilon ^ 2 * (delta * conversation.horizon) ≤
          epsilon ^ 2 * (round_subsequence conversation (j + 1)).card :=
      mul_le_mul_of_nonneg_left hroundSurvive (sq_nonneg epsilon)
    by_cases hjeven : j % 2 = 0
    · have hrole : party_round true j := by
        left
        exact ⟨rfl, hjeven⟩
      have hraw := raw_round_error_decrease conversation true humanError
        humanWidth epsilon j hhuman hrole hrun hj
      change squared_error conversation Finset.univ (frozen j) ≤
          squared_error conversation Finset.univ (frozen (j - 1)) -
            epsilon ^ 2 * (round_subsequence conversation (j + 1)).card +
            humanWidth conversation.horizon * conversation.horizon +
            3 * (humanError
              (humanWidth conversation.horizon * conversation.horizon) /
                humanWidth conversation.horizon) at hraw
      dsimp [q]
      rw [sub_mul, hbetaScale]
      nlinarith [hmodelWidthPos.le, hhumanWidthPos.le,
        hhumanRatioNonneg, hmodelRatioNonneg]
    · have hjodd : j % 2 = 1 := by omega
      have hrole : party_round false j := by
        right
        exact ⟨rfl, hjodd⟩
      have hraw := raw_round_error_decrease conversation false modelError
        modelWidth epsilon j hmodel hrole hrun hj
      change squared_error conversation Finset.univ (frozen j) ≤
          squared_error conversation Finset.univ (frozen (j - 1)) -
            epsilon ^ 2 * (round_subsequence conversation (j + 1)).card +
            modelWidth conversation.horizon * conversation.horizon +
            3 * (modelError
              (modelWidth conversation.horizon * conversation.horizon) /
                modelWidth conversation.horizon) at hraw
      dsimp [q]
      rw [sub_mul, hbetaScale]
      nlinarith [hmodelWidthPos.le, hhumanWidthPos.le,
        hhumanRatioNonneg, hmodelRatioNonneg]
  have hfirst :
      squared_error conversation Finset.univ (frozen 1) ≤
        squared_error conversation Finset.univ (frozen 0) -
          q * conversation.horizon -
          3 * (humanError
            (humanWidth conversation.horizon * conversation.horizon) /
              humanWidth conversation.horizon) := by
    have hroundSurvive := hsurviveEarlier 2 hk2
    have hcharge :
        epsilon ^ 2 * (delta * conversation.horizon) ≤
          epsilon ^ 2 * (round_subsequence conversation 2).card :=
      mul_le_mul_of_nonneg_left hroundSurvive (sq_nonneg epsilon)
    have hraw := raw_round_error_decrease conversation false modelError
      modelWidth epsilon 1 hmodel hmodelRole1 hrun (by omega)
    change squared_error conversation Finset.univ (frozen 1) ≤
        squared_error conversation Finset.univ (frozen 0) -
          epsilon ^ 2 * (round_subsequence conversation 2).card +
          modelWidth conversation.horizon * conversation.horizon +
          3 * (modelError
            (modelWidth conversation.horizon * conversation.horizon) /
              modelWidth conversation.horizon) at hraw
    dsimp [q]
    rw [sub_mul, hbetaScale]
    nlinarith [hmodelWidthPos.le, hhumanWidthPos.le,
      hhumanRatioNonneg, hmodelRatioNonneg]
  have hfirstBound :
      squared_error conversation Finset.univ (frozen 1) ≤
        (conversation.horizon : ℝ) / 4 - q * conversation.horizon := by
    have hfrozen0 : frozen 0 = conversation.prediction 0 := by
      funext t
      simp [frozen]
    rw [hfrozen0] at hfirst
    nlinarith [hinitial]
  have hcumulative : ∀ m : ℕ, m ≤ k - 2 →
      squared_error conversation Finset.univ (frozen (m + 1)) ≤
        squared_error conversation Finset.univ (frozen 1) -
          (m : ℝ) * q * conversation.horizon := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
        have hmle : m ≤ k - 2 := by omega
        have hjk : m + 2 + 1 ≤ k := by omega
        have hnext := hstep (m + 2) (by omega) hjk
        have hprev := ih hmle
        calc
          squared_error conversation Finset.univ (frozen (m + 1 + 1)) ≤
              squared_error conversation Finset.univ (frozen (m + 2 - 1)) -
                q * conversation.horizon := by simpa [Nat.add_assoc] using hnext
          _ ≤ (squared_error conversation Finset.univ (frozen 1) -
                (m : ℝ) * q * conversation.horizon) -
                q * conversation.horizon := sub_le_sub_right hprev _
          _ = squared_error conversation Finset.univ (frozen 1) -
                ((m + 1 : ℕ) : ℝ) * q * conversation.horizon := by
            push_cast
            ring
  have hterminal := hcumulative (k - 2) (by omega)
  have hterminalNonneg := squared_error_nonnegative conversation Finset.univ
    (frozen (k - 2 + 1))
  have hquarter : ((k - 1 : ℕ) : ℝ) * q ≤ 1 / 4 := by
    have hkcalc : (k - 2 : ℕ) + 1 = k - 1 := by omega
    rw [hkcalc] at hterminal hterminalNonneg
    have hcombine :
        squared_error conversation Finset.univ (frozen (k - 1)) ≤
          (conversation.horizon : ℝ) / 4 -
            ((k - 1 : ℕ) : ℝ) * q * conversation.horizon := by
      calc
        _ ≤ squared_error conversation Finset.univ (frozen 1) -
              ((k - 2 : ℕ) : ℝ) * q * conversation.horizon := hterminal
        _ ≤ ((conversation.horizon : ℝ) / 4 - q * conversation.horizon) -
              ((k - 2 : ℕ) : ℝ) * q * conversation.horizon :=
            sub_le_sub_right hfirstBound _
        _ = _ := by
          push_cast
          have hkcastOne : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ k)]
            norm_num
          have hkcastTwo : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
            rw [Nat.cast_sub hk2]
            norm_num
          rw [hkcastOne, hkcastTwo]
          ring
    nlinarith [hterminalNonneg]
  by_cases hq : q ≤ 0
  · have hkNonneg : (0 : ℝ) ≤ k := by positivity
    have : (k : ℝ) * q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hkNonneg hq
    simpa [q] using this.trans (by norm_num : (0 : ℝ) ≤ 1)
  · have hqpos : 0 < q := lt_of_not_ge hq
    have hkcast : (k : ℝ) ≤ 2 * ((k - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show k ≤ 2 * (k - 1) by omega)
    have hmul := mul_le_mul_of_nonneg_right hkcast hqpos.le
    dsimp [q] at hquarter hmul ⊢
    nlinarith

@[blueprint "lem:agreement-fraction-from-round-bound"
  (statement := /-- Let \(C\) be a canonical conversation over \(T\) days, let \(f_h,f_m\colon\mathbb R\to\mathbb R\), let \(g_h,g_m\colon\mathbb N\to\mathbb R\), and let \(\epsilon,\delta\in[0,1]\). Assume that the Human is \((f_h,g_h)\)-conversation-calibrated, that the Model is \((f_m,g_m)\)-conversation-calibrated, and that \(C\) is an \(\epsilon\)-agreement run. Put \(q=\epsilon^2\delta-\beta(T)\), where \(\beta(T)\) is defined in \cref{def:beta-error}. If \(q>0\), then there exists \(K\in\mathbb R\) with \(K\leq q^{-1}\) such that at least \((1-\delta)T\) days have conversation length at most \(K\). -/)
  (proof := /-- Assume \(q>0\) and set \(K=q^{-1}\). If fewer than \((1-\delta)T\) days had conversation length at most \(K\), then more than \(\delta T\) days would have length strictly greater than \(K\). Let \(k=\lfloor K\rfloor+1\). Since conversation lengths are natural numbers, \cref{def:round-subsequence} shows that every such day belongs to \(T^{\geq k}\), so \(|T^{\geq k}|\geq\delta T\). By \cref{lem:surviving-round-bound}, one has \(kq\leq1\). On the other hand, \(k>K=q^{-1}\), and multiplication by the positive number \(q\) gives \(kq>1\), a contradiction. Hence at least \((1-\delta)T\) days have length at most \(K\). By \cref{def:agreement-by-round}, this is precisely agreement by round \(K\) on a \(1-\delta\) fraction of days, and \(K=q^{-1}\) gives the required bound. -/)
  (title := /-- From surviving rounds to a fraction of days -/)
  (latexEnv := "lemma")]
lemma agreement_fraction_from_round_bound
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
    0 < epsilon ^ 2 * delta -
        beta_error conversation humanError modelError
          humanWidth modelWidth →
      ∃ K : ℝ,
        K ≤ 1 / (epsilon ^ 2 * delta -
          beta_error conversation humanError modelError
            humanWidth modelWidth) ∧
        agreement_by_round conversation K delta := by
  classical
  intro hpositive
  let q :=
    epsilon ^ 2 * delta -
      beta_error conversation humanError modelError humanWidth modelWidth
  have hq : 0 < q := by
    simpa [q] using hpositive
  let K : ℝ := 1 / q
  refine ⟨K, ?_, ?_⟩
  · simp [K, q]
  · unfold agreement_by_round
    by_contra hagreement
    have hgood :
        (((Finset.univ.filter fun t : Fin conversation.horizon =>
          (conversation.length t : ℝ) ≤ K).card : ℕ) : ℝ) <
          (1 - delta) * conversation.horizon :=
      lt_of_not_ge hagreement
    let good : Finset (Fin conversation.horizon) :=
      Finset.univ.filter fun t =>
        (conversation.length t : ℝ) ≤ K
    let bad : Finset (Fin conversation.horizon) :=
      Finset.univ.filter fun t =>
        ¬(conversation.length t : ℝ) ≤ K
    have hgood' :
        (good.card : ℝ) < (1 - delta) * conversation.horizon := by
      simpa [good] using hgood
    have hpartitionNat :
        good.card + bad.card = conversation.horizon := by
      simpa [good, bad] using
        (Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin conversation.horizon)))
          (p := fun t => (conversation.length t : ℝ) ≤ K))
    have hpartition :
        (good.card : ℝ) + bad.card = conversation.horizon := by
      exact_mod_cast hpartitionNat
    have hbadLarge :
        delta * conversation.horizon < (bad.card : ℝ) := by
      nlinarith
    let k : ℕ := ⌊K⌋₊ + 1
    have hKnonneg : 0 ≤ K := (one_div_pos.mpr hq).le
    have hbadSubset :
        bad ⊆ round_subsequence conversation k := by
      intro t ht
      have ht' : K < (conversation.length t : ℝ) := by
        simpa [bad] using ht
      have hfloor : ⌊K⌋₊ < conversation.length t :=
        (Nat.floor_lt hKnonneg).2 ht'
      simpa [round_subsequence, k] using (Nat.succ_le_iff.mpr hfloor)
    have hcard :
        bad.card ≤ (round_subsequence conversation k).card :=
      Finset.card_le_card hbadSubset
    have hsurvives :
        delta * conversation.horizon ≤
          (round_subsequence conversation k).card := by
      exact le_trans (le_of_lt hbadLarge) (by exact_mod_cast hcard)
    have hround :=
      surviving_round_bound conversation humanError modelError
        humanWidth modelWidth epsilon delta hepsilon hdelta hhuman hmodel hrun
        k hsurvives
    have hKlt : K < (k : ℝ) := by
      simpa [k] using (Nat.lt_floor_add_one K)
    have hstrict := mul_lt_mul_of_pos_right hKlt hq
    have hKq : K * q = 1 := by
      simp [K, hq.ne']
    have hround' : (k : ℝ) * q ≤ 1 := by
      simpa [q] using hround
    nlinarith

@[blueprint "thm:canonical"
  (statement := /-- Let \(C\) be a canonical conversation over \(T\) days, let \(f_h,f_m\colon\mathbb R\to\mathbb R\), let \(g_h,g_m\colon\mathbb N\to\mathbb R\), and let \(\epsilon,\delta\in[0,1]\). Assume that the Human is \((f_h,g_h)\)-conversation-calibrated, that the Model is \((f_m,g_m)\)-conversation-calibrated, and that \(C\) is an \(\epsilon\)-agreement run. Put \(q=\epsilon^2\delta-\beta(T)\), with \(\beta(T)\) as in \cref{def:beta-error}. If \(q>0\), then there exists \(K\in\mathbb R\) with \(K\leq q^{-1}\) such that agreement is reached by round \(K\) on at least a \(1-\delta\) fraction of days. Furthermore, for every even Human round \(k\in\mathbb N\) with \(k\geq2\) satisfying \(|T^{\geq k+1}|\geq\delta T\),
  \[
  \frac{\operatorname{SQErr}(\bar p_h^k,y)}{T}
  \leq
  \min\left\{
  \frac{\operatorname{SQErr}(\bar p_m^1,y)}{T}-q,
  \frac{\operatorname{SQErr}(\bar p_h^2,y)}{T}
  \right\}-(k-2)q.
  \]
  Thus the recursive decrement is anchored at round \(2\): it vanishes at the Human round-\(2\) baseline, while the comparison with the Model round-\(1\) baseline includes the preceding one-round decrement. -/)
  (proof := /-- The conditional round bound on a \(1-\delta\) fraction of days is \cref{lem:agreement-fraction-from-round-bound}. For the accuracy assertion, fix an even Human round \(k\geq2\) and assume that at least \(\delta T\) days survive through round \(k+1\). Put \(q=\epsilon^2\delta-\beta(T)\). Applying \cref{lem:recursive-error-improvement} with these three hypotheses gives
  \[
  \frac{\operatorname{SQErr}(\bar p_h^k,y)}{T}
  \leq
  \min\left\{
  \frac{\operatorname{SQErr}(\bar p_m^1,y)}{T}-q,
  \frac{\operatorname{SQErr}(\bar p_h^2,y)}{T}
  \right\}-(k-2)q,
  \]
  which is the required accuracy bound. -/)
  (title := /-- Agreement in the canonical setting -/)
  (latexEnv := "theorem")]
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
        (round_subsequence conversation (k + 1)).card →
      squared_error conversation Finset.univ
          (human_bucketed_round_prediction conversation
            humanWidth k) /
          conversation.horizon ≤
        min
          (squared_error conversation Finset.univ
                (bucketed_round_prediction conversation
                  (modelWidth conversation.horizon) 1) /
              conversation.horizon -
            (epsilon ^ 2 * delta -
              beta_error conversation humanError modelError
                humanWidth modelWidth))
          (squared_error conversation Finset.univ
                (bucketed_round_prediction conversation
                  (humanWidth conversation.horizon) 2) /
              conversation.horizon) -
          ((k : ℝ) - 2) * (epsilon ^ 2 * delta -
            beta_error conversation humanError modelError
              humanWidth modelWidth) := by
  constructor
  · exact agreement_fraction_from_round_bound conversation humanError modelError
      humanWidth modelWidth epsilon delta hepsilon hdelta hhuman hmodel hrun
  · exact recursive_error_improvement conversation humanError modelError
      humanWidth modelWidth epsilon delta hepsilon hdelta hhuman hmodel hrun

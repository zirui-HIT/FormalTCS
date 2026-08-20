import Architect
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:strategic-label"
  (statement := /-- The binary label space is the two-element type
  $\mathcal Y=\{-1,+1\}$. -/)
  (title := /-- Binary labels -/)
  (latexEnv := "definition")]
inductive strategic_label where
  | negative
  | positive
  deriving DecidableEq

@[blueprint "def:classifier"
  (statement := /-- For a feature space $\mathcal X$, a classifier is a map
  $h\colon\mathcal X\to\mathcal Y$. -/)
  (title := /-- Classifiers -/)
  (latexEnv := "definition")]
abbrev classifier (X : Type*) := X → strategic_label

@[blueprint "def:closed-neighborhood"
  (statement := /-- Let $G$ be a directed manipulation graph on $\mathcal X$.
  The closed out-neighborhood of $x$ is
  $N_G[x]=\{z:z=x\text{ or }(x,z)\in E(G)\}$. -/)
  (title := /-- Closed manipulation neighborhood -/)
  (latexEnv := "definition")]
def closed_neighborhood {X : Type*} (G : Digraph X) (x : X) : Set X :=
  {z | z = x ∨ G.Adj x z}

@[blueprint "def:best-responses"
  (statement := /-- For a graph $G$, classifier $h$, and feature $x$, define
  $\operatorname{BR}_{G,h}(x)=\{z\in N_G[x]:h(z)=+1\}$. -/)
  (title := /-- Strategic best responses -/)
  (latexEnv := "definition")]
def best_responses {X : Type*} (G : Digraph X) (h : classifier X) (x : X) : Set X :=
  {z | z ∈ closed_neighborhood G x ∧ h z = strategic_label.positive}

@[blueprint "def:manipulation-rule"
  (statement := /-- A manipulation rule is a fixed deterministic tie-breaking
  rule.  It leaves $x$ unchanged when $h(x)=+1$ or when no positive point lies
  in $N_G[x]$; otherwise it chooses an element of
  $\operatorname{BR}_{G,h}(x)$. -/)
  (title := /-- Tie-broken manipulation -/)
  (latexEnv := "definition")]
structure manipulation_rule (X : Type*) where
  choose : Digraph X → classifier X → X → X
  self_of_positive :
    ∀ (G : Digraph X) (h : classifier X) (x : X),
      h x = strategic_label.positive → choose G h x = x
  self_of_no_best_response :
    ∀ (G : Digraph X) (h : classifier X) (x : X),
      best_responses G h x = ∅ → choose G h x = x
  best_response_of_available :
    ∀ (G : Digraph X) (h : classifier X) (x : X),
      h x ≠ strategic_label.positive →
      (best_responses G h x).Nonempty →
      choose G h x ∈ best_responses G h x

@[blueprint "def:all-positive-classifier"
  (statement := /-- The classifier $h^+$ assigns the positive label to every
  feature vector. -/)
  (title := /-- The all-positive classifier -/)
  (latexEnv := "definition")]
def all_positive_classifier (X : Type*) : classifier X :=
  fun _ => strategic_label.positive

@[blueprint "def:strategic-loss"
  (statement := /-- Given $G$, its fixed tie-breaking rule, a classifier $h$,
  and an example $(x,y)$, the strategic zero-one loss is
  $\ell_G^{\mathrm{str}}(h,(x,y))
  =\mathbf 1\{h(z_{G,h}(x))\ne y\}$. -/)
  (title := /-- Strategic zero-one loss -/)
  (latexEnv := "definition")]
def strategic_loss {X : Type*} (G : Digraph X) (rule : manipulation_rule X)
    (h : classifier X) (sample : X × strategic_label) : ℝ :=
  if h (rule.choose G h sample.1) = sample.2 then 0 else 1

@[blueprint "def:shifted-loss"
  (statement := /-- The shifted loss subtracts the loss of the all-positive
  classifier:
  $d_G(h,(x,y))=\ell_G^{\mathrm{str}}(h,(x,y))
  -\ell_G^{\mathrm{str}}(h^+,(x,y))$. -/)
  (title := /-- Shifted strategic loss -/)
  (latexEnv := "definition")]
def shifted_loss {X : Type*} (G : Digraph X) (rule : manipulation_rule X)
    (h : classifier X) (sample : X × strategic_label) : ℝ :=
  strategic_loss G rule h sample -
    strategic_loss G rule (all_positive_classifier X) sample

@[blueprint "def:observed-round"
  (statement := /-- A learner-observed round records the sampled action, the
  manipulated feature revealed to the learner, and the label. -/)
  (title := /-- Learner-visible round data -/)
  (latexEnv := "definition")]
structure observed_round (X : Type*) (ι : Type*) where
  action : Option ι
  manipulatedFeature : X
  label : strategic_label

@[blueprint "def:full-round"
  (statement := /-- A full round additionally records the agent's original
  feature, which is known to the adversary but need not be revealed to the
  learner. -/)
  (title := /-- Full interaction round -/)
  (latexEnv := "definition")]
structure full_round (X : Type*) (ι : Type*) where
  action : Option ι
  originalFeature : X
  manipulatedFeature : X
  label : strategic_label

@[blueprint "def:public-round"
  (statement := /-- The public record of a round contains the classifier
  revealed by the learner, the adversary's original feature, the manipulated
  feature, and the label, but not the learner's internal action index. -/)
  (title := /-- Adversary-visible round data -/)
  (latexEnv := "definition")]
structure public_round (X : Type*) where
  playedClassifier : classifier X
  originalFeature : X
  manipulatedFeature : X
  label : strategic_label

@[blueprint "def:observed-history"
  (statement := /-- The learner's view of a full transcript is obtained by
  forgetting every original feature while retaining sampled actions,
  manipulated features, and labels. -/)
  (title := /-- Learner observation map -/)
  (latexEnv := "definition")]
def observed_history {X : Type*} {ι : Type*}
    (history : List (full_round X ι)) : List (observed_round X ι) :=
  history.map fun round =>
    { action := round.action
      manipulatedFeature := round.manipulatedFeature
      label := round.label }

@[blueprint "def:action-classifier"
  (statement := /-- For a finite class $(h_i)_{i\in\iota}$, decode an action
  by sending $\bot$ to $h^+$ and $i$ to $h_i$. -/)
  (title := /-- Decoding improper actions -/)
  (latexEnv := "definition")]
def action_classifier {X : Type*} {ι : Type*} (H : ι → classifier X) :
    Option ι → classifier X
  | none => all_positive_classifier X
  | some i => H i

@[blueprint "def:public-history"
  (statement := /-- The adversary's view replaces each internal action index
  by the classifier that was publicly revealed on that round. -/)
  (title := /-- Adversary observation map -/)
  (latexEnv := "definition")]
def public_history {X : Type*} {ι : Type*} (H : ι → classifier X)
    (history : List (full_round X ι)) : List (public_round X) :=
  history.map fun round =>
    { playedClassifier := action_classifier H round.action
      originalFeature := round.originalFeature
      manipulatedFeature := round.manipulatedFeature
      label := round.label }

@[blueprint "def:improper-learner"
  (statement := /-- An improper randomized learner announces, for every
  horizon and observed history, a probability mass function on
  $\{\bot\}\cup\iota$.  The action $\bot$ denotes $h^+$, while $i\in\iota$
  denotes the class member $h_i$. -/)
  (title := /-- Improper randomized learner -/)
  (latexEnv := "definition")]
structure improper_learner (X : Type*) (ι : Type*) where
  play : ℕ → List (observed_round X ι) → PMF (Option ι)

@[blueprint "def:adaptive-adversary"
  (statement := /-- An adaptive adversary receives the horizon, the complete
  public past transcript, and the learner's currently announced distribution
  over classifiers before choosing the next agent $(x,y)$. -/)
  (title := /-- Adaptive adversary -/)
  (latexEnv := "definition")]
structure adaptive_adversary (X : Type*) (ι : Type*) where
  choose :
    ℕ → List (public_round X) → PMF (classifier X) → X × strategic_label

@[blueprint "def:extend-transcript"
  (statement := /-- Given a past transcript and sampled action, first expose
  the learner's announced distribution to the adaptive adversary, then let the
  adversary choose $(x,y)$, apply the fixed manipulation rule, and append the
  resulting full round. -/)
  (title := /-- One protocol transition -/)
  (latexEnv := "definition")]
noncomputable def extend_transcript {X : Type*} {ι : Type*}
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (learner : improper_learner X ι) (adversary : adaptive_adversary X ι)
    (horizon : ℕ) (history : List (full_round X ι)) (action : Option ι) :
    List (full_round X ι) :=
  let announcedActions := learner.play horizon (observed_history history)
  let announcedClassifiers := PMF.map (action_classifier H) announcedActions
  let sample :=
    adversary.choose horizon (public_history H history) announcedClassifiers
  let h := action_classifier H action
  let manipulated := rule.choose G h sample.1
  history ++
    [{ action := action
       originalFeature := sample.1
       manipulatedFeature := manipulated
       label := sample.2 }]

@[blueprint "def:interaction-law"
  (statement := /-- Recursively composing the learner's conditional PMFs
  yields the law of the complete transcript.  At every round the adversary's
  choice is made after the current PMF is announced and before the learner's
  action is sampled from it. -/)
  (title := /-- Law of the adaptive interaction -/)
  (latexEnv := "definition")]
noncomputable def interaction_law {X : Type*} {ι : Type*}
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (learner : improper_learner X ι) (adversary : adaptive_adversary X ι)
    (horizon : ℕ) : (rounds : ℕ) → PMF (List (full_round X ι))
  | 0 => PMF.pure []
  | rounds + 1 =>
      PMF.bind (interaction_law G rule H learner adversary horizon rounds)
        fun history =>
          let announced := learner.play horizon (observed_history history)
          PMF.map
            (fun action =>
              extend_transcript G rule H learner adversary horizon history action)
            announced

@[blueprint "def:transcript-consistent"
  (statement := /-- A full transcript is protocol-consistent when every
  recorded manipulated feature is exactly the response selected by the fixed
  manipulation rule for that round's sampled classifier and original
  feature. -/)
  (title := /-- Protocol-consistent transcripts -/)
  (latexEnv := "definition")]
def transcript_consistent {X : Type*} {ι : Type*}
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (history : List (full_round X ι)) : Prop :=
  ∀ round ∈ history,
    round.manipulatedFeature =
      rule.choose G (action_classifier H round.action) round.originalFeature

@[blueprint "def:learner-cumulative-loss"
  (statement := /-- The learner's cumulative loss on a transcript is the sum
  of the zero-one losses of the sampled classifiers at the manipulated
  features actually revealed in that transcript. -/)
  (title := /-- Learner cumulative loss -/)
  (latexEnv := "definition")]
def learner_cumulative_loss {X : Type*} {ι : Type*}
    (H : ι → classifier X) (history : List (full_round X ι)) : ℝ :=
  (history.map fun round =>
    if action_classifier H round.action round.manipulatedFeature = round.label
    then (0 : ℝ) else 1).sum

@[blueprint "def:comparator-cumulative-loss"
  (statement := /-- The cumulative loss of comparator $h_i$ recomputes, on
  every original example in the transcript, the manipulation that would have
  occurred had $h_i$ been deployed. -/)
  (title := /-- Comparator cumulative strategic loss -/)
  (latexEnv := "definition")]
def comparator_cumulative_loss {X : Type*} {ι : Type*}
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (history : List (full_round X ι)) (i : ι) : ℝ :=
  (history.map fun round =>
    strategic_loss G rule (H i) (round.originalFeature, round.label)).sum

@[blueprint "def:best-comparator-loss"
  (statement := /-- For a nonempty finite class, the best comparator loss is
  $\min_{i\in\iota}\sum_t\ell_G^{\mathrm{str}}(h_i,(x_t,y_t))$. -/)
  (title := /-- Best finite-class comparator -/)
  (latexEnv := "definition")]
noncomputable def best_comparator_loss {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (history : List (full_round X ι)) : ℝ :=
  (Finset.univ : Finset ι).inf' Finset.univ_nonempty
    (comparator_cumulative_loss G rule H history)

@[blueprint "def:transcript-regret"
  (statement := /-- The Stackelberg regret of a transcript is the learner's
  cumulative strategic loss minus the least cumulative strategic loss of a
  hypothesis in the finite comparison class. -/)
  (title := /-- Transcript Stackelberg regret -/)
  (latexEnv := "definition")]
noncomputable def transcript_regret {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (history : List (full_round X ι)) : ℝ :=
  learner_cumulative_loss H history -
    best_comparator_loss G rule H history

@[blueprint "def:shifted-learner-cumulative-loss"
  (statement := /-- The learner's shifted cumulative loss sums the shifted
  strategic losses of its sampled classifiers on the original examples. -/)
  (title := /-- Learner shifted cumulative loss -/)
  (latexEnv := "definition")]
def shifted_learner_cumulative_loss {X : Type*} {ι : Type*}
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (history : List (full_round X ι)) : ℝ :=
  (history.map fun round =>
    shifted_loss G rule (action_classifier H round.action)
      (round.originalFeature, round.label)).sum

@[blueprint "def:shifted-comparator-cumulative-loss"
  (statement := /-- For $i\in\iota$, its shifted cumulative loss is
  $\sum_t d_G(h_i,(x_t,y_t))$. -/)
  (title := /-- Comparator shifted cumulative loss -/)
  (latexEnv := "definition")]
def shifted_comparator_cumulative_loss {X : Type*} {ι : Type*}
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (history : List (full_round X ι)) (i : ι) : ℝ :=
  (history.map fun round =>
    shifted_loss G rule (H i) (round.originalFeature, round.label)).sum

@[blueprint "def:shifted-transcript-regret"
  (statement := /-- Shifted regret is the learner's shifted cumulative loss
  minus the minimum shifted cumulative loss among the comparison hypotheses. -/)
  (title := /-- Shifted transcript regret -/)
  (latexEnv := "definition")]
noncomputable def shifted_transcript_regret {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (history : List (full_round X ι)) : ℝ :=
  shifted_learner_cumulative_loss G rule H history -
    (Finset.univ : Finset ι).inf' Finset.univ_nonempty
      (shifted_comparator_cumulative_loss G rule H history)

@[blueprint "def:pmf-expectation"
  (statement := /-- For a discrete law $p$ and a real random variable $Z$,
  define $\mathbb E_p[Z]=\sum_\omega p(\omega)Z(\omega)$. -/)
  (title := /-- Expectation under a PMF -/)
  (latexEnv := "definition")]
noncomputable def pmf_expectation {Ω : Type*} (p : PMF Ω) (Z : Ω → ℝ) : ℝ :=
  ∑' ω, (p ω).toReal * Z ω

@[blueprint "def:expected-regret"
  (statement := /-- The expected Stackelberg regret at horizon $T$ is the
  expectation of transcript regret under the adaptive interaction law run for
  exactly $T$ rounds. -/)
  (title := /-- Expected Stackelberg regret -/)
  (latexEnv := "definition")]
noncomputable def expected_regret {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (learner : improper_learner X ι) (adversary : adaptive_adversary X ι)
    (T : ℕ) : ℝ :=
  pmf_expectation
    (interaction_law G rule H learner adversary T T)
    (transcript_regret G rule H)

@[blueprint "def:expected-shifted-regret"
  (statement := /-- Expected shifted regret is the expectation of shifted
  transcript regret under the same adaptive interaction law. -/)
  (title := /-- Expected shifted-loss regret -/)
  (latexEnv := "definition")]
noncomputable def expected_shifted_regret {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (learner : improper_learner X ι) (adversary : adaptive_adversary X ι)
    (T : ℕ) : ℝ :=
  pmf_expectation
    (interaction_law G rule H learner adversary T T)
    (shifted_transcript_regret G rule H)

@[blueprint "def:guarantees-expected-regret-rate"
  (statement := /-- For a nonempty finite hypothesis class indexed by
  $\iota$, a learner guarantees the uniform expected-regret rate established
  by Improper-Hedge if, for every horizon $T$ and every adaptive adversary,
  $\mathbb E[\mathfrak R_T]\le
  8\sqrt{T\log|\iota|}$.  In particular, the multiplicative constant is
  independent of the hypothesis class, manipulation graph, horizon, and
  adversary. -/)
  (title := /-- Uniform expected-regret rate -/)
  (latexEnv := "definition")]
def guarantees_expected_regret_rate {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (learner : improper_learner X ι) : Prop :=
  ∀ (T : ℕ) (adversary : adaptive_adversary X ι),
    expected_regret G rule H learner adversary T ≤
      8 * Real.sqrt ((T : ℝ) * Real.log (Fintype.card ι : ℝ))

@[blueprint "def:source-parameter-regime"
  (statement := /-- For a finite index type $\iota$ and a horizon
  $T\in\mathbb N$, the source parameters are in their regular regime when
  $T>0$, $|\iota|>1$, and $\log |\iota|\le T$.  These conditions are
  precisely those under which the source learning rate is positive and its
  exploration rate is a probability. -/)
  (title := /-- Regular regime for the source parameters -/)
  (latexEnv := "definition")]
def source_parameter_regime {ι : Type*} [Fintype ι] (T : ℕ) : Prop :=
  0 < T ∧
    1 < Fintype.card ι ∧
      Real.log (Fintype.card ι : ℝ) ≤ (T : ℝ)

@[blueprint "def:improper-hedge-observation-reveals-original"
  (statement := /-- An observed round reveals the agent's original feature
  when the learner played $h^+$, or when it played $h_i$ and the revealed
  feature is labeled negative by $h_i$.  In the latter case no positive best
  response was taken, so the revealed feature is the original one. -/)
  (title := /-- Rounds revealing the original feature -/)
  (latexEnv := "definition")]
def improper_hedge_observation_reveals_original {X : Type*} {ι : Type*}
    (H : ι → classifier X) (round : observed_round X ι) : Prop :=
  match round.action with
  | none => True
  | some i => H i round.manipulatedFeature = strategic_label.negative

@[blueprint "def:improper-hedge-observed-outcome"
  (statement := /-- Given an action and an original labeled example, the
  corresponding learner observation records that action, its tie-broken
  manipulated feature, and the label. -/)
  (title := /-- One-round observation under a fixed action -/)
  (latexEnv := "definition")]
def improper_hedge_observed_outcome {X : Type*} {ι : Type*}
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (action : Option ι) (sample : X × strategic_label) : observed_round X ι :=
  { action := action
    manipulatedFeature :=
      rule.choose G (action_classifier H action) sample.1
    label := sample.2 }

@[blueprint "def:improper-hedge-update"
  (statement := /-- Fix a finite nonempty comparison class $(h_i)_{i\in\iota}$.
  An Improper-Hedge update consists of learning and exploration rates
  $\eta_T,\rho_T$, the set $R(x)$ of experts having no positive best response
  at $x$, exponential weights $w_t(i)$, their normalized law $p_t$, the
  exploration mixture on $\{\bot\}\cup\iota$, and an observable estimator
  $\widehat d_t(i)$.  Initially $w_1(i)=1$ and
  $w_{t+1}(i)=w_t(i)e^{-\eta_T\widehat d_t(i)}$.  The action law assigns mass
  $\rho_T$ to $h^+$ and mass $(1-\rho_T)p_t(i)$ to $h_i$.  At a regular-regime
  horizon, if the observation reveals $x_t$ and $i\in R(x_t)$, the estimator is
  $(a_t+\eta_T)^{-1}$ for a positive label and
  $-(a_t-\eta_T)^{-1}$ for a negative label, where
  $a_t=\rho_T+(1-\rho_T)p_t(R(x_t))$; it is zero otherwise. -/)
  (title := /-- Concrete Improper-Hedge update and estimator -/)
  (latexEnv := "definition")]
structure improper_hedge_update {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X) where
  eta : ℕ → ℝ
  rho : ℕ → ℝ
  negativeExperts : X → Finset ι
  negative_experts_spec :
    ∀ x i, i ∈ negativeExperts x ↔ best_responses G (H i) x = ∅
  weights : ℕ → List (observed_round X ι) → ι → ℝ
  expertDistribution : ℕ → List (observed_round X ι) → PMF ι
  actionDistribution : ℕ → List (observed_round X ι) → PMF (Option ι)
  observationProbability : ℕ → List (observed_round X ι) → X → ℝ
  estimator :
    ℕ → List (observed_round X ι) → observed_round X ι → ι → ℝ
  eta_formula :
    ∀ T, source_parameter_regime (ι := ι) T →
      eta T =
        (1 / 2 : ℝ) *
          Real.sqrt (Real.log (Fintype.card ι : ℝ) / (T : ℝ))
  rho_formula :
    ∀ T, source_parameter_regime (ι := ι) T →
      rho T = Real.sqrt (Real.log (Fintype.card ι : ℝ) / (T : ℝ))
  eta_positive : ∀ T, 0 < eta T
  rho_nonnegative : ∀ T, 0 ≤ rho T
  rho_at_most_one : ∀ T, rho T ≤ 1
  weight_initial : ∀ T i, weights T [] i = 1
  weight_positive : ∀ T history i, 0 < weights T history i
  weight_update :
    ∀ T history round i,
      weights T (history ++ [round]) i =
        weights T history i * Real.exp (-eta T * estimator T history round i)
  expert_distribution_formula :
    ∀ T history i,
      (expertDistribution T history i).toReal =
        weights T history i / ∑ j, weights T history j
  exploration_probability :
    ∀ T history,
      (actionDistribution T history none).toReal = rho T
  expert_action_probability :
    ∀ T history i,
      (actionDistribution T history (some i)).toReal =
        (1 - rho T) * (expertDistribution T history i).toReal
  observation_probability_formula :
    ∀ T history x,
      observationProbability T history x =
        rho T + (1 - rho T) *
          ∑ i ∈ negativeExperts x,
            (expertDistribution T history i).toReal
  estimator_positive :
    ∀ T history round i,
      source_parameter_regime (ι := ι) T →
      improper_hedge_observation_reveals_original H round →
      round.label = strategic_label.positive →
      i ∈ negativeExperts round.manipulatedFeature →
      estimator T history round i =
        1 / (observationProbability T history round.manipulatedFeature + eta T)
  estimator_negative :
    ∀ T history round i,
      source_parameter_regime (ι := ι) T →
      improper_hedge_observation_reveals_original H round →
      round.label = strategic_label.negative →
      i ∈ negativeExperts round.manipulatedFeature →
      estimator T history round i =
        -1 / (observationProbability T history round.manipulatedFeature - eta T)
  estimator_zero :
    ∀ T history round i,
      (¬ improper_hedge_observation_reveals_original H round ∨
        i ∉ negativeExperts round.manipulatedFeature) →
      estimator T history round i = 0

@[blueprint "def:improper-hedge-learner"
  (statement := /-- The learner induced by an Improper-Hedge update announces
  the update's action law at the given horizon and observed history. -/)
  (title := /-- Learner induced by the Improper-Hedge update -/)
  (latexEnv := "definition")]
def improper_hedge_learner {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {G : Digraph X} {rule : manipulation_rule X} {H : ι → classifier X}
    (update : improper_hedge_update G rule H) : improper_learner X ι :=
  { play := update.actionDistribution }

@[blueprint "def:improper-hedge-estimated-cumulative-loss-from"
  (statement := /-- Starting from a learner-visible past $s$, sum the
  concrete estimates along a future observed history, updating the past after
  every round. -/)
  (title := /-- Estimated cumulative loss from a visible past -/)
  (latexEnv := "definition")]
def improper_hedge_estimated_cumulative_loss_from {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {G : Digraph X} {rule : manipulation_rule X} {H : ι → classifier X}
    (update : improper_hedge_update G rule H) (T : ℕ) :
    List (observed_round X ι) → List (observed_round X ι) → ι → ℝ
  | _, [], _ => 0
  | past, round :: future, i =>
      update.estimator T past round i +
        improper_hedge_estimated_cumulative_loss_from update T
          (past ++ [round]) future i

@[blueprint "def:improper-hedge-estimated-cumulative-loss"
  (statement := /-- The estimated cumulative loss of expert $i$ is the sum
  of its sequential estimates from the empty history. -/)
  (title := /-- Estimated expert loss -/)
  (latexEnv := "definition")]
def improper_hedge_estimated_cumulative_loss {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {G : Digraph X} {rule : manipulation_rule X} {H : ι → classifier X}
    (update : improper_hedge_update G rule H) (T : ℕ)
    (history : List (observed_round X ι)) (i : ι) : ℝ :=
  improper_hedge_estimated_cumulative_loss_from update T [] history i

@[blueprint "def:improper-hedge-estimated-bar-loss-from"
  (statement := /-- Starting from a visible past, sum
  $\langle p_t,\widehat d_t\rangle$ along a future observed history. -/)
  (title := /-- Estimated mixture loss from a visible past -/)
  (latexEnv := "definition")]
def improper_hedge_estimated_bar_loss_from {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {G : Digraph X} {rule : manipulation_rule X} {H : ι → classifier X}
    (update : improper_hedge_update G rule H) (T : ℕ) :
    List (observed_round X ι) → List (observed_round X ι) → ℝ
  | _, [] => 0
  | past, round :: future =>
      (∑ i, (update.expertDistribution T past i).toReal *
        update.estimator T past round i) +
      improper_hedge_estimated_bar_loss_from update T
        (past ++ [round]) future

@[blueprint "def:improper-hedge-estimated-bar-loss"
  (statement := /-- The estimated mixture loss is
  $\widehat{\bar L}_T=\sum_t\langle p_t,\widehat d_t\rangle$. -/)
  (title := /-- Estimated cumulative mixture loss -/)
  (latexEnv := "definition")]
def improper_hedge_estimated_bar_loss {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {G : Digraph X} {rule : manipulation_rule X} {H : ι → classifier X}
    (update : improper_hedge_update G rule H) (T : ℕ)
    (history : List (observed_round X ι)) : ℝ :=
  improper_hedge_estimated_bar_loss_from update T [] history

@[blueprint "def:improper-hedge-estimated-square-mass-from"
  (statement := /-- Starting from a visible past, sum the conditional
  quadratic quantities $\langle p_t,\widehat d_t^2\rangle$ along the future
  observations. -/)
  (title := /-- Cumulative estimated second moment from a visible past -/)
  (latexEnv := "definition")]
def improper_hedge_estimated_square_mass_from {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {G : Digraph X} {rule : manipulation_rule X} {H : ι → classifier X}
    (update : improper_hedge_update G rule H) (T : ℕ) :
    List (observed_round X ι) → List (observed_round X ι) → ℝ
  | _, [] => 0
  | past, round :: future =>
      (∑ i, (update.expertDistribution T past i).toReal *
        (update.estimator T past round i) ^ 2) +
      improper_hedge_estimated_square_mass_from update T
        (past ++ [round]) future

@[blueprint "def:improper-hedge-estimated-square-mass"
  (statement := /-- The cumulative estimated second moment is
  $\sum_t\langle p_t,\widehat d_t^2\rangle$. -/)
  (title := /-- Cumulative estimated second moment -/)
  (latexEnv := "definition")]
def improper_hedge_estimated_square_mass {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {G : Digraph X} {rule : manipulation_rule X} {H : ι → classifier X}
    (update : improper_hedge_update G rule H) (T : ℕ)
    (history : List (observed_round X ι)) : ℝ :=
  improper_hedge_estimated_square_mass_from update T [] history

@[blueprint "def:improper-hedge-bar-cumulative-loss-from"
  (statement := /-- Starting from a visible past, sum the true conditional
  mixture losses $\langle p_t,d_t\rangle$ along a full future transcript,
  extending the visible past after each round. -/)
  (title := /-- True mixture loss from a visible past -/)
  (latexEnv := "definition")]
def improper_hedge_bar_cumulative_loss_from {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {G : Digraph X} {rule : manipulation_rule X} {H : ι → classifier X}
    (update : improper_hedge_update G rule H) (T : ℕ) :
    List (observed_round X ι) → List (full_round X ι) → ℝ
  | _, [] => 0
  | past, round :: future =>
      (∑ i, (update.expertDistribution T past i).toReal *
        shifted_loss G rule (H i) (round.originalFeature, round.label)) +
      improper_hedge_bar_cumulative_loss_from update T
        (past ++
          [{ action := round.action
             manipulatedFeature := round.manipulatedFeature
             label := round.label }]) future

@[blueprint "def:improper-hedge-bar-cumulative-loss"
  (statement := /-- On a full transcript, the true cumulative mixture loss is
  $\bar L_T=\sum_t\langle p_t,d_t\rangle$, with each $p_t$ computed from the
  learner-visible prefix. -/)
  (title := /-- True cumulative mixture loss -/)
  (latexEnv := "definition")]
def improper_hedge_bar_cumulative_loss {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {G : Digraph X} {rule : manipulation_rule X} {H : ι → classifier X}
    (update : improper_hedge_update G rule H) (T : ℕ)
    (history : List (full_round X ι)) : ℝ :=
  improper_hedge_bar_cumulative_loss_from update T [] history

@[blueprint "def:improper-hedge-main-path-term"
  (statement := /-- The pathwise main term is the true cumulative mixture loss
  minus the least true shifted cumulative loss among the experts. -/)
  (title := /-- Pathwise main shifted-loss term -/)
  (latexEnv := "definition")]
noncomputable def improper_hedge_main_path_term {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {G : Digraph X} {rule : manipulation_rule X} {H : ι → classifier X}
    (update : improper_hedge_update G rule H) (T : ℕ)
    (history : List (full_round X ι)) : ℝ :=
  improper_hedge_bar_cumulative_loss update T history -
    (Finset.univ : Finset ι).inf' Finset.univ_nonempty
      (shifted_comparator_cumulative_loss G rule H history)

@[blueprint "def:improper-hedge-hedge-path-term"
  (statement := /-- The pathwise Hedge term is the estimated mixture loss
  minus the least estimated expert loss. -/)
  (title := /-- Pathwise Hedge term -/)
  (latexEnv := "definition")]
noncomputable def improper_hedge_hedge_path_term {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {G : Digraph X} {rule : manipulation_rule X} {H : ι → classifier X}
    (update : improper_hedge_update G rule H) (T : ℕ)
    (history : List (full_round X ι)) : ℝ :=
  improper_hedge_estimated_bar_loss update T (observed_history history) -
    (Finset.univ : Finset ι).inf' Finset.univ_nonempty
      (improper_hedge_estimated_cumulative_loss update T
        (observed_history history))

@[blueprint "def:improper-hedge-bias-path-term"
  (statement := /-- The pathwise bias term is the true mixture loss minus its
  estimated counterpart. -/)
  (title := /-- Pathwise estimator-bias term -/)
  (latexEnv := "definition")]
def improper_hedge_bias_path_term {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {G : Digraph X} {rule : manipulation_rule X} {H : ι → classifier X}
    (update : improper_hedge_update G rule H) (T : ℕ)
    (history : List (full_round X ι)) : ℝ :=
  improper_hedge_bar_cumulative_loss update T history -
    improper_hedge_estimated_bar_loss update T (observed_history history)

@[blueprint "def:improper-hedge-deviation-path-term"
  (statement := /-- The pathwise deviation term is the least estimated expert
  loss minus the least true shifted expert loss.  With the preceding Hedge and
  bias terms, this gives an exact decomposition of the main term. -/)
  (title := /-- Pathwise estimator-deviation term -/)
  (latexEnv := "definition")]
noncomputable def improper_hedge_deviation_path_term {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {G : Digraph X} {rule : manipulation_rule X} {H : ι → classifier X}
    (update : improper_hedge_update G rule H) (T : ℕ)
    (history : List (full_round X ι)) : ℝ :=
  (Finset.univ : Finset ι).inf' Finset.univ_nonempty
      (improper_hedge_estimated_cumulative_loss update T
        (observed_history history)) -
    (Finset.univ : Finset ι).inf' Finset.univ_nonempty
      (shifted_comparator_cumulative_loss G rule H history)

@[blueprint "def:improper-hedge-analysis"
  (statement := /-- An Improper-Hedge analysis package records the cumulative
  quantities used by the source proof and a learner valid at every horizon.
  In the regular parameter regime of
  \cref{def:source-parameter-regime}, it records the source formulae for
  $\eta$ and $\rho$ and the Hedge, bias, and deviation estimates.  At every
  horizon, $\eta$ is positive, $\rho$ is a probability, the exploration
  identity and the bound $|\bar L_T|\le T$ hold, and shifted regret is at
  most $T$.  If the comparison class is a singleton, shifted regret is
  nonpositive. -/)
  (title := /-- Interface to the preceding Improper-Hedge analysis -/)
  (latexEnv := "definition")]
structure improper_hedge_analysis {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (learner : improper_learner X ι) where
  update : improper_hedge_update G rule H
  eta : ℕ → ℝ
  rho : ℕ → ℝ
  barLoss : ℕ → adaptive_adversary X ι → ℝ
  mainTerm : ℕ → adaptive_adversary X ι → ℝ
  hedgeTerm : ℕ → adaptive_adversary X ι → ℝ
  biasTerm : ℕ → adaptive_adversary X ι → ℝ
  deviationTerm : ℕ → adaptive_adversary X ι → ℝ
  learner_eq : learner = improper_hedge_learner update
  eta_eq_update : eta = update.eta
  rho_eq_update : rho = update.rho
  bar_loss_formula :
    ∀ T adversary,
      barLoss T adversary =
        pmf_expectation
          (interaction_law G rule H learner adversary T T)
          (improper_hedge_bar_cumulative_loss update T)
  main_term_formula :
    ∀ T adversary,
      mainTerm T adversary =
        pmf_expectation
          (interaction_law G rule H learner adversary T T)
          (improper_hedge_main_path_term update T)
  hedge_term_formula :
    ∀ T adversary,
      hedgeTerm T adversary =
        pmf_expectation
          (interaction_law G rule H learner adversary T T)
          (improper_hedge_hedge_path_term update T)
  bias_term_formula :
    ∀ T adversary,
      biasTerm T adversary =
        pmf_expectation
          (interaction_law G rule H learner adversary T T)
          (improper_hedge_bias_path_term update T)
  deviation_term_formula :
    ∀ T adversary,
      deviationTerm T adversary =
        pmf_expectation
          (interaction_law G rule H learner adversary T T)
          (improper_hedge_deviation_path_term update T)
  eta_formula :
    ∀ T, source_parameter_regime (ι := ι) T →
      eta T =
        (1 / 2 : ℝ) *
          Real.sqrt (Real.log (Fintype.card ι : ℝ) / (T : ℝ))
  rho_formula :
    ∀ T, source_parameter_regime (ι := ι) T →
      rho T =
        Real.sqrt (Real.log (Fintype.card ι : ℝ) / (T : ℝ))
  eta_positive : ∀ T, 0 < eta T
  rho_nonnegative : ∀ T, 0 ≤ rho T
  rho_at_most_one : ∀ T, rho T ≤ 1
  exploration_identity :
    ∀ T adversary,
      expected_shifted_regret G rule H learner adversary T =
        mainTerm T adversary - rho T * barLoss T adversary
  bar_loss_abs_bound :
    ∀ T adversary, |barLoss T adversary| ≤ (T : ℝ)
  main_decomposition :
    ∀ T adversary,
      mainTerm T adversary =
        hedgeTerm T adversary + biasTerm T adversary +
          deviationTerm T adversary
  hedge_term_bound :
    ∀ T adversary,
      source_parameter_regime (ι := ι) T →
        hedgeTerm T adversary ≤
          Real.log (Fintype.card ι : ℝ) / eta T +
            4 * eta T * (T : ℝ)
  bias_term_bound :
    ∀ T adversary,
      source_parameter_regime (ι := ι) T →
        biasTerm T adversary ≤ 2 * eta T * (T : ℝ)
  deviation_term_bound :
    ∀ T adversary,
      source_parameter_regime (ι := ι) T →
        deviationTerm T adversary ≤
          Real.log (Fintype.card ι : ℝ) / eta T
  fallback_regret_bound :
    ∀ T adversary,
      expected_shifted_regret G rule H learner adversary T ≤ (T : ℝ)
  singleton_regret_bound :
    Fintype.card ι = 1 →
      ∀ T adversary,
        expected_shifted_regret G rule H learner adversary T ≤ 0

@[blueprint "lem:all-positive-shifted-loss-zero"
  (statement := /-- For every feature space $\mathcal X$, manipulation graph
  $G$ on $\mathcal X$, tie-breaking manipulation rule, and labeled example
  $(x,y)\in\mathcal X\times\mathcal Y$, the shifted loss of the all-positive
  classifier $h^+$ is zero. -/)
  (proof := /-- By \cref{def:shifted-loss}, the two terms are both the
  strategic loss of the all-positive classifier from
  \cref{def:all-positive-classifier}; their difference is therefore zero. -/)
  (title := /-- The exploration action has zero shifted loss -/)
  (latexEnv := "lemma")]
lemma all_positive_shifted_loss_zero {X : Type*}
    (G : Digraph X) (rule : manipulation_rule X)
    (sample : X × strategic_label) :
    shifted_loss G rule (all_positive_classifier X) sample = 0 := by
  simp only [shifted_loss, sub_self]

@[blueprint "lem:shifted-loss-abs-le-one"
  (statement := /-- For every feature space $\mathcal X$, manipulation graph
  $G$ on $\mathcal X$, fixed tie-breaking manipulation rule, classifier $h$,
  and labeled example $(x,y)$, the shifted loss satisfies
  $|d_G(h,(x,y))|\le 1$. -/)
  (proof := /-- Each strategic loss in \cref{def:strategic-loss} belongs to
  $\{0,1\}$.  Their difference, which is the shifted loss by
  \cref{def:shifted-loss}, consequently belongs to $\{-1,0,1\}$ and has
  absolute value at most one. -/)
  (title := /-- Uniform bound on shifted loss -/)
  (latexEnv := "lemma")]
lemma shifted_loss_abs_le_one {X : Type*}
    (G : Digraph X) (rule : manipulation_rule X)
    (h : classifier X) (sample : X × strategic_label) :
    |shifted_loss G rule h sample| ≤ 1 := by
  unfold shifted_loss strategic_loss
  split_ifs <;> norm_num

@[blueprint "lem:shifted-regret-eq-strategic-regret"
  (statement := /-- Let $\mathcal X$ be a feature space, let $\iota$ be a
  nonempty finite index type, let $G$ be a manipulation graph on $\mathcal X$
  with manipulation rule, and let $(h_i)_{i\in\iota}$ be a family of
  classifiers.  For every full transcript that is protocol-consistent with
  these data, its shifted transcript regret equals its strategic transcript
  regret. -/)
  (proof := /-- Let
  $B=\sum_t\ell_G^{\mathrm{str}}(h^+,(x_t,y_t))$.  Induction on the transcript,
  using \cref{def:shifted-learner-cumulative-loss,
  def:learner-cumulative-loss, def:shifted-loss, def:strategic-loss} and the
  roundwise equality in \cref{def:transcript-consistent}, proves that the
  learner's shifted cumulative loss is its recorded cumulative loss minus
  $B$.  A second induction, now using
  \cref{def:shifted-comparator-cumulative-loss,
  def:comparator-cumulative-loss, def:shifted-loss}, proves for every
  $i\in\iota$ that the shifted cumulative loss of $h_i$ is its strategic
  cumulative loss minus $B$.  The two order inequalities characterizing the
  infimum over the nonempty finite set $\iota$ therefore show that the least
  shifted comparator loss is the least strategic comparator loss minus $B$.
  Expanding \cref{def:shifted-transcript-regret, def:transcript-regret,
  def:best-comparator-loss} and cancelling $B$ gives the claimed equality. -/)
  (title := /-- Shift invariance of transcript regret -/)
  (latexEnv := "lemma")]
lemma shifted_regret_eq_strategic_regret {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (history : List (full_round X ι))
    (hconsistent : transcript_consistent G rule H history) :
    shifted_transcript_regret G rule H history =
      transcript_regret G rule H history := by
  let baseline : ℝ :=
    (history.map fun round =>
      strategic_loss G rule (all_positive_classifier X)
        (round.originalFeature, round.label)).sum
  have hlearner :
      shifted_learner_cumulative_loss G rule H history =
        learner_cumulative_loss H history - baseline := by
    dsimp only [baseline]
    induction history with
    | nil =>
        simp [shifted_learner_cumulative_loss, learner_cumulative_loss]
    | cons round history ih =>
        simp only [transcript_consistent, List.forall_mem_cons] at hconsistent
        change
          shifted_loss G rule (action_classifier H round.action)
                (round.originalFeature, round.label) +
              shifted_learner_cumulative_loss G rule H history =
            (if action_classifier H round.action round.manipulatedFeature =
                round.label then 0 else 1) +
              learner_cumulative_loss H history -
                (strategic_loss G rule (all_positive_classifier X)
                    (round.originalFeature, round.label) +
                  (history.map fun r =>
                    strategic_loss G rule (all_positive_classifier X)
                      (r.originalFeature, r.label)).sum)
        rw [ih hconsistent.2]
        unfold shifted_loss strategic_loss
        rw [← hconsistent.1]
        ring
  have hcomparator (i : ι) :
      shifted_comparator_cumulative_loss G rule H history i =
        comparator_cumulative_loss G rule H history i - baseline := by
    dsimp only [baseline]
    clear hconsistent hlearner baseline
    induction history with
    | nil =>
        simp [shifted_comparator_cumulative_loss, comparator_cumulative_loss]
    | cons round history ih =>
        change
          shifted_loss G rule (H i) (round.originalFeature, round.label) +
              shifted_comparator_cumulative_loss G rule H history i =
            strategic_loss G rule (H i) (round.originalFeature, round.label) +
              comparator_cumulative_loss G rule H history i -
                (strategic_loss G rule (all_positive_classifier X)
                    (round.originalFeature, round.label) +
                  (history.map fun r =>
                    strategic_loss G rule (all_positive_classifier X)
                      (r.originalFeature, r.label)).sum)
        rw [ih]
        unfold shifted_loss
        ring
  have hminimum :
      (Finset.univ : Finset ι).inf' Finset.univ_nonempty
          (shifted_comparator_cumulative_loss G rule H history) =
        (Finset.univ : Finset ι).inf' Finset.univ_nonempty
            (comparator_cumulative_loss G rule H history) - baseline := by
    apply le_antisymm
    · have hbound :
          (Finset.univ : Finset ι).inf' Finset.univ_nonempty
                (shifted_comparator_cumulative_loss G rule H history) + baseline ≤
            (Finset.univ : Finset ι).inf' Finset.univ_nonempty
              (comparator_cumulative_loss G rule H history) := by
          apply Finset.le_inf'
          intro i hi
          have hshifted := Finset.inf'_le
            (f := shifted_comparator_cumulative_loss G rule H history) hi
          rw [hcomparator i] at hshifted
          linarith
      linarith
    · apply Finset.le_inf'
      intro i hi
      rw [hcomparator i]
      have horiginal := Finset.inf'_le
        (f := comparator_cumulative_loss G rule H history) hi
      linarith
  unfold shifted_transcript_regret transcript_regret best_comparator_loss
  rw [hlearner, hminimum]
  ring

@[blueprint "lem:interaction-law-consistent"
  (statement := /-- Let $G$ be a manipulation graph on a feature type
  $\mathcal X$, let a fixed manipulation rule be given, let $H$ be a family
  of classifiers indexed by an arbitrary type, and fix an improper learner,
  an adaptive adversary, a horizon, and a number of rounds.  Every full-round
  history having nonzero mass under the resulting interaction law is
  protocol-consistent. -/)
  (proof := /-- Induct on the number of rounds in
  \cref{def:interaction-law}.  At zero rounds, nonzero mass under the pure law
  forces the history to be empty, which is protocol-consistent.  At a
  successor, the bind and map defining the interaction law show that a
  positive-mass history is \cref{def:extend-transcript} applied to a
  positive-mass predecessor and some sampled action.  The induction hypothesis
  proves consistency for every round in the predecessor.  The only remaining
  round is the appended singleton, whose manipulated feature is, by
  \cref{def:extend-transcript}, exactly the fixed rule's response to its
  sampled classifier and original feature. -/)
  (title := /-- Support of the interaction law -/)
  (latexEnv := "lemma")]
lemma interaction_law_consistent {X : Type*} {ι : Type*}
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (learner : improper_learner X ι) (adversary : adaptive_adversary X ι)
    (horizon rounds : ℕ) :
    ∀ history : List (full_round X ι),
      interaction_law G rule H learner adversary horizon rounds history ≠ 0 →
        transcript_consistent G rule H history := by
  intro history hmass
  induction rounds generalizing history with
  | zero =>
    have hnil : history = [] := by
      simpa [interaction_law] using hmass
    subst history
    simp [transcript_consistent]
  | succ rounds ih =>
    simp [interaction_law, extend_transcript] at hmass
    rcases hmass with ⟨prior, hprior, action, rfl, haction⟩
    intro round hround
    simp only [List.mem_append, List.mem_singleton] at hround
    rcases hround with hround | rfl
    · exact ih prior hprior round hround
    · rfl

@[blueprint "lem:expected-shifted-regret-eq-expected-regret"
  (statement := /-- Let $\mathcal X$ be a feature space, let $\iota$ be a
  nonempty finite index type, let $G$ be a manipulation graph on $\mathcal X$
  with a fixed manipulation rule, and let $(h_i)_{i\in\iota}$ be an arbitrary
  indexed family of classifiers.  For every improper learner, every adaptive
  adversary, and every horizon $T\in\mathbb N$, expected shifted-loss regret
  equals expected strategic regret. -/)
  (proof := /-- Expand \cref{def:expected-shifted-regret,
  def:expected-regret, def:pmf-expectation} and compare the two sums term by
  term.  Fix a full-round history.  If its mass under
  \cref{def:interaction-law} is zero, then both corresponding summands vanish.
  Otherwise, \cref{lem:interaction-law-consistent} makes the history
  protocol-consistent, so \cref{lem:shifted-regret-eq-strategic-regret}
  identifies its shifted transcript regret with its strategic transcript
  regret.  Multiplication by the common mass therefore gives equality of the
  two summands, and hence of the two sums. -/)
  (title := /-- Shift invariance in expectation -/)
  (latexEnv := "lemma")]
lemma expected_shifted_regret_eq_expected_regret {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (learner : improper_learner X ι) (adversary : adaptive_adversary X ι)
    (T : ℕ) :
    expected_shifted_regret G rule H learner adversary T =
      expected_regret G rule H learner adversary T := by
  unfold expected_shifted_regret expected_regret pmf_expectation
  apply tsum_congr
  intro history
  by_cases hmass :
      interaction_law G rule H learner adversary T T history = 0
  · simp [hmass]
  · rw [shifted_regret_eq_strategic_regret G rule H history
      (interaction_law_consistent G rule H learner adversary T T history hmass)]

@[blueprint "lem:source-parameter-validity"
  (statement := /-- Let $\iota$ be a nonempty finite type and let
  $T\in\mathbb N$ satisfy $T>0$, $|\iota|>1$, and
  $\log |\iota|\le T$.  Then the source parameter choices
  $\eta=\frac12\sqrt{\log |\iota|/T}$ and
  $\rho=\sqrt{\log |\iota|/T}$ satisfy $\eta>0$ and $0\le\rho\le1$. -/)
  (proof := /-- By \cref{def:source-parameter-regime}, $T>0$ and
  $|\iota|>1$.  Hence $\log |\iota|>0$, so
  $\log |\iota|/T>0$ and therefore $\eta>0$ and $\rho\ge0$.  The remaining
  regime inequality $\log |\iota|\le T$, divided by the positive number
  $T$, gives $\log |\iota|/T\le1$.  Monotonicity of the nonnegative square
  root yields $\rho\le1$. -/)
  (title := /-- Validity of the source parameters in the regular regime -/)
  (latexEnv := "lemma")]
lemma source_parameter_validity {ι : Type*} [Fintype ι] [Nonempty ι]
    (T : ℕ) (hT : source_parameter_regime (ι := ι) T) :
    0 <
        (1 / 2 : ℝ) *
          Real.sqrt (Real.log (Fintype.card ι : ℝ) / (T : ℝ)) ∧
    0 ≤ Real.sqrt (Real.log (Fintype.card ι : ℝ) / (T : ℝ)) ∧
    Real.sqrt (Real.log (Fintype.card ι : ℝ) / (T : ℝ)) ≤ 1 := by
  rcases hT with ⟨hTpos, hcard, hlog⟩
  have hTreal : (0 : ℝ) < (T : ℝ) := by
    exact_mod_cast hTpos
  have hcardreal : (1 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast hcard
  have hlogpos : 0 < Real.log (Fintype.card ι : ℝ) :=
    Real.log_pos hcardreal
  have hratio : 0 < Real.log (Fintype.card ι : ℝ) / (T : ℝ) :=
    div_pos hlogpos hTreal
  have hrle : Real.log (Fintype.card ι : ℝ) / (T : ℝ) ≤ 1 :=
    (div_le_one hTreal).2 hlog
  constructor
  · exact mul_pos (by norm_num) (Real.sqrt_pos_of_pos hratio)
  · constructor
    · exact Real.sqrt_nonneg _
    · simpa using Real.sqrt_le_sqrt hrle

@[blueprint "lem:improper-hedge-update-exists"
  (statement := /-- Let $\mathcal X$ be a type and let $\iota$ be a nonempty
  finite type.  For every manipulation graph $G$ on $\mathcal X$, every
  manipulation rule on $\mathcal X$, and every $\iota$-indexed family of
  classifiers on $\mathcal X$, there exists an Improper-Hedge update in the
  sense of \cref{def:improper-hedge-update}. -/)
  (proof := /-- In the regular regime, take
  $\eta_T=\frac12\sqrt{\log|\iota|/T}$ and
  $\rho_T=\sqrt{\log|\iota|/T}$; their admissibility is
  \cref{lem:source-parameter-validity}.  Outside that regime take
  $\eta_T=1$ and $\rho_T=0$.  For each feature $x$, let $R(x)$ consist
  exactly of the indices whose positive best-response set is empty.  Starting
  from unit weights, recursively normalize the positive weights to obtain
  $p_t$, form the mixture assigning mass $\rho_T$ to $h^+$ and mass
  $(1-\rho_T)p_t(i)$ to $h_i$, define $a_t$ by the displayed formula in
  \cref{def:improper-hedge-update}, and use its two signed denominators on
  precisely the rounds revealing the original feature.  Positivity of the
  exponential weights makes every normalization well-defined, and the
  mixture masses sum to one. -/)
  (title := /-- Existence of the concrete Improper-Hedge update -/)
  (latexEnv := "lemma")]
lemma improper_hedge_update_exists {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X) :
    Nonempty (improper_hedge_update G rule H) := by
  classical
  let etaFn : ℕ → ℝ := fun T =>
    if source_parameter_regime (ι := ι) T then
      (1 / 2 : ℝ) *
        Real.sqrt (Real.log (Fintype.card ι : ℝ) / (T : ℝ))
    else 1
  let rhoFn : ℕ → ℝ := fun T =>
    if source_parameter_regime (ι := ι) T then
      Real.sqrt (Real.log (Fintype.card ι : ℝ) / (T : ℝ))
    else 0
  have etaFn_formula (T : ℕ) (hT : source_parameter_regime (ι := ι) T) :
      etaFn T =
        (1 / 2 : ℝ) *
          Real.sqrt (Real.log (Fintype.card ι : ℝ) / (T : ℝ)) := by
    simp [etaFn, hT]
  have rhoFn_formula (T : ℕ) (hT : source_parameter_regime (ι := ι) T) :
      rhoFn T = Real.sqrt (Real.log (Fintype.card ι : ℝ) / (T : ℝ)) := by
    simp [rhoFn, hT]
  have etaFn_positive (T : ℕ) : 0 < etaFn T := by
    by_cases hT : source_parameter_regime (ι := ι) T
    · simpa [etaFn, hT] using (source_parameter_validity T hT).1
    · simp [etaFn, hT]
  have rhoFn_nonnegative (T : ℕ) : 0 ≤ rhoFn T := by
    by_cases hT : source_parameter_regime (ι := ι) T
    · simpa [rhoFn, hT] using (source_parameter_validity T hT).2.1
    · simp [rhoFn, hT]
  have rhoFn_at_most_one (T : ℕ) : rhoFn T ≤ 1 := by
    by_cases hT : source_parameter_regime (ι := ι) T
    · simpa [rhoFn, hT] using (source_parameter_validity T hT).2.2
    · simp [rhoFn, hT]
  let negativeExpertsFn : X → Finset ι := fun x =>
    Finset.univ.filter fun i => best_responses G (H i) x = ∅
  have negativeExpertsFn_spec (x : X) (i : ι) :
      i ∈ negativeExpertsFn x ↔ best_responses G (H i) x = ∅ := by
    simp [negativeExpertsFn]
  let WeightState := { w : ι → ℝ // ∀ i, 0 < w i }
  let initialState : WeightState :=
    ⟨fun _ => 1, fun _ => by norm_num⟩
  let expertPMF : WeightState → PMF ι := fun state =>
    PMF.ofFintype
      (fun i =>
        ENNReal.ofReal
          (state.1 i / ∑ j, state.1 j))
      (by
        have hsum : 0 < ∑ j, state.1 j :=
          Finset.sum_pos (fun j _ => state.2 j) Finset.univ_nonempty
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · change ENNReal.ofReal
            (∑ i ∈ Finset.univ, state.1 i / ∑ j, state.1 j) = 1
          rw [← Finset.sum_div, div_self hsum.ne']
          norm_num
        · intro i hi
          exact div_nonneg (state.2 i).le hsum.le)
  have expertPMF_formula (state : WeightState) (i : ι) :
      (expertPMF state i).toReal = state.1 i / ∑ j, state.1 j := by
    have hsum : 0 < ∑ j, state.1 j :=
      Finset.sum_pos (fun j _ => state.2 j) Finset.univ_nonempty
    simp [expertPMF, div_nonneg (state.2 i).le hsum.le]
  let observationFn (T : ℕ) (state : WeightState) (x : X) : ℝ :=
    rhoFn T + (1 - rhoFn T) *
      ∑ i ∈ negativeExpertsFn x, (expertPMF state i).toReal
  let estimatorFn (T : ℕ) (state : WeightState)
      (round : observed_round X ι) (i : ι) : ℝ :=
    if improper_hedge_observation_reveals_original H round ∧
        i ∈ negativeExpertsFn round.manipulatedFeature then
      match round.label with
      | strategic_label.positive =>
          1 / (observationFn T state round.manipulatedFeature + etaFn T)
      | strategic_label.negative =>
          -1 / (observationFn T state round.manipulatedFeature - etaFn T)
    else 0
  let stepState (T : ℕ) (state : WeightState)
      (round : observed_round X ι) : WeightState :=
    ⟨fun i =>
        state.1 i * Real.exp (-etaFn T * estimatorFn T state round i),
      fun i => mul_pos (state.2 i) (Real.exp_pos _)⟩
  let stateAt (T : ℕ) (history : List (observed_round X ι)) : WeightState :=
    history.foldl (stepState T) initialState
  let weightsFn (T : ℕ) (history : List (observed_round X ι)) (i : ι) : ℝ :=
    (stateAt T history).1 i
  let expertDistributionFn (T : ℕ) (history : List (observed_round X ι)) : PMF ι :=
    expertPMF (stateAt T history)
  let actionPMF (T : ℕ) (state : WeightState) : PMF (Option ι) :=
    PMF.ofFintype
      (fun action =>
        match action with
        | none => ENNReal.ofReal (rhoFn T)
        | some i =>
            ENNReal.ofReal (1 - rhoFn T) * expertPMF state i)
      (by
        have hsum : 0 < ∑ j, state.1 j :=
          Finset.sum_pos (fun j _ => state.2 j) Finset.univ_nonempty
        have hexpert : ∑ i, expertPMF state i = 1 := by
          simp only [expertPMF, PMF.ofFintype_apply]
          rw [← ENNReal.ofReal_sum_of_nonneg]
          · change ENNReal.ofReal
              (∑ i ∈ Finset.univ, state.1 i / ∑ j, state.1 j) = 1
            rw [← Finset.sum_div, div_self hsum.ne']
            norm_num
          · intro i hi
            exact div_nonneg (state.2 i).le hsum.le
        rw [Fintype.sum_option]
        rw [← Finset.mul_sum]
        rw [hexpert, mul_one]
        rw [← ENNReal.ofReal_add (rhoFn_nonnegative T)
          (sub_nonneg.mpr (rhoFn_at_most_one T))]
        norm_num)
  have actionPMF_none (T : ℕ) (state : WeightState) :
      (actionPMF T state none).toReal = rhoFn T := by
    simp [actionPMF, rhoFn_nonnegative T]
  have actionPMF_some (T : ℕ) (state : WeightState) (i : ι) :
      (actionPMF T state (some i)).toReal =
        (1 - rhoFn T) * (expertPMF state i).toReal := by
    simp [actionPMF, sub_nonneg.mpr (rhoFn_at_most_one T)]
  let actionDistributionFn (T : ℕ) (history : List (observed_round X ι)) :
      PMF (Option ι) := actionPMF T (stateAt T history)
  refine ⟨{
    eta := etaFn
    rho := rhoFn
    negativeExperts := negativeExpertsFn
    weights := weightsFn
    expertDistribution := expertDistributionFn
    actionDistribution := actionDistributionFn
    observationProbability := fun T history x => observationFn T (stateAt T history) x
    estimator := fun T history round i => estimatorFn T (stateAt T history) round i
    eta_formula := etaFn_formula
    rho_formula := rhoFn_formula
    eta_positive := etaFn_positive
    rho_nonnegative := rhoFn_nonnegative
    rho_at_most_one := rhoFn_at_most_one
    negative_experts_spec := negativeExpertsFn_spec
    weight_initial := by
      intro T i
      simp [weightsFn, stateAt, initialState]
    weight_positive := by
      intro T history i
      exact (stateAt T history).2 i
    weight_update := by
      intro T history round i
      simp [weightsFn, stateAt, stepState, List.foldl_append]
    expert_distribution_formula := by
      intro T history i
      exact expertPMF_formula (stateAt T history) i
    exploration_probability := by
      intro T history
      exact actionPMF_none T (stateAt T history)
    expert_action_probability := by
      intro T history i
      exact actionPMF_some T (stateAt T history) i
    observation_probability_formula := by
      intro T history x
      rfl
    estimator_positive := by
      intro T history round i hT hreveal hlabel hi
      simp [estimatorFn, hreveal, hi, hlabel]
    estimator_negative := by
      intro T history round i hT hreveal hlabel hi
      simp [estimatorFn, hreveal, hi, hlabel]
    estimator_zero := by
      intro T history round i hzero
      simp only [estimatorFn]
      split
      · rename_i hboth
        exact False.elim (hzero.elim (fun h => h hboth.1) (fun h => h hboth.2))
      · rfl
  }⟩

@[blueprint "lem:improper-hedge-estimator-scaled-abs-le-one"
  (statement := /-- Let $\mathcal X$ and $\iota$ be types, with $\iota$
  finite and nonempty, and fix an Improper-Hedge update.  At every horizon in
  the regular parameter regime, every estimator coordinate satisfies
  $|\eta_T\widehat d_t(i)|\le 1$. -/)
  (proof := /-- The observation probability is at least the exploration
  probability because it is the latter plus a nonnegative weighted mass, by
  \cref{def:improper-hedge-update}.  In the regular regime the parameter
  formulas give $\rho_T=2\eta_T$, with $\eta_T>0$.  Thus both signed estimator
  denominators are at least $\eta_T$.  The defining positive and negative
  estimator formulas then give the claimed absolute bound; the remaining
  coordinates vanish by the zero-estimator formula. -/)
  (title := /-- Uniform scaled estimator bound -/)
  (latexEnv := "lemma")]
lemma improper_hedge_estimator_scaled_abs_le_one {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {G : Digraph X} {rule : manipulation_rule X} {H : ι → classifier X}
    (update : improper_hedge_update G rule H) (T : ℕ)
    (hT : source_parameter_regime (ι := ι) T)
    (past : List (observed_round X ι)) (round : observed_round X ι) (i : ι) :
    |update.eta T * update.estimator T past round i| ≤ 1 := by
  have heta : 0 < update.eta T := update.eta_positive T
  have hrho : update.rho T = 2 * update.eta T := by
    rw [update.rho_formula T hT, update.eta_formula T hT]
    ring
  have hsum : 0 ≤ ∑ k ∈ update.negativeExperts round.manipulatedFeature,
      (update.expertDistribution T past k).toReal := by
    exact Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hobs : 0 ≤ update.observationProbability T past round.manipulatedFeature := by
    rw [update.observation_probability_formula]
    have hone : 0 ≤ 1 - update.rho T := sub_nonneg.mpr (update.rho_at_most_one T)
    have hprod : 0 ≤ (1 - update.rho T) *
        ∑ k ∈ update.negativeExperts round.manipulatedFeature,
          (update.expertDistribution T past k).toReal := mul_nonneg hone hsum
    linarith [update.rho_nonnegative T]
  by_cases hreveal : improper_hedge_observation_reveals_original H round
  · by_cases hi : i ∈ update.negativeExperts round.manipulatedFeature
    · cases hlabel : round.label with
      | negative =>
          rw [update.estimator_negative T past round i hT hreveal hlabel hi]
          have hmass : update.rho T ≤
              update.observationProbability T past round.manipulatedFeature := by
            rw [update.observation_probability_formula]
            have hone : 0 ≤ 1 - update.rho T :=
              sub_nonneg.mpr (update.rho_at_most_one T)
            nlinarith
          have hdenom : 0 <
              update.observationProbability T past round.manipulatedFeature -
                update.eta T := by
            rw [hrho] at hmass
            linarith
          rw [abs_mul, abs_of_pos heta, abs_div, abs_neg, abs_one,
            abs_of_pos hdenom]
          simpa [div_eq_mul_inv] using
            (div_le_one hdenom).2 (by rw [hrho] at hmass; linarith)
      | positive =>
          rw [update.estimator_positive T past round i hT hreveal hlabel hi]
          have hdenom : 0 <
              update.observationProbability T past round.manipulatedFeature +
                update.eta T := by linarith
          rw [abs_mul, abs_of_pos heta, abs_div, abs_one, abs_of_pos hdenom]
          simpa [div_eq_mul_inv] using
            (div_le_one hdenom).2 (by linarith)
    · rw [update.estimator_zero T past round i (Or.inr hi)]
      simp
  · rw [update.estimator_zero T past round i (Or.inl hreveal)]
    simp

@[blueprint "lem:improper-hedge-estimator-exp-bound"
  (statement := /-- Under the hypotheses of
  \cref{lem:improper-hedge-estimator-scaled-abs-le-one}, every estimator
  coordinate satisfies
  $\exp(-\eta_T\widehat d_t(i))\le
  1-\eta_T\widehat d_t(i)+\eta_T^2\widehat d_t(i)^2$. -/)
  (proof := /-- By
  \cref{lem:improper-hedge-estimator-scaled-abs-le-one}, the absolute value of
  the exponent is at most one.  The order-two Taylor remainder estimate for
  the real exponential function then bounds the exponential by
  $1+x+x^2$ at $x=-\eta_T\widehat d_t(i)$, which is the stated inequality
  after expansion. -/)
  (title := /-- Quadratic exponential bound for the estimator -/)
  (latexEnv := "lemma")]
lemma improper_hedge_estimator_exp_bound {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {G : Digraph X} {rule : manipulation_rule X} {H : ι → classifier X}
    (update : improper_hedge_update G rule H) (T : ℕ)
    (hT : source_parameter_regime (ι := ι) T)
    (past : List (observed_round X ι)) (round : observed_round X ι) (i : ι) :
    Real.exp (-update.eta T * update.estimator T past round i) ≤
      1 - update.eta T * update.estimator T past round i +
        update.eta T ^ 2 * update.estimator T past round i ^ 2 := by
  have habs : |-update.eta T * update.estimator T past round i| ≤ 1 := by
    simpa [abs_neg] using
      improper_hedge_estimator_scaled_abs_le_one update T hT past round i
  have hbound := Real.exp_bound habs (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ] at hbound
  have hupper := (abs_le.mp hbound).2
  have hsq : (|update.eta T| * |update.estimator T past round i|) ^ 2 =
      update.eta T ^ 2 * update.estimator T past round i ^ 2 := by
    rw [mul_pow, sq_abs, sq_abs]
  rw [hsq] at hupper
  have hnonneg : 0 ≤ update.eta T ^ 2 *
      update.estimator T past round i ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [← neg_mul] at hupper
  calc
    Real.exp (-update.eta T * update.estimator T past round i) ≤
        1 + (-update.eta T * update.estimator T past round i) +
          update.eta T ^ 2 * update.estimator T past round i ^ 2 * (3 / 4) := by
      linarith
    _ ≤ 1 - update.eta T * update.estimator T past round i +
        update.eta T ^ 2 * update.estimator T past round i ^ 2 := by
      nlinarith

@[blueprint "lem:improper-hedge-weight-sum-step-bound"
  (statement := /-- Fix an Improper-Hedge update and a regular-regime
  horizon.  After one observed round, the total expert weight is at most its
  preceding value multiplied by
  $\exp(-\eta_T\langle p_t,\widehat d_t\rangle+
  \eta_T^2\langle p_t,\widehat d_t^2\rangle)$. -/)
  (proof := /-- Substitute the weight update from
  \cref{def:improper-hedge-update} and apply
  \cref{lem:improper-hedge-estimator-exp-bound} coordinatewise.  All weights
  are positive, so summation preserves the inequality.  The formula defining
  the expert distribution converts the two weighted raw-weight sums into the
  corresponding expectations under $p_t$.  Finally,
  $1+x\le\exp(x)$ bounds the resulting quadratic factor. -/)
  (title := /-- One-round total-weight bound -/)
  (latexEnv := "lemma")]
lemma improper_hedge_weight_sum_step_bound {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {G : Digraph X} {rule : manipulation_rule X} {H : ι → classifier X}
    (update : improper_hedge_update G rule H) (T : ℕ)
    (hT : source_parameter_regime (ι := ι) T)
    (past : List (observed_round X ι)) (round : observed_round X ι) :
    (∑ i, update.weights T (past ++ [round]) i) ≤
      (∑ i, update.weights T past i) *
        Real.exp
          (-update.eta T *
              ∑ i, (update.expertDistribution T past i).toReal *
                update.estimator T past round i +
            update.eta T ^ 2 *
              ∑ i, (update.expertDistribution T past i).toReal *
                update.estimator T past round i ^ 2) := by
  let W : ℝ := ∑ i, update.weights T past i
  obtain ⟨j : ι⟩ := ‹Nonempty ι›
  have hWpos : 0 < W := by
    have hle : update.weights T past j ≤ W := by
      exact Finset.single_le_sum
        (fun i _ => (update.weight_positive T past i).le) (Finset.mem_univ j)
    linarith [update.weight_positive T past j]
  have hWne : W ≠ 0 := ne_of_gt hWpos
  have hbar :
      (∑ i, (update.expertDistribution T past i).toReal *
        update.estimator T past round i) =
        (∑ i, update.weights T past i * update.estimator T past round i) / W := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [update.expert_distribution_formula]
    change update.weights T past i / W * update.estimator T past round i = _
    ring
  have hsquare :
      (∑ i, (update.expertDistribution T past i).toReal *
        update.estimator T past round i ^ 2) =
        (∑ i, update.weights T past i *
          update.estimator T past round i ^ 2) / W := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [update.expert_distribution_formula]
    change update.weights T past i / W *
      update.estimator T past round i ^ 2 = _
    ring
  calc
    (∑ i, update.weights T (past ++ [round]) i) =
        ∑ i, update.weights T past i *
          Real.exp (-update.eta T * update.estimator T past round i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [update.weight_update]
    _ ≤ ∑ i, update.weights T past i *
        (1 - update.eta T * update.estimator T past round i +
          update.eta T ^ 2 * update.estimator T past round i ^ 2) := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left
          (improper_hedge_estimator_exp_bound update T hT past round i)
          (update.weight_positive T past i).le
    _ = W *
        (1 - update.eta T *
            ∑ i, (update.expertDistribution T past i).toReal *
              update.estimator T past round i +
          update.eta T ^ 2 *
            ∑ i, (update.expertDistribution T past i).toReal *
              update.estimator T past round i ^ 2) := by
      rw [hbar, hsquare]
      field_simp [hWne]
      simp_rw [mul_add, mul_sub, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
      dsimp [W]
      rw [Finset.mul_sum, Finset.mul_sum]
      simp only [mul_one]
      apply congrArg₂ (· + ·)
      · apply congrArg₂ (· - ·) rfl
        apply Finset.sum_congr rfl
        intro i _
        ring
      · apply Finset.sum_congr rfl
        intro i _
        ring
    _ ≤ W * Real.exp
        (-update.eta T *
            ∑ i, (update.expertDistribution T past i).toReal *
              update.estimator T past round i +
          update.eta T ^ 2 *
            ∑ i, (update.expertDistribution T past i).toReal *
              update.estimator T past round i ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hWpos.le
      have hexp := Real.add_one_le_exp
        (-update.eta T *
            ∑ i, (update.expertDistribution T past i).toReal *
              update.estimator T past round i +
          update.eta T ^ 2 *
            ∑ i, (update.expertDistribution T past i).toReal *
              update.estimator T past round i ^ 2)
      linarith

@[blueprint "lem:improper-hedge-weight-sum-future-bound"
  (statement := /-- Fix an Improper-Hedge update and a regular-regime
  horizon.  From every visible past $s$ and along every future observed
  history $u$, the final total weight is at most the total weight at $s$
  multiplied by
  $\exp(-\eta_T\widehat{\bar L}(u;s)+
  \eta_T^2\widehat V(u;s))$. -/)
  (proof := /-- Induct on the future history.  The empty history gives
  equality.  For a nonempty history, apply
  \cref{lem:improper-hedge-weight-sum-step-bound} to its first round and the
  induction hypothesis from the extended visible past.  Positivity of the
  exponential preserves the first-round inequality under multiplication,
  and the identity $\exp(x)\exp(y)=\exp(x+y)$ combines the two factors.  The
  recursive cumulative definitions identify the sum of the two exponents
  with the exponent stated here. -/)
  (title := /-- Total-weight bound along a future history -/)
  (latexEnv := "lemma")]
lemma improper_hedge_weight_sum_future_bound {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {G : Digraph X} {rule : manipulation_rule X} {H : ι → classifier X}
    (update : improper_hedge_update G rule H) (T : ℕ)
    (hT : source_parameter_regime (ι := ι) T)
    (past future : List (observed_round X ι)) :
    (∑ i, update.weights T (past ++ future) i) ≤
      (∑ i, update.weights T past i) *
        Real.exp
          (-update.eta T *
              improper_hedge_estimated_bar_loss_from update T past future +
            update.eta T ^ 2 *
              improper_hedge_estimated_square_mass_from update T past future) := by
  induction future generalizing past with
  | nil => simp [improper_hedge_estimated_bar_loss_from,
      improper_hedge_estimated_square_mass_from]
  | cons round future ih =>
      let stepBar : ℝ := ∑ i, (update.expertDistribution T past i).toReal *
        update.estimator T past round i
      let stepSquare : ℝ :=
        ∑ i, (update.expertDistribution T past i).toReal *
          update.estimator T past round i ^ 2
      let tailBar : ℝ := improper_hedge_estimated_bar_loss_from update T
        (past ++ [round]) future
      let tailSquare : ℝ := improper_hedge_estimated_square_mass_from update T
        (past ++ [round]) future
      calc
        (∑ i, update.weights T (past ++ round :: future) i) =
            ∑ i, update.weights T ((past ++ [round]) ++ future) i := by
          congr 2
          simp
        _ ≤ (∑ i, update.weights T (past ++ [round]) i) *
            Real.exp (-update.eta T * tailBar +
              update.eta T ^ 2 * tailSquare) := by
          exact ih (past ++ [round])
        _ ≤ ((∑ i, update.weights T past i) *
              Real.exp (-update.eta T * stepBar +
                update.eta T ^ 2 * stepSquare)) *
            Real.exp (-update.eta T * tailBar +
              update.eta T ^ 2 * tailSquare) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          exact improper_hedge_weight_sum_step_bound update T hT past round
        _ = (∑ i, update.weights T past i) *
            Real.exp
              (-update.eta T *
                  improper_hedge_estimated_bar_loss_from update T past
                    (round :: future) +
                update.eta T ^ 2 *
                  improper_hedge_estimated_square_mass_from update T past
                    (round :: future)) := by
          rw [mul_assoc, ← Real.exp_add]
          simp only [improper_hedge_estimated_bar_loss_from,
            improper_hedge_estimated_square_mass_from]
          dsimp [stepBar, stepSquare, tailBar, tailSquare]
          congr 1
          ring_nf

@[blueprint "lem:improper-hedge-individual-weight-future"
  (statement := /-- Fix an Improper-Hedge update.  From every visible past
  $s$, along every future observed history $u$, and for every expert $j$, its
  final weight equals its weight at $s$ multiplied by
  $\exp(-\eta_T\widehat L(j;u,s))$. -/)
  (proof := /-- Induct on the future history.  The empty case is immediate.
  In the nonempty case, the weight-update identity in
  \cref{def:improper-hedge-update} supplies the factor for the first round,
  while the induction hypothesis supplies the remaining factor from the
  extended visible past.  The exponential addition identity combines them,
  and the recursive definition of estimated cumulative loss gives the stated
  exponent. -/)
  (title := /-- Individual weight along a future history -/)
  (latexEnv := "lemma")]
lemma improper_hedge_individual_weight_future {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {G : Digraph X} {rule : manipulation_rule X} {H : ι → classifier X}
    (update : improper_hedge_update G rule H) (T : ℕ)
    (past future : List (observed_round X ι)) (j : ι) :
    update.weights T (past ++ future) j =
      update.weights T past j *
        Real.exp (-update.eta T *
          improper_hedge_estimated_cumulative_loss_from update T past future j) := by
  induction future generalizing past with
  | nil => simp [improper_hedge_estimated_cumulative_loss_from]
  | cons round future ih =>
      calc
        update.weights T (past ++ round :: future) j =
            update.weights T ((past ++ [round]) ++ future) j := by
          congr 1
          simp
        _ = update.weights T (past ++ [round]) j *
            Real.exp (-update.eta T *
              improper_hedge_estimated_cumulative_loss_from update T
                (past ++ [round]) future j) := ih (past ++ [round])
        _ = update.weights T past j *
            Real.exp (-update.eta T *
              improper_hedge_estimated_cumulative_loss_from update T past
                (round :: future) j) := by
          rw [update.weight_update, mul_assoc, ← Real.exp_add]
          simp only [improper_hedge_estimated_cumulative_loss_from]
          congr 1
          ring_nf

@[blueprint "lem:improper-hedge-potential"
  (statement := /-- Let $\mathcal X$ and $\iota$ be types, with $\iota$
  finite and nonempty.  Fix a manipulation graph on $\mathcal X$, a
  manipulation rule, an $\iota$-indexed family of classifiers, and an
  Improper-Hedge update for these data.  For every $T\in\mathbb N$ such that
  $T>0$, $|\iota|>1$, and $\log|\iota|\le T$, every finite observed history
  $s$, and every $j\in\iota$, the estimated mixture loss satisfies

  \[
    \widehat{\bar L}(s)-\widehat L(j;s)
    \le \frac{\log|\iota|}{\eta_T}
       +\eta_T\sum_t\langle p_t,\widehat d_t^2\rangle .
  \] -/)
  (proof := /-- By \cref{lem:improper-hedge-individual-weight-future}, the
  final weight of $j$ is
  $\exp(-\eta_T\widehat L(j;s))$, since its initial weight is one.  By
  \cref{lem:improper-hedge-weight-sum-future-bound}, the final total weight is
  at most
  $|\iota|\exp(-\eta_T\widehat{\bar L}(s)+\eta_T^2\widehat V(s))$.
  Positivity of all weights places the weight of $j$ below this total.
  Writing $|\iota|=\exp(\log|\iota|)$ and using strict monotonicity of the
  exponential gives
  $-\eta_T\widehat L(j;s)\le
  \log|\iota|-\eta_T\widehat{\bar L}(s)+\eta_T^2\widehat V(s)$.
  Finally, $\eta_T>0$ by \cref{def:improper-hedge-update}; rearranging and
  dividing by $\eta_T$ yields the claimed inequality. -/)
  (title := /-- Exponential-weights potential inequality -/)
  (latexEnv := "lemma")]
lemma improper_hedge_potential {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {G : Digraph X} {rule : manipulation_rule X} {H : ι → classifier X}
    (update : improper_hedge_update G rule H) (T : ℕ)
    (hT : source_parameter_regime (ι := ι) T)
    (history : List (observed_round X ι)) (j : ι) :
    improper_hedge_estimated_bar_loss update T history -
        improper_hedge_estimated_cumulative_loss update T history j ≤
      Real.log (Fintype.card ι : ℝ) / update.eta T +
        update.eta T * improper_hedge_estimated_square_mass update T history := by
  have heta : 0 < update.eta T := update.eta_positive T
  have hcard : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hindividual :
      update.weights T history j =
        Real.exp (-update.eta T *
          improper_hedge_estimated_cumulative_loss update T history j) := by
    simpa [improper_hedge_estimated_cumulative_loss, update.weight_initial] using
      improper_hedge_individual_weight_future update T [] history j
  have htotal :
      (∑ i, update.weights T history i) ≤
        (Fintype.card ι : ℝ) *
          Real.exp
            (-update.eta T *
                improper_hedge_estimated_bar_loss update T history +
              update.eta T ^ 2 *
                improper_hedge_estimated_square_mass update T history) := by
    simpa [improper_hedge_estimated_bar_loss,
      improper_hedge_estimated_square_mass, update.weight_initial] using
      improper_hedge_weight_sum_future_bound update T hT [] history
  have hjle : update.weights T history j ≤
      ∑ i, update.weights T history i := by
    exact Finset.single_le_sum
      (fun i _ => (update.weight_positive T history i).le) (Finset.mem_univ j)
  have hexp :
      Real.exp (-update.eta T *
          improper_hedge_estimated_cumulative_loss update T history j) ≤
        Real.exp
          (Real.log (Fintype.card ι : ℝ) +
            (-update.eta T *
                improper_hedge_estimated_bar_loss update T history +
              update.eta T ^ 2 *
                improper_hedge_estimated_square_mass update T history)) := by
    calc
      Real.exp (-update.eta T *
          improper_hedge_estimated_cumulative_loss update T history j) =
          update.weights T history j := hindividual.symm
      _ ≤ ∑ i, update.weights T history i := hjle
      _ ≤ (Fintype.card ι : ℝ) *
          Real.exp
            (-update.eta T *
                improper_hedge_estimated_bar_loss update T history +
              update.eta T ^ 2 *
                improper_hedge_estimated_square_mass update T history) := htotal
      _ = Real.exp
          (Real.log (Fintype.card ι : ℝ) +
            (-update.eta T *
                improper_hedge_estimated_bar_loss update T history +
              update.eta T ^ 2 *
                improper_hedge_estimated_square_mass update T history)) := by
        symm
        rw [Real.exp_add, Real.exp_log hcard]
  have hlinear := Real.exp_le_exp.mp hexp
  calc
    improper_hedge_estimated_bar_loss update T history -
        improper_hedge_estimated_cumulative_loss update T history j ≤
      (Real.log (Fintype.card ι : ℝ) +
          update.eta T ^ 2 *
            improper_hedge_estimated_square_mass update T history) /
        update.eta T := by
      apply (le_div_iff₀ heta).2
      nlinarith
    _ = Real.log (Fintype.card ι : ℝ) / update.eta T +
        update.eta T *
          improper_hedge_estimated_square_mass update T history := by
      field_simp [ne_of_gt heta]

@[blueprint "lem:improper-hedge-second-moment-rational-bound"
  (statement := /-- Let $a,q,d\in\mathbb R$.  If $a>0$, $q\le a$, $d>0$,
  and $a\le 2d$, then
  \[
    aq\left(\frac{1}{d}\right)^2\le 4.
  \] -/)
  (proof := /-- Since $a>0$ and $q\le a$, multiplication by $a$ gives
  $aq\le a^2$.  The assumptions $d>0$ and $a\le2d$ imply that both
  $2d-a$ and $2d+a$ are nonnegative.  Hence
  $(2d-a)(2d+a)=4d^2-a^2\ge0$, so $aq\le4d^2$.  Finally, $d^2>0$, and
  division by $d^2$ proves the asserted inequality. -/)
  (title := /-- Rational second-moment bound -/)
  (latexEnv := "lemma")]
lemma improper_hedge_second_moment_rational_bound
    (a q d : ℝ) (ha : 0 < a) (hq : q ≤ a) (hd : 0 < d)
    (had : a ≤ 2 * d) :
    a * q * (1 / d) ^ 2 ≤ 4 := by
  have haq : a * q ≤ a * a :=
    mul_le_mul_of_nonneg_left hq (le_of_lt ha)
  have hfactor : 0 ≤ (2 * d - a) * (2 * d + a) :=
    mul_nonneg (sub_nonneg.mpr had) (by nlinarith)
  have hnumerator : a * q ≤ 4 * d ^ 2 := by
    nlinarith
  rw [div_pow]
  norm_num
  exact (div_le_iff₀ (sq_pos_of_pos hd)).2 (by nlinarith)

@[blueprint "lem:improper-hedge-second-moment"
  (statement := /-- Let $\mathcal X$ and $\iota$ be types, with $\iota$
  finite and nonempty.  Fix a manipulation graph $G$ on $\mathcal X$, a
  manipulation rule, an $\iota$-indexed family $H$ of classifiers, and an
  Improper-Hedge update $U$ for these data.  For every horizon $T$ in the
  regular parameter regime, every observed history $s$, and every labeled
  example $(x,y)$, let $A$ have law $U.\operatorname{actionDistribution}(T,s)$
  and write $p_{T,s}=U.\operatorname{expertDistribution}(T,s)$.  Then
  \[
    \mathbb E_A\!\left[\sum_{i\in\iota}p_{T,s}(i)
      \left(U.\operatorname{estimator}
        \bigl(T,s,\operatorname{observedOutcome}_{G,\mathrm{rule},H}(A,(x,y)),i\bigr)
      \right)^2\right]\le 4.
  \] -/)
  (proof := /-- Let $R(x)$ be the set of indices with no positive best
  response at $x$, put $q=p_{T,s}(R(x))$, and set
  $a=\rho_T+(1-\rho_T)q$.  The PMF identity in
  \cref{def:pmf-expectation} gives $0\le q\le1$.  By
  \cref{def:best-responses,def:manipulation-rule,def:all-positive-classifier,
  def:action-classifier,def:improper-hedge-observed-outcome,
  def:improper-hedge-observation-reveals-original}, the observation reveals
  the original feature $x$ precisely when the action is the all-positive
  classifier or an index in $R(x)$.  In either revealing case the manipulated
  feature equals $x$.

  The estimator identities and mixture probabilities in
  \cref{def:improper-hedge-update} therefore show that the conditional
  second moment equals
  \[
    aq\left(\frac{1}{a-\eta_T}\right)^2
    \quad\text{for a negative label},\qquad
    aq\left(\frac{1}{a+\eta_T}\right)^2
    \quad\text{for a positive label}.
  \]
  Indeed, the revealing event has probability $a$, the estimator vanishes
  outside that event and outside $R(x)$, and its nonzero value is respectively
  $-(a-\eta_T)^{-1}$ or $(a+\eta_T)^{-1}$.

  In the regular regime, \cref{def:improper-hedge-update} gives
  $\rho_T=2\eta_T$, $\eta_T>0$, and $0\le\rho_T\le1$.  Consequently
  $a-\rho_T=(1-\rho_T)q\ge0$ and
  $a-q=\rho_T(1-q)\ge0$, so $a\ge\rho_T$, $a\ge q$, and $a>0$.
  For the negative label, $d=a-\eta_T$ is positive and $a\le2d$; for the
  positive label, $d=a+\eta_T$ has the same two properties.  Applying
  \cref{lem:improper-hedge-second-moment-rational-bound} in the two cases
  proves the claimed bound. -/)
  (title := /-- Conditional second-moment estimate -/)
  (latexEnv := "lemma")]
lemma improper_hedge_second_moment {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {G : Digraph X} {rule : manipulation_rule X} {H : ι → classifier X}
    (update : improper_hedge_update G rule H) (T : ℕ)
    (hT : source_parameter_regime (ι := ι) T)
    (history : List (observed_round X ι))
    (sample : X × strategic_label) :
    pmf_expectation (update.actionDistribution T history) (fun action =>
      ∑ i, (update.expertDistribution T history i).toReal *
        (update.estimator T history
          (improper_hedge_observed_outcome G rule H action sample) i) ^ 2) ≤ 4 := by
  classical
  rcases sample with ⟨x, y⟩
  have hnone_manipulated :
      (improper_hedge_observed_outcome G rule H none (x, y)).manipulatedFeature = x := by
    simp [improper_hedge_observed_outcome, action_classifier,
      all_positive_classifier, rule.self_of_positive]
  have hchoose_negative (j : ι) (hj : j ∈ update.negativeExperts x) :
      rule.choose G (H j) x = x := by
    apply rule.self_of_no_best_response
    exact (update.negative_experts_spec x j).mp hj
  have hH_negative (j : ι) (hj : j ∈ update.negativeExperts x) :
      H j x = strategic_label.negative := by
    cases hval : H j x with
    | negative => rfl
    | positive =>
        have hxmem : x ∈ best_responses G (H j) x := by
          exact ⟨Or.inl rfl, hval⟩
        rw [(update.negative_experts_spec x j).mp hj] at hxmem
        simp at hxmem
  have hchosen_positive (j : ι) (hj : j ∉ update.negativeExperts x) :
      H j (rule.choose G (H j) x) = strategic_label.positive := by
    by_cases hx : H j x = strategic_label.positive
    · rw [rule.self_of_positive G (H j) x hx]
      exact hx
    · have hnonempty : (best_responses G (H j) x).Nonempty := by
        rw [Set.nonempty_iff_ne_empty]
        intro hempty
        exact hj ((update.negative_experts_spec x j).mpr hempty)
      exact (rule.best_response_of_available G (H j) x hx hnonempty).2
  let a := update.observationProbability T history x
  let v := match y with
    | strategic_label.negative =>
        -1 / (a - update.eta T)
    | strategic_label.positive =>
        1 / (a + update.eta T)
  have hnone_reveals :
      improper_hedge_observation_reveals_original H
        (improper_hedge_observed_outcome G rule H none (x, y)) := by
    simp [improper_hedge_observation_reveals_original,
      improper_hedge_observed_outcome]
  have hsome_manipulated (j : ι) (hj : j ∈ update.negativeExperts x) :
      (improper_hedge_observed_outcome G rule H (some j) (x, y)).manipulatedFeature = x := by
    simp [improper_hedge_observed_outcome, action_classifier,
      hchoose_negative j hj]
  have hsome_reveals (j : ι) (hj : j ∈ update.negativeExperts x) :
      improper_hedge_observation_reveals_original H
        (improper_hedge_observed_outcome G rule H (some j) (x, y)) := by
    simp [improper_hedge_observation_reveals_original,
      improper_hedge_observed_outcome, action_classifier,
      hchoose_negative j hj, hH_negative j hj]
  have hsome_not_reveals (j : ι) (hj : j ∉ update.negativeExperts x) :
      ¬ improper_hedge_observation_reveals_original H
        (improper_hedge_observed_outcome G rule H (some j) (x, y)) := by
    simp [improper_hedge_observation_reveals_original,
      improper_hedge_observed_outcome, action_classifier,
      hchosen_positive j hj]
  have hest_none (i : ι) :
      update.estimator T history
          (improper_hedge_observed_outcome G rule H none (x, y)) i =
        if i ∈ update.negativeExperts x then v else 0 := by
    by_cases hi : i ∈ update.negativeExperts x
    · rw [if_pos hi]
      cases y with
      | negative =>
          dsimp [v]
          simpa only [hnone_manipulated] using
            update.estimator_negative T history _ i hT hnone_reveals rfl
              (by simpa only [hnone_manipulated] using hi)
      | positive =>
          dsimp [v]
          simpa only [hnone_manipulated] using
            update.estimator_positive T history _ i hT hnone_reveals rfl
              (by simpa only [hnone_manipulated] using hi)
    · rw [if_neg hi]
      apply update.estimator_zero
      right
      simpa only [hnone_manipulated] using hi
  have hest_some (j i : ι) :
      update.estimator T history
          (improper_hedge_observed_outcome G rule H (some j) (x, y)) i =
        if j ∈ update.negativeExperts x then
          if i ∈ update.negativeExperts x then v else 0
        else 0 := by
    by_cases hj : j ∈ update.negativeExperts x
    · rw [if_pos hj]
      by_cases hi : i ∈ update.negativeExperts x
      · rw [if_pos hi]
        cases y with
        | negative =>
            dsimp [v]
            simpa only [hsome_manipulated j hj] using
              update.estimator_negative T history _ i hT
                (hsome_reveals j hj) rfl
                (by simpa only [hsome_manipulated j hj] using hi)
        | positive =>
            dsimp [v]
            simpa only [hsome_manipulated j hj] using
              update.estimator_positive T history _ i hT
                (hsome_reveals j hj) rfl
                (by simpa only [hsome_manipulated j hj] using hi)
      · rw [if_neg hi]
        apply update.estimator_zero
        right
        simpa only [hsome_manipulated j hj] using hi
    · rw [if_neg hj]
      apply update.estimator_zero
      exact Or.inl (hsome_not_reveals j hj)
  simp [pmf_expectation, hest_none, hest_some]
  rw [update.exploration_probability]
  simp_rw [update.expert_action_probability, ← Finset.sum_mul,
    ← Finset.mul_sum]
  let q := ∑ i ∈ update.negativeExperts x,
    (update.expertDistribution T history i).toReal
  change update.rho T * (q * v ^ 2) +
      ((1 - update.rho T) * q) * (q * v ^ 2) ≤ 4
  have hp_sum :
      (∑ i, (update.expertDistribution T history i).toReal) = 1 := by
    calc
      (∑ i, (update.expertDistribution T history i).toReal) =
          ∑' i, (update.expertDistribution T history i).toReal := by
        rw [tsum_fintype]
      _ = (∑' i, update.expertDistribution T history i).toReal :=
        (ENNReal.tsum_toReal_eq (fun i => PMF.apply_ne_top _ i)).symm
      _ = 1 := by rw [PMF.tsum_coe]; norm_num
  have hq_nonnegative : 0 ≤ q := by
    dsimp [q]
    exact Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg
  have hq_at_most_one : q ≤ 1 := by
    dsimp [q]
    calc
      (∑ i ∈ update.negativeExperts x,
          (update.expertDistribution T history i).toReal) =
          ∑ i, if i ∈ update.negativeExperts x then
            (update.expertDistribution T history i).toReal else 0 := by simp
      _ ≤
          ∑ i, (update.expertDistribution T history i).toReal := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases himem : i ∈ update.negativeExperts x
        · simp [himem]
        · simp [himem, ENNReal.toReal_nonneg]
      _ = 1 := hp_sum
  have ha : a = update.rho T + (1 - update.rho T) * q := by
    dsimp [a, q]
    exact update.observation_probability_formula T history x
  have hrho_eta : update.rho T = 2 * update.eta T := by
    rw [update.rho_formula T hT, update.eta_formula T hT]
    ring
  have hrho_positive : 0 < update.rho T := by
    nlinarith [update.eta_positive T]
  have ha_at_least_rho : update.rho T ≤ a := by
    rw [ha]
    have hproduct : 0 ≤ (1 - update.rho T) * q :=
      mul_nonneg (sub_nonneg.mpr (update.rho_at_most_one T)) hq_nonnegative
    linarith
  have ha_at_least_q : q ≤ a := by
    rw [ha]
    have hproduct : 0 ≤ update.rho T * (1 - q) :=
      mul_nonneg (update.rho_nonnegative T) (sub_nonneg.mpr hq_at_most_one)
    nlinarith
  have ha_positive : 0 < a := lt_of_lt_of_le hrho_positive ha_at_least_rho
  calc
    update.rho T * (q * v ^ 2) +
        (1 - update.rho T) * q * (q * v ^ 2) = a * q * v ^ 2 := by
      rw [ha]
      ring
    _ ≤ 4 := by
      cases y with
      | negative =>
          have hd : 0 < a - update.eta T := by
            nlinarith
          have had : a ≤ 2 * (a - update.eta T) := by
            nlinarith
          dsimp [v]
          rw [show (-1 / (a - update.eta T)) ^ 2 =
            (1 / (a - update.eta T)) ^ 2 by ring]
          exact improper_hedge_second_moment_rational_bound
            a q (a - update.eta T) ha_positive ha_at_least_q hd had
      | positive =>
          have hd : 0 < a + update.eta T := by
            nlinarith [update.eta_positive T]
          have had : a ≤ 2 * (a + update.eta T) := by
            nlinarith [update.eta_positive T]
          simpa [v] using improper_hedge_second_moment_rational_bound
            a q (a + update.eta T) ha_positive ha_at_least_q hd had

@[blueprint "lem:improper-hedge-bias"
  (statement := /-- Let $\mathcal X$ and $\iota$ be types, with $\iota$
  finite and nonempty.  Fix a manipulation graph $G$ on $\mathcal X$, a
  tie-breaking manipulation rule, an $\iota$-indexed family $H$ of
  classifiers, and an Improper-Hedge update for these data.  For every horizon
  $T$ in the regular parameter regime, every observed history $s$, and every
  labeled example $(x,y)$, the update's expert law $p_{T,s}$ and action law
  $A_{T,s}$ satisfy
  \[
    \sum_{i\in\iota}p_{T,s}(i)\left(
      d_G(H_i,(x,y))-
      \mathbb E_{a\sim A_{T,s}}
        \bigl[\widehat d_{T,s}(\operatorname{obs}(a,x,y),i)\bigr]\right)
    \le 2\eta_T,
  \]
  where $\operatorname{obs}(a,x,y)$ is the observed outcome generated by
  action $a$ and example $(x,y)$. -/)
  (proof := /-- Put $q_t=\sum_{i\in R(x)}p_{T,s}(i)$ and
  $a_t=\rho_T+(1-\rho_T)q_t$.  By
  \cref{def:strategic-loss,def:shifted-loss,def:all-positive-classifier}, an
  expert in $R(x)$ has shifted loss $-1$ for a negative label and $1$ for a
  positive label, whereas an expert outside $R(x)$ has shifted loss zero.
  The action probabilities and estimator identities in
  \cref{def:improper-hedge-update} show that the total mass of revealing
  actions is exactly $a_t$.  Hence the conditional estimator mean of an
  expert in $R(x)$ is respectively $-a_t/(a_t-\eta_T)$ and
  $a_t/(a_t+\eta_T)$; outside $R(x)$ it is zero.  The mixture bias is therefore
  $q_t\eta_T/(a_t-\eta_T)$ for a negative label and
  $q_t\eta_T/(a_t+\eta_T)$ for a positive label.

  In the regular regime, $\rho_T=2\eta_T$, $0<\eta_T\le1/2$, and
  $0\le q_t\le1$.  Thus
  $a_t=2\eta_T+(1-2\eta_T)q_t$.  If $4\eta_T\le1$, nonnegativity of $q_t$
  gives $q_t\le2(a_t-\eta_T)$ and $q_t\le2(a_t+\eta_T)$.  If
  $4\eta_T>1$, multiplying $q_t\le1$ by $1-4\eta_T<0$ gives the same two
  inequalities, using $2\eta_T\le1$.  Both denominators are positive, so
  either bias is at most $2\eta_T$. -/)
  (title := /-- Conditional estimator-bias estimate -/)
  (latexEnv := "lemma")]
lemma improper_hedge_bias {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {G : Digraph X} {rule : manipulation_rule X} {H : ι → classifier X}
    (update : improper_hedge_update G rule H) (T : ℕ)
    (hT : source_parameter_regime (ι := ι) T)
    (history : List (observed_round X ι))
    (sample : X × strategic_label) :
    (∑ i, (update.expertDistribution T history i).toReal *
      (shifted_loss G rule (H i) sample -
        pmf_expectation (update.actionDistribution T history) (fun action =>
          update.estimator T history
            (improper_hedge_observed_outcome G rule H action sample) i))) ≤
      2 * update.eta T := by
  classical
  rcases sample with ⟨x, y⟩
  have hnegative_of_mem (i : ι) (hi : i ∈ update.negativeExperts x) :
      H i x = strategic_label.negative := by
    have hbr : best_responses G (H i) x = ∅ :=
      (update.negative_experts_spec x i).1 hi
    cases hix : H i x with
    | negative => rfl
    | positive =>
        exfalso
        have hx : x ∈ best_responses G (H i) x := by
          exact ⟨Or.inl rfl, hix⟩
        rw [hbr] at hx
        exact hx
  have hchoose_of_mem (i : ι) (hi : i ∈ update.negativeExperts x) :
      rule.choose G (H i) x = x :=
    rule.self_of_no_best_response G (H i) x
      ((update.negative_experts_spec x i).1 hi)
  have hpositive_of_not_mem (i : ι) (hi : i ∉ update.negativeExperts x) :
      H i (rule.choose G (H i) x) = strategic_label.positive := by
    by_cases hix : H i x = strategic_label.positive
    · rw [rule.self_of_positive G (H i) x hix]
      exact hix
    · have hbrne : best_responses G (H i) x ≠ ∅ := by
        intro hbr
        exact hi ((update.negative_experts_spec x i).2 hbr)
      exact (rule.best_response_of_available G (H i) x hix
        (Set.nonempty_iff_ne_empty.mpr hbrne)).2
  have hnone_feature :
      (improper_hedge_observed_outcome G rule H none (x, y)).manipulatedFeature = x := by
    exact rule.self_of_positive G (all_positive_classifier X) x rfl
  have hnone_reveals :
      improper_hedge_observation_reveals_original H
        (improper_hedge_observed_outcome G rule H none (x, y)) := by
    simp [improper_hedge_observation_reveals_original,
      improper_hedge_observed_outcome]
  have hsome_feature_of_mem (j : ι) (hj : j ∈ update.negativeExperts x) :
      (improper_hedge_observed_outcome G rule H (some j) (x, y)).manipulatedFeature = x := by
    exact hchoose_of_mem j hj
  have hsome_reveals_of_mem (j : ι) (hj : j ∈ update.negativeExperts x) :
      improper_hedge_observation_reveals_original H
        (improper_hedge_observed_outcome G rule H (some j) (x, y)) := by
    simp [improper_hedge_observation_reveals_original,
      improper_hedge_observed_outcome, action_classifier, hchoose_of_mem j hj,
      hnegative_of_mem j hj]
  have hsome_not_reveals_of_not_mem (j : ι)
      (hj : j ∉ update.negativeExperts x) :
      ¬ improper_hedge_observation_reveals_original H
        (improper_hedge_observed_outcome G rule H (some j) (x, y)) := by
    simp [improper_hedge_observation_reveals_original,
      improper_hedge_observed_outcome, action_classifier,
      hpositive_of_not_mem j hj]
  have hrho_eta : update.rho T = 2 * update.eta T := by
    rw [update.rho_formula T hT, update.eta_formula T hT]
    ring
  have heta_pos : 0 < update.eta T := update.eta_positive T
  have heta_le_half : update.eta T ≤ (1 / 2 : ℝ) := by
    nlinarith [update.rho_at_most_one T]
  have hp_nonnegative (i : ι) :
      0 ≤ ((update.expertDistribution T history i).toReal : ℝ) :=
    ENNReal.toReal_nonneg
  have hloss_of_mem (i : ι) (hi : i ∈ update.negativeExperts x) :
      shifted_loss G rule (H i) (x, y) =
        match y with
        | strategic_label.negative => -1
        | strategic_label.positive => 1 := by
    cases y <;>
      simp [shifted_loss, strategic_loss, hchoose_of_mem i hi,
        hnegative_of_mem i hi, all_positive_classifier]
  have hloss_of_not_mem (i : ι) (hi : i ∉ update.negativeExperts x) :
      shifted_loss G rule (H i) (x, y) = 0 := by
    cases y <;>
      simp [shifted_loss, strategic_loss, hpositive_of_not_mem i hi,
        all_positive_classifier]
  have hestimator_none (i : ι) (hi : i ∈ update.negativeExperts x) :
      update.estimator T history
          (improper_hedge_observed_outcome G rule H none (x, y)) i =
        match y with
        | strategic_label.negative =>
            -1 / (update.observationProbability T history x - update.eta T)
        | strategic_label.positive =>
            1 / (update.observationProbability T history x + update.eta T) := by
    cases y
    · simpa only [hnone_feature] using
        update.estimator_negative T history
          (improper_hedge_observed_outcome G rule H none
            (x, strategic_label.negative)) i hT hnone_reveals rfl
          (by simpa only [hnone_feature] using hi)
    · simpa only [hnone_feature] using
        update.estimator_positive T history
          (improper_hedge_observed_outcome G rule H none
            (x, strategic_label.positive)) i hT hnone_reveals rfl
          (by simpa only [hnone_feature] using hi)
  have hestimator_some_of_mem (i j : ι)
      (hi : i ∈ update.negativeExperts x) (hj : j ∈ update.negativeExperts x) :
      update.estimator T history
          (improper_hedge_observed_outcome G rule H (some j) (x, y)) i =
        match y with
        | strategic_label.negative =>
            -1 / (update.observationProbability T history x - update.eta T)
        | strategic_label.positive =>
            1 / (update.observationProbability T history x + update.eta T) := by
    cases y
    · simpa only [hsome_feature_of_mem j hj] using
        update.estimator_negative T history
          (improper_hedge_observed_outcome G rule H (some j)
            (x, strategic_label.negative)) i hT
          (hsome_reveals_of_mem j hj) rfl
          (by simpa only [hsome_feature_of_mem j hj] using hi)
    · simpa only [hsome_feature_of_mem j hj] using
        update.estimator_positive T history
          (improper_hedge_observed_outcome G rule H (some j)
            (x, strategic_label.positive)) i hT
          (hsome_reveals_of_mem j hj) rfl
          (by simpa only [hsome_feature_of_mem j hj] using hi)
  have hestimator_some_of_not_mem (i j : ι)
      (hj : j ∉ update.negativeExperts x) :
      update.estimator T history
          (improper_hedge_observed_outcome G rule H (some j) (x, y)) i = 0 := by
    exact update.estimator_zero T history _ i
      (Or.inl (hsome_not_reveals_of_not_mem j hj))
  have hestimator_of_expert_not_mem (i : ι)
      (hi : i ∉ update.negativeExperts x) (action : Option ι) :
      update.estimator T history
          (improper_hedge_observed_outcome G rule H action (x, y)) i = 0 := by
    cases action with
    | none =>
        apply update.estimator_zero T history _ i
        exact Or.inr (by simpa only [hnone_feature] using hi)
    | some j =>
        by_cases hj : j ∈ update.negativeExperts x
        · apply update.estimator_zero T history _ i
          exact Or.inr (by simpa only [hsome_feature_of_mem j hj] using hi)
        · exact hestimator_some_of_not_mem i j hj
  have hp_sum :
      ∑ i, (update.expertDistribution T history i).toReal = (1 : ℝ) := by
    have hconvert :
        (∑' i : ι, update.expertDistribution T history i).toReal =
          ∑' i : ι, (update.expertDistribution T history i).toReal :=
      ENNReal.tsum_toReal_eq (fun i => PMF.apply_ne_top _ i)
    calc
      ∑ i, (update.expertDistribution T history i).toReal =
          ∑' i, (update.expertDistribution T history i).toReal := by simp
      _ = (∑' i, update.expertDistribution T history i).toReal := hconvert.symm
      _ = 1 := by
        rw [(update.expertDistribution T history).tsum_coe]
        rfl
  have hq_nonnegative :
      0 ≤ ∑ i ∈ update.negativeExperts x,
        (update.expertDistribution T history i).toReal := by
    exact Finset.sum_nonneg fun i _ => hp_nonnegative i
  have hq_le_one :
      (∑ i ∈ update.negativeExperts x,
        (update.expertDistribution T history i).toReal) ≤ 1 := by
    calc
      (∑ i ∈ update.negativeExperts x,
          (update.expertDistribution T history i).toReal) ≤
          ∑ i, (update.expertDistribution T history i).toReal := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.subset_univ _) (fun i _ _ => hp_nonnegative i)
      _ = 1 := hp_sum
  have ha_formula := update.observation_probability_formula T history x
  rw [hrho_eta] at ha_formula
  cases y
  · have hdenominator_positive :
        0 < update.observationProbability T history x - update.eta T := by
      rw [ha_formula]
      nlinarith
    have hexpectation (i : ι) (hi : i ∈ update.negativeExperts x) :
        pmf_expectation (update.actionDistribution T history) (fun action =>
          update.estimator T history
            (improper_hedge_observed_outcome G rule H action
              (x, strategic_label.negative)) i) =
          -update.observationProbability T history x /
            (update.observationProbability T history x - update.eta T) := by
      unfold pmf_expectation
      rw [tsum_fintype, Fintype.sum_option,
        update.exploration_probability]
      simp only
      rw [hestimator_none i hi]
      have hsum :
          (∑ j,
            (update.actionDistribution T history (some j)).toReal *
              update.estimator T history
                (improper_hedge_observed_outcome G rule H (some j)
                  (x, strategic_label.negative)) i) =
            ∑ j, if j ∈ update.negativeExperts x then
              (1 - update.rho T) *
                  (update.expertDistribution T history j).toReal *
                (-1 / (update.observationProbability T history x -
                  update.eta T))
              else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j ∈ update.negativeExperts x
        · rw [if_pos hj, update.expert_action_probability,
            hestimator_some_of_mem i j hi hj]
        · rw [if_neg hj, hestimator_some_of_not_mem i j hj, mul_zero]
      rw [hsum, ← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      rw [← add_mul, ← update.observation_probability_formula T history x]
      ring
    have hbias (i : ι) (hi : i ∈ update.negativeExperts x) :
        shifted_loss G rule (H i) (x, strategic_label.negative) -
            pmf_expectation (update.actionDistribution T history) (fun action =>
              update.estimator T history
                (improper_hedge_observed_outcome G rule H action
                  (x, strategic_label.negative)) i) =
          update.eta T /
            (update.observationProbability T history x - update.eta T) := by
      rw [hloss_of_mem i hi, hexpectation i hi]
      field_simp
      ring
    have hsum_bias :
        (∑ i, (update.expertDistribution T history i).toReal *
          (shifted_loss G rule (H i) (x, strategic_label.negative) -
            pmf_expectation (update.actionDistribution T history) (fun action =>
              update.estimator T history
                (improper_hedge_observed_outcome G rule H action
                  (x, strategic_label.negative)) i))) =
          (∑ i ∈ update.negativeExperts x,
              (update.expertDistribution T history i).toReal) *
            (update.eta T /
              (update.observationProbability T history x - update.eta T)) := by
      calc
        _ = ∑ i, if i ∈ update.negativeExperts x then
              (update.expertDistribution T history i).toReal *
                (update.eta T /
                  (update.observationProbability T history x - update.eta T))
            else 0 := by
              apply Finset.sum_congr rfl
              intro i _
              by_cases hi : i ∈ update.negativeExperts x
              · rw [if_pos hi, hbias i hi]
              · rw [if_neg hi, hloss_of_not_mem i hi]
                simp [pmf_expectation, tsum_fintype,
                  hestimator_of_expert_not_mem i hi]
        _ = _ := by
          rw [← Finset.sum_filter]
          simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
          rw [Finset.sum_mul]
    rw [hsum_bias]
    have hmass_bound :
        (∑ i ∈ update.negativeExperts x,
            (update.expertDistribution T history i).toReal) ≤
          2 * (update.observationProbability T history x - update.eta T) := by
      rw [ha_formula]
      by_cases hquarter : 4 * update.eta T ≤ 1
      · have hproduct :
            0 ≤ (1 - 4 * update.eta T) *
              (∑ i ∈ update.negativeExperts x,
                (update.expertDistribution T history i).toReal) :=
          mul_nonneg (by nlinarith) hq_nonnegative
        nlinarith
      · have hcoefficient : 1 - 4 * update.eta T ≤ 0 := by nlinarith
        have hproduct := mul_le_mul_of_nonpos_left hq_le_one hcoefficient
        nlinarith
    have hnumerator :
        (∑ i ∈ update.negativeExperts x,
            (update.expertDistribution T history i).toReal) * update.eta T ≤
          2 * update.eta T *
            (update.observationProbability T history x - update.eta T) := by
      have := mul_le_mul_of_nonneg_right hmass_bound (le_of_lt heta_pos)
      nlinarith
    calc
      _ = ((∑ i ∈ update.negativeExperts x,
              (update.expertDistribution T history i).toReal) * update.eta T) /
            (update.observationProbability T history x - update.eta T) := by ring
      _ ≤ 2 * update.eta T :=
        (div_le_iff₀ hdenominator_positive).2 (by simpa [mul_assoc] using hnumerator)
  · have hdenominator_positive :
        0 < update.observationProbability T history x + update.eta T := by
      rw [ha_formula]
      nlinarith
    have hexpectation (i : ι) (hi : i ∈ update.negativeExperts x) :
        pmf_expectation (update.actionDistribution T history) (fun action =>
          update.estimator T history
            (improper_hedge_observed_outcome G rule H action
              (x, strategic_label.positive)) i) =
          update.observationProbability T history x /
            (update.observationProbability T history x + update.eta T) := by
      unfold pmf_expectation
      rw [tsum_fintype, Fintype.sum_option,
        update.exploration_probability]
      simp only
      rw [hestimator_none i hi]
      have hsum :
          (∑ j,
            (update.actionDistribution T history (some j)).toReal *
              update.estimator T history
                (improper_hedge_observed_outcome G rule H (some j)
                  (x, strategic_label.positive)) i) =
            ∑ j, if j ∈ update.negativeExperts x then
              (1 - update.rho T) *
                  (update.expertDistribution T history j).toReal *
                (1 / (update.observationProbability T history x +
                  update.eta T))
              else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j ∈ update.negativeExperts x
        · rw [if_pos hj, update.expert_action_probability,
            hestimator_some_of_mem i j hi hj]
        · rw [if_neg hj, hestimator_some_of_not_mem i j hj, mul_zero]
      rw [hsum, ← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      rw [← add_mul, ← update.observation_probability_formula T history x]
      ring
    have hbias (i : ι) (hi : i ∈ update.negativeExperts x) :
        shifted_loss G rule (H i) (x, strategic_label.positive) -
            pmf_expectation (update.actionDistribution T history) (fun action =>
              update.estimator T history
                (improper_hedge_observed_outcome G rule H action
                  (x, strategic_label.positive)) i) =
          update.eta T /
            (update.observationProbability T history x + update.eta T) := by
      rw [hloss_of_mem i hi, hexpectation i hi]
      field_simp
      ring
    have hsum_bias :
        (∑ i, (update.expertDistribution T history i).toReal *
          (shifted_loss G rule (H i) (x, strategic_label.positive) -
            pmf_expectation (update.actionDistribution T history) (fun action =>
              update.estimator T history
                (improper_hedge_observed_outcome G rule H action
                  (x, strategic_label.positive)) i))) =
          (∑ i ∈ update.negativeExperts x,
              (update.expertDistribution T history i).toReal) *
            (update.eta T /
              (update.observationProbability T history x + update.eta T)) := by
      calc
        _ = ∑ i, if i ∈ update.negativeExperts x then
              (update.expertDistribution T history i).toReal *
                (update.eta T /
                  (update.observationProbability T history x + update.eta T))
            else 0 := by
              apply Finset.sum_congr rfl
              intro i _
              by_cases hi : i ∈ update.negativeExperts x
              · rw [if_pos hi, hbias i hi]
              · rw [if_neg hi, hloss_of_not_mem i hi]
                simp [pmf_expectation, tsum_fintype,
                  hestimator_of_expert_not_mem i hi]
        _ = _ := by
          rw [← Finset.sum_filter]
          simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
          rw [Finset.sum_mul]
    rw [hsum_bias]
    have hmass_bound :
        (∑ i ∈ update.negativeExperts x,
            (update.expertDistribution T history i).toReal) ≤
          2 * (update.observationProbability T history x + update.eta T) := by
      rw [ha_formula]
      by_cases hquarter : 4 * update.eta T ≤ 1
      · have hproduct :
            0 ≤ (1 - 4 * update.eta T) *
              (∑ i ∈ update.negativeExperts x,
                (update.expertDistribution T history i).toReal) :=
          mul_nonneg (by nlinarith) hq_nonnegative
        nlinarith
      · have hcoefficient : 1 - 4 * update.eta T ≤ 0 := by nlinarith
        have hproduct := mul_le_mul_of_nonpos_left hq_le_one hcoefficient
        nlinarith
    have hnumerator :
        (∑ i ∈ update.negativeExperts x,
            (update.expertDistribution T history i).toReal) * update.eta T ≤
          2 * update.eta T *
            (update.observationProbability T history x + update.eta T) := by
      have := mul_le_mul_of_nonneg_right hmass_bound (le_of_lt heta_pos)
      nlinarith
    calc
      _ = ((∑ i ∈ update.negativeExperts x,
              (update.expertDistribution T history i).toReal) * update.eta T) /
            (update.observationProbability T history x + update.eta T) := by ring
      _ ≤ 2 * update.eta T :=
        (div_le_iff₀ hdenominator_positive).2 (by simpa [mul_assoc] using hnumerator)

@[blueprint "lem:improper-hedge-exponential-moment"
  (statement := /-- Let $\iota$ be a finite nonempty expert index type, let
  $G$ be a manipulation graph with a fixed manipulation rule, let
  $(h_i)_{i\in\iota}$ be a family of classifiers, and fix an Improper-Hedge
  update for these data.  If the horizon $T$ satisfies the source parameter
  regime, then for every observed history $s$, labeled sample $z$, and expert
  $i\in\iota$,
  \[
    \mathbb E_{A\sim\mathcal D_T(s)}\!\left[
      \exp\!\left(\eta_T\bigl(
        \widehat d_{T,s}(\operatorname{obs}_{G}(A,z),i)-d_G(h_i,z)
      \bigr)\right)
    \right]\le 1,
  \]
  where $\mathcal D_T(s)$ is the update's action distribution,
  $\operatorname{obs}_{G}(A,z)$ is the observation induced by action $A$ and
  sample $z$, $\widehat d_{T,s}$ is the update's estimator, and $d_G$ is the
  shifted strategic loss. -/)
  (proof := /-- Write $R(x)$ for the negative-expert set and $a$ for the
  observation probability at the original feature $x$.  The definitions of
  best response and manipulation imply that the observation reveals $x$
  exactly when the action is $\bot$ or is an index in $R(x)$; on this event
  the manipulated feature equals $x$.  This follows from
  \cref{def:best-responses, def:manipulation-rule,
  def:improper-hedge-observation-reveals-original,
  def:improper-hedge-observed-outcome}.  Expanding the finite expectation in
  \cref{def:pmf-expectation} and using the action-mass and
  observation-probability identities in
  \cref{def:improper-hedge-update} shows that every random variable equal to
  $u$ on the revealing event and $v$ otherwise has expectation
  $au+(1-a)v$.

  The parameter formulas in \cref{def:improper-hedge-update} give
  $\rho_T=2\eta_T$.  Since the expert masses are nonnegative and
  $\rho_T\le1$, the observation-probability formula yields
  $a\ge2\eta_T>0$.  If $i\notin R(x)$, the manipulation rule makes both
  $h_i$ and the all-positive classifier predict positively after
  manipulation.  Hence the shifted loss in \cref{def:shifted-loss} and the
  estimator in \cref{def:improper-hedge-update} both vanish, so the integrand
  is identically one.

  Suppose $i\in R(x)$.  For a negative label, the shifted loss is $-1$ and
  the estimator equals $-1/(a-\eta_T)$ on the revealing event and zero
  otherwise.  Put $q=\eta_T/(a-\eta_T)\ge0$.  From
  $1+q\le e^q$ one obtains $e^{-q}\le(1+q)^{-1}$, and therefore
  [
    ae^{-q}+1-a\le1-\eta_T\le e^{-\eta_T}.
  ]
  Multiplication by $e^{\eta_T}$ proves the required bound.  For a positive
  label, the shifted loss is $1$ and the revealing estimate is
  $1/(a+\eta_T)$.  With $r=\eta_T/(a+\eta_T)\in[0,1)$, the standard bound
  $e^r\le(1-r)^{-1}$ gives
  [
    ae^r+1-a\le1+\eta_T\le e^{\eta_T}.
  ]
  Multiplication by $e^{-\eta_T}$ completes the positive-label case. -/)
  (title := /-- Conditional exponential-moment estimate -/)
  (latexEnv := "lemma")]
lemma improper_hedge_exponential_moment {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {G : Digraph X} {rule : manipulation_rule X} {H : ι → classifier X}
    (update : improper_hedge_update G rule H) (T : ℕ)
    (hT : source_parameter_regime (ι := ι) T)
    (history : List (observed_round X ι))
    (sample : X × strategic_label) (i : ι) :
    pmf_expectation (update.actionDistribution T history) (fun action =>
      Real.exp (update.eta T *
        (update.estimator T history
            (improper_hedge_observed_outcome G rule H action sample) i -
          shifted_loss G rule (H i) sample))) ≤ 1 := by
  classical
  have hchoose_negative_iff (j : ι) :
      H j (rule.choose G (H j) sample.1) = strategic_label.negative ↔
        j ∈ update.negativeExperts sample.1 := by
    rw [update.negative_experts_spec]
    constructor
    · intro hneg
      by_contra hne
      have hnempty : (best_responses G (H j) sample.1).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr hne
      have hxnot : H j sample.1 ≠ strategic_label.positive := by
        intro hpos
        rw [rule.self_of_positive G (H j) sample.1 hpos, hpos] at hneg
        contradiction
      have hbest :=
        rule.best_response_of_available G (H j) sample.1 hxnot hnempty
      have hbestlabel :
          H j (rule.choose G (H j) sample.1) = strategic_label.positive :=
        hbest.2
      rw [hneg] at hbestlabel
      contradiction
    · intro hempty
      have hself := rule.self_of_no_best_response G (H j) sample.1 hempty
      have hxneg : H j sample.1 = strategic_label.negative := by
        cases hlabel : H j sample.1
        · rfl
        · exfalso
          have hxmem : sample.1 ∈ best_responses G (H j) sample.1 :=
            ⟨Or.inl rfl, hlabel⟩
          rw [hempty] at hxmem
          exact hxmem
      rw [hself, hxneg]
  have hnone : improper_hedge_observation_reveals_original H
      (improper_hedge_observed_outcome G rule H none sample) := by
    simp [improper_hedge_observation_reveals_original,
      improper_hedge_observed_outcome]
  have hsome (j : ι) : improper_hedge_observation_reveals_original H
      (improper_hedge_observed_outcome G rule H (some j) sample) ↔
        j ∈ update.negativeExperts sample.1 := by
    simpa [improper_hedge_observation_reveals_original,
      improper_hedge_observed_outcome, action_classifier] using
        hchoose_negative_iff j
  have hfeature_of_reveal (action : Option ι)
      (ha : improper_hedge_observation_reveals_original H
        (improper_hedge_observed_outcome G rule H action sample)) :
      (improper_hedge_observed_outcome G rule H action sample).manipulatedFeature =
        sample.1 := by
    cases action with
    | none =>
        simp [improper_hedge_observed_outcome, action_classifier,
          all_positive_classifier, rule.self_of_positive]
    | some j =>
        have hj := (hsome j).mp ha
        have hempty := (update.negative_experts_spec sample.1 j).mp hj
        simp [improper_hedge_observed_outcome, action_classifier,
          rule.self_of_no_best_response G (H j) sample.1 hempty]
  have hpsum :
      ∑ j, (update.expertDistribution T history j).toReal = 1 := by
    calc
      ∑ j, (update.expertDistribution T history j).toReal =
          ∑' j, (update.expertDistribution T history j).toReal :=
        (tsum_fintype _).symm
      _ = (∑' j, update.expertDistribution T history j).toReal :=
        (ENNReal.tsum_toReal_eq
          (fun j => (update.expertDistribution T history).apply_ne_top j)).symm
      _ = 1 := by rw [PMF.tsum_coe]; norm_num
  have hmix (u v : ℝ) :
      (∑ j, (update.expertDistribution T history j).toReal *
        (if j ∈ update.negativeExperts sample.1 then u else v)) =
        (∑ j ∈ update.negativeExperts sample.1,
            (update.expertDistribution T history j).toReal) * u +
          (1 - ∑ j ∈ update.negativeExperts sample.1,
            (update.expertDistribution T history j).toReal) * v := by
    calc
      _ = ∑ j, ((update.expertDistribution T history j).toReal * v +
          if j ∈ update.negativeExperts sample.1 then
            (update.expertDistribution T history j).toReal * (u - v)
          else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j ∈ update.negativeExperts sample.1 <;>
          simp [hj] <;> ring
      _ = (∑ j, (update.expertDistribution T history j).toReal) * v +
          (∑ j ∈ update.negativeExperts sample.1,
            (update.expertDistribution T history j).toReal) * (u - v) := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
        simp [Finset.sum_mul]
      _ = _ := by rw [hpsum]; ring
  have hexpect (u v : ℝ) :
      pmf_expectation (update.actionDistribution T history) (fun action =>
        if improper_hedge_observation_reveals_original H
            (improper_hedge_observed_outcome G rule H action sample) then u
        else v) =
        update.observationProbability T history sample.1 * u +
          (1 - update.observationProbability T history sample.1) * v := by
    simp [pmf_expectation, tsum_fintype, Fintype.sum_option, hnone, hsome,
      update.exploration_probability, update.expert_action_probability]
    rw [show (∑ x, if x ∈ update.negativeExperts sample.1 then
          (1 - update.rho T) *
            (update.expertDistribution T history x).toReal * u
        else
          (1 - update.rho T) *
            (update.expertDistribution T history x).toReal * v) =
        ∑ x, (1 - update.rho T) *
          ((update.expertDistribution T history x).toReal *
            (if x ∈ update.negativeExperts sample.1 then u else v)) by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ update.negativeExperts sample.1 <;> simp [hx] <;> ring]
    rw [← Finset.mul_sum, hmix, update.observation_probability_formula]
    ring
  by_cases hi : i ∈ update.negativeExperts sample.1
  · have heta : 0 < update.eta T := update.eta_positive T
    have hrho : update.rho T = 2 * update.eta T := by
      rw [update.rho_formula T hT, update.eta_formula T hT]
      ring
    have hq : 0 ≤ ∑ j ∈ update.negativeExperts sample.1,
        (update.expertDistribution T history j).toReal := by
      exact Finset.sum_nonneg fun j _ =>
        ENNReal.toReal_nonneg
    have ha : 2 * update.eta T ≤
        update.observationProbability T history sample.1 := by
      rw [update.observation_probability_formula, hrho]
      have hrle := update.rho_at_most_one T
      nlinarith [mul_nonneg (sub_nonneg.mpr hrle) hq]
    have hapos : 0 < update.observationProbability T history sample.1 := by
      linarith
    cases hy : sample.2
    · have hchosen_neg :
          H i (rule.choose G (H i) sample.1) =
            strategic_label.negative :=
        (hchoose_negative_iff i).mpr hi
      have hloss : shifted_loss G rule (H i) sample = -1 := by
        simp [shifted_loss, strategic_loss, all_positive_classifier,
          rule.self_of_positive, hchosen_neg, hy]
      have hest (action : Option ι) :
          update.estimator T history
              (improper_hedge_observed_outcome G rule H action sample) i =
            if improper_hedge_observation_reveals_original H
                (improper_hedge_observed_outcome G rule H action sample) then
              -1 / (update.observationProbability T history sample.1 -
                update.eta T)
            else 0 := by
        by_cases hreveal : improper_hedge_observation_reveals_original H
          (improper_hedge_observed_outcome G rule H action sample)
        · have hfeature := hfeature_of_reveal action hreveal
          have himem : i ∈ update.negativeExperts
              (improper_hedge_observed_outcome G rule H action sample).manipulatedFeature := by
            rwa [hfeature]
          rw [if_pos hreveal,
            update.estimator_negative T history
              (improper_hedge_observed_outcome G rule H action sample) i hT
              hreveal (by simpa [improper_hedge_observed_outcome] using hy)
              himem,
            hfeature]
        · rw [if_neg hreveal]
          exact update.estimator_zero T history
            (improper_hedge_observed_outcome G rule H action sample) i
            (Or.inl hreveal)
      have hreduce :
          pmf_expectation (update.actionDistribution T history) (fun action =>
            Real.exp (update.eta T *
              (update.estimator T history
                  (improper_hedge_observed_outcome G rule H action sample) i -
                shifted_loss G rule (H i) sample))) =
            pmf_expectation (update.actionDistribution T history) (fun action =>
              if improper_hedge_observation_reveals_original H
                  (improper_hedge_observed_outcome G rule H action sample) then
                Real.exp (update.eta T *
                  (-1 / (update.observationProbability T history sample.1 -
                    update.eta T) + 1))
              else Real.exp (update.eta T)) := by
        apply congrArg (pmf_expectation (update.actionDistribution T history))
        funext action
        rw [hest, hloss]
        by_cases hreveal : improper_hedge_observation_reveals_original H
          (improper_hedge_observed_outcome G rule H action sample) <;>
          simp [hreveal]
      rw [hreduce, hexpect]
      have hbpos : 0 <
          update.observationProbability T history sample.1 - update.eta T := by
        linarith
      have hxnonneg : 0 ≤
          update.eta T /
            (update.observationProbability T history sample.1 - update.eta T) :=
        div_nonneg heta.le hbpos.le
      have hxdenpos : 0 < 1 + update.eta T /
          (update.observationProbability T history sample.1 - update.eta T) := by
        linarith
      have hexpfrac :
          Real.exp (-update.eta T /
              (update.observationProbability T history sample.1 -
                update.eta T)) ≤
            1 / (1 + update.eta T /
              (update.observationProbability T history sample.1 -
                update.eta T)) := by
        rw [show -update.eta T /
            (update.observationProbability T history sample.1 - update.eta T) =
            -(update.eta T /
              (update.observationProbability T history sample.1 -
                update.eta T)) by ring,
          Real.exp_neg]
        rw [one_div]
        exact (inv_le_inv₀ (Real.exp_pos _) hxdenpos).2
          (by simpa [add_comm] using (Real.add_one_le_exp
            (update.eta T /
              (update.observationProbability T history sample.1 -
                update.eta T))))
      have hfrac :
          1 / (1 + update.eta T /
              (update.observationProbability T history sample.1 -
                update.eta T)) =
            (update.observationProbability T history sample.1 - update.eta T) /
              update.observationProbability T history sample.1 := by
        field_simp [ne_of_gt hapos, ne_of_gt hbpos]
        ring
      have hbracket :
          update.observationProbability T history sample.1 *
              Real.exp (-update.eta T /
                (update.observationProbability T history sample.1 -
                  update.eta T)) +
              (1 - update.observationProbability T history sample.1) ≤
            1 - update.eta T := by
        calc
          _ ≤ update.observationProbability T history sample.1 *
                (1 / (1 + update.eta T /
                  (update.observationProbability T history sample.1 -
                    update.eta T))) +
                (1 - update.observationProbability T history sample.1) :=
            add_le_add
              (mul_le_mul_of_nonneg_left hexpfrac hapos.le) le_rfl
          _ = 1 - update.eta T := by
            rw [hfrac]
            field_simp [ne_of_gt hapos]
            ring
      have hscaled :
          Real.exp (update.eta T) *
              (update.observationProbability T history sample.1 *
                  Real.exp (-update.eta T /
                    (update.observationProbability T history sample.1 -
                      update.eta T)) +
                (1 - update.observationProbability T history sample.1)) ≤
            1 := by
        calc
          _ ≤ Real.exp (update.eta T) * (1 - update.eta T) :=
            mul_le_mul_of_nonneg_left hbracket (Real.exp_pos _).le
          _ ≤ Real.exp (update.eta T) * Real.exp (-update.eta T) :=
            mul_le_mul_of_nonneg_left
              (Real.one_sub_le_exp_neg (update.eta T)) (Real.exp_pos _).le
          _ = 1 := by rw [← Real.exp_add]; norm_num
      rw [show Real.exp (update.eta T *
          (-1 / (update.observationProbability T history sample.1 -
            update.eta T) + 1)) =
          Real.exp (update.eta T) *
            Real.exp (-update.eta T /
              (update.observationProbability T history sample.1 -
                update.eta T)) by
        rw [← Real.exp_add]
        congr 1
        ring]
      convert hscaled using 1 <;> ring
    · have hchosen_neg :
          H i (rule.choose G (H i) sample.1) =
            strategic_label.negative :=
        (hchoose_negative_iff i).mpr hi
      have hloss : shifted_loss G rule (H i) sample = 1 := by
        simp [shifted_loss, strategic_loss, all_positive_classifier,
          rule.self_of_positive, hchosen_neg, hy]
      have hest (action : Option ι) :
          update.estimator T history
              (improper_hedge_observed_outcome G rule H action sample) i =
            if improper_hedge_observation_reveals_original H
                (improper_hedge_observed_outcome G rule H action sample) then
              1 / (update.observationProbability T history sample.1 +
                update.eta T)
            else 0 := by
        by_cases hreveal : improper_hedge_observation_reveals_original H
          (improper_hedge_observed_outcome G rule H action sample)
        · have hfeature := hfeature_of_reveal action hreveal
          have himem : i ∈ update.negativeExperts
              (improper_hedge_observed_outcome G rule H action sample).manipulatedFeature := by
            rwa [hfeature]
          rw [if_pos hreveal,
            update.estimator_positive T history
              (improper_hedge_observed_outcome G rule H action sample) i hT
              hreveal (by simpa [improper_hedge_observed_outcome] using hy)
              himem,
            hfeature]
        · rw [if_neg hreveal]
          exact update.estimator_zero T history
            (improper_hedge_observed_outcome G rule H action sample) i
            (Or.inl hreveal)
      have hreduce :
          pmf_expectation (update.actionDistribution T history) (fun action =>
            Real.exp (update.eta T *
              (update.estimator T history
                  (improper_hedge_observed_outcome G rule H action sample) i -
                shifted_loss G rule (H i) sample))) =
            pmf_expectation (update.actionDistribution T history) (fun action =>
              if improper_hedge_observation_reveals_original H
                  (improper_hedge_observed_outcome G rule H action sample) then
                Real.exp (update.eta T *
                  (1 / (update.observationProbability T history sample.1 +
                    update.eta T) - 1))
              else Real.exp (-update.eta T)) := by
        apply congrArg (pmf_expectation (update.actionDistribution T history))
        funext action
        rw [hest, hloss]
        by_cases hreveal : improper_hedge_observation_reveals_original H
          (improper_hedge_observed_outcome G rule H action sample) <;>
          simp [hreveal]
      rw [hreduce, hexpect]
      have hbpos : 0 <
          update.observationProbability T history sample.1 + update.eta T := by
        linarith
      have hxnonneg : 0 ≤
          update.eta T /
            (update.observationProbability T history sample.1 + update.eta T) :=
        div_nonneg heta.le hbpos.le
      have hxlt : update.eta T /
            (update.observationProbability T history sample.1 + update.eta T) <
          1 := by
        rw [div_lt_one hbpos]
        linarith
      have hexpfrac :
          Real.exp (update.eta T /
              (update.observationProbability T history sample.1 +
                update.eta T)) ≤
            1 / (1 - update.eta T /
              (update.observationProbability T history sample.1 +
                update.eta T)) :=
        Real.exp_bound_div_one_sub_of_interval hxnonneg hxlt
      have hfrac :
          1 / (1 - update.eta T /
              (update.observationProbability T history sample.1 +
                update.eta T)) =
            (update.observationProbability T history sample.1 + update.eta T) /
              update.observationProbability T history sample.1 := by
        field_simp [ne_of_gt hapos, ne_of_gt hbpos]
        ring
      have hbracket :
          update.observationProbability T history sample.1 *
              Real.exp (update.eta T /
                (update.observationProbability T history sample.1 +
                  update.eta T)) +
              (1 - update.observationProbability T history sample.1) ≤
            1 + update.eta T := by
        calc
          _ ≤ update.observationProbability T history sample.1 *
                (1 / (1 - update.eta T /
                  (update.observationProbability T history sample.1 +
                    update.eta T))) +
                (1 - update.observationProbability T history sample.1) :=
            add_le_add
              (mul_le_mul_of_nonneg_left hexpfrac hapos.le) le_rfl
          _ = 1 + update.eta T := by
            rw [hfrac]
            field_simp [ne_of_gt hapos]
            ring
      have hscaled :
          Real.exp (-update.eta T) *
              (update.observationProbability T history sample.1 *
                  Real.exp (update.eta T /
                    (update.observationProbability T history sample.1 +
                      update.eta T)) +
                (1 - update.observationProbability T history sample.1)) ≤
            1 := by
        calc
          _ ≤ Real.exp (-update.eta T) * (1 + update.eta T) :=
            mul_le_mul_of_nonneg_left hbracket (Real.exp_pos _).le
          _ ≤ Real.exp (-update.eta T) * Real.exp (update.eta T) :=
            mul_le_mul_of_nonneg_left
              (by simpa [add_comm] using (Real.add_one_le_exp (update.eta T)))
              (Real.exp_pos _).le
          _ = 1 := by rw [← Real.exp_add]; norm_num
      rw [show Real.exp (update.eta T *
          (1 / (update.observationProbability T history sample.1 +
            update.eta T) - 1)) =
          Real.exp (-update.eta T) *
            Real.exp (update.eta T /
              (update.observationProbability T history sample.1 +
                update.eta T)) by
        rw [← Real.exp_add]
        congr 1
        ring]
      convert hscaled using 1 <;> ring
  · have hchosen_pos :
        H i (rule.choose G (H i) sample.1) = strategic_label.positive := by
      cases hchosen : H i (rule.choose G (H i) sample.1)
      · exact False.elim (hi ((hchoose_negative_iff i).mp hchosen))
      · rfl
    have hloss : shifted_loss G rule (H i) sample = 0 := by
      simp [shifted_loss, strategic_loss, all_positive_classifier,
        rule.self_of_positive, hchosen_pos]
      ring_nf
    have hest_zero (action : Option ι) :
        update.estimator T history
          (improper_hedge_observed_outcome G rule H action sample) i = 0 := by
      by_cases ha : improper_hedge_observation_reveals_original H
        (improper_hedge_observed_outcome G rule H action sample)
      · apply update.estimator_zero
        right
        rw [hfeature_of_reveal action ha]
        exact hi
      · exact update.estimator_zero T history
          (improper_hedge_observed_outcome G rule H action sample) i (Or.inl ha)
    simp [pmf_expectation, tsum_fintype, Fintype.sum_option, hest_zero, hloss,
      update.exploration_probability, update.expert_action_probability]
    rw [← Finset.mul_sum, hpsum]
    norm_num

@[blueprint "lem:improper-hedge-interaction-finite-support"
  (statement := /-- Let $\mathcal X$ be a type and let $\iota$ be a finite
  type.  For every manipulation graph, manipulation rule, indexed classifier
  family, improper learner, adaptive adversary, horizon, and finite number of
  rounds, the support of the corresponding interaction law is finite. -/)
  (proof := /-- Induct on the number of rounds in
  \cref{def:interaction-law}.  The zero-round law is a point mass.  At the
  successor step, the induction hypothesis gives finitely many supported
  past histories.  Conditional on each such history, the next law is the
  image of a probability mass function on the finite action type
  $\{\bot\}\cup\iota$, and hence has finite support.  A finite union of these
  finite images is finite. -/)
  (title := /-- Finite support of finite-round interactions -/)
  (latexEnv := "lemma")]
lemma improper_hedge_interaction_finite_support {X : Type*} {ι : Type*}
    [Fintype ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (learner : improper_learner X ι) (adversary : adaptive_adversary X ι)
    (horizon rounds : ℕ) :
    (interaction_law G rule H learner adversary horizon rounds).support.Finite := by
  induction rounds with
  | zero => simp [interaction_law]
  | succ rounds ih =>
      rw [interaction_law, PMF.support_bind]
      apply ih.biUnion
      intro history hhistory
      rw [PMF.support_map]
      exact (Set.finite_univ.subset (Set.subset_univ _)).image _

@[blueprint "lem:improper-hedge-pmf-expectation-finite-support"
  (statement := /-- Let $p$ be a probability mass function with finite
  support.  The expectation of any real-valued function under $p$ equals the
  finite sum over the support of $p$. -/)
  (proof := /-- Expand the expectation from
  \cref{def:pmf-expectation}.  Every summand outside the support vanishes
  because its probability mass is zero, so the infinite sum reduces to the
  finite sum over the support. -/)
  (title := /-- Expectation as a sum over finite support -/)
  (latexEnv := "lemma")]
lemma improper_hedge_pmf_expectation_finite_support {Ω : Type*}
    (p : PMF Ω) (hp : p.support.Finite) (Z : Ω → ℝ) :
    pmf_expectation p Z = ∑ ω ∈ hp.toFinset, (p ω).toReal * Z ω := by
  unfold pmf_expectation
  apply tsum_eq_sum
  intro ω hω
  have hnot : ω ∉ p.support := by simpa using hω
  have hzero : p ω = 0 := by simpa [PMF.support, Function.mem_support] using hnot
  simp [hzero]

@[blueprint "lem:improper-hedge-pmf-expectation-bind"
  (statement := /-- Let $p$ be a probability mass function with finite
  support and let $q_\omega$ be finitely supported conditional probability
  mass functions for every $\omega$ in that support.  Then expectation under
  the bound law equals the outer expectation of the conditional
  expectations. -/)
  (proof := /-- Expand both expectations using
  \cref{def:pmf-expectation} and expand the mass of a bound probability mass
  function.  The hypotheses reduce the outer law and every relevant
  conditional law to finite sums.  Convert the finite extended-real sum to
  real numbers and interchange the two finite sums. -/)
  (title := /-- Tower identity for finitely supported PMFs -/)
  (latexEnv := "lemma")]
lemma improper_hedge_pmf_expectation_bind {Ω Λ : Type*}
    (p : PMF Ω) (q : Ω → PMF Λ)
    (hp : p.support.Finite)
    (hq : ∀ ω ∈ p.support, (q ω).support.Finite)
    (Z : Λ → ℝ) :
    pmf_expectation (p.bind q) Z =
      pmf_expectation p (fun ω => pmf_expectation (q ω) Z) := by
  let s := hp.toFinset
  have hp_zero (ω : Ω) (hω : ω ∉ s) : p ω = 0 := by
    have hnot : ω ∉ p.support := by simpa [s] using hω
    simpa [PMF.support, Function.mem_support] using hnot
  have hinner (a : Λ) :
      (∑' ω, (p ω).toReal * (q ω a).toReal) =
        ∑ ω ∈ s, (p ω).toReal * (q ω a).toReal := by
    apply tsum_eq_sum
    intro ω hω
    simp [hp_zero ω hω]
  have hq_summable (ω : Ω) (hω : ω ∈ s) :
      Summable (fun a => (q ω a).toReal * Z a) := by
    apply summable_of_hasFiniteSupport
    apply (hq ω (by simpa [s] using hω)).subset
    intro a ha
    simp only [Function.mem_support] at ha ⊢
    intro hzero
    simp [hzero] at ha
  have hsummable (ω : Ω) (hω : ω ∈ s) :
      Summable (fun a => (p ω).toReal * (q ω a).toReal * Z a) := by
    simpa [mul_assoc] using (hq_summable ω hω).mul_left (p ω).toReal
  have houter (F : Ω → ℝ) :
      (∑' ω, (p ω).toReal * F ω) =
        ∑ ω ∈ s, (p ω).toReal * F ω := by
    apply tsum_eq_sum
    intro ω hω
    simp [hp_zero ω hω]
  unfold pmf_expectation
  simp_rw [PMF.bind_apply]
  have htoReal (a : Λ) :
      (∑' ω, p ω * q ω a).toReal =
        ∑' ω, (p ω).toReal * (q ω a).toReal := by
    rw [ENNReal.tsum_toReal_eq]
    · congr 1
      funext ω
      exact ENNReal.toReal_mul
    · intro ω
      exact ENNReal.mul_ne_top (p.apply_ne_top ω) ((q ω).apply_ne_top a)
  simp_rw [htoReal, hinner, Finset.sum_mul]
  rw [Summable.tsum_finsetSum]
  · rw [houter]
    apply Finset.sum_congr rfl
    intro ω hω
    calc
      (∑' a, (p ω).toReal * (q ω a).toReal * Z a) =
          ∑' a, (p ω).toReal * ((q ω a).toReal * Z a) := by
            apply tsum_congr
            intro a
            ring
      _ = (p ω).toReal * ∑' a, (q ω a).toReal * Z a :=
        (hq_summable ω hω).tsum_mul_left (p ω).toReal
  · intro ω hω
    exact hsummable ω hω

@[blueprint "lem:improper-hedge-pmf-expectation-map"
  (statement := /-- Let $p$ be a probability mass function on a finite type.
  For every map $f$ and real-valued function $Z$, the expectation of $Z$
  under the pushforward of $p$ equals the expectation of $Z\circ f$ under
  $p$. -/)
  (proof := /-- Express the pushforward as a bind against point masses and
  apply \cref{lem:improper-hedge-pmf-expectation-bind}.  The support of $p$
  is finite because its domain is finite, each point mass has singleton
  support, and expectation under a point mass is evaluation. -/)
  (title := /-- Expectation under a finite PMF pushforward -/)
  (latexEnv := "lemma")]
lemma improper_hedge_pmf_expectation_map {Ω Λ : Type*} [Fintype Ω]
    (p : PMF Ω) (f : Ω → Λ) (Z : Λ → ℝ) :
    pmf_expectation (PMF.map f p) Z = pmf_expectation p (fun ω => Z (f ω)) := by
  rw [show PMF.map f p = p.bind (fun ω => PMF.pure (f ω)) by rfl]
  rw [improper_hedge_pmf_expectation_bind]
  · apply congrArg (pmf_expectation p)
    funext ω
    unfold pmf_expectation
    calc
      (∑' b, ((PMF.pure (f ω)) b).toReal * Z b) =
          ((PMF.pure (f ω)) (f ω)).toReal * Z (f ω) := by
            apply tsum_eq_single (f ω)
            intro b hb
            simp [PMF.pure_apply, hb]
      _ = Z (f ω) := by simp [PMF.pure_apply]
  · exact Set.finite_univ.subset (Set.subset_univ _)
  · intro ω hω
    simp

@[blueprint "lem:improper-hedge-pmf-expectation-mono"
  (statement := /-- Let $p$ be a finitely supported probability mass
  function.  If $F(\omega)\le G(\omega)$ for every outcome, then
  $\mathbb E_p[F]\le\mathbb E_p[G]$. -/)
  (proof := /-- Rewrite both expectations as finite sums using
  \cref{lem:improper-hedge-pmf-expectation-finite-support}.  Every probability
  mass is nonnegative, so the pointwise inequality remains valid after
  multiplication and finite summation. -/)
  (title := /-- Monotonicity of finite-support expectation -/)
  (latexEnv := "lemma")]
lemma improper_hedge_pmf_expectation_mono {Ω : Type*}
    (p : PMF Ω) (hp : p.support.Finite) (F K : Ω → ℝ)
    (hFK : ∀ ω, F ω ≤ K ω) :
    pmf_expectation p F ≤ pmf_expectation p K := by
  rw [improper_hedge_pmf_expectation_finite_support p hp F,
    improper_hedge_pmf_expectation_finite_support p hp K]
  apply Finset.sum_le_sum
  intro ω hω
  exact mul_le_mul_of_nonneg_left (hFK ω) ENNReal.toReal_nonneg

@[blueprint "lem:improper-hedge-estimated-cumulative-loss-append"
  (statement := /-- For every visible history $s$, next observed round $r$,
  and expert $i$, the cumulative concrete estimate on $s$ followed by $r$
  equals the cumulative estimate on $s$ plus the estimator evaluated at the
  past $s$ and round $r$. -/)
  (proof := /-- Generalize to an arbitrary visible past preceding $s$ and
  induct on $s$ using the recursive definition of cumulative estimated loss
  in \cref{def:improper-hedge-estimated-cumulative-loss-from}.  The empty case
  is the defining equation.  In the successor case, apply the induction
  hypothesis after extending the past by the head round and reassociate list
  concatenation. -/)
  (title := /-- Estimated cumulative loss after one round -/)
  (latexEnv := "lemma")]
lemma improper_hedge_estimated_cumulative_loss_append {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {G : Digraph X} {rule : manipulation_rule X} {H : ι → classifier X}
    (update : improper_hedge_update G rule H) (T : ℕ)
    (history : List (observed_round X ι)) (round : observed_round X ι) (i : ι) :
    improper_hedge_estimated_cumulative_loss update T (history ++ [round]) i =
      improper_hedge_estimated_cumulative_loss update T history i +
        update.estimator T history round i := by
  unfold improper_hedge_estimated_cumulative_loss
  have haux (past future : List (observed_round X ι)) :
      improper_hedge_estimated_cumulative_loss_from update T past
          (future ++ [round]) i =
        improper_hedge_estimated_cumulative_loss_from update T past future i +
          update.estimator T (past ++ future) round i := by
    induction future generalizing past with
    | nil => simp [improper_hedge_estimated_cumulative_loss_from]
    | cons head tail ih =>
        simp only [List.cons_append,
          improper_hedge_estimated_cumulative_loss_from]
        rw [ih (past ++ [head])]
        simp [List.append_assoc, add_assoc]
  simpa using haux [] history

@[blueprint "lem:improper-hedge-cumulative-exponential-moment"
  (statement := /-- Fix a regular-regime horizon, an adaptive adversary, and
  an expert $i$.  After every finite number of rounds, the expectation under
  the concrete Improper-Hedge interaction law of
  $\exp(\eta_T(\widehat L(i)-L(i)))$ is at most one. -/)
  (proof := /-- Induct on the number of rounds.  For zero rounds, reduce the
  expectation to its singleton support with
  \cref{lem:improper-hedge-pmf-expectation-finite-support}; the exponential is
  one.  For a successor round, use
  \cref{lem:improper-hedge-interaction-finite-support,
  lem:improper-hedge-pmf-expectation-bind,
  lem:improper-hedge-pmf-expectation-map} to condition on the past history and
  then on the finite next-action law.  By
  \cref{lem:improper-hedge-estimated-cumulative-loss-append}, the new
  exponential factors into the past exponential and the exponential of the
  one-round estimation error.  The conditional expectation of the latter is
  at most one by \cref{lem:improper-hedge-exponential-moment}.  Monotonicity
  from \cref{lem:improper-hedge-pmf-expectation-mono} and the induction
  hypothesis complete the step. -/)
  (title := /-- Cumulative exponential-moment bound -/)
  (latexEnv := "lemma")]
lemma improper_hedge_cumulative_exponential_moment {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (update : improper_hedge_update G rule H) (T : ℕ)
    (hT : source_parameter_regime (ι := ι) T)
    (adversary : adaptive_adversary X ι) (rounds : ℕ) (i : ι) :
    pmf_expectation
        (interaction_law G rule H (improper_hedge_learner update) adversary T rounds)
        (fun history => Real.exp (update.eta T *
          (improper_hedge_estimated_cumulative_loss update T
              (observed_history history) i -
            shifted_comparator_cumulative_loss G rule H history i))) ≤ 1 := by
  classical
  induction rounds with
  | zero =>
      rw [improper_hedge_pmf_expectation_finite_support _
        (improper_hedge_interaction_finite_support G rule H
          (improper_hedge_learner update) adversary T 0)]
      simp [interaction_law, improper_hedge_estimated_cumulative_loss,
        improper_hedge_estimated_cumulative_loss_from,
        shifted_comparator_cumulative_loss, observed_history]
  | succ rounds ih =>
      let learner := improper_hedge_learner update
      let P := interaction_law G rule H learner adversary T rounds
      let Q : List (full_round X ι) → PMF (List (full_round X ι)) := fun history =>
        PMF.map
          (fun action =>
            extend_transcript G rule H learner adversary T history action)
          (update.actionDistribution T (observed_history history))
      let M : List (full_round X ι) → ℝ := fun history =>
        Real.exp (update.eta T *
          (improper_hedge_estimated_cumulative_loss update T
              (observed_history history) i -
            shifted_comparator_cumulative_loss G rule H history i))
      change pmf_expectation (P.bind Q) M ≤ 1
      have hP : P.support.Finite :=
        improper_hedge_interaction_finite_support G rule H learner adversary T rounds
      have hQ (history : List (full_round X ι)) (hhistory : history ∈ P.support) :
          (Q history).support.Finite := by
        dsimp [Q]
        rw [PMF.support_map]
        exact (Set.finite_univ.subset (Set.subset_univ _)).image _
      rw [improper_hedge_pmf_expectation_bind P Q hP hQ M]
      have hconditional (history : List (full_round X ι)) :
          pmf_expectation (Q history) M ≤ M history := by
        let sample := adversary.choose T (public_history H history)
          (PMF.map (action_classifier H)
            (update.actionDistribution T (observed_history history)))
        have hstep (action : Option ι) :
            M (extend_transcript G rule H learner adversary T history action) =
              M history * Real.exp (update.eta T *
                (update.estimator T (observed_history history)
                    (improper_hedge_observed_outcome G rule H action sample) i -
                  shifted_loss G rule (H i) sample)) := by
          dsimp [M]
          have hobs :
              observed_history
                  (extend_transcript G rule H learner adversary T history action) =
                observed_history history ++
                  [improper_hedge_observed_outcome G rule H action sample] := by
            simp [extend_transcript, learner, improper_hedge_learner, sample,
              observed_history, improper_hedge_observed_outcome]
          rw [hobs, improper_hedge_estimated_cumulative_loss_append]
          simp [extend_transcript, learner, improper_hedge_learner, sample,
            shifted_comparator_cumulative_loss]
          rw [← Real.exp_add]
          congr 1
          ring
        rw [show Q history = PMF.map
            (fun action =>
              extend_transcript G rule H learner adversary T history action)
            (update.actionDistribution T (observed_history history)) by rfl,
          improper_hedge_pmf_expectation_map]
        simp_rw [hstep]
        rw [show pmf_expectation (update.actionDistribution T (observed_history history))
            (fun action => M history * Real.exp (update.eta T *
              (update.estimator T (observed_history history)
                  (improper_hedge_observed_outcome G rule H action sample) i -
                shifted_loss G rule (H i) sample))) =
              M history * pmf_expectation
                (update.actionDistribution T (observed_history history))
                (fun action => Real.exp (update.eta T *
                  (update.estimator T (observed_history history)
                      (improper_hedge_observed_outcome G rule H action sample) i -
                    shifted_loss G rule (H i) sample))) by
              simp only [pmf_expectation, tsum_fintype, Fintype.sum_option]
              rw [mul_add, Finset.mul_sum]
              congr 1
              · ring
              · apply Finset.sum_congr rfl
                intro j hj
                ring]
        exact mul_le_of_le_one_right (Real.exp_nonneg _)
          (improper_hedge_exponential_moment update T hT
            (observed_history history) sample i)
      calc
        pmf_expectation P (fun history => pmf_expectation (Q history) M) ≤
            pmf_expectation P M :=
          improper_hedge_pmf_expectation_mono P hP _ _ hconditional
        _ ≤ 1 := ih

@[blueprint "lem:improper-hedge-maximum-from-exponential-moments"
  (statement := /-- Let $p$ be a finitely supported probability mass
  function, let $\iota$ be a nonempty finite type, and let $\eta>0$.  If
  $\mathbb E_p[e^{\eta D_i}]\le1$ for every $i\in\iota$, then
  \[
    \mathbb E_p\!\left[\max_{i\in\iota}D_i\right]
      \le \frac{\log|\iota|}{\eta}.
  \] -/)
  (proof := /-- Put $n=|\iota|$ and $c=(\log n)/\eta$.  For every outcome and
  index $i$, the inequality $1+x\le e^x$ with
  $x=\eta(D_i-c)$, together with $e^{\eta c}=n$, gives
  \[
    D_i\le c+\frac{n^{-1}\sum_j e^{\eta D_j}-1}{\eta}.
  \]
  Taking the finite maximum preserves this inequality.  Apply
  \cref{lem:improper-hedge-pmf-expectation-mono}, expand expectations over the
  finite support using
  \cref{lem:improper-hedge-pmf-expectation-finite-support}, interchange the
  two finite sums, and use the assumed moment bound for every index.  The
  correction term is nonpositive, leaving $c$. -/)
  (title := /-- Expected maximum from exponential moments -/)
  (latexEnv := "lemma")]
lemma improper_hedge_maximum_from_exponential_moments {Ω ι : Type*}
    [Fintype ι] [Nonempty ι]
    (p : PMF Ω) (hp : p.support.Finite) (eta : ℝ) (heta : 0 < eta)
    (D : Ω → ι → ℝ)
    (hmoment : ∀ i, pmf_expectation p (fun ω => Real.exp (eta * D ω i)) ≤ 1) :
    pmf_expectation p (fun ω =>
        (Finset.univ : Finset ι).sup' Finset.univ_nonempty (D ω)) ≤
      Real.log (Fintype.card ι : ℝ) / eta := by
  classical
  let n : ℝ := Fintype.card ι
  let c : ℝ := Real.log n / eta
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast Fintype.card_pos
  have hetac : eta * c = Real.log n := by
    dsimp [c]
    field_simp
  have hexpc : Real.exp (eta * c) = n := by
    rw [hetac, Real.exp_log hn]
  let K : Ω → ℝ := fun ω =>
    c + ((∑ i, Real.exp (eta * D ω i)) / n - 1) / eta
  have hpoint (ω : Ω) :
      (Finset.univ : Finset ι).sup' Finset.univ_nonempty (D ω) ≤ K ω := by
    apply Finset.sup'_le
    intro i hi
    have hsingle :
        Real.exp (eta * (D ω i - c)) = Real.exp (eta * D ω i) / n := by
      rw [mul_sub, Real.exp_sub, hexpc]
    have hisum :
        Real.exp (eta * D ω i) ≤ ∑ j, Real.exp (eta * D ω j) := by
      exact Finset.single_le_sum
        (fun j (hj : j ∈ (Finset.univ : Finset ι)) =>
          Real.exp_nonneg (eta * D ω j)) (Finset.mem_univ i)
    have hdiv :
        Real.exp (eta * (D ω i - c)) ≤
          (∑ j, Real.exp (eta * D ω j)) / n := by
      rw [hsingle]
      exact div_le_div_of_nonneg_right hisum hn.le
    have htangent := Real.add_one_le_exp (eta * (D ω i - c))
    have hbasic :
        eta * (D ω i - c) ≤
          (∑ j, Real.exp (eta * D ω j)) / n - 1 := by
      linarith
    dsimp [K]
    have hdiveta := (div_le_div_iff_of_pos_right heta).2 hbasic
    calc
      D ω i = c + (eta * (D ω i - c)) / eta := by field_simp; ring
      _ ≤ c + ((∑ j, Real.exp (eta * D ω j)) / n - 1) / eta :=
        by simpa [add_comm] using add_le_add_left hdiveta c
  calc
    pmf_expectation p (fun ω =>
        (Finset.univ : Finset ι).sup' Finset.univ_nonempty (D ω)) ≤
        pmf_expectation p K :=
      improper_hedge_pmf_expectation_mono p hp _ _ hpoint
    _ ≤ c := by
      rw [improper_hedge_pmf_expectation_finite_support p hp K]
      let s := hp.toFinset
      have hp_zero (ω : Ω) (hω : ω ∉ s) : p ω = 0 := by
        have hnot : ω ∉ p.support := by simpa [s] using hω
        simpa [PMF.support, Function.mem_support] using hnot
      have hmass : (∑ ω ∈ s, (p ω).toReal) = 1 := by
        calc
          (∑ ω ∈ s, (p ω).toReal) = ∑' ω, (p ω).toReal := by
            symm
            apply tsum_eq_sum
            intro ω hω
            simp [hp_zero ω hω]
          _ = (∑' ω, p ω).toReal := by
            symm
            apply ENNReal.tsum_toReal_eq
            intro ω
            exact p.apply_ne_top ω
          _ = 1 := by simp
      have hmoment_sum :
          (∑ i, ∑ ω ∈ s, (p ω).toReal * Real.exp (eta * D ω i)) ≤ n := by
        calc
          (∑ i, ∑ ω ∈ s, (p ω).toReal * Real.exp (eta * D ω i)) =
              ∑ i, pmf_expectation p (fun ω => Real.exp (eta * D ω i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            symm
            simpa [s] using improper_hedge_pmf_expectation_finite_support p hp
              (fun ω => Real.exp (eta * D ω i))
          _ ≤ ∑ i : ι, 1 := Finset.sum_le_sum fun i hi => hmoment i
          _ = n := by simp [n]
      have hweighted :
          (∑ ω ∈ s, (p ω).toReal * ∑ i, Real.exp (eta * D ω i)) ≤ n := by
        calc
          (∑ ω ∈ s, (p ω).toReal * ∑ i, Real.exp (eta * D ω i)) =
              ∑ i, ∑ ω ∈ s, (p ω).toReal * Real.exp (eta * D ω i) := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
          _ ≤ n := hmoment_sum
      have hratio :
          (∑ ω ∈ s, (p ω).toReal * ∑ i, Real.exp (eta * D ω i)) / n ≤ 1 :=
        (div_le_one hn).2 hweighted
      have hcorrection :
          (((∑ ω ∈ s, (p ω).toReal * ∑ i, Real.exp (eta * D ω i)) / n) - 1) /
              eta ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hratio) heta.le
      change (∑ ω ∈ s, (p ω).toReal * K ω) ≤ c
      calc
        (∑ ω ∈ s, (p ω).toReal * K ω) =
            c * (∑ ω ∈ s, (p ω).toReal) +
              (((∑ ω ∈ s,
                (p ω).toReal * ∑ i, Real.exp (eta * D ω i)) / n) -
                (∑ ω ∈ s, (p ω).toReal)) / eta := by
          have hterm (ω : Ω) :
              (p ω).toReal * K ω =
                c * (p ω).toReal +
                  (((p ω).toReal * ∑ i, Real.exp (eta * D ω i)) / n -
                    (p ω).toReal) / eta := by
            dsimp [K]
            field_simp
          simp_rw [hterm, Finset.sum_add_distrib]
          rw [← Finset.mul_sum]
          congr 1
          rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_div]
        _ = c +
              (((∑ ω ∈ s,
                (p ω).toReal * ∑ i, Real.exp (eta * D ω i)) / n) - 1) /
                eta := by rw [hmass, mul_one]
        _ ≤ c := by linarith
    _ = Real.log (Fintype.card ι : ℝ) / eta := by rfl

@[blueprint "lem:improper-hedge-uniform-deviation"
  (statement := /-- Let $\mathcal X$ be a type, let $\iota$ be a nonempty
  finite type, let $G$ be a manipulation graph on $\mathcal X$ with a fixed
  manipulation rule, and let $(h_i)_{i\in\iota}$ be a family of classifiers.
  Fix an Improper-Hedge update, a horizon $T\in\mathbb N$ satisfying
  $T>0$, $|\iota|>1$, and $\log|\iota|\le T$, and an adaptive adversary.
  Under the $T$-round interaction law of the learner induced by this update,
  \[
    \mathbb E\!\left[
      \max_{i\in\iota}(\widehat L_T(i)-L_T(i))\right]
    \le \frac{\log|\iota|}{\eta_T},
  \]
  where $\widehat L_T(i)$ is the cumulative concrete loss estimate along the
  learner-visible history, $L_T(i)$ is the cumulative shifted comparator loss
  on the full history, and $\eta_T$ is the update's learning rate. -/)
  (proof := /-- The $T$-round interaction law has finite support by
  \cref{lem:improper-hedge-interaction-finite-support}.  For every expert
  $i$, \cref{lem:improper-hedge-cumulative-exponential-moment} gives
  \[
    \mathbb E\!\left[
      e^{\eta_T(\widehat L_T(i)-L_T(i))}\right]\le1.
  \]
  The learning rate is positive by the defining contract of the
  Improper-Hedge update.  Apply
  \cref{lem:improper-hedge-maximum-from-exponential-moments} to these moment
  bounds to obtain the claimed expectation of the finite maximum. -/)
  (title := /-- Uniform cumulative estimator deviation -/)
  (latexEnv := "lemma")]
lemma improper_hedge_uniform_deviation {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (update : improper_hedge_update G rule H) (T : ℕ)
    (hT : source_parameter_regime (ι := ι) T)
    (adversary : adaptive_adversary X ι) :
    pmf_expectation
        (interaction_law G rule H (improper_hedge_learner update) adversary T T)
        (fun history =>
          (Finset.univ : Finset ι).sup' Finset.univ_nonempty (fun i =>
            improper_hedge_estimated_cumulative_loss update T
                (observed_history history) i -
              shifted_comparator_cumulative_loss G rule H history i)) ≤
      Real.log (Fintype.card ι : ℝ) / update.eta T := by
  classical
  apply improper_hedge_maximum_from_exponential_moments
    (interaction_law G rule H (improper_hedge_learner update) adversary T T)
    (improper_hedge_interaction_finite_support G rule H
      (improper_hedge_learner update) adversary T T)
    (update.eta T) (update.eta_positive T)
    (fun history i =>
      improper_hedge_estimated_cumulative_loss update T
          (observed_history history) i -
        shifted_comparator_cumulative_loss G rule H history i)
  intro i
  exact improper_hedge_cumulative_exponential_moment G rule H update T hT
    adversary T i

@[blueprint "lem:improper-hedge-finite-expectation-algebra"
  (statement := /-- Let $p$ be a finitely supported probability mass
  function on a type $\Omega$.  For every $F\colon\Omega\to\mathbb R$ and
  every $c\in\mathbb R$, expectation under $p$ commutes with adding the
  constant $c$ and with negation:
  \[
    \mathbb E_p[F+c]=\mathbb E_p[F]+c,
    \qquad
    \mathbb E_p[-F]=-\mathbb E_p[F],
    \qquad
    \mathbb E_p[cF]=c\mathbb E_p[F].
  \] -/)
  (proof := /-- Rewrite each expectation as a finite support sum using
  \cref{lem:improper-hedge-pmf-expectation-finite-support}.  The sum of the
  real probability masses on that support is one, because the corresponding
  infinite sum is the total mass of the probability mass function.
  Distributivity of finite sums then proves both identities. -/)
  (title := /-- Algebra of finite-support expectations -/)
  (latexEnv := "lemma")]
lemma improper_hedge_finite_expectation_algebra {Ω : Type*}
    (p : PMF Ω) (hp : p.support.Finite) (F : Ω → ℝ) (c : ℝ) :
    pmf_expectation p (fun ω => F ω + c) = pmf_expectation p F + c ∧
      pmf_expectation p (fun ω => -F ω) = -pmf_expectation p F ∧
      pmf_expectation p (fun ω => c * F ω) = c * pmf_expectation p F := by
  have hmass : ∑ ω ∈ hp.toFinset, (p ω).toReal = 1 := by
    calc
      ∑ ω ∈ hp.toFinset, (p ω).toReal =
          ∑' ω, (p ω).toReal := by
        symm
        apply tsum_eq_sum
        intro ω hω
        have hnot : ω ∉ p.support := by simpa using hω
        have hzero : p ω = 0 := by
          simpa [PMF.support, Function.mem_support] using hnot
        simp [hzero]
      _ = (∑' ω, p ω).toReal :=
        (ENNReal.tsum_toReal_eq (fun ω => p.apply_ne_top ω)).symm
      _ = 1 := by rw [PMF.tsum_coe]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [improper_hedge_pmf_expectation_finite_support p hp,
      improper_hedge_pmf_expectation_finite_support p hp]
    calc
      ∑ ω ∈ hp.toFinset, (p ω).toReal * (F ω + c) =
          (∑ ω ∈ hp.toFinset, (p ω).toReal * F ω) +
            c * ∑ ω ∈ hp.toFinset, (p ω).toReal := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω hω
        ring
      _ = (∑ ω ∈ hp.toFinset, (p ω).toReal * F ω) + c := by
        rw [hmass]
        ring
  · rw [improper_hedge_pmf_expectation_finite_support p hp
        (fun ω => -F ω),
      improper_hedge_pmf_expectation_finite_support p hp F]
    simp_rw [mul_neg]
    rw [Finset.sum_neg_distrib]
  · calc
      pmf_expectation p (fun ω => c * F ω) =
          ∑ ω ∈ hp.toFinset, (p ω).toReal * (c * F ω) :=
        improper_hedge_pmf_expectation_finite_support p hp _
      _ =
          c * (∑ ω ∈ hp.toFinset, (p ω).toReal * F ω) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω hω
        ring
      _ = c * pmf_expectation p F := by
        rw [improper_hedge_pmf_expectation_finite_support p hp F]

@[blueprint "lem:improper-hedge-additive-interaction-bound"
  (statement := /-- Fix a finite action index type, a manipulation graph,
  tie-breaking rule, classifier family, improper learner, adaptive adversary,
  and horizon.  Let $F$ be a real functional of full transcripts with
  $F(\varnothing)=0$.  Suppose appending the action $a$ to a history $s$
  changes $F$ by $K(s,a)$, and the conditional expectation of $K(s,\cdot)$
  under the learner's announced law is at most $c$ for every $s$.  Then after
  every $r\in\mathbb N$ rounds,
  \[
    \mathbb E[F(S_r)]\le r c.
  \] -/)
  (proof := /-- Induct on $r$.  The zero-round law is a point mass at the
  empty transcript.  At the successor step, apply the tower identity
  \cref{lem:improper-hedge-pmf-expectation-bind} and the pushforward identity
  \cref{lem:improper-hedge-pmf-expectation-map}.  The inner expectation is
  at most $F(s)+c$ by the increment hypothesis and
  \cref{lem:improper-hedge-finite-expectation-algebra}.  Monotonicity from
  \cref{lem:improper-hedge-pmf-expectation-mono}, the induction hypothesis,
  and another application of the expectation algebra give the result.
  Finite support at each use follows from
  \cref{lem:improper-hedge-interaction-finite-support}. -/)
  (title := /-- Additive functional bound along an adaptive interaction -/)
  (latexEnv := "lemma")]
lemma improper_hedge_additive_interaction_bound {X : Type*} {ι : Type*}
    [Fintype ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (learner : improper_learner X ι) (adversary : adaptive_adversary X ι)
    (horizon rounds : ℕ) (F : List (full_round X ι) → ℝ)
    (K : List (full_round X ι) → Option ι → ℝ) (c : ℝ)
    (hzero : F [] = 0)
    (happend : ∀ history action,
      F (extend_transcript G rule H learner adversary horizon history action) =
        F history + K history action)
    (hstep : ∀ history,
      pmf_expectation (learner.play horizon (observed_history history))
        (K history) ≤ c) :
    pmf_expectation
        (interaction_law G rule H learner adversary horizon rounds) F ≤
      (rounds : ℝ) * c := by
  induction rounds with
  | zero =>
      simp only [interaction_law, Nat.cast_zero, zero_mul]
      change pmf_expectation (PMF.pure []) F ≤ 0
      unfold pmf_expectation
      calc
        (∑' ω, ((PMF.pure []) ω).toReal * F ω) =
            ((PMF.pure []) []).toReal * F [] := by
          apply tsum_eq_single []
          intro history hhistory
          simp [PMF.pure_apply, hhistory]
        _ = 0 := by simp [PMF.pure_apply, hzero]
        _ ≤ 0 := le_rfl
  | succ rounds ih =>
      let p :=
        interaction_law G rule H learner adversary horizon rounds
      have hp : p.support.Finite :=
        improper_hedge_interaction_finite_support G rule H learner adversary
          horizon rounds
      have haction (history : List (full_round X ι)) :
          (learner.play horizon (observed_history history)).support.Finite :=
        Set.finite_univ.subset (Set.subset_univ _)
      have hinner (history : List (full_round X ι)) :
          pmf_expectation
              (PMF.map
                (fun action =>
                  extend_transcript G rule H learner adversary horizon history
                    action)
                (learner.play horizon (observed_history history)))
              F ≤
            F history + c := by
        rw [improper_hedge_pmf_expectation_map]
        calc
          pmf_expectation (learner.play horizon (observed_history history))
              (fun action =>
                F (extend_transcript G rule H learner adversary horizon history
                  action)) =
              pmf_expectation
                (learner.play horizon (observed_history history))
                (fun action => K history action + F history) := by
            apply congrArg
            funext action
            rw [happend]
            ring
          _ =
              pmf_expectation
                  (learner.play horizon (observed_history history))
                  (K history) +
                F history :=
            (improper_hedge_finite_expectation_algebra
              (learner.play horizon (observed_history history))
              (haction history) (K history) (F history)).1
          _ ≤ c + F history := by linarith [hstep history]
          _ = F history + c := by ring
      rw [interaction_law,
        improper_hedge_pmf_expectation_bind
          p
          (fun history =>
            PMF.map
              (fun action =>
                extend_transcript G rule H learner adversary horizon history
                  action)
              (learner.play horizon (observed_history history)))
          hp]
      · calc
          pmf_expectation p
              (fun history =>
                pmf_expectation
                  (PMF.map
                    (fun action =>
                      extend_transcript G rule H learner adversary horizon
                        history action)
                    (learner.play horizon (observed_history history)))
                  F) ≤
              pmf_expectation p (fun history => F history + c) :=
            improper_hedge_pmf_expectation_mono p hp _ _
              (fun history => hinner history)
          _ = pmf_expectation p F + c :=
            (improper_hedge_finite_expectation_algebra p hp F c).1
          _ ≤ (rounds : ℝ) * c + c := by linarith [ih]
          _ = (↑(rounds + 1) : ℝ) * c := by
            push_cast
            ring
      · intro history hhistory
        rw [PMF.support_map]
        exact (haction history).image _

@[blueprint "lem:improper-hedge-update-with-zero-fallback-exists"
  (statement := /-- Let $\mathcal X$ and $\iota$ be types, with $\iota$
  finite and nonempty.  For every manipulation graph $G$ on $\mathcal X$,
  every tie-breaking manipulation rule, and every family
  $H\colon\iota\to\mathcal Y^{\mathcal X}$ of classifiers, there exists
  an Improper-Hedge update whose exploration rate is zero outside the regular
  parameter regime and whose action law there is the pushforward of its
  expert law under the inclusion $i\mapsto\operatorname{some}(i)$. -/)
  (proof := /-- Start with the update supplied by
  \cref{lem:improper-hedge-update-exists}.  Retain its learning rate,
  negative-expert sets, weights, expert distributions, and estimator.  In the
  regular regime retain its exploration rate, action law, and observation
  probability.  Outside that regime set the exploration rate to zero, push
  the expert law forward under $i\mapsto\operatorname{some}(i)$, and define
  the observation probability to be the mass of the negative experts.  The
  pushforward assigns zero mass to $\operatorname{none}$ and preserves the
  mass of every $\operatorname{some}(i)$; hence all fields of
  \cref{def:improper-hedge-update} retain their required identities. -/)
  (title := /-- Improper-Hedge update with zero-exploration fallback -/)
  (latexEnv := "lemma")]
lemma improper_hedge_update_with_zero_fallback_exists {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X) :
    ∃ update : improper_hedge_update G rule H,
      (∀ T, ¬ source_parameter_regime (ι := ι) T → update.rho T = 0) ∧
      (∀ T history, ¬ source_parameter_regime (ι := ι) T →
        update.actionDistribution T history =
          PMF.map some (update.expertDistribution T history)) := by
  classical
  let base : improper_hedge_update G rule H :=
    Classical.choice (improper_hedge_update_exists G rule H)
  let rhoFn : ℕ → ℝ := fun T =>
    if source_parameter_regime (ι := ι) T then base.rho T else 0
  let actionFn : ℕ → List (observed_round X ι) → PMF (Option ι) :=
    fun T history =>
      if source_parameter_regime (ι := ι) T then
        base.actionDistribution T history
      else PMF.map some (base.expertDistribution T history)
  let observationFn : ℕ → List (observed_round X ι) → X → ℝ :=
    fun T history x =>
      if source_parameter_regime (ι := ι) T then
        base.observationProbability T history x
      else
        ∑ i ∈ base.negativeExperts x,
          (base.expertDistribution T history i).toReal
  have hnone (T : ℕ) (history : List (observed_round X ι))
      (hT : ¬ source_parameter_regime (ι := ι) T) :
      (actionFn T history none).toReal = 0 := by
    simp [actionFn, hT, PMF.map_apply]
  have hsome (T : ℕ) (history : List (observed_round X ι)) (i : ι)
      (hT : ¬ source_parameter_regime (ι := ι) T) :
      (actionFn T history (some i)).toReal =
        (base.expertDistribution T history i).toReal := by
    simp [actionFn, hT, PMF.map_apply]
  let update : improper_hedge_update G rule H :=
    { eta := base.eta
      rho := rhoFn
      negativeExperts := base.negativeExperts
      negative_experts_spec := base.negative_experts_spec
      weights := base.weights
      expertDistribution := base.expertDistribution
      actionDistribution := actionFn
      observationProbability := observationFn
      estimator := base.estimator
      eta_formula := base.eta_formula
      rho_formula := by
        intro T hT
        simp [rhoFn, hT, base.rho_formula T hT]
      eta_positive := base.eta_positive
      rho_nonnegative := by
        intro T
        by_cases hT : source_parameter_regime (ι := ι) T
        · simpa [rhoFn, hT] using base.rho_nonnegative T
        · simp [rhoFn, hT]
      rho_at_most_one := by
        intro T
        by_cases hT : source_parameter_regime (ι := ι) T
        · simpa [rhoFn, hT] using base.rho_at_most_one T
        · simp [rhoFn, hT]
      weight_initial := base.weight_initial
      weight_positive := base.weight_positive
      weight_update := base.weight_update
      expert_distribution_formula := base.expert_distribution_formula
      exploration_probability := by
        intro T history
        by_cases hT : source_parameter_regime (ι := ι) T
        · simpa [actionFn, rhoFn, hT] using
            base.exploration_probability T history
        · simpa [rhoFn, hT] using hnone T history hT
      expert_action_probability := by
        intro T history i
        by_cases hT : source_parameter_regime (ι := ι) T
        · simpa [actionFn, rhoFn, hT] using
            base.expert_action_probability T history i
        · simpa [rhoFn, hT] using hsome T history i hT
      observation_probability_formula := by
        intro T history x
        by_cases hT : source_parameter_regime (ι := ι) T
        · simpa [observationFn, rhoFn, hT] using
            base.observation_probability_formula T history x
        · simp [observationFn, rhoFn, hT]
      estimator_positive := by
        intro T history round i hT hreveal hlabel hi
        simpa [observationFn, hT] using
          base.estimator_positive T history round i hT hreveal hlabel hi
      estimator_negative := by
        intro T history round i hT hreveal hlabel hi
        simpa [observationFn, hT] using
          base.estimator_negative T history round i hT hreveal hlabel hi
      estimator_zero := base.estimator_zero }
  refine ⟨update, ?_, ?_⟩
  · intro T hT
    simp [update, rhoFn, hT]
  · intro T history hT
    simp [update, actionFn, hT]

@[blueprint "lem:improper-hedge-expert-mixture-abs-le-one"
  (statement := /-- For every Improper-Hedge update, horizon, observed
  history, and labeled example, the expert-law average of the shifted losses
  lies in $[-1,1]$. -/)
  (proof := /-- The real masses of the update's expert probability mass
  function are nonnegative and sum to one.  Multiply the two inequalities
  $-1\le d_G(H_i,(x,y))\le1$ from
  \cref{lem:shifted-loss-abs-le-one} by these masses and sum over the finite
  expert class. -/)
  (title := /-- Bounded shifted loss of the expert mixture -/)
  (latexEnv := "lemma")]
lemma improper_hedge_expert_mixture_abs_le_one {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {G : Digraph X} {rule : manipulation_rule X} {H : ι → classifier X}
    (update : improper_hedge_update G rule H) (T : ℕ)
    (history : List (observed_round X ι)) (sample : X × strategic_label) :
    |∑ i, (update.expertDistribution T history i).toReal *
        shifted_loss G rule (H i) sample| ≤ 1 := by
  have hmass :
      ∑ i, (update.expertDistribution T history i).toReal = 1 := by
    calc
      ∑ i, (update.expertDistribution T history i).toReal =
          ∑' i, (update.expertDistribution T history i).toReal :=
        (tsum_fintype _).symm
      _ = (∑' i, update.expertDistribution T history i).toReal :=
        (ENNReal.tsum_toReal_eq
          (fun i => (update.expertDistribution T history).apply_ne_top i)).symm
      _ = 1 := by rw [PMF.tsum_coe]; norm_num
  rw [abs_le]
  constructor
  · calc
      (-1 : ℝ) =
          ∑ i, (update.expertDistribution T history i).toReal * (-1) := by
        rw [← Finset.sum_mul, hmass]
        ring
      _ ≤ ∑ i, (update.expertDistribution T history i).toReal *
          shifted_loss G rule (H i) sample := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left
          (abs_le.mp (shifted_loss_abs_le_one G rule (H i) sample)).1
          ENNReal.toReal_nonneg
  · calc
      ∑ i, (update.expertDistribution T history i).toReal *
          shifted_loss G rule (H i) sample ≤
          ∑ i, (update.expertDistribution T history i).toReal * 1 := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left
          (abs_le.mp (shifted_loss_abs_le_one G rule (H i) sample)).2
          ENNReal.toReal_nonneg
      _ = 1 := by rw [← Finset.sum_mul, hmass]; ring

@[blueprint "lem:improper-hedge-path-append-identities"
  (statement := /-- Fix an Improper-Hedge update and a horizon.  Appending
  one observed round to a visible history adds its current estimated mixture
  loss and estimated square mass to the corresponding cumulative quantities.
  Appending one full round to a full transcript adds its current true expert
  mixture loss to the true cumulative mixture loss. -/)
  (proof := /-- For each identity, unfold the cumulative quantity into its
  version with an explicit visible past from
  \cref{def:improper-hedge-estimated-bar-loss-from,
  def:improper-hedge-estimated-square-mass-from,
  def:improper-hedge-bar-cumulative-loss-from}.  Induct on the existing
  history, apply the corresponding recursive defining equation at its head,
  and reassociate list concatenation when applying the induction
  hypothesis. -/)
  (title := /-- One-round append identities for pathwise quantities -/)
  (latexEnv := "lemma")]
lemma improper_hedge_path_append_identities {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {G : Digraph X} {rule : manipulation_rule X} {H : ι → classifier X}
    (update : improper_hedge_update G rule H) (T : ℕ)
    (observed : List (observed_round X ι)) (nextObserved : observed_round X ι)
    (full : List (full_round X ι)) (nextFull : full_round X ι) :
    improper_hedge_estimated_bar_loss update T (observed ++ [nextObserved]) =
        improper_hedge_estimated_bar_loss update T observed +
          ∑ i, (update.expertDistribution T observed i).toReal *
            update.estimator T observed nextObserved i ∧
    improper_hedge_estimated_square_mass update T
          (observed ++ [nextObserved]) =
        improper_hedge_estimated_square_mass update T observed +
          ∑ i, (update.expertDistribution T observed i).toReal *
            (update.estimator T observed nextObserved i) ^ 2 ∧
    improper_hedge_bar_cumulative_loss update T (full ++ [nextFull]) =
        improper_hedge_bar_cumulative_loss update T full +
          ∑ i, (update.expertDistribution T (observed_history full) i).toReal *
            shifted_loss G rule (H i)
              (nextFull.originalFeature, nextFull.label) := by
  have hbarAux (past future : List (observed_round X ι)) :
      improper_hedge_estimated_bar_loss_from update T past
          (future ++ [nextObserved]) =
        improper_hedge_estimated_bar_loss_from update T past future +
          ∑ i, (update.expertDistribution T (past ++ future) i).toReal *
            update.estimator T (past ++ future) nextObserved i := by
    induction future generalizing past with
    | nil => simp [improper_hedge_estimated_bar_loss_from]
    | cons head tail ih =>
        simp only [List.cons_append, improper_hedge_estimated_bar_loss_from]
        rw [ih (past ++ [head])]
        simp [List.append_assoc, add_assoc]
  have hsquareAux (past future : List (observed_round X ι)) :
      improper_hedge_estimated_square_mass_from update T past
          (future ++ [nextObserved]) =
        improper_hedge_estimated_square_mass_from update T past future +
          ∑ i, (update.expertDistribution T (past ++ future) i).toReal *
            (update.estimator T (past ++ future) nextObserved i) ^ 2 := by
    induction future generalizing past with
    | nil => simp [improper_hedge_estimated_square_mass_from]
    | cons head tail ih =>
        simp only [List.cons_append, improper_hedge_estimated_square_mass_from]
        rw [ih (past ++ [head])]
        simp [List.append_assoc, add_assoc]
  have htrueAux (past : List (observed_round X ι))
      (future : List (full_round X ι)) :
      improper_hedge_bar_cumulative_loss_from update T past
          (future ++ [nextFull]) =
        improper_hedge_bar_cumulative_loss_from update T past future +
          ∑ i,
            (update.expertDistribution T
              (past ++ observed_history future) i).toReal *
              shifted_loss G rule (H i)
                (nextFull.originalFeature, nextFull.label) := by
    induction future generalizing past with
    | nil =>
        simp [improper_hedge_bar_cumulative_loss_from, observed_history]
    | cons head tail ih =>
        simp only [List.cons_append, improper_hedge_bar_cumulative_loss_from]
        let headObserved : observed_round X ι :=
          { action := head.action
            manipulatedFeature := head.manipulatedFeature
            label := head.label }
        calc
          (∑ i, (update.expertDistribution T past i).toReal *
                shifted_loss G rule (H i)
                  (head.originalFeature, head.label)) +
              improper_hedge_bar_cumulative_loss_from update T
                (past ++ [headObserved]) (tail ++ [nextFull]) =
            (∑ i, (update.expertDistribution T past i).toReal *
                shifted_loss G rule (H i)
                  (head.originalFeature, head.label)) +
              (improper_hedge_bar_cumulative_loss_from update T
                  (past ++ [headObserved]) tail +
                ∑ i,
                  (update.expertDistribution T
                    ((past ++ [headObserved]) ++ observed_history tail) i).toReal *
                    shifted_loss G rule (H i)
                      (nextFull.originalFeature, nextFull.label)) := by
            rw [ih (past ++ [headObserved])]
          _ =
              (∑ i, (update.expertDistribution T past i).toReal *
                shifted_loss G rule (H i)
                  (head.originalFeature, head.label)) +
                improper_hedge_bar_cumulative_loss_from update T
                  (past ++ [headObserved]) tail +
              ∑ i,
                (update.expertDistribution T
                  (past ++ observed_history (head :: tail)) i).toReal *
                  shifted_loss G rule (H i)
                    (nextFull.originalFeature, nextFull.label) := by
            simp [headObserved, observed_history, List.append_assoc, add_assoc]
  refine ⟨?_, ?_, ?_⟩
  · unfold improper_hedge_estimated_bar_loss
    simpa using hbarAux [] observed
  · unfold improper_hedge_estimated_square_mass
    simpa using hsquareAux [] observed
  · unfold improper_hedge_bar_cumulative_loss
    simpa using htrueAux [] full

@[blueprint "lem:improper-hedge-transcript-regret-le-length"
  (statement := /-- For every full transcript, its Stackelberg regret is at
  most the real-valued length of that transcript. -/)
  (proof := /-- Each recorded learner loss is either zero or one, so induction
  bounds \cref{def:learner-cumulative-loss} by the transcript length.  By
  \cref{def:strategic-loss, def:comparator-cumulative-loss}, every comparator
  loss is a sum of nonnegative zero-one losses; hence the finite minimum in
  \cref{def:best-comparator-loss} is nonnegative.  Expanding
  \cref{def:transcript-regret} and subtracting this minimum proves the claim. -/)
  (title := /-- Crude regret bound by transcript length -/)
  (latexEnv := "lemma")]
lemma improper_hedge_transcript_regret_le_length {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (history : List (full_round X ι)) :
    transcript_regret G rule H history ≤ (history.length : ℝ) := by
  have hlearner :
      learner_cumulative_loss H history ≤ (history.length : ℝ) := by
    induction history with
    | nil => simp [learner_cumulative_loss]
    | cons round history ih =>
        change
          (if action_classifier H round.action round.manipulatedFeature =
              round.label then 0 else 1) +
              learner_cumulative_loss H history ≤
            ((history.length + 1 : ℕ) : ℝ)
        push_cast
        split_ifs <;> linarith
  have hcomparator :
      0 ≤ best_comparator_loss G rule H history := by
    unfold best_comparator_loss
    apply Finset.le_inf'
    intro i hi
    unfold comparator_cumulative_loss
    apply List.sum_nonneg
    intro value hvalue
    simp only [List.mem_map] at hvalue
    rcases hvalue with ⟨round, hround, rfl⟩
    unfold strategic_loss
    split_ifs <;> norm_num
  unfold transcript_regret
  linarith

@[blueprint "lem:improper-hedge-deviation-path-le-maximum"
  (statement := /-- For every Improper-Hedge update, horizon, and full
  transcript, the least estimated expert loss minus the least true shifted
  expert loss is at most the maximum, over experts, of estimated loss minus
  true shifted loss. -/)
  (proof := /-- Expand the deviation term using
  \cref{def:improper-hedge-deviation-path-term}.  Choose an expert attaining
  the finite minimum of the true shifted losses from
  \cref{def:shifted-comparator-cumulative-loss}.  The minimum estimated loss
  from \cref{def:improper-hedge-estimated-cumulative-loss} is at most that
  expert's estimated loss, while its pointwise estimation error is at most
  the finite maximum of all estimation errors.  Adding these two inequalities
  gives the result. -/)
  (title := /-- Difference of minima bounded by maximal deviation -/)
  (latexEnv := "lemma")]
lemma improper_hedge_deviation_path_le_maximum {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {G : Digraph X} {rule : manipulation_rule X} {H : ι → classifier X}
    (update : improper_hedge_update G rule H) (T : ℕ)
    (history : List (full_round X ι)) :
    improper_hedge_deviation_path_term update T history ≤
      (Finset.univ : Finset ι).sup' Finset.univ_nonempty (fun i =>
        improper_hedge_estimated_cumulative_loss update T
            (observed_history history) i -
          shifted_comparator_cumulative_loss G rule H history i) := by
  obtain ⟨j, hj, hminimum⟩ :=
    Finset.exists_mem_eq_inf'
      (s := (Finset.univ : Finset ι)) Finset.univ_nonempty
      (shifted_comparator_cumulative_loss G rule H history)
  have hestimated := Finset.inf'_le
    (f := improper_hedge_estimated_cumulative_loss update T
      (observed_history history)) hj
  have hmaximum := Finset.le_sup'
    (s := (Finset.univ : Finset ι))
    (f := fun i =>
      improper_hedge_estimated_cumulative_loss update T
          (observed_history history) i -
        shifted_comparator_cumulative_loss G rule H history i)
    hj
  unfold improper_hedge_deviation_path_term
  rw [hminimum]
  linarith

@[blueprint "lem:improper-hedge-analysis-exists"
  (statement := /-- Let $\mathcal X$ and $\iota$ be types, with $\iota$
  finite and nonempty.  For every manipulation graph $G$ on $\mathcal X$,
  every tie-breaking manipulation rule, and every injective family
  $H\colon\iota\to\mathcal Y^{\mathcal X}$ of classifiers, there exist an
  improper learner and an Improper-Hedge analysis package for $G$, the rule,
  $H$, and that learner in the sense of
  \cref{def:improper-hedge-analysis}. -/)
  (proof := /-- Choose the update with zero exploration outside the regular
  regime from
  \cref{lem:improper-hedge-update-with-zero-fallback-exists}, and take its
  induced learner.  Define the five scalar fields of
  \cref{def:improper-hedge-analysis} as expectations of the corresponding
  pathwise quantities in
  \cref{def:improper-hedge-bar-cumulative-loss,
  def:improper-hedge-main-path-term, def:improper-hedge-hedge-path-term,
  def:improper-hedge-bias-path-term,
  def:improper-hedge-deviation-path-term}.  The append identities in
  \cref{lem:improper-hedge-path-append-identities}, the tower bound
  \cref{lem:improper-hedge-additive-interaction-bound}, and the finite-support
  algebra \cref{lem:improper-hedge-finite-expectation-algebra} convert all
  one-round estimates into cumulative expectation estimates.  Finite support
  is supplied by \cref{lem:improper-hedge-interaction-finite-support};
  expansions, pushforwards, and order comparisons of expectations use
  \cref{lem:improper-hedge-pmf-expectation-finite-support,
  lem:improper-hedge-pmf-expectation-map,
  lem:improper-hedge-pmf-expectation-mono}.

  For the exploration identity, the $h^+$ action contributes zero by
  \cref{lem:all-positive-shifted-loss-zero}, while the expert actions have
  conditional shifted loss
  $(1-\rho_T)\langle p_t,d_t\rangle$.  Applying the additive bound to this
  martingale difference and its negative gives
  $\mathbb E[\mathfrak R_T^{\rm shift}]=M_T-\rho_T\bar L_T$.
  The pointwise mixture estimate
  \cref{lem:improper-hedge-expert-mixture-abs-le-one}, applied to both signs,
  gives $|\bar L_T|\le T$.

  In the regular regime, choose an expert attaining the estimated minimum and
  apply \cref{lem:improper-hedge-potential}.  Summing the conditional
  second-moment estimate
  \cref{lem:improper-hedge-second-moment} gives the Hedge bound
  $\log|\iota|/\eta_T+4\eta_TT$, while summing
  \cref{lem:improper-hedge-bias} gives the bias bound $2\eta_TT$.
  The pathwise comparison
  \cref{lem:improper-hedge-deviation-path-le-maximum}, followed by
  \cref{lem:improper-hedge-uniform-deviation}, gives the deviation bound
  $\log|\iota|/\eta_T$.  The main decomposition follows by expanding the
  four pathwise terms and cancelling.

  At arbitrary horizons,
  \cref{lem:improper-hedge-transcript-regret-le-length} and monotonicity give
  strategic regret at most $T$; the identity
  \cref{lem:expected-shifted-regret-eq-expected-regret} transfers this to
  shifted regret.  If $|\iota|=1$, the zero-exploration fallback is the
  pushforward of the singleton expert law, so the sampled shifted loss equals
  the unique comparator loss and the regret is zero.  These facts fill every
  field of \cref{def:improper-hedge-analysis}. -/)
  (title := /-- Improper-Hedge analysis package -/)
  (latexEnv := "lemma")]
lemma improper_hedge_analysis_exists {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (hH : Function.Injective H) :
    ∃ learner : improper_learner X ι,
      Nonempty (improper_hedge_analysis G rule H learner) := by
  classical
  obtain ⟨update, hrhoFallback, hactionFallback⟩ :=
    improper_hedge_update_with_zero_fallback_exists G rule H
  let learner : improper_learner X ι := improper_hedge_learner update
  refine ⟨learner, ⟨?_⟩⟩
  refine {
    update := update
    eta := update.eta
    rho := update.rho
    barLoss := fun T adversary =>
      pmf_expectation
        (interaction_law G rule H learner adversary T T)
        (improper_hedge_bar_cumulative_loss update T)
    mainTerm := fun T adversary =>
      pmf_expectation
        (interaction_law G rule H learner adversary T T)
        (improper_hedge_main_path_term update T)
    hedgeTerm := fun T adversary =>
      pmf_expectation
        (interaction_law G rule H learner adversary T T)
        (improper_hedge_hedge_path_term update T)
    biasTerm := fun T adversary =>
      pmf_expectation
        (interaction_law G rule H learner adversary T T)
        (improper_hedge_bias_path_term update T)
    deviationTerm := fun T adversary =>
      pmf_expectation
        (interaction_law G rule H learner adversary T T)
        (improper_hedge_deviation_path_term update T)
    learner_eq := rfl
    eta_eq_update := rfl
    rho_eq_update := rfl
    bar_loss_formula := by intros; rfl
    main_term_formula := by intros; rfl
    hedge_term_formula := by intros; rfl
    bias_term_formula := by intros; rfl
    deviation_term_formula := by intros; rfl
    eta_formula := update.eta_formula
    rho_formula := update.rho_formula
    eta_positive := update.eta_positive
    rho_nonnegative := update.rho_nonnegative
    rho_at_most_one := update.rho_at_most_one
    exploration_identity := by
      intro T adversary
      let sampleAt : List (full_round X ι) → X × strategic_label :=
        fun history =>
          adversary.choose T (public_history H history)
            (PMF.map (action_classifier H)
              (update.actionDistribution T (observed_history history)))
      let mixture : List (full_round X ι) → ℝ :=
        fun history =>
          ∑ i, (update.expertDistribution T (observed_history history) i).toReal *
            shifted_loss G rule (H i) (sampleAt history)
      let F : List (full_round X ι) → ℝ :=
        fun history =>
          shifted_learner_cumulative_loss G rule H history -
            (1 - update.rho T) *
              improper_hedge_bar_cumulative_loss update T history
      let K : List (full_round X ι) → Option ι → ℝ :=
        fun history action =>
          shifted_loss G rule (action_classifier H action) (sampleAt history) -
            (1 - update.rho T) * mixture history
      have happend (history : List (full_round X ι)) (action : Option ι) :
          F (extend_transcript G rule H learner adversary T history action) =
            F history + K history action := by
        let nextObserved :=
          improper_hedge_observed_outcome G rule H action (sampleAt history)
        let nextFull : full_round X ι :=
          { action := action
            originalFeature := (sampleAt history).1
            manipulatedFeature := nextObserved.manipulatedFeature
            label := (sampleAt history).2 }
        have hextend :
            extend_transcript G rule H learner adversary T history action =
              history ++ [nextFull] := by
          rfl
        rw [hextend]
        have hbar :=
          (improper_hedge_path_append_identities update T
            (observed_history history) nextObserved history nextFull).2.2
        unfold F
        rw [hbar]
        simp [shifted_learner_cumulative_loss, K, mixture, nextFull]
        ring
      have hstep (history : List (full_round X ι)) :
          pmf_expectation (learner.play T (observed_history history))
              (K history) = 0 := by
        have hmass :
            ∑ i, (update.expertDistribution T
              (observed_history history) i).toReal = 1 := by
          calc
            ∑ i, (update.expertDistribution T
                (observed_history history) i).toReal =
                ∑' i, (update.expertDistribution T
                  (observed_history history) i).toReal :=
              (tsum_fintype _).symm
            _ = (∑' i, update.expertDistribution T
                (observed_history history) i).toReal :=
              (ENNReal.tsum_toReal_eq (fun i =>
                (update.expertDistribution T
                  (observed_history history)).apply_ne_top i)).symm
            _ = 1 := by rw [PMF.tsum_coe]; norm_num
        simp only [learner, improper_hedge_learner]
        unfold pmf_expectation
        rw [tsum_fintype, Fintype.sum_option]
        simp only [K]
        rw [show shifted_loss G rule (action_classifier H none)
            (sampleAt history) = 0 by
          simpa [action_classifier] using
            all_positive_shifted_loss_zero G rule (sampleAt history)]
        simp only [zero_sub, action_classifier,
          update.exploration_probability, update.expert_action_probability]
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
        have hone :
            ∑ i,
                (1 - update.rho T) *
                  (update.expertDistribution T
                    (observed_history history) i).toReal *
                  shifted_loss G rule (H i) (sampleAt history) =
              (1 - update.rho T) * mixture history := by
          simp only [mixture]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        have htwo :
            ∑ i,
                (1 - update.rho T) *
                  (update.expertDistribution T
                    (observed_history history) i).toReal *
                  ((1 - update.rho T) * mixture history) =
              (1 - update.rho T) ^ 2 * mixture history := by
          calc
            _ = ∑ i,
                (update.expertDistribution T
                  (observed_history history) i).toReal *
                  ((1 - update.rho T) ^ 2 * mixture history) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = (∑ i, (update.expertDistribution T
                    (observed_history history) i).toReal) *
                  ((1 - update.rho T) ^ 2 * mixture history) := by
              rw [Finset.sum_mul]
            _ = _ := by rw [hmass]; ring
        rw [hone, htwo]
        ring
      have hupper :=
        improper_hedge_additive_interaction_bound G rule H learner adversary
          T T F K 0
          (by simp [F, shifted_learner_cumulative_loss,
            improper_hedge_bar_cumulative_loss,
            improper_hedge_bar_cumulative_loss_from])
          happend
          (fun history => (hstep history).le)
      have hlower :=
        improper_hedge_additive_interaction_bound G rule H learner adversary
          T T (fun history => -F history)
          (fun history action => -K history action) 0
          (by simp [F, shifted_learner_cumulative_loss,
            improper_hedge_bar_cumulative_loss,
            improper_hedge_bar_cumulative_loss_from])
          (by
            intro history action
            rw [happend history action]
            ring)
          (by
            intro history
            have hfinite :
                (learner.play T (observed_history history)).support.Finite :=
              Set.finite_univ.subset (Set.subset_univ _)
            rw [(improper_hedge_finite_expectation_algebra
              (learner.play T (observed_history history)) hfinite
              (K history) 0).2.1, hstep history]
            norm_num)
      let p := interaction_law G rule H learner adversary T T
      have hp : p.support.Finite :=
        improper_hedge_interaction_finite_support G rule H learner adversary T T
      have hneg :=
        (improper_hedge_finite_expectation_algebra p hp F 0).2.1
      have hFzero : pmf_expectation p F = 0 := by
        rw [hneg] at hlower
        have hu : pmf_expectation p F ≤ 0 := by simpa [p] using hupper
        have hl : -pmf_expectation p F ≤ 0 := by simpa [p] using hlower
        linarith
      have hpath (history : List (full_round X ι)) :
          shifted_transcript_regret G rule H history =
            F history + improper_hedge_main_path_term update T history -
              update.rho T *
                improper_hedge_bar_cumulative_loss update T history := by
        unfold shifted_transcript_regret F improper_hedge_main_path_term
        ring
      have hdecomposition :
          pmf_expectation p (shifted_transcript_regret G rule H) =
            pmf_expectation p F +
              pmf_expectation p (improper_hedge_main_path_term update T) -
                update.rho T *
                  pmf_expectation p
                    (improper_hedge_bar_cumulative_loss update T) := by
        rw [improper_hedge_pmf_expectation_finite_support p hp,
          improper_hedge_pmf_expectation_finite_support p hp,
          improper_hedge_pmf_expectation_finite_support p hp,
          improper_hedge_pmf_expectation_finite_support p hp]
        calc
          ∑ history ∈ hp.toFinset,
              (p history).toReal *
                shifted_transcript_regret G rule H history =
            ∑ history ∈ hp.toFinset,
              (p history).toReal *
                (F history +
                  improper_hedge_main_path_term update T history -
                    update.rho T *
                      improper_hedge_bar_cumulative_loss update T history) := by
            apply Finset.sum_congr rfl
            intro history hhistory
            rw [hpath history]
          _ =
              (∑ history ∈ hp.toFinset,
                (p history).toReal * F history) +
                (∑ history ∈ hp.toFinset,
                  (p history).toReal *
                    improper_hedge_main_path_term update T history) -
                  update.rho T *
                    ∑ history ∈ hp.toFinset,
                      (p history).toReal *
                        improper_hedge_bar_cumulative_loss update T history := by
            calc
              ∑ history ∈ hp.toFinset,
                  (p history).toReal *
                    (F history +
                      improper_hedge_main_path_term update T history -
                        update.rho T *
                          improper_hedge_bar_cumulative_loss update T history) =
                ∑ history ∈ hp.toFinset,
                  ((p history).toReal * F history +
                    (p history).toReal *
                      improper_hedge_main_path_term update T history -
                    update.rho T *
                      ((p history).toReal *
                        improper_hedge_bar_cumulative_loss update T history)) := by
                apply Finset.sum_congr rfl
                intro history hhistory
                ring
              _ = _ := by
                rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
                  Finset.mul_sum]
      unfold expected_shifted_regret
      rw [hdecomposition, hFzero]
      ring
    main_decomposition := by
      intro T adversary
      let p := interaction_law G rule H learner adversary T T
      have hp : p.support.Finite :=
        improper_hedge_interaction_finite_support G rule H learner adversary T T
      rw [improper_hedge_pmf_expectation_finite_support p hp,
        improper_hedge_pmf_expectation_finite_support p hp,
        improper_hedge_pmf_expectation_finite_support p hp,
        improper_hedge_pmf_expectation_finite_support p hp]
      calc
        ∑ history ∈ hp.toFinset,
            (p history).toReal *
              improper_hedge_main_path_term update T history =
          ∑ history ∈ hp.toFinset,
            (p history).toReal *
              (improper_hedge_hedge_path_term update T history +
                improper_hedge_bias_path_term update T history +
                improper_hedge_deviation_path_term update T history) := by
          apply Finset.sum_congr rfl
          intro history hhistory
          congr 1
          unfold improper_hedge_main_path_term
            improper_hedge_hedge_path_term
            improper_hedge_bias_path_term
            improper_hedge_deviation_path_term
          ring
        _ =
            (∑ history ∈ hp.toFinset,
              (p history).toReal *
                improper_hedge_hedge_path_term update T history) +
            (∑ history ∈ hp.toFinset,
              (p history).toReal *
                improper_hedge_bias_path_term update T history) +
            ∑ history ∈ hp.toFinset,
              (p history).toReal *
                improper_hedge_deviation_path_term update T history := by
          simp_rw [mul_add, Finset.sum_add_distrib]
    bar_loss_abs_bound := by
      intro T adversary
      let sampleAt : List (full_round X ι) → X × strategic_label :=
        fun history =>
          adversary.choose T (public_history H history)
            (PMF.map (action_classifier H)
              (update.actionDistribution T (observed_history history)))
      let K : List (full_round X ι) → Option ι → ℝ :=
        fun history _ =>
          ∑ i, (update.expertDistribution T (observed_history history) i).toReal *
            shifted_loss G rule (H i) (sampleAt history)
      have happend (history : List (full_round X ι)) (action : Option ι) :
          improper_hedge_bar_cumulative_loss update T
              (extend_transcript G rule H learner adversary T history action) =
            improper_hedge_bar_cumulative_loss update T history +
              K history action := by
        let nextObserved :=
          improper_hedge_observed_outcome G rule H action (sampleAt history)
        let nextFull : full_round X ι :=
          { action := action
            originalFeature := (sampleAt history).1
            manipulatedFeature := nextObserved.manipulatedFeature
            label := (sampleAt history).2 }
        have hextend :
            extend_transcript G rule H learner adversary T history action =
              history ++ [nextFull] := by
          rfl
        rw [hextend]
        have hpath :=
          (improper_hedge_path_append_identities update T
            (observed_history history) nextObserved history nextFull).2.2
        rw [hpath]
      have hconstant (history : List (full_round X ι)) (value : ℝ) :
          pmf_expectation (learner.play T (observed_history history))
              (fun _ => value) = value := by
        have hfinite :
            (learner.play T (observed_history history)).support.Finite :=
          Set.finite_univ.subset (Set.subset_univ _)
        have hadd :=
          (improper_hedge_finite_expectation_algebra
            (learner.play T (observed_history history)) hfinite
            (fun _ => (0 : ℝ)) value).1
        simpa [pmf_expectation] using hadd
      have hpositive :=
        improper_hedge_additive_interaction_bound G rule H learner adversary
          T T (improper_hedge_bar_cumulative_loss update T) K 1
          (by simp [improper_hedge_bar_cumulative_loss,
            improper_hedge_bar_cumulative_loss_from])
          happend
          (by
            intro history
            rw [hconstant history (K history none)]
            exact
              (abs_le.mp
                (improper_hedge_expert_mixture_abs_le_one update T
                  (observed_history history) (sampleAt history))).2)
      have hnegative :=
        improper_hedge_additive_interaction_bound G rule H learner adversary
          T T
          (fun history =>
            -improper_hedge_bar_cumulative_loss update T history)
          (fun history action => -K history action) 1
          (by simp [improper_hedge_bar_cumulative_loss,
            improper_hedge_bar_cumulative_loss_from])
          (by
            intro history action
            rw [happend history action]
            ring)
          (by
            intro history
            rw [hconstant history (-K history none)]
            have habs :=
              improper_hedge_expert_mixture_abs_le_one update T
                (observed_history history) (sampleAt history)
            have hlower := (abs_le.mp habs).1
            simp only [K]
            linarith)
      let p := interaction_law G rule H learner adversary T T
      have hp : p.support.Finite :=
        improper_hedge_interaction_finite_support G rule H learner adversary T T
      have hnegExpectation :=
        (improper_hedge_finite_expectation_algebra p hp
          (improper_hedge_bar_cumulative_loss update T) 0).2.1
      rw [abs_le]
      constructor
      · rw [hnegExpectation] at hnegative
        norm_num at hnegative
        change (-T : ℝ) ≤
          pmf_expectation p
            (improper_hedge_bar_cumulative_loss update T)
        change -pmf_expectation p
            (improper_hedge_bar_cumulative_loss update T) ≤ (T : ℝ)
          at hnegative
        linarith
      · simpa [p] using hpositive
    deviation_term_bound := by
      intro T adversary hT
      let p := interaction_law G rule H learner adversary T T
      have hp : p.support.Finite :=
        improper_hedge_interaction_finite_support G rule H learner adversary T T
      calc
        pmf_expectation p
            (improper_hedge_deviation_path_term update T) ≤
          pmf_expectation p (fun history =>
            (Finset.univ : Finset ι).sup' Finset.univ_nonempty (fun i =>
              improper_hedge_estimated_cumulative_loss update T
                  (observed_history history) i -
                shifted_comparator_cumulative_loss G rule H history i)) :=
          improper_hedge_pmf_expectation_mono p hp _ _
            (fun history =>
              improper_hedge_deviation_path_le_maximum update T history)
        _ ≤ Real.log (Fintype.card ι : ℝ) / update.eta T := by
          simpa [p, learner] using
            improper_hedge_uniform_deviation G rule H update T hT adversary
    hedge_term_bound := by
      intro T adversary hT
      let sampleAt : List (full_round X ι) → X × strategic_label :=
        fun history =>
          adversary.choose T (public_history H history)
            (PMF.map (action_classifier H)
              (update.actionDistribution T (observed_history history)))
      let K : List (full_round X ι) → Option ι → ℝ :=
        fun history action =>
          ∑ i, (update.expertDistribution T (observed_history history) i).toReal *
            (update.estimator T (observed_history history)
              (improper_hedge_observed_outcome G rule H action
                (sampleAt history)) i) ^ 2
      have hsquare :=
        improper_hedge_additive_interaction_bound G rule H learner adversary
          T T
          (fun history =>
            improper_hedge_estimated_square_mass update T
              (observed_history history))
          K 4
          (by simp [observed_history, improper_hedge_estimated_square_mass,
            improper_hedge_estimated_square_mass_from])
          (by
            intro history action
            let nextObserved :=
              improper_hedge_observed_outcome G rule H action (sampleAt history)
            let nextFull : full_round X ι :=
              { action := action
                originalFeature := (sampleAt history).1
                manipulatedFeature := nextObserved.manipulatedFeature
                label := (sampleAt history).2 }
            have hextend :
                extend_transcript G rule H learner adversary T history action =
                  history ++ [nextFull] := by
              rfl
            rw [hextend]
            have hobserved :
                observed_history (history ++ [nextFull]) =
                  observed_history history ++ [nextObserved] := by
              simp [observed_history, nextFull, nextObserved,
                improper_hedge_observed_outcome]
            rw [hobserved]
            exact
              (improper_hedge_path_append_identities update T
                (observed_history history) nextObserved history nextFull).2.1)
          (by
            intro history
            simpa [learner, improper_hedge_learner, K] using
              improper_hedge_second_moment update T hT
                (observed_history history) (sampleAt history))
      let p := interaction_law G rule H learner adversary T T
      have hp : p.support.Finite :=
        improper_hedge_interaction_finite_support G rule H learner adversary T T
      have hpath (history : List (full_round X ι)) :
          improper_hedge_hedge_path_term update T history ≤
            Real.log (Fintype.card ι : ℝ) / update.eta T +
              update.eta T *
                improper_hedge_estimated_square_mass update T
                  (observed_history history) := by
        obtain ⟨j, hj, hminimum⟩ :=
          Finset.exists_mem_eq_inf'
            (s := (Finset.univ : Finset ι)) Finset.univ_nonempty
            (improper_hedge_estimated_cumulative_loss update T
              (observed_history history))
        unfold improper_hedge_hedge_path_term
        rw [hminimum]
        exact improper_hedge_potential update T hT
          (observed_history history) j
      have hmono :
          pmf_expectation p
              (improper_hedge_hedge_path_term update T) ≤
            pmf_expectation p (fun history =>
              Real.log (Fintype.card ι : ℝ) / update.eta T +
                update.eta T *
                  improper_hedge_estimated_square_mass update T
                    (observed_history history)) :=
        improper_hedge_pmf_expectation_mono p hp _ _ hpath
      calc
        pmf_expectation p
            (improper_hedge_hedge_path_term update T) ≤
          pmf_expectation p (fun history =>
            Real.log (Fintype.card ι : ℝ) / update.eta T +
              update.eta T *
                improper_hedge_estimated_square_mass update T
                  (observed_history history)) := hmono
        _ =
            Real.log (Fintype.card ι : ℝ) / update.eta T +
              update.eta T *
                pmf_expectation p (fun history =>
                  improper_hedge_estimated_square_mass update T
                    (observed_history history)) := by
          let square : List (full_round X ι) → ℝ :=
            fun history =>
              improper_hedge_estimated_square_mass update T
                (observed_history history)
          have hadd :=
            (improper_hedge_finite_expectation_algebra p hp
              (fun history => update.eta T * square history)
              (Real.log (Fintype.card ι : ℝ) / update.eta T)).1
          have hscale :=
            (improper_hedge_finite_expectation_algebra p hp square
              (update.eta T)).2.2
          rw [show (fun history =>
              Real.log (Fintype.card ι : ℝ) / update.eta T +
                update.eta T * square history) =
              (fun history =>
                update.eta T * square history +
                  Real.log (Fintype.card ι : ℝ) / update.eta T) by
            funext history
            ring]
          rw [hadd, hscale]
          ring
        _ ≤
            Real.log (Fintype.card ι : ℝ) / update.eta T +
              update.eta T * ((T : ℝ) * 4) := by
          have heta := (update.eta_positive T).le
          have hscaled := mul_le_mul_of_nonneg_left hsquare heta
          linarith
        _ =
            Real.log (Fintype.card ι : ℝ) / update.eta T +
              4 * update.eta T * (T : ℝ) := by ring
    bias_term_bound := by
      intro T adversary hT
      let sampleAt : List (full_round X ι) → X × strategic_label :=
        fun history =>
          adversary.choose T (public_history H history)
            (PMF.map (action_classifier H)
              (update.actionDistribution T (observed_history history)))
      let K : List (full_round X ι) → Option ι → ℝ :=
        fun history action =>
          ∑ i, (update.expertDistribution T (observed_history history) i).toReal *
            (shifted_loss G rule (H i) (sampleAt history) -
              update.estimator T (observed_history history)
                (improper_hedge_observed_outcome G rule H action
                  (sampleAt history)) i)
      have hbound :=
        improper_hedge_additive_interaction_bound G rule H learner adversary
          T T (improper_hedge_bias_path_term update T) K (2 * update.eta T)
          (by simp [improper_hedge_bias_path_term,
            observed_history,
            improper_hedge_bar_cumulative_loss,
            improper_hedge_bar_cumulative_loss_from,
            improper_hedge_estimated_bar_loss,
            improper_hedge_estimated_bar_loss_from])
          (by
            intro history action
            let nextObserved :=
              improper_hedge_observed_outcome G rule H action (sampleAt history)
            let nextFull : full_round X ι :=
              { action := action
                originalFeature := (sampleAt history).1
                manipulatedFeature := nextObserved.manipulatedFeature
                label := (sampleAt history).2 }
            have hextend :
                extend_transcript G rule H learner adversary T history action =
                  history ++ [nextFull] := by
              rfl
            have hpaths :=
              improper_hedge_path_append_identities update T
                (observed_history history) nextObserved history nextFull
            rw [hextend]
            unfold improper_hedge_bias_path_term
            have hobserved :
                observed_history (history ++ [nextFull]) =
                  observed_history history ++ [nextObserved] := by
              simp [observed_history, nextFull, nextObserved,
                improper_hedge_observed_outcome]
            rw [hobserved, hpaths.2.2, hpaths.1]
            simp only [K, nextFull, nextObserved]
            simp_rw [mul_sub]
            rw [Finset.sum_sub_distrib]
            ring)
          (by
            intro history
            have hmass :
                ∑ action,
                  (update.actionDistribution T
                    (observed_history history) action).toReal = 1 := by
              calc
                ∑ action,
                    (update.actionDistribution T
                      (observed_history history) action).toReal =
                    ∑' action,
                      (update.actionDistribution T
                        (observed_history history) action).toReal :=
                  (tsum_fintype _).symm
                _ = (∑' action,
                    update.actionDistribution T
                      (observed_history history) action).toReal :=
                  (ENNReal.tsum_toReal_eq (fun action =>
                    (update.actionDistribution T
                      (observed_history history)).apply_ne_top action)).symm
                _ = 1 := by rw [PMF.tsum_coe]; norm_num
            calc
              pmf_expectation
                  (learner.play T (observed_history history)) (K history) =
                ∑ i,
                  (update.expertDistribution T
                    (observed_history history) i).toReal *
                  (shifted_loss G rule (H i) (sampleAt history) -
                    pmf_expectation
                      (update.actionDistribution T (observed_history history))
                      (fun action =>
                        update.estimator T (observed_history history)
                          (improper_hedge_observed_outcome G rule H action
                            (sampleAt history)) i)) := by
                simp only [learner, improper_hedge_learner, K]
                unfold pmf_expectation
                rw [tsum_fintype]
                simp_rw [Finset.mul_sum, mul_sub]
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro i hi
                rw [tsum_fintype, Finset.sum_sub_distrib]
                have hconstant :
                    ∑ action,
                        (update.actionDistribution T
                          (observed_history history) action).toReal *
                          ((update.expertDistribution T
                            (observed_history history) i).toReal *
                            shifted_loss G rule (H i) (sampleAt history)) =
                      (update.expertDistribution T
                        (observed_history history) i).toReal *
                        shifted_loss G rule (H i) (sampleAt history) := by
                  rw [← Finset.sum_mul, hmass]
                  ring
                rw [hconstant]
                congr 1
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro action haction
                ring
              _ ≤ 2 * update.eta T :=
                improper_hedge_bias update T hT (observed_history history)
                  (sampleAt history))
      calc
        pmf_expectation
            (interaction_law G rule H learner adversary T T)
            (improper_hedge_bias_path_term update T) ≤
          (T : ℝ) * (2 * update.eta T) := by
            simpa [learner] using hbound
        _ = 2 * update.eta T * (T : ℝ) := by ring
    fallback_regret_bound := by
      intro T adversary
      rw [expected_shifted_regret_eq_expected_regret]
      let p := interaction_law G rule H learner adversary T T
      have hp : p.support.Finite :=
        improper_hedge_interaction_finite_support G rule H learner adversary T T
      calc
        expected_regret G rule H learner adversary T =
            pmf_expectation p (transcript_regret G rule H) := rfl
        _ ≤ pmf_expectation p (fun history => (history.length : ℝ)) :=
          improper_hedge_pmf_expectation_mono p hp _ _
            (fun history =>
              improper_hedge_transcript_regret_le_length G rule H history)
        _ ≤ (T : ℝ) := by
          have hbound :=
            improper_hedge_additive_interaction_bound G rule H learner
              adversary T T (fun history => (history.length : ℝ))
              (fun _ _ => 1) 1
              (by simp)
              (by
                intro history action
                simp [extend_transcript])
              (by
                intro history
                have hfinite :
                    (learner.play T (observed_history history)).support.Finite :=
                  Set.finite_univ.subset (Set.subset_univ _)
                have hone :=
                  (improper_hedge_finite_expectation_algebra
                    (learner.play T (observed_history history)) hfinite
                    (fun _ => (0 : ℝ)) 1).1
                simpa [pmf_expectation] using hone.le)
          simpa [p] using hbound
    singleton_regret_bound := by
      intro hcard T adversary
      obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.mp hcard
      have hnot : ¬ source_parameter_regime (ι := ι) T := by
        intro hreg
        have hlarge := hreg.2.1
        rw [hcard] at hlarge
        omega
      let sampleAt : List (full_round X ι) → X × strategic_label :=
        fun history =>
          adversary.choose T (public_history H history)
            (PMF.map (action_classifier H)
              (update.actionDistribution T (observed_history history)))
      let F : List (full_round X ι) → ℝ :=
        fun history =>
          shifted_learner_cumulative_loss G rule H history -
            shifted_comparator_cumulative_loss G rule H history i
      let K : List (full_round X ι) → Option ι → ℝ :=
        fun history action =>
          shifted_loss G rule (action_classifier H action) (sampleAt history) -
            shifted_loss G rule (H i) (sampleAt history)
      have happend (history : List (full_round X ι)) (action : Option ι) :
          F (extend_transcript G rule H learner adversary T history action) =
            F history + K history action := by
        let nextObserved :=
          improper_hedge_observed_outcome G rule H action (sampleAt history)
        let nextFull : full_round X ι :=
          { action := action
            originalFeature := (sampleAt history).1
            manipulatedFeature := nextObserved.manipulatedFeature
            label := (sampleAt history).2 }
        have hextend :
            extend_transcript G rule H learner adversary T history action =
              history ++ [nextFull] := by
          rfl
        rw [hextend]
        simp [F, K, shifted_learner_cumulative_loss,
          shifted_comparator_cumulative_loss, nextFull]
        ring
      have hstep (history : List (full_round X ι)) :
          pmf_expectation (learner.play T (observed_history history))
              (K history) = 0 := by
        change
          pmf_expectation
              (update.actionDistribution T (observed_history history))
              (K history) = 0
        rw [hactionFallback T (observed_history history) hnot,
          improper_hedge_pmf_expectation_map]
        have hzero :
            (fun j =>
              K history (some j)) = fun _ => (0 : ℝ) := by
          funext j
          simp [K, action_classifier, hi j]
        rw [hzero]
        simp [pmf_expectation]
      have hupper :=
        improper_hedge_additive_interaction_bound G rule H learner adversary
          T T F K 0
          (by simp [F, shifted_learner_cumulative_loss,
            shifted_comparator_cumulative_loss])
          happend
          (fun history => (hstep history).le)
      have hlower :=
        improper_hedge_additive_interaction_bound G rule H learner adversary
          T T (fun history => -F history)
          (fun history action => -K history action) 0
          (by simp [F, shifted_learner_cumulative_loss,
            shifted_comparator_cumulative_loss])
          (by
            intro history action
            rw [happend history action]
            ring)
          (by
            intro history
            have hfinite :
                (learner.play T (observed_history history)).support.Finite :=
              Set.finite_univ.subset (Set.subset_univ _)
            rw [(improper_hedge_finite_expectation_algebra
              (learner.play T (observed_history history)) hfinite
              (K history) 0).2.1, hstep history]
            norm_num)
      let p := interaction_law G rule H learner adversary T T
      have hp : p.support.Finite :=
        improper_hedge_interaction_finite_support G rule H learner adversary T T
      have hneg :=
        (improper_hedge_finite_expectation_algebra p hp F 0).2.1
      have hFzero : pmf_expectation p F = 0 := by
        rw [hneg] at hlower
        have hu : pmf_expectation p F ≤ 0 := by simpa [p] using hupper
        have hl : -pmf_expectation p F ≤ 0 := by simpa [p] using hlower
        linarith
      have hminimum (history : List (full_round X ι)) :
          (Finset.univ : Finset ι).inf' Finset.univ_nonempty
              (shifted_comparator_cumulative_loss G rule H history) =
            shifted_comparator_cumulative_loss G rule H history i := by
        apply le_antisymm
        · exact Finset.inf'_le
            (f := shifted_comparator_cumulative_loss G rule H history)
            (Finset.mem_univ i)
        · apply Finset.le_inf'
          intro j hj
          rw [hi j]
      have hpath :
          (shifted_transcript_regret G rule H) = F := by
        funext history
        unfold shifted_transcript_regret F
        rw [hminimum history]
      unfold expected_shifted_regret
      change pmf_expectation p (shifted_transcript_regret G rule H) ≤ 0
      rw [hpath, hFzero] }

@[blueprint "lem:improper-hedge-main-term-bound"
  (statement := /-- Let $\mathcal X$ and $\iota$ be types, with $\iota$
  finite and nonempty.  Fix a manipulation graph on $\mathcal X$, a
  tie-breaking manipulation rule, an $\iota$-indexed family of classifiers,
  an improper learner, and an Improper-Hedge analysis package for these data.
  For every horizon $T$ in the regular parameter regime and every adaptive
  adversary, the package's main shifted-loss term satisfies
  \[
    M_T\le \frac{2\log |\iota|}{\eta_T}+6\eta_T T,
  \]
  where $\eta_T$ is the learning rate recorded by the package. -/)
  (proof := /-- By the regular-regime decomposition and estimates in
  \cref{def:improper-hedge-analysis}, the main term is the sum of its Hedge,
  bias, and deviation terms.  Their recorded bounds are respectively
  $\log n/\eta+4\eta T$, $2\eta T$, and $\log n/\eta$.  Adding these three
  inequalities yields $2\log n/\eta+6\eta T$. -/)
  (title := /-- Bound for the main shifted-loss term -/)
  (latexEnv := "lemma")]
lemma improper_hedge_main_term_bound {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (learner : improper_learner X ι)
    (analysis : improper_hedge_analysis G rule H learner)
    (T : ℕ) (adversary : adaptive_adversary X ι)
    (hT : source_parameter_regime (ι := ι) T) :
    analysis.mainTerm T adversary ≤
      2 * Real.log (Fintype.card ι : ℝ) / analysis.eta T +
        6 * analysis.eta T * (T : ℝ) := by
  calc
    analysis.mainTerm T adversary =
        analysis.hedgeTerm T adversary + analysis.biasTerm T adversary +
          analysis.deviationTerm T adversary :=
      analysis.main_decomposition T adversary
    _ ≤
        (Real.log (Fintype.card ι : ℝ) / analysis.eta T +
            4 * analysis.eta T * (T : ℝ)) +
          2 * analysis.eta T * (T : ℝ) +
            Real.log (Fintype.card ι : ℝ) / analysis.eta T :=
      add_le_add
        (add_le_add
          (analysis.hedge_term_bound T adversary hT)
          (analysis.bias_term_bound T adversary hT))
        (analysis.deviation_term_bound T adversary hT)
    _ =
        2 * Real.log (Fintype.card ι : ℝ) / analysis.eta T +
          6 * analysis.eta T * (T : ℝ) := by
      ring

@[blueprint "lem:improper-hedge-exploration-cost"
  (statement := /-- Let $\iota$ be a nonempty finite index type, let $G$ be
  a manipulation graph on a feature space $\mathcal X$, fix a manipulation
  rule, and let $H\colon\iota\to\mathcal Y^{\mathcal X}$ be an indexed
  family of classifiers.  Let an improper learner and an associated
  Improper-Hedge analysis package be given.  Then, for every horizon
  $T\in\mathbb N$ and every adaptive adversary, the expected shifted regret
  is at most the package's main term $M_T$ plus $\rho_T T$. -/)
  (proof := /-- The exploration identity in
  \cref{def:improper-hedge-analysis} gives
  $\mathbb E[\mathfrak R_T^{\mathrm{shift}}]
  =M_T-\rho\bar L_T$.  Since $|\bar L_T|\le T$ and $\rho\ge0$, one has
  $-\rho\bar L_T\le\rho T$, which proves the claim. -/)
  (title := /-- Cost of the all-positive exploration mixture -/)
  (latexEnv := "lemma")]
lemma improper_hedge_exploration_cost {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (learner : improper_learner X ι)
    (analysis : improper_hedge_analysis G rule H learner)
    (T : ℕ) (adversary : adaptive_adversary X ι) :
    expected_shifted_regret G rule H learner adversary T ≤
      analysis.mainTerm T adversary + analysis.rho T * (T : ℝ) := by
  rw [analysis.exploration_identity]
  have hbar :=
    (abs_le.mp (analysis.bar_loss_abs_bound T adversary)).1
  have hmul :=
    mul_le_mul_of_nonneg_left hbar (analysis.rho_nonnegative T)
  nlinarith

@[blueprint "lem:improper-hedge-parameter-arithmetic"
  (statement := /-- Let $\iota$ be a nonempty finite type and let
  $T\in\mathbb N$.  With natural numbers coerced to real numbers and real
  division totalized by $x/0=0$, one has
  \[
    \frac{2\log |\iota|}{\frac12\sqrt{\log |\iota|/T}}
      +6\left(\frac12\sqrt{\frac{\log |\iota|}{T}}\right)T
      +\sqrt{\frac{\log |\iota|}{T}}\,T
      =8\sqrt{T\log |\iota|}.
  \] -/)
  (proof := /-- Put $L=\log |\iota|$, which is nonnegative because
  $|\iota|$ is a natural number.  Rewrite
  $\sqrt{L/T}=\sqrt L/\sqrt T$ and
  $\sqrt{TL}=\sqrt T\sqrt L$.  If $T=0$, or if $L=0$, totalized division
  makes both sides equal to zero.  Otherwise $\sqrt T$ and $\sqrt L$ are
  nonzero, so the denominators may be cleared.  The identities
  $(\sqrt T)^2=T$ and $(\sqrt L)^2=L$ then reduce the asserted equality
  to the polynomial identity $4\sqrt{TL}+3\sqrt{TL}+\sqrt{TL}
  =8\sqrt{TL}$. -/)
  (title := /-- Evaluation of the learning-rate bound -/)
  (latexEnv := "lemma")]
lemma improper_hedge_parameter_arithmetic {ι : Type*}
    [Fintype ι] [Nonempty ι] (T : ℕ) :
    2 * Real.log (Fintype.card ι : ℝ) /
          ((1 / 2 : ℝ) *
            Real.sqrt (Real.log (Fintype.card ι : ℝ) / (T : ℝ))) +
        6 *
          ((1 / 2 : ℝ) *
            Real.sqrt (Real.log (Fintype.card ι : ℝ) / (T : ℝ))) *
          (T : ℝ) +
        Real.sqrt (Real.log (Fintype.card ι : ℝ) / (T : ℝ)) * (T : ℝ) =
      8 * Real.sqrt ((T : ℝ) * Real.log (Fintype.card ι : ℝ)) := by
  have hlog : 0 ≤ Real.log (Fintype.card ι : ℝ) := Real.log_natCast_nonneg _
  rw [Real.sqrt_div hlog, Real.sqrt_mul (show 0 ≤ (T : ℝ) by positivity)]
  by_cases hT : T = 0
  · subst T
    norm_num
  have hsqrtT : Real.sqrt (T : ℝ) ≠ 0 := by positivity
  by_cases hL : Real.log (Fintype.card ι : ℝ) = 0
  · simp [hL]
  have hsqrtL : Real.sqrt (Real.log (Fintype.card ι : ℝ)) ≠ 0 := by positivity
  field_simp
  nlinarith [Real.sq_sqrt hlog, Real.sq_sqrt (show 0 ≤ (T : ℝ) by positivity)]

@[blueprint "lem:improper-hedge-short-horizon-arithmetic"
  (statement := /-- Let $\iota$ be a nonempty finite type and let
  $T\in\mathbb N$ be positive.  If
  $T<\log |\iota|$, then
  \[
    T\le 8\sqrt{T\log |\iota|}.
  \] -/)
  (proof := /-- Write $t$ for the positive real number corresponding to
  $T$ and set $L=\log |\iota|$.  The short-horizon hypothesis gives $L>t>0$,
  so $tL$ is nonnegative.  If $s=\sqrt{tL}$, then $s\ge 0$ and
  $s^2=tL>t^2$.  Consequently $s>t$, and hence
  $t\le 8s=8\sqrt{tL}$. -/)
  (title := /-- Short-horizon comparison with the target rate -/)
  (latexEnv := "lemma")]
lemma improper_hedge_short_horizon_arithmetic {ι : Type*}
    [Fintype ι] [Nonempty ι] (T : ℕ) (hT : 0 < T)
    (hshort : (T : ℝ) < Real.log (Fintype.card ι : ℝ)) :
    (T : ℝ) ≤
      8 * Real.sqrt ((T : ℝ) * Real.log (Fintype.card ι : ℝ)) := by
  have hTpos : (0 : ℝ) < (T : ℝ) := by
    exact_mod_cast hT
  have hlogpos : 0 < Real.log (Fintype.card ι : ℝ) := lt_trans hTpos hshort
  have hprod : 0 ≤ (T : ℝ) * Real.log (Fintype.card ι : ℝ) :=
    mul_nonneg hTpos.le hlogpos.le
  nlinarith [Real.sq_sqrt hprod,
    Real.sqrt_nonneg ((T : ℝ) * Real.log (Fintype.card ι : ℝ))]

@[blueprint "lem:improper-hedge-expected-regret-bound"
  (statement := /-- Let $\mathcal X$ be a feature space, let $\iota$ be a
  nonempty finite index type, let $G$ be a manipulation graph on
  $\mathcal X$, fix a manipulation rule, and let
  $H\colon\iota\to\mathcal Y^{\mathcal X}$ be an indexed family of
  classifiers.  Let an improper learner and an associated Improper-Hedge
  analysis package be given.  Then, for every horizon $T\in\mathbb N$ and
  every adaptive adversary,
  \[
    \mathbb E[\mathfrak R_T]
      \le 8\sqrt{T\log |\iota|}.
  \] -/)
  (proof := /-- By
  \cref{lem:expected-shifted-regret-eq-expected-regret}, it suffices to bound
  expected shifted regret.  Suppose first that $T$ lies in the regular regime
  of \cref{def:source-parameter-regime}.  Apply
  \cref{lem:improper-hedge-exploration-cost}, followed by
  \cref{lem:improper-hedge-main-term-bound}, to obtain
  $2\log n/\eta+6\eta T+\rho T$.  Substitute the regular-regime parameter
  formulae from \cref{def:improper-hedge-analysis}; the identity
  \cref{lem:improper-hedge-parameter-arithmetic} yields the claimed bound.

  It remains to treat the complement of the regular regime.  If $T=0$, the
  fallback bound in \cref{def:improper-hedge-analysis} is zero, as is the
  target expression.  If $|\iota|=1$, the singleton bound in the same
  analysis package gives nonpositive shifted regret, while
  $\log |\iota|=0$.  In the remaining case $T>0$ and $|\iota|>1$; failure
  of the regular-regime condition therefore gives
  $T<\log |\iota|$.  The fallback bound is at most $T$, and
  \cref{lem:improper-hedge-short-horizon-arithmetic} bounds this by
  $8\sqrt{T\log |\iota|}$. -/)
  (title := /-- Explicit Improper-Hedge regret bound -/)
  (latexEnv := "lemma")]
lemma improper_hedge_expected_regret_bound {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (learner : improper_learner X ι)
    (analysis : improper_hedge_analysis G rule H learner)
    (T : ℕ) (adversary : adaptive_adversary X ι) :
    expected_regret G rule H learner adversary T ≤
      8 * Real.sqrt ((T : ℝ) * Real.log (Fintype.card ι : ℝ)) := by
  rw [← expected_shifted_regret_eq_expected_regret G rule H learner adversary T]
  by_cases hreg : source_parameter_regime (ι := ι) T
  · calc
      expected_shifted_regret G rule H learner adversary T ≤
          analysis.mainTerm T adversary + analysis.rho T * (T : ℝ) :=
        improper_hedge_exploration_cost G rule H learner analysis T adversary
      _ ≤
          (2 * Real.log (Fintype.card ι : ℝ) / analysis.eta T +
              6 * analysis.eta T * (T : ℝ)) +
            analysis.rho T * (T : ℝ) :=
        add_le_add
          (improper_hedge_main_term_bound G rule H learner analysis T adversary hreg)
          (le_refl _)
      _ = 8 * Real.sqrt ((T : ℝ) * Real.log (Fintype.card ι : ℝ)) := by
        rw [analysis.eta_formula T hreg, analysis.rho_formula T hreg]
        exact improper_hedge_parameter_arithmetic T
  · by_cases hT : T = 0
    · subst T
      simpa using analysis.fallback_regret_bound 0 adversary
    · by_cases hcard : Fintype.card ι = 1
      · simpa [hcard] using analysis.singleton_regret_bound hcard T adversary
      · have hTpos : 0 < T := Nat.pos_of_ne_zero hT
        have hcardpos : 0 < Fintype.card ι := Fintype.card_pos
        have hcardgt : 1 < Fintype.card ι := by omega
        have hshort :
            (T : ℝ) < Real.log (Fintype.card ι : ℝ) := by
          apply lt_of_not_ge
          intro hle
          exact hreg ⟨hTpos, hcardgt, hle⟩
        exact (analysis.fallback_regret_bound T adversary).trans
          (improper_hedge_short_horizon_arithmetic T hTpos hshort)

@[blueprint "thm:improper-upper-bound"
  (statement := /-- Let $\mathcal X$ be a feature type and let $\iota$ be a
  nonempty finite index type.  For every manipulation graph $G$ on
  $\mathcal X$, every tie-breaking manipulation rule, and every injective
  family $H\colon\iota\to\mathcal Y^{\mathcal X}$ of classifiers, there exists
  an improper randomized learner such that, for every horizon $T\in\mathbb N$
  and every adaptive adversary, its expected Stackelberg regret is at most
  $8\sqrt{T\log |\iota|}$. -/)
  (proof := /-- By \cref{lem:improper-hedge-analysis-exists}, choose the
  Improper-Hedge learner and its analysis package.  For each horizon $T$ and
  each adaptive adversary, apply
  \cref{lem:improper-hedge-expected-regret-bound} to that package.  The
  resulting estimate is precisely the uniform bound required by
  \cref{def:guarantees-expected-regret-rate}, and hence proves the assertion. -/)
  (title := /-- Agnostic improper upper bound -/)
  (latexEnv := "theorem")]
theorem improper_upper_bound {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (hH : Function.Injective H) :
    ∃ learner : improper_learner X ι,
      guarantees_expected_regret_rate G rule H learner := by
  obtain ⟨learner, hanalysis⟩ :=
    improper_hedge_analysis_exists G rule H hH
  refine ⟨learner, fun T adversary ↦ ?_⟩
  exact improper_hedge_expected_regret_bound G rule H learner
    (Classical.choice hanalysis) T adversary

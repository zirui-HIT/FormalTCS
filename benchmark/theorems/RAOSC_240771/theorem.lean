import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad

inductive strategic_label where
  | negative
  | positive
  deriving DecidableEq

abbrev classifier (X : Type*) := X → strategic_label

def closed_neighborhood {X : Type*} (G : Digraph X) (x : X) : Set X :=
  {z | z = x ∨ G.Adj x z}

def best_responses {X : Type*} (G : Digraph X) (h : classifier X) (x : X) : Set X :=
  {z | z ∈ closed_neighborhood G x ∧ h z = strategic_label.positive}

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

def all_positive_classifier (X : Type*) : classifier X :=
  fun _ => strategic_label.positive

def strategic_loss {X : Type*} (G : Digraph X) (rule : manipulation_rule X)
    (h : classifier X) (sample : X × strategic_label) : ℝ :=
  if h (rule.choose G h sample.1) = sample.2 then 0 else 1

structure observed_round (X : Type*) (ι : Type*) where
  action : Option ι
  manipulatedFeature : X
  label : strategic_label

structure full_round (X : Type*) (ι : Type*) where
  action : Option ι
  originalFeature : X
  manipulatedFeature : X
  label : strategic_label

structure public_round (X : Type*) where
  playedClassifier : classifier X
  originalFeature : X
  manipulatedFeature : X
  label : strategic_label

def observed_history {X : Type*} {ι : Type*}
    (history : List (full_round X ι)) : List (observed_round X ι) :=
  history.map fun round =>
    { action := round.action
      manipulatedFeature := round.manipulatedFeature
      label := round.label }

def action_classifier {X : Type*} {ι : Type*} (H : ι → classifier X) :
    Option ι → classifier X
  | none => all_positive_classifier X
  | some i => H i

def public_history {X : Type*} {ι : Type*} (H : ι → classifier X)
    (history : List (full_round X ι)) : List (public_round X) :=
  history.map fun round =>
    { playedClassifier := action_classifier H round.action
      originalFeature := round.originalFeature
      manipulatedFeature := round.manipulatedFeature
      label := round.label }

structure improper_learner (X : Type*) (ι : Type*) where
  play : ℕ → List (observed_round X ι) → PMF (Option ι)

structure adaptive_adversary (X : Type*) (ι : Type*) where
  choose :
    ℕ → List (public_round X) → PMF (classifier X) → X × strategic_label

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

def learner_cumulative_loss {X : Type*} {ι : Type*}
    (H : ι → classifier X) (history : List (full_round X ι)) : ℝ :=
  (history.map fun round =>
    if action_classifier H round.action round.manipulatedFeature = round.label
    then (0 : ℝ) else 1).sum

def comparator_cumulative_loss {X : Type*} {ι : Type*}
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (history : List (full_round X ι)) (i : ι) : ℝ :=
  (history.map fun round =>
    strategic_loss G rule (H i) (round.originalFeature, round.label)).sum

noncomputable def best_comparator_loss {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (history : List (full_round X ι)) : ℝ :=
  (Finset.univ : Finset ι).inf' Finset.univ_nonempty
    (comparator_cumulative_loss G rule H history)

noncomputable def transcript_regret {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (history : List (full_round X ι)) : ℝ :=
  learner_cumulative_loss H history -
    best_comparator_loss G rule H history

noncomputable def pmf_expectation {Ω : Type*} (p : PMF Ω) (Z : Ω → ℝ) : ℝ :=
  ∑' ω, (p ω).toReal * Z ω

noncomputable def expected_regret {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (learner : improper_learner X ι) (adversary : adaptive_adversary X ι)
    (T : ℕ) : ℝ :=
  pmf_expectation
    (interaction_law G rule H learner adversary T T)
    (transcript_regret G rule H)

def guarantees_expected_regret_rate {X : Type*} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (learner : improper_learner X ι) : Prop :=
  ∀ (T : ℕ) (adversary : adaptive_adversary X ι),
    expected_regret G rule H learner adversary T ≤
      8 * Real.sqrt ((T : ℝ) * Real.log (Fintype.card ι : ℝ))

theorem improper_upper_bound {X : Type*} {ι : Type*} [Fintype ι] [Nonempty ι]
    (G : Digraph X) (rule : manipulation_rule X) (H : ι → classifier X)
    (hH : Function.Injective H) :
    ∃ learner : improper_learner X ι,
      guarantees_expected_regret_rate G rule H learner := by sorry

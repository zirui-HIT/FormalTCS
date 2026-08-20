import Mathlib.Data.Fintype.BigOperators
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.Topology.MetricSpace.Defs

open scoped BigOperators
open MeasureTheory

structure metric_election (Candidate Voter Point : Type*)
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point] where
  candidatePoint : Candidate → Point
  voterPoint : Voter → Point
  voterMeasure : ProbabilityMeasure Voter
  voterPoint_measurable : Measurable voterPoint
  voter_distance_integrable : ∀ c,
    Integrable (fun i => dist (voterPoint i) (candidatePoint c))
      voterMeasure
  strict_rankings : ∀ᵐ i ∂(voterMeasure : Measure Voter),
    ∀ a b, a ≠ b →
      dist (voterPoint i) (candidatePoint a) ≠
        dist (voterPoint i) (candidatePoint b)

noncomputable def social_cost {Candidate Voter Point : Type*}
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) (c : Candidate) : ℝ :=
  ∫ i, dist (E.voterPoint i) (E.candidatePoint c) ∂E.voterMeasure

noncomputable def normalized_bias {Candidate Voter Point : Type*}
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) (i : Voter)
    (a b : Candidate) : ℝ :=
  (dist (E.voterPoint i) (E.candidatePoint a) -
      dist (E.voterPoint i) (E.candidatePoint b)) /
    dist (E.candidatePoint a) (E.candidatePoint b)

noncomputable def first_bias_mass {Candidate Voter Point : Type*}
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) {k : ℕ}
    (g : Fin k → Voter) (a b : Candidate) : ℝ :=
  ∑ j, max (-normalized_bias E (g j) a b) 0

noncomputable def second_bias_mass {Candidate Voter Point : Type*}
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) {k : ℕ}
    (g : Fin k → Voter) (a b : Candidate) : ℝ :=
  ∑ j, max (normalized_bias E (g j) a b) 0

noncomputable def random_choice_group_probability {Candidate Voter Point : Type*}
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) {k : ℕ}
    (g : Fin k → Voter) (a b : Candidate) : ℝ :=
  first_bias_mass E g a b /
    (first_bias_mass E g a b + second_bias_mass E g a b)

noncomputable def random_choice_win_probability {Candidate Voter Point : Type*}
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) (k : ℕ)
    (a b : Candidate) : ℝ :=
  ∫ g, random_choice_group_probability E g a b ∂
    (ProbabilityMeasure.pi (fun _ : Fin k => E.voterMeasure) :
      Measure (Fin k → Voter))

def deliberation_dominates {Candidate Voter Point : Type*}
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) (k : ℕ)
    (a b : Candidate) : Prop :=
  (1 / 2 : ℝ) ≤ random_choice_win_probability E k a b

noncomputable def copeland_score {Candidate Voter Point : Type*}
    [Fintype Candidate] [DecidableEq Candidate]
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) (k : ℕ)
    (a : Candidate) : ℕ := by
  classical
  exact (Finset.univ.filter fun b =>
    b ≠ a ∧ deliberation_dominates E k a b).card

def tournament_covers {Candidate Voter Point : Type*}
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) (k : ℕ)
    (a b : Candidate) : Prop :=
  a ≠ b ∧ deliberation_dominates E k a b ∧
    ∀ c, deliberation_dominates E k b c →
      deliberation_dominates E k a c

def uncovered_candidate {Candidate Voter Point : Type*}
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) (k : ℕ)
    (a : Candidate) : Prop :=
  ¬ ∃ b, tournament_covers E k b a

def copeland_winner {Candidate Voter Point : Type*}
    [Fintype Candidate] [DecidableEq Candidate]
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) (k : ℕ)
    (a : Candidate) : Prop :=
  uncovered_candidate E k a ∧
    ∀ b, uncovered_candidate E k b →
      copeland_score E k b ≤ copeland_score E k a

def social_optimum {Candidate Voter Point : Type*}
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) (optimal : Candidate) : Prop :=
  ∀ c, social_cost E optimal ≤ social_cost E c

def copeland_distortion_at_most {Candidate Voter Point : Type*}
    [Fintype Candidate] [DecidableEq Candidate]
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) (k : ℕ) (D : ℝ) : Prop :=
  ∀ winner optimal,
    copeland_winner E k winner → social_optimum E optimal →
      social_cost E winner ≤ D * social_cost E optimal

theorem random_choice_copeland_small_group_distortion
    {Candidate Voter Point : Type*}
    [Fintype Candidate] [DecidableEq Candidate] [Nonempty Candidate]
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) :
    copeland_distortion_at_most E 2 3.34 ∧
      copeland_distortion_at_most E 3 2.31 ∧
      copeland_distortion_at_most E 4 1.901 := by sorry

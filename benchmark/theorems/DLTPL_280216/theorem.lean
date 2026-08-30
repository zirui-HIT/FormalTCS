import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators

abbrev boolean_cube (n : ℕ) := Fin n → Bool

abbrev boolean_restriction (n : ℕ) := Fin n → Option Bool

def satisfies_boolean_restriction {n : ℕ} (ρ : boolean_restriction n)
    (x : boolean_cube n) : Prop :=
  ∀ i b, ρ i = some b → x i = b

def coordinate_restriction {n : ℕ} (i : Fin n) (b : Bool) :
    boolean_restriction n :=
  fun j => if j = i then some b else none

def restriction_has_positive_mass {n : ℕ} (D : PMF (boolean_cube n))
    (ρ : boolean_restriction n) : Prop :=
  ∃ x ∈ {x | satisfies_boolean_restriction ρ x}, x ∈ D.support

noncomputable def conditioned_boolean_distribution {n : ℕ}
    (D : PMF (boolean_cube n)) (ρ : boolean_restriction n)
    (hρ : restriction_has_positive_mass D ρ) : PMF (boolean_cube n) :=
  D.filter {x | satisfies_boolean_restriction ρ x} hρ

def distribution_family_closed_under_restrictions {n : ℕ}
    (𝒟 : Set (PMF (boolean_cube n))) : Prop :=
  ∀ D ∈ 𝒟, ∀ ρ, ∀ hρ : restriction_has_positive_mass D ρ,
    conditioned_boolean_distribution D ρ hρ ∈ 𝒟

abbrev boolean_concept_class (n : ℕ) := Set (boolean_cube n → Bool)

abbrev boolean_labeled_sample (n m : ℕ) :=
  Fin m → (boolean_cube n × Bool)

structure learning_algorithm (n m : ℕ) where
  run : boolean_labeled_sample n m → boolean_cube n → Bool
  runningTime : boolean_labeled_sample n m → ℕ

def runs_in_time {n m : ℕ} (A : learning_algorithm n m) (t : ℕ) : Prop :=
  ∀ S, A.runningTime S ≤ t

noncomputable def population_prediction_error {n : ℕ}
    (D : PMF (boolean_cube n)) (c h : boolean_cube n → Bool) : ℝ :=
  ∑ x : boolean_cube n, (D x).toReal * if h x ≠ c x then 1 else 0

noncomputable def expected_learning_error {n m : ℕ}
    (D : PMF (boolean_cube n)) (c : boolean_cube n → Bool)
    (A : learning_algorithm n m) : ℝ :=
  ∑ S : Fin m → boolean_cube n,
    (∏ i : Fin m, (D (S i)).toReal) *
      population_prediction_error D c
        (A.run (fun i => (S i, c (S i))))

def learns_in_expected_error {n m : ℕ} (C : boolean_concept_class n)
    (D : PMF (boolean_cube n)) (A : learning_algorithm n m) (ε : ℝ) : Prop :=
  ∀ c ∈ C, expected_learning_error D c A ≤ ε

def learns_family_in_expected_error {n m : ℕ}
    (C : boolean_concept_class n) (𝒟 : Set (PMF (boolean_cube n)))
    (A : learning_algorithm n m) (ε : ℝ) : Prop :=
  ∀ D ∈ 𝒟, learns_in_expected_error C D A ε

inductive has_decision_tree_decomposition {n : ℕ}
    (𝒟 : Set (PMF (boolean_cube n))) : ℕ → PMF (boolean_cube n) → Prop
  | leaf {d : ℕ} {D : PMF (boolean_cube n)} (hD : D ∈ 𝒟) :
      has_decision_tree_decomposition 𝒟 d D
  | split {d : ℕ} {D : PMF (boolean_cube n)} (i : Fin n)
      (hbranch : ∀ b : Bool,
        ∀ hb : restriction_has_positive_mass D (coordinate_restriction i b),
          has_decision_tree_decomposition 𝒟 d
            (conditioned_boolean_distribution D (coordinate_restriction i b) hb)) :
      has_decision_tree_decomposition 𝒟 (d + 1) D

noncomputable def sample_complexity_bound (n d m m' : ℕ) (ε K : ℝ) : Prop :=
  0 < K ∧
    (m' : ℝ) ≤ K *
      (((2 : ℝ) ^ d * (m : ℝ)) / ε +
        ((2 : ℝ) ^ d * Real.log (n : ℝ)) / ε ^ 2)

noncomputable def time_complexity_bound (n d m' t t' q : ℕ)
    (ε K : ℝ) : Prop :=
  0 < K ∧
    (t' : ℝ) ≤
      K * (n : ℝ) ^ (q * d) * (m' : ℝ) * (t : ℝ) *
        Real.log (t : ℝ) / ε ^ 2

theorem distributional_lifting_for_decision_tree_decompositions
    {n d m t : ℕ} {ε : ℝ} (hεpos : 0 < ε) (hεone : ε < 1)
    (C : boolean_concept_class n) (𝒟 : Set (PMF (boolean_cube n)))
    (hclosed : distribution_family_closed_under_restrictions 𝒟)
    (A : learning_algorithm n m) (hAtime : runs_in_time A t)
    (hAlearns : learns_family_in_expected_error C 𝒟 A ε) :
    ∃ (m' t' : ℕ) (Km Kt : ℝ) (q : ℕ)
      (A' : learning_algorithm n m'),
      sample_complexity_bound n d m m' ε Km ∧
      time_complexity_bound n d m' t t' q ε Kt ∧
      runs_in_time A' t' ∧
      ∀ Dstar : PMF (boolean_cube n),
        has_decision_tree_decomposition 𝒟 d Dstar →
          learns_in_expected_error C Dstar A' ε := by sorry

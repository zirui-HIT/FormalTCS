import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory ProbabilityTheory

abbrev full_space (d : ℕ) : Type := (Fin d → ℝ) × Bool × ℝ × ℝ

abbrev observed_space (d : ℕ) : Type := (Fin d → ℝ) × Bool × ℝ

structure observational_study (d : ℕ) where
  law : Measure (full_space d)
  isProb : IsProbabilityMeasure law

instance study_law_is_probability_measure {d : ℕ} (D : observational_study d) :
    IsProbabilityMeasure D.law := D.isProb

def censoring_map (d : ℕ) : full_space d → observed_space d :=
  fun w => (w.1, w.2.1, if w.2.1 then w.2.2.2 else w.2.2.1)

noncomputable def censored_distribution {d : ℕ} (D : observational_study d) :
    Measure (observed_space d) :=
  D.law.map (censoring_map d)

noncomputable def average_treatment_effect {d : ℕ} (D : observational_study d) : ℝ :=
  ∫ w, (w.2.2.2 - w.2.2.1) ∂D.law

noncomputable def induced_propensity {d : ℕ} (D : observational_study d) (t : Bool) :
    (Fin d → ℝ) × ℝ → ℝ :=
  fun z =>
    ((condDistrib (fun w : full_space d => w.2.1)
      (fun w : full_space d => (w.1, if t then w.2.2.2 else w.2.2.1)) D.law) z {t}).toReal

noncomputable def outcome_marginal {d : ℕ} (D : observational_study d) (t : Bool) :
    Measure ((Fin d → ℝ) × ℝ) :=
  D.law.map (fun w : full_space d => (w.1, if t then w.2.2.2 else w.2.2.1))

abbrev propensity_class (d : ℕ) : Type := Set ((Fin d → ℝ) × ℝ → ℝ)

abbrev outcome_class (d : ℕ) : Type := Set (Measure ((Fin d → ℝ) × ℝ))

def finite_first_moment {d : ℕ} (P : Measure ((Fin d → ℝ) × ℝ)) : Prop :=
  Integrable (fun z : (Fin d → ℝ) × ℝ => z.2) P

def realizable {d : ℕ} (D : observational_study d)
    (Pcl : propensity_class d) (Dcl : outcome_class d) : Prop :=
  induced_propensity D false ∈ Pcl ∧ induced_propensity D true ∈ Pcl ∧
    outcome_marginal D false ∈ Dcl ∧ outcome_marginal D true ∈ Dcl ∧
    finite_first_moment (outcome_marginal D false) ∧
    finite_first_moment (outcome_marginal D true)

def compatible {d : ℕ} (Pcl : propensity_class d) (Dcl : outcome_class d)
    (t : Bool) (p : (Fin d → ℝ) × ℝ → ℝ)
    (P : Measure ((Fin d → ℝ) × ℝ)) : Prop :=
  p ∈ Pcl ∧ P ∈ Dcl ∧
    ∃ D : observational_study d,
      realizable D Pcl Dcl ∧
        outcome_marginal D t = P ∧ induced_propensity D t =ᵐ[P] p

def identifiability_condition {d : ℕ} (Pcl : propensity_class d) (Dcl : outcome_class d) :
    Prop :=
  ∀ (t : Bool) (p : (Fin d → ℝ) × ℝ → ℝ) (P : Measure ((Fin d → ℝ) × ℝ))
    (q : (Fin d → ℝ) × ℝ → ℝ) (Q : Measure ((Fin d → ℝ) × ℝ)),
    compatible Pcl Dcl t p P → compatible Pcl Dcl t q Q →
      (∫ z, z.2 ∂P) = (∫ z, z.2 ∂Q) ∨
        P.map Prod.fst ≠ Q.map Prod.fst ∨
        P.withDensity (fun z => ENNReal.ofReal (p z)) ≠
          Q.withDensity (fun z => ENNReal.ofReal (q z))

def ate_identifiable {d : ℕ} (Pcl : propensity_class d) (Dcl : outcome_class d) : Prop :=
  ∃ f : Measure (observed_space d) → ℝ,
    ∀ D : observational_study d, realizable D Pcl Dcl →
      f (censored_distribution D) = average_treatment_effect D

theorem ate_identifiable_iff_condition {d : ℕ}
    (Pcl : propensity_class d) (Dcl : outcome_class d) :
    ate_identifiable Pcl Dcl ↔ identifiability_condition Pcl Dcl := by sorry

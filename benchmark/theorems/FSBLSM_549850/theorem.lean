import Mathlib

set_option linter.all false
set_option maxHeartbeats 400000

abbrev polynomial_factor (n : ℕ) := Fin n → ℕ

def factor_support {n : ℕ} (factor : polynomial_factor n) : Finset (Fin n) :=
  Finset.univ.filter fun j => 0 < factor j

def factors_at {n : ℕ} (factors : Finset (polynomial_factor n)) (j : Fin n) :
    Finset (polynomial_factor n) :=
  factors.filter fun factor => j ∈ factor_support factor

def maximal_factors {n : ℕ} (factors : Finset (polynomial_factor n)) :
    Finset (polynomial_factor n) :=
  factors.filter fun factor =>
    ¬ ∃ larger ∈ factors,
      factor_support factor ⊆ factor_support larger ∧
        factor_support factor ≠ factor_support larger

def incident_maximal_factors {n : ℕ} (factors : Finset (polynomial_factor n)) (i : Fin n) :
    Finset (polynomial_factor n) :=
  (maximal_factors factors).filter fun factor => i ∈ factor_support factor

def interaction_order {n : ℕ} (factors : Finset (polynomial_factor n)) : ℕ :=
  factors.sup fun factor => (factor_support factor).card

def family_degree_at_most {n : ℕ} (factors : Finset (polynomial_factor n)) (d : ℕ) : Prop :=
  ∀ factor ∈ factors, (∑ j, factor j) ≤ d

def monomial_value {n : ℕ} (factor : polynomial_factor n) (x : Fin n → ℝ) : ℝ :=
  ∏ j, x j ^ factor j

def monomial_first_partial {n : ℕ} (factor : polynomial_factor n) (i : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  (factor i : ℝ) * x i ^ (factor i - 1) *
    ∏ j ∈ Finset.univ.erase i, x j ^ factor j

def monomial_second_partial {n : ℕ} (factor : polynomial_factor n) (i : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  (factor i : ℝ) * ((factor i - 1 : ℕ) : ℝ) * x i ^ (factor i - 2) *
    ∏ j ∈ Finset.univ.erase i, x j ^ factor j

def exponential_energy {n : ℕ} (factors : Finset (polynomial_factor n))
    (theta : polynomial_factor n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ factor ∈ factors, theta factor * monomial_value factor x

def energy_first_partial {n : ℕ} (factors : Finset (polynomial_factor n))
    (theta : polynomial_factor n → ℝ) (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  ∑ factor ∈ factors, theta factor * monomial_first_partial factor i x

def energy_second_partial {n : ℕ} (factors : Finset (polynomial_factor n))
    (theta : polynomial_factor n → ℝ) (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  ∑ factor ∈ factors, theta factor * monomial_second_partial factor i x

noncomputable def local_score_matching_loss {n : ℕ} (factors : Finset (polynomial_factor n))
    (theta : polynomial_factor n → ℝ) (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  energy_second_partial factors theta i x +
    (1 / 2 : ℝ) * (energy_first_partial factors theta i x) ^ 2

noncomputable def empirical_local_score_matching_loss {n M : ℕ}
    (factors : Finset (polynomial_factor n)) (theta : polynomial_factor n → ℝ) (i : Fin n)
    (observations : Fin M → (Fin n → ℝ)) : ℝ :=
  (M : ℝ)⁻¹ * ∑ m, local_score_matching_loss factors theta i (observations m)

def parameter_feasible {n : ℕ} (factors : Finset (polynomial_factor n)) (B : ℝ)
    (theta : polynomial_factor n → ℝ) : Prop :=
  ∀ j, ∑ factor ∈ factors_at factors j, |theta factor| ≤ B

def constrained_empirical_minimizer {n M : ℕ}
    (factors : Finset (polynomial_factor n)) (B : ℝ) (i : Fin n)
    (observations : Fin M → (Fin n → ℝ)) (thetaHat : polynomial_factor n → ℝ) : Prop :=
  parameter_feasible factors B thetaHat ∧
    ∀ theta, parameter_feasible factors B theta →
      empirical_local_score_matching_loss factors thetaHat i observations ≤
        empirical_local_score_matching_loss factors theta i observations

def unit_base_polynomial_exponential_family {n : ℕ}
    (factors : Finset (polynomial_factor n)) (theta : polynomial_factor n → ℝ)
    (p : MeasureTheory.Measure (Fin n → ℝ)) : Prop :=
  ∃ Z : ℝ, 0 < Z ∧
    Z = ∫ x, Real.exp (exponential_energy factors theta x) ∂MeasureTheory.volume ∧
    p = MeasureTheory.Measure.withDensity MeasureTheory.volume
      (fun x => ENNReal.ofReal (Real.exp (exponential_energy factors theta x) / Z))

def tail_decay_condition {n : ℕ} (d : ℕ) (tailRate : ℝ) (Ct : ℕ)
    (p : MeasureTheory.Measure (Fin n → ℝ)) : Prop :=
  0 < tailRate ∧ 2 ≤ d ∧
    max (Real.rpow (Real.log 2 / tailRate) (1 / ((d : ℝ) - 1))) 1 ≤ (Ct : ℝ) ∧
    (Ct : ℝ) ≤ Real.exp (n : ℝ) ∧
    ∀ s : ℝ, (Ct : ℝ) ≤ s →
      p.real {x | s < ‖x‖} ≤ Real.exp (-tailRate * s ^ (d - 1))

def iid_samples {n M : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (mu : MeasureTheory.Measure Ω) (p : MeasureTheory.Measure (Fin n → ℝ))
    (samples : Fin M → Ω → (Fin n → ℝ)) : Prop :=
  ProbabilityTheory.iIndepFun samples mu ∧
    ∀ m, ProbabilityTheory.IdentDistrib (samples m) id mu p

def family_structure_sample_scale (A0 : ℝ) (C d : ℕ) (B : ℝ) (Ct w : ℕ)
    (Mstar : ℝ) : Prop :=
  1 < A0 ∧ 0 < C ∧ 1 ≤ Mstar ∧
    Mstar ≤ max A0 ((max (1 + (1 / 1024 : ℝ))
      ((d : ℝ) * B * (Ct : ℝ) ^ d)) ^ (C * d ^ 2 * w))

def family_structure_recovery_at_scale {n : ℕ} (d : ℕ)
    (factors : Finset (polynomial_factor n)) (thetaStar : polynomial_factor n → ℝ)
    (i : Fin n) (B : ℝ) (Ct : ℕ) (p : MeasureTheory.Measure (Fin n → ℝ))
    (Mstar : ℝ) : Prop :=
  ∀ (M : ℕ) (Ω : Type) [MeasurableSpace Ω]
    (mu : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure mu]
    (samples : Fin M → Ω → (Fin n → ℝ))
    (thetaHat : Ω → polynomial_factor n → ℝ)
    (rho epsilon : ℝ),
    iid_samples mu p samples →
    (∀ omega, constrained_empirical_minimizer factors B i
      (fun m => samples m omega) (thetaHat omega)) →
    (∀ factor ∈ incident_maximal_factors factors i,
      Measurable (fun omega => thetaHat omega factor)) →
    1 ≤ rho → 0 < epsilon → epsilon ≤ 1 →
    rho * (n : ℝ) ^ (d + 1) * Mstar / epsilon ^ 2 ≤ (M : ℝ) →
    1 - 1 / (rho * (n : ℝ) * (Ct : ℝ)) <
      mu.real {omega | ∀ factor ∈ incident_maximal_factors factors i,
        (thetaStar factor - thetaHat omega factor) ^ 2 ≤ epsilon}

def family_structure_conclusion {n : ℕ} (A0 : ℝ) (C d : ℕ)
    (factors : Finset (polynomial_factor n)) (thetaStar : polynomial_factor n → ℝ)
    (i : Fin n) (B : ℝ) (Ct : ℕ) (p : MeasureTheory.Measure (Fin n → ℝ)) : Prop :=
  ∃ Mstar : ℝ,
    family_structure_sample_scale A0 C d B Ct (interaction_order factors) Mstar ∧
      family_structure_recovery_at_scale d factors thetaStar i B Ct p Mstar

theorem family_structure_learning :
    ∃ A0 : ℝ, 1 < A0 ∧
      ∃ C : ℕ, 0 < C ∧
        ∀ {n : ℕ} (d : ℕ)
        (factors : Finset (polynomial_factor n)) (thetaStar : polynomial_factor n → ℝ)
        (i : Fin n) (B tailRate : ℝ) (Ct : ℕ) (p : MeasureTheory.Measure (Fin n → ℝ))
        [MeasureTheory.IsProbabilityMeasure p],
        family_degree_at_most factors d →
        unit_base_polynomial_exponential_family factors thetaStar p →
        0 < B → parameter_feasible factors B thetaStar →
        1 + (1 / 1024 : ℝ) ≤ (d : ℝ) * B * (Ct : ℝ) ^ d →
        tail_decay_condition d tailRate Ct p →
        family_structure_conclusion A0 C d factors thetaStar i B Ct p := by sorry

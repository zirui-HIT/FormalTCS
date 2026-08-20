import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators

noncomputable def binary_entropy_bits (p : ℝ) : ℝ :=
  Real.binEntropy p / Real.log 2

noncomputable def bernoulli_kl_bits (p q : ℝ) : ℝ :=
  p * Real.logb 2 (p / q) + (1 - p) * Real.logb 2 ((1 - p) / (1 - q))

noncomputable def mdl_tilted_error (lambda q : ℝ) : ℝ :=
  1 / (1 + Real.rpow ((1 - q) / q) (lambda / (lambda - 1)))

noncomputable def mdl_upper_curve (lambda q : ℝ) : ℝ :=
  lambda * bernoulli_kl_bits (mdl_tilted_error lambda q) q +
    binary_entropy_bits (mdl_tilted_error lambda q)

noncomputable def mdl_upper_curve_inverse (lambda y : ℝ) : ℝ :=
  letI : Nonempty (Set.Icc (0 : ℝ) (1 / 2)) :=
    ⟨⟨0, le_rfl, by norm_num⟩⟩
  (Function.invFun
    (fun q : Set.Icc (0 : ℝ) (1 / 2) => mdl_upper_curve lambda q.1) y).1

noncomputable def mdl_worst_case_curve (lambda Lstar : ℝ) : ℝ :=
  if lambda ≤ 1 then
    1 - Real.rpow 2 (-binary_entropy_bits Lstar / lambda)
  else
    mdl_upper_curve_inverse lambda (binary_entropy_bits Lstar)

def mdl_zero_one_loss {X H : Type*} (predict : H → X → Bool)
    (h : H) (z : X × Bool) : ℝ :=
  if predict h z.1 = z.2 then 0 else 1

noncomputable def mdl_population_error {X H : Type*} [MeasurableSpace (X × Bool)]
    (predict : H → X → Bool) (D : MeasureTheory.ProbabilityMeasure (X × Bool))
    (h : H) : ℝ :=
  MeasureTheory.integral D.1 (mdl_zero_one_loss predict h)

def mdl_error_count {X H : Type*} {m : ℕ} (predict : H → X → Bool)
    (sample : Fin m → X × Bool) (h : H) : ℕ :=
  (Finset.univ.filter fun i => predict h (sample i).1 ≠ (sample i).2).card

noncomputable def mdl_valid_prior {H : Type*} (prior : H → ℝ) : Prop :=
  Summable prior ∧ (∀ h, 0 ≤ prior h) ∧ ∑' h, prior h ≤ 1

noncomputable def mdl_description_length {H : Type*} (prior : H → ℝ) (h : H) : ℝ :=
  -Real.logb 2 (prior h)

noncomputable def mdl_objective {X H : Type*} {m : ℕ} (lambda : ℝ)
    (prior : H → ℝ) (predict : H → X → Bool)
    (sample : Fin m → X × Bool) (h : H) : ℝ :=
  lambda * mdl_description_length prior h +
    Real.logb 2 (Nat.choose m (mdl_error_count predict sample h) : ℝ)

def mdl_empirically_admissible {X H : Type*} {m : ℕ}
    (predict : H → X → Bool) (sample : Fin m → X × Bool) (h : H) : Prop :=
  2 * mdl_error_count predict sample h ≤ m

structure mdl_configuration (lambda Lstar : ℝ) where
  X : Type
  H : Type
  measurableSpace : MeasurableSpace (X × Bool)
  predict : H → X → Bool
  prior : H → ℝ
  prior_valid : mdl_valid_prior prior
  source : letI := measurableSpace; MeasureTheory.ProbabilityMeasure (X × Bool)
  loss_measurable : ∀ h, letI := measurableSpace
    Measurable (mdl_zero_one_loss predict h)
  reference : H
  reference_supported : 0 < prior reference
  reference_error : letI := measurableSpace
    mdl_population_error predict source reference = Lstar
  select : ∀ m : ℕ, (Fin m → X × Bool) → H
  select_supported : ∀ (m : ℕ) (sample : Fin m → X × Bool),
    0 < prior (select m sample)
  select_admissible : ∀ (m : ℕ) (sample : Fin m → X × Bool),
    mdl_empirically_admissible predict sample (select m sample)
  select_minimizes : ∀ (m : ℕ) (sample : Fin m → X × Bool) (h : H),
    0 < prior h → mdl_empirically_admissible predict sample h →
      mdl_objective lambda prior predict sample (select m sample) ≤
        mdl_objective lambda prior predict sample h
  selected_error_measurable : ∀ m, letI := measurableSpace
    Measurable fun sample : Fin m → X × Bool =>
      mdl_population_error predict source (select m sample)

noncomputable def mdl_iid_sample_measure {Z : Type*} [MeasurableSpace Z]
    (D : MeasureTheory.ProbabilityMeasure Z) (m : ℕ) : MeasureTheory.Measure (Fin m → Z) :=
  MeasureTheory.Measure.pi fun _ : Fin m => D.1

noncomputable def expected_mdl_error {lambda Lstar : ℝ}
    (config : mdl_configuration lambda Lstar) (m : ℕ) : ℝ :=
  letI := config.measurableSpace
  MeasureTheory.integral (mdl_iid_sample_measure config.source m) fun sample =>
    mdl_population_error config.predict config.source (config.select m sample)

noncomputable def mdl_supremum_of_pointwise_limits (lambda Lstar : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ config : mdl_configuration lambda Lstar,
    Filter.Tendsto (fun m => expected_mdl_error config m)
      Filter.atTop (nhds r)}

noncomputable def mdl_finite_sample_supremum
    (lambda Lstar : ℝ) (m : ℕ) : ℝ :=
  ⨆ config : mdl_configuration lambda Lstar, expected_mdl_error config m

def mdl_limit_of_finite_sample_suprema
    (lambda Lstar limit : ℝ) : Prop :=
  Filter.Tendsto (mdl_finite_sample_supremum lambda Lstar)
    Filter.atTop (nhds limit)

theorem finite_mdl_worst_case_limit
    (lambda Lstar : ℝ)
    (hlambda : 0 < lambda) (hLstar_pos : 0 < Lstar) (hLstar_half : Lstar < 1 / 2) :
    ∃ limit : ℝ,
      mdl_limit_of_finite_sample_suprema lambda Lstar limit ∧
        mdl_worst_case_curve lambda Lstar =
          mdl_supremum_of_pointwise_limits lambda Lstar ∧
        mdl_supremum_of_pointwise_limits lambda Lstar ≤ limit ∧
        limit = mdl_worst_case_curve lambda Lstar := by sorry

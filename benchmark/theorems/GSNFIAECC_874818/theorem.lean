import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Finset.Powerset
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators ENNReal

open MeasureTheory

def full_support_pmf {Ω : Type*} (μ : PMF Ω) : Prop :=
  ∀ x, μ x ≠ 0

noncomputable def one_coordinate_mean {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω) (f : Ω → ℝ) : ℝ :=
  ∑ x, (μ x).toReal * f x

noncomputable def one_coordinate_noise {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω) (ρ : ℝ) (f : Ω → ℝ) : Ω → ℝ :=
  fun x ↦ ρ * f x + (1 - ρ) * one_coordinate_mean μ f

noncomputable def product_measure {Ω : Type*} [MeasurableSpace Ω]
    (μ : PMF Ω) (n : ℕ) : Measure (Fin n → Ω) :=
  Measure.pi fun _ : Fin n ↦ μ.toMeasure

noncomputable def weighted_lp_norm {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (q : ℝ≥0∞) (f : α → ℝ) : ℝ≥0∞ :=
  eLpNorm f q ν

noncomputable def coordinate_conditional_average {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω) {n : ℕ} (S : Finset (Fin n))
    (f : (Fin n → Ω) → ℝ) : (Fin n → Ω) → ℝ := by
  classical
  exact fun x ↦
    ∑ y, if ∀ i ∈ S, y i = x i then
      (∏ i ∈ Sᶜ, (μ (y i)).toReal) * f y
    else 0

noncomputable def product_noise {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω) (ρ : ℝ) {n : ℕ}
    (f : (Fin n → Ω) → ℝ) : (Fin n → Ω) → ℝ := by
  classical
  exact fun x ↦
    ∑ y, (∏ i, if y i = x i then
      ρ + (1 - ρ) * (μ (y i)).toReal
    else
      (1 - ρ) * (μ (y i)).toReal) * f y

def bernoulli_subset_weight {n : ℕ} (lam : ℝ) (S : Finset (Fin n)) : ℝ :=
  lam ^ S.card * (1 - lam) ^ (n - S.card)

def minimum_mass_spike {Ω : Type*} [DecidableEq Ω]
    (μ : PMF Ω) (f : Ω → ℝ) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ ∃ xStar : Ω,
    (∀ y, μ xStar ≤ μ y) ∧
      f = fun x ↦ if x = xStar then c else 0

noncomputable def one_coordinate_extremal_property {Ω : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [DecidableEq Ω]
    (μ : PMF Ω) (q : ℝ≥0∞) (ρ lam : ℝ) : Prop :=
  0 < lam ∧ lam < 1 ∧
    ∀ f : Ω → ℝ, (∀ x, 0 ≤ f x) →
      let lhs := weighted_lp_norm μ.toMeasure q (one_coordinate_noise μ ρ f)
      let rhs :=
        ENNReal.rpow (weighted_lp_norm μ.toMeasure 1 f) (1 - lam) *
          ENNReal.rpow (weighted_lp_norm μ.toMeasure q f) lam
      lhs ≤ rhs ∧
        (lhs = rhs ↔
          (∃ c : ℝ, 0 ≤ c ∧ f = fun _ ↦ c) ∨ minimum_mass_spike μ f)

noncomputable def tensorized_samorodnitsky_property {Ω : Type*}
    [Fintype Ω] [MeasurableSpace Ω]
    (μ : PMF Ω) (q : ℝ≥0∞) (ρ lam : ℝ) : Prop :=
  ∀ (n : ℕ) (f : (Fin n → Ω) → ℝ), (∀ x, 0 ≤ f x) →
    ENNReal.log
        (weighted_lp_norm (product_measure μ n) q (product_noise μ ρ f)) ≤
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        (bernoulli_subset_weight lam S : EReal) *
          ENNReal.log
            (weighted_lp_norm (product_measure μ n) q
              (coordinate_conditional_average μ S f))

noncomputable def two_point_moment (r s a b : ℝ) : ℝ :=
  (a * Real.rpow (1 + s * b) r + b * Real.rpow (1 - s * a) r) / (a + b)

noncomputable def minimum_atom_mass {Ω : Type*} [Fintype Ω] (μ : PMF Ω) : ℝ :=
  sInf (Set.range fun x ↦ (μ x).toReal)

noncomputable def optimal_samorodnitsky_parameter
    (q : ℝ≥0∞) (p ρ : ℝ) : ℝ :=
  if p = 1 then
    1 / 2
  else
    let α := 1 / p - 1
    if q = ⊤ then
      Real.log (1 + ρ * α) / Real.log (1 + α)
    else
      Real.log (two_point_moment q.toReal ρ 1 α) /
        Real.log (two_point_moment q.toReal 1 1 α)

theorem generalized_samorodnitsky_inequality {Ω : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [DecidableEq Ω] (μ : PMF Ω) (q : ℝ≥0∞) (ρ : ℝ)
    (hμ : full_support_pmf μ) (hq : (2 : ℝ≥0∞) ≤ q)
    (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) :
    one_coordinate_extremal_property μ q ρ
        (optimal_samorodnitsky_parameter q (minimum_atom_mass μ) ρ) ∧
      tensorized_samorodnitsky_property μ q ρ
        (optimal_samorodnitsky_parameter q (minimum_atom_mass μ) ρ) := by sorry

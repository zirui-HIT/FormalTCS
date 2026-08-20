import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Support

open MeasureTheory

noncomputable def chebyshev_first (n : ℕ) (x : ℝ) : ℝ :=
  (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x

noncomputable def chebyshev_moment
    (p : MeasureTheory.ProbabilityMeasure ℝ) (n : ℕ) : ℝ :=
  ∫ x, chebyshev_first n x ∂(p : MeasureTheory.Measure ℝ)

noncomputable def weighted_moment_discrepancy_sq
    (p q : MeasureTheory.ProbabilityMeasure ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 k,
    (chebyshev_moment p j - chebyshev_moment q j) ^ 2 / (j : ℝ) ^ 2

def is_coupling
    (p q : MeasureTheory.ProbabilityMeasure ℝ)
    (γ : MeasureTheory.Measure (ℝ × ℝ)) : Prop :=
  γ.fst = (p : MeasureTheory.Measure ℝ) ∧
    γ.snd = (q : MeasureTheory.Measure ℝ)

noncomputable def wasserstein_one
    (p q : MeasureTheory.ProbabilityMeasure ℝ) : ℝ :=
  sInf {c : ℝ | ∃ γ : MeasureTheory.Measure (ℝ × ℝ),
    is_coupling p q γ ∧ c = ∫ z, |z.1 - z.2| ∂γ}

theorem master_chebyshev_moment_matching
    (p q : MeasureTheory.ProbabilityMeasure ℝ)
    (hp : (p : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
    (hq : (q : MeasureTheory.Measure ℝ).support ⊆ Set.Icc (-1 : ℝ) 1)
    (k : ℕ) (hk : 0 < k) (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hmom : weighted_moment_discrepancy_sq p q k ≤ Γ ^ 2) :
    wasserstein_one p q ≤ 36 / (k : ℝ) + Γ := by sorry

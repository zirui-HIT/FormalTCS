import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Probability.Distributions.Poisson.Basic

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable def qtd_total_variation {α : Type*} [MeasurableSpace α]
    (μ ν : ProbabilityMeasure α) : ℝ :=
  sSup {r : ℝ | ∃ s : Set α, MeasurableSet s ∧
    r = |(μ : Measure α).real s - (ν : Measure α).real s|}

noncomputable def qtd_discrete_total_variation (p q : ℕ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑' x : ℕ, |p x - q x|

noncomputable def qtd_discrete_kl (p q : ℕ → ℝ) : ℝ :=
  ∑' x : ℕ, if p x = 0 then 0 else p x * Real.log (p x / q x)

def qtd_probability_mass (p : ℕ → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ Summable p ∧ (∑' x, p x) = 1 ∧ ∃ N, ∀ x, N ≤ x → p x = 0

def qtd_admissible_error (ε : ℝ) : Prop := 0 < ε ∧ ε < 1

noncomputable def qtd_complexity_scale (d : ℕ) (ε : ℝ) : ℝ :=
  (d : ℝ) * (Real.log ((d : ℝ) / ε)) ^ 2

structure quantized_transition_diffusion_family (d : ℕ) where
  pStar : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))
  pBar : ℝ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d))
  pHat : ℝ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d))
  encode : ℝ → EuclideanSpace ℝ (Fin d) → ℕ
  decode : ℝ → (ℕ → ℝ) → ProbabilityMeasure (EuclideanSpace ℝ (Fin d))
  quantizationCodebook : ℝ → Finset ℕ
  quantizationCellLower : ℝ → ℕ → EuclideanSpace ℝ (Fin d)
  fStar : EuclideanSpace ℝ (Fin d) → ℝ
  sigma : ℝ
  hessianBound : ℝ
  secondMomentBound : ℝ
  cubeRadius : ℝ → ℝ
  cellWidth : ℝ → ℝ
  binCount : ℝ → ℝ
  horizon : ℝ → ℝ
  earlyStop : ℝ → ℝ
  scoreError : ℝ → ℝ
  scoreEntropyLoss : ℝ → ℝ
  terminalIndex : ℝ → ℕ
  timestamp : ℝ → ℕ → ℝ
  rate : ℝ → ℕ → ℝ
  qStar : ℝ → ℕ → ℝ
  qForwardAtDelta : ℝ → ℕ → ℝ
  qReverseInitial : ℝ → ℕ → ℝ
  qApproxInitial : ℝ → ℕ → ℝ
  qReverseAtStop : ℝ → ℕ → ℝ
  qApproxAtStop : ℝ → ℕ → ℝ
  qForward : ℝ → ℝ → ℕ → ℝ
  qReverse : ℝ → ℝ → ℕ → ℝ
  qApproxReverse : ℝ → ℝ → ℕ → ℝ
  forwardRate : ℝ → ℕ → ℕ → ℝ
  reverseRate : ℝ → ℝ → ℕ → ℕ → ℝ
  learnedScore : ℝ → ℝ → ℕ → ℕ → ℝ
  learnedReverseRate : ℝ → ℝ → ℕ → ℕ → ℝ

noncomputable def qtd_aggregate_rate {d : ℕ}
    (F : quantized_transition_diffusion_family d) (ε : ℝ) : ℝ :=
  ∑ w ∈ Finset.range (F.terminalIndex ε),
    F.rate ε w * (F.timestamp ε (w + 1) - F.timestamp ε w)

noncomputable def qtd_expected_iterations {d : ℕ}
    (F : quantized_transition_diffusion_family d) (ε : ℝ) : ℝ :=
  ∫ n : ℕ, (n : ℝ) ∂
    ProbabilityTheory.poissonMeasure (Real.toNNReal (qtd_aggregate_rate F ε))

def qtd_quantization_cube {d : ℕ} (F : quantized_transition_diffusion_family d)
    (ε : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, |x i| ≤ F.cubeRadius ε}

def qtd_quantization_cell {d : ℕ} (F : quantized_transition_diffusion_family d)
    (ε : ℝ) (n : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  qtd_quantization_cube F ε ∩
    {x | ∀ i,
      F.quantizationCellLower ε n i ≤ x i ∧
      x i < F.quantizationCellLower ε n i + F.cellWidth ε}

noncomputable def qtd_analytic_assumptions {d : ℕ}
    (F : quantized_transition_diffusion_family d) : Prop :=
  (∃ Z : ℝ, 0 < Z ∧
    (F.pStar : Measure (EuclideanSpace ℝ (Fin d))) =
      volume.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-F.fStar x) / Z))) ∧
  MeasureTheory.Integrable (fun x ↦ ‖x‖ ^ 2)
    (F.pStar : Measure (EuclideanSpace ℝ (Fin d))) ∧
  (∫ x, ‖x‖ ^ 2 ∂(F.pStar : Measure (EuclideanSpace ℝ (Fin d)))) ≤
    F.secondMomentBound ∧
  ContDiff ℝ 2 F.fStar ∧
  (∀ x, ‖fderiv ℝ (gradient F.fStar) x‖ ≤ F.hessianBound) ∧
  (∀ (t : ℝ) (u : EuclideanSpace ℝ (Fin d)),
    MeasureTheory.Integrable (fun x ↦ Real.exp (t * inner ℝ x u))
      (F.pStar : Measure (EuclideanSpace ℝ (Fin d))) ∧
    (∫ x, Real.exp (t * inner ℝ x u)
        ∂(F.pStar : Measure (EuclideanSpace ℝ (Fin d)))) ≤
      Real.exp (F.sigma ^ 2 * t ^ 2 * ‖u‖ ^ 2 / 2)) ∧
  MeasureTheory.Integrable (fun x ↦ ‖gradient F.fStar x‖ ^ 2)
    (F.pStar : Measure (EuclideanSpace ℝ (Fin d))) ∧
  (∫ x, ‖gradient F.fStar x‖ ^ 2
      ∂(F.pStar : Measure (EuclideanSpace ℝ (Fin d)))) ≤
    (d : ℝ) * F.hessianBound ∧
  (∀ ε, qtd_admissible_error ε →
    qtd_total_variation F.pStar (F.pBar ε) ≤
      ((F.pStar : Measure (EuclideanSpace ℝ (Fin d)))
        ((qtd_quantization_cube F ε)ᶜ)).toReal + 2 * ε)

def qtd_training_assumption {d : ℕ}
    (F : quantized_transition_diffusion_family d) : Prop :=
  ∀ ε, qtd_admissible_error ε →
    0 ≤ F.scoreError ε ∧
    F.scoreEntropyLoss ε ≤ (F.scoreError ε) ^ 2

noncomputable def qtd_parameter_schedule {d : ℕ}
    (F : quantized_transition_diffusion_family d) : Prop :=
  ∀ ε, qtd_admissible_error ε →
    0 < F.sigma ∧ 0 < F.hessianBound ∧ 0 < F.secondMomentBound ∧
    F.cubeRadius ε = F.sigma * Real.sqrt (2 * Real.log (2 * (d : ℝ) / ε)) ∧
    F.cellWidth ε = ε /
      (2 * F.hessianBound *
        (F.sigma * Real.sqrt (2 * (d : ℝ) * Real.log (2 * (d : ℝ) / ε)) +
          (d : ℝ) + Real.sqrt ((d : ℝ) * F.secondMomentBound))) ∧
    F.binCount ε = 2 * F.cubeRadius ε / F.cellWidth ε ∧
    F.scoreError ε ≤ ε /
      (Real.log ((d : ℝ) / ε) + Real.log (Real.logb 2 (F.binCount ε))) ∧
    F.horizon ε =
      Real.log ((d : ℝ) / ε) + Real.log (Real.logb 2 (F.binCount ε)) ∧
    0 < F.earlyStop ε ∧
    F.earlyStop ε ≤ ε / ((d : ℝ) * Real.logb 2 (F.binCount ε)) ∧
    F.timestamp ε 0 = 0 ∧
    (∀ w < F.terminalIndex ε,
      F.timestamp ε (w + 1) - F.timestamp ε w =
        (1 / 2 : ℝ) * (F.horizon ε - F.timestamp ε (w + 1))) ∧
    F.timestamp ε (F.terminalIndex ε) = F.horizon ε - F.earlyStop ε ∧
    (∀ w ≤ F.terminalIndex ε,
      F.rate ε w =
        2 * (d : ℝ) * Real.logb 2 (F.binCount ε) /
          min 1 (F.horizon ε - F.timestamp ε w))

noncomputable def qtd_validated_parameter_schedule {d : ℕ}
    (F : quantized_transition_diffusion_family d) : Prop :=
  qtd_parameter_schedule F ∧
  ∀ ε, qtd_admissible_error ε →
    1 ≤ (d : ℝ) * Real.logb 2 (F.binCount ε) ∧
    F.scoreError ε ≤ ε / max 1 (F.horizon ε) ∧
    (2 / 3 : ℝ) *
        (ε / ((d : ℝ) * Real.logb 2 (F.binCount ε))) <
      F.earlyStop ε

def qtd_hamming_neighbor {d : ℕ} (F : quantized_transition_diffusion_family d)
    (ε : ℝ) (x y : ℕ) : Prop :=
  x ∈ F.quantizationCodebook ε ∧
  y ∈ F.quantizationCodebook ε ∧
  ∃ i < d * ⌊Real.logb 2 (F.binCount ε)⌋₊,
    y = Nat.xor x (2 ^ i)

def qtd_algorithmic_laws {d : ℕ}
    (F : quantized_transition_diffusion_family d) : Prop :=
  (∀ ε, qtd_admissible_error ε →
    qtd_probability_mass (F.qStar ε) ∧
    qtd_probability_mass (F.qForwardAtDelta ε) ∧
    qtd_probability_mass (F.qReverseInitial ε) ∧
    qtd_probability_mass (F.qApproxInitial ε) ∧
    qtd_probability_mass (F.qReverseAtStop ε) ∧
    qtd_probability_mass (F.qApproxAtStop ε)) ∧
  (∀ ε, qtd_admissible_error ε →
    ∀ x, x ∉ F.quantizationCodebook ε →
      F.qStar ε x = 0 ∧
      F.qForwardAtDelta ε x = 0 ∧
      F.qReverseInitial ε x = 0 ∧
      F.qApproxInitial ε x = 0 ∧
      F.qReverseAtStop ε x = 0 ∧
      F.qApproxAtStop ε x = 0) ∧
  (∀ ε, qtd_admissible_error ε →
    Measurable (F.encode ε) ∧
    0 < (F.pStar : Measure (EuclideanSpace ℝ (Fin d)))
      (qtd_quantization_cube F ε) ∧
    (∀ x ∈ F.quantizationCodebook ε,
      MeasurableSet (qtd_quantization_cell F ε x) ∧
      0 < volume (qtd_quantization_cell F ε x) ∧
      volume (qtd_quantization_cell F ε x) < ∞) ∧
    qtd_quantization_cube F ε =
      ⋃ x ∈ F.quantizationCodebook ε, qtd_quantization_cell F ε x ∧
    (∀ x ∈ F.quantizationCodebook ε,
      ∀ y ∈ F.quantizationCodebook ε, x ≠ y →
        Disjoint (qtd_quantization_cell F ε x)
          (qtd_quantization_cell F ε y)) ∧
    (∀ x ∈ F.quantizationCodebook ε,
      qtd_quantization_cube F ε ∩ (F.encode ε) ⁻¹' ({x} : Set ℕ) =
        qtd_quantization_cell F ε x) ∧
    (∀ x, ENNReal.ofReal (F.qStar ε x) =
      if x ∈ F.quantizationCodebook ε then
        (F.pStar : Measure (EuclideanSpace ℝ (Fin d)))
            (qtd_quantization_cell F ε x) /
          (F.pStar : Measure (EuclideanSpace ℝ (Fin d)))
            (qtd_quantization_cube F ε)
      else 0) ∧
    F.pBar ε = F.decode ε (F.qStar ε) ∧
    F.pHat ε = F.decode ε (F.qApproxAtStop ε)) ∧
  (∀ ε p, qtd_admissible_error ε →
    qtd_probability_mass p →
    (∀ x, x ∉ F.quantizationCodebook ε → p x = 0) →
    ∀ s, MeasurableSet s →
      (F.decode ε p : Measure (EuclideanSpace ℝ (Fin d))) s =
        ∑ x ∈ F.quantizationCodebook ε,
          ENNReal.ofReal (p x) *
            (volume (s ∩ qtd_quantization_cell F ε x) /
              volume (qtd_quantization_cell F ε x))) ∧
  (∀ ε p q, qtd_admissible_error ε →
    qtd_probability_mass p → qtd_probability_mass q →
    qtd_total_variation (F.decode ε p) (F.decode ε q) =
      qtd_discrete_total_variation p q) ∧
  ((∀ ε x, qtd_admissible_error ε →
      F.qReverseAtStop ε x = F.qForwardAtDelta ε x) ∧
    (∀ ε, qtd_admissible_error ε →
      Real.logb 2 (F.binCount ε) =
        (⌊Real.logb 2 (F.binCount ε)⌋₊ : ℝ) ∧
      (∀ x, x ∈ F.quantizationCodebook ε ↔
        x < 2 ^ (d * ⌊Real.logb 2 (F.binCount ε)⌋₊)) ∧
      (∀ x y, x ≠ y →
        (qtd_hamming_neighbor F ε x y → F.forwardRate ε x y = 1) ∧
        (¬qtd_hamming_neighbor F ε x y → F.forwardRate ε x y = 0)) ∧
      qtd_discrete_total_variation (F.qStar ε) (F.qForwardAtDelta ε) ≤
        1 - Real.exp
          (-F.earlyStop ε * (d : ℝ) * Real.logb 2 (F.binCount ε))))

noncomputable def qtd_reverse_process_laws {d : ℕ}
    (F : quantized_transition_diffusion_family d) : Prop :=
  ∀ ε, qtd_admissible_error ε →
    (∀ t, 0 ≤ t → t ≤ F.horizon ε →
      qtd_probability_mass (F.qForward ε t)) ∧
    (∀ t, 0 ≤ t → t ≤ F.horizon ε - F.earlyStop ε →
      qtd_probability_mass (F.qReverse ε t) ∧
      qtd_probability_mass (F.qApproxReverse ε t)) ∧
    (∀ x, F.qForward ε 0 x = F.qStar ε x) ∧
    (∀ x, F.qForward ε (F.earlyStop ε) x = F.qForwardAtDelta ε x) ∧
    (∀ t x, 0 ≤ t → t ≤ F.horizon ε - F.earlyStop ε →
      F.qReverse ε t x = F.qForward ε (F.horizon ε - t) x) ∧
    (∀ x, F.qReverse ε 0 x = F.qReverseInitial ε x) ∧
    (∀ x,
      F.qReverse ε (F.horizon ε - F.earlyStop ε) x =
        F.qReverseAtStop ε x) ∧
    (∀ x, F.qApproxReverse ε 0 x = F.qApproxInitial ε x) ∧
    (∀ x,
      F.qApproxReverse ε (F.horizon ε - F.earlyStop ε) x =
        F.qApproxAtStop ε x) ∧
    (∀ x y, x ≠ y → 0 ≤ F.forwardRate ε x y) ∧
    (∀ y,
      F.forwardRate ε y y =
        -∑' x, if x = y then 0 else F.forwardRate ε x y) ∧
    (∀ t x y, 0 ≤ t → t ≤ F.horizon ε - F.earlyStop ε → x ≠ y →
      F.reverseRate ε t x y =
        F.forwardRate ε y x * F.qReverse ε t x / F.qReverse ε t y) ∧
    (∀ t x y, 0 ≤ t → t ≤ F.horizon ε - F.earlyStop ε → x ≠ y →
      F.learnedReverseRate ε t x y =
        F.forwardRate ε y x * F.learnedScore ε t x y) ∧
    (∀ t x y, 0 ≤ t → t ≤ F.horizon ε - F.earlyStop ε → x ≠ y →
      0 ≤ F.reverseRate ε t x y ∧
      0 ≤ F.learnedReverseRate ε t x y ∧
      (0 < F.reverseRate ε t x y → 0 < F.learnedReverseRate ε t x y)) ∧
    (∀ t y, 0 ≤ t → t ≤ F.horizon ε - F.earlyStop ε →
      F.reverseRate ε t y y =
        -∑' x, if x = y then 0 else F.reverseRate ε t x y) ∧
    (∀ t y, 0 ≤ t → t ≤ F.horizon ε - F.earlyStop ε →
      F.learnedReverseRate ε t y y =
        -∑' x, if x = y then 0 else F.learnedReverseRate ε t x y) ∧
    (∀ t y, 0 ≤ t → t ≤ F.horizon ε →
      HasDerivAt (fun s ↦ F.qForward ε s y)
        (∑' x, F.forwardRate ε y x * F.qForward ε t x) t) ∧
    (∀ t y, 0 ≤ t → t ≤ F.horizon ε - F.earlyStop ε →
      HasDerivAt (fun s ↦ F.qReverse ε s y)
        (∑' x, F.reverseRate ε t y x * F.qReverse ε t x) t) ∧
    (∀ t y, 0 ≤ t → t ≤ F.horizon ε - F.earlyStop ε →
      HasDerivAt (fun s ↦ F.qApproxReverse ε s y)
        (∑' x, F.learnedReverseRate ε t y x *
          F.qApproxReverse ε t x) t) ∧
    (∀ w < F.terminalIndex ε, ∀ t y,
      F.timestamp ε w ≤ t → t ≤ F.timestamp ε (w + 1) →
      (∑' x, if x = y then 0 else F.learnedReverseRate ε t x y) ≤
        F.rate ε w) ∧
    (∀ t, 0 ≤ t → t ≤ F.horizon ε - F.earlyStop ε →
      (∑' y, F.qReverse ε t y *
        ∑' x, if x = y then 0 else
          if F.reverseRate ε t x y = 0 then
            F.learnedReverseRate ε t x y
          else
            F.reverseRate ε t x y *
                Real.log (F.reverseRate ε t x y /
                  F.learnedReverseRate ε t x y) +
              F.learnedReverseRate ε t x y -
                F.reverseRate ε t x y) ≤ F.scoreEntropyLoss ε) ∧
    (∀ t, 0 ≤ t → t ≤ F.horizon ε - F.earlyStop ε →
      ∃ r,
        HasDerivAt
          (fun s ↦ qtd_discrete_kl (F.qReverse ε s)
            (F.qApproxReverse ε s)) r t ∧
        r ≤ F.scoreEntropyLoss ε) ∧
    (∀ t, 0 ≤ t → t ≤ F.horizon ε →
      ∃ r,
        HasDerivAt
          (fun s ↦ qtd_discrete_kl (F.qForward ε s)
            (F.qApproxInitial ε)) r t ∧
        r ≤ -qtd_discrete_kl (F.qForward ε t) (F.qApproxInitial ε)) ∧
    qtd_discrete_kl (F.qForward ε 0) (F.qApproxInitial ε) ≤
      (d : ℝ) * Real.logb 2 (F.binCount ε)

noncomputable def qtd_validated_reverse_process_laws {d : ℕ}
    (F : quantized_transition_diffusion_family d) : Prop :=
  qtd_reverse_process_laws F ∧
  ∀ ε, qtd_admissible_error ε →
    ∀ t, 0 ≤ t → t ≤ F.horizon ε →
      ∃ r,
        HasDerivAt
          (fun s ↦ qtd_discrete_kl (F.qForward ε s)
            (F.qApproxInitial ε)) r t ∧
        r ≤ -2 *
          qtd_discrete_kl (F.qForward ε t) (F.qApproxInitial ε)

theorem main_thm {d : ℕ} (F : quantized_transition_diffusion_family d)
    (hd : 0 < d)
    (ha : qtd_analytic_assumptions F) (ht : qtd_training_assumption F)
    (hp : qtd_validated_parameter_schedule F) (hl : qtd_algorithmic_laws F)
    (hr : qtd_validated_reverse_process_laws F) :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0))
        (qtd_expected_iterations F) (qtd_complexity_scale d) ∧
      ∀ ε, qtd_admissible_error ε →
        qtd_total_variation F.pStar (F.pHat ε) ≤ 5 * ε := by sorry

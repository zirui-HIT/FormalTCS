import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Process.Filtration

set_option linter.all false
set_option maxHeartbeats 500000

noncomputable def reg_bound_full (T K : ℕ) (C ρ δ : ℝ) : ℝ :=
  4 * Real.logb 2 (T : ℝ) * Real.sqrt ((T : ℝ) * Real.log ((K : ℝ) * (T : ℝ)))
    + (2 * C / ρ) * Real.logb 2 (T : ℝ)
    + 4 * Real.sqrt ((T : ℝ) * Real.log ((T : ℝ) * (K : ℝ) / δ))

structure conomd_fs_run where
  T : ℕ
  K : ℕ
  m : ℕ
  hT : 0 < T
  hK : 0 < K
  hm : 0 < m
  Ω : Type
  instMeasurableSpace : MeasurableSpace Ω
  P : @MeasureTheory.Measure Ω instMeasurableSpace
  instIsProbabilityMeasure : @MeasureTheory.IsProbabilityMeasure Ω instMeasurableSpace P
  loss : ℕ → Ω → Fin K → ℝ
  hloss : ∀ t ω k, loss t ω k ∈ Set.Icc (0 : ℝ) 1
  constr : ℕ → Fin m → Ω → Fin K → ℝ
  hconstr : ∀ t i ω k, constr t i ω k ∈ Set.Icc (-1 : ℝ) 1
  meanLoss : ℕ → Fin K → ℝ
  hmeanLoss : ∀ t k,
    meanLoss t k = @MeasureTheory.integral Ω ℝ _ _ instMeasurableSpace P
      (fun ω => loss t ω k)
  meanConstr : ℕ → Fin m → Fin K → ℝ
  hmeanConstr : ∀ t i k,
    meanConstr t i k = @MeasureTheory.integral Ω ℝ _ _ instMeasurableSpace P
      (fun ω => constr t i ω k)
  hist : @MeasureTheory.Filtration Ω ℕ _ instMeasurableSpace
  hloss_condMean : ∀ t k A, @MeasurableSet Ω (hist t) A →
    @MeasureTheory.integral Ω ℝ _ _ instMeasurableSpace (P.restrict A)
        (fun ω => loss t ω k)
      = @MeasureTheory.integral Ω ℝ _ _ instMeasurableSpace (P.restrict A)
        (fun ω => meanLoss t k)
  hconstr_condMean : ∀ t i k A, @MeasurableSet Ω (hist t) A →
    @MeasureTheory.integral Ω ℝ _ _ instMeasurableSpace (P.restrict A)
        (fun ω => constr t i ω k)
      = @MeasureTheory.integral Ω ℝ _ _ instMeasurableSpace (P.restrict A)
        (fun ω => meanConstr t i k)
  action : ℕ → Ω → Fin K
  haction_meas : ∀ t, @Measurable Ω (Fin K) instMeasurableSpace _ (action t)
  hloss_past_meas : ∀ s t k, s < t →
    @Measurable Ω ℝ (hist t) _ (fun ω => loss s ω k)
  hconstr_past_meas : ∀ s t i k, s < t →
    @Measurable Ω ℝ (hist t) _ (fun ω => constr s i ω k)
  haction_past_meas : ∀ s t, s < t →
    @Measurable Ω (Fin K) (hist t) _ (action s)
  strategy : ℕ → Ω → Fin K → ℝ
  hstrategy_nonneg : ∀ t ω k, 0 ≤ strategy t ω k
  hstrategy_sum : ∀ t ω, ∑ k, strategy t ω k = 1
  hstrategy_init : ∀ ω k, strategy 0 ω k = (K : ℝ)⁻¹
  hstrategy_adapted : ∀ t k,
    @Measurable Ω ℝ (hist t) _ (fun ω => strategy t ω k)
  hsampling : ∀ t k A, @MeasurableSet Ω (hist t) A →
    @MeasureTheory.integral Ω ℝ _ _ instMeasurableSpace (P.restrict A)
        (fun ω => if action t ω = k then (1 : ℝ) else 0)
      = @MeasureTheory.integral Ω ℝ _ _ instMeasurableSpace (P.restrict A)
        (fun ω => strategy t ω k)
  hloss_sampling : ∀ t k A, @MeasurableSet Ω (hist t) A →
    @MeasureTheory.integral Ω ℝ _ _ instMeasurableSpace (P.restrict A)
        (fun ω => loss t ω k * (if action t ω = k then (1 : ℝ) else 0))
      = @MeasureTheory.integral Ω ℝ _ _ instMeasurableSpace (P.restrict A)
        (fun ω => strategy t ω k * meanLoss t k)
  hconstr_sampling : ∀ t i k A, @MeasurableSet Ω (hist t) A →
    @MeasureTheory.integral Ω ℝ _ _ instMeasurableSpace (P.restrict A)
        (fun ω => constr t i ω k * (if action t ω = k then (1 : ℝ) else 0))
      = @MeasureTheory.integral Ω ℝ _ _ instMeasurableSpace (P.restrict A)
        (fun ω => strategy t ω k * meanConstr t i k)
  η : ℝ
  hη : η = Real.sqrt (Real.log ((K : ℝ) * (T : ℝ)) / (T : ℝ))
  γ : ℝ
  hγ : γ = (T : ℝ)⁻¹
  ζ : ℝ
  hζ : ζ = Real.sqrt (Real.log ((K : ℝ) * (T : ℝ)) / (T : ℝ))
  dual : ℕ → Ω → Fin m → ℝ
  hdual_init : ∀ ω i, dual 0 ω i = 0
  hdual_update : ∀ t ω i,
    dual (t + 1) ω i
      = max 0 (dual t ω i + ζ * ∑ k, constr t i ω k * strategy t ω k)
  hdual_bound : ∀ t, t < T → ∀ ω i, dual t ω i ∈ Set.Icc (0 : ℝ) 1
  adjLoss : ℕ → Ω → Fin K → ℝ
  hadjLoss : ∀ t ω k,
    adjLoss t ω k = loss t ω k
      + (m : ℝ)⁻¹ * ∑ i, dual t ω i * constr t i ω k
  hstrategy_update : ∀ t ω k,
    strategy (t + 1) ω k
      = (1 - γ) * ((strategy t ω k * Real.exp (-η * adjLoss t ω k))
          / ∑ j, strategy t ω j * Real.exp (-η * adjLoss t ω j))
        + γ * (K : ℝ)⁻¹
  xStar : Fin K → ℝ
  hxStar_nonneg : ∀ k, 0 ≤ xStar k
  hxStar_sum : ∑ k, xStar k = 1
  hxStar_feasible : ∀ t, t < T → ∀ i, ∑ k, meanConstr t i k * xStar k ≤ 0
  hxStar_opt : ∀ x : Fin K → ℝ, (∀ k, 0 ≤ x k) → (∑ k, x k = 1) →
    (∀ t, t < T → ∀ i, ∑ k, meanConstr t i k * x k ≤ 0) →
    (∑ t ∈ Finset.range T, ∑ k, meanLoss t k * xStar k)
      ≤ ∑ t ∈ Finset.range T, ∑ k, meanLoss t k * x k
  regret : Ω → ℝ
  hregret : ∀ ω,
    regret ω = (∑ t ∈ Finset.range T, loss t ω (action t ω))
      - ∑ t ∈ Finset.range T, ∑ k, meanLoss t k * xStar k
  Ccorr : Fin m → ℝ
  hCcorr : ∀ i, IsGLB
    {c : ℝ | ∃ g : Fin K → ℝ, (∀ k, g k ∈ Set.Icc (-1 : ℝ) 1) ∧
      c = ∑ t ∈ Finset.range T, ∑ k, |meanConstr t i k - g k|} (Ccorr i)
  C : ℝ
  hC_def : IsLUB (Set.range Ccorr) C
  hC : 0 ≤ C
  ρ : ℝ
  hρ_def : IsLUB
    {r : ℝ | ∃ x : Fin K → ℝ, (∀ k, 0 ≤ x k) ∧ (∑ k, x k = 1) ∧
      ∀ t, t < T → ∀ i, r ≤ -(∑ k, meanConstr t i k * x k)} ρ
  hρ : 0 < ρ
  hρle : ρ ≤ 1

theorem reg_full (run : conomd_fs_run) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - 3 * δ) ≤
      run.P {ω | run.regret ω ≤ reg_bound_full run.T run.K run.C run.ρ δ} := by sorry

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Lattice.Fold

noncomputable def hard_context (m t : ℕ) : ℝ :=
  let first := (m + 3) / 4
  let count := (3 * m) / 4 - first + 1
  ((first + t % count : ℕ) : ℝ) / (m : ℝ)

noncomputable def hard_construction_constant : ℝ := (1 : ℝ) / 100

noncomputable def hard_threshold (δ : ℝ) (m T : ℕ) : ℝ :=
  δ * Real.sqrt ((m : ℝ) / (T : ℝ))

noncomputable def hard_group_family (η : ℝ) : Fin 3 → ℝ → ℝ → ℝ :=
  fun i x v =>
    if i = 0 then (if x + η ≤ v then 1 else 0)
    else if i = 1 then (if v ≤ x - η then 1 else 0)
    else (if |v - x| < η then 1 else 0)

noncomputable def empirical_bias (T : ℕ) (x p y : Fin T → ℝ) (g : ℝ → ℝ → ℝ) (v : ℝ) : ℝ :=
  ∑ t : Fin T, (if p t = v then (1 : ℝ) else 0) * g (x t) (p t) * (p t - y t)

noncomputable def prediction_values (T : ℕ) (p : Fin T → ℝ) : Finset ℝ :=
  Finset.image p Finset.univ

noncomputable def group_error (T : ℕ) (x p y : Fin T → ℝ) (g : ℝ → ℝ → ℝ) : ℝ :=
  ∑ v ∈ prediction_values T p, |empirical_bias T x p y g v|

noncomputable def multicalibration_error (T : ℕ) (x p y : Fin T → ℝ)
    (G : Fin 3 → ℝ → ℝ → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => group_error T x p y (G i))

structure online_mc_hard_instance where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  μ : MeasureTheory.Measure Ω
  [isProb : MeasureTheory.IsProbabilityMeasure μ]
  T : ℕ
  m : ℕ
  hm_grid : 2 ≤ m
  hm_lower : m ^ 3 ≤ T
  hm_upper : T < (m + 1) ^ 3
  y : Fin T → Ω → ℝ
  y_meas : ∀ t, Measurable (y t)
  y_binary : ∀ t ω, y t ω = 0 ∨ y t ω = 1
  y_mean : ∀ t, ∫ ω, y t ω ∂μ = hard_context m t.val
  y_indep : ProbabilityTheory.iIndepFun y μ
  algRandomness : MeasurableSpace Ω
  alg_le : algRandomness ≤ mΩ
  alg_indep : ProbabilityTheory.Indep algRandomness
    (⨆ t : Fin T, MeasurableSpace.comap (y t) inferInstance) μ
  p : Fin T → Ω → ℝ
  p_range : ∀ t ω, p t ω ∈ Set.Icc (0 : ℝ) 1
  p_adapted : ∀ t : Fin T,
    @Measurable Ω ℝ (algRandomness ⊔
      (⨆ s : Fin T, ⨆ _ : s < t, MeasurableSpace.comap (y s) inferInstance))
      inferInstance (p t)

noncomputable def expected_mc_error (inst : online_mc_hard_instance) : ℝ :=
  letI := inst.mΩ
  ∫ ω, multicalibration_error inst.T
      (fun t => hard_context inst.m t.val)
      (fun t => inst.p t ω)
      (fun t => inst.y t ω)
      (hard_group_family (hard_threshold hard_construction_constant inst.m inst.T)) ∂inst.μ

theorem main_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, ∀ inst : online_mc_hard_instance, T₀ ≤ inst.T →
      expected_mc_error inst ≥ c * (inst.T : ℝ) ^ ((2 : ℝ) / 3) := by sorry

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Process.HittingTime

set_option linter.all false
set_option maxHeartbeats 500000

def ts_pull_count {Ω : Type*} {K : ℕ}
    (action : ℕ → ℕ → Ω → Fin K) (a : Fin K) (T t : ℕ) (ω : Ω) : ℕ :=
  ((Finset.range t).filter fun s ↦ action T s ω = a).card

noncomputable def ts_empirical_mean {Ω : Type*} {K : ℕ}
    (action : ℕ → ℕ → Ω → Fin K) (reward : Fin K → ℕ → Ω → ℝ)
    (a : Fin K) (T t : ℕ) (ω : Ω) : ℝ :=
  (∑ s ∈ Finset.range t, if action T s ω = a then reward a s ω else 0) /
    (ts_pull_count action a T t ω : ℝ)

structure ts_history_space (K : ℕ) where
  entries : ℕ → Sum Unit (Fin K × ℝ)

instance ts_history_space_measurable (K : ℕ) : MeasurableSpace (ts_history_space K) :=
  MeasurableSpace.comap ts_history_space.entries
    (@MeasurableSpace.pi ℕ (fun _ ↦ Sum Unit (Fin K × ℝ)) (fun _ ↦ inferInstance))

def ts_history {Ω : Type*} {K : ℕ}
    (action : ℕ → ℕ → Ω → Fin K) (reward : Fin K → ℕ → Ω → ℝ)
    (T t : ℕ) (ω : Ω) : ts_history_space K :=
  ⟨fun s ↦ if s < t then Sum.inr (action T s ω, reward (action T s ω) s ω)
    else Sum.inl ()⟩

def variance_growth (gamma : ℕ → ℝ) : Prop :=
  (∀ T, 1 < gamma T) ∧
    Filter.Tendsto gamma Filter.atTop Filter.atTop ∧
    Filter.Tendsto
      (fun T ↦ gamma T * (Real.log (T : ℝ)) ^ 2 / (T : ℝ))
      Filter.atTop (nhds 0)

structure variance_inflated_ts_model (Ω : Type*) [MeasurableSpace Ω]
    (ℙ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure ℙ]
    (K : ℕ) (means : Fin K → ℝ) (gamma : ℕ → ℝ) where
  action : ℕ → ℕ → Ω → Fin K
  noise : Fin K → ℕ → Ω → ℝ
  index : ℕ → Fin K → ℕ → Ω → ℝ
  bestMean : ℝ
  best_mean_upper : ∀ a, means a ≤ bestMean
  best_mean_attained : ∃ a, means a = bestMean
  action_measurable : ∀ T t, Measurable (action T t)
  noise_measurable : ∀ a t, Measurable (noise a t)
  index_measurable : ∀ T a t, Measurable (index T a t)
  noise_independent :
    ProbabilityTheory.iIndepFun
      (fun i : Fin K × ℕ ↦ fun ω ↦ noise i.1 i.2 ω) ℙ
  noise_identically_distributed :
    ∀ i j : Fin K × ℕ,
      ProbabilityTheory.IdentDistrib
        (fun ω ↦ noise i.1 i.2 ω) (fun ω ↦ noise j.1 j.2 ω) ℙ ℙ
  noise_nondegenerate :
    ∀ a t, ¬ ∃ c : ℝ, (fun ω ↦ noise a t ω) =ᵐ[ℙ] (fun _ ↦ c)
  noise_centered : ∀ a t, (∫ ω, noise a t ω ∂ℙ) = 0
  noise_subgaussian :
    ∀ a t, ProbabilityTheory.HasSubgaussianMGF (noise a t) 1 ℙ
  initialization : ∀ T, K ≤ T → ∀ a ω, ts_pull_count action a T K ω = 1
  history_measurable :
    ∀ T t,
      Measurable
        (ts_history action (fun a s ω ↦ means a + noise a s ω) T t)
  selected_noise_conditional_subgaussian :
    ∀ T t a, t < T → ∀ u : ℝ,
      MeasureTheory.Integrable (fun ω ↦ Real.exp (u * noise a t ω)) ℙ ∧
      (MeasureTheory.condExp
          (m := MeasurableSpace.comap
            (fun ω ↦
              (ts_history action (fun b s ω' ↦ means b + noise b s ω') T t ω,
                action T t ω))
            inferInstance)
          ℙ (fun ω ↦ Real.exp (u * noise a t ω)))
        ≤ᵐ[ℙ] (fun _ ↦ Real.exp (u ^ 2 / 2))
  conditional_index_law :
    ∀ T t a, K ≤ t → t < T →
      (fun ω ↦
          ProbabilityTheory.condDistrib (index T a t)
            (ts_history action (fun b s ω' ↦ means b + noise b s ω') T t) ℙ
            (ts_history action (fun b s ω' ↦ means b + noise b s ω') T t ω))
        =ᵐ[ℙ]
      (fun ω ↦
          ProbabilityTheory.gaussianReal
            (ts_empirical_mean action (fun b s ω' ↦ means b + noise b s ω')
              a T t ω)
            (Real.toNNReal
              (gamma T / (ts_pull_count action a T t ω : ℝ))))
  conditional_index_independent :
    ∀ T t, K ≤ t → t < T →
      ∀ (f : Fin K → ℝ → ℝ),
        (∀ a, Measurable (f a)) → (∀ a x, |f a x| ≤ 1) →
        let m := MeasurableSpace.comap
          (ts_history action (fun b s ω ↦ means b + noise b s ω) T t)
          inferInstance
        (MeasureTheory.condExp (m := m) ℙ
          (fun ω ↦ ∏ a, f a (index T a t ω))) =ᵐ[ℙ]
        (fun ω ↦ ∏ a,
          MeasureTheory.condExp (m := m) ℙ
            (fun ω' ↦ f a (index T a t ω')) ω)
  index_future_noise_conditional_independent :
    ∀ T t, K ≤ t → t < T →
      ∀ (s : Finset (Fin K × ℕ))
        (f : (Fin K → ℝ) → ℝ) (g : Fin K × ℕ → ℝ → ℝ),
        Measurable f → (∀ i, Measurable (g i)) →
        (∀ x, |f x| ≤ 1) → (∀ i x, |g i x| ≤ 1) →
        let m := MeasurableSpace.comap
          (ts_history action (fun b u ω ↦ means b + noise b u ω) T t)
          inferInstance
        (MeasureTheory.condExp (m := m) ℙ
          (fun ω ↦ f (fun a ↦ index T a t ω) *
            ∏ i ∈ s, g i (noise i.1 (t + i.2) ω))) =ᵐ[ℙ]
        (fun ω ↦
          MeasureTheory.condExp (m := m) ℙ
              (fun ω' ↦ f (fun a ↦ index T a t ω')) ω *
            MeasureTheory.condExp (m := m) ℙ
              (fun ω' ↦ ∏ i ∈ s, g i (noise i.1 (t + i.2) ω')) ω)
  greedy_action :
    ∀ T t, K ≤ t → t < T → ∀ ω a,
      index T a t ω ≤ index T (action T t ω) t ω

noncomputable def ts_optimal_arms {Ω : Type*} [MeasurableSpace Ω]
    {ℙ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure ℙ]
    {K : ℕ} {means : Fin K → ℝ} {gamma : ℕ → ℝ}
    (algorithm : variance_inflated_ts_model Ω ℙ K means gamma) : Finset (Fin K) :=
  Finset.univ.filter fun a ↦ means a = algorithm.bestMean

noncomputable def ts_optimal_arm_count {Ω : Type*} [MeasurableSpace Ω]
    {ℙ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure ℙ]
    {K : ℕ} {means : Fin K → ℝ} {gamma : ℕ → ℝ}
    (algorithm : variance_inflated_ts_model Ω ℙ K means gamma) : ℕ :=
  (ts_optimal_arms algorithm).card

def ts_gap {Ω : Type*} [MeasurableSpace Ω]
    {ℙ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure ℙ]
    {K : ℕ} {means : Fin K → ℝ} {gamma : ℕ → ℝ}
    (algorithm : variance_inflated_ts_model Ω ℙ K means gamma) (a : Fin K) : ℝ :=
  algorithm.bestMean - means a

def ts_optimal_allocation_limit {Ω : Type*} [MeasurableSpace Ω]
    (ℙ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure ℙ]
    {K : ℕ} {means : Fin K → ℝ} {gamma : ℕ → ℝ}
    (algorithm : variance_inflated_ts_model Ω ℙ K means gamma) : Prop :=
  ∀ a, a ∈ ts_optimal_arms algorithm →
    MeasureTheory.TendstoInMeasure ℙ
      (fun T ω ↦ (ts_pull_count algorithm.action a T T ω : ℝ) / (T : ℝ))
      Filter.atTop
      (fun _ ↦ 1 / (ts_optimal_arm_count algorithm : ℝ))

def ts_suboptimal_allocation_limit {Ω : Type*} [MeasurableSpace Ω]
    (ℙ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure ℙ]
    {K : ℕ} {means : Fin K → ℝ} {gamma : ℕ → ℝ}
    (algorithm : variance_inflated_ts_model Ω ℙ K means gamma) : Prop :=
  ∀ a, a ∉ ts_optimal_arms algorithm →
    MeasureTheory.TendstoInMeasure ℙ
      (fun T ω ↦
        (ts_pull_count algorithm.action a T T ω : ℝ) /
          (gamma T * Real.log ((T : ℝ) / gamma T)))
      Filter.atTop
      (fun _ ↦ 2 / (ts_gap algorithm a) ^ 2)

def ts_stable_with {Ω : Type*} [MeasurableSpace Ω]
    (ℙ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure ℙ]
    {K : ℕ} (action : ℕ → ℕ → Ω → Fin K)
    (center : Fin K → ℕ → ℝ) : Prop :=
  ∀ a,
    MeasureTheory.TendstoInMeasure ℙ
      (fun T ω ↦ (ts_pull_count action a T T ω : ℝ) / center a T)
      Filter.atTop (fun _ ↦ 1) ∧
    Filter.Tendsto (center a) Filter.atTop Filter.atTop

noncomputable def ts_intended_center {Ω : Type*} [MeasurableSpace Ω]
    {ℙ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure ℙ]
    {K : ℕ} {means : Fin K → ℝ} {gamma : ℕ → ℝ}
    (algorithm : variance_inflated_ts_model Ω ℙ K means gamma)
    (a : Fin K) (T : ℕ) : ℝ :=
  if a ∈ ts_optimal_arms algorithm then
    (T : ℝ) / (ts_optimal_arm_count algorithm : ℝ)
  else
    2 * gamma T * Real.log ((T : ℝ) / gamma T) / (ts_gap algorithm a) ^ 2

theorem stability_for_ts_with_variance_inflation {Ω : Type*} [MeasurableSpace Ω]
    (ℙ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure ℙ]
    {K : ℕ} (means : Fin K → ℝ) (gamma : ℕ → ℝ)
    (algorithm : variance_inflated_ts_model Ω ℙ K means gamma)
    (hK : 2 ≤ K) (hgamma : variance_growth gamma) :
    ts_optimal_allocation_limit ℙ algorithm ∧
      ts_suboptimal_allocation_limit ℙ algorithm ∧
      ts_stable_with ℙ algorithm.action (ts_intended_center algorithm) := by sorry

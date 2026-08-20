import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Process.Filtration

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory

noncomputable def adagrad_grad_coord {d : ℕ} (F : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (i : Fin d) : ℝ :=
  fderiv ℝ F x (Pi.single i 1)

def adagrad_l1_norm {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  ∑ i, |v i|

noncomputable def adagrad_linf_norm {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  ⨆ i, |v i|

structure adagrad_setting (Ω : Type) [mΩ : MeasurableSpace Ω] where
  μ : Measure Ω
  isProbabilityMeasure : IsProbabilityMeasure μ
  ℱ : Filtration ℕ mΩ
  d : ℕ
  one_le_d : 1 ≤ d
  T : ℕ
  one_le_T : 1 ≤ T
  η : ℝ
  eta_pos : 0 < η
  δ : ℝ
  delta_pos : 0 < δ
  delta_lt : δ < 1 / (d : ℝ)
  obj : (Fin d → ℝ) → ℝ
  obj_differentiable : Differentiable ℝ obj
  objMin : ℝ
  obj_lower_bounded : ∀ x, objMin ≤ obj x
  L : Fin d → ℝ
  L_nonneg : ∀ i, 0 ≤ L i
  σ : Fin d → ℝ
  sigma_nonneg : ∀ i, 0 ≤ σ i
  obj_smooth : ∀ x y : Fin d → ℝ,
    |obj y - obj x - ∑ i, adagrad_grad_coord obj x i * (y i - x i)|
      ≤ ∑ i, L i / 2 * (x i - y i) ^ 2
  w : ℕ → Ω → Fin d → ℝ
  g : ℕ → Ω → Fin d → ℝ
  init : Fin d → ℝ
  w_one : ∀ ω, w 1 ω = init
  w_adapted : ∀ t : ℕ, Measurable[ℱ t] fun ω => w (t + 1) ω
  g_adapted : ∀ t : ℕ, Measurable[ℱ t] fun ω => g t ω
  g_integrable : ∀ (t : ℕ) (i : Fin d), Integrable (fun ω => g t ω i) μ
  g_sq_integrable : ∀ (t : ℕ) (i : Fin d), Integrable (fun ω => g t ω i ^ 2) μ
  obj_integrable : ∀ t : ℕ, Integrable (fun ω => obj (w t ω)) μ
  adagrad_update : ∀ t : ℕ, 1 ≤ t → ∀ (ω : Ω) (i : Fin d),
    w (t + 1) ω i
      = w t ω i - η * (g t ω i / (Real.sqrt (∑ s ∈ Finset.Icc 1 t, g s ω i ^ 2) + δ))
  g_unbiased : ∀ t : ℕ, 1 ≤ t → ∀ i : Fin d,
    μ[fun ω => g t ω i|ℱ (t - 1)] =ᵐ[μ] fun ω => adagrad_grad_coord obj (w t ω) i
  g_bounded_variance : ∀ t : ℕ, 1 ≤ t → ∀ i : Fin d,
    μ[fun ω => (g t ω i - adagrad_grad_coord obj (w t ω) i) ^ 2|ℱ (t - 1)]
      ≤ᵐ[μ] fun _ => σ i ^ 2

noncomputable def adagrad_gap {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω) : ℝ :=
  S.obj S.init - S.objMin

noncomputable def adagrad_h {Ω : Type} [MeasurableSpace Ω] (S : adagrad_setting Ω) : ℝ :=
  ((S.T : ℝ) * adagrad_linf_norm S.σ ^ 2
      + (S.T : ℝ) * adagrad_linf_norm (fun i => adagrad_grad_coord S.obj S.init i) ^ 2
      + S.η ^ 2 * adagrad_linf_norm S.L * adagrad_l1_norm S.L * (S.T : ℝ) ^ 3) / S.δ ^ 2

noncomputable def adagrad_log_budget {Ω : Type} [MeasurableSpace Ω]
    (S : adagrad_setting Ω) (c : ℝ) : ℝ :=
  Real.log (c * (1 + adagrad_h S))

noncomputable def adagrad_stationarity {Ω : Type} [MeasurableSpace Ω]
    (S : adagrad_setting Ω) : ℝ :=
  ∫ ω, (1 / (S.T : ℝ))
    * ∑ t ∈ Finset.Icc 1 S.T, adagrad_l1_norm (fun i => adagrad_grad_coord S.obj (S.w t ω) i)
    ∂S.μ

theorem adagrad_coord_main_result :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : ℕ → adagrad_setting Ω),
      (∀ n, (S n).T = n + 1) →
      (∀ n, (S n).d = (S 0).d) →
      (∀ n, (S n).η = (S 0).η) →
      (∀ n, (S n).δ = (S 0).δ) →
      (∀ n, adagrad_gap (S n) = adagrad_gap (S 0)) →
      (∀ n, adagrad_l1_norm (S n).L = adagrad_l1_norm (S 0).L) →
      (∀ n, adagrad_linf_norm (S n).L = adagrad_linf_norm (S 0).L) →
      (∀ n, adagrad_l1_norm (S n).σ = adagrad_l1_norm (S 0).σ) →
      (∀ n, adagrad_linf_norm (S n).σ = adagrad_linf_norm (S 0).σ) →
      (∀ n, adagrad_linf_norm (fun i => adagrad_grad_coord (S n).obj (S n).init i)
          = adagrad_linf_norm (fun i => adagrad_grad_coord (S 0).obj (S 0).init i)) →
      ∃ (C : ℝ) (N : ℕ), ∀ n, N ≤ n →
        adagrad_stationarity (S n)
          ≤ C * (adagrad_gap (S n) / ((S n).η * Real.sqrt ((S n).T : ℝ))
            + (S n).η * adagrad_l1_norm (S n).L * adagrad_log_budget (S n) c
                / Real.sqrt ((S n).T : ℝ)
            + Real.sqrt (adagrad_l1_norm (S n).σ * adagrad_gap (S n))
                / (Real.sqrt ((S n).η) * ((S n).T : ℝ) ^ ((1 : ℝ) / 4))
            + Real.sqrt ((S n).η * adagrad_l1_norm (S n).σ * adagrad_l1_norm (S n).L
                * adagrad_log_budget (S n) c) / ((S n).T : ℝ) ^ ((1 : ℝ) / 4)
            + adagrad_l1_norm (S n).σ * Real.sqrt (adagrad_log_budget (S n) c)
                / ((S n).T : ℝ) ^ ((1 : ℝ) / 4)) := by sorry

import Mathlib

set_option linter.all false
set_option maxHeartbeats 500000

def is_moore_penrose_inverse {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  A * B * A = A ∧ B * A * B = B ∧
    Matrix.conjTranspose (A * B) = A * B ∧
    Matrix.conjTranspose (B * A) = B * A

def cumulative_score {Ω : Type*} {T d : ℕ}
    (X : Fin T → Ω → Fin d → ℝ) (Y : Fin T → Ω → ℝ) (ω : Ω) : Fin d → ℝ :=
  ∑ t, Y t ω • X t ω

def empirical_gram {Ω : Type*} {T d : ℕ}
    (X : Fin T → Ω → Fin d → ℝ) (ω : Ω) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ t, Matrix.vecMulVec (X t ω) (X t ω)

def self_normalized_energy {d : ℕ}
    (s : Fin d → ℝ) (Vdagger : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  dotProduct s (Matrix.mulVec Vdagger s)

def predictable_covariates {Ω : Type*} [mΩ : MeasurableSpace Ω] {T d : ℕ}
    (ℱ : MeasureTheory.Filtration ℕ mΩ) (X : Fin T → Ω → Fin d → ℝ) : Prop :=
  ∀ t : Fin T, @Measurable Ω (Fin d → ℝ) (ℱ t.val) inferInstance (X t)

def covariate_history_filtration {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {T d : ℕ} (ℋx : MeasureTheory.Filtration ℕ mΩ)
    (X : Fin T → Ω → Fin d → ℝ) : Prop :=
  ∀ n : ℕ, ℋx n = MeasurableSpace.generateFrom
    {s : Set Ω | ∃ t : Fin T, t.val < n ∧
      ∃ A : Set (Fin d → ℝ), MeasurableSet A ∧ s = X t ⁻¹' A}

def conditionally_subgaussian_noise {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {T : ℕ} (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (ℱ : MeasureTheory.Filtration ℕ mΩ) (Y : Fin T → Ω → ℝ) (σ : ℝ) : Prop :=
  (∀ t : Fin T, @Measurable Ω ℝ (ℱ (t.val + 1)) inferInstance (Y t)) ∧
  ∀ (t : Fin T) (α : ℝ),
    MeasureTheory.Integrable (fun ω => Real.exp (α * Y t ω)) μ ∧
    MeasureTheory.condExp (m := ℱ t.val) μ
      (fun ω => Real.exp (α * Y t ω))
      ≤ᵐ[μ] fun _ => Real.exp (α ^ 2 * σ ^ 2 / 2)

def conditional_covariate_law {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {T d : ℕ} (μ : MeasureTheory.Measure Ω)
    (ℋx : MeasureTheory.Filtration ℕ mΩ) (X : Fin T → Ω → Fin d → ℝ)
    (P : (t : Fin T) → @ProbabilityTheory.Kernel Ω (Fin d → ℝ)
      (ℋx t.val) inferInstance) : Prop :=
  (∀ t ω, MeasureTheory.IsProbabilityMeasure (P t ω)) ∧
  ∀ (t : Fin T) (f : (Fin d → ℝ) → ℝ), Measurable f →
    MeasureTheory.Integrable (fun ω => f (X t ω)) μ →
    MeasureTheory.condExp (m := ℋx t.val) μ (fun ω => f (X t ω))
      =ᵐ[μ] fun ω => ∫ x, f x ∂P t ω

noncomputable def smooth_covariates {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {T d : ℕ} (ℋx : MeasureTheory.Filtration ℕ mΩ)
    (P : (t : Fin T) → @ProbabilityTheory.Kernel Ω (Fin d → ℝ)
      (ℋx t.val) inferInstance)
    (μ0 : MeasureTheory.Measure (Fin d → ℝ)) (Ccov : ℝ) : Prop :=
  ∀ t ω, P t ω ≤ ENNReal.ofReal Ccov • μ0

noncomputable def self_normalized_smooth_rate
    (T d : ℕ) (σ Ccov δ : ℝ) : ℝ :=
  σ ^ 2 * (Real.sqrt ((d : ℝ) * Ccov * (T : ℝ) *
    Real.log (2 * (T : ℝ) / δ)) + Real.log (2 / δ))

def self_normalized_smoothness_claim : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (T d : ℕ) (Ω : Type*) [mΩ : MeasurableSpace Ω]
      (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
      (ℱ ℋx : MeasureTheory.Filtration ℕ mΩ)
      (X : Fin T → Ω → Fin d → ℝ) (Y : Fin T → Ω → ℝ)
      (P : (t : Fin T) → @ProbabilityTheory.Kernel Ω (Fin d → ℝ)
        (ℋx t.val) inferInstance)
      (μ0 : MeasureTheory.Measure (Fin d → ℝ))
      [MeasureTheory.IsProbabilityMeasure μ0]
      (Vdagger : Ω → Matrix (Fin d) (Fin d) ℝ)
      (σ Ccov δ : ℝ),
      0 < T → 0 < d → 0 < σ → 1 ≤ Ccov → 0 < δ → δ < 1 →
      covariate_history_filtration ℋx X →
      (∀ n, ℋx n ≤ ℱ n) →
      predictable_covariates ℱ X →
      conditionally_subgaussian_noise μ ℱ Y σ →
      conditional_covariate_law μ ℋx X P →
      smooth_covariates ℋx P μ0 Ccov →
      (∀ ω, is_moore_penrose_inverse (empirical_gram X ω) (Vdagger ω)) →
      μ {ω | self_normalized_energy (cumulative_score X Y ω) (Vdagger ω)
        ≤ C * self_normalized_smooth_rate T d σ Ccov δ}
        ≥ ENNReal.ofReal (1 - δ)

theorem self_normalized_martingales_under_smoothness :
    self_normalized_smoothness_claim := by sorry

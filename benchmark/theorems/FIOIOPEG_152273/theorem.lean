import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Real.Sign

variable {X : Type*} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def kernel_of_feature_map (Φ : X × ℝ → F) (z z' : X × ℝ) : ℝ :=
  inner ℝ (Φ z) (Φ z')

def history_local {α : Type*} (t : ℕ) (G : (ℕ → Fin 2) → α) : Prop :=
  ∀ σ τ : ℕ → Fin 2, (∀ s, s < t → σ s = τ s) → G σ = G τ

structure any_kernel_transcript (Feature : Type*) where
  feature : ℕ → (ℕ → Fin 2) → Feature
  candidate : ℕ → (ℕ → Fin 2) → Fin 2 → ℝ
  weight : ℕ → (ℕ → Fin 2) → Fin 2 → ℝ
  outcome : ℕ → (ℕ → Fin 2) → ℝ
  feature_history_local : ∀ t : ℕ, history_local t (feature t)
  candidate_history_local : ∀ t : ℕ, history_local t (candidate t)
  weight_history_local : ∀ t : ℕ, history_local t (weight t)
  outcome_history_local : ∀ t : ℕ, history_local t (outcome t)
  weight_nonneg : ∀ t : ℕ, ∀ σ : ℕ → Fin 2, ∀ i : Fin 2, 0 ≤ weight t σ i
  weight_sum_one : ∀ t : ℕ, ∀ σ : ℕ → Fin 2, ∑ i : Fin 2, weight t σ i = 1
  candidate_mem_unitInterval :
    ∀ t : ℕ, ∀ σ : ℕ → Fin 2, ∀ i : Fin 2, candidate t σ i ∈ Set.Icc (0 : ℝ) 1
  outcome_mem_zero_one :
    ∀ t : ℕ, ∀ σ : ℕ → Fin 2, outcome t σ = 0 ∨ outcome t σ = 1

def selector_extension (T : ℕ) (σ : Fin T → Fin 2) : ℕ → Fin 2 :=
  fun t => if h : t < T then σ ⟨t, h⟩ else 0

def trajectory_weight (tr : any_kernel_transcript X) (T : ℕ) (σ : Fin T → Fin 2) : ℝ :=
  ∏ t ∈ Finset.range T,
    tr.weight t (selector_extension T σ) (selector_extension T σ t)

def round_expectation (tr : any_kernel_transcript X) (t : ℕ) (σ : ℕ → Fin 2)
    (g : Fin 2 → ℝ) : ℝ :=
  ∑ i : Fin 2, tr.weight t σ i * g i

def horizon_expectation (tr : any_kernel_transcript X) (T : ℕ)
    (G : (ℕ → Fin 2) → ℝ) : ℝ :=
  ∑ σ : Fin T → Fin 2, trajectory_weight tr T σ * G (selector_extension T σ)

noncomputable def score_function (Φ : X × ℝ → F) (tr : any_kernel_transcript X) (t : ℕ)
    (σ : ℕ → Fin 2) (p : ℝ) : ℝ :=
  (∑ s ∈ Finset.range t,
      kernel_of_feature_map Φ (tr.feature t σ, p) (tr.feature s σ, tr.candidate s σ (σ s))
        * (tr.outcome s σ - tr.candidate s σ (σ s)))
    + (1 / 2) * kernel_of_feature_map Φ (tr.feature t σ, p) (tr.feature t σ, p) * (1 - 2 * p)

def is_any_kernel_round (Φ : X × ℝ → F) (tr : any_kernel_transcript X) (bound : ℝ)
    (t : ℕ) (σ : ℕ → Fin 2) : Prop :=
  (Real.sign (score_function Φ tr t σ 0) = Real.sign (score_function Φ tr t σ 1) ∧
      Real.sign (score_function Φ tr t σ 0) ≠ 0 ∧
      tr.candidate t σ 0 = (1 + Real.sign (score_function Φ tr t σ 0)) / 2 ∧
      tr.candidate t σ 1 = tr.candidate t σ 0)
    ∨ (0 < bound ∧
      score_function Φ tr t σ (tr.candidate t σ 0) *
          score_function Φ tr t σ (tr.candidate t σ 1) < 0 ∧
      tr.weight t σ 0 =
        |score_function Φ tr t σ (tr.candidate t σ 1)| /
          (|score_function Φ tr t σ (tr.candidate t σ 0)| +
            |score_function Φ tr t σ (tr.candidate t σ 1)|) ∧
      |tr.candidate t σ 0 - tr.candidate t σ 1| ≤ 1 / (10 * bound * ((t : ℝ) + 1) ^ 3) ∧
      |score_function Φ tr t σ (tr.candidate t σ 0)| ≤ ((t : ℝ) + 1) * bound)

theorem indistinguishability_main (Φ : X × ℝ → F) (tr : any_kernel_transcript X)
    (bound : ℝ) (T : ℕ) (f : F)
    (hrounds : ∀ t ∈ Finset.range T, ∀ σ : ℕ → Fin 2,
      is_any_kernel_round Φ tr bound t σ) :
    |∑ t ∈ Finset.range T,
        horizon_expectation tr T (fun σ =>
          round_expectation tr t σ (fun i =>
            (tr.outcome t σ - tr.candidate t σ i) *
              inner ℝ f (Φ (tr.feature t σ, tr.candidate t σ i))))| ≤
      ‖f‖ * Real.sqrt (1 + ∑ t ∈ Finset.range T,
        horizon_expectation tr T (fun σ =>
          round_expectation tr t σ (fun i =>
            tr.candidate t σ i * (1 - tr.candidate t σ i) *
              kernel_of_feature_map Φ (tr.feature t σ, tr.candidate t σ i)
                (tr.feature t σ, tr.candidate t σ i)))) := by sorry

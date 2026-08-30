import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option linter.all false
set_option maxHeartbeats 500000

abbrev binary_vector (n : ℕ) := Fin n → ZMod 2

def binary_vector_support_size {n : ℕ} (v : binary_vector n) : ℕ :=
  (Finset.univ.filter fun i => v i ≠ 0).card

structure lspn_instance (n k : ℕ) (η : ℝ) where
  noise_nonnegative : 0 ≤ η
  noise_at_most_one : η ≤ 1
  sample : PMF (binary_vector n × ZMod 2)

def is_lspn_instance {n k : ℕ} {η : ℝ} (I : lspn_instance n k η)
    (secret : binary_vector n) : Prop :=
  binary_vector_support_size secret ≤ k ∧
    ∀ x y,
      I.sample (x, y) =
      PMF.uniformOfFintype (binary_vector n) x *
        if y = dotProduct x secret then 1 - ENNReal.ofReal η else ENNReal.ofReal η

structure lspn_algorithm where
  output : ∀ {n k : ℕ} {η : ℝ}, lspn_instance n k η → PMF (binary_vector n)
  running_time : ℕ → ℕ → ℝ → ℕ
  samples_used : ℕ → ℕ → ℝ → ℕ

def succeeds_with_probability (algorithm : lspn_algorithm) {n k : ℕ} {η : ℝ}
    (I : lspn_instance n k η) (secret : binary_vector n) (p : ENNReal) : Prop :=
  p ≤ algorithm.output I secret

noncomputable def lspn_time_scale (k : ℕ) (η : ℝ) (n : ℕ) : ℝ :=
  (η * (n : ℝ) / (k : ℝ)) ^ k

noncomputable def lspn_sample_scale (k : ℕ) (η : ℝ) (n : ℕ) : ℝ :=
  (k : ℝ) / η + (k : ℝ) * Real.log ((n : ℝ) / (k : ℝ))

def has_lspn_time_bound (algorithm : lspn_algorithm) (k : ℕ) (η : ℝ) : Prop :=
  Asymptotics.IsBigO Filter.atTop
    (fun n : ℕ => (algorithm.running_time n k η : ℝ))
    (lspn_time_scale k η)

def has_lspn_sample_bound (algorithm : lspn_algorithm) (k : ℕ) (η : ℝ) : Prop :=
  Asymptotics.IsBigO Filter.atTop
    (fun n : ℕ => (algorithm.samples_used n k η : ℝ))
    (lspn_sample_scale k η)

def solves_low_noise_lspn (algorithm : lspn_algorithm) : Prop :=
  ∀ (η : ℝ) (k : ℕ),
    0 < η → η < (1 : ℝ) / 20 →
      has_lspn_time_bound algorithm k η ∧
      has_lspn_sample_bound algorithm k η ∧
      ∀ (n : ℕ), (k : ℝ) / η < (n : ℝ) →
        ∀ (secret : binary_vector n) (I : lspn_instance n k η),
          is_lspn_instance I secret →
            succeeds_with_probability algorithm I secret ((9 : ENNReal) / 10)

theorem low_noise_main : ∃ algorithm : lspn_algorithm, solves_low_noise_lspn algorithm := by sorry

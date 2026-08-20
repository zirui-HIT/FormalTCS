import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option linter.all false
set_option maxHeartbeats 500000

abbrev robust_point (d : ℕ) := EuclideanSpace ℝ (Fin d)

abbrev robust_dataset (n d : ℕ) := Fin n → robust_point d

noncomputable def empirical_mean_on {n d : ℕ}
    (S : robust_dataset n d) (I : Finset (Fin n)) : robust_point d :=
  (I.card : ℝ)⁻¹ • ∑ i ∈ I, S i

noncomputable def empirical_covariance_on {n d : ℕ}
    (S : robust_dataset n d) (I : Finset (Fin n)) : Matrix (Fin d) (Fin d) ℝ :=
  fun j k =>
    (I.card : ℝ)⁻¹ *
      ∑ i ∈ I,
        ((S i - empirical_mean_on S I) j) * ((S i - empirical_mean_on S I) k)

def stable_dataset {n d : ℕ}
    (S : robust_dataset n d) (ε δ : ℝ) (μ : robust_point d) : Prop :=
  0 < ε ∧ ε < (1 / 2 : ℝ) ∧ ε ≤ δ ∧
    ∀ I : Finset (Fin n), (1 - ε) * (n : ℝ) ≤ (I.card : ℝ) →
      ‖empirical_mean_on S I - μ‖ ≤ δ ∧
        ‖(empirical_covariance_on S I - 1).toEuclideanLin.toContinuousLinearMap‖ ≤ δ ^ 2 / ε

def strong_local_corruption {n d : ℕ}
    (S₀ S : robust_dataset n d) (ρ : ℝ) : Prop :=
  ∀ v : robust_point d, ‖v‖ = 1 →
    (n : ℝ)⁻¹ * ∑ i : Fin n, |inner ℝ v (S i - S₀ i)| ≤ ρ

def global_corruption {n d : ℕ}
    (S T : robust_dataset n d) (ε : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∃ I : Finset (Fin n),
    (1 - ε) * (n : ℝ) ≤ (I.card : ℝ) ∧ ∀ i ∈ I, T (σ i) = S i

def combined_corruption {n d : ℕ}
    (S₀ T : robust_dataset n d) (ε ρ : ℝ) : Prop :=
  ∃ S : robust_dataset n d,
    strong_local_corruption S₀ S ρ ∧ global_corruption S T ε

abbrev stability_estimator (n d : ℕ) (Ω : Type*) :=
  robust_dataset n d → ℝ → ℝ → Ω → robust_point d

def stability_based_algorithm {n d : ℕ} {Ω : Type*}
    (highProbability : (Ω → Prop) → Prop) (runsInPolynomialTime : Prop)
    (A : stability_estimator n d Ω) (K : ℝ) : Prop :=
  runsInPolynomialTime ∧ 0 < K ∧
    ∀ (S T₀ T : robust_dataset n d) (μ : robust_point d) (ε η ρ : ℝ),
      stable_dataset S ε η μ →
      global_corruption S T₀ ε →
      strong_local_corruption T₀ T ρ →
      ρ ≤ η →
      highProbability (fun ω => ‖A T ε η ω - μ‖ ≤ K * η)

theorem mean_estimation :
    ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧
      ∀ {n d : ℕ} {Ω : Type*}
        (highProbability : (Ω → Prop) → Prop) (runsInPolynomialTime : Prop)
        (A : stability_estimator n d Ω) (K : ℝ)
        (S₀ T : robust_dataset n d) (μ : robust_point d)
        (c C ε δ ρ : ℝ),
        stability_based_algorithm highProbability runsInPolynomialTime A K →
        0 < c → c ≤ c₀ → C₀ ≤ C → 0 < ε → ε < c → 0 < ρ → ε < δ →
        stable_dataset S₀ ε δ μ →
        combined_corruption S₀ T ε ρ →
        highProbability
          (fun ω =>
            ‖A T ε (C * (δ + ρ)) ω - μ‖ ≤
              K * (C * (δ + ρ))) := by sorry

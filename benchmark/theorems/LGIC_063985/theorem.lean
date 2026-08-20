import Mathlib

noncomputable def empirical_noise_rate {U : Type*} (L : Set U) (x : ℕ → U) (n : ℕ) : ℝ :=
  (Set.ncard {t : ℕ | t < n ∧ x t ∉ L} : ℝ) / (n : ℝ)

def generation_in_the_limit {U : Type*} (G : (ℕ → U) → ℕ → U) (K : Set U) (x : ℕ → U) : Prop :=
  ∃ nStar : ℕ, ∀ n : ℕ, nStar ≤ n → G x n ∈ K

def element_based {U : Type*} (G : (ℕ → U) → ℕ → U) : Prop :=
  ∀ (x : ℕ → U) (n : ℕ), G x n ∉ (x '' Set.Iic n ∪ (fun m => G x m) '' Set.Iio n)

def enumeration_o1_noise_omission {U : Type*} (x : ℕ → U) (K : Set U) : Prop :=
  ∃ Khat : Set U, Khat ⊆ K ∧ Khat.Infinite ∧
    (∀ a ∈ Khat, ∃! t : ℕ, x t = a) ∧
    Filter.Tendsto (fun n => empirical_noise_rate Khat x n) Filter.atTop (nhds (0 : ℝ))

theorem vanishing_noise_generation {U : Type*} [Infinite U] :
    ∃ G : (ℕ → Set U) → (ℕ → U) → ℕ → U,
      ∀ (L : ℕ → Set U),
        element_based (G L) ∧
        (∀ (x y : ℕ → U) (n : ℕ),
          (∀ t ∈ Set.Iic n, x t = y t) →
          G L x n = G L y n) ∧
        ∀ (istar : ℕ) (x : ℕ → U),
          (∀ i, (L i).Infinite) →
          enumeration_o1_noise_omission x (L istar) →
          generation_in_the_limit (G L) (L istar) x := by sorry

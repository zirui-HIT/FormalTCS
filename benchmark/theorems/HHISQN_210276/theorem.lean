import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi

set_option maxHeartbeats 500000

open scoped BigOperators

noncomputable section

structure partite_distribution (d : ℕ) where
  Face : Type
  [faceFintype : Fintype Face]
  Coord : Fin d → Type
  [coordFintype : ∀ i, Fintype (Coord i)]
  coordinate : (x : Face) → (i : Fin d) → Coord i
  coordinate_injective : ∀ {x y : Face}, (∀ i, coordinate x i = coordinate y i) → x = y
  weight : Face → ℝ
  weight_nonnegative : ∀ x, 0 ≤ weight x
  weight_sum_one : ∑ x, weight x = 1

def partite_agree_on {d : ℕ} (X : partite_distribution d) (S : Finset (Fin d))
    (x z : X.Face) : Prop :=
  ∀ i, i ∈ S → X.coordinate x i = X.coordinate z i

noncomputable def partite_fiber_mass {d : ℕ} (X : partite_distribution d)
    (S : Finset (Fin d)) (z : X.Face) : ℝ := by
  classical
  letI : Fintype X.Face := X.faceFintype
  exact ∑ x, if partite_agree_on X S x z then X.weight x else 0

noncomputable def partite_conditional_expectation {d : ℕ} (X : partite_distribution d)
    (S : Finset (Fin d)) (f : X.Face → ℝ) (z : X.Face) : ℝ := by
  classical
  letI : Fintype X.Face := X.faceFintype
  let m := partite_fiber_mass X S z
  exact if m = 0 then 0
    else (∑ x, if partite_agree_on X S x z then X.weight x * f x else 0) / m

noncomputable def partite_qnorm {d : ℕ} (X : partite_distribution d)
    (q : ℝ) (f : X.Face → ℝ) : ℝ := by
  classical
  letI : Fintype X.Face := X.faceFintype
  exact Real.rpow (∑ x, X.weight x * Real.rpow |f x| q) (1 / q)

noncomputable def conditioned_coordinate_mass {d : ℕ} (X : partite_distribution d)
    (S : Finset (Fin d)) (z : X.Face) (i : Fin d) (a : X.Coord i) : ℝ := by
  classical
  letI : Fintype X.Face := X.faceFintype
  exact ∑ x, if partite_agree_on X S x z ∧ X.coordinate x i = a then X.weight x else 0

noncomputable def conditioned_coordinate_qnorm {d : ℕ} (X : partite_distribution d)
    (S : Finset (Fin d)) (z : X.Face) (i : Fin d) (q : ℝ)
    (g : X.Coord i → ℝ) : ℝ := by
  classical
  letI : Fintype (X.Coord i) := X.coordFintype i
  let m := partite_fiber_mass X S z
  exact if m = 0 then 0 else
    Real.rpow
      (∑ a, conditioned_coordinate_mass X S z i a / m * Real.rpow |g a| q)
      (1 / q)

noncomputable def conditioned_marginal_average {d : ℕ} (X : partite_distribution d)
    (S : Finset (Fin d)) (z : X.Face) (i j : Fin d)
    (g : X.Coord j → ℝ) (a : X.Coord i) : ℝ := by
  classical
  letI : Fintype X.Face := X.faceFintype
  let m := conditioned_coordinate_mass X S z i a
  exact if m = 0 then 0 else
    (∑ x, if partite_agree_on X S x z ∧ X.coordinate x i = a
      then X.weight x * g (X.coordinate x j) else 0) / m

noncomputable def conditioned_stationary_average {d : ℕ} (X : partite_distribution d)
    (S : Finset (Fin d)) (z : X.Face) (j : Fin d)
    (g : X.Coord j → ℝ) : ℝ :=
  partite_conditional_expectation X S (fun x => g (X.coordinate x j)) z

noncomputable def conditioned_marginal_deviation {d : ℕ} (X : partite_distribution d)
    (S : Finset (Fin d)) (z : X.Face) (i j : Fin d)
    (g : X.Coord j → ℝ) : X.Coord i → ℝ :=
  fun a => conditioned_marginal_average X S z i j g a -
    conditioned_stationary_average X S z j g

def is_q_gamma_product {d : ℕ} (X : partite_distribution d) (q γ : ℝ) : Prop :=
  ∀ (S : Finset (Fin d)) (z : X.Face) (i j : Fin d),
    i ∉ S → j ∉ S → i ≠ j → 0 < partite_fiber_mass X S z →
      ∀ g : X.Coord j → ℝ,
        conditioned_coordinate_qnorm X S z i q
            (conditioned_marginal_deviation X S z i j g) ≤
          γ * conditioned_coordinate_qnorm X S z j q g

noncomputable def efron_stein_component {d : ℕ} (X : partite_distribution d)
    (S : Finset (Fin d)) (f : X.Face → ℝ) : X.Face → ℝ := by
  classical
  exact fun z => ∑ T ∈ S.powerset,
    (-1 : ℝ) ^ (S.card - T.card) * partite_conditional_expectation X T f z

noncomputable def generalized_noise {d : ℕ} (X : partite_distribution d)
    (r : Fin d → ℝ) (f : X.Face → ℝ) : X.Face → ℝ := by
  classical
  exact fun x => ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
    (∏ i ∈ S, r i) * efron_stein_component X S f x

noncomputable def scalar_noise {d : ℕ} (X : partite_distribution d)
    (ρ : ℝ) (f : X.Face → ℝ) : X.Face → ℝ := by
  classical
  exact fun x => ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
    ρ ^ S.card * efron_stein_component X S f x

def rademacher_sign : Bool → ℝ
  | false => -1
  | true => 1

noncomputable def partite_symmetrization {d : ℕ} (X : partite_distribution d)
    (g : X.Face → ℝ) (r : Fin d → Bool) (x : X.Face) : ℝ :=
  generalized_noise X (fun i => rademacher_sign (r i)) g x

noncomputable def symmetrized_qnorm {d : ℕ} (X : partite_distribution d)
    (q : ℝ) (g : X.Face → ℝ) : ℝ := by
  classical
  letI : Fintype X.Face := X.faceFintype
  exact Real.rpow
    (((2 : ℝ) ^ d)⁻¹ * ∑ r : Fin d → Bool, ∑ x,
      X.weight x * Real.rpow |partite_symmetrization X g r x| q)
    (1 / q)

noncomputable def exponential_error (growth : ℝ) (d : ℕ) (γ : ℝ) : ℝ :=
  Real.rpow 2 (growth * (d : ℝ)) * γ

def exponentially_small (decay : ℝ) (d : ℕ) (γ : ℝ) : Prop :=
  γ ≤ Real.rpow 2 (-(decay * (d : ℝ)))

def upper_symmetrization_bound (q decay growth : ℝ) : Prop :=
  ∀ (d : ℕ) (X : partite_distribution d) (γ : ℝ) (f : X.Face → ℝ),
    0 ≤ γ → is_q_gamma_product X q γ → exponentially_small decay d γ →
      partite_qnorm X q f ≤
        (1 + exponential_error growth d γ) *
          symmetrized_qnorm X q (scalar_noise X 2 f)

def lower_symmetrization_bound (q c decay growth : ℝ) : Prop :=
  ∀ (d : ℕ) (X : partite_distribution d) (γ : ℝ) (f : X.Face → ℝ),
    0 ≤ γ → is_q_gamma_product X q γ → exponentially_small decay d γ →
      (1 - exponential_error growth d γ) *
          symmetrized_qnorm X q (scalar_noise X c f) ≤
        partite_qnorm X q f

theorem symmetrization (q : ℝ) (hq : 1 < q) :
    ∃ c_q decay growth : ℝ,
      0 ≤ c_q ∧ c_q ≤ 1 ∧ 0 < decay ∧ 0 < growth ∧
        upper_symmetrization_bound q decay growth ∧
        lower_symmetrization_bound q c_q decay growth := by sorry

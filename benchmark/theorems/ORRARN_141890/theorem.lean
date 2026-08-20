import Mathlib

set_option linter.all false
set_option maxHeartbeats 500000

variable {X Y : Type*}

def approx_pseudometric (c : ℝ) (ℓ : Y → Y → ℝ) : Prop :=
  1 ≤ c ∧ (∀ y, ℓ y y = 0) ∧ (∀ y₁ y₂, ℓ y₁ y₂ = ℓ y₂ y₁) ∧
    ∀ y₁ y₂ y₃, ℓ y₁ y₂ ≤ c * (ℓ y₁ y₃ + ℓ y₂ y₃)

noncomputable def induced_metric (ℓ : Y → Y → ℝ) (f g : X → Y) : ℝ :=
  ⨆ x, ℓ (f x) (g x)

noncomputable def diameter (ℓ : Y → Y → ℝ) (H : Set (X → Y)) : ℝ :=
  ⨆ (f : H) (g : H), induced_metric ℓ f.1 g.1

def finite_diameter (ℓ : Y → Y → ℝ) (H : Set (X → Y)) : Prop :=
  ∃ M : ℝ, ∀ f ∈ H, ∀ g ∈ H, ∀ x, ℓ (f x) (g x) ≤ M

noncomputable def covering_number (ℓ : Y → Y → ℝ) (H : Set (X → Y)) (U : Set (X → Y))
    (ε : ℝ) : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ S : Finset (X → Y), (↑S : Set (X → Y)) ⊆ H ∧ (S.card : ℕ∞) = n ∧
    ∀ u ∈ U, ∃ s ∈ S, induced_metric ℓ u s ≤ ε}

noncomputable def entropy_potential (ℓ : Y → Y → ℝ) (H : Set (X → Y)) (U : Set (X → Y)) : ENNReal :=
  MeasureTheory.lintegral
    (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) (diameter ℓ H)))
    (fun ε => if covering_number ℓ H U ε = ⊤ then (⊤ : ENNReal)
      else ENNReal.ofReal (Real.logb 2 (covering_number ℓ H U ε).toENNReal.toReal))

structure scaled_tree (X Y : Type*) where
  inst : List Bool → X
  edge : List Bool → Bool → Y

def branch_prefix (b : ℕ → Bool) (t : ℕ) : List Bool :=
  (List.range t).map b

def node_gap (ℓ : Y → Y → ℝ) (T : scaled_tree X Y) (u : List Bool) : ℝ :=
  ℓ (T.edge u false) (T.edge u true)

def realizable_tree (H : Set (X → Y)) (T : scaled_tree X Y) : Prop :=
  ∀ b : ℕ → Bool, ∀ n : ℕ, ∃ h ∈ H, ∀ t < n,
    h (T.inst (branch_prefix b t)) = T.edge (branch_prefix b t) (b t)

noncomputable def online_dim (ℓ : Y → Y → ℝ) (H : Set (X → Y)) : ENNReal :=
  ⨆ (T : scaled_tree X Y) (_ : realizable_tree H T),
    ⨅ b : ℕ → Bool, ∑' t : ℕ, ENNReal.ofReal (node_gap ℓ T (branch_prefix b t))

theorem intro_Donl_via_Phi (ℓ : Y → Y → ℝ) (c : ℝ) (H : Set (X → Y))
    (hℓ : approx_pseudometric c ℓ) (hdiam : finite_diameter ℓ H) :
    online_dim ℓ H ≤ ENNReal.ofReal (4 * c) * entropy_potential ℓ H H := by
  sorry

import Mathlib

set_option linter.all false
set_option maxHeartbeats 500000

abbrev Dataset (X : Type*) : Type _ := List (X × Bool)

def Realizable {X : Type*} (H : Set (X → Bool)) (D : Dataset X) : Prop :=
  ∃ h ∈ H, ∀ p ∈ D, h p.1 = p.2

def ShattersSet {X : Type*} (H : Set (X → Bool)) (S : Finset X) : Prop :=
  ∀ f : X → Bool, ∃ h ∈ H, ∀ x ∈ S, h x = f x

def VCDimLE {X : Type*} (H : Set (X → Bool)) (d : ℕ) : Prop :=
  ∀ S : Finset X, ShattersSet H S → S.card ≤ d

def IsShatteredLittlestoneTree {X : Type*} (H : Set (X → Bool)) (ℓ : ℕ)
    (label : List Bool → X) : Prop :=
  ∀ branch : List Bool, branch.length = ℓ →
    ∃ h ∈ H, ∀ i : Fin ℓ, h (label (branch.take (i : ℕ))) = branch.getD (i : ℕ) false

def LittlestoneDimLE {X : Type*} (H : Set (X → Bool)) (d : ℕ) : Prop :=
  ∀ ℓ : ℕ, (∃ label : List Bool → X, IsShatteredLittlestoneTree H ℓ label) → ℓ ≤ d

def ApproxClose (ε δ : ℝ) (P Q : PMF Bool) : Prop :=
  ∀ W' : Set Bool, (P.toOuterMeasure W').toReal ≤ Real.exp ε * (Q.toOuterMeasure W').toReal + δ

structure LUScheme (X : Type*) (H : Set (X → Bool)) (ε δ : ℝ) where
  learn : Dataset X → PMF (Bool × List Bool)
  unlearn : Dataset X → List Bool → PMF Bool
  learn_correct : ∀ D, ∀ p ∈ (learn D).support, (p.1 = true ↔ Realizable H D)
  unlearn_close : ∀ keep remove : Dataset X,
    ApproxClose ε δ
      ((learn (keep ++ remove)).bind (fun p => unlearn remove p.2))
      ((learn keep).map Prod.fst)
  space : ℕ → ℝ
  space_isLUB : ∀ n : ℕ, IsLUB
    { r : ℝ | ∃ (D : Dataset X) (p : Bool × List Bool),
        D.length = n ∧ p ∈ (learn D).support ∧ r = (p.2.length : ℝ) } (space n)

structure TiLUScheme (X : Type*) (H : Set (X → Bool)) (ε δ : ℝ) where
  learn : Dataset X → PMF (Bool × List Bool × List (List Bool))
  unlearn : Dataset X → List Bool → List (List Bool) → PMF Bool
  learn_correct : ∀ D, ∀ p ∈ (learn D).support, (p.1 = true ↔ Realizable H D)
  unlearn_close : ∀ (keep remove : Dataset X) (ticketsRemove : List (List Bool)),
    ApproxClose ε δ
      ((learn (keep ++ remove)).bind (fun p => unlearn remove p.2.1 ticketsRemove))
      ((learn keep).map Prod.fst)
  space : ℕ → ℝ
  space_isLUB : ∀ n : ℕ, IsLUB
    { r : ℝ | ∃ (D : Dataset X) (p : Bool × List Bool × List (List Bool)),
        D.length = n ∧ p ∈ (learn D).support ∧
        r = max (p.2.1.length : ℝ) (((p.2.2.map List.length).foldr max 0 : ℕ) : ℝ) } (space n)

def IsSpaceLowerBound (s g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in Filter.atTop, c * g n ≤ s n

theorem vc_space_lower_bound (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (ε δ : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hδ : δ ∈ Set.Ico (0 : ℝ) (1 / 2)) :
    ∃ (X : Type) (H : Set (X → Bool)) (d : ℕ),
      Finite X ∧ LittlestoneDimLE H d ∧ VCDimLE H d ∧ (d : ℝ) ≤ 1 / β + 1 ∧
      (∀ S : LUScheme X H ε δ,
        IsSpaceLowerBound S.space (fun n => (1 - Real.binEntropy δ) * (n : ℝ))) ∧
      (∀ T : TiLUScheme X H ε δ,
        IsSpaceLowerBound T.space
          (fun n => β * (1 - Real.binEntropy δ) * (n : ℝ) ^ (1 - β))) := by sorry

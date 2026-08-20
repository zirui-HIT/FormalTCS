import Mathlib

set_option linter.all false
set_option maxHeartbeats 500000

open Classical

noncomputable def erasureFrac {n : ℕ} {α : Type*} [DecidableEq α]
    (g : Fin n → Option α) : ℝ :=
  ((Finset.univ.filter (fun i => g i = none)).card : ℝ) / (n : ℝ)

noncomputable def erasureDist {n : ℕ} {α : Type*} [DecidableEq α]
    (g : Fin n → Option α) (h : Fin n → α) : ℝ :=
  ((Finset.univ.filter (fun i => g i ≠ none ∧ g i ≠ some (h i))).card : ℝ) / (n : ℝ)

def AvgRadiusLDCErasures {n : ℕ} {α : Type*} [DecidableEq α]
    (C : Set (Fin n → α)) (δ : ℝ) (k : ℕ) (ε : ℝ) : Prop :=
  ∀ (g : Fin n → Option α) (H : Finset (Fin n → α)),
    (↑H : Set (Fin n → α)) ⊆ C → 1 ≤ H.card → H.card ≤ k →
    ((H.card : ℝ) - 1) * (δ - erasureFrac g - ε) ≤ ∑ h ∈ H, erasureDist g h

structure ExpanderGraph (n d : ℕ) (lam : ℝ) where
  nbrs : Fin n → Finset (Fin n)
  leftReg : ∀ ℓ : Fin n, (nbrs ℓ).card = d
  rightReg : ∀ r : Fin n, (Finset.univ.filter (fun ℓ : Fin n => r ∈ nbrs ℓ)).card = d
  mixing : ∀ S T : Finset (Fin n),
      |(∑ ℓ ∈ S, ((nbrs ℓ ∩ T).card : ℝ))
          - (d : ℝ) / (n : ℝ) * (S.card : ℝ) * (T.card : ℝ)|
        ≤ lam * (d : ℝ) * (n : ℝ)

structure AELCode (n d : ℕ) (lam δout : ℝ) (α : Type*) [DecidableEq α] where
  G : ExpanderGraph n d lam
  outer : Set (Fin n → α)
  inner : Set (Fin d → α)
  code : Set (Fin n → (Fin d → α))
  innerEnc : α → (Fin d → α)
  hEncMem : ∀ a : α, innerEnc a ∈ inner
  hEncInj : Function.Injective innerEnc
  edge : (Fin n × Fin d) ≃ (Fin n × Fin d)
  hEdgeMem : ∀ (ℓ : Fin n) (i : Fin d), (edge (ℓ, i)).1 ∈ G.nbrs ℓ
  hEdgeInj : ∀ ℓ : Fin n, Function.Injective (fun i : Fin d => (edge (ℓ, i)).1)
  hCode : code =
      (fun c : Fin n → α =>
        fun r : Fin n => fun j : Fin d =>
          innerEnc (c (edge.symm (r, j)).1) ((edge.symm (r, j)).2)) '' outer
  hOuterDist : ∀ x ∈ outer, ∀ y ∈ outer, x ≠ y →
      δout ≤ ((Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card : ℝ) / (n : ℝ)

theorem main_technical_avg {n d k0 : ℕ} {lam δ0 δout ε : ℝ} {α : Type*} [DecidableEq α]
    (hk : 1 ≤ k0) (hε : 0 < ε)
    (A : AELCode n d lam δout α)
    (hinner : AvgRadiusLDCErasures A.inner δ0 k0 (ε / 2))
    (hlam : lam ≤ δout / (6 * (k0 : ℝ) ^ k0) * ε) :
    AvgRadiusLDCErasures A.code δ0 k0 ε := by sorry

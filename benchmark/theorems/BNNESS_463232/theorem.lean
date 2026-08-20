import Mathlib

namespace NNE

def relu (x : ℝ) : ℝ := max x 0

def reluV {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

inductive ReLURep (n : ℕ) : (k m : ℕ) → ((Fin n → ℝ) → (Fin m → ℝ)) → Prop where
  | zero {m : ℕ} (A : (Fin n → ℝ) →ᵃ[ℝ] (Fin m → ℝ)) :
      ReLURep n 0 m (fun x => A x)
  | succ {k m p : ℕ} {g : (Fin n → ℝ) → (Fin p → ℝ)}
      (hg : ReLURep n k p g) (A : (Fin p → ℝ) →ᵃ[ℝ] (Fin m → ℝ)) :
      ReLURep n (k + 1) m (fun x => A (reluV (g x)))

def ReLUClass (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ g : (Fin n → ℝ) → (Fin 1 → ℝ), ReLURep n k 1 g ∧ ∀ x, f x = g x 0}

noncomputable def MAXf {k : ℕ} (x : Fin k → ℝ) : ℝ :=
  if h : (Finset.univ : Finset (Fin k)).Nonempty then Finset.univ.sup' h x else 0

theorem thm1 (n : ℕ) (hn : 1 ≤ n) :
    (MAXf : (Fin (3 ^ n + 2) → ℝ) → ℝ) ∈ ReLUClass (3 ^ n + 2) (n + 1) := by sorry

end NNE

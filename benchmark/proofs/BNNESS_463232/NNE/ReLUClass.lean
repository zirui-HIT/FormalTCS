/-
Copyright (c) 2026 Anthony Chang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Chang
-/
import Mathlib
import NNE.ReLU
import NNE.ReLUk

/-!
Helper file to compose the ReLU class.
-/

namespace NNE

/-- `ReLU_{n,k}`: scalar functions on `ℝⁿ` computed by a ReLU network with at most
`k` hidden layers. The scalar output is the single coordinate of a width-one vector
output of `ReLUk`; "at most `k`" is free from `ReLUk.mono`. -/
def ReLUClass (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ReLUk k (fun x (_ : Fin 1) => f x)}

@[simp] lemma mem_ReLUClass {n k : ℕ} {f : (Fin n → ℝ) → ℝ} :
    f ∈ ReLUClass n k ↔ ReLUk k (fun x (_ : Fin 1) => f x) := Iff.rfl

lemma ReLUClass_mono {n k k' : ℕ} (h : k ≤ k') : ReLUClass n k ⊆ ReLUClass n k' :=
  fun _ hf => (mem_ReLUClass.mp hf).mono h

/-! ### Closure properties -/

/-- The affine map `(u, v) ↦ u + v` on width-one pairs. -/
private noncomputable def sumFunnel : (Fin (1 + 1) → ℝ) →ᵃ[ℝ] (Fin 1 → ℝ) :=
  (LinearMap.pi fun _ : Fin 1 => projₗ 0 + projₗ 1).toAffineMap

/-- Affine functions lie in every `ReLUClass`. -/
lemma affine_mem_ReLUClass {n : ℕ} (φ : (Fin n → ℝ) →ᵃ[ℝ] ℝ) (k : ℕ) :
    (fun x => φ x) ∈ ReLUClass n k := by
  have h0 : ReLUk 0 (fun x (_ : Fin 1) => φ x) := by
    have h := ReLUk.affine (AffineMap.pi fun _ : Fin 1 => φ)
    have e : (fun x => (AffineMap.pi fun _ : Fin 1 => φ) x) = fun x (_ : Fin 1) => φ x := by
      funext x i; simp [AffineMap.pi_apply]
    rwa [e] at h
  exact mem_ReLUClass.mpr (h0.mono (Nat.zero_le k))

/-- Constants lie in every `ReLUClass`. -/
lemma const_mem_ReLUClass {n : ℕ} (c : ℝ) (k : ℕ) :
    (fun _ : Fin n → ℝ => c) ∈ ReLUClass n k := by
  have h := affine_mem_ReLUClass (AffineMap.const ℝ (Fin n → ℝ) c) k
  simpa using h

/-- `ReLUClass` is closed under pointwise addition. -/
lemma ReLUClass.add {n k : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (hf : f ∈ ReLUClass n k) (hg : g ∈ ReLUClass n k) :
    (fun x => f x + g x) ∈ ReLUClass n k := by
  have hp := ReLUk.append (mem_ReLUClass.mp hf) (mem_ReLUClass.mp hg)
  have hc := hp.comp_affine_left sumFunnel
  refine mem_ReLUClass.mpr ?_
  have e : (fun x => sumFunnel (Fin.append (fun _ : Fin 1 => f x) (fun _ : Fin 1 => g x)))
      = fun x (_ : Fin 1) => f x + g x := by
    funext x i
    rfl
  rwa [e] at hc

/-- `ReLUClass` is closed under scalar multiples. -/
lemma ReLUClass.smul {n k : ℕ} {f : (Fin n → ℝ) → ℝ} (c : ℝ)
    (hf : f ∈ ReLUClass n k) : (fun x => c * f x) ∈ ReLUClass n k := by
  have hc := (mem_ReLUClass.mp hf).comp_affine_left
    ((c • LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)).toAffineMap)
  refine mem_ReLUClass.mpr ?_
  have e : (fun x => ((c • LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)).toAffineMap :
        (Fin 1 → ℝ) →ᵃ[ℝ] (Fin 1 → ℝ)) ((fun x (_ : Fin 1) => f x) x))
      = fun x (_ : Fin 1) => c * f x := by
    funext x i
    rfl
  rwa [e] at hc

/-- `ReLUClass` is closed under negation. -/
lemma ReLUClass.neg {n k : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : f ∈ ReLUClass n k) : (fun x => -f x) ∈ ReLUClass n k := by
  have h := ReLUClass.smul (-1) hf
  have e : (fun x => (-1 : ℝ) * f x) = fun x => -f x := by
    funext x; ring
  rwa [e] at h

/-- `ReLUClass` is closed under pointwise subtraction. -/
lemma ReLUClass.sub {n k : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (hf : f ∈ ReLUClass n k) (hg : g ∈ ReLUClass n k) :
    (fun x => f x - g x) ∈ ReLUClass n k := by
  have h := ReLUClass.add hf (ReLUClass.neg hg)
  have e : (fun x => f x + -g x) = fun x => f x - g x := by
    funext x; ring
  rwa [e] at h

/-- `ReLUClass` is closed under pointwise maxima, at the cost of one layer. -/
lemma ReLUClass.sup {n k : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (hf : f ∈ ReLUClass n k) (hg : g ∈ ReLUClass n k) :
    (fun x => f x ⊔ g x) ∈ ReLUClass n (k + 1) := by
  have hp := ReLUk.append (mem_ReLUClass.mp hf) (mem_ReLUClass.mp hg)
  have hc := ReLUk.comp ReLUk.max2 hp
  refine mem_ReLUClass.mpr ?_
  have e : (fun x => (fun v : Fin (1 + 1) → ℝ => (fun _ : Fin 1 => v 0 ⊔ v 1))
        (Fin.append (fun _ : Fin 1 => f x) (fun _ : Fin 1 => g x)))
      = fun x (_ : Fin 1) => f x ⊔ g x := by
    funext x i
    change Fin.append (fun _ : Fin 1 => f x) (fun _ : Fin 1 => g x) 0
        ⊔ Fin.append (fun _ : Fin 1 => f x) (fun _ : Fin 1 => g x) 1 = f x ⊔ g x
    rfl
  rwa [e] at hc

end NNE

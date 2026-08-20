/-
Copyright (c) 2026 Anthony Chang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Chang
-/
import Mathlib
import NNE.ReLU

/-!
# ReLU network function classes

`ReLUk k f` says that the (vector-valued) function `f : (Fin n → ℝ) → (Fin m → ℝ)`
is computed by a ReLU network with `k` hidden layers, i.e.

  `f = T⁽ᵏ⁺¹⁾ ∘ ReLU ∘ T⁽ᵏ⁾ ∘ ⋯ ∘ ReLU ∘ T⁽¹⁾`

for affine maps `T⁽ⁱ⁾`.
-/

namespace NNE

/-- `ReLUk k f`: the function `f` is computed by a ReLU network with `k` hidden
layers. `ReLUk 0` is the affine maps; `layer` adds one `affine ∘ ReLU` on top. -/
inductive ReLUk : ∀ {n m : ℕ}, ℕ → ((Fin n → ℝ) → (Fin m → ℝ)) → Prop
  | affine {n m : ℕ} (T : (Fin n → ℝ) →ᵃ[ℝ] (Fin m → ℝ)) :
      ReLUk 0 (fun x => T x)
  | layer {n p m k : ℕ} {g : (Fin n → ℝ) → (Fin p → ℝ)}
      (hg : ReLUk k g) (T : (Fin p → ℝ) →ᵃ[ℝ] (Fin m → ℝ)) :
      ReLUk (k + 1) (fun x => T (reluV (g x)))

/-- Post-composing a network with an affine map keeps the hidden-layer count:
the new affine map folds into the top layer. -/
lemma ReLUk.comp_affine_left {n m m' k : ℕ} {f : (Fin n → ℝ) → (Fin m → ℝ)}
    (hf : ReLUk k f) (S : (Fin m → ℝ) →ᵃ[ℝ] (Fin m' → ℝ)) :
    ReLUk k (fun x => S (f x)) := by
  cases hf with
  | affine T => exact .affine (S.comp T)
  | layer hg T => exact .layer hg (S.comp T)

/-- Pre-composing a network with an affine map keeps the hidden-layer count:
the new affine map folds into the bottom (first) layer. -/
lemma ReLUk.comp_affine_right {n n' m k : ℕ} {f : (Fin n → ℝ) → (Fin m → ℝ)}
    (hf : ReLUk k f) (A : (Fin n' → ℝ) →ᵃ[ℝ] (Fin n → ℝ)) :
    ReLUk k (fun x => f (A x)) := by
  induction hf with
  | affine T => exact .affine (T.comp A)
  | layer hg T ih => exact .layer ih T

/-- The componentwise ReLU is a one-hidden-layer network. -/
lemma ReLUk.reluV_one {n : ℕ} : ReLUk 1 (reluV (n := n)) := by
  have h := ReLUk.layer (ReLUk.affine (AffineMap.id ℝ (Fin n → ℝ)))
    (AffineMap.id ℝ (Fin n → ℝ))
  simpa using h

/-- The identity on `Fin m → ℝ` realized through a single ReLU layer of width
`m + m`: send `y ↦ (y, -y)`, apply `ReLU`, then subtract the two halves.  Since
`relu t - relu (-t) = t`, this recovers `y`.  This is the gadget behind depth
monotonicity. -/
private lemma exists_reluId (m : ℕ) :
    ∃ (A₁ : (Fin m → ℝ) →ᵃ[ℝ] (Fin (m + m) → ℝ))
      (A₂ : (Fin (m + m) → ℝ) →ᵃ[ℝ] (Fin m → ℝ)),
      ∀ y : Fin m → ℝ, A₂ (reluV (A₁ y)) = y := by
  -- Write `y` into a width-`m + m` vector as `(y, -y)`: first block `y`, second block `-y`.
  let dup : (Fin m → ℝ) →ₗ[ℝ] (Fin (m + m) → ℝ) :=
    LinearMap.pi fun j => Fin.addCases (fun i => LinearMap.proj i) (fun i => -LinearMap.proj i) j
  -- Recombine a width-`m + m` vector as `first block - second block`.
  let merge : (Fin (m + m) → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    LinearMap.funLeft ℝ ℝ (Fin.castAdd m) - LinearMap.funLeft ℝ ℝ (Fin.natAdd m)
  -- A ReLU in between turns coordinate `i` into `relu (y i) - relu (-(y i)) = y i`.
  refine ⟨dup.toAffineMap, merge.toAffineMap, fun y => funext fun i => ?_⟩
  simp only [dup, merge, LinearMap.coe_toAffineMap, LinearMap.pi_apply, LinearMap.sub_apply,
    Pi.sub_apply, LinearMap.funLeft_apply, LinearMap.neg_apply, LinearMap.proj_apply,
    Fin.addCases_left, Fin.addCases_right, reluV_apply, relu_sub_relu_neg]

/-- Adding one hidden layer: `ReLUk` is monotone in the depth (single step). -/
lemma ReLUk.succ {n m k : ℕ} {f : (Fin n → ℝ) → (Fin m → ℝ)} (hf : ReLUk k f) :
    ReLUk (k + 1) f := by
  obtain ⟨A₁, A₂, hid⟩ := exists_reluId m
  have key : ReLUk (k + 1) (fun x => A₂ (reluV (A₁ (f x)))) :=
    .layer (hf.comp_affine_left A₁) A₂
  have hfun : (fun x => A₂ (reluV (A₁ (f x)))) = f := funext fun x => hid (f x)
  rwa [hfun] at key

/-- `ReLUk` is monotone in the depth: more hidden layers can only compute more. -/
lemma ReLUk.mono {n m k k' : ℕ} {f : (Fin n → ℝ) → (Fin m → ℝ)}
    (hf : ReLUk k f) (h : k ≤ k') : ReLUk k' f := by
  induction h with
  | refl => exact hf
  | step _ ih => exact ih.succ

/-- Stacking networks: composing a `k`-hidden-layer network after a `j`-hidden-layer
network gives a `j + k`-hidden-layer network (the two affine maps at the junction
merge into one). -/
lemma ReLUk.comp {n p q j k : ℕ} {f : (Fin n → ℝ) → (Fin p → ℝ)}
    {g : (Fin p → ℝ) → (Fin q → ℝ)} (hg : ReLUk k g) (hf : ReLUk j f) :
    ReLUk (j + k) (fun x => g (f x)) := by
  induction hg with
  | affine T => simpa using hf.comp_affine_left T
  | layer _ T ih => exact .layer ih T

/-! ### Affine auxiliaries -/

/-- Coordinate projection as a linear functional, with the scalars fixed to `ℝ`. -/
def projₗ {n : ℕ} (i : Fin n) : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.proj i

@[simp] lemma projₗ_apply {n : ℕ} (i : Fin n) (x : Fin n → ℝ) : projₗ i x = x i := rfl

/-- Affine maps expand along rays. -/
lemma affine_apply_add_smul {n p : ℕ} (A : (Fin n → ℝ) →ᵃ[ℝ] (Fin p → ℝ))
    (z w : Fin n → ℝ) (t : ℝ) : A (z + t • w) = A z + t • A.linear w := by
  rw [show z + t • w = t • w +ᵥ z from by rw [vadd_eq_add, add_comm]]
  rw [A.map_vadd, map_smul, vadd_eq_add, add_comm]

lemma affine_apply_sub_smul {n p : ℕ} (A : (Fin n → ℝ) →ᵃ[ℝ] (Fin p → ℝ))
    (z w : Fin n → ℝ) (t : ℝ) : A (z - t • w) = A z - t • A.linear w := by
  have h := affine_apply_add_smul A z w (-t)
  rw [show z + (-t) • w = z - t • w from by rw [neg_smul]; abel] at h
  rw [h, neg_smul]
  abel

/-- Glue two affine maps into one with `Fin.append`ed codomain. -/
noncomputable def affineAppend {n m₁ m₂ : ℕ} (T₁ : (Fin n → ℝ) →ᵃ[ℝ] (Fin m₁ → ℝ))
    (T₂ : (Fin n → ℝ) →ᵃ[ℝ] (Fin m₂ → ℝ)) : (Fin n → ℝ) →ᵃ[ℝ] (Fin (m₁ + m₂) → ℝ) :=
  AffineMap.pi (Fin.addCases (motive := fun _ => (Fin n → ℝ) →ᵃ[ℝ] ℝ)
    (fun i => (AffineMap.proj i).comp T₁) (fun j => (AffineMap.proj j).comp T₂))

lemma affineAppend_apply {n m₁ m₂ : ℕ} (T₁ : (Fin n → ℝ) →ᵃ[ℝ] (Fin m₁ → ℝ))
    (T₂ : (Fin n → ℝ) →ᵃ[ℝ] (Fin m₂ → ℝ)) (x : Fin n → ℝ) :
    affineAppend T₁ T₂ x = Fin.append (T₁ x) (T₂ x) := by
  funext k
  induction k using Fin.addCases with
  | left i => simp [affineAppend, AffineMap.pi_apply]
  | right j => simp [affineAppend, AffineMap.pi_apply]

/-- Restriction to the first block, as an affine map. -/
noncomputable def restrictL (p₁ p₂ : ℕ) : (Fin (p₁ + p₂) → ℝ) →ᵃ[ℝ] (Fin p₁ → ℝ) :=
  (LinearMap.funLeft ℝ ℝ (Fin.castAdd p₂)).toAffineMap

/-- Restriction to the second block, as an affine map. -/
noncomputable def restrictR (p₁ p₂ : ℕ) : (Fin (p₁ + p₂) → ℝ) →ᵃ[ℝ] (Fin p₂ → ℝ) :=
  (LinearMap.funLeft ℝ ℝ (Fin.natAdd p₁)).toAffineMap

lemma restrictL_append {p₁ p₂ : ℕ} (u : Fin p₁ → ℝ) (v : Fin p₂ → ℝ) :
    restrictL p₁ p₂ (Fin.append u v) = u := by
  funext i
  simp [restrictL, LinearMap.funLeft_apply]

lemma restrictR_append {p₁ p₂ : ℕ} (u : Fin p₁ → ℝ) (v : Fin p₂ → ℝ) :
    restrictR p₁ p₂ (Fin.append u v) = v := by
  funext j
  simp [restrictR, LinearMap.funLeft_apply]

/-- Zero-extension by one coordinate, as a linear map. -/
noncomputable def extZero (m : ℕ) : (Fin m → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) :=
  LinearMap.pi fun j => if h : (j : ℕ) < m then projₗ ⟨(j : ℕ), h⟩ else 0

lemma extZero_castAdd (m : ℕ) (x : Fin m → ℝ) (i : Fin m) :
    extZero m x (Fin.castAdd 1 i) = x i := by
  simp only [extZero, LinearMap.pi_apply]
  rw [dif_pos (show ((Fin.castAdd 1 i : Fin (m + 1)) : ℕ) < m from i.isLt)]
  rfl

/-! ### Parallel composition -/

/-- Two networks of the same depth on the same input can be run in parallel. -/
lemma ReLUk.append : ∀ {k n m₁ m₂ : ℕ} {f : (Fin n → ℝ) → (Fin m₁ → ℝ)}
    {g : (Fin n → ℝ) → (Fin m₂ → ℝ)}, ReLUk k f → ReLUk k g →
    ReLUk k (fun x => Fin.append (f x) (g x)) := by
  intro k
  induction k with
  | zero =>
      intro n m₁ m₂ f g hf hg
      cases hf with | affine T₁ =>
      cases hg with | affine T₂ =>
      have h : (fun x => Fin.append (T₁ x) (T₂ x)) = fun x => affineAppend T₁ T₂ x := by
        funext x; rw [affineAppend_apply]
      rw [h]
      exact .affine _
  | succ k ih =>
      intro n m₁ m₂ f g hf hg
      cases hf with | layer hf₁ T₁ =>
      cases hg with | layer hg₂ T₂ =>
      rename_i p₁ f₁ p₂ g₂
      have key := ReLUk.layer (ih hf₁ hg₂)
        (affineAppend (T₁.comp (restrictL p₁ p₂)) (T₂.comp (restrictR p₁ p₂)))
      have h : (fun x => (affineAppend (T₁.comp (restrictL p₁ p₂)) (T₂.comp (restrictR p₁ p₂)))
            (reluV (Fin.append (f₁ x) (g₂ x))))
          = fun x => Fin.append (T₁ (reluV (f₁ x))) (T₂ (reluV (g₂ x))) := by
        funext x
        rw [reluV_append, affineAppend_apply, AffineMap.comp_apply, AffineMap.comp_apply,
          restrictL_append, restrictR_append]
      rwa [h] at key

/-! ### The binary-maximum network -/

/-- First layer of the binary-max network: `(u, v) ↦ (u - v, v, -v)`. -/
private noncomputable def max2A₁ : (Fin (1 + 1) → ℝ) →ᵃ[ℝ] (Fin 3 → ℝ) :=
  (LinearMap.pi (![projₗ 0 - projₗ 1, projₗ 1, -projₗ 1] :
    Fin 3 → ((Fin (1 + 1) → ℝ) →ₗ[ℝ] ℝ))).toAffineMap

/-- Second layer of the binary-max network: `(r₀, r₁, r₂) ↦ r₀ + r₁ - r₂`. -/
private noncomputable def max2A₂ : (Fin 3 → ℝ) →ᵃ[ℝ] (Fin 1 → ℝ) :=
  (LinearMap.pi fun _ : Fin 1 => projₗ 0 + projₗ 1 - projₗ 2).toAffineMap

/-- The binary maximum `(v 0) ⊔ (v 1)` as a one-hidden-layer network. -/
lemma ReLUk.max2 : ReLUk 1 (fun v : Fin (1 + 1) → ℝ => (fun _ : Fin 1 => v 0 ⊔ v 1)) := by
  have key := ReLUk.layer (ReLUk.affine max2A₁) max2A₂
  have e : (fun v => max2A₂ (reluV (max2A₁ v)))
      = fun v : Fin (1 + 1) → ℝ => (fun _ : Fin 1 => v 0 ⊔ v 1) := by
    funext v i
    change relu (v 0 - v 1) + relu (v 1) - relu (-v 1) = v 0 ⊔ v 1
    exact relu_max_gadget (v 0) (v 1)
  rwa [e] at key

/-! ### Inversion of shallow networks -/

/-- Inversion of a one-hidden-layer network. -/
lemma ReLUk.one_inversion {n m : ℕ} {f : (Fin n → ℝ) → (Fin m → ℝ)} (h : ReLUk 1 f) :
    ∃ (p : ℕ) (A : (Fin n → ℝ) →ᵃ[ℝ] (Fin p → ℝ)) (B : (Fin p → ℝ) →ᵃ[ℝ] (Fin m → ℝ)),
      f = fun x => B (reluV (A x)) := by
  cases h with
  | layer hg T =>
      cases hg with
      | affine A => exact ⟨_, A, T, rfl⟩

end NNE

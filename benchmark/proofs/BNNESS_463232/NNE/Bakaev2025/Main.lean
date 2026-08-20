/-
Copyright (c) 2026 Anthony Chang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Chang
-/

import NNE.ReLUClass
import NNE.Max
import NNE.Bakaev2025.M
import NNE.T
import NNE.Bakaev2025.Lemmas

/-!
Neural network expressivity
-/

namespace NNE

/-- `MAX₅ = M`. The pointwise identity underlying `max5_mem`. (Claim 4) -/
theorem max5_eq_M : (MAXf : (Fin 5 → ℝ) → ℝ) = M := by
  funext x
  have hcore := max5_core_identity (x 4) (x 0) (x 1) (x 2) (x 3)
  rw [MAXf_five]
  rw [show M x = (P₁ x + P₂ x + P₃ x + P₄ x + Q x - R₁₃ x - R₁₄ x - R₂₃ x - R₂₄ x) / 2 from rfl]
  rw [P₁_eq, P₂_eq, P₃_eq, P₄_eq, Q_eq, R₁₃_eq, R₁₄_eq, R₂₃_eq, R₂₄_eq]
  linarith

/-- `MAX₅` is computable with two hidden layers (upper-bound half of Prop 3). -/
theorem max5_mem : (MAXf : (Fin 5 → ℝ) → ℝ) ∈ ReLUClass 5 2 := by
  rw [max5_eq_M]
  -- class-0 affine atoms
  have c0 : (fun x : Fin 5 → ℝ => x 0) ∈ ReLUClass 5 0 :=
    affine_mem_ReLUClass ((projₗ (0 : Fin 5)).toAffineMap) 0
  have c1 : (fun x : Fin 5 → ℝ => x 1) ∈ ReLUClass 5 0 :=
    affine_mem_ReLUClass ((projₗ (1 : Fin 5)).toAffineMap) 0
  have c2 : (fun x : Fin 5 → ℝ => x 2) ∈ ReLUClass 5 0 :=
    affine_mem_ReLUClass ((projₗ (2 : Fin 5)).toAffineMap) 0
  have c3 : (fun x : Fin 5 → ℝ => x 3) ∈ ReLUClass 5 0 :=
    affine_mem_ReLUClass ((projₗ (3 : Fin 5)).toAffineMap) 0
  have a24 : (fun x : Fin 5 → ℝ => 2 * x 4) ∈ ReLUClass 5 0 :=
    affine_mem_ReLUClass (((2 : ℝ) • projₗ (4 : Fin 5)).toAffineMap) 0
  have a01 : (fun x : Fin 5 → ℝ => x 0 + x 1) ∈ ReLUClass 5 0 :=
    affine_mem_ReLUClass ((projₗ (0 : Fin 5) + projₗ 1).toAffineMap) 0
  have a23 : (fun x : Fin 5 → ℝ => x 2 + x 3) ∈ ReLUClass 5 0 :=
    affine_mem_ReLUClass ((projₗ (2 : Fin 5) + projₗ 3).toAffineMap) 0
  -- the nine block functions, each with two hidden layers
  have hP₁ : P₁ ∈ ReLUClass 5 2 := by
    rw [funext P₁_eq]
    exact ReLUClass.sup (ReLUClass.sup a24 a01)
      (ReLUClass.add (ReLUClass.sup c0 c2) (ReLUClass.sup c0 c3))
  have hP₂ : P₂ ∈ ReLUClass 5 2 := by
    rw [funext P₂_eq]
    exact ReLUClass.sup (ReLUClass.sup a24 a01)
      (ReLUClass.add (ReLUClass.sup c1 c2) (ReLUClass.sup c1 c3))
  have hP₃ : P₃ ∈ ReLUClass 5 2 := by
    rw [funext P₃_eq]
    exact ReLUClass.sup (ReLUClass.sup a24 a23)
      (ReLUClass.add (ReLUClass.sup c2 c0) (ReLUClass.sup c2 c1))
  have hP₄ : P₄ ∈ ReLUClass 5 2 := by
    rw [funext P₄_eq]
    exact ReLUClass.sup (ReLUClass.sup a24 a23)
      (ReLUClass.add (ReLUClass.sup c3 c0) (ReLUClass.sup c3 c1))
  have hQ : Q ∈ ReLUClass 5 2 := by
    rw [funext Q_eq]
    exact ReLUClass.sup (ReLUClass.sup a24 a23)
      (ReLUClass.add (ReLUClass.sup c0 c0) (ReLUClass.sup c1 c1))
  have hR₁₃ : R₁₃ ∈ ReLUClass 5 2 := by
    rw [funext R₁₃_eq]
    exact ReLUClass.sup (ReLUClass.sup a24 a23)
      (ReLUClass.add (ReLUClass.sup c1 c2) (ReLUClass.sup c0 c0))
  have hR₁₄ : R₁₄ ∈ ReLUClass 5 2 := by
    rw [funext R₁₄_eq]
    exact ReLUClass.sup (ReLUClass.sup a24 a23)
      (ReLUClass.add (ReLUClass.sup c1 c3) (ReLUClass.sup c0 c0))
  have hR₂₃ : R₂₃ ∈ ReLUClass 5 2 := by
    rw [funext R₂₃_eq]
    exact ReLUClass.sup (ReLUClass.sup a24 a23)
      (ReLUClass.add (ReLUClass.sup c0 c2) (ReLUClass.sup c1 c1))
  have hR₂₄ : R₂₄ ∈ ReLUClass 5 2 := by
    rw [funext R₂₄_eq]
    exact ReLUClass.sup (ReLUClass.sup a24 a23)
      (ReLUClass.add (ReLUClass.sup c0 c3) (ReLUClass.sup c1 c1))
  -- assemble `M`
  have hM : M = fun x => (2⁻¹ : ℝ) *
      ((((((((P₁ x + P₂ x) + P₃ x) + P₄ x) + Q x) - R₁₃ x) - R₁₄ x) - R₂₃ x) - R₂₄ x) := by
    funext x
    change (P₁ x + P₂ x + P₃ x + P₄ x + Q x - R₁₃ x - R₁₄ x - R₂₃ x - R₂₄ x) / 2 = _
    ring
  rw [hM]
  exact ReLUClass.smul _ (ReLUClass.sub (ReLUClass.sub (ReLUClass.sub (ReLUClass.sub
    (ReLUClass.add (ReLUClass.add (ReLUClass.add (ReLUClass.add hP₁ hP₂) hP₃) hP₄) hQ)
    hR₁₃) hR₁₄) hR₂₃) hR₂₄)

/-- `MAX₅` is *not* computable with one hidden layer (lower-bound half of Prop 3). -/
theorem max5_not_mem_one : (MAXf : (Fin 5 → ℝ) → ℝ) ∉ ReLUClass 5 1 := by
  intro hmem
  obtain ⟨p, A, B, heq⟩ := ReLUk.one_inversion (mem_ReLUClass.mp hmem)
  have hpt : ∀ x, MAXf x = B (reluV (A x)) 0 := fun x => congrFun (congrFun heq x) 0
  -- the curve `γ t = (1-t, 1-t, t, 0, 0)` and the transverse direction `v`
  set v : Fin 5 → ℝ := ![1, -1, 0, 0, 0] with hv
  set dir : Fin 5 → ℝ := ![-1, -1, 1, 0, 0] with hdir
  set γ : ℝ → (Fin 5 → ℝ) := fun t => ![1 - t, 1 - t, t, 0, 0] with hγ
  have hγt : ∀ t : ℝ, γ t = γ 0 + t • dir := by
    intro t
    funext i
    fin_cases i <;> simp [hγ, hdir] <;> ring
  have hAγ : ∀ t : ℝ, A (γ t) = A (γ 0) + t • A.linear dir := by
    intro t
    rw [hγt t, affine_apply_add_smul]
  -- the finitely many parameters where the vanishing pattern can change
  set badF : Finset ℝ := Finset.univ.image (fun i : Fin p => -(A (γ 0) i) / A.linear dir i)
    with hbadF
  have hgood : ∀ t : ℝ, t ∉ (badF : Set ℝ) → ∀ i,
      (A (γ t) i = 0 ↔ A (γ 0) i = 0 ∧ A.linear dir i = 0) := by
    intro t ht i
    rw [hAγ t]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · intro h0
      by_cases he : A.linear dir i = 0
      · exact ⟨by rw [he, mul_zero, add_zero] at h0; exact h0, he⟩
      · exfalso
        apply ht
        refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, ?_⟩)
        field_simp
        linarith
    · rintro ⟨hc, he⟩
      rw [hc, he, mul_zero, add_zero]
  -- the slope jump is constant off the bad set
  have hconst : ∀ t : ℝ, t ∉ (badF : Set ℝ) → slopeJump A B (γ t) v
      = B.linear (fun i => if A (γ 0) i = 0 ∧ A.linear dir i = 0 then |A.linear v i| else 0)
          0 := by
    intro t ht
    unfold slopeJump
    have e : (fun i => if A (γ t) i = 0 then |A.linear v i| else 0)
        = fun i => if A (γ 0) i = 0 ∧ A.linear dir i = 0 then |A.linear v i| else 0 := by
      funext i
      exact if_congr (hgood t ht i) rfl rfl
    rw [e]
  -- explicit curve values
  have hcurve_add : ∀ t ε : ℝ, γ t + ε • v = ![1 - t + ε, 1 - t - ε, t, 0, 0] := by
    intro t ε
    funext i
    fin_cases i <;> simp [hγ, hv]
    ring
  have hcurve_sub : ∀ t ε : ℝ, γ t - ε • v = ![1 - t - ε, 1 - t + ε, t, 0, 0] := by
    intro t ε
    funext i
    fin_cases i <;> simp [hγ, hv]
  have hγval : ∀ t : ℝ, γ t = ![1 - t, 1 - t, t, 0, 0] := fun t => rfl
  -- jump value 2 on (0, 1/2)
  have hJ2 : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 / 2) → slopeJump A B (γ t) v = 2 := by
    rintro t ⟨ht0, ht12⟩
    have hev := net_second_diff A B (γ t) v
    have hev2 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        B (reluV (A (γ t + ε • v))) 0 + B (reluV (A (γ t - ε • v))) 0
          - 2 * B (reluV (A (γ t))) 0 = ε * 2 := by
      filter_upwards [self_mem_nhdsWithin] with ε (hε : ε ∈ Set.Ioi (0 : ℝ))
      have hε' : (0 : ℝ) < ε := hε
      rw [← hpt, ← hpt, ← hpt, hcurve_add, hcurve_sub, hγval]
      rw [MAXf_dominant₀ (by linarith) (by linarith) (by linarith) (by linarith),
        MAXf_dominant₁ (by linarith) (by linarith) (by linarith) (by linarith),
        MAXf_dominant₀ (le_refl (1 - t)) (by linarith) (by linarith) (by linarith)]
      ring
    obtain ⟨ε, hεJ, hε2, hεpos⟩ := (hev.and (hev2.and self_mem_nhdsWithin)).exists
    have hcancel : ε * slopeJump A B (γ t) v = ε * 2 := by rw [← hεJ, hε2]
    exact mul_left_cancel₀ (ne_of_gt hεpos) hcancel
  -- jump value 0 on (1/2, 1)
  have hJ0 : ∀ t : ℝ, t ∈ Set.Ioo (1 / 2 : ℝ) 1 → slopeJump A B (γ t) v = 0 := by
    rintro t ⟨ht12, ht1⟩
    have hev := net_second_diff A B (γ t) v
    have hev2 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        B (reluV (A (γ t + ε • v))) 0 + B (reluV (A (γ t - ε • v))) 0
          - 2 * B (reluV (A (γ t))) 0 = ε * 0 := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 * t - 1 by linarith)] with ε hε
      obtain ⟨hε0, hεlt⟩ := hε
      rw [← hpt, ← hpt, ← hpt, hcurve_add, hcurve_sub, hγval]
      rw [MAXf_dominant₂ (by linarith) (by linarith) (by linarith) (by linarith),
        MAXf_dominant₂ (by linarith) (by linarith) (by linarith) (by linarith),
        MAXf_dominant₂ (by linarith) (by linarith) (by linarith) (by linarith)]
      ring
    obtain ⟨ε, hεJ, hε2, hεpos⟩ := (hev.and (hev2.and self_mem_nhdsWithin)).exists
    have hcancel : ε * slopeJump A B (γ t) v = ε * 0 := by rw [← hεJ, hε2]
    exact mul_left_cancel₀ (ne_of_gt hεpos) hcancel
  -- pick good parameters on both sides of 1/2 and derive the contradiction
  obtain ⟨t₁, ht₁⟩ :=
    ((Set.Ioo_infinite (by norm_num : (0 : ℝ) < 1 / 2)).sdiff badF.finite_toSet).nonempty
  obtain ⟨t₂, ht₂⟩ :=
    ((Set.Ioo_infinite (by norm_num : (1 / 2 : ℝ) < 1)).sdiff badF.finite_toSet).nonempty
  have h1 := hJ2 t₁ ht₁.1
  have h2 := hJ0 t₂ ht₂.1
  rw [hconst t₁ ht₁.2] at h1
  rw [hconst t₂ ht₂.2] at h2
  linarith

/-- **Proposition 3.** Two is exactly the minimum number of hidden layers needed to
compute `MAX₅`. Drawn from both bounds (`max5_mem`, `max5_not_mem_one`). -/
theorem prop3 : IsLeast {k | (MAXf : (Fin 5 → ℝ) → ℝ) ∈ ReLUClass 5 k} 2 := by
  refine ⟨max5_mem, ?_⟩
  intro k hk
  by_contra h
  exact max5_not_mem_one (ReLUClass_mono (by omega) hk)

/-- `T_{a,b+4}`, viewed on `ℝ^{4a+b+4+1}` ignoring the last coordinate, lies in
`𝒯_{a+1,b+1}`. (Claim 5) -/
theorem claim5 (a b : ℕ) :
    (fun x : Fin (4 * a + (b + 4) + 1) → ℝ =>
        T a (b + 4) (fun i => x (Fin.castAdd 1 i)))
      ∈ Tspace (a + 1) (b + 1) (4 * a + (b + 4) + 1) := by
  have hmem : ∀ s t u v e : (Fin (4 * a + (b + 4) + 1) → ℝ) →ₗ[ℝ] ℝ,
      (fun x => T (a + 1) (b + 1) (Lgen a b s t u v e x))
        ∈ Tspace (a + 1) (b + 1) (4 * a + (b + 4) + 1) :=
    fun s t u v e => Submodule.subset_span ⟨Lgen a b s t u v e, rfl⟩
  set g1 : (Fin (4 * a + (b + 4) + 1) → ℝ) → ℝ := fun x => T (a + 1) (b + 1)
    (Lgen a b (yproj a b 0) (yproj a b 2) (yproj a b 0) (yproj a b 3)
      (yproj a b 0 + yproj a b 1) x) with hg1def
  set g2 : (Fin (4 * a + (b + 4) + 1) → ℝ) → ℝ := fun x => T (a + 1) (b + 1)
    (Lgen a b (yproj a b 1) (yproj a b 2) (yproj a b 1) (yproj a b 3)
      (yproj a b 0 + yproj a b 1) x) with hg2def
  set g3 : (Fin (4 * a + (b + 4) + 1) → ℝ) → ℝ := fun x => T (a + 1) (b + 1)
    (Lgen a b (yproj a b 2) (yproj a b 0) (yproj a b 2) (yproj a b 1)
      (yproj a b 2 + yproj a b 3) x) with hg3def
  set g4 : (Fin (4 * a + (b + 4) + 1) → ℝ) → ℝ := fun x => T (a + 1) (b + 1)
    (Lgen a b (yproj a b 3) (yproj a b 0) (yproj a b 3) (yproj a b 1)
      (yproj a b 2 + yproj a b 3) x) with hg4def
  set g5 : (Fin (4 * a + (b + 4) + 1) → ℝ) → ℝ := fun x => T (a + 1) (b + 1)
    (Lgen a b (yproj a b 0) (yproj a b 0) (yproj a b 1) (yproj a b 1)
      (yproj a b 2 + yproj a b 3) x) with hg5def
  set g6 : (Fin (4 * a + (b + 4) + 1) → ℝ) → ℝ := fun x => T (a + 1) (b + 1)
    (Lgen a b (yproj a b 1) (yproj a b 2) (yproj a b 0) (yproj a b 0)
      (yproj a b 2 + yproj a b 3) x) with hg6def
  set g7 : (Fin (4 * a + (b + 4) + 1) → ℝ) → ℝ := fun x => T (a + 1) (b + 1)
    (Lgen a b (yproj a b 1) (yproj a b 3) (yproj a b 0) (yproj a b 0)
      (yproj a b 2 + yproj a b 3) x) with hg7def
  set g8 : (Fin (4 * a + (b + 4) + 1) → ℝ) → ℝ := fun x => T (a + 1) (b + 1)
    (Lgen a b (yproj a b 0) (yproj a b 2) (yproj a b 1) (yproj a b 1)
      (yproj a b 2 + yproj a b 3) x) with hg8def
  set g9 : (Fin (4 * a + (b + 4) + 1) → ℝ) → ℝ := fun x => T (a + 1) (b + 1)
    (Lgen a b (yproj a b 0) (yproj a b 3) (yproj a b 1) (yproj a b 1)
      (yproj a b 2 + yproj a b 3) x) with hg9def
  have combo : ((2⁻¹ : ℝ) • (g1 + g2 + g3 + g4 + g5) - (2⁻¹ : ℝ) • (g6 + g7 + g8 + g9))
      ∈ Tspace (a + 1) (b + 1) (4 * a + (b + 4) + 1) := by
    refine Submodule.sub_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
    · refine add_mem (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_) ?_ <;>
        [rw [hg1def]; rw [hg2def]; rw [hg3def]; rw [hg4def]; rw [hg5def]] <;>
        exact hmem _ _ _ _ _
    · refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_ <;>
        [rw [hg6def]; rw [hg7def]; rw [hg8def]; rw [hg9def]] <;>
        exact hmem _ _ _ _ _
  have keyfun : (fun x : Fin (4 * a + (b + 4) + 1) → ℝ =>
        T a (b + 4) (fun i => x (Fin.castAdd 1 i)))
      = (2⁻¹ : ℝ) • (g1 + g2 + g3 + g4 + g5) - (2⁻¹ : ℝ) • (g6 + g7 + g8 + g9) := by
    funext x
    have h1 := gen_eval a b x (yproj a b 0) (yproj a b 2) (yproj a b 0) (yproj a b 3)
      (yproj a b 0 + yproj a b 1) (two_ymin_le_add a b x (by omega) (by omega))
    have h2 := gen_eval a b x (yproj a b 1) (yproj a b 2) (yproj a b 1) (yproj a b 3)
      (yproj a b 0 + yproj a b 1) (two_ymin_le_add a b x (by omega) (by omega))
    have h3 := gen_eval a b x (yproj a b 2) (yproj a b 0) (yproj a b 2) (yproj a b 1)
      (yproj a b 2 + yproj a b 3) (two_ymin_le_add a b x (by omega) (by omega))
    have h4 := gen_eval a b x (yproj a b 3) (yproj a b 0) (yproj a b 3) (yproj a b 1)
      (yproj a b 2 + yproj a b 3) (two_ymin_le_add a b x (by omega) (by omega))
    have h5 := gen_eval a b x (yproj a b 0) (yproj a b 0) (yproj a b 1) (yproj a b 1)
      (yproj a b 2 + yproj a b 3) (two_ymin_le_add a b x (by omega) (by omega))
    have h6 := gen_eval a b x (yproj a b 1) (yproj a b 2) (yproj a b 0) (yproj a b 0)
      (yproj a b 2 + yproj a b 3) (two_ymin_le_add a b x (by omega) (by omega))
    have h7 := gen_eval a b x (yproj a b 1) (yproj a b 3) (yproj a b 0) (yproj a b 0)
      (yproj a b 2 + yproj a b 3) (two_ymin_le_add a b x (by omega) (by omega))
    have h8 := gen_eval a b x (yproj a b 0) (yproj a b 2) (yproj a b 1) (yproj a b 1)
      (yproj a b 2 + yproj a b 3) (two_ymin_le_add a b x (by omega) (by omega))
    have h9 := gen_eval a b x (yproj a b 0) (yproj a b 3) (yproj a b 1) (yproj a b 1)
      (yproj a b 2 + yproj a b 3) (two_ymin_le_add a b x (by omega) (by omega))
    simp only [yproj_apply, yproj_add_apply] at h1 h2 h3 h4 h5 h6 h7 h8 h9
    have hL : T a (b + 4) (fun i => x (Fin.castAdd 1 i))
        = yc a b x 0 ⊔ (yc a b x 1 ⊔ (yc a b x 2 ⊔ (yc a b x 3 ⊔ Wval a b x))) :=
      T_xrest_eq a b x
    have hcore := max5_core_identity (Wval a b x) (yc a b x 0) (yc a b x 1) (yc a b x 2)
      (yc a b x 3)
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, hg1def, hg2def,
      hg3def, hg4def, hg5def, hg6def, hg7def, hg8def, hg9def]
    rw [hL, h1, h2, h3, h4, h5, h6, h7, h8, h9]
    linarith
  rw [keyfun]
  exact combo

/-- `T_{3ⁿ,2}` in depth `k` gives `T_{0,3ⁿ⁺¹+2}` in depth `k`. (Claim 6) -/
theorem claim6 (n k : ℕ) :
    Tcomputable (3 ^ n) 2 k → Tcomputable 0 (3 ^ (n + 1) + 2) k := by
  intro h
  have key : ∀ d, d ≤ 3 ^ n →
      T (3 ^ n - d) (3 * d + 2) ∈ ReLUClass (4 * (3 ^ n - d) + (3 * d + 2)) k := by
    intro d
    induction d with
    | zero => intro _; exact h
    | succ d ih =>
        intro hd
        haveI : NeZero ((3 ^ n - d) + (3 * d + 2)) := ⟨by omega⟩
        haveI : NeZero ((3 ^ n - (d + 1)) + (3 * (d + 1) + 2)) := ⟨by omega⟩
        exact step_class_of' (a := 3 ^ n - (d + 1)) (b := 3 * d + 1)
          (a' := 3 ^ n - d) (b' := 3 * d + 2) (B := 3 * (d + 1) + 2)
          (by omega) (by omega) (by omega)
          (claim5 (3 ^ n - (d + 1)) (3 * d + 1)) (ih (by omega))
  haveI : NeZero ((3 ^ n - 3 ^ n) + (3 * 3 ^ n + 2)) := ⟨by omega⟩
  exact T_mem_congr (by omega) (by rw [pow_succ]; ring) (key (3 ^ n) le_rfl)

/-- `T_{0,3ⁿ+2}` in depth `k` gives `T_{3ⁿ,2}` in depth `k+1`. (Claim 7) -/
theorem claim7 (n k : ℕ) :
    Tcomputable 0 (3 ^ n + 2) k → Tcomputable (3 ^ n) 2 (k + 1) := by
  intro h
  exact claim7_general (3 ^ n) k h

/-- **Theorem 1.** For `n ≥ 1`, `MAX_{3ⁿ+2}` ∈ `ReLU_{n+1}` -/
theorem thm1 (n : ℕ) (hn : 1 ≤ n) :
    (MAXf : (Fin (3 ^ n + 2) → ℝ) → ℝ) ∈ ReLUClass (3 ^ n + 2) (n + 1) := by
  induction n, hn using Nat.le_induction with
  | base => exact max5_mem
  | succ n hn ih =>
      have h1 : Tcomputable 0 (3 ^ n + 2) (n + 1) := Tcomputable_of_MAXf_mem ih
      have h2 : Tcomputable (3 ^ n) 2 (n + 1 + 1) := claim7 n (n + 1) h1
      have h3 : Tcomputable 0 (3 ^ (n + 1) + 2) (n + 1 + 1) := claim6 n (n + 1 + 1) h2
      exact MAXf_mem_of_Tcomputable h3

end NNE

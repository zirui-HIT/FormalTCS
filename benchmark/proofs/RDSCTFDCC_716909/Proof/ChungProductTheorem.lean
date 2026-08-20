import Mathlib

namespace Proof.ChungProductTheorem

open Finset

/-!
# Chung–Frankl–Graham–Shearer Product Theorem (Chung 1986)

A complete, entropy-free combinatorial proof of the projection inequality
`chung_main`: for a `k`-uniform cover `A : Fin p → Finset U` (every `u` in ≥ `k`
of the `A i`, `0 < k`) and a family `F`, `|F|^k ≤ ∏ i, |F.image (· ∩ A i)|`.

The proof: a product-Mahler / superadditive-geometric-mean core
(`mahler_real`, `pm_mono`, `L2_core`, `real_mahler_ge`, `L2_final_P`) plus an
erase-induction on the ground set (`chung_main`/`chung_step`) with a
doubled-set fiber-conditioning step (`E1`, `dbl_trace_dom`). Depends only on
Mathlib's standard axioms.
-/

namespace L2

/-- **Mahler / superadditive geometric mean (real, exponent = |T|).**
For nonnegative reals `a i, b i` over a nonempty finset `T` with `n = |T|`,
`(∏ a)^{1/n} + (∏ b)^{1/n} ≤ (∏ (a + b))^{1/n}`. -/
theorem mahler_real {ι : Type*} (T : Finset ι) (hT : T.Nonempty)
    (a b : ι → ℝ) (ha : ∀ i ∈ T, 0 ≤ a i) (hb : ∀ i ∈ T, 0 ≤ b i) :
    (∏ i ∈ T, a i) ^ ((T.card : ℝ)⁻¹) + (∏ i ∈ T, b i) ^ ((T.card : ℝ)⁻¹)
      ≤ (∏ i ∈ T, (a i + b i)) ^ ((T.card : ℝ)⁻¹) := by
  set n : ℝ := (T.card : ℝ) with hn
  have hncard : 0 < T.card := Finset.card_pos.mpr hT
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast hncard
  set S : ℝ := ∏ i ∈ T, (a i + b i) with hSdef
  have hab : ∀ i ∈ T, 0 ≤ a i + b i := fun i hi => add_nonneg (ha i hi) (hb i hi)
  have hSnonneg : 0 ≤ S := Finset.prod_nonneg hab
  -- Case: some factor is zero ⇒ S = 0 ⇒ both products zero.
  by_cases hS0 : S = 0
  · -- every product (a, b, a+b) vanishes
    have hSz := hS0
    rw [hSdef, Finset.prod_eq_zero_iff] at hSz
    obtain ⟨j, hjT, hj0⟩ := hSz
    have haj : a j = 0 := by
      have := ha j hjT; have := hb j hjT; linarith
    have hbj : b j = 0 := by
      have := ha j hjT; have := hb j hjT; linarith
    have hMa : (∏ i ∈ T, a i) = 0 := Finset.prod_eq_zero hjT haj
    have hNb : (∏ i ∈ T, b i) = 0 := Finset.prod_eq_zero hjT hbj
    rw [hMa, hNb, hS0]
    rw [Real.zero_rpow (by positivity)]
    simp
  · -- All factors positive.
    have hSpos : 0 < S := lt_of_le_of_ne hSnonneg (Ne.symm hS0)
    have habpos : ∀ i ∈ T, 0 < a i + b i := by
      intro i hi
      rcases lt_or_eq_of_le (hab i hi) with h | h
      · exact h
      · exfalso; apply hS0
        exact Finset.prod_eq_zero hi h.symm
    -- weights w i = 1/n, z_a i = a i / (a i + b i)
    have hw_sum : ∑ _i ∈ T, (T.card : ℝ)⁻¹ = 1 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp
    -- AM-GM for a
    have key_a : (∏ i ∈ T, a i) ^ ((T.card : ℝ)⁻¹) / S ^ ((T.card : ℝ)⁻¹)
        ≤ (T.card : ℝ)⁻¹ * ∑ i ∈ T, a i / (a i + b i) := by
      have hgm := Real.geom_mean_le_arith_mean_weighted T (fun _ => (T.card : ℝ)⁻¹)
        (fun i => a i / (a i + b i)) (fun i _ => by positivity) hw_sum
        (fun i hi => div_nonneg (ha i hi) (hab i hi))
      -- simplify LHS product
      have hLHS : (∏ i ∈ T, (a i / (a i + b i)) ^ ((T.card : ℝ)⁻¹))
          = (∏ i ∈ T, a i) ^ ((T.card : ℝ)⁻¹) / S ^ ((T.card : ℝ)⁻¹) := by
        rw [Real.finsetProd_rpow T _ (fun i hi => div_nonneg (ha i hi) (hab i hi))]
        rw [Finset.prod_div_distrib, Real.div_rpow (Finset.prod_nonneg ha) hSnonneg]
      rw [hLHS] at hgm
      -- RHS sum: ∑ (1/n) * (a/(a+b)) = (1/n) * ∑
      rw [Finset.mul_sum]
      convert hgm using 2
    -- symmetric for b
    have key_b : (∏ i ∈ T, b i) ^ ((T.card : ℝ)⁻¹) / S ^ ((T.card : ℝ)⁻¹)
        ≤ (T.card : ℝ)⁻¹ * ∑ i ∈ T, b i / (a i + b i) := by
      have hgm := Real.geom_mean_le_arith_mean_weighted T (fun _ => (T.card : ℝ)⁻¹)
        (fun i => b i / (a i + b i)) (fun i _ => by positivity) hw_sum
        (fun i hi => div_nonneg (hb i hi) (hab i hi))
      have hLHS : (∏ i ∈ T, (b i / (a i + b i)) ^ ((T.card : ℝ)⁻¹))
          = (∏ i ∈ T, b i) ^ ((T.card : ℝ)⁻¹) / S ^ ((T.card : ℝ)⁻¹) := by
        rw [Real.finsetProd_rpow T _ (fun i hi => div_nonneg (hb i hi) (hab i hi))]
        rw [Finset.prod_div_distrib, Real.div_rpow (Finset.prod_nonneg hb) hSnonneg]
      rw [hLHS] at hgm
      rw [Finset.mul_sum]
      convert hgm using 2
    -- combine: (M^{1/n} + N^{1/n})/S^{1/n} ≤ 1
    have hsum_one : (T.card : ℝ)⁻¹ * ∑ i ∈ T, a i / (a i + b i)
        + (T.card : ℝ)⁻¹ * ∑ i ∈ T, b i / (a i + b i) = 1 := by
      rw [← mul_add, ← Finset.sum_add_distrib]
      have : ∀ i ∈ T, a i / (a i + b i) + b i / (a i + b i) = 1 := by
        intro i hi
        field_simp
        exact div_self (ne_of_gt (habpos i hi))
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact inv_mul_cancel₀ (ne_of_gt hnpos)
    have hSrpow_pos : 0 < S ^ ((T.card : ℝ)⁻¹) := Real.rpow_pos_of_pos hSpos _
    have hcomb : ((∏ i ∈ T, a i) ^ ((T.card : ℝ)⁻¹) + (∏ i ∈ T, b i) ^ ((T.card : ℝ)⁻¹))
        / S ^ ((T.card : ℝ)⁻¹) ≤ 1 := by
      rw [add_div]
      calc (∏ i ∈ T, a i) ^ ((T.card : ℝ)⁻¹) / S ^ ((T.card : ℝ)⁻¹)
            + (∏ i ∈ T, b i) ^ ((T.card : ℝ)⁻¹) / S ^ ((T.card : ℝ)⁻¹)
          ≤ (T.card : ℝ)⁻¹ * ∑ i ∈ T, a i / (a i + b i)
            + (T.card : ℝ)⁻¹ * ∑ i ∈ T, b i / (a i + b i) := add_le_add key_a key_b
        _ = 1 := hsum_one
    rw [div_le_one hSrpow_pos] at hcomb
    exact hcomb

/-- **Power-mean monotonicity in the exponent (two-point).**
For `0 < k ≤ n` and `M, N ≥ 0`:
`(M^{1/k} + N^{1/k})^k ≤ (M^{1/n} + N^{1/n})^n`. -/
theorem pm_mono (M N : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N) (k n : ℕ)
    (hk : 0 < k) (hkn : k ≤ n) :
    (M ^ ((k : ℝ)⁻¹) + N ^ ((k : ℝ)⁻¹)) ^ k
      ≤ (M ^ ((n : ℝ)⁻¹) + N ^ ((n : ℝ)⁻¹)) ^ n := by
  have hn : 0 < n := lt_of_lt_of_le hk hkn
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  -- set a = M^{1/(k n)}, b = N^{1/(k n)}
  set a : ℝ := M ^ (((k : ℝ) * n)⁻¹) with hadef
  set b : ℝ := N ^ (((k : ℝ) * n)⁻¹) with hbdef
  have hapos : 0 ≤ a := Real.rpow_nonneg hM _
  have hbpos : 0 ≤ b := Real.rpow_nonneg hN _
  -- key: (a^n + b^n)^{1/n} ≤ (a^k + b^k)^{1/k}
  have hrpow := Real.rpow_add_rpow_le hapos hbpos hkR (by exact_mod_cast hkn : (k:ℝ) ≤ (n:ℝ))
  -- rewrite a^n = M^{1/k}, a^k = M^{1/n}, etc. (rpow with nat exponents)
  have haM_n : a ^ (n : ℝ) = M ^ ((k : ℝ)⁻¹) := by
    rw [hadef, ← Real.rpow_mul hM]
    congr 1
    field_simp
  have haM_k : a ^ (k : ℝ) = M ^ ((n : ℝ)⁻¹) := by
    rw [hadef, ← Real.rpow_mul hM]
    congr 1
    field_simp
  have hbN_n : b ^ (n : ℝ) = N ^ ((k : ℝ)⁻¹) := by
    rw [hbdef, ← Real.rpow_mul hN]
    congr 1
    field_simp
  have hbN_k : b ^ (k : ℝ) = N ^ ((n : ℝ)⁻¹) := by
    rw [hbdef, ← Real.rpow_mul hN]
    congr 1
    field_simp
  -- The hypothesis with rpow nat exponents folded
  rw [haM_n, hbN_n, haM_k, hbN_k] at hrpow
  -- hrpow : (M^{1/k} + N^{1/k})^{1/n} ≤ (M^{1/n} + N^{1/n})^{1/k}
  -- raise both sides to power (k*n)
  have hL0 : 0 ≤ M ^ ((k : ℝ)⁻¹) + N ^ ((k : ℝ)⁻¹) :=
    add_nonneg (Real.rpow_nonneg hM _) (Real.rpow_nonneg hN _)
  have hR0 : 0 ≤ M ^ ((n : ℝ)⁻¹) + N ^ ((n : ℝ)⁻¹) :=
    add_nonneg (Real.rpow_nonneg hM _) (Real.rpow_nonneg hN _)
  have hmono := Real.rpow_le_rpow (Real.rpow_nonneg hL0 _) hrpow
    (le_of_lt (mul_pos hkR hnR))
  -- ((·)^{1/n})^{kn} = (·)^k ; ((·)^{1/k})^{kn} = (·)^n
  rw [← Real.rpow_natCast (M ^ ((k:ℝ)⁻¹) + N ^ ((k:ℝ)⁻¹)) k,
      ← Real.rpow_natCast (M ^ ((n:ℝ)⁻¹) + N ^ ((n:ℝ)⁻¹)) n]
  rw [← Real.rpow_mul hL0, ← Real.rpow_mul hR0] at hmono
  have e1 : (1 / (n:ℝ)) * ((k : ℝ) * n) = (k : ℝ) := by field_simp
  have e2 : (1 / (k:ℝ)) * ((k : ℝ) * n) = (n : ℝ) := by field_simp
  rw [e1, e2] at hmono
  exact hmono

/-- **L2 core (ℕ):** if `g^k ≤ ∏ α` and `d^k ≤ ∏ β` with `k ≤ |T|`, then
`(g + d)^k ≤ ∏ (α + β)`. -/
theorem L2_core {ι : Type*} (T : Finset ι) (k : ℕ) (hk : k ≤ T.card)
    (α β : ι → ℕ) (g d : ℕ)
    (hg : g ^ k ≤ ∏ i ∈ T, α i) (hd : d ^ k ≤ ∏ i ∈ T, β i) :
    (g + d) ^ k ≤ ∏ i ∈ T, (α i + β i) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- k = 0 : goal `1 ≤ ∏ (α + β)`
    subst hk0
    simp only [pow_zero] at hg ⊢
    -- hg : 1 ≤ ∏ α i ⇒ every α i ≥ 1
    have hαne : ∀ i ∈ T, α i ≠ 0 := by
      intro i hi
      have hne : (∏ j ∈ T, α j) ≠ 0 := by omega
      rw [Finset.prod_ne_zero_iff] at hne
      exact hne i hi
    refine Finset.one_le_prod' ?_
    intro i hi
    have : α i ≠ 0 := hαne i hi
    omega
  · -- k ≥ 1
    have hTne : T.Nonempty := by
      rw [← Finset.card_pos]; omega
    set n : ℕ := T.card with hndef
    have hnpos : 0 < n := Finset.card_pos.mpr hTne
    -- Real products
    set M : ℝ := ∏ i ∈ T, (α i : ℝ) with hMdef
    set N : ℝ := ∏ i ∈ T, (β i : ℝ) with hNdef
    set S : ℝ := ∏ i ∈ T, ((α i : ℝ) + (β i : ℝ)) with hSdef
    have hMnonneg : 0 ≤ M := Finset.prod_nonneg (fun i _ => by positivity)
    have hNnonneg : 0 ≤ N := Finset.prod_nonneg (fun i _ => by positivity)
    have hSnonneg : 0 ≤ S := Finset.prod_nonneg (fun i _ => by positivity)
    -- cast bridges
    have hMcast : ((∏ i ∈ T, α i : ℕ) : ℝ) = M := by
      rw [hMdef]; push_cast; rfl
    have hNcast : ((∏ i ∈ T, β i : ℕ) : ℝ) = N := by
      rw [hNdef]; push_cast; rfl
    have hScast : ((∏ i ∈ T, (α i + β i) : ℕ) : ℝ) = S := by
      rw [hSdef]; push_cast; rfl
    -- (g:ℝ)^k ≤ M
    have hgR : (g : ℝ) ^ k ≤ M := by
      rw [← hMcast]; exact_mod_cast hg
    have hdR : (d : ℝ) ^ k ≤ N := by
      rw [← hNcast]; exact_mod_cast hd
    have hkR : (0:ℝ) < k := by exact_mod_cast hkpos
    -- g ≤ M^{1/k}
    have hg_root : (g : ℝ) ≤ M ^ ((k : ℝ)⁻¹) := by
      rw [Real.le_rpow_inv_iff_of_pos (by positivity) hMnonneg hkR, Real.rpow_natCast]
      exact hgR
    have hd_root : (d : ℝ) ≤ N ^ ((k : ℝ)⁻¹) := by
      rw [Real.le_rpow_inv_iff_of_pos (by positivity) hNnonneg hkR, Real.rpow_natCast]
      exact hdR
    -- (g + d : ℝ) ≤ M^{1/k} + N^{1/k}
    have hsum_root : ((g : ℝ) + d) ≤ M ^ ((k : ℝ)⁻¹) + N ^ ((k : ℝ)⁻¹) :=
      add_le_add hg_root hd_root
    have hgd_nonneg : (0:ℝ) ≤ (g : ℝ) + d := by positivity
    -- ((g+d):ℝ)^k ≤ (M^{1/k}+N^{1/k})^k
    have hstep1 : ((g : ℝ) + d) ^ k
        ≤ (M ^ ((k : ℝ)⁻¹) + N ^ ((k : ℝ)⁻¹)) ^ k :=
      pow_le_pow_left₀ hgd_nonneg hsum_root k
    -- power-mean monotonicity
    have hstep2 := pm_mono M N hMnonneg hNnonneg k n hkpos hk
    -- mahler: M^{1/n} + N^{1/n} ≤ S^{1/n}
    have hmahler := mahler_real T hTne (fun i => (α i : ℝ)) (fun i => (β i : ℝ))
      (fun i _ => by positivity) (fun i _ => by positivity)
    -- rewrite mahler products to M, N, S and card to n
    have hmahler' : M ^ ((n : ℝ)⁻¹) + N ^ ((n : ℝ)⁻¹) ≤ S ^ ((n : ℝ)⁻¹) := by
      rw [hMdef, hNdef, hSdef, hndef]
      exact hmahler
    have hMNroot_nonneg : 0 ≤ M ^ ((n : ℝ)⁻¹) + N ^ ((n : ℝ)⁻¹) :=
      add_nonneg (Real.rpow_nonneg hMnonneg _) (Real.rpow_nonneg hNnonneg _)
    -- raise mahler to power n
    have hstep3 : (M ^ ((n : ℝ)⁻¹) + N ^ ((n : ℝ)⁻¹)) ^ n
        ≤ (S ^ ((n : ℝ)⁻¹)) ^ n :=
      pow_le_pow_left₀ hMNroot_nonneg hmahler' n
    -- (S^{1/n})^n = S
    have hSpow : (S ^ ((n : ℝ)⁻¹)) ^ n = S := by
      rw [← Real.rpow_natCast (S ^ ((n : ℝ)⁻¹)) n, ← Real.rpow_mul hSnonneg]
      rw [inv_mul_cancel₀ (by exact_mod_cast (Nat.pos_iff_ne_zero.mp hnpos))]
      exact Real.rpow_one S
    rw [hSpow] at hstep3
    -- chain all: ((g+d):ℝ)^k ≤ S
    have hchain : ((g : ℝ) + d) ^ k ≤ S := le_trans hstep1 (le_trans hstep2 hstep3)
    -- convert back to ℕ
    have hgoalR : (((g + d) ^ k : ℕ) : ℝ) ≤ ((∏ i ∈ T, (α i + β i) : ℕ) : ℝ) := by
      rw [hScast]
      push_cast
      exact hchain
    exact_mod_cast hgoalR

end L2

/-- Projection of a set family `G` onto a subset `C`. -/
def proj {U : Type*} [DecidableEq U] (C : Finset U) (G : Finset (Finset U)) : Finset (Finset U) :=
  G.image (fun S => S ∩ C)

namespace Chung

variable {U : Type*} [DecidableEq U]

/-- Erasing `x` from a projected trace = projecting onto `C.erase x`:
`proj (C.erase x) G = (proj C G).image (·.erase x)`. -/
theorem proj_erase (x : U) (C : Finset U) (G : Finset (Finset U)) :
    proj (C.erase x) G = (proj C G).image (fun T => T.erase x) := by
  unfold proj
  rw [Finset.image_image]
  apply Finset.image_congr
  intro S _
  simp only [Function.comp]
  ext y
  simp only [Finset.mem_inter, Finset.mem_erase]
  tauto

/-- The doubled set: traces `w` onto `C.erase x` whose both lifts (`w` and
`insert x w`) appear in `proj C G`. -/
def DblSet (x : U) (C : Finset U) (G : Finset (Finset U)) : Finset (Finset U) :=
  (proj (C.erase x) G).filter (fun w => w ∈ proj C G ∧ insert x w ∈ proj C G)

/-- Membership in `proj C G` forces `T ⊆ C`. -/
theorem proj_subset {C : Finset U} {G : Finset (Finset U)} {T : Finset U}
    (hT : T ∈ proj C G) : T ⊆ C := by
  unfold proj at hT
  rw [Finset.mem_image] at hT
  obtain ⟨S, _, rfl⟩ := hT
  exact Finset.inter_subset_right

/-- The fiber of the erase-`x` map over `w ∈ proj (C.erase x) G`, computed as a
subset of `{w, insert x w}`. -/
theorem fiber_card (x : U) (C : Finset U) (G : Finset (Finset U))
    {w : Finset U} (hw : w ∈ proj (C.erase x) G) :
    {T ∈ proj C G | T.erase x = w}.card
      = 1 + (if w ∈ DblSet x C G then 1 else 0) := by
  -- `x ∉ w` since `w ⊆ C.erase x`
  have hxw : x ∉ w := fun hx => (Finset.mem_erase.mp (proj_subset hw hx)).1 rfl
  -- The fiber is contained in `{w, insert x w}`.
  have hsub : {T ∈ proj C G | T.erase x = w} ⊆ {w, insert x w} := by
    intro T hT
    rw [Finset.mem_filter] at hT
    obtain ⟨hTmem, hTerase⟩ := hT
    rw [Finset.mem_insert, Finset.mem_singleton]
    by_cases hxT : x ∈ T
    · -- T = insert x w
      right
      rw [← hTerase, Finset.insert_erase hxT]
    · -- T = w
      left
      rw [← hTerase, Finset.erase_eq_of_notMem hxT]
  -- `w ∈ proj (C.erase x) G` gives at least one lift is in `proj C G`.
  -- Now split on whether w is doubled.
  by_cases hdbl : w ∈ DblSet x C G
  · -- fiber = {w, insert x w}, card 2
    simp only [hdbl, if_true]
    rw [DblSet, Finset.mem_filter] at hdbl
    obtain ⟨_, hwmem, hinswmem⟩ := hdbl
    have hset : {T ∈ proj C G | T.erase x = w} = {w, insert x w} := by
      apply Finset.Subset.antisymm hsub
      intro T hT
      rw [Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl
      · rw [Finset.mem_filter]
        exact ⟨hwmem, Finset.erase_eq_of_notMem hxw⟩
      · rw [Finset.mem_filter]
        refine ⟨hinswmem, ?_⟩
        rw [Finset.erase_insert hxw]
    rw [hset]
    rw [Finset.card_pair]
    intro hcontra
    apply hxw
    rw [hcontra]; exact Finset.mem_insert_self x w
  · -- fiber has card 1
    simp only [hdbl, if_false, Nat.add_zero]
    -- exactly one of w, insert x w is in proj C G
    have hor : w ∈ proj C G ∨ insert x w ∈ proj C G := by
      rw [proj_erase] at hw
      rw [Finset.mem_image] at hw
      obtain ⟨T, hTmem, hTe⟩ := hw
      by_cases hxT : x ∈ T
      · right
        rw [← hTe, Finset.insert_erase hxT]; exact hTmem
      · left
        rw [← hTe, Finset.erase_eq_of_notMem hxT]; exact hTmem
    have hnotboth : ¬ (w ∈ proj C G ∧ insert x w ∈ proj C G) := by
      intro h
      apply hdbl
      rw [DblSet, Finset.mem_filter]
      exact ⟨hw, h⟩
    -- so the fiber is a singleton
    rcases hor with hwmem | hinswmem
    · have hnotins : insert x w ∉ proj C G := fun h => hnotboth ⟨hwmem, h⟩
      have hset : {T ∈ proj C G | T.erase x = w} = {w} := by
        apply Finset.Subset.antisymm
        · intro T hT
          have hT' := hsub hT
          rw [Finset.mem_insert, Finset.mem_singleton] at hT'
          rw [Finset.mem_singleton]
          rcases hT' with rfl | rfl
          · rfl
          · exfalso; rw [Finset.mem_filter] at hT; exact hnotins hT.1
        · intro T hT
          rw [Finset.mem_singleton] at hT; subst hT
          rw [Finset.mem_filter]
          exact ⟨hwmem, Finset.erase_eq_of_notMem hxw⟩
      rw [hset, Finset.card_singleton]
    · have hnotw : w ∉ proj C G := fun h => hnotboth ⟨h, hinswmem⟩
      have hset : {T ∈ proj C G | T.erase x = w} = {insert x w} := by
        apply Finset.Subset.antisymm
        · intro T hT
          have hT' := hsub hT
          rw [Finset.mem_insert, Finset.mem_singleton] at hT'
          rw [Finset.mem_singleton]
          rcases hT' with rfl | rfl
          · exfalso; rw [Finset.mem_filter] at hT; exact hnotw hT.1
          · rfl
        · intro T hT
          rw [Finset.mem_singleton] at hT; subst hT
          rw [Finset.mem_filter]
          exact ⟨hinswmem, Finset.erase_insert hxw⟩
      rw [hset, Finset.card_singleton]

/-- `erase` commutes with intersection on the left:
`(C ∩ D).erase x = C.erase x ∩ D`. -/
theorem erase_inter (x : U) (C D : Finset U) :
    (C ∩ D).erase x = C.erase x ∩ D := by
  ext y
  simp only [Finset.mem_erase, Finset.mem_inter]
  tauto

/-- If `x ∉ D` then erasing `x` from `C` does not change `C ∩ D`. -/
theorem inter_erase_eq (x : U) (C D : Finset U) (hxD : x ∉ D) :
    C ∩ D = C.erase x ∩ D := by
  ext y
  simp only [Finset.mem_inter, Finset.mem_erase]
  constructor
  · rintro ⟨hyC, hyD⟩; exact ⟨⟨fun h => hxD (h ▸ hyD), hyC⟩, hyD⟩
  · rintro ⟨⟨_, hyC⟩, hyD⟩; exact ⟨hyC, hyD⟩

/-- Projecting a member and intersecting with `D` lands in the projection onto
`C ∩ D`: `T ∈ proj C G → T ∩ D ∈ proj (C ∩ D) G`. -/
theorem proj_inter_mono {C D : Finset U} {G : Finset (Finset U)} {T : Finset U}
    (hT : T ∈ proj C G) : T ∩ D ∈ proj (C ∩ D) G := by
  unfold proj at hT ⊢
  rw [Finset.mem_image] at hT ⊢
  obtain ⟨S, hSmem, rfl⟩ := hT
  exact ⟨S, hSmem, by rw [Finset.inter_assoc]⟩

/-- **(E1) Fiber identity.** For `x ∈ C`,
`(proj C G).card = (proj (C.erase x) G).card + (DblSet x C G).card`. -/
theorem E1 (x : U) (C : Finset U) (G : Finset (Finset U)) :
    (proj C G).card
      = (proj (C.erase x) G).card + (DblSet x C G).card := by
  rw [Finset.card_eq_sum_card_image (fun T => T.erase x) (proj C G)]
  rw [← proj_erase]
  -- card of proj (C.erase x) G = ∑ w, 1 ; DblSet card = ∑ w∈Dbl, 1
  have hfib : ∀ w ∈ proj (C.erase x) G,
      {T ∈ proj C G | T.erase x = w}.card
        = 1 + (if w ∈ DblSet x C G then 1 else 0) := fun w hw => fiber_card x C G hw
  rw [Finset.sum_congr rfl hfib]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_const, smul_eq_mul, mul_one]
  · rw [Finset.sum_boole, Nat.cast_id]
    -- DblSet x C G ⊆ proj (C.erase x) G, so filter (· ∈ DblSet) = DblSet
    have hfilter : {w ∈ proj (C.erase x) G | w ∈ DblSet x C G} = DblSet x C G := by
      rw [DblSet]
      ext w
      simp only [Finset.mem_filter]
      tauto
    rw [hfilter]

/-- **(d-vs-b) Doubled-set trace domination.** For `x ∈ Ai`,
`proj (B.erase x ∩ Ai) (DblSet x B G) ⊆ DblSet x (B ∩ Ai) G`. -/
theorem dbl_trace_dom (x : U) (B Ai : Finset U) (G : Finset (Finset U))
    (hxAi : x ∈ Ai) :
    proj (B.erase x ∩ Ai) (DblSet x B G) ⊆ DblSet x (B ∩ Ai) G := by
  intro z hz
  -- z = w ∩ (B.erase x ∩ Ai) for some w ∈ DblSet x B G
  unfold proj at hz
  rw [Finset.mem_image] at hz
  obtain ⟨w, hwDbl, rfl⟩ := hz
  -- unpack DblSet x B G membership of w
  rw [DblSet, Finset.mem_filter] at hwDbl
  obtain ⟨hwproj, hwB, hinswB⟩ := hwDbl
  -- w ⊆ B.erase x, so w ∩ (B.erase x ∩ Ai) = w ∩ Ai
  have hwsub : w ⊆ B.erase x := proj_subset hwproj
  have hxw : x ∉ w := fun h => (Finset.mem_erase.mp (hwsub h)).1 rfl
  have hwinter : w ∩ (B.erase x ∩ Ai) = w ∩ Ai := by
    ext y
    simp only [Finset.mem_inter, Finset.mem_erase]
    constructor
    · rintro ⟨hyw, _, hyAi⟩; exact ⟨hyw, hyAi⟩
    · rintro ⟨hyw, hyAi⟩
      exact ⟨hyw, ⟨fun h => hxw (h ▸ hyw), (Finset.mem_erase.mp (hwsub hyw)).2⟩, hyAi⟩
  rw [hwinter]
  -- (B ∩ Ai).erase x = B.erase x ∩ Ai
  have herase : (B ∩ Ai).erase x = B.erase x ∩ Ai := erase_inter x B Ai
  -- target: w ∩ Ai ∈ DblSet x (B ∩ Ai) G
  rw [DblSet, Finset.mem_filter]
  refine ⟨?_, ?_, ?_⟩
  · -- w ∩ Ai ∈ proj ((B ∩ Ai).erase x) G
    rw [herase]
    -- w ∈ proj (B.erase x) G ⟹ w ∩ Ai ∈ proj (B.erase x ∩ Ai) G
    exact proj_inter_mono hwproj
  · -- w ∩ Ai ∈ proj (B ∩ Ai) G
    exact proj_inter_mono hwB
  · -- insert x (w ∩ Ai) ∈ proj (B ∩ Ai) G
    have h2 : (insert x w) ∩ Ai ∈ proj (B ∩ Ai) G := proj_inter_mono hinswB
    have hins : (insert x w) ∩ Ai = insert x (w ∩ Ai) := by
      rw [Finset.insert_inter_of_mem hxAi]
    rw [hins] at h2
    exact h2

/-- **Real Mahler bound (exponent `k`, index set of size ≥ k).**
For nonnegative `α β : ι → ℝ` over `T` with `0 < k ≤ |T|`:
`((∏ α)^{1/k} + (∏ β)^{1/k})^k ≤ ∏ (α + β)`. -/
theorem real_mahler_ge {ι : Type*} (T : Finset ι) (k : ℕ) (hkpos : 0 < k)
    (hk : k ≤ T.card) (α β : ι → ℝ)
    (hα : ∀ i ∈ T, 0 ≤ α i) (hβ : ∀ i ∈ T, 0 ≤ β i) :
    ((∏ i ∈ T, α i) ^ ((k : ℝ)⁻¹) + (∏ i ∈ T, β i) ^ ((k : ℝ)⁻¹)) ^ k
      ≤ ∏ i ∈ T, (α i + β i) := by
  have hTne : T.Nonempty := by
    rw [← Finset.card_pos]; omega
  set n : ℕ := T.card with hndef
  have hnpos : 0 < n := Finset.card_pos.mpr hTne
  set M : ℝ := ∏ i ∈ T, α i with hMdef
  set N : ℝ := ∏ i ∈ T, β i with hNdef
  set S : ℝ := ∏ i ∈ T, (α i + β i) with hSdef
  have hMnonneg : 0 ≤ M := Finset.prod_nonneg hα
  have hNnonneg : 0 ≤ N := Finset.prod_nonneg hβ
  have hSnonneg : 0 ≤ S := Finset.prod_nonneg (fun i hi => add_nonneg (hα i hi) (hβ i hi))
  -- power-mean monotonicity k → n
  have hstep2 := L2.pm_mono M N hMnonneg hNnonneg k n hkpos hk
  -- mahler at exponent n
  have hmahler := L2.mahler_real T hTne α β hα hβ
  have hmahler' : M ^ ((n : ℝ)⁻¹) + N ^ ((n : ℝ)⁻¹) ≤ S ^ ((n : ℝ)⁻¹) := by
    rw [hMdef, hNdef, hSdef, hndef]; exact hmahler
  have hMNroot_nonneg : 0 ≤ M ^ ((n : ℝ)⁻¹) + N ^ ((n : ℝ)⁻¹) :=
    add_nonneg (Real.rpow_nonneg hMnonneg _) (Real.rpow_nonneg hNnonneg _)
  have hstep3 : (M ^ ((n : ℝ)⁻¹) + N ^ ((n : ℝ)⁻¹)) ^ n ≤ (S ^ ((n : ℝ)⁻¹)) ^ n :=
    pow_le_pow_left₀ hMNroot_nonneg hmahler' n
  have hSpow : (S ^ ((n : ℝ)⁻¹)) ^ n = S := by
    rw [← Real.rpow_natCast (S ^ ((n : ℝ)⁻¹)) n, ← Real.rpow_mul hSnonneg]
    rw [inv_mul_cancel₀ (by exact_mod_cast (Nat.pos_iff_ne_zero.mp hnpos))]
    exact Real.rpow_one S
  rw [hSpow] at hstep3
  exact le_trans hstep2 hstep3

/-- **L2 final (arithmetic crux with a common factor).** Over `univ' ⊇ T`,
with `b` supported on `T`, `1 ≤ a i` everywhere, `g^k ≤ ∏_{univ'} a`,
`d^k ≤ ∏_T b`, we get `(g+d)^k ≤ ∏_{univ'} (a + b)`. -/
theorem L2_final {ι : Type*} [DecidableEq ι] (univ' : Finset ι) (T : Finset ι)
    (hT : T ⊆ univ') (k : ℕ) (hkpos : 0 < k) (hk : k ≤ T.card) (a b : ι → ℕ) (g d : ℕ)
    (hbT : ∀ i ∉ T, b i = 0) (ha1 : ∀ i ∈ univ', 1 ≤ a i)
    (hg : g ^ k ≤ ∏ i ∈ univ', a i) (hd : d ^ k ≤ ∏ i ∈ T, b i) :
    (g + d) ^ k ≤ ∏ i ∈ univ', (a i + b i) := by
  -- split univ' = T ∪ (univ' \ T)
  have hsplit_a : ∏ i ∈ univ', a i = (∏ i ∈ T, a i) * ∏ i ∈ univ' \ T, a i := by
    rw [← Finset.prod_union (Finset.disjoint_sdiff), Finset.union_sdiff_of_subset hT]
  have hsplit_ab : ∏ i ∈ univ', (a i + b i) = (∏ i ∈ T, (a i + b i)) * ∏ i ∈ univ' \ T, a i := by
    conv_lhs => rw [← Finset.union_sdiff_of_subset hT, Finset.prod_union (Finset.disjoint_sdiff)]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_sdiff] at hi
    rw [hbT i hi.2, Nat.add_zero]
  set Pc : ℕ := ∏ i ∈ univ' \ T, a i with hPcdef
  have hPc1 : 1 ≤ Pc := by
    rw [hPcdef]
    apply Finset.one_le_prod'
    intro i hi
    rw [Finset.mem_sdiff] at hi
    exact ha1 i hi.1
  rw [hsplit_a] at hg
  rw [hsplit_ab]
  -- reduce to: (g+d)^k ≤ (∏_T (a+b)) * Pc, via reals
  -- Real setup
  have hkR : (0:ℝ) < k := by exact_mod_cast hkpos
  -- M := ∏_T a, Nb := ∏_T b, Pc as reals
  set Ma : ℝ := ∏ i ∈ T, (a i : ℝ) with hMadef
  set Nb : ℝ := ∏ i ∈ T, (b i : ℝ) with hNbdef
  set PcR : ℝ := (Pc : ℝ) with hPcRdef
  have hMa_nonneg : 0 ≤ Ma := Finset.prod_nonneg (fun i _ => by positivity)
  have hNb_nonneg : 0 ≤ Nb := Finset.prod_nonneg (fun i _ => by positivity)
  have hPcR_pos : 0 < PcR := by rw [hPcRdef]; exact_mod_cast hPc1
  have hPcR1 : 1 ≤ PcR := by rw [hPcRdef]; exact_mod_cast hPc1
  -- g^k ≤ Ma * Pc  (real)
  have hgR : (g : ℝ) ^ k ≤ Ma * PcR := by
    have h := hg
    have : ((g ^ k : ℕ) : ℝ) ≤ (((∏ i ∈ T, a i) * Pc : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    rw [hMadef, hPcRdef]; exact this
  -- d^k ≤ Nb  (real)
  have hdR : (d : ℝ) ^ k ≤ Nb := by
    have : ((d ^ k : ℕ) : ℝ) ≤ ((∏ i ∈ T, b i : ℕ) : ℝ) := by exact_mod_cast hd
    push_cast at this; rw [hNbdef]; exact this
  -- g ≤ (Ma*Pc)^{1/k}
  have hg_root : (g : ℝ) ≤ (Ma * PcR) ^ ((k : ℝ)⁻¹) := by
    rw [Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) hkR, Real.rpow_natCast]
    exact hgR
  -- d ≤ (Nb*Pc)^{1/k}  (since Pc ≥ 1)
  have hd_root : (d : ℝ) ≤ (Nb * PcR) ^ ((k : ℝ)⁻¹) := by
    rw [Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) hkR, Real.rpow_natCast]
    calc (d : ℝ) ^ k ≤ Nb := hdR
      _ ≤ Nb * PcR := by nlinarith [hNb_nonneg, hPcR_pos]
  -- (g+d) ≤ Pc^{1/k} * ((Ma)^{1/k} + (Nb)^{1/k})
  have hPcRk_pos : 0 < PcR ^ ((k:ℝ)⁻¹) := Real.rpow_pos_of_pos hPcR_pos _
  have hfactor : (Ma * PcR) ^ ((k : ℝ)⁻¹) = Ma ^ ((k:ℝ)⁻¹) * PcR ^ ((k:ℝ)⁻¹) :=
    Real.mul_rpow hMa_nonneg (le_of_lt hPcR_pos)
  have hfactor2 : (Nb * PcR) ^ ((k : ℝ)⁻¹) = Nb ^ ((k:ℝ)⁻¹) * PcR ^ ((k:ℝ)⁻¹) :=
    Real.mul_rpow hNb_nonneg (le_of_lt hPcR_pos)
  have hsum_root : ((g : ℝ) + d) ≤ (Ma ^ ((k:ℝ)⁻¹) + Nb ^ ((k:ℝ)⁻¹)) * PcR ^ ((k:ℝ)⁻¹) := by
    have := add_le_add hg_root hd_root
    rw [hfactor, hfactor2] at this
    calc (g : ℝ) + d ≤ Ma ^ ((k:ℝ)⁻¹) * PcR ^ ((k:ℝ)⁻¹) + Nb ^ ((k:ℝ)⁻¹) * PcR ^ ((k:ℝ)⁻¹) := this
      _ = (Ma ^ ((k:ℝ)⁻¹) + Nb ^ ((k:ℝ)⁻¹)) * PcR ^ ((k:ℝ)⁻¹) := by ring
  -- raise to k
  have hgd_nonneg : (0:ℝ) ≤ (g : ℝ) + d := by positivity
  have hrhs_nonneg : 0 ≤ (Ma ^ ((k:ℝ)⁻¹) + Nb ^ ((k:ℝ)⁻¹)) * PcR ^ ((k:ℝ)⁻¹) := by positivity
  have hpow : ((g : ℝ) + d) ^ k
      ≤ ((Ma ^ ((k:ℝ)⁻¹) + Nb ^ ((k:ℝ)⁻¹)) * PcR ^ ((k:ℝ)⁻¹)) ^ k :=
    pow_le_pow_left₀ hgd_nonneg hsum_root k
  -- ((·) * Pc^{1/k})^k = (·)^k * Pc
  have hPcpow : (PcR ^ ((k:ℝ)⁻¹)) ^ k = PcR := by
    rw [← Real.rpow_natCast (PcR ^ ((k:ℝ)⁻¹)) k, ← Real.rpow_mul (le_of_lt hPcR_pos)]
    rw [inv_mul_cancel₀ (by exact_mod_cast (Nat.pos_iff_ne_zero.mp hkpos))]
    exact Real.rpow_one PcR
  have hmulpow : ((Ma ^ ((k:ℝ)⁻¹) + Nb ^ ((k:ℝ)⁻¹)) * PcR ^ ((k:ℝ)⁻¹)) ^ k
      = (Ma ^ ((k:ℝ)⁻¹) + Nb ^ ((k:ℝ)⁻¹)) ^ k * PcR := by
    rw [mul_pow, hPcpow]
  rw [hmulpow] at hpow
  -- mahler over T (cast a,b to ℝ): ((Ma)^{1/k}+(Nb)^{1/k})^k ≤ ∏_T (a+b)
  have hmahlerT := real_mahler_ge T k hkpos hk (fun i => (a i : ℝ)) (fun i => (b i : ℝ))
    (fun i _ => by positivity) (fun i _ => by positivity)
  -- the products in hmahlerT are Ma, Nb, and ∏ (a+b) (real)
  rw [show (∏ i ∈ T, (a i : ℝ)) = Ma from rfl, show (∏ i ∈ T, (b i : ℝ)) = Nb from rfl] at hmahlerT
  -- chain: (g+d)^k ≤ ((Ma)^{1/k}+(Nb)^{1/k})^k * Pc ≤ (∏_T (a+b)) * Pc
  have hchain : ((g : ℝ) + d) ^ k ≤ (∏ i ∈ T, ((a i : ℝ) + (b i : ℝ))) * PcR := by
    calc ((g : ℝ) + d) ^ k
        ≤ (Ma ^ ((k:ℝ)⁻¹) + Nb ^ ((k:ℝ)⁻¹)) ^ k * PcR := hpow
      _ ≤ (∏ i ∈ T, ((a i : ℝ) + (b i : ℝ))) * PcR := by
          apply mul_le_mul_of_nonneg_right hmahlerT (le_of_lt hPcR_pos)
  -- convert back to ℕ
  have hgoalR : (((g + d) ^ k : ℕ) : ℝ)
      ≤ (((∏ i ∈ T, (a i + b i)) * Pc : ℕ) : ℝ) := by
    push_cast
    rw [hPcRdef] at hchain
    convert hchain using 2
  exact_mod_cast hgoalR

end Chung

/-- **L2 final with symmetric Pc factor.** For `k ≤ |T|`, `1 ≤ Pc`,
`g^k ≤ (∏_T a) * Pc`, `d^k ≤ (∏_T b) * Pc`,
we get `(g+d)^k ≤ (∏_T (a+b)) * Pc`. -/
lemma L2_final_P {ι : Type*} [DecidableEq ι] (T : Finset ι) (k : ℕ) (hkpos : 0 < k)
    (hk : k ≤ T.card) (a b : ι → ℕ) (g d Pc : ℕ) (hPc : 1 ≤ Pc)
    (hg : g ^ k ≤ (∏ i ∈ T, a i) * Pc) (hd : d ^ k ≤ (∏ i ∈ T, b i) * Pc) :
    (g + d) ^ k ≤ (∏ i ∈ T, (a i + b i)) * Pc := by
  have hkR : (0:ℝ) < k := by exact_mod_cast hkpos
  set Ma : ℝ := ∏ i ∈ T, (a i : ℝ)
  set Nb : ℝ := ∏ i ∈ T, (b i : ℝ)
  set PcR : ℝ := (Pc : ℝ)
  have hMa_nonneg : 0 ≤ Ma := Finset.prod_nonneg (fun i _ => by positivity)
  have hNb_nonneg : 0 ≤ Nb := Finset.prod_nonneg (fun i _ => by positivity)
  have hPcR_pos : 0 < PcR := by
    have : 0 < Pc := Nat.lt_of_lt_of_le Nat.zero_lt_one hPc
    simp only [PcR]
    exact_mod_cast this
  -- cast hypotheses to ℝ
  have hgR : (g : ℝ) ^ k ≤ Ma * PcR := by
    have : ((g ^ k : ℕ) : ℝ) ≤ (((∏ i ∈ T, a i) * Pc : ℕ) : ℝ) := by exact_mod_cast hg
    push_cast at this; exact this
  have hdR : (d : ℝ) ^ k ≤ Nb * PcR := by
    have : ((d ^ k : ℕ) : ℝ) ≤ (((∏ i ∈ T, b i) * Pc : ℕ) : ℝ) := by exact_mod_cast hd
    push_cast at this; exact this
  -- g ≤ (Ma*PcR)^{1/k}
  have hg_root : (g : ℝ) ≤ (Ma * PcR) ^ ((k : ℝ)⁻¹) := by
    rw [Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) hkR, Real.rpow_natCast]
    exact hgR
  -- d ≤ (Nb*PcR)^{1/k}
  have hd_root : (d : ℝ) ≤ (Nb * PcR) ^ ((k : ℝ)⁻¹) := by
    rw [Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) hkR, Real.rpow_natCast]
    exact hdR
  -- factor out PcR^{1/k}
  have hfactorG : (Ma * PcR) ^ ((k : ℝ)⁻¹) = Ma ^ ((k:ℝ)⁻¹) * PcR ^ ((k:ℝ)⁻¹) :=
    Real.mul_rpow hMa_nonneg (le_of_lt hPcR_pos)
  have hfactorD : (Nb * PcR) ^ ((k : ℝ)⁻¹) = Nb ^ ((k:ℝ)⁻¹) * PcR ^ ((k:ℝ)⁻¹) :=
    Real.mul_rpow hNb_nonneg (le_of_lt hPcR_pos)
  have hsum_root : ((g : ℝ) + d) ≤ (Ma ^ ((k:ℝ)⁻¹) + Nb ^ ((k:ℝ)⁻¹)) * PcR ^ ((k:ℝ)⁻¹) := by
    have hadd := add_le_add hg_root hd_root
    rw [hfactorG, hfactorD] at hadd
    linarith [mul_comm (Ma ^ ((k:ℝ)⁻¹)) (PcR ^ ((k:ℝ)⁻¹)),
              mul_comm (Nb ^ ((k:ℝ)⁻¹)) (PcR ^ ((k:ℝ)⁻¹))]
  -- raise to k
  have hpow : ((g : ℝ) + d) ^ k
      ≤ ((Ma ^ ((k:ℝ)⁻¹) + Nb ^ ((k:ℝ)⁻¹)) * PcR ^ ((k:ℝ)⁻¹)) ^ k :=
    pow_le_pow_left₀ (by positivity) hsum_root k
  -- expand: (·*Pc^{1/k})^k = (·)^k * Pc
  have hPcpow : (PcR ^ ((k:ℝ)⁻¹)) ^ k = PcR := by
    rw [← Real.rpow_natCast (PcR ^ ((k:ℝ)⁻¹)) k, ← Real.rpow_mul (le_of_lt hPcR_pos)]
    rw [inv_mul_cancel₀ (by exact_mod_cast (Nat.pos_iff_ne_zero.mp hkpos))]
    exact Real.rpow_one PcR
  have hmulpow : ((Ma ^ ((k:ℝ)⁻¹) + Nb ^ ((k:ℝ)⁻¹)) * PcR ^ ((k:ℝ)⁻¹)) ^ k
      = (Ma ^ ((k:ℝ)⁻¹) + Nb ^ ((k:ℝ)⁻¹)) ^ k * PcR := by
    rw [mul_pow, hPcpow]
  rw [hmulpow] at hpow
  -- mahler bound: (Ma^{1/k}+Nb^{1/k})^k ≤ ∏_T(a+b)
  have hmahlerT := Chung.real_mahler_ge T k hkpos hk (fun i => (a i : ℝ)) (fun i => (b i : ℝ))
    (fun i _ => by positivity) (fun i _ => by positivity)
  rw [show (∏ i ∈ T, (a i : ℝ)) = Ma from rfl, show (∏ i ∈ T, (b i : ℝ)) = Nb from rfl] at hmahlerT
  -- chain and cast back to ℕ
  have hchain : ((g : ℝ) + d) ^ k ≤ (∏ i ∈ T, ((a i : ℝ) + (b i : ℝ))) * PcR :=
    le_trans hpow (mul_le_mul_of_nonneg_right hmahlerT (le_of_lt hPcR_pos))
  have hgoalR : (((g + d) ^ k : ℕ) : ℝ) ≤ (((∏ i ∈ T, (a i + b i)) * Pc : ℕ) : ℝ) := by
    push_cast; exact hchain
  exact_mod_cast hgoalR

/-- **Crux inductive step**: lifts `(★ (B.erase x))` (the per-family IH) to `(★ B)` by peeling `x`, via the doubled-set fiber identity and the common-factor Mahler bound `L2_final_P`. -/
lemma chung_step {U} [Fintype U] [DecidableEq U] {p : ℕ} (A : Fin p → Finset U) (k : ℕ)
    (hk : 0 < k) (hcover : ∀ u, k ≤ (univ.filter (fun i => u ∈ A i)).card)
    (B : Finset U) (x : U) (hx : x ∈ B)
    (IH : ∀ G : Finset (Finset U),
          (proj (B.erase x) G).card ^ k ≤ ∏ i, (proj ((B.erase x) ∩ A i) G).card) :
    ∀ G : Finset (Finset U), (proj B G).card ^ k ≤ ∏ i, (proj (B ∩ A i) G).card := by
  intro G
  set B' := B.erase x with hB'def
  set Sx := (Finset.univ : Finset (Fin p)).filter (fun i => x ∈ A i) with hSxdef
  have hkSx : k ≤ Sx.card := hcover x
  set a : Fin p → ℕ := fun i => (proj (B' ∩ A i) G).card with hadef
  set b : Fin p → ℕ := fun i => (Chung.DblSet x (B ∩ A i) G).card with hbdef
  set g := (proj B' G).card with hgdef
  set d := (Chung.DblSet x B G).card with hddef
  have hBcard : (proj B G).card = g + d := Chung.E1 x B G
  rw [hBcard]
  -- b i = 0 for x ∉ A i
  have hb0 : ∀ i : Fin p, x ∉ A i → b i = 0 := by
    intro i hxAi
    simp only [hbdef, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [Chung.DblSet, Finset.mem_filter] at hw
    obtain ⟨_, _, hw2⟩ := hw
    exact hxAi (Finset.mem_inter.mp (Chung.proj_subset hw2 (Finset.mem_insert_self x w))).2
  -- (proj (B ∩ A i) G).card = a i + b i
  have hfac : ∀ i : Fin p, (proj (B ∩ A i) G).card = a i + b i := by
    intro i
    by_cases hxAi : x ∈ A i
    · have herase : (B ∩ A i).erase x = B' ∩ A i := by rw [hB'def, Chung.erase_inter]
      have := Chung.E1 x (B ∩ A i) G
      rw [herase] at this; exact this
    · rw [hb0 i hxAi, Nat.add_zero]
      rw [Chung.inter_erase_eq x B (A i) hxAi]
  have hRHS : ∏ i, (proj (B ∩ A i) G).card = ∏ i, (a i + b i) :=
    Finset.prod_congr rfl (fun i _ => hfac i)
  rw [hRHS]
  have hgIH : g ^ k ≤ ∏ i, a i := IH G
  set H := Chung.DblSet x B G with hHdef
  -- proj B' H = H  (members of H ⊆ B', so w ∩ B' = w)
  have hHB' : proj B' H = H := by
    unfold proj
    ext w
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨v, hvH, rfl⟩
      have hvH' : v ∈ Chung.DblSet x B G := hHdef ▸ hvH
      rw [Chung.DblSet, Finset.mem_filter] at hvH'
      have hvsub : v ⊆ B' := Chung.proj_subset hvH'.1
      rwa [Finset.inter_eq_left.mpr hvsub]
    · intro hwH
      have hwH' : w ∈ Chung.DblSet x B G := hHdef ▸ hwH
      rw [Chung.DblSet, Finset.mem_filter] at hwH'
      exact ⟨w, hwH, Finset.inter_eq_left.mpr (Chung.proj_subset hwH'.1)⟩
  have hdH : d = (proj B' H).card := by
    rw [hHB']
  have hIHH : (proj B' H).card ^ k ≤ ∏ i, (proj (B' ∩ A i) H).card := IH H
  rw [← hdH] at hIHH
  -- per-factor bound
  have hci : ∀ i : Fin p, (proj (B' ∩ A i) H).card ≤ if x ∈ A i then b i else a i := by
    intro i
    by_cases hxAi : x ∈ A i
    · simp only [hxAi, if_true, hbdef]
      exact Finset.card_le_card (Chung.dbl_trace_dom x B (A i) G hxAi)
    · simp only [hxAi, if_false, hadef]
      apply Finset.card_le_card
      intro w hw
      -- w = v ∩ (B'∩A i) for some v ∈ H; v ∈ H ⊆ proj B' G = G.image(·∩B')
      -- so v = S ∩ B' for some S ∈ G; then w = S ∩ B' ∩ (B'∩A i) = S ∩ (B'∩A i)
      unfold proj at hw ⊢
      rw [Finset.mem_image] at hw ⊢
      obtain ⟨v, hvH, rfl⟩ := hw
      have hvB' : v ∈ proj B' G := by
        rw [hHdef, Chung.DblSet, Finset.mem_filter] at hvH; exact hvH.1
      unfold proj at hvB'
      rw [Finset.mem_image] at hvB'
      obtain ⟨S, hSG, rfl⟩ := hvB'
      refine ⟨S, hSG, ?_⟩
      ext y; simp only [Finset.mem_inter]; tauto
  have hd_split : d ^ k ≤ ∏ i, (if x ∈ A i then b i else a i) :=
    le_trans hIHH (Finset.prod_le_prod' (fun i _ => hci i))
  -- Case split: G = ∅ or G nonempty
  rcases G.eq_empty_or_nonempty with hGempty | hGne
  · -- G = ∅: g = 0, d = 0; use 0^k = 0 ≤ ∏ i, 0
    subst hGempty
    have hg0 : g = 0 := by simp [hgdef, proj]
    have hd0 : d = 0 := by
      simp only [hddef, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro w hw
      rw [hHdef, Chung.DblSet, Finset.mem_filter] at hw
      obtain ⟨_, hw1, _⟩ := hw
      simp [proj] at hw1
    rw [hg0, hd0, Nat.add_zero, zero_pow (Nat.pos_iff_ne_zero.mp hk)]
    exact Nat.zero_le _
  · -- G nonempty: a i ≥ 1 (proj of nonempty G is nonempty)
    have ha1 : ∀ i : Fin p, 1 ≤ a i := fun i => by
      simp only [hadef, Finset.one_le_card]; exact hGne.image _
    -- Pc = product over complement of Sx
    set Pc := ∏ i ∈ Finset.univ.filter (fun i : Fin p => ¬x ∈ A i), a i with hPcdef
    have hPc1 : 1 ≤ Pc := Finset.one_le_prod' (fun i _ => ha1 i)
    -- Product identity: ∏ i, f i = (∏ i ∈ Sx, f i) * (∏ i ∈ Sx.compl, f i)
    -- via Finset.prod_filter_mul_prod_filter_not
    have hprod_a : ∏ i : Fin p, a i = (∏ i ∈ Sx, a i) * Pc := by
      have h := (Finset.prod_filter_mul_prod_filter_not Finset.univ
        (fun i : Fin p => x ∈ A i) a).symm
      rw [hSxdef, hPcdef]; exact h
    have hprod_if : ∏ i : Fin p, (if x ∈ A i then b i else a i) = (∏ i ∈ Sx, b i) * Pc := by
      have h := (Finset.prod_filter_mul_prod_filter_not Finset.univ
        (fun i : Fin p => x ∈ A i) (fun i => if x ∈ A i then b i else a i)).symm
      rw [hSxdef, hPcdef]
      convert h using 2
      · apply Finset.prod_congr rfl
        intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi; simp [hi]
      · apply Finset.prod_congr rfl
        intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi; simp [hi]
    have hg_P : g ^ k ≤ (∏ i ∈ Sx, a i) * Pc := hprod_a ▸ hgIH
    have hd_P : d ^ k ≤ (∏ i ∈ Sx, b i) * Pc := hprod_if ▸ hd_split
    have hL2 := L2_final_P Sx k hk hkSx a b g d Pc hPc1 hg_P hd_P
    -- ∏_univ (a+b) = (∏_Sx (a+b)) * Pc
    have hprod_ab : ∏ i : Fin p, (a i + b i) = (∏ i ∈ Sx, (a i + b i)) * Pc := by
      have h := (Finset.prod_filter_mul_prod_filter_not Finset.univ
        (fun i : Fin p => x ∈ A i) (fun i => a i + b i)).symm
      rw [hSxdef, hPcdef]
      convert h using 2
      apply Finset.prod_congr rfl
      intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [hb0 i hi, Nat.add_zero]
    rw [hprod_ab]; exact hL2

/-- **Main projection inequality (corrected Chung statement, with `0 < k`).** -/
theorem chung_main {U : Type*} [Fintype U] [DecidableEq U] {p : ℕ}
    (A : Fin p → Finset U) (k : ℕ) (hk : 0 < k)
    (hcover : ∀ u : U, k ≤ (Finset.univ.filter (fun i => u ∈ A i)).card)
    (F : Finset (Finset U)) :
    (F.card) ^ k ≤ ∏ i, (F.image (· ∩ A i)).card := by
  -- Generalized statement, proved by erase-induction on the ground set B.
  have key : ∀ B : Finset U, ∀ G : Finset (Finset U),
      (proj B G).card ^ k ≤ ∏ i, (proj (B ∩ A i) G).card := by
    refine Finset.eraseInduction ?_
    intro B IH
    -- IH : ∀ x ∈ B, ∀ G, (proj (B.erase x) G).card^k ≤ ∏ i, (proj ((B.erase x) ∩ A i) G).card
    rcases B.eq_empty_or_nonempty with hBempty | hBne
    · -- Base case B = ∅
      subst hBempty
      intro G
      -- proj ∅ G = G.image (fun S => S ∩ ∅) = G.image (fun _ => ∅)
      have hprojempty : proj (∅ : Finset U) G = G.image (fun _ => (∅ : Finset U)) := by
        unfold proj
        apply Finset.image_congr
        intro S _
        simp
      have hcard_le_one : (proj (∅ : Finset U) G).card ≤ 1 := by
        rw [hprojempty]
        calc (G.image (fun _ => (∅ : Finset U))).card
            ≤ ({(∅ : Finset U)} : Finset (Finset U)).card := by
              apply Finset.card_le_card
              intro s hs
              simp only [Finset.mem_image] at hs
              obtain ⟨a, _, ha⟩ := hs
              simp [← ha]
          _ = 1 := by simp
      -- ∅ ∩ A i = ∅, so each factor on RHS equals (proj ∅ G).card
      have hrhs : ∀ i, proj ((∅ : Finset U) ∩ A i) G = proj (∅ : Finset U) G := by
        intro i
        rw [Finset.empty_inter]
      rw [Finset.prod_congr rfl (fun i _ => by rw [hrhs i])]
      -- goal: (proj ∅ G).card ^ k ≤ ∏ i, (proj ∅ G).card  i.e. c^k ≤ c^p
      rw [Finset.prod_const]
      -- c ≤ 1 and 0 < k ; if c = 0: 0^k = 0 ≤ RHS; if c = 1: 1 ≤ 1
      interval_cases h : (proj (∅ : Finset U) G).card
      · -- c = 0
        rw [zero_pow (Nat.pos_iff_ne_zero.mp hk)]
        exact Nat.zero_le _
      · -- c = 1
        simp
    · -- Step case B ≠ ∅
      obtain ⟨x, hx⟩ := hBne
      exact chung_step A k hk hcover B x hx (fun G => IH x hx G)
  -- Instantiate key at B = univ.
  have hkey := key Finset.univ F
  -- proj univ F = F
  have hprojuniv : proj (Finset.univ : Finset U) F = F := by
    unfold proj
    rw [show (fun S => S ∩ (Finset.univ : Finset U)) = id from by
      funext S; simp]
    rw [Finset.image_id]
  -- univ ∩ A i = A i, so proj (univ ∩ A i) F = F.image (· ∩ A i)
  have hprojA : ∀ i, proj ((Finset.univ : Finset U) ∩ A i) F = F.image (· ∩ A i) := by
    intro i
    unfold proj
    rw [Finset.univ_inter]
  rw [hprojuniv] at hkey
  rw [Finset.prod_congr rfl (fun i _ => by rw [hprojA i])] at hkey
  exact hkey

end Proof.ChungProductTheorem
